import argparse
from datetime import datetime, timezone
import gzip
import hashlib
import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import time

ap=argparse.ArgumentParser()
ap.add_argument('stem')
ap.add_argument('--seconds',type=int,default=900)
ap.add_argument('--address-space-gib',type=float,default=1.25)
ap.add_argument('--input-stem')
ap.add_argument('--cnf-gzip')
ap.add_argument('--expected-cnf-sha256')
ap.add_argument('--shared-memory-start-gib',type=float,default=4.0)
ap.add_argument('--shared-memory-stop-gib',type=float,default=6.5)
args=ap.parse_args()
address_limit=int(args.address_space_gib*1024**3)
assert address_limit>0
resource.setrlimit(resource.RLIMIT_AS,(address_limit,address_limit))
stem=Path(args.stem)
input_stem=Path(args.input_stem) if args.input_stem else stem
mapping=json.loads(input_stem.with_suffix('.mapping.json').read_text())
variables=mapping['signature_variables']
assert len(variables)%2==0
k=len(variables)//2
vertices=mapping['line_inputs']
points=mapping['points']
targets=mapping['target_masks']
n=len(vertices)
assert len(points)==len(targets)
assert mapping['positive_samples']==[1<<i for i in range(n)]
positive=mapping['positive_samples']
negative=mapping['negative_samples']
samples=positive+negative
command=['/tmp/oec/pequalnp-pilot-62/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical',
         '-t',str(args.seconds),'-w',str(stem.with_suffix('.sol')),
         '-' if args.cnf_gzip else str(input_stem.with_suffix('.cnf'))]
stem.with_suffix('.command.json').write_text(json.dumps(command,indent=2)+'\n')
if args.cnf_gzip:
    assert args.expected_cnf_sha256
    checksum=hashlib.sha256()
    with gzip.open(args.cnf_gzip,'rb') as data:
        while chunk:=data.read(1048576):checksum.update(chunk)
    assert checksum.hexdigest()==args.expected_cnf_sha256
start=time.monotonic()
memory_path=Path('/sys/fs/cgroup/memory.current')
assert memory_path.is_file()
start_limit=int(args.shared_memory_start_gib*1024**3)
stop_limit=int(args.shared_memory_stop_gib*1024**3)
assert 0<start_limit<stop_limit
initial_memory=int(memory_path.read_text())
if initial_memory>start_limit:
    status={'result':'not_started','reason':'shared_memory_preflight',
            'shared_memory_bytes':initial_memory,'start_limit_bytes':start_limit}
    stem.with_suffix('.status.json').write_text(json.dumps(status,indent=2)+'\n')
    print(json.dumps(status),flush=True)
    raise SystemExit(0)
stop_reason=None
signals=[]
maximum_shared_memory=initial_memory
reader=None
reader_exit=None
print(json.dumps({'or_count':k,'inputs':n,'positive_samples':len(positive),
                  'negative_samples':len(negative),'solver_seconds':args.seconds}),flush=True)
with stem.with_suffix('.solver.log').open('w') as log, stem.with_suffix('.reader.log').open('w') as reader_log:
    process=subprocess.Popen(command,stdin=subprocess.PIPE if args.cnf_gzip else None,
                             stdout=log,stderr=subprocess.STDOUT,process_group=0)
    owned_group=process.pid
    assert os.getpgid(process.pid)==owned_group
    if args.cnf_gzip:
        reader_command=['/usr/bin/gzip','-d','-c',args.cnf_gzip]
        try:
            reader=subprocess.Popen(reader_command,stdout=process.stdin,stderr=reader_log,
                                    process_group=owned_group)
        except BaseException:
            process.stdin.close()
            process.terminate()
            process.wait()
            raise
        process.stdin.close()
    def signal_owned_group(sig):
        live=[p for p in [process,reader] if p is not None and p.poll() is None]
        if live:
            assert any(os.getpgid(p.pid)==owned_group for p in live)
            try:os.killpg(owned_group,sig)
            except ProcessLookupError:pass
    identity={'pid':process.pid,'started_utc':datetime.now(timezone.utc).isoformat(),
              'command':command,'address_space_limit_bytes':address_limit,
              'input_stem':str(input_stem),'shared_memory_start_limit_bytes':start_limit,
              'shared_memory_stop_limit_bytes':stop_limit,'owned_process_group':owned_group,
              'reader_pid':reader.pid if reader else None,'input_gzip':args.cnf_gzip,
              'input_uncompressed_sha256':args.expected_cnf_sha256}
    stat_path=Path('/proc')/str(process.pid)/'stat'
    if stat_path.is_file():
        stat=stat_path.read_text()
        identity['process_start_ticks']=int(stat[stat.rfind(')')+2:].split()[19])
    stem.with_suffix('.process.json').write_text(json.dumps(identity,indent=2)+'\n')
    while process.poll() is None:
        current_memory=int(memory_path.read_text())
        maximum_shared_memory=max(maximum_shared_memory,current_memory)
        if current_memory>=stop_limit:
            stop_reason='shared_memory_guard'
            signal_owned_group(signal.SIGINT)
            signals.append('SIGINT')
            stem.with_suffix('.resource-stop-request.json').write_text(json.dumps({
                'requested_at':datetime.now(timezone.utc).isoformat(),'pid':process.pid,
                'reason':stop_reason,'shared_memory_bytes':current_memory,
                'stop_limit_bytes':stop_limit,'signals':signals},indent=2)+'\n')
            break
        time.sleep(0.25)
    if stop_reason:
        try: process.wait(timeout=2)
        except subprocess.TimeoutExpired:
            signal_owned_group(signal.SIGTERM);signals.append('SIGTERM')
            try: process.wait(timeout=2)
            except subprocess.TimeoutExpired:
                signal_owned_group(signal.SIGKILL);signals.append('SIGKILL')
    returncode=process.wait()
    if reader:
        try:reader_exit=reader.wait(timeout=2)
        except subprocess.TimeoutExpired:
            signal_owned_group(signal.SIGTERM);signals.append('SIGTERM_READER_CLEANUP')
            try:reader_exit=reader.wait(timeout=2)
            except subprocess.TimeoutExpired:
                signal_owned_group(signal.SIGKILL);signals.append('SIGKILL_READER_CLEANUP')
                reader_exit=reader.wait()
result={10:'sat',20:'unsat'}.get(returncode,'unknown')
if args.cnf_gzip and reader_exit!=0 and result in ('sat','unsat'):
    result='unconfirmed_input_reader_failure'
usage=resource.getrusage(resource.RUSAGE_CHILDREN)
status={'result':result,'solver_exit':returncode,'solver_wall_seconds':time.monotonic()-start,
        'child_user_cpu_seconds':usage.ru_utime,'child_system_cpu_seconds':usage.ru_stime,
        'child_max_rss_KiB':usage.ru_maxrss,'stop_reason':stop_reason,'signals':signals,
        'maximum_shared_memory_bytes':maximum_shared_memory,'reader_exit':reader_exit}
stem.with_suffix('.status.json').write_text(json.dumps(status,indent=2)+'\n')
print(json.dumps(status),flush=True)
if returncode!=10 or result!='sat':raise SystemExit(0)
assignment={}
for line in stem.with_suffix('.sol').read_text().splitlines():
    if line.startswith('v '):
        for word in line.split()[1:]:
            lit=int(word)
            if lit:assignment[abs(lit)]=lit>0
assert all(type(v) is bool or v in assignment for group in variables for v in group)
signatures=[sum(int(v if type(v) is bool else assignment[v])<<b for b,v in enumerate(group)) for group in variables]
np=len(positive)
pm=(1<<np)-1
full=(1<<len(samples))-1
values=[sum(bool(q>>i&1)<<j for j,q in enumerate(samples)) for i in range(n)]
operands=[]
for g in range(k):
    branch_signatures=signatures[2*g:2*g+2]
    a,b=branch_signatures
    assert a&~b and b&~a and a<b
    chosen=[[i for i,w in enumerate(values) if w&sig==sig] for sig in branch_signatures]
    assert all(chosen)
    branch_values=[]
    for sig,refs in zip(branch_signatures,chosen):
        value=full
        for ref in refs:value &= values[ref]
        assert value&pm==sig
        branch_values.append(value)
    operands.append(chosen)
    values.append(branch_values[0]|branch_values[1])
output_refs=[[i for i,w in enumerate(values) if w&t==t] for t in targets]
assert all(output_refs)
for t,refs in zip(targets,output_refs):
    value=full
    for ref in refs:value &= values[ref]
    assert value==sum(bool(q&t)<<j for j,q in enumerate(samples))
for row,bound in enumerate(mapping['false_OR_bounds'],np):
    assert sum(not(w>>row&1) for w in values[n:])>=bound
# Independently generate the geometric caps and replay explicit wire references.
D={0,1,3,9}
pencils=[sum(1<<i for i,l in enumerate(vertices) if (p-l)%13 in D) for p in range(13)]
def is_cap(q):return all((q&t).bit_count()<=2 for t in pencils)
def evaluate(q):
    wires=[bool(q>>i&1) for i in range(n)]
    for a,b in operands:wires.append(all(wires[i] for i in a) or all(wires[i] for i in b))
    return [all(wires[i] for i in refs) for refs in output_refs]
caps=[q for q in range(1<<n) if is_cap(q)]
for q in caps:
    assert evaluate(q)==[bool(q&t) for t in targets]
witness={'points':points,'line_inputs':vertices,'or_count':k,
         'operand_signatures':[signatures[2*g:2*g+2] for g in range(k)],
         'operand_wire_lists':operands,'output_wire_lists':output_refs,
         'checked_assignments':len(caps),'checked_output_cap_pairs':len(caps)*len(points)}
stem.with_suffix('.witness.json').write_text(json.dumps(witness,indent=2)+'\n')
print('WITNESS_VERIFIED',k,'ORs',len(points),'outputs',len(caps),'caps',flush=True)
if points==list(range(13)) and vertices==list(range(13)):
    # Lift the shared line outputs and join their thirteen point-weighted terms.
    def remap(i):return 13+i if i<n else 26+i-n
    global_ops=[[[remap(i) for i in branch] for branch in pair] for pair in operands]
    terms=[[p]+[remap(i) for i in refs] for p,refs in zip(points,output_refs)]
    previous=terms[0]
    for term in terms[1:]:
        global_ops.append([previous,term])
        previous=[26+len(global_ops)-1]
    global_witness={'input_count':26,'or_count':len(global_ops),
       'operand_wire_lists':global_ops,'output_wire_list':previous,
       'source_multioutput_or_count':k}
    # Verify against all actual generic geometric inputs, not just the pruned caps.
    geom=json.loads(Path('/tmp/oec/pequalnp-pilot-62/geometry-data.json').read_text())
    negatives=[]
    for row in geom['generic']:
        negatives.append(row['S'] | (row['D']<<13))
    positives=[(1<<p)|(1<<(13+l)) for p in range(13) for l in range(13) if (p-l)%13 in D]
    for q,expected in [(q,True) for q in positives]+[(q,False) for q in negatives]+[(1<<i,False) for i in range(26)]:
        wires=[bool(q>>i&1) for i in range(26)]
        for a,b in global_ops:wires.append(all(wires[i] for i in a) or all(wires[i] for i in b))
        assert all(wires[i] for i in previous)==expected
    global_witness['checked_positive_samples']=len(positives)
    global_witness['checked_negative_samples']=len(negatives)+26
    stem.with_suffix('.global-witness.json').write_text(json.dumps(global_witness,indent=2)+'\n')
    print('GLOBAL_WITNESS_VERIFIED',len(global_ops),'ORs',flush=True)
