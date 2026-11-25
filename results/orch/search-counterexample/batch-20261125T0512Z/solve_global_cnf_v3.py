import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import resource
import signal
import subprocess
import time

ap=argparse.ArgumentParser()
ap.add_argument('stem')
ap.add_argument('--seconds',type=int,default=900)
ap.add_argument('--input-stem')
ap.add_argument('--shared-memory-start-gib',type=float,default=4.0)
ap.add_argument('--shared-memory-stop-gib',type=float,default=6.5)
args=ap.parse_args()
resource.setrlimit(resource.RLIMIT_AS,(3*1024**3,3*1024**3))
stem=Path(args.stem)
input_stem=Path(args.input_stem) if args.input_stem else stem
mapping=json.loads(input_stem.with_suffix('.mapping.json').read_text())
variables=mapping['signature_variables']
assert len(variables)%2==0
k=len(variables)//2
n=mapping['input_count']
positive=mapping['positive_samples']
negative=mapping['negative_samples']
samples=positive+negative
command=['/tmp/oec/pequalnp-pilot-62/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical',
         '-t',str(args.seconds),'-w',str(stem.with_suffix('.sol')),str(input_stem.with_suffix('.cnf'))]
stem.with_suffix('.command.json').write_text(json.dumps(command,indent=2)+'\n')
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
print(json.dumps({'or_count':k,'inputs':n,'positive_samples':len(positive),
                  'negative_samples':len(negative),'solver_seconds':args.seconds}),flush=True)
with stem.with_suffix('.solver.log').open('w') as log:
    process=subprocess.Popen(command,stdout=log,stderr=subprocess.STDOUT)
    identity={'pid':process.pid,'started_utc':datetime.now(timezone.utc).isoformat(),
              'command':command,'address_space_limit_bytes':3*1024**3,
              'input_stem':str(input_stem),'shared_memory_start_limit_bytes':start_limit,
              'shared_memory_stop_limit_bytes':stop_limit}
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
            process.send_signal(signal.SIGINT)
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
            process.terminate();signals.append('SIGTERM')
            try: process.wait(timeout=2)
            except subprocess.TimeoutExpired:
                process.kill();signals.append('SIGKILL')
    returncode=process.wait()
result={10:'sat',20:'unsat'}.get(returncode,'unknown')
usage=resource.getrusage(resource.RUSAGE_CHILDREN)
status={'result':result,'solver_exit':returncode,'solver_wall_seconds':time.monotonic()-start,
        'child_user_cpu_seconds':usage.ru_utime,'child_system_cpu_seconds':usage.ru_stime,
        'child_max_rss_KiB':usage.ru_maxrss,'stop_reason':stop_reason,'signals':signals,
        'maximum_shared_memory_bytes':maximum_shared_memory}
stem.with_suffix('.status.json').write_text(json.dumps(status,indent=2)+'\n')
print(json.dumps(status),flush=True)
if returncode!=10:raise SystemExit(0)
assignment={}
for line in stem.with_suffix('.sol').read_text().splitlines():
    if line.startswith('v '):
        for word in line.split()[1:]:
            lit=int(word)
            if lit:assignment[abs(lit)]=lit>0
assert all(v in assignment for group in variables for v in group)
signatures=[sum(int(assignment[v])<<b for b,v in enumerate(group)) for group in variables]
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
output_refs=[i for i,w in enumerate(values) if w&pm==pm]
assert output_refs
output=full
for ref in output_refs:output &= values[ref]
assert output==pm
for row,bound in enumerate(mapping['false_OR_bounds'],np):
    assert sum(not(w>>row&1) for w in values[n:])>=bound
if mapping.get('dirty_singletons'):
    assert negative[-n:]==[1<<i for i in range(n)]
    singleton_part=((1<<n)-1)<<(len(samples)-n)
    assert any(w&singleton_part for w in values[n:])
witness={'scenario':mapping['scenario'],'input_count':n,'or_count':k,
         'operand_signatures':[signatures[2*g:2*g+2] for g in range(k)],
         'operand_wire_lists':operands,'output_wire_list':output_refs,
         'checked_positive_samples':len(positive),'checked_negative_samples':len(negative)}
stem.with_suffix('.witness.json').write_text(json.dumps(witness,indent=2)+'\n')
print('WITNESS_VERIFIED',k,'ORs',len(samples),'samples',flush=True)
