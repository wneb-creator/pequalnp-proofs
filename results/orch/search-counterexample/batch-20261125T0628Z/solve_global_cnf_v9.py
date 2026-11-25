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
ap.add_argument('--random-seed',type=int,default=0)
ap.add_argument('--save-simplified',action='store_true')
ap.add_argument('--conflicts',type=int)
ap.add_argument('--address-space-gib',type=float,default=3.0)
ap.add_argument('--input-stem')
ap.add_argument('--cnf-gzip')
ap.add_argument('--cnf-composition')
ap.add_argument('--expected-cnf-sha256')
ap.add_argument('--shared-memory-start-gib',type=float,default=4.0)
ap.add_argument('--shared-memory-stop-gib',type=float,default=6.5)
args=ap.parse_args()
assert not(args.cnf_gzip and args.cnf_composition)
assert 0<=args.random_seed<=2000000000
assert args.conflicts is None or args.conflicts>=0
address_limit=int(args.address_space_gib*1024**3)
assert 0<address_limit<=3*1024**3
resource.setrlimit(resource.RLIMIT_AS,(address_limit,address_limit))
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
         '--seed='+str(args.random_seed),'-t',str(args.seconds),'-w',str(stem.with_suffix('.sol')),
         '-' if (args.cnf_gzip or args.cnf_composition) else str(input_stem.with_suffix('.cnf'))]
if args.save_simplified:
    command[-1:-1]=['-o',str(stem.with_suffix('.simplified.cnf.gz')),
                   '-e',str(stem.with_suffix('.extension.txt.gz'))]
if args.conflicts is not None:
    command[-1:-1]=['-c',str(args.conflicts)]
stem.with_suffix('.command.json').write_text(json.dumps(command,indent=2)+'\n')
if args.cnf_gzip:
    assert args.expected_cnf_sha256
    checksum=hashlib.sha256()
    with gzip.open(args.cnf_gzip,'rb') as data:
        while chunk:=data.read(1048576):checksum.update(chunk)
    assert checksum.hexdigest()==args.expected_cnf_sha256
elif args.cnf_composition:
    composition=json.loads(Path(args.cnf_composition).read_text())
    assert Path(composition['mapping_path']).resolve()==input_stem.with_suffix('.mapping.json').resolve()
    assert hashlib.sha256(Path(composition['composer_script']).read_bytes()).hexdigest()==composition['composer_sha256']
    expected=composition['composed_uncompressed_sha256']
    if args.expected_cnf_sha256:assert args.expected_cnf_sha256==expected
    args.expected_cnf_sha256=expected
    checksum=hashlib.sha256()
    with stem.with_suffix('.input-verification.log').open('w') as verify_log:
        verification=subprocess.Popen(['python3',composition['composer_script'],args.cnf_composition],
            stdout=subprocess.PIPE,stderr=verify_log,process_group=0)
        try:
            while chunk:=verification.stdout.read(1048576):checksum.update(chunk)
            assert verification.wait()==0
        finally:
            verification.stdout.close()
            if verification.poll() is None:verification.kill();verification.wait()
    assert checksum.hexdigest()==expected
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
    process=subprocess.Popen(command,stdin=subprocess.PIPE if (args.cnf_gzip or args.cnf_composition) else None,
                             stdout=log,stderr=subprocess.STDOUT,process_group=0)
    owned_group=process.pid
    assert os.getpgid(process.pid)==owned_group
    if args.cnf_gzip or args.cnf_composition:
        reader_command=['python3',composition['composer_script'],args.cnf_composition] if args.cnf_composition else ['/usr/bin/gzip','-d','-c',args.cnf_gzip]
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
              'input_composition':args.cnf_composition,
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
if (args.cnf_gzip or args.cnf_composition) and reader_exit!=0 and result in ('sat','unsat'):
    result='unconfirmed_input_reader_failure'
usage=resource.getrusage(resource.RUSAGE_CHILDREN)
status={'result':result,'solver_exit':returncode,'solver_wall_seconds':time.monotonic()-start,
        'child_user_cpu_seconds':usage.ru_utime,'child_system_cpu_seconds':usage.ru_stime,
        'child_max_rss_KiB':usage.ru_maxrss,'stop_reason':stop_reason,'signals':signals,
        'maximum_shared_memory_bytes':maximum_shared_memory,'reader_exit':reader_exit,
        'simplified_output_requested':args.save_simplified,
        'simplified_cnf_exists':stem.with_suffix('.simplified.cnf.gz').is_file(),
        'extension_stack_exists':stem.with_suffix('.extension.txt.gz').is_file()}
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
if mapping['scenario']=='global' and n==26:
    data=json.loads(Path('/tmp/oec/pequalnp-pilot-62/global-first-or-symmetry.json').read_text())
    full_positive=data['positive_samples']
    full_generic=data['negative_samples']
    assert len(full_positive)==52 and len(full_generic)==468
    all_samples=full_positive+full_generic+[1<<i for i in range(26)]
    all_mask=(1<<len(all_samples))-1
    full_values=[sum(bool(q>>i&1)<<j for j,q in enumerate(all_samples)) for i in range(26)]
    for left_refs,right_refs in operands:
        left=right=all_mask
        for ref in left_refs:left &= full_values[ref]
        for ref in right_refs:right &= full_values[ref]
        full_values.append(left|right)
    actual=all_mask
    for ref in output_refs:actual &= full_values[ref]
    positive_errors=[i for i in range(52) if not(actual>>i&1)]
    generic_errors=[i for i in range(468) if actual>>(52+i)&1]
    singleton_errors=[i for i in range(26) if actual>>(520+i)&1]
    witness['full_positive_errors']=positive_errors
    witness['full_generic_negative_error_indices']=generic_errors
    witness['full_singleton_errors']=singleton_errors
    witness['full_generic_false_OR_counts']=[sum(not(w>>(52+i)&1) for w in full_values[26:]) for i in range(468)]
    witness['is_global_counterexample_candidate']=k<=50 and not(positive_errors or generic_errors or singleton_errors)
    witness['full_separation_valid']=not(positive_errors or generic_errors or singleton_errors)
    witness['search_scope']=mapping.get('search_scope')
    witness['generic_negative_indices_used_in_CNF']=mapping.get('generic_negative_indices',list(range(468)))
    print('FULL_GLOBAL_CHECK',json.dumps({'or_count':k,'positive_errors':len(positive_errors),
          'generic_errors':len(generic_errors),'singleton_errors':len(singleton_errors),
          'is_global_counterexample_candidate':witness['is_global_counterexample_candidate']}),flush=True)
stem.with_suffix('.witness.json').write_text(json.dumps(witness,indent=2)+'\n')
label='INVALID_FULL_GLOBAL_SAMPLE_CANDIDATE' if witness.get('full_separation_valid') is False else 'WITNESS_VERIFIED'
print(label,k,'ORs',len(samples),'encoded samples',flush=True)
