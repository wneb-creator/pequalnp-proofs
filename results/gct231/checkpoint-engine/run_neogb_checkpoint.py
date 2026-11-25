"""Bounded finite-field run with restartable, explicitly partial checkpoints."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import resource
import signal
import subprocess
import time

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('input',type=Path)
parser.add_argument('output',type=Path)
parser.add_argument('prefix',type=Path)
parser.add_argument('--base-input',type=Path)
parser.add_argument('--seconds',type=int,default=120)
parser.add_argument('--memory-mib',type=int,default=4096)
parser.add_argument('--output-mib',type=int,default=2048)
parser.add_argument('--pairs',type=int,default=32)
parser.add_argument('--threads',type=int,default=1)
parser.add_argument('--checkpoint-seconds',type=float,default=60)
parser.add_argument('--stop-after-round',type=int,default=0)
args=parser.parse_args()
assert args.seconds>0 and args.memory_mib>=64 and args.output_mib>=1
assert args.pairs>=0 and args.threads in (1,2,3)
assert 0<=args.checkpoint_seconds<=3600 and args.stop_after_round>=0
base_input=(args.base_input or args.input).resolve()
source=args.input.resolve()

def digest(path):
    result=hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda:stream.read(1024*1024),b''):
            result.update(block)
    return result.hexdigest()

def header(stream):
    n,m,p,terms=map(int,stream.readline().split())
    lengths=list(map(int,stream.readline().split()))
    assert n>0 and m>0 and p>1 and terms>0
    assert len(lengths)==m and min(lengths)>0 and sum(lengths)==terms
    return n,m,p,terms,lengths

with base_input.open() as base, source.open() as current:
    bn,bm,bp,bt,bl=header(base)
    n,m,p,terms,lengths=header(current)
    assert (n,p)==(bn,bp) and m>=bm and lengths[:bm]==bl
    if base_input!=source:
        for _ in range(bt):
            bnum,bden,*be=map(int,base.readline().split())
            num,den,*exponents=map(int,current.readline().split())
            assert len(be)==len(exponents)==n and be==exponents
            assert bden%p and den%p
            assert bnum*pow(bden,-1,p)%p==num*pow(den,-1,p)%p

directory=Path(__file__).parent/'checkpoint'
binary=directory/'neogb_cli_checkpoint'
library=directory/'libneogb_checkpoint.so'
checkpoint_prefix=Path(str(args.prefix)+'.checkpoint')
assert not args.prefix.with_suffix('.log').exists(), 'Use a fresh run prefix'
assert not Path(str(checkpoint_prefix)+'.latest.json').exists()
command=[str(binary),str(source),str(args.output.resolve()),str(args.pairs),
         str(args.threads),str(checkpoint_prefix.resolve()),
         str(args.checkpoint_seconds),str(args.stop_after_round),str(bm)]
launch={'prepared_utc':datetime.now(timezone.utc).isoformat(),'command':command,
        'input_sha256':digest(source),'base_input':str(base_input),
        'base_input_sha256':digest(base_input),'base_generators':bm,
        'binary_sha256':digest(binary),'library_sha256':digest(library),
        'scope':'Finite-field research computation; checkpoints are partial polynomial consequences.'}
args.prefix.with_suffix('.launch.json').write_text(json.dumps(launch,indent=2)+'\n')

def limits():
    resource.setrlimit(resource.RLIMIT_CORE,(0,0))
    bound=args.memory_mib*1024**2
    resource.setrlimit(resource.RLIMIT_AS,(bound,bound))
    bound=args.output_mib*1024**2
    resource.setrlimit(resource.RLIMIT_FSIZE,(bound,bound))
    resource.setrlimit(resource.RLIMIT_CPU,
        (args.seconds*args.threads+2,args.seconds*args.threads+3))

started=time.monotonic()
with args.prefix.with_suffix('.log').open('w') as log:
    try:
        process=subprocess.run(command,stdout=log,stderr=subprocess.STDOUT,
                               timeout=args.seconds,preexec_fn=limits)
        code=process.returncode
        status={0:'COMPLETED',75:'STOPPED_AFTER_CHECKPOINT',
                76:'UNKNOWN_CHECKPOINT_FAILURE',
                -signal.SIGXFSZ:'UNKNOWN_OUTPUT_FILE_SIZE_LIMIT'}.get(code,'ERROR_NO_VERDICT')
    except subprocess.TimeoutExpired:
        code=None
        status='UNKNOWN_TIME_LIMIT'
result={**launch,'status':status,'returncode':code,'seconds':time.monotonic()-started,
        'wall_limit_seconds':args.seconds,'memory_mib':args.memory_mib,
        'output_mib':args.output_mib,'threads':args.threads,'pairs':args.pairs,
        'checkpoint_seconds':args.checkpoint_seconds,
        'stop_after_round':args.stop_after_round,
        'child_maxrss_kib':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss}
if status=='COMPLETED':
    basis=json.loads(args.output.read_text())
    assert basis['characteristic']==p and basis['nvars']==n
    assert sum(map(len,basis['basis']))==basis['nterms']
    result['unit_basis']=any(len(poly)==1 and int(poly[0][0])%p!=0
        and not any(poly[0][1]) for poly in basis['basis'])
    result['basis_size']=len(basis['basis'])
    result['output_sha256']=digest(args.output)
latest=Path(str(checkpoint_prefix)+'.latest.json')
if latest.exists():
    metadata=json.loads(latest.read_text())
    sequence=metadata['sequence'];assert isinstance(sequence,int) and sequence>0
    snapshot=Path(str(checkpoint_prefix)+f'.s{sequence:06d}.in')
    with snapshot.open() as stream:
        sn,sm,sp,st,sl=header(stream)
    assert (sn,sp)==(n,p) and sl[:bm]==bl
    assert metadata['original_generators']==bm and metadata['original_terms']==bt
    assert sm==bm+metadata['appended_basis_rows']
    assert st==bt+metadata['appended_basis_terms']
    result['checkpoint']={'path':str(snapshot),'sha256':digest(snapshot),
                          'bytes':snapshot.stat().st_size,'metadata':metadata}
args.prefix.with_suffix('.result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,sort_keys=True),flush=True)
