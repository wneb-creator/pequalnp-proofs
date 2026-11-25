from pathlib import Path
import argparse, hashlib, json, resource, subprocess, time

parser=argparse.ArgumentParser()
parser.add_argument('input',type=Path)
parser.add_argument('output',type=Path)
parser.add_argument('prefix',type=Path)
parser.add_argument('--seconds',type=int,default=120)
parser.add_argument('--memory-mib',type=int,default=4096)
parser.add_argument('--pairs',type=int,default=0)
args=parser.parse_args()
if args.seconds<1 or args.memory_mib<64 or args.pairs<0: parser.error('invalid limit')
binary=Path(__file__).with_name('neogb_cli')
command=[str(binary),str(args.input.resolve()),str(args.output.resolve()),str(args.pairs)]
def limits():
    resource.setrlimit(resource.RLIMIT_CORE,(0,0))
    bound=args.memory_mib*1024*1024
    resource.setrlimit(resource.RLIMIT_AS,(bound,bound))
    resource.setrlimit(resource.RLIMIT_CPU,(args.seconds+2,args.seconds+3))
started=time.monotonic()
with args.prefix.with_suffix('.log').open('w') as log:
    try:
        result=subprocess.run(command,stdout=log,stderr=subprocess.STDOUT,
                              timeout=args.seconds,preexec_fn=limits)
        code=result.returncode
        status='COMPLETED' if code==0 else 'ERROR_OR_RESOURCE_LIMIT'
    except subprocess.TimeoutExpired:
        code=None
        status='UNKNOWN_TIME_LIMIT'
elapsed=time.monotonic()-started
meta={'command':command,'status':status,'returncode':code,'seconds':elapsed,
      'wall_limit_seconds':args.seconds,'memory_mib':args.memory_mib,
      'child_maxrss_kib':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
      'binary_sha256':hashlib.sha256(binary.read_bytes()).hexdigest(),
      'input_sha256':hashlib.sha256(args.input.read_bytes()).hexdigest()}
if status=='COMPLETED':
    data=json.loads(args.output.read_text())
    assert set(data)=={'characteristic','nvars','nterms','basis'}
    assert sum(map(len,data['basis']))==data['nterms']
    for poly in data['basis']:
        for coefficient,exponents in poly:
            assert len(exponents)==data['nvars'] and all(e>=0 for e in exponents)
            int(coefficient)
    meta['unit_basis']=any(len(poly)==1 and int(poly[0][0])!=0 and not any(poly[0][1])
                           for poly in data['basis'])
    meta['basis_size']=len(data['basis'])
    meta['output_sha256']=hashlib.sha256(args.output.read_bytes()).hexdigest()
args.prefix.with_suffix('.result.json').write_text(json.dumps(meta,indent=2)+'\n')
print(json.dumps(meta,sort_keys=True))
