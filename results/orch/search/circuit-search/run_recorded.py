import argparse,hashlib,json,resource,subprocess,sys,time
from datetime import datetime,timezone
from pathlib import Path

parser=argparse.ArgumentParser()
parser.add_argument('--name',required=True)
parser.add_argument('--cnf',required=True)
parser.add_argument('--phases',required=True)
parser.add_argument('--seconds',required=True,type=int)
args=parser.parse_args()
base=Path('/tmp/oec/pequalnp-pilot-70/circuit-search')
cnf=Path(args.cnf);phases=Path(args.phases)
def stamp():return datetime.now(timezone.utc).isoformat()
meta={'name':args.name,'started_at':stamp(),'wall_limit_seconds':args.seconds,
      'command':[str(base/'phased'),str(cnf),str(phases),str(args.seconds)],
      'cnf_sha256':hashlib.sha256(cnf.read_bytes()).hexdigest(),
      'phases_sha256':hashlib.sha256(phases.read_bytes()).hexdigest()}
(base/f'{args.name}-run.json').write_text(json.dumps(meta,indent=2))
before=resource.getrusage(resource.RUSAGE_CHILDREN);start=time.monotonic()
with (base/f'{args.name}-solve.log').open('w') as log:
 rc=subprocess.run(meta['command'],stdout=log,stderr=subprocess.STDOUT).returncode
after=resource.getrusage(resource.RUSAGE_CHILDREN)
result={**meta,'finished_at':stamp(),'wall_seconds':time.monotonic()-start,
        'cpu_seconds':after.ru_utime+after.ru_stime-before.ru_utime-before.ru_stime,
        'max_rss_kib':after.ru_maxrss,'exit_code':rc,
        'status':{0:'UNKNOWN',10:'SAT',20:'UNSAT'}.get(rc,'ERROR')}
if rc==10:
 verify=base/f'{args.name}-verified.log'
 with verify.open('w') as log:
  checked=subprocess.run([sys.executable,str(base/'decode.py'),str(cnf.with_suffix('.map.json')),str(base/f'{args.name}-solve.log')],stdout=log,stderr=subprocess.STDOUT)
 result['full_truth_table_verified']=checked.returncode==0
 if checked.returncode==0:
  text=verify.read_text();gates,_=json.JSONDecoder().raw_decode(text.split('\n',1)[1])
  witness=base/f'{args.name}-witness.json';witness.write_text(json.dumps(gates,indent=2))
  result['witness_file']=str(witness)
(base/f'{args.name}-result.json').write_text(json.dumps(result,indent=2))
print(json.dumps(result),flush=True)
