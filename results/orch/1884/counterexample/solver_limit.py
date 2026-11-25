import argparse,datetime,json,resource,subprocess,time
from pathlib import Path

parser=argparse.ArgumentParser()
parser.add_argument('stem')
parser.add_argument('--seconds',type=int,default=600)
parser.add_argument('--seed',type=int,default=154)
parser.add_argument('--memory-mib',type=int,default=1024)
parser.add_argument('--proof',action='store_true')
args=parser.parse_args()
base=Path('/tmp/oec/pequalnp-pilot-154/counterexample')
started=datetime.datetime.now(datetime.timezone.utc).isoformat()
wall=time.monotonic()
memory=args.memory_mib*1024**2
def limit():resource.setrlimit(resource.RLIMIT_AS,(memory,memory))
command=['/tmp/oec/pequalnp-pilot-154/lean-4.36.0-linux/bin/cadical','-t',str(args.seconds),'--seed='+str(args.seed),
 '-w',str(base/(args.stem+'.model')),str(base/(args.stem+'.cnf'))]
if args.proof:
    command.insert(1,'--lrat')
    command.append(str(base/(args.stem+'.lrat')))
with (base/(args.stem+'-solver.log')).open('w') as f:
    p=subprocess.run(command,stdout=f,stderr=subprocess.STDOUT,preexec_fn=limit)
result={'started_utc':started,'finished_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'elapsed_seconds':time.monotonic()-wall,'exit_code':p.returncode,'limit_seconds':args.seconds,
 'address_space_limit_bytes':memory,'max_child_rss_kib':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
 'seed':args.seed,'lrat_requested':args.proof}
(base/(args.stem+'-solver-result.json')).write_text(json.dumps(result,indent=2))
print(json.dumps(result),flush=True)
