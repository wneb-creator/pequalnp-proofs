import argparse,datetime,hashlib,json,subprocess,sys,time
from pathlib import Path
BASE=Path('/tmp/oec/pequalnp-pilot-81')
p=argparse.ArgumentParser();p.add_argument('--source',required=True);p.add_argument('--sha256',required=True);p.add_argument('--tag',required=True);p.add_argument('--seconds',type=int,default=1200);args=p.parse_args()
source=BASE/args.source
assert source.parent==BASE and source.is_file()
assert hashlib.sha256(source.read_bytes()).hexdigest()==args.sha256
assert '/' not in args.tag
for suffix in ['.stdout','.stderr','.receipt.json','.compact.json','.runlog','.driver.stderr']:
 assert not (BASE/(args.tag+suffix)).exists(), 'run tag must be fresh'
started=datetime.datetime.now(datetime.timezone.utc).isoformat();clock=time.monotonic()
with (BASE/(args.tag+'.runlog')).open('w') as out,(BASE/(args.tag+'.driver.stderr')).open('w') as err:
 proc=subprocess.run([sys.executable,str(source),'--cap','18','--tag',args.tag,'--negative-proxy','--solve',str(args.seconds)],stdout=out,stderr=err)
status='UNKNOWN';solver=BASE/(args.tag+'.stdout')
if solver.exists():
 for line in solver.read_text().splitlines():
  if line.startswith('s '):status=line[2:]
receipt=dict(source=str(source),source_sha256=args.sha256,tag=args.tag,started_utc=started,completed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),seconds_limit=args.seconds,wall_seconds=time.monotonic()-clock,driver_exit=proc.returncode,status=status,scope='Computational SAT search only; UNKNOWN is not an impossibility result and UNSAT is not a Lean refutation.')
(BASE/(args.tag+'.receipt.json')).write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt),flush=True)
assert proc.returncode==0
if status=='SATISFIABLE':
 candidate=BASE/(args.tag+'.compact.json')
 with (BASE/(args.tag+'.reconstruct.stdout')).open('w') as out,(BASE/(args.tag+'.reconstruct.stderr')).open('w') as err:
  checked=subprocess.run([sys.executable,str(BASE/'sat-p14-reconstruct.py'),str(candidate)],stdout=out,stderr=err)
 assert checked.returncode==0
 validation=json.loads(candidate.with_name(candidate.stem+'.circuit.validation.json').read_text())
 assert validation['verdict']=='PASS' and validation['truth_rows']==16384
 assert len(validation['all_flags'])==21
 actual=json.loads(Path(validation['circuit']).read_text());assert actual['size']==27 and len(actual['gates'])==27 and actual['output']==40
 assert any(f['point']==0 and f['line']==0 and not f['forward'] and not f['reverse'] for f in validation['all_flags'])
 print(json.dumps(dict(actual_witness=validation['circuit'],truth_rows=16384,verified_derivative_pairs=len(validation['all_flags']),marked_quiet=True)),flush=True)
