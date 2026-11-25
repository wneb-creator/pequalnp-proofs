import argparse,datetime,hashlib,json,subprocess,sys,time
from pathlib import Path
BASE=Path('/tmp/oec/pequalnp-pilot-81')
p=argparse.ArgumentParser();p.add_argument('--tag',required=True);p.add_argument('--seconds',type=int,default=1200);args=p.parse_args()
source=BASE/'sat-collinear4-minimal.py';expected='c428fe71d33b713a32c1899e51dcd40a7aa35a21e516d8cbfb02c60332a3f57c'
assert hashlib.sha256(source.read_bytes()).hexdigest()==expected
assert '/' not in args.tag
for suffix in ['.stdout','.stderr','.receipt.json','.witness.json','.full-fano.json','.runlog','.driver.stderr']:
 assert not (BASE/(args.tag+suffix)).exists(),'run tag must be fresh'
started=datetime.datetime.now(datetime.timezone.utc).isoformat();clock=time.monotonic()
with (BASE/(args.tag+'.runlog')).open('w') as out,(BASE/(args.tag+'.driver.stderr')).open('w') as err:
 proc=subprocess.run([sys.executable,str(source),'--size','15','--tag',args.tag,'--solve',str(args.seconds)],stdout=out,stderr=err)
status='UNKNOWN';solver=BASE/(args.tag+'.stdout')
if solver.exists():
 for line in solver.read_text().splitlines():
  if line.startswith('s '):status=line[2:]
receipt=dict(source=str(source),source_sha256=expected,tag=args.tag,started_utc=started,completed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),seconds_limit=args.seconds,wall_seconds=time.monotonic()-clock,driver_exit=proc.returncode,status=status,scope='Computational witness search only; UNKNOWN or UNSAT is not a Lean refutation.')
(BASE/(args.tag+'.receipt.json')).write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt),flush=True)
assert proc.returncode==0
if status=='SATISFIABLE':
 path=BASE/(args.tag+'.full-fano.json');actual=json.loads(path.read_text());gates=actual['gates'];assert actual['size']==27 and len(gates)==27 and actual['output']==40
 for j,(op,a,b) in enumerate(gates):assert op in ('and','or') and a!=b and 0<=a<14+j and 0<=b<14+j
 def evaluate(mask):
  vs=[bool(mask>>i&1) for i in range(14)]
  for op,a,b in gates:vs.append(vs[a] and vs[b] if op=='and' else vs[a] or vs[b])
  return vs
 edges=[(p,7+l) for p in range(7) for l in range(7) if (p-l)%7 in (0,1,3)]
 for mask in range(16384):assert evaluate(mask)[-1]==any(mask>>a&1 and mask>>b&1 for a,b in edges)
 def derivative(base,seed):
  vs=evaluate(1<<base);ds=[i==seed for i in range(14)]
  for op,a,b in gates:ds.append((vs[a] and ds[b]) or (ds[a] and vs[b]) if op=='and' else ds[a] or ds[b])
  return ds[-1]
 flags=[dict(point=p,line=l-7,forward=derivative(p,l),reverse=derivative(l,p)) for p,l in edges]
 assert len(flags)==21
 p,l=actual['target_edge'];assert (p,7+l) in edges and not derivative(p,7+l) and not derivative(7+l,p)
 validation=dict(status='PASS',actual_witness=str(path),size=27,truth_rows=16384,target_edge=[p,l],all_flags=flags)
 (BASE/(args.tag+'.full-validation.json')).write_text(json.dumps(validation,indent=2)+'\n');print(json.dumps(dict(actual_witness=str(path),truth_rows=16384,verified_derivative_pairs=21,marked_quiet=True)),flush=True)
