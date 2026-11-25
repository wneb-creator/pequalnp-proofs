from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,os,resource,subprocess,time

base=Path(__file__).resolve().parent
binary=base/'notor_search_full'
matrix=Path('/tmp/oec/pequalnp-pilot-87/finite_invariants/dynamic-loader/rectangles-v3.txt')
edges=((0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5))
def limits():
 resource.setrlimit(resource.RLIMIT_AS,(1_000_000_000,1_000_000_000))
 os.sched_setaffinity(0,{4});os.nice(10)
def verify(path):
 d=json.loads(path.read_text());gates=d['gates'];assert len(gates)<=19
 assert gates[0]==[1,0,d['first_b']] and gates[1]==[2,10,10]
 assert sum(op==2 for op,a,b in gates)==1
 left_only=right_only=False;sound=True;last=gates[d['output']-10];final_or=last[0]==1
 for row in range(1024):
  values=[bool(row>>i&1) for i in range(10)]
  for op,a,b in gates:
   assert 0<=a<len(values) and 0<=b<len(values) and op in (0,1,2)
   values.append(values[a] and values[b] if op==0 else values[a] or values[b] if op==1 else not values[a])
  goal=any(bool(row>>a&1) and bool(row>>b&1) for a,b in edges)
  assert values[d['output']]==goal
  if final_or:
   a,b=values[last[1]],values[last[2]];left_only|=a and not b;right_only|=b and not a;sound&=not(a or b) or goal
 return {'gate_count':len(gates),'not_count':1,'full1024':True,'final_or':final_or,'sound_operands':sound,'incomparable':left_only and right_only}
while True:
 status=base/'cases-status.json'
 prior=json.loads(status.read_text()) if status.exists() else []
 if any(x.get('independent_replay') for x in prior):raise SystemExit(0)
 if len(prior)==4:break
 time.sleep(1)
results=[]
for first,keep in [('oredge',False),('oredge',True),('ornonedge',False),('ornonedge',True)]:
 original=first+('-retained' if keep else '-consumed')
 if 'heuristic finished found=0' in (base/original/'stdout.txt').read_text():
  print(json.dumps({'case':original,'skipped':'baseline heuristic tree completed without witness'}),flush=True);continue
 name='full-'+original;folder=base/name;folder.mkdir(exist_ok=True)
 cmd=[str(binary),'--first',first,'--cap','19','--seconds','180','--nodes','2000000','--extra-rectangles',str(matrix),'--candidate',str(folder/'candidate.json')]
 if not keep:cmd.append('--consume-or')
 metadata={'command':cmd,'source_sha256':hashlib.sha256((base/'notor_search_full.cpp').read_bytes()).hexdigest(),'matrix_sha256':hashlib.sha256(matrix.read_bytes()).hexdigest(),'cpu':4,'address_limit':1_000_000_000,'started_utc':datetime.now(timezone.utc).isoformat(),'scope':'heuristic witness search only; negative outcomes do not establish UNSAT'}
 (folder/'command.json').write_text(json.dumps(metadata,indent=2)+'\n');started=time.monotonic()
 with (folder/'stdout.txt').open('w') as out,(folder/'stderr.txt').open('w') as err:
  r=subprocess.run(cmd,cwd=folder,stdout=out,stderr=err,preexec_fn=limits)
 metadata.update(exit_code=r.returncode,wall_seconds=time.monotonic()-started,ended_utc=datetime.now(timezone.utc).isoformat())
 if (folder/'candidate.json').exists():metadata['independent_replay']=verify(folder/'candidate.json')
 (folder/'status.json').write_text(json.dumps(metadata,indent=2)+'\n');results.append(metadata)
 (base/'full-cases-status.json').write_text(json.dumps(results,indent=2)+'\n')
 print(json.dumps({'case':name,'exit':r.returncode,'wall_seconds':metadata['wall_seconds'],'witness':metadata.get('independent_replay')}),flush=True)
 if metadata.get('independent_replay'):break
