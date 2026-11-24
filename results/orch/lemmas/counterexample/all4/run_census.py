import json,subprocess,sys,time,threading
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor,as_completed
from datetime import datetime,timezone
base=Path(__file__).resolve().parent;D=json.loads((base/'classes.json').read_text());N=D['N'];n=2*N;stop=threading.Event();lock=threading.Lock();beg=time.monotonic();results=[]
def now():return datetime.now(timezone.utc).isoformat()
def record(row):
 with lock:
  results.append(row);(base/'census_results.json').write_text(json.dumps(results,indent=2)+'\n')
  with(base/'events.jsonl').open('a')as f:f.write(json.dumps(row)+'\n')
  print(json.dumps(row),flush=True)
def upper(g):
 edges=[tuple(e)for e in g['edges']];cover=g['vertex_cover_mask'];groups={v:[]for v in range(n)if cover>>v&1}
 for i,j in edges:groups[i if cover>>i&1 else N+j].append(N+j if cover>>i&1 else i)
 gates=[];roots=[]
 def add(op,a,b):gates.append([op,a,b]);return n+len(gates)-1
 for center,neighbors in groups.items():
  if not neighbors:continue
  r=neighbors[0]
  for v in neighbors[1:]:r=add('or',r,v)
  roots.append(add('and',center,r))
 if not roots:return {'size':0,'gates':[],'output':n}
 output=roots[0]
 for r in roots[1:]:output=add('or',output,r)
 R=1<<n;vals=[sum(1<<r for r in range(R)if r>>i&1)for i in range(n)];forbidden={1<<i for i in range(n)}|{(1<<i)|(1<<(N+j))for i in range(N)for j in range(N)if(i,j)not in edges};mask=sum(1<<r for r in forbidden)
 for op,a,b in gates:
  v=vals[a]&vals[b]if op=='and'else vals[a]|vals[b];vals.append(v);assert not(op=='and'and v&mask)
 target=sum(1<<r for r in range(R)if any((r>>i&1)and(r>>(N+j)&1)for i,j in edges));assert vals[output]==target;assert len(gates)==g['clean_upper']
 return {'size':len(gates),'gates':gates,'output':output}
uppers={g['id']:upper(g)for g in D['classes']};(base/'clean_upper_witnesses.json').write_text(json.dumps(uppers,indent=2)+'\n')
def work(g):
 if stop.is_set()or time.monotonic()-beg>3500:return
 bound=g['clean_upper']-1
 if bound<g['active_vertices']-1 or not g['edges']:
  record({'at':now(),'id':g['id'],'result':'no_smaller_by_essential_inputs','clean_upper':g['clean_upper'],'active_vertices':g['active_vertices']});return
 key=f'{g["id"]}_free_atmost{bound}';existing=base/(key+'.json')
 if existing.exists():
  r=json.loads(existing.read_text());r['reused']=True;record(r);return
 limit=300 if g['components']==1 and g['active_vertices']==8 and g['cycle_rank']>=1 else 120
 limit=min(limit,max(1,int(3500-(time.monotonic()-beg))))
 record({'at':now(),'id':g['id'],'result':'started','bound':bound,'timeout_seconds':limit})
 with(base/(key+'.stdout')).open('w')as f:
  p=subprocess.run([sys.executable,str(base/'solve.py'),'--id',g['id'],'--timeout',str(limit)],stdout=f,stderr=subprocess.STDOUT)
 if p.returncode!=0:
  record({'at':now(),'id':g['id'],'result':'process_error','returncode':p.returncode});return
 r=json.loads(existing.read_text());record(r)
 if r['result']=='sat':
  (base/'CANDIDATE.json').write_text(json.dumps(r,indent=2)+'\n');stop.set()
with ThreadPoolExecutor(max_workers=2)as ex:
 fs=[ex.submit(work,g)for g in D['classes']]
 for f in as_completed(fs):f.result()
record({'at':now(),'result':'batch_complete','seconds':round(time.monotonic()-beg,2),'candidate':stop.is_set()})
