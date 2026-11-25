from pathlib import Path
from collections import Counter
import argparse, functools, json, re, time

ap=argparse.ArgumentParser()
ap.add_argument('directory',type=Path)
ap.add_argument('output',type=Path)
ap.add_argument('--profile',type=int)
ap.add_argument('--strong-singlezero',action='store_true')
args=ap.parse_args()
source=(Path(__file__).parent/'copy_search_first_prooftrace.cpp').read_text()
profiles=[tuple(map(int,x)) for x in re.findall(r'\{(\d+),(\d+),(\d+),(\d+)\}',source.split('static const CP profiles[CP_COUNT] = ',1)[1].split(';',1)[0])]
masks=[sum(1<<r for r in range(1024) if r&z==0 and r&o==o) for z,o,_,_ in profiles]
inputs=[sum(1<<r for r in range(1024) if r>>j&1) for j in range(10)]
free=[{0,m}|{x&m for x in inputs} for m in masks]
nodes={}; signals={}; requested=[]
for line in (args.directory/'proof.jsonl').open():
 e=json.loads(line);kind=e['event']
 if kind=='node':nodes[e['id']]={'node':e,'entries':[]}
 elif kind=='basis':nodes[e['node']]['basis']=e
 elif kind=='entry':nodes[e['node']]['entries'].append(e)
 elif kind=='signal':signals[e['id']]=int(e['hex'],16)
 elif kind=='subtree_cut' or (kind=='done' and e['kind']=='cofactor'):
  if (args.profile is not None and e['profile']==args.profile) or (args.strong_singlezero and e['profile']<10):requested.append(e)

def history(entries,i):
 e=entries[i]
 if e['left']<0:return []
 return history(entries,e['left'])+history(entries,e['right'])+[[e['op'],entries[e['left']]['signal'],entries[e['right']]['signal'],e['signal']]]

def witness(v,state,k,hist):
 mask=masks[v];lower=profiles[v][3]
 pool=[signals[x]&mask for x in state]
 mass=sum(x in (0,mask) for x in pool)
 if lower+mass<=k:return None
 outs={};f=free[v]
 for i,(d,a,b,z) in enumerate(hist):
  value=signals[z]&mask;av=signals[a]&mask;bv=signals[b]&mask
  if value in f or value in outs:continue
  if av not in f and av not in outs:continue
  if bv not in f and bv not in outs:continue
  assert value==(av&bv if d==0 else av|bv)
  outs[value]=(i,av,bv)
 selected=set()
 while pool:
  value=pool.pop()
  if value in f:continue
  if value not in outs:return None
  i,a,b=outs[value]
  if i in selected:continue
  selected.add(i);pool.extend((a,b))
 if lower+mass>k+len(selected):return dict(profile=v,lower=lower,mass=mass,paid=len(selected),budget=k,selected_history=sorted(selected))
 return None

def actual(e):
 nodeid=e.get('node',e.get('id'));n=nodes[nodeid]
 if e['event']=='done':return nodeid,n['node']['state'],n['node']['remaining'],n['node']['history']
 entries=n['entries'];a,b=e['left'],e['right'];basis=n['basis']
 counts=[x+y for x,y in zip(entries[a]['counts'],entries[b]['counts'])]
 state=[r for r,total,used in zip(basis['roots'],basis['total'],counts) for _ in range(total-used)]+[e['signal']]
 hist=n['node']['history']+history(entries,a)+history(entries,b)+[[e['op'],entries[a]['signal'],entries[b]['signal'],e['signal']]]
 return nodeid,state,e['remaining'],hist

result=[];same=0;failed=0;started=time.monotonic();cache={}
for index,e in enumerate(requested):
 nodeid,state,k,hist=actual(e)
 key=(tuple(state),k,tuple(tuple(x) for x in hist))
 if key in cache:replacement=cache[key]
 else:
  order=range(len(profiles))
  if args.profile is None:
   replacement=witness(e['profile'],state,k,hist)
  else:replacement=None
  if replacement is None:
   for v in order:
    if v==args.profile:continue
    replacement=witness(v,state,k,hist)
    if replacement is not None:break
  cache[key]=replacement
 same+=replacement is not None and replacement['profile']==e['profile']
 failed+=replacement is None
 result.append(dict(node=nodeid,event=e['event'],left=e.get('left'),right=e.get('right'),op=e.get('op'),signal=e.get('signal'),original_profile=e['profile'],replacement=replacement,remaining=k,state=state,history=hist))
 if (index+1)%1000==0:print(json.dumps({'processed':index+1,'requested':len(requested),'same':same,'failed':failed,'seconds':time.monotonic()-started}),flush=True)
report=dict(directory=str(args.directory),requested=len(requested),same_profile=same,failed=failed,unique_contexts=len(cache),seconds=time.monotonic()-started,replacements=result,scope='Exact existing projected-history replay, weak signed lower priors only; no Lean certificate or new circuit search.')
args.output.write_text(json.dumps(report,separators=(',',':'))+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='replacements'}),flush=True)
