"""Finite regression of the candidate Cert0-to-Cert2 bridge; not Lean proof."""
import importlib.util,json,time
from collections import Counter
from pathlib import Path
base=Path(__file__).resolve().parent.parent
s=importlib.util.spec_from_file_location('copy',base/'live/copy_search_irredundant.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
front=json.loads((base/'cofactor/frontier-allcofactor-survivors.json').read_text())
checks=0
for fi,row in enumerate(front):
 state=tuple(sorted(map(int,row['state'])));search=m.CopySearch(False,int(row['remaining']),60,100000,10000);search.current_k=int(row['remaining'])
 roots,es,target=search.closure(state);assert target is None
 total=tuple(state.count(r)for r in roots)
 for ai,(a,w,_,_,_)in enumerate(es):
  new=[]
  for r,t,n in zip(roots,total,a):new.extend([r]*(t-n))
  new.extend((w,w));new=tuple(sorted(new))
  nr,ne,nt=search.closure(new);assert nt is None,(fi,ai,'target')
  idx={r:i for i,r in enumerate(nr)};totalnew=tuple(new.count(r)for r in nr);known={(b,v)for b,v,_,_,_ in ne}
  for b,v,_,_,_ in es:
   if any(x+y>t for x,y,t in zip(a,b,total)):continue
   mapped=[0]*len(nr)
   for r,n in zip(roots,b):
    if n:mapped[idx[r]]+=n
   mapped=tuple(mapped);outside=0
   for r,n,t in zip(nr,mapped,totalnew):
    if n<t:outside |=search.sr.col(r)
   need=search.sr.allcov&~outside
   if need&~search.sr.col(v):continue
   checks+=1
   assert(mapped,v)in known,(fi,ai,'missingbridge',b,v)
 print('state',fi,'oldentries',len(es),'cumulativebridgechecks',checks,'seconds',round(time.monotonic()-search.start,3),flush=True)
print('PASS all fresh closure bridge cases',checks,flush=True)
