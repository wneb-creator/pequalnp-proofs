import importlib.util,json,time
from pathlib import Path
spec=importlib.util.spec_from_file_location('fdp',str(Path(__file__).resolve().parent.parent/'live/formula_sparse.py'));fdp=importlib.util.module_from_spec(spec);spec.loader.exec_module(fdp);live=fdp.live

def closure(state,mode=False,limit=10000):
 n=len(state);full=(1<<n)-1;sr=live.Search(mode=mode);leafcov=[sr.col(a)for a in state];required={}
 def need(mask):
  if mask not in required:
   cov=0
   for i,v in enumerate(leafcov):
    if not mask>>i&1:cov|=v
   required[mask]=sr.allcov&~cov
  return required[mask]
 entries=[(1<<i,a)for i,a in enumerate(state)];known=set(entries);j=0
 while j<len(entries):
  if len(entries)>limit:return None
  bj,b=entries[j]
  for i in range(j):
   ai,a=entries[i]
   if ai&bj:continue
   mask=ai|bj;req=need(mask)
   for op in range(4 if mode else 2):
    z=live.opval(op,a,b)
    if z==0 or z==live.FULL or (mask,z)in known:continue
    if req&~sr.col(z):continue
    known.add((mask,z));entries.append((mask,z))
  j+=1
 return entries

def one_share(state,mode=False):
 start=time.monotonic();es=closure(state,mode)
 if es is None:return None,{}
 calls=0;total=0
 for mask,v in es:
  if v==live.TARGET:return True,dict(kind='readonce')
  leaves=[x for i,x in enumerate(state)if not mask>>i&1]+[v,v]
  ans,details=fdp.formula(leaves,mode,seconds=10)
  calls+=1;total+=details['count']
  if ans is not False:return ans,dict(mask=mask,subexpr=v,closure=len(es),calls=calls,seconds=time.monotonic()-start,total=total)
 return False,dict(closure=len(es),calls=calls,seconds=time.monotonic()-start,total=total)

if __name__=='__main__':
 states=json.loads(Path(str(Path(__file__).resolve().parent.parent/'cofactor/frontier-allcofactor-survivors.json')).read_text())
 for i,r in enumerate(states):print(i,one_share(list(map(int,r['state']))),flush=True)
