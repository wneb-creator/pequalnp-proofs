import importlib.util,json,time,argparse
from pathlib import Path
spec=importlib.util.spec_from_file_location('live',str(Path(__file__).resolve().parent.parent/'live/live_search.py'));live=importlib.util.module_from_spec(spec);spec.loader.exec_module(live)

def formula(state,mode=False,seconds=10,maxfunctions=100000):
 n=len(state);full=(1<<n)-1;sr=live.Search(mode=mode);leafcov=[sr.col(a)for a in state]
 required={}
 def need(mask):
  if mask not in required:
   cov=0
   for i,v in enumerate(leafcov):
    if not mask>>i&1:cov|=v
   required[mask]=sr.allcov&~cov
  return required[mask]
 start=time.monotonic();entries=[(1<<i,a)for i,a in enumerate(state)];known=set(entries);combines=0
 j=0
 while j<len(entries):
  bj,b=entries[j]
  for i in range(j):
   ai,a=entries[i]
   if ai&bj:continue
   mask=ai|bj;requiredmask=need(mask)
   for op in range(4 if mode else 2):
    combines+=1
    if combines&1023==0 and(time.monotonic()-start>seconds or len(entries)>maxfunctions):return None,dict(seconds=time.monotonic()-start,count=len(entries),combines=combines)
    z=live.opval(op,a,b)
    if z==0 or z==live.FULL or (mask,z)in known:continue
    if requiredmask&~sr.col(z):continue
    if mask==full and z==live.TARGET:return True,dict(seconds=time.monotonic()-start,count=len(entries),combines=combines)
    known.add((mask,z));entries.append((mask,z))
  j+=1
 return False,dict(seconds=time.monotonic()-start,count=len(entries),combines=combines)

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--count',type=int,default=10);args=ap.parse_args()
 f=json.loads(Path(str(Path(__file__).resolve().parent.parent/'live/frontier-depth7.json')).read_text())['frontier'];f=[x for x in f if x['remaining']-len(x['state'])+1==0]
 for k,s in enumerate(f[:args.count]):
  ans,info=formula(tuple(map(int,s['state'])));print(k,ans,info,flush=True)
if __name__=='__main__':main()
