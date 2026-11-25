"""Export finite indexed-label fresh closure tables; no Lean proof claimed."""
import importlib.util,json
from pathlib import Path
BASE=Path(__file__).resolve().parent.parent
s=importlib.util.spec_from_file_location('live',BASE/'live/live_search.py');live=importlib.util.module_from_spec(s);s.loader.exec_module(live)
sr=live.Search(mode=False)
def export(row,index):
 signals=[];ids={}
 def intern(v,origin=None):
  if v in ids:return ids[v]
  i=len(signals);ids[v]=i;signals.append(dict(id=i,hex=hex(v),origin=origin,col=hex(sr.col(v))));return i
 inputs=[intern(v,dict(input=i))for i,v in enumerate(live.INPUTS)]
 for op,a,b in row['history']:
  a,b=int(a),int(b);intern(live.opval(op,a,b),dict(op=op,a=intern(a),b=intern(b)))
 raw=list(map(int,row['state']));m=len(raw);target=intern(live.TARGET,dict(target=True))
 def closure(values,basis):
  es=[];known=set();required={}
  for i,v in enumerate(values):
   if basis>>i&1:es.append(dict(mask=1<<i,sig=intern(v),left=-1,right=-1,op=-1));known.add((1<<i,v))
  def need(mask):
   if mask not in required:
    cov=0
    for i,v in enumerate(values):
     if basis>>i&1 and not mask>>i&1:cov|=sr.col(v)
    required[mask]=sr.allcov&~cov
   return required[mask]
  j=0
  while j<len(es):
   eb=es[j];b=int(signals[eb['sig']]['hex'],16)
   for i in range(j):
    ea=es[i];a=int(signals[ea['sig']]['hex'],16)
    if ea['mask']&eb['mask'] or a==b:continue
    mask=ea['mask']|eb['mask']
    for op in range(2):
     z=live.opval(op,a,b)
     if z in(0,live.FULL,a,b) or(mask,z)in known:continue
     if need(mask)&~sr.col(z):continue
     known.add((mask,z));es.append(dict(mask=mask,sig=intern(z,dict(op=op,a=intern(a),b=intern(b))),left=i,right=j,op=op))
   j+=1
  assert (basis,live.TARGET)not in known
  return es,known,need
 basis=(1<<m)-1;cert0,known0,need0=closure(raw,basis);copies=[];bridgecount=0
 for e in cert0:
  a,w=e['mask'],int(signals[e['sig']]['hex'],16);raw2=raw+[w,w];basis2=(basis^a)|(1<<m)|(1<<(m+1))
  cert2,known2,need2=closure(raw2,basis2);bridges=[]
  for bi,b in enumerate(cert0):
   if b['mask']&a:continue
   v=int(signals[b['sig']]['hex'],16)
   if need2(b['mask'])&~sr.col(v):continue
   assert(b['mask'],v)in known2
   bridges.append(bi)
  bridgecount+=len(bridges)
  copies.append(dict(A=a,w=e['sig'],raw=[intern(v)for v in raw2],basis=basis2,entries=cert2,bridge_indices=bridges))
 return dict(description='Finite data only; kernel checks required',index=index,mode=False,remaining=row['remaining'],inputs=inputs,target=target,raw=[intern(v)for v in raw],basis=basis,positive_rows=sr.positive,negative_rows=sr.negative,pair_count=sr.paircount,all_columns=hex(sr.allcov),signals=signals,cert0=cert0,copies=copies,bridge_count=bridgecount,history=row['history'])
front=json.loads((BASE/'cofactor/frontier-allcofactor-survivors.json').read_text())
dest=BASE/'live/delta1-tables';dest.mkdir(exist_ok=True)
for i,row in enumerate(front):
 data=export(row,i);p=dest/('state-'+str(i)+'.json');p.write_text(json.dumps(data,separators=(',',':'))+'\n')
 print(p.name,'bytes',p.stat().st_size,'signals',len(data['signals']),'oldentries',len(data['cert0']),'newentries',sum(len(x['entries'])for x in data['copies']),'bridges',data['bridge_count'],flush=True)
