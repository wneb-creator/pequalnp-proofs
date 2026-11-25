from pathlib import Path
from collections import defaultdict,Counter
import ast,json,time
start=time.monotonic();allbits=(1<<1024)-1;sigbits=(1<<128)-1
states={};picks={};pools=defaultdict(list)
for line in Path('/tmp/oec/pequalnp-pilot-184/replacement/all-states.tsv').read_text().splitlines():
 if '\t' not in line:continue
 fs=line.split('\t')
 if fs[0]=='META' or fs[2]=='RAW':continue
 name,k,i,raw=fs
 states[(name,int(k),int(i))]=[(a,b[0],b[1]) for a,b in ast.literal_eval(raw)]
for line in Path('/tmp/oec/pequalnp-pilot-184/search/all-pools.tsv').read_text().splitlines():
 if '\t' not in line:continue
 fs=line.split('\t');key=(fs[1],int(fs[2]),int(fs[3]))
 if fs[0]=='PICKS':picks[key]=ast.literal_eval(fs[4])
 elif fs[0]=='POOL':pools[key].append((int(fs[4]),int(fs[5]),int(fs[6]),int(fs[7]),ast.literal_eval(fs[8])))
 else:raise RuntimeError(fs[0])
def binary(d,a,b):return a&b if d==0 else a|b if d==1 else a&~b if d==2 else ~a&b
out=[];profiles=[];totals=defaultdict(Counter)
for key,ws in states.items():
 name,k,i=key;ps=pools[key];n=len(ws);np=len(ps);vals={x[0] for x in ws}
 assert len(vals)==n
 pc=[]
 for pid,D,bound,paid,bank in ps:
  A={0,D};A.update(v&D for v in bank);A.update((~v)&D for v in bank)
  missing=sum(1<<j for j,x in enumerate(ws) if x[0]&D not in A)
  constants=sum(1<<j for j,x in enumerate(ws) if x[0]&D in (0,D))
  pc.append((D,bound,paid,A,missing,constants))
 counts=Counter();visited=0
 if np>=2:
  for ai,a in enumerate(ws):
   for bi in range(ai+1,n):
    b=ws[bi];ac=a[1]^a[2];bc=b[1]^b[2];rest=0
    for j,v in enumerate(ws):
     if j!=ai and j!=bi:rest|=v[1]^v[2]
    for d in range(4):
     z=tuple(binary(d,x,y) for x,y in zip(a,b))
     if z[0] in (0,sigbits) or z[0] in vals:continue
     base=rest|(z[1]^z[2])
     for ka in (False,True):
      for kb in (False,True):
       if n-1+ka+kb>k:continue
       cov=base|(ac if ka else 0)|(bc if kb else 0)
       if cov!=allbits:continue
       visited+=1;R=((1<<n)-1)^((0 if ka else 1)<<ai)^((0 if kb else 1)<<bi)
       mask=0
       for j,(D,bound,paid,A,missing,constants) in enumerate(pc):
        budget=k-1+paid
        if bound+constants.bit_count()+1<=budget:continue
        con=bound+(R&constants).bit_count()+(z[0]&D in (0,D))
        if con<=budget:continue
        extra=(z[0]&D) not in A
        if budget+extra>=con:continue
        if R&missing:continue
        if extra and missing&((1<<ai)|(1<<bi)):continue
        mask|=1<<j
       counts[mask]+=1
 def cost(order):
  return sum(c*next((r+1 for r,j in enumerate(order) if m>>j&1),np) for m,c in counts.items())
 remaining=dict(counts);remaining.pop(0,None);order=[];unselected=list(range(np))
 while unselected:
  j=max(unselected,key=lambda j:sum(c for m,c in remaining.items() if m>>j&1))
  order.append(j);unselected.remove(j)
  remaining={m:c for m,c in remaining.items() if not m>>j&1}
 old=cost(range(np));new=cost(order)
 if new>=old:order=list(range(np));new=old
 oldids=picks[key];validids=[p[0] for p in ps]
 newids=[validids[j] for j in order];extra=list(oldids)
 for v in validids:extra.remove(v)
 newids+=extra
 if Counter(newids)!=Counter(oldids):raise RuntimeError(key)
 if new==old:newids=oldids
 profiles.append({'name':name,'k':k,'i':i,'ids':oldids,'counts':dict(counts)})
 totals[name].update({'states':1,'visited':visited,'old':old,'new':new,'reordered':int(newids!=oldids),'no_pool_success':counts[0]})
 if newids!=oldids:
  out.append({'name':name,'k':k,'i':i,'old_ids':oldids,'new_ids':newids,'old_scans':old,'new_scans':new,'transitions':visited,'reject_masks':dict(counts)})
 if len(out)%100==0 and newids!=oldids:print('progress',len(out),'nodes',key,'seconds',round(time.monotonic()-start,2),flush=True)
for name,v in totals.items():print(name,dict(v),flush=True)
report={'seconds':time.monotonic()-start,'totals':{n:dict(v) for n,v in totals.items()},'reordered':out,'profiles':profiles}
Path('/tmp/oec/pequalnp-pilot-184/search/pool-order.json').write_text(json.dumps(report,indent=2))
print('TOTAL',dict(sum(totals.values(),Counter())),'time',report['seconds'],flush=True)
