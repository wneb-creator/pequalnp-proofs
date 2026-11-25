import time, json, collections, datetime
from pathlib import Path
D={0,1,3,9}
inc=lambda p,l:(p-l)%13 in D
E=[(p,l) for p in range(13) for l in range(13) if not inc(p,l)]
n=len(E); full=(1<<n)-1
N=[sum(1<<j for j,(q,m) in enumerate(E) if inc(p,m) or inc(q,l)) for p,l in E]
rows=[sum(1<<i for i,(p,l) in enumerate(E) if p==j) for j in range(13)]
cols=[sum(1<<i for i,(p,l) in enumerate(E) if l==j) for j in range(13)]
def common(a):
 b=full
 while a:
  x=a&-a; a-=x; b &= N[x.bit_length()-1]
  if not b: return 0
 return b
def closure(a): return common(common(a))
def edges(a): return [E[i] for i in range(n) if a>>i&1]
def shape(a): return (sum(bool(a&r) for r in rows),sum(bool(a&c) for c in cols))
start=time.monotonic(); a=closure(0); count=0; maxmin=-1; records=[]; hist=collections.Counter()
while True:
 b=common(a); count+=1
 ra,ca=shape(a); rb,cb=shape(b)
 v=min(ra,ca,rb,cb); hist[v]+=1
 if v>maxmin:
  maxmin=v; rec={'index':count,'score':v,'shapes':[[ra,ca],[rb,cb]],'a':edges(a),'b':edges(b)}; records.append(rec); print(json.dumps(rec),flush=True)
 if count%1000==0 and time.monotonic()-start>=300: status='TIME_LIMIT'; break
 found=False
 for i in range(n-1,-1,-1):
  bit=1<<i
  if not a&bit:
   prefix=a&(bit-1); nxt=closure(prefix|bit)
   if (nxt&(bit-1))==prefix: a=nxt; found=True; break
 if not found: status='COMPLETE'; break
result={'status':status,'count':count,'seconds':time.monotonic()-start,'maxmin_row_column_support':maxmin,'histogram':dict(hist),'records':records,'finished':datetime.datetime.now(datetime.timezone.utc).isoformat()}
Path('/tmp/oec/pequalnp-pilot-73/library-route/cofactor-shapes-summary.json').write_text(json.dumps(result,indent=2))
print(json.dumps(result),flush=True)
