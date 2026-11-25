import time,json,collections,datetime
D={0,1,3,9}
inc=lambda p,l:(p-l)%13 in D
E=[(p,l) for p in range(13) for l in range(13) if not inc(p,l)]
n=len(E); full=(1<<n)-1
N=[sum(1<<j for j,(q,m) in enumerate(E) if inc(p,m) or inc(q,l)) for p,l in E]
def common(a):
 b=full
 while a:
  x=a&-a; a-=x; b &= N[x.bit_length()-1]
  if not b:return 0
 return b
def closure(a):return common(common(a))
def edges(a):return [E[i] for i in range(n) if a>>i&1]
start=time.monotonic(); a=closure(0); count=0; distribution=collections.Counter(); balanced=[]; maxmin=0
out=open('/tmp/oec/pequalnp-pilot-73/library-route/badpair-balanced.jsonl','w')
while True:
 b=common(a); x=a.bit_count();y=b.bit_count(); count+=1; distribution[(min(x,y),max(x,y))]+=1
 if min(x,y)>maxmin:
  maxmin=min(x,y);print('record',count,x,y,edges(a),edges(b),flush=True)
 if min(x,y)>=10:
  record={'a':edges(a),'b':edges(b)};out.write(json.dumps(record)+'\n')
 if count%1000==0 and time.monotonic()-start>=120:status='TIME_LIMIT';break
 found=False
 for i in range(n-1,-1,-1):
  bit=1<<i
  if not a&bit:
   prefix=a&(bit-1); nxt=closure(prefix|bit)
   if (nxt&(bit-1))==prefix:a=nxt;found=True;break
 if not found:status='COMPLETE';break
out.close()
result={'status':status,'count':count,'seconds':time.monotonic()-start,'maxmin':maxmin,'distribution':{str(k):v for k,v in sorted(distribution.items())},'finished':datetime.datetime.now(datetime.timezone.utc).isoformat()}
open('/tmp/oec/pequalnp-pilot-73/library-route/badpair-concepts-summary.json','w').write(json.dumps(result,indent=2))
print(json.dumps(result),flush=True)
