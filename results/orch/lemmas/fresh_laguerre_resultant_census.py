from fresh_laguerre_resultant import *
from collections import Counter
limit=int(sys.argv[3]) if len(sys.argv)>3 else 100000;st=time.time();sqs={i*i%p:[] for i in range(p)}
for i in range(p):sqs[i*i%p].append(i)
tally=Counter();examples={};count=0
for x,y,z,a in it.product(range(p),repeat=4):
 L=(q2-2*(x+y+z)-a)%p;B=(L+2*y-2*x)%p;C0=(a*L+(x+y+z)**2+2*a*z+2*L*x-q1)%p
 for w in sqs.get((B*B+4*C0)%p,[]):
  b=(B+w)*iv[2]%p;c=(L-b)%p
  if (a*b*c+a*z*z+b*y*y+c*x*x+2*x*y*z-q0)%p:continue
  S=np.array([[a,x,y],[x,b,z],[y,z,c]])
  assert (abc(S)==Rc[:3]).all()
  v=verdict(S);key=tuple(v.values());tally[key]+=1;examples.setdefault(key,S.tolist());count+=1
  if count%1000==0:print('anchors',count,'time',time.time()-st,'hist',dict(tally),flush=True)
 if count>=limit:break
print('RESULT',p,la,'anchors',count,'seconds',time.time()-st,'hist',sorted(tally.items()),'first examples',examples)
