import z3,json,time,sys
from pathlib import Path

def extrema(n,edges):
 adj=[0]*n
 for u,v in edges:adj[u]|=1<<v;adj[v]|=1<<u
 mis=[]
 for m in range(1<<n):
  if any((m>>u&1) and (adj[u]&m) for u in range(n)):continue
  if all((m>>u&1) or (adj[u]&m) for u in range(n)):mis.append(m)
 positive=[(1<<u)|(1<<v) for u,v in edges]
 return positive+mis,len(positive),mis

def synth(n,edges,s,mode='general',timeout=120000,seed=None,maxchanges=None,symmetry=True,dominance=False,maxorder=False,firstpairs=None,localcuts=False,maxor=None):
 t0=time.monotonic();tests,k,mis=extrema(n,edges);width=len(tests);iw=max(1,(n+s).bit_length());allmask=(1<<width)-1;target=(1<<k)-1
 inputs=[sum(1<<j for j,a in enumerate(tests) if a>>i&1) for i in range(n)]
 vals=[z3.BitVecVal(v,width) for v in inputs]
 sol=z3.SolverFor('QF_BV');sol.set(timeout=timeout)
 aa=[];bb=[];oo=[];unsafe=[]
 for j in range(s):
  a=z3.BitVec('a'+str(j),iw);b=z3.BitVec('b'+str(j),iw);op=z3.Bool('and'+str(j));v=z3.BitVec('v'+str(j),width)
  sol.add(z3.ULT(a,b),z3.ULT(b,n+j))
  if j==0 and firstpairs is not None:sol.add(z3.Or(*[z3.And(a==u,b==v) for u,v in firstpairs]))
  def pick(k):
   r=vals[-1]
   for i in range(len(vals)-2,-1,-1):r=z3.If(k==i,vals[i],r)
   return r
  x=pick(a);y=pick(b);sol.add(v==z3.If(op,x&y,x|y))
  if localcuts:
   pm=z3.BitVecVal(target,width);nm=z3.BitVecVal(allmask^target,width)
   sol.add(z3.If(op,z3.And((x & ~y & nm)!=0,(y & ~x & nm)!=0),z3.And((x & ~y & pm)!=0,(y & ~x & pm)!=0)))
   sol.add((v & pm)!=0)
  for old in vals:
   sol.add(v!=old)
   if dominance:
    sol.add(z3.Or((v & ~old & z3.BitVecVal(target,width))!=0,(old & ~v & z3.BitVecVal(allmask^target,width))!=0))
  if dominance:sol.add((v & z3.BitVecVal(target,width))!=0)
  bad=z3.And(op,v&z3.BitVecVal(allmask^target,width)!=0)
  if mode=='sound':sol.add(z3.Not(bad))
  unsafe.append(bad);aa.append(a);bb.append(b);oo.append(op);vals.append(v)
  if j and maxorder:
   prevord=z3.Concat(bb[j-1],aa[j-1],z3.If(oo[j-1],z3.BitVecVal(0,1),z3.BitVecVal(1,1)))
   currord=z3.Concat(b,a,z3.If(op,z3.BitVecVal(0,1),z3.BitVecVal(1,1)))
   sol.add(z3.ULT(prevord,currord))
  if j and symmetry and not maxorder:
   prevord=z3.Concat(aa[j-1],bb[j-1],z3.If(oo[j-1],z3.BitVecVal(0,1),z3.BitVecVal(1,1)))
   currord=z3.Concat(a,b,z3.If(op,z3.BitVecVal(0,1),z3.BitVecVal(1,1)))
   sol.add(z3.Or(a==n+j-1,b==n+j-1,z3.ULE(prevord,currord)))
 for j in range(s-1):sol.add(z3.Or(*[z3.Or(aa[k]==n+j,bb[k]==n+j) for k in range(j+1,s)]))
 if seed is not None:
  changes=[z3.Or(aa[j]!=a,bb[j]!=b,oo[j]!=(op=='and')) for j,(op,a,b) in enumerate(seed)]
  sol.add(z3.PbLe([(q,1) for q in changes],maxchanges))
 if maxor is not None:sol.add(z3.PbLe([(z3.Not(op),1) for op in oo],maxor))
 if mode=='unsound':sol.add(z3.Or(*unsafe))
 sol.add(vals[-1]==target)
 print(json.dumps({'starting':True,'n':n,'size':s,'mode':mode,'tests':width,'maximal_independent_sets':len(mis)}),flush=True)
 r=sol.check();result={'n':n,'edges':edges,'size':s,'mode':mode,'result':str(r),'seconds':time.monotonic()-t0,'tests':width,'maximal_independent_sets':len(mis)}
 if r==z3.sat:
  m=sol.model();result['gates']=[('and' if z3.is_true(m.eval(o)) else 'or',m.eval(a).as_long(),m.eval(b).as_long()) for a,b,o in zip(aa,bb,oo)]
  bad=[];allvals=[];badands=set();owned=[set() for _ in range(s)]
  ancestors=[]
  for j,(op,a,b) in enumerate(result['gates']):
   ac=set()
   if a>=n:ac|=ancestors[a-n]|({a-n} if result['gates'][a-n][0]=='and' else set())
   if b>=n:ac|=ancestors[b-n]|({b-n} if result['gates'][b-n][0]=='and' else set())
   ancestors.append(ac)
  for a in range(1<<n):
   vv=[bool(a>>i&1) for i in range(n)];target=any(a>>u&1 and a>>v&1 for u,v in edges)
   for j,(op,x,y) in enumerate(result['gates']):
    v=vv[x] and vv[y] if op=='and' else vv[x] or vv[y]
    if op=='and' and v and not target:badands.add(j)
    vv.append(v)
   if vv[-1]!=target:bad.append(a)
   for ei,(u,v) in enumerate(edges):
    if a!=(1<<u)|(1<<v):continue
    for j,(op,_,_) in enumerate(result['gates']):
     if op=='and' and vv[n+j] and not any(vv[n+k] for k in ancestors[j]):owned[j].add((u,v))
  result['full_truth_table_errors']=bad;result['unsafe_ands']=sorted(badands)
  result['ownership']=[list(x) for x in owned]
  result['bad_ownership']=[j for j,e in enumerate(owned) if result['gates'][j][0]=='and' and (not e or not set.intersection(*(set(x) for x in e)))]
 if r==z3.unknown:result['reason']=sol.reason_unknown()
 return result

PETER=[(i,(i+1)%5) for i in range(5)]+[(i,i+5) for i in range(5)]+[(5+i,5+(i+2)%5) for i in range(5)]
FANO=[(p,7+l) for l in range(7) for p in range(7) if (p-l)%7 in [0,1,3]]
if __name__=='__main__':
 z3.set_param('memory_max_size',768)
 names=sys.argv[1:] or ['Petersen','Fano']
 for name in names:
  n,e,s=(10,PETER,20) if name=='Petersen' else (14,FANO,27)
  for k,mode in [(s-1,'general'),(s,'sound'),(s,'unsound')]:
   r=synth(n,e,k,mode);r['name']=name
   with Path('/tmp/oec/pequalnp-pilot-55/counterexample-sparse-results.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
   print(json.dumps(r),flush=True)
