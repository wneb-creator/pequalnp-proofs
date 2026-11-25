import argparse,builtins,itertools,json,sys,time
from pathlib import Path
builtins.Z3_LIB_DIRS=['/tmp/oec/pequalnp-pilot-56/z3-5.3.3-x64-glibc-2.39/bin']
sys.path.insert(0,'/tmp/oec/pequalnp-pilot-56/z3-5.3.3-x64-glibc-2.39/bin/python')
import z3 as z
p=argparse.ArgumentParser();p.add_argument('n',type=int);p.add_argument('m',type=int);p.add_argument('k',type=int);p.add_argument('--seconds',type=int,default=180);a=p.parse_args();n,m,k=a.n,a.m,a.k
pairs=list(itertools.combinations(range(n),2));edge={uv:z.Bool('e%d_%d'%uv)for uv in pairs}
def E(u,v):return edge[tuple(sorted((u,v)))]
s=z.SolverFor('QF_BV');s.set(timeout=a.seconds*1000,random_seed=1031)
s.add(z.PbEq([(edge[p],1)for p in pairs],m))
for u,v,w in itertools.combinations(range(n),3):s.add(z.Not(z.And(E(u,v),E(v,w),E(u,w))))
for u,v in pairs:
 for x,y in itertools.combinations([i for i in range(n)if i not in [u,v]],2):s.add(z.Not(z.And(E(u,x),E(v,x),E(u,y),E(v,y))))
alpha=n-(k-m+2)
for inds in itertools.combinations(range(n),alpha+1):s.add(z.Or(*[E(u,v)for u,v in itertools.combinations(inds,2)]))
degs=[sum([z.If(E(i,j),z.BitVecVal(1,4),z.BitVecVal(0,4))for j in range(n)if i!=j],z.BitVecVal(0,4))for i in range(n)]
for i in range(n-1):s.add(z.UGE(degs[i],degs[i+1]))
bits=1<<n;ibits=(n+k).bit_length();inputs=[z.BitVecVal(sum(1<<x for x in range(bits)if x>>i&1),bits)for i in range(n)]
w=inputs+[z.BitVec('w'+str(j),bits)for j in range(k)];aa=[z.BitVec('a'+str(j),ibits)for j in range(k)];bb=[z.BitVec('b'+str(j),ibits)for j in range(k)];oo=[z.Bool('o'+str(j))for j in range(k)]
def pick(index,values):
 r=values[-1]
 for i in range(len(values)-2,-1,-1):r=z.If(index==i,values[i],r)
 return r
for j in range(k):
 s.add(z.ULT(aa[j],bb[j]),z.ULT(bb[j],n+j));va=pick(aa[j],w[:n+j]);vb=pick(bb[j],w[:n+j]);s.add(w[n+j]==z.If(oo[j],va|vb,va&vb))
 s.add(w[n+j]!=0,w[n+j]!=(1<<bits)-1)
 for v in w[:n+j]:s.add(w[n+j]!=v)
 if j<k-1:
  s.add(z.Or(*[z.Or(aa[t]==n+j,bb[t]==n+j)for t in range(j+1,k)]))
  code=lambda t:z.Concat(z.If(oo[t],z.BitVecVal(1,1),z.BitVecVal(0,1)),bb[t],aa[t])
  s.add(z.Or(aa[j+1]==n+j,bb[j+1]==n+j,z.ULT(code(j),code(j+1))))
for x in range(bits):s.add((z.Extract(x,x,w[-1])==1)==z.Or(*[edge[u,v]for u,v in pairs if (x>>u&1)and(x>>v&1)]))
print('START variablegraph',n,m,k,'alpha<=',alpha,'timeout',a.seconds,flush=True);t=time.time();r=s.check();print('RESULT',r,'seconds',time.time()-t,flush=True)
if r==z.sat:
 model=s.model();edges=[uv for uv,e in edge.items()if z.is_true(model.eval(e))];gates=[[int(z.is_true(model.eval(oo[j]))),model.eval(aa[j]).as_long(),model.eval(bb[j]).as_long()]for j in range(k)]
 print('EDGES',edges,'GATES',gates,flush=True)
 def ev(x):
  ws=[bool(x>>i&1)for i in range(n)]
  for op,i,j in gates:ws.append((ws[i]or ws[j])if op else(ws[i]and ws[j]))
  return ws[-1]
 errors=[x for x in range(1<<n)if ev(x)!=any((x>>u&1)and(x>>v&1)for u,v in edges)];print('FULL_TABLE_ERRORS',errors,flush=True)
 Path('/tmp/oec/pequalnp-pilot-56/counter_variable_%d_%d_%d_witness.json'%(n,m,k)).write_text(json.dumps({'n':n,'edges':edges,'gates':gates,'errors':errors},indent=2))
print(s.statistics(),flush=True)
