import argparse,builtins,json,math,sys,time,subprocess,re
from pathlib import Path
builtins.Z3_LIB_DIRS=['/tmp/oec/pequalnp-pilot-56/z3-5.3.3-x64-glibc-2.39/bin']
sys.path.insert(0,'/tmp/oec/pequalnp-pilot-56/z3-5.3.3-x64-glibc-2.39/bin/python')
import z3 as z
p=argparse.ArgumentParser();p.add_argument('graph');p.add_argument('gates',type=int);p.add_argument('--seconds',type=int,default=60);p.add_argument('--mode',choices=['any','dirty','badprofile','star'],default='any');p.add_argument('--seed',type=int,default=1031);p.add_argument('--sym',action='store_true');p.add_argument('--ands',type=int);p.add_argument('--ordered',action='store_true');p.add_argument('--backend',choices=['z3','cadical'],default='z3');p.add_argument('--aux-mask',type=int);p.add_argument('--dominance',action='store_true');p.add_argument('--fixed')
a=p.parse_args();d=json.loads(Path(a.graph).read_text());n=d['n'];k=a.gates;pos=d['positive'];neg=d['negative'];rows=pos+neg;bits=len(rows);ibits=(n+k).bit_length()
assert a.mode=='any' and not a.dominance and a.aux_mask is None
auxmasks=d['aux_masks'];targets=[(1<<len(pos))-1]+[sum(1<<r for r,x in enumerate(rows)if x&mask)for mask in auxmasks]
s=z.SolverFor('QF_BV');s.set(timeout=1000*a.seconds,random_seed=a.seed)
inputs=[z.BitVecVal(sum(1<<j for j,x in enumerate(rows)if x>>i&1),bits)for i in range(n)]
w=inputs+[z.BitVec('w'+str(j),bits)for j in range(k)];aa=[z.BitVec('a'+str(j),ibits)for j in range(k)];bb=[z.BitVec('b'+str(j),ibits)for j in range(k)];oo=[z.Bool('o'+str(j))for j in range(k)]
def pick(index,values):
 r=values[-1]
 for i in range(len(values)-2,-1,-1):r=z.If(index==i,values[i],r)
 return r
for j in range(k):
 s.add(z.ULT(aa[j],bb[j]),z.ULT(bb[j],n+j))
 va=pick(aa[j],w[:n+j]);vb=pick(bb[j],w[:n+j]);s.add(w[n+j]==z.If(oo[j],va|vb,va&vb))
 s.add(w[n+j]!=0,w[n+j]!=(1<<bits)-1)
 for v in w[:n+j]:
  s.add(w[n+j]!=v)
  if a.dominance:s.add(z.Or(v&~w[n+j]!=0,w[n+j]&((1<<len(pos))-1)&~v!=0))
 if a.dominance:s.add(w[n+j]&((1<<len(pos))-1)!=0)
 if j<k-1:s.add(z.Or(*[z.Or(aa[t]==n+j,bb[t]==n+j)for t in range(j+1,k)],z.Or(*[w[n+j]==target for target in targets])))
 if j<k-1:
  code=lambda t:z.Concat(bb[t],aa[t],z.If(oo[t],z.BitVecVal(1,1),z.BitVecVal(0,1))) if a.ordered else z.Concat(z.If(oo[t],z.BitVecVal(1,1),z.BitVecVal(0,1)),bb[t],aa[t])
  s.add(z.ULT(code(j),code(j+1)) if a.ordered else z.Or(aa[j+1]==n+j,bb[j+1]==n+j,z.ULT(code(j),code(j+1))))
for target in targets:s.add(z.Or(*[w[n+j]==target for j in range(k)]))
s.add(z.Or(*[w[-1]==target for target in targets]))
if a.aux_mask is not None:s.add(z.Or(*[w[n+j]==sum(1<<r for r,x in enumerate(rows)if x&a.aux_mask)for j in range(k-1)]))
if a.ands is not None:s.add(z.PbEq([(z.Not(x),1)for x in oo],a.ands))
if a.sym:
 adj=[[False]*n for _ in range(n)]
 for u,v in d['edges']:adj[u][v]=adj[v][u]=True
 degree=[sum(r)for r in adj];mapping=[-1]*n;used=[False]*n;autos=[]
 def rec():
  if all(x>=0 for x in mapping):
    if {sum(1<<mapping[u]for u in range(n)if mask>>u&1)for mask in auxmasks}==set(auxmasks):autos.append(mapping.copy())
    return
  u=max((u for u in range(n)if mapping[u]<0),key=lambda u:(sum(adj[u][v]for v in range(n)if mapping[v]>=0),degree[u],-u))
  for v in range(n):
   if used[v]or degree[u]!=degree[v]or(a.aux_mask is not None and (a.aux_mask>>u&1)!=(a.aux_mask>>v&1)):continue
   if any(adj[u][x]!=adj[v][mapping[x]]for x in range(n)if mapping[x]>=0):continue
   mapping[u]=v;used[v]=True;rec();mapping[u]=-1;used[v]=False
 rec()
 reps=set()
 for u in range(n):
  for v in range(u+1,n):reps.add(min(tuple(sorted((q[u],q[v])))for q in autos))
 s.add(z.Or(*[z.And(aa[0]==u,bb[0]==v)for u,v in sorted(reps)]))
 print('AUTOMORPHISMS',len(autos),'first_pair_reps',sorted(reps),flush=True)
if a.mode=='dirty':s.add(z.Or(*[z.And(z.Not(oo[j]),w[n+j]&(((1<<bits)-1)^((1<<len(pos))-1))!=0)for j in range(k)]))
if a.mode in ['badprofile','star']:
 cones=[z.BitVecVal(0,k)for i in range(n)];profiles=[]
 for j in range(k):
  cone=pick(aa[j],cones)|pick(bb[j],cones);cones.append(cone|z.BitVecVal(1<<j,k))
  own=[z.And(z.Extract(e,e,w[n+j])==1,*[z.Implies(z.And(z.Extract(t,t,cone)==1,z.Not(oo[t])),z.Extract(e,e,w[n+t])==0)for t in range(j)])for e in range(len(pos))]
  center=z.Or(*[z.And(*[z.Not(own[e])for e,x in enumerate(pos)if not(x>>i&1)])for i in range(n)])
  profiles.append(z.Or(oo[j],z.And(z.Or(*own),center)))
 if a.mode=='star':s.add(*profiles)
 else:s.add(z.Not(z.And(*profiles)))
if a.fixed:
 fixed=json.loads(Path(a.fixed).read_text())['gates'];assert len(fixed)==k
 for j,(op,u,v)in enumerate(fixed):s.add(oo[j]==bool(op),aa[j]==u,bb[j]==v)
print('START',d['name'],'n',n,'k',k,'rows',bits,'mode',a.mode,'timeout',a.seconds,flush=True)
t=time.time();gates=None
if a.backend=='z3':
 r=s.check();print('RESULT',r,'seconds',time.time()-t,flush=True)
 if r==z.sat:
  model=s.model();gates=[[int(z.is_true(model.eval(oo[j]))),model.eval(aa[j]).as_long(),model.eval(bb[j]).as_long()]for j in range(k)]
else:
 goal=z.Goal();goal.add(*s.assertions());markers={}
 for label,vecs in [('a',aa),('b',bb)]:
  for j,vec in enumerate(vecs):
   for bit in range(ibits):
    name='mark_'+label+str(j)+'_'+str(bit);bo=z.Bool(name);markers[name]=(label,j,bit);goal.add(bo==(z.Extract(bit,bit,vec)==1))
 cnf=z.Then('simplify','bit-blast','tseitin-cnf')(goal)[0].dimacs()
 stem='counter_multi_cnf_'+d['name']+'_'+str(k)+'_'+a.mode+('_ordered'if a.ordered else'')+('_a'+str(a.ands)if a.ands is not None else'')+('_dominance'if a.dominance else'')
 cnfpath=Path('/tmp/oec/pequalnp-pilot-56')/(stem+'.cnf');cnfpath.write_text(cnf)
 outpath=cnfpath.with_suffix('.out');errpath=cnfpath.with_suffix('.err')
 print('CNF',len(cnf),'bytes',flush=True)
 with outpath.open('w')as out,errpath.open('w')as err:
  rr=subprocess.run(['/tmp/oec/pequalnp-pilot-56/lean-4.36.0-linux/bin/cadical','-t',str(a.seconds),str(cnfpath)],stdout=out,stderr=err)
 result=outpath.read_text();r=z.sat if 's SATISFIABLE' in result else z.unsat if 's UNSATISFIABLE' in result else z.unknown
 print('RESULT',r,'seconds',time.time()-t,'exit',rr.returncode,flush=True)
 if r==z.sat:
  values={abs(int(v)):int(v)>0 for line in result.splitlines()if line.startswith('v ')for v in line[2:].split()if int(v)}
  names={line.split(maxsplit=2)[2]:int(line.split()[1])for line in cnf.splitlines()if line.startswith('c ')}
  gates=[]
  for j in range(k):
   g=[int(values[names['o'+str(j)]])]
   for label in ['a','b']:g.append(sum((1<<bit)*values[names['mark_'+label+str(j)+'_'+str(bit)]]for bit in range(ibits)))
   gates.append(g)
if gates is not None: 
 print('GATES',json.dumps(gates),flush=True)
 def ev(x):
  ws=[bool(x>>i&1)for i in range(n)]
  for op,i,j in gates:ws.append((ws[i]or ws[j])if op else(ws[i]and ws[j]))
  return ws
 tables=[ev(x)for x in range(1<<n)]
 required=[[any((x>>u&1)and(x>>v&1)for u,v in d['edges'])for x in range(1<<n)]]+[[bool(x&mask)for x in range(1<<n)]for mask in auxmasks]
 outputs=[next((j for j in range(n,n+k)if all(tables[x][j]==values[x]for x in range(1<<n))),None)for values in required]
 errors=[i for i,v in enumerate(outputs)if v is None]
 print('OUTPUTS',outputs,flush=True)
 print('FULL_TABLE_ERRORS',errors,flush=True)
 out=Path('/tmp/oec/pequalnp-pilot-56')/('counter_multi_sat_'+d['name']+'_'+str(k)+'_'+a.mode+'_witness.json');out.write_text(json.dumps({'graph':d,'gates':gates,'errors':errors,'outputs':outputs},indent=2))
print(s.statistics(),flush=True)
