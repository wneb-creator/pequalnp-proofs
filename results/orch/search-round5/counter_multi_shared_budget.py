import argparse,builtins,json,sys,subprocess,time
from pathlib import Path
builtins.Z3_LIB_DIRS=['/tmp/oec/pequalnp-pilot-56/z3-5.3.3-x64-glibc-2.39/bin']
sys.path.insert(0,'/tmp/oec/pequalnp-pilot-56/z3-5.3.3-x64-glibc-2.39/bin/python')
import z3 as z
p=argparse.ArgumentParser();p.add_argument('graph');p.add_argument('k',type=int);p.add_argument('--count',choices=['and','or'],default='and');p.add_argument('--seconds',type=int,default=120);p.add_argument('--disjoint',action='store_true');p.add_argument('--free-budget',type=int,required=True);p.add_argument('--fixed');a=p.parse_args();assert a.disjoint;d=json.loads(Path(a.graph).read_text());n=d['n'];k=a.k;rows=d['positive']+d['negative'];R=len(rows);P=len(d['positive']);andcount=a.count=='and';s=z.SolverFor('QF_BV');full=(1<<R)-1
w=[z.BitVecVal(sum(1<<r for r,x in enumerate(rows)if x>>i&1),R)for i in range(n)]+[z.BitVecVal(0,R),z.BitVecVal(full,R)]
selectors=[]
def cone(name,ws):
 ss=[z.Bool(name+'_'+str(i))for i in range(len(ws))];selectors.append((name,ss));v=z.BitVecVal(0 if andcount else full,R)
 for sel,q in zip(ss,ws):
  v=(v|z.If(sel,q,z.BitVecVal(0,R)))if andcount else(v&z.If(sel,q,z.BitVecVal(full,R)))
 return v,ss
for j in range(k):
 l,ls=cone('l'+str(j),w);r,rs=cone('r'+str(j),w);v=z.BitVec('w'+str(j),R);s.add(v==(l&r if andcount else l|r));w.append(v)
 if a.disjoint:
  s.add(z.Or(*ls),z.Or(*rs))
  for u,vv in zip(ls,rs):s.add(z.Not(z.And(u,vv)))
  for i in [n,n+1]:s.add(z.Not(ls[i]),z.Not(rs[i]))
 # Commutativity: compare each subset as a binary selector word.
 lw=z.Concat(*[z.If(b,z.BitVecVal(1,1),z.BitVecVal(0,1))for b in ls]);rw=z.Concat(*[z.If(b,z.BitVecVal(1,1),z.BitVecVal(0,1))for b in rs]);s.add(z.ULE(lw,rw))
targets=[(1<<P)-1]+[sum(1<<r for r,x in enumerate(rows)if x&mask)for mask in d['aux_masks']]
output_selectors=[]
for j,target in enumerate(targets):
 out,os=cone('out'+str(j),w);s.add(out==target);output_selectors.append(os)
if a.disjoint:
 for os in output_selectors:s.add(z.Not(os[n]),z.Not(os[n+1]))
 adj=[[False]*n for _ in range(n)]
 for u,v in d['edges']:adj[u][v]=adj[v][u]=True
 degree=[sum(r)for r in adj];mapping=[-1]*n;used=[False]*n;autos=[]
 def rec():
  if all(x>=0 for x in mapping):
    if {sum(1<<mapping[u]for u in range(n)if mask>>u&1)for mask in d['aux_masks']}==set(d['aux_masks']):autos.append(mapping.copy())
    return
  u=max((u for u in range(n)if mapping[u]<0),key=lambda u:(sum(adj[u][v]for v in range(n)if mapping[v]>=0),degree[u],-u))
  for v in range(n):
   if used[v]or degree[u]!=degree[v]:continue
   if any(adj[u][x]!=adj[v][mapping[x]]for x in range(n)if mapping[x]>=0):continue
   mapping[u]=v;used[v]=True;rec();mapping[u]=-1;used[v]=False
 rec();reps={min(tuple(sorted((q[u],q[v])))for q in autos)for u in range(n)for v in range(u+1,n)}
 ls=selectors[0][1];rs=selectors[1][1];s.add(z.Or(*[z.Or(z.And(ls[u],rs[v]),z.And(ls[v],rs[u]))for u,v in reps]))
 print('DISJOINT first-pair orbits',sorted(reps),'automorphisms',len(autos),flush=True)
for os in output_selectors:s.add(z.Or(*os))
allbits=[b for _,bs in selectors for b in bs]
width=(len(allbits)+1).bit_length()
words=[];cost=z.BitVecVal(0,width)
for _,bs in selectors:
 padded=bs+[z.BoolVal(False)]*(n+2+k-len(bs))
 word=z.Concat(*[z.If(b,z.BitVecVal(1,1),z.BitVecVal(0,1))for b in padded])
 fresh=z.And(*[word!=prev for prev in words]);words.append(word)
 cardinal=sum((z.If(b,z.BitVecVal(1,width),z.BitVecVal(0,width))for b in bs),z.BitVecVal(0,width))
 cost=cost+z.If(fresh,cardinal-1,z.BitVecVal(0,width))
s.add(z.ULE(cost,z.BitVecVal(a.free_budget,width)))
if a.fixed:
 fixed=json.loads(Path(a.fixed).read_text());assert set(fixed)=={name for name,_ in selectors}
 for name,bs in selectors:
  for i,b in enumerate(bs):s.add(b==(i in fixed[name]))
goal=z.Goal();goal.add(*s.assertions());cnf=z.Then('simplify','bit-blast','tseitin-cnf')(goal)[0].dimacs();base=Path('/tmp/oec/pequalnp-pilot-56');stem='counter_multi_shared_'+d['name']+'_'+a.count+str(k)+('_disjoint'if a.disjoint else'')+'_budget'+str(a.free_budget)+('_fixed'if a.fixed else'');cp=base/(stem+'.cnf');cp.write_text(cnf);op=base/(stem+'.out');ep=base/(stem+'.err')
print('START',d['name'],a.count,k,'rows',R,'cnfbytes',len(cnf),flush=True);t=time.time()
with op.open('w')as of,ep.open('w')as ef:rr=subprocess.run(['/tmp/oec/pequalnp-pilot-56/lean-4.36.0-linux/bin/cadical','-t',str(a.seconds),str(cp)],stdout=of,stderr=ef)
text=op.read_text();status='sat'if's SATISFIABLE'in text else'unsat'if's UNSATISFIABLE'in text else'unknown';print('RESULT',status,'seconds',time.time()-t,'exit',rr.returncode,flush=True)
if status=='sat':
 values={abs(int(v)):int(v)>0 for line in text.splitlines()if line.startswith('v ')for v in line[2:].split()if int(v)};names={line.split(maxsplit=2)[2]:int(line.split()[1])for line in cnf.splitlines()if line.startswith('c ')}
 sels={name:[i for i,b in enumerate(bs)if values.get(names.get(str(b),0),False)]for name,bs in selectors};print('SUBSETS',json.dumps(sels),flush=True)
 def evaluate(x):
  ww=[bool(x>>i&1)for i in range(n)]+[False,True]
  for j in range(k):
   left=[ww[i]for i in sels['l'+str(j)]];right=[ww[i]for i in sels['r'+str(j)]]
   ww.append((any(left)and any(right))if andcount else(all(left)or all(right)))
  return [(any(ww[i]for i in sels['out'+str(j)])if andcount else all(ww[i]for i in sels['out'+str(j)]))for j in range(len(targets))]
 errors=[x for x in range(1<<n)if evaluate(x)!=[any((x>>u&1)and(x>>v&1)for u,v in d['edges'])]+[bool(x&mask)for mask in d['aux_masks']]];print('FULL_TABLE_ERRORS',errors,flush=True)
 (base/(stem+'_witness.json')).write_text(json.dumps({'graph':d,'basis':a.count,'k':k,'subsets':sels,'errors':errors,'free_budget':a.free_budget,'naive_free_count':sum(max(0,len(q)-1)for q in sels.values()),'dedup_free_count':sum(len(q)-1 for q in {tuple(q)for q in sels.values()})},indent=2))
