import argparse,json,time,z3,subprocess,sys
from pathlib import Path
from itertools import permutations
from datetime import datetime,timezone
p=argparse.ArgumentParser();p.add_argument('--id',required=True);p.add_argument('--clean',action='store_true');p.add_argument('--formula',action='store_true');p.add_argument('--timeout',type=int,default=180);p.add_argument('--bound',type=int);a=p.parse_args()
base=Path(__file__).resolve().parent;data=json.loads((base/'classes.json').read_text());N=data['N'];n=2*N;g=next(d for d in data['classes']if d['id']==a.id);edges=[tuple(e)for e in g['edges']];s=a.bound if a.bound is not None else g['clean_upper']-1
assert edges and s>=1
R=1<<n;target=lambda r:any((r>>i&1)and(r>>(N+j)&1)for i,j in edges)
forbidden={1<<i for i in range(n)}|{(1<<i)|(1<<(N+j))for i in range(N)for j in range(N)if(i,j)not in edges}
assignments=sorted(forbidden|{(1<<i)|(1<<(N+j))for i,j in edges}|{r for r in range(R)if not target(r)and all(target(r|(1<<i))for i in range(n)if not r>>i&1)})
width=len(assignments);idxbits=(n+s-1).bit_length();targetbits=sum(1<<k for k,r in enumerate(assignments)if target(r));fbd=sum(1<<k for k,r in enumerate(assignments)if r in forbidden);inputs=[z3.BitVecVal(sum(1<<k for k,r in enumerate(assignments)if r>>i&1),width)for i in range(n)]
solver=z3.SolverFor('QF_BV');solver.set(timeout=1000*a.timeout)
aidx=[z3.BitVec(f'a{j}',idxbits)for j in range(s)];bidx=[z3.BitVec(f'b{j}',idxbits)for j in range(s)];w=[z3.BitVec(f'w{j}',width)for j in range(s)];op=[z3.Bool(f'and{j}')for j in range(s)];active=[z3.Bool(f'active{j}')for j in range(s)]
solver.add(active[0])
# Every essential input must reach the output through the live binary DAG.
if g['active_vertices']>1 and g['active_vertices']-2<s:solver.add(active[g['active_vertices']-2])
for i,d in enumerate(g['degrees']):
 if d:solver.add(z3.Or([z3.And(active[j],z3.Or(aidx[j]==i,bidx[j]==i))for j in range(s)]))
# Isolated input variables can be fixed to false and constants eliminated.
isolated=[i for i,d in enumerate(g['degrees'])if d==0]
for j in range(s):
 solver.add(z3.ULT(bidx[j],n+j),z3.Implies(active[j],z3.ULT(aidx[j],bidx[j])))
 for k in isolated:solver.add(z3.Implies(active[j],z3.And(aidx[j]!=k,bidx[j]!=k)))
 if j:
  solver.add(z3.Implies(active[j],active[j-1]),z3.Implies(z3.Not(active[j]),z3.And(aidx[j]==n+j-1,bidx[j]==n+j-1,z3.Not(op[j]))))
 def mux(selector):
  terms=inputs+w[:j];r=terms[-1]
  for k in reversed(range(len(terms)-1)):r=z3.If(selector==k,terms[k],r)
  return r
 x=mux(aidx[j]);y=mux(bidx[j]);solver.add(w[j]==z3.If(op[j],x&y,x|y))
 redundants=inputs+[x,y] if a.formula else inputs+w[:j]
 solver.add(z3.Implies(active[j],z3.And([w[j]!=v for v in redundants])))
 if a.clean:solver.add(z3.Implies(op[j],w[j]&fbd==0))
 if j<s-1:
  used=z3.Or([z3.And(active[k],z3.Or(aidx[k]==n+j,bidx[k]==n+j))for k in range(j+1,s)])
  solver.add(z3.Implies(active[j],z3.Or(z3.Not(active[j+1]),used)))
if a.formula:
 for j in range(s):
  occurrences=[z3.If(z3.And(active[k],src[k]==n+j),1,0)for k in range(j+1,s)for src in [aidx,bidx]]
  if occurrences:solver.add(z3.Sum(occurrences)<=1)
for j in range(s-1):
 independent=z3.And(active[j],active[j+1],aidx[j+1]!=n+j,bidx[j+1]!=n+j)
 lex=z3.Or(z3.ULT(aidx[j],aidx[j+1]),z3.And(aidx[j]==aidx[j+1],z3.Or(z3.ULT(bidx[j],bidx[j+1]),z3.And(bidx[j]==bidx[j+1],z3.Or(op[j],z3.Not(op[j+1]))))))
 solver.add(z3.Implies(independent,lex))
# Quotient the first source pair by genuine input automorphisms of this graph.
automorphisms=[];es=set(edges)
for rp in permutations(range(N)):
 for cp in permutations(range(N)):
  if {(rp[i],cp[j])for i,j in edges}==es:automorphisms.append(tuple(rp)+tuple(N+j for j in cp))
  if {(cp[j],rp[i])for i,j in edges}==es:automorphisms.append(tuple(N+i for i in rp)+tuple(cp))
allowed=[]
for i in range(n):
 for j in range(i+1,n):
  if (i,j)==min(tuple(sorted((au[i],au[j])))for au in automorphisms):allowed.append(z3.And(aidx[0]==i,bidx[0]==j))
solver.add(z3.Or(allowed));solver.add(w[-1]==targetbits)
key=f'{a.id}_{"formula"if a.formula else"clean"if a.clean else"free"}_atmost{s}';(base/(key+'.smt2')).write_text(solver.to_smt2())
beg=time.monotonic();r=solver.check();elapsed=time.monotonic()-beg
out={'encoding_version':4,'formula':a.formula,'at':datetime.now(timezone.utc).isoformat(),'id':a.id,'rows':g['rows'],'edges':edges,'bound':s,'clean':a.clean,'result':str(r),'seconds':round(elapsed,3),'boundary_rows':width,'automorphisms':len(automorphisms),'reason':solver.reason_unknown()if r==z3.unknown else None}
if r==z3.sat:
 m=solver.model();vals=[sum(1<<r for r in range(R)if r>>i&1)for i in range(n)];circ=[];isactive=[];fb=sum(1<<r for r in forbidden)
 for j in range(s):
  av=m.eval(aidx[j]).as_long();bv=m.eval(bidx[j]).as_long();opv=z3.is_true(m.eval(op[j]));act=z3.is_true(m.eval(active[j]));assert av<=bv<n+j;v=vals[av]&vals[bv]if opv else vals[av]|vals[bv];vals.append(v);circ.append(['and'if opv else'or',av,bv]);isactive.append(act);assert not(a.clean and opv and v&fb)
 assert vals[-1]==sum(1<<r for r in range(R)if target(r));out['active_gates']=sum(isactive);out['circuit']=circ[:sum(isactive)];out['padded_circuit']=circ
 if a.formula:
  active_circ=circ[:sum(isactive)]
  for j in range(len(active_circ)):assert sum((av==n+j)+(bv==n+j)for _,av,bv in active_circ)<=1
 (base/(key+'.model.txt')).write_text(str(m)+'\n')
(base/(key+'.log')).write_text(str(solver.statistics())+'\n');(base/(key+'.json')).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)

# One sequential formula probe per requested graph, within this existing worker.
if a.id=='g51795' and not a.formula and r==z3.unknown:
 for gid in ['g51795','g59731']:
  with(base/(gid+'-formula-run.log')).open('w')as f:
   subprocess.run([sys.executable,str(Path(__file__).resolve()),'--id',gid,'--formula','--timeout','60'],stdout=f,stderr=subprocess.STDOUT,check=True)

if a.id=='g51795' and not a.formula and r==z3.unknown:
 for smtname,seconds in [('g12544_free_atmost3.smt2',5),('g12544_free_atmost5.smt2',5),('g59731_free_atmost11.smt2',120),('g54833_free_atmost10.smt2',120)]:
  with(base/(Path(smtname).stem+'-kissat-run.log')).open('w')as f:
   subprocess.run([sys.executable,str(base/'kissat_probe.py'),'--smt',str(base/smtname),'--seconds',str(seconds)],stdout=f,stderr=subprocess.STDOUT,check=True)
  if(base/'CANDIDATE.json').exists():break

if not a.formula and r!=z3.sat and a.id!='g51795':
 marker=base/'kissat_batch_started.txt'
 try:
  with marker.open('x')as f:f.write(datetime.now(timezone.utc).isoformat()+'\n')
  owns_probe=True
 except FileExistsError:owns_probe=False
 if owns_probe:
  for smtname,seconds in [('g12544_free_atmost3.smt2',5),('g12544_free_atmost5.smt2',5),('g59731_free_atmost11.smt2',120),('g54833_free_atmost10.smt2',120)]:
   with(base/(Path(smtname).stem+'-kissat-run.log')).open('w')as f:
    subprocess.run([sys.executable,str(base/'kissat_probe.py'),'--smt',str(base/smtname),'--seconds',str(seconds)],stdout=f,stderr=subprocess.STDOUT,check=True)
   if(base/'CANDIDATE.json').exists():break
