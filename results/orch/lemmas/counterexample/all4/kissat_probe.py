import argparse,json,subprocess,time,z3,re
from pathlib import Path
from datetime import datetime,timezone
ap=argparse.ArgumentParser();ap.add_argument('--smt',required=True);ap.add_argument('--tag',default='');ap.add_argument('--replay',action='store_true');ap.add_argument('--seconds',type=int,default=120);ap.add_argument('--binary',default='/tmp/oec/pequalnp-pilot-40/kissat/kissat-4.0.4-linux-amd64');a=ap.parse_args()
base=Path(__file__).resolve().parent;smt=Path(a.smt);key=(a.tag+'_'if a.tag else'')+smt.stem+'_kissat';original=z3.parse_smt2_file(str(smt));goal=z3.Goal(models=True);goal.add(original);goals=z3.Then('simplify','bit-blast','tseitin-cnf')(goal);assert len(goals)==1;cnfgoal=goals[0]
atoms=[];ids={};clauses=[]
for term in cnfgoal:
 if z3.is_true(term):continue
 if z3.is_false(term):clauses.append([]);continue
 clause=[];tautology=False;lits=list(term.children())if z3.is_or(term)else[term]
 for lit in lits:
  lit=z3.simplify(lit)
  if z3.is_true(lit):tautology=True;break
  if z3.is_false(lit):continue
  neg=z3.is_not(lit);atom=lit.arg(0)if neg else lit;assert z3.is_const(atom)and atom.sort()==z3.BoolSort()
  if atom.get_id()not in ids:ids[atom.get_id()]=len(atoms)+1;atoms.append(atom)
  v=ids[atom.get_id()];clause.append(-v if neg else v)
 if not tautology:clauses.append(clause)
cnf=base/(key+'.cnf');cnf.write_text(f'p cnf {len(atoms)} {len(clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n'for c in clauses))
(base/(key+'.atoms.json')).write_text(json.dumps([str(x)for x in atoms])+'\n')
beg=time.monotonic()
if a.replay:
 from types import SimpleNamespace
 old=(base/(key+'.stdout')).read_text();r=SimpleNamespace(returncode=10 if 's SATISFIABLE' in old else 20 if 's UNSATISFIABLE' in old else 0)
else:
 with(base/(key+'.stdout')).open('w')as f:r=subprocess.run([a.binary,f'--time={a.seconds}','--statistics',str(cnf)],stdout=f,stderr=subprocess.STDOUT)
text=(base/(key+'.stdout')).read_text();out={'tag':a.tag,'replayed':a.replay,'at':datetime.now(timezone.utc).isoformat(),'smt':smt.name,'solver':'kissat4.0.4','exit_code':r.returncode,'result':{10:'sat',20:'unsat',0:'unknown'}.get(r.returncode,'error'),'seconds':round(time.monotonic()-beg,3),'variables':len(atoms),'clauses':len(clauses)}
if r.returncode==10:
 literals=[int(x)for ln in text.splitlines()if ln.startswith('v ')for x in ln[2:].split()if x!='0'];ass={abs(v):v>0 for v in literals};assert all(any(ass.get(abs(v))==(v>0)for v in c)for c in clauses)
 bitmodel=z3.Model()
 for i,atom in enumerate(atoms):bitmodel.update_value(atom,z3.BoolVal(ass.get(i+1,False)))
 model=cnfgoal.convert_model(bitmodel);bad=[str(f)for f in original if not z3.is_true(model.eval(f,model_completion=True))]
 if bad:
  (base/(key+'.bad-model.json')).write_text(json.dumps({'model':str(model),'failed':bad},indent=2));raise AssertionError('converted model violates original constraints')
 match=re.fullmatch(r'(g\d+)_(free|clean|formula)_atmost(\d+)',smt.stem);assert match;gid,kind,bound=match.group(1),match.group(2),int(match.group(3));D=json.loads((base/'classes.json').read_text());N=D['N'];n=2*N;R=1<<n;g=next(q for q in D['classes']if q['id']==gid);edges=[tuple(e)for e in g['edges']];bits=(n+bound-1).bit_length();vals=[sum(1<<r for r in range(R)if r>>i&1)for i in range(n)];circ=[];active=[];mask=sum(1<<(1<<i)for i in range(n))|sum(1<<((1<<i)|(1<<(N+j)))for i in range(N)for j in range(N)if(i,j)not in edges)
 for j in range(bound):
  av=model.eval(z3.BitVec(f'a{j}',bits)).as_long();bv=model.eval(z3.BitVec(f'b{j}',bits)).as_long();op=z3.is_true(model.eval(z3.Bool(f'and{j}')));act=z3.is_true(model.eval(z3.Bool(f'active{j}')));assert av<=bv<n+j;v=vals[av]&vals[bv]if op else vals[av]|vals[bv];vals.append(v);circ.append(['and'if op else'or',av,bv]);active.append(act);assert not(kind=='clean'and op and v&mask)
 assert vals[-1]==sum(1<<r for r in range(R)if any((r>>i&1)and(r>>(N+j)&1)for i,j in edges));out.update(id=gid,bound=bound,active_gates=sum(active),circuit=circ[:sum(active)])
 if kind=='formula':
  for j in range(sum(active)):assert sum((av==n+j)+(bv==n+j)for _,av,bv in circ[:sum(active)])<=1
 (base/(key+'.model.txt')).write_text(str(model)+'\n')
 if kind=='free'and bound<g['clean_upper']:(base/'CANDIDATE.json').write_text(json.dumps(out,indent=2)+'\n')
(base/(key+'.json')).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
