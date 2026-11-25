import sys,time,json,subprocess,os,hashlib
from pathlib import Path
from datetime import datetime,timezone
sys.path.insert(0,'/tmp/oec/pequalnp-pilot-152/z3-python')
import z3
smt=Path(sys.argv[1]);spec=json.loads(Path(sys.argv[2]).read_text());m=int(sys.argv[3]);q=int(sys.argv[4]);seconds=int(sys.argv[5]);base=Path(sys.argv[6])
n=spec['n'];L=m-2*q+1;iw=(n+m).bit_length();assert L>=1 and q>=1
print(datetime.now(timezone.utc).isoformat(),'BEGIN',smt.name,'size',m,'q',q,'Z3',z3.get_version_string(),flush=True)
start=time.monotonic();original=list(z3.parse_smt2_file(str(smt)));g=z3.Goal(models=True);g.add(*original)
result=z3.Then('simplify','bit-blast','tseitin-cnf')(g);assert len(result)==1;cnfgoal=result[0];dimacs=cnfgoal.dimacs()
raw=dimacs.encode();assert len(raw)<100*1024*1024
fs=os.statvfs(str(base.parent));assert fs.f_bavail*fs.f_frsize>len(raw)+220*1024*1024
cnfpath=base.with_suffix('.cnf');cnfpath.write_bytes(raw)
print('CNF_READY',len(raw),'bytes','seconds',round(time.monotonic()-start,3),'sha256',hashlib.sha256(raw).hexdigest(),flush=True)
cnfvars={};clauses=[];declared=None
for line in dimacs.splitlines():
 if line.startswith('p '):declared=tuple(map(int,line.split()[2:4]))
 elif line.startswith('c '):
  _,num,name=line.split(maxsplit=2);cnfvars[int(num)]=name
 elif line.strip():
  ints=list(map(int,line.split()));assert ints[-1]==0;clauses.append(ints[:-1])
assert declared and len(clauses)==declared[1]
stdout=base.with_suffix('.cadical.stdout');stderr=base.with_suffix('.cadical.stderr')
command=['/tmp/oec/pequalnp-pilot-152/toolchain/lean-4.36.0-linux/bin/cadical','-t',str(seconds),str(cnfpath)]
with stdout.open('w') as out,stderr.open('w') as err:proc=subprocess.run(command,stdout=out,stderr=err)
text=stdout.read_text();status='UNSAT' if 's UNSATISFIABLE' in text else 'SAT' if 's SATISFIABLE' in text else 'UNKNOWN'
metadata=dict(smt_file=smt.name,smt_sha256=hashlib.sha256(smt.read_bytes()).hexdigest(),cnf_sha256=hashlib.sha256(raw).hexdigest(),cnf_bytes=len(raw),cnf_variables=declared[0],cnf_clauses=declared[1],status=status,returncode=proc.returncode,seconds=time.monotonic()-start,proof_enabled=False)
print('CADICAL_RESULT',status,'returncode',proc.returncode,'seconds',round(metadata['seconds'],3),flush=True)
if status=='SAT':
 assigned={}
 for line in text.splitlines():
  if line.startswith('v '):
   for lit in map(int,line.split()[1:]):
    if lit:assigned[abs(lit)]=lit>0
 assert all(any(assigned[abs(lit)]==(lit>0) for lit in clause) for clause in clauses)
 atoms={}
 for clause in cnfgoal:
  literals=list(clause.children()) if z3.is_or(clause) else [clause]
  for lit in literals:
   atom=lit.arg(0) if z3.is_not(lit) else lit
   assert z3.is_const(atom) and z3.is_bool(atom) and not z3.is_true(atom) and not z3.is_false(atom)
   name=str(atom.decl().name());assert name not in atoms or z3.eq(atoms[name],atom);atoms[name]=atom
 # Internal bit-blast constants are omitted by an ordinary Solver model in this Z3 version.
 # Populate their interpretations explicitly before invoking the stored model converter.
 boolmodel=z3.Model()
 for num,name in cnfvars.items():boolmodel.update_value(atoms[name],z3.BoolVal(assigned[num]))
 model=cnfgoal.convert_model(boolmodel)
 assert all(z3.is_true(model.eval(a,model_completion=True)) for a in original)
 gates=[]
 for i in range(L):
  op='or' if z3.is_true(model.eval(z3.Bool('or'+str(i)),model_completion=True)) else 'and'
  a=model.eval(z3.BitVec('a'+str(i),iw),model_completion=True).as_long();b=model.eval(z3.BitVec('b'+str(i),iw),model_completion=True).as_long();gates.append([op,a,b])
 for i in range(q):
  a=model.eval(z3.BitVec('ta'+str(i),iw),model_completion=True).as_long();b=model.eval(z3.BitVec('tb'+str(i),iw),model_completion=True).as_long();gates.append(['and',a,b])
 output=n+L
 for i in range(1,q):gates.append(['or',*sorted([output,n+L+i])]);output=n+len(gates)-1
 assert len(gates)==m and output==n+m-1
 edges=[tuple(e) for e in spec['edges']];neighbors=[set() for _ in range(n)]
 for a,b in edges:assert a!=b and spec['colors'][a]!=spec['colors'][b];neighbors[a].add(b);neighbors[b].add(a)
 assert all(len(neighbors[a]&neighbors[b])<=1 for a in range(n) for b in range(a))
 values=[sum(1<<x for x in range(1<<n) if x>>i&1) for i in range(n)];F=sum(1<<x for x in range(1<<n) if any(x>>a&1 and x>>b&1 for a,b in edges));mask=(1<<(1<<n))-1
 for i,(op,a,b) in enumerate(gates):
  assert 0<=a<n+i and 0<=b<n+i
  values.append(values[a]|values[b] if op=='or' else values[a]&values[b])
 assert values[-1]==F
 below=[v&(mask^F)==0 for v in values];dirty=[i for i,(op,a,b) in enumerate(gates) if op=='and' and not below[n+i]];assert dirty
 assert all(op!='or' or below[a]==below[b] for op,a,b in gates)
 minima=[(1<<a)|(1<<b) for a,b in edges]
 for fault,(op,fa,fb) in enumerate(gates):
  for replacement in [None,fa,fb]:
   altered=values[:n]
   for i,(operation,a,b) in enumerate(gates):altered.append((0 if replacement is None else altered[replacement]) if i==fault else (altered[a]&altered[b] if operation=='and' else altered[a]|altered[b]))
   assert altered[-1]!=F
   if replacement is None:assert any(not(altered[-1]>>x&1) for x in minima)
 from itertools import combinations
 cover=next(S for k in range(n+1) for S in combinations(range(n),k) if all(a in S or b in S for a,b in edges))
 data=dict(n=n,edges=edges,bipartition=spec['colors'],gates=gates,output=output,dirty_and_indices=dirty,below_gate=below[n:],cover=list(cover),standard_bound=len(edges)+len(cover)-1,clean_ands=q,dirty_ands=len(dirty))
 base.with_suffix('.model.json').write_text(json.dumps(data,indent=2)+'\n');metadata.update(original_assertions_verified=len(original),full_assignments_verified=1<<n,gate_count=m,dirty_and_indices=dirty)
 print('SAT_MODEL_FULLY_VERIFIED',json.dumps(data),flush=True)
base.with_suffix('.metadata.json').write_text(json.dumps(metadata,indent=2)+'\n')
print('FINISHED',datetime.now(timezone.utc).isoformat(),flush=True)
