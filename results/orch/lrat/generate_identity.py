import argparse,json,subprocess
from pathlib import Path
from export_rup import export

ap=argparse.ArgumentParser()
ap.add_argument('witness',type=Path)
ap.add_argument('directory',type=Path)
ap.add_argument('--solver',type=Path,required=True)
ap.add_argument('--prefix',default='PEqualNP.Outside.L_meta_2602_aux.sat_candidate')
a=ap.parse_args();a.directory.mkdir(exist_ok=True)
w=json.loads(a.witness.read_text());gates=w['gates'][:]
assert all(op in ('and','or') and 0<=u<26+i and 0<=v<26+i and u!=v for i,(op,u,v) in enumerate(gates))
assert 0<=w['output']<26+len(gates)
roots=[]
for p in range(13):
 for l in range(13):
  if (p-l)%13 in (0,1,3,9):
   roots.append(26+len(gates));gates.append(['and',p,13+l])
out=roots[0]
for root in roots[1:]:
 gates.append(['or',out,root]);out=26+len(gates)-1
clauses=[]
for i,(op,u,v) in enumerate(gates):
 z=27+i;u+=1;v+=1
 clauses.extend([[-z,u],[-z,v],[z,-u,-v]] if op=='and' else [[z,-u],[z,-v],[-z,u,v]])
x=w['output']+1;y=out+1
clauses.extend([[x,y],[-x,-y]])
cnf=a.directory/'identity.cnf';lrat=a.directory/'identity.lrat'
cnf.write_text(f'p cnf {26+len(gates)} {len(clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in clauses))
with (a.directory/'cadical.log').open('w') as log:
 r=subprocess.run([str(a.solver),'--lrat=true','--binary=false',str(cnf),str(lrat)],stdout=log,stderr=subprocess.STDOUT)
assert r.returncode==20,f'Expected UNSAT20, got{r.returncode}; inspect cadical.log'
s=export(cnf,lrat,a.prefix+'_unsat')
s=s[:s.index('\n#print axioms')]
s+='\nnamespace PEqualNP.Outside.L_meta_2602_aux\n\n'
s+=(Path(__file__).parent/'bool-clause-lemmas.lean.inc').read_text()
s+='\nend PEqualNP.Outside.L_meta_2602_aux\n\n'
s+=f'open PEqualNP.Outside.L_meta_2602_aux in\ntheorem {a.prefix}_identity (w : Nat → Bool)\n'
for i,(op,u,v) in enumerate(gates):
 z=26+i;oper='&&' if op=='and' else '||'
 s+=f'    (h{z} : w {z} = (w {u} {oper} w {v}))\n'
s+=f'    : w {x-1} = w {y-1} := by\n  by_contra h\n  exact {a.prefix}_unsat (fun i => w i = true)\n'
for i,(op,u,v) in enumerate(gates):
 z=26+i
 for part in ['left','right','out']:s+=f'    (sat_{op}_{part} (w {u}) (w {v}) (w {z}) h{z})\n'
for part in ['left','right']:s+=f'    (sat_xor_{part} (w {x-1}) (w {y-1}) h)\n'
s+=f'\n#print axioms {a.prefix}_identity\n'
(a.directory/'Identity.lean').write_text(s)
(a.directory/'metadata.json').write_text(json.dumps({'variables':26+len(gates),'gates':gates,'clauses':len(clauses),'original_output':x-1,'dnf_output':y-1},indent=2))
print(f'Generated {len(s.splitlines())} lines, {len(s)} bytes')
