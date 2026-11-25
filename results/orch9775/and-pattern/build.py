import json,itertools
from pathlib import Path
rows=json.loads(Path('results/orch9775/kw_formula_lp.json').read_text())['negative_masks']
cs=[];nv=84+6*len(rows)
def m(p,g,b):return 1+12*p+2*g+b
def f(r,g):return 85+6*r+g
for p in range(7):
 lits=[m(p,g,b) for g in range(6) for b in range(2)]
 cs.append(lits)
 for triple in itertools.combinations(lits,3):cs.append([-a for a in triple])
 for g in range(6):cs.append([-m(p,g,0),-m(p,g,1)])
for r,I in enumerate(rows):
 for p in range(7):
  if I>>p&1:
   for g in range(6):
    for b in range(2):cs.append([-m(p,g,b), -f(r,g) if b else f(r,g)])
  else:
   terms=[]
   for g in range(6):
    for b in range(2):
     nv+=1;z=nv;lit=f(r,g) if b else -f(r,g);memb=m(p,g,b)
     cs += [[-z,memb],[-z,lit],[z,-memb,-lit]];terms.append(z)
   cs.append(terms)
p=Path('/tmp/oec/pequalnp-pilot-103/9775-and-pattern.cnf')
with p.open('w') as o:
 o.write(f'p cnf {nv} {len(cs)}\n')
 for c in cs:o.write(' '.join(map(str,c))+' 0\n')
Path('results/orch9775/and-pattern/input.json').write_text(json.dumps({'rows':rows,'variables':nv,'clauses':len(cs),'gates':6,'scope':'necessary singleton occurrence pattern from L910 free_bound; NOT actual circuit synthesis'},indent=2)+'\n')
print(nv,len(cs))
