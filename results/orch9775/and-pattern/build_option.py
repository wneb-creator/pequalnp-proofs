import json,itertools
from pathlib import Path
rows=json.loads(Path('results/orch9775/kw_formula_lp.json').read_text())['negative_masks']
cs=[];nv=84+12*len(rows)
def m(p,g,b):return 1+12*p+2*g+b
def f(r,g,b):return 85+12*r+2*g+b
for p in range(7):
 lits=[m(p,g,b) for g in range(6) for b in range(2)]
 cs.append(lits)
 for triple in itertools.combinations(lits,3):cs.append([-a for a in triple])
 for g in range(6):cs.append([-m(p,g,0),-m(p,g,1)])
for r,I in enumerate(rows):
 for g in range(6):cs.append([-f(r,g,0),-f(r,g,1)])
 for p in range(7):
  if I>>p&1:
   for g in range(6):
    for b in range(2):cs.append([-m(p,g,b), -f(r,g,b)])
  else:
   terms=[]
   for g in range(6):
    for b in range(2):
     nv+=1;z=nv;lit=f(r,g,b);memb=m(p,g,b)
     cs += [[-z,memb],[-z,lit],[z,-memb,-lit]];terms.append(z)
   cs.append(terms)
p=Path('/tmp/oec/pequalnp-pilot-103/9775-and-pattern-option.cnf')
with p.open('w') as o:
 o.write(f'p cnf {nv} {len(cs)}\n')
 for c in cs:o.write(' '.join(map(str,c))+' 0\n')
Path('results/orch9775/and-pattern/option-input.json').write_text(json.dumps({'rows':rows,'variables':nv,'clauses':len(cs),'gates':6,'scope':'Option Bool orientations; necessary singleton occurrence pattern from L910 free_bound; NOT actual circuit synthesis'},indent=2)+'\n')
print(nv,len(cs))
