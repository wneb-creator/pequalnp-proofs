import itertools
import json
from pathlib import Path
import sympy as s

base=Path('/tmp/oec/pequalnp-pilot-78')
source=base/'numeric/chart-047-p0.ms'
lines=source.read_text().splitlines()
names=lines[0].split(',')
assert names==['x'+str(i) for i in range(18)]
xs=s.symbols('x0:18')
expressions=[s.sympify(v.strip().replace('^','**'),locals=dict(zip(names,xs)))
             for v in '\n'.join(lines[2:]).split(',') if v.strip()]
polys=[dict(s.Poly(e,*xs).terms()) for e in expressions]
assert len(polys)==31
edges=[(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
lookup={(e,k):3*i+k for i,e in enumerate(edges) for k in range(3)}
exponents=[e for d in (2,3,4) for e in itertools.product(range(d+1),repeat=3) if sum(e)==d]
assert len(exponents)==31
rows=[]
for sigma3 in itertools.permutations(range(3)):
    sigma=sigma3+(3,)
    variable_map=[]
    for e in edges:
        for k in range(3):
            moved=tuple(sorted((sigma[e[0]],sigma[e[1]])))
            variable_map.append(lookup[(moved,sigma[k])])
    generator_map=[]
    for e,poly in zip(exponents,polys):
        moved_e=[0,0,0]
        for k in range(3):moved_e[sigma[k]]=e[k]
        j=exponents.index(tuple(moved_e))
        moved_poly={}
        for monomial,c in poly.items():
            moved=[0]*18
            for k in range(18):moved[variable_map[k]]=monomial[k]
            moved_poly[tuple(moved)]=c
        assert moved_poly==polys[j],(sigma,e,j)
        generator_map.append(j)
    row={'permutation':list(sigma3),'variable_map':variable_map,'generator_map':generator_map}
    rows.append(row)
    print(json.dumps(row),flush=True)
out={'coordinate_order':['00','01','02','03','11','12','13','22','23','33'],
     'off_diagonal_rows':['01','02','03','12','13','23'],
     'variable_convention':'x[3*edge_index+parameter_index]',
     'generator_parameter_exponents':[list(e) for e in exponents],
     'substitution_convention':'x_i maps to x_variable_map[i]; generator f_i maps exactly to f_generator_map[i]',
     'maps':rows,'verified_generator_equalities':6*31}
(base/'geometry_search/diag047-symmetry.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS:186 exact polynomial permutation identities',flush=True)
