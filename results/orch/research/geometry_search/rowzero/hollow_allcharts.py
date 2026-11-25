import sympy as S,itertools,time,json
from pathlib import Path

A,B,K,s,t=S.symbols('A B K s t')
x1,x2,y1,y2,z=S.symbols('x1 x2 y1 y2 z')
coords=[x1+z,x2+z,-x1-x2-y1-y2-5*z,z,y2+z,y1+z]
a,b,c,d,e,f=coords
T=S.Matrix([[0,a,b,c],[a,0,d,e],[b,d,0,f],[c,e,f,0]])
cub=0
for rows in itertools.combinations(range(4),3):
 for cols in itertools.combinations(range(4),3):
  cub+=sum(S.prod(T[rows[i],cols[pm[i]]] for i in range(3)) for pm in itertools.permutations(range(3)))
cub=S.expand(cub)
assert S.expand(cub.xreplace({x1:y1,y1:x1,x2:y2,y2:x2})-cub)==0
Z=A*s+B*t
P1=s;P2=t;Q1=3*A*Z+K*t;Q2=3*B*Z-K*s
odd_sub={x1:Q1,x2:P2,y1:P1,y2:Q2,z:Z}
odd_eq=S.Poly(S.expand(cub.subs(odd_sub)),s,t).coeffs()
print('ODD START',time.time(),flush=True)
G=S.groebner(odd_eq,A,B,K,order='grevlex',method='f5b')
print('ODD ZERO DIMENSIONAL',G.is_zero_dimensional,flush=True)
L=G.fglm('lex')
print('ODD K FACTOR',S.factor(list(L)[-1]),flush=True)
odd=S.solve_poly_system(list(L),A,B,K)
print('ODD SOLUTIONS',odd,flush=True)
orig=Path('/tmp/oec/pequalnp-pilot-78/geometry_search/rowzero/hollow_chart.stdout').read_text().splitlines()
even=S.sympify(next(l.removeprefix('SOLUTIONS ') for l in orig if l.startswith('SOLUTIONS ')))
planes={}
for flip in itertools.product([0,1],repeat=2):
 sols=odd if sum(flip)%2 else even
 subst={x1:Q1 if flip[0] else P1,y1:P1 if flip[0] else Q1,
        x2:Q2 if flip[1] else P2,y2:P2 if flip[1] else Q2,z:Z}
 for sol in sols:
  cs=[S.expand(c.subs(subst).subs(dict(zip((A,B,K),sol)))) for c in coords]
  mat=S.Matrix([[c.coeff(s) for c in cs],[c.coeff(t) for c in cs]])
  rr=mat.rref()[0]
  key=tuple(str(v) for v in rr)
  planes.setdefault(key,[]).append((flip,tuple(str(v) for v in sol)))
 print('CHART',flip,'POINTS',len(sols),'CUMULATIVE PLANES',len(planes),flush=True)
out=[{'rref':[list(key[:6]),list(key[6:])],'charts':cs} for key,cs in sorted(planes.items())]
Path('/tmp/oec/pequalnp-pilot-78/geometry_search/rowzero/hollow_planes.json').write_text(json.dumps(out,indent=2))
print('TOTAL PLANES',len(out),flush=True)
for row in out:print(row['rref'],flush=True)
