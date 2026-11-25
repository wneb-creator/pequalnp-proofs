from pathlib import Path
import sympy as S, json, resource, time
resource.setrlimit(resource.RLIMIT_AS, (256*2**20,256*2**20))
resource.setrlimit(resource.RLIMIT_CPU, (30,35))
b=Path('/tmp/oec/pequalnp-pilot-78/construct_search')
lines=(b/'rank1-incident-opposite-nonzero-Q.ms').read_text().splitlines()
x=S.symbols('x0:10'); zz=S.Symbol('zz'); loc={str(t):t for t in x+(zz,)}
g=[S.sympify(t.strip().rstrip(',').replace('^','**'),locals=loc) for t in lines[2:]]
assert len(g)==13
H=[x[i] for i in (3,5,7,9)]
V=[x[i] for i in (0,1,2,4,6,8)]
GH=S.groebner([g[0],g[3]],*H,order='grevlex')
lin=[]
for k in (1,4,8):
 p=S.Poly(g[k],*V)
 assert p.total_degree()==1
 constant=S.factor(GH.reduce(S.expand(g[k].subs(dict.fromkeys(V,0))))[1])
 lin.append([S.factor(GH.reduce(S.expand(S.diff(g[k],v)))[1]) for v in V]+[constant])
M=S.Matrix([a[:6] for a in lin]); const=S.Matrix([a[6] for a in lin])
print('V order:',V)
print('Reduced linear matrix:',M)
print('Constant:',const)
print('Off-block 2x2 minors:')
for i in range(2,6):
 for j in range(i+1,6):
  print(i,j,S.factor(GH.reduce(S.expand(M[:2,[i,j]].det()))[1]))
rec={'variables':[str(v) for v in V],'linear_matrix':[[str(t) for t in row[:6]] for row in lin],'constants':[str(row[6]) for row in lin],'scope':'Coefficient reduction modulo two hollow constraints only, no elimination conclusion'}
(b/'rank1-linear-reduction.json').write_text(json.dumps(rec,indent=2)+'\n')
