import ast
import itertools
from pathlib import Path
import sys
import sympy as s

job=Path('/tmp/oec/pequalnp-pilot-78/construct_search')
planes=ast.literal_eval((job/'real-planes.txt').read_text())
indices=[int(x) for x in sys.argv[1:]] or [1,11]
a,b,z=s.symbols('a b z')
vv=s.symbols('v00 v01 v02 v03 v11 v12 v13 v22 v23 v33')
ij=[(i,j) for i in range(4) for j in range(i,4)]
V=s.zeros(4)
for k,(i,j) in zip(vv,ij):V[i,j]=V[j,i]=k
perms=list(itertools.permutations(range(4)))
for index in indices:
    print('REPRESENTATIVE',index,flush=True)
    aa,bb=planes[index]
    AA=s.Matrix(4,4,aa);BB=s.Matrix(4,4,bb)
    _,piv=s.Matrix([aa,bb]).rref()
    M=s.ones(4)+a*AA+b*BB+z*V
    P=s.Poly(s.expand(sum(s.prod(M[i,j] for i,j in enumerate(p)) for p in perms)-24),a,b,z)
    linear=[c for m,c in P.terms() if m[2]==1]+[V[k//4,k%4] for k in piv]
    solution=list(s.linsolve(linear,vv))[0]
    print('linear solution',solution,flush=True)
    R=s.Poly(s.expand(P.as_expr().subs(dict(zip(vv,solution)))),a,b,z)
    eq=[s.factor(c) for m,c in R.terms() if c!=0]
    params=sorted(set().union(*(x.free_symbols for x in eq)),key=str)
    print('remaining equations',eq,flush=True)
    print('parameters',params,flush=True)
    outputs=[]
    for var in params:
        rest=[x for x in params if x!=var]
        es=[s.expand(e.subs(var,1)) for e in eq]
        g=s.groebner(es,*rest) if rest else ('INCONSISTENT' if any(e!=0 for e in es) else 'TRIVIAL')
        print('chart',var,'GB',g,flush=True)
        outputs.append((str(var),str(g)))
    (job/('extension-'+str(index)+'.txt')).write_text(str({'linear':solution,'equations':eq,'charts':outputs}))
