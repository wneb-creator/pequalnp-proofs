from pathlib import Path
import itertools,json
import sympy as sp
from sympy.polys.rings import ring

base=Path('/tmp/oec/pequalnp-pilot-78/numeric')
coords=[(i,j) for i in range(4) for j in range(i,4)]
lookup={p:k for k,p in enumerate(coords)}
w=[1 if i==j else 2 for i,j in coords]
for chart in ((0,1,4),(0,1,7),(0,4,8)):
    diagonals=[k for k in chart if w[k]==1]
    edge=next(k for k in chart if w[k]==2)
    pivots=diagonals+[edge]
    dep=next(k for k in range(10) if w[k]==1 and k not in pivots)
    zero=next(k for k in range(10) if w[k]==1 and k not in pivots and k!=dep)
    solve=next(k for k in range(10) if w[k]==2 and k not in pivots)
    free=[k for k in range(10) if k not in pivots and k!=dep]
    R,*xs=ring(','.join('x'+str(i) for i in range(16)),sp.QQ,order='grevlex')
    U=[[R.zero for _ in range(3)] for _ in range(10)]
    for j,k in enumerate(pivots):U[k][j]=R.one
    n=0
    for k in free:
        for j in range(3):
            if j==2 and k in (zero,solve):continue
            U[k][j]=xs[n];n+=1
    assert n==16
    U[solve][2]=-sum((U[k][2] for k in range(10) if w[k]==2 and k!=solve),R.zero)
    for j in range(3):U[dep][j]=-sum((w[k]*U[k][j] for k in range(10)),R.zero)
    assert all(U[k][2]==0 for k in range(10) if w[k]==1)
    exps=[e for d in range(5) for e in itertools.product(range(d+1),repeat=3) if sum(e)==d]
    coeff={e:R.zero for e in exps}
    for perm in itertools.permutations(range(4)):
        cs=[lookup[tuple(sorted((r,perm[r])))] for r in range(4)]
        for choice in itertools.product(range(4),repeat=4):
            term=R.one
            for r,k in enumerate(choice):
                if k:term*=U[cs[r]][k-1]
                if not term:break
            if term:coeff[tuple(choice.count(k) for k in (1,2,3))]+=term
    assert coeff[(0,0,0)]==R(24)
    assert all(not v for e,v in coeff.items() if sum(e)==1)
    polys=[v for e,v in coeff.items() if sum(e)>=2 and v]
    name='chart-rank2-'+''.join(map(str,chart))
    for characteristic in (0,101):
        p=base/f'{name}-p{characteristic}.ms'
        p.write_text(','.join('x'+str(i) for i in range(16))+'\n'+str(characteristic)+'\n'+',\n'.join(str(poly).replace('**','^') for poly in polys)+'\n')
    print(json.dumps({'chart':chart,'pivots_in_order':pivots,'dependent_diagonal':dep,'zero_coordinate':zero,'solved_coordinate':solve,'polynomials':len(polys),'terms':sum(map(len,polys))}),flush=True)
