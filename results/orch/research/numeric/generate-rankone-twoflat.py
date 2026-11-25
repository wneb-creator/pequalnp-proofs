from pathlib import Path
import itertools,json
import sympy as sp
from sympy.polys.rings import ring

base=Path('/tmp/oec/pequalnp-pilot-78/numeric')
coords=[(i,j) for i in range(4) for j in range(i,4)]
lookup={p:k for k,p in enumerate(coords)}
w=[1 if i==j else 2 for i,j in coords]
for label,edge in (('incident',1),('disjoint',5)):
    solved=next(k for k in range(10) if w[k]==2 and k!=edge)
    dep=9
    R,*xs=ring(','.join('x'+str(i) for i in range(11)),sp.QQ,order='grevlex')
    U=[[R.zero for _ in range(2)] for _ in range(10)]
    U[edge][0]=R.one
    U[0][1]=R.one
    n=0
    for k in range(10):
        if w[k]==2 and k not in (edge,solved):U[k][0]=xs[n];n+=1
    U[solved][0]=-sum((U[k][0] for k in range(10) if w[k]==2 and k!=solved),R.zero)
    for k in range(10):
        if k not in (0,edge,dep):U[k][1]=xs[n];n+=1
    U[dep][1]=-sum((w[k]*U[k][1] for k in range(10)),R.zero)
    assert n==11
    assert all(U[k][0]==0 for k in range(10) if w[k]==1)
    assert U[edge][0]==R.one and U[edge][1]==R.zero and U[0][1]==R.one
    exps=[(i,d-i) for d in range(5) for i in range(d+1)]
    coeff={e:R.zero for e in exps}
    for perm in itertools.permutations(range(4)):
        cs=[lookup[tuple(sorted((r,perm[r])))] for r in range(4)]
        for choice in itertools.product(range(3),repeat=4):
            term=R.one
            for r,k in enumerate(choice):
                if k:term*=U[cs[r]][k-1]
                if not term:break
            if term:coeff[tuple(choice.count(k) for k in (1,2))]+=term
    assert coeff[(0,0)]==R(24)
    assert all(not v for e,v in coeff.items() if sum(e)==1)
    polys=[v for e,v in coeff.items() if sum(e)>=2 and v]
    name='chart-rank1-'+label
    for characteristic in (0,101):
        p=base/f'{name}-p{characteristic}.ms'
        p.write_text(','.join('x'+str(i) for i in range(11))+'\n'+str(characteristic)+'\n'+',\n'.join(str(poly).replace('**','^') for poly in polys)+'\n')
    print(json.dumps({'chart':label,'hollow_edge':edge,'solved_hollow_edge':solved,'dependent_diagonal':dep,'polynomials':len(polys),'terms':sum(map(len,polys))}),flush=True)
