import sympy as s,itertools,json,time
from pathlib import Path
p=Path('/tmp/oec/pequalnp-pilot-78/construct_search/net_normal_form');start=time.monotonic()
w,a,b,c,d,X,Y=s.symbols('w a b c d X Y');rels=w*w+w+1
red=lambda e:s.Poly(s.expand(e),w).rem(s.Poly(rels,w)).as_expr().expand()
U=s.Matrix([[0,1,w*w,w],[1,a,b,w*b],[w*w,b,w*w*a,w*w*b],[w,w*b,w*w*b,w*a]])
V=s.Matrix([[0,1,w,w*w],[1,c,d,w*w*d],[w,d,w*c,w*d],[w*w,w*w*d,w*d,w*w*c]])
T=s.ones(4)+X*U+Y*V
per=red(sum(s.prod(T[i,perm[i]] for i in range(4)) for perm in itertools.permutations(range(4))))
poly=s.Poly(per,X,Y);nonzero={str(m):s.factor(coef) for m,coef in poly.terms() if m!=(0,0)}
print('PERMANENT_COEFFICIENTS')
for m,coef in nonzero.items():print(m,coef)
assert set(nonzero)=={'(3, 0)','(2, 2)','(1, 1)','(0, 3)'}
q=s.factor(poly.coeff_monomial(X*Y));cu=s.factor(poly.coeff_monomial(X**3));cv=s.factor(poly.coeff_monomial(Y**3));pm=s.factor(poly.coeff_monomial(X**2*Y**2));eqs=[q,cu,cv,pm]
assert all(red(f.subs({w:7,a:13,b:2,c:10,d:12}))%19==0 for f in eqs)
source=['ring R=(0,w),(a,b,c,d),dp;','minpoly=w^2+w+1;','short=0;','option(redSB);']
for i,e in enumerate(eqs):source.append('poly F'+str(i+1)+'='+s.sstr(e).replace('**','^')+';')
source+=['ideal I=F1,F2,F3,F4;','print("START_C3_CLASSIFICATION");','ideal G=std(I);','print("BASIS_SIZE");size(G);','print("DIMENSION");dim(G);','print("UNIT_IDEAL");int(reduce(1,G)==0);','print("BASIS");G;','print("DONE");quit;']
(p/'c3-tracezero.sing').write_text('\n'.join(source)+'\n')
(p/'c3-tracezero-system.json').write_text(json.dumps({'variables':['a','b','c','d'],'field_relation':str(rels),'U':[[str(x) for x in row] for row in U.tolist()],'V':[[str(x) for x in row] for row in V.tolist()],'equations':[str(e) for e in eqs]},indent=2)+'\n')
print('SECONDS',time.monotonic()-start)
