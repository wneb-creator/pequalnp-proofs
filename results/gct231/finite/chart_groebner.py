import sympy as s,itertools,json,time,sys
from pathlib import Path
base=Path(__file__).parent
chart=sys.argv[1];mode=sys.argv[2];method=sys.argv[3] if len(sys.argv)>3 else 'f5b'
pivots={'star':[(0,1),(0,2),(0,3)],'triangle':[(0,1),(0,2),(1,2)],'path':[(0,1),(1,2),(2,3)]}[chart]
x=s.symbols('x y z');edges=list(itertools.combinations(range(4),2))
remaining=[edge for edge in edges if edge not in pivots]
D=s.symbols('d0:9');O=s.symbols('o0:9') if mode=='full' else []
unknowns=list(D)+list(O)
T=s.zeros(4)
for i in range(3):T[i,i]=sum(D[3*i+j]*x[j] for j in range(3))
for edge,value in zip(pivots,x):T[edge[0],edge[1]]=T[edge[1],edge[0]]=value
for i,edge in enumerate(remaining):
 value=sum(O[3*i+j]*x[j] for j in range(3)) if mode=='full' else 0
 T[edge[0],edge[1]]=T[edge[1],edge[0]]=value
T[3,3]=-sum(T[i,i] for i in range(3))-2*sum(T[i,j] for i,j in edges)
print('CHART',chart,'MODE',mode,'UNKNOWNS',len(unknowns),'METHOD',method,flush=True)
start=time.monotonic()
f=s.Poly(s.expand(sum(s.prod(1+T[i,perm[i]] for i in range(4)) for perm in itertools.permutations(range(4)))-24),*x)
records=[{'monomial':mon,'coefficient':str(s.factor(coef))} for mon,coef in f.terms() if coef!=0]
assert all(sum(r['monomial'])>=2 for r in records)
eqs=[s.Poly(coef,*unknowns).primitive()[1].as_expr() for mon,coef in f.terms() if coef!=0]
prefix=chart+'-'+mode+'-'+method
(base/(prefix+'-equations.json')).write_text(json.dumps({'pivots':pivots,'remaining':remaining,'unknowns':[str(u) for u in unknowns],'matrix':[[str(T[i,j]) for j in range(4)] for i in range(4)],'equations':records},indent=2)+'\n')
print('EQUATIONS',len(eqs),'GEN_SECONDS',time.monotonic()-start,flush=True)
G=s.groebner(eqs,*unknowns,domain=s.QQ,order='grevlex',method=method)
print('GROEBNER_SECONDS',time.monotonic()-start,flush=True)
print('BASIS',G,flush=True)
(base/(prefix+'-basis.json')).write_text(json.dumps({'basis':[str(p.as_expr()) for p in G.polys],'inconsistent':len(G.polys)==1 and G.polys[0].as_expr()==1},indent=2)+'\n')
