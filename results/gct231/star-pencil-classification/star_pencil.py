from pathlib import Path
import json,resource,itertools,time
import sympy as S
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
out=Path(__file__).parent
p,q,r,a,b,x,y=S.symbols('p q r a b x y');names=[p,q,r,a,b]
w=a*x+b*y
D=[-p*x-q*y-r*w-2*(x+y+w),p*x,q*y,r*w]
T=S.diag(*D)
for j,edge in enumerate((x,y,w),start=1):T[0,j]=T[j,0]=edge
A=S.ones(4)+T
per=S.expand(sum(S.prod(A[i,perm[i]] for i in range(4)) for perm in itertools.permutations(range(4)))-24)
ryser=0
for mask in range(1,16):
 cols=[j for j in range(4) if mask>>j&1]
 ryser+=(-1)**(4-len(cols))*S.prod(sum(A[i,j] for j in cols) for i in range(4))
assert S.expand(ryser-24-per)==0
rows=[]
for mon,coefficient in S.Poly(per,x,y).terms():
 assert sum(mon)>=2
 coefficient=S.factor(coefficient)
 print(mon,coefficient,flush=True)
 rows.append({'monomial':list(mon),'coefficient':str(coefficient)})
data={'unknowns':list(map(str,names)),'equations':rows,'matrix':[[str(v) for v in row] for row in T.tolist()], 'scope':'Star-supported two-parameter symmetric pencil with leaf diagonals in the corresponding incident-edge spans; tangent sum identically zero. Necessary for coordinate-two-support center-kernel branch; no contradiction yet.'}
(out/'star-pencil-five.json').write_text(json.dumps(data,indent=2)+'\n')
print('GENERATED',len(rows),'terms',sum(len(S.Poly(S.sympify(z['coefficient']),*names).terms()) for z in rows),flush=True)
start=time.monotonic();G=S.groebner([S.sympify(z['coefficient']) for z in rows],*names,order='grevlex',method='f5b')
print('GB_SECONDS',time.monotonic()-start,'BASIS',len(G.polys),flush=True)
for poly in G.polys:print(S.factor(poly.as_expr()),flush=True)
(out/'star-pencil-five-gb.json').write_text(json.dumps({'basis':[str(z.as_expr()) for z in G.polys],'seconds':time.monotonic()-start,'unit':len(G.polys)==1 and G.polys[0].as_expr()==1},indent=2)+'\n')
