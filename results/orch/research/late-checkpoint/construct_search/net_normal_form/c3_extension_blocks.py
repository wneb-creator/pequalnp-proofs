import sympy as S,itertools,json,time
from pathlib import Path
p=Path('/tmp/oec/pequalnp-pilot-78/construct_search/net_normal_form');start=time.monotonic()
w,a,B,c,D=S.symbols('w a B c D');red=lambda e:S.Poly(S.expand(e),w).rem(S.Poly(w*w+w+1,w)).as_expr().expand()
def plus(u,x,b):return S.Matrix([[0,u,w*w*u,w*u],[u,x,w*b,w*w*b],[w*w*u,w*b,w*w*x,b],[w*u,w*w*b,b,w*x]])
def minus(v,x,d):return S.Matrix([[0,v,w*v,w*w*v],[v,x,w*w*d,w*d],[w*v,w*w*d,w*x,d],[w*w*v,w*d,d,w*w*x]])
U=plus(1,a,B);V=minus(1,c,D)
slots=[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)];ix={xy:i for i,xy in enumerate(slots)}
grad={(i,j):[[] for z in range(10)] for i in range(4) for j in range(4-i)}
for perm in itertools.permutations(range(4)):
 for row in range(4):
  coord=ix[tuple(sorted((row,perm[row])))];other=[k for k in range(4) if k!=row]
  for choices in itertools.product(range(3),repeat=3):
   mon=(choices.count(1),choices.count(2));value=S.Integer(1)
   for k,choice in zip(other,choices):value*=1 if choice==0 else (U if choice==1 else V)[k,perm[k]]
   grad[mon][coord].append(value)
grad={mon:S.Matrix([[red(S.Add(*terms)) for terms in coeffs]]) for mon,coeffs in grad.items()}
trivial=[S.diag(1,0,0,0),S.diag(0,1,1,1),S.Matrix([[0,1,1,1],[1,0,0,0],[1,0,0,0],[1,0,0,0]]),S.Matrix([[0,0,0,0],[0,0,1,1],[0,1,0,1],[0,1,1,0]])]
wp=[plus(1,0,0),plus(0,1,0),plus(0,0,1)];wm=[minus(1,0,0),minus(0,1,0),minus(0,0,1)]
blocks={}
for name,basis,mons in [('trivial',trivial,[(0,0),(1,1),(3,0),(0,3)]),('plus',wp,[(0,1),(2,0),(1,2)]),('minus',wm,[(1,0),(0,2),(2,1)])]:
 mat=S.Matrix([[red((grad[mon]*S.Matrix([m[i,j] for i,j in slots]))[0]) for m in basis] for mon in mons]);blocks[name]=mat
 print('BLOCK',name);print(mat);print('DET',S.factor(mat.det()))
print('SECONDS',time.monotonic()-start)
(p/'c3-extension-blocks.json').write_text(json.dumps({'variables':['a','B','c','D'],'blocks':{name:[[str(x) for x in row] for row in mat.tolist()] for name,mat in blocks.items()}},indent=2)+'\n')
