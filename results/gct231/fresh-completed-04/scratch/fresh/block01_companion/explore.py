from datetime import datetime,timezone
import sympy as s
import json
from pathlib import Path
from sympy.polys.rings import ring

print('Start UTC',datetime.now(timezone.utc).isoformat(),flush=True)
x,y=s.symbols('x y');r=s.sqrt(2)
A=s.Matrix([[r-1,1,0,0],[1,-r-1,0,0],[0,0,0,0],[0,0,0,0]])
bs=s.symbols('b00 b01 b02 b03 b11 b12 b13 b22 b23 b33')
B=s.zeros(4);idx=0
for i in range(4):
 for j in range(i,4):B[i,j]=B[j,i]=bs[idx];idx+=1
rr,*gens=ring(','.join(map(str,[x,y,*bs])),s.QQ.algebraic_field(r))
M=s.ones(4)+x*A+y*B
MR=[[rr.from_expr(M[i,j]) for j in range(4)] for i in range(4)]
P=rr.zero
for mask in range(1,16):
 term=rr.one
 for i in range(4):term*=sum((MR[i][j] for j in range(4) if mask>>j&1),rr.zero)
 P+=(-1)**(4-mask.bit_count())*term
P-=24
coeff={}
for mon,c in P.items():
 key=mon[:2]
 coeff[key]=coeff.get(key,0)+rr.domain.to_sympy(c)*s.prod(v**e for v,e in zip(bs,mon[2:]))
linear=[p for mon,p in coeff.items() if mon[1]==1]+[bs[1],bs[2]-1,bs[3]]
sol=next(iter(s.linsolve(linear,bs)));sub=dict(zip(bs,sol))
print('LINEAR_SOLUTION',sub,flush=True)
vs=sorted(set().union(*(v.free_symbols for v in sol)),key=str)
print('PARAMETERS',vs,flush=True)
for mon,p in sorted(coeff.items()):
 eq=s.Poly(s.expand(p.subs(sub)),*vs,extension=r).as_expr()
 if eq!=0:print('EQUATION',mon,'degree',s.Poly(eq,*vs).total_degree(),'terms',len(s.Poly(eq,*vs).terms()),flush=True)
print('Finish UTC',datetime.now(timezone.utc).isoformat(),flush=True)

Path(__file__).with_suffix('.json').write_text(json.dumps({'parameters':list(map(str,vs)),'sub':{str(k):str(v) for k,v in sub.items()},'equations':[{ 'monomial':mon,'expression':str(s.Poly(s.expand(p.subs(sub)),*vs,extension=r).as_expr())} for mon,p in sorted(coeff.items()) if s.Poly(s.expand(p.subs(sub)),*vs,extension=r).as_expr()!=0]},indent=2)+'\n')
