from pathlib import Path
exec(Path('/tmp/oec/pequalnp-pilot-75/gct231/fresh/rank1_pencil.py').read_text())
z=s.symbols('z');cs=s.symbols('c00 c01 c02 c03 c11 c12 c13 c22 c23 c33')
C=s.zeros(4);k=0
for i in range(4):
 for j in range(i,4):C[i,j]=C[j,i]=cs[k];k+=1
N=s.ones(4)+x*A+y*B+z*C
P=s.Poly(s.expand(sum(s.prod(N[i,p[i]] for i in range(4)) for p in itertools.permutations(range(4)))-24),x,y,z)
lin=[v for mon,v in P.terms() if mon[2]==1]+[cs[1],cs[3]]
sol=next(iter(s.linsolve(lin,cs)));sub=dict(zip(cs,sol))
print('NORMALIZED_LINEAR_SOLUTION',sub,flush=True)
vs=sorted(set().union(*(v.free_symbols for v in sol)),key=str)
rest=list(dict.fromkeys(s.Poly(s.expand(v.subs(sub)),*vs,extension=r).as_expr() for mon,v in P.terms())) if vs else []
rest=[v for v in rest if v!=0]
print('REMAINING_VARIABLES',vs,'CONSTRAINTS',rest,flush=True)
if not vs:
 print('NO_THIRD_DIRECTION_ALREADY_LINEAR',flush=True)
elif not rest:
 print('EVERY_REMAINING_DIRECTION_EXTENDS',flush=True)
else:
 G=s.groebner(rest,*vs,extension=r,order='grevlex');print('GROEBNER',list(G),flush=True)
 for v in vs:
  power=next((n for n in range(1,17) if G.reduce(v**n)[1]==0),None)
  print('NILPOTENT_PARAMETER',v,power,flush=True)
