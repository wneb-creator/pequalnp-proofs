import sympy as s,itertools
w=s.symbols('w');r,e,f,x,y=s.symbols('r e f x y')
u=[s.Matrix([1,1,1,0]),s.Matrix([1,w,w*w,0]),s.Matrix([1,w*w,w,0]),s.Matrix([0,0,0,1])]
sm=lambda i,j:u[i]*u[j].T+u[j]*u[i].T
B=sm(0,1)-3*sm(3,1)+r*u[2]*u[2].T
A=sm(0,2)+e*sm(3,2)+f*u[1]*u[1].T
M=s.ones(4)+x*B+y*A
F=s.rem(s.Poly(s.expand(sum(s.prod(M[i,p[i]] for i in range(4)) for p in itertools.permutations(range(4))))-24,w),s.Poly(w*w+w+1,w)).as_expr()
ps=[]
for mon,coef in s.Poly(F,x,y).terms():
 print(mon,s.factor(coef),flush=True);ps.append(coef)
print('GB',s.groebner(ps,r,e,f,order='grevlex'),flush=True)
