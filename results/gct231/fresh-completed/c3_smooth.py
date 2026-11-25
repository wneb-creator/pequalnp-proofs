import sympy as s
u,v,q,w=s.symbols('u v q w')
F=2*q**3-3*q*q*v*(w+1)+6*q*u*u*w-6*q*u*v*w+3*u*u*v+6*u*v*v+v**3
eq=[s.diff(F,t) for t in [u,v,q]]
print('derivatives',eq)
print('q=1',s.groebner([f.subs(q,1) for f in eq]+[w*w+w+1],u,v,w,order='grevlex'))
print('q=0,u=1',s.groebner([f.subs({q:0,u:1}) for f in eq]+[w*w+w+1],v,w,order='grevlex'))
print('q=0,v=1',s.groebner([f.subs({q:0,v:1}) for f in eq]+[w*w+w+1],u,w,order='grevlex'))
