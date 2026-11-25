import sympy as s

B,C,E,z,h=s.symbols('B C E z h')
r=s.sqrt(2)
P=-1+r
R=-1-r
D=r-2+(r-4)*B+r*C+(r-1)*E
F=-2-r-r*B-(4+r)*C-(r+1)*E
a=1+z
b=1+B*z
c=1+C*z
d=1+D*z+P*h
e=1+E*z+h
f=1+F*z+R*h
per=s.expand(2*a*a*(d*f+e*e)+8*a*b*c*e+4*a*(b*b*f+c*c*d)+4*b*b*c*c-24)
poly=s.Poly(per,z,h)
print('MIXED',[(m,s.factor(co,extension=r)) for m,co in poly.terms() if m[1]],flush=True)
for name,Cval in [('equal',B),('other',s.simplify((2*r-(1+r)*B)/(r-1)))]:
    eqs=[]
    print('BRANCH',name,Cval,flush=True)
    for k in (2,3,4):
        value=s.factor(poly.coeff_monomial(z**k).subs(C,Cval),extension=r)
        print('COEFF',k,value,flush=True)
        eqs.append(value)
    G=s.groebner(eqs,E,B,extension=r)
    print('GB',G,flush=True)
    print('SOLUTIONS',s.solve(eqs,[B,E]),flush=True)
