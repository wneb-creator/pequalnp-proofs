import itertools, resource, sympy as s
resource.setrlimit(resource.RLIMIT_AS, (512 * 2**20, 512 * 2**20))
resource.setrlimit(resource.RLIMIT_CPU, (45, 50))
b,c,d,e = s.symbols('b c d e')
f = -1-b-c-d-e
u,v,w = s.symbols('u v w')
h,j,k,l = s.symbols('h j k l')
m = -(1+u+v+w)/2-h-j-k-l
A=s.Matrix([[0,1,b,c],[1,0,d,e],[b,d,0,f],[c,e,f,0]])
B=s.Matrix([[1,0,h,j],[0,u,k,l],[h,k,v,m],[j,l,m,w]])
perms=list(itertools.permutations(range(4)))
def coefficient(na,nb):
    value=0
    for pi in perms:
        for ac in itertools.combinations(range(4),na):
            for bc in itertools.combinations([i for i in range(4) if i not in ac],nb):
                value+=s.prod(A[i,pi[i]] for i in ac)*s.prod(B[i,pi[i]] for i in bc)
    return s.expand(value)
Q=s.expand(f+b*e+c*d)
F11=coefficient(1,1)
F21=coefficient(2,1)
F31=coefficient(3,1)
claimed=2*(d*e*f+b*c*f*u+c*e*v+b*d*w)
quotient,remainder=s.div(s.expand(F31-claimed),Q,*[b,c,d,e,u,v,w,h,j,k,l])
assert remainder==0
print('A23 =',f)
print('q(A) =',Q)
print('s^3*t minus claimed = q(A) *',s.factor(quotient))
print('B33 solution =',s.factor(-(d*e*f+b*c*f*u+c*e*v)/(b*d)))
print('F11 =',s.factor(F11))
print('F21 =',s.factor(F21))
print('A cubic =',s.factor(coefficient(3,0)))
offs=[h,j,k,l]
for a0,a1 in itertools.combinations(offs,2):
    determinant=s.expand(s.diff(F11,a0)*s.diff(F21,a1)-s.diff(F11,a1)*s.diff(F21,a0))
    print('det',a0,a1,'=',s.factor(determinant))
    det_on_q=s.factor(determinant.subs(e,(1+b+c+d-c*d)/(b-1)))
    print('det on q',a0,a1,'=',det_on_q)
