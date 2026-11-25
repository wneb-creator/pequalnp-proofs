import itertools
import resource
import sympy as s

resource.setrlimit(resource.RLIMIT_AS, (512 * 2**20, 512 * 2**20))
resource.setrlimit(resource.RLIMIT_CPU, (45, 50))
b,c,d,e,r,u,v,w,h,j,k,l = s.symbols('b c d e r u v w h j k l')
f = -1-b-c-d-e
m = -(r+u+v+w)/2-h-j-k-l
C = s.Matrix([[0,1,b,c],[1,0,d,e],[b,d,0,f],[c,e,f,0]])
V = s.Matrix([[r,0,h,j],[0,u,k,l],[h,k,v,m],[j,l,m,w]])

def coefficient(nc,nv):
    value=0
    for pi in itertools.permutations(range(4)):
        for cc in itertools.combinations(range(4),nc):
            for vc in itertools.combinations([i for i in range(4) if i not in cc],nv):
                value += s.prod(C[i,pi[i]] for i in cc)*s.prod(V[i,pi[i]] for i in vc)
    return s.expand(value)

q = f+b*e+c*d
H = c*(f-b)+d*(1-e)
J = b*(f-c)+e*(1-d)
K = e*(f-d)+b*(1-c)
L = d*(f-e)+c*(1-b)
rho = [1+b+c,1+d+e,b+d+f,c+e+f]
kap = (b+d)*(c+e)+f
C1 = 4*(c-1)*k+4*(b-1)*l-2*sum((2*ri+1)*di for ri,di in zip(rho,[r,u,v,w]))
C2 = 2*K*k+2*L*l+sum((ri**2-kap)*di for ri,di in zip(rho,[r,u,v,w]))
Delta = (e-1)*J-(d-1)*H
F11,F21,F31 = coefficient(1,1),coefficient(2,1),coefficient(3,1)
assert s.expand(F11-(4*(e-1)*h+4*(d-1)*j+C1)) == 0
assert s.expand(F21-(2*H*h+2*J*j+C2)) == 0
assert s.expand(F31-2*(d*e*f*r+b*c*f*u+c*e*v+b*d*w)-q*(2*b*l+2*c*k+2*d*j+2*e*h-2*h-2*j-2*k-2*l-r-u-v-w)) == 0
assert s.expand(Delta-(f*(b*(e-1)-c*(d-1))+(d-e)*(b*c+(d-1)*(e-1)))) == 0
hn = 2*(d-1)*C2-J*C1
jn = H*C1-2*(e-1)*C2
assert s.expand((e-1)*hn+(d-1)*jn+C1*Delta) == 0
assert s.expand(H*hn+J*jn+2*C2*Delta) == 0

print('PASS: exact symbolic identities for the general diagonal extension vector.')
print('C = [[0,1,b,c],[1,0,d,e],[b,d,0,f],[c,e,f,0]], f=-1-b-c-d-e.')
print('V = [[r,0,h,j],[0,u,k,l],[h,k,v,m],[j,l,m,w]].')
print('m=-(r+u+v+w)/2-h-j-k-l; q=f+b*e+c*d.')
print('H=c*(f-b)+d*(1-e); J=b*(f-c)+e*(1-d).')
print('K=e*(f-d)+b*(1-c); L=d*(f-e)+c*(1-b).')
print('rho=(1+b+c,1+d+e,b+d+f,c+e+f); kap=(b+d)*(c+e)+f.')
print('C1=4*(c-1)*k+4*(b-1)*l-2*sum_i((2*rho_i+1)*diag_i(V)).')
print('C2=2*K*k+2*L*l+sum_i((rho_i^2-kap)*diag_i(V)).')
print('Delta=(e-1)*J-(d-1)*H = f*(b*(e-1)-c*(d-1))+(d-e)*(b*c+(d-1)*(e-1)).')
print('On q=0 and b*d*Delta != 0, set w=-(d*e*f*r+b*c*f*u+c*e*v)/(b*d),')
print('then substitute this w in C1,C2 and set h=(2*(d-1)*C2-J*C1)/(4*Delta),')
print('j=(H*C1-2*(e-1)*C2)/(4*Delta), and m as above.')
print('This makes coefficients (s*t,s^2*t,s^3*t) of per(J+s*C+t*V)-24 zero.')
print('Free variables for chart014: b,c,d,e and (v,k,l) independently for (r,u)=(1,0),(0,1): ten variables.')
print('Still impose pure-C constraints q=0 and cubic(C)=0, plus ALL remaining three-variable permanent coefficients.')
print('Exceptional branches: b=0, d=0, or Delta=0. Clearing denominators requires saturation by b*d*Delta.')
