import itertools, json, sympy as s
from pathlib import Path
x,y=s.symbols('x y')
v=s.symbols('v0:12')
T=s.zeros(4)
T[0,1]=T[1,0]=x
T[0,2]=T[2,0]=y
slots=[(0,0),(1,1),(2,2),(1,2),(1,3),(2,3)]
for k,(i,j) in enumerate(slots):
    T[i,j]=T[j,i]=v[2*k]*x+v[2*k+1]*y
T[3,3]=-sum(T[i,i] for i in range(3))-2*sum(T[i,j] for i in range(4) for j in range(i+1,4))
M=s.ones(4)+T
P=s.Poly(s.expand(sum(s.prod(M[i,p[i]] for i in range(4)) for p in itertools.permutations(range(4)))-24),x,y)
eq=P.coeffs()
assert len(eq)==12
print('VARIABLES',len(v),'EQUATIONS',len(eq),'DEGREES',[s.Poly(e,*v).total_degree() for e in eq], 'TERMS',sum(len(s.Poly(e,*v).terms()) for e in eq),flush=True)
Jac=s.Matrix(eq).jacobian(v)
rows=[x,y,-x-y]
count=0
for perm in itertools.permutations(range(3)):
    for signs in itertools.product([1,-1],repeat=3):
        if s.prod(signs)!=1: continue
        dif=[signs[i]*rows[perm[i]] for i in range(3)]
        a,b,c=[(rows[i]+dif[i])/2 for i in range(3)]
        f,e,d=[(rows[i]-dif[i])/2 for i in range(3)]
        if c!=0: continue
        S=s.Matrix([[0,a,b,c],[a,0,d,e],[b,d,0,f],[c,e,f,0]])
        N=s.Matrix([[s.expand(a).coeff(x),s.expand(a).coeff(y)],[s.expand(b).coeff(x),s.expand(b).coeff(y)]])
        if N.det()==0: continue
        inv=N.inv()*s.Matrix([x,y])
        S=S.subs({x:inv[0],y:inv[1]},simultaneous=True)
        values=[]
        for i,j in slots: values.extend([s.expand(S[i,j]).coeff(x),s.expand(S[i,j]).coeff(y)])
        subs=dict(zip(v,values))
        assert all(e.subs(subs)==0 for e in eq)
        J=Jac.subs(subs)
        print('SEED',count,'VALUES',values,'JACOBIAN_RANK',J.rank(),'TANGENT_DIM',12-J.rank(),flush=True)
        print('KERNEL',[list(z) for z in J.nullspace()],flush=True)
        count+=1
assert count==2
out={'variables':list(map(str,v)),'matrix':[[str(T[i,j]) for j in range(4)] for i in range(4)],'equations':list(map(str,eq))}
Path('/tmp/oec/pequalnp-pilot-75/gct231/fresh/zero-edge-pencil.json').write_text(json.dumps(out,indent=2))
print('PASS',flush=True)
