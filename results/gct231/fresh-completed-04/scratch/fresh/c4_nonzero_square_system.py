import itertools,json,time,sympy as s,sys
from pathlib import Path
e,f,a,b,H,X,Y=s.symbols('e f a b H X Y')
vs=[e,f,a,b,H,X,Y]; z=vs[1:]
alpha,beta,gamma,u,v,lam=s.symbols('alpha beta gamma u v lam')
parameters=[alpha,beta,gamma,u,v]
q=6*e**2+2*f**2+a**2+b**2-H**2-X**2-Y**2-X*(a+b)+Y*(b-a)
c=2*f*a*b-2*H*X*Y+e*(-4*X**2-4*Y**2+4*X*(a+b)+4*Y*(a-b)-a*a-b*b+4*f*f)-4*e**3
G=s.hessian(q,z)/2;Gi=G.inv()
def det4(M):
    ans=0
    for p in itertools.permutations(range(4)):
        sign=(-1)**sum(p[i]>p[j] for i in range(4) for j in range(i+1,4))
        ans+=sign*s.prod(M[i,p[i]] for i in range(4))
    return s.expand(ans)
start=time.monotonic();allperms=list(itertools.permutations([f,a,b]))
for index in ([int(sys.argv[1])] if len(sys.argv)>1 else range(6)):
    perm=allperms[index]
    n1=s.Matrix([s.diff(H-alpha*perm[0],w) for w in z]);n2=s.Matrix([s.diff(X-beta*perm[1],w) for w in z])
    w=Gi*(u*n1+v*n2);subw={e:1,**dict(zip(z,w))}
    subk={e:0,H:alpha*perm[0],X:beta*perm[1]}
    wk=[f,a,b,Y]
    B=s.Matrix([subk.get(t,t) for t in z]).jacobian(wk)
    GW=s.simplify(B.T*G*B);detW=s.factor(GW.det())
    assert (B.T*G*w).applyfunc(s.expand)==s.zeros(4,1)
    qw=s.factor(q.subs(subw,simultaneous=True));cw=s.factor(c.subs(subw,simultaneous=True))
    Rpoly=s.expand(sum(s.diff(c,t)*subw[t] for t in vs).subs(subk,simultaneous=True))
    GR=s.hessian(Rpoly,wk)/2
    D=s.Poly(det4(GR-lam*GW),lam)
    d4,d3,d2,d1,d0=D.all_coeffs()
    square3=s.factor(8*d1*d4*d4-4*d3*d2*d4+d3**3)
    normal=s.Matrix([s.diff(Y-gamma*perm[2],t) for t in wk]);nv=GW.adjugate()*normal
    normalQ=s.factor((normal.T*nv)[0])
    normalR=s.factor((nv.T*GR*nv)[0])
    Lpoly=s.expand(sum(s.diff(c,ti,tj)*subw[ti]*subw[tj] for ti in vs for tj in vs).subs(subk,simultaneous=True)/2)
    Lv=s.factor((s.Matrix([s.diff(Lpoly,t) for t in wk]).T*nv)[0])
    equations=[alpha*beta*gamma-1,qw,cw,normalQ,square3,normalR,Lv]
    result={'variables':list(map(str,parameters)),'permutation':list(map(str,perm)),
       'equations':list(map(str,equations)),'equation_labels':['product_scales','q_w','c_w','normal_q','square_cubic','normal_R','normal_L'],
       'det_W':str(detW),'w':{str(t):str(subw[t]) for t in vs},
       'gram_W':[[str(GW[i,j]) for j in range(4)] for i in range(4)],
       'gram_R':[[str(GR[i,j]) for j in range(4)] for i in range(4)],
       'normal':list(map(str,normal)),'scope':'Necessary equations for nonzero product branch, conditional on det_W nonzero. No consistency claim.'}
    target=Path(f'/tmp/oec/pequalnp-pilot-75/gct231/fresh/c4-nonzero-square-{index}.json');target.write_text(json.dumps(result,indent=2))
    print('CASE',index,'PERM',perm,'DET_W',detW,'TERMS',[len(s.Poly(t,*parameters).terms()) for t in equations], 'DEGREES',[s.Poly(t,*parameters).total_degree() for t in equations],'SECONDS',time.monotonic()-start,flush=True)
