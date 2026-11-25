import itertools,json,sympy as s,time
from pathlib import Path
e,f,a,b,H,X,Y=s.symbols('e f a b H X Y')
vs=[e,f,a,b,H,X,Y]
u,v,t,lam=s.symbols('u v t lam')
q=6*e**2+2*f**2+a**2+b**2-H**2-X**2-Y**2-X*(a+b)+Y*(b-a)
c=2*f*a*b-2*H*X*Y+e*(-4*X**2-4*Y**2+4*X*(a+b)+4*Y*(a-b)-a*a-b*b+4*f*f)-4*e**3
G=s.hessian(q,vs)/2
records=[]
for left,right in itertools.product([f,a,b],[H,X,Y]):
    start=time.monotonic()
    zs=[left,right];ws=[z for z in [f,a,b,H,X,Y] if z not in zs]
    wi=[vs.index(z) for z in ws];zi=[vs.index(z) for z in zs]
    GW=G.extract(wi,wi);GZ=G.extract(wi,zi)
    r=-GW.inv()*GZ*s.Matrix([u,v])
    subw={e:1,left:u,right:v,**dict(zip(ws,r))}
    assert all(s.simplify(sum(G[i,j]*subw[vs[j]] for j in range(7)))==0 for i in wi)
    qw=s.factor(q.subs(subw,simultaneous=True));cw=s.factor(c.subs(subw,simultaneous=True))
    subk={e:0,left:0,right:0}
    Rpoly=s.Poly(s.expand(c.subs({z:subk.get(z,z)+t*subw[z] for z in vs},simultaneous=True)),t).coeff_monomial(t)
    GR=s.hessian(Rpoly,ws)/2
    det=s.Poly(s.expand((GR-lam*GW).det()),lam).monic()
    c3,c2,c1,c0=det.all_coeffs()[1:]
    square3=s.factor(8*c1-4*c3*c2+c3**3)
    square4=s.factor(64*c0-(4*c2-c3*c3)**2)
    equations=[qw,cw,square3,square4]
    gro=s.groebner(equations,u,v,order='grevlex',domain=s.QQ)
    result={'zero_coordinates':list(map(str,zs)),'w':{str(z):str(subw[z]) for z in vs},'q_w':str(qw),'c_w':str(cw),'det_monic':str(det.as_expr()),'square_cubic':str(square3),'square_quartic':str(square4),'basis':list(map(str,gro)),'seconds':time.monotonic()-start}
    records.append(result)
    print(json.dumps(result),flush=True)
    if list(gro)!=[1]:print('NOT_EXCLUDED_BY_SQUARE_TEST',flush=True)
Path('/tmp/oec/pequalnp-pilot-75/gct231/fresh/c4-zero-product-square-test.json').write_text(json.dumps(records,indent=2))
print('COMPLETED',len(records),'UNIT_CASES',sum(r['basis']==['1'] for r in records),flush=True)
