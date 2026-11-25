from fresh_laguerre_resultant import *
from fresh_laguerre_plucker import build
from fresh_block_moment_circuit import evaluate
c=build(p,la);other=roots[:];other.remove(la)
S=np.diag(other) if len(other)==3 else np.array([[10,0,0],[0,7,1],[0,1,5]])
assert (abc(S)==Rc[:3]).all()
(A,BB,CC,E),rank=first_data(S)
ev=[int(E[i+1,j+1]) for i,j in idx3]
for u,vvv in [(1,0),(0,1),(3,2)]:
 for h0 in [0,1,13]:
  pt=dict(a=int(S[0,0]),b=int(S[1,1]),x=int(S[0,1]),y=int(S[0,2]),z=int(S[1,2]),alpha=h0,u=u,v=vvv)
  ns=evaluate(c,pt,p);k=next(i for i,a in enumerate(ev) if a);sc=ns[c['minor'][k]]*iv[ev[k]]%p;assert sc
  B=(u*(BB[0]+h0*CC[0])+vvv*(BB[1]+h0*CC[1]))%p
  T=(B+np.array([-1,0,1])[:,None,None]*E)%p
  polys=[o@globals()['vv'].T%p for o in [polar(A,T,co2),polar(J,T,co2),polar((A-la*J)%p,T,co3)]]
  want=[int(resultant_quad(polys[i],polys[j]))*pow(sc,4,p)%p for i,j in it.combinations(range(3),2)]
  actual=[ns[i] for i in c['out']];assert actual==want,(pt,actual,want)
print('PASS all three pivot-free trace resultants match direct 24-permutation binary elimination with correct Plucker scaling at nine (slope,alpha) choices, p',p,'lambda',la)
