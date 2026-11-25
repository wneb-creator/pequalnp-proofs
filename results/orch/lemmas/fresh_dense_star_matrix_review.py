from pathlib import Path
from itertools import permutations,combinations
import hashlib,json,re,sympy as sy
j=Path('/tmp/oec/pequalnp-pilot-79');f=j/'DenseStarMatrixConstraints.lean';s=f.read_text();sha=hashlib.sha256(f.read_bytes()).hexdigest()
st=json.loads((j/'root-DenseStarMatrixConstraints-lean-3g-profile-status.json').read_text());assert st['sha256']==st['source_sha256_after']==sha=='542090ab049f61c88579f77d277546a9eab0aef54bd31d1ef857fd82d8422f39' and st['exit_code']==0
assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',s)
h,d,e,f0,a,b,c,X,Y,k=sy.symbols('h d e f a b c X Y k');local={str(i):i for i in [h,d,e,f0,a,b,c,X,Y,k]}
def expr(n):
 u=s.split('noncomputable def '+n+' ',1)[1].split(':=',1)[1].split('\n\n',1)[0].split('noncomputable def',1)[0]
 return sy.sympify(u.replace('^','**').replace('\n',''),locals=local)
L0,L1,K,XX,YY,Q,F=[expr(n) for n in ['linear0','linear1','coordK','coordX','coordY','lowerQuadratic','quotientQuadratic']]
S=sy.Matrix([[d,e,f0],[e,a,b],[f0,b,c]]);ones=sy.ones(3,1);w=sy.Matrix([1,h,-1-h]);inds=range(3)
kf=sy.Matrix(3,3,lambda i,j:sum(sy.prod(S[r,q] for r,q in zip([t for t in inds if t!=i],pi)) for pi in permutations([t for t in inds if t!=j])))
def ck(x):assert sy.expand(x)==0
ck(L0-(w.T*S*w)[0]);ck(L1-(w.T*S*ones)[0]);ck(Q-(w.T*kf*w)[0])
dd=h*h*a-2*h*(h+1)*b+(h+1)**2*c-2*(2*h+1)*k;ee=-h*a+(h+1)*b+(h+2)*k;ff=-h*b+(h+1)*c+(h-1)*k
ck(Q.subs({d:dd,e:ee,f0:ff})-2*F.subs({X:XX,Y:YY}));ck(YY-h*XX-h*(h+1)*(a-b));ck(YY-(h+1)*XX-h*(h+1)*(b-c))
assert 'have hz := hp (-δ⁻¹)' in s and 'M=star (M 0 1) (M 0 2)' in s and 'hh1 : h+1≠0' in s
print('PASS',sha,'Lean',st['seconds'],'seconds; source parsed L0=wSw,L1=wS1,Q=wK(S)w; exact rank-three quotient scalar identity, radical differences and delta!=0 diagonal lower-block specialization. Dense endpoint gives isotropy and kernel-to-centered-star only.')
