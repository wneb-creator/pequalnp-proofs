from pathlib import Path
from itertools import permutations
from hashlib import sha256
import json, re,sympy as s
j=Path('/tmp/oec/pequalnp-pilot-79')
f=j/'ExceptionalDirectionNormalization.lean'; src=f.read_text();sha=sha256(f.read_bytes()).hexdigest()
assert sha=='542c6c04d5f77ba5000ecae94f44973de4c6805d5b64a0214bbba19639001671'
data=json.loads((j/'root-ExceptionalDirectionNormalization-lean-3g-profile-status.json').read_text())
assert data['sha256']==data['source_sha256_after']==sha and data['exit_code']==0
assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',src)
r,a,z,b,c=s.symbols('r a z b c'); M=s.Matrix([[0,1,r,0],[1,a,-a*r,0],[r,-a*r,a*r**2,0],[0,0,0,0]])
per=sum(s.prod(1+z*M[i,pi[i]] for i in range(4)) for pi in permutations(range(4)))
hs=a*(1-r)**2+2*(1+r);hq=4*a*a*r*r+2*(r+1)**2;Q=r**4-4*r**3+14*r*r-4*r+1;alpha=(3*r**3-11*r*r+37*r+3);H4=4*a+alpha
def ck(x):assert s.expand(x)==0
ck(per-24-6*hs*z-hq*z*z)
ck((r+1)**2*Q-(1-r)**4*hq/2+(2*a*r**4-4*a*r**3+2*a*r*r-4*r**3-4*r*r)*hs)
ck(a+alpha/4-(r**3-s.Rational(7,2)*r*r+12*r+s.Rational(5,2))*hs/4-(-a*r+s.Rational(3,2)*a-2)*Q/4)
ck(-a*r-(r**3-5*r*r+15*r-3)/4+r*H4/4-3*Q/4)
ck(a*r*r-(r**3-r*r-r+1)/4-r*r*H4/4+(3*r+1)*Q/4)
ck(r*(b+a*r)-(c+2*r*b+r*r*a)/2+(c-r*r*a)/2)
for token in ['(hr : r≠0) (hne : r+1≠0)','(hG : T 2 2+2*r*T 1 2+r^2*T 1 1=0)','(hK : T 2 2=r^2*T 1 1)','r^4-4*r^3+14*r^2-4*r+1=0 ∧ T=fixedT r']:
 assert token in src
print('PASS exact source',sha,'Lean exit0',data['seconds'],'sec',data['peak_rss_bytes'],'bytes; normalized matrix permanent verified 24 permutations, both scalar and both fixed-coordinate identities, nonzero-r cancellation and directional hypotheses, independent of the downstream obstruction.')
