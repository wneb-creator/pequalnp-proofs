import sympy as s,re,hashlib
from pathlib import Path
path=Path('SparseStarPairedPlane.lean');src=path.read_text();p,c,a,d,k,b,t,r=s.symbols('p c a d k b t r');env={str(x):x for x in (p,c,a,d,k,b,t,r)}
def parse(x,ctx):return s.sympify(re.sub(r':\s*ℂ','',x).replace('^','**'),locals=ctx)
pdecl=src.split('def pairedPermanent',1)[1].split(':=',1)[1].split('def pairedPlane',1)[0];P=parse(pdecl,env);assert s.expand(P-(2*b**2*(a*d+r*r)+4*b*(a*c*c+d*p*p+2*p*c*r)+4*p*p*c*c))==0
sdecl=src.split('def pairedPlane',1)[1].split(':=',1)[1].split('set_option',1)[0];toks=re.findall(r'\([^\n]+?\)(?=\s+\(|\s*$)|(?<=pairedPermanent )b',sdecl);actual=' '.join(sdecl.split());assert actual=='pairedPermanent b (p + (1 - p) * b) (c + (1 - c) * b) (a + (1 - a) * b + (k - 1) * t) (b + t) (d + (1 - d) * b - (1 + k) * t)'
P=P.subs({p:p+(1-p)*b,c:c+(1-c)*b,a:a+(1-a)*b+(k-1)*t,r:b+t,d:d+(1-d)*b-(1+k)*t},simultaneous=True)-24;ctx=env.copy()
proof=src.split('theorem paired_plane_impossible',1)[1]
for name,B,T in re.findall(r'have (h\w+) := h (\(-?\d+(?: / \d+)?\)|-?\d+) (\(-?\d+(?: / \d+)?\)|-?\d+)',proof):
 ctx[name]=P.subs({b:parse(B,{}),t:parse(T,{})})
for name,lhs,rhs,comb in re.findall(r'  have (h\w+) : (.*?) = (.*?) := by\n    linear_combination (.*?)(?=\n  (?:have|exact))',proof,re.S):
 assert '\n' not in lhs;goal=parse(lhs,env)-parse(rhs,env);val=parse(comb,ctx);assert s.expand(goal-val)==0,name;ctx[name]=goal
 print('verified',name)
assert set(['hk','hH','hS','hD','hN','hE'])<=ctx.keys();print('PASS actual pairedPermanent and pairedPlane definitions; all16 sample substitutions and six actual-source linear combinations hold exactly over Q. SHA256',hashlib.sha256(path.read_bytes()).hexdigest())
