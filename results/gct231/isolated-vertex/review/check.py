from pathlib import Path
import hashlib,re,itertools,json
import sympy as S
base=Path(__file__).resolve().parents[1];source=base/'isolated-vertex/IsolatedVertex.lean';text=source.read_text()
assert hashlib.sha256(source.read_bytes()).hexdigest()=='46ca6e535347b18b674028d70744585b63112c7e0c98eb6b6479614c59644470'
a,b,c,d,e,f,g,z=S.symbols('a b c d e f g z');loc={str(x):x for x in (a,b,c,d,e,f,g,z)}
values={}
for name in ['blockSum','blockRookTwo','blockPermanent']:
 match=re.search(r'def '+name+r' \(a b c e f g : ℂ\) : ℂ :=\s*(.*?)\n\n',text,re.S);assert match
 values[name]=S.sympify(match[1].replace('^','**'),locals=loc)
M=S.Matrix([[d,0,0,0],[0,a,b,c],[0,b,e,f],[0,c,f,g]])
J=S.ones(4);N=J+z*M
# Independent Ryser formula, rather than the source's 24-permutation expansion.
per=0
for mask in range(1,16):
 indices=[j for j in range(4) if mask>>j&1]
 per+=(-1)**(4-len(indices))*S.prod(sum(N[i,j] for j in indices) for i in range(4))
s,r,p=[values[name] for name in ['blockSum','blockRookTwo','blockPermanent']]
assert S.expand(per-(24+6*(s+d)*z+2*(r+s*d)*z*z+(p+d*r)*z**3+d*p*z**4))==0
assert S.expand(d**3*S.Rational(1,6)*6*(s+d)-d*d*S.Rational(1,2)*2*(r+s*d)+d*(p+d*r)-d*p-d**4)==0
print('PASS actual Lean block formulas via independent Ryser expansion and d^4 certificate',flush=True)
L,Q,C,F=S.symbols('L Q C F');pol=L*z+Q*z*z+C*z**3+F*z**4
samples=[pol.subs(z,u) for u in [1,-1,2,-2]]
weights=[(S.Rational(2,3),-S.Rational(2,3),-S.Rational(1,12),S.Rational(1,12)),(S.Rational(2,3),S.Rational(2,3),-S.Rational(1,24),-S.Rational(1,24)),(-S.Rational(1,6),S.Rational(1,6),S.Rational(1,12),-S.Rational(1,12)),(-S.Rational(1,6),-S.Rational(1,6),S.Rational(1,24),S.Rational(1,24))]
for coeff,ws in zip([L,Q,C,F],weights):assert S.expand(sum(w*p for w,p in zip(ws,samples))-coeff)==0
print('PASS four displayed finite-evaluation coefficient identities',flush=True)
formula=text.split('lemma perm4 ',1)[1].split(':= by',1)[0]
terms=re.findall(r'M ([0-3]) ([0-3]) \* M ([0-3]) ([0-3]) \* M ([0-3]) ([0-3]) \* M ([0-3]) ([0-3])',formula)
assert len(terms)==24;perms=[]
for term in terms:
 pairs=list(zip(map(int,term[::2]),map(int,term[1::2])))
 assert sorted(x for x,y in pairs)==list(range(4)) and sorted(y for x,y in pairs)==list(range(4))
 perms.append(tuple(y for x,y in sorted(pairs)))
assert set(perms)==set(itertools.permutations(range(4)))
assert not any(x in text for x in ['sorry','axiom','native_decide','_root_','"','@['])
for line in text.splitlines():
 if line.startswith('set_option '):assert re.fullmatch(r'set_option (maxRecDepth|maxHeartbeats) [0-9]+ in',line)
run=json.loads((base/'isolated-vertex/build01.run.json').read_text());assert run['status']=='PASS' and run['returncode']==0
print('PASS complete24-term permanent formula, source format and recorded build status',flush=True)
print('SCOPE arbitrary isolated vertex, symmetry and constant permanent line imply its diagonal0; no tangent or rank premise is assumed.',flush=True)
