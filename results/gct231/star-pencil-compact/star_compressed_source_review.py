from pathlib import Path
from datetime import datetime,timezone
from fractions import Fraction
import json,hashlib,re,math,ast
import sympy as s
base=Path(__file__).resolve().parent
print('Start UTC',datetime.now(timezone.utc).isoformat(),flush=True)
path=base/'StarPencilClassificationCompressed.lean';src=path.read_text();sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(path)=='fc97915621bef10f7bab6d5f77eeb8d566786fadc27fcca5d7b5d00896ad6963'
d=json.loads((base/'star-r-native-compressed-certificate.json').read_text());low=json.loads((base/'star-lowdegree.json').read_text());names=d['variables'];vs=s.symbols(names);loc=dict(zip(names,vs));assert names==low['unknowns']
def todict(terms):return {tuple(mon):Fraction(c) for mon,c in terms}
gens=list(map(todict,d['generators']));ms=list(map(todict,d['multipliers']))
for got,row in zip(gens,low['equations']):
 poly=s.Poly(s.sympify(row['coefficient'],locals=loc),*vs,domain=s.QQ);_,ip=poly.clear_denoms();_,prim=ip.primitive();assert got=={m:Fraction(c) for m,c in prim.terms()}
D=math.lcm(*[c.denominator for m in ms for c in m.values()]);assert D==61193160
# Read the actual emitted syntax using a small independent sparse integer-polynomial parser.
allnames=names+['h'+str(i) for i in range(8)];n=len(allnames);zero=(0,)*n
def add(a,b):
 c=dict(a)
 for m,v in b.items():c[m]=c.get(m,0)+v
 return {m:v for m,v in c.items() if v}
def mul(a,b):
 c={}
 for m,v in a.items():
  for k,w in b.items():
   z=tuple(x+y for x,y in zip(m,k));c[z]=c.get(z,0)+v*w
 return {m:v for m,v in c.items() if v}
def parse(text):
 def run(t):
  if isinstance(t,ast.Constant):assert isinstance(t.value,int);return {zero:t.value} if t.value else {}
  if isinstance(t,ast.Name):m=[0]*n;m[allnames.index(t.id)]=1;return {tuple(m):1}
  if isinstance(t,ast.UnaryOp) and isinstance(t.op,ast.USub):return {m:-v for m,v in run(t.operand).items()}
  if isinstance(t,ast.BinOp):
   if isinstance(t.op,ast.Add):return add(run(t.left),run(t.right))
   if isinstance(t.op,ast.Sub):return add(run(t.left),{m:-v for m,v in run(t.right).items()})
   if isinstance(t.op,ast.Mult):return mul(run(t.left),run(t.right))
   if isinstance(t.op,ast.Pow):
    assert isinstance(t.right,ast.Constant) and isinstance(t.right.value,int) and t.right.value>=0
    a=run(t.left);v={zero:1}
    for _ in range(t.right.value):v=mul(v,a)
    return v
  raise AssertionError(ast.dump(t))
 return run(ast.parse(text.replace('^','**'),mode='eval').body)
hyps=re.findall(r'    \(h(\d+) : \((.*?) : ℂ\) = 0\)',src)
assert len(hyps)==14
for i,expr in hyps:
 got=parse(expr);want={m+(0,)*8:int(v) for m,v in gens[int(i)].items()};assert got==want
line=next(line for line in src.splitlines() if line.startswith('    linear_combination '));actual=parse(line[len('    linear_combination '):]);expected={}
for i,m in enumerate(ms):
 for mon,c in m.items():
  hs=[0]*8;hs[i]=1;expected[mon+tuple(hs)]=int(c*D)
assert actual==expected
result={}
for g,m in zip(gens,ms):
 for a,c in g.items():
  for b,e in m.items():
   mon=tuple(x+y for x,y in zip(a,b));result[mon]=result.get(mon,Fraction(0))+c*e
result={m:c for m,c in result.items() if c};assert result==todict(d['target'])=={(0,0,1,0,0):Fraction(1)}
print('Actual Lean hypothesis and balanced linear_combination syntax parsed independently; all7used primitive generators and244 multiplier terms match exact certificate. Sparse Fraction multiplication gives r exactly: PASS',flush=True)
assert ms[0]=={} and [i for i,m in enumerate(ms) if m]==list(range(1,8))
p,q,r,a,b=vs
for i,var in [(6,p),(7,q)]:assert s.expand(sum(s.Rational(c.numerator,c.denominator)*s.prod(v**e for v,e in zip(vs,m)) for m,c in gens[i].items()).subs(r,0))==-var
for i,var in [(2,a),(5,b)]:assert s.expand(sum(s.Rational(c.numerator,c.denominator)*s.prod(v**e for v,e in zip(vs,m)) for m,c in gens[i].items()).subs({p:0,q:0,r:0})-(var+1)**2)==0
print('Elementary second theorem: r=0 gives p=q=0, normalized quadratics give(a+1)^2=(b+1)^2=0; no additional assumptions or divisions: PASS',flush=True)
assert len(re.findall(r'^theorem ',src,re.M))==2 and not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',src)
assert all(' in' in x for x in re.findall(r'^set_option.*$',src,re.M))
old=(base/'StarPencilClassification.lean').read_text().splitlines();new=src.splitlines()
assert len(old)==len(new)==52
assert all(a==b for i,(a,b) in enumerate(zip(old,new)) if i not in [17,18])
assert sum(len(m) for m in ms)==244
print('All original seven hypotheses, theorem conclusions, options and elementary corollary byte-identical; only denominator and linear_combination certificate changed: PASS',flush=True)
print('Scoped options, two explicit conditional scalar theorems, standard proof tactics; no geometry/whole-gap claim. Source review only, compilation owned separately.',flush=True)
print('Hashes',json.dumps({name:sha(base/name) for name in ['StarPencilClassificationCompressed.lean','emit_star_lean.py','star-r-native-compressed-certificate.json','star-lowdegree.json']}),flush=True)
print('Finish UTC',datetime.now(timezone.utc).isoformat(),flush=True);print('PASS',flush=True)
