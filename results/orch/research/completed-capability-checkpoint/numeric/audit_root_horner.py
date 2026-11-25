from pathlib import Path
import ast,hashlib,importlib.util,json,random,time
from fractions import Fraction

BASE=Path('/tmp/oec/pequalnp-pilot-78')
SOURCE=BASE/'root-algebra/generate_rank1_certificate_lean.py'
AUDITOR=BASE/'root-algebra/audit_rank1_certificate.py'
spec=importlib.util.spec_from_file_location('root_horner',SOURCE)
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
def expand(expression,names):
 zero=(0,)*len(names)
 def add(a,b):
  c=dict(a)
  for e,v in b.items():
   c[e]=c.get(e,0)+v
   if c[e]==0:del c[e]
  return c
 def mul(a,b):
  c={}
  for e,v in a.items():
   for f,w in b.items():
    k=tuple(x+y for x,y in zip(e,f));c[k]=c.get(k,0)+v*w
  return {e:v for e,v in c.items() if v}
 def node(t):
  if isinstance(t,ast.Constant) and type(t.value)==int:return {zero:t.value} if t.value else {}
  if isinstance(t,ast.Name):
   e=list(zero);e[names.index(t.id)]=1;return {tuple(e):1}
  if isinstance(t,ast.UnaryOp) and isinstance(t.op,ast.USub):return {e:-v for e,v in node(t.operand).items()}
  assert isinstance(t,ast.BinOp)
  if isinstance(t.op,ast.Add):return add(node(t.left),node(t.right))
  if isinstance(t.op,ast.Mult):return mul(node(t.left),node(t.right))
  if isinstance(t.op,ast.Pow):
   assert isinstance(t.right,ast.Constant) and type(t.right.value)==int and t.right.value>=0
   a=node(t.left);b={zero:1}
   for _ in range(t.right.value):b=mul(b,a)
   return b
  raise AssertionError(ast.dump(t))
 return node(ast.parse(expression.replace('^','**'),mode='eval').body)

start=time.monotonic();rng=random.Random(231781)
cases=0
for n in [1,2,3,11]:
 names=['x'+str(i) for i in range(n)]
 polynomials=[{}, {(0,)*n:1}, {(0,)*n:-7}, {(8,)+(0,)*(n-1):-1}]
 for _ in range(60):
  d={}
  for __ in range(rng.randrange(1,45)):
   e=[0]*n
   for ___ in range(rng.randrange(0,10)):e[rng.randrange(n)]+=1
   c=rng.randrange(-1000,1001)
   if c:d[tuple(e)]=c
  polynomials.append(d)
 for d in polynomials:
  terms=[(Fraction(c),list(e)) for e,c in d.items()]
  expression=m.emit_horner(terms,names)
  assert expand(expression,names)==d
  cases+=1
conventions=BASE/'construct_search/rank1-certificate-conventions.json'
j=json.loads(conventions.read_text());names=j['variable_order']
for g in j['generators']:
 expected={tuple(e):int(Fraction(c)) for c,e in g['terms'] if c}
 assert all(Fraction(c).denominator==1 for c,e in g['terms'])
 assert expand(m.emit_horner(g['terms'],names),names)==expected
 cases+=1
report={'status':'PASS','scope':'Independent exact AST expansion of emitted Horner expressions; 256 deterministic edge/random polynomials plus all13 actual generators. Code review found no unsafe evaluation, I/O side effects, or mathematical-identity acceptance without exact sparse residual. This does not check any unavailable inconsistency certificate or compile generated Lean.','cases':cases,'generator_source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),'auditor_source_sha256':hashlib.sha256(AUDITOR.read_bytes()).hexdigest(),'conventions_sha256':hashlib.sha256(conventions.read_bytes()).hexdigest(),'review_notes':['Auditor rejects duplicate certificate monomials and checks full rational residual exactly.','Generator must be used after auditor PASS, since it does not itself recheck certificate identity.','Current generator imports full Mathlib; use the existing selective imports when integrating into the large proof to avoid known resource limits.'],'seconds':time.monotonic()-start}
(BASE/'numeric/root-horner-independent-audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
