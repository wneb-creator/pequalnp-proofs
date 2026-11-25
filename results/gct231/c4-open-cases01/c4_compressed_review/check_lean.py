"""Parse actual Lean arithmetic independently; verify emitted polynomial identities."""
from pathlib import Path
from fractions import Fraction as Q
import ast,json,re,hashlib
import sympy as S
from verify_certificate import input_polynomials,decode
base=Path(__file__).resolve().parents[1];out=Path(__file__).parent
zero=(0,0)
def clean(p):return {e:c for e,c in p.items() if c}
def add(p,q):
 r=p.copy()
 for e,c in q.items():r[e]=r.get(e,Q(0))+c
 return clean(r)
def scale(p,c):return clean({e:v*c for e,v in p.items()})
def multiply(p,q):
 r={}
 for e,a in p.items():
  for f,b in q.items():
   g=tuple(x+y for x,y in zip(e,f));r[g]=r.get(g,Q(0))+a*b
 return clean(r)
context={'x0':{(1,0):Q(1)},'x1':{(0,1):Q(1)}}
def evaluate(text):
 node=ast.parse(text.replace(': ℂ','').replace('^','**').strip(),mode='eval').body
 def visit(n):
  if isinstance(n,ast.Constant):assert type(n.value)==int;return clean({zero:Q(n.value)})
  if isinstance(n,ast.Name):return context[n.id]
  if isinstance(n,ast.UnaryOp):
   assert isinstance(n.op,(ast.UAdd,ast.USub));return scale(visit(n.operand),-1 if isinstance(n.op,ast.USub) else 1)
  assert isinstance(n,ast.BinOp)
  if isinstance(n.op,ast.Pow):
   assert isinstance(n.right,ast.Constant) and type(n.right.value)==int and n.right.value>=0
   result={zero:Q(1)};factor=visit(n.left)
   for _ in range(n.right.value):result=multiply(result,factor)
   return result
  p,q=visit(n.left),visit(n.right)
  if isinstance(n.op,ast.Add):return add(p,q)
  if isinstance(n.op,ast.Sub):return add(p,scale(q,-1))
  if isinstance(n.op,ast.Mult):return multiply(p,q)
  assert isinstance(n.op,ast.Div) and set(q)=={zero} and q[zero]
  return scale(p,1/q[zero])
 return visit(node)

certificate=json.loads((base/'c4-small-certificates/case0-v_nonzero-nosat.certificate.json').read_text())
steps={step['index']:step for step in certificate['steps']}
source=base/'c4-small-certificates/C4Case0Nonzero.lean';text=source.read_text()
assert hashlib.sha256(source.read_bytes()).hexdigest()=='99a2284e7cb3e67f20d24bf7617d51416f37de56442edcfbd25e14ce770fbf46'
hypotheses=[];identities=0;seen=[];lines=text.splitlines()
for pos,line in enumerate(lines):
 hyp=re.fullmatch(r'\s+\(h(\d+) : \((.*) : ℂ\) = 0\)',line)
 have=re.fullmatch(r'\s+have h(\d+) : \((.*) : ℂ\) = 0 := by',line)
 if not(hyp or have):continue
 match=hyp or have;idx=int(match[1]);poly=evaluate(match[2])
 assert idx in steps and poly==decode(steps[idx]['polynomial'],2)
 assert idx not in seen;seen.append(idx)
 if hyp:
  assert 'generator' in steps[idx]['kind'];hypotheses.append(idx)
 else:
  assert 'output_node' in steps[idx]['kind']
  prefix='    linear_combination ';assert lines[pos+1].startswith(prefix)
  assert evaluate(lines[pos+1][len(prefix):])==poly,idx
  identities+=1
 context['h'+str(idx)]=poly
assert hypotheses==[0,1,3]
assert context['h25']==evaluate('(x0+x1)^2')
assert context['h21']==evaluate('(x1^2-x1-1)^2')
assert evaluate('(x1^2-x1-1)+(x0-x1+1)*(x0+x1)')==evaluate('x0^2+x0-1')
assert '    (h_open : x0 ^ 2 + x0 - 1 ≠ 0) : False := by' in lines
assert len(re.findall(r'^theorem ',text,re.M))==1
assert not any(x in text for x in ['sorry','axiom','native_decide','_root_','"','@['])
print('PASS actual Lean arithmetic:',hypotheses,'generator premises,',identities,'derived identities, exact squared targets and final contradiction identity',flush=True)

# Match the unsaturated companion roots with the already reviewed raw four equations.
names,roots=input_polynomials(Path(certificate['input']))
x0,x1=S.symbols('x0 x1');beta,gamma=S.symbols('beta gamma')
raw=json.loads((base/'c4-nonzero-bivariate-0.json').read_text())['branches']['v_nonzero']
expected=[]
for row in raw:
 p=S.Poly(S.sympify(row,locals={'beta':x0,'gamma':x1}),x0,x1,domain=S.QQ)
 expected.append({e:Q(str(c)) for e,c in p.terms()})
assert roots==expected
print('PASS exact four unsaturated source roots; actual theorem uses only roots0,1,3',flush=True)

# Independently check the signed symmetry on every raw equation.
d0=json.loads((base/'c4-nonzero-bivariate-0.json').read_text())
d1=json.loads((base/'c4-nonzero-bivariate-1.json').read_text())
for branch,signs in [('v_zero',[1,1,1,1]),('v_nonzero',[1,-1,1,-1])]:
 for i,sign in enumerate(signs):
  p=S.sympify(d0['branches'][branch][i],locals={'beta':beta,'gamma':gamma})
  q=S.sympify(d1['branches'][branch][i],locals={'beta':beta,'gamma':gamma})
  assert S.expand(p.subs(gamma,-gamma)-sign*q)==0
print('PASS exact gamma-sign symmetry of all eight equations; open beta factor unchanged',flush=True)

# Preserve the rejected wrapper candidate's byte identity and exact stale bullet.
combined=(base/'c4-small-certificates/C4OpenCases01.lean').read_text()
assert hashlib.sha256(combined.encode()).hexdigest()=='98ffc97fdfa13644182260bef945c6f7cd43c7e58a58954d45fc4c96d14d32b8'
body=text.split('namespace PEqualNP.Outside.L_gct_231.trace\n',1)[1].rsplit('end PEqualNP.Outside.L_gct_231.trace',1)[0].strip()
assert body in combined
wrapper=combined.split('theorem c4_open_1_v_nonzero',1)[1]
assert '(h2 :' not in wrapper and '  · linear_combination h2\n' in wrapper
print('CONFIRMED failed combined wrapper has stale h2 bullet; case0 body byte-preserved',flush=True)
print('SCOPE: scratch global options need scoped-in conversion before named-file integration.',flush=True)
