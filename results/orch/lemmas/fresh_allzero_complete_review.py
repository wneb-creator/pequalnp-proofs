from pathlib import Path
from fractions import Fraction
import ast,re,json,hashlib
j=Path('/tmp/oec/pequalnp-pilot-79')
old=(j/'TopAllZeroMatrixBridge.lean').read_text();f=j/'TopAllZeroMatrixBridgeComplete.lean';s=f.read_text()
sha=hashlib.sha256(f.read_bytes()).hexdigest();status=json.loads((j/'root-TopAllZeroMatrixBridgeComplete-lean-status.json').read_text())
assert sha==status['source_sha256_after']==status['sha256']=='1a2e543788aac25e2bb96c996c2da600f0a91107bef1cd79e0250155895020f1' and status['exit_code']==0
assert hashlib.sha256(old.encode()).hexdigest()=='e36df83f69a3216f2cc224ee9302c090f7821da03e57c17f4e6b1d314c505549'
assert s[:s.index('  rw [perm4]')]==old[:old.index('  rw [perm4]')]
assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',s)
def expr(raw,vals):
 clean=raw.replace(': ℂ','').strip();tree=ast.parse(clean,mode='eval').body
 def rec(n):
  if isinstance(n,ast.Constant):return Fraction(n.value)
  if isinstance(n,ast.Name):return vals[n.id]
  if isinstance(n,ast.UnaryOp):return -rec(n.operand)
  a,b=rec(n.left),rec(n.right)
  return {ast.Add:lambda:a+b,ast.Sub:lambda:a-b,ast.Mult:lambda:a*b,ast.Div:lambda:a/b}[type(n.op)]()
 return rec(tree)
coef=s.split('theorem extract_equations',1)[1].split('theorem actual_matrix_equations',1)[0]
inputs={n:(t,tuple(map(int,re.findall(r'-?\d+',xyz)))) for n,t,xyz in re.findall(r'^  have ([qcr]\w+) := h([qcr]) (.*)$',coef,re.M)}
rows=re.findall(r'· linear_combination (.+)',coef);assert len(rows)==19
degree=[(k,tuple(map(int,ex))) for kind in ['quad','cubic'] for k,*ex in re.findall(r'\(p(\d+) a b c l m n h\) \* x \^ (\d) \* y \^ (\d) \* z \^ (\d)',re.search(r'def '+kind+r'[^\n]*\n  ([^\n]+)',s)[1])]
degrees=dict((int(k),e) for k,e in degree);degrees.update({17:(1,1,2),18:(1,2,1),19:(2,1,1)})
for k in range(1,20):
 vals={}
 for n,(t,xyz) in inputs.items():
  group= 'q' if k<7 else ('c' if k<17 else 'r')
  m=1
  for u,d in zip(xyz,degrees[k]):m*=u**d
  vals[n]=m if group==t else 0
 for ix,rr in enumerate(rows,1):assert expr(rr,vals)==(ix==k)
stages=re.findall(r'have hs : .*? := by\n      linear_combination (.*)',coef)
assert len(stages)==3
for d in range(2,5):
 vals={n:Fraction(w)**d for n,w in [('u1',1),('un1',-1),('u2',2),('un2',-2)]}
 for t,lc in enumerate(stages,2):assert expr(lc,vals)==(d==t)
assert all(s.count(f'    p{k} a b c l m n h = 0')==2 for k in range(20))
assert 'rw [HP x y z w] at he\n  linear_combination -he' in s
print('PASS',sha,'exact definitions, helpers and permanent_expansion statement match prior full 24-permutation integer audit; four w evaluations isolate degrees 2,3,4, 19 parsed finite differences give entire 19x19 identity on source coefficient ordering, p0=hk; actual_matrix_equations transfers universal scaled-matrix hypothesis, and repeats p0..p19. Lean',status['seconds'],'sec',status['peak_rss_bytes'],'bytes.')
