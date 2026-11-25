from pathlib import Path
import ast,hashlib,json,re,sys,time
sys.setrecursionlimit(10000);sys.set_int_max_str_digits(0)
b=Path('/tmp/oec/pequalnp-pilot-75/gct231');start=time.monotonic()
def norm(a):
 while len(a)>1 and a[-1]==0:a.pop()
 return a
def add(a,b):
 z=[0]*max(len(a),len(b))
 for i,c in enumerate(a):z[i]+=c
 for i,c in enumerate(b):z[i]+=c
 return norm(z)
def neg(a):return [-v for v in a]
def mul(a,b):
 z=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):z[i+j]+=x*y
 return norm(z)
def power(a,n):
 out=[1]
 while n:
  if n&1:out=mul(out,a)
  a=mul(a,a);n//=2
 return out
def visit(n):
 if isinstance(n,ast.Constant) and isinstance(n.value,int):return [n.value]
 if isinstance(n,ast.Name) and n.id=='P':return [0,1]
 if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub):return neg(visit(n.operand))
 if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.UAdd):return visit(n.operand)
 if isinstance(n,ast.BinOp):
  if isinstance(n.op,ast.Add):return add(visit(n.left),visit(n.right))
  if isinstance(n.op,ast.Sub):return add(visit(n.left),neg(visit(n.right)))
  if isinstance(n.op,ast.Mult):return mul(visit(n.left),visit(n.right))
  if isinstance(n.op,ast.Pow) and isinstance(n.right,ast.Constant) and isinstance(n.right.value,int) and 0<=n.right.value<=200:return power(visit(n.left),n.right.value)
 raise ValueError(ast.dump(n))
def parse(t):return visit(ast.parse(t.replace('^','**').strip(),mode='eval').body)
src=(b/'C4Case2ProjectiveNorm.lean').read_text();lines=src.splitlines()
assert hashlib.sha256(src.encode()).hexdigest()=='bbb25336dd33dc4cf5e1047020305dc5f646e87eeb98ac847ed40cd3e016a2c0'
assert not re.search(r'_root_|"|\bsorry\b|\baxiom\b|native_decide|unsafe|implemented_by|\battribute\b|@\[',src)
assert src.count('theorem ')==1 and src.count('import ')==1
assert lines[0]=='import PEqualNP.Defs'
assert lines[4:7]==['set_option maxHeartbeats 4000000 in','set_option maxRecDepth 4096 in','theorem case2_projective_norm_obstruction (P : ℂ)']
h=[]
for i in [0,1]:
 line=lines[7+i];pre='    (h'+str(i)+' : '
 assert line.startswith(pre)
 h.append(parse(line[len(pre):].rsplit(' = 0)',1)[0]))
data=json.loads((b/'c4-case2-projective-cofactors.json').read_text())
assert h==[parse(r['norm']) for r in data['norms']]
G=parse(data['gcd']);f,g=[parse(v) for v in data['cofactors']]
assert h==[mul(G,f),mul(G,g)]
assert G==parse('(P+2)^2*(P^4-2*P^3+4*P+2)^14')
print('ACTUAL LEAN PREMISES EXACTLY MATCH BOTH NORMS; EXACT G*COFACTOR FACTORIZATIONS PASS',flush=True)
line=lines[11];assert line.startswith('    linear_combination ')
a,c=line[len('    linear_combination '):].split(' * h0 + ',1)
assert c.endswith(' * h1');c=c[:-len(' * h1')]
A,B=parse(a),parse(c)
cert=json.loads((b/'c4-case2-projective-bezout.integer-certificate.json').read_text())
assert A==list(map(int,cert['first_multiplier']))
assert B==list(map(int,cert['second_multiplier']))
scale=int(cert['scale']);assert scale>0
assert add(mul(A,f),mul(B,g))==[scale]
assert add(mul(A,h[0]),mul(B,h[1]))==[scale*c for c in G]
hg=lines[10];hd=lines[12]
assert hg=='  have hg : ('+str(scale)+' : ℂ) * ((P+2)^2 * (P^4 - 2*P^3 + 4*P + 2)^14) = 0 := by'
assert hd=='  have hd : ('+str(scale)+' : ℂ) ≠ 0 := by norm_num'
assert lines[9]=='    P + 2 = 0 ∨ P^4 - 2*P^3 + 4*P + 2 = 0 := by'
assert lines[13:17]==['  have hp := (mul_eq_zero.mp hg).resolve_left hd','  rcases mul_eq_zero.mp hp with h | h','  · exact Or.inl (pow_eq_zero h)','  · exact Or.inr (pow_eq_zero h)']
print('ACTUAL LEAN MULTIPLIERS PARSED AND EXACT INTEGER CONVOLUTION IDENTITY PASS',flush=True)
print('SCOPE PASS: only two explicit univariate premises imply P=-2 or Q=0; no premise is asserted to follow from the original C4 system.',flush=True)
out={'status':'PASS_INDEPENDENT_INTEGER_POLYNOMIAL_IDENTITY','source_sha256':hashlib.sha256(src.encode()).hexdigest(),'premise_degrees':[len(x)-1 for x in h],'gcd_degree':len(G)-1,'multiplier_degrees':[len(A)-1,len(B)-1],'scale_digits':len(str(scale)),'wall_seconds':time.monotonic()-start,'Lean_build':'not run by reviewer; source-only approval'}
(Path(__file__).parent/'verdict.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out),flush=True)
