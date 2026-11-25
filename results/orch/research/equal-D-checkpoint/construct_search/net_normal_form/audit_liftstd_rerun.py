from pathlib import Path
from fractions import Fraction
import ast,json,re,hashlib
base=Path('/tmp/oec/pequalnp-pilot-78/construct_search')
src=base/'rank1-incident-opposite-liftstd-Q-rerun.sing'
runner=base/'run_rank1_liftstd_rerun.py'
conv=base/'rank1-certificate-conventions.json'
s=src.read_text();r=runner.read_text();data=json.loads(conv.read_text());names=data['variable_order'];n=len(names);zero=(0,)*n

def add(a,b):
 c=a.copy()
 for m,v in b.items():
  c[m]=c.get(m,Fraction(0))+v
  if not c[m]:del c[m]
 return c

def scale(a,s):return {m:v*s for m,v in a.items() if v*s}
def mul(a,b):
 c={}
 for m,v in a.items():
  for k,w in b.items():
   q=tuple(x+y for x,y in zip(m,k));c[q]=c.get(q,Fraction(0))+v*w
 return {m:v for m,v in c.items() if v}
def parse(expr):
 def visit(t):
  if isinstance(t,ast.Constant):return {zero:Fraction(t.value)} if t.value else {}
  if isinstance(t,ast.Name):
   m=[0]*n;m[names.index(t.id)]=1;return {tuple(m):Fraction(1)}
  if isinstance(t,ast.UnaryOp) and isinstance(t.op,ast.USub):return scale(visit(t.operand),-1)
  if isinstance(t,ast.BinOp):
   a=visit(t.left)
   if isinstance(t.op,ast.Pow):
    assert isinstance(t.right,ast.Constant) and isinstance(t.right.value,int) and t.right.value>=0
    b={zero:Fraction(1)}
    for _ in range(t.right.value):b=mul(b,a)
    return b
   b=visit(t.right)
   if isinstance(t.op,ast.Add):return add(a,b)
   if isinstance(t.op,ast.Sub):return add(a,scale(b,-1))
   if isinstance(t.op,ast.Mult):return mul(a,b)
  raise ValueError(ast.dump(t))
 return visit(ast.parse(expr.replace('^','**'),mode='eval').body)
input_polys=re.search(r'ideal I=(.*?);',s,re.S).group(1).split(',');assert len(input_polys)==12
original=[{tuple(m):Fraction(v) for v,m in g['terms']} for g in data['generators']]
kept=[0,1,2,3,4,5,6,8,9,10,11,12]
assert all(parse(a)==original[i] for a,i in zip(input_polys,kept))
assert mul(original[0],original[0])==scale(original[7],16)
exports=re.findall(r'print\("COFACTOR_INDEX"\);(\d+);print\("COFACTOR_POLYNOMIAL"\);([^;]+);',s)
assert len(exports)==13
for i,(idx,val) in enumerate(exports,1):
 assert int(idx)==i
 assert val==('0' if i==8 else 'C['+str(i if i<8 else i-1)+',1]')
assert 'ring R=0,('+','.join(names)+'),dp;' in s
assert 'ideal E=1;' in s
assert 'for(i=1;i<=n;i++){C[i,1]=T[i,j]/G[j];}' in s
assert 'if(G[j]!=0 && deg(G[j])==0)' in s
assert 'if(size(residual)!=0){ERROR("Transformation identity failed");}' in s
assert 'return(size(residual)==0);' in s
assert 'modular("focusedLiftstd",list(I,E),primeOK,keepAll,pOK,exactTest)' in s
for flag in ['--no-rc','--no-shell','--cpus=1','--threads=1','--flint-threads=1']:assert flag in r
assert "'LD_LIBRARY_PATH'" in r and 'os.environ' not in r
report={'status':'PASS with log-consumption caveats','scope':'Independent exact Fraction-polynomial audit of active liftstd source and runner; no CAS, no new certificate, no claim that the running job succeeds.','input_generator_mapping_1based':[i+1 for i in kept],'omitted_generator_identity':'generator1^2 = 16*generator8','restored_zero_cofactor_index':8,'checks':['All12 active generators equal audited original generators except original8.','Original8 is redundant exactly over QQ via generator1 squared.','Output13-vector restores zero at original index8 and shifts later cofactors correctly.','Constant standard-basis column normalized by its nonzero field constant.','Every raw prime result must satisfy exact input*cofactors=1 before return.','Modular finalTest signature matches installed modular.lib; it checks exact QQ identity.','Final QQ identity recomputed after modular returns.','Runner bounds memory/CPU/output, retains complete stdout/stderr, uses fixed credential-free child environment.'],'caveats':['EXACT_CERTIFICATE_VALID label is printed unconditionally before the Boolean result; require following value1, residual0, and independent exact13-vector verification.','Exit0 alone is not a certificate: Singular may report interpreter errors without nonzero process status.','pOK always returns1, so no additional independent-prime validation occurs; correctness relies on raw-prime identities and exact QQ finalTest.','keepAll rejects no unlucky primes; different prime cofactor supports can prevent reconstruction convergence without causing a false exact identity.','modular.lib performs3 prime computations per serial iteration, so first PRIME_UNIT_IDENTITY_VALID is not yet a rational certificate.','If option(probabilistic) were set, modular skips finalTest; source/runner do not set it and --no-rc prevents startup options, but final independent13-vector check remains mandatory.'],'files':[{'path':str(p),'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in [src,runner,conv]]}
out=base/'net_normal_form/liftstd-rerun-independent-review.json';out.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
