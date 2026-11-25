from pathlib import Path
from collections import defaultdict
import json,hashlib,time,resource
import sympy as s
from sympy.polys.rings import ring
from sympy.polys.domains import ZZ
resource.setrlimit(resource.RLIMIT_CORE,(0,0))
resource.setrlimit(resource.RLIMIT_AS,(700*1024**2,700*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(45,45))
start=time.monotonic();job=Path('/tmp/oec/pequalnp-pilot-79')
certfile=job/'root-allzero-original-exact-certificate.json';c=json.loads(certfile.read_text())
inputfile=job/'fresh_top_allzero_0.msolve';lines=inputfile.read_text().splitlines();names=lines[0].split(',')
assert c['variables']==names and lines[1]=='0'
assert inputfile.read_bytes()==Path('/workspace/pequalnp-proofs/results/orch/lemmas/fresh_top_allzero_0.msolve').read_bytes()
R,*vs=ring(','.join(names),ZZ);local=dict(zip(names,s.symbols(' '.join(names))))
polys=[R.from_expr(s.sympify(q.replace('^','**'),locals=local)) for q in ''.join(lines[2:]).split(',') if q]
assert len(polys)==len(c['multipliers'])==20
assert isinstance(c['denominator'],int) and c['denominator']>0
out=defaultdict(int);terms=0
for i,(f,entries) in enumerate(zip(polys,c['multipliers'])):
 assert len(entries)==c['terms'][i]
 seen=set()
 for e,a in entries:
  e=tuple(e);assert e not in seen;seen.add(e)
  assert len(e)==len(names) and all(isinstance(x,int) and x>=0 for x in e)
  assert isinstance(a,int) and a!=0
  terms+=1
  for m,b in f.items():out[tuple(x+y for x,y in zip(e,m))]+=a*int(b)
actual={m:a for m,a in out.items() if a};assert actual=={(0,)*len(names):c['denominator']}
print(json.dumps({'integer_identity_verified':True,'input_equations':len(polys),'multiplier_support':terms,'constant_bits':c['denominator'].bit_length(),'input_sha256':hashlib.sha256(inputfile.read_bytes()).hexdigest(),'certificate_sha256':hashlib.sha256(certfile.read_bytes()).hexdigest(),'source_variable_order':names,'scope':'Exact characteristic-zero obstruction for the conditional all-three-complementary-diagonal-restrictions-zero normalized coefficient system; no Lean or global coverage claim','seconds':time.monotonic()-start},indent=2))
