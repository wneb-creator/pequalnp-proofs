from pathlib import Path
from fractions import Fraction
import hashlib,json,time
import sympy as s
base=Path('/tmp/oec/pequalnp-pilot-75/gct231/triangle-kernel-zero');start=time.monotonic()
source=json.loads((base/'star-lowdegree.json').read_text());data=json.loads((base/'star-r-flat-certificate.json').read_text())
assert source['unknowns']==data['variables']==['p','q','r','a','b']
xs=s.symbols(data['variables']);n=len(xs)
def read(rows):
 out={}
 for mon,c in rows:
  key=tuple(mon);assert len(key)==n and all(type(e)==int and e>=0 for e in key)
  assert key not in out and Fraction(c)!=0;out[key]=Fraction(c)
 return out
gens=[read(rows) for rows in data['generators']];mults=[read(rows) for rows in data['multipliers']]
assert len(gens)==len(mults)==len(source['equations'])
for i,(g,row) in enumerate(zip(gens,source['equations'])):
 p=s.Poly(s.sympify(row['coefficient'],locals=dict(zip(data['variables'],xs))),*xs,domain=s.QQ)
 p=p.clear_denoms()[1].primitive()[1]
 expected={tuple(m):Fraction(str(c)) for m,c in p.terms()}
 assert g==expected,i
print('EXACT GENERATOR ORDER AND PRIMITIVE SCALINGS PASS',len(gens),flush=True)
out={}
for g,m in zip(gens,mults):
 for a,x in g.items():
  for b,y in m.items():
   key=tuple(i+j for i,j in zip(a,b));out[key]=out.get(key,Fraction(0))+x*y
out={m:c for m,c in out.items() if c}
assert out==read(data['target'])=={(0,0,1,0,0):Fraction(1)}
verdict={'status':'PASS_INDEPENDENT_EXACT_RATIONAL_CONVOLUTION','source_sha256':hashlib.sha256((base/'star-lowdegree.json').read_bytes()).hexdigest(),'certificate_sha256':hashlib.sha256((base/'star-r-flat-certificate.json').read_bytes()).hexdigest(),'generators':len(gens),'nonzero_multipliers':sum(bool(x) for x in mults),'multiplier_terms':sum(len(x) for x in mults),'identity':'sum multiplier_i * exact primitive source_generator_i = r','seconds':time.monotonic()-start,'scope':'Conditional explicit polynomial identity; geometry and nonzero-a/b derivation of added E equations separately reviewed by c3; no Lean build here.'}
(Path(__file__).parent/'verdict.json').write_text(json.dumps(verdict,indent=2)+'\n');print(json.dumps(verdict),flush=True)
