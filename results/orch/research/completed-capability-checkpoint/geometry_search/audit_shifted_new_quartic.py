from pathlib import Path
from fractions import Fraction
from collections import defaultdict
import json,subprocess,sympy as s,hashlib
base=Path('/tmp/oec/pequalnp-pilot-78');job=base/'numeric/shifted-full31'
source=base/'geometry_search/tracezero_rankdrop/full31-shifted.json';raw=json.loads(source.read_text());new=json.loads((job/'new-quartic.json').read_text());cert=json.loads((job/'D5-certificates.jsonl').read_text());maps=json.loads(subprocess.check_output(['zstd','-q','-d','-c',str(job/'D5-rowmap.json.zst')]))
vs=s.symbols(' '.join(raw['variables']));assert raw['variables']==new['variables'];gens=[]
for f in raw['generators']:
 p=s.Poly(s.sympify(f),*vs,domain=s.QQ);d={}
 for exp,c in p.terms():d[tuple(i for i,e in enumerate(exp) for _ in range(e))]=Fraction(int(c.p),int(c.q))
 gens.append(d)
encoded=json.loads((job/'generators.json').read_text());assert len(encoded)==len(gens)==31
for direct,other in zip(gens,encoded):assert direct=={tuple(m):Fraction(c) for m,c in other}
target={tuple(m):Fraction(c) for m,c in new['polynomial']};target2={tuple(maps['columns'][i]):Fraction(c) for i,c in cert['polynomial']};assert target==target2
assert new['certificate']==cert['certificate']
acc=defaultdict(Fraction)
for i,weight in new['certificate']:
 gi,mult=maps['rows'][i];weight=Fraction(weight)
 for mon,c in gens[gi].items():acc[tuple(sorted(tuple(mult)+mon))]+=weight*c
acc={m:c for m,c in acc.items() if c};assert acc==target
assert max(map(len,target))==4 and len(target)==247
r={'status':'PASS','source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'target_terms':len(target),'certificate_terms':len(new['certificate']),'independent_exact_residual':'0','method':'Reparsed all31 source polynomials independently, checked encoded generator equality, expanded72 rational generator-monomial products via Fraction arithmetic, compared every coefficient to both exported target encodings.','scope':'Exact necessary degree4 consequence; not a unit identity or global proof. Suitable as a redundant generator in the full31 fallback.'}
(base/'geometry_search/shifted-new-quartic-independent-audit.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
