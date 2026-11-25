from pathlib import Path
from sympy.polys.rings import ring
from sympy.polys.domains import QQ
import sympy as S
import json,hashlib
base=Path('/tmp/oec/pequalnp-pilot-78/geometry_search/rowzero')
manifest=json.loads((base/'Bzero-boundaries-manifest.json').read_text())
R,a,b,c,d=ring('a,b,c,d',QQ)
reports={}
for name,data in manifest.items():
 path=base/f'Bzero-boundary-{name}-lift2.stdout';raw=path.read_bytes();text=raw.decode()
 assert 'VERIFIED\n1' in text
 target=S.sympify(text.split('CERTIFICATE_TARGET\n')[1].splitlines()[0])
 assert target.is_Rational and target!=0
 lines=[x.strip() for x in text.split('CERTIFICATE_START\n')[1].split('CERTIFICATE_END')[0].splitlines() if x.strip()]
 assert len(lines)==len(data['generators'])
 multipliers=[R.from_expr(S.sympify(x.replace('^','**'))) for x in lines]
 generators=[R.from_expr(S.sympify(x)) for x in data['generators']]
 total=sum((g*m for g,m in zip(generators,multipliers)),R.zero)
 assert total==R.from_expr(target)
 reports[name]={'status':'PASS','target':str(target),'generator_count':len(generators),'multiplier_term_counts':[len(x) for x in multipliers],'multiplier_total_terms':sum(len(x) for x in multipliers),'stdout_bytes':len(raw),'stdout_sha256':hashlib.sha256(raw).hexdigest(),'multipliers':lines,'generators':data['generators'],'identity':'sum generators[i]*multipliers[i]=target, independently multiplied over QQ[a,b,c,d]'}
 print(json.dumps({k:v for k,v in reports[name].items() if k not in ['multipliers','generators']},sort_keys=True),flush=True)
(base/'Bzero-boundary-certificates-verified.json').write_text(json.dumps(reports,indent=2)+'\n')
