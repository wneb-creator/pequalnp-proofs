from pathlib import Path
from datetime import datetime,timezone
import itertools,json,resource
import sympy as s
resource.setrlimit(resource.RLIMIT_CPU,(40,42))
resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3))
base=Path(__file__).resolve().parent
data=json.loads((base/'explore.json').read_text())
vs=list(s.symbols(' '.join(data['parameters'])))
eq=list(map(lambda d:s.sympify(d['expression']),data['equations']))
print('Start UTC',datetime.now(timezone.utc).isoformat(),flush=True)
for free in itertools.combinations(vs,2):
 sub={v:0 for v in vs if v not in free}
 pols=[s.expand(p.subs(sub)) for p in eq]
 G=s.groebner(pols,*free,extension=s.sqrt(2))
 print('FREE',free,'BASIS',list(G),flush=True)
 if list(G)!=[1]:
  try:print('SOLUTIONS',s.solve_poly_system(list(G),*free),flush=True)
  except NotImplementedError:print('POSITIVE_DIMENSION_OR_UNSOLVED',flush=True)
print('Finish UTC',datetime.now(timezone.utc).isoformat(),flush=True)
