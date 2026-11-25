import json,z3
from pathlib import Path
from or_elimination_search import search
z3.set_param('memory_max_size',256)
edges=[(0,2),(2,1),(0,3),(3,4),(4,1),(0,5),(5,6),(6,1)]
r=search(7,edges,7,timeout=90000)
r['name']='theta233'
r['scope']='No minimality claim; every OR operand replacement loses at least two edges'
Path('/tmp/oec/pequalnp-pilot-55/normal-form-theta-elim.json').write_text(json.dumps(r,indent=2))
print(json.dumps(r),flush=True)
