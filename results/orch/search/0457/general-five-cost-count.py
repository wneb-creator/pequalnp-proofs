import hashlib,importlib.util,json,resource,time
from pathlib import Path
root=Path('/tmp/oec/pequalnp-pilot-21/search')
spec=importlib.util.spec_from_file_location('cost_counted',root/'cegis-general-five-cost.py')
q=importlib.util.module_from_spec(spec);spec.loader.exec_module(q)
class CountOnly(q.f.b.CNF):
 def __init__(self):self.n=0;self.clauses=0;self.body_bytes=0
 def add(self,*xs):self.clauses+=1;self.body_bytes+=len(' '.join(map(str,xs)))+3
started=time.monotonic();c=CountOnly();q.encode(c,q.f.ROWS)
r={'status':'COUNTED_NO_CNF_OR_SOLVER','variables':c.n,'clauses':c.clauses,'exact_DIMACS_bytes':c.body_bytes+len(f'p cnf {c.n} {c.clauses}\n'),'elapsed_seconds':time.monotonic()-started,'max_RSS_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'source_sha256':hashlib.sha256((root/'cegis-general-five-cost.py').read_bytes()).hexdigest()}
(root/'general-five-cost-count.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
