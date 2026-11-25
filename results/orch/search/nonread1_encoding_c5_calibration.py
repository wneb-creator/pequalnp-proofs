import json
from pathlib import Path
import counterexample_q3_nonread1 as m

m.base.NINPUT=5
m.base.EDGES=[(0,1),(1,2),(2,3),(3,4),(0,4)]
m.base.POSITIVE=[(1<<a)|(1<<b) for a,b in m.base.EDGES]
target=lambda s:any(s>>a&1 and s>>b&1 for a,b in m.base.EDGES)
m.base.NEGATIVE=[s for s in range(32) if not target(s) and all(target(s|(1<<i)) for i in range(5) if not s>>i&1)]
m.forced_pair=(0,1)
seed=[(op=='and',a,b) for op,a,b in json.loads(Path(__file__).with_name('c5-7-nonread1-witness.json').read_text())['gates']]
e=m.Encoding(seed,list(range(7)),m.base.POSITIVE+m.base.NEGATIVE)
e.verify_known()
report=dict(gates=7,variables=e.count,clauses=len(e.clauses),positive_patterns=len(m.base.POSITIVE),negative_patterns=len(m.base.NEGATIVE),all_clauses_validated=True,forced_pair=[0,1],read1=m.reads_pair(seed,(0,1)))
assert not report['read1']
print(json.dumps(report))
