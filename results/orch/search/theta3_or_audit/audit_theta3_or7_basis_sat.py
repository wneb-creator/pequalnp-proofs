from pathlib import Path
import sys,json,subprocess,time
sys.path.insert(0, '/workspace/pequalnp-proofs/results/orch/search')
from repair_nearmiss_v3 import CNF,SOLVER
root=Path('/tmp/oec/pequalnp-pilot-64')
c=CNF(); selectors=[]
for j in range(7):
    pair=[]
    for side in range(2):
        ss=[c.new() for _ in range(8+j)]
        c.add(*ss)
        pair.append(ss)
    selectors.append(pair)
output=[c.new() for _ in range(15)];c.add(*output)
def conjunction(ss,w):
    value=1
    for s,a in zip(ss,w):value=c.land(value,c.lor(-s,a))
    return value
edges=[(0,2),(2,5),(5,1),(0,3),(3,6),(6,1),(0,4),(4,7),(7,1)]
def target_fn(mask):return any(mask>>a&1 and mask>>b&1 for a,b in edges)
positives=[(1<<a)|(1<<b) for a,b in edges]
negatives=[mask for mask in range(256) if not target_fn(mask) and all(target_fn(mask|(1<<i)) for i in range(8) if not mask>>i&1)]
assert all(target_fn(m)==any(m&p==p for p in positives) and (not target_fn(m))==any(m&n==m for n in negatives) for m in range(256))
rows=positives+negatives
for mask in rows:
    w=[1 if mask>>i&1 else -1 for i in range(8)]
    for a,b in selectors:w.append(c.lor(conjunction(a,w),conjunction(b,w)))
    value=conjunction(output,w)
    target=any(mask>>a&1 and mask>>b&1 for a,b in [(0,2),(2,5),(5,1),(0,3),(3,6),(6,1),(0,4),(4,7),(7,1)])
    c.add(value if target else -value)
cnf=root/'audit-theta3-or7-basis.cnf';c.write(cnf)
start=time.time()
with (root/'audit-theta3-or7-basis.stdout').open('w') as out,(root/'audit-theta3-or7-basis.stderr').open('w') as err:
    p=subprocess.run([str(SOLVER),'-t','30',str(cnf)],stdout=out,stderr=err)
summary={'or_gates':7,'basis_rows':len(rows),'negative_rows':negatives,'arbitrary_and_regions':True,'variables':c.n,'clauses':len(c.cs),'solver_code':p.returncode,'seconds':time.time()-start}
if p.returncode==10:
    truth={int(x) for line in (root/'audit-theta3-or7-basis.stdout').read_text().splitlines() if line.startswith('v ') for x in line[2:].split() if int(x)>0}
    def bits(ss):return sum(1<<i for i,s in enumerate(ss) if s in truth)
    summary['normalized_or_gates']=[[bits(a),bits(b)] for a,b in selectors]+[bits(output)]
(root/'audit-theta3-or7-basis-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary),flush=True)
