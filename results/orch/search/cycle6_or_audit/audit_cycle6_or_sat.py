from pathlib import Path
import sys,json,subprocess,time
sys.path.insert(0, '/workspace/pequalnp-proofs/results/orch/search')
from repair_nearmiss_v3 import CNF,SOLVER
root=Path('/tmp/oec/pequalnp-pilot-64')
c=CNF(); selectors=[]
for j in range(4):
    pair=[]
    for side in range(2):
        ss=[c.new() for _ in range(6+j)]
        c.add(*ss)
        pair.append(ss)
    selectors.append(pair)
output=[c.new() for _ in range(10)];c.add(*output)
def conjunction(ss,w):
    value=1
    for s,a in zip(ss,w):value=c.land(value,c.lor(-s,a))
    return value
for mask in range(64):
    w=[1 if mask>>i&1 else -1 for i in range(6)]
    for a,b in selectors:w.append(c.lor(conjunction(a,w),conjunction(b,w)))
    value=conjunction(output,w)
    target=any(mask>>i&1 and mask>>((i+1)%6)&1 for i in range(6))
    c.add(value if target else -value)
cnf=root/'audit-cycle6-or4.cnf';c.write(cnf)
start=time.time()
with (root/'audit-cycle6-or4.stdout').open('w') as out,(root/'audit-cycle6-or4.stderr').open('w') as err:
    p=subprocess.run([str(SOLVER),'-t','30',str(cnf)],stdout=out,stderr=err)
summary={'or_gates':4,'arbitrary_and_regions':True,'variables':c.n,'clauses':len(c.cs),'solver_code':p.returncode,'seconds':time.time()-start}
if p.returncode==10:
    truth={int(x) for line in (root/'audit-cycle6-or4.stdout').read_text().splitlines() if line.startswith('v ') for x in line[2:].split() if int(x)>0}
    def bits(ss):return sum(1<<i for i,s in enumerate(ss) if s in truth)
    summary['normalized_or_gates']=[[bits(a),bits(b)] for a,b in selectors]+[bits(output)]
(root/'audit-cycle6-or4-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary),flush=True)
