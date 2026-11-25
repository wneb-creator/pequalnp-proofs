import hashlib
import json
from pathlib import Path

base=Path('/tmp/oec/pequalnp-pilot-96')
source=base/'counterexample-best.txt'
gates=[]
for line in source.read_text().splitlines():
    fields=line.split()
    if len(fields)==4 and fields[0].isdigit():
        index,op,a,b=map(int,fields)
        assert index==10+len(gates) and op in [0,1] and 0<=a<index and 0<=b<index
        gates.append((op,a,b))
assert len(gates)==19
edges=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
failures=[]
restored=[]
lost=[]
for mask in range(1024):
    inputs=[bool(mask&(1<<i)) for i in range(10)]
    wires=list(inputs)
    for op,a,b in gates:wires.append((wires[a] and wires[b]) if op==0 else (wires[a] or wires[b]))
    full=any(inputs[a] and inputs[b] for a,b in edges)
    deleted=any(inputs[a] and inputs[b] for a,b in edges if {a,b}!={7,9})
    triple=inputs[7] and inputs[8] and inputs[9]
    assert wires[28]==(deleted or triple)
    if full and not deleted:lost.append(mask)
    if wires[28] and not deleted:restored.append(mask)
    if wires[28]!=full:failures.append(mask)
report={'status':'PASS','rows':1024,'baseline_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'exact_identity':'Petersen with edge 7-9 deleted OR x7 AND x8 AND x9','edge_deletion_losses':lost,'triple_restored':restored,'full_target_failures':failures,'scope':'Truth table identity for a 19-gate zero-NOT approximate candidate; not a counterexample to the posted statement.'}
(base/'baseline-identity-audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
