import json
from pathlib import Path

root=Path('/tmp/oec/pequalnp-pilot-73/fresh-count')
deltas={0,1,3,9}
def incident(p,l): return (p-l)%13 in deltas
gates=[]
def gate(op,a,b):
    gates.append([op,a,b])
    return 25+len(gates)
def sum_wires(wires):
    out=wires[0]
    for w in wires[1:]: out=gate('or',out,w)
    return out
stars=[]
for l in range(13):
    points=[p for p in range(13) if incident(p,l)]
    stars.append(gate('and',sum_wires(points),13+l))
out=sum_wires(stars)

def evaluate(point,lines):
    values=[p==point for p in range(13)]+[l in lines for l in range(13)]
    for op,a,b in gates:
        values.append((values[a] and values[b]) if op=='and' else (values[a] or values[b]))
    return values

charges=[[] for _ in gates]
rows=[]
for p in range(13):
    zero=evaluate(p,set())
    singles=[evaluate(p,{l}) for l in range(13)]
    support=[{l for l in range(13) if singles[l][w]} for w in range(26+len(gates))]
    row=[]
    for k,(op,a,b) in enumerate(gates):
        if op=='or' and not zero[26+k] and not support[a]<=support[b] and not support[b]<=support[a]:
            charges[k].append(p)
            row.append(k)
    rows.append(row)
    assert len(row)==3
    assert support[out]=={l for l in range(13) if incident(p,l)}
    for mask in range(8192):
        lines={l for l in range(13) if mask>>l&1}
        assert evaluate(p,lines)[out] == any(incident(p,l) for l in lines)
nonempty=[(k,c) for k,c in enumerate(charges) if c]
answer={
    'status':'computational illustration only, not a Lean certificate or a gap witness',
    'purpose':'A shared cofactor OR charge cannot be repaid only by selector AND gates.',
    'gates':gates,
    'output':out,
    'gate_count':len(gates),
    'and_count':sum(op=='and' for op,_,_ in gates),
    'or_count':sum(op=='or' for op,_,_ in gates),
    'point_cofactor_charges':rows,
    'charged_gate_users':nonempty,
    'total_charges':sum(map(len,charges)),
    'distinct_charged_or_gates':len(nonempty),
    'excess_shared_charges':sum(len(c)-1 for _,c in nonempty),
    'verified_assignments':13*8192,
}
(root/'cofactor-charge-example.json').write_text(json.dumps(answer,indent=2)+'\n')
print(json.dumps({k:v for k,v in answer.items() if k not in {'gates','point_cofactor_charges','charged_gate_users'}},indent=2))
