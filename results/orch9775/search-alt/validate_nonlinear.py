import ast
import json
import re
import sys
from pathlib import Path

log, prefix = map(Path,sys.argv[1:3])
elastic = bool(int(sys.argv[3]))
data = json.loads(Path('results/orch9775/search-alt/data.json').read_text())
inputs = [sum(((m>>v)&1)<<m for m in range(16384)) for v in range(14)]
target = 0
for a,b in data['edges']:
    target |= inputs[a]&inputs[b]

def evaluate(gates, output):
    wires=inputs.copy()
    for op,a,b in gates:
        assert op in (0,1) and 0<=a<len(wires) and 0<=b<len(wires)
        wires.append(wires[a]&wires[b] if op==0 else wires[a]|wires[b])
    assert 0<=output<len(wires)
    return wires[output]

def used(gates):
    live={13+len(gates)}
    for i in range(len(gates)-1,-1,-1):
        if 14+i in live:
            live.update(gates[i][1:])
    return sum(14+i in live for i in range(len(gates)))

def deficiency(gates):
    singles=[{v} for v in range(14)]
    pairs=[set() for _ in range(14)]
    for op,a,b in gates:
        if op:
            singles.append(singles[a]|singles[b]); pairs.append(pairs[a]|pairs[b])
        else:
            singles.append(set())
            pairs.append({tuple(sorted((u,v))) for u in singles[a] for v in singles[b] if u!=v})
    missing=[edge for edge in data['edges'] if tuple(edge) not in pairs[-1]]
    return missing

reports=[]
for line in log.read_text().splitlines():
    if line.startswith('best '):
        m=re.fullmatch(r'best (\d+) trial (\d+) gates (\[.*\])',line)
        assert m
        gates=ast.literal_eval(m[3]);assert len(gates)==(29 if elastic else 24)
        actual=evaluate(gates,13+len(gates));fp=(actual&~target).bit_count();fn=(target&~actual).bit_count()
        s_fp=sum(bool((actual>>x)&1) and not bool((target>>x)&1) for x in data['rows'])
        s_fn=sum(bool((target>>x)&1) and not bool((actual>>x)&1) for x in data['rows'])
        score=(8192*(s_fp+s_fn)+32*used(gates)-len(deficiency(gates))) if elastic else (4*s_fp+s_fn)
        assert score==int(m[1])
        if elastic:assert fp==fn==0
        report=dict(trial=int(m[2]),score=score,sample_false_positive=s_fp,sample_false_negative=s_fn,full_false_positive=fp,full_false_negative=fn,used_gates=used(gates),squarefree_missing_edges=deficiency(gates))
        reports.append(report)
        prefix.with_name(prefix.name+'-best.json').write_text(json.dumps(dict(inputs=14,output=13+len(gates),gates=gates,validation=report),indent=2)+'\n')
    elif line.startswith('nonlinear '):
        m=re.fullmatch(r'nonlinear cost (\d+) missing (\d+) trial (\d+) gates (\[.*\])',line)
        assert m
        gates=ast.literal_eval(m[4]); assert len(gates)==29
        assert evaluate(gates,42)==target
        assert used(gates)==int(m[1])
        missing=deficiency(gates); assert len(missing)==int(m[2])
        candidate=dict(inputs=14,output=42,gates=gates,full_assignments_checked=16384,used_gates=used(gates),squarefree_missing_edges=missing,trial=int(m[3]))
        prefix.with_name(prefix.name+'-nonlinear-'+m[1]+'-'+m[2]+'.json').write_text(json.dumps(candidate,indent=2)+'\n')
    elif line.startswith('WITNESS '):
        candidate=json.loads(line[8:]);assert len(candidate['gates'])<=24
        assert evaluate(candidate['gates'],candidate['output'])==target
        candidate['full_assignments_checked']=16384
        prefix.with_name(prefix.name+'-witness.json').write_text(json.dumps(candidate,indent=2)+'\n')
prefix.with_name(prefix.name+'-validation.json').write_text(json.dumps(reports,indent=2)+'\n')
print(json.dumps(reports))
