import hashlib
import importlib.util
import json
from pathlib import Path

root = Path('/tmp/oec/pequalnp-pilot-121/andcount2056')
spec = importlib.util.spec_from_file_location('base', root / 'andcount2056.py')
base = importlib.util.module_from_spec(spec)
spec.loader.exec_module(base)
source = root / 'exact66-directed-cleanup.json'
c = json.loads(source.read_text())
edges, rows = base.geometry()
gates = c['gates']
out = c['output']
pm = (1 << len(edges)) - 1
nm = ((1 << len(rows)) - 1) ^ pm
v = [sum(((r >> i) & 1) << k for k, r in enumerate(rows)) for i in range(26)]
singletons = [1 << i for i in range(26)]
sv = [sum(((r >> i) & 1) << k for k, r in enumerate(singletons)) for i in range(26)]
readers = [[] for _ in range(26 + len(gates))]
for j, (op, a, b) in enumerate(gates):
    assert op in (0, 1) and 0 <= a < 26+j and 0 <= b < 26+j
    v.append((v[a] | v[b]) if op else (v[a] & v[b]))
    sv.append((sv[a] | sv[b]) if op else (sv[a] & sv[b]))
    for x in set((a, b)):
        readers[x].append(j)
assert v[out] == pm
clean = [(x & nm) == 0 for x in v]
missing = []
for ei, (a, b) in enumerate(edges):
    proof = [int(i == a) + 2 * int(i == b) for i in range(26)]
    for op, x, y in gates:
        u, w = proof[x], proof[y]
        proof.append((u | w) if op else (4 if ((u & 1 and w & 2) or (u & 2 and w & 1)) else 0))
    if not proof[out] & 4:
        missing.append({'edge_index': ei, 'edge': [a, b]})

def next_ands(wire):
    todo = [wire]
    seen = set()
    ans = set()
    while todo:
        x = todo.pop()
        if x in seen:
            continue
        seen.add(x)
        for j in readers[x]:
            if gates[j][0] == 0:
                ans.add(j)
            else:
                todo.append(26+j)
    return sorted(ans)

dirty_ands = []
clean_violations = []
dominance = []
for j, (op, a, b) in enumerate(gates):
    wire = 26+j
    if not op and not clean[wire]:
        dirty_ands.append({'gate': j, 'wire': wire, 'operands': [a,b],
                           'positive_count': (v[wire]&pm).bit_count(),
                           'negative_count': (v[wire]&nm).bit_count(),
                           'singleton_inputs': [k for k in range(26) if sv[wire] >> k & 1],
                           'direct_readers': readers[wire], 'next_AND_gates': next_ands(wire)})
    if not op and (clean[a] or clean[b]):
        clean_violations.append({'kind': 'AND_clean_operand', 'gate': j})
    if op and clean[a] != clean[b]:
        clean_violations.append({'kind': 'mixed_OR', 'gate': j})
    if clean[wire] and len(readers[wire]) > 1:
        clean_violations.append({'kind': 'clean_fanout', 'gate': j, 'readers': readers[wire]})
    for x in range(wire):
        if (v[wire]&pm&~v[x]) == 0 and (v[x]&nm&~v[wire]) == 0:
            dominance.append({'gate': j, 'replacement_wire': x})
            break
live = set()
todo = [out]
while todo:
    x = todo.pop()
    if x < 26 or x in live:
        continue
    live.add(x)
    todo.extend(gates[x-26][1:])
report = {'source': str(source), 'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
          'gate_count': len(gates), 'AND_count': sum(op == 0 for op,_,_ in gates),
          'OR_count': sum(op == 1 for op,_,_ in gates), 'boundary_rows': len(rows),
          'boundary_mismatches': 0, 'live_gate_count': len(live),
          'missing_joint_Read1_edges': missing, 'dirty_ANDs': dirty_ands,
          'clean_AND_gate_indices': [j for j,(op,_,_) in enumerate(gates) if op == 0 and clean[26+j]],
          'dirty_OR_gate_indices': [j for j,(op,_,_) in enumerate(gates) if op == 1 and not clean[26+j]],
          'clean_rule_violations': clean_violations, 'earlier_wire_dominance': dominance,
          'zero_positive_gate_indices': [j for j in range(len(gates)) if v[26+j]&pm == 0]}
(root / 'exact66-structural-analysis.json').write_text(json.dumps(report, indent=2)+'\n')
print(json.dumps(report, indent=2))
