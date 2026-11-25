import json
import pathlib
import sys

packet_path, case_index, circuit_path, report_path = sys.argv[1:]
case = json.loads(pathlib.Path(packet_path).read_text())[int(case_index)]
obj = json.loads(pathlib.Path(circuit_path).read_text())
gates = obj['gates'] if isinstance(obj, dict) else obj
n, raw = case['inputs'], case['raw_inputs']
output = obj.get('output', n+len(gates)-1) if isinstance(obj, dict) else n+len(gates)-1
values = [int(('1'*(1 << i)+'0'*(1 << i))*(1 << (raw-i-1)), 2) for i in range(raw)]
monomials = [{1 << i} for i in range(raw)]
for feature in case['features']:
    value = 0
    for i in feature['raw_indices']:
        value |= values[i]
    values.append(value)
    monomials.append({1 << i for i in feature['raw_indices']})
expected = 0
edge_masks = {(1 << a) | (1 << b) for a, b in case['edges']}
for a, b in case['edges']:
    expected |= values[a] & values[b]
for i, (op, a, b) in enumerate(gates):
    assert op in (0, 1) and 0 <= a < n+i and 0 <= b < n+i
    values.append(values[a] | values[b] if op else values[a] & values[b])
    candidates = monomials[a] | monomials[b] if op else {u | v for u in monomials[a] for v in monomials[b]}
    prime = []
    for term in sorted(candidates, key=lambda v: (v.bit_count(), v)):
        if not any(prior & term == prior for prior in prime):
            prime.append(term)
    monomials.append(set(prime))
actual = values[output]
wrong = misses = one_owner_wrong = 0
point_mask = (1 << len(case['group']))-1
for x, label in case['raw_tests']:
    found = actual >> x & 1
    wrong += bool(found and not label)
    one_owner_wrong += bool(found and not label and (x & point_mask).bit_count() == 1)
    misses += bool(label and not found)
used = {output}
for i in range(len(gates)-1, -1, -1):
    if n+i in used:
        used.update(gates[i][1:])
report = dict(case=case['name'], raw_assignments=1 << raw, gates=len(gates),
              active_gates=sum(n+i in used for i in range(len(gates))),
              active_ands=sum(n+i in used and op == 0 and a != b for i, (op, a, b) in enumerate(gates)),
              omitted_raw_inputs=[i for i in range(raw) if i not in used],
              false_positives=(actual & ~expected).bit_count(),
              false_negatives=(expected & ~actual).bit_count(),
              boundary_false=wrong, boundary_misses=misses,
              one_owner_boundary_errors=one_owner_wrong,
              maximum_extra_degree=max((term.bit_count() for term in monomials[output]-edge_masks), default=0),
              minimum_extra_point_count=min(((term & point_mask).bit_count() for term in monomials[output]-edge_masks), default=None),
              extra_monomials=[[i for i in range(raw) if term >> i & 1]
                               for term in sorted(monomials[output]-edge_masks)])
pathlib.Path(report_path).write_text(json.dumps(report, indent=2)+'\n')
print(json.dumps(report))
