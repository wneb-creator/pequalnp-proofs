import json
import pathlib
import sys

packet_path, case_index, candidate_path, output_path = sys.argv[1:]
case = json.loads(pathlib.Path(packet_path).read_text())[int(case_index)]
gadget = json.loads(pathlib.Path(candidate_path).read_text())
n = case['inputs']
gates = [g.copy() for g in case['outside_gates']]
mapping = {i: original for i, original in enumerate(case['input_original'])}
for i, feature in enumerate(case['features']):
    mapping[case['raw_inputs']+i] = feature['outside_wire']
for i, (op, a, b) in enumerate(gadget):
    assert op in (0, 1) and 0 <= a < n+i and 0 <= b < n+i
    gates.append([op, mapping[a], mapping[b]])
    mapping[n+i] = 25+len(gates)
gates.append([1, case['outside_output'], mapping[n+len(gadget)-1]])
assert len(gates) <= 63
monomials = [{1 << i} for i in range(26)]
for i, (op, a, b) in enumerate(gates):
    assert op in (0, 1) and 0 <= a < 26+i and 0 <= b < 26+i
    candidates = monomials[a] | monomials[b] if op else {u | v for u in monomials[a] for v in monomials[b]}
    prime = []
    for term in sorted(candidates, key=lambda x: (x.bit_count(), x)):
        if not any(previous & term == previous for previous in prime):
            prime.append(term)
    monomials.append(set(prime))
directory = pathlib.Path(__file__).resolve().parent
full = json.loads((directory/'full-case.json').read_text())
geometry = json.loads((directory/'geometry.json').read_text())
expected = {(1 << a) | (1 << b) for a, b in geometry['edges']}
assert expected <= monomials[-1]
errors = misses = 0
for x, label in full['tests']:
    actual = any(term & x == term for term in monomials[-1])
    errors += bool(actual and not label)
    misses += bool(label and not actual)
report = dict(status='approximate only', case=case['name'], gates=len(gates),
              ands=sum(op == 0 for op, _, _ in gates), boundary_errors=errors,
              positive_misses=misses, extra_monomials=[[i for i in range(26) if term >> i & 1]
                                                       for term in sorted(monomials[-1]-expected)])
pathlib.Path(output_path).write_text(json.dumps(gates)+'\n')
pathlib.Path(output_path).with_suffix('.validation.json').write_text(json.dumps(report, indent=2)+'\n')
print(json.dumps(report))
