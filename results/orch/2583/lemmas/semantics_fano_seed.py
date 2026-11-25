import json
from pathlib import Path
from search_read1_tracker import tracked, exact_read1

baseline = json.loads(Path('results/orch/2583/lemmas/search_fano_baseline.json').read_text())
lines = baseline['line_points']
edges = [tuple(e) for e in baseline['edges']]
gates = []


def gate(op,a,b):
    gates.append((op,a,b))
    return 13+len(gates)


def ors(xs):
    out = xs[0]
    for x in xs[1:]:
        out = gate(1,out,x)
    return out


# The first output replaces the mixed stars at point0 and line0.
leaf = ors([1,3])
lower = gate(0,7,leaf)
mixed = gate(1,0,lower)
point_neighbours = ors([7,11,13])
core = gate(0,mixed,point_neighbours)
outputs = [core]
for l in range(1,7):
    neighbours = [p for p in lines[l] if p != 0]
    outputs.append(gate(0,7+l,ors(neighbours)))
output = ors(outputs)
assert output == 14+len(gates)-1

inputs = [sum(1<<row for row in range(1<<14) if row>>i&1) for i in range(14)]
target = 0
for a,b in edges:
    target |= inputs[a]&inputs[b]


def signatures(circ):
    values = inputs.copy()
    for op,a,b in circ:
        values.append(values[a]|values[b] if op else values[a]&values[b])
    return values


values = signatures(gates)
assert values[-1] == target
linear, pairs = tracked(gates)
missing = [edge for k,edge in enumerate(edges) if not(pairs>>k&1)]
assert linear == 0 and missing == [(1,7),(3,7)]
assert all(exact_read1(gates,*e) == (e not in missing) for e in edges)


def erase(j,w):
    aliases = list(range(14))
    circ = []
    for k,(op,a,b) in enumerate(gates):
        if j == k:
            aliases.append(aliases[w])
            continue
        a,b = aliases[a],aliases[b]
        if a == b:
            aliases.append(a)
            continue
        aliases.append(14+len(circ))
        circ.append((op,a,b))
    out = aliases[output]
    if out < 14:
        return []
    live = set()

    def visit(w):
        if w < 14 or w in live:
            return
        live.add(w)
        _,a,b = circ[w-14]
        visit(a)
        visit(b)

    visit(out)
    mapping = {i:i for i in range(14)}
    result = []
    for k,(op,a,b) in enumerate(circ):
        if 14+k in live:
            mapping[14+k] = 14+len(result)
            result.append((op,mapping[a],mapping[b]))
    assert mapping[out] == 14+len(result)-1
    return result


improvements = []
for j in range(len(gates)):
    for w in range(14+j):
        candidate = erase(j,w)
        if candidate and signatures(candidate)[-1] == target:
            improvements.append({'gates':candidate,'size':len(candidate),'erase':[j,w],
                                 'read1_edges':tracked(candidate)[1].bit_count()})
data = {'status':'verified28-gate non-READ1 search seed; not a counterexample',
        'input_count':14,'gates':gates,'output_wire':output,'gate_count':len(gates),
        'missing_read1_edges':missing,'verified_truth_table_rows':1<<14,
        'verified_joint_read1_edges':21-len(missing),'single_gate_erasure_improvements':improvements}
Path('results/orch/2583/lemmas/semantics_fano_seed.json').write_text(json.dumps(data,indent=2)+'\n')
print(json.dumps(data,indent=2))
