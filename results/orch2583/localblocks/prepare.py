import itertools
import json
from pathlib import Path

scratch = Path('/tmp/oec/pequalnp-pilot-103/localblocks')
archive = Path('/workspace/pequalnp-proofs/results/orch2583/localblocks')
scratch.mkdir(parents=True, exist_ok=True)
source = json.loads(Path('/tmp/oec/pequalnp-pilot-103/orch2583/fano-data.json').read_text())
edges = [tuple(e) for e in source['edges']]
lines = [frozenset(p for p, w in edges if w == 7+l) for l in range(7)]
line_index = {s:i for i,s in enumerate(lines)}
autos = []
for perm in itertools.permutations(range(7)):
    images = [frozenset(perm[p] for p in line) for line in lines]
    if all(s in line_index for s in images):
        autos.append(tuple(perm) + tuple(7+line_index[s] for s in images))
assert len(autos) == 168

def canonical(local_edges, mapping, points):
    inverse = {v:i for i,v in enumerate(mapping)}
    n = len(mapping)
    gates = []
    outputs = []
    for p in points:
        neighbors = [inverse[l] for a,l in local_edges if a == p]
        assert len(neighbors) == 3
        a,b,c = neighbors
        gates.append([1,a,b]); first = n+len(gates)-1
        gates.append([1,first,c]); both = n+len(gates)-1
        gates.append([0,inverse[p],both]); outputs.append(n+len(gates)-1)
    acc = outputs[0]
    for out in outputs[1:]:
        gates.append([1,acc,out]); acc = n+len(gates)-1
    assert acc == n+len(gates)-1
    return gates

def evaluate(gates, n, mask):
    wires = [bool(mask & (1<<j)) for j in range(n)]
    for op,a,b in gates:
        wires.append((wires[a] or wires[b]) if op else (wires[a] and wires[b]))
    return wires[-1]

cases = []
for k in [3,4]:
    remaining = set(itertools.combinations(range(7), k))
    while remaining:
        selected = min(remaining)
        orbit = {tuple(sorted(perm[p] for p in selected)) for perm in autos}
        remaining -= orbit
        local_edges = [(p,l) for p,l in edges if p in selected]
        mapping = sorted({v for e in local_edges for v in e})
        inverse = {v:i for i,v in enumerate(mapping)}
        E = [(inverse[p],inverse[l]) for p,l in local_edges]
        n = len(mapping)
        positive = sorted({(1<<p)|(1<<l) for p,l in E})
        def target(mask):
            return any(mask & (1<<p) and mask & (1<<l) for p,l in E)
        negative = [mask for mask in range(1<<n) if not target(mask)
                    and all(target(mask | (1<<v)) for v in range(n) if not mask & (1<<v))]
        baseline = canonical(local_edges, mapping, selected)
        assert len(baseline) == 4*k-1
        assert all(evaluate(baseline,n,mask) == bool(target(mask)) for mask in range(1<<n))
        collinear = any(line <= set(selected) for line in lines)
        tag = f'k{k}-'+('line' if collinear else 'noline')
        stabilizer = [perm for perm in autos if {perm[p] for p in selected} == set(selected)]
        local_autos = [tuple(inverse[perm[v]] for v in mapping) for perm in stabilizer]
        unseen = set(itertools.combinations(range(n),2)); pair_orbits = []
        while unseen:
            pair = min(unseen)
            po = {tuple(sorted((perm[pair[0]],perm[pair[1]]))) for perm in local_autos}
            unseen -= po
            pair_orbits.append({'representative':list(pair),'size':len(po)})
        data = {'tag':tag,'inputs':n,'selected_points':list(selected),'orbit_size':len(orbit),
                'original_wires':mapping,'edges':E,'positive_rows':positive,
                'negative_rows':negative,'baseline':baseline,'target_gates':4*k-2,
                'stabilizer_size':len(stabilizer),'first_pair_orbits':pair_orbits}
        for directory in [scratch,archive]:
            (directory/f'{tag}-data.json').write_text(json.dumps(data,indent=2)+'\n')
            (directory/f'{tag}-baseline.json').write_text(json.dumps(baseline)+'\n')
        cases.append(data)
        print(json.dumps({key:data[key] for key in ['tag','inputs','selected_points','orbit_size','target_gates','stabilizer_size','first_pair_orbits']}), flush=True)
for directory in [scratch,archive]:
    (directory/'cases.json').write_text(json.dumps(cases,indent=2)+'\n')
