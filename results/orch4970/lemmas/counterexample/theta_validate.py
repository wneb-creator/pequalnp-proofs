from itertools import combinations

EDGES = [(0,5),(0,6),(0,7),(1,5),(1,4),(2,6),(2,4),(3,7),(3,4)]


def validate(circuit, output=None):
    values = [sum(1 << r for r in range(256) if r >> i & 1) for i in range(8)]
    reach = [{i} for i in range(8)]
    mixed = []
    backward = True
    for j, (op,a,b) in enumerate(circuit):
        backward &= 0 <= a < 8+j and 0 <= b < 8+j
        va = values[a] if 0 <= a < len(values) else 0
        vb = values[b] if 0 <= b < len(values) else 0
        values.append(va & vb if op == 'and' else va | vb)
        ra = reach[a] if 0 <= a < len(reach) else set()
        rb = reach[b] if 0 <= b < len(reach) else set()
        newreach = set() if op == 'and' else ra | rb
        reach.append(newreach)
        if op == 'or' and any(i < 4 for i in newreach) and any(i >= 4 for i in newreach):
            mixed.append(j)
    witnesses = {}
    uncovered = []
    for a,b in EDGES:
        candidates = []
        for center, leaf in [(a,b),(b,a)]:
            neighbors = [v if u == center else u for u,v in EDGES if center in (u,v)]
            for k in range(2,len(neighbors)+1):
                for subset in combinations(neighbors,k):
                    if leaf not in subset:
                        continue
                    function = 0
                    for v in subset:
                        function |= values[v]
                    for j,(op,_,_) in enumerate(circuit):
                        if op == 'or' and values[8+j] == function:
                            candidates.append({'center':center,'leaves':subset,'gate':j})
        witnesses[str((a,b))] = candidates
        if not candidates:
            uncovered.append((a,b))
    target = 0
    for a,b in EDGES:
        target |= values[a] & values[b]
    output = len(values)-1 if output is None else output
    output_valid = 0 <= output < len(values)
    output_value = values[output] if output_valid else 0
    errors = [r for r in range(256) if (output_value^target) >> r & 1]
    return {'gates':len(circuit),'reads_back':backward,'all_ops_ao':all(op in ['and','or'] for op,_,_ in circuit),
            'full_truth_errors':errors,'two_colour_gates':mixed,'uncovered_edges':uncovered,
            'star_witnesses':witnesses,
            'output':output, 'output_valid':output_valid,
            'satisfies_4970_hypotheses':backward and output_valid and all(op in ['and','or'] for op,_,_ in circuit) and not errors and not mixed and not uncovered}
