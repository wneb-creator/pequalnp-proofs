import json
from pathlib import Path
from free_and_sat import encode, cycle_graph


def assess(n, gates, final):
    cnf, meta = encode(n, cycle_graph(n), len(gates))
    assign = {cnf.one: True}
    canonical = []
    for gate, sides in zip(meta['selected'], gates):
        sides = sorted(sides, key=lambda xs: sum(1 << x for x in xs))
        canonical.append(sides)
        for side, selected in zip(gate, sides):
            for i, var in enumerate(side):
                assign[var] = i in selected
    for i, var in enumerate(meta['final']):
        assign[var] = i in final
    def truth(v):
        return assign[abs(v)] if v > 0 else not assign[-v]
    for v, op, args in cnf.ops:
        assign[v] = all(truth(x) for x in args) if op == 'and' else truth(args[0]) == truth(args[1])
    bad = [i for i, cs in enumerate(cnf.cs) if not any(truth(v) for v in cs)]
    assert not bad, bad[:5]
    edges = cycle_graph(n)
    for mask in range(1 << n):
        wires = [bool(mask >> i & 1) for i in range(n)]
        for a, b in canonical:
            wires.append(all(wires[i] for i in a) or all(wires[i] for i in b))
        actual = all(wires[i] for i in final)
        expected = any(mask >> u & 1 and mask >> v & 1 for u, v in edges)
        assert actual == expected, (mask, actual, expected)
    return {'n': n, 'or_count': len(gates), 'all_truth_rows': 1 << n,
            'all_cnf_clauses': len(cnf.cs), 'result': 'PASS'}


reports = [assess(4, [([0], [2]), ([1], [3])], [4, 5]),
    assess(8, [([7], [1]), ([1], [3]), ([3], [5]), ([5], [7]),
               ([0, 8], [2, 9]), ([12], [4, 10]), ([13], [6, 11])], [14])]
print(json.dumps(reports, indent=2))
Path('/tmp/oec/pequalnp-pilot-71/combinatorial-bound/control-summary.json').write_text(
    json.dumps(reports, indent=2) + '\n')
