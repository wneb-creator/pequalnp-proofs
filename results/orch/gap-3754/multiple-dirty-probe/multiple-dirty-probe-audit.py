from itertools import product
import json


def audit(m):
    n = 2*m
    inputs = [sum(1 << x for x in range(1 << n) if (x >> v) & 1) for v in range(n)]
    values = list(inputs)
    gates = []
    subsets = {(v,): v for v in range(n)}
    def gate(op, a, b):
        gates.append((op, a, b))
        values.append(values[a] | values[b] if op == 'or' else values[a] & values[b])
        return len(values)-1
    def disj(vs):
        if vs not in subsets:
            subsets[vs] = gate('or', disj(vs[:-1]), vs[-1])
        return subsets[vs]
    clauses = [disj(tuple(2*i+b for i,b in enumerate(bits))) for bits in product((0,1), repeat=m)]
    def conj(ws):
        if len(ws) == 1:
            return ws[0]
        half = len(ws)//2
        return gate('and', conj(ws[:half]), conj(ws[half:]))
    output = conj(clauses)
    truth = 0
    edge_masks = []
    for i in range(m):
        truth |= inputs[2*i] & inputs[2*i+1]
        edge_masks.append((1 << (2*i)) | (1 << (2*i+1)))
    assert values[output] == truth
    below = [v & ~truth == 0 for v in values]
    singletons = [tuple(v for v in range(n) if (f >> (1 << v)) & 1) for f in values]
    assert all(not below[a] and not below[b] for op,a,b in gates if op == 'and')
    assert all(below[n+k] or (not below[a] and not below[b]) for k,(op,a,b) in enumerate(gates) if op == 'or')
    assert len(values) == len(set(values))
    live = {output}
    for k in reversed(range(len(gates))):
        if n+k in live:
            live.update(gates[k][1:])
    assert all(n+k in live for k in range(len(gates)))
    critical = []
    for cut in range(len(gates)):
        witnesses = []
        for edge in edge_masks:
            bits = [bool(edge & (1 << v)) for v in range(n)]
            for k,(op,a,b) in enumerate(gates):
                bits.append(False if k == cut else (bits[a] or bits[b] if op == 'or' else bits[a] and bits[b]))
            if not bits[output]:
                witnesses.append(edge)
        assert witnesses
        critical.append(witnesses)
    op,a,b = gates[output-n]
    assert op == 'and'
    assert singletons[a] == (0,) and singletons[b] == (1,)
    assert values[a] != sum(1 << x for x in range(1 << n) if x & 1)
    assert values[b] != sum(1 << x for x in range(1 << n) if x & 2)
    dirty_and = [k for k,(op,_,_) in enumerate(gates) if op == 'and' and not below[n+k]]
    assert len(dirty_and) == 2**m-2
    assert len(gates) == 3*(2**m)-5
    return dict(matching_edges=m, inputs=n, gates=len(gates), clean_upper=2*m-1,
                dirty_ands=len(dirty_and), output_operands_singletons=[singletons[a],singletons[b]],
                all_gates_edge_critical=True, lift_fixed=True, no_and_below_operand=True,
                all_wires_semantically_distinct=True, full_truth_table_checked=True,
                posted_counterexample=False, circuit=gates, output=output)

if __name__ == '__main__':
    answers = [audit(m) for m in range(2,6)]
    print(json.dumps(answers, indent=2))
