#!/usr/bin/env python3
"""Expand a small base witness with observed OR helpers into a symbolic Lean certificate."""
import argparse
import json
from pathlib import Path

from make_symbolic_witness import symbolic_render


def amplify(data):
    graph = data['graph']
    witness = data['witness']
    n0 = graph['n']
    assert type(n0) is int and 0 < n0 <= 16
    base_gates = witness['gates']
    output0 = witness.get('output', n0 + len(base_gates) - 1)
    helpers = witness['observed_helpers']
    assert helpers and all(h['support'] for h in helpers)
    assert len({tuple(sorted(h['support'])) for h in helpers}) == len(helpers)
    for j, (op, a, b) in enumerate(base_gates):
        assert op in ('and', 'or') and 0 <= a < n0+j and 0 <= b < n0+j
    assert 0 <= output0 < n0 + len(base_gates)

    # This finite crosscheck is only over the base inputs. Lean independently
    # checks the same base identity and the complete symbolic extension.
    rows = 1 << n0
    inputs = [sum(1 << a for a in range(rows) if (a >> i) & 1) for i in range(n0)]
    wire_values = inputs[:]
    for op, a, b in base_gates:
        wire_values.append(wire_values[a] & wire_values[b] if op == 'and'
                           else wire_values[a] | wire_values[b])
    graph_value = 0
    for a, b in graph['edges']:
        assert 0 <= a < n0 and 0 <= b < n0 and a != b
        graph_value |= inputs[a] & inputs[b]
    assert wire_values[output0] == graph_value
    for helper in helpers:
        support = helper['support']
        assert len(support) == len(set(support)) and all(0 <= v < n0 for v in support)
        assert 0 <= helper['wire'] < len(wire_values)
        expected = 0
        for v in support:
            expected |= inputs[v]
        assert wire_values[helper['wire']] == expected

    n = n0 + 2*len(helpers)
    shift = lambda w: w if w < n0 else w + n - n0
    gates = [[op, shift(a), shift(b)] for op, a, b in base_gates]
    output = shift(output0)
    edges = [list(e) for e in graph['edges']]
    cuts = [{'wire': output, 'edges': graph['edges']}]
    for j, helper in enumerate(helpers):
        center, private = n0 + 2*j, n0 + 2*j + 1
        helper_wire = shift(helper['wire'])
        # Helper proofs are retained as separate cut facts when their circuit
        # uses more than literal OR gates, which algebraic normalization would
        # otherwise have to discover.
        cone = {helper['wire']}
        pending = [helper['wire']]
        literal_only = True
        while pending:
            w = pending.pop()
            if w < n0:
                continue
            op, a, b = base_gates[w-n0]
            literal_only &= op == 'or'
            for v in (a, b):
                if v not in cone:
                    cone.add(v)
                    pending.append(v)
        if not literal_only:
            cuts.append({'wire': helper_wire, 'or_inputs': helper['support']})
        gates.append(['or', helper_wire, private])
        union = n + len(gates) - 1
        gates.append(['and', center, union])
        star = n + len(gates) - 1
        gates.append(['or', output, star])
        output = n + len(gates) - 1
        edges.extend([[center, v] for v in helper['support']] + [[center, private]])

    full = {'n': n, 'edges': edges, 'size': len(gates), 'gates': gates,
            'output': output, 'base_rows_checked': rows,
            'verification': 'Base truth table and exact OR helpers checked; extension certified symbolically in Lean'}
    return full, {'cuts': cuts}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('base_witness_json', type=Path)
    parser.add_argument('output_prefix', type=Path)
    args = parser.parse_args()
    full, plan = amplify(json.loads(args.base_witness_json.read_text()))
    prefix = str(args.output_prefix)
    Path(prefix + '.witness.json').write_text(json.dumps(full, indent=2))
    Path(prefix + '.cuts.json').write_text(json.dumps(plan, indent=2))
    Path(prefix + '.lean').write_text(symbolic_render(full, plan))
    print(json.dumps({'prefix': prefix, 'n': full['n'], 'gates': full['size'],
                      'edges': len(full['edges']), 'cuts': len(plan['cuts'])}, sort_keys=True))


if __name__ == '__main__':
    main()
