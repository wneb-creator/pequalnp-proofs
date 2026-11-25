import itertools
import json
from pathlib import Path

from circuit_to_and_skeleton import extract
from generate_double_star_phases import antichain
from and_skeleton_minimal import verify_minimal_conditions
from and_skeleton_sat import validate_problem, verify


def build(data, point, line, first_pair):
    n = data['inputs']
    edges = {tuple(edge) for edge in data['edges']}
    points = sorted({u for u, _ in edges})
    gates = []

    def gate(op, a, b):
        gates.append([op, a, b])
        return n + len(gates) - 1

    def disjoin(wires):
        wires = list(wires)
        assert wires
        output = wires[0]
        for wire in wires[1:]:
            output = gate(1, output, wire)
        return output

    a = sorted(v for p, v in edges if p == point and v != line)
    b = sorted(p for p, v in edges if v == line and p != point)
    assert len(a) == 3 and 1 <= len(b) <= 2
    clauses = [disjoin([point] + b), disjoin([line] + a), gate(1, point, line)]
    first = gate(0, clauses[first_pair[0]], clauses[first_pair[1]])
    remaining = next(i for i in range(3) if i not in first_pair)
    roots = [gate(0, first, clauses[remaining])]
    for owner in points:
        if owner != point:
            neighbors = sorted(v for p, v in edges if p == owner and v != line)
            roots.append(gate(0, owner, disjoin(neighbors)))
    output = disjoin(roots)
    assert output == n + len(gates) - 1
    assert len(gates) == 31 and sum(op == 0 for op, _, _ in gates) == 7
    dnfs = [[1 << v] for v in range(n)]
    for i, (op, u, v) in enumerate(gates):
        assert 0 <= u < n + i and 0 <= v < n + i
        dnfs.append(antichain(dnfs[u] + dnfs[v] if op else
                              [left | right for left in dnfs[u] for right in dnfs[v]]))
    assert set(dnfs[output]) == {(1 << u) | (1 << v) for u, v in edges}
    skeleton = extract(gates, n, output)
    verify_minimal_conditions(data, skeleton, True, True)
    dirty = [term for term in dnfs[first]
             if term.bit_count() <= 2 and not any(term >> u & 1 and term >> v & 1 for u, v in edges)]
    assert dirty
    return {'point': point, 'line': line, 'first_clause_pair': list(first_pair),
            'gates': gates, 'output': output, 'gate_count': 31, 'and_count': 7,
            'dirty_input': dirty[0], 'exact_DNF_verified': True,
            'positive_live_ANDs': True, 'negative_child_incomparability': True,
            'target28_met': False, 'skeleton': skeleton}


def main():
    base = Path(__file__).parent
    data = json.loads((base / 'and_skeleton_six_data.json').read_text())
    validate_problem(data)
    bank = [build(data, p, line, pair) for p, line in data['edges']
            for pair in itertools.combinations(range(3), 2)]
    assert len(bank) == 72
    (base / 'six_double_star_exact31_phases.json').write_text(json.dumps(bank))
    phase = bank[0]['skeleton']
    phase.update({'edges': data['edges'], 'input_original': data['input_original'], 'and_count': 7,
                  'source_gate_count': 31, 'exact_target_DNF_verified': True,
                  'dirty_input': bank[0]['dirty_input'], 'total_gate_bound_established': False})
    assert verify(data, phase, phase['dirty_input'], full=True)
    (base / 'and_skeleton_six_exact_dirty7_phase.json').write_text(json.dumps(phase))
    print('PASS all72 exact31/7AND six-owner double-star phases; each output DNF is exactly24 target edges')
    print('Selected phase also checked on all2^17 inputs; all ANDs positive-live and negative-child-incomparable')


if __name__ == '__main__':
    main()
