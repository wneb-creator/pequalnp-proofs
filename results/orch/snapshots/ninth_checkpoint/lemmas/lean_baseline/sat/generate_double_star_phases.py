import itertools
import json
from pathlib import Path

from circuit_to_and_skeleton import extract
from and_skeleton_minimal import verify_minimal_conditions
from and_skeleton_sat import validate_problem


def antichain(terms):
    answer = []
    for term in sorted(set(terms), key=lambda x: (x.bit_count(), x)):
        if not any(old & term == old for old in answer):
            answer.append(term)
    return answer


def build(data, point, line, first_pair):
    n = data['inputs']
    edges = {tuple(edge) for edge in data['edges']}
    gates = []

    def gate(op, a, b):
        gates.append([op, a, b])
        return n + len(gates) - 1

    def disjoin(wires):
        wires = list(wires)
        assert wires
        answer = wires[0]
        for wire in wires[1:]:
            answer = gate(1, answer, wire)
        return answer

    a = sorted(v for p, v in edges if p == point and v != line)
    b = sorted(p for p, v in edges if v == line and p != point)
    assert len(a) == len(b) == 3
    clauses = [disjoin([point] + b), disjoin([line] + a), gate(1, point, line)]
    first = gate(0, clauses[first_pair[0]], clauses[first_pair[1]])
    remaining = next(i for i in range(3) if i not in first_pair)
    roots = [gate(0, first, clauses[remaining])]
    for owner in range(13):
        if owner != point:
            neighbors = sorted(v for p, v in edges if p == owner and v != line)
            roots.append(gate(0, owner, disjoin(neighbors)))
    output = disjoin(roots)
    assert output == n + len(gates) - 1
    assert len(gates) == 66 and sum(op == 0 for op, _, _ in gates) == 14
    dnfs = [[1 << v] for v in range(n)]
    for i, (op, u, v) in enumerate(gates):
        assert 0 <= u < n + i and 0 <= v < n + i
        dnfs.append(antichain(dnfs[u] + dnfs[v] if op else
                              [left | right for left in dnfs[u] for right in dnfs[v]]))
    assert set(dnfs[output]) == {(1 << u) | (1 << v) for u, v in edges}
    skeleton = extract(gates, n, output)
    verify_minimal_conditions(data, skeleton, True, True)
    # Every first intermediate AND has an independent input making it true.
    dirty = [term for term in dnfs[first]
             if term.bit_count() <= 2 and not any(term >> u & 1 and term >> v & 1 for u, v in edges)]
    assert dirty
    return {'point': point, 'line': line, 'first_clause_pair': list(first_pair),
            'gates': gates, 'output': output, 'gate_count': len(gates), 'and_count': 14,
            'dirty_input': dirty[0], 'exact_DNF_verified': True,
            'positive_live_ANDs': True, 'negative_child_incomparability': True,
            'target63_met': False, 'skeleton': skeleton}


def main():
    base = Path(__file__).parent
    data = json.loads((base / 'and_skeleton_full_data.json').read_text())
    validate_problem(data)
    bank = [build(data, p, line, pair) for p, line in data['edges']
            for pair in itertools.combinations(range(3), 2)]
    assert len(bank) == 156
    (base / 'full_double_star_exact66_phases.json').write_text(json.dumps(bank))
    phase = bank[0]['skeleton']
    phase.update({'edges': data['edges'], 'input_original': list(range(26)), 'and_count': 14,
                  'source_gate_count': 66, 'exact_target_DNF_verified': True,
                  'dirty_input': bank[0]['dirty_input'], 'total_gate_bound_established': False})
    (base / 'and_skeleton_full_exact_dirty14_phase.json').write_text(json.dumps(phase))
    print('PASS all156 exact66/14AND double-star phases; every output DNF is exactly the52 target edges')
    print('All ANDs positive-live and negative-child-incomparable; no63-gate witness claimed')


if __name__ == '__main__':
    main()
