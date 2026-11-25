"""Independent exhaustive Fano data and circuit controls; imports no search code."""
import hashlib
import json
from pathlib import Path

DATA = Path('/tmp/oec/pequalnp-pilot-99/gap2583/counterexample')


def main():
    files = ['fano.json', 'upper27.json', 'fano27-control.circuit.json',
             'fano27-visible-control.circuit.json']
    before = {name: hashlib.sha256((DATA / name).read_bytes()).hexdigest() for name in files}
    data = json.loads((DATA / 'fano.json').read_text())
    lines = [set((l + d) % 7 for d in (0, 1, 3)) for l in range(7)]
    assert [set(row) for row in data['lines']] == lines
    assert all(len(row) == 3 for row in lines)
    assert all(sum(p in row and q in row for row in lines) == 1
               for p in range(7) for q in range(7) if p != q)
    edges = {(p, l + 7) for l, row in enumerate(lines) for p in row}
    assert set(map(tuple, data['edges'])) == edges and len(edges) == 21
    edge_masks = {2 ** p + 2 ** l for p, l in edges}
    truth = [any(mask & edge == edge for edge in edge_masks) for mask in range(2 ** 14)]
    independent = {mask for mask, value in enumerate(truth) if not value}
    maximal = {mask for mask in independent
               if all(truth[mask | (1 << i)] for i in range(14) if not (mask >> i) & 1)}
    assert len(independent) == 458 and len(maximal) == 37
    assert set(data['maximal']) == maximal
    assert data['maximal'] == sorted(maximal)
    assert data['rows'] == sorted(edge_masks | maximal) and len(data['rows']) == 58
    for mask in range(2 ** 14):
        if truth[mask]:
            assert any(mask & edge == edge for edge in edge_masks)
        else:
            assert any(mask & upper == mask for upper in maximal)
    minimal_true = {mask for mask in range(2 ** 14) if truth[mask] and
                    all(not truth[mask ^ (1 << i)] for i in range(14) if (mask >> i) & 1)}
    assert minimal_true == edge_masks
    print('PASS incidence: 7 lines, 3 points each, unique common line, 21 edges')
    print('PASS full enumeration: 458 independent sets, 37 maximal, 58 complete monotone rows')
    print('PASS prime implicants are exactly the 21 incident pairs')
    for filename in files[1:]:
        circuit = json.loads((DATA / filename).read_text())
        gates, output = circuit['gates'], circuit['output']
        assert len(gates) == 27 and 0 <= output < 14 + len(gates)
        for j, (op, a, b) in enumerate(gates):
            assert op in (0, 1) and 0 <= a < 14 + j and 0 <= b < 14 + j
        wrong = []
        support = [False] * 27
        for mask in range(2 ** 14):
            values = [bool((mask >> i) & 1) for i in range(14)]
            for j, (op, a, b) in enumerate(gates):
                values.append((values[a] and values[b]) if op == 0 else (values[a] or values[b]))
                if mask in edge_masks and values[-1]:
                    support[j] = True
            if values[output] != truth[mask]:
                wrong.append(mask)
        assert not wrong
        assert all(support)
        for p, l in edges:
            vectors = [{(1, 0)} if i == p else {(0, 1)} if i == l else set() for i in range(14)]
            for op, a, b in gates:
                if op == 1:
                    vectors.append(vectors[a] | vectors[b])
                else:
                    vectors.append({(min(2, u[0] + v[0]), min(2, u[1] + v[1]))
                                    for u in vectors[a] for v in vectors[b]})
            assert (1, 1) in vectors[output], (filename, p, l)
        print('PASS', filename, ': 27 strict AO2 gates, 16384 truth rows, 21 joint READ1 pairs, all gates edge-visible')
    after = {name: hashlib.sha256((DATA / name).read_bytes()).hexdigest() for name in files}
    assert before == after
    print(json.dumps({'reviewed_sha256': before}, indent=2))
    print('ALL INDEPENDENT FANO CONTROLS PASSED')


if __name__ == '__main__':
    main()
