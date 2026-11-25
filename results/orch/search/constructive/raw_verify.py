import argparse
import hashlib
import json
from pathlib import Path


HEAWOOD = [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13),
           (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12),
           (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12),
           (6, 8), (6, 9), (6, 11)]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_cnf(path):
    header = None
    pending = []
    clauses = []
    for line in path.read_text().splitlines():
        words = line.split()
        if not words or words[0] == 'c':
            continue
        if words[0] == 'p':
            assert header is None and len(words) == 4 and words[1] == 'cnf'
            header = (int(words[2]), int(words[3]))
            assert header[0] > 0 and header[1] >= 0
            continue
        assert header is not None
        for word in words:
            literal = int(word)
            if literal == 0:
                clauses.append(pending)
                pending = []
            else:
                assert abs(literal) <= header[0]
                pending.append(literal)
    assert header is not None and not pending and len(clauses) == header[1]
    return header[0], clauses


def read_model(path, nv):
    assignment = {}
    statuses = []
    for line in path.read_text().splitlines():
        words = line.split()
        if not words:
            continue
        if words[0] == 's':
            statuses.append(words[1:])
        if words[0] == 'v':
            for word in words[1:]:
                literal = int(word)
                if not literal:
                    continue
                variable, value = abs(literal), literal > 0
                assert variable <= nv
                assert variable not in assignment or assignment[variable] == value
                assignment[variable] = value
    assert statuses == [['SATISFIABLE']], 'Expected exactly one SAT status'
    assert len(assignment) == nv, 'SAT model is incomplete'
    return assignment


def evaluate(gates, mask):
    values = [bool(mask >> i & 1) for i in range(14)]
    for op, a, b in gates:
        assert op in ('and', 'or') and 0 <= a <= b < len(values)
        values.append((values[a] or values[b]) if op == 'or' else (values[a] and values[b]))
    return values


def verify(cnf, map_path, model_path, output):
    assert not output.exists()
    metadata = json.loads(map_path.read_text())
    assert metadata['ninputs'] == 14
    assert sorted(map(tuple, metadata['edges'])) == sorted(HEAWOOD)
    assert len(metadata['structure']) == metadata['gates'] > 0
    nv, clauses = read_cnf(cnf)
    assert (nv, len(clauses)) == (metadata['nv'], metadata['clauses'])
    if 'cnf_sha256' in metadata:
        assert metadata['cnf_sha256'] == digest(cnf)
    assignment = read_model(model_path, nv)
    for index, clause in enumerate(clauses):
        assert any(assignment[abs(literal)] == (literal > 0) for literal in clause), index
    gates = []
    for index, gate in enumerate(metadata['structure']):
        assert len(gate['left']) == len(gate['right']) == 14 + index
        left = [i for i, variable in enumerate(gate['left']) if assignment[variable]]
        right = [i for i, variable in enumerate(gate['right']) if assignment[variable]]
        assert len(left) == len(right) == 1
        assert left[0] <= right[0] < 14 + index
        gates.append(['or' if assignment[gate['op']] else 'and', left[0], right[0]])
    for mask in range(1 << 14):
        values = evaluate(gates, mask)
        target = any(values[a] and values[b] for a, b in HEAWOOD)
        assert values[-1] == target, f'Target mismatch on raw input {mask}'
    for row, mask in enumerate(metadata['rows']):
        assert 0 <= mask < 1 << 14
        values = evaluate(gates, mask)
        for index, gate in enumerate(metadata['structure']):
            assert len(gate['out']) == len(metadata['rows'])
            assert assignment[gate['out'][row]] == values[14 + index]
            for key, operand in (('left_values', gates[index][1]), ('right_values', gates[index][2])):
                if key in gate:
                    assert len(gate[key]) == len(metadata['rows'])
                    assert assignment[gate[key][row]] == values[operand]
    report = dict(status='VERIFIED', gates=gates, gate_count=len(gates),
                  checked_clauses=len(clauses), checked_assignments=1 << 14,
                  checked_encoded_rows=len(metadata['rows']), cnf_sha256=digest(cnf),
                  map_sha256=digest(map_path), model_sha256=digest(model_path),
                  verifier_sha256=digest(Path(__file__)), target='Exact posted Heawood edge function')
    output.write_text(json.dumps(report, indent=2) + '\n')
    return {key: value for key, value in report.items() if key != 'gates'}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--cnf', type=Path, required=True)
    parser.add_argument('--map', type=Path, required=True)
    parser.add_argument('--model', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(verify(args.cnf, args.map, args.model, args.output)), flush=True)


if __name__ == '__main__':
    main()
