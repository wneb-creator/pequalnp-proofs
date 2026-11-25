"""Exhaustive finite check of a sharp protected-matching K4 control."""
import json

GATES = [
    ['or', 0, 2], ['and', 5, 10],
    ['or', 1, 3], ['and', 8, 12],
    ['or', 4, 6], ['and', 0, 14],
    ['or', 4, 7], ['and', 1, 16],
    ['or', 7, 9], ['and', 2, 18],
    ['or', 6, 9], ['and', 3, 20],
    ['or', 11, 13], ['or', 22, 15], ['or', 23, 17],
    ['or', 24, 19], ['or', 25, 21],
]
EDGE_ENDS = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
EDGES = [(v, 4 + e) for e, pair in enumerate(EDGE_ENDS) for v in pair]


def evaluate(mask, seed=None):
    values = [bool(mask & (1 << i)) for i in range(10)]
    derivatives = [i == seed for i in range(10)]
    for j, (op, a, b) in enumerate(GATES):
        assert a != b and 0 <= a < 10 + j and 0 <= b < 10 + j
        if op == 'and':
            values.append(values[a] and values[b])
            derivatives.append((values[a] and derivatives[b]) or (derivatives[a] and values[b]))
        else:
            values.append(values[a] or values[b])
            derivatives.append(derivatives[a] or derivatives[b])
    return values, derivatives


if __name__ == '__main__':
    for mask in range(1024):
        expected = any(mask & (1 << a) and mask & (1 << b) for a, b in EDGES)
        assert evaluate(mask)[0][-1] == expected
    readers = [[] for _ in range(27)]
    for j, (_, a, b) in enumerate(GATES):
        readers[a].append(10 + j)
        readers[b].append(10 + j)
    singleton_tables = [evaluate(1 << i)[0] for i in range(10)]
    supports = [[i for i in range(10) if singleton_tables[i][w]] for w in range(27)]
    eligible = sorted({i for w in range(27) if len(readers[w]) >= 2 for i in supports[w]})
    bplus = sum(max(0, len(readers[w]) - 1) for w in range(26) if supports[w])
    bzero = sum(max(0, len(readers[w]) - 1) for w in range(26) if not supports[w])
    assert eligible == [0, 1, 2, 3, 4, 6, 7, 9] and bplus == 8 and bzero == 0
    for i in [5, 8]:
        pending, reached = [i], set()
        while pending:
            w = pending.pop()
            if w in reached:
                continue
            reached.add(w)
            assert len(readers[w]) <= 1
            pending.extend(readers[w])
    traces = []
    for a, b in EDGES:
        forward = evaluate(1 << a, b)[1][-1]
        reverse = evaluate(1 << b, a)[1][-1]
        assert forward and reverse
        traces.append({'edge': [a, b], 'both_output_derivatives': [forward, reverse]})
    print(json.dumps({'scope': 'Computational K4 control only; not a Fano witness or a Lean theorem.',
                      'inputs': 10, 'gates': GATES, 'output': 26, 'size': 17,
                      'truth_assignments_verified': 1024, 'eligible': eligible,
                      'Bplus': bplus, 'Bzero': bzero, 'residual_units': bplus-len(eligible),
                      'protected_inputs': [5, 8], 'edge_derivatives': traces}, indent=2))
