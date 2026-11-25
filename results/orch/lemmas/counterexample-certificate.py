from itertools import combinations
from pathlib import Path
import re
import sys


LINES = [(0, 1, 2), (0, 3, 4), (0, 5, 6), (1, 3, 5), (1, 4, 6), (2, 3, 6), (2, 4, 5)]
EDGES = [(a, 7 + b) for b, line in enumerate(LINES) for a in line]


def signature_check():
    maximal = set()
    for A in range(1 << 7):
        B = sum(1 << b for b, line in enumerate(LINES) if all(not (A >> a & 1) for a in line))
        closed_A = sum(1 << a for a in range(7)
                       if all(not (B >> b & 1) for b, line in enumerate(LINES) if a in line))
        if A == closed_A:
            maximal.add(A | (B << 7))
    assert len(maximal) == 37
    for x in range(1 << 14):
        independent = all(not (x >> a & 1 and x >> b & 1) for a, b in EDGES)
        assert independent == any(x & ~s == 0 for s in maximal)
    assert all(len(set(LINES[b]) & set(LINES[c])) == 1 for b, c in combinations(range(7), 2))
    cover = min(x.bit_count() for x in range(1 << 14)
                if all(x >> a & 1 or x >> b & 1 for a, b in EDGES))
    assert cover == 7
    print('Independent closure enumeration: 37 maximal independent sets; all 16384 assignments covered exactly.')
    print('Fano graph: 21 edges; C4-free; exhaustive minimum vertex-cover size 7; target bound 27.')


def known_star():
    gates = []
    outputs = []
    for a in range(7):
        leaves = [7 + b for b, line in enumerate(LINES) if a in line]
        w = 14 + len(gates)
        gates += [('OR', leaves[0], leaves[1]), ('OR', w, leaves[2]), ('AND', a, w + 1)]
        outputs.append(w + 2)
    while len(outputs) > 1:
        a, b = outputs.pop(), outputs.pop()
        outputs.append(14 + len(gates))
        gates.append(('OR', a, b))
    return gates, outputs[0]


def verify(gates, output):
    assert 0 <= output < 14 + len(gates)
    active = {output}
    for j in reversed(range(len(gates))):
        op, a, b = gates[j]
        assert op in ['AND', 'OR'] and 0 <= a < 14 + j and 0 <= b < 14 + j
        if 14 + j in active:
            active.update([a, b])
    values = [sum(1 << x for x in range(1 << 14) if x >> i & 1) for i in range(14)]
    reach = [frozenset([i]) for i in range(14)]
    target = 0
    for a, b in EDGES:
        target |= values[a] & values[b]
    for j, (op, a, b) in enumerate(gates):
        values.append(values[a] & values[b] if op == 'AND' else values[a] | values[b])
        reach.append(frozenset() if op == 'AND' else reach[a] | reach[b])
        if 14 + j in active:
            assert not (any(i < 7 for i in reach[-1]) and any(i >= 7 for i in reach[-1]))
    assert values[output] == target
    size = sum(14 + j in active for j in range(len(gates)))
    ors = sum(14 + j in active and op == 'OR' for j, (op, _, _) in enumerate(gates))
    print('All 16384 input truth values match; binary AO reads back; every active OR is monochromatic.')
    print('Active gates', size, 'AND', size - ors, 'OR', ors)
    if size < 27:
        print('COUNTEREXAMPLE TO POSTED TOTAL BOUND; Lean certification still required.')
    elif ors < 20:
        print('COUNTEREXAMPLE TO SEPARATE OR BOUND; not a counterexample to the posted total bound.')
    return size, ors


if __name__ == '__main__':
    signature_check()
    if len(sys.argv) == 1:
        gates, output = known_star()
    else:
        text = Path(sys.argv[1]).read_text().rsplit('WITNESS', 1)[1]
        match = re.search(r'output[= ](\d+)', text)
        assert match
        output = int(match.group(1))
        gates = [(op, int(a), int(b)) for op, a, b in re.findall(r'^(AND|OR) (\d+) (\d+)$', text, re.M)]
    verify(gates, output)
