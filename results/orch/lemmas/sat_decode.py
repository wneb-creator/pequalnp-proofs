"""Decode a SAT model of the existing LinkN encoder and exhaustively test it."""
import argparse
import json
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument('n', type=int)
parser.add_argument('s', type=int)
parser.add_argument('edges')
parser.add_argument('model', type=Path)
args = parser.parse_args()
n, s = args.n, args.s
edges = [tuple(map(int, e)) for e in args.edges.split(',')]
A = (1 << n) + n + s + 2
text = args.model.read_text()
assert 's SATISFIABLE' in text, 'No SAT result in this solver log'
positive = {int(v) for line in text.splitlines() if line.startswith('v ')
            for v in line.split()[1:] if int(v) > 0}

def true(kd, j, a):
    return (kd * (s + 1) + j) * A + a + 1 in positive

def pick(kd, j, size):
    return next(i for i in range(size) if true(kd, j, i))

gates = [[pick(0, j, 4), pick(1, j, n+j+1), pick(2, j, n+j+1)]
         for j in range(s)]
output = pick(6, 0, n+s+1)

def evaluate(row):
    wires = [bool(row >> i & 1) for i in range(n)]
    for op, a, b in gates:
        x = wires[a] if a < len(wires) else False
        y = wires[b] if b < len(wires) else False
        wires.append((x and y) if op == 0 else (x or y) if op == 1
                     else True if op == 2 else not x)
    return wires[output] if output < len(wires) else False

bad = [row for row in range(1 << n)
       if evaluate(row) != any((row >> u & 1) and (row >> v & 1)
                               for u, v in edges)]
print(json.dumps({'n': n, 'size': s, 'gates': gates, 'output': output,
                  'not_count': sum(op == 3 for op, _, _ in gates),
                  'mismatches': bad}, indent=2))
