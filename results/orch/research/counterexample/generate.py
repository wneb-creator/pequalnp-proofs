from pathlib import Path

ROOT = Path(__file__).resolve().parent
EDGES = [(p, 7 + l) for p in range(7) for l in range(7)
         if (p - l) % 7 in (0, 1, 3)]


def target(mask):
    return any((mask >> p) & 1 and (mask >> l) & 1 for p, l in EDGES)


trues = [(1 << p) | (1 << l) for p, l in EDGES]
falses = [mask for mask in range(1 << 14)
          if not target(mask)
          and all(target(mask | (1 << i)) for i in range(14)
                  if not (mask >> i) & 1)]
tests = trues + falses
assert len(trues) == 21 and len(falses) == 37
assert all(any(edge & mask == edge for edge in trues)
           if target(mask)
           else any(mask & maximal == mask for maximal in falses)
           for mask in range(1 << 14))
columns = [sum(((mask >> i) & 1) << j for j, mask in enumerate(tests))
           for i in range(14)]
gates = []
stars = []
for l in range(7):
    ps = [p for p in range(7) if (p - l) % 7 in (0, 1, 3)]
    gates.append((0, ps[0], ps[1]))
    a = 14 + len(gates) - 1
    gates.append((0, a, ps[2]))
    b = 14 + len(gates) - 1
    gates.append((1, b, 7 + l))
    stars.append(14 + len(gates) - 1)
a = stars[0]
for b in stars[1:]:
    gates.append((0, a, b))
    a = 14 + len(gates) - 1
assert len(gates) == 27
for mask in range(1 << 14):
    wires = [(mask >> i) & 1 for i in range(14)]
    for op, left, right in gates:
        wires.append((wires[left] & wires[right]) if op
                     else (wires[left] | wires[right]))
    assert bool(wires[a]) == target(mask)

(ROOT / 'problem.txt').write_text(
    str(len(tests)) + ' ' + str((1 << len(trues)) - 1) + '\n'
    + ' '.join(map(str, columns)) + '\n'
    + '\n'.join(' '.join(map(str, gate)) for gate in gates) + '\n')
print('Verified canonical27-gate circuit on all16384 inputs.')
print('Verified exact characterization by21 positive and37 maximal false inputs.')
