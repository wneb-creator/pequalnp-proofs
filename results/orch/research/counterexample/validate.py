import sys
from pathlib import Path

lines = Path(sys.argv[1]).read_text().splitlines()
start = max(i for i, line in enumerate(lines) if line.startswith('output '))
output = int(lines[start].split()[1])
gates = []
for line in lines[start + 1:]:
    parts = line.split()
    if len(parts) != 4 or not parts[0].isdigit():
        break
    index, op, left, right = parts
    index, left, right = int(index), int(left), int(right)
    assert index == 14 + len(gates)
    assert 0 <= left < index and 0 <= right < index
    assert op in ('AND', 'OR')
    gates.append((op, left, right))
assert 0 <= output < 14 + len(gates)
bad = []
for mask in range(1 << 14):
    wires = [bool(mask & (1 << i)) for i in range(14)]
    wanted = any(wires[p] and wires[7 + l]
                 for l in range(7) for p in (l, (l + 1) % 7, (l + 3) % 7))
    for op, left, right in gates:
        wires.append((wires[left] and wires[right]) if op == 'AND'
                     else (wires[left] or wires[right]))
    if wires[output] != wanted:
        bad.append(mask)
print('gates', len(gates), 'output', output,
      'wrong full truth table assignments', len(bad), 'of16384')
print('first mismatches', bad[:20])
sys.exit(bool(bad))
