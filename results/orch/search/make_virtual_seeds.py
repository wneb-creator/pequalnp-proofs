"""Create two exact-function seeds exercising virtual-signature propagation."""
import sys
from pathlib import Path

rows = Path(sys.argv[1]).read_text().splitlines()
header = list(map(int, rows[0].split()))
assert header[0] == 14 and header[-1] == 27
base = [list(map(int, row.split())) for row in rows[2:]]
assert len(base) == 27
output = Path(sys.argv[2])
output.mkdir(parents=True, exist_ok=True)

def save(name, gates):
    changed = header.copy()
    changed[-1] = len(gates)
    text = ' '.join(map(str, changed)) + '\n' + rows[1] + '\n'
    text += '\n'.join(' '.join(map(str, gate)) for gate in gates) + '\n'
    (output / name).write_text(text)

zero = [gate.copy() for gate in base]
zero.extend([[0, 0, 7], [0, 41, 1], [1, 40, 42]])
save('fano-virtual-zero.input', zero)
one = [gate.copy() for gate in base]
wire = 0
for variable in range(1, 14):
    one.append([1, wire, variable])
    wire = 14 + len(one) - 1
one.append([0, 40, wire])
save('fano-virtual-one.input', one)
