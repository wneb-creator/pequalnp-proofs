import json
from pathlib import Path

base = Path('/tmp/oec/pequalnp-pilot-86/counterexample')
data = json.loads((base/'c6-15-sym-semantic-edge-active.json').read_text())
n = data['n']
gates = [(a, b, 0) for a, b in data['edges']]
def add(a, b):
    gates.append((a, b, 1))
    return n+len(gates)-1
groups = [6, 7, add(8, 9), add(10, 11)]
pairs = [add(groups[i], groups[(i+1)%4]) for i in range(4)]
left, right = add(pairs[0], pairs[1]), add(pairs[2], pairs[3])
add(left, right)
assert len(gates) == 15
index = {i: i for i in range(n)}
remaining = set(range(len(gates)))
ordered = []
while remaining:
    ready = [(*sorted((index[a], index[b])), op, i)
             for i in remaining for a, b, op in [gates[i]] if a in index and b in index]
    assert ready
    a, b, op, i = min(ready)
    index[n+i] = n+len(ordered)
    ordered.append((a, b, op))
    remaining.remove(i)
assert index[n+len(gates)-1] == n+len(gates)-1
for essential in [False, True]:
    stem = 'c6-15-sym-semantic-edge-active'+('-edge-essential' if essential else '')
    data = json.loads((base/(stem+'.json')).read_text())
    lines = (base/(stem+'.cnf')).read_text().splitlines()
    extra = []
    for i, (a, b, op) in enumerate(ordered):
        extra.extend([[data['A'][i][a]], [data['B'][i][b]],
                      [data['O'][i] if op else -data['O'][i]]])
    header = lines[0].split()
    header[3] = str(int(header[3])+len(extra))
    lines[0] = ' '.join(header)
    lines.extend(' '.join(map(str, c))+' 0' for c in extra)
    out = base/('essential-negative-'+('with' if essential else 'without')+'.cnf')
    out.write_text('\n'.join(lines)+'\n')
(base/'essential-negative-gates.json').write_text(json.dumps(ordered, indent=2)+'\n')
print('Pinned a C6 circuit with four globally redundant but locally incomparable OR gates.')
