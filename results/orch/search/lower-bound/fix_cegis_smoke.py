import json
from pathlib import Path

base = Path('/tmp/oec/pequalnp-pilot-70/lower-bound')
search = Path('/tmp/oec/pequalnp-pilot-70/circuit-search')

def fix(source, mapping, gates, destination):
    model = json.loads(mapping.read_text())
    assert len(gates) == len(model['structure'])
    lines = source.read_text().splitlines()
    header = lines[0].split()
    variables, count = map(int, header[2:])
    units = []
    for gate, description in zip(gates, model['structure']):
        op, a, b = gate
        assert a <= b
        units.extend([description['left'][a], description['right'][b],
                      description['op'] if op == 'or' else -description['op']])
    destination.write_text(f'p cnf {variables} {count+len(units)}\n' +
                          '\n'.join(lines[1:]) + '\n' +
                          '\n'.join(f'{u} 0' for u in units) + '\n')

star = json.loads((search/'star27.json').read_text())
fix(base/'cegis27.cnf', search/'heawood27.map.json', star, base/'cegis27-fixed.cnf')

complete = [('or',0,1),('or',0,2),('or',14,15)]
last = 16
for i in range(3,7):
    complete.append(('or',i,last))
    last = 13 + len(complete)
left = last
complete.append(('or',7,8))
last = 13 + len(complete)
for i in range(9,14):
    complete.append(('or',i,last))
    last = 13 + len(complete)
complete.append(('and',left,last))
while len(complete) < 26:
    last = 13 + len(complete)
    complete.append(('or',last,last))
assert len(complete)==26
fix(base/'cegis26.cnf', search/'heawood26.map.json', complete, base/'cegis26-complete.cnf')
(base/'cegis26-complete-network.json').write_text(json.dumps(complete)+'\n')
print('Prepared fixed exact 27-gate and fixed complete-bipartite 26-gate smoke instances.')
