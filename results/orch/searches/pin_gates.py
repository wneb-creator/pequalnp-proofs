import argparse
import json
from pathlib import Path

ap = argparse.ArgumentParser()
ap.add_argument('metadata')
ap.add_argument('cnf')
ap.add_argument('gates')
ap.add_argument('output')
args = ap.parse_args()
data = json.loads(Path(args.metadata).read_text())
source = json.loads(Path(args.gates).read_text())
gates = source['gates'] if isinstance(source, dict) else source
assert len(gates) == len(data['O'])
extra = []
for i, (a, b, op) in enumerate(gates):
    assert 0 <= a < b < data['n']+i and op in [0, 1]
    extra.extend([[data['A'][i][a]], [data['B'][i][b]],
                  [data['O'][i] if op else -data['O'][i]]])
lines = Path(args.cnf).read_text().splitlines()
header = lines[0].split()
assert header[:2] == ['p', 'cnf']
header[3] = str(int(header[3])+len(extra))
lines[0] = ' '.join(header)
lines.extend(' '.join(map(str, c))+' 0' for c in extra)
Path(args.output).write_text('\n'.join(lines)+'\n')
print('Pinned', len(gates), 'gates in', args.output)
