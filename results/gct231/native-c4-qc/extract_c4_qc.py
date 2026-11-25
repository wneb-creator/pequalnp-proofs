"""Select exactly the degree-two/three necessary equations, keeping their order."""
import argparse
import hashlib
import json
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument('source', type=Path)
parser.add_argument('output', type=Path)
args = parser.parse_args()
data = json.loads(args.source.read_text())
data['equations'] = [equation for equation in data['equations']
                     if sum(equation['monomial']) in (2, 3)]
assert len(data['equations']) == 16
assert sum(sum(equation['monomial']) == 2 for equation in data['equations']) == 6
assert sum(sum(equation['monomial']) == 3 for equation in data['equations']) == 10
data['scope'] = ('Only quadratic and cubic necessary equations from the direct '
                 'path-C4 chart; quartic conditions omitted.')
data['subset_source_sha256'] = hashlib.sha256(args.source.read_bytes()).hexdigest()
text = json.dumps(data, indent=2) + '\n'
if args.output.exists():
    assert args.output.read_text() == text
else:
    args.output.write_text(text)
print('PASS exact ordered subset: six quadratic and ten cubic equations.')
print('Source SHA256:', data['subset_source_sha256'])
print('Subset SHA256:', hashlib.sha256(args.output.read_bytes()).hexdigest())
