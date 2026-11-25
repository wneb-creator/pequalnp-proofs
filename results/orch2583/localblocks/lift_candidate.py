import argparse
import json
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument('--data', required=True)
parser.add_argument('--witness', required=True)
parser.add_argument('--output', required=True)
args = parser.parse_args()
data = json.loads(Path(args.data).read_text())
local = json.loads(Path(args.witness).read_text())
source = json.loads(Path('/tmp/oec/pequalnp-pilot-103/orch2583/fano-data.json').read_text())
edges = [tuple(e) for e in source['edges']]
n = data['inputs']
mapping = data['original_wires']
selected = set(data['selected_points'])

def remap(w):
    return mapping[w] if w < n else 14+w-n

gates = [[op,remap(a),remap(b)] for op,a,b in local]
acc = 14+len(gates)-1
for p in range(7):
    if p in selected:
        continue
    a,b,c = [l for q,l in edges if q == p]
    gates.append([1,a,b]); first = 14+len(gates)-1
    gates.append([1,first,c]); second = 14+len(gates)-1
    gates.append([0,p,second]); star = 14+len(gates)-1
    gates.append([1,acc,star]); acc = 14+len(gates)-1
assert acc == 14+len(gates)-1
assert len(gates) <= 26
for i,(op,a,b) in enumerate(gates):
    assert op in [0,1] and 0 <= a < 14+i and 0 <= b < 14+i
for mask in range(1<<14):
    wires = [bool(mask & (1<<i)) for i in range(14)]
    for op,a,b in gates:
        wires.append((wires[a] or wires[b]) if op else (wires[a] and wires[b]))
    target = any(mask & (1<<p) and mask & (1<<l) for p,l in edges)
    assert wires[-1] == bool(target), mask
Path(args.output).write_text(json.dumps(gates)+'\n')
print(json.dumps({'status':'VALIDATED','gates':len(gates),'rows':1<<14,
                  'source_data':args.data,'source_witness':args.witness,'output':args.output}), flush=True)
