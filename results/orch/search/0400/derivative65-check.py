import hashlib
import json
from pathlib import Path

HERE = Path('/tmp/oec/pequalnp-pilot-21/search')
source = HERE/'diagnostic157/explicit29-diagnostic.json'
data = json.loads(source.read_text())
gates = [(a,b,not op) for a,b,op in data['gates']]
outputs = data['out']
lines = [{(w+d)%13 for d in (0,1,3,9)} for w in range(13)]
rows = set()
for line in lines:
    zero = 8191 ^ sum(1<<p for p in line)
    rows.add(zero)
    rows.update(zero | (1<<p) for p in line)
assert len(gates) == 29 and len(rows) == 65
band_errors = [0]*13
for x in range(8192):
    wires = [bool(x>>p&1) for p in range(13)]
    for a,b,is_and in gates:
        assert 0 <= a < len(wires) and 0 <= b < len(wires)
        wires.append(wires[a] and wires[b] if is_and else wires[a] or wires[b])
    targets = [any(x>>p&1 for p in line) for line in lines]
    for w in range(13):
        got = wires[outputs[w]]
        assert not got or targets[w]
        if x in rows:
            assert got == targets[w]
        if x.bit_count() in (7,8):
            band_errors[w] += got != targets[w]
record = json.loads((HERE/'diagnostic157/derivative65-original29.json').read_text())
assert [list(g) for g in gates] == record['original_orientation_gates']
assert outputs == record['out']
assert band_errors == record['band_errors_per_output']
print(json.dumps({'status':'PASS','gates':len(gates),'derivative_rows':len(rows),
                  'global_upper_rows':8192,'band_errors_per_output':band_errors,
                  'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest()},indent=2))
