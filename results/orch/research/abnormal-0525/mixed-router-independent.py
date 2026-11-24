import argparse
import hashlib
import json
from pathlib import Path

parser = argparse.ArgumentParser(description='Independent full-table check of the auxiliary mixed router.')
parser.add_argument('artifact', type=Path)
args = parser.parse_args()
data = json.loads(args.artifact.read_text())
lines = [{(w + t) % 13 for t in (0, 1, 3, 9)} for w in range(13)]
columns = [sum(1 << x for x in range(8192) if (x >> p) & 1) for p in range(13)]
for j, (op, a, b) in enumerate(data['gates']):
    assert op in ('and', 'or') and a != b and 0 <= a < 13 + j and 0 <= b < 13 + j
    columns.append(columns[a] & columns[b] if op == 'and' else columns[a] | columns[b])
band = sum(1 << x for x in range(8192) if x.bit_count() in (7, 8))
assert band.bit_count() == 3003 and len(data['gates']) == 52
assert all((c & band) not in (0, band) for c in columns[13:])
for w, out in enumerate(data['outputs']):
    target = 0
    for p in lines[w]:
        target |= columns[p]
    assert ((columns[out] ^ target) & band) == 0
router = columns[data['shared_gate']]
def is_minimal(column, mask):
    return bool((column >> mask) & 1) and all(
        not ((column >> (mask ^ (1 << p))) & 1)
        for p in range(13) if (mask >> p) & 1)
minterms = [x for x in range(8192) if is_minimal(router, x)]
assert minterms == data['shared_minterms']
assert sorted(x.bit_count() for x in minterms) == [8, 9, 9, 10]
first = []
for w in (0, 1):
    complement = sum(1 << p for p in range(13) if p not in lines[w])
    first.append(next(i for i in range(13, len(columns)) if is_minimal(columns[i], complement)))
assert first == [23, 23]
positive_band = [x for x in range(8192) if ((router & band) >> x) & 1]
assert positive_band == [6629]
abnormal = [w for w, out in enumerate(data['outputs'])
            if (columns[out] >> sum(1 << p for p in range(13) if p not in lines[w])) & 1]
assert abnormal == [0, 1]
print(json.dumps({'status': 'PASS', 'gate_count': 52, 'all_band_rows_checked': 3003,
                  'all_gates_band_nonconstant': True, 'first_complement_minterm_gates': first,
                  'router_minterms': minterms, 'router_band_positive_rows': positive_band,
                  'abnormal_outputs': abnormal,
                  'artifact_sha256': hashlib.sha256(args.artifact.read_bytes()).hexdigest(),
                  'scope': 'Auxiliary nonminimal router only; not a gap counterexample or Lean proof'}, indent=2))
