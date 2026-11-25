import hashlib
import json
import re
from datetime import datetime, timezone
from pathlib import Path
import validate

P = Path(__file__).resolve().parent
record = json.loads((P / 'run1-record.json').read_text())
assert 'exit_code' in record
lines = (P / 'run1.stdout').read_text().splitlines()
seen = set()
results = []
for k, line in enumerate(lines):
    if not line.startswith(('INITIAL ', 'BEST ', 'FINAL ')):
        continue
    m = re.search(r'fn=(\d+) fp=(\d+).*output=(-?\d+)', line)
    assert m
    gates = []
    for item in lines[k+1:k+19]:
        wire, op, a, b = map(int, item.split())
        assert wire == 11 + len(gates)
        gates.append([op, a if a >= 0 else 100000, b if b >= 0 else 100000])
    out = int(m[3])
    data = {'physical_inputs': 11, 'input_map': list(range(10)), 'free_unary': 'not',
            'gates': gates, 'output': out if out >= 0 else 100000}
    key = json.dumps(data, sort_keys=True)
    if key in seen:
        continue
    seen.add(key)
    path = P / ('run1-improvement-' + str(len(results)).zfill(2) + '.json')
    assert not path.exists()
    path.write_text(json.dumps(data, indent=2) + '\n')
    checked = validate.check(path)
    assert checked['wrong_rows'] == int(m[1]) + int(m[2])
    checked['source_header'] = line
    results.append(checked)
(P / 'run1-improvement-checks.json').write_text(json.dumps(results, indent=2) + '\n')
files = [P / 'freeze_heuristic.py', P / 'run1-record.json', P / 'run1.stdout', P / 'run1.stderr',
         P / 'run1-driver.stdout', P / 'run1-driver.stderr', P / 'run1-improvement-checks.json']
files += [Path(r['circuit']) for r in results]
for suffix in ['best.json', 'final.json', 'counterexample.json', 'control0.json', 'control1.json', 'control2.json', 'control3.json']:
    file = P / ('run1.' + suffix)
    if file.exists():
        files.append(file)
manifest = {'frozen_utc': datetime.now(timezone.utc).isoformat(), 'record': record,
            'scope': 'Heuristic results; independently replayed every improvement on all1024 inputs. No lower-bound conclusion.',
            'files': [{'path': str(f), 'size': f.stat().st_size, 'sha256': hashlib.sha256(f.read_bytes()).hexdigest()} for f in files]}
(P / 'run1-final-manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
print('Frozen', len(results), 'unique improvements; final best wrong rows', min(r['wrong_rows'] for r in results),
      'child exit', record['exit_code'], 'counterexamples', sum(r['is_posted_counterexample'] for r in results))
