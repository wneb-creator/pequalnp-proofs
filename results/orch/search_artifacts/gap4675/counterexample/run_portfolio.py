import json
import subprocess
from datetime import datetime, timezone
from pathlib import Path
import validate

P = Path(__file__).resolve().parent
records = []
for n, seconds in [(11, 300), (16, 600)]:
    if (P.parent / 'STOP').exists() or (P / 'STOP').exists():
        print('STOP before next phase', flush=True)
        break
    case = P / ('case' + str(n))
    prefix = case / 'run1'
    assert not prefix.with_suffix('.stdout').exists()
    command = [str(P / ('search' + str(n))), str(case / 'seeds.dat'), str(seconds), str(prefix), str(467500 + n)]
    record = {'n': n, 'seconds': seconds, 'command': command, 'started_utc': datetime.now(timezone.utc).isoformat()}
    with prefix.with_suffix('.stdout').open('w') as out, prefix.with_suffix('.stderr').open('w') as err:
        child = subprocess.Popen(command, stdout=out, stderr=err)
        record['pid'] = child.pid
        (P / 'current-run.json').write_text(json.dumps(record, indent=2) + '\n')
        record['exit_code'] = child.wait()
    record['finished_utc'] = datetime.now(timezone.utc).isoformat()
    if record['exit_code'] == 10:
        checked = validate.check(case / 'run1.counterexample.graph.json', case / 'run1.counterexample.circuit.json')
        (case / 'run1-counterexample-fullcheck.json').write_text(json.dumps(checked, indent=2) + '\n')
        record['counterexample_independently_validated'] = checked['is_counterexample']
    records.append(record)
    (P / 'portfolio1-results.json').write_text(json.dumps(records, indent=2) + '\n')
    print(json.dumps(record), flush=True)
    if record['exit_code'] != 0:
        break
