import hashlib
import json
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

P = Path(__file__).resolve().parent
stop = P.parent.parent / 'STOP'
assert not stop.exists() and not (P / 'STOP').exists(), 'STOP active'
prior = json.loads((P.parent / 'stochastic' / 'portfolio1-results.json').read_text())
assert len(prior) == 5 and all(r['exit_code'] == 0 for r in prior), 'Fixed portfolio has not completed safely'
seconds = int(sys.argv[1]) if len(sys.argv) > 1 else 1200
prefix = P / 'variable1'
assert not prefix.with_suffix('.stdout').exists()
command = [str(P / 'search'), str(P / 'seeds.dat'), str(seconds), str(prefix), '497020']
record = {'started_utc': datetime.now(timezone.utc).isoformat(), 'command': command, 'seconds': seconds}
with prefix.with_suffix('.stdout').open('w') as out, prefix.with_suffix('.stderr').open('w') as err:
    child = subprocess.Popen(command, stdout=out, stderr=err)
    record['pid'] = child.pid
    (P / 'variable1-run.json').write_text(json.dumps(record, indent=2) + '\n')
    code = child.wait()
record.update(exit_code=code, finished_utc=datetime.now(timezone.utc).isoformat())
(P / 'variable1-run.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record), flush=True)
sys.exit(0 if code in (0, 10, 75) else code)
