import json
import subprocess
from datetime import datetime, timezone
from pathlib import Path

P = Path(__file__).resolve().parent
assert not (P.parent / 'STOP').exists() and not (P / 'STOP').exists()
prefix = P / 'run1'
assert not prefix.with_suffix('.stdout').exists()
command = [str(P / 'search'), '900', str(prefix), '1884']
record = {'started_utc': datetime.now(timezone.utc).isoformat(), 'command': command, 'seconds': 900}
with prefix.with_suffix('.stdout').open('w') as out, prefix.with_suffix('.stderr').open('w') as err:
    child = subprocess.Popen(command, stdout=out, stderr=err)
    record['pid'] = child.pid
    (P / 'run1-record.json').write_text(json.dumps(record, indent=2) + '\n')
    record['exit_code'] = child.wait()
record['finished_utc'] = datetime.now(timezone.utc).isoformat()
(P / 'run1-record.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record), flush=True)
