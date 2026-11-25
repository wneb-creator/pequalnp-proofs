import datetime
import hashlib
import json
import re
from pathlib import Path


base = Path(__file__).parent
records = []
for path in sorted(base.glob('*-solve.log')):
    name = path.name.removesuffix('-solve.log')
    meta_path = base / (name + '.json')
    log = path.read_text()
    finished = re.search(r'^c exit (\d+)$', log, re.M)
    runtime = re.search(r'^c total real time since initialization:\s+([\d.]+)', log, re.M)
    code = None if finished is None else int(finished.group(1))
    rec = {'name': name, 'exit_code': code,
           'wall_seconds': None if runtime is None else float(runtime.group(1)),
           'status': {10: 'SAT', 20: 'UNSAT', 0: 'TIMEOUT_OR_UNKNOWN'}.get(code, 'RUNNING')}
    status_path = base / (name + '.status.json')
    if status_path.exists():
        supervised = json.loads(status_path.read_text())
        rec['supervisor_status'] = supervised
        rec['status'] = supervised['status']
        if 'returncode' in supervised:
            rec['exit_code'] = supervised['returncode']
        if 'wall_seconds' in supervised:
            rec['wall_seconds'] = supervised['wall_seconds']
    if meta_path.exists():
        data = json.loads(meta_path.read_text())
        rec.update({key: data.get(key) for key in
                    ['k', 'roots', 'support', 'minimum', 'violation', 'ordered',
                     'projected', 'patterns', 'fanout_budget', 'and_count',
                     'exact_and_count', 'require_nonbelow_and']})
    cnf = base / (name + '.cnf')
    if cnf.exists():
        rec['cnf_sha256'] = hashlib.sha256(cnf.read_bytes()).hexdigest()
    decoded = base / (name + '-decoded.json')
    if decoded.exists():
        rec['independent_verification'] = json.loads(decoded.read_text())['status']
    records.append(rec)
result = {'generated_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'records': records}
(base / 'sat-all-search-summary.json').write_text(json.dumps(result, indent=2) + '\n')
fano_result = dict(result, records=[r for r in records if r['name'].startswith('fano-')])
(base / 'fano-all-search-summary.json').write_text(json.dumps(fano_result, indent=2) + '\n')
print(json.dumps({'records': len(records), 'counts': {
    status: sum(r['status'] == status for r in records)
    for status in ['SAT', 'UNSAT', 'TIMEOUT_OR_UNKNOWN', 'INTERRUPTED', 'RUNNING']}}))
