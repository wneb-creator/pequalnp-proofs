import json
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

root = Path('/tmp/oec/pequalnp-pilot-71/structural')
cases = json.loads(Path('/tmp/oec/pequalnp-pilot-71/core-counterexample/fano-10gate-necessary-supports.json').read_text())
cases = [c for c in cases if c['size'] == 10]
cases.sort(key=lambda c: -c['gain'])
solver = '/tmp/oec/pequalnp-pilot-71/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical'
active = []
finished = []
found = False


def announce(**row):
    row['utc'] = datetime.now(timezone.utc).isoformat()
    print(json.dumps(row), flush=True)


while cases or active:
    if (root / 'SAT_STOP').exists() or found:
        for job in active:
            job['process'].terminate()
        for job in active:
            job['process'].wait()
            job['log'].close()
            announce(event='stopped', support=job['case']['support'])
        break
    limit = int((root / 'sat-workers.txt').read_text())
    while cases and len(active) < limit:
        case = cases.pop(0)
        name = 'fano-g10-control-' + str(case['support'])
        stem = str(root / name)
        with open(stem + '-encode.log', 'w') as log:
            result = subprocess.run([sys.executable, str(root / 'fano_sat.py'),
                '--gates', '10', '--minimum', '9', '--support', ','.join(map(str, case['vertices'])),
                '--ordered', '--projected', '--patterns', '--stem', stem], stdout=log, stderr=subprocess.STDOUT)
        if result.returncode:
            announce(event='encoding_error', support=case['support'], returncode=result.returncode)
            continue
        log = open(stem + '-solve.log', 'w')
        process = subprocess.Popen([solver, '-t', '300', '-w', stem + '.sol', stem + '.cnf'],
            stdout=log, stderr=subprocess.STDOUT)
        active.append(dict(case=case, stem=stem, process=process, log=log, started=time.time()))
        announce(event='started', support=case['support'], vertices=case['vertices'], pid=process.pid)
    for job in active[:]:
        result = job['process'].poll()
        if result is None:
            continue
        job['log'].close()
        active.remove(job)
        row = dict(support=job['case']['support'], exit=result, seconds=time.time() - job['started'])
        finished.append(row)
        announce(event='finished', **row)
        (root / 'sat-control-summary.json').write_text(json.dumps(finished, indent=2))
        if result == 10:
            with open(job['stem'] + '-decode.log', 'w') as log:
                decoded = subprocess.run([sys.executable, str(root / 'decode_sat.py'), job['stem']],
                    stdout=log, stderr=subprocess.STDOUT)
            announce(event='SAT_verification', support=job['case']['support'], exit=decoded.returncode)
            if decoded.returncode == 0:
                found = True
    time.sleep(1)
announce(event='queue_done', finished=len(finished), found=found)
