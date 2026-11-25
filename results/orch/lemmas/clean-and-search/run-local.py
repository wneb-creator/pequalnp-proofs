from pathlib import Path
import itertools, json, subprocess, time

root = Path('/tmp/oec/pequalnp-pilot-184/clean-and-search')
source = Path('/workspace/pequalnp-proofs/results/orch/lemmas/clean-and-counter/theta233/one-error-candidate.json')
c = next(c for c in json.loads((root / 'cases.json').read_text()) if c['name'] == 'theta233')
snapshot = json.loads(source.read_text())
(root / 'theta233-one-error-snapshot.json').write_text(json.dumps(snapshot, indent=2) + '\n')
n, s = 7, 10
base = root / 'theta233-local-base.cnf'
with (root / 'local-base.gen.stdout').open('w') as out, (root / 'local-base.gen.stderr').open('w') as err:
    subprocess.run(['python3', str(root / 'gen.py'), str(n), str(s), str(root / 'theta233.edges.json'), str(base), 'ordinary'], stdout=out, stderr=err, check=True)
lines = base.read_text().splitlines()
_, _, variables, count = lines[0].split()
A = (1 << n) + n + s + 2
ix = lambda kd, j, a: (kd * (s + 1) + j) * A + a + 1
reports = []
for free in itertools.combinations(range(s), 2):
    units = []
    for j, (op, a, b) in enumerate(snapshot['gates']):
        if j in free: continue
        a, b = sorted((a, b))
        units.extend((ix(0, j, 0 if op == 'and' else 1), ix(1, j, a), ix(2, j, b)))
    stem = 'theta233-local-' + '-'.join(map(str, free))
    cnf = root / (stem + '.cnf')
    cnf.write_text('p cnf ' + variables + ' ' + str(int(count) + len(units)) + '\n' + '\n'.join(lines[1:]) + '\n' + ''.join(str(u) + ' 0\n' for u in units))
    started = time.monotonic()
    peak = 0
    stopped = False
    with (root / (stem + '.stdout')).open('w') as out, (root / (stem + '.stderr')).open('w') as err:
        proc = subprocess.Popen(['/tmp/oec/pequalnp-pilot-184/replacement/cadical/build/cadical', '--sat', '-t', '5', str(cnf)], stdout=out, stderr=err)
        while proc.poll() is None:
            usage = subprocess.run(['ps', '-o', 'rss=', '-p', str(proc.pid)], capture_output=True, text=True)
            rss = int(usage.stdout.strip() or 0)
            peak = max(peak, rss)
            if rss > 300 * 1024:
                proc.terminate()
                stopped = True
            time.sleep(.05)
    report = {'free_gates': free, 'exit': proc.returncode, 'seconds': time.monotonic() - started, 'peak_KiB': peak, 'memory_stopped': stopped}
    if proc.returncode == 10:
        positive = {int(v) for line in (root / (stem + '.stdout')).read_text().splitlines() if line.startswith('v ') for v in line.split()[1:] if int(v) > 0}
        gates = [(next(d for d in range(3) if ix(0, j, d) in positive), next(k for k in range(n+j+1) if ix(1,j,k) in positive), next(k for k in range(n+j+1) if ix(2,j,k) in positive)) for j in range(s)]
        errors = []
        unsafe = []
        for r in range(1 << n):
            f = any((r >> a & 1) and (r >> b & 1) for a, b in c['edges'])
            wires = [bool(r >> i & 1) for i in range(n)]
            for j, (op, a, b) in enumerate(gates):
                u = wires[a] if a < len(wires) else False
                v = wires[b] if b < len(wires) else False
                w = (u and v) if op == 0 else (u or v) if op == 1 else True
                wires.append(w)
                if op != 1 and w and not f: unsafe.append((r, j))
            if wires[-1] != bool(f): errors.append(r)
        report.update({'witness': gates, 'truth_errors': errors, 'unsafe_ANDs': unsafe})
        assert not errors
    reports.append(report)
    (root / 'local-results.json').write_text(json.dumps(reports, indent=2) + '\n')
    print({k: v for k, v in report.items() if k not in ('witness', 'unsafe_ANDs')}, flush=True)
    if proc.returncode == 10: break
