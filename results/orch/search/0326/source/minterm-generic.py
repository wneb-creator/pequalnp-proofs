import importlib.util, itertools, json, os, pathlib, subprocess, time

HERE = pathlib.Path('/tmp/oec/pequalnp-pilot-21/search')
spec = importlib.util.spec_from_file_location('genericbase', HERE / 'cegis-full.py')
f = importlib.util.module_from_spec(spec)
spec.loader.exec_module(f)
ROOT = HERE / 'minterm-generic'
ROOT.mkdir(exist_ok=True)


def main():
    results = []
    for n, d in [(4, 3), (5, 3), (5, 4), (6, 4), (6, 5)]:
        started = time.monotonic()
        rows = [x for x in range(1 << n) if x.bit_count() in (d-1, n-1)]
        base = [sum(1 << r for r, x in enumerate(rows) if x >> p & 1) for p in range(n)]
        f.TARGETS = [sum(1 << r for r, x in enumerate(rows) if x.bit_count() == n-1)]
        ng = 2*d-2
        c, ops, aa, bb = f.encode(base, [None]*n, [0], ng, set(range(len(rows))), True)
        c.add(aa[0][0])
        c.add(bb[0][1])
        stem = f'n{n}-d{d}-g{ng}'
        cnf, log, proof = (ROOT / (stem+suffix) for suffix in ('.cnf', '.log', '.lrat.gz'))
        c.save(cnf)
        print('SOLVE', stem, 'rows', len(rows), 'vars', c.n, 'clauses', len(c.cs), flush=True)
        with log.open('w') as output:
            proc = subprocess.run([f.SOLVER, '--unsat', '--lrat', '-t', '15', str(cnf), str(proof)], stdout=output, stderr=subprocess.STDOUT, preexec_fn=lambda: os.nice(15))
        status, gates, _ = f.b.extract(log, ops, aa, bb, [])
        record = {'n': n, 'required_degree': d, 'gates_bound': ng, 'status': status, 'exit': proc.returncode, 'elapsed': round(time.monotonic()-started, 3)}
        if status == 'sat':
            satisfying = []
            for x in range(1 << n):
                ws = [bool(x >> p & 1) for p in range(n)]
                for a, b, op in gates:
                    ws.append((ws[a] and ws[b]) if op else (ws[a] or ws[b]))
                if ws[-1]:
                    satisfying.append(x)
            assert satisfying and 0 not in satisfying
            degree = min(x.bit_count() for x in satisfying)
            mandatory = (1 << n)-1
            for x in satisfying:
                mandatory &= x
            count = mandatory.bit_count()
            assert degree >= d and count == 0 and ng < 2*degree-count-1
            record.update({'actual_degree': degree, 'mandatory_count': count, 'gates': gates, 'out': n+ng-1, 'satisfying_inputs': satisfying})
            (ROOT / (stem+'-counterexample.json')).write_text(json.dumps(record, indent=2)+'\n')
            print('FOUND_FULLCUBE_VERIFIED', json.dumps(record), flush=True)
        results.append(record)
        (ROOT / 'results.json').write_text(json.dumps(results, indent=2)+'\n')
        print('RESULT', json.dumps(record), flush=True)
        if status == 'sat':
            return


if __name__ == '__main__':
    main()
