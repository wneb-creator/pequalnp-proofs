import argparse, gc, hashlib, importlib.util, itertools, json, pathlib, random, shutil, signal, subprocess, time

HERE = pathlib.Path('/tmp/oec/pequalnp-pilot-21/search')
spec = importlib.util.spec_from_file_location('symbolicbase', HERE / 'cegis-symbolic.py')
s = importlib.util.module_from_spec(spec)
spec.loader.exec_module(s)
ROOT = HERE / 'symbolic-five'
ROOT.mkdir(exist_ok=True)
GOALS = [2, 3, 6, 8, 9]


def reachability(c, aa, bb, meta, goals):
    """Exact syntactic input reachability, independent of gate operation."""
    rs = [[c.var() for _ in range(13)] for _ in aa]
    for j in range(len(aa)):
        children = [[c.var() for _ in range(13)] for _ in range(2)]
        for sels, dests in zip((aa[j], bb[j]), children):
            for k, sel in enumerate(sels):
                for p, dest in enumerate(dests):
                    if k < len(meta):
                        present = p == k if k < 13 else p in meta[k][1]
                        c.add(-sel, dest if present else -dest)
                    else:
                        src = rs[k-len(meta)][p]
                        c.add(-sel, -src, dest)
                        c.add(-sel, src, -dest)
        for p, v in enumerate(rs[j]):
            a, b = children[0][p], children[1][p]
            c.add(-a, v)
            c.add(-b, v)
            c.add(a, b, -v)
    for goal, r in zip(goals, rs[-len(goals):]):
        for p in s.LINES[goal]:
            c.add(r[p])
    return rs


def live_sinks(c, aa, bb, base_count, output_count):
    internal_count = len(aa)-output_count
    first_output = base_count+internal_count
    for a, b in zip(aa, bb):
        for selector in a[first_output:]+b[first_output:]:
            c.add(-selector)
    for j in range(internal_count):
        source = base_count+j
        c.add(*(selector for a, b in zip(aa[j+1:], bb[j+1:]) for selector in (a[source], b[source])))


def lex_internal(c, ops, aa, bb, output_count):
    """Refine existing B order to weak (B,A,op) order on internal gates."""
    for j in range(len(aa)-output_count-1):
        same_b = c.var()
        for left, right in zip(bb[j], bb[j+1]):
            c.add(-left, -right, same_b)
        prefixes = [c.var() for _ in aa[j+1]]
        for k, sel in enumerate(aa[j+1]):
            c.add(-sel, prefixes[k])
            if k:
                c.add(-prefixes[k-1], prefixes[k])
        for k, left in enumerate(aa[j]):
            if k:
                c.add(-same_b, -left, -prefixes[k-1])
            c.add(-same_b, -left, -aa[j+1][k], -ops[j], ops[j+1])


def offband_rows(c, ops, aa, bb, dual=False, normal_dual=False):
    """Audited redundant boundary rows; returns original-orientation values."""
    assert len(aa[0]) == 13 and len(ops) == 38
    masks = [sum(1 << p for p in line) for line in s.LINES]
    specifications = {}
    for w, mask in enumerate(masks):
        specifications[8191 ^ mask] = {other: True for other in range(13) if other != w}
        if normal_dual:
            specifications[8191 ^ mask][w] = False
    for w in range(13):
        for v in range(w+1, 13):
            x = 8191 ^ (masks[w] | masks[v])
            assert x not in specifications
            specifications[x] = {w: False, v: False}
    for p in range(13):
        specifications[1 << p] = {w: False for w in range(13) if p not in s.LINES[w]}
    assert len(specifications) == 104
    outputs = {}
    for original_x, known in sorted(specifications.items()):
        x = original_x ^ 8191 if dual else original_x
        vs = [c.var() for _ in ops]
        for j, op in enumerate(ops):
            a, b = c.var(), c.var()
            v = vs[j]
            for selectors, dest in ((aa[j], a), (bb[j], b)):
                for k, sel in enumerate(selectors):
                    if k < 13:
                        c.add(-sel, dest if x >> k & 1 else -dest)
                    else:
                        src = vs[k-13]
                        c.add(-sel, -src, dest)
                        c.add(-sel, src, -dest)
            c.add(-op, -a, -b, v)
            c.add(-op, a, -v)
            c.add(-op, b, -v)
            c.add(op, a, b, -v)
            c.add(op, -a, v)
            c.add(op, -b, v)
        original_values = [-v if dual else v for v in vs[25:]]
        outputs[original_x] = original_values
        for w, value in known.items():
            c.add(original_values[w] if value else -original_values[w])
    return {
        'own_complement': [outputs[8191 ^ masks[w]][w] for w in range(13)],
        'singleton': {p: outputs[1 << p] for p in range(13)},
        'row_count': len(specifications),
    }


def nonordinary_lower_bound(c, values, minimum=3):
    exotic = []
    for w in range(13):
        bad = [values['own_complement'][w]] + [-values['singleton'][p][w] for p in s.LINES[w]]
        e = c.var()
        for literal in bad:
            c.add(-literal, e)
        c.add(-e, *bad)
        exotic.append(e)
    assert 1 <= minimum <= len(exotic)
    for excluded in itertools.combinations(exotic, minimum-1):
        c.add(*(other for other in exotic if other not in excluded))
    return exotic


def nonordinary_support(c, exotic, output_supports):
    assert len(exotic) == len(output_supports) == 13
    for e, support in zip(exotic, output_supports):
        assert len(support) == 13
        for excluded in itertools.combinations(range(13), 7):
            c.add(-e, *(support[p] for p in range(13) if p not in excluded))


def initial_rows():
    approximation = json.loads((HERE / 'repair-best-approximation.json').read_text())
    rows = set()
    for r, x in enumerate(s.ROWS):
        y = 8191 ^ x
        ws = [bool(y >> p & 1) for p in range(13)]
        for a, b, op in approximation['gates']:
            ws.append((ws[a] and ws[b]) if op else (ws[a] or ws[b]))
        if any(ws[approximation['out'][w]] != all(y >> p & 1 for p in s.LINES[w]) for w in GOALS):
            rows.add(r)
        if x.bit_count() == 8 and any(not(s.TARGETS[w] >> r & 1) for w in GOALS):
            rows.add(r)
    rows.update(random.Random(10245).sample(range(len(s.ROWS)), 50))
    return rows


def digest(p):
    h = hashlib.sha256()
    with p.open('rb') as src:
        for chunk in iter(lambda: src.read(1048576), b''):
            h.update(chunk)
    return h.hexdigest()


def validate(candidate):
    assert len(candidate['gates']) == 38
    assert len(candidate['out']) == 13
    for j, (a, b, op) in enumerate(candidate['gates']):
        assert 0 <= a < 13+j and 0 <= b < 13+j
        assert isinstance(op, bool)
    for x in s.ROWS:
        ws = [bool(x >> p & 1) for p in range(13)]
        for a, b, op in candidate['gates']:
            ws.append((ws[a] and ws[b]) if op else (ws[a] or ws[b]))
        assert all(ws[candidate['out'][w]] == any(x >> p & 1 for p in s.LINES[w]) for w in range(13))


def main():
    ap = argparse.ArgumentParser(description='Continuous symbolic five-output search with all15 direct trees for each fixed output.')
    ap.add_argument('--seconds', type=int, default=1800)
    ap.add_argument('--prepare-only', action='store_true')
    args = ap.parse_args()
    started = time.monotonic()
    deadline = started + args.seconds
    samples = initial_rows()
    base, meta, index = s.bases(GOALS)
    ng = 14
    proof = True
    rng = random.Random(1024538)
    for it in range(100):
        remaining = int(deadline-time.monotonic())
        if remaining <= 0:
            break
        c, ops, aa, bb = s.encode(base, meta, GOALS, ng, samples)
        c.add(*ops)
        for op in ops:
            c.add(*(other for other in ops if other != op))
        reachability(c, aa, bb, meta, GOALS)
        live_sinks(c, aa, bb, len(base), len(GOALS))
        lex_internal(c, ops, aa, bb, len(GOALS))
        stem = f'continuous-{it:03d}'
        cnf, log, lrat = (ROOT / (stem+ext) for ext in ('.cnf', '.log', '.lrat.gz'))
        c.save(cnf)
        (ROOT / (stem+'-rows.json')).write_text(json.dumps(sorted(samples))+'\n')
        print('SOLVE', it, 'goals', GOALS, 'rows', len(samples), 'vars', c.n, 'clauses', len(c.cs), 'proof', proof, 'budget', remaining, flush=True)
        del c
        gc.collect()
        if args.prepare_only:
            print('PREPARED_ONLY', flush=True)
            return
        argv = [s.SOLVER, '--unsat', '-t', str(remaining), str(cnf)]
        if proof:
            argv = [s.SOLVER, '--unsat', '--lrat', '-t', str(remaining), str(cnf), str(lrat)]
        diskstop = False
        interrupted = None
        lastnote = 0
        with log.open('w') as output:
            proc = subprocess.Popen(argv, stdout=output, stderr=subprocess.STDOUT)
            while proc.poll() is None:
                now = time.monotonic()
                free = shutil.disk_usage(ROOT).free
                if free < 6.5*2**30 and interrupted is None:
                    diskstop = True
                    interrupted = now
                    proc.send_signal(signal.SIGINT)
                    print('DISK_FLOOR_INTERRUPT', 'freeGiB', round(free/2**30, 2), flush=True)
                if now >= deadline and interrupted is None:
                    interrupted = now
                    proc.send_signal(signal.SIGINT)
                    print('BUDGET_INTERRUPT', flush=True)
                if interrupted is not None and now-interrupted > 30 and proc.poll() is None:
                    proc.terminate()
                if now-lastnote >= 60:
                    print('RUNNING', 'elapsed', round(now-started), 'freeGiB', round(free/2**30, 2), 'proofMiB', round(lrat.stat().st_size/2**20, 1) if lrat.exists() else 0, flush=True)
                    lastnote = now
                time.sleep(5)
            code = proc.wait()
        status, gates, _ = s.b.extract(log, ops, aa, bb, [])
        print('RESULT', status, 'exit', code, 'elapsed', round(time.monotonic()-started), flush=True)
        if status == 'unsat':
            record = {'status': 'UNSAT_LOCAL_ENCODING', 'goals': GOALS, 'fixed_direct_output_count': 8, 'residual_gate_count': 14, 'cnf': str(cnf), 'cnf_sha256': digest(cnf), 'proof': str(lrat) if proof else None, 'rows': len(samples)}
            (ROOT / 'unsat.json').write_text(json.dumps(record, indent=2)+'\n')
            print('UNSAT_LOCAL_ENCODING', flush=True)
            return
        if status == 'sat':
            vals = list(base)
            for a, b, op in gates:
                vals.append(vals[a] & vals[b] if op else vals[a] | vals[b])
            outs = list(range(ng-len(GOALS), ng))
            bad = []
            for goal, o in zip(GOALS, outs):
                diff = vals[len(base)+o] ^ s.TARGETS[goal]
                bad.append([r for r in range(len(s.ROWS)) if diff >> r & 1])
            print('ERRORS', [len(rows) for rows in bad], flush=True)
            if not any(bad):
                candidate = s.reconstruct(meta, index, GOALS, gates, outs)
                validate(candidate)
                (ROOT / 'counterexample.json').write_text(json.dumps(candidate, indent=2)+'\n')
                print('FOUND_SCALAR_VERIFIED_ALL3003', flush=True)
                return
            for rows in bad:
                rng.shuffle(rows)
                samples.update(rows[:32])
        if diskstop and lrat.exists():
            record = {'status': 'incomplete_trace_removed_for_disk_floor', 'path': str(lrat), 'bytes': lrat.stat().st_size, 'sha256': digest(lrat)}
            (ROOT / (stem+'-removed-proof.json')).write_text(json.dumps(record, indent=2)+'\n')
            lrat.unlink()
            proof = False
            print('SWITCHING_TO_WITNESS_SEARCH_WITHOUT_PROOF', flush=True)
        if status != 'sat' and not diskstop:
            break
    print('FINISHED elapsed', round(time.monotonic()-started), flush=True)


if __name__ == '__main__':
    main()
