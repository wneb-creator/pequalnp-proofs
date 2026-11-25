import argparse, importlib.util, json, random, subprocess, time
from pathlib import Path
BUDGET_SOURCE = Path('/tmp/oec/pequalnp-pilot-85/counterexample/compact_budget.py')
spec = importlib.util.spec_from_file_location('compact_budget_base', BUDGET_SOURCE)
budget = importlib.util.module_from_spec(spec)
spec.loader.exec_module(budget)
b = budget.b

def make_model(k, position, helper, limit, rows, ordered=False, side_lex=False, cone=False):
    middle = ['or', 'flip'] if helper == 'dual' else [helper]
    kinds = ['and'] * position + middle + ['and'] * (k - position)
    c = b.CNF()
    sides = []
    for j, kind in enumerate(kinds):
        sides.append([[c.var() for _ in range(b.N + j)]
                      for _ in range(2 if kind == 'and' else 0 if kind == 'flip' else 1)])
    output = [c.var() for _ in kinds]
    for ss in [ss for node in sides for ss in node] + [output]:
        c.add(*ss)
    for x, target in rows:
        ws = [bool(x >> i & 1) for i in range(b.N)]
        for kind, node in zip(kinds, sides):
            values = []
            for selectors in node:
                terms = []
                for sel, w in zip(selectors, ws):
                    if isinstance(w, bool):
                        if w:
                            terms.append(sel)
                    else:
                        terms.append(c.conj(sel, w))
                values.append(c.union(terms))
            if kind == 'and':
                ws.append(c.conj(*values))
            elif kind == 'or':
                ws.append(values[0])
            else:
                source = ws[-1] if kind == 'flip' else values[0]
                z = c.var()
                c.add(z, source)
                c.add(-z, -source)
                ws.append(z)
        final = c.union([c.conj(sel, w) for sel, w in zip(output, ws[b.N:])])
        c.add(final if target else -final)
    selectors = [v for node in sides for ss in node for v in ss] + output
    budget.at_most(c, selectors, limit)
    if side_lex:
        for kind, node in zip(kinds, sides):
            if kind == 'and':
                budget.lex_sides(c, *node)
    if ordered:
        for j in range(len(kinds) - 1):
            if kinds[j] != 'and' or kinds[j + 1] != 'and':
                continue
            for w in range(b.N + j):
                later = sides[j + 1][0][w:] + sides[j + 1][1][w:]
                for ss in sides[j]:
                    c.add(-ss[w], *later)
    if cone:
        for j in range(len(kinds)):
            if j + 1 < len(kinds) and kinds[j + 1] == 'flip':
                continue
            uses = [output[j]]
            for node in sides[j + 1:]:
                uses += [ss[b.N + j] for ss in node]
            c.add(*uses)
    return c, {'kinds': kinds, 'sides': sides, 'output': output}

def extract(schema, model):
    nodes = [[[i for i, sel in enumerate(ss) if sel in model] for ss in node]
             for node in schema['sides']]
    out = [i for i, sel in enumerate(schema['output']) if sel in model]
    return nodes, out

def phase_hints(c, schema, seed):
    """Complete deterministic auxiliary phases from a concrete selector seed.

    These are preferences only. A seed above the gate budget can violate the
    terminal budget clause; no phase becomes a clause or an assumption.
    """
    assert seed['kinds'] == schema['kinds']
    assert len(seed['nodes']) == len(schema['sides'])
    values = {}
    for ss, chosen in [(ss, chosen)
                       for node, selected in zip(schema['sides'], seed['nodes'])
                       for ss, chosen in zip(node, selected)]:
        assert all(0 <= i < len(ss) for i in chosen)
        for i, v in enumerate(ss):
            values[v] = i in chosen
    assert all(0 <= i < len(schema['output']) for i in seed['output'])
    for i, v in enumerate(schema['output']):
        values[v] = i in seed['output']
    passes = 0
    while True:
        assigned = len(values)
        for clause in c.clauses:
            if any(abs(v) in values and values[abs(v)] == (v > 0) for v in clause):
                continue
            missing = [v for v in clause if abs(v) not in values]
            if len(missing) == 1:
                v = missing[0]
                values[abs(v)] = v > 0
        passes += 1
        if len(values) == assigned:
            break
    assert len(values) == c.n, (len(values), c.n)
    violated = [i + 1 for i, clause in enumerate(c.clauses)
                if not any(values[abs(v)] == (v > 0) for v in clause)]
    return [v if values[v] else -v for v in range(1, c.n + 1)], {
        'assigned_variables': len(values), 'passes': passes,
        'violated_clause_indices': violated,
        'warning': 'Phase preferences only; no constraints or assumptions added'}

def root_circuit(kinds, nodes, output):
    root = []
    wires = list(range(b.N))
    def fold_or(ids):
        assert ids
        w = ids[0]
        for v in ids[1:]:
            root.append((1, w, v))
            w = b.N + len(root) - 1
        return w
    for kind, node in zip(kinds, nodes):
        vals = [fold_or([wires[i] for i in ss]) for ss in node]
        if kind == 'and':
            root.append((0, vals[0], vals[1]))
            out = b.N + len(root) - 1
        elif kind in ('not', 'flip'):
            source = wires[-1] if kind == 'flip' else vals[0]
            root.append((2, source, -1))
            out = b.N + len(root) - 1
        else:
            out = vals[0]
        wires.append(out)
    final = fold_or([wires[b.N + i] for i in output])
    return {'gates': root, 'output': final, 'size': len(root)}

def validate(root):
    errors = []
    for x in range(1 << b.N):
        ws = [bool(x >> i & 1) for i in range(b.N)]
        for op, a, d in root['gates']:
            ws.append(ws[a] and ws[d] if op == 0 else ws[a] or ws[d] if op == 1 else not ws[a])
        target = any(x >> a & 1 and x >> d & 1 for a, d in b.E)
        if ws[root['output']] != target:
            errors.append(x)
    return errors

def main():
    p = argparse.ArgumentParser()
    p.add_argument('--ands', type=int, default=7)
    p.add_argument('--position', type=int, default=3)
    p.add_argument('--helper', choices=['or', 'not', 'dual'], default='not')
    p.add_argument('--budget', type=int)
    p.add_argument('--seconds', type=int, default=600)
    p.add_argument('--rounds', type=int, default=20)
    p.add_argument('--total-seconds', type=int)
    p.add_argument('--samples')
    p.add_argument('--hint', help='A compact concrete seed; requires cadical-phase wrapper')
    p.add_argument('--out', required=True)
    p.add_argument('--solver', required=True)
    p.add_argument('--profile', choices=['default', 'sat', 'unsat'], default='default')
    p.add_argument('--ordered', action='store_true')
    p.add_argument('--side-lex', action='store_true')
    p.add_argument('--cone', action='store_true')
    p.add_argument('--prepare-only', action='store_true')
    args = p.parse_args()
    assert 0 <= args.position <= args.ands
    limit = args.budget if args.budget is not None else args.ands + (26 if args.helper == 'or' else 25)
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    (out / 'compact_hybrid-source.py').write_text(Path(__file__).read_text())
    (out / 'compact_budget-source.py').write_text(BUDGET_SOURCE.read_text())
    (out / 'andcount_sat-source.py').write_text(budget.BASE.read_text())
    maximal_false = [x for x in range(1 << b.N)
                     if all(not (x >> a & 1 and x >> d & 1) for a, d in b.E)
                     and all(x >> v & 1 or b.NEI[v] & x for v in range(b.N))]
    samples = set(maximal_false + [(1 << a) | (1 << d) for a, d in b.E])
    if args.helper != 'or':
        samples.update(x for x in range(1 << b.N) if x.bit_count() <= 2)
    if args.samples:
        extra = json.loads(Path(args.samples).read_text())
        assert isinstance(extra, list)
        for item in extra:
            x = item[0] if isinstance(item, list) else item
            assert isinstance(x, int) and 0 <= x < (1 << b.N)
            samples.add(x)
    rng = random.Random(9811)
    started = time.monotonic()
    for r in range(args.rounds):
        rows = [(x, any(x >> a & 1 and x >> d & 1 for a, d in b.E)) for x in sorted(samples)]
        c, schema = make_model(args.ands, args.position, args.helper, limit, rows,
                               args.ordered, args.side_lex, args.cone)
        cnf_path = out / f'round-{r:03d}.cnf'
        c.write(cnf_path)
        (out / f'round-{r:03d}-schema.json').write_text(json.dumps(schema))
        (out / f'round-{r:03d}-rows.json').write_text(json.dumps(rows))
        selectors = sum(len(ss) for node in schema['sides'] for ss in node) + len(schema['output'])
        print('round', r, 'rows', len(rows), 'selectors', selectors, 'budget', limit,
              'variables', c.n, 'clauses', len(c.clauses), flush=True)
        hint_path = None
        if args.hint:
            seed = json.loads(Path(args.hint).read_text())
            hints, hint_info = phase_hints(c, schema, seed)
            hint_path = out / f'round-{r:03d}-phases.txt'
            hint_path.write_text(' '.join(map(str, hints)) + '\n')
            (out / f'round-{r:03d}-phase-info.json').write_text(json.dumps(hint_info, indent=2))
            (out / 'phase-seed.json').write_text(json.dumps(seed, indent=2))
            print('hint variables', len(hints), 'violated clauses',
                  len(hint_info['violated_clause_indices']), flush=True)
        del c
        if args.prepare_only:
            print('Prepared; no solver launched', flush=True)
            return
        seconds = args.seconds
        if args.total_seconds is not None:
            remaining = int(args.total_seconds - (time.monotonic() - started))
            if remaining <= 0:
                print('Total time budget exhausted', flush=True)
                return
            seconds = min(seconds, remaining)
        log = out / f'round-{r:03d}.solver.log'
        command = [args.solver, '--' + args.profile, '-t', str(seconds), str(cnf_path)]
        if hint_path is not None:
            command += ['--phase-file', str(hint_path)]
        with log.open('w') as f:
            proc = subprocess.run(command, stdout=f, stderr=subprocess.STDOUT)
        print('solver exit', proc.returncode, 'elapsed', round(time.monotonic() - started, 2), flush=True)
        if proc.returncode != 10:
            print('UNSAT for this restricted template' if proc.returncode == 20 else 'UNKNOWN', flush=True)
            return
        text = log.read_text()
        model = {int(v) for line in text.splitlines() if line.startswith('v ')
                 for v in line[2:].split() if int(v) > 0}
        nodes, output = extract(schema, model)
        selected = sum(len(ss) for node in nodes for ss in node) + len(output)
        root = root_circuit(schema['kinds'], nodes, output)
        assert selected <= limit
        expected = selected - args.ands - (2 if args.helper == 'or' else 1)
        assert root['size'] == expected
        errors = validate(root)
        result = {'kinds': schema['kinds'], 'nodes': nodes, 'output': output,
                  'selected': selected, 'root_circuit': root, 'errors': errors}
        (out / f'round-{r:03d}-candidate.json').write_text(json.dumps(result, indent=2))
        print('actual gate count', root['size'], 'full truth-table errors', len(errors), flush=True)
        assert not set(errors) & samples, 'Candidate fails a constrained row'
        if not errors:
            if root['size'] <= 24:
                (out / 'FOUND.json').write_text(json.dumps(result, indent=2))
                print('FOUND <=24-gate circuit', flush=True)
            return
        assert args.helper != 'or', 'Monotone sample characterization error'
        samples.update(errors[:32])
        samples.update(rng.sample(errors, min(32, len(errors))))
    print('Round budget exhausted', flush=True)

if __name__ == '__main__':
    main()
