import argparse, importlib.util, json, subprocess, time
from pathlib import Path
BASE = Path('/tmp/oec/pequalnp-pilot-85/lower_bound/andcount_sat.py')
spec = importlib.util.spec_from_file_location('andcount_model', BASE)
b = importlib.util.module_from_spec(spec)
spec.loader.exec_module(b)

def neg(v):
    return not v if isinstance(v, bool) else -v

def simple(c, *ls):
    if any(v is True for v in ls):
        return
    c.add(*[v for v in ls if v is not False])

def at_most(c, xs, k):
    prev = [True] + [False] * (k + 1)
    for i, x in enumerate(xs, 1):
        cur = [True]
        for t in range(1, k + 2):
            if t > i:
                cur.append(False)
                continue
            a, d = prev[t], prev[t - 1]
            z = c.var()
            cur.append(z)
            simple(c, neg(a), z)
            simple(c, -x, neg(d), z)
            simple(c, a, x, -z)
            simple(c, a, d, -z)
        prev = cur
    simple(c, neg(prev[k + 1]))

def lex_sides(c, aa, bb):
    eq = True
    for i, (a, d) in enumerate(zip(aa, bb)):
        simple(c, neg(eq), -a, d)
        if i + 1 == len(aa):
            break
        z = c.var()
        simple(c, -z, eq)
        c.add(-z, -a, d)
        c.add(-z, a, -d)
        simple(c, neg(eq), a, d, z)
        simple(c, neg(eq), -a, -d, z)
        eq = z

def make_model(k, budget, rows, ordered=False, side_lex=False, cone=False):
    c, schema = b.make(k, rows, strip=False)
    left, right, output = schema
    for ss in left + right + [output]:
        c.add(*ss)
    selectors = [v for ss in left + right + [output] for v in ss]
    at_most(c, selectors, budget)
    if side_lex:
        for aa, bb in zip(left, right):
            lex_sides(c, aa, bb)
    if ordered:
        for j in range(k - 1):
            for w in range(b.N + j):
                later = left[j + 1][w:] + right[j + 1][w:]
                c.add(-left[j][w], *later)
                c.add(-right[j][w], *later)
    if cone:
        for j in range(k):
            uses = [output[j]]
            for t in range(j + 1, k):
                uses += [left[t][b.N + j], right[t][b.N + j]]
            c.add(*uses)
    return c, schema

def extract(schema, model):
    left, right, out = schema
    gates = [([i for i, s in enumerate(aa) if s in model],
              [i for i, s in enumerate(bb) if s in model])
             for aa, bb in zip(left, right)]
    output = [j for j, s in enumerate(out) if s in model]
    return gates, output

def root_circuit(gates, output):
    root = []
    wires = list(range(b.N))
    def fold_or(ids):
        assert ids
        w = ids[0]
        for v in ids[1:]:
            root.append((1, w, v))
            w = b.N + len(root) - 1
        return w
    for aa, bb in gates:
        a = fold_or([wires[i] for i in aa])
        d = fold_or([wires[i] for i in bb])
        root.append((0, a, d))
        wires.append(b.N + len(root) - 1)
    out = fold_or([wires[b.N + j] for j in output])
    return {'gates': root, 'output': out, 'size': len(root)}

def validate(root):
    bad = []
    for x in range(1 << b.N):
        ws = [bool(x >> i & 1) for i in range(b.N)]
        for op, a, d in root['gates']:
            ws.append(ws[a] and ws[d] if op == 0 else ws[a] or ws[d])
        wanted = any(x >> a & 1 and x >> d & 1 for a, d in b.E)
        if ws[root['output']] != wanted:
            bad.append(x)
    return bad

def main():
    p = argparse.ArgumentParser()
    p.add_argument('--gates', type=int, default=7)
    p.add_argument('--budget', type=int, default=32)
    p.add_argument('--seconds', type=int, default=600)
    p.add_argument('--out', required=True)
    p.add_argument('--solver', required=True)
    p.add_argument('--profile', choices=['default', 'sat', 'unsat'], default='default')
    p.add_argument('--ordered', action='store_true')
    p.add_argument('--side-lex', action='store_true')
    p.add_argument('--cone', action='store_true')
    p.add_argument('--prepare-only', action='store_true')
    args = p.parse_args()
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    (out / 'compact_budget-source.py').write_text(Path(__file__).read_text())
    (out / 'andcount_sat-source.py').write_text(BASE.read_text())
    mis = [x for x in range(1 << b.N)
           if all(not (x >> a & 1 and x >> d & 1) for a, d in b.E)
           and all(x >> v & 1 or b.NEI[v] & x for v in range(b.N))]
    rows = [(x, False) for x in mis] + [((1 << a) | (1 << d), True) for a, d in b.E]
    c, schema = make_model(args.gates, args.budget, rows, args.ordered, args.side_lex, args.cone)
    c.write(out / 'model.cnf')
    (out / 'schema.json').write_text(json.dumps(schema))
    (out / 'rows.json').write_text(json.dumps(rows))
    selectors = sum(map(len, schema[0] + schema[1] + [schema[2]]))
    print('rows', len(rows), 'selectors', selectors, 'budget', args.budget,
          'variables', c.n, 'clauses', len(c.clauses), flush=True)
    del c
    if args.prepare_only:
        print('Prepared; no solver launched', flush=True)
        return
    started = time.monotonic()
    with (out / 'solver.log').open('w') as f:
        proc = subprocess.run([args.solver, '--' + args.profile, '-t', str(args.seconds), str(out / 'model.cnf')],
                              stdout=f, stderr=subprocess.STDOUT)
    print('solver exit', proc.returncode, 'seconds', round(time.monotonic() - started, 2), flush=True)
    if proc.returncode != 10:
        print('UNSAT for restricted unshared-OR model' if proc.returncode == 20 else 'UNKNOWN', flush=True)
        return
    text = (out / 'solver.log').read_text()
    model = {int(v) for line in text.splitlines() if line.startswith('v ')
             for v in line[2:].split() if int(v) > 0}
    gates, output = extract(schema, model)
    selected = sum(len(a) + len(d) for a, d in gates) + len(output)
    root = root_circuit(gates, output)
    assert root['size'] == selected - args.gates - 1
    assert selected <= args.budget
    bad = validate(root)
    result = {'abstract_gates': gates, 'abstract_output': output,
              'selected': selected, 'root_circuit': root, 'errors': bad}
    (out / 'candidate.json').write_text(json.dumps(result, indent=2))
    print('selected', selected, 'root gates', root['size'], 'full truth errors', len(bad), flush=True)
    assert not bad, 'Monotone sample characterization or encoder error'
    if root['size'] <= 24:
        (out / 'FOUND.json').write_text(json.dumps(result, indent=2))
        print('FOUND <=24-gate circuit', flush=True)

if __name__ == '__main__':
    main()
