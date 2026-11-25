import argparse, hashlib, itertools, json, subprocess, time
from datetime import datetime, timezone
from pathlib import Path

P = argparse.ArgumentParser()
P.add_argument('--gates', type=int, default=18)
P.add_argument('--max-nots', type=int, default=0)
P.add_argument('--seconds', type=int, default=120)
P.add_argument('--first')
P.add_argument('--pin')
P.add_argument('--mutable')
P.add_argument('--allow-unused', action='store_true')
P.add_argument('--require-free-use', action='store_true')
P.add_argument('--full-rows', action='store_true')
P.add_argument('--fresh', action='store_true')
P.add_argument('--sat-preset', action='store_true')
P.add_argument('--seed', type=int, default=0)
P.add_argument('--once-input', type=int)
P.add_argument('--rail-readers', action='store_true')
P.add_argument('--primary-minimal', action='store_true')
P.add_argument('--tag', default='free-not')
args = P.parse_args()
root = Path('/tmp/oec/pequalnp-pilot-103/orch1884')
solver = Path('/tmp/oec/pequalnp-pilot-103/setup/lean-4.36.0-linux/bin/cadical')
data = json.loads((root / 'data.json').read_text())
E = data['edges']
N = args.gates
n, base = 10, 11
assert 0 <= args.max_nots <= N

def target(x):
    return any(x >> a & 1 and x >> b & 1 for a, b in E)

def input_bit(x, src):
    return bool(x >> src & 1) if src < n else not bool(x & 1)

class CNF:
    def __init__(self):
        self.nv, self.cs = 0, []
    def var(self):
        self.nv += 1
        return self.nv
    def clause(self, *xs):
        self.cs.append(tuple(xs))
    def one(self, xs):
        self.clause(*xs)
        for a, b in itertools.combinations(xs, 2):
            self.clause(-a, -b)
    def write(self, path):
        with path.open('w') as f:
            f.write(f'p cnf {self.nv} {len(self.cs)}\n')
            for clause in self.cs:
                f.write(' '.join(map(str, clause)) + ' 0\n')

fixed_inputs = {0}
exact_cofactors = args.max_nots == 0
if args.first and args.max_nots == 1:
    first_op, first_a, _ = map(int, args.first.split(','))
    if first_op == 2 and first_a < base:
        fixed_inputs.add(first_a if first_a < n else 0)
        exact_cofactors = True
seen = set(range(1024)) if args.full_rows else set(data['rows'])
if exact_cofactors and not args.full_rows:
    seen = {x for x in range(1024) if
            (target(x) and all(not target(x ^ (1 << i)) for i in range(n)
                               if i not in fixed_inputs and x >> i & 1)) or
            (not target(x) and all(target(x | (1 << i)) for i in range(n)
                                  if i not in fixed_inputs and not x >> i & 1))}
elif args.max_nots:
    seen.update(x for x in range(1024) if x.bit_count() <= 2 or x.bit_count() >= 9)
assert not args.fresh or exact_cofactors or args.full_rows
started = datetime.now(timezone.utc).isoformat()
start = time.monotonic()
deadline = start + args.seconds
records = []
print('START', started, vars(args), flush=True)
for stage in range(30):
    c = CNF()
    A, B, O = [], [], []
    for i in range(N):
        A.append([c.var() for _ in range(base + i)])
        B.append([c.var() for _ in range(base + i)])
        O.append([c.var() for _ in range(3)])
        c.one(A[i]); c.one(B[i]); c.one(O[i])
        for a in range(base + i):
            for b in range(a):
                c.clause(-A[i][a], -B[i][b])
        for a in range(base + i):
            c.clause(-O[i][2], -A[i][a], B[i][a])
            c.clause(-O[i][2], A[i][a], -B[i][a])
    for ns in itertools.combinations([o[2] for o in O], args.max_nots + 1):
        c.clause(*(-v for v in ns))
    if not args.allow_unused:
        for i in range(N - 1):
            c.clause(*(v for j in range(i + 1, N) for v in (A[j][base + i], B[j][base + i])))
    for src in range(1, n):
        c.clause(*(v for j in range(N) for v in (A[j][src], B[j][src])))
    if args.require_free_use:
        c.clause(*(v for j in range(N) for v in (A[j][10], B[j][10])))
        if args.max_nots == 0:
            c.clause(*(v for j in range(N) for v in (A[j][0], B[j][0])))
    if args.once_input is not None:
        assert args.max_nots == 0 and 0 <= args.once_input < n
        c.one([v for j in range(N) for v in (A[j][args.once_input], B[j][args.once_input])])
    if args.rail_readers:
        assert args.max_nots == 0
        for src, op in [(0,1),(10,0)]:
            readers=[v for j in range(N) for v in (A[j][src],B[j][src])]
            c.one(readers)
            for j in range(N):
                c.clause(-A[j][src],O[j][op]);c.clause(-B[j][src],O[j][op])
    if args.first:
        op, a, b = map(int, args.first.split(','))
        if op == 2:
            b = a
        a, b = sorted((a, b))
        c.clause(O[0][op]); c.clause(A[0][a]); c.clause(B[0][b])
    if args.pin:
        pin = json.loads(Path(args.pin).read_text())
        if isinstance(pin, dict):
            pin = pin['gates']
        assert len(pin) == N
        mutable = set(map(int, args.mutable.split(','))) if args.mutable else set()
        for i, (op, a, b) in enumerate(pin):
            if i in mutable:
                continue
            if op == 2:
                b = a
            a, b = sorted((a, b))
            assert op in range(3) and 0 <= a <= b < base + i
            c.clause(O[i][op]); c.clause(A[i][a]); c.clause(B[i][b])
    vectors = [[] for _ in range(N)]
    for x in sorted(seen):
        values = []
        for i in range(N):
            u, v, w = c.var(), c.var(), c.var()
            for src in range(base + i):
                for selectors, dest in ((A[i], u), (B[i], v)):
                    if src < base:
                        c.clause(-selectors[src], dest if input_bit(x, src) else -dest)
                    else:
                        r = values[src - base]
                        c.clause(-selectors[src], -dest, r)
                        c.clause(-selectors[src], dest, -r)
            oa, oo, on = O[i]
            c.clause(-oa, -u, -v, w); c.clause(-oa, u, -w); c.clause(-oa, v, -w)
            c.clause(-oo, u, v, -w); c.clause(-oo, -u, w); c.clause(-oo, -v, w)
            c.clause(-on, u, w); c.clause(-on, -u, -w)
            values.append(w)
            vectors[i].append(w)
        c.clause(values[-1] if target(x) else -values[-1])
    if args.fresh:
        ordered_rows = sorted(seen)
        for i, values in enumerate(vectors):
            c.clause(*values)
            c.clause(*(-v for v in values))
            for src in range(base):
                c.clause(*(v if not input_bit(x, src) else -v
                           for x, v in zip(ordered_rows, values)))
            for j in range(i):
                different = []
                for u, v in zip(vectors[j], values):
                    d = c.var()
                    different.append(d)
                    c.clause(-d, u, v); c.clause(-d, -u, -v)
                    c.clause(d, u, -v); c.clause(d, -u, v)
                c.clause(*different)
    if args.primary_minimal:
        assert args.max_nots == 0
        ordered_rows = sorted(seen)
        for values in vectors:
            for src in range(base):
                differences=[v if not input_bit(x,src) else -v
                             for x,v in zip(ordered_rows,values) if target(x)]
                increases=[-v for x,v in zip(ordered_rows,values)
                           if not target(x) and input_bit(x,src)]
                c.clause(*(differences+increases))
    cnf = root / f'{args.tag}-stage{stage}.cnf'
    c.write(cnf)
    stdout = root / f'{args.tag}-stage{stage}.stdout'
    stderr = root / f'{args.tag}-stage{stage}.stderr'
    remaining = max(1, int(deadline - time.monotonic()))
    if time.monotonic() >= deadline:
        break
    record = {'stage': stage, 'rows': len(seen), 'variables': c.nv, 'clauses': len(c.cs),
              'cnf_sha256': hashlib.sha256(cnf.read_bytes()).hexdigest(), 'solver_seconds': remaining}
    print('STAGE', json.dumps(record, sort_keys=True), flush=True)
    solver_args = [str(solver), '-t', str(remaining), '--seed=' + str(args.seed)]
    if args.sat_preset:
        solver_args.append('--sat')
    solver_args.append(str(cnf))
    record['solver_arguments'] = solver_args[1:]
    with stdout.open('w') as out, stderr.open('w') as err:
        try:
            run = subprocess.run(solver_args,
                                 stdout=out, stderr=err, timeout=remaining + 10)
            record['exit'] = run.returncode
        except subprocess.TimeoutExpired:
            record['exit'] = 'external timeout'
    text = stdout.read_text()
    status = 'SAT' if 's SATISFIABLE' in text else 'UNSAT' if 's UNSATISFIABLE' in text else 'UNKNOWN'
    record['status'] = status
    records.append(record)
    print('RESULT', json.dumps(record, sort_keys=True), flush=True)
    if status != 'SAT':
        break
    pos = {int(v) for line in text.splitlines() if line.startswith('v ')
           for v in line.split()[1:] if int(v) > 0}
    gates = [(next(j for j, v in enumerate(O[i]) if v in pos),
              next(j for j, v in enumerate(A[i]) if v in pos),
              next(j for j, v in enumerate(B[i]) if v in pos)) for i in range(N)]
    def ev(x):
        wires = [input_bit(x, j) for j in range(base)]
        for op, a, b in gates:
            wires.append((wires[a] and wires[b]) if op == 0 else
                         (wires[a] or wires[b]) if op == 1 else not wires[a])
        return wires[-1]
    bad = [x for x in range(1024) if ev(x) != target(x)]
    record['full_rows_checked'] = 1024
    record['bad_rows'] = bad
    record['candidate'] = gates
    print('CANDIDATE', json.dumps(gates), 'BAD_ROWS', len(bad), flush=True)
    if not bad:
        witness = {'inputs': 10, 'free_input': 'not x0', 'gate_base': 11,
                   'output': 11 + N - 1, 'gates': gates}
        (root / f'{args.tag}-witness.json').write_text(json.dumps(witness, indent=2) + '\n')
        print('WITNESS', json.dumps(witness), flush=True)
        break
    if exact_cofactors:
        raise AssertionError('Exact cofactor extrema specification was insufficient')
    new = []
    for wt in range(11):
        for truth in (False, True):
            new.extend([x for x in bad if x.bit_count() == wt and target(x) == truth][:6])
    seen.update(new)
    print('ADDED_ROWS', json.dumps(new), flush=True)
result = {'started_at': started, 'finished_at': datetime.now(timezone.utc).isoformat(),
          'elapsed_seconds': time.monotonic() - start, 'arguments': vars(args), 'stages': records,
          'strict_earlier_wires': True, 'free_not_input': 10, 'constant_sources': False,
          'exact_cofactor_specification': exact_cofactors,
          'fixed_inputs_for_cofactor_specification': sorted(fixed_inputs),
          'solver_results_are_not_lean_proofs': True}
(root / f'{args.tag}-result.json').write_text(json.dumps(result, indent=2) + '\n')
print('FINISHED', json.dumps(result), flush=True)
