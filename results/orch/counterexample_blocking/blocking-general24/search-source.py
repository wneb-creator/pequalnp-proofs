"""Exact local resynthesis, with frozen complementary stars evaluated explicitly."""
import argparse, hashlib, itertools, json, random, subprocess, time
from pathlib import Path
from synthesize_reference import CNF, E, MASK, N, TARGET, X, evaluate


def star_prefix(side, chosen):
    gates = []

    def gate(op, a, b):
        w = N + len(gates)
        gates.append([op, a, b])
        return w

    def star(v):
        ns = [b if a == v else a for a, b in E if a == v or b == v]
        r = ns[0]
        for t in ns[1:]:
            r = gate(1, r, t)
        return gate(0, v, r)

    outside = [v for v in range(7 * side, 7 * side + 7) if v not in chosen]
    outs = [star(v) for v in outside]
    g = outs[0]
    for t in outs[1:]:
        g = gate(1, g, t)
    frozen = [x[:] for x in gates]
    for v in chosen:
        t = star(v)
        g = gate(1, g, t)
    assert len(gates) == 25 and not evaluate(gates)
    return frozen, gates


def make(prefix, samples, tail_size):
    c = CNF()
    ops, lhs, rhs = [], [], []
    base = N + len(prefix)
    for j in range(tail_size):
        oo = [c.var() for _ in range(3)]
        aa = [c.var() for _ in range(base + j + 1)]
        bb = [c.var() for _ in range(base + j + 1)]
        ops.append(oo)
        lhs.append(aa)
        rhs.append(bb)
        c.one(oo)
        c.one(aa)
        c.one(bb)
        for a in range(len(aa)):
            for b in range(a):
                c.add(-oo[0], -aa[a], -bb[b])
                c.add(-oo[1], -aa[a], -bb[b])
        c.add(-oo[2], bb[-1])
    for sample in samples:
        ws = [bool(sample >> i & 1) for i in range(N)]
        for op, a, b in prefix:
            av = False if a < 0 else ws[a]
            bv = False if b < 0 else ws[b]
            ws.append(av and bv if op == 0 else av or bv if op == 1 else not av)
        for j in range(tail_size):
            a, b, z = c.var(), c.var(), c.var()
            for sel, w in zip(lhs[j], ws + [False]):
                c.mux(sel, a, w)
            for sel, w in zip(rhs[j], ws + [False]):
                c.mux(sel, b, w)
            o = ops[j]
            c.add(-o[0], -a, -b, z)
            c.add(-o[0], a, -z)
            c.add(-o[0], b, -z)
            c.add(-o[1], a, b, -z)
            c.add(-o[1], -a, z)
            c.add(-o[1], -b, z)
            c.add(-o[2], a, z)
            c.add(-o[2], -a, -z)
            ws.append(z)
        c.add(ws[-1] if TARGET >> sample & 1 else -ws[-1])
    return c, (ops, lhs, rhs)


def decode(prefix, schema, model):
    gates = [x[:] for x in prefix]
    for oo, aa, bb in zip(*schema):
        op = next(i for i, v in enumerate(oo) if v in model)
        a = next(i for i, v in enumerate(aa) if v in model)
        b = next(i for i, v in enumerate(bb) if v in model)
        if a == N + len(gates):
            a = -1
        if b == N + len(gates):
            b = -1
        gates.append([op, a, b])
    return gates


def run_case(case, prefix, solver, seconds, rng):
    samples = {x for x in range(1 << N) if not (TARGET >> x & 1) or x.bit_count() <= 2}
    started = time.monotonic()
    result = {'frozen': len(prefix), 'variable': 24 - len(prefix), 'samples_initial': len(samples)}
    for round_id in range(12):
        remain = int(seconds - (time.monotonic() - started))
        if remain <= 0:
            result['status'] = 'TIME_BUDGET'
            break
        cnf, schema = make(prefix, sorted(samples), 24 - len(prefix))
        cnf_path = case / f'round-{round_id:02d}.cnf'
        cnf.write(cnf_path)
        (case / f'round-{round_id:02d}-schema.json').write_text(json.dumps(schema))
        (case / f'round-{round_id:02d}-samples.json').write_text(json.dumps(sorted(samples)))
        result.update({'round': round_id, 'vars': cnf.n, 'clauses': len(cnf.clauses)})
        log = case / f'round-{round_id:02d}.solver.log'
        command = [solver, '--default', '-t', str(remain), str(cnf_path)]
        (case / f'round-{round_id:02d}-command.json').write_text(json.dumps(command))
        with log.open('w') as f:
            p = subprocess.run(command, stdout=f, stderr=subprocess.STDOUT)
        result['solver_exit'] = p.returncode
        if p.returncode == 20:
            result['status'] = 'UNSAT_LOCAL_MODEL'
            break
        if p.returncode != 10:
            result['status'] = 'UNKNOWN' if p.returncode == 0 else 'SOLVER_ERROR'
            break
        model = {int(v) for line in log.read_text().splitlines() if line.startswith('v ')
                 for v in line[2:].split() if int(v) > 0}
        gates = decode(prefix, schema, model)
        delta = evaluate(gates)
        errors = [x for x in range(1 << N) if delta >> x & 1]
        assert not any(x in samples for x in errors), 'Encoding/sample validation failed'
        candidate = {'gates': gates, 'errors': len(errors), 'output': 37, 'gate_count': 24}
        (case / f'round-{round_id:02d}-candidate.json').write_text(json.dumps(candidate))
        if not errors:
            (case / 'FOUND.json').write_text(json.dumps(candidate))
            result['status'] = 'FOUND'
            break
        samples.update(errors[:32])
        samples.update(rng.sample(errors, min(64, len(errors))))
    else:
        result['status'] = 'ROUND_BUDGET'
    result.update({'elapsed': time.monotonic() - started, 'samples_final': len(samples)})
    return result


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--solver', required=True)
    ap.add_argument('--out', required=True)
    ap.add_argument('--sizes', default='2')
    ap.add_argument('--seconds', type=int, default=15)
    ap.add_argument('--total-seconds', type=int, default=1200)
    ap.add_argument('--seed', type=int, default=981188)
    a = ap.parse_args()
    out = Path(a.out)
    out.mkdir(exist_ok=True)
    rng = random.Random(a.seed)
    jobs = [(side, chosen) for size in map(int, a.sizes.split(',')) for side in range(2)
            for chosen in itertools.combinations(range(7 * side, 7 * side + 7), size)]
    rng.shuffle(jobs)
    summaries = []
    started = time.monotonic()
    for i, (side, chosen) in enumerate(jobs):
        if time.monotonic() - started > a.total_seconds or (out / 'STOP').exists():
            break
        case = out / f'case-{i:03d}'
        case.mkdir(exist_ok=True)
        prefix, baseline = star_prefix(side, chosen)
        (case / 'scope.json').write_text(json.dumps({'side': side, 'chosen': chosen, 'prefix': prefix}))
        (case / 'baseline25.json').write_text(json.dumps({'gates': baseline, 'errors': 0}))
        print('START', i, 'side', side, 'chosen', chosen, 'tail', 24 - len(prefix), flush=True)
        result = run_case(case, prefix, a.solver, a.seconds, rng)
        result.update({'case': i, 'side': side, 'chosen': chosen})
        (case / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
        summaries.append(result)
        (out / 'summary.json').write_text(json.dumps(summaries, indent=2) + '\n')
        print('FINISH', result, flush=True)
        if result['status'] in {'FOUND', 'SOLVER_ERROR'}:
            break
    print('COMPLETE', len(summaries), 'elapsed', time.monotonic() - started, flush=True)


if __name__ == '__main__':
    main()
