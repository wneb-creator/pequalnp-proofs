"""Cone and actual-fanin-order symmetry breaking for the variable circuit tail."""
import argparse, json, random, subprocess, time
from pathlib import Path
from search import N, TARGET, evaluate, make, decode, star_prefix


def add_normalization(cnf, schema, prefix_size, input_count=N):
    ops, lhs, rhs = schema
    base = input_count + prefix_size
    keys = []
    for j, (oo, aa, bb) in enumerate(zip(ops, lhs, rhs)):
        # Index0 is constantfalse (rank-1), indexw+1 is actual wirew.
        kk = [cnf.var() for _ in range(base + j + 1)]
        keys.append(kk)
        cnf.one(kk)
        for a, sa in enumerate(aa):
            key_a = 0 if a == base + j else a + 1
            cnf.add(-oo[2], -sa, kk[key_a])
            for op in [0, 1]:
                cnf.add(-oo[op], -bb[-1], -sa, kk[key_a])
        for b, sb in enumerate(bb[:-1]):
            for op in [0, 1]:
                cnf.add(-oo[op], -sb, kk[b + 1])
    for left, right in zip(keys, keys[1:]):
        for a, sa in enumerate(left):
            for b in range(a):
                cnf.add(-sa, -right[b])
    for j in range(len(ops) - 1):
        wire = base + j
        uses = []
        for k in range(j + 1, len(ops)):
            uses.extend([lhs[k][wire], rhs[k][wire]])
        cnf.add(*uses)
    return keys


def normalize(prefix, gates):
    # Prune nothing for the control; its entire variable tail is output-reachable.
    base = N + len(prefix)
    done = {-1: -1, **{i: i for i in range(base)}}
    pending = set(range(len(prefix), len(gates)))
    result = [x[:] for x in prefix]
    while pending:
        ready = []
        for j in pending:
            op, a, b = gates[j]
            if a in done and (op == 2 or b in done):
                av, bv = done[a], done[b] if op < 2 else -1
                ready.append((max(av, bv), j, op, av, bv))
        assert ready
        _, j, op, av, bv = min(ready)
        done[N + j] = N + len(result)
        result.append([op, av, bv])
        pending.remove(j)
    assert done[N + len(gates) - 1] == N + len(result) - 1
    keys = [max(a, b if op < 2 else -1) for op, a, b in result[len(prefix):]]
    assert keys == sorted(keys)
    assert not evaluate(result)
    return result


def run_case(scope, out, solver, seconds, control=False):
    prefix, baseline = star_prefix(scope['side'], scope['chosen'])
    size = 25 if control else 24
    samples = {x for x in range(1 << N) if not (TARGET >> x & 1) or x.bit_count() <= 2}
    rng = random.Random(981190)
    started = time.monotonic()
    result = {'scope': scope, 'gates': size}
    for round_id in range(12):
        remain = int(seconds - (time.monotonic() - started))
        if remain <= 0:
            result['status'] = 'TIME_BUDGET'
            break
        cnf, schema = make(prefix, sorted(samples), size - len(prefix))
        keys = add_normalization(cnf, schema, len(prefix))
        if control:
            control_gates = normalize(prefix, baseline)
            for j, (oo, aa, bb) in enumerate(zip(*schema), start=len(prefix)):
                op, a, b = control_gates[j]
                if a < 0:
                    a = N + j
                if b < 0 or op == 2:
                    b = N + j
                if op < 2 and a > b:
                    a, b = b, a
                cnf.add(oo[op])
                cnf.add(aa[a])
                cnf.add(bb[b])
        path = out / f'round-{round_id:02d}.cnf'
        cnf.write(path)
        (out / f'round-{round_id:02d}-schema.json').write_text(json.dumps({'gates': schema, 'keys': keys}))
        (out / f'round-{round_id:02d}-samples.json').write_text(json.dumps(sorted(samples)))
        command = [solver, '--default', '-t', str(remain), str(path)]
        (out / f'round-{round_id:02d}-command.json').write_text(json.dumps(command))
        log = out / f'round-{round_id:02d}.solver.log'
        with log.open('w') as f:
            p = subprocess.run(command, stdout=f, stderr=subprocess.STDOUT)
        result.update({'round': round_id, 'exit': p.returncode, 'variables': cnf.n, 'clauses': len(cnf.clauses)})
        if p.returncode == 20:
            result['status'] = 'UNSAT_NORMALIZED_LOCAL_MODEL'
            assert not control
            break
        if p.returncode != 10:
            result['status'] = 'UNKNOWN' if p.returncode == 0 else 'SOLVER_ERROR'
            break
        model = {int(v) for line in log.read_text().splitlines() if line.startswith('v ')
                 for v in line[2:].split() if int(v) > 0}
        gates = decode(prefix, schema, model)
        delta = evaluate(gates)
        errors = [x for x in range(1 << N) if delta >> x & 1]
        assert not any(x in samples for x in errors)
        candidate = {'gates': gates, 'gate_count': len(gates), 'errors': len(errors)}
        (out / f'round-{round_id:02d}-candidate.json').write_text(json.dumps(candidate))
        if not errors:
            (out / ('VALID25.json' if control else 'FOUND.json')).write_text(json.dumps(candidate))
            result['status'] = 'VALID25_CONTROL' if control else 'FOUND'
            break
        samples.update(errors[:32])
        samples.update(rng.sample(errors, min(64, len(errors))))
    else:
        result['status'] = 'ROUND_BUDGET'
    result.update({'elapsed': time.monotonic() - started, 'samples_final': len(samples)})
    (out / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
    return result


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--case', required=True)
    ap.add_argument('--out', required=True)
    ap.add_argument('--solver', required=True)
    ap.add_argument('--seconds', type=int, default=60)
    ap.add_argument('--valid25', action='store_true')
    a = ap.parse_args()
    out = Path(a.out)
    out.mkdir(exist_ok=True)
    scope = json.loads((Path(a.case) / 'scope.json').read_text())
    print(run_case(scope, out, a.solver, a.seconds, a.valid25), flush=True)


if __name__ == '__main__':
    main()
