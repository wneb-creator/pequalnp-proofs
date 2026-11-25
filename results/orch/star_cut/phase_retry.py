"""Resynthesize frozen-star cuts using the nearest 24-gate star as SAT phases."""
import argparse, json, random, subprocess, time
from pathlib import Path
from search import N, TARGET, evaluate, make, decode, star_prefix


def remove_gate(gs, index, side):
    replacement = gs[index][1 + side]
    assert 0 <= replacement < N + index
    def wire(w):
        if w == N + index:
            w = replacement
        return w - 1 if w > N + index else w
    return [[op, wire(a), wire(b)] for j, (op, a, b) in enumerate(gs) if j != index]


def phases(prefix, schema, gates, samples, nvars):
    result = []
    for j, (oo, aa, bb) in enumerate(zip(*schema), start=len(prefix)):
        op, a, b = gates[j]
        if a < 0:
            a = N + j
        if b < 0 or op == 2:
            b = N + j
        if op < 2 and a > b:
            a, b = b, a
        for vs, chosen in [(oo, op), (aa, a), (bb, b)]:
            result.extend(v if i == chosen else -v for i, v in enumerate(vs))
    pos = nvars - 3 * (len(gates) - len(prefix)) * len(samples)
    for sample in samples:
        ws = [bool(sample >> i & 1) for i in range(N)]
        for j, (op, a, b) in enumerate(gates):
            av = False if a < 0 else ws[a]
            bv = False if b < 0 or op == 2 else ws[b]
            z = av and bv if op == 0 else av or bv if op == 1 else not av
            if j >= len(prefix):
                ia = N + j if a < 0 else a
                ib = N + j if b < 0 else b
                if op < 2 and ia > ib:
                    av, bv = bv, av
                for v in [av, bv, z]:
                    pos += 1
                    result.append(pos if v else -pos)
            ws.append(z)
    assert pos == nvars
    assert len(result) == nvars and len({abs(v) for v in result}) == nvars
    return result


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--case', required=True)
    ap.add_argument('--out', required=True)
    ap.add_argument('--solver', required=True)
    ap.add_argument('--seconds', type=int, default=60)
    ap.add_argument('--delete', type=int, default=0)
    ap.add_argument('--bypass', type=int, choices=[0, 1], default=0)
    ap.add_argument('--valid25', action='store_true')
    a = ap.parse_args()
    case = Path(a.case)
    out = Path(a.out)
    out.mkdir(exist_ok=True)
    scope = json.loads((case / 'scope.json').read_text())
    prefix, baseline = star_prefix(scope['side'], scope['chosen'])
    gates = baseline if a.valid25 else remove_gate(baseline, len(prefix) + a.delete, a.bypass)
    tail_size = len(gates) - len(prefix)
    assert gates[:len(prefix)] == prefix
    samples = {x for x in range(1 << N) if not (TARGET >> x & 1) or x.bit_count() <= 2}
    rng = random.Random(981189)
    started = time.monotonic()
    result = {'scope': scope, 'gates': len(gates)}
    for round_id in range(12):
        remain = int(a.seconds - (time.monotonic() - started))
        if remain <= 0:
            result['status'] = 'TIME_BUDGET'
            break
        cnf, schema = make(prefix, sorted(samples), tail_size)
        path = out / f'round-{round_id:02d}.cnf'
        cnf.write(path)
        hp = out / f'round-{round_id:02d}-phases.txt'
        hp.write_text(' '.join(map(str, phases(prefix, schema, gates, sorted(samples), cnf.n))) + '\n')
        (out / f'round-{round_id:02d}-schema.json').write_text(json.dumps(schema))
        (out / f'round-{round_id:02d}-samples.json').write_text(json.dumps(sorted(samples)))
        command = [a.solver, '--default', '-t', str(remain), '--phase-file', str(hp), str(path)]
        (out / f'round-{round_id:02d}-command.json').write_text(json.dumps(command))
        log = out / f'round-{round_id:02d}.solver.log'
        with log.open('w') as f:
            p = subprocess.run(command, stdout=f, stderr=subprocess.STDOUT)
        result.update({'round': round_id, 'solver_exit': p.returncode, 'variables': cnf.n, 'clauses': len(cnf.clauses)})
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
        assert not any(x in samples for x in errors)
        candidate = {'gates': gates, 'gate_count': len(gates), 'errors': len(errors)}
        (out / f'round-{round_id:02d}-candidate.json').write_text(json.dumps(candidate))
        print('round', round_id, 'errors', len(errors), flush=True)
        if not errors:
            (out / ('VALID25.json' if a.valid25 else 'FOUND.json')).write_text(json.dumps(candidate))
            result['status'] = 'VALID25_CONTROL' if a.valid25 else 'FOUND'
            break
        samples.update(errors[:32])
        samples.update(rng.sample(errors, min(64, len(errors))))
    else:
        result['status'] = 'ROUND_BUDGET'
    result.update({'elapsed': time.monotonic() - started, 'samples_final': len(samples)})
    (out / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
    print(result, flush=True)


if __name__ == '__main__':
    main()
