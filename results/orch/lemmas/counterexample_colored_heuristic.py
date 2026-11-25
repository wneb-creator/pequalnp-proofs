import sys
sys.dont_write_bytecode = True
import argparse
import hashlib
import json
import math
import random
import time
from datetime import datetime, timezone
from pathlib import Path


def run(seconds):
    source = Path(__file__)
    fixture_path = source.with_name('counterexample_colored_lift.json')
    fixture = json.loads(fixture_path.read_text())
    N = fixture['N']
    n = 2 * N
    mask = fixture['incidence_mask']
    full_xs = [sum(1 << a for a in range(1 << n) if a >> i & 1) for i in range(n)]
    edges = [(p, N + line) for p, line in fixture['edges']]
    full_target = 0
    for p, line in edges:
        full_target |= full_xs[p] & full_xs[line]
    positives = {(1 << p) | (1 << line) for p, line in edges}
    forbidden = {1 << i for i in range(n)} | {
        (1 << p) | (1 << (N + line))
        for p in range(N) for line in range(N)
        if not (mask >> (N * p + line) & 1)
    }
    maximal_negative = {
        a for a in range(1 << n)
        if not (full_target >> a & 1)
        and all(a >> i & 1 or full_target >> (a | (1 << i)) & 1 for i in range(n))
    }
    tests = sorted(positives | forbidden | maximal_negative)
    xs = [sum(1 << j for j, a in enumerate(tests) if a >> i & 1) for i in range(n)]
    target = sum(1 << j for j, a in enumerate(tests) if full_target >> a & 1)
    full_forbidden = sum(1 << a for a in forbidden)
    clean = [(int(op == 'or'), a, b) for op, a, b in fixture['clean_gates']]
    k = len(clean) - 1

    def evaluate(gates, initial, goal):
        wires = initial[:]
        for op, a, b in gates:
            assert 0 <= a < len(wires) and 0 <= b < len(wires)
            wires.append(wires[a] | wires[b] if op else wires[a] & wires[b])
        return (wires[-1] ^ goal).bit_count(), wires

    assert evaluate(clean, full_xs, full_target)[0] == 0
    starts = []
    for removed, gate in enumerate(clean):
        for replacement in gate[1:]:
            def shift(wire):
                if wire == n + removed:
                    wire = replacement
                return wire - int(wire > n + removed)

            if shift(n + len(clean) - 1) != n + k - 1:
                continue
            gates = [(op, shift(a), shift(b)) for j, (op, a, b) in enumerate(clean) if j != removed]
            assert len(gates) == k
            starts.append(gates)
    rng = random.Random(3451)
    started = time.monotonic()
    deadline = started + seconds
    print(json.dumps({
        'event': 'start', 'at': datetime.now(timezone.utc).isoformat(),
        'N': N, 'mask': mask, 'gate_budget': k, 'seconds': seconds,
        'test_assignments': tests, 'seed': 3451, 'initial_circuits': starts,
        'algorithm': '6000-step restarts from one-gate deletions; mutate one op or operand; temperature4.5*0.01^(step/6000)',
        'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
        'fixture_sha256': hashlib.sha256(fixture_path.read_bytes()).hexdigest(),
    }), flush=True)
    best = len(tests) + 1
    tries = 0
    restarts = 0
    while time.monotonic() < deadline:
        gates = list(rng.choice(starts))
        score = evaluate(gates, xs, target)[0]
        for step in range(6000):
            if step % 256 == 0 and time.monotonic() >= deadline:
                break
            j = rng.randrange(k)
            old = gates[j]
            change = rng.randrange(5)
            if change == 0:
                new = (1 - old[0], old[1], old[2])
            elif change <= 2:
                new = (old[0], rng.randrange(n + j), old[2])
            else:
                new = (old[0], old[1], rng.randrange(n + j))
            gates[j] = new
            new_score = evaluate(gates, xs, target)[0]
            tries += 1
            temperature = 4.5 * (0.01 ** (step / 6000))
            if new_score <= score or rng.random() < math.exp((score - new_score) / temperature):
                score = new_score
            else:
                gates[j] = old
            if score < best:
                best = score
                full_errors, wires = evaluate(gates, full_xs, full_target)
                record = {
                    'event': 'best', 'N': N, 'mask': mask, 'gates': k,
                    'boundary_errors': best, 'full_errors': full_errors,
                    'tries': tries, 'restarts': restarts, 'elapsed_s': time.monotonic() - started,
                    'circuit': [['or' if op else 'and', a, b] for op, a, b in gates],
                    'all_ANDs_clean': all(op or not wires[n + j] & full_forbidden for j, (op, a, b) in enumerate(gates)),
                    'all_assignments_checked': 1 << n,
                }
                if best == 0:
                    assert full_errors == 0
                    record['event'] = 'full_validated_sat'
                print(json.dumps(record), flush=True)
                Path('/tmp/oec/pequalnp-pilot-51/counterexample_colored_heuristic_best.json').write_text(json.dumps(record, indent=2) + '\n')
                if best == 0:
                    return
        restarts += 1
    print(json.dumps({
        'event': 'end', 'result': 'no exact candidate found; heuristic only, no lower bound',
        'best_boundary_errors': best, 'tries': tries, 'restarts': restarts,
        'elapsed_s': time.monotonic() - started,
    }), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--seconds', type=float, default=300)
    arguments = parser.parse_args()
    run(arguments.seconds)
