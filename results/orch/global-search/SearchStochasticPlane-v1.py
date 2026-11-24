"""Heuristic source-set search including shared linear OR helpers."""
import argparse
import json
import math
import random
import time
from pathlib import Path

from SearchPlaneProblem import (ALL_TESTS, EDGES, INPUT_MASKS, N, POINTS, NEIGHBORS, AUTOMORPHISMS,
                                POSITIVES, RAW_NEGATIVES, TARGET, TESTS, bits)


def evaluate(rows, out):
    values = list(INPUT_MASKS)
    for row in rows:
        value = ALL_TESTS
        for selected in row:
            operand = 0
            for j in bits(selected):
                operand |= values[j]
            value &= operand
        values.append(value)
    output = 0
    for i in bits(out):
        output |= values[N + i]
    active = out
    for i in range(len(rows) - 1, -1, -1):
        if active >> i & 1:
            for selected in rows[i]:
                active |= selected >> N
    size = out.bit_count() - 1
    for i in bits(active):
        size += sum(s.bit_count() for s in rows[i]) - 1
    wrong_pos = (TARGET & ~output).bit_count()
    wrong_neg = (output & (ALL_TESTS ^ TARGET)).bit_count()
    return size, wrong_pos, wrong_neg, active, output


def decode(rows, out, active):
    gates = []
    node_wires = {}

    def combine(wires):
        assert wires
        current = wires[0]
        for following in wires[1:]:
            gates.append(['or', sorted([current, following])])
            current = N + len(gates) - 1
        return current

    for i in bits(active):
        operands = []
        for selected in rows[i]:
            operands.append(combine([j if j < N else node_wires[j - N]
                                     for j in bits(selected)]))
        if len(operands) == 1:
            node_wires[i] = operands[0]
        else:
            gates.append(['and', sorted(operands)])
            node_wires[i] = N + len(gates) - 1
    output = combine([node_wires[i] for i in bits(out)])
    for x in sorted(POSITIVES | RAW_NEGATIVES):
        vals = [bool(x >> j & 1) for j in range(N)]
        for op, (a, b) in gates:
            assert 0 <= a < len(vals) and 0 <= b < len(vals)
            vals.append(vals[a] and vals[b] if op == 'and' else vals[a] or vals[b])
        assert vals[output] == any((x >> u & 1) and (x >> v & 1) for u, v in EDGES)
    return gates, output


def baseline(rng, linear, helpers):
    multiplier,delta=rng.choice(AUTOMORPHISMS)
    shift=rng.randrange(POINTS)
    side=rng.randrange(2)
    if side==0:
        centers=[(multiplier*u+shift)%POINTS for u in range(POINTS)]
    else:
        centers=[POINTS+(multiplier*u+shift+delta)%POINTS for u in range(POINTS)]
    rng.shuffle(centers)
    rows=[]
    for i in range(linear):
        if rng.random()<.6:
            u=rng.choice(centers)
            choices=rng.sample(NEIGHBORS[u],rng.randrange(2,6))
        else:
            choices=rng.sample(range(N),rng.randrange(2,6))
        rows.append((sum(1<<j for j in choices),))
    dirty_centers=rng.sample(centers,helpers)
    activate_dirty=rng.random()<.6
    for h in range(helpers):
        i=len(rows)
        if activate_dirty:
            u=dirty_centers[h]
            other=rng.choice([v for v in centers if v!=u])
            sides=[(1<<u)|(1<<other),sum(1<<v for v in NEIGHBORS[u])]
        else:
            sides=[]
            for _ in range(2):
                choices=rng.sample(range(N+i),rng.randrange(1,6))
                sides.append(sum(1<<j for j in choices))
        rows.append(tuple(sides))
    for u in centers:
        right=sum(1<<v for v in NEIGHBORS[u])
        if activate_dirty and u in dirty_centers:
            right=1<<(N+linear+dirty_centers.index(u))
        rows.append((1<<u,right))
    for i in range(linear,len(rows)):
        sides=list(rows[i])
        for side in range(len(sides)):
            for h in range(linear):
                if rows[h][0]&sides[side]==rows[h][0]:
                    sides[side]=(sides[side]&~rows[h][0])|(1<<(N+h))
        rows[i]=tuple(sides)
    return rows,((1<<POINTS)-1)<<(linear+helpers)


def mutate(rng, rows, out, linear):
    changed = list(rows)
    if rng.random() < .055:
        new_out = out ^ (1 << rng.randrange(linear, len(rows)))
        return changed, new_out or out
    i = rng.randrange(len(rows))
    side = rng.randrange(len(rows[i]))
    operands = list(rows[i])
    old = operands[side]
    limit = N if i < linear else N + i
    choice = rng.random()
    if choice < .38:
        new = old ^ (1 << rng.randrange(limit))
    elif choice < .64:
        remove = rng.choice(list(bits(old)))
        new = (old & ~(1 << remove)) | (1 << rng.randrange(limit))
    elif choice < .80:
        new = old | (1 << rng.randrange(limit))
    elif choice < .90:
        new = 1 << rng.randrange(limit)
    elif choice < .96:
        choices = rng.sample(range(limit), rng.randrange(1, 7))
        new = sum(1 << j for j in choices)
    else:
        # Replace an existing OR subexpression by a compatible shared OR source.
        eligible = [j for j in range(min(i, linear)) if rows[j][0] & old == rows[j][0]]
        if eligible:
            j = rng.choice(eligible)
            new = (old & ~rows[j][0]) | (1 << (N + j))
        else:
            new = old
    operands[side] = new or old
    changed[i] = tuple(operands)
    return changed, out


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--seed', type=int, required=True)
    p.add_argument('--seconds', type=float, required=True)
    p.add_argument('--output-dir', type=Path, required=True)
    p.add_argument('--epoch-steps', type=int, default=18000)
    args = p.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    rng = random.Random(args.seed)
    started = time.monotonic()
    last_log = started
    steps = epochs = 0
    best_valid = 10 ** 9
    best_by_wrong = {}
    archive = {}
    print(json.dumps({'event': 'start', 'seed': args.seed, 'seconds': args.seconds,
                      'tests': len(TESTS), 'model': 'global plane:22/23 AND nodes,1/2 shared OR helpers,random point/line star bases'}), flush=True)

    def record(rows, out, ev, linear):
        nonlocal best_valid
        size, wp, wn, active, output = ev
        wrong = wp + wn
        previous = best_by_wrong.get(wrong)
        if previous is None or size < previous:
            best_by_wrong[wrong] = size
        # Keep semantic diversity at the low-error frontier, including ties.
        key = (linear, len(rows), output)
        previous = archive.get(key)
        if wp + wn / 128 <= 16 and (previous is None or size < previous[0] or
                          (size == previous[0] and rng.random() < .002)):
            archive[key] = (size, list(rows), out)
            if len(archive) > 10000:
                del archive[next(iter(archive))]
        if wrong == 0 and size < best_valid:
            gates, output_wire = decode(rows, out, active)
            assert len(gates) == size
            best_valid = size
            result = {'inputs': N, 'output': output_wire, 'gates': gates, 'size': size,
                      'ands': sum(op == 'and' for op, _ in gates),
                      'ors': sum(op == 'or' for op, _ in gates),
                      'edge_list': EDGES, 'rows': rows, 'selected_outputs': out,
                      'linear_helpers': linear, 'seed': args.seed, 'steps': steps,
                      'elapsed_seconds': time.monotonic() - started,
                      'verified_positive': len(POSITIVES),
                      'verified_negative': len(RAW_NEGATIVES),
                      'proof_status': 'computational witness; requires Lean verification'}
            target = args.output_dir / ('best-valid-' + str(size) + '.json')
            target.write_text(json.dumps(result, indent=2) + '\n')
            print(json.dumps({'event': 'valid', 'size': size, 'file': str(target), 'steps': steps}), flush=True)
            if size <= 124:
                (args.output_dir / 'witness.json').write_text(json.dumps(result, indent=2) + '\n')
                (args.output_dir / 'witness-tuples.json').write_text(json.dumps(gates) + '\n')
                return True
        return False

    while time.monotonic() - started < args.seconds:
        linear = 1 + (epochs % 2)
        helpers = 1 + ((epochs // 2) % 2)
        rows, out = baseline(rng, linear, helpers)
        if epochs and rng.random() < .50:
            options = [v for (s, n, _), v in archive.items()
                       if s == linear and n == len(rows)]
            if options:
                _, rows, out = rng.choice(options)
                rows = list(rows)
        penalty = rng.choice([.9, 1.2, 1.7, 2.4, 3.5, 5.0])
        neg_weight = rng.choice([0.002, 0.005, 0.01, 0.025, 0.05, 0.1, 0.25, 1.0])
        ev = evaluate(rows, out)
        if record(rows, out, ev, linear):
            return
        score = ev[0] + penalty * (ev[1] + neg_weight * ev[2])
        for step in range(args.epoch_steps):
            candidate, candidate_out = mutate(rng, rows, out, linear)
            next_ev = evaluate(candidate, candidate_out)
            next_score = next_ev[0] + penalty * (next_ev[1] + neg_weight * next_ev[2])
            temperature = .07 + 1.8 * (1.0 - step / args.epoch_steps) ** 2
            delta = next_score - score
            if delta <= 0 or rng.random() < math.exp(-delta / temperature):
                rows, out, ev, score = candidate, candidate_out, next_ev, next_score
                if record(rows, out, ev, linear):
                    return
            steps += 1
            if steps % 2048 == 0:
                now = time.monotonic()
                if now - last_log >= 15:
                    print(json.dumps({'event': 'progress', 'seconds': round(now - started, 2),
                                      'steps': steps, 'epochs': epochs, 'best_valid': best_valid,
                                      'archive': len(archive),
                                      'frontier': {str(k): v for k, v in sorted(best_by_wrong.items()) if k <= 12}}), flush=True)
                    last_log = now
                if now - started >= args.seconds:
                    break
        epochs += 1
    (args.output_dir / 'frontier.json').write_text(json.dumps(best_by_wrong, indent=2) + '\n')
    print(json.dumps({'event': 'finished', 'seconds': time.monotonic() - started,
                      'steps': steps, 'epochs': epochs, 'best_valid': best_valid,
                      'conclusion': 'heuristic search only; no lower-bound conclusion'}), flush=True)


if __name__ == '__main__':
    main()
