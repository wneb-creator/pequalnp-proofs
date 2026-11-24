"""One-worker heuristic search; only fully evaluated witnesses are results."""
import argparse
import itertools
import json
import math
import random
import time
from pathlib import Path


N = 21
PAIRS = list(itertools.combinations(range(6), 2))
EDGES = [(u, 6 + j) for j, pair in enumerate(PAIRS) for u in pair]
POSITIVES = {(1 << u) | (1 << v) for u, v in EDGES}
NEGATIVES = set()
RAW_NEGATIVES = set()
for left in range(64):
    allowed = [6 + j for j, (u, v) in enumerate(PAIRS)
               if not (left >> u & 1) and not (left >> v & 1)]
    RAW_NEGATIVES.add(left | sum(1 << v for v in allowed))
    closed = [u for u in range(6)
              if not any(a == u and b in allowed for a, b in EDGES)]
    NEGATIVES.add(sum(1 << u for u in closed) + sum(1 << v for v in allowed))
TESTS = sorted(POSITIVES) + sorted(NEGATIVES)
INPUT_MASKS = [sum(1 << t for t, x in enumerate(TESTS) if x >> j & 1)
               for j in range(N)]
TARGET = (1 << len(POSITIVES)) - 1
ALL_TESTS = (1 << len(TESTS)) - 1


def bits(mask):
    while mask:
        low = mask & -mask
        yield low.bit_length() - 1
        mask -= low


def evaluate(rows, out):
    values = list(INPUT_MASKS)
    for left, right in rows:
        lv = 0
        rv = 0
        for j in bits(left):
            lv |= values[j]
        for j in bits(right):
            rv |= values[j]
        values.append(lv & rv)
    output = 0
    for i in bits(out):
        output |= values[N + i]
    active = out
    for i in range(len(rows) - 1, -1, -1):
        if active >> i & 1:
            active |= (rows[i][0] | rows[i][1]) >> N
    size = out.bit_count() - 1
    for i in bits(active):
        size += rows[i][0].bit_count() + rows[i][1].bit_count() - 1
    wrong_pos = (TARGET & ~output).bit_count()
    wrong_neg = (output & (ALL_TESTS ^ TARGET)).bit_count()
    return size, wrong_pos, wrong_neg, active


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


def baseline(rng, helpers):
    rows = []
    for i in range(helpers):
        sides = []
        for _ in range(2):
            choices = rng.sample(range(N + i), rng.randrange(1, 6))
            sides.append(sum(1 << j for j in choices))
        rows.append(tuple(sides))
    for u in range(6):
        rows.append((1 << u, sum(1 << v for a, v in EDGES if a == u)))
    return rows, ((1 << 6) - 1) << helpers


def mutate(rng, rows, out):
    changed = list(rows)
    if rng.random() < 0.07:
        new_out = out ^ (1 << rng.randrange(len(rows)))
        return changed, new_out or out
    i = rng.randrange(len(rows))
    side = rng.randrange(2)
    operands = list(rows[i])
    old = operands[side]
    limit = N + i
    choice = rng.random()
    if choice < 0.43:
        new = old ^ (1 << rng.randrange(limit))
    elif choice < 0.70:
        remove = rng.choice(list(bits(old)))
        new = (old & ~(1 << remove)) | (1 << rng.randrange(limit))
    elif choice < 0.86:
        new = old | (1 << rng.randrange(limit))
    elif choice < 0.94:
        new = 1 << rng.randrange(limit)
    else:
        selected = rng.sample(range(limit), rng.randrange(1, 7))
        new = sum(1 << j for j in selected)
    operands[side] = new or old
    changed[i] = tuple(operands)
    return changed, out


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--seed', type=int, required=True)
    p.add_argument('--seconds', type=float, required=True)
    p.add_argument('--output-dir', type=Path, required=True)
    p.add_argument('--epoch-steps', type=int, default=12000)
    args = p.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    rng = random.Random(args.seed)
    started = time.monotonic()
    last_log = started
    steps = 0
    epochs = 0
    best_valid = 10 ** 9
    best_by_wrong = {}
    print(json.dumps({'event': 'start', 'seed': args.seed, 'seconds': args.seconds,
                      'tests': len(TESTS), 'positive': len(POSITIVES),
                      'closed_negative': len(NEGATIVES), 'raw_negative': len(RAW_NEGATIVES),
                      'model': '7 or 8 ANDs over unshared OR-selected preceding sources'}), flush=True)

    def record(rows, out, ev):
        nonlocal best_valid
        size, wp, wn, active = ev
        wrong = wp + wn
        previous = best_by_wrong.get(wrong)
        if previous is None or size < previous[0]:
            best_by_wrong[wrong] = (size, list(rows), out)
        if wrong == 0 and size < best_valid:
            gates, output = decode(rows, out, active)
            assert len(gates) == size
            best_valid = size
            result = {'inputs': N, 'output': output, 'gates': gates, 'size': size,
                      'ands': sum(op == 'and' for op, _ in gates),
                      'ors': sum(op == 'or' for op, _ in gates),
                      'right_pairs': PAIRS, 'rows': rows, 'selected_outputs': out,
                      'seed': args.seed, 'steps': steps,
                      'elapsed_seconds': time.monotonic() - started,
                      'verified_positive': len(POSITIVES),
                      'verified_negative': len(RAW_NEGATIVES),
                      'proof_status': 'computational witness; requires Lean verification'}
            target = args.output_dir / ('best-valid-' + str(size) + '.json')
            target.write_text(json.dumps(result, indent=2) + '\n')
            print(json.dumps({'event': 'valid', 'size': size, 'file': str(target),
                              'steps': steps}), flush=True)
            if size <= 34:
                (args.output_dir / 'witness.json').write_text(json.dumps(result, indent=2) + '\n')
                (args.output_dir / 'witness-tuples.json').write_text(json.dumps(gates) + '\n')
                return True
        return False

    while time.monotonic() - started < args.seconds:
        helpers = 1 + (epochs % 2)
        rows, out = baseline(rng, helpers)
        if epochs > 0 and rng.random() < 0.45:
            options = [item for wrong, item in best_by_wrong.items()
                       if wrong <= 12 and len(item[1]) == helpers + 6]
            if options:
                _, rows, out = rng.choice(options)
                rows = list(rows)
        penalty = rng.choice([0.65, 0.9, 1.2, 1.7, 2.4, 3.5, 5.0])
        neg_weight = rng.choice([0.8, 1.0, 1.2])
        ev = evaluate(rows, out)
        if record(rows, out, ev):
            return
        score = ev[0] + penalty * (ev[1] + neg_weight * ev[2])
        for step in range(args.epoch_steps):
            candidate, candidate_out = mutate(rng, rows, out)
            next_ev = evaluate(candidate, candidate_out)
            next_score = next_ev[0] + penalty * (next_ev[1] + neg_weight * next_ev[2])
            temperature = 0.07 + 1.6 * (1.0 - step / args.epoch_steps) ** 2
            delta = next_score - score
            if delta <= 0 or rng.random() < math.exp(-delta / temperature):
                rows, out, ev, score = candidate, candidate_out, next_ev, next_score
                if record(rows, out, ev):
                    return
            steps += 1
            if steps % 2048 == 0:
                now = time.monotonic()
                if now - last_log >= 15:
                    print(json.dumps({'event': 'progress', 'seconds': round(now - started, 2),
                                      'steps': steps, 'epochs': epochs, 'best_valid': best_valid,
                                      'frontier': {str(k): v[0] for k, v in sorted(best_by_wrong.items()) if k <= 12}}), flush=True)
                    last_log = now
                if now - started >= args.seconds:
                    break
        epochs += 1
    frontier = {str(k): {'size': v[0], 'rows': v[1], 'selected_outputs': v[2]}
                for k, v in sorted(best_by_wrong.items())}
    (args.output_dir / 'frontier.json').write_text(json.dumps(frontier, indent=2) + '\n')
    print(json.dumps({'event': 'finished', 'seconds': time.monotonic() - started,
                      'steps': steps, 'epochs': epochs, 'best_valid': best_valid,
                      'conclusion': 'heuristic search only; no lower-bound conclusion'}), flush=True)


if __name__ == '__main__':
    main()
