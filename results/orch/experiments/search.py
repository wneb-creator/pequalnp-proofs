import json
import random
import time
from pathlib import Path

root = Path('/tmp/oec/pequalnp-pilot-73/counterexample')
data = json.loads((root / 'promises.json').read_text())
rows = data['positive'] + data['negative']
pos = (1 << len(data['positive'])) - 1
allbits = (1 << len(rows)) - 1
neg = allbits ^ pos
inputs = [sum(1 << j for j, row in enumerate(rows) if row >> i & 1) for i in range(26)]
rng = random.Random(2089)

def evaluate(gates):
    vals = inputs.copy()
    for op, a, b in gates:
        vals.append((vals[a] & vals[b]) if op == 0 else
                    (vals[a] | vals[b]) if op == 1 else allbits if op == 2 else 0)
    false_neg = (pos & ~vals[-1]).bit_count()
    false_pos = (neg & vals[-1]).bit_count()
    return 4 * false_neg + false_pos, false_neg, false_pos, vals

def standard():
    gates = []
    def put(op, a, b):
        gates.append((op, a, b))
        return 25 + len(gates)
    pivot = rng.randrange(13)
    points = [p for p in range(13) if p != pivot]
    rng.shuffle(points)
    terms = []
    for p in points:
        ns = [13 + l for l in range(13) if data['lines_through'][p] >> l & 1]
        rng.shuffle(ns)
        q = ns[0]
        for i in ns[1:]:
            q = put(1, q, i)
        terms.append(put(0, p, q))
    rng.shuffle(terms)
    while len(terms) > 1:
        a = terms.pop(rng.randrange(len(terms)))
        b = terms.pop(rng.randrange(len(terms)))
        terms.append(put(1, a, b))
    f0 = terms[0]
    ns = [13 + l for l in range(13) if data['lines_through'][pivot] >> l & 1]
    rng.shuffle(ns)
    q = ns[0]
    for i in ns[1:]:
        q = put(1, q, i)
    a = put(1, f0, pivot)
    b = put(1, f0, q)
    put(0, a, b)
    assert len(gates) == 65 and evaluate(gates)[0] == 0
    for _ in range(2):
        j = rng.randrange(len(gates) - 3)
        old = 26 + j
        replacement = gates[j][rng.randrange(1, 3)]
        gates.pop(j)
        def fix(i):
            return replacement if i == old else i - 1 if i > old else i
        gates = [(op, fix(a), fix(b)) for op, a, b in gates]
    return gates

def bad_path(gates, vals, bit, desired):
    index = 26 + len(gates) - 1
    path = []
    while index >= 26:
        j = index - 26
        path.append(j)
        op, a, b = gates[j]
        av, bv = (vals[a] >> bit) & 1, (vals[b] >> bit) & 1
        if op >= 2:
            break
        candidates = [i for i, v in [(a, av), (b, bv)] if v != desired]
        if not candidates:
            break
        index = rng.choice(candidates)
    return path

start = time.monotonic()
best = 100000
iteration = 0
restarts = 0
while time.monotonic() - start < 240:
    gates = standard()
    score, fn, fp, vals = evaluate(gates)
    stale = 0
    restarts += 1
    while stale < 6000 and time.monotonic() - start < 240:
        iteration += 1
        bad = (pos ^ vals[-1]) & allbits
        bits = [i for i in range(len(rows)) if bad >> i & 1]
        bit = rng.choice(bits)
        desired = 1 if bit < len(data['positive']) else 0
        path = bad_path(gates, vals, bit, desired)
        j = rng.choice(path if rng.random() < 0.8 else list(range(len(gates))))
        op, a, b = gates[j]
        bound = 26 + j
        replacement = list(gates[j])
        if rng.random() < 0.1 and j != len(gates) - 1:
            replacement[0] = 1 - op if op < 2 else rng.randrange(2)
        else:
            which = rng.randrange(1, 3)
            candidates = [i for i in range(bound) if ((vals[i] >> bit) & 1) == desired]
            replacement[which] = rng.choice(candidates) if candidates and rng.random() < 0.8 else rng.randrange(bound)
        old = gates[j]
        gates[j] = tuple(replacement)
        new_score, new_fn, new_fp, new_vals = evaluate(gates)
        if new_score <= score or rng.random() < 0.0005:
            stale = 0 if new_score < score else stale + 1
            score, fn, fp, vals = new_score, new_fn, new_fp, new_vals
        else:
            gates[j] = old
            stale += 1
        if score < best:
            best = score
            print('best', best, 'fn', fn, 'fp', fp, 'iterations', iteration,
                  'restarts', restarts, 'seconds', round(time.monotonic() - start, 2), flush=True)
            (root / 'best-candidate.json').write_text(json.dumps({'gates': gates, 'fn': fn, 'fp': fp, 'score': score}))
        if score == 0:
            print('FOUND', flush=True)
            raise SystemExit(0)
print('DONE', iteration, restarts, best, flush=True)
