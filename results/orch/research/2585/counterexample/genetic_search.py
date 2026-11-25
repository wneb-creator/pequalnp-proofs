import itertools
import json
import math
import random
import resource
import sys
import time
from pathlib import Path
from macro_count_search import boundary_rows

OUT = Path(__file__).resolve().parent


def star_circuit(P, L, E):
    n = P + L
    edges = [(p, P + l) for p, l in E]
    cover = next(S for k in range(n + 1) for S in itertools.combinations(range(n), k)
                 if all(a in S or b in S for a, b in edges))
    assigned = {v: [] for v in cover}
    for a, b in edges:
        center = a if a in cover else b
        assigned[center].append(b if center == a else a)
    gates, stars = [], []
    for center, leaves in assigned.items():
        if not leaves:
            continue
        root = leaves[0]
        for leaf in leaves[1:]:
            gates.append((1, root, leaf))
            root = n + len(gates) - 1
        gates.append((0, center, root))
        stars.append(n + len(gates) - 1)
    root = stars[0]
    for star in stars[1:]:
        gates.append((1, root, star))
        root = n + len(gates) - 1
    return gates, root, cover


def delete_gate(gates, output, n, i, side):
    removed = n + i
    replacement = gates[i][side]
    def remap(w):
        return replacement if w == removed else w - (w > removed)
    return [(op, remap(a), remap(b)) for j, (op, a, b) in enumerate(gates) if j != i], remap(output)


def prune(gates, output, n):
    used = set()
    def visit(w):
        if w < n or w in used:
            return
        used.add(w)
        _, a, b = gates[w - n]
        visit(a)
        visit(b)
    visit(output)
    mapping = {i: i for i in range(n)}
    clean = []
    for i, (op, a, b) in enumerate(gates):
        old = n + i
        if old not in used:
            continue
        aa, bb = mapping[a], mapping[b]
        if aa == bb:
            mapping[old] = aa
        else:
            clean.append((op, aa, bb))
            mapping[old] = n + len(clean) - 1
    return clean, mapping[output]


def search(P, L, E, seconds, seed, name):
    n = P + L
    original, root, cover = star_circuit(P, L, E)
    size = len(original) - 1
    rows = boundary_rows(n, E, P)
    masks = [sum((bool(x >> i & 1) << j) for j, (x, _) in enumerate(rows)) for i in range(n)]
    target = sum(y << j for j, (_, y) in enumerate(rows))
    rng = random.Random(seed)
    best_score, best = len(rows) + 1, None
    attempts = 0
    start = time.monotonic()
    next_log = start + 20
    deadline = start + seconds
    next_restart = start
    print('START', name, 'inputs', n, 'edges', len(E), 'cover', cover,
          'target_gates', size, 'boundary_rows', len(rows), flush=True)

    def evaluate(gs, out):
        values = masks.copy()
        for op, a, b in gs:
            values.append(values[a] | values[b] if op else values[a] & values[b])
        return (values[out] ^ target).bit_count()

    while time.monotonic() < deadline:
        now = time.monotonic()
        if now >= next_restart:
            gs, output = delete_gate(original, root, n, rng.randrange(len(original)), rng.choice([1, 2]))
            score = evaluate(gs, output)
            next_restart = now + rng.uniform(0.5, 2.0)
        candidate = gs.copy()
        new_output = output
        number = rng.choices([1, 2, 3], [80, 17, 3])[0]
        for _ in range(number):
            if rng.randrange(size + 1) == size:
                new_output = rng.randrange(n + size)
            else:
                i = rng.randrange(size)
                op, a, b = candidate[i]
                field = rng.randrange(3)
                if field == 0:
                    op ^= 1
                elif field == 1:
                    a = rng.randrange(n + i)
                else:
                    b = rng.randrange(n + i)
                candidate[i] = (op, a, b)
        new_score = evaluate(candidate, new_output)
        attempts += 1
        if new_score <= score or rng.random() < math.exp((score - new_score) / 0.35):
            gs, output, score = candidate, new_output, new_score
        if new_score < best_score:
            best_score = new_score
            clean, out = prune(candidate, new_output, n)
            best = {'P': P, 'L': L, 'edges': E, 'gates': clean, 'output': out,
                    'score': best_score, 'attempts': attempts, 'seed': seed}
            (OUT / (name + '-best.json')).write_text(json.dumps(best, indent=2))
            print('BEST', best_score, 'attempts', attempts, 'active_gates', len(clean), flush=True)
            if best_score == 0:
                for x in range(1 << n):
                    values = [bool(x >> i & 1) for i in range(n)]
                    for op, a, b in clean:
                        values.append(values[a] or values[b] if op else values[a] and values[b])
                    expected = any((x >> p) & (x >> (P + l)) & 1 for p, l in E)
                    assert values[out] == expected
                print('FULL_TRUTH_TABLE_WITNESS', json.dumps(best), flush=True)
                return best
        if now >= next_log:
            print('PROGRESS', round(now - start, 2), 'attempts', attempts,
                  'best_score', best_score, flush=True)
            next_log = now + 20
    print('FINISH', round(time.monotonic() - start, 2), 'attempts', attempts,
          'best_score', best_score, flush=True)
    return best


if __name__ == '__main__':
    problem, seconds, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    resource.setrlimit(resource.RLIMIT_AS, (256 * 1024**2, 256 * 1024**2))
    resource.setrlimit(resource.RLIMIT_CPU, (seconds + 10, seconds + 10))
    if problem == 'theta':
        P = L = 4
        E = json.loads((OUT / 'maximum44.json').read_text())
    elif problem == 'fano':
        P = L = 7
        E = [(p, l) for p in range(7) for l in range(7) if (p - l) % 7 in [0, 1, 3]]
    else:
        raise ValueError(problem)
    search(P, L, E, seconds, seed, f'genetic-{problem}-{seed}')
