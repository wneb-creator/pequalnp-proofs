import json, math, random, sys, time

limit = float(sys.argv[1]) if len(sys.argv) > 1 else 1800
seed = int(sys.argv[2]) if len(sys.argv) > 2 else 165
rng = random.Random(seed)
p = l = 7
n = p + l
edges = {(a, p + b) for a in range(p) for b in range(l) if (a - b) % 7 in (0, 1, 3)}
assert len(edges) == 21
assert all(0 <= a < p <= b < n for a, b in edges)
assert all((a, p + a) in edges for a in range(p))
assert all(not all((a, b) in edges for a in (a0, a1) for b in (b0, b1))
           for a0 in range(p) for a1 in range(a0 + 1, p)
           for b0 in range(p, n) for b1 in range(b0 + 1, n))

def target(x):
    return any((x >> a & 1) and (x >> b & 1) for a, b in edges)

positive = sorted((1 << a) | (1 << b) for a, b in edges)
negative = [x for x in range(1 << n) if not target(x) and
            all(target(x | (1 << v)) for v in range(n) if not (x >> v & 1))]
samples = positive + negative
want = (1 << len(positive)) - 1
all_mask = (1 << len(samples)) - 1
negative_mask = all_mask ^ want
base_values = [sum((x >> v & 1) << d for d, x in enumerate(samples)) for v in range(n)]
base_colors = [1] * p + [2] * l
N = 26

def initial():
    gates = []
    stars = []
    point_order = list(range(p)); rng.shuffle(point_order)
    removable = []
    for a in point_order:
        bs = [b for aa, b in edges if aa == a]; rng.shuffle(bs)
        removable.append(len(gates))
        w0 = n + len(gates); gates.append((bs[0], bs[1], 1))
        w1 = n + len(gates); gates.append((w0, bs[2], 1))
        w2 = n + len(gates); gates.append((a, w1, 0)); stars.append(w2)
    rng.shuffle(stars)
    while len(stars) > 1:
        a = stars.pop(rng.randrange(len(stars)))
        b = stars.pop(rng.randrange(len(stars)))
        gates.append((a, b, 1)); stars.append(n + len(gates) - 1)
    output = stars[0]
    gone = rng.choice(removable)
    replacement = gates[gone][rng.randrange(2)]
    gone_wire = n + gone
    def remap(w):
        if w == gone_wire:
            return replacement
        return w - 1 if w > gone_wire else w
    gates = [(remap(a), remap(b), op) for g, (a, b, op) in enumerate(gates) if g != gone]
    assert len(gates) == N
    return gates, remap(output)

def evaluate(gates, output):
    values = base_values.copy(); reach = base_colors.copy(); deps = [0] * n; mixed = 0
    for g, (a, b, op) in enumerate(gates):
        values.append((values[a] | values[b]) if op else (values[a] & values[b]))
        r = (reach[a] | reach[b]) if op else 0
        reach.append(r)
        bit = 1 << g
        deps.append(deps[a] | deps[b] | bit)
        if r == 3:
            mixed |= bit
    live = deps[output]
    errors = values[output] ^ want
    score = (errors & want).bit_count() + 2 * (errors & negative_mask).bit_count()
    return (None if live & mixed else score), live, values

def validate(gates, output):
    assert 0 <= output < n + len(gates)
    reach = base_colors.copy()
    for g, (a, b, op) in enumerate(gates):
        assert 0 <= a < n + g and 0 <= b < n + g and op in (0, 1)
        r = (reach[a] | reach[b]) if op else 0
        assert r != 3
        reach.append(r)
    for x in range(1 << n):
        values = [(x >> v) & 1 for v in range(n)]
        for a, b, op in gates:
            values.append((values[a] | values[b]) if op else (values[a] & values[b]))
        assert bool(values[output]) == target(x), x

def prune(gates, output, live):
    mapping = list(range(n)); result = []
    for g, (a, b, op) in enumerate(gates):
        if live >> g & 1:
            result.append((mapping[a], mapping[b], op)); mapping.append(n + len(result) - 1)
        else:
            mapping.append(-1)
    return result, mapping[output]

start = time.monotonic(); next_report = start + 30; next_restart = start + 120
iterations = accepted = restarts = 0
best = 1
gates, output = initial(); current, _, _ = evaluate(gates, output)
assert current == 1
print(json.dumps({'search': 'Fano26 simulated annealing', 'seed': seed, 'limit_seconds': limit,
                  'samples': len(samples), 'initial_weighted_errors': current}), flush=True)
found = False
while time.monotonic() - start < limit:
    iterations += 1
    candidate = gates.copy(); new_output = output
    mutation_count = 1 if rng.random() < 0.8 else rng.randrange(2, 4)
    for _ in range(mutation_count):
        pos = rng.randrange(3 * N + 1)
        if pos == 3 * N:
            new_output = rng.randrange(n, n + N)
        else:
            g, gene = divmod(pos, 3)
            item = list(candidate[g]); item[gene] = rng.randrange(2) if gene == 2 else rng.randrange(n + g)
            candidate[g] = tuple(item)
    score, live, values = evaluate(candidate, new_output)
    if score is not None:
        temperature = 0.2 + 2.8 * (1 - (iterations % 50000) / 50000) ** 2
        if score <= current or rng.random() < math.exp((current - score) / temperature):
            gates, output, current = candidate, new_output, score; accepted += 1
        if score < best:
            best = score
        if score == 0:
            result, result_output = prune(candidate, new_output, live)
            validate(result, result_output)
            print(json.dumps({'elapsed': time.monotonic() - start, 'gates': result,
                              'gate_count': len(result), 'output': result_output,
                              'full_truth_table_and_color_validated': True}), flush=True)
            found = True; break
    now = time.monotonic()
    if now >= next_report:
        print(json.dumps({'elapsed': now - start, 'iterations': iterations, 'accepted': accepted,
                          'current_errors': current, 'best_errors': best, 'restarts': restarts}), flush=True)
        next_report = now + 30
    if now >= next_restart:
        restarts += 1; gates, output = initial(); current, _, _ = evaluate(gates, output)
        next_restart = now + 120
print(json.dumps({'finished_seconds': time.monotonic() - start, 'iterations': iterations,
                  'best_errors': best, 'found_counterexample': found}), flush=True)
