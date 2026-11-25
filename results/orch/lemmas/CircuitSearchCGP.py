import json, random, sys, time, math

limit = float(sys.argv[1]) if len(sys.argv) > 1 else 1800
seed = int(sys.argv[2]) if len(sys.argv) > 2 else 164
rng = random.Random(seed)
p = l = 7
n = p + l
edges = {(a, p + b) for a in range(p) for b in range(l) if (a - b) % 7 in (0, 1, 3)}
assert all(0 <= a < p <= b < n for a, b in edges)
assert len(edges) == 21
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
base_values = [sum((x >> v & 1) << d for d, x in enumerate(samples)) for v in range(n)]
base_colors = [1] * p + [2] * l

# op 0 is AND; op 1 is OR.
base = []
stars = []
for a in range(p):
    b0, b1, b2 = sorted(b for aa, b in edges if aa == a)
    w0 = n + len(base); base.append((b0, b1, 1))
    w1 = n + len(base); base.append((w0, b2, 1))
    w2 = n + len(base); base.append((a, w1, 0)); stars.append(w2)
out = stars[0]
for w in stars[1:]:
    base.append((out, w, 1)); out = n + len(base) - 1
assert len(base) == 27

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

validate(base, out)
print(json.dumps({'search': 'Fano neutral Cartesian genetic programming', 'seed': seed,
                  'limit_seconds': limit, 'samples': len(samples), 'base_gates': len(base),
                  'base_validated_full_truth_table': True}), flush=True)

N = 96

def initial():
    gates = []
    mapping = list(range(n))
    for a, b, op in base:
        for _ in range(2):
            top = n + len(gates)
            gates.append((rng.randrange(top), rng.randrange(top), rng.randrange(2)))
        gates.append((mapping[a], mapping[b], op))
        mapping.append(n + len(gates) - 1)
    output = mapping[out]
    while len(gates) < N:
        top = n + len(gates)
        gates.append((rng.randrange(top), rng.randrange(top), rng.randrange(2)))
    return gates, output

def score(gates, output):
    values = base_values.copy()
    reach = base_colors.copy()
    deps = [0] * n
    mixed = 0
    for g, (a, b, op) in enumerate(gates):
        values.append((values[a] | values[b]) if op else (values[a] & values[b]))
        r = (reach[a] | reach[b]) if op else 0
        reach.append(r)
        bit = 1 << g
        deps.append(deps[a] | deps[b] | bit)
        if r == 3:
            mixed |= bit
    live = deps[output]
    if values[output] != want or live & mixed:
        return None, live
    return live.bit_count(), live

def prune(gates, output, live):
    mapping = list(range(n))
    result = []
    for g, (a, b, op) in enumerate(gates):
        if live >> g & 1:
            result.append((mapping[a], mapping[b], op))
            mapping.append(n + len(result) - 1)
        else:
            mapping.append(-1)
    return result, mapping[output]

start = time.monotonic()
next_report = start + 30
next_restart = start + 180
best = 27
iterations = accepted = restarts = 0
gates, output = initial()
current, _ = score(gates, output)
assert current == 27
while time.monotonic() - start < limit:
    iterations += 1
    candidate = gates.copy()
    new_output = output
    for _ in range(1 if rng.random() < 0.95 else rng.randrange(2, 5)):
        pos = rng.randrange(3 * N + 1)
        if pos == 3 * N:
            new_output = rng.randrange(n, n + N)
        else:
            g, gene = divmod(pos, 3)
            item = list(candidate[g])
            item[gene] = rng.randrange(2) if gene == 2 else rng.randrange(n + g)
            candidate[g] = tuple(item)
    new_score, live = score(candidate, new_output)
    if new_score is not None:
        if new_score <= current or rng.random() < math.exp((current - new_score) / 0.25):
            gates, output, current = candidate, new_output, new_score
            accepted += 1
        if new_score < best:
            best = new_score
            result, result_output = prune(candidate, new_output, live)
            validate(result, result_output)
            print(json.dumps({'elapsed': time.monotonic() - start, 'new_best': best,
                              'gates': result, 'output': result_output,
                              'full_truth_table_and_color_validated': True}), flush=True)
            if best <= 26:
                break
    now = time.monotonic()
    if now >= next_report:
        print(json.dumps({'elapsed': now - start, 'iterations': iterations, 'accepted': accepted,
                          'current': current, 'best': best, 'restarts': restarts}), flush=True)
        next_report = now + 30
    if now >= next_restart:
        restarts += 1
        gates, output = initial()
        current, _ = score(gates, output)
        next_restart = now + 180
print(json.dumps({'finished_seconds': time.monotonic() - start, 'iterations': iterations,
                  'best': best, 'found_counterexample': best <= 26}), flush=True)
