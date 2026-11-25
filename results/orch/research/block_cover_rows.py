from functools import lru_cache
from math import ceil
from time import monotonic
import sys

START = monotonic()
LIMIT = 120
BUDGET = 11
pairs = [tuple(map(int, arg.split(','))) for arg in sys.argv[1:]]
rows = [0] + [1 << i for i in range(6)] + [sum(1 << i for i in pair) for pair in pairs]
NROWS = len(rows)
FULL = (1 << NROWS) - 1
NCAN = 1 << (NROWS - 1)
key = lambda m: min(m, m ^ FULL)
raw = [sum(1 << r for r, row in enumerate(rows) if row >> i & 1) for i in range(6)]
seed_values = [0] + [key(m) for m in raw]
seed_mask = sum(1 << m for m in seed_values)
profiles = [sum(1 << r for r,row in enumerate(rows) if row & p) for p in [56,38,21,11]]
cells = [(p, 1 << r) for p in profiles for r in range(NROWS) if not p >> r & 1]
all_cells = (1 << len(cells)) - 1
blocks = {}
for z in range(1 << NROWS):
    cov = sum(1 << i for i, (p, bit) in enumerate(cells) if not p & z and bit & z)
    if cov:
        k = key(z)
        assert k not in blocks or blocks[k] == cov
        blocks[k] = cov
options = [[(k, cov) for k, cov in blocks.items() if cov >> i & 1] for i in range(len(cells))]
pair_products = {}
for a in range(NCAN):
    for b in range(NCAN):
        pair_products[a, b] = sum(1 << q for q in {
            key(a & b), key(a & (b ^ FULL)),
            key((a ^ FULL) & b), key((a ^ FULL) & (b ^ FULL))})

def values(m):
    while m:
        bit = m & -m
        yield bit.bit_length() - 1
        m ^= bit

checks = 0
@lru_cache(maxsize=300000)
def products(m):
    xs = list(values(m))
    result = 0
    for a in xs:
        for b in xs:
            result |= pair_products[a, b]
    return result

@lru_cache(maxsize=500000)
def can_build(wanted, remaining, m):
    global checks
    checks += 1
    if checks % 1000 == 0 and monotonic() - START > LIMIT:
        raise TimeoutError
    need = wanted & ~m
    if not need:
        return ()
    if remaining < need.bit_count():
        return None
    available = products(m) & ~m
    candidates = available & need if remaining == need.bit_count() else available
    for q in sorted(values(candidates), key=lambda z: not (need >> z & 1)):
        answer = can_build(wanted, remaining - 1, m | (1 << q))
        if answer is not None:
            return (q,) + answer
    return None

visits = 0
@lru_cache(maxsize=500000)
def solve(count, coverage, wanted):
    global visits
    visits += 1
    if visits % 1000 == 0:
        if monotonic() - START > LIMIT:
            raise TimeoutError
        if visits % 100000 == 0:
            print('progress', visits, checks, round(monotonic()-START, 2), flush=True)
    missing = all_cells & ~coverage
    lb = ceil(missing.bit_count() / max(c.bit_count() for c in blocks.values()))
    if count + lb + wanted.bit_count() > BUDGET:
        return None
    if not missing:
        result = can_build(wanted, BUDGET-count, seed_mask)
        if result is not None:
            return (), result
        return None
    i = min(values(missing), key=lambda j: len(options[j]))
    choices = sorted(options[i], key=lambda p: (-(p[1] & missing).bit_count(), not(seed_mask >> p[0] & 1)))
    for k, covered in choices:
        next_wanted = wanted | ((1 << k) & ~seed_mask)
        result = solve(count+1, coverage | covered, next_wanted)
        if result is not None:
            bs, program = result
            return (k,)+bs, program
    return None

print('pairs',pairs,'rows',rows,'cells', cells, 'blocks', len(blocks), 'budget', BUDGET, flush=True)
try:
    answer = solve(0, 0, 0)
    print('answer', answer, 'visits', visits, 'core_checks', checks, 'seconds', monotonic()-START, flush=True)
except TimeoutError:
    print('TIMEOUT', 'visits', visits, 'core_checks', checks, 'seconds', monotonic()-START, flush=True)
