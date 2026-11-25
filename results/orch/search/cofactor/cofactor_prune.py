"""Search-side cofactor bounds; cuts need Lean projected_bound certificates.

State contains exact live wire truth tables, not merely available wires.
History triples (op, a, b) use 0=AND, 1=OR, 2=AND-NOT, 3=NOT-AND.
The zero-cofactor bounds are transported from L_meta_670:
16 monotone binary gates, 15 binary gates with free complementation.
"""

from functools import lru_cache
from itertools import combinations
import json
from pathlib import Path

N = 10
FULL = (1 << (1 << N)) - 1
INPUTS = tuple(sum(1 << r for r in range(1 << N) if (r >> i) & 1)
               for i in range(N))
EDGES = ((0, 1), (1, 2), (2, 3), (3, 4), (4, 0),
         (0, 5), (1, 6), (2, 7), (3, 8), (4, 9),
         (5, 7), (7, 9), (9, 6), (6, 8), (8, 5))
TARGET = 0
for _a, _b in EDGES:
    TARGET |= INPUTS[_a] & INPUTS[_b]


def combine(op, a, b):
    if op in (0, "and"):
        return a & b
    if op in (1, "or"):
        return a | b
    if op in (2, "andnot"):
        return a & (FULL ^ b)
    if op in (3, "notand"):
        return (FULL ^ a) & b
    raise ValueError("unsupported binary operation")


def _key(word, mask, mode):
    word &= mask
    return min(word, word ^ mask) if mode else word


@lru_cache(maxsize=2048)
def _free_keys(mask, mode):
    return frozenset([_key(0, mask, mode), _key(mask, mask, mode)] +
                     [_key(a, mask, mode) for a in INPUTS])


@lru_cache(maxsize=512)
def direct_seed_defs(mask, mode):
    """One binary gate over free input literals; negative replay indices."""
    free = _free_keys(mask, mode)
    constants = {_key(0, mask, mode), _key(mask, mask, mode)}
    basis = sorted(free - constants)
    definitions = {}
    records = []
    for a, b in combinations(basis, 2):
        for op in range(4 if mode else 2):
            c = _key(combine(op, a, b), mask, mode)
            if c in free or c in definitions:
                continue
            records.append((op, a, b, c))
            definitions[c] = (-len(records), a, b)
    return definitions, tuple(records)


def paid_pool(state, mask, mode, history, direct=False):
    """Return (paid gates, replay indices), or None if history insufficient.

Projected outputs that become constants or aliases cost zero. The earliest
remaining realization is retained, then unused replay gates are removed.
This is a constructive upper bound on supplying the restricted live pool.
"""
    free = _free_keys(mask, mode)
    needed = {_key(a, mask, mode) for a in state} - free
    if not needed:
        return 0, ()
    if history is None and not direct:
        return None
    defs = dict(direct_seed_defs(mask, mode)[0]) if direct else {}
    for i, (op, a, b) in enumerate(history or ()):
        if not mode and op not in (0, 1, "and", "or"):
            return None
        c = combine(op, a, b)
        ck = _key(c, mask, mode)
        if ck in free or ck in defs:
            continue
        ak, bk = _key(a, mask, mode), _key(b, mask, mode)
        # Invalid or incomplete traces cannot justify a paid-pool certificate.
        if any(k not in free and k not in defs for k in (ak, bk)):
            continue
        defs[ck] = (i, ak, bk)
    selected = set()
    seen = set()
    pending = list(needed)
    while pending:
        k = pending.pop()
        if k in free or k in seen:
            continue
        seen.add(k)
        if k not in defs:
            return None
        i, ak, bk = defs[k]
        selected.add(i)
        pending.extend((ak, bk))
    return len(selected), tuple(sorted(selected))


def prune(state, remaining, mode, history=None, _direct=False):
    """Return (rejected, certificate details) using ten zero cofactors.

Do not feed available-but-dead wire pools here: constant roots are charged
because Live requires every listed wire to be consumed into the target.
"""
    lower = 15 if mode else 16
    best = None
    for v, input_word in enumerate(INPUTS):
        mask = FULL ^ input_word
        mass = sum((a & mask) in (0, mask) for a in state)
        pool = paid_pool(state, mask, mode, history, direct=_direct)
        if pool is None:
            continue
        paid, selected = pool
        margin = lower + mass - remaining - paid
        details = dict(vertex=v, value=False, lower=lower, mass=mass,
                       paid=paid, replay=selected, margin=margin)
        if best is None or margin > best["margin"]:
            best = details
        if margin > 0:
            return True, details
    return False, best


@lru_cache(maxsize=2)
def _extra_cofactors(mode):
    tables = json.loads(Path(__file__).with_name('subgraph_bounds.json').read_text())
    bounds = tables['signed' if mode else 'mono']
    cofactors = []
    for v in range(N):
        neighbors = {b if a == v else a for a, b in EDGES if v in (a, b)}
        residue = 1023 ^ (1 << v)
        for w in neighbors:
            residue &= ~(1 << w)
        # With v=1, its three neighbors are essential literal terms. Fixing
        # those neighbors to0 leaves an induced six-cycle with lower bound8.
        lower = bounds[residue] + len(neighbors)
        cofactors.append((INPUTS[v], lower, dict(zeroes=(), ones=(v,),
                                                residual=residue)))
    for a, b in combinations(range(N), 2):
        residue = 1023 ^ ((1 << a) | (1 << b))
        mask = FULL ^ (INPUTS[a] | INPUTS[b])
        cofactors.append((mask, bounds[residue], dict(zeroes=(a, b), ones=(),
                                                    residual=residue)))
    return tuple(cofactors)


def prune_multi(state, remaining, mode, history=None, _direct=False):
    """Single0, single1, and double0 restrictions with transported bounds."""
    hit, best = prune(state, remaining, mode, history, _direct=_direct)
    if hit:
        return hit, best
    for mask, lower, restriction in _extra_cofactors(mode):
        mass = sum((a & mask) in (0, mask) for a in state)
        pool = paid_pool(state, mask, mode, history, direct=_direct)
        if pool is None:
            continue
        paid, selected = pool
        margin = lower + mass - remaining - paid
        details = dict(restriction, lower=lower, mass=mass, paid=paid,
                       replay=selected, margin=margin)
        if best is None or margin > best['margin']:
            best = details
        if margin > 0:
            return True, details
    return False, best


def prune_direct(state, remaining, mode, history=None):
    """65 cofactors, permitting direct one-gate synthesis in paid pools.

Negative replay index -j denotes the j-th record (1-based) returned by
direct_seed_defs(mask,mode)[1]; nonnegative indices refer to input history.
"""
    return prune_multi(state, remaining, mode, history, _direct=True)


@lru_cache(maxsize=2)
def supplemental_cofactors(mode):
    """Optional120 mixed-pair and120 triple-zero restrictions."""
    tables = json.loads(Path(__file__).with_name('subgraph_bounds.json').read_text())
    bounds = tables['signed' if mode else 'mono']
    restrictions = []
    for a, b in combinations(range(N), 2):
        restrictions.extend([((a,), (b,)), ((b,), (a,)), ((), (a, b))])
    restrictions.extend((vs, ()) for vs in combinations(range(N), 3))
    result = []
    for zeroes, ones in restrictions:
        if any(a in ones and b in ones for a, b in EDGES):
            continue
        remaining = set(range(N)) - set(zeroes) - set(ones)
        literals = {b if a in ones else a for a, b in EDGES
                    if (a in ones and b in remaining) or
                    (b in ones and a in remaining)}
        residue = sum(1 << v for v in remaining - literals)
        proper_residue = any(residue >> a & 1 and residue >> b & 1
                             for a, b in EDGES)
        if proper_residue:
            lower = bounds[residue] + len(literals)
        elif literals:
            lower = len(literals) - 1
        else:
            continue
        mask = FULL
        for v in zeroes:
            mask &= FULL ^ INPUTS[v]
        for v in ones:
            mask &= INPUTS[v]
        result.append((mask, lower, dict(zeroes=zeroes, ones=ones,
                                         residual=residue)))
    return tuple(result)


def prune_supplemental(state, remaining, mode, history=None):
    """Profile-only extension; call after prune_direct to avoidduplicatework."""
    best = None
    for mask, lower, restriction in supplemental_cofactors(mode):
        mass = sum((a & mask) in (0, mask) for a in state)
        pool = paid_pool(state, mask, mode, history, direct=True)
        if pool is None:
            continue
        paid, selected = pool
        margin = lower + mass - remaining - paid
        details = dict(restriction, lower=lower, mass=mass, paid=paid,
                       replay=selected, margin=margin)
        if best is None or margin > best['margin']:
            best = details
        if margin > 0:
            return True, details
    return False, best
