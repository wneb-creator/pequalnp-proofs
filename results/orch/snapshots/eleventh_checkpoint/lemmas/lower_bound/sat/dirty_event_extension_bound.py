"""A propagation consequence of weighted rejected-input packing.

Caller requirements: binary monotone gates, OR-only encoded features, and the
listed negative family and all graph edges enforced exactly. Every pair of
distinct negatives must have a positive union. If k ANDs accept raw witness X,
the m family members extending X each contribute at least 2**k to packing.
Thus N + m*(2**k - 1) <= 2**r, where r counts all binary ANDs, copies included.
"""

from itertools import combinations


def extension_bounds(case, maximum_ands):
    negatives = [mask for mask, label in case['raw_tests'] if not label]
    assert len(negatives) == len(set(negatives))
    assert all(any((left | right) >> a & 1 and (left | right) >> b & 1
                   for a, b in case['edges'])
               for left, right in combinations(negatives, 2))
    capacity = (1 << maximum_ands) - len(negatives)
    assert capacity >= 0
    r = case['raw_inputs']
    masks = [0] + [1 << i for i in range(r)]
    masks += [(1 << a) | (1 << b) for a, b in combinations(range(r), 2)]
    answer = []
    for mask in masks:
        if any(mask >> a & 1 and mask >> b & 1 for a, b in case['edges']):
            continue
        extensions = sum(mask & negative == mask for negative in negatives)
        if extensions == 0:
            continue
        bound = (capacity // extensions + 1).bit_length() - 1
        if bound < maximum_ands:
            answer.append(dict(mask=mask, extensions=extensions, maximum_events=bound))
    return answer


def add_extension_bound(cnf, raw, events, selected, case, maximum_ands):
    assert len(raw) == case['raw_inputs'] and len(events) == len(selected)
    event_levels = cnf.count_row(events, maximum_ands)
    and_levels = cnf.count_row([-op for op, _, _ in selected], maximum_ands)
    guard = and_levels[maximum_ands + 1]
    bounds = extension_bounds(case, maximum_ands)
    for entry in bounds:
        mismatch = [-literal if entry['mask'] >> i & 1 else literal
                    for i, literal in enumerate(raw)]
        cnf.clause(guard, *mismatch, -event_levels[entry['maximum_events'] + 1])
    return bounds
