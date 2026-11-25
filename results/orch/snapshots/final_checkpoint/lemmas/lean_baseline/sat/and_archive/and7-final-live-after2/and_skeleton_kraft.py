"""Equal-child Kraft bound with a small exact binary weighted accumulator.

For r complete maximal negatives and k ANDs, the bound is sum(2**c) <= 2**k.
The encoded nonnegative charge is sum(2**c - 1) <= 2**k - r.
Both false/false and true/true children contribute to c.
"""

from and_skeleton_sat import conjunction, disjunction, thresholds


def exclusive_or(cnf, a, b, hint):
    if a == -1:
        return b
    if b == -1:
        return a
    if a == 1:
        return -b
    if b == 1:
        return -a
    if a == b:
        return -1
    if a == -b:
        return 1
    z = cnf.var(hint)
    cnf.clause(a, b, -z)
    cnf.clause(a, -b, z)
    cnf.clause(-a, b, z)
    cnf.clause(-a, -b, -z)
    return z


def weighted_bound(cnf, terms, maximum):
    """Enforce sum(literal * 2**shift) <= maximum; return little-endian bits.

    Each term is (signed literal, shift, Boolean phase hint). Overflow of the
    fixed-width nonnegative accumulator is forbidden at every addition.
    """
    assert maximum >= 0
    width = max(1, maximum.bit_length())
    bits = [-1] * width
    hints = [False] * width
    for literal, shift, hint in terms:
        assert shift >= 0
        if shift >= width:
            cnf.clause(-literal)
            continue
        carry, hint_carry = literal, bool(hint)
        for bit in range(shift, width):
            previous, hint_previous = bits[bit], hints[bit]
            bits[bit] = exclusive_or(cnf, previous, carry, hint_previous != hint_carry)
            hints[bit] = hint_previous != hint_carry
            carry = conjunction(cnf, previous, carry, hint_previous and hint_carry)
            hint_carry = hint_previous and hint_carry
        cnf.clause(-carry)
    for bit in range(width):
        if not (maximum >> bit & 1):
            cnf.clause(-bits[bit], *(-bits[higher] if maximum >> higher & 1 else bits[higher]
                                   for higher in range(bit + 1, width)))
    return bits


def add_equal_child_kraft(cnf, negatives, and_count):
    slack = (1 << and_count) - len(negatives)
    assert slack >= 0
    maximum_count = min(and_count, (slack + 1).bit_length() - 1)
    terms = []
    for sides, hints in negatives:
        assert len(sides) == len(hints) == and_count
        equality = []
        for (left, right), (ha, hb) in zip(sides, hints):
            both_true = conjunction(cnf, left, right, ha and hb)
            both_false = conjunction(cnf, -left, -right, not ha and not hb)
            equality.append((disjunction(cnf, [both_true, both_false], ha == hb), ha == hb))
        count = thresholds(cnf, equality, maximum_count)
        cnf.clause(-count[maximum_count + 1])
        hint_count = sum(hint for _, hint in equality)
        for level in range(1, maximum_count + 1):
            terms.append((count[level], level - 1, hint_count >= level))
    weighted_bound(cnf, terms, slack)
    return {'AND_nodes': and_count, 'maximal_negatives': len(negatives),
            'maximum_weight_sum': 1 << and_count, 'maximum_slack_charge': slack}


def verify_equal_child_kraft(case, skeleton, evaluate):
    counts = []
    for mask, label in case['raw_tests']:
        if label:
            continue
        values, _ = evaluate(case, skeleton, mask)
        counts.append(sum(any(values[v] for v in gate['left']) ==
                          any(values[v] for v in gate['right'])
                          for gate in skeleton['and_gates']))
    weight = sum(1 << count for count in counts)
    assert weight <= 1 << len(skeleton['and_gates'])
    return {'equal_child_counts': counts, 'weight_sum': weight,
            'slack_charge': weight - len(counts)}
