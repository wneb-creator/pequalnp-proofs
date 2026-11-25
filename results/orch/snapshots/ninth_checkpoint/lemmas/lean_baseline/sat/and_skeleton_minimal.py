from and_skeleton_sat import (
    CNF, conjunction, disjunction, evaluate, normalize, side_value, thresholds, validate_problem,
)


def traced_assignment(cnf, selected, output, seed, input_literals, hint_mask):
    n = seed['inputs']
    hints, _ = evaluate(seed, hint_mask)
    values = input_literals.copy()
    sides = []
    for i, ((left, right), gate) in enumerate(zip(selected, seed['and_gates'])):
        a = side_value(cnf, left, values, gate['left'], hints)
        b = side_value(cnf, right, values, gate['right'], hints)
        sides.append((a, b))
        values.append(conjunction(cnf, a, b, hints[n + i]))
    final = side_value(cnf, output, values, seed['output'], hints)
    return values, final, sides


def emit_minimal(path, data, seed, dirty=False, side_order=True,
                 positive_live=False, child_incomparable=False,
                 dirty_pairs=None, negative_slack=None):
    n = data['inputs']
    edges = validate_problem(data)
    seed = normalize(seed)
    assert n == seed['inputs']
    cnf = CNF(path)
    selected = []
    for i, gate in enumerate(seed['and_gates']):
        left = [cnf.var(v in gate['left']) for v in range(n + i)]
        right = [cnf.var(v in gate['right']) for v in range(n + i)]
        selected.append((left, right))
        if side_order:
            equal = 1
            hint_equal = True
            for v, (a, b) in enumerate(zip(left, right)):
                cnf.clause(-equal, a, -b)
                hint_equal = hint_equal and ((v in gate['left']) == (v in gate['right']))
                next_equal = cnf.var(hint_equal)
                cnf.clause(-next_equal, equal)
                cnf.clause(-next_equal, -a, b)
                cnf.clause(-next_equal, a, -b)
                cnf.clause(-equal, -a, -b, next_equal)
                cnf.clause(-equal, a, b, next_equal)
                equal = next_equal
    output = [cnf.var(v in seed['output']) for v in range(n + len(selected))]
    positive_values = []
    negative_sides = []
    negative_values = []
    for test in data['tests']:
        mask = test['mask']
        values, final, sides = traced_assignment(
            cnf, selected, output, seed,
            [1 if mask >> v & 1 else -1 for v in range(n)], mask)
        cnf.clause(final if test['label'] else -final)
        if test['label']:
            positive_values.append(values[n:])
        else:
            hints, _ = evaluate(seed, mask)
            side_hints = [(any(hints[v] for v in gate['left']),
                           any(hints[v] for v in gate['right']))
                          for gate in seed['and_gates']]
            negative_sides.append((sides, side_hints))
            negative_values.append((values[n:], hints[n:]))
    dirty_inputs = None
    if dirty:
        possibilities = [0] + [1 << v for v in range(n)] + [
            (1 << a) | (1 << b) for a in range(n) for b in range(a + 1, n)]
        possibilities = [m for m in possibilities
                         if not any(m >> a & 1 and m >> b & 1 for a, b in edges)]

        def hint_score(mask):
            values, out = evaluate(seed, mask)
            return not any(values[n:]), out, mask.bit_count(), mask

        hint_mask = min(possibilities, key=hint_score)
        dirty_inputs = [cnf.var(bool(hint_mask >> v & 1)) for v in range(n)]
        count = thresholds(cnf, [(v, bool(hint_mask >> i & 1))
                                 for i, v in enumerate(dirty_inputs)], 2)
        cnf.clause(-count[3])
        for a, b in edges:
            cnf.clause(-dirty_inputs[a], -dirty_inputs[b])
        values, final, _ = traced_assignment(cnf, selected, output, seed, dirty_inputs, hint_mask)
        cnf.clause(-final)
        cnf.clause(*values[n:])
        if dirty_pairs is not None:
            assert dirty_pairs and all(len(pair) == 2 and len(set(pair)) == 2
                                       and all(0 <= v < n for v in pair)
                                       and tuple(sorted(pair)) not in {tuple(sorted(e)) for e in edges}
                                       for pair in dirty_pairs)
            cnf.clause(*(conjunction(cnf, dirty_inputs[a], dirty_inputs[b],
                                    bool(hint_mask >> a & 1 and hint_mask >> b & 1))
                         for a, b in dirty_pairs))
    else:
        assert dirty_pairs is None
    if positive_live:
        for i in range(len(selected)):
            cnf.clause(*(values[i] for values in positive_values))
    if child_incomparable:
        for i in range(len(selected)):
            left_only = []
            right_only = []
            for sides, hints in negative_sides:
                a, b = sides[i]
                ha, hb = hints[i]
                left_only.append(conjunction(cnf, a, -b, ha and not hb))
                right_only.append(conjunction(cnf, b, -a, hb and not ha))
            cnf.clause(*left_only)
            cnf.clause(*right_only)
    if negative_slack is not None:
        assert 0 <= negative_slack <= 64
        assert (1 << len(selected)) - len(negative_values) == negative_slack
        entries = []
        for (values, _), (sides, hints) in zip(negative_values, negative_sides):
            row = []
            for value, (a, b), (ha, hb) in zip(values, sides, hints):
                both_false = conjunction(cnf, -a, -b, not ha and not hb)
                equal = disjunction(cnf, [value, both_false], ha == hb)
                row.append((equal, ha == hb))
            if negative_slack <= 2:
                entries.extend(row)
                if negative_slack == 2:
                    count = thresholds(cnf, row, 1)
                    cnf.clause(-count[2])
            else:
                maximum = min(len(selected), (negative_slack + 1).bit_length() - 1)
                count = thresholds(cnf, row, maximum)
                cnf.clause(-count[maximum + 1])
                equal_hint = sum(hint for _, hint in row)
                for level in range(1, maximum + 1):
                    entries.extend([(count[level], equal_hint >= level)] * (1 << (level - 1)))
        count = thresholds(cnf, entries, negative_slack)
        cnf.clause(-count[negative_slack + 1])
    cnf.finish()
    return selected, output, dirty_inputs, cnf.variables, cnf.clauses, seed


def verify_minimal_conditions(data, skeleton, positive_live, child_incomparable):
    n = data['inputs']
    live = [False] * len(skeleton['and_gates'])
    orientations = [[False, False] for _ in skeleton['and_gates']]
    for test in data['tests']:
        values, _ = evaluate(skeleton, test['mask'])
        for i, gate in enumerate(skeleton['and_gates']):
            if test['label']:
                live[i] |= values[n + i]
            else:
                a = any(values[v] for v in gate['left'])
                b = any(values[v] for v in gate['right'])
                orientations[i][0] |= a and not b
                orientations[i][1] |= b and not a
    assert not positive_live or all(live)
    assert not child_incomparable or all(a and b for a, b in orientations)


def verify_negative_slack(data, skeleton, slack):
    if slack is None:
        return
    n = data['inputs']
    counts = []
    for test in data['tests']:
        if test['label']:
            continue
        values, _ = evaluate(skeleton, test['mask'])
        counts.append(sum(any(values[v] for v in gate['left']) ==
                          any(values[v] for v in gate['right'])
                          for gate in skeleton['and_gates']))
    assert (1 << len(skeleton['and_gates'])) - len(counts) == slack
    assert sum((1 << count) - 1 for count in counts) <= slack
