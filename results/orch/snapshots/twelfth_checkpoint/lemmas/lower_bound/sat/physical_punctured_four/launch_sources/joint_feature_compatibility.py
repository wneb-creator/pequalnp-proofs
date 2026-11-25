def optional_prefix_constraints(cnf, selected, groups, ninputs):
    """Permit at most one referenced optional prefix in each outside-row group."""
    flattened = [wire for group in groups for wire in group]
    assert len(flattened) == len(set(flattened))
    assert all(0 <= wire < ninputs for wire in flattened)
    used = {}
    for wire in flattened:
        occurrences = [side[wire] for _, left, right in selected
                       for side in (left, right)]
        literal = cnf.var()
        used[wire] = literal
        cnf.clause(-literal, *occurrences)
        for occurrence in occurrences:
            cnf.clause(-occurrence, literal)
    for group in groups:
        for i, left in enumerate(group):
            for right in group[i + 1:]:
                cnf.clause(-used[left], -used[right])
    return used


def used_optional_prefixes(gates, groups):
    referenced = {wire for _, left, right in gates for wire in (left, right)}
    answer = [sorted(referenced.intersection(group)) for group in groups]
    assert all(len(group) <= 1 for group in answer)
    return answer


def used_feature_cardinality(cnf, selected, raw_inputs, ninputs, maximum, used):
    """Expose the structurally implied bound on distinct optional input wires."""
    used = dict(used)
    for wire in range(raw_inputs, ninputs):
        if wire not in used:
            occurrences = [side[wire] for _, left, right in selected
                           for side in (left, right)]
            literal = cnf.var()
            used[wire] = literal
            cnf.clause(-literal, *occurrences)
            for occurrence in occurrences:
                cnf.clause(-occurrence, literal)
    assert set(used) == set(range(raw_inputs, ninputs))
    levels = cnf.count_row(list(used.values()), maximum)
    cnf.clause(-levels[maximum + 1])
    return used
