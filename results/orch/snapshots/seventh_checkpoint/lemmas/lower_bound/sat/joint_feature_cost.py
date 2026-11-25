def copy_credited_prefix_constraints(cnf, selected, groups, raw_inputs, ninputs):
    """Charge extra outside prefixes against removable equal-fanin paid gates."""
    flattened = [wire for group in groups for wire in group]
    assert len(flattened) == len(set(flattened))
    assert all(raw_inputs <= wire < ninputs for wire in flattened)
    used = {}
    for wire in range(raw_inputs, ninputs):
        occurrences = [side[wire] for _, left, right in selected
                       for side in (left, right)]
        literal = cnf.var()
        used[wire] = literal
        cnf.clause(-literal, *occurrences)
        for occurrence in occurrences:
            cnf.clause(-occurrence, literal)
    extra = []
    for group in groups:
        levels = cnf.count_row([used[wire] for wire in group], len(group) - 1)
        extra.extend(levels[2:len(group) + 1])
    copies = []
    for _, left, right in selected:
        same = cnf.var()
        copies.append(same)
        for a, b in zip(left, right):
            cnf.clause(-a, -b, same)
            cnf.clause(-a, -same, b)
    count = len(selected)
    cost = cnf.count_row(extra + [-copy for copy in copies], count)
    cnf.clause(-cost[count + 1])
    allowance = count - raw_inputs + 1
    assert allowance >= 0
    support = cnf.count_row(list(used.values()) + extra, allowance)
    cnf.clause(-support[allowance + 1])
    return dict(used=used, extra=extra, copies=copies)


def syntactic_budget(gates, groups):
    referenced = {wire for _, left, right in gates for wire in (left, right)}
    extra = sum(max(0, len(referenced.intersection(group)) - 1) for group in groups)
    copies = sum(left == right for _, left, right in gates)
    return dict(extra=extra, copies=copies, within_budget=extra <= copies)
