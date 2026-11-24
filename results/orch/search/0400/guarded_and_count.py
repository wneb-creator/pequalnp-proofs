def at_least(cnf, literals, minimum):
    if minimum < 1 or minimum > len(literals):
        raise ValueError('minimum must lie between one and the input count')
    previous = []
    for index, literal in enumerate(literals, start=1):
        current = []
        for count in range(1, min(minimum, index)+1):
            output = cnf.var()
            current.append(output)
            same = previous[count-1] if count <= len(previous) else None
            lower = previous[count-2] if count > 1 else None
            if count == 1:
                if same is None:
                    cnf.add(-output, literal)
                    cnf.add(output, -literal)
                else:
                    cnf.add(-same, output)
                    cnf.add(-literal, output)
                    cnf.add(-output, same, literal)
            elif same is None:
                cnf.add(-output, lower)
                cnf.add(-output, literal)
                cnf.add(output, -lower, -literal)
            else:
                # output iff same OR (lower AND literal).
                cnf.add(-same, output)
                cnf.add(-lower, -literal, output)
                cnf.add(-output, same, lower)
                cnf.add(-output, same, literal)
        previous = current
    return previous[minimum-1]


def abnormal_needs_eight_ands(cnf, original_and_literals, own_complement_literals):
    threshold = at_least(cnf, original_and_literals, 8)
    for abnormal in own_complement_literals:
        cnf.add(-abnormal, threshold)
    return threshold
