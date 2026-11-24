def combine_cost(c, operation, left, right, result):
    assert len(left) == len(right) == len(result) == 6
    for a in range(6):
        for b in range(6):
            c.add(-operation, -left[a], -right[b], result[min(a, b)])
            c.add(operation, -left[a], -right[b], result[min(5, a+b)])


def exact_costs(c, operations, aa, bb, raw_inputs, constant_costs):
    base = len(aa[0])
    assert set(constant_costs) == set(range(raw_inputs, base))
    assert all(0 <= value <= 5 for value in constant_costs.values())
    costs = [[c.var() for _ in range(6)] for _ in operations]
    for row in costs:
        c.one(row)
    for j, operation in enumerate(operations):
        children = [[c.var() for _ in range(6)] for _ in range(2)]
        for selectors, values in zip((aa[j], bb[j]), children):
            for k, selected in enumerate(selectors):
                if k < base:
                    source = 1 if k < raw_inputs else constant_costs[k]
                    for cost, value in enumerate(values):
                        c.add(-selected, value if cost == source else -value)
                else:
                    for source, value in zip(costs[k-base], values):
                        c.add(-selected, -source, value)
                        c.add(-selected, source, -value)
        combine_cost(c, operation, children[0], children[1], costs[j])
    return costs
