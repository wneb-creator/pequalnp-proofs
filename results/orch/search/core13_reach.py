import core13 as base

_original_encode = base.encode


def encode(m, notcount, first=-1):
    c, left, right, ops, outputs = _original_encode(m, notcount, first)
    n = base.N
    positive = [[c.var() for _ in range(n)] for _ in range(n + m)]
    negative = [[c.var() for _ in range(n)] for _ in range(n + m)]
    for wire in range(n):
        for variable in range(n):
            c.clause(positive[wire][variable] if wire == variable else -positive[wire][variable])
            c.clause(-negative[wire][variable])

    def mux(selectors, table, variable):
        value = c.var()
        for wire, selected in enumerate(selectors):
            other = table[wire][variable]
            c.clause(-selected, -value, other)
            c.clause(-selected, value, -other)
        return value

    for gate in range(m):
        is_not = ops[gate][2]
        for variable in range(n):
            pa = mux(left[gate], positive, variable)
            pb = mux(right[gate], positive, variable)
            na = mux(left[gate], negative, variable)
            nb = mux(right[gate], negative, variable)
            pz = positive[n + gate][variable]
            nz = negative[n + gate][variable]
            # Binary gates union both signs; NOT swaps signs of its first operand.
            for z, a, b in [(pz, pa, pb), (nz, na, nb)]:
                c.clause(is_not, -z, a, b)
                c.clause(is_not, z, -a)
                c.clause(is_not, z, -b)
            c.clause(-is_not, -pz, na)
            c.clause(-is_not, pz, -na)
            c.clause(-is_not, -nz, pa)
            c.clause(-is_not, nz, -pa)

    required = list(base.TRIPLES) + [tuple(range(1, n))]
    for target, variables in enumerate(required):
        for gate, selected in enumerate(outputs[target]):
            for variable in variables:
                c.clause(-selected, positive[n + gate][variable])
    return c, left, right, ops, outputs


base.encode = encode

if __name__ == '__main__':
    base.main()
