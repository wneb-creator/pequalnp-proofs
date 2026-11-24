"""Merge equal wire signatures on a supplied complete monotone test basis."""


def reduce_gates(n, gates, output, input_masks, target):
    assert len(input_masks) == n
    values = list(input_masks)
    mapping = list(range(n))
    representatives = {}
    for i, value in enumerate(values):
        representatives.setdefault(value, i)
    reduced = []
    for operation, sources in gates:
        assert operation in ('and', 'or') and len(sources) == 2
        assert all(0 <= source < len(mapping) for source in sources)
        a, b = (mapping[source] for source in sources)
        value = values[a] & values[b] if operation == 'and' else values[a] | values[b]
        wire = representatives.get(value)
        if wire is None:
            wire = n + len(reduced)
            reduced.append([operation, sorted([a, b])])
            values.append(value)
            representatives[value] = wire
        mapping.append(wire)
    assert 0 <= output < len(mapping)
    output = mapping[output]
    assert values[output] == target
    # Merging can disconnect earlier nodes, so prune their output cones as well.
    active = {output}
    for i in range(len(reduced) - 1, -1, -1):
        if n + i in active:
            active.update(reduced[i][1])
    final = []
    remap = {i: i for i in range(n)}
    for i, (operation, sources) in enumerate(reduced):
        if n + i in active:
            remap[n+i] = n + len(final)
            final.append([operation, [remap[source] for source in sources]])
    output = remap[output]
    # Independent forward replay checks both rewiring and the selected root.
    values = list(input_masks)
    for operation, (a, b) in final:
        assert a < len(values) and b < len(values)
        values.append(values[a] & values[b] if operation == 'and' else values[a] | values[b])
    assert values[output] == target
    return final, output


def expand_rows(n, rows, selected_outputs, active):
    """Use exactly the source-set decoder's deterministic OR association."""
    def bits(mask):
        while mask:
            bit = mask & -mask
            yield bit.bit_length() - 1
            mask -= bit
    gates, node_wires = [], {}
    def combine(wires):
        assert wires
        current = wires[0]
        for following in wires[1:]:
            gates.append(['or', sorted([current, following])])
            current = n + len(gates) - 1
        return current
    for i in bits(active):
        operands = [combine([j if j < n else node_wires[j-n] for j in bits(selected)])
                    for selected in rows[i]]
        if len(operands) == 1:
            node_wires[i] = operands[0]
        else:
            assert len(operands) == 2
            gates.append(['and', sorted(operands)])
            node_wires[i] = n + len(gates) - 1
    output = combine([node_wires[i] for i in bits(selected_outputs)])
    return gates, output
