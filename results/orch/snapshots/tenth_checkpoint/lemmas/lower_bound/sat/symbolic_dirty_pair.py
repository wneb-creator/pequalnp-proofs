"""One existential graph-negative input activating an internal AND.

For a budget-realizable exact gadget, the full pair-clean lower bound supplies
a graph-negative full input of weight at most two with an active AND. Outside
star ANDs are sound. Projection onto the core raw inputs preserves every paid
wire because each free feature is an OR of core raw inputs. Thus the dirty AND
has a core input witness of weight at most two, while the exact output is false.
This cut is target-only; it is not valid for the overbudget star calibration.
"""

from itertools import combinations


def require_symbolic_dirty_pair(cnf, selected, case):
    raw = [cnf.var() for _ in range(case['raw_inputs'])]
    levels = cnf.count_row(raw, 2)
    cnf.clause(-levels[3])
    for left, right in case['edges']:
        cnf.clause(-raw[left], -raw[right])
    wires = raw[:]
    for feature in case['features']:
        indices = feature['raw_indices']
        assert indices and all(0 <= i < len(raw) for i in indices)
        value = raw[indices[0]]
        for index in indices[1:]:
            value = cnf.ao_gate(1, value, raw[index])
        wires.append(value)
    assert len(wires) == case['inputs']
    events = []
    for op, left, right in selected:
        values = []
        for selectors in (left, right):
            assert len(selectors) == len(wires)
            value = cnf.var()
            for selector, source in zip(selectors, wires):
                cnf.clause(-selector, -value, source)
                cnf.clause(-selector, value, -source)
            values.append(value)
        output = cnf.ao_gate(op, *values)
        wires.append(output)
        event = cnf.var()
        cnf.clause(-event, -op)
        cnf.clause(-event, output)
        cnf.clause(op, -output, event)
        events.append(event)
    cnf.clause(-wires[-1])
    cnf.clause(*events)
    return raw, events


def dirty_pair_witness(case, gates):
    raw_inputs = case['raw_inputs']
    masks = [0] + [1 << i for i in range(raw_inputs)]
    masks += [(1 << i) | (1 << j) for i, j in combinations(range(raw_inputs), 2)]
    for mask in masks:
        if any(mask >> a & 1 and mask >> b & 1 for a, b in case['edges']):
            continue
        wires = [bool(mask >> i & 1) for i in range(raw_inputs)]
        wires += [any(wires[i] for i in feature['raw_indices'])
                  for feature in case['features']]
        events = []
        for index, (op, left, right) in enumerate(gates):
            assert op in (0, 1) and 0 <= left < len(wires) and 0 <= right < len(wires)
            value = (wires[left] or wires[right]) if op else (wires[left] and wires[right])
            wires.append(value)
            if op == 0 and value:
                events.append(index)
        if not wires[-1] and events:
            return {'raw_mask': mask, 'active_and_gates': events}
    return None
