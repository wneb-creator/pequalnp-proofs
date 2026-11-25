"""Deterministic control checks for the collapsed free-OR AND model."""
import json
from pathlib import Path

import free_or_and_sat as model


def unit_propagate(cnf):
    values = {}
    while True:
        changed = False
        for row in cnf.rows:
            if any(abs(lit) in values and values[abs(lit)] == (lit > 0) for lit in row):
                continue
            unknown = [lit for lit in row if abs(lit) not in values]
            if not unknown:
                return False
            if len(unknown) == 1:
                literal = unknown[0]
                values[abs(literal)] = literal > 0
                changed = True
        if not changed:
            assert all(any(abs(lit) in values and values[abs(lit)] == (lit > 0)
                           for lit in row) for row in cnf.rows)
            return True


def pin(cnf, selectors, outputs, operands, chosen_outputs):
    for g, pair in enumerate(selectors):
        cnf.clause(outputs[g] if g in chosen_outputs else -outputs[g])
        for side, flags in enumerate(pair):
            for source, flag in enumerate(flags):
                cnf.clause(flag if source in operands[g][side] else -flag)


def check(name, p, l, edges, operands, chosen_outputs, expected_size):
    cnf, selectors, outputs, tests, _ = model.make_problem(p, l, edges, len(operands))
    pin(cnf, selectors, outputs, operands, chosen_outputs)
    assert unit_propagate(cnf), name
    record, verified = model.reconstruct(p, l, edges, operands, chosen_outputs)
    assert verified['gate_count'] == expected_size
    assert verified['and_count'] == len(operands)
    assert verified['inputs_verified'] == 1 << (p + l)
    assert verified['tCount'] == 0
    base = Path(__file__).parent / ('free_or_and_control_' + name)
    base.with_suffix('.circuit.json').write_text(json.dumps(record, indent=2) + '\n')
    return {'name': name, 'pinned_cnf_satisfiable_by_unit_propagation': True,
            'variables': cnf.n, 'clauses': len(cnf.rows), 'tests': len(tests),
            'verification': verified}


def main():
    core, leaves, _ = model.corona_graph()
    p, l, edges = model.read_graph('coronaC6')
    operands = [[[core[g]], [core[(g + 1) % 6], leaves[g]]] for g in range(6)]
    records = [check('corona', p, l, edges, operands, list(range(6)), 17)]

    masked = [[[0], [0]]]
    masked.extend([[[12 if source == 0 else source for source in side]
                    for side in pair] for pair in operands])
    records.append(check('duplicate_and_mask', p, l, edges, masked, list(range(1, 7)), 18))

    cnf, selectors, outputs, _, _ = model.make_problem(p, l, edges, 6)
    left, right = selectors[0][0][0], selectors[0][0][6]
    assert [-left, -right] in cnf.rows
    colour_check = model.CNF()
    colour_check.rows = [[-left, -right], [left], [right]]
    assert not unit_propagate(colour_check)
    records.append({'name': 'mixed_raw_colour_rejected', 'unit_propagation_conflict': True})

    path = Path(__file__).parent / 'fano_minus_incident_pair.json'
    p, l, edges = model.read_graph(str(path))
    operands = [[[a], [p + b for u, b in edges if u == a]] for a in range(p)]
    records.append(check('fano_minor', p, l, edges, operands, list(range(p)), 21))
    print(json.dumps(records, indent=2))


if __name__ == '__main__':
    main()
