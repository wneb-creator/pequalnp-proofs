"""Check local erase-and-redirect irreducibility of the nonleast P5 witness."""

import json
from itertools import product

GATES = (
    ("or", 2, 4), ("or", 0, 5), ("or", 1, 3),
    ("and", 6, 7), ("or", 1, 5), ("and", 8, 9),
    ("or", 0, 2), ("or", 11, 3), ("and", 10, 12),
)
EDGES = ((0, 1), (1, 2), (2, 3), (3, 4))
ROWS = tuple(product((False, True), repeat=5))


def target(bits):
    return any(bits[u] and bits[v] for u, v in EDGES)


def bypass_value(bits, gate, operand):
    wires = list(bits)
    for index, (operation, left, right) in enumerate(GATES):
        if index == gate:
            wires.append(True if operand is None else wires[operand])
        elif operation == "and":
            wires.append(wires[left] and wires[right])
        else:
            wires.append(wires[left] or wires[right])
    return wires[-1]


results = []
for gate, (_, left, right) in enumerate(GATES):
    for operand in range(5 + gate):
        witnesses = [
            [index for index, value in enumerate(bits) if value]
            for bits in ROWS if bypass_value(bits, gate, operand) != target(bits)
        ]
        assert witnesses
        results.append({
            "gate": gate,
            "operand": operand,
            "is_original_operand": operand in (left, right),
            "changed_assignments": len(witnesses),
            "first_witness": witnesses[0],
        })

true_overrides = []
for gate in range(len(GATES)):
    witnesses = [
        [index for index, value in enumerate(bits) if value]
        for bits in ROWS if bypass_value(bits, gate, None) != target(bits)
    ]
    assert witnesses
    true_overrides.append({
        "gate": gate,
        "changed_assignments": len(witnesses),
        "first_witness": witnesses[0],
    })

print(json.dumps({
    "assignments_per_replacement": len(ROWS),
    "replacements": len(results),
    "every_prior_wire_redirect_changes_function": True,
    "results": results,
    "every_true_override_changes_function": True,
    "true_overrides": true_overrides,
    "scope": "The 9-gate circuit is nonleast; a 5-gate circuit exists.",
}, indent=2))
