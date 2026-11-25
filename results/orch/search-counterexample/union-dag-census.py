"""Exhaustive small coverage census, not a Lean proof or a circuit lower bound.

An available union U covers requirement (p,D) when N(p) is contained in U
and U is disjoint from D. Inputs and all gates are pure unions of 13 lines.
The findings concern this restricted multi-output model only.
"""

import hashlib
import itertools
import json
from collections import defaultdict
from pathlib import Path


def minimal_transversals(vertices, rows):
    for size in range(len(vertices) + 1):
        solutions = [
            list(choice)
            for choice in itertools.combinations(vertices, size)
            if all(set(choice).intersection(row) for row in rows)
        ]
        if solutions:
            return {"minimum": size, "minimizers": solutions}
    return None


source = Path(__file__).with_name("multi-output-line-neighborhoods.json")
raw = source.read_bytes()
data = json.loads(raw)
assert data["input_count"] == 13
targets = data["targets"]
negatives = data["negative_samples"]
pencils = [target["positive_mask"] for target in targets]
assert len(targets) == 13 and len(negatives) == 468
assert all(mask.bit_count() == 4 for mask in pencils)
assert all(len(target["negative_rows"]) == 126 for target in targets)
assert all(
    not pencils[p] & negatives[row]
    for p, target in enumerate(targets)
    for row in target["negative_rows"]
)

census = defaultdict(lambda: {"sets": 0, "useful": 0, "coverage_values": set()})
dead_masks = []
for union in range(1 << 13):
    contained = [p for p, pencil in enumerate(pencils) if pencil & union == pencil]
    coverage = sum(
        not union & negatives[row]
        for p in contained
        for row in targets[p]["negative_rows"]
    )
    if contained:
        record = census[(union.bit_count(), len(contained))]
        record["sets"] += 1
        record["useful"] += bool(coverage)
        record["coverage_values"].add(coverage)
    if not any(not union & negative for negative in negatives):
        dead_masks.append(union)

profiles = []
for p, target in enumerate(targets):
    rows = [negatives[row] for row in target["negative_rows"]]
    outside_lines = [line for line in range(13) if not pencils[p] >> line & 1]
    proper = minimal_transversals(
        outside_lines,
        [{line for line in outside_lines if not negative >> line & 1} for negative in rows],
    )
    other_points = [q for q in range(13) if q != p]
    shared = minimal_transversals(
        other_points,
        [{q for q in other_points if not pencils[q] & negative} for negative in rows],
    )
    assert proper["minimum"] == 3 and len(proper["minimizers"]) == 12
    assert shared["minimum"] == 9 and len(shared["minimizers"]) == 4
    profiles.append({"point": p, "proper_clause_extras": proper, "shared_clause_partners": shared})

output = {
    "status": "finite computation only; not Lean checked; no 39-OR lower bound or counterexample claimed",
    "input_file": source.name,
    "input_sha256": hashlib.sha256(raw).hexdigest(),
    "requirements": sum(len(target["negative_rows"]) for target in targets),
    "census": [
        {
            "union_size": key[0],
            "contained_pencils": key[1],
            **{field: sorted(value) if isinstance(value, set) else value for field, value in record.items()},
        }
        for key, record in sorted(census.items())
    ],
    "dead_masks": dead_masks,
    "dead_mask_count": len(dead_masks),
    "profiles": profiles,
}
print(json.dumps(output, indent=2, sort_keys=True))
