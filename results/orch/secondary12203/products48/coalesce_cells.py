"""Prepare a reversible, static-only cells batching transformation.

Only literal split-depth arguments of concrete certificate theorems change.
The preexisting product fallback is never overwritten.
"""

import hashlib
import json
import re
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path


HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent / "products" / "L_meta_670_products12203.lean"
OUTPUT = HERE / "L_meta_670_products48_12203.lean"
CAP = 48
source_bytes = SOURCE.read_bytes()
source = source_bytes.decode()
lines = source.splitlines(keepends=True)
changed_lines = list(lines)
claims = []
edits = []
current_header = None
header_pattern = re.compile(
    r"theorem (\w+) : (block|CutRow) (\w+) (\d+) (\d+) (\d+)"
    r"(?:\s*=\s*true)? := by"
)
call_pattern = re.compile(
    r"  apply q08 \(ar:=(\d+)\) \(rows:=(\d+)\) \(d:=(\d+)\)"
)


def split_leaves(start, count, depth):
    if depth == 0:
        return [[start, count]]
    first = count // 2
    return split_leaves(start, first, depth - 1) + split_leaves(
        start + first, count - first, depth - 1
    )


def expanded(forest, level, arity, leaves):
    return [
        [forest, level, state, arity]
        for start, count in leaves
        for state in range(start, start + count)
    ]


for index, line in enumerate(lines):
    plain = line.rstrip("\n")
    if plain.startswith("theorem "):
        current_header = plain
    if "apply q08 " not in plain:
        continue
    header = header_pattern.fullmatch(current_header or "")
    call = call_pattern.fullmatch(plain)
    assert header is not None, (index + 1, current_header)
    assert call is not None, (index + 1, plain)
    name, kind, forest, level, start, count = header.groups()
    level, start, count = map(int, (level, start, count))
    arity, rows, old_depth = map(int, call.groups())
    new_depth = 0
    while (count + (1 << new_depth) - 1) // (1 << new_depth) > CAP:
        new_depth += 1
    assert new_depth <= old_depth
    old_leaves = split_leaves(start, count, old_depth)
    new_leaves = split_leaves(start, count, new_depth)
    old_states = expanded(forest, level, arity, old_leaves)
    new_states = expanded(forest, level, arity, new_leaves)
    assert old_states == new_states
    assert all(0 < n <= CAP for _, n in new_leaves)
    assert sum(n for _, n in new_leaves) == count
    record = {
        "theorem": name,
        "claim_kind": kind,
        "forest": forest,
        "level": level,
        "start": start,
        "count": count,
        "arity": arity,
        "rows_depth_unchanged": rows,
        "old_depth": old_depth,
        "new_depth": new_depth,
        "old_leaves": old_leaves,
        "new_leaves": new_leaves,
        "expanded_state_arity_sha256": hashlib.sha256(
            json.dumps(old_states, separators=(",", ":")).encode()
        ).hexdigest(),
    }
    claims.append(record)
    if new_depth != old_depth:
        new_line = line.replace(f"(d:={old_depth})", f"(d:={new_depth})")
        assert new_line != line
        changed_lines[index] = new_line
        edits.append({"line": index + 1, "old": line, "new": new_line})

assert len(claims) == 52
assert len(edits) == 38
candidate = "".join(changed_lines)
candidate_bytes = candidate.encode()
assert len(candidate_bytes) <= 512 * 1024
restored = candidate.splitlines(keepends=True)
for edit in edits:
    assert restored[edit["line"] - 1] == edit["new"]
    restored[edit["line"] - 1] = edit["old"]
assert "".join(restored) == source
marker = "theorem PEqualNP.Outside.L_meta_670 :"
assert source.count(marker) == candidate.count(marker) == 1
assert source[source.index(marker) :] == candidate[candidate.index(marker) :]
imports = lambda text: [x for x in text.splitlines() if x.startswith("import ")]
assert imports(source) == imports(candidate)
assert SOURCE.read_bytes() == source_bytes
OUTPUT.write_bytes(candidate_bytes)
summary = {
    "status": "STATIC CHECKS ONLY; FULL LEAN BUILD AND CHECKER UNVALIDATED",
    "utc": datetime.now(timezone.utc).isoformat(),
    "source": str(SOURCE),
    "source_sha256": hashlib.sha256(source_bytes).hexdigest(),
    "candidate": str(OUTPUT),
    "candidate_sha256": hashlib.sha256(candidate_bytes).hexdigest(),
    "candidate_bytes": len(candidate_bytes),
    "size_headroom": 512 * 1024 - len(candidate_bytes),
    "cap": CAP,
    "claims": len(claims),
    "changed_claims": len(edits),
    "states_in_cells_claims": sum(c["count"] for c in claims),
    "old_state_batches": sum(len(c["old_leaves"]) for c in claims),
    "new_state_batches": sum(len(c["new_leaves"]) for c in claims),
    "maximum_new_state_batch": max(n for c in claims for _, n in c["new_leaves"]),
    "state_census_by_forest": dict(Counter({
        root: sum(c["count"] for c in claims if c["forest"] == root)
        for root in sorted({c["forest"] for c in claims})
    })),
    "invariants": {
        "source_untouched": True,
        "reversible_exact_bytes": True,
        "exact_final_declaration_unchanged": True,
        "imports_unchanged": True,
        "per_state_forest_level_index_arity_unchanged": True,
        "row_split_depths_unchanged": True,
        "panel_and_mixed_proofs_unchanged": True,
        "all_edits_are_numeric_cells_depth_only": True,
    },
}
(HERE / "manifest.json").write_text(
    json.dumps({**summary, "claims_detail": claims, "reversible_edits": edits}, indent=2)
    + "\n"
)
print(json.dumps(summary, indent=2))
