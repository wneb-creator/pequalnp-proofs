#!/usr/bin/env python3
"""Validate a PHP(5,4) RUP certificate and emit a kernel-checkable Lean module."""

import argparse
import json
import re
from pathlib import Path


def input_database():
    rows = [[2 * (4 * p + h) for h in range(4)] for p in range(5)]
    blocks = [
        [2 * (4 * p + h) + 1, 2 * (4 * q + h) + 1]
        for h in range(4) for p in range(5) for q in range(p + 1, 5)
    ]
    return rows + blocks


def checked_ints(value, upper, label):
    if not isinstance(value, list):
        raise ValueError(f"{label} must be a list")
    if any(type(k) is not int or not 0 <= k < upper for k in value):
        raise ValueError(f"{label} contains an out-of-range integer")
    return value


def find_trace(database, clause):
    false_literals = set(clause)
    trail = []
    while True:
        progressed = False
        for index, known in enumerate(database):
            remaining = [literal for literal in known if literal not in false_literals]
            if not remaining:
                return trail + [index]
            if len(remaining) == 1 and remaining[0] ^ 1 not in false_literals:
                trail.append(index)
                false_literals.add(remaining[0] ^ 1)
                progressed = True
                break
        if not progressed:
            raise ValueError("candidate clause is not RUP by unit propagation")


def replay(database, clause, trail):
    false_literals = set(clause)
    for position, index in enumerate(trail):
        remaining = [literal for literal in database[index] if literal not in false_literals]
        if not remaining:
            if position + 1 != len(trail):
                raise ValueError("trail contains unused indices after its conflict")
            return
        if len(remaining) != 1:
            raise ValueError("trail points to a clause that is neither unit nor false")
        false_literals.add(remaining[0] ^ 1)
    raise ValueError("trail ends without a falsified known clause")


def lean_list(values):
    return "[" + ", ".join(str(k) for k in values) + "]"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--module", default="Candidate")
    parser.add_argument("--normalized-json", type=Path)
    args = parser.parse_args()
    if not re.fullmatch(r"[A-Z][A-Za-z0-9_]*", args.module) or "_root_" in args.module:
        raise ValueError("module must be a simple capitalized Lean identifier")
    data = json.loads(args.certificate.read_text())
    if not isinstance(data, dict) or not isinstance(data.get("steps"), list):
        raise ValueError("certificate must be an object with a steps list")
    database = input_database()
    steps = []
    for number, step in enumerate(data["steps"]):
        if not isinstance(step, dict):
            raise ValueError("each step must be an object")
        clause = checked_ints(step.get("clause"), 40, f"step {number} clause")
        if len(set(clause)) != len(clause):
            raise ValueError("duplicate literals must be removed before certification")
        trail = step.get("trail")
        if trail is None:
            trail = find_trace(database, clause)
        trail = checked_ints(trail, len(database), f"step {number} trail")
        replay(database, clause, trail)
        steps.append({"clause": clause, "trail": trail})
        database.append(clause)
    if not any(not step["clause"] for step in steps):
        raise ValueError("certificate does not contain an empty learned clause")
    count = len(steps)
    entries = ",\n".join(
        f"    ({lean_list(step['clause'])}, {lean_list(step['trail'])})" for step in steps
    )
    namespace = f"PEqualNP.Outside.L_meta_9248.{args.module}"
    source = f"""import RUPHarness

namespace {namespace}

open PEqualNP.ProofComplexity PEqualNP.Search
open PEqualNP.Outside.L_meta_9248.RUPHarness

def steps : List (List (Literal Board) × List Nat) :=
  ([
{entries}
  ] : List (List Nat × List Nat)).map (fun p => (p.1.map readLiteral, p.2))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem checked : verify input steps = true := by decide +kernel

theorem run : IsRUPRun (PHP 5 4) (learned steps []) := validated_run steps checked

theorem contains_empty : (∅ : Clause Board) ∈ learned steps [] := by decide +kernel

theorem count : (learned steps []).length = {count} := by decide +kernel
"""
    if count <= 12:
        source += """
theorem witness : ∃ ρ : List (Clause (Fin 5 × Fin 4)),
    IsRUPRun (PHP 5 4) ρ ∧ (∅ : Clause (Fin 5 × Fin 4)) ∈ ρ ∧ ρ.length ≤ 12 :=
  validated_refutation steps checked contains_empty (count.le.trans (by decide))
"""
    source += f"\nend {namespace}\n"
    args.output.write_text(source)
    if args.normalized_json:
        args.normalized_json.write_text(json.dumps({"steps": steps}, indent=2) + "\n")
    print(json.dumps({"validated_steps": count, "within_12": count <= 12,
                      "output": str(args.output), "lean_check_pending": True}))


if __name__ == "__main__":
    main()
