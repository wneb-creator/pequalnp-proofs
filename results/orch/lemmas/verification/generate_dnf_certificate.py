#!/usr/bin/env python3
"""Generate finite DNF normalization certificates for binary monotone circuits."""

import argparse
import hashlib
import json
from pathlib import Path


def normalize(terms):
    ordered = sorted(set(map(frozenset, terms)), key=lambda t: (len(t), sorted(t)))
    result = []
    for term in ordered:
        if not any(old <= term for old in result):
            result.append(term)
    return result


def equivalent_by_subsumption(left, right):
    return all(any(b <= a for b in right) for a in left) and all(
        any(a <= b for a in left) for b in right
    )


def generate(n, gates):
    environment = [[frozenset([i])] for i in range(n)]
    certificates = []
    raw_counts = []
    for gate_index, gate in enumerate(gates):
        if not isinstance(gate, list) or len(gate) != 3:
            raise ValueError(f"Gate {gate_index} is not a three-integer array")
        op, a, b = gate
        if any(type(v) is not int or v < 0 for v in gate) or op not in (0, 1):
            raise ValueError(f"Gate {gate_index} is not binary AND/OR with natural references")
        left = environment[a] if a < len(environment) else []
        right = environment[b] if b < len(environment) else []
        raw = [x | y for x in left for y in right] if op == 0 else left + right
        normal = normalize(raw)
        if not equivalent_by_subsumption(raw, normal):
            raise AssertionError(f"Normalization certificate failed at gate {gate_index}")
        raw_counts.append(len(raw))
        certificates.append([sorted(term) for term in normal])
        environment.append(normal)
    return certificates, environment, raw_counts


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--inputs", type=int, required=True)
    parser.add_argument("--wire", type=int)
    args = parser.parse_args()
    if args.inputs < 0:
        parser.error("--inputs must be nonnegative")
    raw_bytes = args.input.read_bytes()
    data = json.loads(raw_bytes)
    gates = data["gates"] if isinstance(data, dict) else data
    if not isinstance(gates, list):
        parser.error("input must contain a gate list")
    certificates, environment, raw_counts = generate(args.inputs, gates)
    wire = args.wire if args.wire is not None else args.inputs + len(gates) - 1
    if wire < 0:
        parser.error("output wire must be nonnegative")
    output_dnf = environment[wire] if wire < len(environment) else []
    result = {
        "source_sha256": hashlib.sha256(raw_bytes).hexdigest(),
        "n_inputs": args.inputs,
        "gates": gates,
        "output": wire,
        "certificates": certificates,
        "output_dnf": [sorted(term) for term in output_dnf],
        "raw_term_counts": raw_counts,
        "normal_term_counts": list(map(len, certificates)),
        "status": "generated finite certificate; Lean verification required",
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    lean_literal = json.dumps(certificates, separators=(",", ":"))
    args.output.with_suffix(".lean.txt").write_text(
        "def generatedCertificate : List (List (List Nat)) :=\n  "
        + lean_literal
        + "\n"
    )
    print(json.dumps({
        "gates": len(gates),
        "output_terms": len(output_dnf),
        "largest_raw": max(raw_counts, default=0),
        "largest_normal": max(map(len, certificates), default=0),
        "total_certificate_terms": sum(map(len, certificates)),
    }))


if __name__ == "__main__":
    main()
