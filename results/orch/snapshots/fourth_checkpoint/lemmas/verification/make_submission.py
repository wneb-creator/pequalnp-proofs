#!/usr/bin/env python3
"""Assemble the exact L-meta-650 proof only from a verified target candidate."""

import argparse
import hashlib
import json
import re
from pathlib import Path

from generate_dnf_certificate import generate


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("candidate", type=Path)
    parser.add_argument("statement", type=Path)
    parser.add_argument("--wire", type=int)
    parser.add_argument("--validate-only", action="store_true")
    args = parser.parse_args()
    repository = Path(__file__).resolve().parents[4]
    statement = args.statement.read_text().strip()
    expected_statement_hash = "2f423a13954b274d19d1c8766b82e12bb5ea843a124eebfdc6e995defee5b630"
    if hashlib.sha256(statement.encode()).hexdigest() != expected_statement_hash:
        parser.error("statement does not match the exact assigned L-meta-650 statement")
    edges = [(int(a), int(b)) for a, b in re.findall(r"\((\d+),\s*(\d+)\)", statement)]
    if len(edges) != 52 or len(set(edges)) != 52:
        parser.error("statement does not contain exactly the 52 distinct posted edges")
    if not all(0 <= a < 13 <= b < 26 for a, b in edges) or "C.size ≤ 63" not in statement:
        parser.error("statement does not have the posted vertex ranges and gate budget")
    data = json.loads(args.candidate.read_text())
    gates = data.get("gates") if isinstance(data, dict) else data
    if not isinstance(gates, list):
        parser.error("candidate must be a gate list or contain a gates field")
    if len(gates) > 63:
        parser.error("candidate exceeds the posted 63-gate budget")
    if isinstance(data, dict) and data.get("n_inputs", 26) != 26:
        parser.error("candidate is not a full 26-input circuit")
    default_wire = data.get("output", 26 + len(gates) - 1) if isinstance(data, dict) else 26 + len(gates) - 1
    wire = args.wire if args.wire is not None else default_wire
    if type(wire) is not int or wire < 0:
        parser.error("output must be a natural wire index")
    certificate, environment, _ = generate(26, gates)
    actual = set(environment[wire]) if wire < len(environment) else set()
    expected = {frozenset(edge) for edge in edges}
    if actual != expected:
        parser.error(
            f"candidate is not the posted function: {len(expected - actual)} missing and "
            f"{len(actual - expected)} extra prime terms"
        )
    if args.validate_only:
        print(f"Exact target candidate: {len(gates)} gates, output {wire}, 52 prime terms")
        return
    target = repository / "lean/PEqualNP/Outside/L_meta_650.lean"
    if target.exists():
        parser.error("target file already exists; inspect it before replacing any work")
    verifier = repository / "results/orch/lemmas/reduction_analysis/DNFVerifierMono.lean"
    text = verifier.read_text()
    text += "\nnamespace PEqualNP.Outside.L_meta_650_aux.Submission\n\n"
    text += "open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_650_aux.DNF\n\n"
    text += "def circuit : Circuit :=\n  ⟨[\n"
    gate_lines = [f"    ⟨GateOp.{'and' if op == 0 else 'or'}, [{a}, {b}]⟩" for op, a, b in gates]
    text += ",\n".join(gate_lines) + f"\n  ], {wire}⟩\n\n"
    text += "def certificate : List Form :=\n  " + json.dumps(certificate, separators=(",", ":")) + "\n\n"
    output_terms = [list(edge) for edge in sorted(edges)]
    text += "def outputTerms : Form :=\n  " + json.dumps(output_terms, separators=(",", ":")) + "\n\n"
    text += """set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem certificate_valid : checkCircuit 26 circuit certificate = true := by
  decide +kernel

theorem output_terms : (initial 26 ++ certificate).getD circuit.output [] = outputTerms := by
  rfl

end PEqualNP.Outside.L_meta_650_aux.Submission

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
"""
    text += "theorem PEqualNP.Outside.L_meta_650 : " + statement + " := by\n"
    text += """  let C := PEqualNP.Outside.L_meta_650_aux.Submission.circuit
  have checked := PEqualNP.Outside.L_meta_650_aux.Submission.certificate_valid
  refine ⟨C, PEqualNP.Outside.L_meta_650_aux.DNF.checkCircuit_monotone 26 C _ checked, ?_, ?_⟩
  · decide
  · intro x
    rw [PEqualNP.Outside.L_meta_650_aux.DNF.checkCircuit_eval 26 C _ checked
      (List.ofFn x) (by simp)]
    change PEqualNP.Outside.L_meta_650_aux.DNF.eval
      ((PEqualNP.Outside.L_meta_650_aux.DNF.initial 26 ++
        PEqualNP.Outside.L_meta_650_aux.Submission.certificate).getD
        PEqualNP.Outside.L_meta_650_aux.Submission.circuit.output []) (List.ofFn x) = true ↔ _
    rw [PEqualNP.Outside.L_meta_650_aux.Submission.output_terms]
    simp [PEqualNP.Outside.L_meta_650_aux.DNF.eval,
      PEqualNP.Outside.L_meta_650_aux.DNF.evalMonomial,
      PEqualNP.Outside.L_meta_650_aux.Submission.outputTerms, List.ofFn_succ,
      Fin.exists_iff, Prod.mk.injEq, or_and_right, exists_or, and_assoc,
      and_or_left, or_assoc]
"""
    try:
        with target.open("x", encoding="utf-8") as output:
            output.write(text)
    except FileExistsError:
        parser.error("target file appeared during assembly; no existing file was overwritten")
    print(f"Wrote {target}; Lean build and repository checker are still required")


if __name__ == "__main__":
    main()
