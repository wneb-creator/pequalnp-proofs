# L-meta-1479 orchestration notes

Lease acquired: 2026-11-25T09:33:51Z after nine null desk replies. Only root holds and renews this lease.
The task asks for at most 27 normalized binary AND/OR gates computing Fano incidence on 14 inputs, with a double re-read incidence.
Exact desk statement: results/orch/statement.txt. Full assignment remains in scratch desk-assigned.json.
Lean binaries: /tmp/oec/pequalnp-pilot-81/lean-4.36.0-linux/bin. Cache, verifier and definitions are ready.
Main proof file is root-owned: lean/PEqualNP/Outside/L_meta_1479.lean.
Agents own separate files under results/orch/lemmas. No agent except root may call the desk, commit or push.

## Checked partial results

- A normalized, correct 27-gate star baseline, without the required double re-read.
- An explicit 28-gate circuit satisfying every posted clause except the 27-gate bound.
- Trace existence, finite gate/trace checks, and a 21-positive/37-negative correctness certificate.
- Fano no-four-cycle and strict Hall properties; only whole bipartition sides are vertex covers of size at most seven.
- Final AND singleton-support restriction; derivative-support and single-gate substitution lemmas.
- Complete positive-support normalization: replace unsupported gates by another incidence edge, preserving gate count, output, and both marked traces. Every resulting gate turns on for some positive edge input.

These are partials. The exact posted theorem is not yet proved. Three reductions are already live globally, so a fourth reduction cannot be submitted.

## Search status and scope

- Thirty-two internal 28-gate seeds are verified on all 16,384 inputs and both traces.
- Captured 27-gate near-candidates compute Fano minus one edge; none solves the task.
- C6 at eight gates is computationally UNSAT both with distinct and repeated operands. This is not a Lean certificate.
- Sequential deletion of private inputs reduces the shared-edge three-star case to repeated-input C6; a private marked edge instead leaves C6 plus one leaf. Formal elimination/certificate work remains.
- Current focus: four-cap points {0,1,4,6}, twelve edges, ten relevant inputs. A 15-gate double-quiet witness would splice into a full 27-gate witness.
- The machine has five logical CPUs. Search workers are coordinated with Lean builds; avoid oversubscription.

Root must renew before long runs and every ten minutes, preserve all compiled progress promptly, independently review every pushed diff, and keep any eventual PR to the exact single named Lean file.
