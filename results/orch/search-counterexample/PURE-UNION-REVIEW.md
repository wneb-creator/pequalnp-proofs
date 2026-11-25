# Independent pure-union model review

Approved for the planned restricted search: no encoding or reconstruction blocker found.

- Each branch selects exactly one earlier wire. The two implication clauses correctly equate every branch bit with the selected wire bit. Parent indices increase, removing branch exchange symmetry without losing a circuit. Parent-mask incomparability removes only redundant unions; repeated useful gates remain permitted, so smaller solutions can be padded with duplicate two-input unions.
- A computed mask covers a pencil/cap requirement exactly when it contains the four target lines and avoids the cap. Taking the free conjunction of all computed masks containing the target therefore rejects every required cap while accepting the target singleton inputs. Input wires cannot themselves contain a four-line target, so excluding them from coverage candidates is harmless.
- Independent enumeration of all 560 cap assignments found exactly 54 maximal disjoint caps per target and 702 requirements altogether. Every smaller disjoint cap extends to one of these maximal caps. The saved requirement list agrees exactly.
- All 39 affine Singer actions preserve the requirement set. Their unordered input-pair orbits have representatives `(0,1)` and `(0,2)`, matching the first-OR restriction. The fixed-baseline control intentionally bypasses that restriction.
- Independent replay of the saved 39-OR witness verified every parent is earlier, parent masks are incomparable, recorded gate masks are correct, all 702 requirements are covered, and all 7,280 output/cap comparisons pass.

A 38-OR witness would still require Lean translation and verification. An UNSAT result would rule out only circuits whose internal gates compute pure line unions, with free conjunctions at the outputs; it would not rule out the broader canonical free-AND model or prove the posted lower bound.

Exact source and witness hashes are recorded in `pure-union-independent-audit.json`. The reproducible independent checker and complete output are `audit_pure_union.py` and `pure-union-independent-audit.log`. No heavy search or Lean compilation was performed for this review.
