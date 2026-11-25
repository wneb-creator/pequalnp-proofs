# Second independent audit: total nine-variable circuit floor

UTC: 2026-11-25T16:14:22.385811+00:00
Verdict: PASS as a checked dependency helper. This supplements lower_bound's separate REVIEW-nine-general-floor.md.
Source: `results/orch1884/lemmas/NineGeneralFloor.lean`
SHA256: `f1b11610b17cdde28749ae7841f9079528fe9e5071729ce8598dfa78b2513370`.

The author reports second-run Lean exit0 and successful export; complete1884-nine-general-second.stdout/.stderr and1884-nine-general-export.stdout/.stderr were independently verified empty.

The compiler generalizes the reviewed monotone compiler without changing pointwise simulation. AND/OR consume one Reach step, including harmless overcharging of nullary/unary gates; NOT consumes no step only in signed mode. NOT constants and first-operand semantics exactly match Circuit evaluation. All default-false references and output reads remain accounted for. Thus circuit_floor bounds actual non-NOT count, not total gates.

The dependency test's constructor-preserving bridge transports MonoBase.Reach into Binary17.Reach. Their wire, Available, graph, and input definitions coincide, as the successful bridge check confirms; the signed floor is fifteen non-NOT gates. count_partition uses the exact library notCount definition. If no paid NOT occurs, the monotone sixteen-gate certificate applies. Otherwise fifteen non-NOT gates plus a positive paid-NOT count give total size at least sixteen. No gate-order, output-validity, or exact-two-input hypothesis is added.

The final Defs-only assembly replaces only the cross-module bridge with its in-file nineSignedFloor, derived from the unchanged checked L4332 signedRoot certificate. It keeps the same proposition and the same count argument. That assembly still needs its complete build. No options, attributes, forbidden constructs, or observed credential material occur in this helper. The reviewer did not author the compiler.
