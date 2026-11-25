# Status and library review

2026-11-25, status_review agent.

## L-meta-1035 status

- No exact matching file or commit in updated upstream history through 93ae4a0b.
- Complete open pull-request census had 830 entries and no title/body/head match for 1035.
- GitHub search endpoint returned HTTP 422 (repository not searchable); direct closed census was still running when assignment changed.
- Local checker supports refute mode, proving the negation of the recorded statement. Current join instructions ask refutations to use the posted negated twin, so desk metadata controls routing.

## L-meta-2592 findings

- Gap already has reductions_live = 3. Existing reductions R_meta_2592_271, _318, _408 exhaust the stated maximum.
- R_meta_2592_271 splits into a lower bound of 15 binary gates and exclusion of circuits with 1 through 4 NOT gates.
- R_meta_2592_318 cuts the last NOT, leaving a fan-in-two prefix and a monotone suffix; its separator claim remains difficult.
- R_meta_2592_408 normalizes invalid reads, NOT arity, and output, then asks a normalized lower bound.
- Checked L_meta_6194 proves the full Petersen function needs at least 15 non-NOT gates. It is self-contained (3255 lines, 148848 bytes), importing only Mathlib and PEqualNP.Defs. The proof can be copied under fresh helper namespaces if required, since importing the outside module is forbidden by the assignment.
- L_meta_6194_aux.petersen_binary_lower is the central lemma; notCount_eq_filter_isNotGate relates its NOT count to PEqualNP.NotBracket.notCount. Together with nonNotCount_add_notCount, it excludes size-at-most-19 circuits with at least 5 NOT gates.
- L_meta_5238 contains essentially the same proof and handles an extra precomputed OR wire.
- Several checked Petersen-minus-one-vertex bounds exist (L_meta_2048, L_meta_2442, L_meta_3176, L_meta_2758, L_meta_3415), typically 15 or 16 gates with specified first gates. They are long self-contained proofs (often 8000+ lines), with gate-elimination and branch-count methods.

## Remaining obstacle

A proof excluding 1–4 NOT gates in a 19-gate circuit is not supplied by the binary-gate floor. No existing full 20-gate lower bound was found in the reviewed local sources. A new reduction is disallowed by the three-live-reductions ceiling unless one closes.

## Stronger floor found by orchestrator

- L_meta_6581 proves a stronger full Petersen lower bound: at least 16 binary (non-NOT) gates, even allowing free wire complementation in its certificate calculus.
- Adapted that self-contained certificate into results/orch/lemmas/NotCountFloor.lean, under PEqualNP.Outside.Pilot118NotCount16. The new lemma no_small_with_four_nots combines the 16-binary lower bound with the count of NOT gates to exclude every size-at-most-19 circuit containing at least four NOTs.
- The stronger source imports only PEqualNP.Defs and declares no custom data types/instances. File remains below 512 KiB and has no forbidden format markers. Lean build is pending toolchain/cache installation; no claim of successful compilation yet.
- Table search over 712 Petersen-related checked statements found no general binary floor 17 or higher. L_meta_5236 handles first gate x0 OR x2 with 3–4 NOTs in the suffix and uses a similar signed certificate backbone.
