# L-meta-2590: normalized monotone Petersen SAT proof route

Updated 2026-11-25T15:14:09.969128+00:00. Root owns only the new2590 lease. This agent stopped2583 work on reassignment and makes no desk calls or git mutations.

## Exact target and chosen encoding

Target: every Monotone2 circuit of size≤19 fails the ten-input Petersen edge function. Monotone2 permits nullary/unary AND/OR gates and invalid/default-false reads, so a connected binary search requires a checked normalization argument.

Existing L5050 generic `main` proves arbitrary Monotone2 size≤s circuits yield a satisfying assignment of full `Defs.LratEncoding.enc2` plus one last-gate cube. It does NOT require ReadsBack; its original final14/26 wrapper accepted that assumption but ignored it. The generic proof handles raw semantics, then normalizes padding, output, ordered operands, used gates, and adjacent-independent lex order by a minimizing model argument.

Important naming: unrestricted3-op core `fOp++fSrcAlo++fSrcEq++fGate++fOutAlo++fOutEq` is NOT literally enc or enc2. `enc` additionally has fOut/fPad/fPre/fPadRd/fOrd/fUsed; enc2 additionally fLex. The chosen certified baseline is the full enc2, not a guessed restricted variant.

Rows are sorted15 edge masks plus15 maximal independent masks:
`[3,6,12,17,24,33,50,66,69,104,116,132,138,160,201,208,264,276,288,320,385,402,521,528,548,554,576,640,770,773]`. Python independently enumerated76 total independent sets and15 maximal ones. The implication from a genuine full circuit to CNF only needs these rows inrange, which is kernel checked. No unproved row-completeness premise enters the formal lower-bound implication.

## Frozen compiled proof connection

`/tmp/oec/pequalnp-pilot-99/gap2590/sat_encoding/NormalizedCNF.lean`
SHA256 `1c265db3879d6fef62d1687db0f0ff0f7f89a56b2bf11242d12992581f9115b6`,1492lines70925bytes. Lean exited0 on first run; full logs `normalized-cnf-01.stdout/.stderr`. Original L5050 generic proof renamed into `PEqualNP.Outside.L_meta_2590_aux.SatEncoding`; anonymous noncomputable section explicitly named Encoding; original unrelated external wrapper removed. `circuit_sat_normalized` drops the cube clauses from the inherited coverage theorem. `petersen_from_unsat` concludes the exact posted2590 statement from unsatisfiability of full enc2 on these30 rows. Root/reviewer notified immediately.

`NormalizedReplay.lean`
SHA256 `d6c8de40fecb32c7e0cf0ed197c04b38c6932ee2c13bbf385eeb88383d262b06`,1967lines91645bytes. Lean exited0 on first run; full logs `normalized-replay-01.stdout/.stderr`. Adds the unchanged464-line LRAT kernel replay block from previously checked PetersenReplay, plus generic replay_unsat and exact posted-statement `petersen_of_certificate`. Thus any packed RUP certificate accepted by LRAT.checkW proves the target; no certificate exists yet. Existing frozen lrat_pack.py handles binary/text RUP, dependency slicing, remapping, and packed tokens. Use kernel evaluation for the eventual acceptance proof; no native_decide/bv_decide.

## Exact Lean/Python formula agreement

Counterexample's frozen `gap2590/counterexample/encode.py` SHA256 `6c96af4eb803b7d58646eb55e4987b3f2f177a4da556e535dd02979fa89e7369` was read in full. Its fUsed and fLex loop nesting/literal order agrees with the definitions.

Stronger check: diagnostic `DumpEncoding.lean` directly evaluates actual Lean Defs.enc2 and emits DIMACS. Result `sat_encoding/lean-enc2.cnf` is BYTE-FOR-BYTE identical to counterexample's `petersen19-enc2.cnf`:5609856bytes,138019clauses,maxvariable166533, SHA256 `c34d684c7fd7ee2a38a0e3f205639b7be8fe762771a72781ffca28c84810f96d`. The dump run exited0 with empty stderr. This diagnostic uses IO/strings and is not part of the PR proof source.

## Remaining work and scope

A completed UNSAT certificate is still required. The baseline enc2 CNF and exact proof bridge are ready. The inherited87-cube last-gate split is available if search decomposition is useful; one can prove each cube UNSAT and use the existing checked cover. Added semantic seed restrictions or partial-row function identifications need their own joint-normalization bridge and must not silently modify this certified baseline.

Source before certificate is91645bytes, leaving roughly432KB within a512KiB PR cap; certificate slicing/compression may be important. No solver timeout, heuristic near-solution, or incomplete LRAT prefix is a theorem or refutation.
