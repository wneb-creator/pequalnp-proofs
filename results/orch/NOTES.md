# pequalnp-pilot-68: L-meta-670

Assigned 2026-11-25 04:48:24 UTC. Parent alone holds and renews lease.

Target: ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 15

Allowed project module: PEqualNP.Defs. Three live reductions already, so seek complete proof. Root controls final file and git. Agents use their own files under results/orch/lemmas and append notes. No sorry, axioms, native_decide, or changes to project definitions.

## Structural lane (04:55 UTC)
Computed the 12 graph automorphisms by exhaustive permutation check; confirmed pair orbit representatives (0,1),(0,2),(0,3),(0,4),(0,6),(4,6), unary reps 0 and 4. Generated Structural.lean with finite bijectivity/orbit proofs and graph invariance by associative/commutative Boolean identities. Awaiting Lean installation to check it.

## Counterexample lane, initial computation

- Standard circuit semantics offer no obvious malformed-wire shortcut.
- Exhaustive Python enumeration gives independent-set count by size: 1, 9, 24, 21, 3; alpha=4, vertex-cover number=5; 12 automorphisms and 6 unordered-pair orbits.
- Constructed 16-gate cover circuit and checked all 512 inputs. Existing L_meta_1001.lean already checks precisely this upper bound, so no duplicate Lean partial is needed.
- Reproducible bit-parallel heuristic 15-gate search is running from deleted-gate variants of the 16-gate circuit. A failure to find a witness is not a lower-bound proof.

## Assembly findings

- All14 first-gate cases L_meta_1665..1678 are merged and exact, but imports are only Defs.
- L_meta_2440 (27,494 bytes) already proves full ordinary first-gate normalization, including constants/copies and12 graph automorphisms. Renamed into results/orch/lemmas/Assembly.lean as L_meta_670.Normalize.normalized (not yet compiled; Lean path pending).
- L_meta_4334 (36,153 bytes) is priority normalizer AND before NOT before OR, exactly first hypothesis of R670_419.
- L_meta_2444 (379,693 bytes) packages all six AND cases; L_meta_2442 (511,700 bytes) packages both NOT cases. L2446 OR bundle absent.
- Live extraction in certificate framework removes constants/copies; alternative assembly works on first Live move, requiring signature coordinate permutation under graph autos.

- Parent chose priority normalization; prepared results/orch/lemmas/Normalize.lean from L_meta_4334, with helpers under L_meta_670.Normalize and final helper normalized. Pending compile.

## First-gate/certificate audit 2026-11-25T04:52:04.947518+00:00

- All fourteen first-gate cases L_meta_1665 through L_meta_1678 are checked upstream, but combined source is 5.79MB; exact declaration dedup remains 2.87MB. Their proof engines differ.
- Better AND bundle: L_meta_2444 (379693 bytes), all six pair cases; NOT bundle: L_meta_2442 (511700 bytes), both unary representatives. OR bundle L_meta_2446 remains reduced.
- L_meta_2442.Binary.petersen_binary_bound (through line3407) proves every correct circuit has at least14 non-NOT gates; thus any hypothetical size<=15 circuit has at most1 NOT. The rest of2442 exploits no more NOT gates after a first NOT. This may support a smaller direct root certificate.
- Defs/LratEncoding only encodes monotone AND/OR circuits; generic NOT-circuit SAT proof requires independent soundness machinery. Existing first-gate case files instead use live-wire backward enumeration and restriction certificates, with all data checked using decide +kernel.
- All-bundle whitespace-insensitive declaration dedup still >2MB (AND+NOT+six OR cases), so straightforward copy is not enough. Need semantic/generic certificate consolidation or a direct proof.

- Normalize.lean cleanup: replaced custom inductive Stat with standard Bool⊕ℕ and Sum constructors, preserving compiler logic; now36,038 bytes/716 lines. Still awaiting Lean availability.

## Counterexample lane, SAT setup (04:53 UTC)

- Bundled CaDiCaL found in Lean toolchain. A normalized 15-gate synthesis CNF on 70 samples (all 58 negatives + 12 minimal positive pairs) has 3,675 variables / 66,583 clauses / 1.05 MB. Four-minute solver run in progress. This has no Lean soundness proof and no UNSAT certificate yet.
- Validated the CNF encoder by fixing the known 16-gate circuit on all 512 assignments: CaDiCaL returns SAT, decoded circuit matches the truth table on all 512 inputs.

## Structural lane update 2026-11-25T04:55:35.683355+00:00
L2440 already supplies complete first-gate normalization and the same automorphism orbits; new Structural.lean is redundant. L2442 lines4001–4052 already supplies `rename` and `live_rename`; new LiveMap.lean is an uncompiled independent draft, not needed if reusing that framework.
Library scan: no compact checked general C4-free monotone m+tau-1 bound found; root R612 still has reductions. L1737/L3525 require acyclic. L616 requires 3-regular and proves only n+tau. L2551 is exact augmented OR0,4 bound but 362KB certificate.
L2442 size anatomy: Binary174KB, base engine263KB (26KB hex), tagged engine52KB, final tables23KB (9KB hex). Across 14 first-gate proofs, unique hexadecimal data alone is1,135,707 bytes, preventing naive merging under512KiB. New sparse root certificate is likely required.

## Counterexample lane, exact-library emitter (04:57 UTC)

- `emit_linkn.py` mirrors `LinkN.enc` plus `LinkN2.fLex`; 70-row case has 109,336 clauses (3.45 MB), max DIMACS variable 67,789. Root assigned assembly agent to inline the corresponding Lean soundness route. Python output is not yet compared against Lean evaluation.
- Fixed the known 16-gate circuit after a topological lexicographic reorder: this encoding returns SAT, validating consistency of the generated constraints with a real witness.
- Stochastic search finished 1,058,400,000 mutations with no witness; best error count was 5/512.

## SAT soundness extraction

Prepared SatSoundness.lean from Checker+LinkN+LinkN2 and only used Shannon wire lemmas, under L_meta_670.Sat; only imports Mathlib and Defs. Expanded wdt tactics, stripped comments, replaced custom Trie with BinaryTree (Option Nat), named computational section, and removed pad instance by making its definition an abbrev. Fixed code 95821 bytes. Still has three source structures Model/Valid/NF (manual-review issue), and not compiled yet per parent instruction.

## First-gate strategy update 2026-11-25T05:01:12.345160+00:00

- Extracted existing non-NOT>=14 proof to results/orch/lemmas/NonNot.lean (175253bytes including wrapper atMostOneNot). Awaiting project compilation.
- Prototype direct search search_root.py reached10 surviving root orbit/keep cases,171 depth2 states,2358 depth3 states using all true/false separation and cube/clipped pool bounds. This was search evidence only, not a certificate. Structural agent added search_rect.py.
- Root found existing full candidate PR12184 by benoitrazet (516536bytes), already using a stronger free-complement binary bound>14 and monotone bound>15. Switched effort to runtime optimization rather than duplicating the search.
- Optimized12184.lean adds explicit forcing of packed batch wire signatures and coverage values before rowCut loops. This preserves semantics via forcePackedList_eq and forceBatch_eq. BenchForce.lean (core Lean only) compiled successfully with Lean4.36; full candidate variant awaits build/profile.
