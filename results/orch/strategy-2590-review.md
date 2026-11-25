# Independent review for L-meta-2590

2026-11-25, resumed after the second desk HTTP 410. No desk calls, builds, commits, pushes, or credential access were performed by this reviewer.

## Assignment and lease evidence

The third saved assignment names L-meta-2590: no monotone fan-in-two circuit of at most 19 gates computes the ten-variable Petersen edge function. The listed edges are 01, 12, 23, 34, 40, 05, 16, 27, 38, 49, 57, 79, 96, 68, 85.

The response reports holding=5 and the note: “you hold 5 gaps, the most one handle may hold at once; release one to get another”. Its terms were issued at 2026-11-25T15:07:28.124Z; the returned expiry is 2026-11-25T15:35:27.263Z. No owner/pilot identifier or new-versus-existing-lease flag appears among the response fields. This evidence does not establish whether a different pilot originally obtained this lease.

The saved join instructions say that another=1 allows up to five leases, each with its own lease/file/PR (lines 99–101), and that a lease lasts 20 minutes after renewal (lines 107–113). They also say HTTP 410 may mean a step was settled or withdrawn. Both saved error responses have cache-control:no-store and the same body: “no such live lease: it expired or was released. Ask /desk/next again.” These records do not identify the cause of the earlier lease losses. An earlier terms timestamp alone cannot establish that cause or ownership.

## Bounded repository search

Discovered candidate files with Petersen names, explicit size-20 bounds, or size-19 rejection statements, then inspected bounded declaration signatures. The main name search found 137 files containing Petersen/petersen and relevant lower-bound declarations. A second search checked every relevant declaration for numeric 19/20 size bounds. A direct repository search for size <=19 or size >=20 expressions checked additional files whose naming did not mention Petersen. No unconditional full-strength monotone Petersen lower bound was found.

Important exclusions:

- The working `lean/PEqualNP/Outside/L_meta_2592.lean` is this job's earlier partial, not a recorded solution to the monotone gap.
- `L_meta_8021.lean:4` simultaneously assumes every gate is not NOT and notCount >=1. Its contradiction is vacuous for monotone circuits and provides no lower-bound argument.
- `L_meta_1483.lean:1058` is a 14-variable Fano/Heawood bound, not Petersen.
- `L_meta_5238.lean:3175` proves only at least 15 non-NOT gates for the ten-variable Petersen function.
- `L_meta_2778.lean:6829` and `:7587` prove a 15-gate bound for a nine-variable restriction, not the desired ten-variable 20-gate bound.

The three existing reductions for the active step remain conditional:

- `R_meta_2590_1.lean`: two remaining-18-gate boundary-row searches, depending on whether the removed first gate is AND or OR.
- `R_meta_2590_932.lean`: three normalized trace searches, first edge-OR, nonedge-OR, or edge-AND. It already removes nonedge atomic ANDs, duplicates, constants, and uses Petersen automorphisms. This is the strongest reusable checked search preprocessing located.
- `R_meta_2590_491.lean`: two row obstructions after eliminating an input boundary gate, split by its AND/OR behavior.

The first-gate reductions or a semantic conversion to a read-one circuit are feasible routes, but their remaining finite/structural obstructions are not solved by the existing partials. A lower bound assuming joint IsReadK 1 cannot be applied to arbitrary Monotone2 circuits without such a conversion.

## Compiled partial independently approved

`results/orch/lemmas/ReadOnePetersen2590.lean`, SHA256 `3da4d332bd36fd1350557771ebdeaf4cc1e56bee717c70f25bf9df69094508eb`, 1447 lines.

Lines 8–1393 are an exact substring of checked `L_meta_6369.lean`. The new suffix supplies Petersen's 15 edges, absence of four-cycles, and minimum vertex-cover size 6. The inherited theorem gives edges + cover <= circuit size + 1; hence size >=20. The conclusion explicitly requires IsAO2 and joint IsReadK 1. It is a correct partial, not the posted unrestricted theorem. Both captured build logs are empty; the parent reported exit 0. Static scans found no forbidden root marker, string literal, sorry, axiom, native_decide, or attributes. The only import is Defs; option changes use permitted limits with `in`.

## Special L-meta-1035 status

No exact L-meta-1035 proof path exists in the current checkout, and the exact path has no local git history. The saved public head and gap snapshots contain no exact L-meta-1035 identifier (similarly numbered 10351, etc. are different steps). The gap snapshot is timestamped 2026-11-25T14:18:23.713Z. This establishes only absence from these local records, not whether the older statement was refuted, withdrawn, or held. No claim about its current public status is justified by these records.

## Completed follow-up before desk error

The bounded edge-deletion search found `L_meta_9781.lean:7239/7251`: no monotone circuit of at most 16 gates computes the graph obtained from Petersen by deleting adjacent edges 01 and 12. Its conclusion is an exact graph-function lower bound of 17. No one-edge-deleted lower bound of 18 was located. `R_meta_4137_1.lean` and `R_meta_4137_252.lean` contain conditional reductions for the relevant promise x0 AND x1 = false and size at most 17. They do not discharge that promise lower bound.

Setting an atomic edge-AND gate false preserves the other minimal true rows but may leave cubic minterms containing the removed edge. Consequently an exact deleted-graph lower bound cannot be applied without a further cleanup or promise argument. Research stopped immediately on the parent's DESK_ERROR instruction.

`PetersenFormula2590.lean`, SHA256 `8ac735714ecf9f96fe2132dd659584f9142cc15a688894a7682612d6ca9b2ccb`, 907 lines, received static approval pending compilation. Its first 802 lines match selected checked blocks of L_meta_3793 after namespace/whitespace normalization. The new theorem gives at least 21 leaves for a positive Petersen formula and at least 20 gates only for a binary-earlier circuit whose internal wires occur at most once among the output and all gate inputs. The structural restrictions are explicit. It contains a copied private RawFormula datatype and a decidability instance, which would require the join instructions' declaration-review disclosure if retained in a final PR.

## Final preservation review after third desk error

Approved only as uncompiled branch checkpoints, not as proofs or PR-ready files:

- Normalize2590.lean: `9b9cf265e4b837e6ed18197548a5e7931c24e5c5467e2db82f5a544c2eae58b4`.
- Singleton2590.lean: `ae1a21411954697189cc40e477a260e5c1d9090533aafe104c8380734209c0a9`. Its second compile failed at line 633; the captured log confirms the unresolved Boolean simplification.
- StrongNormal2590.lean: `72254debc32133711a12a78fde17ea985bc6a444d155f9c14305ef38a72f7d2c`. Never compiled. Compared with the previously reviewed 2583 draft, only namespace changes and local elaboration edits were made.
- PetersenFormula2590.lean: `b0431d957c39d68eb53a346c4877006e35a26d0a6db9d95bf28efb87775a66e4`. This supersedes the earlier hash above; the delta adds two permitted scoped heartbeat limits. Still uncompiled.
- PetersenReaders2590.lean: `fb994b39b1ca9a9b418dce811dafb688872d160192f04ce7e7a23c60e461b390`. The conditional counting argument is sound: if all ten inputs have at least two occurrences, at most 19 binary gates and liveness leave no repeated internal read. Still uncompiled.

All five files passed static forbidden-text/import/option checks. Search archives contain no counterexample: the best stochastic candidate has two extremal-row errors and 22 total truth-table errors. The SAT query was interrupted with no SAT or UNSAT result. Its documentation explicitly records that the whole implementation and combined normalizations were not fully independently reviewed, and that exact-19 UNSAT alone would not exclude smaller irredundant witnesses. Search and SAT source/log archives passed a bounded credential-pattern scan. A stale “search running” label in best-analysis.json was identified and corrected by its author to terminated/no witness.
