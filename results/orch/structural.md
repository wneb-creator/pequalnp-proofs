# Structural strategy notes

- R_meta_2448_263 contains a proved local `pairDirt` lemma: in a C4-free graph, a fan-in-two monotone AND gate owning two disjoint graph edges fires on a nonedge pair among their four endpoints, permitting singleton pairs. This is independent of minimality.
- Its remaining two repair hypotheses hSingle and hPair assert a size-preserving circuit transformation decreasing the count of gates owning disjoint edges, depending on whether the false positive is a singleton or a proper nonedge.
- R_meta_2448_17 instead classifies gate-owned graphs after an unproved crossing condition into double stars or C5; C5 ownership forces a singleton false positive. It then assumes an extension of a star prefix.
- L_meta_8237 (checked) proves that if any gate of a minimum monotone graph circuit is true on a singleton u, replacing that gate by u loses some graph edge disjoint from u. The proof supplies substantial deletion/replacement lemmas. This blocks the naive strategy of simply replacing a dirty singleton gate by that input.
- L_meta_2668 proves every AND gate in a minimum monotone graph circuit is critical on some edge, via eraseGate-to-false.
- A plausible broad route is a size-preserving quadratic monotone normal form, or the lower bound |E| + vertex-cover-number - 1 for graphs without C3/C4. Neither has yet been derived; dirty intermediate gates may accept nonedges filtered by later AND gates, so false positives alone do not contradict correctness.

## Checked scratch components

- `StrongStructural.lean`: 435 lines, pinned Lean exit 0, empty log. Exposes cross_nonedge and star_of_proper_pair_sound (singleton behavior unrestricted). Adapted checked L_meta_7406 plus an explicit star conclusion.
- `DiamondFull.lean`: 202 lines, pinned Lean exit 0, empty log. Three-gate common-input OR/OR/AND block becomes two-gate AND/OR. Arbitrary prefix/suffix allowed; suffix/output may not read the two discarded OR intermediates. Saves one gate and proves the original block cannot occur in a minimum circuit under these conditions.
- `Matching.lean`: 215 lines, pinned Lean exit 0, empty log. Preserves previously computed/shared A=a OR c and B=b OR d, replaces five-gate (A AND B) AND ((a OR d) AND (b OR c)) by three-gate (a AND b) OR (c AND d). Arbitrary prefix/suffix allowed; suffix cannot read four discarded intermediates. Saves two gates.
- `KeepLeft.lean`: pinned Lean exit 0, empty log. Equal-size common-input diamond repair: retains first OR(s,a), changes second OR(s,b) to AND(a,b), changes final AND to OR(s,newAND). Only the old second-OR wire must not be read outside the block. Preserves minimality. Earlier first-OR users remain valid and unchanged.
- `InputStar-snippet.lean`: primary-input operand forces owned edges to contain that primary vertex. Combined compilation passed with empty log after a minor linter cleanup.
- `Prefix-snippet.lean`: ownership is invariant for a gate in a common circuit prefix; compiled exit 0 with empty log.
- `KeepLeftStar-snippet.lean`: compiled exit 0 with empty log; equal-size repair extends a star prefix whenever a is primary (s and b may be arbitrary earlier signals). Combined KeepLeftStar.lean builds all these components together.

## Remaining mathematical obstacle

None of these local repairs shows that an arbitrary minimum circuit with a bad ownership gate contains a repairable block. The missing step is a global structural or counting argument controlling shared dirty operands. Nonminimum C6 circuits can share both operands of a dirty AND, so no-C3/C4 alone does not forbid sharing. The singleton-overlap case yields neighborhood restrictions: along u-a-b, N(u) intersect N(a) is empty and N(u) intersect N(b) is contained in {a}. Clean direct users of shared factors may then make the dirty gate redundant, but dirty shared users can form larger components.

## Auxiliary separate-count route

The hoped-for full route would prove AND-count >= tau(G) and OR-count >= |E(G)|-1 separately, then apply the canonical star-cover construction. Neither generic inequality has been proved here. Biclique-cover <= AND-count is not a general graph theorem; saturated graph constructions can defeat naive versions. No-C3/C4 remains a substantive hypothesis, not a justification by itself.

A global normal form preserving AND-count only (ORs free) is sound: maintain each old signal as an OR of primary variables and previously retained AND atoms. Expand the two operands of each AND, pull their common source set R outside using (R OR A) AND (R OR B) = R OR (A AND B), and create at most one new AND on the disjoint remainders. Every retained AND atom is singleton-silent by induction. This does not bound the number of OR gates.

Also for OR-free cost, select every clean AND signal (below the target function) as an output disjunct and remove references to clean signals from later AND operands. The output is unchanged because any removed true signal already causes acceptance. Iterate as new signals become clean. This yields an AND-count-preserving top form, again with uncontrolled OR cost. The base encoding is independently reviewed; review of the stronger normalization constraints is pending.

### Computational probes (not Lean proofs)

- C7: <=3 ANDs, ORs free: UNSAT, 0.134 s. Four ANDs: SAT, all 128 inputs verified.
- C9: <=4 ANDs in disjoint-source/ordered normal form: UNSAT, 0.492 s; cover number is 5.
- C5 dual: <=3 ANDs (equivalently original <=3 ORs) UNSAT, 0.075 s; four ANDs SAT and gives an optimal seven-gate original after dualization.
- C7 dual: <=5 ANDs (original <=5 ORs) UNSAT, 23.7 s; expected OR count is 6.
- Petersen: <=5 ANDs base and disjoint-only models each timed out at 120 s (UNKNOWN).
- Petersen: <=5 ANDs in canonical top-form model UNSAT, 114.5 s, pending normalization review. Six ANDs SAT, all 1024 inputs verified, 24 binary gates.
- A C7 four-AND top-form witness still has a nonstar first ownership gate: (x0 OR x2) AND (x1 OR x6) owns edges 01,06,12. Its total size is 14, so it does not contradict the target or known ten-gate optimum. It does refute the stronger idea that every AND-count minimum circuit already has a star profile.

Base script `free_or_sat.py` SHA256 ca33829e0d047e59bda013f381278977dfc4a9a2cbc1c6477a521efe3044f7a4 independently reviewed PASS by lean_setup. It validates each SAT CNF model and both collapsed and concrete binary realizations on every Boolean assignment. UNSAT outcomes are solver evidence only. The ordered/disjoint Petersen five-AND run completed UNSAT in 142.1 seconds (900-second budget). This avoids dependence on the semantic top-form constraints. The dual Petersen thirteen-AND run timed out at 120 seconds (UNKNOWN). No solver sessions remain active.


All computational scripts and results are now frozen for independent review. The ordered/disjoint model adds only two structural constraints to the independently reviewed base: disjoint operand source sets, and minimum selected source on the left (swap the two operands; an unused false gate may have empty sides). The extraction normal-form argument was independently endorsed by lean_setup; source-level constrained encoding review is pending from status_review. No generic separate-count inequality or main theorem has been proved.

## Frozen free-OR archive

Completed bounded-AND/free-OR searches are frozen under `results/orch/free-or/`: six source scripts, fourteen runs with complete CNFs/full solver logs/full runner logs/JSON models, README, catalog and SHA256 manifest. There are 65 files totaling 1,101,865 bytes. The SHA256 of `SHA256SUMS` is `7411ee9a6465aff9b3b31e81e9e5687c3a4ce462e701970dd2352812c2ba3143`. Outcomes are 5 SAT, 6 UNSAT and 3 UNKNOWN. The independent generator/validator and complete output are `results/orch/free_or_review.py` and `results/orch/free_or_review.log`; all fourteen CNFs matched and all five SAT witnesses passed CNF and full collapsed/binary truth validation. Independent mathematical review accepted disjoint/ordered and optional top normalization for AND count only. None of this proves the posted total-size theorem. No solver runs were started during preservation.

## Essential-edge certificate route and a minimum-AND obstruction

For an AND gate g, define Ess(g) as graph edges whose accepted pair input becomes rejected when g is forced false. A useful conditional induction is valid: if Ess(g) is contained in a star centered v, restrict v=0 and delete g. Every surviving graph edge remains accepted and monotonicity bounds the altered function above and below by the induced graph function. This gives a circuit with one fewer AND for G-v.

However, existence of such an essential-star gate is false even for AND-minimum circuits of girth at least five. For P4 with edges ab,bc,cd, let g=(a or c) and (b or d), h=g and (b or c), and output h. The function is exactly ab or bc or cd. Forcing either AND false kills every edge, so both essential-edge sets are the whole nonstar P4. Two ANDs are minimum: in the reviewed free-OR model a one-AND singleton-silent output is one product of two primary ORs, and all 256 operand source pairs fail for P4. The finite exact check and full output are results/orch/essential_p4.py and results/orch/essential_p4.log. No SAT solver was started.

This is not a counterexample to the posted gap: the circuit has five total gates while b(a or c) or cd has four, both with two ANDs. A minimum-AND circuit selected by a secondary minimum-total-size criterion might still have an essential-star gate; that statement remains unproved. The downstream-blocker descent has no unconditional strictness: in this P4 example the source AND and its blocker have identical essential sets.

An allowed-import Lean witness at structural/EssentialP4.lean compiled with an empty log. It proves the explicit wide and short circuit identities, both forced-zero output identities, no triangle/no four-cycle, the absence of a common edge center, both AND counts, the 5-versus-4 size comparison, and nonminimality of the wide circuit for total size. It does not assert the generic one-AND normalization theorem or unrestricted AND-minimality in Lean. The root was notified immediately for preservation.

Literature boundary checked on 2026-11-25: Jukna, Disproving the Single Level Conjecture, explicitly distinguishes total circuit size from AND-only complexity and gives saturated-graph separations. It supplies no girth-five certificate argument used here: https://web.vu.lt/mif/s.jukna/ftp/single1.pdf .
