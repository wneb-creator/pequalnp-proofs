# Independent status review for L-meta-2583

Public snapshot: 2026-11-25T14:52:49.057Z; fetched on 2026-11-25. Both L2583 and L2592 remain conjectures with empty attempt lists. No public proof, refutation, or withdrawal explains the old lease HTTP 410; its cause remains unknown. Exact snapshots: https://data.pequalnp.com/data/lemma/L-meta-2583.567fbafe0560.json and https://data.pequalnp.com/data/lemma/L-meta-2592.bb62b8ddb8cf.json.

The complete targeted GitHub searches found one open PR for each step. L2583 PR13723 was submitted by the same handle's pilot76 at 11:49 UTC. It was refused before building because the exact final theorem is absent: https://github.com/open-goat/pequalnp-proofs/pull/13723#issuecomment-7161809767 . L2592 PR15867 was submitted by pilot116 at 14:50:56 UTC and received two identical format refusals. It postdates our 410 and has no acceptance: https://github.com/open-goat/pequalnp-proofs/pull/15867 . These PRs were only read, never modified.

## External source provenance

PR13723.lean is the exact 7,090-line, 333,774-byte file fetched through the GitHub blob API from wneb-creator/pequalnp-proofs, blob 1fe8cf4516d13a69485f8ad5492d3dc92abf2300, PR head 80e523b7ee77818257e60fbd35611ba975d43a4c. SHA256: 01825179e85adb345b8c0a239845547a995c463e6a09d54ce935a209f6ab74ad. Source: https://github.com/open-goat/pequalnp-proofs/pull/13723/files .

This is an EXTERNAL PARTIAL SOURCE, not locally recompiled and not accepted. The repository import/plain guard passes; its full proof guard reports the missing final theorem. No sorry, axiom, native_decide, _root_, quotes, unsafe, or Lean escape tokens were found. The import line names PEqualNP.Defs, Mathlib.Tactic.Linarith, and Mathlib.Logic.Relation. These source checks do not establish kernel compilation.

The source ends with unrestricted_plane_size_lower (line7075), proving only 3*N−1 ≤ C.size under the exact plane, IsAO2, and computation assumptions. It contains no theorem PEqualNP.Outside.L_meta_2583. Therefore a format change alone cannot solve the gap.

Useful external helpers:

- plane_read_one_upper (line1216): a read-1 construction of size at most N*(q+2)−1.
- read_one_plane_lower (line3395): every read-1 incidence circuit has size at least N*(q+2)−1.
- read_one_replacement_iff_size (line3416): the desired replacement exists for C exactly when N*(q+2)−1 ≤ C.size.
- unrestricted_plane_size_lower (line7075): only the weaker 3*N−1 lower bound for arbitrary C.

For q=2 and N=7, the canonical read-1 size is27, versus the unrestricted floor20 established in this source. A checked26-gate Fano incidence circuit, paired with the read-1 lower bound, would refute the posted statement.

## Existing checked components

These sources exist locally and are marked checked in the public metadata. Reusable source must be copied into the final file's permitted namespace rather than importing an Outside module.

- L_meta_7684.lean: a canonical read-1 circuit for bipartite edges and a vertex cover, with size at most |E|+|P|+|L|−1.
- L_meta_6579.lean: read-1 certification when AND gates combine pure left and right OR circuits.
- L_meta_4897.lean and L_meta_2237.lean: a read-1 circuit on a graph with no four-cycle yields a vertex cover and |E|+|cover| ≤ size+1.
- L_meta_8385.lean: a least AO circuit for a nonempty graph admits TopForm with equal size.
- L_meta_3700.lean: under fixed-point and cleanliness assumptions, and exactly one exceptional AND, produces a circuit with no AND inside another AND without increasing size.
- L_meta_3679.lean: refutes universal AND-antichain normalization for arbitrary bipartite graphs. It omits the no-four-cycle assumption, so it does not refute our plane claim.
- L_meta_7344.lean: a generic read-1 replacement with factor3 and a cost for problematic implicants; it does not preserve size.
- L_meta_6434.lean: already assumes read-1, so it does not supply this gap's normalization.

All paths above are under lean/PEqualNP/Outside/. Exact statements are saved in read1-statements.json and star-statements.json.

READ1 is defined at Defs/ReadK.lean:162 per prime implicant: one proof tree must read each variable at most once. It does not mean global input fanout one. IsAO2 at Defs/TopForm.lean:82 requires only AND/OR gates, earlier wire inputs, and exactly two inputs per gate.

No accepted reduction for2583 was found. Prior PR6987 is a conditional minimum/read-1 reduction and was closed because this step does not accept reductions: https://github.com/open-goat/pequalnp-proofs/pull/6987#issuecomment-7134148064 . The other five closed reduction PRs in the targeted search are also unmerged.

## Preservation audit

PlaneCount.lean is independently approved as a partial lemma: it sums uniform line cardinalities q+1 over N lines to obtain N*(q+1) incidences. It introduces no extra hypotheses or forbidden constructs. Its lemma-only structure explains the standalone guard's expected no-theorem refusal. Root reported a clean compiler exit0. Validation explicitly marks the gap unproved and the external PR source unrechecked. Approval covers partial preservation only.

## SingleLevel preservation review 2026-11-25T14:58:28.344754+00:00

Approved SingleLevelChecked.lean for partial preservation. SHA256: a33452377361ae5c66cb06c0ce70b83b9ea8ab10beaef43ae7bde955fdf459ea; 541 lines, 23,579 bytes. The current SingleLevel.lean is byte-identical. The agent reported a clean compiler exit0 for this frozen source.

The final theorem requires IsAO2 n C, TopForm G C, and junk G C=∅. Empty junk places every AND below the loopless graph function, which forbids a true AND on a singleton assignment. TopForm then prohibits AND ancestry. Pure OR inputs to each AND provide two distinct variable leaves, giving a capped read vector with all coordinates at most1. No claim is made that an arbitrary circuit can be normalized to satisfy empty junk.

The source needs no separate computation assumption: its structural hypotheses suffice. An invalid or trailing output is covered explicitly at lines461–466, where getD=false contradicts the true prime-implicant premise. Input outputs and OR-only circuits are also handled. Repo import/plain guard passes; no forbidden constructs, attributes, or options were found. This is a conditional helper, not the posted L2583 theorem.

## Boundary and replacement review 2026-11-25T15:02:20.971574+00:00

APPROVED partial preservation of PrimeReplacement.lean (SHA256634f5b221ac59ec9a809a703e7f82eb77b8a5afcea84f899a21b28eae4b5dca8), Boundary.lean (61a1fbf026aacfaac0102642aa3e58ede9b577502338981f26fe1a8961ffcab2), and refreshed FanoFinite.checked.lean (fa0298ae6a8ec58488ed2fd12581c68315ca94d4ab175d3216d471dea573738c). All were reported compiled with exit0 by their owners.

PrimeReplacement proves semantic preservation conditional on a monotone replacement signal lying below the original and agreeing on every accepted edge. It imposes no cost bound and claims no automatic normalization. Its monotonicity argument covers arbitrary wire indices through equal-length getD defaults. Boundary is a general finite-preorder result: a monotone Boolean g matching all minimal true and maximal false points of f equals f. No monotonicity of f is needed.

FanoFinite proves the finite plane incidence facts and both positive/negative boundary covers. Independently checked all21 distinct edges, all37 maximal false masks, and coverage on all16,384 inputs, plus line size3 and unique common lines for point pairs. The original two global resource options failed the repository guard; the author replaced them by local options and reran compilation. The refreshed working file is byte-identical to its checked snapshot and passes the guard. None of these files claims the full posted theorem or a counterexample.

Also reviewed pg3_local.py as a fixed-backbone local SAT search. Independently recovered its704 maximal false assignments by enumerating line subsets, verified52 edges and756 unique boundary rows, checked earlier-wire validity of the63-gate backbone, and exhaustively tested guarded AND/OR Tseitin clauses. Selector equivalences and operation polarity match circuit reconstruction. UNSAT results apply only to the selected mutation window, not all63-gate circuits. No solver result was rerun or represented as a Lean proof.

## Integrated module and rewrite review 2026-11-25T15:04:27.503225+00:00

APPROVED preservation of the named882-line module, SHA2562c4443925446f0ae0efbf2d0481b2fd96fe7c9d8055524eec5bd51e1f6206b35. Every source hash in integration-manifest.json matches, and each of the five reviewed source bodies occurs byte-exactly in the integration. The repository import/plain guard passes; the full guard reports only the intentionally absent final target theorem. Root reports lake build exit0. This remains a partial module, not a proof of L2583.

BoundaryReplacement.lean (SHA2563406fd78e470932798531e279440d9a30a12ef0a8312b0825774fc20a464733e) retains the reviewed PrimeReplacement body unchanged. Its new raised_eq_on_negatives and raise_wire_preserves theorems correctly use a monotone replacement above the original signal, equality on a complete negative boundary, and correctness of the original circuit. They establish semantic preservation only; no gate-count benefit is asserted.

ThreeClause.lean (SHA256635ab51eeb02b57f9e708fe37768d050637afc79762215126bfd59ad9c756b77) proves the concrete Boolean identity ((a OR A) AND (b OR B)) AND (a OR b) = (a AND (b OR B)) OR (b AND A). Its explicit circuits use5 and4 gates, have valid AO2 structure, and respectively fail/pass read1. This is a specific rewrite example, not arbitrary normalization. Forbidden scans pass; the lemma-only artifact has the expected standalone no-theorem guard result.
