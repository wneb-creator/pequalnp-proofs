# L-meta-2583: read-one construction and finite Fano checks

Updated 2026-11-25T14:46:03.029068+00:00. Parent owns lease and git; this agent makes no desk calls or git mutations. Old2592 work stopped on reassignment.

## Definitions and structural meaning

ReadK.IsReadK quantifies over prime implicants and requires one proof tree whose counts jointly bound all variables. It is not input fanout and not separate scalar minimization per variable. For incidence functions prime implicants are incident point-line pairs. Existing L7639 proves read-one circuits for C4-free bipartite incidence with a perfect matching require |E|+N−1 gates; existing L7684 constructs read-one circuits from a bipartite vertex cover with at most |E|+cover−1 gates. Hence plane normalization amounts to the unrestricted AO2 size lower bound N*(q+2)−1. For Fano this is27. No unrestricted lower bound has been proved here.

## Frozen compiled generic construction

`/tmp/oec/pequalnp-pilot-99/gap2583/sat_encoding/StarConstruction.lean`
SHA256 `022d1ca8288ed3d7bfd0a687c4f012cb8b8d368064b63fce00b7b875aca79d38`;1171lines,54067bytes. Lean exited0; complete logs `star-construction-03.stdout/.stderr`. Root and independent reviewer notified.

Adapts all of L7684 under `PEqualNP.Outside.L_meta_2583_aux.StarConstruction`, renaming its final theorem `exists_read_one`. New proofs count the incidence edges from constant line cardinality, derive `incidence_read_one_upper` with AO2 + exact posted incidence function + READ1 + size≤N*(q+2)−1, and derive `normalize_of_size_bound` with the explicit premise N*(q+2)−1≤C.size. Construction needs only the line cardinality assumption; it does not assert the missing general circuit lower bound.

## Fano extension in validation

`FanoConstruction.lean` extends the frozen generic source with cyclic lines l,l+1,l+3 modulo7, matching counterexample agent data. Includes kernel finite checks of line cardinality3 and unique common line for distinct points, identity matching, no rectangle,21 edges, and the27-gate read-one upper bound. Compile pending; do not yet claim this extension checked.

## 2026-11-25T14:50:14.925702+00:00 Fano finite checks compiled

Frozen `FanoConstruction.lean`, SHA256 `521cf0512e3c52cda012b09bdfdbd2b61ce8e7378d77109221fd250b73222fb5`,1216lines55917bytes. Lean exited0; full `fano-construction-02.stdout/.stderr`. Formal cyclic incidence agrees with counterexample agent, kernel finite checks confirm line cardinalities and unique common line, and generic constructor yields READ1upper27. Root and reviewer notified. Inherited `exists_read_one` placement outside helper namespace is a guard-only issue; library_route is making an integration copy with namespace wrapper, keeping this frozen source intact.

## Edge-invisible gate removal in progress

Root requested a new minimality fact: every gate in a least-size graph AO2 circuit must be true on some edge input. Reduction_strategy identified L4747 force-false and strict AO2 bypass surgery. New `EdgeInvisible.lean` extracts91 transitive helper declarations and combines them with a new edge-preservation argument: forcing a gate that is false on every edge input preserves output by monotonicity and edge generation, then an OR-reader bypass reduces size. Statement currently assumes the gate is in the output cone; unused-gate trimming handles the complementary case separately. Generic arbitrary graph, no bipartite/C4 assumption. Compile pending.

## 2026-11-25T14:53:08.251376+00:00 Novel edge-invisible removal theorem compiled

Frozen `EdgeInvisible.lean`, SHA256 `cbdd0f32b1e1791eaba3d7f659533a1b50557bff88f23f0f6a9f83029ce778ca`,1392lines68408bytes. Lean exited0, full logs `edge-invisible-02.stdout/.stderr`. Root/reviewer notified immediately for independent review and preservation. Imports onlyMathlib+Defs.90helper declarations extracted from L4747; unrelated original theorem and assumptions omitted.

New `edge_invisible_gate_removable`: for ANY simple graph, an AO2 circuit computing its graph function, and a gate in the output cone that is false on every edge input, there exists a strictly smaller AO2 circuit computing the same graph function. The proof forces the gate false, preserves every positive edge by evaluation equality, extends to all positive inputs using monotonicity, and uses strict AO2 OR-reader bypass surgery. No C4-free, bipartite, lift-fixed-point, or star-form assumptions. `least_gate_has_edge` concludes every such gate in a globally least AO2 circuit accepts at least one edge. Output-cone membership remains explicit; unrelated unused-gate deletion supplies that premise.

Parent requested generalized earlier-wire replacement: if earlier y implies gate g globally and agrees with g on every edge input, erase g redirecting to y; this should give a smaller circuit computing the same function. Separate `EdgeReplacement.lean` draft is compiling with that lemma, a least-gate separation corollary, and singleton-overlap OR-support combinatorics. Frozen EdgeInvisible unchanged.

## 2026-11-25T14:54:07.312628+00:00 Earlier-wire replacement compiled

Frozen `EdgeReplacement.lean`, SHA256 `d2eba86ded07dd451b567d01572b250ab795c9336b7c0c9621b804baa9796010`,1495lines73290bytes. Lean exited0 on first run; full logs `edge-replacement-01.stdout/.stderr`. Contains frozen EdgeInvisible plus103newlines. Root/reviewer/lower_bound notified.

`edge_equiv_smaller_replacement` requires an earlier wire y<n+g whose value implies gate g on every input, and agrees with g on every graph-edge input. Erasing g and redirecting to y yields strict AO2, strictly smaller size, and the same exact graph function. No output-cone premise, no bipartite/C4 assumptions. Proof combines the general erasure relation with monotonicity and graph edge generation.

`least_gate_separates_earlier`: in a least AO2 graph circuit, each such earlier implicant wire must miss some edge accepted by the gate. `singleton_overlap_on_edge` proves the pure set identity needed for the first-AND overlap case: if A∩B is exactly{u} and every graph edge across A×B touches u, then AND(OR A,OR B) and input u agree on every edge input. The global implication from u to that gate is immediate, hence the replacement lemma rules out such a gate in a least circuit.

## 2026-11-25T15:05:21.378362+00:00 Target-relative same-size gate patch compiled

Frozen `GatePatch.lean`, SHA256 `f4bf6171d882de4c430064c8274a84b96e124aaee6ba53758dca8aef511b2e70`,1659lines80549bytes. Lean exited0 on first run; complete logs `gate-patch-01.stdout/.stderr`. Exactly frozen EdgeReplacement prefix plus164lines. Root/reviewer/lower_bound/library_route notified immediately.

`patchGate C g fresh` replaces one gate slot and preserves the output index. New helpers prove exact length, strict AO2 when fresh is AND/OR with exactly2 earlier operands, prefix wire equality, and generic `patch_val_rel` propagation for a reflexive relation preserved by old AND/OR gates.

`patch_below_target` assumes C computes graphFun G ∅, old gate g implies the target globally, fresh gate evaluation on the old earlier wires also implies the target globally, and fresh dominates the old gate on every positive edge input. It concludes strict AO2, exact unchanged size, and the same complete graph function for the patched circuit. On target-false inputs both gate values are false, so the complete execution agrees by equality propagation; on true edge inputs acceptance propagates forward by implication; monotonicity extends edge acceptance to every target-true assignment. No global fresh≤old or fresh≥old condition is assumed.

This matches lower_bound's RectangleFamilies envelope: fresh can be one AND whose operands are a raw center input and one already-existing earlier pure OR-clause wire. The finite geometry supplies global below-target and edge-dominance premises, while this compiler lemma handles the circuit modification. It does not by itself classify arbitrary alternating AND/OR blocks or complete the posted normalization theorem.

## 2026-11-25T15:05:48.100935+00:00 Frozen interface and remaining obstacle

Root requested artifact generation pause; all compiled files and reported hashes remain frozen. No active Lean processes remain from this agent.

Final checked compiler interface is `L_meta_2583_aux.EdgeInvisible.patch_below_target n G C g fresh hAO hF hg hop hlen hback hold hnew hedge`. Fresh must be an AND or OR gate with exactly2 operands less than n+g. `hold` and `hnew` state that old and proposed gate values globally imply graphFun G ∅. `hedge` states the proposed gate is true whenever the old gate is true on an incident-pair input. Output: patched AO2, exactly equal size, exactly equal graph function.

The unrestricted obstacle remains precise: RectangleFamilies supplies the star envelope for an AND-only cone over pure one-sided OR clauses. General AO2 blocks may instead contain alternating OR mixtures internally. We have not proved that every such block can be rewritten into the required pure-clause AND-cone form at the same cost, nor that its accepted edges admit the required star represented by an already-existing earlier clause wire. Thus the checked geometry plus gate patch proves restricted replacements only. It does not prove the complete posted read-one normalization theorem or its equivalent unrestricted size lower bound.
