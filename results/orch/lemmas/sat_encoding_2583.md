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
