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
