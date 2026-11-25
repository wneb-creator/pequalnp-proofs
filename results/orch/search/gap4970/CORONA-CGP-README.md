# Exact-hypothesis six-cycle corona CGP search

Separate source: `corona_cgp.cpp`; separate verifier: `verify_corona_cgp.py`. The frozen K4-incidence search is unchanged.

The graph is a six-cycle with one private leaf at each cycle vertex. In the6+6 bipartition, core vertices in cycle order are0,6,1,7,2,8 and the corresponding leaves are9,3,10,4,11,5. It has12edges and minimum cover6. The canonical circuit OR_i[core_i AND(leaf_i OR core_(i+1))] has17gates; a valid circuit with at most16gates would refute L4970.

The search evaluates all4096assignments. It uses the same independently reviewed joint output-plus-witness-cone logic as the K4 search, including unused witnesses, output before the last gate, duplicate parents, exact semantic pure-star tests, and syntactic two-colour reach. Greedy witness selection is only a valid-size upper bound. This is a heuristic search, not an exhaustive decision procedure.

Controls passed: canonical17; DNF23 plus6requiredpost-outputstarORs29; canonical plus duplicate AND colour shields35. The verifier independently enumerates all4096truthrows, vertex covers, and every pure-star witness. A two-second smoke run attempted1,629,024mutations across7restarts, with733,962accepted; best remained17. Complete control and smoke logs are archived as `corona-cgp-*`.

No long run starts before independent review and root lease renewal.


The planned480-second corona run was intentionally stopped after approximately124seconds at2026-11-25 16:02:50.835UTC, with SIGTERM/exit143, on root instruction. It had emitted only the three valid controls and no smaller circuit. All emitted circuits were revalidated on4096inputs. Complete partial stdout/stderr are preserved; no final mutation count was emitted before termination.

Reason: any essential private leaf reaches an AND through OR gates (otherwise the singleton leaf would make the output true). Set that leaf to1: its first AND receives a true operand and becomes a copy. Set its unique neighbour to0: the remaining graph is the five-core path with one private leaf at each core. Its cover number is five, so the checked general L217 bound requires five remaining ANDs, giving at least six originally. The checked L599 pseudoforest bound requires at least eleven ORs for the original twelve-edge corona. Together they give at least17gates. Root independently checked this mathematical assembly; it is not presented as a newly Lean-checked proof. No UNSAT claim is made from the interrupted search.
