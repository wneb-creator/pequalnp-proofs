# Counterexample search for L-meta-2592

Circuit semantics inspected: genuine AND/OR/NOT gates with input lists of length at most two; acyclic evaluation; unavailable wire reads are false. No semantic loophole found.

Bitparallel stochastic search runs in scratch, checking all 1024 truth assignments. Seeds are 20-gate monotone circuits obtained from minimum vertex covers of Petersen (6 centers, 15 assigned edges, 5 top ORs); one gate is deleted to give 19. Mutations permit NOT. Initial best 19-gate candidates have 9 false negatives and zero false positives; no witness as yet.

SAT/CEGIS synthesis is delegated to child sat_search. CaDiCaL obtained from GitHub in scratch and compiling. All source, diagnostics and candidates remain under /tmp/oec/pequalnp-pilot-95/.

Petersen graph is Kneser KG(5,2): input variables can be interpreted as edges of K5; target asks whether selected edges include a disjoint pair. This may offer an algebraic nonmonotone construction.

Latest stochastic best: 19-gate candidate with only four false positives, at independent triples {0,2,6}, {4,6,7}, {2,4,8}, {0,7,8}; zero false negatives. NOT is unused, so effective circuit uses 18 monotone gates. Python independently verified all 1024 inputs. This is not a counterexample. Candidate saved in scratch best952.txt; exact 20-gate star-cover witness in exact20.txt. SAT repair within four gate changes returned UNSAT; larger neighborhoods ongoing.
