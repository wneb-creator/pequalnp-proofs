# Counterexample search for L-meta-2592

Circuit semantics inspected: genuine AND/OR/NOT gates with input lists of length at most two; acyclic evaluation; unavailable wire reads are false. No semantic loophole found.

Bitparallel stochastic search runs in scratch, checking all 1024 truth assignments. Seeds are 20-gate monotone circuits obtained from minimum vertex covers of Petersen (6 centers, 15 assigned edges, 5 top ORs); one gate is deleted to give 19. Mutations permit NOT. Initial best 19-gate candidates have 9 false negatives and zero false positives; no witness as yet.

SAT/CEGIS synthesis is delegated to child sat_search. CaDiCaL obtained from GitHub in scratch and compiling. All source, diagnostics and candidates remain under /tmp/oec/pequalnp-pilot-95/.

Petersen graph is Kneser KG(5,2): input variables can be interpreted as edges of K5; target asks whether selected edges include a disjoint pair. This may offer an algebraic nonmonotone construction.

Latest stochastic best: 19-gate candidate with only four false positives, at independent triples {0,2,6}, {4,6,7}, {2,4,8}, {0,7,8}; zero false negatives. NOT is unused, so effective circuit uses 18 monotone gates. Python independently verified all 1024 inputs. This is not a counterexample. Candidate saved in scratch best952.txt; exact 20-gate star-cover witness in exact20.txt. SAT repair within four gate changes returned UNSAT; larger neighborhoods ongoing.

Structured vector strategy: set (a,b,c,d,e,f)=(x0,x2,x6,x4,x7,x8). Compute A=b∨d∨f, B=a∨b∨c, C=a∨e∨f, D=d∨c∨e, and N with D∧N=ad∨be∨cf. An11gate vector realization plus8 outergates gives19gate Petersen. Exhaustive restricted search tried all81 choices of pairfirst computation forA/B/C/D (8fixedORgates), followed by≤3extraAND/OR/NOT gates with≥1NOT. No witness after17,860,500 thirdgate checks. Source structured.cpp/log structured.stdout. This is a restricted search result, not a lowerbound for arbitrarycircuits. SAT child searching freer11gate vector sharing/interleaving.

Accepted L_meta_1036 identity inspected and independently checked on all 32 assignments: threshold2 of four variables, excluding z from a five-variable bank, equals T3 OR (T2 AND NOT z), where T2 and T3 are thresholds on all five variables. The bank already contains 20 sorting/comparator intermediates. This is a three-gate extraction versus at least four monotone extra gates; it does not directly simplify our pure OR bank.
