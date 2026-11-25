# L-meta-2448: small normalized circuit synthesis

This independent model searches proper binary AND/OR circuits, with last-gate output, every gate used, and incomparable operands on the complete separating rows. Edge positives and maximal-independent-set negatives determine the full monotone edge function. Strict dependency cones and edge ownership are modeled literally. On a triangle-free graph, star profile is equivalent to having no two disjoint owned edges per AND gate. Every SAT control is independently evaluated on all Boolean inputs and its cones/owned edges are recomputed.

Completed finite-model outcomes: C5star7 SAT0.012s; C5any6 UNSAT0.250s; C5nonstar7 UNSAT1.736s; C6star8 SAT0.008s; C6any7 UNSAT1.411s; C6nonstar8 UNSAT21.949s. C7star10 and Petersenstar20 controls also pass, over128 and1024 full inputs. The prepared Petersen19 input has8550 variables and71792 clauses. Its running query is outside this frozen batch.

These UNSAT outcomes concern only the explicitly normalized finite model. Standard deletion/constant/alias normalization arguments have not been Lean-formalized here, and no full2448 theorem or counterexample is claimed. No UNSAT proof certificate is claimed beyond complete solver output.

Guardian v1 changes no model and records the owned group,1GiB process ceiling and shared-memory guards. Independent review identified a lifecycle limitation on a forced group stop: waiting only for the Python leader does not prove all descendants exited. Current normal completion is unaffected; a later guardian will strengthen group cleanup. This archive does not claim v1 alone guarantees descendant reaping after interruption.
