# Focused OR-bound review

Read/reasoning date: 2026-11-25. Target investigated: for every full C4-free bipartite quadratic incidence function, every AO2 circuit has at least |E|-1 OR gates. This is equivalent by Boolean duality to an AND-count bound for the vertex-cover CNF. **No proof or counterexample to that general claim was obtained. No unconditional L2585 theorem is claimed.**

## Closed restricted argument: forests

The OR bound holds for forests by leaf restriction and an opcode-specific constant-propagation lemma. Let y be a leaf and suppose at least two edges remain. The graph function depends essentially on y, and setting y=0 deletes exactly its one edge while leaving a nonzero graph function.

Essentiality ensures a syntactic path from input y to the output. Since the restriction y=0 is nonzero, monotonicity implies that the assignment y=0 and every other input=1 is accepted. Thus no y-to-output path can use only AND gates. On any such path, take the first OR gate. The path prefix consists only of AND gates, so y=0 makes that predecessor wire constant false. Constant propagation removes this OR. Other propagation steps cannot increase OR count. Induction on edge count gives OR(C) >= |E|-1, including forests with several components.

The dual AND restriction is also useful. Essentiality gives a path from y to the output, while rejection of the singleton {y} excludes any all-OR path. Its first AND has an OR-only prefix; setting y=1 makes its predecessor constant true and removes that AND. For a pendant edge xy, additionally setting x=0 yields G-{x,y}. The exact cover recurrence is tau(G)=1+tau(G-{x,y}): a minimum cover can replace y by x, and removing x leaves a cover of the residual graph. Thus the analogous induction proves AND(C) >= tau(G) for forests. This separates the forest full-cost bound into two counts without needing cone disjointness or a degree-two/sibling-leaf case split.

These are informal closed arguments. The compiler and formalization are owned by the certificate agent; no duplicate Lean compiler was started here.

## Why the same counting does not settle cyclic cores

Deleting a degree-d vertex removes d edges, while the generic zero-propagation argument forces only one OR deletion. To extend the induction one needs d distinct eliminated ORs or a compensating invariant. C4-freeness cannot simply be imposed on intermediate functions. The identity

    (a OR c) AND (b OR d) AND (b OR c) = ab OR bc OR cd

has a C4 rectangle at the first product, then a free AND filter removes the unwanted ad term while all resulting higher terms are absorbed. The output is the C4-free path P4. This identity was checked on all16 assignments in `or-bound-filter-check.json`. It is not an OR-bound counterexample: this representation uses3 ORs, while the3-edge path needs only2 canonically.

Prime-clause counting alone also does not bound arbitrary circuit AND count: distribution can generate several clauses at an OR gate, and later absorption can delete them. A proof must charge actual gates globally rather than count a final expanded CNF.

## Primary-source scope

No exact unrestricted OR-count theorem was found in the sources read. Jukna's *Disproving the Single Level Conjecture*, Problem8.2, asks in2006 for a superlinear monotone circuit lower bound for an explicit quadratic function. The proposed OR>=|E|-1 theorem would itself imply Omega(n^(3/2)) size for projective-plane incidence functions. This is an inference about the strength of the claim, not proof of its current open status. **UNVERIFIED:** current2026 status of that literature-wide question. Source read: https://web.vu.lt/mif/s.jukna/ftp/single1.pdf , Section8.

The superficially related Katz paper *On the CNF-complexity of bipartite graphs containing no K2,2's* concerns graph representation on pairs, not exact full incidence functions or their dual vertex-cover functions. Its small-CNF representation does not supply a counterexample here. Source metadata and abstract read: https://arxiv.org/abs/1206.6068 .

## Finite evidence from counterexample agent

The team's complete macro encoding proves C6 cannot use at most4 OR gates even with arbitrarily many ANDs (canonical count5). Theta with9 edges and at most7 OR remains unresolved after a300-second run. The macro encoding flattens every AND-only region into conjunctions of inputs and previous OR outputs, so its OR-count search is not restricted by total AND count. These results were reported by the counterexample agent; no new broad search was run here. No OR-bound violation was found.
