Exact statement audit for L-meta-952

The posted statement elaborates unchanged under import PEqualNP.Defs in Statement.lean. statement.log contains only the expected axiom report for the proposition definition: propext, Classical.choice, Quot.sound. This establishes well-formedness only, not the theorem.

Circuit semantics checked: input wires precede append-only gate outputs; unavailable/future inputs read false; out-of-range final outputs read false. Empty AND and empty NOT evaluate true, empty OR false. NOT ignores its second input if one is present. The stated basis excludes MOD/MAJ and counts all gates. The map from Fin 1 to gate indices correctly imposes at most one NOT and additionally excludes an empty gate list, which cannot compute these nontrivial outputs anyway. No semantic counterexample found.

Monotone lower-bound route: for each line S, evaluate its maximal false assignment z_S (all outside points true). At a safe AND choose a safe child, and at a safe OR retain both. Singleton witnesses for all q+1 points persist. At least q branching OR gates are then required. Any such useful safe gate has at least two singleton witnesses in S, so pairwise line intersection one prevents sharing its charge with another line. The unique NOT breaks the safe-child implication at AND; this is the unresolved step.

One-NOT semantic reduction: write downstream monotone cut F(x,n) with n=not g(x), where g is monotone. Cofactors satisfy F(x,false) <= OR S <= F(x,true). Setting n=true preserves a line output whenever g(z_S)=false. Setting n=false preserves a line output whenever g(e_p)=true for every p in S. The independent helper NotReplacement.lean formalizes these implications correctly. It does not yet construct the actual cut circuit or prove gate counting.

Let A be points with g(e_p)=true and B be lines with g(z_S)=false. Monotonicity gives A contained in every line of B. Thus two points in A force at most one line in B, and two distinct lines in B force at most one point in A. This does not resolve the remaining case where neither cofactor alone computes many outputs.

Every downstream wire true at the all-zero input has singleton-change support contained in A. Hence AND with such a wire can remove only A singleton supports. The two-cofactor accounting is unresolved: gates may contribute to both rails, and charging each rail separately double-counts.

Singleton-only set accounting is insufficient in principle. On one-hot point assignments, union/intersection circuits can build both values of coordinate bits as ORs of point variables and implement finite-field incidence predicates by dual-rail Boolean arithmetic in m polylog(m) gates. Those circuits need not compute OR line functions on arbitrary multi-point inputs. Full outside-line-max safety constraints must remain in any lower-bound invariant.

No proof or refutation of the posted statement has been obtained. No repository file was modified by this agent.
