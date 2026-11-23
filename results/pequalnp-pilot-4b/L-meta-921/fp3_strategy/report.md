# L-meta-921 strategy status

> Archive note: These are historical research-phase notes. Statements that no repository files were changed describe that phase, before this authorized archival checkpoint. Scratch paths and unpreserved search artifacts below are provenance, not archive dependencies.

The complete 39-gate lower bound remains unproved and unrefuted. All statements below are either explicitly restricted mathematical arguments or checked semantic helper lemmas. No target proof file has been created by this agent.

## Checked semantic lemmas

`SingletonCofactor.lean` compiles with Mathlib only and an empty `singleton-cofactor.log`.

For a circuit cut represented by a function `F(X,z)` monotone jointly in the input support X and Boolean cut z, suppose `F(X, a in X or b in X)` computes the conjunction of a fixed line L on all supports of size at most k+1, with a and b distinct. Then the upper cofactor `F(X,true)` computes that conjunction on all supports of size at most k. Proof: any true upper-cofactor input X extends to true original inputs X+a and X+b, so L is contained in their intersection X. Any false positive of the upper cofactor within the original promise must omit both endpoints a and b. For this gap, only five-point leaks remain after this substitution.

The file also proves the finite-set context fact: if L is contained in C+a and in C+b for distinct a,b, then L is contained in C. Consequently, an exact-line accepting proof that uses a first OR gate a OR b has all line variables already present outside that gate occurrence. This is semantic certificate redundancy; it does not by itself justify deleting the gate while retaining correctness on five-point inputs.

## Promising first-OR elimination (mathematical, not encoded)

The child `fresh_simulation` found this reduction, independently inspected by this agent. Work in the dual conjunction formulation. Before the first OR gate g, every nonconstant wire is a conjunction of a fixed set of input variables. Write g=A OR B. If B contains at least two variables, B can be true on at most one exact projective-line input K, since different lines intersect in at most one point.

Replace g by A and suppress B's root gate, replacing its later uses by false. Every other exact-line positive input is unchanged; all negative promised inputs remain false because every replacement only decreases the circuit. If B fits no line, there is no output to repair. Otherwise suppress the old K-output wire too and reconstruct K with three AND gates. Ordinarily the deleted gates g, B's root, and the old K output pay for these three gates. If the old K output equals B's root or g, B necessarily has all four K variables, so a distinct nontrivial AND ancestor of B supplies a third deletable gate; that ancestor is false on every other exact line as well. Constants and comparable monomials admit simpler direct deletion.

Thus a minimum-size, minimum-OR counterexample can be arranged so its first OR has two distinct singleton operands. The transformation needs a formal circuit deletion/renumbering implementation before it is a Lean result. It does not eliminate arbitrary later OR gates, whose operands need not be monomials.

## Other partial arguments and the remaining obstacle

The child subsequently strengthened the deletion argument: any OR gate with a gate operand true on at most one exact positive line can be eliminated without increasing size, regardless of earlier OR gates. If that operand or the OR gate itself is the selected output for the exceptional line, direct bypass avoids the three-gate refund collision. Otherwise delete the OR, its private operand, and the exceptional old output and rebuild the exceptional line with three ANDs. A minimum-OR counterexample therefore has no private gate feeding an OR. Every private gate is itself AND, and all its descendants are private AND gates for the same line. This gives a shared core (each wire true on at least two exact lines) followed by thirteen disjoint AND-only output tails. Each tail can be normalized to the conjunction of d distinct shared frontier wires using d-1 AND gates. A complete proof could follow from a core-cost bound paying the deficits 4-d for tails with d<4; that bound is not established.

Further, minimum size gives 2<=d<=4: d=1 would make the output a shared wire, while d>4 would be shortened by the direct three-AND construction. Therefore the exact remaining charge is that the shared core has at least twice the number of two-wire tails plus the number of three-wire tails. Formal_audit independently approved the general private-OR elimination and tail normalization as mathematical arguments; they have not been encoded as a Lean circuit transformation.

With only one OR gate in the entire dual circuit, its monomial operands of size at least two each fit at most one line, so at most two output lines can depend essentially on it. Their AND-only descendants can be refactored with at most one extra AND, paid by deleting the OR. The stronger first-OR suppression argument above avoids this restricted descendant assumption.

Certificate splicing says that if a shared gate has an accepting witness B and the surrounding proof for line L has context C, then any substituted support B union C of size at most five must contain L. This makes multilinear three-AND line proofs essentially private. Repeated-variable contexts and full-line alternative witnesses can push cross supports to size six, outside the promise. Those alternatives require extra gates, but no complete amortized accounting has been established.

The checked external helpers `formal_audit/meta921/Mixing.lean` and `FirstOutput.lean` were independently read and found sound. The former shows that two proper binary decompositions of distinct four-point lines cannot make both opposite bad cross unions exceed five. The latter shows that the earliest promise-correct dual line output cannot be an OR gate. Neither supplies the missing global gate-count invariant.
