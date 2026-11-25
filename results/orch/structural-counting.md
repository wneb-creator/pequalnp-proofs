# Structural counting after the clamp compiler

Status at 2026-11-25 04:08 UTC: the compiler and minimum all-active corollary are checked separately. The counting ideas below remain mathematical research; none is a proof of L-meta-2602.

## What the normalization gives

Clamping a gate false on every minimal positive edge, retaining OR aliases as padding for duplicate AND inputs, and then removing the unread source preserves the incidence function and both marked zero derivatives while reducing size. Thus a minimum-size realization among all sizes at most64 can be chosen with every gate active on an incidence pair. This does not provide the missing ordinary lower bound at sizes at most62.

In an AND-only prefix of an all-active circuit, each gate computes a conjunction supported on at most two input vertices. Two distinct vertices must be incident. An AND-only prefix cannot first create a one-variable copy under distinct-input properness: the first such copy would need two earlier distinct wires computing that same variable. Consequently all AND gates before the first OR are clean single-edge signals, possibly with repeated formal occurrences.

## Formal-context restriction

Fix a gate and unfold a formal output monomial using one occurrence of that gate. If the remaining context has singleton support v, every singleton monomial a of the gate forces the output edge av. Therefore the singleton support of the gate and its useful singleton contexts form a complete bipartite graph in the target. With no C4, a gate having at least two singleton monomials has at most one useful singleton context. A gate with an empty useful context must reject every singleton.

The difficult case is one singleton plus quadratic or higher clean summands. Several contexts may then reuse those summands, and a global count must pay for assembling the contexts.

## Failed component potential

Let the available functions be closed under arbitrary free AND. Joining two target edges whenever some available clean function accepts both does not give a rank that drops at most one per OR.

Counterexample: the four-edge path function F=vz OR wt OR av OR aw. First form q1=vz OR wt, then q2=q1 OR a. The first OR joins vz and wt. The second allows clean functions v AND q2 and w AND q2, joining av and aw to that component simultaneously. A third OR v OR w is still needed to compute F as q2 AND (v OR w). Connectivity forgets that last context-assembly cost.

## Failed local clean-cover potential

A stronger candidate is the minimum number of available clean AND-meet functions covering all target edges. One OR cannot lower this cover number by more than one if either operand is itself globally clean: that operand covers all its contributions, together with one intersection using the other operand for each new cover member.

The unrestricted local bound is false even when every gate is active and essential on some minimal edge. Root independently verified the matching-five example in tau-drop-counterexample.json. For edges ei=xi yi, let

    a=x0 OR e1 OR e3
    b=x0 OR e2 OR e4
    t1=y0 OR e1 OR e2
    t2=y0 OR e3 OR e4

Build these by adjoining the dirty singleton first. The old clean-cover number is4. Adding the single OR u=a OR b permits the two clean functions u AND t1 and u AND t2 to cover all five edges, lowering it to2. Earlier dirty ORs have accumulated substantial unused cost; a valid potential must account for that cost globally.

## More restrictive normalization under investigation

The matching-five example has redundant OR branches, such as x0 OR e1 where the x0 contribution is supplied elsewhere. When the retained child is an earlier gate, copying that gate into the OR slot preserves a distinct physical wire and decreases ordinary values and formal derivatives. If the child is an AND gate, OR count decreases without changing total size. Minimum OR count among size-minimal double-zero circuits can therefore exclude that case. Retaining an original input instead is subtler because properness does not permit a one-input copy, and duplicate-AND derivative blockers may need a padding gate.

Branch irredundancy alone does not restore the local clean-cover bound; the counterexample below disproves that repair. It is not established that global minimum OR count restores a suitable bound, or that OR-tight dirty circuits necessarily incur an extra AND.

## Stronger counterexample with every OR branch essential

The exact computational certificate is tau-branch-irredundant-counterexample.json. The target consists of two disjoint two-edge stars:

    F = l(x1 OR x2) OR m(y1 OR y2).

For each i=1,2 first compute ei=xi AND l and fi=yi AND m, and then

    hi = (ei OR yi) AND (fi OR xi)
       = ei OR fi OR (xi AND yi).

Before the next OR, every clean function in the full AND closure accepts at most one of the four minimal edges, so the cover number is4. Add q=l OR m. Both h1 AND q and h2 AND q are now clean, and together they cover all four edges, lowering the cover number to2. Their final OR computes F exactly.

All64 truth-table rows were checked. Both directed formal derivatives vanish at each of the four target edges. Clamping any of the14 gates to false loses a minimal positive edge, and replacing any OR by either operand changes the output function. Thus the circuit satisfies the gate-essential and OR-branch-essential normalizations. It has6 OR gates, whereas the direct two-star circuit uses3, so the example does not violate the hoped-for global OR bound. It establishes that any valid argument must account for the cost of earlier dirty computations, not just local clean-cover changes or branch redundancy.

The algebraic family extends to k private pairs, giving two disjoint k-edge stars. The cover number changes from2k to k after the single OR q=l OR m, so the local drop is unbounded. Before q, any meet using atoms from two distinct private pairs accepts no minimal edge; a meet using one private pair and a raw variable accepts at most one; and the remaining two-edge meets are dirty. After q, each hi AND q is clean and covers exactly its own two edges. The circuit uses3k ORs versus2k−1 in the direct construction. Every private edge has the surviving formal monomial xi^2 l^2 or yi^2 m^2, explaining the two derivative zeros. This generalization is a mathematical argument, not an additional Lean theorem; the k=2 certificate was checked computationally in full.

No concrete global count or plane circuit below the stated threshold was obtained from these investigations.
