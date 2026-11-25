# Gap 2585 direct route

Checked files (all compiler exits 0, final target untouched):

- StarRectangles.lean: every C4-free incidence rectangle has a side of cardinality at most one; a nonempty rectangle has |A×B|=|A|+|B|-1.
- CleanBlockBridge.lean: AND(point-OR A,line-OR B) is below the incidence function iff every pair in A×B is incident. Thus a nonempty clean block is a star with exact edge/gate cost.
- PrivatePureOr.lean: at least two pure line leaves determine at most one point center; dual fact for point leaves; distinct-center supports intersect in at most one leaf.
- SharedOrBudget.lean: arbitrary binary reader network with disjoint leaf/internal-wire sets, each node a root or read by an internal node, has leaves.card≤gates.card+roots.card. Sharing and cycles are allowed; no cone-disjointness assumption.
- NormalFormWitness.lean: on 2+2 inputs, I(p,l): l≤p is C4-free. The five-gate circuit OR(0,1), OR(2,3), AND(4,5), OR(1,2), AND(6,7), output8, computes I, satisfies the proposed generic normal form, and fails ReadK1. A four-gate star circuit computes the same function and is ReadK1. This is NOT a refutation of gap2585; it rules out NF⇒ReadK1 without an additional size argument.
- EmptyIncidence.lean is checked but duplicates toolchain agent EdgeCases.lean; do not prioritize it.

Safe global clean-block charging route:

Group top star ANDs by chosen center c. Let k_c count these tops and L_c be the union of their leaves. The shared binary OR budget gives |L_c|≤|G_c|+k_c. Nontrivial pure OR supports cannot serve different centers by PrivatePureOr; trivial support-one OR gates can be bypassed in a least circuit. Summing therefore gives internal-OR+AND cost at least sum|L_c|≥|E|. The output OR region requires at least sum k_c−1 gates and is disjoint from pure OR regions because it is below the incidence function and cannot accept a singleton. Centers cover the graph, and their number is at most sum k_c. Therefore total cost≥|E|+tau−1 in this clean case. This allows all sharing within a center; it does not assume arbitrary cones are disjoint.

Unresolved: structural agent normal form allows dirty internal ANDs, so its blocks need not be clean stars. NormalFormWitness demonstrates that distinction. A genuine mixed-block/global charge is still needed; the checked lemmas do not prove it.

Existing repository evidence:

- Defs/CircuitMoves.lean defines eraseGate, liftAt, WireBelowOutput, Lift.
- Outside/L_meta_4742.lean has lift_size at1175, model preservation around1192, and lift_eval at1242. These are reusable with attribution, but cannot be imported because gap allows only Defs.
- Outside/L_meta_3243.lean proves coverCircuitB exact owner-list cost and incidence semantics; L_meta_3245 proves AO2 and pure point/line operand classes.
- L_meta_3653 proves elimination of a unique dirty AND that accepts a singleton under additional normalized hypotheses. L4742/L4743/L4746/L4747 cover further unique-dirty cases, not arbitrary many dirty gates.
- L_meta_3444/L_meta_3446/L_meta_2969 refute several naive aggregate core/cone budget inequalities. Do not assume cone additivity.

## Least-circuit structural progress 2026-11-25T01:00:09.610380+00:00

`LeastGatePrivateBoundary.lean` compiles with Lean4.36.0 and Defs only. Prefix is the independently checked generic least-normalization proof, followed by our OR-deletion and AND-deletion lemmas. Every chosen operand of an OR in a globally least graph circuit differs from that OR on some positive edge input. Every chosen operand of an AND differs from that AND on a negative input in any cofinal negative boundary family. Both are necessary local witness conditions; neither gives distinct witnesses, an injective global gate charge, or dirty-AND elimination. Independent reviewer PASS.

`dirty_nf_search.py` adapts the counterexample agent's exact boundary-row circuit synthesis and adds dirty indicators d_i iff gate i is AND and is not below output. C6, size8, strong NF, at least2 dirty AND gates: Cadical UNSAT in1.571seconds,496variables4521clauses. Full stdout/stderr `c6-size8-nf-dirty2-boundary.log`; driver `dirty-nf-driver.log`. This finite computational result is not a Lean theorem and supplies no general dirty-elimination proof.

The direct path-CNF witness in `NormalFormWitness.lean` still establishes that strong NF alone does not imply ReadK1. It is not globally least: five gates versus a four-gate star circuit. Thus adding leastness remains meaningful. Latest-dirty elimination cannot directly reuse unique-dirty lemmas because its operands may contain earlier dirty ANDs; earliest-dirty elimination leaves later dirty contexts. The unique-dirty lemmas require uniqueness in the whole circuit.

L3706's frontier accounting charges only R=E\U, where U are edges with no squarefree proof at output. It yields |R|+tau(R)<=size+1. The remaining debt is |U|+tau(G)-tau(R). Its proof slack splits as unused gates + (OR-frontier+1-AND-frontier) + (AND-frontier+selected-internal-OR-|R|) + (AND-frontier-tau(R)). A new global theorem must pay this debt without assuming cone disjointness. The inspected R2384 reductions assume such compensation; they do not prove it.

L634 provides a generic AND-count normalization with free ORs: every AND rejects singleton inputs, direct variable sides are disjoint, and count/function are preserved. Its `wit` lemma says: for independent I and u adjacent to some x in I, some direct gate side contains u and avoids I. This is stronger than edge-pair coverage, but an unrestricted C4-free bipartite label-count theorem has not been derived. Simple maximal-independent-set counting does not prove #AND>=tau: C12 has29 maximal independent sets but tau6, so ceil(log2(29))=5. Other agents own the stronger macro-count search.
