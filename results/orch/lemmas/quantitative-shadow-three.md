# At least three missing degree-two edges

2026-11-25 UTC. Mathematical review by constructive of the proposed strengthening. This note concerns constant-free, forward, binary AND/OR circuits. Repeated operands and arbitrary fanout are permitted. No CPU search, Lean build, desk call, or git action was performed.

## Verdict and scope

The strengthening is sound in this model: a circuit with at most 26 gates computing the posted Heawood edge function must omit at least three target edges from its formal squarefree degree-two monomials.

The key stronger lemma is that, when minimum-degree extraction changes the Boolean function and the extracted output has degree two, extraction followed by unused-gate removal deletes at least two gates. This note does not assert that the transformation or bound has been formalized in Lean. It also does not automatically transfer the degree-two count from an arbitrary repository circuit to a separately normalized circuit.

## Why one deletion cannot change the Boolean output

Use the formal polynomial semantics and extraction from `quantitative-shadow.md`. Inputs have degree one, all gate polynomials are nonzero, and AND adds minimum degrees while OR takes their minimum. Extraction bypasses every OR whose operands have unequal minimum degrees, selecting its lower-degree input. It then removes gates outside the output's input cone. The resulting productive circuit computes a homogeneous polynomial.

Assume the original output polynomial has degree-two terms and the original Boolean function differs from the Boolean function of its degree-two component. Its polynomial is then inhomogeneous. The earlier argument guarantees at least one bypassed OR.

For contradiction suppose that only one original gate disappears altogether. It must be that OR, write it as `g = OR(u,v)` with `d(u) < d(v)`. No other unequal-degree OR was bypassed and no other original gate became unused.

1. The high-degree operand v is earlier than g, and all earlier gate polynomials are homogeneous. Indeed, an earlier first inhomogeneous polynomial would have to be an OR of homogeneous operands of different degrees, giving another bypassed gate. Thus v's original polynomial equals its extracted polynomial; it has no hidden higher-degree terms. More directly, since g is the only modified gate and references are forward, all wires before g retain their Boolean values.

2. Since `d(u) >= 1`, we have `d(v) >= 2`. Therefore v is a gate output rather than an input variable. Because g is the only deleted gate and v is earlier than g, v remains in the extracted circuit's productive cone.

3. The extracted output polynomial is homogeneous of degree two. Every nonzero productive wire in the extracted circuit is homogeneous. Along any productive path, an AND increases degree by at least one, and an OR preserves degree. Hence v has degree exactly two and its path to the extracted output uses only OR gates. In particular, if v is true on an assignment, the extracted output is true on that assignment.

4. Fix an arbitrary Boolean assignment. If v is false, restoring `g = OR(u,v)` in place of the bypassed u changes no wire value, by forward induction. If v is true, the extracted output is already true by step 3; restoring an OR can only increase values, so the original output is true as well. In either case the original and extracted outputs agree.

This contradicts the assumed change of Boolean function. A changed degree-two shadow therefore loses at least two gates.

## Sharing and other potential pitfalls

- Shared consumers of g do not hurt the argument. When v is false, every consumer receives the same value as before. When v is true, the shadow output is already true, independently of those consumers.
- A retained v which was originally inhomogeneous is impossible under the one-deletion assumption. Its first source of inhomogeneity would force a second bypassed OR before g. Forward references are essential to this reasoning.
- Repeated operands are allowed. Their formal multiplication adds degrees normally; no Boolean idempotence is used in degree propagation.
- The productive path from v is a path in the extracted graph. It does not need to be a path through g. In fact g has been bypassed. The point is that v must have some remaining productive use, or deleting v itself would already be the second gate loss.
- All unequal-degree OR gates must be bypassed globally. An algorithm that stops after selectively extracting only one local component needs a separate proof and is not what is analyzed here.
- Constant 1 permits multiplication without increasing degree, and invalid references introduce zero polynomials. The stated proof deliberately assumes the ordinary constant-free, valid binary search model. Additional normalization details are required before stating it in the repository's wider `Monotone2` model.

## Heawood consequence

Let k be the number of missing target edge monomials.

If k=0, the full 21-edge shadow requires at least 27 gates by the existing generic pair-clean bound, already contradicting the 26-gate budget. If k=1 or k=2, the shadow is a proper nonempty subgraph, so its Boolean function differs on the missing edge assignments. The stronger lemma gives a shadow with at most 24 gates.

The three edge-disjoint perfect matchings listed in `quantitative-shadow.md` show that deleting any two edges leaves a perfect matching. Thus for k=1 or k=2 the shadow has vertex-cover number seven. The generic lower bound requires

`(21-k) + 7 - 1 = 27-k`

gates: 26 when k=1 and 25 when k=2. Both exceed 24. Consequently k>=3. If the degree-two component is empty, k=21 and the conclusion is immediate.

The SAT implementation therefore may require at least three absent target-edge bits at the output, provided it uses the exact constant-free forward binary model. This conclusion rules out a structural class of candidate circuits; it is not a proof that no 26-gate witness exists.

## Verification status

Constructive mathematical review: PASS. The lower_bound agent independently reviewed the argument and also reported PASS under the stated constant-free assumptions, identifying productive pruning, absence of zero/constant wires, and degree propagation along the retained path as the formal obligations. It found no sharing counterexample. No additional empirical search or Lean compilation was used.
