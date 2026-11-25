Zero-paid-NOT structural investigation (unformalized notes)

Status: no full exclusion or counterexample. No new broad SAT run was started. The statements below are proof ideas, not newly Lean-checked results. The existing independently checked cofactor floors and root/agent helpers remain the formal evidence.

Ordinary monotone size18 equality case

After choosing a minimum clean circuit computing the ordinary ten-variable Petersen function, the checked nine-variable cofactor floor16 implies at most two direct readers of every raw vertex. This uses vertex transitivity to transport the checked cofactor floor. Exact two-input, useful-gate normalization and absorption deletion are needed for the following counting arguments.

If g=AND(x,H), then g is pointwise at most x. A direct reader of g that also directly reads x is redundant: AND(x,g)=g and OR(x,g)=x. In a minimum circuit these absorptions forbid such a reader. The output cannot be g, because the x=false cofactor is nonconstant. Fixing x=false therefore deletes the raw-x reader gates and at least one separate direct reader of g. The cofactor16 bound forces exactly one raw-x reader and exactly one direct reader of g. That unique successor must be OR: if it were AND, the false constant would propagate to another gate (or make the output constantly false), saving a third gate. Thus every raw-AND occurrence forms a private two-gate branch, AND followed by OR. The lower_bound agent agreed this argument is sound under the stated minimum/normalization hypotheses, but it was not formalized during this job.

An earliest raw OR g=x OR y has both endpoints read elsewhere. A sole OR reader with raw partner y would violate the checked SoleOrPartner singleton rejection (after relabeling the ordinary monotone setting). The cofactor bound then makes both endpoints have exactly two readers. Their second readers must be OR, by the preceding private-AND argument. This forces four primary OR incidences and exact deletion equality for both first-OR endpoints. It does not exclude the circuit.

The remaining obstruction is a first AND whose operands are both computed OR sums, with nonedge products later filtered away. C4-freeness rules out sharing in ordinary star covers but does not directly rule out such mixed truth signatures. Treating these computed products as disjoint rectangles would be an unsupported inference. A useful missing lemma would be a sufficiently strong cofactor lower bound with a free nonedge OR, or a rigorous classification of equality cases for cofactor16.

Limited library census

A bounded census of the 142 Outside files mentioning Petersen did not reveal the needed unconditional nine-input free-nonedge-OR floor16. In that census, L_meta_1922 gives a free(0 OR4) sparse-row floor15; L_meta_2149 handles a first(0 OR4) followed by AND with total floor16, so only a free-prefix floor15; L_meta_2752 and L_meta_2748 cover other specific initial patterns. These weaker statements must not be substituted for the missing floor16. This was not a complete semantic census of every repository theorem. Complete search stdout/stderr were retained in /tmp/oec/pequalnp-pilot-103/petersen-bounds.stdout and .stderr.

Free complement / zero paid NOT

The checked two-reader bound gives the positive0 OR reader and negative0 AND reader in the live-rail equality case. The positive reader's partner H at x0=false satisfies the guard H AND OR(neighbors0) <= cofactor. This does not by itself force H to accept an unsafe alternating triad: H could be pointwise below the cofactor. The prior SAT unsafe-H family is therefore a focused auxiliary, not an exhaustive full-target split.

LeastLiftNormalization is about the full independent n-input circuit function. Its PC condition cannot be invoked with an implication known only on the valid eleven-input dual-rail slice. A possible repair is to parameterize the pointwise Boolean lifting transformations and the least-size choice by the actual input family. If a version preserving only the valid slice is established, a safe positive-OR partner H could be lifted into the output OR set; that would force the positive input itself below the target and contradict the singleton0 assignment. This is a proposed normalization route, not a checked extension. Even after it establishes an unsafe H, the existing sixteen-gate cofactor/unsafe-triad auxiliary remains open.
