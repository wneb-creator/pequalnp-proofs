# Fresh universal-simulation pass

> Archive note: These are historical research-phase notes. Statements that no repository files were changed describe that phase, before this authorized archival checkpoint. Scratch paths and unpreserved search artifacts below are provenance, not archive dependencies.

Date: 2026-11-23. The posted fixed-exponent FP3 statement remains unproved and unrefuted. No repository file was changed, and no Lean theorem is claimed by this report.

The pass read CONTRIBUTING.md and README.md first, then the exact TimeAlt definitions and the existing strategy, catalytic, factorization, circuit-compression, and algebraic reports. It did not use desk, git, gh, or credentials. Public web searches were restricted to github.com and produced no new primary-source simulation theorem used below.

## 1. A numerical opening created by the improved one-tape verifier

The strengthened restricted protocol has prospective cost A^(3/5), ignoring logarithmic factors, for a computation of time A on one writable tape. Therefore a general-machine normalization with time A=T^a would suffice whenever a<5/3. Ordinary quadratic normalization does not suffice.

An optimistic cache accounting is

    A(T,b) = T*b + T^2/b.

It would balance at b=T^(1/2), A=T^(3/2), and give verifier cost T^(9/10). The earlier objection based solely on composing this accounting with the older 2/3 verifier no longer applies after the 3/5 improvement.

The accounting is nevertheless not an implemented simulation. Its second term assumes that a remote b-symbol block can be transferred through distance O(T) in O(T) time by one writable head. Finite control cannot carry b arbitrary symbols in one crossing. Ordinary copying, adjacent shifting, or repeated shuttling incurs a payload factor. A second writable head would help transport, but it breaks the one-selected-block replay premise of the restricted verifier.

A useful quantitative version is to suppose a refill costs O(T*b^rho). Then

    A(T,b) = T*b + T^2*b^(rho-1),
    b = T^(1/(2-rho)),
    A = T^((3-rho)/(2-rho)).

For 0<=rho<=1, composing the 3/5 verifier gives an exponent below one exactly when rho<1/2. At rho=0 the resulting exponent is 9/10; at rho=1/2 it is exactly one. Thus this construction needs transport or regeneration with a sub-square-root payload cost, not merely any improvement over linear payload transport.

Exact unmet premise: a uniform deterministic one-writable-head algorithm for arbitrary source machines, using the short original input, that produces the correct b-symbol refill at that cost. A descriptor (M,x,time,address) is short but is not a fast decoder. No such decoder was obtained.

## 2. Compressing the controllers of a slow normalization

There is a second conditional numerical route. Suppose a quadratic one-tape simulation A=T^2 had a boundary-controller commitment of size O(T/b), measured by the original productive computation rather than by all simulator travel. Combining that commitment with nested replay in space b would give

    C = O(T/b + T^(2/3)*b^(2/3)).

Balancing b=T^(1/5) gives C=T^(4/5).

Standard sweeping simulation compresses repeated travel instructions, but each source step can transport new source-dependent symbols or states. Recording those symbols once per productive step still costs Theta(T), before the repetitions are compressed. Replacing transport by symbolic copy pointers removes carrier bits only by creating nonlocal provenance dependencies on source writes. Then independent local replay is no longer justified by one-head locality; the original coupled memory graph has returned.

Exact unmet premise: a short, fixed, efficiently openable controller representation that includes source-dependent carried values, of total size O(T/b). No such representation was obtained.

## 3. Higher-dimensional geometry does not fix the current budget

Consider a proposed d-dimensional single-writable-head extension, with fixed d>=1. Cubes of side b have mutable volume b^d. Assuming O(A/b) boundary events and deterministic replay in time A and space b^d, the same three-block construction has budget

    C = O(A/b + A^(1/3)*b^(2*d/3)).

Its balanced exponent in A is (2*d+1)/(2*d+3).

Even granting a geometric normalization with time A=T^(1+1/d), composition gives

    ((d+1)*(2*d+1))/(d*(2*d+3))
      = 1 + 1/(d*(2*d+3)),

which is greater than one for every fixed d. This is budget algebra, not a proof that the proposed normalization is optimal, nor a claim that an actual grid simulator and verifier have been implemented.

Exact unmet premise: a physical normalization with exponent a<(2*d+3)/(2*d+1), or a stronger local verifier. For example, a genuine normalization exponent 1+1/(d+1) would compose below one, but no layout or regeneration mechanism achieving that exponent was found.

The same calculation for a j-block local checkpoint cost A^(1/j)*b^(d*(j-1)/j) has local exponent (1+d*(j-1))/(j+d*(j-1)). Composing with 1+1/d again exceeds one, by exactly 1/[d*(j+d*(j-1))]. Merely increasing a fixed number of checkpoint levels does not repair this geometric estimate.

## 4. Exact obstruction to the direct multistack block extension

Offset cuts can still give O(T/b) boundary events on each of finitely many stacks. Between consecutive such events, however, a phase simultaneously mutates several b-symbol blocks. Replaying one block requires the other active blocks' top symbols at each productive step. Replaying the full tuple avoids that missing input only until the tuple changes; transferring each changed block's b-symbol state costs b per event and returns a total Theta(T) interface.

The mathematical object needed is a short representation of the joint block-transfer maps that is closed under composition on the encountered inputs and permits fast exact openings. Complete lookup tables for all b-bit inputs have exponential size; storing only encountered input/output words has linear total payload. This is the precise missing semantic compression step in this attempted generalization.

The short input length prevents treating the generated blocks as independent arbitrary b-bit inputs. It therefore does not justify an information-theoretic lower bound against all protocols. At the same time, low description entropy alone gives no decoding-time bound.

## 5. Why stronger fingerprints do not implement the missing refill

For a family of all B-bit candidate refill strings, the generic adaptive-certificate union-bound condition is |F|>2^B*D, where D>=1 bounds the degree of each nonzero false-certificate polynomial. Using that condition requires a field-element width at least B+log_2(D), up to rounding. Committing one binding value of that scale for each of N approximately T/B refill events costs NB=Theta(T). A logarithmic-width field has short values, but this union bound does not then establish binding of arbitrary adaptive B-bit replies. This is not a lower bound against every possible fingerprint analysis; special correlations between the false polynomials could support a stronger argument. If all false polynomials are nonzero constants, they have no bad seeds and this entropy-driven width calculation is inapplicable.

This is a limitation of this particular binding construction. A smaller previously certified candidate family, or fast exact decoding from a short name, could change the count. Establishing either property is precisely the unresolved requirement here.

## Outcome

The pass found sharper conditional thresholds, but no unconditional universal simulation, no proof of the posted FP3 statement, and no counterexample to it. The cache route at rho<1/2 and the geometric normalization threshold above are concrete research targets with their missing premises exposed. They should not be cited as achieved algorithms or checked theorems.
