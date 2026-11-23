The trace-circuit route is conditional. No circuit compression theorem proving L-lib-123 has been established.

For a fixed binary-input/binary-output machine M, clock constant B, exponent q, and input x of length m, normalize the first N = B*2^(q*m)+B steps into one primitive stack operation per microstep, then pad after halting. A record contains finite control, operation, stack and symbol tags, each stack height. Constants depend on M. A record has O_M(log(N+2)) bits. A bit-address circuit therefore takes q*m + O_M,B,q(log(m+2)) Boolean inputs. The normalization, finite reachable-alphabet coding, and complete binary encoding remain to be assembled with the checked local trace helpers.

A sufficient compression hypothesis has this quantifier order:

    There exist natural a < b such that,
    for every machine M and clock constant B,
    there exist constants D and k such that,
    for every input x of length m,
    the bit-address function for its B*2^((2*b)*m)+B-step trace
    has a binary circuit with at most
        D*2^((2*a)*m)*(m+1)^k + D
    gates.

The circuit may depend nonuniformly on x. The verifier does not have to construct it. The first existential block guesses it. The saving parameters a,b must be common to all machines; D,k may depend on the machine and clock constant. The Lean definition in TraceCircuitHypothesis.lean states these quantifiers using the existing HasBinarySize definition and a parameter for the canonical trace-bit family. That parameter is not a claimed construction or an axiom.

Choose q=2*b and p=2*b-1. Since a<b, 2*a <= q-2. One exponent is available for arbitrary fixed powers of m from circuit encoding, evaluating several record bits, sorting evaluation certificates, binary arithmetic, and local checking. The checked ExponentBudget.lean in prior_routes proves the more general real-exponent choice and polynomial absorption. This requires a quasilinear circuit evaluation verifier: a fixed quadratic cost in gate count would invalidate the argument for arbitrarily small savings.

The first block commits to one circuit. The universal block selects times t,u and a local constraint. The final existential block supplies evaluations of the committed circuit on all needed addresses. Sound evaluation certificates force the same answer whenever an address is reused, so this repairs the adaptive local-witness problem. The mate-free local stack challenge handles matching push/pop symbols using a universal candidate push and a final existential intervening-dip position. GlobalTrace.lean now proves exact control transitions, arbitrary initial stacks, and halted clean-output semantics for the primitive model. A linear-time relation can reject oversized or malformed descriptions and use the witness block length as a clock. Its complete FinTM2 machine and runtime construction is still work, and would not remove the unproved circuit-compression hypothesis.

BinaryCircuit counts gates while storing arbitrary natural wire indices. Gate count alone does not directly bound description length. CircuitClamp.lean closes this gap: replace all indices by min(index,d+g), where d is input length and g gate count. All out-of-range indices read false, so the new circuit has identical wires and output on length-d inputs, identical gate count, and indices at most d+g. A bounded encoding then uses O(g*log(d+g)+d) bits.

Elementary Shannon compression does not supply the missing exponent saving. With x hardwired, the trace-bit truth table has O(N*log N) entries; its input length is log N + O(log log N). The generic circuit-size upper bound is approximately N up to logarithmic factors. If records had constant width, the usual N/log N gate saving would still be only logarithmic. Neither bound implies N^(1-epsilon) for a fixed positive epsilon. A short program (M,x,time,address) is not already a small circuit: unrolling the needed replay can cost N steps. There are only 2^m inputs of length m, but a small family of functions need not consist of small-circuit functions.

These facts isolate a sufficient unresolved mathematical statement. They do not prove it false, and they do not refute FP3.

A weaker machine-dependent exponent hypothesis might suffice through a fixed universal simulator if a sufficiently sharp overhead bound were proved. The existing repository universal simulation is only proved with polynomial overhead, so that does not presently replace the uniform exponent assumption above.
