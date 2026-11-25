Intermediate counterexamples for L-meta-4970

None of these constructions refutes the posted gap. Each satisfies its hypotheses and its conclusion.

Available witness centers versus AND count

Use the Fano incidence graph with points and lines indexed modulo 7, where line b contains b, b+1, b+3. It has 21 edges and minimum vertex cover 7. Start with the usual circuit that computes one three-leaf star at each point and ORs the seven terms.

For point a=0, with incident lines l1,l2,l3, replace its term by:

    g = a AND l1
    h = l2 OR g
    k = l3 OR h
    t = a AND k

This still computes a AND (l1 OR l2 OR l3). Add three unused OR gates, each computing a OR a_i, where a_i is another point on one of the three lines through a. The circuit has 8 AND gates and 23 OR gates. Its mixed-colour OR-reach count is zero.

The available witness centers are exactly the other six points and the three lines through a. All nine are forced in a cover restricted to those available centers. Thus the minimum available-center cover has size 9, larger than the AND count 8. The ordinary minimum cover still has size 7, and the posted bound is 21+7 <= 31+1.

Two independent enumerators checked all 16,384 input assignments, the semantic star witnesses, syntactic OR reach, and the available-center cover subsets. This refutes only the proposed available-center AND bound.

Constant and bypass erasure under independent-set restrictions

Use left vertices c,a1,a1',a2,a2' and right vertices b1,b2,d. The seven edges are:

    c-b1, c-b2, c-d, a1-b1, a1'-b1, a2-b2, a2'-b2

This is a tree with minimum vertex cover 3. Compute:

    u  = b1 OR b2
    v  = u OR d
    t  = c AND v
    s1 = a1 OR a1'
    t1 = b1 AND s1
    s2 = a2 OR a2'
    t2 = b2 AND s2
    z  = t OR t1
    out = z OR t2

All edges have the required pure-OR witnesses, the circuit has zero mixed-colour OR reach, and the posted bound is equality: 7+3=9+1.

For an independent set U, force its variables to true. Count a gate as erased if its output or either operand becomes constant. Every valid AO2 wire is true on the all-true input, so constant restricted wires are true; monotonicity makes this erasure condition equivalent to at least one operand being true at the characteristic input of U.

Independent exhaustive checking covered all 256 input assignments and all 66 independent sets. The maximum erased-gate count is 6. The five maximal independent sets give counts 5,6,6,6,5. Consequently, the proposed existence of U erasing at least |E| gates is false.

For U consisting of all private leaves, u remains nonconstant but becomes unused when v becomes true. A stronger argument would have to account for this additional redundancy. The checked generic cofactor budget itself remains valid.

Counting only pure OR gates and OR gates below the output

Use left vertices a,b,c,d and right vertices u,v,w,z, with edges au,av,aw,bw,cz,dz. Compute:

    r = u OR v
    g = a AND r
    s = a OR b
    h = w OR g
    k = s AND h
    t = c OR d
    m = t AND z
    out = k OR m

The three pure OR gates r,s,t supply all required witnesses. Only out is an OR gate whose entire function is bounded by the output function. Thus these two semantic classes contain four OR gates, less than |E|-1=5. The remaining OR gate h is essential to this nested-cover implementation.

Two independent evaluations checked all 256 assignments, C4-freeness, the witness sets, raw OR reach, and the minimum vertex cover. The cover number is 3, and the full posted bound is equality: 6+3=8+1. This circuit has a safe AND below another AND, so it does not refute a variant restricted to top-form circuits.
