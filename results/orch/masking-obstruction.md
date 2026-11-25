# Singleton masking and the scope of L-meta-3457

This is a mathematical reduction, not a Lean proof of L-meta-3457 and not a counterexample to it.

Let N≥1. Let C be a backwards-reading monotone fan-in-at-most-two circuit computing the bipartite incidence function f_I on P∪L, with |P|=|L|=N. There is a circuit C_mask of size at most C.size+4N−1, computing the same function, such that every gate of C_mask except the two initial OR trees is false on all unit inputs. In particular every AND is false on all unit inputs.

Construction:

1. Compute A=OR(P) and B=OR(L), using N−1 OR gates each; for N=1 these are input wires.
2. Compute M=A AND B, using one gate.
3. For each of the 2N original input wires x_i, compute x_i'=x_i AND M, using 2N gates.
4. Replay each original gate in order on the remapped wires. An original empty AND is replaced by unary OR[M]. All other original OR and AND gates, including unary gates and empty OR gates, retain their operations and remapped inputs. This retains exactly one replay gate per original gate. An out-of-range original output is represented by an out-of-range new output and remains false.

The wire invariant is w_i'=M AND w_i. It holds for inputs by construction. For nonempty OR and AND it follows from Boolean distributivity/idempotence; it also holds for empty OR. The exceptional empty AND originally equals true, so its masked value is M, exactly the replacement unary OR[M]. This explicitly handles the zero-arity gates permitted by Monotone2; no hidden positive-arity hypothesis is needed.

On each unit input M=false. Hence all masked input wires and all replay wires are false, and the gate computing M is false. The initial OR trees contain no AND. ReadsBack and fan-in-two are preserved by sequential construction and index remapping.

The final output is M AND f_I. Since any true incidence edge uses both parts, f_I implies M, so this is exactly f_I. The overhead is 2(N−1)+1+2N=4N−1.

Consequently, the precise statement of L-meta-3457 combined with checked HEAD L_meta_3447 (whose conclusion is |E|≤5*D.size+1) implies for every such arbitrary original C:

    |E| ≤ 5*C.size + 20*N − 4.

For a projective-plane incidence graph with N=q²+q+1 and |E|=N(q+1), this would give

    5*C.size ≥ N(q−19)+4,

hence a superlinear monotone circuit lower bound as q grows. The reduction is entirely independent of C4-freeness; that hypothesis is used only when applying L3457 and L3447.

This explains a concrete obstruction to the degree-two/singleton-support approach. After masking, every replay wire has empty singleton support, while the complete arbitrary computation is retained on every cross pair. Thus facts derived only from singleton supports cannot by themselves settle the multi-edge dirty-AND case. They need a further global invariant sensitive to nonincident pairs and size.

Historical context only: Jukna, Disproving the Single Level Conjecture, SIAM J. Comput.36(1), 2006, Section 8, Problem 8.2 asks for a superlinear monotone circuit lower bound for an explicit quadratic function. That question is stated for quadratic functions generally, rather than specifically for bipartite C4-free graphs. This note does not assert the problem's current status. Primary source, read 2026-11-25: https://web.vu.lt/mif/s.jukna/ftp/single1.pdf , PDF page 17. The paper's saturated non-bipartite counterexamples do not refute L3457.

Independent source census: no same/stronger theorem was found in an additional search of61 HEAD Outside files containing AND-count/singleton terminology. L_meta_314 provides a checked cycle-specific characterization and may supply a further even-cycle partial, but does not handle general incidence graphs. All fetched source material was written under this scratch directory; no Lean process was started.
