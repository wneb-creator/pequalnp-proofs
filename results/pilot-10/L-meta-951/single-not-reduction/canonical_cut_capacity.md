# Antitone oracle capacity at a monotone decoding cut

This is a mathematical observation, not a Lean-checked proof of L-meta-951.

Let F : {0,1}^n -> {0,1}^m be the OR-family map, so F preserves joins. Suppose
F(x) = D(b(x), z(x)), where b(x) consists of k arbitrary Boolean cut wires,
z is antitone, and D is monotone in all k+1 arguments. Then |range(F)| <= 2^k.

For each reachable output vector v, write C_u for the output-incidence column
of input u, and define M_v(u)=1 exactly when C_u <= v. Then F(M_v)=v: every
selected column is <=v, and every active input of any witness F(x)=v is
selected. Moreover v<=w implies M_v<=M_w.

The map v -> b(M_v) is injective. If two ordinary codes agree and their oracle
bits agree, deterministic decoding gives equal output vectors. Otherwise,
reorder the two vectors so that z(M_v)=0 and z(M_w)=1. Monotonicity of D gives
v<=w, hence M_v<=M_w. Antitonicity of z would then require 0>=1, a contradiction.

Zero-incidence input columns are included in every M_v and cause no problem.
Only reachable output vectors are used; a constant map has range size one.

The SMT experiments in cut_encoding.py impose exactly code(x)<=code(y) =>
F(x)<=F(y), together with antitonicity of the distinguished oracle bit. The
ordinary cut wires have arbitrary truth tables. They report UNSAT for:

- Triangle edge ORs with two ordinary cut bits (triangle_cut2.log).
- Four-cycle edge ORs with three ordinary cut bits (cycle4_cut3.log).
- K4-star/Pasch ORs with three ordinary cut bits (pasch_cut3.log).

Their range sizes exceed 2^k, so the observation explains these finite checks.
A global charging argument converting such cut constraints into the desired
sum-of-set-sizes gate lower bound has not been obtained.
