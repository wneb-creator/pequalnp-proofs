# Fano-line maximal partner assessment

Author: lower_bound. Date: 2026-11-25. This is a construction assessment and a conditional mathematical obstruction, not a new Lean result or a solved gap.

With a fixed linear factor `OR(all left)`, the largest allowed complementary factor is `B(L,R)=G(L,R) OR D(R)`, where D detects a Fano line among the right inputs. D must be on the opposite side: adding left-side line terms would survive the fixed linear factor and give false positives.

The seven-variable D has both a DNF of the seven line products and a CNF of the same seven line sums. It is self-dual. The short finite probe verifies these identities on all 128 inputs. If `z_i=OR(N_i(R))`, then `D(R)=AND_i z_i` and `B=OR_i(L_i AND z_i) OR AND_i z_i`. The possible weights of the correlated z-vector are 0,3,5,6,7. This is a useful specification, but computing all seven z sums separately and then applying the obvious outer circuit exceeds the desired budget.

Around one Fano point, label the three opposite pairs `(a,A),(b,B),(c,C)` and the marked point x. Then

`D = c*(a*b OR A*B) OR C*(a*B OR A*b) OR x*(a*A OR b*B OR c*C)`.

Here multiplication means Boolean AND. The first two terms cost nine binary gates together; the third costs six; their final OR gives a 16-gate circuit. This is an upper bound only. The probe records an explicit network in assignment-compatible seven-point coordinates and checks all 128 inputs.

Simply retaining those 16 gates and adding three OR-injection gates carrying left-only signals cannot yield a 19-new-gate partner. The seven singleton-left cofactors of B are exactly the seven neighborhood ORs: D is absorbed because every Fano line meets every neighborhood line. These cofactors are pairwise incomparable. Three injection bits cannot encode seven incomparable cofactors; their Boolean cube has largest antichain three, and four bits still allow only six. At least five interface signals are necessary.

There is a stronger conditional consequence for the exact maximal partner. Mark all structurally pure-left wires, including the six fixed prefix gates. Every path carrying left information to a non-pure-left output crosses a gate with one pure-left fanin and one non-pure-left fanin. Cutting those pure-left signals expresses B as a monotone function of the cut signals and right inputs. The seven singleton-left patterns must form an antichain, so at least five distinct signals, and hence at least five such boundary gates, occur. On setting all left inputs to zero, every pure-left wire becomes zero; each boundary gate becomes either zero or its other input and can be removed. Removing the six prefix gates and these five gates from a 25-gate partner network leaves a circuit of at most 14 gates for D. Thus an exact maximal partner using 19 new gates would imply `C(D)<=14`. Root independently reviewed this mathematical argument. It remains unformalized and applies to the exact maximal partner `B=G OR D`; no lower bound `C(D)>=15` is established here.

The conditional obstruction does not apply directly to an arbitrary allowed partner between G and Bmax. Its zero-left cofactor may be a proper subfunction of D, including zero. It also does not establish that a 16-gate formula is optimal, or that a useful mixed construction is impossible.

A tempting direct matroid substitution fails concretely. To make a right variable generate exactly its three required cross edges inside a Fano-line function, it can activate a noncollinear triple complementary to its incidence line. But two different such triples have a union containing a Fano line, which creates forbidden right-pair minterms. Additional filtering would be necessary.

The repository's `R_meta_1480_*` interfaces concern the 14-variable Fano incidence edge function and a double-read obstruction, not the seven-variable line-detection function D. No result from that separate posted gap was assumed.

Reproduction:

- `/tmp/oec/pequalnp-pilot-70/lower-bound/fano_line_probe.py`
- `/tmp/oec/pequalnp-pilot-70/lower-bound/fano-line-probe.log`

The probe exited 0 in under one second, verifies the 16-gate upper bound and identities, and exhausts Boolean antichains through four bits. No new SAT instance, production solver, or Lean build was started.
