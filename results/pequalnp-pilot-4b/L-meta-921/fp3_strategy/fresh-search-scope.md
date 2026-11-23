# L-meta-921 fresh pass

> Archive note: These are historical research-phase notes. Statements that no repository files were changed describe that phase, before this authorized archival checkpoint. Scratch paths and unpreserved search artifacts below are provenance, not archive dependencies.

The full 39-gate statement remains unproved and unrefuted. No repository file was changed. Results below are mathematical arguments and ordinary finite synthesis evidence; no new Lean theorem is claimed here.

Work in the dual monotone model: each output for a four-point line L agrees with AND_L on supports of size at most five. Distinct lines intersect in at most one point. Exact line supports are called positive line inputs. A monotone circuit is correct on all positive promised inputs once it is true on each corresponding positive line input.

## Stronger normalization: no private wire feeds an OR

Call a gate wire private if it is true on at most one positive line input. An arbitrary OR gate g=u OR v with a private operand gate u can be eliminated without increasing size, even when it is not the first OR.

If u is false on every positive line input, bypass g by v. This preserves all positive line evaluations and decreases all other evaluations.

Otherwise u is true only on line K. When g, u, and the chosen K output are three distinct gates, bypass g by v, suppress u and the old K output, delete those three gates, and rebuild K with three direct AND gates. All other positive line inputs are unchanged, all negative promised inputs remain rejected, and the repair computes K exactly.

There are two coincidence cases. If u is already the K output, retain u and simply bypass g by v; the other positive lines have u=0, so their evaluations are unchanged. If g is the K output, then u<=g and u(K)=1 show that u already computes the K target on the promise. Bypass g by u globally, retaining u as K's output. This again preserves every positive line input and only decreases negative evaluations. The OR gate is deleted without needing a repair.

The operand cannot be a raw input variable in the projective-plane instance, since each point belongs to four positive lines. Constants cause only simpler bypass cases.

Therefore a size-minimal, then OR-count-minimal counterexample has no private gate feeding an OR gate. Wires false on every positive line input can first be suppressed and removed. All remaining private gates are AND gates; their AND descendants remain private, so the private part consists of thirteen disjoint AND-only tails. The shared subcircuit is ancestor-closed. After removing duplicate factors, each tail is a conjunction of d_L distinct shared boundary wires and needs d_L-1 private AND gates. Necessarily d_L>=2, since a single shared boundary wire is true on at least two positive line inputs. In a minimum-size counterexample d_L<=4 as well: a longer private tail can be replaced by the direct three-AND construction of its target line. The unresolved shared-part inequality is

    number of shared gates >= sum_L max(0, 4-d_L).

In the normalized range 2<=d_L<=4 this is exactly twice the number of two-wire frontiers plus the number of three-wire frontiers.

This normalization is mathematical progress, not a proof of that inequality. In particular shared CNF constructions can compute a function such as ac OR AND_K without any private gate feeding an OR, so three private gates per output do not follow immediately.

The formal-audit agent independently reviewed the arbitrary-OR elimination, its collision cases, and the shared/private decomposition and found no mathematical flaw. Circuit deletion and reindexing have not been formalized here.

## First-OR elimination with a non-singleton operand

This reduction allows arbitrarily many later OR gates.

Let g be the first OR gate. Its input functions are conjunctions of variable sets A and B, or constants, since all earlier gates are AND gates. Suppose B is a nonconstant conjunction involving at least two distinct variables. B is contained in at most one target line K. If it is contained in none, replace g by its other operand A: this preserves every positive line input and decreases every wire value, so all negative promised inputs stay rejected. No repair is necessary.

Suppose B is contained in K. Replace g by A and rebuild the K output at the end with the direct three-AND construction of AND_K. No other output needs repair: on every other positive line input, B was false, so replacing g by A changes nothing there. Subsequent suppressions of wires that were false on all other positive line inputs also change nothing there. All modifications before the repair only decrease gate values, preserving every negative promised input.

Three old gates can be deleted to pay for the three new AND gates:

* Delete g, redirecting its uses to A.
* Delete the producing gate h of the B operand, redirecting its other uses to false. It is a gate, since |B|>=2.
* Ordinarily delete the old K output gate o_K, also redirecting its later uses to false. It is false on every other positive line input.

If o_K equals h or g, these are not three distinct gates. In either case B must be the entire four-point set K: otherwise the assignment supported by B, of size at most three, would make the chosen K output true, contrary to correctness. The AND-only cone producing B then contains another nontrivial AND gate r, distinct from h, whose variable support has at least two points and lies inside K. Use r as the third deleted gate. Every such r is false on every other positive line input by the intersection bound. The same reasoning handles a non-earliest or redundant B wire: a four-variable conjunction requires at least two distinct nontrivial gates in its cone.

When all three ordinary gates are distinct, deleting o_K is safe even if it had downstream uses: it was false on every other positive line input. Replacing a removed wire by false and deleting/reindexing its gate is available in the abstract model; the project's invalid-index convention also supplies false without a new gate.

Thus the transformation does not increase total gate count and strictly reduces the number of OR gates. False or true constant operands are simpler, and a singleton conjunction can be redirected to its corresponding input variable.

Consequently, a counterexample minimizing size and then the number of OR gates must have its first genuine OR gate equal to x_a OR x_b for two distinct input variables. This does not show that every OR gate can be made a singleton OR, and does not eliminate the remaining case.

## Why the singleton case is still open

If g=x_a OR x_b is forced to true, correctness is preserved on all supports of size at most four. For a false target input X of size at most four, at least one of X+{a} and X+{b} is still false for AND_L; that extension has size at most five and turns the original g on. Monotonicity then forbids a newly accepted X.

The same argument fails at size five because the extension has size six. This failure is real for a circuit transformation, although it does not supply a size counterexample. For example,

    F_L = AND_L OR ((x_a OR x_b) AND AND_C),

where C is a five-element set disjoint from {a,b}, is correct for L on supports of size at most five. Forcing the displayed OR to true introduces the false positive C. One can take L={0,1,3,9}, a=0, b=1, and C={2,4,5,6,7}.

A proof still needs to charge or eliminate these five-point leaks without spending more gates. Every exact-line accepting certificate involving the singleton OR already contains all four target variables in the context outside that OR, but converting this certificate fact into a simultaneous circuit rewrite remains unproved.

## Output sink normalization

In the dual model, choose one wire for each target output. The L output is false on every other positive line input K. Replacing its later uses by false preserves all other positive line inputs, and decreases values on negative inputs. Its own selected output is retained. Repeating this operation makes all outputs sinks without adding gates. They can then be placed last, in any prescribed line order.

This justifies the outputs-last reduction in the direct dual synthesis experiments below. It is not merely an optional search heuristic.

## Certificate splice test

If an accepting proof of L factors through wire g with an outside context C contained in L, every accepting set B for g satisfying |B union C|<=5 must satisfy L subset B union C. Otherwise splicing the proof for B into the same context yields a promised false positive.

Thus a context of size at most one makes g exclusive to L among all other positive line inputs. A disjoint two-point certificate with a two-point context prevents g from having a certificate of size at most three inside any other line. These facts give three disjoint charges per output when the accepting proof trees are multilinear. Repeated variable occurrences in general proof DAGs are the unresolved obstruction to applying this argument universally.

## Finite searches

The script small_promise.py reuses the ctypes Z3 wrapper from lean_setup/meta952/synthesize.py. It checks all supports of size at most five in the dual model, allows AND/OR gates, allows constants, and uses the justified sink normalization. Exact SMT inputs, metadata, and result JSON are retained here.

| Line family | Inputs | Gate cap | Result |
|---|---:|---:|---|
| 0123, 0456 | 7 | 5 | UNSAT, 0.26 s |
| 0123, 0456, 1478 | 9 | 8 | UNSAT, 46.02 s |
| Four general-position lines on ten points | 10 | 11 | UNKNOWN, 60 s timeout |

The direct costs are six and nine gates. These are finite solver results, not kernel-checked universal lower bounds. They show no small local gadget saving in these two configurations. An earlier unrestricted-output version of the three-line search timed out; the justified sink normalization enabled the completed result.

The four-line instance is 0126, 0347, 1358, 2459, with direct cost twelve. Its timeout gives no satisfiability conclusion.
