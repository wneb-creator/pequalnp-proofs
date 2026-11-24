L-meta-1544 independent generalization audit

Reviewer: /root/counterexample_search
Source inspected: lean/PEqualNP/Outside/L_meta_1516.lean
Conclusion: the generalization is mathematically valid under the posted hypotheses.
No counterexample or missing hypothesis was found. No Lean command was run by this reviewer.

The proof before the old concrete `lines` definition is already generic in the
input dimension n. Keep binary fan-in 2, the one-colour merge cost 1, and the
intersection threshold 1 unchanged. Only its namespace needs to change.

Replace the concrete geometry block by root's generic `geometry` helper. The
needed facts are: line size q+1, intersection size at most1, every distinct line
difference nonempty, and for every line t and point v some line s contains v
while L(t) minus L(s) is nonempty. The last fact follows by joining v to an
outside point when v is on L(t), or to any point on L(t) when it is not. This uses
only pair coverage, line sizes, thin intersections, and N>q+1. The root helper
has independently passed mathematical and format review.

Required special-constant substitutions in `final_bound`:
- Fin13 becomes Fin N everywhere in its domain, witnesses, colours, and indices.
- Every wire offset13 becomes N, including row_bound's dimension, pay/props,
  output bounds, idx=o(t)-N, and idxeq.
- The row charge3 becomes q, deduced from q+1 <= 1+card(pay t).
- The total charge3*card(Lam) becomes q*card(Lam); constant-sum simplification
  still uses Nat.mul_comm, and the final omega only compares that common product.
- The remaining-output count13-card(Lam) becomes N-card(Lam).
- Remove the equality-to-cyclic-lines hypothesis and the hLeq/subst L step.
  Use the supplied L directly throughout.

Two special assumptions must not survive substitution:
- `hup (neg 0) ... (hd 0)` should use the current t instead. This avoids any
  unneeded distinguished Fin N zero or NeZero instance.
- `t in lines t` is special to the cyclic model and is NOT an assumption for L.
  In the all-ones output proof, choose any point of L(t), using card(L t)=q+1>0.

Mathematical counting argument:
For each chosen line t, mark OR gates false on its complement but true on two
distinct p-union-B(t,p) witnesses. The generic colour-merging lemma gives at
least q such gates. If one gate is marked for two distinct chosen lines, their
one-point intersection leaves an accepted witness point outside the other line
in each direction. Monotonicity then forces both forbidden B-crossings. Thus
the marked OR sets are disjoint and contain at least q*card(Lam) gates total.
All gates in I are ANDs and therefore disjoint from that OR set. Each unchosen
line has a distinct genuine gate output: its complement distinguishes it from
other outputs, the point-through-another-line fact excludes raw-input outputs,
and the all-ones valuation excludes nonexistent output wires. Those N-card(Lam)
outputs are also disjoint from the marked set. Combining these two disjoint
counts yields the requested max term.

Red-team cases checked:
- q=2 gives N=7 and satisfies every strict inequality used; no q=3 fact remains.
- Arbitrary line labels are allowed; self-incidence t in L(t) is not used.
- Lam empty, Lam all lines, and natural subtraction are handled by the same
  finite-set counts; no unstated positivity of Lam is needed.
- Empty/unary/repeated gate inputs and malformed or forward indices are already
  handled by val_and/val_or and their default-false prefix semantics. Empty AND
  is true and cannot satisfy a negative-row premise; invalid inputs cannot
  provide a true positive witness. Repeated input wires cannot create a new
  colour merger. No extra topological-legality hypothesis is introduced.
- The output map is initially arbitrary; range validity and injectivity are
  proved from the required complement valuations and line differences.
- I may include dead AND gates. The proof only uses its gate-operation condition
  and its finite-set cardinality, not reachability or productivity.
- No plane existence result for arbitrary q is needed: the theorem is conditional
  on the supplied incidence axioms.
