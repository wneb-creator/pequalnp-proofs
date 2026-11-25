# L-meta-4675 exact library and public-status audit

No full proof or refutation has been found. The statement is stronger than L4970: it assumes only bipartite C4-freeness, strict AO2 correctness, and syntactic tCount zero. There is no semantic pure-star witness premise.

## Exact checked census

A bounded filename census of Outside files containing the exact identifier `tCount` found exactly one checked source: `lean/PEqualNP/Outside/L_meta_4791.lean`. Its final theorem transforms any nonempty AO2 circuit false on all singleton inputs into an equivalent tCount-zero circuit D with `D.size + 4 <= 6*C.size`. It is a transformation, not a lower bound. Searches for the substring tCount without word boundaries also match notCount and SplitCount and must not be treated as an exact census.

The archived checked L4970 Shield component has the same factor-six bound. Factor three was only an earlier mathematical construction idea (shield each original OR operand with a duplicated-input AND), not a checked artifact. An initial message incorrectly called factor three checked; that claim was corrected immediately.

The complete selected filenames, final theorem headers, and query stderr are preserved in scratch `gap4675/library_route/tcount-exact-*`. No exact tCount lower-bound theorem was found.

## Other checked interfaces

- L3525 gives the full `edges + minimum-cover <= gates+1` lower bound for acyclic graphs and arbitrary monotone circuits. L1737 is a related forest result. C4-freeness does not imply acyclicity.
- L8933 gives the full desired graph lower bound under the additional condition that no non-below-target AND gate accepts two distinct edges whose endpoint pairs are both reread. This isolates a concrete dirty-AND obstruction. Syntactic tCount zero does not immediately exclude it: a conjunction of a point-only OR and a line-only OR already has tCount zero and can accept many false-positive pairs before later filtering.
- L616 gives `n + tau <= size` for cubic graphs without four-cycles, weaker than `edges + tau - 1` at cubic density.
- L217 and L2399, identified in the earlier audit, prove AND-count at least a vertex-cover lower bound only for thresholds at most five, using finite certificates. No unrestricted AND-count theorem is asserted here.
- Our prior PostedEdgeBound proves `edges <= 2*OR-count` only with the additional pure-star witness premise; it cannot be applied to L4675.

## Public status

Structured GitHub PR searches over all states for 4675, 4970, and the literal identifier tCount each returned an empty JSON list. Full responses and stderr are preserved as `pr4675.json`, `pr4970.json`, and `pr-tcount.json` in the same scratch folder. These are exact query results, not a census of every semantically related PR.

## Difficulty boundary

Composing the posted statement with checked L4791 would imply a lower bound proportional to the number of edges for arbitrary monotone circuits computing these C4-free bipartite edge functions. The prior primary-source audit in library_route_4970.md cites Jukna's Remark10, which distinguished the easy multioutput matrix bound from the single-output Boolean bilinear-form bound and called the latter unknown in that source. That historical statement does not establish current research status. No verified modern theorem or concrete counterexample closing the present task was located.

The most concrete structural interface is L8933's dirty-AND obstruction. A valid route would have to eliminate or charge such gates while accounting for their later filters; treating syntactic OR-only input reach as semantic purity is invalid.

## Stop status

Root later assigned an additive-input-count shielding compiler, then issued STOP before any source was written or any compiler was launched. The unformalized construction prepends n gates AND(i,i), maps every original input reference and output w to n+w, and would have exact size C.size+n. Invalid original outputs remain invalid after that shift. Existing Shield.mem_orIn would make the T0 argument short because every new OR operand is at least n. This is only an outline, not a checked theorem. No active process or new Lean artifact remained at STOP.
