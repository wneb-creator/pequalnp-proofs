# Free nonedge OR lookup

Read-only lookup by circuit_search, 2026-11-25T16:58:26.637097+00:00. No Lean build or new proof was attempted.

I did not find a checked theorem giving a 16-gate floor when the canonical nine-variable Petersen-minus-vertex function is supplied the free input x4 OR x6. This is a statement about the inspected census, not a proof that no such library result exists.

The target graph has edges 01,12,23,34,40,05,16,27,38,57,68,85. The deleted tenth vertex had neighbors4,6,7; adjacent helper0 OR4 is a different orbit and is not interchangeable with helper4 OR6.

Closest exact results:

- `L_meta_3551`: a FanInTwo circuit C computing that target from `List.ofFn x ++ [x4 || x6]` has at least15 gates, assuming x4 and x6 have distinct, unique effective reader gates and the x4 reader occurs first. An effective reader is a gate whose first input is the wire, or a non-NOT gate containing it anywhere. There is no global NOT-count assumption.
- `L_meta_3553`: the same15-gate result with the x6 reader occurring first. These two statements do not exclude a shared reader or multiple readers, and do not give16.
- `L_meta_3953`: a Monotone2 circuit of size at most14 matching the listed12 positive and12 negative rows with helper4 OR6 is impossible if raw4 and6 each occur in exactly one gate's inputs. This is a conditional15 lower bound.
- `L_meta_4986` and `L_meta_4988` are narrower versions of the same15 bound with zeroNOT/one-to-twoNOT premises and ordered sole readers; they provide no stronger bound than3551.
- `L_meta_3346`: FanInTwo C computing the target, with its first PAID output wire9 equal to x4 ORx6 and its second gate AND, satisfies16 <= C.size. The paid OR is counted in16; stripping it only gives a15 lower bound on the remainder.
- `L_meta_3233`: a16 lower bound with paid first OR4/6 and second OR plus an explicit symmetry-order guard. `L_meta_2746` is the degenerate no-second-gate branch of the paid-prefix problem. Neither is a free-OR16 theorem.
- `L_meta_4439`/`L_meta_4401` reduce a <=15 paid-first-OR circuit with second OR to <=13 gates with two supplied OR helpers; `L_meta_4405`/`L_meta_4445` exclude specified second helpers at that13 budget. Even assembling these branches concerns the paid-first-OR16 threshold, not free-OR16.

Scope: inspected the supplied416 candidate filenames,269 previously extracted statements, and42 strong statement summaries, then re-extracted final theorem text from the416 existing files to avoid truncation at local `have ... := ...` definitions. The direct pair scan excludes `&&` boundaries to avoid reading the disjunction between two edge monomials as a free helper.28 resulting correct-orbit/superset statements are preserved in `free-or-neighbor-pair-statements.json`. Wider preliminary extraction tables contain false-positive supersets and are lookup aids, not classifications.
