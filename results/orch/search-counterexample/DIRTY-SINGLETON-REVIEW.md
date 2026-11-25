# Independent dirty-singleton cut review

Approved for arbitrary global searches with at most50OR gates. The fixed51baseline is also checked explicitly below.

`CleanOrGeneral.clean_or_bound_general` requires accepted positive samples, rejection of every distinct pairwise meet, and rejection of those meets at every OR gate; it then gives the number of positives minus one as the OR lower bound. `Flags.meet_small` shows that each distinct flag meet has support of size at most one. Every singleton lies below126generic negative rows, so a monotone separator already rejects it. The empty input is false throughout this normalized model because every free conjunction is nonempty. Thus if every OR were false on every singleton, the clean-OR theorem would force at least51ORs. Its contrapositive justifies the new disjunction for at most50ORs.

This remains valid after normalization: the normalized circuit itself is a separator with no larger OR count, so the same theorem applies to it. The singleton set and the existence-of-a-dirty-OR condition are preserved by every coordinate permutation used for first-gate symmetry.

The implementation appends exactly26singleton negatives, places the new clause over exactly their OR-wire values, and restricts the option to the global scenario and at most50ORs or the fixed51control. Ordinary output constraints, sensitivity bounds and prefix-cover cuts also process the new rows correctly. The new singleton sensitivity bound is3at each coordinate.

Independent replay of the canonical51baseline accepts all52positives and rejects468generic rows, all26singletons and the empty assignment. Exactly39OR gates are true on some singleton, with104true OR/singleton entries, so the added disjunction is satisfied. Source hash and complete finite audit are recorded in `dirty-singletons-independent-audit.json`; reproducible source and output are `audit_dirty_singletons.py` and `dirty-singletons-independent-audit.log`. No heavy solver or Lean run was performed for this review.
