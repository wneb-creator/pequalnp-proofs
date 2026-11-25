# Failure of a local clean-cover potential

This is a counterexample to an attempted proof invariant, not to L-meta-2602.
Let e_i = x_i AND y_i for five disjoint matching edges, i=0,...,4. Build a=x_0 OR e_1 OR e_3, b=x_0 OR e_2 OR e_4, t_1=y_0 OR e_1 OR e_2, t_2=y_0 OR e_3 OR e_4, adjoining the original input before the edge terms in each two-OR chain. The prefix includes the four e_1,...,e_4 AND gates and all original inputs.

Among the AND closure of these available functions, any clean function covers at most one of e_1,...,e_4, possibly also e_0. The minimum number of clean AND-meets needed to cover the target is four. Adjoin one OR u=a OR b. Now u AND t_1 covers e_0,e_1,e_2 and u AND t_2 covers e_0,e_3,e_4, so the minimum drops to two. Their OR is exactly the matching function on all1024 inputs. All16 gates are active and essential on some minimal edge. For each marked edge e_1,...,e_4, both formal derivative values are zero.

The full AND closures have12112 and12922 functions; independent truth-table code records all distinct clean edge profiles and exact set-cover costs in tau-drop-counterexample.json. The diagram-free counting argument above was independently checked by structural_proof. These computations are not Lean proofs.

A stronger OR-branch normalization could exclude the construction: deleting the x_0 branch from the first x_0 OR e_1 does not lose an output edge because b still supplies x_0. Gate essentiality alone does not exclude it. A successful counting proof must account for earlier dirty OR costs or justify a stronger normalization.
