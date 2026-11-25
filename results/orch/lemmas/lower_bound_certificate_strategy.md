# Certificate strategy for L-meta-10760

The current `Engine.lean` copies the 10762 search, approximately226KiB. It permits the full root lower-bound14 via existing `imp_run`, with `K=13`, `L=14`, and `t=0..13`. All claims must be checked using the original proof definitions; scratch native rewrites only guide certificate search.

`MM=214` is a pair-hash bucket count, not a mathematical graph parameter. `hb H x` tests residue `x % MM` against H. `pairsC H` restricts the initial pair merge; `ph=1` separately permits the non-pair move route. `mFull` requires all residues covered and some phase1 entry. Therefore a safe exact partition for each t is214 entries `(t,2^r,0)` plus `(t,0,1)`. Coarse all-mask `(t,FF,1)` first; split only expensive cases. Worst3010 scalar checks should fit under512KiB with the original226KiB engine if grouped in table chunks and proved by `decide +kernel`.

Old10762 engine uses arbitrary-length packed restriction lists; each counter occupies5 bits with a16 offset. I found no16-row cap. Distinguish this from the newer10758 engine's explicit16-wide parallel operations.

The110 positive restriction target bounds are in `lower_bound_candidates.lean.txt`, grouped deepest masks first. Singleton/pair bounds were independently matched by explicit monotone formula upper bounds from graph_search. This confirms their numerical sharpness; native and final kernel checks are still needed for the new row samples.

The target graph has only two automorphisms: identity, and the input map `[5,4,3,2,1,0,6]`. If the larger10758 first-gate hierarchy becomes needed, use these to collapse its42 binary AND/OR input-pair types to orbits. The larger engine works by proving no solution after each extra free first gate, forbidding earlier gate types through a validated hash filter; its final `iroot_min` upgrades the minimum bound one gate at a time. It is about414KiB before adaptation.
