# Library route for L-meta-2583

The new desk statement asks no-larger AO2 READ1 normalization for arbitrary projective-plane incidence circuits. READ1 here means an individual proof tree for each prime implicant reads each variable at most once; it does not mean each circuit input has fanout one.

## Existing exact components

- `L_meta_7684.lean` constructs an AO2 READ1 circuit from any bipartite vertex cover A,B, with size at most `|E|+|A|+|B|-1` (~50KB). sat_encoding is adapting this to the canonical projective-plane upper bound `N*(q+2)-1`.
- `L_meta_4897.lean` proves every AO2 READ1 circuit for a C4-free bipartite edge function yields a vertex cover A,B satisfying `|E|+|A|+|B|≤C.size+1` (~94KB). Its adaptation `new2583/library_route/ReadOneCost.lean` compiled with exit0, only `import PEqualNP.Defs`, under namespace `PEqualNP.Outside.L_meta_2583.ReadOneCost`; final helper is `cover_bound`. Full diagnostics saved as `readone-cost.stdout` (warnings) and `.stderr` (empty). Parent was notified immediately.
- `L_meta_7639.lean` gives the equivalent read1 lower bound `|E|+N≤C.size+1` when the C4-free bipartite graph has a perfect matching.
- `L_meta_8805.lean` lines890–974 already proves projective-plane point degree `q+1` (`lines_through`), two incidence double-counting lemmas (`cardL`, `cardR`), and every bipartite cover has `N≤|A|+|B|` (`cover`). lower_bound is adapting these. This avoids Hall/matching machinery.

## What the missing theorem entails

Plane incidence has `|E|=N*(q+1)`. Combining the checked read1 lower bound with regularity shows every READ1 plane circuit has size at least `N*(q+2)-1`, exactly matched by the canonical all-point or all-line star cover. Therefore the posted no-cost normalization is equivalent, for each computing AO2 circuit C, to the unrestricted exact size lower bound `N*(q+2)≤C.size+1`. I am assembling this equivalence from the adapted components.

A census of329AO2-source files and41READ1 candidates found no established unrestricted exact lower bound of this strength. Existing unrestricted plane results include only `3*N≤C.size+1` (L8805 and related), while stronger asymptotic statements impose READ2/READ3. Existing reductions R4895_1/_215/_628 isolate the same unresolved unrestricted lower bound plus known star construction.

reduction_strategy found lifting/termination/block decomposition in L4293, L4295, L7372 and pure-OR interior charging in L7649. The missing transformation is eliminating or charging arbitrary internal AND gates whose function is not below the incidence target.

## Checked exact characterization

`PlaneReadOneFloor.lean` compiled with exit0 and empty logs. It combines the copied read1 cover bound with the checked PlaneGeometry module to prove `N*(q+2)≤C.size+1` from the plane axioms, AO2, incidence correctness, and READ1.

`StarConstructionFixed.lean` is a checked integration copy of sat_encoding’s canonical constructor: the `L_meta_2583_aux` prefix was nested under `L_meta_2583`, and the external `exists_read_one` declaration was enclosed in its explicit helper namespace. Proof bodies are unchanged.

`NormalizationEquivalence.lean` compiled with exit0 and empty logs. Its theorem `normalization_iff_exact_cost` shows, under the plane axioms and for any circuit-size budget `C.size`, that existence of a correct AO2 READ1 incidence circuit of size at most that budget is equivalent to `N*(q+2)≤C.size+1`. This identifies the exact remaining obligation for the posted statement.

Finally, `CostEquivalence.lean` (3315 lines,161540bytes) concatenates these checked components into a standalone file importing only `PEqualNP.Defs`. The inherited `ReadOneCost.cover_bound` declaration is also enclosed in its explicit namespace. This standalone file compiled with exit0; complete output is in `cost-equivalence.stdout` and `.stderr`. Source is frozen for independent review and preservation. It is a partial characterization, not a proof of the unrestricted lower bound or of L-meta-2583.
