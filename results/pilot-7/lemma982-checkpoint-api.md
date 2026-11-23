# Compact certificate interface

The pure decoder is `Checkpoint982Decoder.lean`; copy its namespace body without the final examples. All declarations live in `PEqualNP.Outside.L_meta_982_aux.Checkpoint`. The generated data and wrappers live in sibling namespace `CheckpointData`.

For core `N`, use `cNStates : Nat → Nat → List Nat`, `cNCount : Nat → Nat`, `cNAdvice : Nat → Nat → Array Nat`, `cNPerms : Array (List Nat)`, `cNPool : List Nat`, `cNRows : List Nat`, `cNinputs : List Nat`, `cNK : Nat`, and `cNMask : Nat`. Advice entries use the unchanged original convention `tag + 1024 * (1 + symmetry + 64 * childIndex)`; tags and group indices retain their original meaning. State recipes are internally packed more tightly, with a per-layer tag width.

For the twelve large cores, retain only remaining budgets `cap`, `cap−1`, `cap−2`. The cutoff is8 for cap10 cores and9 for cap11 cores. `cNCount s=0` below the cutoff. Prove cutoff leaves using `Fast.rejectLeDepth`, then `Reduced.rejectLeDepth_no` via equality and `pairedBar_all_le_from_leaves`. Do not use exact-budget `rejectDepth` for the upper-budget theorem. The raw JSON reports every count and packing width.

For seed0 and seed8, the full DAG remains. Seed0 retains only the maximum-budget root9 and reachable states, then reindexes to331 states; old combined-budget357-state proof indices therefore change. Seed8 retains116 states with its original indexing.

Symmetry actions have exactly the original indexing. `Checkpoint.group` starts with the identity permutation, then appends `new[j]=old[generator[j]]` from packed parent/generator recipes. `Checkpoint.actions` applies the final reference permutation to restore the original group indexing. Core26 needs two generators for its48 actions, saving about40KB. The generic symmetry proof can reason through generator composition; final arrays can also be used directly by the existing checker.

To reproduce large packs, run `python3 lemma982_checkpoint_pack.py --depth 2` from any explicit working directory. To reproduce small full packs, add `--depth 20 --case 0` or `--depth 20 --case 8`. Default scratch directory is `/tmp/oec/pequalnp-pilot-7`; `--directory` changes it. The script reads existing core data and writes only `lemma982-checkpoint*` outputs.

Total emitted data plus usable wrappers is230141bytes. Decoder is about3.7KB. Parent/state/checker proof text is separate. Twelve large checkpoints lead to250592 surviving DFS visits, compared with67560 stored DAG states. A benchmark sample for core28 remaining9: index251 is easy (1 surviving visit),986 median (20),0 moderate (108),1086 hard (1440).

`Checkpoint982AllDataCheck.lean` compiled with exit0 and empty diagnostics. It elaborates all fourteen generated data modules and proves two concrete seed8 kernel equalities, for state(8,0) and advice(9,0). This is not a full closure check. Python independently round-trips every retained state, packed stream and group composition. See `lemma982-checkpoint-manifest.json` for hashes and exact validation scope.
