# Retired triangle-factor candidate preparation

All12 prepared cases were retired before solving. S01's joint-factor argument,
independently reviewed by S04, requires at least18clean-prefix gates for the
triangle `(1,4,8)` and19for `(3,6,7)`. Every prepared case provides only17.
This is reviewed mathematics, not a Lean theorem or an UNSAT certificate. It
does not refute the parent, assigned shard, or posted existential statement.

The source, bounded controls, all12 metadata files, original reviews, and complete
generation/audit logs are preserved. The `mathematics/` directory includes the
argument, independent review source/results/logs, and explicit bindings to all
12 cases. `retirement.json` gives the final status. Historical READY labels and
six individual-cost-feasible labels predate the joint bound and are superseded;
no case should be launched on their basis.

The encoding audit remains valid: both factor products agree with the target on
all2048 inputs, and each child is the pinned J18 parent plus exactly93unit clauses,
with no new variables. Exact factors were placed at the last three prefix gates.
The suffix copies its first factor twice, then conjoins the other two. Removing
those copies gives an effective19gate construction if such a prefix existed.

No raw CNF is stored. For historical reproduction only, first obtain the exact
parent `orch/S01/consecutive-junk-v2/normalized.cnf` and its metadata; the expected
hashes are pinned in the generator and archived family metadata. The existing
S06 preservation archive contains the original-parent reproduction sources.
Given that original CNF and its matching JSON, the included unchanged
`dependencies/build_consecutive_junk.py` reconstructs the normalized parent:

```sh
python3 results/pilot-18/search/triangle-upper-factors/dependencies/build_consecutive_junk.py \
  /path/to/original.cnf \
  /tmp/oec/pequalnp-pilot-18/triangle-parent-reconstruction-fresh
```

The source pins both original hashes and adds the J18 unit3243. Its normalized
metadata must match the included `parent-metadata.json` exactly. Then run the
unchanged factor generator with that parent explicitly supplied:

```sh
python3 results/pilot-18/search/triangle-upper-factors/generate_triangle_factors.py \
  /tmp/oec/pequalnp-pilot-18/triangle-historical-reconstruction-fresh \
  --parent /tmp/oec/pequalnp-pilot-18/triangle-parent-reconstruction-fresh/normalized.cnf
```

The13 archived metadata JSONs bind all generated CNF hashes. This command does
not launch a solver. Retention documents an abandoned candidate restriction and
its reason, with no claimed machine-checked impossibility result.
