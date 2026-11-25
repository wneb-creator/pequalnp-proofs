# Active-prefix bounded-cost preparation

Completed, independently approved preparation only. No63-gate witness
or Lean proof is present. The live K16 solver continues to use its
earlier unchanged source; this successor has not had a long target run.

Source1acc9485a918f97b95ec05d1188dadd1a3888243f630218bd6ba3ac2e3e6cea2
extends the profile-only fallback with active records forming a prefix,
output selections pointing to active records, and primary0 belonging to
the first record's left operand. It imposes no right13 or disjointness
condition. Compaction drops false references without increasing the
independent-OR membership cost. Singer translation and optional point/line
duality preserve incidence and cost; singleton orientations are restored.
The full argument, normalizer, original/normalized models, and independent
review are included.

Actual controls preserve the nested16-AND warm model's cost63/six misses,
and the near14-AND model's cost63/three misses under duality. A deliberately
gapped, rotated star with false references reduces its accounting bound
121→64 and remains exact. Its native positive control decodes64 ordinary
gates and passes all756 boundary rows; every solver clause/internal row
value was independently checked. Fixing the64-star under budget63 returns
external UNSAT, which is not a general circuit lower bound.

The incomplete target has309920 variables/1424708 clauses. Exactly its six
known positive-row constraints fail under the warm phase; all cost and
symmetry constraints hold. Native controls and all complete logs are
preserved. Raw CNFs are omitted; CNF-REGENERATION.json gives portable
emit-only argv and exact source/CNF identities. Create REGEN first; native
execution additionally needs the CaDiCaL path named by the source.
