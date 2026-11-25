# Guarded streaming and seeded repair controls

All sources and finished artifacts in this batch are immutable. No ≤50 witness has been found.

The guarded stdin runner verifies the uncompressed CNF SHA256, streams gzip into CaDiCaL, records its own process group, reaps its reader, and preserves complete stdout/stderr. Default preflight is4GiB shared usage; runtime stop is6.5GiB. Version5 adds only a configurable positive process address limit, capped at3GiB; the secondary repair uses1GiB. The two-OR C4 gzip control passes SAT and reconstructs all6samples.

The independently audited seeded encoder fixes most positive operand signatures from the51-OR baseline. Its fully fixed control passes SAT in0.255seconds and reconstructs all546samples. The five-free-gate control passes SAT in15.34seconds and also reconstructs all546samples; it has different first-gate signatures from the baseline but still needs51ORs after sample-preserving operand compaction.

Two50-OR neighborhoods are prepared here. The first deletes baseline gate2 and frees gates0–7; it has not been queried. The selected second deletes baseline gate38 (the last pencil's final union), frees gates33–37 and46–49, and keeps all other operand signatures fixed. These free the two last pencil blocks and the final four global joins. It uses134224variables/857586clauses. Its900second run began05:37UTC under a1GiB cap; running logs will be preserved separately. Any UNSAT conclusion applies only to its fixed-signature neighborhood, never to unrestricted50-OR circuits.

The live unrestricted50 query uses the archived CNF in batch0512 and is not duplicated here. The prepared multi-output streamed runner is included as source only; it has not been queried. Compressed inputs and assignments are lossless, with original hashes in ORIGINAL-FILES.json.
