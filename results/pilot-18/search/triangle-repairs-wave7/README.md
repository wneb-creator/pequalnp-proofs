S02 triangle589 repair preservation

Eight prepared candidate CNFs: original triangle589 connected11/K4/K6 (no runtime included); immutable best3 connected12/K4/K6 (all three completed UNKNOWN at120seconds); and rescheduled best3 dirty-early14/reverse-readyK6 (main review PASS, runtime explicitly absent). No active solver outputs were read or copied. Historical READY labels and future command recipes are provenance, not evidence of a launch or result.

Both original and improved source circuits remain inexact. Their exact functions are F OR x2(x0 OR x7)(x1 OR x4), and F OR x2x4(x0 OR x7). The latter has exactly five erroneous full inputs21,29,85,148,149. Rescheduling preserves all21gate values and every input, but different legal dependency orders need not produce nested repair domains.

Both finite single-gate controls completed12362 arbitrary operator/fanin rewrites and420308 free-output checks each in under0.1CPUsecond; neither found an exact circuit. The original control saved a boundary-score improvement to5FP; independent scalar checking here shows F OR x9 and22full errors, so it is not a better full-error seed. Controls are local finite enumerations, not proofs against multi-gate repairs or the global model.

Sources, full generation/audit logs, main and self reviews, controller deltas, exact seed metadata, both one-gate control outputs, and all three completed solver stdout/stderr pairs plus complete controller logs are preserved. No raw CNFs, solver executables, credential or lease values are included. MANIFEST.json binds every payload.

Reconstruct with Python3 and its standard library only: python3 reconstruct_triangle_repairs.py /tmp/oec/pequalnp-pilot-18/fresh-triangle-reproduction. The path must be fresh. Missing pinned sources are staged only under the named scratch root; existing different sources are rejected, never overwritten. All8CNFs/26generated files are checked against exact hashes. No solver, enumeration, network or Lean build runs during reconstruction. Completed results do not establish a21gate witness or any global/shard exhaustion. Main independently reviews before preservation push.
