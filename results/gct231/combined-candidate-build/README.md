# Compiled preservation candidate

This frozen candidate preserves the prior 1528-line named body and six independently checked components. It is a partial preservation artifact: the posted existential theorem remains absent. The named file was not changed by this branch.

The exact source compiled successfully with Lean 4.36.0, one worker, a 450-second limit and a 6-GiB RSS limit. `combined-build01.json` records the source hash, elapsed time, memory, exit code, and completion timestamp. `combined-build01.log` is the full compiler log. Root and an independent child reviewed body preservation, imports, namespaces, options, and forbidden constructs; their complete results are included.

`components/` contains the exact inputs under stable labels. Their original paths and hashes are recorded in `assembly-manifest.json`; source inner bodies are preserved bytewise. The three subsequently reviewed endpoint additions are not part of this compiled V1 candidate. They appear in the distinct V2 candidate to be built by the root agent under the named path.
