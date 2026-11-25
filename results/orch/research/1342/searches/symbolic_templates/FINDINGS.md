# L-meta-1342 bounded symbolic shared-gate search

No21-gate witness found. Three45-second HiGHS MILP runs each reached its time limit without an incumbent. This proves no impossibility, even within the template families.

The first family contains all stars, every3-edge-path CNF decomposition, triangle majority CNFs and alternative selector decompositions, with complete Boolean truth tables used as semantic gate keys. There are63path/triangle templates,546binary actions and132output blocks. The wrapped family adds `(vertex OR dirtyIntermediate) AND thirdClause` whenever its complete truth table is below the target function, enabling the optimizer's cost-neutral triangle wrapping; it has1827actions and153blocks. The final active model prunes actions with no path to a block and requires every selected action to have a selected consumer, leaving726actions and153blocks.

Each model requires exactly2junk AND actions and at most21total binary gates, counting the final OR tree. Allcandidate gates use only AND/OR. Blocks are verified below the graph function on all2048 assignments and their accepted edge pairs must collectively cover all16edges. Any returned DAG would then be reconstructed and rechecked for all2048inputs. None was returned.

The initial run-001.log records a startup error before the script was written; valid runs are run-002.log, run-wrapped-001.log and run-active-001.log. Complete logs, resultJSONs and sourceSHA256 hashes are retained; see validation.json. No tracked files changed.
