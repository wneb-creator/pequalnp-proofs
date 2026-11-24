# Completed singleton-rejecting physical repairs005/006

Both runs use the independently reviewed SearchPhysicalRepairDirty source in physical-repair-dirty/, with target28, width256,40rounds,120second cap, --reject-singletons and --min-nontrivial-dirty 2. These are explicit beam-admission restrictions, not a theorem about all raw circuits. Every recorded improvement accepts all24positive tests and is independently scalar-replayed on all88cases; it remains INVALID.

Run005,seed14772943, inspected6,203,392neighbors in120.05754seconds, improving56negative errors to52. Its three saved improvements have55/53/52errors and4/4/3diagnostic nontrivialdirtyANDs. Run006,seed14772944, continued from the52error state and inspected5,502,976neighbors in120.00491seconds, saving one49error improvement. All four saved circuits reject every singleton input, as separately verified in the included diagnostic log.

No28gate witness or UNSAT result was found. Complete stdout/stderr and exact mistaken assignment lists are preserved. Unlike earlier unrestricted physical runs, these improvements were checked to avoid singleton leakage. The search still remains heuristic and its dirty classifications use the complete test basis.
