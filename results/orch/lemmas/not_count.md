# Unary count refinement

The checked scratch module `not-count-helpers.lean` contains a full semantic bridge for the target graph. It imports `KernelEngine` only to avoid duplicating the generic search engine in scratch. For final integration, inline its body after the generic engine in the owned namespace, retaining only the allowed project import at the file top.

`LR m T q u S` records a `Live` derivation using at most q gates and at most u unary (NOT) steps. Its constructors copy the existing backwards-live conversion and preserve unary counts. `ex_lr` converts the actual posted circuit list directly into LR, with budget `ncount gates`. `ncount_one` proves the posted unique-NOT-indices hypothesis implies ncount≤1.

`imp_of_lr` uses a known unrestricted lower bound L−1 to ensure that the actual LR witness is minimum, then runs the existing search soundness tail for its actual unary count. It therefore needs only root checks for t≤u. At L=14,u=1, the already checked unrestricted lowerbound13 plus root14 checks t0 andt1 suffice; no checks at t2..13 are needed.

The extended module also defines the target graph f/EF and `bridge_lr`, validating the actual Circuit.eval semantics and all sample rows before invoking ex_lr. If the final file already contains evaluator/bit helpers or f/EF, omit duplicates. The stable284-line core `not-count-core.lean` is available separately for checkpoint review; the full helper file has406 lines.

Both modules compiled with Lean exit0, no admits. Full stdout/stderr files: `/tmp/oec/pequalnp-pilot-182/not-count-core-build.stdout`, `.stderr`, and `/tmp/oec/pequalnp-pilot-182/not-count-build.stdout`, `.stderr`. Full helper log has only inherited deprecation/unused-simp warnings. No final-file edits were made by this agent.
