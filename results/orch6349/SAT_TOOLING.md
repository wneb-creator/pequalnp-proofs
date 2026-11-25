# L-meta-6349 SAT tooling inventory

Read on 2026-11-25, without launching a new Lean process.

- Bundled solver: `/tmp/oec/pequalnp-pilot-61/lean-4.36.0-linux/bin/cadical`. Its checked help supports `--lrat=true` and `--binary=false`; full help is in scratch `cadical-help.txt`. No SAT executable is on the default PATH, and Python z3/pysat/pycosat/ortools modules are absent.
- Exact bridge: `PEqualNP.Library.LRAT.Promise.rep_lower44` in `lean/PEqualNP/Library/LRAT/Promise.lean:38`. It needs unsatisfiability of `enc2 8 9 g rows44` and agreement of `g` on the16 oneEach rows. `rep_lower_mask 4 4 5805 9` in `PromiseGen.lean:79` packages the mask agreement.
- The assignment permits only the project import `PEqualNP.Defs`; that imports the encoding definitions in `Defs.LratEncoding`, but no LRAT checker or soundness bridge. CONTRIBUTING20–21 restricts project imports to the assignment list.
- A direct library inline comprises Checker26553B, Link50997B, Link226169B, plus Promise. It requires additional work: Checker uses an inductiveTrie; Link uses Model/Valid/NF structures, a Decidable instance, and a Shannon helper dependency. Those constructs cannot simply be pasted into the final proof under the current plain-proof guard.
- Existing numerical certificate example: `Outside/L_meta_2229.lean`, using packed `runs`, `spread`, `checkW`, `decide +kernel`, and `checkW_sound`. It imports Library modules directly and is not a self-contained bridge for this assignment.
- Normalization agent owns exact CNF generation and solver execution. This inventory performs no duplicate solve or certificate build.
