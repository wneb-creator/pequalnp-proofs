Read-only inventory by /root/status_review, 2026-11-25 06:12 UTC. No desk calls, git mutations, Lean builds, or proof-source edits.

The assigned gap is L-meta-6349: mask 5805 on Fin 4 × Fin 4 has representation size at most 10 and not at most 9. The only allowed project import is `PEqualNP.Defs`. The assignment reports zero open PRs, and a completely paginated GitHub search for the exact gap name returns zero results. A separate mask5805 search finds only the unrelated PR number5805. The Table 1a search returns thirteen PRs, only one currently open (PR12645 for L-meta-6300); this is a keyword census, not a claim to enumerate every possible related proof. Full structured findings are in `public-status-inventory.json`.

The advertised bridge exists at `lean/PEqualNP/Library/LRAT/Promise.lean:38`. `Promise.rep_lower44 A s g hg hU` converts unsatisfiability of `enc2 8 s g rows44` into `¬ RepSizeAtMost A s`, provided `g (row44 u v) = A u v`. `PromiseGen.lean:79` offers `rep_lower_mask`, with canonical row and mask functions. The latest public-main change to Promise is commit `9c4fa2bd4f85e59f6cebbe16ca9a4ba71df2b472`, already present locally.

The allowed definitions are present: `Defs.lean` includes `Defs.Represents` and `Defs.LratEncoding`. However, no file in the definitions family imports a `PEqualNP.Library` module, so neither Promise theorem is available from the allowed import closure. Importing Promise would violate this gap's import list. Reusing it requires inlining the necessary dependency proofs under the owned namespace. Promise depends on Link2, Link, Checker, and helpers from Shannon; the four LRAT sources total106868 bytes before pruning. Link defines Model/Valid/NF and a Decidable instance; Checker defines Trie. Those declarations need ordinary-library-type conversion or would trigger manual review under CONTRIBUTING's plain-file rule5. Library comments and namespaces also need adjustment when copied into a submitted file. No compilation claim is made for an inline conversion.

Existing allowed-import examples in the local base:

| Source | Exact mask/cost | Lower-bound method |
| --- | --- | --- |
| `L_meta_5464.lean` | 18 / 3 | Generic sixteen-bit forward reachability, budget2 |
| `L_meta_5465.lean` | 19 / 4 | Generic finite table simulation and reachability, budget3 |
| `L_meta_5468.lean` | 1919 / 5 | Backward live-wire normalization and separation cuts, budget4 |
| `L_meta_5471.lean` | 22 / 4 | Finite reachability split into first-step cases, budget3 |

Newer merged examples fetched read-only from public main, saved as `/tmp/oec/pequalnp-pilot-61/table1a-main-<id>.lean`:

| Source | Exact mask/cost | Size | Method and relevance |
| --- | --- | ---: | --- |
| L-meta-5535, PR11495 | 375 / 6 | 48428B | Inline normalized finite search; the full lower bound is `q_lower`. |
| L-meta-5552, PR11469 | 4398 / 8 | 30849B | Circuit expansion at a tight input-count bound yields a read-once formula, then a rectangle contradiction. It excludes seven gates; extending to a nine-gate budget requires additional reasoning. |
| L-meta-5909, PR11749 | 15871 / 7 | 11159B | Generic `reads_le` proves forced-left plus forced-right input counts ≤ gates+1. For mask5805 all eight inputs are forced, yielding only the preliminary lower bound seven. |

All seven examples use only allowed Mathlib imports plus `PEqualNP.Defs`; none uses Promise. The three newer files were not found in the local base during this inventory. The root agent alone controls fetching/updating that base.
