# Few-NOT investigation

Task: L-meta-2592, Petersen edge function, at most nineteen gates with at least one NOT.

## 2026-11-25 initial findings

- Existing `MetaComplexity/Helpers/OneNot{Split,Piece,Eval,Relabel}.lean` supplies splitting at the unique NOT and constant replacement on regions where its input is fixed. It does not supply size-preserving elimination of a NOT from an arbitrary monotone function.
- Recent graph-specific elimination results such as `Outside/L_meta_11151.lean` and `Outside/L_meta_10798.lean` ignore the at-most-one-NOT hypothesis: they prove an unrestricted lower bound, then return a fixed matching monotone witness. They cannot directly solve Petersen without its lower bound.
- A general one-NOT elimination theorem would be too strong a route. Families of monotone outputs can benefit from one NOT, and adding selector inputs converts such a family into one monotone output. The supplied L-meta-1035 counterexample claim is not independently reconstructed here.

## Essential one-NOT separator

Cut a one-NOT circuit at that gate. Its output has the form `f(x) = G(x, not h(x))`, where `G` and `h` are monotone. Put `lo(x)=G(x,false)` and `hi(x)=G(x,true)`. Then `lo <= f <= hi`.

For the Petersen edge function:

1. If `h` is true on every edge assignment, `lo` accepts every minterm, so monotonicity gives `lo=f`. Replacing the NOT by false is valid.
2. If `h` is false on every maximal independent assignment, `hi` rejects every maximal negative point, so monotonicity gives `hi=f`. Replacing the NOT by true is valid.
3. Therefore an essential NOT has `h(E)=false` for some edge assignment E and `h(I)=true` for some maximal independent assignment I.

The graph has fifteen edge assignments, ten maximal independent triples, and five maximal independent quadruples. Their bit masks are:

`50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773`.

All thirty boundary assignments are mutually incomparable between the positive and negative families; thus monotonicity alone does not constrain the separator's thirty truth values.

Enumerating the 120 adjacency-preserving vertex permutations gives five orbits of ordered pairs `(E,I)`. Normalize E to `{0,1}`. Representative I, stabilizer orbit size, full pair orbit size:

| I | edge-stabilizer orbit | full orbit |
|---|---:|---:|
| `{1,4,5}` | 2 | 30 |
| `{3,5,6}` | 4 | 60 |
| `{2,4,5,6}` | 1 | 15 |
| `{1,3,7}` | 4 | 60 |
| `{0,3,6,7}` | 4 | 60 |

The counterexample agent is using these constraints for exact one-NOT synthesis. This classification was computed in Python, not checked in Lean yet.

`lemmas/FewNots.lean` contains a draft compact function-level proof of the essential-separator witness theorem and a kernel-checked boundary certificate. It compiled successfully with pinned Lean 4.36.0, exit 0 and empty stdout/stderr. The boundary certificate uses Boolean list predicates and exhaustive ten-Bool enumeration in the kernel. It is a partial result, not a proof of L-meta-2592.

## Research checked on 2026-11-25

Read the search result excerpt for https://pequalnp.com/papers/note-1: it documents the monotone upper bound `|E|+|T|-1`. Opening the full page through the browser failed. No stronger lower-bound figure from that page was used.

No general one-NOT graph elimination theorem was found in the allowed primary sources.

## 2026-11-25T14:15:55.578807+00:00

`FewNots.lean` compiled successfully. `FirstGate.lean` combines the signed-circuit normalization prefix and the finite pair-separation certificate with a new proof that a first-gate input has a second reader, then uses `elim_ge_2_two` to delete at least two binary gates under a false restriction. Its initial compilation is running.

## 2026-11-25T14:21:59.042701+00:00 checked first-gate components

- `lemmas/FirstGate.lean`: checked original signed-model bundle.
- `lemmas/FirstGatePlain.lean`: checked product-only signed-model bundle, no new structures or local instances.
- `lemmas/FirstGateCases.lean`: checked product-only bundle plus strongest first-source phase condition below.

All three passed pinned Lean with exit 0 and empty stdout/stderr. The complete artifacts are frozen for root preservation.

`FirstGate.zero_restriction_saves_two` proves every minimal signed binary circuit for Petersen has a variable whose false restriction deletes at least two binary gates. It uses `PairSeparation.cofactorKeepsOtherInput` to exclude a first-gate source with no second reader.

`FirstGateCases.first_sources_negative_everywhere` takes the explicit hypothesis `ZeroFloor`: every variable-false Petersen cofactor requires at least fifteen signed binary gates. Under this hypothesis, a minimal Petersen signed circuit of at most seventeen gates has its first gate reading both variables with negative phase, and every later reader of either variable also has negative phase. Opposite phases delete at least three binary gates at false; repeated positive phase deletes at least four. Both contradict the cofactor floor under a seventeen-gate budget. This is a conditional component, not the full posted theorem.

- FewNots.lean SHA256 e16b752e23303f60a81220e87760b5175cfc6baca279b6e1ce2604a7545d116d
- FirstGate.lean SHA256 37f0c9f21197191856c59671ff1c32018797ab52d9cf808615434128736dbd89
- FirstGatePlain.lean SHA256 3f92659d0d405ec744207e49e6e268dea588e1ab90c080c107b4337b97302f82
- FirstGateCases.lean SHA256 f2cce06b05949cf5556694bdebd1e6ffc4942b279034a90b9d3c500658ba1b89

## 2026-11-25T14:27:45.562532+00:00 checked reader budgets

`ReadBudget.lean` compiled with exit 0 and empty stdout/stderr. `reader_bound` proves, under the same explicit ZeroFloor15 hypothesis, that the number of distinct binary gates reading any primary input plus fifteen is at most the total binary gate count. Thus at cap17 every primary input has at most two readers; at cap18 at most three. This is an upper bound only; lower bound two is proved only for the first-gate inputs. At cap18, a positive-phase first-gate input must be read with negative phase at all its later readers. These statements are for minimum unrestricted signed circuits; transferring them together with an actual one-NOT budget would require a separate budget-preserving minimization argument.

ReadBudget.lean SHA256 43b2a4982158384b3a514645634d6eebd86a11249dce5685182541fa9ea05c25

## 2026-11-25T14:33:43.573614+00:00 final checked components

`Duplicate.lean`, `ReadBudgetGeneral.lean`, and `Promotion.lean` all compiled successfully with empty stdout/stderr. The duplicate lemma rules out a later gate reading both first-gate sources, hence their future readers are distinct. General reader bounds require only well-formedness and computing the target. Promotion derives the universal signed binary floor17 from ZeroFloor15, then shows every computing circuit of at most17 binary gates is minimum. This makes phase pruning independent of a prefix representative history.

All full artifacts are frozen. Commands/results and SHA256 hashes are recorded in `few_nots_validation.txt`.


NOT-budget compiler checkpoint (2026-11-25 14:43 UTC):

- `NotBudgetCore.lean` and `NotBudgetStep.lean` compile with exit 0. The latter is the frozen complete checkpoint; `NotBudget.lean` has identical bytes.
- Namespace `PEqualNP.Outside.L_meta_2592_aux.NotBudget`. `RefGood phase marks r` requires valid source index and phase agreement for an unmarked source. `GatesGood` requires primary storage phases false, source bounds, and unmarked-edge parity equal to source phase XOR consumer gate phase.
- `append_gate p` appends storage phase p: physical AND corresponds to false, physical OR to true. `refGood_flip_mark` implements an original NOT by adding its source to the marked set.
- `step_budget` is checked for every original gate, including unsupported operations and arities which the existing compiler maps to constants. It constructs new phase/marks lists with `marks'.card ≤ marks.card + notCount ⟨[g],0⟩`.
- Remaining task is a straightforward induction over `toU2Fold`, initial-state annotation, and final output reference extraction. These were not started before the root requested a pause for the desk lease error.
- Full successful logs are `/tmp/oec/pequalnp-pilot-104/notbudget-step2.stdout` and `.stderr` (both empty).
