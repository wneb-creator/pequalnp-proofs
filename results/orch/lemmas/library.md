# Library and descendant search: L-meta-2592

Status checked against public desk feed at 2026-11-25T14:04:37.954Z and repo db2dab29.

## Strongest directly relevant checked theorem

`lean/PEqualNP/Outside/L_meta_4725.lean` (3224 lines) proves `15 + PEqualNP.NotBracket.notCount C ≤ C.size` for any fan-in-two circuit computing the Petersen edge function. It uses the generic branching budget and a six-group lower bound on twin-class elimination. Its root theorem is at the end; `petersen_binary_lower` proves 15 non-NOT gates. All this must be ported inline because the assigned gap permits only `PEqualNP.Defs`, not Outside imports. The definitions-root files contain no theorem/lemma declarations detected by the top-level search.

## Existing reductions and remaining gaps

- `R_meta_2592_271`: binary lower bound plus exclusion for 1–4 NOT gates. Binary side is checked as `L_meta_4725`. Remaining `L-meta-4727` is open.
- `R_meta_2592_408`: normalize invalid reads, unused operands of NOT gates, and trim output; then finite normal-form lower bound. Normalization is checked as `L_meta_7389`; remaining `L-meta-7391` is open.
- `R_meta_2592_318`: cut at last NOT gate into arbitrary prefix and monotone suffix. Cut is checked as `L_meta_8295`; remaining separator `L-meta-8297` is open.
- `R_meta_4727_17`: compile to distinct Boolean straight-line functions, allowing complements of at most four marked functions. Compiler is checked as `L_meta_6060`; lower bound `L-meta-6062` remains open.
- `R_meta_4727_53`: compile to signed binary circuits with at most four marked negation wires. Compiler is checked as `L_meta_7227`; signed-circuit bound `L-meta-7229` remains open.
- `R_meta_4727_1` is marked dead and merely split presence/absence of a NOT gate; avoid it.

No existing solved-piece assembly closes the assigned gap. All five open descendant bounds have no open PRs in the fetched feed.

## Monotone sibling

`L-meta-2590` is still open. Its three live reductions remain substantial: first-gate AND/OR residual searches (`R_meta_2590_1`), first raw gate classified up to Petersen symmetries (`R_meta_2590_932`), and compressed input-0 formula with restricted rows (`R_meta_2590_491`). None provides a finished monotone 20-gate lower bound. `L_meta_614`/`L_meta_1483` give a generic `n + vertexCoverNumber - 1` bound, only 15 for Petersen, not the conjectured `edgeCount + vertexCoverNumber - 1 = 20`.

## Local data artifacts

- `/tmp/oec/pequalnp-pilot-109/library-desk-gaps.json`: complete public feed.
- `/tmp/oec/pequalnp-pilot-109/library-descendants.json`: five open descendants with exact statements.
- `/tmp/oec/pequalnp-pilot-109/library-petersen-files.txt`: narrowed relevant source list.

Source: https://data.pequalnp.com/data/desk/gaps.json (read 2026-11-25).

## One-NOT and targeted repair follow-up

At 14:10–14:17 UTC, investigated semantic elimination and algebraic repair of the search agent's near circuit.

Lean-checked new semantic partials (plain `lake env lean`, exit 0):

- `/tmp/oec/pequalnp-pilot-109/library/NotComparable.lean`: a monotone suffix computes the same target after replacing its NOT input by true when the inverted operand is below the target, or by false when above. A genuinely essential NOT therefore has an operand incomparable with the target.
- `/tmp/oec/pequalnp-pilot-109/library/GraphSeparator.lean`: for monotone operands, a positive graph input where the operand is false can be shrunk to one actual edge where it is false. Combined with incomparability, an essential sole NOT separates some independent input (operand true) from some edge input (operand false).

These are semantic facts, not a circuit gate-count bound. The seven-vertex elimination proofs inspected mostly combine a coarse binary-gate lower bound with an explicit monotone witness of matching size; they do not supply a general size-preserving one-NOT transformation for Petersen.

Targeted repair searches (computed Z3 UNSAT, not Lean certificates):

- Fixed eight preprocessing OR gates, three star AND gates, and two merging OR gates from the near circuit; synthesized six final gates with exactly one NOT. UNSAT in 39.7 seconds on 125 necessary input assignments.
- Allowed all 81 choices of which pair is formed first in the four triple ORs, preserving the same star outputs. Six final gates, exactly one NOT: UNSAT in 46.7 seconds.
- Scripts and full logs under `/tmp/oec/pequalnp-pilot-109/library/repair/`; `repair_flex_many.py` removes the at-most-one-NOT restriction for a stronger local search.
- A first version using pseudo-Boolean cardinality was stopped after switching to a pure bitvector/Boolean encoding; those cardinality constraints forced Z3 onto a much slower backend.

At 14:24 UTC, changed route to a global one-NOT prefix case: the NOT negates raw input x0 (all raw-input choices are equivalent under Petersen symmetry); eighteen subsequent gates are AND/OR. Source `library/repair/raw_not.py`, full log `raw-not19.log`. This is a witness search with normalization restrictions, not an exhaustive proof of the held statement.

A caution for structural arguments: semantic essentiality does not force NOT fanout at least two. The formula `(not x OR (x AND a)) AND (x OR (a AND c))` equals `a AND (x OR c)`; its NOT occurs only once, and either constant replacement changes the result. It costs six gates while the monotone expression costs two. Any useful no-fanout-one theorem must therefore use minimality, not semantic essentiality alone.

The primary site paper `https://pequalnp.com/papers/note-1`, read 2026-11-25 at 14:19 UTC, says its exact edge-count-plus-cover lower bounds apply to forests, or to graphs with cycles and hub separations at least seven. Petersen fails those hypotheses. Full locally parsed text: `library/note-1-text.txt`.

## Five-case normalization of an essential sole NOT

At 14:40 UTC, completed kernel-checked finite symmetry certificates. `OrbitCover.lean` proves all 120 explicit Petersen automorphisms valid, enumerates all 15 maximal independent sets, and proves every maximal-independent-set/edge pair lies in one of five orbits. Representatives (bit i means input xi) are `(50,3)`, `(50,6)`, `(50,12)`, `(116,3)`, `(116,6)`. The first component has operand h=true; the second has h=false. Maximal independent sets have two orbits: ten size-three sets and five size-four sets. Pair orbit sizes are 30,60,60,15,60.

`EssentialFiveCases.lean` (341 lines, SHA256 f01b5a474b1ab812bc41bbc886230c40bdb9a53b9fadfa25e5dbfee2ecdcf328) combines the generic maximal-independent extension and edge shrinking with this finite cover. Its theorem `essential_operand_five_cases` is proved using only kernel evaluation and ordinary Lean tactics. `lake env lean` exited 0 with an empty log. It is self-contained and repeats the earlier helper definitions; do not concatenate it verbatim with those same helpers.

To relabel an operand using the certificate permutation p, define h'(x)=h(x composed with p). Then h' is true on the canonical maximal independent set and false on its canonical edge. This applies when the sole NOT is essential under both constant substitutions and its operand is monotone. If a constant substitution preserves the target, the intended separate route is a monotone circuit with at most 18 gates after folding constants; that circuit-size bridge is not part of these semantic lemmas.

Remaining completed search results: the flexible six-gate repair with any positive NOT count was UNSAT in 95.9 seconds; freeing the three star products timed out at 180 seconds; the global raw-input-NOT case timed out at 180 seconds. These are computational exploration results, not certified lower bounds.

## Read-two formula angle

A monotone function represented by a DeMorgan formula with at most two occurrences of each variable admits a monotone formula with no more leaves: for opposite-signed occurrences of a variable, inspect their lowest common ancestor. If it is OR, replace the negative occurrence by true; if AND, replace it by false. The cofactor monotonicity inequality makes this valid through the enclosing monotone Boolean context. Negative-only variables are irrelevant because the represented function is both monotone and antitone in them. The finite-bound agent owns formal cofactor identities for this route.

The structural agent found a stronger finite projection route: two singly occurring variables in a read-two Petersen formula can be placed on an induced three-vertex path. Its outside cofactors include truth tables 200,234,254, but a signed three-variable skeleton with at most four leaves cannot realize all three by pruning. I am supplying the independent Petersen cofactor certificate, leaving the formula/skeleton theorem to the structural agent.
