# Independent audit: L-meta-2592

Read against `/tmp/oec/pequalnp-pilot-114/statement.txt`, the desk gap object, and the actual definitions on upstream base 1920101f. Agent: status_review. No desk calls, repository commits, or final proof edits.

## Mathematical statement

The conclusion forbids a circuit of at most 19 AND, OR, and NOT gates which computes the 10-variable Petersen edge function and contains at least one NOT gate. The graph has 15 distinct edges and every vertex has degree three.

Independent finite Python checks (all 1024 inputs) establish computationally:

- false inputs are exactly the independent sets;
- counts by weight are 1, 10, 30, 30, 5 for weights zero through four;
- therefore there are 76 false and 948 true inputs;
- all ten input variables are essential;
- independence number is four, minimum vertex-cover cardinality is six;
- there are fifteen maximal independent sets.

These are computational checks, not Lean-checked lemmas. They support the posted graph interpretation and provide compact SAT examples.

## Exact semantic pitfalls

`FanInTwo` explicitly limits operations to AND, OR, NOT, so MOD and majority cannot slip through. It imposes input-list length at most two. It does not enforce topological indices, output being the final gate, reachable gates, or distinct operands.

`Circuit.wires` appends one result for every gate in order. Every missing or future wire reads false at the time of the read. A future index never becomes a retroactive dependency. `Circuit.eval` reads the chosen final wire and defaults to false out of range. `Circuit.size` is exactly the number of list entries, so dead gates and all NOT gates count.

Nullary AND and nullary NOT are true; nullary OR is false. Unary AND and OR are copies. Repeated operands are allowed. A NOT gate negates only its first operand and ignores its second. These cases need coverage in a proof or normalization argument, but expose no immediate counterexample.

The NOT hypothesis is syntactic: a dead NOT is enough. Thus any monotone circuit with at most 18 gates would also refute this step by adding one dead NOT. Any search that requires every gate to be used must justify normalization and handle dropping the final remaining NOT. The existing normalization reduction handles this by retaining either a NOT or a strict size decrease.

No malformed-circuit exploit or direct logical contradiction was found. The hard part is a genuine small circuit lower bound, not ordinary monotonicity of the target function: monotone output functions can have nonmonotone intermediates.

## Existing reductions and PR evidence

Git history confirms three merged reductions for this exact step, matching `reductions_live: 3` in the desk answer:

- `R_meta_2592_271.lean`, merged PR https://github.com/brilliant-hq/pequalnp-proofs/pull/7606, commit 1893529425b2f6e486cbea2caff3df6eb364d270. Splits into the lower bound `15 + notCount C <= C.size` and rejection with one through four NOT gates.
- `R_meta_2592_408.lean`, merged PR https://github.com/brilliant-hq/pequalnp-proofs/pull/9069, commit 5cd9136ca93377772c56c3578bb189bbc56dd3ea. Splits normalization from a normalized lower bound.
- `R_meta_2592_318.lean`, merged PR https://github.com/brilliant-hq/pequalnp-proofs/pull/11694, commit 7bbc0b9494f33cb362c5810f97b19b695468ecf7. Cuts at the last NOT into arbitrary prefix and monotone suffix; remaining separator is essentially the hard lower bound.

Parent split `R_meta_651_7.lean` was merged in PR https://github.com/brilliant-hq/pequalnp-proofs/pull/4041 and is exactly monotone case plus at-least-one-NOT case. Other parent reductions split by first-gate automorphism orbit or final-gate shape. None supplies an unconditional lower bound.

The complete initial open-PR census contained 820 entries and no exact 2592, 2590, or 651 reference in title/body. Structured `gh pr list --state all --search` returned empty arrays for all three numeric IDs even though merged reductions are present, so those search results should not be treated as conclusive history. Raw responses are preserved under `/tmp/oec/pequalnp-pilot-114/audit-*-prs.json`.

## Review requirements for final file

Require exact posted conclusion and allowed project import `PEqualNP.Defs`; no imported outside proof or helper modules. Check all reachable proof axioms, no trust-extending tactics, all arithmetic and finite computation kernel checked. Cover constants, missing reads, duplicate operands, ignored NOT operands, dead gates, and arbitrary output index if proving the universal theorem. A finite SAT or enumeration certificate needs a proved bridge from these original Circuit semantics, not only normalized well-formed circuits.

## Preserved strategy and stopping audit 2026-11-25T14:23:33.813859+00:00

Root allocation retry returned the same preexisting lease. Its issued_at predates this job, and the desk reports five held gaps at the handle cap. Work stopped under the owner rule; do not release that lease. No further desk requests or research by this reviewer.

LastNot.lean independently reviewed PASS after its reported successful compilation. It chooses the last syntactic NOT, keeps its first operand as prefix output (or one-past-prefix for empty input), preserves original wire indices by feeding the suffix all prefix wires plus the NOT result, and proves exact size decomposition. This is an existing-upstream result equivalent to L-meta-8295, retained as a clearly labeled partial.

LowerBound16.lean independently reviewed PASS as an adaptation of L_meta_5236. The full original certificate prefix is unchanged except namespace. New realizePlain executes the original circuit on ten pins, then enlarges only the live-signal membership set into the eleven-signal initial set. This avoids any input-index shift and supports 16 + notCount <= size. Successful compilation remains required before claiming checked.

Unproved next strategy, preserved without further work: the existing nine-input signed binary floor15 may yield floor17 for the Petersen function by cutting the first binary step. For each signed binary gate on distinct input variables, both operands must remain live: fixing the other input to a canalizing bit leaves Petersen dependent on the selected operand, while that first gate becomes constant. A graph automorphism sends the selected operand to input0. Restricting input0 to false makes the first gate either a constant or the other input, both already available in the nine-input roots, and the retained original operand contributes one constant to projection mass. This would give at least16 binary steps after the first, hence17 in total.

For AND and the two signed AND forms, choose the zero restriction that annihilates the new first-gate signal. Both this new signal and the retained operand become constants, yielding mass at least2 and a potential floor18. For ordinary OR, the new signal aliases the other retained operand after restriction. The existing mass function counts only constants, not duplicate projected signals, so a second OR charge requires an additional proved duplicate-loss lemma. Do not infer that charge from the existing mass theorem. not_elimination/lower_bound agents hold the cofactor and projection implementation plans.
