# Semantic audit, 2026-11-23

The posted FP3 theorem remains unproved. These scratch results prove semantic reductions and do not assert a short first witness or a fast verifier.

`PrimitiveBridge.lean` compiles with Lean 4.36.0 and the pinned project dependencies. The final full diagnostic log is `primitive-bridge-13.log` (empty; exit 0). It concatenates the independently checked local-stack helpers, GlobalTrace, AlphabetBound, Normalization, and five new bridge bodies. Repository files are unchanged by this work.

The final `binaryGame_computes` theorem takes an actual `TM2ComputableInTime` computing `f : List Bool → Bool` and any clock `t ≥ c.time |x|`. It proves equivalence between `f x = true` and the explicit bounded-query game at primitive horizon `T = 2 * Normalization.bound(c.tm) * t`.

Checked semantic points:

- The original machine has arbitrary dependent stack alphabets. The shared finite alphabet contains every symbol reachable in the normalized machine plus both designated Boolean output symbols. Finiteness follows from finite input alphabet, finite internal states, and finitely many push sites.
- The compiler has finite control, including temporary peek-restoration states. A normalized step uses at most two primitive steps. Empty pop/peek is handled explicitly; nonempty peek pops and then restores the exact same encoded symbol.
- The partial tagged-symbol decoder is used only on supported encoded stacks. Its irrelevant wrong-tag branch cannot affect a reachable compiled run. Support is propagated at every normalized transition.
- Original bounded runs transfer to exact primitive time by padding only after the halted state is reached. A label `none` configuration and the outer `Option.none` transition result are treated separately.
- Input and output alphabets retain their original equivalences. Output-symbol coding is injective. The final state includes the original reset internal state; the output stack is exactly the one-element output and every other stack is empty.
- Local stack checking handles input-loading prefixes, exact symbol matching, positive-height pops, and a virtual terminal output pop. The mate-free challenge recovers any matching pointer only inside the proof.
- The game quantifies fixed control, operation, and height functions before all queries. The universal query consists of a stack and two bounded indices; the final witness is a bounded dip index. All heights can be encoded in `Fin (|x| + T + 2)`. This bounds the fields, not the description of the entire first-witness functions.

Independent review: fp3_strategy reviewed all GlobalTrace body files and the first four PrimitiveBridge bodies; root reviewed Normalization/AlphabetBound/MacroBudget independently through this agent and reviewed the new bridge's finite coding, support, run composition, and terminal interface. No semantic flaw was found. The actual theorem proof is kernel checked; no `sorry`, new axiom, or `native_decide` was introduced.

`PrimitiveBridgeAxiomAudit.lean` also compiled with exit 0. Its complete log, `primitive-bridge-axioms.log`, reports only `propext`, `Classical.choice`, and `Quot.sound` for `binaryGame_computes` and `terminal_three_block_bounded_heights_iff`.

Remaining obligations for the posted theorem:

1. An unconditional uniform power saving for committing the operation stream or another sound global representation. A short source input, finite alphabets, and the existence of the local game do not establish it. Generic Shannon compression supplies only logarithmic savings at this address size.
2. Actual finite encodings and a single deterministic TM2 verifier whose runtime is linear in the entire supplied pair on all inputs, including malformed and undersized encodings. Finite noncomputable tables are valid machine-dependent constants, but the current semantic game is not already that verifier.
3. Resource accounting for every replay, circuit evaluation certificate, sorting/arithmetic operation, checkpoint table, and padding; then an integer exponent choice before machine-dependent constants. Existing exponent-budget helpers apply only after those bounds and the saving in item 1 are established.
4. Assembly into exactly the posted target, followed by its build and repository checker. No target build, checker pass, or proof PR is claimed here.

Checkpoint replay can remove a separate circuit assumption for control/height fields: fixed samples bind their local replay from a fixed operation stream. It does not by itself supply the missing short operation stream. Shared-controller or nondeterministic replay strategies must be checked for global consistency before being counted as progress on item 1.
