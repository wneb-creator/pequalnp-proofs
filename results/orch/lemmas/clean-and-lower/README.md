# L-meta-1904 research: local normalization

These files are checked research components. None proves or refutes the full posted statement.

- `UnsafeBypass.lean` (SHA256 `22ae9381d4bc3381c8b171ad567ae45a2fbba33f8cfd0a389eaa3358f06cecef`) checks a counterexample to replacing a first unsafe AND by either operand. Its graph is the four-vertex path with edges 02,03,12. The five-gate circuit computes `(a OR c) AND (a OR b) AND (c OR d)`. Its first AND is true on singleton a. Bypassing either operand is wrong, but a different four-gate safe circuit computes the same function. Canonical Defs import, Lean exit 0; complete diagnostics in `validation.txt`.
- `DiamondRewrite.lean` (SHA256 `1e8956cf8603f13c24bee0af984e4726bb6b361c28bbfd0d6c2779e9e9e8c7d2`) proves a general circuit surgery. Replace consecutive OR(a,b), OR(a,c), AND(the two ORs) by OR(a,b), AND(b,c), OR(a,new AND). Gate count and output function are preserved. All three input indices must precede the block. The suffix and output must not read the changed middle wire. The first OR may have arbitrary later readers. Canonical Defs import, Lean exit 0; complete diagnostics in `diamond-validation.txt`.
- The independent replacement agent extended this surgery in `../clean-and-proof/DiamondRank.lean`: for primary inputs with b different from c, the sum of active AND gates over singleton inputs drops exactly by one. This combines with its ranked-minimum theorem. See that directory for the checked corollary and logs.

## Remaining global obstruction

A first unsafe AND need not have two immediately preceding OR inputs sharing one literal. Its inputs can contain larger, shared OR networks and earlier safe AND outputs. Even after exposing the local diamond, both OR outputs might be read later, violating the surgery's essential no-read hypothesis. No proof was found that triangle/square-freeness permits reorganizing all these uses without increasing size. The checked bypass example rules out the simplest per-reader replacement.

The first-unsafe-AND witness on at most two vertices is already proved in accepted reduction R_meta_1904_493; it was reused conceptually and not duplicated. The singleton-normalization and pair-normalization children remain open. The three reduction slots were occupied during this lease.

## Positive safe-gate exchange plan (not implemented)

A potentially useful additional normal form concerns a wire u satisfying u => F, where F is the final function. Setting that wire to false in the suffix gives the semantic identity F = u OR F[u:=false]. Constant propagation removes each later effective reader of u; retaining the prefix computing u and adding one output OR should give a circuit D with the same function and

    D.size + effectiveReaders(C,u) <= C.size + 1.

Only readers after u exists count. For NOT gates, only their first input is effective. For a monotone input circuit, the simplifier and output OR should preserve monotonicity. The existing repository `Helpers/Elim.lean` supplies the required constant-propagation machinery; `Helpers/ExchangeElim.lean` proves the negative counterpart, with a two-gate NOT-plus-OR overhead. A canonical-Defs standalone proof would need those helpers copied with attribution and the terminal cases adapted to the positive counterpart. No such implementation or proof has been claimed here.

The bound would imply that a safe wire in a minimum monotone circuit has at most one effective reader. A tie-breaking argument could then move already-safe AND outputs toward the final OR branches. This still would not solve the shared dirty-AND normalization problem.

## Research source

Read 2026-11-25: https://pequalnp.com/papers/note-1, section 7. The site's account distinguishes single-level graph-function bounds from bounds for unrestricted monotone circuits and describes explicit superlinear bounds as open in the cited historical literature. Underlying Jukna sources are UNVERIFIED here: only the allowed site's account was read. This is context, not evidence that L-meta-1904 is false.
