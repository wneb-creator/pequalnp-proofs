# Official SAT encoding and kernel LRAT route

Recorded 2026-11-25 12:56 UTC for L-meta-9811. These are infrastructure results,
not a proof of the posted 24-gate exclusion. No completed UNSAT certificate for
that exclusion had been obtained when this note was written.

## What has been checked

1. `official_enc2.py` is a direct translation of the formula definitions in
   `lean/PEqualNP/Library/LRAT/LinkN.lean` and `LinkN2.lean`.
2. `OfficialEncodingCheck.lean` independently evaluates those verbatim Lean
   formula definitions. Its entire 45,245,056-byte output agrees byte for byte
   with the Python output. Both SHA-256 digests are
   `b877eccd57565a513b25c347eca5193429883cc32be15b30ebc0230dd2c084b0`.
3. The formula uses 571 rows: all 552 false assignments and the 19 minimal
   positive assignments. There are only 39 maximal false assignments; the
   larger number here means all false assignments.
4. The formula has 1,466,230 clauses, 42,543 used variables, and maximum
   DIMACS variable 3,251,953. The variable numbering is intentionally the
   original sparse numbering, preserving exact correspondence with Lean.
5. `KernelLRATSmoke.lean` copies the repository kernel checker and proves
   a tiny contradiction with `check_sound` and `decide +kernel`. A deliberately
   incorrect unit hint is rejected. It compiles, and the axiom report contains
   only `propext`, `Classical.choice`, and `Quot.sound`.
6. `decode_official.py` verifies every CNF clause before decoding a model, then
   evaluates the circuit on all 16,384 inputs. Its small smoke case includes a
   TRUE padding gate and three NOT gates. All 1,052 clauses and all four inputs
   of that two-input case pass.

The copied Lean smoke files contain commands and comments suitable for scratch
validation. They are not in the required plain-file submission format.

## Reproduce the exact target CNF

From this directory, using Python 3:

```
python3 official_enc2.py --edges edges.json --negative-rows all-negative.json --out regenerated
```

This creates `regenerated/official.cnf`, `rows.json`, and `metadata.json`.
`official24/metadata.json` and `official24/rows.json` record the checked output.
The 45 MB CNF is not committed because the compact generator and full inputs
reproduce it exactly.

For the independent Lean output, run from the repository's `lean/` directory
under its pinned Lean 4.36.0 environment:

```
lake env lean --run ../results/orch/official_sat/OfficialEncodingCheck.lean > /tmp/oec/pequalnp-pilot-85/official-lean.cnf 2> /tmp/oec/pequalnp-pilot-85/official-lean.stderr
```

The original invocation exited 0 and wrote an empty stderr. Compare the entire
output hash to the digest above. The hard-coded DIMACS header is checked by
the exact Python/Lean byte agreement; both generators produce the same bodies.

## Existing kernel theorem and circuit bridge

`PEqualNP.Library.LRAT.Checker` contains:

```
check_sound F fk toks (h : check F fk toks = true) : ¬ FormulaSat F
checkW_sound F fk W words (h : checkW F fk W words = true) : ¬ FormulaSat F
```

The proof-token format uses natural-number literals: positive DIMACS variable
`d` is `2*d`, and negative `d` is `2*d+1`. A step carries its new clause key,
the clause literals followed by zero, then RUP hint keys interspersed with
explicit unit literals. It ends at the first falsified hint. A converter must
replay standard LRAT unit propagation to supply those unit literals. The
checker verifies them, so the converter need not be trusted.

Packed words encode many tokens as fixed-width fields with a sentinel top bit.
`checkFirst_sound`, `checkSeg_sound`, and `checkLast_sound` support segments
connected by explicit lists of live clauses. This bounds kernel cache memory
per theorem. The implementation handles RUP derivations, not arbitrary RAT
steps. A certificate with negative RAT hints needs conversion or another route.

`PEqualNP.Library.LRAT.LinkN.size_of_unsat2` at line 591 proves:

```
(∀ r ∈ rows, r < 2^n) →
¬ FormulaSat (enc2 n s (rowFun n f) rows) →
∀ t, HasCircuitSize n f t → s+1 ≤ t
```

It covers AND, OR, and NOT circuits, permits padding, and includes a proof of
its gate normalization and lexicographic ordering. In particular, an UNSAT
certificate for the exact official `n=14,s=24` formula would provide the
needed lower bound once checked. It is unnecessary to test all positive rows:
UNSAT on any subset of correctly labeled rows suffices. SAT on the subset is
only a candidate and still needs exhaustive validation.

The official operation codes are 0=AND, 1=OR, 2=TRUE, 3=NOT. A NOT gate has
equal sources. TRUE is padding or a genuine one-gate constant operation and
can be represented by NOT of the default false wire in the search format.
The encoding deliberately omits at-most-one selector clauses. The proved
direction from circuits to satisfying assignments is enough for UNSAT bounds.
The decoder validates any chosen selections against the sampled rows.

## Why stock `bv_decide` is not usable here

Lean 4.36.0's
`Lean/Meta/Tactic/BVDecide/Prover/Bitblast.lean:39` invokes `nativeEqTrue` when
turning the LRAT certificate into a reflection proof. This creates a generated
native-evaluation axiom. `lean/CheckLemma.lean:51` allows only `propext`,
`Classical.choice`, and `Quot.sound`, and traverses transitive axioms.
Consequently stock `bv_decide` does not satisfy the checker, even though its
source text is not separately named in the plain-file ban. The repository
kernel LRAT path above does satisfy the axiom requirement on the tested case.

Std also has `Std.Tactic.BVDecide.LRAT.check_sound`; one could evaluate its
checker in the kernel, but its array-based implementation is not optimized
for this task. Mathlib's `Mathlib.Tactic.Sat.FromLRAT` reconstructs kernel
proof terms for RUP-only LRAT, but its convenient interfaces use strings and
custom commands, which conflict with the submission's plain-file format.

## Realistic remaining work

- Obtain a complete UNSAT certificate. A timed-out trace is incomplete and
  proves nothing about the entire formula.
- Translate and trim the certificate, preserving clause IDs or proving the
  formula relation. The present checker stores clauses as large integer
  bitmasks. Sparse literal IDs near 6.5 million can make a single mask about
  0.8 MB, so a full direct check may be impractical. Dense renaming needs a
  proved satisfiability-preserving bridge, or a much smaller used core.
- Connect the actual checked formula to `enc2`. Byte equality outside Lean
  validates the generator but is not itself this theorem. Evaluating `enc2`
  inside the kernel or proving a compact generated/core relation remains.
- Fit the bridge and certificate into the required single-file format. The
  checker, LinkN, LinkN2, and Shannon source total 114,408 bytes before
  adaptation, leaving about 400 KiB under a 512 KiB cap for the final statement,
  certificates, and other necessary helpers. Their existing custom structures,
  instances, and local macros also need format review/adaptation if imports
  are restricted to Mathlib and PEqualNP.Defs.

The reusable checker eliminates the need to invent soundness machinery, but
does not make a million-clause certificate check immediate. Small trimmed RUP
certificates are a realistic short task; a large full 24-gate certificate may
require substantial memory and representation work. No unmeasured runtime
estimate is asserted here.
