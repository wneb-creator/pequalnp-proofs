# One suffix junk gate: PASS for this target

The separate postprocessor `add_suffix_some_junk.py` adds exactly

    junk[17] OR junk[18] OR junk[19] OR junk[20]

to each of the seven reverse-counter tail formulas. It creates no variables.
It does not restore the gate-17 unit or the disjunction over gates 18 through
20 used by the old two-junk restriction. All four assignments with exactly
one junk flag are permitted by the new clause. Existing `enforce_junk=False`
and `second_junk=False` metadata remain unchanged; `suffix_some_junk=True`
records this separate condition. The historical `first_junk=17` field remains
the clean-prefix boundary, not an assertion that gate 17 must now be junk.

## Mathematical consequence

The fixed target graph has 16 edges, no four-cycle, and minimum vertex cover
7. The audit enumerates all 7,920 ordered quadruples of distinct vertices and
all 2,048 vertex subsets, records a seven-vertex cover, and finds no smaller
one. Therefore the established clean-circuit bound is
`16 + 7 - 1 = 22` gates. In the actual-circuit theorem, singleton rejection
and edge acceptance yield a cover T with `16 + |T| <= gates + 1`; a circuit
of at most 21 gates would force `23 <= 22`.

Suppose a modeled 21-gate circuit satisfying the exact edge target had no
junk AND. Prefix ANDs are already clean. The suffix junk flags are exact
equivalences between being an AND and being true on some maximal independent
input. Monotonicity and extension of every independent set to a maximal one
make this equivalent to being unclean on some negative input. Thus every
AND in the entire circuit would be clean.

Eliminate the virtual constants by AND/OR identities and propagate aliases.
The target is nonconstant, so a constant-free actual Circuit with no more
gates remains. Every surviving gate computes its original function; hence
every surviving AND is still clean. Dead gates may be discarded. The clean
lower bound now contradicts the at-most-21 size. This uses the already
reviewed constant-elimination argument; no new Lean formalization of that
argument is claimed here.

Consequently some suffix AND must be junk in every valid modeled witness.
The argument applies after the seven-tail rewrite directly to its resulting
circuit; it does not assume that any particular old junk gate survives or
that two junk gates survive. It also applies with repetitions, dead gates,
all prior prefix restrictions, and the reverse totalizer: the new clause is
a consequence of the common target/clean-prefix/size semantics.

## Exact code and file audit

Fresh output is `tail7-ancestorreverse-onejunk/`. Each formula retains every
parent clause byte-for-byte after its adjusted header and appends exactly
the four-positive-literal clause. The postprocessor requires a fresh output
directory, checks all seven parent hashes/counts/literal bounds before any
write, and records its own SHA256 and each direct parent CNF SHA256.

`suffix-some-junk-review.json` binds all seven resulting formulas and reports
the finite graph checks, eight junk-equivalence Boolean controls and sixteen
new-clause controls. All inherited metadata except CNF count/hash is retained.
The old gate-17 unit and old three-literal two-junk clause are checked absent.
The existing validator's full-CNF audit checks this new clause even though its
older semantic-check interface does not yet have a dedicated check for this
metadata flag.

No solver was started and no running CNF was changed. Main independent code
and mathematics review remains the next step before use. No runtime benefit,
SAT/UNSAT verdict, or global refutation is claimed.
