# S01: consecutive first junk gates

Updated 2026-11-24 03:29 UTC. Mathematical result; not yet a Lean theorem or an
independently reviewed SAT restriction. No solver or generator has been changed.

## Main result

Under the already reviewed all-live/output-last normalization for this shard,
**gate 18 can also be required to be a junk AND**. Thus the original `AOAA`
operation case can be eliminated by normalization to `AAOA` or `AAAA`.
The remaining operation strings are `AAAA`, `AAOA`, and `AAAO`, with both
gates 17 and 18 junk. This is an existence-preserving normalization, not a
logical implication satisfied by every unmodified circuit.

The only graph-specific ingredient in the proof below is the existing formal
clean-circuit lower bound 22. No global one-junk lower bound is assumed. Repeated
operands, aliases, free constants and semantically redundant gates are allowed.
Free constants are propagated away when applying the clean-circuit lower bound.

## Definitions and premises

F is the target graph function. A signal is clean if it is false on every
independent input, and dirty otherwise. A junk gate is a dirty AND. All 17
prefix gates have clean ANDs. There are four live suffix gates 17..20, output20
computes F, gate17 is junk, and there is another junk AND. The established
three-AND argument leaves exactly AAAA, AAOA, AOAA and AAAO.

Any prefix signals R,T whose product is clean and covers every target edge
would give F with one additional clean AND, using at most18 clean gates.
Consequently such a pair cannot occur. This observation applies to functions
computed by prefix wires, not just raw input variables.

## The three easy operation cases

- AAOA: gate19 is OR and gate20 is clean, so the second junk must be gate18.
- AAAO: gate19 feeds the clean final OR, so gate19 is clean. Again gate18 is
  the second junk AND.
- AAAA: if gate18 is already junk, nothing is needed. Otherwise gate19 is
  junk, and it cannot read the clean AND gate18: an AND with a clean operand
  is clean. Swap gates18 and19 and update references. Both were available in
  this order; gate17 stays unchanged and the new gate18 is junk.

The last argument uses only cleanliness and a topological swap, not a
minimal-factor or minimal-circuit assumption.

## Direct normalization of AOAA

Write D = g17, O = g18, J = g19. Both D and J are dirty ANDs; O is OR.
Gate19 is live and therefore is an operand of the final gate.

If J does not read O, swap gates18 and19. This gives AAOA with both first
ANDs junk and the function unchanged. Otherwise, using commutativity, write

    D = A AND B,   J = O AND T,   F = J AND R.

Here A,B are prefix wires; T is a prefix wire, D, or O. R cannot be J or O,
because J <= O and either choice would make the dirty J the output. Hence R
is a prefix wire or D. These exhaust the possible references.

### Case T = O (J is an AND-copy of O)

If R = D, O cannot read D: absorption would make F = D dirty. Thus O reads
only prefix wires. Replace the suffix by D, AND-copy(D), O, D AND O. This
is AAOA; its first two ANDs are dirty and every suffix gate is live after the
copy is used by the final AND.

If R is a prefix wire, liveness of D forces O = D OR Q for a prefix wire Q
or Q=D. Replace the suffix by D, AND-copy(D), copy(D) OR Q, R AND that OR.
Again this is AAOA, both first ANDs are dirty, and the function is unchanged.

### Case T = D

R=D would give output J and is impossible, so R is a prefix wire.
If O reads D, absorption gives F = R AND D. Use D, AND-copy(D), AND-copy(D),
R AND D, with the copies chained and the final gate reading the last copy.
This is AAAA with three dirty intermediate ANDs.

Otherwise O reads only prefix wires. Set H = R AND D. If H is dirty, order
the suffix as D, H, O, H AND O. This is AAOA with two junk ANDs. If H is
clean, then H = F: it contains F and is false on all negative inputs. Use
the preceding three-dirty-copies AAAA construction for H = R AND D.

### Case T is a prefix wire and R = D

If O reads D, absorption gives F = T AND D. Use the AAAA construction just
described. Otherwise set H = T AND D; if dirty use D,H,O,H AND O, and if
clean use the same AAAA construction for H=F.

### Case T and R are both prefix wires

Liveness forces D to feed O, so O = D OR Q, where Q is a prefix wire or D.
Set H = R AND T. Since F = H AND O, H covers all target edges. H cannot be
clean by the clean-prefix-plus-one-AND contradiction above. Hence H is dirty.
Use D,H,D OR Q,H AND (D OR Q), with the last two gates referencing their
predecessor outputs. This is AAOA and preserves the entire Boolean function.

These cases allow repeated operands throughout. Each replacement has exactly
four live suffix gates, keeps gate17 dirty, and makes gate18 dirty.

## Prefix normalization and safe SAT consequence

Some absorption replacements discard prefix dependencies. Prune unused prefix
gates and restore 17 with the reviewed final OR-copy chain, then reapply the
reviewed ordering and prefix normal forms. These changes preserve retained
signals on all independent inputs and preserve or increase their edge values.
The suffix remains exact on the 40 boundary rows, both first junk gates stay
dirty, and all prefix ANDs stay clean. Universal support/ancestor-cost and
common-neighbor consequences can be reassigned on the resulting prefix.

Therefore a fresh complete search may add the unit `J18` to the reviewed
original-DAG parent, provided this normalization receives independent review.
It must not be described as a clause implied by the existing parent. Adding
it to a future search is a symmetry/normal-form restriction with the proof
above. Existing searches and their certificate claims remain unchanged.

## Additional stronger forms already derived

For AAAA, take a minimal clean subfamily of its at most five external prefix
factors. Its size is 3..5: one or two would give a clean circuit with at most18
gates. Sort the factors and pad with copies of the smallest. A left-fold chain
has g17,g18,g19 all dirty and g20 clean. The leaf equality patterns are exactly
`a=b=c<d<e`, `a=b<c<d<e`, or `a<b<c<d<e`.

For AAAO, the final OR is P OR g19 with clean prefix wire P, and the three
preceding ANDs form a clean product of at most four external factors. A minimal
clean factor family has size3 or4; a smaller one would give an all-clean circuit
with at most19 gates. Sort and pad its smallest factor, obtaining `a<=b<c<d`.
The chain has junk17,junk18,clean19, and output P OR g19. Minimality supplies
one independent input witnessing all proper chain products dirty.

Detailed arguments and finite checks are preserved at
`/tmp/oec/pequalnp-pilot-18/math-analysis/junk_preserving_chain_normal_forms.md`
and `junk-preserving-chain-validation.json` (4,704 abstract truth rows,
180 private-negative-row checks, 4,096 concrete fixture input checks).
These checks do not construct a17-gate prefix or prove shard exhaustion.

## Boundaries of the result

No one-junk impossibility, global22 lower bound for arbitrary monotone circuits,
or full posted theorem is claimed. The useful new consequence is the existence
of a representative with consecutive first junk gates. No code, CNF, lease,
solver, git or named Lean file was modified for this argument.

Sub-agents: none

## Follow-up: AAOA has four forms, plus an AAAA fallback

This additional classification is awaiting separate independent review. It
assumes both first ANDs are junk, as justified above. It does not use a one-junk
lower bound. Four exact formulas suffice for AAOA, with all letters prefix
wire occurrences and repeats allowed:

| Form | g17 | g18 | g19 | g20 |
|---|---|---|---|---|
| T1: a AND (b OR cde) | c AND d | e AND g17 | b OR g18 | a AND g19 |
| T2: a AND (bc OR de) | b AND c | d AND e | g17 OR g18 | a AND g19 |
| T3: ab AND (c OR de) | a AND b | d AND e | c OR g18 | g17 AND g19 |
| T4: abc AND (d OR e) | a AND b | c AND g17 | d OR e | g18 AND g19 |

In each form g17 and g18 are required to be dirty. In T1/T4 the three-factor
product at g18 is dirty, so every subproduct is dirty and those three factors
can be sorted arbitrarily. In T2 both pairs can be sorted and the OR branches
exchanged. In T3 the two pairs can each be sorted, but their outer/inner roles
must not be exchanged without a further identity.

Proof by ports: write D=g17=A AND B, J=g18, O=g19, F=O AND R. Gate19 is
live, so it feeds the output. R cannot equal O: liveness forces dirty J into
that OR, which would then be the dirty output. Thus R is prefix, D or J.
J either is D AND C (C prefix or D), or is an independent prefix pair.

1. If R is prefix, J must feed O. If J=D AND C, the other OR operand is
   prefix, D or J. A prefix operand gives T1. An operand D or J absorbs the
   OR and gives a pure conjunction, handled by AAAA. If J is a prefix pair,
   D can be live only as the other OR operand, giving T2.
2. If R=D, again J must feed O. If J=D AND C, an OR operand D or J would
   make the output equal dirty D or J, impossible. A prefix operand b gives
   D AND (b OR D C) = D AND (b OR C). This is T4 with the outer pair D
   padded to three factors by repeating one factor. C=D would make the
   output dirty and is impossible. If J is an independent prefix pair, an
   OR operand D is impossible, an operand J gives a pure conjunction, and
   a prefix operand gives T3.
3. If R=J and J=D AND C, O cannot read either D or J, since O would contain
   J and make the output J dirty. Thus O reads two prefix wires, giving T4.
   If J is an independent prefix pair, D must feed O. The other OR operand
   J is impossible, D gives a pure conjunction, and a prefix operand gives
   T3 after exchanging the two independent junk gates in the schedule.

When J=D is a repeated-operand AND, represent its factor product by repeating
one of A/B in T1 or T4; since D is dirty all intermediate subproducts are
dirty. A pure conjunction produced by absorption is either R AND D, R AND J,
or D AND J. Retain the dirty D/J as appropriate and fill unused suffix slots
with AND copies; alternatively apply the already proved AAAA chain form.
All such outputs remain exact F. Prefix prune/stabilize/pad applies as above.

Thus the complete normalized search can use AAAA, AAAO, and these four AAOA
templates, all retaining junk17 and junk18. The old seven loose templates had
dropped junk flags; this is a different, stronger six-template reduction.
For this conclusion use the precise port schedules in the table, not merely
the old template names, because an old implementation may put its OR earlier.

The suggested two AAOA forms alone do not follow from Boolean identities.
With five distinct independent terminals, T3 has minimal true terms of sizes
3 and4 with a two-variable intersection; T4 has sizes4 and4 with a
three-variable intersection. T1 has sizes2 and4 with intersection size1, and
T2 has sizes3 and3 with intersection size1. Relabeling cannot identify these.
Repeated terminals or constants lose essential variables, so cannot fix this
five-essential-variable distinction. This is a warning about generic shape
coverage, not an actual 21-gate graph counterexample. A graph-specific theorem
could conceivably remove T3/T4, but none is established here.

## Generated artifacts

The self-contained generator is
`/tmp/oec/pequalnp-pilot-18/orch/S01/build_consecutive_junk.py`, SHA
`3802650c1492cb267a8f8ae5e44715b9b86fe88e642617b85ffbbe857184bb71`.
Use its fresh `consecutive-junk-v2/` directory. `normalized.cnf` is exactly the
original11968-variable parent body plus unit3243, with114567clauses and SHA
`3fefefe3949bc703fc2b9f023be12bc42f1afe7619e8ed5ed63be2f8e7648812`.
The three operation cases each have114571clauses. The optional AAAA-chain
and AAAO-chain variants have116381 and115946clauses, respectively. They keep
the original junk requirements and add the sorted-chain restrictions described
above. They are alternatives to two operation cases, not extra partition cases.

`family.json` binds every CNF/metadata pair. `encoding-validation.json` separately
checks unchanged original body bytes, every added clause, all16operation
assignments,6300leaf-order projection assignments, source/metadata bindings,
and rejection of wrong parents and existing output directories. PASS. No
solver has been launched. The earlier `consecutive-junk/` directory is a
superseded generation with less precise metadata field wording; use v2.

`LateJunkBool.lean` in the same scratch directory contains six small Boolean
helpers for absorption, reordering, copying, clean operands, dirty parents,
and equality of a clean superfunction with F. Its39lines compile successfully
under the shared Lean lock in1.33seconds; source SHA
`cbc7bcfab33a9595038592bd3115552df26b723d886ae51c4cb6fd79ab4c9843`.
Full successful logs are `late-junk-bool-third.stdout.txt` and `.stderr.txt`,
both empty; `late-junk-bool-third-validation.json` records exit0 and the source
hash. Earlier failed attempts are retained separately. The independent axiom
inspection in `late-junk-bool-axioms.stdout.txt` reports no axioms for the three
Boolean identities, propext for the clean/dirty operand lemmas, and Quot.sound
for functional equality. Audit exit0 in1.70seconds, empty stderr. These are
checked components, not a Lean formalization of the full four-gate normalization.
