# S01: consecutive first junk gates

Updated 2026-11-24 04:03 UTC. Mathematical normalization independently reviewed
by S04, with generated clauses independently checked. This is not a Lean
formalization or an exhaustion result. S01 has launched no solver.

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

This additional classification and its generated clauses passed S04 review. It
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

The four AAOA files are in `orch/S01/aaoa-four-v1/`. Their self-contained
generator `build_aaoa_shapes.py` has SHA
`6bcb7e1abdb2c65ffdc9a6a1ced8554509ed2f96a40a756f30d718708256ae63`.
The family manifest has SHA
`b05805738736e9b04257657dd8bd39d0fe1c6c31428f191a9fa727fb32109401`.
All four preserve the exact reviewed AAOA parent and add 879,1313,877,1313
clauses. S01 controls check every added clause,9000order projections and128
five-terminal truth rows. S04 independently reviewed the full six-case cover
(AAAA-chain,AAAO-chain,T1,T2,T3,T4), including the AAAA absorption fallback;
its manifest is `orch/S04/six-case-review-manifest.json`, SHA
`96286c7bc5424c199bf5a1336e9d52e2f016c1a726403af0959ca4ebd8d8f39b`.

## Early full-cover prefix factors

For a clean-prefix wire W accepting all16edges, with proper singleton support
S, the exact function is W=F OR OR(S). Negative inputs follow from prefix
cleanliness; positive inputs follow from monotonicity and edge coverage.
The already formal support bound is

    L(S) = |S| + |E(G minus S)| + cover(G minus S) - 1.

Because S plus a residual cover covers G, L(S) is at least
|E(G minus S)|+6. Thus a nonconstant full-cover wire needs at least6ancestor
gates. Free TRUE is exempt: full support cannot be excluded merely by this
bound. There is an important indexing distinction: augmented wire18 is g5,
so has at most6earlier-and-current gates; wire19 is g6 and has at most7.

Every proper support with L<=7 has exactly one of these forms:

| Support size | Residual edges | Residual cover | L | Number of supports |
|---|---|---|---|---|
| 7 | 0 | 0 | 6 | 22 |
| 8 | 0 | 0 | 7 | 52 |
| 6 | 1 | 1 | 7 | 46 |

The finite enumeration is `orch/S01/early-full-cover-supports.json`. In
particular wire19 need not be an OR of a seven-vertex cover: it may compute
the OR of six variables and one residual edge product. Example:

    g0=x1 AND x4; g1=x5 OR x6; g2=x7 OR x8; g3=x9 OR x10;
    g4=g0 OR g1; g5=g2 OR g3; g6=g4 OR g5.

Its support is {5,6,7,8,9,10}; the only residual edge is(1,4). This is a
seven-gate full-cover prefix factor, not a circuit for F.

These small bounds also constrain gate types. An OR-only ancestry graph of
a proper-support output has its support variables as leaves, and stops at
clean AND outputs. If any AND is present, at least one such frontier exists.
A connected binary OR graph with at least |S|+1 distinct leaves needs at
least |S| OR nodes. Consequently a seven-variable OR factor with at most7
ancestor gates has no AND ancestor. An eight-variable OR with7gates is an OR
tree. A six-support,one-residual-edge factor with7gates has exactly one AND
and six ORs. The AND is the raw residual-edge product: an OR ancestor of
that AND would lie in the six-support OR ancestry and vanish on the residual
edge row. Constants, aliases and repeated leaves cannot improve these counts.

## Limits of independent factor-cost obstructions

The sorted-budget proposal alone admits supports {8,10},{4,6},{3,4} with
L=14,16,17. Their zero sets cover all24MIS and the family is minimal.
`orch/S01/position-budget-counterexample.json` retains this finite check.
This is not a common17-gate prefix construction.

The refined no-common-neighbor proposal also has a feasible support family:

| S | Common neighbor | Residual edges | Residual cover | L |
|---|---|---|---|---|
| {4,8}=N(1) | 1 | 10 | 5 | 16 |
| {1,8,10}=N(4) | 4 | 7 | 4 | 13 |
| {1,4,5,9}=N(8) | 8 | 6 | 3 | 12 |

All three have a common neighbor, so r=0 and the proposed cap17 permits
every factor. Any independent input hitting N(1) contains4 or8. In the
first case it cannot hit N(4); in the second it cannot hit N(8). Thus their
zero sets cover every independent input. Singleton inputs1,4,8 respectively
witness that all three factors are necessary. The independent scalar script
`orch/S01/check_common_neighbor_family.py` verifies costs,common neighbors,
all24MIS and8192full-input identities; full logs and
`common-neighbor-family-validation.json` are saved alongside it.

S05 algebra handoff: let A be the triangle function on {3,6,7},
B=x10 AND(x0 OR x2 OR x6), C=x9 AND(x0 OR x5 OR x7), D=x2 AND x5.
The three required outputs H_v=F OR OR(N(v)) are exactly

    H1=A OR B OR C OR D OR x4 OR x8;
    H4=A OR C OR D OR x1 OR x8 OR x10;
    H8=A OR B OR x1 OR x4 OR x5 OR x9.

Their conjunction is F. These are an exact multi-output optimization target,
not a17-gate implementation. Shared-prefix cost remains the obstruction to
resolve. No uniform cap for common-neighbor factors follows from dominance:
the earlier dominance rule requires its dominating wire to have empty
singleton support. No general ancestry antichain is asserted here.

## New joint bound excludes that three-factor family

The individual-cost counterexample above has a stronger joint obstruction.
For a minimal family of at least three proper full-cover factors in a
productive clean prefix, fix S_i with nonempty residual graph. Let z count
other factors with no common neighbor, and let d count distinct vertices v
in S_i which are the unique common neighbor of some other factor. Then

    prefix gates >= L(S_i)+z+d.

Full argument: `orch/S01/joint-factor-cost.md`, SHA
`78070f3939d1ac081e67f1b4f18e1655e1aaaed7e4efa4b0d9fa3a4cf24d865f`.
This passed S04 independent mathematical review, as relayed by main at04:10;
it is not Lean or an implemented cut. Each relevant factor outside the ancestor cone costs a separate output
gate; an ancestor factor instead supplies a clean AND removable on restricting
S_i, in addition to the usual |S_i| OR deletions. Distinct owners supply
distinct ANDs. Multiple factors with one owner are charged only once.

For S_i=N(1), the other owners4,8 belong to S_i, giving16+2=18. Hence this
particular family cannot fit the17-gate productive clean prefix, even though
all its individual-cost and negative-row conditions hold. This does not
exclude every possible factor family or prove AAAA exhaustion.

The same calculation gives19prefixgates for N(3),N(6),N(7), using L(N(3))=17
and the two charged owners6,7. Thus both S02 triangle pin families, including
all six individually cost-feasible permutations, are excluded at17gates by
this mathematical argument. `orch/S01/triangle-joint-cost-validation.json`
binds all twelve pinned metadata files and checks the finite graph data and
eight ancestor/outside-cone count cases. It is not a solver certificate.

## First surviving support family and a further obstruction

The authorized single-CPU finite probe found a survivor in0.025seconds and
stopped after six search nodes. It did not exhaust sizes3..5. The exact source
and complete logs are `orch/S01/enumerate_joint_supports.py` and
`joint-support-enumeration.stdout.txt`/`.stderr.txt`; result
`joint-support-enumeration.json`. This uses sorted position budgets and joint
charges, with edgeless residuals exempted from the joint charge.

The surviving supports are A={8,10}, B={9,10}, C={4,6}. Their individual costs
are14,14,16, common-neighbor owners4,0,10, and joint bounds15,15,17. Independent
`validate_joint_survivor.py` checks4096full-input identities, minimality,
antichain and cost values. A AND B is exactly F OR x10, and ABC=F. These
support functions are not a common-prefix construction.

New structural argument, pending independent review:
`orch/S01/tight-survivor-obstruction.md`, SHA
`69bb5f1587acceb0fd5ecebf3ed4a525919c439eef62c70a7c11e9ae149a1acc`.
It excludes this triple from17productivecleanprefixgates as well. Joint
tightness forces B ancestor C. Three selected OR outputs occupy three of
indices13..16, leaving one AND q. Hence q=B AND R, C=q OR P, with supportR={0}
and supportP={4,6}; R/P are raw inputs or core gates0..12. B has exactly14
ancestor gates, including every core gate. A restriction-charge lemma for
arbitrary supported ancestors forces R to be rawx0. Consequently P accepts
eight residual edges with a matching of size4, giving cost13; P is gate12.
It must directly feed B's OR, contradicting their incompatible supports.

The new charge permits a non-full-cover ancestor: after restricting the
output's support, bypass its first AND by the other operand if that operand's
support lies in the zeroed set. This preserves independent rows and only
increases accepted edge rows, sufficient for the formal partial-edge bound.
The proof counts this AND separately from support OR deletions.

`check_tight_survivor.py` and `tight-survivor-validation.json` verify all four
possible late-prefix position patterns, the residual graph, matching/cover
certificate and arithmetic. Full logs are saved. These finite controls do
not independently verify the structural proof. No further support enumeration,
solver, active-worker mutation, or named Lean edit was performed.

## Coverage of the515 three-factor, common-neighbor survivors

S04 independently enumerated all18424 triples from49 common-neighbor support
candidates, retaining515 after individual, sorted-position, joint and minimal
negative-cover tests. S01's new scripts consume that exact hash-pinned list.

The reusable one-spare-late-gate lemma applies when all three individual costs
are at least14. Only one unselected gate remains among indices13..16. Ancestry
between selected factors therefore forms a star through one clean AND. Its
source and nonchildren have exact14-gate cones; each child has a16-gate cone.
Supported-ancestor restriction charges and partial-operand bounds reject all
possible stars for233families. Full proof `orch/S01/one-late-AND-pattern.md`;
source `classify_three_common_factors.py`; results and full logs alongside.

The further position/relation filter enumerates all distinct output positions
and transitive selected-ancestry choices, checking necessary intervening-AND
slots and actual cone upper/lower bounds. It excludes20additional families.
The combined result is253excluded,262remaining. All are mathematical pattern
exclusions pending independent review, not a SAT or Lean certificate.

Proof `orch/S01/three-factor-position-conditions.md`, source
`classify_three_factor_positions.py` SHA
`30a0f04da70984ac6e554325f0ceff246febaf0c558572b8dbc0ff6b18bd610d`.
Its result `three-factor-position-classification.json` saves every family's
rejection counts or an explicit remaining abstract position/ancestry pattern.
The run examined13927choices in0.057seconds. A v2 cone-union experiment gives
the same count; it is preserved but unnecessary for the253claim.

Separately, `orch/S01/irrelevant-input-charge.md` gives a proposed reusable
per-output +1cost charge: if rawv is an ancestor, v is outside supportS and
N(v) is contained in S, the existing ancestor partial-edge bound increases
by1. Nonempty residuals use an extra first-AND deletion; empty residuals use
the elementary OR-support node count plus that AND. It does not require any
selected factor family. Full support automatically disables the condition.
An encoding can use17penaltybits and3366implicationclauses with existing
gate-ancestor/raw-operand selectors; no code for that cut was authored here.

None of these results closes AAAA:262three-factor/all-common-neighbor patterns
remain, and other support classes and larger families are outside this scope.

## Multiple irrelevant inputs: +2/+3 coverage

The per-output +1 charge passed S04 mathematics, trigger-specification and
counter-reuse review; S06 prepared its encoding. S01 has not modified a CNF.

The new `orch/S01/disjoint-neighborhood-input-charge.md` generalizes the charge
to any set I of irrelevant actual-ancestor inputs with pairwise-disjoint
neighborhoods. Their first ANDs are distinct: sharing an operand would require
a nonempty intersection of neighborhoods, while entering opposite operands
would make the AND true on an independent pair. Restriction and simultaneous
bypasses remove |I| distinct ANDs in addition to the support OR deletions.
The empty-residual case uses |S|-1 OR support nodes plus these ANDs. The
generalization is pending independent review; no Lean theorem is claimed.

The complete2048-support table has14eligible input pairs and3eligible triples.
There are202support masks permitting+2,132with nonempty residual graph, and
9masks permitting+3. Maximum disjoint charge is3. Actual input ancestry is
still required; these counts alone do not justify a penalty on an output.

This does not reduce the262remaining all-common-neighbor factor families.
In a C4-free graph with minimum degree2, a support with a common neighbor
has at most one vertex outside it whose neighborhood it contains. The
proved ancestry lemma also prevents a no-common-neighbor prefix wire from
reaching a common-neighbor factor in a productive live prefix. Thus no live
prefix wire of these families can trigger+2. The broader suffix search can.

An unimplemented encoding outline reuses per-input witness flags and existing
counter thresholds: relative to+1, +2needs204variables/3621clauses; supporting
+3as well needs221variables/3689clauses. These are separate threshold bounds,
not a sum of1+2+3penalties. Exact graph witnesses, full logs, source hashes,
proof and encoding caveats are bound by `orch/S01/disjoint-charge-handoff.json`,
SHA `c4ec0d309a0a8c7702629d51ab617138f59c5d663d4e80e972cd17cd7573582c`.

## Reviewed k5 common-neighbor closure and new r-positive relaxation

S04 independently passed all331 k5/r0 exclusions; reviewed remaining counts
are115 k4/r0 and262 k3/r0. The exact combined proof and finite results are
bound by five-factor-closure-handoff.json SHA c0dbd623da51cb86717098177a867eabe3399fc1880d3fe8659a44e4152073b1.
All-common-neighbor k5 is closed only within the stated productive17-prefix
minimal-full-factor scope; there is no global AAAA or shard conclusion.

The stronger irrelevant-input neighborhood-hitting charge also passed S04
math review and S08 actual S06 delta review. Hitting rank, rather than only
disjoint neighborhoods, yields24 minimal rank2 patterns and5 rank3 patterns.
The proof/coverage is preserved in the same27-file closure handoff.

New r-positive work is bound by no-common-cover-handoff.json SHA a4f80666a2c3de18353fbc10a24ec0bcf6a035a7b027f31854086baf15aa4a76.
A no-common-neighbor factor lies outside every other minimal selected-output
cone. Hence costs are at most18-r for such outputs and17-r for common-neighbor
outputs. Across all958 supports,382 exact MIS-rejection patterns retain their
minimum costs. A complete scalar relaxation excludes k3/r3; an independent
edge-branch-cover/bitset-triple enumeration confirms no three CN-empty
patterns of cost at most15 cover all24MIS. Eleven other(k,r)classes have
explicit abstract support-family witnesses. No shared-prefix circuit follows.
This new exclusion awaits independent review; all other r-positive classes
remain open. Sources, complete results and full stdout/stderr stay in orch/S01.

## Exact mixed triples and pending two-spare extension

The complete exact958-support census now leaves800 triples with one no-CN
factor,68 with two, and none with three. This uses the existing cone caps,
nonempty-residual joint charge and reviewed position conditions with the
no-CN ancestry prohibition. All868 survivors have concrete abstract
position/ancestry patterns; none is a circuit claim. Handoff mixed-triple-handoff.json SHA 159ca97f5b0d24fec9f727e8a58d93648f23cec92b6ef6e323ab7f754b570b8d.
Independent review remains pending. S04 proposed gamma-region refinement
removes none here because every surviving no-CN factor has gamma2.

A separate generic two-spare forest argument rejects4 additional k3/r0
families and3 k4/r0 families. Its handoff two-spare-forest-handoff.json SHA 5bcf4d6d1127b8a631b248073a6ce3b2bb9d51fa97e2aa4e4cd046aa6e7bb36a preserves proof/source/complete tables/logs.
Pending review, these would reduce262/115 to258/112; until review the older
reviewed counts remain authoritative. No new k5 work is needed: its r0
case already passed independent review.
