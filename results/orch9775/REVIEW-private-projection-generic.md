# Independent review: PrivateProjection generic framework

Verdict: PASS for the unchanged generic prefix and its stated scope.
The 44 concrete finite witnesses are being reviewed separately by
`status_check`; I do not claim to have independently replayed them here.

Reviewed source: 637 lines, 40,391 bytes, SHA-256
`44b9b39221be13e8502eeaf2b3393ee1b2201151c98159b58e4f8373e8b413f4`.
Programmatic comparison confirms that new lines 4–108 exactly equal
upstream `L_meta_9774.lean` lines 4754–4858. That archived upstream source
was independently matched to commit
`790ef40780fc680c09cde228f2229fe058bd6e08` in my preceding framework review.
The comparison is recorded in
`projection/private-projection-generic-independent.json`.

`partial_exits` is a generic graph/circuit theorem. It constructs one
exposure exit for each member of `Q`, proves those exits injective using
the independent sets containing `T.erase f`, and proves them disjoint
from the exits assigned to `J`. The inclusion `Q <= T` is explicitly
used both for injectivity and membership in the carrier exit set. Thus
the sum `J.card + Q.card` is justified by two disjoint injected sets,
not by an unproved assumption that all witnesses are different.

`local_merge` is a graph-specific application of the previously checked
generic charging theorem. Its `Bzero = 0` premise is explicit and passed
to `occurs`. Projected neighborhoods are injective whenever their sizes
are at least two because distinct projections intersect in at most one
vertex. The size-three and size-two projection families are separated
before applying `sup_charge`; the argument does not assume their images
are disjoint without proof. Independence of `P`, `P.card <= 7`, and
membership of the indexing vertices in the ineligible set are retained
as premises.

`private_bound` combines these merge and exit bounds with carrier flow,
pure-branch surplus, and the complement identity for eligible vertices.
Its conclusion is the displayed conditional inequality involving
`Bplus`; it is not an unconditional circuit bound. In particular,
`Bzero = 0`, `I = ineligSet`, independence and cardinality of `P`,
`Q <= P`, and every neighborhood/free-witness condition are explicit.
Natural subtraction `14 - I.card` is tied to the checked complement
identity through the equality with the actual ineligible set.

Each of the 44 following `projection...` statements still requires
`Bzero = 0` and equality to its particular ineligible mask. Their
conclusion is `12 <= Bplus`; it must not be extended to the `Bzero = 1`
case or to unlisted masks without further proof.

Both archived complete check logs are empty, and the validation JSON
records exit 0. No build was rerun for this review. The only options are
the permitted `maxHeartbeats` and `maxRecDepth` limits. The source has no
`sorry`, new axiom, `native_decide`, forbidden root marker, string
literal, or attribute. `decide +kernel` is used for finite certificates.
The scratch import `UpstreamGraph` requires the usual final single-file
assembly/checker treatment before any proof PR is claimed.
