# L-meta-2590: reduction-strategy record

Frozen after root reported HTTP 410 at 2026-11-25 15:22:26 UTC, despite previously advertised expiry 15:34:37. Root owns all desk actions and result preservation.

## Checked component

`/tmp/oec/pequalnp-pilot-99/gap2590/reduction_strategy/FourOrbitCodes.lean`

- 65 lines; SHA256 `720f5c65cc9a106c1dabb2725ae5e252a0f65d8aa07070168b2294c60af82f25`.
- Lean exit 0; complete `FourOrbitCodes.stdout` and `.stderr` are empty.
- Scratch imports checked `PetersenGeometry`; final use requires inlining root/library namespaces and dependencies.
- Any vertex with two distinct ineligible neighbors has at least three consuming positions.
- For the maximum independent-set representative I={2,4,5,6}, every eligible vertex has two such neighbors. Consequently each eligible vertex occupies at least one residual surplus unit.
- This does not prove the posted statement: six labels may share the at-most-four residual units.

## Unchecked draft, frozen

`FourOrbitLowSharing.lean` was written immediately before the lease failure and was not compiled. It attempts to prove that two distinct eligible labels, each occurring in exactly one residual unit, cannot share that unit. Treat it as research source only.

Mathematical route: `ri_gen` says singleton residual sharing makes every consuming position except one carry the other label. Every assigned ineligible-neighbor position is forced to carry that other label: each neighborhood supplies a nonadjacent witness, and `sem_pg_cover_free` excludes it from being the exceptional position. Applying this in both directions puts the union of both vertices' ineligible-neighbor positions in both consuming codes. The union has at least three positions; each code has at most three by `sem_code_count`. The codes are then identical, contradicting `sem_antichain`. This still leaves high-incidence residual labels, so it is not a complete orbit exclusion.

## Other routes examined

The generic L-meta-971 surplus framework has been adapted by library_route to Petersen. Hypothetical size <=19 gives total surplus <=10. The eligible set has size 10-|I|, leaving residual supported surplus plus empty-support surplus at most |I|. Independent-set orbit representatives are empty, {0}, {0,2}, {1,3,5}, {1,4,5}, {2,4,5,6}.

For the size-four orbit the six eligible vertices induce three disjoint edges; their four ineligible neighborhoods are triples with pairwise intersection one. Under zero empty-support surplus, unique-chain factorization can produce exact neighborhood masks because the complement of each neighborhood inside those six vertices is independent. The generic `cnt_main` charges eight merges and four large exits, but another five charges are needed. Matching-edge witnesses do not directly satisfy its independent-set witness condition, so no complete bound was claimed.

The earlier structural normalization route may eliminate the first-AND seed case by choosing a least circuit, lifting below-function OR gates, and proving that the absence of raw input OR gates forces a DNF circuit of at least 29 gates. Lifting can create a raw input OR; that creation would be a successful reduction to the two OR seed cases, not an invariant failure. This argument is not yet formalized. Existing seed bounds only yield monotone >=19 for first AND and >=18 for first OR, short of the requested >=20.
