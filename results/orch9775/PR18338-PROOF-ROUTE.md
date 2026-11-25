# Public proof route and compression use

Read-only source: [PR18338](https://github.com/open-goat/pequalnp-proofs/pull/18338),
author `ithurtstom`, public name Thomas Brovelli (Meyer), exact head
`79345c8812d893da9c305e0d1bec931bb198594a`. This is not a `wnebpilot` login.
The PR was observed open, not a draft, and adds only
`lean/PEqualNP/Outside/L_meta_9777.lean` (7,611 lines, 380,727 bytes).
The fetched source is `new-upstream/PR18338_L_meta_9777.lean`, SHA256
`5a772e3c8ed68fee29dbf8dbd2f723b45b9bbb7240f03dd28ebe9fb5c9740554`.
Its theorem is the exact negative twin of L-meta-9775. It imports only
`PEqualNP.Defs`. Root reported its unchanged full source compiled successfully;
this note does not independently assert an axiom audit or accepted PR status.

The public argument normalizes to a strict live binary DAG, tracks singleton
support and residual fanout units, and classifies 143 canonical ineligible-set
orbits. Small finite geometry checks select analytic counting arguments.
It does not use the large SAT payloads in our current construction.

The four expensive current certificates map as follows:

| Ineligible mask | Public orbit index | Public exclusion |
|---|---:|---|
| 111 = {0,1,2,3,5,6} | 136 | `elim_cnt_b1`, using `cnt_b1_idx 23` |
| 4757 = {0,2,4,7,9,12} | 141 | `elim_141` |
| 4293 = {0,2,6,7,12} | 132 | `elim_132` |
| 2213 = {0,2,5,7,11} | 129 | `elim_129`, an instance of `elim_res2_3w3` |

Blindly transplanting these declarations is inefficient: their dependency
closure includes global orbit classification and side-counting infrastructure.
Our existing weight classification supplies the needed surplus facts. Our
residual-code approach independently removes the certificates for 111, 4757,
and 2213 through small finite checks (lower_bound owns those sources).

For 4293, lower_bound's existing exact-position and exposure witnesses force
the residual codes of vertices 5 and 10 to be empty. Thus each has at most two
consumption slots. The public proof's final local argument then closes this
case, without importing its five-slot or full-support infrastructure:

1. The assigned slot of center 12 belongs to W5; the assigned slot of center 0
   belongs to W10 and carries vertex 8.
2. Edge 5–10 supplies a slot e in W5 and its opposite in W10. Edge 5–9 supplies
   f in W5 and its opposite in W9. Neither e nor f is the assigned slot of 12,
   because the opposite operand of that assigned slot carries only 12.
3. Since W5 has at most two slots, e=f. The opposite slot therefore belongs to
   both W10 and W9. It differs from the assigned slot of 0.
4. The generic exposure lemma, using neighbor 4 of vertex 10, provides a W10
   slot carrying neither 8 nor 9. With only two W10 slots it must be one of the
   preceding two; each choice contradicts its missing label.

This specialization is `lemmas/Public4293.lean`, 73 lines / 3,281 bytes, SHA256
`8029db2ea407f35996febfb335ed32f4345a9ab0465f4a98e942122812c6b722`.
It imports `CompactFramework` and includes explicit provenance for the adapted
`pa_m1` / `elim_132` strategy. The theorem is
`Public4293.low_slots_impossible`: actual StrictLive and sem_Comp premises,
mask 4293, and |W5|,|W10|≤2 imply False. There is no unproved normalization or
graph-geometry assumption in it.

Author compile/export returned exit 0 with empty logs:
`/tmp/oec/pequalnp-pilot-103/9775-public4293-001.stdout` and `.stderr`.
Lower_bound owns `ResidualShape4293.lean` and the final wrapper connecting its
empty-code conclusion to these two slot bounds. Replacing the roughly 31 KB
certificate with that wrapper and this helper should reduce the final file.

No lease, git, PR, or workflow mutation was performed by this agent.
