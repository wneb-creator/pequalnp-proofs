# RootCover independent review

Reviewed 2026-11-25 by lower_bound. PASS for stable source SHA256
`d56457c7b36fac72b1117bfd4e20a5709516f36a6137abd201699da73fc65107`.

The checked AcceptingPath prefix is byte-for-byte unchanged. The intermediate
path_flag_transition theorem matches the independently checked selected-path
source. The final RootCover fragment uses an earlier clean boundary root to
contradict minimality whenever an accepted pair misses a positive false-flag
support. This applies to both dirty operands and to the opposite operand of
an accepted false-to-true selected transition. The raw-filter cover then
contradicts the missed dirty label.

The final live-set correction is necessary and correct: roots lie in V,
selected-child closure propagates path membership in V, and hraw is required
only for live valid clean ANDs with false carry flag and true chosen-child
carry flag. Thus irrelevant nonlive consumers do not enlarge the required
raw cover. Neither a last-transition assumption nor hidden reachability
assumption is used.

The result is conditional coverage of accepted root pairs. It is not an edge
count, a full one-dirty size bound, or a proof/refutation of L-meta-2732.
Author-reported Lean exit 0 and the empty complete root-cover-check-3.log
were inspected; no independent build was started. The forbidden-format scan
returned status 1 with no matches.
