# Independent source review: WeightClassification

Reviewed source SHA256:
`9c9c1fc9de1a43e3c5f9c1e3b086ab447c2894e0c2b51ffaf25e526789d8a037`.

Result: source semantics and finite-data assembly PASS. Root reported the
second compilation/export checked with exit0 and empty logs. The final source
was reread after that check. Its changes from the first reviewed version only
fix Boolean simplification in surplus_ten: the false classTest conjunct is now
closed directly after substituting possible9=true. The argument and every
theorem statement retain the same scope.

* All130 WeightSpec tuples exactly match the independently validated generator
  output. Every ValidPrivate witness, geometric cost witness, subset condition,
  and numeric weight inequality was checked by a finite Python validator.
* An alternate enumeration directly optimized J inside each actual independent
  ineligible mask, using cost geometry from every vertex of that mask. Across
  all560 independent masks and261 feasible T sets, its strongest weights agree
  with the130 subset-key rules. This validates coverage, not just the rows.
* The sixteen finite chunks use offsets0,1024,...,15360 and all quantify over
  Fin1024. They therefore cover all16384 vertex masks without gaps.
* The cap10 and cap11 lists match the independent five- and117-mask censuses.
* possible_of derives independent ineligibility from eligible vertex-cover
  coverage, then applies only WeightSpec rules whose key is a subset of the
  actual ineligible set.
* The unconditional23-gate lower bound follows from Bplus≥10 and the checked
  normalized surplus identity. The≤24 classification only concludes the117
  possible masks, with the five-mask refinement when Bplus≤10.

This source does not prove the posted existence statement, nor does it exclude
all24-gate circuits. Its import is the checked graph-specific UpstreamGraph
helper, so it is a dependency-test artifact rather than an allowed standalone
gap submission.
