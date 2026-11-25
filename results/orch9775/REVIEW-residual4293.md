# Independent review: residual-code closure for mask4293

UTC: 2026-11-25T17:49:00.472319+00:00

Verdict: PASS. ResidualShape4293 SHA-256 `17d87f83552ed555b6f75cfeba04cf55fc54da54072ba68cca2cd58081f21be8` (33 lines,4,369 bytes); Residual4293 SHA-256 `a9e3c573b2a06745e5f454864a2e365e5ae33cc512e1679d330d0ed35092f341` (16 lines,777 bytes). Author validation records both checks/exports exit0; all four complete success streams are empty. No new compilation was run.

I independently parsed all eight geometry and directed-code constraints from the actual shape source and checked every independent-set, adjacency, exposure, eligibility, shared-neighbor, and distinguishing-neighbor premise. All256 assignments to the four Fin2 code sets were enumerated. Exactly two satisfy the antecedents, and both have code5=code10=empty. The Lean conclusion correctly asserts those empty codes, rather than falsely claiming the antecedents alone are inconsistent.

The wrapper obtains a genuine two-residual Layout from Bplus=11 and the five-element mask4293. It applies the shape theorem to that Layout's actual pure branch and residual-unit enumeration. Layout.size_code converts each empty code to the required at-most-two exit-slot bound. The separately reviewed Public4293.low_slots_impossible then closes the case. There is no residual-code/cardinality assumption left undisclosed; StrictLive, exact computation, Bzero=0, Bplus=11 and exact mask4293 remain explicit.

Source scans pass the prohibited-marker/string/attribute rules and scoped-limit syntax. Both sources are auxiliary dependency tests requiring inlining for the final file. The public helper's original proof attribution remains in Public4293 and its separate review.
