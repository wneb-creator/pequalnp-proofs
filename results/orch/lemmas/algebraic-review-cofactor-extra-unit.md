Independent review by algebraic_route

PASS on structural-cofactor-extra-unit-tail.lean and structural-high-collinear-tail.lean.

The original cf_main construction and charged lost set are retained. The additional reserved unit is outside that set: residual units exclude all reserved units, and distinct eligible singleton supports make the reserved-wire assignment injective. If the extra unit is lost, inserting it increases the lost count by one. If kept, its free label remains in the cofactor singleton support, while ineligibility of that label in the cofactor triggers the previously reviewed strict-slack inequality. This correctly permits cofactor aliasing.

The collinear p11 application assumes Bzero >= 2, derives one residual unit carrying the common line, charges eight units, and invokes the checked K4 equality classification. A free eligible original point is outside the charged center/line set, producing the ninth unit and contradiction. The conclusion here is Bzero <= 1; the stronger zero claim is not reviewed in this report.

Cached compilation passed according to the author. Standalone builds remain required before preservation. New tails contain no forbidden trust or format markers.
