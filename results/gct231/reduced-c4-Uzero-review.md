# Conditional U=0 classification and U-saturation input review

Under the additional hypothesis U=0, each of the six-equation reduced C4 systems has exactly its previously displayed rational solution. Independent direct multiplication verifies the saved Bezout identities, and every branch excluded below uses a nonzero scalar or the existing saturation equation.

For case 2, the two equations linear in B have Sylvester determinant `−3 V²(V−6)²(V+2)`. The branch V=0 forces B=0, contradicting saturation. The branch V=−2 forces B=1/3 and the saved Bezout combination of equations 2 and 4 equals 1. The remaining V=6 forces B=1; the saved combination of equations 2 and 3 equals P+2. Hence P=−2, and saturation gives sat=−1/26.

For case 3, V=0 forces A=0 and contradicts saturation. With zero-based equation numbering, `e1+2e0 = −6 V²(2 beta−1)²`, so beta=1/2. Then equation 2 is `−(A−4)(4A−3)/8`, while saturation is `A(4A−3)sat/4−1`. Thus A=4. Equation 3 becomes `169(V+12)/8`, forcing V=−12, and saturation gives sat=1/13. Direct substitution verifies all six original equations at each final point.

These steps do not prove U=0 for arbitrary solutions. The independent checker and full log are `/tmp/oec/pequalnp-pilot-75/gct231/reduced_c4_Uzero_review.py` and `reduced-c4-Uzero-review.log`, completed 2026-11-25T11:39:06.938349+00:00. The author's initial assertion failure was a comparison of equivalent factored expressions; its corrected log and saved polynomial identities pass the independent expansion checks.

The separate U-nonzero auxiliary inputs preserve the original six equation strings and variable order exactly and append the variable invU and equation `invU*U−1`. Both QQ and F1009 sparse conversions were checked coefficient by coefficient, including hashes, normalized lineage, primitive scaling, exponents, and modular reduction. Each has six variables and seven equations: 136 terms in case 2 and 134 in case 3. The source JSON hashes are `aaa912a4c745e97e084be80a028287e31e67c77e768856ba602bb7fd4237d17c` and `aabaf7dda448f177fcb94706ebe8a6a3c1b678e5ccc900e3d76f18c54dedf1fc`.

Over C, every original solution with U nonzero lifts uniquely by invU=1/U. Consequently a characteristic-zero unit certificate for the auxiliary system would establish U=0 for the original reduced system. No such solver verdict is asserted here. Source and complete log: `reduced_c4_Usaturation_review.py` and `reduced-c4-Usaturation-review.log` in the same scratch directory, completed 2026-11-25T11:39:49.717110+00:00. No solver or compiler was run by these reviews.
