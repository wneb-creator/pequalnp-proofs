Exact necessary-resultant classification of open C4 case 2

Scope: this is an exact rational CAS derivation from the separately reviewed six-equation reduced case-2 system. It is not a Lean theorem, a formal geometry reduction, or a full-gap result. Independent chain review is pending at freeze time.

The variables are P,B,U,V,sat. The saturation equation implies P,B,detW are nonzero. The scale equation F obeys F=(P^2+P-1)(-6B^2+(5P^2-P+10)B-8P^2)-3PB, so K=P^2+P-1 is also nonzero.

Reduce equations as polynomials in B modulo F over QQ(P,U,V), clear denominators, and remove only factors supported on P*B*K*detW. Affine normalR permits resultants eliminating U, then V. Taking norms along F and a univariate gcd gives (P+2)^2 Q^22 R13^4 up to a nonzero scalar, with Q=P^4-2P^3+4P+2. Repeating in the reverse variable order and taking one additional norm removes R13, leaving (P+2)^2 Q^22. Resultants and norms are only used as necessary equations; no leading-coefficient division is used.

The Q=0 branch must retain the original B-linear resultant; its polynomial remainder is a(P)*(3B+P^3-2P^2) modulo Q, and a has an explicit Bezout inverse modulo Q. The exact identity then gives detW=P^2*Q after substituting B=(2P^2-P^3)/3. Thus this branch contradicts the chart's detW nonzero condition. The finish JSON stores and the finish script checks those polynomial identities. This avoids the incorrect inference from a vanishing norm alone to the actual branch's detW=0.

Hence P=-2. F=-2(B-1)(3B-16). Direct exactQQ Groebner computations on the remaining small equations give [1] at B=16/3, and [U,V-6,26sat+1] at B=1. Thus the original six-equation system has only P=-2,B=1,U=0,V=6,sat=-1/26. The separately reviewed square condition excludes that point; it is not duplicated here.

Every substantial symbolic job had a 512 MiB address-space cap and 60 or90 second wall cap, with complete stdout/stderr and run metadata retained. The final two small branch checks took under2 seconds. The failed folder records an initial factor-of3 typo in a debug assertion; the corrected exact identity is detW=P^2*Q, and the corrected finish script passes.
