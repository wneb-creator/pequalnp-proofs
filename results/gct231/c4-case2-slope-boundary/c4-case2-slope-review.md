Independent case2 nonzero-slope boundary review: PASS (2026-11-25T12:17:04Z).

For the actual reduced linear row r=aU+bV+c, the scale equation F=0 and P*B*W nonzero imply a nonzero or b nonzero. The premise r=0 is unnecessary. W is the recorded chart determinant numerator, K=P²+P−1 and Q=P⁴−2P³+4P+2.

The original row reduces to r/(8K³) modulo F. F=K[−6B²+(5P²−P+10)B−8P²]−3PB proves K nonzero. Independent quadratic/linear Sylvester identities verify norm(a)=256P⁴K³Q²R13 and norm(b)=64P³K³Q²S13. Explicit integer Bézout multipliers give 91612984850589100953600 from R13,S13, so simultaneous zero slopes force Q=0. Modulo Q, a=A(P)(3B+P³−2P²); explicit Bézout multipliers give 27406080 from A,Q. Thus 3B+P³−2P²=0. Finally W−P²Q=(3B−P³−4)(3B+P³−2P²), contradicting W nonzero.

These identities never divide by a slope or its leading coefficient. All source, norm, Bézout and affine determinant identities were independently expanded over QQ. No general chart classification or Lean verification is claimed here.

Scratch reproducer/log/certificates: `c4_case2_slope_review.py`, `c4-case2-slope-review.log`, `c4-case2-slope-review-certificates.json`. The first diagnostic log is retained: an assertion compared equivalent unexpanded Sympy expressions structurally; the final checker expands their difference to zero. Standalone `case2-necessity/Case2SlopeBoundary.lean` is generated but not yet compiled.

Review note saved 2026-11-25T12:19:39.017330+00:00.
