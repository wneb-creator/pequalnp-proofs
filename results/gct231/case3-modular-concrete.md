# Checked case3 modular coprimality

The standalone 10,283-byte Lean file proves that the two exact integer radical polynomials of degrees 67 and 85 map to coprime polynomials over ZMod 11, and that both mapped degrees are preserved. It uses the checked coefficient-list API and an explicit coefficient-level Bezout identity. The build and axiom audit passed in 16.37 seconds with 4.34 GiB sampled peak RSS. Only propext, Classical.choice and Quot.sound were reported.

The exact checked source SHA256 is 068e69749d812de901748856d3b1a322b22ba0256005b4b70464be5c0f1aea2c. All complete outputs are preserved. The generation log predates a small proof-only cast correction; the manifest identifies the final checked source and the current corrected generator.

This component is coprimality with degree preservation. It does not by itself assert the original six-equation system is impossible, the full case3 norm implication, or the posted gap theorem. The generic modular-resultant transfer is separately checked and preserved. The full norm wrapper is being checked separately.
