# Correction: the eight-vertex core already has an accepted lower bound

On 2026-11-25, after the bounded searches, a repository search identified accepted `L_meta_1007` and `L_meta_2036`. They exclude every circuit of at most12 gates in the repository's more general `FanInTwo` model for a graph isomorphic to our eight-vertex Petersen adjacent-deletion core. `L_meta_1003` supplies a13-gate upper bound.

Our vertex labels map to the accepted theorem's labels by `[0,1,5,6,3,4,2,7]`. Applying that permutation maps all ten edges exactly. The relevant final declarations are at `lean/PEqualNP/Outside/L_meta_1007.lean:3588`, `L_meta_2036.lean:3749`, and `L_meta_1003.lean:616`.

The completed at-most12 SAT searches honestly returned UNKNOWN. They were redundant given this previously accepted lower bound, and should not be repeated as counterexample searches. Their logs and scope statements remain unchanged historical evidence.

A nonstar13-gate circuit on this core would now be a useful diagnostic against the stronger claim that every minimum circuit has a star profile, because the13-gate minimum is already known. It would still not refute L-meta-2448: a13-gate star construction exists, and the posted statement requires only one minimum circuit with a star profile. The completed nonstar-prefix13 search also returned UNKNOWN.
