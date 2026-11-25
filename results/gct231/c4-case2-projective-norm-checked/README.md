Checked scalar implication from two explicit univariate norms

C4Case2ProjectiveNorm.lean proves that the two displayed norm equations imply P+2=0 or P^4-2P^3+4P+2=0. It does not establish that the original C4 chart hypotheses imply those equations, nor a C4-family or full-gap theorem.

The exact-source axiom driver compiled PASS in33.03seconds, peak5408160KiB under240seconds/6GiB sampledRSS, using only propext, Classical.choice, Quot.sound. Actual coefficients and Bezout identity were independently checked by a separate strict source parser and integer polynomial arithmetic. The proof has only Defs import and permitted scoped limits.

The earlier failed candidate had the same checked large polynomial identity but used nonexistent pow_eq_zero in the final two lines. The exact two-identifier change to eq_zero_of_pow_eq_zero was independently reviewed. Failed artifacts are kept separately and are not valid theorem results. The original frozen certificate/source review stays unchanged in ../c4-case2-projective-certificate/ and ../projective-norm-review/.
