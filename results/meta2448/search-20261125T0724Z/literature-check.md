# Literature check, read 2026-11-25

Primary source: Stasys Jukna, [Disproving the Single Level Conjecture](https://web.vu.lt/mif/s.jukna/ftp/single1.pdf), SIAM Journal on Computing 36(1), 2006.

The abstract states that certain quadratic functions have small general circuits while “their monotone single level circuits require almost quadratic size.” Theorem2.1 uses saturated extensions, whose two vertex parts induce cliques. Those examples therefore do not directly satisfy2448's triangle-free hypothesis.

The paper's Problem8.2 asks for an explicit quadratic function requiring superlinear monotone circuit size. This is historical context, not a claim about its current2026 status. I found no directly applicable girth-five normalization theorem or counterexample in this paper. A general transformation to one AND level is false without graph restrictions; star ownership is also a different property from having one AND level.

UNVERIFIED: whether later literature resolves the exact girth-five minimum-star-profile assertion. The limited search did not establish this.

Additional primary references read 2026-11-25:

- Robert E. Tarjan, [Complexity of Monotone Networks for Computing Conjunctions](https://ftpmirror.your.org/pub/misc/bitsavers/pdf/stanford/Stanford_CS_TR_Collection_2025-12-12/OCR/CS-TR-76-553-ocr.pdf), Stanford report STAN-CS-76-553 (1976), printed pages16–17, Theorems7–8: the exact-linear/projective-plane multioutput bound. Printed pages11–12 give the17-versus18 mixed-operation example. These do not establish the single-output star-profile statement.
- Stasys Jukna, [Single Level Conjecture for Quadratic Functions and Graphs](https://web.vu.lt/mif/s.jukna/papers/single-dag5.pdf), slide14: a triangle/C4-free lower bound is explicitly a formula bound. The slides distinguish exact quadratic functions from their restrictions to weight-two inputs. Their file discovery timestamp is not evidence of a recent theorem.
- Kazuyuki Amano and Akira Maruoka, [The Monotone Circuit Complexity of Quadratic Boolean Functions](https://doi.org/10.1007/s00453-006-0073-0), Algorithmica46(1),2006,3–14: publisher abstract read, full paper not obtained. The abstract compares single-level and arbitrary circuits; it supplies no stated high-girth normalization.

Research boundary: academic pages above were read using the browser tool following the parent's latest primary-literature assignment; no shell fetches or external writes occurred. After a teammate flagged the earlier host restriction, further outside-host browsing stopped. None of these references is imported into Lean or used as an unproved premise.

Conclusion of this check: no verified theorem supplies the missing exchange. The claimed total-size formula remains UNVERIFIED, and failure to locate it is not evidence of falsity. The currently checked local lemmas must remain separate from a full2448 result.
