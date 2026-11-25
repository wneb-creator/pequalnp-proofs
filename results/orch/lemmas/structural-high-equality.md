# High eligible-card equality cases

Accepted source: L_meta_6659.lean, SHA256 e856158208c582f389897b6941fd0cd675fe6e590fb09b4299b35b9c91a76a20, PR https://github.com/open-goat/pequalnp-proofs/pull/13206. Read2026-11-25. This artifact copies its first7824 lines, renaming only the enclosing namespace. Newtail is stored separately in structural-high-equality-tail.lean.

For a strictlive14-input DAG, ordinary size27 means totalSurplus=14. Write p=eligible-card and B=Bplus+Bzero.

Compiled consequences (Lean exit0; complete build2 stdout/stderr empty; independent review PASS by algebraic_route):
- p14: eligible-card≤Bplus forces Bzero0.
- p13, canonical ineligible{0}: tight_le excludes Bplus≤p, so Bplus≥14 and Bzero0.
- p12, canonical ineligible{0,1} or{0,9}: pa_setup and the two case proofs actually require only Bplus≤13. Their stronger total≤13 hypotheses were used only to derive this arithmetic bound. Generalizing those copies gives Bplus≥14, hence Bzero0 atB≤14.
- p11, canonical collinear ineligible{0,1,3}: unresolved. The attempted supported-budget generalization failed during Lean checking because cf_six concludes a bound involving totalSurplus, so its final arithmetic genuinely needs total≤13. That attempted theorem has been removed.
- p11, canonical noncollinear ineligible{0,1,2}: tri012 gives Bplus≥13, whence Bzero≤1. tri_hw then gives Bplus≥14, whence Bzero0.

Unresolved high case: p11 with canonical mixed ineligible{0,1,11}. Its accepted proof derives Bzero0 from total≤13 and then uses that semantic fact in the exact-mask argument. One cannot replace this assumption by Bplus≤13 throughout. At total14 the residual possibility Bplus13/Bzero1 remains; no exclusion is claimed.

These results alone do not refute doublequiet. Bzero0 only says that wires with empty singleton support cannot branch. Ineligible inputs then have single-reader chains to output (sem_inelig_reach and sem_bzero_branch), which excludes zero derivative in that input once the generic chain/derivative bridge is applied. A quiet incidence may still have two eligible endpoints, so no universal no-quiet conclusion follows.

Normalization caution: the accepted general normalization can collapse duplicate-input AND gates and change formal derivatives. For an already strict27-gate witness, ordinary minimality (acceptedFano≥27) prevents any size-decreasing function-preserving normalization. The separately compiled formalization-minimal-trace-bridge.lean now uses direct strict-DAG conversion and ordinary minimality to prove that the original output is last and every earlier wire has a reader. It preserves every wire value and derivative trace without modifying the original DAG. The explicit minimality and function hypotheses remain necessary.

New ordinary-minimality SAT cuts independently validated: atsize27, AND operands are incomparable on maximal-negative rows and OR operands on minimal-positive rows; everygate is false on some maximal-negative row. Replacement/deletion gives an ordinary≤26 Fano circuit if a cut fails, so trace preservation is not required for those contradictions. These are not general size28 restrictions.

Further compiled extension: structural-high-equality-next.lean retains accepted prefix8183 plus the reviewed high-case tail, then136newlines. Its p11 mixed supported-budget contradiction truncates the accepted proof before the Bzero0 step: Bplus≤12 forces residual-card≤1, while the geometric argument forces residual-card≠1 and at least1. Therefore Bplus≥13 and Bzero≤1 at totalSurplus≤14. This still leaves Bplus13/Bzero1 and does not establish no-quiet. Complete next-build logs are empty.
