# L-meta-2448 research status

## Assignment and scope
- Assigned at07:03:52 UTC after the previous L-meta-1896 lease returned410 and all reviewed old-gap work was pushed. Root holds only the new lease and manages renewals, branch and submission.
- Posted target: every finite triangle-free/C4-free graph admits a globally minimum total-gate Monotone2 circuit computing its exact graph function and having HasStarProfile.
- The full target remains unproved and no valid refutation has been found. The three reduction slots are occupied. No PR has been opened.

## Replan 2026-11-25T07:22Z
- The named674-line partial combines checked minimum-circuit existence, the triangle-free equivalence between star ownership and no disjoint owned edges, and pair-soundness/dirty-pair obstruction lemmas. Named lake build passed12.52seconds; four key axiom audits use only propext, Classical.choice and Quot.sound.
- Actual tools/check-lean.mjs returned FAULT/exit3 before a verdict because its fullMathlib statement environment lacks Batteries.olean. This is separate from the still-unproved mathematical conclusion. Full logs and the partial are pushed at639f838c01b47aab349a426fa35d794e73ac1832.
- A119-line StarExistence component is also Lean checked: explicit star-profile DNF and a minimum only within the star-profile subclass. It is not yet merged into the named file. EdgePruning is a small separate check in progress after the transport recovery.
- Finite normalized-model results: C5star7 and C6star8 controls pass; C5six, C5nonstar7, C6seven and C6nonstar8 are UNSAT. C7nine timed out UNKNOWN. Both Petersen19 variants timed out UNKNOWN. These are computational evidence only; arbitrary-circuit normalization and UNSAT certificates are not Lean checked.
- P4 has a five-gate nonstar positive control, while a four-gate star circuit exists; this is not a counterexample to the minimum-existence claim. With fixed shared P4 OR interfaces, a small exhaustive search obstructs a too-local repair. The equal-cost private cleanup rewrite needs both relevant private blocks; it does not resolve arbitrary sharing.
- Next finite searches are theta(2,3,3) and theta(3,3,3) total-gate models, after independent dataset/control review. The theory work concentrates on the size-preserving cleanup/exchange step; no classical unrestricted normalization theorem has been established from the literature check.
- The exec transport briefly failed around07:19–07:20 and the environment was marked unavailable, then recovered. Files, the renewal timer and the current small solver survived. The final push639f was confirmed in its complete push log after recovery. No successful check is inferred from a failed tool launch.
- Fresh renewal07:21:34 UTC expires07:41:34 UTC. Seven sub-agents used cumulatively, including the prior completed child. Whole-job budget ends around08:43 UTC.

## Replan 2026-11-25T07:52:51.169722+00:00
- Consolidated1114-line named partial passed lake build in27.09s; all74 theorem/lemma declarations have only standard axioms. Actual official checker again returned FAULT/exit3, missing Batteries.olean. Full target remains unproved; no PR.
- Two-center pure-product semantic repair is checked, including arbitrary monotone cofactors. Its high-fanout cost argument is still an unformalized DAG argument and does not cover general nonlinear operands or low fanout.
- Star profile alone cannot strengthen an OR-only lower bound: input-AND copies enforce the profile while preserving ORcount, at the cost of extra ANDs. Accepted total-count bounds use stronger hypotheses on all accepted edges.
- The8-vertex Petersen deletion core at-most12 search ended UNKNOWN after300.026s. Petersen at-most19 continues to07:56:27. Next diagnostic is an independently reviewed earliest-exact-nonstar-prefix search, explicitly not a refutation by itself.
- Environment restarted briefly07:50; exact solver identities survived, detached shared-memory watchdog was restored, and renewal timer was restarted detached. Fresh renewal07:51:46 expires08:11:47.

## Final integration 2026-11-25T08:21:19.474551+00:00
- Named2341-line partial now passes lake build (20.56s); all174 declarations have standard axioms only. Actual checker again reports FAULT/exit3 missing Batteries.olean. The posted theorem is absent and unresolved.
- Checked concrete repair now discharges cofactor premises for actual AND operands. Under the pure two-center configuration its exact graph circuit obeys newsize+readers≤oldsize+3. TracedRepair separately couples size and strict sampled true-AND decrease in one repaired circuit under explicit repair/sample assumptions. No global minimum star-profile theorem follows yet.
- A reviewed graph isomorphism identifies the8vertex core with accepted L_meta_1007; its12gate impossibility was already known. Completed local UNKNOWNs add no lower bound.
- Accepted L584 has an exact20gate Petersen circuit with13OR+7AND and a nonstar owner. Its input-copy extension has30gates,13OR and star profile. Hence OR≥14 is false even with star profile absent a minimum-size requirement. This is not a refutation of2448.
- Last strengthened Petersen19 model uses accepted AND≥6 plus reviewed earliest-prefix substitution cuts; running under a detached guardian until about08:36:47. Limited local seed-deletion/two-edit searches have found no witness.

## Lease loss and closure 2026-11-25T08:34:42.205227+00:00
- The08:31:28 renewal returned410; the exactcurl-si retry returned the same full error. Last successful expiry had been08:42:51, so the cause is unknown. Root stopped its timer; no invalid release request or other pilot lease was touched.
- Main strengthened Petersen19 was stopped at08:32:44; wrapperexit-2 and explicit SIGINT evidence are preserved. It is interruptedUNKNOWN, not a completed20minute query and not a SAT/UNSAT verdict. Full final source/CNF/log archive is lossless and independently under review.
- All mathematical work stopped. The2341-line partial and all174-declaration audits are already pushed; unrestricted2448 remains unproved, no valid refutation orPR.

## Final desk recovery
- After every checked/interrupted result was pushed, request008 at2026-11-25T08:36:38.756963+00:00 returned no gap and no lease. Its exact note is archived in validation/desk-recovery-record.json. Six null responses occurred over this job. No new step was taken near the whole-job deadline; no owned lease or worker remains.
