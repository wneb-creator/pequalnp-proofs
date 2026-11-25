# K4 equality obstruction (mathematical review, not Lean-certified)

Accepted proof PR: https://github.com/open-goat/pequalnp-proofs/pull/13206 (read2026-11-25). The Lean partial copies the first5,086 source lines, renames their enclosing namespace, and adds85 new lines.

Accepted source reviewed: /tmp/oec/pequalnp-pilot-81/status-L_meta_6659.lean, lines4703–5086, plus sem_dom_pure and semantic carrier lemmas.

For a strict live 10-input circuit computing the subdivided K4 with at most15 gates, totalSurplus = gates-inputs+1 ≤6. k4_surplus_six forces Bplus=6,totalSurplus=6,Bzero=0. Eligible labels form a vertex cover and have size≤6. k4_surplus_seven_matching excludes each perfectmatching pair {4,9},{5,8},{6,7} from the ineligible set.

Finite enumeration leaves exactly these five eligible covers, all of size6:
- {0,1,2,6,8,9}
- {0,1,3,5,7,9}
- {0,2,3,4,7,8}
- {1,2,3,4,5,6}
- {4,5,6,7,8,9}

Each mixed cover has an eligible original vertex with two ineligible subdivided-edge neighbors and a third neighbor. k4_three_cons gives at least3 exits from its singleton carrier. k4_budget with T={that vertex}, Bplus=eligibleCard=6 gives exits+merges≤2, contradiction. Therefore exactly the6 subdivided-edge labels are eligible; every original vertex is ineligible.

Generic further deduction: if v is ineligible and Bzero=0, no branching wire can be reached from inputv. Pick the first branch on a reader path; all earlier wires form a single-reader chain, so the branch dominatesv. sem_dom_pure implies its singleton support is contained in {v}. If its support containsv, v is eligible. Otherwise it has empty support, contradicting Bzero=0. Therefore v has a single-reader chain to output. Off-chain operands cannot depend syntactically onv, so the Boolean formal derivative wrtv is the ordinary Boolean change when flippingv; at every neighbor singleton it is true.

Consequently a strictlive cap15 circuit cannot have doublequiet on any incidence. This deduction still needs a formal derivative/path bridge and preservation under normalization of the proposed14-input formulation. It is a serious blocker to submitting cap15 quiet as a supposedly plausible reduction hypothesis.

Caution: Bzero=0 alone does NOT exclude quiet; duplicated gates (a AND b), (a AND b), then theirAND are a counterexample, with distinct top operands and no empty-support fanout. The ineligible-label condition is essential.

First compile attempt checked the accepted prefix but rejected the large finite equality proposition at Decidable-instance synthesis. The certificate was split into five explicit eligible-cover cases, then four explicit neighbor triples. Attempt1 full logs are preserved; second build completed exit0 with empty stdout/stderr. Frozen SHA2563042fc014905e95c489e834d85dfb8341b63b50cb5abc326199731dff1e58316 (5,171lines).

2026-11-25T10:42:34.117253+00:00 — Certified k4_equality_eligible, k4_equality_zero and k4_equality_chain. The final theorem proves a unique reader chain for every original point of a strictlive10-input K4 circuit with≤15gates. A separate derivative bridge is being prepared by lean_setup. No arbitrary14-input quiet-normalization claim is made.
