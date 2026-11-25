Job start: 2026-11-25T13:43:13Z
Lease issued: 2026-11-25T13:44:05.796Z
Lease initial expiry: 2026-11-25T14:04:05.796Z
2026-11-25T13:46:07.164782+00:00 beat 1
{
 "lease": {
  "id": "d30cd9f5-2ff3-41d8-b031-e33b731294ac",
  "expires_at": "2026-11-25T14:06:06.716Z",
  "renew": "POST /desk/beat?lease=d30cd9f5-2ff3-41d8-b031-e33b731294ac",
  "beat": "Renew every 5 minutes (POST the renew link). A 410 means stop: the step was withdrawn or proved.",
  "release": "POST /desk/release?lease=d30cd9f5-2ff3-41d8-b031-e33b731294ac&reason=<submitted|hypothesis_too_weak|missing_lemma|statement_seems_false|does_not_elaborate|exhausted|rechecked|recheck_failed|reduced|out_of_time|other>",
  "terms": {
   "kind": "prove",
   "level": "hard",
   "points": 250,
   "reductions_open": true,
   "issued_at": "2026-11-25T13:44:05.796Z"
  }
 },
 "next_beat_s": 300
}

2026-11-25T13:49:13.079401+00:00 beat 2
{
 "lease": {
  "id": "d30cd9f5-2ff3-41d8-b031-e33b731294ac",
  "expires_at": "2026-11-25T14:09:12.374Z",
  "renew": "POST /desk/beat?lease=d30cd9f5-2ff3-41d8-b031-e33b731294ac",
  "beat": "Renew every 5 minutes (POST the renew link). A 410 means stop: the step was withdrawn or proved.",
  "release": "POST /desk/release?lease=d30cd9f5-2ff3-41d8-b031-e33b731294ac&reason=<submitted|hypothesis_too_weak|missing_lemma|statement_seems_false|does_not_elaborate|exhausted|rechecked|recheck_failed|reduced|out_of_time|other>",
  "terms": {
   "kind": "prove",
   "level": "hard",
   "points": 250,
   "reductions_open": true,
   "issued_at": "2026-11-25T13:44:05.796Z"
  }
 },
 "next_beat_s": 300
}

2026-11-25T13:50:35.724651+00:00 Stopped globalSAT AND-edge shard after two60-second unknowns; replacing with local bounded-edit SAT around near-solution. OR-nonedge shard still running.
2026-11-25T13:51:38.762770+00:00 beat 3
{
 "lease": {
  "id": "d30cd9f5-2ff3-41d8-b031-e33b731294ac",
  "expires_at": "2026-11-25T14:11:38.324Z",
  "renew": "POST /desk/beat?lease=d30cd9f5-2ff3-41d8-b031-e33b731294ac",
  "beat": "Renew every 5 minutes (POST the renew link). A 410 means stop: the step was withdrawn or proved.",
  "release": "POST /desk/release?lease=d30cd9f5-2ff3-41d8-b031-e33b731294ac&reason=<submitted|hypothesis_too_weak|missing_lemma|statement_seems_false|does_not_elaborate|exhausted|rechecked|recheck_failed|reduced|out_of_time|other>",
  "terms": {
   "kind": "prove",
   "level": "hard",
   "points": 250,
   "reductions_open": true,
   "issued_at": "2026-11-25T13:44:05.796Z"
  }
 },
 "next_beat_s": 300
}

2026-11-25T13:53:09.838225+00:00 renewed; expiry 2026-11-25T14:13:10.039Z
2026-11-25T13:57:26.864486+00:00 structural automorphism and robust essentiality helper compiled successfully.
2026-11-25T13:57:40.248205+00:00 first compiled component: structural.lean, exit0; preparing early push.
2026-11-25T13:58:10.528541+00:00 renewed; expiry 2026-11-25T14:18:10.060Z
2026-11-25T13:58:41.151164+00:00 Stopped global ORnonedge SAT shard after9minutes ofunknown, replaced with≤5gate-edits search around4false-positive K4star seed; QF_FD engine andraw-input pair essentiality pruning.
2026-11-25T13:59:44.253116+00:00 local stochastic batch finished: 600s, 1667631432 candidates,66703 restarts; no witness. Paused CPU for Lean.
2026-11-25T14:03:11.038644+00:00 renewed; expiry 2026-11-25T14:23:10.715Z
2026-11-25T14:03:35.157057+00:00 bankfinite.lean compiled and independently reviewed; preparing early push.
2026-11-25T14:04:19.477369+00:00 reduction_design: canonical-bank finite certificate compiled; generalizedbank lower andLive-map drafted pendingmainolean.
2026-11-25T14:06:21.829802+00:00 named partial build PASSED (16 binary gates plus NOT count lower bound); preparing early push.
2026-11-25T14:06:35.436797+00:00 beat4 before cached proof extensions
{
 "lease": {
  "id": "d30cd9f5-2ff3-41d8-b031-e33b731294ac",
  "expires_at": "2026-11-25T14:26:34.659Z",
  "renew": "POST /desk/beat?lease=d30cd9f5-2ff3-41d8-b031-e33b731294ac",
  "beat": "Renew every 5 minutes (POST the renew link). A 410 means stop: the step was withdrawn or proved.",
  "release": "POST /desk/release?lease=d30cd9f5-2ff3-41d8-b031-e33b731294ac&reason=<submitted|hypothesis_too_weak|missing_lemma|statement_seems_false|does_not_elaborate|exhausted|rechecked|recheck_failed|reduced|out_of_time|other>",
  "terms": {
   "kind": "prove",
   "level": "hard",
   "points": 250,
   "reductions_open": true,
   "issued_at": "2026-11-25T13:44:05.796Z"
  }
 },
 "next_beat_s": 300
}

2026-11-25T14:07:26.136445+00:00 reduction_design: canonicalbank16andconjunction17 residualtheoremscompiled.
2026-11-25T14:07:39.560030+00:00 bank16.lean compiled and independently reviewed; preserving component.
2026-11-25T14:08:10.983519+00:00 local_near.lean compiled successfully; independent exhaustive truth-table and format review passed.
2026-11-25T14:08:11.460115+00:00 renewed; expiry 2026-11-25T14:28:11.151Z
2026-11-25T14:08:25.136227+00:00 local_near.lean compiled and independently reviewed; preserving exact near-witness.

- 2026-11-25T14:10:02.466402+00:00: structural transport (row permutation, Live preservation, canonical first-pair normalization) compiled PASS. Root and independent reviewer notified.
2026-11-25T14:10:55.558218+00:00 transport compiled/reviewed; preserving snapshot. Replan: retain17binary firstgate route, one-NOT analysis, exact15template SAT; drop generic duplicate-charge route (counterexamples).
2026-11-25T14:11:37.243155+00:00 deterministic two-edit neighborhood finished: all390 deletion/rewire seeds,1078288780 score evaluations, no witness.

- 2026-11-25T14:11:42.435120+00:00: canonical transport with used-extra membership compiled PASS; notified root, reviewer, integration agent.
2026-11-25T14:11:54.378058+00:00 beat5 before neutral-network search
{
 "lease": {
  "id": "d30cd9f5-2ff3-41d8-b031-e33b731294ac",
  "expires_at": "2026-11-25T14:31:53.751Z",
  "renew": "POST /desk/beat?lease=d30cd9f5-2ff3-41d8-b031-e33b731294ac",
  "beat": "Renew every 5 minutes (POST the renew link). A 410 means stop: the step was withdrawn or proved.",
  "release": "POST /desk/release?lease=d30cd9f5-2ff3-41d8-b031-e33b731294ac&reason=<submitted|hypothesis_too_weak|missing_lemma|statement_seems_false|does_not_elaborate|exhausted|rechecked|recheck_failed|reduced|out_of_time|other>",
  "terms": {
   "kind": "prove",
   "level": "hard",
   "points": 250,
   "reductions_open": true,
   "issued_at": "2026-11-25T13:44:05.796Z"
  }
 },
 "next_beat_s": 300
}

2026-11-25T14:12:08.035171+00:00 started900second neutral-network CGP search; exact20gate seed,32 internal slots, objective active gate count plus unusedNOT padding if needed.
2026-11-25T14:13:12.024210+00:00 renewed; expiry 2026-11-25T14:33:11.968Z

- 2026-11-25T14:14:15.490600+00:00 reduction_design: exact canonical residual-bank component compiled; independently reviewed PASS.
2026-11-25T14:15:02.955702+00:00 beat6 before integrated17bound build
{
 "lease": {
  "id": "d30cd9f5-2ff3-41d8-b031-e33b731294ac",
  "expires_at": "2026-11-25T14:35:02.366Z",
  "renew": "POST /desk/beat?lease=d30cd9f5-2ff3-41d8-b031-e33b731294ac",
  "beat": "Renew every 5 minutes (POST the renew link). A 410 means stop: the step was withdrawn or proved.",
  "release": "POST /desk/release?lease=d30cd9f5-2ff3-41d8-b031-e33b731294ac&reason=<submitted|hypothesis_too_weak|missing_lemma|statement_seems_false|does_not_elaborate|exhausted|rechecked|recheck_failed|reduced|out_of_time|other>",
  "terms": {
   "kind": "prove",
   "level": "hard",
   "points": 250,
   "reductions_open": true,
   "issued_at": "2026-11-25T13:44:05.796Z"
  }
 },
 "next_beat_s": 300
}

2026-11-25T14:13:13Z Completed15prefix18monotonegatecensus:15UNSAT,0unknown,0witness; restrictedcomputedresult.
2026-11-25T14:15:59.153297+00:00 preserving reviewed17integration and three checked components; full named rebuild running.
2026-11-25T14:18:12.441165+00:00 renewed; expiry 2026-11-25T14:38:12.202Z

- 2026-11-25T14:18:22.463815+00:00 reduction_design: integrated17 source review PASS; second-gate exploration stopped short of residual certificate.
2026-11-25T14:19:35.933229+00:00 local_projection.lean compiled and independently reviewed: nonedge alias x0=not x2 has15 total gates,14 binary,1 NOT; proposed projection bound false.
2026-11-25T14:19:53.487345+00:00 checked nonedge-projection witness preserved; projection lower-bound route dropped.
2026-11-25T14:21:19.487905+00:00 frozen computational archives independently audited; preserving scripts and complete logs.
2026-11-25T14:23:12.754557+00:00 renewed; expiry 2026-11-25T14:43:12.835Z
2026-11-25T14:28:06.166089+00:00 neutral-network900second run finished,1996365633 evaluations,no improvement of exact20gate baseline.
2026-11-25T14:28:13.344196+00:00 renewed; expiry 2026-11-25T14:48:13.407Z
2026-11-25T14:28:56.047445+00:00 started300second local C6 search with3 fixed opposite-OR gates plus7 unknown gates; root renewal14:28:13Z.
2026-11-25T14:30:35.338584+00:00 full integrated17bound build PASSED; cached target artifacts backed up before further edits.
