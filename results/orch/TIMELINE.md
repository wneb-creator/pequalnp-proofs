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
