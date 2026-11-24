# Slack-one finite-check splitting diagnostics

These are native/Python scheduling diagnostics, not Lean proofs. Sources use the same414pairs and phase convention as the signed-slack package. Run `python3 compute_slack_orbits.py`, `python3 slack_one_child_costs.py`, and `python3 slack_one_grandchild_costs.py` to regenerate outputs.

The154 possible first phase outputs split into23 graph-automorphism orbits:20 proper nonraw orbits,2 raw-input orbits, and1constant orbit. All members of an orbit have identical measured no-memo call/trial counts. Correct transport must account for raw phase orientation changing under input permutation. No formal orbit-transport theorem is supplied here.

For the concrete initial first output phase(raw0 AND raw1), the slack-one depth4 search has3,277valid no-memo calls and483,776candidate trials. Its coverage-surviving immediate successors comprise160ordered moves but78 distinct phase-multiset states. Sixty-seven distinct children cost at most28validcalls; ten cost129..181; the remaining duplicate-computed-signal child costs841. The latter splits into82ordered moves/19 distinct tight grandchildren:18 cost5..28calls, one106. JSON records exact signal values, move parameters, and subtree costs.

The cost recurrence memoizes returned subtree counts but sums those counts on every use, so the reported totals are no-memo search costs. The child graph uses sorted phase multisets only for diagnostic deduplication; formal reuse must prove the required permutation relation. No branch was excluded on timing evidence.

## All24 pair/sign scheduling table

`python3 slack_all_case_costs.py` reproduces all24 cases for the6 graph pair representatives(0,1),(0,2),(0,3),(0,4),(0,6),(4,6). Each sign is a2-bit mask on ORIGINAL raw inputs: bit1 complements the first, bit0 the second. The initial list is g::raw.map phase. Raw0 andraw4 require complementation for the canonical phase; other raw phases do not. To convert normalized-operand operation index to this sign, XOR the normalized index with2*phaseBit(first)+phaseBit(second).

The24cases sum29,233valid recursive calls. All retention child subtrees cost≤28; only21consume rows exceed60calls, with maximum181. The JSON table records all coverage-surviving consume/retain indices and duplicate costs. Unordered pair order is lexicographic on original list positions; each pair has4 operations ordered00,01,10,11. Retention index then multiplies by2, appending keep-first=0/keep-second=1.

For normalized pair(0,2),u0 (actual sign2), consume43 has119calls. Its next split has17distinct covered grandchildren, all≤23calls. For each of the10 duplicate branches, the220-child tight split has maximum grandchild cost[23,10,17,10,17,7,8,8,17,10]; no grandchild exceeds60. These are scheduling facts only; all formal finite exclusions remain the responsibility of the Lean proof files.
