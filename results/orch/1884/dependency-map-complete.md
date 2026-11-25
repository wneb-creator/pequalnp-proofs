# L-meta-1884 checked reduction closure

Checked at 2026-11-25T16:45:23.843155+00:00. Source: repository proof declarations and public static lemma metadata. Fresh FETCH_HEAD e125f04 additions were scanned: no new full Petersen18 bound.

## R_meta_1884_1

| Hypothesis | Exact step | Status |
|---|---|---|
| h_p10_18, ordinary Petersen has no size18 circuit | L-meta-4031 | OPEN |
| h_pv_15, vertex-deleted Petersen has no size15 circuit | L-meta-4033, also L-meta-670 | CHECKED |
| h_only10, no0readers and at most2 free-negative-input readers | L-meta-4035 | OPEN |
| h_both010, one positive OR reader and one negative AND reader | L-meta-4037 | OPEN |

## Recursive closure

- R4031_23: L670/L4033 checked, L9206 OPEN. L9206 says a least ordinary Petersen circuit of size at most18 has an input with at least3 affected gates when set false: direct effective readers, plus readers of its direct AND/NOT readers. This is the gate-elimination route.
- R4031_1: L9037 CHECKED input-output case; L9039 CHECKED all gate operands original-input case; L9041 OPEN remaining case. The hard leaf is essentially full original circuit problem.
- R4035_452: L7312 CHECKED rising-NOT trace, L7314 CHECKED normalization, L4031 OPEN ordinary bound, L7316 OPEN exact-size18/output28 core. Core has no original0 readers, no NOT reader of free input10, at most2 readers of10, and a rising-NOT trace on the edge01 restriction.
- R4035_1: L4031 OPEN, L6474 OPEN one binary reader of10, L6476 OPEN two binary readers of10.
- R4035_534: L8269 CHECKED each of8 six-variable restrictions has at least16 distinct wire truth columns; L8271 OPEN filtered circuit impossibility using those8 column bounds.
- R4037_1: L6146 OPEN unique OR reader of0 impossible; L6148 OPEN unique AND reader of10 impossible. Its proof uses L6146 alone to close the result.
- R1884_412: L6081 CHECKED robust pivotality; L6083 OPEN monotone/autoinvariant/robust-pivotal core disagreement on masks3,50,116.
- R1884_773: relabel is CHECKED stronger L7338 (arbitrary suffix); unary-function normalization has no located posted child; exact free-NOT18 core OPEN/unlocated.

Public search index has no further descendants of these open leaves. Searches can miss unindexed newer reductions, but local and FETCH_HEAD filenames contain no solved versions of the remaining exact leaves.

## Strong reusable components

- L670/L4033 complete vertex-deleted16 lower bound (6.5k lines), by mono/signed finite truth-table certificates and constant propagation.
- L8269 restriction-column16 lower bound, finite truth-table certificates.
- L7312/L7314 directly discharge R4035_452 helper premises.
- L7338 arbitrary input relabel preserving size and arbitrary suffix.
- L7340 bounds all wire indices preserving semantics (not unary normalization).
- L8241 eliminates constant/equal-earlier wires after a9variable restriction; D.size+K.card <= C.size+1, extra1 pays the remaining free negative literal.
- L4725/L6194 ordinary Petersen requires at least15 non-NOT gates.
- L9818 Petersen minus edges01,12 requires17 gates.
- L3087 normalized essential10input graph occurrence count: 9 + NOTcount + excess fanout <= size.

## Monotone lower-bound search

Among all712 locally checked proof IDs indexed under Petersen, no genuine full monotone Petersen19/20 lower bound appeared. L584/L587/L1755 are size20 upper bounds. L8021 is vacuous: assumptions include no NOT gates AND positive NOT count. No one-NOT purification theorem located.

## Constant propagation code already available

R1884_1 lines37-99 symbolic evaluator and gate simplification; lines138-242 gate correctness; lines243-305 constant gate simplification; lines306-459 elimRun_inv proves exact erased-count, FanInTwo, bounds, semantics; lines460-537 per-gate erasure flags; lines538-599 two/three erasures; lines607-649 ordinary-circuit contradiction helper.

R4031_23 lines38-54 simplify definitions,55-138 semantic/local lemmas,139ff elimStep and invariant. Its mathematical input is exactly unresolvedL9206 above.
