Read-only upstream census completed 2026-11-25T14:40:16.684180+00:00.
Source commit: `425600fa58bc89d80594a4b29a984f54f58c8557`. Previous base: `db2dab2963890e3c6dd90c6e43283828946976c6`.

Inspected exactly the 192 added/changed Outside Lean paths listed in `/tmp/oec/pequalnp-pilot-108/upstream-added-002.txt`, using git show against the immutable source commit. No merge, reset, build, or Lean source changes. All 192 final named theorem statements were extracted; 23 files also matched nine/ten-input or Petersen text and their helper theorem statements were indexed.

Result: no new final theorem proves the full Petersen ten-input monotone bound of 19/20, a nine-vertex Petersen NOT premium of 17, or the one/two-NOT nineteen-gate exclusion. Seven new nine-input final statements assert ordinary total-gate bounds of 14, 15, or 16 on different graphs. Their edge counts/degrees rule out equality with the twelve-edge Petersen-minus-vertex graph under a permutation. The only new final statement mentioning any of 18/19/20 is L_meta_9734, a different twelve-input Heawood deletion graph. This census does not rule out a useful equivalent formulation among generic helper lemmas. No new proof was compiled in this census.

Exact nine-input theorem statements (source SHA above applies to every path):

Path: `lean/PEqualNP/Outside/L_meta_10520.lean`, line 7276. SHA256 `b348033da3f218624b1e4cefd37ade8639ec6590acc93f74289eb6275710bdb6`.
Computed edge count 10; sorted vertex degrees [1, 2, 2, 2, 2, 2, 3, 3, 3].
```lean
theorem PEqualNP.Outside.L_meta_10520 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 0 && x 8) || (x 3 && x 8) || (x 5 && x 8)) t → 14 ≤ t
```

Path: `lean/PEqualNP/Outside/L_meta_10666.lean`, line 3794. SHA256 `b623d3e61039588854bdf5d099bb0b56bfa94a7b45b2feb9c79e60cf9eb44045`.
Computed edge count 11; sorted vertex degrees [2, 2, 2, 2, 2, 2, 3, 3, 4].
```lean
theorem PEqualNP.Outside.L_meta_10666 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 4 && x 8) || (x 5 && x 8)) t → 14 ≤ t
```

Path: `lean/PEqualNP/Outside/L_meta_10832.lean`, line 6792. SHA256 `9e103d34d522f3fb215b4008afa70e72560e99b3fd557e6f0d3287c22dc5eb7c`.
Computed edge count 11; sorted vertex degrees [1, 2, 2, 2, 3, 3, 3, 3, 3].
```lean
theorem PEqualNP.Outside.L_meta_10832 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 5 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 4 && x 8)) t → 15 ≤ t
```

Path: `lean/PEqualNP/Outside/L_meta_10934.lean`, line 3782. SHA256 `d45a2e62cb40d274a84f7e3c0a1a47377f76100213f71c4fb0fe9720bff4c3a5`.
Computed edge count 11; sorted vertex degrees [1, 2, 2, 2, 2, 3, 3, 3, 4].
```lean
theorem PEqualNP.Outside.L_meta_10934 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 6 && x 8)) t → 15 ≤ t
```

Path: `lean/PEqualNP/Outside/L_meta_10976.lean`, line 4837. SHA256 `d62d466f74e2ac1449c2834aae86c3efbc5d787f901aff3f8b4e279c91277d9d`.
Computed edge count 11; sorted vertex degrees [1, 1, 2, 2, 2, 2, 3, 4, 5].
```lean
theorem PEqualNP.Outside.L_meta_10976 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 6 && x 8) || (x 7 && x 8)) t → 15 ≤ t
```

Path: `lean/PEqualNP/Outside/L_meta_10980.lean`, line 8588. SHA256 `209668ee1101451629b2358cacbb48617d91a98c634c2d4472548c35ca80c342`.
Computed edge count 11; sorted vertex degrees [1, 1, 2, 2, 2, 2, 3, 3, 6].
```lean
theorem PEqualNP.Outside.L_meta_10980 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 0 && x 8) || (x 1 && x 8) || (x 2 && x 8) || (x 5 && x 8) || (x 6 && x 8) || (x 7 && x 8)) t → 15 ≤ t
```

Path: `lean/PEqualNP/Outside/L_meta_11042.lean`, line 5107. SHA256 `ce5143fd997fc221a96296f2dacb507b26780bdf9ab454fd151b0f3be9afa69d`.
Computed edge count 12; sorted vertex degrees [2, 2, 2, 2, 2, 2, 2, 4, 6].
```lean
theorem PEqualNP.Outside.L_meta_11042 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 6 && x 8) || (x 7 && x 8)) t → 16 ≤ t
```

Related monotone theorem; not the Petersen graph:
Path: `lean/PEqualNP/Outside/L_meta_9734.lean`, line 8919. SHA256 `932d9454be4ac831f1d4ce1fae86a95a8f48ff30412d9cc26abc1ed99334d6ce`.
```lean
theorem PEqualNP.Outside.L_meta_9734 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 18 ∧ (∀ x : Fin 12 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 12, (u.val, v.val) ∈ ([(0, 6), (0, 10), (0, 11), (1, 5), (1, 9), (1, 10), (2, 8), (2, 9), (2, 11), (3, 7), (3, 8), (3, 10), (4, 6), (4, 7), (4, 9)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)))
```

Its internal heawood_lb_27 proves a 27-gate monotone lower bound on fourteen inputs. Ten-input helper statements in that file concern the subdivided K4 graph, not Petersen. L_meta_10520 also contains generic ten-input deletion/shape lemmas with small 13/12/11 gate hypotheses; they do not supply the requested Petersen threshold. Several seven-input one-NOT elimination proofs copy the signed nine-input certificate infrastructure already under extraction, but their final statements remain seven-input graph-specific.

Complete git show stdout/stderr and return codes are preserved compressed in scratch `upstream-census-002-complete.json.gz`. Candidate/helper statements: `upstream-census-002-candidates.json`; all final named statements: `upstream-census-002-final-statements.json`; bounded ten-input helper extraction: `upstream-census-002-ten-statements.json`. These files were written before lease-expiry notification; no additional search was performed afterward.
