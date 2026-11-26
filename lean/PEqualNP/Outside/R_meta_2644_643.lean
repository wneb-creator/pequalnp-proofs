import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_2644_643
    (h1 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack 16 C ∧ C.size ≤ 22 ∧
      (∀ m ∈ ([33, 34, 40, 66, 68, 80, 132, 136, 264, 272, 513, 528,
       1026, 2052, 4104, 8208, 16385, 32769, 32772] : List ℕ),
        PEqualNP.MetaComplexity.circuitFun 16 C (fun i => m.testBit i.val) = true) ∧
      (∀ m ∈ ([31, 1053, 2075, 2195, 3097, 4119, 4243, 4359, 5141, 6163, 7313, 8207,
       8455, 8718, 9229, 10251, 11337, 12295, 13573, 14723, 15809, 16414, 16910, 17436,
       18458, 20502, 21556, 24590, 26124, 29446, 30500, 34842, 49178, 52248, 55442, 56496,
       59914, 61000, 64386, 65504] : List ℕ),
        PEqualNP.MetaComplexity.circuitFun 16 C (fun i => m.testBit i.val) = false))
    (h2 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack 16 C →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 D ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack 17 D ∧ D.size ≤ C.size + 1 ∧
        ∀ x : Fin 17 → Bool,
          PEqualNP.MetaComplexity.circuitFun 17 D x =
          PEqualNP.MetaComplexity.circuitFun 16 C (fun i =>
            if i.val = 10 then x 10 || x 15
            else x (Fin.ofNat 17 (if i.val < 15 then i.val else i.val + 1)))) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     PEqualNP.MetaComplexity.NestedCover.ReadsBack (17 : ℕ) x1 ∧       x1.size ≤ (23 : ℕ) ∧         (∀ x2 ∈ [(33 : ℕ), (513 : ℕ), (16385 : ℕ), (65537 : ℕ), (34 : ℕ), (66 : ℕ), (1026 : ℕ), (32770 : ℕ), (68 : ℕ), (132 : ℕ), (2052 : ℕ), (65540 : ℕ), (40 : ℕ), (136 : ℕ), (264 : ℕ), (4104 : ℕ), (80 : ℕ), (272 : ℕ), (528 : ℕ), (8208 : ℕ)], (PEqualNP.MetaComplexity.circuitFun (17 : ℕ) x1 fun (x4 : Fin (17 : ℕ)) => x2.testBit ↑x4) = Bool.true) ∧           ∀             x2 ∈               have x3 : List ℕ :=                 have x3 : List ℕ :=                   have x3 : List ℕ := [(92682 : ℕ), (97154 : ℕ), (117784 : ℕ), (122032 : ℕ), (126536 : ℕ), (131040 : ℕ)];                   (58892 : ℕ) :: (63268 : ℕ) :: (67610 : ℕ) :: (81946 : ℕ) :: (88210 : ℕ) :: x3;                 have x4 : List ℕ := (40973 : ℕ) :: (44105 : ℕ) :: (46341 : ℕ) :: (48577 : ℕ) :: (49180 : ℕ) :: (54324 : ℕ) :: x3;                 (29446 : ℕ) :: (33821 : ℕ) :: (34841 : ℕ) :: (36885 : ℕ) :: (40081 : ℕ) :: x4;               have x4 : List ℕ :=                 have x4 : List ℕ := (16414 : ℕ) :: (16910 : ℕ) :: (17436 : ℕ) :: (18458 : ℕ) :: (20502 : ℕ) :: (24590 : ℕ) :: x3;                 (8718 : ℕ) :: (9229 : ℕ) :: (10251 : ℕ) :: (12295 : ℕ) :: (14723 : ℕ) :: x4;               have x5 : List ℕ := (4243 : ℕ) :: (4359 : ℕ) :: (5141 : ℕ) :: (6163 : ℕ) :: (8207 : ℕ) :: (8455 : ℕ) :: x4;               (31 : ℕ) :: (2075 : ℕ) :: (2195 : ℕ) :: (3097 : ℕ) :: (4119 : ℕ) :: x5,             (PEqualNP.MetaComplexity.circuitFun (17 : ℕ) x1 fun (x4 : Fin (17 : ℕ)) => x2.testBit ↑x4) = Bool.false := by
  obtain ⟨C, hCmono, hCback, hCsize, hCpos, hCneg⟩ := h1
  obtain ⟨D, hDmono, hDback, hDsize, hEval⟩ := h2 C hCmono hCback
  let collapse (m : ℕ) : ℕ :=
    (m % 32768) ||| ((m / 65536) * 32768) ||| (if m.testBit 15 then 1024 else 0)
  let inputs (m : ℕ) (i : Fin 16) : Bool :=
    if i.val = 10 then m.testBit 10 || m.testBit 15
    else m.testBit ((Fin.ofNat 17 (if i.val < 15 then i.val else i.val + 1)).val)
  let positives : List ℕ := [33, 513, 16385, 65537, 34, 66, 1026, 32770, 68, 132, 2052, 65540,
       40, 136, 264, 4104, 80, 272, 528, 8208]
  let negatives : List ℕ := [31, 2075, 2195, 3097, 4119, 4243, 4359, 5141, 6163, 8207, 8455, 8718,
       9229, 10251, 12295, 14723, 16414, 16910, 17436, 18458, 20502, 24590, 29446, 33821,
       34841, 36885, 40081, 40973, 44105, 46341, 48577, 49180, 54324, 58892, 63268, 67610,
       81946, 88210, 92682, 97154, 117784, 122032, 126536, 131040]
  let smallerPositives : List ℕ := [33, 34, 40, 66, 68, 80, 132, 136, 264, 272, 513, 528,
       1026, 2052, 4104, 8208, 16385, 32769, 32772]
  let smallerNegatives : List ℕ := [31, 1053, 2075, 2195, 3097, 4119, 4243, 4359, 5141, 6163, 7313, 8207,
       8455, 8718, 9229, 10251, 11337, 12295, 13573, 14723, 15809, 16414, 16910, 17436,
       18458, 20502, 21556, 24590, 26124, 29446, 30500, 34842, 49178, 52248, 55442, 56496,
       59914, 61000, 64386, 65504]
  have bits : ∀ m ∈ positives ++ negatives, ∀ i : Fin 16,
      inputs m i = (collapse m).testBit i.val := by decide +kernel
  have posMasks : ∀ m ∈ positives,
      collapse m ∈ smallerPositives := by decide +kernel
  have negMasks : ∀ m ∈ negatives,
      collapse m ∈ smallerNegatives := by decide +kernel
  have evaluate (m : ℕ) (hm : m ∈ positives ++ negatives) :
      PEqualNP.MetaComplexity.circuitFun 17 D (fun i => m.testBit i.val) =
        PEqualNP.MetaComplexity.circuitFun 16 C (fun i => (collapse m).testBit i.val) :=
    (hEval (fun i => m.testBit i.val)).trans
      (congrArg (PEqualNP.MetaComplexity.circuitFun 16 C) (funext (bits m hm)))
  refine ⟨D, hDmono, hDback, by omega, ?_, ?_⟩
  · intro m hm
    exact (evaluate m (List.mem_append_left negatives hm)).trans (hCpos _ (posMasks _ hm))
  · intro m hm
    exact (evaluate m (List.mem_append_right positives hm)).trans (hCneg _ (negMasks _ hm))
