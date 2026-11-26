import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- One bit of a wire's natural number records its value in one test row.
-- There are nineteen positive rows followed by forty negative rows.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_4243_26
  (synthesis : let s : List ℕ := [1095216333825, 192910783291068426, 1116226786697296, 116195354822066564, 34969968327559712, 306842908986703879, 360288554305191992, 459367987200131264, 433190953444967168, 541419321021172736, 383549969011838976, 573092725669240832, 460265395329187840, 541488584885043200, 575333752885018624, 575334852396974080]
    ∃ d : List ℕ, d.length = 22 ∧ d.getD 21 0 = 524287 ∧
      ∀ j < d.length, ∃ a b : ℕ, a < s.length + j ∧ b < s.length + j ∧
        (d.getD j 0 = ((s ++ d).getD a 0 &&& (s ++ d).getD b 0) ∨
         d.getD j 0 = ((s ++ d).getD a 0 ||| (s ++ d).getD b 0)))
  (realize : ∀ (s d : List ℕ) (q : ℕ),
      (∀ j < d.length, ∃ a b : ℕ, a < s.length + j ∧ b < s.length + j ∧
        (d.getD j 0 = ((s ++ d).getD a 0 &&& (s ++ d).getD b 0) ∨
         d.getD j 0 = ((s ++ d).getD a 0 ||| (s ++ d).getD b 0))) →
      ∃ C : Circuit, Monotone2 C ∧ ReadsBack s.length C ∧ C.size = d.length ∧
        ∀ k, circuitFun s.length C (fun i => (s.getD i.val 0).testBit k) =
          ((s ++ d).getD q 0).testBit k) :
∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     PEqualNP.MetaComplexity.NestedCover.ReadsBack (16 : ℕ) x1 ∧       x1.size ≤ (22 : ℕ) ∧         (∀ x2 ∈ [(33 : ℕ), (34 : ℕ), (40 : ℕ), (66 : ℕ), (68 : ℕ), (80 : ℕ), (132 : ℕ), (136 : ℕ), (264 : ℕ), (272 : ℕ), (513 : ℕ), (528 : ℕ), (1026 : ℕ), (2052 : ℕ), (4104 : ℕ), (8208 : ℕ), (16385 : ℕ), (32769 : ℕ), (32772 : ℕ)], (PEqualNP.MetaComplexity.circuitFun (16 : ℕ) x1 fun (x4 : Fin (16 : ℕ)) => x2.testBit ↑x4) = Bool.true) ∧           ∀             x2 ∈               have x3 : List ℕ :=                 have x3 : List ℕ :=                   have x3 : List ℕ := [(56496 : ℕ), (59914 : ℕ), (61000 : ℕ), (64386 : ℕ), (65504 : ℕ)];                   (30500 : ℕ) :: (34842 : ℕ) :: (49178 : ℕ) :: (52248 : ℕ) :: (55442 : ℕ) :: x3;                 have x4 : List ℕ := (20502 : ℕ) :: (21556 : ℕ) :: (24590 : ℕ) :: (26124 : ℕ) :: (29446 : ℕ) :: x3;                 (15809 : ℕ) :: (16414 : ℕ) :: (16910 : ℕ) :: (17436 : ℕ) :: (18458 : ℕ) :: x4;               have x4 : List ℕ :=                 have x4 : List ℕ := (10251 : ℕ) :: (11337 : ℕ) :: (12295 : ℕ) :: (13573 : ℕ) :: (14723 : ℕ) :: x3;                 (7313 : ℕ) :: (8207 : ℕ) :: (8455 : ℕ) :: (8718 : ℕ) :: (9229 : ℕ) :: x4;               have x5 : List ℕ := (4119 : ℕ) :: (4243 : ℕ) :: (4359 : ℕ) :: (5141 : ℕ) :: (6163 : ℕ) :: x4;               (31 : ℕ) :: (1053 : ℕ) :: (2075 : ℕ) :: (2195 : ℕ) :: (3097 : ℕ) :: x5,             (PEqualNP.MetaComplexity.circuitFun (16 : ℕ) x1 fun (x4 : Fin (16 : ℕ)) => x2.testBit ↑x4) = Bool.false := by
  let s : List ℕ := [1095216333825, 192910783291068426, 1116226786697296, 116195354822066564, 34969968327559712, 306842908986703879, 360288554305191992, 459367987200131264, 433190953444967168, 541419321021172736, 383549969011838976, 573092725669240832, 460265395329187840, 541488584885043200, 575333752885018624, 575334852396974080]
  let pos : List ℕ := [33, 34, 40, 66, 68, 80, 132, 136, 264, 272, 513, 528, 1026, 2052, 4104, 8208, 16385, 32769, 32772]
  let neg : List ℕ := [31, 1053, 2075, 2195, 3097, 4119, 4243, 4359, 5141, 6163, 7313, 8207, 8455, 8718, 9229, 10251, 11337, 12295, 13573, 14723, 15809, 16414, 16910, 17436, 18458, 20502, 21556, 24590, 26124, 29446, 30500, 34842, 49178, 52248, 55442, 56496, 59914, 61000, 64386, 65504]
  obtain ⟨d, hlen, target, trace⟩ := synthesis
  obtain ⟨C, mono, back, sz, ev⟩ := realize s d 37 trace
  have output : (s ++ d).getD 37 0 = 524287 := by
    rw [List.getD_append_right s d 0 37 (by decide)]
    exact target
  have positive : ∀ j : Fin 19,
      (524287 : ℕ).testBit j.val = true ∧
      ∀ i : Fin 16, (s.getD i.val 0).testBit j.val = (pos.getD j.val 0).testBit i.val := by
    decide +kernel
  have negative : ∀ j : Fin 40,
      (524287 : ℕ).testBit (19 + j.val) = false ∧
      ∀ i : Fin 16, (s.getD i.val 0).testBit (19 + j.val) = (neg.getD j.val 0).testBit i.val := by
    decide +kernel
  refine ⟨C, mono, back, by omega, ?_, ?_⟩
  · intro row hrow
    change row ∈ pos at hrow
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hrow
    let J : Fin 19 := ⟨j, hj⟩
    have bits := (positive J).2
    change ∀ i : Fin 16, (s.getD i.val 0).testBit j = (pos.getD j 0).testBit i.val at bits
    rw [List.getD_eq_getElem _ _ hj] at bits
    have hEval := ev j
    change circuitFun 16 C (fun i => (s.getD i.val 0).testBit j) =
      ((s ++ d).getD 37 0).testBit j at hEval
    rw [funext bits, output] at hEval
    exact hEval.trans (positive J).1
  · intro row hrow
    change row ∈ neg at hrow
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hrow
    let J : Fin 40 := ⟨j, hj⟩
    have bits := (negative J).2
    change ∀ i : Fin 16, (s.getD i.val 0).testBit (19 + j) =
      (neg.getD j 0).testBit i.val at bits
    rw [List.getD_eq_getElem _ _ hj] at bits
    have hEval := ev (19 + j)
    change circuitFun 16 C (fun i => (s.getD i.val 0).testBit (19 + j)) =
      ((s ++ d).getD 37 0).testBit (19 + j) at hEval
    rw [funext bits, output] at hEval
    exact hEval.trans (negative J).1
