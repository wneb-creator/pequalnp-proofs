import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5112_42
    (h1 : ∃ gs : List (Bool × Fin 28 × Fin 28), gs.length = 14 ∧ (List.foldl (fun (xs : List Nat) (g : Bool × Fin 28 × Fin 28) => xs ++ [if g.1 = true then xs.getD g.2.1.val 0 ||| xs.getD g.2.2.val 0 else xs.getD g.2.1.val 0 &&& xs.getD g.2.2.val 0]) [251137, 817232, 3224100, 5542026, 11018243, 9060364, 12746800, 10682560, 13370112, 15731712, 15376435, 16403468, 15664064] gs).getD 26 0 = 4095)
    (h2 : ∀ (xs ys : List Nat) (gs : List (Bool × Nat × Nat)) (r s k : Nat), xs.length = ys.length → (∀ i, (xs.getD i 0).testBit r = true → (ys.getD i 0).testBit s = true) → ((List.foldl (fun (xs : List Nat) (g : Bool × Nat × Nat) => xs ++ [if g.1 = true then xs.getD g.2.1 0 ||| xs.getD g.2.2 0 else xs.getD g.2.1 0 &&& xs.getD g.2.2 0]) xs gs).getD k 0).testBit r = true → ((List.foldl (fun (xs : List Nat) (g : Bool × Nat × Nat) => xs ++ [if g.1 = true then xs.getD g.2.1 0 ||| xs.getD g.2.2 0 else xs.getD g.2.1 0 &&& xs.getD g.2.2 0]) ys gs).getD k 0).testBit s = true) :
    ∃ (x1 : List (Bool × ℕ × ℕ)), (1 : ℕ) ≤ x1.length ∧ x1.length ≤ (14 : ℕ) ∧ (List.foldl (fun (x2 : List ℕ) (x3 : Bool × ℕ × ℕ) => x2 ++ [if x3.1 = Bool.true then x2.getD x3.2.1 (0 : ℕ) ||| x2.getD x3.2.2 (0 : ℕ) else x2.getD x3.2.1 (0 : ℕ) &&& x2.getD x3.2.2 (0 : ℕ)]) [(256463372304 : ℕ), (8521482511360 : ℕ), (14003410187716736 : ℕ), (55389823206179104 : ℕ), (155696362464215096 : ℕ), (218994303131713984 : ℕ), (183565875465424384 : ℕ), (229736628136996864 : ℕ), (270286071508729856 : ℕ), (288160007409369088 : ℕ), (192860064594267704 : ℕ), (288166778660192704 : ℕ), (283797140973809664 : ℕ)] x1).getD ((13 : ℕ) + x1.length - (1 : ℕ)) (0 : ℕ) = (1764784 : ℕ) := by
  obtain ⟨fgs, hlen, houtFin⟩ := h1
  let gs : List (Bool × Nat × Nat) := fgs.map (fun g => (g.1, g.2.1.val, g.2.2.val))
  have hlenN : gs.length = 14 := by simp only [gs, List.length_map, hlen]
  have hout : (List.foldl (fun (xs : List Nat) (g : Bool × Nat × Nat) => xs ++
      [if g.1 = true then xs.getD g.2.1 0 ||| xs.getD g.2.2 0
       else xs.getD g.2.1 0 &&& xs.getD g.2.2 0])
      [251137, 817232, 3224100, 5542026, 11018243, 9060364, 12746800, 10682560, 13370112, 15731712, 15376435, 16403468, 15664064]
      gs).getD (13 + gs.length - 1) 0 = 4095 := by
    simpa only [gs, List.length_map, List.foldl_map, hlen] using houtFin
  refine ⟨gs, (by omega), (by omega), ?_⟩
  let original : List Nat := [256463372304, 8521482511360, 14003410187716736, 55389823206179104, 155696362464215096, 218994303131713984, 183565875465424384, 229736628136996864, 270286071508729856, 288160007409369088, 192860064594267704, 288166778660192704, 283797140973809664]
  let compressed : List Nat := [251137, 817232, 3224100, 5542026, 11018243, 9060364, 12746800, 10682560, 13370112, 15731712, 15376435, 16403468, 15664064]
  let step := (fun (xs : List Nat) (g : Bool × Nat × Nat) => xs ++ [if g.1 = true then xs.getD g.2.1 0 ||| xs.getD g.2.2 0 else xs.getD g.2.1 0 &&& xs.getD g.2.2 0])
  let run := fun xs => List.foldl step xs gs
  let k := 13 + gs.length - 1
  change (run compressed).getD k 0 = 4095 at hout
  change (run original).getD k 0 = 1764784
  have mono (xs ys : List Nat) (r s : Nat) (hlen : xs.length = ys.length)
      (hin : ∀ i, (xs.getD i 0).testBit r = true → (ys.getD i 0).testBit s = true) :
      ((run xs).getD k 0).testBit r = true → ((run ys).getD k 0).testBit s = true :=
    h2 xs ys gs r s k hlen hin
  have default (xs : List Nat) (i : Nat) (hi : xs.length ≤ i) : xs.getD i 0 = 0 := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
  have cert : ∀ r : Fin 58,
      ((1764784 : Nat).testBit r = true → ∃ s : Fin 12,
        ∀ i : Fin 13, (compressed.getD i 0).testBit s = true →
          (original.getD i 0).testBit r = true) ∧
      ((1764784 : Nat).testBit r = false → ∃ s : Fin 12,
        ∀ i : Fin 13, (original.getD i 0).testBit r = true →
          (compressed.getD i 0).testBit (12 + s) = true) := by
    decide +kernel
  have positive : ∀ s : Fin 12, (4095 : Nat).testBit s = true := by decide
  have negative : ∀ s : Fin 12, (4095 : Nat).testBit (12 + s) = false := by decide
  have bounded : ∀ i : Fin 13, original.getD i 0 < 2 ^ 58 := by decide
  apply Nat.eq_of_testBit_eq
  intro r
  by_cases hr : r < 58
  · by_cases ht : (1764784 : Nat).testBit r = true
    · obtain ⟨s, hs⟩ := (cert ⟨r, hr⟩).1 ht
      have hin : ∀ i, (compressed.getD i 0).testBit s = true →
          (original.getD i 0).testBit r = true := by
        intro i hi
        by_cases hb : i < 13
        · exact hs ⟨i, hb⟩ hi
        · have hz := default compressed i (by change 13 ≤ i; omega)
          rw [hz] at hi
          simp at hi
      have hval : ((run original).getD k 0).testBit r = true :=
        mono compressed original s r rfl hin (by rw [hout]; exact positive s)
      exact hval.trans ht.symm
    · have htf : (1764784 : Nat).testBit r = false := by
        exact Bool.eq_false_iff.mpr ht
      obtain ⟨s, hs⟩ := (cert ⟨r, hr⟩).2 htf
      have hin : ∀ i, (original.getD i 0).testBit r = true →
          (compressed.getD i 0).testBit (12 + s) = true := by
        intro i hi
        by_cases hb : i < 13
        · exact hs ⟨i, hb⟩ hi
        · have hz := default original i (by change 13 ≤ i; omega)
          rw [hz] at hi
          simp at hi
      have hn : ((run original).getD k 0).testBit r ≠ true := by
        intro hv
        have hf := mono original compressed r (12 + s) rfl hin hv
        rw [hout, negative s] at hf
        contradiction
      have hf : ((run original).getD k 0).testBit r = false := by
        exact Bool.eq_false_iff.mpr hn
      exact hf.trans htf.symm
  · have hp : 2 ^ 58 ≤ 2 ^ r := Nat.pow_le_pow_right (by decide) (by omega)
    have hin : ∀ i, (original.getD i 0).testBit r = true →
        (compressed.getD i 0).testBit 12 = true := by
      intro i hi
      have hb : original.getD i 0 < 2 ^ 58 := by
        by_cases hb : i < 13
        · exact bounded ⟨i, hb⟩
        · rw [default original i (by change 13 ≤ i; omega)]
          decide
      have hz := Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hb hp)
      rw [hz] at hi
      contradiction
    have hn : ((run original).getD k 0).testBit r ≠ true := by
      intro hv
      have hf := mono original compressed r 12 rfl hin hv
      rw [hout] at hf
      have hz : (4095 : Nat).testBit 12 = false := by decide
      rw [hz] at hf
      contradiction
    have hf : ((run original).getD k 0).testBit r = false := by
      exact Bool.eq_false_iff.mpr hn
    have ht : (1764784 : Nat).testBit r = false :=
      Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le (by decide : 1764784 < 2 ^ 58) hp)
    exact hf.trans ht.symm
