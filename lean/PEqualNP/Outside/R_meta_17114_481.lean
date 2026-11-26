import PEqualNP.Defs

open PEqualNP PEqualNP.CircuitLowerBounds

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.R_meta_17114_481
    (finite : ∃ C : Circuit, C.size ≤ 15 ∧ 25 ≤ C.output ∧ C.output < 25 + C.size ∧
      (∀ j g, C.gates[j]? = some g → (g.op = .and ∨ g.op = .or) ∧
        ∃ a b, g.inputs = [a,b] ∧ a ≠ b ∧ a < 25+j ∧ b < 25+j) ∧
      (∀ m ∈ ([129,130,136,2064,2080,2049,4128,4160,4098,8256,8193,8196] : List ℕ),
        C.eval (List.ofFn (fun i : Fin 14 => m.testBit i.val) ++ List.replicate 11 false) = true) ∧
      (∀ m ∈ ([1919,2036,3918,4036,5917,6036,7948,8068,10042,10160,12042,14104,14224,16136,16256] : List ℕ),
        C.eval (List.ofFn (fun i : Fin 14 => m.testBit i.val) ++ List.replicate 11 true) = false) ∧
      ∀ s : Bool, ∃ r : ℕ → ℕ, r (if s = true then 0 else 7) = 0 ∧ r (if s = true then 7 else 0) ≤ 1 ∧
        (∀ j < 25, j ≠ 0 → j ≠ 7 → r j = 2) ∧ 2 ≤ r C.output ∧
        ∀ j g a b, C.gates[j]? = some g → g.inputs = [a,b] →
          (g.op = .and → r (25+j) ≤ r a + r b) ∧ (g.op = .or → r (25+j) ≤ min (r a) (r b)))
    (mono : ∀ C : Circuit, (∀ g ∈ C.gates, g.op = .and ∨ g.op = .or) → ∀ a b : List Bool,
       (∀ i, a.getD i false = true → b.getD i false = true) → C.eval a = true → C.eval b = true) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (15 : ℕ) ∧ (25 : ℕ) ≤ x1.output ∧ x1.output < (25 : ℕ) + x1.size ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (25 : ℕ) + x2 ∧ x6 < (25 : ℕ) + x2) ∧ (∀ (x2 : Fin (14 : ℕ) → Bool) (x3 : List Bool), x3.length = (11 : ℕ) → (x1.eval (List.ofFn x2 ++ x3) = Bool.true ↔ ∃ (x5 : Fin (7 : ℕ)) (x6 : Fin (7 : ℕ)), ¬((1 : ℕ) ≤ ↑x6 ∧ ↑x6 ≤ (3 : ℕ)) ∧ (x5 = x6 ∨ x5 = x6 + (1 : Fin (7 : ℕ)) ∨ x5 = x6 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x5) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x6) = Bool.true)) ∧ ∀ (x2 : Bool), ∃ (x3 : ℕ → ℕ), x3 (if x2 = Bool.true then (0 : ℕ) else (7 : ℕ)) = (0 : ℕ) ∧ x3 (if x2 = Bool.true then (7 : ℕ) else (0 : ℕ)) ≤ (1 : ℕ) ∧ (∀ x4 < (25 : ℕ), x4 ≠ (0 : ℕ) → x4 ≠ (7 : ℕ) → x3 x4 = (2 : ℕ)) ∧ (2 : ℕ) ≤ x3 x1.output ∧ ∀ (x4 : ℕ) (x5 : PEqualNP.CircuitLowerBounds.Gate) (x6 x7 : ℕ), x1.gates[x4]? = Option.some x5 → x5.inputs = [x6, x7] → (x5.op = PEqualNP.CircuitLowerBounds.GateOp.and → x3 ((25 : ℕ) + x4) ≤ x3 x6 + x3 x7) ∧ (x5.op = PEqualNP.CircuitLowerBounds.GateOp.or → x3 ((25 : ℕ) + x4) ≤ Min.min (x3 x6) (x3 x7)) := by
  let E := fun p l : Fin 7 => ¬ (1 ≤ l.val ∧ l.val ≤ 3) ∧ (p = l ∨ p = l + 1 ∨ p = l + 3)
  let P : List ℕ := [129,130,136,2064,2080,2049,4128,4160,4098,8256,8193,8196]
  let Z : List ℕ := [1919,2036,3918,4036,5917,6036,7948,8068,10042,10160,12042,14104,14224,16136,16256]
  let row (m : ℕ) (i : Fin 14) := m.testBit i.val
  have pos : ∀ p l : Fin 7, E p l → ∃ m ∈ P,
      ∀ i : Fin 14, row m i = true → i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l := by decide +kernel
  have neg : ∀ a : Fin 7 → Bool, ∃ m ∈ Z,
      (∀ i : Fin 7, a i = true → row m (Fin.castAdd 7 i) = true) ∧
      (∀ j : Fin 7, (∀ i : Fin 7, E i j → a i = false) → row m (Fin.natAdd 7 j) = true) := by decide +kernel
  obtain ⟨C,hs,ho,hou,hg,hp,hn,hr⟩ := finite
  have ops : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg'
    obtain ⟨j,hj,hjg⟩ := List.mem_iff_getElem.mp hg'
    exact (hg j g (by rw [List.getElem?_eq_getElem hj, hjg])).1
  have cmp (x y : Fin 14 → Bool) (a b : List Bool)
      (hxy : ∀ i, x i = true → y i = true)
      (hab : ∀ i, a.getD i false = true → b.getD i false = true) :
      ∀ i, (List.ofFn x ++ a).getD i false = true → (List.ofFn y ++ b).getD i false = true := by
    intro i hv
    by_cases hi : i < 14
    · have read (z : Fin 14 → Bool) : (List.ofFn z).getD i false = z ⟨i,hi⟩ := by
        have hz : i < (List.ofFn z).length := by simpa using hi
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hz, List.getElem_ofFn]
        rfl
      rw [List.getD_append _ _ _ _ (by simpa using hi), read x] at hv
      rw [List.getD_append _ _ _ _ (by simpa using hi), read y]
      exact hxy _ hv
    · have hx : (List.ofFn x).length ≤ i := by simpa using Nat.le_of_not_lt hi
      have hy : (List.ofFn y).length ≤ i := by simpa using Nat.le_of_not_lt hi
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hx, List.getElem?_append_right hy,
        List.length_ofFn] at hv ⊢
      simp only [List.getD_eq_getElem?_getD] at hab
      exact hab _ hv
  refine ⟨C,hs,ho,hou,hg,?_,hr⟩
  intro x a ha
  suffices h : C.eval (List.ofFn x ++ a) = true ↔ ∃ p l : Fin 7, E p l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true by
    simpa only [E, and_assoc] using h
  constructor
  · intro hv
    by_contra he
    obtain ⟨m,hm,hmp,hml⟩ := neg (fun i => x (Fin.castAdd 7 i))
    have sub : ∀ i, x i = true → row m i = true := by
      intro i hi
      by_cases hl : i.val < 7
      · let p : Fin 7 := ⟨i.val,hl⟩
        have eq : Fin.castAdd 7 p = i := Fin.ext rfl
        rw [← eq] at hi ⊢
        exact hmp p hi
      · let l : Fin 7 := ⟨i.val - 7, by omega⟩
        have eq : Fin.natAdd 7 l = i := Fin.ext (by simp [l]; omega)
        rw [← eq] at hi ⊢
        apply hml l
        intro p hepl
        cases hx : x (Fin.castAdd 7 p)
        · rfl
        · exact False.elim (he ⟨p,l,hepl,hx,hi⟩)
    have tail : ∀ i, a.getD i false = true → (List.replicate 11 true).getD i false = true := by
      intro i h
      by_cases hi : i < 11
      · rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
        simp only [hi, ite_true, Option.getD_some]
      · rw [List.getD_eq_default _ _ (by omega)] at h
        exact Bool.noConfusion h
    have hy := mono C ops _ _ (cmp x (row m) a (List.replicate 11 true) sub tail) hv
    exact Bool.noConfusion ((hn m hm).symm.trans hy)
  · rintro ⟨p,l,he,hxp,hxl⟩
    obtain ⟨m,hm,hm'⟩ := pos p l he
    have sub : ∀ i, row m i = true → x i = true := by
      intro i hi
      rcases hm' i hi with rfl | rfl
      · exact hxp
      · exact hxl
    have tail : ∀ i, (List.replicate 11 false).getD i false = true → a.getD i false = true := by
      intro i h
      rw [List.getD_eq_getElem?_getD, List.getElem?_replicate] at h
      by_cases hi : i < 11 <;> simp only [hi, ite_true, ite_false, Option.getD_some, Option.getD_none,
        Bool.false_eq_true] at h
    exact mono C ops _ _ (cmp (row m) x (List.replicate 11 false) a sub tail) (hp m hm)
