import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2590

def petersen (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
  (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
  (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) ||
  (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)

def row (k : ℕ) (i : Fin 10) : Bool := k.testBit i.val

set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
lemma exceptional_supports : ∀ x : Fin 10 → Bool,
    x 0 = false → petersen x = false →
    ((∀ w : Fin 10, w = 1 ∨ w = 4 ∨ w = 5 →
        petersen (Function.update x w true) = true) ↔
      x = row 772 ∨ x = row 200) := by
  decide

lemma neighbor_forces (x : Fin 10 → Bool) (w : Fin 10)
    (hw : w = 1 ∨ w = 4 ∨ w = 5) :
    petersen (Function.update (Function.update x w true) 0 true) = true := by
  rcases hw with rfl | rfl | rfl <;> simp [petersen]

lemma or_guard_exceptional (B h : (Fin 10 → Bool) → Bool)
    (hm : Monotone h)
    (correct : ∀ x : Fin 10 → Bool,
      B (Function.update x 0 (x 0 || h x)) = petersen x)
    (x : Fin 10 → Bool) (hx : x 0 = false) (hf : petersen x = false)
    (hh : h x = true) : x = row 772 ∨ x = row 200 := by
  apply (exceptional_supports x hx hf).mp
  intro w hw
  let y := Function.update x w true
  have hxy : x ≤ y := by
    intro i
    by_cases hi : i = w <;> simp [y, hi]
  have hy : h y = true := by
    have ht := hm hxy
    rw [hh] at ht
    exact Bool.le_iff_imp.mp ht rfl
  have cy := correct y
  rw [hy, Bool.or_true] at cy
  have cz := correct (Function.update y 0 true)
  simp only [Function.update_self, Bool.true_or, Function.update_idem] at cz
  rw [← cy, cz]
  exact neighbor_forces x w hw

set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
lemma petersen_clear_zero (x : Fin 10 → Bool) (hx : petersen x = false) :
    petersen (Function.update x 0 false) = false := by
  have h : ∀ x : Fin 10 → Bool, petersen x = false →
      petersen (Function.update x 0 false) = false := by decide
  exact h x hx

lemma or_guard_below (B h : (Fin 10 → Bool) → Bool)
    (hm : Monotone h)
    (ignores : ∀ x, h (Function.update x 0 false) = h x)
    (correct : ∀ x : Fin 10 → Bool,
      B (Function.update x 0 (x 0 || h x)) = petersen x)
    (e1 : h (row 772) = false) (e2 : h (row 200) = false) :
    ∀ x, h x = true → petersen x = true := by
  intro x hx
  cases hf : petersen x with
  | true => rfl
  | false =>
      have hy : h (Function.update x 0 false) = true := (ignores x).trans hx
      have he := or_guard_exceptional B h hm correct (Function.update x 0 false)
        (by simp) (petersen_clear_zero x hf) hy
      rcases he with he | he
      · rw [he, e1] at hy
        contradiction
      · rw [he, e2] at hy
        contradiction

def edgeRow (i : Fin 15) : Fin 10 → Bool :=
  row (([3, 6, 12, 24, 17, 33, 66, 132, 264, 528, 160, 640, 576, 320, 288] : List ℕ).get i)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
lemma positive_has_edge : ∀ x : Fin 10 → Bool, petersen x = true →
    ∃ i : Fin 15, edgeRow i ≤ x := by
  decide

lemma edgeRow_true (i : Fin 15) : petersen (edgeRow i) = true := by
  have h : ∀ i : Fin 15, petersen (edgeRow i) = true := by decide
  exact h i

lemma drop_or_guard (B h : (Fin 10 → Bool) → Bool)
    (hm : Monotone B)
    (correct : ∀ x : Fin 10 → Bool,
      B (Function.update x 0 (x 0 || h x)) = petersen x)
    (empty : ∀ i : Fin 15, h (edgeRow i) = false) :
    ∀ x, B x = petersen x := by
  intro x
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hx
    have hxy : x ≤ Function.update x 0 (x 0 || h x) := by
      intro i
      by_cases hi : i = 0
      · subst i
        simp only [Function.update_self]
        cases x 0 <;> cases h x <;> decide
      · simp [hi]
    have hb := Bool.le_iff_imp.mp (hm hxy) hx
    rw [correct x] at hb
    exact hb
  · intro hx
    obtain ⟨i, hi⟩ := positive_has_edge x hx
    have he := correct (edgeRow i)
    rw [empty i, Bool.or_false] at he
    simp only [Function.update_eq_self] at he
    have hb : B (edgeRow i) = true := he.trans (edgeRow_true i)
    exact Bool.le_iff_imp.mp (hm hi) hb

end PEqualNP.Outside.L_meta_2590
