import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2602_aux.FirstAnd

lemma first_and (n k : ℕ) (X Y Z : ℕ → Bool) (op : ℕ → Bool) (a b : ℕ → ℕ)
    (hseed : ∀ i < n, Z i = (X i || Y i))
    (hx : ∀ j < k, X (n + j) = if op j then X (a j) || X (b j) else X (a j) && X (b j))
    (hy : ∀ j < k, Y (n + j) = if op j then Y (a j) || Y (b j) else Y (a j) && Y (b j))
    (hz : ∀ j < k, Z (n + j) = if op j then Z (a j) || Z (b j) else Z (a j) && Z (b j))
    (ha : ∀ j < k, a j < n + j) (hb : ∀ j < k, b j < n + j)
    (out : ℕ) (hout : out < n + k) (hZo : Z out = true)
    (hXo : X out = false) (hYo : Y out = false) :
    ∃ j < k, op j = false ∧
      ((X (a j) = true ∧ Y (a j) = false ∧ X (b j) = false ∧ Y (b j) = true) ∨
       (X (a j) = false ∧ Y (a j) = true ∧ X (b j) = true ∧ Y (b j) = false)) := by
  classical
  let Bad (i : ℕ) : Prop := Z i = true ∧ X i = false ∧ Y i = false
  have hex : ∃ i, Bad i := ⟨out, hZo, hXo, hYo⟩
  let w := Nat.find hex
  have hw : Bad w := Nat.find_spec hex
  have hwo : w ≤ out := Nat.find_min' hex ⟨hZo, hXo, hYo⟩
  have hmin (i : ℕ) (hi : i < w) : ¬ Bad i := by
    intro hbad
    have hle : w ≤ i := Nat.find_min' hex hbad
    omega
  have hn : n ≤ w := by
    by_contra hnot
    have hwlt : w < n := by omega
    have heq := hseed w hwlt
    simp only [Bad] at hw
    simp [hw.1, hw.2.1, hw.2.2] at heq
  let j := w - n
  have hj : j < k := by omega
  have hwj : n + j = w := by omega
  have hna := hmin (a j) (by simpa only [hwj] using ha j hj)
  have hnb := hmin (b j) (by simpa only [hwj] using hb j hj)
  have hxe := hx j hj
  have hye := hy j hj
  have hze := hz j hj
  rw [hwj] at hxe hye hze
  rcases hw with ⟨hZw, hXw, hYw⟩
  cases hop : op j
  · refine ⟨j, hj, hop, ?_⟩
    simp only [hop, Bool.false_eq_true, ↓reduceIte] at hxe hye hze
    have hza : Z (a j) = true := (Bool.and_eq_true_iff.mp (hze.symm.trans hZw)).1
    have hzb : Z (b j) = true := (Bool.and_eq_true_iff.mp (hze.symm.trans hZw)).2
    simp only [Bad, hza, hzb, true_and] at hna hnb
    cases hxa : X (a j) <;> cases hya : Y (a j) <;>
      cases hxb : X (b j) <;> cases hyb : Y (b j) <;>
      simp_all
  · exfalso
    simp only [hop, ↓reduceIte] at hxe hye hze
    have hxa : X (a j) = false := (Bool.or_eq_false_iff.mp (hxe.symm.trans hXw)).1
    have hxb : X (b j) = false := (Bool.or_eq_false_iff.mp (hxe.symm.trans hXw)).2
    have hya : Y (a j) = false := (Bool.or_eq_false_iff.mp (hye.symm.trans hYw)).1
    have hyb : Y (b j) = false := (Bool.or_eq_false_iff.mp (hye.symm.trans hYw)).2
    rcases Bool.or_eq_true_iff.mp (hze.symm.trans hZw) with hza | hzb
    · exact hna ⟨hza, hxa, hya⟩
    · exact hnb ⟨hzb, hxb, hyb⟩

end PEqualNP.Outside.L_meta_2602_aux.FirstAnd
