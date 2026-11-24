import Mathlib

namespace PEqualNP.Outside.L_meta_1482

abbrev incidence (p l : Fin 13) : Prop :=
  p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9

lemma incidence_refl (p : Fin 13) : incidence p p := Or.inl rfl

lemma line_degree :
    ∀ l : Fin 13, ((Finset.univ : Finset (Fin 13)).filter fun p => incidence p l).card = 4 := by
  decide

lemma point_degree :
    ∀ p : Fin 13, ((Finset.univ : Finset (Fin 13)).filter fun l => incidence p l).card = 4 := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma no_four_cycle :
    ∀ p q l m : Fin 13,
      incidence p l → incidence p m → incidence q l → incidence q m → p = q ∨ l = m := by
  decide

lemma incidence_count :
    ((Finset.univ : Finset (Fin 13 × Fin 13)).filter fun e => incidence e.1 e.2).card = 52 := by
  decide

lemma cover_card_lower_bound (points lines : Finset (Fin 13))
    (hcover : ∀ p l : Fin 13, incidence p l → p ∈ points ∨ l ∈ lines) :
    13 ≤ points.card + lines.card := by
  have hsub : (Finset.univ : Finset (Fin 13)) ⊆ points ∪ lines := by
    intro p _
    exact Finset.mem_union.mpr (hcover p p (incidence_refl p))
  calc
    13 = (Finset.univ : Finset (Fin 13)).card := by simp
    _ ≤ (points ∪ lines).card := Finset.card_le_card hsub
    _ ≤ points.card + lines.card := Finset.card_union_le points lines

lemma missing_linear_witness
    (n m : ℕ) (isAnd : Fin m → Prop) [DecidablePred isAnd]
    (left right : Fin m → ℕ)
    (hleft : ∀ j, left j < n + j.val)
    (hright : ∀ j, right j < n + j.val)
    (a b d : ℕ → Bool)
    (hin : ∀ i < n, b i = true → a i = true ∨ d i = true)
    (ha : ∀ j, a (n + j.val) =
      if isAnd j then a (left j) && a (right j) else a (left j) || a (right j))
    (hb : ∀ j, b (n + j.val) =
      if isAnd j then b (left j) && b (right j) else b (left j) || b (right j))
    (hd : ∀ j, d (n + j.val) =
      if isAnd j then (a (left j) && d (right j)) || (d (left j) && a (right j))
      else d (left j) || d (right j))
    (o : ℕ) (ho : o < n + m) (hao : a o = false) (hbo : b o = true)
    (hdo : d o = false) :
    ∃ j : Fin m, isAnd j ∧ b (left j) = true ∧ b (right j) = true ∧
      a (left j) = false ∧ a (right j) = false ∧
      d (left j) = true ∧ d (right j) = true := by
  revert ho hao hbo hdo
  induction o using Nat.strong_induction_on with
  | ind o ih =>
    intro ho hao hbo hdo
    by_cases hoi : o < n
    · have := hin o hoi hbo
      simp [hao, hdo] at this
    · let j : Fin m := ⟨o - n, by omega⟩
      have hjo : n + j.val = o := by dsimp [j]; omega
      have hlj : left j < o := by simpa only [hjo] using hleft j
      have hrj : right j < o := by simpa only [hjo] using hright j
      have hae := ha j
      have hbe := hb j
      have hde := hd j
      rw [hjo, hao] at hae
      rw [hjo, hbo] at hbe
      rw [hjo, hdo] at hde
      by_cases hj : isAnd j
      · simp only [if_pos hj] at hae hbe hde
        have hbl : b (left j) = true := by
          cases hl : b (left j) <;> cases hr : b (right j) <;> simp [hl, hr] at hbe ⊢
        have hbr : b (right j) = true := by
          cases hl : b (left j) <;> cases hr : b (right j) <;> simp [hl, hr] at hbe ⊢
        by_cases hal : a (left j) = true
        · have har : a (right j) = false := by
            cases hr : a (right j) <;> simp [hal, hr] at hae ⊢
          have hdr : d (right j) = false := by
            cases hr : d (right j) <;> simp [hal, hr] at hde ⊢
          exact ih (right j) hrj (by omega) har hbr hdr
        · have hal' : a (left j) = false := Bool.eq_false_of_not_eq_true hal
          by_cases har : a (right j) = true
          · have hdl : d (left j) = false := by
              cases hl : d (left j) <;> simp [har, hl] at hde ⊢
            exact ih (left j) hlj (by omega) hal' hbl hdl
          · have har' : a (right j) = false := Bool.eq_false_of_not_eq_true har
            by_cases hdl : d (left j) = true
            · by_cases hdr : d (right j) = true
              · exact ⟨j, hj, hbl, hbr, hal', har', hdl, hdr⟩
              · exact ih (right j) hrj (by omega) har' hbr
                  (Bool.eq_false_of_not_eq_true hdr)
            · exact ih (left j) hlj (by omega) hal' hbl
                (Bool.eq_false_of_not_eq_true hdl)
      · simp only [if_neg hj] at hae hbe hde
        have hal : a (left j) = false := by
          cases hl : a (left j) <;> simp [hl] at hae ⊢
        have har : a (right j) = false := by
          cases hr : a (right j) <;> simp [hr] at hae ⊢
        have hdl : d (left j) = false := by
          cases hl : d (left j) <;> simp [hl] at hde ⊢
        have hdr : d (right j) = false := by
          cases hr : d (right j) <;> simp [hr] at hde ⊢
        have hbor : b (left j) = true ∨ b (right j) = true := by
          cases hl : b (left j) <;> cases hr : b (right j) <;> simp [hl, hr] at hbe ⊢
        rcases hbor with hbl | hbr
        · exact ih (left j) hlj (by omega) hal hbl hdl
        · exact ih (right j) hrj (by omega) har hbr hdr

lemma addCases_monotone {n m : ℕ} (x x' : Fin n → Bool) (y y' : Fin m → Bool)
    (hx : ∀ p, x p = true → x' p = true) (hy : ∀ l, y l = true → y' l = true) :
    ∀ i : Fin (n + m), Fin.addCases x y i = true → Fin.addCases x' y' i = true := by
  intro i
  refine Fin.addCases (fun p => ?_) (fun l => ?_) i
  · simpa using hx p
  · simpa using hy l

def zeroLineClosure {P L : Type} [Fintype P] (I : P → L → Prop) [DecidableRel I]
    (x : P → Bool) (l : L) : Bool :=
  decide (∀ p : P, x p = true → ¬ I p l)

def zeroPointClosure {P L : Type} [Fintype L] (I : P → L → Prop) [DecidableRel I]
    (y : L → Bool) (p : P) : Bool :=
  decide (∀ l : L, y l = true → ¬ I p l)

lemma critical_inputs_correct {P L : Type} [Fintype P] [Fintype L]
    [DecidableEq P] [DecidableEq L] (I : P → L → Prop) [DecidableRel I]
    (F : (P → Bool) → (L → Bool) → Bool)
    (hmono : ∀ x y x' y', (∀ p, x p = true → x' p = true) →
      (∀ l, y l = true → y' l = true) → F x y = true → F x' y' = true)
    (hpos : ∀ p l, I p l →
      F (fun p' => decide (p' = p)) (fun l' => decide (l' = l)) = true)
    (hneg : ∀ x, F (zeroPointClosure I (zeroLineClosure I x)) (zeroLineClosure I x) = false) :
    ∀ x y, F x y = true ↔ ∃ p l, I p l ∧ x p = true ∧ y l = true := by
  intro x y
  constructor
  · intro hf
    by_contra hn
    have hx : ∀ p, x p = true → zeroPointClosure I (zeroLineClosure I x) p = true := by
      intro p hp
      simp only [zeroPointClosure, decide_eq_true_eq]
      intro l hl
      exact (of_decide_eq_true hl) p hp
    have hy : ∀ l, y l = true → zeroLineClosure I x l = true := by
      intro l hl
      simp only [zeroLineClosure, decide_eq_true_eq]
      intro p hp hip
      exact hn ⟨p, l, hip, hp, hl⟩
    have h := hmono x y _ _ hx hy hf
    rw [hneg] at h
    exact Bool.noConfusion h
  · rintro ⟨p, l, hip, hp, hl⟩
    apply hmono _ _ x y _ _ (hpos p l hip)
    · intro p' hp'
      simp only [decide_eq_true_eq] at hp'
      simpa only [hp'] using hp
    · intro l' hl'
      simp only [decide_eq_true_eq] at hl'
      simpa only [hl'] using hl

end PEqualNP.Outside.L_meta_1482
