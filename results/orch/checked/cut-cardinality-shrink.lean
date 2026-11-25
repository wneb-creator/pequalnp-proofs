import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1896.CutCard

open Classical

variable {α : Type} [DecidableEq α]

def Closed (P : Finset (Finset α)) : Prop :=
  ∀ X ∈ P, ∀ Y ∈ P, symmDiff X Y ∈ P

lemma agree_symm (X Y : Finset α) (a b : α) :
    (a ∈ symmDiff X Y ↔ b ∈ symmDiff X Y) ↔
      ((a ∈ X ↔ b ∈ X) ↔ (a ∈ Y ↔ b ∈ Y)) := by
  by_cases haX : a ∈ X <;> by_cases hbX : b ∈ X <;>
    by_cases haY : a ∈ Y <;> by_cases hbY : b ∈ Y <;>
    simp [Finset.mem_symmDiff, haX, hbX, haY, hbY]

lemma closed_filter (P : Finset (Finset α)) (hP : Closed P) (a b : α) :
    Closed (P.filter fun X => a ∈ X ↔ b ∈ X) := by
  intro X hX Y hY
  rw [Finset.mem_filter] at hX hY ⊢
  exact ⟨hP X hX.1 Y hY.1, (agree_symm X Y a b).2 (by simp [hX.2, hY.2])⟩

lemma card_filter_le (P : Finset (Finset α)) (hP : Closed P) (a b : α) :
    P.card ≤ 2 * (P.filter fun X => a ∈ X ↔ b ∈ X).card := by
  by_cases hex : ∃ Y ∈ P, ¬ (a ∈ Y ↔ b ∈ Y)
  · obtain ⟨Y, hYP, hY⟩ := hex
    have hf (X : Finset α) :
        (a ∈ symmDiff X Y ↔ b ∈ symmDiff X Y) ↔ ¬ (a ∈ X ↔ b ∈ X) := by
      rw [agree_symm]
      simp [hY]
    have hb : (P.filter fun X => ¬ (a ∈ X ↔ b ∈ X)).card =
        (P.filter fun X => a ∈ X ↔ b ∈ X).card := by
      refine Finset.card_bij' (fun X _ => symmDiff X Y) (fun X _ => symmDiff X Y)
        ?_ ?_ ?_ ?_
      · intro X hX
        rw [Finset.mem_filter] at hX ⊢
        exact ⟨hP X hX.1 Y hYP, (hf X).2 hX.2⟩
      · intro X hX
        rw [Finset.mem_filter] at hX ⊢
        exact ⟨hP X hX.1 Y hYP, fun h => (hf X).1 h hX.2⟩
      · intro X _
        exact symmDiff_symmDiff_cancel_right Y X
      · intro X _
        exact symmDiff_symmDiff_cancel_right Y X
    have hs := Finset.card_filter_add_card_filter_not (s := P)
      (fun X => a ∈ X ↔ b ∈ X)
    omega
  · have he : (P.filter fun X => a ∈ X ↔ b ∈ X) = P := by
      apply Finset.filter_eq_self.2
      intro X hX
      by_contra hn
      exact hex ⟨X, hX, hn⟩
    rw [he]
    omega

def Agree (E : List (α × α)) (X : Finset α) : Prop :=
  ∀ e ∈ E, e.1 ∈ X ↔ e.2 ∈ X

omit [DecidableEq α] in
lemma agree_cons (e : α × α) (E : List (α × α)) (X : Finset α) :
    Agree (e :: E) X ↔ (e.1 ∈ X ↔ e.2 ∈ X) ∧ Agree E X := by
  simp [Agree]

lemma card_filter_agree_le (P : Finset (Finset α)) (hP : Closed P)
    (E : List (α × α)) :
    P.card ≤ 2 ^ E.length * (P.filter fun X => Agree E X).card := by
  induction E generalizing P with
  | nil => simp [Agree]
  | cons e E ih =>
    have h1 := card_filter_le P hP e.1 e.2
    have h2 := ih (P.filter fun X => e.1 ∈ X ↔ e.2 ∈ X)
      (closed_filter P hP e.1 e.2)
    have hf : ((P.filter fun X => e.1 ∈ X ↔ e.2 ∈ X).filter fun X => Agree E X) =
        P.filter (fun X => Agree (e :: E) X) := by
      ext X
      simp only [Finset.mem_filter, agree_cons]
      tauto
    rw [hf] at h2
    have h3 := Nat.mul_le_mul_left 2 h2
    calc
      P.card ≤ 2 * (P.filter fun X => e.1 ∈ X ↔ e.2 ∈ X).card := h1
      _ ≤ 2 * (2 ^ E.length * (P.filter fun X => Agree (e :: E) X).card) := h3
      _ = 2 ^ (e :: E).length * (P.filter fun X => Agree (e :: E) X).card := by
        simp [pow_succ, Nat.mul_assoc, Nat.mul_comm]

lemma card_filter_uniform_le (P : Finset (Finset α)) (hP : Closed P)
    (a : α) (R : List α) :
    P.card ≤ 2 ^ R.length *
      (P.filter fun X => ∀ b ∈ R, a ∈ X ↔ b ∈ X).card := by
  have h := card_filter_agree_le P hP (R.map fun b => (a, b))
  have hf : (P.filter fun X => Agree (R.map fun b => (a, b)) X) =
      (P.filter fun X => ∀ b ∈ R, a ∈ X ↔ b ∈ X) := by
    ext X
    simp only [Finset.mem_filter]
    apply and_congr_right
    intro _
    constructor
    · intro h b hb
      exact h (a, b) (List.mem_map.mpr ⟨b, hb, rfl⟩)
    · intro h e he
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp he
      exact h b hb
  rw [hf, List.length_map] at h
  exact h

lemma card_filter_eight_le (P : Finset (Finset α)) (hP : Closed P)
    (a : α) (R : List α) (hR : R.length ≤ 7) :
    P.card ≤ 128 * (P.filter fun X => ∀ b ∈ R, a ∈ X ↔ b ∈ X).card := by
  have h1 := card_filter_uniform_le P hP a R
  have h2 : 2 ^ R.length ≤ 128 := by
    have := Nat.pow_le_pow_right (by decide : 0 < 2) hR
    norm_num at this ⊢
    exact this
  exact h1.trans (Nat.mul_le_mul_right _ h2)

end PEqualNP.Outside.L_meta_1896.CutCard
