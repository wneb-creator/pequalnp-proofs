import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4970_aux

open Finset

def lineOr {p l : Nat} (Q : Finset (Fin l)) (x : Fin (p + l) → Bool) : Bool :=
  decide (∃ b ∈ Q, x (Fin.natAdd p b) = true)

def pointOr {p l : Nat} (P : Finset (Fin p)) (x : Fin (p + l) → Bool) : Bool :=
  decide (∃ a ∈ P, x (Fin.castAdd l a) = true)

theorem lineOr_unique {p l : Nat} {Q R : Finset (Fin l)}
    (h : ∀ x : Fin (p + l) → Bool, lineOr Q x = lineOr R x) : Q = R := by
  ext b
  have hh := h (fun i => decide (i = Fin.natAdd p b))
  have hi : ∀ b' : Fin l, Fin.natAdd p b' = Fin.natAdd p b ↔ b' = b := by
    intro b'
    constructor
    · intro he
      apply Fin.ext
      exact Nat.add_left_cancel (congrArg Fin.val he)
    · rintro rfl; rfl
  simpa [lineOr, hi] using hh

theorem pointOr_unique {p l : Nat} {P R : Finset (Fin p)}
    (h : ∀ x : Fin (p + l) → Bool, pointOr P x = pointOr R x) : P = R := by
  ext a
  have hh := h (fun i => decide (i = Fin.castAdd l a))
  have hi : ∀ a' : Fin p, Fin.castAdd l a' = Fin.castAdd l a ↔ a' = a := by
    intro a'
    constructor
    · intro he
      exact Fin.ext (congrArg (fun i : Fin (p + l) => i.val) he)
    · rintro rfl; rfl
  simpa [pointOr, hi] using hh

theorem different_colours_ne {p l : Nat} {P : Finset (Fin p)} {Q : Finset (Fin l)}
    (hP : P.Nonempty) : ¬ (∀ x : Fin (p + l) → Bool, pointOr P x = lineOr Q x) := by
  intro h
  obtain ⟨a, ha⟩ := hP
  let x : Fin (p + l) → Bool := fun i => decide (i = Fin.castAdd l a)
  have hp : pointOr P x = true := by
    simp only [pointOr, decide_eq_true_eq]
    exact ⟨a, ha, by simp [x]⟩
  have hq : lineOr Q x = false := by
    simp only [lineOr, decide_eq_false_iff_not]
    rintro ⟨b, _, hb⟩
    have hba : Fin.natAdd p b = Fin.castAdd l a := by simpa [x] using hb
    have hv := congrArg Fin.val hba
    have ha' := a.isLt
    simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
    omega
  have hh := h x
  rw [hp, hq] at hh
  cases hh

theorem star_centre_unique {p l : Nat} {E : Finset (Fin p × Fin l)}
    (hE : ∀ a a' : Fin p, ∀ b b' : Fin l, a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    {a a' : Fin p} {Q : Finset (Fin l)} (hQ : 2 ≤ Q.card)
    (ha : ∀ b ∈ Q, (a,b) ∈ E) (ha' : ∀ b ∈ Q, (a',b) ∈ E) : a = a' := by
  by_contra haa
  obtain ⟨b, hb, b', hb', hbb⟩ := Finset.one_lt_card.mp (by omega : 1 < Q.card)
  exact hE a a' b b' haa hbb ⟨ha b hb, ha b' hb', ha' b hb, ha' b' hb'⟩

theorem one_wire_one_point_centre {p l : Nat} {E : Finset (Fin p × Fin l)}
    (hE : ∀ a a' : Fin p, ∀ b b' : Fin l, a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    {a a' : Fin p} {Q R : Finset (Fin l)} (hQ : 2 ≤ Q.card)
    (ha : ∀ b ∈ Q, (a,b) ∈ E) (ha' : ∀ b ∈ R, (a',b) ∈ E)
    (h : ∀ x : Fin (p + l) → Bool, lineOr Q x = lineOr R x) : a = a' := by
  have hQR := lineOr_unique h
  subst R
  exact star_centre_unique hE hQ ha ha'

end PEqualNP.Outside.L_meta_4970_aux
