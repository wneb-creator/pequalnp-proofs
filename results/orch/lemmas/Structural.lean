import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592

lemma monotone_context_is_bit {n : ℕ} (G : (Fin n → Bool) → Bool → Bool)
    (hG : Monotone (fun y : (Fin n → Bool) × Bool => G y.1 y.2))
    (lo : G (fun _ => false) true = true)
    (hi : G (fun _ => true) false = false) :
    ∀ (x : Fin n → Bool) (b : Bool), G x b = b := by
  intro x b
  cases b with
  | false =>
    have h := hG (show (x, false) ≤ ((fun _ => true), false) by
      constructor
      · intro i
        exact Bool.le_true _
      · exact le_rfl)
    change G x false ≤ G (fun _ => true) false at h
    rw [hi] at h
    exact le_antisymm h (Bool.false_le _)
  | true =>
    have h := hG (show ((fun _ => false), true) ≤ (x, true) by
      constructor
      · intro i
        exact Bool.false_le _
      · exact le_rfl)
    change G (fun _ => false) true ≤ G x true at h
    rw [lo] at h
    exact le_antisymm (Bool.le_true _) h

lemma double_negation_context {n : ℕ} (G : (Fin n → Bool) → Bool → Bool)
    (H : (Fin n → Bool) → Bool)
    (hG : Monotone (fun y : (Fin n → Bool) × Bool => G y.1 y.2))
    (lo : !G (fun _ => false) (!H (fun _ => false)) = false)
    (hi : !G (fun _ => true) (!H (fun _ => true)) = true) :
    ∀ x : Fin n → Bool, !G x (!H x) = H x := by
  have hlo : G (fun _ => false) true = true := by
    have h := hG (show ((fun _ => false), !H (fun _ => false)) ≤
        ((fun _ => false), true) by
      exact ⟨le_rfl, Bool.le_true _⟩)
    change G (fun _ => false) (!H (fun _ => false)) ≤ G (fun _ => false) true at h
    have hz : G (fun _ => false) (!H (fun _ => false)) = true := by simpa using lo
    rw [hz] at h
    exact le_antisymm (Bool.le_true _) h
  have hhi : G (fun _ => true) false = false := by
    have h := hG (show ((fun _ => true), false) ≤
        ((fun _ => true), !H (fun _ => true)) by
      exact ⟨le_rfl, Bool.false_le _⟩)
    change G (fun _ => true) false ≤ G (fun _ => true) (!H (fun _ => true)) at h
    have hz : G (fun _ => true) (!H (fun _ => true)) = false := by simpa using hi
    rw [hz] at h
    exact le_antisymm h (Bool.false_le _)
  intro x
  rw [monotone_context_is_bit G hG hlo hhi x (!H x)]
  simp

end PEqualNP.Outside.L_meta_2592
