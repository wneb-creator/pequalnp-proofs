import Mathlib

namespace PEqualNP.Outside.FP3Strategy

def checkpointCount : List ℕ → ℕ
  | [] => 0
  | b :: bs => (b - 1) + b * checkpointCount bs

lemma checkpoint_count (bs : List ℕ) (h : ∀ b ∈ bs, 1 ≤ b) :
    checkpointCount bs + 1 = bs.prod := by
  induction bs with
  | nil => simp [checkpointCount]
  | cons b bs ih =>
    have hb : 1 ≤ b := h b (by simp)
    have ht : ∀ c ∈ bs, 1 ≤ c := fun c hc => h c (by simp [hc])
    have he := ih ht
    simp only [checkpointCount, List.prod_cons]
    rw [← he]
    rw [mul_add, mul_one]
    omega

lemma flattened_checkpoint_budget (T S B C : ℕ)
    (hT : T ≤ (B + 1) * C) (hW : B * S ≤ C) :
    T * S ≤ C * (C + S) := by
  calc
    T * S ≤ ((B + 1) * C) * S := Nat.mul_le_mul_right S hT
    _ = (B * S) * C + S * C := by ring
    _ ≤ C * C + S * C := Nat.add_le_add_right (Nat.mul_le_mul_right C hW) _
    _ = C * (C + S) := by ring

lemma flattened_checkpoint_barrier (T S B C : ℕ)
    (hT : T ≤ (B + 1) * C) (hW : B * S ≤ C) :
    T ≤ C ∨ S ≤ C := by
  rcases Nat.eq_zero_or_pos B with hB | hB
  · left
    simpa [hB] using hT
  · right
    have hs : S ≤ B * S := by nlinarith
    exact hs.trans hW

end PEqualNP.Outside.FP3Strategy
