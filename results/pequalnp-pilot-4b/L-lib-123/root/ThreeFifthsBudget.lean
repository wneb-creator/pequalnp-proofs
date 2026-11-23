import Mathlib

namespace PEqualNP.Outside.ThreeFifthsBudget

lemma budget_lower_bound (T B C W : ℕ)
    (controllers : T ≤ B * W)
    (checkpoints : T * B ≤ C * W)
    (localCheck : C * B ≤ W ^ 2) :
    T ^ 3 ≤ W ^ 5 := by
  have hsquare : T ^ 2 ≤ B ^ 2 * W ^ 2 := by
    simpa [mul_pow] using Nat.pow_le_pow_left controllers 2
  have hblock : T * B ^ 2 ≤ W ^ 3 := by
    calc
      T * B ^ 2 = T * B * B := by ring
      _ ≤ C * W * B := Nat.mul_le_mul_right B checkpoints
      _ = C * B * W := by ring
      _ ≤ W ^ 2 * W := Nat.mul_le_mul_right W localCheck
      _ = W ^ 3 := by ring
  calc
    T ^ 3 = T * T ^ 2 := by ring
    _ ≤ T * (B ^ 2 * W ^ 2) := Nat.mul_le_mul_left T hsquare
    _ = (T * B ^ 2) * W ^ 2 := by ring
    _ ≤ W ^ 3 * W ^ 2 := Nat.mul_le_mul_right (W ^ 2) hblock
    _ = W ^ 5 := by ring

lemma exact_balance (r : ℕ) :
    r ^ 5 = r ^ 2 * r ^ 3 ∧
    r ^ 5 * r ^ 2 = r ^ 4 * r ^ 3 ∧
    r ^ 4 * r ^ 2 = (r ^ 3) ^ 2 := by
  constructor
  · ring
  constructor <;> ring

lemma quadratic_conversion_cannot_save (N T B C W : ℕ)
    (hN : 1 < N) (hT : N ^ 2 ≤ T)
    (controllers : T ≤ B * W)
    (checkpoints : T * B ≤ C * W)
    (localCheck : C * B ≤ W ^ 2) : N < W := by
  by_contra! hW
  have hlower : N ^ 6 ≤ W ^ 5 := by
    calc
      N ^ 6 = (N ^ 2) ^ 3 := by ring
      _ ≤ T ^ 3 := Nat.pow_le_pow_left hT 3
      _ ≤ W ^ 5 := budget_lower_bound T B C W controllers checkpoints localCheck
  have hupper : W ^ 5 ≤ N ^ 5 := Nat.pow_le_pow_left hW 5
  have hstrict : N ^ 5 < N ^ 6 := Nat.pow_lt_pow_right hN (by omega)
  omega

end PEqualNP.Outside.ThreeFifthsBudget
