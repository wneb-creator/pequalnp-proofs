import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12179.TableFacts

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (3892346880 * 2 ^ 32 + 2147483648)
    (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma target_eq_threshold : ∀ x : Fin 6 → Bool,
    target x = (x 3 && decide (4 ≤
      (Finset.univ.filter fun i : Fin 6 => i ≠ 3 ∧ x i = true).card)) := by
  decide

lemma target_monotone (x y : Fin 6 → Bool)
    (hxy : ∀ i, x i = true → y i = true) :
    target x = true → target y = true := by
  rw [target_eq_threshold, target_eq_threshold]
  simp only [Bool.and_eq_true_iff, decide_eq_true_eq]
  rintro ⟨hx3, hxcount⟩
  refine ⟨hxy 3 hx3, hxcount.trans ?_⟩
  apply Finset.card_le_card
  intro i hi
  obtain ⟨_, hi3, hxi⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi3, hxy i hxi⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma target_true_iff_index (x : Fin 6 → Bool) :
    target x = true ↔
      (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) ∈
        ({31, 47, 59, 61, 62, 63} : Finset ℕ) := by
  revert x
  decide

end PEqualNP.Outside.L_meta_12179.TableFacts
