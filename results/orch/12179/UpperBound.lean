import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12179

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (3892346880 * 2 ^ 32 + 2147483648)
    (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

lemma target_threshold : ∀ x : Fin 6 → Bool,
    target x = (x 3 && decide
      (4 ≤ (Finset.univ.filter fun i : Fin 6 => i ≠ 3 ∧ x i = true).card)) := by
  decide

lemma target_zero_guard : ∀ x : Fin 6 → Bool, x 3 = false → target x = false := by
  intro x h
  rw [target_threshold, h]
  rfl

lemma target_one_guard : ∀ x : Fin 6 → Bool, x 3 = true →
    target x = decide
      (4 ≤ (Finset.univ.filter fun i : Fin 6 => i ≠ 3 ∧ x i = true).card) := by
  intro x h
  rw [target_threshold, h]
  rfl

lemma target_forces_guard : ∀ x : Fin 6 → Bool, target x = true → x 3 = true := by
  intro x h
  rw [target_threshold, Bool.and_eq_true] at h
  exact h.1

end PEqualNP.Outside.L_meta_12179


namespace PEqualNP.Outside.L_meta_12179

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def monoEleven : Circuit :=
  ⟨[⟨.and, [0, 1]⟩, ⟨.and, [4, 5]⟩, ⟨.and, [6, 7]⟩,
    ⟨.or, [0, 1]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [6, 10]⟩,
    ⟨.and, [7, 9]⟩, ⟨.or, [11, 12]⟩, ⟨.and, [2, 13]⟩,
    ⟨.or, [8, 14]⟩, ⟨.and, [3, 15]⟩], 16⟩

lemma monoEleven_size : monoEleven.size = 11 := rfl

lemma monoEleven_monotone : Monotone2 monoEleven := by
  simp [Monotone2, monoEleven]

lemma monoEleven_correct : ∀ x : Fin 6 → Bool,
    monoEleven.eval (List.ofFn x) = target x := by
  decide

lemma monotone_replacement_of_lower_bound
    (hlower : ∀ s, HasCircuitSize 6 target s → 11 ≤ s) :
    ∀ s, HasCircuitSize 6 target s →
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧
        ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x := by
  intro s hs
  exact ⟨monoEleven, monoEleven_monotone,
    monoEleven_size ▸ hlower s hs, monoEleven_correct⟩

end PEqualNP.Outside.L_meta_12179
