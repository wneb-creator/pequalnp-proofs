import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1400

-- an input is coded by a natural number, bit i is the value of variable i
def dec (n : ℕ) : Fin 10 → Bool := fun i => n.testBit i.val

-- a necessary condition for a depth k formula to be true on A and false on B
def sol : ℕ → List ℕ → List ℕ → Bool
  | 0, A, B => (List.range 10).any
      (fun i => A.all (fun a => a.testBit i) && B.all (fun b => !b.testBit i))
  | k + 1, A, B => sol k A B
      || A.sublists.any (fun S => sol k S B && sol k (A.filter (fun a => !S.contains a)) B)
      || B.sublists.any (fun S => sol k A S && sol k A (B.filter (fun b => !S.contains b)))

def T (k : ℕ) : Set ((Fin 10 → Bool) → Bool) :=
  {g | ∀ A B : List ℕ, (∀ a ∈ A, g (dec a) = true) → (∀ b ∈ B, g (dec b) = false) →
    sol k A B = true}

theorem T0 (i : Fin 10) : (fun x : Fin 10 → Bool => x i) ∈ T 0 := by
  intro A B hA hB
  simp only [sol, List.any_eq_true, List.mem_range, Bool.and_eq_true, List.all_eq_true]
  refine ⟨i.val, i.isLt, fun a ha => hA a ha, fun b hb => ?_⟩
  have h := hB b hb
  simp only [dec] at h
  simp [h]

theorem Tstep (k : ℕ) (f : (Fin 10 → Bool) → Bool) (hf : f ∈ T k) : f ∈ T (k + 1) := by
  intro A B hA hB
  simp only [sol, Bool.or_eq_true]
  exact Or.inl (Or.inl (hf A B hA hB))

theorem Tor (k : ℕ) (f g : (Fin 10 → Bool) → Bool) (hf : f ∈ T k) (hg : g ∈ T k) :
    (fun y : Fin 10 → Bool => f y || g y) ∈ T (k + 1) := by
  intro A B hA hB
  simp only [sol, Bool.or_eq_true]
  refine Or.inl (Or.inr ?_)
  rw [List.any_eq_true]
  refine ⟨A.filter (fun a => f (dec a)), List.mem_sublists.2 List.filter_sublist, ?_⟩
  rw [Bool.and_eq_true]
  constructor
  · apply hf
    · intro a ha
      exact (List.mem_filter.1 ha).2
    · intro b hb
      have h := hB b hb
      simp only [Bool.or_eq_false_iff] at h
      exact h.1
  · apply hg
    · intro a ha
      obtain ⟨haA, hn⟩ := List.mem_filter.1 ha
      have h := hA a haA
      simp only [Bool.or_eq_true] at h
      rcases h with h | h
      · exfalso
        have hm : a ∈ A.filter (fun a => f (dec a)) := List.mem_filter.2 ⟨haA, h⟩
        simp [hm] at hn
      · exact h
    · intro b hb
      have h := hB b hb
      simp only [Bool.or_eq_false_iff] at h
      exact h.2

theorem Tand (k : ℕ) (f g : (Fin 10 → Bool) → Bool) (hf : f ∈ T k) (hg : g ∈ T k) :
    (fun y : Fin 10 → Bool => f y && g y) ∈ T (k + 1) := by
  intro A B hA hB
  simp only [sol, Bool.or_eq_true]
  refine Or.inr ?_
  rw [List.any_eq_true]
  refine ⟨B.filter (fun b => !f (dec b)), List.mem_sublists.2 List.filter_sublist, ?_⟩
  rw [Bool.and_eq_true]
  constructor
  · apply hf
    · intro a ha
      have h := hA a ha
      simp only [Bool.and_eq_true] at h
      exact h.1
    · intro b hb
      have h := (List.mem_filter.1 hb).2
      simpa using h
  · apply hg
    · intro a ha
      have h := hA a ha
      simp only [Bool.and_eq_true] at h
      exact h.2
    · intro b hb
      obtain ⟨hbB, hn⟩ := List.mem_filter.1 hb
      have h := hB b hbB
      simp only [Bool.and_eq_false_iff] at h
      rcases h with h | h
      · exfalso
        have hm : b ∈ B.filter (fun b => !f (dec b)) := List.mem_filter.2 ⟨hbB, by simp [h]⟩
        simp [hm] at hn
      · exact h

theorem hard : sol 4 [99, 198, 396, 792, 561] [505, 981, 687, 847, 762] = false := by
  decide +kernel

end PEqualNP.Outside.L_meta_1400

theorem PEqualNP.Outside.L_meta_1400 : ¬ (∀ T : ℕ → Set ((Fin 10 → Bool) → Bool), (∀ i : Fin 10, (fun x : Fin 10 → Bool => x i) ∈ T 0) → (∀ (k : ℕ) (f : (Fin 10 → Bool) → Bool), f ∈ T k → f ∈ T (k + 1)) → (∀ (k : ℕ) (f g : (Fin 10 → Bool) → Bool), f ∈ T k → g ∈ T k → (fun y : Fin 10 → Bool => f y && g y) ∈ T (k + 1) ∧ (fun y : Fin 10 → Bool => f y || g y) ∈ T (k + 1)) → (fun z : Fin 10 → Bool => (z 0 && z 5 && z 1 && z 6) || (z 1 && z 6 && z 2 && z 7) || (z 2 && z 7 && z 3 && z 8) || (z 3 && z 8 && z 4 && z 9) || (z 4 && z 9 && z 0 && z 5)) ∈ T 4) := by
  intro h
  have h4 := h PEqualNP.Outside.L_meta_1400.T PEqualNP.Outside.L_meta_1400.T0
    PEqualNP.Outside.L_meta_1400.Tstep
    (fun k f g hf hg => ⟨PEqualNP.Outside.L_meta_1400.Tand k f g hf hg,
      PEqualNP.Outside.L_meta_1400.Tor k f g hf hg⟩)
    [99, 198, 396, 792, 561] [505, 981, 687, 847, 762] (by decide +kernel) (by decide +kernel)
  rw [PEqualNP.Outside.L_meta_1400.hard] at h4
  exact Bool.false_ne_true h4
