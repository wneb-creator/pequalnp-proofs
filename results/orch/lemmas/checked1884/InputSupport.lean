import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1884_aux.InputSupport

open PEqualNP.CircuitLowerBounds

def pet (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
  x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
  x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 ||
  x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def neighbour : Fin 10 → Fin 10 := ![1, 2, 3, 4, 0, 0, 1, 2, 3, 4]

def low (v : Fin 10) (i : Fin 10) : Bool := decide (i = neighbour v)

def high (v : Fin 10) (i : Fin 10) : Bool :=
  if i = v then true else low v i

lemma witness_values : ∀ v, pet (low v) = false ∧ pet (high v) = true := by
  decide +kernel

lemma agree_off (v i : Fin 10) (hi : i ≠ v) : low v i = high v i := by
  simp [high, hi]

def Correct (C : Circuit) (r : Fin 10 → Fin 10) (f : Bool → Bool) : Prop :=
  ∀ x : Fin 10 → Bool,
    C.eval (List.ofFn (x ∘ r) ++ [f (x 0)]) = pet x

lemma missing_forces_unary_change (C : Circuit) (r : Fin 10 → Fin 10)
    (f : Bool → Bool) (hc : Correct C r f) (v : Fin 10)
    (hm : ∀ i, r i ≠ v) : f (low v 0) ≠ f (high v 0) := by
  intro he
  have hi : List.ofFn (low v ∘ r) = List.ofFn (high v ∘ r) := by
    congr 1
    funext i
    exact agree_off v (r i) (hm i)
  have hv := witness_values v
  have hl := hc (low v)
  have hh := hc (high v)
  rw [hi, he] at hl
  rw [hh, hv.1, hv.2] at hl
  contradiction

lemma required_nonzero (C : Circuit) (r : Fin 10 → Fin 10)
    (f : Bool → Bool) (hc : Correct C r f) (v : Fin 10) (hv : v ≠ 0) :
    ∃ i, r i = v := by
  by_contra h
  push Not at h
  exact missing_forces_unary_change C r f hc v h
    (congrArg f (agree_off v 0 (Ne.symm hv)))

lemma missing_zero_nonconstant (C : Circuit) (r : Fin 10 → Fin 10)
    (f : Bool → Bool) (hc : Correct C r f) (hm : ∀ i, r i ≠ 0) :
    f false ≠ f true := by
  simpa [low, high, neighbour] using missing_forces_unary_change C r f hc 0 hm

lemma constant_unary_surjective (C : Circuit) (r : Fin 10 → Fin 10)
    (f : Bool → Bool) (hc : Correct C r f) (hf : f false = f true) :
    Function.Surjective r := by
  intro v
  by_cases hv : v = 0
  · subst v
    by_contra h
    push Not at h
    exact missing_zero_nonconstant C r f hc h hf
  · exact required_nonzero C r f hc v hv

lemma constant_unary_bijective (C : Circuit) (r : Fin 10 → Fin 10)
    (f : Bool → Bool) (hc : Correct C r f) (hf : f false = f true) :
    Function.Bijective r := by
  have hs := constant_unary_surjective C r f hc hf
  exact ⟨Finite.injective_iff_surjective.mpr hs, hs⟩

lemma missing_zero_id_or_not (C : Circuit) (r : Fin 10 → Fin 10)
    (f : Bool → Bool) (hc : Correct C r f) (hm : ∀ i, r i ≠ 0) :
    (∀ b, f b = b) ∨ (∀ b, f b = !b) := by
  have hn := missing_zero_nonconstant C r f hc hm
  cases hf : f false <;> cases ht : f true <;> simp_all

end PEqualNP.Outside.L_meta_1884_aux.InputSupport
