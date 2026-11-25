import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux.SensitivityExtension

def edge (x : Fin 9 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
    x 5 && x 7 || x 6 && x 8 || x 8 && x 5

abbrev sensitive (x : Fin 9 → Bool) : Prop :=
  edge x = false ∧ (x 4 || x 6 || x 7) = true

def obstruction (x : Fin 9 → Bool) : Bool :=
  edge x || (x 1 && x 3 && x 5) || (x 0 && x 2 && x 8)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma extension_certificate : ∀ x : Fin 9 → Bool, obstruction x = false →
    ([4, 6, 7] : List (Fin 9)).any
      (fun i => decide (sensitive (Function.update x i true))) = true := by
  decide +kernel

lemma sensitive_extension (x : Fin 9 → Bool) (hx : obstruction x = false) :
    ∃ y : Fin 9 → Bool, sensitive y ∧ ∀ i, x i = true → y i = true := by
  obtain ⟨i, _, hi⟩ := List.any_eq_true.mp (extension_certificate x hx)
  refine ⟨Function.update x i true, of_decide_eq_true hi, ?_⟩
  intro j hj
  by_cases hji : j = i
  · subst j
    simp
  · simpa [Function.update_of_ne hji] using hj

lemma monotone_mask_bound (h : (Fin 9 → Bool) → Bool)
    (hmono : ∀ x y : Fin 9 → Bool,
      (∀ i, x i = true → y i = true) → h x = true → h y = true)
    (hzero : ∀ x : Fin 9 → Bool, sensitive x → h x = false) :
    ∀ x : Fin 9 → Bool, h x = true → obstruction x = true := by
  intro x hx
  cases ho : obstruction x with
  | true => rfl
  | false =>
    obtain ⟨y, hy, hxy⟩ := sensitive_extension x ho
    have hp := hmono x y hxy hx
    have hn := hzero y hy
    exact False.elim (Bool.false_ne_true (hn.symm.trans hp))

end PEqualNP.Outside.L_meta_2592_aux.SensitivityExtension
