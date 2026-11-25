import dominated_source_witness

namespace PEqualNP.Outside.L_meta_1886_aux.PrefixMonotone

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2592_aux

lemma ofFn_le {n : ℕ} (x y : Fin n → Bool) (h : ∀ i, x i ≤ y i) :
    List.Forall₂ (· ≤ ·) (List.ofFn x) (List.ofFn y) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ,List.ofFn_succ]
    exact List.Forall₂.cons (h 0) (ih (fun i => x i.succ) (fun i => y i.succ) (fun i => h i.succ))

lemma supplied_inputs_le (p : Fin 10 → Fin 10) (x y : Fin 10 → Bool)
    (h : ∀ i, x i ≤ y i) :
    List.Forall₂ (· ≤ ·) (List.ofFn (x ∘ p) ++ [x 0 && x 1])
      (List.ofFn (y ∘ p) ++ [y 0 && y 1]) := by
  have hp := ofFn_le (x ∘ p) (y ∘ p) (fun i => h (p i))
  have hb : (x 0 && x 1) ≤ (y 0 && y 1) := by
    have h0 := h 0
    have h1 := h 1
    cases hx0 : x 0 <;> cases hx1 : x 1 <;>
      cases hy0 : y 0 <;> cases hy1 : y 1 <;> simp_all [Bool.le_iff_imp]
  exact List.rel_append hp (.cons hb .nil)

lemma source_monotone (p : Fin 10 → Fin 10) (pre : List Gate) (source : ℕ)
    (mono : Monotone2 (Circuit.mk pre source)) :
    ∀ x y : Fin 10 → Bool, (∀ i, x i ≤ y i) →
      (Circuit.mk pre source).eval (List.ofFn (x ∘ p) ++ [x 0 && x 1]) ≤
        (Circuit.mk pre source).eval (List.ofFn (y ∘ p) ++ [y 0 && y 1]) := by
  intro x y h
  exact OneNot.circuit_le (Circuit.mk pre source) mono (supplied_inputs_le p x y h)

end PEqualNP.Outside.L_meta_1886_aux.PrefixMonotone
