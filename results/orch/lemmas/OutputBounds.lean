import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3821_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def boundsPet (x : Fin 10 → Bool) : Bool :=
  (List.finRange 5).any fun i =>
    x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1)) ||
    x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i) ||
    x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2))

def boundsRun (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]) w

def boundsRead (D : Circuit) (x : Fin 10 → Bool) (i : ℕ) : Bool :=
  (D.wires (List.ofFn x)).getD i false

lemma boundsRun_length (gs : List Gate) (w : List Bool) :
    (boundsRun gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [boundsRun]
  | cons g gs ih =>
    change (boundsRun gs (w ++ [_])).length = w.length + (g :: gs).length
    rw [ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

lemma boundsRun_input (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (boundsRun gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (boundsRun gs (w ++ [_])).getD i false = w.getD i false
    rw [ih _ (by simp only [List.length_append, List.length_singleton]; omega)]
    exact List.getD_append _ _ _ _ hi

lemma boundsRead_input (D : Circuit) (x : Fin 10 → Bool) (i : Fin 10) :
    boundsRead D x i.val = x i := by
  change (boundsRun D.gates (List.ofFn x)).getD i.val false = x i
  rw [boundsRun_input D.gates (List.ofFn x) i.val (by simp)]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using i.isLt)]
  simp only [List.getElem_ofFn]

lemma boundsRead_lt (D : Circuit) (x : Fin 10 → Bool) (i : ℕ)
    (hi : boundsRead D x i = true) : i < 10 + D.size := by
  have hlen : (D.wires (List.ofFn x)).length = 10 + D.size := by
    simpa [Circuit.wires, Circuit.size, boundsRun] using
      boundsRun_length D.gates (List.ofFn x)
  by_contra h
  have hz : boundsRead D x i = false :=
    List.getD_eq_default _ _ (by omega)
  rw [hz] at hi
  contradiction

lemma boundsPet_singleton (i : Fin 10) :
    boundsPet (fun j => decide (j = i)) = false := by
  fin_cases i <;> decide

lemma boundsRead_gate (D : Circuit) (a b : ℕ)
    (hoff : ∀ x : Fin 10 → Bool, boundsPet x = false →
      (boundsRead D x a || boundsRead D x b) = false) : 10 ≤ a ∧ 10 ≤ b := by
  have notInput (i k : ℕ)
      (h : ∀ x : Fin 10 → Bool, boundsPet x = false →
        (boundsRead D x i || boundsRead D x k) = false) : 10 ≤ i := by
    by_contra hi
    have hil : i < 10 := by omega
    let x : Fin 10 → Bool := fun j => decide (j = (⟨i, hil⟩ : Fin 10))
    have hx : boundsPet x = false := boundsPet_singleton ⟨i, hil⟩
    have hv : boundsRead D x i = true := by
      simpa [x] using boundsRead_input D x ⟨i, hil⟩
    have he := h x hx
    simp only [hv, Bool.true_or] at he
    contradiction
  refine ⟨notInput a b hoff, notInput b a ?_⟩
  intro x hx
  simpa only [Bool.or_comm] using hoff x hx

lemma output_bounds (D : Circuit) (a b : ℕ)
    (ha : ∃ x : Fin 10 → Bool, boundsRead D x a = true ∧ boundsRead D x b = false)
    (hb : ∃ x : Fin 10 → Bool, boundsRead D x a = false ∧ boundsRead D x b = true)
    (hrows : ∀ x : Fin 10 → Bool,
      boundsPet x = false ∨ (List.ofFn x).count true ≤ 2 →
        (boundsRead D x a || boundsRead D x b) = boundsPet x) :
    10 ≤ a ∧ 10 ≤ b ∧ a < 10 + D.size ∧ b < 10 + D.size ∧ a ≠ b := by
  obtain ⟨x, hxa, hxb⟩ := ha
  obtain ⟨y, hya, hyb⟩ := hb
  have lower := boundsRead_gate D a b (fun z hz =>
    (hrows z (Or.inl hz)).trans hz)
  refine ⟨lower.1, lower.2, boundsRead_lt D x a hxa, boundsRead_lt D y b hyb, ?_⟩
  intro he
  subst b
  rw [hxa] at hxb
  contradiction

end PEqualNP.Outside.L_meta_3821_aux
