import PairCode
import FirstMerge

namespace PEqualNP.Outside.L_meta_2592_aux.FirstOrigin

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_2592_aux.FirstMerge
open PEqualNP.Outside.L_meta_2592_aux.Restriction

def OriginUnary (n : ℕ) (origins : List (Option ℕ))
    (w : (Fin n → Bool) → List Bool) : Prop :=
  (∀ x, (w x).length = origins.length) ∧
    ∀ j v, origins.getD j none = some v →
      ∃ h : v < n, ∃ f : Bool → Bool, ∀ x, (w x).getD j false = f (x ⟨v,h⟩)

lemma unary_step {n : ℕ} (origins : List (Option ℕ))
    (w : (Fin n → Bool) → List Bool) (g : Gate) (unary : OriginUnary n origins w) :
    OriginUnary n (originStep origins g) (fun x => gateStep (w x) g) := by
  refine ⟨fun x => by simp [originStep, gateStep, unary.1 x], ?_⟩
  intro j v hmem
  by_cases hj : j < origins.length
  · have old : origins.getD j none = some v := by
      simpa only [originStep, List.getD_append _ _ _ _ hj] using hmem
    obtain ⟨h,f,hf⟩ := unary.2 j v old
    refine ⟨h,f,fun x => ?_⟩
    have hjw : j < (w x).length := by rw [unary.1 x]; exact hj
    simpa only [gateStep, List.getD_append _ _ _ _ hjw] using hf x
  · by_cases he : j = origins.length
    · subst j
      have horig : gateOrigin origins g = some v := by simpa [originStep] using hmem
      cases ho : g.op <;> simp only [gateOrigin, ho] at horig
      all_goals try cases horig
      cases hi : g.inputs with
      | nil => simp [hi] at horig
      | cons i is =>
        have old : origins.getD i none = some v := by simpa [hi] using horig
        obtain ⟨h,f,hf⟩ := unary.2 i v old
        refine ⟨h, fun b => !(f b), fun x => ?_⟩
        have len := unary.1 x
        simp only [gateStep]
        rw [← len]
        rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self]
        simp only [List.getD_cons_zero]
        rw [ho, hi]
        change (!( (w x).getD i false)) = (!(f (x ⟨v,h⟩)))
        rw [hf]
    · have beyond : (originStep origins g).getD j none = none :=
        List.getD_eq_default _ _ (by simp [originStep]; omega)
      rw [beyond] at hmem
      cases hmem

lemma initial_unary (n : ℕ) :
    OriginUnary n (List.ofFn fun i : Fin n => some i.val) (fun x => List.ofFn x) := by
  refine ⟨fun x => by simp, ?_⟩
  intro j v hmem
  by_cases hj : j < n
  · have eq : j = v := by
      simpa [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hj] using hmem
    subst v
    refine ⟨hj, id, fun x => ?_⟩
    simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hj]
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hj)] at hmem
    cases hmem

lemma unary_tail {n : ℕ} (origins : List (Option ℕ))
    (w : (Fin n → Bool) → List Bool) (gs : List Gate)
    (unary : OriginUnary n origins w) :
    OriginUnary n (gs.foldl originStep origins) (fun x => gs.foldl gateStep (w x)) := by
  induction gs generalizing origins w with
  | nil => exact unary
  | cons g gs ih => exact ih _ _ (unary_step origins w g unary)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma petersen_cofactor_values : ∀ i : Fin 10, ∀ b : Bool,
    petersen (Function.update (fun _ => false) i b) = false ∧
      petersen (Function.update (fun _ => true) i b) = true := by
  decide +kernel

lemma output_origin_none (C : Circuit)
    (correct : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x) :
    (C.gates.foldl originStep (List.ofFn fun i : Fin 10 => some i.val)).getD C.output none = none := by
  have unary := unary_tail _ _ C.gates (initial_unary 10)
  cases ho : (C.gates.foldl originStep (List.ofFn fun i : Fin 10 => some i.val)).getD C.output none with
  | none => rfl
  | some v =>
    obtain ⟨hv,f,hf⟩ := unary.2 C.output v ho
    let i : Fin 10 := ⟨v,hv⟩
    have value (x : Fin 10 → Bool) : petersen x = f (x i) := by
      rw [← correct]
      exact hf x
    have low := value (Function.update (fun _ => false) i false)
    have high := value (Function.update (fun _ => true) i false)
    rw [(petersen_cofactor_values i false).1] at low
    rw [(petersen_cofactor_values i false).2] at high
    simp [Function.update] at low high
    exact Bool.noConfusion (low.symm.trans high)

end PEqualNP.Outside.L_meta_2592_aux.FirstOrigin
