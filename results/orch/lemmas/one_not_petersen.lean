import one_not_eliminate
import first_and_circuit

namespace PEqualNP.Outside.L_meta_2592_aux.OneNotPetersen

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open ConstantSweep OneNotEliminate Stronger.Extended Subgraphs

lemma first_and_value (a b : Fin 10) (mid : List Gate) (x : Fin 10 → Bool) :
    (run (⟨.and,[a.val,b.val]⟩ :: mid) (List.ofFn x)).getD 10 false = (x a && x b) := by
  have get (i : Fin 10) : (List.ofFn x).getD i.val false = x i := by
    fin_cases i <;> rfl
  have head : GateOp.and.eval ([a.val,b.val].map (fun i => (List.ofFn x).getD i false)) =
      (x a && x b) := by
    simp only [List.map_cons,List.map_nil,get,GateOp.eval,List.all_cons,List.all_nil,id,Bool.and_true]
  change (run mid (List.ofFn x ++ [_])).getD 10 false = _
  rw [head,run_prefix mid _ 10 (by simp)]
  simpa only [List.length_ofFn] using getD_last (List.ofFn x) (x a && x b) false

lemma first_adjacent_and_not_lower (a b : Fin 10) (hab : a ≠ b)
    (edge : ∀ x : Fin 10 → Bool, (x a && x b) ≤ f10 x)
    (mid suffix : List Gate) (outIdx : ℕ)
    (hp : ∀ q ∈ (⟨.and,[a.val,b.val]⟩ :: mid), good q)
    (hs : Monotone2 (Circuit.mk suffix outIdx))
    (correct : ∀ x, (Circuit.mk ((⟨.and,[a.val,b.val]⟩ :: mid) ++
      ⟨.not,[10]⟩ :: suffix) outIdx).eval (List.ofFn x) = f10 x)
    (used : ∃ q ∈ suffix, 11 + mid.length ∈ q.inputs) :
    20 ≤ (Circuit.mk ((⟨.and,[a.val,b.val]⟩ :: mid) ++
      ⟨.not,[10]⟩ :: suffix) outIdx).size := by
  have below : ∀ x, (run (⟨.and,[a.val,b.val]⟩ :: mid) (List.ofFn x)).getD 10 false ≤ f10 x := by
    intro x
    rw [first_and_value]
    exact edge x
  have nonconstant : ∃ x y : Fin 10 → Bool, f10 x ≠ f10 y := by
    refine ⟨fun _ => false, fun _ => true, ?_⟩
    decide +kernel
  have consumed : ∃ q ∈ suffix, 10 + (⟨GateOp.and,[a.val,b.val]⟩ :: mid).length ∈ q.inputs := by
    have h : 10 + (⟨GateOp.and,[a.val,b.val]⟩ :: mid).length = 11 + mid.length := by
      simp only [List.length_cons]
      omega
    rw [h]
    exact used
  obtain ⟨out,j,legal,saved,computes⟩ :=
    eliminate_consumed_dominated_not f10 (⟨.and,[a.val,b.val]⟩ :: mid) suffix 10 outIdx
      hp hs correct below consumed nonconstant
  have lower := first_and_size_lower
    (Circuit.mk ((⟨.and,[a.val,b.val]⟩ :: mid) ++ out) j) a b hab
    ⟨mid ++ out,rfl⟩ legal computes
  omega

lemma adjacent_implies (a b : Fin 10) (edge : adjacent a b = true) :
    ∀ x : Fin 10 → Bool, (x a && x b) ≤ f10 x := by
  intro x
  rw [Bool.le_iff_imp]
  intro h
  rw [f10_eq_edgeFun, edgeFun]
  have pair : x a = true ∧ x b = true := by simpa using h
  obtain ⟨ha,hb⟩ := pair
  exact decide_eq_true_eq.mpr ⟨a,b,edge,ha,hb⟩

end PEqualNP.Outside.L_meta_2592_aux.OneNotPetersen
