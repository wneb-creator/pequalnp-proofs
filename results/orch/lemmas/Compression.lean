import FirstOrigin
import CutCost

namespace PEqualNP.Outside.L_meta_2592_aux.Compression

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_2592_aux.FirstMerge
open PEqualNP.Outside.L_meta_2592_aux.FirstOrigin
open PEqualNP.Outside.L_meta_2592_aux.Restriction

lemma agree_snoc (origins : List (Option ℕ)) (u v : ℕ) (a b : List Bool) (za zb : Bool)
    (agree : AgreeOutside origins u v a b) (eq : za = zb) :
    AgreeOutside (origins ++ [none]) u v (a ++ [za]) (b ++ [zb]) := by
  have la := agree.1
  have lb := agree.2.1
  refine ⟨by simp [la], by simp [lb], ?_⟩
  intro i hu hv
  by_cases hi : i < origins.length
  · have ai : i < a.length := by omega
    have bi : i < b.length := by omega
    have hu' : origins.getD i none ≠ some u := by
      simpa only [List.getD_append _ _ _ _ hi] using hu
    have hv' : origins.getD i none ≠ some v := by
      simpa only [List.getD_append _ _ _ _ hi] using hv
    simpa only [List.getD_append _ _ _ _ ai, List.getD_append _ _ _ _ bi]
      using agree.2.2 i hu' hv'
  · by_cases he : i = origins.length
    · subst i
      rw [List.getD_append_right _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by omega)]
      have ha : origins.length - a.length = 0 := by omega
      have hb : origins.length - b.length = 0 := by omega
      simpa only [ha, hb, List.getD_cons_zero] using eq
    · rw [List.getD_eq_default _ _ (by simp; omega),
          List.getD_eq_default _ _ (by simp; omega)]

lemma no_first_compression (C : Circuit) (pre post : List Gate) (g : Gate)
    (split : C.gates = pre ++ g :: post)
    (allNot : ∀ q ∈ pre, q.op = .not) (notFlag : isNotGate g.op = false)
    (u v : Fin 10) (hne : u ≠ v) (code : Bool → Bool → Bool)
    (factor : ∀ x : Fin 10 → Bool,
      g.op.eval (g.inputs.map fun i => (pre.foldl gateStep (List.ofFn x)).getD i false) =
        code (x u) (x v))
    (readU : readsOrigin (pre.foldl originStep (List.ofFn fun i : Fin 10 => some i.val)) u.val g = true)
    (readV : readsOrigin (pre.foldl originStep (List.ofFn fun i : Fin 10 => some i.val)) v.val g = true)
    (costU : cutCost (List.ofFn fun i : Fin 10 => some i.val) u.val C.gates ≤ 1)
    (costV : cutCost (List.ofFn fun i : Fin 10 => some i.val) v.val C.gates ≤ 1)
    (correct : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x) : False := by
  obtain ⟨a,b,initial,codeEq,different⟩ := no_pair_code u v hne code
  let origins := List.ofFn fun i : Fin 10 => some i.val
  let preOrig := pre.foldl originStep origins
  have preAgree := agree_tail origins u.val v.val (List.ofFn a) (List.ofFn b) pre
    (agreeOutside_initial 10 u v a b initial)
    (cutCost_not_prefix origins u.val pre allNot) (cutCost_not_prefix origins v.val pre allNot)
  have newEq : g.op.eval (g.inputs.map fun i => (pre.foldl gateStep (List.ofFn a)).getD i false) =
      g.op.eval (g.inputs.map fun i => (pre.foldl gateStep (List.ofFn b)).getD i false) := by
    rw [factor, factor, codeEq]
  have newOrigin : gateOrigin preOrig g = none := by
    cases ho : g.op <;> simp [gateOrigin, ho]
    simp [isNotGate, ho] at notFlag
  have middle : AgreeOutside (originStep preOrig g) u.val v.val
      (gateStep (pre.foldl gateStep (List.ofFn a)) g)
      (gateStep (pre.foldl gateStep (List.ofFn b)) g) := by
    simpa only [originStep, newOrigin, gateStep] using
      agree_snoc preOrig u.val v.val _ _ _ _ preAgree newEq
  have tailU : cutCost (originStep preOrig g) u.val post = 0 :=
    suffix_cost_zero origins u.val pre post g (by dsimp only [origins]; rw [← split]; exact costU) notFlag readU
  have tailV : cutCost (originStep preOrig g) v.val post = 0 :=
    suffix_cost_zero origins v.val pre post g (by dsimp only [origins]; rw [← split]; exact costV) notFlag readV
  have final := agree_tail (originStep preOrig g) u.val v.val _ _ post middle tailU tailV
  have originsFull : C.gates.foldl originStep origins = post.foldl originStep (originStep preOrig g) := by
    rw [split, List.foldl_append]
    rfl
  have wiresFull (x : Fin 10 → Bool) : C.wires (List.ofFn x) =
      post.foldl gateStep (gateStep (pre.foldl gateStep (List.ofFn x)) g) := by
    change C.gates.foldl gateStep (List.ofFn x) = _
    rw [split, List.foldl_append]
    rfl
  rw [← originsFull, ← wiresFull a, ← wiresFull b] at final
  have outNone := output_origin_none C correct
  have eq := final.2.2 C.output (by rw [outNone]; simp) (by rw [outNone]; simp)
  change C.eval (List.ofFn a) = C.eval (List.ofFn b) at eq
  rw [correct, correct] at eq
  exact different eq

end PEqualNP.Outside.L_meta_2592_aux.Compression
