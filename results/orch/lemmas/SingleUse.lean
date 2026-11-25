import Compression

namespace PEqualNP.Outside.L_meta_2592_aux.SingleUse

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_2592_aux.FirstMerge
open PEqualNP.Outside.L_meta_2592_aux.FirstOrigin
open PEqualNP.Outside.L_meta_2592_aux.Restriction
open PEqualNP.Outside.L_meta_2592_aux.Compression

lemma no_first_single_use (C : Circuit) (pre post : List Gate) (g : Gate)
    (split : C.gates = pre ++ g :: post)
    (allNot : ∀ q ∈ pre, q.op = .not) (notFlag : isNotGate g.op = false)
    (u v : Fin 10) (hne : u ≠ v) (code : Bool → Bool → Bool)
    (canal : ∃ b : Bool, ∀ a : Bool, code a b = code false b)
    (factor : ∀ x : Fin 10 → Bool,
      g.op.eval (g.inputs.map fun i => (pre.foldl gateStep (List.ofFn x)).getD i false) =
        code (x u) (x v))
    (readU : readsOrigin (pre.foldl originStep (List.ofFn fun i : Fin 10 => some i.val)) u.val g = true)
    (costU : cutCost (List.ofFn fun i : Fin 10 => some i.val) u.val C.gates ≤ 1)
    (correct : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x) : False := by
  obtain ⟨b,hb⟩ := canal
  obtain ⟨w,hw⟩ := left_probe u v hne
  let a := probe u v w false b
  let z := probe u v w true b
  have initial : ∀ i : Fin 10, i ≠ u → i ≠ u → a i = z i := by
    intro i hi _
    simp [a,z,probe,hi]
  have newEq : g.op.eval (g.inputs.map fun i => (pre.foldl gateStep (List.ofFn a)).getD i false) =
      g.op.eval (g.inputs.map fun i => (pre.foldl gateStep (List.ofFn z)).getD i false) := by
    rw [factor, factor]
    simpa [a,z,probe,hne.symm] using (hb true).symm
  let origins := List.ofFn fun i : Fin 10 => some i.val
  let preOrig := pre.foldl originStep origins
  have preAgree := agree_tail origins u.val u.val (List.ofFn a) (List.ofFn z) pre
    (agreeOutside_initial 10 u u a z initial)
    (cutCost_not_prefix origins u.val pre allNot) (cutCost_not_prefix origins u.val pre allNot)
  have newOrigin : gateOrigin preOrig g = none := by
    cases ho : g.op <;> simp [gateOrigin, ho]
    simp [isNotGate, ho] at notFlag
  have middle : AgreeOutside (originStep preOrig g) u.val u.val
      (gateStep (pre.foldl gateStep (List.ofFn a)) g)
      (gateStep (pre.foldl gateStep (List.ofFn z)) g) := by
    simpa only [originStep, newOrigin, gateStep] using
      agree_snoc preOrig u.val u.val _ _ _ _ preAgree newEq
  have tailU : cutCost (originStep preOrig g) u.val post = 0 :=
    suffix_cost_zero origins u.val pre post g
      (by dsimp only [origins]; rw [← split]; exact costU) notFlag readU
  have final := agree_tail (originStep preOrig g) u.val u.val _ _ post middle tailU tailU
  have originsFull : C.gates.foldl originStep origins = post.foldl originStep (originStep preOrig g) := by
    rw [split, List.foldl_append]
    rfl
  have wiresFull (x : Fin 10 → Bool) : C.wires (List.ofFn x) =
      post.foldl gateStep (gateStep (pre.foldl gateStep (List.ofFn x)) g) := by
    change C.gates.foldl gateStep (List.ofFn x) = _
    rw [split, List.foldl_append]
    rfl
  rw [← originsFull, ← wiresFull a, ← wiresFull z] at final
  have outNone := output_origin_none C correct
  have eq := final.2.2 C.output (by rw [outNone]; simp) (by rw [outNone]; simp)
  change C.eval (List.ofFn a) = C.eval (List.ofFn z) at eq
  rw [correct, correct] at eq
  change petersen (probe u v w false b) = petersen (probe u v w true b) at eq
  rw [hw,hw] at eq
  cases eq

lemma signed_and_or_canal : ∀ join sa sb : Bool,
    ∃ b : Bool, ∀ a : Bool,
      (if join then (a != sa) || (b != sb) else (a != sa) && (b != sb)) =
        (if join then (false != sa) || (b != sb) else (false != sa) && (b != sb)) := by
  decide

end PEqualNP.Outside.L_meta_2592_aux.SingleUse
