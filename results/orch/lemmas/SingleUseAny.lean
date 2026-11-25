import SingleUse

namespace PEqualNP.Outside.L_meta_2592_aux.SingleUseAny

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_2592_aux.FirstMerge
open PEqualNP.Outside.L_meta_2592_aux.FirstOrigin
open PEqualNP.Outside.L_meta_2592_aux.Restriction
open PEqualNP.Outside.L_meta_2592_aux.Compression

lemma costs_zero_around_reader (origins : List (Option ℕ)) (u : ℕ)
    (pre post : List Gate) (g : Gate)
    (cost : cutCost origins u (pre ++ g :: post) ≤ 1)
    (notFlag : isNotGate g.op = false)
    (reads : readsOrigin (pre.foldl originStep origins) u g = true) :
    cutCost origins u pre = 0 ∧
      cutCost (originStep (pre.foldl originStep origins) g) u post = 0 := by
  rw [cutCost_append] at cost
  simp only [cutCost, cutCharge, notFlag, reads, Bool.false_eq_true, Bool.true_eq,
    ↓reduceIte] at cost
  omega

lemma no_single_use (C : Circuit) (pre post : List Gate) (g : Gate)
    (split : C.gates = pre ++ g :: post) (notFlag : isNotGate g.op = false)
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
  obtain ⟨prefixU,tailU⟩ := costs_zero_around_reader origins u.val pre post g
    (by dsimp only [origins]; rw [← split]; exact costU) notFlag readU
  have preAgree := agree_tail origins u.val u.val (List.ofFn a) (List.ofFn z) pre
    (agreeOutside_initial 10 u u a z initial) prefixU prefixU
  have newOrigin : gateOrigin preOrig g = none := by
    cases ho : g.op <;> simp [gateOrigin, ho]
    simp [isNotGate, ho] at notFlag
  have middle : AgreeOutside (originStep preOrig g) u.val u.val
      (gateStep (pre.foldl gateStep (List.ofFn a)) g)
      (gateStep (pre.foldl gateStep (List.ofFn z)) g) := by
    simpa only [originStep, newOrigin, gateStep] using
      agree_snoc preOrig u.val u.val _ _ _ _ preAgree newEq
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

end PEqualNP.Outside.L_meta_2592_aux.SingleUseAny
