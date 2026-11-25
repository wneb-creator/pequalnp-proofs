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
  simp only [cutCost, cutCharge, notFlag, reads, Bool.false_eq_true,
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

lemma left_operand_twice (C : Circuit) (pre post : List Gate) (g : Gate)
    (split : C.gates = pre ++ g :: post)
    (shape : g.op = .and ∨ g.op = .or) (a b : ℕ) (inputs : g.inputs = [a, b])
    (u v : Fin 10) (different : u ≠ v) (sa sb : Bool)
    (origin : (pre.foldl originStep (List.ofFn fun i : Fin 10 => some i.val)).getD a none = some u.val)
    (valueA : ∀ x : Fin 10 → Bool,
      (pre.foldl gateStep (List.ofFn x)).getD a false = if sa then !(x u) else x u)
    (valueB : ∀ x : Fin 10 → Bool,
      (pre.foldl gateStep (List.ofFn x)).getD b false = if sb then !(x v) else x v)
    (correct : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x) :
    2 ≤ cutCost (List.ofFn fun i : Fin 10 => some i.val) u.val C.gates := by
  by_contra! small
  have flag : isNotGate g.op = false := by
    rcases shape with op | op <;> simp [isNotGate, op]
  have read : readsOrigin
      (pre.foldl originStep (List.ofFn fun i : Fin 10 => some i.val)) u.val g = true := by
    apply List.any_eq_true.mpr
    refine ⟨a, by simp [inputs], ?_⟩
    exact decide_eq_true origin
  have canal : ∃ z : Bool, ∀ x : Bool,
      g.op.eval [if sa then !x else x, if sb then !z else z] =
        g.op.eval [if sa then !false else false, if sb then !z else z] := by
    rcases shape with op | op <;> rw [op] <;> cases sa <;> cases sb <;> decide
  apply no_single_use C pre post g split flag u v different
    (fun x y => g.op.eval [if sa then !x else x, if sb then !y else y])
    canal ?_ read (by omega) correct
  intro x
  simp only [inputs, List.map_cons, List.map_nil, valueA, valueB]

lemma right_operand_twice (C : Circuit) (pre post : List Gate) (g : Gate)
    (split : C.gates = pre ++ g :: post)
    (shape : g.op = .and ∨ g.op = .or) (a b : ℕ) (inputs : g.inputs = [a, b])
    (u v : Fin 10) (different : u ≠ v) (sa sb : Bool)
    (origin : (pre.foldl originStep (List.ofFn fun i : Fin 10 => some i.val)).getD b none = some v.val)
    (valueA : ∀ x : Fin 10 → Bool,
      (pre.foldl gateStep (List.ofFn x)).getD a false = if sa then !(x u) else x u)
    (valueB : ∀ x : Fin 10 → Bool,
      (pre.foldl gateStep (List.ofFn x)).getD b false = if sb then !(x v) else x v)
    (correct : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x) :
    2 ≤ cutCost (List.ofFn fun i : Fin 10 => some i.val) v.val C.gates := by
  by_contra! small
  have flag : isNotGate g.op = false := by
    rcases shape with op | op <;> simp [isNotGate, op]
  have read : readsOrigin
      (pre.foldl originStep (List.ofFn fun i : Fin 10 => some i.val)) v.val g = true := by
    apply List.any_eq_true.mpr
    refine ⟨b, by simp [inputs], ?_⟩
    exact decide_eq_true origin
  have canal : ∃ z : Bool, ∀ x : Bool,
      g.op.eval [if sa then !z else z, if sb then !x else x] =
        g.op.eval [if sa then !z else z, if sb then !false else false] := by
    rcases shape with op | op <;> rw [op] <;> cases sa <;> cases sb <;> decide
  apply no_single_use C pre post g split flag v u different.symm
    (fun x y => g.op.eval [if sa then !y else y, if sb then !x else x])
    canal ?_ read (by omega) correct
  intro x
  simp only [inputs, List.map_cons, List.map_nil, valueA, valueB]

end PEqualNP.Outside.L_meta_2592_aux.SingleUseAny
