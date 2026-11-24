import PEqualNP.Outside.L_meta_3451

namespace PEqualNP.Outside.L_meta_3451

open CircuitLowerBounds MetaComplexity NestedCover

lemma saReplacement (n : ℕ) (C : Circuit) (pre post : List Gate) (g r : Gate)
    (hsplit : C.gates = pre ++ g :: post)
    (hmono : Monotone2 C) (hreads : ReadsBack n C)
    (hrop : r.op = GateOp.and ∨ r.op = GateOp.or) (hrsize : r.inputs.length ≤ 2)
    (hrread : ∀ a ∈ r.inputs, a < n + pre.length)
    (hrle : ∀ z : Fin n → Bool,
      g.op.eval (g.inputs.map fun i => (pre.foldl decStep (List.ofFn z)).getD i false) = true →
      r.op.eval (r.inputs.map fun i => (pre.foldl decStep (List.ofFn z)).getD i false) = true)
    (hrsafe : ∀ z : Fin n → Bool,
      r.op.eval (r.inputs.map fun i => (pre.foldl decStep (List.ofFn z)).getD i false) = true →
      circuitFun n C z = true) :
    let D : Circuit := ⟨pre ++ r :: post, C.output⟩
    Monotone2 D ∧ ReadsBack n D ∧ D.size = C.size ∧
      (∀ z : Fin n → Bool, ∀ i,
        (C.wires (List.ofFn z)).getD i false = true →
        (D.wires (List.ofFn z)).getD i false = true) ∧
      (∀ z : Fin n → Bool, circuitFun n D z = circuitFun n C z) := by
  intro D
  have hm : Monotone2 D := by
    intro a ha
    change a ∈ pre ++ r :: post at ha
    simp only [List.mem_append, List.mem_cons] at ha
    rcases ha with ha | rfl | ha
    · exact hmono a (by rw [hsplit]; simp [ha])
    · exact ⟨hrop, hrsize⟩
    · exact hmono a (by rw [hsplit]; simp [ha])
  have hr : ReadsBack n D := by
    intro k hk a ha
    by_cases he : k = pre.length
    · subst k
      have har : a ∈ r.inputs := by simpa [gateAt, D] using ha
      exact hrread a har
    · have hg := lcGetDReplace pre post g r ⟨GateOp.or, []⟩ k he
      have hak : a ∈ (gateAt C k).inputs := by
        change a ∈ ((pre ++ r :: post).getD k ⟨GateOp.or, []⟩).inputs at ha
        rw [hg] at ha
        simpa only [gateAt, hsplit] using ha
      exact hreads k (by simpa [hsplit, D] using hk) a hak
  have hle : ∀ z : Fin n → Bool, ∀ i,
      (C.wires (List.ofFn z)).getD i false = true →
      (D.wires (List.ofFn z)).getD i false = true := by
    intro z
    change ∀ i, (C.gates.foldl decStep (List.ofFn z)).getD i false = true →
      ((pre ++ r :: post).foldl decStep (List.ofFn z)).getD i false = true
    rw [hsplit, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons]
    apply decFoldMono post (fun a ha => (hmono a (by rw [hsplit]; simp [ha])).1)
    · simp [decStep]
    · exact lcSnocMono _ _ _ (hrle z)
  refine ⟨hm, hr, by simp [Circuit.size, hsplit, D], hle, ?_⟩
  intro z
  cases hout : circuitFun n C z with
  | true => exact hle z C.output hout
  | false =>
    have hrf : r.op.eval
        (r.inputs.map fun i => (pre.foldl decStep (List.ofFn z)).getD i false) = false := by
      apply Bool.eq_false_iff.mpr
      intro ht
      have ho := hrsafe z ht
      rw [hout] at ho
      contradiction
    have hgf : g.op.eval
        (g.inputs.map fun i => (pre.foldl decStep (List.ofFn z)).getD i false) = false := by
      apply Bool.eq_false_iff.mpr
      intro ht
      have hr' := hrle z ht
      rw [hrf] at hr'
      contradiction
    have heq := lcReplaceEq n C pre post g r hsplit z (hrf.trans hgf.symm)
    change D.wires (List.ofFn z) = C.wires (List.ofFn z) at heq
    change (D.wires (List.ofFn z)).getD C.output false = false
    rw [heq]
    exact hout

lemma saSafeOperand (n : ℕ) (C : Circuit) (pre post : List Gate) (g : Gate)
    (hsplit : C.gates = pre ++ g :: post)
    (hmono : Monotone2 C) (hreads : ReadsBack n C)
    (hop : g.op = GateOp.and) (w : ℕ) (hmem : w ∈ g.inputs)
    (hsafe : ∀ z : Fin n → Bool,
      (C.wires (List.ofFn z)).getD w false = true → circuitFun n C z = true) :
    let D : Circuit := ⟨pre ++ ⟨GateOp.or, [w]⟩ :: post, C.output⟩
    Monotone2 D ∧ ReadsBack n D ∧ D.size = C.size ∧
      (∀ z : Fin n → Bool, ∀ i,
        (C.wires (List.ofFn z)).getD i false = true →
        (D.wires (List.ofFn z)).getD i false = true) ∧
      (∀ z : Fin n → Bool, circuitFun n D z = circuitFun n C z) := by
  have hw : w < n + pre.length := by
    apply hreads pre.length (by simp [hsplit])
    simpa [gateAt, hsplit] using hmem
  have hprefix (z : Fin n → Bool) :
      (C.wires (List.ofFn z)).getD w false =
        (pre.foldl decStep (List.ofFn z)).getD w false := by
    change (C.gates.foldl decStep (List.ofFn z)).getD w false = _
    rw [hsplit, List.foldl_append]
    apply lcRead
    simpa [lcLength] using hw
  apply saReplacement n C pre post g ⟨GateOp.or, [w]⟩ hsplit hmono hreads
    (Or.inr rfl) (by simp) (by simpa using hw)
  · intro z hz
    rw [hop] at hz
    simp only [GateOp.eval, List.all_map, List.all_eq_true] at hz
    simpa [GateOp.eval] using hz w hmem
  · intro z hz
    apply hsafe z
    rw [hprefix]
    simpa [GateOp.eval] using hz

end PEqualNP.Outside.L_meta_3451
