import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1031

open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma run_append (gs hs : List Gate) (w : List Bool) :
    run (gs ++ hs) w = run hs (run gs w) := by
  simp [run, List.foldl_append]

lemma edge_list_circuit {n : ℕ} (es : List (Fin n × Fin n)) :
    ∀ (m a : ℕ), n ≤ m → a < m →
      ∃ (gs : List Gate) (o : ℕ),
        (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
        o < m + gs.length ∧
        ∀ w : List Bool, w.length = m →
          (run gs w).getD o false =
            (w.getD a false || es.any (fun p => w.getD p.1.val false && w.getD p.2.val false)) := by
  induction es with
  | nil =>
      intro m a _ ha
      refine ⟨[], a, by simp, by simpa using ha, ?_⟩
      intro w _
      simp [run]
  | cons p es ih =>
      intro m a hnm ha
      obtain ⟨gs, o, hgs, ho, hev⟩ := ih (m + 2) (m + 1) (by omega) (by omega)
      let pre : List Gate := [⟨GateOp.and, [p.1.val, p.2.val]⟩, ⟨GateOp.or, [a, m]⟩]
      refine ⟨pre ++ gs, o, ?_, ?_, ?_⟩
      · intro g hg
        rcases List.mem_append.mp hg with hg | hg
        · simp only [pre, List.mem_cons, List.not_mem_nil, or_false] at hg
          rcases hg with rfl | rfl <;> simp
        · exact hgs g hg
      · simp only [List.length_append]
        have : pre.length = 2 := rfl
        omega
      · intro w hw
        let e := w.getD p.1.val false && w.getD p.2.val false
        have hstep : run pre w = w ++ [e, w.getD a false || e] := by
          have ha' : a < w.length := by omega
          simp [pre, run, GateOp.eval, List.getElem?_append_left ha', ← hw, e]
        have hlen : (run pre w).length = m + 2 := by rw [hstep]; simp [hw]
        have old (i : Fin n) : (run pre w).getD i.val false = w.getD i.val false := by
          rw [hstep]
          exact List.getD_append _ _ _ _ (by have := i.isLt; omega)
        have acc : (run pre w).getD (m + 1) false = (w.getD a false || e) := by
          rw [hstep]
          simp [← hw]
        rw [run_append, hev _ hlen, acc]
        have he : es.any (fun p => (run pre w).getD p.1.val false &&
            (run pre w).getD p.2.val false) =
            es.any (fun p => w.getD p.1.val false && w.getD p.2.val false) := by
          congr 1
          funext p
          rw [old, old]
        rw [he]
        simp [List.any_cons, Bool.or_assoc, e]

lemma graph_has_circuit (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ∃ C : Circuit,
      (∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
        decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) := by
  classical
  let es : List (Fin n × Fin n) := (Finset.univ.filter (fun p => G.Adj p.1 p.2)).toList
  obtain ⟨gs, o, hgs, _, hev⟩ := edge_list_circuit es (n + 1) n (by omega) (by omega)
  refine ⟨⟨⟨GateOp.or, []⟩ :: gs, o⟩, ?_, ?_⟩
  · intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · simp
    · exact hgs g hg
  · intro x
    change (run gs (List.ofFn x ++ [false])).getD o false = _
    rw [hev _ (by simp)]
    have old (i : Fin n) : (List.ofFn x ++ [false]).getD i.val false = x i := by
      rw [List.getD_append _ _ _ _ (by simpa using i.isLt)]
      simp
    have acc : (List.ofFn x ++ [false]).getD n false = false := by simp
    rw [acc, Bool.false_or]
    have he : es.any (fun p => (List.ofFn x ++ [false]).getD p.1.val false &&
        (List.ofFn x ++ [false]).getD p.2.val false) =
        es.any (fun p => x p.1 && x p.2) := by
      congr 1
      funext p
      rw [old, old]
    rw [he]
    apply Bool.eq_iff_iff.mpr
    simp [es, List.any_eq_true, Prod.exists, Bool.and_eq_true, and_assoc]


lemma graph_has_minimum (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ∃ C : Circuit,
      (∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) =
        decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) ∧
      ∀ D : Circuit,
        (∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
        (∀ x : Fin n → Bool, D.eval (List.ofFn x) =
          decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) →
        C.size ≤ D.size := by
  classical
  let Good (C : Circuit) : Prop :=
    (∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
        decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)
  have hex : ∃ s : ℕ, ∃ C : Circuit, Good C ∧ C.size = s := by
    obtain ⟨C, hC⟩ := graph_has_circuit n G
    exact ⟨C.size, C, hC, rfl⟩
  obtain ⟨C, hC, hs⟩ := Nat.find_spec hex
  refine ⟨C, hC.1, hC.2, ?_⟩
  intro D hD hf
  rw [hs]
  exact Nat.find_min' hex ⟨D, ⟨hD, hf⟩, rfl⟩

end PEqualNP.Outside.L_meta_1031
