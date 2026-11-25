import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2962.AbsorbWrapper

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadTwo PEqualNP.Core PEqualNP.SplitCount

def wrap {n : ℕ} (C : Circuit) (v : Fin n) : Circuit :=
  ⟨C.gates ++ [⟨.or, [C.output, v.val]⟩,
    ⟨.and, [n + C.gates.length, C.output]⟩], n + C.gates.length + 1⟩

lemma fold_length (gs : List Gate) (acc : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc).length =
      acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih => simp only [List.foldl_cons, ih, List.length_append,
      List.length_cons, List.length_nil]; omega

lemma fold_prefix (gs : List Gate) (acc : List Bool) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) acc).getD i false =
      acc.getD i false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by simp only [List.length_append, List.length_singleton]; omega)]
    simp [List.getD, List.getElem?_append_left hi]

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := fold_length _ _

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (v : Fin n) :
    wval C x v.val = x v := by
  unfold wval Circuit.wires
  rw [fold_prefix _ _ _ (by simp)]
  simp [List.getD]

lemma prefix_value {n : ℕ} (C : Circuit) (v : Fin n) (x : Fin n → Bool)
    (i : ℕ) (hi : i < n + C.gates.length) :
    wval (wrap C v) x i = wval C x i := by
  unfold wval wrap Circuit.wires
  rw [List.foldl_append]
  apply fold_prefix
  simpa only [fold_length, List.length_ofFn] using hi

lemma wires_wrap {n : ℕ} (C : Circuit) (v : Fin n) (x : Fin n → Bool)
    (hout : C.output < n + C.gates.length) :
    (wrap C v).wires (List.ofFn x) = C.wires (List.ofFn x) ++
      [circuitFun n C x || x v, circuitFun n C x] := by
  have hlen := wires_length C (List.ofFn x)
  simp only [List.length_ofFn] at hlen
  have hv := input_value C x v
  unfold wval at hv
  have ho : (C.wires (List.ofFn x)).getD C.output false = circuitFun n C x := rfl
  have hop : ((C.wires (List.ofFn x)) ++ [circuitFun n C x || x v]).getD C.output false =
      circuitFun n C x := by
    simpa [List.getD, List.getElem?_append_left (by omega : C.output <
      (C.wires (List.ofFn x)).length)] using ho
  have hqp : ((C.wires (List.ofFn x)) ++ [circuitFun n C x || x v]).getD
      (n + C.gates.length) false = (circuitFun n C x || x v) := by
    rw [← hlen]
    cases circuitFun n C x <;> cases x v <;> simp [List.getD]
  change (C.gates ++ ([⟨.or, [C.output, v.val]⟩,
      ⟨.and, [n + C.gates.length, C.output]⟩] : List Gate)).foldl
      (fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (List.ofFn x) = _
  rw [List.foldl_append]
  change ([⟨.or, [C.output, v.val]⟩, ⟨.and, [n + C.gates.length, C.output]⟩] : List Gate).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (C.wires (List.ofFn x)) = _
  simp only [List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil,
    GateOp.eval, List.any_cons, List.any_nil, List.all_cons, List.all_nil,
    Bool.or_false, Bool.and_true, ho, hv]
  change (C.wires (List.ofFn x) ++ [circuitFun n C x || x v]) ++
      [((C.wires (List.ofFn x) ++ [circuitFun n C x || x v]).getD
        (n + C.gates.length) false) &&
       ((C.wires (List.ofFn x) ++ [circuitFun n C x || x v]).getD C.output false)] = _
  rw [hqp, hop]
  cases circuitFun n C x <;> cases x v <;> simp

lemma correct {n : ℕ} (C : Circuit) (v : Fin n)
    (hout : C.output < n + C.gates.length) :
    circuitFun n (wrap C v) = circuitFun n C := by
  funext x
  unfold circuitFun Circuit.eval
  rw [wires_wrap C v x hout]
  simp [wrap, List.getD, wires_length, circuitFun, Circuit.eval]

lemma q_value {n : ℕ} (C : Circuit) (v : Fin n) (x : Fin n → Bool)
    (hout : C.output < n + C.gates.length) :
    gateVal n (wrap C v) C.gates.length x = (circuitFun n C x || x v) := by
  unfold gateVal
  rw [wires_wrap C v x hout]
  cases circuitFun n C x <;> cases x v <;> simp [List.getD, wires_length]

lemma r_value {n : ℕ} (C : Circuit) (v : Fin n) (x : Fin n → Bool)
    (hout : C.output < n + C.gates.length) :
    gateVal n (wrap C v) (C.gates.length + 1) x = circuitFun n C x := by
  change circuitFun n (wrap C v) x = circuitFun n C x
  rw [correct C v hout]

lemma gate_prefix {n : ℕ} (C : Circuit) (v : Fin n) {j : ℕ} (hj : j < C.gates.length) :
    gateAt (wrap C v) j = gateAt C j := by
  simp [gateAt, wrap, List.getD, List.getElem?_append_left hj]

lemma gate_q {n : ℕ} (C : Circuit) (v : Fin n) :
    gateAt (wrap C v) C.gates.length = ⟨.or, [C.output, v.val]⟩ := by
  unfold gateAt wrap
  simp only
  unfold List.getD
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp

lemma gate_r {n : ℕ} (C : Circuit) (v : Fin n) :
    gateAt (wrap C v) (C.gates.length + 1) = ⟨.and, [n + C.gates.length, C.output]⟩ := by
  unfold gateAt wrap
  simp only
  unfold List.getD
  rw [List.getElem?_append_right (by omega)]
  simp

lemma ao2 {n : ℕ} (C : Circuit) (v : Fin n) (hAO : IsAO2 n C)
    (hout : C.output < n + C.gates.length) : IsAO2 n (wrap C v) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hAO.1 g hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl <;> simp
  · intro j hj i hi
    by_cases old : j < C.gates.length
    · rw [gate_prefix C v old] at hi
      exact hAO.2.1 j old i hi
    · have hj' : j = C.gates.length ∨ j = C.gates.length + 1 := by
        simp only [wrap, List.length_append, List.length_cons, List.length_nil] at hj
        omega
      rcases hj' with rfl | rfl
      · rw [gate_q] at hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · exact hout
        · have := v.isLt; omega
      · rw [gate_r] at hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> omega
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hAO.2.2 g hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl <;> rfl

lemma edge_truth {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
  simp [graphFun]

lemma graph_unit_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) :
    graphFun G ∅ (unitInput v) = false := by
  cases hf : graphFun G ∅ (unitInput v) with
  | false => rfl
  | true =>
    rw [edge_truth] at hf
    rcases hf with ⟨u, w, hadj, hu, hw⟩
    simp only [unitInput, decide_eq_true_eq] at hu hw
    subst hu; subst hw
    exact (G.ne_of_adj hadj rfl).elim

lemma r_below {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (v : Fin n) (hout : C.output < n + C.gates.length)
    (hcorrect : circuitFun n C = graphFun G ∅) :
    BelowF G (wrap C v) (C.gates.length + 1) := by
  intro x hx
  rwa [r_value C v x hout, hcorrect] at hx

lemma q_not_below {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (v : Fin n) (hout : C.output < n + C.gates.length)
    (hcorrect : circuitFun n C = graphFun G ∅) :
    ¬ BelowF G (wrap C v) C.gates.length := by
  intro h
  have hq : gateVal n (wrap C v) C.gates.length (unitInput v) = true := by
    rw [q_value C v _ hout, hcorrect, graph_unit_false]
    simp [unitInput]
  have hf := h (unitInput v) hq
  rw [graph_unit_false] at hf
  cases hf

lemma gamma_all {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (v : Fin n) (hout : C.output < n + C.gates.length)
    (hcorrect : circuitFun n C = graphFun G ∅) :
    gammaE G (wrap C v) (C.gates.length + 1) = G.edgeFinset := by
  apply Finset.ext
  intro e
  refine Sym2.inductionOn e ?_
  intro u w
  simp only [gammaE, Finset.mem_filter]
  constructor
  · exact And.left
  · intro hedge
    refine ⟨hedge, u, w, rfl, ?_⟩
    rw [r_value C v _ hout, hcorrect]
    apply (edge_truth _).mpr
    exact ⟨u, w, by simpa using hedge, by simp [pairInput], by simp [pairInput]⟩

end PEqualNP.Outside.L_meta_2962.AbsorbWrapper
