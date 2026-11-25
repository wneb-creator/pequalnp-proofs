import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3566

open PEqualNP.MetaComplexity

lemma cut_adj_iff {n : ℕ} (G : SimpleGraph (Fin n)) (z a b : Fin n) :
    (G.deleteEdges (G.incidenceSet z)).Adj a b ↔
      G.Adj a b ∧ a ≠ z ∧ b ≠ z :=
  SimpleGraph.deleteIncidenceSet_adj

lemma cover_cut_erase {n : ℕ} (G : SimpleGraph (Fin n)) (z : Fin n)
    (S : Finset (Fin n)) (hS : CoverPromise.IsVertexCover G S) :
    CoverPromise.IsVertexCover (G.deleteEdges (G.incidenceSet z)) (S.erase z) := by
  intro a b hab
  obtain ⟨hab, haz, hbz⟩ := (cut_adj_iff G z a b).mp hab
  rcases hS a b hab with ha | hb
  · exact Or.inl (Finset.mem_erase.mpr ⟨haz, ha⟩)
  · exact Or.inr (Finset.mem_erase.mpr ⟨hbz, hb⟩)

lemma cover_insert_of_cut {n : ℕ} (G : SimpleGraph (Fin n)) (z : Fin n)
    (S : Finset (Fin n))
    (hS : CoverPromise.IsVertexCover (G.deleteEdges (G.incidenceSet z)) S) :
    CoverPromise.IsVertexCover G (insert z S) := by
  intro a b hab
  by_cases haz : a = z
  · exact Or.inl (Finset.mem_insert.mpr (Or.inl haz))
  by_cases hbz : b = z
  · exact Or.inr (Finset.mem_insert.mpr (Or.inl hbz))
  rcases hS a b ((cut_adj_iff G z a b).mpr ⟨hab, haz, hbz⟩) with ha | hb
  · exact Or.inl (Finset.mem_insert.mpr (Or.inr ha))
  · exact Or.inr (Finset.mem_insert.mpr (Or.inr hb))

lemma cover_drop_iff_minimum_contains {n : ℕ} (G : SimpleGraph (Fin n)) (z : Fin n) :
    (∃ S : Finset (Fin n),
      CoverPromise.IsVertexCover (G.deleteEdges (G.incidenceSet z)) S ∧
      ∀ T : Finset (Fin n), CoverPromise.IsVertexCover G T → S.card < T.card) ↔
    ∃ T : Finset (Fin n), CoverPromise.IsVertexCover G T ∧ z ∈ T ∧
      ∀ U : Finset (Fin n), CoverPromise.IsVertexCover G U → T.card ≤ U.card := by
  constructor
  · rintro ⟨S, hS, hlt⟩
    have hz : z ∉ S := by
      intro hz
      have hc := cover_insert_of_cut G z S hS
      rw [Finset.insert_eq_of_mem hz] at hc
      exact (Nat.lt_irrefl S.card) (hlt S hc)
    refine ⟨insert z S, cover_insert_of_cut G z S hS, Finset.mem_insert_self z S, ?_⟩
    intro U hU
    rw [Finset.card_insert_of_notMem hz]
    exact hlt U hU
  · rintro ⟨T, hT, hz, hmin⟩
    refine ⟨T.erase z, cover_cut_erase G z T hT, ?_⟩
    intro U hU
    exact lt_of_lt_of_le (Finset.card_erase_lt_of_mem hz) (hmin U hU)

lemma cut_graphFun_eq_restrict {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (z : Fin n) :
    (fun y : Fin n → Bool => @decide
      (∃ a b : Fin n, (G.deleteEdges (G.incidenceSet z)).Adj a b ∧
        y a = true ∧ y b = true) (Classical.propDecidable _)) =
    (fun y : Fin n → Bool => NestedCover.graphFun G ∅ (Function.update y z false)) := by
  classical
  funext y
  simp only [NestedCover.graphFun, Finset.notMem_empty, false_and, exists_false,
    decide_false, Bool.false_or]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    obtain ⟨hab, haz, hbz⟩ := (cut_adj_iff G z a b).mp hab
    exact ⟨a, b, hab, by simpa [Function.update_of_ne haz] using ha,
      by simpa [Function.update_of_ne hbz] using hb⟩
  · rintro ⟨a, b, hab, ha, hb⟩
    have haz : a ≠ z := by rintro rfl; simp at ha
    have hbz : b ≠ z := by rintro rfl; simp at hb
    exact ⟨a, b, (cut_adj_iff G z a b).mpr ⟨hab, haz, hbz⟩,
      by simpa [Function.update_of_ne haz] using ha,
      by simpa [Function.update_of_ne hbz] using hb⟩

namespace SemanticAudit

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.size := by
  rw [wires_eq_foldl, foldl_stepWire_length, List.length_ofFn]
  rfl

lemma circuitFun_input {n : ℕ} (C : Circuit) (h : C.output < n) (x : Fin n → Bool) :
    circuitFun n C x = x ⟨C.output, h⟩ := by
  unfold circuitFun Circuit.eval
  rw [wires_eq_foldl, foldl_stepWire_getD_lt C.gates (List.ofFn x) C.output
    (by simpa using h)]
  simp [List.getD_eq_getElem?_getD, h]

lemma circuitFun_past {n : ℕ} (C : Circuit) (h : n + C.size ≤ C.output)
    (x : Fin n → Bool) : circuitFun n C x = false := by
  unfold circuitFun Circuit.eval
  exact getD_ge_length _ _ (by rw [wires_length]; exact h)

lemma graphFun_singleton {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v : Fin n) : graphFun G ∅ (fun w => decide (w = v)) = false := by
  simp [graphFun]

lemma graphFun_allTrue {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hedge : ∃ a b, G.Adj a b) : graphFun G ∅ (fun _ => true) = true := by
  simpa [graphFun] using hedge

lemma output_is_gate {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hedge : ∃ a b, G.Adj a b) (C : Circuit)
    (hfun : circuitFun n C = graphFun G ∅) :
    n ≤ C.output ∧ C.output < n + C.size := by
  constructor
  · by_contra h
    have hi : C.output < n := by omega
    let v : Fin n := ⟨C.output, hi⟩
    have hinput := circuitFun_input C hi (fun w => decide (w = v))
    have hgraph := graphFun_singleton G v
    rw [hfun] at hinput
    simp [v, hgraph] at hinput
  · by_contra h
    have hpast := circuitFun_past (n := n) C (by omega) (fun _ => true)
    rw [hfun, graphFun_allTrue G hedge] at hpast
    cases hpast

lemma positive_size {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hedge : ∃ a b, G.Adj a b) (C : Circuit)
    (hfun : circuitFun n C = graphFun G ∅) : 0 < C.size := by
  have h := output_is_gate G hedge C hfun
  omega

def falseCircuit (n : ℕ) : Circuit := ⟨[], n⟩

lemma falseCircuit_isAO2 (n : ℕ) : IsAO2 n (falseCircuit n) := by
  simp [IsAO2, AndOrOnly, ReadsBack, falseCircuit]

lemma falseCircuit_fun (n : ℕ) : circuitFun n (falseCircuit n) = fun _ => false := by
  funext x
  exact circuitFun_past _ (by simp [falseCircuit, Circuit.size]) x

lemma falseCircuit_size (n : ℕ) : (falseCircuit n).size = 0 := rfl

end SemanticAudit

end PEqualNP.Outside.L_meta_3566
