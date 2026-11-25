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

namespace K6Subdivision

open PEqualNP.MetaComplexity PEqualNP.EdgeOwnership PEqualNP.TopForm

abbrev graph : SimpleGraph (Fin 21) :=
  edgeGraph 21
    [(0, 6), (1, 6), (0, 7), (2, 7), (0, 8), (3, 8), (0, 9), (4, 9),
     (0, 10), (5, 10), (1, 11), (2, 11), (1, 12), (3, 12), (1, 13), (4, 13),
     (1, 14), (5, 14), (2, 15), (3, 15), (2, 16), (4, 16), (2, 17), (5, 17),
     (3, 18), (4, 18), (3, 19), (5, 19), (4, 20), (5, 20)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma bipartite : ∃ c : Fin 21 → Bool, ∀ u v, graph.Adj u v → c u ≠ c v := by
  refine ⟨fun v => decide (v.val < 6), ?_⟩
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma noFourCycle : NoFourCycle graph := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma card_edges : graph.edgeFinset.card = 30 := by decide

def originalCover : Finset (Fin 21) := {0, 1, 2, 3, 4, 5}

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma originalCover_isCover : CoverPromise.IsVertexCover graph originalCover := by
  unfold CoverPromise.IsVertexCover
  decide

lemma originalCover_card : originalCover.card = 6 := by decide

lemma matching_card_le_cover {n k : ℕ} (G : SimpleGraph (Fin n))
    (l r : Fin k → Fin n) (hl : Function.Injective l) (hr : Function.Injective r)
    (hd : ∀ i j, l i ≠ r j) (he : ∀ i, G.Adj (l i) (r i))
    (S : Finset (Fin n)) (hS : CoverPromise.IsVertexCover G S) : k ≤ S.card := by
  classical
  let f : Fin k → {v : Fin n // v ∈ S} := fun i =>
    if h : l i ∈ S then ⟨l i, h⟩
    else ⟨r i, (hS _ _ (he i)).resolve_left h⟩
  have hf : Function.Injective f := by
    intro i j hij
    have hv := congrArg Subtype.val hij
    by_cases hi : l i ∈ S <;> by_cases hj : l j ∈ S
    · apply hl
      simpa [f, hi, hj] using hv
    · have hbad : l i = r j := by simpa [f, hi, hj] using hv
      exact False.elim (hd i j hbad)
    · have hbad : r i = l j := by simpa [f, hi, hj] using hv
      exact False.elim (hd j i hbad.symm)
    · apply hr
      simpa [f, hi, hj] using hv
  have hcard := Fintype.card_le_of_injective f hf
  simpa using hcard

def leftEndpoint (i : Fin 6) : Fin 21 := i.castLE (by decide)

def rightEndpoint : Fin 6 → Fin 21 := ![6, 11, 15, 18, 20, 10]

lemma leftEndpoint_injective : Function.Injective leftEndpoint := by decide

lemma rightEndpoint_injective : Function.Injective rightEndpoint := by decide

lemma endpoints_disjoint : ∀ i j, leftEndpoint i ≠ rightEndpoint j := by decide

set_option maxRecDepth 10000 in
lemma matching_edges : ∀ i, graph.Adj (leftEndpoint i) (rightEndpoint i) := by decide

lemma cover_card_lower (S : Finset (Fin 21))
    (hS : CoverPromise.IsVertexCover graph S) : 6 ≤ S.card :=
  matching_card_le_cover graph leftEndpoint rightEndpoint leftEndpoint_injective
    rightEndpoint_injective endpoints_disjoint matching_edges S hS

lemma minimum_cover : ∃ S : Finset (Fin 21), CoverPromise.IsVertexCover graph S ∧
    S.card = 6 ∧ ∀ T : Finset (Fin 21), CoverPromise.IsVertexCover graph T → S.card ≤ T.card := by
  refine ⟨originalCover, originalCover_isCover, originalCover_card, ?_⟩
  intro T hT
  rw [originalCover_card]
  exact cover_card_lower T hT

end K6Subdivision

namespace C6Book3

open PEqualNP.MetaComplexity PEqualNP.EdgeOwnership PEqualNP.TopForm

abbrev graph : SimpleGraph (Fin 14) :=
  edgeGraph 14
    [(0, 1), (0, 2), (2, 3), (3, 4), (4, 5), (5, 1), (0, 6), (6, 7), (7, 8), (8, 9), (9, 1), (0, 10), (10, 11), (11, 12), (12, 13), (13, 1)]

def cover : Finset (Fin 14) := {0, 3, 5, 7, 9, 11, 13}

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma bipartite : ∃ c : Fin 14 → Bool, ∀ u v, graph.Adj u v → c u ≠ c v := by
  refine ⟨fun v => decide (v ∈ cover), ?_⟩
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma noFourCycle : NoFourCycle graph := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma card_edges : graph.edgeFinset.card = 16 := by decide

set_option maxRecDepth 10000 in
lemma cover_isCover : CoverPromise.IsVertexCover graph cover := by
  unfold CoverPromise.IsVertexCover
  decide

lemma cover_card : cover.card = 7 := by decide

def leftEndpoint : Fin 7 → Fin 14 := ![0, 2, 4, 6, 8, 10, 12]

def rightEndpoint : Fin 7 → Fin 14 := ![1, 3, 5, 7, 9, 11, 13]

lemma leftEndpoint_injective : Function.Injective leftEndpoint := by decide

lemma rightEndpoint_injective : Function.Injective rightEndpoint := by decide

lemma endpoints_disjoint : ∀ i j, leftEndpoint i ≠ rightEndpoint j := by decide

set_option maxRecDepth 10000 in
lemma matching_edges : ∀ i, graph.Adj (leftEndpoint i) (rightEndpoint i) := by decide

lemma cover_card_lower (S : Finset (Fin 14))
    (hS : CoverPromise.IsVertexCover graph S) : 7 ≤ S.card :=
  K6Subdivision.matching_card_le_cover graph leftEndpoint rightEndpoint leftEndpoint_injective
    rightEndpoint_injective endpoints_disjoint matching_edges S hS

lemma minimum_cover : ∃ S : Finset (Fin 14), CoverPromise.IsVertexCover graph S ∧
    S.card = 7 ∧ ∀ T : Finset (Fin 14), CoverPromise.IsVertexCover graph T → S.card ≤ T.card := by
  refine ⟨cover, cover_isCover, cover_card, ?_⟩
  intro T hT
  rw [cover_card]
  exact cover_card_lower T hT

abbrev jsonGraph : SimpleGraph (Fin 14) :=
  edgeGraph 14
    [(0, 7), (0, 8), (1, 8), (1, 9), (2, 9), (2, 7), (0, 10), (3, 10), (3, 11), (4, 11), (4, 7), (0, 12), (5, 12), (5, 13), (6, 13), (6, 7)]

def requestedToJson : Fin 14 → Fin 14 := ![0, 7, 8, 1, 9, 2, 10, 3, 11, 4, 12, 5, 13, 6]

set_option maxRecDepth 10000 in
lemma requestedToJson_bijective : Function.Bijective requestedToJson := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma requestedToJson_adj : ∀ u v, graph.Adj u v ↔
    jsonGraph.Adj (requestedToJson u) (requestedToJson v) := by decide

end C6Book3

end PEqualNP.Outside.L_meta_3566
