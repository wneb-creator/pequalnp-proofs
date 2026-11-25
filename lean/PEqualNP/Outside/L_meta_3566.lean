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

namespace AndSignature

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

lemma getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

def isAnd : GateOp → Bool
  | .and => true
  | _ => false

def andCount (gs : List Gate) : ℕ := gs.countP (fun g => isAnd g.op)

def step (g : Gate) (s : List Bool) : List Bool :=
  s ++ [g.op.eval (g.inputs.map fun i => s.getD i false)]

def sigRun : List Gate → List Bool → List Bool
  | [], _ => []
  | g :: gs, s =>
      (if isAnd g.op then [s.getD (g.inputs.getD 0 0) false] else []) ++
        sigRun gs (step g s)

lemma sigRun_length (gs : List Gate) (s : List Bool) :
    (sigRun gs s).length = andCount gs := by
  induction gs generalizing s with
  | nil => simp [sigRun, andCount]
  | cons g gs ih =>
    simp only [sigRun, List.length_append, ih, andCount, List.countP_cons]
    cases isAnd g.op <;> simp [Nat.add_comm]

def JoinRel (s t u : List Bool) : Prop :=
  s.length = t.length ∧ s.length = u.length ∧
    ∀ i, u.getD i false = (s.getD i false || t.getD i false)

lemma gate_join (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (a b c d : Bool) (hleft : op = GateOp.and → a = c) :
    op.eval [a || c, b || d] = (op.eval [a, b] || op.eval [c, d]) := by
  rcases hop with rfl | rfl <;>
    cases a <;> cases b <;> cases c <;> cases d <;> simp_all [GateOp.eval]

lemma step_join (g : Gate) (s t u : List Bool) (h : JoinRel s t u)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length = 2)
    (hleft : g.op = GateOp.and →
      s.getD (g.inputs.getD 0 0) false = t.getD (g.inputs.getD 0 0) false) :
    JoinRel (step g s) (step g t) (step g u) := by
  refine ⟨by simp [step, h.1], by simp [step, h.2.1], ?_⟩
  intro i
  by_cases hi : i = s.length
  · subst i
    have ht := h.1
    have hu := h.2.1
    unfold step
    rw [getD_snoc_eq, ht, getD_snoc_eq, ← ht, hu, getD_snoc_eq]
    obtain ⟨a, b, hg⟩ := List.length_eq_two.mp hlen
    have hl : g.op = GateOp.and → s.getD a false = t.getD a false := by
      simpa [hg] using hleft
    simp only [hg, List.map_cons, List.map_nil]
    rw [h.2.2 a, h.2.2 b]
    exact gate_join g.op hop _ _ _ _ hl
  · have ht := h.1
    have hu := h.2.1
    unfold step
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ hi,
      getD_snoc_ne _ _ _ _ (by omega)]
    exact h.2.2 i

lemma sigRun_join (gs : List Gate) (s t u : List Bool) (h : JoinRel s t u)
    (hbasis : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hsig : sigRun gs s = sigRun gs t) :
    JoinRel (wiresFrom gs s) (wiresFrom gs t) (wiresFrom gs u) := by
  induction gs generalizing s t u with
  | nil => exact h
  | cons g gs ih =>
    obtain ⟨hop, hlen⟩ := hbasis g List.mem_cons_self
    have htail : sigRun gs (step g s) = sigRun gs (step g t) := by
      rcases hop with hp | hp
      · have hpair :
            s.getD (g.inputs.getD 0 0) false = t.getD (g.inputs.getD 0 0) false ∧
            sigRun gs (step g s) = sigRun gs (step g t) := by
          simpa [sigRun, isAnd, hp] using hsig
        exact hpair.2
      · simpa [sigRun, isAnd, hp] using hsig
    have hleft : g.op = GateOp.and →
        s.getD (g.inputs.getD 0 0) false = t.getD (g.inputs.getD 0 0) false := by
      intro hp
      have hpair :
          s.getD (g.inputs.getD 0 0) false = t.getD (g.inputs.getD 0 0) false ∧
          sigRun gs (step g s) = sigRun gs (step g t) := by
        simpa [sigRun, isAnd, hp] using hsig
      exact hpair.1
    exact ih _ _ _ (step_join g s t u h hop hlen hleft)
      (fun g' hg' => hbasis g' (List.mem_cons_of_mem g hg')) htail

def signature (n : ℕ) (C : Circuit) (x : Fin n → Bool) : List Bool :=
  sigRun C.gates (List.ofFn x)

lemma signature_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (signature n C x).length = andCount C.gates := sigRun_length _ _

lemma same_signature_join (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (x y : Fin n → Bool) (hsig : signature n C x = signature n C y) :
    circuitFun n C (fun i => x i || y i) = (circuitFun n C x || circuitFun n C y) := by
  have hinit : JoinRel (List.ofFn x) (List.ofFn y) (List.ofFn fun i => x i || y i) := by
    refine ⟨by simp, by simp, ?_⟩
    intro i
    by_cases hi : i < n <;> simp [List.getD_eq_getElem?_getD, hi]
  exact (sigRun_join C.gates _ _ _ hinit
    (fun g hg => ⟨hAO.1 g hg, hAO.2.2 g hg⟩) hsig).2.2 C.output

def signatureFn (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    Fin (andCount C.gates) → Bool := fun i => (signature n C x).getD i.val false

lemma signature_eq_of_fn_eq (n : ℕ) (C : Circuit) (x y : Fin n → Bool)
    (h : signatureFn n C x = signatureFn n C y) : signature n C x = signature n C y := by
  apply List.ext_getElem
  · rw [signature_length, signature_length]
  · intro i hi hj
    have hi' : i < andCount C.gates := by simpa [signature_length] using hi
    have hv := congrFun h ⟨i, hi'⟩
    simpa [signatureFn, List.getD_eq_getElem?_getD, hi, hj] using hv

lemma false_family_card_bound (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (S : Finset (Fin n → Bool))
    (hfalse : ∀ x ∈ S, circuitFun n C x = false)
    (hjoin : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → circuitFun n C (fun i => x i || y i) = true) :
    S.card ≤ 2 ^ andCount C.gates := by
  classical
  have hinj : Function.Injective (fun x : ↥S => signatureFn n C x.val) := by
    intro x y hxy
    apply Subtype.ext
    by_contra hne
    have hsig := signature_eq_of_fn_eq n C x.val y.val hxy
    have heq := same_signature_join n C hAO x.val y.val hsig
    rw [hfalse _ x.property, hfalse _ y.property, hjoin _ x.property _ y.property hne] at heq
    contradiction
  have hcard := Fintype.card_le_of_injective _ hinj
  simpa using hcard

lemma maximal_false_family_card_bound (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (S : Finset (Fin n → Bool))
    (hmax : ∀ x ∈ S, Maximal (fun y => circuitFun n C y = false) x) :
    S.card ≤ 2 ^ andCount C.gates := by
  apply false_family_card_bound n C hAO S
  · intro x hx
    exact (hmax x hx).1
  · intro x hx y hy hne
    let u : Fin n → Bool := fun i => x i || y i
    have hxu : x ≤ u := by
      intro i
      apply Bool.le_iff_imp.mpr
      intro hi
      simp [u, hi]
    have hyu : y ≤ u := by
      intro i
      apply Bool.le_iff_imp.mpr
      intro hi
      simp [u, hi]
    by_contra hf
    have huf : circuitFun n C u = false := by
      cases he : circuitFun n C u <;> simp_all [u]
    have hux : u ≤ x := (hmax x hx).2 huf hxu
    have huy : u ≤ y := (hmax y hy).2 huf hyu
    exact hne (le_antisymm (hxu.trans huy) (hyu.trans hux))

def charInput {n : ℕ} (S : Finset (Fin n)) : Fin n → Bool := fun i => decide (i ∈ S)

lemma charInput_injective {n : ℕ} : Function.Injective (@charInput n) := by
  intro S T h
  ext i
  have hi := Bool.eq_iff_iff.mp (congrFun h i)
  simpa [charInput] using hi

lemma independent_family_card_bound {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C)
    (hfun : circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅)
    (F : Finset (Finset (Fin n)))
    (hindep : ∀ S ∈ F, G.IsIndepSet (S : Set (Fin n)))
    (hpairs : ∀ S ∈ F, ∀ T ∈ F, S ≠ T →
      ∃ a ∈ S ∪ T, ∃ b ∈ S ∪ T, G.Adj a b) :
    F.card ≤ 2 ^ andCount C.gates := by
  classical
  have hbound := false_family_card_bound n C hAO (F.image charInput) ?_ ?_
  · simpa only [Finset.card_image_of_injective F charInput_injective] using hbound
  · intro x hx
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hx
    rw [hfun]
    have hno : ¬ ∃ a b, G.Adj a b ∧ charInput S a = true ∧ charInput S b = true := by
      rintro ⟨a, b, hab, ha, hb⟩
      exact hindep S hS (of_decide_eq_true ha) (of_decide_eq_true hb) hab.ne hab
    simp [PEqualNP.MetaComplexity.NestedCover.graphFun, hno]
  · intro x hx y hy hne
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hy
    have hST : S ≠ T := by intro h; subst T; exact hne rfl
    obtain ⟨a, ha, b, hb, hab⟩ := hpairs S hS T hT hST
    rw [hfun]
    simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, Finset.notMem_empty,
      false_and, exists_false, decide_false, Bool.false_or, decide_eq_true_eq]
    exact ⟨a, b, hab, by simpa [charInput] using ha, by simpa [charInput] using hb⟩

lemma maximal_independent_family_card_bound {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C)
    (hfun : circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅)
    (F : Finset (Finset (Fin n)))
    (hmax : ∀ S ∈ F, Maximal (fun T : Finset (Fin n) => G.IsIndepSet (T : Set (Fin n))) S) :
    F.card ≤ 2 ^ andCount C.gates := by
  apply independent_family_card_bound G C hAO hfun F
    (fun S hS => (hmax S hS).1)
  intro S hS T hT hne
  by_contra hno
  have hU : G.IsIndepSet ((S ∪ T : Finset (Fin n)) : Set (Fin n)) := by
    intro a ha b hb hab hAdj
    exact hno ⟨a, ha, b, hb, hAdj⟩
  have hUS : S ∪ T ⊆ S := (hmax S hS).2 hU Finset.subset_union_left
  have hUT : S ∪ T ⊆ T := (hmax T hT).2 hU Finset.subset_union_right
  exact hne (Finset.Subset.antisymm (Finset.subset_union_left.trans hUT)
    (Finset.subset_union_right.trans hUS))


end AndSignature

namespace K6Subdivision

def independentCode : Fin 58 → ℕ := ![63, 124, 186, 2105, 2296, 310, 4149, 4468, 32819, 33202, 38961, 39408, 558, 8237, 8812, 65579, 66218, 75817, 76520, 262183, 262950, 274469, 275300, 360483, 361378, 374817, 375776, 1054, 16413, 17500, 131099, 132250, 149529, 150744, 524311, 525590, 544789, 546132, 688147, 689554, 710673, 712144, 1048591, 1050126, 1073165, 1074764, 1245195, 1246858, 1271817, 1273544, 1835015, 1836806, 1863685, 1865540, 2064387, 2066306, 2095105, 2097088]

def independentSet (i : Fin 58) : Finset (Fin 21) :=
  Finset.univ.filter fun v => (independentCode i).testBit v.val

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma independentSet_independent : ∀ i : Fin 58,
    ∀ u ∈ independentSet i, ∀ v ∈ independentSet i, ¬ graph.Adj u v := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma independentSet_dominates : ∀ i : Fin 58, ∀ v : Fin 21,
    v ∉ independentSet i → ∃ u ∈ independentSet i, graph.Adj v u := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma independentSet_injective : Function.Injective independentSet := by
  decide

lemma independentSet_isIndepSet (i : Fin 58) :
    graph.IsIndepSet (independentSet i : Set (Fin 21)) := by
  intro u hu v hv _
  exact independentSet_independent i u hu v hv

lemma independentSet_maximal (i : Fin 58) (T : Finset (Fin 21))
    (hT : graph.IsIndepSet (T : Set (Fin 21))) (hsub : independentSet i ⊆ T) :
    T ⊆ independentSet i := by
  intro v hv
  by_contra hn
  obtain ⟨u, hu, hadj⟩ := independentSet_dominates i v hn
  exact (hT hv (hsub hu) (graph.ne_of_adj hadj)) hadj

lemma exists_58_maximal_independent :
    ∃ f : Fin 58 → Finset (Fin 21), Function.Injective f ∧
      ∀ i, graph.IsIndepSet (f i : Set (Fin 21)) ∧
        ∀ T : Finset (Fin 21), graph.IsIndepSet (T : Set (Fin 21)) →
          f i ⊆ T → T ⊆ f i := by
  exact ⟨independentSet, independentSet_injective, fun i =>
    ⟨independentSet_isIndepSet i, independentSet_maximal i⟩⟩

def independentInput (i : Fin 58) : Fin 21 → Bool :=
  fun v => decide (v ∈ independentSet i)

lemma independentInput_injective : Function.Injective independentInput := by
  intro i j hij
  apply independentSet_injective
  ext v
  have hv := congrFun hij v
  simpa [independentInput] using hv

lemma independentInput_false (i : Fin 58) :
    PEqualNP.MetaComplexity.NestedCover.graphFun graph ∅ (independentInput i) = false := by
  simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, Finset.notMem_empty,
    false_and, exists_false, decide_false, Bool.false_or, decide_eq_false_iff_not]
  rintro ⟨u, v, hadj, hu, hv⟩
  simp only [independentInput, decide_eq_true_eq] at hu hv
  exact independentSet_independent i u hu v hv hadj

lemma independentInput_maximal (i : Fin 58) (y : Fin 21 → Bool)
    (hupper : ∀ v, independentInput i v = true → y v = true)
    (hfalse : PEqualNP.MetaComplexity.NestedCover.graphFun graph ∅ y = false) :
    y = independentInput i := by
  funext v
  by_cases hv : v ∈ independentSet i
  · have hy := hupper v (by simp [independentInput, hv])
    simp [independentInput, hv, hy]
  · have hy : y v = false := by
      cases he : y v with
      | false => rfl
      | true =>
        obtain ⟨u, hu, hadj⟩ := independentSet_dominates i v hv
        have huy := hupper u (by simp [independentInput, hu])
        have htrue : PEqualNP.MetaComplexity.NestedCover.graphFun graph ∅ y = true := by
          simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, Finset.notMem_empty,
            false_and, exists_false, decide_false, Bool.false_or, decide_eq_true_eq]
          exact ⟨v, u, hadj, he, huy⟩
        rw [htrue] at hfalse
        cases hfalse
    simp [independentInput, hv, hy]

lemma independentInput_join_true (i j : Fin 58) (hne : i ≠ j) :
    PEqualNP.MetaComplexity.NestedCover.graphFun graph ∅
      (fun v => independentInput i v || independentInput j v) = true := by
  cases he : PEqualNP.MetaComplexity.NestedCover.graphFun graph ∅
      (fun v => independentInput i v || independentInput j v) with
  | true => rfl
  | false =>
    have hi := independentInput_maximal i
      (fun v => independentInput i v || independentInput j v)
      (by intro v hv; simp [hv]) he
    have hj := independentInput_maximal j
      (fun v => independentInput i v || independentInput j v)
      (by intro v hv; simp [hv]) he
    exact False.elim (hne (independentInput_injective (hi.symm.trans hj)))

def independentInputs : Finset (Fin 21 → Bool) :=
  Finset.univ.image independentInput

lemma independentInputs_card : independentInputs.card = 58 := by
  rw [independentInputs, Finset.card_image_of_injective _ independentInput_injective]
  simp

lemma independentInputs_false (x : Fin 21 → Bool) (hx : x ∈ independentInputs) :
    PEqualNP.MetaComplexity.NestedCover.graphFun graph ∅ x = false := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  exact independentInput_false i

lemma independentInputs_join_true (x y : Fin 21 → Bool)
    (hx : x ∈ independentInputs) (hy : y ∈ independentInputs) (hne : x ≠ y) :
    PEqualNP.MetaComplexity.NestedCover.graphFun graph ∅ (fun v => x v || y v) = true := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
  apply independentInput_join_true i j
  intro he
  exact hne (he ▸ rfl)

end K6Subdivision

namespace K6Subdivision

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

lemma six_le_of_fiftyeight_le_pow_two (a : ℕ) (h : 58 ≤ 2 ^ a) : 6 ≤ a := by
  by_contra hn
  have ha : a ≤ 5 := by omega
  have hp : 2 ^ a ≤ 2 ^ 5 := Nat.pow_le_pow_right (by decide) ha
  norm_num at hp
  omega

lemma fiftyeight_le_pow_andCount (C : Circuit) (hAO : IsAO2 21 C)
    (hfun : circuitFun 21 C = PEqualNP.MetaComplexity.NestedCover.graphFun graph ∅) :
    58 ≤ 2 ^ AndSignature.andCount C.gates := by
  have hb := AndSignature.false_family_card_bound 21 C hAO independentInputs
    (fun x hx => by rw [hfun]; exact independentInputs_false x hx)
    (fun x hx y hy hne => by rw [hfun]; exact independentInputs_join_true x y hx hy hne)
  rw [independentInputs_card] at hb
  exact hb

lemma six_le_andCount (C : Circuit) (hAO : IsAO2 21 C)
    (hfun : circuitFun 21 C = PEqualNP.MetaComplexity.NestedCover.graphFun graph ∅) :
    6 ≤ AndSignature.andCount C.gates :=
  six_le_of_fiftyeight_le_pow_two _ (fiftyeight_le_pow_andCount C hAO hfun)

end K6Subdivision

end PEqualNP.Outside.L_meta_3566
