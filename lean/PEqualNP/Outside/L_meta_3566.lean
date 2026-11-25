import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3566

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

def reviewPathAdj (a b : Fin 4) : Prop :=
  (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨
  (a = 0 ∧ b = 3) ∨ (a = 3 ∧ b = 0) ∨
  (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1)

def reviewPath : SimpleGraph (Fin 4) where
  Adj := reviewPathAdj
  symm := ⟨by unfold reviewPathAdj; decide⟩
  loopless := ⟨by unfold reviewPathAdj; decide⟩

abbrev reviewPathDecidable : DecidableRel reviewPath.Adj := by
  unfold reviewPath reviewPathAdj
  infer_instance

def reviewNested : Circuit :=
  ⟨[⟨.and, [1, 2]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [0, 3]⟩,
    ⟨.or, [1, 6]⟩, ⟨.and, [5, 7]⟩], 8⟩

lemma reviewNested_AO2 : IsAO2 4 reviewNested := by decide

lemma reviewNested_size : reviewNested.size = 5 := rfl

lemma reviewNested_lastAnd : (NestedCover.gateAt reviewNested 4).op = .and := rfl

lemma reviewPath_bipartite :
    ∃ c : Fin 4 → Bool, ∀ u v, reviewPath.Adj u v → c u ≠ c v := by
  refine ⟨fun u => decide (u = 1 ∨ u = 3), ?_⟩
  unfold reviewPath reviewPathAdj
  decide

lemma reviewPath_noFourCycle :
    @NoFourCycle 4 reviewPath reviewPathDecidable := by decide

lemma reviewNested_computes :
    circuitFun 4 reviewNested =
      @NestedCover.graphFun 4 reviewPath reviewPathDecidable ∅ := by decide

lemma reviewNested_clean :
    @BelowF 4 reviewPath reviewPathDecidable reviewNested 4 := by decide

lemma reviewNested_notTopForm :
    ¬ @PEqualNP.TopForm.TopForm 4 reviewPath reviewPathDecidable reviewNested := by decide

lemma reviewPath_noSingleCover :
    ∀ z : Fin 4, ¬ CoverPromise.IsVertexCover reviewPath {z} := by
  unfold CoverPromise.IsVertexCover reviewPath reviewPathAdj
  decide

def reviewBoundaryHood : Fin 11 → ℕ :=
  ![1536, 272, 1056, 192, 1282, 772, 1160, 584, 562, 417, 85]

abbrev reviewBoundaryAdj (v w : Fin 11) :=
  (reviewBoundaryHood v).testBit w.val = true

def reviewBoundaryGraph : SimpleGraph (Fin 11) where
  Adj := reviewBoundaryAdj
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

def reviewBoundaryCircuit : PEqualNP.AndCount.AndCountCircuit 11 where
  size := 6
  leftVars := ![{7, 10}, {2}, {0}, {8}, {4, 8}, {3}]
  leftGates := ![∅, ∅, ∅, {0}, ∅, ∅]
  rightVars := ![{6, 9}, {5, 10}, {9, 10}, {4, 5}, {1}, {6, 7}]
  rightGates := ![∅, {0}, ∅, ∅, {0}, ∅]
  outVars := ∅
  outGates := {1, 2, 3, 4, 5}

lemma reviewBoundary_wellFormed : reviewBoundaryCircuit.WellFormed := by
  unfold PEqualNP.AndCount.AndCountCircuit.WellFormed
  decide

lemma reviewBoundary_edge : reviewBoundaryGraph.Adj 6 7 := by
  change reviewBoundaryAdj 6 7
  decide

lemma reviewBoundary_missed : reviewBoundaryCircuit.eval {6, 7} = false := by decide

lemma reviewBoundary_notComputes :
    ¬ reviewBoundaryCircuit.Computes reviewBoundaryGraph := by
  intro h
  have ht := (h {6, 7}).mpr
    ⟨6, by decide, 7, by decide, reviewBoundary_edge⟩
  rw [reviewBoundary_missed] at ht
  contradiction

end PEqualNP.Outside.L_meta_3566

namespace PEqualNP.Outside.L_meta_3566.BipartiteBoundary

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

/-- A selected subset of the enumerated vertices, together with every true-color
  vertex having no neighbor in the selected subset. -/
def negativeInput {n p : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : Fin n → Bool) (e : Fin p → Fin n) (s : Fin p → Bool) : Fin n → Bool :=
  fun i => decide (∃ j, e j = i ∧ s j = true) ||
    (c i && decide (∀ j, s j = true → ¬ G.Adj (e j) i))

lemma graph_true_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  simp [graphFun]

/-- Every negative input is below a canonical input. This implication needs
  only enumeration of the false-color vertices, not a proper coloring. -/
lemma negative_le_canonical {n p : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (c : Fin n → Bool) (e : Fin p → Fin n)
    (hcover : ∀ i, c i = false → ∃ j, e j = i)
    (x : Fin n → Bool) (hx : graphFun G ∅ x = false) :
    x ≤ negativeInput G c e (fun j => x (e j)) := by
  intro i
  apply Bool.le_iff_imp.mpr
  intro hi
  simp only [negativeInput, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true]
  by_cases hci : c i = false
  · obtain ⟨j, hj⟩ := hcover i hci
    exact Or.inl ⟨j, hj, by rw [hj]; exact hi⟩
  · have hcit : c i = true := by cases h : c i <;> simp_all
    right
    refine ⟨hcit, ?_⟩
    intro j hj hadj
    have htrue := (graph_true_iff G x).2 ⟨e j, i, hadj, hj, hi⟩
    rw [hx] at htrue
    cases htrue

/-- Edge pairs and this family of at most 2^p canonical inputs suffice to
  check a monotone function. Bipartiteness is not needed for this direction. -/
lemma eq_graph_of_boundary {n p : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (c : Fin n → Bool) (e : Fin p → Fin n)
    (hcover : ∀ i, c i = false → ∃ j, e j = i)
    (f : (Fin n → Bool) → Bool) (hf : Monotone f)
    (hedges : ∀ u v, G.Adj u v → f (pairInput u v) = true)
    (hnegative : ∀ s : Fin p → Bool, f (negativeInput G c e s) = false) :
    f = graphFun G ∅ := by
  funext x
  by_cases hx : graphFun G ∅ x = true
  · obtain ⟨u, v, huv, hu, hv⟩ := (graph_true_iff G x).1 hx
    have hpair : pairInput u v ≤ x := by
      intro i
      apply Bool.le_iff_imp.mpr
      intro hi
      have hmem : i = u ∨ i = v := by simpa [pairInput] using hi
      rcases hmem with rfl | rfl
      · exact hu
      · exact hv
    have hfx : f x = true := by
      have h := hf hpair
      rw [hedges u v huv] at h
      exact Bool.le_iff_imp.mp h rfl
    exact hfx.trans hx.symm
  · have hgx : graphFun G ∅ x = false := Bool.eq_false_iff.mpr hx
    have h := hf (negative_le_canonical G c e hcover x hgx)
    rw [hnegative] at h
    have hfx : f x = false := by
      cases hfx : f x <;> simp_all [Bool.le_iff_imp]
    exact hfx.trans hgx.symm

/-- Proper coloring and false-color enumeration make every canonical input
  negative. Neither surjectivity nor injectivity of e is needed here. -/
lemma canonical_negative {n p : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (c : Fin n → Bool) (e : Fin p → Fin n)
    (hproper : ∀ u v, G.Adj u v → c u ≠ c v)
    (hleft : ∀ j, c (e j) = false) (s : Fin p → Bool) :
    graphFun G ∅ (negativeInput G c e s) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨u, v, huv, hu, hv⟩ := (graph_true_iff G _).1 h
  simp only [negativeInput, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at hu hv
  rcases hu with ⟨j, rfl, hj⟩ | ⟨hcu, hnu⟩
  · rcases hv with ⟨k, rfl, hk⟩ | ⟨hcv, hnv⟩
    · exact hproper _ _ huv ((hleft j).trans (hleft k).symm)
    · exact hnv j hj huv
  · rcases hv with ⟨k, rfl, hk⟩ | ⟨hcv, hnv⟩
    · exact hnu k hk huv.symm
    · exact hproper _ _ huv (hcu.trans hcv.symm)

lemma eq_graph_iff_boundary {n p : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (c : Fin n → Bool) (e : Fin p → Fin n)
    (hcover : ∀ i, c i = false → ∃ j, e j = i)
    (hproper : ∀ u v, G.Adj u v → c u ≠ c v)
    (hleft : ∀ j, c (e j) = false)
    (f : (Fin n → Bool) → Bool) (hf : Monotone f) :
    f = graphFun G ∅ ↔
      (∀ u v, G.Adj u v → f (pairInput u v) = true) ∧
      (∀ s : Fin p → Bool, f (negativeInput G c e s) = false) := by
  constructor
  · intro h
    subst f
    constructor
    · intro u v huv
      apply (graph_true_iff G _).2
      exact ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩
    · exact canonical_negative G c e hproper hleft
  · rintro ⟨hedges, hnegative⟩
    exact eq_graph_of_boundary G c e hcover f hf hedges hnegative

end PEqualNP.Outside.L_meta_3566.BipartiteBoundary
