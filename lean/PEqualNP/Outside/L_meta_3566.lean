import PEqualNP.Defs
import Mathlib.Combinatorics.Hall.Basic

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

namespace PEqualNP.Outside.L_meta_3566.SingletonOnly

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership
open scoped BigOperators

/-- Nine shared OR gates compute the five functions OR_{v != j} x_v.
  For each pair {a,b}, two AND gates conjoin the other three such functions.
  This example concerns singleton tests only, not the full-complement theorem. -/
def circuit : Circuit :=
  ⟨[⟨GateOp.or, [0, 1]⟩,
    ⟨GateOp.or, [5, 2]⟩,
    ⟨GateOp.or, [6, 3]⟩,
    ⟨GateOp.or, [3, 4]⟩,
    ⟨GateOp.or, [2, 8]⟩,
    ⟨GateOp.or, [1, 9]⟩,
    ⟨GateOp.or, [0, 9]⟩,
    ⟨GateOp.or, [5, 8]⟩,
    ⟨GateOp.or, [6, 4]⟩,
    ⟨GateOp.and, [12, 13]⟩,
    ⟨GateOp.and, [14, 7]⟩,
    ⟨GateOp.and, [11, 13]⟩,
    ⟨GateOp.and, [16, 7]⟩,
    ⟨GateOp.and, [11, 12]⟩,
    ⟨GateOp.and, [18, 7]⟩,
    ⟨GateOp.and, [11, 12]⟩,
    ⟨GateOp.and, [20, 13]⟩,
    ⟨GateOp.and, [10, 13]⟩,
    ⟨GateOp.and, [22, 7]⟩,
    ⟨GateOp.and, [10, 12]⟩,
    ⟨GateOp.and, [24, 7]⟩,
    ⟨GateOp.and, [10, 12]⟩,
    ⟨GateOp.and, [26, 13]⟩,
    ⟨GateOp.and, [10, 11]⟩,
    ⟨GateOp.and, [28, 7]⟩,
    ⟨GateOp.and, [10, 11]⟩,
    ⟨GateOp.and, [30, 13]⟩,
    ⟨GateOp.and, [10, 11]⟩,
    ⟨GateOp.and, [32, 12]⟩], 33⟩

def pairSets : List (Finset (Fin 5)) :=
  [{0, 1}, {0, 2}, {0, 3}, {0, 4}, {1, 2}, {1, 3}, {1, 4}, {2, 3}, {2, 4}, {3, 4}]

def outputWires : List ℕ := [15, 17, 19, 21, 23, 25, 27, 29, 31, 33]

def pairSet (i : Fin 10) : Finset (Fin 5) := pairSets.getD i.val ∅

def outputWire (i : Fin 10) : ℕ := outputWires.getD i.val 0

def wire (w : ℕ) (x : Fin 5 → Bool) : Bool :=
  (circuit.wires (List.ofFn x)).getD w false

def isOr : GateOp → Bool
  | GateOp.or => true
  | _ => false

lemma isOr_iff (op : GateOp) : isOr op = true ↔ op = GateOp.or := by
  cases op <;> simp [isOr]

def orGates : Finset ℕ :=
  (Finset.range circuit.size).filter fun j => isOr (gateAt circuit j).op = true

lemma mem_orGates (j : ℕ) :
    j ∈ orGates ↔ j < circuit.size ∧ (gateAt circuit j).op = GateOp.or := by
  simp [orGates, isOr_iff]

lemma circuit_ao2 : IsAO2 5 circuit := by decide

lemma circuit_size : circuit.size = 29 := by decide

lemma outputs_valid : ∀ i : Fin 10, outputWire i < 5 + circuit.size := by decide

lemma or_count : orGates.card = 9 := by decide

lemma pair_card : ∀ i : Fin 10, (pairSet i).card = 2 := by decide

lemma singleton_values : ∀ (i : Fin 10) (v : Fin 5),
    wire (outputWire i) (pairInput v v) = decide (v ∈ pairSet i) := by decide

lemma outside_singletons_false : ∀ (i : Fin 10) (v : Fin 5), v ∉ pairSet i →
    wire (outputWire i) (pairInput v v) = false := by
  intro i v hv
  rw [singleton_values]
  exact decide_eq_false hv

lemma pairwise_intersections : ∀ i j : Fin 10, i ≠ j →
    (pairSet i ∩ pairSet j).card ≤ 1 := by decide

lemma support_charge_sum : (∑ i : Fin 10, ((pairSet i).card - 1)) = 10 := by decide

lemma full_complements_true : ∀ i : Fin 10,
    wire (outputWire i) (fun v => decide (v ∉ pairSet i)) = true := by decide

lemma singleton_only_bound_fails :
    ¬ (∑ i : Fin 10, ((pairSet i).card - 1)) ≤ orGates.card := by
  rw [support_charge_sum, or_count]
  decide

end PEqualNP.Outside.L_meta_3566.SingletonOnly

namespace PEqualNP.Outside.L_meta_3566.AndIndexTransport

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

noncomputable def andIndices (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter fun j => (gateAt C j).op = .and

noncomputable def badAnds {n : ℕ} (C : Circuit) (P : (Fin n → Bool) → Prop) : Finset ℕ := by
  classical
  exact (andIndices C).filter fun j => ∃ x, P x ∧ gateVal n C j x = true

lemma mem_andIndices {C : Circuit} {j : ℕ} :
    j ∈ andIndices C ↔ j < C.gates.length ∧ (gateAt C j).op = .and := by
  classical
  simp [andIndices]

lemma mem_badAnds {n : ℕ} {C : Circuit} {P : (Fin n → Bool) → Prop} {j : ℕ} :
    j ∈ badAnds C P ↔ j ∈ andIndices C ∧ ∃ x, P x ∧ gateVal n C j x = true := by
  classical
  simp [badAnds]

lemma badAnds_image {n : ℕ} (C D : Circuit) (f : ℕ → ℕ)
    (P : (Fin n → Bool) → Prop)
    (hforward : ∀ j ∈ andIndices C, f j ∈ andIndices D)
    (hsurj : ∀ k ∈ andIndices D, ∃ j ∈ andIndices C, f j = k)
    (hval : ∀ j ∈ andIndices C, ∀ x, P x → gateVal n D (f j) x = gateVal n C j x) :
    badAnds D P = (badAnds C P).image f := by
  classical
  ext k
  constructor
  · intro hk
    obtain ⟨hkA, x, hx, hv⟩ := mem_badAnds.mp hk
    obtain ⟨j, hj, rfl⟩ := hsurj k hkA
    exact Finset.mem_image.mpr ⟨j, mem_badAnds.mpr ⟨hj, x, hx, (hval j hj x hx) ▸ hv⟩, rfl⟩
  · intro hk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨hjA, x, hx, hv⟩ := mem_badAnds.mp hj
    exact mem_badAnds.mpr ⟨hforward j hjA, x, hx, (hval j hjA x hx).symm ▸ hv⟩

lemma badAnds_card {n : ℕ} (C D : Circuit) (f : ℕ → ℕ)
    (P : (Fin n → Bool) → Prop)
    (hforward : ∀ j ∈ andIndices C, f j ∈ andIndices D)
    (hsurj : ∀ k ∈ andIndices D, ∃ j ∈ andIndices C, f j = k)
    (hinj : Set.InjOn f (andIndices C : Set ℕ))
    (hval : ∀ j ∈ andIndices C, ∀ x, P x → gateVal n D (f j) x = gateVal n C j x) :
    (badAnds D P).card = (badAnds C P).card := by
  classical
  rw [badAnds_image C D f P hforward hsurj hval]
  apply Finset.card_image_of_injOn
  intro i hi j hj hij
  exact hinj (mem_badAnds.mp hi).1 (mem_badAnds.mp hj).1 hij

lemma junk_eq_badAnds {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) :
    junk G C = badAnds C (fun x => graphFun G ∅ x = false) := by
  classical
  ext j
  have hjunk : j ∈ junk G C ↔ j < C.gates.length ∧ IsDirtyAnd n G C j := by
    unfold PEqualNP.TopForm.junk PEqualNP.TopForm.gatesWhere
    rw [Finset.mem_filter, Finset.mem_range]
  rw [hjunk, mem_badAnds, mem_andIndices]
  change (j < C.gates.length ∧ (gateAt C j).op = .and ∧ j < C.gates.length ∧
    ∃ x, gateVal n C j x = true ∧ graphFun G ∅ x = false) ↔ _
  constructor
  · rintro ⟨hj, hop, _, x, hv, hx⟩
    exact ⟨⟨hj, hop⟩, x, hx, hv⟩
  · rintro ⟨⟨hj, hop⟩, x, hx, hv⟩
    exact ⟨hj, hop, hj, x, hv, hx⟩

lemma junk_image {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit) (f : ℕ → ℕ)
    (hforward : ∀ j ∈ andIndices C, f j ∈ andIndices D)
    (hsurj : ∀ k ∈ andIndices D, ∃ j ∈ andIndices C, f j = k)
    (hval : ∀ j ∈ andIndices C, ∀ x, graphFun G ∅ x = false →
      gateVal n D (f j) x = gateVal n C j x) :
    junk G D = (junk G C).image f := by
  rw [junk_eq_badAnds, junk_eq_badAnds]
  exact badAnds_image C D f _ hforward hsurj hval

lemma junk_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit) (f : ℕ → ℕ)
    (hforward : ∀ j ∈ andIndices C, f j ∈ andIndices D)
    (hsurj : ∀ k ∈ andIndices D, ∃ j ∈ andIndices C, f j = k)
    (hinj : Set.InjOn f (andIndices C : Set ℕ))
    (hval : ∀ j ∈ andIndices C, ∀ x, graphFun G ∅ x = false →
      gateVal n D (f j) x = gateVal n C j x) :
    (junk G D).card = (junk G C).card := by
  rw [junk_eq_badAnds, junk_eq_badAnds]
  exact badAnds_card C D f _ hforward hsurj hinj hval

noncomputable def pairLeakyAnds {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) : Finset ℕ := by
  classical
  exact (andIndices C).filter fun j =>
    ∃ a b, ¬ G.Adj a b ∧ gateVal n C j (pairInput a b) = true

lemma mem_pairLeakyAnds {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit} {j : ℕ} :
    j ∈ pairLeakyAnds G C ↔ j ∈ andIndices C ∧
      ∃ a b, ¬ G.Adj a b ∧ gateVal n C j (pairInput a b) = true := by
  classical
  simp [pairLeakyAnds]

lemma pairLeakyAnds_eq_badAnds {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) :
    pairLeakyAnds G C = badAnds C (fun x => ∃ a b, ¬ G.Adj a b ∧ x = pairInput a b) := by
  classical
  ext j
  rw [mem_pairLeakyAnds, mem_badAnds]
  constructor
  · rintro ⟨hj, a, b, hab, hv⟩
    exact ⟨hj, pairInput a b, ⟨a, b, hab, rfl⟩, hv⟩
  · rintro ⟨hj, x, ⟨a, b, hab, rfl⟩, hv⟩
    exact ⟨hj, a, b, hab, hv⟩

lemma pairLeakyAnds_image {n : ℕ} (G : SimpleGraph (Fin n))
    (C D : Circuit) (f : ℕ → ℕ)
    (hforward : ∀ j ∈ andIndices C, f j ∈ andIndices D)
    (hsurj : ∀ k ∈ andIndices D, ∃ j ∈ andIndices C, f j = k)
    (hval : ∀ j ∈ andIndices C, ∀ a b, ¬ G.Adj a b →
      gateVal n D (f j) (pairInput a b) = gateVal n C j (pairInput a b)) :
    pairLeakyAnds G D = (pairLeakyAnds G C).image f := by
  rw [pairLeakyAnds_eq_badAnds, pairLeakyAnds_eq_badAnds]
  apply badAnds_image C D f _ hforward hsurj
  rintro j hj x ⟨a, b, hab, rfl⟩
  exact hval j hj a b hab

lemma pairLeakyAnds_card {n : ℕ} (G : SimpleGraph (Fin n))
    (C D : Circuit) (f : ℕ → ℕ)
    (hforward : ∀ j ∈ andIndices C, f j ∈ andIndices D)
    (hsurj : ∀ k ∈ andIndices D, ∃ j ∈ andIndices C, f j = k)
    (hinj : Set.InjOn f (andIndices C : Set ℕ))
    (hval : ∀ j ∈ andIndices C, ∀ a b, ¬ G.Adj a b →
      gateVal n D (f j) (pairInput a b) = gateVal n C j (pairInput a b)) :
    (pairLeakyAnds G D).card = (pairLeakyAnds G C).card := by
  rw [pairLeakyAnds_eq_badAnds, pairLeakyAnds_eq_badAnds]
  apply badAnds_card C D f _ hforward hsurj hinj
  rintro j hj x ⟨a, b, hab, rfl⟩
  exact hval j hj a b hab

end PEqualNP.Outside.L_meta_3566.AndIndexTransport

/-!
  # Helpers for L-meta-2604 (the implicant lift)

  The fold inside `Circuit.wires`, run from an arbitrary wire list: it only appends, one value per
  gate, so a wire that already exists keeps its value.
-/

namespace PEqualNP.Outside.L_meta_3566.HoistEval

open PEqualNP.CircuitLowerBounds

/-- One gate step of `Circuit.wires`. -/
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem foldl_step_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ s : List Bool, gs.foldl step w = w ++ s ∧ s.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨s, hs, hl⟩ := ih (step w g)
    refine ⟨(g.op.eval (g.inputs.map fun i => w.getD i false)) :: s, ?_, by simp [hl]⟩
    rw [List.foldl_cons, hs]
    simp [step]

theorem foldl_step_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  obtain ⟨s, hs, hl⟩ := foldl_step_prefix gs w
  simp [hs, hl]

theorem getD_append_left (w s : List Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ s).getD i false = w.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem foldl_step_getD (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  obtain ⟨s, hs, _⟩ := foldl_step_prefix gs w
  rw [hs, getD_append_left w s i hi]

theorem getD_append_singleton_last (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_append_singleton (w : List Bool) (b : Bool) (i : ℕ) (hi : i ≠ w.length) :
    (w ++ [b]).getD i false = w.getD i false := by
  rcases Nat.lt_or_gt_of_ne hi with h | h
  · exact getD_append_left w [b] i h
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega : (w ++ [b]).length ≤ i),
      List.getElem?_eq_none (by omega : w.length ≤ i)]

end PEqualNP.Outside.L_meta_3566.HoistEval


/-!
  # Helpers for L-meta-2715 (the implicant lift iterated to a fixed point)

  * `foldl_set_equiv`: replacing a gate by one with the same value on every wire list keeps the
  wires.
  * `del n k u E`: delete gate `k` of `E`, redirecting every read of wire `n + k` to `u` and
  shifting every wire above it down by one. If gate `k` always equals wire `u` (`u < n + k`),
  the function is kept (`del_fun`).
-/

namespace PEqualNP.Outside.L_meta_3566.HoistBase

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3566.HoistEval
open PEqualNP.MetaComplexity.NestedCover

/-! ## Replacing a gate by an equivalent one -/

theorem foldl_set_equiv (gs : List Gate) (k : ℕ) (g g' : Gate) (hg : gs[k]? = some g)
    (heq : ∀ w : List Bool, g'.op.eval (g'.inputs.map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false)) (w0 : List Bool) :
    (gs.set k g').foldl step w0 = gs.foldl step w0 := by
  induction gs generalizing k w0 with
  | nil => simp
  | cons h gs ih =>
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hg
      subst hg
      simp only [List.set_cons_zero, List.foldl_cons]
      congr 1
      unfold step
      rw [heq]
    | succ k =>
      simp only [List.getElem?_cons_succ] at hg
      simp only [List.set_cons_succ, List.foldl_cons]
      exact ih k hg _

/-! ## The value of a gate -/

theorem foldl_split (gs : List Gate) (k : ℕ) (g : Gate) (hg : gs[k]? = some g) (w0 : List Bool) :
    gs.foldl step w0 = (gs.drop (k + 1)).foldl step (step ((gs.take k).foldl step w0) g) := by
  have hk : k < gs.length := by
    rcases (List.getElem?_eq_some_iff.mp hg) with ⟨hk, _⟩
    exact hk
  have hgk : gs[k] = g := (List.getElem?_eq_some_iff.mp hg).2
  conv_lhs => rw [← List.take_append_drop k gs, List.drop_eq_getElem_cons hk, hgk]
  rw [List.foldl_append, List.foldl_cons]

theorem take_fold_length (gs : List Gate) (k : ℕ) (hk : k < gs.length) (w0 : List Bool) :
    ((gs.take k).foldl step w0).length = w0.length + k := by
  rw [foldl_step_length, List.length_take]
  omega

/-- A gate `OR [u]` at position `k` has the value of wire `u`. -/
theorem wires_copy (F : Circuit) (k u : ℕ) (hk : F.gates[k]? = some ⟨GateOp.or, [u]⟩)
    (w0 : List Bool) (hu : u < w0.length + k) :
    (F.wires w0).getD (w0.length + k) false = (F.wires w0).getD u false := by
  have hk' : k < F.gates.length := (List.getElem?_eq_some_iff.mp hk).1
  rw [wires_eq, foldl_split F.gates k _ hk w0]
  have hl := take_fold_length F.gates k hk' w0
  set Wp := (F.gates.take k).foldl step w0
  rw [foldl_step_getD _ _ _ (by simp [step]; omega), foldl_step_getD _ _ _ (by simp [step]; omega)]
  unfold step
  rw [← hl, getD_append_singleton_last, getD_append_left _ _ _ (by omega)]
  simp [GateOp.eval]

/-! ## Deleting a copy gate -/

/-- The wire renaming of a deletion of wire `m`, whose reads go to `u`. -/
def sig (m u : ℕ) (i : ℕ) : ℕ := if i < m then i else if i = m then u else i - 1

/-- A gate with its reads renamed. -/
def rd (m u : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (sig m u)⟩

/-- The gate renaming of a deletion of gate `k`. -/
def sg (k : ℕ) (j : ℕ) : ℕ := if j < k then j else j - 1

/-- Delete gate `k` of `E`, redirecting its reads to `u`. -/
def del (n k u : ℕ) (E : Circuit) : Circuit :=
  ⟨(E.gates.eraseIdx k).map (rd (n + k) u), sig (n + k) u E.output⟩

theorem sig_gate (n k u j : ℕ) (hj : j ≠ k) : sig (n + k) u (n + j) = n + sg k j := by
  unfold sig sg
  split_ifs <;> omega

/-- The simulation relation between the old wire list `a` and the new one `b`. -/
def Rel (m u : ℕ) (a b : List Bool) : Prop :=
  a.length = b.length + 1 ∧ m < a.length ∧ ∀ i, b.getD (sig m u i) false = a.getD i false

theorem getD_oob (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

theorem rel_step (m u : ℕ) (hu : u < m) (a b : List Bool) (g : Gate) (h : Rel m u a b) :
    Rel m u (step a g) (step b (rd m u g)) := by
  obtain ⟨hl, hm, hv⟩ := h
  have hev : (rd m u g).op.eval ((rd m u g).inputs.map fun i => b.getD i false) =
      g.op.eval (g.inputs.map fun i => a.getD i false) := by
    simp only [rd, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    exact hv i
  unfold step
  rw [hev]
  set v := g.op.eval (g.inputs.map fun i => a.getD i false)
  refine ⟨by simp [hl], by simp; omega, ?_⟩
  intro i
  rcases Nat.lt_trichotomy i a.length with h1 | h1 | h1
  · have hs : sig m u i < b.length := by unfold sig; split_ifs <;> omega
    rw [getD_append_left _ _ _ hs, getD_append_left _ _ _ h1, hv]
  · have hs : sig m u i = b.length := by unfold sig; split_ifs <;> omega
    rw [hs, getD_append_singleton_last, h1, getD_append_singleton_last]
  · have hs : sig m u i > b.length := by unfold sig; split_ifs <;> omega
    rw [getD_oob _ _ (by simp; omega), getD_oob _ _ (by simp; omega)]

theorem rel_fold (m u : ℕ) (hu : u < m) (gs : List Gate) : ∀ a b : List Bool, Rel m u a b →
    Rel m u (gs.foldl step a) ((gs.map (rd m u)).foldl step b) := by
  induction gs with
  | nil => intro a b h; simpa using h
  | cons g gs ih =>
    intro a b h
    simp only [List.foldl_cons, List.map_cons]
    exact ih _ _ (rel_step m u hu a b g h)

theorem rd_id (m u : ℕ) (g : Gate) (h : ∀ i ∈ g.inputs, i < m) : rd m u g = g := by
  obtain ⟨op, ins⟩ := g
  simp only [rd, Gate.mk.injEq, true_and]
  conv_rhs => rw [← List.map_id ins]
  apply List.map_congr_left
  intro i hi
  have := h i hi
  simp [sig, this]

theorem del_fun (n k u : ℕ) (E : Circuit) (hk : k < E.gates.length) (hu : u < n + k)
    (hpre : ∀ g ∈ E.gates.take k, ∀ i ∈ g.inputs, i < n + k)
    (hcopy : ∀ x : Fin n → Bool,
      (E.wires (List.ofFn x)).getD (n + k) false = (E.wires (List.ofFn x)).getD u false) :
    circuitFun n (del n k u E) = circuitFun n E := by
  funext x
  have hc := hcopy x
  unfold circuitFun Circuit.eval
  have hgk : E.gates[k]? = some E.gates[k] := List.getElem?_eq_getElem hk
  set gk := E.gates[k]
  set w0 := List.ofFn x with hw0
  have hw0l : w0.length = n := by simp [hw0]
  have hl := take_fold_length E.gates k hk w0
  rw [hw0l] at hl
  set Wp := (E.gates.take k).foldl step w0 with hWp
  have hW : E.wires w0 = (E.gates.drop (k + 1)).foldl step (step Wp gk) := by
    rw [wires_eq, foldl_split E.gates k gk hgk w0]
  have hD : (del n k u E).wires w0 =
      ((E.gates.drop (k + 1)).map (rd (n + k) u)).foldl step Wp := by
    rw [wires_eq]
    simp only [del]
    rw [List.eraseIdx_eq_take_drop_succ, List.map_append, List.foldl_append]
    congr 1
    rw [hWp]
    congr 1
    conv_rhs => rw [← List.map_id (E.gates.take k)]
    apply List.map_congr_left
    intro g hg
    exact rd_id _ _ g (hpre g hg)
  -- the value of gate k equals that of u
  have hvk : (step Wp gk).getD (n + k) false = Wp.getD u false := by
    rw [hW, foldl_step_getD _ _ _ (by simp [step]; omega),
      foldl_step_getD _ _ _ (by simp [step]; omega)] at hc
    rw [hc]
    unfold step
    exact getD_append_left _ _ _ (by omega)
  have hrel0 : Rel (n + k) u (step Wp gk) Wp := by
    refine ⟨by simp [step], by simp [step]; omega, ?_⟩
    intro i
    rcases Nat.lt_trichotomy i (n + k) with h1 | h1 | h1
    · have : sig (n + k) u i = i := by simp [sig, h1]
      rw [this]
      unfold step
      rw [getD_append_left _ _ _ (by omega)]
    · have : sig (n + k) u i = u := by simp [sig, h1]
      rw [this, h1, hvk]
    · have : sig (n + k) u i = i - 1 := by
        unfold sig; split_ifs <;> omega
      rw [this, getD_oob _ _ (by omega), getD_oob _ _ (by simp [step]; omega)]
  have hrel := rel_fold (n + k) u hu (E.gates.drop (k + 1)) _ _ hrel0
  rw [hD, hW]
  exact hrel.2.2 E.output

theorem del_length (n k u : ℕ) (E : Circuit) (hk : k < E.gates.length) :
    (del n k u E).gates.length + 1 = E.gates.length := by
  simp only [del, List.length_map, List.length_eraseIdx, if_pos hk]
  omega

theorem del_get (n k u : ℕ) (E : Circuit) (j : ℕ) (g : Gate) (hj : j ≠ k)
    (h : E.gates[j]? = some g) : (del n k u E).gates[sg k j]? = some (rd (n + k) u g) := by
  by_cases h1 : j < k
  · simp only [del, sg, if_pos h1, List.getElem?_map, List.getElem?_eraseIdx, h]; rfl
  · have h2 : ¬ (j - 1 < k) := by omega
    have h3 : j - 1 + 1 = j := by omega
    simp only [del, sg, if_neg h1, List.getElem?_map, List.getElem?_eraseIdx, if_neg h2, h3, h]
    rfl

theorem del_get_inv (n k u : ℕ) (E : Circuit) (j : ℕ) (g : Gate)
    (h : (del n k u E).gates[j]? = some g) :
    ∃ g0, E.gates[if j < k then j else j + 1]? = some g0 ∧ g = rd (n + k) u g0 := by
  simp only [del, List.getElem?_map, List.getElem?_eraseIdx] at h
  split_ifs at h ⊢ with h1
  · cases hh : E.gates[j]? with
    | none => rw [hh] at h; simp at h
    | some g0 => rw [hh] at h; simp at h; exact ⟨g0, rfl, h.symm⟩
  · cases hh : E.gates[j + 1]? with
    | none => rw [hh] at h; simp at h
    | some g0 => rw [hh] at h; simp at h; exact ⟨g0, rfl, h.symm⟩

theorem del_mono (n k u : ℕ) (E : Circuit) (hE : Monotone2 E) : Monotone2 (del n k u E) := by
  intro g hg
  simp only [del, List.mem_map] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  have := hE g0 (List.mem_of_mem_eraseIdx hg0)
  simpa [rd] using this

theorem gateAt_some (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    C.gates[j]? = some (gateAt C j) := by
  rw [List.getElem?_eq_getElem hj]
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

theorem readsBack_get (n : ℕ) (C : Circuit) (h : ReadsBack n C) (j : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) : ∀ i ∈ g.inputs, i < n + j := by
  have hj : j < C.gates.length := (List.getElem?_eq_some_iff.mp hg).1
  have := gateAt_some C j hj
  rw [hg] at this
  cases this
  exact h j hj

theorem readsBack_of_get (n : ℕ) (C : Circuit)
    (h : ∀ j (g : Gate), C.gates[j]? = some g → ∀ i ∈ g.inputs, i < n + j) : ReadsBack n C := by
  intro j hj
  exact h j _ (gateAt_some C j hj)

theorem del_readsBack (n k u : ℕ) (E : Circuit) (hE : ReadsBack n E) (hu : u < n + k) :
    ReadsBack n (del n k u E) := by
  apply readsBack_of_get
  intro j g hg
  obtain ⟨g0, hg0, rfl⟩ := del_get_inv n k u E j g hg
  have hr := readsBack_get n E hE _ g0 hg0
  intro i hi
  simp only [rd, List.mem_map] at hi
  obtain ⟨i0, hi0, rfl⟩ := hi
  have := hr i0 hi0
  unfold sig
  split_ifs at this ⊢ <;> omega

theorem readsBack_take (n : ℕ) (C : Circuit) (h : ReadsBack n C) (k : ℕ) :
    ∀ g ∈ C.gates.take k, ∀ i ∈ g.inputs, i < n + k := by
  intro g hg i hi
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
  rw [List.getElem_take] at hi
  have hjl : j < k := by simp at hj; omega
  have hj' : j < C.gates.length := by simp at hj; omega
  have := readsBack_get n C h j _ (List.getElem?_eq_getElem hj') i hi
  omega

end PEqualNP.Outside.L_meta_3566.HoistBase

namespace PEqualNP.Outside.L_meta_3566.HoistNegative
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_3566.HoistEval PEqualNP.Outside.L_meta_3566.HoistBase

lemma foldl_set_state (gs : List Gate) (k : ℕ) (g g' : Gate) (hg : gs[k]? = some g)
    (w0 : List Bool)
    (heq : g'.op.eval (g'.inputs.map fun i => ((gs.take k).foldl step w0).getD i false) =
      g.op.eval (g.inputs.map fun i => ((gs.take k).foldl step w0).getD i false)) :
    (gs.set k g').foldl step w0 = gs.foldl step w0 := by
  induction gs generalizing k w0 with
  | nil => simp at hg
  | cons h gs ih =>
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hg
      subst h
      simp only [List.take_zero, List.foldl_nil] at heq
      simp only [List.set_cons_zero, List.foldl_cons]
      congr 1
      unfold step
      rw [heq]
    | succ k =>
      simp only [List.getElem?_cons_succ] at hg
      simp only [List.take_succ_cons, List.foldl_cons] at heq
      simp only [List.set_cons_succ, List.foldl_cons]
      exact ih k hg _ heq

lemma prefix_wire (gs : List Gate) (k : ℕ) (hk : k < gs.length)
    (w0 : List Bool) (i : ℕ) (hi : i < w0.length + k) :
    (gs.foldl step w0).getD i false = ((gs.take k).foldl step w0).getD i false := by
  have hl := take_fold_length gs k hk w0
  have heq : gs.foldl step w0 = (gs.drop k).foldl step ((gs.take k).foldl step w0) := by
    rw [← List.foldl_append, List.take_append_drop]
  rw [heq]
  exact foldl_step_getD _ _ _ (by omega)

lemma copy_or_wires_eq_of_false (n : ℕ) (D : Circuit) (k u t : ℕ)
    (hkg : D.gates[k]? = some ⟨GateOp.or, [u,t]⟩)
    (ht : t < n + k) (x : Fin n → Bool)
    (hfalse : (D.wires (List.ofFn x)).getD t false = false) :
    (D.gates.set k ⟨GateOp.or, [u]⟩).foldl step (List.ofFn x) =
      D.gates.foldl step (List.ofFn x) := by
  have hk := (List.getElem?_eq_some_iff.mp hkg).1
  have htP : ((D.gates.take k).foldl step (List.ofFn x)).getD t false = false := by
    rw [← prefix_wire D.gates k hk (List.ofFn x) t (by simpa using ht)]
    exact hfalse
  apply foldl_set_state D.gates k _ _ hkg (List.ofFn x)
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, htP,
    id_eq, Bool.false_or, Bool.or_false]

def lifted (n : ℕ) (D : Circuit) (k u t : ℕ) : Circuit :=
  ⟨D.gates.set k ⟨GateOp.or, [u]⟩ ++ [⟨GateOp.or, [D.output,t]⟩], n+D.gates.length⟩

lemma lifted_get_ne (n : ℕ) (D : Circuit) (k u t j : ℕ)
    (hjk : j ≠ k) (hj : j < D.gates.length) :
    (lifted n D k u t).gates[j]? = D.gates[j]? := by
  simp only [lifted]
  rw [List.getElem?_append_left (by simpa using hj), List.getElem?_set_ne (Ne.symm hjk)]

lemma lifted_get_copy (n : ℕ) (D : Circuit) (k u t : ℕ) (hk : k < D.gates.length) :
    (lifted n D k u t).gates[k]? = some ⟨GateOp.or,[u]⟩ := by
  simp only [lifted]
  rw [List.getElem?_append_left (by simpa using hk)]
  simp [List.getElem?_set, hk]

lemma lifted_get_last (n : ℕ) (D : Circuit) (k u t : ℕ) :
    (lifted n D k u t).gates[D.gates.length]? = some ⟨GateOp.or,[D.output,t]⟩ := by
  simp only [lifted]
  rw [List.getElem?_append_right (by simp)]
  simp

lemma lifted_readsBack (n : ℕ) (D : Circuit) (k u t : ℕ)
    (hR : ReadsBack n D) (hk : k < D.gates.length)
    (hu : u < n+k) (ht : t < n+k) (ho : D.output < n+D.gates.length) :
    ReadsBack n (lifted n D k u t) := by
  apply readsBack_of_get
  intro j g hg i hi
  rcases Nat.lt_trichotomy j D.gates.length with hj | hj | hj
  · by_cases hjk : j = k
    · subst j
      rw [lifted_get_copy n D k u t hk] at hg
      cases hg
      simp at hi
      omega
    · rw [lifted_get_ne n D k u t j hjk hj] at hg
      exact readsBack_get n D hR j g hg i hi
  · subst j
    rw [lifted_get_last] at hg
    cases hg
    simp at hi
    omega
  · have hlen : (lifted n D k u t).gates.length = D.gates.length+1 := by simp [lifted]
    rw [List.getElem?_eq_none (by omega)] at hg
    cases hg

lemma lifted_negative_wires (n : ℕ) (D : Circuit) (k u t : ℕ)
    (hkg : D.gates[k]? = some ⟨GateOp.or,[u,t]⟩) (ht : t < n+k)
    (x : Fin n → Bool) (htfalse : (D.wires (List.ofFn x)).getD t false = false)
    (hofalse : circuitFun n D x = false) :
    (lifted n D k u t).wires (List.ofFn x) = D.wires (List.ofFn x) ++ [false] := by
  have hc := copy_or_wires_eq_of_false n D k u t hkg ht x htfalse
  change (D.gates.set k _ ++ [_]).foldl step (List.ofFn x) = _
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil, hc]
  change step (D.wires (List.ofFn x)) _ = _
  change (D.wires (List.ofFn x)).getD D.output false = false at hofalse
  simp only [step, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
    htfalse, hofalse, id_eq, Bool.false_or]

end PEqualNP.Outside.L_meta_3566.HoistNegative

namespace PEqualNP.Outside.L_meta_3566.HoistBase
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3566.HoistEval

theorem del_wire (n k u : ℕ) (E : Circuit) (hk : k < E.gates.length) (hu : u < n + k)
    (hpre : ∀ g ∈ E.gates.take k, ∀ i ∈ g.inputs, i < n + k)
    (hcopy : ∀ x : Fin n → Bool,
      (E.wires (List.ofFn x)).getD (n + k) false = (E.wires (List.ofFn x)).getD u false) :
    ∀ (x : Fin n → Bool) (i : ℕ),
      ((del n k u E).wires (List.ofFn x)).getD (sig (n+k) u i) false =
        (E.wires (List.ofFn x)).getD i false := by
  intro x i
  have hc := hcopy x
  have hgk : E.gates[k]? = some E.gates[k] := List.getElem?_eq_getElem hk
  set gk := E.gates[k]
  set w0 := List.ofFn x with hw0
  have hw0l : w0.length = n := by simp [hw0]
  have hl := take_fold_length E.gates k hk w0
  rw [hw0l] at hl
  set Wp := (E.gates.take k).foldl step w0 with hWp
  have hW : E.wires w0 = (E.gates.drop (k + 1)).foldl step (step Wp gk) := by
    rw [wires_eq, foldl_split E.gates k gk hgk w0]
  have hD : (del n k u E).wires w0 =
      ((E.gates.drop (k + 1)).map (rd (n + k) u)).foldl step Wp := by
    rw [wires_eq]
    simp only [del]
    rw [List.eraseIdx_eq_take_drop_succ, List.map_append, List.foldl_append]
    congr 1
    rw [hWp]
    congr 1
    conv_rhs => rw [← List.map_id (E.gates.take k)]
    apply List.map_congr_left
    intro g hg
    exact rd_id _ _ g (hpre g hg)
  -- the value of gate k equals that of u
  have hvk : (step Wp gk).getD (n + k) false = Wp.getD u false := by
    rw [hW, foldl_step_getD _ _ _ (by simp [step]; omega),
      foldl_step_getD _ _ _ (by simp [step]; omega)] at hc
    rw [hc]
    unfold step
    exact getD_append_left _ _ _ (by omega)
  have hrel0 : Rel (n + k) u (step Wp gk) Wp := by
    refine ⟨by simp [step], by simp [step]; omega, ?_⟩
    intro i
    rcases Nat.lt_trichotomy i (n + k) with h1 | h1 | h1
    · have : sig (n + k) u i = i := by simp [sig, h1]
      rw [this]
      unfold step
      rw [getD_append_left _ _ _ (by omega)]
    · have : sig (n + k) u i = u := by simp [sig, h1]
      rw [this, h1, hvk]
    · have : sig (n + k) u i = i - 1 := by
        unfold sig; split_ifs <;> omega
      rw [this, getD_oob _ _ (by omega), getD_oob _ _ (by simp [step]; omega)]
  have hrel := rel_fold (n + k) u hu (E.gates.drop (k + 1)) _ _ hrel0
  rw [hD, hW]
  exact hrel.2.2 i


end PEqualNP.Outside.L_meta_3566.HoistBase

namespace PEqualNP.Outside.L_meta_3566.HoistNegative
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_3566.HoistEval PEqualNP.Outside.L_meta_3566.HoistBase

def hoisted (n : ℕ) (D : Circuit) (k u t : ℕ) : Circuit :=
  del n k u (lifted n D k u t)

lemma hoisted_negative_wire (n : ℕ) (D : Circuit) (k u t : ℕ)
    (hR : ReadsBack n D) (hkg : D.gates[k]? = some ⟨GateOp.or,[u,t]⟩)
    (hu : u < n+k) (ht : t < n+k) (ho : D.output < n+D.gates.length)
    (x : Fin n → Bool) (htfalse : (D.wires (List.ofFn x)).getD t false = false)
    (hofalse : circuitFun n D x = false) (i : ℕ) (hi : i < n+D.gates.length) :
    ((hoisted n D k u t).wires (List.ofFn x)).getD (sig (n+k) u i) false =
      (D.wires (List.ofFn x)).getD i false := by
  have hk : k < D.gates.length := (List.getElem?_eq_some_iff.mp hkg).1
  let E := lifted n D k u t
  have hER := lifted_readsBack n D k u t hR hk hu ht ho
  have hEk := lifted_get_copy n D k u t hk
  have hkE : k < E.gates.length := by simp [E, lifted]; omega
  have hcopy : ∀ y : Fin n → Bool,
      (E.wires (List.ofFn y)).getD (n+k) false = (E.wires (List.ofFn y)).getD u false := by
    intro y
    simpa using wires_copy E k u hEk (List.ofFn y) (by simpa using hu)
  have hw := del_wire n k u E hkE hu (readsBack_take n E hER k) hcopy x i
  have hl : (D.wires (List.ofFn x)).length = n+D.gates.length := by
    rw [wires_eq, foldl_step_length, List.length_ofFn]
  change ((hoisted n D k u t).wires (List.ofFn x)).getD _ false = _ at hw
  rw [lifted_negative_wires n D k u t hkg ht x htfalse hofalse,
    List.getD_append _ _ _ _ (by omega)] at hw
  exact hw

lemma hoisted_negative_gate (n : ℕ) (D : Circuit) (k u t j : ℕ)
    (hR : ReadsBack n D) (hkg : D.gates[k]? = some ⟨GateOp.or,[u,t]⟩)
    (hu : u < n+k) (ht : t < n+k) (ho : D.output < n+D.gates.length)
    (hj : j < D.gates.length) (hjk : j ≠ k)
    (x : Fin n → Bool) (htfalse : (D.wires (List.ofFn x)).getD t false = false)
    (hofalse : circuitFun n D x = false) :
    ((hoisted n D k u t).wires (List.ofFn x)).getD (n+sg k j) false =
      (D.wires (List.ofFn x)).getD (n+j) false := by
  have h := hoisted_negative_wire n D k u t hR hkg hu ht ho x htfalse hofalse
    (n+j) (by omega)
  rw [sig_gate n k u j hjk] at h
  exact h

lemma hoisted_get (n : ℕ) (D : Circuit) (k u t j : ℕ) (g : Gate)
    (hjk : j ≠ k) (hj : D.gates[j]? = some g) :
    (hoisted n D k u t).gates[sg k j]? = some (rd (n+k) u g) := by
  have hjlt : j < D.gates.length := (List.getElem?_eq_some_iff.mp hj).1
  apply del_get n k u (lifted n D k u t) j g hjk
  rw [lifted_get_ne n D k u t j hjk hjlt, hj]

lemma clean_hoist_negative_gate {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D : Circuit) (k u t j : ℕ)
    (hR : ReadsBack n D) (hkg : D.gates[k]? = some ⟨GateOp.or,[u,t]⟩)
    (hu : u < n+k) (ht : t < n+k) (ho : D.output < n+D.gates.length)
    (hfun : circuitFun n D = graphFun G ∅)
    (hclean : ∀ x : Fin n → Bool, (D.wires (List.ofFn x)).getD t false = true →
      graphFun G ∅ x = true)
    (hj : j < D.gates.length) (hjk : j ≠ k)
    (x : Fin n → Bool) (hx : graphFun G ∅ x = false) :
    ((hoisted n D k u t).wires (List.ofFn x)).getD (n+sg k j) false =
      (D.wires (List.ofFn x)).getD (n+j) false := by
  have htfalse : (D.wires (List.ofFn x)).getD t false = false := by
    cases h : (D.wires (List.ofFn x)).getD t false
    · rfl
    · have hc := hclean x h
      rw [hx] at hc
      cases hc
  exact hoisted_negative_gate n D k u t j hR hkg hu ht ho hj hjk x htfalse (by rw [hfun, hx])

end PEqualNP.Outside.L_meta_3566.HoistNegative

namespace PEqualNP.Outside.L_meta_3566.HoistAndIndices

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_3566.HoistBase PEqualNP.Outside.L_meta_3566.HoistNegative
open PEqualNP.Outside.L_meta_3566.AndIndexTransport (andIndices)

lemma mem_andIndices (C : Circuit) (j : ℕ) :
    j ∈ andIndices C ↔ ∃ g, C.gates[j]? = some g ∧ g.op = .and := by
  classical
  simp only [AndIndexTransport.andIndices, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hj, hop⟩
    refine ⟨gateAt C j, ?_, hop⟩
    simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  · rintro ⟨g, hg, hop⟩
    refine ⟨(List.getElem?_eq_some_iff.mp hg).1, ?_⟩
    simpa [gateAt, List.getD_eq_getElem?_getD, hg] using hop

lemma indexShift_injOn (k : ℕ) (S : Finset ℕ) (hS : k ∉ S) :
    Set.InjOn (sg k) (S : Set ℕ) := by
  intro a ha b hb hab
  have ha' : a ≠ k := fun h => hS (h ▸ ha)
  have hb' : b ≠ k := fun h => hS (h ▸ hb)
  unfold sg at hab
  split_ifs at hab <;> omega

lemma changed_not_and (C : Circuit) (k : ℕ) (g : Gate)
    (hkg : C.gates[k]? = some g) (hor : g.op = .or) : k ∉ andIndices C := by
  intro hk
  obtain ⟨g', hg', hand⟩ := (mem_andIndices C k).mp hk
  rw [hkg] at hg'
  cases hg'
  rw [hor] at hand
  cases hand

lemma hoisted_and_injOn (C : Circuit) (k : ℕ) (g : Gate)
    (hkg : C.gates[k]? = some g) (hor : g.op = .or) :
    Set.InjOn (sg k) (andIndices C : Set ℕ) :=
  indexShift_injOn k (andIndices C) (changed_not_and C k g hkg hor)

lemma hoisted_and_forward (n : ℕ) (C : Circuit) (k u t : ℕ) (g : Gate)
    (hkg : C.gates[k]? = some g) (hor : g.op = .or)
    (j : ℕ) (hj : j ∈ andIndices C) : sg k j ∈ andIndices (hoisted n C k u t) := by
  have hjk : j ≠ k := by
    intro heq
    exact changed_not_and C k g hkg hor (heq ▸ hj)
  obtain ⟨g0, hg0, hand⟩ := (mem_andIndices C j).mp hj
  apply (mem_andIndices _ _).mpr
  exact ⟨rd (n + k) u g0, HoistNegative.hoisted_get n C k u t j g0 hjk hg0, hand⟩

lemma hoisted_and_inverse (n : ℕ) (C : Circuit) (k u t j : ℕ)
    (hj : j ∈ andIndices (hoisted n C k u t)) :
    ∃ i ∈ andIndices C, sg k i = j := by
  obtain ⟨g, hg, hand⟩ := (mem_andIndices _ j).mp hj
  obtain ⟨g0, hg0, hrd⟩ := del_get_inv n k u (lifted n C k u t) j g hg
  let i := if j < k then j else j + 1
  have hik : i ≠ k := by dsimp [i]; split_ifs <;> omega
  have hi : i < (lifted n C k u t).gates.length :=
    (List.getElem?_eq_some_iff.mp hg0).1
  have hlen : (lifted n C k u t).gates.length = C.gates.length + 1 := by
    simp [lifted]
  have hiold : i < C.gates.length := by
    by_contra hn
    have heq : i = C.gates.length := by omega
    have hlast := lifted_get_last n C k u t
    change (lifted n C k u t).gates[i]? = some g0 at hg0
    rw [heq, hlast] at hg0
    cases hg0
    simp [hrd, rd] at hand
  have hOld : C.gates[i]? = some g0 := by
    rw [← lifted_get_ne n C k u t i hik hiold]
    exact hg0
  refine ⟨i, (mem_andIndices C i).mpr ⟨g0, hOld, ?_⟩, ?_⟩
  · simpa [hrd, rd] using hand
  · dsimp [i, sg]
    split_ifs <;> omega

lemma hoisted_and_image (n : ℕ) (C : Circuit) (k u t : ℕ) (g : Gate)
    (hkg : C.gates[k]? = some g) (hor : g.op = .or) :
    andIndices (hoisted n C k u t) = (andIndices C).image (sg k) := by
  ext j
  constructor
  · intro hj
    obtain ⟨i, hi, heq⟩ := hoisted_and_inverse n C k u t j hj
    exact Finset.mem_image.mpr ⟨i, hi, heq⟩
  · intro hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact hoisted_and_forward n C k u t g hkg hor i hi

lemma hoisted_and_bijection (n : ℕ) (C : Circuit) (k u t : ℕ) (g : Gate)
    (hkg : C.gates[k]? = some g) (hor : g.op = .or)
    (j : ℕ) (hj : j ∈ andIndices (hoisted n C k u t)) :
    ∃! i, i ∈ andIndices C ∧ sg k i = j := by
  obtain ⟨i, hi, heq⟩ := hoisted_and_inverse n C k u t j hj
  refine ⟨i, ⟨hi, heq⟩, ?_⟩
  intro i' hi'
  exact indexShift_injOn k (andIndices C) (changed_not_and C k g hkg hor)
    hi'.1 hi (hi'.2.trans heq.symm)

lemma hoisted_and_card (n : ℕ) (C : Circuit) (k u t : ℕ) (g : Gate)
    (hkg : C.gates[k]? = some g) (hor : g.op = .or) :
    (andIndices (hoisted n C k u t)).card = (andIndices C).card := by
  rw [hoisted_and_image n C k u t g hkg hor]
  exact Finset.card_image_of_injOn
    (indexShift_injOn k (andIndices C) (changed_not_and C k g hkg hor))

end PEqualNP.Outside.L_meta_3566.HoistAndIndices

namespace PEqualNP.Outside.L_meta_3566.HoistDirty

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.Outside.L_meta_3566.HoistBase (sg)
open PEqualNP.Outside.L_meta_3566.HoistNegative (hoisted)
open PEqualNP.Outside.L_meta_3566.AndIndexTransport (andIndices pairLeakyAnds)

lemma negative_and_profile {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (k u t : ℕ)
    (hR : ReadsBack n C) (hkg : C.gates[k]? = some ⟨GateOp.or, [u,t]⟩)
    (ho : C.output < n + C.gates.length) (hfun : circuitFun n C = graphFun G ∅)
    (hclean : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD t false = true →
      graphFun G ∅ x = true) :
    ∀ j ∈ andIndices C, ∀ x, graphFun G ∅ x = false →
      gateVal n (hoisted n C k u t) (sg k j) x = gateVal n C j x := by
  have hreads := HoistBase.readsBack_get n C hR k ⟨GateOp.or, [u,t]⟩ hkg
  have hu : u < n + k := hreads u (by simp)
  have ht : t < n + k := hreads t (by simp)
  intro j hj x hx
  have hjlt := (AndIndexTransport.mem_andIndices.mp hj).1
  have hjk : j ≠ k := by
    intro h
    exact HoistAndIndices.changed_not_and C k _ hkg rfl (h ▸ hj)
  exact HoistNegative.clean_hoist_negative_gate G C k u t j hR hkg hu ht ho
    hfun hclean hjlt hjk x hx

lemma junk_image {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (k u t : ℕ)
    (hR : ReadsBack n C) (hkg : C.gates[k]? = some ⟨GateOp.or, [u,t]⟩)
    (ho : C.output < n + C.gates.length) (hfun : circuitFun n C = graphFun G ∅)
    (hclean : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD t false = true →
      graphFun G ∅ x = true) :
    junk G (hoisted n C k u t) = (junk G C).image (sg k) := by
  exact AndIndexTransport.junk_image G C (hoisted n C k u t) (sg k)
    (HoistAndIndices.hoisted_and_forward n C k u t _ hkg rfl)
    (HoistAndIndices.hoisted_and_inverse n C k u t)
    (negative_and_profile G C k u t hR hkg ho hfun hclean)

lemma junk_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (k u t : ℕ)
    (hR : ReadsBack n C) (hkg : C.gates[k]? = some ⟨GateOp.or, [u,t]⟩)
    (ho : C.output < n + C.gates.length) (hfun : circuitFun n C = graphFun G ∅)
    (hclean : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD t false = true →
      graphFun G ∅ x = true) :
    (junk G (hoisted n C k u t)).card = (junk G C).card := by
  exact AndIndexTransport.junk_card G C (hoisted n C k u t) (sg k)
    (HoistAndIndices.hoisted_and_forward n C k u t _ hkg rfl)
    (HoistAndIndices.hoisted_and_inverse n C k u t)
    (HoistAndIndices.hoisted_and_injOn C k _ hkg rfl)
    (negative_and_profile G C k u t hR hkg ho hfun hclean)

lemma graphFun_pair_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b : Fin n) (hab : ¬ G.Adj a b) : graphFun G ∅ (pairInput a b) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have hh : ∃ p q, G.Adj p q ∧ pairInput a b p = true ∧ pairInput a b q = true := by
    simpa [graphFun] using h
  obtain ⟨p, q, hpq, hp, hq⟩ := hh
  have hp' : p = a ∨ p = b := by simpa [pairInput] using hp
  have hq' : q = a ∨ q = b := by simpa [pairInput] using hq
  rcases hp' with rfl | rfl <;> rcases hq' with rfl | rfl
  · exact G.loopless.irrefl _ hpq
  · exact hab hpq
  · exact hab hpq.symm
  · exact G.loopless.irrefl _ hpq

lemma pair_negative_and_profile {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (k u t : ℕ)
    (hR : ReadsBack n C) (hkg : C.gates[k]? = some ⟨GateOp.or, [u,t]⟩)
    (ho : C.output < n + C.gates.length) (hfun : circuitFun n C = graphFun G ∅)
    (hclean : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD t false = true →
      graphFun G ∅ x = true) :
    ∀ j ∈ andIndices C, ∀ a b, ¬ G.Adj a b →
      gateVal n (hoisted n C k u t) (sg k j) (pairInput a b) =
        gateVal n C j (pairInput a b) := by
  intro j hj a b hab
  exact negative_and_profile G C k u t hR hkg ho hfun hclean j hj
    (pairInput a b) (graphFun_pair_false G a b hab)

lemma pairLeakyAnds_image {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (k u t : ℕ)
    (hR : ReadsBack n C) (hkg : C.gates[k]? = some ⟨GateOp.or, [u,t]⟩)
    (ho : C.output < n + C.gates.length) (hfun : circuitFun n C = graphFun G ∅)
    (hclean : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD t false = true →
      graphFun G ∅ x = true) :
    pairLeakyAnds G (hoisted n C k u t) = (pairLeakyAnds G C).image (sg k) := by
  exact AndIndexTransport.pairLeakyAnds_image G C (hoisted n C k u t) (sg k)
    (HoistAndIndices.hoisted_and_forward n C k u t _ hkg rfl)
    (HoistAndIndices.hoisted_and_inverse n C k u t)
    (pair_negative_and_profile G C k u t hR hkg ho hfun hclean)

lemma pairLeakyAnds_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (k u t : ℕ)
    (hR : ReadsBack n C) (hkg : C.gates[k]? = some ⟨GateOp.or, [u,t]⟩)
    (ho : C.output < n + C.gates.length) (hfun : circuitFun n C = graphFun G ∅)
    (hclean : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD t false = true →
      graphFun G ∅ x = true) :
    (pairLeakyAnds G (hoisted n C k u t)).card = (pairLeakyAnds G C).card := by
  exact AndIndexTransport.pairLeakyAnds_card G C (hoisted n C k u t) (sg k)
    (HoistAndIndices.hoisted_and_forward n C k u t _ hkg rfl)
    (HoistAndIndices.hoisted_and_inverse n C k u t)
    (HoistAndIndices.hoisted_and_injOn C k _ hkg rfl)
    (pair_negative_and_profile G C k u t hR hkg ho hfun hclean)

end PEqualNP.Outside.L_meta_3566.HoistDirty

namespace PEqualNP.Outside.L_meta_3566.HoistDirtyUnordered

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.Outside.L_meta_3566.HoistEval
open PEqualNP.Outside.L_meta_3566.HoistBase
open PEqualNP.Outside.L_meta_3566.HoistNegative (lifted hoisted)
open PEqualNP.Outside.L_meta_3566.AndIndexTransport (andIndices pairLeakyAnds)

lemma copy_or_wires_eq_of_false (n : ℕ) (C : Circuit) (k u t : ℕ) (g : Gate)
    (hkg : C.gates[k]? = some g) (hor : g.op = GateOp.or)
    (hinputs : g.inputs = [u,t] ∨ g.inputs = [t,u])
    (ht : t < n + k) (x : Fin n → Bool)
    (hfalse : (C.wires (List.ofFn x)).getD t false = false) :
    (C.gates.set k ⟨GateOp.or, [u]⟩).foldl step (List.ofFn x) =
      C.gates.foldl step (List.ofFn x) := by
  have hk := (List.getElem?_eq_some_iff.mp hkg).1
  have htP : ((C.gates.take k).foldl step (List.ofFn x)).getD t false = false := by
    rw [← HoistNegative.prefix_wire C.gates k hk (List.ofFn x) t (by simpa using ht)]
    exact hfalse
  apply HoistNegative.foldl_set_state C.gates k g _ hkg (List.ofFn x)
  rcases hinputs with hi | hi <;>
    simp only [hor, hi, GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
      List.any_nil, htP, id_eq, Bool.false_or, Bool.or_false]

lemma lifted_negative_wires (n : ℕ) (C : Circuit) (k u t : ℕ) (g : Gate)
    (hkg : C.gates[k]? = some g) (hor : g.op = GateOp.or)
    (hinputs : g.inputs = [u,t] ∨ g.inputs = [t,u]) (ht : t < n + k)
    (x : Fin n → Bool) (htfalse : (C.wires (List.ofFn x)).getD t false = false)
    (hofalse : circuitFun n C x = false) :
    (lifted n C k u t).wires (List.ofFn x) = C.wires (List.ofFn x) ++ [false] := by
  have hc := copy_or_wires_eq_of_false n C k u t g hkg hor hinputs ht x htfalse
  change (C.gates.set k _ ++ [_]).foldl step (List.ofFn x) = _
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil, hc]
  change step (C.wires (List.ofFn x)) _ = _
  change (C.wires (List.ofFn x)).getD C.output false = false at hofalse
  simp only [step, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
    htfalse, hofalse, id_eq, Bool.false_or]

lemma negative_and_profile {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (k u t : ℕ) (g : Gate)
    (hR : ReadsBack n C) (hkg : C.gates[k]? = some g) (hor : g.op = GateOp.or)
    (hinputs : g.inputs = [u,t] ∨ g.inputs = [t,u])
    (ho : C.output < n + C.gates.length) (hfun : circuitFun n C = graphFun G ∅)
    (hclean : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD t false = true →
      graphFun G ∅ x = true) :
    ∀ j ∈ andIndices C, ∀ x, graphFun G ∅ x = false →
      gateVal n (hoisted n C k u t) (sg k j) x = gateVal n C j x := by
  have hk := (List.getElem?_eq_some_iff.mp hkg).1
  have hreads := readsBack_get n C hR k g hkg
  have hu : u < n + k := hreads u (by rcases hinputs with hi | hi <;> simp [hi])
  have ht : t < n + k := hreads t (by rcases hinputs with hi | hi <;> simp [hi])
  intro j hj x hx
  have hjlt := (AndIndexTransport.mem_andIndices.mp hj).1
  have hjk : j ≠ k := by
    intro h
    exact HoistAndIndices.changed_not_and C k g hkg hor (h ▸ hj)
  have htfalse : (C.wires (List.ofFn x)).getD t false = false := by
    cases h : (C.wires (List.ofFn x)).getD t false
    · rfl
    · have hc := hclean x h
      rw [hx] at hc
      cases hc
  let E := lifted n C k u t
  have hER := HoistNegative.lifted_readsBack n C k u t hR hk hu ht ho
  have hEk := HoistNegative.lifted_get_copy n C k u t hk
  have hkE : k < E.gates.length := by simp [E, lifted]; omega
  have hcopy : ∀ y : Fin n → Bool,
      (E.wires (List.ofFn y)).getD (n+k) false = (E.wires (List.ofFn y)).getD u false := by
    intro y
    simpa using wires_copy E k u hEk (List.ofFn y) (by simpa using hu)
  have hw := del_wire n k u E hkE hu (readsBack_take n E hER k) hcopy x (n+j)
  have hl : (C.wires (List.ofFn x)).length = n + C.gates.length := by
    rw [wires_eq, foldl_step_length, List.length_ofFn]
  change ((hoisted n C k u t).wires (List.ofFn x)).getD _ false = _ at hw
  rw [lifted_negative_wires n C k u t g hkg hor hinputs ht x htfalse (by rw [hfun, hx]),
    List.getD_append _ _ _ _ (by omega), sig_gate n k u j hjk] at hw
  exact hw

lemma junk_image {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (k u t : ℕ) (g : Gate)
    (hR : ReadsBack n C) (hkg : C.gates[k]? = some g) (hor : g.op = GateOp.or)
    (hinputs : g.inputs = [u,t] ∨ g.inputs = [t,u])
    (ho : C.output < n + C.gates.length) (hfun : circuitFun n C = graphFun G ∅)
    (hclean : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD t false = true →
      graphFun G ∅ x = true) :
    junk G (hoisted n C k u t) = (junk G C).image (sg k) := by
  apply AndIndexTransport.junk_image G C (hoisted n C k u t) (sg k)
  · exact HoistAndIndices.hoisted_and_forward n C k u t g hkg hor
  · exact HoistAndIndices.hoisted_and_inverse n C k u t
  · exact negative_and_profile G C k u t g hR hkg hor hinputs ho hfun hclean

lemma junk_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (k u t : ℕ) (g : Gate)
    (hR : ReadsBack n C) (hkg : C.gates[k]? = some g) (hor : g.op = GateOp.or)
    (hinputs : g.inputs = [u,t] ∨ g.inputs = [t,u])
    (ho : C.output < n + C.gates.length) (hfun : circuitFun n C = graphFun G ∅)
    (hclean : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD t false = true →
      graphFun G ∅ x = true) :
    (junk G (hoisted n C k u t)).card = (junk G C).card := by
  apply AndIndexTransport.junk_card G C (hoisted n C k u t) (sg k)
  · exact HoistAndIndices.hoisted_and_forward n C k u t g hkg hor
  · exact HoistAndIndices.hoisted_and_inverse n C k u t
  · exact HoistAndIndices.hoisted_and_injOn C k g hkg hor
  · exact negative_and_profile G C k u t g hR hkg hor hinputs ho hfun hclean

lemma pairLeakyAnds_image {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (k u t : ℕ) (g : Gate)
    (hR : ReadsBack n C) (hkg : C.gates[k]? = some g) (hor : g.op = GateOp.or)
    (hinputs : g.inputs = [u,t] ∨ g.inputs = [t,u])
    (ho : C.output < n + C.gates.length) (hfun : circuitFun n C = graphFun G ∅)
    (hclean : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD t false = true →
      graphFun G ∅ x = true) :
    pairLeakyAnds G (hoisted n C k u t) = (pairLeakyAnds G C).image (sg k) := by
  apply AndIndexTransport.pairLeakyAnds_image G C (hoisted n C k u t) (sg k)
  · exact HoistAndIndices.hoisted_and_forward n C k u t g hkg hor
  · exact HoistAndIndices.hoisted_and_inverse n C k u t
  · intro j hj a b hab
    exact negative_and_profile G C k u t g hR hkg hor hinputs ho hfun hclean j hj
      (pairInput a b) (HoistDirty.graphFun_pair_false G a b hab)

lemma pairLeakyAnds_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (k u t : ℕ) (g : Gate)
    (hR : ReadsBack n C) (hkg : C.gates[k]? = some g) (hor : g.op = GateOp.or)
    (hinputs : g.inputs = [u,t] ∨ g.inputs = [t,u])
    (ho : C.output < n + C.gates.length) (hfun : circuitFun n C = graphFun G ∅)
    (hclean : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD t false = true →
      graphFun G ∅ x = true) :
    (pairLeakyAnds G (hoisted n C k u t)).card = (pairLeakyAnds G C).card := by
  apply AndIndexTransport.pairLeakyAnds_card G C (hoisted n C k u t) (sg k)
  · exact HoistAndIndices.hoisted_and_forward n C k u t g hkg hor
  · exact HoistAndIndices.hoisted_and_inverse n C k u t
  · exact HoistAndIndices.hoisted_and_injOn C k g hkg hor
  · intro j hj a b hab
    exact negative_and_profile G C k u t g hR hkg hor hinputs ho hfun hclean j hj
      (pairInput a b) (HoistDirty.graphFun_pair_false G a b hab)

end PEqualNP.Outside.L_meta_3566.HoistDirtyUnordered

/-
  A full-function bound for one mixed OR filter over k pure products.
  Correctness on all embedded inputs, including triples, is essential.
  This bounds matching size by k+1 for this expression shape only.
-/
namespace PEqualNP.Outside.L_meta_3566.FilteredRectangle

variable {m k : ℕ}

def hit (P Q : Fin k → Fin m → Prop) (S T : Fin m → Prop)
    (t : Fin k) (a : Fin m) : Prop := P t a ∧ Q t a ∧ (S a ∨ T a)

section

variable (R : Fin m → Fin m → Prop) (P Q : Fin k → Fin m → Prop)
  (S T : Fin m → Prop)
  (hcross : ∀ a b, a ≠ b → R a b → ¬ R b a)
  (hrect : ∀ t a b, P t a → Q t b → (S a ∨ T b) → R a b)
  (hleft : ∀ t a b c, P t a → Q t b → S c → ¬ R a b → R c b)
  (hright : ∀ t a b c, P t a → Q t b → T c → ¬ R a b → R a c)

include hcross hrect

lemma no_two_left (t : Fin k) (a b : Fin m)
    (ha : hit P Q S T t a) (hb : hit P Q S T t b) (hab : a ≠ b)
    (hSa : S a) (hSb : S b) : False := by
  exact hcross a b hab (hrect t a b ha.1 hb.2.1 (Or.inl hSa))
    (hrect t b a hb.1 ha.2.1 (Or.inl hSb))

lemma no_two_right (t : Fin k) (a b : Fin m)
    (ha : hit P Q S T t a) (hb : hit P Q S T t b) (hab : a ≠ b)
    (hTa : T a) (hTb : T b) : False := by
  exact hcross a b hab (hrect t a b ha.1 hb.2.1 (Or.inr hTb))
    (hrect t b a hb.1 ha.2.1 (Or.inr hTa))

lemma double_types (t : Fin k) (a b : Fin m)
    (ha : hit P Q S T t a) (hb : hit P Q S T t b) (hab : a ≠ b) :
    (S a ∧ ¬ T a ∧ ¬ S b ∧ T b) ∨ (S b ∧ ¬ T b ∧ ¬ S a ∧ T a) := by
  rcases ha.2.2 with hSa | hTa
  · have hSb : ¬ S b := no_two_left R P Q S T hcross hrect t a b ha hb hab hSa
    have hTb := hb.2.2.resolve_left hSb
    have hTa : ¬ T a := fun h => no_two_right R P Q S T hcross hrect t a b ha hb hab h hTb
    exact Or.inl ⟨hSa, hTa, hSb, hTb⟩
  · have hTb : ¬ T b := no_two_right R P Q S T hcross hrect t a b ha hb hab hTa
    have hSb := hb.2.2.resolve_right hTb
    have hSa : ¬ S a := fun h => no_two_left R P Q S T hcross hrect t a b ha hb hab h hSb
    exact Or.inr ⟨hSb, hTb, hSa, hTa⟩

include hleft hright

lemma oriented_double_unique (t t' : Fin k) (a b c d : Fin m)
    (ha : hit P Q S T t a) (hb : hit P Q S T t b) (hab : a ≠ b)
    (hSa : S a) (hTb : T b)
    (hc : hit P Q S T t' c) (hd : hit P Q S T t' d) (hcd : c ≠ d)
    (hSc : S c) (hTd : T d) : a = c ∧ b = d := by
  have hnba : ¬ R b a := hcross a b hab (hrect t a b ha.1 hb.2.1 (Or.inl hSa))
  have hndc : ¬ R d c := hcross c d hcd (hrect t' c d hc.1 hd.2.1 (Or.inl hSc))
  constructor
  · by_contra hac
    exact hcross a c hac
      (hleft t' d c a hd.1 hc.2.1 hSa hndc)
      (hleft t b a c hb.1 ha.2.1 hSc hnba)
  · by_contra hbd
    exact hcross b d hbd
      (hright t b a d hb.1 ha.2.1 hTd hnba)
      (hright t' d c b hd.1 hc.2.1 hTb hndc)

lemma double_same_pair (t t' : Fin k) (a b c d : Fin m)
    (ha : hit P Q S T t a) (hb : hit P Q S T t b) (hab : a ≠ b)
    (hc : hit P Q S T t' c) (hd : hit P Q S T t' d) (hcd : c ≠ d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  rcases double_types R P Q S T hcross hrect t a b ha hb hab with
    ⟨hSa, _, _, hTb⟩ | ⟨hSb, _, _, hTa⟩
  · rcases double_types R P Q S T hcross hrect t' c d hc hd hcd with
      ⟨hSc, _, _, hTd⟩ | ⟨hSd, _, _, hTc⟩
    · exact Or.inl (oriented_double_unique R P Q S T hcross hrect hleft hright
        t t' a b c d ha hb hab hSa hTb hc hd hcd hSc hTd)
    · exact Or.inr (oriented_double_unique R P Q S T hcross hrect hleft hright
        t t' a b d c ha hb hab hSa hTb hd hc hcd.symm hSd hTc)
  · rcases double_types R P Q S T hcross hrect t' c d hc hd hcd with
      ⟨hSc, _, _, hTd⟩ | ⟨hSd, _, _, hTc⟩
    · obtain ⟨hbc, had⟩ := oriented_double_unique R P Q S T hcross hrect hleft hright
        t t' b a c d hb ha hab.symm hSb hTa hc hd hcd hSc hTd
      exact Or.inr ⟨had, hbc⟩
    · obtain ⟨hbd, hac⟩ := oriented_double_unique R P Q S T hcross hrect hleft hright
        t t' b a d c hb ha hab.symm hSb hTa hd hc hcd.symm hSd hTc
      exact Or.inl ⟨hac, hbd⟩

theorem matching_bound (hcover : ∀ a, ∃ t, hit P Q S T t a) : m ≤ k + 1 := by
  classical
  let owner : Fin m → Fin k := fun a => Classical.choose (hcover a)
  have howner (a : Fin m) : hit P Q S T (owner a) a := Classical.choose_spec (hcover a)
  by_cases hinj : Function.Injective owner
  · have hcard := Fintype.card_le_of_injective owner hinj
    simp only [Fintype.card_fin] at hcard
    omega
  · have hcoll : ∃ a b, a ≠ b ∧ owner a = owner b := by
      by_contra hn
      apply hinj
      intro a b hab
      by_contra hne
      exact hn ⟨a, b, hne, hab⟩
    obtain ⟨a, b, hab, heq⟩ := hcoll
    let f : Fin m → Option (Fin k) := fun x => if x = a then none else some (owner x)
    have hf : Function.Injective f := by
      intro c d hcd
      by_cases hca : c = a
      · by_cases hda : d = a
        · exact hca.trans hda.symm
        · simp [f, hca, hda] at hcd
      · by_cases hda : d = a
        · simp [f, hca, hda] at hcd
        · have he : owner c = owner d := by simpa [f, hca, hda] using hcd
          by_contra hne
          have hb : hit P Q S T (owner a) b := by rw [heq]; exact howner b
          have hd : hit P Q S T (owner c) d := by rw [he]; exact howner d
          rcases double_same_pair R P Q S T hcross hrect hleft hright
            (owner a) (owner c) a b c d (howner a) hb hab (howner c) hd hne with hp | hp
          · exact hca hp.1.symm
          · exact hda hp.1.symm
    have hcard := Fintype.card_le_of_injective f hf
    simpa using hcard

end

end PEqualNP.Outside.L_meta_3566.FilteredRectangle

namespace PEqualNP.Outside.L_meta_3566.FilteredRectangleSemantics

variable {m k : ℕ}

def singleton (a : Fin m) : Fin m → Bool := fun i => decide (i = a)

theorem matching_bound (R : Fin m → Fin m → Prop)
    (A B : Fin k → (Fin m → Bool) → Bool)
    (U V : (Fin m → Bool) → Bool)
    (hdiag : ∀ a, R a a)
    (hcross : ∀ a b, a ≠ b → R a b → ¬ R b a)
    (hA : ∀ t x y, (∀ i, x i = true → y i = true) → A t x = true → A t y = true)
    (hB : ∀ t x y, (∀ i, x i = true → y i = true) → B t x = true → B t y = true)
    (hU : ∀ x y, (∀ i, x i = true → y i = true) → U x = true → U y = true)
    (hV : ∀ x y, (∀ i, x i = true → y i = true) → V x = true → V y = true)
    (hfull : ∀ x y,
      ((∃ t, A t x = true ∧ B t y = true) ∧ (U x = true ∨ V y = true)) ↔
        ∃ a b, R a b ∧ x a = true ∧ y b = true) : m ≤ k + 1 := by
  let P : Fin k → Fin m → Prop := fun t a => A t (singleton a) = true
  let Q : Fin k → Fin m → Prop := fun t a => B t (singleton a) = true
  let S : Fin m → Prop := fun a => U (singleton a) = true
  let T : Fin m → Prop := fun a => V (singleton a) = true
  apply FilteredRectangle.matching_bound R P Q S T hcross
  · intro t a b hp hq hs
    obtain ⟨i, j, hij, hi, hj⟩ := (hfull (singleton a) (singleton b)).mp
      ⟨⟨t, hp, hq⟩, hs⟩
    have hi' : i = a := by simpa [singleton] using hi
    have hj' : j = b := by simpa [singleton] using hj
    simpa [hi', hj'] using hij
  · intro t a b c hp hq hs hn
    let x : Fin m → Bool := fun i => decide (i = a ∨ i = c)
    have hax : ∀ i, singleton a i = true → x i = true := by
      intro i hi
      have hi' : i = a := by simpa [singleton] using hi
      simp [x, hi']
    have hcx : ∀ i, singleton c i = true → x i = true := by
      intro i hi
      have hi' : i = c := by simpa [singleton] using hi
      simp [x, hi']
    obtain ⟨i, j, hij, hi, hj⟩ := (hfull x (singleton b)).mp
      ⟨⟨t, hA t _ _ hax hp, hq⟩, Or.inl (hU _ _ hcx hs)⟩
    have hj' : j = b := by simpa [singleton] using hj
    have hi' : i = a ∨ i = c := by simpa [x] using hi
    rcases hi' with rfl | rfl
    · exact False.elim (hn (by simpa [hj'] using hij))
    · simpa [hj'] using hij
  · intro t a b c hp hq ht hn
    let y : Fin m → Bool := fun i => decide (i = b ∨ i = c)
    have hby : ∀ i, singleton b i = true → y i = true := by
      intro i hi
      have hi' : i = b := by simpa [singleton] using hi
      simp [y, hi']
    have hcy : ∀ i, singleton c i = true → y i = true := by
      intro i hi
      have hi' : i = c := by simpa [singleton] using hi
      simp [y, hi']
    obtain ⟨i, j, hij, hi, hj⟩ := (hfull (singleton a) y).mp
      ⟨⟨t, hp, hB t _ _ hby hq⟩, Or.inr (hV _ _ hcy ht)⟩
    have hi' : i = a := by simpa [singleton] using hi
    have hj' : j = b ∨ j = c := by simpa [y] using hj
    rcases hj' with rfl | rfl
    · exact False.elim (hn (by simpa [hi'] using hij))
    · simpa [hi'] using hij
  · intro a
    have hf := (hfull (singleton a) (singleton a)).mpr
      ⟨a, a, hdiag a, by simp [singleton], by simp [singleton]⟩
    obtain ⟨⟨t, ha, hb⟩, h⟩ := hf
    exact ⟨t, ha, hb, h⟩

end PEqualNP.Outside.L_meta_3566.FilteredRectangleSemantics

namespace PEqualNP.Outside.L_meta_3566.FilteredRectangleGraph

open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

variable {n m : ℕ}

lemma matching_cross (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hno4 : NoFourCycle G) (ell r : Fin m → Fin n)
    (hell : Function.Injective ell) (hr : Function.Injective r)
    (hdiag : ∀ a, G.Adj (ell a) (r a)) :
    ∀ a b, a ≠ b → G.Adj (ell a) (r b) → ¬ G.Adj (ell b) (r a) := by
  classical
  intro a b hab hab' hba'
  have habL : ell a ≠ ell b := fun h => hab (hell h)
  have habR : r a ≠ r b := fun h => hab (hr h)
  have hs : ({r a, r b} : Finset (Fin n)) ⊆
      Finset.univ.filter (fun w => G.Adj (ell a) w ∧ G.Adj (ell b) w) := by
    intro w hw
    have hw' : w = r a ∨ w = r b := by simpa only [Finset.mem_insert, Finset.mem_singleton] using hw
    rcases hw' with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdiag a, hba'⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab', hdiag b⟩
  have hc := (Finset.card_le_card hs).trans (hno4 (ell a) (ell b) habL)
  simp [habR] at hc

def supportInput (e : Fin m → Fin n) (x : Fin m → Bool) : Fin n → Bool :=
  fun v => decide (∃ a, e a = v ∧ x a = true)

def matchingInput (ell r : Fin m → Fin n) (x y : Fin m → Bool) : Fin n → Bool :=
  fun v => supportInput ell x v || supportInput r y v

lemma supportInput_true (e : Fin m → Fin n) (x : Fin m → Bool) (v : Fin n) :
    supportInput e x v = true ↔ ∃ a, e a = v ∧ x a = true := by
  simp [supportInput]

lemma matchingInput_true (ell r : Fin m → Fin n) (x y : Fin m → Bool) (v : Fin n) :
    matchingInput ell r x y v = true ↔
      (∃ a, ell a = v ∧ x a = true) ∨ (∃ b, r b = v ∧ y b = true) := by
  simp [matchingInput, supportInput]

lemma graphFun_matchingInput (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ell r : Fin m → Fin n)
    (hLL : ∀ a b, ¬ G.Adj (ell a) (ell b))
    (hRR : ∀ a b, ¬ G.Adj (r a) (r b)) (x y : Fin m → Bool) :
    graphFun G ∅ (matchingInput ell r x y) = true ↔
      ∃ a b, G.Adj (ell a) (r b) ∧ x a = true ∧ y b = true := by
  have hf : graphFun G ∅ (matchingInput ell r x y) = true ↔
      ∃ p q, G.Adj p q ∧ matchingInput ell r x y p = true ∧
        matchingInput ell r x y q = true := by simp [graphFun]
  rw [hf]
  constructor
  · rintro ⟨p, q, hpq, hp, hq⟩
    rcases (matchingInput_true ell r x y p).mp hp with ⟨a, rfl, ha⟩ | ⟨a, rfl, ha⟩
    · rcases (matchingInput_true ell r x y q).mp hq with ⟨b, rfl, hb⟩ | ⟨b, rfl, hb⟩
      · exact (hLL a b hpq).elim
      · exact ⟨a, b, hpq, ha, hb⟩
    · rcases (matchingInput_true ell r x y q).mp hq with ⟨b, rfl, hb⟩ | ⟨b, rfl, hb⟩
      · exact ⟨b, a, hpq.symm, hb, ha⟩
      · exact (hRR a b hpq).elim
  · rintro ⟨a, b, hab, ha, hb⟩
    exact ⟨ell a, r b, hab,
      (matchingInput_true ell r x y (ell a)).mpr (Or.inl ⟨a, rfl, ha⟩),
      (matchingInput_true ell r x y (r b)).mpr (Or.inr ⟨b, rfl, hb⟩)⟩

lemma graphFun_matchingInput_of_coloring (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ell r : Fin m → Fin n) (c : Fin n → Bool)
    (hcolor : ∀ u v, G.Adj u v → c u ≠ c v)
    (hL : ∀ a, c (ell a) = false) (hR : ∀ a, c (r a) = true)
    (x y : Fin m → Bool) :
    graphFun G ∅ (matchingInput ell r x y) = true ↔
      ∃ a b, G.Adj (ell a) (r b) ∧ x a = true ∧ y b = true := by
  apply graphFun_matchingInput G ell r
  · intro a b hab
    have h := hcolor (ell a) (ell b) hab
    rw [hL a, hL b] at h
    exact h rfl
  · intro a b hab
    have h := hcolor (r a) (r b) hab
    rw [hR a, hR b] at h
    exact h rfl

theorem matching_bound {k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hno4 : NoFourCycle G) (ell r : Fin m → Fin n)
    (hell : Function.Injective ell) (hr : Function.Injective r)
    (hdiag : ∀ a, G.Adj (ell a) (r a))
    (hLL : ∀ a b, ¬ G.Adj (ell a) (ell b))
    (hRR : ∀ a b, ¬ G.Adj (r a) (r b))
    (A B : Fin k → (Fin m → Bool) → Bool) (U V : (Fin m → Bool) → Bool)
    (hA : ∀ t x y, (∀ i, x i = true → y i = true) → A t x = true → A t y = true)
    (hB : ∀ t x y, (∀ i, x i = true → y i = true) → B t x = true → B t y = true)
    (hU : ∀ x y, (∀ i, x i = true → y i = true) → U x = true → U y = true)
    (hV : ∀ x y, (∀ i, x i = true → y i = true) → V x = true → V y = true)
    (hfull : ∀ x y,
      ((∃ t, A t x = true ∧ B t y = true) ∧ (U x = true ∨ V y = true)) ↔
        graphFun G ∅ (matchingInput ell r x y) = true) : m ≤ k + 1 := by
  apply FilteredRectangleSemantics.matching_bound (fun a b => G.Adj (ell a) (r b))
    A B U V hdiag (matching_cross G hno4 ell r hell hr hdiag) hA hB hU hV
  intro x y
  exact (hfull x y).trans (graphFun_matchingInput G ell r hLL hRR x y)

theorem matching_bound_of_coloring {k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hno4 : NoFourCycle G) (ell r : Fin m → Fin n)
    (hell : Function.Injective ell) (hr : Function.Injective r)
    (hdiag : ∀ a, G.Adj (ell a) (r a)) (c : Fin n → Bool)
    (hcolor : ∀ u v, G.Adj u v → c u ≠ c v)
    (hL : ∀ a, c (ell a) = false) (hR : ∀ a, c (r a) = true)
    (A B : Fin k → (Fin m → Bool) → Bool) (U V : (Fin m → Bool) → Bool)
    (hA : ∀ t x y, (∀ i, x i = true → y i = true) → A t x = true → A t y = true)
    (hB : ∀ t x y, (∀ i, x i = true → y i = true) → B t x = true → B t y = true)
    (hU : ∀ x y, (∀ i, x i = true → y i = true) → U x = true → U y = true)
    (hV : ∀ x y, (∀ i, x i = true → y i = true) → V x = true → V y = true)
    (hfull : ∀ x y,
      ((∃ t, A t x = true ∧ B t y = true) ∧ (U x = true ∨ V y = true)) ↔
        graphFun G ∅ (matchingInput ell r x y) = true) : m ≤ k + 1 := by
  apply FilteredRectangleSemantics.matching_bound (fun a b => G.Adj (ell a) (r b))
    A B U V hdiag (matching_cross G hno4 ell r hell hr hdiag) hA hB hU hV
  intro x y
  exact (hfull x y).trans (graphFun_matchingInput_of_coloring G ell r c hcolor hL hR x y)

end PEqualNP.Outside.L_meta_3566.FilteredRectangleGraph

/-
  The finite bipartite matching-cover argument follows L_meta_6510.
  Its proof is included here so this file imports only Defs and Mathlib.
  The global expression theorem retains explicit purity and full correctness.
-/
namespace PEqualNP.Outside.L_meta_3566.FilteredRectangleKonig

-- One side of a least cover is matched into the uncovered part of the other side (Hall).
theorem side {α β : Type} [DecidableEq α] [DecidableEq β] (E : Finset (α × β))
    (P : Finset α) (Q : Finset β)
    (hmin : ∀ (P' : Finset α) (Q' : Finset β), (∀ e ∈ E, e.1 ∈ P' ∨ e.2 ∈ Q') →
      P.card + Q.card ≤ P'.card + Q'.card)
    (hcov : ∀ e ∈ E, e.1 ∈ P ∨ e.2 ∈ Q) :
    ∃ f : {p // p ∈ P} → β, Function.Injective f ∧ ∀ p, (p.val, f p) ∈ E ∧ f p ∉ Q := by
  let t : {p // p ∈ P} → Finset β :=
    fun p => ((E.filter (fun e => e.1 = p.val)).image Prod.snd) \ Q
  have hall : ∀ S : Finset {p // p ∈ P}, S.card ≤ (S.biUnion t).card := by
    intro S
    have hsub : S.image Subtype.val ⊆ P := by
      intro x hx
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hx
      exact p.property
    have hc := hmin (P \ S.image Subtype.val) (Q ∪ S.biUnion t) (by
      intro e he
      rcases hcov e he with h | h
      · by_cases hS : e.1 ∈ S.image Subtype.val
        · right
          by_cases hq : e.2 ∈ Q
          · exact Finset.mem_union_left _ hq
          · apply Finset.mem_union_right
            obtain ⟨p, hp, hpe⟩ := Finset.mem_image.mp hS
            rw [Finset.mem_biUnion]
            refine ⟨p, hp, ?_⟩
            show e.2 ∈ ((E.filter (fun e => e.1 = p.val)).image Prod.snd) \ Q
            rw [Finset.mem_sdiff]
            exact ⟨Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hpe.symm⟩, rfl⟩, hq⟩
        · left
          exact Finset.mem_sdiff.mpr ⟨h, hS⟩
      · right
        exact Finset.mem_union_left _ h)
    have h1 : (P \ S.image Subtype.val).card + (S.image Subtype.val).card = P.card :=
      Finset.card_sdiff_add_card_eq_card hsub
    have h2 : (S.image Subtype.val).card = S.card :=
      Finset.card_image_of_injective S Subtype.val_injective
    have h3 := Finset.card_union_le Q (S.biUnion t)
    omega
  obtain ⟨f, hinj, hf⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hall
  refine ⟨f, hinj, fun p => ?_⟩
  have := hf p
  have h' : f p ∈ ((E.filter (fun e => e.1 = p.val)).image Prod.snd) \ Q := this
  rw [Finset.mem_sdiff] at h'
  obtain ⟨e, he, hef⟩ := Finset.mem_image.mp h'.1
  obtain ⟨heE, hep⟩ := Finset.mem_filter.mp he
  refine ⟨?_, h'.2⟩
  have : e = (p.val, f p) := Prod.ext hep hef
  rw [← this]
  exact heE

theorem konig {α β : Type} [DecidableEq α] [DecidableEq β] (E : Finset (α × β)) :
    ∃ (M : Finset (α × β)) (P : Finset α) (Q : Finset β), M ⊆ E ∧
      (∀ e ∈ M, ∀ e' ∈ M, e.1 = e'.1 → e = e') ∧ (∀ e ∈ M, ∀ e' ∈ M, e.2 = e'.2 → e = e') ∧
      (∀ e ∈ E, e.1 ∈ P ∨ e.2 ∈ Q) ∧ P.card + Q.card ≤ M.card := by
  classical
  have hex : ∃ k : ℕ, ∃ (P : Finset α) (Q : Finset β),
      (∀ e ∈ E, e.1 ∈ P ∨ e.2 ∈ Q) ∧ P.card + Q.card = k :=
    ⟨_, E.image Prod.fst, ∅, fun e he => Or.inl (Finset.mem_image_of_mem _ he), rfl⟩
  obtain ⟨P, Q, hcov, hk⟩ := Nat.find_spec hex
  have hmin : ∀ (P' : Finset α) (Q' : Finset β), (∀ e ∈ E, e.1 ∈ P' ∨ e.2 ∈ Q') →
      P.card + Q.card ≤ P'.card + Q'.card := by
    intro P' Q' h
    rw [hk]
    exact Nat.find_min' hex ⟨P', Q', h, rfl⟩
  obtain ⟨f, hfi, hf⟩ := side E P Q hmin hcov
  have hswap : ∀ (a : α) (b : β), (b, a) ∈ E.image Prod.swap ↔ (a, b) ∈ E := by
    intro a b
    constructor
    · intro h
      obtain ⟨e, he, hab⟩ := Finset.mem_image.mp h
      have : e = (a, b) := by
        rw [← Prod.swap_swap e, hab]; rfl
      rw [← this]; exact he
    · intro h
      exact Finset.mem_image.mpr ⟨(a, b), h, rfl⟩
  obtain ⟨g, hgi, hg⟩ := side (E.image Prod.swap) Q P (by
      intro Q' P' h
      have := hmin P' Q' (fun e he => by
        have := h (e.2, e.1) ((hswap e.1 e.2).mpr he)
        exact this.symm)
      omega) (by
      intro e he
      have h1 : (e.2, e.1) ∈ E := (hswap e.2 e.1).mp he
      exact (hcov _ h1).symm)
  have hg' : ∀ q : {q // q ∈ Q}, (g q, q.val) ∈ E ∧ g q ∉ P :=
    fun q => ⟨(hswap _ _).mp (hg q).1, (hg q).2⟩
  let M1 : Finset (α × β) := P.attach.image (fun p => (p.val, f p))
  let M2 : Finset (α × β) := Q.attach.image (fun q => (g q, q.val))
  have m1 : ∀ e ∈ M1, ∃ p : {p // p ∈ P}, e = (p.val, f p) := by
    intro e he
    obtain ⟨p, _, hp⟩ := Finset.mem_image.mp he
    exact ⟨p, hp.symm⟩
  have m2 : ∀ e ∈ M2, ∃ q : {q // q ∈ Q}, e = (g q, q.val) := by
    intro e he
    obtain ⟨q, _, hq⟩ := Finset.mem_image.mp he
    exact ⟨q, hq.symm⟩
  refine ⟨M1 ∪ M2, P, Q, ?_, ?_, ?_, hcov, ?_⟩
  · intro e he
    rcases Finset.mem_union.mp he with h | h
    · obtain ⟨p, rfl⟩ := m1 e h
      exact (hf p).1
    · obtain ⟨q, rfl⟩ := m2 e h
      exact (hg' q).1
  · intro e he e' he' h
    rcases Finset.mem_union.mp he with h1 | h1 <;> rcases Finset.mem_union.mp he' with h2 | h2
    · obtain ⟨p, rfl⟩ := m1 e h1
      obtain ⟨p', rfl⟩ := m1 e' h2
      have : p = p' := Subtype.ext h
      rw [this]
    · obtain ⟨p, rfl⟩ := m1 e h1
      obtain ⟨q, rfl⟩ := m2 e' h2
      exfalso
      apply (hg' q).2
      have h' : p.val = g q := h
      rw [← h']
      exact p.property
    · obtain ⟨q, rfl⟩ := m2 e h1
      obtain ⟨p, rfl⟩ := m1 e' h2
      exfalso
      apply (hg' q).2
      have h' : g q = p.val := h
      rw [h']
      exact p.property
    · obtain ⟨q, rfl⟩ := m2 e h1
      obtain ⟨q', rfl⟩ := m2 e' h2
      have : q = q' := hgi h
      rw [this]
  · intro e he e' he' h
    rcases Finset.mem_union.mp he with h1 | h1 <;> rcases Finset.mem_union.mp he' with h2 | h2
    · obtain ⟨p, rfl⟩ := m1 e h1
      obtain ⟨p', rfl⟩ := m1 e' h2
      have : p = p' := hfi h
      rw [this]
    · obtain ⟨p, rfl⟩ := m1 e h1
      obtain ⟨q, rfl⟩ := m2 e' h2
      exfalso
      apply (hf p).2
      have h' : f p = q.val := h
      rw [h']
      exact q.property
    · obtain ⟨q, rfl⟩ := m2 e h1
      obtain ⟨p, rfl⟩ := m1 e' h2
      exfalso
      apply (hf p).2
      have h' : q.val = f p := h
      rw [← h']
      exact q.property
    · obtain ⟨q, rfl⟩ := m2 e h1
      obtain ⟨q', rfl⟩ := m2 e' h2
      have : q = q' := Subtype.ext h
      rw [this]
  · have hd : Disjoint M1 M2 := by
      rw [Finset.disjoint_left]
      intro e h1 h2
      obtain ⟨p, rfl⟩ := m1 e h1
      obtain ⟨q, hq⟩ := m2 _ h2
      apply (hg' q).2
      have h' : p.val = g q := congrArg Prod.fst hq
      rw [← h']
      exact p.property
    have c1 : M1.card = P.card := by
      rw [Finset.card_image_of_injective _ (fun p p' h => Subtype.ext (congrArg Prod.fst h)),
        Finset.card_attach]
    have c2 : M2.card = Q.card := by
      rw [Finset.card_image_of_injective _ (fun q q' h => Subtype.ext (congrArg Prod.snd h)),
        Finset.card_attach]
    rw [Finset.card_union_of_disjoint hd, c1, c2]

theorem cover_of_matching_bound {n b : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : Fin n → Bool) (hcolor : ∀ u v, G.Adj u v → c u ≠ c v)
    (hbound : ∀ (m : ℕ) (ell r : Fin m → Fin n),
      Function.Injective ell → Function.Injective r →
      (∀ a, c (ell a) = false) → (∀ a, c (r a) = true) →
      (∀ a, G.Adj (ell a) (r a)) → m ≤ b) :
    ∃ T : Finset (Fin n), G.IsVertexCover (T : Set (Fin n)) ∧ T.card ≤ b := by
  classical
  let E : Finset (Fin n × Fin n) := Finset.univ.filter fun e =>
    G.Adj e.1 e.2 ∧ c e.1 = false ∧ c e.2 = true
  obtain ⟨M, P, Q, hME, hfst, hsnd, hcov, hcard⟩ := konig E
  let enum : Fin (Fintype.card {e // e ∈ M}) ≃ {e // e ∈ M} := (Fintype.equivFin _).symm
  let ell : Fin (Fintype.card {e // e ∈ M}) → Fin n := fun a => (enum a).val.1
  let r : Fin (Fintype.card {e // e ∈ M}) → Fin n := fun a => (enum a).val.2
  have hell : Function.Injective ell := by
    intro a a' haa'
    apply enum.injective
    apply Subtype.ext
    exact hfst _ (enum a).property _ (enum a').property haa'
  have hr : Function.Injective r := by
    intro a a' haa'
    apply enum.injective
    apply Subtype.ext
    exact hsnd _ (enum a).property _ (enum a').property haa'
  have hE (a : Fin (Fintype.card {e // e ∈ M})) :
      G.Adj (ell a) (r a) ∧ c (ell a) = false ∧ c (r a) = true := by
    exact (Finset.mem_filter.mp (hME (enum a).property)).2
  have hM : M.card ≤ b := by
    have h := hbound _ ell r hell hr (fun a => (hE a).2.1)
      (fun a => (hE a).2.2) (fun a => (hE a).1)
    simpa only [Fintype.card_coe] using h
  refine ⟨P ∪ Q, ?_, (Finset.card_union_le P Q).trans (hcard.trans hM)⟩
  intro u v huv
  change u ∈ P ∪ Q ∨ v ∈ P ∪ Q
  have hne := hcolor u v huv
  cases hu : c u <;> cases hv : c v
  · exact (hne (hu.trans hv.symm)).elim
  · have he : (u, v) ∈ E := Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv, hu, hv⟩
    rcases hcov (u, v) he with hp | hq
    · exact Or.inl (Finset.mem_union_left _ hp)
    · exact Or.inr (Finset.mem_union_right _ hq)
  · have he : (v, u) ∈ E := Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv.symm, hv, hu⟩
    rcases hcov (v, u) he with hp | hq
    · exact Or.inr (Finset.mem_union_left _ hp)
    · exact Or.inl (Finset.mem_union_right _ hq)
  · exact (hne (hu.trans hv.symm)).elim

end PEqualNP.Outside.L_meta_3566.FilteredRectangleKonig

namespace PEqualNP.Outside.L_meta_3566.FilteredRectangleGlobal

open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_3566.FilteredRectangleGraph

variable {n m k : ℕ}

def PureOn (c : Fin n → Bool) (side : Bool) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x y, (∀ v, c v = side → x v = y v) → f x = f y

lemma supportInput_mono (e : Fin m → Fin n) (x y : Fin m → Bool)
    (hxy : ∀ i, x i = true → y i = true) :
    ∀ v, supportInput e x v = true → supportInput e y v = true := by
  intro v hv
  obtain ⟨i, hi, hx⟩ := (supportInput_true e x v).mp hv
  exact (supportInput_true e y v).mpr ⟨i, hi, hxy i hx⟩

lemma left_on_matching (c : Fin n → Bool) (ell r : Fin m → Fin n)
    (hR : ∀ a, c (r a) = true) (f : (Fin n → Bool) → Bool)
    (hf : PureOn c false f) (x y : Fin m → Bool) :
    f (matchingInput ell r x y) = f (supportInput ell x) := by
  apply hf
  intro v hv
  have hr : supportInput r y v = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨i, hi, _⟩ := (supportInput_true r y v).mp h
    have hc := hR i
    rw [hi, hv] at hc
    cases hc
  simp [matchingInput, hr]

lemma right_on_matching (c : Fin n → Bool) (ell r : Fin m → Fin n)
    (hL : ∀ a, c (ell a) = false) (f : (Fin n → Bool) → Bool)
    (hf : PureOn c true f) (x y : Fin m → Bool) :
    f (matchingInput ell r x y) = f (supportInput r y) := by
  apply hf
  intro v hv
  have hl : supportInput ell x v = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨i, hi, _⟩ := (supportInput_true ell x v).mp h
    have hc := hL i
    rw [hi, hv] at hc
    cases hc
  simp [matchingInput, hl]

theorem matching_bound (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hno4 : NoFourCycle G) (c : Fin n → Bool)
    (hcolor : ∀ u v, G.Adj u v → c u ≠ c v)
    (A B : Fin k → (Fin n → Bool) → Bool) (U V : (Fin n → Bool) → Bool)
    (hA : ∀ t x y, (∀ i, x i = true → y i = true) → A t x = true → A t y = true)
    (hB : ∀ t x y, (∀ i, x i = true → y i = true) → B t x = true → B t y = true)
    (hU : ∀ x y, (∀ i, x i = true → y i = true) → U x = true → U y = true)
    (hV : ∀ x y, (∀ i, x i = true → y i = true) → V x = true → V y = true)
    (hpA : ∀ t, PureOn c false (A t)) (hpB : ∀ t, PureOn c true (B t))
    (hpU : PureOn c false U) (hpV : PureOn c true V)
    (hfull : ∀ z,
      ((∃ t, A t z = true ∧ B t z = true) ∧ (U z = true ∨ V z = true)) ↔
        graphFun G ∅ z = true)
    (ell r : Fin m → Fin n) (hell : Function.Injective ell) (hr : Function.Injective r)
    (hdiag : ∀ a, G.Adj (ell a) (r a))
    (hL : ∀ a, c (ell a) = false) (hR : ∀ a, c (r a) = true) : m ≤ k + 1 := by
  apply FilteredRectangleGraph.matching_bound_of_coloring G hno4 ell r hell hr hdiag c hcolor hL hR
    (fun t x => A t (supportInput ell x)) (fun t y => B t (supportInput r y))
    (fun x => U (supportInput ell x)) (fun y => V (supportInput r y))
  · intro t x y hxy
    exact hA t _ _ (supportInput_mono ell x y hxy)
  · intro t x y hxy
    exact hB t _ _ (supportInput_mono r x y hxy)
  · intro x y hxy
    exact hU _ _ (supportInput_mono ell x y hxy)
  · intro x y hxy
    exact hV _ _ (supportInput_mono r x y hxy)
  · intro x y
    have h := hfull (matchingInput ell r x y)
    simp only [left_on_matching c ell r hR _ (hpA _) x y,
      right_on_matching c ell r hL _ (hpB _) x y,
      left_on_matching c ell r hR U hpU x y,
      right_on_matching c ell r hL V hpV x y] at h
    exact h

theorem cover_bound (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hno4 : NoFourCycle G) (c : Fin n → Bool)
    (hcolor : ∀ u v, G.Adj u v → c u ≠ c v)
    (A B : Fin k → (Fin n → Bool) → Bool) (U V : (Fin n → Bool) → Bool)
    (hA : ∀ t x y, (∀ i, x i = true → y i = true) → A t x = true → A t y = true)
    (hB : ∀ t x y, (∀ i, x i = true → y i = true) → B t x = true → B t y = true)
    (hU : ∀ x y, (∀ i, x i = true → y i = true) → U x = true → U y = true)
    (hV : ∀ x y, (∀ i, x i = true → y i = true) → V x = true → V y = true)
    (hpA : ∀ t, PureOn c false (A t)) (hpB : ∀ t, PureOn c true (B t))
    (hpU : PureOn c false U) (hpV : PureOn c true V)
    (hfull : ∀ z,
      ((∃ t, A t z = true ∧ B t z = true) ∧ (U z = true ∨ V z = true)) ↔
        graphFun G ∅ z = true) :
    ∃ T : Finset (Fin n), G.IsVertexCover (T : Set (Fin n)) ∧ T.card ≤ k + 1 := by
  apply FilteredRectangleKonig.cover_of_matching_bound G c hcolor
  intro m ell r hell hr hL hR hdiag
  exact matching_bound G hno4 c hcolor A B U V hA hB hU hV hpA hpB hpU hpV
    hfull ell r hell hr hdiag hL hR

end PEqualNP.Outside.L_meta_3566.FilteredRectangleGlobal
