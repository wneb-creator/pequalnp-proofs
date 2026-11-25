import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5190

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership

-- An AND or OR gate is monotone in the wire values it reads.
theorem op_mono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (x y : List Bool)
    (h : ∀ i, x.getD i false = true → y.getD i false = true) :
    g.op.eval (g.inputs.map fun i => x.getD i false) = true →
      g.op.eval (g.inputs.map fun i => y.getD i false) = true := by
  rcases hop with ho | ho
  · rw [ho]
    simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro hx i hi
    exact h i (hx i hi)
  · rw [ho]
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, hx⟩
    exact ⟨i, hi, h i hx⟩

-- Running AND/OR gates preserves the pointwise order of the wire lists.
theorem run_mono (gs : List Gate) (hM : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (x y : List Bool), x.length = y.length →
      (∀ i, x.getD i false = true → y.getD i false = true) →
      ∀ i, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).getD i false
          = true →
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) y).getD i false
          = true := by
  induction gs with
  | nil =>
    intro x y _ h i hi
    exact h i hi
  | cons g gs ih =>
    intro x y hl h
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hM g' (List.mem_cons_of_mem _ hg'))
    · simp [hl]
    · intro i hi
      rcases Nat.lt_trichotomy i x.length with hlt | heq | hgt
      · rw [List.getD_append _ _ _ _ hlt] at hi
        rw [List.getD_append _ _ _ _ (hl ▸ hlt)]
        exact h i hi
      · rw [List.getD_append_right _ _ _ _ (le_of_eq heq.symm)] at hi
        rw [List.getD_append_right _ _ _ _ (le_of_eq (hl ▸ heq.symm))]
        have e1 : i - x.length = 0 := by omega
        have e2 : i - y.length = 0 := by omega
        rw [e1] at hi
        rw [e2]
        simp only [List.getD_cons_zero] at hi ⊢
        exact op_mono g (hM g (List.mem_cons_self)) x y h hi
      · exfalso
        rw [List.getD_append_right _ _ _ _ (le_of_lt hgt)] at hi
        have e1 : i - x.length = (i - x.length - 1) + 1 := by omega
        rw [e1] at hi
        simp at hi

-- A gate of an AND/OR circuit true at the one-vertex input a is true at every pair input a, v.
theorem gate_mono {n : ℕ} (C : Circuit) (hM : Monotone2 C) (j : ℕ) (a v : Fin n)
    (h : gateVal n C j (pairInput a a) = true) : gateVal n C j (pairInput a v) = true := by
  unfold gateVal at h ⊢
  unfold Circuit.wires at h ⊢
  refine run_mono C.gates (fun g hg => ?_) (List.ofFn (pairInput a a)) (List.ofFn (pairInput a v))
    (by simp) (fun i hi => ?_) (n + j) h
  · simpa using (hM g hg).1
  · by_cases hin : i < n
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hin, dite_true, Option.getD_some,
        pairInput, decide_eq_true_eq] at hi ⊢
      rcases hi with hi | hi
      · exact Or.inl hi
      · exact Or.inl hi
    · exfalso
      simp [List.getD_eq_getElem?_getD, hin] at hi

-- No triangle when every cycle has length at least five.
theorem no_tri {n : ℕ} (G : SimpleGraph (Fin n))
    (hg : ∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 5 ≤ w.length)
    {a u w : Fin n} (h1 : G.Adj a u) (h2 : G.Adj u w) (h3 : G.Adj w a) : False := by
  have hau := h1.ne
  have huw := h2.ne
  have hwa := h3.ne
  have hc : (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2
      (SimpleGraph.Walk.cons h3 SimpleGraph.Walk.nil))).IsCycle := by
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    constructor
    · simp [SimpleGraph.Walk.cons_isPath_iff, huw, hwa, hau.symm]
    · simp [hau, hau.symm, huw, hwa.symm]
  have h5 := hg a _ hc
  simp at h5

-- No four-cycle when every cycle has length at least five.
theorem no_sq {n : ℕ} (G : SimpleGraph (Fin n))
    (hg : ∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 5 ≤ w.length)
    {a u w u' : Fin n} (h1 : G.Adj a u) (h2 : G.Adj u w) (h3 : G.Adj w u') (h4 : G.Adj u' a)
    (huu : u ≠ u') (hwa : w ≠ a) : False := by
  have hau := h1.ne
  have huw := h2.ne
  have hwu := h3.ne
  have hua := h4.ne
  have hc : (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2
      (SimpleGraph.Walk.cons h3 (SimpleGraph.Walk.cons h4 SimpleGraph.Walk.nil)))).IsCycle := by
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    constructor
    · simp [SimpleGraph.Walk.cons_isPath_iff, huw, hwu, hua, huu, hwa, hau.symm]
    · simp [hau, hau.symm, huw, hua.symm, huu, hwa.symm]
  have h5 := hg a _ hc
  simp at h5

-- The core: around a vertex c whose one-vertex input turns the gate on, the non-neighbours of c give
-- enough false pairs, pairwise disjoint outside any set R holding c.
theorem core (k n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hk : 2 * k + 1 ≤ n) (hdeg : ∀ v : Fin n, G.degree v = 0 ∨ 3 ≤ G.degree v)
    (hg : ∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 5 ≤ w.length)
    (C : Circuit) (hM : Monotone2 C) (j : ℕ) (c : Fin n)
    (hc : gateVal n C j (pairInput c c) = true) (R : Finset (Fin n)) (hR : c ∈ R) :
    ∃ S : Finset (Fin n × Fin n), S.card = k ∧
      (∀ p ∈ S, gateVal n C j (pairInput p.1 p.2) = true ∧ ¬ G.Adj p.1 p.2) ∧
      ∀ p ∈ S, ∀ q ∈ S, p ≠ q →
        Disjoint (({p.1, p.2} : Finset (Fin n)) \ R) (({q.1, q.2} : Finset (Fin n)) \ R) := by
  classical
  have : Nonempty (Fin n) := ⟨c⟩
  have hex : ∀ u, G.Adj c u → ∃ w, G.Adj u w ∧ w ≠ c := by
    intro u hu
    have hmem : c ∈ G.neighborFinset u := by simp [hu.symm]
    have hpos : 0 < (G.neighborFinset u).card := Finset.card_pos.mpr ⟨c, hmem⟩
    rw [SimpleGraph.card_neighborFinset_eq_degree] at hpos
    have h3 : 3 ≤ G.degree u := by
      rcases hdeg u with h0 | h3
      · omega
      · exact h3
    have h1 : 1 < (G.neighborFinset u).card := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]; omega
    obtain ⟨w, hw, hne⟩ := Finset.exists_mem_ne h1 c
    exact ⟨w, by simpa using hw, hne⟩
  choose! f hf using hex
  let T : Finset (Fin n) := Finset.univ \ insert c (G.neighborFinset c)
  have hT : ∀ v, v ∈ T ↔ v ≠ c ∧ ¬ G.Adj c v := by
    intro v
    simp [T]
  have hmaps : ∀ u ∈ G.neighborFinset c, f u ∈ T := by
    intro u hu
    have hu' : G.Adj c u := by simpa using hu
    obtain ⟨h1, h2⟩ := hf u hu'
    rw [hT]
    exact ⟨h2, fun h3 => no_tri G hg hu' h1 h3.symm⟩
  have hinj : Set.InjOn f (G.neighborFinset c : Set (Fin n)) := by
    intro u hu u' hu' he
    by_contra hne
    have hu1 : G.Adj c u := by simpa using hu
    have hu2 : G.Adj c u' := by simpa using hu'
    obtain ⟨h1, h2⟩ := hf u hu1
    obtain ⟨h1', _⟩ := hf u' hu2
    rw [← he] at h1'
    exact no_sq G hg hu1 h1 h1'.symm hu2.symm hne h2
  have hcard1 : (G.neighborFinset c).card ≤ T.card :=
    Finset.card_le_card_of_injOn f hmaps hinj
  have hcard2 : T.card + ((G.neighborFinset c).card + 1) = n := by
    have h := Finset.card_sdiff_add_card_eq_card
      (Finset.subset_univ (insert c (G.neighborFinset c)))
    rw [Finset.card_insert_of_notMem (by simp), Finset.card_univ, Fintype.card_fin] at h
    exact h
  have hkT : k ≤ T.card := by omega
  obtain ⟨S', hS'sub, hS'card⟩ := Finset.exists_subset_card_eq hkT
  refine ⟨S'.image (fun v => (c, v)), ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ (Prod.mk_right_injective c)]
    exact hS'card
  · intro p hp
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
    have hvT := (hT v).mp (hS'sub hv)
    exact ⟨gate_mono C hM j c v hc, hvT.2⟩
  · intro p hp q hq hpq
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨v', hv', rfl⟩ := Finset.mem_image.mp hq
    have hvv : v ≠ v' := fun e => hpq (by rw [e])
    rw [Finset.disjoint_left]
    intro z hz hz'
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hz hz'
    rcases hz.1 with rfl | rfl
    · exact hz.2 hR
    · rcases hz'.1 with rfl | rfl
      · exact hz.2 hR
      · exact hvv rfl

end PEqualNP.Outside.L_meta_5190

theorem PEqualNP.Outside.L_meta_5190 : ∀ (x1 x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj],   (2 : ℕ) * x1 + (1 : ℕ) ≤ x2 →     (∀ (x6 : Fin x2), x3.degree x6 = (0 : ℕ) ∨ (3 : ℕ) ≤ x3.degree x6) →       (∀ (x7 : Fin x2) (x8 : x3.Walk x7 x7), x8.IsCycle → (5 : ℕ) ≤ x8.length) →         ∀ (x8 : PEqualNP.CircuitLowerBounds.Circuit),           PEqualNP.MetaComplexity.Monotone2 x8 →             ∀ (x10 x11 : Fin x2) (x12 : Fin x8.gates.length),               x3.Adj x10 x11 →                 have x14 : Fin x2 → Fin x2 → Prop := fun (x14 x15 : Fin x2) => PEqualNP.EdgeOwnership.gateVal x2 x8 (↑x12) (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true;                 have x15 : Fin x2 × Fin x2 → Finset (Fin x2) := fun (x15 : Fin x2 × Fin x2) => {x15.1, x15.2} \ {x10, x11};                 x14 x10 x10 ∨ x14 x11 x11 → ∃ (x17 : Finset (Fin x2 × Fin x2)), x17.card = x1 ∧ (∀ x18 ∈ x17, x14 x18.1 x18.2 ∧ ¬x3.Adj x18.1 x18.2) ∧ ∀ x18 ∈ x17, ∀ x20 ∈ x17, x18 ≠ x20 → Disjoint (x15 x18) (x15 x20) := by
  intro x1 x2 x3 _ h1 h2 h3 x8 hM x10 x11 x12 _
  dsimp only
  intro h
  rcases h with h | h
  · exact PEqualNP.Outside.L_meta_5190.core x1 x2 x3 h1 h2 h3 x8 hM x12 x10 h {x10, x11} (by simp)
  · exact PEqualNP.Outside.L_meta_5190.core x1 x2 x3 h1 h2 h3 x8 hM x12 x11 h {x10, x11} (by simp)
