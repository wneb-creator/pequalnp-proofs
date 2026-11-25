import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4970

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.TwoColour

lemma no_two_colour_of_zero (n : ℕ) (C : Circuit) (isLine : ℕ → Bool)
    (h : tCount n C isLine = 0) (g : ℕ) : ¬ IsTwoColour n C isLine g := by
  intro hg
  have hm : g ∈ twoColour n C isLine := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hg.1, hg⟩
  have hz : twoColour n C isLine = ∅ := Finset.card_eq_zero.mp h
  rw [hz] at hm
  exact Finset.notMem_empty _ hm

lemma or_reach_monochrome (p l : ℕ) (C : Circuit)
    (h : tCount (p + l) C (fun i => decide (p ≤ i)) = 0)
    (g : ℕ) (hg : g < C.gates.length) (hop : (gateAt C g).op = GateOp.or) :
    (∀ i ∈ orIn (p + l) C (p + l + g), (i : ℕ) < p) ∨
    (∀ i ∈ orIn (p + l) C (p + l + g), p ≤ (i : ℕ)) := by
  classical
  by_cases hp : ∃ i ∈ orIn (p + l) C (p + l + g), (i : ℕ) < p
  · left
    intro i hi
    by_contra hli
    obtain ⟨j, hj, hjp⟩ := hp
    apply no_two_colour_of_zero (p + l) C (fun i => decide (p ≤ i)) h g
    exact ⟨hg, hop, ⟨j, hj, by simp only [decide_eq_false_iff_not]; omega⟩,
      ⟨i, hi, by simp only [decide_eq_true_eq]; omega⟩⟩
  · right
    intro i hi
    by_contra hip
    exact hp ⟨i, hi, by omega⟩

open PEqualNP.MetaComplexity

lemma circuit_dependencies (k : ℕ) (C : Circuit) (ao : IsAO2 k C) : ∃ S : Finset (Fin k),
    S.card ≤ C.size + 1 ∧ ∀ x y : Fin k → Bool, (∀ v ∈ S, x v = y v) → circuitFun k C x = circuitFun k C y := by
  classical
  let step (u : List Bool) (g : Gate) := u ++ [g.op.eval (g.inputs.map fun i => u.getD i false)]
  have tailRead (w : List Bool) (b : Bool) (j : ℕ) (h : j ≠ w.length) :
      (w ++ [b]).getD j false = w.getD j false := by
    by_cases small : j < w.length
    · exact List.getD_append _ _ _ _ small
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
  have plan (gs : List Gate) (arity : ∀ g ∈ gs, g.inputs.length = 2) (l : ℕ) :
      ∃ P : Finset ℕ, P.card ≤ gs.length + 1 ∧ ∀ a b : List Bool,
        a.length=l → b.length=l → (∀ j ∈ P, a.getD j false = b.getD j false) →
        (gs.foldl step a).getD C.output false = (gs.foldl step b).getD C.output false := by
    induction gs generalizing l with
    | nil => exact ⟨{C.output},by simp,fun _ _ _ _ h => h _ (by simp)⟩
    | cons g gs ih =>
      obtain ⟨T,cost,agree⟩ := ih (fun v hv => arity v (List.mem_cons_of_mem _ hv)) (l+1)
      by_cases present : l ∈ T
      · let P := T.erase l ∪ g.inputs.toFinset
        refine ⟨P,?_,?_⟩
        · have h1 := Finset.card_union_le (T.erase l) g.inputs.toFinset
          have h2 := Finset.card_erase_add_one present
          have h3 := List.toFinset_card_le g.inputs
          have h4 := arity g List.mem_cons_self
          change (T.erase l ∪ g.inputs.toFinset).card ≤ gs.length+1+1
          omega
        · intro a b ha hb h
          apply agree (step a g) (step b g) (by simp [step,ha]) (by simp [step,hb])
          intro j hj
          by_cases hit : j=l
          · subst j
            have vals : g.inputs.map (fun i => a.getD i false) = g.inputs.map (fun i => b.getD i false) :=
              List.map_congr_left (fun i hi => h i (Finset.mem_union_right _ (List.mem_toFinset.mpr hi)))
            have last (u : List Bool) (hu : u.length=l) :
                (step u g).getD l false = g.op.eval (g.inputs.map fun i => u.getD i false) := by
              rw [← hu]; simp [step]
            rw [last a ha,last b hb,vals]
          · unfold step
            rw [tailRead _ _ _ (by omega),tailRead _ _ _ (by omega)]
            exact h j (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hit,hj⟩))
      · refine ⟨T,by simp only [List.length_cons]; omega,?_⟩
        intro a b ha hb h
        apply agree (step a g) (step b g) (by simp [step,ha]) (by simp [step,hb])
        intro j hj
        have ne : j ≠ l := fun eq => present (eq ▸ hj)
        unfold step
        rw [tailRead _ _ _ (by omega),tailRead _ _ _ (by omega),h j hj]
  obtain ⟨P,bound,agrees⟩ := plan C.gates ao.2.2 k
  let S := Finset.univ.filter (fun i : Fin k => i.val ∈ P)
  have cap : S.card ≤ P.card := by
    rw [← Finset.card_image_of_injective _ Fin.val_injective]
    apply Finset.card_le_card
    intro j hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
    exact (Finset.mem_filter.mp hi).2
  refine ⟨S,cap.trans bound,?_⟩
  intro x y h
  apply agrees (List.ofFn x) (List.ofFn y) (by simp) (by simp)
  intro j hj
  by_cases small : j<k
  · let i : Fin k := ⟨j,small⟩
    have atInput (a : Fin k → Bool) : (List.ofFn a).getD j false = a i := by
      rw [List.getD_eq_getElem _ _ (by simpa)]
      exact List.getElem_ofFn _
    rw [atInput,atInput]
    exact h i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩)
  · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp; omega)]

def edgeEnds {p l : ℕ} (e : Fin p × Fin l) : Finset (Fin (p + l)) :=
  {Fin.castAdd l e.1, Fin.natAdd p e.2}

def edgeEval {p l : ℕ} (E : Finset (Fin p × Fin l)) (x : Fin (p + l) → Bool) : Bool :=
  decide (∃ e ∈ E, x (Fin.castAdd l e.1) = true ∧ x (Fin.natAdd p e.2) = true)

lemma input_sides_ne {p l : ℕ} (a : Fin p) (b : Fin l) :
    Fin.castAdd l a ≠ Fin.natAdd p b := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
  have := a.isLt
  omega

lemma edgeEnds_card {p l : ℕ} (e : Fin p × Fin l) : (edgeEnds e).card = 2 := by
  simp [edgeEnds, input_sides_ne]

lemma edge_active {p l : ℕ} (E : Finset (Fin p × Fin l)) (e : Fin p × Fin l)
    (he : e ∈ E) (u : Fin (p + l)) (hu : u ∈ edgeEnds e) :
    ∃ x : Fin (p + l) → Bool, edgeEval E x ≠ edgeEval E (Function.update x u false) := by
  let x := fun v => decide (v ∈ edgeEnds e)
  refine ⟨x, ?_⟩
  have yes : edgeEval E x = true := by
    apply decide_eq_true
    exact ⟨e, he, by simp [x, edgeEnds]⟩
  rw [yes]
  intro bad
  obtain ⟨f, hf, L, R⟩ := of_decide_eq_true bad.symm
  have old (z : Fin (p + l)) (h : Function.update x u false z = true) :
      z ∈ edgeEnds e ∧ z ≠ u := by
    by_cases hz : z = u
    · subst z
      simp at h
    · simpa [x, Function.update_of_ne hz, hz] using h
  have hl := old _ L
  have hr := old _ R
  have sub : edgeEnds f ⊆ edgeEnds e := by
    intro i h
    rcases (show i = Fin.castAdd l f.1 ∨ i = Fin.natAdd p f.2 by
      simpa [edgeEnds] using h) with rfl | rfl
    · exact hl.1
    · exact hr.1
  have eq := Finset.eq_of_subset_of_card_le sub (by rw [edgeEnds_card, edgeEnds_card])
  have mem : u ∈ edgeEnds f := eq.symm ▸ hu
  rcases (show u = Fin.castAdd l f.1 ∨ u = Fin.natAdd p f.2 by
    simpa [edgeEnds] using mem) with h | h
  · exact hl.2 h.symm
  · exact hr.2 h.symm

lemma edge_inputs_bound {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit)
    (ao : IsAO2 (p + l) C)
    (computes : ∀ x, circuitFun (p + l) C x = edgeEval E x) :
    (E.biUnion edgeEnds).card ≤ C.size + 1 := by
  classical
  obtain ⟨S, cap, dep⟩ := circuit_dependencies (p + l) C ao
  have subset : E.biUnion edgeEnds ⊆ S := by
    intro u hu
    obtain ⟨e, he, mem⟩ := Finset.mem_biUnion.mp hu
    obtain ⟨x, hx⟩ := edge_active E e he u mem
    by_contra outside
    have same := dep x (Function.update x u false) (by
      intro z hz
      have ne : z ≠ u := fun e => outside (e ▸ hz)
      simp [Function.update_of_ne ne])
    exact hx ((computes x).symm.trans (same.trans (computes _)))
  exact (Finset.card_le_card subset).trans cap

lemma single_left_star_bound {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit)
    (ao : IsAO2 (p + l) C)
    (computes : ∀ x, circuitFun (p + l) C x = edgeEval E x)
    (a : Fin p) (star : ∀ e ∈ E, e.1 = a) :
    ∃ S : Finset (Fin (p + l)),
      (∀ e ∈ E, Fin.castAdd l e.1 ∈ S ∨ Fin.natAdd p e.2 ∈ S) ∧
      E.card + S.card ≤ C.size + 1 := by
  classical
  by_cases empty : E = ∅
  · refine ⟨∅, ?_, ?_⟩ <;> simp [empty]
  obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr empty
  have inj : Set.InjOn Prod.snd (E : Set (Fin p × Fin l)) := by
    intro e he f hf h
    apply Prod.ext
    · exact (star e he).trans (star f hf).symm
    · exact h
  have card : (E.image Prod.snd).card = E.card := Finset.card_image_of_injOn inj
  have ends : E.biUnion edgeEnds =
      insert (Fin.castAdd l a) ((E.image Prod.snd).image (Fin.natAdd p)) := by
    ext u
    constructor
    · intro hu
      obtain ⟨f, hf, hu⟩ := Finset.mem_biUnion.mp hu
      rcases (show u = Fin.castAdd l f.1 ∨ u = Fin.natAdd p f.2 by
        simpa [edgeEnds] using hu) with h | h
      · exact Finset.mem_insert.mpr (Or.inl (h.trans (congrArg (Fin.castAdd l) (star f hf))))
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr
          ⟨f.2, Finset.mem_image.mpr ⟨f, hf, rfl⟩, h.symm⟩))
    · intro hu
      rcases Finset.mem_insert.mp hu with h | h
      · subst u
        exact Finset.mem_biUnion.mpr ⟨e, he, by simp [edgeEnds, star e he]⟩
      · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp h
        obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hb
        exact Finset.mem_biUnion.mpr ⟨f, hf, by simp [edgeEnds]⟩
  have absent : Fin.castAdd l a ∉ (E.image Prod.snd).image (Fin.natAdd p) := by
    intro h
    obtain ⟨b, _, eq⟩ := Finset.mem_image.mp h
    exact input_sides_ne a b eq.symm
  have ends_card : (E.biUnion edgeEnds).card = E.card + 1 := by
    rw [ends, Finset.card_insert_of_notMem absent,
      Finset.card_image_of_injective _ (fun _ _ h => Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))), card]
  refine ⟨{Fin.castAdd l a}, ?_, ?_⟩
  · intro f hf
    left
    simp [star f hf]
  · have cap := edge_inputs_bound E C ao computes
    simpa only [ends_card, Finset.card_singleton] using cap

lemma single_right_star_bound {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit)
    (ao : IsAO2 (p + l) C)
    (computes : ∀ x, circuitFun (p + l) C x = edgeEval E x)
    (b : Fin l) (star : ∀ e ∈ E, e.2 = b) :
    ∃ S : Finset (Fin (p + l)),
      (∀ e ∈ E, Fin.castAdd l e.1 ∈ S ∨ Fin.natAdd p e.2 ∈ S) ∧
      E.card + S.card ≤ C.size + 1 := by
  classical
  by_cases empty : E = ∅
  · refine ⟨∅, ?_, ?_⟩ <;> simp [empty]
  obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr empty
  have inj : Set.InjOn Prod.fst (E : Set (Fin p × Fin l)) := by
    intro e he f hf h
    apply Prod.ext
    · exact h
    · exact (star e he).trans (star f hf).symm
  have card : (E.image Prod.fst).card = E.card := Finset.card_image_of_injOn inj
  have ends : E.biUnion edgeEnds =
      insert (Fin.natAdd p b) ((E.image Prod.fst).image (Fin.castAdd l)) := by
    ext u
    constructor
    · intro hu
      obtain ⟨f, hf, hu⟩ := Finset.mem_biUnion.mp hu
      rcases (show u = Fin.castAdd l f.1 ∨ u = Fin.natAdd p f.2 by
        simpa [edgeEnds] using hu) with h | h
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr
          ⟨f.1, Finset.mem_image.mpr ⟨f, hf, rfl⟩, h.symm⟩))
      · exact Finset.mem_insert.mpr (Or.inl (h.trans (congrArg (Fin.natAdd p) (star f hf))))
    · intro hu
      rcases Finset.mem_insert.mp hu with h | h
      · subst u
        exact Finset.mem_biUnion.mpr ⟨e, he, by simp [edgeEnds, star e he]⟩
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp h
        obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp ha
        exact Finset.mem_biUnion.mpr ⟨f, hf, by simp [edgeEnds]⟩
  have absent : Fin.natAdd p b ∉ (E.image Prod.fst).image (Fin.castAdd l) := by
    intro h
    obtain ⟨a, _, eq⟩ := Finset.mem_image.mp h
    exact input_sides_ne a b eq
  have ends_card : (E.biUnion edgeEnds).card = E.card + 1 := by
    rw [ends, Finset.card_insert_of_notMem absent,
      Finset.card_image_of_injective _ (fun _ _ h => Fin.castAdd_inj.mp h), card]
  refine ⟨{Fin.natAdd p b}, ?_, ?_⟩
  · intro f hf
    right
    simp [star f hf]
  · have cap := edge_inputs_bound E C ao computes
    simpa only [ends_card, Finset.card_singleton] using cap

lemma edgeEval_set_left_false {p l : ℕ} (E : Finset (Fin p × Fin l))
    (a : Fin p) (x : Fin (p + l) → Bool) :
    edgeEval E (Function.update x (Fin.castAdd l a) false) =
      edgeEval (E.filter fun e => e.1 ≠ a) x := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp only [edgeEval, decide_eq_true_eq]
  constructor
  · rintro ⟨e, he, hp, hl⟩
    have ne : e.1 ≠ a := by
      intro eq
      simp [eq] at hp
    refine ⟨e, Finset.mem_filter.mpr ⟨he, ne⟩, ?_, ?_⟩
    · simpa [Function.update_of_ne (fun h => ne (Fin.castAdd_inj.mp h))] using hp
    · simpa [Function.update_of_ne (input_sides_ne a e.2).symm] using hl
  · rintro ⟨e, he, hp, hl⟩
    obtain ⟨he, ne⟩ := Finset.mem_filter.mp he
    refine ⟨e, he, ?_, ?_⟩
    · simpa [Function.update_of_ne (fun h => ne (Fin.castAdd_inj.mp h))] using hp
    · simpa [Function.update_of_ne (input_sides_ne a e.2).symm] using hl

lemma forced_or_false_positive_neighbors {p l : ℕ} (E : Finset (Fin p × Fin l))
    (a : Fin p) (Q : Finset (Fin l)) (H : (Fin (p + l) → Bool) → Bool → Bool)
    (mono : Monotone fun x => H x true)
    (correct : ∀ x, H x (decide (∃ b ∈ Q, x (Fin.natAdd p b) = true)) =
      edgeEval (E.filter fun e => e.1 ≠ a) x)
    (x : Fin (p + l) → Bool)
    (falseOutput : edgeEval (E.filter fun e => e.1 ≠ a) x = false)
    (forced : H x true = true) :
    ∀ b ∈ Q, ∃ a' : Fin p, a' ≠ a ∧ (a', b) ∈ E ∧ x (Fin.castAdd l a') = true := by
  classical
  intro b hb
  let y := Function.update x (Fin.natAdd p b) true
  have le : x ≤ y := by
    intro i
    by_cases hi : i = Fin.natAdd p b
    · subst i
      simp [y]
    · simp [y, Function.update_of_ne hi]
  have hH : H y true = true := by
    have hle : H x true ≤ H y true := mono le
    rw [forced] at hle
    exact Bool.eq_true_of_true_le hle
  have hQ : decide (∃ b' ∈ Q, y (Fin.natAdd p b') = true) = true := by
    apply decide_eq_true
    exact ⟨b, hb, by simp [y]⟩
  have hy : edgeEval (E.filter fun e => e.1 ≠ a) y = true := by
    rw [← correct, hQ]
    exact hH
  obtain ⟨e, he, hp, hl⟩ := of_decide_eq_true hy
  obtain ⟨he, hne⟩ := Finset.mem_filter.mp he
  have hp' : x (Fin.castAdd l e.1) = true := by
    simpa [y, Function.update_of_ne (input_sides_ne e.1 b)] using hp
  have eq : e.2 = b := by
    by_contra hne'
    have different : Fin.natAdd p e.2 ≠ Fin.natAdd p b := by
      intro eq
      exact hne' (Fin.ext (Nat.add_left_cancel (congrArg Fin.val eq)))
    have hl' : x (Fin.natAdd p e.2) = true := by
      simpa [y, Function.update_of_ne different] using hl
    have yes : edgeEval (E.filter fun e => e.1 ≠ a) x = true := by
      apply decide_eq_true
      exact ⟨e, Finset.mem_filter.mpr ⟨he, hne⟩, hp', hl'⟩
    rw [falseOutput] at yes
    cases yes
  refine ⟨e.1, hne, ?_, hp'⟩
  have heq : (e.1, b) = e := Prod.ext rfl eq.symm
  rw [heq]
  exact he

namespace Forced

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run : List Gate → ℕ → Bool → List Bool → List Bool
  | [], _, _, w => w
  | _ :: gs, 0, t, w => gs.foldl step (w ++ [t])
  | g :: gs, j + 1, t, w => run gs j t (step w g)

lemma fold_preserve (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have next : i < (step w g).length := by
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [List.foldl_cons, ih (step w g) next]
    exact List.getD_append _ _ _ _ hi

lemma run_original (gs : List Gate) (j : ℕ) (t : Bool) (w : List Bool)
    (hj : j < gs.length)
    (ht : (gs.foldl step w).getD (w.length + j) false = t) :
    run gs j t w = gs.foldl step w := by
  induction gs generalizing j w with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero =>
      have actual : (gs.foldl step (step w g)).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        rw [fold_preserve gs (step w g) w.length (by simp [step])]
        simp [step]
      have same : g.op.eval (g.inputs.map fun i => w.getD i false) = t := by
        simpa only [List.foldl_cons, Nat.add_zero, actual] using ht
      simp only [run, List.foldl_cons]
      rw [← same]
      rfl
    | succ j =>
      simp only [run, List.foldl_cons]
      apply ih j (step w g) (by simpa using hj)
      have eq : (step w g).length + j = w.length + (j + 1) := by
        simp [step]
        omega
      simpa only [eq, List.foldl_cons] using ht

def value {n : ℕ} (C : Circuit) (j : ℕ) (x : Fin n → Bool) (t : Bool) : Bool :=
  (run C.gates j t (List.ofFn x)).getD C.output false

lemma value_original {n : ℕ} (C : Circuit) (j : ℕ) (x : Fin n → Bool)
    (hj : j < C.gates.length) :
    value C j x ((C.wires (List.ofFn x)).getD (n + j) false) =
      PEqualNP.MetaComplexity.circuitFun n C x := by
  unfold value
  rw [run_original C.gates j _ (List.ofFn x) hj (by simp only [List.length_ofFn]; rfl)]
  rfl

lemma gate_eval_monotone (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : ℕ → Bool) (hxy : ∀ i, x i = true → y i = true) :
    g.op.eval (g.inputs.map x) = true → g.op.eval (g.inputs.map y) = true := by
  rcases hg with hg | hg
  · rw [hg]
    simp only [GateOp.eval, List.all_map, Function.comp_def, id_eq, List.all_eq_true]
    intro h i hi
    exact hxy i (h i hi)
  · rw [hg]
    simp only [GateOp.eval, List.any_map, Function.comp_def, id_eq, List.any_eq_true]
    rintro ⟨i,hi,h⟩
    exact ⟨i,hi,hxy i h⟩

lemma step_getD (w : List Bool) (g : Gate) (i : ℕ) :
    (step w g).getD i false =
      if i = w.length then g.op.eval (g.inputs.map fun j => w.getD j false)
      else w.getD i false := by
  unfold step
  rcases lt_trichotomy i w.length with h | h | h
  · rw [ite_eq_right (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left h]
  · rw [ite_eq_left h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [h]
  · rw [ite_eq_right (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

lemma step_monotone (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (w v : List Bool) (hlen : w.length = v.length)
    (hle : ∀ i, w.getD i false = true → v.getD i false = true) :
    ∀ i, (step w g).getD i false = true → (step v g).getD i false = true := by
  intro i hi
  rw [step_getD] at hi ⊢
  rw [← hlen]
  split_ifs at hi ⊢ with h
  · exact gate_eval_monotone g hg _ _ hle hi
  · exact hle i hi

lemma fold_state_monotone (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w v : List Bool) (hlen : w.length = v.length)
    (hle : ∀ i, w.getD i false = true → v.getD i false = true) :
    ∀ i, (gs.foldl step w).getD i false = true → (gs.foldl step v).getD i false = true := by
  induction gs generalizing w v with
  | nil => exact hle
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih (fun k hk => hg k (List.mem_cons_of_mem _ hk))
    · simp [step,hlen]
    · exact step_monotone g (hg g List.mem_cons_self) w v hlen hle

lemma append_getD (w : List Bool) (t : Bool) (i : ℕ) :
    (w ++ [t]).getD i false = if i = w.length then t else w.getD i false := by
  cases t with
  | false => simpa [step, GateOp.eval] using step_getD w ⟨GateOp.or, []⟩ i
  | true => simpa [step, GateOp.eval] using step_getD w ⟨GateOp.and, []⟩ i

lemma run_state_monotone (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (j : ℕ) (t : Bool) (w v : List Bool) (hlen : w.length = v.length)
    (hle : ∀ i, w.getD i false = true → v.getD i false = true) :
    ∀ i, (run gs j t w).getD i false = true → (run gs j t v).getD i false = true := by
  induction gs generalizing j w v with
  | nil => exact hle
  | cons g gs ih =>
    have hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or :=
      fun k hk => hg k (List.mem_cons_of_mem _ hk)
    cases j with
    | zero =>
      simp only [run]
      apply fold_state_monotone gs hgs (w ++ [t]) (v ++ [t]) (by simp [hlen])
      intro i hi
      rw [append_getD] at hi ⊢
      rw [← hlen]
      split_ifs at hi ⊢ with h
      · exact hi
      · exact hle i hi
    | succ j =>
      simp only [run]
      apply ih hgs j (step w g) (step v g) (by simp [step, hlen])
      exact step_monotone g (hg g List.mem_cons_self) w v hlen hle

lemma value_monotone {n : ℕ} (C : Circuit)
    (hg : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or) (j : ℕ) (t : Bool) :
    Monotone fun x : Fin n → Bool => value C j x t := by
  intro x y hxy
  apply Bool.le_iff_imp.mpr
  apply run_state_monotone C.gates hg j t (List.ofFn x) (List.ofFn y) (by simp)
  intro i
  by_cases hi : i < n
  · simpa [List.getD_eq_getElem?_getD, hi] using Bool.le_iff_imp.mp (hxy ⟨i, hi⟩)
  · simp [List.getD_eq_getElem?_getD, hi]

lemma cofactor_value_correct {p l : ℕ} (E : Finset (Fin p × Fin l))
    (C : Circuit) (a : Fin p) (Q : Finset (Fin l)) (j : ℕ)
    (hj : j < C.gates.length)
    (computes : ∀ x, PEqualNP.MetaComplexity.circuitFun (p + l) C x = edgeEval E x)
    (star : ∀ x : Fin (p + l) → Bool,
      (C.wires (List.ofFn x)).getD (p + l + j) false =
        decide (∃ b ∈ Q, x (Fin.natAdd p b) = true)) :
    ∀ x : Fin (p + l) → Bool,
      value C j (Function.update x (Fin.castAdd l a) false)
          (decide (∃ b ∈ Q, x (Fin.natAdd p b) = true)) =
        edgeEval (E.filter fun e => e.1 ≠ a) x := by
  intro x
  have hQ : (C.wires (List.ofFn (Function.update x (Fin.castAdd l a) false))).getD
      (p + l + j) false = decide (∃ b ∈ Q, x (Fin.natAdd p b) = true) := by
    rw [star]
    congr 1
    apply propext
    constructor <;> rintro ⟨b, hb, hx⟩ <;> refine ⟨b, hb, ?_⟩ <;>
      simpa [Function.update_of_ne (input_sides_ne a b).symm] using hx
  rw [← hQ, value_original C j _ hj, computes, edgeEval_set_left_false]

lemma cofactor_value_monotone {p l : ℕ} (C : Circuit)
    (hg : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (a : Fin p) (j : ℕ) (t : Bool) :
    Monotone fun x : Fin (p + l) → Bool =>
      value C j (Function.update x (Fin.castAdd l a) false) t := by
  intro x y hxy
  apply value_monotone C hg j t
  intro i
  by_cases hi : i = Fin.castAdd l a
  · subst i
    simp
  · simpa [Function.update_of_ne hi] using hxy i

def trueCircuit (C : Circuit) (j : ℕ) : Circuit :=
  ⟨C.gates.set j ⟨GateOp.and, []⟩, C.output⟩

lemma run_true_set (gs : List Gate) (j : ℕ) (w : List Bool) :
    run gs j true w = (gs.set j ⟨GateOp.and, []⟩).foldl step w := by
  induction gs generalizing j w with
  | nil => cases j <;> rfl
  | cons g gs ih =>
    cases j with
    | zero => rfl
    | succ j => exact ih j (step w g)

lemma trueCircuit_value {n : ℕ} (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    circuitFun n (trueCircuit C j) x = value C j x true := by
  unfold value
  rw [run_true_set]
  rfl

lemma set_preserves_predicate (P : Gate → Prop) (gs : List Gate)
    (hg : ∀ g ∈ gs, P g) (v : Gate) (hv : P v) (j : ℕ) :
    ∀ g ∈ gs.set j v, P g := by
  induction gs generalizing j with
  | nil => cases j <;> simp
  | cons g gs ih =>
    have tail : ∀ h ∈ gs, P h := fun h hh => hg h (List.mem_cons_of_mem _ hh)
    cases j with
    | zero =>
      intro h hh
      rcases List.mem_cons.mp hh with eq | mem
      · simpa [eq] using hv
      · exact tail h mem
    | succ j =>
      intro h hh
      rcases List.mem_cons.mp hh with eq | mem
      · simpa [eq] using hg g List.mem_cons_self
      · exact ih tail j h mem

lemma trueCircuit_andOrOnly (C : Circuit) (j : ℕ)
    (hg : PEqualNP.EdgeOwnership.AndOrOnly C) :
    PEqualNP.EdgeOwnership.AndOrOnly (trueCircuit C j) := by
  apply set_preserves_predicate _ C.gates hg ⟨GateOp.and, []⟩ (Or.inl rfl) j

lemma trueCircuit_fanin (C : Circuit) (j : ℕ)
    (hg : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    ∀ g ∈ (trueCircuit C j).gates, g.inputs.length ≤ 2 := by
  apply set_preserves_predicate _ C.gates hg ⟨GateOp.and, []⟩ (by simp) j

lemma gateAt_eq (C : Circuit) (i : ℕ) (hi : i < C.gates.length) :
    gateAt C i = C.gates[i] := List.getD_eq_getElem _ _ hi

lemma trueCircuit_gateAt (C : Circuit) (j i : ℕ) (hi : i < C.gates.length) :
    gateAt (trueCircuit C j) i = if i = j then ⟨GateOp.and, []⟩ else gateAt C i := by
  have hi' : i < (trueCircuit C j).gates.length := by simpa [trueCircuit] using hi
  rw [gateAt_eq (trueCircuit C j) i hi', gateAt_eq C i hi]
  by_cases h : i = j
  · subst i
    simp [trueCircuit]
  · simp [trueCircuit, h, Ne.symm h]

lemma trueCircuit_readsBack (n : ℕ) (C : Circuit) (j : ℕ) (hb : ReadsBack n C) :
    ReadsBack n (trueCircuit C j) := by
  intro i hi w hw
  have hi' : i < C.gates.length := by simpa [trueCircuit] using hi
  rw [trueCircuit_gateAt C j i hi'] at hw
  split_ifs at hw with eq
  · simp at hw
  · exact hb i hi' w hw

lemma countP_set_false_le (f : Gate → Bool) (gs : List Gate) (v : Gate)
    (hf : f v = false) (j : ℕ) :
    (gs.set j v).countP f ≤ gs.countP f := by
  induction gs generalizing j with
  | nil => cases j <;> simp
  | cons g gs ih =>
    cases j with
    | zero => simp [List.set, List.countP_cons, hf]
    | succ j =>
      simpa only [List.set_cons_succ, List.countP_cons] using
        Nat.add_le_add_right (ih j) (if f g then 1 else 0)

end Forced



namespace Protected

def respects (n : ℕ) (C : Circuit) (j : ℕ) (W : ℕ → Bool) : Prop :=
  ∀ k, k < C.gates.length → k ≠ j →
    W (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map W)

lemma gate_frontier (g : Gate) (W : ℕ → Bool)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hl : g.inputs.length ≤ 2) (hv : g.op.eval (g.inputs.map W) = true) :
    ∃ J : Finset ℕ,
      J ⊆ g.inputs.toFinset ∧
      J.card ≤ (if AndBudget.branching_and g then 1 else 0) + 1 ∧
      (∀ i ∈ J, W i = true) ∧
      ∀ V : ℕ → Bool, (∀ i ∈ J, V i = true) → g.op.eval (g.inputs.map V) = true := by
  rcases hop with ha | ho
  · refine ⟨g.inputs.toFinset, Finset.Subset.refl _, ?_, ?_, ?_⟩
    · by_cases htwo : 2 ≤ g.inputs.length
      · simpa [AndBudget.branching_and, ha, htwo] using (List.toFinset_card_le _).trans hl
      · have hsmall : g.inputs.length ≤ 1 := by omega
        simpa [AndBudget.branching_and, ha, htwo] using (List.toFinset_card_le _).trans hsmall
    · rw [ha] at hv
      simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq] at hv
      intro i hi
      exact hv i (List.mem_toFinset.mp hi)
    · intro V hy
      rw [ha]
      simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
      intro i hi
      exact hy i (List.mem_toFinset.mpr hi)
  · rw [ho] at hv
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hv
    obtain ⟨i, hi, hv⟩ := hv
    refine ⟨{i}, by simpa using List.mem_toFinset.mpr hi,
      by simp [AndBudget.branching_and, ho], ?_, ?_⟩
    · intro a ha
      simpa only [Finset.mem_singleton.mp ha] using hv
    · intro V hy
      rw [ho]
      simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
      exact ⟨i, hi, hy i (by simp)⟩

lemma frontier_certificate (n : ℕ) (C : Circuit) (j : ℕ)
    (hAO : PEqualNP.EdgeOwnership.AndOrOnly C) (hback : ReadsBack n C)
    (hfanin : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (W : ℕ → Bool) (hW : respects n C j W) :
    ∀ k, k ≤ C.gates.length → ∀ R : Finset ℕ,
      (∀ w ∈ R, w < n + k ∨ w = n + j) → (∀ w ∈ R, W w = true) →
      ∃ T : Finset ℕ,
        (∀ w ∈ T, w < n ∨ w = n + j) ∧ (∀ w ∈ T, W w = true) ∧
        (∀ V : ℕ → Bool, respects n C j V → (∀ w ∈ T, V w = true) →
          ∀ w ∈ R, V w = true) ∧
        T.card ≤ AndBudget.and_count C k + R.card := by
  intro k
  induction k with
  | zero =>
    intro _ R hR ht
    exact ⟨R, by simpa using hR, ht, by aesop, by simp [AndBudget.and_count]⟩
  | succ k ih =>
    intro hk R hR ht
    have hkl : k < C.gates.length := by omega
    have hcount := AndBudget.and_count_succ C k hkl
    by_cases hj : k = j
    · have hR0 : ∀ w ∈ R, w < n + k ∨ w = n + j := by
        intro w hw
        rcases hR w hw with hb | eq
        · by_cases heq : w = n + j
          · exact Or.inr heq
          · left
            omega
        · exact Or.inr eq
      obtain ⟨T, hTb, hTt, hTf, hTc⟩ := ih (by omega) R hR0 ht
      exact ⟨T, hTb, hTt, hTf, by omega⟩
    · by_cases hm : n + k ∈ R
      · have hgmem := AndBudget.output_gateAt_mem hkl
        have hv := ht (n + k) hm
        rw [hW k hkl hj] at hv
        obtain ⟨J, hJsub, hJc, hJt, hJforce⟩ := gate_frontier (gateAt C k) W
          (hAO _ hgmem) (hfanin _ hgmem) hv
        let R' := J ∪ R.erase (n + k)
        have hR'b : ∀ w ∈ R', w < n + k ∨ w = n + j := by
          intro w hw
          rcases Finset.mem_union.mp hw with h | h
          · exact Or.inl (hback k hkl w (List.mem_toFinset.mp (hJsub h)))
          · have hwR := Finset.mem_of_mem_erase h
            have hne := Finset.ne_of_mem_erase h
            rcases hR w hwR with hb | eq
            · exact Or.inl (by omega)
            · exact Or.inr eq
        have hR't : ∀ w ∈ R', W w = true := by
          intro w hw
          rcases Finset.mem_union.mp hw with h | h
          · exact hJt w h
          · exact ht w (Finset.mem_of_mem_erase h)
        obtain ⟨T, hTb, hTt, hTf, hTc⟩ := ih (by omega) R' hR'b hR't
        refine ⟨T, hTb, hTt, ?_, ?_⟩
        · intro V hV ht w hw
          by_cases hwm : w = n + k
          · subst w
            rw [hV k hkl hj]
            apply hJforce V
            intro i hi
            exact hTf V hV ht i (Finset.mem_union.mpr (Or.inl hi))
          · exact hTf V hV ht w (Finset.mem_union.mpr
              (Or.inr (Finset.mem_erase.mpr ⟨hwm, hw⟩)))
        · have hR'c : R'.card ≤ J.card + (R.erase (n + k)).card := Finset.card_union_le _ _
          have hRc := Finset.card_erase_add_one hm
          omega
      · have hR0 : ∀ w ∈ R, w < n + k ∨ w = n + j := by
          intro w hw
          rcases hR w hw with hb | eq
          · left
            have hne : w ≠ n + k := by intro h; exact hm (h ▸ hw)
            omega
          · exact Or.inr eq
        obtain ⟨T, hTb, hTt, hTf, hTc⟩ := ih (by omega) R hR0 ht
        exact ⟨T, hTb, hTt, hTf, by omega⟩

lemma boundary_respects (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool)
    (hb : ReadsBack n C) : respects n C j (AndBudget.boundary_W n C x) := by
  intro k hk _
  rw [AndBudget.boundary_W_gate n C x k hk]
  congr 1
  apply List.map_congr_left
  intro w hw
  simp [hb k hk w hw]


lemma true_boundary_respects (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool)
    (hb : ReadsBack n C) :
    respects n C j (AndBudget.boundary_W n (Forced.trueCircuit C j) x) := by
  intro k hk hkj
  have hk' : k < (Forced.trueCircuit C j).gates.length := by simpa [Forced.trueCircuit] using hk
  have h := boundary_respects n (Forced.trueCircuit C j) j x
    (Forced.trueCircuit_readsBack n C j hb) k hk' hkj
  simpa [Forced.trueCircuit_gateAt C j k hk, hkj] using h

lemma true_boundary_protected (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool)
    (hj : j < C.gates.length) :
    AndBudget.boundary_W n (Forced.trueCircuit C j) x (n + j) = true := by
  have hj' : j < (Forced.trueCircuit C j).gates.length := by simpa [Forced.trueCircuit] using hj
  rw [AndBudget.boundary_W_gate n (Forced.trueCircuit C j) x j hj',
    Forced.trueCircuit_gateAt C j j hj]
  simp [GateOp.eval]

lemma forced_input_certificate (n : ℕ) (C : Circuit) (j : ℕ)
    (hAO : PEqualNP.EdgeOwnership.AndOrOnly C) (hback : ReadsBack n C)
    (hfanin : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (hj : j < C.gates.length)
    (x : Fin n → Bool)
    (hx : circuitFun n (Forced.trueCircuit C j) x = true)
    (hfalse : circuitFun n C x = false) :
    ∃ S : Finset (Fin n), (∀ i ∈ S, x i = true) ∧
      (∀ y : Fin n → Bool, (∀ i ∈ S, y i = true) →
        circuitFun n (Forced.trueCircuit C j) y = true) ∧
      S.card ≤ C.gates.countP AndBudget.branching_and := by
  classical
  let W := AndBudget.boundary_W n (Forced.trueCircuit C j) x
  have hval : W C.output = true := hx
  have hout : C.output < n + C.gates.length := by
    by_contra h
    have hz : W C.output = false := by
      apply AndBudget.boundary_getD_ge_length
      rw [AndBudget.boundary_wires_length]
      simp only [Forced.trueCircuit, List.length_set]
      omega
    rw [hz] at hval
    contradiction
  obtain ⟨T, hTb, hTt, hTf, hTc⟩ := frontier_certificate n C j hAO hback hfanin W
    (true_boundary_respects n C j x hback) C.gates.length le_rfl {C.output}
    (by simpa using Or.inl hout) (by simpa using hval)
  have hprotected : n + j ∈ T := by
    by_contra hp
    have raw : ∀ w ∈ T, w < n := by
      intro w hw
      rcases hTb w hw with h | eq
      · exact h
      · exact (hp (eq ▸ hw)).elim
    have hyes : circuitFun n C x = true := by
      apply hTf (AndBudget.boundary_W n C x) (boundary_respects n C j x hback) _ C.output (by simp)
      intro w hw
      have wt := hTt w hw
      rw [AndBudget.boundary_W_input n C x w (raw w hw)]
      exact (AndBudget.boundary_W_input n (Forced.trueCircuit C j) x w (raw w hw)) ▸ wt
    rw [hfalse] at hyes
    contradiction
  let S : Finset (Fin n) := Finset.univ.filter fun i => i.val ∈ T
  have himage : S.image Fin.val = T.erase (n + j) := by
    ext w
    constructor
    · intro hw
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
      apply Finset.mem_erase.mpr
      exact ⟨by omega, (Finset.mem_filter.mp hi).2⟩
    · intro hw
      have hb : w < n := by
        rcases hTb w (Finset.mem_of_mem_erase hw) with hb | eq
        · exact hb
        · exact (Finset.ne_of_mem_erase hw eq).elim
      exact Finset.mem_image.mpr ⟨⟨w, hb⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_of_mem_erase hw⟩, rfl⟩
  refine ⟨S, ?_, ?_, ?_⟩
  · intro i hi
    have h := hTt i.val (Finset.mem_filter.mp hi).2
    simpa only [W, AndBudget.boundary_W_input n (Forced.trueCircuit C j) x i.val i.isLt] using h
  · intro y hy
    apply hTf (AndBudget.boundary_W n (Forced.trueCircuit C j) y)
      (true_boundary_respects n C j y hback) _ C.output (by simp)
    intro w hw
    rcases hTb w hw with hb | eq
    · rw [AndBudget.boundary_W_input n (Forced.trueCircuit C j) y w hb]
      exact hy ⟨w, hb⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩)
    · subst w
      exact true_boundary_protected n C j y hj
  · have hcard := Finset.card_erase_add_one hprotected
    have hcardS : S.card = (T.erase (n + j)).card := by
      rw [← himage, Finset.card_image_of_injective S Fin.val_injective]
    simp only [Finset.card_singleton, AndBudget.and_count, List.take_length] at hTc
    omega

end Protected


lemma circuit_forced_or_false_positive_neighbors {p l : ℕ}
    (E : Finset (Fin p × Fin l)) (C : Circuit) (a : Fin p)
    (Q : Finset (Fin l)) (j : ℕ) (hj : j < C.gates.length)
    (hg : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (computes : ∀ x, circuitFun (p + l) C x = edgeEval E x)
    (star : ∀ x : Fin (p + l) → Bool,
      (C.wires (List.ofFn x)).getD (p + l + j) false =
        decide (∃ b ∈ Q, x (Fin.natAdd p b) = true))
    (x : Fin (p + l) → Bool)
    (falseOutput : edgeEval (E.filter fun e => e.1 ≠ a) x = false)
    (forced : Forced.value C j (Function.update x (Fin.castAdd l a) false) true = true) :
    ∀ b ∈ Q, ∃ a' : Fin p, a' ≠ a ∧ (a', b) ∈ E ∧ x (Fin.castAdd l a') = true := by
  exact forced_or_false_positive_neighbors E a Q
    (fun x t => Forced.value C j (Function.update x (Fin.castAdd l a) false) t)
    (Forced.cofactor_value_monotone C hg a j true)
    (Forced.cofactor_value_correct E C a Q j hj computes star) x falseOutput forced

lemma dirty_or_binary_and_bound {p l : ℕ} (E : Finset (Fin p × Fin l))
    (C : Circuit) (a : Fin p) (Q : Finset (Fin l)) (j : ℕ)
    (hcycle : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (ao : IsAO2 (p + l) C) (hj : j < C.gates.length)
    (hQ : ∀ b ∈ Q, (a, b) ∈ E)
    (computes : ∀ x, circuitFun (p + l) C x = edgeEval E x)
    (star : ∀ x : Fin (p + l) → Bool,
      (C.wires (List.ofFn x)).getD (p + l + j) false =
        decide (∃ b ∈ Q, x (Fin.natAdd p b) = true))
    (x : Fin (p + l) → Bool)
    (falseOutput : edgeEval (E.filter fun e => e.1 ≠ a) x = false)
    (forced : Forced.value C j (Function.update x (Fin.castAdd l a) false) true = true) :
    Q.card ≤ C.gates.countP AndBudget.branching_and := by
  classical
  let y := Function.update x (Fin.castAdd l a) false
  have trueY : circuitFun (p + l) (Forced.trueCircuit C j) y = true := by
    rw [Forced.trueCircuit_value]
    exact forced
  have falseY : circuitFun (p + l) C y = false := by
    rw [computes, edgeEval_set_left_false]
    exact falseOutput
  obtain ⟨S, hS, cert, bound⟩ := Protected.forced_input_certificate (p + l)
    C j ao.1 ao.2.1 (fun g hg => (ao.2.2 g hg).le) hj y trueY falseY
  have absent : Fin.castAdd l a ∉ S := by
    intro h
    have hy := hS _ h
    simp [y] at hy
  let z : Fin (p + l) → Bool := fun i => decide (i ∈ S)
  have trueZ : circuitFun (p + l) (Forced.trueCircuit C j) z = true :=
    cert z (fun i hi => by simp [z, hi])
  have updateZ : Function.update z (Fin.castAdd l a) false = z := by
    funext i
    by_cases hi : i = Fin.castAdd l a
    · subst i
      simp [z, absent]
    · simp [Function.update_of_ne hi]
  have forcedZ : Forced.value C j (Function.update z (Fin.castAdd l a) false) true = true := by
    rw [updateZ, ← Forced.trueCircuit_value]
    exact trueZ
  have zx : ∀ i, z i = true → x i = true := by
    intro i hi
    have hs : i ∈ S := of_decide_eq_true hi
    have hy := hS i hs
    by_cases hia : i = Fin.castAdd l a
    · subst i
      exact (absent hs).elim
    · simpa [y, Function.update_of_ne hia] using hy
  have falseZ : edgeEval (E.filter fun e => e.1 ≠ a) z = false := by
    apply Bool.eq_false_iff.mpr
    intro hz
    obtain ⟨e, he, hl, hr⟩ := of_decide_eq_true hz
    have yes : edgeEval (E.filter fun e => e.1 ≠ a) x = true :=
      decide_eq_true ⟨e, he, zx _ hl, zx _ hr⟩
    rw [falseOutput] at yes
    cases yes
  have cover := circuit_forced_or_false_positive_neighbors E C a Q j hj ao.1
    computes star z falseZ forcedZ
  let A : Finset (Fin p) := Finset.univ.filter fun a' => Fin.castAdd l a' ∈ S
  have aA : a ∉ A := by simpa [A] using absent
  have hcover : ∀ b ∈ Q, ∃ a' ∈ A, (a', b) ∈ E := by
    intro b hb
    obtain ⟨a', _, ha'b, ha'⟩ := cover b hb
    exact ⟨a', Finset.mem_filter.mpr ⟨Finset.mem_univ _, of_decide_eq_true ha'⟩, ha'b⟩
  have qA : Q.card ≤ A.card :=
    left_star_covered_by_other_centers_card_le E hcycle a Q A aA hQ hcover
  have Asub : A.image (Fin.castAdd l) ⊆ S := by
    intro i hi
    obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp hi
    exact (Finset.mem_filter.mp ha').2
  have AS : A.card ≤ S.card := by
    rw [← Finset.card_image_of_injective A (fun _ _ h => Fin.castAdd_inj.mp h)]
    exact Finset.card_le_card Asub
  exact qA.trans (AS.trans bound)

end PEqualNP.Outside.L_meta_4970
