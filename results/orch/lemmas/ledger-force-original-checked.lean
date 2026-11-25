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

end Forced

end PEqualNP.Outside.L_meta_4970
