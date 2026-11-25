import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4970

lemma empty_edges (p l : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) :
    ∃ S : Finset (Fin (p + l)),
      (∀ (a : Fin p) (b : Fin l), (a, b) ∈ (∅ : Finset (Fin p × Fin l)) →
        Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      (∅ : Finset (Fin p × Fin l)).card + S.card ≤ C.size + 1 := by
  exact ⟨∅, by simp⟩

end PEqualNP.Outside.L_meta_4970

namespace PEqualNP.Outside.L_meta_4970

lemma left_star_unique {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hcycle : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {a a' : Fin p} (Q : Finset (Fin l)) (hQ : 2 ≤ Q.card)
    (hleft : ∀ b ∈ Q, (a, b) ∈ E) (hright : ∀ b ∈ Q, (a', b) ∈ E) :
    a = a' := by
  obtain ⟨b, hb, b', hb', hne⟩ := Finset.one_lt_card.mp hQ
  by_contra ha
  exact hcycle a a' b b' ha hne ⟨hleft b hb, hleft b' hb', hright b hb, hright b' hb'⟩

lemma right_star_unique {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hcycle : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {b b' : Fin l} (P : Finset (Fin p)) (hP : 2 ≤ P.card)
    (hleft : ∀ a ∈ P, (a, b) ∈ E) (hright : ∀ a ∈ P, (a, b') ∈ E) :
    b = b' := by
  obtain ⟨a, ha, a', ha', hne⟩ := Finset.one_lt_card.mp hP
  by_contra hb
  exact hcycle a a' b b' hne hb ⟨hleft a ha, hright a ha, hleft a' ha', hright a' ha'⟩

lemma left_star_inter_card_le_one {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hcycle : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {a a' : Fin p} (ha : a ≠ a') (Q R : Finset (Fin l))
    (hQ : ∀ b ∈ Q, (a, b) ∈ E) (hR : ∀ b ∈ R, (a', b) ∈ E) :
    (Q ∩ R).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro b hb b' hb'
  by_contra hne
  exact hcycle a a' b b' ha hne
    ⟨hQ b (Finset.mem_inter.mp hb).1, hQ b' (Finset.mem_inter.mp hb').1,
      hR b (Finset.mem_inter.mp hb).2, hR b' (Finset.mem_inter.mp hb').2⟩

lemma ownership_cover {p l : ℕ} (E : Finset (Fin p × Fin l))
    (own : Fin p × Fin l → Fin (p + l))
    (hown : ∀ e ∈ E,
      own e = Fin.castAdd l e.1 ∨ own e = Fin.natAdd p e.2) :
    ∀ a b, (a, b) ∈ E →
      Fin.castAdd l a ∈ E.image own ∨ Fin.natAdd p b ∈ E.image own := by
  intro a b hab
  have hm : own (a, b) ∈ E.image own := Finset.mem_image_of_mem own hab
  rcases hown (a, b) hab with h | h
  · exact Or.inl (h ▸ hm)
  · exact Or.inr (h ▸ hm)

lemma ownership_ledger {α β : Type*} [DecidableEq β]
    (E : Finset α) (own : α → β) :
    (∑ v ∈ E.image own, ((E.filter (fun e => own e = v)).card - 1)) +
      (E.image own).card = E.card := by
  have hpos : ∀ v ∈ E.image own, 1 ≤ (E.filter (fun e => own e = v)).card := by
    intro v hv
    obtain ⟨e, he, hev⟩ := Finset.mem_image.mp hv
    exact Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hev⟩⟩
  calc
    (∑ v ∈ E.image own, ((E.filter (fun e => own e = v)).card - 1)) +
        (E.image own).card =
        ∑ v ∈ E.image own, ((E.filter (fun e => own e = v)).card - 1 + 1) := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
    _ = ∑ v ∈ E.image own, (E.filter (fun e => own e = v)).card := by
      apply Finset.sum_congr rfl
      intro v hv
      exact Nat.sub_add_cancel (hpos v hv)
    _ = E.card := (Finset.card_eq_sum_card_image own E).symm

lemma right_or_injective {p l : ℕ} (Q R : Finset (Fin l))
    (h : ∀ x : Fin (p + l) → Bool,
      decide (∃ b ∈ Q, x (Fin.natAdd p b) = true) =
      decide (∃ b ∈ R, x (Fin.natAdd p b) = true)) : Q = R := by
  ext b
  have hx := h (fun i => decide (i = Fin.natAdd p b))
  simpa using hx

lemma left_or_injective {p l : ℕ} (P R : Finset (Fin p))
    (h : ∀ x : Fin (p + l) → Bool,
      decide (∃ a ∈ P, x (Fin.castAdd l a) = true) =
      decide (∃ a ∈ R, x (Fin.castAdd l a) = true)) : P = R := by
  ext a
  have hx := h (fun i => decide (i = Fin.castAdd l a))
  simpa using hx

lemma opposite_or_distinct {p l : ℕ} (P : Finset (Fin p)) (Q : Finset (Fin l))
    (hQ : Q.Nonempty) :
    ¬ (∀ x : Fin (p + l) → Bool,
      decide (∃ a ∈ P, x (Fin.castAdd l a) = true) =
      decide (∃ b ∈ Q, x (Fin.natAdd p b) = true)) := by
  intro h
  obtain ⟨b, hb⟩ := hQ
  have hx := h (fun i => decide (i = Fin.natAdd p b))
  have hne : ∀ a : Fin p, Fin.castAdd l a ≠ Fin.natAdd p b := by
    intro a ha
    have hv := congrArg Fin.val ha
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    omega
  simp [hne, hb] at hx

lemma same_right_or_center_unique {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hcycle : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {a a' : Fin p} (Q R : Finset (Fin l)) (hQ : 2 ≤ Q.card)
    (hleft : ∀ b ∈ Q, (a, b) ∈ E) (hright : ∀ b ∈ R, (a', b) ∈ E)
    (h : ∀ x : Fin (p + l) → Bool,
      decide (∃ b ∈ Q, x (Fin.natAdd p b) = true) =
      decide (∃ b ∈ R, x (Fin.natAdd p b) = true)) : a = a' := by
  have heq := right_or_injective Q R h
  subst R
  exact left_star_unique E hcycle Q hQ hleft hright

lemma singleton_bilinear_false {p l : ℕ} (E : Finset (Fin p × Fin l))
    (v : Fin (p + l)) :
    decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧
      decide (Fin.castAdd l a = v) = true ∧
      decide (Fin.natAdd p b = v) = true) = false := by
  apply decide_eq_false_iff_not.mpr
  rintro ⟨a, b, _, ha, hb⟩
  simp only [decide_eq_true_eq] at ha hb
  have hv := congrArg Fin.val (ha.trans hb.symm)
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

lemma singleton_not_below_bilinear {p l : ℕ} (E : Finset (Fin p × Fin l))
    (f : (Fin (p + l) → Bool) → Bool) (v : Fin (p + l))
    (hv : f (fun i => decide (i = v)) = true) :
    ¬ (∀ x : Fin (p + l) → Bool, f x = true →
      decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧
        x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true) = true) := by
  intro h
  have hx := h (fun i => decide (i = v)) hv
  rw [singleton_bilinear_false E v] at hx
  cases hx

lemma right_or_not_below_bilinear {p l : ℕ} (E : Finset (Fin p × Fin l))
    (Q : Finset (Fin l)) (hQ : Q.Nonempty) :
    ¬ (∀ x : Fin (p + l) → Bool,
      decide (∃ b ∈ Q, x (Fin.natAdd p b) = true) = true →
      decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧
        x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true) = true) := by
  obtain ⟨b, hb⟩ := hQ
  apply singleton_not_below_bilinear E
    (fun x => decide (∃ b' ∈ Q, x (Fin.natAdd p b') = true)) (Fin.natAdd p b)
  simp [hb]

lemma left_or_not_below_bilinear {p l : ℕ} (E : Finset (Fin p × Fin l))
    (P : Finset (Fin p)) (hP : P.Nonempty) :
    ¬ (∀ x : Fin (p + l) → Bool,
      decide (∃ a ∈ P, x (Fin.castAdd l a) = true) = true →
      decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧
        x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true) = true) := by
  obtain ⟨a, ha⟩ := hP
  apply singleton_not_below_bilinear E
    (fun x => decide (∃ a' ∈ P, x (Fin.castAdd l a') = true)) (Fin.castAdd l a)
  simp [ha]

lemma singleton_separates_gate_sets {p l : ℕ} {ι : Type*}
    (E : Finset (Fin p × Fin l)) (A B : Finset ι)
    (value : ι → (Fin (p + l) → Bool) → Bool)
    (hA : ∀ j ∈ A, ∃ v : Fin (p + l), value j (fun i => decide (i = v)) = true)
    (hB : ∀ j ∈ B, ∀ x : Fin (p + l) → Bool, value j x = true →
      decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧
        x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true) = true) :
    Disjoint A B := by
  apply Finset.disjoint_left.mpr
  intro j hjA hjB
  obtain ⟨v, hv⟩ := hA j hjA
  exact singleton_not_below_bilinear E (value j) v hv (hB j hjB)

def StarWitness {p l : ℕ} (E : Finset (Fin p × Fin l))
    (value : ℕ → (Fin (p + l) → Bool) → Bool) : Fin p ⊕ Fin l → ℕ → Prop
  | .inl a, j => ∃ Q : Finset (Fin l), 2 ≤ Q.card ∧
      (∀ b ∈ Q, (a, b) ∈ E) ∧
      ∀ x : Fin (p + l) → Bool,
        value j x = decide (∃ b ∈ Q, x (Fin.natAdd p b) = true)
  | .inr b, j => ∃ P : Finset (Fin p), 2 ≤ P.card ∧
      (∀ a ∈ P, (a, b) ∈ E) ∧
      ∀ x : Fin (p + l) → Bool,
        value j x = decide (∃ a ∈ P, x (Fin.castAdd l a) = true)

lemma star_witness_center_unique {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hcycle : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (value : ℕ → (Fin (p + l) → Bool) → Bool)
    {v w : Fin p ⊕ Fin l} {j : ℕ}
    (hv : StarWitness E value v j) (hw : StarWitness E value w j) : v = w := by
  cases v with
  | inl a =>
    cases w with
    | inl a' =>
      obtain ⟨Q, hQ, hE, hval⟩ := hv
      obtain ⟨R, _, hE', hval'⟩ := hw
      apply congrArg Sum.inl
      apply same_right_or_center_unique E hcycle Q R hQ hE hE'
      intro x
      exact (hval x).symm.trans (hval' x)
    | inr b =>
      obtain ⟨Q, hQ, _, hval⟩ := hv
      obtain ⟨P, _, _, hval'⟩ := hw
      exfalso
      apply opposite_or_distinct P Q (Finset.card_pos.mp (by omega))
      intro x
      exact (hval' x).symm.trans (hval x)
  | inr b =>
    cases w with
    | inl a =>
      obtain ⟨P, _, _, hval⟩ := hv
      obtain ⟨Q, hQ, _, hval'⟩ := hw
      exfalso
      apply opposite_or_distinct P Q (Finset.card_pos.mp (by omega))
      intro x
      exact (hval x).symm.trans (hval' x)
    | inr b' =>
      obtain ⟨P, hP, hE, hval⟩ := hv
      obtain ⟨R, _, hE', hval'⟩ := hw
      have heq : P = R := left_or_injective P R (fun x => (hval x).symm.trans (hval' x))
      subst R
      exact congrArg Sum.inr (right_star_unique E hcycle P hP hE hE')

def centerEmbed {p l : ℕ} : Fin p ⊕ Fin l → Fin (p + l) :=
  Sum.elim (Fin.castAdd l) (Fin.natAdd p)

lemma centerEmbed_injective {p l : ℕ} :
    Function.Injective (@centerEmbed p l) := by
  intro v w h
  cases v with
  | inl a =>
    cases w with
    | inl a' =>
      have hv := congrArg Fin.val h
      change a.val = a'.val at hv
      exact congrArg Sum.inl (Fin.ext hv)
    | inr b =>
      have hv := congrArg Fin.val h
      change a.val = p + b.val at hv
      omega
  | inr b =>
    cases w with
    | inl a =>
      have hv := congrArg Fin.val h
      change p + b.val = a.val at hv
      omega
    | inr b' =>
      have hv := congrArg Fin.val h
      change p + b.val = p + b'.val at hv
      exact congrArg Sum.inr (Fin.ext (Nat.add_left_cancel hv))

lemma image_card_le_of_fiber_refinement {α β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (E : Finset α) (owner : α → β) (gate : α → γ)
    (hf : ∀ a ∈ E, ∀ b ∈ E, gate a = gate b → owner a = owner b) :
    (E.image owner).card ≤ (E.image gate).card := by
  classical
  let pick : E.image owner → α := fun b => (Finset.mem_image.mp b.property).choose
  have hpick : ∀ b : E.image owner, pick b ∈ E ∧ owner (pick b) = b.val := by
    intro b
    exact (Finset.mem_image.mp b.property).choose_spec
  let f : E.image owner → E.image gate := fun b =>
    ⟨gate (pick b), Finset.mem_image_of_mem gate (hpick b).1⟩
  apply Finset.card_le_card_of_injective (f := f)
  intro u v huv
  apply Subtype.ext
  exact (hpick u).2.symm.trans
    ((hf (pick u) (hpick u).1 (pick v) (hpick v).1 (congrArg Subtype.val huv)).trans
      (hpick v).2)

lemma selected_star_cover {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hcycle : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (value : ℕ → (Fin (p + l) → Bool) → Bool)
    (owner : Fin p × Fin l → Fin p ⊕ Fin l) (gate : Fin p × Fin l → ℕ)
    (howner : ∀ e ∈ E, owner e = .inl e.1 ∨ owner e = .inr e.2)
    (hstar : ∀ e ∈ E, StarWitness E value (owner e) (gate e)) :
    ∃ S : Finset (Fin (p + l)),
      (∀ a b, (a, b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      S.card ≤ (E.image gate).card := by
  let S := E.image (fun e => centerEmbed (owner e))
  refine ⟨S, ?_, ?_⟩
  · apply ownership_cover E (fun e => centerEmbed (owner e))
    intro e he
    rcases howner e he with h | h
    · exact Or.inl (congrArg centerEmbed h)
    · exact Or.inr (congrArg centerEmbed h)
  · have hcard : S.card = (E.image owner).card := by
      change (E.image (centerEmbed ∘ owner)).card = (E.image owner).card
      rw [← Finset.image_image]
      exact Finset.card_image_of_injOn centerEmbed_injective.injOn
    rw [hcard]
    apply image_card_le_of_fiber_refinement E owner gate
    intro e he e' he' hgate
    exact star_witness_center_unique E hcycle value (hstar e he) (hgate ▸ hstar e' he')

end PEqualNP.Outside.L_meta_4970

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

end PEqualNP.Outside.L_meta_4970

namespace PEqualNP.Outside.L_meta_4970.Semantic

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD i false

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma val_nil {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    val [] x i = if h : i < n then x ⟨i, h⟩ else false := by
  unfold val
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

lemma val_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
    val (gs ++ [g]) x i =
      if i = n + gs.length then g.op.eval (g.inputs.map fun j => val gs x j)
      else val gs x i := by
  unfold val
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, step]
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rcases lt_trichotomy i (n + gs.length) with h | h | h
  · rw [ite_eq_right (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [ite_eq_left h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [ite_eq_right (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

lemma gate_cases {X : Type} (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length ≤ 2) (f : X → ℕ → Bool) (z : X) :
    (∀ y, g.op.eval (g.inputs.map (f y)) = false) ∨
    ∃ a b, g.op.eval (g.inputs.map (f z)) = false →
      (f z a = false ∧ f z b = false ∧
        ∀ y, g.op.eval (g.inputs.map (f y)) = true → f y a = true ∨ f y b = true) := by
  obtain ⟨op, ins⟩ := g
  simp only at hop hlen ⊢
  match ins, hlen with
  | [], _ =>
    rcases hop with rfl | rfl
    · right
      exact ⟨0, 0, by simp [GateOp.eval]⟩
    · left
      simp [GateOp.eval]
  | [a], _ =>
    right
    refine ⟨a, a, ?_⟩
    rcases hop with rfl | rfl <;> simp [GateOp.eval]
  | [a, b], _ =>
    rcases hop with rfl | rfl
    · right
      by_cases h : f z a = false
      · refine ⟨a, a, ?_⟩
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          Bool.and_true, id_eq, Bool.and_eq_true]
        intro _
        exact ⟨h, h, fun y hy => Or.inl hy.1⟩
      · refine ⟨b, b, ?_⟩
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          Bool.and_true, id_eq, Bool.and_eq_true]
        intro hz
        have hb : f z b = false := by
          cases ha : f z a <;> cases hb : f z b <;> simp_all
        exact ⟨hb, hb, fun y hy => Or.inl hy.2⟩
    · right
      refine ⟨a, b, ?_⟩
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        Bool.or_false, id_eq, Bool.or_eq_true, Bool.or_eq_false_iff]
      intro hz
      exact ⟨hz.1, hz.2, fun y hy => hy⟩
  | _ :: _ :: _ :: _, h => simp at h

def Zof {n : ℕ} (S : Finset (Fin n)) : Fin n → Bool := fun c => decide (c ∉ S)

def eof {n : ℕ} (u : Fin n) : Fin n → Bool := fun c => decide (c = u)

def Inv {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) (l : Fin n → Fin n) : Prop :=
  ∀ i u v, val gs (Zof S) i = false → val gs (eof u) i = true → val gs (eof v) i = true →
    u ∈ S ∧ l u = l v

def Cnt {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) (i : ℕ) : Prop :=
  val gs (Zof S) i = false ∧
    ∃ u v : Fin n, u ≠ v ∧ val gs (eof u) i = true ∧ val gs (eof v) i = true

open Classical in
noncomputable def D {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) : Finset ℕ :=
  (Finset.Ico n (n + gs.length)).filter fun i =>
    Cnt S gs i ∧ (gs[i - n]?).map Gate.op = some GateOp.or

open Classical in
noncomputable def orGates (n : ℕ) (gs : List Gate) : Finset ℕ :=
  (Finset.Ico n (n + gs.length)).filter fun i =>
    (gs[i - n]?).map Gate.op = some GateOp.or

lemma D_mono {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) (g : Gate) :
    D S gs ⊆ D S (gs ++ [g]) := by
  classical
  intro i hi
  simp only [D, Finset.mem_filter, Finset.mem_Ico, List.length_append, List.length_cons,
    List.length_nil] at hi ⊢
  refine ⟨⟨hi.1.1, by omega⟩, ?_⟩
  have hne : i ≠ n + gs.length := by omega
  obtain ⟨⟨hz, u, v, huv, hu, hv⟩, hop⟩ := hi.2
  constructor
  · refine ⟨?_, u, v, huv, ?_, ?_⟩
    · rw [val_snoc, ite_eq_right hne]; exact hz
    · rw [val_snoc, ite_eq_right hne]; exact hu
    · rw [val_snoc, ite_eq_right hne]; exact hv
  · rw [List.getElem?_append_left (by omega)]
    exact hop

lemma merging_is_or {n : ℕ} (S : Finset (Fin n)) (gs : List Gate)
    (l : Fin n → Fin n) (hinv : Inv S gs l) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hz : g.op.eval (g.inputs.map fun j => val gs (Zof S) j) = false)
    {u v : Fin n}
    (hu : g.op.eval (g.inputs.map fun j => val gs (eof u) j) = true)
    (hv : g.op.eval (g.inputs.map fun j => val gs (eof v) j) = true)
    (hne : l u ≠ l v) : g.op = GateOp.or := by
  rcases hop with hop | hop
  · exfalso
    rw [hop] at hz hu hv
    simp only [GateOp.eval, List.all_map, Function.comp_def, id_eq,
      List.all_eq_true] at hu hv
    have hnot : ¬ ∀ i ∈ g.inputs, val gs (Zof S) i = true := by
      intro hall
      have htrue : GateOp.and.eval (g.inputs.map fun j => val gs (Zof S) j) = true := by
        simp only [GateOp.eval, List.all_map, Function.comp_def, id_eq, List.all_eq_true]
        exact hall
      simp_all
    push Not at hnot
    obtain ⟨i, hi, hfalse⟩ := hnot
    have hz' : val gs (Zof S) i = false := by
      cases h : val gs (Zof S) i <;> simp_all
    exact hne (hinv i u v hz' (hu i hi) (hv i hi)).2
  · exact hop

lemma main_inv {n : ℕ} (S : Finset (Fin n)) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∃ l : Fin n → Fin n, Inv S gs l ∧ S.card ≤ (S.image l).card + (D S gs).card := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨id, ?_, by simp⟩
    intro i u v hz hu hv
    rw [val_nil] at hz hu hv
    by_cases h : i < n
    · simp only [h, dite_true, Zof, eof, decide_eq_false_iff_not, not_not,
        decide_eq_true_eq] at hz hu hv
      subst hu
      subst hv
      exact ⟨hz, rfl⟩
    · simp [h] at hu
  | append_singleton gs g ih =>
    obtain ⟨l, hinv, hcard⟩ := ih (fun g' hg' => hg g' (by simp [hg']))
    obtain ⟨hop, hlen⟩ := hg g (by simp)
    set N := n + gs.length with hN
    set P : (Fin n → Bool) → Bool := fun x => g.op.eval (g.inputs.map fun j => val gs x j)
      with hP
    have hnew : ∀ x : Fin n → Bool, val (gs ++ [g]) x N = P x := by
      intro x
      rw [val_snoc, ite_eq_left hN]
    have hold : ∀ (x : Fin n → Bool) (i : ℕ), i ≠ N → val (gs ++ [g]) x i = val gs x i := by
      intro x i hi
      rw [val_snoc, ite_eq_right hi]
    -- facts about the new wire from the old invariant
    have key : P (Zof S) = false → ∀ u, P (eof u) = true →
        u ∈ S ∧ ∃ A B : Fin n → Prop, (∀ w, P (eof w) = true → A w ∨ B w) ∧
          (∀ w w', A w → A w' → l w = l w') ∧ (∀ w w', B w → B w' → l w = l w') := by
      intro hz u hu
      rcases gate_cases g hop hlen (fun x j => val gs x j) (Zof S) with hall | ⟨a, b, hab⟩
      · have := hall (eof u)
        simp only [hP] at hu
        rw [this] at hu
        exact absurd hu (by simp)
      · obtain ⟨ha, hb, hy⟩ := hab hz
        refine ⟨?_, fun w => val gs (eof w) a = true, fun w => val gs (eof w) b = true,
          fun w hw => hy (eof w) hw, fun w w' hw hw' => (hinv a w w' ha hw hw').2,
          fun w w' hw hw' => (hinv b w w' hb hw hw').2⟩
        rcases hy (eof u) hu with h | h
        · exact (hinv a u u ha h h).1
        · exact (hinv b u u hb h h).1
    by_cases hm : P (Zof S) = false ∧ ∃ u v, P (eof u) = true ∧ P (eof v) = true ∧ l u ≠ l v
    · obtain ⟨hz, u0, v0, hu0, hv0, hne⟩ := hm
      have hgor : g.op = GateOp.or := merging_is_or S gs l hinv g hop hz hu0 hv0 hne
      refine ⟨fun w => if l w = l v0 then l u0 else l w, ?_, ?_⟩
      · intro i u v hiz hiu hiv
        by_cases hi : i = N
        · subst hi
          rw [hnew] at hiz hiu hiv
          obtain ⟨huS, A, B, hAB, hA, hB⟩ := key hiz u hiu
          refine ⟨huS, ?_⟩
          have two : ∀ w, P (eof w) = true → l w = l u0 ∨ l w = l v0 := by
            intro w hw
            rcases hAB w hw with h | h <;> rcases hAB u0 hu0 with h0 | h0 <;>
              rcases hAB v0 hv0 with h1 | h1
            · exact Or.inl (hA w u0 h h0)
            · exact Or.inl (hA w u0 h h0)
            · exact Or.inr (hA w v0 h h1)
            · exact absurd (hB u0 v0 h0 h1) hne
            · exact absurd (hA u0 v0 h0 h1) hne
            · exact Or.inr (hB w v0 h h1)
            · exact Or.inl (hB w u0 h h0)
            · exact Or.inl (hB w u0 h h0)
          have red : ∀ w, P (eof w) = true → (if l w = l v0 then l u0 else l w) = l u0 := by
            intro w hw
            rcases two w hw with h | h
            · rw [h]; split_ifs <;> rfl
            · rw [ite_eq_left h]
          show (if l u = l v0 then l u0 else l u) = (if l v = l v0 then l u0 else l v)
          rw [red u hiu, red v hiv]
        · rw [hold _ _ hi] at hiz hiu hiv
          obtain ⟨huS, hl⟩ := hinv i u v hiz hiu hiv
          refine ⟨huS, ?_⟩
          show (if l u = l v0 then l u0 else l u) = (if l v = l v0 then l u0 else l v)
          rw [hl]
      · have himg : S.image l ⊆
            insert (l v0) (S.image fun w => if l w = l v0 then l u0 else l w) := by
          intro y hy
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
          by_cases h : l w = l v0
          · rw [h]; exact Finset.mem_insert_self _ _
          · refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨w, hw, ?_⟩)
            rw [ite_eq_right h]
        have h1 : (S.image l).card ≤
            (S.image fun w => if l w = l v0 then l u0 else l w).card + 1 :=
          (Finset.card_le_card himg).trans (Finset.card_insert_le _ _)
        have hNin : N ∈ D S (gs ++ [g]) := by
          simp only [D, Finset.mem_filter, Finset.mem_Ico, List.length_append,
            List.length_cons, List.length_nil]
          refine ⟨⟨by omega, by omega⟩, ⟨?_, u0, v0, ?_, ?_, ?_⟩, ?_⟩
          · rw [hnew]; exact hz
          · intro h; exact hne (by rw [h])
          · rw [hnew]; exact hu0
          · rw [hnew]; exact hv0
          · simp [hN, hgor]
        have hNnot : N ∉ D S gs := by
          simp only [D, Finset.mem_filter, Finset.mem_Ico]
          intro h
          omega
        have h2 : (D S gs).card + 1 ≤ (D S (gs ++ [g])).card := by
          rw [← Finset.card_insert_of_notMem hNnot]
          apply Finset.card_le_card
          intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · exact hNin
          · exact D_mono S gs g hi
        omega
    · refine ⟨l, ?_, ?_⟩
      · intro i u v hiz hiu hiv
        by_cases hi : i = N
        · subst hi
          rw [hnew] at hiz hiu hiv
          obtain ⟨huS, -⟩ := key hiz u hiu
          refine ⟨huS, ?_⟩
          by_contra hne
          exact hm ⟨hiz, u, v, hiu, hiv, hne⟩
        · rw [hold _ _ hi] at hiz hiu hiv
          exact hinv i u v hiz hiu hiv
      · have := Finset.card_le_card (D_mono S gs g)
        omega

lemma or_outputs_bound : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x)) = decide (∃ v ∈ S w, x v = true)) → ∑ w, ((S w).card - 1) ≤ (orGates n gates).card := by
  classical
  intro n m S hS gates out hg hev
  have hval : ∀ (w : Fin m) (x : Fin n → Bool),
      val gates x (out w) = decide (∃ v ∈ S w, x v = true) := fun w x => hev w x
  have hZ : ∀ w, val gates (Zof (S w)) (out w) = false := by
    intro w
    rw [hval]
    simp [Zof]
  have hE : ∀ w, ∀ u ∈ S w, val gates (eof u) (out w) = true := by
    intro w u hu
    rw [hval]
    simp only [decide_eq_true_eq]
    exact ⟨u, hu, by simp [eof]⟩
  choose l hinv hcard using fun w => main_inv (S w) gates hg
  have hbound : ∀ w, (S w).card - 1 ≤ (D (S w) gates).card := by
    intro w
    have h1 : ((S w).image (l w)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
      exact (hinv w (out w) u v (hZ w) (hE w u hu) (hE w v hv)).2
    have := hcard w
    omega
  have hdisj : ∀ a ∈ (Finset.univ : Finset (Fin m)), ∀ b ∈ (Finset.univ : Finset (Fin m)),
      a ≠ b → Disjoint (D (S a) gates) (D (S b) gates) := by
    intro a _ b _ hab
    rw [Finset.disjoint_left]
    intro i hia hib
    simp only [D, Finset.mem_filter, Finset.mem_Ico] at hia hib
    obtain ⟨-, ⟨hza, u, v, huv, hu, hv⟩, -⟩ := hia
    obtain ⟨-, ⟨hzb, -⟩, -⟩ := hib
    have hua := (hinv a i u u hza hu hu).1
    have hva := (hinv a i v v hza hv hv).1
    have hub := (hinv b i u u hzb hu hu).1
    have hvb := (hinv b i v v hzb hv hv).1
    have hsub : ({u, v} : Finset (Fin n)) ⊆ S a ∩ S b := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨hua, hub⟩
      · exact Finset.mem_inter.mpr ⟨hva, hvb⟩
    have h2 : ({u, v} : Finset (Fin n)).card = 2 := Finset.card_pair huv
    have := Finset.card_le_card hsub
    have := hS a b hab
    omega
  calc ∑ w, ((S w).card - 1) ≤ ∑ w, (D (S w) gates).card :=
        Finset.sum_le_sum fun w _ => hbound w
    _ = (Finset.univ.biUnion fun w => D (S w) gates).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ (orGates n gates).card := by
        apply Finset.card_le_card
        intro i hi
        obtain ⟨w, -, hw⟩ := Finset.mem_biUnion.mp hi
        simp only [D, Finset.mem_filter] at hw
        exact Finset.mem_filter.mpr ⟨hw.1, hw.2.2⟩

end PEqualNP.Outside.L_meta_4970.Semantic

namespace PEqualNP.Outside.L_meta_4970.AndBudget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

lemma output_gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma output_gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [output_gateAt_eq hj]; exact List.getElem_mem hj

open PEqualNP.CleanedNonEdge

lemma output_orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma output_orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [output_orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma output_orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := output_orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

lemma output_tail_step (n : ℕ) (C : Circuit) (g : ℕ) :
    ∀ w, OrReaches n C w g → g ≠ w - n →
      ∃ k, k < C.gates.length ∧ OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧
        n + g ∈ (gateAt C k).inputs := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h hne
    have hnw : n ≤ w := h.1
    obtain ⟨k0, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (output_orReaches_iff n C k0 g).mp h
    rcases h3 with h3 | ⟨hop, i, hi, hlt, hr⟩
    · exact (hne (by omega)).elim
    · have hself : OrReaches n C (n + k0) k0 :=
        (output_orReaches_iff n C k0 k0).mpr ⟨hk, Or.inl rfl⟩
      by_cases hg : g = i - n
      · refine ⟨k0, hk, hself, hop, ?_⟩
        have hni : n ≤ i := hr.1
        have e : n + g = i := by omega
        rw [e]
        exact hi
      · obtain ⟨k, hkl, hrk, hopk, hin⟩ := ih i hlt hr hg
        exact ⟨k, hkl,
          (output_orReaches_iff n C k0 k).mpr ⟨hk, Or.inr ⟨hop, i, hi, hlt, hrk⟩⟩, hopk, hin⟩

def output_par (n : ℕ) (C : Circuit) (O : Finset ℕ) : Finset ℕ :=
  O.biUnion (fun k => ((gateAt C k).inputs.toFinset).image (fun w => w - n))

lemma output_par_card (n : ℕ) (C : Circuit) (O : Finset ℕ)
    (h : ∀ k ∈ O, (gateAt C k).inputs.length = 2) : (output_par n C O).card ≤ O.card * 2 := by
  unfold output_par
  calc (O.biUnion (fun k => ((gateAt C k).inputs.toFinset).image (fun w => w - n))).card
      ≤ ∑ k ∈ O, (((gateAt C k).inputs.toFinset).image (fun w => w - n)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _k ∈ O, 2 := by
        apply Finset.sum_le_sum
        intro k hk
        exact Finset.card_image_le.trans
          ((List.toFinset_card_le _).trans (le_of_eq (h k hk)))
    _ = O.card * 2 := by rw [Finset.sum_const, smul_eq_mul]

lemma output_or_bound : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Finset ℕ), PEqualNP.TopForm.IsAO2 n C → (∀ j ∈ F, j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output j) → F.card ≤ Set.ncard {i : ℕ | i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output i} + 1 := by
  intro n C F hC hF
  obtain ⟨_, _, hlen⟩ := hC
  obtain ⟨O, hO⟩ : ∃ O : Finset ℕ, ∀ i, i ∈ O ↔ (i < C.gates.length ∧
      (gateAt C i).op = GateOp.or ∧ OrReaches n C C.output i) :=
      by
    have hfin : {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧
        OrReaches n C C.output i}.Finite := by
      apply (Finset.finite_toSet (Finset.range C.gates.length)).subset
      intro i hi
      have hi2 : i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧
          OrReaches n C C.output i := Eq.mp Set.mem_setOf_eq hi
      exact Finset.mem_coe.mpr (Finset.mem_range.mpr hi2.1)
    refine ⟨hfin.toFinset, fun i => ?_⟩
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have hset : {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧
      OrReaches n C C.output i} = (↑O : Set ℕ) := by
    ext i
    simp only [Set.mem_setOf_eq, Finset.mem_coe, hO]
  rw [hset, Set.ncard_coe_finset]
  have hdisj : Disjoint F O := by
    rw [Finset.disjoint_left]
    intro a ha hb
    have h1 := (hF a ha).2.1
    have h2 := ((hO a).mp hb).2.1
    rw [h1] at h2
    exact GateOp.noConfusion h2
  have hsub : F ∪ O ⊆ insert (C.output - n) (output_par n C O) := by
    intro g hg
    have hr : OrReaches n C C.output g := by
      rcases Finset.mem_union.mp hg with h | h
      · exact (hF g h).2.2
      · exact ((hO g).mp h).2.2
    by_cases hgo : g = C.output - n
    · exact Finset.mem_insert.mpr (Or.inl hgo)
    · obtain ⟨k, hk, hrk, hop, hin⟩ := output_tail_step n C g C.output hr hgo
      refine Finset.mem_insert.mpr (Or.inr ?_)
      unfold output_par
      exact Finset.mem_biUnion.mpr ⟨k, (hO k).mpr ⟨hk, hop, hrk⟩,
        Finset.mem_image.mpr ⟨n + g, List.mem_toFinset.mpr hin, by omega⟩⟩
  have hcard := output_par_card n C O (fun k hk => hlen _ (output_gateAt_mem ((hO k).mp hk).1))
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj] at h1
  have h2 := Finset.card_insert_le (C.output - n) (output_par n C O)
  omega

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def boundary_stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma boundary_wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl boundary_stepWire x := rfl

lemma boundary_foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl boundary_stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [boundary_stepWire]
    omega

lemma boundary_foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl boundary_stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (boundary_stepWire w g).length := by simp [boundary_stepWire]; omega
    rw [ih (boundary_stepWire w g) hlt]
    simp [boundary_stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma boundary_getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma boundary_wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [boundary_wires_eq_foldl, boundary_foldl_stepWire_length, List.length_ofFn]

lemma boundary_split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]


def boundary_W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

lemma boundary_gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma boundary_W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    boundary_W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then boundary_W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := boundary_split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [boundary_gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl boundary_stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, boundary_foldl_stepWire_length, hpre_len]
  have hCj : boundary_W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [boundary_W]
    rw [boundary_wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [boundary_foldl_stepWire_getD_lt post (boundary_stepWire w0 gj) (n + k) (by simp [boundary_stepWire]; omega)]
    simp [boundary_stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [boundary_W]
    rw [boundary_wires_eq_foldl, hgs, List.foldl_append]
    exact (boundary_foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact boundary_getD_ge_length w0 i (by omega)

lemma boundary_W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    boundary_W n C x u = x ⟨u, hu⟩ := by
  simp only [boundary_W]
  rw [boundary_wires_eq_foldl, boundary_foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

open PEqualNP.CleanedNonEdge in

lemma boundary_W_or (n : ℕ) (C : Circuit) (x : Fin n → Bool) (r : ℕ)
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or)
    (i : ℕ) (hi : i ∈ (gateAt C r).inputs) (hlt : i < n + r)
    (hv : boundary_W n C x i = true) : boundary_W n C x (n + r) = true := by
  rw [boundary_W_gate n C x r hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  exact ⟨i, hi, by rw [if_pos hlt]; exact hv⟩

lemma boundary_reach_up (n : ℕ) (C : Circuit) (x : Fin n → Bool) (g : ℕ)
    (hv : boundary_W n C x (n + g) = true) :
    ∀ w, OrReaches n C w g → boundary_W n C x w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hr
    have hn : n ≤ w := hr.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    rcases (output_orReaches_iff n C k g).mp hr with ⟨hk, rfl | ⟨hop, i, hi, hlt, hir⟩⟩
    · exact hv
    · exact boundary_W_or n C x k hk hop i hi hlt (ih i hlt hir)

lemma boundary_orIn_up (n : ℕ) (C : Circuit) (k i : ℕ) (a : Fin n)
    (hk : k < C.gates.length) (hop : (gateAt C k).op = GateOp.or)
    (hi : i ∈ (gateAt C k).inputs) (hlt : i < n + k)
    (ha : a ∈ PEqualNP.TopForm.orIn n C i) :
    a ∈ PEqualNP.TopForm.orIn n C (n + k) := by
  classical
  letI : DecidableEq GateOp := gateOpDecEq
  unfold PEqualNP.TopForm.orIn at ha ⊢
  have ha' := (@Finset.mem_filter _ _ _ _ _).mp ha
  apply (@Finset.mem_filter _ _ _ _ _).mpr
  refine ⟨Finset.mem_univ _, Or.inr ?_⟩
  rcases ha'.2 with h | ⟨j, hj, hr, hjor, haj⟩
  · exact ⟨k, hk, (output_orReaches_iff n C k k).mpr ⟨hk, Or.inl rfl⟩,
      hop, h ▸ hi⟩
  · exact ⟨j, hj, (output_orReaches_iff n C k j).mpr
      ⟨hk, Or.inr ⟨hop, i, hi, hlt, hr⟩⟩, hjor, haj⟩

lemma boundary_orIn_true (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (a : Fin n) (ha : a ∈ PEqualNP.TopForm.orIn n C w) (hx : x a = true) :
    boundary_W n C x w = true := by
  classical
  letI : DecidableEq GateOp := gateOpDecEq
  unfold PEqualNP.TopForm.orIn at ha
  have ha' := (@Finset.mem_filter _ _ _ _ _).mp ha
  rcases ha'.2 with h | ⟨k, hk, hr, hop, hin⟩
  · rw [← h, boundary_W_input n C x a.val a.isLt]
    exact hx
  · apply boundary_reach_up n C x k _ w hr
    apply boundary_W_or n C x k hk hop a.val hin (by have := a.isLt; omega)
    rw [boundary_W_input n C x a.val a.isLt]
    exact hx

lemma boundary_true_witness (n : ℕ) (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (x : Fin n → Bool) : ∀ w, boundary_W n C x w = true →
      (∃ a ∈ PEqualNP.TopForm.orIn n C w, x a = true) ∨
      ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧
        OrReaches n C w j ∧ boundary_W n C x (n + j) = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · left
      refine ⟨⟨w, hw⟩, ?_, ?_⟩
      · simp [PEqualNP.TopForm.orIn]
      · rw [boundary_W_input n C x w hw] at hv
        exact hv
    · have hn : n ≤ w := by omega
      obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by
        by_contra h
        have he : boundary_W n C x (n + k) = false := by
          apply boundary_getD_ge_length
          rw [boundary_wires_length]
          omega
        rw [he] at hv
        contradiction
      have hm := output_gateAt_mem hk
      rcases hAO.1 _ hm with hop | hop
      · right
        exact ⟨k, hk, hop, (output_orReaches_iff n C k k).mpr ⟨hk, Or.inl rfl⟩, hv⟩
      · have hv' := hv
        rw [boundary_W_gate n C x k hk, hop] at hv'
        simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hv'
        obtain ⟨i, hi, hiv⟩ := hv'
        have hlt : i < n + k := hAO.2.1 k hk i hi
        rw [if_pos hlt] at hiv
        rcases ih i hlt hiv with ⟨a, ha, hax⟩ | ⟨j, hj, hja, hr, hjv⟩
        · exact Or.inl ⟨a, boundary_orIn_up n C k i a hk hop hi hlt ha, hax⟩
        · exact Or.inr ⟨j, hj, hja, (output_orReaches_iff n C k j).mpr
            ⟨hk, Or.inr ⟨hop, i, hi, hlt, hr⟩⟩, hjv⟩

lemma boundary_output_and (n : ℕ) (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hsingle : ∀ a : Fin n, PEqualNP.MetaComplexity.circuitFun n C
      (fun i => decide (i = a)) = false) (x : Fin n → Bool)
    (hx : PEqualNP.MetaComplexity.circuitFun n C x = true) :
    ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧
      OrReaches n C C.output j ∧ boundary_W n C x (n + j) = true := by
  have hval : boundary_W n C x C.output = true := hx
  rcases boundary_true_witness n C hAO x C.output hval with ⟨a, ha, _⟩ | h
  · have hbad := boundary_orIn_true n C (fun i => decide (i = a)) C.output a ha (by simp)
    have hz : boundary_W n C (fun i => decide (i = a)) C.output = false := hsingle a
    rw [hz] at hbad
    contradiction
  · exact h

end PEqualNP.Outside.L_meta_4970.AndBudget
