import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2685.EliminationRoute

lemma leaf_zero {Np Nl : ℕ} (I : Fin Np → Fin Nl → Prop) [DecidableRel I]
    (p0 : Fin Np) (x : Fin Np → Bool) (y : Fin Nl → Bool) :
    decide (∃ p l, I p l ∧ Function.update x p0 false p = true ∧ y l = true) =
      decide (∃ p l, I p l ∧ p ≠ p0 ∧ x p = true ∧ y l = true) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨p, l, hp, hx, hy⟩
    have hne : p ≠ p0 := by
      rintro rfl
      simp at hx
    exact ⟨p, l, hp, hne, by simpa [Function.update_of_ne hne] using hx, hy⟩
  · rintro ⟨p, l, hp, hne, hx, hy⟩
    exact ⟨p, l, hp, by simpa [Function.update_of_ne hne] using hx, hy⟩

lemma leaf_one {Np Nl : ℕ} (I : Fin Np → Fin Nl → Prop) [DecidableRel I]
    (p0 : Fin Np) (l0 : Fin Nl) (edge : I p0 l0)
    (leaf : ∀ l, I p0 l → l = l0) (x : Fin Np → Bool) (y : Fin Nl → Bool) :
    decide (∃ p l, I p l ∧ Function.update x p0 true p = true ∧ y l = true) =
      (y l0 || decide (∃ p l, I p l ∧ l ≠ l0 ∧ x p = true ∧ y l = true)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Bool.or_eq_true]
  constructor
  · rintro ⟨p, l, hp, hx, hy⟩
    by_cases hl : l = l0
    · exact Or.inl (hl ▸ hy)
    · right
      have hne : p ≠ p0 := by
        rintro rfl
        exact hl (leaf l hp)
      exact ⟨p, l, hp, hl, by simpa [Function.update_of_ne hne] using hx, hy⟩
  · rintro (hy | ⟨p, l, hp, hl, hx, hy⟩)
    · exact ⟨p0, l0, edge, by simp, hy⟩
    · have hne : p ≠ p0 := by
        rintro rfl
        exact hl (leaf l hp)
      exact ⟨p, l, hp, by simpa [Function.update_of_ne hne] using hx, hy⟩

lemma duplicate_leaf_cover {Np Nl : ℕ} (I : Fin Np → Fin Nl → Prop)
    (p0 p1 : Fin Np) (l0 : Fin Nl) (distinct : p0 ≠ p1)
    (edge : I p1 l0) (leaf0 : ∀ l, I p0 l → l = l0)
    (leaf1 : ∀ l, I p1 l → l = l0)
    (A : Finset (Fin Np)) (B : Finset (Fin Nl))
    (cover : ∀ p l, I p l → p ≠ p0 → p ∈ A ∨ l ∈ B) :
    ∃ (A' : Finset (Fin Np)) (B' : Finset (Fin Nl)),
      (∀ p l, I p l → p ∈ A' ∨ l ∈ B') ∧
      A'.card + B'.card ≤ A.card + B.card := by
  classical
  by_cases hb : l0 ∈ B
  · refine ⟨A, B, ?_, le_rfl⟩
    intro p l hp
    by_cases h : p = p0
    · exact Or.inr ((leaf0 l (h ▸ hp)) ▸ hb)
    · exact cover p l hp h
  · have ha : p1 ∈ A := (cover p1 l0 edge distinct.symm).resolve_right hb
    refine ⟨A.erase p1, insert l0 B, ?_, ?_⟩
    · intro p l hp
      by_cases hp0 : p = p0
      · right
        have h := leaf0 l (hp0 ▸ hp)
        simp [h]
      by_cases hp1 : p = p1
      · right
        have h := leaf1 l (hp1 ▸ hp)
        simp [h]
      rcases cover p l hp hp0 with h | h
      · exact Or.inl (Finset.mem_erase.mpr ⟨hp1, h⟩)
      · exact Or.inr (Finset.mem_insert_of_mem h)
    · have he := Finset.card_erase_add_one ha
      rw [Finset.card_insert_of_notMem hb]
      omega


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

noncomputable def inputSupport {n : ℕ} (f : (Fin n → Bool) → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i => ∃ x, f (Function.update x i (!x i)) ≠ f x

lemma mem_inputSupport {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n) :
    i ∈ inputSupport f ↔ ∃ x, f (Function.update x i (!x i)) ≠ f x := by
  classical
  simp [inputSupport]

lemma support_family_update {α : Type} [DecidableEq α] (R : ℕ → Finset α)
    (k : ℕ) (bound : ∀ S : Finset ℕ, (S.biUnion R).card ≤ k + S.card)
    (w : ℕ) (T : Finset ℕ) (B : Finset α)
    (hT : T.card ≤ 2) (hB : B ⊆ T.biUnion R) (S : Finset ℕ) :
    (S.biUnion (Function.update R w B)).card ≤ k + 1 + S.card := by
  classical
  by_cases hw : w ∈ S
  · have sub : S.biUnion (Function.update R w B) ⊆ (S.erase w ∪ T).biUnion R := by
      intro i hi
      obtain ⟨v, hv, hi⟩ := Finset.mem_biUnion.mp hi
      by_cases hvw : v = w
      · subst v
        simp only [Function.update_self] at hi
        obtain ⟨v, hv, hi⟩ := Finset.mem_biUnion.mp (hB hi)
        exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_union_right _ hv, hi⟩
      · rw [Function.update_of_ne hvw] at hi
        exact Finset.mem_biUnion.mpr
          ⟨v, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hvw, hv⟩), hi⟩
    have hcard := Finset.card_le_card sub
    have hbound := bound (S.erase w ∪ T)
    have hunion := Finset.card_union_le (S.erase w) T
    have herase := Finset.card_erase_add_one hw
    omega
  · have eq : S.biUnion (Function.update R w B) = S.biUnion R := by
      apply Finset.biUnion_congr rfl
      intro v hv
      have hvw : v ≠ w := by
        rintro rfl
        exact hw hv
      exact Function.update_of_ne hvw _ _
    rw [eq]
    have := bound S
    omega

lemma fold_wires_length (gs : List Gate) (x : List Bool) :
    (gs.foldl (fun vs g => vs ++ [g.op.eval (g.inputs.map fun w => vs.getD w false)]) x).length =
      x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    simp
    omega

lemma getD_append_one (xs : List Bool) (b : Bool) (w : ℕ) :
    (xs ++ [b]).getD w false = if w = xs.length then b else xs.getD w false := by
  induction xs generalizing w with
  | nil => cases w <;> simp
  | cons a xs ih => cases w <;> simp_all

noncomputable def wireSupport (n : ℕ) (gs : List Gate) (w : ℕ) : Finset (Fin n) :=
  inputSupport (circuitFun n ⟨gs, w⟩)

def nextValue (n : ℕ) (gs : List Gate) (g : Gate) (x : Fin n → Bool) : Bool :=
  g.op.eval (g.inputs.map fun w => circuitFun n ⟨gs, w⟩ x)

lemma circuitFun_append (n : ℕ) (gs : List Gate) (g : Gate) (w : ℕ) (x : Fin n → Bool) :
    circuitFun n ⟨gs ++ [g], w⟩ x =
      if w = n + gs.length then nextValue n gs g x else circuitFun n ⟨gs, w⟩ x := by
  simp only [circuitFun, Circuit.eval, Circuit.wires, List.foldl_append,
    List.foldl_cons, List.foldl_nil, getD_append_one, fold_wires_length, List.length_ofFn]
  rfl

lemma wireSupport_append (n : ℕ) (gs : List Gate) (g : Gate) :
    wireSupport n (gs ++ [g]) =
      Function.update (wireSupport n gs) (n + gs.length) (inputSupport (nextValue n gs g)) := by
  classical
  funext w
  by_cases hw : w = n + gs.length
  · subst w
    simp only [Function.update_self, wireSupport]
    congr 1
    funext x
    simp [circuitFun_append]
  · rw [Function.update_of_ne hw]
    unfold wireSupport
    congr 1
    funext x
    simp [circuitFun_append, hw]

lemma nextValue_support (n : ℕ) (gs : List Gate) (g : Gate) :
    inputSupport (nextValue n gs g) ⊆ g.inputs.toFinset.biUnion (wireSupport n gs) := by
  classical
  intro i hi
  obtain ⟨x, hx⟩ := (mem_inputSupport _ _).mp hi
  by_contra hn
  have hagree : ∀ w ∈ g.inputs,
      circuitFun n ⟨gs, w⟩ (Function.update x i (!x i)) = circuitFun n ⟨gs, w⟩ x := by
    intro w hw
    have hnot : i ∉ wireSupport n gs w := by
      intro hs
      exact hn (Finset.mem_biUnion.mpr ⟨w, List.mem_toFinset.mpr hw, hs⟩)
    apply Classical.byContradiction
    intro h
    exact hnot ((mem_inputSupport _ _).mpr ⟨x, h⟩)
  apply hx
  unfold nextValue
  congr 1
  exact List.map_congr_left hagree

lemma empty_support_mem (n w : ℕ) (i : Fin n) (hi : i ∈ wireSupport n [] w) :
    i.val = w := by
  classical
  obtain ⟨x, hx⟩ := (mem_inputSupport _ _).mp hi
  by_contra hne
  apply hx
  simp only [circuitFun, Circuit.eval, Circuit.wires, List.foldl_nil,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split
  · rename_i hw
    have h : (⟨w, hw⟩ : Fin n) ≠ i := by
      intro he
      exact hne (congrArg Fin.val he).symm
    simp [Function.update_of_ne h]
  · rfl

lemma support_family_bound (n : ℕ) (gs : List Gate)
    (fanin : ∀ g ∈ gs, g.inputs.length ≤ 2) (S : Finset ℕ) :
    (S.biUnion (wireSupport n gs)).card ≤ gs.length + S.card := by
  classical
  induction gs using List.reverseRecOn generalizing S with
  | nil =>
    simp only [List.length_nil, Nat.zero_add]
    apply Finset.card_le_card_of_injOn (fun i : Fin n => i.val)
    · intro i hi
      obtain ⟨w, hw, hi⟩ := Finset.mem_biUnion.mp hi
      change i.val ∈ S
      rw [empty_support_mem n w i hi]
      exact hw
    · intro i hi j hj h
      exact Fin.ext h
  | append_singleton gs g ih =>
    have hgs : ∀ a ∈ gs, a.inputs.length ≤ 2 := by
      intro a ha
      exact fanin a (List.mem_append.mpr (Or.inl ha))
    have hg : g.inputs.length ≤ 2 := fanin g (by simp)
    rw [wireSupport_append]
    have := support_family_update (wireSupport n gs) gs.length (ih hgs)
      (n + gs.length) g.inputs.toFinset (inputSupport (nextValue n gs g))
      (le_trans (List.toFinset_card_le g.inputs) hg) (nextValue_support n gs g) S
    simpa using this

lemma essential_card_le_size (n : ℕ) (C : Circuit)
    (fanin : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (S : Finset (Fin n))
    (hS : ∀ i ∈ S, ∃ x : Fin n → Bool,
      circuitFun n C (Function.update x i (!x i)) ≠ circuitFun n C x) :
    S.card ≤ C.size + 1 := by
  classical
  have sub : S ⊆ wireSupport n C.gates C.output := by
    intro i hi
    exact (mem_inputSupport _ _).mpr (hS i hi)
  have hb := support_family_bound n C.gates fanin {C.output}
  simpa only [Finset.singleton_biUnion, Finset.card_singleton, Circuit.size] using
    (Finset.card_le_card sub).trans (by simpa using hb)

end PEqualNP.Outside.L_meta_2685.EliminationRoute
