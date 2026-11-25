import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4970_aux

lemma right_centre_unique {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hC4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {Q : Finset (Fin l)} (hQ : 2 ≤ Q.card) {a a' : Fin p}
    (ha : ∀ b ∈ Q, (a, b) ∈ E) (ha' : ∀ b ∈ Q, (a', b) ∈ E) : a = a' := by
  by_contra hne
  obtain ⟨b, hb, b', hb', hbb'⟩ := Finset.one_lt_card.mp (by omega : 1 < Q.card)
  exact hC4 a a' b b' hne hbb' ⟨ha b hb, ha b' hb', ha' b hb, ha' b' hb'⟩

lemma left_centre_unique {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hC4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {P : Finset (Fin p)} (hP : 2 ≤ P.card) {b b' : Fin l}
    (hb : ∀ a ∈ P, (a, b) ∈ E) (hb' : ∀ a ∈ P, (a, b') ∈ E) : b = b' := by
  by_contra hne
  obtain ⟨a, ha, a', ha', haa'⟩ := Finset.one_lt_card.mp (by omega : 1 < P.card)
  exact hC4 a a' b b' haa' hne ⟨hb a ha, hb' a ha, hb a' ha', hb' a' ha'⟩

lemma right_leaf_set_unique {p l : ℕ} {Q Q' : Finset (Fin l)}
    (h : ∀ x : Fin (p + l) → Bool,
      decide (∃ b ∈ Q, x (Fin.natAdd p b) = true) =
        decide (∃ b ∈ Q', x (Fin.natAdd p b) = true)) : Q = Q' := by
  classical
  ext b
  have hb := h (fun i => decide (i = Fin.natAdd p b))
  simpa using hb

lemma left_leaf_set_unique {p l : ℕ} {P P' : Finset (Fin p)}
    (h : ∀ x : Fin (p + l) → Bool,
      decide (∃ a ∈ P, x (Fin.castAdd l a) = true) =
        decide (∃ a ∈ P', x (Fin.castAdd l a) = true)) : P = P' := by
  classical
  ext a
  have ha := h (fun i => decide (i = Fin.castAdd l a))
  simpa using ha

lemma left_right_pure_ne {p l : ℕ} (P : Finset (Fin p)) (Q : Finset (Fin l))
    (hQ : Q.Nonempty) :
    ¬ (∀ x : Fin (p + l) → Bool,
      decide (∃ a ∈ P, x (Fin.castAdd l a) = true) =
        decide (∃ b ∈ Q, x (Fin.natAdd p b) = true)) := by
  classical
  intro h
  obtain ⟨b, hb⟩ := hQ
  have htest := h (fun i => decide (p ≤ i.val))
  have hleft : ¬ (∃ a ∈ P, decide (p ≤ (Fin.castAdd l a).val) = true) := by
    rintro ⟨a, _, ha⟩
    have := of_decide_eq_true ha
    exact Nat.not_le_of_gt a.isLt this
  have hright : ∃ b ∈ Q, decide (p ≤ (Fin.natAdd p b).val) = true := by
    exact ⟨b, hb, by simp⟩
  simp only [hleft, hright, decide_false, decide_true, Bool.false_eq_true] at htest

lemma cover_card_of_unique_witnesses {p l : ℕ} (E : Finset (Fin p × Fin l))
    (J : Finset ℕ) (W : ℕ → Fin (p + l) → Prop)
    (hUnique : ∀ j ∈ J, ∀ u v, W j u → W j v → u = v)
    (hCover : ∀ a b, (a, b) ∈ E →
      (∃ j ∈ J, W j (Fin.castAdd l a)) ∨
        (∃ j ∈ J, W j (Fin.natAdd p b))) :
    ∃ S : Finset (Fin (p + l)),
      (∀ a b, (a, b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
        S.card ≤ J.card := by
  classical
  let S := J.biUnion fun j => Finset.univ.filter (W j)
  refine ⟨S, ?_, ?_⟩
  · intro a b hab
    rcases hCover a b hab with ⟨j, hj, hw⟩ | ⟨j, hj, hw⟩
    · exact Or.inl (Finset.mem_biUnion.mpr
        ⟨j, hj, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩⟩)
    · exact Or.inr (Finset.mem_biUnion.mpr
        ⟨j, hj, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩⟩)
  · calc
      S.card ≤ ∑ j ∈ J, (Finset.univ.filter (W j)).card := Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ J, 1 := by
        apply Finset.sum_le_sum
        intro j hj
        apply Finset.card_le_one.mpr
        intro u hu v hv
        exact hUnique j hj u v (Finset.mem_filter.mp hu).2 (Finset.mem_filter.mp hv).2
      _ = J.card := by simp

def StarCentre {p l : ℕ} (E : Finset (Fin p × Fin l))
    (f : ℕ → (Fin (p + l) → Bool) → Bool) (j : ℕ) (v : Fin (p + l)) : Prop :=
  (∃ (a : Fin p) (Q : Finset (Fin l)), v = Fin.castAdd l a ∧ 2 ≤ Q.card ∧
    (∀ b ∈ Q, (a, b) ∈ E) ∧
    ∀ x, f j x = decide (∃ b ∈ Q, x (Fin.natAdd p b) = true)) ∨
  (∃ (b : Fin l) (P : Finset (Fin p)), v = Fin.natAdd p b ∧ 2 ≤ P.card ∧
    (∀ a ∈ P, (a, b) ∈ E) ∧
    ∀ x, f j x = decide (∃ a ∈ P, x (Fin.castAdd l a) = true))

lemma starCentre_unique {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hC4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (f : ℕ → (Fin (p + l) → Bool) → Bool) (j : ℕ) (u v : Fin (p + l))
    (hu : StarCentre E f j u) (hv : StarCentre E f j v) : u = v := by
  rcases hu with ⟨a, Q, rfl, hQ, ha, hfun⟩ | ⟨b, P, rfl, hP, hb, hfun⟩
  · rcases hv with ⟨a', Q', rfl, hQ', ha', hfun'⟩ | ⟨b', P', rfl, hP', hb', hfun'⟩
    · have hQQ' : Q = Q' := right_leaf_set_unique (fun x => (hfun x).symm.trans (hfun' x))
      subst Q'
      exact congrArg (Fin.castAdd l) (right_centre_unique E hC4 hQ ha ha')
    · exact False.elim (left_right_pure_ne P' Q
        (Finset.card_pos.mp (by omega)) (fun x => (hfun' x).symm.trans (hfun x)))
  · rcases hv with ⟨a', Q', rfl, hQ', ha', hfun'⟩ | ⟨b', P', rfl, hP', hb', hfun'⟩
    · exact False.elim (left_right_pure_ne P Q'
        (Finset.card_pos.mp (by omega)) (fun x => (hfun x).symm.trans (hfun' x)))
    · have hPP' : P = P' := left_leaf_set_unique (fun x => (hfun x).symm.trans (hfun' x))
      subst P'
      exact congrArg (Fin.natAdd p) (left_centre_unique E hC4 hP hb hb')

lemma cover_card_of_star_witnesses {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hC4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (J : Finset ℕ) (f : ℕ → (Fin (p + l) → Bool) → Bool)
    (hCover : ∀ a b, (a, b) ∈ E →
      (∃ j ∈ J, ∃ Q : Finset (Fin l), 2 ≤ Q.card ∧ b ∈ Q ∧
        (∀ b' ∈ Q, (a, b') ∈ E) ∧
        ∀ x, f j x = decide (∃ b' ∈ Q, x (Fin.natAdd p b') = true)) ∨
      (∃ j ∈ J, ∃ P : Finset (Fin p), 2 ≤ P.card ∧ a ∈ P ∧
        (∀ a' ∈ P, (a', b) ∈ E) ∧
        ∀ x, f j x = decide (∃ a' ∈ P, x (Fin.castAdd l a') = true))) :
    ∃ S : Finset (Fin (p + l)),
      (∀ a b, (a, b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
        S.card ≤ J.card := by
  apply cover_card_of_unique_witnesses E J (StarCentre E f)
  · intro j _ u v hu hv
    exact starCentre_unique E hC4 f j u v hu hv
  · intro a b hab
    rcases hCover a b hab with ⟨j, hj, Q, hQ, _, ha, hfun⟩ | ⟨j, hj, P, hP, _, hb, hfun⟩
    · exact Or.inl ⟨j, hj, Or.inl ⟨a, Q, rfl, hQ, ha, hfun⟩⟩
    · exact Or.inr ⟨j, hj, Or.inr ⟨b, P, rfl, hP, hb, hfun⟩⟩

lemma pure_or_of_max_zero {α : Type} [Fintype α] [DecidableEq α]
    (Q : Finset α) (f : (α → Bool) → Bool)
    (hmono : ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true)
    (haccept : ∀ x, (∃ i ∈ Q, x i = true) → f x = true)
    (hzero : f (fun i => decide (i ∉ Q)) = false) :
    ∀ x, f x = decide (∃ i ∈ Q, x i = true) := by
  intro x
  by_cases hx : ∃ i ∈ Q, x i = true
  · simp only [decide_eq_true hx]
    exact haccept x hx
  · have hf : f x = false := by
      cases heq : f x with
      | false => rfl
      | true =>
          have ht := hmono x (fun i => decide (i ∉ Q)) (by
            intro i hi
            apply decide_eq_true
            intro hmem
            exact hx ⟨i, hmem, hi⟩) heq
          rw [hzero] at ht
          contradiction
    simp only [decide_eq_false hx]
    exact hf

lemma pure_or_and_choice {α : Type} [Fintype α] [DecidableEq α]
    (Q : Finset α) (f g : (α → Bool) → Bool)
    (hf : ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true)
    (hg : ∀ x y, (∀ i, x i = true → y i = true) → g x = true → g y = true)
    (heq : ∀ x, (f x && g x) = decide (∃ i ∈ Q, x i = true)) :
    (∀ x, f x = decide (∃ i ∈ Q, x i = true)) ∨
    (∀ x, g x = decide (∃ i ∈ Q, x i = true)) := by
  classical
  have hzero : (f (fun i => decide (i ∉ Q)) && g (fun i => decide (i ∉ Q))) = false := by
    rw [heq]
    apply decide_eq_false
    rintro ⟨i, hi, hni⟩
    exact (of_decide_eq_true hni) hi
  have haccept : ∀ x, (∃ i ∈ Q, x i = true) → f x = true ∧ g x = true := by
    intro x hx
    have h := heq x
    rw [decide_eq_true hx] at h
    exact Bool.and_eq_true_iff.mp h
  rcases Bool.and_eq_false_iff.mp hzero with h | h
  · exact Or.inl (pure_or_of_max_zero Q f hf (fun x hx => (haccept x hx).1) h)
  · exact Or.inr (pure_or_of_max_zero Q g hg (fun x hx => (haccept x hx).2) h)

lemma no_twoColour (p l : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit)
    (ht : PEqualNP.TwoColour.tCount (p + l) C (fun i => decide (p ≤ i)) = 0)
    (g : ℕ) :
    ¬ PEqualNP.TwoColour.IsTwoColour (p + l) C (fun i => decide (p ≤ i)) g := by
  intro h
  have he : PEqualNP.TwoColour.twoColour (p + l) C (fun i => decide (p ≤ i)) = ∅ :=
    Finset.card_eq_zero.mp ht
  have hm : g ∈ PEqualNP.TwoColour.twoColour (p + l) C (fun i => decide (p ≤ i)) := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h.1, h⟩
  rw [he] at hm
  exact Finset.notMem_empty g hm

lemma orIn_monochromatic (p l : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit)
    (ht : PEqualNP.TwoColour.tCount (p + l) C (fun i => decide (p ≤ i)) = 0)
    (g : ℕ) (hg : g < C.gates.length)
    (ho : (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op =
      PEqualNP.CircuitLowerBounds.GateOp.or) :
    (∀ i ∈ PEqualNP.TopForm.orIn (p + l) C (p + l + g), (i : ℕ) < p) ∨
    (∀ i ∈ PEqualNP.TopForm.orIn (p + l) C (p + l + g), p ≤ (i : ℕ)) := by
  classical
  by_cases h : ∀ i ∈ PEqualNP.TopForm.orIn (p + l) C (p + l + g), p ≤ (i : ℕ)
  · exact Or.inr h
  · push Not at h
    obtain ⟨i, hi, hip⟩ := h
    refine Or.inl ?_
    intro j hj
    by_contra hnp
    apply no_twoColour p l C ht g
    refine ⟨hg, ho, ⟨i, hi, ?_⟩, ⟨j, hj, ?_⟩⟩
    · exact decide_eq_false (by omega)
    · exact decide_eq_true (by omega)

def pureOr {α : Type*} [Fintype α] [DecidableEq α] (Q : Finset α)
    (x : α → Bool) : Bool := decide (∃ q ∈ Q, x q = true)

def complementInput {α : Type*} [DecidableEq α] (Q : Finset α) (i : α) : Bool :=
  decide (i ∉ Q)

lemma below_pureOr_iff_complement_false {α : Type*} [Fintype α] [DecidableEq α]
    (Q : Finset α) (f : (α → Bool) → Bool) (hf : Monotone f) :
    (∀ x, f x = true → pureOr Q x = true) ↔ f (complementInput Q) = false := by
  constructor
  · intro h
    by_contra hfalse
    have htrue : f (complementInput Q) = true := Bool.eq_true_of_not_eq_false hfalse
    have hp := h (complementInput Q) htrue
    unfold pureOr complementInput at hp
    simp at hp
  · intro hfalse x hx
    by_contra hnot
    have hn : ¬ ∃ q ∈ Q, x q = true := by
      simpa only [pureOr, decide_eq_true_eq] using hnot
    have hxle : x ≤ complementInput Q := by
      intro i
      by_cases hi : i ∈ Q
      · have hix : x i = false := by
          cases h : x i
          · rfl
          · exact False.elim (hn ⟨i, hi, h⟩)
        simp [complementInput, hi, hix]
      · simp [complementInput, hi]
    have hle := hf hxle
    rw [hx, hfalse] at hle
    exact (by decide : ¬ (true ≤ false)) hle

lemma and_below_pureOr_choose {α : Type*} [Fintype α] [DecidableEq α]
    (Q : Finset α) (f g : (α → Bool) → Bool) (hf : Monotone f) (hg : Monotone g)
    (h : ∀ x, (f x && g x) = true → pureOr Q x = true) :
    (∀ x, f x = true → pureOr Q x = true) ∨
      (∀ x, g x = true → pureOr Q x = true) := by
  have hfalse : (f (complementInput Q) && g (complementInput Q)) = false := by
    by_contra hn
    have ht := h (complementInput Q) (Bool.eq_true_of_not_eq_false hn)
    simp [pureOr, complementInput] at ht
  rcases Bool.and_eq_false_iff.mp hfalse with hf0 | hg0
  · exact Or.inl ((below_pureOr_iff_complement_false Q f hf).mpr hf0)
  · exact Or.inr ((below_pureOr_iff_complement_false Q g hg).mpr hg0)

lemma singleton_below_pureOr {α : Type*} [Fintype α] [DecidableEq α]
    (Q : Finset α) (f : (α → Bool) → Bool)
    (h : ∀ x, f x = true → pureOr Q x = true)
    (i : α) (hi : f (fun j => decide (j = i)) = true) : i ∈ Q := by
  have hp := h _ hi
  simpa [pureOr] using hp

lemma demand_split_union {α : Type*} [DecidableEq α] (D A B : Finset α)
    (hD : D ⊆ A ∪ B) :
    ∃ DA DB : Finset α,
      DA ⊆ A ∧ DB ⊆ B ∧ Disjoint DA DB ∧ DA ∪ DB = D := by
  refine ⟨D ∩ A, D \ A, Finset.inter_subset_right, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨hiD, hiA⟩ := Finset.mem_sdiff.mp hi
    exact (Finset.mem_union.mp (hD hiD)).resolve_left hiA
  · exact Finset.disjoint_left.mpr (by
      intro i hi hi'
      exact (Finset.mem_sdiff.mp hi').2 (Finset.mem_inter.mp hi).2)
  · ext i
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

lemma single_centre_size : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m)) (C : Circuit), E.Nonempty → (∃ t : Fin (n+m), ∀ e ∈ E, Fin.castAdd m e.1 = t ∨ Fin.natAdd n e.2 = t) →
      let computes := fun (F : Finset (Fin n × Fin m)) (D : Circuit) => IsAO2 (n+m) D ∧
          ∀ z, circuitFun (n+m) D z = decide (∃ e ∈ F, z (Fin.castAdd m e.1) = true ∧ z (Fin.natAdd n e.2) = true)
      computes E C → E.card ≤ C.size := by
  classical
  let run (gs : List Gate) (x : List Bool) : List Bool :=
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

  have other (x : List Bool) (b : Bool) (i : ℕ) (h : i ≠ x.length) :
      (x ++ [b]).getD i false = x.getD i false := by
    by_cases lt : i < x.length
    · exact List.getD_append _ _ _ _ lt
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

  have cone (gs : List Gate) (arity : ∀ g ∈ gs, g.inputs.length ≤ 2)
      (n : ℕ) (T : Finset ℕ) :
      ∃ S : Finset ℕ, S.card ≤ T.card + gs.length ∧
        ∀ x y : List Bool, x.length = n → y.length = n →
          (∀ i ∈ S, x.getD i false = y.getD i false) →
          ∀ j ∈ T, (run gs x).getD j false = (run gs y).getD j false := by
    induction gs generalizing n T with
    | nil => exact ⟨T,by simp,fun _ _ _ _ h => h⟩
    | cons g gs ih =>
      obtain ⟨S,small,protect⟩ := ih (fun u hu => arity u (by simp [hu])) (n+1) T
      let value (x : List Bool) := g.op.eval (g.inputs.map fun i => x.getD i false)
      by_cases used : n ∈ S
      · let R := S.erase n ∪ g.inputs.toFinset
        refine ⟨R,?_,?_⟩
        · have h := Finset.card_union_le (S.erase n) g.inputs.toFinset
          have ea := Finset.card_erase_add_one used
          have inputs := List.toFinset_card_le g.inputs
          have two := arity g (by simp)
          change (S.erase n ∪ g.inputs.toFinset).card ≤ T.card + (g :: gs).length
          simp only [List.length_cons]
          omega
        · intro x y hx hy agree
          apply protect (x ++ [value x]) (y ++ [value y]) (by simp [hx]) (by simp [hy])
          intro j hj
          by_cases split : j = n
          · subst j
            have val : value x = value y := by
              apply congrArg g.op.eval
              apply List.map_congr_left
              intro i hi
              exact agree i (Finset.mem_union_right _ (List.mem_toFinset.mpr hi))
            have atEnd (z : List Bool) (b : Bool) : (z ++ [b]).getD z.length false = b := by simp
            calc
              (x ++ [value x]).getD n false = value x := hx ▸ atEnd x _
              _ = value y := val
              _ = (y ++ [value y]).getD n false := hy ▸ (atEnd y _).symm
          · rw [other x _ j (by omega),other y _ j (by omega)]
            exact agree j (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨split,hj⟩))
      · refine ⟨S,by simp only [List.length_cons]; omega,?_⟩
        intro x y hx hy agree
        apply protect (x ++ [value x]) (y ++ [value y]) (by simp [hx]) (by simp [hy])
        intro j hj
        have diff : j ≠ n := fun h => used (h ▸ hj)
        rw [other x _ j (by omega),other y _ j (by omega)]
        exact agree j hj

  have essentialInputs (n : ℕ) (C : Circuit) (arity : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
      (A : Finset (Fin n))
      (essential : ∀ i ∈ A, ∃ x y : Fin n → Bool,
        (∀ j, j ≠ i → x j = y j) ∧ circuitFun n C x ≠ circuitFun n C y) :
      A.card ≤ C.size + 1 := by
    obtain ⟨S,hs,protect⟩ := cone C.gates arity n {C.output}
    have subset : A.image Fin.val ⊆ S := by
      intro j hj
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
      by_contra notin
      obtain ⟨x,y,agree,changeVal⟩ := essential i hi
      apply changeVal
      apply protect (List.ofFn x) (List.ofFn y) (by simp) (by simp) _ C.output (by simp)
      intro k hk
      by_cases h : k < n
      · rw [List.getD_eq_getElem (List.ofFn x) _ (by simpa using h),List.getD_eq_getElem (List.ofFn y) _ (by simpa using h)]
        simp only [List.getElem_ofFn]
        exact agree ⟨k,h⟩ (fun e => notin ((congrArg Fin.val e) ▸ hk))
      · rw [List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by simp;omega)]
    have ci := Finset.card_le_card subset
    rw [Finset.card_image_of_injective _ Fin.val_injective] at ci
    simp only [Finset.card_singleton] at hs
    change A.card ≤ C.gates.length + 1
    omega

  have star : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m)) (C : Circuit), E.Nonempty → (∃ t : Fin (n+m), ∀ e ∈ E, Fin.castAdd m e.1 = t ∨ Fin.natAdd n e.2 = t) →
      let computes := fun (F : Finset (Fin n × Fin m)) (D : Circuit) => IsAO2 (n+m) D ∧
          ∀ z, circuitFun (n+m) D z = decide (∃ e ∈ F, z (Fin.castAdd m e.1) = true ∧ z (Fin.natAdd n e.2) = true)
      computes E C → E.card ≤ C.size := by
    classical
    intro n m E C nonempty single
    dsimp only
    rintro ⟨ao,correct⟩
    obtain ⟨t,atCenter⟩ := single
    let L (p : Fin n) := Fin.castAdd m p
    let R (l : Fin m) := Fin.natAdd n l
    have separated (p : Fin n) (l : Fin m) : L p ≠ R l := by
      intro e
      have h := congrArg Fin.val e
      change p.val = n + l.val at h
      omega
    let ends (e : Fin n × Fin m) : Finset (Fin (n+m)) := {L e.1,R e.2}
    let A := E.biUnion ends
    have left (e) (he : e ∈ E) : L e.1 ∈ A :=
      Finset.mem_biUnion.mpr ⟨e,he,by simp [ends]⟩
    have right (e) (he : e ∈ E) : R e.2 ∈ A :=
      Finset.mem_biUnion.mpr ⟨e,he,by simp [ends]⟩
    have singletonOff (v : Fin (n+m)) :
        circuitFun (n+m) C (fun j => decide (j = v)) = false := by
      rw [correct,decide_eq_false_iff_not]
      rintro ⟨e,_,one,two⟩
      exact separated e.1 e.2 ((of_decide_eq_true one).trans (of_decide_eq_true two).symm)
    have edgeOn (e) (he : e ∈ E) :
        circuitFun (n+m) C (fun j => decide (j ∈ ends e)) = true := by
      rw [correct,decide_eq_true_eq]
      exact ⟨e,he,by simp [ends,L],by simp [ends,R]⟩
    have active : A.card ≤ C.size + 1 := by
      apply essentialInputs (n+m) C (fun g hg => Nat.le_of_eq (ao.2.2 g hg)) A
      intro i hi
      obtain ⟨e,he,hi⟩ := Finset.mem_biUnion.mp hi
      have keep (u v : Fin (n+m)) (record : ends e = {u,v}) :
          ∃ x y : Fin (n+m) → Bool, (∀ j, j ≠ u → x j = y j) ∧
            circuitFun (n+m) C x ≠ circuitFun (n+m) C y := by
        refine ⟨fun j => decide (j ∈ ends e),fun j => decide (j = v),?_,?_⟩
        · intro j diff
          simp [record,diff]
        · rw [edgeOn e he,singletonOff]
          decide
      rcases (show i = L e.1 ∨ i = R e.2 by simpa [ends] using hi) with rfl | rfl
      · exact keep _ _ rfl
      · exact keep _ _ (Finset.pair_comm ..)
    obtain ⟨e₀,h₀⟩ := nonempty
    have tin : t ∈ A := (atCenter e₀ h₀).elim (fun h => h ▸ left e₀ h₀) (fun h => h ▸ right e₀ h₀)
    let opposite (e : Fin n × Fin m) := if L e.1 = t then R e.2 else L e.1
    have otherIn (e) (he : e ∈ E) : opposite e ∈ A.erase t := by
      rcases atCenter e he with l | r
      · change L e.1 = t at l
        have nr : R e.2 ≠ t := fun h => separated _ _ (l.trans h.symm)
        simpa [opposite,l] using Finset.mem_erase.mpr ⟨nr,right e he⟩
      · change R e.2 = t at r
        have nl : L e.1 ≠ t := fun h => separated _ _ (h.trans r.symm)
        simpa [opposite,nl] using Finset.mem_erase.mpr ⟨nl,left e he⟩
    have leftInj : Function.Injective L := by
      intro a b h
      exact Fin.ext (congrArg (fun z : Fin (n+m) => z.val) h)
    have rightInj : Function.Injective R := by
      intro a b h
      apply Fin.ext
      have e := congrArg Fin.val h
      change n + a.val = n + b.val at e
      omega
    have inj : Set.InjOn opposite (E : Set (Fin n × Fin m)) := by
      intro e he f hf same
      by_cases le : L e.1 = t <;> by_cases lf : L f.1 = t <;> simp only [opposite,le,lf,↓reduceIte] at same
      · exact Prod.ext (leftInj (le.trans lf.symm)) (rightInj same)
      · exact (separated f.1 e.2 same.symm).elim
      · exact (separated e.1 f.2 same).elim
      · exact Prod.ext (leftInj same) (rightInj (((atCenter e he).resolve_left le).trans ((atCenter f hf).resolve_left lf).symm))
    have sz := Finset.card_le_card (show E.image opposite ⊆ A.erase t by
      intro j hj
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hj
      exact otherIn e he)
    rw [Finset.card_image_of_injOn inj] at sz
    have := Finset.card_erase_add_one tin
    omega
  exact star


lemma single_centre_cover (n m : ℕ) (E : Finset (Fin n × Fin m)) (C : Circuit)
    (ao : IsAO2 (n + m) C)
    (correct : ∀ x : Fin (n + m) → Bool, circuitFun (n + m) C x =
      decide (∃ e ∈ E, x (Fin.castAdd m e.1) = true ∧ x (Fin.natAdd n e.2) = true))
    (centre : ∃ t : Fin (n + m), ∀ e ∈ E,
      Fin.castAdd m e.1 = t ∨ Fin.natAdd n e.2 = t) :
    ∃ S : Finset (Fin (n + m)),
      (∀ a b, (a, b) ∈ E → Fin.castAdd m a ∈ S ∨ Fin.natAdd n b ∈ S) ∧
      E.card + S.card ≤ C.size + 1 := by
  classical
  by_cases empty : E = ∅
  · refine ⟨∅, ?_, ?_⟩
    · simp [empty]
    · simp [empty]
  · obtain ⟨t, ht⟩ := centre
    have cost := single_centre_size n m E C (Finset.nonempty_iff_ne_empty.mpr empty)
      ⟨t, ht⟩ ⟨ao, correct⟩
    refine ⟨{t}, ?_, ?_⟩
    · intro a b hab
      simpa only [Finset.mem_singleton] using ht (a, b) hab
    · simpa only [Finset.card_singleton] using Nat.add_le_add_right cost 1

namespace OrCount

open PEqualNP.CircuitLowerBounds
def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma gate_inputs {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size) :
    ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ r ∈ P, r < w) ∧
      ∀ (x y : Fin n → Bool), (∀ r ∈ P, value C x r = true → value C y r = true) →
        value C x w = true → value C y w = true := by
  let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
  obtain ⟨hop, hlen⟩ := hG g (List.getElem_mem _)
  let P := g.inputs.toFinset.filter (· < w)
  refine ⟨P, (Finset.card_filter_le _ _).trans ((List.toFinset_card_le g.inputs).trans hlen), ?_, ?_⟩
  · exact fun r hr => (Finset.mem_filter.mp hr).2
  · intro x y hxy hx
    have step (r) (hr : r ∈ g.inputs) :
        (if r < w then value C x r else false) = true →
        (if r < w then value C y r else false) = true := by
      by_cases h : r < w
      · simpa [h] using hxy r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr,h⟩)
      · simp [h]
    have form (z : Fin n → Bool) :
        value C z w = g.op.eval (g.inputs.map fun r => if r < w then value C z r else false) :=
      gate_value C z w hn hw
    rw [form x] at hx
    rw [form y]
    rcases hop with hop|hop
    · simp only [hop, GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hx ⊢
      intro b hb
      obtain ⟨r,hr,rfl⟩ := hb
      exact step r hr (hx _ ⟨r,hr,rfl⟩)
    · simp only [hop, GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hx ⊢
      obtain ⟨b,⟨r,hr,rfl⟩,hv⟩ := hx
      exact ⟨_, ⟨r,hr,rfl⟩, step r hr hv⟩

lemma value_mono {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using hxy p
    by_cases hw : w < n + C.size
    · obtain ⟨P, _, hP, hstep⟩ := gate_inputs C hG w (by omega) hw
      exact hstep x y fun r hr => ih r (hP r hr)
    · simp [missing_value C x w (by omega)]

def support {n : ℕ} (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p => value C (fun q => decide (q = p)) w = true)

lemma mem_support {n : ℕ} (C : Circuit) (w : ℕ) (p : Fin n) :
    p ∈ support C w ↔ value C (fun q => decide (q = p)) w = true := by
  simp [support]

lemma support_gate {n : ℕ} (C : Circuit) (w : ℕ) (h : 2 ≤ (support (n := n) C w).card) :
    n ≤ w ∧ w < n + C.size := by
  constructor
  · by_contra! hw
    let p : Fin n := ⟨w, hw⟩
    have hs : support C w ⊆ {p} := by
      intro q hq
      have hv := (mem_support C w q).mp hq
      change value C (fun r => decide (r = q)) p = true at hv
      simpa [input_value, eq_comm] using hv
    have hb := Finset.card_le_card hs
    simp at hb
    omega
  · by_contra! hw
    have hs : support (n := n) C w = ∅ := by
      ext q
      simp [mem_support, missing_value C _ w hw]
    simp [hs] at h

abbrev good (C : Circuit) := ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

def orFlag (n : ℕ) (C : Circuit) (w : ℕ) : Bool :=
  match (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - n)).op with
  | .or => true
  | _ => false

lemma split_false {n : ℕ} (C : Circuit) (hG : good C) (y : Fin n → Bool)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size) (hy : value C y w = false) :
    ∃ P : Finset ℕ, P.card ≤ 1 + (if orFlag n C w then 1 else 0) ∧
      (∀ r ∈ P, r < w) ∧ (∀ r ∈ P, value C y r = false) ∧
      ∀ a ∈ support (n := n) C w, ∃ r ∈ P, a ∈ support C r := by
  classical
  have hj : w - n < C.gates.length := by unfold Circuit.size at hw; omega
  let g := C.gates[w - n]
  have hgate : PEqualNP.MetaComplexity.NestedCover.gateAt C (w - n) = g := by
    rw [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem _ _ hj]
  have hgval : ∀ x : Fin n → Bool,
      value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) :=
    fun x => gate_value C x w hn hw
  obtain ⟨hop, hlen⟩ := hG g (List.getElem_mem _)
  rcases hop with hop | hop
  · have hgy : (g.inputs.map fun r => if r < w then value C y r else false).all id = false := by
      have h := (hgval y).symm
      rw [hy, hop] at h
      exact h
    have hgy' : ¬ ((g.inputs.map fun r => if r < w then value C y r else false).all id = true) :=
      fun h => Bool.false_ne_true (hgy.symm.trans h)
    simp only [List.all_eq_true, List.mem_map, id_eq, not_forall] at hgy'
    obtain ⟨_, ⟨u, hu, rfl⟩, huf⟩ := hgy'
    have hsupport : ∀ a ∈ support (n := n) C w,
        (if u < w then value C (fun q => decide (q = a)) u else false) = true := by
      intro a ha
      have hgp : (g.inputs.map fun r =>
          if r < w then value C (fun q => decide (q = a)) r else false).all id = true := by
        have h := (hgval (fun q => decide (q = a))).symm
        rw [(mem_support C w a).mp ha, hop] at h
        exact h
      simp only [List.all_eq_true, List.mem_map, id_eq] at hgp
      exact hgp _ ⟨u, hu, rfl⟩
    by_cases hut : u < w
    · have huy : value C y u = false := by
        simp only [hut, ↓reduceIte] at huf
        exact Bool.eq_false_iff.mpr huf
      refine ⟨{u}, by simp, ?_, ?_, ?_⟩
      · intro r hr
        obtain rfl := Finset.mem_singleton.mp hr
        exact hut
      · intro r hr
        obtain rfl := Finset.mem_singleton.mp hr
        exact huy
      · intro a ha
        refine ⟨u, Finset.mem_singleton_self _, (mem_support C u a).mpr ?_⟩
        simpa [hut] using hsupport a ha
    · refine ⟨∅, by simp, by simp, by simp, ?_⟩
      intro a ha
      have := hsupport a ha
      simp [hut] at this
  · let P := g.inputs.toFinset.filter (· < w)
    have hor : orFlag n C w = true := by
      simp only [orFlag, hgate, hop]
    have hPc : P.card ≤ 2 :=
      (Finset.card_filter_le _ _).trans ((List.toFinset_card_le g.inputs).trans hlen)
    refine ⟨P, by simpa [hor] using hPc, ?_, ?_, ?_⟩
    · intro r hr
      exact (Finset.mem_filter.mp hr).2
    · intro r hr
      have hmem := List.mem_toFinset.mp (Finset.mem_filter.mp hr).1
      have hlt := (Finset.mem_filter.mp hr).2
      have hgy : (g.inputs.map fun s => if s < w then value C y s else false).any id = false := by
        have h := (hgval y).symm
        rw [hy, hop] at h
        exact h
      have hgy' : ¬ ((g.inputs.map fun s => if s < w then value C y s else false).any id = true) :=
        fun h => Bool.false_ne_true (hgy.symm.trans h)
      simp only [List.any_eq_true, List.mem_map, id_eq] at hgy'
      rw [Bool.eq_false_iff]
      intro hv
      exact hgy' ⟨true, ⟨r, hmem, by simp [hlt, hv]⟩, rfl⟩
    · intro a ha
      have hgp : (g.inputs.map fun r =>
          if r < w then value C (fun q => decide (q = a)) r else false).any id = true := by
        have h := (hgval (fun q => decide (q = a))).symm
        rw [(mem_support C w a).mp ha, hop] at h
        exact h
      simp only [List.any_eq_true, List.mem_map, id_eq] at hgp
      obtain ⟨_, ⟨u, hu, rfl⟩, huv⟩ := hgp
      by_cases hut : u < w
      · exact ⟨u, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hu, hut⟩,
          (mem_support C u a).mpr (by simpa [hut] using huv)⟩
      · simp [hut] at huv

lemma frontier_cut {α : Type*} [DecidableEq α]
    (supp : ℕ → Finset α) (neg : ℕ → Prop) (G K : Finset ℕ)
    (hstep : ∀ w ∈ G, neg w → ∃ P : Finset ℕ,
      P.card ≤ 1 + (if w ∈ K then 1 else 0) ∧
      (∀ r ∈ P, r < w) ∧ (∀ r ∈ P, neg r) ∧
      ∀ a ∈ supp w, ∃ r ∈ P, a ∈ supp r)
    (t : ℕ) (F : Finset ℕ)
    (hFt : ∀ w ∈ F, w ∈ G → w < t) (hFn : ∀ w ∈ F, neg w) :
    ∃ B : Finset ℕ, Disjoint B G ∧ (∀ w ∈ B, neg w) ∧
      B.card ≤ F.card + (K.filter (· < t)).card ∧
      ∀ a, (∃ w ∈ F, a ∈ supp w) → ∃ w ∈ B, a ∈ supp w := by
  classical
  induction t generalizing F with
  | zero =>
    refine ⟨F, Finset.disjoint_left.mpr ?_, hFn, by simp, fun _ h => h⟩
    intro w hw hg
    have := hFt w hw hg
    omega
  | succ t ih =>
    by_cases hex : t ∈ F ∧ t ∈ G
    · obtain ⟨P, hPc, hPt, hPn, hPs⟩ := hstep t hex.2 (hFn t hex.1)
      let F' := F.erase t ∪ P
      have hF't : ∀ w ∈ F', w ∈ G → w < t := by
        intro w hw hg
        rcases Finset.mem_union.mp hw with hw | hw
        · have hne := (Finset.mem_erase.mp hw).1
          have hlt := hFt w (Finset.mem_erase.mp hw).2 hg
          omega
        · exact hPt w hw
      have hF'n : ∀ w ∈ F', neg w := by
        intro w hw
        rcases Finset.mem_union.mp hw with hw | hw
        · exact hFn w (Finset.mem_erase.mp hw).2
        · exact hPn w hw
      obtain ⟨B, hd, hn, hc, hs⟩ := ih F' hF't hF'n
      have hsize : F'.card ≤ F.card + (if t ∈ K then 1 else 0) := by
        have hu := Finset.card_union_le (F.erase t) P
        have he := Finset.card_erase_add_one hex.1
        change F'.card ≤ _ at hu
        omega
      have hfilter : (K.filter (· < t + 1)).card =
          (K.filter (· < t)).card + (if t ∈ K then 1 else 0) := by
        by_cases ht : t ∈ K
        · have heq : K.filter (· < t + 1) = insert t (K.filter (· < t)) := by
            ext w
            simp only [Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨hw, hlt⟩
              by_cases h : w = t
              · exact Or.inl h
              · exact Or.inr ⟨hw, by omega⟩
            · rintro (rfl | ⟨hw, hlt⟩)
              · exact ⟨ht, by omega⟩
              · exact ⟨hw, by omega⟩
          rw [heq, Finset.card_insert_of_notMem (by simp)]
          simp [ht]
        · have heq : K.filter (· < t + 1) = K.filter (· < t) := by
            ext w
            simp only [Finset.mem_filter]
            constructor
            · rintro ⟨hw, hlt⟩
              have hne : w ≠ t := fun h => ht (h ▸ hw)
              exact ⟨hw, by omega⟩
            · rintro ⟨hw, hlt⟩
              exact ⟨hw, by omega⟩
          rw [heq]
          simp [ht]
      refine ⟨B, hd, hn, by omega, ?_⟩
      intro a ⟨w, hw, ha⟩
      apply hs a
      by_cases hwt : w = t
      · subst w
        obtain ⟨r, hr, har⟩ := hPs a ha
        exact ⟨r, Finset.mem_union_right _ hr, har⟩
      · exact ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwt, hw⟩), ha⟩
    · have hF't : ∀ w ∈ F, w ∈ G → w < t := by
        intro w hw hg
        have hne : w ≠ t := fun h => hex ⟨h ▸ hw, h ▸ hg⟩
        have hlt := hFt w hw hg
        omega
      obtain ⟨B, hd, hn, hc, hs⟩ := ih F hF't hFn
      have hle : (K.filter (· < t)).card ≤ (K.filter (· < t + 1)).card :=
        Finset.card_le_card fun w hw => Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hw).1, by have := (Finset.mem_filter.mp hw).2; omega⟩
      exact ⟨B, hd, hn, by omega, hs⟩

def owned {n : ℕ} (C : Circuit) (S : Finset (Fin n)) : Finset ℕ :=
  (Finset.Ico n (n + C.size)).filter fun w =>
    support C w ⊆ S ∧ 2 ≤ (support (n := n) C w).card

def ownedOr {n : ℕ} (C : Circuit) (S : Finset (Fin n)) : Finset ℕ :=
  (owned C S).filter fun w => orFlag n C w

lemma count_or {n : ℕ} (C : Circuit) (hG : good C) (S : Finset (Fin n))
    (F : Finset ℕ)
    (hpos : ∀ p ∈ S, ∃ w ∈ F, p ∈ support C w)
    (hneg : ∀ w ∈ F, value C (fun p => decide (p ∉ S)) w = false) :
    S.card ≤ F.card + (ownedOr C S).card := by
  classical
  let y : Fin n → Bool := fun p => decide (p ∉ S)
  let G := owned C S
  let K := ownedOr C S
  have hgate : ∀ w ∈ G, n ≤ w ∧ w < n + C.size := by
    intro w hw
    exact Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1
  have hstep : ∀ w ∈ G, value C y w = false → ∃ P : Finset ℕ,
      P.card ≤ 1 + (if w ∈ K then 1 else 0) ∧
      (∀ r ∈ P, r < w) ∧ (∀ r ∈ P, value C y r = false) ∧
      ∀ a ∈ support (n := n) C w, ∃ r ∈ P, a ∈ support C r := by
    intro w hw hy
    obtain ⟨P, hc, ht, hn, hs⟩ := split_false C hG y w (hgate w hw).1 (hgate w hw).2 hy
    have hmem : w ∈ K ↔ orFlag n C w = true := by
      simp only [K, ownedOr, Finset.mem_filter]
      change w ∈ G ∧ orFlag n C w = true ↔ orFlag n C w = true
      simp [hw]
    exact ⟨P, by simpa only [hmem] using hc, ht, hn, hs⟩
  obtain ⟨B, hd, hn, hc, hs⟩ :=
    frontier_cut (support (n := n) C) (fun w => value C y w = false) G K hstep
      (n + C.size) F (fun w _ hw => (hgate w hw).2) hneg
  have hsmall : ∀ w ∈ B, (support (n := n) C w).card ≤ 1 := by
    intro w hw
    have hsub : support (n := n) C w ⊆ S := by
      intro p hp
      by_contra hpS
      have hpt := (mem_support C w p).mp hp
      have hmono := value_mono C hG (fun q => decide (q = p)) y (by
        intro q hq
        have hqp : q = p := of_decide_eq_true hq
        subst q
        simp [y, hpS]) w hpt
      rw [hn w hw] at hmono
      exact Bool.false_ne_true hmono
    by_contra! hlarge
    have hreal := support_gate C w (by omega)
    have hwG : w ∈ G := Finset.mem_filter.mpr
      ⟨Finset.mem_Ico.mpr hreal, hsub, by omega⟩
    exact Finset.disjoint_left.mp hd hw hwG
  have hcovered : S ⊆ B.biUnion (support C) := by
    intro p hp
    obtain ⟨w, hw, hwp⟩ := hs p (hpos p hp)
    exact Finset.mem_biUnion.mpr ⟨w, hw, hwp⟩
  have h1 := Finset.card_le_card hcovered
  have h2 := Finset.card_biUnion_le_card_mul B (support C) 1 hsmall
  have h3 := Finset.card_filter_le K (fun w => w < n + C.size)
  change S.card ≤ F.card + K.card
  omega

lemma count_or_one {n : ℕ} (C : Circuit) (hG : good C) (S : Finset (Fin n))
    (o : ℕ) (hpos : ∀ p ∈ S, p ∈ support C o)
    (hneg : value C (fun p => decide (p ∉ S)) o = false) :
    S.card - 1 ≤ (ownedOr C S).card := by
  have h := count_or C hG S {o}
    (fun p hp => ⟨o, Finset.mem_singleton_self _, hpos p hp⟩)
    (by intro w hw; obtain rfl := Finset.mem_singleton.mp hw; exact hneg)
  simp only [Finset.card_singleton] at h
  omega

end OrCount

lemma owned_support_disjoint {α β : Type*} [DecidableEq α] [DecidableEq β]
    (Q : α → Finset β) (K : Finset ℕ) (supp : ℕ → Finset β)
    {a b : α} (hsep : (Q a ∩ Q b).card ≤ 1) :
    Disjoint (K.filter fun j => 2 ≤ (supp j).card ∧ supp j ⊆ Q a)
      (K.filter fun j => 2 ≤ (supp j).card ∧ supp j ⊆ Q b) := by
  apply Finset.disjoint_left.mpr
  intro j hja hjb
  obtain ⟨_, hlarge, hsa⟩ := Finset.mem_filter.mp hja
  obtain ⟨_, _, hsb⟩ := Finset.mem_filter.mp hjb
  have hcard := Finset.card_le_card (Finset.subset_inter hsa hsb)
  omega

lemma sum_owned_support_bound {α β : Type*} [DecidableEq α] [DecidableEq β]
    (I : Finset α) (Q : α → Finset β) (K : Finset ℕ) (supp : ℕ → Finset β)
    (hsep : ∀ a ∈ I, ∀ b ∈ I, a ≠ b → (Q a ∩ Q b).card ≤ 1)
    (hcost : ∀ a ∈ I, (Q a).card - 1 ≤
      (K.filter fun j => 2 ≤ (supp j).card ∧ supp j ⊆ Q a).card) :
    ∑ a ∈ I, ((Q a).card - 1) ≤ K.card := by
  let owned := fun a => K.filter fun j => 2 ≤ (supp j).card ∧ supp j ⊆ Q a
  have hdisj : (I : Set α).PairwiseDisjoint owned := by
    intro a ha b hb hab
    exact owned_support_disjoint Q K supp (hsep a ha b hb hab)
  calc
    ∑ a ∈ I, ((Q a).card - 1) ≤ ∑ a ∈ I, (owned a).card :=
      Finset.sum_le_sum (fun a ha => hcost a ha)
    _ = (I.biUnion owned).card := (Finset.card_biUnion hdisj).symm
    _ ≤ K.card := by
      apply Finset.card_le_card
      intro j hj
      obtain ⟨a, _, hja⟩ := Finset.mem_biUnion.mp hj
      exact (Finset.mem_filter.mp hja).1

def orGateIndices (C : PEqualNP.CircuitLowerBounds.Circuit) : Finset ℕ := by
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  exact (Finset.range C.gates.length).filter fun j =>
    (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op =
      PEqualNP.CircuitLowerBounds.GateOp.or

lemma cover_card_le_or_gates (p l : ℕ) (E : Finset (Fin p × Fin l))
    (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hC4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (hstar : ∀ (a : Fin p) (b : Fin l), (a, b) ∈ E →
      (∃ (j : ℕ) (Q : Finset (Fin l)), j < C.gates.length ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op =
          PEqualNP.CircuitLowerBounds.GateOp.or ∧
        2 ≤ Q.card ∧ b ∈ Q ∧ (∀ b' ∈ Q, (a, b') ∈ E) ∧
        ∀ x : Fin (p + l) → Bool,
          (C.wires (List.ofFn x)).getD (p + l + j) false =
            decide (∃ b' ∈ Q, x (Fin.natAdd p b') = true)) ∨
      (∃ (j : ℕ) (P : Finset (Fin p)), j < C.gates.length ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op =
          PEqualNP.CircuitLowerBounds.GateOp.or ∧
        2 ≤ P.card ∧ a ∈ P ∧ (∀ a' ∈ P, (a', b) ∈ E) ∧
        ∀ x : Fin (p + l) → Bool,
          (C.wires (List.ofFn x)).getD (p + l + j) false =
            decide (∃ a' ∈ P, x (Fin.castAdd l a') = true))) :
    ∃ S : Finset (Fin (p + l)),
      (∀ (a : Fin p) (b : Fin l), (a, b) ∈ E →
        Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      S.card ≤ (orGateIndices C).card := by
  classical
  apply cover_card_of_star_witnesses E hC4
    (orGateIndices C)
    (fun j x => (C.wires (List.ofFn x)).getD (p + l + j) false)
  intro a b hab
  rcases hstar a b hab with ⟨j, Q, hj, ho, hQ, hb, hE, hf⟩ |
    ⟨j, P, hj, ho, hP, ha, hE, hf⟩
  · have hj' : j ∈ orGateIndices C := by
      simp only [orGateIndices, Finset.mem_filter, Finset.mem_range]
      exact ⟨hj, ho⟩
    exact Or.inl ⟨j, hj', Q, hQ, hb, hE, hf⟩
  · have hj' : j ∈ orGateIndices C := by
      simp only [orGateIndices, Finset.mem_filter, Finset.mem_range]
      exact ⟨hj, ho⟩
    exact Or.inr ⟨j, hj', P, hP, ha, hE, hf⟩

end PEqualNP.Outside.L_meta_4970_aux
