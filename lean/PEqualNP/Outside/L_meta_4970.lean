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

end PEqualNP.Outside.L_meta_4970_aux
