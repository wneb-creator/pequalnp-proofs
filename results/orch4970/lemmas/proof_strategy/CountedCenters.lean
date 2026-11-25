import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4970_aux.StarCenters
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

variable {p l : ℕ}

def NoFour (E : Finset (Fin p × Fin l)) : Prop :=
  ∀ a a' b b', a ≠ a' → b ≠ b' →
    ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E)

def lineValue (Q : Finset (Fin l)) (x : Fin (p+l) → Bool) : Bool :=
  decide (∃ b ∈ Q, x (Fin.natAdd p b) = true)

def pointValue (P : Finset (Fin p)) (x : Fin (p+l) → Bool) : Bool :=
  decide (∃ a ∈ P, x (Fin.castAdd l a) = true)

lemma line_singleton (Q : Finset (Fin l)) (b : Fin l) :
    lineValue Q (fun i => decide (i = Fin.natAdd p b)) = decide (b ∈ Q) := by
  simp [lineValue]

lemma point_singleton (P : Finset (Fin p)) (a : Fin p) :
    pointValue P (fun i => decide (i = Fin.castAdd l a)) = decide (a ∈ P) := by
  simp [pointValue]

lemma opposite_singleton (P : Finset (Fin p)) (b : Fin l) :
    pointValue P (fun i => decide (i = Fin.natAdd p b)) = false := by
  apply decide_eq_false
  rintro ⟨a, _, h⟩
  have eq := of_decide_eq_true h
  have hv := congrArg Fin.val eq
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

def LineStar (E : Finset (Fin p × Fin l)) (C : Circuit) (j : ℕ)
    (a : Fin p) (Q : Finset (Fin l)) : Prop :=
  j < C.gates.length ∧ (gateAt C j).op = GateOp.or ∧ 2 ≤ Q.card ∧
    (∀ b ∈ Q, (a,b) ∈ E) ∧
    ∀ x : Fin (p+l) → Bool, (C.wires (List.ofFn x)).getD (p+l+j) false = lineValue Q x

def PointStar (E : Finset (Fin p × Fin l)) (C : Circuit) (j : ℕ)
    (b : Fin l) (P : Finset (Fin p)) : Prop :=
  j < C.gates.length ∧ (gateAt C j).op = GateOp.or ∧ 2 ≤ P.card ∧
    (∀ a ∈ P, (a,b) ∈ E) ∧
    ∀ x : Fin (p+l) → Bool, (C.wires (List.ofFn x)).getD (p+l+j) false = pointValue P x

lemma line_star_unique {E : Finset (Fin p × Fin l)} {C : Circuit} {j : ℕ}
    (noFour : NoFour E) {a a' : Fin p} {Q Q' : Finset (Fin l)}
    (h : LineStar E C j a Q) (h' : LineStar E C j a' Q') : a = a' := by
  have sub : Q ⊆ Q' := by
    intro b hb
    have eq := (h.2.2.2.2 (fun i => decide (i = Fin.natAdd p b))).symm.trans
      (h'.2.2.2.2 (fun i => decide (i = Fin.natAdd p b)))
    rw [line_singleton, line_singleton] at eq
    simpa [hb] using eq.symm
  have two : 2 ≤ Q.card := h.2.2.1
  obtain ⟨b, hb, b', hb', distinct⟩ := Finset.one_lt_card.mp (by omega : 1 < Q.card)
  by_contra ne
  exact noFour a a' b b' ne distinct
    ⟨h.2.2.2.1 b hb, h.2.2.2.1 b' hb', h'.2.2.2.1 b (sub hb), h'.2.2.2.1 b' (sub hb')⟩

lemma point_star_unique {E : Finset (Fin p × Fin l)} {C : Circuit} {j : ℕ}
    (noFour : NoFour E) {b b' : Fin l} {P P' : Finset (Fin p)}
    (h : PointStar E C j b P) (h' : PointStar E C j b' P') : b = b' := by
  have sub : P ⊆ P' := by
    intro a ha
    have eq := (h.2.2.2.2 (fun i => decide (i = Fin.castAdd l a))).symm.trans
      (h'.2.2.2.2 (fun i => decide (i = Fin.castAdd l a)))
    rw [point_singleton, point_singleton] at eq
    simpa [ha] using eq.symm
  have two : 2 ≤ P.card := h.2.2.1
  obtain ⟨a, ha, a', ha', distinct⟩ := Finset.one_lt_card.mp (by omega : 1 < P.card)
  by_contra ne
  exact noFour a a' b b' distinct ne
    ⟨h.2.2.2.1 a ha, h'.2.2.2.1 a (sub ha), h.2.2.2.1 a' ha', h'.2.2.2.1 a' (sub ha')⟩

lemma line_point_exclusive {E : Finset (Fin p × Fin l)} {C : Circuit} {j : ℕ}
    {a : Fin p} {b : Fin l} {Q : Finset (Fin l)} {P : Finset (Fin p)}
    (h : LineStar E C j a Q) (h' : PointStar E C j b P) : False := by
  have two : 2 ≤ Q.card := h.2.2.1
  have nonempty : Q.Nonempty := Finset.card_pos.mp (by omega : 0 < Q.card)
  obtain ⟨b', hb'⟩ := nonempty
  have eq := (h.2.2.2.2 (fun i => decide (i = Fin.natAdd p b'))).symm.trans
    (h'.2.2.2.2 (fun i => decide (i = Fin.natAdd p b')))
  rw [line_singleton, opposite_singleton] at eq
  simp [hb'] at eq

def Star (E : Finset (Fin p × Fin l)) (C : Circuit) (j : ℕ) (v : Fin (p+l)) : Prop :=
  (∃ a Q, v = Fin.castAdd l a ∧ LineStar E C j a Q) ∨
  (∃ b P, v = Fin.natAdd p b ∧ PointStar E C j b P)

lemma star_center_unique {E : Finset (Fin p × Fin l)} {C : Circuit} {j : ℕ}
    (noFour : NoFour E) {v w : Fin (p+l)} (h : Star E C j v) (h' : Star E C j w) : v = w := by
  rcases h with ⟨a,Q,rfl,h⟩ | ⟨b,P,rfl,h⟩ <;>
    rcases h' with ⟨a',Q',rfl,h'⟩ | ⟨b',P',rfl,h'⟩
  · rw [line_star_unique noFour h h']
  · exact False.elim (line_point_exclusive h h')
  · exact False.elim (line_point_exclusive h' h)
  · rw [point_star_unique noFour h h']

lemma common_lines_unique {E : Finset (Fin p × Fin l)} (noFour : NoFour E)
    {a a' : Fin p} {Q : Finset (Fin l)} (two : 2 ≤ Q.card)
    (left : ∀ b ∈ Q, (a,b) ∈ E) (right : ∀ b ∈ Q, (a',b) ∈ E) : a = a' := by
  obtain ⟨b, hb, b', hb', distinct⟩ := Finset.one_lt_card.mp (by omega : 1 < Q.card)
  by_contra ne
  exact noFour a a' b b' ne distinct ⟨left b hb, left b' hb', right b hb, right b' hb'⟩

lemma common_points_unique {E : Finset (Fin p × Fin l)} (noFour : NoFour E)
    {b b' : Fin l} {P : Finset (Fin p)} (two : 2 ≤ P.card)
    (left : ∀ a ∈ P, (a,b) ∈ E) (right : ∀ a ∈ P, (a,b') ∈ E) : b = b' := by
  obtain ⟨a, ha, a', ha', distinct⟩ := Finset.one_lt_card.mp (by omega : 1 < P.card)
  by_contra ne
  exact noFour a a' b b' distinct ne ⟨left a ha, right a ha, left a' ha', right a' ha'⟩

def isOr (g : Gate) : Bool := match g.op with | .or => true | _ => false

def orIndices (C : Circuit) : Finset ℕ :=
  (Finset.range C.gates.length).filter fun j => isOr (gateAt C j)

lemma star_or_index {E : Finset (Fin p × Fin l)} {C : Circuit} {j : ℕ} {v : Fin (p+l)}
    (h : Star E C j v) : j ∈ orIndices C := by
  rcases h with ⟨a,Q,_,h⟩ | ⟨b,P,_,h⟩
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr h.1, ?_⟩
    change isOr (gateAt C j) = true
    simp [isOr, h.2.1]
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr h.1, ?_⟩
    change isOr (gateAt C j) = true
    simp [isOr, h.2.1]

theorem star_cover_count {E : Finset (Fin p × Fin l)} {C : Circuit}
    (noFour : NoFour E)
    (served : ∀ a b, (a,b) ∈ E →
      (∃ j Q, LineStar E C j a Q ∧ b ∈ Q) ∨
      (∃ j P, PointStar E C j b P ∧ a ∈ P)) :
    ∃ S : Finset (Fin (p+l)),
      (∀ a b, (a,b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      S.card ≤ (orIndices C).card := by
  classical
  let S : Finset (Fin (p+l)) := Finset.univ.filter fun v => ∃ j, Star E C j v
  have witnesses (v : {v // v ∈ S}) : ∃ j ∈ orIndices C, Star E C j v.val := by
    obtain ⟨j, hj⟩ := (Finset.mem_filter.mp v.property).2
    exact ⟨j, star_or_index hj, hj⟩
  let pick : {v // v ∈ S} → {j // j ∈ orIndices C} := fun v =>
    ⟨Classical.choose (witnesses v), (Classical.choose_spec (witnesses v)).1⟩
  have spec (v : {v // v ∈ S}) : Star E C (pick v).val v.val :=
    (Classical.choose_spec (witnesses v)).2
  have injective : Function.Injective pick := by
    intro v w eq
    apply Subtype.ext
    have same : (pick v).val = (pick w).val := congrArg Subtype.val eq
    have hv := spec v
    rw [same] at hv
    exact star_center_unique noFour hv (spec w)
  refine ⟨S, ?_, ?_⟩
  · intro a b hab
    rcases served a b hab with ⟨j,Q,h,_⟩ | ⟨j,P,h,_⟩
    · left
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, Or.inl ⟨a,Q,rfl,h⟩⟩
    · right
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, Or.inr ⟨b,P,rfl,h⟩⟩
  · simpa using Fintype.card_le_of_injective pick injective

end PEqualNP.Outside.L_meta_4970_aux.StarCenters

namespace PEqualNP.Outside.L_meta_4970_aux.StarCenters
variable {p l : ℕ}

def neighbors (E : Finset (Fin p × Fin l)) : Fin p ⊕ Fin l → Finset (Fin (p+l))
  | Sum.inl a => ((Finset.univ : Finset (Fin l)).filter fun b => (a,b) ∈ E).image (Fin.natAdd p)
  | Sum.inr b => ((Finset.univ : Finset (Fin p)).filter fun a => (a,b) ∈ E).image (Fin.castAdd l)

lemma left_mem {E : Finset (Fin p × Fin l)} {a : Fin p} {v : Fin (p+l)}
    (h : v ∈ neighbors E (Sum.inl a)) : ∃ b : Fin l, (a,b) ∈ E ∧ Fin.natAdd p b = v := by
  simpa [neighbors] using h

lemma right_mem {E : Finset (Fin p × Fin l)} {b : Fin l} {v : Fin (p+l)}
    (h : v ∈ neighbors E (Sum.inr b)) : ∃ a : Fin p, (a,b) ∈ E ∧ Fin.castAdd l a = v := by
  simpa [neighbors] using h

lemma opposite_neighborhoods {E : Finset (Fin p × Fin l)} {a : Fin p} {b : Fin l}
    {v : Fin (p+l)} (h : v ∈ neighbors E (Sum.inl a))
    (h' : v ∈ neighbors E (Sum.inr b)) : False := by
  obtain ⟨b', _, hb⟩ := left_mem h
  obtain ⟨a', _, ha⟩ := right_mem h'
  have eq := congrArg Fin.val (hb.trans ha.symm)
  simp only [Fin.val_natAdd, Fin.val_castAdd] at eq
  omega

lemma neighbors_center_unique {E : Finset (Fin p × Fin l)} (noFour : NoFour E)
    {c c' : Fin p ⊕ Fin l} {u v : Fin (p+l)} (ne : u ≠ v)
    (hu : u ∈ neighbors E c) (hv : v ∈ neighbors E c)
    (hu' : u ∈ neighbors E c') (hv' : v ∈ neighbors E c') : c = c' := by
  cases c with
  | inl a =>
    cases c' with
    | inl a' =>
      obtain ⟨b, hab, rfl⟩ := left_mem hu
      obtain ⟨b', hab', rfl⟩ := left_mem hv
      obtain ⟨b0, ha'b0, hb0⟩ := left_mem hu'
      obtain ⟨b1, ha'b1, hb1⟩ := left_mem hv'
      have e0 : b0 = b := by simpa using hb0
      have e1 : b1 = b' := by simpa using hb1
      subst b0; subst b1
      have bb' : b ≠ b' := by intro eq; subst b'; exact ne rfl
      have aa' : a = a' := by
        by_contra neq
        exact noFour a a' b b' neq bb' ⟨hab,hab',ha'b0,ha'b1⟩
      rw [aa']
    | inr b => exact False.elim (opposite_neighborhoods hu hu')
  | inr b =>
    cases c' with
    | inl a => exact False.elim (opposite_neighborhoods hu' hu)
    | inr b' =>
      obtain ⟨a, hab, rfl⟩ := right_mem hu
      obtain ⟨a', ha'b, rfl⟩ := right_mem hv
      obtain ⟨a0, ha0b', ha0⟩ := right_mem hu'
      obtain ⟨a1, ha1b', ha1⟩ := right_mem hv'
      have e0 : a0 = a := by simpa using ha0
      have e1 : a1 = a' := by simpa using ha1
      subst a0; subst a1
      have aa' : a ≠ a' := by intro eq; subst a'; exact ne rfl
      have bb' : b = b' := by
        by_contra neq
        exact noFour a a' b b' aa' neq ⟨hab,ha0b',ha'b,ha1b'⟩
      rw [bb']

lemma neighbors_pairwise_linear {E : Finset (Fin p × Fin l)} (noFour : NoFour E)
    (c c' : Fin p ⊕ Fin l) (ne : c ≠ c') :
    (neighbors E c ∩ neighbors E c').card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro u hu v hv
  by_contra uv
  exact ne (neighbors_center_unique noFour uv
    (Finset.mem_inter.mp hu).1 (Finset.mem_inter.mp hv).1
    (Finset.mem_inter.mp hu).2 (Finset.mem_inter.mp hv).2)

def MonotoneBool {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true

def CountedFor {n : ℕ} (S : Finset (Fin n)) (f : (Fin n → Bool) → Bool) : Prop :=
  f (fun i => decide (i ∉ S)) = false ∧
    ∃ u v : Fin n, u ≠ v ∧ f (fun i => decide (i = u)) = true ∧
      f (fun i => decide (i = v)) = true

lemma accepted_singleton_mem {n : ℕ} {S : Finset (Fin n)}
    {f : (Fin n → Bool) → Bool} (mono : MonotoneBool f)
    (zero : f (fun i => decide (i ∉ S)) = false) {u : Fin n}
    (one : f (fun i => decide (i = u)) = true) : u ∈ S := by
  by_contra absent
  have value := mono (fun i => decide (i = u)) (fun i => decide (i ∉ S))
    (by intro i hi; have eq := of_decide_eq_true hi; subst i; simp [absent]) one
  rw [zero] at value
  cases value

lemma counted_center_unique {E : Finset (Fin p × Fin l)} (noFour : NoFour E)
    {c c' : Fin p ⊕ Fin l} {f : (Fin (p+l) → Bool) → Bool}
    (mono : MonotoneBool f) (h : CountedFor (neighbors E c) f)
    (h' : CountedFor (neighbors E c') f) : c = c' := by
  obtain ⟨u,v,ne,hu,hv⟩ := h.2
  exact neighbors_center_unique noFour ne
    (accepted_singleton_mem mono h.1 hu) (accepted_singleton_mem mono h.1 hv)
    (accepted_singleton_mem mono h'.1 hu) (accepted_singleton_mem mono h'.1 hv)

noncomputable def countedIndices (E : Finset (Fin p × Fin l)) (J : Finset ℕ)
    (f : ℕ → (Fin (p+l) → Bool) → Bool) (c : Fin p ⊕ Fin l) : Finset ℕ := by
  classical
  exact J.filter fun j => CountedFor (neighbors E c) (f j)

lemma counted_disjoint {E : Finset (Fin p × Fin l)} (noFour : NoFour E)
    (J : Finset ℕ) (f : ℕ → (Fin (p+l) → Bool) → Bool)
    (mono : ∀ j ∈ J, MonotoneBool (f j)) (c c' : Fin p ⊕ Fin l) (ne : c ≠ c') :
    Disjoint (countedIndices E J f c) (countedIndices E J f c') := by
  classical
  apply Finset.disjoint_left.mpr
  intro j hj hj'
  have h := Finset.mem_filter.mp hj
  have h' := Finset.mem_filter.mp hj'
  exact ne (counted_center_unique noFour (mono j h.1) h.2 h'.2)

lemma total_counted_le {E : Finset (Fin p × Fin l)} (noFour : NoFour E)
    (J : Finset ℕ) (f : ℕ → (Fin (p+l) → Bool) → Bool)
    (mono : ∀ j ∈ J, MonotoneBool (f j)) :
    ∑ c : Fin p ⊕ Fin l, (countedIndices E J f c).card ≤ J.card := by
  classical
  have disj : ∀ a ∈ (Finset.univ : Finset (Fin p ⊕ Fin l)),
      ∀ b ∈ (Finset.univ : Finset (Fin p ⊕ Fin l)), a ≠ b →
        Disjoint (countedIndices E J f a) (countedIndices E J f b) := by
    intro a _ b _ ne
    exact counted_disjoint noFour J f mono a b ne
  rw [← Finset.card_biUnion disj]
  apply Finset.card_le_card
  intro j hj
  obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.mp hj
  exact (Finset.mem_filter.mp hc).1

end PEqualNP.Outside.L_meta_4970_aux.StarCenters
