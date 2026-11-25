import Mathlib

namespace PEqualNP.Outside.L_meta_4970

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

end PEqualNP.Outside.L_meta_4970
