import PEqualNP.Defs

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

lemma left_star_covered_by_other_centers_card_le {p l : ℕ}
    (E : Finset (Fin p × Fin l))
    (hcycle : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (a : Fin p) (Q : Finset (Fin l)) (A : Finset (Fin p))
    (hA : a ∉ A) (hQ : ∀ b ∈ Q, (a, b) ∈ E)
    (hcover : ∀ b ∈ Q, ∃ a' ∈ A, (a', b) ∈ E) : Q.card ≤ A.card := by
  classical
  let f : Q → A := fun b =>
    ⟨(hcover b b.property).choose, (hcover b b.property).choose_spec.1⟩
  have hf : ∀ b : Q, ((f b).val, b.val) ∈ E := by
    intro b
    exact (hcover b b.property).choose_spec.2
  apply Finset.card_le_card_of_injective (f := f)
  intro b b' heq
  apply Subtype.ext
  by_contra hne
  have ha : a ≠ (f b).val := by
    intro h
    exact hA (h.symm ▸ (f b).property)
  have hsame : (f b).val = (f b').val := congrArg Subtype.val heq
  exact hcycle a (f b).val b.val b'.val ha hne
    ⟨hQ b b.property, hQ b' b'.property, hf b, hsame.symm ▸ hf b'⟩

end PEqualNP.Outside.L_meta_4970
