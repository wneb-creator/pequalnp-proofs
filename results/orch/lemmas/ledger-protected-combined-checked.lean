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

def branching_and (g : Gate) : Bool :=
  match g.op with
  | GateOp.and => decide (2 ≤ g.inputs.length)
  | _ => false

def and_count (C : Circuit) (k : ℕ) : ℕ :=
  (C.gates.take k).countP branching_and

lemma and_count_succ (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    and_count C (k + 1) = and_count C k + (if branching_and (gateAt C k) then 1 else 0) := by
  unfold and_count
  rw [List.take_succ, List.countP_append, List.getElem?_eq_getElem hk]
  simp only [Option.toList_some, List.countP_singleton, output_gateAt_eq hk]

lemma true_gate_frontier (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ)
    (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    (hb : ∀ i ∈ (gateAt C k).inputs, i < n + k)
    (hl : (gateAt C k).inputs.length ≤ 2)
    (hv : boundary_W n C x (n + k) = true) :
    ∃ J : Finset ℕ,
      J.card ≤ (if branching_and (gateAt C k) then 1 else 0) + 1 ∧
      (∀ i ∈ J, i < n + k) ∧ (∀ i ∈ J, boundary_W n C x i = true) ∧
      ∀ y : Fin n → Bool, (∀ i ∈ J, boundary_W n C y i = true) →
        boundary_W n C y (n + k) = true := by
  rcases hop with ha | ho
  · refine ⟨(gateAt C k).inputs.toFinset, ?_, ?_, ?_, ?_⟩
    · by_cases htwo : 2 ≤ (gateAt C k).inputs.length
      · simpa [branching_and, ha, htwo] using (List.toFinset_card_le _).trans hl
      · have hsmall : (gateAt C k).inputs.length ≤ 1 := by omega
        simpa [branching_and, ha, htwo] using (List.toFinset_card_le _).trans hsmall
    · intro i hi
      exact hb i (List.mem_toFinset.mp hi)
    · rw [boundary_W_gate n C x k hk, ha] at hv
      simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq] at hv
      intro i hi
      have hit := List.mem_toFinset.mp hi
      simpa [hb i hit] using hv i hit
    · intro y hy
      rw [boundary_W_gate n C y k hk, ha]
      simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
      intro i hi
      simpa [hb i hi] using hy i (List.mem_toFinset.mpr hi)
  · rw [boundary_W_gate n C x k hk, ho] at hv
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hv
    obtain ⟨i, hi, hv⟩ := hv
    have hiv : boundary_W n C x i = true := by simpa [hb i hi] using hv
    refine ⟨{i}, by simp [branching_and, ho], ?_, ?_, ?_⟩
    · intro j hj
      simpa using (Finset.mem_singleton.mp hj ▸ hb i hi)
    · intro j hj
      simpa using (Finset.mem_singleton.mp hj ▸ hiv)
    · intro y hy
      exact boundary_W_or n C y k hk ho i hi (hb i hi) (hy i (by simp))

lemma true_frontier_certificate (n : ℕ) (C : Circuit)
    (hAO : PEqualNP.EdgeOwnership.AndOrOnly C) (hback : ReadsBack n C)
    (hfanin : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (x : Fin n → Bool) :
    ∀ k, k ≤ C.gates.length → ∀ R : Finset ℕ,
      (∀ w ∈ R, w < n + k) → (∀ w ∈ R, boundary_W n C x w = true) →
      ∃ S : Finset (Fin n), (∀ i ∈ S, x i = true) ∧
        (∀ y : Fin n → Bool, (∀ i ∈ S, y i = true) →
          ∀ w ∈ R, boundary_W n C y w = true) ∧
        S.card ≤ and_count C k + R.card := by
  intro k
  induction k with
  | zero =>
    intro _ R hR ht
    let S : Finset (Fin n) := Finset.univ.filter fun i => i.val ∈ R
    refine ⟨S, ?_, ?_, ?_⟩
    · intro i hi
      have hv := ht i.val ((Finset.mem_filter.mp hi).2)
      rw [boundary_W_input n C x i.val i.isLt] at hv
      exact hv
    · intro y hy w hw
      have hwn : w < n := by simpa using hR w hw
      rw [boundary_W_input n C y w hwn]
      apply hy ⟨w, hwn⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
    · have hsub : S.image Fin.val ⊆ R := by
        intro w hw
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
        exact (Finset.mem_filter.mp hi).2
      have hc := Finset.card_le_card hsub
      rw [Finset.card_image_of_injective S Fin.val_injective] at hc
      simpa [and_count] using hc
  | succ k ih =>
    intro hk R hR ht
    have hkl : k < C.gates.length := by omega
    have hcount := and_count_succ C k hkl
    by_cases hm : n + k ∈ R
    · have hgmem := output_gateAt_mem hkl
      obtain ⟨J, hJc, hJb, hJt, hJforce⟩ := true_gate_frontier n C x k hkl
        (hAO _ hgmem) (hback k hkl) (hfanin _ hgmem) (ht (n + k) hm)
      let R' : Finset ℕ := J ∪ R.erase (n + k)
      have hR'b : ∀ w ∈ R', w < n + k := by
        intro w hw
        rcases Finset.mem_union.mp hw with h | h
        · exact hJb w h
        · have hwR := Finset.mem_of_mem_erase h
          have hne := Finset.ne_of_mem_erase h
          have hb := hR w hwR
          omega
      have hR't : ∀ w ∈ R', boundary_W n C x w = true := by
        intro w hw
        rcases Finset.mem_union.mp hw with h | h
        · exact hJt w h
        · exact ht w (Finset.mem_of_mem_erase h)
      obtain ⟨S, hSt, hSf, hSc⟩ := ih (by omega) R' hR'b hR't
      refine ⟨S, hSt, ?_, ?_⟩
      · intro y hy w hw
        by_cases hwm : w = n + k
        · subst w
          apply hJforce y
          intro i hi
          exact hSf y hy i (Finset.mem_union.mpr (Or.inl hi))
        · exact hSf y hy w (Finset.mem_union.mpr
            (Or.inr (Finset.mem_erase.mpr ⟨hwm, hw⟩)))
      · have hR'c : R'.card ≤ J.card + (R.erase (n + k)).card := Finset.card_union_le _ _
        have hRc := Finset.card_erase_add_one hm
        omega
    · have hR0 : ∀ w ∈ R, w < n + k := by
        intro w hw
        have hb := hR w hw
        have hne : w ≠ n + k := by intro h; exact hm (h ▸ hw)
        omega
      obtain ⟨S, hSt, hSf, hSc⟩ := ih (by omega) R hR0 ht
      exact ⟨S, hSt, hSf, by omega⟩

lemma true_input_certificate (n : ℕ) (C : Circuit)
    (hAO : PEqualNP.EdgeOwnership.AndOrOnly C) (hback : ReadsBack n C)
    (hfanin : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (x : Fin n → Bool)
    (hx : PEqualNP.MetaComplexity.circuitFun n C x = true) :
    ∃ S : Finset (Fin n), (∀ i ∈ S, x i = true) ∧
      (∀ y : Fin n → Bool, (∀ i ∈ S, y i = true) →
        PEqualNP.MetaComplexity.circuitFun n C y = true) ∧
      S.card ≤ C.gates.countP branching_and + 1 := by
  have hval : boundary_W n C x C.output = true := hx
  have hout : C.output < n + C.gates.length := by
    by_contra h
    have hz : boundary_W n C x C.output = false := by
      apply boundary_getD_ge_length
      rw [boundary_wires_length]
      omega
    rw [hz] at hval
    contradiction
  obtain ⟨S, hS, hforce, hcard⟩ := true_frontier_certificate n C hAO hback hfanin x
    C.gates.length le_rfl {C.output} (by simpa using hout) (by simpa using hval)
  refine ⟨S, hS, ?_, ?_⟩
  · intro y hy
    exact hforce y hy C.output (by simp)
  · simpa [and_count] using hcard

end PEqualNP.Outside.L_meta_4970.AndBudget

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
