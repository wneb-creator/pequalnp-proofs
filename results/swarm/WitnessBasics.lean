import Mathlib

namespace PEqualNP.Outside.L_meta_4970_aux

variable {α β : Type*} [Fintype α] [DecidableEq α]

def singletonInput (a : α) : α → Bool := fun i => decide (i = a)

def outsideInput (Q : Finset α) : α → Bool := fun i => decide (i ∉ Q)

def orFunction (Q : Finset α) (x : α → Bool) : Bool :=
  decide (∃ a ∈ Q, x a = true)

def BoolMonotone (f : (α → Bool) → Bool) : Prop :=
  ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true

def singletonSupport (f : (α → Bool) → Bool) : Finset α :=
  Finset.univ.filter fun a => f (singletonInput a) = true

lemma orFunction_outside (Q : Finset α) : orFunction Q (outsideInput Q) = false := by
  simp [orFunction, outsideInput]

lemma orFunction_singleton {Q : Finset α} {a : α} (ha : a ∈ Q) :
    orFunction Q (singletonInput a) = true := by
  simp [orFunction, singletonInput, ha]

lemma singletonSupport_mem (f : (α → Bool) → Bool) (a : α) :
    a ∈ singletonSupport f ↔ f (singletonInput a) = true := by
  simp [singletonSupport]

lemma singletonSupport_subset_of_usable {f : (α → Bool) → Bool}
    (hf : BoolMonotone f) {Q : Finset α} (hQ : f (outsideInput Q) = false) :
    singletonSupport f ⊆ Q := by
  intro a ha
  by_contra hn
  have hv := (singletonSupport_mem f a).1 ha
  have ht : f (outsideInput Q) = true := hf _ _ (by
    intro i hi
    have he : i = a := by simpa [singletonInput] using hi
    subst i
    simp [outsideInput, hn]) hv
  simp_all

lemma eq_orFunction_of_usable_singletons {f : (α → Bool) → Bool}
    (hf : BoolMonotone f) {Q : Finset α} (hQ : f (outsideInput Q) = false)
    (hs : ∀ a ∈ Q, f (singletonInput a) = true) : f = orFunction Q := by
  funext x
  by_cases hx : ∃ a ∈ Q, x a = true
  · obtain ⟨a, ha, hax⟩ := hx
    have ht : f x = true := hf _ _ (by
      intro i hi
      have he : i = a := by simpa [singletonInput] using hi
      subst i
      exact hax) (hs a ha)
    have htarget : orFunction Q x = true := by
      exact decide_eq_true ⟨a, ha, hax⟩
    exact ht.trans htarget.symm
  · have hxQ : ∀ i, x i = true → outsideInput Q i = true := by
      intro i hi
      have hn : i ∉ Q := fun h => hx ⟨i, h, hi⟩
      simp [outsideInput, hn]
    have hv : f x = false := by
      cases hh : f x
      · rfl
      · have ht := hf _ _ hxQ hh
        simp_all
    simp [orFunction, hx, hv]

lemma usable_and {f g : (α → Bool) → Bool} {Q : Finset α}
    (h : (f (outsideInput Q) && g (outsideInput Q)) = false) :
    f (outsideInput Q) = false ∨ g (outsideInput Q) = false := by
  cases hf : f (outsideInput Q) <;> cases hg : g (outsideInput Q) <;> simp_all

lemma usable_or {f g : (α → Bool) → Bool} {Q : Finset α}
    (h : (f (outsideInput Q) || g (outsideInput Q)) = false) :
    f (outsideInput Q) = false ∧ g (outsideInput Q) = false := by
  cases hf : f (outsideInput Q) <;> cases hg : g (outsideInput Q) <;> simp_all

lemma and_eq_orFunction_bypass {f g : (α → Bool) → Bool}
    (hf : BoolMonotone f) (hg : BoolMonotone g) (Q : Finset α)
    (h : ∀ x, (f x && g x) = orFunction Q x) :
    f = orFunction Q ∨ g = orFunction Q := by
  have ho : (f (outsideInput Q) && g (outsideInput Q)) = false := by
    rw [h, orFunction_outside]
  have hs : ∀ a ∈ Q, f (singletonInput a) = true ∧ g (singletonInput a) = true := by
    intro a ha
    have hv := h (singletonInput a)
    rw [orFunction_singleton ha] at hv
    simpa using hv
  rcases usable_and ho with hfo | hgo
  · exact Or.inl (eq_orFunction_of_usable_singletons hf hfo (fun a ha => (hs a ha).1))
  · exact Or.inr (eq_orFunction_of_usable_singletons hg hgo (fun a ha => (hs a ha).2))

lemma singletonSupport_and (f g : (α → Bool) → Bool) :
    singletonSupport (fun x => f x && g x) = singletonSupport f ∩ singletonSupport g := by
  ext a
  simp [singletonSupport]

lemma singletonSupport_or (f g : (α → Bool) → Bool) :
    singletonSupport (fun x => f x || g x) = singletonSupport f ∪ singletonSupport g := by
  ext a
  simp [singletonSupport]

lemma usable_singletonSupport_inter {f : (α → Bool) → Bool}
    (hf : BoolMonotone f) {Q R : Finset α}
    (hQ : f (outsideInput Q) = false) (hR : f (outsideInput R) = false) :
    singletonSupport f ⊆ Q ∩ R := by
  intro a ha
  exact Finset.mem_inter.mpr
    ⟨singletonSupport_subset_of_usable hf hQ ha, singletonSupport_subset_of_usable hf hR ha⟩

lemma star_center_unique [DecidableEq β] (E : Finset (α × β))
    (hE : ∀ (a a' : α) (b b' : β), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {a a' : α} (Q : Finset β) (hQ : 2 ≤ Q.card)
    (ha : ∀ b ∈ Q, (a, b) ∈ E) (ha' : ∀ b ∈ Q, (a', b) ∈ E) : a = a' := by
  by_contra hne
  obtain ⟨b, hb, b', hb', hbb⟩ := Finset.one_lt_card.mp (show 1 < Q.card by omega)
  exact hE a a' b b' hne hbb ⟨ha b hb, ha b' hb', ha' b hb, ha' b' hb'⟩

lemma star_common_subset_card [DecidableEq β] (E : Finset (α × β))
    (hE : ∀ (a a' : α) (b b' : β), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {a a' : α} (hne : a ≠ a') (Q : Finset β)
    (ha : ∀ b ∈ Q, (a, b) ∈ E) (ha' : ∀ b ∈ Q, (a', b) ∈ E) : Q.card ≤ 1 := by
  by_contra h
  exact hne (star_center_unique E hE Q (by omega) ha ha')

lemma usable_large_support_center_unique [Fintype β] [DecidableEq β]
    (E : Finset (α × β))
    (hE : ∀ (a a' : α) (b b' : β), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {f : (β → Bool) → Bool} (hf : BoolMonotone f)
    (hcard : 2 ≤ (singletonSupport f).card) {a a' : α} {Q R : Finset β}
    (hQ : f (outsideInput Q) = false) (hR : f (outsideInput R) = false)
    (ha : ∀ b ∈ Q, (a, b) ∈ E) (ha' : ∀ b ∈ R, (a', b) ∈ E) : a = a' := by
  apply star_center_unique E hE (singletonSupport f) hcard
  · intro b hb
    exact ha b (singletonSupport_subset_of_usable hf hQ hb)
  · intro b hb
    exact ha' b (singletonSupport_subset_of_usable hf hR hb)

lemma usable_disjoint_support_empty {f : (α → Bool) → Bool}
    (hf : BoolMonotone f) {Q R : Finset α}
    (hQ : f (outsideInput Q) = false) (hR : f (outsideInput R) = false)
    (hd : Disjoint Q R) : singletonSupport f = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  exact Finset.disjoint_left.mp hd (singletonSupport_subset_of_usable hf hQ ha)
    (singletonSupport_subset_of_usable hf hR ha)

lemma BoolMonotone_input (a : α) : BoolMonotone (fun x => x a) := by
  intro x y hxy hx
  exact hxy a hx

lemma BoolMonotone_and {f g : (α → Bool) → Bool}
    (hf : BoolMonotone f) (hg : BoolMonotone g) : BoolMonotone (fun x => f x && g x) := by
  intro x y hxy hx
  have hh : f x = true ∧ g x = true := by simpa using hx
  simp [hf x y hxy hh.1, hg x y hxy hh.2]

lemma BoolMonotone_or {f g : (α → Bool) → Bool}
    (hf : BoolMonotone f) (hg : BoolMonotone g) : BoolMonotone (fun x => f x || g x) := by
  intro x y hxy hx
  have hh : f x = true ∨ g x = true := by simpa using hx
  rcases hh with hh | hh
  · simp [hf x y hxy hh]
  · simp [hg x y hxy hh]

end PEqualNP.Outside.L_meta_4970_aux
