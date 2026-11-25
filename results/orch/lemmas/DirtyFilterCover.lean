import Mathlib.Init

namespace PEqualNP.Outside.L_meta_2732_aux

lemma safeRows_unique {α β : Type} (R : α → β → Prop)
    (A : α → Prop) (B : β → Prop) (S : α → Prop) (T : β → Prop)
    (free : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ (R a b ∧ R a b' ∧ R a' b ∧ R a' b'))
    (safe : ∀ a b, A a → B b → (S a ∨ T b) → R a b)
    (b b' : β) (hb : B b) (hb' : B b') (hne : b ≠ b')
    (a a' : α) (ha : A a) (ha' : A a') (hs : S a) (hs' : S a') :
    a = a' := by
  apply Classical.byContradiction
  intro haa
  exact free a a' b b' haa hne
    ⟨safe a b ha hb (Or.inl hs), safe a b' ha hb' (Or.inl hs),
      safe a' b ha' hb (Or.inl hs'), safe a' b' ha' hb' (Or.inl hs')⟩

lemma safeColumns_unique {α β : Type} (R : α → β → Prop)
    (A : α → Prop) (B : β → Prop) (S : α → Prop) (T : β → Prop)
    (free : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ (R a b ∧ R a b' ∧ R a' b ∧ R a' b'))
    (safe : ∀ a b, A a → B b → (S a ∨ T b) → R a b)
    (a a' : α) (ha : A a) (ha' : A a') (hne : a ≠ a')
    (b b' : β) (hb : B b) (hb' : B b') (ht : T b) (ht' : T b') :
    b = b' := by
  apply Classical.byContradiction
  intro hbb
  exact free a a' b b' hne hbb
    ⟨safe a b ha hb (Or.inr ht), safe a b' ha hb' (Or.inr ht'),
      safe a' b ha' hb (Or.inr ht), safe a' b' ha' hb' (Or.inr ht')⟩

lemma safeFilter_doubleStar {α β : Type} (R : α → β → Prop)
    (A : α → Prop) (B : β → Prop) (S : α → Prop) (T : β → Prop)
    (free : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ (R a b ∧ R a b' ∧ R a' b ∧ R a' b'))
    (safe : ∀ a b, A a → B b → (S a ∨ T b) → R a b)
    (a₀ a₁ : α) (ha₀ : A a₀) (ha₁ : A a₁) (ha : a₀ ≠ a₁)
    (b₀ b₁ : β) (hb₀ : B b₀) (hb₁ : B b₁) (hb : b₀ ≠ b₁) :
    ∃ p q, A p ∧ B q ∧
      ∀ a b, A a → B b → (S a ∨ T b) → a = p ∨ b = q := by
  have row : ∃ p, A p ∧ ∀ a, A a → S a → a = p := by
    by_cases h : ∃ p, A p ∧ S p
    · obtain ⟨p, hp, hs⟩ := h
      exact ⟨p, hp, fun a ha hs' =>
        safeRows_unique R A B S T free safe b₀ b₁ hb₀ hb₁ hb a p ha hp hs' hs⟩
    · exact ⟨a₀, ha₀, fun a ha hs => False.elim (h ⟨a, ha, hs⟩)⟩
  have col : ∃ q, B q ∧ ∀ b, B b → T b → b = q := by
    by_cases h : ∃ q, B q ∧ T q
    · obtain ⟨q, hq, ht⟩ := h
      exact ⟨q, hq, fun b hb ht' =>
        safeColumns_unique R A B S T free safe a₀ a₁ ha₀ ha₁ ha b q hb hq ht' ht⟩
    · exact ⟨b₀, hb₀, fun b hb ht => False.elim (h ⟨b, hb, ht⟩)⟩
  obtain ⟨p, hp, hrow⟩ := row
  obtain ⟨q, hq, hcol⟩ := col
  exact ⟨p, q, hp, hq, fun a b ha hb h =>
    h.elim (fun hs => Or.inl (hrow a ha hs)) (fun ht => Or.inr (hcol b hb ht))⟩

end PEqualNP.Outside.L_meta_2732_aux


namespace PEqualNP.Outside.L_meta_2732_aux

lemma commonFilter_center {α : Type} (R : α → α → Prop)
    (A B S : α → Prop)
    (symm : ∀ u v, R u v → R v u)
    (free : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ (R a b ∧ R a b' ∧ R a' b ∧ R a' b'))
    (safe : ∀ u v, (A u ∨ A v) → (B u ∨ B v) → (S u ∨ S v) → R u v)
    (i : α) (hiA : A i) (hiB : B i) (p : α) (hp : S p)
    (cross : ∀ u v, (A u ∨ A v) → (B u ∨ B v) → S u → v ≠ i → R p v) :
    ∀ u v, (A u ∨ A v) → (B u ∨ B v) → (S u ∨ S v) →
      u = i ∨ v = i ∨ u = p ∨ v = p := by
  have common : ∀ s, S s → R s i := fun s hs =>
    symm i s (safe i s (Or.inl hiA) (Or.inl hiB) (Or.inr hs))
  have same : ∀ u v, (A u ∨ A v) → (B u ∨ B v) → S u → v ≠ i → u = p := by
    intro u v ha hb hu hv
    apply Classical.byContradiction
    intro hup
    exact free u p i v hup (fun h => hv h.symm)
      ⟨common u hu, safe u v ha hb (Or.inl hu), common p hp,
        cross u v ha hb hu hv⟩
  intro u v ha hb hs
  cases hs with
  | inl hu =>
      by_cases hv : v = i
      · exact Or.inr (Or.inl hv)
      · exact Or.inr (Or.inr (Or.inl (same u v ha hb hu hv)))
  | inr hv =>
      by_cases hu : u = i
      · exact Or.inl hu
      · exact Or.inr (Or.inr (Or.inr
          (same v u (ha.elim Or.inr Or.inl) (hb.elim Or.inr Or.inl) hv hu)))

lemma commonFilter_twoStars {α : Type} (R : α → α → Prop)
    (A B S : α → Prop)
    (symm : ∀ u v, R u v → R v u)
    (triangle : ∀ u v w, R u v → R v w → ¬ R u w)
    (free : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ (R a b ∧ R a b' ∧ R a' b ∧ R a' b'))
    (safe : ∀ u v, (A u ∨ A v) → (B u ∨ B v) → (S u ∨ S v) → R u v)
    (i : α) (hiA : A i) (hiB : B i) :
    ∃ p, ∀ u v, (A u ∨ A v) → (B u ∨ B v) → (S u ∨ S v) →
      u = i ∨ v = i ∨ u = p ∨ v = p := by
  have common : ∀ s, S s → R i s := fun s hs =>
    safe i s (Or.inl hiA) (Or.inl hiB) (Or.inr hs)
  by_cases hA : ∃ p, A p ∧ S p
  · obtain ⟨p, hpA, hpS⟩ := hA
    refine ⟨p, commonFilter_center R A B S symm free safe i hiA hiB p hpS ?_⟩
    intro u v _ hb hu _
    have hnu : ¬ B u := by
      intro hbu
      exact triangle i p u (common p hpS)
        (safe p u (Or.inl hpA) (Or.inr hbu) (Or.inl hpS)) (common u hu)
    exact safe p v (Or.inl hpA) (Or.inr (hb.resolve_left hnu)) (Or.inl hpS)
  · by_cases hB : ∃ p, B p ∧ S p
    · obtain ⟨p, hpB, hpS⟩ := hB
      refine ⟨p, commonFilter_center R A B S symm free safe i hiA hiB p hpS ?_⟩
      intro u v ha _ hu _
      have hnu : ¬ A u := fun hau => hA ⟨u, hau, hu⟩
      exact safe p v (Or.inr (ha.resolve_left hnu)) (Or.inl hpB) (Or.inl hpS)
    · by_cases hS : ∃ p, S p
      · obtain ⟨p, hpS⟩ := hS
        refine ⟨p, commonFilter_center R A B S symm free safe i hiA hiB p hpS ?_⟩
        intro u v ha hb hu _
        have hna : ¬ A u := fun hau => hA ⟨u, hau, hu⟩
        have hnb : ¬ B u := fun hbu => hB ⟨u, hbu, hu⟩
        exact safe p v (Or.inr (ha.resolve_left hna))
          (Or.inr (hb.resolve_left hnb)) (Or.inl hpS)
      · refine ⟨i, ?_⟩
        intro u v _ _ hs
        exact hs.elim (fun hu => False.elim (hS ⟨u, hu⟩))
          (fun hv => False.elim (hS ⟨v, hv⟩))

end PEqualNP.Outside.L_meta_2732_aux

namespace PEqualNP.Outside.L_meta_2732_aux

lemma safeFilter_coverTwo {α : Type} (R : α → α → Prop)
    (A B S : α → Prop) (z : α)
    (symm : ∀ u v, R u v → R v u)
    (triangle : ∀ u v w, R u v → R v w → ¬ R u w)
    (free : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ (R a b ∧ R a b' ∧ R a' b ∧ R a' b'))
    (safe : ∀ u v, (A u ∨ A v) → (B u ∨ B v) → (S u ∨ S v) → R u v) :
    ∃ p q, ∀ u v, (A u ∨ A v) → (B u ∨ B v) → (S u ∨ S v) →
      u = p ∨ v = p ∨ u = q ∨ v = q := by
  by_cases hA : ∃ a, A a
  · obtain ⟨a₀, ha₀⟩ := hA
    by_cases hB : ∃ b, B b
    · obtain ⟨b₀, hb₀⟩ := hB
      by_cases hI : ∃ i, A i ∧ B i
      · obtain ⟨i, hiA, hiB⟩ := hI
        obtain ⟨p, hp⟩ := commonFilter_twoStars R A B S symm triangle free safe i hiA hiB
        exact ⟨i, p, hp⟩
      · by_cases hA₂ : ∃ a₁, A a₁ ∧ a₁ ≠ a₀
        · obtain ⟨a₁, ha₁, hna⟩ := hA₂
          by_cases hB₂ : ∃ b₁, B b₁ ∧ b₁ ≠ b₀
          · obtain ⟨b₁, hb₁, hnb⟩ := hB₂
            have cross : ∀ a b, A a → B b → (S a ∨ S b) → R a b := by
              intro a b ha hb hs
              exact safe a b (Or.inl ha) (Or.inr hb) hs
            obtain ⟨p, q, _, _, hpq⟩ := safeFilter_doubleStar R A B S S free cross
              a₀ a₁ ha₀ ha₁ (fun h => hna h.symm)
              b₀ b₁ hb₀ hb₁ (fun h => hnb h.symm)
            refine ⟨p, q, ?_⟩
            intro u v ha hb hs
            cases ha with
            | inl hau =>
                cases hb with
                | inl hbu => exact False.elim (hI ⟨u, hau, hbu⟩)
                | inr hbv =>
                    exact (hpq u v hau hbv hs).elim Or.inl
                      (fun h => Or.inr (Or.inr (Or.inr h)))
            | inr hav =>
                cases hb with
                | inl hbu =>
                    exact (hpq v u hav hbu (hs.elim Or.inr Or.inl)).elim
                      (fun h => Or.inr (Or.inl h))
                      (fun h => Or.inr (Or.inr (Or.inl h)))
                | inr hbv => exact False.elim (hI ⟨v, hav, hbv⟩)
          · have unique : ∀ b, B b → b = b₀ := by
              intro b hb
              apply Classical.byContradiction
              intro h
              exact hB₂ ⟨b, hb, h⟩
            exact ⟨b₀, z, fun u v _ hb _ => hb.elim
              (fun h => Or.inl (unique u h))
              (fun h => Or.inr (Or.inl (unique v h)))⟩
        · have unique : ∀ a, A a → a = a₀ := by
            intro a ha
            apply Classical.byContradiction
            intro h
            exact hA₂ ⟨a, ha, h⟩
          exact ⟨a₀, z, fun u v ha _ _ => ha.elim
            (fun h => Or.inl (unique u h))
            (fun h => Or.inr (Or.inl (unique v h)))⟩
    · exact ⟨z, z, fun u v _ hb _ => hb.elim
        (fun h => False.elim (hB ⟨u, h⟩)) (fun h => False.elim (hB ⟨v, h⟩))⟩
  · exact ⟨z, z, fun u v ha _ _ => ha.elim
      (fun h => False.elim (hA ⟨u, h⟩)) (fun h => False.elim (hA ⟨v, h⟩))⟩

end PEqualNP.Outside.L_meta_2732_aux
