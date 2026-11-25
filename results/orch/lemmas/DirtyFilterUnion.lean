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

lemma tripleFilter_cross {α : Type} (A B S : α → Prop) (a b c d : α)
    (habA : A a ∨ A b) (habB : B a ∨ B b) (habS : S a ∨ S b)
    (hcdA : A c ∨ A d) (hcdB : B c ∨ B d) (hcdS : S c ∨ S d) :
    ((A a ∨ A c) ∧ (B a ∨ B c) ∧ (S a ∨ S c)) ∨
    ((A a ∨ A d) ∧ (B a ∨ B d) ∧ (S a ∨ S d)) ∨
    ((A b ∨ A c) ∧ (B b ∨ B c) ∧ (S b ∨ S c)) ∨
    ((A b ∨ A d) ∧ (B b ∨ B d) ∧ (S b ∨ S d)) := by
  cases habA <;> cases habB <;> cases habS <;>
    cases hcdA <;> cases hcdB <;> cases hcdS <;>
    first
    | exact Or.inl ⟨(by first | exact Or.inl ‹A a› | exact Or.inr ‹A c›), (by first | exact Or.inl ‹B a› | exact Or.inr ‹B c›), (by first | exact Or.inl ‹S a› | exact Or.inr ‹S c›)⟩
    | exact (fun h => Or.inr (Or.inl h)) ⟨(by first | exact Or.inl ‹A a› | exact Or.inr ‹A d›), (by first | exact Or.inl ‹B a› | exact Or.inr ‹B d›), (by first | exact Or.inl ‹S a› | exact Or.inr ‹S d›)⟩
    | exact (fun h => Or.inr (Or.inr (Or.inl h))) ⟨(by first | exact Or.inl ‹A b› | exact Or.inr ‹A c›), (by first | exact Or.inl ‹B b› | exact Or.inr ‹B c›), (by first | exact Or.inl ‹S b› | exact Or.inr ‹S c›)⟩
    | exact (fun h => Or.inr (Or.inr (Or.inr h))) ⟨(by first | exact Or.inl ‹A b› | exact Or.inr ‹A d›), (by first | exact Or.inl ‹B b› | exact Or.inr ‹B d›), (by first | exact Or.inl ‹S b› | exact Or.inr ‹S d›)⟩

lemma twoCover_oneSmall {α : Type} (R : α → α → Prop)
    (symm : ∀ u v, R u v → R v u)
    (irrefl : ∀ u, ¬ R u u)
    (free : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ (R a b ∧ R a b' ∧ R a' b ∧ R a' b'))
    (cross : ∀ a b c d, R a b → R c d →
      R a c ∨ R a d ∨ R b c ∨ R b d)
    (p q : α) (hpq : p ≠ q) (hnpq : ¬ R p q)
    (cover : ∀ u v, R u v → u = p ∨ v = p ∨ u = q ∨ v = q) :
    (∀ a b, R p a → R p b → a = b) ∨
    (∀ a b, R q a → R q b → a = b) := by
  have cross' : ∀ a c, R p a → R q c → R p c ∨ R q a := by
    intro a c hpa hqc
    have hanp : a ≠ p := fun h => irrefl p (h ▸ hpa)
    have hanq : a ≠ q := fun h => hnpq (h ▸ hpa)
    have hcnp : c ≠ p := fun h => hnpq (symm q p (h ▸ hqc))
    have hcnq : c ≠ q := fun h => irrefl q (h ▸ hqc)
    have hnac : ¬ R a c := by
      intro hac
      rcases cover a c hac with h | h | h | h
      · exact hanp h
      · exact hcnp h
      · exact hanq h
      · exact hcnq h
    rcases cross p a q c hpa hqc with h | h | h | h
    · exact False.elim (hnpq h)
    · exact Or.inl h
    · exact Or.inr (symm a q h)
    · exact False.elim (hnac h)
  by_cases hp : ∃ a b, R p a ∧ R p b ∧ a ≠ b
  · obtain ⟨a, b, hpa, hpb, hab⟩ := hp
    refine Or.inr ?_
    intro c d hqc hqd
    apply Classical.byContradiction
    intro hcd
    by_cases hqa : R q a
    · by_cases hqb : R q b
      · exact free p q a b hpq hab ⟨hpa, hpb, hqa, hqb⟩
      · exact free p q c d hpq hcd
          ⟨(cross' b c hpb hqc).resolve_right hqb,
            (cross' b d hpb hqd).resolve_right hqb, hqc, hqd⟩
    · exact free p q c d hpq hcd
        ⟨(cross' a c hpa hqc).resolve_right hqa,
          (cross' a d hpa hqd).resolve_right hqa, hqc, hqd⟩
  · refine Or.inl ?_
    intro a b hpa hpb
    exact Classical.byContradiction (fun hab => hp ⟨a, b, hpa, hpb, hab⟩)

lemma oneCover_adjacent {α : Type} (R : α → α → Prop)
    (symm : ∀ u v, R u v → R v u) (p : α)
    (nonempty : ∃ u v, R u v)
    (cover : ∀ u v, R u v → u = p ∨ v = p) :
    ∃ q, R p q ∧ ∀ u v, R u v → u = p ∨ v = p ∨ u = q ∨ v = q := by
  have neighbor : ∃ q, R p q := by
    obtain ⟨u, v, huv⟩ := nonempty
    rcases cover u v huv with hu | hv
    · exact ⟨v, hu ▸ huv⟩
    · exact ⟨u, symm u p (hv ▸ huv)⟩
  obtain ⟨q, hpq⟩ := neighbor
  refine ⟨q, hpq, ?_⟩
  intro u v huv
  exact (cover u v huv).elim Or.inl (fun h => Or.inr (Or.inl h))

lemma twoCover_cross {α : Type} (R : α → α → Prop)
    (symm : ∀ u v, R u v → R v u) (irrefl : ∀ u, ¬ R u u)
    (cross : ∀ a b c d, R a b → R c d →
      R a c ∨ R a d ∨ R b c ∨ R b d)
    (p q : α) (hnpq : ¬ R p q)
    (cover : ∀ u v, R u v → u = p ∨ v = p ∨ u = q ∨ v = q) :
    ∀ a c, R p a → R q c → R p c ∨ R q a := by
  intro a c hpa hqc
  have hanp : a ≠ p := fun h => irrefl p (h ▸ hpa)
  have hanq : a ≠ q := fun h => hnpq (h ▸ hpa)
  have hcnp : c ≠ p := fun h => hnpq (symm q p (h ▸ hqc))
  have hcnq : c ≠ q := fun h => irrefl q (h ▸ hqc)
  have hnac : ¬ R a c := by
    intro hac
    rcases cover a c hac with h | h | h | h
    · exact hanp h
    · exact hcnp h
    · exact hanq h
    · exact hcnq h
  rcases cross p a q c hpa hqc with h | h | h | h
  · exact False.elim (hnpq h)
  · exact Or.inl h
  · exact Or.inr (symm a q h)
  · exact False.elim (hnac h)

lemma smallCover_adjacent {α : Type} (R : α → α → Prop)
    (symm : ∀ u v, R u v → R v u) (p q : α)
    (nonempty : ∃ u v, R u v)
    (cover : ∀ u v, R u v → u = p ∨ v = p ∨ u = q ∨ v = q)
    (cross : ∀ a c, R p a → R q c → R p c ∨ R q a)
    (small : ∀ a b, R q a → R q b → a = b) :
    ∃ p' q', R p' q' ∧
      ∀ u v, R u v → u = p' ∨ v = p' ∨ u = q' ∨ v = q' := by
  by_cases hq : ∃ r, R q r
  · obtain ⟨r, hqr⟩ := hq
    by_cases hpr : R p r
    · refine ⟨p, r, hpr, ?_⟩
      intro u v huv
      rcases cover u v huv with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr (small v r (h ▸ huv) hqr)))
      · exact Or.inr (Or.inr (Or.inl (small u r (symm u q (h ▸ huv)) hqr)))
    · have hp : ∀ a, ¬ R p a := by
        intro a hpa
        have hqa := (cross a r hpa hqr).resolve_left hpr
        exact hpr ((small a r hqa hqr) ▸ hpa)
      have cq : ∀ u v, R u v → u = q ∨ v = q := by
        intro u v huv
        rcases cover u v huv with h | h | h | h
        · exact False.elim (hp v (h ▸ huv))
        · exact False.elim (hp u (symm u p (h ▸ huv)))
        · exact Or.inl h
        · exact Or.inr h
      obtain ⟨r', hqr', cr⟩ := oneCover_adjacent R symm q nonempty cq
      exact ⟨q, r', hqr', cr⟩
  · have cp : ∀ u v, R u v → u = p ∨ v = p := by
      intro u v huv
      rcases cover u v huv with h | h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact False.elim (hq ⟨v, h ▸ huv⟩)
      · exact False.elim (hq ⟨u, symm u q (h ▸ huv)⟩)
    obtain ⟨r, hpr, cr⟩ := oneCover_adjacent R symm p nonempty cp
    exact ⟨p, r, hpr, cr⟩

lemma twoCover_adjacent {α : Type} (R : α → α → Prop)
    (symm : ∀ u v, R u v → R v u) (irrefl : ∀ u, ¬ R u u)
    (free : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ (R a b ∧ R a b' ∧ R a' b ∧ R a' b'))
    (cross : ∀ a b c d, R a b → R c d →
      R a c ∨ R a d ∨ R b c ∨ R b d)
    (nonempty : ∃ u v, R u v)
    (p q : α)
    (cover : ∀ u v, R u v → u = p ∨ v = p ∨ u = q ∨ v = q) :
    ∃ p' q', R p' q' ∧
      ∀ u v, R u v → u = p' ∨ v = p' ∨ u = q' ∨ v = q' := by
  by_cases hpq : p = q
  · subst q
    have cp : ∀ u v, R u v → u = p ∨ v = p := by
      intro u v huv
      rcases cover u v huv with h | h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact Or.inl h
      · exact Or.inr h
    obtain ⟨r, hpr, cr⟩ := oneCover_adjacent R symm p nonempty cp
    exact ⟨p, r, hpr, cr⟩
  · by_cases hadj : R p q
    · exact ⟨p, q, hadj, cover⟩
    · rcases twoCover_oneSmall R symm irrefl free cross p q hpq hadj cover with hp | hq
      · have cqp : ∀ u v, R u v → u = q ∨ v = q ∨ u = p ∨ v = p := by
          intro u v huv
          rcases cover u v huv with h | h | h | h
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr h))
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
        have hnqp : ¬ R q p := fun h => hadj (symm q p h)
        exact smallCover_adjacent R symm q p nonempty cqp
          (twoCover_cross R symm irrefl cross q p hnqp cqp) hp
      · exact smallCover_adjacent R symm p q nonempty cover
          (twoCover_cross R symm irrefl cross p q hadj cover) hq

lemma safeFilter_adjacentCover {α : Type} (R : α → α → Prop)
    (A B S : α → Prop)
    (symm : ∀ u v, R u v → R v u)
    (triangle : ∀ u v w, R u v → R v w → ¬ R u w)
    (free : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ (R a b ∧ R a b' ∧ R a' b ∧ R a' b'))
    (safe : ∀ u v, (A u ∨ A v) → (B u ∨ B v) → (S u ∨ S v) → R u v)
    (nonempty : ∃ u v, (A u ∨ A v) ∧ (B u ∨ B v) ∧ (S u ∨ S v)) :
    ∃ p q, R p q ∧ ∀ u v, (A u ∨ A v) → (B u ∨ B v) → (S u ∨ S v) →
      u = p ∨ v = p ∨ u = q ∨ v = q := by
  let T : α → α → Prop := fun u v => (A u ∨ A v) ∧ (B u ∨ B v) ∧ (S u ∨ S v)
  have tsafe : ∀ u v, T u v → R u v := fun u v h => safe u v h.1 h.2.1 h.2.2
  have tsymm : ∀ u v, T u v → T v u := by
    intro u v h
    exact ⟨h.1.elim Or.inr Or.inl, h.2.1.elim Or.inr Or.inl, h.2.2.elim Or.inr Or.inl⟩
  have tirrefl : ∀ u, ¬ T u u := by
    intro u h
    have huu := tsafe u u h
    exact triangle u u u huu huu huu
  have tfree : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ (T a b ∧ T a b' ∧ T a' b ∧ T a' b') := by
    intro a a' b b' haa hbb h
    exact free a a' b b' haa hbb
      ⟨tsafe a b h.1, tsafe a b' h.2.1, tsafe a' b h.2.2.1, tsafe a' b' h.2.2.2⟩
  have tcross : ∀ a b c d, T a b → T c d →
      T a c ∨ T a d ∨ T b c ∨ T b d := by
    intro a b c d hab hcd
    exact tripleFilter_cross A B S a b c d hab.1 hab.2.1 hab.2.2 hcd.1 hcd.2.1 hcd.2.2
  obtain ⟨z, w, hzw⟩ := nonempty
  obtain ⟨p, q, hcover⟩ := safeFilter_coverTwo R A B S z symm triangle free safe
  obtain ⟨p', q', hpq, hcover'⟩ := twoCover_adjacent T tsymm tirrefl tfree tcross
    ⟨z, w, hzw⟩ p q (fun u v h => hcover u v h.1 h.2.1 h.2.2)
  exact ⟨p', q', tsafe p' q' hpq, fun u v ha hb hs => hcover' u v ⟨ha, hb, hs⟩⟩

lemma safeFilters_unionAdjacentCover {α ι : Type} (R : α → α → Prop)
    (A B : α → Prop) (S : ι → α → Prop)
    (symm : ∀ u v, R u v → R v u)
    (triangle : ∀ u v w, R u v → R v w → ¬ R u w)
    (free : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ (R a b ∧ R a b' ∧ R a' b ∧ R a' b'))
    (safe : ∀ i u v, (A u ∨ A v) → (B u ∨ B v) → (S i u ∨ S i v) → R u v)
    (nonempty : ∃ i u v, (A u ∨ A v) ∧ (B u ∨ B v) ∧ (S i u ∨ S i v)) :
    ∃ p q, R p q ∧ ∀ i u v,
      (A u ∨ A v) → (B u ∨ B v) → (S i u ∨ S i v) →
      u = p ∨ v = p ∨ u = q ∨ v = q := by
  let U : α → Prop := fun u => ∃ i, S i u
  have usafe : ∀ u v, (A u ∨ A v) → (B u ∨ B v) → (U u ∨ U v) → R u v := by
    intro u v ha hb hu
    rcases hu with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact safe i u v ha hb (Or.inl hi)
    · exact safe i u v ha hb (Or.inr hi)
  obtain ⟨i, z, w, ha, hb, hs⟩ := nonempty
  have une : ∃ u v, (A u ∨ A v) ∧ (B u ∨ B v) ∧ (U u ∨ U v) := by
    refine ⟨z, w, ha, hb, ?_⟩
    exact hs.elim (fun h => Or.inl ⟨i, h⟩) (fun h => Or.inr ⟨i, h⟩)
  obtain ⟨p, q, hpq, hc⟩ := safeFilter_adjacentCover R A B U symm triangle free usafe une
  refine ⟨p, q, hpq, ?_⟩
  intro j u v hau hbu hsu
  exact hc u v hau hbu (hsu.elim (fun h => Or.inl ⟨j, h⟩) (fun h => Or.inr ⟨j, h⟩))

end PEqualNP.Outside.L_meta_2732_aux
