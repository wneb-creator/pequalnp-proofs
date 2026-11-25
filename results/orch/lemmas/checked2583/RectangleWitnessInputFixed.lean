import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583.RectangleWitness

open scoped BigOperators

lemma point_avoiding (q N r : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hdegree : ∀ l, (Finset.univ.filter fun p => I p l).card = q+1)
    (hr : r ≤ q) (centres : Fin r → Fin N) (l : Fin N) :
    ∃ p, I p l ∧ ∀ i, p ≠ centres i := by
  classical
  let T : Finset (Fin N) := Finset.univ.image centres
  have ht : T.card ≤ r := by
    exact Finset.card_image_le.trans (by simp)
  by_contra h
  push Not at h
  have hs : (Finset.univ.filter fun p => I p l) ⊆ T := by
    intro p hp
    obtain ⟨i, hi⟩ := h p (Finset.mem_filter.mp hp).2
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi.symm⟩
  have hc := Finset.card_le_card hs
  rw [hdegree] at hc
  omega

lemma line_avoiding (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hdegree : ∀ p, (Finset.univ.filter fun l => I p l).card = q+1)
    (hunique : ∀ p p', p ≠ p' → ∃! l, I p l ∧ I p' l)
    (A : Finset (Fin N)) (ha : A.card ≤ q) (p : Fin N) (hp : p ∉ A) :
    ∃ l, I p l ∧ ∀ a ∈ A, ¬I a l := by
  classical
  let bad (a : Fin N) : Finset (Fin N) := Finset.univ.filter fun l => I p l ∧ I a l
  have hbad : ∀ a ∈ A, (bad a).card ≤ 1 := by
    intro a ha
    apply Finset.card_le_one.mpr
    intro l hl l' hl'
    have hpa : p ≠ a := by
      intro he
      subst a
      exact hp ha
    obtain ⟨k, hk, hu⟩ := hunique p a hpa
    exact (hu l (Finset.mem_filter.mp hl).2).trans (hu l' (Finset.mem_filter.mp hl').2).symm
  let B := A.biUnion bad
  have hB : B.card ≤ A.card := by
    calc
      B.card ≤ ∑ a ∈ A, (bad a).card := Finset.card_biUnion_le
      _ ≤ ∑ a ∈ A, 1 := Finset.sum_le_sum hbad
      _ = A.card := by simp
  by_contra h
  push Not at h
  have hs : (Finset.univ.filter fun l => I p l) ⊆ B := by
    intro l hl
    have hpl := (Finset.mem_filter.mp hl).2
    obtain ⟨a, ha, hal⟩ := h l hpl
    apply Finset.mem_biUnion.mpr
    exact ⟨a, ha, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl, hal⟩⟩
  have hc := Finset.card_le_card hs
  rw [hdegree] at hc
  omega

lemma rectangle_family_negative (q N r : ℕ)
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hline : ∀ l, (Finset.univ.filter fun p => I p l).card = q+1)
    (hpoint : ∀ p, (Finset.univ.filter fun l => I p l).card = q+1)
    (hunique : ∀ p p', p ≠ p' → ∃! l, I p l ∧ I p' l)
    (hr : r ≤ q) (centres lines : Fin r → Fin N) :
    ∃ A B : Finset (Fin N), A.card ≤ r ∧ B.card ≤ r ∧
      (∀ a ∈ A, ∀ b ∈ B, ¬I a b) ∧
      (∀ i, ∃ a ∈ A, I a (lines i)) ∧
      (∀ i, ∃ b ∈ B, I (centres i) b) := by
  classical
  have hx : ∀ i, ∃ a, I a (lines i) ∧ ∀ j, a ≠ centres j :=
    fun i => point_avoiding q N r I hline hr centres (lines i)
  choose a ha hne using hx
  let A : Finset (Fin N) := Finset.univ.image a
  have hA : A.card ≤ r := Finset.card_image_le.trans (by simp)
  have hcentres : ∀ i, centres i ∉ A := by
    intro i hi
    obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hi
    exact hne j i he
  have hy : ∀ i, ∃ b, I (centres i) b ∧ ∀ c ∈ A, ¬I c b :=
    fun i => line_avoiding q N I hpoint hunique A (hA.trans hr) (centres i) (hcentres i)
  choose b hb havoid using hy
  let B : Finset (Fin N) := Finset.univ.image b
  refine ⟨A, B, hA, Finset.card_image_le.trans (by simp), ?_, ?_, ?_⟩
  · intro x hx y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    exact havoid i x hx
  · intro i
    exact ⟨a i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, ha i⟩
  · intro i
    exact ⟨b i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, hb i⟩

lemma rectangle_family_false_positive (q N r : ℕ)
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hline : ∀ l, (Finset.univ.filter fun p => I p l).card = q+1)
    (hpoint : ∀ p, (Finset.univ.filter fun l => I p l).card = q+1)
    (hunique : ∀ p p', p ≠ p' → ∃! l, I p l ∧ I p' l)
    (hr : r ≤ q) (centres lines : Fin r → Fin N) :
    ∃ z : Fin (N+N) → Bool,
      (¬∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
      ∀ i, (∃ p, I p (lines i) ∧ z (Fin.castAdd N p) = true) ∧
        (∃ l, I (centres i) l ∧ z (Fin.natAdd N l) = true) := by
  classical
  obtain ⟨A, B, hA, hB, hind, ha, hb⟩ :=
    rectangle_family_negative q N r I hline hpoint hunique hr centres lines
  let z : Fin (N+N) → Bool :=
    Fin.addCases (fun p => decide (p ∈ A)) (fun l => decide (l ∈ B))
  have hzP (p : Fin N) : z (Fin.castAdd N p) = decide (p ∈ A) := by simp [z]
  have hzL (l : Fin N) : z (Fin.natAdd N l) = decide (l ∈ B) := by
    exact Fin.addCases_right l
  refine ⟨z, ?_, ?_⟩
  · rintro ⟨p, l, hpl, hp, hl⟩
    rw [hzP] at hp
    rw [hzL] at hl
    exact hind p (of_decide_eq_true hp) l (of_decide_eq_true hl) hpl
  · intro i
    obtain ⟨p, hp, hpi⟩ := ha i
    obtain ⟨l, hl, hil⟩ := hb i
    refine ⟨⟨p, hpi, ?_⟩, ⟨l, hil, ?_⟩⟩
    · simpa only [hzP, decide_eq_true_eq] using hp
    · simpa only [hzL, decide_eq_true_eq] using hl

end PEqualNP.Outside.L_meta_2583.RectangleWitness
