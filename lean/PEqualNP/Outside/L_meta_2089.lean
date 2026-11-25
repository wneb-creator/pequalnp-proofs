import Mathlib

namespace PEqualNP.Outside.L_meta_2089

lemma maximal_pair_cover {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (R : α → β → Prop)
    (A U : Finset α) (B V : Finset β)
    (maxA : ∀ a, a ∉ A → ∃ b ∈ B, R a b)
    (maxB : ∀ b, b ∉ B → ∃ a ∈ A, R a b)
    (disjA : Disjoint U A) (disjB : Disjoint V B)
    (cover : ∀ a b, R a b → a ∈ U ∨ b ∈ V) :
    U = Aᶜ ∧ V = Bᶜ := by
  constructor
  · ext a
    simp only [Finset.mem_compl]
    constructor
    · intro ha hA
      exact Finset.disjoint_left.mp disjA ha hA
    · intro ha
      obtain ⟨b, hb, hab⟩ := maxA a ha
      rcases cover a b hab with hu | hv
      · exact hu
      · exact False.elim (Finset.disjoint_left.mp disjB hv hb)
  · ext b
    simp only [Finset.mem_compl]
    constructor
    · intro hb hB
      exact Finset.disjoint_left.mp disjB hb hB
    · intro hb
      obtain ⟨a, ha, hab⟩ := maxB b hb
      rcases cover a b hab with hu | hv
      · exact False.elim (Finset.disjoint_left.mp disjA hu ha)
      · exact hv

lemma weighted_cut {X : Type} (V : X → ℕ → Bool) (x : X) (G O : Finset ℕ)
    (hstep : ∀ w ∈ G, ∃ P : Finset ℕ,
      P.card ≤ 1 + (if w ∈ O then 1 else 0) ∧
      (∀ r ∈ P, r < w) ∧ (∀ r ∈ P, V x r = false) ∧
      ∀ y, (∀ r ∈ P, V y r = false) → V y w = false)
    (t : ℕ) (F : Finset ℕ) (hF : ∀ w ∈ F, w ∈ G → w < t)
    (hFx : ∀ w ∈ F, V x w = false) :
    ∃ B : Finset ℕ, Disjoint B G ∧
      B.card ≤ F.card + (O.filter (· < t)).card ∧
      (∀ r ∈ B, V x r = false) ∧
      ∀ y, (∀ r ∈ B, V y r = false) → ∀ w ∈ F, V y w = false := by
  classical
  induction t generalizing F with
  | zero =>
    refine ⟨F, Finset.disjoint_left.mpr ?_, Nat.le_add_right .., hFx, ?_⟩
    · intro w hw hg
      have := hF w hw hg
      omega
    · exact fun _ h => h
  | succ t ih =>
    by_cases hex : t ∈ F ∧ t ∈ G
    · obtain ⟨P, hPcard, hP, hPx, hp⟩ := hstep t hex.2
      let F' := F.erase t ∪ P
      have hF' : ∀ w ∈ F', w ∈ G → w < t := by
        intro w hw hg
        rcases Finset.mem_union.mp hw with hw | hw
        · have hne := (Finset.mem_erase.mp hw).1
          have hlt := hF w (Finset.mem_erase.mp hw).2 hg
          omega
        · exact hP w hw
      have hF'x : ∀ w ∈ F', V x w = false := by
        intro w hw
        rcases Finset.mem_union.mp hw with hw | hw
        · exact hFx w (Finset.mem_erase.mp hw).2
        · exact hPx w hw
      obtain ⟨B, hd, hc, hBx, hi⟩ := ih F' hF' hF'x
      have hsize : F'.card ≤ F.card + (if t ∈ O then 1 else 0) := by
        have hu := Finset.card_union_le (F.erase t) P
        have he := Finset.card_erase_add_one hex.1
        change F'.card ≤ _ at hu
        omega
      have hfilter : (O.filter (· < t + 1)).card =
          (O.filter (· < t)).card + (if t ∈ O then 1 else 0) := by
        by_cases ht : t ∈ O
        · have heq : O.filter (· < t + 1) = insert t (O.filter (· < t)) := by
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
          rw [heq, Finset.card_insert_of_notMem (by simp), ite_eq_left ht]
        · have heq : O.filter (· < t + 1) = O.filter (· < t) := by
            ext w
            simp only [Finset.mem_filter]
            constructor
            · rintro ⟨hw, hlt⟩
              refine ⟨hw, ?_⟩
              have : w ≠ t := fun h => ht (h ▸ hw)
              omega
            · rintro ⟨hw, hlt⟩
              exact ⟨hw, by omega⟩
          rw [heq, ite_eq_right ht, add_zero]
      refine ⟨B, hd, ?_, hBx, ?_⟩
      · rw [hfilter]
        omega
      · intro y hy w hw
        by_cases h : w = t
        · subst w
          exact hp y fun r hr => hi y hy r (Finset.mem_union_right _ hr)
        · exact hi y hy w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hw⟩))
    · have hF' : ∀ w ∈ F, w ∈ G → w < t := by
        intro w hw hg
        have hne : w ≠ t := fun e => hex ⟨e ▸ hw, e ▸ hg⟩
        have hlt := hF w hw hg
        omega
      obtain ⟨B, hd, hc, hBx, hi⟩ := ih F hF' hFx
      have hle : (O.filter (· < t)).card ≤ (O.filter (· < t + 1)).card :=
        Finset.card_le_card fun w hw =>
          Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1,
            by have := (Finset.mem_filter.mp hw).2; omega⟩
      exact ⟨B, hd, by omega, hBx, hi⟩

def delta : Finset (Fin 13) := {0, 1, 3, 9}

def incidence (p l : Fin 13) : Prop := ∃ d ∈ delta, p = l + d

lemma separated_points : ∀ p q : Fin 13, p ≠ q →
    ∃ l : Fin 13, ¬incidence p l ∧ incidence q l := by
  unfold incidence delta
  decide

lemma singleton_maximal (p : Fin 13) : ∀ q ∉ ({p} : Finset (Fin 13)),
    ∃ l : Fin 13, (∀ x ∈ ({p} : Finset (Fin 13)), ¬incidence x l) ∧
      incidence q l := by
  intro q hq
  obtain ⟨l, hl, hql⟩ := separated_points p q (by simpa [eq_comm] using hq)
  refine ⟨l, ?_, hql⟩
  intro x hx
  obtain rfl := Finset.mem_singleton.mp hx
  exact hl

lemma incidence_refl (p : Fin 13) : incidence p p := by
  exact ⟨0, by simp [delta], by simp⟩

end PEqualNP.Outside.L_meta_2089
