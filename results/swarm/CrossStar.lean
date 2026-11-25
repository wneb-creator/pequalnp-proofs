import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5012

def CrossStar {n : ℕ} (G : SimpleGraph (Fin n)) (A B : Finset (Fin n)) : Prop :=
  ∃ x ∈ A, ∃ y ∈ B, G.Adj x y ∧
    (∀ a ∈ A, G.Adj a y) ∧ (∀ b ∈ B, G.Adj x b)

lemma no_four {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : PEqualNP.TopForm.NoFourCycle G) {a b u v : Fin n}
    (hab : a ≠ b) (huv : u ≠ v) (hau : G.Adj a u) (hav : G.Adj a v)
    (hbu : G.Adj b u) (hbv : G.Adj b v) : False := by
  have hh := h a b hab
  have hsub : ({u, v} : Finset (Fin n)) ⊆
      Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj b w) := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · simp [hau, hbu]
    · have he := Finset.mem_singleton.mp hw
      subst w
      simp [hav, hbv]
  have hc := Finset.card_le_card hsub
  rw [Finset.card_pair huv] at hc
  omega

lemma two_shared_right_crossStar {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (h4 : PEqualNP.TopForm.NoFourCycle G)
    (A B C D : Finset (Fin n)) (ha : 2 ≤ A.card) (hc : 2 ≤ C.card)
    (x y z : Fin n) (hxa : x ∈ A) (hxc : x ∈ C)
    (hyb : y ∈ B) (hyd : y ∈ D) (hzb : z ∈ B) (hzd : z ∈ D) (hyz : y ≠ z)
    (h : ∀ a ∈ A, ∀ b ∈ B, ∀ c ∈ C, ∀ d ∈ D,
      G.Adj a b ∨ G.Adj a d ∨ G.Adj c b ∨ G.Adj c d) :
    CrossStar G A B ∨ CrossStar G C D := by
  classical
  have row : (∀ b ∈ B, G.Adj x b) ∨ (∀ d ∈ D, G.Adj x d) := by
    by_cases hh : ∀ b ∈ B, G.Adj x b
    · exact Or.inl hh
    · right
      push Not at hh
      obtain ⟨b, hb, hxb⟩ := hh
      intro d hd
      have := h x hxa b hb x hxc d hd
      tauto
  have col : ∀ t ∈ B ∩ D,
      (∀ a ∈ A, G.Adj a t) ∨ (∀ c ∈ C, G.Adj c t) := by
    intro t ht
    obtain ⟨htb, htd⟩ := Finset.mem_inter.mp ht
    by_cases hh : ∀ a ∈ A, G.Adj a t
    · exact Or.inl hh
    · right
      push Not at hh
      obtain ⟨a, ha', hat⟩ := hh
      intro c hc'
      have := h a ha' t htb c hc' t htd
      tauto
  have notAA : ¬ ((∀ a ∈ A, G.Adj a y) ∧ (∀ a ∈ A, G.Adj a z)) := by
    rintro ⟨hy, hz⟩
    obtain ⟨a, ha', b, hb', hab⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
    exact no_four G h4 hab hyz (hy a ha') (hz a ha') (hy b hb') (hz b hb')
  have notCC : ¬ ((∀ c ∈ C, G.Adj c y) ∧ (∀ c ∈ C, G.Adj c z)) := by
    rintro ⟨hy, hz⟩
    obtain ⟨a, ha', b, hb', hab⟩ := Finset.one_lt_card.mp (by omega : 1 < C.card)
    exact no_four G h4 hab hyz (hy a ha') (hz a ha') (hy b hb') (hz b hb')
  have cy := col y (Finset.mem_inter.mpr ⟨hyb, hyd⟩)
  have cz := col z (Finset.mem_inter.mpr ⟨hzb, hzd⟩)
  have split : ((∀ a ∈ A, G.Adj a y) ∧ (∀ c ∈ C, G.Adj c z)) ∨
      ((∀ a ∈ A, G.Adj a z) ∧ (∀ c ∈ C, G.Adj c y)) := by
    tauto
  rcases row with rB | rD
  · left
    rcases split with hs | hs
    · exact ⟨x, hxa, y, hyb, rB y hyb, hs.1, rB⟩
    · exact ⟨x, hxa, z, hzb, rB z hzb, hs.1, rB⟩
  · right
    rcases split with hs | hs
    · exact ⟨x, hxc, z, hzd, rD z hzd, hs.2, rD⟩
    · exact ⟨x, hxc, y, hyd, rD y hyd, hs.2, rD⟩

lemma clean_products_quad {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (A B C D : Finset (Fin n)) (color : Bool)
    (hA : ∀ a ∈ A, s a = color) (hB : ∀ b ∈ B, s b = !color)
    (hC : ∀ c ∈ C, s c = color) (hD : ∀ d ∈ D, s d = !color)
    (hclean : ∀ x : Fin n → Bool,
      (∃ a ∈ A, x a = true) → (∃ b ∈ B, x b = true) →
      (∃ c ∈ C, x c = true) → (∃ d ∈ D, x d = true) →
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true) :
    ∀ a ∈ A, ∀ b ∈ B, ∀ c ∈ C, ∀ d ∈ D,
      G.Adj a b ∨ G.Adj a d ∨ G.Adj c b ∨ G.Adj c d := by
  intro a ha b hb c hc d hd
  let x : Fin n → Bool := fun w => decide (w = a ∨ w = b ∨ w = c ∨ w = d)
  have hx := hclean x ⟨a, ha, by simp [x]⟩ ⟨b, hb, by simp [x]⟩
    ⟨c, hc, by simp [x]⟩ ⟨d, hd, by simp [x]⟩
  have he : ∃ u v, G.Adj u v ∧ (u = a ∨ u = b ∨ u = c ∨ u = d) ∧
      (v = a ∨ v = b ∨ v = c ∨ v = d) := by
    simpa [PEqualNP.MetaComplexity.NestedCover.graphFun, x] using hx
  have hAC : ¬ G.Adj a c := fun hac => (hbip a c hac) ((hA a ha).trans (hC c hc).symm)
  have hBD : ¬ G.Adj b d := fun hbd => (hbip b d hbd) ((hB b hb).trans (hD d hd).symm)
  obtain ⟨u, v, huv, hu, hv⟩ := he
  rcases hu with rfl | rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl | rfl
  all_goals first
    | exact False.elim (hAC huv)
    | exact False.elim (hAC (huv.symm))
    | exact False.elim (hBD huv)
    | exact False.elim (hBD (huv.symm))
    | (have hsym := huv.symm; tauto)

end PEqualNP.Outside.L_meta_5012
