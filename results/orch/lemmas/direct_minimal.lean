import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2870_aux

private lemma point_ne_line {n : ℕ} (p l : Fin n) : Fin.castAdd n p ≠ Fin.natAdd n l := by
  intro h
  have hval := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
  have hp := p.isLt
  omega

private lemma line_ne_point {n : ℕ} (l p : Fin n) : Fin.natAdd n l ≠ Fin.castAdd n p :=
  (point_ne_line p l).symm

private lemma pair_line_count {n : ℕ} (p l : Fin n) :
    Fintype.card {r : Fin n // Fin.natAdd n r ∈
      ({Fin.castAdd n p, Fin.natAdd n l} : Finset (Fin (n+n)))} = 1 := by
  simp only [Finset.mem_insert, Finset.mem_singleton, line_ne_point, false_or, Fin.natAdd_inj]
  simp

private lemma line_count_mono {n : ℕ} (u t : Finset (Fin (n+n))) (h : u ⊆ t) :
    Fintype.card {l : Fin n // Fin.natAdd n l ∈ u} ≤
      Fintype.card {l : Fin n // Fin.natAdd n l ∈ t} := by
  apply Fintype.card_le_of_injective (fun l => ⟨l.1, h l.2⟩)
  intro a b hab
  apply Subtype.ext
  exact congrArg (fun z : {l : Fin n // Fin.natAdd n l ∈ t} => z.1) hab

private lemma forced_pair {n : ℕ} (u : Finset (Fin (n+n))) (p l a b : Fin n)
    (hsub : u ⊆ {Fin.castAdd n p, Fin.natAdd n l})
    (hp : Fin.castAdd n a ∈ u) (hl : Fin.natAdd n b ∈ u) :
    u = {Fin.castAdd n p, Fin.natAdd n l} := by
  have ha : a = p := by
    have h := hsub hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h
    · exact Fin.castAdd_inj.mp h
    · exact False.elim (point_ne_line a l h)
  have hb : b = l := by
    have h := hsub hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h
    · exact False.elim (line_ne_point b p h)
    · apply Fin.ext
      have hval := congrArg Fin.val h
      simp only [Fin.val_natAdd] at hval
      omega
  subst a b
  apply Finset.Subset.antisymm hsub
  intro i hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl
  · exact hp
  · exact hl

lemma sparse_minimal_supports (q n : ℕ) (I : Fin n → Fin n → Prop)
    (F : Finset (Finset (Fin (n+n)))) (hq : 1 ≤ q)
    (complete : ∀ p l, I p l → ∃ t ∈ F, t ⊆ {Fin.castAdd n p, Fin.natAdd n l})
    (sound : ∀ t ∈ F, Fintype.card {l : Fin n // Fin.natAdd n l ∈ t} ≤ q →
      ∃ p l, I p l ∧ Fin.castAdd n p ∈ t ∧ Fin.natAdd n l ∈ t)
    (t : Finset (Fin (n+n))) :
    Minimal (fun u => u ∈ F ∧ Fintype.card {l : Fin n // Fin.natAdd n l ∈ u} ≤ q) t ↔
      ∃ p l, I p l ∧ t = {Fin.castAdd n p, Fin.natAdd n l} := by
  have pairSmall (p l : Fin n) :
      Fintype.card {r : Fin n // Fin.natAdd n r ∈
        ({Fin.castAdd n p, Fin.natAdd n l} : Finset (Fin (n+n)))} ≤ q := by
    rw [pair_line_count]
    exact hq
  have pairMember (p l : Fin n) (inc : I p l) :
      ({Fin.castAdd n p, Fin.natAdd n l} : Finset (Fin (n+n))) ∈ F := by
    obtain ⟨u, hu, sub⟩ := complete p l inc
    have small := (line_count_mono u _ sub).trans (pairSmall p l)
    obtain ⟨a, b, _, ha, hb⟩ := sound u hu small
    rwa [forced_pair u p l a b sub ha hb] at hu
  constructor
  · intro h
    obtain ⟨p, l, inc, hp, hl⟩ := sound t h.prop.1 h.prop.2
    have sub : ({Fin.castAdd n p, Fin.natAdd n l} : Finset (Fin (n+n))) ⊆ t := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact hp
      · exact hl
    exact ⟨p, l, inc, Finset.Subset.antisymm (h.le_of_le ⟨pairMember p l inc, pairSmall p l⟩ sub) sub⟩
  · rintro ⟨p, l, inc, rfl⟩
    refine ⟨⟨pairMember p l inc, pairSmall p l⟩, ?_⟩
    intro u hu sub
    obtain ⟨a, b, _, ha, hb⟩ := sound u hu.1 hu.2
    rw [forced_pair u p l a b sub ha hb]

end PEqualNP.Outside.L_meta_2870_aux
