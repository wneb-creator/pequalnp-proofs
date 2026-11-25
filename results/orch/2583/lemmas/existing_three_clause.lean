import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583_aux.ThreeClause

def Hits {N : ℕ} (S : Finset (Fin N)) (x : Fin N → Bool) : Prop :=
  ∃ p ∈ S, x p = true

def Original {N : ℕ} (P L Rp Rl : Finset (Fin N))
    (x y : Fin N → Bool) : Prop :=
  Hits P x ∧ Hits L y ∧ (Hits Rp x ∨ Hits Rl y)

def Pruned {N : ℕ} (P L Rp Rl : Finset (Fin N))
    (x y : Fin N → Bool) : Prop :=
  (Hits (P ∩ Rp) x ∧ Hits L y) ∨ (Hits P x ∧ Hits (L ∩ Rl) y)

lemma pruned_below {N : ℕ} (P L Rp Rl : Finset (Fin N))
    (x y : Fin N → Bool) : Pruned P L Rp Rl x y → Original P L Rp Rl x y := by
  rintro (⟨⟨p,hp,xp⟩,hl⟩ | ⟨hp,⟨l,hl,yl⟩⟩)
  · exact ⟨⟨p,(Finset.mem_inter.mp hp).1,xp⟩,hl,
      Or.inl ⟨p,(Finset.mem_inter.mp hp).2,xp⟩⟩
  · exact ⟨hp,⟨l,(Finset.mem_inter.mp hl).1,yl⟩,
      Or.inr ⟨l,(Finset.mem_inter.mp hl).2,yl⟩⟩

lemma pair_agreement {N : ℕ} (P L Rp Rl : Finset (Fin N)) (p l : Fin N) :
    Pruned P L Rp Rl (fun i => decide (i = p)) (fun i => decide (i = l)) ↔
      Original P L Rp Rl (fun i => decide (i = p)) (fun i => decide (i = l)) := by
  simp only [Pruned, Original, Hits, decide_eq_true_eq, exists_eq_right,
    Finset.mem_inter]
  tauto

lemma point_centres_card_le_one {N : ℕ} (I : Fin N → Fin N → Prop)
    (P L Rp Rl : Finset (Fin N)) (hL : 2 ≤ L.card)
    (rect : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (clean : ∀ p l : Fin N,
      Original P L Rp Rl (fun i => decide (i = p)) (fun i => decide (i = l)) → I p l) :
    (P ∩ Rp).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro p hp p' hp'
  by_contra ne
  have hsmall : L.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro l hl l' hl'
    by_contra ll
    apply rect p p' l l' ne ll
    have edge (a : Fin N) (ha : a ∈ P ∩ Rp) (b : Fin N) (hb : b ∈ L) : I a b := by
      apply clean a b
      simp only [Original, Hits, decide_eq_true_eq, exists_eq_right]
      exact ⟨(Finset.mem_inter.mp ha).1,hb,Or.inl (Finset.mem_inter.mp ha).2⟩
    exact ⟨edge p hp l hl,edge p hp l' hl',edge p' hp' l hl,edge p' hp' l' hl'⟩
  omega

lemma line_centres_card_le_one {N : ℕ} (I : Fin N → Fin N → Prop)
    (P L Rp Rl : Finset (Fin N)) (hP : 2 ≤ P.card)
    (rect : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (clean : ∀ p l : Fin N,
      Original P L Rp Rl (fun i => decide (i = p)) (fun i => decide (i = l)) → I p l) :
    (L ∩ Rl).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro l hl l' hl'
  by_contra ne
  have hsmall : P.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro p hp p' hp'
    by_contra pp
    apply rect p p' l l' pp ne
    have edge (a : Fin N) (ha : a ∈ P) (b : Fin N) (hb : b ∈ L ∩ Rl) : I a b := by
      apply clean a b
      simp only [Original, Hits, decide_eq_true_eq, exists_eq_right]
      exact ⟨ha,(Finset.mem_inter.mp hb).1,Or.inr (Finset.mem_inter.mp hb).2⟩
    exact ⟨edge p hp l hl,edge p hp l' hl',edge p' hp' l hl,edge p' hp' l' hl'⟩
  omega

lemma edges_use_centres {N : ℕ} (P L Rp Rl : Finset (Fin N)) (p l : Fin N)
    (h : Original P L Rp Rl (fun i => decide (i = p)) (fun i => decide (i = l))) :
    p ∈ P ∩ Rp ∨ l ∈ L ∩ Rl := by
  simp only [Original, Hits, decide_eq_true_eq, exists_eq_right] at h
  rcases h.2.2 with hp | hl
  · exact Or.inl (Finset.mem_inter.mpr ⟨h.1,hp⟩)
  · exact Or.inr (Finset.mem_inter.mpr ⟨h.2.1,hl⟩)

end PEqualNP.Outside.L_meta_2583_aux.ThreeClause
