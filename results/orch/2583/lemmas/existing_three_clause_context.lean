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

lemma hits_mono {N : ℕ} (S : Finset (Fin N)) (x x' : Fin N → Bool)
    (le : ∀ p, x p = true → x' p = true) : Hits S x → Hits S x' := by
  rintro ⟨p,hp,xp⟩
  exact ⟨p,hp,le p xp⟩

lemma pruned_mono {N : ℕ} (P L Rp Rl : Finset (Fin N))
    (x y x' y' : Fin N → Bool)
    (hx : ∀ p, x p = true → x' p = true)
    (hy : ∀ l, y l = true → y' l = true) :
    Pruned P L Rp Rl x y → Pruned P L Rp Rl x' y' := by
  rintro (⟨hp,hl⟩ | ⟨hp,hl⟩)
  · exact Or.inl ⟨hits_mono _ _ _ hx hp,hits_mono _ _ _ hy hl⟩
  · exact Or.inr ⟨hits_mono _ _ _ hx hp,hits_mono _ _ _ hy hl⟩

lemma replace_in_monotone_context {N : ℕ} (I : Fin N → Fin N → Prop)
    (g h : (Fin N → Bool) → (Fin N → Bool) → Prop)
    (K : (Fin N → Bool) → (Fin N → Bool) → Prop → Prop)
    (below : ∀ x y, h x y → g x y)
    (pair : ∀ p l : Fin N, I p l →
      (h (fun i => decide (i = p)) (fun i => decide (i = l)) ↔
       g (fun i => decide (i = p)) (fun i => decide (i = l))))
    (hmono : ∀ x y x' y', (∀ p, x p = true → x' p = true) →
      (∀ l, y l = true → y' l = true) → h x y → h x' y')
    (kmono : ∀ x y x' y' (a b : Prop), (∀ p, x p = true → x' p = true) →
      (∀ l, y l = true → y' l = true) → (a → b) → K x y a → K x' y' b)
    (correct : ∀ x y, K x y (g x y) ↔ ∃ p l, I p l ∧ x p = true ∧ y l = true) :
    ∀ x y, K x y (h x y) ↔ ∃ p l, I p l ∧ x p = true ∧ y l = true := by
  intro x y
  constructor
  · intro hit
    apply (correct x y).mp
    exact kmono x y x y (h x y) (g x y) (fun _ => id) (fun _ => id) (below x y) hit
  · rintro ⟨p,l,edge,xp,yl⟩
    let x₀ : Fin N → Bool := fun i => decide (i = p)
    let y₀ : Fin N → Bool := fun i => decide (i = l)
    have pairTrue : K x₀ y₀ (g x₀ y₀) :=
      (correct x₀ y₀).mpr ⟨p,l,edge,by simp [x₀],by simp [y₀]⟩
    have changed : K x₀ y₀ (h x₀ y₀) := by
      rw [propext (pair p l edge)]
      exact pairTrue
    have lx : ∀ i, x₀ i = true → x i = true := by
      intro i hi
      have eq : i = p := of_decide_eq_true hi
      exact eq ▸ xp
    have ly : ∀ i, y₀ i = true → y i = true := by
      intro i hi
      have eq : i = l := of_decide_eq_true hi
      exact eq ▸ yl
    exact kmono x₀ y₀ x y (h x₀ y₀) (h x y) lx ly
      (hmono x₀ y₀ x y lx ly) changed

end PEqualNP.Outside.L_meta_2583_aux.ThreeClause
