import PNPAccepted6659

namespace PEqualNP.Outside.L_meta_6659_aux

lemma two_exit_cross_adj {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    {x : Fin 14} {e f : Nat × Bool} (code : sem_W 14 D x = {e,f})
    {a b : Fin 14} (ha : a ∈ supp 14 D (src D e))
    (hb : b ∈ supp 14 D (src D f)) (hax : a ≠ x) (hbx : b ≠ x) : Adj a b := by
  classical
  by_contra absent
  obtain ⟨q,hq,hqa,hqb⟩ := sem_hw_cover_free h hD (Ne.symm hax) (Ne.symm hbx) absent
  rw [code,Finset.mem_insert,Finset.mem_singleton] at hq
  rcases hq with rfl | rfl
  · exact hqa ha
  · exact hqb hb

lemma two_exit_extras {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    {x : Fin 14} {e f : Nat × Bool} (code : sem_W 14 D x = {e,f}) :
    Disjoint ((supp 14 D (src D e)).erase x) ((supp 14 D (src D f)).erase x) ∧
    (((supp 14 D (src D e)).erase x).card ≤ 1 ∨
      ((supp 14 D (src D f)).erase x).card ≤ 1) := by
  classical
  have cross : ∀ a ∈ (supp 14 D (src D e)).erase x,
      ∀ b ∈ (supp 14 D (src D f)).erase x, Adj a b := by
    intro a ha b hb
    exact two_exit_cross_adj h hD code (Finset.mem_erase.mp ha).2
      (Finset.mem_erase.mp hb).2 (Finset.mem_erase.mp ha).1 (Finset.mem_erase.mp hb).1
  constructor
  · rw [Finset.disjoint_left]
    intro a ha hb
    exact adj_irrefl a (cross a ha a hb)
  · by_cases small : ((supp 14 D (src D e)).erase x).card ≤ 1
    · exact Or.inl small
    · right
      obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp (Nat.lt_of_not_ge small)
      rw [Finset.card_le_one]
      intro c hc d hd
      exact sem_hw_common a b c d hab
        ((hc_adjB_iff d a).mpr (adj_symm (cross a ha d hd)))
        ((hc_adjB_iff d b).mpr (adj_symm (cross b hb d hd)))
        ((hc_adjB_iff c a).mpr (adj_symm (cross a ha c hc)))
        ((hc_adjB_iff c b).mpr (adj_symm (cross b hb c hc)))

lemma two_exit_support_dichotomy {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    {x : Fin 14} {e f : Nat × Bool} (code : sem_W 14 D x = {e,f}) :
    supp 14 D (src D e) = {x} ∨ supp 14 D (src D f) = {x} ∨
      (∃ a : Fin 14, a ≠ x ∧ supp 14 D (src D e) = {x,a} ∧
        ∀ b ∈ supp 14 D (src D f), b = x ∨ Adj a b) ∨
      (∃ a : Fin 14, a ≠ x ∧ supp 14 D (src D f) = {x,a} ∧
        ∀ b ∈ supp 14 D (src D e), b = x ∨ Adj a b) := by
  classical
  have classify : ∀ A : Finset (Fin 14), x ∈ A → (A.erase x).card ≤ 1 →
      A = {x} ∨ ∃ a, a ≠ x ∧ A = {x,a} := by
    intro A hx small
    by_cases singleton : ∀ a ∈ A, a = x
    · left
      ext a
      simp only [Finset.mem_singleton]
      exact ⟨fun ha => singleton a ha,fun equal => equal.symm ▸ hx⟩
    · push Not at singleton
      obtain ⟨a,ha,hax⟩ := singleton
      refine Or.inr ⟨a,hax,?_⟩
      ext b
      simp only [Finset.mem_insert,Finset.mem_singleton]
      constructor
      · intro hb
        by_cases hbx : b = x
        · exact Or.inl hbx
        · exact Or.inr ((Finset.card_le_one.mp small) b
            (Finset.mem_erase.mpr ⟨hbx,hb⟩) a (Finset.mem_erase.mpr ⟨hax,ha⟩))
      · rintro (rfl | rfl) <;> assumption
  have xe : x ∈ supp 14 D (src D e) :=
    (sem_mem_W.mp (by rw [code]; simp)).2.1
  have xf : x ∈ supp 14 D (src D f) :=
    (sem_mem_W.mp (by rw [code]; simp)).2.1
  rcases (two_exit_extras h hD code).2 with small | small
  · rcases classify _ xe small with pure | ⟨a,hax,pair⟩
    · exact Or.inl pure
    · refine Or.inr (Or.inr (Or.inl ⟨a,hax,pair,?_⟩))
      intro b hb
      by_cases hbx : b = x
      · exact Or.inl hbx
      · exact Or.inr (two_exit_cross_adj h hD code (by rw [pair]; simp) hb hax hbx)
  · rcases classify _ xf small with pure | ⟨a,hax,pair⟩
    · exact Or.inr (Or.inl pure)
    · refine Or.inr (Or.inr (Or.inr ⟨a,hax,pair,?_⟩))
      intro b hb
      by_cases hbx : b = x
      · exact Or.inl hbx
      · exact Or.inr (adj_symm (two_exit_cross_adj h hD code hb (by rw [pair]; simp) hbx hax))

end PEqualNP.Outside.L_meta_6659_aux
