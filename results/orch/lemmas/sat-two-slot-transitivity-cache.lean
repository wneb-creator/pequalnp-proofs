import PNPAccepted6659
set_option maxRecDepth 100000
set_option maxHeartbeats 200000
namespace PEqualNP.Outside.L_meta_6659_aux

lemma two_slot_together_trans {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    {x y z : Fin 14} (hxy : x ≠ y) (hyz : y ≠ z) (hxz : ¬ Adj x z)
    (hy : (sem_W 14 D y).card ≤ 2)
    (first : ∃ e, e ∈ sem_W 14 D x ∧ e ∈ sem_W 14 D y)
    (second : ∃ e, e ∈ sem_W 14 D y ∧ e ∈ sem_W 14 D z) :
    ∃ e, e ∈ sem_W 14 D x ∧ e ∈ sem_W 14 D z := by
  classical
  obtain ⟨a,hax,hay⟩ := first
  obtain ⟨b,hby,hbz⟩ := second
  by_cases hab : a = b
  · exact ⟨a,hax,by simpa only [hab] using hbz⟩
  obtain ⟨c,hcy,hcx,hcz⟩ := sem_hw_cover_free h hD (Ne.symm hxy) hyz hxz
  have hca : c ≠ a := by
    intro eq
    subst c
    exact hcx (sem_mem_W.mp hax).2.1
  have hcb : c ≠ b := by
    intro eq
    subst c
    exact hcz (sem_mem_W.mp hbz).2.1
  have sub : ({a,b,c} : Finset (ℕ × Bool)) ⊆ sem_W 14 D y := by
    intro e he
    simp only [Finset.mem_insert,Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact hay
    · exact hby
    · exact hcy
  have card := Finset.card_le_card sub
  have three : ({a,b,c} : Finset (ℕ × Bool)).card = 3 := by
    simp [hab,Ne.symm hca,Ne.symm hcb]
  rw [three] at card
  omega

end PEqualNP.Outside.L_meta_6659_aux
