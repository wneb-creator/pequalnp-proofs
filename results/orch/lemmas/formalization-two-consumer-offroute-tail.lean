namespace PEqualNP.Outside.L_meta_6659_aux

lemma two_consumers_offroute_agreement {n : Nat} {D : Dag} (hS : Strict n D)
    (i u : Fin n) (e : Nat × Bool) (he : e ∈ sem_W n D i)
    (empty : supp n D (src D (sem_bar e)) = ∅)
    (g target : Nat)
    (two : ∀ f ∈ sem_W n D i, f.1 = g ∨ f.1 = e.1)
    (offroute : ¬ Relation.ReflTransGen (sem_step n D) (n + g) target)
    (absent : i ∉ supp n D target) :
    val D (single u) target = val D (sem_ins i (single u)) target := by
  have inputs : ∀ k, k ≠ i → single u k = sem_ins i (single u) k := by
    intro k hk
    simp [sem_ins,hk]
  have pathLe : ∀ {a b : Nat}, Relation.ReflTransGen (sem_step n D) a b → a ≤ b := by
    intro a b path
    induction path with
    | refl => rfl
    | tail path step ih => exact Nat.le_trans ih (Nat.le_of_lt (sem_step_lt hS step))
  have hj := (sem_mem_W.mp he).1
  have childStep : sem_step n D (src D (sem_bar e)) (n + e.1) := by
    exact sem_step_src (n := n) hj (!e.2)
  have childLt : src D (sem_bar e) < n + e.1 :=
    sem_src_lt hS hj (!e.2)
  apply consuming_ancestors_agreement hS (single u) (sem_ins i (single u)) i inputs target _ absent
  intro f hf reach
  rcases two f hf with first | second
  · exact False.elim (offroute (by simpa only [first] using reach))
  · have parentReach : Relation.ReflTransGen (sem_step n D) (n + e.1) target := by
      simpa only [second] using reach
    have childSame : val D (single u) (src D (sem_bar e)) =
        val D (sem_ins i (single u)) (src D (sem_bar e)) := by
      apply consuming_ancestors_agreement hS (single u) (sem_ins i (single u)) i inputs _
      · intro f hf toChild
        rcases two f hf with first | second
        · apply False.elim
          apply offroute
          have fromG : Relation.ReflTransGen (sem_step n D) (n + g) (src D (sem_bar e)) := by
            simpa only [first] using toChild
          exact fromG.trans (Relation.ReflTransGen.head childStep parentReach)
        · have bound := pathLe toChild
          omega
      · rw [empty]
        exact Finset.notMem_empty i
    have childZero : val D (single u) (src D (sem_bar e)) = false := by
      cases hv : val D (single u) (src D (sem_bar e)) with
      | false => rfl
      | true =>
        have member : u ∈ supp n D (src D (sem_bar e)) := mem_supp.mpr hv
        rw [empty] at member
        exact False.elim (Finset.notMem_empty u member)
    have gateZero : ∀ x : Fin n → Bool, val D x (src D (sem_bar e)) = false →
        val D x (n + e.1) = false := by
      intro x hx
      rw [val_gate hS x e.1 hj,sem_W_and hS he]
      obtain ⟨j,s⟩ := e
      cases s <;> simp only [sem_bar,src,Bool.not_false,Bool.not_true,ite_true,
        Bool.false_eq_true,ite_false] at hx ⊢ <;> simp [gop,hx]
    rw [second,gateZero _ childZero,gateZero _ (childSame.symm.trans childZero)]

end PEqualNP.Outside.L_meta_6659_aux
