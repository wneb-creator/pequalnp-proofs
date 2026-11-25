theorem pilot_nonedge_extension :
    ∀ u v i : Fin 14, hc_adjB u v = false → i ≠ u → i ≠ v →
      ∃ z : Fin 14, hc_adjB i z = true ∧ hc_adjB u z = false ∧ hc_adjB v z = false := by
  decide +kernel

theorem pilot_chain_nonedge_pair_false {D : Dag} (hS : Strict 14 D) (hD : Correct D)
    {i u v : Fin 14} {w : ℕ} (chain : sem_Chain 14 D i.val w)
    (huv : ¬ Adj u v) (hiu : i ≠ u) (hiv : i ≠ v) :
    val D (sem_ind ({u,v} : Finset (Fin 14))) w = false := by
  obtain ⟨z,hiz,huz,hvz⟩ := pilot_nonedge_extension u v i
    (sem_adjB_false.2 huv) hiu hiv
  have hiz' := (hc_adjB_iff _ _).1 hiz
  have huz' := sem_adjB_false.1 huz
  have hvz' := sem_adjB_false.1 hvz
  have independent : ∀ a ∈ ({u,v,z} : Finset (Fin 14)),
      ∀ b ∈ ({u,v,z} : Finset (Fin 14)), ¬ Adj a b := by
    intro a ha b hb
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    · exact adj_irrefl _
    · exact huv
    · exact huz'
    · exact fun h => huv (adj_symm h)
    · exact adj_irrefl _
    · exact hvz'
    · exact fun h => huz' (adj_symm h)
    · exact fun h => hvz' (adj_symm h)
    · exact adj_irrefl _
  have negative := sem_ind_no_edge independent
  have positive : sem_Edge Adj (sem_ins i (sem_ind ({u,v,z} : Finset (Fin 14)))) := by
    refine ⟨i,z,hiz',sem_ins_self _ _,sem_ins_ge _ _ z ?_⟩
    simp [sem_ind]
  have branch_false := (sem_dom_split hS (sem_heawood_comp hD)
    (sem_ind ({u,v,z} : Finset (Fin 14))) i w (sem_chain_dom hS chain)
    negative positive).1
  have monotone : ∀ k : Fin 14, sem_ind ({u,v} : Finset (Fin 14)) k = true →
      sem_ind ({u,v,z} : Finset (Fin 14)) k = true := by
    intro k hk
    simp only [sem_ind,decide_eq_true_eq,Finset.mem_insert,Finset.mem_singleton] at hk ⊢
    rcases hk with rfl | rfl <;> simp
  cases value : val D (sem_ind ({u,v} : Finset (Fin 14))) w with
  | false => rfl
  | true =>
    have bad := val_mono hS _ _ monotone w value
    rw [branch_false] at bad
    exact Bool.noConfusion bad
