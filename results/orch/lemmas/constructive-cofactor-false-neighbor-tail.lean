theorem equality_cofactor_neighbor_branch_empty {D : Dag} (h : StrictLive 14 D)
    (hD : Correct D) {c z : Fin 14} {l : List ℕ} (hgood : cf_good c l)
    (edge : Adj c z) {b : ℕ} (chain : sem_Chain 14 D z.val b) :
    cof_supp D (cf_rho c) (cf_iota l) b = ∅ := by
  classical
  have hC := sem_heawood_comp hD
  have hok : cof_Ok (cf_rho c) (cf_iota l) := ⟨hgood.1,hgood.2.1⟩
  have truefixed (u : Fin 14) : cf_rho c u = some true ↔ u = c := by
    by_cases equal : u = c
    · simp [cf_rho,equal]
    · simp [cf_rho,equal]
  apply Finset.eq_empty_iff_forall_notMem.2
  intro i member
  let base := cof_ext (cf_rho c) (cf_iota l) (single i)
  have supported (u : Fin 14) : base u = true ↔ u = cf_iota l i ∨ u = c := by
    rw [show base u = cof_ext (cf_rho c) (cf_iota l) (single i) u from rfl,
      cof_ext_single hok,truefixed]
  have free : cf_rho c (cf_iota l i) = none := (hgood.2.1 _).2 ⟨i,rfl⟩
  have distinct : cf_iota l i ≠ c := by
    intro equal
    simpa [equal,cf_rho] using free
  have nonedge : ¬ Adj c (cf_iota l i) := by
    intro adjacent
    rw [cf_rho,if_neg distinct,if_pos ((hc_adjB_iff _ _).2 adjacent)] at free
    cases free
  have zero : val D base (outW 14 D) = false := by
    cases value : val D base (outW 14 D) with
    | false => rfl
    | true =>
      obtain ⟨u,v,adjacent,hu,hv⟩ := (hC base).1 value
      rcases (supported u).1 hu with rfl | rfl <;>
        rcases (supported v).1 hv with rfl | rfl
      · exact (adj_irrefl _ adjacent).elim
      · exact (nonedge (adj_symm adjacent)).elim
      · exact (nonedge adjacent).elim
      · exact (adj_irrefl _ adjacent).elim
  have after : val D (sem_ins z base) (outW 14 D) = true := by
    apply (hC _).2
    refine ⟨c,z,edge,?_,?_⟩
    · have basec : base c = true := (supported c).2 (Or.inr rfl)
      have unequal : c ≠ z := fun equal => adj_irrefl z (equal ▸ edge)
      simpa [sem_ins,unequal] using basec
    · simp [sem_ins]
  have falsebranch := equality_critical_branch_false h.1 base z chain zero after
  have truebranch := cof_mem_supp.1 member
  rw [falsebranch] at truebranch
  exact Bool.false_ne_true truebranch
