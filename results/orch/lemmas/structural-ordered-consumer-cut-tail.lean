namespace PEqualNP.Outside.L_meta_6659_aux

lemma consumer_chain_cut {n : Nat} {D : Dag} (hS : Strict n D)
    (i u : Fin n) (e : Nat × Bool) (he : e ∈ sem_W n D i)
    (empty : supp n D (src D (sem_bar e)) = ∅)
    (g barrier : Nat)
    (two : ∀ f ∈ sem_W n D i, f.1 = g ∨ f.1 = e.1)
    (chain : sem_Chain n D (n+g) barrier)
    (same : val D (single u) barrier = val D (sem_ins i (single u)) barrier) :
    ∀ target, barrier ≤ target → i ∉ supp n D target →
      val D (single u) target = val D (sem_ins i (single u)) target := by
  have inputs := sem_ins_agree i (single u)
  have blocked : ∀ target, barrier ≤ target →
      val D (single u) (n+g) ≠ val D (sem_ins i (single u)) (n+g) →
      Relation.ReflTransGen (fun a b => sem_step n D a b ∧
        val D (single u) b ≠ val D (sem_ins i (single u)) b) (n+g) target → False := by
    intro target bound changed path
    exact (single_reader_chain_hits hS chain
      (fun w => val D (single u) w ≠ val D (sem_ins i (single u)) w)
      target path changed bound) same
  have hj := (sem_mem_W.mp he).1
  have childZero : val D (single u) (src D (sem_bar e)) = false := by
    cases value : val D (single u) (src D (sem_bar e)) with
    | false => rfl
    | true =>
      have member := mem_supp.mpr value
      rw [empty] at member
      exact False.elim (Finset.notMem_empty u member)
  have parentPath : val D (single u) (n+e.1) ≠ val D (sem_ins i (single u)) (n+e.1) →
      (val D (single u) (n+g) ≠ val D (sem_ins i (single u)) (n+g)) ∧
        Relation.ReflTransGen (fun a b => sem_step n D a b ∧
          val D (single u) b ≠ val D (sem_ins i (single u)) b) (n+g) (n+e.1) := by
    intro parentChanged
    have childChanged : val D (single u) (src D (sem_bar e)) ≠
        val D (sem_ins i (single u)) (src D (sem_bar e)) := by
      intro childSame
      have zero : ∀ x : Fin n → Bool, val D x (src D (sem_bar e)) = false →
          val D x (n+e.1) = false := by
        intro x hx
        rw [val_gate hS x e.1 hj,sem_W_and hS he]
        obtain ⟨j,s⟩ := e
        cases s <;> simp only [sem_bar,src,Bool.not_false,Bool.not_true,ite_true,
          Bool.false_eq_true,ite_false] at hx ⊢ <;> simp [gop,hx]
      exact parentChanged ((zero _ childZero).trans
        (zero _ (childSame.symm.trans childZero)).symm)
    obtain ⟨f,hf,changed,path⟩ := consuming_changed_path hS (single u)
      (sem_ins i (single u)) i inputs (src D (sem_bar e)) childChanged
      (by rw [empty]; exact Finset.notMem_empty i)
    rcases two f hf with fromG | fromE
    · have initial : val D (single u) (n+g) ≠ val D (sem_ins i (single u)) (n+g) := by
        simpa only [fromG] using changed
      have toChild : Relation.ReflTransGen (fun a b => sem_step n D a b ∧
          val D (single u) b ≠ val D (sem_ins i (single u)) b)
          (n+g) (src D (sem_bar e)) := by simpa only [fromG] using path
      exact ⟨initial,Relation.ReflTransGen.tail toChild ⟨sem_step_src hj (!e.2),parentChanged⟩⟩
    · have backward := sem_rtg_le hS (fun _ _ step => step.1) path
      have before := sem_src_lt hS hj (!e.2)
      change src D (sem_bar e) < n+e.1 at before
      omega
  intro target bound absent
  by_contra changed
  obtain ⟨f,hf,initial,path⟩ := consuming_changed_path hS (single u)
    (sem_ins i (single u)) i inputs target changed absent
  rcases two f hf with fromG | fromE
  · apply blocked target bound
    · simpa only [fromG] using initial
    · simpa only [fromG] using path
  · have changedE : val D (single u) (n+e.1) ≠ val D (sem_ins i (single u)) (n+e.1) := by
      simpa only [fromE] using initial
    obtain ⟨changedG,toE⟩ := parentPath changedE
    have fromEPath : Relation.ReflTransGen (fun a b => sem_step n D a b ∧
        val D (single u) b ≠ val D (sem_ins i (single u)) b) (n+e.1) target := by
      simpa only [fromE] using path
    exact blocked target bound changedG (toE.trans fromEPath)

lemma consumer_barrier_true {n : Nat} {D : Dag} (hS : Strict n D)
    (i u : Fin n) (e : Nat × Bool) (he : e ∈ sem_W n D i)
    (empty : supp n D (src D (sem_bar e)) = ∅)
    (g barrier : Nat)
    (two : ∀ f ∈ sem_W n D i, f.1 = g ∨ f.1 = e.1)
    (chain : sem_Chain n D (n+g) barrier)
    (target : Nat) (after : barrier ≤ target) (absent : i ∉ supp n D target)
    (baseZero : val D (single u) target = false)
    (positive : val D (sem_ins i (single u)) target = true) :
    val D (sem_ins i (single u)) barrier = true := by
  cases value : val D (sem_ins i (single u)) barrier with
  | true => rfl
  | false =>
    have baseFalse : val D (single u) barrier = false := by
      cases base : val D (single u) barrier with
      | false => rfl
      | true =>
        have raised := val_mono hS (single u) (sem_ins i (single u))
          (sem_ins_ge i (single u)) barrier base
        rw [value] at raised
        exact False.elim (Bool.noConfusion raised)
    have same := consumer_chain_cut hS i u e he empty g barrier two chain
      (baseFalse.trans value.symm) target after absent
    rw [baseZero,positive] at same
    exact False.elim (Bool.noConfusion same)

end PEqualNP.Outside.L_meta_6659_aux
