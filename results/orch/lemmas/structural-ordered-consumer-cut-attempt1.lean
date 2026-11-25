import PNPAccepted6659

namespace PEqualNP.Outside.L_meta_6659_aux

lemma single_reader_path_le {n : ℕ} {D : Dag} (hS : Strict n D) {a b : ℕ}
    (path : Relation.ReflTransGen (sem_step n D) a b) : a ≤ b := by
  induction path with
  | refl => rfl
  | tail path step ih => exact Nat.le_trans ih (Nat.le_of_lt (sem_step_lt hS step))

lemma single_reader_chain_le {n : ℕ} {D : Dag} (hS : Strict n D) {a b : ℕ}
    (path : sem_Chain n D a b) : a ≤ b :=
  single_reader_path_le hS (sem_rtg_mono (fun _ _ h => h.1) path)

lemma single_reader_other_unreachable {n : ℕ} {D : Dag} (hS : Strict n D)
    {v a b c : ℕ} (chain : sem_Chain n D v a)
    (last : sem_step n D a b) (one : fanout D a = 1)
    (other : sem_step n D c b) (different : c ≠ a) :
    ¬ Relation.ReflTransGen (sem_step n D) v c := by
  induction chain using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro reach
    rcases Relation.ReflTransGen.cases_head reach with equal | ⟨z,first,rest⟩
    · exact different equal.symm
    · have same : b = z := sem_step_unique last first one
      have le := single_reader_path_le hS rest
      have lt := sem_step_lt hS other
      omega
  | @head start next first rest ih =>
    intro reach
    rcases Relation.ReflTransGen.cases_head reach with equal | ⟨z,initial,remaining⟩
    · have direct : sem_step n D start b := by simpa [equal] using other
      have same : next = b := sem_step_unique first.1 direct first.2
      have le := single_reader_chain_le hS rest
      have lt := sem_step_lt hS last
      omega
    · have same : next = z := sem_step_unique first.1 initial first.2
      subst z
      exact ih remaining

lemma single_reader_chain_hits {n : ℕ} {D : Dag} (hS : Strict n D)
    {a b : ℕ} (chain : sem_Chain n D a b) (P : ℕ → Prop) :
    ∀ w, Relation.ReflTransGen (fun u v => sem_step n D u v ∧ P v) a w →
      P a → b ≤ w → P b := by
  induction chain using Relation.ReflTransGen.head_induction_on with
  | refl => intro w path start bound; exact start
  | @head a next step rest ih =>
    intro w path start bound
    rcases Relation.ReflTransGen.cases_head path with equal | ⟨z,first,remaining⟩
    · have increasing := sem_step_lt hS step.1
      have restLe := single_reader_chain_le hS rest
      omega
    · have same : next = z := sem_step_unique step.1 first.1 step.2
      subst z
      exact ih w remaining first.2 bound

end PEqualNP.Outside.L_meta_6659_aux

namespace PEqualNP.Outside.L_meta_6659_aux

lemma consuming_changed_path {n : Nat} {D : Dag} (hS : Strict n D)
    (x y : Fin n → Bool) (i : Fin n)
    (inputs : ∀ k, k ≠ i → x k = y k) (target : Nat)
    (changed : val D x target ≠ val D y target) (absent : i ∉ supp n D target) :
    ∃ e ∈ sem_W n D i, val D x (n+e.1) ≠ val D y (n+e.1) ∧
      Relation.ReflTransGen (fun a b => sem_step n D a b ∧ val D x b ≠ val D y b)
        (n+e.1) target := by
  have first : ∀ {a b : Nat},
      Relation.ReflTransGen (fun a b => sem_step n D a b ∧ val D x b ≠ val D y b) a b →
      i ∈ supp n D a → i ∉ supp n D b →
      ∃ e ∈ sem_W n D i, val D x (n+e.1) ≠ val D y (n+e.1) ∧
        Relation.ReflTransGen (fun a b => sem_step n D a b ∧ val D x b ≠ val D y b)
          (n+e.1) b := by
    intro a b path
    induction path using Relation.ReflTransGen.head_induction_on with
    | refl => intro present absent; exact False.elim (absent present)
    | @head a c step rest ih =>
      intro present absent
      by_cases next : i ∈ supp n D c
      · exact ih next absent
      · obtain ⟨j,s,hj,rfl,source⟩ := sem_step_iff.mp step.1
        refine ⟨(j,s),sem_mem_W.mpr ⟨hj,?_,next⟩,step.2,rest⟩
        rw [source]
        exact present
  apply first (sem_changed_path hS x y i inputs target changed) _ absent
  rw [supp_input D i]
  exact Finset.mem_singleton_self i

end PEqualNP.Outside.L_meta_6659_aux

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
