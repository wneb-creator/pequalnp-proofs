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

lemma single_reader_chain_agreement {n : ℕ} {D : Dag} (hS : Strict n D)
    (x y : Fin n → Bool) (i : Fin n) (agree : ∀ k, k ≠ i → x k = y k)
    {a w : ℕ} (chain : sem_Chain n D i.val a) (bound : a ≤ w)
    (same : val D x a = val D y a) : val D x w = val D y w := by
  by_contra changed
  have inputChanged : x i ≠ y i := by
    intro hi
    have equal : x = y := by
      funext k
      by_cases hk : k = i
      · simpa only [hk] using hi
      · exact agree k hk
    exact changed (congrArg (fun z => val D z w) equal)
  have firstChanged : val D x i.val ≠ val D y i.val := by
    simpa only [val_input D x i.val i.isLt,val_input D y i.val i.isLt] using inputChanged
  exact (single_reader_chain_hits hS chain (fun z => val D x z ≠ val D y z)
    w (sem_changed_path hS x y i agree w changed) firstChanged bound) same

lemma ineligible_consumption_insert_false {n : ℕ} {D : Dag} (hS : Strict n D)
    (i c : Fin n) (hi : i ∈ ineligSet n D) (e : ℕ × Bool)
    (he : e ∈ sem_W n D i) (absent : c ∉ supp n D (src D (sem_bar e)))
    (w : ℕ) (bound : n + e.1 ≤ w) (absentW : c ∉ supp n D w) :
    val D (sem_ins i (single c)) w = false := by
  obtain ⟨hj,carrier,_⟩ := sem_mem_W.mp he
  have chain : sem_Chain n D i.val (src D e) := sem_inelig_chain hS hi carrier
  have step : sem_step n D (src D e) (n+e.1) := sem_step_src hj e.2
  have one : fanout D (src D e) = 1 := by
    have lower := sem_step_fanout step
    have upper := mem_ineligSet.mp hi (src D e) carrier
    omega
  have otherSame : val D (single c) (src D (sem_bar e)) =
      val D (sem_ins i (single c)) (src D (sem_bar e)) := by
    by_contra changed
    have reach := sem_rtg_mono (fun _ _ h => h.1)
      (sem_changed_path hS (single c) (sem_ins i (single c)) i
        (sem_ins_agree i (single c)) _ changed)
    exact single_reader_other_unreachable hS chain step one
      (sem_step_src hj (!e.2)) (sem_src_ne hS hj e.2).symm reach
  have otherFalse : val D (single c) (src D (sem_bar e)) = false := by
    cases hv : val D (single c) (src D (sem_bar e)) with
    | false => rfl
    | true => exact False.elim (absent (mem_supp.mpr hv))
  have gateFalse (z : Fin n → Bool) (hz : val D z (src D (sem_bar e)) = false) :
      val D z (n+e.1) = false := by
    rw [val_gate hS z e.1 hj,sem_W_and hS he]
    cases hs : e.2 <;> simp [sem_bar,src,hs] at hz <;> simp [gop,hz]
  have sameGate : val D (single c) (n+e.1) = val D (sem_ins i (single c)) (n+e.1) :=
    (gateFalse _ otherFalse).trans (gateFalse _ (otherSame.symm.trans otherFalse)).symm
  have sameW := single_reader_chain_agreement hS (single c) (sem_ins i (single c)) i
    (sem_ins_agree i (single c)) (Relation.ReflTransGen.tail chain ⟨step,one⟩) bound sameGate
  have baseFalse : val D (single c) w = false := by
    cases hv : val D (single c) w with
    | false => rfl
    | true => exact False.elim (absentW (mem_supp.mpr hv))
  exact sameW.symm.trans baseFalse

end PEqualNP.Outside.L_meta_6659_aux
