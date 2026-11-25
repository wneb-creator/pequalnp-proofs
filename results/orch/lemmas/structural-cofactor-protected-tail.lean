namespace PEqualNP.Outside.L_meta_6659_aux

def equality_cof_rep {n m : ℕ} (ι : Fin m → Fin n) (q : ℕ → ℕ) (e : ℕ) : ℕ :=
  if he : e < m then (ι ⟨e,he⟩).val else n + q (e-m)

theorem equality_cof_rep_input {n m : ℕ} (ι : Fin m → Fin n) (q : ℕ → ℕ) (i : Fin m) :
    equality_cof_rep ι q i.val = (ι i).val := by
  simp [equality_cof_rep,i.isLt]

theorem equality_cof_rep_gate {n m : ℕ} (ι : Fin m → Fin n) (q : ℕ → ℕ) (j : ℕ) :
    equality_cof_rep ι q (m+j) = n + q j := by
  simp [equality_cof_rep]

theorem equality_cof_rep_reaches {n m : ℕ} {D E : Dag} {ρ : Fin n → Option Bool}
    {ι : Fin m → Fin n} {t q : ℕ → ℕ} (hS : Strict n D) (hok : cof_Ok ρ ι)
    (hI : cof_Inv D ρ ι D.length E t q) {w : ℕ} (hw : cof_live D ρ ι w) :
    Relation.ReflTransGen (sem_step n D) (equality_cof_rep ι q (t w)) w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases input : w < n
    · obtain ⟨i,rfl⟩ := cof_live_input hok input hw
      rw [hI.2.2.2.2 i,equality_cof_rep_input]
    · let j := w-n
      have wj : w = n+j := by omega
      have hj : j < D.length := by have := cof_live_lt hw; omega
      rw [wj] at hw ⊢
      rcases hI.2.2.2.1 j hj hw with ⟨i,hi,hqi⟩ | collapsed
      · have image := (hI.2.2.1 i hi).2.2.1
        rw [hqi] at image
        rw [image,equality_cof_rep_gate,hqi]
      · obtain ⟨s,hs⟩ := cof_live_op hS hj hw
        have lt : src D (j,s) < w := by
          rw [wj]
          cases s
          · simpa only [sb_src_false] using (hS j hj).1
          · simpa only [sb_src_true] using (hS j hj).2.1
        have path := ih (src D (j,s)) lt hs
        rw [collapsed s hs] at path
        exact path.tail (sem_step_src hj s)

theorem equality_cof_step_lift {n m : ℕ} {D E : Dag} {ρ : Fin n → Option Bool}
    {ι : Fin m → Fin n} {t q : ℕ → ℕ} (hS : Strict n D) (hok : cof_Ok ρ ι)
    (hI : cof_Inv D ρ ι D.length E t q) {a b : ℕ} (hab : sem_step m E a b) :
    Relation.ReflTransGen (sem_step n D) (equality_cof_rep ι q a) (equality_cof_rep ι q b) := by
  obtain ⟨j,s,hj,rfl,rfl⟩ := sem_step_iff.mp hab
  obtain ⟨hq,_,_,ha,hb,hla,hlb⟩ := hI.2.2.1 j hj
  have image : src E (j,s) = t (src D (q j,s)) := by
    cases s <;> simp only [sb_src_false,sb_src_true] <;> assumption
  have live : cof_live D ρ ι (src D (q j,s)) := by
    cases s <;> simp only [sb_src_false,sb_src_true] <;> assumption
  rw [image,equality_cof_rep_gate]
  exact (equality_cof_rep_reaches hS hok hI live).tail (sem_step_src hq s)

theorem equality_cof_path_lift {n m : ℕ} {D E : Dag} {ρ : Fin n → Option Bool}
    {ι : Fin m → Fin n} {t q : ℕ → ℕ} (hS : Strict n D) (hok : cof_Ok ρ ι)
    (hI : cof_Inv D ρ ι D.length E t q) {a b : ℕ}
    (hab : Relation.ReflTransGen (sem_step m E) a b) :
    Relation.ReflTransGen (sem_step n D) (equality_cof_rep ι q a) (equality_cof_rep ι q b) := by
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact ih.trans (equality_cof_step_lift hS hok hI step)

theorem equality_cof_preserves_protection {n m : ℕ} {D E : Dag} {ρ : Fin n → Option Bool}
    {ι : Fin m → Fin n} {t q : ℕ → ℕ} (hS : Strict n D) (hok : cof_Ok ρ ι)
    (hI : cof_Inv D ρ ι D.length E t q) (i : Fin m)
    (hprotected : ∀ w, Relation.ReflTransGen (sem_step n D) (ι i).val w → fanout D w ≤ 1) :
    ∀ e, Relation.ReflTransGen (sem_step m E) i.val e → fanout E e ≤ 1 := by
  classical
  intro e path
  have lifted := equality_cof_path_lift hS hok hI path
  rw [equality_cof_rep_input] at lifted
  have sum : ∑ w ∈ cof_fib D ρ ι t e, cof_deg D ρ ι w ≤ (cof_fib D ρ ι t e).card := by
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_le_sum
    intro w hw
    obtain ⟨_,live,image⟩ := Finset.mem_filter.mp hw
    apply (cof_deg_le w).trans
    apply hprotected
    have tail := equality_cof_rep_reaches hS hok hI live
    rw [image] at tail
    exact lifted.trans tail
  have bound := cof_fib_bound hS hok hI e
  omega

end PEqualNP.Outside.L_meta_6659_aux
