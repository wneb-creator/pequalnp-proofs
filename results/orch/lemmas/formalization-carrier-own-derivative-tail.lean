namespace PEqualNP.Outside.L_meta_6659_aux

def MarkedTrace (n : ℕ) (D : Dag) (base : Fin n → Bool)
    (v : Fin n) (d : ℕ → Bool) : Prop :=
  (∀ i : Fin n, d i.val = decide (i = v)) ∧
  ∀ j, j < D.length → d (n + j) = if tag D j then
    (val D base (opA D j) && d (opB D j)) ||
      (d (opA D j) && val D base (opB D j))
    else d (opA D j) || d (opB D j)

lemma carrier_own_derivative {n : ℕ} {D : Dag} (hS : Strict n D)
    (andEmpty : ∀ j, j < D.length → tag D j = true → supp n D (n+j) = ∅)
    (base : Fin n → Bool) (x : Fin n) (d : ℕ → Bool)
    (trace : MarkedTrace n D base x d) : ∀ w, x ∈ supp n D w → d w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro member
    have value : val D (single x) w = true := by simpa [supp] using member
    by_cases input : w < n
    · rw [val_input D (single x) w input] at value
      exact (trace.1 ⟨w,input⟩).trans value
    · by_cases valid : w < n+D.length
      · obtain ⟨j,rfl⟩ : ∃ j, w = n+j := ⟨w-n,by omega⟩
        have hj : j < D.length := by omega
        obtain ⟨ha,hb,_⟩ := hS j hj
        cases ht : tag D j with
        | true =>
          rw [andEmpty j hj ht] at member
          exact False.elim (Finset.notMem_empty _ member)
        | false =>
          rw [val_gate hS (single x) j hj,ht] at value
          simp only [gop,Bool.or_eq_true] at value
          rw [trace.2 j hj,ht]
          rcases value with va | vb
          · have hd := ih _ ha (by simpa [supp] using va)
            simp [hd]
          · have hd := ih _ hb (by simpa [supp] using vb)
            simp [hd]
      · rw [val_ge D (single x) w (by omega)] at value
        exact Bool.noConfusion value

end PEqualNP.Outside.L_meta_6659_aux
