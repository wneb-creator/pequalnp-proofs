import Floor17Projection
namespace PEqualNP.Outside.L_meta_2592.Full

lemma first_keeps_all {k : Nat} {d : Fin 4} {a b : Fin 10} {ka kb : Bool}
    {rest : List (Wire Row)} (hab : a ≠ b)
    (perm : (raw a :: raw b :: rest).Perm (inputs.map observe))
    (run : Run true (observe graph) k
      (comb d.val (raw a) (raw b) :: kept ka (raw a) (kept kb (raw b) rest))) :
    ∀ i : Fin 10, (i = a ∨ i = b) → raw i ∈ kept ka (raw a) (kept kb (raw b) rest) := by
  intro i hi
  by_contra absent
  obtain ⟨different,gateSame,otherSame⟩ := first_witness d a b i hab hi
  apply different
  apply Run.rows_agree run
  intro w hw
  rcases List.mem_cons.mp hw with rfl | hw
  · exact gateSame
  · have old := perm.mem_iff.mp (kept_inputs_mem ka kb (raw a) (raw b) w rest hw)
    rw [raw_bank] at old
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp old
    apply otherSame j
    rintro rfl
    exact absent hw

lemma first_split {k : Nat} (run : Run true (observe graph) k (inputs.map observe)) :
    ∃ (s : Nat) (d : Fin 4) (a b : Fin 10), k = s+1 ∧ a ≠ b ∧
      Run true (observe graph) s (comb d.val (raw a) (raw b) :: inputs.map observe) := by
  cases k with
  | zero =>
    change List.Perm [observe graph] (inputs.map observe) at run
    have len := run.length_eq
    simp only [List.length_cons,List.length_nil,List.length_map] at len
    have il : inputs.length = 10 := rfl
    omega
  | succ s =>
    obtain ⟨op,ka,kb,a,b,rest,allowedOp,perm,tail⟩ := run
    have small : op < 4 := by
      rcases allowedOp with h | ⟨_,h⟩ <;> omega
    have ha := perm.mem_iff.mp (show a ∈ a :: b :: rest from by simp)
    have hb := perm.mem_iff.mp (show b ∈ a :: b :: rest from by simp)
    rw [raw_bank] at ha hb
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hb
    have nodup := perm.nodup_iff.mpr raw_bank_nodup
    have noA := (List.nodup_cons.mp nodup).1
    have noB := (List.nodup_cons.mp (List.nodup_cons.mp nodup).2).1
    have notEqual : raw i ≠ raw j := by
      intro h
      apply noA
      simp [h]
    have ij : i ≠ j := fun h => notEqual (congrArg raw h)
    have keptAll := first_keeps_all (d:=⟨op,small⟩) ij perm tail
    have kaTrue : ka = true := by
      cases ka
      · have h := keptAll i (Or.inl rfl)
        apply False.elim
        apply noA
        cases kb <;> simp_all [kept]
      · rfl
    have kbTrue : kb = true := by
      cases kb
      · have h := keptAll j (Or.inr rfl)
        rw [kaTrue] at h
        simp only [kept,ite_true,Bool.false_eq_true,ite_false,List.mem_cons] at h
        rcases h with h | h
        · exact False.elim (notEqual h.symm)
        · exact False.elim (noB h)
      · rfl
    refine ⟨s,⟨op,small⟩,i,j,rfl,ij,?_⟩
    rw [kaTrue,kbTrue] at tail
    simp only [kept,ite_true] at tail
    exact Run.perm (perm.cons _) tail

lemma binary_seventeen (C : PEqualNP.CircuitLowerBounds.Circuit)
    (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = edge x) :
    17 ≤ C.gates.countP (fun g => !isNot g) := by
  obtain ⟨k,hk,run⟩ := circuit_run C legal computes
  obtain ⟨s,d,a,b,heq,_,tail⟩ := first_split run
  have hs := first_suffix_floor d a b tail
  omega

lemma seventeen_not_lower (C : PEqualNP.CircuitLowerBounds.Circuit)
    (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = edge x) :
    17 + PEqualNP.NotBracket.notCount C ≤ C.size := by
  have lower := binary_seventeen C legal computes
  have total := count_partition C.gates
  rw [not_count_eq]
  change 17 + C.gates.countP isNot ≤ C.gates.length
  omega

lemma two_not_bound (C : PEqualNP.CircuitLowerBounds.Circuit)
    (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = edge x)
    (small : C.size ≤ 19) : PEqualNP.NotBracket.notCount C ≤ 2 := by
  have lower := seventeen_not_lower C legal computes
  omega

end PEqualNP.Outside.L_meta_2592.Full
