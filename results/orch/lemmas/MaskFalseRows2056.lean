import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2056_aux.MaskRows

def decode {n : ℕ} (m : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => m.testBit i.val

theorem mem_decode {n : ℕ} (m : ℕ) (i : Fin n) :
    i ∈ decode m ↔ m.testBit i.val = true := by simp [decode]

def maskEval {n : ℕ} (E : List (Fin n × Fin n)) (m : ℕ) : Bool :=
  E.any fun e => m.testBit e.1.val && m.testBit e.2.val

def maskGood {n : ℕ} (E : List (Fin n × Fin n)) (m : ℕ) : Bool :=
  !maskEval E m && (List.range n).all (fun i => m.testBit i || maskEval E (m ||| 2 ^ i))

def setEval {n : ℕ} (E : List (Fin n × Fin n)) (U : Finset (Fin n)) : Bool :=
  E.any fun e => decide (e.1 ∈ U) && decide (e.2 ∈ U)

theorem setEval_decode {n : ℕ} (E : List (Fin n × Fin n)) (m : ℕ) :
    setEval E (decode m) = maskEval E m := by
  simp [setEval, maskEval, mem_decode]

theorem decode_insert {n : ℕ} (m : ℕ) (i : Fin n) :
    decode (m ||| 2 ^ i.val) = insert i (decode m) := by
  ext j
  simp only [mem_decode, Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow,
    decide_eq_true_eq, Finset.mem_insert]
  constructor
  · rintro (h | h)
    · exact Or.inr h
    · exact Or.inl (Fin.ext h.symm)
  · rintro (rfl | h)
    · exact Or.inr rfl
    · exact Or.inl h

theorem decode_injective_bounded {n : ℕ} {m k : ℕ}
    (hm : m < 2 ^ n) (hk : k < 2 ^ n)
    (he : (decode m : Finset (Fin n)) = decode k) : m = k := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · have hiff : m.testBit i = true ↔ k.testBit i = true := by
      simpa only [mem_decode] using
        (show (⟨i, hi⟩ : Fin n) ∈ decode m ↔ (⟨i, hi⟩ : Fin n) ∈ decode k by rw [he])
    cases hmi : m.testBit i <;> cases hki : k.testBit i <;> simp_all
  · have hp : 2 ^ n ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hm hp),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hk hp)]

def MaximalFalseSet {n : ℕ} (f : Finset (Fin n) → Bool) (U : Finset (Fin n)) : Prop :=
  f U = false ∧ ∀ i, i ∉ U → f (insert i U) = true

theorem good_maximal {n : ℕ} (E : List (Fin n × Fin n)) (m : ℕ)
    (h : maskGood E m = true) : MaximalFalseSet (setEval E) (decode m) := by
  rw [maskGood, Bool.and_eq_true] at h
  have hm : maskEval E m = false := by
    cases he : maskEval E m
    · rfl
    · simp [he] at h
  refine ⟨by simpa only [setEval_decode] using hm, ?_⟩
  intro i hi
  have hbit : m.testBit i.val = false := by
    cases hb : m.testBit i.val
    · rfl
    · exact False.elim (hi ((mem_decode m i).2 hb))
  have hv := List.all_eq_true.mp h.2 i.val (List.mem_range.mpr i.isLt)
  rw [hbit, Bool.false_or] at hv
  rw [← decode_insert m i, setEval_decode]
  exact hv

theorem distinct_good_rows_lower_bound {n : ℕ} (E : List (Fin n × Fin n)) (M : List ℕ)
    (hn : M.Nodup) (hb : M.all (fun m => decide (m < 2 ^ n)) = true)
    (hg : M.all (maskGood E) = true)
    (f : Finset (Fin n) → Bool) (hf : ∀ U, f U = setEval E U) :
    M.length ≤ Nat.card {U : Finset (Fin n) // MaximalFalseSet f U} := by
  classical
  let embed (i : Fin M.length) : {U : Finset (Fin n) // MaximalFalseSet f U} :=
    ⟨decode (M.get i), by
      have hgood := good_maximal E (M.get i)
        (List.all_eq_true.mp hg (M.get i) (List.get_mem M i))
      simpa only [MaximalFalseSet, hf] using hgood⟩
  have hinj : Function.Injective embed := by
    intro i j he
    apply hn.injective_get
    have hi : M.get i < 2 ^ n := of_decide_eq_true
      (List.all_eq_true.mp hb (M.get i) (List.get_mem M i))
    have hj : M.get j < 2 ^ n := of_decide_eq_true
      (List.all_eq_true.mp hb (M.get j) (List.get_mem M j))
    exact decode_injective_bounded hi hj (congrArg Subtype.val he)
  simpa using Fintype.card_le_of_injective embed hinj

end PEqualNP.Outside.L_meta_2056_aux.MaskRows
