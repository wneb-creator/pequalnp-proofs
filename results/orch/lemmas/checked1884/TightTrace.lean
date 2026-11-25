import Bound17
import PrefixNot

namespace PEqualNP.Outside.L_meta_1884.TightTrace

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2592 PEqualNP.Outside.L_meta_2592.Projection

lemma initial_nonOr_bound {k d : Nat} {U : Finset Extended.Sig} {a b : Extended.Sig}
    (hd : Extended.allowed true d) (notOr : d ≠ 1)
    (ha : a ∈ Extended.initial) (hb : b ∈ Extended.initial) (hab : a ≠ b)
    (fresh : Extended.bin d a b ∉ insert a (insert b U))
    (raw : ∀ c ∈ U, c ∈ Extended.initial)
    (tail : Extended.Live true Extended.target k (insert (Extended.bin d a b) U)) :
    18 ≤ k + 1 := by
  have retained := Extended.initial_retained hd ha hb hab raw tail
  obtain ⟨i, rfl⟩ := initial_pin ha
  obtain ⟨j, rfl⟩ := initial_pin hb
  have leftFresh : Extended.bin d (pin i) (pin j) ∉ insert (pin i) U := by
    intro h
    apply fresh
    rcases Finset.mem_insert.mp h with h | h
    · exact Finset.mem_insert.mpr (Or.inl h)
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h)
  rcases Extended.allowed_four hd with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · have bound := tail_bound_two_constants (Or.inl rfl) retained.1 leftFresh raw tail
    omega
  · exact (notOr rfl).elim
  · have bound := tail_bound_two_constants (Or.inr rfl) retained.1 leftFresh raw tail
    omega
  · have same : Extended.bin 3 (pin i) (pin j) = Extended.bin 2 (pin j) (pin i) := by
      simp [Extended.bin, BitVec.and_comm]
    rw [same] at fresh tail
    have rightFresh : Extended.bin 2 (pin j) (pin i) ∉ insert (pin j) U := by
      intro h
      exact fresh (Finset.mem_insert_of_mem h)
    have bound := tail_bound_two_constants (Or.inr rfl) retained.2 rightFresh raw tail
    omega

lemma saturated_first_or {S : Finset Extended.Sig}
    (run : Extended.Live true Extended.target 17 S)
    (raw : ∀ a ∈ S, a ∈ Extended.initial) :
    ∃ (U : Finset Extended.Sig) (a b : Extended.Sig),
      a ∈ Extended.initial ∧ b ∈ Extended.initial ∧ a ≠ b ∧
      (∀ c ∈ U, c ∈ Extended.initial) ∧
      Extended.bin 1 a b ∉ insert a (insert b U) ∧
      a ∈ U ∧ b ∈ U ∧
      Extended.Live true Extended.target 16 (insert (Extended.bin 1 a b) U) := by
  obtain ⟨U, a, b, d, hd, rfl, ha, hb, hab, fresh, tail⟩ := run
  have ha0 := raw a (by simp)
  have hb0 := raw b (by simp)
  have rawU : ∀ c ∈ U, c ∈ Extended.initial := by
    intro c hc
    exact raw c (by simp [hc])
  have hd1 : d = 1 := by
    by_contra hne
    have hb := initial_nonOr_bound hd hne ha0 hb0 hab fresh rawU tail
    norm_num at hb
  subst d
  have retained := Extended.initial_retained hd ha0 hb0 hab rawU tail
  exact ⟨U, a, b, ha0, hb0, hab, rawU, fresh, retained.1, retained.2, tail⟩

lemma nonNot_count_add (C : Circuit) :
    C.gates.countP (fun g => !Extended.isNot g) + PEqualNP.NotBracket.notCount C = C.size := by
  have sameNot :
      (fun g : Gate => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op GateOp.not)) =
        Extended.isNot := by
    funext g
    obtain ⟨op, operands⟩ := g
    cases op <;> rfl
  rw [PEqualNP.NotBracket.notCount, sameNot, ← List.countP_eq_length_filter]
  have negSame : (fun g : Gate => decide (¬ Extended.isNot g = true)) =
      (fun g => !Extended.isNot g) := by
    funext g
    cases Extended.isNot g <;> rfl
  have hc := List.length_eq_countP_add_countP Extended.isNot (l := C.gates)
  rw [negSame] at hc
  change _ + _ = C.gates.length
  omega

lemma canonical_one_not_trace (C : Circuit) (fan : FanInTwo C) (small : C.size ≤ 18)
    (oneNot : PEqualNP.NotBracket.notCount C = 1)
    (correct : ∀ x : Fin 10 → Bool,
      C.eval (List.ofFn x ++ [!(x 0)]) = Extended.f10 x) :
    ∃ S : Finset Extended.Sig,
      Extended.Live true Extended.target 17 S ∧ (∀ a ∈ S, a ∈ Extended.initial) := by
  let D := PrefixNot.addNotZero C
  have hfan : FanInTwo D := PrefixNot.fan_prefix C fan
  have hcorrect : ∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = Extended.f10 x := by
    intro x
    rw [PrefixNot.eval_prefix_ofFn]
    exact correct x
  have hs : D.size ≤ 19 := by
    rw [PrefixNot.size_prefix]
    omega
  have hn : PEqualNP.NotBracket.notCount D = 2 := by
    rw [PrefixNot.notCount_prefix, oneNot]
  have hb := nonNot_count_add D
  obtain ⟨k, S, hk, run, raw⟩ := Extended.realize D hfan hcorrect
  have hf := atLeastSeventeen run raw
  have heq : k = 17 := by omega
  subst k
  exact ⟨S, run, raw⟩

lemma canonical_one_not_first_or (C : Circuit) (fan : FanInTwo C) (small : C.size ≤ 18)
    (oneNot : PEqualNP.NotBracket.notCount C = 1)
    (correct : ∀ x : Fin 10 → Bool,
      C.eval (List.ofFn x ++ [!(x 0)]) = Extended.f10 x) :
    ∃ (U : Finset Extended.Sig) (a b : Extended.Sig),
      a ∈ Extended.initial ∧ b ∈ Extended.initial ∧ a ≠ b ∧
      (∀ c ∈ U, c ∈ Extended.initial) ∧
      Extended.bin 1 a b ∉ insert a (insert b U) ∧
      a ∈ U ∧ b ∈ U ∧
      Extended.Live true Extended.target 16 (insert (Extended.bin 1 a b) U) := by
  obtain ⟨S, run, raw⟩ := canonical_one_not_trace C fan small oneNot correct
  exact saturated_first_or run raw

end PEqualNP.Outside.L_meta_1884.TightTrace
