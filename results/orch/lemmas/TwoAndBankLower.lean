import TwoAndBank
import TwoZeroInfluence

namespace PEqualNP.Outside.L_meta_2373.Live1024.TwoAndBank
open LiftSeventeen

lemma and_bit (a b : Fin 10) (r : Row) :
    bit r (andCol a b) = (bit r (input a) && bit r (input b)) := by
  rw [andCol, bit_bin_eq_boolBin]
  rfl

lemma retained_left (a b c d : Fin 10) (ab : a ≠ b) (cd : c ≠ d)
    {S : Finset Sig} {k : Nat} (sub : S ⊆ bank a b c d) (run : Live false graph k S) :
    input a ∈ S := by
  obtain ⟨e, ae, ec⟩ : ∃ e : Fin 10, a ≠ e ∧ (e = c ∨ e = d) := by
    by_cases ac : a = c
    · subst a
      exact ⟨d, cd, Or.inr rfl⟩
    · exact ⟨c, ac, Or.inl rfl⟩
  obtain ⟨r, s, same, rb, sb, re, se, different⟩ := two_zero_influence_rows a b e ab ae
  have h1r : bit r (andCol a b) = false := by rw [and_bit, rb]; simp
  have h1s : bit s (andCol a b) = false := by rw [and_bit, sb]; simp
  have other (t : Row) (off : bit t (input e) = false) : bit t (andCol c d) = false := by
    rw [and_bit]
    rcases ec with rfl | rfl <;> rw [off] <;> simp only [Bool.false_and, Bool.and_false]
  have h2r := other r re
  have h2s := other s se
  by_contra missing
  obtain ⟨w, hw, diff⟩ := live_row_difference run different
  have mem := sub hw
  rcases Finset.mem_insert.mp mem with rfl | mem
  · exact diff (h1r.trans h1s.symm)
  rcases Finset.mem_insert.mp mem with rfl | mem
  · apply diff
    rw [neg_bit, neg_bit, h1r, h1s]
  rcases Finset.mem_insert.mp mem with rfl | mem
  · exact diff (h2r.trans h2s.symm)
  rcases Finset.mem_insert.mp mem with rfl | mem
  · apply diff
    rw [neg_bit, neg_bit, h2r, h2s]
  · obtain ⟨i, rfl⟩ := input_index w (List.mem_toFinset.mp mem)
    exact diff (same i (by rintro rfl; exact missing hw))

lemma used_left_lower (a b c d : Fin 10) (ab : a ≠ b) (cd : c ≠ d)
    {S : Finset Sig} {k : Nat} (sub : S ⊆ bank a b c d) (run : Live false graph k S)
    (used : andCol a b ∈ S ∨ neg (andCol a b) ∈ S) : 16 ≤ k := by
  have ha := retained_left a b c d ab cd sub run
  have ca : Constant (projected (rowMap a) (input a)) := ⟨false, funext (rowMap_missing a)⟩
  apply paid_tail_lower a b c d sub run
  rcases used with h | h
  · exact ⟨input a, ha, andCol a b, h, (input_distinct a b ab).1, ca, ⟨false, and_zero a b⟩⟩
  · exact ⟨input a, ha, neg (andCol a b), h, (input_distinct a b ab).2, ca, ⟨true, neg_and_one a b⟩⟩

lemma bank_swap (a b c d : Fin 10) : bank a b c d = bank c d a b := by
  ext w
  simp [bank, or_assoc, or_left_comm, or_comm]

lemma positive_tail_lower (a b c d : Fin 10) (ab : a ≠ b) (cd : c ≠ d)
    {S : Finset Sig} {k : Nat} (sub : S ⊆ bank a b c d) (run : Live false graph k S) : 16 ≤ k := by
  by_cases leftUsed : andCol a b ∈ S ∨ neg (andCol a b) ∈ S
  · exact used_left_lower a b c d ab cd sub run leftUsed
  by_cases rightUsed : andCol c d ∈ S ∨ neg (andCol c d) ∈ S
  · exact used_left_lower c d a b cd ab (bank_swap a b c d ▸ sub) run rightUsed
  have subset : ∀ w ∈ S, w ∈ inputs := by
    intro w hw
    have mem := sub hw
    rcases Finset.mem_insert.mp mem with eq | mem
    · exact False.elim (leftUsed (Or.inl (eq ▸ hw)))
    rcases Finset.mem_insert.mp mem with eq | mem
    · exact False.elim (leftUsed (Or.inr (eq ▸ hw)))
    rcases Finset.mem_insert.mp mem with eq | mem
    · exact False.elim (rightUsed (Or.inl (eq ▸ hw)))
    rcases Finset.mem_insert.mp mem with eq | mem
    · exact False.elim (rightUsed (Or.inr (eq ▸ hw)))
    · exact List.mem_toFinset.mp mem
  have eq : S = inputs.toFinset := by
    ext w
    constructor
    · exact fun hw => List.mem_toFinset.mpr (subset w hw)
    · intro hw
      obtain ⟨i, rfl⟩ := input_index w (List.mem_toFinset.mp hw)
      apply raw_required run inputs (input i) subset (absentRow i) (presentRow i) (requiredInputs.1 i)
      intro v hv hn
      obtain ⟨j, rfl⟩ := input_index v hv
      apply requiredInputs.2 i j
      rintro rfl
      exact hn rfl
  have bound := live_lower_seventeen (live_up (eq ▸ run))
  omega

end PEqualNP.Outside.L_meta_2373.Live1024.TwoAndBank
