import OneForcedBank

namespace PEqualNP.Outside.L_meta_2373.Live1024.NotOrBank
open PEqualNP.Outside.L_meta_2373 LiftSeventeen OneForcedBank OneNotFirstAnd

def source (edge : Bool) : Sig := bin 1 (input 0) (input (if edge then 1 else 2))

def positiveRow (edge : Bool) (i : Fin 10) : Row :=
  Fin.ofNat 1024 ((if edge then ![19,7,6,12,24,33,66,132,264,528]
    else ![21,3,13,12,24,33,66,132,264,528]) i)

def negativeRow (edge : Bool) (i : Fin 10) : Row :=
  Fin.ofNat 1024 ((if edge then ![18,5,2,4,8,1,2,4,8,16]
    else ![20,1,9,4,8,1,2,4,8,16]) i)

set_option maxHeartbeats 1000000 in
lemma separating_rows : ∀ edge : Bool, ∀ i : Fin 10,
    bit (positiveRow edge i) graph = true ∧ bit (negativeRow edge i) graph = false ∧
    bit (positiveRow edge i) (source edge) = bit (negativeRow edge i) (source edge) ∧
    ∀ j : Fin 10, i ≠ j →
      bit (positiveRow edge i) (input j) = bit (negativeRow edge i) (input j) := by
  intro edge i
  cases edge <;> fin_cases i <;> decide +kernel

theorem inputs_retained (edge : Bool) {S : Finset Sig} {k : Nat}
    (sub : S ⊆ OneNotForcedPair.bank (source edge)) (run : Live false graph k S) :
    inputs.toFinset ⊆ S := by
  intro v member
  obtain ⟨i, rfl⟩ := input_index v (List.mem_toFinset.mp member)
  by_contra absent
  have values := separating_rows edge i
  have ordered : ∀ w ∈ S,
      bit (positiveRow edge i) w = true → bit (negativeRow edge i) w = true := by
    intro w hw
    have available := sub hw
    rcases Finset.mem_insert.mp available with rfl | available
    · rw [values.2.2.1]
      exact id
    rcases Finset.mem_insert.mp available with rfl | available
    · simp only [neg_bit]
      rw [values.2.2.1]
      exact id
    · obtain ⟨j, rfl⟩ := input_index w (List.mem_toFinset.mp available)
      have distinct : i ≠ j := by
        rintro rfl
        exact absent hw
      rw [values.2.2.2 j distinct]
      exact id
  have impossible := live_row_order run (positiveRow edge i) (negativeRow edge i)
    ordered values.1
  rw [values.2.1] at impossible
  cases impossible

theorem used_bank_cases (edge : Bool) {S : Finset Sig} {k : Nat}
    (sub : S ⊆ OneNotForcedPair.bank (source edge))
    (used : neg (source edge) ∈ S) (run : Live false graph k S) :
    S = insert (neg (source edge)) inputs.toFinset ∨
      S = OneNotForcedPair.bank (source edge) := by
  have roots := inputs_retained edge sub run
  by_cases retained : source edge ∈ S
  · right
    apply Finset.Subset.antisymm sub
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact retained
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact used
    · exact roots hw
  · left
    apply Finset.Subset.antisymm
    · intro w hw
      have available := sub hw
      rcases Finset.mem_insert.mp available with rfl | available
      · exact False.elim (retained hw)
      · exact available
    · intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact used
      · exact roots hw

set_option maxHeartbeats 1000000 in
lemma bank_cardinalities : ∀ edge : Bool,
    (OneNotForcedPair.bank (source edge)).card = 12 ∧
      (insert (neg (source edge)) inputs.toFinset).card = 11 := by
  decide +kernel

end PEqualNP.Outside.L_meta_2373.Live1024.NotOrBank
