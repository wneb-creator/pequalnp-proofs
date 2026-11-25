import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2590_aux.PetersenReaders

open PEqualNP.CircuitLowerBounds
open scoped BigOperators

lemma input_count_sum (n : Nat) (xs : List Nat) :
    (∑ i ∈ Finset.range n, xs.count i) =
      (xs.filter fun i => decide (i < n)).length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.count_cons, Finset.sum_add_distrib, ih]
    have h : (∑ i ∈ Finset.range n, if a == i then (1 : Nat) else 0) =
        if a < n then 1 else 0 := by
      simp [beq_iff_eq, Finset.sum_ite_eq', Finset.mem_range]
    rw [h]
    by_cases ha : a < n <;> simp [ha]

lemma flat_length (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length = 2) :
    (gs.flatMap Gate.inputs).length = 2 * gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    rw [h g List.mem_cons_self, ih (fun g hg => h g (List.mem_cons_of_mem _ hg))]
    omega

lemma no_fanout_of_double_inputs (C : Circuit)
    (size : C.size ≤ 19)
    (fanin : ∀ g ∈ C.gates, g.inputs.length = 2)
    (live : ∀ j < C.size, 10 + j ∈ C.output :: C.gates.flatMap Gate.inputs)
    (inputs : ∀ i : Fin 10, 2 ≤ (C.gates.flatMap Gate.inputs).count i.val) :
    ((C.output :: C.gates.flatMap Gate.inputs).filter fun i => decide (10 ≤ i)).Nodup := by
  let reads := C.output :: C.gates.flatMap Gate.inputs
  let inner := reads.filter fun i => decide (10 ≤ i)
  have hinput : 20 ≤ (reads.filter fun i => decide (i < 10)).length := by
    rw [← input_count_sum]
    have low : (∑ i ∈ Finset.range 10, (2 : Nat)) ≤
        ∑ i ∈ Finset.range 10, reads.count i := by
      apply Finset.sum_le_sum
      intro i hi
      have hh := inputs ⟨i,Finset.mem_range.mp hi⟩
      simp only [reads,List.count_cons]
      omega
    simpa using low
  have whole : reads.length = 2 * C.size + 1 := by
    simp only [reads,List.length_cons,flat_length C.gates fanin,Circuit.size]
  have partition : reads.length =
      (reads.filter fun i => decide (i < 10)).length + inner.length := by
    simpa only [inner, Bool.not_decide, Nat.not_lt] using
      List.length_eq_length_filter_add (l := reads) (fun i => decide (i < 10))
  have upper : inner.length ≤ C.size := by omega
  have subset : Finset.Ico 10 (10 + C.size) ⊆ inner.toFinset := by
    intro w hw
    obtain ⟨lo,hi⟩ := Finset.mem_Ico.mp hw
    have member := live (w - 10) (by omega)
    have eq : 10 + (w - 10) = w := by omega
    rw [eq] at member
    exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨member, by simpa using lo⟩)
  have lower : C.size ≤ inner.toFinset.card := by
    have hh := Finset.card_le_card subset
    simpa using hh
  have card : inner.toFinset.card = inner.length := by
    have hh := List.toFinset_card_le inner
    omega
  have nodup : (inner : Multiset Nat).Nodup :=
    Multiset.toFinset_card_eq_card_iff_nodup.mp card
  exact nodup

lemma single_input_of_no_formula (C : Circuit)
    (size : C.size ≤ 19)
    (fanin : ∀ g ∈ C.gates, g.inputs.length = 2)
    (live : ∀ j < C.size, 10 + j ∈ C.output :: C.gates.flatMap Gate.inputs)
    (obstruction : ((C.output :: C.gates.flatMap Gate.inputs).filter
      fun i => decide (10 ≤ i)).Nodup → False) :
    ∃ i : Fin 10, (C.gates.flatMap Gate.inputs).count i.val ≤ 1 := by
  by_contra! repeated
  exact obstruction (no_fanout_of_double_inputs C size fanin live (fun i => by
    have h := repeated i
    omega))

end PEqualNP.Outside.L_meta_2590_aux.PetersenReaders
