import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3821_aux

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

def effectiveInputs (g : Gate) : List ℕ :=
  match g.op with
  | GateOp.not => g.inputs.take 1
  | _ => g.inputs

def effectiveSlots (C : Circuit) : List ℕ :=
  C.gates.flatMap effectiveInputs

lemma effectiveInputs_length_le {g : Gate}
    (h : g.inputs.length ≤ 2) : (effectiveInputs g).length ≤ 2 := by
  cases g with
  | mk op inputs =>
    cases op <;> simp_all [effectiveInputs, List.length_take]

lemma effective_flatMap_length_le (gs : List Gate)
    (h : ∀ g ∈ gs, (effectiveInputs g).length ≤ 2) :
    (gs.flatMap effectiveInputs).length ≤ 2 * gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have hg := h g (by simp)
    have ht := ih (fun k hk => h k (by simp [hk]))
    omega

lemma effectiveSlots_length_le (C : Circuit) (hC : FanInTwo C) :
    (effectiveSlots C).length ≤ 2 * C.size :=
  effective_flatMap_length_le C.gates
    (fun g hg => effectiveInputs_length_le (hC g hg).2)

lemma effective_flatMap_length_eq (gs : List Gate)
    (h : ∀ g ∈ gs, (effectiveInputs g).length ≤ 2)
    (heq : (gs.flatMap effectiveInputs).length = 2 * gs.length) :
    ∀ g ∈ gs, (effectiveInputs g).length = 2 := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have hg := h g (by simp)
    have ht : ∀ k ∈ gs, (effectiveInputs k).length ≤ 2 :=
      fun k hk => h k (by simp [hk])
    have htb := effective_flatMap_length_le gs ht
    simp only [List.flatMap_cons, List.length_append, List.length_cons] at heq
    have hge : (effectiveInputs g).length = 2 := by omega
    have hte : (gs.flatMap effectiveInputs).length = 2 * gs.length := by omega
    intro k hk
    rcases List.mem_cons.mp hk with rfl | hk
    · exact hge
    · exact ih ht hte k hk

lemma sum_count_le_length (s : Finset ℕ) (L : List ℕ) :
    (∑ i ∈ s, L.count i) ≤ L.length := by
  classical
  induction L with
  | nil => simp
  | cons x xs ih =>
    simp only [List.count_cons, List.length_cons]
    simp only [Finset.sum_add_distrib]
    by_cases hx : x ∈ s
    · simpa [hx] using Nat.add_le_add_right ih 1
    · simpa [hx] using Nat.le_succ_of_le ih

lemma two_root_count (L : List ℕ) (m a b : ℕ)
    (hinputs : ∀ i < 10, 2 ≤ L.count i)
    (hgates : ∀ j < m, j ≠ a → j ≠ b → 1 ≤ L.count (10 + j)) :
    m + 18 ≤ L.length := by
  have hinputSum : 20 ≤ ∑ i ∈ Finset.range 10, L.count i := by
    calc
      20 = ∑ _i ∈ Finset.range 10, 2 := by simp
      _ ≤ ∑ i ∈ Finset.range 10, L.count i :=
        Finset.sum_le_sum (fun i hi => hinputs i (Finset.mem_range.mp hi))
  have hgateSum : m ≤ (∑ j ∈ Finset.range m, L.count (10 + j)) + 2 := by
    have h := Finset.sum_le_sum (s := Finset.range m)
      (f := fun _ => 1)
      (g := fun j => L.count (10 + j) + (if j = a then 1 else 0) +
        (if j = b then 1 else 0)) (by
          intro j hj
          by_cases ha : j = a
          · simp [ha]
            omega
          by_cases hb : j = b
          · simp [hb]
          simpa [ha, hb] using hgates j (Finset.mem_range.mp hj) ha hb)
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      smul_eq_mul, mul_one, Finset.sum_ite_eq'] at h
    split_ifs at h <;> omega
  have htotal := sum_count_le_length (Finset.range (10 + m)) L
  rw [Finset.sum_range_add] at htotal
  omega

lemma two_root_gate_lower_bound (C : Circuit) (a b : ℕ)
    (hC : FanInTwo C)
    (hinputs : ∀ i < 10, 2 ≤ (effectiveSlots C).count i)
    (hgates : ∀ j < C.size, j ≠ a → j ≠ b →
      1 ≤ (effectiveSlots C).count (10 + j)) :
    18 ≤ C.size := by
  have h := two_root_count (effectiveSlots C) C.size a b hinputs hgates
  have hb := effectiveSlots_length_le C hC
  omega

lemma two_root_gate_rigidity (C : Circuit) (a b : ℕ)
    (hC : FanInTwo C) (hsize : C.size ≤ 18)
    (hinputs : ∀ i < 10, 2 ≤ (effectiveSlots C).count i)
    (hgates : ∀ j < C.size, j ≠ a → j ≠ b →
      1 ≤ (effectiveSlots C).count (10 + j)) :
    C.size = 18 ∧ ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
  have h := two_root_count (effectiveSlots C) C.size a b hinputs hgates
  have hb := effectiveSlots_length_le C hC
  have hsizeEq : C.size = 18 := by omega
  have hslotsEq : (effectiveSlots C).length = 2 * C.size := by omega
  refine ⟨hsizeEq, ?_⟩
  intro g hg
  have hgEq := effective_flatMap_length_eq C.gates
    (fun g hg => effectiveInputs_length_le (hC g hg).2) hslotsEq g hg
  have hlegal := (hC g hg).1
  cases g with
  | mk op inputs =>
    cases op <;> simp_all [effectiveInputs, List.length_take]
    omega

lemma small_two_root_has_single_use (C : Circuit) (a b : ℕ)
    (hC : FanInTwo C) (hsize : C.size ≤ 17)
    (hgates : ∀ j < C.size, j ≠ a → j ≠ b →
      1 ≤ (effectiveSlots C).count (10 + j)) :
    ∃ i < 10, (effectiveSlots C).count i ≤ 1 := by
  by_contra h
  push Not at h
  have hinputs : ∀ i < 10, 2 ≤ (effectiveSlots C).count i := by
    intro i hi
    have := h i hi
    omega
  have := two_root_gate_lower_bound C a b hC hinputs hgates
  omega

lemma not_gate_forces_single_use (C : Circuit) (a b : ℕ)
    (hC : FanInTwo C) (hsize : C.size ≤ 18)
    (hgates : ∀ j < C.size, j ≠ a → j ≠ b →
      1 ≤ (effectiveSlots C).count (10 + j))
    (hnot : ∃ g ∈ C.gates, g.op = GateOp.not) :
    ∃ i < 10, (effectiveSlots C).count i ≤ 1 := by
  by_contra h
  push Not at h
  have hinputs : ∀ i < 10, 2 ≤ (effectiveSlots C).count i := by
    intro i hi
    have := h i hi
    omega
  obtain ⟨g, hg, hop⟩ := hnot
  have hrigid := (two_root_gate_rigidity C a b hC hsize hinputs hgates).2 g hg
  rcases hrigid.1 with h | h <;> simp_all

end PEqualNP.Outside.L_meta_3821_aux
