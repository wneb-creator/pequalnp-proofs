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

def notContribution (g : Gate) : ℕ :=
  match g.op with
  | GateOp.not => 1
  | _ => 0

def notCount (C : Circuit) : ℕ :=
  (C.gates.map notContribution).sum

lemma effectiveInputs_weight_le {g : Gate} (h : g.inputs.length ≤ 2) :
    (effectiveInputs g).length + notContribution g ≤ 2 := by
  cases g with
  | mk op inputs =>
    cases op <;> simp_all [effectiveInputs, notContribution, List.length_take]

lemma effectiveSlots_weight_le (C : Circuit) (hC : FanInTwo C) :
    (effectiveSlots C).length + notCount C ≤ 2 * C.size := by
  have bound (gs : List Gate) :
      (∀ g ∈ gs, g.inputs.length ≤ 2) →
      (gs.flatMap effectiveInputs).length + (gs.map notContribution).sum ≤
        2 * gs.length := by
    induction gs with
    | nil => simp
    | cons g gs ih =>
      intro h
      have hg := effectiveInputs_weight_le (h g (by simp))
      have ht := ih (fun k hk => h k (by simp [hk]))
      simp only [List.flatMap_cons, List.length_append, List.length_cons,
        List.map_cons, List.sum_cons]
      omega
  exact bound C.gates (fun g hg => (hC g hg).2)

lemma nonroot_count_sum (L : List ℕ) (n m a b : ℕ)
    (hgates : ∀ j < m, j ≠ a → j ≠ b → 1 ≤ L.count (n + j)) :
    m ≤ (∑ j ∈ Finset.range m, L.count (n + j)) + 2 := by
  have h := Finset.sum_le_sum (s := Finset.range m)
    (f := fun _ => 1)
    (g := fun j => L.count (n + j) + (if j = a then 1 else 0) +
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

lemma input_not_budget (C : Circuit) (a b : ℕ) (hC : FanInTwo C)
    (hgates : ∀ j < C.size, j ≠ a → j ≠ b →
      1 ≤ (effectiveSlots C).count (10 + j)) :
    (∑ i ∈ Finset.range 10, (effectiveSlots C).count i) + notCount C ≤
      C.size + 2 := by
  have hg := nonroot_count_sum (effectiveSlots C) 10 C.size a b hgates
  have ht := sum_count_le_length (Finset.range (10 + C.size)) (effectiveSlots C)
  rw [Finset.sum_range_add] at ht
  have hw := effectiveSlots_weight_le C hC
  omega

lemma single_use_not_budget (C : Circuit) (a b : ℕ) (hC : FanInTwo C)
    (hinputs : ∀ i < 10, 1 ≤ (effectiveSlots C).count i)
    (hgates : ∀ j < C.size, j ≠ a → j ≠ b →
      1 ≤ (effectiveSlots C).count (10 + j)) :
    notCount C + 18 ≤ C.size +
      ((Finset.range 10).filter fun i => (effectiveSlots C).count i = 1).card := by
  have h := Finset.sum_le_sum (s := Finset.range 10)
    (f := fun _ => 2)
    (g := fun i => (effectiveSlots C).count i +
      if (effectiveSlots C).count i = 1 then 1 else 0) (by
        intro i hi
        have hp := hinputs i (Finset.mem_range.mp hi)
        split_ifs <;> omega)
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul,
    Finset.sum_add_distrib, Finset.sum_boole] at h
  norm_num at h
  have hb := input_not_budget C a b hC hgates
  omega

lemma two_root_exact_counts (L : List ℕ) (a b : Fin 18) (hab : a ≠ b)
    (hlen : L.length ≤ 36)
    (hinputs : ∀ i < 10, 2 ≤ L.count i)
    (hgates : ∀ j < 18, j ≠ a.val → j ≠ b.val → 1 ≤ L.count (10 + j)) :
    (∀ i < 10, L.count i = 2) ∧
    (∀ j < 18, L.count (10 + j) = if j = a.val ∨ j = b.val then 0 else 1) ∧
    (∀ i, 28 ≤ i → L.count i = 0) := by
  classical
  have habv : a.val ≠ b.val := fun h => hab (Fin.ext h)
  let w : ℕ → ℕ := fun i =>
    if i < 10 then 2 else if i = 10 + a.val ∨ i = 10 + b.val then 0 else 1
  let q : ℕ → ℕ := fun j => if j = a.val ∨ j = b.val then 0 else 1
  have hq (j : ℕ) :
      q j + (if j = a.val then 1 else 0) + (if j = b.val then 1 else 0) = 1 := by
    by_cases ha : j = a.val
    · have hb : j ≠ b.val := by omega
      simp [q, ha, habv]
    · by_cases hb : j = b.val <;> simp [q, ha, hb, Ne.symm habv]
  have hqsum : ∑ j ∈ Finset.range 18, q j = 16 := by
    have hs := Finset.sum_congr (s₁ := Finset.range 18) rfl (fun j _ => hq j)
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      smul_eq_mul, mul_one, Finset.sum_ite_eq'] at hs
    simp only [Finset.mem_range, a.isLt, b.isLt, ite_true] at hs
    omega
  have hwsum : ∑ i ∈ Finset.range 28, w i = 36 := by
    rw [show 28 = 10 + 18 by omega, Finset.sum_range_add]
    have hfirst : ∑ i ∈ Finset.range 10, w i = 20 := by
      calc
        _ = ∑ _i ∈ Finset.range 10, 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          simp [w, Finset.mem_range.mp hi]
        _ = 20 := by simp
    have hsecond : ∑ j ∈ Finset.range 18, w (10 + j) = 16 := by
      rw [← hqsum]
      apply Finset.sum_congr rfl
      intro j _
      simp [w, q]
    omega
  have hwle : ∀ i ∈ Finset.range 28, w i ≤ L.count i := by
    intro i hi
    by_cases hlo : i < 10
    · simpa [w, hlo] using hinputs i hlo
    · by_cases hr : i = 10 + a.val ∨ i = 10 + b.val
      · simp [w, hlo, hr]
      · have hiz : i = 10 + (i - 10) := by omega
        have hi28 : i < 28 := Finset.mem_range.mp hi
        have ht := hgates (i - 10) (by omega) (by omega) (by omega)
        simpa [w, hlo, hr, ← hiz] using ht
  have hcountsum : ∑ i ∈ Finset.range 28, L.count i = 36 := by
    have hlow := Finset.sum_le_sum hwle
    have hupp := sum_count_le_length (Finset.range 28) L
    omega
  have heq : ∀ i ∈ Finset.range 28, w i = L.count i :=
    (Finset.sum_eq_sum_iff_of_le hwle).mp (hwsum.trans hcountsum.symm)
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have h := heq i (Finset.mem_range.mpr (by omega))
    simpa [w, hi] using h.symm
  · intro j hj
    have h := heq (10 + j) (Finset.mem_range.mpr (by omega))
    simpa [w] using h.symm
  · intro i hi
    have hout : i ∉ Finset.range 28 := by simpa using hi
    have h := sum_count_le_length (insert i (Finset.range 28)) L
    rw [Finset.sum_insert hout, hcountsum] at h
    omega

lemma two_root_usage_rigidity (C : PEqualNP.CircuitLowerBounds.Circuit)
    (a b : Fin 18) (hab : a ≠ b)
    (hC : PEqualNP.MetaComplexity.FanInTwo C) (hsize : C.size ≤ 18)
    (hinputs : ∀ i < 10, 2 ≤ (effectiveSlots C).count i)
    (hgates : ∀ j < C.size, j ≠ a.val → j ≠ b.val →
      1 ≤ (effectiveSlots C).count (10 + j)) :
    (∀ i < 10, (effectiveSlots C).count i = 2) ∧
    (∀ j < 18, (effectiveSlots C).count (10 + j) =
      if j = a.val ∨ j = b.val then 0 else 1) ∧
    (∀ i, 28 ≤ i → (effectiveSlots C).count i = 0) := by
  have hs := (two_root_gate_rigidity C a.val b.val hC hsize hinputs hgates).1
  have hlen : (effectiveSlots C).length ≤ 36 := by
    have := effectiveSlots_length_le C hC
    omega
  exact two_root_exact_counts (effectiveSlots C) a b hab hlen hinputs
    (fun j hj ha hb => hgates j (by omega) ha hb)

end PEqualNP.Outside.L_meta_3821_aux
