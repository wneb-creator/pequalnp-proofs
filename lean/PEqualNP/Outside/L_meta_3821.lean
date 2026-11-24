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

open PEqualNP.CircuitLowerBounds

abbrev FormulaTree := BinaryTree (Sum (Fin 10) Bool)

def formulaValue (x : Fin 10 → Bool) : FormulaTree → Bool
  | .nil => false
  | .node (.inl i) _ _ => x i
  | .node (.inr false) l r => formulaValue x l && formulaValue x r
  | .node (.inr true) l r => formulaValue x l || formulaValue x r

def formulaCount (i : Fin 10) : FormulaTree → ℕ
  | .nil => 0
  | .node (.inl j) _ _ => if i = j then 1 else 0
  | .node (.inr _) l r => formulaCount i l + formulaCount i r

def inputTrees : List FormulaTree :=
  List.ofFn (fun i : Fin 10 => BinaryTree.node (.inl i) .nil .nil)

def gateTree (g : Gate) (w : List FormulaTree) : FormulaTree :=
  match g.op with
  | .and => .node (.inr false) (w.getD (g.inputs.getD 0 0) .nil)
      (w.getD (g.inputs.getD 1 0) .nil)
  | .or => .node (.inr true) (w.getD (g.inputs.getD 0 0) .nil)
      (w.getD (g.inputs.getD 1 0) .nil)
  | _ => .nil

def unfoldTrees : List Gate → List FormulaTree → List FormulaTree
  | [], w => w
  | g :: gs, w => unfoldTrees gs (w ++ [gateTree g w])

lemma binary_inputs (g : Gate) (h : g.inputs.length = 2) :
    ∃ a b, g.inputs = [a, b] := by
  rcases g with ⟨op, inputs⟩
  cases inputs with
  | nil => simp at h
  | cons a inputs =>
    cases inputs with
    | nil => simp at h
    | cons b inputs =>
      have : inputs = [] := by simpa using h
      exact ⟨a, b, by simp [this]⟩

lemma gateTree_value (x : Fin 10 → Bool) (g : Gate) (w : List FormulaTree)
    (hop : g.op = .and ∨ g.op = .or) (hlen : g.inputs.length = 2) :
    formulaValue x (gateTree g w) =
      g.op.eval (g.inputs.map fun i => (w.map (formulaValue x)).getD i false) := by
  obtain ⟨a, b, hab⟩ := binary_inputs g hlen
  have get (j : ℕ) :
      (w.map (formulaValue x)).getD j false = formulaValue x (w.getD j .nil) :=
    List.getD_map w .nil (formulaValue x)
  simp_rw [get]
  rcases hop with hop | hop <;>
    simp [gateTree, hop, hab, formulaValue, GateOp.eval]

lemma unfoldTrees_value (x : Fin 10 → Bool) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2)
    (w : List FormulaTree) :
    (unfoldTrees gs w).map (formulaValue x) =
      gs.foldl (fun p g => p ++ [g.op.eval (g.inputs.map fun i => p.getD i false)])
        (w.map (formulaValue x)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [unfoldTrees, ih (fun k hk => hg k (List.mem_cons_of_mem _ hk))]
    simp only [List.foldl_cons, List.map_append, List.map_cons, List.map_nil]
    rw [gateTree_value x g w (hg g List.mem_cons_self).1 (hg g List.mem_cons_self).2]

lemma unfoldTrees_prefix (gs : List Gate) (w : List FormulaTree) :
    ∃ tail, unfoldTrees gs w = w ++ tail := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp [unfoldTrees]⟩
  | cons g gs ih =>
    obtain ⟨tail, ht⟩ := ih (w ++ [gateTree g w])
    exact ⟨gateTree g w :: tail, by simpa [unfoldTrees, List.append_assoc] using ht⟩

lemma formulaCount_getD_append_le (i : Fin 10) (w tail : List FormulaTree) (j : ℕ) :
    formulaCount i (w.getD j .nil) ≤ formulaCount i ((w ++ tail).getD j .nil) := by
  by_cases hj : j < w.length
  · rw [List.getD_append _ _ _ _ hj]
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hj)]
    exact Nat.zero_le _

lemma gateTree_count_le (i : Fin 10) (g : Gate) (w final : List FormulaTree)
    (hop : g.op = .and ∨ g.op = .or) (hlen : g.inputs.length = 2)
    (hprefix : ∃ tail, final = w ++ tail) :
    formulaCount i (gateTree g w) ≤
      (g.inputs.map fun j => formulaCount i (final.getD j .nil)).sum := by
  obtain ⟨a, b, hab⟩ := binary_inputs g hlen
  obtain ⟨tail, rfl⟩ := hprefix
  have ha := formulaCount_getD_append_le i w tail a
  have hb := formulaCount_getD_append_le i w tail b
  rcases hop with hop | hop <;>
    simpa [gateTree, hop, hab, formulaCount] using Nat.add_le_add ha hb

lemma unfoldTrees_count_le (i : Fin 10) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2)
    (w : List FormulaTree) :
    ((unfoldTrees gs w).map (formulaCount i)).sum ≤
      (w.map (formulaCount i)).sum +
      ((gs.flatMap Gate.inputs).map fun j =>
        formulaCount i ((unfoldTrees gs w).getD j .nil)).sum := by
  induction gs generalizing w with
  | nil => simp [unfoldTrees]
  | cons g gs ih =>
    have ht := ih (fun k hk => hg k (List.mem_cons_of_mem _ hk)) (w ++ [gateTree g w])
    have hhead := gateTree_count_le i g w (unfoldTrees (g :: gs) w)
      (hg g List.mem_cons_self).1 (hg g List.mem_cons_self).2 (unfoldTrees_prefix _ _)
    simp only [unfoldTrees, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero] at ht hhead ⊢
    simp only [List.flatMap_cons, List.map_append, List.sum_append]
    omega

lemma unfoldTrees_length (gs : List Gate) (w : List FormulaTree) :
    (unfoldTrees gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [unfoldTrees]
  | cons g gs ih =>
    simp only [unfoldTrees, ih, List.length_append, List.length_cons, List.length_nil]
    omega

lemma weighted_count_sum (L : List ℕ) (f : ℕ → ℕ) (s : Finset ℕ)
    (hmem : ∀ i ∈ L, i ∈ s) :
    (L.map f).sum = ∑ i ∈ s, L.count i * f i := by
  classical
  rw [Finset.sum_list_map_count]
  simp only [nsmul_eq_mul]
  apply Finset.sum_subset
  · intro i hi
    exact hmem i (List.mem_toFinset.mp hi)
  · intro i hi hnot
    have hn : i ∉ L := by simpa using hnot
    simp [List.count_eq_zero.mpr hn]

lemma list_map_sum_range {α : Type} (w : List α) (f : α → ℕ) (d : α) :
    (w.map f).sum = ∑ i ∈ Finset.range w.length, f (w.getD i d) := by
  induction w with
  | nil => simp
  | cons a w ih =>
    simpa [Finset.sum_range_succ', Nat.add_comm] using congrArg (fun x => f a + x) ih

lemma two_root_weighted_count (L : List ℕ) (a b : Fin 18) (hab : a ≠ b)
    (hlen : L.length ≤ 36)
    (hinputs : ∀ i < 10, 2 ≤ L.count i)
    (hgates : ∀ j < 18, j ≠ a.val → j ≠ b.val → 1 ≤ L.count (10 + j))
    (f : ℕ → ℕ) :
    (L.map f).sum + f (10 + a.val) + f (10 + b.val) =
      2 * (∑ i ∈ Finset.range 10, f i) + ∑ j ∈ Finset.range 18, f (10 + j) := by
  classical
  obtain ⟨hi, hg, ho⟩ := two_root_exact_counts L a b hab hlen hinputs hgates
  have hm : ∀ i ∈ L, i ∈ Finset.range 28 := by
    intro i him
    have hp : 0 < L.count i := List.count_pos_iff.mpr him
    have := ho i
    simp only [Finset.mem_range]
    omega
  rw [weighted_count_sum L f (Finset.range 28) hm]
  rw [show 28 = 10 + 18 by omega, Finset.sum_range_add]
  have hfirst : ∑ i ∈ Finset.range 10, L.count i * f i =
      2 * ∑ i ∈ Finset.range 10, f i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i him => by rw [hi i (Finset.mem_range.mp him)])
  have hpoint (j : ℕ) (hj : j < 18) :
      L.count (10 + j) * f (10 + j) +
        (if j = a.val then f (10 + a.val) else 0) +
        (if j = b.val then f (10 + b.val) else 0) = f (10 + j) := by
    have habv : a.val ≠ b.val := fun h => hab (Fin.ext h)
    rw [hg j hj]
    by_cases ha : j = a.val
    · simp [ha, habv]
    · by_cases hb : j = b.val <;> simp [ha, hb, Ne.symm habv]
  have hsum := Finset.sum_congr (s₁ := Finset.range 18) rfl
    (fun j hj => hpoint j (Finset.mem_range.mp hj))
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_range,
    a.isLt, b.isLt, ite_true] at hsum
  omega

lemma inputTrees_count (i : Fin 10) : (inputTrees.map (formulaCount i)).sum = 1 := by
  fin_cases i <;> decide

lemma effectiveSlots_eq_inputs (C : Circuit)
    (hop : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or) :
    effectiveSlots C = C.gates.flatMap Gate.inputs := by
  unfold effectiveSlots
  have h (gs : List Gate) (hs : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
      gs.flatMap effectiveInputs = gs.flatMap Gate.inputs := by
    induction gs with
    | nil => rfl
    | cons g gs ih =>
      have ht := ih (fun k hk => hs k (List.mem_cons_of_mem _ hk))
      have hg := hs g List.mem_cons_self
      rcases hg with hg | hg <;> simp [List.flatMap_cons, effectiveInputs, hg, ht]
  exact h C.gates hop

def circuitFormula (C : Circuit) (a b : ℕ) : FormulaTree :=
  let w := unfoldTrees C.gates inputTrees
  .node (.inr true) (w.getD a .nil) (w.getD b .nil)

lemma circuitFormula_value (C : Circuit) (a b : ℕ)
    (hg : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2)
    (x : Fin 10 → Bool) :
    formulaValue x (circuitFormula C a b) =
      ((C.wires (List.ofFn x)).getD a false || (C.wires (List.ofFn x)).getD b false) := by
  have h := unfoldTrees_value x C.gates hg inputTrees
  have hi : inputTrees.map (formulaValue x) = List.ofFn x := by
    simp [inputTrees, formulaValue]
  rw [hi] at h
  change (unfoldTrees C.gates inputTrees).map (formulaValue x) = C.wires (List.ofFn x) at h
  rw [← h]
  change (formulaValue x ((unfoldTrees C.gates inputTrees).getD a .nil) ||
      formulaValue x ((unfoldTrees C.gates inputTrees).getD b .nil)) = _
  have get (j : ℕ) :
      ((unfoldTrees C.gates inputTrees).map (formulaValue x)).getD j false =
        formulaValue x ((unfoldTrees C.gates inputTrees).getD j .nil) :=
    List.getD_map _ .nil (formulaValue x)
  rw [get a, get b]

lemma circuitFormula_count_le_two (C : Circuit) (a b : Fin 18) (hab : a ≠ b)
    (hC : PEqualNP.MetaComplexity.FanInTwo C) (hsize : C.size ≤ 18)
    (hinputs : ∀ i < 10, 2 ≤ (effectiveSlots C).count i)
    (hgates : ∀ j < C.size, j ≠ a.val → j ≠ b.val →
      1 ≤ (effectiveSlots C).count (10 + j))
    (i : Fin 10) :
    formulaCount i (circuitFormula C (10 + a.val) (10 + b.val)) ≤ 2 := by
  obtain ⟨hsizeEq, hbinary⟩ := two_root_gate_rigidity C a.val b.val hC hsize hinputs hgates
  let w := unfoldTrees C.gates inputTrees
  let f : ℕ → ℕ := fun j => formulaCount i (w.getD j .nil)
  have hmass := unfoldTrees_count_le i C.gates hbinary inputTrees
  have heff := effectiveSlots_eq_inputs C (fun g hg => (hbinary g hg).1)
  rw [← heff, inputTrees_count] at hmass
  change (w.map (formulaCount i)).sum ≤ 1 + ((effectiveSlots C).map f).sum at hmass
  have hlen : w.length = 28 := by
    simp only [w, unfoldTrees_length, inputTrees, List.length_ofFn]
    change 10 + C.size = 28
    omega
  have hfirst : ∑ j ∈ Finset.range 10, f j = 1 := by
    obtain ⟨tail, htail⟩ := unfoldTrees_prefix C.gates inputTrees
    have ht : w = inputTrees ++ tail := htail
    calc
      _ = ∑ j ∈ Finset.range 10, formulaCount i (inputTrees.getD j .nil) := by
        apply Finset.sum_congr rfl
        intro j hj
        dsimp [f]
        rw [ht, List.getD_append _ _ _ _ (by simpa [inputTrees] using Finset.mem_range.mp hj)]
      _ = (inputTrees.map (formulaCount i)).sum := by
        rw [list_map_sum_range inputTrees (formulaCount i) .nil]
        simp [inputTrees]
      _ = 1 := inputTrees_count i
  have hfull : (w.map (formulaCount i)).sum =
      (∑ j ∈ Finset.range 10, f j) + ∑ j ∈ Finset.range 18, f (10 + j) := by
    rw [list_map_sum_range w (formulaCount i) .nil, hlen]
    exact Finset.sum_range_add f 10 18
  have hslotlen : (effectiveSlots C).length ≤ 36 := by
    have := effectiveSlots_length_le C hC
    omega
  have hweighted := two_root_weighted_count (effectiveSlots C) a b hab hslotlen hinputs
    (fun j hj ha hb => hgates j (by omega) ha hb) f
  change f (10 + a.val) + f (10 + b.val) ≤ 2
  omega

variable {α β : Type*}

abbrev FormulaRectangle (α β : Type*) := Fin 10 × Finset α × Finset β

def formulaRectangles (x : α → Fin 10 → Bool) (y : β → Fin 10 → Bool) :
    FormulaTree → Finset α → Finset β → List (FormulaRectangle α β)
  | .nil, _, _ => []
  | .node (.inl i) _ _, A, B => [(i, A, B)]
  | .node (.inr false) l r, A, B =>
      formulaRectangles x y l A (B.filter fun b => formulaValue (y b) l = false) ++
      formulaRectangles x y r A (B.filter fun b => formulaValue (y b) l = true)
  | .node (.inr true) l r, A, B =>
      formulaRectangles x y l (A.filter fun a => formulaValue (x a) l = true) B ++
      formulaRectangles x y r (A.filter fun a => formulaValue (x a) l = false) B

def formulaRectangleLabelCount (i : Fin 10) (R : List (FormulaRectangle α β)) : ℕ :=
  (R.filter fun r => r.1 = i).length

def formulaRectangleHitCount [DecidableEq α] [DecidableEq β] (a : α) (b : β) (R : List (FormulaRectangle α β)) : ℕ :=
  (R.filter fun r => a ∈ r.2.1 ∧ b ∈ r.2.2).length

lemma formulaRectangles_label_count (x : α → Fin 10 → Bool) (y : β → Fin 10 → Bool)
    (f : FormulaTree) (A : Finset α) (B : Finset β) (i : Fin 10) :
    formulaRectangleLabelCount i (formulaRectangles x y f A B) = formulaCount i f := by
  induction f generalizing A B with
  | nil => simp [formulaRectangles, formulaRectangleLabelCount, formulaCount]
  | node v l r ihl ihr =>
    cases v with
    | inl j =>
      by_cases h : i = j <;>
        simp [formulaRectangles, formulaRectangleLabelCount, formulaCount,
          h, eq_comm]
    | inr op =>
      cases op <;>
        simp only [formulaRectangles, formulaRectangleLabelCount, List.filter_append,
          List.length_append, formulaCount] <;>
        exact congrArg₂ (· + ·) (ihl _ _) (ihr _ _)

lemma formulaRectangles_hit_count [DecidableEq α] [DecidableEq β] (x : α → Fin 10 → Bool) (y : β → Fin 10 → Bool)
    (f : FormulaTree) (A : Finset α) (B : Finset β)
    (hx : ∀ a ∈ A, formulaValue (x a) f = true)
    (hy : ∀ b ∈ B, formulaValue (y b) f = false)
    (a : α) (b : β) :
    formulaRectangleHitCount a b (formulaRectangles x y f A B) =
      if a ∈ A ∧ b ∈ B then 1 else 0 := by
  induction f generalizing A B with
  | nil =>
    have ha : a ∉ A := by intro ha; simpa [formulaValue] using hx a ha
    simp [formulaRectangles, formulaRectangleHitCount, ha]
  | node v l r ihl ihr =>
    cases v with
    | inl i =>
      by_cases ha : a ∈ A <;> by_cases hb : b ∈ B <;>
        simp [formulaRectangles, formulaRectangleHitCount, ha, hb]
    | inr op =>
      cases op with
      | false =>
        have hxl : ∀ a ∈ A, formulaValue (x a) l = true := by
          intro a ha
          have h := hx a ha
          cases hl : formulaValue (x a) l <;> simp_all [formulaValue]
        have hxr : ∀ a ∈ A, formulaValue (x a) r = true := by
          intro a ha
          have h := hx a ha
          cases hr : formulaValue (x a) r <;> simp_all [formulaValue]
        have hyl : ∀ b ∈ B.filter (fun b => formulaValue (y b) l = false),
            formulaValue (y b) l = false := by
          intro b hb
          exact (Finset.mem_filter.mp hb).2
        have hyr : ∀ b ∈ B.filter (fun b => formulaValue (y b) l = true),
            formulaValue (y b) r = false := by
          intro b hb
          have hb' := Finset.mem_filter.mp hb
          have h := hy b hb'.1
          simpa [formulaValue, hb'.2] using h
        change formulaRectangleHitCount a b
          (formulaRectangles x y l A (B.filter fun b => formulaValue (y b) l = false) ++
           formulaRectangles x y r A (B.filter fun b => formulaValue (y b) l = true)) = _
        simp only [formulaRectangleHitCount, List.filter_append, List.length_append]
        change formulaRectangleHitCount a b _ + formulaRectangleHitCount a b _ = _
        rw [ihl _ _ hxl hyl, ihr _ _ hxr hyr]
        cases h : formulaValue (y b) l <;> simp [h]
      | true =>
        have hxl : ∀ a ∈ A.filter (fun a => formulaValue (x a) l = true),
            formulaValue (x a) l = true := by
          intro a ha
          exact (Finset.mem_filter.mp ha).2
        have hxr : ∀ a ∈ A.filter (fun a => formulaValue (x a) l = false),
            formulaValue (x a) r = true := by
          intro a ha
          have ha' := Finset.mem_filter.mp ha
          have h := hx a ha'.1
          simpa [formulaValue, ha'.2] using h
        have hyl : ∀ b ∈ B, formulaValue (y b) l = false := by
          intro b hb
          exact (Bool.or_eq_false_iff.mp (hy b hb)).1
        have hyr : ∀ b ∈ B, formulaValue (y b) r = false := by
          intro b hb
          exact (Bool.or_eq_false_iff.mp (hy b hb)).2
        change formulaRectangleHitCount a b
          (formulaRectangles x y l (A.filter fun a => formulaValue (x a) l = true) B ++
           formulaRectangles x y r (A.filter fun a => formulaValue (x a) l = false) B) = _
        simp only [formulaRectangleHitCount, List.filter_append, List.length_append]
        change formulaRectangleHitCount a b _ + formulaRectangleHitCount a b _ = _
        rw [ihl _ _ hxl hyl, ihr _ _ hxr hyr]
        cases h : formulaValue (x a) l <;> simp [h]

lemma formulaRectangles_sound (x : α → Fin 10 → Bool) (y : β → Fin 10 → Bool)
    (f : FormulaTree) (A : Finset α) (B : Finset β)
    (hx : ∀ a ∈ A, formulaValue (x a) f = true)
    (hy : ∀ b ∈ B, formulaValue (y b) f = false) :
    ∀ q ∈ formulaRectangles x y f A B,
      (∀ a ∈ q.2.1, x a q.1 = true) ∧ (∀ b ∈ q.2.2, y b q.1 = false) := by
  induction f generalizing A B with
  | nil => simp [formulaRectangles]
  | node v l r ihl ihr =>
    cases v with
    | inl i =>
      intro q hq
      simp only [formulaRectangles, List.mem_singleton] at hq
      subst q
      exact ⟨hx, hy⟩
    | inr op =>
      cases op with
      | false =>
        have hxl : ∀ a ∈ A, formulaValue (x a) l = true := by
          intro a ha
          have h := hx a ha
          cases hl : formulaValue (x a) l <;> simp_all [formulaValue]
        have hxr : ∀ a ∈ A, formulaValue (x a) r = true := by
          intro a ha
          have h := hx a ha
          cases hr : formulaValue (x a) r <;> simp_all [formulaValue]
        have hyl : ∀ b ∈ B.filter (fun b => formulaValue (y b) l = false),
            formulaValue (y b) l = false := by
          intro b hb
          exact (Finset.mem_filter.mp hb).2
        have hyr : ∀ b ∈ B.filter (fun b => formulaValue (y b) l = true),
            formulaValue (y b) r = false := by
          intro b hb
          have hb' := Finset.mem_filter.mp hb
          have h := hy b hb'.1
          simpa [formulaValue, hb'.2] using h
        intro q hq
        simp only [formulaRectangles, List.mem_append] at hq
        rcases hq with hq | hq
        · exact ihl _ _ hxl hyl q hq
        · exact ihr _ _ hxr hyr q hq
      | true =>
        have hxl : ∀ a ∈ A.filter (fun a => formulaValue (x a) l = true),
            formulaValue (x a) l = true := by
          intro a ha
          exact (Finset.mem_filter.mp ha).2
        have hxr : ∀ a ∈ A.filter (fun a => formulaValue (x a) l = false),
            formulaValue (x a) r = true := by
          intro a ha
          have ha' := Finset.mem_filter.mp ha
          have h := hx a ha'.1
          simpa [formulaValue, ha'.2] using h
        have hyl : ∀ b ∈ B, formulaValue (y b) l = false := by
          intro b hb
          exact (Bool.or_eq_false_iff.mp (hy b hb)).1
        have hyr : ∀ b ∈ B, formulaValue (y b) r = false := by
          intro b hb
          exact (Bool.or_eq_false_iff.mp (hy b hb)).2
        intro q hq
        simp only [formulaRectangles, List.mem_append] at hq
        rcases hq with hq | hq
        · exact ihl _ _ hxl hyl q hq
        · exact ihr _ _ hxr hyr q hq

lemma exists_formula_rectangle_partition [DecidableEq α] [DecidableEq β]
    [Fintype α] [Fintype β]
    (x : α → Fin 10 → Bool) (y : β → Fin 10 → Bool) (f : FormulaTree)
    (hx : ∀ a, formulaValue (x a) f = true)
    (hy : ∀ b, formulaValue (y b) f = false) :
    ∃ R : List (FormulaRectangle α β),
      (∀ a b, formulaRectangleHitCount a b R = 1) ∧
      (∀ i, formulaRectangleLabelCount i R = formulaCount i f) ∧
      (∀ q ∈ R, (∀ a ∈ q.2.1, x a q.1 = true) ∧
        (∀ b ∈ q.2.2, y b q.1 = false)) := by
  refine ⟨formulaRectangles x y f Finset.univ Finset.univ, ?_, ?_, ?_⟩
  · intro a b
    simpa using formulaRectangles_hit_count x y f Finset.univ Finset.univ
      (fun a _ => hx a) (fun b _ => hy b) a b
  · intro i
    exact formulaRectangles_label_count x y f Finset.univ Finset.univ i
  · exact formulaRectangles_sound x y f Finset.univ Finset.univ
      (fun a _ => hx a) (fun b _ => hy b)

namespace RectangleTwo

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma two_rectangles_three_diagonals :
    ∀ (r₁ r₂ c₁ c₂ : Fin 3 → Bool),
      (∀ i j, ¬ (r₁ i = true ∧ c₁ j = true ∧ r₂ i = true ∧ c₂ j = true)) →
      (∀ i j, i ≠ j → (r₁ i && c₁ j || r₂ i && c₂ j) = true) →
      (((r₁ 0 && c₁ 0 || r₂ 0 && c₂ 0) && (r₁ 1 && c₁ 1 || r₂ 1 && c₂ 1)) ||
       ((r₁ 0 && c₁ 0 || r₂ 0 && c₂ 0) && (r₁ 2 && c₁ 2 || r₂ 2 && c₂ 2)) ||
       ((r₁ 1 && c₁ 1 || r₂ 1 && c₂ 1) && (r₁ 2 && c₁ 2 || r₂ 2 && c₂ 2))) = true := by
  decide

end RectangleTwo

namespace PetersenOrientation

def value (b : Bool) : ℕ := if b then 1 else 0

lemma value_complement (b : Bool) : value b + value (!b) = 1 := by
  cases b <;> rfl

lemma value_three (a b c : Bool) :
    ((a && b) || (a && c) || (b && c)) = true →
      2 ≤ value a + value b + value c := by
  cases a <;> cases b <;> cases c <;> decide

def slots : Fin 10 → Fin 3 → Fin 15 × Bool :=
  ![![(1, true), (2, true), (0, true)],
    ![(4, true), (3, true), (0, false)],
    ![(3, false), (6, true), (5, true)],
    ![(7, true), (5, false), (8, true)],
    ![(7, false), (9, true), (1, false)],
    ![(10, true), (11, true), (2, false)],
    ![(4, false), (12, true), (13, true)],
    ![(10, false), (6, false), (14, true)],
    ![(11, false), (12, false), (8, false)],
    ![(9, false), (13, false), (14, false)]]

def win (o : Fin 15 → Bool) (v : Fin 10) (i : Fin 3) : Bool :=
  if (slots v i).2 then o (slots v i).1 else !(o (slots v i).1)

lemma no_orientation_all_two (o : Fin 15 → Bool)
    (h : ∀ v : Fin 10, 2 ≤ value (win o v 0) + value (win o v 1) + value (win o v 2)) :
    False := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h5 := h 5
  have h6 := h 6
  have h7 := h 7
  have h8 := h 8
  have h9 := h 9
  change 2 ≤ value (o 1) + value (o 2) + value (o 0) at h0
  change 2 ≤ value (o 4) + value (o 3) + value (!(o 0)) at h1
  change 2 ≤ value (!(o 3)) + value (o 6) + value (o 5) at h2
  change 2 ≤ value (o 7) + value (!(o 5)) + value (o 8) at h3
  change 2 ≤ value (!(o 7)) + value (o 9) + value (!(o 1)) at h4
  change 2 ≤ value (o 10) + value (o 11) + value (!(o 2)) at h5
  change 2 ≤ value (!(o 4)) + value (o 12) + value (o 13) at h6
  change 2 ≤ value (!(o 10)) + value (!(o 6)) + value (o 14) at h7
  change 2 ≤ value (!(o 11)) + value (!(o 12)) + value (!(o 8)) at h8
  change 2 ≤ value (!(o 9)) + value (!(o 13)) + value (!(o 14)) at h9
  have c0 := value_complement (o 0)
  have c1 := value_complement (o 1)
  have c2 := value_complement (o 2)
  have c3 := value_complement (o 3)
  have c4 := value_complement (o 4)
  have c5 := value_complement (o 5)
  have c6 := value_complement (o 6)
  have c7 := value_complement (o 7)
  have c8 := value_complement (o 8)
  have c9 := value_complement (o 9)
  have c10 := value_complement (o 10)
  have c11 := value_complement (o 11)
  have c12 := value_complement (o 12)
  have c13 := value_complement (o 13)
  have c14 := value_complement (o 14)
  omega

end PetersenOrientation

namespace PetersenBridge

open PetersenOrientation

def edges : Fin 15 → Fin 10 × Fin 10 :=
  ![(0, 1), (0, 4), (0, 5), (1, 2), (1, 6), (2, 3), (2, 7),
    (3, 4), (3, 8), (4, 9), (5, 7), (5, 8), (6, 8), (6, 9), (7, 9)]

def independent : Fin 5 → Finset (Fin 10) :=
  ![{0, 2, 8, 9}, {0, 3, 6, 7}, {1, 3, 5, 9}, {1, 4, 7, 8}, {2, 4, 5, 6}]

def columns : Fin 10 → Fin 3 → Fin 5 :=
  ![![2, 3, 4], ![0, 1, 4], ![1, 2, 3], ![0, 3, 4], ![0, 1, 2],
    ![0, 1, 3], ![0, 2, 3], ![0, 2, 4], ![1, 2, 4], ![1, 3, 4]]

def edgeColumn : Fin 15 → Fin 5 := ![4, 2, 3, 1, 0, 3, 2, 0, 4, 1, 0, 1, 2, 3, 4]

def row (v : Fin 10) (i : Fin 3) : Fin 15 := (slots v i).1

def allowed (e : Fin 15) (c : Fin 5) (v : Fin 10) : Prop :=
  (v = (edges e).1 ∨ v = (edges e).2) ∧ v ∉ independent c

lemma column_eq : ∀ v i, columns v i = edgeColumn (row v i) := by decide

lemma off_diagonal_forced :
    ∀ (v : Fin 10) (i j : Fin 3) (w : Fin 10),
      i ≠ j → allowed (row v i) (columns v j) w → w = v := by
  unfold allowed
  decide

lemma diagonal_reflection :
    ∀ (v : Fin 10) (i : Fin 3) (w : Fin 10),
      allowed (row v i) (columns v i) w →
      decide (w = v) =
        (if (slots v i).2 then decide (w = (edges (row v i)).1)
          else !decide (w = (edges (row v i)).1)) := by
  unfold allowed
  decide

def orientation (owner : Fin 15 → Fin 5 → Fin 10) (e : Fin 15) : Bool :=
  decide (owner e (edgeColumn e) = (edges e).1)

lemma diagonal_win (owner : Fin 15 → Fin 5 → Fin 10)
    (legal : ∀ e c, allowed e c (owner e c)) (v : Fin 10) (i : Fin 3) :
    decide (owner (row v i) (columns v i) = v) = win (orientation owner) v i := by
  have h := diagonal_reflection v i (owner (row v i) (columns v i)) (legal _ _)
  simpa only [win, orientation, row, column_eq] using h

lemma no_two_rectangle_owners
    (owner : Fin 15 → Fin 5 → Fin 10)
    (legal : ∀ e c, allowed e c (owner e c))
    (A₁ A₂ : Fin 10 → Finset (Fin 15)) (B₁ B₂ : Fin 10 → Finset (Fin 5))
    (partition : ∀ v e c, owner e c = v ↔
      (e ∈ A₁ v ∧ c ∈ B₁ v) ∨ (e ∈ A₂ v ∧ c ∈ B₂ v))
    (disjoint : ∀ v e c, ¬ (e ∈ A₁ v ∧ c ∈ B₁ v ∧ e ∈ A₂ v ∧ c ∈ B₂ v)) :
    False := by
  apply no_orientation_all_two (orientation owner)
  intro v
  let r₁ := fun i : Fin 3 => decide (row v i ∈ A₁ v)
  let r₂ := fun i : Fin 3 => decide (row v i ∈ A₂ v)
  let c₁ := fun i : Fin 3 => decide (columns v i ∈ B₁ v)
  let c₂ := fun i : Fin 3 => decide (columns v i ∈ B₂ v)
  have dj : ∀ i j, ¬ (r₁ i = true ∧ c₁ j = true ∧ r₂ i = true ∧ c₂ j = true) := by
    intro i j
    simpa only [r₁, r₂, c₁, c₂, decide_eq_true_eq] using disjoint v (row v i) (columns v j)
  have off : ∀ i j, i ≠ j → (r₁ i && c₁ j || r₂ i && c₂ j) = true := by
    intro i j hij
    have h := (partition v (row v i) (columns v j)).mp
      (off_diagonal_forced v i j _ hij (legal _ _))
    simpa only [r₁, r₂, c₁, c₂, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] using h
  have diag (i : Fin 3) :
      (r₁ i && c₁ i || r₂ i && c₂ i) = win (orientation owner) v i := by
    rw [← diagonal_win owner legal v i]
    apply Bool.eq_iff_iff.mpr
    simpa only [r₁, r₂, c₁, c₂, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] using
      (partition v (row v i) (columns v i)).symm
  have h := RectangleTwo.two_rectangles_three_diagonals r₁ r₂ c₁ c₂ dj off
  rw [diag 0, diag 1, diag 2] at h
  exact value_three _ _ _ h

abbrev Rectangle := Fin 10 × Finset (Fin 15) × Finset (Fin 5)

def hitCount (a : Fin 15) (b : Fin 5) (R : List Rectangle) : ℕ :=
  (R.filter fun r => a ∈ r.2.1 ∧ b ∈ r.2.2).length

lemma small_rectangles (L : List Rectangle) (size : L.length ≤ 2)
    (unique : ∀ a b, hitCount a b L ≤ 1) :
    ∃ (A₁ A₂ : Finset (Fin 15)) (B₁ B₂ : Finset (Fin 5)),
      (∀ a b, (∃ r ∈ L, a ∈ r.2.1 ∧ b ∈ r.2.2) ↔
        (a ∈ A₁ ∧ b ∈ B₁) ∨ (a ∈ A₂ ∧ b ∈ B₂)) ∧
      (∀ a b, ¬ (a ∈ A₁ ∧ b ∈ B₁ ∧ a ∈ A₂ ∧ b ∈ B₂)) := by
  cases L with
  | nil => exact ⟨∅, ∅, ∅, ∅, by simp, by simp⟩
  | cons r rest =>
    cases rest with
    | nil => exact ⟨r.2.1, ∅, r.2.2, ∅, by simp, by simp⟩
    | cons s rest =>
      cases rest with
      | nil =>
        refine ⟨r.2.1, s.2.1, r.2.2, s.2.2, by simp, ?_⟩
        intro a b ⟨ha, hb, hc, hd⟩
        have h := unique a b
        simp [hitCount, ha, hb, hc, hd] at h
      | cons t rest => simp at size

lemma no_list_partition (R : List Rectangle)
    (coverage : ∀ a b, hitCount a b R = 1)
    (labels : ∀ v : Fin 10, (R.filter fun r => r.1 = v).length ≤ 2)
    (sound : ∀ r ∈ R, ∀ a ∈ r.2.1, ∀ b ∈ r.2.2, allowed a b r.1) : False := by
  classical
  have hs : ∀ a b, ∃ r, (R.filter fun r => a ∈ r.2.1 ∧ b ∈ r.2.2) = [r] := by
    intro a b
    exact ⟨_, List.eq_cons_of_length_one (coverage a b)⟩
  choose selected hselected using hs
  have hmem (a : Fin 15) (b : Fin 5) : selected a b ∈ R ∧
      a ∈ (selected a b).2.1 ∧ b ∈ (selected a b).2.2 := by
    have h : selected a b ∈ (R.filter fun r => a ∈ r.2.1 ∧ b ∈ r.2.2) := by
      rw [hselected]
      simp
    simpa only [List.mem_filter, decide_eq_true_eq] using h
  have hsame (a : Fin 15) (b : Fin 5) (r : Rectangle)
      (hr : r ∈ R) (ha : a ∈ r.2.1) (hb : b ∈ r.2.2) : r = selected a b := by
    have h : r ∈ (R.filter fun r => a ∈ r.2.1 ∧ b ∈ r.2.2) := by
      simp only [List.mem_filter, decide_eq_true_eq]
      exact ⟨hr, ha, hb⟩
    rw [hselected] at h
    simpa only [List.mem_singleton] using h
  let owner := fun a b => (selected a b).1
  have legal : ∀ a b, allowed a b (owner a b) := by
    intro a b
    exact sound _ (hmem a b).1 _ (hmem a b).2.1 _ (hmem a b).2.2
  have local_unique (v : Fin 10) (a : Fin 15) (b : Fin 5) :
      hitCount a b (R.filter fun r => r.1 = v) ≤ 1 := by
    unfold hitCount
    rw [List.filter_comm]
    exact (List.filter_sublist ..).length_le.trans (coverage a b).le
  have local_owner (v : Fin 10) (a : Fin 15) (b : Fin 5) :
      owner a b = v ↔
      ∃ r ∈ R.filter (fun r => r.1 = v), a ∈ r.2.1 ∧ b ∈ r.2.2 := by
    constructor
    · intro hv
      refine ⟨selected a b, ?_, (hmem a b).2⟩
      simp only [List.mem_filter, decide_eq_true_eq]
      exact ⟨(hmem a b).1, hv⟩
    · rintro ⟨r, hr, ha, hb⟩
      simp only [List.mem_filter, decide_eq_true_eq] at hr
      have hh := hsame a b r hr.1 ha hb
      simpa only [owner, ← hh] using hr.2
  have small (v : Fin 10) := small_rectangles (R.filter fun r => r.1 = v)
    (labels v) (local_unique v)
  choose A₁ A₂ B₁ B₂ hpart hdisjoint using small
  exact no_two_rectangle_owners owner legal A₁ A₂ B₁ B₂
    (fun v a b => (local_owner v a b).trans (hpart v a b)) hdisjoint

end PetersenBridge

namespace PetersenBridge

def edgeInput (e : Fin 15) (v : Fin 10) : Bool :=
  decide (v = (edges e).1 ∨ v = (edges e).2)

def independentInput (c : Fin 5) (v : Fin 10) : Bool :=
  decide (v ∈ independent c)

def petersen (x : Fin 10 → Bool) : Bool :=
  (List.finRange 5).any fun i : Fin 5 =>
    x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1)) ||
    x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i) ||
    x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2))

lemma edgeInput_positive : ∀ e, petersen (edgeInput e) = true := by decide

lemma edgeInput_count : ∀ e, (List.ofFn (edgeInput e)).count true ≤ 2 := by decide

lemma independentInput_negative : ∀ c, petersen (independentInput c) = false := by decide

lemma input_sound (e : Fin 15) (c : Fin 5) (v : Fin 10)
    (he : edgeInput e v = true) (hc : independentInput c v = false) : allowed e c v := by
  simpa only [edgeInput, independentInput, decide_eq_true_eq, decide_eq_false_iff_not, allowed]
    using And.intro he hc

end PetersenBridge

namespace Pruning

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

variable {α : Type}

def d3r1Fold (δ : α) (Φ : GateOp → List α → α) (gs : List Gate) (init : List α) : List α :=
  gs.foldl (fun w g => w ++ [Φ g.op (g.inputs.map fun i => w.getD i δ)]) init

lemma d3r1Fold_snoc (δ : α) (Φ : GateOp → List α → α) (gs : List Gate) (g : Gate)
    (init : List α) :
    d3r1Fold δ Φ (gs ++ [g]) init = d3r1Fold δ Φ gs init ++
      [Φ g.op (g.inputs.map fun i => (d3r1Fold δ Φ gs init).getD i δ)] := by
  simp only [d3r1Fold, List.foldl_append, List.foldl_cons, List.foldl_nil]

lemma d3r1Fold_length (δ : α) (Φ : GateOp → List α → α) (gs : List Gate) (init : List α) :
    (d3r1Fold δ Φ gs init).length = init.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [d3r1Fold]
  | append_singleton gs g ih => rw [d3r1Fold_snoc]; simp [ih]; omega

lemma d3r1Fold_lt (δ : α) (Φ : GateOp → List α → α) (gs : List Gate) (init : List α)
    (i : ℕ) (h : i < init.length) : (d3r1Fold δ Φ gs init).getD i δ = init.getD i δ := by
  induction gs using List.reverseRecOn with
  | nil => simp [d3r1Fold]
  | append_singleton gs g ih =>
    rw [d3r1Fold_snoc, List.getD_append _ _ _ _ (by rw [d3r1Fold_length]; omega), ih]

lemma d3r1Fold_ge (δ : α) (Φ : GateOp → List α → α) (gs : List Gate) (init : List α)
    (i : ℕ) (h : init.length + gs.length ≤ i) : (d3r1Fold δ Φ gs init).getD i δ = δ := by
  rw [List.getD_eq_default _ _ (by rw [d3r1Fold_length]; exact h)]

lemma d3r1Fold_gate (δ : α) (Φ : GateOp → List α → α) (gs : List Gate) (init : List α) :
    ∀ (j : ℕ) (hj : j < gs.length), (d3r1Fold δ Φ gs init).getD (init.length + j) δ =
      Φ gs[j].op (gs[j].inputs.map fun i =>
        if i < init.length + j then (d3r1Fold δ Φ gs init).getD i δ else δ) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hl := d3r1Fold_length δ Φ gs init
    rw [d3r1Fold_snoc]
    by_cases hjl : j < gs.length
    · rw [List.getD_append _ _ _ _ (by omega), ih j hjl]
      simp only [List.getElem_append_left hjl]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < init.length + j
      · rw [ite_eq_left hi, ite_eq_left hi, List.getD_append _ _ _ _ (by omega)]
      · simp only [hi, ite_false]
    · have hje : j = gs.length := by simp at hj; omega
      subst hje
      rw [List.getD_append_right _ _ _ _ (by omega)]
      simp only [List.getElem_append_right (Nat.le_refl _), hl, Nat.sub_self,
        List.getD_cons_zero, List.getElem_cons_zero]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < init.length + gs.length
      · rw [ite_eq_left hi, List.getD_append _ _ _ _ (by omega)]
      · simp only [hi, ite_false]
        rw [List.getD_eq_default _ _ (by omega)]


def d3r1Rank (κ : ℕ → Bool) (t : ℕ) : ℕ := ((List.range t).filter κ).length

lemma d3r1_range_split (κ : ℕ → Bool) (s t : ℕ) (h : s ≤ t) :
    (List.range t).filter κ = (List.range s).filter κ ++ (List.range' s (t - s)).filter κ := by
  rw [← List.filter_append]
  congr 1
  rw [List.range_eq_range', List.range_eq_range']
  have := @List.range'_append_1 0 s (t - s)
  simp only [Nat.zero_add] at this
  rw [this]
  congr 1
  omega

lemma d3r1_rank_lt (κ : ℕ → Bool) (s t : ℕ) (hst : s < t) (hs : κ s = true) :
    d3r1Rank κ s < d3r1Rank κ t := by
  unfold d3r1Rank
  rw [d3r1_range_split κ s t hst.le, List.length_append]
  obtain ⟨m, hm⟩ : ∃ m, t - s = m + 1 := ⟨t - s - 1, by omega⟩
  rw [hm, List.range'_succ, List.filter_cons_of_pos hs]
  simp

lemma d3r1_L_get (κ : ℕ → Bool) (len t : ℕ) (ht : t < len) (hk : κ t = true) :
    ((List.range len).filter κ)[d3r1Rank κ t]? = some t := by
  rw [d3r1_range_split κ t len ht.le]
  unfold d3r1Rank
  rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  obtain ⟨m, hm⟩ : ∃ m, len - t = m + 1 := ⟨len - t - 1, by omega⟩
  rw [hm, List.range'_succ, List.filter_cons_of_pos hk]
  simp

lemma d3r1_L_back (κ : ℕ → Bool) (len r : ℕ) (hr : r < ((List.range len).filter κ).length) :
    κ ((List.range len).filter κ)[r] = true ∧ ((List.range len).filter κ)[r] < len ∧
      d3r1Rank κ ((List.range len).filter κ)[r] = r := by
  have hm : ((List.range len).filter κ)[r] ∈ (List.range len).filter κ := List.getElem_mem hr
  have hm2 := List.mem_filter.mp hm
  have hlt := List.mem_range.mp hm2.1
  refine ⟨hm2.2, hlt, ?_⟩
  have hg := d3r1_L_get κ len _ hlt hm2.2
  rw [List.getElem?_eq_some_iff] at hg
  obtain ⟨hb, he⟩ := hg
  have hnd : ((List.range len).filter κ).Nodup := (List.nodup_range).filter _
  exact (hnd.getElem_inj_iff).mp he

def d3r1New (n : ℕ) (κ : ℕ → Bool) (top u : ℕ) : ℕ :=
  if u < n then u else if κ (u - n) then n + d3r1Rank κ (u - n) else n + top

def d3r1Top (κ : ℕ → Bool) (gs : List Gate) : ℕ := ((List.range gs.length).filter κ).length

def d3r1PGate (n : ℕ) (κ : ℕ → Bool) (gs : List Gate) (t : ℕ) : Gate :=
  { op := (gs.getD t ⟨GateOp.and, []⟩).op,
    inputs := (gs.getD t ⟨GateOp.and, []⟩).inputs.map fun a =>
      if a < n + t then d3r1New n κ (d3r1Top κ gs) a else n + d3r1Rank κ t }

def d3r1Pruned (n : ℕ) (κ : ℕ → Bool) (gs : List Gate) : List Gate :=
  ((List.range gs.length).filter κ).map (d3r1PGate n κ gs)

lemma d3r1_pruned_length (n : ℕ) (κ : ℕ → Bool) (gs : List Gate) :
    (d3r1Pruned n κ gs).length = d3r1Top κ gs := by
  simp [d3r1Pruned, d3r1Top]

lemma d3r1_pruned_get (n : ℕ) (κ : ℕ → Bool) (gs : List Gate) (t : ℕ) (ht : t < gs.length)
    (hk : κ t = true) : ∃ h : d3r1Rank κ t < (d3r1Pruned n κ gs).length,
      (d3r1Pruned n κ gs)[d3r1Rank κ t] = d3r1PGate n κ gs t := by
  have hg := d3r1_L_get κ gs.length t ht hk
  rw [List.getElem?_eq_some_iff] at hg
  obtain ⟨hb, he⟩ := hg
  refine ⟨by simpa [d3r1Pruned] using hb, ?_⟩
  simp [d3r1Pruned, he]

lemma d3r1_new_lt (n : ℕ) (κ : ℕ → Bool) (top a t : ℕ) (hat : a < n + t)
    (ha : a < n ∨ κ (a - n) = true) : d3r1New n κ top a < n + d3r1Rank κ t := by
  unfold d3r1New
  by_cases han : a < n
  · rw [ite_eq_left han]; omega
  · have hk := ha.resolve_left han
    rw [ite_eq_right han, ite_eq_left hk]
    have := d3r1_rank_lt κ (a - n) t (by omega) hk
    omega

lemma d3r1_prune_val {α : Type} (δ : α) (Φ : GateOp → List α → α) (init : List α) (n : ℕ)
    (hn : init.length = n) (gs : List Gate) (κ : ℕ → Bool)
    (hκ : ∀ t, κ t = true → t < gs.length)
    (hcl : ∀ (t : ℕ) (ht : t < gs.length), κ t = true → ∀ a ∈ gs[t].inputs, n ≤ a → a < n + t →
      κ (a - n) = true) :
    ∀ u, (u < n ∨ κ (u - n) = true) →
      (d3r1Fold δ Φ (d3r1Pruned n κ gs) init).getD (d3r1New n κ (d3r1Top κ gs) u) δ =
        (d3r1Fold δ Φ gs init).getD u δ := by
  subst hn
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu
    by_cases hun : u < init.length
    · simp only [d3r1New, hun, ite_true]
      rw [d3r1Fold_lt _ _ _ _ _ hun, d3r1Fold_lt _ _ _ _ _ hun]
    · have hk : κ (u - init.length) = true := hu.resolve_left hun
      obtain ⟨t, rfl⟩ : ∃ t, u = init.length + t := ⟨u - init.length, by omega⟩
      simp only [Nat.add_sub_cancel_left] at hk
      have ht := hκ t hk
      have hnew : d3r1New init.length κ (d3r1Top κ gs) (init.length + t) =
          init.length + d3r1Rank κ t := by
        simp [d3r1New, hk]
      obtain ⟨hb, hpr⟩ := d3r1_pruned_get init.length κ gs t ht hk
      rw [hnew, d3r1Fold_gate _ _ _ _ _ hb, d3r1Fold_gate _ _ _ _ t ht, hpr]
      have hg : gs.getD t ⟨GateOp.and, []⟩ = gs[t] := List.getD_eq_getElem _ _ ht
      simp only [d3r1PGate, hg, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a ha
      simp only [Function.comp]
      by_cases hat : a < init.length + t
      · have hA : a < init.length ∨ κ (a - init.length) = true := by
          by_cases han : a < init.length
          · exact Or.inl han
          · exact Or.inr (hcl t ht hk a ha (by omega) hat)
        rw [ite_eq_left hat, ite_eq_left (d3r1_new_lt _ _ _ a t hat hA), ite_eq_left hat]
        exact ih a hat hA
      · simp only [hat, ite_false, lt_irrefl]

lemma d3r1_prune_out {α : Type} (δ : α) (Φ : GateOp → List α → α) (init : List α) (n : ℕ)
    (hn : init.length = n) (gs : List Gate) (κ : ℕ → Bool) (o : ℕ)
    (hκ : ∀ t, κ t = true → t < gs.length)
    (hcl : ∀ (t : ℕ) (ht : t < gs.length), κ t = true → ∀ a ∈ gs[t].inputs, n ≤ a → a < n + t →
      κ (a - n) = true)
    (ho : n ≤ o → o < n + gs.length → κ (o - n) = true) :
    (d3r1Fold δ Φ (d3r1Pruned n κ gs) init).getD (d3r1New n κ (d3r1Top κ gs) o) δ =
      (d3r1Fold δ Φ gs init).getD o δ := by
  by_cases hA : o < n ∨ κ (o - n) = true
  · exact d3r1_prune_val δ Φ init n hn gs κ hκ hcl o hA
  · have hon : n ≤ o := by omega
    have hk : κ (o - n) = false := by simpa using (fun h => hA (Or.inr h))
    have hol : n + gs.length ≤ o := by
      by_contra h
      rw [ho hon (by omega)] at hk
      exact Bool.noConfusion hk
    have hnew : d3r1New n κ (d3r1Top κ gs) o = n + d3r1Top κ gs := by
      simp [d3r1New, hk, show ¬ o < n by omega]
    rw [hnew, d3r1Fold_ge _ _ _ _ _ (by rw [hn, d3r1_pruned_length]),
      d3r1Fold_ge _ _ _ _ _ (by omega)]

lemma pruned_fanInTwo (n : ℕ) (C : Circuit) (κ : ℕ → Bool) (hfan : FanInTwo C) :
    FanInTwo ⟨d3r1Pruned n κ C.gates, d3r1New n κ (d3r1Top κ C.gates) C.output⟩ := by
  intro g hg
  simp only [d3r1Pruned, List.mem_map, List.mem_filter, List.mem_range] at hg
  obtain ⟨t, ⟨ht, _⟩, rfl⟩ := hg
  have h := hfan C.gates[t] (List.getElem_mem ht)
  simpa only [d3r1PGate, List.getD_eq_getElem _ _ ht, List.length_map] using h

end Pruning

namespace LivePair

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3821_aux

def normalizeGate (g : Gate) : Gate := ⟨g.op, effectiveInputs g⟩

def normalize (C : Circuit) : Circuit :=
  ⟨C.gates.map normalizeGate, C.output⟩

lemma normalizeGate_eval (g : Gate) (w : List Bool) :
    (normalizeGate g).op.eval ((normalizeGate g).inputs.map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
  cases g with
  | mk op inputs =>
    cases op <;> simp [normalizeGate, effectiveInputs, GateOp.eval]
    cases inputs <;> simp

lemma normalize_size (C : Circuit) : (normalize C).size = C.size := by
  simp [normalize, Circuit.size]

lemma normalize_fan (C : Circuit) (hC : FanInTwo C) : FanInTwo (normalize C) := by
  intro g hg
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hg
  exact ⟨(hC k hk).1, effectiveInputs_length_le (hC k hk).2⟩

lemma normalize_wires (C : Circuit) (x : List Bool) :
    (normalize C).wires x = C.wires x := by
  have fold (gs : List Gate) (w : List Bool) :
      (gs.map normalizeGate).foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.map_cons, List.foldl_cons, normalizeGate_eval]
      exact ih _
  exact fold C.gates x

lemma normalize_effective (C : Circuit) {g : Gate} (hg : g ∈ (normalize C).gates) :
    effectiveInputs g = g.inputs := by
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hg
  cases k with
  | mk op inputs =>
    cases op <;> simp [normalizeGate, effectiveInputs, List.take_take]

lemma delete_unused_pair (n : ℕ) (C : Circuit) (a b j : ℕ)
    (hC : FanInTwo C) (hj : j < C.size)
    (ha : a ≠ n + j) (hb : b ≠ n + j)
    (hno : ∀ g ∈ C.gates, n + j ∉ g.inputs) :
    ∃ (D : Circuit) (c d : ℕ), FanInTwo D ∧ D.size + 1 = C.size ∧
      ∀ x : Fin n → Bool,
        (D.wires (List.ofFn x)).getD c false = (C.wires (List.ofFn x)).getD a false ∧
        (D.wires (List.ofFn x)).getD d false = (C.wires (List.ofFn x)).getD b false := by
  classical
  let κ : ℕ → Bool := fun t => decide (t < C.gates.length ∧ t ≠ j)
  have hk (t : ℕ) : κ t = true ↔ t < C.gates.length ∧ t ≠ j := by simp [κ]
  have hκ : ∀ t, κ t = true → t < C.gates.length := fun t h => ((hk t).mp h).1
  have hcl : ∀ (t : ℕ) (ht : t < C.gates.length), κ t = true →
      ∀ u ∈ C.gates[t].inputs, n ≤ u → u < n + t → κ (u - n) = true := by
    intro t ht _ u hu hn hut
    apply (hk _).mpr
    refine ⟨by omega, ?_⟩
    intro he
    have huj : u = n + j := by omega
    exact hno C.gates[t] (List.getElem_mem ht) (huj ▸ hu)
  have ho (o : ℕ) (hne : o ≠ n + j) :
      n ≤ o → o < n + C.gates.length → κ (o - n) = true := by
    intro hon hol
    exact (hk _).mpr ⟨by omega, by omega⟩
  let D : Circuit := ⟨Pruning.d3r1Pruned n κ C.gates, 0⟩
  let new : ℕ → ℕ := Pruning.d3r1New n κ (Pruning.d3r1Top κ C.gates)
  have hf : FanInTwo D := by
    intro g hg
    exact Pruning.pruned_fanInTwo n C κ hC g hg
  have hset : ((List.range C.size).filter κ).toFinset =
      (Finset.range C.size).erase j := by
    ext t
    simp [κ, Circuit.size, and_comm]
  have hc := List.toFinset_card_of_nodup ((List.nodup_range (n := C.size)).filter κ)
  rw [hset] at hc
  have he := Finset.card_erase_add_one (Finset.mem_range.mpr hj)
  simp only [Finset.card_range] at he
  have hsize : D.size + 1 = C.size := by
    change (Pruning.d3r1Pruned n κ C.gates).length + 1 = C.gates.length
    rw [Pruning.d3r1_pruned_length]
    change ((List.range C.size).filter κ).length + 1 = C.size
    omega
  refine ⟨D, new a, new b, hf, hsize, ?_⟩
  intro x
  exact ⟨Pruning.d3r1_prune_out false GateOp.eval (List.ofFn x) n (by simp)
      C.gates κ a hκ hcl (ho a ha),
    Pruning.d3r1_prune_out false GateOp.eval (List.ofFn x) n (by simp)
      C.gates κ b hκ hcl (ho b hb)⟩

lemma exists_live_pair (n : ℕ) (C : Circuit) (a b : ℕ) (hC : FanInTwo C) :
    ∃ (D : Circuit) (c d : ℕ), FanInTwo D ∧ D.size ≤ C.size ∧
      (∀ x : Fin n → Bool,
        (D.wires (List.ofFn x)).getD c false = (C.wires (List.ofFn x)).getD a false ∧
        (D.wires (List.ofFn x)).getD d false = (C.wires (List.ofFn x)).getD b false) ∧
      (∀ g ∈ D.gates, effectiveInputs g = g.inputs) ∧
      ∀ j < D.size, c ≠ n + j → d ≠ n + j →
        1 ≤ (effectiveSlots D).count (n + j) := by
  classical
  let P : ℕ → Prop := fun k => ∃ (E : Circuit) (c d : ℕ), FanInTwo E ∧ E.size = k ∧
    ∀ x : Fin n → Bool,
      (E.wires (List.ofFn x)).getD c false = (C.wires (List.ofFn x)).getD a false ∧
      (E.wires (List.ofFn x)).getD d false = (C.wires (List.ofFn x)).getD b false
  have hex : ∃ k, P k := ⟨C.size, C, a, b, hC, rfl, fun _ => ⟨rfl, rfl⟩⟩
  obtain ⟨E, c, d, hE, hsize, hsame⟩ := Nat.find_spec hex
  have hsmall : E.size ≤ C.size := by
    rw [hsize]
    exact Nat.find_min' hex ⟨C, a, b, hC, rfl, fun _ => ⟨rfl, rfl⟩⟩
  have hleast (F : Circuit) (e f : ℕ) (hF : FanInTwo F)
      (hpair : ∀ x : Fin n → Bool,
        (F.wires (List.ofFn x)).getD e false = (C.wires (List.ofFn x)).getD a false ∧
        (F.wires (List.ofFn x)).getD f false = (C.wires (List.ofFn x)).getD b false) :
      E.size ≤ F.size := by
    rw [hsize]
    exact Nat.find_min' hex ⟨F, e, f, hF, rfl, hpair⟩
  let D := normalize E
  have hD : FanInTwo D := normalize_fan E hE
  have hDsize : D.size = E.size := normalize_size E
  have hDsame (x : Fin n → Bool) :
      (D.wires (List.ofFn x)).getD c false = (C.wires (List.ofFn x)).getD a false ∧
      (D.wires (List.ofFn x)).getD d false = (C.wires (List.ofFn x)).getD b false := by
    simpa only [D, normalize_wires] using hsame x
  refine ⟨D, c, d, hD, by omega, hDsame, ?_, ?_⟩
  · exact fun g hg => normalize_effective E hg
  · intro j hj hc hd
    by_contra hcount
    have hz : (effectiveSlots D).count (n + j) = 0 := by omega
    have hnone : n + j ∉ effectiveSlots D := List.count_eq_zero.mp hz
    have hno : ∀ g ∈ D.gates, n + j ∉ g.inputs := by
      intro g hg hmem
      apply hnone
      apply List.mem_flatMap.mpr
      refine ⟨g, hg, ?_⟩
      rwa [normalize_effective E hg]
    obtain ⟨F, e, f, hF, hFsize, hFsame⟩ := delete_unused_pair n D c d j hD hj hc hd hno
    have hbound := hleast F e f hF (fun x =>
      ⟨((hFsame x).1).trans (hDsame x).1, ((hFsame x).2).trans (hDsame x).2⟩)
    omega

end LivePair

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

lemma no_read_two_partial_formula (f : FormulaTree)
    (hcount : ∀ i : Fin 10, formulaCount i f ≤ 2)
    (hrows : ∀ x : Fin 10 → Bool,
      PetersenBridge.petersen x = false ∨ (List.ofFn x).count true ≤ 2 →
      formulaValue x f = PetersenBridge.petersen x) : False := by
  have hpos (e : Fin 15) : formulaValue (PetersenBridge.edgeInput e) f = true :=
    (hrows _ (Or.inr (PetersenBridge.edgeInput_count e))).trans
      (PetersenBridge.edgeInput_positive e)
  have hneg (c : Fin 5) : formulaValue (PetersenBridge.independentInput c) f = false :=
    (hrows _ (Or.inl (PetersenBridge.independentInput_negative c))).trans
      (PetersenBridge.independentInput_negative c)
  obtain ⟨R, hcover, hlabels, hsound⟩ := exists_formula_rectangle_partition
    PetersenBridge.edgeInput PetersenBridge.independentInput f hpos hneg
  apply PetersenBridge.no_list_partition R
  · exact hcover
  · intro i
    exact (hlabels i).trans_le (hcount i)
  · intro r hr e he c hc
    exact PetersenBridge.input_sound e c r.1 ((hsound r hr).1 e he) ((hsound r hr).2 c hc)

lemma no_two_use_small_partial_source (C : Circuit) (a b : Fin 18) (hab : a ≠ b)
    (hC : FanInTwo C) (hsize : C.size ≤ 18)
    (hinputs : ∀ i < 10, 2 ≤ (effectiveSlots C).count i)
    (hgates : ∀ j < C.size, j ≠ a.val → j ≠ b.val →
      1 ≤ (effectiveSlots C).count (10 + j))
    (hrows : ∀ x : Fin 10 → Bool,
      PetersenBridge.petersen x = false ∨ (List.ofFn x).count true ≤ 2 →
      ((C.wires (List.ofFn x)).getD (10 + a.val) false ||
        (C.wires (List.ofFn x)).getD (10 + b.val) false) = PetersenBridge.petersen x) :
    False := by
  apply no_read_two_partial_formula (circuitFormula C (10 + a.val) (10 + b.val))
    (circuitFormula_count_le_two C a b hab hC hsize hinputs hgates)
  intro x hx
  have hbinary := (two_root_gate_rigidity C a.val b.val hC hsize hinputs hgates).2
  exact (circuitFormula_value C (10 + a.val) (10 + b.val) hbinary x).trans (hrows x hx)

namespace InputUnused

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_3821_aux

lemma append_equal_except (w z : List Bool) (p : ℕ) (a : Bool)
    (hlen : w.length = z.length)
    (h : ∀ j, j ≠ p → w.getD j false = z.getD j false) :
    ∀ j, j ≠ p → (w ++ [a]).getD j false = (z ++ [a]).getD j false := by
  intro j hj
  by_cases before : j < w.length
  · rw [List.getD_append _ _ _ _ before,
      List.getD_append _ _ _ _ (by omega)]
    exact h j hj
  · rw [List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega), hlen]

lemma fold_equal_except (gs : List Gate) (p : ℕ)
    (hno : ∀ g ∈ gs, p ∉ g.inputs)
    (w z : List Bool) (hlen : w.length = z.length)
    (h : ∀ j, j ≠ p → w.getD j false = z.getD j false) :
    ∀ j, j ≠ p →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])
        w).getD j false =
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])
        z).getD j false := by
  induction gs generalizing w z with
  | nil => exact h
  | cons g gs ih =>
    have he : g.op.eval (g.inputs.map fun k => w.getD k false) =
        g.op.eval (g.inputs.map fun k => z.getD k false) := by
      congr 1
      apply List.map_congr_left
      intro k hk
      exact h k (fun hkp => hno g List.mem_cons_self (hkp ▸ hk))
    simp only [List.foldl_cons]
    apply ih (fun g hg => hno g (List.mem_cons_of_mem _ hg))
    · simpa using hlen
    · rw [← he]
      exact append_equal_except w z p _ hlen h

lemma ofFn_equal_except {n : ℕ} (x y : Fin n → Bool) (p : ℕ)
    (h : ∀ i : Fin n, i.val ≠ p → x i = y i) :
    ∀ j, j ≠ p → (List.ofFn x).getD j false = (List.ofFn y).getD j false := by
  intro j hj
  by_cases hjn : j < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hjn),
      List.getD_eq_getElem _ _ (by simpa using hjn)]
    simpa using h ⟨j, hjn⟩ hj
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hjn),
      List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hjn)]

lemma wires_equal_except {n : ℕ} (C : Circuit) (p : ℕ)
    (hno : ∀ g ∈ C.gates, p ∉ g.inputs)
    (x y : Fin n → Bool)
    (hxy : ∀ i : Fin n, i.val ≠ p → x i = y i) :
    ∀ j, j ≠ p →
      (C.wires (List.ofFn x)).getD j false = (C.wires (List.ofFn y)).getD j false := by
  exact fold_equal_except C.gates p hno (List.ofFn x) (List.ofFn y)
    (by simp) (ofFn_equal_except x y p hxy)

lemma zero_count_wires_equal_except {n : ℕ} (C : Circuit) (p : ℕ)
    (heff : ∀ g ∈ C.gates, effectiveInputs g = g.inputs)
    (hzero : (effectiveSlots C).count p = 0)
    (x y : Fin n → Bool)
    (hxy : ∀ i : Fin n, i.val ≠ p → x i = y i) :
    ∀ j, j ≠ p →
      (C.wires (List.ofFn x)).getD j false = (C.wires (List.ofFn y)).getD j false := by
  apply wires_equal_except C p _ x y hxy
  intro g hg hp
  apply (List.count_eq_zero.mp hzero)
  apply List.mem_flatMap.mpr
  refine ⟨g, hg, ?_⟩
  rwa [heff g hg]

lemma positive_count_of_pair_change {n : ℕ} (C : Circuit) (p a b : ℕ)
    (heff : ∀ g ∈ C.gates, effectiveInputs g = g.inputs)
    (ha : a ≠ p) (hb : b ≠ p)
    (x y : Fin n → Bool)
    (hxy : ∀ i : Fin n, i.val ≠ p → x i = y i)
    (hchange :
      ((C.wires (List.ofFn x)).getD a false || (C.wires (List.ofFn x)).getD b false) ≠
      ((C.wires (List.ofFn y)).getD a false || (C.wires (List.ofFn y)).getD b false)) :
    1 ≤ (effectiveSlots C).count p := by
  by_contra hcount
  have hz : (effectiveSlots C).count p = 0 := by omega
  have h := zero_count_wires_equal_except C p heff hz x y hxy
  exact hchange (by rw [h a ha, h b hb])

end InputUnused

end PEqualNP.Outside.L_meta_3821_aux
