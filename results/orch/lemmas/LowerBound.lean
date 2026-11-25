import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def effectiveInputs (g : Gate) : List ℕ :=
  match g.op with
  | .not => g.inputs.take 1
  | _ => g.inputs

def negCharge (g : Gate) : ℕ :=
  match g.op with
  | .not => 1
  | _ => 0

lemma effectiveInputs_budget (g : Gate) (h : g.inputs.length ≤ 2) :
    (effectiveInputs g).length + negCharge g ≤ 2 := by
  cases hop : g.op <;> simp [effectiveInputs, negCharge, hop] <;> omega

lemma effectiveRead_budget (gs : List Gate)
    (fan : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (gs.flatMap effectiveInputs).length + (gs.map negCharge).sum ≤ 2 * gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have head := effectiveInputs_budget g (fan g (by simp))
    have tail := ih (by intro a ha; exact fan a (by simp [ha]))
    simp only [List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons,
      List.length_cons]
    omega

lemma negCharge_positive (gs : List Gate)
    (hasNot : ∃ g ∈ gs, g.op = GateOp.not) : 1 ≤ (gs.map negCharge).sum := by
  induction gs with
  | nil => simp at hasNot
  | cons g gs ih =>
    obtain ⟨a, ha, hop⟩ := hasNot
    rcases List.mem_cons.mp ha with rfl | ha
    · simp [negCharge, hop]
    · have tail := ih ⟨a, ha, hop⟩
      simp only [List.map_cons, List.sum_cons]
      omega

lemma all_inputs_branch_budget (C : Circuit) (fan : FanInTwo C)
    (hasNot : ∃ g ∈ C.gates, g.op = GateOp.not)
    (allReads :
      (List.range 10 ++ List.range 10 ++ (List.range (C.size - 1)).map (10 + ·)).Subperm
        (C.gates.flatMap effectiveInputs)) :
    20 ≤ C.size := by
  have reads := allReads.length_le
  have budget := effectiveRead_budget C.gates (by intro g hg; exact (fan g hg).2)
  have positive := negCharge_positive C.gates hasNot
  simp only [List.length_append, List.length_range, List.length_map] at reads
  change 20 + (C.size - 1) ≤ _ at reads
  change _ + _ ≤ 2 * C.size at budget
  omega

def petersenValue (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

lemma and_input_witness : ∀ v u : Fin 10, v ≠ u → ∃ w : Fin 10,
    w ≠ v ∧ w ≠ u ∧
      petersenValue (fun i => decide (i = w)) = false ∧
      petersenValue (fun i => decide (i = w) || decide (i = v)) = true := by
  decide +kernel

lemma or_input_witness : ∀ v u : Fin 10, v ≠ u → ∃ w : Fin 10,
    w ≠ v ∧ w ≠ u ∧
      petersenValue (fun i => decide (i = u) || decide (i = w)) = false ∧
      petersenValue (fun i => decide (i = u) || decide (i = w) || decide (i = v)) = true := by
  decide +kernel

lemma single_use_and_input_impossible (v u : Fin 10) (different : v ≠ u)
    (factor : ∀ x y : Fin 10 → Bool,
      (∀ i, i ≠ v → x i = y i) →
      (x v && x u) = (y v && y u) → petersenValue x = petersenValue y) : False := by
  obtain ⟨w, wv, wu, no, yes⟩ := and_input_witness v u different
  have same := factor (fun i => decide (i = w))
    (fun i => decide (i = w) || decide (i = v))
    (by intro i hi; simp [hi])
    (by simp [Ne.symm wv, Ne.symm wu, Ne.symm different])
  rw [no, yes] at same
  cases same

lemma single_use_or_input_impossible (v u : Fin 10) (different : v ≠ u)
    (factor : ∀ x y : Fin 10 → Bool,
      (∀ i, i ≠ v → x i = y i) →
      (x v || x u) = (y v || y u) → petersenValue x = petersenValue y) : False := by
  obtain ⟨w, wv, wu, no, yes⟩ := or_input_witness v u different
  have same := factor (fun i => decide (i = u) || decide (i = w))
    (fun i => decide (i = u) || decide (i = w) || decide (i = v))
    (by intro i hi; simp [hi])
    (by simp)
  rw [no, yes] at same
  cases same

end PEqualNP.Outside.L_meta_2592_aux
