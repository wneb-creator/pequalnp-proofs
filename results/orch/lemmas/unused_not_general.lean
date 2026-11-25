import endpoint_unused

namespace PEqualNP.Outside.L_meta_1886_aux.EndpointOrder

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2592_aux
open ConstantSweep MapRigidity

lemma not_wire_output (pre suffix : List Gate) (source : Nat) (rest : List Nat) (w : List Bool) :
    (Circuit.mk (pre ++ ⟨.not,source :: rest⟩ :: suffix) (w.length + pre.length)).eval w =
      !((run pre w).getD source false) := by
  change (run (pre ++ ⟨.not,source :: rest⟩ :: suffix) w).getD (w.length + pre.length) false = _
  rw [run_append]
  change (run suffix (run pre w ++ [!((run pre w).getD source false)])).getD (w.length + pre.length) false = _
  rw [run_prefix _ _ _ (by simp [run_length]),←run_length pre w,getD_last]

lemma not_output_impossible (pre suffix : List Gate) (source outIdx : Nat) (rest : List Nat)
    (monoPre : ∀ g ∈ pre, g.op = .and ∨ g.op = .or)
    (computes : ∀ x : Fin 10 → Bool,
      (Circuit.mk (pre ++ ⟨.not,source :: rest⟩ :: suffix) outIdx).eval (initial x) = edge10 x) :
    outIdx ≠ 11 + pre.length := by
  intro eq
  let xzero : Fin 10 → Bool := fun _ => false
  let xone : Fin 10 → Bool := fun _ => true
  have low := computes xzero
  have high := computes xone
  rw [eq] at low high
  have lowEval := not_wire_output pre suffix source rest (initial xzero)
  have highEval := not_wire_output pre suffix source rest (initial xone)
  rw [initial_length] at lowEval highEval
  rw [lowEval,show edge10 xzero = false from rfl] at low
  rw [highEval,show edge10 xone = true from rfl] at high
  have initOrder : List.Forall₂ (· ≤ ·) (initial xzero) (initial xone) := by decide +kernel
  have order : (run pre (initial xzero)).getD source false ≤ (run pre (initial xone)).getD source false :=
    OneNot.read_le (OneNot.run_le pre monoPre initOrder) source
  cases hl : (run pre (initial xzero)).getD source false <;>
    cases hh : (run pre (initial xone)).getD source false <;> simp_all [Bool.le_iff_imp]

lemma unused_not_replace_any (pre suffix : List Gate) (source outIdx : Nat) (rest : List Nat)
    (monoPre : ∀ g ∈ pre, g.op = .and ∨ g.op = .or)
    (monoSuffix : ∀ g ∈ suffix, g.op = .and ∨ g.op = .or)
    (unused : ∀ g ∈ suffix, 11 + pre.length ∉ g.inputs)
    (computes : ∀ x : Fin 10 → Bool,
      (Circuit.mk (pre ++ ⟨.not,source :: rest⟩ :: suffix) outIdx).eval (initial x) = edge10 x)
    (b : Bool) : ∀ x : Fin 10 → Bool,
      (Circuit.mk suffix outIdx).eval (run pre (initial x) ++ [b]) = edge10 x := by
  have outputDifferent := not_output_impossible pre suffix source outIdx rest monoPre computes
  intro x
  let w := run pre (initial x)
  have len : w.length = 11 + pre.length := by simp [w,run_length,initial_length]
  have same := unused_last_output suffix w outIdx b (!(w.getD source false)) monoSuffix
    (fun g hg => by rw [len]; exact unused g hg) (by rw [len]; exact outputDifferent)
  have h := computes x
  change (run (pre ++ ⟨.not,source :: rest⟩ :: suffix) (initial x)).getD outIdx false = _ at h
  rw [run_append] at h
  change (run suffix (w ++ [!(w.getD source false)])).getD outIdx false = _ at h
  change (run suffix (w ++ [b])).getD outIdx false = _
  exact same.trans h

end PEqualNP.Outside.L_meta_1886_aux.EndpointOrder
