import CanonicalCompilerStructure
import CanonicalCompilerSamples
import CanonicalSampleFactsRemaining

namespace PEqualNP.Outside.L_meta_1896_aux.CanonicalCompiler

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma certified_positive {k : Nat} (program : Program 26 k) (certificates : List Nat)
    (hcheck : checkMasks k program sampleTruthMask sampleInputMasks certificates positiveResultMask = true)
    (p l : Fin 13) (hincident : AllRows.incidence p l) :
    circuitFun 26 (compile k program 26 Fin.val) (FourRows.pairInput p l) = true := by
  let a := Flags.indexFor p l
  have htruth : sampleTruthMask.testBit a.val = true :=
    sample_truth_bits ⟨a.val, by have h := a.isLt; omega⟩
  have hinputs (i : Fin 26) :
      (sampleInputMasks i).testBit a.val = FourRows.pairInput p l i := by
    rw [sample_positive_bits]
    exact congrFun (Flags.input_indexFor p l hincident) i
  have h := compile_mask_at k program sampleTruthMask sampleInputMasks certificates
    positiveResultMask a.val (FourRows.pairInput p l) htruth hinputs hcheck
  exact h.trans (sample_result_positive a)

lemma certified_negative_row {k : Nat} (program : Program 26 k) (certificates : List Nat)
    (hcheck : checkMasks k program sampleTruthMask sampleInputMasks certificates positiveResultMask = true)
    (r : AllRows.R) :
    circuitFun 26 (compile k program 26 Fin.val) (AllRows.row r) = false := by
  let index := 52 + 13 * r.1.val + r.2.val
  have hindex : index < 520 := by
    have h1 := r.1.isLt
    have h2 := r.2.isLt
    dsimp [index]
    omega
  have h := compile_mask_at k program sampleTruthMask sampleInputMasks certificates
    positiveResultMask index (AllRows.row r) (sample_truth_bits ⟨index, hindex⟩)
    (fun i => sample_negative_bits i r) hcheck
  exact h.trans (sample_result_negative r)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma refutes_posted (k : Nat) (program : Program 26 k) (certificates : List Nat)
    (hsmall : k < 51)
    (hcheck : checkMasks k program sampleTruthMask sampleInputMasks certificates positiveResultMask = true)
    (hcomplete : ∀ X : Finset (Fin 13), AllRows.admissible X →
      ∃ r : AllRows.R, AllRows.points r = X)
    (hrows : ∀ r : AllRows.R, AllRows.row r = AllRows.rowInput (AllRows.points r)) :
    ¬ (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 x4 : Fin (13 : ℕ)), x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ)) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x1 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x3 ∨ x6 = Fin.natAdd (13 : ℕ) x4)) = Bool.true) → (∀ (x4 : Finset (Fin (13 : ℕ))), (∀ x5 ∉ x4, ∃ (x7 : Fin (13 : ℕ)), (∀ x8 ∈ x4, ¬(x8 = x7 ∨ x8 = x7 + (1 : Fin (13 : ℕ)) ∨ x8 = x7 + (3 : Fin (13 : ℕ)) ∨ x8 = x7 + (9 : Fin (13 : ℕ)))) ∧ (x5 = x7 ∨ x5 = x7 + (1 : Fin (13 : ℕ)) ∨ x5 = x7 + (3 : Fin (13 : ℕ)) ∨ x5 = x7 + (9 : Fin (13 : ℕ)))) → ((¬∃ (x6 : Fin (13 : ℕ)), ∀ x7 ∈ x4, x7 = x6 ∨ x7 = x6 + (1 : Fin (13 : ℕ)) ∨ x7 = x6 + (3 : Fin (13 : ℕ)) ∨ x7 = x6 + (9 : Fin (13 : ℕ))) ∧ ¬∃ (x6 : Fin (13 : ℕ)), ∀ (x7 : Fin (13 : ℕ)), (∀ x8 ∈ x4, ¬(x8 = x7 ∨ x8 = x7 + (1 : Fin (13 : ℕ)) ∨ x8 = x7 + (3 : Fin (13 : ℕ)) ∨ x8 = x7 + (9 : Fin (13 : ℕ)))) → x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x1 fun (x7 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x8 ∈ x4, x7 = Fin.castAdd (13 : ℕ) x8) ∨ ∃ (x8 : Fin (13 : ℕ)), x7 = Fin.natAdd (13 : ℕ) x8 ∧ ∀ x9 ∈ x4, ¬(x9 = x8 ∨ x9 = x8 + (1 : Fin (13 : ℕ)) ∨ x9 = x8 + (3 : Fin (13 : ℕ)) ∨ x9 = x8 + (9 : Fin (13 : ℕ))))) = Bool.false) → (51 : ℕ) ≤ {x5 : Fin x1.gates.length | (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard) := by
  intro posted
  let C := compile k program 26 Fin.val
  have legal : Monotone2 C := compile_monotone2 k program 26 Fin.val
  have pos : ∀ p l : Fin 13, AllRows.incidence p l →
      circuitFun 26 C (FourRows.pairInput p l) = true := by
    intro p l hi
    exact certified_positive program certificates hcheck p l hi
  have neg : ∀ X : Finset (Fin 13), AllRows.admissible X →
      circuitFun 26 C (AllRows.rowInput X) = false := by
    intro X hX
    obtain ⟨r, hr⟩ := hcomplete X hX
    have h := certified_negative_row program certificates hcheck r
    rw [hrows r, hr] at h
    exact h
  have lower := posted C legal pos (by
    intro X hmax hgeneric
    exact neg X ⟨hmax, hgeneric⟩)
  have count : {j : Fin C.gates.length | (C.gates.get j).op = GateOp.or}.ncard = k :=
    compile_or_ncard k program 26 Fin.val
  rw [count] at lower
  omega

end PEqualNP.Outside.L_meta_1896_aux.CanonicalCompiler
