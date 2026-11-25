import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2089.OperandWitness

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def delta : Finset (Fin 13) := {0, 1, 3, 9}

def incidence (p l : Fin 13) : Prop := ∃ d ∈ delta, p = l + d

def pairInput (p l : Fin 13) (i : Fin 26) : Bool :=
  decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)

def singletonInput (i j : Fin 26) : Bool := decide (j = i)

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

def badPairSet (f : (Fin 26 → Bool) → Bool) : Finset (Fin 13 × Fin 13) := by
  letI : DecidableRel incidence := fun p l => by unfold incidence; infer_instance
  exact Finset.univ.filter fun e => ¬incidence e.1 e.2 ∧ f (pairInput e.1 e.2) = true

def circuit : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 1]⟩,
      ⟨GateOp.or, [13, 14]⟩,
      ⟨GateOp.or, [27, 17]⟩,
      ⟨GateOp.or, [28, 18]⟩,
      ⟨GateOp.or, [29, 23]⟩,
      ⟨GateOp.or, [30, 24]⟩,
      ⟨GateOp.or, [31, 25]⟩,
      ⟨GateOp.and, [26, 32]⟩,
      ⟨GateOp.or, [2, 3]⟩,
      ⟨GateOp.or, [13, 14]⟩,
      ⟨GateOp.or, [35, 15]⟩,
      ⟨GateOp.or, [36, 16]⟩,
      ⟨GateOp.or, [37, 19]⟩,
      ⟨GateOp.or, [38, 20]⟩,
      ⟨GateOp.or, [39, 25]⟩,
      ⟨GateOp.and, [34, 40]⟩,
      ⟨GateOp.or, [14, 16]⟩,
      ⟨GateOp.or, [42, 17]⟩,
      ⟨GateOp.or, [43, 21]⟩,
      ⟨GateOp.and, [4, 44]⟩,
      ⟨GateOp.or, [15, 17]⟩,
      ⟨GateOp.or, [46, 18]⟩,
      ⟨GateOp.or, [47, 22]⟩,
      ⟨GateOp.and, [5, 48]⟩,
      ⟨GateOp.or, [16, 18]⟩,
      ⟨GateOp.or, [50, 19]⟩,
      ⟨GateOp.or, [51, 23]⟩,
      ⟨GateOp.and, [6, 52]⟩,
      ⟨GateOp.or, [17, 19]⟩,
      ⟨GateOp.or, [54, 20]⟩,
      ⟨GateOp.or, [55, 24]⟩,
      ⟨GateOp.and, [7, 56]⟩,
      ⟨GateOp.or, [18, 20]⟩,
      ⟨GateOp.or, [58, 21]⟩,
      ⟨GateOp.or, [59, 25]⟩,
      ⟨GateOp.and, [8, 60]⟩,
      ⟨GateOp.or, [13, 19]⟩,
      ⟨GateOp.or, [62, 21]⟩,
      ⟨GateOp.or, [63, 22]⟩,
      ⟨GateOp.and, [9, 64]⟩,
      ⟨GateOp.or, [14, 20]⟩,
      ⟨GateOp.or, [66, 22]⟩,
      ⟨GateOp.or, [67, 23]⟩,
      ⟨GateOp.and, [10, 68]⟩,
      ⟨GateOp.or, [15, 21]⟩,
      ⟨GateOp.or, [70, 23]⟩,
      ⟨GateOp.or, [71, 24]⟩,
      ⟨GateOp.and, [11, 72]⟩,
      ⟨GateOp.or, [16, 22]⟩,
      ⟨GateOp.or, [74, 24]⟩,
      ⟨GateOp.or, [75, 25]⟩,
      ⟨GateOp.and, [12, 76]⟩,
      ⟨GateOp.or, [33, 41]⟩,
      ⟨GateOp.or, [78, 45]⟩,
      ⟨GateOp.or, [79, 49]⟩,
      ⟨GateOp.or, [80, 53]⟩,
      ⟨GateOp.or, [81, 57]⟩,
      ⟨GateOp.or, [82, 61]⟩,
      ⟨GateOp.or, [83, 65]⟩,
      ⟨GateOp.or, [84, 69]⟩,
      ⟨GateOp.or, [85, 73]⟩,
      ⟨GateOp.or, [86, 77]⟩ ]
    output := 87 }

def wireFun (x : Fin 26 → Bool) : Bool := value circuit x circuit.output

def badPairs : Finset (Fin 13 × Fin 13) :=
  {(0, 1), (0, 5), (0, 11), (1, 4), (1, 10), (1, 12), (2, 0), (2, 3), (2, 7), (3, 1), (3, 6), (3, 12)}

def pairResult (p l : Fin 13) : Bool :=
  decide ((∃ d ∈ delta, p = l + d) ∨ (p, l) ∈ badPairs)

lemma circuit_monotone : Monotone2 circuit := by
  simp [Monotone2, circuit]

lemma circuit_size : circuit.size = 62 := rfl

lemma output_valid : circuit.output < 26 + circuit.size := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma pair_values : ∀ p l : Fin 13, wireFun (pairInput p l) = pairResult p l := by
  unfold wireFun value circuit pairInput pairResult delta badPairs
  decide +kernel

lemma incident_accepted (p l : Fin 13) (h : incidence p l) :
    wireFun (pairInput p l) = true := by
  rw [pair_values]
  simp only [pairResult, decide_eq_true_eq]
  exact Or.inl h

lemma bad_pairs_nonincident : ∀ e ∈ badPairs, ¬incidence e.1 e.2 := by
  unfold badPairs incidence delta
  decide +kernel

lemma bad_pair_set : badPairSet wireFun = badPairs := by
  ext e
  rcases e with ⟨p, l⟩
  simp only [badPairSet, Finset.mem_filter, Finset.mem_univ, true_and,
    pair_values, pairResult, decide_eq_true_eq]
  change (¬incidence p l ∧ (incidence p l ∨ (p, l) ∈ badPairs)) ↔ (p, l) ∈ badPairs
  have hn := bad_pairs_nonincident (p, l)
  tauto

lemma bad_pair_card : (badPairSet wireFun).card = 12 := by
  rw [bad_pair_set]
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma singletons_rejected : ∀ i : Fin 26, wireFun (singletonInput i) = false := by
  unfold wireFun value circuit singletonInput
  decide +kernel

lemma properties : Monotone2 circuit ∧ circuit.size = 62 ∧
    circuit.output < 26 + circuit.size ∧
    (∀ p l, incidence p l → wireFun (pairInput p l) = true) ∧
    (badPairSet wireFun).card = 12 ∧
    (∀ i : Fin 26, wireFun (singletonInput i) = false) :=
  ⟨circuit_monotone, circuit_size, output_valid, incident_accepted,
    bad_pair_card, singletons_rejected⟩

end PEqualNP.Outside.L_meta_2089.OperandWitness
