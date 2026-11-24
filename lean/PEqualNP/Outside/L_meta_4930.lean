import Mathlib.Data.List.GetD

namespace PEqualNP.Outside.L_meta_4930_aux

def inputs : List (BitVec 58) := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752]

def target : BitVec 58 := 2097151

lemma input_count : inputs.length = 14 := rfl

lemma incomparable_inputs : ∀ i : Fin 14,
    target &&& inputs.getD i.val 0 ≠ target ∧
    target &&& inputs.getD i.val 0 ≠ inputs.getD i.val 0 := by
  decide

lemma and_input_ne_target (i : Fin 14) (v : BitVec 58) :
    inputs.getD i.val 0 &&& v ≠ target := by
  intro h
  have hsub : target &&& inputs.getD i.val 0 = target := by
    rw [← h]
    rw [BitVec.and_comm (inputs.getD i.val 0 &&& v) (inputs.getD i.val 0)]
    rw [← BitVec.and_assoc, BitVec.and_self]
  exact (incomparable_inputs i).1 hsub

lemma or_input_ne_target (i : Fin 14) (v : BitVec 58) :
    inputs.getD i.val 0 ||| v ≠ target := by
  intro h
  have hsub : target &&& inputs.getD i.val 0 = inputs.getD i.val 0 := by
    rw [← h]
    apply BitVec.eq_of_getElem_eq
    intro j hj
    simp only [BitVec.getElem_and, BitVec.getElem_or]
    cases (inputs.getD i.val 0)[j] <;> simp
  exact (incomparable_inputs i).2 hsub


lemma target_gate_indices (w : List (BitVec 58))
    (hw : ∀ i : Fin 14, w.getD i.val 0 = inputs.getD i.val 0)
    (op : Bool) (a b : ℕ)
    (h : (if op = true then w.getD a 0 &&& w.getD b 0 else
      w.getD a 0 ||| w.getD b 0) = target) : 14 ≤ a ∧ 14 ≤ b := by
  have ha : ¬ a < 14 := by
    intro ha
    rw [hw ⟨a, ha⟩] at h
    cases op <;> simp only [Bool.false_eq_true, ite_false, ite_true] at h
    · exact or_input_ne_target ⟨a, ha⟩ _ h
    · exact and_input_ne_target ⟨a, ha⟩ _ h
  have hb : ¬ b < 14 := by
    intro hb
    rw [hw ⟨b, hb⟩] at h
    cases op <;> simp only [Bool.false_eq_true, ite_false, ite_true] at h
    · rw [BitVec.or_comm] at h
      exact or_input_ne_target ⟨b, hb⟩ _ h
    · rw [BitVec.and_comm] at h
      exact and_input_ne_target ⟨b, hb⟩ _ h
  omega

end PEqualNP.Outside.L_meta_4930_aux
