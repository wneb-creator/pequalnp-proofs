import Mathlib.Data.Fin.Basic

namespace PEqualNP.Outside.L_meta_2592_aux

def edgeValue (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
  (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) ||
  (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
  (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) ||
  (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)

def singleInput (u : Fin 10) : Fin 10 → Bool := fun i => decide (i = u)

def pairInput (u v : Fin 10) : Fin 10 → Bool := fun i => decide (i = u ∨ i = v)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma two_false_witness : ∀ v a b : Fin 10, v ≠ a → v ≠ b →
    ∃ u : Fin 10, u ≠ a ∧ u ≠ b ∧ u ≠ v ∧
      edgeValue (singleInput u) = false ∧ edgeValue (pairInput v u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma one_true_witness : ∀ v a : Fin 10, v ≠ a →
    ∃ u : Fin 10, u ≠ v ∧
      edgeValue (pairInput a u) = false ∧
      edgeValue (fun i => decide (i = v ∨ i = a ∨ i = u)) = true := by
  decide +kernel

def Critical (v : Fin 10) (x : Fin 10 → Bool) : Prop :=
  x v = false ∧ edgeValue x = false ∧ edgeValue (Function.update x v true) = true

lemma single_update (u v : Fin 10) :
    Function.update (singleInput u) v true = pairInput v u := by
  funext i
  by_cases hi : i = v
  · subst i
    simp [singleInput, pairInput]
  · simp [Function.update_of_ne hi, singleInput, pairInput, hi]

lemma pair_update (v a u : Fin 10) :
    Function.update (pairInput a u) v true =
      (fun i => decide (i = v ∨ i = a ∨ i = u)) := by
  funext i
  by_cases hi : i = v
  · subst i
    simp [pairInput]
  · simp [Function.update_of_ne hi, pairInput, hi]

lemma no_binary_partner (v a b : Fin 10) (isAnd : Bool) (ha : v ≠ a) (hb : v ≠ b) :
    ¬ ∀ x : Fin 10 → Bool, Critical v x →
      (if isAnd then x a && x b else x a || x b) = true := by
  intro partner
  obtain ⟨u, hua, hub, huv, hzero, hedge⟩ := two_false_witness v a b ha hb
  have hcrit : Critical v (singleInput u) := by
    refine ⟨?_, hzero, ?_⟩
    · simp [singleInput, Ne.symm huv]
    · rw [single_update]
      exact hedge
  have bad := partner (singleInput u) hcrit
  simp [singleInput, Ne.symm hua, Ne.symm hub] at bad

lemma no_negated_partner (v a : Fin 10) (ha : v ≠ a) :
    ¬ ∀ x : Fin 10 → Bool, Critical v x → (!x a) = true := by
  intro partner
  obtain ⟨u, huv, hzero, hedge⟩ := one_true_witness v a ha
  have hcrit : Critical v (pairInput a u) := by
    refine ⟨?_, hzero, ?_⟩
    · simp [pairInput, ha, Ne.symm huv]
    · rw [pair_update]
      exact hedge
  have bad := partner (pairInput a u) hcrit
  simp [pairInput] at bad

end PEqualNP.Outside.L_meta_2592_aux
