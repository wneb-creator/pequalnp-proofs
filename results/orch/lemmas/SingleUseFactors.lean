import Mathlib.Data.List.Count
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

namespace PEqualNP.Outside.L_meta_10760_aux.SingleUseFactors

def binary (d a b : Bool) : Bool := if d then a || b else a && b

lemma partner_value (d a : Bool) (H : Bool → Bool)
    (diff : H (binary d false a) ≠ H (binary d true a)) : a = !d := by
  cases d <;> cases a <;> simp [binary] at *

def target (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 2) || (x 1 && x 3) || (x 0 && x 4) || (x 1 && x 4) ||
  (x 2 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 3 && x 5) ||
  (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 5 && x 6)

def point (b : Fin 128) (i : Fin 7) : Bool := b.val.testBit i.val

def force (i : Fin 7) (x : Fin 7 → Bool) : Fin 7 → Bool :=
  fun j => if j = i then true else x j

def critical (i j : Fin 7) (d : Bool) (b : Fin 128) : Prop :=
  point b i = false ∧ target (point b) = false ∧
    target (force i (point b)) = true ∧ point b j = d

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma critical_exists : ∀ (i j : Fin 7) (d : Bool), i ≠ j →
    ∃ b : Fin 128, critical i j d b := by
  unfold critical
  decide +kernel

lemma no_raw_partner (i j : Fin 7) (ne : i ≠ j) (d : Bool)
    (K : Bool → (Fin 7 → Bool) → Bool)
    (blind : ∀ z x, K z (force i x) = K z x)
    (factor : ∀ x, target x = K (binary d (x i) (x j)) x) : False := by
  obtain ⟨b, hi, low, high, hj⟩ := critical_exists i j d ne
  have ji : j ≠ i := Ne.symm ne
  have same : binary d (force i (point b) i) (force i (point b) j) =
      binary d (point b i) (point b j) := by
    cases d <;> simp [binary, force, ji, hi, hj]
  have eq : target (force i (point b)) = target (point b) := by
    rw [factor, factor, same, blind]
  rw [high, low] at eq
  contradiction

def changes (i : Fin 7) (b : Fin 128) : Prop :=
  point b i = false ∧ target (point b) = false ∧
    target (force i (point b)) = true

lemma negative_partner (i j : Fin 7) (ne : i ≠ j) (d : Bool) :
    ∃ b : Fin 128, changes i b ∧ !(point b j) = d := by
  obtain ⟨b, hi, low, high, hj⟩ := critical_exists i j (!d) ne
  refine ⟨b, ⟨hi, low, high⟩, ?_⟩
  cases d <;> simp [hj]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma and_partner_not_binary : ∀ (i p q : Fin 7) (d : Bool),
    i ≠ p → i ≠ q → ∃ b : Fin 128, changes i b ∧
      binary d (point b p) (point b q) = false := by
  intro i
  fin_cases i <;> unfold changes <;> decide +kernel

def edge (p q : Fin 7) : Prop :=
  target (fun k => decide (k = p ∨ k = q)) = true

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma or_partner_binary_class : ∀ (i p q : Fin 7) (d : Bool),
    i ≠ p → i ≠ q →
    (∀ b : Fin 128, changes i b → binary d (point b p) (point b q) = false) →
      d = false ∧ edge p q := by
  intro i
  fin_cases i <;> unfold changes edge <;> decide +kernel

end PEqualNP.Outside.L_meta_10760_aux.SingleUseFactors
