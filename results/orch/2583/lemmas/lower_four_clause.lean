import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583_aux.FourClause

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

abbrev Row := Fin 64
abbrev Matrix := Fin 512

def bit (r : Row) (v : Fin 6) : Bool := r.val.testBit v.val

def adj (m : Matrix) (p l : Fin 3) : Bool := m.val.testBit (3 * p.val + l.val)

def valid (m : Matrix) : Prop :=
  (∀ p : Fin 3, adj m p p = true) ∧
  (∀ p p' l l' : Fin 3, p ≠ p' → l ≠ l' →
    ¬ (adj m p l = true ∧ adj m p' l = true ∧ adj m p l' = true ∧ adj m p' l' = true))

def rows (m : Matrix) : List ℕ :=
  match m.val with
  | 273 => [7, 14, 21, 28, 35]
  | 275 => [7, 14, 28, 35, 42]
  | 277 => [7, 14, 21, 28, 42]
  | 279 => [7, 14, 28, 42, 56]
  | 281 => [7, 21, 28, 35, 49]
  | 285 => [7, 21, 28, 34, 56]
  | 305 => [7, 14, 21, 28, 49]
  | 307 => [7, 14, 28, 33, 56]
  | 309 => [7, 14, 21, 28, 56]
  | 313 => [7, 21, 28, 49, 56]
  | 337 => [7, 21, 35, 42, 49]
  | 339 => [7, 20, 35, 42, 56]
  | 345 => [7, 21, 35, 49, 56]
  | 369 => [7, 10, 21, 49, 56]
  | 371 => [7, 10, 20, 33, 56]
  | 401 => [7, 14, 35, 42, 49]
  | 403 => [7, 14, 35, 42, 56]
  | 405 => [7, 14, 17, 42, 56]
  | 409 => [7, 12, 35, 49, 56]
  | 413 => [7, 12, 17, 34, 56]
  | 465 => [7, 35, 42, 49, 56]
  | _ => []

def witness (m : Matrix) (i : Fin 5) : Row := Fin.ofNat 64 ((rows m).getD i.val 0)

def independent (m : Matrix) (r : Row) : Prop :=
  ∀ p l : Fin 3, adj m p l = true →
    ¬ (bit r (Fin.castAdd 3 p) = true ∧ bit r (Fin.natAdd 3 l) = true)

def pairCovered (r s : Row) : Prop :=
  ∃ p : Fin 3,
    (bit r (Fin.castAdd 3 p) = true ∨ bit s (Fin.castAdd 3 p) = true) ∧
    (bit r (Fin.natAdd 3 p) = true ∨ bit s (Fin.natAdd 3 p) = true)

theorem certificate : ∀ m : Matrix, valid m →
    (∀ i : Fin 5, independent m (witness m i)) ∧
    (∀ i j : Fin 5, i ≠ j → pairCovered (witness m i) (witness m j)) := by
  letI (m : Matrix) : Decidable (valid m) := by unfold valid; infer_instance
  letI (m : Matrix) (r : Row) : Decidable (independent m r) := by unfold independent; infer_instance
  letI (r s : Row) : Decidable (pairCovered r s) := by unfold pairCovered; infer_instance
  decide

theorem clauses_ge_five {k : ℕ} (m : Matrix) (hm : valid m)
    (clauses : Fin k → Finset (Fin 6))
    (hmatching : ∀ j p, Fin.castAdd 3 p ∈ clauses j ∨ Fin.natAdd 3 p ∈ clauses j)
    (hclean : ∀ x : Fin 6 → Bool,
      (∀ j, ∃ v ∈ clauses j, x v = true) →
      ∃ p l : Fin 3, adj m p l = true ∧
        x (Fin.castAdd 3 p) = true ∧ x (Fin.natAdd 3 l) = true) :
    5 ≤ k := by
  classical
  have hc := certificate m hm
  have hex (i : Fin 5) : ∃ j, ¬ ∃ v ∈ clauses j, bit (witness m i) v = true := by
    by_contra h
    push_neg at h
    obtain ⟨p, l, hpl, hp, hl⟩ := hclean (bit (witness m i)) h
    exact hc.1 i p l hpl ⟨hp, hl⟩
  choose selected hselected using hex
  have hinj : Function.Injective selected := by
    intro i j hij
    by_contra hne
    obtain ⟨p, hp, hl⟩ := hc.2 i j hne
    rcases hmatching (selected i) p with hmem | hmem
    · rcases hp with hi | hj
      · exact hselected i ⟨_, hmem, hi⟩
      · exact hselected j ⟨_, hij ▸ hmem, hj⟩
    · rcases hl with hi | hj
      · exact hselected i ⟨_, hmem, hi⟩
      · exact hselected j ⟨_, hij ▸ hmem, hj⟩
  have hcard := Fintype.card_le_of_injective selected hinj
  simpa using hcard

theorem four_clauses_impossible (m : Matrix) (hm : valid m)
    (clauses : Fin 4 → Finset (Fin 6))
    (hmatching : ∀ j p, Fin.castAdd 3 p ∈ clauses j ∨ Fin.natAdd 3 p ∈ clauses j)
    (hclean : ∀ x : Fin 6 → Bool,
      (∀ j, ∃ v ∈ clauses j, x v = true) →
      ∃ p l : Fin 3, adj m p l = true ∧
        x (Fin.castAdd 3 p) = true ∧ x (Fin.natAdd 3 l) = true) : False := by
  have := clauses_ge_five m hm clauses hmatching hclean
  omega

end PEqualNP.Outside.L_meta_2583_aux.FourClause
