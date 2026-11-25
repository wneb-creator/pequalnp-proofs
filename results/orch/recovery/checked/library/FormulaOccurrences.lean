import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592.FormulaPruning

open PEqualNP.MetaComplexity

def occurs {n : Nat} : DMFormula n → Fin n → Nat
  | .lit j _, i => if j = i then 1 else 0
  | .and a b, i => occurs a i + occurs b i
  | .or a b, i => occurs a i + occurs b i

def literalTable (i : Fin 3) (b : Bool) : Nat :=
  let p := if i.val = 0 then 170 else if i.val = 1 then 204 else 240
  if b then p else Nat.xor 255 p

def pruningTables : DMFormula 3 → List Nat
  | .lit i b => [0, 255, literalTable i b]
  | .and a b => ([0, 255] ++ (pruningTables a).flatMap
      (fun x => (pruningTables b).map (Nat.land x))).eraseDups
  | .or a b => ([0, 255] ++ (pruningTables a).flatMap
      (fun x => (pruningTables b).map (Nat.lor x))).eraseDups

end PEqualNP.Outside.L_meta_2592.FormulaPruning

namespace PEqualNP.Outside.L_meta_2592.FormulaPruning

open PEqualNP.MetaComplexity

lemma sum_occurs {n : Nat} (φ : DMFormula n) :
    (∑ i : Fin n, occurs φ i) = φ.leaves := by
  induction φ with
  | lit j b => simp [occurs, DMFormula.leaves]
  | and a b ha hb => simp [occurs, DMFormula.leaves, Finset.sum_add_distrib, ha, hb]
  | or a b ha hb => simp [occurs, DMFormula.leaves, Finset.sum_add_distrib, ha, hb]

lemma two_small_entries (c : Fin 10 → Nat) (bound : (∑ i, c i) ≤ 17) :
    ∃ u v : Fin 10, u ≠ v ∧ c u ≤ 1 ∧ c v ≤ 1 := by
  have some : ∃ u : Fin 10, c u ≤ 1 := by
    by_contra! h
    have lower : (∑ i : Fin 10, 2) ≤ ∑ i, c i :=
      Finset.sum_le_sum (fun i _ => by have := h i; omega)
    norm_num at lower
    omega
  obtain ⟨u, hu⟩ := some
  by_contra! h
  have lower : (∑ i : Fin 10, if i = u then 0 else 2) ≤ ∑ i, c i := by
    apply Finset.sum_le_sum
    intro i _
    split_ifs with same
    · exact Nat.zero_le _
    · have hv := h u i (Ne.symm same) hu
      omega
  have value : ∀ u : Fin 10, (∑ i : Fin 10, if i = u then 0 else 2) = 18 := by
    decide +kernel
  rw [value u] at lower
  omega

lemma two_single_occurrences (φ : DMFormula 10) (bound : φ.leaves ≤ 17) :
    ∃ u v : Fin 10, u ≠ v ∧ occurs φ u ≤ 1 ∧ occurs φ v ≤ 1 := by
  apply two_small_entries (occurs φ)
  simpa only [sum_occurs] using bound

lemma triple_occurrences_at_most_four {n : Nat} (φ : DMFormula n)
    (readTwo : ∀ i, occurs φ i ≤ 2)
    (u v a b c : Fin n) (different : u ≠ v)
    (hu : occurs φ u ≤ 1) (hv : occurs φ v ≤ 1)
    (u_in : u = a ∨ u = b ∨ u = c) (v_in : v = a ∨ v = b ∨ v = c) :
    occurs φ a + occurs φ b + occurs φ c ≤ 4 := by
  have ha := readTwo a
  have hb := readTwo b
  have hc := readTwo c
  rcases u_in with rfl | rfl | rfl <;>
    rcases v_in with rfl | rfl | rfl <;> omega

end PEqualNP.Outside.L_meta_2592.FormulaPruning
