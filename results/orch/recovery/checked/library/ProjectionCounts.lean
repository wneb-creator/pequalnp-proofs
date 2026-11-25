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

def joinProjection (isOr : Bool) : Option (DMFormula 3) → Option (DMFormula 3) →
    Option (DMFormula 3)
  | none, b => b
  | a, none => a
  | some a, some b => some (if isOr then .or a b else .and a b)

def project {n : Nat} (ρ : Fin n → Option (Fin 3)) : DMFormula n → Option (DMFormula 3)
  | .lit i b => (ρ i).map (fun j => .lit j b)
  | .and a b => joinProjection false (project ρ a) (project ρ b)
  | .or a b => joinProjection true (project ρ a) (project ρ b)

def tablesOpt : Option (DMFormula 3) → List Nat
  | none => [0,255]
  | some a => pruningTables a

def occursOpt (a : Option (DMFormula 3)) (i : Fin 3) : Nat :=
  match a with
  | none => 0
  | some φ => occurs φ i

def leavesOpt : Option (DMFormula 3) → Nat
  | none => 0
  | some φ => φ.leaves

def cofactorInput {n : Nat} (ρ : Fin n → Option (Fin 3)) (base : Fin n → Bool)
    (r : Fin 8) (i : Fin n) : Bool :=
  match ρ i with
  | none => base i
  | some j => r.val.testBit j.val

def realizes (a : Option (DMFormula 3)) (f : Fin 8 → Bool) : Prop :=
  ∃ t ∈ tablesOpt a, ∀ r, f r = t.testBit r.val

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

namespace PEqualNP.Outside.L_meta_2592.FormulaPruning

open PEqualNP.MetaComplexity

lemma occursOpt_joinProjection (isOr : Bool) (a b : Option (DMFormula 3)) (j : Fin 3) :
    occursOpt (joinProjection isOr a b) j = occursOpt a j + occursOpt b j := by
  cases a <;> cases b <;> cases isOr <;> simp [joinProjection, occursOpt, occurs]

lemma occurs_project_unique {n : Nat} (ρ : Fin n → Option (Fin 3))
    (φ : DMFormula n) (i : Fin n) (j : Fin 3)
    (unique : ∀ k, ρ k = some j ↔ k = i) :
    occursOpt (project ρ φ) j = occurs φ i := by
  induction φ with
  | lit k b =>
    cases value : ρ k with
    | none =>
      have different : k ≠ i := by
        intro same
        have hit := (unique k).mpr same
        simp [value] at hit
      simp [project, value, occursOpt, occurs, different]
    | some l =>
      have same : l = j ↔ k = i := by simpa only [value, Option.some.injEq] using unique k
      simp [project, value, occursOpt, occurs, same]
  | and a b ha hb =>
    simp only [project, occursOpt_joinProjection, occurs, ha, hb]
  | or a b ha hb =>
    simp only [project, occursOpt_joinProjection, occurs, ha, hb]

lemma leavesOpt_eq_sum_occursOpt (a : Option (DMFormula 3)) :
    leavesOpt a = ∑ j, occursOpt a j := by
  cases a with
  | none => simp [leavesOpt, occursOpt]
  | some φ => simpa only [leavesOpt, occursOpt] using (sum_occurs φ).symm

lemma projected_leaves_eq_three_occurrences {n : Nat}
    (ρ : Fin n → Option (Fin 3)) (φ : DMFormula n) (a b c : Fin n)
    (ha : ∀ k, ρ k = some 0 ↔ k = a)
    (hb : ∀ k, ρ k = some 1 ↔ k = b)
    (hc : ∀ k, ρ k = some 2 ↔ k = c) :
    leavesOpt (project ρ φ) = occurs φ a + occurs φ b + occurs φ c := by
  rw [leavesOpt_eq_sum_occursOpt]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Nat.add_zero]
  change occursOpt (project ρ φ) 0 + (occursOpt (project ρ φ) 1 +
    occursOpt (project ρ φ) 2) = _
  rw [occurs_project_unique ρ φ a 0 ha, occurs_project_unique ρ φ b 1 hb,
    occurs_project_unique ρ φ c 2 hc]
  omega

end PEqualNP.Outside.L_meta_2592.FormulaPruning
