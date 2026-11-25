import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583_aux.FourClause

def inputUnion {n : ℕ} (x y : Fin n → Bool) : Fin n → Bool :=
  fun j => x j || y j

lemma obstruction_bound {n k m : ℕ}
    (clauses : Fin k → (Fin n → Bool) → Bool)
    (preserves : ∀ i x y,
      clauses i (inputUnion x y) = (clauses i x || clauses i y))
    (witness : Fin m → Fin n → Bool)
    (rejects : ∀ j, ∃ i, clauses i (witness j) = false)
    (accepts : ∀ j l, j ≠ l → ∀ i,
      clauses i (inputUnion (witness j) (witness l)) = true) :
    m ≤ k := by
  classical
  choose rejecting rejecting_spec using rejects
  have inj : Function.Injective rejecting := by
    intro j l eq
    by_contra ne
    have h := accepts j l ne (rejecting j)
    rw [preserves, rejecting_spec, eq, rejecting_spec] at h
    cases h
  have bound := Fintype.card_le_of_injective rejecting inj
  simpa using bound

def pathSix (x : Fin 6 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
    (x 3 && x 4) || (x 4 && x 5)

def cycleSix (x : Fin 6 → Bool) : Bool :=
  pathSix x || (x 5 && x 0)

def pathWitness (i : Fin 5) (j : Fin 6) : Bool :=
  decide (j.val ∈ match i.val with
    | 0 => [0, 2, 4]
    | 1 => [0, 2, 5]
    | 2 => [0, 3, 5]
    | 3 => [1, 3, 5]
    | _ => [1, 4])

def cycleWitness (i : Fin 5) (j : Fin 6) : Bool :=
  decide (j.val ∈ match i.val with
    | 0 => [0, 2, 4]
    | 1 => [1, 3, 5]
    | 2 => [0, 3]
    | 3 => [1, 4]
    | _ => [2, 5])

lemma path_witness_rejected : ∀ i, pathSix (pathWitness i) = false := by decide

lemma path_witness_unions : ∀ i j, i ≠ j →
    pathSix (inputUnion (pathWitness i) (pathWitness j)) = true := by decide

lemma cycle_witness_rejected : ∀ i, cycleSix (cycleWitness i) = false := by decide

lemma cycle_witness_unions : ∀ i j, i ≠ j →
    cycleSix (inputUnion (cycleWitness i) (cycleWitness j)) = true := by decide

lemma cnf_obstruction_bound {n k m : ℕ}
    (f : (Fin n → Bool) → Bool)
    (clauses : Fin k → (Fin n → Bool) → Bool)
    (preserves : ∀ i x y,
      clauses i (inputUnion x y) = (clauses i x || clauses i y))
    (represents : ∀ x, f x = true ↔ ∀ i, clauses i x = true)
    (witness : Fin m → Fin n → Bool)
    (rejects : ∀ j, f (witness j) = false)
    (accepts : ∀ j l, j ≠ l →
      f (inputUnion (witness j) (witness l)) = true) : m ≤ k := by
  classical
  apply obstruction_bound clauses preserves witness
  · intro j
    by_contra no
    have all : ∀ i, clauses i (witness j) = true := by
      intro i
      cases h : clauses i (witness j)
      · exact False.elim (no ⟨i, h⟩)
      · rfl
    have h := (represents (witness j)).mpr all
    rw [rejects] at h
    cases h
  · intro j l ne i
    exact (represents _).mp (accepts j l ne) i

lemma path_six_needs_five_clauses {k : ℕ}
    (clauses : Fin k → (Fin 6 → Bool) → Bool)
    (preserves : ∀ i x y,
      clauses i (inputUnion x y) = (clauses i x || clauses i y))
    (represents : ∀ x, pathSix x = true ↔ ∀ i, clauses i x = true) :
    5 ≤ k :=
  cnf_obstruction_bound pathSix clauses preserves represents pathWitness
    path_witness_rejected path_witness_unions

lemma cycle_six_needs_five_clauses {k : ℕ}
    (clauses : Fin k → (Fin 6 → Bool) → Bool)
    (preserves : ∀ i x y,
      clauses i (inputUnion x y) = (clauses i x || clauses i y))
    (represents : ∀ x, cycleSix x = true ↔ ∀ i, clauses i x = true) :
    5 ≤ k :=
  cnf_obstruction_bound cycleSix clauses preserves represents cycleWitness
    cycle_witness_rejected cycle_witness_unions


end PEqualNP.Outside.L_meta_2583_aux.FourClause
