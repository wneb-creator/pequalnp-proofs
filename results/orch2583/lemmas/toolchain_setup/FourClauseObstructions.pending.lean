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

lemma bool_eq_of_true_iff {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

def orClause {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ i ∈ S, x i = true)

lemma or_clause_preserves {n : ℕ} (S : Finset (Fin n)) (x y : Fin n → Bool) :
    orClause S (inputUnion x y) = (orClause S x || orClause S y) := by
  apply bool_eq_of_true_iff
  simp only [orClause, inputUnion, decide_eq_true_eq, Bool.or_eq_true]
  aesop

def liftInput {m n : ℕ} (e : Fin m → Fin n) (x : Fin m → Bool) : Fin n → Bool :=
  fun v => decide (∃ i, e i = v ∧ x i = true)

lemma lift_input_preserves {m n : ℕ} (e : Fin m → Fin n) (x y : Fin m → Bool) :
    liftInput e (inputUnion x y) = inputUnion (liftInput e x) (liftInput e y) := by
  funext v
  apply bool_eq_of_true_iff
  simp only [liftInput, inputUnion, decide_eq_true_eq, Bool.or_eq_true]
  aesop

lemma graph_lift_true {m n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (e : Fin m → Fin n) (x : Fin m → Bool) :
    PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ (liftInput e x) = true ↔
      ∃ i j, G.Adj (e i) (e j) ∧ x i = true ∧ x j = true := by
  simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, Finset.not_mem_empty,
    false_and, exists_false, decide_false, Bool.false_or, decide_eq_true_eq,
    liftInput]
  constructor
  · rintro ⟨u, v, uv, ⟨i, hi, xi⟩, ⟨j, hj, xj⟩⟩
    exact ⟨i, j, hi ▸ hj ▸ uv, xi, xj⟩
  · rintro ⟨i, j, hij, xi, xj⟩
    exact ⟨e i, e j, hij, ⟨i, rfl, xi⟩, ⟨j, rfl, xj⟩⟩

lemma path_six_true : ∀ x : Fin 6 → Bool, pathSix x = true ↔
    ∃ i j : Fin 6, (i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧
      x i = true ∧ x j = true := by decide

lemma cycle_six_true : ∀ x : Fin 6 → Bool, cycleSix x = true ↔
    ∃ i j : Fin 6,
      (i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
        (i.val = 0 ∧ j.val = 5) ∨ (i.val = 5 ∧ j.val = 0)) ∧
      x i = true ∧ x j = true := by decide

lemma induced_path_six_needs_five_clauses {n k : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (e : Fin 6 → Fin n)
    (induced : ∀ i j, G.Adj (e i) (e j) ↔
      i.val + 1 = j.val ∨ j.val + 1 = i.val)
    (clauses : Fin k → (Fin n → Bool) → Bool)
    (preserves : ∀ i x y,
      clauses i (inputUnion x y) = (clauses i x || clauses i y))
    (represents : ∀ x,
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true ↔
        ∀ i, clauses i x = true) : 5 ≤ k := by
  apply path_six_needs_five_clauses (fun i x => clauses i (liftInput e x))
  · intro i x y
    rw [lift_input_preserves, preserves]
  · intro x
    rw [← represents, graph_lift_true]
    simp_rw [induced]
    exact path_six_true x

lemma induced_cycle_six_needs_five_clauses {n k : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (e : Fin 6 → Fin n)
    (induced : ∀ i j, G.Adj (e i) (e j) ↔
      (i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
        (i.val = 0 ∧ j.val = 5) ∨ (i.val = 5 ∧ j.val = 0)))
    (clauses : Fin k → (Fin n → Bool) → Bool)
    (preserves : ∀ i x y,
      clauses i (inputUnion x y) = (clauses i x || clauses i y))
    (represents : ∀ x,
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true ↔
        ∀ i, clauses i x = true) : 5 ≤ k := by
  apply cycle_six_needs_five_clauses (fun i x => clauses i (liftInput e x))
  · intro i x y
    rw [lift_input_preserves, preserves]
  · intro x
    rw [← represents, graph_lift_true]
    simp_rw [induced]
    exact cycle_six_true x

end PEqualNP.Outside.L_meta_2583_aux.FourClause
