import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2590_aux.PetersenBoundary

def edgeFunction (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def maskInput (r : Nat) (i : Fin 10) : Bool := r.testBit i.val

def maximalFalseMasks : List Nat :=
  [50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773]

def support (r : Nat) : Finset (Fin 10) :=
  Finset.univ.filter (fun i => maskInput r i = true)

theorem maximalFalseMasks_length : maximalFalseMasks.length = 15 := rfl

theorem maximalFalseMasks_nodup : maximalFalseMasks.Nodup := by decide +kernel

theorem listed_masks_false :
    ∀ r ∈ maximalFalseMasks, edgeFunction (maskInput r) = false := by
  decide +kernel

theorem listed_masks_maximal :
    ∀ r ∈ maximalFalseMasks, ∀ i : Fin 10, maskInput r i = false →
      edgeFunction (fun j => if j = i then true else maskInput r j) = true := by
  decide +kernel

theorem distinct_listed_union_true :
    ∀ r ∈ maximalFalseMasks, ∀ s ∈ maximalFalseMasks, r ≠ s →
      edgeFunction (fun i => maskInput r i || maskInput s i) = true := by
  decide +kernel

theorem listed_masks_sizes :
    ∀ r ∈ maximalFalseMasks, (support r).card = 3 ∨ (support r).card = 4 := by
  decide +kernel

theorem three_vertex_mask_count :
    (maximalFalseMasks.filter (fun r => decide ((support r).card = 3))).length = 10 := by
  decide +kernel

theorem four_vertex_mask_count :
    (maximalFalseMasks.filter (fun r => decide ((support r).card = 4))).length = 5 := by
  decide +kernel

theorem complement_sizes :
    ∀ r ∈ maximalFalseMasks, (support r)ᶜ.card = 6 ∨ (support r)ᶜ.card = 7 := by
  decide +kernel

theorem seven_vertex_complement :
    50 ∈ maximalFalseMasks ∧ (support 50)ᶜ.card = 7 := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem false_boundary_complete :
    ∀ x : Fin 10 → Bool, edgeFunction x = false →
      ∃ r ∈ maximalFalseMasks, ∀ i : Fin 10, x i = true → maskInput r i = true := by
  decide +kernel

end PEqualNP.Outside.L_meta_2590_aux.PetersenBoundary

namespace PEqualNP.Outside.L_meta_2590_aux.PetersenCNF

open PEqualNP.Outside.L_meta_2590_aux.PetersenBoundary

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


def witness (i : Fin 15) : Fin 10 → Bool := maskInput (maximalFalseMasks.get i)

lemma witness_false : ∀ i, edgeFunction (witness i) = false := by decide +kernel

lemma witness_union : ∀ i j, i ≠ j → edgeFunction (inputUnion (witness i) (witness j)) = true := by
  decide +kernel

def clause (S : Finset (Fin 10)) (x : Fin 10 → Bool) : Bool :=
  decide (∃ v ∈ S, x v = true)

lemma clause_union (S : Finset (Fin 10)) (x y : Fin 10 → Bool) :
    clause S (inputUnion x y) = (clause S x || clause S y) := by
  simp [clause, inputUnion, Bool.or_eq_true, and_or_left, exists_or]

lemma rejects_clause {k : ℕ} (sets : Fin k → Finset (Fin 10))
    (computes : ∀ x, (∀ j, clause (sets j) x = true) ↔ edgeFunction x = true)
    (x : Fin 10 → Bool) (hx : edgeFunction x = false) :
    ∃ j, clause (sets j) x = false := by
  by_contra! h
  have hc : ∀ j, clause (sets j) x = true := by
    intro j
    cases hj : clause (sets j) x <;> simp_all
  have hf := (computes x).1 hc
  simp [hx] at hf

lemma clauses_at_least_fifteen {k : ℕ} (sets : Fin k → Finset (Fin 10))
    (computes : ∀ x, (∀ j, clause (sets j) x = true) ↔ edgeFunction x = true) :
    15 ≤ k := by
  apply obstruction_bound (fun j => clause (sets j))
    (fun i x y => clause_union (sets i) x y) witness
  · intro j
    exact rejects_clause sets computes (witness j) (witness_false j)
  · intro j l hne i
    exact (computes _).2 (witness_union j l hne) i

lemma large_clause {k : ℕ} (sets : Fin k → Finset (Fin 10))
    (computes : ∀ x, (∀ j, clause (sets j) x = true) ↔ edgeFunction x = true) :
    ∃ j, 7 ≤ (sets j).card := by
  have hm : 50 ∈ maximalFalseMasks := by decide
  obtain ⟨j, hj⟩ := rejects_clause sets computes _ (listed_masks_false 50 hm)
  have sub : (support 50)ᶜ ⊆ sets j := by
    intro v hv
    have hvf : maskInput 50 v = false := by
      simpa [support] using hv
    have he := listed_masks_maximal 50 hm v hvf
    have hc := (computes _).2 he j
    simp only [clause, decide_eq_true_eq] at hc
    obtain ⟨u, hu, hval⟩ := hc
    by_cases huv : u = v
    · simpa [huv] using hu
    · have hum : maskInput 50 u = true := by simpa [huv] using hval
      have ht : clause (sets j) (maskInput 50) = true := by
        simp only [clause, decide_eq_true_eq]
        exact ⟨u, hu, hum⟩
      simp [hj] at ht
  have hh := Finset.card_le_card sub
  rw [seven_vertex_complement.2] at hh
  exact ⟨j, hh⟩

end PEqualNP.Outside.L_meta_2590_aux.PetersenCNF
