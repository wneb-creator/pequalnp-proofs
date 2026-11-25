
namespace PEqualNP.Outside.L_meta_2583_aux.Fano

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

def dot (a b : ℕ) : ℕ :=
  (a % 2) * (b % 2) + (a / 2 % 2) * (b / 2 % 2) + (a / 4 % 2) * (b / 4 % 2)

abbrev incidence (p l : Fin 7) : Prop := dot (p.val + 1) (l.val + 1) % 2 = 0

/-- This finite relation matches the nonzero three-bit vectors used by the search. -/
theorem incidence_rows : ∀ p l : Fin 7, incidence p l ↔
    p ∈ (![({1, 3, 5} : Finset (Fin 7)), {0, 3, 4}, {2, 3, 6},
      {0, 1, 2}, {1, 4, 6}, {0, 5, 6}, {2, 4, 5}] l) := by decide

theorem three_points : ∀ l : Fin 7,
    (Finset.univ.filter (fun p => incidence p l)).card = 2 + 1 := by decide

theorem unique_line : ∀ p p' : Fin 7, p ≠ p' →
    ∃! l : Fin 7, incidence p l ∧ incidence p' l := by
  simp only [ExistsUnique]
  decide

def function (z : Fin 14 → Bool) : Bool :=
  decide (∃ p l : Fin 7, incidence p l ∧ z (Fin.castAdd 7 p) = true ∧
    z (Fin.natAdd 7 l) = true)

theorem read_one_size (C : Circuit) (hao : PEqualNP.TopForm.IsAO2 14 C)
    (computes : ∀ z : Fin 14 → Bool, circuitFun 14 C z = function z)
    (readone : IsReadK 14 C 1) : 27 ≤ C.size := by
  have bound := PEqualNP.Outside.L_meta_2583.PlaneCount.read_one_lower
    2 7 incidence C (by decide) (by decide) three_points unique_line hao computes readone
  omega

/-- This is a conditional refutation interface. It does not assert that a
  circuit satisfying its three hypotheses exists. -/
theorem refutes_posted_of_twenty_six
    (C : Circuit) (hao : PEqualNP.TopForm.IsAO2 14 C)
    (computes : ∀ z : Fin 14 → Bool, circuitFun 14 C z = function z)
    (small : C.size ≤ 26) :
    ¬ (∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (C : Circuit), 2 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      PEqualNP.TopForm.IsAO2 (N + N) C →
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
        decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
          z (Fin.natAdd N l) = true)) →
      ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (N + N) D ∧
        (∀ y : Fin (N + N) → Bool, circuitFun (N + N) D y =
          decide (∃ p l : Fin N, I p l ∧ y (Fin.castAdd N p) = true ∧
            y (Fin.natAdd N l) = true)) ∧ D.size ≤ C.size ∧ IsReadK (N + N) D 1) := by
  intro posted
  obtain ⟨D, dao, dcomputes, dsize, dreadone⟩ :=
    posted 2 7 incidence C (by decide) (by decide) three_points unique_line hao computes
  have lower := read_one_size D dao dcomputes dreadone
  omega

end PEqualNP.Outside.L_meta_2583_aux.Fano
