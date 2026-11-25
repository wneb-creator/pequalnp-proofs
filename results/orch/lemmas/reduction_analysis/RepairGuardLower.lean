import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.PermInputs

/- Research-only support bound for a possible final-AND repair guard.
This is not a lower bound for the full target circuit and does not forbid
sharing gates with an existing circuit. -/
namespace PEqualNP.Outside.L_meta_650_aux.RepairGuard

open PEqualNP.MetaComplexity

def desiredEdges : List (ℕ × ℕ) :=
  [(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)]

def pairInput (a b : Fin 26) (i : Fin 26) : Bool := decide (i = a ∨ i = b)

def essential : Finset (Fin 26) := {1, 2, 6, 7, 9, 11, 12, 13, 14, 15, 20, 21, 24, 25}

def firstCase (i : Fin 26) : Bool :=
  decide (i.val ∈ ([2, 6, 7, 9, 13, 15, 21, 25] : List ℕ))

def badInput (i : Fin 26) : Fin 26 → Bool :=
  if firstCase i then pairInput 1 20 else pairInput 2 15

def edgeFor (i : Fin 26) : Fin 26 × Fin 26 :=
  if i.val < 13 then (i, if firstCase i then 20 else 15)
  else (if firstCase i then 1 else 2, i)

lemma witnesses : ∀ i ∈ essential,
    ((edgeFor i).1.val, (edgeFor i).2.val) ∈ desiredEdges ∧
      ∀ j : Fin 26, pairInput (edgeFor i).1 (edgeFor i).2 j = true →
        Function.update (badInput i) i (!(badInput i i)) j = true := by
  decide +kernel

lemma essential_card : essential.card = 14 := by decide

theorem guard_lower (f : (Fin 26 → Bool) → Bool) (s : ℕ)
    (mono : ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true)
    (positive : ∀ a b : Fin 26, (a.val, b.val) ∈ desiredEdges → f (pairInput a b) = true)
    (bad1 : f (pairInput 1 20) = false) (bad2 : f (pairInput 2 15) = false)
    (size : HasCircuitSize 26 f s) : 13 ≤ s := by
  have dep : ∀ i ∈ essential, ∃ x : Fin 26 → Bool,
      f (Function.update x i (!(x i))) ≠ f x := by
    intro i hi
    refine ⟨badInput i, ?_⟩
    have neg : f (badInput i) = false := by
      unfold badInput
      split <;> assumption
    have pos : f (Function.update (badInput i) i (!(badInput i i))) = true :=
      mono _ _ (witnesses i hi).2
        (positive (edgeFor i).1 (edgeFor i).2 (witnesses i hi).1)
    rw [pos, neg]
    decide
  have bound := Helpers.PermInputs.dep_lower_set 26 f essential dep s size
  rw [essential_card] at bound
  omega

end PEqualNP.Outside.L_meta_650_aux.RepairGuard
