import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1772_aux.literalCover

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

lemma disjoint_pair_clause {n : ℕ} {a b c d u v : Fin n}
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hp : (pairInput a b u || pairInput a b v) = true)
    (hq : (pairInput c d u || pairInput c d v) = true) :
    ((u = a ∨ u = b) ∧ (v = c ∨ v = d)) ∨
      ((v = a ∨ v = b) ∧ (u = c ∨ u = d)) := by
  simp only [Bool.or_eq_true, pairInput, decide_eq_true_eq] at hp hq
  rcases hp with (hp | hp) | (hp | hp) <;>
    rcases hq with (hq | hq) | (hq | hq) <;> aesop

lemma intersecting_pair_clause {n : ℕ} {z a b u v : Fin n}
    (hab : a ≠ b)
    (hp : (pairInput z a u || pairInput z a v) = true)
    (hq : (pairInput z b u || pairInput z b v) = true) :
    u = z ∨ v = z ∨ (u = a ∧ v = b) ∨ (u = b ∧ v = a) := by
  simp only [Bool.or_eq_true, pairInput, decide_eq_true_eq] at hp hq
  rcases hp with (hp | hp) | (hp | hp) <;>
    rcases hq with (hq | hq) | (hq | hq) <;> aesop

lemma shared_covers_force_base_clause {n m : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (clauses : Fin m → Fin n × Fin n)
    {z a b : Fin n} (hab : a ≠ b)
    (hp : ∀ i, (pairInput z a (clauses i).1 || pairInput z a (clauses i).2) = true)
    (hq : ∀ i, (pairInput z b (clauses i).1 || pairInput z b (clauses i).2) = true)
    (safe : ∀ x : Fin n → Bool,
      (∀ i, (x (clauses i).1 || x (clauses i).2) = true) → graphFun G ∅ x = true) :
    (∀ i, (clauses i).1 = z ∨ (clauses i).2 = z ∨
      ((clauses i).1 = a ∧ (clauses i).2 = b) ∨
      ((clauses i).1 = b ∧ (clauses i).2 = a)) ∧
    (∃ i, ((clauses i).1 = a ∧ (clauses i).2 = b) ∨
      ((clauses i).1 = b ∧ (clauses i).2 = a)) := by
  have shape : ∀ i, (clauses i).1 = z ∨ (clauses i).2 = z ∨
      ((clauses i).1 = a ∧ (clauses i).2 = b) ∨
      ((clauses i).1 = b ∧ (clauses i).2 = a) :=
    fun i => intersecting_pair_clause hab (hp i) (hq i)
  refine ⟨shape, ?_⟩
  by_contra h
  have hF := safe (pairInput z z) (by
    intro i
    rcases shape i with hi | hi | hi | hi
    · simp [pairInput, hi]
    · simp [pairInput, hi]
    · exact (h ⟨i, Or.inl hi⟩).elim
    · exact (h ⟨i, Or.inr hi⟩).elim)
  simpa [graphFun, pairInput] using hF

end PEqualNP.Outside.L_meta_1772_aux.literalCover
