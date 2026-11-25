import PEqualNP.Defs
import Mathlib.Tactic

namespace PEqualNP.Outside.L_meta_1904

open PEqualNP.EdgeOwnership

lemma graph_hit_pair {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n)
    (h : ∃ a b : Fin n, G.Adj a b ∧
      pairInput u v a = true ∧ pairInput u v b = true) : G.Adj u v := by
  obtain ⟨a, b, hab, ha, hb⟩ := h
  simp only [pairInput, decide_eq_true_eq] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · simp at hab
  · exact hab
  · exact hab.symm
  · simp at hab

lemma singleton_pair_le {n : ℕ} (u v w : Fin n) (hw : w = u ∨ w = v) :
    pairInput w w ≤ pairInput u v := by
  intro i
  by_cases hi : i = w
  · subst i
    simp [pairInput, hw]
  · simp [pairInput, hi]

lemma monotone_singleton_pair {n : ℕ} (F : (Fin n → Bool) → Bool)
    (hF : Monotone F) (u v w : Fin n) (hw : w = u ∨ w = v)
    (h : F (pairInput w w) = true) : F (pairInput u v) = true := by
  have hle := hF (singleton_pair_le u v w hw)
  by_contra hnot
  have hfalse : F (pairInput u v) = false := by simpa using hnot
  rw [h, hfalse] at hle
  exact (show ¬ ((true : Bool) ≤ false) by decide) hle

lemma singleton_overlap_orientation {n : ℕ} (G : SimpleGraph (Fin n))
    (htri : ∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (A B T : (Fin n → Bool) → Bool)
    (hA : Monotone A) (hB : Monotone B) (hT : Monotone T)
    (hbelow : ∀ x : Fin n → Bool, A x = true → B x = true → T x = true →
      ∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true)
    (a : Fin n) (haA : A (pairInput a a) = true)
    (haB : B (pairInput a a) = true) :
    (∀ b : Fin n, A (pairInput b b) = true → T (pairInput b b) = false) ∨
      (∀ c : Fin n, B (pairInput c c) = true → T (pairInput c c) = false) := by
  by_cases hleft : ∀ b : Fin n,
      A (pairInput b b) = true → T (pairInput b b) = false
  · exact Or.inl hleft
  · push Not at hleft
    obtain ⟨b, hbA, hbT⟩ := hleft
    have hbT' : T (pairInput b b) = true := by simpa using hbT
    refine Or.inr ?_
    intro c hcB
    by_contra hcT
    have hcT' : T (pairInput c c) = true := by simpa using hcT
    have hab : G.Adj a b := graph_hit_pair G a b (hbelow _
      (monotone_singleton_pair A hA a b a (Or.inl rfl) haA)
      (monotone_singleton_pair B hB a b a (Or.inl rfl) haB)
      (monotone_singleton_pair T hT a b b (Or.inr rfl) hbT'))
    have hac : G.Adj a c := graph_hit_pair G a c (hbelow _
      (monotone_singleton_pair A hA a c a (Or.inl rfl) haA)
      (monotone_singleton_pair B hB a c a (Or.inl rfl) haB)
      (monotone_singleton_pair T hT a c c (Or.inr rfl) hcT'))
    have hbc : G.Adj b c := graph_hit_pair G b c (hbelow _
      (monotone_singleton_pair A hA b c b (Or.inl rfl) hbA)
      (monotone_singleton_pair B hB b c c (Or.inr rfl) hcB)
      (monotone_singleton_pair T hT b c b (Or.inl rfl) hbT'))
    exact htri a b c hab hbc hac.symm

end PEqualNP.Outside.L_meta_1904
