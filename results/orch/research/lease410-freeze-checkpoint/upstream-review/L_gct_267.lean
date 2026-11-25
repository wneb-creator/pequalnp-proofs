import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_267

open Polynomial

-- f = x^4 - 65 x^2 and g = c (x^4 - 65 x^2 + 848) with c = 1/50176. With t = x^4 - 65 x^2,
-- f g + 1 = c (t + 64) (t + 784) = c (x^2 - 1) (x^2 - 64) (x^2 - 16) (x^2 - 49),
-- which has the eight real roots 1, -1, 4, -4, 7, -7, 8, -8.

noncomputable def f : Polynomial ℝ := monomial 4 1 + monomial 2 (-65)

noncomputable def g : Polynomial ℝ :=
  monomial 4 (1 / 50176) + monomial 2 (-65 / 50176) + monomial 0 (848 / 50176)

lemma f_card : f.support.card ≤ 3 := by
  have h1 : f.support ⊆ ({4, 2} : Finset ℕ) := by
    intro n hn
    have h := support_add hn
    rw [Finset.mem_union] at h
    rcases h with h | h
    · rw [Finset.mem_singleton.mp (support_monomial_subset _ _ h)]; simp
    · rw [Finset.mem_singleton.mp (support_monomial_subset _ _ h)]; simp
  exact (Finset.card_le_card h1).trans (by decide)

lemma g_card : g.support.card ≤ 3 := by
  have h1 : g.support ⊆ ({4, 2, 0} : Finset ℕ) := by
    intro n hn
    have h := support_add hn
    rw [Finset.mem_union] at h
    rcases h with h | h
    · have h' := support_add h
      rw [Finset.mem_union] at h'
      rcases h' with h' | h'
      · rw [Finset.mem_singleton.mp (support_monomial_subset _ _ h')]; simp
      · rw [Finset.mem_singleton.mp (support_monomial_subset _ _ h')]; simp
    · rw [Finset.mem_singleton.mp (support_monomial_subset _ _ h)]; simp
  exact (Finset.card_le_card h1).trans (by decide)

lemma eval_p (x : ℝ) : eval x (f * g + 1) =
    (x ^ 4 - 65 * x ^ 2) * ((x ^ 4 - 65 * x ^ 2 + 848) / 50176) + 1 := by
  simp only [f, g, eval_add, eval_mul, eval_monomial, eval_one]
  ring

lemma p_ne : f * g + 1 ≠ 0 := by
  intro h
  have h2 := eval_p 0
  rw [h, eval_zero] at h2
  norm_num at h2

def S : Finset ℤ := {1, -1, 4, -4, 7, -7, 8, -8}

lemma sub_roots : S.map ⟨(Int.cast : ℤ → ℝ), Int.cast_injective⟩ ⊆ (f * g + 1).roots.toFinset := by
  intro x hx
  rw [Finset.mem_map] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  rw [Multiset.mem_toFinset, mem_roots p_ne, IsRoot, eval_p]
  simp only [S, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

end PEqualNP.Outside.L_gct_267

theorem PEqualNP.Outside.L_gct_267 : ¬ (∀ f g : Polynomial ℝ, (f.support.card ≤ 3 ∧ g.support.card ≤ 3) → ((f * g + 1).roots.toFinset).card ≤ 7) := by
  intro h
  have h7 := h PEqualNP.Outside.L_gct_267.f PEqualNP.Outside.L_gct_267.g
    ⟨PEqualNP.Outside.L_gct_267.f_card, PEqualNP.Outside.L_gct_267.g_card⟩
  have h8 := Finset.card_le_card PEqualNP.Outside.L_gct_267.sub_roots
  rw [Finset.card_map] at h8
  have hS : PEqualNP.Outside.L_gct_267.S.card = 8 := by decide
  omega
