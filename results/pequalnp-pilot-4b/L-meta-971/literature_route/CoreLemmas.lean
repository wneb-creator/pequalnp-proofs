import Mathlib

namespace Meta971Research

/-- A safe OR branch can be moved to the final output.  A circuit-level
implementation must still account for rewiring and topological order. -/
theorem safe_or_extract (F : Bool → Bool) (a b : Bool)
    (hsafe : b = true → F (a || b) = true) :
    F (a || b) = (F a || b) := by
  cases b <;> simp_all

/-- Exactness forces every singleton support of a gate to be adjacent to
every singleton context in which that gate can reach the output. -/
theorem singleton_context_adj {α : Type*} (E : α → α → Prop)
    (hsymm : ∀ a b, E a b → E b a)
    (hloop : ∀ a, ¬ E a a) (h : Set α → Prop)
    (hmono : Monotone h) (a v : α) (ha : h {a})
    (hcontext : ∀ S : Set α, v ∈ S → h S →
      ∃ x ∈ S, ∃ y ∈ S, E x y) : E v a := by
  have hh : h ({a, v} : Set α) := hmono (by intro x hx; simp_all) ha
  obtain ⟨x, hx, y, hy, hxy⟩ := hcontext {a, v} (by simp) hh
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with hx | hx
  · subst x
    rcases hy with hy | hy
    · subst y
      exact (hloop a hxy).elim
    · subst y
      exact hsymm a v hxy
  · subst x
    rcases hy with hy | hy
    · subst y
      exact hxy
    · subst y
      exact (hloop v hxy).elim

/-- In a graph with no rectangular four-cycle, a gate with two distinct
singleton supports has at most one safe singleton context. -/
theorem singleton_context_unique {α : Type*} (E : α → α → Prop)
    (hsymm : ∀ a b, E a b → E b a)
    (hloop : ∀ a, ¬ E a a)
    (hc4 : ∀ u v a b, u ≠ v → a ≠ b →
      E u a → E u b → E v a → E v b → False)
    (h : Set α → Prop) (hmono : Monotone h)
    (a b u v : α) (hab : a ≠ b) (ha : h {a}) (hb : h {b})
    (hu : ∀ S : Set α, u ∈ S → h S → ∃ x ∈ S, ∃ y ∈ S, E x y)
    (hv : ∀ S : Set α, v ∈ S → h S → ∃ x ∈ S, ∃ y ∈ S, E x y) :
    u = v := by
  by_contra huv
  exact hc4 u v a b huv hab
    (singleton_context_adj E hsymm hloop h hmono a u ha hu)
    (singleton_context_adj E hsymm hloop h hmono b u hb hu)
    (singleton_context_adj E hsymm hloop h hmono a v ha hv)
    (singleton_context_adj E hsymm hloop h hmono b v hb hv)

end Meta971Research
