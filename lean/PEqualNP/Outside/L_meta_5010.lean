import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5010

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def fn (x : Fin 9 → Bool) : Bool := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)].any fun (e : Fin 9 × Fin 9) => x e.1 && x e.2

def W (t : Fin 11) (x : Fin 9 → Bool) : List Bool :=
  List.ofFn x ++ [x 0 || x 2] ++ [!(List.ofFn x ++ [x 0 || x 2]).getD t.val false]

def xx (k : ℕ) : Fin 9 → Bool := fun i => k.testBit i.val

def A : List ℕ := [0, 1, 2, 4, 8, 16, 32, 64, 128, 256]

def B : List ℕ := [3, 6, 12, 24, 17, 33, 66, 132, 264, 160, 320, 288]

theorem key : ∀ t ∈ [(0 : Fin 11), 3, 4], ∀ i j : Fin 12, ∃ a ∈ A, ∃ b ∈ B,
    (W t (xx a)).getD i.val false = (W t (xx b)).getD i.val false ∧
    (W t (xx a)).getD j.val false = (W t (xx b)).getD j.val false ∧ fn (xx a) ≠ fn (xx b) := by
  decide +kernel

theorem dep (C : Circuit) (hC : FanInTwo C) (h : ¬ ∃ g, C.gates[1]? = some g) :
    ∃ i j : ℕ, ∀ u v : List Bool, u.length = 11 → v.length = 11 →
      u.getD i false = v.getD i false → u.getD j false = v.getD j false → C.eval u = C.eval v := by
  obtain ⟨gs, o⟩ := C
  match gs, h with
  | [], _ => exact ⟨o, o, fun u v _ _ h _ => h⟩
  | [g], _ =>
    have hlen : g.inputs.length ≤ 2 := (hC g (by simp)).2
    by_cases ho : o = 11
    · obtain ⟨i, j, hij⟩ : ∃ i j, ∀ k ∈ g.inputs, k = i ∨ k = j := by
        match g.inputs, hlen with
        | [], _ => exact ⟨0, 0, by simp⟩
        | [a], _ => exact ⟨a, a, by simp⟩
        | [a, b], _ => exact ⟨a, b, by simp⟩
      refine ⟨i, j, fun u v hu hv h1 h2 => ?_⟩
      have e : g.op.eval (g.inputs.map fun k => u.getD k false) =
          g.op.eval (g.inputs.map fun k => v.getD k false) := by
        rw [List.map_congr_left fun k hk => ?_]
        rcases hij k hk with rfl | rfl
        · exact h1
        · exact h2
      change (u ++ [g.op.eval (g.inputs.map fun k => u.getD k false)]).getD o false =
        (v ++ [g.op.eval (g.inputs.map fun k => v.getD k false)]).getD o false
      rw [e, ho, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by omega), List.getElem?_append_right (by omega), hu, hv]
    · refine ⟨o, o, fun u v hu hv h1 _ => ?_⟩
      change (u ++ [g.op.eval (g.inputs.map fun k => u.getD k false)]).getD o false =
        (v ++ [g.op.eval (g.inputs.map fun k => v.getD k false)]).getD o false
      rcases Nat.lt_or_ge o 11 with h | h
      · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_left (by omega), List.getElem?_append_left (by omega),
          ← List.getD_eq_getElem?_getD, ← List.getD_eq_getElem?_getD]
        exact h1
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  | g :: g' :: l, h => exact absurd ⟨g', by simp⟩ h

end PEqualNP.Outside.L_meta_5010

open PEqualNP.Outside.L_meta_5010 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_5010 : ∀ (x1 : Fin (11 : ℕ)),   x1 = (0 : Fin (11 : ℕ)) ∨ x1 = (3 : Fin (11 : ℕ)) ∨ x1 = (4 : Fin (11 : ℕ)) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           (¬∃ (x6 : PEqualNP.CircuitLowerBounds.Gate), x3.gates[(1 : ℕ)]? = Option.some x6) →             ∃ (x7 : Fin (9 : ℕ) → Bool),               have x8 : List Bool := List.ofFn x7 ++ [x7 (0 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ))];               x3.eval (x8 ++ [!x8.getD (↑x1) Bool.false]) ≠ [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x9 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x7 x9.1 && x7 x9.2 := by
  intro t ht C hC _ hg
  by_contra hcon
  have hC' : ∀ x, C.eval (W t x) = fn x := fun x => by
    by_contra hx
    exact hcon ⟨x, hx⟩
  obtain ⟨i, j, hd⟩ := dep C hC hg
  have hlen : ∀ x, (W t x).length = 11 := fun x => by simp [W]
  have hmin : ∀ (k : ℕ) (x : Fin 9 → Bool), (W t x).getD (Min.min k 11) false = (W t x).getD k false := by
    intro k x
    rcases Nat.lt_or_ge k 11 with h | h
    · rw [Nat.min_eq_left h.le]
    · rw [Nat.min_eq_right h, List.getD_eq_default _ _ (by rw [hlen]),
        List.getD_eq_default _ _ (by rw [hlen]; exact h)]
  obtain ⟨a, _, b, _, h1, h2, h3⟩ := key t (by simpa using ht) ⟨Min.min i 11, by omega⟩ ⟨Min.min j 11, by omega⟩
  simp only [hmin] at h1 h2
  apply h3
  rw [← hC', ← hC']
  exact hd _ _ (hlen _) (hlen _) h1 h2
