import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2602_aux

open PEqualNP.CircuitLowerBounds

def upper65Circuit : Circuit :=
  ⟨[
    ⟨.or, [0, 1]⟩,
    ⟨.or, [26, 3]⟩,
    ⟨.or, [27, 9]⟩,
    ⟨.and, [13, 28]⟩,
    ⟨.or, [2, 3]⟩,
    ⟨.or, [30, 5]⟩,
    ⟨.or, [31, 11]⟩,
    ⟨.and, [15, 32]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.or, [34, 6]⟩,
    ⟨.or, [35, 12]⟩,
    ⟨.and, [16, 36]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.or, [38, 7]⟩,
    ⟨.or, [39, 0]⟩,
    ⟨.and, [17, 40]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.or, [42, 8]⟩,
    ⟨.or, [43, 1]⟩,
    ⟨.and, [18, 44]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.or, [46, 9]⟩,
    ⟨.or, [47, 2]⟩,
    ⟨.and, [19, 48]⟩,
    ⟨.or, [7, 8]⟩,
    ⟨.or, [50, 10]⟩,
    ⟨.or, [51, 3]⟩,
    ⟨.and, [20, 52]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.or, [54, 11]⟩,
    ⟨.or, [55, 4]⟩,
    ⟨.and, [21, 56]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.or, [58, 12]⟩,
    ⟨.or, [59, 5]⟩,
    ⟨.and, [22, 60]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.or, [62, 0]⟩,
    ⟨.or, [63, 6]⟩,
    ⟨.and, [23, 64]⟩,
    ⟨.or, [11, 12]⟩,
    ⟨.or, [66, 1]⟩,
    ⟨.or, [67, 7]⟩,
    ⟨.and, [24, 68]⟩,
    ⟨.or, [12, 0]⟩,
    ⟨.or, [70, 2]⟩,
    ⟨.or, [71, 8]⟩,
    ⟨.and, [25, 72]⟩,
    ⟨.or, [29, 33]⟩,
    ⟨.or, [74, 37]⟩,
    ⟨.or, [75, 41]⟩,
    ⟨.or, [76, 45]⟩,
    ⟨.or, [77, 49]⟩,
    ⟨.or, [78, 53]⟩,
    ⟨.or, [79, 57]⟩,
    ⟨.or, [80, 61]⟩,
    ⟨.or, [81, 65]⟩,
    ⟨.or, [82, 69]⟩,
    ⟨.or, [83, 73]⟩,
    ⟨.or, [84, 1]⟩,
    ⟨.or, [85, 2]⟩,
    ⟨.or, [86, 4]⟩,
    ⟨.or, [87, 10]⟩,
    ⟨.or, [84, 14]⟩,
    ⟨.and, [88, 89]⟩], 90⟩

def upper65Star (x : Fin 26 → Bool) (l : Fin 13) : Bool :=
  x (Fin.natAdd 13 l) &&
    (x (Fin.castAdd 13 l) || x (Fin.castAdd 13 (l + 1)) ||
      x (Fin.castAdd 13 (l + 3)) || x (Fin.castAdd 13 (l + 9)))

def upper65Rest (x : Fin 26 → Bool) : Bool :=
  upper65Star x 0 || upper65Star x 2 || upper65Star x 3 || upper65Star x 4 || upper65Star x 5 || upper65Star x 6 || upper65Star x 7 || upper65Star x 8 || upper65Star x 9 || upper65Star x 10 || upper65Star x 11 || upper65Star x 12

def upper65B (x : Fin 26 → Bool) : Bool := x 1 || x 2 || x 4 || x 10

lemma upper65_size : upper65Circuit.size = 65 := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
lemma upper65_eval (x : Fin 26 → Bool) :
    upper65Circuit.eval (List.ofFn x) =
      ((upper65Rest x || upper65B x) && (upper65Rest x || x 14)) := by
  simp [upper65Circuit, Circuit.eval, Circuit.wires, GateOp.eval,
    List.ofFn_succ, List.ofFn_zero, upper65Rest, upper65Star, upper65B, Bool.or_assoc]

lemma upper65_absorb (r b y : Bool) :
    ((r || b) && (r || y)) = (r || (y && b)) := by
  cases r <;> cases b <;> cases y <;> rfl

def upper65Lines : List (Fin 13) := [0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 1]

lemma upper65_lines_mem (l : Fin 13) : l ∈ upper65Lines := by
  fin_cases l <;> simp [upper65Lines]

lemma upper65_eval_stars (x : Fin 26 → Bool) :
    upper65Circuit.eval (List.ofFn x) = upper65Lines.any (upper65Star x) := by
  rw [upper65_eval, upper65_absorb]
  simp [upper65Lines, upper65Rest, upper65Star, upper65B, Bool.or_assoc]

lemma upper65_star_true (x : Fin 26 → Bool) (l : Fin 13) :
    upper65Star x l = true ↔ ∃ p : Fin 13,
      (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
      x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true := by
  simp only [upper65Star, Bool.and_eq_true, Bool.or_eq_true, or_assoc]
  constructor
  · rintro ⟨hl, h | h | h | h⟩
    · exact ⟨l, Or.inl rfl, h, hl⟩
    · exact ⟨l + 1, Or.inr (Or.inl rfl), h, hl⟩
    · exact ⟨l + 3, Or.inr (Or.inr (Or.inl rfl)), h, hl⟩
    · exact ⟨l + 9, Or.inr (Or.inr (Or.inr rfl)), h, hl⟩
  · rintro ⟨p, h | h | h | h, hp, hl⟩
    · exact ⟨hl, Or.inl (h ▸ hp)⟩
    · exact ⟨hl, Or.inr (Or.inl (h ▸ hp))⟩
    · exact ⟨hl, Or.inr (Or.inr (Or.inl (h ▸ hp)))⟩
    · exact ⟨hl, Or.inr (Or.inr (Or.inr (h ▸ hp)))⟩

lemma upper65_semantics (x : Fin 26 → Bool) :
    upper65Circuit.eval (List.ofFn x) = true ↔ ∃ p l : Fin 13,
      (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
      x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true := by
  rw [upper65_eval_stars, List.any_eq_true]
  constructor
  · rintro ⟨l, _, hl⟩
    obtain ⟨p, hp⟩ := (upper65_star_true x l).mp hl
    exact ⟨p, l, hp⟩
  · rintro ⟨p, l, hp⟩
    exact ⟨l, upper65_lines_mem l, (upper65_star_true x l).mpr ⟨p, hp⟩⟩

lemma upper65_gate_bound (j : ℕ) (g : Gate)
    (hj : upper65Circuit.gates[j]? = some g) : j < 65 := by
  by_contra h
  have hn : upper65Circuit.gates[j]? = none :=
    List.getElem?_eq_none (by change 65 ≤ j; omega)
  simp [hj] at hn

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
lemma upper65_valid (j : ℕ) (g : Gate)
    (hj : upper65Circuit.gates[j]? = some g) :
    (g.op = .and ∨ g.op = .or) ∧ ∃ a b : ℕ,
      g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + j ∧ b < 26 + j := by
  have jb := upper65_gate_bound j g hj
  interval_cases j <;>
    simp only [upper65Circuit, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.some.injEq] at hj <;>
    subst g <;> norm_num

end PEqualNP.Outside.L_meta_2602_aux
