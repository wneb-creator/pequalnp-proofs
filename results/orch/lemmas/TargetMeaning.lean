import PEqualNP.Defs

example (a b : Bool) (h : a = true ↔ b = true) : a = b :=
  Bool.eq_iff_iff.mpr h

theorem targetMeaning (x : Fin 25 → Bool) :
    let D : Finset (Fin 13) := {0, 1, 3, 9}
    let ln (l : Fin 13) : Fin 25 := ⟨12 + l.val, by omega⟩
    let t := Finset.univ.filter fun l : Fin 13 => x (ln l) = true
    (x 12 || x 13 || x 15 || x 21) = true ↔ ∃ l ∈ t, l ∈ D := by
  dsimp only
  simp [Bool.or_eq_true, or_assoc, and_or_left, exists_or]
