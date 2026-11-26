import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

set_option maxHeartbeats 3200000 in
theorem PEqualNP.Outside.R_meta_5995_926
    (compress : ∀ (n : ℕ) (C : Circuit) (v : Fin n) (S : Finset ℕ),
      IsAO2 n C →
      (∀ j ∈ S, j < C.size ∧ ∃ p < n + j,
        ∀ x : Fin n → Bool,
          let w := C.wires (List.ofFn (Function.update x v false))
          w.getD (n + j) false = w.getD p false) →
      (∃ x y : Fin n → Bool,
        C.eval (List.ofFn (Function.update x v false)) ≠
          C.eval (List.ofFn (Function.update y v false))) →
      ∃ D : Circuit, IsAO2 n D ∧ D.size + S.card ≤ C.size ∧
        ∀ x : Fin n → Bool,
          D.eval (List.ofFn x) = C.eval (List.ofFn (Function.update x v false)))
    (aliases :
      let I := fun p l : Fin 13 => (p - l).val ∈ ([0, 1, 3, 9] : List ℕ)
      ∀ C : Circuit, IsAO2 26 C → C.size ≤ 63 →
        (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
          ∃ p l : Fin 13, I p l ∧
            x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) →
        ∃ (v : Fin 26) (S : Finset ℕ), 5 ≤ S.card ∧
          ∀ j ∈ S, j < C.size ∧ ∃ p < 26 + j,
            ∀ x : Fin 26 → Bool,
              let w := C.wires (List.ofFn (Function.update x v false))
              w.getD (26 + j) false = w.getD p false) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → x1.size ≤ (63 : ℕ) → (∀ (x4 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), (x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨ x5 = x6 + (9 : Fin (13 : ℕ))) ∧ x4 (Fin.castAdd (13 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x6) = Bool.true) → ∃ (x5 : Fin (26 : ℕ)) (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x6 ∧ x6.size + (5 : ℕ) ≤ x1.size ∧ ∀ (x7 : Fin (26 : ℕ) → Bool), x6.eval (List.ofFn x7) = Bool.true ↔ ∃ (x8 : Fin (13 : ℕ)) (x9 : Fin (13 : ℕ)), (x8 = x9 ∨ x8 = x9 + (1 : Fin (13 : ℕ)) ∨ x8 = x9 + (3 : Fin (13 : ℕ)) ∨ x8 = x9 + (9 : Fin (13 : ℕ))) ∧ Fin.castAdd (13 : ℕ) x8 ≠ x5 ∧ Fin.natAdd (13 : ℕ) x9 ≠ x5 ∧ x7 (Fin.castAdd (13 : ℕ) x8) = Bool.true ∧ x7 (Fin.natAdd (13 : ℕ) x9) = Bool.true := by
  intro C model cap correct
  let pt := (Fin.castAdd 13 : Fin 13 → Fin 26)
  let ln := (Fin.natAdd 13 : Fin 13 → Fin 26)
  let I := fun p l : Fin 13 => p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
  let J := fun p l : Fin 13 => (p - l).val ∈ ([0, 1, 3, 9] : List ℕ)
  have incidences : ∀ p l : Fin 13, I p l ↔ J p l := by decide +kernel
  have compressed (x : Fin 26 → Bool) : C.eval (List.ofFn x) = true ↔
      ∃ p l : Fin 13, J p l ∧ x (pt p) = true ∧ x (ln l) = true := by
    rw [correct]
    constructor
    · rintro ⟨p, l, h, hp, hl⟩
      exact ⟨p, l, (incidences p l).1 h, hp, hl⟩
    · rintro ⟨p, l, h, hp, hl⟩
      exact ⟨p, l, (incidences p l).2 h, hp, hl⟩
  obtain ⟨v, S, count, cert⟩ := aliases C model cap compressed
  let upd (x : Fin 26 → Bool) := Function.update x v false
  have pinSpec (x : Fin 26 → Bool) : C.eval (List.ofFn (upd x)) = true ↔
      ∃ p l : Fin 13, I p l ∧ pt p ≠ v ∧ ln l ≠ v ∧
        x (pt p) = true ∧ x (ln l) = true := by
    rw [correct]
    constructor
    · rintro ⟨p, l, h, hp, hl⟩
      have pn : pt p ≠ v := by
        intro eq
        change Function.update x v false (pt p) = true at hp
        rw [eq, Function.update_self] at hp
        contradiction
      have hn : ln l ≠ v := by
        intro eq
        change Function.update x v false (ln l) = true at hl
        rw [eq, Function.update_self] at hl
        contradiction
      change Function.update x v false (pt p) = true at hp
      change Function.update x v false (ln l) = true at hl
      rw [Function.update_of_ne pn] at hp
      rw [Function.update_of_ne hn] at hl
      exact ⟨p, l, h, pn, hn, hp, hl⟩
    · rintro ⟨p, l, h, pn, hn, hp, hl⟩
      refine ⟨p, l, h, ?_, ?_⟩
      · change Function.update x v false (pt p) = true
        rwa [Function.update_of_ne pn]
      · change Function.update x v false (ln l) = true
        rwa [Function.update_of_ne hn]
  have edgeOutside : ∀ a : Fin 26,
      ∃ p l : Fin 13, I p l ∧ pt p ≠ a ∧ ln l ≠ a := by decide +kernel
  obtain ⟨p, l, e, pn, hn⟩ := edgeOutside v
  let off : Fin 26 → Bool := fun _ => false
  let on : Fin 26 → Bool := fun j => decide (j = pt p ∨ j = ln l)
  have zero : C.eval (List.ofFn (upd off)) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨a, b, _, _, _, bad, _⟩ := (pinSpec off).1 h
    exact Bool.false_ne_true bad
  have one : C.eval (List.ofFn (upd on)) = true := by
    apply (pinSpec on).2
    exact ⟨p, l, e, pn, hn, by simp [on], by simp [on]⟩
  have different : ∃ x y : Fin 26 → Bool,
      C.eval (List.ofFn (upd x)) ≠ C.eval (List.ofFn (upd y)) := by
    exact ⟨off, on, by rw [zero, one]; decide⟩
  obtain ⟨D, dm, budget, eval⟩ := compress 26 C v S model cert different
  refine ⟨v, D, dm, by omega, fun x => ?_⟩
  rw [eval x]
  exact pinSpec x
