import PEqualNP.Defs.CircuitLowerBounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

namespace PEqualNP.Outside.L_meta_2602_aux.Witness65

open PEqualNP.CircuitLowerBounds

def circuit : Circuit :=
  ⟨[
    ⟨.or, [21, 25]⟩,
    ⟨.or, [18, 26]⟩,
    ⟨.or, [20, 27]⟩,
    ⟨.and, [8, 28]⟩,
    ⟨.or, [15, 20]⟩,
    ⟨.or, [13, 16]⟩,
    ⟨.or, [30, 31]⟩,
    ⟨.and, [3, 32]⟩,
    ⟨.or, [15, 18]⟩,
    ⟨.or, [17, 34]⟩,
    ⟨.or, [22, 35]⟩,
    ⟨.and, [5, 36]⟩,
    ⟨.or, [22, 23]⟩,
    ⟨.or, [14, 20]⟩,
    ⟨.or, [38, 39]⟩,
    ⟨.and, [10, 40]⟩,
    ⟨.or, [13, 17]⟩,
    ⟨.or, [23, 42]⟩,
    ⟨.or, [25, 43]⟩,
    ⟨.and, [0, 44]⟩,
    ⟨.or, [13, 19]⟩,
    ⟨.or, [22, 46]⟩,
    ⟨.or, [21, 47]⟩,
    ⟨.and, [9, 48]⟩,
    ⟨.or, [14, 15]⟩,
    ⟨.or, [25, 50]⟩,
    ⟨.or, [19, 51]⟩,
    ⟨.and, [2, 52]⟩,
    ⟨.or, [22, 24]⟩,
    ⟨.or, [25, 54]⟩,
    ⟨.or, [16, 55]⟩,
    ⟨.and, [12, 56]⟩,
    ⟨.or, [14, 24]⟩,
    ⟨.or, [13, 58]⟩,
    ⟨.or, [18, 59]⟩,
    ⟨.and, [1, 60]⟩,
    ⟨.or, [19, 20]⟩,
    ⟨.or, [24, 62]⟩,
    ⟨.or, [17, 63]⟩,
    ⟨.and, [7, 64]⟩,
    ⟨.or, [16, 23]⟩,
    ⟨.or, [19, 66]⟩,
    ⟨.or, [18, 67]⟩,
    ⟨.and, [6, 68]⟩,
    ⟨.or, [14, 16]⟩,
    ⟨.or, [17, 70]⟩,
    ⟨.or, [21, 71]⟩,
    ⟨.or, [21, 23]⟩,
    ⟨.or, [15, 24]⟩,
    ⟨.or, [73, 74]⟩,
    ⟨.and, [11, 75]⟩,
    ⟨.or, [45, 53]⟩,
    ⟨.or, [41, 77]⟩,
    ⟨.or, [69, 78]⟩,
    ⟨.or, [37, 57]⟩,
    ⟨.or, [29, 61]⟩,
    ⟨.or, [79, 80]⟩,
    ⟨.or, [33, 82]⟩,
    ⟨.or, [49, 76]⟩,
    ⟨.or, [81, 84]⟩,
    ⟨.or, [83, 85]⟩,
    ⟨.or, [65, 86]⟩,
    ⟨.or, [4, 87]⟩,
    ⟨.or, [72, 87]⟩,
    ⟨.and, [88, 89]⟩
  ], 90⟩

lemma circuit_size : circuit.size = 65 := rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma circuit_eval (x : Fin 26 → Bool) :
    circuit.eval (List.ofFn x) = ((x 4 || ((x 7 && (x 17 || (x 24 || (x 19 || x 20)))) || (((x 3 && ((x 15 || x 20) || (x 13 || x 16))) || (((x 6 && (x 18 || (x 19 || (x 16 || x 23)))) || ((x 10 && ((x 22 || x 23) || (x 14 || x 20))) || ((x 0 && (x 25 || (x 23 || (x 13 || x 17)))) || (x 2 && (x 19 || (x 25 || (x 14 || x 15))))))) || ((x 5 && (x 22 || (x 17 || (x 15 || x 18)))) || (x 12 && (x 16 || (x 25 || (x 22 || x 24))))))) || (((x 8 && (x 20 || (x 18 || (x 21 || x 25)))) || (x 1 && (x 18 || (x 13 || (x 14 || x 24))))) || ((x 9 && (x 21 || (x 22 || (x 13 || x 19)))) || (x 11 && ((x 21 || x 23) || (x 15 || x 24)))))))) && ((x 21 || (x 17 || (x 14 || x 16))) || ((x 7 && (x 17 || (x 24 || (x 19 || x 20)))) || (((x 3 && ((x 15 || x 20) || (x 13 || x 16))) || (((x 6 && (x 18 || (x 19 || (x 16 || x 23)))) || ((x 10 && ((x 22 || x 23) || (x 14 || x 20))) || ((x 0 && (x 25 || (x 23 || (x 13 || x 17)))) || (x 2 && (x 19 || (x 25 || (x 14 || x 15))))))) || ((x 5 && (x 22 || (x 17 || (x 15 || x 18)))) || (x 12 && (x 16 || (x 25 || (x 22 || x 24))))))) || (((x 8 && (x 20 || (x 18 || (x 21 || x 25)))) || (x 1 && (x 18 || (x 13 || (x 14 || x 24))))) || ((x 9 && (x 21 || (x 22 || (x 13 || x 19)))) || (x 11 && ((x 21 || x 23) || (x 15 || x 24))))))))) := by
  simp [circuit, Circuit.eval, Circuit.wires, GateOp.eval, List.ofFn_succ]

lemma distribute_right (a b c : Bool) :
    ((b || a) && (c || a)) = (a || (b && c)) := by
  cases a <;> cases b <;> cases c <;> rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma circuit_spec (x : Fin 26 → Bool) :
    circuit.eval (List.ofFn x) = true ↔
      ∃ p l : Fin 13, (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
        x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true := by
  rw [circuit_eval, distribute_right]
  simp only [Bool.or_eq_true, Bool.and_eq_true]
  constructor
  · intro h
    rcases h with h | h
    ·
      rcases h with h | h
      ·
        rcases h with ⟨hp, hl⟩
        rcases hl with hl | hl
        ·
          exact ⟨7, 4, by decide, hp, hl⟩
        ·
          rcases hl with hl | hl
          ·
            exact ⟨7, 11, by decide, hp, hl⟩
          ·
            rcases hl with hl | hl
            ·
              exact ⟨7, 6, by decide, hp, hl⟩
            ·
              exact ⟨7, 7, by decide, hp, hl⟩
      ·
        rcases h with h | h
        ·
          rcases h with h | h
          ·
            rcases h with ⟨hp, hl⟩
            rcases hl with hl | hl
            ·
              rcases hl with hl | hl
              ·
                exact ⟨3, 2, by decide, hp, hl⟩
              ·
                exact ⟨3, 7, by decide, hp, hl⟩
            ·
              rcases hl with hl | hl
              ·
                exact ⟨3, 0, by decide, hp, hl⟩
              ·
                exact ⟨3, 3, by decide, hp, hl⟩
          ·
            rcases h with h | h
            ·
              rcases h with h | h
              ·
                rcases h with ⟨hp, hl⟩
                rcases hl with hl | hl
                ·
                  exact ⟨6, 5, by decide, hp, hl⟩
                ·
                  rcases hl with hl | hl
                  ·
                    exact ⟨6, 6, by decide, hp, hl⟩
                  ·
                    rcases hl with hl | hl
                    ·
                      exact ⟨6, 3, by decide, hp, hl⟩
                    ·
                      exact ⟨6, 10, by decide, hp, hl⟩
              ·
                rcases h with h | h
                ·
                  rcases h with ⟨hp, hl⟩
                  rcases hl with hl | hl
                  ·
                    rcases hl with hl | hl
                    ·
                      exact ⟨10, 9, by decide, hp, hl⟩
                    ·
                      exact ⟨10, 10, by decide, hp, hl⟩
                  ·
                    rcases hl with hl | hl
                    ·
                      exact ⟨10, 1, by decide, hp, hl⟩
                    ·
                      exact ⟨10, 7, by decide, hp, hl⟩
                ·
                  rcases h with h | h
                  ·
                    rcases h with ⟨hp, hl⟩
                    rcases hl with hl | hl
                    ·
                      exact ⟨0, 12, by decide, hp, hl⟩
                    ·
                      rcases hl with hl | hl
                      ·
                        exact ⟨0, 10, by decide, hp, hl⟩
                      ·
                        rcases hl with hl | hl
                        ·
                          exact ⟨0, 0, by decide, hp, hl⟩
                        ·
                          exact ⟨0, 4, by decide, hp, hl⟩
                  ·
                    rcases h with ⟨hp, hl⟩
                    rcases hl with hl | hl
                    ·
                      exact ⟨2, 6, by decide, hp, hl⟩
                    ·
                      rcases hl with hl | hl
                      ·
                        exact ⟨2, 12, by decide, hp, hl⟩
                      ·
                        rcases hl with hl | hl
                        ·
                          exact ⟨2, 1, by decide, hp, hl⟩
                        ·
                          exact ⟨2, 2, by decide, hp, hl⟩
            ·
              rcases h with h | h
              ·
                rcases h with ⟨hp, hl⟩
                rcases hl with hl | hl
                ·
                  exact ⟨5, 9, by decide, hp, hl⟩
                ·
                  rcases hl with hl | hl
                  ·
                    exact ⟨5, 4, by decide, hp, hl⟩
                  ·
                    rcases hl with hl | hl
                    ·
                      exact ⟨5, 2, by decide, hp, hl⟩
                    ·
                      exact ⟨5, 5, by decide, hp, hl⟩
              ·
                rcases h with ⟨hp, hl⟩
                rcases hl with hl | hl
                ·
                  exact ⟨12, 3, by decide, hp, hl⟩
                ·
                  rcases hl with hl | hl
                  ·
                    exact ⟨12, 12, by decide, hp, hl⟩
                  ·
                    rcases hl with hl | hl
                    ·
                      exact ⟨12, 9, by decide, hp, hl⟩
                    ·
                      exact ⟨12, 11, by decide, hp, hl⟩
        ·
          rcases h with h | h
          ·
            rcases h with h | h
            ·
              rcases h with ⟨hp, hl⟩
              rcases hl with hl | hl
              ·
                exact ⟨8, 7, by decide, hp, hl⟩
              ·
                rcases hl with hl | hl
                ·
                  exact ⟨8, 5, by decide, hp, hl⟩
                ·
                  rcases hl with hl | hl
                  ·
                    exact ⟨8, 8, by decide, hp, hl⟩
                  ·
                    exact ⟨8, 12, by decide, hp, hl⟩
            ·
              rcases h with ⟨hp, hl⟩
              rcases hl with hl | hl
              ·
                exact ⟨1, 5, by decide, hp, hl⟩
              ·
                rcases hl with hl | hl
                ·
                  exact ⟨1, 0, by decide, hp, hl⟩
                ·
                  rcases hl with hl | hl
                  ·
                    exact ⟨1, 1, by decide, hp, hl⟩
                  ·
                    exact ⟨1, 11, by decide, hp, hl⟩
          ·
            rcases h with h | h
            ·
              rcases h with ⟨hp, hl⟩
              rcases hl with hl | hl
              ·
                exact ⟨9, 8, by decide, hp, hl⟩
              ·
                rcases hl with hl | hl
                ·
                  exact ⟨9, 9, by decide, hp, hl⟩
                ·
                  rcases hl with hl | hl
                  ·
                    exact ⟨9, 0, by decide, hp, hl⟩
                  ·
                    exact ⟨9, 6, by decide, hp, hl⟩
            ·
              rcases h with ⟨hp, hl⟩
              rcases hl with hl | hl
              ·
                rcases hl with hl | hl
                ·
                  exact ⟨11, 8, by decide, hp, hl⟩
                ·
                  exact ⟨11, 10, by decide, hp, hl⟩
              ·
                rcases hl with hl | hl
                ·
                  exact ⟨11, 2, by decide, hp, hl⟩
                ·
                  exact ⟨11, 11, by decide, hp, hl⟩
    ·
      rcases h with ⟨hp, hl⟩
      rcases hl with hl | hl
      ·
        exact ⟨4, 8, by decide, hp, hl⟩
      ·
        rcases hl with hl | hl
        ·
          exact ⟨4, 4, by decide, hp, hl⟩
        ·
          rcases hl with hl | hl
          ·
            exact ⟨4, 1, by decide, hp, hl⟩
          ·
            exact ⟨4, 3, by decide, hp, hl⟩
  · rintro ⟨p, l, hI, hp, hl⟩
    fin_cases p <;> fin_cases l <;> norm_num at hI
    · exact (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl ⟨hp, (Or.inr (Or.inr (Or.inl hl)))⟩))))))))
    · exact (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl ⟨hp, (Or.inr (Or.inr (Or.inr hl)))⟩))))))))
    · exact (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl ⟨hp, (Or.inr (Or.inl hl))⟩))))))))
    · exact (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl ⟨hp, (Or.inl hl)⟩))))))))
    · exact (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr ⟨hp, (Or.inr (Or.inl hl))⟩)))))
    · exact (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr ⟨hp, (Or.inr (Or.inr (Or.inl hl)))⟩)))))
    · exact (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr ⟨hp, (Or.inl hl)⟩)))))
    · exact (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr ⟨hp, (Or.inr (Or.inr (Or.inr hl)))⟩)))))
    · exact (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr ⟨hp, (Or.inr (Or.inr (Or.inl hl)))⟩))))))))
    · exact (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr ⟨hp, (Or.inr (Or.inr (Or.inr hl)))⟩))))))))
    · exact (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr ⟨hp, (Or.inl hl)⟩))))))))
    · exact (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr ⟨hp, (Or.inr (Or.inl hl))⟩))))))))
    · exact (Or.inl (Or.inr (Or.inl (Or.inl ⟨hp, (Or.inr (Or.inl hl))⟩))))
    · exact (Or.inl (Or.inr (Or.inl (Or.inl ⟨hp, (Or.inl (Or.inl hl))⟩))))
    · exact (Or.inl (Or.inr (Or.inl (Or.inl ⟨hp, (Or.inr (Or.inr hl))⟩))))
    · exact (Or.inl (Or.inr (Or.inl (Or.inl ⟨hp, (Or.inl (Or.inr hl))⟩))))
    · exact (Or.inr ⟨hp, (Or.inr (Or.inr (Or.inl hl)))⟩)
    · exact (Or.inr ⟨hp, (Or.inr (Or.inr (Or.inr hl)))⟩)
    · exact (Or.inr ⟨hp, (Or.inr (Or.inl hl))⟩)
    · exact (Or.inr ⟨hp, (Or.inl hl)⟩)
    · exact (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl ⟨hp, (Or.inr (Or.inr (Or.inl hl)))⟩))))))
    · exact (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl ⟨hp, (Or.inr (Or.inl hl))⟩))))))
    · exact (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl ⟨hp, (Or.inr (Or.inr (Or.inr hl)))⟩))))))
    · exact (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl ⟨hp, (Or.inl hl)⟩))))))
    · exact (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl ⟨hp, (Or.inr (Or.inr (Or.inl hl)))⟩))))))
    · exact (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl ⟨hp, (Or.inl hl)⟩))))))
    · exact (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl ⟨hp, (Or.inr (Or.inl hl))⟩))))))
    · exact (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl ⟨hp, (Or.inr (Or.inr (Or.inr hl)))⟩))))))
    · exact (Or.inl (Or.inl ⟨hp, (Or.inl hl)⟩))
    · exact (Or.inl (Or.inl ⟨hp, (Or.inr (Or.inr (Or.inl hl)))⟩))
    · exact (Or.inl (Or.inl ⟨hp, (Or.inr (Or.inr (Or.inr hl)))⟩))
    · exact (Or.inl (Or.inl ⟨hp, (Or.inr (Or.inl hl))⟩))
    · exact (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl ⟨hp, (Or.inr (Or.inl hl))⟩)))))
    · exact (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl ⟨hp, (Or.inl hl)⟩)))))
    · exact (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl ⟨hp, (Or.inr (Or.inr (Or.inl hl)))⟩)))))
    · exact (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl ⟨hp, (Or.inr (Or.inr (Or.inr hl)))⟩)))))
    · exact (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨hp, (Or.inr (Or.inr (Or.inl hl)))⟩)))))
    · exact (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨hp, (Or.inr (Or.inr (Or.inr hl)))⟩)))))
    · exact (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨hp, (Or.inl hl)⟩)))))
    · exact (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨hp, (Or.inr (Or.inl hl))⟩)))))
    · exact (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl ⟨hp, (Or.inr (Or.inl hl))⟩)))))))
    · exact (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl ⟨hp, (Or.inr (Or.inr hl))⟩)))))))
    · exact (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl ⟨hp, (Or.inl (Or.inl hl))⟩)))))))
    · exact (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl ⟨hp, (Or.inl (Or.inr hl))⟩)))))))
    · exact (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ⟨hp, (Or.inr (Or.inl hl))⟩)))))
    · exact (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ⟨hp, (Or.inl (Or.inl hl))⟩)))))
    · exact (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ⟨hp, (Or.inl (Or.inr hl))⟩)))))
    · exact (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ⟨hp, (Or.inr (Or.inr hl))⟩)))))
    · exact (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr ⟨hp, (Or.inl hl)⟩))))))
    · exact (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr ⟨hp, (Or.inr (Or.inr (Or.inl hl)))⟩))))))
    · exact (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr ⟨hp, (Or.inr (Or.inr (Or.inr hl)))⟩))))))
    · exact (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr ⟨hp, (Or.inr (Or.inl hl))⟩))))))

def trace0 (i : Nat) : Bool :=
  ([false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, false, false, false, false, false, false, false, false, false, true, true, true, true, true, true, true, false, false, false, false, false, false, false, false, false, false, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, false, false, true, true, false, false, true, true, true, true, false] : List Bool).getD i false

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma singleton_wires0 :
    circuit.wires (List.ofFn fun i : Fin 26 => decide (i.val = 0)) =
      [true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false] := by
  simp [circuit, Circuit.wires, GateOp.eval, List.ofFn_succ]

lemma trace0_input : ∀ i < 26, trace0 i = decide (i = 13) := by
  have h : ∀ i : Fin 26, trace0 i.val = decide (i.val = 13) := by decide
  exact fun i hi => h ⟨i, hi⟩

lemma trace0_output : trace0 circuit.output = false := rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma trace0_finite : ∀ j : Fin 65,
    let g := (circuit.gates[j.val]?).getD ⟨.or, []⟩
    let a := g.inputs.getD 0 0
    let b := g.inputs.getD 1 0
    let w := circuit.wires (List.ofFn fun i : Fin 26 => decide (i.val = 0))
    match g.op with
    | .and => trace0 (26 + j.val) = ((w.getD a false && trace0 b) || (trace0 a && w.getD b false))
    | .or => trace0 (26 + j.val) = (trace0 a || trace0 b)
    | _ => False := by
  rw [singleton_wires0]
  intro j
  fin_cases j <;> norm_num [circuit, trace0]

def trace13 (i : Nat) : Bool :=
  ([true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, false, false, true, true, false, false, true, true, true, true, false] : List Bool).getD i false

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma singleton_wires13 :
    circuit.wires (List.ofFn fun i : Fin 26 => decide (i.val = 13)) =
      [false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, false, false, false, false, false, false, false, false, false, true, true, true, false, true, true, true, false, false, false, false, false, false, false, false, false, false, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false] := by
  simp [circuit, Circuit.wires, GateOp.eval, List.ofFn_succ]

lemma trace13_input : ∀ i < 26, trace13 i = decide (i = 0) := by
  have h : ∀ i : Fin 26, trace13 i.val = decide (i.val = 0) := by decide
  exact fun i hi => h ⟨i, hi⟩

lemma trace13_output : trace13 circuit.output = false := rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma trace13_finite : ∀ j : Fin 65,
    let g := (circuit.gates[j.val]?).getD ⟨.or, []⟩
    let a := g.inputs.getD 0 0
    let b := g.inputs.getD 1 0
    let w := circuit.wires (List.ofFn fun i : Fin 26 => decide (i.val = 13))
    match g.op with
    | .and => trace13 (26 + j.val) = ((w.getD a false && trace13 b) || (trace13 a && w.getD b false))
    | .or => trace13 (26 + j.val) = (trace13 a || trace13 b)
    | _ => False := by
  rw [singleton_wires13]
  intro j
  fin_cases j <;> norm_num [circuit, trace13]

lemma trace0_recurrence (j : Nat) (g : Gate) (a b : Nat)
    (hj : circuit.gates[j]? = some g) (hi : g.inputs = [a,b]) :
    (g.op = .and → trace0 (26+j) =
      (((circuit.wires (List.ofFn fun i : Fin 26 => decide (i.val = 0))).getD a false && trace0 b) ||
       (trace0 a && (circuit.wires (List.ofFn fun i : Fin 26 => decide (i.val = 0))).getD b false))) ∧
    (g.op = .or → trace0 (26+j) = (trace0 a || trace0 b)) := by
  have hjlt : j < 65 := by
    change j < circuit.gates.length
    by_contra! h
    rw [List.getElem?_eq_none h] at hj
    contradiction
  have h := trace0_finite ⟨j,hjlt⟩
  constructor
  · intro op
    simpa [hj,hi,op] using h
  · intro op
    simpa [hj,hi,op] using h

lemma trace13_recurrence (j : Nat) (g : Gate) (a b : Nat)
    (hj : circuit.gates[j]? = some g) (hi : g.inputs = [a,b]) :
    (g.op = .and → trace13 (26+j) =
      (((circuit.wires (List.ofFn fun i : Fin 26 => decide (i.val = 13))).getD a false && trace13 b) ||
       (trace13 a && (circuit.wires (List.ofFn fun i : Fin 26 => decide (i.val = 13))).getD b false))) ∧
    (g.op = .or → trace13 (26+j) = (trace13 a || trace13 b)) := by
  have hjlt : j < 65 := by
    change j < circuit.gates.length
    by_contra! h
    rw [List.getElem?_eq_none h] at hj
    contradiction
  have h := trace13_finite ⟨j,hjlt⟩
  constructor
  · intro op
    simpa [hj,hi,op] using h
  · intro op
    simpa [hj,hi,op] using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma circuit_valid_finite : ∀ j : Fin 65,
    let g := (circuit.gates[j.val]?).getD ⟨.or, []⟩
    (g.op = .and ∨ g.op = .or) ∧
      ∃ a b : Nat, g.inputs = [a,b] ∧ a ≠ b ∧ a < 26+j.val ∧ b < 26+j.val := by
  intro j
  fin_cases j <;> norm_num [circuit]

lemma circuit_valid (j : Nat) (g : Gate) (hj : circuit.gates[j]? = some g) :
    (g.op = .and ∨ g.op = .or) ∧
      ∃ a b : Nat, g.inputs = [a,b] ∧ a ≠ b ∧ a < 26+j ∧ b < 26+j := by
  have hjlt : j < 65 := by
    change j < circuit.gates.length
    by_contra! h
    rw [List.getElem?_eq_none h] at hj
    contradiction
  simpa [hj] using circuit_valid_finite ⟨j,hjlt⟩

lemma size65_double_read :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size = (65 : ℕ) ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (26 : ℕ) + x2 ∧ x6 < (26 : ℕ) + x2) ∧ (∀ (x2 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ))) ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true) ∧ (∃ (x2 : ℕ → Bool), (∀ x3 < (26 : ℕ), x2 x3 = Decidable.decide (x3 = (13 : ℕ))) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate) (x5 x6 : ℕ), x1.gates[x3]? = Option.some x4 → x4.inputs = [x5, x6] → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and → x2 ((26 : ℕ) + x3) = ((x1.wires (List.ofFn fun (x10 : Fin (26 : ℕ)) => Decidable.decide (↑x10 = (0 : ℕ)))).getD x5 Bool.false && x2 x6 || x2 x5 && (x1.wires (List.ofFn fun (x10 : Fin (26 : ℕ)) => Decidable.decide (↑x10 = (0 : ℕ)))).getD x6 Bool.false)) ∧ (x4.op = PEqualNP.CircuitLowerBounds.GateOp.or → x2 ((26 : ℕ) + x3) = (x2 x5 || x2 x6))) ∧ x2 x1.output = Bool.false) ∧ ∃ (x2 : ℕ → Bool), (∀ x3 < (26 : ℕ), x2 x3 = Decidable.decide (x3 = (0 : ℕ))) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate) (x5 x6 : ℕ), x1.gates[x3]? = Option.some x4 → x4.inputs = [x5, x6] → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and → x2 ((26 : ℕ) + x3) = ((x1.wires (List.ofFn fun (x10 : Fin (26 : ℕ)) => Decidable.decide (↑x10 = (13 : ℕ)))).getD x5 Bool.false && x2 x6 || x2 x5 && (x1.wires (List.ofFn fun (x10 : Fin (26 : ℕ)) => Decidable.decide (↑x10 = (13 : ℕ)))).getD x6 Bool.false)) ∧ (x4.op = PEqualNP.CircuitLowerBounds.GateOp.or → x2 ((26 : ℕ) + x3) = (x2 x5 || x2 x6))) ∧ x2 x1.output = Bool.false := by
  refine ⟨circuit, circuit_size, circuit_valid, circuit_spec, ?_, ?_⟩
  · exact ⟨trace0, trace0_input, trace0_recurrence, trace0_output⟩
  · exact ⟨trace13, trace13_input, trace13_recurrence, trace13_output⟩

end PEqualNP.Outside.L_meta_2602_aux.Witness65
