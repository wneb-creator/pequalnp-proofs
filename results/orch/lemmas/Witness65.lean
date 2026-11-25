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

end PEqualNP.Outside.L_meta_2602_aux.Witness65
