import Mathlib

namespace PEqualNP.Outside.L_meta_3787

def fsVec (s t : Finset (Fin 13)) (i : Fin 26) : Bool :=
  if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ s)
  else decide (Fin.ofNat 13 i.val ∈ t)

set_option maxHeartbeats 2000000 in
lemma fsMembership (s t : Finset (Fin 13)) :
  (((((0 : Fin 13) ∈ s ∧ ((((0 : Fin 13) ∈ t ∨ (1 : Fin 13) ∈ t) ∨ (3 : Fin 13) ∈ t) ∨ (9 : Fin 13) ∈ t)) ∨ ((1 : Fin 13) ∈ s ∧ ((((0 : Fin 13) ∈ t ∨ (2 : Fin 13) ∈ t) ∨ (8 : Fin 13) ∈ t) ∨ (12 : Fin 13) ∈ t))) ∨ ((3 : Fin 13) ∈ s ∧ ((((0 : Fin 13) ∈ t ∨ (6 : Fin 13) ∈ t) ∨ (10 : Fin 13) ∈ t) ∨ (11 : Fin 13) ∈ t))) ∨ ((9 : Fin 13) ∈ s ∧ ((((0 : Fin 13) ∈ t ∨ (4 : Fin 13) ∈ t) ∨ (5 : Fin 13) ∈ t) ∨ (7 : Fin 13) ∈ t))) ↔
    ∃ p ∈ s, p.val ∈ ([0, 1, 3, 9] : List ℕ) ∧
      ∃ l ∈ t, (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) := by
  constructor
  · intro h
    rcases h with ((h | h) | h) | h
    · obtain ⟨hp, h⟩ := h
      rcases h with ((hl | hl) | hl) | hl
      · exact ⟨0, hp, by decide, 0, hl, by decide⟩
      · exact ⟨0, hp, by decide, 1, hl, by decide⟩
      · exact ⟨0, hp, by decide, 3, hl, by decide⟩
      · exact ⟨0, hp, by decide, 9, hl, by decide⟩
    · obtain ⟨hp, h⟩ := h
      rcases h with ((hl | hl) | hl) | hl
      · exact ⟨1, hp, by decide, 0, hl, by decide⟩
      · exact ⟨1, hp, by decide, 2, hl, by decide⟩
      · exact ⟨1, hp, by decide, 8, hl, by decide⟩
      · exact ⟨1, hp, by decide, 12, hl, by decide⟩
    · obtain ⟨hp, h⟩ := h
      rcases h with ((hl | hl) | hl) | hl
      · exact ⟨3, hp, by decide, 0, hl, by decide⟩
      · exact ⟨3, hp, by decide, 6, hl, by decide⟩
      · exact ⟨3, hp, by decide, 10, hl, by decide⟩
      · exact ⟨3, hp, by decide, 11, hl, by decide⟩
    · obtain ⟨hp, h⟩ := h
      rcases h with ((hl | hl) | hl) | hl
      · exact ⟨9, hp, by decide, 0, hl, by decide⟩
      · exact ⟨9, hp, by decide, 4, hl, by decide⟩
      · exact ⟨9, hp, by decide, 5, hl, by decide⟩
      · exact ⟨9, hp, by decide, 7, hl, by decide⟩
  · rintro ⟨p, hp, hs, l, hl, hnear⟩
    fin_cases p <;> norm_num at hs
    all_goals fin_cases l <;> norm_num at hnear
    all_goals simp_all

lemma fsSemantics (s t : Finset (Fin 13)) :
  ((((fsVec s t 0 && (((fsVec s t 13 || fsVec s t 14) || fsVec s t 16) || fsVec s t 22)) || (fsVec s t 1 && (((fsVec s t 13 || fsVec s t 15) || fsVec s t 21) || fsVec s t 25))) || (fsVec s t 3 && (((fsVec s t 13 || fsVec s t 19) || fsVec s t 23) || fsVec s t 24))) || (fsVec s t 9 && (((fsVec s t 13 || fsVec s t 17) || fsVec s t 18) || fsVec s t 20))) = true ↔
    ∃ p ∈ s, p.val ∈ ([0, 1, 3, 9] : List ℕ) ∧
      ∃ l ∈ t, (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) := by
  change ((((decide ((0 : Fin 13) ∈ s) && (((decide ((0 : Fin 13) ∈ t) || decide ((1 : Fin 13) ∈ t)) || decide ((3 : Fin 13) ∈ t)) || decide ((9 : Fin 13) ∈ t))) || (decide ((1 : Fin 13) ∈ s) && (((decide ((0 : Fin 13) ∈ t) || decide ((2 : Fin 13) ∈ t)) || decide ((8 : Fin 13) ∈ t)) || decide ((12 : Fin 13) ∈ t)))) || (decide ((3 : Fin 13) ∈ s) && (((decide ((0 : Fin 13) ∈ t) || decide ((6 : Fin 13) ∈ t)) || decide ((10 : Fin 13) ∈ t)) || decide ((11 : Fin 13) ∈ t)))) || (decide ((9 : Fin 13) ∈ s) && (((decide ((0 : Fin 13) ∈ t) || decide ((4 : Fin 13) ∈ t)) || decide ((5 : Fin 13) ∈ t)) || decide ((7 : Fin 13) ∈ t)))) = true ↔ _
  simpa only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] using fsMembership s t

lemma fsSemanticsOr (s t : Finset (Fin 13)) (b : Bool) :
  (((((b || (fsVec s t 0 && (((fsVec s t 13 || fsVec s t 14) || fsVec s t 16) || fsVec s t 22))) ||
    (fsVec s t 1 && (((fsVec s t 13 || fsVec s t 15) || fsVec s t 21) || fsVec s t 25))) ||
    (fsVec s t 3 && (((fsVec s t 13 || fsVec s t 19) || fsVec s t 23) || fsVec s t 24))) ||
    (fsVec s t 9 && (((fsVec s t 13 || fsVec s t 17) || fsVec s t 18) || fsVec s t 20)))) = true ↔
    b = true ∨ ∃ p ∈ s, p.val ∈ ([0, 1, 3, 9] : List ℕ) ∧
      ∃ l ∈ t, (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) := by
  simpa only [Bool.or_eq_true, or_assoc] using
    or_congr (Iff.rfl : b = true ↔ b = true) (fsSemantics s t)

end PEqualNP.Outside.L_meta_3787
