import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_2590_aux.Bridge
abbrev V := Fin 10
def edges : Finset (Sym2 V) := {s(0, 1), s(1, 2), s(2, 3), s(3, 4), s(4, 0), s(0, 5), s(1, 6), s(2, 7), s(3, 8), s(4, 9), s(5, 7), s(6, 8), s(7, 9), s(8, 5), s(9, 6)}
def related (v w : V) : Bool := decide (s(v, w) ∈ edges)
def petersenFun (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

set_option maxRecDepth 4000 in
theorem related_pairs : ∀ a b : Fin 10, related a b = true ↔
    (a = 0 ∧ b = 1) ∨
    (a = 1 ∧ b = 2) ∨
    (a = 2 ∧ b = 3) ∨
    (a = 3 ∧ b = 4) ∨
    (a = 4 ∧ b = 0) ∨
    (a = 0 ∧ b = 5) ∨
    (a = 1 ∧ b = 6) ∨
    (a = 2 ∧ b = 7) ∨
    (a = 3 ∧ b = 8) ∨
    (a = 4 ∧ b = 9) ∨
    (a = 5 ∧ b = 7) ∨
    (a = 7 ∧ b = 9) ∨
    (a = 9 ∧ b = 6) ∨
    (a = 6 ∧ b = 8) ∨
    (a = 8 ∧ b = 5) ∨
    (a = 1 ∧ b = 0) ∨
    (a = 2 ∧ b = 1) ∨
    (a = 3 ∧ b = 2) ∨
    (a = 4 ∧ b = 3) ∨
    (a = 0 ∧ b = 4) ∨
    (a = 5 ∧ b = 0) ∨
    (a = 6 ∧ b = 1) ∨
    (a = 7 ∧ b = 2) ∨
    (a = 8 ∧ b = 3) ∨
    (a = 9 ∧ b = 4) ∨
    (a = 7 ∧ b = 5) ∨
    (a = 9 ∧ b = 7) ∨
    (a = 6 ∧ b = 9) ∨
    (a = 8 ∧ b = 6) ∨
    (a = 5 ∧ b = 8) := by
  decide +kernel

theorem petersen_relation : ∀ x : Fin 10 → Bool,
    petersenFun x = decide (∃ a b : Fin 10, x a = true ∧ x b = true ∧ related a b = true) := by
  intro x
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  simp only [petersenFun, Bool.or_eq_true, Bool.and_eq_true]
  constructor
  · intro h
    simp only [or_assoc] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, h.2, by decide⟩
    · exact ⟨1, 2, h.1, h.2, by decide⟩
    · exact ⟨2, 3, h.1, h.2, by decide⟩
    · exact ⟨3, 4, h.1, h.2, by decide⟩
    · exact ⟨4, 0, h.1, h.2, by decide⟩
    · exact ⟨0, 5, h.1, h.2, by decide⟩
    · exact ⟨1, 6, h.1, h.2, by decide⟩
    · exact ⟨2, 7, h.1, h.2, by decide⟩
    · exact ⟨3, 8, h.1, h.2, by decide⟩
    · exact ⟨4, 9, h.1, h.2, by decide⟩
    · exact ⟨5, 7, h.1, h.2, by decide⟩
    · exact ⟨7, 9, h.1, h.2, by decide⟩
    · exact ⟨9, 6, h.1, h.2, by decide⟩
    · exact ⟨6, 8, h.1, h.2, by decide⟩
    · exact ⟨8, 5, h.1, h.2, by decide⟩
  · rintro ⟨a, b, ha, hb, hab⟩
    rcases (related_pairs a b).mp hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all

end PEqualNP.Outside.L_meta_2590_aux.Bridge
