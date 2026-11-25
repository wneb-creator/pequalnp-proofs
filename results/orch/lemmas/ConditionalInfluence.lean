import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2373

def edge (x : Fin 10 → Bool) : Bool :=
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
    x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5


def pairInput (a c : Fin 10) (i : Fin 10) : Bool := decide (i = a ∨ i = c)


def singleInput (c i : Fin 10) : Bool := decide (i = c)

def tripleInput (a b c i : Fin 10) : Bool := decide (i = a ∨ i = b ∨ i = c)

lemma singleton_no_edge : ∀ c : Fin 10, edge (singleInput c) = false := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma zero_separator : ∀ a b : Fin 10, a ≠ b → ∃ c : Fin 10,
    c ≠ a ∧ c ≠ b ∧ edge (pairInput a c) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma one_separator : ∀ a b : Fin 10, a ≠ b → ∃ c : Fin 10,
    c ≠ a ∧ edge (pairInput b c) = false ∧ edge (tripleInput a b c) = true := by
  decide +kernel

lemma conditional_influence (a b : Fin 10) (hab : a ≠ b) (t : Bool) :
    ∃ x y : Fin 10 → Bool,
      (∀ i, i ≠ a → x i = y i) ∧ x b = t ∧ y b = t ∧
      x a = false ∧ y a = true ∧ edge x ≠ edge y := by
  cases t
  · obtain ⟨c, hca, hcb, he⟩ := zero_separator a b hab
    refine ⟨singleInput c, pairInput a c, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hia
      simp [singleInput, pairInput, hia]
    · simp [singleInput, Ne.symm hcb]
    · simp [pairInput, Ne.symm hab, Ne.symm hcb]
    · simp [singleInput, Ne.symm hca]
    · simp [pairInput]
    · rw [singleton_no_edge, he]
      decide
  · obtain ⟨c, hca, he0, he1⟩ := one_separator a b hab
    refine ⟨pairInput b c, tripleInput a b c, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hia
      simp [pairInput, tripleInput, hia]
    · simp [pairInput]
    · simp [tripleInput]
    · simp [pairInput, hab, Ne.symm hca]
    · simp [tripleInput]
    · rw [he0, he1]
      decide

def boolBin (d : Nat) (a b : Bool) : Bool :=
  if d = 0 then a && b else if d = 1 then a || b else
    if d = 2 then a && !b else !a && b

lemma no_binary_identification_left (d : Nat) (hd : d < 4) (a b : Fin 10)
    (hab : a ≠ b) : ∃ x y : Fin 10 → Bool,
      (∀ i, i ≠ a → x i = y i) ∧
      boolBin d (x a) (x b) = boolBin d (y a) (y b) ∧ edge x ≠ edge y := by
  obtain ⟨x, y, same, xb, yb, xa, ya, different⟩ :=
    conditional_influence a b hab (decide (d = 1 ∨ d = 2))
  refine ⟨x, y, same, ?_, different⟩
  have hcases : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl <;> simp_all [boolBin]

end PEqualNP.Outside.L_meta_2373
