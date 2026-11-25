import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1896_aux.PackingData

abbrev Block := Nat × Nat × Nat
abbrev State := Nat × Nat × Nat × Nat

def ok (s : State) (b : Block) : Bool :=
  ((s.2.1 &&& b.1) == 0) && ((s.2.2.2 &&& b.2.1) == 0)

def step (s : State) (b : Block) : State :=
  (s.1 + b.2.2, s.2.1 ||| b.1, s.2.2.1 ||| b.2.1,
    s.2.2.2 ||| (s.2.2.1 &&& b.2.1))

def good (s : State) : Bool := decide (s.1 ≤ 7)

lemma and_zero_of_or_left (a b c : Nat) (h : (a ||| b) &&& c = 0) : a &&& c = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hi := congrArg (fun n : Nat => n.testBit i) h
  rw [Nat.testBit_land, Nat.testBit_lor] at hi
  rw [Nat.testBit_land]
  cases ha : a.testBit i <;> cases hc : c.testBit i <;> simp_all

lemma ok_antitone : ∀ (s : State) (b c : Block), ok (step s b) c = true → ok s c = true := by
  intro s b c h
  simp only [ok, step, Bool.and_eq_true, beq_iff_eq] at h ⊢
  exact ⟨and_zero_of_or_left _ _ _ h.1, and_zero_of_or_left _ _ _ h.2⟩

end PEqualNP.Outside.L_meta_1896_aux.PackingData
