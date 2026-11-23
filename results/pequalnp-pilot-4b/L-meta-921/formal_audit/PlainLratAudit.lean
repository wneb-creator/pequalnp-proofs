import Mathlib.Tactic.Sat.FromLRAT

namespace Meta921Audit.CheckedPlain

def cnf : String := String.ofList ([112, 32, 99, 110, 102, 32, 50, 32, 52, 10, 49, 32, 50, 32, 48, 10, 45, 49, 32, 50, 32, 48, 10, 49, 32, 45, 50, 32, 48, 10, 45, 49, 32, 45, 50, 32, 48, 10].map Char.ofNat)

def certificate : String := String.ofList ([53, 32, 45, 50, 32, 48, 32, 51, 32, 52, 32, 48, 10, 54, 32, 49, 32, 48, 32, 53, 32, 49, 32, 48, 10, 55, 32, 48, 32, 54, 32, 53, 32, 50, 32, 48, 10].map Char.ofNat)

lemma checked : ∀ (a b : Prop), (¬a ∧ ¬b ∨ a ∧ ¬b) ∨ ¬a ∧ b ∨ a ∧ b :=
  from_lrat cnf certificate

end Meta921Audit.CheckedPlain

#print axioms Meta921Audit.CheckedPlain.checked
