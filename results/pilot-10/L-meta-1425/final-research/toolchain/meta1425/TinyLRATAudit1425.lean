import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1425.Cert

theorem tiny : ∀ (a b : Prop), (¬a ∧ ¬b ∨ a ∧ ¬b) ∨ ¬a ∧ b ∨ a ∧ b := from_lrat
  (String.ofList (List.map Char.ofNat [112, 32, 99, 110, 102, 32, 50, 32, 52, 10, 49, 32, 50, 32, 48, 10, 45, 49, 32, 50, 32, 48, 10, 49, 32, 45, 50, 32, 48, 10, 45, 49, 32, 45, 50, 32, 48, 10]))
  (String.ofList (List.map Char.ofNat [53, 32, 45, 50, 32, 48, 32, 52, 32, 51, 32, 48, 10, 54, 32, 49, 32, 48, 32, 53, 32, 49, 32, 48, 10, 55, 32, 48, 32, 53, 32, 50, 32, 54, 32, 48, 10]))

end PEqualNP.Outside.L_meta_1425.Cert

#print axioms PEqualNP.Outside.L_meta_1425.Cert.tiny
#check PEqualNP.Outside.L_meta_1425.Cert.tiny
