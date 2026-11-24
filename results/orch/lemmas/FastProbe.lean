import Perf16Small

namespace PEqualNP.Outside.L_meta_1677_FastProbe
open PEqualNP.Outside.L_meta_1677

def fallbackFastAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  let z := choiceVal (movedChoice op a b)
  let ws := c.2.2.1
  if !properB z || ws.any (fun v => v.1==z) then true else
    let rest := (opKeep (op==2) ka kb a b ws).map Prod.fst
    c.2.2.2.2.2.2 (c.1-1) (z :: rest) ||
      closeChild c.2.2.2.2.1 c.2.2.2.2.2.1 (c.1-1) rest (movedChoice op a b)

theorem fallbackFast_sound {c i j op ka kb} (h : fallbackFastAt c i j op ka kb=true) :
    checkAt c i j op ka kb=true := by
  rcases c with ⟨cap,n,ws,cov,pools,links,extra⟩
  simp only [fallbackFastAt] at h
  simp only [checkAt,evalMove,moved_full]
  split_ifs <;> simp_all

end PEqualNP.Outside.L_meta_1677_FastProbe
