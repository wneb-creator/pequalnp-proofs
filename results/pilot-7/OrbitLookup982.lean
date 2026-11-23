import Indexed982
namespace PEqualNP.Outside.L_meta_982_aux.Finite.Reduced

def orbitLookup (find : List Nat → Nat) (S : Nat → List Nat) (bound : Nat)
    (ys : List Nat) : List (List Nat → List Nat) → Nat × List Nat
  | [] => (find ys,ys)
  | a::acts =>
    let zs := a ys
    let i := find zs
    if decide (i < bound) && zs.isPerm (S i) then (i,zs)
    else orbitLookup find S bound ys acts

theorem orbitLookup_run {forbidden m y t ys} (find : List Nat → Nat)
    (S : Nat → List Nat) (bound : Nat) (acts : List (List Nat → List Nat))
    (h : RNatRun forbidden m y t ys)
    (ha : ∀ a ∈ acts, RNatRun forbidden m y t (a ys)) :
    RNatRun forbidden m y t (orbitLookup find S bound ys acts).2 := by
  induction acts with
  | nil => exact h
  | cons a acts ih =>
    simp only [orbitLookup]
    split
    · exact ha a List.mem_cons_self
    · exact ih (fun b hb => ha b (List.mem_cons_of_mem a hb))

end PEqualNP.Outside.L_meta_982_aux.Finite.Reduced
