import OrbitLookup982
namespace PEqualNP.Outside.L_meta_982_aux.Finite.Reduced

def lexCmp : List Nat → List Nat → Ordering
  | [],[] => .eq
  | [],_::_ => .lt
  | _::_,[] => .gt
  | a::as,b::bs => if a == b then lexCmp as bs else if a < b then .lt else .gt

def binarySeek (S : Nat → List Nat) (bound : Nat) (key : List Nat) :
    Nat → Nat → Nat → Nat
  | 0,_,_ => bound
  | fuel+1,lo,hi =>
    if lo < hi then
      let mid := (lo+hi)/2
      match lexCmp key (S mid) with
      | .eq => mid
      | .lt => binarySeek S bound key fuel lo mid
      | .gt => binarySeek S bound key fuel (mid+1) hi
    else bound

def binaryInsert (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b::bs => if a ≤ b then a::b::bs else b::binaryInsert a bs

def binarySort : List Nat → List Nat
  | [] => []
  | a::as => binaryInsert a (binarySort as)

def binaryFind (S : Nat → List Nat) (bound : Nat) (ys : List Nat) : Nat :=
  binarySeek S bound (binarySort ys) (bound+1) 0 bound

def binaryOrbitHint (S : Nat → Nat → List Nat) (N : Nat → Nat)
    (acts : List (List Nat → List Nat)) (p _i _tag : Nat) (ys : List Nat) : Nat × List Nat :=
  orbitLookup (binaryFind (S (p-1)) (N (p-1))) (S (p-1)) (N (p-1)) ys acts

theorem binaryOrbitHint_run {forbidden m y S N acts}
    (ha : ∀ a ∈ acts, ∀ {t ys}, RNatRun forbidden m y t ys → RNatRun forbidden m y t (a ys))
    (p i tag : Nat) {t ys} (h : RNatRun forbidden m y t ys) :
    RNatRun forbidden m y t (binaryOrbitHint S N acts p i tag ys).2 := by
  exact orbitLookup_run _ _ _ _ h (fun a hmem => ha a hmem h)

example : binaryFind (fun i => [[1,2],[1,3],[2,3]].getD i []) 3 [3,1] = 1 := by decide +kernel
example : binaryFind (fun i => [[1,2],[1,3],[2,3]].getD i []) 3 [1,4] = 3 := by decide +kernel
example : binaryFind (fun _ => []) 0 [1] = 0 := by decide +kernel

end PEqualNP.Outside.L_meta_982_aux.Finite.Reduced
