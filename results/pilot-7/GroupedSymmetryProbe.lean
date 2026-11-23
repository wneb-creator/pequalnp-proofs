import LinearSymmetryData26
import RadixSymmetry
namespace PEqualNP.Outside.L_meta_982_aux.Finite.Symmetry.GroupedProbe

def split (bit : Nat) (p : List (Nat × Nat)) : List (Nat × Nat) :=
  p.filter (fun j => !(Fast.bit j.1 bit)) ++ p.filter (fun j => Fast.bit j.1 bit)
def sort : Nat → List (Nat × Nat) → List (Nat × Nat)
  | 0,p => p
  | b+1,p => split b (sort b p)
def merge : List (Nat × Nat) → List (Nat × Nat)
  | [] => []
  | (d,m)::xs =>
      match merge xs with
      | [] => [(d,m)]
      | (e,n)::ys => if d=e then (d,m|||n)::ys else (d,m)::(e,n)::ys

def ops (bits width : Nat) (p : List Nat) : List (Nat × Nat) :=
  merge (sort bits (p.zipIdx.map (fun (s,j) => (width+s-j,2^j))))

def fast (bits width : Nat) (p : List Nat) (x : Nat) : Nat :=
  (ops bits width p).foldr (fun (d,m) y => (((x/2^(d-width))*2^(width-d)) &&& m) ||| y)
    ((x / 2^width)*2^width)
end PEqualNP.Outside.L_meta_982_aux.Finite.Symmetry.GroupedProbe
