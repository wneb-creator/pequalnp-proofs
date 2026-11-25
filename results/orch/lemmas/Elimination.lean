import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bitwise

namespace PEqualNP.Outside.L_meta_2592_aux.ProfileCheck

def key (m : Nat) : Nat := min m (Nat.xor m 127)

def seeds : List Nat := [0, 2, 4, 8, 16, 32, 63]

def targets : List Nat := [15, 22, 42, 51]

def extras : List Nat := (List.range 64).filter fun a =>
  !(seeds.contains a || targets.contains a)

def canMake (known : List Nat) (z : Nat) : Bool :=
  known.any fun a => known.any fun b =>
    key (Nat.land a b) == z ||
    key (Nat.land a (Nat.xor b 127)) == z ||
    key (Nat.land (Nat.xor a 127) b) == z ||
    key (Nat.land (Nat.xor a 127) (Nat.xor b 127)) == z

def extend (candidates known : List Nat) : List Nat :=
  candidates.foldl (fun seen z =>
    if seen.contains z then seen
    else if canMake seen z then z :: seen
    else seen) known

def closure (a b c : Nat) : List Nat :=
  (List.range 7).foldl (fun seen _ => extend (targets ++ [a,b,c]) seen) seeds

def missing (a b c : Nat) : Bool :=
  let seen := closure a b c
  (seeds.all fun t => seen.contains t) &&
  ((targets ++ [a,b,c]).all fun t => !(canMake seen t) || seen.contains t) &&
  !(targets.all fun t => seen.contains t)

def checked : Bool :=
  extras.all fun a => extras.all fun b =>
    !(decide (a < b)) || extras.all fun c => !(decide (b < c)) || missing a b c

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma no_three_helpers : checked = true := by
  decide +kernel

end PEqualNP.Outside.L_meta_2592_aux.ProfileCheck
