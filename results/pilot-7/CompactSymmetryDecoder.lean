import Mathlib

namespace PEqualNP.Outside.L_meta_982_aux.Checkpoint

def getPacked (width block : Nat) (data : Array Nat) (i : Nat) : Nat :=
  (data.getD (i / block) 0 >>> ((i % block) * width)) % 2 ^ width

def values (width block : Nat) (data : Array Nat) (count : Nat) : List Nat :=
  (List.range count).map (getPacked width block data)

def generators (k count width block : Nat) (data : Array Nat) : Array (List Nat) :=
  ((List.range count).map fun g =>
    (List.range k).map fun j => getPacked width block data (g*k+j)).toArray

def group (k parentWidth recipeWidth recipeBlock count : Nat)
    (gens : Array (List Nat)) (recipes : Array Nat) : Array (List Nat) :=
  (List.range count).foldl (fun acc i =>
    let code := getPacked recipeWidth recipeBlock recipes i
    let old := acc.getD (code % 2 ^ parentWidth) []
    let gen := gens.getD (code / 2 ^ parentWidth) []
    acc.push (gen.map (old.getD · 0))) #[(List.range k)]

def actions (refWidth refBlock count : Nat) (refs : Array Nat)
    (gs : Array (List Nat)) : Array (List Nat) :=
  ((List.range count).map fun i => gs.getD (getPacked refWidth refBlock refs i) []).toArray

end PEqualNP.Outside.L_meta_982_aux.Checkpoint
