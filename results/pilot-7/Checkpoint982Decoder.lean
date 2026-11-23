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

def permute (k : Nat) (p : List Nat) (w : Nat) : Nat :=
  ((List.range (k+k)).map fun j =>
    w.testBit (if j < k then p.getD j 0 else k + p.getD (j-k) 0)).foldr Nat.bit 0

def move (mask : Nat) (ws : List Nat) (tag : Nat) : List Nat :=
  if tag < 48 then
    let i := tag / 4
    let a := ws.getD i 0
    [a ^^^ mask] ++ (if tag % 4 = 3 then [a] else []) ++ ws.take i ++ ws.drop (i+1)
  else
    let t := (tag-48) / 8
    let b := (List.range 16).foldl (fun old j => if j*(j+1)/2 ≤ t then j else old) 0
    let a := t - b*(b+1)/2
    let x := ws.getD a 0
    let y := ws.getD b 0
    let v := if (tag-48) / 4 % 2 = 1 then x &&& y else x ||| y
    [v] ++ (if (tag-48) / 2 % 2 = 1 then [x] else []) ++
      (if (tag-48) % 2 = 1 then [y] else []) ++
      (ws.zipIdx.filterMap fun (w,i) => if i = a ∨ i = b then none else some w)

def ins (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b::bs => if a ≤ b then a::b::bs else b::ins a bs

def state (k mask parentWidth tagWidth recipeWidth recipeBlock : Nat)
    (perms : Array (List Nat)) (upper : Nat → List Nat) (recipes : Array Nat) (i : Nat) :
    List Nat :=
  let code := getPacked recipeWidth recipeBlock recipes i
  let parent := code % 2 ^ parentWidth
  let tag := code / 2 ^ parentWidth % 2 ^ tagWidth
  let g := code / 2 ^ (parentWidth+tagWidth)
  let moved := move mask (upper parent) tag
  (if g = 0 then moved else moved.map (permute k (perms.getD g []))).foldr ins []

def advice (tagWidth symmetryWidth lengthWidth lengthBlock adviceWidth adviceBlock : Nat)
    (lengths data : Array Nat) (i : Nat) : Array Nat :=
  let count := getPacked lengthWidth lengthBlock lengths i
  let offset := ((List.range i).map (getPacked lengthWidth lengthBlock lengths)).sum
  ((List.range count).map fun j =>
    let v := getPacked adviceWidth adviceBlock data (offset+j)
    v % 2 ^ tagWidth + 1024*(1+(v/2 ^ tagWidth) % 2 ^ symmetryWidth+
      64*(v/2 ^ tagWidth/2 ^ symmetryWidth))).toArray

example : getPacked 4 8 #[0x1234] 2 = 2 := by decide
example : values 4 8 #[0x1234] 4 = [4,3,2,1] := by decide
example : generators 3 1 2 8 #[0x21] = #[[1,0,2]] := by decide
example : group 3 1 1 8 1 #[[1,0,2]] #[0] = #[[0,1,2],[1,0,2]] := by decide
example : permute 3 [1,0,2] 0x9 = 0x12 := by decide
example : move 15 [3,5,6] 56 = [7,6] := by decide
example : move 15 [3,5,6] 60 = [1,6] := by decide
example : move 15 [3,5,6] 63 = [1,3,5,6] := by decide
example : advice 10 1 3 8 14 2 #[0x21] #[0x2001402] 0 = #[133122] := by decide

end PEqualNP.Outside.L_meta_982_aux.Checkpoint
