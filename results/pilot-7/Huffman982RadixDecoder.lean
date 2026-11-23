import Mathlib

namespace PEqualNP.Outside.L_meta_982_aux.Huffman

abbrev Table := Array (Array Nat)

def tableAt (data : Table) (i : Nat) : Nat :=
  ((data.getD (i/32) #[]).getD (i%32) 0)

def packedAt (width block : Nat) (data : Array Nat) (i : Nat) : Nat :=
  (data.getD (i / block) 0 / 2 ^ ((i % block) * width)) % 2 ^ width

def symbolAt (baseWidth block : Nat) (data : Table) (i : Nat) : Nat :=
  let c := tableAt data (i / block)
  let b := c % 2 ^ baseWidth
  let w := (c / 2 ^ baseWidth) % 32
  b + (c / 2 ^ (baseWidth+5+(i%block)*w)) % 2 ^ w

def readAux (starts counts bases : Array Nat) (baseWidth block : Nat)
    (symbols data : Table) : Nat → Nat → Nat → Nat → Nat × Nat
  | 0, _, _, pos => (0,pos)
  | fuel+1, length, old, pos =>
    let code := 2*old + tableAt data (pos/1024) / 2 ^ (pos%1024) % 2
    let start := starts.getD length 0
    let count := counts.getD length 0
    if start ≤ code ∧ code < start+count then
      (symbolAt baseWidth block symbols (bases.getD length 0+code-start), pos+1)
    else readAux starts counts bases baseWidth block symbols data fuel (length+1) code (pos+1)

def read (starts counts bases : Array Nat) (baseWidth block : Nat)
    (symbols data : Table) (pos : Nat) : Nat × Nat :=
  readAux starts counts bases baseWidth block symbols data 32 1 0 pos

def recordAux (delta tag : Table → Nat → Nat × Nat) (data : Table) :
    Nat → Nat → Nat → Nat → Nat × Nat
  | 0, _, parent, last => (parent,last)
  | n+1, pos, parent, _ =>
    let (d,pos') := delta data pos
    let (t,pos'') := tag data pos'
    let parent' := if d%2=0 then parent+d/2 else parent-(d/2+1)
    recordAux delta tag data n pos'' parent' t

def record (block offsetWidth offsetBlock : Nat) (offsets layerBase : Array Nat) (data : Table)
    (delta tag : Table → Nat → Nat × Nat) (s i : Nat) : Nat × Nat :=
  let pos := packedAt offsetWidth offsetBlock offsets (layerBase.getD s 0+i/block)
  recordAux delta tag data (i%block+1) pos 0 0

def readRecords (delta tag : Table → Nat → Nat × Nat) (data : Table) :
    Nat → Nat → Nat → List (Nat × Nat)
  | 0, _, _ => []
  | n+1, pos, parent =>
    let (d,pos') := delta data pos
    let (t,pos'') := tag data pos'
    let parent' := if d%2=0 then parent+d/2 else parent-(d/2+1)
    (parent',t) :: readRecords delta tag data n pos'' parent'

def recordBlock (block offsetWidth offsetBlock : Nat) (offsets layerBase : Array Nat) (data : Table)
    (delta tag : Table → Nat → Nat × Nat) (s b : Nat) : List (Nat × Nat) :=
  let pos := packedAt offsetWidth offsetBlock offsets (layerBase.getD s 0+b)
  readRecords delta tag data block pos 0

def recordFromBlocks (block : Nat) (blocks : Nat → Nat → List (Nat × Nat))
    (s i : Nat) : Nat × Nat :=
  (blocks s (i/block)).getD (i%block) (0,0)

end PEqualNP.Outside.L_meta_982_aux.Huffman
