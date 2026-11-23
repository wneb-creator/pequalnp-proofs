namespace PEqualNP.Outside.L_meta_670_aux.FiniteCase159
open LiveCheck PEqualNP.CircuitLowerBounds
def case159State : List Sig := [raw0,raw1,raw2,raw3,raw4,raw5,raw6,raw7,raw8,(bin false raw2 raw0),(bin false raw3 raw1)]
def case159Codes : List Nat := [0x1,0x2,0x3,0x4,0x5,0x6,0x7,0x8,0x9,0xb31,0xb42]
def case159Hint (a : Sig) : Nat :=
  ((case159State.zip case159Codes).find? (fun p => p.1 == a)).getD (zero,0) |>.2
def case159Programs (i : Fin 12) : List Gate × List Nat :=
  match i.val with
  | 0 => ([⟨.and,[2,0]⟩,⟨.and,[3,1]⟩],[0,1,2,3,8,4,5,6,7,10,11])
  | 1 => ([⟨.and,[4,1]⟩,⟨.and,[7,0]⟩],[1,0,4,7,5,2,8,6,3,10,11])
  | 2 => ([⟨.and,[2,0]⟩,⟨.and,[4,1]⟩],[2,1,0,4,6,3,5,8,7,10,11])
  | 3 => ([⟨.and,[3,2]⟩],[8,3,0,2,8,6,4,5,1,8,10])
  | 4 => ([⟨.and,[3,2]⟩],[2,0,3,8,8,1,5,4,6,10,8])
  | 5 => ([⟨.and,[4,0]⟩,⟨.and,[5,3]⟩],[4,3,0,5,8,1,8,2,6,10,11])
  | 6 => ([⟨.and,[5,3]⟩,⟨.and,[6,0]⟩],[3,0,5,6,8,4,2,8,1,10,11])
  | 7 => ([⟨.and,[6,3]⟩],[3,8,6,1,4,0,8,5,2,10,8])
  | 8 => ([⟨.and,[1,0]⟩,⟨.and,[6,2]⟩],[0,2,1,6,5,3,8,4,8,10,11])
  | 9 => ([⟨.and,[4,0]⟩,⟨.and,[3,1]⟩],[0,3,4,1,2,5,8,8,6,10,11])
  | 10 => ([⟨.and,[6,3]⟩],[0,3,8,6,5,2,4,8,1,8,10])
  | _ => ([⟨.and,[3,2]⟩,⟨.and,[1,0]⟩],[3,0,2,1,4,8,5,8,6,10,11])


open DynamicLeaf

def context : DynamicCovered.CheckedContext ClosedDomains12.oracles case159State :=
  ⟨FastRecipe.initial ClosedDomains12.oracles CachedProjection.cachedRaw
      case159Hint case159State case159Programs,
    FastRecipe.initial_valid ClosedDomains12.oracles CachedProjection.cachedRaw
      case159Hint Cut12StrictReplay.rhoCorrect case159State case159Programs⟩

def proposals : List MemoChildren.Proposal := MemoChildren.proposals 13 2 case159State

def child (i : Nat) : MemoChildren.Proposal :=
  proposals.getD i ⟨0,[],.unary zero⟩

def check (i : Nat) : Bool :=
  ProjectedChild.check ClosedDomains12.oracles 12 context (child i)

def prefixCheck (i : Nat) : Bool :=
  ProjectedChild.prefixCheck ClosedDomains12.oracles 12 context (child i)

lemma check_sound (i : Nat) (h : check i = true) :
    Impossible 12 (child i).nots (child i).wires :=
  ProjectedChild.check_sound ClosedDomains12.oracles Cut12Certificate.oracleSound
    ProjectionDomains.project_target 12 context (child i) h

lemma prefixCheck_sound (i : Nat) (h : prefixCheck i = true) :
    Impossible 12 (child i).nots (child i).wires :=
  ProjectedChild.prefixCheck_sound ClosedDomains12.oracles Cut12Certificate.oracleSound
    ProjectionDomains.project_target 12 context (child i) h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma child_count : proposals.length = 59 := by decide +kernel

end PEqualNP.Outside.L_meta_670_aux.FiniteCase159
