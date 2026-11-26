import BlockReplay
import DirectDecode

namespace PEqualNP.Outside.L_meta_2373_aux.Cert18.Replay.DirectMode
open PEqualNP.Outside.L_meta_6581

abbrev Node := Fin 5230

def state : Node → State := Direct.state

def budget (i : Node) : Nat := 17 - (state i).paidPrefix.length

def lowerParent (wanted : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | fuel+1, lo, hi => if lo < hi then
      let mid := (lo+hi)/2
      if Direct.parentAt mid < wanted then lowerParent wanted fuel (mid+1) hi
      else lowerParent wanted fuel lo mid
    else lo

def identityLinks (i : Node) : List (Link 5230) :=
  let first := lowerParent i.val 13 1 5230
  let last := lowerParent (i.val+1) 13 1 5230
  (List.range (last-first)).map fun j => (Fin.ofNat 5230 (first+j), [])

lemma identityLinks_valid (i : Node) :
    ∀ l ∈ identityLinks i, Automorphism.autoOK Extended.target l.2 = true := by
  intro l hl
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hl
  simp [Automorphism.autoOK,Automorphism.composedOK,Automorphism.movedWord]

def externalLinks (i : Node) : List (Link 5230) :=
  (explicitLinkIndices (state i).paidPrefix.length i.val).map fun l =>
    (Fin.ofNat 5230 l.1, autoMoves (Fin.ofNat 120 l.2))

def allLinks (i : Node) : List (Link 5230) := identityLinks i ++ externalLinks i

lemma allLinks_valid (i : Node) :
    ∀ l ∈ allLinks i, Automorphism.autoOK Extended.target l.2 = true := by
  intro l hl
  rcases List.mem_append.mp hl with hi | he
  · exact identityLinks_valid i l hi
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp he
    exact autoMoves_valid _

def oracle (i : Node) : Nat → List Word → Choice → Bool :=
  preparedOracleFast (poolList (state i) (BlockPools.hints i))
    (profilePairs (state i).live pairs) (prepareLinks state budget i (allLinks i))

lemma oracle_sound (i : Node)
    (earlier : ∀ j, budget j < budget i →
      Impossible Extended.target (budget j) (state j).live)
    {k ws op} (checked : oracle i k ws op = true) :
    Impossible Extended.target k ws := by
  exact preparedOracleFast_sound (fun _ hc => poolList_sound hc)
    (prepareLinks_sound (allLinks_valid i) earlier) checked

def checkNode (i : Node) : Bool :=
  nodeCheckHalf Extended.target (oracle i) (budget i) (state i).live

lemma closed (checked : ∀ i, checkNode i = true) :
    Impossible Extended.target 17 Extended.initial := by
  have go : ∀ b i, budget i = b → Impossible Extended.target (budget i) (state i).live := by
    intro b
    induction b using Nat.strong_induction_on with
    | ind b ih =>
      intro i hi
      apply nodeCheckHalf_sound (fun k ws op hc => oracle_sound i ?_ hc) (checked i)
      intro j hj
      exact ih (budget j) (by omega) j rfl
  exact go 17 0 rfl

end PEqualNP.Outside.L_meta_2373_aux.Cert18.Replay.DirectMode
