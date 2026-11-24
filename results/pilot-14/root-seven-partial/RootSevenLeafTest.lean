import RootSevenBase
namespace PEqualNP.Outside.L_meta_670_aux.RootSevenLeaf

open LiveCheck

def row (i : Nat) : Nat := RootSeven.nodes12.getD i 0

def state (i : Nat) : List Sig := Cut12StrictReplay.state 12 4 (row i)

def context (i : Nat) : DynamicCovered.CheckedContext ClosedDomains12.oracles (state i) :=
  Cut12StrictReplay.initial 12 4 (row i)

def proposals (i : Nat) : List MemoChildren.Proposal := MemoChildren.proposals 12 4 (state i)

def child (i j : Nat) : MemoChildren.Proposal := (proposals i).getD j ⟨0,[],.unary zero⟩

def check (i j : Nat) : Bool :=
  ProjectedChild.check ClosedDomains12.oracles 11 (context i) (child i j)

def prefixCheck (i j : Nat) : Bool :=
  ProjectedChild.prefixCheck ClosedDomains12.oracles 11 (context i) (child i j)

lemma check_sound (i j : Nat) (h : check i j = true) :
    Impossible 11 (child i j).nots (child i j).wires :=
  ProjectedChild.check_sound ClosedDomains12.oracles Cut12Certificate.oracleSound
    ProjectionDomains.project_target 11 (context i) (child i j) h

lemma prefixCheck_sound (i j : Nat) (h : prefixCheck i j = true) :
    Impossible 11 (child i j).nots (child i j).wires :=
  ProjectedChild.prefixCheck_sound ClosedDomains12.oracles Cut12Certificate.oracleSound
    ProjectionDomains.project_target 11 (context i) (child i j) h

lemma excluded (i : Nat)
    (hc : ∀ j : Fin (proposals i).length, Impossible 11
      ((proposals i)[j.val]).nots ((proposals i)[j.val]).wires)
    (h : ProjectedChild.parentCheck 11 4 (state i) = true) : Impossible 12 4 (state i) :=
  ProjectedChild.parentCheck_fin_sound hc h

end PEqualNP.Outside.L_meta_670_aux.RootSevenLeaf
