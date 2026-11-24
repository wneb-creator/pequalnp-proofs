import Case159Combine
namespace PEqualNP.Outside.L_meta_670_aux.FiniteCase159
open LiveCheck DynamicLeaf

def context56 : DynamicCovered.CheckedContext ClosedDomains12.oracles (child 56).wires :=
  MetadataStrictEdges.childContext ClosedDomains12.oracles context (child 56)

def proposals56 : List MemoChildren.Proposal :=
  MemoChildren.proposals 12 (child 56).nots (child 56).wires

def grandchild (i : Nat) : MemoChildren.Proposal :=
  proposals56.getD i ⟨0,[],.unary zero⟩

def grandCheck (i : Nat) : Bool :=
  ProjectedChild.check ClosedDomains12.oracles 11 context56 (grandchild i)

def grandPrefixCheck (i : Nat) : Bool :=
  ProjectedChild.prefixCheck ClosedDomains12.oracles 11 context56 (grandchild i)

lemma grandCheck_sound (i : Nat) (h : grandCheck i = true) :
    Impossible 11 (grandchild i).nots (grandchild i).wires :=
  ProjectedChild.check_sound ClosedDomains12.oracles Cut12Certificate.oracleSound
    ProjectionDomains.project_target 11 context56 (grandchild i) h

lemma grandPrefixCheck_sound (i : Nat) (h : grandPrefixCheck i = true) :
    Impossible 11 (grandchild i).nots (grandchild i).wires :=
  ProjectedChild.prefixCheck_sound ClosedDomains12.oracles Cut12Certificate.oracleSound
    ProjectionDomains.project_target 11 context56 (grandchild i) h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma grandchild_count : proposals56.length = 44 := by decide +kernel

end PEqualNP.Outside.L_meta_670_aux.FiniteCase159
