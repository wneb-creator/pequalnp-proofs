import FiniteProofTreeTest

namespace PEqualNP.Outside.L_meta_670_aux.FiniteProofTree

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma child11_closed : Closed ClosedDomains12.oracles 12
    (FiniteCase159.child 11).nots (FiniteCase159.child 11).wires
    (MetadataStrictEdges.childContext ClosedDomains12.oracles
      FiniteCase159.context (FiniteCase159.child 11)) := by
  repeat'
    first
    | (apply of_prefix ClosedDomains12.oracles Cut12Certificate.oracleSound
        ProjectionDomains.project_target
       decide +kernel)
    | (apply of_children ClosedDomains12.oracles
       case parent => decide +kernel
       intro i
       fin_cases i)

#print axioms child11_closed
end PEqualNP.Outside.L_meta_670_aux.FiniteProofTree
