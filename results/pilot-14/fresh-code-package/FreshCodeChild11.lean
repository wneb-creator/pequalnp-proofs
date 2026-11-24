import Case159Common
import FreshCodeSearchTest

namespace PEqualNP.Outside.L_meta_670_aux.FiniteCase159

def freshCodes (i : Nat) : List Nat :=
  (child i).wires.map (MetadataStrictEdges.childHint case159Hint (child i))

def freshCheck (i : Nat) : Bool :=
  FreshCodeSearch.leafCheck ClosedDomains12.oracles CachedProjection.cachedRaw
    Cut12StrictReplay.programs 12 (child i).nots (child i).wires (freshCodes i)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma freshChild11_checked : freshCheck 11 = true := by decide +kernel

lemma freshChild11_excluded :
    LiveCheck.Impossible 12 (child 11).nots (child 11).wires :=
  FreshCodeSearch.leafCheck_sound ClosedDomains12.oracles Cut12Certificate.oracleSound
    ProjectionDomains.project_target CachedProjection.cachedRaw Cut12StrictReplay.programs
    Cut12StrictReplay.rhoCorrect freshChild11_checked

end PEqualNP.Outside.L_meta_670_aux.FiniteCase159
