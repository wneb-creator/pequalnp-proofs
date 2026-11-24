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
#eval freshCheck 11


def freshNodeCount : Nat → Nat → List LiveCheck.Sig → List Nat → Nat
  | 0,_,_,_ => 1
  | k+1,t,v,codes =>
      if FreshCodeSearch.cut ClosedDomains12.oracles CachedProjection.cachedRaw
          Cut12StrictReplay.programs (k+1) t v codes then 1 else
        1 + ((MemoChildren.proposals (k+1) t v).map fun p =>
          let unary := match p.move with
            | .unary _ => true
            | .binary _ _ _ => false
          freshNodeCount k p.nots p.wires
            (FreshCodeSearch.nextCodes unary v codes p.wires)).sum

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
#eval freshNodeCount 12 (child 11).nots (child 11).wires (freshCodes 11)

end PEqualNP.Outside.L_meta_670_aux.FiniteCase159
