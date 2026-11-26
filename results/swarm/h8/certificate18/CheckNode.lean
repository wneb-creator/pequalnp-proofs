import Replay
namespace PEqualNP.Outside.L_meta_2373_aux.Cert18.Replay
def checkNode (i : Node) : Bool := check i
def hintsPrefix (i : Node) : List PoolHint :=
  (((poolDecode (i.val+1) poolDeltaStream #[])[i.val]?).getD []).map hintOfCode

def checkNodePrefix (i : Node) : Bool :=
  nodeCheckHalf PEqualNP.Outside.L_meta_6581.Extended.target
    (oracleOf hintsPrefix i) (budget i) (state i).live

lemma closedPrefix (checked : ∀ i, checkNodePrefix i = true) :
    Impossible PEqualNP.Outside.L_meta_6581.Extended.target 17
      PEqualNP.Outside.L_meta_6581.Extended.initial := closedOf hintsPrefix checked

end PEqualNP.Outside.L_meta_2373_aux.Cert18.Replay
