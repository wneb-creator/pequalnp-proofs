import DirectReplay
import FastCofactorPools

namespace PEqualNP.Outside.L_meta_2373_aux.Cert18.FastDirectCofactorPools

open PEqualNP.Outside.L_meta_6581

/-- Direct replay with only the cofactor pool construction replaced. -/
def oracle (i : Replay.DirectMode.Node) : Nat → List Word → Choice → Bool :=
  preparedOracleFast
    (FastCofactorPools.poolList (Replay.DirectMode.state i) (Replay.BlockPools.hints i))
    (profilePairs (Replay.DirectMode.state i).live Replay.pairs)
    (prepareLinks Replay.DirectMode.state Replay.DirectMode.budget i
      (Replay.DirectMode.allLinks i))

set_option maxRecDepth 8192 in
lemma oracle_eq (i : Replay.DirectMode.Node) :
    oracle i = Replay.DirectMode.oracle i := by
  simp only [oracle, Replay.DirectMode.oracle, FastCofactorPools.poolList_eq]

def checkNode (i : Replay.DirectMode.Node) : Bool :=
  nodeCheckHalf Extended.target (oracle i)
    (Replay.DirectMode.budget i) (Replay.DirectMode.state i).live

set_option maxRecDepth 8192 in
lemma check_eq (i : Replay.DirectMode.Node) :
    checkNode i = Replay.DirectMode.checkNode i := by
  simp only [checkNode, Replay.DirectMode.checkNode, oracle_eq]

lemma closed (checked : ∀ i, checkNode i = true) :
    Impossible Extended.target 17 Extended.initial := by
  apply Replay.DirectMode.closed
  intro i
  exact (check_eq i).symm.trans (checked i)

end PEqualNP.Outside.L_meta_2373_aux.Cert18.FastDirectCofactorPools
