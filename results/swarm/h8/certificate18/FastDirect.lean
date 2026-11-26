import DirectReplay
import FastCofactorPools
import CollisionProfiles

namespace PEqualNP.Outside.L_meta_2373_aux.Cert18.Replay.DirectMode.Fast
open PEqualNP.Outside.L_meta_6581

def oracle (i : Node) : Nat → List Word → Choice → Bool :=
  preparedOracleFast (FastCofactorPools.poolList (state i) (BlockPools.hints i))
    (profilePairs (state i).live pairs) (prepareLinks state budget i (allLinks i))

lemma oracle_eq (i : Node) : oracle i = DirectMode.oracle i := by
  simp only [oracle,DirectMode.oracle,FastCofactorPools.poolList_eq]

def checkNode (i : Node) : Bool :=
  nodeCheckHalf Extended.target (oracle i) (budget i) (state i).live

lemma checkNode_eq (i : Node) : checkNode i = DirectMode.checkNode i := by
  simp only [checkNode,DirectMode.checkNode,oracle_eq]

lemma closed (checked : ∀ i, checkNode i = true) :
    Impossible Extended.target 17 Extended.initial := by
  apply DirectMode.closed
  intro i
  exact (checkNode_eq i).symm.trans (checked i)

def profileOracle (i : Node) : Nat → List Word → Choice → Bool :=
  preparedOracleProfile (state i).live
    (FastCofactorPools.poolList (state i) (BlockPools.hints i))
    (profilePairs (state i).live pairs) (prepareLinks state budget i (allLinks i))

lemma profileOracle_sound (i : Node)
    (earlier : ∀ j, budget j < budget i →
      Impossible Extended.target (budget j) (state j).live)
    {k ws op} (checked : profileOracle i k ws op = true) :
    Impossible Extended.target k ws := by
  apply preparedOracleProfile_sound ?_ (prepareLinks_sound (allLinks_valid i) earlier) checked
  intro c hc
  rw [FastCofactorPools.poolList_eq] at hc
  exact poolList_sound hc

def profileCheckNode (i : Node) : Bool :=
  nodeCheckHalf Extended.target (profileOracle i) (budget i) (state i).live

lemma profileClosed (checked : ∀ i, profileCheckNode i = true) :
    Impossible Extended.target 17 Extended.initial := by
  have go : ∀ b i, budget i = b → Impossible Extended.target (budget i) (state i).live := by
    intro b
    induction b using Nat.strong_induction_on with
    | ind b ih =>
      intro i hi
      apply nodeCheckHalf_sound (fun k ws op hc => profileOracle_sound i ?_ hc) (checked i)
      intro j hj
      exact ih (budget j) (by omega) j rfl
  exact go 17 0 rfl

end PEqualNP.Outside.L_meta_2373_aux.Cert18.Replay.DirectMode.Fast
