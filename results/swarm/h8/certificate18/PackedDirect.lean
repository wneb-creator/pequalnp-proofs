import PackedRows
import FastDirect

namespace PEqualNP.Outside.L_meta_2373_aux.Cert18.Replay.DirectMode.Packed
open PEqualNP.Outside.L_meta_6581

def oracle (i : Node) (k : Nat) (ws : List Word) (op : Choice) : Bool :=
  PackedCollision.checkCached PackedRows.positive PackedRows.negative
      (PackedRows.cache Direct.stateCodeAt 9 i.val) ws op ||
    (FastCofactorPools.poolList (state i) (BlockPools.hints i)).any
      (fun c => cutCheckFast c k ws op) ||
    preparedLinkCheckFast (prepareLinks state budget i (allLinks i)) k ws

lemma oracle_sound (i : Node)
    (earlier : ∀ j, budget j < budget i →
      Impossible Extended.target (budget j) (state j).live)
    {k ws op} (checked : oracle i k ws op = true) :
    Impossible Extended.target k ws := by
  simp only [oracle,Bool.or_eq_true,List.any_eq_true] at checked
  rcases checked with (collision | ⟨c,hc,cut⟩) | link
  · exact PackedCollision.checkCached_sound PackedRows.target_different
      (PackedRows.cache_valid Direct.stateCodeAt 9 i.val) collision k
  · rw [cutCheckFast_eq] at cut
    rw [FastCofactorPools.poolList_eq] at hc
    exact Projection.cutCheck_sound (poolList_sound hc) cut
  · exact preparedLinkCheckFast_sound
      (prepareLinks_sound (allLinks_valid i) earlier) link

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

end PEqualNP.Outside.L_meta_2373_aux.Cert18.Replay.DirectMode.Packed
