import PackedDirect

namespace PEqualNP.Outside.L_meta_2373_aux.Cert18.Replay.ArrayLookup
open PEqualNP.Outside.L_meta_6581

def getD {α : Type} (a : Array α) (i : Nat) (fallback : α) : α :=
  a.toList.getD i fallback

lemma getD_eq {α : Type} (a : Array α) (i : Nat) (fallback : α) :
    getD a i fallback = a[i]?.getD fallback := by
  simp only [getD,List.getD_eq_getElem?_getD,Array.getElem?_toList]

def explicitLinkIndices (depth node : Nat) : List (Nat × Nat) :=
  let n := getD linkCodes node 0
  readLinks (n &&& 63) (getD linkLevelStarts (depth + 1) 0) (n >>> 6)

lemma explicitLinkIndices_eq (depth node : Nat) :
    explicitLinkIndices depth node = Replay.explicitLinkIndices depth node := by
  simp only [explicitLinkIndices,Replay.explicitLinkIndices,getD_eq]

def externalLinks (i : DirectMode.Node) : List (Link 5230) :=
  (explicitLinkIndices (DirectMode.state i).paidPrefix.length i.val).map fun l =>
    (Fin.ofNat 5230 l.1, autoMoves (Fin.ofNat 120 l.2))

lemma externalLinks_eq (i : DirectMode.Node) :
    externalLinks i = DirectMode.externalLinks i := by
  simp only [externalLinks,DirectMode.externalLinks,explicitLinkIndices_eq]

def allLinks (i : DirectMode.Node) : List (Link 5230) :=
  DirectMode.identityLinks i ++ externalLinks i

lemma allLinks_eq (i : DirectMode.Node) :
    allLinks i = DirectMode.allLinks i := by
  simp only [allLinks,DirectMode.allLinks,externalLinks_eq]

def oracle (i : DirectMode.Node) (k : Nat) (ws : List Word) (op : Choice) : Bool :=
  PackedCollision.checkCached PackedRows.positive PackedRows.negative
      (PackedRows.cache Direct.stateCodeAt 9 i.val) ws op ||
    (FastCofactorPools.poolList (DirectMode.state i) (BlockPools.hints i)).any
      (fun c => cutCheckFast c k ws op) ||
    preparedLinkCheckFast
      (prepareLinks DirectMode.state DirectMode.budget i (allLinks i)) k ws

lemma oracle_eq (i : DirectMode.Node) : oracle i = DirectMode.Packed.oracle i := by
  funext k ws op
  simp only [oracle,DirectMode.Packed.oracle,allLinks_eq]

def checkNode (i : DirectMode.Node) : Bool :=
  nodeCheckHalf Extended.target (oracle i) (DirectMode.budget i) (DirectMode.state i).live

lemma checkNode_eq (i : DirectMode.Node) :
    checkNode i = DirectMode.Packed.checkNode i := by
  simp only [checkNode,DirectMode.Packed.checkNode,oracle_eq]

lemma closed (checked : ∀ i, checkNode i = true) :
    Impossible Extended.target 17 Extended.initial := by
  apply DirectMode.Packed.closed
  intro i
  exact (checkNode_eq i).symm.trans (checked i)

end PEqualNP.Outside.L_meta_2373_aux.Cert18.Replay.ArrayLookup
