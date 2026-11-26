import ArrayLookup

namespace PEqualNP.Outside.L_meta_2373_aux.Cert18.Replay.ArrayDataLookup
open PEqualNP.Outside.L_meta_6581

def poolDecode : Nat → Nat → Array (List Nat) → Array (List Nat)
  | 0, _, rows => rows
  | count + 1, data, rows =>
      let (kept, data) :=
        if data % 2 = 0 then ([], data / 2)
        else
          let (quotient, data) := BlockPools.poolUnary 64 (data / 2) 0
          let scale := 2 ^ BlockPools.poolDeltaRiceBits
          let distance := quotient * scale + data % scale + 1
          let data := data / scale
          let old := ArrayLookup.getD rows (rows.size - distance) []
          let scale := 2 ^ old.length
          (BlockPools.poolKeep old (data % scale), data / scale)
      let (addedCount, data) := BlockPools.poolUnary 32 data 0
      let (added, data) := BlockPools.poolSymbols addedCount data
      poolDecode count data (rows.push (kept ++ added))

lemma poolDecode_eq (count data : Nat) (rows : Array (List Nat)) :
    poolDecode count data rows = BlockPools.poolDecode count data rows := by
  induction count generalizing data rows with
  | zero => rfl
  | succ count ih =>
    simp only [poolDecode,BlockPools.poolDecode,ArrayLookup.getD_eq,ih]

def poolHintCodesAt (i : Nat) : List Nat :=
  let localIndex := i % BlockPools.poolBlockSize
  let data := ArrayLookup.getD BlockPools.poolBlockCodes (i / BlockPools.poolBlockSize) 0
  let rows := poolDecode (localIndex + 1) data #[]
  ArrayLookup.getD rows localIndex []

lemma poolHintCodesAt_eq (i : Nat) :
    poolHintCodesAt i = BlockPools.poolHintCodesAt i := by
  simp only [poolHintCodesAt,BlockPools.poolHintCodesAt,poolDecode_eq,ArrayLookup.getD_eq]

def hints (i : DirectMode.Node) : List PoolHint :=
  (poolHintCodesAt i.val).map hintOfCode

lemma hints_eq (i : DirectMode.Node) : hints i = BlockPools.hints i := by
  simp only [hints,BlockPools.hints,poolHintCodesAt_eq]

def stateCodeAt (i : Nat) : Nat :=
  let block := ArrayLookup.getD Direct.parentStateBlocks (i / 32) 0
  let parent := Direct.readStateParent (i % 32) (block &&& 8191) (block >>> 13)
  ((Direct.localStateCodes >>> (19 * i)) &&& 524287) ||| (parent <<< 19)

lemma stateCodeAt_eq (i : Nat) : stateCodeAt i = Direct.stateCodeAt i := by
  simp only [stateCodeAt,Direct.stateCodeAt,ArrayLookup.getD_eq]

lemma stateCodeAt_fun_eq : stateCodeAt = Direct.stateCodeAt := funext stateCodeAt_eq

def state (i : DirectMode.Node) : State := decodeStateBy stateCodeAt 9 i.val

lemma state_eq (i : DirectMode.Node) : state i = DirectMode.state i := by
  simp only [state,DirectMode.state,Direct.state,stateCodeAt_fun_eq]

lemma state_fun_eq : state = DirectMode.state := funext state_eq

def budget (i : DirectMode.Node) : Nat := 17 - (state i).paidPrefix.length

lemma budget_eq (i : DirectMode.Node) : budget i = DirectMode.budget i := by
  simp only [budget,DirectMode.budget,state_eq]

lemma budget_fun_eq : budget = DirectMode.budget := funext budget_eq

def parentAt (i : Nat) : Nat := stateCodeAt i >>> 19

lemma parentAt_eq (i : Nat) : parentAt i = Direct.parentAt i := by
  simp only [parentAt,Direct.parentAt,stateCodeAt_eq]

def lowerParent (wanted : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | fuel+1, lo, hi => if lo < hi then
      let mid := (lo+hi)/2
      if parentAt mid < wanted then lowerParent wanted fuel (mid+1) hi
      else lowerParent wanted fuel lo mid
    else lo

lemma lowerParent_eq (wanted fuel lo hi : Nat) :
    lowerParent wanted fuel lo hi = DirectMode.lowerParent wanted fuel lo hi := by
  induction fuel generalizing lo hi with
  | zero => rfl
  | succ fuel ih =>
    simp only [lowerParent,DirectMode.lowerParent,parentAt_eq,ih]

def identityLinks (i : DirectMode.Node) : List (Link 5230) :=
  let first := lowerParent i.val 13 1 5230
  let last := lowerParent (i.val+1) 13 1 5230
  (List.range (last-first)).map fun j => (Fin.ofNat 5230 (first+j), [])

lemma identityLinks_eq (i : DirectMode.Node) :
    identityLinks i = DirectMode.identityLinks i := by
  simp only [identityLinks,DirectMode.identityLinks,lowerParent_eq]

def externalLinks (i : DirectMode.Node) : List (Link 5230) :=
  (ArrayLookup.explicitLinkIndices (state i).paidPrefix.length i.val).map fun l =>
    (Fin.ofNat 5230 l.1, autoMoves (Fin.ofNat 120 l.2))

lemma externalLinks_eq (i : DirectMode.Node) :
    externalLinks i = DirectMode.externalLinks i := by
  simp only [externalLinks,DirectMode.externalLinks,ArrayLookup.explicitLinkIndices_eq,state_eq]

def allLinks (i : DirectMode.Node) : List (Link 5230) := identityLinks i ++ externalLinks i

lemma allLinks_eq (i : DirectMode.Node) : allLinks i = DirectMode.allLinks i := by
  simp only [allLinks,DirectMode.allLinks,identityLinks_eq,externalLinks_eq]

def oracle (i : DirectMode.Node) (k : Nat) (ws : List Word) (op : Choice) : Bool :=
  PackedCollision.checkCached PackedRows.positive PackedRows.negative
      (PackedRows.cache stateCodeAt 9 i.val) ws op ||
    (FastCofactorPools.poolList (state i) (hints i)).any
      (fun c => cutCheckFast c k ws op) ||
    preparedLinkCheckFast (prepareLinks state budget i (allLinks i)) k ws

lemma oracle_eq (i : DirectMode.Node) : oracle i = DirectMode.Packed.oracle i := by
  funext k ws op
  simp only [oracle,DirectMode.Packed.oracle,stateCodeAt_fun_eq,state_fun_eq,
    budget_fun_eq,hints_eq,allLinks_eq]

def checkNode (i : DirectMode.Node) : Bool :=
  nodeCheckHalf Extended.target (oracle i) (budget i) (state i).live

lemma checkNode_eq (i : DirectMode.Node) :
    checkNode i = DirectMode.Packed.checkNode i := by
  simp only [checkNode,DirectMode.Packed.checkNode,oracle_eq,budget_eq,state_eq]

lemma closed (checked : ∀ i, checkNode i = true) :
    Impossible Extended.target 17 Extended.initial := by
  apply DirectMode.Packed.closed
  intro i
  exact (checkNode_eq i).symm.trans (checked i)

end PEqualNP.Outside.L_meta_2373_aux.Cert18.Replay.ArrayDataLookup
