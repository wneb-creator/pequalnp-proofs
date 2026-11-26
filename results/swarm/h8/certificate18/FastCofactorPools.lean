import CheckNode

namespace PEqualNP.Outside.L_meta_2373_aux.Cert18.FastCofactorPools

open PEqualNP.Outside.L_meta_6581

/-- Use the already certified pin lookup for coordinate masks. -/
def fastLiftWord (v : Fin 10) (a : Sig) : Word :=
  Automorphism.movedWord
    (Automorphism.fastSwapWords (Cofactor.cofactorSwaps v)) (Cofactor.doubleWord a)

lemma fastLiftWord_eq (v : Fin 10) (a : Sig) :
    fastLiftWord v a = Cofactor.fastLiftWord v a := by
  simp only [fastLiftWord, Cofactor.fastLiftWord, Automorphism.fastSwapWords_eq]

def liftDomain (v : Fin 10) (a : Sig) : Word :=
  fastLiftWord v a &&& ~~~(Extended.pins.getD v.val Extended.zero)

lemma liftDomain_eq (v : Fin 10) (a : Sig) :
    liftDomain v a = Cofactor.liftDomain v a := by
  simp only [liftDomain, Cofactor.liftDomain, Cofactor.liftWord, fastLiftWord_eq]

def source (v : Fin 10) (j : Fin 216) : Word × Nat :=
  if h : j.val < 215 then
    let c := Cofactor.column ⟨j.val, h⟩
    (liftDomain v (subcube c.1 c.2.1), c.2.2.2.2)
  else (liftDomain v one, 15)

lemma source_eq (v : Fin 10) (j : Fin 216) :
    source v j = Cofactor.source v j := by
  simp only [source, Cofactor.source, liftDomain_eq]

def hintPool (st : State) (h : PoolHint) : Option Projection.BoundPool :=
  let s := source h.1.1 h.1.2
  Projection.materialize true Extended.initial (selectedPrefix st h.2) s.1 s.2

lemma hintPool_eq (st : State) (h : PoolHint) :
    hintPool st h = PEqualNP.Outside.L_meta_2373_aux.Cert18.hintPool st h := by
  simp only [hintPool, PEqualNP.Outside.L_meta_2373_aux.Cert18.hintPool, source_eq]

def poolList (st : State) (hs : List PoolHint) : List Projection.BoundPool :=
  hs.filterMap (hintPool st)

set_option maxRecDepth 8192 in
lemma poolList_eq (st : State) (hs : List PoolHint) :
    poolList st hs = PEqualNP.Outside.L_meta_2373_aux.Cert18.poolList st hs := by
  unfold poolList PEqualNP.Outside.L_meta_2373_aux.Cert18.poolList
  congr 1
  funext h
  exact hintPool_eq st h

def oracleOf (hints : Replay.Node → List PoolHint) (i : Replay.Node) :
    Nat → List Word → Choice → Bool :=
  preparedOracleFast (poolList (Replay.state i) (hints i))
    (profilePairs (Replay.state i).live Replay.pairs)
    (prepareLinks Replay.state Replay.budget i (Replay.allLinks i))

lemma oracleOf_eq (hints : Replay.Node → List PoolHint) (i : Replay.Node) :
    oracleOf hints i = Replay.oracleOf hints i := by
  simp only [oracleOf, Replay.oracleOf, poolList_eq]

/-- Identical to the original prefix checker, using the faster cofactor masks. -/
def check (i : Replay.Node) : Bool :=
  nodeCheckHalf Extended.target (oracleOf Replay.hintsPrefix i)
    (Replay.budget i) (Replay.state i).live

lemma check_eq (i : Replay.Node) : check i = Replay.checkNodePrefix i := by
  simp only [check, Replay.checkNodePrefix, oracleOf_eq]

lemma closed (checked : ∀ i, check i = true) :
    Impossible Extended.target 17 Extended.initial := by
  apply Replay.closedPrefix
  intro i
  exact (check_eq i).symm.trans (checked i)

end PEqualNP.Outside.L_meta_2373_aux.Cert18.FastCofactorPools
