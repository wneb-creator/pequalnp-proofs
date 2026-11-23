namespace PEqualNP.Outside.L_meta_670_aux.MetadataStrictEdges

open LiveCheck DynamicLeaf

def codeLength : Nat → Nat → Nat
  | 0, _ => 0
  | fuel+1, code => if code = 0 then 0 else 1+codeLength fuel (code >>> 4)

def appendCode (a b : Nat) : Nat := a + (b <<< (4*codeLength 31 a))

def moveCode (hint : Sig → Nat) : MemoChildren.Move → Nat
  | .unary a => appendCode (hint a) 10
  | .binary d a b => appendCode (appendCode (hint a) (hint b)) (if d then 12 else 11)

def childHint (hint : Sig → Nat) (p : MemoChildren.Proposal) (a : Sig) : Nat :=
  if a == p.move.value then moveCode hint p.move else hint a

def listHint (v : List Sig) (codes : List Nat) (a : Sig) : Nat :=
  codes.getD (v.idxOf a) 0

def childContext {n : Nat} (oracles : Fin n → Oracle) {v : List Sig}
    (c : DynamicCovered.CheckedContext oracles v) (p : MemoChildren.Proposal) :
    DynamicCovered.CheckedContext oracles p.wires :=
  ⟨StrictPrefix.updateWithRecipe oracles v p.wires c.val (some (DynamicCovered.recipe p.move)),
    @StrictPrefix.updateWithRecipe_valid n oracles v c.val c.property p.wires
      (some (DynamicCovered.recipe p.move))⟩

def edge {n : Nat} (oracles : Fin n → Oracle) (hint : Sig → Nat) (k : Nat)
    {v : List Sig} (c : DynamicCovered.CheckedContext oracles v)
    (p : MemoChildren.Proposal) : MetadataReplay.Edge :=
  ⟨p.nots,p.wires,childHint hint p,
    BoolNodup.check p.wires && DynamicCovered.cut oracles k p.nots p.wires
      (childContext oracles c p)⟩

lemma edge_cut_sound {n : Nat} (oracles : Fin n → Oracle)
    (hsound : ∀ i, (oracles i).Sound)
    (htarget : ∀ i, (oracles i).project target = Base1007.target)
    (hint : Sig → Nat) (k : Nat) {v : List Sig}
    (c : DynamicCovered.CheckedContext oracles v) (p : MemoChildren.Proposal)
    (h : (edge oracles hint k c p).cut = true) : Impossible k p.nots p.wires := by
  simp only [edge,Bool.and_eq_true] at h
  exact DynamicCovered.cut_sound oracles hsound htarget k p.nots p.wires
    (childContext oracles c p) (BoolNodup.sound h.1) h.2

def edges {n : Nat} (oracles : Fin n → Oracle)
    (state : Nat → Nat → Nat → List Sig)
    (initial : (k t j : Nat) → DynamicCovered.CheckedContext oracles (state k t j))
    (hint : Nat → Nat → Nat → Sig → Nat) : Nat → Nat → Nat → List MetadataReplay.Edge
  | 0,_,_ => []
  | k+1,t,j =>
    (MemoChildren.proposals (k+1) t (state (k+1) t j)).map
      (edge oracles (hint (k+1) t j) k (initial (k+1) t j))

lemma edges_cut_sound {n : Nat} (oracles : Fin n → Oracle)
    (hsound : ∀ i, (oracles i).Sound)
    (htarget : ∀ i, (oracles i).project target = Base1007.target)
    (state : Nat → Nat → Nat → List Sig)
    (initial : (k t j : Nat) → DynamicCovered.CheckedContext oracles (state k t j))
    (hint : Nat → Nat → Nat → Sig → Nat)
    (k t j : Nat) (e : MetadataReplay.Edge)
    (he : e ∈ edges oracles state initial hint (k+1) t j)
    (h : e.cut = true) : Impossible k e.nots e.wires := by
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp he
  exact edge_cut_sound oracles hsound htarget _ _ _ p h

end PEqualNP.Outside.L_meta_670_aux.MetadataStrictEdges
