namespace PEqualNP.Outside.L_meta_670_aux.ProjectedChild

open LiveCheck DynamicLeaf

def check {n : Nat} (oracles : Fin n → Oracle) (k : Nat) {v : List Sig}
    (c : DynamicCovered.CheckedContext oracles v) (p : MemoChildren.Proposal) : Bool :=
  BoolNodup.check p.wires && !(DynamicRawNoMemo.search oracles k p.nots p.wires
    (MetadataStrictEdges.childContext oracles c p).val)

lemma check_sound {n : Nat} (oracles : Fin n → Oracle)
    (hsound : ∀ q, (oracles q).Sound)
    (htarget : ∀ q, (oracles q).project target = Base1007.target)
    (k : Nat) {v : List Sig} (c : DynamicCovered.CheckedContext oracles v)
    (p : MemoChildren.Proposal) (h : check oracles k c p = true) :
    Impossible k p.nots p.wires := by
  simp only [check,Bool.and_eq_true,Bool.not_eq_true'] at h
  exact DynamicRawNoMemo.search_sound oracles hsound htarget k p.nots p.wires
    (MetadataStrictEdges.childContext oracles c p).val (BoolNodup.sound h.1)
    (MetadataStrictEdges.childContext oracles c p).property h.2

def prefixCheck {n : Nat} (oracles : Fin n → Oracle) (k : Nat) {v : List Sig}
    (c : DynamicCovered.CheckedContext oracles v) (p : MemoChildren.Proposal) : Bool :=
  BoolNodup.check p.wires && DynamicCovered.cut oracles k p.nots p.wires
    (MetadataStrictEdges.childContext oracles c p)

lemma prefixCheck_sound {n : Nat} (oracles : Fin n → Oracle)
    (hsound : ∀ q, (oracles q).Sound)
    (htarget : ∀ q, (oracles q).project target = Base1007.target)
    (k : Nat) {v : List Sig} (c : DynamicCovered.CheckedContext oracles v)
    (p : MemoChildren.Proposal) (h : prefixCheck oracles k c p = true) :
    Impossible k p.nots p.wires := by
  simp only [prefixCheck,Bool.and_eq_true] at h
  exact DynamicCovered.cut_sound oracles hsound htarget k p.nots p.wires
    (MetadataStrictEdges.childContext oracles c p) (BoolNodup.sound h.1) h.2

def children (k t : Nat) (v : List Sig) : List ChildReplay.Child :=
  (MemoChildren.proposals (k+1) t v).map (fun p => ⟨p.nots,p.wires⟩)

def parentCheck (k t : Nat) (v : List Sig) : Bool :=
  ChildReplay.check k t v (children k t v)

lemma parentCheck_sound {k t : Nat} {v : List Sig}
    (hc : ∀ p ∈ MemoChildren.proposals (k+1) t v, Impossible k p.nots p.wires)
    (h : parentCheck k t v = true) : Impossible (k+1) t v := by
  apply ChildReplay.check_sound (children k t v) ?_ h
  intro q hq
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hq
  exact hc p hp

lemma parentCheck_fin_sound {k t : Nat} {v : List Sig}
    (hc : ∀ i : Fin (MemoChildren.proposals (k+1) t v).length,
      let p := (MemoChildren.proposals (k+1) t v)[i.val]
      Impossible k p.nots p.wires)
    (h : parentCheck k t v = true) : Impossible (k+1) t v := by
  apply parentCheck_sound ?_ h
  intro p hp
  obtain ⟨i,hi,he⟩ := List.getElem_of_mem hp
  simpa only [he] using hc ⟨i,hi⟩

end PEqualNP.Outside.L_meta_670_aux.ProjectedChild
