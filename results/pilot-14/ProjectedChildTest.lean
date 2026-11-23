import DiagonalT7Base
namespace PEqualNP.Outside.L_meta_670_aux.ChildReplay

open LiveCheck

structure Child where
  nots : Nat
  wires : List Sig

def fill (k : Nat) : List Child → MemoBoolFast.Memo → MemoBoolFast.Memo
  | [],m => m
  | p :: ps,m => fill k ps (MemoBoolFast.save (fun _ _ _ => true) k p.nots p.wires m)

lemma fill_sound {k : Nat} (ps : List Child) {m : MemoBoolFast.Memo}
    (hm : MemoBoolFast.Sound m)
    (children : ∀ p ∈ ps, Impossible k p.nots p.wires) : MemoBoolFast.Sound (fill k ps m) := by
  induction ps generalizing m with
  | nil => exact hm
  | cons p ps ih =>
    exact ih (MemoBoolFast.save_sound _ hm (children p List.mem_cons_self))
      (fun q hq => children q (List.mem_cons_of_mem p hq))

def check (k t : Nat) (v : List Sig) (children : List Child) : Bool :=
  let memo := fill k children .empty
  BoolNodup.check v && !(stepTest k t v
    (fun w => MemoBoolFast.answer k (t-1) w memo)
    (fun w => MemoBoolFast.answer k t w memo))

lemma check_sound {k t : Nat} {v : List Sig} (ps : List Child)
    (children : ∀ p ∈ ps, Impossible k p.nots p.wires)
    (h : check k t v ps = true) : Impossible (k+1) t v := by
  have hm := fill_sound ps (show MemoBoolFast.Sound .empty from trivial) children
  simp only [check,Bool.and_eq_true,Bool.not_eq_true'] at h
  apply exclude_step (BoolNodup.sound h.1) _ _ h.2
  · intro w hw
    exact MemoBoolFast.answer_false hm hw
  · intro w hw
    exact MemoBoolFast.answer_false hm hw

lemma check_fin_sound {k t : Nat} {v : List Sig} (ps : List Child)
    (children : ∀ i : Fin ps.length, Impossible k ps[i.val].nots ps[i.val].wires)
    (h : check k t v ps = true) : Impossible (k+1) t v := by
  apply check_sound ps ?_ h
  intro p hp
  obtain ⟨i,hi,he⟩ := List.getElem_of_mem hp
  simpa only [he] using children ⟨i,hi⟩

end PEqualNP.Outside.L_meta_670_aux.ChildReplay
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
