namespace PEqualNP.Outside.L_meta_670_aux.FiniteProofTree

open LiveCheck DynamicLeaf

structure Closed {n : Nat} (oracles : Fin n → Oracle) (k t : Nat) (v : List Sig)
    (ctx : DynamicCovered.CheckedContext oracles v) : Prop where
  excluded : Impossible k t v

def prefixCheck {n : Nat} (oracles : Fin n → Oracle) (k t : Nat) (v : List Sig)
    (ctx : DynamicCovered.CheckedContext oracles v) : Bool :=
  BoolNodup.check v && DynamicCovered.cut oracles k t v ctx

lemma of_prefix {n : Nat} (oracles : Fin n → Oracle)
    (hsound : ∀ i, (oracles i).Sound)
    (htarget : ∀ i, (oracles i).project target = Base1007.target)
    {k t : Nat} {v : List Sig} {ctx : DynamicCovered.CheckedContext oracles v}
    (h : prefixCheck oracles k t v ctx = true) : Closed oracles k t v ctx := by
  have hh := Bool.and_eq_true_iff.mp h
  exact ⟨DynamicCovered.cut_sound oracles hsound htarget k t v ctx
    (BoolNodup.sound hh.1) hh.2⟩

lemma of_children {n : Nat} (oracles : Fin n → Oracle)
    {k t : Nat} {v : List Sig} {ctx : DynamicCovered.CheckedContext oracles v}
    (children : ∀ i : Fin (MemoChildren.proposals (k+1) t v).length,
      let p := (MemoChildren.proposals (k+1) t v)[i.val]
      Closed oracles k p.nots p.wires (MetadataStrictEdges.childContext oracles ctx p))
    (parent : ProjectedChild.parentCheck k t v = true) : Closed oracles (k+1) t v ctx := by
  constructor
  apply ProjectedChild.parentCheck_fin_sound ?_ parent
  intro i
  exact (children i).excluded

lemma all_of_fin {α : Type} {p : α → Prop} (xs : List α)
    (h : ∀ i : Fin xs.length, p xs[i.val]) : ∀ x ∈ xs, p x := by
  intro x hx
  obtain ⟨i,hi,he⟩ := List.getElem_of_mem hx
  simpa only [he] using h ⟨i,hi⟩

end PEqualNP.Outside.L_meta_670_aux.FiniteProofTree
