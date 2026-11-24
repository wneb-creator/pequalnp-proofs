namespace PEqualNP.Outside.L_meta_670_aux.RootSevenLeaf

open LiveCheck

lemma leaf_from_children (i : Fin 12)
    (children : ∀ j : Fin 9, Impossible 11 (child i.val j.val).nots (child i.val j.val).wires)
    (parent : ProjectedChild.parentCheck 11 4 (state i.val) = true) :
    Impossible 12 4 (state i.val) := by
  apply excluded i.val ?_ parent
  intro j
  let jj : Fin 9 := ⟨j.val,by simpa only [counts i] using j.isLt⟩
  simpa only [jj,child,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem j.isLt,Option.getD_some]
    using children jj

lemma raw_from_leaves
    (leaves : ∀ i : Fin 12, Impossible 12 4 (state i.val)) : Impossible 15 7 raw := by
  apply RootSeven.excluded
  intro i
  let ii : Fin 12 := ⟨i.val,by simpa only [RootSeven.nodes12,List.length_cons,List.length_nil] using i.isLt⟩
  simpa only [ii,state,row,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem i.isLt,Option.getD_some]
    using leaves ii

end PEqualNP.Outside.L_meta_670_aux.RootSevenLeaf
