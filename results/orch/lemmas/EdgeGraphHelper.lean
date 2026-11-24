import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3678

lemma graphFun_edgeGraph_list (n : ℕ) (edges : List (ℕ × ℕ))
    (he : ∀ e ∈ edges, e.1 < n ∧ e.2 < n ∧ e.1 ≠ e.2)
    (x : Fin n → Bool) :
    PEqualNP.MetaComplexity.NestedCover.graphFun (PEqualNP.EdgeOwnership.edgeGraph n edges) ∅ x =
      edges.any (fun e => (List.ofFn x).getD e.1 false && (List.ofFn x).getD e.2 false) := by
  apply Bool.eq_iff_iff.mpr
  simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, Finset.notMem_empty,
    false_and, exists_false, decide_false, Bool.false_or, decide_eq_true_eq,
    List.any_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨u, v, ⟨huv, hmem | hmem⟩, hu, hv⟩
    · refine ⟨(u.val, v.val), hmem, ?_, ?_⟩
      · simpa [List.getD_eq_getElem?_getD] using hu
      · simpa [List.getD_eq_getElem?_getD] using hv
    · refine ⟨(v.val, u.val), hmem, ?_, ?_⟩
      · simpa [List.getD_eq_getElem?_getD] using hv
      · simpa [List.getD_eq_getElem?_getD] using hu
  · rintro ⟨⟨a,b⟩, hab, ha, hb⟩
    obtain ⟨ha', hb', hne⟩ := he (a,b) hab
    refine ⟨⟨a, ha'⟩, ⟨b, hb'⟩, ⟨?_, Or.inl hab⟩, ?_, ?_⟩
    · simpa [Fin.ext_iff] using hne
    · simpa [List.getD_eq_getElem?_getD, ha'] using ha
    · simpa [List.getD_eq_getElem?_getD, hb'] using hb

end PEqualNP.Outside.L_meta_3678
