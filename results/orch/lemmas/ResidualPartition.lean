import PrunedInterface

namespace PEqualNP.Outside.L_meta_2373.Live1024

lemma residual_partition_perm {α : Type} [DecidableEq α]
    (roots A B : Finset α) (sub : B ⊆ roots) (disjoint : Disjoint A B) :
    (B.toList ++ (roots \ (A ∪ B)).toList).Perm (roots \ A).toList := by
  have separate : Disjoint B (roots \ (A ∪ B)) := by
    apply Finset.disjoint_left.mpr
    intro r hr ho
    have hn := (Finset.mem_sdiff.mp ho).2
    exact hn (Finset.mem_union_right A hr)
  have nd : (B.toList ++ (roots \ (A ∪ B)).toList).Nodup := by
    simp only [List.nodup_append]
    refine ⟨Finset.nodup_toList _, Finset.nodup_toList _, ?_⟩
    intro r hr s hs eq
    subst s
    exact Finset.disjoint_left.mp separate (Finset.mem_toList.mp hr) (Finset.mem_toList.mp hs)
  apply List.perm_of_nodup_nodup_toFinset_eq nd (Finset.nodup_toList _)
  ext r
  simp only [List.toFinset_append, Finset.toList_toFinset, Finset.mem_union,
    Finset.mem_sdiff, not_or]
  constructor
  · rintro (hb | ⟨hr, ha, hb⟩)
    · exact ⟨sub hb, fun ha => Finset.disjoint_left.mp disjoint ha hb⟩
    · exact ⟨hr, ha⟩
  · rintro ⟨hr, ha⟩
    by_cases hb : r ∈ B
    · exact Or.inl hb
    · exact Or.inr ⟨hr, ha, hb⟩

lemma admissible_left_of_union {α Ω : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (col : Sig → Set Ω) (need : Set Ω)
    {A B : Finset α} {a b z : Sig} (subB : B ⊆ roots) (disjoint : Disjoint A B)
    (gate : col z ⊆ col a ∪ col b) (supportB : ColumnSupport raw col B b)
    (parent : ColumnAdmissible roots raw col need (A ∪ B) z) :
    ColumnAdmissible roots raw col need A a := by
  intro o hn outside
  have hz := parent o hn (fun r hr hnot => outside r hr (fun ha => hnot (Finset.mem_union_left B ha)))
  rcases gate hz with ha | hb
  · exact ha
  · obtain ⟨r, hr, covered⟩ := supportB o hb
    exact False.elim (outside r (subB hr)
      (fun ha => Finset.disjoint_left.mp disjoint ha hr) covered)

end PEqualNP.Outside.L_meta_2373.Live1024
