namespace PEqualNP.Outside.L_meta_670_aux.TightFormula
open LiveCheck LiteralBinary
lemma literal_phase_mem {a : Sig} (ha : a ∈ literals) : phase a ∈ inputs := by
  rw [literal_phase_index ha]
  exact List.mem_map.mpr ⟨index a, by simp, rfl⟩
lemma retained_extension {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
    (ha : a ∈ literals) (hb : b ∈ literals) (hne : a ≠ b)
    (hu : ∀ z ∈ U, z ∈ literals) (h : Live k t (insert (bin d a b) U))
    (hc : U.card ≤ 10) : ∃ extra : List Sig, extra.length ≤ 1 ∧ extra ⊆ inputs ∧
      (U.toList.map phase).Perm (extra ++ inputs) := by
  have sub : inputs ⊆ U.toList.map phase := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hz
    obtain ⟨a, ha, hi⟩ := every_class ha hb hne hu h i
    exact List.mem_map.mpr ⟨a, Finset.mem_toList.mpr ha,
      by rw [literal_phase_index (hu a ha), hi]⟩
  obtain ⟨w, pw, hw⟩ := inputs_nodup.subperm sub
  obtain ⟨extra, he⟩ := hw.exists_perm_append
  have hp : (U.toList.map phase).Perm (extra ++ inputs) :=
    (he.trans (pw.append_right extra)).trans (List.perm_append_comm)
  refine ⟨extra, ?_, ?_, hp⟩
  · have hl := hp.length_eq
    simp only [List.length_map, Finset.length_toList, List.length_append] at hl
    have hin : inputs.length = 9 := by simp [inputs]
    omega
  · intro z hz
    have hm := hp.mem_iff.mpr (List.mem_append_left inputs hz)
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
    exact literal_phase_mem (hu a (Finset.mem_toList.mp ha))
end PEqualNP.Outside.L_meta_670_aux.TightFormula
