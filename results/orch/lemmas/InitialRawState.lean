import EntryTableAdapters

namespace PEqualNP.Outside.L_meta_2373.Live1024

theorem initial_raw_state {α Ω : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (col : Sig → Set Ω)
    (Cert : Finset α → Sig → Prop) (u : Bool)
    (distinct : Set.InjOn raw (↑roots : Set α))
    (initial : ∀ r ∈ roots, Cert {r} (raw r)) :
    ∃ label : Sig → Finset α,
      LabelPartition roots (roots.image raw) label ∧
      (∀ v ∈ roots.image raw, Cert (label v) v) ∧
      (∀ v ∈ roots.image raw, ReadOnce raw u (label v) v) ∧
      (∀ v ∈ roots.image raw, ColumnSupport raw col (label v) v) := by
  classical
  let label (v : Sig) := roots.filter (fun r => raw r = v)
  have leaf (r : α) (hr : r ∈ roots) : label (raw r) = {r} := by
    ext q
    simp only [label, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hq, he⟩
      exact distinct hq hr he
    · rintro rfl
      exact ⟨hr, rfl⟩
  have part : LabelPartition roots (roots.image raw) label := by
    refine ⟨?_, ?_, ?_⟩
    · intro v hv r hr
      exact (Finset.mem_filter.mp hr).1
    · intro v hv w hw hne
      apply Finset.disjoint_left.mpr
      intro r hrv hrw
      have ev := (Finset.mem_filter.mp hrv).2
      have ew := (Finset.mem_filter.mp hrw).2
      exact hne (ev.symm.trans ew)
    · intro r hr
      exact ⟨raw r, Finset.mem_image_of_mem raw hr, Finset.mem_filter.mpr ⟨hr, rfl⟩⟩
  refine ⟨label, part, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hv
    simpa only [leaf r hr] using initial r hr
  · intro v hv
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hv
    simpa only [leaf r hr] using ReadOnce.leaf raw u r
  · intro v hv o ho
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hv
    exact ⟨r, Finset.mem_filter.mpr ⟨hr, rfl⟩, ho⟩

end PEqualNP.Outside.L_meta_2373.Live1024
