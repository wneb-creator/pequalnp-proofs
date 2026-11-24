import RootSevenFiniteCore
namespace PEqualNP.Outside.L_meta_670_aux.RootSeven
lemma levels : ∀ k ≤ 15, ∀ t ≤ 7, MetadataReplay.levelCheck config k t = true := by
  intro k hk t ht
  by_cases hz : config.count k t = 0
  · simp only [MetadataReplay.levelCheck,hz,MetadataReplay.span]
  · have hb : 12 ≤ k ∧ k ≤ 15 ∧ t+8 = k := by
      by_contra bad
      apply hz
      simp only [config,MetadataMarker.config,restricted,DiagonalT7.config,Cut12StrictReplay.count]
      split_ifs <;> omega
    have casesK : k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 := by omega
    rcases casesK with rfl | rfl | rfl | rfl
    · have h : t = 4 := by omega
      subst t
      exact level12
    · have h : t = 5 := by omega
      subst t
      exact level13
    · have h : t = 6 := by omega
      subst t
      exact level14
    · have h : t = 7 := by omega
      subst t
      exact level15

lemma excluded
    (leaves : ∀ i : Fin nodes12.length, LiveCheck.Impossible 12 4
      (Cut12StrictReplay.state 12 4 nodes12[i.val])) : LiveCheck.Impossible 15 7 LiveCheck.raw :=
  MetadataReplay.checked_link_sound config (config_valid leaves) 15 levels (by omega) (by change 7 ≤ 7; omega) root_link

end PEqualNP.Outside.L_meta_670_aux.RootSeven
