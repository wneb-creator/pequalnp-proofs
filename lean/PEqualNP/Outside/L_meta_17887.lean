import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.Acyclic

theorem PEqualNP.Outside.L_meta_17887 : (∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)) (x5 : SimpleGraph (Fin (x1 + x2))), (∀ (x6 x7 : Fin (x1 + x2)), x5.Adj x6 x7 ↔ ∃ x8 ∈ x3, x6 = Fin.castAdd x2 x8.1 ∧ x7 = Fin.natAdd x1 x8.2 ∨ x7 = Fin.castAdd x2 x8.1 ∧ x6 = Fin.natAdd x1 x8.2) → ¬x5.IsAcyclic → (∀ x8 ∈ x4, ∀ x10 ∈ x4, x8.1 = x10.1 → x8 = x10) → (∀ x9 ∈ x4, ∀ x11 ∈ x4, x9.2 = x11.2 → x9 = x11) → x4 ⊆ x3 → (∀ (x11 x12 : Fin x1) (x13 x14 : Fin x2), x11 ≠ x12 → x13 ≠ x14 → ¬((x11, x13) ∈ x3 ∧ (x11, x14) ∈ x3 ∧ (x12, x13) ∈ x3 ∧ (x12, x14) ∈ x3)) → (∀ x12 ∈ x3, ((∀ x14 ∈ x3, x14.1 = x12.1 → x14 = x12) ∨ ∀ x14 ∈ x3, x14.2 = x12.2 → x14 = x12) → (x3.erase x12).Nonempty → x12 ∈ x4) → ∃ x13 ∈ x3, x13 ∉ x4) := by
  classical
  intro m n edges matching G adj cycle leftUnique rightUnique _ _ _
  by_contra! covered
  have separated (i : Fin m) (j : Fin n) : Fin.castAdd n i ≠ Fin.natAdd m j := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
    omega
  have unique {u v w : Fin (m + n)} (hv : G.Adj u v) (hw : G.Adj u w) : v = w := by
    obtain ⟨e, he, hv⟩ := (adj u v).mp hv
    obtain ⟨f, hf, hw⟩ := (adj u w).mp hw
    obtain ⟨hu, hv⟩ | ⟨hv, hu⟩ := hv <;>
      obtain ⟨hu', hw⟩ | ⟨hw, hu'⟩ := hw
    · have hef := leftUnique e (covered e he) f (covered f hf) (by simpa using hu.symm.trans hu')
      exact hv.trans (hef ▸ hw.symm)
    · exact (separated e.1 f.2 (hu.symm.trans hu')).elim
    · exact (separated f.1 e.2 (hu'.symm.trans hu)).elim
    · have hvf := congrArg Fin.val (hu.symm.trans hu')
      have hef := rightUnique e (covered e he) f (covered f hf) (Fin.ext (by simp at hvf; omega))
      exact hv.trans (hef ▸ hw.symm)
  apply cycle
  intro u p hp
  exact hp.snd_ne_penultimate (unique (p.adj_snd hp.not_nil) (p.adj_penultimate hp.not_nil).symm)