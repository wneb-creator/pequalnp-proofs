import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1533

theorem core (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hno : ∀ s t w w' : Fin n, s ≠ t → w ≠ w' → G.Adj s w → G.Adj t w → G.Adj s w' →
      G.Adj t w' → False)
    (U : Finset (Sym2 (Fin n))) (hU : ∀ e ∈ U, e ∈ G.edgeSet) (x : Fin n) (Y : Finset (Fin n))
    (hY : ∀ y ∈ Y, s(x, y) ∈ U) (B : Finset (Fin n))
    (hB : 2 ≤ B.card ∧ ∃ c : Fin n, (∀ y ∈ B, G.Adj c y) ∧ ∀ y ∈ B, s(c, y) ∉ U) :
    (B ∩ Y).card ≤ 1 ∧ ((∀ b ∈ B, G.Adj x b) → B ∩ Y = ∅) := by
  obtain ⟨h2, c, hc, hcU⟩ := hB
  have hxy : ∀ y ∈ Y, G.Adj x y := fun y hy => by
    have := hU _ (hY y hy)
    simpa using this
  have hcx : ∀ y ∈ B ∩ Y, x ≠ c := by
    intro y hy hxc
    rw [Finset.mem_inter] at hy
    exact hcU y hy.1 (hxc ▸ hY y hy.2)
  constructor
  · apply Finset.card_le_one.2
    intro y hy y' hy'
    by_contra hne
    have h1 := Finset.mem_inter.1 hy
    have h2' := Finset.mem_inter.1 hy'
    exact hno x c y y' (hcx y hy) hne (hxy y h1.2) (hc y h1.1) (hxy y' h2'.2) (hc y' h2'.1)
  · intro hall
    by_contra hne
    obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.2 hne
    have h1 := Finset.mem_inter.1 hy
    obtain ⟨b, hb, hby⟩ := Finset.exists_mem_ne (by omega : 1 < B.card) y
    exact hno x c y b (hcx y hy) (Ne.symm hby) (hxy y h1.2) (hc y h1.1) (hall b hb) (hc b hb)

end PEqualNP.Outside.L_meta_1533

theorem PEqualNP.Outside.L_meta_1533 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], PEqualNP.TopForm.NoFourCycle G →
    ∀ (U : Finset (Sym2 (Fin n))), (∀ e ∈ U, e ∈ G.edgeSet) → ∀ (x : Fin n) (Y : Finset (Fin n)), (∀ y ∈ Y, s(x, y) ∈ U) →
    ∀ (B : Finset (Fin n)), (2 ≤ B.card ∧ ∃ c : Fin n, (∀ y ∈ B, G.Adj c y) ∧ ∀ y ∈ B, s(c, y) ∉ U) →
    (B ∩ Y).card ≤ 1 ∧ ((∀ b ∈ B, G.Adj x b) → B ∩ Y = ∅) := by
  intro n G _ hnf U hU x Y hY B hB
  have hno : ∀ s t w w' : Fin n, s ≠ t → w ≠ w' → G.Adj s w → G.Adj t w → G.Adj s w' →
      G.Adj t w' → False := by
    intro s t w w' hst hww h1 h2 h3 h4
    exact hww (Finset.card_le_one.1 (hnf s t hst) w (by simp [h1, h2]) w' (by simp [h3, h4]))
  exact PEqualNP.Outside.L_meta_1533.core n G hno U hU x Y hY B hB
