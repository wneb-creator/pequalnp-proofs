import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5004

open PEqualNP.CircuitLowerBounds

def rel (σ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map σ⟩

lemma getD_snoc (w : List Bool) (a : Bool) (k : ℕ) :
    (w ++ [a]).getD k false = if k < w.length then w.getD k false else if k = w.length then a else false := by
  by_cases h1 : k < w.length
  · rw [if_pos h1, List.getD_append _ _ _ _ h1]
  · rw [if_neg h1]
    by_cases h2 : k = w.length
    · rw [if_pos h2, h2]
      simp
    · rw [if_neg h2]
      apply List.getD_eq_default
      rw [List.length_append]
      simp
      omega

lemma main (n : ℕ) (σ : ℕ → ℕ) (h1 : ∀ i < n, σ i < n) (h2 : ∀ i, n ≤ i → σ i = i) :
    ∀ (gs : List Gate) (w7 w5 : List Bool), w7.length = w5.length → n ≤ w5.length →
      (∀ i, w7.getD (σ i) false = w5.getD i false) →
      ∀ i, ((gs.map (rel σ)).foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w7).getD (σ i) false =
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w5).getD i false := by
  intro gs
  induction gs with
  | nil => intro w7 w5 _ _ hinv i; simpa using hinv i
  | cons g gs ih =>
    intro w7 w5 hlen hn hinv
    have hval : (rel σ g).op.eval ((rel σ g).inputs.map fun i => w7.getD i false) =
        g.op.eval (g.inputs.map fun i => w5.getD i false) := by
      simp only [rel, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact hinv i
    simp only [List.map_cons, List.foldl_cons]
    rw [hval]
    apply ih
    · simp [hlen]
    · simp; omega
    · intro i
      rw [getD_snoc, getD_snoc, hlen]
      by_cases hi : i < n
      · have hs := h1 i hi
        rw [if_pos (by omega), if_pos (by omega)]
        exact hinv i
      · have hs : σ i = i := h2 i (by omega)
        rw [hs]
        by_cases hl : i < w5.length
        · rw [if_pos hl, if_pos hl]
          have := hinv i
          rw [hs] at this
          exact this
        · rw [if_neg hl, if_neg hl]

end PEqualNP.Outside.L_meta_5004

theorem PEqualNP.Outside.L_meta_5004 : ∀ (x1 : ℕ) (x2 : ℕ → ℕ), (∀ x3 < x1, x2 x3 < x1) → (∀ (x4 : ℕ), x1 ≤ x4 → x2 x4 = x4) → ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x7 ∧ x7.size = x5.size ∧ ∀ (x8 x9 : List Bool), x8.length = x1 → x9.length = x1 → (∀ (x12 : ℕ), x8.getD (x2 x12) Bool.false = x9.getD x12 Bool.false) → x7.eval x8 = x5.eval x9 := by
  intro n σ h1 h2 C hC
  refine ⟨⟨C.gates.map (PEqualNP.Outside.L_meta_5004.rel σ), σ C.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    have := hC g0 hg0
    exact ⟨this.1, by simpa [PEqualNP.Outside.L_meta_5004.rel] using this.2⟩
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro x8 x9 l8 l9 hx
    exact PEqualNP.Outside.L_meta_5004.main n σ h1 h2 C.gates x8 x9 (by rw [l8, l9]) (by rw [l9]) hx C.output
