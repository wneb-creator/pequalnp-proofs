import PackingThreeDefs

namespace PEqualNP.Outside.L_meta_1896_aux

namespace PackingPrunedDFS

variable {α σ : Type}

lemma branchAt_cons_succ (ok : σ → α → Bool) (step : σ → α → σ)
    (recur : σ → List α → Bool) (s : σ) (b : α) (bs : List α) (i : Nat) :
    branchAt ok step recur s (b :: bs) (i + 1) = branchAt ok step recur s bs i := by
  rfl

lemma branches_of_branchAt (ok : σ → α → Bool) (step : σ → α → σ)
    (recur : σ → List α → Bool) (s : σ) (bs : List α)
    (h : ∀ i < bs.length, branchAt ok step recur s bs i = true) :
    branches ok step recur s bs = true := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [branches, Bool.and_eq_true]
    constructor
    · exact h 0 (by simp)
    · apply ih
      intro i hi
      have hh := h (i + 1) (by simp; omega)
      exact hh

lemma branchAt_of_chunk (ok : σ → α → Bool) (step : σ → α → σ)
    (recur : σ → List α → Bool) (s : σ) (bs : List α)
    (start count offset : Nat)
    (h : chunk ok step recur s bs start count = true) (hoffset : offset < count) :
    branchAt ok step recur s bs (start + offset) = true := by
  unfold chunk at h
  exact (List.all_eq_true.mp h) offset (List.mem_range.mpr hoffset)

lemma branches_of_chunk_cover (ok : σ → α → Bool) (step : σ → α → σ)
    (recur : σ → List α → Bool) (s : σ) (bs : List α)
    (intervals : List (Nat × Nat))
    (hchunks : ∀ p ∈ intervals, chunk ok step recur s bs p.1 p.2 = true)
    (hcover : ∀ i < bs.length, ∃ p ∈ intervals, p.1 ≤ i ∧ i < p.1 + p.2) :
    branches ok step recur s bs = true := by
  apply branches_of_branchAt
  intro i hi
  obtain ⟨p, hp, hstart, hend⟩ := hcover i hi
  have hoffset : i - p.1 < p.2 := by omega
  have hsum : p.1 + (i - p.1) = i := by omega
  have h := branchAt_of_chunk ok step recur s bs p.1 p.2 (i - p.1)
    (hchunks p hp) hoffset
  simpa only [hsum] using h

lemma branches_of_full_chunk (ok : σ → α → Bool) (step : σ → α → σ)
    (recur : σ → List α → Bool) (s : σ) (bs : List α)
    (h : chunk ok step recur s bs 0 bs.length = true) :
    branches ok step recur s bs = true := by
  apply branches_of_branchAt
  intro i hi
  simpa only [Nat.zero_add] using branchAt_of_chunk ok step recur s bs 0 bs.length i h hi

end PackingPrunedDFS

end PEqualNP.Outside.L_meta_1896_aux
