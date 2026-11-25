import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9502.ClosedNoLive

variable {α : Type} [DecidableEq α]

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

lemma closed_no_live (ops : α → α → Finset α) (goal : α)
    (closed : ℕ → Finset α → Prop)
    (hzero : ∀ s, closed 0 s → s ≠ {goal})
    (hskip : ∀ k s, closed (k + 1) s → closed k s)
    (hstep : ∀ k s a b z rest, closed (k + 1) s →
      a ∈ s → b ∈ s → a ≠ b → z ∈ ops a b → z ∉ s →
      s = insert a (insert b rest) → closed k (insert z rest))
    {k : ℕ} {s : Finset α} (hc : closed k s) : ¬ live ops goal k s := by
  induction k generalizing s with
  | zero => exact hzero s hc
  | succ k ih =>
    intro h
    rcases h with h | ⟨a, ha, b, hb, hab, z, hz, hzs, rest, hr, hnext⟩
    · exact ih (hskip k s hc) h
    · exact ih (hstep k s a b z rest hc ha hb hab hz hzs hr) hnext

lemma closed_no_live_budget (ops : α → α → Finset α) (goal : α)
    (table : Finset (ℕ × Finset α))
    (hbase : ∀ n s, (n, s) ∈ table → s ≠ {goal})
    (hstep : ∀ n s a b z rest, (n, s) ∈ table → 0 < n →
      a ∈ s → b ∈ s → a ≠ b → z ∈ ops a b → z ∉ s →
      s = insert a (insert b rest) →
      ∃ m, n - 1 ≤ m ∧ (m, insert z rest) ∈ table)
    {k : ℕ} {s : Finset α} (hc : ∃ n, k ≤ n ∧ (n, s) ∈ table) :
    ¬ live ops goal k s := by
  apply closed_no_live ops goal (fun k s => ∃ n, k ≤ n ∧ (n, s) ∈ table) ?_ ?_ ?_ hc
  · intro s hs
    obtain ⟨n, hn, hmem⟩ := hs
    exact hbase n s hmem
  · intro k s hs
    obtain ⟨n, hn, hmem⟩ := hs
    exact ⟨n, by omega, hmem⟩
  · intro k s a b z rest hs ha hb hab hz hzs hr
    obtain ⟨n, hn, hmem⟩ := hs
    obtain ⟨m, hm, hmem'⟩ := hstep n s a b z rest hmem (by omega) ha hb hab hz hzs hr
    exact ⟨m, by omega, hmem'⟩

end PEqualNP.Outside.L_meta_9502.ClosedNoLive
