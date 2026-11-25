import PEqualNP.Defs

-- The live-set search and its completeness proof are adapted from
-- lean/PEqualNP/Outside/L_meta_6345.lean in this repository, widened from 64 to 36
-- (true entry, false entry) pairs; the rows, the 10-gate search and the conclusion are new.

namespace PEqualNP.Outside.L_meta_9502.LiveBudget

open scoped Classical

section Live

variable {α : Type}

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

section Budget
variable {α : Type}

noncomputable def oldCount (a b : α) (rest : Finset α) : Nat :=
  (if a ∈ rest then 1 else 0) + (if b ∈ rest then 1 else 0)

lemma card_step {a b z : α} {rest : Finset α} (hab : a ≠ b)
    (hz : z ∉ insert a (insert b rest)) :
    (insert a (insert b rest)).card + oldCount a b rest = (insert z rest).card + 1 := by
  have hzr : z ∉ rest := fun h => hz (by simp [h])
  rw [Finset.card_insert_of_notMem hzr]
  by_cases ha : a ∈ rest <;> by_cases hb : b ∈ rest
  · simp [oldCount,ha,hb]
  · rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem ha), Finset.card_insert_of_notMem hb]
    simp [oldCount,ha,hb]
  · rw [Finset.insert_eq_of_mem hb, Finset.card_insert_of_notMem ha]
    simp [oldCount,ha,hb]
  · rw [Finset.card_insert_of_notMem (by simp [hab,ha]), Finset.card_insert_of_notMem hb]
    simp [oldCount,ha,hb]

lemma live_budget_induction {ops : α → α → Finset α} {goal : α}
    (R : α → Prop) (Good : Finset α → Nat → Prop)
    (hops : ∀ a b z, R a → R b → z ∈ ops a b → R z)
    (hbase : R goal → Good {goal} 0)
    (hstep : ∀ a b z rest r, a ≠ b → z ∉ insert a (insert b rest) → z ∈ ops a b →
      (∀ w ∈ insert a (insert b rest), R w) → Good (insert z rest) r →
      Good (insert a (insert b rest)) (r + oldCount a b rest))
    {k : Nat} {S : Finset α} (hR : ∀ w ∈ S, R w) (hl : live ops goal k S) :
    ∃ r, Good S r ∧ S.card + r ≤ k + 1 := by
  induction k generalizing S with
  | zero =>
    change S = {goal} at hl
    subst S
    exact ⟨0,hbase (hR goal (by simp)),by simp⟩
  | succ k ih =>
    rcases hl with hskip | ⟨a,ha,b,hb,hab,z,hz,hout,rest,hS,htail⟩
    · obtain ⟨r,hgood,hbound⟩ := ih hR hskip
      exact ⟨r,hgood,by omega⟩
    · subst S
      have hr : ∀ w ∈ insert z rest, R w := by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact hops a b w (hR a (by simp)) (hR b (by simp)) hz
        · exact hR w (by simp [hw])
      obtain ⟨r,hgood,hbound⟩ := ih hr htail
      refine ⟨r + oldCount a b rest,hstep a b z rest r hab hout hz hR hgood,?_⟩
      have hc := card_step hab hout
      omega

end Budget
end PEqualNP.Outside.L_meta_9502.LiveBudget
