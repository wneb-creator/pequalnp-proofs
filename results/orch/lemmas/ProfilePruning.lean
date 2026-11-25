import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace PEqualNP.Outside.L_meta_2592_aux.ProfilePruning

variable {α : Type*}

def Trace (step : List α → α → Prop) (known : List α) : List α → Prop
  | [] => True
  | z :: tail => step known z ∧ Trace step (z :: known) tail

def prune [DecidableEq α] (known : List α) : List α → List α
  | [] => []
  | z :: tail => if z ∈ known then prune known tail else z :: prune (z :: known) tail

lemma trace_mono (step : List α → α → Prop)
    (mono : ∀ {xs ys : List α}, xs ⊆ ys → ∀ {z}, step xs z → step ys z)
    {known seen gs : List α} (inside : known ⊆ seen) (build : Trace step known gs) :
    Trace step seen gs := by
  induction gs generalizing known seen with
  | nil => trivial
  | cons z gs ih =>
    obtain ⟨first, rest⟩ := build
    refine ⟨mono inside first, ih ?_ rest⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem z (inside hx)

lemma prune_trace [DecidableEq α] (step : List α → α → Prop)
    (mono : ∀ {xs ys : List α}, xs ⊆ ys → ∀ {z}, step xs z → step ys z)
    {known gs : List α} (build : Trace step known gs) :
    Trace step known (prune known gs) := by
  induction gs generalizing known with
  | nil => trivial
  | cons z gs ih =>
    obtain ⟨first, rest⟩ := build
    by_cases hz : z ∈ known
    · rw [prune, if_pos hz]
      apply ih
      apply trace_mono step mono ?_ rest
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hz
      · exact hx
    · rw [prune, if_neg hz]
      exact ⟨first, ih rest⟩

lemma prune_subset [DecidableEq α] (known gs : List α) : prune known gs ⊆ gs := by
  induction gs generalizing known with
  | nil => simp [prune]
  | cons z gs ih =>
    by_cases hz : z ∈ known
    · rw [prune, if_pos hz]
      exact fun _ h => List.mem_cons_of_mem z (ih known h)
    · rw [prune, if_neg hz]
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem z (ih (z :: known) hx)

lemma prune_avoids [DecidableEq α] (known gs : List α) :
    ∀ z ∈ prune known gs, z ∉ known := by
  induction gs generalizing known with
  | nil => simp [prune]
  | cons a gs ih =>
    by_cases ha : a ∈ known
    · rw [prune, if_pos ha]
      exact ih known
    · rw [prune, if_neg ha]
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact ha
      · exact fun h => ih (a :: known) z hz (List.mem_cons_of_mem a h)

lemma prune_nodup [DecidableEq α] (known gs : List α) : (prune known gs).Nodup := by
  induction gs generalizing known with
  | nil => simp [prune]
  | cons a gs ih =>
    by_cases ha : a ∈ known
    · rw [prune, if_pos ha]
      exact ih known
    · rw [prune, if_neg ha]
      exact List.nodup_cons.mpr ⟨fun h => prune_avoids (a :: known) gs a h List.mem_cons_self,
        ih (a :: known)⟩

lemma prune_covers [DecidableEq α] (known gs : List α) :
    gs ⊆ prune known gs ++ known := by
  induction gs generalizing known with
  | nil => simp
  | cons a gs ih =>
    by_cases ha : a ∈ known
    · rw [prune, if_pos ha]
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact List.mem_append_right _ ha
      · exact ih known hz
    · rw [prune, if_neg ha]
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · simp
      · have covered := ih (a :: known) hz
        simp only [List.mem_append, List.mem_cons] at covered ⊢
        tauto

lemma prune_outputs [DecidableEq α] {known gs outputs : List α}
    (h : outputs ⊆ gs ++ known) : outputs ⊆ prune known gs ++ known := by
  intro z hz
  rcases List.mem_append.mp (h hz) with fromGates | fromKnown
  · exact prune_covers known gs fromGates
  · exact List.mem_append_right _ fromKnown

lemma prune_length_le [DecidableEq α] (known gs : List α) :
    (prune known gs).length ≤ gs.length := by
  induction gs generalizing known with
  | nil => simp [prune]
  | cons a gs ih =>
    by_cases ha : a ∈ known
    · rw [prune, if_pos ha]
      exact (ih known).trans (by simp)
    · rw [prune, if_neg ha]
      simpa using ih (a :: known)

lemma prune_length_lt_of_seed [DecidableEq α] (known gs : List α)
    (seed : ∃ z ∈ gs, z ∈ known) :
    (prune known gs).length < gs.length := by
  induction gs generalizing known with
  | nil => simpa using seed
  | cons a gs ih =>
    by_cases ha : a ∈ known
    · rw [prune, if_pos ha]
      have bound := prune_length_le known gs
      simp only [List.length_cons]
      omega
    · rw [prune, if_neg ha]
      obtain ⟨z, hz, knownZ⟩ := seed
      have tailZ : z ∈ gs := by
        rcases List.mem_cons.mp hz with rfl | hz
        · exact (ha knownZ).elim
        · exact hz
      have bound := ih (a :: known) ⟨z, tailZ, List.mem_cons_of_mem a knownZ⟩
      simpa using bound

end PEqualNP.Outside.L_meta_2592_aux.ProfilePruning
