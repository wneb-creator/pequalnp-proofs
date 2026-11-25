import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9811.CoverProfile

abbrev V := Fin 14
abbrev E := Fin 19

def edge : E → V × V :=
  ![(0,8),(0,10),(1,7),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),
    (4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]

def incident (v : V) : Finset E :=
  Finset.univ.filter fun e => (edge e).1 = v ∨ (edge e).2 = v

def covered (S : Finset V) : Finset E := S.biUnion incident

def uncovered (S : Finset V) : Finset E := Finset.univ \ covered S

def cycle : Finset E := {0,2,6,8,10,15,17,1,3,5,7,11,13,16}

lemma degree : ∀ v : V, (incident v).card ≤ 3 := by decide +kernel
lemma cycle_degree : ∀ v : V, (incident v ∩ cycle).card = 2 := by decide +kernel
lemma cycle_size : cycle.card = 14 := by decide +kernel

lemma covered_le (S : Finset V) : (covered S).card ≤ 3 * S.card := by
  calc
    (covered S).card ≤ ∑ v ∈ S, (incident v).card := Finset.card_biUnion_le
    _ ≤ ∑ v ∈ S, 3 := Finset.sum_le_sum fun v _ => degree v
    _ = 3 * S.card := by simp [Nat.mul_comm]

lemma cycle_covered (S : Finset V) :
    covered S ∩ cycle = S.biUnion (fun v => incident v ∩ cycle) := by
  ext e
  simp only [covered, Finset.mem_inter, Finset.mem_biUnion]
  aesop

lemma cycle_covered_le (S : Finset V) : (covered S ∩ cycle).card ≤ 2 * S.card := by
  rw [cycle_covered]
  calc
    (S.biUnion fun v => incident v ∩ cycle).card ≤ ∑ v ∈ S, (incident v ∩ cycle).card := Finset.card_biUnion_le
    _ = 2 * S.card := by simp [cycle_degree, Nat.mul_comm]

lemma cover_profile (S : Finset V) :
    19 ≤ (uncovered S).card + 3 * S.card ∧
    14 ≤ (uncovered S).card + 2 * S.card := by
  have htotal := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (covered S))
  have hcycle := Finset.card_sdiff_add_card_inter cycle (covered S)
  have hsub : cycle \ covered S ⊆ uncovered S := by
    intro e he
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp he).2⟩
  have hle := Finset.card_le_card hsub
  have h1 := covered_le S
  have h2 := cycle_covered_le S
  simp only [Finset.card_univ, Fintype.card_fin] at htotal
  change (uncovered S).card + (covered S).card = 19 at htotal
  simp only [Finset.inter_comm cycle, cycle_size] at hcycle
  omega

lemma robust_cover (S : Finset V) :
    (S.card ≤ 6 → 2 ≤ (uncovered S).card) ∧
    (S.card ≤ 5 → 4 ≤ (uncovered S).card) ∧
    (S.card ≤ 4 → 7 ≤ (uncovered S).card) := by
  obtain ⟨h1,h2⟩ := cover_profile S
  omega

end PEqualNP.Outside.L_meta_9811.CoverProfile
