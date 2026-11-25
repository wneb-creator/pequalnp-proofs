import PetersenSurplus
import Neighbourhoods

namespace PEqualNP.Outside.L_meta_4675_aux.BipartiteGeometry

open PEqualNP.Outside.L_meta_2590_aux.Surplus
open PEqualNP.Outside.L_meta_4970_aux

def Adj {p l : ℕ} (E : Finset (Fin p × Fin l)) (u v : Fin (p + l)) : Prop :=
  v ∈ neighbours E u

lemma adj_symm {p l : ℕ} (E : Finset (Fin p × Fin l)) :
    ∀ u v, Adj E u v → Adj E v u := by
  intro u
  refine Fin.addCases (fun a => ?_) (fun b => ?_) u
  · intro v hv
    change v ∈ neighbours E (Fin.castAdd l a) at hv
    rw [neighbours_left] at hv
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hv
    change Fin.castAdd l a ∈ neighbours E (Fin.natAdd p b)
    rw [neighbours_right]
    exact Finset.mem_image.mpr ⟨a, by simpa using hb, rfl⟩
  · intro v hv
    change v ∈ neighbours E (Fin.natAdd p b) at hv
    rw [neighbours_right] at hv
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
    change Fin.natAdd p b ∈ neighbours E (Fin.castAdd l a)
    rw [neighbours_left]
    exact Finset.mem_image.mpr ⟨b, by simpa using ha, rfl⟩

lemma adj_irrefl {p l : ℕ} (E : Finset (Fin p × Fin l)) : ∀ u, ¬ Adj E u u := by
  intro u
  refine Fin.addCases (fun a => ?_) (fun b => ?_) u
  · intro hu
    change Fin.castAdd l a ∈ neighbours E (Fin.castAdd l a) at hu
    rw [neighbours_left] at hu
    obtain ⟨b, -, he⟩ := Finset.mem_image.mp hu
    exact left_right_ne a b he.symm
  · intro hu
    change Fin.natAdd p b ∈ neighbours E (Fin.natAdd p b) at hu
    rw [neighbours_right] at hu
    obtain ⟨a, -, he⟩ := Finset.mem_image.mp hu
    exact left_right_ne a b he

lemma sem_geometry {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (hdegree : ∀ v, 2 ≤ (neighbours E v).card) : sem_Gr (Adj E) := by
  refine ⟨adj_symm E, adj_irrefl E, ?_, ?_⟩
  · intro u v huv
    by_contra hno
    push Not at hno
    have hsub : neighbours E u ⊆ neighbours E v := hno
    have hi := neighbours_inter_card E hfour u v huv
    rw [Finset.inter_eq_left.mpr hsub] at hi
    have hd := hdegree u
    omega
  · intro u v
    by_contra hno
    push Not at hno
    have hsub : neighbours E u ⊆ {v} := by
      intro a ha
      exact Finset.mem_singleton.mpr (hno a ha)
    have hcard := Finset.card_le_card hsub
    have hd := hdegree u
    simp only [Finset.card_singleton] at hcard
    omega

lemma edge_iff {p l : ℕ} (E : Finset (Fin p × Fin l)) (x : Fin (p + l) → Bool) :
    sem_Edge (Adj E) x ↔ ∃ a b, (a, b) ∈ E ∧
      x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true := by
  constructor
  · rintro ⟨u, v, huv, hu, hv⟩
    revert v huv hu hv
    refine Fin.addCases (fun a => ?_) (fun b => ?_) u
    · intro v huv hu hv
      change v ∈ neighbours E (Fin.castAdd l a) at huv
      rw [neighbours_left] at huv
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp huv
      exact ⟨a, b, (Finset.mem_filter.mp hb).2, hu, hv⟩
    · intro v huv hu hv
      change v ∈ neighbours E (Fin.natAdd p b) at huv
      rw [neighbours_right] at huv
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp huv
      exact ⟨a, b, (Finset.mem_filter.mp ha).2, hv, hu⟩
  · rintro ⟨a, b, hab, ha, hb⟩
    refine ⟨Fin.castAdd l a, Fin.natAdd p b, ?_, ha, hb⟩
    change Fin.natAdd p b ∈ neighbours E (Fin.castAdd l a)
    rw [neighbours_left]
    exact Finset.mem_image.mpr ⟨b, by simp [hab], rfl⟩

end PEqualNP.Outside.L_meta_4675_aux.BipartiteGeometry
