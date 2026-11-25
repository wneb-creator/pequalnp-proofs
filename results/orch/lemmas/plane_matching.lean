import PEqualNP.Defs
import Mathlib.Tactic
import Mathlib.Combinatorics.Hall.Basic

namespace PEqualNP.Outside.L_meta_2583

lemma regular_incidence_matching {N k : ℕ} (I : Fin N → Fin N → Prop)
    [DecidableRel I] (hk : 0 < k)
    (hrow : ∀ p : Fin N, (Finset.univ.filter (fun l => I p l)).card = k)
    (hcol : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = k) :
    ∃ σ : Equiv.Perm (Fin N), ∀ p : Fin N, I p (σ p) := by
  classical
  let S (p : Fin N) : Finset (Fin N) := Finset.univ.filter (fun l => I p l)
  have hall : ∀ B : Finset (Fin N), B.card ≤ (B.biUnion S).card := by
    intro B
    let U := B.biUnion S
    have h1 : ∑ p ∈ B, (U ∩ S p).card = B.card * k := by
      rw [Finset.sum_congr rfl (fun p hp => by
        rw [Finset.inter_eq_right.mpr (Finset.subset_biUnion_of_mem S hp), hrow]),
        Finset.sum_const, smul_eq_mul]
    have h2 : ∑ p ∈ B, (U ∩ S p).card =
        ∑ l ∈ U, (B.filter (fun p => l ∈ S p)).card := by
      simp_rw [← Finset.filter_mem_eq_inter, Finset.card_eq_sum_ones, Finset.sum_filter]
      exact Finset.sum_comm
    have h3 : ∑ l ∈ U, (B.filter (fun p => l ∈ S p)).card ≤ U.card * k := by
      have hbound (l : Fin N) : (B.filter (fun p => l ∈ S p)).card ≤ k := by
        have he : B.filter (fun p => l ∈ S p) = B.filter (fun p => I p l) := by
          ext p
          simp [S]
        rw [he, ← hcol l]
        exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ B))
      have hsum := Finset.sum_le_card_nsmul U
        (fun l => (B.filter (fun p => l ∈ S p)).card) k (fun l _ => hbound l)
      simpa [smul_eq_mul] using hsum
    have h4 : B.card * k ≤ U.card * k := by omega
    exact Nat.le_of_mul_le_mul_right h4 hk
  obtain ⟨f, hinj, hf⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective S).mp hall
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), ?_⟩
  intro p
  exact (Finset.mem_filter.mp (hf p)).2

lemma incidence_card {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] :
    (Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)).card =
      ∑ p : Fin N, (Finset.univ.filter (fun l => I p l)).card := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_product Finset.univ Finset.univ
    (fun e : Fin N × Fin N => if I e.1 e.2 then 1 else 0)

end PEqualNP.Outside.L_meta_2583
