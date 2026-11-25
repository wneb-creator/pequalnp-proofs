import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace PEqualNP.Outside.L_meta_2583.FanoSmall

def incident (p l : Fin 7) : Bool :=
  p == l || p == l + 1 || p == l + 3

def edges (A B : Finset (Fin 7)) : Finset (Fin 7 × Fin 7) :=
  (A ×ˢ B).filter fun e => incident e.1 e.2 = true

lemma row_degree : ∀ p : Fin 7, (Finset.univ.filter fun l => incident p l = true).card = 3 := by
  decide

lemma col_degree : ∀ l : Fin 7, (Finset.univ.filter fun p => incident p l = true).card = 3 := by
  decide

lemma common_degree : ∀ p p' : Fin 7, p ≠ p' →
    (Finset.univ.filter fun l => incident p l = true ∧ incident p' l = true).card ≤ 1 := by
  decide

lemma edges_card_left (A B : Finset (Fin 7)) :
    (edges A B).card = ∑ p ∈ A, (B.filter fun l => incident p l = true).card := by
  rw [edges, Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.card_filter]

lemma edges_card_right (A B : Finset (Fin 7)) :
    (edges A B).card = ∑ l ∈ B, (A.filter fun p => incident p l = true).card := by
  rw [edges, Finset.card_filter, Finset.sum_product_right]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.card_filter]

lemma row_le_three (p : Fin 7) (B : Finset (Fin 7)) :
    (B.filter fun l => incident p l = true).card ≤ 3 := by
  rw [← row_degree p]
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ B))

lemma col_le_three (l : Fin 7) (A : Finset (Fin 7)) :
    (A.filter fun p => incident p l = true).card ≤ 3 := by
  rw [← col_degree l]
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ A))

lemma three_by_three (A B : Finset (Fin 7)) (hA : A.card = 3) (hB : B.card = 3) :
    (edges A B).card ≤ 6 := by
  rw [edges_card_left]
  by_cases small : ∀ p ∈ A, (B.filter fun l => incident p l = true).card ≤ 2
  · calc
      _ ≤ ∑ _p ∈ A, 2 := Finset.sum_le_sum small
      _ = 6 := by simp [hA]
  push Not at small
  obtain ⟨p, hp, hlarge⟩ := small
  have full : B.filter (fun l => incident p l = true) = B := by
    apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
    omega
  have other (p' : Fin 7) (hne : p' ≠ p) :
      (B.filter fun l => incident p' l = true).card ≤ 1 := by
    apply (Finset.card_le_card ?_).trans (common_degree p p' hne.symm)
    intro l hl
    have hlB := (Finset.mem_filter.mp hl).1
    rw [← full] at hlB
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp hlB).2, (Finset.mem_filter.mp hl).2⟩
  have hs : (∑ p' ∈ A.erase p, (B.filter fun l => incident p' l = true).card) ≤ 2 := by
    calc
      _ ≤ ∑ _p' ∈ A.erase p, 1 :=
        Finset.sum_le_sum fun p' hp' => other p' (Finset.ne_of_mem_erase hp')
      _ = 2 := by simp [Finset.card_erase_of_mem hp, hA]
  rw [← Finset.sum_erase_add A (fun p => (B.filter fun l => incident p l = true).card) hp]
  have hd := row_le_three p B
  omega

lemma six_vertices (A B : Finset (Fin 7)) (hs : A.card + B.card ≤ 6) :
    (edges A B).card ≤ 6 := by
  by_cases hA : A.card ≤ 2
  · calc
      _ = ∑ p ∈ A, (B.filter fun l => incident p l = true).card := edges_card_left A B
      _ ≤ ∑ _p ∈ A, 3 := Finset.sum_le_sum fun p _ => row_le_three p B
      _ = A.card * 3 := by simp [Nat.nsmul_eq_mul]
      _ ≤ 6 := by omega
  by_cases hB : B.card ≤ 2
  · calc
      _ = ∑ l ∈ B, (A.filter fun p => incident p l = true).card := edges_card_right A B
      _ ≤ ∑ _l ∈ B, 3 := Finset.sum_le_sum fun l _ => col_le_three l A
      _ = B.card * 3 := by simp [Nat.nsmul_eq_mul]
      _ ≤ 6 := by omega
  exact three_by_three A B (by omega) (by omega)

lemma subgraph_six_endpoints (E : Finset (Fin 7 × Fin 7))
    (hI : ∀ e ∈ E, incident e.1 e.2 = true)
    (hs : (E.image Prod.fst).card + (E.image Prod.snd).card ≤ 6) : E.card ≤ 6 := by
  apply (Finset.card_le_card ?_).trans (six_vertices (E.image Prod.fst) (E.image Prod.snd) hs)
  intro e he
  exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
    ⟨Finset.mem_image.mpr ⟨e, he, rfl⟩, Finset.mem_image.mpr ⟨e, he, rfl⟩⟩, hI e he⟩

end PEqualNP.Outside.L_meta_2583.FanoSmall
