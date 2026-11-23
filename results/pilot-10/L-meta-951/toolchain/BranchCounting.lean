import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_951.BranchCounting

variable {ι γ : Type*} [Fintype ι] [DecidableEq ι] [Fintype γ] [DecidableEq γ]

def deficient (H : Finset ι) (outI : ι → ℕ) : Finset ι := H.filter fun v => outI v = 1

lemma input_edges_lower (A H : Finset ι) (hHA : H ⊆ A) (outI : ι → ℕ)
    (hactive : ∀ v ∈ A, 1 ≤ outI v) :
    A.card + H.card ≤ (∑ v, outI v) + (deficient H outI).card := by
  have hp (v : ι) : (if v ∈ A then 1 else 0) + (if v ∈ H then 1 else 0) ≤
      outI v + (if v ∈ deficient H outI then 1 else 0) := by
    by_cases hvA : v ∈ A
    · have ho := hactive v hvA
      by_cases hvH : v ∈ H
      · by_cases ho1 : outI v = 1
        · simp [hvA, hvH, deficient, ho1]
        · simp only [hvA, hvH, deficient, Finset.mem_filter, ho1, and_false,
            not_false_eq_true, ite_false, ite_true]
          omega
      · simp only [hvA, hvH, deficient, Finset.mem_filter, false_and,
          not_false_eq_true, ite_false, ite_true]
        omega
    · have hvH : v ∉ H := fun h => hvA (hHA h)
      simp [hvA, hvH]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hp v)
  simpa [Finset.sum_add_distrib] using hs

lemma branch_surplus (D : Finset ι) (outG : γ → ℕ)
    (b : {v // v ∈ D} → γ) (hinj : Function.Injective b)
    (hbranch : ∀ v, 2 ≤ outG (b v)) :
    D.card ≤ ∑ u, (outG u - 1) := by
  let J : Finset γ := Finset.univ.image b
  have hcard : J.card = D.card := by
    dsimp [J]
    rw [Finset.card_image_of_injective _ hinj]
    simp
  have hp (u : γ) : (if u ∈ J then 1 else 0) ≤ outG u - 1 := by
    by_cases hu : u ∈ J
    · obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hu
      have hh := hbranch v
      simp only [hu, ite_true]
      omega
    · simp [hu]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun u _ => hp u)
  simpa [hcard] using hs

lemma gate_edges_decompose (outG : γ → ℕ) (hgate : ∀ u, 1 ≤ outG u) :
    (∑ u, outG u) = Fintype.card γ + ∑ u, (outG u - 1) := by
  calc
    (∑ u, outG u) = ∑ u, (1 + (outG u - 1)) := by
      apply Finset.sum_congr rfl
      intro u _
      have hh := hgate u
      omega
    _ = Fintype.card γ + ∑ u, (outG u - 1) := by
      simp [Finset.sum_add_distrib]

lemma edge_lower_of_branch_injection (A H : Finset ι) (hHA : H ⊆ A)
    (outI : ι → ℕ) (outG : γ → ℕ)
    (hactive : ∀ v ∈ A, 1 ≤ outI v) (hgate : ∀ u, 1 ≤ outG u)
    (b : {v // v ∈ deficient H outI} → γ) (hinj : Function.Injective b)
    (hbranch : ∀ v, 2 ≤ outG (b v)) :
    A.card + H.card + Fintype.card γ ≤ (∑ v, outI v) + ∑ u, outG u := by
  have hi := input_edges_lower A H hHA outI hactive
  have hs := branch_surplus (deficient H outI) outG b hinj hbranch
  have hg := gate_edges_decompose outG hgate
  omega

lemma fanin_two_lower (A H : Finset ι) (hHA : H ⊆ A)
    (outI : ι → ℕ) (outG : γ → ℕ)
    (hactive : ∀ v ∈ A, 1 ≤ outI v) (hgate : ∀ u, 1 ≤ outG u)
    (b : {v // v ∈ deficient H outI} → γ) (hinj : Function.Injective b)
    (hbranch : ∀ v, 2 ≤ outG (b v)) (m loss : ℕ)
    (hfanin : (∑ v, outI v) + (∑ u, outG u) + loss ≤ 2 * Fintype.card γ + m) :
    A.card + H.card + loss ≤ Fintype.card γ + m := by
  have hl := edge_lower_of_branch_injection A H hHA outI outG hactive hgate b hinj hbranch
  omega

lemma capped_degree_sum (d : ι → ℕ) :
    (∑ v, min (d v) 2) =
      (Finset.univ.filter fun v => 0 < d v).card +
        (Finset.univ.filter fun v => 2 ≤ d v).card := by
  let A : Finset ι := Finset.univ.filter fun v => 0 < d v
  let H : Finset ι := Finset.univ.filter fun v => 2 ≤ d v
  have hp (v : ι) : min (d v) 2 =
      (if v ∈ A then 1 else 0) + (if v ∈ H then 1 else 0) := by
    simp only [A, H, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs <;> omega
  calc
    (∑ v, min (d v) 2) = ∑ v, ((if v ∈ A then 1 else 0) + (if v ∈ H then 1 else 0)) :=
      Finset.sum_congr rfl (fun v _ => hp v)
    _ = A.card + H.card := by simp [Finset.sum_add_distrib]

lemma degree_capped_fanin_lower (d outI : ι → ℕ) (outG : γ → ℕ)
    (hactive : ∀ v, 0 < d v → 1 ≤ outI v) (hgate : ∀ u, 1 ≤ outG u)
    (b : {v // v ∈ deficient (Finset.univ.filter fun v => 2 ≤ d v) outI} → γ)
    (hinj : Function.Injective b) (hbranch : ∀ v, 2 ≤ outG (b v)) (m loss : ℕ)
    (hfanin : (∑ v, outI v) + (∑ u, outG u) + loss ≤ 2 * Fintype.card γ + m) :
    (∑ v, min (d v) 2) + loss ≤ Fintype.card γ + m := by
  rw [capped_degree_sum]
  apply fanin_two_lower _ _ _ outI outG _ hgate b hinj hbranch m loss hfanin
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    omega
  · intro v hv
    apply hactive v
    simpa using hv

lemma degree_at_most_two_fanin_lower (d outI : ι → ℕ) (outG : γ → ℕ)
    (hdegree : ∀ v, d v ≤ 2)
    (hactive : ∀ v, 0 < d v → 1 ≤ outI v) (hgate : ∀ u, 1 ≤ outG u)
    (b : {v // v ∈ deficient (Finset.univ.filter fun v => 2 ≤ d v) outI} → γ)
    (hinj : Function.Injective b) (hbranch : ∀ v, 2 ≤ outG (b v)) (m loss : ℕ)
    (hfanin : (∑ v, outI v) + (∑ u, outG u) + loss ≤ 2 * Fintype.card γ + m) :
    (∑ v, d v) + loss ≤ Fintype.card γ + m := by
  have hh := degree_capped_fanin_lower d outI outG hactive hgate b hinj hbranch m loss hfanin
  simpa only [min_eq_left (hdegree _)] using hh

end PEqualNP.Outside.L_meta_951.BranchCounting
