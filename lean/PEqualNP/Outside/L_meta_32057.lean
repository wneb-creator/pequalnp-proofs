import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.Abel
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Projection
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Positivity
import PEqualNP.Defs
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Basis.VectorSpace

namespace PEqualNP.Outside.L_meta_32057_aux


section h5_part_1

lemma h5_weighted_bound {I : Type*} [Fintype I]
    (raw denom target total : ℕ) (weight bias : I → ℕ)
    (hraw : raw ≤ ∑ i, weight i * bias i)
    (hweight : (∑ i, weight i) = total)
    (hbias : ∀ i, denom * bias i ≤ target) :
    denom * raw ≤ total * target := by
  calc
    denom * raw ≤ denom * ∑ i, weight i * bias i := Nat.mul_le_mul_left _ hraw
    _ = ∑ i, weight i * (denom * bias i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ ∑ i, weight i * target :=
      Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (hbias i))
    _ = total * target := by rw [← Finset.sum_mul, hweight]

lemma h5_low_dimension_bound (m b t plane bias : ℕ)
    (ht : t + 2 ≤ b) (hbias : bias ≤ 2 ^ t) (hplane : 2 ^ m ≤ plane) :
    2 ^ (m + 2) * bias ≤ 2 ^ b * plane := by
  calc
    2 ^ (m + 2) * bias ≤ 2 ^ (m + 2) * 2 ^ t := Nat.mul_le_mul_left _ hbias
    _ = 2 ^ (m + 2 + t) := (pow_add _ _ _).symm
    _ ≤ 2 ^ (b + m) := Nat.pow_le_pow_right (by decide) (by omega)
    _ = 2 ^ b * 2 ^ m := pow_add _ _ _
    _ ≤ 2 ^ b * plane := Nat.mul_le_mul_left _ hplane

lemma h5_three_case_bound (m b t plane line bias : ℕ)
    (ht : t ≤ b) (hbias : bias ≤ 2 ^ t) (hplane : 2 ^ m ≤ plane)
    (hfull : t = b → 2 ^ (m + 2) * bias ≤ 2 ^ b * plane)
    (hone : t + 1 = b → 2 ^ (m + 2) * bias ≤ 2 ^ b * line) :
    2 ^ (m + 2) * bias ≤ 2 ^ b * max plane line := by
  by_cases h0 : t = b
  · exact (hfull h0).trans (Nat.mul_le_mul_left _ (le_max_left _ _))
  by_cases h1 : t + 1 = b
  · exact (hone h1).trans (Nat.mul_le_mul_left _ (le_max_right _ _))
  exact (h5_low_dimension_bound m b t plane bias (by omega) hbias hplane).trans
    (Nat.mul_le_mul_left _ (le_max_left _ _))

lemma h5_circuit_upper_reduction {I : Type*} [Fintype I]
    (n m b plane line raw : ℕ) (dim weight bias : I → ℕ)
    (hraw : raw ≤ ∑ i, weight i * bias i)
    (hweight : (∑ i, weight i) = 2 ^ n)
    (hdim : ∀ i, dim i ≤ b)
    (hbias : ∀ i, bias i ≤ 2 ^ (dim i))
    (hplane : 2 ^ m ≤ plane)
    (hfull : ∀ i, dim i = b → 2 ^ (m + 2) * bias i ≤ 2 ^ b * plane)
    (hone : ∀ i, dim i + 1 = b → 2 ^ (m + 2) * bias i ≤ 2 ^ b * line) :
    2 ^ (m + 2) * raw ≤ 2 ^ (n + b) * max plane line := by
  have h := h5_weighted_bound raw (2 ^ (m + 2)) (2 ^ b * max plane line)
    (2 ^ n) weight bias hraw hweight
    (fun i => h5_three_case_bound m b (dim i) plane line (bias i)
      (hdim i) (hbias i) hplane (hfull i) (hone i))
  simpa only [pow_add, Nat.mul_assoc] using h

noncomputable def h5Weight {k m : ℕ} (A : Fin m → Fin k → ZMod 2)
    (a : Fin k → ZMod 2) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin m)).filter (fun i => dotProduct (A i) a ≠ 0)).card

lemma h5_weight_le {k m : ℕ} (A : Fin m → Fin k → ZMod 2)
    (a : Fin k → ZMod 2) : h5Weight A a ≤ m := by
  classical
  calc
    h5Weight A a ≤ (Finset.univ : Finset (Fin m)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = m := by simp

lemma h5_distance_le_length {k m d : ℕ} (A : Fin m → Fin k → ZMod 2)
    (hattain : ∃ a, a ≠ 0 ∧ h5Weight A a = d) : d ≤ m := by
  obtain ⟨a, _, ha⟩ := hattain
  simpa only [ha] using h5_weight_le A a

lemma h5_code_injective {k m d : ℕ} (A : Fin m → Fin k → ZMod 2)
    (hd : 0 < d) (hmin : ∀ a, a ≠ 0 → d ≤ h5Weight A a) :
    Function.Injective (fun a : Fin k → ZMod 2 => fun i : Fin m => dotProduct (A i) a) := by
  classical
  intro x y hxy
  by_contra hne
  have hsub : x - y ≠ 0 := sub_ne_zero.mpr hne
  have hz : ∀ i : Fin m, dotProduct (A i) (x - y) = 0 := by
    intro i
    have hi := congrFun hxy i
    change (∑ j, A i j * (x j - y j)) = 0
    simp only [mul_sub, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr hi
  have hw : h5Weight A (x - y) = 0 := by simp [h5Weight, hz]
  have hm := hmin (x - y) hsub
  omega

lemma h5_selector_pair {k : ℕ} (hk : 2 ≤ k) :
    ∃ a b : Fin k → ZMod 2, a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b := by
  let a : Fin k → ZMod 2 := fun i => if i.val = 0 then 1 else 0
  let b : Fin k → ZMod 2 := fun i => if i.val = 1 then 1 else 0
  refine ⟨a, b, ?_, ?_, ?_⟩
  · intro h
    have hi := congrFun h ⟨0, by omega⟩
    simp [a] at hi
  · intro h
    have hi := congrFun h ⟨1, by omega⟩
    simp [b] at hi
  · intro h
    have hi := congrFun h ⟨0, by omega⟩
    simp [a, b] at hi

lemma h5_plane_baseline {k : ℕ} (hk : 2 ≤ k) (m : ℕ)
    (wt : (Fin k → ZMod 2) → ℕ) :
    (2 : ℕ) ^ m ≤ (Finset.univ : Finset ((Fin k → ZMod 2) × (Fin k → ZMod 2))).sup
      (fun w => if w.1 ≠ 0 ∧ w.2 ≠ 0 ∧ w.1 ≠ w.2 then
        2 ^ m + 2 ^ (m - wt w.1) + 2 ^ (m - wt w.2) + 2 ^ (m - wt (w.1 + w.2))
        else 0) := by
  classical
  obtain ⟨a, b, ha, hb, hab⟩ := h5_selector_pair hk
  apply le_trans (b :=
    2 ^ m + 2 ^ (m - wt a) + 2 ^ (m - wt b) + 2 ^ (m - wt (a + b)))
  · exact (Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
  · have h := Finset.le_sup (f := fun w : (Fin k → ZMod 2) × (Fin k → ZMod 2) =>
        if w.1 ≠ 0 ∧ w.2 ≠ 0 ∧ w.1 ≠ w.2 then
          2 ^ m + 2 ^ (m - wt w.1) + 2 ^ (m - wt w.2) + 2 ^ (m - wt (w.1 + w.2))
          else 0) (Finset.mem_univ (a, b))
    change (if a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b then
      2 ^ m + 2 ^ (m - wt a) + 2 ^ (m - wt b) + 2 ^ (m - wt (a + b)) else 0) ≤ _ at h
    rw [ite_eq_left ⟨ha, hb, hab⟩] at h
    exact h

end h5_part_1

namespace Fourier

open Classical

abbrev F2 := ZMod 2

lemma card_filter_add_not {α : Type*} [DecidableEq α] (s : Finset α)
    (p : α → Prop) [DecidablePred p] :
    (s.filter p).card + (s.filter (fun x => ¬ p x)).card = s.card := by
  exact Finset.card_filter_add_card_filter_not (s := s) (p := p)

lemma f2_add_self (a : F2) : a + a = 0 := by
  fin_cases a <;> decide

lemma f2_cases (a : F2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma f2_vec_add_self {ι : Type*} (x : ι → F2) : x + x = 0 := by
  funext i
  exact f2_add_self (x i)

def chi (a : F2) : ℤ := if a = 0 then 1 else -1

lemma chi_zero : chi 0 = 1 := rfl

lemma chi_one : chi 1 = -1 := rfl

lemma chi_add (a b : F2) : chi (a + b) = chi a * chi b := by
  fin_cases a <;> fin_cases b <;> rfl

lemma chi_eq (a b : F2) : (if a = b then (1 : ℤ) else -1) = chi (a + b) := by
  fin_cases a <;> fin_cases b <;> rfl

lemma chi_abs (a : F2) : |chi a| = 1 := by
  fin_cases a <;> decide

lemma chi_le_one (a : F2) : chi a ≤ 1 := by
  fin_cases a <;> decide

lemma chi_sum {α : Type*} (s : Finset α) (f : α → F2) :
    chi (∑ i ∈ s, f i) = ∏ i ∈ s, chi (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [chi]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, chi_add, ih]

lemma sum_chi_addHom {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Finset (ι → F2)) (hadd : ∀ x ∈ H, ∀ y ∈ H, x + y ∈ H)
    (φ : (ι → F2) → F2) (hφ : ∀ x ∈ H, ∀ y ∈ H, φ (x + y) = φ x + φ y) :
    (∑ x ∈ H, chi (φ x)) = if ∀ x ∈ H, φ x = 0 then (H.card : ℤ) else 0 := by
  split_ifs with hall
  · have h1 : ∀ x ∈ H, chi (φ x) = 1 := fun x hx => by rw [hall x hx]; rfl
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one]
  · push Not at hall
    obtain ⟨x₀, hx₀, hne⟩ := hall
    have hx₀1 : φ x₀ = 1 := by
      rcases f2_cases (φ x₀) with h | h
      · exact absurd h hne
      · exact h
    have hbij : ∑ x ∈ H, chi (φ x) = ∑ x ∈ H, chi (φ (x + x₀)) := by
      refine Finset.sum_bij (fun x _ => x + x₀) ?_ ?_ ?_ ?_
      · intro x hx; exact hadd x hx x₀ hx₀
      · intro x _ y _ hxy
        have := congrArg (· + x₀) hxy
        simpa [add_assoc, f2_vec_add_self] using this
      · intro y hy
        refine ⟨y + x₀, hadd y hy x₀ hx₀, ?_⟩
        simp [add_assoc, f2_vec_add_self]
      · intro x _
        congr 2
        rw [add_assoc, f2_vec_add_self, add_zero]
    have hneg : ∑ x ∈ H, chi (φ (x + x₀)) = - ∑ x ∈ H, chi (φ x) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [hφ x hx x₀ hx₀, hx₀1, chi_add, chi_one]
      ring
    linarith

def wt {m : ℕ} (h : Fin m → F2) : ℕ :=
  (Finset.univ.filter (fun i : Fin m => h i = 1)).card

lemma wt_le {m : ℕ} (h : Fin m → F2) : wt h ≤ m := by
  unfold wt
  calc (Finset.univ.filter (fun i : Fin m => h i = 1)).card
      ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_filter_le _ _
    _ = m := Finset.card_fin m

lemma pow_two_wt_fourier {m : ℕ} (u : Fin m → F2) :
    (2 : ℤ) ^ m * (2 : ℤ) ^ (m - wt u) =
      ∑ S : Finset (Fin m), (3 : ℤ) ^ (Finset.univ \ S).card * chi (∑ i ∈ S, u i) := by
  have hprod : (2 : ℤ) ^ m * (2 : ℤ) ^ (m - wt u) = ∏ i : Fin m, (chi (u i) + 3) := by
    have hfactor : ∀ i : Fin m, chi (u i) + 3 = (2 : ℤ) * (if u i = 1 then 1 else 2) := by
      intro i
      rcases f2_cases (u i) with h | h <;> rw [h] <;> decide
    simp_rw [hfactor, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_fin]
    congr 1
    rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
    congr 1
    have hcompl : (Finset.univ.filter (fun i : Fin m => u i = 1)).card +
        (Finset.univ.filter (fun i : Fin m => ¬ u i = 1)).card = m := by
      simpa [Finset.card_fin] using card_filter_add_not (Finset.univ : Finset (Fin m)) (fun i => u i = 1)
    unfold wt
    omega
  rw [hprod, Finset.prod_add]
  have hpow : (Finset.univ : Finset (Fin m)).powerset = Finset.univ := by
    ext S; simp
  rw [hpow]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.prod_const, ← chi_sum, mul_comm]

lemma coset_wt_le {m : ℕ} (H : Finset (Fin m → F2))
    (hadd : ∀ x ∈ H, ∀ y ∈ H, x + y ∈ H) (u0 : Fin m → F2) :
    ∑ u ∈ H, (2 : ℤ) ^ (m - wt (u + u0)) ≤ ∑ u ∈ H, (2 : ℤ) ^ (m - wt u) := by
  suffices h : (2 : ℤ) ^ m * ∑ u ∈ H, (2 : ℤ) ^ (m - wt (u + u0)) ≤
      (2 : ℤ) ^ m * ∑ u ∈ H, (2 : ℤ) ^ (m - wt u) from
    le_of_mul_le_mul_left h (by positivity)
  rw [Finset.mul_sum, Finset.mul_sum]
  simp_rw [pow_two_wt_fourier]
  rw [Finset.sum_comm, Finset.sum_comm (s := H)]
  refine Finset.sum_le_sum fun S _ => ?_
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hshift : ∑ u ∈ H, chi (∑ i ∈ S, (u + u0) i) =
      chi (∑ i ∈ S, u0 i) * ∑ u ∈ H, chi (∑ i ∈ S, u i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [Pi.add_apply, Finset.sum_add_distrib, chi_add]
    ring
  rw [hshift]
  have hnonneg : 0 ≤ ∑ u ∈ H, chi (∑ i ∈ S, u i) := by
    rw [sum_chi_addHom H hadd (fun u => ∑ i ∈ S, u i)
      (fun x _ y _ => by simp only [Pi.add_apply, Finset.sum_add_distrib])]
    split_ifs <;> positivity
  calc chi (∑ i ∈ S, u0 i) * ∑ u ∈ H, chi (∑ i ∈ S, u i)
      ≤ 1 * ∑ u ∈ H, chi (∑ i ∈ S, u i) :=
        mul_le_mul_of_nonneg_right (chi_le_one _) hnonneg
    _ = ∑ u ∈ H, chi (∑ i ∈ S, u i) := one_mul _

lemma wt_eq_nonzero {m : ℕ} (u : Fin m → F2) :
    wt u = ((Finset.univ : Finset (Fin m)).filter (fun i => u i ≠ 0)).card := by
  unfold wt
  congr 1
  ext i
  rcases f2_cases (u i) with h | h <;> simp [h]

lemma coset_weight_le {m : ℕ} (H : Finset (Fin m → F2))
    (hadd : ∀ x ∈ H, ∀ y ∈ H, x + y ∈ H) (v : Fin m → F2) :
    ∑ u ∈ H, (2 : ℤ) ^ (m - ((Finset.univ : Finset (Fin m)).filter
        (fun i => (u + v) i ≠ 0)).card) ≤
      ∑ u ∈ H, (2 : ℤ) ^ (m - ((Finset.univ : Finset (Fin m)).filter
        (fun i => u i ≠ 0)).card) := by
  simpa only [wt_eq_nonzero] using coset_wt_le H hadd v

lemma submodule_coset_wt_le {m : ℕ}
    (U : Submodule F2 (Fin m → F2)) (v : Fin m → F2) :
    (∑ u : U, (2 : ℤ) ^ (m - wt ((u : Fin m → F2) + v))) ≤
      ∑ u : U, (2 : ℤ) ^ (m - wt (u : Fin m → F2)) := by
  classical
  let H : Finset (Fin m → F2) := Finset.univ.filter (fun u => u ∈ U)
  have hmem (u : Fin m → F2) : u ∈ H ↔ u ∈ U := by simp [H]
  have hadd : ∀ x ∈ H, ∀ y ∈ H, x + y ∈ H := by
    intro x hx y hy
    exact (hmem _).mpr (U.add_mem ((hmem _).mp hx) ((hmem _).mp hy))
  have h := coset_wt_le H hadd v
  rw [Finset.sum_subtype H hmem (fun u => (2 : ℤ) ^ (m - wt (u + v))),
    Finset.sum_subtype H hmem (fun u => (2 : ℤ) ^ (m - wt u))] at h
  exact h

lemma linear_code_coset_wt_le {k m : ℕ} (H : Finset (Fin k → F2))
    (hadd : ∀ x ∈ H, ∀ y ∈ H, x + y ∈ H)
    (L : (Fin k → F2) →ₗ[F2] (Fin m → F2)) (v : Fin m → F2) :
    ∑ u ∈ H, (2 : ℤ) ^ (m - wt (L u + v)) ≤
      ∑ u ∈ H, (2 : ℤ) ^ (m - wt (L u)) := by
  suffices h : (2 : ℤ) ^ m * ∑ u ∈ H, (2 : ℤ) ^ (m - wt (L u + v)) ≤
      (2 : ℤ) ^ m * ∑ u ∈ H, (2 : ℤ) ^ (m - wt (L u)) from
    le_of_mul_le_mul_left h (by positivity)
  rw [Finset.mul_sum, Finset.mul_sum]
  simp_rw [pow_two_wt_fourier]
  rw [Finset.sum_comm, Finset.sum_comm (s := H)]
  refine Finset.sum_le_sum fun S _ => ?_
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hshift : ∑ u ∈ H, chi (∑ i ∈ S, (L u + v) i) =
      chi (∑ i ∈ S, v i) * ∑ u ∈ H, chi (∑ i ∈ S, L u i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [Pi.add_apply, Finset.sum_add_distrib, chi_add]
    ring
  rw [hshift]
  have hnonneg : 0 ≤ ∑ u ∈ H, chi (∑ i ∈ S, L u i) := by
    rw [sum_chi_addHom H hadd (fun u => ∑ i ∈ S, L u i)
      (fun x _ y _ => by simp only [map_add, Pi.add_apply, Finset.sum_add_distrib])]
    split_ifs <;> positivity
  calc chi (∑ i ∈ S, v i) * ∑ u ∈ H, chi (∑ i ∈ S, L u i)
      ≤ 1 * ∑ u ∈ H, chi (∑ i ∈ S, L u i) :=
        mul_le_mul_of_nonneg_right (chi_le_one _) hnonneg
    _ = ∑ u ∈ H, chi (∑ i ∈ S, L u i) := one_mul _

lemma linear_code_submodule_coset_weight_le {k m : ℕ}
    (U : Submodule F2 (Fin k → F2))
    (L : (Fin k → F2) →ₗ[F2] (Fin m → F2)) (v : Fin m → F2) :
    (∑ u : U, (2 : ℤ) ^ (m - ((Finset.univ : Finset (Fin m)).filter
        (fun i => (L u + v) i ≠ 0)).card)) ≤
      ∑ u : U, (2 : ℤ) ^ (m - ((Finset.univ : Finset (Fin m)).filter
        (fun i => L u i ≠ 0)).card) := by
  classical
  let H : Finset (Fin k → F2) := Finset.univ.filter (fun u => u ∈ U)
  have hmem (u : Fin k → F2) : u ∈ H ↔ u ∈ U := by simp [H]
  have hadd : ∀ x ∈ H, ∀ y ∈ H, x + y ∈ H := by
    intro x hx y hy
    exact (hmem _).mpr (U.add_mem ((hmem _).mp hx) ((hmem _).mp hy))
  have h := linear_code_coset_wt_le H hadd L v
  rw [Finset.sum_subtype H hmem (fun u => (2 : ℤ) ^ (m - wt (L u + v))),
    Finset.sum_subtype H hmem (fun u => (2 : ℤ) ^ (m - wt (L u)))] at h
  simpa only [wt_eq_nonzero] using h

end Fourier

section h5_part_2

lemma h5_binary_module_self_add {S : Type*} [AddCommGroup S] [Module (ZMod 2) S]
    (a : S) : a+a=0 := by
  have h : (2 : ZMod 2) = 0 := by decide
  calc
    a+a = (2 : ZMod 2) • a := (two_smul (ZMod 2) a).symm
    _ = 0 := by rw [h, zero_smul]

lemma h5_binary_pair_kernel {S : Type*} [AddCommGroup S] [Module (ZMod 2) S]
    (a b : S) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (s t : ZMod 2) (hz : s • a + t • b = 0) : s = 0 ∧ t = 0 := by
  have hbit (x : ZMod 2) : x = 0 ∨ x = 1 := by
    fin_cases x
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hbit s with rfl | rfl <;> rcases hbit t with rfl | rfl
  · exact ⟨rfl,rfl⟩
  · simp only [zero_smul, one_smul, zero_add] at hz
    exact False.elim (hb hz)
  · simp only [zero_smul, one_smul, add_zero] at hz
    exact False.elim (ha hz)
  · simp only [one_smul] at hz
    have hh : a = b := by
      calc
        a = a+(b+b) := by rw [h5_binary_module_self_add b, add_zero]
        _ = (a+b)+b := (add_assoc _ _ _).symm
        _ = b := by rw [hz, zero_add]
    exact False.elim (hab hh)

noncomputable def h5PlaneMap {S : Type*} [AddCommGroup S] [Module (ZMod 2) S]
    (a b : S) : (Fin 2 → ZMod 2) →ₗ[ZMod 2] S where
  toFun := fun x => x 0 • a + x 1 • b
  map_add' := by
    intro x y
    simp only [Pi.add_apply, add_smul]
    abel
  map_smul' := by
    intro c x
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, smul_add, RingHom.id_apply]

lemma h5_plane_map_injective {S : Type*} [AddCommGroup S] [Module (ZMod 2) S]
    (a b : S) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    Function.Injective (h5PlaneMap a b) := by
  intro x y hxy
  have hz : h5PlaneMap a b (x-y) = 0 := by rw [map_sub, hxy, sub_self]
  have hk := h5_binary_pair_kernel a b ha hb hab ((x-y) 0) ((x-y) 1) hz
  apply sub_eq_zero.mp
  funext i
  fin_cases i
  · exact hk.1
  · exact hk.2

end h5_part_2

section h5_part_3

lemma h5_two_add (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

lemma h5_plane_interpolation {S : Type*} [AddCommGroup S] [Module (ZMod 2) S]
    (h : S → ZMod 2) (a u v : S) (s t : ZMod 2) :
    h (a + s • u + t • v) =
      h a + (h (a + u) + h a) * s + (h (a + v) + h a) * t +
      (h (a + u + v) + h (a + u) + h (a + v) + h a) * s * t := by
  have hb (x : ZMod 2) : x = 0 ∨ x = 1 := by
    fin_cases x
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hb s with rfl | rfl <;> rcases hb t with rfl | rfl <;>
    simp only [zero_smul, one_smul, add_zero, mul_zero, mul_one] <;> ring_nf <;>
    simp only [show (2 : ZMod 2) = 0 by decide, show (4 : ZMod 2) = 0 by decide,
      mul_zero, add_zero, zero_add]

noncomputable def h5Chi (x : ZMod 2) : ℤ := if x = 0 then 1 else -1

lemma h5_chi_zero : h5Chi 0 = 1 := by simp [h5Chi]

lemma h5_chi_add (x y : ZMod 2) : h5Chi (x+y) = h5Chi x * h5Chi y := by
  fin_cases x <;> fin_cases y <;> decide

lemma h5_chi_sum {I : Type*} (s : Finset I) (f : I → ZMod 2) :
    h5Chi (∑ i ∈ s, f i) = ∏ i ∈ s, h5Chi (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [h5_chi_zero]
  | insert a s ha ih => simp [ha, h5_chi_add, ih]

lemma h5_pair_sum (c : ZMod 2) :
    (∑ p : ZMod 2 × ZMod 2, h5Chi (c * p.1 * p.2)) =
      if c = 0 then 4 else 2 := by
  fin_cases c <;> decide

lemma h5_data_factor {m : ℕ} (c : Fin m → ZMod 2) :
    (∑ u : Fin m → ZMod 2, ∑ v : Fin m → ZMod 2,
      h5Chi (∑ i, c i * u i * v i)) =
      ∏ i : Fin m, (if c i = 0 then (4 : ℤ) else 2) := by
  classical
  let F : Fin m → ZMod 2 × ZMod 2 → ℤ := fun i p => h5Chi (c i * p.1 * p.2)
  have hps := Fintype.prod_sum F
  have hpair : ∀ i, (∑ p : ZMod 2 × ZMod 2, F i p) =
      if c i = 0 then 4 else 2 := fun i => h5_pair_sum (c i)
  simp_rw [← hpair]
  rw [hps]
  let ep : ((Fin m → ZMod 2) × (Fin m → ZMod 2)) ≃ (Fin m → ZMod 2 × ZMod 2) :=
    { toFun := fun p i => (p.1 i, p.2 i)
      invFun := fun f => (fun i => (f i).1, fun i => (f i).2)
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := fun _ => rfl }
  rw [← Fintype.sum_prod_type', ← ep.sum_comp]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [h5_chi_sum]
  rfl

lemma h5_data_sum_weight {m : ℕ} (c : Fin m → ZMod 2) :
    (∑ u : Fin m → ZMod 2, ∑ v : Fin m → ZMod 2,
      h5Chi (∑ i, c i * u i * v i)) =
      (2 : ℤ) ^ m * 2 ^ (m - ((Finset.univ : Finset (Fin m)).filter (fun i => c i ≠ 0)).card) := by
  classical
  rw [h5_data_factor]
  have hp (i : Fin m) : (if c i = 0 then (4 : ℤ) else 2) =
      2 * (if c i = 0 then 2 else 1) := by split_ifs <;> norm_num
  simp_rw [hp]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  rw [Finset.prod_ite]
  simp only [Finset.prod_const, one_pow, mul_one]
  congr 1
  have hc := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin m))) (p := fun i => c i = 0)
  simp only [Finset.card_univ, Fintype.card_fin] at hc
  change ((Finset.univ : Finset (Fin m)).filter (fun i => c i = 0)).card +
    ((Finset.univ : Finset (Fin m)).filter (fun i => c i ≠ 0)).card = m at hc
  omega

lemma h5_sum_binary {R : Type*} [AddCommMonoid R] (f : ZMod 2 → R) :
    (∑ s : ZMod 2, f s) = f 0 + f 1 := by
  exact Fin.sum_univ_two f

lemma h5_four_selector_values {S R : Type*} [AddCommGroup S] [Module (ZMod 2) S]
    [AddCommMonoid R] (f : S → R) (a b : S) :
    (∑ s : ZMod 2, ∑ t : ZMod 2, f (s • a + t • b)) =
      f 0 + f a + f b + f (a+b) := by
  simp only [h5_sum_binary, zero_smul, one_smul, zero_add, add_zero]
  ac_rfl

lemma h5_plane_data_character {k m : ℕ} (A : Fin m → Fin k → ZMod 2)
    (a b : Fin k → ZMod 2) :
    let wt := fun w : Fin k → ZMod 2 =>
      ((Finset.univ : Finset (Fin m)).filter (fun i => dotProduct (A i) w ≠ 0)).card
    (∑ s : ZMod 2, ∑ t : ZMod 2,
      ∑ u : Fin m → ZMod 2, ∑ v : Fin m → ZMod 2,
        h5Chi (∑ i, dotProduct (A i) (s • a + t • b) * u i * v i)) =
      (2 : ℤ)^m * (2^m + 2^(m-wt a) + 2^(m-wt b) + 2^(m-wt (a+b))) := by
  classical
  dsimp only
  rw [h5_four_selector_values (fun w =>
    ∑ u : Fin m → ZMod 2, ∑ v : Fin m → ZMod 2,
      h5Chi (∑ i, dotProduct (A i) w * u i * v i)) a b]
  simp_rw [h5_data_sum_weight]
  simp only [dotProduct_zero, ne_eq, not_true_eq_false, Finset.filter_false,
    Finset.card_empty, Nat.sub_zero]
  ring

end h5_part_3
section h5_part_4

lemma h5_sum_plane_map {R S : Type*} [AddCommMonoid R] [AddCommGroup S]
    [Module (ZMod 2) S] (f : S → R) (a b : S) :
    (∑ x : Fin 2 → ZMod 2, f (h5PlaneMap a b x)) = f 0 + f a + f b + f (a+b) := by
  let e := finTwoArrowEquiv (ZMod 2)
  rw [← e.symm.sum_comp]
  change (∑ x : ZMod 2 × ZMod 2, f (x.1 • a + x.2 • b)) = _
  rw [Fintype.sum_prod_type]
  exact h5_four_selector_values f a b

lemma h5_four_shift_weight_le {k m : ℕ}
    (L : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2))
    (a b v : Fin k → ZMod 2) :
    let f := fun w : Fin k → ZMod 2 => (2 : ℤ)^(m-Fourier.wt (L w))
    f v + f (a+v) + f (b+v) + f (a+b+v) ≤ f 0 + f a + f b + f (a+b) := by
  classical
  dsimp only
  let P := h5PlaneMap a b
  have h := Fourier.linear_code_coset_wt_le Finset.univ
    (fun _ _ _ _ => Finset.mem_univ _) (L.comp P) (L v)
  simp only [LinearMap.comp_apply] at h
  have hleft : (∑ x : Fin 2 → ZMod 2, (2:ℤ)^(m-Fourier.wt (L (P x)+L v))) =
      (2:ℤ)^(m-Fourier.wt (L v)) + (2:ℤ)^(m-Fourier.wt (L (a+v))) +
        (2:ℤ)^(m-Fourier.wt (L (b+v))) + (2:ℤ)^(m-Fourier.wt (L (a+b+v))) := by
    simp_rw [← map_add]
    have hs := h5_sum_plane_map (fun w => (2:ℤ)^(m-Fourier.wt (L (w+v)))) a b
    simpa only [zero_add] using hs
  rw [hleft] at h
  dsimp only [P] at h
  rw [h5_sum_plane_map (fun w => (2:ℤ)^(m-Fourier.wt (L w))) a b] at h
  exact h

open Classical in
lemma h5_subgroup_average_plane {k m : ℕ}
    (U : Submodule (ZMod 2) (Fin k → ZMod 2))
    (L : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2))
    (a b : U) :
    let f := fun w : Fin k → ZMod 2 => (2:ℤ)^(m-Fourier.wt (L w))
    4 * (∑ u : U, f u) ≤ Fintype.card U * (f 0 + f a + f b + f ((a:Fin k→ZMod 2)+b)) := by
  classical
  dsimp only
  let f := fun w : U => (2:ℤ)^(m-Fourier.wt (L w))
  have h (u : U) := h5_four_shift_weight_le L a b u
  dsimp only at h
  have ht : ∀ v : U, (∑ u : U, f (v+u)) = ∑ u : U, f u := by
    intro v
    exact Equiv.sum_comp (Equiv.addLeft v) f
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun u _ => h u)
  change (∑ u : U, (f u + f (a+u) + f (b+u) + f ((a+b)+u))) ≤ _ at hh
  simp only [Finset.sum_add_distrib, ht, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hh
  convert hh using 1 <;> ring

end h5_part_4

section h5_part_5

lemma h5_linear_coord_dot {n : ℕ} (f : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) :
    ∃ l : Fin n → ZMod 2, ∀ x, f x = dotProduct l x := by
  classical
  refine ⟨fun j => f (Pi.single j 1),?_⟩
  intro x
  have hx : x = ∑ j, x j • Pi.single j (1 : ZMod 2) := by
    ext i
    simp [Pi.single_apply]
  conv_lhs => rw [hx, map_sum]
  simp only [dotProduct, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma h5_two_linear_function_quad {n : ℕ}
    (f g : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) (z α β γ : ZMod 2) :
    ∃ (l : Fin n → ZMod 2) (M : Fin n → Fin n → ZMod 2), ∀ x,
      z + α*f x + β*g x + γ*f x*g x =
        z + dotProduct l x + ∑ i, ∑ j, M i j*x i*x j := by
  obtain ⟨u,hu⟩ := h5_linear_coord_dot f
  obtain ⟨v,hv⟩ := h5_linear_coord_dot g
  refine ⟨fun i => α*u i+β*v i,fun i j => γ*u j*v i,?_⟩
  intro x
  rw [hu,hv]
  have hl : dotProduct (fun i => α*u i+β*v i) x =
      α*dotProduct u x+β*dotProduct v x := by
    simp only [dotProduct, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  have hq : (∑ i, ∑ j, γ*u j*v i*x i*x j) = γ*dotProduct u x*dotProduct v x := by
    simp only [dotProduct, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hl,hq]
  ring

lemma h5_selector_h_quad {n k : ℕ} (h : (Fin k → ZMod 2) → ZMod 2)
    (a b : Fin k → ZMod 2)
    (T : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin 2 → ZMod 2)) :
    ∃ (z : ZMod 2) (l : Fin n → ZMod 2) (M : Fin n → Fin n → ZMod 2), ∀ x,
      h ((T x) 0 • a + (T x) 1 • b) =
        z + dotProduct l x + ∑ i, ∑ j, M i j * x i * x j := by
  let f := (LinearMap.proj 0).comp T
  let g := (LinearMap.proj 1).comp T
  obtain ⟨l,M,hq⟩ := h5_two_linear_function_quad f g (h 0)
    (h a+h 0) (h b+h 0) (h (a+b)+h a+h b+h 0)
  refine ⟨h 0,l,M,?_⟩
  intro x
  have hp := h5_plane_interpolation h 0 a b ((T x) 0) ((T x) 1)
  simp only [zero_add] at hp
  exact hp.trans (hq x)

lemma h5_plane_domain_equiv (m r : ℕ) :
    Nonempty ((Fin (2*m+r+2) → ZMod 2) ≃ₗ[ZMod 2]
      ((Fin 2 → ZMod 2) × ((Fin m → ZMod 2) × ((Fin m → ZMod 2) × (Fin r → ZMod 2))))) := by
  refine ⟨LinearEquiv.ofFinrankEq _ _ ?_⟩
  simp only [Module.finrank_pi, Fintype.card_fin, Module.finrank_prod]
  omega

lemma h5_same_selector_sign (x y : ZMod 2) :
    (if x+y=x then (1:ℤ) else -1) = h5Chi y := by
  fin_cases x <;> fin_cases y <;> decide

lemma h5_plane_with_noise_sum {k m r : ℕ} (A : Fin m → Fin k → ZMod 2)
    (a b : Fin k → ZMod 2) :
    (∑ s : Fin 2 → ZMod 2, ∑ u : Fin m → ZMod 2, ∑ v : Fin m → ZMod 2,
      ∑ _z : Fin r → ZMod 2, h5Chi (∑ i, dotProduct (A i) (h5PlaneMap a b s)*u i*v i)) =
      (2:ℤ)^(m+r) *
        (2^m + 2^(m-((Finset.univ : Finset (Fin m)).filter (fun i => dotProduct (A i) a ≠ 0)).card) +
         2^(m-((Finset.univ : Finset (Fin m)).filter (fun i => dotProduct (A i) b ≠ 0)).card) +
         2^(m-((Finset.univ : Finset (Fin m)).filter (fun i => dotProduct (A i) (a+b) ≠ 0)).card)) := by
  classical
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    ZMod.card, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  simp_rw [← Finset.mul_sum]
  rw [h5_sum_plane_map (fun w : Fin k → ZMod 2 =>
    ∑ u : Fin m → ZMod 2, ∑ v : Fin m → ZMod 2,
      h5Chi (∑ i, dotProduct (A i) w*u i*v i)) a b]
  simp_rw [h5_data_sum_weight]
  simp only [dotProduct_zero, ne_eq, not_true_eq_false, Finset.filter_false,
    Finset.card_empty, Nat.sub_zero, pow_add]
  ring

lemma h5_explicit_plane_attainment {n k m r : ℕ}
    (e : (Fin n → ZMod 2) ≃ₗ[ZMod 2]
      ((Fin k → ZMod 2) × ((Fin m → ZMod 2) × ((Fin m → ZMod 2) × (Fin r → ZMod 2)))))
    (A : Fin m → Fin k → ZMod 2) (h : (Fin k → ZMod 2) → ZMod 2)
    (a b : Fin k → ZMod 2) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    ∃ (L : (Fin (2*m+r+2) → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
      (q : (Fin (2*m+r+2) → ZMod 2) → ZMod 2),
      Function.Injective L ∧
      (∃ (z : ZMod 2) (l : Fin (2*m+r+2) → ZMod 2)
        (M : Fin (2*m+r+2) → Fin (2*m+r+2) → ZMod 2),
        ∀ x, q x = z + dotProduct l x + ∑ i, ∑ j, M i j*x i*x j) ∧
      (∑ x : Fin (2*m+r+2) → ZMod 2,
        if h (e (L x)).1 + ∑ i, dotProduct (A i) (e (L x)).1 *
          (e (L x)).2.1 i * (e (L x)).2.2.1 i = q x then (1:ℤ) else -1) =
        (2:ℤ)^(m+r) *
        (2^m + 2^(m-((Finset.univ : Finset (Fin m)).filter (fun i => dotProduct (A i) a ≠ 0)).card) +
         2^(m-((Finset.univ : Finset (Fin m)).filter (fun i => dotProduct (A i) b ≠ 0)).card) +
         2^(m-((Finset.univ : Finset (Fin m)).filter (fun i => dotProduct (A i) (a+b) ≠ 0)).card)) := by
  classical
  obtain ⟨D⟩ := h5_plane_domain_equiv m r
  let K := (h5PlaneMap a b).prodMap
    (LinearMap.id : ((Fin m → ZMod 2) × ((Fin m → ZMod 2) × (Fin r → ZMod 2))) →ₗ[ZMod 2]
      ((Fin m → ZMod 2) × ((Fin m → ZMod 2) × (Fin r → ZMod 2))))
  let L := e.symm.toLinearMap.comp (K.comp D.toLinearMap)
  let T := (LinearMap.fst (ZMod 2) (Fin 2 → ZMod 2)
    ((Fin m → ZMod 2) × ((Fin m → ZMod 2) × (Fin r → ZMod 2)))).comp D.toLinearMap
  let q := fun x => h (h5PlaneMap a b (T x))
  have hK : Function.Injective K := by
    intro x y hxy
    apply Prod.ext
    · exact h5_plane_map_injective a b ha hb hab (congrArg Prod.fst hxy)
    · have hs := congrArg Prod.snd hxy
      exact hs
  refine ⟨L,q,e.symm.injective.comp (hK.comp D.injective),?_,?_⟩
  · exact h5_selector_h_quad h a b T
  · have hEL (x) : e (L x) = K (D x) := by
      dsimp only [L,LinearMap.comp_apply,LinearEquiv.coe_coe]
      exact e.apply_symm_apply _
    simp_rw [hEL]
    change (∑ x, if h (h5PlaneMap a b (D x).1) +
      ∑ i, dotProduct (A i) (h5PlaneMap a b (D x).1)*(D x).2.1 i*(D x).2.2.1 i =
        h (h5PlaneMap a b (D x).1) then (1:ℤ) else -1) = _
    simp_rw [h5_same_selector_sign]
    rw [← D.symm.toEquiv.sum_comp]
    have hDD (w) : D (D.symm.toEquiv w) = w := D.apply_symm_apply w
    simp_rw [hDD]
    simp only [Fintype.sum_prod_type]
    exact h5_plane_with_noise_sum (r := r) A a b

end h5_part_5
section h5_part_6

lemma h5_best_plane {k : ℕ} (hk : 2 ≤ k) (m : ℕ) (wt : (Fin k → ZMod 2) → ℕ) :
    ∃ a b : Fin k → ZMod 2, a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧
      (2:ℕ)^m + 2^(m-wt a) + 2^(m-wt b) + 2^(m-wt (a+b)) =
      (Finset.univ : Finset ((Fin k → ZMod 2) × (Fin k → ZMod 2))).sup
        (fun w => if w.1 ≠ 0 ∧ w.2 ≠ 0 ∧ w.1 ≠ w.2 then
          2^m+2^(m-wt w.1)+2^(m-wt w.2)+2^(m-wt (w.1+w.2)) else 0) := by
  classical
  let mass := fun w : (Fin k → ZMod 2) × (Fin k → ZMod 2) =>
    if w.1 ≠ 0 ∧ w.2 ≠ 0 ∧ w.1 ≠ w.2 then
      (2:ℕ)^m+2^(m-wt w.1)+2^(m-wt w.2)+2^(m-wt (w.1+w.2)) else 0
  have hbase : 2^m ≤ (Finset.univ : Finset ((Fin k → ZMod 2) × (Fin k → ZMod 2))).sup mass :=
    h5_plane_baseline hk m wt
  obtain ⟨w,hw,hmax⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty mass
  have hvalid : w.1 ≠ 0 ∧ w.2 ≠ 0 ∧ w.1 ≠ w.2 := by
    by_contra hn
    have hz : mass w = 0 := by simp only [mass,ite_eq_right_iff]; exact fun hh => False.elim (hn hh)
    rw [hmax,hz] at hbase
    have hp : 0 < (2:ℕ)^m := Nat.pow_pos (by decide)
    omega
  refine ⟨w.1,w.2,hvalid.1,hvalid.2.1,hvalid.2.2,?_⟩
  simpa only [mass,ite_eq_left_iff,ite_eq_left hvalid] using hmax.symm

lemma h5_posted_flat_attainment {n k m r : ℕ} (hk : 2 ≤ k)
    (e : (Fin n → ZMod 2) ≃ₗ[ZMod 2]
      ((Fin k → ZMod 2) × ((Fin m → ZMod 2) × ((Fin m → ZMod 2) × (Fin r → ZMod 2)))))
    (A : Fin m → Fin k → ZMod 2) (h : (Fin k → ZMod 2) → ZMod 2) :
    let wt := fun a => ((Finset.univ : Finset (Fin m)).filter (fun i => dotProduct (A i) a ≠ 0)).card
    let plane := (Finset.univ : Finset ((Fin k → ZMod 2) × (Fin k → ZMod 2))).sup
      (fun w => if w.1 ≠ 0 ∧ w.2 ≠ 0 ∧ w.1 ≠ w.2 then
        (2:ℕ)^m+2^(m-wt w.1)+2^(m-wt w.2)+2^(m-wt (w.1+w.2)) else 0)
    ∃ (L : (Fin (2*m+r+2) → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
      (q : (Fin (2*m+r+2) → ZMod 2) → ZMod 2),
      Function.Injective L ∧
      (∃ (z : ZMod 2) (l : Fin (2*m+r+2) → ZMod 2)
        (M : Fin (2*m+r+2) → Fin (2*m+r+2) → ZMod 2),
        ∀ x, q x = z + dotProduct l x + ∑ i, ∑ j, M i j*x i*x j) ∧
      2^(m+2) * (∑ x : Fin (2*m+r+2) → ZMod 2,
        if h (e (L x)).1 + ∑ i, dotProduct (A i) (e (L x)).1 *
          (e (L x)).2.1 i * (e (L x)).2.2.1 i = q x then (1:ℤ) else -1).natAbs =
        2^(2*m+r+2) * plane := by
  classical
  dsimp only
  let wt := fun a : Fin k → ZMod 2 =>
    ((Finset.univ : Finset (Fin m)).filter (fun i => dotProduct (A i) a ≠ 0)).card
  let plane := (Finset.univ : Finset ((Fin k → ZMod 2) × (Fin k → ZMod 2))).sup
    (fun w => if w.1 ≠ 0 ∧ w.2 ≠ 0 ∧ w.1 ≠ w.2 then
      (2:ℕ)^m+2^(m-wt w.1)+2^(m-wt w.2)+2^(m-wt (w.1+w.2)) else 0)
  obtain ⟨a,b,ha,hb,hab,hm⟩ := h5_best_plane hk m wt
  obtain ⟨L,q,hL,hq,hs⟩ := h5_explicit_plane_attainment e A h a b ha hb hab
  refine ⟨L,q,hL,hq,?_⟩
  have hint : (2:ℤ)^m+2^(m-wt a)+2^(m-wt b)+2^(m-wt (a+b)) = (plane:ℤ) := by
    exact_mod_cast hm
  change _ = (2:ℤ)^(m+r) * ((2:ℤ)^m+2^(m-wt a)+2^(m-wt b)+2^(m-wt (a+b))) at hs
  rw [hint] at hs
  have hn := congrArg Int.natAbs hs
  simp only [Int.natAbs_mul,Int.natAbs_pow] at hn
  rw [hn]
  change (2:ℕ)^(m+2) * (2^(m+r)*plane) = 2^(2*m+r+2)*plane
  rw [← Nat.mul_assoc,← pow_add]
  rw [show m+2+(m+r) = 2*m+r+2 by omega]

end h5_part_6

section h5_part_7

lemma h5_cancel_active_weight {m : ℕ} (c : Fin m → ZMod 2) (j : Fin m)
    (hj : c j ≠ 0) :
    ((Finset.univ : Finset (Fin m)).filter (fun i => (c i + if i=j then 1 else 0) ≠ 0)).card + 1 =
      ((Finset.univ : Finset (Fin m)).filter (fun i => c i ≠ 0)).card := by
  classical
  have hcj : c j = 1 := by
    have hc : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
    exact hc _ hj
  let S := (Finset.univ : Finset (Fin m)).filter (fun i => c i ≠ 0)
  have hS : j ∈ S := by simp [S,hj]
  have heq : (Finset.univ.filter (fun i : Fin m => (c i + if i=j then 1 else 0) ≠ 0)) = S.erase j := by
    ext i
    by_cases hi : i=j
    · subst i
      simp [S,hcj,show (1:ZMod 2)+1=0 by decide]
    · simp [S,hi]
  rw [heq]
  exact Finset.card_erase_add_one hS

lemma h5_cancel_active_sum {m : ℕ} (c u v : Fin m → ZMod 2) (j : Fin m) :
    (∑ i, c i*u i*v i) + u j*v j =
      ∑ i, (c i + if i=j then 1 else 0)*u i*v i := by
  classical
  simp only [add_mul,Finset.sum_add_distrib]
  congr 1
  symm
  rw [Finset.sum_eq_single j]
  · simp
  · intro i hi hij
    simp [hij]
  · simp

lemma h5_line_h_interpolation {S : Type*} [AddCommGroup S] [Module (ZMod 2) S]
    (h : S → ZMod 2) (a : S) (s : ZMod 2) :
    h (s • a) = h 0 + (h a+h 0)*s := by
  have hbit : s=0 ∨ s=1 := by
    fin_cases s
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hbit with rfl | rfl
  · simp
  · simp only [one_smul,mul_one]
    have hh : h 0+h 0=0 := by
      have hh : ∀ x : ZMod 2, x+x=0 := by decide
      exact hh _
    calc
      h a = h a + (h 0+h 0) := by rw [hh,add_zero]
      _ = h 0+(h a+h 0) := by ac_rfl

lemma h5_line_data_sum {m : ℕ} (c : Fin m → ZMod 2) (j : Fin m) (hj : c j ≠ 0) :
    (∑ s : ZMod 2, ∑ u : Fin m → ZMod 2, ∑ v : Fin m → ZMod 2,
      h5Chi (s*(∑ i, c i*u i*v i) + s*u j*v j)) =
      (2:ℤ)^m * (2^m + 2^(m+1-((Finset.univ : Finset (Fin m)).filter (fun i => c i ≠ 0)).card)) := by
  classical
  rw [h5_sum_binary]
  simp only [zero_mul,zero_add,one_mul,h5_chi_zero]
  simp_rw [h5_cancel_active_sum]
  rw [h5_data_sum_weight]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,
    ZMod.card,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat,mul_one]
  have hw := h5_cancel_active_weight c j hj
  have he : m - ((Finset.univ : Finset (Fin m)).filter
      (fun i => (c i+if i=j then 1 else 0) ≠ 0)).card =
      m+1-((Finset.univ : Finset (Fin m)).filter (fun i => c i ≠ 0)).card := by omega
  rw [he]
  ring

lemma h5_line_with_noise_sum {m r : ℕ} (c : Fin m → ZMod 2) (j : Fin m) (hj : c j ≠ 0) :
    (∑ s : ZMod 2, ∑ u : Fin m → ZMod 2, ∑ v : Fin m → ZMod 2,
      ∑ _z : Fin r → ZMod 2, h5Chi (s*(∑ i, c i*u i*v i) + s*u j*v j)) =
      (2:ℤ)^(m+r) * (2^m + 2^(m+1-((Finset.univ : Finset (Fin m)).filter (fun i => c i ≠ 0)).card)) := by
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,
    ZMod.card,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
  simp_rw [← Finset.mul_sum]
  rw [h5_line_data_sum c j hj,pow_add]
  ring

lemma h5_line_domain_equiv (m r : ℕ) :
    Nonempty ((Fin (2*m+r+1) → ZMod 2) ≃ₗ[ZMod 2]
      (ZMod 2 × ((Fin m → ZMod 2) × ((Fin m → ZMod 2) × (Fin r → ZMod 2))))) := by
  refine ⟨LinearEquiv.ofFinrankEq _ _ ?_⟩
  simp only [Module.finrank_pi,Fintype.card_fin,Module.finrank_prod,Module.finrank_self]
  omega

noncomputable def h5LineMap {S : Type*} [AddCommGroup S] [Module (ZMod 2) S]
    (a : S) : ZMod 2 →ₗ[ZMod 2] S where
  toFun s := s • a
  map_add' s t := add_smul s t a
  map_smul' s t := by simp only [RingHom.id_apply,smul_eq_mul,mul_smul]

lemma h5_line_map_injective {S : Type*} [AddCommGroup S] [Module (ZMod 2) S]
    (a : S) (ha : a ≠ 0) : Function.Injective (h5LineMap a) := by
  intro s t hst
  have hz : (s-t) • a = 0 := by
    change h5LineMap a (s-t)=0
    rw [map_sub,hst,sub_self]
  have hbit : ∀ x : ZMod 2, x=0 ∨ x=1 := by decide
  rcases hbit (s-t) with h | h
  · exact sub_eq_zero.mp h
  · rw [h,one_smul] at hz
    exact False.elim (ha hz)

lemma h5_same_selector_triple_sign (h data triple : ZMod 2) :
    (if h+data=h+triple then (1:ℤ) else -1) = h5Chi (data+triple) := by
  fin_cases h <;> fin_cases data <;> fin_cases triple <;> decide

lemma h5_explicit_line_attainment {n k m r : ℕ}
    (e : (Fin n → ZMod 2) ≃ₗ[ZMod 2]
      ((Fin k → ZMod 2) × ((Fin m → ZMod 2) × ((Fin m → ZMod 2) × (Fin r → ZMod 2)))))
    (A : Fin m → Fin k → ZMod 2) (h : (Fin k → ZMod 2) → ZMod 2)
    (a : Fin k → ZMod 2) (ha : a ≠ 0) (j : Fin m) (hj : dotProduct (A j) a ≠ 0) :
    ∃ (L : (Fin (2*m+r+1) → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
      (q : (Fin (2*m+r+1) → ZMod 2) → ZMod 2)
      (f1 f2 f3 : (Fin (2*m+r+1) → ZMod 2) →ₗ[ZMod 2] ZMod 2),
      Function.Injective L ∧
      (∃ (z : ZMod 2) (l : Fin (2*m+r+1) → ZMod 2)
        (M : Fin (2*m+r+1) → Fin (2*m+r+1) → ZMod 2),
        ∀ x, q x = z + dotProduct l x + ∑ i, ∑ j, M i j*x i*x j) ∧
      (∑ x : Fin (2*m+r+1) → ZMod 2,
        if h (e (L x)).1 + ∑ i, dotProduct (A i) (e (L x)).1 *
          (e (L x)).2.1 i * (e (L x)).2.2.1 i = q x + f1 x*f2 x*f3 x then (1:ℤ) else -1) =
        (2:ℤ)^(m+r) * (2^m +
          2^(m+1-((Finset.univ : Finset (Fin m)).filter (fun i => dotProduct (A i) a ≠ 0)).card)) := by
  classical
  obtain ⟨D⟩ := h5_line_domain_equiv m r
  let K := (h5LineMap a).prodMap
    (LinearMap.id : ((Fin m → ZMod 2) × ((Fin m → ZMod 2) × (Fin r → ZMod 2))) →ₗ[ZMod 2]
      ((Fin m → ZMod 2) × ((Fin m → ZMod 2) × (Fin r → ZMod 2))))
  let L := e.symm.toLinearMap.comp (K.comp D.toLinearMap)
  let f1 : (Fin (2*m+r+1) → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    { toFun x := (D x).1
      map_add' x y := by simp
      map_smul' c x := by simp }
  let f2 : (Fin (2*m+r+1) → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    { toFun x := (D x).2.1 j
      map_add' x y := by simp
      map_smul' c x := by simp }
  let f3 : (Fin (2*m+r+1) → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    { toFun x := (D x).2.2.1 j
      map_add' x y := by simp
      map_smul' c x := by simp }
  let q := fun x => h ((D x).1 • a)
  have hK : Function.Injective K := by
    intro x y hxy
    apply Prod.ext
    · exact h5_line_map_injective a ha (congrArg Prod.fst hxy)
    · have hs := congrArg Prod.snd hxy
      exact hs
  refine ⟨L,q,f1,f2,f3,e.symm.injective.comp (hK.comp D.injective),?_,?_⟩
  · obtain ⟨l,M,hq⟩ := h5_two_linear_function_quad f1 0 (h 0) (h a+h 0) 0 0
    refine ⟨h 0,l,M,?_⟩
    intro x
    have hlin := h5_line_h_interpolation h a ((D x).1)
    exact hlin.trans (by simpa [f1] using hq x)
  · have hEL (x) : e (L x) = K (D x) := by
      dsimp only [L,LinearMap.comp_apply,LinearEquiv.coe_coe]
      exact e.apply_symm_apply _
    simp_rw [hEL]
    change (∑ x, if h ((D x).1 • a) +
      ∑ i, dotProduct (A i) ((D x).1 • a)*(D x).2.1 i*(D x).2.2.1 i =
        h ((D x).1 • a) + (D x).1*(D x).2.1 j*(D x).2.2.1 j then (1:ℤ) else -1) = _
    simp_rw [h5_same_selector_triple_sign]
    rw [← D.symm.toEquiv.sum_comp]
    have hDD (w) : D (D.symm.toEquiv w) = w := D.apply_symm_apply w
    simp_rw [hDD]
    simp only [Fintype.sum_prod_type]
    have hs := h5_line_with_noise_sum (r := r) (fun i => dotProduct (A i) a) j hj
    simpa only [dotProduct_smul,smul_eq_mul,Finset.mul_sum,mul_assoc] using hs

lemma h5_posted_line_attainment {n k m r d : ℕ} (hd : 0 < d)
    (e : (Fin n → ZMod 2) ≃ₗ[ZMod 2]
      ((Fin k → ZMod 2) × ((Fin m → ZMod 2) × ((Fin m → ZMod 2) × (Fin r → ZMod 2)))))
    (A : Fin m → Fin k → ZMod 2) (h : (Fin k → ZMod 2) → ZMod 2)
    (hw : ∃ a : Fin k → ZMod 2, a ≠ 0 ∧
      ((Finset.univ : Finset (Fin m)).filter (fun i => dotProduct (A i) a ≠ 0)).card = d) :
    ∃ (L : (Fin (2*m+r+1) → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
      (q : (Fin (2*m+r+1) → ZMod 2) → ZMod 2)
      (f1 f2 f3 : (Fin (2*m+r+1) → ZMod 2) →ₗ[ZMod 2] ZMod 2),
      Function.Injective L ∧
      (∃ (z : ZMod 2) (l : Fin (2*m+r+1) → ZMod 2)
        (M : Fin (2*m+r+1) → Fin (2*m+r+1) → ZMod 2),
        ∀ x, q x = z + dotProduct l x + ∑ i, ∑ j, M i j*x i*x j) ∧
      2^(m+2) * (∑ x : Fin (2*m+r+1) → ZMod 2,
        if h (e (L x)).1 + ∑ i, dotProduct (A i) (e (L x)).1 *
          (e (L x)).2.1 i * (e (L x)).2.2.1 i = q x + f1 x*f2 x*f3 x then (1:ℤ) else -1).natAbs =
        2^(2*m+r+2) * (2^m+2^(m+1-d)) := by
  classical
  obtain ⟨a,ha,haw⟩ := hw
  have hpos : 0 < ((Finset.univ : Finset (Fin m)).filter
      (fun i => dotProduct (A i) a ≠ 0)).card := by omega
  obtain ⟨j,hj⟩ := Finset.card_pos.mp hpos
  obtain ⟨L,q,f1,f2,f3,hL,hq,hs⟩ := h5_explicit_line_attainment e A h a ha j
    (Finset.mem_filter.mp hj).2
  refine ⟨L,q,f1,f2,f3,hL,hq,?_⟩
  rw [haw] at hs
  have hint : (2:ℤ)^m+2^(m+1-d) = ((2^m+2^(m+1-d):ℕ):ℤ) := by simp
  rw [hint] at hs
  have hn := congrArg Int.natAbs hs
  simp only [Int.natAbs_mul,Int.natAbs_pow] at hn
  rw [hn]
  change (2:ℕ)^(m+2) * (2^(m+r)*(2^m+2^(m+1-d))) =
    2^(2*m+r+2)*(2^m+2^(m+1-d))
  rw [← Nat.mul_assoc,← pow_add]
  rw [show m+2+(m+r)=2*m+r+2 by omega]

end h5_part_7

namespace Circuit

open PEqualNP.CircuitLowerBounds

def gateAt (C : Circuit) (j : ℕ) : Gate :=
  C.gates.getD j ⟨GateOp.or, []⟩

def ReadsBack (n : ℕ) (C : Circuit) : Prop :=
  ∀ j < C.gates.length, ∀ i ∈ (gateAt C j).inputs, i < n + j

abbrev F2 := ZMod 2

def legalGates (n : ℕ) (gs : List Gate) : Prop :=
  ReadsBack n ⟨gs, 0⟩ ∧
    ∀ h ∈ gs, h.inputs.length ≤ 2 ∧
      (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1))

noncomputable def costGates (gs : List Gate) : ℕ :=
  gs.countP (fun h => @decide ((h.op = .and ∨ h.op = .or) ∧ h.inputs.length = 2) (Classical.propDecidable _))

def wiresOf (gs : List Gate) (x : List Bool) : List Bool :=
  (Circuit.mk gs 0).wires x

def bitsOf (n : ℕ) (u : Fin n → F2) : List Bool :=
  List.ofFn (fun j : Fin n => decide (u j = 1))

lemma bitsOf_len (n : ℕ) (u : Fin n → F2) : (bitsOf n u).length = n := by
  simp [bitsOf]

lemma bitsOf_getD (n : ℕ) (u : Fin n → F2) (j : Fin n) :
    (bitsOf n u).getD j.val false = decide (u j = 1) := by
  simp [bitsOf, List.getD_eq_getElem?_getD, j.isLt]

lemma zmod2_add_decide (a b : F2) :
    decide (a + b = 1) = Bool.xor (decide (a = 1)) (decide (b = 1)) := by
  fin_cases a <;> fin_cases b <;> decide

lemma zmod2_mul_decide (a b : F2) :
    decide (a * b = 1) = (decide (a = 1) && decide (b = 1)) := by
  fin_cases a <;> fin_cases b <;> decide

lemma zmod2_bool_decide (b : Bool) :
    decide ((if b then (1 : F2) else 0) = 1) = b := by
  cases b <;> decide

lemma zmod2_cases (a : F2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma zmod2_xor_zero_iff (b ow : Bool) (d : F2) :
    d + (if Bool.xor b ow then (1 : F2) else 0) = 0 ↔ b = Bool.xor ow (decide (d = 1)) := by
  cases b <;> cases ow <;> fin_cases d <;> decide

lemma zmod2_decide_bool (a : F2) :
    (if decide (a = 1) then (1 : F2) else 0) = a := by
  fin_cases a <;> rfl

lemma zmod2_sub_eq_add (a b : F2) : a - b = a + b := by
  fin_cases a <;> fin_cases b <;> decide

lemma zmod2_vec_sub_eq_add {k : ℕ} (x y : Fin k → F2) : x - y = x + y := by
  funext j; exact zmod2_sub_eq_add (x j) (y j)

lemma zmod2_vec_add_self {k : ℕ} (x : Fin k → F2) : x + x = 0 := by
  funext j
  have : x j + x j = 0 := by
    rcases zmod2_cases (x j) with h | h <;> rw [h] <;> decide
  exact this

lemma wiresOf_len (gs : List Gate) (x : List Bool) :
    (wiresOf gs x).length = x.length + gs.length := by
  unfold wiresOf Circuit.wires
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

lemma wiresOf_append (gs1 gs2 : List Gate) (x : List Bool) :
    wiresOf (gs1 ++ gs2) x = wiresOf gs2 (wiresOf gs1 x) := by
  unfold wiresOf Circuit.wires
  exact List.foldl_append

lemma wiresOf_getD_lt (gs : List Gate) (x : List Bool) {i : ℕ} (hi : i < x.length) :
    (wiresOf gs x).getD i false = x.getD i false := by
  unfold wiresOf Circuit.wires
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hi' : i < (x ++ [g.op.eval (g.inputs.map fun idx => x.getD idx false)]).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]; omega
    rw [ih _ hi']
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma wiresOf_append_getD_lt (gs1 gs2 : List Gate) (x : List Bool) {i : ℕ}
    (hi : i < x.length + gs1.length) :
    (wiresOf (gs1 ++ gs2) x).getD i false = (wiresOf gs1 x).getD i false := by
  rw [wiresOf_append, wiresOf_getD_lt gs2 (wiresOf gs1 x) (by rw [wiresOf_len]; exact hi)]

lemma wiresOf_snoc_last (gs : List Gate) (g : Gate) (x : List Bool) :
    (wiresOf (gs ++ [g]) x).getD (x.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (wiresOf gs x).getD i false) := by
  rw [wiresOf_append]
  set w := wiresOf gs x
  have hlen : w.length = x.length + gs.length := wiresOf_len gs x
  change (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).getD (x.length + gs.length) false = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
      show x.length + gs.length - w.length = 0 by omega]
  rfl

lemma wiresOf_snoc_last_eq {n : ℕ} (gs : List Gate) (g : Gate) (x : List Bool) (hx : x.length = n) :
    (wiresOf (gs ++ [g]) x).getD (n + gs.length) false =
      g.op.eval (g.inputs.map fun i => (wiresOf gs x).getD i false) := by
  have h := wiresOf_snoc_last gs g x
  rw [hx] at h
  exact h

lemma readsBack_append {n : ℕ} {gs1 gs2 : List Gate}
    (h1 : ReadsBack n ⟨gs1, 0⟩)
    (h2 : ∀ j < gs2.length, ∀ i ∈ (gs2.getD j ⟨.or, []⟩).inputs, i < n + gs1.length + j) :
    ReadsBack n ⟨gs1 ++ gs2, 0⟩ := by
  intro j hj i hi
  simp only [gateAt] at hi
  simp only [List.length_append] at hj
  by_cases hlt : j < gs1.length
  · have hget : (gs1 ++ gs2).getD j ⟨.or, []⟩ = gs1.getD j ⟨.or, []⟩ := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
    rw [hget] at hi
    exact h1 j hlt i hi
  · have hge : gs1.length ≤ j := by omega
    have hget : (gs1 ++ gs2).getD j ⟨.or, []⟩ = gs2.getD (j - gs1.length) ⟨.or, []⟩ := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hge]
    rw [hget] at hi
    have := h2 (j - gs1.length) (by omega) i hi
    omega

lemma legalGates_snoc {n : ℕ} {gs : List Gate} {g : Gate}
    (hgs : legalGates n gs)
    (hback : ∀ i ∈ g.inputs, i < n + gs.length)
    (hshape : g.inputs.length ≤ 2 ∧
      (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))) :
    legalGates n (gs ++ [g]) := by
  refine ⟨readsBack_append hgs.1 ?_, ?_⟩
  · intro j hj i hi
    have hj0 : j = 0 := by simp at hj; omega
    subst hj0
    simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero, Option.getD_some] at hi
    have := hback i hi
    omega
  · intro h hh
    rcases List.mem_append.mp hh with h1 | h2
    · exact hgs.2 h h1
    · simp only [List.mem_singleton] at h2; subst h2; exact hshape

lemma legalGates_prefix {n : ℕ} {gs : List Gate} {g : Gate}
    (h : legalGates n (gs ++ [g])) :
    legalGates n gs ∧
      (∀ i ∈ g.inputs, i < n + gs.length) ∧
      (g.inputs.length ≤ 2 ∧
        (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))) := by
  refine ⟨⟨?_, fun h' hh' => h.2 h' (List.mem_append_left _ hh')⟩, ?_, h.2 g (by simp)⟩
  · intro j hj i hi
    have hj0 : j < gs.length := hj
    have hj' : j < (gs ++ [g]).length := by simp; omega
    have hget : (gs ++ [g]).getD j ⟨.or, []⟩ = gs.getD j ⟨.or, []⟩ := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hj0]
    have hi' : i ∈ (gateAt ⟨gs ++ [g], 0⟩ j).inputs := by
      change i ∈ ((gs ++ [g]).getD j ⟨.or, []⟩).inputs
      rw [hget]; exact hi
    exact h.1 j hj' i hi'
  · intro i hi
    have hj' : gs.length < (gs ++ [g]).length := by simp
    have hget : (gs ++ [g]).getD gs.length ⟨.or, []⟩ = g := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self,
        List.getElem?_cons_zero, Option.getD_some]
    exact h.1 gs.length hj' i (by simpa [gateAt, hget] using hi)

lemma costGates_append (gs1 gs2 : List Gate) :
    costGates (gs1 ++ gs2) = costGates gs1 + costGates gs2 := by
  unfold costGates; exact List.countP_append

lemma costGates_snoc_zero (gs : List Gate) (g : Gate)
    (h0 : ¬ ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2)) :
    costGates (gs ++ [g]) = costGates gs := by
  rw [costGates_append]
  unfold costGates
  simp [h0]

lemma costGates_snoc_one (gs : List Gate) (g : Gate)
    (h1 : (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) :
    costGates (gs ++ [g]) = costGates gs + 1 := by
  rw [costGates_append]
  unfold costGates
  simp [h1]

lemma addXor_step (t : ℕ) (gs : List Gate) (w1 w2 : ℕ)
    (hgs : legalGates t gs) (hw1 : w1 < t + gs.length) (hw2 : w2 < t + gs.length) :
    let gs' := gs ++ [⟨.mod 2, [w1, w2]⟩, ⟨.not, [t + gs.length]⟩]
    legalGates t gs' ∧
    costGates gs' = costGates gs ∧
    gs'.length = gs.length + 2 ∧
    ∀ x : List Bool, x.length = t →
      (wiresOf gs' x).getD (t + gs.length + 1) false =
        Bool.xor ((wiresOf gs x).getD w1 false) ((wiresOf gs x).getD w2 false) := by
  intro gs'
  have h1 : legalGates t (gs ++ [⟨.mod 2, [w1, w2]⟩]) := by
    apply legalGates_snoc hgs
    · intro i hi; simp at hi; rcases hi with rfl | rfl <;> omega
    · exact ⟨by simp, Or.inr (Or.inr (Or.inl rfl))⟩
  have h2 : legalGates t ((gs ++ [⟨.mod 2, [w1, w2]⟩]) ++ [⟨.not, [t + gs.length]⟩]) := by
    apply legalGates_snoc h1
    · intro i hi; simp at hi; subst hi; simp
    · exact ⟨by simp, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
  have hgs'_eq : gs' = (gs ++ [⟨.mod 2, [w1, w2]⟩]) ++ [⟨.not, [t + gs.length]⟩] := by simp [gs']
  refine ⟨hgs'_eq ▸ h2, ?_, by simp [gs'], ?_⟩
  · rw [hgs'_eq,
        costGates_snoc_zero (gs ++ [(⟨.mod 2, [w1, w2]⟩ : Gate)]) (⟨.not, [t + gs.length]⟩ : Gate) (by simp),
        costGates_snoc_zero gs (⟨.mod 2, [w1, w2]⟩ : Gate) (by simp)]
  · intro x hx
    rw [hgs'_eq]
    have hidx : t + gs.length + 1 = x.length + (gs ++ [(⟨.mod 2, [w1, w2]⟩ : Gate)]).length := by simp; omega
    rw [hidx, wiresOf_snoc_last]
    have hidx1 : t + gs.length = x.length + gs.length := by omega
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
    rw [hidx1, wiresOf_snoc_last]
    simp only [List.map_cons, List.map_nil, GateOp.eval]
    cases (wiresOf gs x).getD w1 false <;> cases (wiresOf gs x).getD w2 false <;> decide

def addXorMany (t cWire : ℕ) (flag : ℕ → Bool) (old : ℕ → ℕ) :
    ℕ → List Gate → List Gate × (ℕ → ℕ)
  | 0, gs => (gs, old)
  | m + 1, gs =>
    let res := addXorMany t cWire flag old m gs
    let gs1 := res.1
    let f1 := res.2
    if flag m then
      (gs1 ++ [⟨.mod 2, [old m, cWire]⟩, ⟨.not, [t + gs1.length]⟩],
        fun u => if u = m then t + gs1.length + 1 else f1 u)
    else (gs1, f1)

lemma addXorMany_spec (t cWire : ℕ) (flag : ℕ → Bool) (old : ℕ → ℕ) :
    ∀ (m : ℕ) (gs : List Gate),
      legalGates t gs →
      cWire < t + gs.length →
      (∀ u < m, old u < t + gs.length) →
      let res := addXorMany t cWire flag old m gs
      ∃ ext : List Gate,
        res.1 = gs ++ ext ∧
        legalGates t res.1 ∧
        costGates res.1 = costGates gs ∧
        (∀ u < m, res.2 u < t + res.1.length) ∧
        (∀ u < m, ∀ x : List Bool, x.length = t →
          (wiresOf res.1 x).getD (res.2 u) false =
            if flag u then
              Bool.xor ((wiresOf gs x).getD (old u) false) ((wiresOf gs x).getD cWire false)
            else (wiresOf gs x).getD (old u) false) := by
  intro m
  induction m with
  | zero =>
    intro gs hleg _ _
    exact ⟨[], by simp [addXorMany], hleg, rfl, fun _ hu => by omega, fun _ hu => by omega⟩
  | succ m ih =>
    intro gs hleg hc hold
    rcases ih gs hleg hc (fun u hu => hold u (by omega)) with ⟨ext1, h1eq, h1leg, h1cost, h1lt, h1sem⟩
    set gs1 := (addXorMany t cWire flag old m gs).1
    set f1 := (addXorMany t cWire flag old m gs).2
    have hlen1 : gs.length ≤ gs1.length := by rw [h1eq, List.length_append]; omega
    by_cases hfl : flag m = true
    · have hstep := addXor_step t gs1 (old m) cWire h1leg
        (by have := hold m (by omega); omega) (by omega)
      refine ⟨ext1 ++ [⟨.mod 2, [old m, cWire]⟩, ⟨.not, [t + gs1.length]⟩], ?_, ?_, ?_, ?_, ?_⟩
      · simp [addXorMany, hfl, gs1, h1eq, List.append_assoc]
      · simpa [addXorMany, hfl, gs1] using hstep.1
      · simpa [addXorMany, hfl, gs1, h1cost] using hstep.2.1
      · intro u hu
        simp only [addXorMany, hfl, ↓reduceIte]
        by_cases hum : u = m
        · subst hum; simp only [↓reduceIte, List.length_append, List.length_cons, List.length_nil]; omega
        · simp only [hum, ↓reduceIte, List.length_append, List.length_cons, List.length_nil]
          have := h1lt u (by omega); dsimp only [gs1, f1] at this; omega
      · intro u hu x hx
        simp only [addXorMany, hfl, ↓reduceIte]
        by_cases hum : u = m
        · subst hum
          simp only [↓reduceIte, hfl]
          change (wiresOf (gs1 ++ [⟨.mod 2, [old u, cWire]⟩, ⟨.not, [t + gs1.length]⟩]) x).getD (t + gs1.length + 1) false = _
          rw [hstep.2.2.2 x hx, h1eq,
              wiresOf_append_getD_lt gs ext1 x (by rw [hx]; exact hold u (by omega)),
              wiresOf_append_getD_lt gs ext1 x (by rw [hx]; exact hc)]
        · simp only [hum, ↓reduceIte]
          change (wiresOf (gs1 ++ [⟨.mod 2, [old m, cWire]⟩, ⟨.not, [t + gs1.length]⟩]) x).getD (f1 u) false = _
          rw [wiresOf_append_getD_lt gs1 _ x (by rw [hx]; exact h1lt u (by omega))]
          exact h1sem u (by omega) x hx
    · have hflf : flag m = false := Bool.eq_false_iff.mpr hfl
      refine ⟨ext1, ?_, ?_, ?_, ?_, ?_⟩
      · simp [addXorMany, hflf, gs1, h1eq]
      · simpa [addXorMany, hflf, gs1] using h1leg
      · simpa [addXorMany, hflf, gs1] using h1cost
      · intro u hu
        simp only [addXorMany, hflf, Bool.false_eq_true, ↓reduceIte]
        by_cases hum : u = m
        · subst hum
          have hfm : (addXorMany t cWire flag old u gs).2 u = old u := by
            clear h1eq h1leg h1cost h1lt h1sem hlen1 ih
            have hkeep : ∀ (n : ℕ) (g : List Gate), u ≥ n → (addXorMany t cWire flag old n g).2 u = old u := by
              intro n
              induction n with
              | zero => intro g _; rfl
              | succ n ihn =>
                intro g hge
                simp only [addXorMany]
                split_ifs
                · have hne : u ≠ n := by omega
                  simp only [hne, ↓reduceIte]
                  exact ihn g (by omega)
                · exact ihn g (by omega)
            exact hkeep u gs (le_refl _)
          rw [hfm]; have := hold u (by omega); dsimp only [gs1] at hlen1; omega
        · exact h1lt u (by omega)
      · intro u hu x hx
        simp only [addXorMany, hflf, Bool.false_eq_true, ↓reduceIte]
        by_cases hum : u = m
        · subst hum
          have hfm : (addXorMany t cWire flag old u gs).2 u = old u := by
            clear h1eq h1leg h1cost h1lt h1sem hlen1 ih
            have hkeep : ∀ (n : ℕ) (g : List Gate), u ≥ n → (addXorMany t cWire flag old n g).2 u = old u := by
              intro n
              induction n with
              | zero => intro g _; rfl
              | succ n ihn =>
                intro g hge
                simp only [addXorMany]
                split_ifs
                · have hne : u ≠ n := by omega
                  simp only [hne, ↓reduceIte]
                  exact ihn g (by omega)
                · exact ihn g (by omega)
            exact hkeep u gs (le_refl _)
          rw [hfm, hflf]
          simp only [Bool.false_eq_true, ↓reduceIte]
          change (wiresOf gs1 x).getD (old u) false = _
          rw [h1eq, wiresOf_append_getD_lt gs ext1 x (by rw [hx]; exact hold u (by omega))]
        · exact h1sem u (by omega) x hx

def dotLin {k : ℕ} (s0 : Fin k → F2) : (Fin k → F2) →ₗ[F2] F2 :=
  { toFun := fun u => dotProduct s0 u
    map_add' := fun a b => dotProduct_add s0 a b
    map_smul' := fun c a => by simp [dotProduct_smul] }

def kerDot {k : ℕ} (U : Submodule F2 (Fin k → F2)) (s0 : Fin k → F2) : Submodule F2 (Fin k → F2) :=
  U ⊓ LinearMap.ker (dotLin s0)

lemma mem_kerDot {k : ℕ} (U : Submodule F2 (Fin k → F2)) (s0 u : Fin k → F2) :
    u ∈ kerDot U s0 ↔ u ∈ U ∧ dotProduct s0 u = 0 := Iff.rfl

lemma finrank_ker_dot {k : ℕ} (U : Submodule F2 (Fin k → F2)) (s0 v0 : Fin k → F2)
    (hv0 : v0 ∈ U) (hdot : dotProduct s0 v0 = 1) :
    Module.finrank F2 (kerDot U s0) + 1 = Module.finrank F2 U := by
  let φ : U →ₗ[F2] F2 :=
    { toFun := fun u => dotProduct s0 u.val
      map_add' := fun a b => dotProduct_add s0 a.val b.val
      map_smul' := fun c a => by simp [dotProduct_smul] }
  have hsurj : Function.Surjective φ := by
    intro c
    refine ⟨c • ⟨v0, hv0⟩, ?_⟩
    simp only [map_smul, φ, LinearMap.coe_mk, AddHom.coe_mk, hdot, smul_eq_mul, mul_one]
  have hrk := LinearMap.finrank_range_add_finrank_ker φ
  have hran : LinearMap.range φ = ⊤ := LinearMap.range_eq_top.mpr hsurj
  rw [hran, finrank_top, Module.finrank_self] at hrk
  have hequiv : kerDot U s0 ≃ₗ[F2] LinearMap.ker φ :=
    { toFun := fun u => ⟨⟨u.val, u.property.1⟩, u.property.2⟩
      invFun := fun u => ⟨u.val.val, ⟨u.val.property, u.property⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  rw [hequiv.finrank_eq]
  omega

abbrev Branch (k _t : ℕ) :=
  ℕ × Submodule F2 (Fin k → F2) × List Gate × (Fin k → ℕ) ×
    (ℕ → ℕ) × (ℕ → (Fin k → F2))

def Branch.mk {k t : ℕ} (r : ℕ) (U : Submodule F2 (Fin k → F2))
    (gates : List Gate) (tap : Fin k → ℕ) (off : ℕ → ℕ)
    (slope : ℕ → (Fin k → F2)) : Branch k t :=
  (r, U, gates, tap, off, slope)

abbrev Branch.r {k t : ℕ} (B : Branch k t) : ℕ := B.1

abbrev Branch.U {k t : ℕ} (B : Branch k t) : Submodule F2 (Fin k → F2) := B.2.1

abbrev Branch.gates {k t : ℕ} (B : Branch k t) : List Gate := B.2.2.1

abbrev Branch.tap {k t : ℕ} (B : Branch k t) : Fin k → ℕ := B.2.2.2.1

abbrev Branch.off {k t : ℕ} (B : Branch k t) : ℕ → ℕ := B.2.2.2.2.1

abbrev Branch.slope {k t : ℕ} (B : Branch k t) : ℕ → (Fin k → F2) := B.2.2.2.2.2

def Branch.pos {k t : ℕ} (B : Branch k t) (z : Fin t → F2) (j : Fin k) : F2 :=
  if (wiresOf B.gates (bitsOf t z)).getD (B.tap j) false then 1 else 0

def ValidBranch {k t : ℕ} (gs : List Gate) (B : Branch k t) : Prop :=
  Module.finrank F2 B.U + B.r = k ∧
  legalGates t B.gates ∧
  costGates B.gates + B.r ≤ costGates gs ∧
  (∀ j : Fin k, B.tap j < t + B.gates.length) ∧
  (∀ w < k + t + gs.length, B.off w < t + B.gates.length) ∧
  (∀ w < k + t + gs.length, ∀ (z : Fin t → F2) (u : Fin k → F2), u ∈ B.U →
    (wiresOf gs (bitsOf k (B.pos z + u) ++ bitsOf t z)).getD w false =
      Bool.xor ((wiresOf B.gates (bitsOf t z)).getD (B.off w) false)
        (decide (dotProduct (B.slope w) u = 1)))

lemma branch_eval_add_gate {k t : ℕ} {gs : List Gate} {g : Gate} {B : Branch k t}
    (_hleg : legalGates (k + t) (gs ++ [g]))
    (hB : ValidBranch gs B)
    (gs' : List Gate) (ext : List Gate) (hgs' : gs' = B.gates ++ ext)
    (hleg' : legalGates t gs')
    (hcost' : costGates gs' + B.r ≤ costGates (gs ++ [g]))
    (wNew : ℕ) (hwNew : wNew < t + gs'.length) (sNew : Fin k → F2)
    (hsemNew : ∀ (z : Fin t → F2) (u : Fin k → F2), u ∈ B.U →
      g.op.eval (g.inputs.map fun i => (wiresOf gs (bitsOf k (B.pos z + u) ++ bitsOf t z)).getD i false) =
        Bool.xor ((wiresOf gs' (bitsOf t z)).getD wNew false) (decide (dotProduct sNew u = 1))) :
    let B' : Branch k t :=
      ⟨B.r, B.U, gs', B.tap,
        fun w => if w = k + t + gs.length then wNew else B.off w,
        fun w => if w = k + t + gs.length then sNew else B.slope w⟩
    ValidBranch (gs ++ [g]) B' ∧
      ∀ z : Fin t → F2, B'.pos z = B.pos z := by
  intro B'
  have hpos_eq : ∀ z : Fin t → F2, B'.pos z = B.pos z := by
    intro z; funext j
    simp only [Branch.r, Branch.U, Branch.gates, Branch.tap, Branch.off, Branch.slope, Branch.pos, B', hgs']
    rw [wiresOf_append_getD_lt B.gates ext (bitsOf t z) (by rw [bitsOf_len]; exact hB.2.2.2.1 j)]
  refine ⟨⟨hB.1, hleg', hcost', ?_, ?_, ?_⟩, hpos_eq⟩
  · intro j; simp only [Branch.r, Branch.U, Branch.gates, Branch.tap, Branch.off, Branch.slope, B', hgs', List.length_append]; have := hB.2.2.2.1 j; simp only [Branch.tap, Branch.gates] at this; omega
  · intro w hw
    simp only [List.length_append, List.length_cons, List.length_nil] at hw
    simp only [Branch.r, Branch.U, Branch.gates, Branch.tap, Branch.off, Branch.slope, B']
    by_cases hweq : w = k + t + gs.length
    · simp only [hweq, ↓reduceIte]; exact hwNew
    · simp only [hweq, ↓reduceIte, hgs', List.length_append]
      have := hB.2.2.2.2.1 w (by omega); simp only [Branch.off] at this; omega
  · intro w hw z u hu
    simp only [List.length_append, List.length_cons, List.length_nil] at hw
    rw [hpos_eq z]
    have hlen_in : (bitsOf k (B.pos z + u) ++ bitsOf t z).length = k + t := by
      simp [bitsOf_len]
    by_cases hweq : w = k + t + gs.length
    · subst hweq
      simp only [Branch.r, Branch.U, Branch.gates, Branch.tap, Branch.off, Branch.slope, B', ↓reduceIte]
      have hidx : k + t + gs.length = (bitsOf k (B.pos z + u) ++ bitsOf t z).length + gs.length := by omega
      rw [hidx, wiresOf_snoc_last]
      exact hsemNew z u hu
    · simp only [Branch.r, Branch.U, Branch.gates, Branch.tap, Branch.off, Branch.slope, B', hweq, ↓reduceIte]
      rw [wiresOf_append_getD_lt gs [g] _ (by rw [hlen_in]; omega)]
      rw [hgs', wiresOf_append_getD_lt B.gates ext (bitsOf t z) (by rw [bitsOf_len]; exact hB.2.2.2.2.1 w (by omega))]
      exact hB.2.2.2.2.2 w (by omega) z u hu

lemma step_single_branch {k t : ℕ} {gs : List Gate} {g : Gate} (B : Branch k t)
    (hleg : legalGates (k + t) (gs ++ [g])) (hB : ValidBranch gs B) :
    ∃ L : List (Branch k t),
      (∀ B' ∈ L, ValidBranch (gs ++ [g]) B') ∧
      ∀ (z : Fin t → F2) (x : Fin k → F2),
        (x - B.pos z ∈ B.U → ∃! idx : Fin L.length, x - (L.get idx).pos z ∈ (L.get idx).U) ∧
        (x - B.pos z ∉ B.U → ∀ idx : Fin L.length, x - (L.get idx).pos z ∉ (L.get idx).U) := by
  have hpre := legalGates_prefix hleg
  have hback := hpre.2.1
  have hshape := hpre.2.2
  have hcost_ge : costGates gs ≤ costGates (gs ++ [g]) := by
    rw [costGates_append]; omega
  have hwrap_one : ∀ (B' : Branch k t), ValidBranch (gs ++ [g]) B' → B'.U = B.U →
      (∀ z, B'.pos z = B.pos z) →
      ∃ L : List (Branch k t),
        (∀ b ∈ L, ValidBranch (gs ++ [g]) b) ∧
        ∀ (z : Fin t → F2) (x : Fin k → F2),
          (x - B.pos z ∈ B.U → ∃! idx : Fin L.length, x - (L.get idx).pos z ∈ (L.get idx).U) ∧
          (x - B.pos z ∉ B.U → ∀ idx : Fin L.length, x - (L.get idx).pos z ∉ (L.get idx).U) := by
    intro B' hB' hU hpos
    refine ⟨[B'], fun b hb => by simp at hb; subst hb; exact hB', fun z x => ⟨?_, ?_⟩⟩
    · intro hx
      refine ⟨⟨0, by simp⟩, by simpa [hpos, hU] using hx, fun j _ => Fin.ext (by have := j.isLt; simp only [List.length_singleton] at this; change j.val = 0; omega)⟩
    · intro hnx idx
      have hi0 : idx = ⟨0, by simp⟩ := Fin.ext (by have := idx.isLt; simp only [List.length_singleton] at this; change idx.val = 0; omega)
      subst hi0
      simpa [hpos, hU] using hnx
  rcases hshape.2 with hop | hop | hop | ⟨hop, hlen1⟩
  ·
    rcases hg : g.inputs with _ | ⟨w0, rest⟩
    ·
      let gs' := B.gates ++ [⟨.and, []⟩]
      have hleg' : legalGates t gs' :=
        legalGates_snoc hB.2.1 (by simp) ⟨by simp, Or.inl rfl⟩
      have hcost' : costGates gs' + B.r ≤ costGates (gs ++ [g]) := by
        rw [costGates_snoc_zero B.gates _ (by simp)]; have := hB.2.2.1; omega
      have hres := branch_eval_add_gate hleg hB gs' [⟨.and, []⟩] rfl hleg' hcost'
        (t + B.gates.length) (by simp [gs']) 0 (fun z u _ => by
          rw [hop, hg]
          have hidx : t + B.gates.length = (bitsOf t z).length + B.gates.length := by rw [bitsOf_len]
          rw [hidx, wiresOf_snoc_last]; simp [GateOp.eval])
      exact hwrap_one _ hres.1 rfl hres.2
    · rcases rest with _ | ⟨w1, rest2⟩
      ·
        have hw0 : w0 < k + t + gs.length := hback w0 (by rw [hg]; simp)
        have hres := branch_eval_add_gate hleg hB B.gates [] (by simp) hB.2.1
          (by have := hB.2.2.1; omega) (B.off w0) (hB.2.2.2.2.1 w0 hw0) (B.slope w0)
          (fun z u hu => by
            rw [hop, hg]; simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons,
              List.all_nil, id_eq, Bool.and_true]
            exact hB.2.2.2.2.2 w0 hw0 z u hu)
        exact hwrap_one _ hres.1 rfl hres.2
      · rcases rest2 with _ | ⟨_, _⟩
        ·
          have hw0 : w0 < k + t + gs.length := hback w0 (by rw [hg]; simp)
          have hw1 : w1 < k + t + gs.length := hback w1 (by rw [hg]; simp)
          have hcost1 : costGates (gs ++ [g]) = costGates gs + 1 :=
            costGates_snoc_one gs g ⟨Or.inl hop, by rw [hg]; rfl⟩
          by_cases hvan : (∀ u ∈ B.U, dotProduct (B.slope w0) u = 0) ∧
              (∀ u ∈ B.U, dotProduct (B.slope w1) u = 0)
          ·
            let gs' := B.gates ++ [⟨.and, [B.off w0, B.off w1]⟩]
            have hleg' : legalGates t gs' :=
              legalGates_snoc hB.2.1
                (fun i hi => by simp at hi; rcases hi with rfl | rfl; exact hB.2.2.2.2.1 w0 hw0; exact hB.2.2.2.2.1 w1 hw1)
                ⟨by simp, Or.inl rfl⟩
            have hcost' : costGates gs' + B.r ≤ costGates (gs ++ [g]) := by
              rw [costGates_snoc_one B.gates _ ⟨Or.inl rfl, rfl⟩, hcost1]; have := hB.2.2.1; omega
            have hres := branch_eval_add_gate hleg hB gs' [⟨.and, [B.off w0, B.off w1]⟩] rfl hleg' hcost'
              (t + B.gates.length) (by simp [gs']) 0 (fun z u hu => by
                rw [hop, hg]
                have hidx : t + B.gates.length = (bitsOf t z).length + B.gates.length := by rw [bitsOf_len]
                rw [hidx, wiresOf_snoc_last]
                simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
                  id_eq, Bool.and_true]
                rw [hB.2.2.2.2.2 w0 hw0 z u hu, hB.2.2.2.2.2 w1 hw1 z u hu,
                    hvan.1 u hu, hvan.2 u hu]
                simp)
            exact hwrap_one _ hres.1 rfl hres.2
          ·
            have hex : ∃ (wa wb : ℕ), wa < k + t + gs.length ∧ wb < k + t + gs.length ∧
                ((wa = w0 ∧ wb = w1) ∨ (wa = w1 ∧ wb = w0)) ∧
                ∃ v0 ∈ B.U, dotProduct (B.slope wa) v0 = 1 := by
              by_cases h0 : ∀ u ∈ B.U, dotProduct (B.slope w0) u = 0
              · have h1 : ¬ ∀ u ∈ B.U, dotProduct (B.slope w1) u = 0 := fun h => hvan ⟨h0, h⟩
                push Not at h1
                rcases h1 with ⟨v0, hv0, hne⟩
                have hd1 : dotProduct (B.slope w1) v0 = 1 := by
                  rcases zmod2_cases (dotProduct (B.slope w1) v0) with h | h
                  · exact absurd h hne
                  · exact h
                exact ⟨w1, w0, hw1, hw0, Or.inr ⟨rfl, rfl⟩, v0, hv0, hd1⟩
              · push Not at h0
                rcases h0 with ⟨v0, hv0, hne⟩
                have hd1 : dotProduct (B.slope w0) v0 = 1 := by
                  rcases zmod2_cases (dotProduct (B.slope w0) v0) with h | h
                  · exact absurd h hne
                  · exact h
                exact ⟨w0, w1, hw0, hw1, Or.inl ⟨rfl, rfl⟩, v0, hv0, hd1⟩
            rcases hex with ⟨wa, wb, hwa, hwb, hwab, v0, hv0, hdot⟩
            let U' : Submodule F2 (Fin k → F2) := kerDot B.U (B.slope wa)
            have hdim' : Module.finrank F2 U' + (B.r + 1) = k := by
              have h1 : Module.finrank F2 U' + 1 = Module.finrank F2 B.U :=
                finrank_ker_dot B.U (B.slope wa) v0 hv0 hdot
              have h2 := hB.1
              omega
            have hbuild_child : ∀ (b : Bool), ∃ Bc : Branch k t,
                ValidBranch (gs ++ [g]) Bc ∧ Bc.U = U' ∧
                ∀ z : Fin t → F2,
                  Bc.pos z = B.pos z +
                    (if Bool.xor b ((wiresOf B.gates (bitsOf t z)).getD (B.off wa) false) then (1 : F2) else 0) • v0 := by
              intro b
              let gs0 := if b then B.gates ++ [⟨.not, [B.off wa]⟩] else B.gates
              let cWire := if b then t + B.gates.length else B.off wa
              have hgs0_ext : ∃ e0, gs0 = B.gates ++ e0 := by
                cases b
                · exact ⟨[], by simp [gs0]⟩
                · exact ⟨[⟨.not, [B.off wa]⟩], rfl⟩
              have hgs0_leg : legalGates t gs0 := by
                cases b
                · exact hB.2.1
                · exact legalGates_snoc hB.2.1 (fun i hi => by simp at hi; subst hi; exact hB.2.2.2.2.1 wa hwa)
                    ⟨by simp, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
              have hgs0_cost : costGates gs0 = costGates B.gates := by
                cases b
                · rfl
                · exact costGates_snoc_zero B.gates _ (by simp)
              have hcWire_lt : cWire < t + gs0.length := by
                cases b
                · exact hB.2.2.2.2.1 wa hwa
                · simp [gs0, cWire]
              have hcWire_sem : ∀ z : Fin t → F2,
                  (wiresOf gs0 (bitsOf t z)).getD cWire false =
                    Bool.xor b ((wiresOf B.gates (bitsOf t z)).getD (B.off wa) false) := by
                intro z
                cases b
                · simp [gs0, cWire]
                · simp only [gs0, cWire, ↓reduceIte]
                  have hidx : t + B.gates.length = (bitsOf t z).length + B.gates.length := by rw [bitsOf_len]
                  rw [hidx, wiresOf_snoc_last]
                  simp [GateOp.eval]
              let tapOld : ℕ → ℕ := fun j => if hj : j < k then B.tap ⟨j, hj⟩ else 0
              let flagTap : ℕ → Bool := fun j => if hj : j < k then decide (v0 ⟨j, hj⟩ = 1) else false
              let resT := addXorMany t cWire flagTap tapOld k gs0
              have hresT := addXorMany_spec t cWire flagTap tapOld k gs0 hgs0_leg hcWire_lt
                (fun j hj => by
                  simp only [tapOld, hj, ↓reduceDIte]
                  rcases hgs0_ext with ⟨e0, he0⟩
                  rw [he0, List.length_append]
                  have := hB.2.2.2.1 ⟨j, hj⟩; omega)
              rcases hresT with ⟨extT, hTeq, hTleg, hTcost, hTlt, hTsem⟩
              let flagOff : ℕ → Bool := fun w => decide (dotProduct (B.slope w) v0 = 1)
              let resO := addXorMany t cWire flagOff B.off (k + t + gs.length) resT.1
              have hresO := addXorMany_spec t cWire flagOff B.off (k + t + gs.length) resT.1 hTleg
                (by rw [hTeq, List.length_append]; omega)
                (fun w hw => by
                  rcases hgs0_ext with ⟨e0, he0⟩
                  rw [hTeq, he0, List.length_append, List.length_append]
                  have := hB.2.2.2.2.1 w hw; omega)
              rcases hresO with ⟨extO, hOeq, hOleg, hOcost, hOlt, hOsem⟩
              let gsF := if b then resO.1 else resO.1 ++ [⟨.or, []⟩]
              have hgsF_ext : ∃ eF, gsF = resO.1 ++ eF := by
                cases b
                · exact ⟨[⟨.or, []⟩], rfl⟩
                · exact ⟨[], by simp [gsF]⟩
              have hgsF_leg : legalGates t gsF := by
                cases b
                · exact legalGates_snoc hOleg (by simp) ⟨by simp, Or.inr (Or.inl rfl)⟩
                · exact hOleg
              have hgsF_cost : costGates gsF = costGates B.gates := by
                cases b
                · rw [show gsF = resO.1 ++ [⟨.or, []⟩] from rfl, costGates_snoc_zero _ _ (by simp), hOcost, hTcost, hgs0_cost]
                · simp only [gsF, ↓reduceIte]; rw [hOcost, hTcost, hgs0_cost]
              let tapF : Fin k → ℕ := fun j => resT.2 j.val
              let wNew := if b then resO.2 wb else t + resO.1.length
              let sNew : Fin k → F2 := if b then B.slope wb else 0
              let Bc : Branch k t :=
                ⟨B.r + 1, U', gsF, tapF,
                  fun w => if w = k + t + gs.length then wNew else resO.2 w,
                  fun w => if w = k + t + gs.length then sNew else B.slope w⟩
              have hpos_c : ∀ z : Fin t → F2,
                  Bc.pos z = B.pos z +
                    (if Bool.xor b ((wiresOf B.gates (bitsOf t z)).getD (B.off wa) false) then (1 : F2) else 0) • v0 := by
                intro z; funext j
                rcases hgsF_ext with ⟨eF, heF⟩
                rcases hgs0_ext with ⟨e0, he0⟩
                have htap_val : (wiresOf gsF (bitsOf t z)).getD (tapF j) false =
                    (wiresOf resT.1 (bitsOf t z)).getD (resT.2 j.val) false := by
                  rw [heF, hOeq, List.append_assoc,
                      wiresOf_append_getD_lt resT.1 _ (bitsOf t z) (by rw [bitsOf_len]; exact hTlt j.val j.isLt)]
                simp only [Branch.r, Branch.U, Branch.gates, Branch.tap, Branch.off, Branch.slope, Branch.pos, Bc, htap_val]
                rw [hTsem j.val j.isLt (bitsOf t z) (bitsOf_len t z)]
                simp only [flagTap, tapOld, j.isLt, ↓reduceDIte, hcWire_sem z]
                rw [he0, wiresOf_append_getD_lt B.gates e0 (bitsOf t z) (by rw [bitsOf_len]; exact hB.2.2.2.1 j)]
                simp only [Branch.r, Branch.U, Branch.gates, Branch.tap, Branch.off, Branch.slope, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Branch.pos]
                cases (wiresOf B.gates (bitsOf t z)).getD (B.tap j) false <;>
                  cases Bool.xor b ((wiresOf B.gates (bitsOf t z)).getD (B.off wa) false) <;>
                  rcases zmod2_cases (v0 j) with h | h <;> simp [h] <;> decide
              have hsem_old : ∀ w < k + t + gs.length, ∀ (z : Fin t → F2) (u : Fin k → F2), u ∈ U' →
                  (wiresOf gs (bitsOf k (Bc.pos z + u) ++ bitsOf t z)).getD w false =
                    Bool.xor ((wiresOf gsF (bitsOf t z)).getD (resO.2 w) false)
                      (decide (dotProduct (B.slope w) u = 1)) := by
                intro w hw z u hu
                rcases hgsF_ext with ⟨eF, heF⟩
                rcases hgs0_ext with ⟨e0, he0⟩
                set cbit := Bool.xor b ((wiresOf B.gates (bitsOf t z)).getD (B.off wa) false)
                set cf : F2 := if cbit then 1 else 0
                have hu_in_B : cf • v0 + u ∈ B.U := B.U.add_mem (B.U.smul_mem cf hv0) hu.1
                have hpos_rw : Bc.pos z + u = B.pos z + (cf • v0 + u) := by
                  rw [hpos_c z, add_assoc]
                rw [hpos_rw, hB.2.2.2.2.2 w hw z (cf • v0 + u) hu_in_B]
                have hwireO : (wiresOf gsF (bitsOf t z)).getD (resO.2 w) false =
                    if decide (dotProduct (B.slope w) v0 = 1) then
                      Bool.xor ((wiresOf B.gates (bitsOf t z)).getD (B.off w) false) cbit
                    else (wiresOf B.gates (bitsOf t z)).getD (B.off w) false := by
                  rw [heF, wiresOf_append_getD_lt resO.1 eF (bitsOf t z) (by rw [bitsOf_len]; exact hOlt w hw)]
                  rw [hOsem w hw (bitsOf t z) (bitsOf_len t z)]
                  rw [hTeq,
                      wiresOf_append_getD_lt gs0 extT (bitsOf t z) (by rw [bitsOf_len, he0, List.length_append]; have := hB.2.2.2.2.1 w hw; omega),
                      wiresOf_append_getD_lt gs0 extT (bitsOf t z) (by rw [bitsOf_len]; exact hcWire_lt)]
                  rw [hcWire_sem z, he0, wiresOf_append_getD_lt B.gates e0 (bitsOf t z) (by rw [bitsOf_len]; exact hB.2.2.2.2.1 w hw)]
                rw [hwireO, dotProduct_add, dotProduct_smul, zmod2_add_decide, smul_eq_mul, zmod2_mul_decide, zmod2_bool_decide]
                cases (wiresOf B.gates (bitsOf t z)).getD (B.off w) false <;>
                  cases cbit <;> cases decide (dotProduct (B.slope w) v0 = 1) <;>
                  cases decide (dotProduct (B.slope w) u = 1) <;> decide
              refine ⟨Bc, ⟨hdim', hgsF_leg, by change costGates gsF + (B.r + 1) ≤ costGates (gs ++ [g]); rw [hgsF_cost, hcost1]; have := hB.2.2.1; omega, ?_, ?_, ?_⟩, rfl, hpos_c⟩
              · intro j
                rcases hgsF_ext with ⟨eF, heF⟩
                have h1 : resT.2 j.val < t + resT.1.length := hTlt j.val j.isLt
                have h2 : resO.1.length = resT.1.length + extO.length := by rw [hOeq, List.length_append]
                simp only [Branch.r, Branch.U, Branch.gates, Branch.tap, Branch.off, Branch.slope, Bc, tapF, heF, List.length_append]
                omega
              · intro w hw
                simp only [List.length_append, List.length_cons, List.length_nil] at hw
                simp only [Branch.r, Branch.U, Branch.gates, Branch.tap, Branch.off, Branch.slope, Bc]
                by_cases hweq : w = k + t + gs.length
                · simp only [hweq, ↓reduceIte, wNew, gsF]
                  cases b
                  · simp
                  · simp only [↓reduceIte]; exact hOlt wb hwb
                · simp only [hweq, ↓reduceIte]
                  rcases hgsF_ext with ⟨eF, heF⟩
                  have h1 : resO.2 w < t + resO.1.length := hOlt w (by omega)
                  rw [heF, List.length_append]; omega
              · intro w hw z u hu
                simp only [List.length_append, List.length_cons, List.length_nil] at hw
                have hlen_in : (bitsOf k (Bc.pos z + u) ++ bitsOf t z).length = k + t := by simp [bitsOf_len]
                by_cases hweq : w = k + t + gs.length
                · subst hweq
                  simp only [Branch.r, Branch.U, Branch.gates, Branch.tap, Branch.off, Branch.slope, Bc, ↓reduceIte]
                  rw [wiresOf_snoc_last_eq gs g _ hlen_in, hop, hg]
                  simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
                    id_eq, Bool.and_true]
                  have hwa_val : (wiresOf gs (bitsOf k (Bc.pos z + u) ++ bitsOf t z)).getD wa false = b := by
                    have hu2 : dotProduct (B.slope wa) u = 0 := hu.2
                    rw [hsem_old wa hwa z u hu, hu2]
                    rcases hgsF_ext with ⟨eF, heF⟩
                    rcases hgs0_ext with ⟨e0, he0⟩
                    rw [heF, wiresOf_append_getD_lt resO.1 eF (bitsOf t z) (by rw [bitsOf_len]; exact hOlt wa hwa)]
                    rw [hOsem wa hwa (bitsOf t z) (bitsOf_len t z)]
                    simp only [flagOff, hdot]
                    rw [hTeq,
                        wiresOf_append_getD_lt gs0 extT (bitsOf t z) (by rw [bitsOf_len, he0, List.length_append]; have := hB.2.2.2.2.1 wa hwa; omega),
                        wiresOf_append_getD_lt gs0 extT (bitsOf t z) (by rw [bitsOf_len]; exact hcWire_lt)]
                    rw [hcWire_sem z, he0, wiresOf_append_getD_lt B.gates e0 (bitsOf t z) (by rw [bitsOf_len]; exact hB.2.2.2.2.1 wa hwa)]
                    cases b <;> cases (wiresOf B.gates (bitsOf t z)).getD (B.off wa) false <;> decide
                  have hcomm : ((wiresOf gs (bitsOf k (Bc.pos z + u) ++ bitsOf t z)).getD w0 false &&
                      (wiresOf gs (bitsOf k (Bc.pos z + u) ++ bitsOf t z)).getD w1 false) =
                      ((wiresOf gs (bitsOf k (Bc.pos z + u) ++ bitsOf t z)).getD wa false &&
                       (wiresOf gs (bitsOf k (Bc.pos z + u) ++ bitsOf t z)).getD wb false) := by
                    rcases hwab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                    · rfl
                    · exact Bool.and_comm _ _
                  rw [hcomm, hwa_val]
                  cases b
                  · simp only [Bool.false_and, wNew, sNew, gsF, Bool.false_eq_true, ↓reduceIte]
                    rw [wiresOf_snoc_last_eq resO.1 ⟨.or, []⟩ (bitsOf t z) (bitsOf_len t z)]; simp [GateOp.eval]
                  · simp only [Bool.true_and, wNew, sNew, gsF, ↓reduceIte]
                    exact hsem_old wb hwb z u hu
                · simp only [Branch.r, Branch.U, Branch.gates, Branch.tap, Branch.off, Branch.slope, Bc, hweq, ↓reduceIte]
                  rw [wiresOf_append_getD_lt gs [g] _ (by rw [hlen_in]; omega)]
                  exact hsem_old w (by omega) z u hu
            rcases hbuild_child false with ⟨B0, hB0, hU0, hpos0⟩
            rcases hbuild_child true with ⟨B1, hB1, hU1, hpos1⟩
            refine ⟨[B0, B1], ?_, ?_⟩
            · intro b hb; simp at hb; rcases hb with rfl | rfl; exact hB0; exact hB1
            · intro z x
              have hmem_iff : ∀ (b : Bool) (Bc : Branch k t), Bc.U = U' →
                  Bc.pos z = B.pos z + (if Bool.xor b ((wiresOf B.gates (bitsOf t z)).getD (B.off wa) false) then (1 : F2) else 0) • v0 →
                  (x - Bc.pos z ∈ Bc.U ↔
                    x - B.pos z ∈ B.U ∧
                      b = Bool.xor ((wiresOf B.gates (bitsOf t z)).getD (B.off wa) false)
                        (decide (dotProduct (B.slope wa) (x - B.pos z) = 1))) := by
                intro b Bc hUc hpc
                set ow := (wiresOf B.gates (bitsOf t z)).getD (B.off wa) false
                set cb := Bool.xor b ow
                set cf : F2 := if cb then 1 else 0
                have hdiff : x - Bc.pos z = (x - B.pos z) + cf • v0 := by
                  rw [hpc, zmod2_vec_sub_eq_add, zmod2_vec_sub_eq_add, add_assoc]
                rw [hUc, hdiff, mem_kerDot]
                constructor
                · rintro ⟨h1, h2⟩
                  have h1' : x - B.pos z ∈ B.U := by
                    have := B.U.add_mem h1 (B.U.smul_mem cf hv0)
                    rw [add_assoc, zmod2_vec_add_self, add_zero] at this
                    exact this
                  rw [dotProduct_add, dotProduct_smul, hdot, smul_eq_mul, mul_one] at h2
                  exact ⟨h1', (zmod2_xor_zero_iff b ow _).mp h2⟩
                · rintro ⟨h1, h2⟩
                  refine ⟨B.U.add_mem h1 (B.U.smul_mem cf hv0), ?_⟩
                  rw [dotProduct_add, dotProduct_smul, hdot, smul_eq_mul, mul_one]
                  exact (zmod2_xor_zero_iff b ow _).mpr h2
              constructor
              · intro hx
                cases htarget : Bool.xor ((wiresOf B.gates (bitsOf t z)).getD (B.off wa) false)
                    (decide (dotProduct (B.slope wa) (x - B.pos z) = 1))
                · refine ⟨⟨0, by simp⟩, ?_, ?_⟩
                  · exact (hmem_iff false B0 hU0 (hpos0 z)).mpr ⟨hx, htarget.symm⟩
                  · intro idx hidx
                    have hlt : idx.val < 2 := idx.isLt
                    interval_cases hv : idx.val
                    · exact Fin.ext hv
                    · exfalso
                      have hm : x - B1.pos z ∈ B1.U := by simpa [hv] using hidx
                      have := ((hmem_iff true B1 hU1 (hpos1 z)).mp hm).2
                      rw [htarget] at this; simp at this
                · refine ⟨⟨1, by simp⟩, ?_, ?_⟩
                  · exact (hmem_iff true B1 hU1 (hpos1 z)).mpr ⟨hx, htarget.symm⟩
                  · intro idx hidx
                    have hlt : idx.val < 2 := idx.isLt
                    interval_cases hv : idx.val
                    · exfalso
                      have hm : x - B0.pos z ∈ B0.U := by simpa [hv] using hidx
                      have := ((hmem_iff false B0 hU0 (hpos0 z)).mp hm).2
                      rw [htarget] at this; exact Bool.false_ne_true this
                    · exact Fin.ext hv
              · intro hnx idx hidx
                have hlt : idx.val < 2 := idx.isLt
                interval_cases hv : idx.val
                · have hm : x - B0.pos z ∈ B0.U := by simpa [hv] using hidx
                  exact hnx ((hmem_iff false B0 hU0 (hpos0 z)).mp hm).1
                · have hm : x - B1.pos z ∈ B1.U := by simpa [hv] using hidx
                  exact hnx ((hmem_iff true B1 hU1 (hpos1 z)).mp hm).1
        · exfalso; have := hshape.1; rw [hg] at this; simp at this
  ·
    rcases hg : g.inputs with _ | ⟨w0, rest⟩
    ·
      let gs' := B.gates ++ [⟨.or, []⟩]
      have hleg' : legalGates t gs' :=
        legalGates_snoc hB.2.1 (by simp) ⟨by simp, Or.inr (Or.inl rfl)⟩
      have hcost' : costGates gs' + B.r ≤ costGates (gs ++ [g]) := by
        rw [costGates_snoc_zero B.gates _ (by simp)]; have := hB.2.2.1; omega
      have hres := branch_eval_add_gate hleg hB gs' [⟨.or, []⟩] rfl hleg' hcost'
        (t + B.gates.length) (by simp [gs']) 0 (fun z u _ => by
          rw [hop, hg]
          have hidx : t + B.gates.length = (bitsOf t z).length + B.gates.length := by rw [bitsOf_len]
          rw [hidx, wiresOf_snoc_last]; simp [GateOp.eval])
      exact hwrap_one _ hres.1 rfl hres.2
    · rcases rest with _ | ⟨w1, rest2⟩
      ·
        have hw0 : w0 < k + t + gs.length := hback w0 (by rw [hg]; simp)
        have hres := branch_eval_add_gate hleg hB B.gates [] (by simp) hB.2.1
          (by have := hB.2.2.1; omega) (B.off w0) (hB.2.2.2.2.1 w0 hw0) (B.slope w0)
          (fun z u hu => by
            rw [hop, hg]; simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons,
              List.any_nil, id_eq, Bool.or_false]
            exact hB.2.2.2.2.2 w0 hw0 z u hu)
        exact hwrap_one _ hres.1 rfl hres.2
      · rcases rest2 with _ | ⟨_, _⟩
        ·
          have hw0 : w0 < k + t + gs.length := hback w0 (by rw [hg]; simp)
          have hw1 : w1 < k + t + gs.length := hback w1 (by rw [hg]; simp)
          have hcost1 : costGates (gs ++ [g]) = costGates gs + 1 :=
            costGates_snoc_one gs g ⟨Or.inr hop, by rw [hg]; rfl⟩
          by_cases hvan : (∀ u ∈ B.U, dotProduct (B.slope w0) u = 0) ∧
              (∀ u ∈ B.U, dotProduct (B.slope w1) u = 0)
          · let gs' := B.gates ++ [⟨.or, [B.off w0, B.off w1]⟩]
            have hleg' : legalGates t gs' :=
              legalGates_snoc hB.2.1
                (fun i hi => by simp at hi; rcases hi with rfl | rfl; exact hB.2.2.2.2.1 w0 hw0; exact hB.2.2.2.2.1 w1 hw1)
                ⟨by simp, Or.inr (Or.inl rfl)⟩
            have hcost' : costGates gs' + B.r ≤ costGates (gs ++ [g]) := by
              rw [costGates_snoc_one B.gates _ ⟨Or.inr rfl, rfl⟩, hcost1]; have := hB.2.2.1; omega
            have hres := branch_eval_add_gate hleg hB gs' [⟨.or, [B.off w0, B.off w1]⟩] rfl hleg' hcost'
              (t + B.gates.length) (by simp [gs']) 0 (fun z u hu => by
                rw [hop, hg]
                have hidx : t + B.gates.length = (bitsOf t z).length + B.gates.length := by rw [bitsOf_len]
                rw [hidx, wiresOf_snoc_last]
                simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
                  id_eq, Bool.or_false]
                rw [hB.2.2.2.2.2 w0 hw0 z u hu, hB.2.2.2.2.2 w1 hw1 z u hu,
                    hvan.1 u hu, hvan.2 u hu]
                simp)
            exact hwrap_one _ hres.1 rfl hres.2
          · have hex : ∃ (wa wb : ℕ), wa < k + t + gs.length ∧ wb < k + t + gs.length ∧
                ((wa = w0 ∧ wb = w1) ∨ (wa = w1 ∧ wb = w0)) ∧
                ∃ v0 ∈ B.U, dotProduct (B.slope wa) v0 = 1 := by
              by_cases h0 : ∀ u ∈ B.U, dotProduct (B.slope w0) u = 0
              · have h1 : ¬ ∀ u ∈ B.U, dotProduct (B.slope w1) u = 0 := fun h => hvan ⟨h0, h⟩
                push Not at h1
                rcases h1 with ⟨v0, hv0, hne⟩
                have hd1 : dotProduct (B.slope w1) v0 = 1 := by
                  rcases zmod2_cases (dotProduct (B.slope w1) v0) with h | h
                  · exact absurd h hne
                  · exact h
                exact ⟨w1, w0, hw1, hw0, Or.inr ⟨rfl, rfl⟩, v0, hv0, hd1⟩
              · push Not at h0
                rcases h0 with ⟨v0, hv0, hne⟩
                have hd1 : dotProduct (B.slope w0) v0 = 1 := by
                  rcases zmod2_cases (dotProduct (B.slope w0) v0) with h | h
                  · exact absurd h hne
                  · exact h
                exact ⟨w0, w1, hw0, hw1, Or.inl ⟨rfl, rfl⟩, v0, hv0, hd1⟩
            rcases hex with ⟨wa, wb, hwa, hwb, hwab, v0, hv0, hdot⟩
            let U' : Submodule F2 (Fin k → F2) := kerDot B.U (B.slope wa)
            have hdim' : Module.finrank F2 U' + (B.r + 1) = k := by
              have h1 : Module.finrank F2 U' + 1 = Module.finrank F2 B.U :=
                finrank_ker_dot B.U (B.slope wa) v0 hv0 hdot
              have h2 := hB.1
              omega
            have hbuild_child : ∀ (b : Bool), ∃ Bc : Branch k t,
                ValidBranch (gs ++ [g]) Bc ∧ Bc.U = U' ∧
                ∀ z : Fin t → F2,
                  Bc.pos z = B.pos z +
                    (if Bool.xor b ((wiresOf B.gates (bitsOf t z)).getD (B.off wa) false) then (1 : F2) else 0) • v0 := by
              intro b
              let gs0 := if b then B.gates ++ [⟨.not, [B.off wa]⟩] else B.gates
              let cWire := if b then t + B.gates.length else B.off wa
              have hgs0_ext : ∃ e0, gs0 = B.gates ++ e0 := by
                cases b
                · exact ⟨[], by simp [gs0]⟩
                · exact ⟨[⟨.not, [B.off wa]⟩], rfl⟩
              have hgs0_leg : legalGates t gs0 := by
                cases b
                · exact hB.2.1
                · exact legalGates_snoc hB.2.1 (fun i hi => by simp at hi; subst hi; exact hB.2.2.2.2.1 wa hwa)
                    ⟨by simp, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
              have hgs0_cost : costGates gs0 = costGates B.gates := by
                cases b
                · rfl
                · exact costGates_snoc_zero B.gates _ (by simp)
              have hcWire_lt : cWire < t + gs0.length := by
                cases b
                · exact hB.2.2.2.2.1 wa hwa
                · simp [gs0, cWire]
              have hcWire_sem : ∀ z : Fin t → F2,
                  (wiresOf gs0 (bitsOf t z)).getD cWire false =
                    Bool.xor b ((wiresOf B.gates (bitsOf t z)).getD (B.off wa) false) := by
                intro z
                cases b
                · simp [gs0, cWire]
                · simp only [gs0, cWire, ↓reduceIte]
                  have hidx : t + B.gates.length = (bitsOf t z).length + B.gates.length := by rw [bitsOf_len]
                  rw [hidx, wiresOf_snoc_last]
                  simp [GateOp.eval]
              let tapOld : ℕ → ℕ := fun j => if hj : j < k then B.tap ⟨j, hj⟩ else 0
              let flagTap : ℕ → Bool := fun j => if hj : j < k then decide (v0 ⟨j, hj⟩ = 1) else false
              let resT := addXorMany t cWire flagTap tapOld k gs0
              have hresT := addXorMany_spec t cWire flagTap tapOld k gs0 hgs0_leg hcWire_lt
                (fun j hj => by
                  simp only [tapOld, hj, ↓reduceDIte]
                  rcases hgs0_ext with ⟨e0, he0⟩
                  rw [he0, List.length_append]
                  have := hB.2.2.2.1 ⟨j, hj⟩; omega)
              rcases hresT with ⟨extT, hTeq, hTleg, hTcost, hTlt, hTsem⟩
              let flagOff : ℕ → Bool := fun w => decide (dotProduct (B.slope w) v0 = 1)
              let resO := addXorMany t cWire flagOff B.off (k + t + gs.length) resT.1
              have hresO := addXorMany_spec t cWire flagOff B.off (k + t + gs.length) resT.1 hTleg
                (by rw [hTeq, List.length_append]; omega)
                (fun w hw => by
                  rcases hgs0_ext with ⟨e0, he0⟩
                  rw [hTeq, he0, List.length_append, List.length_append]
                  have := hB.2.2.2.2.1 w hw; omega)
              rcases hresO with ⟨extO, hOeq, hOleg, hOcost, hOlt, hOsem⟩
              let gsF := if b then resO.1 ++ [⟨.and, []⟩] else resO.1
              have hgsF_ext : ∃ eF, gsF = resO.1 ++ eF := by
                cases b
                · exact ⟨[], by simp [gsF]⟩
                · exact ⟨[⟨.and, []⟩], rfl⟩
              have hgsF_leg : legalGates t gsF := by
                cases b
                · exact hOleg
                · exact legalGates_snoc hOleg (by simp) ⟨by simp, Or.inl rfl⟩
              have hgsF_cost : costGates gsF = costGates B.gates := by
                cases b
                · simp only [gsF, Bool.false_eq_true, ↓reduceIte]; rw [hOcost, hTcost, hgs0_cost]
                · rw [show gsF = resO.1 ++ [⟨.and, []⟩] from rfl, costGates_snoc_zero _ _ (by simp), hOcost, hTcost, hgs0_cost]
              let tapF : Fin k → ℕ := fun j => resT.2 j.val
              let wNew := if b then t + resO.1.length else resO.2 wb
              let sNew : Fin k → F2 := if b then 0 else B.slope wb
              let Bc : Branch k t :=
                ⟨B.r + 1, U', gsF, tapF,
                  fun w => if w = k + t + gs.length then wNew else resO.2 w,
                  fun w => if w = k + t + gs.length then sNew else B.slope w⟩
              have hpos_c : ∀ z : Fin t → F2,
                  Bc.pos z = B.pos z +
                    (if Bool.xor b ((wiresOf B.gates (bitsOf t z)).getD (B.off wa) false) then (1 : F2) else 0) • v0 := by
                intro z; funext j
                rcases hgsF_ext with ⟨eF, heF⟩
                rcases hgs0_ext with ⟨e0, he0⟩
                have htap_val : (wiresOf gsF (bitsOf t z)).getD (tapF j) false =
                    (wiresOf resT.1 (bitsOf t z)).getD (resT.2 j.val) false := by
                  rw [heF, hOeq, List.append_assoc,
                      wiresOf_append_getD_lt resT.1 _ (bitsOf t z) (by rw [bitsOf_len]; exact hTlt j.val j.isLt)]
                simp only [Branch.r, Branch.U, Branch.gates, Branch.tap, Branch.off, Branch.slope, Branch.pos, Bc, htap_val]
                rw [hTsem j.val j.isLt (bitsOf t z) (bitsOf_len t z)]
                simp only [flagTap, tapOld, j.isLt, ↓reduceDIte, hcWire_sem z]
                rw [he0, wiresOf_append_getD_lt B.gates e0 (bitsOf t z) (by rw [bitsOf_len]; exact hB.2.2.2.1 j)]
                simp only [Branch.r, Branch.U, Branch.gates, Branch.tap, Branch.off, Branch.slope, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Branch.pos]
                cases (wiresOf B.gates (bitsOf t z)).getD (B.tap j) false <;>
                  cases Bool.xor b ((wiresOf B.gates (bitsOf t z)).getD (B.off wa) false) <;>
                  rcases zmod2_cases (v0 j) with h | h <;> simp [h] <;> decide
              have hsem_old : ∀ w < k + t + gs.length, ∀ (z : Fin t → F2) (u : Fin k → F2), u ∈ U' →
                  (wiresOf gs (bitsOf k (Bc.pos z + u) ++ bitsOf t z)).getD w false =
                    Bool.xor ((wiresOf gsF (bitsOf t z)).getD (resO.2 w) false)
                      (decide (dotProduct (B.slope w) u = 1)) := by
                intro w hw z u hu
                rcases hgsF_ext with ⟨eF, heF⟩
                rcases hgs0_ext with ⟨e0, he0⟩
                set cbit := Bool.xor b ((wiresOf B.gates (bitsOf t z)).getD (B.off wa) false)
                set cf : F2 := if cbit then 1 else 0
                have hu_in_B : cf • v0 + u ∈ B.U := B.U.add_mem (B.U.smul_mem cf hv0) hu.1
                have hpos_rw : Bc.pos z + u = B.pos z + (cf • v0 + u) := by
                  rw [hpos_c z, add_assoc]
                rw [hpos_rw, hB.2.2.2.2.2 w hw z (cf • v0 + u) hu_in_B]
                have hwireO : (wiresOf gsF (bitsOf t z)).getD (resO.2 w) false =
                    if decide (dotProduct (B.slope w) v0 = 1) then
                      Bool.xor ((wiresOf B.gates (bitsOf t z)).getD (B.off w) false) cbit
                    else (wiresOf B.gates (bitsOf t z)).getD (B.off w) false := by
                  rw [heF, wiresOf_append_getD_lt resO.1 eF (bitsOf t z) (by rw [bitsOf_len]; exact hOlt w hw)]
                  rw [hOsem w hw (bitsOf t z) (bitsOf_len t z)]
                  rw [hTeq,
                      wiresOf_append_getD_lt gs0 extT (bitsOf t z) (by rw [bitsOf_len, he0, List.length_append]; have := hB.2.2.2.2.1 w hw; omega),
                      wiresOf_append_getD_lt gs0 extT (bitsOf t z) (by rw [bitsOf_len]; exact hcWire_lt)]
                  rw [hcWire_sem z, he0, wiresOf_append_getD_lt B.gates e0 (bitsOf t z) (by rw [bitsOf_len]; exact hB.2.2.2.2.1 w hw)]
                rw [hwireO, dotProduct_add, dotProduct_smul, zmod2_add_decide, smul_eq_mul, zmod2_mul_decide, zmod2_bool_decide]
                cases (wiresOf B.gates (bitsOf t z)).getD (B.off w) false <;>
                  cases cbit <;> cases decide (dotProduct (B.slope w) v0 = 1) <;>
                  cases decide (dotProduct (B.slope w) u = 1) <;> decide
              refine ⟨Bc, ⟨hdim', hgsF_leg, by change costGates gsF + (B.r + 1) ≤ costGates (gs ++ [g]); rw [hgsF_cost, hcost1]; have := hB.2.2.1; omega, ?_, ?_, ?_⟩, rfl, hpos_c⟩
              · intro j
                rcases hgsF_ext with ⟨eF, heF⟩
                have h1 : resT.2 j.val < t + resT.1.length := hTlt j.val j.isLt
                have h2 : resO.1.length = resT.1.length + extO.length := by rw [hOeq, List.length_append]
                simp only [Branch.r, Branch.U, Branch.gates, Branch.tap, Branch.off, Branch.slope, Bc, tapF, heF, List.length_append]
                omega
              · intro w hw
                simp only [List.length_append, List.length_cons, List.length_nil] at hw
                simp only [Branch.r, Branch.U, Branch.gates, Branch.tap, Branch.off, Branch.slope, Bc]
                by_cases hweq : w = k + t + gs.length
                · simp only [hweq, ↓reduceIte, wNew, gsF]
                  cases b
                  · simp only [Bool.false_eq_true, ↓reduceIte]; exact hOlt wb hwb
                  · simp
                · simp only [hweq, ↓reduceIte]
                  rcases hgsF_ext with ⟨eF, heF⟩
                  have h1 : resO.2 w < t + resO.1.length := hOlt w (by omega)
                  rw [heF, List.length_append]; omega
              · intro w hw z u hu
                simp only [List.length_append, List.length_cons, List.length_nil] at hw
                have hlen_in : (bitsOf k (Bc.pos z + u) ++ bitsOf t z).length = k + t := by simp [bitsOf_len]
                by_cases hweq : w = k + t + gs.length
                · subst hweq
                  simp only [Branch.r, Branch.U, Branch.gates, Branch.tap, Branch.off, Branch.slope, Bc, ↓reduceIte]
                  rw [wiresOf_snoc_last_eq gs g _ hlen_in, hop, hg]
                  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
                    id_eq, Bool.or_false]
                  have hwa_val : (wiresOf gs (bitsOf k (Bc.pos z + u) ++ bitsOf t z)).getD wa false = b := by
                    have hu2 : dotProduct (B.slope wa) u = 0 := hu.2
                    rw [hsem_old wa hwa z u hu, hu2]
                    rcases hgsF_ext with ⟨eF, heF⟩
                    rcases hgs0_ext with ⟨e0, he0⟩
                    rw [heF, wiresOf_append_getD_lt resO.1 eF (bitsOf t z) (by rw [bitsOf_len]; exact hOlt wa hwa)]
                    rw [hOsem wa hwa (bitsOf t z) (bitsOf_len t z)]
                    simp only [flagOff, hdot]
                    rw [hTeq,
                        wiresOf_append_getD_lt gs0 extT (bitsOf t z) (by rw [bitsOf_len, he0, List.length_append]; have := hB.2.2.2.2.1 wa hwa; omega),
                        wiresOf_append_getD_lt gs0 extT (bitsOf t z) (by rw [bitsOf_len]; exact hcWire_lt)]
                    rw [hcWire_sem z, he0, wiresOf_append_getD_lt B.gates e0 (bitsOf t z) (by rw [bitsOf_len]; exact hB.2.2.2.2.1 wa hwa)]
                    cases b <;> cases (wiresOf B.gates (bitsOf t z)).getD (B.off wa) false <;> decide
                  have hcomm : ((wiresOf gs (bitsOf k (Bc.pos z + u) ++ bitsOf t z)).getD w0 false ||
                      (wiresOf gs (bitsOf k (Bc.pos z + u) ++ bitsOf t z)).getD w1 false) =
                      ((wiresOf gs (bitsOf k (Bc.pos z + u) ++ bitsOf t z)).getD wa false ||
                       (wiresOf gs (bitsOf k (Bc.pos z + u) ++ bitsOf t z)).getD wb false) := by
                    rcases hwab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                    · rfl
                    · exact Bool.or_comm _ _
                  rw [hcomm, hwa_val]
                  cases b
                  · simp only [Bool.false_or, wNew, sNew, gsF, Bool.false_eq_true, ↓reduceIte]
                    exact hsem_old wb hwb z u hu
                  · simp only [Bool.true_or, wNew, sNew, gsF, ↓reduceIte]
                    rw [wiresOf_snoc_last_eq resO.1 ⟨.and, []⟩ (bitsOf t z) (bitsOf_len t z)]; simp [GateOp.eval]
                · simp only [Branch.r, Branch.U, Branch.gates, Branch.tap, Branch.off, Branch.slope, Bc, hweq, ↓reduceIte]
                  rw [wiresOf_append_getD_lt gs [g] _ (by rw [hlen_in]; omega)]
                  exact hsem_old w (by omega) z u hu
            rcases hbuild_child false with ⟨B0, hB0, hU0, hpos0⟩
            rcases hbuild_child true with ⟨B1, hB1, hU1, hpos1⟩
            refine ⟨[B0, B1], ?_, ?_⟩
            · intro b hb; simp at hb; rcases hb with rfl | rfl; exact hB0; exact hB1
            · intro z x
              have hmem_iff : ∀ (b : Bool) (Bc : Branch k t), Bc.U = U' →
                  Bc.pos z = B.pos z + (if Bool.xor b ((wiresOf B.gates (bitsOf t z)).getD (B.off wa) false) then (1 : F2) else 0) • v0 →
                  (x - Bc.pos z ∈ Bc.U ↔
                    x - B.pos z ∈ B.U ∧
                      b = Bool.xor ((wiresOf B.gates (bitsOf t z)).getD (B.off wa) false)
                        (decide (dotProduct (B.slope wa) (x - B.pos z) = 1))) := by
                intro b Bc hUc hpc
                set ow := (wiresOf B.gates (bitsOf t z)).getD (B.off wa) false
                set cb := Bool.xor b ow
                set cf : F2 := if cb then 1 else 0
                have hdiff : x - Bc.pos z = (x - B.pos z) + cf • v0 := by
                  rw [hpc, zmod2_vec_sub_eq_add, zmod2_vec_sub_eq_add, add_assoc]
                rw [hUc, hdiff, mem_kerDot]
                constructor
                · rintro ⟨h1, h2⟩
                  have h1' : x - B.pos z ∈ B.U := by
                    have := B.U.add_mem h1 (B.U.smul_mem cf hv0)
                    rw [add_assoc, zmod2_vec_add_self, add_zero] at this
                    exact this
                  rw [dotProduct_add, dotProduct_smul, hdot, smul_eq_mul, mul_one] at h2
                  exact ⟨h1', (zmod2_xor_zero_iff b ow _).mp h2⟩
                · rintro ⟨h1, h2⟩
                  refine ⟨B.U.add_mem h1 (B.U.smul_mem cf hv0), ?_⟩
                  rw [dotProduct_add, dotProduct_smul, hdot, smul_eq_mul, mul_one]
                  exact (zmod2_xor_zero_iff b ow _).mpr h2
              constructor
              · intro hx
                cases htarget : Bool.xor ((wiresOf B.gates (bitsOf t z)).getD (B.off wa) false)
                    (decide (dotProduct (B.slope wa) (x - B.pos z) = 1))
                · refine ⟨⟨0, by simp⟩, ?_, ?_⟩
                  · exact (hmem_iff false B0 hU0 (hpos0 z)).mpr ⟨hx, htarget.symm⟩
                  · intro idx hidx
                    have hlt : idx.val < 2 := idx.isLt
                    interval_cases hv : idx.val
                    · exact Fin.ext hv
                    · exfalso
                      have hm : x - B1.pos z ∈ B1.U := by simpa [hv] using hidx
                      have := ((hmem_iff true B1 hU1 (hpos1 z)).mp hm).2
                      rw [htarget] at this; simp at this
                · refine ⟨⟨1, by simp⟩, ?_, ?_⟩
                  · exact (hmem_iff true B1 hU1 (hpos1 z)).mpr ⟨hx, htarget.symm⟩
                  · intro idx hidx
                    have hlt : idx.val < 2 := idx.isLt
                    interval_cases hv : idx.val
                    · exfalso
                      have hm : x - B0.pos z ∈ B0.U := by simpa [hv] using hidx
                      have := ((hmem_iff false B0 hU0 (hpos0 z)).mp hm).2
                      rw [htarget] at this; exact Bool.false_ne_true this
                    · exact Fin.ext hv
              · intro hnx idx hidx
                have hlt : idx.val < 2 := idx.isLt
                interval_cases hv : idx.val
                · have hm : x - B0.pos z ∈ B0.U := by simpa [hv] using hidx
                  exact hnx ((hmem_iff false B0 hU0 (hpos0 z)).mp hm).1
                · have hm : x - B1.pos z ∈ B1.U := by simpa [hv] using hidx
                  exact hnx ((hmem_iff true B1 hU1 (hpos1 z)).mp hm).1
        · exfalso; have := hshape.1; rw [hg] at this; simp at this
  ·
    rcases hg : g.inputs with _ | ⟨w0, rest⟩
    ·
      let gs' := B.gates ++ [⟨.mod 2, []⟩]
      have hleg' : legalGates t gs' :=
        legalGates_snoc hB.2.1 (by simp) ⟨by simp, Or.inr (Or.inr (Or.inl rfl))⟩
      have hcost' : costGates gs' + B.r ≤ costGates (gs ++ [g]) := by
        rw [costGates_snoc_zero B.gates _ (by simp)]; have := hB.2.2.1; omega
      have hres := branch_eval_add_gate hleg hB gs' [⟨.mod 2, []⟩] rfl hleg' hcost'
        (t + B.gates.length) (by simp [gs']) 0 (fun z u _ => by
          rw [hop, hg]
          have hidx : t + B.gates.length = (bitsOf t z).length + B.gates.length := by rw [bitsOf_len]
          rw [hidx, wiresOf_snoc_last]; simp [GateOp.eval])
      exact hwrap_one _ hres.1 rfl hres.2
    · rcases rest with _ | ⟨w1, rest2⟩
      ·
        have hw0 : w0 < k + t + gs.length := hback w0 (by rw [hg]; simp)
        let gs' := B.gates ++ [⟨.not, [B.off w0]⟩]
        have hleg' : legalGates t gs' :=
          legalGates_snoc hB.2.1 (fun i hi => by simp at hi; subst hi; exact hB.2.2.2.2.1 w0 hw0)
            ⟨by simp, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
        have hcost' : costGates gs' + B.r ≤ costGates (gs ++ [g]) := by
          rw [costGates_snoc_zero B.gates _ (by simp)]; have := hB.2.2.1; omega
        have hres := branch_eval_add_gate hleg hB gs' [⟨.not, [B.off w0]⟩] rfl hleg' hcost'
          (t + B.gates.length) (by simp [gs']) (B.slope w0) (fun z u hu => by
            rw [hop, hg]
            have hidx : t + B.gates.length = (bitsOf t z).length + B.gates.length := by rw [bitsOf_len]
            rw [hidx, wiresOf_snoc_last]
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
            rw [hB.2.2.2.2.2 w0 hw0 z u hu]
            cases (wiresOf B.gates (bitsOf t z)).getD (B.off w0) false <;>
              cases decide (dotProduct (B.slope w0) u = 1) <;> decide)
        exact hwrap_one _ hres.1 rfl hres.2
      · rcases rest2 with _ | ⟨_, _⟩
        ·
          have hw0 : w0 < k + t + gs.length := hback w0 (by rw [hg]; simp)
          have hw1 : w1 < k + t + gs.length := hback w1 (by rw [hg]; simp)
          let gs' := B.gates ++ [⟨.mod 2, [B.off w0, B.off w1]⟩]
          have hleg' : legalGates t gs' :=
            legalGates_snoc hB.2.1
              (fun i hi => by simp at hi; rcases hi with rfl | rfl; exact hB.2.2.2.2.1 w0 hw0; exact hB.2.2.2.2.1 w1 hw1)
              ⟨by simp, Or.inr (Or.inr (Or.inl rfl))⟩
          have hcost' : costGates gs' + B.r ≤ costGates (gs ++ [g]) := by
            rw [costGates_snoc_zero B.gates _ (by simp)]; have := hB.2.2.1; omega
          have hres := branch_eval_add_gate hleg hB gs' [⟨.mod 2, [B.off w0, B.off w1]⟩] rfl hleg' hcost'
            (t + B.gates.length) (by simp [gs']) (B.slope w0 + B.slope w1) (fun z u hu => by
              rw [hop, hg]
              have hidx : t + B.gates.length = (bitsOf t z).length + B.gates.length := by rw [bitsOf_len]
              rw [hidx, wiresOf_snoc_last]
              simp only [List.map_cons, List.map_nil, GateOp.eval]
              rw [hB.2.2.2.2.2 w0 hw0 z u hu, hB.2.2.2.2.2 w1 hw1 z u hu, add_dotProduct, zmod2_add_decide]
              cases (wiresOf B.gates (bitsOf t z)).getD (B.off w0) false <;>
                cases (wiresOf B.gates (bitsOf t z)).getD (B.off w1) false <;>
                cases decide (dotProduct (B.slope w0) u = 1) <;>
                cases decide (dotProduct (B.slope w1) u = 1) <;> decide)
          exact hwrap_one _ hres.1 rfl hres.2
        · exfalso; have := hshape.1; rw [hg] at this; simp at this
  ·
    rcases hg : g.inputs with _ | ⟨w0, rest⟩
    · simp [hg] at hlen1
    · rcases rest with _ | ⟨_, _⟩
      · have hw0 : w0 < k + t + gs.length := hback w0 (by rw [hg]; simp)
        let gs' := B.gates ++ [⟨.not, [B.off w0]⟩]
        have hleg' : legalGates t gs' :=
          legalGates_snoc hB.2.1 (fun i hi => by simp at hi; subst hi; exact hB.2.2.2.2.1 w0 hw0)
            ⟨by simp, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
        have hcost' : costGates gs' + B.r ≤ costGates (gs ++ [g]) := by
          rw [costGates_snoc_zero B.gates _ (by simp)]; have := hB.2.2.1; omega
        have hres := branch_eval_add_gate hleg hB gs' [⟨.not, [B.off w0]⟩] rfl hleg' hcost'
          (t + B.gates.length) (by simp [gs']) (B.slope w0) (fun z u hu => by
            rw [hop, hg]
            have hidx : t + B.gates.length = (bitsOf t z).length + B.gates.length := by rw [bitsOf_len]
            rw [hidx, wiresOf_snoc_last]
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
            rw [hB.2.2.2.2.2 w0 hw0 z u hu]
            cases (wiresOf B.gates (bitsOf t z)).getD (B.off w0) false <;>
              cases decide (dotProduct (B.slope w0) u = 1) <;> decide)
        exact hwrap_one _ hres.1 rfl hres.2
      · simp [hg] at hlen1

lemma build_branch_list (k t : ℕ) (gs : List Gate) (hleg : legalGates (k + t) gs) :
    ∃ L : List (Branch k t),
      0 < L.length ∧
      (∀ B ∈ L, ValidBranch gs B) ∧
      ∀ (z : Fin t → F2) (x : Fin k → F2),
        ∃! idx : Fin L.length, x - (L.get idx).pos z ∈ (L.get idx).U := by
  induction gs using List.reverseRecOn with
  | nil =>
    let g0 : List Gate := [⟨.or, []⟩]
    let B0 : Branch k t :=
      ⟨0, ⊤, g0, fun _ => t,
        fun w => if w < k then t else w - k,
        fun w => if hw : w < k then Pi.single ⟨w, hw⟩ (1 : F2) else 0⟩
    have hleg0 : legalGates t g0 := by
      have hnil : legalGates t [] := ⟨fun j hj => by simp at hj, fun h hh => by simp at hh⟩
      exact legalGates_snoc hnil (by simp) ⟨by simp, Or.inr (Or.inl rfl)⟩
    have hg0_val : ∀ z : Fin t → F2, (wiresOf g0 (bitsOf t z)).getD t false = false := by
      intro z
      have h1 := wiresOf_snoc_last_eq ([] : List Gate) ⟨.or, []⟩ (bitsOf t z) (bitsOf_len t z)
      simpa [g0, GateOp.eval] using h1
    have hpos0 : ∀ z : Fin t → F2, B0.pos z = 0 := by
      intro z; funext j
      simp only [Branch.r, Branch.U, Branch.gates, Branch.tap, Branch.off, Branch.slope, Branch.pos, B0, Pi.zero_apply, hg0_val z]
      rfl
    have hvalid0 : ValidBranch [] B0 := by
      refine ⟨?_, hleg0, ?_, fun _ => by simp [Branch.r, Branch.U, Branch.gates, Branch.tap, Branch.off, Branch.slope, B0, g0], ?_, ?_⟩
      · simp [Branch.r, Branch.U, Branch.gates, Branch.tap, Branch.off, Branch.slope, B0]
      · simp [Branch.r, Branch.U, Branch.gates, Branch.tap, Branch.off, Branch.slope, B0, g0, costGates]
      · intro w hw
        simp only [List.length_nil, Nat.add_zero] at hw
        simp only [Branch.r, Branch.U, Branch.gates, Branch.tap, Branch.off, Branch.slope, B0, g0, List.length_singleton]
        split_ifs <;> omega
      · intro w hw z u _
        simp only [List.length_nil, Nat.add_zero] at hw
        rw [hpos0 z, zero_add]
        conv_lhs => simp only [wiresOf, Circuit.wires, List.foldl_nil]
        simp only [Branch.r, Branch.U, Branch.gates, Branch.tap, Branch.off, Branch.slope, B0]
        by_cases hwk : w < k
        · simp only [hwk, ↓reduceIte, ↓reduceDIte]
          have h1 : (bitsOf k u ++ bitsOf t z).getD w false = decide (u ⟨w, hwk⟩ = 1) := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [bitsOf_len]; exact hwk)]
            exact bitsOf_getD k u ⟨w, hwk⟩
          rw [h1, hg0_val z]
          simp
        · simp only [hwk, ↓reduceIte, ↓reduceDIte]
          have h1 : (bitsOf k u ++ bitsOf t z).getD w false = (bitsOf t z).getD (w - k) false := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [bitsOf_len]; omega),
                bitsOf_len, List.getD_eq_getElem?_getD]
          have h2 : (wiresOf g0 (bitsOf t z)).getD (w - k) false = (bitsOf t z).getD (w - k) false :=
            wiresOf_getD_lt g0 (bitsOf t z) (by rw [bitsOf_len]; omega)
          rw [h1, h2]; simp
    refine ⟨[B0], by simp, fun b hb => by simp at hb; subst hb; exact hvalid0, fun z x => ?_⟩
    exact ⟨⟨0, by simp⟩, by simp [Branch.r, Branch.U, Branch.gates, Branch.tap, Branch.off, Branch.slope, B0], fun idx _ => Fin.ext (by have := idx.isLt; simp only [List.length_singleton] at this; change idx.val = 0; omega)⟩
  | append_singleton gs g ih =>
    have hpre := legalGates_prefix hleg
    rcases ih hpre.1 with ⟨L, hLpos, hLval, hLpart⟩
    have hstep_all : ∀ idx : Fin L.length, ∃ Lc : List (Branch k t),
        (∀ B' ∈ Lc, ValidBranch (gs ++ [g]) B') ∧
        ∀ (z : Fin t → F2) (x : Fin k → F2),
          (x - (L.get idx).pos z ∈ (L.get idx).U → ∃! j : Fin Lc.length, x - (Lc.get j).pos z ∈ (Lc.get j).U) ∧
          (x - (L.get idx).pos z ∉ (L.get idx).U → ∀ j : Fin Lc.length, x - (Lc.get j).pos z ∉ (Lc.get j).U) :=
      fun idx => step_single_branch (L.get idx) hleg (hLval _ (List.get_mem L idx))
    let children : Fin L.length → List (Branch k t) := fun idx => (hstep_all idx).choose
    have hchildren_spec : ∀ idx : Fin L.length,
        (∀ B' ∈ children idx, ValidBranch (gs ++ [g]) B') ∧
        ∀ (z : Fin t → F2) (x : Fin k → F2),
          (x - (L.get idx).pos z ∈ (L.get idx).U →
            ∃! j : Fin (children idx).length, x - ((children idx).get j).pos z ∈ ((children idx).get j).U) ∧
          (x - (L.get idx).pos z ∉ (L.get idx).U →
            ∀ j : Fin (children idx).length, x - ((children idx).get j).pos z ∉ ((children idx).get j).U) :=
      fun idx => (hstep_all idx).choose_spec
    let L' : List (Branch k t) := (List.finRange L.length).flatMap children
    have hpart_L' : ∀ (z : Fin t → F2) (x : Fin k → F2),
        ∃! idx' : Fin L'.length, x - (L'.get idx').pos z ∈ (L'.get idx').U := by
      intro z x
      have hflat_bij : ∀ (ms : List (Fin L.length)),
          (∀ a ∈ ms, ∀ b ∈ ms, a = b → True) →
          ms.Nodup →
          ∀ (p : Branch k t → Prop),
            (∃ idx ∈ ms, (∃! j : Fin (children idx).length, p ((children idx).get j)) ∧
              ∀ idx2 ∈ ms, idx2 ≠ idx → ∀ j : Fin (children idx2).length, ¬ p ((children idx2).get j)) →
            ∃! q : Fin (ms.flatMap children).length, p ((ms.flatMap children).get q) := by
        intro ms _ hnd p
        induction ms with
        | nil => rintro ⟨_, h, _⟩; simp at h
        | cons a ms ihms =>
          rintro ⟨idx, hidx, huniq, hrest⟩
          rw [List.nodup_cons] at hnd
          change ∃! q : Fin (children a ++ ms.flatMap children).length, p ((children a ++ ms.flatMap children).get q)
          rcases List.mem_cons.mp hidx with rfl | hmem
          · rcases huniq with ⟨j0, hj0, hj0u⟩
            refine ⟨⟨j0.val, by simp only [List.length_append]; omega⟩, ?_, ?_⟩
            · dsimp only
              rw [List.get_eq_getElem, List.getElem_append_left j0.isLt]
              exact hj0
            · intro q hq
              by_cases hql : q.val < (children idx).length
              · have hq' : p ((children idx).get ⟨q.val, hql⟩) := by
                  simpa [List.get_eq_getElem, List.getElem_append_left hql] using hq
                have := hj0u ⟨q.val, hql⟩ hq'
                exact Fin.ext (by simpa using congrArg Fin.val this)
              · exfalso
                have hqr : q.val - (children idx).length < (ms.flatMap children).length := by
                  have := q.isLt; simp only [List.length_append] at this; omega
                have hq' : p ((ms.flatMap children).get ⟨q.val - (children idx).length, hqr⟩) := by
                  simpa [List.get_eq_getElem, List.getElem_append_right (by omega : (children idx).length ≤ q.val)] using hq
                have hmem_b : (ms.flatMap children).get ⟨q.val - (children idx).length, hqr⟩ ∈ ms.flatMap children :=
                  List.get_mem _ _
                rcases List.mem_flatMap.mp hmem_b with ⟨idx2, hidx2, hb2⟩
                rcases List.mem_iff_get.mp hb2 with ⟨j2, hj2⟩
                have hne2 : idx2 ≠ idx := fun heq => hnd.1 (heq ▸ hidx2)
                exact hrest idx2 (List.mem_cons_of_mem idx hidx2) hne2 j2 (hj2.symm ▸ hq')
          · have hih := ihms (fun _ _ _ _ _ => trivial) hnd.2 ⟨idx, hmem, huniq, fun idx2 hi2 hne2 => hrest idx2 (List.mem_cons_of_mem a hi2) hne2⟩
            rcases hih with ⟨q0, hq0, hq0u⟩
            refine ⟨⟨(children a).length + q0.val, by simp only [List.length_append]; omega⟩, ?_, ?_⟩
            · simp only [List.get_eq_getElem, List.getElem_append_right (by omega : (children a).length ≤ (children a).length + q0.val),
                Nat.add_sub_cancel_left]
              exact hq0
            · intro q hq
              by_cases hql : q.val < (children a).length
              · exfalso
                have hq' : p ((children a).get ⟨q.val, hql⟩) := by
                  simpa [List.get_eq_getElem, List.getElem_append_left hql] using hq
                have hne : a ≠ idx := fun heq => hnd.1 (heq ▸ hmem)
                exact hrest a (List.mem_cons_self) hne ⟨q.val, hql⟩ hq'
              · have hqr : q.val - (children a).length < (ms.flatMap children).length := by
                  have := q.isLt; simp only [List.length_append] at this; omega
                have hq' : p ((ms.flatMap children).get ⟨q.val - (children a).length, hqr⟩) := by
                  simpa [List.get_eq_getElem, List.getElem_append_right (by omega : (children a).length ≤ q.val)] using hq
                have heq := hq0u ⟨q.val - (children a).length, hqr⟩ hq'
                apply Fin.ext
                have := congrArg Fin.val heq
                dsimp at this ⊢; omega
      rcases hLpart z x with ⟨idx0, hidx0, hidx0u⟩
      apply hflat_bij (List.finRange L.length) (fun _ _ _ _ _ => trivial) (List.nodup_finRange L.length)
        (fun B => x - B.pos z ∈ B.U)
      refine ⟨idx0, List.mem_finRange idx0, ((hchildren_spec idx0).2 z x).1 hidx0, ?_⟩
      intro idx2 _ hne2
      have hnot2 : x - (L.get idx2).pos z ∉ (L.get idx2).U := fun hm => hne2 (hidx0u idx2 hm)
      exact ((hchildren_spec idx2).2 z x).2 hnot2
    have hL'pos : 0 < L'.length := by
      rcases hpart_L' 0 0 with ⟨idx0, _, _⟩
      exact Nat.pos_of_ne_zero (fun h0 => by have := idx0.isLt; omega)
    refine ⟨L', hL'pos, ?_, hpart_L'⟩
    intro B' hB'
    rcases List.mem_flatMap.mp hB' with ⟨idx, _, hmem⟩
    exact (hchildren_spec idx).1 B' hmem

open Classical

lemma vec_eq_sum_single {k : ℕ} (v : Fin k → F2) :
    v = ∑ i : Fin k, v i • Pi.single i (1 : F2) := by
  funext j
  simp [Finset.sum_apply, Pi.single_apply]

lemma decomp_835 (k t : ℕ) (C : Circuit) (hC : legalGates (k + t) C.gates) :
    ∃ (N : ℕ) (r : Fin N → ℕ) (U : Fin N → Submodule F2 (Fin k → F2)) (a : Fin N → (Fin k → F2))
      (D : Fin N → Circuit) (tap : Fin N → Fin k → ℕ),
      let pos := fun (i : Fin N) (z : Fin t → F2) (j : Fin k) =>
        if ((D i).wires (bitsOf t z)).getD (tap i j) false then (1 : F2) else 0
      0 < N ∧ (∀ i, Module.finrank F2 (U i) + r i = k ∧ legalGates t (D i).gates ∧
        costGates (D i).gates + r i ≤ costGates C.gates ∧ (D i).output < t + (D i).size ∧
        ∀ j, tap i j < t + (D i).size) ∧
      (∀ (z : Fin t → F2) (x : Fin k → F2), ∃! i : Fin N, x - pos i z ∈ U i) ∧
      ∀ (i : Fin N) (z : Fin t → F2) (u : Fin k → F2), u ∈ U i →
        C.eval (bitsOf k (pos i z + u) ++ bitsOf t z) =
          Bool.xor ((D i).eval (bitsOf t z)) (decide (dotProduct (a i) u = 1)) := by
  rcases build_branch_list k t C.gates hC with ⟨L, hLpos, hLval, hLpart⟩
  by_cases hout : C.output < k + t + C.gates.length
  · refine ⟨L.length,
      fun i => (L.get i).r,
      fun i => (L.get i).U,
      fun i => (L.get i).slope C.output,
      fun i => ⟨(L.get i).gates, (L.get i).off C.output⟩,
      fun i => (L.get i).tap,
      hLpos, ?_, ?_, ?_⟩
    · intro i
      have hBi := hLval (L.get i) (List.get_mem L i)
      exact ⟨hBi.1, hBi.2.1, hBi.2.2.1, hBi.2.2.2.2.1 C.output hout, hBi.2.2.2.1⟩
    · intro z x
      exact hLpart z x
    · intro i z u hu
      have hBi := hLval (L.get i) (List.get_mem L i)
      exact hBi.2.2.2.2.2 C.output hout z u hu
  · refine ⟨L.length,
      fun i => (L.get i).r,
      fun i => (L.get i).U,
      fun _ => 0,
      fun i => ⟨(L.get i).gates ++ [⟨.or, []⟩], t + (L.get i).gates.length⟩,
      fun i => (L.get i).tap,
      hLpos, ?_, ?_, ?_⟩
    · intro i
      have hBi := hLval (L.get i) (List.get_mem L i)
      refine ⟨hBi.1, ?_, ?_, by simp [Circuit.size], ?_⟩
      · exact legalGates_snoc hBi.2.1 (by simp) ⟨by simp, Or.inr (Or.inl rfl)⟩
      · have hc0 := costGates_snoc_zero (L.get i).gates ⟨.or, []⟩ (by simp)
        have := hBi.2.2.1
        change costGates ((L.get i).gates ++ [⟨.or, []⟩]) + (L.get i).r ≤ costGates C.gates
        omega
      · intro j
        simp only [Circuit.size, List.length_append, List.length_singleton]
        have := hBi.2.2.2.1 j; omega
    · intro z x
      have hpeq : ∀ i : Fin L.length,
          (fun j : Fin k => if (Circuit.wires ⟨(L.get i).gates ++ [⟨.or, []⟩], t + (L.get i).gates.length⟩ (bitsOf t z)).getD ((L.get i).tap j) false then (1 : F2) else 0) =
          (L.get i).pos z := by
        intro i; funext j
        have hBi := hLval (L.get i) (List.get_mem L i)
        change (if (wiresOf ((L.get i).gates ++ [⟨.or, []⟩]) (bitsOf t z)).getD ((L.get i).tap j) false then (1 : F2) else 0) = _
        rw [wiresOf_append_getD_lt (L.get i).gates [⟨.or, []⟩] _
          (by rw [bitsOf_len]; exact hBi.2.2.2.1 j)]
        rfl
      have hconv : (fun i : Fin L.length => x - (fun j : Fin k => if (Circuit.wires ⟨(L.get i).gates ++ [⟨.or, []⟩], t + (L.get i).gates.length⟩ (bitsOf t z)).getD ((L.get i).tap j) false then (1 : F2) else 0) ∈ (L.get i).U) =
          (fun i : Fin L.length => x - (L.get i).pos z ∈ (L.get i).U) := by
        funext i; rw [hpeq i]
      exact (congrArg (fun P => ∃! i : Fin L.length, P i) hconv).mpr (hLpart z x)
    · intro i z u _
      have hlhs : ∀ v : Fin k → F2, C.eval (bitsOf k v ++ bitsOf t z) = false := by
        intro v
        have hclen : (C.wires (bitsOf k v ++ bitsOf t z)).length = k + t + C.gates.length := by
          have h := wiresOf_len C.gates (bitsOf k v ++ bitsOf t z)
          simp only [List.length_append, bitsOf_len] at h
          exact h
        unfold Circuit.eval
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
        rfl
      have hrhs : (Circuit.mk ((L.get i).gates ++ [⟨.or, []⟩]) (t + (L.get i).gates.length)).eval (bitsOf t z) = false := by
        unfold Circuit.eval
        change (wiresOf ((L.get i).gates ++ [⟨.or, []⟩]) (bitsOf t z)).getD (t + (L.get i).gates.length) false = false
        rw [wiresOf_snoc_last_eq (L.get i).gates ⟨.or, []⟩ (bitsOf t z) (bitsOf_len t z)]
        simp [GateOp.eval]
      rw [hlhs, hrhs]
      simp

def signBool (b : Bool) : ℤ := if b then -1 else 1

lemma signBool_xor (a b : Bool) : signBool (Bool.xor a b) = signBool a * signBool b := by
  cases a <;> cases b <;> rfl

lemma agree_eq_sign (b1 b2 b3 : Bool) :
    (if b1 = Bool.xor b2 b3 then (1 : ℤ) else -1) = signBool (Bool.xor b1 b2) * signBool b3 := by
  cases b1 <;> cases b2 <;> cases b3 <;> rfl

lemma eq_f2_sign (a b : F2) :
    (if a = b then (1 : ℤ) else -1) = signBool (decide (a = 1)) * signBool (decide (b = 1)) := by
  fin_cases a <;> fin_cases b <;> decide

lemma signBool_abs_one (b : Bool) : |signBool b| = 1 := by
  cases b <;> simp [signBool]

lemma card_submodule_zmod2 {k : ℕ} (U : Submodule F2 (Fin k → F2)) :
    Fintype.card U = 2 ^ Module.finrank F2 U := by
  let b := Module.finBasis F2 U
  rw [Fintype.card_congr b.equivFun.toEquiv]
  simp [ZMod.card]

def orthoComp {k : ℕ} (U : Submodule F2 (Fin k → F2)) : Submodule F2 (Fin k → F2) :=
  { carrier := {w | ∀ u ∈ U, dotProduct w u = 0},
    zero_mem' := fun u _ => by simp, smul_mem' := fun c {a} ha u hu => by rw [smul_dotProduct, ha u hu, smul_zero], add_mem' := fun {a b} ha hb u hu => by rw [add_dotProduct, ha u hu, hb u hu, add_zero] }

lemma mem_orthoComp {k : ℕ} (U : Submodule F2 (Fin k → F2)) (w : Fin k → F2) :
    w ∈ orthoComp U ↔ ∀ u ∈ U, dotProduct w u = 0 := Iff.rfl

lemma finrank_orthoComp {k : ℕ} (U : Submodule F2 (Fin k → F2)) :
    Module.finrank F2 (orthoComp U) + Module.finrank F2 U = k := by
  let b := Module.finBasis F2 U
  let Φ : (Fin k → F2) →ₗ[F2] (Fin (Module.finrank F2 U) → F2) :=
    { toFun := fun w i => dotProduct w (b i).val
      map_add' := fun x y => by funext i; exact add_dotProduct x y (b i).val
      map_smul' := fun c x => by funext i; simp [smul_dotProduct] }
  have hker : LinearMap.ker Φ = orthoComp U := by
    ext w
    simp only [LinearMap.mem_ker, mem_orthoComp]
    constructor
    · intro hw u hu
      have hrep : (⟨u, hu⟩ : U) = ∑ i, b.repr ⟨u, hu⟩ i • b i := (b.sum_repr ⟨u, hu⟩).symm
      have hu_eq : u = ∑ i, b.repr ⟨u, hu⟩ i • (b i).val := by
        have hval := congrArg Subtype.val hrep
        simp only [Submodule.coe_sum, SetLike.val_smul] at hval
        exact hval
      rw [hu_eq, dotProduct_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [dotProduct_smul, smul_eq_mul]
      have hwi : dotProduct w (b i).val = 0 := congrFun hw i
      rw [hwi, mul_zero]
    · intro hw
      funext i
      exact hw (b i).val (b i).property
  have hsurj : LinearMap.range Φ = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro target
    let f : U →ₗ[F2] F2 :=
      { toFun := fun u => ∑ i, target i * b.repr u i
        map_add' := fun x y => by simp only [map_add, Finsupp.coe_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
        map_smul' := fun c x => by
          simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => by ring }
    obtain ⟨V', hcompl⟩ := Submodule.exists_isCompl U
    let π : (Fin k → F2) →ₗ[F2] U := Submodule.linearProjOfIsCompl U V' hcompl
    let g : (Fin k → F2) →ₗ[F2] F2 := f.comp π
    let w : Fin k → F2 := fun j => g (Pi.single j 1)
    refine ⟨w, ?_⟩
    funext i
    have hgx : ∀ x : Fin k → F2, dotProduct w x = g x := by
      intro x
      conv_rhs => rw [vec_eq_sum_single x]
      rw [map_sum]
      simp only [dotProduct, map_smul, smul_eq_mul, w]
      refine Finset.sum_congr rfl fun j _ => by ring
    change dotProduct w (b i).val = target i
    rw [hgx (b i).val]
    have hpi : π (b i).val = b i := Submodule.linearProjOfIsCompl_apply_left hcompl (b i)
    simp only [g, LinearMap.comp_apply, hpi, f, LinearMap.coe_mk, AddHom.coe_mk, Module.Basis.repr_self]
    simp [Finsupp.single_apply]
  have hrk := LinearMap.finrank_range_add_finrank_ker Φ
  rw [hsurj, hker, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at hrk
  omega

lemma sum_sign_dot_submodule {k : ℕ} (U : Submodule F2 (Fin k → F2)) (w : Fin k → F2) :
    (∑ u : U, signBool (decide (dotProduct w u.val = 1))) =
      if w ∈ orthoComp U then (2 : ℤ) ^ Module.finrank F2 U else 0 := by
  by_cases hw : w ∈ orthoComp U
  · simp only [hw, ↓reduceIte]
    have hterm : ∀ u : U, signBool (decide (dotProduct w u.val = 1)) = 1 := by
      intro u
      rw [hw u.val u.property]
      rfl
    simp only [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      card_submodule_zmod2, Nat.cast_pow, Nat.cast_ofNat]
  · simp only [hw, ↓reduceIte]
    have hex : ∃ u0 ∈ U, dotProduct w u0 = 1 := by
      by_contra hnot
      apply hw
      intro u hu
      rcases zmod2_cases (dotProduct w u) with h0 | h1
      · exact h0
      · exact absurd ⟨u, hu, h1⟩ hnot
    rcases hex with ⟨u0, hu0, hdot⟩
    let e : U ≃ U :=
      { toFun := fun u => u + ⟨u0, hu0⟩
        invFun := fun u => u + ⟨u0, hu0⟩
        left_inv := fun u => Subtype.ext (by
          show u.val + u0 + u0 = u.val
          rw [add_assoc, zmod2_vec_add_self, add_zero])
        right_inv := fun u => Subtype.ext (by
          show u.val + u0 + u0 = u.val
          rw [add_assoc, zmod2_vec_add_self, add_zero]) }
    set S := ∑ u : U, signBool (decide (dotProduct w u.val = 1))
    have hS : S = -S := by
      calc S = ∑ u : U, signBool (decide (dotProduct w (e u).val = 1)) :=
            (Equiv.sum_comp e (fun u : U => signBool (decide (dotProduct w u.val = 1)))).symm
        _ = ∑ u : U, -signBool (decide (dotProduct w u.val = 1)) := by
            refine Finset.sum_congr rfl fun u _ => ?_
            show signBool (decide (dotProduct w (u.val + u0) = 1)) = _
            rw [dotProduct_add, hdot, zmod2_add_decide]
            cases decide (dotProduct w u.val = 1) <;> rfl
        _ = -S := by rw [Finset.sum_neg_distrib]
    omega

lemma sum_sign_dot_univ {k : ℕ} (w : Fin k → F2) (hw : w ≠ 0) :
    (∑ x : Fin k → F2, signBool (decide (dotProduct w x = 1))) = 0 := by
  have hex : ∃ j : Fin k, w j = 1 := by
    by_contra hnot; push Not at hnot
    apply hw; funext j
    rcases zmod2_cases (w j) with h0 | h1
    · exact h0
    · exact absurd h1 (hnot j)
  rcases hex with ⟨j, hj⟩
  let u0 : Fin k → F2 := Pi.single j 1
  have hdot : dotProduct w u0 = 1 := by
    simp [u0, dotProduct_single, hj]
  let e : (Fin k → F2) ≃ (Fin k → F2) :=
    { toFun := fun x => x + u0
      invFun := fun x => x + u0
      left_inv := fun x => by dsimp only; rw [add_assoc, zmod2_vec_add_self, add_zero]
      right_inv := fun x => by dsimp only; rw [add_assoc, zmod2_vec_add_self, add_zero] }
  set S := ∑ x : Fin k → F2, signBool (decide (dotProduct w x = 1))
  have hS : S = -S := by
    calc S = ∑ x : Fin k → F2, signBool (decide (dotProduct w (e x) = 1)) :=
          (Equiv.sum_comp e (fun x => signBool (decide (dotProduct w x = 1)))).symm
      _ = ∑ x : Fin k → F2, -signBool (decide (dotProduct w x = 1)) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          show signBool (decide (dotProduct w (x + u0) = 1)) = _
          rw [dotProduct_add, hdot, zmod2_add_decide]
          cases decide (dotProduct w x = 1) <;> rfl
      _ = -S := by rw [Finset.sum_neg_distrib]
  omega

lemma cost_zero_affine {k : ℕ} (gs : List Gate) (hleg : legalGates k gs) (hcost : costGates gs = 0) :
    ∀ w < k + gs.length, ∃ (lin : Fin k → F2) (c : F2), ∀ y : Fin k → F2,
      (wiresOf gs (bitsOf k y)).getD w false = decide (dotProduct lin y + c = 1) := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro w hw
    simp only [List.length_nil, Nat.add_zero] at hw
    refine ⟨Pi.single ⟨w, hw⟩ 1, 0, fun y => ?_⟩
    change (bitsOf k y).getD (⟨w, hw⟩ : Fin k).val false = _
    rw [bitsOf_getD, single_dotProduct, one_mul, add_zero]
  | append_singleton gs g ih =>
    have hpre := legalGates_prefix hleg
    have hcost_app : costGates gs + costGates [g] = 0 := by
      rw [← costGates_append]; exact hcost
    have hcost_gs : costGates gs = 0 := by omega
    have hnot_nl : ¬ ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) := by
      intro hnl
      have h1 : costGates (gs ++ [g]) = costGates gs + 1 := costGates_snoc_one gs g hnl
      omega
    have hih := ih hpre.1 hcost_gs
    intro w hw
    simp only [List.length_append, List.length_singleton] at hw
    by_cases hlt : w < k + gs.length
    · obtain ⟨lin, c, hlin⟩ := hih w hlt
      refine ⟨lin, c, fun y => ?_⟩
      rw [wiresOf_append_getD_lt gs [g] (bitsOf k y) (by rw [bitsOf_len]; exact hlt)]
      exact hlin y
    · have hweq : w = k + gs.length := by omega
      subst hweq
      have hback := hpre.2.1
      have hshape := hpre.2.2
      have eval_snoc : ∀ y : Fin k → F2,
          (wiresOf (gs ++ [g]) (bitsOf k y)).getD (k + gs.length) false =
            g.op.eval (g.inputs.map fun i => (wiresOf gs (bitsOf k y)).getD i false) :=
        fun y => wiresOf_snoc_last_eq gs g (bitsOf k y) (bitsOf_len k y)
      rcases hshape.2 with hop | hop | hop | ⟨hop, hlen1⟩
      · rcases hg : g.inputs with _ | ⟨w0, rest⟩
        · refine ⟨0, 1, fun y => ?_⟩
          rw [eval_snoc y, hop, hg]; simp [GateOp.eval]
        · rcases rest with _ | ⟨w1, rest2⟩
          · obtain ⟨lin, c, hlin⟩ := hih w0 (hback w0 (by rw [hg]; simp))
            refine ⟨lin, c, fun y => ?_⟩
            rw [eval_snoc y, hop, hg]
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
            exact hlin y
          · rcases rest2 with _ | ⟨_, _⟩
            · exfalso; exact hnot_nl ⟨Or.inl hop, by rw [hg]; rfl⟩
            · exfalso; have := hshape.1; rw [hg] at this; simp at this
      · rcases hg : g.inputs with _ | ⟨w0, rest⟩
        · refine ⟨0, 0, fun y => ?_⟩
          rw [eval_snoc y, hop, hg]; simp [GateOp.eval]
        · rcases rest with _ | ⟨w1, rest2⟩
          · obtain ⟨lin, c, hlin⟩ := hih w0 (hback w0 (by rw [hg]; simp))
            refine ⟨lin, c, fun y => ?_⟩
            rw [eval_snoc y, hop, hg]
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
            exact hlin y
          · rcases rest2 with _ | ⟨_, _⟩
            · exfalso; exact hnot_nl ⟨Or.inr hop, by rw [hg]; rfl⟩
            · exfalso; have := hshape.1; rw [hg] at this; simp at this
      · rcases hg : g.inputs with _ | ⟨w0, rest⟩
        · refine ⟨0, 1, fun y => ?_⟩
          rw [eval_snoc y, hop, hg]; simp [GateOp.eval]
        · rcases rest with _ | ⟨w1, rest2⟩
          · obtain ⟨lin, c, hlin⟩ := hih w0 (hback w0 (by rw [hg]; simp))
            refine ⟨lin, c + 1, fun y => ?_⟩
            rw [eval_snoc y, hop, hg]
            simp only [List.map_cons, List.map_nil, hlin y, GateOp.eval]
            rcases zmod2_cases (dotProduct lin y + c) with h | h <;> rw [← add_assoc, h] <;> decide
          · rcases rest2 with _ | ⟨_, _⟩
            · obtain ⟨lin0, c0, hlin0⟩ := hih w0 (hback w0 (by rw [hg]; simp))
              obtain ⟨lin1, c1, hlin1⟩ := hih w1 (hback w1 (by rw [hg]; simp))
              refine ⟨lin0 + lin1, c0 + c1 + 1, fun y => ?_⟩
              rw [eval_snoc y, hop, hg]
              simp only [List.map_cons, List.map_nil, hlin0 y, hlin1 y, GateOp.eval, add_dotProduct]
              have hrw : dotProduct lin0 y + dotProduct lin1 y + (c0 + c1 + 1) =
                  (dotProduct lin0 y + c0) + (dotProduct lin1 y + c1) + 1 := by ring
              rw [hrw]
              rcases zmod2_cases (dotProduct lin0 y + c0) with h0 | h0 <;>
                rcases zmod2_cases (dotProduct lin1 y + c1) with h1 | h1 <;>
                rw [h0, h1] <;> decide
            · exfalso; have := hshape.1; rw [hg] at this; simp at this
      · rcases hg : g.inputs with _ | ⟨w0, rest⟩
        · simp [hg] at hlen1
        · rcases rest with _ | ⟨_, _⟩
          · obtain ⟨lin, c, hlin⟩ := hih w0 (hback w0 (by rw [hg]; simp))
            refine ⟨lin, c + 1, fun y => ?_⟩
            rw [eval_snoc y, hop, hg]
            simp only [List.map_cons, List.map_nil, hlin y, GateOp.eval, List.headD_cons]
            rcases zmod2_cases (dotProduct lin y + c) with h | h <;> rw [← add_assoc, h] <;> decide
          · simp [hg] at hlen1

def isQuad {s : ℕ} (q : (Fin s → F2) → F2) : Prop :=
  ∃ (b : F2) (a : Fin s → F2) (M : Fin s → Fin s → F2), ∀ v,
    q v = b + dotProduct a v + ∑ i, ∑ j, M i j * v i * v j

lemma isQuad_const {s : ℕ} (b : F2) : isQuad (s := s) (fun _ => b) :=
  ⟨b, 0, fun _ _ => 0, fun _ => by simp⟩

lemma isQuad_affine {s : ℕ} (a : Fin s → F2) (b : F2) :
    isQuad (s := s) (fun v => dotProduct a v + b) :=
  ⟨b, a, fun _ _ => 0, fun v => by simp [add_comm]⟩

lemma isQuad_add {s : ℕ} {q1 q2 : (Fin s → F2) → F2} (h1 : isQuad q1) (h2 : isQuad q2) :
    isQuad (fun v => q1 v + q2 v) := by
  rcases h1 with ⟨b1, a1, M1, h1⟩
  rcases h2 with ⟨b2, a2, M2, h2⟩
  refine ⟨b1 + b2, a1 + a2, fun i j => M1 i j + M2 i j, fun v => ?_⟩
  dsimp only
  rw [h1 v, h2 v, add_dotProduct]
  have hsum : (∑ i : Fin s, ∑ j : Fin s, (M1 i j + M2 i j) * v i * v j) =
      (∑ i : Fin s, ∑ j : Fin s, M1 i j * v i * v j) +
      (∑ i : Fin s, ∑ j : Fin s, M2 i j * v i * v j) := by
    simp only [add_mul, Finset.sum_add_distrib]
  rw [hsum]; ring

lemma isQuad_mul_affine {s : ℕ} (u1 u2 : Fin s → F2) (c1 c2 : F2) :
    isQuad (fun v => (dotProduct u1 v + c1) * (dotProduct u2 v + c2)) := by
  refine ⟨c1 * c2, c2 • u1 + c1 • u2, fun i j => u1 i * u2 j, fun v => ?_⟩
  dsimp only
  rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  have hprod : dotProduct u1 v * dotProduct u2 v =
      ∑ i : Fin s, ∑ j : Fin s, u1 i * u2 j * v i * v j := by
    simp only [dotProduct, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [← hprod]; ring

lemma isQuad_finset_sum {s : ℕ} {ι : Type*} (S : Finset ι) (f : ι → (Fin s → F2) → F2)
    (hf : ∀ i ∈ S, isQuad (f i)) :
    isQuad (fun v => ∑ i ∈ S, f i v) := by
  induction S using Finset.induction_on with
  | empty => simpa using isQuad_const (s := s) 0
  | @insert a S ha ih =>
    have hfa := hf a (Finset.mem_insert_self a S)
    have hfs := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have heq : (fun v => ∑ i ∈ insert a S, f i v) = (fun v => f a v + ∑ i ∈ S, f i v) := by
      funext v; exact Finset.sum_insert ha
    rw [heq]
    exact isQuad_add hfa hfs

lemma linear_comp_affine {k s : ℕ} (B : (Fin s → F2) →ₗ[F2] (Fin k → F2))
    (a : Fin k → F2) (u : Fin k → F2) (c : F2) :
    ∃ (u' : Fin s → F2) (c' : F2), ∀ v : Fin s → F2,
      dotProduct u (a + B v) + c = dotProduct u' v + c' := by
  refine ⟨fun i => dotProduct u (B (Pi.single i 1)), dotProduct u a + c, fun v => ?_⟩
  rw [dotProduct_add]
  have hBv : dotProduct u (B v) = dotProduct (fun i => dotProduct u (B (Pi.single i 1))) v := by
    conv_lhs => rw [vec_eq_sum_single v, map_sum, dotProduct_sum]
    simp only [dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [hBv]; ring

lemma forward_decomp_bounds (k s : ℕ) (g : (Fin k → F2) → F2) (C : Circuit)
    (hleg : legalGates (2 * k) C.gates) (hcost : costGates C.gates ≤ s) :
    ∃ (N : ℕ) (r : Fin N → ℕ) (W : Fin N → Submodule F2 (Fin k → F2))
      (a : Fin N → (Fin k → F2)) (D : Fin N → Circuit) (tap : Fin N → Fin k → ℕ),
      let pos := fun (i : Fin N) (y : Fin k → F2) (j : Fin k) =>
        if ((D i).wires (bitsOf k y)).getD (tap i j) false then (1 : F2) else 0
      let Bval := fun i : Fin N =>
        (∑ y : Fin k → F2, if y - a i ∈ W i then
          signBool (Bool.xor ((D i).eval (bitsOf k y)) (decide (dotProduct (pos i y) y = 1))) *
            signBool (decide (g y = 1))
        else 0).natAbs
      0 < N ∧
      (∀ i, Module.finrank F2 (W i) = r i ∧ r i ≤ k ∧ legalGates k (D i).gates ∧
        costGates (D i).gates + r i ≤ s ∧ (D i).output < k + (D i).size ∧
        ∀ j, tap i j < k + (D i).size) ∧
      (∑ i : Fin N, 2 ^ (k - r i)) = 2 ^ k ∧
      (∀ i, Bval i ≤ 2 ^ (r i)) ∧
      (∑ x : Fin k → F2, ∑ y : Fin k → F2,
        if C.eval (bitsOf k x ++ bitsOf k y) = decide (dotProduct x y + g y = 1)
        then (1 : ℤ) else -1).natAbs ≤ ∑ i : Fin N, 2 ^ (k - r i) * Bval i := by
  have hleg' : legalGates (k + k) C.gates := by rwa [show k + k = 2 * k by omega]
  rcases decomp_835 k k C hleg' with ⟨N, r, U, a, D, tap, hNpos, hmeta, hpart, heval⟩
  let pos := fun (i : Fin N) (y : Fin k → F2) (j : Fin k) =>
    if ((D i).wires (bitsOf k y)).getD (tap i j) false then (1 : F2) else 0
  let W : Fin N → Submodule F2 (Fin k → F2) := fun i => orthoComp (U i)
  have hW_dim : ∀ i, Module.finrank F2 (W i) = r i := by
    intro i
    dsimp only [W]
    have h1 := finrank_orthoComp (U i)
    have h2 := (hmeta i).1
    omega
  have hU_dim : ∀ i, Module.finrank F2 (U i) = k - r i := by
    intro i; have := (hmeta i).1; omega
  let hpart_equiv : ∀ y : Fin k → F2, (Σ i : Fin N, U i) ≃ (Fin k → F2) := fun y =>
    let idxOf : (Fin k → F2) → Fin N := fun x => (hpart y x).choose
    have hidx_mem : ∀ x, x - pos (idxOf x) y ∈ U (idxOf x) := fun x => (hpart y x).choose_spec.1
    have hidx_uniq : ∀ x i, x - pos i y ∈ U i → i = idxOf x := fun x i hi => (hpart y x).choose_spec.2 i hi
    { toFun := fun p => pos p.1 y + p.2.val
      invFun := fun x => ⟨idxOf x, ⟨x - pos (idxOf x) y, hidx_mem x⟩⟩
      left_inv := fun ⟨i, ⟨u, hu⟩⟩ => by
        have hmem : pos i y + u - pos i y ∈ U i := by simpa using hu
        have hi : idxOf (pos i y + u) = i := (hidx_uniq (pos i y + u) i hmem).symm
        dsimp only
        generalize hidx_mem (pos i y + u) = hjm
        revert hjm
        generalize idxOf (pos i y + u) = j at hi ⊢
        subst hi
        intro _
        congr 1
        apply Subtype.ext
        simp
      right_inv := fun x => by
        show pos (idxOf x) y + (x - pos (idxOf x) y) = x
        abel }
  have hsum_pow : (∑ i : Fin N, 2 ^ (k - r i)) = 2 ^ k := by
    have hcard_sig : Fintype.card (Σ i : Fin N, U i) = ∑ i : Fin N, 2 ^ (k - r i) := by
      rw [Fintype.card_sigma]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [card_submodule_zmod2, hU_dim i]
    have hcard_V : Fintype.card (Fin k → F2) = 2 ^ k := by simp [ZMod.card]
    rw [← hcard_sig, ← hcard_V]
    exact Fintype.card_congr (hpart_equiv 0)
  have hprof : ∀ y : Fin k → F2,
      (∑ x : Fin k → F2, signBool (Bool.xor (C.eval (bitsOf k x ++ bitsOf k y)) (decide (dotProduct x y = 1)))) =
      ∑ i : Fin N, (2 : ℤ) ^ (k - r i) *
        (if y - a i ∈ W i then
          signBool (Bool.xor ((D i).eval (bitsOf k y)) (decide (dotProduct (pos i y) y = 1)))
        else 0) := by
    intro y
    rw [← Equiv.sum_comp (hpart_equiv y), Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hterm : ∀ u : U i,
        signBool (Bool.xor (C.eval (bitsOf k (pos i y + u.val) ++ bitsOf k y))
          (decide (dotProduct (pos i y + u.val) y = 1))) =
        signBool (Bool.xor ((D i).eval (bitsOf k y)) (decide (dotProduct (pos i y) y = 1))) *
          signBool (decide (dotProduct (y - a i) u.val = 1)) := by
      intro u
      rw [heval i y u.val u.property, add_dotProduct, zmod2_add_decide, signBool_xor, signBool_xor, signBool_xor]
      have hdot_eq : dotProduct (y - a i) u.val = dotProduct (a i) u.val + dotProduct u.val y := by
        rw [zmod2_vec_sub_eq_add, add_dotProduct, dotProduct_comm u.val y]; ring
      rw [hdot_eq, zmod2_add_decide, signBool_xor, signBool_xor]
      ring
    have heq_fn : ∀ u : U i, hpart_equiv y ⟨i, u⟩ = pos i y + u.val := fun _ => by dsimp [hpart_equiv]
    simp_rw [heq_fn, hterm, ← Finset.mul_sum, sum_sign_dot_submodule (U i) (y - a i), hU_dim i]
    dsimp only [W]
    split_ifs <;> ring
  refine ⟨N, r, W, a, D, tap, hNpos, ?_, hsum_pow, ?_, ?_⟩
  · intro i
    have hm := hmeta i
    exact ⟨hW_dim i, by omega, hm.2.1, by omega, hm.2.2.2.1, hm.2.2.2.2⟩
  · intro i
    dsimp only
    have hle : (∑ y : Fin k → F2, if y - a i ∈ W i then
        signBool (Bool.xor ((D i).eval (bitsOf k y)) (decide (dotProduct (pos i y) y = 1))) *
          signBool (decide (g y = 1))
      else 0).natAbs ≤
        ∑ y : Fin k → F2, (if y - a i ∈ W i then (1 : ℕ) else 0) := by
      have htri := Finset.abs_sum_le_sum_abs
        (fun y : Fin k → F2 => if y - a i ∈ W i then
          signBool (Bool.xor ((D i).eval (bitsOf k y)) (decide (dotProduct (pos i y) y = 1))) *
            signBool (decide (g y = 1))
        else 0) Finset.univ
      have habs : ∀ y : Fin k → F2,
          |(if y - a i ∈ W i then
            signBool (Bool.xor ((D i).eval (bitsOf k y)) (decide (dotProduct (pos i y) y = 1))) *
              signBool (decide (g y = 1))
          else 0)| = if y - a i ∈ W i then (1 : ℤ) else 0 := by
        intro y
        split_ifs
        · rw [abs_mul, signBool_abs_one, signBool_abs_one, mul_one]
        · simp
      simp_rw [habs] at htri
      have hnat : ((∑ y : Fin k → F2, if y - a i ∈ W i then
          signBool (Bool.xor ((D i).eval (bitsOf k y)) (decide (dotProduct (pos i y) y = 1))) *
            signBool (decide (g y = 1))
        else 0).natAbs : ℤ) ≤ ∑ y : Fin k → F2, if y - a i ∈ W i then (1 : ℤ) else 0 := by
        simpa [Int.natCast_natAbs] using htri
      exact_mod_cast hnat
    have hcard_coset : (∑ y : Fin k → F2, if y - a i ∈ W i then (1 : ℕ) else 0) = 2 ^ (r i) := by
      rw [← Finset.card_filter]
      let eW : W i ≃ {y : Fin k → F2 // y - a i ∈ W i} :=
        { toFun := fun w => ⟨a i + w.val, by simpa using w.property⟩
          invFun := fun y => ⟨y.val - a i, y.property⟩
          left_inv := fun w => Subtype.ext (by show a i + w.val - a i = w.val; abel)
          right_inv := fun y => Subtype.ext (by show a i + (y.val - a i) = y.val; abel) }
      have hc : (Finset.univ.filter (fun y : Fin k → F2 => y - a i ∈ W i)).card =
          Fintype.card {y : Fin k → F2 // y - a i ∈ W i} := (Fintype.card_subtype _).symm
      rw [hc, ← Fintype.card_congr eW, card_submodule_zmod2, hW_dim i]
    exact le_trans hle (le_of_eq hcard_coset)
  · dsimp only
    have hsum_eq : (∑ x : Fin k → F2, ∑ y : Fin k → F2,
        if C.eval (bitsOf k x ++ bitsOf k y) = decide (dotProduct x y + g y = 1)
        then (1 : ℤ) else -1) =
        ∑ i : Fin N, (2 : ℤ) ^ (k - r i) *
          (∑ y : Fin k → F2, if y - a i ∈ W i then
            signBool (Bool.xor ((D i).eval (bitsOf k y)) (decide (dotProduct (pos i y) y = 1))) *
              signBool (decide (g y = 1))
          else 0) := by
      rw [Finset.sum_comm]
      have hy : ∀ y : Fin k → F2,
          (∑ x : Fin k → F2, if C.eval (bitsOf k x ++ bitsOf k y) = decide (dotProduct x y + g y = 1)
            then (1 : ℤ) else -1) =
          (∑ i : Fin N, (2 : ℤ) ^ (k - r i) *
            (if y - a i ∈ W i then
              signBool (Bool.xor ((D i).eval (bitsOf k y)) (decide (dotProduct (pos i y) y = 1))) *
                signBool (decide (g y = 1))
            else 0)) := by
        intro y
        have hstep : ∀ x : Fin k → F2,
            (if C.eval (bitsOf k x ++ bitsOf k y) = decide (dotProduct x y + g y = 1) then (1 : ℤ) else -1) =
            signBool (Bool.xor (C.eval (bitsOf k x ++ bitsOf k y)) (decide (dotProduct x y = 1))) *
              signBool (decide (g y = 1)) := by
          intro x
          rw [zmod2_add_decide, agree_eq_sign]
        simp_rw [hstep, ← Finset.sum_mul, hprof y, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs <;> ring
      simp_rw [hy]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
    rw [hsum_eq]
    have htri := Finset.abs_sum_le_sum_abs
      (fun i : Fin N => (2 : ℤ) ^ (k - r i) *
        (∑ y : Fin k → F2, if y - a i ∈ W i then
          signBool (Bool.xor ((D i).eval (bitsOf k y)) (decide (dotProduct (pos i y) y = 1))) *
            signBool (decide (g y = 1))
        else 0)) Finset.univ
    have habs_term : ∀ i : Fin N,
        |(2 : ℤ) ^ (k - r i) *
          (∑ y : Fin k → F2, if y - a i ∈ W i then
            signBool (Bool.xor ((D i).eval (bitsOf k y)) (decide (dotProduct (pos i y) y = 1))) *
              signBool (decide (g y = 1))
          else 0)| =
        ((2 ^ (k - r i) * (∑ y : Fin k → F2, if y - a i ∈ W i then
          signBool (Bool.xor ((D i).eval (bitsOf k y)) (decide (dotProduct (pos i y) y = 1))) *
            signBool (decide (g y = 1))
        else 0).natAbs : ℕ) : ℤ) := by
      intro i
      rw [abs_mul, abs_of_nonneg (by positivity), ← Int.natCast_natAbs]
      push_cast; rfl
    simp_rw [habs_term] at htri
    have hnat : ((∑ i : Fin N, (2 : ℤ) ^ (k - r i) *
        (∑ y : Fin k → F2, if y - a i ∈ W i then
          signBool (Bool.xor ((D i).eval (bitsOf k y)) (decide (dotProduct (pos i y) y = 1))) *
            signBool (decide (g y = 1))
        else 0)).natAbs : ℤ) ≤
        ((∑ i : Fin N, 2 ^ (k - r i) * (∑ y : Fin k → F2, if y - a i ∈ W i then
          signBool (Bool.xor ((D i).eval (bitsOf k y)) (decide (dotProduct (pos i y) y = 1))) *
            signBool (decide (g y = 1))
        else 0).natAbs : ℕ) : ℤ) := by
      simpa [Int.natCast_natAbs, Nat.cast_sum] using htri
    exact Int.ofNat_le.mp hnat

end Circuit



namespace Circuit

open PEqualNP.CircuitLowerBounds

def h5OPb2f (b : Bool) : F2 := if b then 1 else 0

lemma h5OPb2f_not (b : Bool) : h5OPb2f (!b) = h5OPb2f b + 1 := by
  cases b <;> rfl

lemma h5OPb2f_and (a b : Bool) : h5OPb2f (a && b) = h5OPb2f a * h5OPb2f b := by
  cases a <;> cases b <;> rfl

lemma h5OPb2f_or (a b : Bool) :
    h5OPb2f (a || b) = h5OPb2f a + h5OPb2f b + h5OPb2f a * h5OPb2f b := by
  cases a <;> cases b <;> rfl

lemma h5OPb2f_mod2_one (a : Bool) :
    h5OPb2f (GateOp.eval (.mod 2) [a]) = h5OPb2f a + 1 := by
  cases a <;> rfl

lemma h5OPb2f_mod2_two (a b : Bool) :
    h5OPb2f (GateOp.eval (.mod 2) [a, b]) = h5OPb2f a + h5OPb2f b + 1 := by
  cases a <;> cases b <;> rfl

def h5OPAff {k : ℕ} (f : (Fin k → F2) → F2) : Prop :=
  ∃ (a : Fin k → F2) (c : F2), ∀ y, f y = c + dotProduct a y

lemma h5OPAff_const {k : ℕ} (c : F2) : h5OPAff (k := k) (fun _ => c) := by
  refine ⟨0, c, fun y => ?_⟩
  simp

lemma h5OPAff_add {k : ℕ} {f1 f2 : (Fin k → F2) → F2}
    (h1 : h5OPAff f1) (h2 : h5OPAff f2) : h5OPAff (fun y => f1 y + f2 y) := by
  rcases h1 with ⟨a1, c1, hf1⟩
  rcases h2 with ⟨a2, c2, hf2⟩
  refine ⟨a1 + a2, c1 + c2, fun y => ?_⟩
  dsimp only
  rw [hf1 y, hf2 y, add_dotProduct]
  ring

lemma h5OPAff_add_const {k : ℕ} {f : (Fin k → F2) → F2}
    (h : h5OPAff f) (d : F2) : h5OPAff (fun y => f y + d) :=
  h5OPAff_add h (h5OPAff_const d)

lemma h5OP_cost_zero_affine {k : ℕ} (gs : List Gate)
    (hleg : legalGates k gs) (hcost : costGates gs = 0) :
    ∀ w < k + gs.length, h5OPAff (fun y => h5OPb2f ((wiresOf gs (bitsOf k y)).getD w false)) := by
  intro w hw
  obtain ⟨a, c, h⟩ := cost_zero_affine gs hleg hcost w hw
  refine ⟨a, c, fun y => ?_⟩
  dsimp only
  rw [h y]
  simpa [h5OPb2f, add_comm] using zmod2_decide_bool (dotProduct a y + c)

lemma h5OP_cost_le_one_decomp (k : ℕ) (ds : List Gate)
    (hleg : legalGates k ds)
    (hcost : costGates ds ≤ 1) :
    ∃ (u v : (Fin k → F2) → F2),
      h5OPAff u ∧ h5OPAff v ∧
      ∀ w < k + ds.length,
        ∃ (fw : (Fin k → F2) → F2) (cw : F2),
          h5OPAff fw ∧
          ∀ (y : Fin k → F2),
            h5OPb2f ((wiresOf ds (bitsOf k y)).getD w false) =
              fw y + cw * (u y * v y) := by
  induction ds using List.reverseRecOn with
  | nil =>
    refine ⟨fun _ => 0, fun _ => 0, h5OPAff_const 0, h5OPAff_const 0, ?_⟩
    intro w hw
    refine ⟨fun y => h5OPb2f ((wiresOf [] (bitsOf k y)).getD w false), 0,
      h5OP_cost_zero_affine [] hleg rfl w hw, fun y => by simp⟩
  | append_singleton ds h ih =>
    have hpre := legalGates_prefix hleg
    have hleg_ds := hpre.1
    have hg_rb := hpre.2.1
    have hleg_h := hpre.2.2
    rw [costGates_append] at hcost
    by_cases hch : costGates [h] = 0
    · rcases ih hleg_ds (by omega) with ⟨u, v, hu, hv, hprev⟩
      refine ⟨u, v, hu, hv, ?_⟩
      intro w hw
      rw [List.length_append, List.length_singleton] at hw
      by_cases hlt : w < k + ds.length
      · rcases hprev w hlt with ⟨fw, cw, hfw, heq⟩
        refine ⟨fw, cw, hfw, fun y => ?_⟩
        rw [wiresOf_append_getD_lt ds [h] _ (by rw [bitsOf_len]; exact hlt)]
        exact heq y
      · have hweq : w = k + ds.length := by omega
        subst hweq
        rcases hleg_h with ⟨hlen_le, hop⟩
        match hins : h.inputs with
        | [] =>
          refine ⟨fun _ => h5OPb2f (h.op.eval []), 0, h5OPAff_const _, fun y => ?_⟩
          have hidx : k + ds.length = (bitsOf k y).length + ds.length := by
            rw [bitsOf_len]
          rw [hidx, wiresOf_snoc_last, hins]
          simp
        | [w1] =>
          have hw1 : w1 < k + ds.length := hg_rb w1 (by simp [hins])
          rcases hprev w1 hw1 with ⟨f1, c1, hf1, heq1⟩
          rcases hop with hand | hor | hmod | ⟨hnot, _⟩
          · refine ⟨f1, c1, hf1, fun y => ?_⟩
            have hidx : k + ds.length = (bitsOf k y).length + ds.length := by
              rw [bitsOf_len]
            rw [hidx, wiresOf_snoc_last, hins, hand]
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
            exact heq1 y
          · refine ⟨f1, c1, hf1, fun y => ?_⟩
            have hidx : k + ds.length = (bitsOf k y).length + ds.length := by
              rw [bitsOf_len]
            rw [hidx, wiresOf_snoc_last, hins, hor]
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
            exact heq1 y
          · refine ⟨fun y => f1 y + 1, c1, h5OPAff_add_const hf1 1, fun y => ?_⟩
            have hidx : k + ds.length = (bitsOf k y).length + ds.length := by
              rw [bitsOf_len]
            rw [hidx, wiresOf_snoc_last, hins, hmod]
            simp only [List.map_cons, List.map_nil]
            rw [h5OPb2f_mod2_one, heq1 y]
            ring
          · refine ⟨fun y => f1 y + 1, c1, h5OPAff_add_const hf1 1, fun y => ?_⟩
            have hidx : k + ds.length = (bitsOf k y).length + ds.length := by
              rw [bitsOf_len]
            rw [hidx, wiresOf_snoc_last, hins, hnot]
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons, h5OPb2f_not, heq1 y]
            ring
        | [w1, w2] =>
          have hw1 : w1 < k + ds.length := hg_rb w1 (by simp [hins])
          have hw2 : w2 < k + ds.length := hg_rb w2 (by simp [hins])
          rcases hop with hand | hor | hmod | ⟨_, hnotlen⟩
          · have h1 : costGates [h] = 1 := by
              simp [costGates, hand, hins]
            omega
          · have h1 : costGates [h] = 1 := by
              simp [costGates, hor, hins]
            omega
          · rcases hprev w1 hw1 with ⟨f1, c1, hf1, heq1⟩
            rcases hprev w2 hw2 with ⟨f2, c2, hf2, heq2⟩
            refine ⟨fun y => f1 y + f2 y + 1, c1 + c2,
              h5OPAff_add_const (h5OPAff_add hf1 hf2) 1, fun y => ?_⟩
            have hidx : k + ds.length = (bitsOf k y).length + ds.length := by
              rw [bitsOf_len]
            rw [hidx, wiresOf_snoc_last, hins, hmod]
            simp only [List.map_cons, List.map_nil]
            rw [h5OPb2f_mod2_two, heq1 y, heq2 y]
            ring
          · simp [hins] at hnotlen
        | _ :: _ :: _ :: _ =>
          simp [hins] at hlen_le
    · have hcost_ds : costGates ds = 0 := by
        have hch1 : costGates [h] ≤ 1 := by
          simp only [costGates, List.countP_cons, List.countP_nil]
          split_ifs <;> omega
        omega
      have haff_ds := h5OP_cost_zero_affine ds hleg_ds hcost_ds
      rcases hleg_h with ⟨hlen_le, hop⟩
      have hbin : (h.op = .and ∨ h.op = .or) ∧ h.inputs.length = 2 := by
        by_contra hnb
        have : costGates [h] = 0 := by simp [costGates, hnb]
        exact hch this
      match hins : h.inputs with
      | [w1, w2] =>
        have hw1 : w1 < k + ds.length := hg_rb w1 (by simp [hins])
        have hw2 : w2 < k + ds.length := hg_rb w2 (by simp [hins])
        let u : (Fin k → F2) → F2 :=
          fun y => h5OPb2f ((wiresOf ds (bitsOf k y)).getD w1 false)
        let v : (Fin k → F2) → F2 :=
          fun y => h5OPb2f ((wiresOf ds (bitsOf k y)).getD w2 false)
        refine ⟨u, v, haff_ds w1 hw1, haff_ds w2 hw2, ?_⟩
        intro w hw
        rw [List.length_append, List.length_singleton] at hw
        by_cases hlt : w < k + ds.length
        · refine ⟨fun y => h5OPb2f ((wiresOf ds (bitsOf k y)).getD w false), 0,
            haff_ds w hlt, fun y => ?_⟩
          rw [wiresOf_append_getD_lt ds [h] _ (by rw [bitsOf_len]; exact hlt)]
          simp
        · have hweq : w = k + ds.length := by omega
          subst hweq
          rcases hbin.1 with hand | hor
          · refine ⟨fun _ => 0, 1, h5OPAff_const 0, fun y => ?_⟩
            have hidx : k + ds.length = (bitsOf k y).length + ds.length := by
              rw [bitsOf_len]
            rw [hidx, wiresOf_snoc_last, hins, hand]
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true, h5OPb2f_and]
            simp [u, v]
          · refine ⟨fun y => u y + v y, 1, h5OPAff_add (haff_ds w1 hw1) (haff_ds w2 hw2), fun y => ?_⟩
            have hidx : k + ds.length = (bitsOf k y).length + ds.length := by
              rw [bitsOf_len]
            rw [hidx, wiresOf_snoc_last, hins, hor]
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false, h5OPb2f_or]
            simp [u, v]
      | [] => simp [hins] at hbin
      | [_] => simp [hins] at hbin
      | _ :: _ :: _ :: _ => simp [hins] at hbin

lemma h5OP_cost_le_one_coeffs (k : ℕ) (ds : List Gate)
    (hleg : legalGates k ds) (hcost : costGates ds ≤ 1) :
    ∃ (u0 v0 : F2) (ul vl : Fin k → F2),
      ∀ w < k + ds.length, ∃ (d0 c : F2) (dl : Fin k → F2),
        ∀ y, h5OPb2f ((wiresOf ds (bitsOf k y)).getD w false) =
          d0 + dotProduct dl y + c * (u0 + dotProduct ul y) * (v0 + dotProduct vl y) := by
  obtain ⟨u, v, ⟨ul, u0, hu⟩, ⟨vl, v0, hv⟩, hw⟩ :=
    h5OP_cost_le_one_decomp k ds hleg hcost
  refine ⟨u0, v0, ul, vl, fun w hwb => ?_⟩
  obtain ⟨f, c, ⟨dl, d0, hf⟩, heq⟩ := hw w hwb
  refine ⟨d0, c, dl, fun y => ?_⟩
  rw [heq y, hf y, hu y, hv y]
  ring

lemma h5OP_shared_product_phase {I : Type*} [Fintype I]
    (d0 c0 u v : F2) (dl p0 c y : I → F2) (P : I → I → F2) :
    (d0 + dotProduct dl y + c0 * u * v) +
        dotProduct (fun i => p0 i + dotProduct (P i) y + c i * u * v) y =
      d0 + dotProduct (dl + p0) y +
        (∑ i, ∑ j, P i j * y i * y j) +
        (c0 + dotProduct c y) * u * v := by
  have hP : dotProduct (fun i => dotProduct (P i) y) y =
      ∑ i, ∑ j, P i j * y i * y j := by
    simp only [dotProduct, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hc : dotProduct (fun i => c i * u * v) y = dotProduct c y * u * v := by
    simp only [dotProduct, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hp : dotProduct (fun i => p0 i + dotProduct (P i) y + c i * u * v) y =
      dotProduct p0 y + dotProduct (fun i => dotProduct (P i) y) y +
        dotProduct (fun i => c i * u * v) y := by
    simp only [dotProduct, add_mul, Finset.sum_add_distrib]
  rw [hp, hP, hc, add_dotProduct]
  ring

lemma h5OP_circuit_phase (k : ℕ) (D : Circuit) (tap : Fin k → ℕ)
    (hleg : legalGates k D.gates) (hcost : costGates D.gates ≤ 1)
    (hout : D.output < k + D.size) (htap : ∀ j, tap j < k + D.size) :
    ∃ (q : (Fin k → F2) → F2), isQuad q ∧
      ∃ (c0 u0 v0 : F2) (c ul vl : Fin k → F2), ∀ y,
        h5OPb2f (D.eval (bitsOf k y)) +
            dotProduct (fun j => h5OPb2f ((D.wires (bitsOf k y)).getD (tap j) false)) y =
          q y + (c0 + dotProduct c y) * (u0 + dotProduct ul y) * (v0 + dotProduct vl y) := by
  classical
  obtain ⟨u0, v0, ul, vl, hw⟩ := h5OP_cost_le_one_coeffs k D.gates hleg hcost
  obtain ⟨d0, c0, dl, hdo⟩ := hw D.output hout
  have htp : ∀ j : Fin k, ∃ (p0 cj : F2) (P : Fin k → F2), ∀ y,
      h5OPb2f ((wiresOf D.gates (bitsOf k y)).getD (tap j) false) =
        p0 + dotProduct P y + cj * (u0 + dotProduct ul y) * (v0 + dotProduct vl y) :=
    fun j => hw (tap j) (htap j)
  choose p0 c P hP using htp
  refine ⟨fun y => d0 + dotProduct (dl + p0) y + ∑ i, ∑ j, P i j * y i * y j,
    ⟨d0, dl + p0, P, fun _ => rfl⟩, c0, u0, v0, c, ul, vl, fun y => ?_⟩
  change h5OPb2f ((wiresOf D.gates (bitsOf k y)).getD D.output false) +
      dotProduct (fun j => h5OPb2f ((wiresOf D.gates (bitsOf k y)).getD (tap j) false)) y = _
  rw [hdo y, show (fun j => h5OPb2f ((wiresOf D.gates (bitsOf k y)).getD (tap j) false)) =
      (fun j => p0 j + dotProduct (P j) y + c j * (u0 + dotProduct ul y) * (v0 + dotProduct vl y))
      from funext (fun j => hP j y)]
  exact h5OP_shared_product_phase d0 c0 (u0 + dotProduct ul y) (v0 + dotProduct vl y)
    dl p0 c y P

lemma h5OP_circuit_phase_zero (k : ℕ) (D : Circuit) (tap : Fin k → ℕ)
    (hleg : legalGates k D.gates) (hcost : costGates D.gates = 0)
    (hout : D.output < k + D.size) (htap : ∀ j, tap j < k + D.size) :
    isQuad (fun y => h5OPb2f (D.eval (bitsOf k y)) +
      dotProduct (fun j => h5OPb2f ((D.wires (bitsOf k y)).getD (tap j) false)) y) := by
  classical
  obtain ⟨dl, d0, hdo⟩ := h5OP_cost_zero_affine D.gates hleg hcost D.output hout
  dsimp only at hdo
  have htp : ∀ j : Fin k, ∃ (P : Fin k → F2) (p0 : F2), ∀ y,
      h5OPb2f ((wiresOf D.gates (bitsOf k y)).getD (tap j) false) =
        p0 + dotProduct P y := fun j => h5OP_cost_zero_affine D.gates hleg hcost (tap j) (htap j)
  choose P p0 hP using htp
  refine ⟨d0, dl + p0, P, fun y => ?_⟩
  change h5OPb2f ((wiresOf D.gates (bitsOf k y)).getD D.output false) +
      dotProduct (fun j => h5OPb2f ((wiresOf D.gates (bitsOf k y)).getD (tap j) false)) y = _
  rw [hdo y, show (fun j => h5OPb2f ((wiresOf D.gates (bitsOf k y)).getD (tap j) false)) =
      (fun j => p0 j + dotProduct (P j) y) from funext (fun j => hP j y)]
  simpa only [zero_mul, mul_zero, add_zero, zero_dotProduct] using
    h5OP_shared_product_phase d0 0 0 0 dl p0 (0 : Fin k → F2) y P

end Circuit


section h5_part_8

end h5_part_8



namespace Circuit

open PEqualNP.CircuitLowerBounds
open Classical

noncomputable def h5BranchPhase {n : ℕ} (D : Circuit) (tap : Fin n → ℕ)
    (y : Fin n → F2) : F2 :=
  h5OPb2f (D.eval (bitsOf n y)) +
    dotProduct (fun j => h5OPb2f ((D.wires (bitsOf n y)).getD (tap j) false)) y

noncomputable def h5FlatBias {n t : ℕ} (g : (Fin n → F2) → F2)
    (B : (Fin t → F2) →ₗ[F2] (Fin n → F2)) (a : Fin n → F2)
    (q : (Fin t → F2) → F2) : ℕ :=
  (∑ v : Fin t → F2, if g (a + B v) = q v then (1 : ℤ) else -1).natAbs

noncomputable def h5BranchBias {n : ℕ} (g : (Fin n → F2) → F2)
    (W : Submodule F2 (Fin n → F2)) (a : Fin n → F2)
    (D : Circuit) (tap : Fin n → ℕ) : ℕ :=
  (∑ y : Fin n → F2, if y - a ∈ W then
    signBool (Bool.xor (D.eval (bitsOf n y))
      (decide (dotProduct (fun j => h5OPb2f ((D.wires (bitsOf n y)).getD (tap j) false)) y = 1))) *
        signBool (decide (g y = 1)) else 0).natAbs

def h5IsQuadPlusTriple {n : ℕ} (f : (Fin n → F2) → F2) : Prop :=
  ∃ (q : (Fin n → F2) → F2), isQuad q ∧
    ∃ (c0 u0 v0 : F2) (c u v : Fin n → F2), ∀ y,
      f y = q y + (c0 + dotProduct c y) * (u0 + dotProduct u y) *
        (v0 + dotProduct v y)

lemma h5_isQuad_comp_affine {n t : ℕ}
    (B : (Fin t → F2) →ₗ[F2] (Fin n → F2)) (a : Fin n → F2)
    (q : (Fin n → F2) → F2) (hq : isQuad q) :
    isQuad (fun v => q (a + B v)) := by
  obtain ⟨c, l, M, hq⟩ := hq
  obtain ⟨l', c', hl⟩ := linear_comp_affine B a l c
  have hlin : isQuad (fun v => c + dotProduct l (a + B v)) := by
    have hf : (fun v => c + dotProduct l (a + B v)) =
        (fun v => dotProduct l' v + c') := by
      funext v
      simpa only [add_comm] using hl v
    rw [hf]
    exact isQuad_affine l' c'
  have hmat : isQuad (fun v => ∑ i : Fin n, ∑ j : Fin n,
      M i j * (a + B v) i * (a + B v) j) := by
    apply isQuad_finset_sum Finset.univ
    intro i _
    apply isQuad_finset_sum Finset.univ
    intro j _
    obtain ⟨u1, b1, hu1⟩ := linear_comp_affine B a (Pi.single i (M i j)) 0
    obtain ⟨u2, b2, hu2⟩ := linear_comp_affine B a (Pi.single j 1) 0
    have hp : (fun v => M i j * (a + B v) i * (a + B v) j) =
        (fun v => (dotProduct u1 v + b1) * (dotProduct u2 v + b2)) := by
      funext v
      have h1 : M i j * (a + B v) i = dotProduct u1 v + b1 := by
        simpa only [single_dotProduct, add_zero] using hu1 v
      have h2 : (a + B v) j = dotProduct u2 v + b2 := by
        simpa only [single_dotProduct, one_mul, add_zero] using hu2 v
      rw [h1, h2]
    rw [hp]
    exact isQuad_mul_affine u1 u2 b1 b2
  have hfn : (fun v => q (a + B v)) = (fun v =>
      (c + dotProduct l (a + B v)) +
        ∑ i : Fin n, ∑ j : Fin n, M i j * (a + B v) i * (a + B v) j) :=
    funext (fun v => hq (a + B v))
  rw [hfn]
  exact isQuad_add hlin hmat

lemma h5_triple_comp_affine {n t : ℕ}
    (B : (Fin t → F2) →ₗ[F2] (Fin n → F2)) (a : Fin n → F2)
    (f : (Fin n → F2) → F2) (hf : h5IsQuadPlusTriple f) :
    h5IsQuadPlusTriple (fun v => f (a + B v)) := by
  obtain ⟨q, hq, c0, u0, v0, c, u, v, hf⟩ := hf
  obtain ⟨c', c0', hc⟩ := linear_comp_affine B a c c0
  obtain ⟨u', u0', hu⟩ := linear_comp_affine B a u u0
  obtain ⟨v', v0', hv⟩ := linear_comp_affine B a v v0
  refine ⟨fun z => q (a + B z), h5_isQuad_comp_affine B a q hq,
    c0', u0', v0', c', u', v', fun z => ?_⟩
  dsimp only
  rw [hf]
  have hc' : c0 + dotProduct c (a + B z) = c0' + dotProduct c' z := by
    simpa only [add_comm] using hc z
  have hu' : u0 + dotProduct u (a + B z) = u0' + dotProduct u' z := by
    simpa only [add_comm] using hu z
  have hv' : v0 + dotProduct v (a + B z) = v0' + dotProduct v' z := by
    simpa only [add_comm] using hv z
  rw [hc', hu', hv']

lemma h5_coset_param {n t : ℕ} (W : Submodule F2 (Fin n → F2))
    (ht : Module.finrank F2 W = t) (a : Fin n → F2) :
    ∃ (B : (Fin t → F2) →ₗ[F2] (Fin n → F2)), Function.Injective B ∧
      ∀ f : (Fin n → F2) → ℤ,
        (∑ y : Fin n → F2, if y - a ∈ W then f y else 0) =
          ∑ v : Fin t → F2, f (a + B v) := by
  let e : (Fin t → F2) ≃ₗ[F2] W :=
    LinearEquiv.ofFinrankEq (Fin t → F2) W (by rw [Module.finrank_fin_fun, ht])
  let B : (Fin t → F2) →ₗ[F2] (Fin n → F2) := W.subtype.comp e.toLinearMap
  have hB : Function.Injective B := Subtype.val_injective.comp e.injective
  refine ⟨B, hB, fun f => ?_⟩
  rw [← Finset.sum_filter]
  let fi : (Fin t → F2) → (Fin n → F2) := fun v => a + B v
  have hbij : Finset.univ.image fi = Finset.univ.filter (fun y => y - a ∈ W) := by
    ext y
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter, fi]
    constructor
    · rintro ⟨v, rfl⟩
      have heq : a + B v - a = (e v).val := by
        show a + (e v).val - a = (e v).val
        abel
      rw [heq]
      exact (e v).property
    · intro hy
      refine ⟨e.symm ⟨y - a, hy⟩, ?_⟩
      show a + (e (e.symm ⟨y - a, hy⟩)).val = y
      rw [LinearEquiv.apply_symm_apply]
      exact add_sub_cancel a y
  rw [← hbij, Finset.sum_image (fun v1 _ v2 _ h => hB (add_left_cancel h))]

lemma h5_branch_sign {n : ℕ} (g : (Fin n → F2) → F2)
    (D : Circuit) (tap : Fin n → ℕ) (y : Fin n → F2) :
    signBool (Bool.xor (D.eval (bitsOf n y))
      (decide (dotProduct (fun j => h5OPb2f ((D.wires (bitsOf n y)).getD (tap j) false)) y = 1))) *
        signBool (decide (g y = 1)) =
      if g y = h5BranchPhase D tap y then (1 : ℤ) else -1 := by
  rw [eq_f2_sign, h5BranchPhase, zmod2_add_decide]
  have hb : decide (h5OPb2f (D.eval (bitsOf n y)) = 1) = D.eval (bitsOf n y) :=
    zmod2_bool_decide _
  rw [hb, mul_comm]

lemma h5_branch_flat {n t : ℕ} (g : (Fin n → F2) → F2)
    (W : Submodule F2 (Fin n → F2)) (ht : Module.finrank F2 W = t)
    (a : Fin n → F2) (D : Circuit) (tap : Fin n → ℕ) :
    ∃ (B : (Fin t → F2) →ₗ[F2] (Fin n → F2)), Function.Injective B ∧
      h5BranchBias g W a D tap =
        h5FlatBias g B a (fun v => h5BranchPhase D tap (a + B v)) := by
  obtain ⟨B, hB, hsum⟩ := h5_coset_param W ht a
  refine ⟨B, hB, ?_⟩
  unfold h5BranchBias h5FlatBias
  simp_rw [h5_branch_sign]
  congr 1
  exact hsum _

lemma h5_circuit_upper_from_flats (n m b plane line : ℕ)
    (g : (Fin n → F2) → F2) (hplane : 2 ^ m ≤ plane)
    (hquad : ∀ (B : (Fin b → F2) →ₗ[F2] (Fin n → F2)) (a : Fin n → F2)
      (q : (Fin b → F2) → F2), Function.Injective B → isQuad q →
        2 ^ (m + 2) * h5FlatBias g B a q ≤ 2 ^ b * plane)
    (htriple : ∀ t, t + 1 = b →
      ∀ (B : (Fin t → F2) →ₗ[F2] (Fin n → F2)) (a : Fin n → F2)
        (q : (Fin t → F2) → F2), Function.Injective B → h5IsQuadPlusTriple q →
          2 ^ (m + 2) * h5FlatBias g B a q ≤ 2 ^ b * line)
    (C : Circuit) (hleg : legalGates (2 * n) C.gates) (hcost : costGates C.gates ≤ b) :
    2 ^ (m + 2) * (∑ x : Fin n → F2, ∑ y : Fin n → F2,
      if C.eval (bitsOf n x ++ bitsOf n y) = decide (dotProduct x y + g y = 1)
        then (1 : ℤ) else -1).natAbs ≤ 2 ^ (n + b) * max plane line := by
  obtain ⟨N, r, W, a, D, tap, _, hmeta, hweight, hbias, hraw⟩ :=
    forward_decomp_bounds n b g C hleg hcost
  let bias : Fin N → ℕ := fun i => h5BranchBias g (W i) (a i) (D i) (tap i)
  apply PEqualNP.Outside.L_meta_32057_aux.h5_circuit_upper_reduction
    n m b plane line _ r (fun i => 2 ^ (n - r i)) bias
  · exact hraw
  · exact hweight
  · intro i
    have h := (hmeta i).2.2.2.1
    omega
  · exact hbias
  · exact hplane
  · intro i hri
    have hm := hmeta i
    have hzero : costGates (D i).gates = 0 := by omega
    have hdim : Module.finrank F2 (W i) = b := by rw [hm.1, hri]
    obtain ⟨B, hB, heq⟩ := h5_branch_flat g (W i) hdim (a i) (D i) (tap i)
    change 2 ^ (m + 2) * h5BranchBias g (W i) (a i) (D i) (tap i) ≤ _
    rw [heq]
    apply hquad B (a i) _ hB
    apply h5_isQuad_comp_affine
    exact h5OP_circuit_phase_zero n (D i) (tap i) hm.2.2.1 hzero
      hm.2.2.2.2.1 hm.2.2.2.2.2
  · intro i hri
    have hm := hmeta i
    have hone : costGates (D i).gates ≤ 1 := by omega
    obtain ⟨B, hB, heq⟩ := h5_branch_flat g (W i) hm.1 (a i) (D i) (tap i)
    change 2 ^ (m + 2) * h5BranchBias g (W i) (a i) (D i) (tap i) ≤ _
    rw [heq]
    apply htriple (r i) hri B (a i) _ hB
    apply h5_triple_comp_affine
    exact h5OP_circuit_phase n (D i) (tap i) hm.2.2.1 hone
      hm.2.2.2.2.1 hm.2.2.2.2.2

end Circuit


namespace Circuit

open PEqualNP.CircuitLowerBounds

lemma appendConst_spec (n : ℕ) (gs : List Gate) (b : F2) (hgs : legalGates n gs) :
    let g := if b = 1 then Gate.mk .and [] else Gate.mk .or []
    let gs' := gs ++ [g]
    legalGates n gs' ∧
    costGates gs' = costGates gs ∧
    n + gs.length < n + gs'.length ∧
    ∀ x : List Bool, x.length = n →
      (wiresOf gs' x).getD (n + gs.length) false = decide (b = 1) := by
  intro g gs'
  have hshape : g.inputs.length ≤ 2 ∧
      (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1)) := by
    dsimp only [g]; split_ifs
    · exact ⟨by simp, Or.inl rfl⟩
    · exact ⟨by simp, Or.inr (Or.inl rfl)⟩
  have hback : ∀ i ∈ g.inputs, i < n + gs.length := by
    dsimp only [g]; split_ifs <;> simp
  refine ⟨legalGates_snoc hgs hback hshape, ?_, by simp [gs'], ?_⟩
  · apply costGates_snoc_zero gs g
    dsimp only [g]; split_ifs <;> simp
  · intro x hx
    rw [wiresOf_snoc_last_eq gs g x hx]
    rcases zmod2_cases b with rfl | rfl <;> simp [g, GateOp.eval]

def appendAffineLoop (n : ℕ) (c : Fin n → F2) : (m : ℕ) → m ≤ n → List Gate → ℕ → List Gate × ℕ
  | 0, _, gs, acc => (gs, acc)
  | m + 1, hm, gs, acc =>
    let res := appendAffineLoop n c m (by omega) gs acc
    let gs1 := res.1
    let acc1 := res.2
    if c ⟨m, hm⟩ = 1 then
      (gs1 ++ [⟨.mod 2, [acc1, m]⟩, ⟨.not, [n + gs1.length]⟩], n + gs1.length + 1)
    else (gs1, acc1)

lemma appendAffineLoop_spec (n : ℕ) (c : Fin n → F2) :
    ∀ (m : ℕ) (hm : m ≤ n) (gs : List Gate) (acc : ℕ),
      legalGates n gs → acc < n + gs.length →
      let res := appendAffineLoop n c m hm gs acc
      ∃ ext : List Gate,
        res.1 = gs ++ ext ∧
        legalGates n res.1 ∧
        costGates res.1 = costGates gs ∧
        res.2 < n + res.1.length ∧
        ∀ u : Fin n → F2,
          (wiresOf res.1 (bitsOf n u)).getD res.2 false =
            Bool.xor ((wiresOf gs (bitsOf n u)).getD acc false)
              (decide ((∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < m), c j * u j) = 1)) := by
  intro m
  induction m with
  | zero =>
    intro hm gs acc hleg hacc
    refine ⟨[], by simp [appendAffineLoop], hleg, rfl, hacc, fun u => ?_⟩
    have hemp : Finset.univ.filter (fun j : Fin n => j.val < 0) = ∅ := by ext j; simp
    simp [appendAffineLoop, hemp]
  | succ m ih =>
    intro hm gs acc hleg hacc
    rcases ih (by omega) gs acc hleg hacc with ⟨ext1, h1eq, h1leg, h1cost, h1lt, h1sem⟩
    set gs1 := (appendAffineLoop n c m (by omega) gs acc).1
    set acc1 := (appendAffineLoop n c m (by omega) gs acc).2
    have hsplit : (Finset.univ.filter (fun j : Fin n => j.val < m + 1)) =
        insert ⟨m, hm⟩ (Finset.univ.filter (fun j : Fin n => j.val < m)) := by
      ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
      omega
    have hnotmem : (⟨m, hm⟩ : Fin n) ∉ Finset.univ.filter (fun j : Fin n => j.val < m) := by simp
    by_cases hcm : c ⟨m, hm⟩ = 1
    · have hstep := addXor_step n gs1 acc1 m h1leg h1lt (by omega)
      refine ⟨ext1 ++ [⟨.mod 2, [acc1, m]⟩, ⟨.not, [n + gs1.length]⟩], ?_, ?_, ?_, ?_, ?_⟩
      · simp [appendAffineLoop, hcm, gs1, acc1, h1eq, List.append_assoc]
      · simpa [appendAffineLoop, hcm, gs1, acc1] using hstep.1
      · simpa [appendAffineLoop, hcm, gs1, acc1, h1cost] using hstep.2.1
      · simp only [appendAffineLoop, hcm, ↓reduceIte, List.length_append, List.length_cons, List.length_nil]
        omega
      · intro u
        simp only [appendAffineLoop, hcm, ↓reduceIte]
        change (wiresOf (gs1 ++ [⟨.mod 2, [acc1, m]⟩, ⟨.not, [n + gs1.length]⟩]) (bitsOf n u)).getD (n + gs1.length + 1) false = _
        rw [hstep.2.2.2 (bitsOf n u) (bitsOf_len n u), h1sem u]
        have hm_wire : (wiresOf gs1 (bitsOf n u)).getD m false = decide (u ⟨m, hm⟩ = 1) := by
          rw [wiresOf_getD_lt gs1 (bitsOf n u) (by rw [bitsOf_len]; exact hm)]
          exact bitsOf_getD n u ⟨m, hm⟩
        rw [hm_wire, hsplit, Finset.sum_insert hnotmem, hcm, one_mul, zmod2_add_decide]
        cases (wiresOf gs (bitsOf n u)).getD acc false <;>
          cases decide (u ⟨m, hm⟩ = 1) <;>
          cases decide ((∑ x ∈ Finset.univ.filter (fun j : Fin n => j.val < m), c x * u x) = 1) <;> decide
    · have hcm0 : c ⟨m, hm⟩ = 0 := by
        rcases zmod2_cases (c ⟨m, hm⟩) with h0 | h1
        · exact h0
        · exact absurd h1 hcm
      refine ⟨ext1, ?_, ?_, ?_, ?_, ?_⟩
      · simp [appendAffineLoop, hcm, gs1, h1eq]
      · simpa [appendAffineLoop, hcm, gs1] using h1leg
      · simpa [appendAffineLoop, hcm, gs1] using h1cost
      · simpa [appendAffineLoop, hcm, gs1, acc1] using h1lt
      · intro u
        simp only [appendAffineLoop, hcm, ↓reduceIte]
        rw [h1sem u, hsplit, Finset.sum_insert hnotmem, hcm0, zero_mul, zero_add]

def appendAffine (n : ℕ) (gs : List Gate) (c : Fin n → F2) (b : F2) : List Gate × ℕ :=
  let g0 := if b = 1 then Gate.mk .and [] else Gate.mk .or []
  appendAffineLoop n c n (le_refl n) (gs ++ [g0]) (n + gs.length)

lemma appendAffine_spec (n : ℕ) (gs : List Gate) (c : Fin n → F2) (b : F2) (hgs : legalGates n gs) :
    let res := appendAffine n gs c b
    ∃ ext : List Gate,
      res.1 = gs ++ ext ∧
      legalGates n res.1 ∧
      costGates res.1 = costGates gs ∧
      res.2 < n + res.1.length ∧
      ∀ u : Fin n → F2,
        (wiresOf res.1 (bitsOf n u)).getD res.2 false = decide (dotProduct c u + b = 1) := by
  have hc := appendConst_spec n gs b hgs
  let g0 := if b = 1 then Gate.mk .and [] else Gate.mk .or []
  rcases appendAffineLoop_spec n c n (le_refl n) (gs ++ [g0]) (n + gs.length) hc.1 hc.2.2.1 with
    ⟨ext1, h1eq, h1leg, h1cost, h1lt, h1sem⟩
  refine ⟨[g0] ++ ext1, ?_, h1leg, ?_, h1lt, ?_⟩
  · simpa [appendAffine, g0, List.append_assoc] using h1eq
  · dsimp only [appendAffine]
    rw [h1cost, hc.2.1]
  · intro u
    change (wiresOf (appendAffineLoop n c n (le_refl n) (gs ++ [g0]) (n + gs.length)).1 (bitsOf n u)).getD
        (appendAffineLoop n c n (le_refl n) (gs ++ [g0]) (n + gs.length)).2 false = _
    rw [h1sem u, hc.2.2.2 (bitsOf n u) (bitsOf_len n u)]
    have huniv : Finset.univ.filter (fun j : Fin n => j.val < n) = Finset.univ := by
      ext j; simp [j.isLt]
    rw [huniv]
    change Bool.xor (decide (b = 1)) (decide (dotProduct c u = 1)) = _
    rw [zmod2_add_decide, Bool.xor_comm]

def appendSumProdsLoop (n s : ℕ) (cA cB : Fin s → Fin n → F2) (bA bB : Fin s → F2) :
    (m : ℕ) → m ≤ s → List Gate → ℕ → List Gate × ℕ
  | 0, _, gs, acc => (gs, acc)
  | m + 1, hm, gs, acc =>
    let res1 := appendSumProdsLoop n s cA cB bA bB m (by omega) gs acc
    let gs1 := res1.1
    let acc1 := res1.2
    let resA := appendAffine n gs1 (cA ⟨m, hm⟩) (bA ⟨m, hm⟩)
    let gs2 := resA.1
    let wA := resA.2
    let resB := appendAffine n gs2 (cB ⟨m, hm⟩) (bB ⟨m, hm⟩)
    let gs3 := resB.1
    let wB := resB.2
    let gs4 := gs3 ++ [⟨.and, [wA, wB]⟩]
    let wP := n + gs3.length
    (gs4 ++ [⟨.mod 2, [acc1, wP]⟩, ⟨.not, [n + gs4.length]⟩], n + gs4.length + 1)

lemma appendSumProdsLoop_spec (n s : ℕ) (cA cB : Fin s → Fin n → F2) (bA bB : Fin s → F2) :
    ∀ (m : ℕ) (hm : m ≤ s) (gs : List Gate) (acc : ℕ),
      legalGates n gs → acc < n + gs.length →
      let res := appendSumProdsLoop n s cA cB bA bB m hm gs acc
      ∃ ext : List Gate,
        res.1 = gs ++ ext ∧
        legalGates n res.1 ∧
        costGates res.1 = costGates gs + m ∧
        res.2 < n + res.1.length ∧
        ∀ u : Fin n → F2,
          (wiresOf res.1 (bitsOf n u)).getD res.2 false =
            Bool.xor ((wiresOf gs (bitsOf n u)).getD acc false)
              (decide ((∑ i ∈ Finset.univ.filter (fun i : Fin s => i.val < m),
                (dotProduct (cA i) u + bA i) * (dotProduct (cB i) u + bB i)) = 1)) := by
  intro m
  induction m with
  | zero =>
    intro hm gs acc hleg hacc
    refine ⟨[], by simp [appendSumProdsLoop], hleg, by simp [appendSumProdsLoop], hacc, fun u => ?_⟩
    have hemp : Finset.univ.filter (fun i : Fin s => i.val < 0) = ∅ := by ext i; simp
    simp [appendSumProdsLoop, hemp]
  | succ m ih =>
    intro hm gs acc hleg hacc
    rcases ih (by omega) gs acc hleg hacc with ⟨ext1, h1eq, h1leg, h1cost, h1lt, h1sem⟩
    set res1 := appendSumProdsLoop n s cA cB bA bB m (by omega) gs acc
    set gs1 := res1.1
    set acc1 := res1.2
    rcases appendAffine_spec n gs1 (cA ⟨m, hm⟩) (bA ⟨m, hm⟩) h1leg with ⟨extA, hAeq, hAleg, hAcost, hAlt, hAsem⟩
    set resA := appendAffine n gs1 (cA ⟨m, hm⟩) (bA ⟨m, hm⟩)
    set gs2 := resA.1
    set wA := resA.2
    rcases appendAffine_spec n gs2 (cB ⟨m, hm⟩) (bB ⟨m, hm⟩) hAleg with ⟨extB, hBeq, hBleg, hBcost, hBlt, hBsem⟩
    set resB := appendAffine n gs2 (cB ⟨m, hm⟩) (bB ⟨m, hm⟩)
    set gs3 := resB.1
    set wB := resB.2
    have hwA_lt3 : wA < n + gs3.length := by rw [hBeq, List.length_append]; omega
    set gs4 := gs3 ++ [⟨.and, [wA, wB]⟩]
    set wP := n + gs3.length
    have h4leg : legalGates n gs4 :=
      legalGates_snoc hBleg (fun i hi => by simp at hi; rcases hi with rfl | rfl; exact hwA_lt3; exact hBlt)
        ⟨by simp, Or.inl rfl⟩
    have h4cost : costGates gs4 = costGates gs3 + 1 :=
      costGates_snoc_one gs3 ⟨.and, [wA, wB]⟩ ⟨Or.inl rfl, rfl⟩
    have hacc1_lt4 : acc1 < n + gs4.length := by
      simp only [gs4, hBeq, hAeq, List.length_append, List.length_singleton]; omega
    have hwP_lt4 : wP < n + gs4.length := by simp [gs4, wP]
    have hstep := addXor_step n gs4 acc1 wP h4leg hacc1_lt4 hwP_lt4
    refine ⟨ext1 ++ extA ++ extB ++ [⟨.and, [wA, wB]⟩, ⟨.mod 2, [acc1, wP]⟩, ⟨.not, [n + gs4.length]⟩],
      ?_, ?_, ?_, ?_, ?_⟩
    · simp only [appendSumProdsLoop]
      change gs4 ++ [⟨.mod 2, [acc1, wP]⟩, ⟨.not, [n + gs4.length]⟩] = _
      simp only [gs4, hBeq, hAeq, h1eq, List.append_assoc, List.cons_append, List.nil_append]
    · exact hstep.1
    · change costGates (gs4 ++ [⟨.mod 2, [acc1, wP]⟩, ⟨.not, [n + gs4.length]⟩]) = _
      rw [hstep.2.1, h4cost, hBcost, hAcost, h1cost]; omega
    · change n + gs4.length + 1 < n + (gs4 ++ ([⟨.mod 2, [acc1, wP]⟩, ⟨.not, [n + gs4.length]⟩] : List Gate)).length
      simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · intro u
      change (wiresOf (gs4 ++ [⟨.mod 2, [acc1, wP]⟩, ⟨.not, [n + gs4.length]⟩]) (bitsOf n u)).getD (n + gs4.length + 1) false = _
      rw [hstep.2.2.2 (bitsOf n u) (bitsOf_len n u)]
      have hacc1_eq : (wiresOf gs4 (bitsOf n u)).getD acc1 false = (wiresOf gs1 (bitsOf n u)).getD acc1 false := by
        have hgs4_eq : gs4 = gs1 ++ (extA ++ extB ++ [⟨.and, [wA, wB]⟩]) := by
          simp only [gs4, hBeq, hAeq, List.append_assoc]
        rw [hgs4_eq, wiresOf_append_getD_lt gs1 _ (bitsOf n u) (by rw [bitsOf_len]; exact h1lt)]
      have hwP_eq : (wiresOf gs4 (bitsOf n u)).getD wP false =
          decide ((dotProduct (cA ⟨m, hm⟩) u + bA ⟨m, hm⟩) * (dotProduct (cB ⟨m, hm⟩) u + bB ⟨m, hm⟩) = 1) := by
        change (wiresOf (gs3 ++ [⟨.and, [wA, wB]⟩]) (bitsOf n u)).getD (n + gs3.length) false = _
        rw [wiresOf_snoc_last_eq gs3 ⟨.and, [wA, wB]⟩ (bitsOf n u) (bitsOf_len n u)]
        simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
        have hwA_val : (wiresOf gs3 (bitsOf n u)).getD wA false = decide (dotProduct (cA ⟨m, hm⟩) u + bA ⟨m, hm⟩ = 1) := by
          rw [hBeq, wiresOf_append_getD_lt gs2 extB (bitsOf n u) (by rw [bitsOf_len]; exact hAlt)]
          exact hAsem u
        rw [hwA_val, hBsem u, zmod2_mul_decide]
      rw [hacc1_eq, h1sem u, hwP_eq]
      have hsplit : (Finset.univ.filter (fun i : Fin s => i.val < m + 1)) =
          insert ⟨m, hm⟩ (Finset.univ.filter (fun i : Fin s => i.val < m)) := by
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
        omega
      have hnotmem : (⟨m, hm⟩ : Fin s) ∉ Finset.univ.filter (fun i : Fin s => i.val < m) := by simp
      rw [hsplit, Finset.sum_insert hnotmem, zmod2_add_decide]
      cases (wiresOf gs (bitsOf n u)).getD acc false <;>
        cases decide ((dotProduct (cA ⟨m, hm⟩) u + bA ⟨m, hm⟩) * (dotProduct (cB ⟨m, hm⟩) u + bB ⟨m, hm⟩) = 1) <;>
        cases decide ((∑ x ∈ Finset.univ.filter (fun i : Fin s => i.val < m),
          (dotProduct (cA x) u + bA x) * (dotProduct (cB x) u + bB x)) = 1) <;> decide

lemma build_sum_prods_circuit (n s : ℕ) (c0 : Fin n → F2) (b0 : F2)
    (cA cB : Fin s → Fin n → F2) (bA bB : Fin s → F2) :
    ∃ C : Circuit, legalGates n C.gates ∧ costGates C.gates = s ∧
      ∀ u : Fin n → F2, C.eval (bitsOf n u) =
        decide ((dotProduct c0 u + b0) +
          ∑ i : Fin s, (dotProduct (cA i) u + bA i) * (dotProduct (cB i) u + bB i) = 1) := by
  have hnil : legalGates n [] := ⟨fun j hj => by simp at hj, fun h hh => by simp at hh⟩
  rcases appendAffine_spec n [] c0 b0 hnil with ⟨_, _, h0leg, h0cost, h0lt, h0sem⟩
  set res0 := appendAffine n [] c0 b0
  rcases appendSumProdsLoop_spec n s cA cB bA bB s (le_refl s) res0.1 res0.2 h0leg h0lt with
    ⟨_, _, hleg, hcost, _, hsem⟩
  set res := appendSumProdsLoop n s cA cB bA bB s (le_refl s) res0.1 res0.2
  refine ⟨⟨res.1, res.2⟩, hleg, ?_, fun u => ?_⟩
  · have hc0 : costGates ([] : List Gate) = 0 := by simp [costGates]
    dsimp only [res, res0] at hcost h0cost ⊢
    omega
  · change (wiresOf res.1 (bitsOf n u)).getD res.2 false = _
    rw [hsem u, h0sem u]
    have huniv : Finset.univ.filter (fun i : Fin s => i.val < s) = Finset.univ := by
      ext i; simp
    rw [huniv, ← zmod2_add_decide]

lemma h5TB_b2f_decide (a : F2) : h5OPb2f (decide (a = 1)) = a :=
  zmod2_decide_bool a

lemma h5TB_b2f_xor (a b : Bool) : h5OPb2f (Bool.xor a b) = h5OPb2f a + h5OPb2f b := by
  cases a <;> cases b <;> rfl

lemma h5TB_append_affine_shared (n : ℕ) (gs : List Gate)
    (c : Fin n → F2) (b d : F2) (wz : ℕ) (z : (Fin n → F2) → F2)
    (hgs : legalGates n gs) (hwz : wz < n + gs.length)
    (hz : ∀ u, h5OPb2f ((wiresOf gs (bitsOf n u)).getD wz false) = z u) :
    ∃ (ext : List Gate) (out : ℕ),
      legalGates n (gs ++ ext) ∧ costGates (gs ++ ext) = costGates gs ∧
      out < n + (gs ++ ext).length ∧
      ∀ u, h5OPb2f ((wiresOf (gs ++ ext) (bitsOf n u)).getD out false) =
        dotProduct c u + b + d * z u := by
  obtain ⟨extA, hAeq, hAleg, hAcost, hAlt, hAsem⟩ := appendAffine_spec n gs c b hgs
  let res := appendAffine n gs c b
  have hleg : legalGates n (gs ++ extA) := by rw [← hAeq]; exact hAleg
  have hcost : costGates (gs ++ extA) = costGates gs := by rw [← hAeq]; exact hAcost
  have hout : res.2 < n + (gs ++ extA).length := by rw [← hAeq]; exact hAlt
  have hsem : ∀ u, h5OPb2f ((wiresOf (gs ++ extA) (bitsOf n u)).getD res.2 false) =
      dotProduct c u + b := by
    intro u
    rw [← hAeq, hAsem u, h5TB_b2f_decide]
  rcases zmod2_cases d with hd | hd
  · refine ⟨extA, res.2, hleg, hcost, hout, fun u => ?_⟩
    rw [hsem u, hd, zero_mul, add_zero]
  · have hwzA : wz < n + (gs ++ extA).length := by rw [List.length_append]; omega
    have hstep := addXor_step n (gs ++ extA) res.2 wz hleg hout hwzA
    let extX : List Gate := [⟨.mod 2, [res.2, wz]⟩, ⟨.not, [n + (gs ++ extA).length]⟩]
    refine ⟨extA ++ extX, n + (gs ++ extA).length + 1, ?_, ?_, ?_, fun u => ?_⟩
    · simpa only [List.append_assoc] using hstep.1
    · simpa only [List.append_assoc, hcost] using hstep.2.1
    · simp only [extX, List.length_append, List.length_cons, List.length_nil]
      omega
    · rw [← List.append_assoc]
      change h5OPb2f ((wiresOf ((gs ++ extA) ++ extX) (bitsOf n u)).getD
        (n + (gs ++ extA).length + 1) false) = _
      rw [hstep.2.2.2 (bitsOf n u) (bitsOf_len n u), h5TB_b2f_xor, hsem u]
      rw [wiresOf_append_getD_lt gs extA (bitsOf n u) (by rw [bitsOf_len]; exact hwz), hz u, hd, one_mul]

lemma h5TB_append_products_shared (n s : ℕ)
    (cA cB : Fin s → Fin n → F2) (bA bB d : Fin s → F2)
    (wz : ℕ) (z : (Fin n → F2) → F2)
    (S : Finset (Fin s)) (gs : List Gate) (acc : ℕ)
    (hgs : legalGates n gs) (hacc : acc < n + gs.length) (hwz : wz < n + gs.length)
    (hz : ∀ u, h5OPb2f ((wiresOf gs (bitsOf n u)).getD wz false) = z u) :
    ∃ (gs' : List Gate) (out : ℕ) (ext : List Gate),
      gs' = gs ++ ext ∧ legalGates n gs' ∧ costGates gs' = costGates gs + S.card ∧
      out < n + gs'.length ∧ ∀ u,
        h5OPb2f ((wiresOf gs' (bitsOf n u)).getD out false) =
          h5OPb2f ((wiresOf gs (bitsOf n u)).getD acc false) +
            ∑ i ∈ S, (dotProduct (cA i) u + bA i) *
              (dotProduct (cB i) u + bB i + d i * z u) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    exact ⟨gs, acc, [], by simp, hgs, by simp, hacc, fun u => by simp⟩
  | @insert i S hi ih =>
    obtain ⟨gs1, acc1, ext1, h1eq, h1leg, h1cost, h1lt, h1sem⟩ := ih
    have hwz1 : wz < n + gs1.length := by rw [h1eq, List.length_append]; omega
    have hz1 : ∀ u, h5OPb2f ((wiresOf gs1 (bitsOf n u)).getD wz false) = z u := by
      intro u
      rw [h1eq, wiresOf_append_getD_lt gs ext1 (bitsOf n u) (by rw [bitsOf_len]; exact hwz), hz u]
    obtain ⟨extA, wA, hAleg, hAcost, hAlt, hAsem⟩ :=
      h5TB_append_affine_shared n gs1 (cA i) (bA i) 0 wz z h1leg hwz1 hz1
    let gs2 := gs1 ++ extA
    simp only [zero_mul, add_zero] at hAsem
    have hwz2 : wz < n + gs2.length := by dsimp only [gs2]; rw [List.length_append]; omega
    have hz2 : ∀ u, h5OPb2f ((wiresOf gs2 (bitsOf n u)).getD wz false) = z u := by
      intro u
      rw [wiresOf_append_getD_lt gs1 extA (bitsOf n u) (by rw [bitsOf_len]; exact hwz1)]
      exact hz1 u
    obtain ⟨extB, wB, hBleg, hBcost, hBlt, hBsem⟩ :=
      h5TB_append_affine_shared n gs2 (cB i) (bB i) (d i) wz z hAleg hwz2 hz2
    let gs3 := gs2 ++ extB
    have hwA2 : wA < n + gs2.length := hAlt
    have hwA3 : wA < n + gs3.length := by dsimp only [gs3]; rw [List.length_append]; omega
    let gs4 := gs3 ++ [Gate.mk .and [wA, wB]]
    let wP := n + gs3.length
    have h4leg : legalGates n gs4 :=
      legalGates_snoc hBleg (fun j hj => by simp at hj; rcases hj with rfl | rfl; exact hwA3; exact hBlt)
        ⟨by simp, Or.inl rfl⟩
    have h4cost : costGates gs4 = costGates gs3 + 1 :=
      costGates_snoc_one gs3 ⟨.and, [wA, wB]⟩ ⟨Or.inl rfl, rfl⟩
    have hacc4 : acc1 < n + gs4.length := by
      simp only [gs4, gs3, gs2, List.length_append, List.length_singleton]
      omega
    have hwP4 : wP < n + gs4.length := by simp [wP, gs4]
    have hstep := addXor_step n gs4 acc1 wP h4leg hacc4 hwP4
    let extX : List Gate := [⟨.mod 2, [acc1, wP]⟩, ⟨.not, [n + gs4.length]⟩]
    let gs5 := gs4 ++ extX
    refine ⟨gs5, n + gs4.length + 1,
      ext1 ++ extA ++ extB ++ [Gate.mk .and [wA, wB]] ++ extX,
      ?_, hstep.1, ?_, ?_, fun u => ?_⟩
    · simp only [gs5, gs4, gs3, gs2, h1eq, List.append_assoc]
    · change costGates (gs4 ++ extX) = _
      rw [hstep.2.1, h4cost, hBcost, hAcost, h1cost, Finset.card_insert_of_notMem hi]
      omega
    · simp only [gs5, extX, List.length_append, List.length_cons, List.length_nil]
      omega
    · change h5OPb2f ((wiresOf (gs4 ++ extX) (bitsOf n u)).getD (n + gs4.length + 1) false) = _
      rw [hstep.2.2.2 (bitsOf n u) (bitsOf_len n u), h5TB_b2f_xor]
      have hacc_eq : (wiresOf gs4 (bitsOf n u)).getD acc1 false =
          (wiresOf gs1 (bitsOf n u)).getD acc1 false := by
        have hgs4 : gs4 = gs1 ++ (extA ++ extB ++ [Gate.mk .and [wA, wB]]) := by
          simp only [gs4, gs3, gs2, List.append_assoc]
        rw [hgs4, wiresOf_append_getD_lt gs1 _ (bitsOf n u) (by rw [bitsOf_len]; exact h1lt)]
      have hprod : h5OPb2f ((wiresOf gs4 (bitsOf n u)).getD wP false) =
          (dotProduct (cA i) u + bA i) * (dotProduct (cB i) u + bB i + d i * z u) := by
        change h5OPb2f ((wiresOf (gs3 ++ [Gate.mk .and [wA, wB]]) (bitsOf n u)).getD
          (n + gs3.length) false) = _
        rw [wiresOf_snoc_last_eq gs3 ⟨.and, [wA, wB]⟩ (bitsOf n u) (bitsOf_len n u)]
        simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
          id_eq, Bool.and_true, h5OPb2f_and]
        have hAval : h5OPb2f ((wiresOf gs3 (bitsOf n u)).getD wA false) = dotProduct (cA i) u + bA i := by
          rw [wiresOf_append_getD_lt gs2 extB (bitsOf n u) (by rw [bitsOf_len]; exact hAlt)]
          exact hAsem u
        rw [hAval, hBsem u]
      rw [hacc_eq, h1sem u, hprod, Finset.sum_insert hi]
      ring

lemma h5TB_build_shared_product (n s : ℕ)
    (c0 cU cV : Fin n → F2) (b0 bU bV d0 : F2)
    (cA cB : Fin s → Fin n → F2) (bA bB d : Fin s → F2) :
    ∃ C : Circuit, legalGates n C.gates ∧ costGates C.gates = s + 1 ∧
      ∀ w : Fin n → F2, C.eval (bitsOf n w) =
        decide ((dotProduct c0 w + b0) +
          d0 * ((dotProduct cU w + bU) * (dotProduct cV w + bV)) +
          ∑ i : Fin s, (dotProduct (cA i) w + bA i) *
            (dotProduct (cB i) w + bB i +
              d i * ((dotProduct cU w + bU) * (dotProduct cV w + bV))) = 1) := by
  classical
  have hnil : legalGates n [] := ⟨fun j hj => by simp at hj, fun g hg => by simp at hg⟩
  obtain ⟨extU, hUeq, hUleg, hUcost, hUlt, hUsem⟩ := appendAffine_spec n [] cU bU hnil
  let gsU := (appendAffine n [] cU bU).1
  let wU := (appendAffine n [] cU bU).2
  obtain ⟨extV, hVeq, hVleg, hVcost, hVlt, hVsem⟩ := appendAffine_spec n gsU cV bV hUleg
  let gsV := (appendAffine n gsU cV bV).1
  let wV := (appendAffine n gsU cV bV).2
  change gsV = gsU ++ extV at hVeq
  have hwU0 : wU < n + gsU.length := hUlt
  have hwU : wU < n + gsV.length := by rw [hVeq, List.length_append]; omega
  let gsZ := gsV ++ [Gate.mk .and [wU, wV]]
  let wz := n + gsV.length
  let z : (Fin n → F2) → F2 := fun w => (dotProduct cU w + bU) * (dotProduct cV w + bV)
  have hZleg : legalGates n gsZ :=
    legalGates_snoc hVleg (fun j hj => by simp at hj; rcases hj with rfl | rfl; exact hwU; exact hVlt)
      ⟨by simp, Or.inl rfl⟩
  have hZcost : costGates gsZ = 1 := by
    rw [costGates_snoc_one gsV ⟨.and, [wU, wV]⟩ ⟨Or.inl rfl, rfl⟩, hVcost, hUcost]
    simp [costGates]
  have hwz : wz < n + gsZ.length := by simp [wz, gsZ]
  have hz : ∀ w, h5OPb2f ((wiresOf gsZ (bitsOf n w)).getD wz false) = z w := by
    intro w
    rw [wiresOf_snoc_last_eq gsV ⟨.and, [wU, wV]⟩ (bitsOf n w) (bitsOf_len n w)]
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
      id_eq, Bool.and_true, h5OPb2f_and]
    have hUw : (wiresOf gsV (bitsOf n w)).getD wU false = decide (dotProduct cU w + bU = 1) := by
      rw [hVeq, wiresOf_append_getD_lt gsU extV (bitsOf n w) (by rw [bitsOf_len]; exact hUlt)]
      exact hUsem w
    rw [hUw, hVsem w, h5TB_b2f_decide, h5TB_b2f_decide]
  obtain ⟨ext0, acc, h0leg, h0cost, h0lt, h0sem⟩ :=
    h5TB_append_affine_shared n gsZ c0 b0 d0 wz z hZleg hwz hz
  let gs0 := gsZ ++ ext0
  have hwz0 : wz < n + gs0.length := by dsimp only [gs0]; rw [List.length_append]; omega
  have hz0 : ∀ w, h5OPb2f ((wiresOf gs0 (bitsOf n w)).getD wz false) = z w := by
    intro w
    rw [wiresOf_append_getD_lt gsZ ext0 (bitsOf n w) (by rw [bitsOf_len]; exact hwz), hz w]
  obtain ⟨gs, out, ext, hgeq, hgleg, hgcost, hglt, hgsem⟩ :=
    h5TB_append_products_shared n s cA cB bA bB d wz z Finset.univ gs0 acc h0leg h0lt hwz0 hz0
  refine ⟨⟨gs, out⟩, hgleg, ?_, fun w => ?_⟩
  · change costGates gs = s + 1
    rw [hgcost, h0cost, hZcost]
    simp [Nat.add_comm]
  · change (wiresOf gs (bitsOf n w)).getD out false = _
    rw [← zmod2_bool_decide ((wiresOf gs (bitsOf n w)).getD out false)]
    change decide (h5OPb2f ((wiresOf gs (bitsOf n w)).getD out false) = 1) = _
    rw [hgsem w, h0sem w]

end Circuit


namespace Circuit

open PEqualNP.CircuitLowerBounds
open Classical

def concatVec {k : ℕ} (x y : Fin k → F2) : Fin (2 * k) → F2 :=
  fun idx => if h : idx.val < k then x ⟨idx.val, h⟩ else y ⟨idx.val - k, by omega⟩

lemma bitsOf_concatVec {k : ℕ} (x y : Fin k → F2) :
    bitsOf k x ++ bitsOf k y = bitsOf (2 * k) (concatVec x y) := by
  apply List.ext_getElem
  · simp [bitsOf_len]; omega
  · intro i h1 h2
    simp only [bitsOf]
    by_cases hik : i < k
    · rw [List.getElem_append_left (by simp; exact hik)]
      simp [concatVec, hik]
    · rw [List.getElem_append_right (by simp; omega)]
      simp [concatVec, hik]

lemma dotProduct_concatVec {k : ℕ} (u v x y : Fin k → F2) :
    dotProduct (concatVec u v) (concatVec x y) = dotProduct u x + dotProduct v y := by
  simp only [dotProduct]
  let e : Fin k ⊕ Fin k ≃ Fin (2 * k) :=
    { toFun := Sum.elim (fun i => ⟨i.val, by omega⟩) (fun i => ⟨k + i.val, by omega⟩)
      invFun := fun i => if h : i.val < k then Sum.inl ⟨i.val, h⟩ else Sum.inr ⟨i.val - k, by omega⟩
      left_inv := fun s => by
        cases s with
        | inl i => simp [i.isLt]
        | inr i =>
          have hnot : ¬ (k + i.val < k) := by omega
          simp [hnot]
      right_inv := fun i => by
        by_cases h : i.val < k
        · simp [h]
        · simp only [h, ↓reduceDIte, Sum.elim_inr]
          apply Fin.ext; dsimp; omega }
  rw [← Equiv.sum_comp e, Fintype.sum_sum_type]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp [e, concatVec, i.isLt]
  · refine Finset.sum_congr rfl fun i _ => ?_
    have hnot : ¬ (k + i.val < k) := by omega
    simp [e, concatVec, hnot]

lemma linear_map_left_inv {k s : ℕ} (B : (Fin s → F2) →ₗ[F2] (Fin k → F2))
    (hB : Function.Injective B) :
    ∃ L : (Fin k → F2) →ₗ[F2] (Fin s → F2), ∀ v : Fin s → F2, L (B v) = v := by
  obtain ⟨V', hcompl⟩ := Submodule.exists_isCompl (LinearMap.range B)
  let π : (Fin k → F2) →ₗ[F2] LinearMap.range B := Submodule.linearProjOfIsCompl (LinearMap.range B) V' hcompl
  let e : (Fin s → F2) ≃ₗ[F2] LinearMap.range B := LinearEquiv.ofInjective B hB
  refine ⟨e.symm.toLinearMap.comp π, fun v => ?_⟩
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  have hmem : B v ∈ LinearMap.range B := ⟨v, rfl⟩
  have hpi : π (B v) = ⟨B v, hmem⟩ := Submodule.linearProjOfIsCompl_apply_left hcompl ⟨B v, hmem⟩
  rw [hpi]
  have hev : e v = ⟨B v, hmem⟩ := rfl
  rw [← hev, LinearEquiv.symm_apply_apply]

lemma linear_coord_dot {k : ℕ} (ℓ : (Fin k → F2) →ₗ[F2] F2) :
    ∃ r : Fin k → F2, ∀ y : Fin k → F2, ℓ y = dotProduct r y := by
  refine ⟨fun j => ℓ (Pi.single j 1), fun y => ?_⟩
  conv_lhs => rw [vec_eq_sum_single y, map_sum]
  simp only [dotProduct, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => by ring

lemma h5_exact_raw_identity (k s : ℕ) (g : (Fin k → F2) → F2)
    (B : (Fin s → F2) →ₗ[F2] (Fin k → F2)) (a : Fin k → F2)
    (q : (Fin s → F2) → F2) (L : (Fin k → F2) →ₗ[F2] (Fin s → F2))
    (hB : Function.Injective B) (hLB : ∀ v : Fin s → F2, L (B v) = v)
    (C : Circuit)
    (hCe : ∀ x y : Fin k → F2,
      C.eval (bitsOf k x ++ bitsOf k y) =
        decide (dotProduct x (a + B (L (y + a))) + q (L (y + a)) = 1)) :
    (∑ x : Fin k → F2, ∑ y : Fin k → F2,
      if C.eval (bitsOf k x ++ bitsOf k y) = decide (dotProduct x y + g y = 1)
      then (1 : ℤ) else -1).natAbs =
        2 ^ k * (∑ v : Fin s → F2, if g (a + B v) = q v then (1 : ℤ) else -1).natAbs := by
  have htotal : (∑ x : Fin k → F2, ∑ y : Fin k → F2,
      if C.eval (bitsOf k x ++ bitsOf k y) = decide (dotProduct x y + g y = 1)
      then (1 : ℤ) else -1) =
      (2 : ℤ) ^ k * ∑ v : Fin s → F2, if g (a + B v) = q v then (1 : ℤ) else -1 := by
    rw [Finset.sum_comm]
    have hinner : ∀ y : Fin k → F2,
        (∑ x : Fin k → F2, if C.eval (bitsOf k x ++ bitsOf k y) = decide (dotProduct x y + g y = 1)
          then (1 : ℤ) else -1) =
        if y + a ∈ LinearMap.range B then
          (2 : ℤ) ^ k * (if g y = q (L (y + a)) then (1 : ℤ) else -1)
        else 0 := by
      intro y
      have hrw : ∀ x : Fin k → F2,
          (if C.eval (bitsOf k x ++ bitsOf k y) = decide (dotProduct x y + g y = 1) then (1 : ℤ) else -1) =
          signBool (decide (dotProduct (a + B (L (y + a)) + y) x = 1)) *
            (if g y = q (L (y + a)) then (1 : ℤ) else -1) := by
        intro x
        rw [hCe x y, zmod2_add_decide (dotProduct x y) (g y), agree_eq_sign, eq_f2_sign]
        have hxor : Bool.xor (decide (dotProduct x (a + B (L (y + a))) + q (L (y + a)) = 1)) (decide (dotProduct x y = 1)) =
            Bool.xor (decide (dotProduct (a + B (L (y + a)) + y) x = 1)) (decide (q (L (y + a)) = 1)) := by
          rw [← zmod2_add_decide, ← zmod2_add_decide, add_dotProduct, dotProduct_comm (a + B (L (y + a))) x,
              dotProduct_comm y x]
          congr 1; ring
        rw [hxor, signBool_xor]
        ring
      simp_rw [hrw, ← Finset.sum_mul]
      by_cases hmem : y + a ∈ LinearMap.range B
      · simp only [hmem, ↓reduceIte]
        rcases hmem with ⟨v, hv⟩
        have hzero : a + B (L (y + a)) + y = 0 := by
          rw [← hv, hLB v, hv]
          calc a + (y + a) + y = (a + a) + (y + y) := by abel
            _ = 0 := by rw [zmod2_vec_add_self, zmod2_vec_add_self, add_zero]
        simp only [hzero, zero_dotProduct]
        have hcard : (∑ _x : Fin k → F2, signBool (decide ((0 : F2) = 1))) = (2 : ℤ) ^ k := by
          change (∑ _x : Fin k → F2, (1 : ℤ)) = (2 : ℤ) ^ k
          simp [ZMod.card]
        rw [hcard]
      · simp only [hmem, ↓reduceIte]
        have hne : a + B (L (y + a)) + y ≠ 0 := by
          intro h0
          apply hmem
          refine ⟨L (y + a), ?_⟩
          have h1 : B (L (y + a)) + (a + B (L (y + a)) + y) = y + a := by
            calc B (L (y + a)) + (a + B (L (y + a)) + y)
                = (B (L (y + a)) + B (L (y + a))) + (y + a) := by abel
              _ = y + a := by rw [zmod2_vec_add_self, zero_add]
          rw [h0, add_zero] at h1
          exact h1
        rw [sum_sign_dot_univ _ hne, zero_mul]
    simp_rw [hinner]
    rw [← Finset.sum_filter]
    let f_inj : (Fin s → F2) → (Fin k → F2) := fun v => a + B v
    have hbij : Finset.univ.image f_inj = Finset.univ.filter (fun y : Fin k → F2 => y + a ∈ LinearMap.range B) := by
      ext y
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter, f_inj]
      constructor
      · rintro ⟨v, rfl⟩
        refine ⟨v, ?_⟩
        calc B v = (a + a) + B v := by rw [zmod2_vec_add_self, zero_add]
          _ = a + B v + a := by abel
      · rintro ⟨v, hv⟩
        refine ⟨v, ?_⟩
        calc a + B v = a + (y + a) := by rw [hv]
          _ = (a + a) + y := by abel
          _ = y := by rw [zmod2_vec_add_self, zero_add]
    rw [← hbij, Finset.sum_image (fun v1 _ v2 _ h => hB (add_left_cancel h)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    have harg : f_inj v + a = B v := by
      dsimp only [f_inj]
      calc a + B v + a = (a + a) + B v := by abel
        _ = B v := by rw [zmod2_vec_add_self, zero_add]
    rw [harg, hLB v]
  rw [htotal, Int.natAbs_mul]
  have h2k : ((2 : ℤ) ^ k).natAbs = 2 ^ k := by
    rw [show (2 : ℤ) ^ k = ((2 ^ k : ℕ) : ℤ) by push_cast; rfl, Int.natAbs_natCast]
  rw [h2k]

end Circuit


namespace Circuit

open PEqualNP.CircuitLowerBounds
open Classical

lemma h5_quadratic_lift_data (k s : ℕ)
    (B : (Fin s → F2) →ₗ[F2] (Fin k → F2)) (a : Fin k → F2)
    (q : (Fin s → F2) → F2) (L : (Fin k → F2) →ₗ[F2] (Fin s → F2))
    (hq : isQuad q) :
    ∃ (c0 : Fin (2 * k) → F2) (b0 : F2)
      (cA cB : Fin s → Fin (2 * k) → F2) (bA bB : Fin s → F2),
      (∀ x y : Fin k → F2, ∀ i : Fin s,
        dotProduct (cA i) (concatVec x y) + bA i = L (y + a) i) ∧
      (∀ x y : Fin k → F2,
        (dotProduct c0 (concatVec x y) + b0) +
          ∑ i : Fin s, (dotProduct (cA i) (concatVec x y) + bA i) *
            (dotProduct (cB i) (concatVec x y) + bB i) =
          dotProduct x (a + B (L (y + a))) + q (L (y + a))) := by
  rcases hq with ⟨b, c, M, hq_eq⟩
  have hcoord : ∀ i : Fin s, ∃ r : Fin k → F2, ∀ w : Fin k → F2, L w i = dotProduct r w := fun i =>
    linear_coord_dot ((LinearMap.proj i).comp L)
  choose rv hrv using hcoord
  let c0 : Fin (2 * k) → F2 := concatVec a 0
  let b0 : F2 := b
  let cA : Fin s → Fin (2 * k) → F2 := fun i => concatVec 0 (rv i)
  let bA : Fin s → F2 := fun i => dotProduct (rv i) a
  let cB : Fin s → Fin (2 * k) → F2 := fun i =>
    concatVec (B (Pi.single i 1)) (∑ j : Fin s, M i j • rv j)
  let bB : Fin s → F2 := fun i => c i + ∑ j : Fin s, M i j * dotProduct (rv j) a
  refine ⟨c0, b0, cA, cB, bA, bB, ?_, ?_⟩
  · intro x y i
    simp only [cA, bA, dotProduct_concatVec, zero_dotProduct, zero_add, hrv i, dotProduct_add]
  intro x y
  have h0 : dotProduct c0 (concatVec x y) + b0 = dotProduct x a + b := by
    simp only [c0, b0, dotProduct_concatVec, zero_dotProduct, add_zero, dotProduct_comm a x]
  have hAi : ∀ i : Fin s, dotProduct (cA i) (concatVec x y) + bA i = L (y + a) i := by
    intro i
    simp only [cA, bA, dotProduct_concatVec, zero_dotProduct, zero_add, hrv i, dotProduct_add]
  have hBi : ∀ i : Fin s, dotProduct (cB i) (concatVec x y) + bB i =
      dotProduct x (B (Pi.single i 1)) + c i + ∑ j : Fin s, M i j * L (y + a) j := by
    intro i
    simp only [cB, bB, dotProduct_concatVec, dotProduct_comm (B (Pi.single i 1)) x]
    have hsum : dotProduct (∑ j : Fin s, M i j • rv j) y + ∑ j : Fin s, M i j * dotProduct (rv j) a =
        ∑ j : Fin s, M i j * L (y + a) j := by
      rw [sum_dotProduct, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_dotProduct, smul_eq_mul, hrv j, dotProduct_add]; ring
    calc
      _ = dotProduct x (B (Pi.single i 1)) + c i +
          (dotProduct (∑ j : Fin s, M i j • rv j) y +
            ∑ j : Fin s, M i j * dotProduct (rv j) a) := by ring
      _ = _ := by rw [hsum]
  have hPB : dotProduct x (B (L (y + a))) =
      ∑ i : Fin s, L (y + a) i * dotProduct x (B (Pi.single i 1)) := by
    conv_lhs => rw [vec_eq_sum_single (L (y + a)), map_sum, dotProduct_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, dotProduct_smul, smul_eq_mul]
  rw [h0, dotProduct_add, hPB, hq_eq (L (y + a))]
  have hterms : (∑ i : Fin s, (dotProduct (cA i) (concatVec x y) + bA i) * (dotProduct (cB i) (concatVec x y) + bB i)) =
      (∑ i : Fin s, L (y + a) i * dotProduct x (B (Pi.single i 1))) +
      dotProduct c (L (y + a)) +
      ∑ i : Fin s, ∑ j : Fin s, M i j * L (y + a) i * L (y + a) j := by
    simp_rw [hAi, hBi]
    calc (∑ i : Fin s, L (y + a) i * (dotProduct x (B (Pi.single i 1)) + c i + ∑ j : Fin s, M i j * L (y + a) j))
        = ∑ i : Fin s, ((L (y + a) i * dotProduct x (B (Pi.single i 1)) + c i * L (y + a) i) +
            ∑ j : Fin s, M i j * L (y + a) i * L (y + a) j) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [mul_add, mul_add, Finset.mul_sum]
          have hinner : (∑ j : Fin s, L (y + a) i * (M i j * L (y + a) j)) =
              ∑ j : Fin s, M i j * L (y + a) i * L (y + a) j :=
            Finset.sum_congr rfl fun j _ => by ring
          rw [hinner]; ring
      _ = (∑ i : Fin s, L (y + a) i * dotProduct x (B (Pi.single i 1))) +
          dotProduct c (L (y + a)) +
          ∑ i : Fin s, ∑ j : Fin s, M i j * L (y + a) i * L (y + a) j := by
          simp only [Finset.sum_add_distrib, dotProduct]
  rw [hterms]; ring

lemma h5_affine_lift_data {k s : ℕ}
    (L : (Fin k → F2) →ₗ[F2] (Fin s → F2)) (a : Fin k → F2)
    (u : Fin s → F2) (u0 : F2) :
    ∃ (u' : Fin (2 * k) → F2) (u0' : F2), ∀ x y : Fin k → F2,
      dotProduct u' (concatVec x y) + u0' = u0 + dotProduct u (L (y + a)) := by
  obtain ⟨v, v0, hv⟩ := linear_comp_affine L (L a) u u0
  refine ⟨concatVec 0 v, v0, fun x y => ?_⟩
  rw [dotProduct_concatVec, zero_dotProduct, zero_add, ← hv y, map_add]
  simp only [dotProduct_add]
  ring

end Circuit


namespace Circuit

open PEqualNP.CircuitLowerBounds
open Classical

lemma h5_flat_quad_to_circuit (k s : ℕ) (g : (Fin k → F2) → F2)
    (B : (Fin s → F2) →ₗ[F2] (Fin k → F2)) (a : Fin k → F2)
    (q : (Fin s → F2) → F2) (hB : Function.Injective B) (hq : isQuad q) :
    ∃ C : Circuit, legalGates (2 * k) C.gates ∧ costGates C.gates = s ∧
      (∑ x : Fin k → F2, ∑ y : Fin k → F2,
        if C.eval (bitsOf k x ++ bitsOf k y) = decide (dotProduct x y + g y = 1)
          then (1 : ℤ) else -1).natAbs = 2 ^ k * h5FlatBias g B a q := by
  obtain ⟨L, hLB⟩ := linear_map_left_inv B hB
  obtain ⟨c0, b0, cA, cB, bA, bB, _, hpoly⟩ := h5_quadratic_lift_data k s B a q L hq
  obtain ⟨C, hleg, hcost, heval⟩ := build_sum_prods_circuit (2 * k) s c0 b0 cA cB bA bB
  refine ⟨C, hleg, hcost, ?_⟩
  apply h5_exact_raw_identity k s g B a q L hB hLB C
  intro x y
  rw [bitsOf_concatVec, heval]
  congr 2
  exact hpoly x y

lemma h5_flat_triple_to_circuit (k s : ℕ) (g : (Fin k → F2) → F2)
    (B : (Fin s → F2) →ₗ[F2] (Fin k → F2)) (a : Fin k → F2)
    (q : (Fin s → F2) → F2) (hB : Function.Injective B) (hq : h5IsQuadPlusTriple q) :
    ∃ C : Circuit, legalGates (2 * k) C.gates ∧ costGates C.gates = s + 1 ∧
      (∑ x : Fin k → F2, ∑ y : Fin k → F2,
        if C.eval (bitsOf k x ++ bitsOf k y) = decide (dotProduct x y + g y = 1)
          then (1 : ℤ) else -1).natAbs = 2 ^ k * h5FlatBias g B a q := by
  obtain ⟨q0, hq0, c0, u0, v0, c, ul, vl, hq⟩ := hq
  obtain ⟨L, hLB⟩ := linear_map_left_inv B hB
  obtain ⟨cb, bb, cA, cB, bA, bB, hA, hpoly⟩ := h5_quadratic_lift_data k s B a q0 L hq0
  obtain ⟨cU, bU, hU⟩ := h5_affine_lift_data L a ul u0
  obtain ⟨cV, bV, hV⟩ := h5_affine_lift_data L a vl v0
  obtain ⟨C, hleg, hcost, heval⟩ :=
    h5TB_build_shared_product (2 * k) s cb cU cV bb bU bV c0 cA cB bA bB c
  refine ⟨C, hleg, hcost, ?_⟩
  apply h5_exact_raw_identity k s g B a q L hB hLB C
  intro x y
  rw [bitsOf_concatVec, heval]
  congr 2
  let z : F2 := (dotProduct cU (concatVec x y) + bU) * (dotProduct cV (concatVec x y) + bV)
  have hz : z = (u0 + dotProduct ul (L (y + a))) * (v0 + dotProduct vl (L (y + a))) := by
    dsimp only [z]
    rw [hU x y, hV x y]
  have hsum : (∑ i : Fin s, (dotProduct (cA i) (concatVec x y) + bA i) *
        (dotProduct (cB i) (concatVec x y) + bB i + c i * z)) =
      (∑ i : Fin s, (dotProduct (cA i) (concatVec x y) + bA i) *
        (dotProduct (cB i) (concatVec x y) + bB i)) + dotProduct c (L (y + a)) * z := by
    simp_rw [mul_add, Finset.sum_add_distrib]
    congr 1
    change (∑ i : Fin s, (dotProduct (cA i) (concatVec x y) + bA i) * (c i * z)) =
      (∑ i : Fin s, c i * L (y + a) i) * z
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [hA x y i]
    ring
  change (dotProduct cb (concatVec x y) + bb) + c0 * z +
      (∑ i : Fin s, (dotProduct (cA i) (concatVec x y) + bA i) *
        (dotProduct (cB i) (concatVec x y) + bB i + c i * z)) = _
  rw [hsum]
  calc
    _ = ((dotProduct cb (concatVec x y) + bb) +
        ∑ i : Fin s, (dotProduct (cA i) (concatVec x y) + bA i) *
          (dotProduct (cB i) (concatVec x y) + bB i)) +
        (c0 + dotProduct c (L (y + a))) * z := by ring
    _ = dotProduct x (a + B (L (y + a))) + q (L (y + a)) := by
      rw [hpoly x y, hq, hz]
      ring

lemma h5_circuit_attainment_from_flats (n m b plane line : ℕ)
    (g : (Fin n → F2) → F2)
    (hquad : ∃ (B : (Fin b → F2) →ₗ[F2] (Fin n → F2)) (a : Fin n → F2)
      (q : (Fin b → F2) → F2), Function.Injective B ∧ isQuad q ∧
        2 ^ (m + 2) * h5FlatBias g B a q = 2 ^ b * plane)
    (htriple : ∃ t, t + 1 = b ∧
      ∃ (B : (Fin t → F2) →ₗ[F2] (Fin n → F2)) (a : Fin n → F2)
        (q : (Fin t → F2) → F2), Function.Injective B ∧ h5IsQuadPlusTriple q ∧
          2 ^ (m + 2) * h5FlatBias g B a q = 2 ^ b * line) :
    ∃ C : Circuit, legalGates (2 * n) C.gates ∧ costGates C.gates ≤ b ∧
      2 ^ (m + 2) * (∑ x : Fin n → F2, ∑ y : Fin n → F2,
        if C.eval (bitsOf n x ++ bitsOf n y) = decide (dotProduct x y + g y = 1)
          then (1 : ℤ) else -1).natAbs = 2 ^ (n + b) * max plane line := by
  by_cases hmax : plane ≤ line
  · obtain ⟨t, ht, B, a, q, hB, hq, hflat⟩ := htriple
    obtain ⟨C, hleg, hcost, hraw⟩ := h5_flat_triple_to_circuit n t g B a q hB hq
    refine ⟨C, hleg, by omega, ?_⟩
    rw [hraw, max_eq_right hmax]
    calc
      _ = 2 ^ n * (2 ^ (m + 2) * h5FlatBias g B a q) := by ring
      _ = 2 ^ (n + b) * line := by rw [hflat, pow_add]; ring
  · obtain ⟨B, a, q, hB, hq, hflat⟩ := hquad
    obtain ⟨C, hleg, hcost, hraw⟩ := h5_flat_quad_to_circuit n b g B a q hB hq
    refine ⟨C, hleg, by omega, ?_⟩
    rw [hraw, max_eq_left (by omega)]
    calc
      _ = 2 ^ n * (2 ^ (m + 2) * h5FlatBias g B a q) := by ring
      _ = 2 ^ (n + b) * plane := by rw [hflat, pow_add]; ring

end Circuit

section h5_part_9

def h5PairSwap (m : ℕ) : (Fin m × Bool) ≃ (Fin m × Bool) where
  toFun p := (p.1, !p.2)
  invFun p := (p.1, !p.2)
  left_inv p := by simp
  right_inv p := by simp

def h5PairDiagonal {m : ℕ} (c : Fin m → ZMod 2) :
    Matrix (Fin m × Bool) (Fin m × Bool) (ZMod 2) :=
  (Matrix.diagonal (fun p : Fin m × Bool => c p.1)).submatrix
    (Equiv.refl _) (h5PairSwap m)

def h5BitWeight {m : ℕ} (c : Fin m → ZMod 2) : ℕ :=
  ((Finset.univ : Finset (Fin m)).filter (fun i => c i ≠ 0)).card

lemma h5_pair_diagonal_apply {m : ℕ} (c : Fin m → ZMod 2)
    (p q : Fin m × Bool) :
    h5PairDiagonal c p q = if p.1 = q.1 ∧ p.2 ≠ q.2 then c p.1 else 0 := by
  rcases p with ⟨i, b⟩
  rcases q with ⟨j, d⟩
  cases b <;> cases d <;> simp [h5PairDiagonal, h5PairSwap, Matrix.diagonal, Prod.mk.injEq]

lemma h5_pair_diagonal_rank {m : ℕ} (c : Fin m → ZMod 2) :
    (h5PairDiagonal c).rank = 2 * h5BitWeight c := by
  rw [h5PairDiagonal, Matrix.rank_submatrix]
  rw [Matrix.rank_diagonal (fun p : Fin m × Bool => c p.1)]
  let e : {p : Fin m × Bool // c p.1 ≠ 0} ≃ ({i : Fin m // c i ≠ 0} × Bool) :=
    { toFun p := (⟨p.1.1, p.2⟩, p.1.2)
      invFun p := ⟨(p.1.1, p.2), p.1.2⟩
      left_inv p := rfl
      right_inv p := rfl }
  rw [Fintype.card_congr e, Fintype.card_prod, Fintype.card_bool]
  simp only [Fintype.card_subtype, h5BitWeight, Nat.mul_comm]

lemma h5_pair_diagonal_add {m : ℕ} (c d : Fin m → ZMod 2) :
    h5PairDiagonal (c + d) = h5PairDiagonal c + h5PairDiagonal d := by
  ext p q
  simp only [h5_pair_diagonal_apply, Pi.add_apply, Matrix.add_apply]
  split <;> simp_all

lemma h5_bit_weight_complement {m : ℕ} (c : Fin m → ZMod 2) :
    h5BitWeight (1 + c) + h5BitWeight c = m := by
  have hbit : ∀ x : ZMod 2, 1 + x ≠ 0 ↔ x = 0 := by decide
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin m))) (fun i => c i = 0)
  simpa only [h5BitWeight, Pi.add_apply, Pi.one_apply, hbit, Fintype.card_fin,
    Finset.card_univ] using h

lemma h5_matrix_rank_add_le {I J : Type*} [Fintype I] [Fintype J]
    (A B : Matrix I J (ZMod 2)) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  have hle : LinearMap.range (A + B).mulVecLin ≤
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    rintro _ ⟨v, rfl⟩
    rw [Matrix.mulVecLin_add, LinearMap.add_apply]
    exact Submodule.add_mem_sup
      (LinearMap.mem_range_self A.mulVecLin v) (LinearMap.mem_range_self B.mulVecLin v)
  exact (Submodule.finrank_mono hle).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

lemma h5_rank_bound_of_full_toggle {m : ℕ}
    (Q : Matrix (Fin m × Bool) (Fin m × Bool) (ZMod 2))
    (z : Fin m → ZMod 2)
    (hz : (Q + h5PairDiagonal z).rank = 2 * m)
    (c : Fin m → ZMod 2) :
    2 * h5BitWeight (1 + z + c) ≤ (Q + h5PairDiagonal c).rank := by
  have htwo : ∀ x : ZMod 2, x + x = 0 := by decide
  have hcancel : (Q + h5PairDiagonal c) + h5PairDiagonal (z + c) =
      Q + h5PairDiagonal z := by
    rw [h5_pair_diagonal_add]
    ext p q
    simp only [Matrix.add_apply]
    have hh := htwo (h5PairDiagonal c p q)
    calc
      Q p q + h5PairDiagonal c p q +
          (h5PairDiagonal z p q + h5PairDiagonal c p q) =
        Q p q + h5PairDiagonal z p q +
          (h5PairDiagonal c p q + h5PairDiagonal c p q) := by ac_rfl
      _ = Q p q + h5PairDiagonal z p q := by rw [hh, add_zero]
  have h := h5_matrix_rank_add_le (Q + h5PairDiagonal c) (h5PairDiagonal (z + c))
  rw [hcancel, hz, h5_pair_diagonal_rank] at h
  have hw := h5_bit_weight_complement (z + c)
  rw [← add_assoc] at hw
  omega

lemma h5_restricted_polar_rank {n t : ℕ}
    (Q : Matrix (Fin n) (Fin n) (ZMod 2))
    (P : Matrix (Fin n) (Fin t) (ZMod 2)) (hP : P.rank = t) :
    Q.rank ≤ (P.transpose * Q * P).rank + 2 * (n - t) := by
  have hPt : P.transpose.rank = t := (Matrix.rank_transpose P).trans hP
  have htn : t ≤ n := by
    have h := Matrix.rank_le_width P.transpose
    omega
  have hleft := Matrix.rank_mul_ge P.transpose Q
  have hright := Matrix.rank_mul_ge (P.transpose * Q) P
  simp only [Fintype.card_fin] at hleft hright
  omega

lemma h5_rank_bound_of_isUnit_toggle {m : ℕ}
    (Q : Matrix (Fin m × Bool) (Fin m × Bool) (ZMod 2))
    (z : Fin m → ZMod 2) (hz : IsUnit (Q + h5PairDiagonal z))
    (c : Fin m → ZMod 2) :
    2 * h5BitWeight (1 + z + c) ≤ (Q + h5PairDiagonal c).rank := by
  apply h5_rank_bound_of_full_toggle Q z
  have h := Matrix.rank_of_isUnit (Q + h5PairDiagonal z) hz
  simpa only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Nat.mul_comm] using h

lemma h5_restricted_rank_bound_of_full_toggle {m t : ℕ}
    (Q : Matrix (Fin m × Bool) (Fin m × Bool) (ZMod 2))
    (z : Fin m → ZMod 2)
    (hz : (Q + h5PairDiagonal z).rank = 2 * m)
    (P : Matrix (Fin m × Bool) (Fin t) (ZMod 2)) (hP : P.rank = t)
    (c : Fin m → ZMod 2) :
    2 * h5BitWeight (1 + z + c) ≤
      (P.transpose * (Q + h5PairDiagonal c) * P).rank + 2 * (2 * m - t) := by
  have hPt : P.transpose.rank = t := (Matrix.rank_transpose P).trans hP
  have htn : t ≤ 2 * m := by
    have h := Matrix.rank_le_card_width P.transpose
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at h
    omega
  have hleft := Matrix.rank_mul_ge P.transpose (Q + h5PairDiagonal c)
  have hright := Matrix.rank_mul_ge (P.transpose * (Q + h5PairDiagonal c)) P
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at hleft hright
  have hbase := h5_rank_bound_of_full_toggle Q z hz c
  omega

lemma h5_symmetric_zero_diagonal_alternating {I : Type*} [Fintype I]
    (Q : Matrix I I (ZMod 2)) (hs : Q.transpose = Q) (hd : ∀ i, Q i i = 0) :
    ∀ x : I → ZMod 2, dotProduct x (Q.mulVec x) = 0 := by
  intro x
  have htwo : ∀ a : ZMod 2, a + a = 0 := by decide
  have heq : dotProduct x (Q.mulVec x) =
      ∑ p : I × I, x p.1 * Q p.1 p.2 * x p.2 := by
    rw [Fintype.sum_prod_type]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rw [heq]
  apply Finset.sum_ninvolution Prod.swap
  · intro p
    have hsym : Q p.2 p.1 = Q p.1 p.2 := congrArg (fun M => M p.1 p.2) hs
    change x p.1 * Q p.1 p.2 * x p.2 + x p.2 * Q p.2 p.1 * x p.1 = 0
    rw [hsym]
    have hterm : x p.2 * Q p.1 p.2 * x p.1 = x p.1 * Q p.1 p.2 * x p.2 := by ring
    rw [hterm, htwo]
  · intro p hp he
    have hpdiag : p.1 = p.2 := (congrArg Prod.fst he).symm
    apply hp
    rw [hpdiag, hd, mul_zero, zero_mul]
  · intro p
    exact Finset.mem_univ _
  · intro p
    exact Prod.swap_swap p

def h5ToggleTwo (z : ZMod 2) : Matrix Bool Bool (ZMod 2) :=
  fun b d => if b = d then 0 else z

lemma h5_toggle_two_isUnit (S : Matrix Bool Bool (ZMod 2))
    (hs : S.transpose = S) (hd : ∀ b, S b b = 0) :
    ∃ z : ZMod 2, IsUnit (S + h5ToggleTwo z) := by
  refine ⟨1 - S false true, ?_⟩
  have heq : S + h5ToggleTwo (1 - S false true) = h5ToggleTwo 1 := by
    ext b d
    have hst : S true false = S false true := congrArg (fun M => M false true) hs
    cases b <;> cases d <;> simp [h5ToggleTwo, hd, hst]
  rw [heq]
  have hJ : h5ToggleTwo 1 * h5ToggleTwo 1 = 1 := by decide
  exact ⟨⟨h5ToggleTwo 1, h5ToggleTwo 1, hJ, hJ⟩, rfl⟩

lemma h5_inverse_alternating {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I (ZMod 2)) (hA : IsUnit A)
    (ha : ∀ x : I → ZMod 2, dotProduct x (A.mulVec x) = 0) :
    ∀ x : I → ZMod 2, dotProduct x (A⁻¹.mulVec x) = 0 := by
  intro x
  have hc : A.mulVec (A⁻¹.mulVec x) = x := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA),
      Matrix.one_mulVec]
  have h := ha (A⁻¹.mulVec x)
  rw [hc] at h
  exact (dotProduct_comm x (A⁻¹.mulVec x)).trans h

lemma h5_schur_alternating {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I (ZMod 2)) (B : Matrix I Bool (ZMod 2))
    (D : Matrix Bool Bool (ZMod 2))
    (hA : IsUnit A) (hsA : A.transpose = A)
    (haA : ∀ x : I → ZMod 2, dotProduct x (A.mulVec x) = 0)
    (hsD : D.transpose = D) (hdD : ∀ b, D b b = 0) :
    (D - B.transpose * A⁻¹ * B).transpose = D - B.transpose * A⁻¹ * B ∧
      ∀ b, (D - B.transpose * A⁻¹ * B) b b = 0 := by
  constructor
  · simp only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_nonsing_inv, hsA, hsD]
    rw [Matrix.mul_assoc]
  · intro b
    have heq : (B.transpose * A⁻¹ * B) b b =
        dotProduct (fun i => B i b) (A⁻¹.mulVec (fun i => B i b)) := by
      rw [Matrix.mul_assoc]
      rfl
    rw [Matrix.sub_apply, hdD b, heq, h5_inverse_alternating A hA haA]
    simp

lemma h5_extend_invertible_pair {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I (ZMod 2)) (B : Matrix I Bool (ZMod 2))
    (D : Matrix Bool Bool (ZMod 2))
    (hA : IsUnit A) (hsA : A.transpose = A)
    (haA : ∀ x : I → ZMod 2, dotProduct x (A.mulVec x) = 0)
    (hsD : D.transpose = D) (hdD : ∀ b, D b b = 0) :
    ∃ z : ZMod 2, IsUnit (Matrix.fromBlocks A B B.transpose (D + h5ToggleTwo z)) := by
  obtain ⟨hs, hd⟩ := h5_schur_alternating A B D hA hsA haA hsD hdD
  obtain ⟨z, hz⟩ := h5_toggle_two_isUnit (D - B.transpose * A⁻¹ * B) hs hd
  obtain ⟨hAi⟩ := hA.nonempty_invertible
  refine ⟨z, Matrix.isUnit_fromBlocks_iff_of_invertible₁₁.mpr ?_⟩
  rw [Matrix.invOf_eq_nonsing_inv]
  convert hz using 1
  ext b d
  simp only [Matrix.add_apply, Matrix.sub_apply]
  ring

def h5TogglePairs {m : ℕ} (z : Fin m → ZMod 2) :
    Matrix (Fin m × Bool) (Fin m × Bool) (ZMod 2) :=
  fun p q => if p.1 = q.1 ∧ p.2 ≠ q.2 then z p.1 else 0

lemma h5_toggle_pairs_symm {m : ℕ} (z : Fin m → ZMod 2) :
    (h5TogglePairs z).transpose = h5TogglePairs z := by
  ext p q
  simp only [Matrix.transpose_apply, h5TogglePairs]
  by_cases hi : p.1 = q.1
  · rw [hi]
    simp [ne_comm]
  · simp [hi, Ne.symm hi]

lemma h5_toggle_pairs_mulVec {m : ℕ} (z : Fin m → ZMod 2)
    (x : Fin m × Bool → ZMod 2) (i : Fin m) (b : Bool) :
    (h5TogglePairs z).mulVec x (i, b) = z i * x (i, !b) := by
  cases b <;> simp [Matrix.mulVec, dotProduct, h5TogglePairs, Fintype.sum_prod_type]

lemma h5_toggle_pairs_alternating {m : ℕ} (z : Fin m → ZMod 2) :
    ∀ x : Fin m × Bool → ZMod 2, dotProduct x ((h5TogglePairs z).mulVec x) = 0 := by
  intro x
  simp only [dotProduct, Fintype.sum_prod_type, h5_toggle_pairs_mulVec]
  apply Finset.sum_eq_zero
  intro i hi
  simp only [Fintype.sum_bool, Bool.not_false, Bool.not_true]
  have htwo : ∀ a : ZMod 2, a + a = 0 := by decide
  calc
    x (i, true) * (z i * x (i, false)) + x (i, false) * (z i * x (i, true)) =
      (x (i, false) * z i * x (i, true)) + (x (i, false) * z i * x (i, true)) := by ring
    _ = 0 := htwo _

def h5PairSucc (m : ℕ) : ((Fin m × Bool) ⊕ Bool) ≃ (Fin (m + 1) × Bool) where
  toFun := Sum.elim (fun p => (p.1.succ, p.2)) (fun b => (0, b))
  invFun p := Fin.cases (Sum.inr p.2) (fun i => Sum.inl (i, p.2)) p.1
  left_inv p := by cases p <;> rfl
  right_inv p := by
    rcases p with ⟨i, b⟩
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

lemma h5_exists_full_toggle : ∀ (m : ℕ)
    (Q : Matrix (Fin m × Bool) (Fin m × Bool) (ZMod 2)),
    Q.transpose = Q →
    (∀ x : Fin m × Bool → ZMod 2, dotProduct x (Q.mulVec x) = 0) →
    ∃ z : Fin m → ZMod 2, IsUnit (Q + h5TogglePairs z) := by
  intro m
  induction m with
  | zero =>
    intro Q hs ha
    refine ⟨fun i => Fin.elim0 i, ?_⟩
    have heq : Q + h5TogglePairs (fun i : Fin 0 => Fin.elim0 i) = 1 := by
      ext p q
      exact Fin.elim0 p.1
    rw [heq]
    exact isUnit_one
  | succ m ih =>
    intro Q hs ha
    let A : Matrix (Fin m × Bool) (Fin m × Bool) (ZMod 2) :=
      fun p q => Q (p.1.succ, p.2) (q.1.succ, q.2)
    let B : Matrix (Fin m × Bool) Bool (ZMod 2) :=
      fun p b => Q (p.1.succ, p.2) (0, b)
    let D : Matrix Bool Bool (ZMod 2) := fun b d => Q (0, b) (0, d)
    have hsA : A.transpose = A := by
      ext p q
      exact congrArg (fun M => M (p.1.succ, p.2) (q.1.succ, q.2)) hs
    have haA : ∀ x : Fin m × Bool → ZMod 2, dotProduct x (A.mulVec x) = 0 := by
      intro x
      let xx : Fin (m + 1) × Bool → ZMod 2 := fun p =>
        Fin.cases 0 (fun i => x (i, p.2)) p.1
      have hh := ha xx
      simpa [xx, A, dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Fin.sum_univ_succ] using hh
    obtain ⟨z, hz⟩ := ih A hsA haA
    have hsAz : (A + h5TogglePairs z).transpose = A + h5TogglePairs z := by
      rw [Matrix.transpose_add, hsA, h5_toggle_pairs_symm]
    have haAz : ∀ x : Fin m × Bool → ZMod 2,
        dotProduct x ((A + h5TogglePairs z).mulVec x) = 0 := by
      intro x
      rw [Matrix.add_mulVec, dotProduct_add, haA, h5_toggle_pairs_alternating]
      rfl
    have hsD : D.transpose = D := by
      ext b d
      exact congrArg (fun M => M (0, b) (0, d)) hs
    have hdD : ∀ b, D b b = 0 := by
      intro b
      have hh := ha (Pi.single (0, b) 1)
      simpa [D] using hh
    obtain ⟨last, hlast⟩ := h5_extend_invertible_pair (A + h5TogglePairs z) B D hz hsAz haAz hsD hdD
    let zz : Fin (m + 1) → ZMod 2 := Fin.cons last z
    refine ⟨zz, ?_⟩
    apply (Matrix.isUnit_submatrix_equiv (h5PairSucc m) (h5PairSucc m)).mp
    have heq : (Q + h5TogglePairs zz).submatrix (h5PairSucc m) (h5PairSucc m) =
        Matrix.fromBlocks (A + h5TogglePairs z) B B.transpose (D + h5ToggleTwo last) := by
      ext p q
      cases p with
      | inl p =>
        cases q with
        | inl q =>
          change Q (p.1.succ, p.2) (q.1.succ, q.2) +
              h5TogglePairs zz (p.1.succ, p.2) (q.1.succ, q.2) =
            A p q + h5TogglePairs z p q
          simp [A, h5TogglePairs, zz]
        | inr q =>
          change Q (p.1.succ, p.2) (0, q) +
              h5TogglePairs zz (p.1.succ, p.2) (0, q) = B p q
          simp [B, h5TogglePairs]
      | inr p =>
        cases q with
        | inl q =>
          have hh := congrArg (fun M => M (0, p) (q.1.succ, q.2)) hs
          have hn : (0 : Fin (m + 1)) ≠ q.1.succ := Ne.symm (Fin.succ_ne_zero _)
          change Q (0, p) (q.1.succ, q.2) +
              h5TogglePairs zz (0, p) (q.1.succ, q.2) = B q p
          simpa [B, h5TogglePairs, hn] using hh.symm
        | inr q =>
          change Q (0, p) (0, q) + h5TogglePairs zz (0, p) (0, q) =
            D p q + h5ToggleTwo last p q
          simp [D, h5TogglePairs, h5ToggleTwo, zz]
    rw [heq]
    exact hlast

lemma h5_pair_diagonal_eq_toggle_pairs {m : ℕ} (c : Fin m → ZMod 2) :
    h5PairDiagonal c = h5TogglePairs c := by
  ext p q
  exact h5_pair_diagonal_apply c p q

lemma h5_exists_unit_pair_diagonal {m : ℕ}
    (Q : Matrix (Fin m × Bool) (Fin m × Bool) (ZMod 2))
    (hs : Q.transpose = Q) (hd : ∀ p, Q p p = 0) :
    ∃ z : Fin m → ZMod 2, IsUnit (Q + h5PairDiagonal z) := by
  obtain ⟨z, hz⟩ := h5_exists_full_toggle m Q hs
    (h5_symmetric_zero_diagonal_alternating Q hs hd)
  refine ⟨z, ?_⟩
  rwa [h5_pair_diagonal_eq_toggle_pairs]

lemma h5_translated_pair_rank_bound {m : ℕ}
    (Q : Matrix (Fin m × Bool) (Fin m × Bool) (ZMod 2))
    (hs : Q.transpose = Q) (hd : ∀ p, Q p p = 0) :
    ∃ a : Fin m → ZMod 2, ∀ c : Fin m → ZMod 2,
      2 * h5BitWeight (a + c) ≤ (Q + h5PairDiagonal c).rank := by
  obtain ⟨z, hz⟩ := h5_exists_unit_pair_diagonal Q hs hd
  exact ⟨1 + z, h5_rank_bound_of_isUnit_toggle Q z hz⟩

lemma h5_translated_pair_restriction_rank_bound {m : ℕ}
    (Q : Matrix (Fin m × Bool) (Fin m × Bool) (ZMod 2))
    (hs : Q.transpose = Q) (hd : ∀ p, Q p p = 0) :
    ∃ a : Fin m → ZMod 2,
      ∀ (t : ℕ) (P : Matrix (Fin m × Bool) (Fin t) (ZMod 2)), P.rank = t →
        ∀ c : Fin m → ZMod 2,
          2 * h5BitWeight (a + c) ≤
            (P.transpose * (Q + h5PairDiagonal c) * P).rank + 2 * (2 * m - t) := by
  obtain ⟨z, hz⟩ := h5_exists_unit_pair_diagonal Q hs hd
  have hr : (Q + h5PairDiagonal z).rank = 2 * m := by
    have h := Matrix.rank_of_isUnit (Q + h5PairDiagonal z) hz
    simpa only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Nat.mul_comm] using h
  refine ⟨1 + z, ?_⟩
  intro t P hP c
  exact h5_restricted_rank_bound_of_full_toggle Q z hr P hP c

end h5_part_9

namespace Fourier

open Classical

end Fourier


section h5_part_10

lemma h5_gaussian_rank_factor_le (m rk w : ℕ) (hw : w ≤ m) (hr : 2 * w ≤ rk) :
    (2 : ℤ) ^ (2 * m - rk / 2) ≤ (2 : ℤ) ^ m * (2 : ℤ) ^ (m - w) := by
  rw [← pow_add]
  apply pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
  omega

open Classical

lemma h5_gaussian_rank_sum_le {k m : ℕ}
    (Q : Matrix (Fin m × Bool) (Fin m × Bool) (ZMod 2))
    (hs : Q.transpose = Q) (hd : ∀ p, Q p p = 0)
    (U : Submodule (ZMod 2) (Fin k → ZMod 2))
    (L : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2)) :
    (∑ u : U, (2 : ℤ) ^ (2 * m - (Q + h5PairDiagonal (L u)).rank / 2)) ≤
      (2 : ℤ) ^ m * ∑ u : U, (2 : ℤ) ^ (m - h5BitWeight (L u)) := by
  classical
  obtain ⟨a, ha⟩ := h5_translated_pair_rank_bound Q hs hd
  have hpoint : ∀ u : U,
      (2 : ℤ) ^ (2 * m - (Q + h5PairDiagonal (L u)).rank / 2) ≤
        (2 : ℤ) ^ m * (2 : ℤ) ^ (m - h5BitWeight (L u + a)) := by
    intro u
    have hr := ha (L u)
    rw [add_comm a (L u)] at hr
    apply h5_gaussian_rank_factor_le m _ _ ?_ hr
    exact (Finset.card_filter_le _ _).trans_eq (Finset.card_fin m)
  have hcoset := Fourier.linear_code_submodule_coset_weight_le U L a
  change (∑ u : U, (2 : ℤ) ^ (m - h5BitWeight (L u + a))) ≤
      ∑ u : U, (2 : ℤ) ^ (m - h5BitWeight (L u)) at hcoset
  calc
    (∑ u : U, (2 : ℤ) ^ (2 * m - (Q + h5PairDiagonal (L u)).rank / 2)) ≤
        ∑ u : U, (2 : ℤ) ^ m * (2 : ℤ) ^ (m - h5BitWeight (L u + a)) :=
      Finset.sum_le_sum (fun u _ => hpoint u)
    _ = (2 : ℤ) ^ m * ∑ u : U, (2 : ℤ) ^ (m - h5BitWeight (L u + a)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (2 : ℤ) ^ m * ∑ u : U, (2 : ℤ) ^ (m - h5BitWeight (L u)) :=
      mul_le_mul_of_nonneg_left hcoset (by positivity)

end h5_part_10
namespace Gauss

open Classical

abbrev F2 := ZMod 2

lemma f2_add_self (a : F2) : a + a = 0 := by
  fin_cases a <;> decide

lemma f2_cases (a : F2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma f2_vec_add_self {ι : Type*} (x : ι → F2) : x + x = 0 := by
  funext i
  exact f2_add_self (x i)

def chi (a : F2) : ℤ := if a = 0 then 1 else -1

lemma chi_zero : chi 0 = 1 := rfl

lemma chi_one : chi 1 = -1 := rfl

lemma chi_add (a b : F2) : chi (a + b) = chi a * chi b := by
  fin_cases a <;> fin_cases b <;> rfl

lemma chi_eq (a b : F2) : (if a = b then (1 : ℤ) else -1) = chi (a + b) := by
  fin_cases a <;> fin_cases b <;> rfl

lemma chi_abs (a : F2) : |chi a| = 1 := by
  fin_cases a <;> decide

lemma chi_le_one (a : F2) : chi a ≤ 1 := by
  fin_cases a <;> decide

lemma chi_sum {α : Type*} (s : Finset α) (f : α → F2) :
    chi (∑ i ∈ s, f i) = ∏ i ∈ s, chi (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [chi]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, chi_add, ih]

lemma sum_chi_addHom {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Finset (ι → F2)) (hadd : ∀ x ∈ H, ∀ y ∈ H, x + y ∈ H)
    (φ : (ι → F2) → F2) (hφ : ∀ x ∈ H, ∀ y ∈ H, φ (x + y) = φ x + φ y) :
    (∑ x ∈ H, chi (φ x)) = if ∀ x ∈ H, φ x = 0 then (H.card : ℤ) else 0 := by
  split_ifs with hall
  · have h1 : ∀ x ∈ H, chi (φ x) = 1 := fun x hx => by rw [hall x hx]; rfl
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one]
  · push Not at hall
    obtain ⟨x₀, hx₀, hne⟩ := hall
    have hx₀1 : φ x₀ = 1 := by
      rcases f2_cases (φ x₀) with h | h
      · exact absurd h hne
      · exact h
    have hbij : ∑ x ∈ H, chi (φ x) = ∑ x ∈ H, chi (φ (x + x₀)) := by
      refine Finset.sum_bij (fun x _ => x + x₀) ?_ ?_ ?_ ?_
      · intro x hx; exact hadd x hx x₀ hx₀
      · intro x _ y _ hxy
        have := congrArg (· + x₀) hxy
        simpa [add_assoc, f2_vec_add_self] using this
      · intro y hy
        refine ⟨y + x₀, hadd y hy x₀ hx₀, ?_⟩
        simp [add_assoc, f2_vec_add_self]
      · intro x _
        congr 2
        rw [add_assoc, f2_vec_add_self, add_zero]
    have hneg : ∑ x ∈ H, chi (φ (x + x₀)) = - ∑ x ∈ H, chi (φ x) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [hφ x hx x₀ hx₀, hx₀1, chi_add, chi_one]
      ring
    linarith

lemma sum_chi_dot {m : ℕ} (a : Fin m → F2) :
    (∑ x : Fin m → F2, chi (dotProduct a x)) = if a = 0 then (2 : ℤ) ^ m else 0 := by
  have h := sum_chi_addHom (Finset.univ : Finset (Fin m → F2))
    (fun _ _ _ _ => Finset.mem_univ _) (fun x => dotProduct a x)
    (fun x _ y _ => dotProduct_add a x y)
  have hiff : (∀ x ∈ (Finset.univ : Finset (Fin m → F2)), dotProduct a x = 0) ↔ a = 0 := by
    constructor
    · intro hall
      funext i
      have hi := hall (Pi.single i 1) (Finset.mem_univ _)
      simpa [dotProduct_single] using hi
    · intro ha x _
      rw [ha, zero_dotProduct]
  rw [h]
  by_cases ha : a = 0
  · simp only [ha, ↓reduceIte]
    have hall : ∀ x ∈ (Finset.univ : Finset (Fin m → F2)), dotProduct 0 x = 0 :=
      fun x _ => zero_dotProduct x
    simp [hall]
  · simp only [mt hiff.mp ha, ha, ↓reduceIte]

def polar {ι : Type*} (q : (ι → F2) → F2) (h t : ι → F2) : F2 :=
  q (h + t) + q h + q t + q 0

lemma gauss_square_identity {m : ℕ} (q : (Fin m → F2) → F2)
    (L : (Fin m → F2) →ₗ[F2] (Fin m → F2))
    (hpol : ∀ h t, polar q h t = dotProduct (L h) t) :
    (∑ x : Fin m → F2, chi (q x)) ^ 2 =
      (2 : ℤ) ^ m * ∑ h ∈ (Finset.univ.filter (fun h => L h = 0)),
        chi (q h + q 0) := by
  classical
  let H : Finset (Fin m → F2) := Finset.univ.filter (fun h => L h = 0)
  have hH_mem : ∀ h, h ∈ H ↔ L h = 0 := by intro h; simp [H]
  have h1 : (∑ x : Fin m → F2, chi (q x)) ^ 2 =
      ∑ x : Fin m → F2, ∑ y : Fin m → F2, chi (q x + q y) := by
    rw [sq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => (chi_add _ _).symm
  have h2 : ∀ x : Fin m → F2,
      (∑ y : Fin m → F2, chi (q x + q y)) =
      ∑ h : Fin m → F2, chi (q h + q 0) * chi (polar q h x) := by
    intro x
    refine Finset.sum_bij (fun y _ => y + x) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
    · intro y₁ _ y₂ _ h12
      have := congrArg (· + x) h12
      simpa [add_assoc, f2_vec_add_self] using this
    · intro h _
      exact ⟨h + x, Finset.mem_univ _, by simp [add_assoc, f2_vec_add_self]⟩
    · intro y _
      rw [← chi_add]
      congr 1
      have hp : polar q (y + x) x = q y + q (y + x) + q x + q 0 := by
        unfold polar
        rw [show (y + x) + x = y by simp [add_assoc, f2_vec_add_self]]
      rw [hp]
      have hqq : q (y + x) + q (y + x) = 0 := f2_add_self _
      have hq0 : q 0 + q 0 = 0 := f2_add_self _
      calc q x + q y
          = (q (y + x) + q (y + x)) + (q 0 + q 0) + (q x + q y) := by
            rw [hqq, hq0]; ring
        _ = q (y + x) + q 0 + (q y + q (y + x) + q x + q 0) := by ring
  rw [h1]
  simp_rw [h2]
  rw [Finset.sum_comm]
  have h3 : ∀ h : Fin m → F2,
      (∑ x : Fin m → F2, chi (q h + q 0) * chi (polar q h x)) =
      if h ∈ H then (2 : ℤ) ^ m * chi (q h + q 0) else 0 := by
    intro h
    rw [← Finset.mul_sum]
    simp_rw [hpol]
    rw [sum_chi_dot]
    by_cases hh : h ∈ H
    · simp only [hh, (hH_mem h).mp hh, ↓reduceIte]; ring
    · simp only [hh, mt (hH_mem h).mpr hh, ↓reduceIte, mul_zero]
  simp_rw [h3]
  rw [← Finset.sum_filter, ← Finset.mul_sum]
  have hfilt : Finset.univ.filter (fun h : Fin m → F2 => h ∈ H) = H := by
    ext h; simp
  rw [hfilt]

lemma gauss_square_bound {m : ℕ} (q : (Fin m → F2) → F2)
    (Q : Matrix (Fin m) (Fin m) F2)
    (hpol : ∀ h t, polar q h t = dotProduct (Q.mulVec h) t) :
    (∑ x : Fin m → F2, chi (q x)) ^ 2 ≤ (2 : ℤ) ^ (2 * m - Q.rank) := by
  classical
  let L := Q.mulVecLin
  let K : Submodule F2 (Fin m → F2) := LinearMap.ker L
  let H : Finset (Fin m → F2) := Finset.univ.filter (fun h => L h = 0)
  let d := Module.finrank F2 K
  have hdim : Q.rank + d = m := by
    simpa only [d, K, L, Matrix.rank, Module.finrank_fin_fun] using
      Q.mulVecLin.finrank_range_add_finrank_ker
  have hKcard : Fintype.card K = 2 ^ d := by
    rw [Fintype.card_congr (Module.finBasis F2 K).equivFun.toEquiv]
    simp [d, F2]
  have hHcard : H.card = 2 ^ d := by
    have hsub : H.card = Fintype.card K := by
      simpa [H, K, LinearMap.mem_ker] using
        (Fintype.card_subtype (fun h : Fin m → F2 => L h = 0)).symm
    rw [hsub, hKcard]
  have hsum : (∑ h ∈ H, chi (q h + q 0)) ≤ (H.card : ℤ) := by
    calc (∑ h ∈ H, chi (q h + q 0)) ≤ ∑ _h ∈ H, (1 : ℤ) :=
        Finset.sum_le_sum fun h _ => chi_le_one _
      _ = (H.card : ℤ) := by simp
  calc (∑ x : Fin m → F2, chi (q x)) ^ 2
      = (2 : ℤ) ^ m * ∑ h ∈ H, chi (q h + q 0) := gauss_square_identity q L hpol
    _ ≤ (2 : ℤ) ^ m * (H.card : ℤ) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (2 : ℤ) ^ (m + d) := by
      rw [hHcard, Nat.cast_pow, Nat.cast_ofNat, ← pow_add]
    _ = (2 : ℤ) ^ (2 * m - Q.rank) := by congr 1; omega

lemma gauss_bound {m : ℕ} (q : (Fin m → F2) → F2)
    (Q : Matrix (Fin m) (Fin m) F2)
    (hpol : ∀ h t, polar q h t = dotProduct (Q.mulVec h) t) :
    |∑ x : Fin m → F2, chi (q x)| ≤ (2 : ℤ) ^ (m - Q.rank / 2) := by
  have hsq := gauss_square_bound q Q hpol
  have hr := Matrix.rank_le_width Q
  have he : 2 * m - Q.rank ≤ (m - Q.rank / 2) * 2 := by omega
  have hp : (2 : ℤ) ^ (2 * m - Q.rank) ≤ (2 : ℤ) ^ ((m - Q.rank / 2) * 2) :=
    pow_le_pow_right₀ (by norm_num) he
  rw [pow_mul] at hp
  exact abs_le_of_sq_le_sq (hsq.trans hp) (by positivity)

lemma gauss_bound_of_rank_ge {m w : ℕ} (q : (Fin m → F2) → F2)
    (Q : Matrix (Fin m) (Fin m) F2)
    (hpol : ∀ h t, polar q h t = dotProduct (Q.mulVec h) t)
    (hrank : 2 * w ≤ Q.rank) :
    |∑ x : Fin m → F2, chi (q x)| ≤ (2 : ℤ) ^ (m - w) := by
  apply (gauss_bound q Q hpol).trans
  apply pow_le_pow_right₀ (by norm_num)
  omega

lemma sum_chi_dot_fintype {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → F2) :
    (∑ x : ι → F2, chi (dotProduct a x)) = if a = 0 then (2 : ℤ) ^ (Fintype.card ι) else 0 := by
  have h := sum_chi_addHom (Finset.univ : Finset (ι → F2))
    (fun _ _ _ _ => Finset.mem_univ _) (fun x => dotProduct a x)
    (fun x _ y _ => dotProduct_add a x y)
  have hiff : (∀ x ∈ (Finset.univ : Finset (ι → F2)), dotProduct a x = 0) ↔ a = 0 := by
    constructor
    · intro hall
      funext i
      have hi := hall (Pi.single i 1) (Finset.mem_univ _)
      simpa [dotProduct_single] using hi
    · intro ha x _
      rw [ha, zero_dotProduct]
  rw [h]
  by_cases ha : a = 0
  · simp only [ha, ↓reduceIte]
    have hall : ∀ x ∈ (Finset.univ : Finset (ι → F2)), dotProduct 0 x = 0 :=
      fun x _ => zero_dotProduct x
    simp [hall]
  · simp only [mt hiff.mp ha, ha, ↓reduceIte]

lemma gauss_square_identity_fintype {ι : Type*} [Fintype ι] [DecidableEq ι] (q : (ι → F2) → F2)
    (L : (ι → F2) →ₗ[F2] (ι → F2))
    (hpol : ∀ h t, polar q h t = dotProduct (L h) t) :
    (∑ x : ι → F2, chi (q x)) ^ 2 =
      (2 : ℤ) ^ (Fintype.card ι) * ∑ h ∈ (Finset.univ.filter (fun h => L h = 0)),
        chi (q h + q 0) := by
  classical
  let H : Finset (ι → F2) := Finset.univ.filter (fun h => L h = 0)
  have hH_mem : ∀ h, h ∈ H ↔ L h = 0 := by intro h; simp [H]
  have h1 : (∑ x : ι → F2, chi (q x)) ^ 2 =
      ∑ x : ι → F2, ∑ y : ι → F2, chi (q x + q y) := by
    rw [sq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => (chi_add _ _).symm
  have h2 : ∀ x : ι → F2,
      (∑ y : ι → F2, chi (q x + q y)) =
      ∑ h : ι → F2, chi (q h + q 0) * chi (polar q h x) := by
    intro x
    refine Finset.sum_bij (fun y _ => y + x) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
    · intro y₁ _ y₂ _ h12
      have := congrArg (· + x) h12
      simpa [add_assoc, f2_vec_add_self] using this
    · intro h _
      exact ⟨h + x, Finset.mem_univ _, by simp [add_assoc, f2_vec_add_self]⟩
    · intro y _
      rw [← chi_add]
      congr 1
      have hp : polar q (y + x) x = q y + q (y + x) + q x + q 0 := by
        unfold polar
        rw [show (y + x) + x = y by simp [add_assoc, f2_vec_add_self]]
      rw [hp]
      have hqq : q (y + x) + q (y + x) = 0 := f2_add_self _
      have hq0 : q 0 + q 0 = 0 := f2_add_self _
      calc q x + q y
          = (q (y + x) + q (y + x)) + (q 0 + q 0) + (q x + q y) := by
            rw [hqq, hq0]; ring
        _ = q (y + x) + q 0 + (q y + q (y + x) + q x + q 0) := by ring
  rw [h1]
  simp_rw [h2]
  rw [Finset.sum_comm]
  have h3 : ∀ h : ι → F2,
      (∑ x : ι → F2, chi (q h + q 0) * chi (polar q h x)) =
      if h ∈ H then (2 : ℤ) ^ (Fintype.card ι) * chi (q h + q 0) else 0 := by
    intro h
    rw [← Finset.mul_sum]
    simp_rw [hpol]
    rw [sum_chi_dot_fintype]
    by_cases hh : h ∈ H
    · simp only [hh, (hH_mem h).mp hh, ↓reduceIte]; ring
    · simp only [hh, mt (hH_mem h).mpr hh, ↓reduceIte, mul_zero]
  simp_rw [h3]
  rw [← Finset.sum_filter, ← Finset.mul_sum]
  have hfilt : Finset.univ.filter (fun h : ι → F2 => h ∈ H) = H := by
    ext h; simp
  rw [hfilt]

lemma gauss_square_bound_fintype {ι : Type*} [Fintype ι] [DecidableEq ι] (q : (ι → F2) → F2)
    (Q : Matrix (ι) (ι) F2)
    (hpol : ∀ h t, polar q h t = dotProduct (Q.mulVec h) t) :
    (∑ x : ι → F2, chi (q x)) ^ 2 ≤ (2 : ℤ) ^ (2 * (Fintype.card ι) - Q.rank) := by
  classical
  let L := Q.mulVecLin
  let K : Submodule F2 (ι → F2) := LinearMap.ker L
  let H : Finset (ι → F2) := Finset.univ.filter (fun h => L h = 0)
  let d := Module.finrank F2 K
  have hdim : Q.rank + d = (Fintype.card ι) := by
    simpa only [d, K, L, Matrix.rank, Module.finrank_pi] using
      Q.mulVecLin.finrank_range_add_finrank_ker
  have hKcard : Fintype.card K = 2 ^ d := by
    rw [Fintype.card_congr (Module.finBasis F2 K).equivFun.toEquiv]
    simp [d, F2]
  have hHcard : H.card = 2 ^ d := by
    have hsub : H.card = Fintype.card K := by
      simpa [H, K, LinearMap.mem_ker] using
        (Fintype.card_subtype (fun h : ι → F2 => L h = 0)).symm
    rw [hsub, hKcard]
  have hsum : (∑ h ∈ H, chi (q h + q 0)) ≤ (H.card : ℤ) := by
    calc (∑ h ∈ H, chi (q h + q 0)) ≤ ∑ _h ∈ H, (1 : ℤ) :=
        Finset.sum_le_sum fun h _ => chi_le_one _
      _ = (H.card : ℤ) := by simp
  calc (∑ x : ι → F2, chi (q x)) ^ 2
      = (2 : ℤ) ^ (Fintype.card ι) * ∑ h ∈ H, chi (q h + q 0) := gauss_square_identity_fintype q L hpol
    _ ≤ (2 : ℤ) ^ (Fintype.card ι) * (H.card : ℤ) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (2 : ℤ) ^ ((Fintype.card ι) + d) := by
      rw [hHcard, Nat.cast_pow, Nat.cast_ofNat, ← pow_add]
    _ = (2 : ℤ) ^ (2 * (Fintype.card ι) - Q.rank) := by congr 1; omega

lemma gauss_bound_fintype {ι : Type*} [Fintype ι] [DecidableEq ι] (q : (ι → F2) → F2)
    (Q : Matrix (ι) (ι) F2)
    (hpol : ∀ h t, polar q h t = dotProduct (Q.mulVec h) t) :
    |∑ x : ι → F2, chi (q x)| ≤ (2 : ℤ) ^ ((Fintype.card ι) - Q.rank / 2) := by
  have hsq := gauss_square_bound_fintype q Q hpol
  have hr := Matrix.rank_le_card_width Q
  have he : 2 * (Fintype.card ι) - Q.rank ≤ ((Fintype.card ι) - Q.rank / 2) * 2 := by omega
  have hp : (2 : ℤ) ^ (2 * (Fintype.card ι) - Q.rank) ≤ (2 : ℤ) ^ (((Fintype.card ι) - Q.rank / 2) * 2) :=
    pow_le_pow_right₀ (by norm_num) he
  rw [pow_mul] at hp
  exact abs_le_of_sq_le_sq (hsq.trans hp) (by positivity)

lemma gauss_bound_of_rank_ge_fintype {ι : Type*} [Fintype ι] [DecidableEq ι] {w : ℕ} (q : (ι → F2) → F2)
    (Q : Matrix (ι) (ι) F2)
    (hpol : ∀ h t, polar q h t = dotProduct (Q.mulVec h) t)
    (hrank : 2 * w ≤ Q.rank) :
    |∑ x : ι → F2, chi (q x)| ≤ (2 : ℤ) ^ ((Fintype.card ι) - w) := by
  apply (gauss_bound_fintype q Q hpol).trans
  apply pow_le_pow_right₀ (by norm_num)
  omega

lemma polar_of_quad {ι : Type*} [Fintype ι] (b : F2) (a : ι → F2) (M : ι → ι → F2)
    (q : (ι → F2) → F2)
    (hq : ∀ x, q x = b + dotProduct a x + ∑ i, ∑ j, M i j * x i * x j) (h t : ι → F2) :
    polar q h t = ∑ i, ∑ j, (M i j + M j i) * h i * t j := by
  unfold polar
  rw [hq (h + t), hq h, hq t, hq 0]
  have h0 : dotProduct a (0 : ι → F2) = 0 := dotProduct_zero a
  have hm0 : (∑ i : ι, ∑ j : ι, M i j * (0 : ι → F2) i * (0 : ι → F2) j) = 0 := by simp
  rw [h0, hm0, dotProduct_add]
  have hba : (b + (dotProduct a h + dotProduct a t) +
      ∑ i, ∑ j, M i j * (h + t) i * (h + t) j) +
      (b + dotProduct a h + ∑ i, ∑ j, M i j * h i * h j) +
      (b + dotProduct a t + ∑ i, ∑ j, M i j * t i * t j) + (b + 0 + 0) =
      ((∑ i, ∑ j, M i j * (h + t) i * (h + t) j) +
        (∑ i, ∑ j, M i j * h i * h j) +
        (∑ i, ∑ j, M i j * t i * t j)) := by
    have hbb : b + b = 0 := f2_add_self b
    have hdh : dotProduct a h + dotProduct a h = 0 := f2_add_self _
    have hdt : dotProduct a t + dotProduct a t = 0 := f2_add_self _
    calc _ = (b + b) + (b + b) + (dotProduct a h + dotProduct a h) +
          (dotProduct a t + dotProduct a t) +
          ((∑ i, ∑ j, M i j * (h + t) i * (h + t) j) +
            (∑ i, ∑ j, M i j * h i * h j) +
            (∑ i, ∑ j, M i j * t i * t j)) := by ring
      _ = _ := by rw [hbb, hdh, hdt]; ring
  rw [hba]
  have hterm : ∀ i j : ι,
      M i j * (h + t) i * (h + t) j + M i j * h i * h j + M i j * t i * t j =
      M i j * h i * t j + M i j * t i * h j := by
    intro i j
    simp only [Pi.add_apply]
    have h1 : M i j * h i * h j + M i j * h i * h j = 0 := f2_add_self _
    have h2 : M i j * t i * t j + M i j * t i * t j = 0 := f2_add_self _
    calc M i j * (h i + t i) * (h j + t j) + M i j * h i * h j + M i j * t i * t j
        = (M i j * h i * h j + M i j * h i * h j) +
          (M i j * t i * t j + M i j * t i * t j) +
          (M i j * h i * t j + M i j * t i * h j) := by ring
      _ = M i j * h i * t j + M i j * t i * h j := by rw [h1, h2]; ring
  have hcomb : (∑ i, ∑ j, M i j * (h + t) i * (h + t) j) +
      (∑ i, ∑ j, M i j * h i * h j) + (∑ i, ∑ j, M i j * t i * t j) =
      ∑ i, ∑ j, (M i j * h i * t j + M i j * t i * h j) := by
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hterm i j
  rw [hcomb]
  simp only [Finset.sum_add_distrib]
  have hswap : (∑ i, ∑ j, M i j * t i * h j) = ∑ i, ∑ j, M j i * h i * t j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hswap, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => by ring

lemma quadratic_polar_matrix {ι : Type*} [Fintype ι]
    (b : F2) (a : ι → F2) (M : Matrix ι ι F2) (q : (ι → F2) → F2)
    (hq : ∀ x, q x = b + dotProduct a x + ∑ i, ∑ j, M i j * x i * x j)
    (h t : ι → F2) :
    polar q h t = dotProduct ((M + M.transpose).mulVec h) t := by
  classical
  rw [polar_of_quad b a M q hq]
  simp only [Matrix.mulVec, dotProduct, Matrix.add_apply, Matrix.transpose_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

lemma quadratic_gauss_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : F2) (a : ι → F2) (M : Matrix ι ι F2) (q : (ι → F2) → F2)
    (hq : ∀ x, q x = b + dotProduct a x + ∑ i, ∑ j, M i j * x i * x j) :
    |∑ x : ι → F2, chi (q x)| ≤
      (2 : ℤ) ^ (Fintype.card ι - (M + M.transpose).rank / 2) := by
  apply gauss_bound_fintype q (M + M.transpose)
  exact quadratic_polar_matrix b a M q hq

lemma quadratic_gauss_bound_of_rank_ge {ι : Type*} [Fintype ι] [DecidableEq ι]
    {w : ℕ} (b : F2) (a : ι → F2) (M : Matrix ι ι F2) (q : (ι → F2) → F2)
    (hq : ∀ x, q x = b + dotProduct a x + ∑ i, ∑ j, M i j * x i * x j)
    (hrank : 2 * w ≤ (M + M.transpose).rank) :
    |∑ x : ι → F2, chi (q x)| ≤ (2 : ℤ) ^ (Fintype.card ι - w) := by
  exact gauss_bound_of_rank_ge_fintype q (M + M.transpose)
    (quadratic_polar_matrix b a M q hq) hrank

lemma gauss_natAbs_bound_fintype {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : (ι → F2) → F2) (Q : Matrix ι ι F2)
    (hpol : ∀ h t, polar q h t = dotProduct (Q.mulVec h) t) :
    (∑ x : ι → F2, chi (q x)).natAbs ≤ 2 ^ (Fintype.card ι - Q.rank / 2) := by
  have h := gauss_bound_fintype q Q hpol
  have hcast : ((∑ x : ι → F2, chi (q x)).natAbs : ℤ) ≤
      ((2 ^ (Fintype.card ι - Q.rank / 2) : ℕ) : ℤ) := by
    simpa only [Int.natCast_natAbs, Nat.cast_pow, Nat.cast_ofNat] using h
  exact_mod_cast hcast

lemma gauss_natAbs_bound_of_rank_ge_fintype
    {ι : Type*} [Fintype ι] [DecidableEq ι] {w : ℕ}
    (q : (ι → F2) → F2) (Q : Matrix ι ι F2)
    (hpol : ∀ h t, polar q h t = dotProduct (Q.mulVec h) t)
    (hrank : 2 * w ≤ Q.rank) :
    (∑ x : ι → F2, chi (q x)).natAbs ≤ 2 ^ (Fintype.card ι - w) := by
  have h := gauss_bound_of_rank_ge_fintype q Q hpol hrank
  have hcast : ((∑ x : ι → F2, chi (q x)).natAbs : ℤ) ≤
      ((2 ^ (Fintype.card ι - w) : ℕ) : ℤ) := by
    simpa only [Int.natCast_natAbs, Nat.cast_pow, Nat.cast_ofNat] using h
  exact_mod_cast hcast

end Gauss
section h5_part_11

end h5_part_11

section h5_part_12

end h5_part_12
section h5_part_13

end h5_part_13

section h5_part_14

open Classical

set_option maxHeartbeats 800000 in
lemma h5_gauss_family_plane_bound {k M : ℕ} {I : Type*} [Fintype I]
    (U : Submodule (ZMod 2) (Fin k → ZMod 2))
    (L : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin M → ZMod 2))
    (a b : U)
    (R : I → U → ((Fin M × Bool) → ZMod 2) → ZMod 2)
    (Q : I → Matrix (Fin M × Bool) (Fin M × Bool) (ZMod 2))
    (hs : ∀ i, (Q i).transpose = Q i) (hd : ∀ i p, Q i p p = 0)
    (hpol : ∀ i u x y, Gauss.polar (R i u) x y =
      dotProduct ((Q i + h5PairDiagonal (L u)).mulVec x) y) :
    4 * |∑ i, ∑ u : U, ∑ x : (Fin M × Bool) → ZMod 2, Gauss.chi (R i u x)| ≤
      (Fintype.card I : ℤ) * Fintype.card U * 2^M *
        (2^M + 2^(M-h5BitWeight (L a)) + 2^(M-h5BitWeight (L b)) +
          2^(M-h5BitWeight (L ((a:Fin k→ZMod 2)+b)))) := by
  classical
  let W : ℤ := ∑ u : U, (2:ℤ)^(M-h5BitWeight (L u))
  have hrow (i : I) :
      |∑ u : U, ∑ x : (Fin M × Bool) → ZMod 2, Gauss.chi (R i u x)| ≤ 2^M * W := by
    calc
      |∑ u : U, ∑ x : (Fin M × Bool) → ZMod 2, Gauss.chi (R i u x)| ≤
          ∑ u : U, |∑ x : (Fin M × Bool) → ZMod 2, Gauss.chi (R i u x)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ u : U, (2:ℤ)^(2*M-(Q i+h5PairDiagonal (L u)).rank/2) := by
        apply Finset.sum_le_sum
        intro u hu
        simpa only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Nat.mul_comm] using
          Gauss.gauss_bound_fintype (R i u) (Q i+h5PairDiagonal (L u)) (hpol i u)
      _ ≤ 2^M * W := h5_gaussian_rank_sum_le (Q i) (hs i) (hd i) U L
  have hall :
      |∑ i, ∑ u : U, ∑ x : (Fin M × Bool) → ZMod 2, Gauss.chi (R i u x)| ≤
        (Fintype.card I : ℤ) * (2^M * W) := by
    calc
      |∑ i, ∑ u : U, ∑ x : (Fin M × Bool) → ZMod 2, Gauss.chi (R i u x)| ≤
          ∑ i, |∑ u : U, ∑ x : (Fin M × Bool) → ZMod 2, Gauss.chi (R i u x)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : I, (2:ℤ)^M * W := Finset.sum_le_sum (fun i _ => hrow i)
      _ = (Fintype.card I : ℤ) * (2^M * W) := by simp
  have havg := h5_subgroup_average_plane U L a b
  dsimp only at havg
  simp only [Fourier.wt_eq_nonzero] at havg
  change 4 * W ≤ (Fintype.card U : ℤ) *
      ((2:ℤ)^(M-h5BitWeight (L 0)) + 2^(M-h5BitWeight (L a)) +
        2^(M-h5BitWeight (L b)) + 2^(M-h5BitWeight (L ((a:Fin k→ZMod 2)+b)))) at havg
  have hzero : h5BitWeight (L 0) = 0 := by simp [h5BitWeight]
  rw [hzero, Nat.sub_zero] at havg
  calc
    4 * |∑ i, ∑ u : U, ∑ x : (Fin M × Bool) → ZMod 2, Gauss.chi (R i u x)| ≤
        4 * ((Fintype.card I : ℤ) * (2^M * W)) := mul_le_mul_of_nonneg_left hall (by norm_num)
    _ = ((Fintype.card I : ℤ) * 2^M) * (4*W) := by ring
    _ ≤ ((Fintype.card I : ℤ) * 2^M) * ((Fintype.card U : ℤ) *
        (2^M + 2^(M-h5BitWeight (L a)) + 2^(M-h5BitWeight (L b)) +
          2^(M-h5BitWeight (L ((a:Fin k→ZMod 2)+b))))) :=
      mul_le_mul_of_nonneg_left havg (by positivity)
    _ = _ := by ring

end h5_part_14

section h5_part_15

open Classical

lemma h5_bit_weight_le_length {m : ℕ} (c : Fin m → ZMod 2) : h5BitWeight c ≤ m :=
  (Finset.card_filter_le _ _).trans_eq (Finset.card_fin m)

lemma h5_weight_power_scale (m M w : ℕ) (hM : M ≤ m) (hw : w ≤ M) :
    (2:ℤ)^m * 2^(M-w) = (2:ℤ)^M * 2^(m-w) := by
  rw [← pow_add, ← pow_add]
  congr 1
  omega

set_option maxHeartbeats 1000000 in
lemma h5_full_flat_family_bound {k m M b : ℕ} {I : Type*} [Fintype I]
    (U : Submodule (ZMod 2) (Fin k → ZMod 2))
    (C : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2))
    (L : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin M → ZMod 2))
    (a c : U) (plane : ℕ) (hM : M ≤ m)
    (hweight : ∀ u : U, h5BitWeight (L u) = h5BitWeight (C u))
    (hmass : (2:ℤ)^m + 2^(m-h5BitWeight (C a)) + 2^(m-h5BitWeight (C c)) +
      2^(m-h5BitWeight (C ((a:Fin k→ZMod 2)+c))) ≤ plane)
    (R : I → U → ((Fin M × Bool) → ZMod 2) → ZMod 2)
    (Q : I → Matrix (Fin M × Bool) (Fin M × Bool) (ZMod 2))
    (hs : ∀ i, (Q i).transpose = Q i) (hd : ∀ i p, Q i p p = 0)
    (hpol : ∀ i u x y, Gauss.polar (R i u) x y =
      dotProduct ((Q i + h5PairDiagonal (L u)).mulVec x) y)
    (hcard : Fintype.card I * Fintype.card U * 2^(2*M) = 2^b) :
    2^(m+2) * (∑ i, ∑ u : U, ∑ x : (Fin M × Bool) → ZMod 2,
      Gauss.chi (R i u x)).natAbs ≤ 2^b * plane := by
  let S : ℤ := ∑ i, ∑ u : U, ∑ x : (Fin M × Bool) → ZMod 2, Gauss.chi (R i u x)
  let massM : ℤ := 2^M + 2^(M-h5BitWeight (L a)) + 2^(M-h5BitWeight (L c)) +
    2^(M-h5BitWeight (L ((a:Fin k→ZMod 2)+c)))
  let massm : ℤ := 2^m + 2^(m-h5BitWeight (C a)) + 2^(m-h5BitWeight (C c)) +
    2^(m-h5BitWeight (C ((a:Fin k→ZMod 2)+c)))
  have h4 : 4*|S| ≤ (Fintype.card I : ℤ) * Fintype.card U * 2^M * massM :=
    h5_gauss_family_plane_bound U L a c R Q hs hd hpol
  have hwac : h5BitWeight (L ((a:Fin k→ZMod 2)+c)) =
      h5BitWeight (C ((a:Fin k→ZMod 2)+c)) := hweight (a+c)
  have hscale : (2:ℤ)^m * massM = (2:ℤ)^M * massm := by
    dsimp only [massM, massm]
    simp only [mul_add]
    rw [h5_weight_power_scale m M _ hM (h5_bit_weight_le_length (L a)),
      h5_weight_power_scale m M _ hM (h5_bit_weight_le_length (L c)),
      h5_weight_power_scale m M _ hM (h5_bit_weight_le_length (L ((a:Fin k→ZMod 2)+c))),
      hweight a, hweight c, hwac]
    ring
  have hc : (Fintype.card I : ℤ) * Fintype.card U * (2:ℤ)^(2*M) = (2:ℤ)^b := by
    exact_mod_cast hcard
  have hz : (2:ℤ)^(m+2) * |S| ≤ (2:ℤ)^b * plane := by
    calc
      (2:ℤ)^(m+2) * |S| = (2:ℤ)^m * (4*|S|) := by rw [pow_add]; norm_num; ring
      _ ≤ (2:ℤ)^m * ((Fintype.card I : ℤ)*Fintype.card U*2^M*massM) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = (Fintype.card I : ℤ)*Fintype.card U*2^M*((2:ℤ)^m*massM) := by ring
      _ = (Fintype.card I : ℤ)*Fintype.card U*2^M*((2:ℤ)^M*massm) := by rw [hscale]
      _ = ((Fintype.card I : ℤ)*Fintype.card U*(2:ℤ)^(2*M))*massm := by
        rw [two_mul, pow_add]
        ring
      _ ≤ ((Fintype.card I : ℤ)*Fintype.card U*(2:ℤ)^(2*M))*plane :=
        mul_le_mul_of_nonneg_left hmass (by positivity)
      _ = (2:ℤ)^b * plane := by rw [hc]
  rw [← Int.natCast_natAbs] at hz
  exact_mod_cast hz

set_option maxHeartbeats 1000000 in
lemma h5_full_flat_bound_of_param {k m M b : ℕ} {I : Type*} [Fintype I]
    (U : Submodule (ZMod 2) (Fin k → ZMod 2))
    (C : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2))
    (L : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin M → ZMod 2))
    (a c : U) (plane : ℕ) (hM : M ≤ m)
    (hweight : ∀ u : U, h5BitWeight (L u) = h5BitWeight (C u))
    (hmass : (2:ℤ)^m + 2^(m-h5BitWeight (C a)) + 2^(m-h5BitWeight (C c)) +
      2^(m-h5BitWeight (C ((a:Fin k→ZMod 2)+c))) ≤ plane)
    (phase : (Fin b → ZMod 2) → ZMod 2)
    (e : (Fin b → ZMod 2) ≃ (I × (U × ((Fin M × Bool) → ZMod 2))))
    (Q : I → Matrix (Fin M × Bool) (Fin M × Bool) (ZMod 2))
    (hs : ∀ i, (Q i).transpose = Q i) (hd : ∀ i p, Q i p p = 0)
    (hpol : ∀ i u x y, Gauss.polar (fun z => phase (e.symm (i,u,z))) x y =
      dotProduct ((Q i + h5PairDiagonal (L u)).mulVec x) y) :
    2^(m+2) * (∑ z : Fin b → ZMod 2, Gauss.chi (phase z)).natAbs ≤ 2^b * plane := by
  have hcard : Fintype.card I * Fintype.card U * 2^(2*M) = 2^b := by
    have h := Fintype.card_congr e
    simpa only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
      ZMod.card, Nat.mul_assoc, Nat.mul_comm M 2] using h.symm
  have hsum : (∑ z : Fin b → ZMod 2, Gauss.chi (phase z)) =
      ∑ i, ∑ u : U, ∑ x : (Fin M × Bool) → ZMod 2, Gauss.chi (phase (e.symm (i,u,x))) := by
    rw [← e.symm.sum_comp]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Fintype.sum_prod_type]
  rw [hsum]
  exact h5_full_flat_family_bound U C L a c plane hM hweight hmass
    (fun i u x => phase (e.symm (i,u,x))) Q hs hd hpol hcard

end h5_part_15

section h5_part_16

open Classical

lemma h5_polar_symmetric {J : Type*} (q : (J → ZMod 2) → ZMod 2) (x y : J → ZMod 2) :
    Gauss.polar q x y = Gauss.polar q y x := by
  unfold Gauss.polar
  rw [add_comm x y]
  ring

lemma h5_polar_self {J : Type*} (q : (J → ZMod 2) → ZMod 2) (x : J → ZMod 2) :
    Gauss.polar q x x = 0 := by
  unfold Gauss.polar
  rw [Gauss.f2_vec_add_self]
  calc
    q 0 + q x + q x + q 0 = (q 0+q 0)+(q x+q x) := by ring
    _ = 0 := by rw [Gauss.f2_add_self, Gauss.f2_add_self, add_zero]

lemma h5_polar_matrix_alternating {J : Type*} [Fintype J]
    (q : (J → ZMod 2) → ZMod 2) (Q : Matrix J J (ZMod 2))
    (hpol : ∀ x y, Gauss.polar q x y = dotProduct (Q.mulVec x) y) :
    Q.transpose = Q ∧ ∀ j, Q j j = 0 := by
  classical
  constructor
  · ext i j
    have h := h5_polar_symmetric q (Pi.single i 1) (Pi.single j 1)
    rw [hpol, hpol] at h
    simpa using h
  · intro i
    have h := hpol (Pi.single i 1) (Pi.single i 1)
    rw [h5_polar_self] at h
    simpa using h.symm

lemma h5_pair_diagonal_zero {M : ℕ} :
    h5PairDiagonal (0 : Fin M → ZMod 2) = 0 := by
  ext p q
  simp [h5_pair_diagonal_apply]

set_option maxHeartbeats 1000000 in
lemma h5_full_flat_bound_of_polar_param {k m M b : ℕ} {I : Type*} [Fintype I]
    (U : Submodule (ZMod 2) (Fin k → ZMod 2))
    (C : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2))
    (L : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin M → ZMod 2))
    (a c : U) (plane : ℕ) (hM : M ≤ m)
    (hweight : ∀ u : U, h5BitWeight (L u) = h5BitWeight (C u))
    (hmass : (2:ℤ)^m + 2^(m-h5BitWeight (C a)) + 2^(m-h5BitWeight (C c)) +
      2^(m-h5BitWeight (C ((a:Fin k→ZMod 2)+c))) ≤ plane)
    (phase : (Fin b → ZMod 2) → ZMod 2)
    (e : (Fin b → ZMod 2) ≃ (I × (U × ((Fin M × Bool) → ZMod 2))))
    (Q : I → Matrix (Fin M × Bool) (Fin M × Bool) (ZMod 2))
    (hpol : ∀ i u x y, Gauss.polar (fun z => phase (e.symm (i,u,z))) x y =
      dotProduct ((Q i + h5PairDiagonal (L u)).mulVec x) y) :
    2^(m+2) * (∑ z : Fin b → ZMod 2, Gauss.chi (phase z)).natAbs ≤ 2^b * plane := by
  have hQ (i : I) : (Q i).transpose = Q i ∧ ∀ p, Q i p p = 0 := by
    apply h5_polar_matrix_alternating (fun z => phase (e.symm (i,0,z))) (Q i)
    intro x y
    simpa only [Submodule.coe_zero, map_zero, h5_pair_diagonal_zero, add_zero] using hpol i 0 x y
  exact h5_full_flat_bound_of_param U C L a c plane hM hweight hmass phase e Q
    (fun i => (hQ i).1) (fun i => (hQ i).2) hpol

end h5_part_16

section h5_part_17

open Classical

lemma h5_code_mass_le_sup {k m : ℕ}
    (C : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2))
    (a c : Fin k → ZMod 2) (ha : a ≠ 0) (hc : c ≠ 0) (hac : a ≠ c) :
    (2:ℤ)^m + 2^(m-h5BitWeight (C a)) + 2^(m-h5BitWeight (C c)) +
      2^(m-h5BitWeight (C (a+c))) ≤
    ((Finset.univ : Finset ((Fin k → ZMod 2) × (Fin k → ZMod 2))).sup
      (fun w => if w.1 ≠ 0 ∧ w.2 ≠ 0 ∧ w.1 ≠ w.2 then
        2^m + 2^(m-h5BitWeight (C w.1)) + 2^(m-h5BitWeight (C w.2)) +
          2^(m-h5BitWeight (C (w.1+w.2))) else 0) : ℕ) := by
  have h := Finset.le_sup (f := fun w : (Fin k → ZMod 2) × (Fin k → ZMod 2) =>
    if w.1 ≠ 0 ∧ w.2 ≠ 0 ∧ w.1 ≠ w.2 then
      2^m + 2^(m-h5BitWeight (C w.1)) + 2^(m-h5BitWeight (C w.2)) +
        2^(m-h5BitWeight (C (w.1+w.2))) else (0:ℕ)) (Finset.mem_univ (a,c))
  dsimp only at h
  rw [ite_eq_left ⟨ha, hc, hac⟩] at h
  exact_mod_cast h

set_option maxHeartbeats 1000000 in
lemma h5_full_flat_sup_bound_of_param {k m M b : ℕ} {I : Type*} [Fintype I]
    (U : Submodule (ZMod 2) (Fin k → ZMod 2))
    (C : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2))
    (L : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin M → ZMod 2))
    (a c : U) (ha : (a:Fin k→ZMod 2) ≠ 0) (hc : (c:Fin k→ZMod 2) ≠ 0)
    (hac : (a:Fin k→ZMod 2) ≠ c) (hM : M ≤ m)
    (hweight : ∀ u : U, h5BitWeight (L u) = h5BitWeight (C u))
    (phase : (Fin b → ZMod 2) → ZMod 2)
    (e : (Fin b → ZMod 2) ≃ (I × (U × ((Fin M × Bool) → ZMod 2))))
    (Q : I → Matrix (Fin M × Bool) (Fin M × Bool) (ZMod 2))
    (hpol : ∀ i u x y, Gauss.polar (fun z => phase (e.symm (i,u,z))) x y =
      dotProduct ((Q i + h5PairDiagonal (L u)).mulVec x) y) :
    let plane := (Finset.univ : Finset ((Fin k → ZMod 2) × (Fin k → ZMod 2))).sup
      (fun w => if w.1 ≠ 0 ∧ w.2 ≠ 0 ∧ w.1 ≠ w.2 then
        2^m + 2^(m-h5BitWeight (C w.1)) + 2^(m-h5BitWeight (C w.2)) +
          2^(m-h5BitWeight (C (w.1+w.2))) else 0)
    2^(m+2) * (∑ z : Fin b → ZMod 2, Gauss.chi (phase z)).natAbs ≤ 2^b * plane := by
  dsimp only
  exact h5_full_flat_bound_of_polar_param U C L a c _ hM hweight
    (h5_code_mass_le_sup C a c ha hc hac) phase e Q hpol

end h5_part_17

section h5_part_18

open Classical

lemma h5_injective_linear_param {K V E : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup E] [Module K E]
    (f : V →ₗ[K] E) (hf : Function.Injective f) :
    ∃ (W : Submodule K E) (e : E ≃ₗ[K] W × V),
      ∀ w v, e.symm (w,v) = (w:E)+f v := by
  obtain ⟨g,hgf⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hf)
  have hg (v : V) : g (f v) = v := congrArg (fun T : V →ₗ[K] V => T v) hgf
  let W := LinearMap.ker g
  let F : W × V →ₗ[K] E :=
    { toFun := fun p => (p.1:E)+f p.2
      map_add' := by intro p q; simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, map_add]; abel
      map_smul' := by intro c p; simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul,
        RingHom.id_apply, map_smul, smul_add] }
  have hgw (w : W) : g (w:E) = 0 := w.property
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨w,v⟩ ⟨w',v'⟩ heq
      have hv : v=v' := by
        have h := congrArg g heq
        change g ((w:E)+f v) = g ((w':E)+f v') at h
        simpa only [map_add, hgw, hg, zero_add] using h
      subst v'
      have hw : w=w' := by
        apply Subtype.ext
        exact add_right_cancel heq
      subst w'
      rfl
    · intro x
      let w : W := ⟨x-f (g x), by change g (x-f (g x))=0; rw [map_sub, hg, sub_self]⟩
      refine ⟨(w,g x),?_⟩
      change x-f (g x)+f (g x)=x
      exact sub_add_cancel _ _
  let e := LinearEquiv.ofBijective F hF
  refine ⟨W,e.symm,?_⟩
  intro w v
  rfl

lemma h5_selector_data_injective {K S E X : Type*} [Field K]
    [AddCommGroup S] [Module K S] [AddCommGroup E] [Module K E]
    [AddCommGroup X] [Module K X]
    (U : Submodule K S) (sel : E →ₗ[K] S)
    (lift : U →ₗ[K] E) (data : X →ₗ[K] E)
    (hlift : ∀ u : U, sel (lift u) = u)
    (hdata : ∀ x, sel (data x) = 0) (hinj : Function.Injective data) :
    Function.Injective (fun p : U × X => lift p.1 + data p.2) := by
  rintro ⟨u,x⟩ ⟨v,y⟩ h
  have huv : u=v := by
    apply Subtype.ext
    have hs := congrArg sel h
    simpa only [map_add, hlift, hdata, add_zero] using hs
  subst v
  have hxy : x=y := hinj (add_left_cancel h)
  subst y
  rfl

end h5_part_18

section h5_part_19

open Classical

lemma h5_quad_add_eq {J : Type*} (q : (J → ZMod 2) → ZMod 2) (x y : J → ZMod 2) :
    q (x+y) = q x+q y+q 0+Gauss.polar q x y := by
  unfold Gauss.polar
  have hx := Gauss.f2_add_self (q x)
  have hy := Gauss.f2_add_self (q y)
  have h0 := Gauss.f2_add_self (q 0)
  calc
    q (x+y) = q (x+y)+(q x+q x)+(q y+q y)+(q 0+q 0) := by rw [hx,hy,h0]; ring
    _ = _ := by ring

lemma h5_polar_translate {J : Type*} [Fintype J]
    (q : (J → ZMod 2) → ZMod 2) (Q : Matrix J J (ZMod 2))
    (hpol : ∀ x y, Gauss.polar q x y = dotProduct (Q.mulVec x) y)
    (a x y : J → ZMod 2) :
    Gauss.polar (fun z => q (a+z)) x y = Gauss.polar q x y := by
  unfold Gauss.polar
  simp only [add_zero]
  rw [h5_quad_add_eq q a (x+y), h5_quad_add_eq q a x, h5_quad_add_eq q a y]
  simp only [hpol, dotProduct_add]
  ring_nf
  simp only [show (2:ZMod 2)=0 by decide, show (3:ZMod 2)=1 by decide,
    show (4:ZMod 2)=0 by decide, mul_zero, mul_one, add_zero, zero_add]

lemma h5_polar_affine_product {J : Type*}
    (f g : (J → ZMod 2) →ₗ[ZMod 2] ZMod 2) (a b : ZMod 2) (x y : J → ZMod 2) :
    Gauss.polar (fun z => (a+f z)*(b+g z)) x y = f x*g y+f y*g x := by
  simp only [Gauss.polar, map_add, map_zero, add_zero]
  ring_nf
  simp only [show (2:ZMod 2)=0 by decide, show (4:ZMod 2)=0 by decide, mul_zero, add_zero, zero_add]

end h5_part_19

section h5_part_20

open Classical

lemma h5_polar_add {J : Type*} (f g : (J → ZMod 2) → ZMod 2) (x y : J → ZMod 2) :
    Gauss.polar (fun z => f z+g z) x y = Gauss.polar f x y+Gauss.polar g x y := by
  unfold Gauss.polar
  ring

lemma h5_polar_const {J : Type*} (c : ZMod 2) (x y : J → ZMod 2) :
    Gauss.polar (fun _ => c) x y = 0 := by
  unfold Gauss.polar
  rw [Gauss.f2_add_self, zero_add, Gauss.f2_add_self]

lemma h5_polar_sum {I J : Type*} [Fintype I]
    (f : I → (J → ZMod 2) → ZMod 2) (x y : J → ZMod 2) :
    Gauss.polar (fun z => ∑ i, f i z) x y = ∑ i, Gauss.polar (f i) x y := by
  simp only [Gauss.polar, ← Finset.sum_add_distrib]

lemma h5_polar_const_mul {J : Type*} (c : ZMod 2) (f : (J → ZMod 2) → ZMod 2)
    (x y : J → ZMod 2) :
    Gauss.polar (fun z => c*f z) x y = c*Gauss.polar f x y := by
  unfold Gauss.polar
  ring

lemma h5_polar_comp_affine {I J : Type*} [Fintype I]
    (q : (I → ZMod 2) → ZMod 2) (Q : Matrix I I (ZMod 2))
    (hpol : ∀ x y, Gauss.polar q x y = dotProduct (Q.mulVec x) y)
    (T : (J → ZMod 2) →ₗ[ZMod 2] (I → ZMod 2))
    (a : I → ZMod 2) (x y : J → ZMod 2) :
    Gauss.polar (fun z => q (a+T z)) x y = dotProduct (Q.mulVec (T x)) (T y) := by
  calc
    Gauss.polar (fun z => q (a+T z)) x y =
        Gauss.polar (fun z => q (a+z)) (T x) (T y) := by
      simp only [Gauss.polar, map_add, map_zero]
    _ = Gauss.polar q (T x) (T y) := h5_polar_translate q Q hpol a (T x) (T y)
    _ = _ := hpol _ _

lemma h5_weighted_affine_pair_polar {m : ℕ} {J : Type*}
    (c a b : Fin m → ZMod 2)
    (f g : Fin m → (J → ZMod 2) →ₗ[ZMod 2] ZMod 2) (x y : J → ZMod 2) :
    Gauss.polar (fun z => ∑ i, c i*((a i+f i z)*(b i+g i z))) x y =
      ∑ i, c i*(f i x*g i y+f i y*g i x) := by
  rw [h5_polar_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [h5_polar_const_mul, h5_polar_affine_product]

lemma h5_pair_diagonal_bilinear {M : ℕ} (c : Fin M → ZMod 2)
    (x y : (Fin M × Bool) → ZMod 2) :
    dotProduct ((h5PairDiagonal c).mulVec x) y =
      ∑ i, c i*(x (i,false)*y (i,true)+x (i,true)*y (i,false)) := by
  rw [h5_pair_diagonal_eq_toggle_pairs]
  simp only [dotProduct, Fintype.sum_prod_type, h5_toggle_pairs_mulVec, Fintype.sum_bool,
    Bool.not_true, Bool.not_false]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma h5_retained_pair_bilinear {m M : ℕ} (e : Fin M ↪ Fin m)
    (c : Fin m → ZMod 2) (hzero : ∀ i, i ∉ Set.range e → c i=0)
    (f g : Fin m → ((Fin M × Bool) → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (hf : ∀ i x, f (e i) x = x (i,false)) (hg : ∀ i x, g (e i) x = x (i,true))
    (x y : (Fin M × Bool) → ZMod 2) :
    (∑ i, c i*(f i x*g i y+f i y*g i x)) =
      dotProduct ((h5PairDiagonal (fun i => c (e i))).mulVec x) y := by
  have hsum := Fintype.sum_of_injective e e.injective
    (fun i => c (e i)*(f (e i) x*g (e i) y+f (e i) y*g (e i) x))
    (fun i => c i*(f i x*g i y+f i y*g i x))
    (fun i hi => by rw [hzero i hi, zero_mul]) (fun i => rfl)
  rw [← hsum, h5_pair_diagonal_bilinear]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hf, hf, hg, hg]
  ring

end h5_part_20

section h5_part_21

open Classical

lemma h5_linear_form_coordinates {J : Type*} [Fintype J] [DecidableEq J]
    (f : (J → ZMod 2) →ₗ[ZMod 2] ZMod 2) (x : J → ZMod 2) :
    f x = dotProduct (fun j => f (Pi.single j 1)) x := by
  have hx : x = ∑ j, x j • Pi.single j (1 : ZMod 2) := by
    ext i
    simp [Pi.single_apply]
  calc
    f x = f (∑ j, x j • Pi.single j (1:ZMod 2)) := congrArg f hx
    _ = dotProduct (fun j => f (Pi.single j 1)) x := by
      rw [map_sum]
      simp only [map_smul, smul_eq_mul, dotProduct]
      apply Finset.sum_congr rfl
      intro j hj
      ring

noncomputable def h5ProductPolarMap {J : Type*} [Fintype J] [DecidableEq J]
    (f g : (J → ZMod 2) →ₗ[ZMod 2] ZMod 2) : (J → ZMod 2) →ₗ[ZMod 2] (J → ZMod 2) :=
  f.smulRight (fun j => g (Pi.single j 1)) + g.smulRight (fun j => f (Pi.single j 1))

lemma h5_product_polar_map_dot {J : Type*} [Fintype J] [DecidableEq J]
    (f g : (J → ZMod 2) →ₗ[ZMod 2] ZMod 2) (x y : J → ZMod 2) :
    dotProduct (h5ProductPolarMap f g x) y = f x*g y+f y*g x := by
  change dotProduct (f x • (fun j => g (Pi.single j 1)) + g x • (fun j => f (Pi.single j 1))) y = _
  rw [add_dotProduct, smul_dotProduct, smul_dotProduct,
    ← h5_linear_form_coordinates g y, ← h5_linear_form_coordinates f y]
  simp only [smul_eq_mul]
  ring

lemma h5_polar_comp_affine_matrix {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (q : (I → ZMod 2) → ZMod 2) (Q : Matrix I I (ZMod 2))
    (hpol : ∀ x y, Gauss.polar q x y = dotProduct (Q.mulVec x) y)
    (T : (J → ZMod 2) →ₗ[ZMod 2] (I → ZMod 2))
    (a : I → ZMod 2) (x y : J → ZMod 2) :
    Gauss.polar (fun z => q (a+T z)) x y =
      dotProduct (((LinearMap.toMatrix' T).transpose * Q * LinearMap.toMatrix' T).mulVec x) y := by
  rw [h5_polar_comp_affine q Q hpol T a x y]
  rw [dotProduct_comm _ y]
  simp only [← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec]
  rw [Matrix.dotProduct_transpose_mulVec, LinearMap.toMatrix'_mulVec]

end h5_part_21

section h5_part_22

open Classical

lemma h5_weighted_affine_pair_matrix {m : ℕ} {J : Type*} [Fintype J] [DecidableEq J]
    (c a b : Fin m → ZMod 2) (h : ZMod 2)
    (f g : Fin m → (J → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (q : (J → ZMod 2) → ZMod 2) (Qq : Matrix J J (ZMod 2))
    (hq : ∀ x y, Gauss.polar q x y = dotProduct (Qq.mulVec x) y) :
    ∃ Q : Matrix J J (ZMod 2), ∀ x y,
      Gauss.polar (fun z => h+(∑ i, c i*((a i+f i z)*(b i+g i z)))+q z) x y =
        dotProduct (Q.mulVec x) y := by
  let L : (J → ZMod 2) →ₗ[ZMod 2] (J → ZMod 2) :=
    (∑ i, c i • h5ProductPolarMap (f i) (g i)) + Qq.mulVecLin
  refine ⟨LinearMap.toMatrix' L,?_⟩
  intro x y
  rw [h5_polar_add, h5_polar_add, h5_polar_const, zero_add,
    h5_weighted_affine_pair_polar, hq, LinearMap.toMatrix'_mulVec]
  simp only [L, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, add_dotProduct,
    sum_dotProduct, smul_dotProduct, h5_product_polar_map_dot, smul_eq_mul]
  rfl

set_option maxHeartbeats 800000 in
lemma h5_selector_family_polar {k m M : ℕ}
    (U : Submodule (ZMod 2) (Fin k → ZMod 2))
    (C : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2))
    (e : Fin M ↪ Fin m)
    (c0 : Fin m → ZMod 2) (h : U → ZMod 2) (a b : U → Fin m → ZMod 2)
    (f g : Fin m → ((Fin M × Bool) → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (q : U → ((Fin M × Bool) → ZMod 2) → ZMod 2)
    (Qq : Matrix (Fin M × Bool) (Fin M × Bool) (ZMod 2))
    (hq : ∀ u x y, Gauss.polar (q u) x y = dotProduct (Qq.mulVec x) y)
    (hsupport : ∀ u : U, ∀ j, j ∉ Set.range e → C u j=0)
    (hf : ∀ i x, f (e i) x = x (i,false)) (hg : ∀ i x, g (e i) x = x (i,true)) :
    ∃ Q : Matrix (Fin M × Bool) (Fin M × Bool) (ZMod 2), ∀ u x y,
      Gauss.polar (fun z => h u+(∑ i, (c0 i+C u i)*((a u i+f i z)*(b u i+g i z)))+q u z) x y =
        dotProduct ((Q+h5PairDiagonal (fun i => C u (e i))).mulVec x) y := by
  obtain ⟨Q,hQ⟩ := h5_weighted_affine_pair_matrix c0 (a 0) (b 0) (h 0) f g (q 0) Qq (hq 0)
  refine ⟨Q,?_⟩
  intro u x y
  have hbase : (∑ i, c0 i*(f i x*g i y+f i y*g i x)) + dotProduct (Qq.mulVec x) y =
      dotProduct (Q.mulVec x) y := by
    have hh := hQ x y
    rw [h5_polar_add, h5_polar_add, h5_polar_const, zero_add,
      h5_weighted_affine_pair_polar, hq] at hh
    exact hh
  have hret := h5_retained_pair_bilinear e (C u) (hsupport u) f g hf hg x y
  rw [h5_polar_add, h5_polar_add, h5_polar_const, zero_add,
    h5_weighted_affine_pair_polar, hq]
  simp only [add_mul, Finset.sum_add_distrib]
  rw [Matrix.add_mulVec, add_dotProduct, ← hbase, ← hret]
  ring

end h5_part_22


section h5_part_23

lemma h5_kernel_dimension {K U : Type*} [Field K] [AddCommGroup U] [Module K U]
    [FiniteDimensional K U] {J : Type*} [Fintype J] (f : U →ₗ[K] (J → K)) :
    Module.finrank K U ≤ Fintype.card J + Module.finrank K (LinearMap.ker f) := by
  have hdim := f.finrank_range_add_finrank_ker
  have hr := (LinearMap.range f).finrank_le
  have hj : Module.finrank K (J → K) = Fintype.card J := by simp
  rw [hj] at hr
  omega

lemma h5_kernel_nonzero {K U : Type*} [Field K] [AddCommGroup U] [Module K U]
    [FiniteDimensional K U] {J : Type*} [Fintype J] (f : U →ₗ[K] (J → K))
    (hsmall : Fintype.card J < Module.finrank K U) :
    ∃ a : U, a ≠ 0 ∧ f a = 0 := by
  have hker : LinearMap.ker f ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hsmall)
  obtain ⟨a, ha, hne⟩ := (LinearMap.ker f).ne_bot_iff.mp hker
  exact ⟨a, hne, ha⟩

lemma h5_kernel_two_dimensions {K U : Type*} [Field K] [AddCommGroup U] [Module K U]
    [FiniteDimensional K U] {J : Type*} [Fintype J] (f : U →ₗ[K] (J → K))
    (hsmall : Fintype.card J + 2 ≤ Module.finrank K U) :
    2 ≤ Module.finrank K (LinearMap.ker f) := by
  have h := h5_kernel_dimension f
  omega

lemma h5_deleted_coordinates_direction {k m : ℕ} (A : Fin m → Fin k → ZMod 2)
    (U : Submodule (ZMod 2) (Fin k → ZMod 2)) (J : Finset (Fin m))
    (hsmall : J.card < Module.finrank (ZMod 2) U) :
    ∃ a : Fin k → ZMod 2, a ∈ U ∧ a ≠ 0 ∧ ∀ j ∈ J, dotProduct (A j) a = 0 := by
  classical
  let f : U →ₗ[ZMod 2] (J → ZMod 2) :=
    { toFun := fun a j => dotProduct (A j) a
      map_add' := by intro x y; ext j; exact dotProduct_add _ _ _
      map_smul' := by intro c x; ext j; exact dotProduct_smul _ _ _ }
  have hs : Fintype.card J < Module.finrank (ZMod 2) U := by simpa using hsmall
  obtain ⟨a, hne, hzero⟩ := h5_kernel_nonzero f hs
  refine ⟨a, a.property, ?_, ?_⟩
  · intro h
    apply hne
    exact Subtype.ext h
  · intro j hj
    exact congrFun hzero ⟨j,hj⟩

lemma h5_two_vectors_of_dimension {K U : Type*} [Field K] [AddCommGroup U] [Module K U]
    [FiniteDimensional K U] (h : 2 ≤ Module.finrank K U) :
    ∃ a b : U, a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b := by
  let i : Fin (Module.finrank K U) := ⟨0,by omega⟩
  let j : Fin (Module.finrank K U) := ⟨1,by omega⟩
  let B := Module.finBasis K U
  refine ⟨B i,B j,B.ne_zero i,B.ne_zero j,?_⟩
  intro hab
  have hij := B.injective hab
  have hv := congrArg Fin.val hij
  change (0 : ℕ) = 1 at hv
  omega

lemma h5_kernel_two_vectors {K U : Type*} [Field K] [AddCommGroup U] [Module K U]
    [FiniteDimensional K U] {J : Type*} [Fintype J] (f : U →ₗ[K] (J → K))
    (hsmall : Fintype.card J + 2 ≤ Module.finrank K U) :
    ∃ a b : U, a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧ f a = 0 ∧ f b = 0 := by
  obtain ⟨a,b,ha,hb,hab⟩ := h5_two_vectors_of_dimension (h5_kernel_two_dimensions f hsmall)
  refine ⟨a,b,?_,?_,?_,a.property,b.property⟩
  · intro h
    exact ha (Subtype.ext h)
  · intro h
    exact hb (Subtype.ext h)
  · intro h
    exact hab (Subtype.ext h)

end h5_part_23

section h5_part_24

open Classical

lemma h5_weight_restrict_zero_outside {m t : ℕ}
    (e : Fin t ↪ Fin m) (a : Fin m → ZMod 2)
    (hzero : ∀ i, i ∉ Set.range e → a i = 0) :
    h5BitWeight (fun i => a (e i)) = h5BitWeight a := by
  classical
  unfold h5BitWeight
  apply Finset.card_bij (fun i _ => e i)
  · intro i hi
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi
  · intro i hi j hj hij
    exact e.injective hij
  · intro j hj
    have haj : a j ≠ 0 := (Finset.mem_filter.mp hj).2
    have hr : j ∈ Set.range e := by
      by_contra hn
      exact haj (hzero j hn)
    obtain ⟨i, rfl⟩ := hr
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, haj⟩, rfl⟩

noncomputable def h5FullSelectorPhase {n k m : ℕ}
    (A : Fin m → Fin k → ZMod 2) (h : (Fin k → ZMod 2) → ZMod 2)
    (s0 : Fin k → ZMod 2) (b0 b1 : Fin m → ZMod 2)
    (S : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2))
    (X Y : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2))
    (q : (Fin n → ZMod 2) → ZMod 2) (x : Fin n → ZMod 2) : ZMod 2 :=
  h (s0+S x)+(∑ i, dotProduct (A i) (s0+S x)*(b0 i+X x i)*(b1 i+Y x i))+q x

set_option maxHeartbeats 2400000 in
lemma h5_full_flat_of_deleted_section {k m r : ℕ}
    (A : Fin m → Fin k → ZMod 2) (h : (Fin k → ZMod 2) → ZMod 2)
    (s0 : Fin k → ZMod 2) (b0 b1 : Fin m → ZMod 2)
    (S : (Fin (2*m+r+2) → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2))
    (X Y : (Fin (2*m+r+2) → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2))
    (q : (Fin (2*m+r+2) → ZMod 2) → ZMod 2)
    (qd : ZMod 2) (ql : Fin (2*m+r+2) → ZMod 2)
    (Mq : Matrix (Fin (2*m+r+2)) (Fin (2*m+r+2)) (ZMod 2))
    (hq : ∀ y, q y = qd+dotProduct ql y+∑ i,∑ j,Mq i j*y i*y j)
    (J : Finset (Fin m))
    (H : ({i : Fin m // i ∉ J} × Bool → ZMod 2) →ₗ[ZMod 2] (Fin (2*m+r+2) → ZMod 2))
    (hSH : ∀ z, S (H z)=0)
    (hXH : ∀ z (i : {i : Fin m // i ∉ J}), X (H z) i.val=z (i,false))
    (hYH : ∀ z (i : {i : Fin m // i ∉ J}), Y (H z) i.val=z (i,true))
    (hJ : J.card+2 ≤ Module.finrank (ZMod 2) (LinearMap.range S)) :
    let wt := fun a : Fin k → ZMod 2 =>
      ((Finset.univ : Finset (Fin m)).filter (fun i => dotProduct (A i) a ≠ 0)).card
    let plane := (Finset.univ : Finset ((Fin k → ZMod 2) × (Fin k → ZMod 2))).sup
      (fun w => if w.1 ≠ 0 ∧ w.2 ≠ 0 ∧ w.1 ≠ w.2 then
        2^m+2^(m-wt w.1)+2^(m-wt w.2)+2^(m-wt (w.1+w.2)) else 0)
    2^(m+2)*(∑ x,Gauss.chi (h5FullSelectorPhase A h s0 b0 b1 S X Y q x)).natAbs ≤
      2^(2*m+r+2)*plane := by
  classical
  let p := Fintype.card {i : Fin m // i ∉ J}
  let f : Fin p ≃ {i : Fin m // i ∉ J} := (Fintype.equivFin _).symm
  let e : Fin p ↪ Fin m :=
    { toFun := fun i => (f i).val
      inj' := by intro i j h; exact f.injective (Subtype.ext h) }
  let R : (Fin p × Bool → ZMod 2) →ₗ[ZMod 2] ({i : Fin m // i ∉ J} × Bool → ZMod 2) :=
    { toFun := fun z ib => z (f.symm ib.1,ib.2)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let D := H.comp R
  have hSD : ∀ z, S (D z)=0 := fun z => hSH (R z)
  have hXD : ∀ z i, X (D z) (e i)=z (i,false) := by
    intro z i
    change X (H (R z)) (f i).val = _
    rw [hXH]
    simp [R]
  have hYD : ∀ z i, Y (D z) (e i)=z (i,true) := by
    intro z i
    change Y (H (R z)) (f i).val = _
    rw [hYH]
    simp [R]
  have hDinj : Function.Injective D := by
    intro z w heq
    funext ib
    rcases ib with ⟨i,b⟩
    cases b
    · have hh := congrArg (fun x => X x (e i)) heq
      simpa only [hXD] using hh
    · have hh := congrArg (fun x => Y x (e i)) heq
      simpa only [hYD] using hh
  let C : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2) :=
    { toFun := fun a i => dotProduct (A i) a
      map_add' := by intro a b; funext i; exact dotProduct_add _ _ _
      map_smul' := by intro c a; funext i; exact dotProduct_smul _ _ _ }
  let V := LinearMap.range S
  let del : V →ₗ[ZMod 2] (J → ZMod 2) :=
    { toFun := fun a j => dotProduct (A j) a
      map_add' := by intro a b; ext j; exact dotProduct_add _ _ _
      map_smul' := by intro c a; ext j; exact dotProduct_smul _ _ _ }
  obtain ⟨aa,cc,haa,hcc,hac,hda,hdc⟩ := h5_kernel_two_vectors del (by simpa using hJ)
  let U : Submodule (ZMod 2) (Fin k → ZMod 2) :=
    { carrier := {a | a ∈ V ∧ ∀ j ∈ J, C a j=0}, add_mem' := by
        intro a b ha hb
        exact ⟨V.add_mem ha.1 hb.1,fun j hj => by simp [map_add,ha.2 j hj,hb.2 j hj]⟩
      zero_mem' := by constructor; exact V.zero_mem; simp
      smul_mem' := by
        intro c a ha
        exact ⟨V.smul_mem c ha.1,fun j hj => by simp [map_smul,ha.2 j hj]⟩ }
  let a : U := ⟨aa,aa.property,fun j hj => congrFun hda ⟨j,hj⟩⟩
  let c : U := ⟨cc,cc.property,fun j hj => congrFun hdc ⟨j,hj⟩⟩
  have ha : (a:Fin k→ZMod 2) ≠ 0 := by intro hh; exact haa (Subtype.ext hh)
  have hc : (c:Fin k→ZMod 2) ≠ 0 := by intro hh; exact hcc (Subtype.ext hh)
  have hac' : (a:Fin k→ZMod 2) ≠ c := by intro hh; exact hac (Subtype.ext hh)
  have hsupport : ∀ u : U, ∀ i, i ∉ Set.range e → C u i=0 := by
    intro u i hi
    apply u.property.2 i
    by_contra hij
    apply hi
    refine ⟨f.symm ⟨i,hij⟩,?_⟩
    change (f (f.symm ⟨i,hij⟩)).val=i
    simp
  let L : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin p → ZMod 2) :=
    { toFun := fun u i => C u (e i)
      map_add' := by intro u v; ext i; exact congrFun (map_add C u v) (e i)
      map_smul' := by intro b u; ext i; exact congrFun (map_smul C b u) (e i) }
  have hweight : ∀ u : U,h5BitWeight (L u)=h5BitWeight (C u) :=
    fun u => h5_weight_restrict_zero_outside e (C u) (hsupport u)
  obtain ⟨G,hG⟩ := S.rangeRestrict.exists_rightInverse_of_surjective S.range_rangeRestrict
  let inc : U →ₗ[ZMod 2] V :=
    { toFun := fun u => ⟨u,u.property.1⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let lift := G.comp inc
  have hSlift : ∀ u : U,S (lift u)=u := by
    intro u
    have hh := congrArg (fun T : V →ₗ[ZMod 2] V => T (inc u)) hG
    exact congrArg Subtype.val hh
  let F : U × ((Fin p × Bool) → ZMod 2) →ₗ[ZMod 2] (Fin (2*m+r+2) → ZMod 2) :=
    { toFun := fun ux => lift ux.1+D ux.2
      map_add' := by intros; simp only [Prod.fst_add,Prod.snd_add,map_add]; abel
      map_smul' := by intros; simp only [Prod.smul_fst,Prod.smul_snd,map_smul,smul_add,RingHom.id_apply] }
  have hFinj : Function.Injective F := h5_selector_data_injective U S lift D hSlift hSD hDinj
  obtain ⟨W,param,hparam⟩ := h5_injective_linear_param F hFinj
  let fx : Fin m → ((Fin p × Bool) → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    fun i => (LinearMap.proj i).comp (X.comp D)
  let fy : Fin m → ((Fin p × Bool) → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    fun i => (LinearMap.proj i).comp (Y.comp D)
  let Qq := (LinearMap.toMatrix' D).transpose*(Mq+Mq.transpose)*LinearMap.toMatrix' D
  have hqpol := Gauss.quadratic_polar_matrix qd ql Mq q hq
  have hpol (w : W) : ∃ Q : Matrix (Fin p × Bool) (Fin p × Bool) (ZMod 2),
      ∀ u x y, Gauss.polar (fun z =>
        h5FullSelectorPhase A h s0 b0 b1 S X Y q (param.symm (w,u,z))) x y =
        dotProduct ((Q+h5PairDiagonal (L u)).mulVec x) y := by
    let cw := C (s0+S w)
    let hw : U → ZMod 2 := fun u => h (s0+S w+u)
    let ax : U → Fin m → ZMod 2 := fun u i => b0 i+X ((w:Fin (2*m+r+2)→ZMod 2)+lift u) i
    let ay : U → Fin m → ZMod 2 := fun u i => b1 i+Y ((w:Fin (2*m+r+2)→ZMod 2)+lift u) i
    let qq : U → ((Fin p × Bool) → ZMod 2) → ZMod 2 :=
      fun u z => q (((w:Fin (2*m+r+2)→ZMod 2)+lift u)+D z)
    have hqq : ∀ u x y, Gauss.polar (qq u) x y=dotProduct (Qq.mulVec x) y := by
      intro u x y
      exact h5_polar_comp_affine_matrix q (Mq+Mq.transpose) hqpol D _ x y
    obtain ⟨Q,hQ⟩ := h5_selector_family_polar U C e cw hw ax ay fx fy qq Qq hqq hsupport
      (fun i x => hXD x i) (fun i x => hYD x i)
    refine ⟨Q,?_⟩
    intro u x y
    have heq : (fun z => h5FullSelectorPhase A h s0 b0 b1 S X Y q (param.symm (w,u,z))) =
        (fun z => hw u+(∑ i,(cw i+C u i)*((ax u i+fx i z)*(ay u i+fy i z)))+qq u z) := by
      funext z
      rw [hparam]
      change h5FullSelectorPhase A h s0 b0 b1 S X Y q ((w:Fin (2*m+r+2)→ZMod 2)+(lift u+D z)) = _
      simp only [h5FullSelectorPhase,map_add,hSlift,hSD,add_zero,Pi.add_apply]
      change h (s0+(S w+u))+(∑ i,dotProduct (A i) (s0+(S w+u))*
        (b0 i+(X w i+(X (lift u) i+X (D z) i)))*
        (b1 i+(Y w i+(Y (lift u) i+Y (D z) i))))+q (↑w+(lift u+D z)) = _
      dsimp only [hw,cw,ax,ay,fx,fy,qq,C,LinearMap.coe_mk,AddHom.coe_mk,
        LinearMap.comp_apply,LinearMap.proj_apply]
      simp only [map_add,Pi.add_apply,dotProduct_add]
      simp only [add_assoc,mul_assoc]
    rw [heq]
    exact hQ u x y
  choose Q hQ using hpol
  have hp : p ≤ m := by
    have hh := Fintype.card_le_of_injective e e.injective
    simpa only [Fintype.card_fin] using hh
  have hh := h5_full_flat_sup_bound_of_param U C L a c ha hc hac' hp hweight
    (h5FullSelectorPhase A h s0 b0 b1 S X Y q) param.toEquiv Q hQ
  exact hh

end h5_part_24

section h5_part_25

lemma h5_full_coordinate_maps {n t k m r : ℕ}
    (e : (Fin n → ZMod 2) ≃ₗ[ZMod 2]
      ((Fin k → ZMod 2) × (Fin m → ZMod 2) × (Fin m → ZMod 2) × (Fin r → ZMod 2)))
    (L : (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (hL : Function.Injective L) :
    ∃ (sel : (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2))
      (X Y : (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2))
      (data : (Fin t → ZMod 2) →ₗ[ZMod 2] ((Fin m × Bool ⊕ Fin r) → ZMod 2)),
      (∀ x, sel x = (e (L x)).1) ∧
      (∀ x, X x = (e (L x)).2.1) ∧
      (∀ x, Y x = (e (L x)).2.2.1) ∧
      (∀ x i, data x (Sum.inl (i,false)) = X x i) ∧
      (∀ x i, data x (Sum.inl (i,true)) = Y x i) ∧
      (∀ x i, data x (Sum.inr i) = (e (L x)).2.2.2 i) ∧
      Function.Injective (sel.prod data) := by
  let F := e.toLinearMap.comp L
  let sel := (LinearMap.fst (ZMod 2) _ _).comp F
  let tail := (LinearMap.snd (ZMod 2) _ _).comp F
  let X := (LinearMap.fst (ZMod 2) _ _).comp tail
  let tail2 := (LinearMap.snd (ZMod 2) _ _).comp tail
  let Y := (LinearMap.fst (ZMod 2) _ _).comp tail2
  let Z := (LinearMap.snd (ZMod 2) _ _).comp tail2
  let data : (Fin t → ZMod 2) →ₗ[ZMod 2] ((Fin m × Bool ⊕ Fin r) → ZMod 2) :=
    { toFun := fun x => Sum.elim (fun q => if q.2 then Y x q.1 else X x q.1) (Z x)
      map_add' := by
        intro x y
        ext j
        rcases j with ⟨i,b⟩ | i
        · cases b <;> simp
        · simp
      map_smul' := by
        intro c x
        ext j
        rcases j with ⟨i,b⟩ | i
        · cases b <;> simp
        · simp }
  refine ⟨sel,X,Y,data,(fun _ => rfl),(fun _ => rfl),(fun _ => rfl),
    (fun _ _ => rfl),(fun _ _ => rfl),(fun _ _ => rfl),?_⟩
  intro x y hxy
  have hs := congrArg Prod.fst hxy
  have hd := congrArg Prod.snd hxy
  apply hL
  apply e.injective
  apply Prod.ext
  · exact hs
  apply Prod.ext
  · funext i
    exact congrFun hd (Sum.inl (i,false))
  · apply Prod.ext
    · funext i
      exact congrFun hd (Sum.inl (i,true))
    · funext i
      exact congrFun hd (Sum.inr i)

set_option maxHeartbeats 1000000 in
lemma h5_full_original_bound_of_geometry {n k m r : ℕ}
    (e : (Fin n → ZMod 2) ≃ₗ[ZMod 2]
      ((Fin k → ZMod 2) × (Fin m → ZMod 2) × (Fin m → ZMod 2) × (Fin r → ZMod 2)))
    (A : Fin m → Fin k → ZMod 2) (h : (Fin k → ZMod 2) → ZMod 2)
    (g : (Fin n → ZMod 2) → ZMod 2)
    (hg : ∀ y, g y = h (e y).1+∑ i,dotProduct (A i) (e y).1*(e y).2.1 i*(e y).2.2.1 i)
    (L : (Fin (2*m+r+2) → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (a : Fin n → ZMod 2) (hL : Function.Injective L)
    (q : (Fin (2*m+r+2) → ZMod 2) → ZMod 2)
    (hq : ∃ (qd : ZMod 2) (ql : Fin (2*m+r+2) → ZMod 2)
      (M : Fin (2*m+r+2) → Fin (2*m+r+2) → ZMod 2),
      ∀ y,q y=qd+dotProduct ql y+∑ i,∑ j,M i j*y i*y j)
    (hgeometry : ∀
      (S : (Fin (2*m+r+2) → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2))
      (D : (Fin (2*m+r+2) → ZMod 2) →ₗ[ZMod 2] ((Fin m × Bool ⊕ Fin r) → ZMod 2)),
      Function.Injective (S.prod D) →
      ∃ J : Finset (Fin m), J.card+2 ≤ Module.finrank (ZMod 2) (LinearMap.range S) ∧
        ∃ H : ({i : Fin m // i ∉ J} × Bool → ZMod 2) →ₗ[ZMod 2] (Fin (2*m+r+2) → ZMod 2),
          (∀ z,S (H z)=0) ∧
          ∀ z (i : {i : Fin m // i ∉ J}) b,D (H z) (Sum.inl (i.val,b))=z (i,b)) :
    let wt := fun s : Fin k → ZMod 2 =>
      ((Finset.univ : Finset (Fin m)).filter (fun i => dotProduct (A i) s ≠ 0)).card
    let plane := (Finset.univ : Finset ((Fin k → ZMod 2) × (Fin k → ZMod 2))).sup
      (fun w => if w.1 ≠ 0 ∧ w.2 ≠ 0 ∧ w.1 ≠ w.2 then
        2^m+2^(m-wt w.1)+2^(m-wt w.2)+2^(m-wt (w.1+w.2)) else 0)
    2^(m+2)*(∑ x,if g (a+L x)=q x then (1:ℤ) else -1).natAbs ≤ 2^(2*m+r+2)*plane := by
  classical
  obtain ⟨S,X,Y,D,hS,hX,hY,hD0,hD1,hDZ,hinj⟩ := h5_full_coordinate_maps e L hL
  obtain ⟨J,hJ,H,hSH,hDH⟩ := hgeometry S D hinj
  obtain ⟨qd,ql,M,hq⟩ := hq
  have hXH : ∀ z (i : {i : Fin m // i ∉ J}),X (H z) i.val=z (i,false) := by
    intro z i
    rw [←hD0,hDH]
  have hYH : ∀ z (i : {i : Fin m // i ∉ J}),Y (H z) i.val=z (i,true) := by
    intro z i
    rw [←hD1,hDH]
  have hb := h5_full_flat_of_deleted_section A h (e a).1 (e a).2.1 (e a).2.2.1
    S X Y q qd ql M hq J H hSH hXH hYH hJ
  have hphase (x : Fin (2*m+r+2) → ZMod 2) :
      g (a+L x)+q x=h5FullSelectorPhase A h (e a).1 (e a).2.1 (e a).2.2.1 S X Y q x := by
    unfold h5FullSelectorPhase
    rw [hg,map_add,hS,hX,hY]
    rfl
  have hsum : (∑ x,if g (a+L x)=q x then (1:ℤ) else -1) =
      ∑ x,Gauss.chi (h5FullSelectorPhase A h (e a).1 (e a).2.1 (e a).2.2.1 S X Y q x) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [Gauss.chi_eq,hphase]
  rw [hsum]
  exact hb

end h5_part_25

section h5_part_26

lemma h5_data_kernel_injective {K E S T : Type*} [Field K]
    [AddCommGroup E] [Module K E] [AddCommGroup S] [Module K S]
    [AddCommGroup T] [Module K T]
    (sel : E →ₗ[K] S) (data : E →ₗ[K] T)
    (hinj : Function.Injective (sel.prod data)) :
    Function.Injective (data.comp (LinearMap.ker sel).subtype) := by
  intro x y h
  apply Subtype.ext
  apply hinj
  apply Prod.ext
  · change sel x=sel y
    rw [x.property,y.property]
  · exact h

lemma h5_data_kernel_quotient_dimension {K E S T : Type*} [Field K]
    [AddCommGroup E] [Module K E] [AddCommGroup S] [Module K S]
    [AddCommGroup T] [Module K T] [FiniteDimensional K E] [FiniteDimensional K T]
    (sel : E →ₗ[K] S) (data : E →ₗ[K] T)
    (hinj : Function.Injective (sel.prod data)) :
    Module.finrank K (LinearMap.range sel)+Module.finrank K T =
      Module.finrank K E+Module.finrank K (T ⧸ LinearMap.range (data.comp (LinearMap.ker sel).subtype)) := by
  have hk := h5_data_kernel_injective sel data hinj
  have hr := LinearMap.finrank_range_of_inj hk
  have hq := (LinearMap.range (data.comp (LinearMap.ker sel).subtype)).finrank_quotient_add_finrank
  have hs := sel.finrank_range_add_finrank_ker
  omega

end h5_part_26


section h5_part_27

lemma h5_coordinate_pivots {K I : Type*} [Field K] [Fintype I]
    (W : Submodule K (I → K)) :
    ∃ P : Finset I, P.card = Module.finrank K ((I → K) ⧸ W) ∧
      ∀ x : I → K, ∃ w : W, ∀ i ∉ P, (w : I → K) i = x i := by
  classical
  let v : I → ((I → K) ⧸ W) := fun i => W.mkQ (Pi.basisFun K I i)
  have hv : Submodule.span K (Set.range v) = ⊤ := by
    change Submodule.span K (Set.range (W.mkQ ∘ Pi.basisFun K I)) = ⊤
    rw [Set.range_comp, ← Submodule.map_span, (Pi.basisFun K I).span_eq,
      Submodule.map_top, W.range_mkQ]
  obtain ⟨s, -, -, hs, hli⟩ := exists_linearIndepOn_extension
    (linearIndepOn_empty K v) (Set.empty_subset (Set.univ : Set I))
  have hsp : Submodule.span K (v '' s) = ⊤ := by
    apply top_unique
    rw [← hv]
    apply Submodule.span_le.mpr
    simpa using hs
  let b : Module.Basis s K ((I → K) ⧸ W) := Module.Basis.mk hli (by
    have hr : Set.range (fun i : s => v i) = v '' s := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩; exact ⟨i, i.property, rfl⟩
      · rintro ⟨i, hi, rfl⟩; exact ⟨⟨i, hi⟩, rfl⟩
    rw [hr, hsp])
  refine ⟨s.toFinset, ?_, ?_⟩
  · simpa using (Module.finrank_eq_card_basis b).symm
  · intro x
    let U : Submodule K (I → K) :=
      { carrier := { z | ∀ i ∉ s, z i = 0 }, add_mem' := by intro a b ha hb i hi; simp [ha i hi, hb i hi]
        zero_mem' := by simp
        smul_mem' := by intro a z hz i hi; simp [hz i hi] }
    have hmap : U.map W.mkQ = ⊤ := by
      apply top_unique
      rw [← hsp]
      apply Submodule.span_le.mpr
      rintro _ ⟨i, hi, rfl⟩
      refine ⟨Pi.basisFun K I i, ?_, rfl⟩
      intro j hj
      have hij : j ≠ i := by intro h; subst j; exact hj hi
      simp [Pi.basisFun_apply, hij]
    have hx : W.mkQ x ∈ U.map W.mkQ := by rw [hmap]; trivial
    obtain ⟨z, hz, heq⟩ := hx
    have hw : x - z ∈ W := by
      rw [← W.ker_mkQ, LinearMap.mem_ker, map_sub, heq, sub_self]
    refine ⟨⟨x-z, hw⟩, ?_⟩
    intro i hi
    have hz0 : z i = 0 := hz i (by simpa using hi)
    simp [hz0]

lemma h5_coordinate_section {K I : Type*} [Field K] [Fintype I]
    (W : Submodule K (I → K)) :
    ∃ P : Finset I, P.card = Module.finrank K ((I → K) ⧸ W) ∧
      ∃ H : ({i : I // i ∉ P} → K) →ₗ[K] W,
        ∀ x (i : {i : I // i ∉ P}), ((H x : W) : I → K) i = x i := by
  classical
  obtain ⟨P, hP, hp⟩ := h5_coordinate_pivots W
  let f : W →ₗ[K] ({i : I // i ∉ P} → K) :=
    { toFun := fun w i => (w : I → K) i
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hf : Function.Surjective f := by
    intro x
    let y : I → K := fun i => if h : i ∉ P then x ⟨i, h⟩ else 0
    obtain ⟨w, hw⟩ := hp y
    refine ⟨w, ?_⟩
    ext i
    change (w : I → K) i = x i
    rw [hw i i.property]
    simp [y, i.property]
  obtain ⟨H, hH⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hf)
  refine ⟨P, hP, H, ?_⟩
  intro x i
  exact congrFun (LinearMap.congr_fun hH x) i

lemma h5_paired_coordinate_section {K A N : Type*} [Field K] [Fintype A] [Fintype N]
    (W : Submodule K ((A × Bool ⊕ N) → K)) :
    ∃ J : Finset A, J.card ≤ Module.finrank K (((A × Bool ⊕ N) → K) ⧸ W) ∧
      ∃ H : (({i : A // i ∉ J} × Bool) → K) →ₗ[K] W,
        ∀ x (i : {i : A // i ∉ J}) b, ((H x : W) : (A × Bool ⊕ N) → K) (Sum.inl (i, b)) = x (i, b) := by
  classical
  obtain ⟨P, hP, hp⟩ := h5_coordinate_pivots W
  let J : Finset A := Finset.univ.filter (fun i => ∃ b : Bool, Sum.inl (i,b) ∈ P)
  have hJ : ∀ i, i ∈ J ↔ ∃ b : Bool, Sum.inl (i,b) ∈ P := by intro i; simp [J]
  have hcard : J.card ≤ P.card := by
    have hex : ∀ i : J, ∃ b : Bool, Sum.inl (i.val,b) ∈ P := fun i => (hJ i).mp i.property
    choose b hb using hex
    let f : J → P := fun i => ⟨Sum.inl (i.val,b i), hb i⟩
    have hinj : Function.Injective f := by
      intro i j hij
      apply Subtype.ext
      exact congrArg Prod.fst (Sum.inl.inj (congrArg Subtype.val hij))
    simpa using Fintype.card_le_of_injective f hinj
  let f : W →ₗ[K] (({i : A // i ∉ J} × Bool) → K) :=
    { toFun := fun w ib => (w : (A × Bool ⊕ N) → K) (Sum.inl (ib.1, ib.2))
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hf : Function.Surjective f := by
    intro x
    let y : (A × Bool ⊕ N) → K := fun z => match z with
      | Sum.inl (i,b) => if h : i ∉ J then x (⟨i,h⟩,b) else 0
      | Sum.inr _ => 0
    obtain ⟨w, hw⟩ := hp y
    refine ⟨w, ?_⟩
    ext ⟨i, b⟩
    have hi : Sum.inl (i.val,b) ∉ P := by
      intro h
      exact i.property ((hJ i).mpr ⟨b,h⟩)
    change (w : (A × Bool ⊕ N) → K) (Sum.inl (i,b)) = x (i,b)
    rw [hw _ hi]
    simp [y, i.property]
  obtain ⟨H, hH⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hf)
  refine ⟨J, hP ▸ hcard, H, ?_⟩
  intro x i b
  exact congrFun (LinearMap.congr_fun hH x) (i,b)

end h5_part_27

section h5_part_28

lemma h5_fullflat_data_section {k m r j : ℕ}
    (S : (Fin (2*m+r+j) → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2))
    (D : (Fin (2*m+r+j) → ZMod 2) →ₗ[ZMod 2] ((Fin m × Bool ⊕ Fin r) → ZMod 2))
    (hinj : Function.Injective (S.prod D)) :
    ∃ J : Finset (Fin m), J.card+j ≤ Module.finrank (ZMod 2) (LinearMap.range S) ∧
      ∃ H : ({i : Fin m // i ∉ J} × Bool → ZMod 2) →ₗ[ZMod 2] (Fin (2*m+r+j) → ZMod 2),
        (∀ z,S (H z)=0) ∧
        ∀ z (i : {i : Fin m // i ∉ J}) b,D (H z) (Sum.inl (i.val,b))=z (i,b) := by
  classical
  let DK := D.comp (LinearMap.ker S).subtype
  let W := LinearMap.range DK
  have hdim := h5_data_kernel_quotient_dimension S D hinj
  have hcod : Module.finrank (ZMod 2) (((Fin m × Bool ⊕ Fin r) → ZMod 2) ⧸ W)+j =
      Module.finrank (ZMod 2) (LinearMap.range S) := by
    simp only [Module.finrank_pi,Fintype.card_sum,
      Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at hdim
    change Module.finrank (ZMod 2) (LinearMap.range S)+(m*2+r) =
      (2*m+r+j)+Module.finrank (ZMod 2) (((Fin m × Bool ⊕ Fin r) → ZMod 2) ⧸ W) at hdim
    omega
  obtain ⟨J,hJ,H0,hH0⟩ := h5_paired_coordinate_section W
  obtain ⟨G,hG⟩ := DK.rangeRestrict.exists_rightInverse_of_surjective DK.range_rangeRestrict
  let H := (LinearMap.ker S).subtype.comp (G.comp H0)
  refine ⟨J,by omega,H,?_,?_⟩
  · intro z
    exact (G (H0 z)).property
  · intro z i b
    have hh : DK (G (H0 z)) = (H0 z : (Fin m × Bool ⊕ Fin r) → ZMod 2) :=
      congrArg Subtype.val (LinearMap.congr_fun hG (H0 z))
    change DK (G (H0 z)) (Sum.inl (i.val,b))=z (i,b)
    rw [hh]
    exact hH0 z i b

end h5_part_28

section h5_part_29

lemma h5_full_original_bound {n k m r : ℕ}
    (e : (Fin n → ZMod 2) ≃ₗ[ZMod 2]
      ((Fin k → ZMod 2) × (Fin m → ZMod 2) × (Fin m → ZMod 2) × (Fin r → ZMod 2)))
    (A : Fin m → Fin k → ZMod 2) (h : (Fin k → ZMod 2) → ZMod 2)
    (g : (Fin n → ZMod 2) → ZMod 2)
    (hg : ∀ y, g y = h (e y).1+∑ i,dotProduct (A i) (e y).1*(e y).2.1 i*(e y).2.2.1 i)
    (L : (Fin (2*m+r+2) → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (a : Fin n → ZMod 2) (hL : Function.Injective L)
    (q : (Fin (2*m+r+2) → ZMod 2) → ZMod 2)
    (hq : ∃ (qd : ZMod 2) (ql : Fin (2*m+r+2) → ZMod 2)
      (M : Fin (2*m+r+2) → Fin (2*m+r+2) → ZMod 2),
      ∀ y,q y=qd+dotProduct ql y+∑ i,∑ j,M i j*y i*y j)
 :
    let wt := fun s : Fin k → ZMod 2 =>
      ((Finset.univ : Finset (Fin m)).filter (fun i => dotProduct (A i) s ≠ 0)).card
    let plane := (Finset.univ : Finset ((Fin k → ZMod 2) × (Fin k → ZMod 2))).sup
      (fun w => if w.1 ≠ 0 ∧ w.2 ≠ 0 ∧ w.1 ≠ w.2 then
        2^m+2^(m-wt w.1)+2^(m-wt w.2)+2^(m-wt (w.1+w.2)) else 0)
    2^(m+2)*(∑ x,if g (a+L x)=q x then (1:ℤ) else -1).natAbs ≤ 2^(2*m+r+2)*plane := by
  exact h5_full_original_bound_of_geometry e A h g hg L a hL q hq
    (fun S D hinj => h5_fullflat_data_section S D hinj)

end h5_part_29

section h5_part_30

lemma h5_product_polar_rank_le_two {I : Type*} [Fintype I] (u v : I → ZMod 2) :
    (Matrix.vecMulVec u v + Matrix.vecMulVec v u).rank ≤ 2 := by
  have h := h5_matrix_rank_add_le (Matrix.vecMulVec u v) (Matrix.vecMulVec v u)
  have hu := Matrix.rank_vecMulVec_le u v
  have hv := Matrix.rank_vecMulVec_le v u
  omega

lemma h5_rank_two_perturbation {I : Type*} [Fintype I]
    (Q : Matrix I I (ZMod 2)) (u v : I → ZMod 2) :
    Q.rank ≤ (Q + (Matrix.vecMulVec u v + Matrix.vecMulVec v u)).rank + 2 := by
  let R := Matrix.vecMulVec u v + Matrix.vecMulVec v u
  have htwo : ∀ x : ZMod 2, x + x = 0 := by decide
  have hcancel : (Q + R) + R = Q := by
    ext i j
    simp only [Matrix.add_apply]
    rw [add_assoc, htwo, add_zero]
  have h := h5_matrix_rank_add_le (Q + R) R
  rw [hcancel] at h
  have hr : R.rank ≤ 2 := h5_product_polar_rank_le_two u v
  change Q.rank ≤ (Q + R).rank + 2
  omega

lemma h5_pair_rank_two_perturbation {m : ℕ} (a : Fin m → ZMod 2)
    (u v : Fin m × Bool → ZMod 2) :
    2 * h5BitWeight a ≤
      (h5PairDiagonal a + (Matrix.vecMulVec u v + Matrix.vecMulVec v u)).rank + 2 := by
  have h := h5_rank_two_perturbation (h5PairDiagonal a) u v
  rwa [h5_pair_diagonal_rank] at h

lemma h5_pair_rank_two_perturbation_sub {m : ℕ} (a : Fin m → ZMod 2)
    (u v : Fin m × Bool → ZMod 2) :
    2 * h5BitWeight a - 2 ≤
      (h5PairDiagonal a + (Matrix.vecMulVec u v + Matrix.vecMulVec v u)).rank := by
  have h := h5_pair_rank_two_perturbation a u v
  omega

lemma h5_affine_product_polar {I : Type*} [Fintype I]
    (u v : I → ZMod 2) (u0 v0 : ZMod 2) (x y : I → ZMod 2) :
    (u0 + dotProduct u (x + y)) * (v0 + dotProduct v (x + y)) +
      (u0 + dotProduct u x) * (v0 + dotProduct v x) +
      (u0 + dotProduct u y) * (v0 + dotProduct v y) + u0 * v0 =
        dotProduct x ((Matrix.vecMulVec u v + Matrix.vecMulVec v u).mulVec y) := by
  have hprod (s t : I → ZMod 2) :
      dotProduct x ((Matrix.vecMulVec s t).mulVec y) = dotProduct x s * dotProduct t y := by
    change (∑ i, x i * ∑ j, s i * t j * y j) =
      (∑ i, x i * s i) * (∑ j, t j * y j)
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp only [Matrix.add_mulVec, dotProduct_add, hprod,
    dotProduct_comm x u, dotProduct_comm x v]
  ring_nf
  simp only [show (2 : ZMod 2) = 0 from rfl, show (4 : ZMod 2) = 0 from rfl,
    mul_zero, add_zero, zero_add]

lemma h5_product_polar_symm {I : Type*} [Fintype I] (u v : I → ZMod 2) :
    (Matrix.vecMulVec u v + Matrix.vecMulVec v u).transpose =
      Matrix.vecMulVec u v + Matrix.vecMulVec v u := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.add_apply, Matrix.vecMulVec_apply]
  ring

lemma h5_product_polar_diag_zero {I : Type*} [Fintype I] (u v : I → ZMod 2) (i : I) :
    (Matrix.vecMulVec u v + Matrix.vecMulVec v u) i i = 0 := by
  have htwo : ∀ x : ZMod 2, x + x = 0 := by decide
  simp only [Matrix.add_apply, Matrix.vecMulVec_apply]
  rw [mul_comm (v i) (u i), htwo]

lemma h5_pair_diagonal_restrict {m t : ℕ} (e : Fin t ↪ Fin m) (a : Fin m → ZMod 2) :
    (h5PairDiagonal a).submatrix (fun p : Fin t × Bool => (e p.1, p.2))
      (fun p : Fin t × Bool => (e p.1, p.2)) =
        h5PairDiagonal (fun i => a (e i)) := by
  ext p q
  simp only [Matrix.submatrix_apply, h5_pair_diagonal_apply, e.injective.eq_iff]

lemma h5_pair_rank_two_restrict {m t : ℕ}
    (e : Fin t ↪ Fin m) (a : Fin m → ZMod 2)
    (hzero : ∀ i, i ∉ Set.range e → a i = 0)
    (u v : Fin m × Bool → ZMod 2) :
    2 * h5BitWeight a ≤
      ((h5PairDiagonal a + (Matrix.vecMulVec u v + Matrix.vecMulVec v u)).submatrix
        (fun p : Fin t × Bool => (e p.1, p.2))
        (fun p : Fin t × Bool => (e p.1, p.2))).rank + 2 := by
  have h := h5_pair_rank_two_perturbation (fun i => a (e i))
    (fun p : Fin t × Bool => u (e p.1, p.2)) (fun p : Fin t × Bool => v (e p.1, p.2))
  rw [h5_weight_restrict_zero_outside e a hzero] at h
  have heq :
      (h5PairDiagonal a + (Matrix.vecMulVec u v + Matrix.vecMulVec v u)).submatrix
        (fun p : Fin t × Bool => (e p.1, p.2))
        (fun p : Fin t × Bool => (e p.1, p.2)) =
      h5PairDiagonal (fun i => a (e i)) +
        (Matrix.vecMulVec (fun p : Fin t × Bool => u (e p.1, p.2))
          (fun p : Fin t × Bool => v (e p.1, p.2)) +
        Matrix.vecMulVec (fun p : Fin t × Bool => v (e p.1, p.2))
          (fun p : Fin t × Bool => u (e p.1, p.2))) := by
    ext p q
    simp only [Matrix.submatrix_apply, Matrix.add_apply, Matrix.vecMulVec_apply,
      h5_pair_diagonal_apply, e.injective.eq_iff]
  rwa [heq]

end h5_part_30

namespace Gauss

open Classical

end Gauss

section h5_part_31

lemma h5_unsigned_pair_bound {I : Type*} [Fintype I] (f g : I → ℤ)
    (hf : ∀ i, f i = 1 ∨ f i = -1) (hg : ∀ i, g i = 1 ∨ g i = -1) :
    (∑ i, f i) + (∑ i, g i) ≤ Fintype.card I + ∑ i, f i * g i := by
  have hpoint (i : I) : f i + g i ≤ 1 + f i * g i := by
    rcases hf i with h | h <;> rcases hg i with h' | h' <;> rw [h, h'] <;> norm_num
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpoint i)
  simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] using hsum

lemma h5_pair_bound {I : Type*} [Fintype I] (f g : I → ℤ)
    (hf : ∀ i, f i = 1 ∨ f i = -1) (hg : ∀ i, g i = 1 ∨ g i = -1) :
    |∑ i, f i| + |∑ i, g i| ≤ Fintype.card I + |∑ i, f i * g i| := by
  have hnf (i : I) : -f i = 1 ∨ -f i = -1 := by rcases hf i with h | h <;> omega
  have hng (i : I) : -g i = 1 ∨ -g i = -1 := by rcases hg i with h | h <;> omega
  have hpos := le_abs_self (∑ i, f i * g i)
  have hneg := neg_le_abs (∑ i, f i * g i)
  by_cases hf0 : 0 ≤ ∑ i, f i <;> by_cases hg0 : 0 ≤ ∑ i, g i
  · rw [abs_of_nonneg hf0, abs_of_nonneg hg0]
    have h := h5_unsigned_pair_bound f g hf hg
    omega
  · rw [abs_of_nonneg hf0, abs_of_neg (by omega : (∑ i, g i) < 0)]
    have h := h5_unsigned_pair_bound f (fun i => -g i) hf hng
    simp only [mul_neg, Finset.sum_neg_distrib] at h
    omega
  · rw [abs_of_neg (by omega : (∑ i, f i) < 0), abs_of_nonneg hg0]
    have h := h5_unsigned_pair_bound (fun i => -f i) g hnf hg
    simp only [neg_mul, Finset.sum_neg_distrib] at h
    omega
  · rw [abs_of_neg (by omega : (∑ i, f i) < 0), abs_of_neg (by omega : (∑ i, g i) < 0)]
    have h := h5_unsigned_pair_bound (fun i => -f i) (fun i => -g i) hnf hng
    simp only [neg_mul_neg, Finset.sum_neg_distrib] at h
    omega

lemma h5_triple_derivative_first (x y z b c : ZMod 2) :
    (x + 1) * (y + b) * (z + c) + x * y * z =
      (y + b*x + b) * (z + c*x + c) := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;> fin_cases b <;> fin_cases c <;> decide

lemma h5_triple_derivative_second (x y z c : ZMod 2) :
    x * (y + 1) * (z + c) + x * y * z = x * (z + c*y + c) := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;> fin_cases c <;> decide

lemma h5_triple_derivative_third (x y z : ZMod 2) :
    x * y * (z + 1) + x * y * z = x * y := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;> decide

lemma h5_triple_derivative_factor (a b c : ZMod 2) :
    ∃ u0 u1 u2 u3 v0 v1 v2 v3 : ZMod 2, ∀ x y z : ZMod 2,
      (x+a)*(y+b)*(z+c)+x*y*z =
        (u0+u1*x+u2*y+u3*z)*(v0+v1*x+v2*y+v3*z) := by
  have hbit (x : ZMod 2) : x = 0 ∨ x = 1 := by
    fin_cases x
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hbit a with rfl | rfl
  · rcases hbit b with rfl | rfl
    · rcases hbit c with rfl | rfl
      · refine ⟨0,0,0,0,0,0,0,0,?_⟩
        intro x y z
        fin_cases x <;> fin_cases y <;> fin_cases z <;> decide
      · refine ⟨0,1,0,0,0,0,1,0,?_⟩
        intro x y z
        simpa using h5_triple_derivative_third x y z
    · refine ⟨0,1,0,0,c,0,c,1,?_⟩
      intro x y z
      simpa only [zero_mul, one_mul, add_zero, zero_add, add_comm, add_left_comm, add_assoc] using h5_triple_derivative_second x y z c
  · refine ⟨b,b,1,0,c,c,0,1,?_⟩
    intro x y z
    simpa only [zero_mul, one_mul, add_zero, zero_add, add_comm, add_left_comm, add_assoc] using h5_triple_derivative_first x y z b c

lemma h5_family_pair_bound {I H : Type*} [Fintype I] [Fintype H]
    (f : I → Bool → H → ℤ) (cap : ℤ)
    (hf : ∀ i b x, f i b x = 1 ∨ f i b x = -1)
    (hcorr : ∀ i, |∑ x, f i false x * f i true x| ≤ cap) :
    |∑ i, ∑ b, ∑ x, f i b x| ≤ Fintype.card I * ((Fintype.card H : ℤ) + cap) := by
  have hpair (i : I) : |∑ b, ∑ x, f i b x| ≤ Fintype.card H + cap := by
    rw [Fintype.sum_bool]
    have hp := h5_pair_bound (f i false) (f i true) (hf i false) (hf i true)
    have ht := abs_add_le (∑ x, f i true x) (∑ x, f i false x)
    have hc := hcorr i
    omega
  calc
    |∑ i, ∑ b, ∑ x, f i b x| ≤ ∑ i, |∑ b, ∑ x, f i b x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : I, ((Fintype.card H : ℤ) + cap) := Finset.sum_le_sum (fun i _ => hpair i)
    _ = Fintype.card I * ((Fintype.card H : ℤ) + cap) := by simp

end h5_part_31


section h5_part_32

lemma h5_line_gauss_bound {m d : ℕ} (a : Fin m → ZMod 2)
    (u v : Fin m × Bool → ZMod 2)
    (q : (Fin m × Bool → ZMod 2) → ZMod 2)
    (hd : d ≤ h5BitWeight a)
    (hpol : ∀ x y, Gauss.polar q x y =
      dotProduct ((h5PairDiagonal a +
        (Matrix.vecMulVec u v + Matrix.vecMulVec v u)).mulVec x) y) :
    |∑ x : Fin m × Bool → ZMod 2, Gauss.chi (q x)| ≤
      (2 : ℤ) ^ (2 * m - (d - 1)) := by
  have h := h5_pair_rank_two_perturbation a u v
  have hr : 2 * (d - 1) ≤
      (h5PairDiagonal a + (Matrix.vecMulVec u v + Matrix.vecMulVec v u)).rank := by omega
  have hg := Gauss.gauss_bound_of_rank_ge_fintype q _ hpol hr
  simpa only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Nat.mul_comm] using hg

lemma h5_line_gauss_restrict_bound {m t d : ℕ}
    (e : Fin t ↪ Fin m) (a : Fin m → ZMod 2)
    (hzero : ∀ i, i ∉ Set.range e → a i = 0)
    (u v : Fin m × Bool → ZMod 2)
    (q : (Fin t × Bool → ZMod 2) → ZMod 2)
    (hd : d ≤ h5BitWeight a)
    (hpol : ∀ x y, Gauss.polar q x y =
      dotProduct (((h5PairDiagonal a + (Matrix.vecMulVec u v + Matrix.vecMulVec v u)).submatrix
        (fun p : Fin t × Bool => (e p.1, p.2))
        (fun p : Fin t × Bool => (e p.1, p.2))).mulVec x) y) :
    |∑ x : Fin t × Bool → ZMod 2, Gauss.chi (q x)| ≤
      (2 : ℤ) ^ (2 * t - (d - 1)) := by
  have h := h5_pair_rank_two_restrict e a hzero u v
  have hr : 2 * (d - 1) ≤
      ((h5PairDiagonal a + (Matrix.vecMulVec u v + Matrix.vecMulVec v u)).submatrix
        (fun p : Fin t × Bool => (e p.1, p.2))
        (fun p : Fin t × Bool => (e p.1, p.2))).rank := by omega
  have hg := Gauss.gauss_bound_of_rank_ge_fintype q _ hpol hr
  simpa only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Nat.mul_comm] using hg

lemma h5_line_pair_gauss_bound {m d : ℕ} (a : Fin m → ZMod 2)
    (u v : Fin m × Bool → ZMod 2)
    (q : (Fin m × Bool → ZMod 2) → ZMod 2)
    (f g : (Fin m × Bool → ZMod 2) → ℤ)
    (hf : ∀ x, f x = 1 ∨ f x = -1) (hg : ∀ x, g x = 1 ∨ g x = -1)
    (hprod : ∀ x, f x * g x = Gauss.chi (q x))
    (hd : d ≤ h5BitWeight a)
    (hpol : ∀ x y, Gauss.polar q x y =
      dotProduct ((h5PairDiagonal a +
        (Matrix.vecMulVec u v + Matrix.vecMulVec v u)).mulVec x) y) :
    |∑ x, f x| + |∑ x, g x| ≤
      (2 : ℤ) ^ (2 * m) + (2 : ℤ) ^ (2 * m - (d - 1)) := by
  have hp := h5_pair_bound f g hf hg
  simp only [hprod] at hp
  have hb := h5_line_gauss_bound a u v q hd hpol
  have hc : (Fintype.card (Fin m × Bool → ZMod 2) : ℤ) = (2 : ℤ) ^ (2 * m) := by
    simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
      ZMod.card, Nat.cast_pow, Nat.cast_ofNat]
    rw [Nat.mul_comm]
  rw [hc] at hp
  exact hp.trans (add_le_add le_rfl hb)

end h5_part_32


section h5_part_33

lemma h5_line_pair_scaling (m p d : ℕ) (hd : 0 < d) (hdm : d ≤ m) (hdp : d ≤ p) :
    2 ^ (m + 2) * (2 ^ (2 * p) + 2 ^ (2 * p - (d - 1))) =
      2 ^ (2 * p + 2) * (2 ^ m + 2 ^ (m + 1 - d)) := by
  rw [Nat.mul_add, Nat.mul_add]
  apply congrArg₂ Nat.add
  · rw [← pow_add, ← pow_add]
    congr 1
    omega
  · rw [← pow_add, ← pow_add]
    congr 1
    omega

lemma h5_line_flat_of_paired_polars
    {E I : Type*} [Fintype E] [Fintype I]
    {m r p d : ℕ} (hd : 0 < d)
    (e : Fin p ↪ Fin m) (a : Fin m → ZMod 2)
    (hzero : ∀ i, i ∉ Set.range e → a i = 0)
    (ha : d ≤ h5BitWeight a)
    (param : (I × (Bool × (Fin p × Bool → ZMod 2))) ≃ E)
    (hcard : Fintype.card I * 2 ^ (2 * p) = 2 ^ (2 * m + r))
    (phase : E → ZMod 2)
    (hpol : ∀ i : I, ∃ u v : Fin m × Bool → ZMod 2,
      ∀ x y : Fin p × Bool → ZMod 2,
        Gauss.polar (fun z => phase (param (i, false, z)) + phase (param (i, true, z))) x y =
          dotProduct (((h5PairDiagonal a + (Matrix.vecMulVec u v + Matrix.vecMulVec v u)).submatrix
            (fun q : Fin p × Bool => (e q.1, q.2))
            (fun q : Fin p × Bool => (e q.1, q.2))).mulVec x) y) :
    2 ^ (m + 2) * (∑ x : E, Gauss.chi (phase x)).natAbs ≤
      2 ^ (2 * m + r + 2) * (2 ^ m + 2 ^ (m + 1 - d)) := by
  classical
  let f : I → Bool → (Fin p × Bool → ZMod 2) → ℤ :=
    fun i b x => Gauss.chi (phase (param (i, b, x)))
  have hf : ∀ i b x, f i b x = 1 ∨ f i b x = -1 := by
    intro i b x
    dsimp [f, Gauss.chi]
    split_ifs <;> simp
  have hcorr : ∀ i : I, |∑ x : Fin p × Bool → ZMod 2, f i false x * f i true x| ≤
      (2 : ℤ) ^ (2 * p - (d - 1)) := by
    intro i
    obtain ⟨u, v, huv⟩ := hpol i
    have hg := h5_line_gauss_restrict_bound e a hzero u v
      (fun z => phase (param (i, false, z)) + phase (param (i, true, z))) ha huv
    simpa only [f, Gauss.chi_add] using hg
  have hsum : (∑ i, ∑ b, ∑ x, f i b x) = ∑ x : E, Gauss.chi (phase x) := by
    have h := Equiv.sum_comp param (fun x : E => Gauss.chi (phase x))
    simpa only [Fintype.sum_prod_type, f] using h
  have hp := h5_family_pair_bound f ((2 : ℤ) ^ (2 * p - (d - 1))) hf hcorr
  have hH : (Fintype.card (Fin p × Bool → ZMod 2) : ℤ) = (2 : ℤ) ^ (2 * p) := by
    simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
      ZMod.card, Nat.cast_pow, Nat.cast_ofNat]
    rw [Nat.mul_comm]
  rw [hsum, hH] at hp
  have hn : (∑ x : E, Gauss.chi (phase x)).natAbs ≤
      Fintype.card I * (2 ^ (2 * p) + 2 ^ (2 * p - (d - 1))) := by
    have hc : ((∑ x : E, Gauss.chi (phase x)).natAbs : ℤ) ≤
        ((Fintype.card I * (2 ^ (2 * p) + 2 ^ (2 * p - (d - 1))) : ℕ) : ℤ) := by
      simpa only [Int.natCast_natAbs, Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat] using hp
    exact_mod_cast hc
  have hdm : d ≤ m := by
    have hw : h5BitWeight a ≤ m :=
      (Finset.card_filter_le _ _).trans_eq (Finset.card_fin m)
    omega
  have hdp : d ≤ p := by
    have hw : h5BitWeight (fun i => a (e i)) ≤ p :=
      (Finset.card_filter_le _ _).trans_eq (Finset.card_fin p)
    rw [h5_weight_restrict_zero_outside e a hzero] at hw
    omega
  have hscale := h5_line_pair_scaling m p d hd hdm hdp
  calc
    2 ^ (m + 2) * (∑ x : E, Gauss.chi (phase x)).natAbs ≤
        2 ^ (m + 2) * (Fintype.card I * (2 ^ (2 * p) + 2 ^ (2 * p - (d - 1)))) :=
      Nat.mul_le_mul_left _ hn
    _ = Fintype.card I *
        (2 ^ (m + 2) * (2 ^ (2 * p) + 2 ^ (2 * p - (d - 1)))) := by ring
    _ = Fintype.card I * (2 ^ (2 * p + 2) * (2 ^ m + 2 ^ (m + 1 - d))) := by rw [hscale]
    _ = (Fintype.card I * 2 ^ (2 * p)) * 2 ^ 2 * (2 ^ m + 2 ^ (m + 1 - d)) := by
      rw [pow_add]
      ring
    _ = 2 ^ (2 * m + r + 2) * (2 ^ m + 2 ^ (m + 1 - d)) := by
      rw [hcard, pow_add]
      ring

end h5_part_33


section h5_part_34

lemma h5_polar_affine {J : Type*} [Fintype J]
    (c : ZMod 2) (l x y : J → ZMod 2) :
    Gauss.polar (fun z => c + dotProduct l z) x y = 0 := by
  simp only [Gauss.polar, dotProduct_add, dotProduct_zero, add_zero]
  ring_nf
  simp only [show (2 : ZMod 2) = 0 from rfl, show (4 : ZMod 2) = 0 from rfl,
    mul_zero, add_zero]

lemma h5_product_polar_right {J : Type*} [Fintype J]
    (u v : J → ZMod 2) (u0 v0 : ZMod 2) (x y : J → ZMod 2) :
    Gauss.polar (fun z => (u0 + dotProduct u z) * (v0 + dotProduct v z)) x y =
      dotProduct ((Matrix.vecMulVec u v + Matrix.vecMulVec v u).mulVec x) y := by
  have h := h5_affine_product_polar u v u0 v0 y x
  rw [dotProduct_comm y] at h
  simp only [Gauss.polar, dotProduct_zero, add_zero]
  convert h using 1
  rw [add_comm x y]
  ring

lemma h5_pair_switch_polar_scalar (a c b0 b1 d0 d1 x0 x1 y0 y1 : ZMod 2) :
    ((c+a)*(d0+(x0+y0))*(d1+(x1+y1))+c*(b0+(x0+y0))*(b1+(x1+y1))) +
      ((c+a)*(d0+x0)*(d1+x1)+c*(b0+x0)*(b1+x1)) +
      ((c+a)*(d0+y0)*(d1+y1)+c*(b0+y0)*(b1+y1)) +
      ((c+a)*d0*d1+c*b0*b1) = a*(x0*y1+y0*x1) := by
  ring_nf
  simp only [show (2 : ZMod 2) = 0 from rfl, show (4 : ZMod 2) = 0 from rfl,
    mul_zero, add_zero, zero_add]

lemma h5_data_pair_difference_polar {J : Type*} [Fintype J] {m : ℕ}
    (c a b0 b1 d0 d1 : Fin m → ZMod 2)
    (H0 H1 : (J → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2))
    (x y : J → ZMod 2) :
    Gauss.polar (fun z : J → ZMod 2 => ∑ i : Fin m,
      ((c i+a i)*(d0 i+H0 z i)*(d1 i+H1 z i)+c i*(b0 i+H0 z i)*(b1 i+H1 z i))) x y =
      ∑ i : Fin m, a i * (H0 x i * H1 y i + H0 y i * H1 x i) := by
  simp only [Gauss.polar, map_add, map_zero, Pi.add_apply, Pi.zero_apply, add_zero,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ =>
    h5_pair_switch_polar_scalar (a i) (c i) (b0 i) (b1 i) (d0 i) (d1 i)
      (H0 x i) (H1 x i) (H0 y i) (H1 y i))

lemma h5_pair_diagonal_mulVec {m : ℕ} (a : Fin m → ZMod 2)
    (x : Fin m × Bool → ZMod 2) (i : Fin m) (b : Bool) :
    (h5PairDiagonal a).mulVec x (i,b) = a i * x (i,!b) := by
  cases b <;> simp [Matrix.mulVec, dotProduct, h5_pair_diagonal_apply, Fintype.sum_prod_type]

lemma h5_pair_diagonal_dot {m : ℕ} (a : Fin m → ZMod 2)
    (x y : Fin m × Bool → ZMod 2) :
    dotProduct ((h5PairDiagonal a).mulVec x) y =
      ∑ i : Fin m, a i * (x (i,false)*y (i,true)+x (i,true)*y (i,false)) := by
  simp only [dotProduct, Fintype.sum_prod_type, h5_pair_diagonal_mulVec,
    Fintype.sum_bool, Bool.not_true, Bool.not_false]
  exact Finset.sum_congr rfl (fun i _ => by ring)

lemma h5_data_pair_difference_retained_polar {m p : ℕ}
    (e : Fin p ↪ Fin m) (c a b0 b1 d0 d1 : Fin m → ZMod 2)
    (hzero : ∀ i, i ∉ Set.range e → a i = 0)
    (H0 H1 : (Fin p × Bool → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2))
    (hH0 : ∀ z i, H0 z (e i) = z (i,false))
    (hH1 : ∀ z i, H1 z (e i) = z (i,true))
    (x y : Fin p × Bool → ZMod 2) :
    Gauss.polar (fun z : Fin p × Bool → ZMod 2 => ∑ i : Fin m,
      ((c i+a i)*(d0 i+H0 z i)*(d1 i+H1 z i)+c i*(b0 i+H0 z i)*(b1 i+H1 z i))) x y =
      dotProduct ((h5PairDiagonal (fun i => a (e i))).mulVec x) y := by
  classical
  rw [h5_data_pair_difference_polar, h5_pair_diagonal_dot]
  let f : Fin m → ZMod 2 := fun i => a i*(H0 x i*H1 y i+H0 y i*H1 x i)
  have hsum : (∑ i ∈ (Finset.univ : Finset (Fin p)).image e, f i) = ∑ i, f i := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i hi hni
    have hr : i ∉ Set.range e := by
      simpa only [Finset.mem_image, Finset.mem_univ, true_and, Set.mem_range] using hni
    simp only [f, hzero i hr, zero_mul]
  rw [← hsum, Finset.sum_image (fun i _ j _ hij => e.injective hij)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [f, hH0, hH1]
  ring

end h5_part_34

section h5_part_35

lemma h5_fd_add_self (a : ZMod 2) : a + a = 0 := by decide +revert

lemma h5_fd_linear_dot {n : ℕ} {J : Type*} [Fintype J] [DecidableEq J]
    (H : (J → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (u : Fin n → ZMod 2) (x : J → ZMod 2) :
    dotProduct u (H x) = dotProduct (fun j => dotProduct u (H (Pi.single j 1))) x := by
  classical
  have hx : x = ∑ j : J, x j • Pi.single j (1 : ZMod 2) := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx, map_sum, dotProduct_sum]
  simp only [map_smul, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma h5_fd_affine_comp {n : ℕ} {J : Type*} [Fintype J] [DecidableEq J]
    (H : (J → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (p u : Fin n → ZMod 2) (u0 : ZMod 2) :
    ∃ (c : ZMod 2) (l : J → ZMod 2),
      ∀ x, u0 + dotProduct u (p + H x) = c + dotProduct l x := by
  refine ⟨u0 + dotProduct u p, fun j => dotProduct u (H (Pi.single j 1)), ?_⟩
  intro x
  rw [dotProduct_add, h5_fd_linear_dot]
  ring

lemma h5_fd_quad_polar {n : ℕ} (b : ZMod 2) (a : Fin n → ZMod 2)
    (M : Matrix (Fin n) (Fin n) (ZMod 2)) (q : (Fin n → ZMod 2) → ZMod 2)
    (hq : ∀ x, q x = b + dotProduct a x + ∑ i, ∑ j, M i j * x i * x j)
    (h t : Fin n → ZMod 2) :
    q (h + t) + q h + q t + q 0 = dotProduct h ((M + M.transpose).mulVec t) := by
  rw [hq (h + t), hq h, hq t, hq 0]
  simp only [Pi.add_apply, Pi.zero_apply, dotProduct_zero, mul_zero, Finset.sum_const_zero, add_zero, dotProduct_add]
  have hba : (b + (dotProduct a h + dotProduct a t) +
      ∑ i, ∑ j, M i j * (h i + t i) * (h j + t j)) +
      (b + dotProduct a h + ∑ i, ∑ j, M i j * h i * h j) +
      (b + dotProduct a t + ∑ i, ∑ j, M i j * t i * t j) + b =
      ((∑ i, ∑ j, M i j * (h i + t i) * (h j + t j)) +
        (∑ i, ∑ j, M i j * h i * h j) +
        (∑ i, ∑ j, M i j * t i * t j)) := by
    calc _ = (b + b) + (b + b) + (dotProduct a h + dotProduct a h) +
          (dotProduct a t + dotProduct a t) +
          ((∑ i, ∑ j, M i j * (h i + t i) * (h j + t j)) +
            (∑ i, ∑ j, M i j * h i * h j) +
            (∑ i, ∑ j, M i j * t i * t j)) := by ring
      _ = _ := by simp only [h5_fd_add_self, zero_add]
  rw [hba]
  have hterm : ∀ i j : Fin n,
      M i j * (h i + t i) * (h j + t j) + M i j * h i * h j + M i j * t i * t j =
      M i j * h i * t j + M i j * t i * h j := by
    intro i j
    calc _ = (M i j * h i * h j + M i j * h i * h j) +
          (M i j * t i * t j + M i j * t i * t j) +
          (M i j * h i * t j + M i j * t i * h j) := by ring
      _ = _ := by simp only [h5_fd_add_self, zero_add]
  have hcomb : (∑ i, ∑ j, M i j * (h i + t i) * (h j + t j)) +
      (∑ i, ∑ j, M i j * h i * h j) + (∑ i, ∑ j, M i j * t i * t j) =
      ∑ i, ∑ j, (M i j * h i * t j + M i j * t i * h j) := by
    simp only [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hterm i j
  rw [hcomb]
  simp only [Finset.sum_add_distrib]
  have hswap : (∑ i, ∑ j, M i j * t i * h j) = ∑ i, ∑ j, M j i * h i * t j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hswap, ← Finset.sum_add_distrib]
  simp only [dotProduct, Matrix.mulVec, Matrix.add_apply, Matrix.transpose_apply,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma h5_fd_polar_fiber_difference {n : ℕ} {J : Type*} [Fintype J] [DecidableEq J]
    (q : (Fin n → ZMod 2) → ZMod 2)
    (N : Matrix (Fin n) (Fin n) (ZMod 2))
    (hpolar : ∀ y z, q (y + z) + q y + q z + q 0 = dotProduct y (N.mulVec z))
    (H : (J → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (p δ : Fin n → ZMod 2) :
    ∀ x, q (p + H x + δ) + q (p + H x) =
      (dotProduct p (N.mulVec δ) + q δ + q 0) +
        dotProduct (fun j => dotProduct (N.mulVec δ) (H (Pi.single j 1))) x := by
  intro x
  have hcancel : ∀ a b c d : ZMod 2, (a + b + c + d) + c + d = a + b := by decide
  have hh := congrArg (fun v => v + q δ + q 0) (hpolar (p + H x) δ)
  rw [hcancel] at hh
  rw [hh, add_dotProduct, dotProduct_comm (H x) (N.mulVec δ), h5_fd_linear_dot]
  ring

lemma h5_fd_quad_fiber_difference {n : ℕ} {J : Type*} [Fintype J] [DecidableEq J]
    (q : (Fin n → ZMod 2) → ZMod 2)
    (b : ZMod 2) (a : Fin n → ZMod 2) (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (hq : ∀ y, q y = b + dotProduct a y + ∑ i, ∑ j, M i j * y i * y j)
    (H : (J → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (p δ : Fin n → ZMod 2) :
    ∃ (c : ZMod 2) (l : J → ZMod 2),
      ∀ x, q (p + H x + δ) + q (p + H x) = c + dotProduct l x := by
  refine ⟨dotProduct p ((M + M.transpose).mulVec δ) + q δ + q 0,
    fun j => dotProduct ((M + M.transpose).mulVec δ) (H (Pi.single j 1)), ?_⟩
  exact h5_fd_polar_fiber_difference q (M + M.transpose) (h5_fd_quad_polar b a M q hq) H p δ

lemma h5_fd_triple_first (x y z b c : ZMod 2) :
    (x + 1) * (y + b) * (z + c) + x * y * z =
      (y + b*x + b) * (z + c*x + c) := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;> fin_cases b <;> fin_cases c <;> decide

lemma h5_fd_triple_second (x y z c : ZMod 2) :
    x * (y + 1) * (z + c) + x * y * z = x * (z + c*y + c) := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;> fin_cases c <;> decide

lemma h5_fd_triple_third (x y z : ZMod 2) :
    x * y * (z + 1) + x * y * z = x * y := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;> decide

lemma h5_fd_scalar_triple_factor (a b c : ZMod 2) :
    ∃ u0 u1 u2 u3 v0 v1 v2 v3 : ZMod 2, ∀ x y z : ZMod 2,
      (x+a)*(y+b)*(z+c)+x*y*z =
        (u0+u1*x+u2*y+u3*z)*(v0+v1*x+v2*y+v3*z) := by
  have hbit (x : ZMod 2) : x = 0 ∨ x = 1 := by
    fin_cases x
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hbit a with rfl | rfl
  · rcases hbit b with rfl | rfl
    · rcases hbit c with rfl | rfl
      · refine ⟨0,0,0,0,0,0,0,0,?_⟩
        intro x y z
        fin_cases x <;> fin_cases y <;> fin_cases z <;> decide
      · refine ⟨0,1,0,0,0,0,1,0,?_⟩
        intro x y z
        simpa using h5_fd_triple_third x y z
    · refine ⟨0,1,0,0,c,0,c,1,?_⟩
      intro x y z
      simpa only [zero_mul, one_mul, add_zero, zero_add, add_comm, add_left_comm, add_assoc] using h5_fd_triple_second x y z c
  · refine ⟨b,b,1,0,c,c,0,1,?_⟩
    intro x y z
    simpa only [zero_mul, one_mul, add_zero, zero_add, add_comm, add_left_comm, add_assoc] using h5_fd_triple_first x y z b c

lemma h5_fd_triple_fiber_difference {n : ℕ} {J : Type*} [Fintype J] [DecidableEq J]
    (T : (Fin n → ZMod 2) → ZMod 2)
    (a0 b0 c0 : ZMod 2) (a b c : Fin n → ZMod 2)
    (hT : ∀ y, T y = (a0 + dotProduct a y) * (b0 + dotProduct b y) * (c0 + dotProduct c y))
    (H : (J → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (p δ : Fin n → ZMod 2) :
    ∃ (u0 v0 : ZMod 2) (u v : J → ZMod 2), ∀ x,
      T (p + H x + δ) + T (p + H x) = (u0 + dotProduct u x) * (v0 + dotProduct v x) := by
  obtain ⟨α, a', ha⟩ := h5_fd_affine_comp H p a a0
  obtain ⟨β, b', hb⟩ := h5_fd_affine_comp H p b b0
  obtain ⟨γ, c', hc⟩ := h5_fd_affine_comp H p c c0
  obtain ⟨u0,u1,u2,u3,v0,v1,v2,v3,hfactor⟩ :=
    h5_fd_scalar_triple_factor (dotProduct a δ) (dotProduct b δ) (dotProduct c δ)
  refine ⟨u0 + u1*α + u2*β + u3*γ, v0 + v1*α + v2*β + v3*γ,
    u1 • a' + u2 • b' + u3 • c', v1 • a' + v2 • b' + v3 • c', ?_⟩
  intro x
  have hshift (d : Fin n → ZMod 2) (d0 : ZMod 2) :
      d0 + dotProduct d (p + H x + δ) = (d0 + dotProduct d (p + H x)) + dotProduct d δ := by
    rw [dotProduct_add]
    ring
  rw [hT, hT, hshift a a0, hshift b b0, hshift c c0, ha x, hb x, hc x, hfactor]
  simp only [add_dotProduct, smul_dotProduct, smul_eq_mul]
  ring

lemma h5_fd_quad_triple_fiber_difference {n : ℕ} {J : Type*} [Fintype J] [DecidableEq J]
    (q T : (Fin n → ZMod 2) → ZMod 2)
    (d : ZMod 2) (l : Fin n → ZMod 2) (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (hq : ∀ y, q y = d + dotProduct l y + ∑ i, ∑ j, M i j * y i * y j)
    (a0 b0 c0 : ZMod 2) (a b c : Fin n → ZMod 2)
    (hT : ∀ y, T y = (a0 + dotProduct a y) * (b0 + dotProduct b y) * (c0 + dotProduct c y))
    (H : (J → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (p δ : Fin n → ZMod 2) :
    ∃ (d' u0 v0 : ZMod 2) (l' u v : J → ZMod 2), ∀ x,
      (q (p + H x + δ) + T (p + H x + δ)) +
        (q (p + H x) + T (p + H x)) =
      d' + dotProduct l' x + (u0 + dotProduct u x) * (v0 + dotProduct v x) := by
  obtain ⟨d', l', hq'⟩ := h5_fd_quad_fiber_difference q d l M hq H p δ
  obtain ⟨u0, v0, u, v, hT'⟩ := h5_fd_triple_fiber_difference T a0 b0 c0 a b c hT H p δ
  refine ⟨d', u0, v0, l', u, v, ?_⟩
  intro x
  calc
    (q (p + H x + δ) + T (p + H x + δ)) +
        (q (p + H x) + T (p + H x)) =
      (q (p + H x + δ) + q (p + H x)) +
        (T (p + H x + δ) + T (p + H x)) := by ring
    _ = _ := by rw [hq' x, hT' x]

end h5_part_35


section h5_part_36

lemma h5_line_flat_of_local_paired_polars
    {E I : Type*} [Fintype E] [Fintype I]
    {m r p d : ℕ} (hd : 0 < d)
    (e : Fin p ↪ Fin m) (a : Fin m → ZMod 2)
    (hzero : ∀ i, i ∉ Set.range e → a i = 0)
    (ha : d ≤ h5BitWeight a)
    (param : (I × (Bool × (Fin p × Bool → ZMod 2))) ≃ E)
    (hcard : Fintype.card I * 2 ^ (2 * p) = 2 ^ (2 * m + r))
    (phase : E → ZMod 2)
    (hpol : ∀ i : I, ∃ u v : Fin p × Bool → ZMod 2,
      ∀ x y : Fin p × Bool → ZMod 2,
        Gauss.polar (fun z => phase (param (i, false, z)) + phase (param (i, true, z))) x y =
          dotProduct ((h5PairDiagonal (fun j => a (e j)) +
            (Matrix.vecMulVec u v + Matrix.vecMulVec v u)).mulVec x) y) :
    2 ^ (m + 2) * (∑ x : E, Gauss.chi (phase x)).natAbs ≤
      2 ^ (2 * m + r + 2) * (2 ^ m + 2 ^ (m + 1 - d)) := by
  classical
  apply h5_line_flat_of_paired_polars hd e a hzero ha param hcard phase
  intro i
  obtain ⟨u,v,huv⟩ := hpol i
  let f : Fin p × Bool → Fin m × Bool := fun q => (e q.1, q.2)
  have hf : Function.Injective f := by
    intro x y hxy
    apply Prod.ext
    · exact e.injective (congrArg (fun q : Fin m × Bool => q.1) hxy)
    · exact congrArg (fun q : Fin m × Bool => q.2) hxy
  let u' := Function.extend f u (fun _ => 0)
  let v' := Function.extend f v (fun _ => 0)
  refine ⟨u',v',?_⟩
  intro x y
  have heq : (h5PairDiagonal a + (Matrix.vecMulVec u' v' + Matrix.vecMulVec v' u')).submatrix f f =
      h5PairDiagonal (fun j => a (e j)) + (Matrix.vecMulVec u v + Matrix.vecMulVec v u) := by
    ext x y
    simp only [Matrix.submatrix_apply, Matrix.add_apply, Matrix.vecMulVec_apply,
      u', v', hf.extend_apply, f, h5_pair_diagonal_apply, e.injective.eq_iff]
  rw [show (fun q : Fin p × Bool => (e q.1,q.2)) = f from rfl, heq]
  exact huv x y

def h5SelectorPhase {n k m : ℕ}
    (A : Fin m → Fin k → ZMod 2) (h : (Fin k → ZMod 2) → ZMod 2)
    (s0 : Fin k → ZMod 2) (b0 b1 : Fin m → ZMod 2)
    (S : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2))
    (X Y : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2))
    (q T : (Fin n → ZMod 2) → ZMod 2) (z : Fin n → ZMod 2) : ZMod 2 :=
  h (s0 + S z) + (∑ i, dotProduct (A i) (s0 + S z) * (b0 + X z) i * (b1 + Y z) i) + q z + T z

lemma h5_selector_phase_pair_polar {n k m p : ℕ}
    (e : Fin p ↪ Fin m)
    (A : Fin m → Fin k → ZMod 2) (h : (Fin k → ZMod 2) → ZMod 2)
    (s0 : Fin k → ZMod 2) (b0 b1 : Fin m → ZMod 2)
    (S : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2))
    (X Y : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2))
    (q T : (Fin n → ZMod 2) → ZMod 2)
    (qd : ZMod 2) (ql : Fin n → ZMod 2) (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (hq : ∀ y, q y = qd + dotProduct ql y + ∑ i, ∑ j, M i j * y i * y j)
    (ta0 tb0 tc0 : ZMod 2) (ta tb tc : Fin n → ZMod 2)
    (hT : ∀ y, T y = (ta0 + dotProduct ta y) * (tb0 + dotProduct tb y) * (tc0 + dotProduct tc y))
    (H : (Fin p × Bool → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (anchor δ : Fin n → ZMod 2)
    (hSH : ∀ z, S (H z) = 0)
    (hXH : ∀ z i, X (H z) (e i) = z (i,false))
    (hYH : ∀ z i, Y (H z) (e i) = z (i,true))
    (hzero : ∀ i, i ∉ Set.range e → dotProduct (A i) (S δ) = 0) :
    ∃ u v : Fin p × Bool → ZMod 2, ∀ x y,
      Gauss.polar (fun z =>
        h5SelectorPhase A h s0 b0 b1 S X Y q T (anchor + H z + δ) +
        h5SelectorPhase A h s0 b0 b1 S X Y q T (anchor + H z)) x y =
      dotProduct ((h5PairDiagonal (fun i => dotProduct (A (e i)) (S δ)) +
        (Matrix.vecMulVec u v + Matrix.vecMulVec v u)).mulVec x) y := by
  classical
  obtain ⟨d',u0,v0,l,u,v,hqt⟩ := h5_fd_quad_triple_fiber_difference
    q T qd ql M hq ta0 tb0 tc0 ta tb tc hT H anchor δ
  let c : Fin m → ZMod 2 := fun i => dotProduct (A i) (s0 + S anchor)
  let a : Fin m → ZMod 2 := fun i => dotProduct (A i) (S δ)
  let r0 := b0 + X anchor
  let r1 := b1 + Y anchor
  let t0 := r0 + X δ
  let t1 := r1 + Y δ
  let H0 := X.comp H
  let H1 := Y.comp H
  let data : (Fin p × Bool → ZMod 2) → ZMod 2 := fun z => ∑ i : Fin m,
    ((c i+a i)*(t0 i+H0 z i)*(t1 i+H1 z i)+c i*(r0 i+H0 z i)*(r1 i+H1 z i))
  let hc := h (s0 + S anchor + S δ) + h (s0 + S anchor)
  have hphase : ∀ z,
      h5SelectorPhase A h s0 b0 b1 S X Y q T (anchor + H z + δ) +
        h5SelectorPhase A h s0 b0 b1 S X Y q T (anchor + H z) =
      ((hc + d') + dotProduct l z) + data z +
        (u0 + dotProduct u z)*(v0 + dotProduct v z) := by
    intro z
    have hs0 : s0 + S (anchor + H z) = s0 + S anchor := by rw [map_add, hSH, add_zero]
    have hs1 : s0 + S (anchor + H z + δ) = s0 + S anchor + S δ := by
      rw [map_add, map_add, hSH, add_zero, add_assoc]
    have hbase (i : Fin m) :
        dotProduct (A i) (s0 + S (anchor + H z)) * (b0 + X (anchor + H z)) i * (b1 + Y (anchor + H z)) i =
        c i*(r0 i+H0 z i)*(r1 i+H1 z i) := by
      rw [hs0]
      simp only [map_add, Pi.add_apply, H0, H1, LinearMap.comp_apply, c, r0, r1]
      ring
    have hshift (i : Fin m) :
        dotProduct (A i) (s0 + S (anchor + H z + δ)) *
          (b0 + X (anchor + H z + δ)) i * (b1 + Y (anchor + H z + δ)) i =
        (c i+a i)*(t0 i+H0 z i)*(t1 i+H1 z i) := by
      rw [hs1, dotProduct_add]
      simp only [map_add, Pi.add_apply, H0, H1, LinearMap.comp_apply, c, a, t0, t1, r0, r1]
      ring
    simp only [h5SelectorPhase, hbase, hshift]
    rw [hs0, hs1]
    have hd : data z =
        (∑ i : Fin m, (c i+a i)*(t0 i+H0 z i)*(t1 i+H1 z i)) +
          (∑ i : Fin m, c i*(r0 i+H0 z i)*(r1 i+H1 z i)) := by
      simp only [data, Finset.sum_add_distrib]
    rw [hd]
    have ht := hqt z
    calc
      _ = hc + ((q (anchor + H z + δ) + T (anchor + H z + δ)) +
          (q (anchor + H z) + T (anchor + H z))) +
          ((∑ i : Fin m, (c i+a i)*(t0 i+H0 z i)*(t1 i+H1 z i)) +
          (∑ i : Fin m, c i*(r0 i+H0 z i)*(r1 i+H1 z i))) := by
        dsimp only [hc]
        ring
      _ = _ := by rw [ht]; dsimp only [hc]; ring
  refine ⟨u,v,?_⟩
  intro x y
  have hfun := funext hphase
  rw [hfun, h5_polar_add, h5_polar_add, h5_polar_affine, zero_add,
    h5_product_polar_right]
  have hdata := h5_data_pair_difference_retained_polar e c a r0 r1 t0 t1 hzero H0 H1 hXH hYH x y
  change Gauss.polar data x y = _ at hdata
  simp only [hdata, Matrix.add_mulVec, add_dotProduct, a]

end h5_part_36

section h5_part_37

def h5_pp_boolEquiv : Bool ≃ ZMod 2 where
  toFun b := if b then 1 else 0
  invFun a := decide (a = 1)
  left_inv b := by cases b <;> decide
  right_inv := by decide

lemma h5_pp_extend_injective {n : ℕ} {J : Type*} [Fintype J]
    (H : (J → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (hH : Function.Injective H) (δ : Fin n → ZMod 2)
    (hδ : δ ∉ LinearMap.range H) :
    Function.Injective ((LinearMap.toSpanSingleton (ZMod 2) (Fin n → ZMod 2) δ).coprod H) := by
  let K := (LinearMap.toSpanSingleton (ZMod 2) (Fin n → ZMod 2) δ).coprod H
  have htwo : ∀ a : ZMod 2, a + a = 0 := by decide
  have hδδ : δ + δ = 0 := by ext i; exact htwo _
  have hzero : ∀ x : ZMod 2 × (J → ZMod 2), K x = 0 → x = 0 := by
    rintro ⟨b, z⟩ hx
    have hb : b = 0 ∨ b = 1 := (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) b
    rcases hb with rfl | rfl
    · have hz : H z = 0 := by simpa [K, LinearMap.toSpanSingleton_apply] using hx
      have hz0 : z = 0 := hH (by simpa using hz)
      exact Prod.ext rfl hz0
    · have hx' : δ + H z = 0 := by simpa [K, LinearMap.toSpanSingleton_apply] using hx
      exfalso
      apply hδ
      refine ⟨z, ?_⟩
      calc
        H z = (δ + δ) + H z := by rw [hδδ, zero_add]
        _ = δ + (δ + H z) := add_assoc _ _ _
        _ = δ := by rw [hx', add_zero]
  intro x y hxy
  apply sub_eq_zero.mp
  apply hzero
  rw [map_sub, hxy, sub_self]

lemma h5_pp_paired_parametrization {n : ℕ} {J : Type*} [Fintype J]
    (H : (J → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (hH : Function.Injective H) (δ : Fin n → ZMod 2)
    (hδ : δ ∉ LinearMap.range H) :
    ∃ (W : Submodule (ZMod 2) (Fin n → ZMod 2))
      (e : (W × Bool × (J → ZMod 2)) ≃ (Fin n → ZMod 2)),
      (∀ (w : W) (b : Bool) (z : J → ZMod 2),
        e (w, b, z) = (w : Fin n → ZMod 2) + H z + if b then δ else 0) ∧
      ∀ (w : W) (z : J → ZMod 2), e (w, true, z) = e (w, false, z) + δ := by
  classical
  let K : (ZMod 2 × (J → ZMod 2)) →ₗ[ZMod 2] (Fin n → ZMod 2) :=
    (LinearMap.toSpanSingleton (ZMod 2) (Fin n → ZMod 2) δ).coprod H
  have hK : Function.Injective K := h5_pp_extend_injective H hH δ hδ
  obtain ⟨W, hW⟩ := (LinearMap.range K).exists_isCompl
  let eK : (ZMod 2 × (J → ZMod 2)) ≃ₗ[ZMod 2] LinearMap.range K :=
    LinearEquiv.ofInjective K hK
  let eB : (Bool × (J → ZMod 2)) ≃ (ZMod 2 × (J → ZMod 2)) :=
    Equiv.prodCongr h5_pp_boolEquiv (Equiv.refl _)
  let eW : (W × LinearMap.range K) ≃ₗ[ZMod 2] (Fin n → ZMod 2) :=
    Submodule.prodEquivOfIsCompl W (LinearMap.range K) hW.symm
  let e : (W × Bool × (J → ZMod 2)) ≃ (Fin n → ZMod 2) :=
    (Equiv.prodCongr (Equiv.refl W) (eB.trans eK.toEquiv)).trans eW.toEquiv
  have he : ∀ (w : W) (b : Bool) (z : J → ZMod 2),
      e (w, b, z) = (w : Fin n → ZMod 2) + H z + if b then δ else 0 := by
    intro w b z
    change (w : Fin n → ZMod 2) + ((if b then (1 : ZMod 2) else 0) • δ + H z) = _
    cases b <;> simp [add_comm, add_left_comm]
  refine ⟨W, e, he, ?_⟩
  intro w z
  rw [he, he]
  simp

lemma h5_pp_card_of_equiv {n : ℕ} {J I : Type*} [Fintype J] [Fintype I]
    (e : (I × Bool × (J → ZMod 2)) ≃ (Fin n → ZMod 2)) :
    Fintype.card I * 2 * 2 ^ Fintype.card J = 2 ^ n := by
  classical
  have h := Fintype.card_congr e
  simpa [ZMod.card, Nat.mul_assoc] using h

lemma h5_pp_pair_card_of_equiv {m r p : ℕ} {I : Type*} [Fintype I]
    (e : (I × Bool × ((Fin p × Bool) → ZMod 2)) ≃
      (Fin (2 * m + r + 1) → ZMod 2)) :
    Fintype.card I * 2 ^ (2 * p) = 2 ^ (2 * m + r) := by
  have h := h5_pp_card_of_equiv e
  apply Nat.eq_of_mul_eq_mul_right (by decide : 0 < 2)
  simpa [Fintype.card_prod, pow_succ, Nat.mul_assoc, Nat.mul_comm,
    Nat.mul_left_comm] using h

end h5_part_37

section h5_part_38

lemma h5_line_section_injective {n m p : ℕ}
    (e : Fin p ↪ Fin m)
    (X Y : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2))
    (H : (Fin p × Bool → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (hXH : ∀ z i, X (H z) (e i) = z (i,false))
    (hYH : ∀ z i, Y (H z) (e i) = z (i,true)) :
    Function.Injective H := by
  intro z w h
  funext j
  rcases j with ⟨i,b⟩
  cases b
  · rw [←hXH z i, ←hXH w i, h]
  · rw [←hYH z i, ←hYH w i, h]

lemma h5_line_flat_of_section {k m p r d : ℕ}
    (hd : 0 < d) (e : Fin p ↪ Fin m)
    (A : Fin m → Fin k → ZMod 2) (h : (Fin k → ZMod 2) → ZMod 2)
    (s0 : Fin k → ZMod 2) (b0 b1 : Fin m → ZMod 2)
    (S : (Fin (2*m+r+1) → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2))
    (X Y : (Fin (2*m+r+1) → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2))
    (q T : (Fin (2*m+r+1) → ZMod 2) → ZMod 2)
    (qd : ZMod 2) (ql : Fin (2*m+r+1) → ZMod 2)
    (M : Matrix (Fin (2*m+r+1)) (Fin (2*m+r+1)) (ZMod 2))
    (hq : ∀ y, q y = qd + dotProduct ql y + ∑ i, ∑ j, M i j * y i * y j)
    (ta0 tb0 tc0 : ZMod 2) (ta tb tc : Fin (2*m+r+1) → ZMod 2)
    (hT : ∀ y, T y = (ta0 + dotProduct ta y) * (tb0 + dotProduct tb y) * (tc0 + dotProduct tc y))
    (H : (Fin p × Bool → ZMod 2) →ₗ[ZMod 2] (Fin (2*m+r+1) → ZMod 2))
    (δ : Fin (2*m+r+1) → ZMod 2)
    (hSH : ∀ z, S (H z) = 0)
    (hXH : ∀ z i, X (H z) (e i) = z (i,false))
    (hYH : ∀ z i, Y (H z) (e i) = z (i,true))
    (hδ : S δ ≠ 0)
    (hzero : ∀ i, i ∉ Set.range e → dotProduct (A i) (S δ) = 0)
    (ha : d ≤ h5BitWeight (fun i => dotProduct (A i) (S δ))) :
    2 ^ (m + 2) * (∑ x, Gauss.chi (h5SelectorPhase A h s0 b0 b1 S X Y q T x)).natAbs ≤
      2 ^ (2 * m + r + 2) * (2 ^ m + 2 ^ (m + 1 - d)) := by
  classical
  have hH := h5_line_section_injective e X Y H hXH hYH
  have hδH : δ ∉ LinearMap.range H := by
    rintro ⟨z,hz⟩
    apply hδ
    rw [←hz, hSH]
  obtain ⟨W,param,hparam,hpair⟩ := h5_pp_paired_parametrization H hH δ hδH
  let : Fintype W := Fintype.ofFinite W
  have hc := h5_pp_pair_card_of_equiv param
  apply h5_line_flat_of_local_paired_polars hd e
    (fun i => dotProduct (A i) (S δ)) hzero ha param hc
  intro w
  obtain ⟨u,v,huv⟩ := h5_selector_phase_pair_polar e A h s0 b0 b1 S X Y q T
    qd ql M hq ta0 tb0 tc0 ta tb tc hT H (w : Fin (2*m+r+1) → ZMod 2) δ
    hSH hXH hYH hzero
  refine ⟨u,v,?_⟩
  intro x y
  have hf : (fun z =>
      h5SelectorPhase A h s0 b0 b1 S X Y q T (param (w,false,z)) +
      h5SelectorPhase A h s0 b0 b1 S X Y q T (param (w,true,z))) =
      (fun z => h5SelectorPhase A h s0 b0 b1 S X Y q T (↑w+H z+δ) +
        h5SelectorPhase A h s0 b0 b1 S X Y q T (↑w+H z)) := by
    funext z
    rw [hparam,hparam]
    simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
    exact add_comm _ _
  rw [hf]
  exact huv x y

end h5_part_38

section h5_part_39

end h5_part_39

section h5_part_40

lemma h5_line_flat_of_deleted_section {k m r d : ℕ}
    (hd : 0 < d)
    (A : Fin m → Fin k → ZMod 2) (h : (Fin k → ZMod 2) → ZMod 2)
    (s0 : Fin k → ZMod 2) (b0 b1 : Fin m → ZMod 2)
    (S : (Fin (2*m+r+1) → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2))
    (X Y : (Fin (2*m+r+1) → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2))
    (q T : (Fin (2*m+r+1) → ZMod 2) → ZMod 2)
    (qd : ZMod 2) (ql : Fin (2*m+r+1) → ZMod 2)
    (M : Matrix (Fin (2*m+r+1)) (Fin (2*m+r+1)) (ZMod 2))
    (hq : ∀ y, q y = qd + dotProduct ql y + ∑ i, ∑ j, M i j * y i * y j)
    (ta0 tb0 tc0 : ZMod 2) (ta tb tc : Fin (2*m+r+1) → ZMod 2)
    (hT : ∀ y, T y = (ta0 + dotProduct ta y) * (tb0 + dotProduct tb y) * (tc0 + dotProduct tc y))
    (J : Finset (Fin m))
    (H : ({i : Fin m // i ∉ J} × Bool → ZMod 2) →ₗ[ZMod 2] (Fin (2*m+r+1) → ZMod 2))
    (hSH : ∀ z, S (H z) = 0)
    (hXH : ∀ z (i : {i : Fin m // i ∉ J}), X (H z) i.val = z (i,false))
    (hYH : ∀ z (i : {i : Fin m // i ∉ J}), Y (H z) i.val = z (i,true))
    (hJ : J.card < Module.finrank (ZMod 2) (LinearMap.range S))
    (hdist : ∀ s : Fin k → ZMod 2, s ≠ 0 →
      d ≤ h5BitWeight (fun i => dotProduct (A i) s)) :
    2 ^ (m + 2) * (∑ x, Gauss.chi (h5SelectorPhase A h s0 b0 b1 S X Y q T x)).natAbs ≤
      2 ^ (2 * m + r + 2) * (2 ^ m + 2 ^ (m + 1 - d)) := by
  classical
  let p := Fintype.card {i : Fin m // i ∉ J}
  let f : Fin p ≃ {i : Fin m // i ∉ J} := (Fintype.equivFin _).symm
  let e : Fin p ↪ Fin m :=
    { toFun := fun i => (f i).val
      inj' := by intro i j h; exact f.injective (Subtype.ext h) }
  let R : (Fin p × Bool → ZMod 2) →ₗ[ZMod 2] ({i : Fin m // i ∉ J} × Bool → ZMod 2) :=
    { toFun := fun z ib => z (f.symm ib.1,ib.2)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let H' := H.comp R
  have hSH' : ∀ z, S (H' z) = 0 := fun z => hSH (R z)
  have hXH' : ∀ z i, X (H' z) (e i) = z (i,false) := by
    intro z i
    change X (H (R z)) (f i).val = _
    rw [hXH]
    simp [R]
  have hYH' : ∀ z i, Y (H' z) (e i) = z (i,true) := by
    intro z i
    change Y (H (R z)) (f i).val = _
    rw [hYH]
    simp [R]
  obtain ⟨a,ha,hane,hazero⟩ := h5_deleted_coordinates_direction A (LinearMap.range S) J hJ
  obtain ⟨δ,hδ⟩ := ha
  have hδne : S δ ≠ 0 := by rwa [hδ]
  have hzero : ∀ i, i ∉ Set.range e → dotProduct (A i) (S δ) = 0 := by
    intro i hi
    rw [hδ]
    apply hazero i
    by_contra hij
    apply hi
    refine ⟨f.symm ⟨i,hij⟩,?_⟩
    change (f (f.symm ⟨i,hij⟩)).val = i
    simp
  exact h5_line_flat_of_section hd e A h s0 b0 b1 S X Y q T qd ql M hq
    ta0 tb0 tc0 ta tb tc hT H' δ hSH' hXH' hYH' hδne hzero (hdist (S δ) hδne)

end h5_part_40

section h5_part_41

lemma h5_line_coordinate_maps {n t k m r : ℕ}
    (e : (Fin n → ZMod 2) ≃ₗ[ZMod 2]
      ((Fin k → ZMod 2) × (Fin m → ZMod 2) × (Fin m → ZMod 2) × (Fin r → ZMod 2)))
    (L : (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (hL : Function.Injective L) :
    ∃ (sel : (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2))
      (X Y : (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2))
      (data : (Fin t → ZMod 2) →ₗ[ZMod 2] ((Fin m × Bool ⊕ Fin r) → ZMod 2)),
      (∀ x, sel x = (e (L x)).1) ∧
      (∀ x, X x = (e (L x)).2.1) ∧
      (∀ x, Y x = (e (L x)).2.2.1) ∧
      (∀ x i, data x (Sum.inl (i,false)) = X x i) ∧
      (∀ x i, data x (Sum.inl (i,true)) = Y x i) ∧
      (∀ x i, data x (Sum.inr i) = (e (L x)).2.2.2 i) ∧
      Function.Injective (sel.prod data) := by
  let F := e.toLinearMap.comp L
  let sel := (LinearMap.fst (ZMod 2) _ _).comp F
  let tail := (LinearMap.snd (ZMod 2) _ _).comp F
  let X := (LinearMap.fst (ZMod 2) _ _).comp tail
  let tail2 := (LinearMap.snd (ZMod 2) _ _).comp tail
  let Y := (LinearMap.fst (ZMod 2) _ _).comp tail2
  let Z := (LinearMap.snd (ZMod 2) _ _).comp tail2
  let data : (Fin t → ZMod 2) →ₗ[ZMod 2] ((Fin m × Bool ⊕ Fin r) → ZMod 2) :=
    { toFun := fun x => Sum.elim (fun q => if q.2 then Y x q.1 else X x q.1) (Z x)
      map_add' := by
        intro x y
        ext j
        rcases j with ⟨i,b⟩ | i
        · cases b <;> simp
        · simp
      map_smul' := by
        intro c x
        ext j
        rcases j with ⟨i,b⟩ | i
        · cases b <;> simp
        · simp }
  refine ⟨sel,X,Y,data,(fun _ => rfl),(fun _ => rfl),(fun _ => rfl),
    (fun _ _ => rfl),(fun _ _ => rfl),(fun _ _ => rfl),?_⟩
  intro x y hxy
  have hs := congrArg Prod.fst hxy
  have hd := congrArg Prod.snd hxy
  apply hL
  apply e.injective
  apply Prod.ext
  · exact hs
  apply Prod.ext
  · funext i
    exact congrFun hd (Sum.inl (i,false))
  · apply Prod.ext
    · funext i
      exact congrFun hd (Sum.inl (i,true))
    · funext i
      exact congrFun hd (Sum.inr i)

lemma h5_line_coordinate_phase {n t k m r : ℕ}
    (e : (Fin n → ZMod 2) ≃ₗ[ZMod 2]
      ((Fin k → ZMod 2) × (Fin m → ZMod 2) × (Fin m → ZMod 2) × (Fin r → ZMod 2)))
    (L : (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (a : Fin n → ZMod 2)
    (A : Fin m → Fin k → ZMod 2) (h : (Fin k → ZMod 2) → ZMod 2)
    (g : (Fin n → ZMod 2) → ZMod 2)
    (hg : ∀ y, g y = h (e y).1 +
      ∑ i, dotProduct (A i) (e y).1 * (e y).2.1 i * (e y).2.2.1 i)
    (sel : (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2))
    (X Y : (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2))
    (hsel : ∀ x, sel x = (e (L x)).1)
    (hX : ∀ x, X x = (e (L x)).2.1)
    (hY : ∀ x, Y x = (e (L x)).2.2.1)
    (q T : (Fin t → ZMod 2) → ZMod 2) (x : Fin t → ZMod 2) :
    g (a + L x) + q x + T x =
      h ((e a).1 + sel x) +
        (∑ i, dotProduct (A i) ((e a).1 + sel x) *
          ((e a).2.1 + X x) i * ((e a).2.2.1 + Y x) i) + q x + T x := by
  rw [hg, map_add, hsel, hX, hY]
  rfl

end h5_part_41

section h5_part_42

lemma h5_line_original_bound_of_geometry {n k m r d : ℕ}
    (hd : 0 < d)
    (e : (Fin n → ZMod 2) ≃ₗ[ZMod 2]
      ((Fin k → ZMod 2) × (Fin m → ZMod 2) × (Fin m → ZMod 2) × (Fin r → ZMod 2)))
    (A : Fin m → Fin k → ZMod 2)
    (hdist : ∀ s : Fin k → ZMod 2, s ≠ 0 → d ≤ h5BitWeight (fun i => dotProduct (A i) s))
    (h : (Fin k → ZMod 2) → ZMod 2)
    (g : (Fin n → ZMod 2) → ZMod 2)
    (hg : ∀ y, g y = h (e y).1 + ∑ i, dotProduct (A i) (e y).1 * (e y).2.1 i * (e y).2.2.1 i)
    (L : (Fin (2*m+r+1) → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (a : Fin n → ZMod 2) (hL : Function.Injective L)
    (q T : (Fin (2*m+r+1) → ZMod 2) → ZMod 2)
    (hq : ∃ (qd : ZMod 2) (ql : Fin (2*m+r+1) → ZMod 2)
      (M : Fin (2*m+r+1) → Fin (2*m+r+1) → ZMod 2),
      ∀ y, q y = qd + dotProduct ql y + ∑ i, ∑ j, M i j * y i * y j)
    (hT : ∃ (ta0 tb0 tc0 : ZMod 2) (ta tb tc : Fin (2*m+r+1) → ZMod 2), ∀ y, T y =
      (ta0 + dotProduct ta y) * (tb0 + dotProduct tb y) * (tc0 + dotProduct tc y))
    (hgeometry : ∀
      (S : (Fin (2*m+r+1) → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2))
      (D : (Fin (2*m+r+1) → ZMod 2) →ₗ[ZMod 2] ((Fin m × Bool ⊕ Fin r) → ZMod 2)),
      Function.Injective (S.prod D) →
      ∃ J : Finset (Fin m), J.card < Module.finrank (ZMod 2) (LinearMap.range S) ∧
        ∃ H : ({i : Fin m // i ∉ J} × Bool → ZMod 2) →ₗ[ZMod 2] (Fin (2*m+r+1) → ZMod 2),
          (∀ z, S (H z) = 0) ∧
          ∀ z (i : {i : Fin m // i ∉ J}) b, D (H z) (Sum.inl (i.val,b)) = z (i,b)) :
    2 ^ (m+2) * (∑ x, if g (a+L x) = q x + T x then (1:ℤ) else -1).natAbs ≤
      2 ^ (2*m+r+2) * (2^m + 2^(m+1-d)) := by
  classical
  obtain ⟨S,X,Y,D,hS,hX,hY,hD0,hD1,hDZ,hinj⟩ := h5_line_coordinate_maps e L hL
  obtain ⟨J,hJ,H,hSH,hDH⟩ := hgeometry S D hinj
  obtain ⟨qd,ql,M,hq⟩ := hq
  obtain ⟨ta0,tb0,tc0,ta,tb,tc,hT⟩ := hT
  have hXH : ∀ z (i : {i : Fin m // i ∉ J}), X (H z) i.val = z (i,false) := by
    intro z i
    rw [←hD0, hDH]
  have hYH : ∀ z (i : {i : Fin m // i ∉ J}), Y (H z) i.val = z (i,true) := by
    intro z i
    rw [←hD1, hDH]
  have hb := h5_line_flat_of_deleted_section hd A h (e a).1 (e a).2.1 (e a).2.2.1
    S X Y q T qd ql M hq ta0 tb0 tc0 ta tb tc hT J H hSH hXH hYH hJ hdist
  have hphase (x : Fin (2*m+r+1) → ZMod 2) :
      g (a+L x) + q x + T x = h5SelectorPhase A h (e a).1 (e a).2.1 (e a).2.2.1 S X Y q T x :=
    h5_line_coordinate_phase e L a A h g hg S X Y hS hX hY q T x
  have hsum : (∑ x, if g (a+L x) = q x + T x then (1:ℤ) else -1) =
      ∑ x, Gauss.chi (h5SelectorPhase A h (e a).1 (e a).2.1 (e a).2.2.1 S X Y q T x) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [Gauss.chi_eq, ←add_assoc, hphase]
  rw [hsum]
  exact hb

end h5_part_42

section h5_part_43

end h5_part_43

section h5_part_44

lemma h5_line_data_dimension (m r : ℕ) :
    Module.finrank (ZMod 2) ((Fin m × Bool ⊕ Fin r) → ZMod 2) + 1 =
      Module.finrank (ZMod 2) (Fin (2*m+r+1) → ZMod 2) := by
  simp [Nat.mul_comm]

lemma h5_line_kernel_section {k m r : ℕ}
    (S : (Fin (2*m+r+1) → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2))
    (D : (Fin (2*m+r+1) → ZMod 2) →ₗ[ZMod 2]
      ((Fin m × Bool ⊕ Fin r) → ZMod 2))
    (hSD : Function.Injective (S.prod D)) :
    ∃ J : Finset (Fin m),
      J.card < Module.finrank (ZMod 2) (LinearMap.range S) ∧
      ∃ H : ({i : Fin m // i ∉ J} × Bool → ZMod 2) →ₗ[ZMod 2]
        (Fin (2*m+r+1) → ZMod 2),
        (∀ z, S (H z) = 0) ∧
        ∀ z (i : {i : Fin m // i ∉ J}) b,
          D (H z) (Sum.inl (i.val,b)) = z (i,b) := by
  classical
  let D0 := D.comp (LinearMap.ker S).subtype
  have hD0 : Function.Injective D0 := by
    intro x y hxy
    apply Subtype.ext
    apply hSD
    apply Prod.ext
    · exact x.property.trans y.property.symm
    · exact hxy
  let W := LinearMap.range D0
  let eW : LinearMap.ker S ≃ₗ[ZMod 2] W := LinearEquiv.ofInjective D0 hD0
  have hW : Module.finrank (ZMod 2) (LinearMap.ker S) =
      Module.finrank (ZMod 2) W := eW.finrank_eq
  have hQ := W.finrank_quotient_add_finrank
  have hS := S.finrank_range_add_finrank_ker
  have hdim := h5_line_data_dimension m r
  have hcodim : Module.finrank (ZMod 2)
      (((Fin m × Bool ⊕ Fin r) → ZMod 2) ⧸ W) + 1 =
        Module.finrank (ZMod 2) (LinearMap.range S) := by
    omega
  obtain ⟨J,hJ,H0,hH0⟩ := h5_paired_coordinate_section W
  let H := (LinearMap.ker S).subtype.comp (eW.symm.toLinearMap.comp H0)
  refine ⟨J,?_,H,?_,?_⟩
  · omega
  · intro z
    exact (eW.symm (H0 z)).property
  · intro z i b
    have hD : D (H z) = (H0 z : (Fin m × Bool ⊕ Fin r) → ZMod 2) := by
      change ((eW (eW.symm (H0 z)) : W) : (Fin m × Bool ⊕ Fin r) → ZMod 2) = _
      rw [eW.apply_symm_apply]
    rw [hD]
    exact hH0 z i b

end h5_part_44
section h5_part_45

lemma h5_line_original_bound {n k m r d : ℕ}
    (hd : 0 < d)
    (e : (Fin n → ZMod 2) ≃ₗ[ZMod 2]
      ((Fin k → ZMod 2) × (Fin m → ZMod 2) × (Fin m → ZMod 2) × (Fin r → ZMod 2)))
    (A : Fin m → Fin k → ZMod 2)
    (hdist : ∀ s : Fin k → ZMod 2, s ≠ 0 → d ≤ h5BitWeight (fun i => dotProduct (A i) s))
    (h : (Fin k → ZMod 2) → ZMod 2)
    (g : (Fin n → ZMod 2) → ZMod 2)
    (hg : ∀ y, g y = h (e y).1 + ∑ i, dotProduct (A i) (e y).1 * (e y).2.1 i * (e y).2.2.1 i)
    (L : (Fin (2*m+r+1) → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (a : Fin n → ZMod 2) (hL : Function.Injective L)
    (q T : (Fin (2*m+r+1) → ZMod 2) → ZMod 2)
    (hq : ∃ (qd : ZMod 2) (ql : Fin (2*m+r+1) → ZMod 2)
      (M : Fin (2*m+r+1) → Fin (2*m+r+1) → ZMod 2),
      ∀ y, q y = qd + dotProduct ql y + ∑ i, ∑ j, M i j * y i * y j)
    (hT : ∃ (ta0 tb0 tc0 : ZMod 2) (ta tb tc : Fin (2*m+r+1) → ZMod 2), ∀ y, T y =
      (ta0 + dotProduct ta y) * (tb0 + dotProduct tb y) * (tc0 + dotProduct tc y))
    :
    2 ^ (m+2) * (∑ x, if g (a+L x) = q x + T x then (1:ℤ) else -1).natAbs ≤
      2 ^ (2*m+r+2) * (2^m + 2^(m+1-d)) := by
  exact h5_line_original_bound_of_geometry hd e A hdist h g hg L a hL q T hq hT
    (fun S D hinj => h5_line_kernel_section S D hinj)

end h5_part_45

end PEqualNP.Outside.L_meta_32057_aux

open PEqualNP.Outside.L_meta_32057_aux

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.L_meta_32057 :
∀ (k m r d : ℕ), 2 ≤ k → 0 < d →
  let n := k+2*m+r
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let F := ZMod 2
  let legal := fun (width : ℕ) (C : Circ) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack width C ∧
      (∀ h ∈ C.gates, h.inputs.length ≤ 2 ∧
        (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1)))
  let cost := fun (C : Circ) => C.gates.countP (fun h => @decide
    ((h.op = .and ∨ h.op = .or) ∧ h.inputs.length = 2) (Classical.propDecidable _))
  let bits := fun (width : ℕ) (u : Fin width → F) => List.ofFn (fun j : Fin width => decide (u j = 1))
  let V := Fin n → F
  let S := Fin k → F
  let D := Fin m → F
  let Z := Fin r → F
  let base := 2*m+r
  ∀ (e : V ≃ₗ[F] S × (D × (D × Z))) (A : Fin m → S),
    let wt := fun (a : S) => ((Finset.univ : Finset (Fin m)).filter
      (fun i => dotProduct (A i) a ≠ 0)).card
    (∀ a : S, a ≠ 0 → d ≤ wt a) → (∃ a : S, a ≠ 0 ∧ wt a = d) →
    ∀ h : S → F,
      let g := fun (y : V) => h (e y).1 + ∑ i : Fin m,
        dotProduct (A i) (e y).1 * (e y).2.1 i * (e y).2.2.1 i
      let raw := fun (C : Circ) => (∑ x : V, ∑ y : V,
        if C.eval (bits n x ++ bits n y) = decide (dotProduct x y + g y = 1)
        then (1 : ℤ) else -1).natAbs
      let b := base+2
      let E := Fin b → F
      let quad := fun (q : E → F) => ∃ (z : F) (l : E) (M : Fin b → Fin b → F),
        ∀ x, q x = z + dotProduct l x + ∑ i, ∑ j, M i j * x i * x j
      let flat := fun (L : E →ₗ[F] V) (a : V) (q : E → F) =>
        (∑ x : E, if g (a+L x) = q x then (1 : ℤ) else -1).natAbs
      let mass := fun (w : S × S) =>
        if w.1 ≠ 0 ∧ w.2 ≠ 0 ∧ w.1 ≠ w.2 then
          2^m + 2^(m-wt w.1) + 2^(m-wt w.2) + 2^(m-wt (w.1+w.2)) else 0
      let plane := (Finset.univ : Finset (S × S)).sup mass
      let line := 2^m + 2^(m+1-d)
      let denom := 2^(m+2)
      (∀ (L : E →ₗ[F] V) (a : V) (q : E → F), Function.Injective L → quad q →
        denom * flat L a q ≤ 2^b * plane) ∧
      (∃ (L : E →ₗ[F] V) (a : V) (q : E → F), Function.Injective L ∧ quad q ∧
        denom * flat L a q = 2^b * plane) ∧
      (∀ C : Circ, legal (2*n) C → cost C ≤ b →
        denom * raw C ≤ 2^(n+b) * max plane line) ∧
      (∃ C : Circ, legal (2*n) C ∧ cost C ≤ b ∧
        denom * raw C = 2^(n+b) * max plane line)
 := by
  classical
  intro k m r d hk hd
  dsimp only
  intro e A hmin hattain h
  let n := k+2*m+r
  let b := 2*m+r+2
  let wt := fun a : Fin k → ZMod 2 =>
    ((Finset.univ : Finset (Fin m)).filter (fun i => dotProduct (A i) a ≠ 0)).card
  let plane := (Finset.univ : Finset ((Fin k → ZMod 2) × (Fin k → ZMod 2))).sup
    (fun w => if w.1 ≠ 0 ∧ w.2 ≠ 0 ∧ w.1 ≠ w.2 then
      (2:ℕ)^m+2^(m-wt w.1)+2^(m-wt w.2)+2^(m-wt (w.1+w.2)) else 0)
  let line := (2:ℕ)^m+2^(m+1-d)
  let g := fun y : Fin n → ZMod 2 => h (e y).1 +
    ∑ i, dotProduct (A i) (e y).1*(e y).2.1 i*(e y).2.2.1 i
  have hg : ∀ y, g y = h (e y).1 +
      ∑ i, dotProduct (A i) (e y).1*(e y).2.1 i*(e y).2.2.1 i := fun _ => rfl
  have hQ : ∀ (B : (Fin b → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
      (a : Fin n → ZMod 2) (q : (Fin b → ZMod 2) → ZMod 2),
      Function.Injective B → Circuit.isQuad q →
      2^(m+2)*Circuit.h5FlatBias g B a q ≤ 2^b*plane := by
    intro B a q hB hq
    exact h5_full_original_bound e A h g hg B a hB q hq
  have hT : ∀ t, t+1=b →
      ∀ (B : (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
        (a : Fin n → ZMod 2) (f : (Fin t → ZMod 2) → ZMod 2),
      Function.Injective B → Circuit.h5IsQuadPlusTriple f →
      2^(m+2)*Circuit.h5FlatBias g B a f ≤ 2^b*line := by
    intro t ht B a f hB hf
    have ht' : t=2*m+r+1 := by dsimp [b] at ht; omega
    subst t
    obtain ⟨q,hq,c0,u0,v0,c,u,v,hf⟩ := hf
    let T := fun y : Fin (2*m+r+1) → ZMod 2 =>
      (c0+dotProduct c y)*(u0+dotProduct u y)*(v0+dotProduct v y)
    have heq : f = fun y => q y+T y := funext hf
    rw [heq]
    exact h5_line_original_bound hd e A hmin h g hg B a hB q T hq
      ⟨c0,u0,v0,c,u,v,fun _ => rfl⟩
  have hP : ∃ (B : (Fin b → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
      (a : Fin n → ZMod 2) (q : (Fin b → ZMod 2) → ZMod 2),
      Function.Injective B ∧ Circuit.isQuad q ∧
      2^(m+2)*Circuit.h5FlatBias g B a q = 2^b*plane := by
    obtain ⟨B,q,hB,hq,heq⟩ := h5_posted_flat_attainment hk e A h
    refine ⟨B,0,q,hB,hq,?_⟩
    simpa only [Circuit.h5FlatBias,zero_add,g] using heq
  have hL : ∃ t, t+1=b ∧
      ∃ (B : (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
        (a : Fin n → ZMod 2) (f : (Fin t → ZMod 2) → ZMod 2),
      Function.Injective B ∧ Circuit.h5IsQuadPlusTriple f ∧
      2^(m+2)*Circuit.h5FlatBias g B a f = 2^b*line := by
    obtain ⟨B,q,f1,f2,f3,hB,hq,heq⟩ := h5_posted_line_attainment hd e A h hattain
    obtain ⟨l1,hl1⟩ := h5_linear_coord_dot f1
    obtain ⟨l2,hl2⟩ := h5_linear_coord_dot f2
    obtain ⟨l3,hl3⟩ := h5_linear_coord_dot f3
    refine ⟨2*m+r+1,by rfl,B,0,fun y => q y+f1 y*f2 y*f3 y,hB,?_,?_⟩
    · refine ⟨q,hq,0,0,0,l1,l2,l3,?_⟩
      intro y
      simp only [zero_add,← hl1,← hl2,← hl3]
    · simpa only [Circuit.h5FlatBias,zero_add,g] using heq
  refine ⟨?_,?_,?_,?_⟩
  · intro L a q hL hq
    exact hQ L a q hL hq
  · exact hP
  · intro C hleg hcost
    exact Circuit.h5_circuit_upper_from_flats n m b plane line g
      (h5_plane_baseline hk m wt) hQ hT C hleg hcost
  · exact Circuit.h5_circuit_attainment_from_flats n m b plane line g hP hL
