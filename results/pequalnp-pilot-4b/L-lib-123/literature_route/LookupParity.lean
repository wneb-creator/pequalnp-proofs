import Mathlib

namespace PEqualNP.Outside.LiteratureRoute

open scoped BigOperators

def homogeneousBasis {F : Type*} [CommRing F] {d : ℕ}
    (u : Fin d → Bool) (z : Fin d → F) (star : F) : F :=
  ∏ i, if u i then z i else star - z i

def homogeneousBooleanExtension {F : Type*} [CommRing F] {d : ℕ}
    (f : (Fin d → Bool) → Bool) (z : Fin d → F) (star : F) : F :=
  ∑ u, (if f u then 1 else 0) * homogeneousBasis u z star

lemma homogeneousBasis_zero_star {F : Type*} [Field F] [CharP F 2]
    {d : ℕ} (u : Fin d → Bool) :
    homogeneousBasis u (fun _ => (1 : F)) 0 = 1 := by
  have htwo : (1 : F) + 1 = 0 := by
    calc
      (1 : F) + 1 = 2 := by ring
      _ = 0 := CharP.cast_eq_zero F 2
  have hneg : -(1 : F) = 1 := neg_eq_iff_add_eq_zero.mpr htwo
  simp [homogeneousBasis, hneg]

/-- The low-degree Boolean extension of an arbitrary local predicate,
evaluated at this legal field vector, gives its parity count. Evaluating
the ordinary arithmetized circuit at that vector need not do so. -/
lemma homogeneousBooleanExtension_parity {F : Type*}
    [Field F] [CharP F 2] {d : ℕ} (f : (Fin d → Bool) → Bool) :
    homogeneousBooleanExtension f (fun _ => (1 : F)) 0 =
      ∑ u : Fin d → Bool, (if f u then (1 : F) else 0) := by
  simp [homogeneousBooleanExtension, homogeneousBasis_zero_star]

/-- Dense univariate interpolation of r groups with a total of d Boolean
coordinates needs C^r >= 2^d if every message has at most C coefficients.
This concerns this representation, not arbitrary proof systems. -/
lemma grouped_sumcheck_budget (r d C : ℕ) (width : Fin r → ℕ)
    (hwidth : ∑ i, width i = d)
    (hmessage : ∀ i, 2 ^ width i ≤ C) : 2 ^ d ≤ C ^ r := by
  calc
    2 ^ d = ∏ i, 2 ^ width i := by
      rw [Finset.prod_pow_eq_pow_sum, hwidth]
    _ ≤ ∏ _i : Fin r, C := Finset.prod_le_prod (fun i _ => hmessage i)
    _ = C ^ r := by simp

lemma pow_two_exceeds_fixed_linear (K : ℕ) :
    K * ((K + 1) * 2 + 2) < 2 ^ ((K + 1) * 2 + 2) := by
  have hbase : K + 2 ≤ 2 ^ (K + 1) := by
    have := (Nat.lt_two_pow_self : K + 1 < 2 ^ (K + 1))
    omega
  have hsquare := Nat.mul_le_mul hbase hbase
  calc
    K * ((K + 1) * 2 + 2) < 4 * (K + 2) * (K + 2) := by nlinarith
    _ ≤ 4 * (2 ^ (K + 1)) * (2 ^ (K + 1)) := by nlinarith
    _ = 2 ^ ((K + 1) * 2 + 2) := by
      simp only [pow_add, pow_mul, pow_two]
      ring

/-- For any fixed number r of groups and any fixed exponent coefficient k,
some Boolean dimension 2^m cannot fit dense group messages of 2^(k*m)
coefficients. In particular, setting the computation cap to 2^(2*m) makes
the Boolean dimension its square root. -/
lemma grouped_sumcheck_no_fixed_round_power (r k : ℕ) :
    ∃ m : ℕ, ∀ width : Fin r → ℕ, (∑ i, width i) = 2 ^ m →
      ¬ ∀ i, 2 ^ width i ≤ 2 ^ (k * m) := by
  let m := (k * r + 1) * 2 + 2
  refine ⟨m, ?_⟩
  intro width hwidth hmessage
  have hbudget := grouped_sumcheck_budget r (2 ^ m) (2 ^ (k * m))
    width hwidth hmessage
  have hlarge : (k * r) * m < 2 ^ m := pow_two_exceeds_fixed_linear (k * r)
  have hpow := Nat.pow_lt_pow_right (by decide : 1 < 2) hlarge
  have hbad : (2 ^ (k * m)) ^ r < 2 ^ (2 ^ m) := by
    rw [← pow_mul]
    have harg : (k * m) * r = (k * r) * m := by ring
    rw [harg]
    exact hpow
  exact (not_lt_of_ge hbudget) hbad

end PEqualNP.Outside.LiteratureRoute
