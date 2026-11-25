import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2056_aux

def FalseMaximal {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) : Prop :=
  f x = false ∧ ∀ y, (∀ i, x i = true → y i = true) → f y = false → y = x

def Disjunction {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ i ∈ S, x i = true)

theorem disjunction_false_union {n : ℕ} (S : Finset (Fin n))
    (x y : Fin n → Bool) (hx : Disjunction S x = false)
    (hy : Disjunction S y = false) :
    Disjunction S (fun i => x i || y i) = false := by
  simp only [Disjunction, decide_eq_false_iff_not, not_exists, not_and] at hx hy ⊢
  intro i hi
  simp only [Bool.or_eq_true, not_or]
  exact ⟨hx i hi, hy i hi⟩

theorem maximal_false_same_disjunction {n : ℕ}
    (f : (Fin n → Bool) → Bool) (S : Finset (Fin n))
    (hu : ∀ x, f x = true → Disjunction S x = true)
    (x y : Fin n → Bool) (hx : FalseMaximal f x) (hy : FalseMaximal f y)
    (hsx : Disjunction S x = false) (hsy : Disjunction S y = false) : x = y := by
  let z : Fin n → Bool := fun i => x i || y i
  have hsz : Disjunction S z = false := disjunction_false_union S x y hsx hsy
  have hfz : f z = false := by
    cases h : f z
    · rfl
    · have := hu z h
      simp [hsz] at this
  have hzx : z = x := hx.2 z (by intro i hi; simp [z, hi]) hfz
  have hzy : z = y := hy.2 z (by intro i hi; simp [z, hi]) hfz
  exact hzx.symm.trans hzy

theorem maximal_false_card_le_selectors {n : ℕ} {ι : Type*} [Fintype ι]
    (f : (Fin n → Bool) → Bool) (S : ι → Finset (Fin n))
    (hu : ∀ j x, f x = true → Disjunction (S j) x = true)
    (hc : ∀ x, f x = false → ∃ j, Disjunction (S j) x = false) :
    Nat.card {x : Fin n → Bool // FalseMaximal f x} ≤ Fintype.card ι := by
  classical
  let pick (x : {x : Fin n → Bool // FalseMaximal f x}) : ι :=
    Classical.choose (hc x.1 x.2.1)
  have hpick (x : {x : Fin n → Bool // FalseMaximal f x}) :
      Disjunction (S (pick x)) x.1 = false := Classical.choose_spec (hc x.1 x.2.1)
  have hinj : Function.Injective pick := by
    intro x y hxy
    apply Subtype.ext
    exact maximal_false_same_disjunction f (S (pick x)) (hu (pick x))
      x.1 y.1 x.2 y.2 (hpick x) (by simpa only [hxy] using hpick y)
  simpa only [Nat.card_eq_fintype_card] using Fintype.card_le_of_injective pick hinj

theorem maximal_false_card_le_two_pow {n a : ℕ}
    (f : (Fin n → Bool) → Bool) (S : (Fin a → Bool) → Finset (Fin n))
    (hu : ∀ j x, f x = true → Disjunction (S j) x = true)
    (hc : ∀ x, f x = false → ∃ j, Disjunction (S j) x = false) :
    Nat.card {x : Fin n → Bool // FalseMaximal f x} ≤ 2 ^ a := by
  simpa using maximal_false_card_le_selectors f S hu hc

end PEqualNP.Outside.L_meta_2056_aux
