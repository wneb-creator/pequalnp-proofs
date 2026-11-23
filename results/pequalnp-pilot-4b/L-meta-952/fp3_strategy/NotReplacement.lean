import Mathlib

namespace PEqualNP.Outside.Meta952Strategy

variable {α : Type*}

def InputLE (x y : α → Bool) : Prop :=
  ∀ i, x i = true → y i = true

def MonotoneBit (h : (α → Bool) → Bool) : Prop :=
  ∀ x y, InputLE x y → h x = true → h y = true

def MonotoneCut (F : (α → Bool) → Bool → Bool) : Prop :=
  ∀ x y, InputLE x y → ∀ a b : Bool,
    (a = true → b = true) → F x a = true → F y b = true

def LineTarget (S : Finset α) (x : α → Bool) : Prop :=
  ∃ i ∈ S, x i = true

def outside [DecidableEq α] (S : Finset α) : α → Bool := fun i => decide (i ∉ S)

def singleton [DecidableEq α] (i : α) : α → Bool := fun j => decide (j = i)

lemma inputLE_refl (x : α → Bool) : InputLE x x := by
  intro i hi
  exact hi

lemma false_target_le_outside [DecidableEq α] (S : Finset α) (x : α → Bool)
    (hx : ¬ LineTarget S x) : InputLE x (outside S) := by
  intro i hi
  simp only [outside, decide_eq_true_eq]
  intro hiS
  exact hx ⟨i, hiS, hi⟩

lemma singleton_le [DecidableEq α] (x : α → Bool) (i : α) (hi : x i = true) :
    InputLE (singleton i) x := by
  intro j hj
  have hji : j = i := by simpa [singleton] using hj
  simpa [hji] using hi

lemma cofactor_lower (S : Finset α) (h : (α → Bool) → Bool)
    (F : (α → Bool) → Bool → Bool) (hF : MonotoneCut F)
    (hreal : ∀ x, F x (!(h x)) = true ↔ LineTarget S x)
    (x : α → Bool) (hx : F x false = true) : LineTarget S x := by
  apply (hreal x).mp
  exact hF x x (inputLE_refl x) false (!(h x)) (by simp) hx

lemma cofactor_upper (S : Finset α) (h : (α → Bool) → Bool)
    (F : (α → Bool) → Bool → Bool) (hF : MonotoneCut F)
    (hreal : ∀ x, F x (!(h x)) = true ↔ LineTarget S x)
    (x : α → Bool) (hx : LineTarget S x) : F x true = true := by
  exact hF x x (inputLE_refl x) (!(h x)) true (by simp) ((hreal x).mpr hx)

lemma replace_not_true [DecidableEq α] (S : Finset α) (h : (α → Bool) → Bool)
    (F : (α → Bool) → Bool → Bool) (hh : MonotoneBit h)
    (hF : MonotoneCut F)
    (hreal : ∀ x, F x (!(h x)) = true ↔ LineTarget S x)
    (houtside : h (outside S) = false) :
    ∀ x, F x true = true ↔ LineTarget S x := by
  intro x
  constructor
  · intro hx
    by_contra hbad
    have horder := false_target_le_outside S x hbad
    have hhx : h x = false := by
      cases hv : h x with
      | false => rfl
      | true =>
        have hc := hh x (outside S) horder hv
        simp [houtside] at hc
    have ht : LineTarget S x := (hreal x).mp (by simpa [hhx] using hx)
    exact hbad ht
  · exact cofactor_upper S h F hF hreal x

lemma replace_not_false [DecidableEq α] (S : Finset α) (h : (α → Bool) → Bool)
    (F : (α → Bool) → Bool → Bool) (hh : MonotoneBit h)
    (hF : MonotoneCut F)
    (hreal : ∀ x, F x (!(h x)) = true ↔ LineTarget S x)
    (hsingle : ∀ i ∈ S, h (singleton i) = true) :
    ∀ x, F x false = true ↔ LineTarget S x := by
  intro x
  constructor
  · exact cofactor_lower S h F hF hreal x
  · rintro ⟨i, hiS, hix⟩
    have hhx : h x = true := hh (singleton i) x (singleton_le x i hix) (hsingle i hiS)
    have ht : LineTarget S x := ⟨i, hiS, hix⟩
    simpa [hhx] using (hreal x).mpr ht

lemma problematic_line [DecidableEq α] (S : Finset α) (h : (α → Bool) → Bool)
    (F : (α → Bool) → Bool → Bool) (hh : MonotoneBit h)
    (hF : MonotoneCut F)
    (hreal : ∀ x, F x (!(h x)) = true ↔ LineTarget S x)
    (htrue : ¬ ∀ x, F x true = true ↔ LineTarget S x)
    (hfalse : ¬ ∀ x, F x false = true ↔ LineTarget S x) :
    h (outside S) = true ∧ ∃ i ∈ S, h (singleton i) = false := by
  classical
  constructor
  · cases hc : h (outside S) with
    | false => exact False.elim (htrue (replace_not_true S h F hh hF hreal hc))
    | true => rfl
  · by_contra hn
    have hs : ∀ i ∈ S, h (singleton i) = true := by
      intro i hi
      cases hc : h (singleton i) with
      | false => exact False.elim (hn ⟨i, hi, hc⟩)
      | true => rfl
    exact hfalse (replace_not_false S h F hh hF hreal hs)

end PEqualNP.Outside.Meta952Strategy
