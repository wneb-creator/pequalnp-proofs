import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1463

/-- The Paley tournament on seven points: `x` beats `y` when `y - x` is 1, 2 or 4. -/
def P (x y : Fin 7) : Bool := y - x == 1 || y - x == 2 || y - x == 4

theorem P_antisymm : ∀ x y : Fin 7, P x y = true → P y x = false := by decide

set_option maxRecDepth 100000 in
theorem P_dom : ∀ T : Finset (Fin 7), T.card ≤ 2 → ∃ z : Fin 7, z ∉ T ∧ ∀ y ∈ T, P z y = true := by
  decide +kernel

end PEqualNP.Outside.L_meta_1463

theorem PEqualNP.Outside.L_meta_1463 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (A : Finset (Fin n)),
    A.card = 7 → (∀ i : Fin m, (S i ∩ A).card ≤ 2) →
    ∃ (r : Fin n → Fin n → Prop) (f : Fin m → Fin n), (∀ a b : Fin n, r a b → ¬ r b a) ∧
      ∀ i : Fin m, f i ∈ A ∧ f i ∉ S i ∧ ∀ y ∈ S i ∩ A, r (f i) y := by
  classical
  intro n m S A hA hS
  let e : A ≃ Fin 7 := Finset.equivFinOfCardEq hA
  have hinj : ∀ x y : Fin 7, ((e.symm x : A) : Fin n) = ((e.symm y : A) : Fin n) → x = y :=
    fun x y h => e.symm.injective (Subtype.ext h)
  let r : Fin n → Fin n → Prop := fun a b =>
    ∃ x y : Fin 7, ((e.symm x : A) : Fin n) = a ∧ ((e.symm y : A) : Fin n) = b ∧
      PEqualNP.Outside.L_meta_1463.P x y = true
  have hf : ∀ i : Fin m, ∃ z : Fin n, z ∈ A ∧ z ∉ S i ∧ ∀ y ∈ S i ∩ A, r z y := by
    intro i
    let T : Finset (Fin 7) := Finset.univ.filter fun z : Fin 7 => ((e.symm z : A) : Fin n) ∈ S i
    have hT : T.card ≤ 2 := by
      refine le_trans (Finset.card_le_card_of_injOn (fun z => ((e.symm z : A) : Fin n)) ?_ ?_) (hS i)
      · intro z hz
        have hz' : ((e.symm z : A) : Fin n) ∈ S i := by simpa [T] using hz
        exact Finset.mem_coe.2 (Finset.mem_inter.2 ⟨hz', (e.symm z).2⟩)
      · intro x _ y _ h
        exact hinj x y h
    obtain ⟨z, hz, hdom⟩ := PEqualNP.Outside.L_meta_1463.P_dom T hT
    refine ⟨((e.symm z : A) : Fin n), (e.symm z).2, ?_, ?_⟩
    · intro hin
      exact hz (by simpa [T] using hin)
    · intro y hy
      obtain ⟨hyS, hyA⟩ := Finset.mem_inter.1 hy
      refine ⟨z, e ⟨y, hyA⟩, rfl, by simp, ?_⟩
      apply hdom
      simpa [T] using hyS
  choose f hfA hfS hfr using hf
  refine ⟨r, f, ?_, fun i => ⟨hfA i, hfS i, hfr i⟩⟩
  rintro a b ⟨x, y, hxa, hyb, hP⟩ ⟨x', y', hxb, hya, hP'⟩
  have h1 : x' = y := hinj _ _ (hxb.trans hyb.symm)
  have h2 : y' = x := hinj _ _ (hya.trans hxa.symm)
  subst h1 h2
  rw [PEqualNP.Outside.L_meta_1463.P_antisymm _ _ hP] at hP'
  exact Bool.false_ne_true hP'
