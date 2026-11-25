import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Basic

namespace PEqualNP.Outside.L_meta_2685

lemma and_below_linear {α : Type*} (A : Finset α)
    (f g : (α → Bool) → Bool) (hf : Monotone f) (hg : Monotone g)
    (h : ∀ x, (f x && g x) = true → ∃ a ∈ A, x a = true) :
    (∀ x, f x = true → ∃ a ∈ A, x a = true) ∨
      (∀ x, g x = true → ∃ a ∈ A, x a = true) := by
  classical
  by_cases hfA : ∀ x, f x = true → ∃ a ∈ A, x a = true
  · exact Or.inl hfA
  right
  intro y hgy
  by_contra hy
  obtain ⟨x, hx⟩ := not_forall.mp hfA
  obtain ⟨hfx, hx⟩ := not_imp.mp hx
  let z : α → Bool := fun a => x a || y a
  have hxz : x ≤ z := by
    intro a
    change x a ≤ (x a || y a)
    cases x a <;> cases y a <;> decide
  have hyz : y ≤ z := by
    intro a
    change y a ≤ (x a || y a)
    cases x a <;> cases y a <;> decide
  have hfz : f z = true := le_antisymm le_top (hfx ▸ hf hxz)
  have hgz : g z = true := le_antisymm le_top (hgy ▸ hg hyz)
  obtain ⟨a, ha, hza⟩ := h z (by simp only [hfz, hgz, Bool.and_self])
  have hxa : x a = false := by
    cases hxa : x a
    · rfl
    · exact False.elim (hx ⟨a, ha, hxa⟩)
  have hya : y a = false := by
    cases hya : y a
    · rfl
    · exact False.elim (hy ⟨a, ha, hya⟩)
  simp only [z, hxa, hya, Bool.or_self, Bool.false_eq_true] at hza

def oneInput {α : Type*} [DecidableEq α] (a : α) : α → Bool :=
  fun b => decide (b = a)

lemma oneInput_le {α : Type*} [DecidableEq α] {a : α} {x : α → Bool}
    (h : x a = true) : oneInput a ≤ x := by
  intro b
  by_cases hb : b = a
  · subst b
    simp only [oneInput, decide_true, h, le_refl]
  · simp only [oneInput, hb, decide_false, Bool.false_le]

lemma below_linear_singleton {α : Type*} [DecidableEq α] (A : Finset α)
    (f : (α → Bool) → Bool)
    (h : ∀ x, f x = true → ∃ a ∈ A, x a = true)
    {a : α} (ha : f (oneInput a) = true) : a ∈ A := by
  obtain ⟨b, hb, hba⟩ := h (oneInput a) ha
  have : b = a := by simpa only [oneInput, decide_eq_true_eq] using hba
  simpa only [this] using hb

lemma linear_or_singletons {α : Type*} [DecidableEq α] (A : Finset α)
    (f g : (α → Bool) → Bool) (hf : Monotone f) (hg : Monotone g)
    (h : ∀ x, (f x || g x) = true ↔ ∃ a ∈ A, x a = true) :
    ∀ x, (f x || g x) = true ↔
      (∃ a, f (oneInput a) = true ∧ x a = true) ∨ g x = true := by
  intro x
  constructor
  · intro hfg
    obtain ⟨a, ha, hxa⟩ := (h x).mp hfg
    have hp : (f (oneInput a) || g (oneInput a)) = true :=
      (h _).mpr ⟨a, ha, by simp only [oneInput, decide_true]⟩
    rw [Bool.or_eq_true_eq_eq_true_or_eq_true] at hp
    rcases hp with hfa | hga
    · exact Or.inl ⟨a, hfa, hxa⟩
    · exact Or.inr (le_antisymm le_top (hga ▸ hg (oneInput_le hxa)))
  · rintro (⟨a, hfa, hxa⟩ | hgx)
    · rw [Bool.or_eq_true_eq_eq_true_or_eq_true]
      exact Or.inl (le_antisymm le_top (hfa ▸ hf (oneInput_le hxa)))
    · rw [Bool.or_eq_true_eq_eq_true_or_eq_true]
      exact Or.inr hgx

lemma shared_singleton_support {α : Type*} [DecidableEq α] (A B : Finset α)
    (f : (α → Bool) → Bool)
    (hA : ∀ x, f x = true → ∃ a ∈ A, x a = true)
    (hB : ∀ x, f x = true → ∃ a ∈ B, x a = true)
    (hAB : ∀ a ∈ A, ∀ b ∈ A, a ∈ B → b ∈ B → a = b)
    {a b : α} (ha : f (oneInput a) = true) (hb : f (oneInput b) = true) :
    a = b := by
  exact hAB a (below_linear_singleton A f hA ha)
    b (below_linear_singleton A f hA hb)
    (below_linear_singleton B f hB ha) (below_linear_singleton B f hB hb)

lemma eq_of_true_iff (a b : Bool) (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

lemma shared_linear_replace {α β : Type*} [DecidableEq α]
    (A : β → Finset α) (v : (α → Bool) → Bool)
    (h : β → (α → Bool) → Bool) (hv : Monotone v)
    (hh : ∀ k, Monotone (h k))
    (hout : ∀ k x, (v x || h k x) = true ↔ ∃ a ∈ A k, x a = true)
    (i j : β)
    (hij : ∀ a ∈ A i, ∀ b ∈ A i, a ∈ A j → b ∈ A j → a = b) :
    (∀ k x, (v x || h k x) = h k x) ∨
      ∃ a, v (oneInput a) = true ∧
        ∀ k x, (v x || h k x) = (x a || h k x) := by
  classical
  have hbelow (k : β) : ∀ x, v x = true → ∃ a ∈ A k, x a = true := by
    intro x hx
    apply (hout k x).mp
    simp only [hx, Bool.true_or]
  have unique {a b : α} (ha : v (oneInput a) = true)
      (hb : v (oneInput b) = true) : a = b :=
    shared_singleton_support (A i) (A j) v (hbelow i) (hbelow j) hij ha hb
  by_cases hs : ∃ a, v (oneInput a) = true
  · obtain ⟨a, ha⟩ := hs
    right
    refine ⟨a, ha, ?_⟩
    intro k x
    apply eq_of_true_iff
    rw [linear_or_singletons (A k) v (h k) hv (hh k) (hout k) x,
      Bool.or_eq_true_eq_eq_true_or_eq_true]
    apply or_congr _ Iff.rfl
    constructor
    · rintro ⟨b, hb, hxb⟩
      simpa only [unique hb ha] using hxb
    · intro hxa
      exact ⟨a, ha, hxa⟩
  · left
    intro k x
    apply eq_of_true_iff
    rw [linear_or_singletons (A k) v (h k) hv (hh k) (hout k) x]
    constructor
    · rintro (⟨a, ha, _⟩ | hkx)
      · exact False.elim (hs ⟨a, ha⟩)
      · exact hkx
    · exact Or.inr

end PEqualNP.Outside.L_meta_2685
