import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace PEqualNP.Outside.L_meta_2592_aux.PetersenBracket

lemma low_replacement_of_generators {α : Type*} [Preorder α]
    (f h : α → Bool) (G : α → Bool → Bool) (E : Finset α)
    (monoX : ∀ z, Monotone (fun x => G x z))
    (monoZ : ∀ x, Monotone (G x))
    (correct : ∀ x, G x (!(h x)) = f x)
    (generators : ∀ x, f x = true → ∃ e ∈ E, e ≤ x ∧ f e = true)
    (allH : ∀ e ∈ E, h e = true) :
    ∀ x, G x false = f x := by
  intro x
  have below : G x false ≤ f x := by
    rw [← correct x]
    apply monoZ x
    cases h x <;> decide
  cases hx : f x with
  | false =>
    rw [hx] at below
    cases hg : G x false with
    | false => rfl
    | true => exact False.elim ((by decide : ¬ (true ≤ false)) (by simpa [hg] using below))
  | true =>
    obtain ⟨e, he, hex, hfe⟩ := generators x hx
    have hge : G e false = true := by simpa [allH e he, hfe] using correct e
    have le : G e false ≤ G x false := monoX false hex
    rw [hge] at le
    cases hg : G x false with
    | false => exact False.elim ((by decide : ¬ (true ≤ false)) (by simpa [hg] using le))
    | true => rfl

lemma high_replacement_of_cogenerators {α : Type*} [Preorder α]
    (f h : α → Bool) (G : α → Bool → Bool) (M : Finset α)
    (monoX : ∀ z, Monotone (fun x => G x z))
    (monoZ : ∀ x, Monotone (G x))
    (correct : ∀ x, G x (!(h x)) = f x)
    (cogenerators : ∀ x, f x = false → ∃ m ∈ M, x ≤ m ∧ f m = false)
    (allH : ∀ m ∈ M, h m = false) :
    ∀ x, G x true = f x := by
  intro x
  have above : f x ≤ G x true := by
    rw [← correct x]
    apply monoZ x
    cases h x <;> decide
  cases hx : f x with
  | false =>
    obtain ⟨m, hm, hxm, hfm⟩ := cogenerators x hx
    have hgm : G m true = false := by simpa [allH m hm, hfm] using correct m
    have le : G x true ≤ G m true := monoX true hxm
    rw [hgm] at le
    cases hg : G x true with
    | false => rfl
    | true => exact False.elim ((by decide : ¬ (true ≤ false)) (by simpa [hg] using le))
  | true =>
    rw [hx] at above
    cases hg : G x true with
    | false => exact False.elim ((by decide : ¬ (true ≤ false)) (by simpa [hg] using above))
    | true => rfl

lemma critical_generator {α : Type*} [Preorder α]
    (f h : α → Bool) (G : α → Bool → Bool) (E : Finset α)
    (monoX : ∀ z, Monotone (fun x => G x z))
    (monoZ : ∀ x, Monotone (G x))
    (correct : ∀ x, G x (!(h x)) = f x)
    (generators : ∀ x, f x = true → ∃ e ∈ E, e ≤ x ∧ f e = true)
    (changed : ∃ x, G x false ≠ f x) :
    ∃ e ∈ E, h e = false := by
  classical
  by_contra! no
  have allH : ∀ e ∈ E, h e = true := by
    intro e he
    have ne := no e he
    cases hh : h e <;> simp_all
  obtain ⟨x, hx⟩ := changed
  exact hx (low_replacement_of_generators f h G E monoX monoZ correct generators allH x)

lemma critical_cogenerator {α : Type*} [Preorder α]
    (f h : α → Bool) (G : α → Bool → Bool) (M : Finset α)
    (monoX : ∀ z, Monotone (fun x => G x z))
    (monoZ : ∀ x, Monotone (G x))
    (correct : ∀ x, G x (!(h x)) = f x)
    (cogenerators : ∀ x, f x = false → ∃ m ∈ M, x ≤ m ∧ f m = false)
    (changed : ∃ x, G x true ≠ f x) :
    ∃ m ∈ M, h m = true := by
  classical
  by_contra! no
  have allH : ∀ m ∈ M, h m = false := by
    intro m hm
    have ne := no m hm
    cases hh : h m <;> simp_all
  obtain ⟨x, hx⟩ := changed
  exact hx (high_replacement_of_cogenerators f h G M monoX monoZ correct cogenerators allH x)


def petersen (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def row (m : ℕ) : Fin 10 → Bool := fun i => m.testBit i.val

def edgeMasks : Finset ℕ :=
  {3, 6, 12, 24, 17, 33, 66, 132, 264, 528, 160, 640, 576, 320, 288}

def independentMasks : Finset ℕ :=
  {50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773}

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma edge_cover : ∀ x : Fin 10 → Bool, petersen x = true →
    ∃ e ∈ edgeMasks, row e ≤ x ∧ petersen (row e) = true := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma independent_cover : ∀ x : Fin 10 → Bool, petersen x = false →
    ∃ m ∈ independentMasks, x ≤ row m ∧ petersen (row m) = false := by
  decide

lemma edge_truth : ∀ e ∈ edgeMasks, petersen (row e) = true := by
  decide

lemma independent_false : ∀ m ∈ independentMasks, petersen (row m) = false := by
  decide

lemma critical_petersen_witnesses
    (h : (Fin 10 → Bool) → Bool) (G : (Fin 10 → Bool) → Bool → Bool)
    (monoX : ∀ z, Monotone (fun x => G x z))
    (monoZ : ∀ x, Monotone (G x))
    (correct : ∀ x, G x (!(h x)) = petersen x)
    (changedLow : ∃ x, G x false ≠ petersen x)
    (changedHigh : ∃ x, G x true ≠ petersen x) :
    ∃ e ∈ edgeMasks, ∃ m ∈ independentMasks, h (row e) = false ∧ h (row m) = true := by
  classical
  have generators : ∀ x, petersen x = true →
      ∃ e ∈ edgeMasks.image row, e ≤ x ∧ petersen e = true := by
    intro x hx
    obtain ⟨e, he, hle, htrue⟩ := edge_cover x hx
    exact ⟨row e, Finset.mem_image.mpr ⟨e, he, rfl⟩, hle, htrue⟩
  have cogenerators : ∀ x, petersen x = false →
      ∃ m ∈ independentMasks.image row, x ≤ m ∧ petersen m = false := by
    intro x hx
    obtain ⟨m, hm, hle, hfalse⟩ := independent_cover x hx
    exact ⟨row m, Finset.mem_image.mpr ⟨m, hm, rfl⟩, hle, hfalse⟩
  obtain ⟨e, he, hhe⟩ := critical_generator petersen h G (edgeMasks.image row)
    monoX monoZ correct generators changedLow
  obtain ⟨m, hm, hhm⟩ := critical_cogenerator petersen h G (independentMasks.image row)
    monoX monoZ correct cogenerators changedHigh
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hm
  exact ⟨a, ha, b, hb, hhe, hhm⟩

end PEqualNP.Outside.L_meta_2592_aux.PetersenBracket
