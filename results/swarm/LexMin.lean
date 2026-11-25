import Mathlib

namespace PEqualNP.Outside.L_meta_4970_aux

lemma exists_four_measure_minimum {α : Type*} (P : α → Prop)
    (m0 m1 m2 m3 : α → ℕ) (x0 : α) (hx0 : P x0) :
    ∃ x : α, P x ∧ m0 x ≤ m0 x0 ∧
      (∀ y, P y → m0 x ≤ m0 y) ∧
      (∀ y, P y → m0 y = m0 x → m1 x ≤ m1 y) ∧
      (∀ y, P y → m0 y = m0 x → m1 y = m1 x → m2 x ≤ m2 y) ∧
      (∀ y, P y → m0 y = m0 x → m1 y = m1 x → m2 y = m2 x → m3 x ≤ m3 y) := by
  classical
  have e0 : ∃ k : ℕ, ∃ x : α, P x ∧ m0 x = k := ⟨m0 x0,x0,hx0,rfl⟩
  obtain ⟨x1,hx1,h10⟩ := Nat.find_spec e0
  have e1 : ∃ k : ℕ, ∃ x : α, P x ∧ m0 x = Nat.find e0 ∧ m1 x = k :=
    ⟨m1 x1,x1,hx1,h10,rfl⟩
  obtain ⟨x2,hx2,h20,h21⟩ := Nat.find_spec e1
  have e2 : ∃ k : ℕ, ∃ x : α,
      P x ∧ m0 x = Nat.find e0 ∧ m1 x = Nat.find e1 ∧ m2 x = k :=
    ⟨m2 x2,x2,hx2,h20,h21,rfl⟩
  obtain ⟨x3,hx3,h30,h31,h32⟩ := Nat.find_spec e2
  have e3 : ∃ k : ℕ, ∃ x : α, P x ∧ m0 x = Nat.find e0 ∧
      m1 x = Nat.find e1 ∧ m2 x = Nat.find e2 ∧ m3 x = k :=
    ⟨m3 x3,x3,hx3,h30,h31,h32,rfl⟩
  obtain ⟨x,hx,h0,h1,h2,h3⟩ := Nat.find_spec e3
  refine ⟨x,hx,?_,?_,?_,?_,?_⟩
  · rw [h0]
    exact Nat.find_min' e0 ⟨x0,hx0,rfl⟩
  · intro y hy
    rw [h0]
    exact Nat.find_min' e0 ⟨y,hy,rfl⟩
  · intro y hy hy0
    rw [h1]
    exact Nat.find_min' e1 ⟨y,hy,hy0.trans h0,rfl⟩
  · intro y hy hy0 hy1
    rw [h2]
    exact Nat.find_min' e2 ⟨y,hy,hy0.trans h0,hy1.trans h1,rfl⟩
  · intro y hy hy0 hy1 hy2
    rw [h3]
    exact Nat.find_min' e3 ⟨y,hy,hy0.trans h0,hy1.trans h1,hy2.trans h2,rfl⟩

end PEqualNP.Outside.L_meta_4970_aux
