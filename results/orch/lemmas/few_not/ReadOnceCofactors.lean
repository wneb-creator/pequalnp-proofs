namespace PEqualNP.Outside.L_meta_2592_aux

theorem or_read_cofactors_equal {α : Type}
    (f : Bool → α → Bool) (h : α → Bool) (F : α → Bool → Bool)
    (computes : ∀ b x, F x (b || h x) = f b x)
    (x : α) (hx : h x = true) : f false x = f true x := by
  rw [← computes false x, ← computes true x]
  simp [hx]

theorem and_read_cofactors_equal {α : Type}
    (f : Bool → α → Bool) (h : α → Bool) (F : α → Bool → Bool)
    (computes : ∀ b x, F x (b && h x) = f b x)
    (x : α) (hx : h x = false) : f false x = f true x := by
  rw [← computes false x, ← computes true x]
  simp [hx]

theorem or_read_false_below_separation {n : Nat}
    (f : Bool → (Fin n → Bool) → Bool) (h : (Fin n → Bool) → Bool)
    (F : (Fin n → Bool) → Bool → Bool)
    (computes : ∀ b x, F x (b || h x) = f b x)
    (operandMono : ∀ x y, (∀ i, x i = true → y i = true) → h x = true → h y = true)
    (x y : Fin n → Bool) (below : ∀ i, x i = true → y i = true)
    (separates : f false y ≠ f true y) : h x = false := by
  cases hx : h x
  · rfl
  · have hy := operandMono x y below hx
    exact False.elim (separates (or_read_cofactors_equal f h F computes y hy))

theorem and_read_true_above_separation {n : Nat}
    (f : Bool → (Fin n → Bool) → Bool) (h : (Fin n → Bool) → Bool)
    (F : (Fin n → Bool) → Bool → Bool)
    (computes : ∀ b x, F x (b && h x) = f b x)
    (operandMono : ∀ x y, (∀ i, x i = true → y i = true) → h x = true → h y = true)
    (x y : Fin n → Bool) (above : ∀ i, y i = true → x i = true)
    (separates : f false y ≠ f true y) : h x = true := by
  have hy : h y = true := by
    cases hy : h y
    · exact False.elim (separates (and_read_cofactors_equal f h F computes y hy))
    · rfl
  exact operandMono y x above hy

theorem not_read_cofactors_antitone {α : Type}
    (f : Bool → α → Bool) (F : α → Bool → Bool)
    (computes : ∀ b x, F x (!b) = f b x)
    (suffixMono : ∀ x, F x false = true → F x true = true) :
    ∀ x, f true x = true → f false x = true := by
  intro x hx
  have hzero : F x false = true := by simpa using (computes true x).trans hx
  have hone := suffixMono x hzero
  simpa using (computes false x).symm.trans hone

theorem not_read_no_positive_separation {α : Type}
    (f : Bool → α → Bool) (F : α → Bool → Bool)
    (computes : ∀ b x, F x (!b) = f b x)
    (suffixMono : ∀ x, F x false = true → F x true = true)
    (x : α) (off : f false x = false) (on : f true x = true) : False := by
  have h := not_read_cofactors_antitone f F computes suffixMono x on
  simp_all

end PEqualNP.Outside.L_meta_2592_aux
