namespace PEqualNP.Outside.L_meta_2592_aux.BooleanFactor

theorem unary_factor_polarity {α : Type} (code target : α → Bool) (outer : Bool → Bool)
    (factor : ∀ x, outer (code x) = target x)
    (nonconstant : ∃ x y, target x ≠ target y) :
    ∃ sign : Bool, ∀ x, (code x != sign) = target x := by
  have different : outer false ≠ outer true := by
    intro equal
    obtain ⟨x, y, differs⟩ := nonconstant
    apply differs
    rw [← factor x, ← factor y]
    cases hx : code x <;> cases hy : code y <;> simp_all
  cases zero : outer false with
  | false =>
    have one : outer true = true := by
      cases h : outer true <;> simp_all
    refine ⟨false, ?_⟩
    intro x
    have h := factor x
    cases hc : code x <;> simp_all
  | true =>
    have one : outer true = false := by
      cases h : outer true <;> simp_all
    refine ⟨true, ?_⟩
    intro x
    have h := factor x
    cases hc : code x <;> simp_all

theorem unary_factor_polarity_at_zero {α : Type} (code target : α → Bool)
    (outer : Bool → Bool) (base : α) (zero : target base = false)
    (factor : ∀ x, outer (code x) = target x)
    (nonconstant : ∃ x y, target x ≠ target y) :
    ∀ x, (code x != code base) = target x := by
  obtain ⟨sign, correct⟩ := unary_factor_polarity code target outer factor nonconstant
  have atBase := correct base
  rw [zero] at atBase
  have same : code base = sign := by
    cases hb : code base <;> cases hs : sign <;> simp_all
  intro x
  rw [same]
  exact correct x

end PEqualNP.Outside.L_meta_2592_aux.BooleanFactor
