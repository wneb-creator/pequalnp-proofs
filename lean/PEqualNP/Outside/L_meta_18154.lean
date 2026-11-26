import PEqualNP.Defs

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_18154 : have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3; have x2 : (Fin (13 : ℕ) → Bool) → (Fin (13 : ℕ) → Bool) → Prop := fun (x2 x3 : Fin (13 : ℕ) → Bool) =>   have x4 : Finset (Fin (13 : ℕ)) := {x4 : Fin (13 : ℕ) | x2 x4 = Bool.true};   have x5 : Finset (Fin (13 : ℕ)) := {x5 : Fin (13 : ℕ) | x3 x5 = Bool.true};   PEqualNP.GenericRejection.IsFalseInput x1 x4 x5 ∧ (∀ (x6 : Fin (13 : ℕ)), {x7 ∈ x1 x6 | x2 x7 = Bool.true}.card ≤ (2 : ℕ)) ∧ (∀ (x6 : Fin (13 : ℕ)), {x7 ∈ x5 | x6 ∈ x1 x7}.card ≤ (2 : ℕ)) ∧ PEqualNP.GenericRejection.IsMaximalFalse x1 x4 x5; ∀ x3 ∈ [((7 : ℕ), (904 : ℕ)), ((13 : ℕ), (2848 : ℕ)), ((19 : ℕ), (708 : ℕ)), ((21 : ℕ), (2720 : ℕ)), ((25 : ℕ), (2656 : ℕ)), ((37 : ℕ), (2440 : ℕ)), ((41 : ℕ), (2370 : ℕ)), ((133 : ℕ), (808 : ℕ))],   ∀ x5 ∈ [(1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))],     ∀ (x7 : Fin (13 : ℕ)) (x8 : Bool),       have x9 : ℕ → ℕ → Fin (13 : ℕ) → Bool := fun (x9 x10 : ℕ) (x11 : Fin (13 : ℕ)) => if x8 = Bool.true then x10.testBit ↑(-(x5 * x11 + x7)) else x9.testBit ↑(x5 * x11 + x7);       x2 (x9 x3.1 x3.2) (x9 x3.2 x3.1) := by
  intro lines good pair hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
  all_goals decide +kernel
