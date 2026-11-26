import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_18069 : have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : (Fin (26 : ℕ) → Bool) → Prop := fun (x2 : Fin (26 : ℕ) → Bool) => ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), x1 x3 x4 ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true; have x3 : (Fin (13 : ℕ) → Bool) → Fin (13 : ℕ) → Bool := fun (x3 : Fin (13 : ℕ) → Bool) (x4 : Fin (13 : ℕ)) => !(x3 x4 || x3 (x4 + (1 : Fin (13 : ℕ))) || x3 (x4 + (3 : Fin (13 : ℕ))) || x3 (x4 + (9 : Fin (13 : ℕ)))); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : ℕ), (∀ (x7 : Fin (26 : ℕ) → Bool), Maximal (fun (x8 : Fin (26 : ℕ) → Bool) => ¬x2 x8) x7 → PEqualNP.BlindGate.wireValue x4 (26 : ℕ) x7 (if x7 (13 : Fin (26 : ℕ)) = Bool.true then x5 else x6) = Bool.false) → ∀ (x8 : Fin (13 : ℕ) → Bool), (∀ (x9 : Fin (13 : ℕ)), x8 x9 = Bool.false → ∃ (x11 : Fin (13 : ℕ)), x1 x9 x11 ∧ x3 x8 x11 = Bool.true) → PEqualNP.BlindGate.wireValue x4 (26 : ℕ) (Fin.append x8 (x3 x8)) (if x3 x8 (0 : Fin (13 : ℕ)) = Bool.true then x5 else x6) = Bool.false := by
  intro I E L C a b off x hx
  let z := Fin.append x (L x)
  have spec (l : Fin 13) : L x l = false ↔ ∃ p, I p l ∧ x p = true := by
    change (!(x l || x (l+1) || x (l+3) || x (l+9))) = false ↔
      ∃ p, (p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9) ∧ x p = true
    simp only [Bool.not_eq_false',Bool.or_eq_true]
    constructor
    · rintro (((h|h)|h)|h)
      · exact ⟨_, Or.inl rfl,h⟩
      · exact ⟨_, Or.inr (Or.inl rfl),h⟩
      · exact ⟨_, Or.inr (Or.inr (Or.inl rfl)),h⟩
      · exact ⟨_, Or.inr (Or.inr (Or.inr rfl)),h⟩
    · rintro ⟨p,(rfl|rfl|rfl|rfl),h⟩ <;> tauto
  have hl (p : Fin 13) : z (Fin.castAdd 13 p) = x p := Fin.append_left _ _ _
  have hr (l : Fin 13) : z (Fin.natAdd 13 l) = L x l := Fin.append_right _ _ _
  have maximal : Maximal (fun y => ¬ E y) z := by
    constructor
    · rintro ⟨p,l,he,hp,hq⟩
      rw [hl] at hp
      rw [hr,(spec l).2 ⟨p,he,hp⟩] at hq
      contradiction
    · intro y hy le i
      refine Fin.addCases (m := 13) (n := 13) (motive := fun k => y k ≤ z k) (fun p => ?_) (fun l => ?_) i
      · rw [hl,Bool.le_iff_imp]
        intro h
        cases e : x p with
        | true => rfl
        | false =>
          obtain ⟨l,he,hL⟩ := hx p e
          exact False.elim (hy ⟨p,l,he,h,Bool.le_iff_imp.mp (le _) ((hr l).trans hL)⟩)
      · rw [hr,Bool.le_iff_imp]
        intro h
        cases e : L x l with
        | true => rfl
        | false =>
          obtain ⟨p,he,hp⟩ := (spec _).1 e
          exact False.elim (hy ⟨p,l,he,Bool.le_iff_imp.mp (le _) ((hl p).trans hp),h⟩)
  have ans := off z maximal
  change BlindGate.wireValue C 26 z (if L x 0 = true then a else b) = false
  have e : z 13 = L x 0 := hr 0
  rwa [e] at ans
