import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection in
theorem PEqualNP.Outside.L_meta_5178 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (1 : ℕ) ≤ x1 → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x7 x8 : Finset (Fin x2)), x8.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x7 x8 → x4.eval (PEqualNP.GenericRejection.incidenceInput x7 x8) = Bool.false) → ∀ (x8 : Finset (Fin (x2 + x2))), List.countP (fun (x9 : Fin x2) => Decidable.decide (Fin.natAdd x2 x9 ∈ x8)) (List.finRange x2) ≤ x1 → (PEqualNP.ReadK.IsPrimeImplicant (x2 + x2) x4 x8 ↔ ∃ (x10 : Fin x2) (x11 : Fin x2), x10 ∈ x3 x11 ∧ x8 = {Fin.castAdd x2 x10, Fin.natAdd x2 x11}) := by
  intro q N S C hq hR hF U hU
  let X : Finset (Fin (N + N)) → Finset (Fin N) := fun T =>
    Finset.univ.filter fun p => Fin.castAdd N p ∈ T
  let Y : Finset (Fin (N + N)) → Finset (Fin N) := fun T =>
    Finset.univ.filter fun l => Fin.natAdd N l ∈ T
  have hX : ∀ T p, p ∈ X T ↔ Fin.castAdd N p ∈ T := fun T p => by simp [X]
  have hY : ∀ T l, l ∈ Y T ↔ Fin.natAdd N l ∈ T := fun T l => by simp [Y]
  have hin : ∀ T, PEqualNP.MetaComplexity.circuitFun (N + N) C (PEqualNP.ReadK.setInput T) =
      C.eval (incidenceInput (X T) (Y T)) := by
    intro T
    change C.eval (List.ofFn (PEqualNP.ReadK.setInput T)) = _
    rw [List.ofFn_add]
    unfold incidenceInput
    congr 2
    · congr 1
      funext p
      exact decide_eq_decide.2 (hX T p).symm
    · congr 1
      funext l
      exact decide_eq_decide.2 (hY T l).symm
  have hcard : (Y U).card ≤ q := by
    have e : Y U = ((List.finRange N).filter fun l => decide (Fin.natAdd N l ∈ U)).toFinset := by
      ext l
      simp [hY]
    rw [e, List.toFinset_card_of_nodup ((List.nodup_finRange N).filter _),
      ← List.countP_eq_length_filter]
    exact hU
  have hmono : ∀ T, T ⊆ U → (Y T).card ≤ q := fun T hT =>
    le_trans (Finset.card_le_card fun l hl => (hY U l).2 (hT ((hY T l).1 hl))) hcard
  have hne : ∀ p l : Fin N, (Fin.castAdd N p : Fin (N + N)) ≠ Fin.natAdd N l := by
    intro p l h
    have := congrArg Fin.val h
    simp at this
    have := p.isLt
    omega
  have hpair : ∀ p l, X {Fin.castAdd N p, Fin.natAdd N l} = {p} ∧
      Y {Fin.castAdd N p, Fin.natAdd N l} = {l} := by
    intro p l
    constructor
    · ext x
      rw [hX, Finset.mem_insert, Finset.mem_singleton, Finset.mem_singleton]
      constructor
      · rintro (h | h)
        · exact Fin.castAdd_injective N N h
        · exact absurd h (hne x l)
      · rintro rfl
        exact Or.inl rfl
    · ext x
      rw [hY, Finset.mem_insert, Finset.mem_singleton, Finset.mem_singleton]
      constructor
      · rintro (h | h)
        · exact absurd h.symm (hne p x)
        · exact Fin.natAdd_injective N N h
      · rintro rfl
        exact Or.inr rfl
  have htrue : ∀ p l, p ∈ S l → PEqualNP.MetaComplexity.circuitFun (N + N) C
      (PEqualNP.ReadK.setInput {Fin.castAdd N p, Fin.natAdd N l}) = true := by
    intro p l h
    rw [hin, (hpair p l).1, (hpair p l).2]
    exact hR l p h
  constructor
  · rintro ⟨h1, h2⟩
    have : ∃ p l, p ∈ S l ∧ p ∈ X U ∧ l ∈ Y U := by
      by_contra hcon
      push Not at hcon
      have hf := hF (X U) (Y U) hcard fun l hl => Finset.disjoint_left.2 fun p hp hpX =>
        hcon p l hp hpX hl
      rw [← hin, h1] at hf
      exact Bool.false_ne_true hf.symm
    obtain ⟨p, l, hpl, hp, hl⟩ := this
    refine ⟨p, l, hpl, ?_⟩
    by_contra hUne
    have hsub : ({Fin.castAdd N p, Fin.natAdd N l} : Finset (Fin (N + N))) ⊆ U := by
      intro x hx
      rcases Finset.mem_insert.1 hx with h | h
      · rw [h]; exact (hX U p).1 hp
      · rw [Finset.mem_singleton.1 h]; exact (hY U l).1 hl
    have := h2 _ (Finset.mem_ssubsets.2 (lt_of_le_of_ne hsub (Ne.symm hUne)))
    rw [htrue p l hpl] at this
    exact Bool.false_ne_true this.symm
  · rintro ⟨p, l, hpl, rfl⟩
    refine ⟨htrue p l hpl, fun T hT => ?_⟩
    have hT' := Finset.mem_ssubsets.1 hT
    rw [hin]
    refine hF _ _ (hmono T hT'.1) fun l' hl' => Finset.disjoint_left.2 fun p' _ hp' => ?_
    have a1 := (hX T p').1 hp'
    have a2 := (hY T l').1 hl'
    have b1 := hT'.1 a1
    have b2 := hT'.1 a2
    have c1 : Fin.castAdd N p' = Fin.castAdd N p := by
      rcases Finset.mem_insert.1 b1 with h | h
      · exact h
      · exact absurd (Finset.mem_singleton.1 h) (hne p' l)
    have c2 : Fin.natAdd N l' = Fin.natAdd N l := by
      rcases Finset.mem_insert.1 b2 with h | h
      · exact absurd h.symm (hne p l')
      · exact Finset.mem_singleton.1 h
    rw [c1] at a1
    rw [c2] at a2
    refine hT'.2 fun x hx => ?_
    rcases Finset.mem_insert.1 hx with h | h
    · rw [h]; exact a1
    · rw [Finset.mem_singleton.1 h]; exact a2
