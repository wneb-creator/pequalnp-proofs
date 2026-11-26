import Mathlib.Data.List.GetD
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3785_376
    (samples :
      let labels : List (Fin 26) := [2,4,5,6,7,8,10,11,12,14,15,16,17,18,19,20,21,22,23,24,25]
      let shifts : List ℕ := [0,1,3,9]
      let edge := fun p l : Fin 13 => decide (p.val ∉ shifts ∧ (p.val+l.val)%13 ∈ shifts)
      let input := fun (S T : Finset (Fin 13)) =>
        labels.map fun i => if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ S)
          else decide (Fin.ofNat 13 i.val ∈ T)
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 43 ∧ C.output < 21 + C.size ∧
        (∀ p l, edge p l = true → C.eval (input {p} {l}) = true) ∧
        ∀ S, C.eval (input S (Finset.univ.filter (fun l => ∀ p ∈ S, edge p l = false))) = false)
    (transfer : ∀ (edge : Fin 13 → Fin 13 → Bool) (labels : List (Fin 26)) (C : Circuit),
      Monotone2 C →
      let input := fun (S T : Finset (Fin 13)) =>
        labels.map fun i => if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ S)
          else decide (Fin.ofNat 13 i.val ∈ T)
      (∀ p l, edge p l = true → C.eval (input {p} {l}) = true) →
      (∀ S, C.eval (input S (Finset.univ.filter (fun l => ∀ p ∈ S, edge p l = false))) = false) →
      ∀ S T, C.eval (input S T) = true ↔ ∃ p ∈ S, ∃ l ∈ T, edge p l = true) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     x1.size ≤ (43 : ℕ) ∧       x1.output < (21 : ℕ) + x1.size ∧         have x2 : List (Fin (26 : ℕ)) := [(2 : Fin (26 : ℕ)), (4 : Fin (26 : ℕ)), (5 : Fin (26 : ℕ)), (6 : Fin (26 : ℕ)), (7 : Fin (26 : ℕ)), (8 : Fin (26 : ℕ)), (10 : Fin (26 : ℕ)), (11 : Fin (26 : ℕ)), (12 : Fin (26 : ℕ)), (14 : Fin (26 : ℕ)), (15 : Fin (26 : ℕ)), (16 : Fin (26 : ℕ)), (17 : Fin (26 : ℕ)), (18 : Fin (26 : ℕ)), (19 : Fin (26 : ℕ)), (20 : Fin (26 : ℕ)), (21 : Fin (26 : ℕ)), (22 : Fin (26 : ℕ)), (23 : Fin (26 : ℕ)), (24 : Fin (26 : ℕ)), (25 : Fin (26 : ℕ))];         have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x3 x4 : Finset (Fin (13 : ℕ))) (x5 : Fin (26 : ℕ)) => if ↑x5 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x3) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x4);         have x4 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x4 x5 : Fin (13 : ℕ)) => (↑x4 + ↑x5) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];         ∀ (x5 x6 : Finset (Fin (13 : ℕ))), x1.eval (List.map (x3 x5 x6) x2) = Bool.true ↔ ∃ x7 ∈ x5, ↑x7 ∉ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ ∃ x8 ∈ x6, x4 x7 x8 := by
  let labels : List (Fin 26) := [2,4,5,6,7,8,10,11,12,14,15,16,17,18,19,20,21,22,23,24,25]
  let shifts : List ℕ := [0,1,3,9]
  let edge := fun p l : Fin 13 => decide (p.val ∉ shifts ∧ (p.val+l.val)%13 ∈ shifts)
  obtain ⟨C,hm,hs,ho,hpos,hneg⟩ := samples
  refine ⟨C,hm,hs,ho,?_⟩
  have correct := transfer edge labels C hm hpos hneg
  dsimp only
  intro S T
  refine (correct S T).trans ?_
  change (∃ p ∈ S, ∃ l ∈ T, edge p l = true) ↔
    ∃ p ∈ S, p.val ∉ shifts ∧ ∃ l ∈ T, (p.val+l.val)%13 ∈ shifts
  simp only [edge, decide_eq_true_eq]
  constructor
  · rintro ⟨p,hp,l,hl,hp',he⟩
    exact ⟨p,hp,hp',l,hl,he⟩
  · rintro ⟨p,hp,hp',l,hl,he⟩
    exact ⟨p,hp,l,hl,hp',he⟩
