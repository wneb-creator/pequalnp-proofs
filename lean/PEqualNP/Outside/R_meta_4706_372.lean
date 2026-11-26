import Mathlib.Data.List.GetD
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_4706_372
    (synthesis : let offsets : Finset (Fin 13) := {0,1,3,9}
      ∃ (k : Fin 4) (g : Fin 62 → Bool × Fin 89 × Fin 89),
      (∀ j, max (g j).2.1.val (g j).2.2.val < 27+j.val) ∧
      let d : Fin 26 := if k.val = 1 then 1 else if k.val = 3 then 14 else 13
      let run := fun (x : Fin 26 → Bool) =>
        ((List.ofFn g).foldl (fun w t =>
          let a := w.getD t.2.1.val false
          let b := w.getD t.2.2.val false
          w ++ [cond t.1 (a || b) (a && b)])
          (List.ofFn (Fin.lastCases (if k.val = 0 then x 0 && x d else x 0 || x d) x))).getD 88 false
      (∀ u v : Fin 13, (∃ h ∈ offsets, u = v+h) →
        run (fun i => decide (i = Fin.castAdd 13 u ∨ i = Fin.natAdd 13 v)) = true) ∧
      ∀ p ∈ ([(7,904),(13,2848),(19,708),(21,2720),(25,2656),(37,2440),(41,2370),(133,808)] : List (ℕ×ℕ)),
        ∀ m ∈ ([1,3,9] : List (Fin 13)), ∀ t : Fin 13, ∀ dual : Bool,
          let bit := fun (a b : ℕ) (i : Fin 13) =>
            if dual then b.testBit (-(m*i+t)).val else a.testBit (m*i+t).val
          run (Fin.append (bit p.1 p.2) (bit p.2 p.1)) = false)
    (compile : ∀ (n s : ℕ) (g : Fin s → Bool × Fin (n+s) × Fin (n+s)) (out : ℕ),
      (∀ j, max (g j).2.1.val (g j).2.2.val < n+j.val) →
      ∃ C : Circuit, Monotone2 C ∧ ReadsBack n C ∧ C.size = s ∧
        ∀ x : Fin n → Bool, circuitFun n C x =
          ((List.ofFn g).foldl (fun w t =>
            let a := w.getD t.2.1.val false
            let b := w.getD t.2.2.val false
            w ++ [cond t.1 (a || b) (a && b)]) (List.ofFn x)).getD out false) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : List (ℕ × ℕ) := [((7 : ℕ), (904 : ℕ)), ((13 : ℕ), (2848 : ℕ)), ((19 : ℕ), (708 : ℕ)), ((21 : ℕ), (2720 : ℕ)), ((25 : ℕ), (2656 : ℕ)), ((37 : ℕ), (2440 : ℕ)), ((41 : ℕ), (2370 : ℕ)), ((133 : ℕ), (808 : ℕ))]; have x3 : ℕ × ℕ → Fin (13 : ℕ) → Fin (13 : ℕ) → Bool → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x3 : ℕ × ℕ) (x4 x5 : Fin (13 : ℕ)) (x6 : Bool) =>   have x7 : ℕ → ℕ → Fin (13 : ℕ) → Bool := fun (x7 x8 : ℕ) (x9 : Fin (13 : ℕ)) => if x6 = Bool.true then x8.testBit ↑(-(x4 * x9 + x5)) else x7.testBit ↑(x4 * x9 + x5);   Fin.append (x7 x3.1 x3.2) (x7 x3.2 x3.1); ∃ (x4 : Fin (4 : ℕ)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x5 ∧     PEqualNP.MetaComplexity.NestedCover.ReadsBack (27 : ℕ) x5 ∧       x5.size ≤ (62 : ℕ) ∧         have x6 : Fin (26 : ℕ) := if ↑x4 = (1 : ℕ) then (1 : Fin (26 : ℕ)) else if ↑x4 = (3 : ℕ) then (14 : Fin (26 : ℕ)) else (13 : Fin (26 : ℕ));         have x7 : Bool := Decidable.decide (↑x4 = (0 : ℕ));         have x8 : (Fin (26 : ℕ) → Bool) → Fin (27 : ℕ) → Bool := fun (x8 : Fin (26 : ℕ) → Bool) (x9 : Fin ((26 : ℕ) + (1 : ℕ))) => Fin.lastCases (if x7 = Bool.true then x8 (0 : Fin (26 : ℕ)) && x8 x6 else x8 (0 : Fin (26 : ℕ)) || x8 x6) x8 x9;         (∀ (x9 x10 : Fin (13 : ℕ)), (∃ x11 ∈ x1, x9 = x10 + x11) → PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x5 (x8 fun (x12 : Fin (26 : ℕ)) => Decidable.decide (x12 = Fin.castAdd (13 : ℕ) x9 ∨ x12 = Fin.natAdd (13 : ℕ) x10)) = Bool.true) ∧ ∀ x9 ∈ x2, ∀ x11 ∈ [(1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], ∀ (x13 : Fin (13 : ℕ)) (x14 : Bool), PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x5 (x8 (x3 x9 x11 x13 x14)) = Bool.false := by
  obtain ⟨k, g, legal, pos, neg⟩ := synthesis
  obtain ⟨C, mono, back, size, eval⟩ := compile 27 62 g 88 legal
  refine ⟨k,C,mono,back,size.le,?_,?_⟩
  · intro u v h
    rw [eval]
    simpa only [decide_eq_true_eq] using pos u v h
  · intro p hp m hm t dual
    rw [eval]
    simpa only [decide_eq_true_eq] using neg p hp m hm t dual
