import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4893_1
    (geometry : let S := PEqualNP.HeptadCover.singerLines3
      let clean := fun (a b : Fin 13 → Bool) =>
        let X := Finset.univ.filter fun i => a i = true
        let Y := Finset.univ.filter fun i => b i = true
        PEqualNP.GenericRejection.IsFalseInput S X Y ∧
        (∀ l, ((S l).filter fun p => a p = true).card ≤ 2) ∧
        (∀ p : Fin 13, (Y.filter fun l => p ∈ S l).card ≤ 2) ∧
        PEqualNP.GenericRejection.IsMaximalFalse S X Y
      ∀ mask ∈ ([(7,904),(13,2848),(19,708),(21,2720),(25,2656),(37,2440),(41,2370),(133,808)] : List (ℕ × ℕ)), ∀ m ∈ ([1,3,9] : List (Fin 13)),
      ∀ (t : Fin 13) (dual : Bool),
        let pick := fun (a b : ℕ) (i : Fin 13) =>
          if dual = true then b.testBit (-(m*i+t)).val else a.testBit (m*i+t).val
        clean (pick mask.1 mask.2) (pick mask.2 mask.1))
    (search : let S := PEqualNP.HeptadCover.singerLines3
      let clean := fun (a b : Fin 13 → Bool) =>
        let X := Finset.univ.filter fun i => a i = true
        let Y := Finset.univ.filter fun i => b i = true
        PEqualNP.GenericRejection.IsFalseInput S X Y ∧
        (∀ l, ((S l).filter fun p => a p = true).card ≤ 2) ∧
        (∀ p : Fin 13, (Y.filter fun l => p ∈ S l).card ≤ 2) ∧
        PEqualNP.GenericRejection.IsMaximalFalse S X Y
      ∃ (op : Fin 63 → Bool) (a b : Fin 63 → Fin 89),
      (∀ j, (a j).val < 26+j.val ∧ (b j).val < 26+j.val ∧ a j ≤ b j) ∧
      let f := fun (x : Fin 26 → Bool) =>
        ((List.ofFn fun j => (op j,a j,b j)).foldl (fun w g => w ++ [
          bif g.1 then w.getD g.2.1.val false && w.getD g.2.2.val false else
            w.getD g.2.1.val false || w.getD g.2.2.val false]) (List.ofFn x)).getD 88 false
      (∀ p l : Fin 13, p ∈ S l →
        f (fun i => decide (i=Fin.castAdd 13 p ∨ i=Fin.natAdd 13 l)) = true) ∧
      ∀ X Y, clean X Y → f (Fin.append X Y) = false) :
    (have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : List (ℕ × ℕ) := [((7 : ℕ), (904 : ℕ)), ((13 : ℕ), (2848 : ℕ)), ((19 : ℕ), (708 : ℕ)), ((21 : ℕ), (2720 : ℕ)), ((25 : ℕ), (2656 : ℕ)), ((37 : ℕ), (2440 : ℕ)), ((41 : ℕ), (2370 : ℕ)), ((133 : ℕ), (808 : ℕ))]; have x3 : ℕ × ℕ → Fin (13 : ℕ) → Fin (13 : ℕ) → Bool → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x3 : ℕ × ℕ) (x4 x5 : Fin (13 : ℕ)) (x6 : Bool) =>   have x7 : ℕ → ℕ → Fin (13 : ℕ) → Bool := fun (x7 x8 : ℕ) (x9 : Fin (13 : ℕ)) => if x6 = Bool.true then x8.testBit ↑(-(x4 * x9 + x5)) else x7.testBit ↑(x4 * x9 + x5);   Fin.append (x7 x3.1 x3.2) (x7 x3.2 x3.1); ∃ (x4 : Fin (63 : ℕ) → Bool) (x5 : Fin (63 : ℕ) → Fin (89 : ℕ)) (x6 : Fin (63 : ℕ) → Fin (89 : ℕ)),   (∀ (x7 : Fin (63 : ℕ)), ↑(x5 x7) < (26 : ℕ) + ↑x7 ∧ ↑(x6 x7) < (26 : ℕ) + ↑x7 ∧ x5 x7 ≤ x6 x7) ∧     have x7 : (Fin (26 : ℕ) → Bool) → Bool := fun (x7 : Fin (26 : ℕ) → Bool) => (List.foldl (fun (x8 : List Bool) (x9 : Bool × Fin (89 : ℕ) × Fin (89 : ℕ)) => x8 ++ [bif x9.1 then x8.getD (↑x9.2.1) Bool.false && x8.getD (↑x9.2.2) Bool.false else x8.getD (↑x9.2.1) Bool.false || x8.getD (↑x9.2.2) Bool.false]) (List.ofFn x7) (List.ofFn fun (x8 : Fin (63 : ℕ)) => (x4 x8, x5 x8, x6 x8))).getD (88 : ℕ) Bool.false;     (∀ (x8 x9 : Fin (13 : ℕ)), (∃ x10 ∈ x1, x8 = x9 + x10) → (x7 fun (x11 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x11 = Fin.castAdd (13 : ℕ) x8 ∨ x11 = Fin.natAdd (13 : ℕ) x9)) = Bool.true) ∧ ∀ x8 ∈ x2, ∀ x10 ∈ [(1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], ∀ (x12 : Fin (13 : ℕ)) (x13 : Bool), x7 (x3 x8 x10 x12 x13) = Bool.false) := by
  obtain ⟨op,a,b,order,yes,no⟩ := search
  refine ⟨op,a,b,order,?_,?_⟩
  · have incidence : ∀ p l : Fin 13, (∃ d ∈ ({0,1,3,9} : Finset (Fin 13)), p=l+d) →
          p ∈ PEqualNP.HeptadCover.singerLines3 l := by decide +kernel
    intro p l h
    exact yes p l (incidence p l h)
  intro mask hm mult hu shift dual
  exact no _ _ (geometry mask hm mult hu shift dual)
