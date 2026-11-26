import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

-- This search must use an AND gate that accepts a rejected pair.
-- The supplied line unions cannot join two neighbors of any of the five active points.
set_option maxHeartbeats 3200000 in
theorem PEqualNP.Outside.R_meta_2712_417
    (pairs : let pins (x : Fin 26 → Bool) (i : Fin 20) :=
        if i.val < 17 then x (Fin.ofNat 26 (if i.val < 5 then i.val else if i.val < 14 then i.val+8 else i.val+9))
        else ((decide (i.val ≠ 18) && (x 16 || x 18)) || (decide (i.val ≠ 17) && (x 19 || x 23)))
      let near (p l : Fin 13) := ∃ d ∈ ([0,1,3,9] : List (Fin 13)), p = l+d
      let duo (u v i : Fin 26) := decide (i = u ∨ i = v)
      ∀ f : (Fin 20 → Bool) → Bool,
      (∀ p l : Fin 13, p.val < 5 → near p l →
        f (pins (duo (Fin.castAdd 13 p) (Fin.natAdd 13 l))) = true) →
      (∀ x : Fin 26 → Bool,
        (∀ p l : Fin 13, x (Fin.castAdd 13 p) = true → x (Fin.natAdd 13 l) = true → ¬ near p l) →
        ((∃ l : Fin 13, ∀ p : Fin 13, x (Fin.castAdd 13 p) = true → near p l) ∨
         ∃ p : Fin 13, ∀ l : Fin 13, x (Fin.natAdd 13 l) = true → near p l) →
        f (pins x) = false) →
      ∀ u v : Fin 26, f (pins (duo u v)) = true ↔ ∃ p l : Fin 13, p.val < 5 ∧ near p l ∧
          duo u v (Fin.castAdd 13 p) = true ∧ duo u v (Fin.natAdd 13 l) = true)
    (bound : let pins (x : Fin 26 → Bool) (i : Fin 20) :=
        if i.val < 17 then x (Fin.ofNat 26 (if i.val < 5 then i.val else if i.val < 14 then i.val+8 else i.val+9))
        else ((decide (i.val ≠ 18) && (x 16 || x 18)) || (decide (i.val ≠ 17) && (x 19 || x 23)))
      let near (p l : Fin 13) := ∃ d ∈ ([0,1,3,9] : List (Fin 13)), p = l+d
      let duo (u v i : Fin 26) := decide (i = u ∨ i = v)
      ∀ C : Circuit, IsAO2 20 C →
      (∀ u v : Fin 26, circuitFun 20 C (pins (duo u v)) = true ↔ ∃ p l : Fin 13, p.val < 5 ∧ near p l ∧
          duo u v (Fin.castAdd 13 p) = true ∧ duo u v (Fin.natAdd 13 l) = true) →
      (∀ j < C.size, (gateAt C j).op = GateOp.and → ∀ u v : Fin 26,
        (C.wires (List.ofFn (pins (duo u v)))).getD (20+j) false = true →
        circuitFun 20 C (pins (duo u v)) = true) → 24 ≤ C.size)
    (search : let pins (x : Fin 26 → Bool) (i : Fin 20) :=
        if i.val < 17 then x (Fin.ofNat 26 (if i.val < 5 then i.val else if i.val < 14 then i.val+8 else i.val+9))
        else ((decide (i.val ≠ 18) && (x 16 || x 18)) || (decide (i.val ≠ 17) && (x 19 || x 23)))
      let near (p l : Fin 13) := ∃ d ∈ ([0,1,3,9] : List (Fin 13)), p = l+d
      let duo (u v i : Fin 26) := decide (i = u ∨ i = v)
      let pass (C : Circuit) := IsAO2 20 C ∧ C.size ≤ 23 ∧
        let f := circuitFun 20 C
        (∀ p l : Fin 13, p.val < 5 → near p l →
        f (pins (duo (Fin.castAdd 13 p) (Fin.natAdd 13 l))) = true) ∧ (∀ x : Fin 26 → Bool,
        (∀ p l : Fin 13, x (Fin.castAdd 13 p) = true → x (Fin.natAdd 13 l) = true → ¬ near p l) →
        ((∃ l : Fin 13, ∀ p : Fin 13, x (Fin.castAdd 13 p) = true → near p l) ∨
         ∃ p : Fin 13, ∀ l : Fin 13, x (Fin.natAdd 13 l) = true → near p l) →
        f (pins x) = false)
      (∀ C, pass C → ¬ (∀ j < C.size, (gateAt C j).op = GateOp.and → ∀ u v : Fin 26,
        (C.wires (List.ofFn (pins (duo u v)))).getD (20+j) false = true →
        circuitFun 20 C (pins (duo u v)) = true)) → ∃ C, pass C) :
    have x1 : (Fin (26 : ℕ) → Bool) → Fin (20 : ℕ) → Bool := fun (x1 : Fin (26 : ℕ) → Bool) (x2 : Fin (20 : ℕ)) => if ↑x2 < (17 : ℕ) then x1 (Fin.ofNat (26 : ℕ) (if ↑x2 < (5 : ℕ) then ↑x2 else if ↑x2 < (14 : ℕ) then ↑x2 + (8 : ℕ) else ↑x2 + (9 : ℕ))) else Decidable.decide (↑x2 ≠ (18 : ℕ)) && (x1 (16 : Fin (26 : ℕ)) || x1 (18 : Fin (26 : ℕ))) || Decidable.decide (↑x2 ≠ (17 : ℕ)) && (x1 (19 : Fin (26 : ℕ)) || x1 (23 : Fin (26 : ℕ))); have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ [(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], x2 = x3 + x4; ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 ∧ x3.size ≤ (23 : ℕ) ∧ (∀ (x4 x5 : Fin (13 : ℕ)), ↑x4 < (5 : ℕ) → x2 x4 x5 → PEqualNP.MetaComplexity.circuitFun (20 : ℕ) x3 (x1 fun (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) x4 ∨ x8 = Fin.natAdd (13 : ℕ) x5)) = Bool.true) ∧ ∀ (x4 : Fin (26 : ℕ) → Bool), (∀ (x5 x6 : Fin (13 : ℕ)), x4 (Fin.castAdd (13 : ℕ) x5) = Bool.true → x4 (Fin.natAdd (13 : ℕ) x6) = Bool.true → ¬x2 x5 x6) → ((∃ (x6 : Fin (13 : ℕ)), ∀ (x7 : Fin (13 : ℕ)), x4 (Fin.castAdd (13 : ℕ) x7) = Bool.true → x2 x7 x6) ∨ ∃ (x6 : Fin (13 : ℕ)), ∀ (x7 : Fin (13 : ℕ)), x4 (Fin.natAdd (13 : ℕ) x7) = Bool.true → x2 x6 x7) → PEqualNP.MetaComplexity.circuitFun (20 : ℕ) x3 (x1 x4) = Bool.false := by
  intro pins near
  classical
  let duo (u v i : Fin 26) := decide (i = u ∨ i = v)
  let pass (C : Circuit) := IsAO2 20 C ∧ C.size ≤ 23 ∧
      let f := circuitFun 20 C
      (∀ p l : Fin 13, p.val < 5 → near p l →
        f (pins (duo (Fin.castAdd 13 p) (Fin.natAdd 13 l))) = true) ∧ (∀ x : Fin 26 → Bool,
        (∀ p l : Fin 13, x (Fin.castAdd 13 p) = true → x (Fin.natAdd 13 l) = true → ¬ near p l) →
        ((∃ l : Fin 13, ∀ p : Fin 13, x (Fin.castAdd 13 p) = true → near p l) ∨
         ∃ p : Fin 13, ∀ l : Fin 13, x (Fin.natAdd 13 l) = true → near p l) →
        f (pins x) = false)
  let safe (C : Circuit) := ∀ j < C.size, (gateAt C j).op = GateOp.and → ∀ u v : Fin 26,
        (C.wires (List.ofFn (pins (duo u v)))).getD (20+j) false = true →
        circuitFun 20 C (pins (duo u v)) = true
  have necessary (C : Circuit) (good : pass C) : ¬ safe C := by
    intro all
    obtain ⟨earlier, small, hits, rejects⟩ := good
    have actual := pairs (circuitFun 20 C) hits rejects
    have low := bound C earlier actual all
    omega
  obtain ⟨C, good⟩ := search necessary
  obtain ⟨earlier, small, hits, rejects⟩ := good
  exact ⟨C, fun g hg => ⟨earlier.1 g hg, (earlier.2.2 g hg).le⟩, small, hits, rejects⟩
