import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.ReadTwo

theorem PEqualNP.Outside.R_meta_7887_1
    (firstTwo : ∀ (N : ℕ) (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (C : Circuit) (a b : ℕ),
      IsAO2 N C → TopForm G C → a ∈ junk G C → b ∈ junk G C → a < b →
      (∀ j ∈ junk G C, j < b → j = a) →
      ∀ j ∈ ([a,b] : List ℕ), ∀ x : Fin N → Bool,
        wval C x (N+j) = true ↔ ∀ t : Fin 2,
          (∃ v ∈ side (n := N) C j t, x v = true) ∨
          (j = b ∧ OrReaches N C (opnd C j t) a ∧ wval C x (N+a) = true))
    (restricted : let N := 11
      let G := edgeGraph 11 (([9, 10, 15, 19, 27, 32, 39, 40, 52, 54, 63, 64, 73, 76, 86, 97] : List ℕ).map fun k => (k / 11, k % 11))
      ∀ (C : Circuit) (a b : ℕ), IsLeastAO G C → TopForm G C → C.size ≤ 21 →
      a ∈ junk G C → b ∈ junk G C → a < b →
      2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card < 2 * (Ustar G C).card →
      (∀ j ∈ ([a,b] : List ℕ), ∀ x : Fin N → Bool,
        wval C x (N+j) = true ↔ ∀ t : Fin 2,
          (∃ v ∈ side (n := N) C j t, x v = true) ∨
          (j = b ∧ OrReaches N C (opnd C j t) a ∧ wval C x (N+a) = true)) →
      ∃ v : Fin 11, v.val < 4 ∧
        let vanishes := fun j => ∃ i < 11+j, ∀ x : Fin 11 → Bool, x v = false →
          wval C x (11+j) = wval C x i
        ∃ i j k, i < j ∧ j < k ∧ k < C.size ∧ vanishes i ∧ vanishes j ∧ vanishes k) :
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsLeastAO x1 x2 →     PEqualNP.TopForm.TopForm x1 x2 →       (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →         x2.size ≤ (21 : ℕ) →           (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card →             (∀ (x8 : Fin (11 : ℕ)),                 ↑x8 < (4 : ℕ) →                   ¬have x10 : ℕ → Prop := fun (x10 : ℕ) => x10 < x2.size ∧ ↑x8 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x10).inputs;                     (∃ (x11 : ℕ) (x12 : ℕ) (x13 : ℕ), x11 < x12 ∧ x12 < x13 ∧ x10 x11 ∧ x10 x12 ∧ x10 x13) ∨ ∃ (x11 : ℕ) (x12 : ℕ), x11 ≠ x12 ∧ x10 x11 ∧ x10 x12 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and) →               ∃ (x9 : Fin (11 : ℕ)),                 ↑x9 < (4 : ℕ) ∧                   have x10 : ℕ → Prop := fun (x10 : ℕ) => ∃ x11 < (11 : ℕ) + x10, ∀ (x12 : Fin (11 : ℕ) → Bool), x12 x9 = Bool.false → PEqualNP.ReadTwo.wval x2 x12 ((11 : ℕ) + x10) = PEqualNP.ReadTwo.wval x2 x12 x11;                   ∃ (x11 : ℕ) (x12 : ℕ) (x13 : ℕ), x11 < x12 ∧ x12 < x13 ∧ x13 < x2.size ∧ x10 x11 ∧ x10 x12 ∧ x10 x13 := by
  classical
  dsimp only
  intro C hLeast hTop hJunk hSize hCharge hSparse
  let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
  have rep : let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsLeastAO x1 x2 →     PEqualNP.TopForm.TopForm x1 x2 →       (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →         x2.size ≤ (21 : ℕ) →           (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card →             ∃ (x8 : Fin (11 : ℕ)),               ↑x8 < (4 : ℕ) ∧                 have x9 : ℕ → Prop := fun (x9 : ℕ) => ∃ x10 < (11 : ℕ) + x9, ∀ (x11 : Fin (11 : ℕ) → Bool), x11 x8 = Bool.false → PEqualNP.ReadTwo.wval x2 x11 ((11 : ℕ) + x9) = PEqualNP.ReadTwo.wval x2 x11 x10;                 ∃ (x10 : ℕ) (x11 : ℕ) (x12 : ℕ), x10 < x11 ∧ x11 < x12 ∧ x12 < x2.size ∧ x9 x10 ∧ x9 x11 ∧ x9 x12 := by
    intro G C least top many small deficit
    let J := junk G C
    have pos : J.Nonempty := Finset.card_pos.mp (by change 0 < (junk G C).card; omega)
    let a := J.min' pos
    have ha : a ∈ J := J.min'_mem _
    let K := J.erase a
    have kcard : K.card = J.card - 1 := Finset.card_erase_of_mem ha
    have kn : K.Nonempty := Finset.card_pos.mp (by change 2 ≤ J.card at many; omega)
    let b := K.min' kn
    have hb : b ∈ K := K.min'_mem _
    have split := Finset.mem_erase.mp hb
    have hab : a < b := lt_of_le_of_ne (J.min'_le _ split.2) (Ne.symm split.1)
    have early (j : ℕ) (hj : j ∈ J) (hlt : j < b) : j = a := by
      by_contra ne
      exact (not_lt_of_ge (K.min'_le j (Finset.mem_erase.mpr ⟨ne,hj⟩))) hlt
    exact restricted C a b least top small ha split.2 hab deficit
      (firstTwo 11 G C a b least.1 top ha split.2 hab early)
  exact rep C hLeast hTop hJunk hSize hCharge
