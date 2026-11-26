import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm

-- A minimal excess family has exactly one more edge than its available
-- budget. Every junk gate that detects such an edge detects at least two.
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.R_meta_2382_481
    (critical : ∀ (U : Finset (Sym2 (Fin 11))) (J : Finset ℕ)
      (A : ℕ → Finset (Sym2 (Fin 11))) (b : ℕ),
      let n := fun V => J.filter (fun j => (V ∩ A j).Nonempty)
      J.card + b < U.card →
      ∃ V ⊆ U, (n V).card + b + 1 = V.card ∧
        (∀ W ⊂ V, W.card ≤ (n W).card + b) ∧
        ∀ j ∈ J, (V ∩ A j).card ≠ 1)
    (exclude :
      let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
        (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
      ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C →
        let J := junk G C
        let U := Ustar G C
        let b := 2 * (centreless G C).card + (orN G C \ lam G C).card
        let A := gammaE G C
        let n := fun V => J.filter (fun j => (V ∩ A j).Nonempty)
        2 ≤ J.card → J.card + b < 2 * U.card →
        (∀ e ∈ U, ∃ j ∈ J, e ∈ A j) →
        ∀ V ⊆ U, (n V).card + b + 1 = V.card →
          (∀ W ⊂ V, W.card ≤ (n W).card + b) →
          (∀ j ∈ J, (V ∩ A j).card ≠ 1) → False) :
  (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   x2.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x1 x2 →       PEqualNP.TopForm.TopForm x1 x2 →         (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →           have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;           have x8 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;           (∀ (x9 x10 : Fin (11 : ℕ)), s(x9, x10) ∈ x7 → ∃ x12 ∈ PEqualNP.TopForm.junk x1 x2, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x2 x12 (PEqualNP.EdgeOwnership.pairInput x9 x10) = Bool.true) → x8 < (2 : ℕ) * x7.card → x7.card ≤ x8) := by
  classical
  let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
    (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
  dsimp only
  intro C size least top two cov dbl
  let J := junk G C
  let U := Ustar G C
  let b := 2 * (centreless G C).card + (orN G C \ lam G C).card
  change 2 ≤ J.card at two
  change 2 * (centreless G C).card + J.card + (orN G C \ lam G C).card < 2 * U.card at dbl
  change U.card ≤ 2 * (centreless G C).card + J.card + (orN G C \ lam G C).card
  have budget : J.card + b = 2 * (centreless G C).card + J.card + (orN G C \ lam G C).card := by
    change J.card + (2 * (centreless G C).card + (orN G C \ lam G C).card) = _
    omega
  have dbl' : J.card + b < 2 * U.card := budget.symm ▸ dbl
  by_contra contra
  have excess : J.card + b < U.card := budget.symm ▸ Nat.lt_of_not_ge contra
  have covers : ∀ e ∈ U, ∃ j ∈ J, e ∈ gammaE G C j := by
    intro e
    induction e using Sym2.inductionOn with
    | _ u v =>
      intro he
      obtain ⟨j,hj,hv⟩ := cov u v he
      have hadj : s(u,v) ∈ G.edgeFinset := (Finset.mem_sdiff.mp he).1
      exact ⟨j,hj,Finset.mem_filter.mpr ⟨hadj,u,v,rfl,hv⟩⟩
  obtain ⟨V,sub,eq,min,twice⟩ := critical U J (gammaE G C) b excess
  exact exclude C size least top two dbl' covers V sub eq min twice
