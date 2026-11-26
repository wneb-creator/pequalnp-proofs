import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm

-- Remove exactly as many unused junk gates as excluded residual edges.
-- The known residual-connection lemma pays a deficit of one.
-- The remaining supports either intersect pairwise or contain disjoint edges.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.R_meta_6752_859
  (connect : ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (C : Circuit),
    IsLeastAO G C → TopForm G C → (Ustar G C).Nonempty →
    (centreless G C).Nonempty ∨ (orN G C \ lam G C).Nonempty)
  (intersecting : let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
    ∀ (C : Circuit) (X : Finset (Sym2 (Fin 11))) (K : Finset ℕ),
    let U := Ustar G C
    let J := junk G C
    let F := fun g => X ∩ gammaE G C g
    C.size ≤ 21 → IsLeastAO G C → TopForm G C → 2 ≤ J.card →
    X ⊆ U → K ⊆ J → X.card + J.card = U.card + K.card →
    (∀ g ∈ J \ K, Disjoint X (gammaE G C g)) →
    (∀ e ∈ X, ∃ g ∈ K, e ∈ F g) → (∀ g ∈ K, (F g).card ≠ 1) →
    K.card + 1 < X.card →
    (∀ g ∈ K, ∀ e ∈ F g, ∀ f ∈ F g, ¬Disjoint e.toFinset f.toFinset) →
    X.card ≤ 2*(centreless G C).card + K.card + (orN G C \ lam G C).card)
  (separated : let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
    ∀ (C : Circuit) (X : Finset (Sym2 (Fin 11))) (K : Finset ℕ),
    let U := Ustar G C
    let J := junk G C
    let F := fun g => X ∩ gammaE G C g
    C.size ≤ 21 → IsLeastAO G C → TopForm G C → 2 ≤ J.card →
    X ⊆ U → K ⊆ J → X.card + J.card = U.card + K.card →
    (∀ g ∈ J \ K, Disjoint X (gammaE G C g)) →
    (∀ e ∈ X, ∃ g ∈ K, e ∈ F g) → (∀ g ∈ K, (F g).card ≠ 1) →
    K.card + 1 < X.card →
    (∃ g ∈ K, ∃ e ∈ F g, ∃ f ∈ F g, Disjoint e.toFinset f.toFinset) →
    X.card ≤ 2*(centreless G C).card + K.card + (orN G C \ lam G C).card) :
let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   x2.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x1 x2 →       PEqualNP.TopForm.TopForm x1 x2 →         have x6 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;         have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;         (2 : ℕ) ≤ x6.card → ∀ x9 ⊆ x7, x9.Nonempty → (x7 \ x9).card ≤ {x12 ∈ x6 | Disjoint x9 (PEqualNP.TopForm.gammaE x1 x2 x12)}.card → (∀ x13 ∈ x6, (x9 ∩ PEqualNP.TopForm.gammaE x1 x2 x13).card ≠ (1 : ℕ)) → (∀ x14 ∈ x7, ∃ x16 ∈ x6, x14 ∈ PEqualNP.TopForm.gammaE x1 x2 x16) → x9.card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (x6.card - (x7 \ x9).card) + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card := by
  classical
  intro G C size least top J U many X within nonempty debt noSingle coverage
  let remove := J.filter fun j => Disjoint X (gammaE G C j)
  have enough : (U \ X).card ≤ remove.card := debt
  obtain ⟨unused, subUnused, eqUnused⟩ := Finset.exists_subset_card_eq enough
  let K := J \ unused
  have uj : unused ⊆ J := subUnused.trans (Finset.filter_subset _ _)
  have kj : K ⊆ J := Finset.sdiff_subset
  have complement := Finset.card_sdiff_add_card_eq_card within
  have available := Finset.card_sdiff_add_card_eq_card uj
  change K.card + unused.card = J.card at available
  have balance : X.card + J.card = U.card + K.card := by omega
  have count : K.card = J.card - (U \ X).card := by omega
  have covered : ∀ e ∈ X, ∃ g ∈ K, e ∈ X ∩ gammaE G C g := by
    intro e he
    obtain ⟨g, hg, support⟩ := coverage e (within he)
    have keeps : g ∉ unused := by
      intro bad
      exact Finset.disjoint_left.mp (Finset.mem_filter.mp (subUnused bad)).2 he support
    exact ⟨g,Finset.mem_sdiff.mpr ⟨hg,keeps⟩,Finset.mem_inter.mpr ⟨he,support⟩⟩
  have misses : ∀ g ∈ J \ K, Disjoint X (gammaE G C g) := by
    intro g hg
    obtain ⟨inJ,notK⟩ := Finset.mem_sdiff.mp hg
    have removed : g ∈ unused := by
      by_contra notRemoved
      exact notK (Finset.mem_sdiff.mpr ⟨inJ,notRemoved⟩)
    exact (Finset.mem_filter.mp (subUnused removed)).2
  have noOne (g : ℕ) (hg : g ∈ K) : (X ∩ gammaE G C g).card ≠ 1 := noSingle g (kj hg)
  by_cases cheap : X.card ≤ K.card + 1
  · have has := connect G C least top (nonempty.mono within)
    rcases has with left | right
    · have fee : 0 < (centreless G C).card := Finset.card_pos.mpr left
      rw [← count]
      omega
    · have fee : 0 < (orN G C \ lam G C).card := Finset.card_pos.mpr right
      rw [← count]
      omega
  have cost : K.card + 1 < X.card := Nat.lt_of_not_ge cheap
  rw [← count]
  by_cases far : ∃ g ∈ K, ∃ e ∈ X ∩ gammaE G C g, ∃ f ∈ X ∩ gammaE G C g,
      Disjoint e.toFinset f.toFinset
  · exact separated C X K size least top many within kj balance misses covered noOne cost far
  · exact intersecting C X K size least top many within kj balance misses covered noOne cost
      (fun g hg e he f hf dis => far ⟨g,hg,e,he,f,hf,dis⟩)
