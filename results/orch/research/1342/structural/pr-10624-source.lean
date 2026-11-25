import Mathlib.Tactic.FinCases
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_5230_1
    (coverSteps : ∀ U : Finset (Sym2 (Fin 11)), ∀ K : Finset (Fin 11),
      ((edgeGraph 11 ([9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97].map
        fun e => (e / 11, e % 11))).deleteEdges ↑U).IsVertexCover ↑K →
      ([16, 12, 8, 5, 3, 2, 1] : List ℕ).getD K.card 0 ≤ U.card)
    (routes : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (w j : ℕ), IsAO2 n C → j ∈ junk G C → OrReaches n C w j →
      (w = n + j ∧ orIn n C w = ∅) ∨
        ∃ m ∈ orN G C \ lam G C, OrReaches n C w m ∧ n + j ∈ (gateAt C m).inputs)
    (obstruction :
      let G := edgeGraph 11 ([9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97].map
        fun e => (e / 11, e % 11))
      ∀ [inst : DecidableRel G.Adj] (C : Circuit) (i j : ℕ),
      IsLeastAO G C → TopForm G C → junk G C = {i,j} → InCone 11 C i j →
      let U := Ustar G C
      let Z := centreless G C
      let R := orN G C \ lam G C
      let A := tops G C
      (∀ u v : Fin 11, s(u,v) ∈ U →
        ∃ a ∈ A, ∃ (b : Fin 2) (k : ℕ), k ∈ junk G C ∧
          gateVal 11 C a (pairInput u v) = true ∧ gateVal 11 C k (pairInput u v) = true ∧
          ((a ∈ Z ∧ opnd C a b = 11 + k) ∨
            ∃ m ∈ R, OrReaches 11 C (opnd C a b) m ∧ 11 + k ∈ (gateAt C m).inputs)) →
      4 ≤ U.card → C.size ≤ 21 →
      ∀ K : Finset (Fin 11), IsMinCover (G.deleteEdges ↑U) K →
        ([16,12,8,5,3,2,1] : List ℕ).getD K.card 0 ≤ U.card →
        K.card ≤ (A \ Z).card →
        0 < 2 * Z.card + R.card →
        (A \ Z).card + 2 * Z.card + R.card ≤ C.size + U.card - 17 → False) :
    ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) (List.map (fun (x6 : ℕ) => (x6 / (11 : ℕ), x6 % (11 : ℕ))) [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ), (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)]) →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         PEqualNP.TopForm.junk x1 x3 = {x4, x5} →           PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x4 x5 →             have x11 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;             have x12 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;             have x13 : Finset ℕ := PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3;             have x14 : Finset ℕ := PEqualNP.TopForm.tops x1 x3;             (∀ x15 ∈ x14,                 have x17 : Fin (2 : ℕ) → Finset (Fin (11 : ℕ)) := PEqualNP.TopForm.side x3 x15;                 (∀ x18 ∈ x17 (0 : Fin (2 : ℕ)), ∀ x20 ∈ x17 (1 : Fin (2 : ℕ)), x1.Adj x18 x20) ∧ ((x17 (0 : Fin (2 : ℕ))).card ≤ (1 : ℕ) ∨ (x17 (1 : Fin (2 : ℕ))).card ≤ (1 : ℕ))) →               (∀ (x16 x17 : Fin (11 : ℕ)), s(x16, x17) ∈ x11 → ∃ x19 ∈ x14, ∃ (x20 : Fin (2 : ℕ)), ∃ x21 ∈ PEqualNP.TopForm.junk x1 x3, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x19 (PEqualNP.EdgeOwnership.pairInput x16 x17) = Bool.true ∧ PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x3 (PEqualNP.TopForm.opnd x3 x19 x20) x21 ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x21 (PEqualNP.EdgeOwnership.pairInput x16 x17) = Bool.true) → x3.size ≤ (21 : ℕ) → (4 : ℕ) ≤ x11.card → ∀ (x19 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x11) x19 → (7 : ℕ) ≤ x19.card + x11.card → x19.card ≤ (x14 \ x12).card → (0 : ℕ) < (2 : ℕ) * x12.card + x13.card → (x14 \ x12).card + (2 : ℕ) * x12.card + x13.card ≤ x3.size + x11.card - (17 : ℕ) → False := by
  intro G inst C i j hg least form dirt nested
  dsimp only
  intro _star trace small many K minimum _coverSum coverTop positive account
  subst G
  have sparse := coverSteps _ K minimum.1
  apply obstruction C i j least form dirt nested _ many small K minimum sparse
    coverTop positive account
  intro u v hu
  obtain ⟨a, ha, b, k, hk, htrue, walk, ktrue⟩ := trace u v hu
  refine ⟨a, ha, b, k, hk, htrue, ktrue, ?_⟩
  rcases routes 11 _ C (opnd C a b) k least.1 hk walk with ⟨direct, empty⟩ | indirect
  · refine Or.inl ⟨Finset.mem_filter.mpr ⟨ha, ?_⟩, direct⟩
    fin_cases b
    · exact Or.inl empty
    · exact Or.inr empty
  · exact Or.inr indirect
