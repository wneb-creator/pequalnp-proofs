import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.R_meta_4833_317
    (pairCleanReduction :
      let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
        (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
      ∀ (v : Fin 11) (C : Circuit), v.val < 4 → IsAO2 11 C → C.size ≤ 18 →
        (∀ x, x v = false → circuitFun 11 C x = graphFun G ∅ x) →
        ∃ D : Circuit, IsAO2 11 D ∧ D.size ≤ C.size ∧
          circuitFun 11 D = graphFun (G.deleteIncidenceSet v) ∅ ∧
          ∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
            ∀ a b : Fin 11, ¬(G.deleteIncidenceSet v).Adj a b →
              gateVal 11 D j (pairInput a b) = false)
    (pairCleanCount :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
        NoFourCycle G → IsAO2 n C → circuitFun n C = graphFun G ∅ →
        (∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
          ∀ a b : Fin n, ¬G.Adj a b → gateVal n C j (pairInput a b) = false) →
        ∃ T : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → a ∈ T ∨ b ∈ T) ∧
          G.edgeFinset.card + T.card ≤ C.size + 1) :
let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : Fin (11 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), ↑x2 < (4 : ℕ) → PEqualNP.TopForm.IsAO2 (11 : ℕ) x3 → (∀ (x6 : Fin (11 : ℕ) → Bool), x6 x2 = Bool.false → PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x3 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x1 ∅ x6) → (19 : ℕ) ≤ x3.size := by
  intro G v C hv hao agrees
  by_contra! short
  let H := G.deleteIncidenceSet v
  obtain ⟨D, dAO, dsize, dFun, dClean⟩ :=
    pairCleanReduction v C hv hao (by omega) agrees
  have noCycleG : NoFourCycle G := by decide +kernel
  have noCycleH : NoFourCycle H := by
    intro a b hab
    refine (Finset.card_le_card ?_).trans (noCycleG a b hab)
    intro w hw
    obtain ⟨_, h₁, h₂⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      G.deleteIncidenceSet_le v h₁, G.deleteIncidenceSet_le v h₂⟩
  obtain ⟨T, cover, bound⟩ := pairCleanCount 11 H D noCycleH dAO dFun dClean
  have edgesG : G.edgeFinset.card = 16 := by decide +kernel
  have degSmall : ∀ w : Fin 11, w.val < 4 → G.degree w = 2 := by decide +kernel
  have edgesH : H.edgeFinset.card = 14 := by
    change (G.deleteIncidenceSet v).edgeFinset.card = 14
    rw [SimpleGraph.card_edgeFinset_deleteIncidenceSet, edgesG, degSmall v hv]
  let es : List (Fin 11 × Fin 11) := [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),
    (3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
  let hits (w : Fin 11) (S : Finset (Fin 11)) : Bool :=
    es.all (fun e => decide (e.1 = w ∨ e.2 = w ∨ e.1 ∈ S ∨ e.2 ∈ S))
  have coverCertificate : ∀ w : Fin 11, w.val < 4 → ∀ S : Finset (Fin 11),
      hits w S = true → 6 ≤ S.card := by
    decide +kernel
  have listed : ∀ e ∈ es, G.Adj e.1 e.2 := by
    decide +kernel
  have hitsT : hits v T = true := by
    apply List.all_eq_true.mpr
    intro e he
    apply decide_eq_true
    by_cases left : e.1 = v
    · exact Or.inl left
    by_cases right : e.2 = v
    · exact Or.inr (Or.inl right)
    exact Or.inr (Or.inr (cover e.1 e.2
      (SimpleGraph.deleteIncidenceSet_adj.mpr ⟨listed e he, left, right⟩)))
  have six := coverCertificate v hv T hitsT
  omega
