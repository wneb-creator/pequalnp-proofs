import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_17136_1
  (cover : let G : SimpleGraph (Fin 11) := edgeGraph 11 [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
    ∀ F : Finset (Sym2 (Fin 11)), ∀ K : Finset (Fin 11),
      CoverPromise.IsVertexCover (G.deleteEdges ↑F) K → 7 ≤ K.card + F.card)
  (small : let G : SimpleGraph (Fin 11) := edgeGraph 11 [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
    ∀ (C : Circuit) (v : Fin 11), v < 4 → IsAO2 11 C →
      (∀ x : Fin 11 → Bool, x v = false → circuitFun 11 C x = graphFun G ∅ x) →
      (List.countP (fun g : Gate => GateOp.rec Bool.false Bool.true Bool.false
        (fun _ : ℕ => Bool.false) Bool.false g.op) C.gates) ≤ 12 →
      ∃ F : Finset (Sym2 (Fin 11)), ∃ K : Finset (Fin 11),
        CoverPromise.IsVertexCover (G.deleteEdges ↑F) K ∧ K.card + F.card ≤ 6) :
  (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : Fin (11 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), ↑x2 < (4 : ℕ) → PEqualNP.TopForm.IsAO2 (11 : ℕ) x3 → (∀ (x6 : Fin (11 : ℕ) → Bool), x6 x2 = Bool.false → PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x3 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x1 ∅ x6) → (13 : ℕ) ≤ List.countP (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.true Bool.false (fun (x8 : ℕ) => Bool.false) Bool.false x7.op) x3.gates) := by
  intro G v C hv hAO hagree
  by_contra hnot
  have hle : (List.countP (fun g : Gate => GateOp.rec Bool.false Bool.true Bool.false
      (fun _ : ℕ => Bool.false) Bool.false g.op) C.gates) ≤ 12 := by omega
  rcases small C v hv hAO hagree hle with ⟨F, K, hcov, hsmall⟩
  have hb := cover F K hcov
  omega
