import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1772.Local

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma owns_of_topForm_local {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (htop : TopForm G C) (j : ℕ) (hj : j < C.gates.length)
    (hand : (gateAt C j).op = GateOp.and) (u v : Fin n)
    (hval : gateVal n C j (pairInput u v) = true)
    (hlocal : ∀ i < j, InCone n C i j → (gateAt C i).op = GateOp.and →
      gateVal n C i (pairInput u v) = true → BelowF G C i) :
    Owns n C j u v := by
  refine ⟨hj, hand, hval, ?_⟩
  intro i hij hcone hiand
  cases hival : gateVal n C i (pairInput u v) with
  | false => rfl
  | true =>
    exact False.elim (htop i (hij.trans hj) j hj hiand
      (hlocal i hij hcone hiand hival) hand hcone)

lemma every_owned_of_topForm_local {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (htop : TopForm G C)
    (hedge : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∃ u v, G.Adj u v ∧ gateVal n C j (pairInput u v) = true)
    (hlocal : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      (∀ u v, G.Adj u v → ¬ Owns n C j u v) →
      ∀ u v, G.Adj u v → gateVal n C j (pairInput u v) = true →
      ∀ i < j, InCone n C i j → (gateAt C i).op = GateOp.and →
        gateVal n C i (pairInput u v) = true → BelowF G C i) :
    ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∃ u v, G.Adj u v ∧ Owns n C j u v := by
  intro j hj hand
  by_contra hnone
  have hbad : ∀ u v, G.Adj u v → ¬ Owns n C j u v :=
    fun u v huv howns => hnone ⟨u, v, huv, howns⟩
  obtain ⟨u, v, huv, hval⟩ := hedge j hj hand
  exact hnone ⟨u, v, huv, owns_of_topForm_local G C htop j hj hand u v hval
    (hlocal j hj hand hbad u v huv hval)⟩

lemma minimum_local_to_owned {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hex : ∃ C : Circuit, IsMinimalMonoCircuit n C ∧
      circuitFun n C = graphFun G ∅ ∧ TopForm G C ∧
      (∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
        ∃ u v, G.Adj u v ∧ gateVal n C j (pairInput u v) = true) ∧
      (∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
        (∀ u v, G.Adj u v → ¬ Owns n C j u v) →
        ∀ u v, G.Adj u v → gateVal n C j (pairInput u v) = true →
        ∀ i < j, InCone n C i j → (gateAt C i).op = GateOp.and →
          gateVal n C i (pairInput u v) = true → BelowF G C i)) :
    ∃ C : Circuit, IsMinimalMonoCircuit n C ∧
      circuitFun n C = graphFun G ∅ ∧
      ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
        ∃ u v, G.Adj u v ∧ Owns n C j u v := by
  obtain ⟨C, hmin, hcomp, htop, hedge, hlocal⟩ := hex
  exact ⟨C, hmin, hcomp, every_owned_of_topForm_local G C htop hedge hlocal⟩

end PEqualNP.Outside.L_meta_1772.Local
