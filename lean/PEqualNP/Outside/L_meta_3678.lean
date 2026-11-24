import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3678

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership

lemma exists_least {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsAO2 n C) (hF : circuitFun n C = graphFun G ∅) :
    ∃ D : Circuit, IsLeastAO G D ∧ D.size ≤ C.size := by
  classical
  have hex : ∃ k : ℕ, ∃ D : Circuit,
      IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧ D.size = k :=
    ⟨_, C, hC, hF, rfl⟩
  obtain ⟨D, hD, hDF, hsize⟩ := Nat.find_spec hex
  refine ⟨D, ⟨hD, hDF, ?_⟩, ?_⟩
  · intro E hE hEF
    rw [hsize]
    exact Nat.find_min' hex ⟨E, hE, hEF, rfl⟩
  · rw [hsize]
    exact Nat.find_min' hex ⟨C, hC, hF, rfl⟩

lemma exists_least_min_andPairs {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : ∃ C : Circuit, IsAO2 n C ∧ circuitFun n C = graphFun G ∅) :
    ∃ D : Circuit, IsLeastAO G D ∧
      ∀ E : Circuit, IsLeastAO G E → andPairs n D ≤ andPairs n E := by
  classical
  obtain ⟨C, hC, hF⟩ := h
  obtain ⟨D, hD, -⟩ := exists_least G C hC hF
  have hex : ∃ k : ℕ, ∃ E : Circuit, IsLeastAO G E ∧ andPairs n E = k :=
    ⟨_, D, hD, rfl⟩
  obtain ⟨E, hE, hcount⟩ := Nat.find_spec hex
  refine ⟨E, hE, ?_⟩
  intro F hF
  rw [hcount]
  exact Nat.find_min' hex ⟨F, hF, rfl⟩

lemma andPairs_eq_zero_iff (n : ℕ) (C : Circuit) :
    andPairs n C = 0 ↔
      ∀ i < C.gates.length, ∀ j < C.gates.length,
        (gateAt C i).op = GateOp.and →
        (gateAt C j).op = GateOp.and → ¬ InCone n C i j := by
  classical
  simp only [andPairs, Finset.card_eq_zero, Finset.filter_eq_empty_iff,
    Finset.mem_product, Finset.mem_range]
  constructor
  · intro h i hi j hj hiand hjand hcone
    exact @h (i, j) ⟨hi, hj⟩ ⟨hiand, hjand, hcone⟩
  · intro h p hp hpand
    exact h p.1 hp.1 p.2 hp.2 hpand.1 hpand.2.1 hpand.2.2

lemma graphFun_single_color {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hs : ∀ u v, G.Adj u v → s u ≠ s v)
    (x : Fin n → Bool) (b : Bool) (hx : ∀ u, x u = true → s u = b) :
    graphFun G ∅ x = false := by
  have hn : ¬ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
    rintro ⟨u, v, huv, hu, hv⟩
    exact hs u v huv ((hx u hu).trans (hx v hv).symm)
  simp [graphFun, hn]

lemma graphFun_singleton {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v : Fin n) : graphFun G ∅ (fun w => decide (w = v)) = false := by
  simp [graphFun]

lemma normalize_edgeless {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : ∀ u v, ¬ G.Adj u v) :
    ∃ D : Circuit, IsLeastAO G D ∧
      ∀ i < D.gates.length, ∀ j < D.gates.length,
        (gateAt D i).op = GateOp.and →
        (gateAt D j).op = GateOp.and → ¬ InCone n D i j := by
  let D : Circuit := ⟨[], n⟩
  refine ⟨D, ⟨?_, ?_, ?_⟩, ?_⟩
  · simp [D, IsAO2, AndOrOnly, ReadsBack]
  · funext x
    simp [D, circuitFun, Circuit.eval, Circuit.wires, graphFun, hG, List.getD]
  · intro E _ _
    exact Nat.zero_le E.size
  · simp [D]

lemma least_zero_of_descent {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : ∃ C : Circuit, IsAO2 n C ∧ circuitFun n C = graphFun G ∅)
    (hd : ∀ C : Circuit, IsLeastAO G C → 0 < andPairs n C →
      ∃ D : Circuit, IsLeastAO G D ∧ andPairs n D < andPairs n C) :
    ∃ D : Circuit, IsLeastAO G D ∧ andPairs n D = 0 := by
  obtain ⟨D, hD, hmin⟩ := exists_least_min_andPairs G h
  refine ⟨D, hD, ?_⟩
  by_contra hzero
  obtain ⟨E, hE, hless⟩ := hd D hD (Nat.pos_of_ne_zero hzero)
  exact (Nat.not_lt_of_ge (hmin E hE)) hless

lemma normalize_of_descent {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : ∃ C : Circuit, IsAO2 n C ∧ circuitFun n C = graphFun G ∅)
    (hd : ∀ C : Circuit, IsLeastAO G C → 0 < andPairs n C →
      ∃ D : Circuit, IsLeastAO G D ∧ andPairs n D < andPairs n C) :
    ∃ D : Circuit, IsLeastAO G D ∧
      ∀ i < D.gates.length, ∀ j < D.gates.length,
        (gateAt D i).op = GateOp.and →
        (gateAt D j).op = GateOp.and → ¬ InCone n D i j := by
  obtain ⟨D, hD, hzero⟩ := least_zero_of_descent G h hd
  exact ⟨D, hD, (andPairs_eq_zero_iff n D).mp hzero⟩


lemma no_and_cone_of_size_le_one (n : ℕ) (C : Circuit) (hsize : C.size ≤ 1) :
    ∀ i < C.gates.length, ∀ j < C.gates.length,
      (gateAt C i).op = GateOp.and →
      (gateAt C j).op = GateOp.and → ¬ InCone n C i j := by
  rcases C with ⟨gates, output⟩
  cases gates with
  | nil => simp
  | cons g gs =>
    have hgs : gs = [] := by
      have : gs.length = 0 := by simpa [Circuit.size] using hsize
      exact List.length_eq_zero_iff.mp this
    subst gs
    intro i hi j hj _ _
    have hi0 : i = 0 := by simpa using hi
    have hj0 : j = 0 := by simpa using hj
    subst i
    subst j
    simp [InCone, cones, coneStep]

lemma exists_flat_of_small {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsAO2 n C) (hF : circuitFun n C = graphFun G ∅)
    (hsize : C.size ≤ 1) :
    ∃ D : Circuit, IsLeastAO G D ∧
      ∀ i < D.gates.length, ∀ j < D.gates.length,
        (gateAt D i).op = GateOp.and →
        (gateAt D j).op = GateOp.and → ¬ InCone n D i j := by
  obtain ⟨D, hD, hle⟩ := exists_least G C hC hF
  exact ⟨D, hD, no_and_cone_of_size_le_one n D (hle.trans hsize)⟩

end PEqualNP.Outside.L_meta_3678
