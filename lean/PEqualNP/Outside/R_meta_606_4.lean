import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Pass to the bipartite double cover: points and lines are both the vertices of G, and
-- point p lies on line w when p and w are adjacent. Girth at least 5 makes this incidence
-- free of 4-cycles, and it has two incidences per edge.
theorem PEqualNP.Outside.R_meta_606_4
    (bipartite : ∃ c : ℕ, ∀ (P L : ℕ) (inc : Fin P → Fin L → Bool) (C : Circuit),
      (∀ (p p' : Fin P) (w w' : Fin L), p ≠ p' → w ≠ w' →
        ¬ (inc p w = true ∧ inc p w' = true ∧ inc p' w = true ∧ inc p' w' = true)) →
      IsMonotoneCircuit C → (∀ g ∈ C.gates, g.inputs.length ≤ 2) →
      (∀ (x : Fin P → Bool) (y : Fin L → Bool), C.eval (List.ofFn x ++ List.ofFn y) =
        decide (∃ (p : Fin P) (w : Fin L), inc p w = true ∧ x p = true ∧ y w = true)) →
      Fintype.card {e : Fin P × Fin L // inc e.1 e.2 = true} ≤ c * (C.gates.length + 1))
    (cover : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      ∀ D : Circuit, Monotone2 D →
      circuitFun n D = (fun x : Fin n → Bool => decide
        (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) →
      ∃ C : Circuit, IsMonotoneCircuit C ∧ (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
        C.gates.length ≤ k * (D.size + 1) ∧
        ∀ (x y : Fin n → Bool), C.eval (List.ofFn x ++ List.ofFn y) =
          decide (∃ p w : Fin n, G.Adj p w ∧ x p = true ∧ y w = true)) :
    ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D → PEqualNP.MetaComplexity.circuitFun n D = (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) → G.edgeFinset.card ≤ c * (D.size + 1) := by
  obtain ⟨c, hc⟩ := bipartite
  obtain ⟨k, hk⟩ := cover
  refine ⟨c * (k + 1), ?_⟩
  intro n G _ hg D hD hfun
  obtain ⟨C, hmon, hfan, hsize, hcomp⟩ := hk n G hg D hD hfun
  -- No 4-cycle in the double cover: it would be a 4-cycle of G.
  have hC4 : ∀ (p p' : Fin n) (w w' : Fin n), p ≠ p' → w ≠ w' →
      ¬ (decide (G.Adj p w) = true ∧ decide (G.Adj p w') = true ∧
        decide (G.Adj p' w) = true ∧ decide (G.Adj p' w') = true) := by
    intro p p' w w' hp hw h
    simp only [decide_eq_true_eq] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    have hpw := G.ne_of_adj h1
    have hpw' := G.ne_of_adj h2
    have hp'w := G.ne_of_adj h3
    have hp'w' := G.ne_of_adj h4
    let q : G.Walk p p :=
      SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h3.symm
        (SimpleGraph.Walk.cons h4 (SimpleGraph.Walk.cons h2.symm SimpleGraph.Walk.nil)))
    have hcyc : q.IsCycle := by
      simp only [q, SimpleGraph.Walk.cons_isCycle_iff, SimpleGraph.Walk.cons_isPath_iff,
        SimpleGraph.Walk.isPath_iff_eq_nil, SimpleGraph.Walk.support_cons,
        SimpleGraph.Walk.support_nil, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
        List.mem_cons, List.not_mem_nil, Sym2.eq_iff]
      refine ⟨⟨⟨⟨trivial, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;> grind
    have hlen := hg p q hcyc
    simp [q] at hlen
  have hcomp' : ∀ (x : Fin n → Bool) (y : Fin n → Bool),
      C.eval (List.ofFn x ++ List.ofFn y) =
        decide (∃ (p : Fin n) (w : Fin n), decide (G.Adj p w) = true ∧ x p = true ∧
          y w = true) := by
    intro x y
    rw [hcomp]
    simp only [decide_eq_true_eq]
  have hb := hc n n (fun p w => decide (G.Adj p w)) C hC4 hmon hfan hcomp'
  -- Two ordered pairs per edge, one per dart.
  have hpairs : G.edgeFinset.card ≤
      Fintype.card {e : Fin n × Fin n // decide (G.Adj e.1 e.2) = true} := by
    have hd : Fintype.card G.Dart =
        Fintype.card {e : Fin n × Fin n // decide (G.Adj e.1 e.2) = true} := by
      exact Fintype.card_congr
        { toFun := fun d => ⟨d.toProd, by simpa using d.adj⟩
          invFun := fun e => ⟨e.1, by simpa using e.2⟩
          left_inv := fun d => rfl
          right_inv := fun e => rfl }
    rw [← hd, G.dart_card_eq_twice_card_edges]
    omega
  have hs : C.gates.length + 1 ≤ (k + 1) * (D.size + 1) := by
    rw [Nat.succ_mul]
    omega
  calc G.edgeFinset.card
      ≤ c * (C.gates.length + 1) := hpairs.trans hb
    _ ≤ c * ((k + 1) * (D.size + 1)) := Nat.mul_le_mul_left c hs
    _ = c * (k + 1) * (D.size + 1) := (Nat.mul_assoc _ _ _).symm
