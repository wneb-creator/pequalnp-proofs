import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3451

lemma decMinCover (n : ℕ) (G : SimpleGraph (Fin n)) :
    ∃ T : Finset (Fin n),
      (∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T) ∧
      ∀ T' : Finset (Fin n), (∀ i j, G.Adj i j → i ∈ T' ∨ j ∈ T') → T.card ≤ T'.card := by
  classical
  let P : ℕ → Prop := fun k => ∃ T : Finset (Fin n),
    (∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T) ∧ T.card = k
  have hex : ∃ k, P k := ⟨n, Finset.univ, by simp, by simp⟩
  obtain ⟨T, hT, hcard⟩ := Nat.find_spec hex
  refine ⟨T, hT, ?_⟩
  intro T' hT'
  rw [hcard]
  exact Nat.find_min' hex ⟨T', hT', rfl⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

lemma decForestBridge (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : Monotone2 C)
    (hfun : circuitFun n C =
      (fun x : Fin n → Bool => decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)))
    (hupper : ∀ T : Finset (Fin n), (∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T) →
      ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧
        circuitFun n D =
          (fun x : Fin n → Bool => decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)) ∧
        D.size + 1 ≤ G.edgeFinset.card + T.card ∧
        (∀ j < D.gates.length, (gateAt D j).op = GateOp.and → ∀ x : Fin n → Bool,
          (D.wires (List.ofFn x)).getD (n + j) false = true →
          ∃ i k, G.Adj i k ∧ x i = true ∧ x k = true))
    (hlower : ∀ k s : ℕ,
      (∀ T : Finset (Fin n), (∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T) → k ≤ T.card) →
      HasCircuitSize n
        (fun x : Fin n → Bool => decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)) s →
      G.edgeFinset.card + k ≤ s + 1) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ D.size ≤ C.size ∧
      circuitFun n D =
        (fun x : Fin n → Bool => decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)) ∧
      (∀ j < D.gates.length, (gateAt D j).op = GateOp.and → ∀ x : Fin n → Bool,
        (D.wires (List.ofFn x)).getD (n + j) false = true →
        ∃ i k, G.Adj i k ∧ x i = true ∧ x k = true) := by
  obtain ⟨T, hT, hmin⟩ := decMinCover n G
  have hfan : FanInTwo C := by
    intro g hg
    obtain ⟨hop, hs⟩ := hC g hg
    refine ⟨?_, hs⟩
    rcases hop with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have hsmall : HasCircuitSize n
      (fun x : Fin n → Bool => decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true))
      C.size := ⟨C, hfan, le_rfl, fun x => congrFun hfun x⟩
  have hlo := hlower T.card C.size hmin hsmall
  obtain ⟨D, hm, hr, hf, hs, ha⟩ := hupper T hT
  exact ⟨D, hm, hr, by omega, hf, ha⟩

lemma decIncidenceFinish (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (G : SimpleGraph (Fin (N + N))) [DecidableRel G.Adj]
    (hgraph : ∀ z : Fin (N + N) → Bool,
      (∃ i j, G.Adj i j ∧ z i = true ∧ z j = true) ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (C : Circuit)
    (hclean : ∃ D : Circuit, Monotone2 D ∧ ReadsBack (N + N) D ∧ D.size ≤ C.size ∧
      circuitFun (N + N) D =
        (fun x : Fin (N + N) → Bool => decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)) ∧
      (∀ j < D.gates.length, (gateAt D j).op = GateOp.and → ∀ x : Fin (N + N) → Bool,
        (D.wires (List.ofFn x)).getD (N + N + j) false = true →
        ∃ i k, G.Adj i k ∧ x i = true ∧ x k = true)) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack (N + N) D ∧ D.size ≤ C.size ∧
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z = true ↔
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
      (∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
        ∀ p l : Fin N, ¬ I p l →
        (D.wires (List.ofFn (fun k : Fin (N + N) =>
          decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)))).getD (N + N + j) false = false) ∧
      (∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
        (∀ p : Fin N, (D.wires (List.ofFn (fun k : Fin (N + N) =>
          decide (k = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧
        ∀ l : Fin N, (D.wires (List.ofFn (fun k : Fin (N + N) =>
          decide (k = Fin.natAdd N l)))).getD (N + N + j) false = false) := by
  obtain ⟨D, hm, hr, hs, hf, ha⟩ := hclean
  refine ⟨D, hm, hr, hs, ?_, ?_, ?_⟩
  · intro z
    rw [hf, decide_eq_true_iff]
    exact hgraph z
  · intro j hj hand p0 l0 hnon
    apply Bool.eq_false_iff.mpr
    intro ht
    obtain ⟨p, l, hil, hp, hl⟩ := (hgraph _).mp (ha j hj hand _ ht)
    have hpp : p = p0 := by
      rcases of_decide_eq_true hp with h | h
      · apply Fin.ext
        exact congrArg (fun k : Fin (N + N) => k.val) h
      · have hh := congrArg (fun k : Fin (N + N) => k.val) h
        change p.val = N + l0.val at hh
        omega
    have hll : l = l0 := by
      rcases of_decide_eq_true hl with h | h
      · have hh := congrArg (fun k : Fin (N + N) => k.val) h
        change N + l.val = p0.val at hh
        omega
      · apply Fin.ext
        have hh := congrArg (fun k : Fin (N + N) => k.val) h
        change N + l.val = N + l0.val at hh
        omega
    exact hnon (hpp ▸ hll ▸ hil)
  · intro j hj hand
    constructor
    · intro p0
      apply Bool.eq_false_iff.mpr
      intro ht
      obtain ⟨p, l, _, _, hl⟩ := (hgraph _).mp (ha j hj hand _ ht)
      have hh := congrArg (fun k : Fin (N + N) => k.val) (of_decide_eq_true hl)
      change N + l.val = p0.val at hh
      omega
    · intro l0
      apply Bool.eq_false_iff.mpr
      intro ht
      obtain ⟨p, l, _, hp, _⟩ := (hgraph _).mp (ha j hj hand _ ht)
      have hh := congrArg (fun k : Fin (N + N) => k.val) (of_decide_eq_true hp)
      change p.val = N + l0.val at hh
      omega

end PEqualNP.Outside.L_meta_3451
