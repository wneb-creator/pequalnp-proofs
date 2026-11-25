import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma split_last_not (gs : List Gate)
    (h : ∃ g ∈ gs, g.op = GateOp.not) :
    ∃ (pre : List Gate) (g : Gate) (suf : List Gate),
      gs = pre ++ g :: suf ∧ g.op = GateOp.not ∧
        ∀ t ∈ suf, t.op ≠ GateOp.not := by
  classical
  induction gs with
  | nil => simp at h
  | cons a tail ih =>
    by_cases ht : ∃ g ∈ tail, g.op = GateOp.not
    · obtain ⟨pre, g, suf, he, hn, hs⟩ := ih ht
      exact ⟨a :: pre, g, suf, by simp [he], hn, hs⟩
    · have ha : a.op = GateOp.not := by
        obtain ⟨g, hg, hn⟩ := h
        rcases List.mem_cons.mp hg with hg | hg
        · simpa [hg] using hn
        · exact (ht ⟨g, hg, hn⟩).elim
      exact ⟨[], a, tail, rfl, ha, fun t mem hn => ht ⟨t, mem, hn⟩⟩

lemma wires_length (gs : List Gate) (o : ℕ) (x : List Bool) :
    (Circuit.wires ⟨gs, o⟩ x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [Circuit.wires]
  | cons g tail ih =>
    change (Circuit.wires ⟨tail, o⟩ (x ++ [_])).length = _
    rw [ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

lemma last_not_factorization (n : ℕ) (C : Circuit) (fan : FanInTwo C)
    (hasNot : ∃ g ∈ C.gates, g.op = GateOp.not) :
    ∃ P Q : Circuit, FanInTwo P ∧ Monotone2 Q ∧ P.size + Q.size + 1 = C.size ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
        Q.eval (P.wires (List.ofFn x) ++ [!P.eval (List.ofFn x)]) := by
  obtain ⟨pre, g, suf, split, gn, rest⟩ := split_last_not C.gates hasNot
  let P : Circuit := ⟨pre, g.inputs.headD (n + pre.length)⟩
  let Q : Circuit := ⟨suf, C.output⟩
  refine ⟨P, Q, ?_, ?_, ?_, ?_⟩
  · intro t ht
    apply fan t
    rw [split]
    exact List.mem_append_left _ ht
  · intro t ht
    have hm : t ∈ C.gates := by
      rw [split]
      exact List.mem_append_right _ (List.mem_cons_of_mem _ ht)
    obtain ⟨hop, hlen⟩ := fan t hm
    refine ⟨?_, hlen⟩
    change t.op = GateOp.and ∨ t.op = GateOp.or
    change t.op = GateOp.and ∨ t.op = GateOp.or ∨ t.op = GateOp.not at hop
    rcases hop with hop | hop | hop
    · exact Or.inl hop
    · exact Or.inr hop
    · exact (rest t ht hop).elim
  · simp only [P, Q, Circuit.size, split, List.length_append, List.length_cons]
    omega
  · intro x
    have gateValue :
        g.op.eval (g.inputs.map fun i => (P.wires (List.ofFn x)).getD i false) =
          !P.eval (List.ofFn x) := by
      rw [gn]
      cases hi : g.inputs with
      | nil =>
        have hlen : (P.wires (List.ofFn x)).length = n + pre.length := by
          simpa [P] using wires_length pre P.output (List.ofFn x)
        have hm : (P.wires (List.ofFn x)).getD (n + pre.length) false = false :=
          List.getD_eq_default _ _ (by omega)
        have hout : P.output = n + pre.length := by simp [P, hi]
        change true = !(P.wires (List.ofFn x)).getD P.output false
        rw [hout, hm]
        rfl
      | cons i tail =>
        have hout : P.output = i := by simp [P, hi]
        change Bool.not ((P.wires (List.ofFn x)).getD i false) =
          Bool.not ((P.wires (List.ofFn x)).getD P.output false)
        rw [hout]
    change (C.gates.foldl _ (List.ofFn x)).getD C.output false = _
    rw [split, List.foldl_append]
    change (suf.foldl _ (P.wires (List.ofFn x) ++
      [g.op.eval (g.inputs.map fun i => (P.wires (List.ofFn x)).getD i false)])).getD
      C.output false = _
    rw [gateValue]
    rfl

end PEqualNP.Outside.L_meta_2592_aux
