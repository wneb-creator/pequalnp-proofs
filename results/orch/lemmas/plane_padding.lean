import PEqualNP.Outside.L_meta_2583

namespace PEqualNP.Outside.L_meta_2583.Padding

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

def appendGate (n : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨op, [a, b]⟩], n + C.size⟩

lemma append_size (n : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ) :
    (appendGate n C op a b).size = C.size + 1 := by
  simp [appendGate, Circuit.size]

lemma append_model (n : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ)
    (hC : IsAO2 n C) (hop : op = GateOp.and ∨ op = GateOp.or)
    (ha : a < n + C.size) (hb : b < n + C.size) :
    IsAO2 n (appendGate n C op a b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [appendGate, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hC.1 g hg
    · exact hop
  · intro j hj i hi
    by_cases hjold : j < C.gates.length
    · have he : gateAt (appendGate n C op a b) j = gateAt C j := by
        simp [gateAt, appendGate, List.getD_eq_getElem?_getD,
          List.getElem?_append_left hjold]
      rw [he] at hi
      exact hC.2.1 j hjold i hi
    · have hjlast : j = C.gates.length := by
        simp only [appendGate, List.length_append, List.length_singleton] at hj
        omega
      subst j
      have he : gateAt (appendGate n C op a b) C.gates.length = ⟨op, [a, b]⟩ := by
        simp [gateAt, appendGate, List.getD_eq_getElem?_getD]
      rw [he] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact ha
      · exact hb
  · intro g hg
    simp only [appendGate, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hC.2.2 g hg
    · rfl

lemma append_eval (n : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ)
    (x : Fin n → Bool) :
    circuitFun n (appendGate n C op a b) x =
      op.eval [(C.wires (List.ofFn x)).getD a false,
        (C.wires (List.ofFn x)).getD b false] := by
  have hlen := ReadLower.General.s2230_wires_length n C x
  conv_lhs =>
    simp only [circuitFun, Circuit.eval, appendGate, Circuit.wires, List.foldl_append,
      List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil]
  change ((C.wires (List.ofFn x)) ++
    [op.eval [(C.wires (List.ofFn x)).getD a false,
      (C.wires (List.ofFn x)).getD b false]]).getD (n + C.size) false = _
  simp [Circuit.size, List.getD_eq_getElem?_getD, hlen]

lemma absorption_padding (n : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ)
    (hop : op = GateOp.and ∨ op = GateOp.or)
    (houtput : ∀ x : Fin n → Bool, circuitFun n C x =
      op.eval [(C.wires (List.ofFn x)).getD a false,
        (C.wires (List.ofFn x)).getD b false]) :
    ∀ x : Fin n → Bool,
      circuitFun n (appendGate n C op C.output a) x = circuitFun n C x := by
  intro x
  rw [append_eval]
  change op.eval [circuitFun n C x, (C.wires (List.ofFn x)).getD a false] = _
  rw [houtput]
  rcases hop with rfl | rfl <;>
    cases (C.wires (List.ofFn x)).getD a false <;>
    cases (C.wires (List.ofFn x)).getD b false <;>
    decide

end PEqualNP.Outside.L_meta_2583.Padding
