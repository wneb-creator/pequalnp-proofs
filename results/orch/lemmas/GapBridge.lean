import PEqualNP.Outside.L_meta_2373

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PEqualNP.Outside.L_meta_2373

def glued (g : Gate) (C : Circuit) (u v : Nat) : Circuit :=
  ⟨g :: (C.gates ++ [⟨GateOp.or, [u, v]⟩]), 11 + C.size⟩

lemma wires_length (C : Circuit) (xs : List Bool) :
    (C.wires xs).length = xs.length + C.size := by
  rcases C with ⟨gs, out⟩
  induction gs generalizing xs with
  | nil => simp [Circuit.wires, Circuit.size]
  | cons g gs ih =>
    change (Circuit.wires ⟨gs, out⟩
      (xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)])).length = _
    rw [ih]
    simp [Circuit.size]
    omega

lemma glued_fan (g : Gate) (C : Circuit) (u v : Nat)
    (hg : FanInTwo ⟨[g], 0⟩) (hC : FanInTwo C) : FanInTwo (glued g C u v) := by
  intro gate hgate
  have hfirst := hg g (by simp)
  simp only [glued, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hgate
  rcases hgate with rfl | hgate | rfl
  · exact hfirst
  · exact hC gate hgate
  · simp

lemma glued_size (g : Gate) (C : Circuit) (u v : Nat) :
    (glued g C u v).size = C.size + 2 := by
  simp [glued, Circuit.size]

lemma glued_eval (g : Gate) (C : Circuit) (u v : Nat) (x : Fin 10 → Bool) :
    (glued g C u v).eval (List.ofFn x) =
      ((C.wires ((⟨[g], 0⟩ : Circuit).wires (List.ofFn x))).getD u false ||
        (C.wires ((⟨[g], 0⟩ : Circuit).wires (List.ofFn x))).getD v false) := by
  let w := C.wires ((⟨[g], 0⟩ : Circuit).wires (List.ofFn x))
  have hw : w.length = 11 + C.size := by
    simp [w, wires_length, Circuit.size]
  simp only [glued, Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_append,
    List.foldl_nil, List.map_cons, List.map_nil, GateOp.eval, List.any_cons,
    List.any_nil, id_eq, Bool.or_false]
  change (w ++ [(w.getD u false || w.getD v false)]).getD (11 + C.size) false = _
  rw [← hw]
  simp [w, Circuit.wires, GateOp.eval]

lemma cover_gives_circuit (g : Gate) (C : Circuit) (u v : Nat)
    (hg : FanInTwo ⟨[g], 0⟩) (hC : FanInTwo C) (hs : C.size ≤ 17)
    (cover : ∀ x : Fin 10 → Bool, edge x =
      ((C.wires ((⟨[g], 0⟩ : Circuit).wires (List.ofFn x))).getD u false ||
       (C.wires ((⟨[g], 0⟩ : Circuit).wires (List.ofFn x))).getD v false)) :
    HasCircuitSize 10 edge 19 := by
  refine ⟨glued g C u v, glued_fan g C u v hg hC, ?_, ?_⟩
  · rw [glued_size]
    omega
  · intro x
    rw [glued_eval, ← cover x]

lemma missed_of_no_circuit (g : Gate) (C : Circuit) (u v : Nat)
    (hg : FanInTwo ⟨[g], 0⟩) (hC : FanInTwo C) (hs : C.size ≤ 17)
    (lower : ¬ HasCircuitSize 10 edge 19)
    (sound : ∀ x : Fin 10 → Bool, edge x = false →
      (C.wires ((⟨[g], 0⟩ : Circuit).wires (List.ofFn x))).getD u false = false ∧
      (C.wires ((⟨[g], 0⟩ : Circuit).wires (List.ofFn x))).getD v false = false) :
    ∃ x : Fin 10 → Bool, edge x = true ∧
      (C.wires ((⟨[g], 0⟩ : Circuit).wires (List.ofFn x))).getD u false = false ∧
      (C.wires ((⟨[g], 0⟩ : Circuit).wires (List.ofFn x))).getD v false = false := by
  classical
  by_contra missing
  apply lower
  apply cover_gives_circuit g C u v hg hC hs
  intro x
  have hx := sound x
  have hm : ¬ (edge x = true ∧
      (C.wires ((⟨[g], 0⟩ : Circuit).wires (List.ofFn x))).getD u false = false ∧
      (C.wires ((⟨[g], 0⟩ : Circuit).wires (List.ofFn x))).getD v false = false) :=
    fun h => missing ⟨x, h⟩
  cases he : edge x <;>
    cases hu : (C.wires ((⟨[g], 0⟩ : Circuit).wires (List.ofFn x))).getD u false <;>
    cases hv : (C.wires ((⟨[g], 0⟩ : Circuit).wires (List.ofFn x))).getD v false <;>
    simp_all

lemma missed_or_few_nots (g : Gate) (C : Circuit) (u v : Nat)
    (hg : FanInTwo ⟨[g], 0⟩) (hC : FanInTwo C) (hs : C.size ≤ 17)
    (sound : ∀ x : Fin 10 → Bool, edge x = false →
      (C.wires ((⟨[g], 0⟩ : Circuit).wires (List.ofFn x))).getD u false = false ∧
      (C.wires ((⟨[g], 0⟩ : Circuit).wires (List.ofFn x))).getD v false = false) :
    (∃ x : Fin 10 → Bool, edge x = true ∧
      (C.wires ((⟨[g], 0⟩ : Circuit).wires (List.ofFn x))).getD u false = false ∧
      (C.wires ((⟨[g], 0⟩ : Circuit).wires (List.ofFn x))).getD v false = false) ∨
      PEqualNP.NotBracket.notCount (glued g C u v) ≤ 2 := by
  classical
  by_cases missing : ∃ x : Fin 10 → Bool, edge x = true ∧
      (C.wires ((⟨[g], 0⟩ : Circuit).wires (List.ofFn x))).getD u false = false ∧
      (C.wires ((⟨[g], 0⟩ : Circuit).wires (List.ofFn x))).getD v false = false
  · exact Or.inl missing
  apply Or.inr
  have cover : ∀ x : Fin 10 → Bool, edge x =
      ((C.wires ((⟨[g], 0⟩ : Circuit).wires (List.ofFn x))).getD u false ||
       (C.wires ((⟨[g], 0⟩ : Circuit).wires (List.ofFn x))).getD v false) := by
    intro x
    have hx := sound x
    have hm : ¬ (edge x = true ∧
        (C.wires ((⟨[g], 0⟩ : Circuit).wires (List.ofFn x))).getD u false = false ∧
        (C.wires ((⟨[g], 0⟩ : Circuit).wires (List.ofFn x))).getD v false = false) :=
      fun h => missing ⟨x, h⟩
    cases he : edge x <;>
      cases hu : (C.wires ((⟨[g], 0⟩ : Circuit).wires (List.ofFn x))).getD u false <;>
      cases hv : (C.wires ((⟨[g], 0⟩ : Circuit).wires (List.ofFn x))).getD v false <;>
      simp_all
  have bound := petersen_not_budget_seventeen (glued g C u v)
    (glued_fan g C u v hg hC) (by
      intro x
      rw [glued_eval, ← cover x])
  have size := glued_size g C u v
  omega

end PEqualNP.Outside.L_meta_2373
