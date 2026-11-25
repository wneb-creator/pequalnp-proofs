import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def endpointCircuit (P Q : Circuit) (b : Bool) : Circuit :=
  ⟨P.gates ++ ⟨if b then GateOp.and else GateOp.or, []⟩ :: Q.gates, Q.output⟩

lemma endpointCircuit_size (P Q : Circuit) (b : Bool) :
    (endpointCircuit P Q b).size = P.size + Q.size + 1 := by
  simp only [endpointCircuit, Circuit.size, List.length_append, List.length_cons]
  omega

lemma endpointCircuit_eval (P Q : Circuit) (b : Bool) (x : List Bool) :
    (endpointCircuit P Q b).eval x = Q.eval (P.wires x ++ [b]) := by
  cases b <;>
    simp [endpointCircuit, Circuit.eval, Circuit.wires, List.foldl_append, GateOp.eval]

lemma endpointCircuit_monotone (P Q : Circuit) (b : Bool)
    (pMono : Monotone2 P) (qMono : Monotone2 Q) :
    Monotone2 (endpointCircuit P Q b) := by
  intro g hg
  change g ∈ P.gates ++ ⟨if b then GateOp.and else GateOp.or, []⟩ :: Q.gates at hg
  rcases List.mem_append.mp hg with hp | hq
  · exact pMono g hp
  · rcases List.mem_cons.mp hq with hg | hg
    · subst g
      cases b <;> simp
    · exact qMono g hg

lemma endpointCircuit_fanInTwo (P Q : Circuit) (b : Bool)
    (pFan : FanInTwo P) (qFan : FanInTwo Q) :
    FanInTwo (endpointCircuit P Q b) := by
  intro g hg
  change g ∈ P.gates ++ ⟨if b then GateOp.and else GateOp.or, []⟩ :: Q.gates at hg
  rcases List.mem_append.mp hg with hp | hq
  · exact pFan g hp
  · rcases List.mem_cons.mp hq with hg | hg
    · subst g
      cases b <;> simp
    · exact qFan g hg

lemma endpointCircuit_notCount (P Q : Circuit) (b : Bool) :
    PEqualNP.NotBracket.notCount (endpointCircuit P Q b) =
      PEqualNP.NotBracket.notCount P + PEqualNP.NotBracket.notCount Q := by
  cases b <;> simp [endpointCircuit, PEqualNP.NotBracket.notCount]

lemma endpointCircuit_computes {n : ℕ}
    (P Q : Circuit) (b : Bool) (f : (Fin n → Bool) → Bool)
    (correct : ∀ x, Q.eval (P.wires (List.ofFn x) ++ [b]) = f x) :
    ∀ x, (endpointCircuit P Q b).eval (List.ofFn x) = f x := by
  intro x
  rw [endpointCircuit_eval]
  exact correct x

end PEqualNP.Outside.L_meta_2592_aux
