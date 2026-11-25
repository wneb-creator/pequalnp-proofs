import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1772_aux.badStarObstruction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

abbrev G : SimpleGraph (Fin 4) := edgeGraph 4 [(0,1),(0,2),(1,3)]

def C : Circuit :=
  ⟨[⟨GateOp.or,[0,3]⟩,⟨GateOp.or,[1,2]⟩,⟨GateOp.and,[4,5]⟩,
    ⟨GateOp.and,[0,6]⟩,⟨GateOp.and,[3,1]⟩,⟨GateOp.or,[7,8]⟩],9⟩

def D : Circuit :=
  ⟨[⟨GateOp.or,[1,2]⟩,⟨GateOp.and,[0,4]⟩,⟨GateOp.and,[3,1]⟩,
    ⟨GateOp.or,[5,6]⟩],7⟩

lemma girth :
    (∀ a b c : Fin 4, G.Adj a b → G.Adj b c → ¬G.Adj c a) ∧ NoFourCycle G := by
  decide +kernel

lemma mono : Monotone2 C := by simp [Monotone2,C]

lemma correct : circuitFun 4 C = graphFun G ∅ := by
  funext x
  revert x
  decide +kernel

lemma top_form : TopForm G C := by
  decide +kernel

lemma earlier_and_owns : ∀ j<3, (gateAt C j).op=GateOp.and →
    ∃ u v : Fin 4, G.Adj u v ∧ Owns 4 C j u v := by
  intro j hj hand
  interval_cases j
  · cases hand
  · cases hand
  · exact ⟨0,1,by decide +kernel,by decide +kernel⟩

lemma bad_star :
    (∀ u v : Fin 4, G.Adj u v → ¬Owns 4 C 3 u v) ∧
    (∀ u v : Fin 4, G.Adj u v → gateVal 4 C 3 (pairInput u v)=true → u=0 ∨ v=0) ∧
    gateVal 4 C 3 (pairInput 0 1)=true ∧ gateVal 4 C 3 (pairInput 0 2)=true := by
  decide +kernel

lemma dirty_ancestor : PEqualNP.CleanedNonEdge.IsDirtyAnd 4 G C 2 := by
  decide +kernel

lemma smaller : Monotone2 D ∧ circuitFun 4 D=graphFun G ∅ ∧ D.size<C.size := by
  refine ⟨by simp [Monotone2,D],?_,by decide +kernel⟩
  funext x
  revert x
  decide +kernel

lemma not_minimal : ¬IsMinimalMonoCircuit 4 C := by
  intro h
  have hbound := h.2 D smaller.1 (smaller.2.1.trans correct.symm)
  exact (Nat.not_le_of_lt smaller.2.2) hbound

end PEqualNP.Outside.L_meta_1772_aux.badStarObstruction
