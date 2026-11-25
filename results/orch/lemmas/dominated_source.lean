import seed_not_operands

namespace PEqualNP.Outside.L_meta_1886_aux.DominatedSource

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2592_aux
open Stronger.Extended

lemma supplied_and_head (x : Fin 10 → Bool) :
    GateOp.and.eval ([0,1].map (fun i => (List.ofFn x).getD i false)) = (x 0 && x 1) := by
  simp [GateOp.eval]

lemma identity_lower (pre suffix : List Gate) (source outIdx : ℕ)
    (legal : FanInTwo (Circuit.mk (pre ++ ⟨.not,[source]⟩ :: suffix) outIdx))
    (mono : Monotone2 (Circuit.mk suffix outIdx))
    (used : ∃ q ∈ suffix, 11 + pre.length ∈ q.inputs)
    (below : ∀ x : Fin 10 → Bool,
      (Circuit.mk pre source).eval (List.ofFn x ++ [x 0 && x 1]) ≤ f10 x)
    (correct : ∀ x : Fin 10 → Bool,
      (Circuit.mk (pre ++ ⟨.not,[source]⟩ :: suffix) outIdx).eval
        (List.ofFn x ++ [x 0 && x 1]) = f10 x) :
    19 ≤ (Circuit.mk (pre ++ ⟨.not,[source]⟩ :: suffix) outIdx).size := by
  have hp : ∀ q ∈ (⟨GateOp.and,[0,1]⟩ :: pre), ConstantSweep.good q := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · simp [ConstantSweep.good]
    · exact legal q (List.mem_append_left _ hq)
  have whole : ∀ x : Fin 10 → Bool,
      (Circuit.mk ((⟨.and,[0,1]⟩ :: pre) ++ ⟨.not,[source]⟩ :: suffix) outIdx).eval
        (List.ofFn x) = f10 x := by
    intro x
    simpa only [Circuit.eval,Circuit.wires,List.cons_append,List.foldl_cons,supplied_and_head]
      using correct x
  have physicalBelow : ∀ x : Fin 10 → Bool,
      (ConstantSweep.run (⟨.and,[0,1]⟩ :: pre) (List.ofFn x)).getD source false ≤ f10 x := by
    intro x
    change (ConstantSweep.run pre (List.ofFn x ++ [_])).getD source false ≤ f10 x
    rw [supplied_and_head]
    exact below x
  have nonconstant : ∃ x y : Fin 10 → Bool, f10 x ≠ f10 y := by
    exact ⟨fun _ => false,fun _ => true,by decide +kernel⟩
  have consumed : ∃ q ∈ suffix, 10 + (⟨GateOp.and,[0,1]⟩ :: pre).length ∈ q.inputs := by
    have h : 10 + (⟨GateOp.and,[0,1]⟩ :: pre).length = 11 + pre.length := by
      simp only [List.length_cons]
      omega
    rw [h]
    exact used
  obtain ⟨out,j,legalNew,saved,correctNew⟩ :=
    OneNotEliminate.eliminate_consumed_dominated_not f10 (⟨.and,[0,1]⟩ :: pre)
      suffix source outIdx hp mono whole physicalBelow consumed nonconstant
  have lower := first_and_size_lower
    (Circuit.mk ((⟨.and,[0,1]⟩ :: pre) ++ out) j) 0 1 (by decide)
    ⟨pre ++ out,rfl⟩ legalNew correctNew
  simp only [Circuit.size,List.length_append,List.length_cons] at lower saved ⊢
  omega

lemma arbitrary_map_lower (p : Fin 10 → Fin 10) (pre suffix : List Gate) (source outIdx : ℕ)
    (legal : FanInTwo (Circuit.mk (pre ++ ⟨.not,[source]⟩ :: suffix) outIdx))
    (mono : Monotone2 (Circuit.mk suffix outIdx))
    (used : ∃ q ∈ suffix, 11 + pre.length ∈ q.inputs)
    (below : ∀ x : Fin 10 → Bool,
      (Circuit.mk pre source).eval (List.ofFn (x ∘ p) ++ [x 0 && x 1]) ≤ f10 x)
    (correct : ∀ x : Fin 10 → Bool,
      (Circuit.mk (pre ++ ⟨.not,[source]⟩ :: suffix) outIdx).eval
        (List.ofFn (x ∘ p) ++ [x 0 && x 1]) = f10 x) :
    19 ≤ (Circuit.mk (pre ++ ⟨.not,[source]⟩ :: suffix) outIdx).size := by
  let C := Circuit.mk (pre ++ ⟨GateOp.not,[source]⟩ :: suffix) outIdx
  let D := Circuit.mk (pre.map (InputRelabel.gate p) ++
    ⟨GateOp.not,[InputRelabel.wire p source]⟩ :: suffix.map (InputRelabel.gate p))
    (InputRelabel.wire p outIdx)
  have shape : InputRelabel.circuit p C = D := by
    simp [InputRelabel.circuit,C,D,InputRelabel.gate]
  have legalD : FanInTwo D := by
    rw [← shape]
    exact InputRelabel.circuit_legal p C legal
  have monoD : Monotone2 (Circuit.mk (suffix.map (InputRelabel.gate p))
      (InputRelabel.wire p outIdx)) :=
    InputRelabel.circuit_mono p (Circuit.mk suffix outIdx) mono
  have usedD : ∃ q ∈ suffix.map (InputRelabel.gate p),
      11 + (pre.map (InputRelabel.gate p)).length ∈ q.inputs := by
    obtain ⟨q,hq,hi⟩ := used
    refine ⟨InputRelabel.gate p q,List.mem_map.mpr ⟨q,hq,rfl⟩,?_⟩
    change 11 + (pre.map (InputRelabel.gate p)).length ∈ q.inputs.map (InputRelabel.wire p)
    rw [List.length_map]
    exact List.mem_map.mpr ⟨11 + pre.length,hi,InputRelabel.wire_fixed p _ (by omega)⟩
  have belowD : ∀ x : Fin 10 → Bool,
      (Circuit.mk (pre.map (InputRelabel.gate p)) (InputRelabel.wire p source)).eval
        (List.ofFn x ++ [x 0 && x 1]) ≤ f10 x := by
    intro x
    change (InputRelabel.circuit p (Circuit.mk pre source)).eval _ ≤ _
    rw [InputRelabel.circuit_eval]
    exact below x
  have correctD : ∀ x : Fin 10 → Bool, D.eval (List.ofFn x ++ [x 0 && x 1]) = f10 x := by
    intro x
    rw [← shape,InputRelabel.circuit_eval]
    exact correct x
  have lower := identity_lower (pre.map (InputRelabel.gate p))
    (suffix.map (InputRelabel.gate p)) (InputRelabel.wire p source)
    (InputRelabel.wire p outIdx) legalD monoD usedD belowD correctD
  have sameSize : D.size = C.size := by rw [← shape,InputRelabel.circuit_size]
  change 19 ≤ D.size at lower
  rw [sameSize] at lower
  exact lower

end PEqualNP.Outside.L_meta_1886_aux.DominatedSource
