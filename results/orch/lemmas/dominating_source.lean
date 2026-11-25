import dominated_source_witness

namespace PEqualNP.Outside.L_meta_1886_aux.DominatingSource

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2592_aux
open Stronger.Extended

open ConstantSweep

lemma eliminate_consumed_dominating_not {n : ℕ} (F : (Fin n → Bool) → Bool)
    (pre suffix : List Gate) (source outIdx : ℕ)
    (hp : ∀ q ∈ pre, good q)
    (hs : Monotone2 (Circuit.mk suffix outIdx))
    (correct : ∀ x, (Circuit.mk (pre ++ ⟨.not,[source]⟩ :: suffix) outIdx).eval
      (List.ofFn x) = F x)
    (above : ∀ x, F x ≤ (run pre (List.ofFn x)).getD source false)
    (used : ∃ q ∈ suffix, n + pre.length ∈ q.inputs)
    (nonconstant : ∃ x y, F x ≠ F y) :
    ∃ (out : List Gate) (j : ℕ),
      FanInTwo (Circuit.mk (pre ++ out) j) ∧
      (Circuit.mk (pre ++ out) j).size + 2 ≤
        (Circuit.mk (pre ++ ⟨.not,[source]⟩ :: suffix) outIdx).size ∧
      ∀ x, (Circuit.mk (pre ++ out) j).eval (List.ofFn x) = F x := by
  have split : ∀ x, F x = (Circuit.mk suffix outIdx).eval
      (run pre (List.ofFn x) ++ [!((run pre (List.ofFn x)).getD source false)]) := by
    intro x
    have hc := (correct x).symm
    change F x = (run (pre ++ ⟨.not,[source]⟩ :: suffix) (List.ofFn x)).getD outIdx false at hc
    rw [run_append] at hc
    exact hc
  have hg : ∀ q ∈ suffix, good q := by
    intro q hq
    have h := hs q hq
    constructor
    · rcases h.1 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact h.2
  have constantCorrect : ∀ x, (Circuit.mk suffix outIdx).eval
      (run pre (List.ofFn x) ++ [false]) = F x :=
    OneNot.replace_not_from_above F (fun x => (run pre (List.ofFn x)).getD source false)
      (fun x => run pre (List.ofFn x)) (Circuit.mk suffix outIdx) hs split above
  obtain ⟨out,j,hout,hsize,hcorrect⟩ :=
    OneNotCompile.compile_constant_suffix F pre suffix outIdx false hg constantCorrect nonconstant
  refine ⟨out,j,?_,?_,hcorrect⟩
  · intro q hq
    exact (List.mem_append.mp hq).elim (hp q) (hout q)
  · have hcount := OneNotEliminate.touched_count hs used
    simp only [Circuit.size,List.length_append,List.length_cons]
    omega

lemma supplied_and_head (x : Fin 10 → Bool) :
    GateOp.and.eval ([0,1].map (fun i => (List.ofFn x).getD i false)) = (x 0 && x 1) := by
  simp [GateOp.eval]

lemma identity_lower (pre suffix : List Gate) (source outIdx : ℕ)
    (legal : FanInTwo (Circuit.mk (pre ++ ⟨.not,[source]⟩ :: suffix) outIdx))
    (mono : Monotone2 (Circuit.mk suffix outIdx))
    (used : ∃ q ∈ suffix, 11 + pre.length ∈ q.inputs)
    (above : ∀ x : Fin 10 → Bool,
      f10 x ≤ (Circuit.mk pre source).eval (List.ofFn x ++ [x 0 && x 1]))
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
  have physicalAbove : ∀ x : Fin 10 → Bool,
      f10 x ≤ (ConstantSweep.run (⟨.and,[0,1]⟩ :: pre) (List.ofFn x)).getD source false := by
    intro x
    change f10 x ≤ (ConstantSweep.run pre (List.ofFn x ++ [_])).getD source false
    rw [supplied_and_head]
    exact above x
  have nonconstant : ∃ x y : Fin 10 → Bool, f10 x ≠ f10 y := by
    exact ⟨fun _ => false,fun _ => true,by decide +kernel⟩
  have consumed : ∃ q ∈ suffix, 10 + (⟨GateOp.and,[0,1]⟩ :: pre).length ∈ q.inputs := by
    have h : 10 + (⟨GateOp.and,[0,1]⟩ :: pre).length = 11 + pre.length := by
      simp only [List.length_cons]
      omega
    rw [h]
    exact used
  obtain ⟨out,j,legalNew,saved,correctNew⟩ :=
    eliminate_consumed_dominating_not f10 (⟨.and,[0,1]⟩ :: pre)
      suffix source outIdx hp mono whole physicalAbove consumed nonconstant
  have lower := first_and_size_lower
    (Circuit.mk ((⟨.and,[0,1]⟩ :: pre) ++ out) j) 0 1 (by decide)
    ⟨pre ++ out,rfl⟩ legalNew correctNew
  simp only [Circuit.size,List.length_append,List.length_cons] at lower saved ⊢
  omega

lemma arbitrary_map_lower (p : Fin 10 → Fin 10) (pre suffix : List Gate) (source outIdx : ℕ)
    (legal : FanInTwo (Circuit.mk (pre ++ ⟨.not,[source]⟩ :: suffix) outIdx))
    (mono : Monotone2 (Circuit.mk suffix outIdx))
    (used : ∃ q ∈ suffix, 11 + pre.length ∈ q.inputs)
    (above : ∀ x : Fin 10 → Bool,
      f10 x ≤ (Circuit.mk pre source).eval (List.ofFn (x ∘ p) ++ [x 0 && x 1]))
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
  have aboveD : ∀ x : Fin 10 → Bool,
      f10 x ≤ (Circuit.mk (pre.map (InputRelabel.gate p)) (InputRelabel.wire p source)).eval
        (List.ofFn x ++ [x 0 && x 1]) := by
    intro x
    change _ ≤ (InputRelabel.circuit p (Circuit.mk pre source)).eval _
    rw [InputRelabel.circuit_eval]
    exact above x
  have correctD : ∀ x : Fin 10 → Bool, D.eval (List.ofFn x ++ [x 0 && x 1]) = f10 x := by
    intro x
    rw [← shape,InputRelabel.circuit_eval]
    exact correct x
  have lower := identity_lower (pre.map (InputRelabel.gate p))
    (suffix.map (InputRelabel.gate p)) (InputRelabel.wire p source)
    (InputRelabel.wire p outIdx) legalD monoD usedD aboveD correctD
  have sameSize : D.size = C.size := by rw [← shape,InputRelabel.circuit_size]
  change 19 ≤ D.size at lower
  rw [sameSize] at lower
  exact lower

end PEqualNP.Outside.L_meta_1886_aux.DominatingSource
