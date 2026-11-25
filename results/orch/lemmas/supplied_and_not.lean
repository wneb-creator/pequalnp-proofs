import one_not_petersen

namespace PEqualNP.Outside.L_meta_1886_aux.SuppliedAnd

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2592_aux

lemma consumed_seed_not_lower (pre suffix : List Gate) (outIdx : Nat)
    (legal : FanInTwo (Circuit.mk (pre ++ ⟨.not,[10]⟩ :: suffix) outIdx))
    (mono : Monotone2 (Circuit.mk suffix outIdx))
    (used : ∃ q ∈ suffix, 11 + pre.length ∈ q.inputs)
    (correct : ∀ x : Fin 10 → Bool,
      (Circuit.mk (pre ++ ⟨.not,[10]⟩ :: suffix) outIdx).eval
        (List.ofFn x ++ [x 0 && x 1]) = Stronger.Extended.f10 x) :
    19 ≤ (Circuit.mk (pre ++ ⟨.not,[10]⟩ :: suffix) outIdx).size := by
  have hp : ∀ q ∈ (⟨GateOp.and,[0,1]⟩ :: pre), ConstantSweep.good q := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · simp [ConstantSweep.good]
    · exact legal q (List.mem_append_left _ hq)
  have whole : ∀ x : Fin 10 → Bool,
      (Circuit.mk ((⟨.and,[0,1]⟩ :: pre) ++ ⟨.not,[10]⟩ :: suffix) outIdx).eval
        (List.ofFn x) = Stronger.Extended.f10 x := by
    intro x
    have head : GateOp.and.eval ([0,1].map (fun i => (List.ofFn x).getD i false)) =
        (x 0 && x 1) := by
      simp [GateOp.eval]
    simpa only [Circuit.eval,Circuit.wires,List.cons_append,List.foldl_cons,head] using correct x
  have lower := OneNotPetersen.first_adjacent_and_not_lower 0 1 (by decide)
    (OneNotPetersen.adjacent_implies 0 1 (by decide +kernel)) pre suffix outIdx hp mono whole used
  simp only [Circuit.size,List.length_append,List.length_cons] at lower ⊢
  omega

lemma consumed_seed_not_exclusion (pre suffix : List Gate) (outIdx : Nat)
    (legal : FanInTwo (Circuit.mk (pre ++ ⟨.not,[10]⟩ :: suffix) outIdx))
    (mono : Monotone2 (Circuit.mk suffix outIdx))
    (used : ∃ q ∈ suffix, 11 + pre.length ∈ q.inputs)
    (budget : (Circuit.mk (pre ++ ⟨.not,[10]⟩ :: suffix) outIdx).size ≤ 18) :
    ∃ x : Fin 10 → Bool,
      (Circuit.mk (pre ++ ⟨.not,[10]⟩ :: suffix) outIdx).eval
        (List.ofFn x ++ [x 0 && x 1]) ≠ Stronger.Extended.f10 x := by
  by_contra! correct
  have lower := consumed_seed_not_lower pre suffix outIdx legal mono used correct
  omega

end PEqualNP.Outside.L_meta_1886_aux.SuppliedAnd
