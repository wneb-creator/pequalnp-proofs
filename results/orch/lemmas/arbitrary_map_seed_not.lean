import supplied_and_not
import input_relabel

namespace PEqualNP.Outside.L_meta_1886_aux.ArbitraryMapSeedNot

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2592_aux.Stronger.Extended
open InputRelabel

lemma consumed_seed_not_lower (p : Fin 10 → Fin 10) (pre suffix : List Gate) (outIdx : ℕ)
    (legal : FanInTwo (Circuit.mk (pre ++ ⟨.not,[10]⟩ :: suffix) outIdx))
    (mono : Monotone2 (Circuit.mk suffix outIdx))
    (used : ∃ q ∈ suffix, 11 + pre.length ∈ q.inputs)
    (correct : ∀ x : Fin 10 → Bool,
      (Circuit.mk (pre ++ ⟨.not,[10]⟩ :: suffix) outIdx).eval
        (List.ofFn (x ∘ p) ++ [x 0 && x 1]) = f10 x) :
    19 ≤ (Circuit.mk (pre ++ ⟨.not,[10]⟩ :: suffix) outIdx).size := by
  let C := Circuit.mk (pre ++ ⟨GateOp.not,[10]⟩ :: suffix) outIdx
  let D := Circuit.mk (pre.map (gate p) ++ ⟨GateOp.not,[10]⟩ :: suffix.map (gate p))
    (wire p outIdx)
  have shape : circuit p C = D := by
    simp [circuit,C,D,gate,wire]
  have legalD : FanInTwo D := by
    rw [← shape]
    exact circuit_legal p C legal
  have monoD : Monotone2 (Circuit.mk (suffix.map (gate p)) (wire p outIdx)) :=
    circuit_mono p (Circuit.mk suffix outIdx) mono
  have usedD : ∃ q ∈ suffix.map (gate p), 11 + (pre.map (gate p)).length ∈ q.inputs := by
    obtain ⟨q,hq,hi⟩ := used
    refine ⟨gate p q,List.mem_map.mpr ⟨q,hq,rfl⟩,?_⟩
    change 11 + (pre.map (gate p)).length ∈ q.inputs.map (wire p)
    rw [List.length_map]
    exact List.mem_map.mpr ⟨11 + pre.length,hi,wire_fixed p _ (by omega)⟩
  have correctD : ∀ x : Fin 10 → Bool, D.eval (List.ofFn x ++ [x 0 && x 1]) = f10 x := by
    intro x
    rw [← shape,circuit_eval]
    exact correct x
  have lower := SuppliedAnd.consumed_seed_not_lower (pre.map (gate p))
    (suffix.map (gate p)) (wire p outIdx) legalD monoD usedD correctD
  have sameSize : D.size = C.size := by rw [← shape,circuit_size]
  change 19 ≤ D.size at lower
  rw [sameSize] at lower
  exact lower

lemma consumed_seed_not_exclusion (p : Fin 10 → Fin 10) (pre suffix : List Gate) (outIdx : ℕ)
    (legal : FanInTwo (Circuit.mk (pre ++ ⟨.not,[10]⟩ :: suffix) outIdx))
    (mono : Monotone2 (Circuit.mk suffix outIdx))
    (used : ∃ q ∈ suffix, 11 + pre.length ∈ q.inputs)
    (budget : (Circuit.mk (pre ++ ⟨.not,[10]⟩ :: suffix) outIdx).size ≤ 18) :
    ∃ x : Fin 10 → Bool,
      (Circuit.mk (pre ++ ⟨.not,[10]⟩ :: suffix) outIdx).eval
        (List.ofFn (x ∘ p) ++ [x 0 && x 1]) ≠ f10 x := by
  by_contra! correct
  have lower := consumed_seed_not_lower p pre suffix outIdx legal mono used correct
  omega

end PEqualNP.Outside.L_meta_1886_aux.ArbitraryMapSeedNot
