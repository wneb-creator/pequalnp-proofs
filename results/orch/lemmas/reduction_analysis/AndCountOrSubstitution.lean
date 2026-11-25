import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_650_aux.AndCountOrSubstitution

open PEqualNP.AndCount

def encode {n m : ℕ} (support : Fin n → Finset (Fin m))
    (U : Finset (Fin m)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => ∃ v ∈ support i, v ∈ U)

def substitute {n m : ℕ} (C : AndCountCircuit n)
    (support : Fin n → Finset (Fin m)) : AndCountCircuit m where
  size := C.size
  leftVars i := (C.leftVars i).biUnion support
  leftGates := C.leftGates
  rightVars i := (C.rightVars i).biUnion support
  rightGates := C.rightGates
  outVars := C.outVars.biUnion support
  outGates := C.outGates

lemma size_eq {n m : ℕ} (C : AndCountCircuit n)
    (support : Fin n → Finset (Fin m)) : (substitute C support).size = C.size := rfl

lemma wellFormed_iff {n m : ℕ} (C : AndCountCircuit n)
    (support : Fin n → Finset (Fin m)) :
    (substitute C support).WellFormed ↔ C.WellFormed := Iff.rfl

lemma support_hit {n m : ℕ} (support : Fin n → Finset (Fin m))
    (B : Finset (Fin n)) (U : Finset (Fin m)) :
    (∃ v ∈ B.biUnion support, v ∈ U) ↔ ∃ i ∈ B, i ∈ encode support U := by
  constructor
  · rintro ⟨v, hv, hU⟩
    obtain ⟨i, hi, hv⟩ := Finset.mem_biUnion.mp hv
    exact ⟨i, hi, Finset.mem_filter.mpr ⟨Finset.mem_univ _, v, hv, hU⟩⟩
  · rintro ⟨i, hi, hU⟩
    obtain ⟨v, hv, hU⟩ := (Finset.mem_filter.mp hU).2
    exact ⟨v, Finset.mem_biUnion.mpr ⟨i, hi, hv⟩, hU⟩

lemma side_eq {n m k : ℕ} (support : Fin n → Finset (Fin m))
    (B : Finset (Fin n)) (U : Finset (Fin m)) (F : Finset (Fin k))
    (i : Fin k) (val : Fin k → Bool) :
    AndCountCircuit.sideTrue U (B.biUnion support) F i val =
      AndCountCircuit.sideTrue (encode support U) B F i val := by
  unfold AndCountCircuit.sideTrue
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, support_hit]

lemma fuel_eq {n m : ℕ} (C : AndCountCircuit n)
    (support : Fin n → Finset (Fin m)) (U : Finset (Fin m)) :
    ∀ (d : ℕ) (i : Fin C.size),
      (substitute C support).gateValFuel U d i = C.gateValFuel (encode support U) d i := by
  intro d
  induction d with
  | zero => intro i; rfl
  | succ d ih =>
    intro i
    simp only [AndCountCircuit.gateValFuel, substitute]
    have hv : (fun j : Fin C.size => (substitute C support).gateValFuel U d j) =
        (fun j : Fin C.size => C.gateValFuel (encode support U) d j) := funext ih
    change
      (AndCountCircuit.sideTrue U ((C.leftVars i).biUnion support) (C.leftGates i) i
          (fun j => (substitute C support).gateValFuel U d j) &&
       AndCountCircuit.sideTrue U ((C.rightVars i).biUnion support) (C.rightGates i) i
          (fun j => (substitute C support).gateValFuel U d j)) = _
    rw [hv, side_eq, side_eq]

lemma gate_eq {n m : ℕ} (C : AndCountCircuit n)
    (support : Fin n → Finset (Fin m)) (U : Finset (Fin m)) (i : Fin C.size) :
    (substitute C support).gateVal U i = C.gateVal (encode support U) i :=
  fuel_eq C support U C.size i

lemma eval_eq {n m : ℕ} (C : AndCountCircuit n)
    (support : Fin n → Finset (Fin m)) (U : Finset (Fin m)) :
    (substitute C support).eval U = C.eval (encode support U) := by
  apply Bool.eq_iff_iff.mpr
  simp only [AndCountCircuit.eval, decide_eq_true_eq]
  change ((∃ v ∈ C.outVars.biUnion support, v ∈ U) ∨
      ∃ j ∈ C.outGates, (substitute C support).gateVal U j = true) ↔ _
  simp only [support_hit, gate_eq]

end PEqualNP.Outside.L_meta_650_aux.AndCountOrSubstitution
