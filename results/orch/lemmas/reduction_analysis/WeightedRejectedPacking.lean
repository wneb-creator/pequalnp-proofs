import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_650_aux.WeightedRejectedPacking

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

-- Extracted from the generic local argument in accepted R-meta-5060-52.
-- This theorem concerns AndCountCircuit; no conversion or gate-count preservation
-- for a different circuit representation is asserted here.

theorem sideEq {n k} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k) (v : Fin k → Bool) :
    sideTrue U B F i v = decide ((∃ u ∈ B, u ∈ U) ∨ ∃ j ∈ F, j < i ∧ v j = true) := rfl

theorem outEq {n} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    C.eval U = decide ((∃ u ∈ C.outVars, u ∈ U) ∨ ∃ j ∈ C.outGates, C.gateVal U j = true) := rfl

theorem fuelEq {n} (C : AndCountCircuit n) (U : Finset (Fin n)) (a : Nat) (i : Fin C.size) :
    C.gateValFuel U (a+1) i =
      (sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateValFuel U a) &&
       sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateValFuel U a)) := rfl

def wing {n} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) (b : Bool) :=
  sideTrue U (if b then C.rightVars i else C.leftVars i)
    (if b then C.rightGates i else C.leftGates i) i (C.gateVal U)

theorem stable {n} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size)
    (a b : Nat) (ha : i.val < a) (hb : i.val < b) :
    C.gateValFuel U a i = C.gateValFuel U b i := by
  induction a generalizing i b with
  | zero => omega
  | succ a ih =>
    cases b with
    | zero => omega
    | succ b =>
      have eq (B : Finset (Fin n)) (F : Finset (Fin C.size)) :
          sideTrue U B F i (C.gateValFuel U a) = sideTrue U B F i (C.gateValFuel U b) := by
        rw [sideEq,sideEq]
        congr 1
        apply propext
        constructor <;> rintro (raw | ⟨j,hj,lt,val⟩)
        · exact Or.inl raw
        · have h := ih j b (by change j.val < i.val at lt; omega) (by change j.val < i.val at lt; omega)
          exact Or.inr ⟨j,hj,lt,h ▸ val⟩
        · exact Or.inl raw
        · have h := ih j b (by change j.val < i.val at lt; omega) (by change j.val < i.val at lt; omega)
          exact Or.inr ⟨j,hj,lt,h.symm ▸ val⟩
      rw [fuelEq,fuelEq,eq,eq]

theorem value {n} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i = (wing C U i false && wing C U i true) :=
  stable C U i C.size (C.size+1) i.isLt (by omega)

theorem unionChoice {n} (C : AndCountCircuit n) (U V : Finset (Fin n)) (q : Fin C.size → Bool)
    (goodU : ∀ i, wing C U i (q i) = C.gateVal U i)
    (goodV : ∀ i, wing C V i (q i) = C.gateVal V i) :
    C.eval (U ∪ V) = true → C.eval U = true ∨ C.eval V = true := by
  have gates (d : Nat) : ∀ i : Fin C.size, C.gateValFuel (U ∪ V) d i = true →
      C.gateVal U i = true ∨ C.gateVal V i = true := by
    induction d with
    | zero => intro i h; cases h
    | succ d ih =>
      intro i h
      have both := Bool.and_eq_true_iff.mp h
      have pick : sideTrue (U ∪ V) (if q i then C.rightVars i else C.leftVars i)
          (if q i then C.rightGates i else C.leftGates i) i (C.gateValFuel (U ∪ V) d) = true := by
        cases q i
        · exact both.1
        · exact both.2
      rw [← goodU i, ← goodV i]
      simp only [wing,sideEq,decide_eq_true_eq] at pick ⊢
      rcases pick with ⟨v,hv,hmem⟩ | ⟨j,hj,hlt,on⟩
      · rcases Finset.mem_union.mp hmem with h | h
        · exact Or.inl (Or.inl ⟨v,hv,h⟩)
        · exact Or.inr (Or.inl ⟨v,hv,h⟩)
      · rcases ih j on with h | h
        · exact Or.inl (Or.inr ⟨j,hj,hlt,h⟩)
        · exact Or.inr (Or.inr ⟨j,hj,hlt,h⟩)
  simp only [outEq,decide_eq_true_eq]
  rintro (⟨v,hv,vhit⟩|⟨i,hi,hit⟩)
  · rcases Finset.mem_union.mp vhit with h | h
    · exact Or.inl (Or.inl ⟨v,hv,h⟩)
    · exact Or.inr (Or.inl ⟨v,hv,h⟩)
  · rcases gates C.size i hit with h | h
    · exact Or.inl (Or.inr ⟨i,hi,h⟩)
    · exact Or.inr (Or.inr ⟨i,hi,h⟩)

def free {n} (C : AndCountCircuit n) (U : Finset (Fin n)) : Finset (Fin C.size) :=
  Finset.univ.filter fun i => wing C U i false = wing C U i true

def encode {n} (C : AndCountCircuit n) (U : Finset (Fin n)) (s : Finset (Fin C.size)) :
    Fin C.size → Bool := fun i => if i ∈ free C U then decide (i ∈ s) else wing C U i false

theorem good {n} (C : AndCountCircuit n) (U : Finset (Fin n)) (s : Finset (Fin C.size))
    (i : Fin C.size) : wing C U i (encode C U s i) = C.gateVal U i := by
  rw [value]
  simp only [encode,free,Finset.mem_filter,Finset.mem_univ,true_and]
  cases h : wing C U i false <;> cases h' : wing C U i true <;> by_cases hs : i ∈ s <;> simp [h,h',hs]

theorem packing {n} (C : AndCountCircuit n) (F : Finset (Finset (Fin n)))
    (neg : ∀ U ∈ F, C.eval U = false)
    (pos : ∀ U ∈ F, ∀ V ∈ F, U ≠ V → C.eval (U ∪ V) = true) :
    (∑ U ∈ F, 2 ^ (free C U).card) ≤ 2 ^ C.size := by
  classical
  let cubes := fun U => (free C U).powerset.image (encode C U)
  have card (U : Finset (Fin n)) : (cubes U).card = 2^(free C U).card := by
    unfold cubes
    rw [Finset.card_image_iff.mpr ?_, Finset.card_powerset]
    intro s hs t ht eq
    have ssub := Finset.mem_powerset.mp hs
    have tsub := Finset.mem_powerset.mp ht
    ext i
    by_cases hi : i ∈ free C U
    · have he := congrFun eq i
      simpa only [encode,ite_eq_left hi,decide_eq_decide] using he
    · exact iff_of_false (fun h => hi (ssub h)) (fun h => hi (tsub h))
  have dis : (F : Set (Finset (Fin n))).PairwiseDisjoint cubes := by
    intro U hu V hv ne
    apply Finset.disjoint_left.mpr
    intro q hq hq'
    obtain ⟨s,_,hs⟩ := Finset.mem_image.mp hq
    obtain ⟨t,_,ht⟩ := Finset.mem_image.mp hq'
    have both := unionChoice C U V q (hs ▸ good C U s) (ht ▸ good C V t) (pos U hu V hv ne)
    simp only [neg U hu,neg V hv, Bool.false_eq_true,or_self] at both
  calc
    _ = ∑ U ∈ F, (cubes U).card := by simp_rw [card]
    _ = (F.biUnion cubes).card := (Finset.card_biUnion dis).symm
    _ ≤ Fintype.card (Fin C.size → Bool) := Finset.card_le_univ _
    _ = _ := by simp

end PEqualNP.Outside.L_meta_650_aux.WeightedRejectedPacking
