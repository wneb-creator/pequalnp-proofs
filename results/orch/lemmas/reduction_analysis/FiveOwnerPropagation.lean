import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_650_aux.FiveOwnerPropagation

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


def sideVars {n} (C : AndCountCircuit n) (i : Fin C.size) (b : Bool) :=
  if b then C.rightVars i else C.leftVars i

def sideGates {n} (C : AndCountCircuit n) (i : Fin C.size) (b : Bool) :=
  if b then C.rightGates i else C.leftGates i

def rawHit {n} (U B : Finset (Fin n)) : Prop := ∃ u ∈ B, u ∈ U

theorem wing_parts {n} (C : AndCountCircuit n) (U : Finset (Fin n))
    (i : Fin C.size) (b : Bool) :
    wing C U i b = true ↔ rawHit U (sideVars C i b) ∨
      ∃ j ∈ sideGates C i b, j < i ∧ C.gateVal U j = true := by
  simp only [wing, sideEq, decide_eq_true_eq, rawHit, sideVars, sideGates]

theorem active_wing {n} (C : AndCountCircuit n) (U : Finset (Fin n))
    (i : Fin C.size) (h : C.gateVal U i = true) (b : Bool) : wing C U i b = true := by
  rw [value] at h
  have both := Bool.and_eq_true_iff.mp h
  cases b
  · exact both.1
  · exact both.2

theorem active_of_raw {n} (C : AndCountCircuit n) (U : Finset (Fin n))
    (i : Fin C.size) (hl : rawHit U (C.leftVars i)) (hr : rawHit U (C.rightVars i)) :
    C.gateVal U i = true := by
  rw [value]
  apply Bool.and_eq_true_iff.mpr
  exact ⟨(wing_parts C U i false).mpr (Or.inl hl),
    (wing_parts C U i true).mpr (Or.inl hr)⟩

theorem no_out_vars_of_rejected_singletons {n} (C : AndCountCircuit n)
    (h : ∀ v : Fin n, C.eval {v} = false) : C.outVars = ∅ := by
  apply Finset.ext
  intro v
  constructor
  · intro hv
    have hon : C.eval {v} = true := by
      rw [outEq]
      apply decide_eq_true_eq.mpr
      exact Or.inl ⟨v,hv,by simp⟩
    rw [h v] at hon
    cases hon
  · intro hv
    simp at hv

theorem sides_disjoint_of_singletons {n} (C : AndCountCircuit n)
    (h : ∀ (i : Fin C.size) (v : Fin n), C.gateVal {v} i = false)
    (i : Fin C.size) : Disjoint (C.leftVars i) (C.rightVars i) := by
  apply Finset.disjoint_left.mpr
  intro v hl hr
  have hon := active_of_raw C {v} i ⟨v,hl,by simp⟩ ⟨v,hr,by simp⟩
  rw [h i v] at hon
  cases hon

theorem first_active_raw {n} (C : AndCountCircuit n) (U : Finset (Fin n))
    (h : ∃ i : Fin C.size, C.gateVal U i = true) :
    ∃ i : Fin C.size, C.gateVal U i = true ∧
      (∀ j, j < i → C.gateVal U j = false) ∧
      rawHit U (C.leftVars i) ∧ rawHit U (C.rightVars i) := by
  let A := Finset.univ.filter fun i => C.gateVal U i = true
  have hA : A.Nonempty := by
    obtain ⟨i,hi⟩ := h
    exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
  let i := A.min' hA
  have hi : i ∈ A := Finset.min'_mem A hA
  have hon : C.gateVal U i = true := (Finset.mem_filter.mp hi).2
  have before : ∀ j, j < i → C.gateVal U j = false := by
    intro j hj
    cases hv : C.gateVal U j
    · rfl
    · have hjA : j ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩
      have hmin : i ≤ j := Finset.min'_le A j hjA
      exact False.elim (not_lt_of_ge hmin hj)
  refine ⟨i,hon,before,?_,?_⟩
  · rcases (wing_parts C U i false).mp (active_wing C U i hon false) with raw | ⟨j,hj,lt,on⟩
    · exact raw
    · rw [before j lt] at on
      cases on
  · rcases (wing_parts C U i true).mp (active_wing C U i hon true) with raw | ⟨j,hj,lt,on⟩
    · exact raw
    · rw [before j lt] at on
      cases on

theorem pair_has_origin {n} (C : AndCountCircuit n) (u v : Fin n)
    (hout : C.outVars = ∅)
    (hsingle : ∀ (i : Fin C.size) (w : Fin n), C.gateVal {w} i = false)
    (hpair : C.eval {u,v} = true) :
    ∃ i : Fin C.size, (u ∈ C.leftVars i ∧ v ∈ C.rightVars i) ∨
      (v ∈ C.leftVars i ∧ u ∈ C.rightVars i) := by
  have hactive : ∃ i : Fin C.size, C.gateVal {u,v} i = true := by
    rw [outEq] at hpair
    have hp := decide_eq_true_eq.mp hpair
    rcases hp with ⟨w,hw,_⟩ | ⟨i,hi,hon⟩
    · simp [hout] at hw
    · exact ⟨i,hon⟩
  obtain ⟨i,hi,hbefore,⟨l,hl,hlU⟩,⟨r,hr,hrU⟩⟩ := first_active_raw C {u,v} hactive
  have hd := Finset.disjoint_left.mp (sides_disjoint_of_singletons C hsingle i)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hlU hrU
  refine ⟨i,?_⟩
  rcases hlU with rfl | rfl <;> rcases hrU with rfl | rfl
  · exact False.elim (hd hl hr)
  · exact Or.inl ⟨hl,hr⟩
  · exact Or.inr ⟨hl,hr⟩
  · exact False.elim (hd hl hr)

-- A rejected input prevents a true source from entering a wing whose opposite raw wing is true.
theorem rejected_forbids_source {n} (C : AndCountCircuit n) (U : Finset (Fin n))
    (i k : Fin C.size) (b : Bool) (hk : C.gateVal U k = true)
    (hi : C.gateVal U i = false) (hlt : k < i)
    (hraw : rawHit U (sideVars C i (!b))) : k ∉ sideGates C i b := by
  intro hin
  have hside : wing C U i b = true :=
    (wing_parts C U i b).mpr (Or.inr ⟨k,hin,hlt,hk⟩)
  have hother : wing C U i (!b) = true :=
    (wing_parts C U i (!b)).mpr (Or.inl hraw)
  have hon : C.gateVal U i = true := by
    rw [value]
    apply Bool.and_eq_true_iff.mpr
    cases b
    · exact ⟨hside,hother⟩
    · exact ⟨hother,hside⟩
  rw [hi] at hon
  cases hon

-- If all other point wings have no active raw input and exclude the chosen gate,
-- no other gate can become the first active successor of that gate.
theorem only_selected_active {n} (C : AndCountCircuit n) (P : Finset (Fin n))
    (k : Fin C.size) (pointSide : Fin C.size → Bool)
    (hraw : ∀ j, j ≠ k → ¬rawHit P (sideVars C j (pointSide j)))
    (hexclude : ∀ j, k < j → k ∉ sideGates C j (pointSide j)) :
    ∀ j, j ≠ k → C.gateVal P j = false := by
  have aux : ∀ t : ℕ, ∀ j : Fin C.size, j.val = t → j ≠ k → C.gateVal P j = false := by
    intro t
    induction t using Nat.strong_induction_on with
    | ind t ih =>
      intro j hj hne
      cases hv : C.gateVal P j
      · rfl
      · have hp := (wing_parts C P j (pointSide j)).mp (active_wing C P j hv (pointSide j))
        rcases hp with raw | ⟨s,hs,hlt,hsval⟩
        · exact False.elim (hraw j hne raw)
        · by_cases hsk : s = k
          · subst s
            exact False.elim (hexclude j hlt hs)
          · have hslt : s.val < t := by change s.val < j.val at hlt; omega
            have hzero := ih s.val hslt s rfl hsk
            rw [hzero] at hsval
            cases hsval
  intro j hne
  exact aux j.val j rfl hne

theorem dirty_source_cannot_compute {n} (C : AndCountCircuit n)
    (P N : Finset (Fin n)) (k : Fin C.size) (pointSide : Fin C.size → Bool)
    (hout : C.outVars = ∅)
    (hraw : ∀ j, j ≠ k → ¬rawHit P (sideVars C j (pointSide j)))
    (hexclude : ∀ j, k < j → k ∉ sideGates C j (pointSide j))
    (hk : C.gateVal N k = true) (hneg : C.eval N = false) (hpos : C.eval P = true) : False := by
  have only := only_selected_active C P k pointSide hraw hexclude
  rw [outEq] at hpos
  have hp := decide_eq_true_eq.mp hpos
  rcases hp with ⟨v,hv,_⟩ | ⟨i,hi,hon⟩
  · simp [hout] at hv
  · have hik : i = k := by
      by_contra hne
      rw [only i hne] at hon
      cases hon
    subst i
    have hwrong : C.eval N = true := by
      rw [outEq]
      exact decide_eq_true_eq.mpr (Or.inr ⟨k,hi,hk⟩)
    rw [hneg] at hwrong
    cases hwrong

end PEqualNP.Outside.L_meta_650_aux.FiveOwnerPropagation
