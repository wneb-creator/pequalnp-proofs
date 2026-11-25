import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9811.AndSeven

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

abbrev V := Fin 14

def edgeList : List (ℕ × ℕ) :=
  [(0, 8), (0, 10), (1, 7), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]

def hAdj (a b : V) : Bool :=
  decide (a ≠ b ∧ (((a : ℕ), (b : ℕ)) ∈ edgeList ∨ ((b : ℕ), (a : ℕ)) ∈ edgeList))

def Good (I : Finset V) : Prop :=
  (∀ a ∈ I, ∀ c ∈ I, hAdj a c = false) ∧
  (∀ w : V, w ∉ I → ∃ a ∈ I, hAdj a w = true)

def rows : Fin 39 → Finset V :=
  ![{0, 1, 2, 3, 4, 5, 6},
    {0, 2, 4, 5, 6, 7},
    {1, 3, 4, 5, 8},
    {4, 5, 7, 8},
    {0, 1, 2, 3, 4, 9},
    {0, 2, 4, 7, 9},
    {1, 3, 4, 8, 9},
    {1, 2, 3, 6, 10},
    {2, 6, 7, 10},
    {1, 2, 3, 9, 10},
    {1, 3, 8, 9, 10},
    {0, 1, 2, 5, 11},
    {0, 2, 5, 7, 11},
    {1, 5, 8, 11},
    {0, 1, 2, 9, 11},
    {0, 2, 7, 9, 11},
    {1, 2, 9, 10, 11},
    {2, 7, 9, 10, 11},
    {0, 1, 4, 6, 12},
    {0, 4, 6, 7, 12},
    {0, 1, 4, 9, 12},
    {0, 4, 7, 9, 12},
    {1, 4, 8, 9, 12},
    {4, 7, 8, 9, 12},
    {1, 6, 10, 12},
    {0, 1, 9, 11, 12},
    {1, 8, 9, 10, 11, 12},
    {0, 3, 5, 6, 13},
    {0, 5, 6, 7, 13},
    {3, 5, 8, 13},
    {0, 3, 9, 13},
    {3, 6, 10, 13},
    {3, 8, 9, 10, 13},
    {0, 5, 7, 11, 13},
    {5, 7, 8, 11, 13},
    {0, 6, 7, 12, 13},
    {6, 7, 10, 12, 13},
    {0, 7, 9, 11, 12, 13},
    {7, 8, 9, 10, 11, 12, 13}]

def through : Fin 2 → Fin 17 → Fin 39 :=
  ![![0, 2, 4, 6, 7, 9, 10, 11, 13, 14, 16, 18, 20, 22, 24, 25, 26],
    ![1, 3, 5, 8, 12, 15, 17, 19, 21, 23, 28, 33, 34, 35, 36, 37, 38]]

def castX (x : Fin 2) : V := ![1,7] x

lemma rowsGood : ∀ r : Fin 39, Good (rows r) := by
  unfold Good
  decide +kernel

lemma rowContains : ∀ (x : Fin 2) (i : Fin 17), castX x ∈ rows (through x i) := by
  decide +kernel

lemma rowDiff : ∀ (x : Fin 2) (i j : Fin 17), i ≠ j →
    ∃ w ∈ rows (through x i), w ∉ rows (through x j) := by
  decide +kernel

lemma coverXY : ∀ v : V, v ∈ rows 0 ∨ v ∈ rows 38 := by
  decide +kernel

private lemma sideTrue_congr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v1 v2 : Fin k → Bool) (h : ∀ j, j < i → v1 j = v2 j) :
    sideTrue U B F i v1 = sideTrue U B F i v2 := by
  unfold sideTrue
  refine decide_eq_decide.mpr ?_
  constructor
  · rintro (hv | ⟨j, hjF, hji, hvj⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨j, hjF, hji, by rwa [← h j hji]⟩
  · rintro (hv | ⟨j, hjF, hji, hvj⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨j, hjF, hji, by rwa [h j hji]⟩

private lemma gateValFuel_indep {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (m : ℕ) (i : Fin C.size), i.val < m →
      ∀ (d1 d2 : ℕ), i.val < d1 → i.val < d2 →
        C.gateValFuel U d1 i = C.gateValFuel U d2 i := by
  intro m
  induction m with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi d1 d2 hd1 hd2
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : d1 ≠ 0) with ⟨k1, rfl⟩
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : d2 ≠ 0) with ⟨k2, rfl⟩
    simp only [gateValFuel]
    have hlt : ∀ j : Fin C.size, j < i → C.gateValFuel U k1 j = C.gateValFuel U k2 j := by
      intro j hji
      exact ih j (by omega) k1 k2 (by omega) (by omega)
    rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hlt,
        sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hlt]

private lemma gateVal_unfold {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n))
    (i : Fin C.size) :
    C.gateVal U i =
      (sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
       sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) := by
  have heq : C.gateVal U i = C.gateValFuel U (i.val + 1) i :=
    gateValFuel_indep C U C.size i i.isLt C.size (i.val + 1) i.isLt (Nat.lt_succ_self _)
  rw [heq]
  simp only [gateValFuel]
  have hlt : ∀ j : Fin C.size, j < i → C.gateValFuel U i.val j = C.gateVal U j := by
    intro j hji
    exact gateValFuel_indep C U C.size j j.isLt i.val C.size hji j.isLt
  rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hlt,
      sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hlt]

private lemma sideTrue_mono_U {n k : ℕ} {U W : Finset (Fin n)} (hUW : U ⊆ W)
    (B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v1 v2 : Fin k → Bool) (hv : ∀ j, j < i → v1 j = true → v2 j = true)
    (hs : sideTrue U B F i v1 = true) :
    sideTrue W B F i v2 = true := by
  unfold sideTrue at hs ⊢
  rw [decide_eq_true_eq] at hs ⊢
  rcases hs with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hvj⟩
  · exact Or.inl ⟨v, hvB, hUW hvU⟩
  · exact Or.inr ⟨j, hjF, hji, hv j hji hvj⟩

private lemma gateValFuel_mono_U {n : ℕ} (C : AndCountCircuit n) {U W : Finset (Fin n)}
    (hUW : U ⊆ W) :
    ∀ (d : ℕ) (i : Fin C.size), C.gateValFuel U d i = true → C.gateValFuel W d i = true := by
  intro d
  induction d with
  | zero =>
    intro i hi
    simp [gateValFuel] at hi
  | succ d ih =>
    intro i hi
    simp only [gateValFuel, Bool.and_eq_true] at hi ⊢
    exact ⟨sideTrue_mono_U hUW _ _ _ _ _ (fun j _ hj => ih j hj) hi.1,
           sideTrue_mono_U hUW _ _ _ _ _ (fun j _ hj => ih j hj) hi.2⟩

private lemma gateVal_mono_U {n : ℕ} (C : AndCountCircuit n) {U W : Finset (Fin n)}
    (hUW : U ⊆ W) (i : Fin C.size) (h : C.gateVal U i = true) : C.gateVal W i = true :=
  gateValFuel_mono_U C hUW C.size i h

private def singSet {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) : Finset (Fin n) :=
  Finset.univ.filter (fun v => C.gateVal {v} i = true)

private lemma mem_singSet {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (v : Fin n) :
    v ∈ singSet C i ↔ C.gateVal {v} i = true := by
  unfold singSet
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ v)

private def stripCircuit {n : ℕ} (C : AndCountCircuit n) : AndCountCircuit n where
  size := C.size
  leftVars i := (C.leftVars i ∪ ((C.leftGates i).filter (fun j => j < i)).biUnion (singSet C)) \ singSet C i
  leftGates := C.leftGates
  rightVars i := (C.rightVars i ∪ ((C.rightGates i).filter (fun j => j < i)).biUnion (singSet C)) \ singSet C i
  rightGates := C.rightGates
  outVars := C.outVars ∪ C.outGates.biUnion (singSet C)
  outGates := C.outGates

private lemma mem_strip_leftVars {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (v : Fin n) :
    v ∈ (stripCircuit C).leftVars i ↔
      (v ∈ C.leftVars i ∨ ∃ j ∈ C.leftGates i, j < i ∧ C.gateVal {v} j = true) ∧
      C.gateVal {v} i ≠ true := by
  change v ∈ (C.leftVars i ∪ ((C.leftGates i).filter (fun j => j < i)).biUnion (singSet C)) \ singSet C i ↔ _
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
    mem_singSet, and_assoc]

private lemma mem_strip_rightVars {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (v : Fin n) :
    v ∈ (stripCircuit C).rightVars i ↔
      (v ∈ C.rightVars i ∨ ∃ j ∈ C.rightGates i, j < i ∧ C.gateVal {v} j = true) ∧
      C.gateVal {v} i ≠ true := by
  change v ∈ (C.rightVars i ∪ ((C.rightGates i).filter (fun j => j < i)).biUnion (singSet C)) \ singSet C i ↔ _
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
    mem_singSet, and_assoc]

private lemma mem_strip_outVars {n : ℕ} (C : AndCountCircuit n) (v : Fin n) :
    v ∈ (stripCircuit C).outVars ↔
      v ∈ C.outVars ∨ ∃ j ∈ C.outGates, C.gateVal {v} j = true := by
  change v ∈ C.outVars ∪ C.outGates.biUnion (singSet C) ↔ _
  simp only [Finset.mem_union, Finset.mem_biUnion, mem_singSet]

private lemma strip_singleton_false {n : ℕ} (C : AndCountCircuit n) (v : Fin n) :
    ∀ (m : ℕ) (i : Fin C.size), i.val < m → (stripCircuit C).gateVal {v} i = false := by
  intro m
  induction m with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi
    rw [Bool.eq_false_iff]
    intro htrue
    rw [gateVal_unfold (stripCircuit C) {v} i, Bool.and_eq_true] at htrue
    have hL := htrue.1
    have hR := htrue.2
    unfold sideTrue at hL hR
    rw [decide_eq_true_eq] at hL hR
    have hLv : v ∈ (stripCircuit C).leftVars i := by
      rcases hL with ⟨w, hw, hwv⟩ | ⟨j, _, hji, hjv⟩
      · rwa [Finset.mem_singleton.mp hwv] at hw
      · rw [ih j (by omega)] at hjv
        exact absurd hjv Bool.false_ne_true
    have hRv : v ∈ (stripCircuit C).rightVars i := by
      rcases hR with ⟨w, hw, hwv⟩ | ⟨j, _, hji, hjv⟩
      · rwa [Finset.mem_singleton.mp hwv] at hw
      · rw [ih j (by omega)] at hjv
        exact absurd hjv Bool.false_ne_true
    rw [mem_strip_leftVars] at hLv
    rw [mem_strip_rightVars] at hRv
    have hCv : C.gateVal {v} i = true := by
      rw [gateVal_unfold C {v} i, Bool.and_eq_true]
      constructor
      · unfold sideTrue
        rw [decide_eq_true_eq]
        rcases hLv.1 with hv | ⟨j, hjF, hji, hjv⟩
        · exact Or.inl ⟨v, hv, Finset.mem_singleton_self v⟩
        · exact Or.inr ⟨j, hjF, hji, hjv⟩
      · unfold sideTrue
        rw [decide_eq_true_eq]
        rcases hRv.1 with hv | ⟨j, hjF, hji, hjv⟩
        · exact Or.inl ⟨v, hv, Finset.mem_singleton_self v⟩
        · exact Or.inr ⟨j, hjF, hji, hjv⟩
    exact hLv.2 hCv

private lemma strip_disjoint {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) :
    Disjoint ((stripCircuit C).leftVars i) ((stripCircuit C).rightVars i) := by
  rw [Finset.disjoint_left]
  intro v hvL hvR
  have hf := strip_singleton_false C v C.size i i.isLt
  have ht : (stripCircuit C).gateVal {v} i = true := by
    rw [gateVal_unfold (stripCircuit C) {v} i, Bool.and_eq_true]
    constructor
    · unfold sideTrue
      rw [decide_eq_true_eq]
      exact Or.inl ⟨v, hvL, Finset.mem_singleton_self v⟩
    · unfold sideTrue
      rw [decide_eq_true_eq]
      exact Or.inl ⟨v, hvR, Finset.mem_singleton_self v⟩
  rw [hf] at ht
  exact Bool.false_ne_true ht

private lemma strip_gateVal_le {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (m : ℕ) (i : Fin C.size), i.val < m →
      (stripCircuit C).gateVal U i = true → C.gateVal U i = true := by
  intro m
  induction m with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi hval
    rw [gateVal_unfold (stripCircuit C) U i, Bool.and_eq_true] at hval
    rw [gateVal_unfold C U i, Bool.and_eq_true]
    constructor
    · have hL := hval.1
      unfold sideTrue at hL ⊢
      rw [decide_eq_true_eq] at hL ⊢
      rcases hL with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjv⟩
      · rw [mem_strip_leftVars] at hvB
        rcases hvB.1 with hvC | ⟨j, hjF, hji, hjv⟩
        · exact Or.inl ⟨v, hvC, hvU⟩
        · exact Or.inr ⟨j, hjF, hji, gateVal_mono_U C (Finset.singleton_subset_iff.mpr hvU) j hjv⟩
      · exact Or.inr ⟨j, hjF, hji, ih j (by omega) hjv⟩
    · have hR := hval.2
      unfold sideTrue at hR ⊢
      rw [decide_eq_true_eq] at hR ⊢
      rcases hR with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjv⟩
      · rw [mem_strip_rightVars] at hvB
        rcases hvB.1 with hvC | ⟨j, hjF, hji, hjv⟩
        · exact Or.inl ⟨v, hvC, hvU⟩
        · exact Or.inr ⟨j, hjF, hji, gateVal_mono_U C (Finset.singleton_subset_iff.mpr hvU) j hjv⟩
      · exact Or.inr ⟨j, hjF, hji, ih j (by omega) hjv⟩

private lemma strip_gateVal_ge {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (m : ℕ) (i : Fin C.size), i.val < m →
      C.gateVal U i = true →
        (∃ v ∈ U, C.gateVal {v} i = true) ∨ (stripCircuit C).gateVal U i = true := by
  intro m
  induction m with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi hval
    by_cases hsing : ∃ v ∈ U, C.gateVal {v} i = true
    · exact Or.inl hsing
    · right
      have hno : ∀ v ∈ U, C.gateVal {v} i ≠ true := fun v hvU hv => hsing ⟨v, hvU, hv⟩
      rw [gateVal_unfold C U i, Bool.and_eq_true] at hval
      rw [gateVal_unfold (stripCircuit C) U i, Bool.and_eq_true]
      constructor
      · have hL := hval.1
        unfold sideTrue at hL ⊢
        rw [decide_eq_true_eq] at hL ⊢
        rcases hL with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjv⟩
        · exact Or.inl ⟨v, (mem_strip_leftVars C i v).mpr ⟨Or.inl hvB, hno v hvU⟩, hvU⟩
        · rcases ih j (by omega) hjv with ⟨v, hvU, hvs⟩ | hj'
          · exact Or.inl ⟨v, (mem_strip_leftVars C i v).mpr ⟨Or.inr ⟨j, hjF, hji, hvs⟩, hno v hvU⟩, hvU⟩
          · exact Or.inr ⟨j, hjF, hji, hj'⟩
      · have hR := hval.2
        unfold sideTrue at hR ⊢
        rw [decide_eq_true_eq] at hR ⊢
        rcases hR with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjv⟩
        · exact Or.inl ⟨v, (mem_strip_rightVars C i v).mpr ⟨Or.inl hvB, hno v hvU⟩, hvU⟩
        · rcases ih j (by omega) hjv with ⟨v, hvU, hvs⟩ | hj'
          · exact Or.inl ⟨v, (mem_strip_rightVars C i v).mpr ⟨Or.inr ⟨j, hjF, hji, hvs⟩, hno v hvU⟩, hvU⟩
          · exact Or.inr ⟨j, hjF, hji, hj'⟩

private lemma strip_eval_eq {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    (stripCircuit C).eval U = C.eval U := by
  unfold AndCountCircuit.eval
  refine decide_eq_decide.mpr ?_
  constructor
  · rintro (⟨v, hvO, hvU⟩ | ⟨j, hjO, hjv⟩)
    · rw [mem_strip_outVars] at hvO
      rcases hvO with hvC | ⟨j, hjO, hvs⟩
      · exact Or.inl ⟨v, hvC, hvU⟩
      · exact Or.inr ⟨j, hjO, gateVal_mono_U C (Finset.singleton_subset_iff.mpr hvU) j hvs⟩
    · exact Or.inr ⟨j, hjO, strip_gateVal_le C U C.size j j.isLt hjv⟩
  · rintro (⟨v, hvO, hvU⟩ | ⟨j, hjO, hjv⟩)
    · exact Or.inl ⟨v, (mem_strip_outVars C v).mpr (Or.inl hvO), hvU⟩
    · rcases strip_gateVal_ge C U C.size j j.isLt hjv with ⟨v, hvU, hvs⟩ | hj'
      · exact Or.inl ⟨v, (mem_strip_outVars C v).mpr (Or.inr ⟨j, hjO, hvs⟩), hvU⟩
      · exact Or.inr ⟨j, hjO, hj'⟩

def Free (C : AndCountCircuit 14) (v : V) : Finset (Fin C.size) :=
  Finset.univ.filter (fun i => v ∉ C.leftVars i ∧ v ∉ C.rightVars i)

def sideL (C : AndCountCircuit 14) (I : Finset V) (i : Fin C.size) : Bool :=
  sideTrue I (C.leftVars i) (C.leftGates i) i (C.gateVal I)

def sideR (C : AndCountCircuit 14) (I : Finset V) (i : Fin C.size) : Bool :=
  sideTrue I (C.rightVars i) (C.rightGates i) i (C.gateVal I)

def Separates (C : AndCountCircuit 14) : Prop :=
  ∀ r : Fin 39, C.eval (rows r) = false ∧ ∀ w : V, w ∉ rows r → C.eval (insert w (rows r)) = true

lemma unionSide (C : AndCountCircuit 14) (U I J B : Finset V)
    (F : Finset (Fin C.size)) (i : Fin C.size) (hU : U ⊆ I ∪ J)
    (ih : ∀ j < i, C.gateVal U j = true → C.gateVal I j = true ∨ C.gateVal J j = true) :
    sideTrue U B F i (C.gateVal U) = true →
    sideTrue I B F i (C.gateVal I) = true ∨ sideTrue J B F i (C.gateVal J) = true := by
  simp only [sideTrue, decide_eq_true_eq]
  rintro (⟨v, hv, hu⟩ | ⟨j, hj, hji, ht⟩)
  · rcases Finset.mem_union.mp (hU hu) with h | h
    · exact Or.inl (Or.inl ⟨v, hv, h⟩)
    · exact Or.inr (Or.inl ⟨v, hv, h⟩)
  · rcases ih j hji ht with h | h
    · exact Or.inl (Or.inr ⟨j, hj, hji, h⟩)
    · exact Or.inr (Or.inr ⟨j, hj, hji, h⟩)

lemma mergeInput (C : AndCountCircuit 14) (I J U : Finset V) (v : V)
    (hi : v ∈ I) (hj : v ∈ J) (hU : U ⊆ I ∪ J)
    (hs : ∀ i ∈ Free C v, sideL C I i = sideL C J i) :
    C.eval U = true → C.eval I = true ∨ C.eval J = true := by
  have gate (i : Fin C.size) : C.gateVal U i = true →
      C.gateVal I i = true ∨ C.gateVal J i = true := by
    induction i using ((wellFounded_lt : WellFounded ((· < ·) : Fin C.size → Fin C.size → Prop)).induction) with
    | h i ih =>
      intro ht
      rw [gateVal_unfold, Bool.and_eq_true] at ht
      rw [gateVal_unfold C I, gateVal_unfold C J]
      change (sideL C I i && sideR C I i) = true ∨ (sideL C J i && sideR C J i) = true
      have hl : sideL C I i = true ∨ sideL C J i = true := unionSide C U I J _ _ i hU ih ht.1
      have hr : sideR C I i = true ∨ sideR C J i = true := unionSide C U I J _ _ i hU ih ht.2
      simp only [Bool.and_eq_true]
      by_cases h1 : v ∈ C.leftVars i
      · have a : sideL C I i = true := decide_eq_true (Or.inl ⟨v, h1, hi⟩)
        have b : sideL C J i = true := decide_eq_true (Or.inl ⟨v, h1, hj⟩)
        rcases hr with hr | hr
        · exact Or.inl ⟨a, hr⟩
        · exact Or.inr ⟨b, hr⟩
      by_cases h2 : v ∈ C.rightVars i
      · have a : sideR C I i = true := decide_eq_true (Or.inl ⟨v, h2, hi⟩)
        have b : sideR C J i = true := decide_eq_true (Or.inl ⟨v, h2, hj⟩)
        rcases hl with hl | hl
        · exact Or.inl ⟨hl, a⟩
        · exact Or.inr ⟨hl, b⟩
      have hh := hs i (by simp [Free, h1, h2])
      have hlj : sideL C J i = true := by
        rcases hl with hl | hl
        · exact hh.symm.trans hl
        · exact hl
      have hli : sideL C I i = true := hh.trans hlj
      rcases hr with hr | hr
      · exact Or.inl ⟨hli, hr⟩
      · exact Or.inr ⟨hlj, hr⟩
  simp only [eval, decide_eq_true_eq]
  rintro (⟨w, hw, h⟩ | ⟨i, hi', h⟩)
  · rcases Finset.mem_union.mp (hU h) with h | h
    · exact Or.inl (Or.inl ⟨_, hw, h⟩)
    · exact Or.inr (Or.inl ⟨_, hw, h⟩)
  · rcases gate i h with h | h
    · exact Or.inl (Or.inr ⟨i, hi', h⟩)
    · exact Or.inr (Or.inr ⟨i, hi', h⟩)

lemma free_bound (C : AndCountCircuit 14) (h : Separates C) (x : Fin 2) :
    5 ≤ (Free C (castX x)).card := by
  let code (a : Fin 17) (i : ↥(Free C (castX x))) := sideL C (rows (through x a)) i
  have hinj : Function.Injective code := by
    intro a b hab
    by_contra hne
    obtain ⟨w, hwa, hwb⟩ := rowDiff x a b hne
    let A := rows (through x a)
    let B := rows (through x b)
    have ha := h (through x a)
    have hb := h (through x b)
    have he := mergeInput C A B (insert w B) (castX x) (rowContains x a) (rowContains x b)
      (Finset.insert_subset (Finset.mem_union_left B hwa) Finset.subset_union_right)
      (fun i hi => congrFun hab ⟨i, hi⟩) (hb.2 w hwb)
    dsimp only [A, B] at he
    simp [ha.1, hb.1] at he
  have hc := Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_fin, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe] at hc
  by_contra! hbad
  have hp : 2 ^ (Free C (castX x)).card ≤ 2 ^ 4 := Nat.pow_le_pow_right (by decide) (by omega)
  omega

lemma bare_out_empty (C : AndCountCircuit 14) (h : Separates C) (v : V) : v ∉ C.outVars := by
  intro hv
  rcases coverXY v with h0 | h36
  · have he := (h 0).1
    have ht : C.eval (rows 0) = true := decide_eq_true (Or.inl ⟨v, hv, h0⟩)
    simp [he] at ht
  · have he := (h 38).1
    have ht : C.eval (rows 38) = true := decide_eq_true (Or.inl ⟨v, hv, h36⟩)
    simp [he] at ht

def litSet (C : AndCountCircuit 14) (v : V) : Finset (Fin C.size × Bool) :=
  Finset.univ.filter (fun p => if p.2 then v ∈ C.rightVars p.1 else v ∈ C.leftVars p.1)

lemma mem_litSet (C : AndCountCircuit 14) (v : V) (g : Fin C.size) (b : Bool) :
    (g, b) ∈ litSet C v ↔ if b then v ∈ C.rightVars g else v ∈ C.leftVars g := by
  simp [litSet]

lemma litSet_disj (C : AndCountCircuit 14) (hdisj : ∀ i, Disjoint (C.leftVars i) (C.rightVars i))
    (v : V) (g : Fin C.size) : ¬ ((g, false) ∈ litSet C v ∧ (g, true) ∈ litSet C v) := by
  rintro ⟨hl, hr⟩
  rw [mem_litSet] at hl hr
  exact Finset.disjoint_left.mp (hdisj g) hl hr

lemma litSet_card_le (C : AndCountCircuit 14) (h : Separates C)
    (hdisj : ∀ i, Disjoint (C.leftVars i) (C.rightVars i)) (hsz : C.size ≤ 6) (x : Fin 2) :
    (litSet C (castX x)).card ≤ 1 := by
  have hinj : Set.InjOn Prod.fst (litSet C (castX x) : Set (Fin C.size × Bool)) := by
    intro p1 hp1 p2 hp2 heq
    rcases p1 with ⟨g1, b1⟩
    rcases p2 with ⟨g2, b2⟩
    dsimp at heq
    subst heq
    cases b1 <;> cases b2
    · rfl
    · exact (litSet_disj C hdisj (castX x) g1 ⟨hp1, hp2⟩).elim
    · exact (litSet_disj C hdisj (castX x) g1 ⟨hp2, hp1⟩).elim
    · rfl
  have hcard : (litSet C (castX x)).card = ((litSet C (castX x)).image Prod.fst).card :=
    (Finset.card_image_of_injOn hinj).symm
  have hsub : (litSet C (castX x)).image Prod.fst ⊆ Finset.univ \ Free C (castX x) := by
    intro g hg
    obtain ⟨⟨g', b⟩, hb, rfl⟩ := Finset.mem_image.mp hg
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ _, ?_⟩
    simp only [Free, Finset.mem_filter, Finset.mem_univ, true_and, not_and_or, not_not]
    rw [mem_litSet] at hb
    cases b
    · exact Or.inl hb
    · exact Or.inr hb
  have hle := Finset.card_le_card hsub
  have htot := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (Free C (castX x)))
  have hfb := free_bound C h x
  simp only [Finset.card_univ, Fintype.card_fin] at htot
  omega

lemma mis_cover (C : AndCountCircuit 14) (h : Separates C) (r : Fin 39) :
    ∃ f : Fin C.size → Option Bool,
      (∀ v ∈ rows r, ∀ l ∈ litSet C v, f l.1 ≠ some l.2) ∧
      (∀ w : V, w ∉ rows r → ∃ l ∈ litSet C w, f l.1 = some l.2) := by
  let I := rows r
  let f : Fin C.size → Option Bool := fun i =>
    if sideL C I i = false then some false
    else if sideR C I i = false then some true
    else none
  refine ⟨f, ?_, ?_⟩
  · intro v hv l hl
    rcases l with ⟨g, b⟩
    rw [mem_litSet] at hl
    cases b
    · have hsL : sideL C I g = true := decide_eq_true (Or.inl ⟨v, hl, hv⟩)
      simp only [f, hsL, Bool.true_eq_false, ↓reduceIte]
      split_ifs <;> simp
    · have hsR : sideR C I g = true := decide_eq_true (Or.inl ⟨v, hl, hv⟩)
      simp only [f, hsR, Bool.true_eq_false, ↓reduceIte]
      split_ifs <;> simp
  · intro w hw
    have hev : C.eval (insert w I) = true := (h r).2 w hw
    have hfl : C.eval I = false := (h r).1
    let S : Finset (Fin C.size) :=
      Finset.univ.filter (fun i => C.gateVal I i = false ∧ C.gateVal (insert w I) i = true)
    have hSne : S.Nonempty := by
      rw [eval, decide_eq_true_eq] at hev
      rcases hev with ⟨v, hv, _⟩ | ⟨i, hi, hit⟩
      · exact (bare_out_empty C h v hv).elim
      · refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, hit⟩⟩
        rw [Bool.eq_false_iff]
        intro hti
        have het : C.eval I = true := decide_eq_true (Or.inr ⟨i, hi, hti⟩)
        simp [hfl] at het
    let g := S.min' hSne
    have hgS : g ∈ S := S.min'_mem hSne
    have hgF : C.gateVal I g = false := (Finset.mem_filter.mp hgS).2.1
    have hgT : C.gateVal (insert w I) g = true := (Finset.mem_filter.mp hgS).2.2
    have hmin : ∀ j : Fin C.size, j < g → C.gateVal (insert w I) j = true → C.gateVal I j = true := by
      intro j hj hjt
      by_contra hnf
      have hjf : C.gateVal I j = false := Bool.eq_false_iff.mpr hnf
      have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjf, hjt⟩
      exact (not_le_of_gt hj) (S.min'_le j hjS)
    rw [gateVal_unfold C (insert w I) g, Bool.and_eq_true] at hgT
    rw [gateVal_unfold C I g] at hgF
    change (sideL C I g && sideR C I g) = false at hgF
    change sideL C (insert w I) g = true ∧ sideR C (insert w I) g = true at hgT
    by_cases hL : sideL C I g = false
    · refine ⟨(g, false), ?_, by simp [f, hL]⟩
      rw [mem_litSet]
      have hLT : sideL C (insert w I) g = true := hgT.1
      unfold sideL sideTrue at hLT hL
      rw [decide_eq_true_eq] at hLT
      rcases hLT with ⟨v, hv, hvI⟩ | ⟨j, hj, hji, hjt⟩
      · rcases Finset.mem_insert.mp hvI with rfl | hvi
        · exact hv
        · have ht : decide ((∃ u ∈ C.leftVars g, u ∈ I) ∨ ∃ j ∈ C.leftGates g, j < g ∧ C.gateVal I j = true) = true :=
            decide_eq_true (Or.inl ⟨v, hv, hvi⟩)
          simp [hL] at ht
      · have hjiT := hmin j hji hjt
        have ht : decide ((∃ u ∈ C.leftVars g, u ∈ I) ∨ ∃ j ∈ C.leftGates g, j < g ∧ C.gateVal I j = true) = true :=
          decide_eq_true (Or.inr ⟨j, hj, hji, hjiT⟩)
        simp [hL] at ht
    · have hLt : sideL C I g = true := by cases h' : sideL C I g <;> simp_all
      have hR : sideR C I g = false := by simp [hLt] at hgF; exact hgF
      refine ⟨(g, true), ?_, by simp [f, hLt, hR]⟩
      rw [mem_litSet]
      have hRT : sideR C (insert w I) g = true := hgT.2
      unfold sideR sideTrue at hRT hR
      rw [decide_eq_true_eq] at hRT
      rcases hRT with ⟨v, hv, hvI⟩ | ⟨j, hj, hji, hjt⟩
      · rcases Finset.mem_insert.mp hvI with rfl | hvi
        · exact hv
        · have ht : decide ((∃ u ∈ C.rightVars g, u ∈ I) ∨ ∃ j ∈ C.rightGates g, j < g ∧ C.gateVal I j = true) = true :=
            decide_eq_true (Or.inl ⟨v, hv, hvi⟩)
          simp [hR] at ht
      · have hjiT := hmin j hji hjt
        have ht : decide ((∃ u ∈ C.rightVars g, u ∈ I) ∨ ∃ j ∈ C.rightGates g, j < g ∧ C.gateVal I j = true) = true :=
          decide_eq_true (Or.inr ⟨j, hj, hji, hjiT⟩)
        simp [hR] at ht


lemma pair_birth (C : AndCountCircuit 14) (h : Separates C)
    (hd : ∀ i, Disjoint (C.leftVars i) (C.rightVars i))
    (hp : C.eval {1,7} = true) :
    ∃ (g : Fin C.size) (b : Bool),
      (g,b) ∈ litSet C 1 ∧ (g,!b) ∈ litSet C 7 := by
  classical
  let S : Finset (Fin C.size) := Finset.univ.filter (fun i => C.gateVal {1,7} i = true)
  have hs : S.Nonempty := by
    rw [eval, decide_eq_true_eq] at hp
    rcases hp with ⟨v,hv,_⟩ | ⟨i,_,hi⟩
    · exact (bare_out_empty C h v hv).elim
    · exact ⟨i, by simp [S,hi]⟩
  let g := S.min' hs
  have hg : C.gateVal {1,7} g = true := (Finset.mem_filter.mp (S.min'_mem hs)).2
  have early (j : Fin C.size) (hj : j < g) : C.gateVal {1,7} j = false := by
    apply Bool.eq_false_iff.mpr
    intro ht
    have hm : j ∈ S := by simp [S,ht]
    exact (not_le_of_gt hj) (S.min'_le j hm)
  rw [gateVal_unfold C {1,7} g, Bool.and_eq_true] at hg
  have pick (B : Finset V) (F : Finset (Fin C.size))
      (hb : sideTrue {1,7} B F g (C.gateVal {1,7}) = true) : 1 ∈ B ∨ 7 ∈ B := by
    rw [sideTrue, decide_eq_true_eq] at hb
    rcases hb with ⟨v,hv,hm⟩ | ⟨j,_,hj,ht⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with rfl | rfl
      · exact Or.inl hv
      · exact Or.inr hv
    · rw [early j hj] at ht
      exact Bool.noConfusion ht
  have hl := pick _ _ hg.1
  have hr := pick _ _ hg.2
  by_cases h1 : (1 : V) ∈ C.leftVars g
  · have hn : (1 : V) ∉ C.rightVars g := fun h2 => Finset.disjoint_left.mp (hd g) h1 h2
    refine ⟨g,false,?_,?_⟩
    · simpa [mem_litSet] using h1
    · simpa [mem_litSet] using hr.resolve_left hn
  · have h7 : (7 : V) ∈ C.leftVars g := hl.resolve_left h1
    have hn : (7 : V) ∉ C.rightVars g := fun h2 => Finset.disjoint_left.mp (hd g) h7 h2
    refine ⟨g,true,?_,?_⟩
    · simpa [mem_litSet] using hr.resolve_right hn
    · simpa [mem_litSet] using h7

lemma lower (C : AndCountCircuit 14) (h : Separates C) (hp : C.eval {1,7} = true) :
    7 ≤ C.size := by
  classical
  by_contra! hsmall
  have hc : C.size ≤ 6 := by omega
  let D := stripCircuit C
  have hD : Separates D := by
    intro r
    simpa only [D, strip_eval_eq] using h r
  have hpD : D.eval {1,7} = true := by simpa only [D, strip_eval_eq] using hp
  have hd : ∀ i, Disjoint (D.leftVars i) (D.rightVars i) := strip_disjoint C
  have hsz : D.size ≤ 6 := hc
  have h1 : (litSet D 1).card ≤ 1 := by
    simpa [castX] using litSet_card_le D hD hd hsz (0 : Fin 2)
  have h7 : (litSet D 7).card ≤ 1 := by
    simpa [castX] using litSet_card_le D hD hd hsz (1 : Fin 2)
  obtain ⟨g,b,hg1,hg7⟩ := pair_birth D hD hd hpD
  obtain ⟨f,_,hf⟩ := mis_cover D hD 27
  obtain ⟨l,hl,he⟩ := hf 1 (by decide +kernel)
  obtain ⟨r,hr,hj⟩ := hf 7 (by decide +kernel)
  have el : l = (g,b) := Finset.card_le_one.mp h1 l hl (g,b) hg1
  have er : r = (g,!b) := Finset.card_le_one.mp h7 r hr (g,!b) hg7
  rw [el] at he
  rw [er] at hj
  have hh := he.symm.trans hj
  simp only [Option.some.injEq] at hh
  cases b <;> simp at hh

end PEqualNP.Outside.L_meta_9811.AndSeven


namespace PEqualNP.Outside.L_meta_9811.AndSevenCompiler

open PEqualNP.CircuitLowerBounds

abbrev Rec (n : ℕ) := Finset (Fin n) × Finset ℕ × Finset (Fin n) × Finset ℕ
abbrev Form (n : ℕ) := Option (Finset (Fin n) × Finset ℕ)

def zeroF {n : ℕ} : Form n := some (∅, ∅)

def orF {n : ℕ} : List (Form n) → Form n
  | [] => some (∅, ∅)
  | f :: fs =>
    match f, orF fs with
    | none, _ => none
    | some _, none => none
    | some (a, b), some (c, d) => some (a ∪ c, b ∪ d)

structure St (n : ℕ) where
  fs : List (Form n)
  rs : List (Rec n)

def getF {n : ℕ} (s : St n) (i : ℕ) : Form n := s.fs.getD i zeroF

def andStep {n : ℕ} (s : St n) (fa fb : Form n) : St n :=
  match fa, fb with
  | none, f => ⟨s.fs ++ [f], s.rs⟩
  | some p, none => ⟨s.fs ++ [some p], s.rs⟩
  | some (va, ga), some (vb, gb) => ⟨s.fs ++ [some (∅, {s.rs.length})], s.rs ++ [(va, ga, vb, gb)]⟩

def step {n : ℕ} (s : St n) (g : Gate) : St n :=
  match g.op, g.inputs with
  | GateOp.or, ins => ⟨s.fs ++ [orF (ins.map (getF s))], s.rs⟩
  | GateOp.and, [] => ⟨s.fs ++ [none], s.rs⟩
  | GateOp.and, [a] => ⟨s.fs ++ [getF s a], s.rs⟩
  | GateOp.and, a :: b :: _ => andStep s (getF s a) (getF s b)
  | _, _ => ⟨s.fs ++ [zeroF], s.rs⟩

def sv {n : ℕ} (U : Finset (Fin n)) (vs : List Bool) (V : Finset (Fin n)) (G : Finset ℕ) : Bool :=
  decide (∃ v ∈ V, v ∈ U) || decide (∃ j ∈ G, vs.getD j false = true)

def rvStep {n : ℕ} (U : Finset (Fin n)) (vs : List Bool) (r : Rec n) : List Bool :=
  vs ++ [sv U vs r.1 r.2.1 && sv U vs r.2.2.1 r.2.2.2]

def rvals {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) : List Bool := rs.foldl (rvStep U) []

def fv {n : ℕ} (U : Finset (Fin n)) (vs : List Bool) : Form n → Bool
  | none => true
  | some p => sv U vs p.1 p.2

theorem fv_orF {n : ℕ} (U : Finset (Fin n)) (vs : List Bool) (fs : List (Form n)) :
    fv U vs (orF fs) = fs.any (fv U vs) := by
  induction fs with
  | nil => simp [orF, fv, sv]
  | cons f fs ih =>
    rcases f with _ | ⟨a, b⟩
    · simp [orF, fv]
    · rcases h : orF fs with _ | ⟨c, d⟩
      · rw [h] at ih
        simp only [orF, h, List.any_cons]
        rw [← ih]
        simp [fv]
      · rw [h] at ih
        simp only [orF, h, List.any_cons]
        rw [← ih]
        simp only [fv, sv, Finset.mem_union, or_and_right, exists_or, Bool.decide_or]
        ac_rfl

theorem rv_pre {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) :
    ∀ (vs : List Bool) (j : ℕ), j < vs.length → (rs.foldl (rvStep U) vs).getD j false = vs.getD j false := by
  induction rs with
  | nil => intro vs j _; rfl
  | cons r rs ih =>
    intro vs j hj
    simp only [List.foldl_cons]
    rw [ih _ j (by simp [rvStep]; omega)]
    simp [rvStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

theorem rv_len {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) :
    ∀ vs : List Bool, (rs.foldl (rvStep U) vs).length = vs.length + rs.length := by
  induction rs with
  | nil => intro vs; simp
  | cons r rs ih => intro vs; simp only [List.foldl_cons, ih]; simp [rvStep]; omega

theorem rvals_len {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) : (rvals U rs).length = rs.length := by
  simp [rvals, rv_len]

theorem rvals_snoc {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) (r : Rec n) :
    rvals U (rs ++ [r]) = rvStep U (rvals U rs) r := by
  simp [rvals, List.foldl_append]

theorem sv_congr {n : ℕ} (U : Finset (Fin n)) (vs vs' : List Bool) (V : Finset (Fin n)) (G : Finset ℕ)
    (h : ∀ j ∈ G, vs.getD j false = vs'.getD j false) : sv U vs V G = sv U vs' V G := by
  unfold sv
  congr 2
  apply propext
  constructor
  · rintro ⟨j, hj, hv⟩; exact ⟨j, hj, (h j hj) ▸ hv⟩
  · rintro ⟨j, hj, hv⟩; exact ⟨j, hj, (h j hj).symm ▸ hv⟩

def RefsLt {n : ℕ} (m : ℕ) (f : Form n) : Prop := ∀ p, f = some p → ∀ j ∈ p.2, j < m

def GoodRecs {n : ℕ} (rs : List (Rec n)) : Prop :=
  ∀ k (hk : k < rs.length), (∀ j ∈ rs[k].2.1, j < k) ∧ (∀ j ∈ rs[k].2.2.2, j < k)

theorem fv_snoc {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) (r : Rec n) (f : Form n)
    (hf : RefsLt rs.length f) : fv U (rvals U (rs ++ [r])) f = fv U (rvals U rs) f := by
  rcases f with _ | p
  · rfl
  · simp only [fv]
    apply sv_congr
    intro j hj
    have hjl := hf p rfl j hj
    rw [rvals_snoc]
    simp [rvStep, List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [rvals_len U]; exact hjl)]

theorem refs_orF {n : ℕ} (m : ℕ) (fs : List (Form n)) (h : ∀ f ∈ fs, RefsLt m f) : RefsLt m (orF fs) := by
  induction fs with
  | nil => intro p hp j hj; simp [orF] at hp; subst hp; simp at hj
  | cons f fs ih =>
    have ih' := ih (fun f' hf' => h f' (by simp [hf']))
    have hf := h f (by simp)
    intro p hp j hj
    rcases f with _ | ⟨a, b⟩
    · simp [orF] at hp
    · rcases hq : orF fs with _ | ⟨c, d⟩
      · simp [orF, hq] at hp
      · simp only [orF, hq, Option.some.injEq] at hp
        subst hp
        rcases Finset.mem_union.1 hj with hj | hj
        · exact hf _ rfl j hj
        · exact ih' _ hq j hj

theorem refs_getF {n : ℕ} (m : ℕ) (s : St n) (h : ∀ f ∈ s.fs, RefsLt m f) (i : ℕ) : RefsLt m (getF s i) := by
  unfold getF
  by_cases hi : i < s.fs.length
  · rw [List.getD_eq_getElem _ _ hi]; exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    intro p hp j hj
    simp [zeroF] at hp; subst hp; simp at hj

def Fw (W : List Bool) (g : Gate) : List Bool := W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]

def Inv {n : ℕ} (U : Finset (Fin n)) (W : List Bool) (s : St n) : Prop :=
  s.fs.length = W.length ∧ (∀ f ∈ s.fs, RefsLt s.rs.length f) ∧ GoodRecs s.rs ∧
    ∀ i, W.getD i false = fv U (rvals U s.rs) (getF s i)

theorem getF_push {n : ℕ} (fs : List (Form n)) (rs : List (Rec n)) (f : Form n) (i : ℕ) :
    getF ⟨fs ++ [f], rs⟩ i = if i < fs.length then fs.getD i zeroF else if i = fs.length then f else zeroF := by
  unfold getF
  split_ifs with h1 h2
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
  · subst h2; simp [List.getD_eq_getElem?_getD]
  · rw [List.getD_eq_default _ _ (by simp; omega)]

theorem fv_zero {n : ℕ} (U : Finset (Fin n)) (vs : List Bool) : fv U vs zeroF = false := by
  simp [fv, zeroF, sv]

theorem inv_push {n : ℕ} (U : Finset (Fin n)) (W : List Bool) (s : St n) (f : Form n) (x : Bool)
    (hI : Inv U W s) (hf : RefsLt s.rs.length f) (hx : x = fv U (rvals U s.rs) f) :
    Inv U (W ++ [x]) ⟨s.fs ++ [f], s.rs⟩ := by
  obtain ⟨hl, hr, hg, hv⟩ := hI
  refine ⟨by simp [hl], ?_, hg, ?_⟩
  · intro f' hf'
    rcases List.mem_append.1 hf' with h | h
    · exact hr f' h
    · simp at h; subst h; exact hf
  · intro i
    rw [getF_push]
    split_ifs with h1 h2
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
      have := hv i
      unfold getF at this
      exact this
    · subst h2; rw [hl]; simp [List.getD_eq_getElem?_getD, hx]
    · rw [List.getD_eq_default _ _ (by simp; omega), fv_zero]

theorem inv_rec {n : ℕ} (U : Finset (Fin n)) (W : List Bool) (s : St n) (r : Rec n) (x : Bool)
    (hI : Inv U W s) (h1 : ∀ j ∈ r.2.1, j < s.rs.length) (h2 : ∀ j ∈ r.2.2.2, j < s.rs.length)
    (hx : x = (sv U (rvals U s.rs) r.1 r.2.1 && sv U (rvals U s.rs) r.2.2.1 r.2.2.2)) :
    Inv U (W ++ [x]) ⟨s.fs ++ [some (∅, {s.rs.length})], s.rs ++ [r]⟩ := by
  obtain ⟨hl, hr, hg, hv⟩ := hI
  refine ⟨by simp [hl], ?_, ?_, ?_⟩
  · intro f' hf'
    simp only [List.length_append, List.length_cons, List.length_nil]
    rcases List.mem_append.1 hf' with h | h
    · intro p hp j hj; have := hr f' h p hp j hj; omega
    · simp at h; subst h; intro p hp j hj; simp at hp; subst hp; simp at hj; omega
  · intro k hk
    simp only [List.length_append, List.length_cons, List.length_nil] at hk
    by_cases hk' : k < s.rs.length
    · rw [List.getElem_append_left hk']; exact hg k hk'
    · have : k = s.rs.length := by omega
      subst this
      simp only [List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero]
      exact ⟨h1, h2⟩
  · intro i
    rw [getF_push]
    split_ifs with hi1 hi2
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
      have := hv i
      unfold getF at this
      rw [this, fv_snoc U s.rs r]
      have := hr _ (List.getElem_mem (by omega : i < s.fs.length))
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact this
    · subst hi2
      rw [hl]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self,
        List.getElem?_cons_zero, Option.getD_some]
      have hlen : (rvals U s.rs).length = s.rs.length := rvals_len U s.rs
      simp only [fv, sv, rvals_snoc, rvStep, Finset.mem_singleton, exists_eq_left]
      rw [List.getD_append_right _ _ _ _ (by omega), hlen, Nat.sub_self]
      simp [hx, sv]
    · rw [List.getD_eq_default _ _ (by simp; omega), fv_zero]

def Ok (g : Gate) : Prop := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

theorem step_inv {n : ℕ} (U : Finset (Fin n)) (W : List Bool) (s : St n) (g : Gate)
    (hI : Inv U W s) (hg : Ok g) : Inv U (Fw W g) (step s g) := by
  have hv := hI.2.2.2
  have hR : ∀ i, RefsLt s.rs.length (getF s i) := refs_getF s.rs.length s hI.2.1
  obtain ⟨hop, hlen⟩ := hg
  rcases g with ⟨op, ins⟩
  simp only at hop hlen
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · apply inv_push U W s none _ hI (by intro p hp; simp at hp)
      simp [GateOp.eval, fv]
    · apply inv_push U W s (getF s a) _ hI (hR a)
      have := hv a
      simp only [List.getD_eq_getElem?_getD] at this
      simp [Fw, GateOp.eval, this]
    · show Inv U (Fw W ⟨GateOp.and, [a, b]⟩) (andStep s (getF s a) (getF s b))
      have ea := hv a
      have eb := hv b
      rcases hfa : getF s a with _ | ⟨va, ga⟩ <;> rcases hfb : getF s b with _ | ⟨vb, gb⟩
      · apply inv_push U W s none _ hI (by intro p hp; simp at hp)
        rw [hfa] at ea; rw [hfb] at eb
        simp [Fw, GateOp.eval, fv] at ea eb ⊢; simp [ea, eb]
      · apply inv_push U W s (some (vb, gb)) _ hI (hfb ▸ hR b)
        rw [hfa] at ea; rw [hfb] at eb
        simp [GateOp.eval, fv] at ea eb ⊢; simp [ea, eb]
      · apply inv_push U W s (some (va, ga)) _ hI (hfa ▸ hR a)
        rw [hfa] at ea; rw [hfb] at eb
        simp [GateOp.eval, fv] at ea eb ⊢; simp [ea, eb]
      · have ha := hR a; rw [hfa] at ha
        have hb := hR b; rw [hfb] at hb
        apply inv_rec U W s (va, ga, vb, gb) _ hI (ha _ rfl) (hb _ rfl)
        rw [hfa] at ea; rw [hfb] at eb
        simp only [fv, List.getD_eq_getElem?_getD] at ea eb
        simp [Fw, GateOp.eval, ea, eb]
    · simp at hlen
  · apply inv_push U W s (orF (ins.map (getF s))) _ hI
      (refs_orF _ _ (fun f hf => by
        obtain ⟨i, _, rfl⟩ := List.mem_map.1 hf
        exact hR i))
    rw [fv_orF]
    simp only [GateOp.eval, List.any_map]
    congr 1
    funext i
    have := hv i
    simp only [List.getD_eq_getElem?_getD] at this
    simp [Function.comp, this]

theorem fold_inv {n : ℕ} (U : Finset (Fin n)) (gs : List Gate) (hgs : ∀ g ∈ gs, Ok g) :
    ∀ (W : List Bool) (s : St n), Inv U W s → Inv U (gs.foldl Fw W) (gs.foldl step s) := by
  induction gs with
  | nil => intro W s h; exact h
  | cons g gs ih =>
    intro W s h
    simp only [List.foldl_cons]
    exact ih (fun g' hg' => hgs g' (by simp [hg'])) _ _ (step_inv U W s g h (hgs g (by simp)))

def isAnd (g : Gate) : Bool := match g.op with
  | GateOp.and => true
  | _ => false

theorem isAnd_iff (g : Gate) : isAnd g = true ↔ g.op = GateOp.and := by
  unfold isAnd
  split <;> simp_all

theorem step_rs {n : ℕ} (s : St n) (g : Gate) :
    (step s g).rs.length ≤ s.rs.length + (if isAnd g = true then 1 else 0) := by
  rcases g with ⟨op, ins⟩
  cases op <;> simp only [step, isAnd] <;> try simp
  rcases ins with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> simp only [step]
  · simp
  · simp
  · unfold andStep
    split <;> simp

theorem fold_rs {n : ℕ} (gs : List Gate) :
    ∀ s : St n, (gs.foldl step s).rs.length ≤ s.rs.length + gs.countP isAnd := by
  induction gs with
  | nil => intro s; simp
  | cons g gs ih =>
    intro s
    simp only [List.foldl_cons, List.countP_cons]
    have h1 := ih (step s g)
    have h2 := step_rs s g
    split_ifs at h2 ⊢ <;> omega

theorem rvals_split {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) (k : ℕ) :
    rvals U rs = (rs.drop k).foldl (rvStep U) (rvals U (rs.take k)) := by
  unfold rvals
  rw [← List.foldl_append, List.take_append_drop]

theorem rvals_take {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) (k j : ℕ) (hj : j < k) (hk : k ≤ rs.length) :
    (rvals U rs).getD j false = (rvals U (rs.take k)).getD j false := by
  rw [rvals_split U rs k, rv_pre]
  rw [rvals_len, List.length_take]; omega

theorem rec_val {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) (hg : GoodRecs rs) (k : ℕ) (hk : k < rs.length) :
    (rvals U rs).getD k false = (sv U (rvals U rs) rs[k].1 rs[k].2.1 && sv U (rvals U rs) rs[k].2.2.1 rs[k].2.2.2) := by
  rw [rvals_take U rs (k + 1) k (by omega) (by omega)]
  rw [List.take_succ_eq_append_getElem hk, rvals_snoc]
  have hl : (rvals U (rs.take k)).length = k := by rw [rvals_len, List.length_take]; omega
  simp only [rvStep]
  rw [List.getD_append_right _ _ _ _ (by omega), hl, Nat.sub_self]
  simp only [List.getD_cons_zero]
  obtain ⟨h1, h2⟩ := hg k hk
  congr 1
  · apply sv_congr; intro j hj; exact (rvals_take U rs k j (h1 j hj) (by omega)).symm
  · apply sv_congr; intro j hj; exact (rvals_take U rs k j (h2 j hj) (by omega)).symm

def toACC {n : ℕ} (rs : List (Rec n)) (V : Finset (Fin n)) (G : Finset ℕ) : PEqualNP.AndCount.AndCountCircuit n where
  size := rs.length
  leftVars i := rs[i].1
  leftGates i := Finset.univ.filter (fun j : Fin rs.length => j.val ∈ rs[i].2.1)
  rightVars i := rs[i].2.2.1
  rightGates i := Finset.univ.filter (fun j : Fin rs.length => j.val ∈ rs[i].2.2.2)
  outVars := V
  outGates := Finset.univ.filter (fun j : Fin rs.length => j.val ∈ G)

theorem side_eq {n : ℕ} (U : Finset (Fin n)) (m : ℕ) (B : Finset (Fin n)) (G : Finset ℕ) (i : Fin m)
    (val : Fin m → Bool) (vs : List Bool) (hG : ∀ j ∈ G, j < i.val)
    (hval : ∀ j : Fin m, j < i → val j = vs.getD j false) :
    PEqualNP.AndCount.AndCountCircuit.sideTrue U B (Finset.univ.filter (fun j : Fin m => j.val ∈ G)) i val
      = sv U vs B G := by
  unfold PEqualNP.AndCount.AndCountCircuit.sideTrue sv
  rw [Bool.decide_or]
  congr 2
  apply propext
  constructor
  · rintro ⟨j, hj, hji, hv⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact ⟨j.val, hj, by rw [← hval j hji]; exact hv⟩
  · rintro ⟨j, hj, hv⟩
    have hji := hG j hj
    refine ⟨⟨j, by omega⟩, by simp [hj], hji, ?_⟩
    rw [hval ⟨j, by omega⟩ hji]
    exact hv

theorem fuel {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) (hg : GoodRecs rs) (V : Finset (Fin n)) (G : Finset ℕ) :
    ∀ d (i : Fin rs.length), i.val < d →
      (toACC rs V G).gateValFuel U d i = (rvals U rs).getD i false := by
  intro d
  induction d with
  | zero => intro i hi; omega
  | succ d ih =>
    intro i hi
    rw [rec_val U rs hg i i.isLt]
    obtain ⟨h1, h2⟩ := hg i i.isLt
    simp only [PEqualNP.AndCount.AndCountCircuit.gateValFuel]
    have hv : ∀ j : Fin rs.length, j < i → (toACC rs V G).gateValFuel U d j = (rvals U rs).getD j false :=
      fun j hj => ih j (by omega)
    congr 1
    · exact side_eq U rs.length _ _ i _ _ h1 hv
    · exact side_eq U rs.length _ _ i _ _ h2 hv

theorem eval_eq {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) (hg : GoodRecs rs) (V : Finset (Fin n)) (G : Finset ℕ)
    (hG : ∀ j ∈ G, j < rs.length) : (toACC rs V G).eval U = sv U (rvals U rs) V G := by
  unfold PEqualNP.AndCount.AndCountCircuit.eval sv
  rw [Bool.decide_or]
  congr 2
  apply propext
  constructor
  · rintro ⟨j, hj, hv⟩
    have hj' : j.val ∈ G := (Finset.mem_filter.1 hj).2
    refine ⟨j.val, hj', ?_⟩
    exact (fuel U rs hg V G rs.length j j.isLt).symm.trans hv
  · rintro ⟨j, hj, hv⟩
    refine ⟨⟨j, hG j hj⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩, ?_⟩
    exact (fuel U rs hg V G rs.length ⟨j, hG j hj⟩ (hG j hj)).trans hv

theorem wf {n : ℕ} (rs : List (Rec n)) (hg : GoodRecs rs) (V : Finset (Fin n)) (G : Finset ℕ) :
    (toACC rs V G).WellFormed := by
  intro i
  obtain ⟨h1, h2⟩ := hg i i.isLt
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · exact h1 j (Finset.mem_filter.1 hj).2
  · exact h2 j (Finset.mem_filter.1 hj).2

end PEqualNP.Outside.L_meta_9811.AndSevenCompiler

theorem PEqualNP.Outside.L_meta_9811.AndSevenCompiler : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∃ (x3 : Finset (Fin (14 : ℕ))), (PEqualNP.MetaComplexity.circuitFun (14 : ℕ) x1 fun (x4 : Fin (14 : ℕ)) => Decidable.decide (x4 ∈ x3)) = Bool.false) → ∃ (x4 : PEqualNP.AndCount.AndCountCircuit (14 : ℕ)), x4.WellFormed ∧ x4.size ≤ Nat.card { x5 : Fin x1.gates.length // (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and } ∧ ∀ (x5 : Finset (Fin (14 : ℕ))), x4.eval x5 = PEqualNP.MetaComplexity.circuitFun (14 : ℕ) x1 fun (x6 : Fin (14 : ℕ)) => Decidable.decide (x6 ∈ x5) := by
  intro C hmono hex
  obtain ⟨U0, hU0⟩ := hex
  have hok : ∀ g ∈ C.gates, PEqualNP.Outside.L_meta_9811.AndSevenCompiler.Ok g := by
    intro g hg
    obtain ⟨h1, h2⟩ := hmono g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    exact ⟨h1, h2⟩
  let s0 : PEqualNP.Outside.L_meta_9811.AndSevenCompiler.St 14 := ⟨List.ofFn (fun i : Fin 14 => some ({i}, ∅)), []⟩
  let s := C.gates.foldl PEqualNP.Outside.L_meta_9811.AndSevenCompiler.step s0
  have hinit : ∀ U : Finset (Fin 14), PEqualNP.Outside.L_meta_9811.AndSevenCompiler.Inv U (List.ofFn fun x : Fin 14 => decide (x ∈ U)) s0 := by
    intro U
    refine ⟨by simp [s0], ?_, ?_, ?_⟩
    · intro f hf p hp j hj
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hf
      simp only [Option.some.injEq] at hp
      subst hp
      simp at hj
    · intro k hk; simp [s0] at hk
    · intro i
      by_cases hi : i < 14
      · simp only [PEqualNP.Outside.L_meta_9811.AndSevenCompiler.getF, s0]
        rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn,
          List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]
        simp [PEqualNP.Outside.L_meta_9811.AndSevenCompiler.fv, PEqualNP.Outside.L_meta_9811.AndSevenCompiler.sv]
      · rw [List.getD_eq_default _ _ (by simp; omega)]
        simp only [PEqualNP.Outside.L_meta_9811.AndSevenCompiler.getF, s0]
        rw [List.getD_eq_default _ _ (by simp; omega), PEqualNP.Outside.L_meta_9811.AndSevenCompiler.fv_zero]
  have hinv : ∀ U : Finset (Fin 14), PEqualNP.Outside.L_meta_9811.AndSevenCompiler.Inv U (C.gates.foldl PEqualNP.Outside.L_meta_9811.AndSevenCompiler.Fw (List.ofFn fun x : Fin 14 => decide (x ∈ U))) s :=
    fun U => PEqualNP.Outside.L_meta_9811.AndSevenCompiler.fold_inv U C.gates hok _ _ (hinit U)
  have hfun : ∀ U : Finset (Fin 14), PEqualNP.MetaComplexity.circuitFun 14 C (fun x => decide (x ∈ U))
      = PEqualNP.Outside.L_meta_9811.AndSevenCompiler.fv U (PEqualNP.Outside.L_meta_9811.AndSevenCompiler.rvals U s.rs) (PEqualNP.Outside.L_meta_9811.AndSevenCompiler.getF s C.output) := fun U => (hinv U).2.2.2 C.output
  rcases hfo : PEqualNP.Outside.L_meta_9811.AndSevenCompiler.getF s C.output with _ | ⟨V, G⟩
  · have := hfun U0
    rw [hfo, hU0] at this
    simp [PEqualNP.Outside.L_meta_9811.AndSevenCompiler.fv] at this
  · have hG : ∀ j ∈ G, j < s.rs.length := PEqualNP.Outside.L_meta_9811.AndSevenCompiler.refs_getF _ s (hinv U0).2.1 C.output _ hfo
    have hgood := (hinv U0).2.2.1
    refine ⟨PEqualNP.Outside.L_meta_9811.AndSevenCompiler.toACC s.rs V G, PEqualNP.Outside.L_meta_9811.AndSevenCompiler.wf s.rs hgood V G, ?_, ?_⟩
    · have h1 := PEqualNP.Outside.L_meta_9811.AndSevenCompiler.fold_rs C.gates s0
      have h2 : C.gates.countP PEqualNP.Outside.L_meta_9811.AndSevenCompiler.isAnd = Nat.card {x5 : Fin C.gates.length // (C.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and} := by
        classical
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
        conv_lhs => rw [← List.ofFn_get C.gates]
        rw [List.countP_ofFn]
        congr 1
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, PEqualNP.Outside.L_meta_9811.AndSevenCompiler.isAnd_iff]
      change s.rs.length ≤ s0.rs.length + _ at h1
      have h0 : s0.rs.length = 0 := rfl
      show s.rs.length ≤ _
      omega
    · intro U
      rw [PEqualNP.Outside.L_meta_9811.AndSevenCompiler.eval_eq U s.rs hgood V G hG, hfun U, hfo]
      rfl
