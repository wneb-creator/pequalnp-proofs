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

