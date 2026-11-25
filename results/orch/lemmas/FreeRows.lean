import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2602_aux.FreeRows

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

lemma sideTrue_congr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
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

lemma gateValFuel_indep {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
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

lemma gateVal_unfold {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n))
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

def Free {n : Nat} (C : AndCountCircuit n) (S : Finset (Fin n)) : Finset (Fin C.size) :=
  Finset.univ.filter (fun i => ∀ v ∈ S, v ∉ C.leftVars i ∧ v ∉ C.rightVars i)

def sideL {n : Nat} (C : AndCountCircuit n) (I : Finset (Fin n)) (i : Fin C.size) : Bool :=
  sideTrue I (C.leftVars i) (C.leftGates i) i (C.gateVal I)

def sideR {n : Nat} (C : AndCountCircuit n) (I : Finset (Fin n)) (i : Fin C.size) : Bool :=
  sideTrue I (C.rightVars i) (C.rightGates i) i (C.gateVal I)

theorem unionSide {n : Nat} (C : AndCountCircuit n) (U I J B : Finset (Fin n))
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

theorem mergeInput {n : Nat} (C : AndCountCircuit n) (I J U S : Finset (Fin n))
    (hi : S ⊆ I) (hj : S ⊆ J) (hU : U ⊆ I ∪ J)
    (hs : ∀ i ∈ Free C S, sideL C I i = sideL C J i) :
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
      by_cases hf : i ∈ Free C S
      · have hh := hs i hf
        have hlj : sideL C J i = true := by
          rcases hl with hl | hl
          · exact hh.symm.trans hl
          · exact hl
        have hli : sideL C I i = true := hh.trans hlj
        rcases hr with hr | hr
        · exact Or.inl ⟨hli, hr⟩
        · exact Or.inr ⟨hlj, hr⟩
      · have hnot : ¬ (∀ v ∈ S, v ∉ C.leftVars i ∧ v ∉ C.rightVars i) := by
          simpa [Free] using hf
        push Not at hnot
        rcases hnot with ⟨v, hv, himp⟩
        by_cases h1 : v ∈ C.leftVars i
        · have a : sideL C I i = true := decide_eq_true (Or.inl ⟨v, h1, hi hv⟩)
          have b : sideL C J i = true := decide_eq_true (Or.inl ⟨v, h1, hj hv⟩)
          rcases hr with hr | hr
          · exact Or.inl ⟨a, hr⟩
          · exact Or.inr ⟨b, hr⟩
        · have h2 := himp h1
          have a : sideR C I i = true := decide_eq_true (Or.inl ⟨v, h2, hi hv⟩)
          have b : sideR C J i = true := decide_eq_true (Or.inl ⟨v, h2, hj hv⟩)
          rcases hl with hl | hl
          · exact Or.inl ⟨hl, a⟩
          · exact Or.inr ⟨hl, b⟩
  simp only [eval, decide_eq_true_eq]
  rintro (⟨w, hw, h⟩ | ⟨i, hi', h⟩)
  · rcases Finset.mem_union.mp (hU h) with h | h
    · exact Or.inl (Or.inl ⟨_, hw, h⟩)
    · exact Or.inr (Or.inl ⟨_, hw, h⟩)
  · rcases gate i h with h | h
    · exact Or.inl (Or.inr ⟨i, hi', h⟩)
    · exact Or.inr (Or.inr ⟨i, hi', h⟩)

theorem row_bound {n : Nat} {α : Type} [Fintype α] (C : AndCountCircuit n)
    (rows : α → Finset (Fin n)) (S : Finset (Fin n))
    (distinct : Function.Injective rows) (contains : ∀ a, S ⊆ rows a)
    (separates : ∀ a, C.eval (rows a) = false ∧
      ∀ v, v ∉ rows a → C.eval (insert v (rows a)) = true) :
    Fintype.card α ≤ 2 ^ (Free C S).card := by
  let code (a : α) (i : ↥(Free C S)) := sideL C (rows a) i
  have hinj : Function.Injective code := by
    intro a b hab
    apply distinct
    apply Finset.ext
    intro v
    constructor
    · intro hva
      by_contra hvb
      have he := mergeInput C (rows a) (rows b) (insert v (rows b)) S
        (contains a) (contains b)
        (Finset.insert_subset (Finset.mem_union_left _ hva) Finset.subset_union_right)
        (fun i hi => congrFun hab ⟨i, hi⟩) ((separates b).2 v hvb)
      simp [(separates a).1, (separates b).1] at he
    · intro hvb
      by_contra hva
      have he := mergeInput C (rows b) (rows a) (insert v (rows a)) S
        (contains b) (contains a)
        (Finset.insert_subset (Finset.mem_union_left _ hvb) Finset.subset_union_right)
        (fun i hi => (congrFun hab ⟨i, hi⟩).symm) ((separates a).2 v hva)
      simp [(separates a).1, (separates b).1] at he
  have hc := Fintype.card_le_of_injective _ hinj
  simpa only [Fintype.card_fun, Fintype.card_bool,
    Fintype.card_coe] using hc

end PEqualNP.Outside.L_meta_2602_aux.FreeRows
