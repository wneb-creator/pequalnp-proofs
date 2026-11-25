import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6659_aux

def q5_mask (m : Fin 8) : Finset (Fin 3) :=
  ![∅,{0},{1},{0,1},{2},{0,2},{1,2},{0,1,2}] m

def q5_neighbors (i : Fin 5) : Finset (Fin 6) :=
  ![{0,1,2},{0,5},{1,4,5},{0,3,4},{2,3,5}] i

def q5_forced (r : Fin 6 → Finset (Fin 3)) (i : Fin 5) : Finset (Fin 6) :=
  Finset.univ.filter (fun t => ∃ x ∈ q5_neighbors i, r x ⊆ r t)

abbrev q5_constraints (r : Fin 6 → Finset (Fin 3)) : Prop :=
  (∀ t, (r t).Nonempty) ∧
  (∀ i ∈ ({0,1,3} : Finset (Fin 5)),
    (∃ x ∈ q5_neighbors i, x ≠ 0 ∧ (r x).card = 1) → q5_forced r i ⊆ q5_neighbors i) ∧
  ∀ t, (Finset.univ.filter (fun i => t ∈ q5_forced r i)).card +
    (if 0 < t.val ∧ t.val < 5 then 1 else 0) ≤ 2 + (r t).card


def compactMaskSubset (a b : Fin 8) : Bool :=
  ![![true,true,true,true,true,true,true,true],
    ![false,true,false,true,false,true,false,true],
    ![false,false,true,true,false,false,true,true],
    ![false,false,false,true,false,false,false,true],
    ![false,false,false,false,true,true,true,true],
    ![false,false,false,false,false,true,false,true],
    ![false,false,false,false,false,false,true,true],
    ![false,false,false,false,false,false,false,true]] a b

def compactMaskCard (a : Fin 8) : ℕ := ![0,1,1,2,1,2,2,3] a

lemma compactMaskSubset_correct : ∀ a b : Fin 8,
    compactMaskSubset a b = true ↔ q5_mask a ⊆ q5_mask b := by decide +kernel

lemma compactMaskCard_correct : ∀ a : Fin 8, compactMaskCard a = (q5_mask a).card := by
  decide +kernel

lemma compactMaskNonempty_correct : ∀ a : Fin 8, a ≠ 0 ↔ (q5_mask a).Nonempty := by
  decide +kernel

lemma compactFilterCardFive : ∀ f : Fin 5 → Bool,
    (Finset.univ.filter (fun i => f i = true)).card =
      (f 0).toNat + (f 1).toNat + (f 2).toNat + (f 3).toNat + (f 4).toNat := by
  decide +kernel

lemma compactForallSix (P : Fin 6 → Prop) :
    (∀ i, P i) ↔ P 0 ∧ P 1 ∧ P 2 ∧ P 3 ∧ P 4 ∧ P 5 := by
  constructor
  · intro h; exact ⟨h 0,h 1,h 2,h 3,h 4,h 5⟩
  · rintro ⟨h0,h1,h2,h3,h4,h5⟩ i
    fin_cases i <;> assumption

def q5_compactForced (r : Fin 6 → Fin 8) (i : Fin 5) (t : Fin 6) : Bool :=
  ![compactMaskSubset (r 0) (r t) || compactMaskSubset (r 1) (r t) || compactMaskSubset (r 2) (r t),
    compactMaskSubset (r 0) (r t) || compactMaskSubset (r 5) (r t),
    compactMaskSubset (r 1) (r t) || compactMaskSubset (r 4) (r t) || compactMaskSubset (r 5) (r t),
    compactMaskSubset (r 0) (r t) || compactMaskSubset (r 3) (r t) || compactMaskSubset (r 4) (r t),
    compactMaskSubset (r 2) (r t) || compactMaskSubset (r 3) (r t) || compactMaskSubset (r 5) (r t)] i

lemma q5_compactForced_correct (r : Fin 6 → Fin 8) (i : Fin 5) (t : Fin 6) :
    q5_compactForced r i t = true ↔ t ∈ q5_forced (fun x => q5_mask (r x)) i := by
  fin_cases i <;>
    simp [q5_compactForced,q5_forced,q5_neighbors,compactMaskSubset_correct,or_assoc]

def q5_compactCount (r : Fin 6 → Fin 8) (t : Fin 6) : ℕ :=
  (q5_compactForced r 0 t).toNat + (q5_compactForced r 1 t).toNat +
  (q5_compactForced r 2 t).toNat + (q5_compactForced r 3 t).toNat +
  (q5_compactForced r 4 t).toNat

lemma q5_compactCount_correct (r : Fin 6 → Fin 8) (t : Fin 6) :
    q5_compactCount r t =
      (Finset.univ.filter (fun i => t ∈ q5_forced (fun x => q5_mask (r x)) i)).card := by
  have eq : Finset.univ.filter (fun i => t ∈ q5_forced (fun x => q5_mask (r x)) i) =
      Finset.univ.filter (fun i => q5_compactForced r i t = true) := by
    ext i
    simp [q5_compactForced_correct]
  rw [eq,compactFilterCardFive]
  rfl

def q5_compact (r : Fin 6 → Fin 8) : Bool :=
  decide (r 0 ≠ 0) && decide (r 1 ≠ 0) && decide (r 2 ≠ 0) &&
  decide (r 3 ≠ 0) && decide (r 4 ≠ 0) && decide (r 5 ≠ 0) &&
  (!(decide (compactMaskCard (r 1) = 1) || decide (compactMaskCard (r 2) = 1)) ||
    (!q5_compactForced r 0 3 && !q5_compactForced r 0 4 && !q5_compactForced r 0 5)) &&
  (!decide (compactMaskCard (r 5) = 1) ||
    (!q5_compactForced r 1 1 && !q5_compactForced r 1 2 &&
      !q5_compactForced r 1 3 && !q5_compactForced r 1 4)) &&
  (!(decide (compactMaskCard (r 3) = 1) || decide (compactMaskCard (r 4) = 1)) ||
    (!q5_compactForced r 3 1 && !q5_compactForced r 3 2 && !q5_compactForced r 3 5)) &&
  decide (q5_compactCount r 0 ≤ 2+compactMaskCard (r 0)) &&
  decide (q5_compactCount r 1+1 ≤ 2+compactMaskCard (r 1)) &&
  decide (q5_compactCount r 2+1 ≤ 2+compactMaskCard (r 2)) &&
  decide (q5_compactCount r 3+1 ≤ 2+compactMaskCard (r 3)) &&
  decide (q5_compactCount r 4+1 ≤ 2+compactMaskCard (r 4)) &&
  decide (q5_compactCount r 5 ≤ 2+compactMaskCard (r 5))

lemma compactBoolImp (a b : Bool) (h : a = true → b = true) : !a || b = true := by
  cases a <;> simp_all

lemma q5_compact_of_constraints (r : Fin 6 → Fin 8)
    (hc : q5_constraints (fun t => q5_mask (r t))) : q5_compact r = true := by
  have hn : ∀ t, r t ≠ 0 := fun t => (compactMaskNonempty_correct _).mpr (hc.1 t)
  have hb (t : Fin 6) : q5_compactCount r t +
      (if 0 < t.val ∧ t.val < 5 then 1 else 0) ≤ 2 + compactMaskCard (r t) := by
    rw [q5_compactCount_correct,compactMaskCard_correct]
    exact hc.2.2 t
  have outside (i : Fin 5) (hi : i ∈ ({0,1,3} : Finset (Fin 5)))
      (hs : ∃ x ∈ q5_neighbors i, x ≠ 0 ∧ compactMaskCard (r x) = 1)
      (t : Fin 6) (ht : t ∉ q5_neighbors i) : q5_compactForced r i t = false := by
    have hs' : ∃ x ∈ q5_neighbors i, x ≠ 0 ∧ (q5_mask (r x)).card = 1 := by
      simpa only [compactMaskCard_correct] using hs
    cases eq : q5_compactForced r i t with
    | false => rfl
    | true => exact False.elim (ht (hc.2.1 i hi hs' ((q5_compactForced_correct r i t).mp eq)))
  have h0 : !(decide (compactMaskCard (r 1) = 1) || decide (compactMaskCard (r 2) = 1)) ||
      (!q5_compactForced r 0 3 && !q5_compactForced r 0 4 && !q5_compactForced r 0 5) = true := by
    apply compactBoolImp
    intro ht
    have hs : ∃ x ∈ q5_neighbors 0, x ≠ 0 ∧ compactMaskCard (r x) = 1 := by
      simp only [Bool.or_eq_true,decide_eq_true_eq] at ht
      rcases ht with h | h
      · exact ⟨1,by decide,by decide,h⟩
      · exact ⟨2,by decide,by decide,h⟩
    rw [outside 0 (by decide) hs 3 (by decide),outside 0 (by decide) hs 4 (by decide),
      outside 0 (by decide) hs 5 (by decide)]
    rfl
  have h1 : !decide (compactMaskCard (r 5) = 1) ||
      (!q5_compactForced r 1 1 && !q5_compactForced r 1 2 &&
        !q5_compactForced r 1 3 && !q5_compactForced r 1 4) = true := by
    apply compactBoolImp
    intro ht
    have hs : ∃ x ∈ q5_neighbors 1, x ≠ 0 ∧ compactMaskCard (r x) = 1 :=
      ⟨5,by decide,by decide,of_decide_eq_true ht⟩
    rw [outside 1 (by decide) hs 1 (by decide),outside 1 (by decide) hs 2 (by decide),
      outside 1 (by decide) hs 3 (by decide),outside 1 (by decide) hs 4 (by decide)]
    rfl
  have h3 : !(decide (compactMaskCard (r 3) = 1) || decide (compactMaskCard (r 4) = 1)) ||
      (!q5_compactForced r 3 1 && !q5_compactForced r 3 2 && !q5_compactForced r 3 5) = true := by
    apply compactBoolImp
    intro ht
    have hs : ∃ x ∈ q5_neighbors 3, x ≠ 0 ∧ compactMaskCard (r x) = 1 := by
      simp only [Bool.or_eq_true,decide_eq_true_eq] at ht
      rcases ht with h | h
      · exact ⟨3,by decide,by decide,h⟩
      · exact ⟨4,by decide,by decide,h⟩
    rw [outside 3 (by decide) hs 1 (by decide),outside 3 (by decide) hs 2 (by decide),
      outside 3 (by decide) hs 5 (by decide)]
    rfl
  have b0 := hb 0
  have b1 := hb 1
  have b2 := hb 2
  have b3 := hb 3
  have b4 := hb 4
  have b5 := hb 5
  simp only [Fin.val_zero,Fin.val_one] at b0 b1
  norm_num at b0 b1 b2 b3 b4 b5
  simp only [q5_compact,h0,h1,h3,Bool.and_true,Bool.and_eq_true,decide_eq_true_eq]
  aesop

end PEqualNP.Outside.L_meta_6659_aux
