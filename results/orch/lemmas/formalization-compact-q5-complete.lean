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


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_0_0 : ∀ c d e : Fin 8, q5_compact ![1,0,0,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_0_1 : ∀ c d e : Fin 8, q5_compact ![1,0,1,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_0_2 : ∀ c d e : Fin 8, q5_compact ![1,0,2,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_0_3 : ∀ c d e : Fin 8, q5_compact ![1,0,3,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_0_4 : ∀ c d e : Fin 8, q5_compact ![1,0,4,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_0_5 : ∀ c d e : Fin 8, q5_compact ![1,0,5,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_0_6 : ∀ c d e : Fin 8, q5_compact ![1,0,6,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_0_7 : ∀ c d e : Fin 8, q5_compact ![1,0,7,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_1_0 : ∀ c d e : Fin 8, q5_compact ![1,1,0,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_1_1 : ∀ c d e : Fin 8, q5_compact ![1,1,1,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_1_2 : ∀ c d e : Fin 8, q5_compact ![1,1,2,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_1_3 : ∀ c d e : Fin 8, q5_compact ![1,1,3,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_1_4 : ∀ c d e : Fin 8, q5_compact ![1,1,4,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_1_5 : ∀ c d e : Fin 8, q5_compact ![1,1,5,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_1_6 : ∀ c d e : Fin 8, q5_compact ![1,1,6,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_1_7 : ∀ c d e : Fin 8, q5_compact ![1,1,7,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_2_0 : ∀ c d e : Fin 8, q5_compact ![1,2,0,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_2_1 : ∀ c d e : Fin 8, q5_compact ![1,2,1,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_2_2 : ∀ c d e : Fin 8, q5_compact ![1,2,2,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_2_3 : ∀ c d e : Fin 8, q5_compact ![1,2,3,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_2_4 : ∀ c d e : Fin 8, q5_compact ![1,2,4,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_2_5 : ∀ c d e : Fin 8, q5_compact ![1,2,5,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_2_6 : ∀ c d e : Fin 8, q5_compact ![1,2,6,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_2_7 : ∀ c d e : Fin 8, q5_compact ![1,2,7,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_3_0 : ∀ c d e : Fin 8, q5_compact ![1,3,0,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_3_1 : ∀ c d e : Fin 8, q5_compact ![1,3,1,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_3_2 : ∀ c d e : Fin 8, q5_compact ![1,3,2,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_3_3 : ∀ c d e : Fin 8, q5_compact ![1,3,3,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_3_4 : ∀ c d e : Fin 8, q5_compact ![1,3,4,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_3_5 : ∀ c d e : Fin 8, q5_compact ![1,3,5,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_3_6 : ∀ c d e : Fin 8, q5_compact ![1,3,6,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_3_7 : ∀ c d e : Fin 8, q5_compact ![1,3,7,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_4_0 : ∀ c d e : Fin 8, q5_compact ![1,4,0,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_4_1 : ∀ c d e : Fin 8, q5_compact ![1,4,1,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_4_2 : ∀ c d e : Fin 8, q5_compact ![1,4,2,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_4_3 : ∀ c d e : Fin 8, q5_compact ![1,4,3,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_4_4 : ∀ c d e : Fin 8, q5_compact ![1,4,4,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_4_5 : ∀ c d e : Fin 8, q5_compact ![1,4,5,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_4_6 : ∀ c d e : Fin 8, q5_compact ![1,4,6,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_4_7 : ∀ c d e : Fin 8, q5_compact ![1,4,7,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_5_0 : ∀ c d e : Fin 8, q5_compact ![1,5,0,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_5_1 : ∀ c d e : Fin 8, q5_compact ![1,5,1,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_5_2 : ∀ c d e : Fin 8, q5_compact ![1,5,2,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_5_3 : ∀ c d e : Fin 8, q5_compact ![1,5,3,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_5_4 : ∀ c d e : Fin 8, q5_compact ![1,5,4,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_5_5 : ∀ c d e : Fin 8, q5_compact ![1,5,5,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_5_6 : ∀ c d e : Fin 8, q5_compact ![1,5,6,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_5_7 : ∀ c d e : Fin 8, q5_compact ![1,5,7,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_6_0 : ∀ c d e : Fin 8, q5_compact ![1,6,0,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_6_1 : ∀ c d e : Fin 8, q5_compact ![1,6,1,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_6_2 : ∀ c d e : Fin 8, q5_compact ![1,6,2,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_6_3 : ∀ c d e : Fin 8, q5_compact ![1,6,3,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_6_4 : ∀ c d e : Fin 8, q5_compact ![1,6,4,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_6_5 : ∀ c d e : Fin 8, q5_compact ![1,6,5,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_6_6 : ∀ c d e : Fin 8, q5_compact ![1,6,6,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_6_7 : ∀ c d e : Fin 8, q5_compact ![1,6,7,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_7_0 : ∀ c d e : Fin 8, q5_compact ![1,7,0,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_7_1 : ∀ c d e : Fin 8, q5_compact ![1,7,1,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_7_2 : ∀ c d e : Fin 8, q5_compact ![1,7,2,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_7_3 : ∀ c d e : Fin 8, q5_compact ![1,7,3,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_7_4 : ∀ c d e : Fin 8, q5_compact ![1,7,4,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_7_5 : ∀ c d e : Fin 8, q5_compact ![1,7,5,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_7_6 : ∀ c d e : Fin 8, q5_compact ![1,7,6,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_single_7_7 : ∀ c d e : Fin 8, q5_compact ![1,7,7,c,d,e] = false := by
  decide +kernel

theorem q5_compact_single_certificate (a b c d e : Fin 8) :
    q5_compact ![1,a,b,c,d,e] = false := by
  fin_cases a <;> fin_cases b
  · exact q5_compact_single_0_0 c d e
  · exact q5_compact_single_0_1 c d e
  · exact q5_compact_single_0_2 c d e
  · exact q5_compact_single_0_3 c d e
  · exact q5_compact_single_0_4 c d e
  · exact q5_compact_single_0_5 c d e
  · exact q5_compact_single_0_6 c d e
  · exact q5_compact_single_0_7 c d e
  · exact q5_compact_single_1_0 c d e
  · exact q5_compact_single_1_1 c d e
  · exact q5_compact_single_1_2 c d e
  · exact q5_compact_single_1_3 c d e
  · exact q5_compact_single_1_4 c d e
  · exact q5_compact_single_1_5 c d e
  · exact q5_compact_single_1_6 c d e
  · exact q5_compact_single_1_7 c d e
  · exact q5_compact_single_2_0 c d e
  · exact q5_compact_single_2_1 c d e
  · exact q5_compact_single_2_2 c d e
  · exact q5_compact_single_2_3 c d e
  · exact q5_compact_single_2_4 c d e
  · exact q5_compact_single_2_5 c d e
  · exact q5_compact_single_2_6 c d e
  · exact q5_compact_single_2_7 c d e
  · exact q5_compact_single_3_0 c d e
  · exact q5_compact_single_3_1 c d e
  · exact q5_compact_single_3_2 c d e
  · exact q5_compact_single_3_3 c d e
  · exact q5_compact_single_3_4 c d e
  · exact q5_compact_single_3_5 c d e
  · exact q5_compact_single_3_6 c d e
  · exact q5_compact_single_3_7 c d e
  · exact q5_compact_single_4_0 c d e
  · exact q5_compact_single_4_1 c d e
  · exact q5_compact_single_4_2 c d e
  · exact q5_compact_single_4_3 c d e
  · exact q5_compact_single_4_4 c d e
  · exact q5_compact_single_4_5 c d e
  · exact q5_compact_single_4_6 c d e
  · exact q5_compact_single_4_7 c d e
  · exact q5_compact_single_5_0 c d e
  · exact q5_compact_single_5_1 c d e
  · exact q5_compact_single_5_2 c d e
  · exact q5_compact_single_5_3 c d e
  · exact q5_compact_single_5_4 c d e
  · exact q5_compact_single_5_5 c d e
  · exact q5_compact_single_5_6 c d e
  · exact q5_compact_single_5_7 c d e
  · exact q5_compact_single_6_0 c d e
  · exact q5_compact_single_6_1 c d e
  · exact q5_compact_single_6_2 c d e
  · exact q5_compact_single_6_3 c d e
  · exact q5_compact_single_6_4 c d e
  · exact q5_compact_single_6_5 c d e
  · exact q5_compact_single_6_6 c d e
  · exact q5_compact_single_6_7 c d e
  · exact q5_compact_single_7_0 c d e
  · exact q5_compact_single_7_1 c d e
  · exact q5_compact_single_7_2 c d e
  · exact q5_compact_single_7_3 c d e
  · exact q5_compact_single_7_4 c d e
  · exact q5_compact_single_7_5 c d e
  · exact q5_compact_single_7_6 c d e
  · exact q5_compact_single_7_7 c d e

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_0_0 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,0,0,c,d,e] = false := by
  intro c d e; exact Or.inr rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_0_1 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,0,1,c,d,e] = false := by
  intro c d e; exact Or.inr rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_0_2 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,0,2,c,d,e] = false := by
  intro c d e; exact Or.inr rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_0_3 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,0,3,c,d,e] = false := by
  intro c d e; exact Or.inr rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_0_4 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,0,4,c,d,e] = false := by
  intro c d e; exact Or.inr rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_0_5 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,0,5,c,d,e] = false := by
  intro c d e; exact Or.inr rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_0_6 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,0,6,c,d,e] = false := by
  intro c d e; exact Or.inr rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_0_7 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,0,7,c,d,e] = false := by
  intro c d e; exact Or.inr rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_1_0 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,1,0,c,d,e] = false := by
  intro c d e; exact Or.inr rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_1_1 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,1,1,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_1_2 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,1,2,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_1_3 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,1,3,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_1_4 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,1,4,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_1_5 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,1,5,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_1_6 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,1,6,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_1_7 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,1,7,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_2_0 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,2,0,c,d,e] = false := by
  intro c d e; exact Or.inr rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_2_1 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,2,1,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_2_2 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,2,2,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_2_3 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,2,3,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_2_4 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,2,4,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_2_5 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,2,5,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_2_6 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,2,6,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_2_7 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,2,7,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_3_0 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,3,0,c,d,e] = false := by
  intro c d e; exact Or.inr rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_3_1 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,3,1,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_3_2 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,3,2,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_3_3 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,3,3,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_3_4 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,3,4,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_3_5 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,3,5,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_3_6 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,3,6,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_3_7 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,3,7,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_4_0 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,4,0,c,d,e] = false := by
  intro c d e; exact Or.inr rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_4_1 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,4,1,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_4_2 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,4,2,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_4_3 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,4,3,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_4_4 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,4,4,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_4_5 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,4,5,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_4_6 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,4,6,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_4_7 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,4,7,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_5_0 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,5,0,c,d,e] = false := by
  intro c d e; exact Or.inr rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_5_1 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,5,1,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_5_2 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,5,2,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_5_3 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,5,3,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_5_4 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,5,4,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_5_5 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,5,5,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_5_6 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,5,6,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_5_7 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,5,7,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_6_0 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,6,0,c,d,e] = false := by
  intro c d e; exact Or.inr rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_6_1 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,6,1,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_6_2 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,6,2,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_6_3 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,6,3,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_6_4 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,6,4,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_6_5 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,6,5,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_6_6 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,6,6,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_6_7 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,6,7,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_7_0 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,7,0,c,d,e] = false := by
  intro c d e; exact Or.inr rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_7_1 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,7,1,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_7_2 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,7,2,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_7_3 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,7,3,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_7_4 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,7,4,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_7_5 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,7,5,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_7_6 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,7,6,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5_compact_pair_7_7 : ∀ c d e : Fin 8, e = 7 ∨ q5_compact ![3,7,7,c,d,e] = false := by
  decide +kernel

theorem q5_compact_pair_certificate (a b c d e : Fin 8) :
    e = 7 ∨ q5_compact ![3,a,b,c,d,e] = false := by
  fin_cases a <;> fin_cases b
  · exact q5_compact_pair_0_0 c d e
  · exact q5_compact_pair_0_1 c d e
  · exact q5_compact_pair_0_2 c d e
  · exact q5_compact_pair_0_3 c d e
  · exact q5_compact_pair_0_4 c d e
  · exact q5_compact_pair_0_5 c d e
  · exact q5_compact_pair_0_6 c d e
  · exact q5_compact_pair_0_7 c d e
  · exact q5_compact_pair_1_0 c d e
  · exact q5_compact_pair_1_1 c d e
  · exact q5_compact_pair_1_2 c d e
  · exact q5_compact_pair_1_3 c d e
  · exact q5_compact_pair_1_4 c d e
  · exact q5_compact_pair_1_5 c d e
  · exact q5_compact_pair_1_6 c d e
  · exact q5_compact_pair_1_7 c d e
  · exact q5_compact_pair_2_0 c d e
  · exact q5_compact_pair_2_1 c d e
  · exact q5_compact_pair_2_2 c d e
  · exact q5_compact_pair_2_3 c d e
  · exact q5_compact_pair_2_4 c d e
  · exact q5_compact_pair_2_5 c d e
  · exact q5_compact_pair_2_6 c d e
  · exact q5_compact_pair_2_7 c d e
  · exact q5_compact_pair_3_0 c d e
  · exact q5_compact_pair_3_1 c d e
  · exact q5_compact_pair_3_2 c d e
  · exact q5_compact_pair_3_3 c d e
  · exact q5_compact_pair_3_4 c d e
  · exact q5_compact_pair_3_5 c d e
  · exact q5_compact_pair_3_6 c d e
  · exact q5_compact_pair_3_7 c d e
  · exact q5_compact_pair_4_0 c d e
  · exact q5_compact_pair_4_1 c d e
  · exact q5_compact_pair_4_2 c d e
  · exact q5_compact_pair_4_3 c d e
  · exact q5_compact_pair_4_4 c d e
  · exact q5_compact_pair_4_5 c d e
  · exact q5_compact_pair_4_6 c d e
  · exact q5_compact_pair_4_7 c d e
  · exact q5_compact_pair_5_0 c d e
  · exact q5_compact_pair_5_1 c d e
  · exact q5_compact_pair_5_2 c d e
  · exact q5_compact_pair_5_3 c d e
  · exact q5_compact_pair_5_4 c d e
  · exact q5_compact_pair_5_5 c d e
  · exact q5_compact_pair_5_6 c d e
  · exact q5_compact_pair_5_7 c d e
  · exact q5_compact_pair_6_0 c d e
  · exact q5_compact_pair_6_1 c d e
  · exact q5_compact_pair_6_2 c d e
  · exact q5_compact_pair_6_3 c d e
  · exact q5_compact_pair_6_4 c d e
  · exact q5_compact_pair_6_5 c d e
  · exact q5_compact_pair_6_6 c d e
  · exact q5_compact_pair_6_7 c d e
  · exact q5_compact_pair_7_0 c d e
  · exact q5_compact_pair_7_1 c d e
  · exact q5_compact_pair_7_2 c d e
  · exact q5_compact_pair_7_3 c d e
  · exact q5_compact_pair_7_4 c d e
  · exact q5_compact_pair_7_5 c d e
  · exact q5_compact_pair_7_6 c d e
  · exact q5_compact_pair_7_7 c d e

lemma q5_compact_map (a b c d e f : Fin 8) :
    (fun t => q5_mask (![a,b,c,d,e,f] t)) =
      ![q5_mask a,q5_mask b,q5_mask c,q5_mask d,q5_mask e,q5_mask f] := by
  funext t
  fin_cases t <;> rfl

theorem q5_singleton_certificate (a b c d e : Fin 8) :
    ¬ q5_constraints ![q5_mask 1,q5_mask a,q5_mask b,q5_mask c,q5_mask d,q5_mask e] := by
  intro hc
  have yes := q5_compact_of_constraints ![1,a,b,c,d,e] (by rw [q5_compact_map]; exact hc)
  rw [q5_compact_single_certificate] at yes
  exact Bool.noConfusion yes

theorem q5_pair_certificate (a b c d e : Fin 8)
    (hc : q5_constraints ![q5_mask 3,q5_mask a,q5_mask b,q5_mask c,q5_mask d,q5_mask e]) : e = 7 := by
  rcases q5_compact_pair_certificate a b c d e with he | hn
  · exact he
  · have yes := q5_compact_of_constraints ![3,a,b,c,d,e] (by rw [q5_compact_map]; exact hc)
    rw [hn] at yes
    exact Bool.noConfusion yes

theorem q5_mask_surjective : ∀ s : Finset (Fin 3), ∃ m : Fin 8, q5_mask m = s := by
  decide +kernel


theorem q5_singleton_impossible {r : Fin 6 → Finset (Fin 3)}
    (hr : r 0 = {0}) (hc : q5_constraints r) : False := by
  obtain ⟨a,ha⟩ := q5_mask_surjective (r 1)
  obtain ⟨b,hb⟩ := q5_mask_surjective (r 2)
  obtain ⟨c,hc'⟩ := q5_mask_surjective (r 3)
  obtain ⟨d,hd⟩ := q5_mask_surjective (r 4)
  obtain ⟨e,he⟩ := q5_mask_surjective (r 5)
  have eq : ![q5_mask 1,q5_mask a,q5_mask b,q5_mask c,q5_mask d,q5_mask e] = r := by
    funext t
    fin_cases t <;> simp [q5_mask,hr,← ha,← hb,← hc',← hd,← he]
  exact q5_singleton_certificate a b c d e (by simpa only [eq] using hc)

theorem q5_pair_full {r : Fin 6 → Finset (Fin 3)}
    (hr : r 0 = {0,1}) (hc : q5_constraints r) : r 5 = Finset.univ := by
  obtain ⟨a,ha⟩ := q5_mask_surjective (r 1)
  obtain ⟨b,hb⟩ := q5_mask_surjective (r 2)
  obtain ⟨c,hc'⟩ := q5_mask_surjective (r 3)
  obtain ⟨d,hd⟩ := q5_mask_surjective (r 4)
  obtain ⟨e,he⟩ := q5_mask_surjective (r 5)
  have eq : ![q5_mask 3,q5_mask a,q5_mask b,q5_mask c,q5_mask d,q5_mask e] = r := by
    funext t
    fin_cases t <;> simp [q5_mask,hr,← ha,← hb,← hc',← hd,← he]
  have seven := q5_pair_certificate a b c d e (by simpa only [eq] using hc)
  subst e
  rw [← he]
  decide +kernel

end PEqualNP.Outside.L_meta_6659_aux
