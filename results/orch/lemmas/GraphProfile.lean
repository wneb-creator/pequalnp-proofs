import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9811.GraphProfile

abbrev V := Fin 14
abbrev E := Fin 19

def edge : E → V × V :=
  ![(0,8),(0,10),(1,7),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),
    (4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]

def incident (v : V) : Finset E :=
  Finset.univ.filter fun e => (edge e).1 = v ∨ (edge e).2 = v

def covered (S : Finset V) : Finset E := S.biUnion incident

def uncovered (S : Finset V) : Finset E := Finset.univ \ covered S

def cycle : Finset E := {0,2,6,8,10,15,17,1,3,5,7,11,13,16}

lemma degree : ∀ v : V, (incident v).card ≤ 3 := by decide +kernel
lemma cycle_degree : ∀ v : V, (incident v ∩ cycle).card = 2 := by decide +kernel
lemma cycle_size : cycle.card = 14 := by decide +kernel

lemma covered_le (S : Finset V) : (covered S).card ≤ 3 * S.card := by
  calc
    (covered S).card ≤ ∑ v ∈ S, (incident v).card := Finset.card_biUnion_le
    _ ≤ ∑ v ∈ S, 3 := Finset.sum_le_sum fun v _ => degree v
    _ = 3 * S.card := by simp [Nat.mul_comm]

lemma cycle_covered (S : Finset V) :
    covered S ∩ cycle = S.biUnion (fun v => incident v ∩ cycle) := by
  ext e
  simp only [covered, Finset.mem_inter, Finset.mem_biUnion]
  aesop

lemma cycle_covered_le (S : Finset V) : (covered S ∩ cycle).card ≤ 2 * S.card := by
  rw [cycle_covered]
  calc
    (S.biUnion fun v => incident v ∩ cycle).card ≤ ∑ v ∈ S, (incident v ∩ cycle).card := Finset.card_biUnion_le
    _ = 2 * S.card := by simp [cycle_degree, Nat.mul_comm]

lemma cover_profile (S : Finset V) :
    19 ≤ (uncovered S).card + 3 * S.card ∧
    14 ≤ (uncovered S).card + 2 * S.card := by
  have htotal := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (covered S))
  have hcycle := Finset.card_sdiff_add_card_inter cycle (covered S)
  have hsub : cycle \ covered S ⊆ uncovered S := by
    intro e he
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp he).2⟩
  have hle := Finset.card_le_card hsub
  have h1 := covered_le S
  have h2 := cycle_covered_le S
  simp only [Finset.card_univ, Fintype.card_fin] at htotal
  change (uncovered S).card + (covered S).card = 19 at htotal
  simp only [Finset.inter_comm cycle, cycle_size] at hcycle
  omega

lemma robust_cover (S : Finset V) :
    (S.card ≤ 6 → 2 ≤ (uncovered S).card) ∧
    (S.card ≤ 5 → 4 ≤ (uncovered S).card) ∧
    (S.card ≤ 4 → 7 ≤ (uncovered S).card) := by
  obtain ⟨h1,h2⟩ := cover_profile S
  omega


def profile : Fin 8 → Nat := ![19,16,13,10,7,4,2,0]

def centers : Fin 8 → Finset V :=
  ![∅,{2},{2,3},{2,3,4},{2,3,4,5},{2,3,4,5,6},{1,2,3,4,5,6},{0,1,2,3,4,5,6}]

lemma profile_witness : ∀ k : Fin 8,
    (centers k).card = k.val ∧ (uncovered (centers k)).card = profile k := by
  decide +kernel

lemma profile_lower (k : Fin 8) (S : Finset V) (hS : S.card = k.val) :
    profile k ≤ (uncovered S).card := by
  obtain ⟨h1,h2⟩ := cover_profile S
  fin_cases k <;> simp_all [profile]

lemma profile_exact (k : Fin 8) :
    (∀ S : Finset V, S.card = k.val → profile k ≤ (uncovered S).card) ∧
    ∃ S : Finset V, S.card = k.val ∧ (uncovered S).card = profile k :=
  ⟨fun S hS => profile_lower k S hS, centers k, profile_witness k⟩

def optimalSix : Finset (Finset V) :=
  {{0,2,3,4,5,6},{1,2,3,4,5,6},{7,8,10,11,12,13},{8,9,10,11,12,13}}

def optimalFive : Finset (Finset V) :=
  {{2,3,4,5,6},{8,10,11,12,13}}

def optimalSeven : Finset (Finset V) :=
  {{0,1,2,3,4,5,6},{7,8,9,10,11,12,13}}

def ofMask (m : Fin 16384) : Finset V :=
  Finset.univ.filter fun v => m.val.testBit v.val = true

def encodeList (L : List V) : Nat :=
  L.foldr (fun v a => 2 ^ v.val ||| a) 0

lemma encodeList_bit (L : List V) (v : V) :
    (encodeList L).testBit v.val = decide (v ∈ L) := by
  induction L with
  | nil => simp [encodeList]
  | cons w L ih =>
    change (2 ^ w.val ||| encodeList L).testBit v.val = _
    rw [Nat.testBit_or, Nat.testBit_two_pow, ih]
    simp [List.mem_cons, Fin.ext_iff, eq_comm]

noncomputable def toMask (S : Finset V) : Fin 16384 :=
  ⟨encodeList S.toList % 16384, Nat.mod_lt _ (by decide)⟩

lemma of_toMask (S : Finset V) : ofMask (toMask S) = S := by
  apply Finset.ext
  intro v
  rw [ofMask, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, toMask]
  change (encodeList S.toList % 2^14).testBit v.val = true ↔ v ∈ S
  rw [Nat.testBit_mod_two_pow, encodeList_bit]
  simp [v.isLt]

def mkMask (hi lo : Fin 128) : Fin 16384 :=
  ⟨hi.val * 128 + lo.val, by have := hi.isLt; have := lo.isLt; omega⟩

lemma splitMask (m : Fin 16384) : ∃ hi lo : Fin 128, mkMask hi lo = m := by
  refine ⟨⟨m.val / 128, by have := m.isLt; omega⟩,
    ⟨m.val % 128, Nat.mod_lt _ (by decide)⟩, ?_⟩
  apply Fin.ext
  simp only [mkMask]
  omega

def sixThree : Finset (Finset V) :=
  {{0,1,2,3,4,5},{0,1,2,3,4,6},{0,1,2,3,5,6},{0,1,2,4,5,6},{0,1,3,4,5,6},{0,2,3,5,6,13},{0,2,4,5,6,7},{0,3,4,5,6,13},{1,2,3,4,5,8},{1,2,3,4,6,10},{1,2,3,5,6,10},{1,3,4,5,6,8},{1,8,9,10,11,12},{1,8,10,11,12,13},{2,3,4,5,6,7},{2,3,4,5,6,8},{2,3,4,5,6,10},{2,3,4,5,6,13},{2,3,5,6,10,13},{3,4,5,6,8,13},{3,5,6,8,10,13},{3,5,8,10,11,13},{3,6,8,10,12,13},{3,8,9,10,11,13},{3,8,9,10,12,13},{3,8,10,11,12,13},{5,7,8,10,11,13},{5,7,8,11,12,13},{5,8,10,11,12,13},{6,7,8,10,12,13},{6,7,10,11,12,13},{6,8,10,11,12,13},{7,8,9,10,11,12},{7,8,9,10,11,13},{7,8,9,10,12,13},{7,8,9,11,12,13},{7,9,10,11,12,13}}

def classified (m : Fin 16384) : Prop :=
  let S := ofMask m
  ((S.card = 6 ∧ (uncovered S).card = 2) → S ∈ optimalSix) ∧
  ((S.card = 5 ∧ (uncovered S).card = 4) → S ∈ optimalFive) ∧
  ((S.card = 7 ∧ (uncovered S).card = 0) → S ∈ optimalSeven) ∧
  ((S.card = 6 ∧ (uncovered S).card = 3) → S ∈ sixThree)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row0 : ∀ lo : Fin 128, classified (mkMask 0 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row1 : ∀ lo : Fin 128, classified (mkMask 1 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row2 : ∀ lo : Fin 128, classified (mkMask 2 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row3 : ∀ lo : Fin 128, classified (mkMask 3 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row4 : ∀ lo : Fin 128, classified (mkMask 4 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row5 : ∀ lo : Fin 128, classified (mkMask 5 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row6 : ∀ lo : Fin 128, classified (mkMask 6 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row7 : ∀ lo : Fin 128, classified (mkMask 7 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row8 : ∀ lo : Fin 128, classified (mkMask 8 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row9 : ∀ lo : Fin 128, classified (mkMask 9 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row10 : ∀ lo : Fin 128, classified (mkMask 10 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row11 : ∀ lo : Fin 128, classified (mkMask 11 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row12 : ∀ lo : Fin 128, classified (mkMask 12 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row13 : ∀ lo : Fin 128, classified (mkMask 13 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row14 : ∀ lo : Fin 128, classified (mkMask 14 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row15 : ∀ lo : Fin 128, classified (mkMask 15 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row16 : ∀ lo : Fin 128, classified (mkMask 16 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row17 : ∀ lo : Fin 128, classified (mkMask 17 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row18 : ∀ lo : Fin 128, classified (mkMask 18 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row19 : ∀ lo : Fin 128, classified (mkMask 19 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row20 : ∀ lo : Fin 128, classified (mkMask 20 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row21 : ∀ lo : Fin 128, classified (mkMask 21 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row22 : ∀ lo : Fin 128, classified (mkMask 22 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row23 : ∀ lo : Fin 128, classified (mkMask 23 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row24 : ∀ lo : Fin 128, classified (mkMask 24 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row25 : ∀ lo : Fin 128, classified (mkMask 25 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row26 : ∀ lo : Fin 128, classified (mkMask 26 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row27 : ∀ lo : Fin 128, classified (mkMask 27 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row28 : ∀ lo : Fin 128, classified (mkMask 28 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row29 : ∀ lo : Fin 128, classified (mkMask 29 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row30 : ∀ lo : Fin 128, classified (mkMask 30 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row31 : ∀ lo : Fin 128, classified (mkMask 31 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row32 : ∀ lo : Fin 128, classified (mkMask 32 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row33 : ∀ lo : Fin 128, classified (mkMask 33 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row34 : ∀ lo : Fin 128, classified (mkMask 34 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row35 : ∀ lo : Fin 128, classified (mkMask 35 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row36 : ∀ lo : Fin 128, classified (mkMask 36 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row37 : ∀ lo : Fin 128, classified (mkMask 37 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row38 : ∀ lo : Fin 128, classified (mkMask 38 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row39 : ∀ lo : Fin 128, classified (mkMask 39 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row40 : ∀ lo : Fin 128, classified (mkMask 40 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row41 : ∀ lo : Fin 128, classified (mkMask 41 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row42 : ∀ lo : Fin 128, classified (mkMask 42 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row43 : ∀ lo : Fin 128, classified (mkMask 43 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row44 : ∀ lo : Fin 128, classified (mkMask 44 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row45 : ∀ lo : Fin 128, classified (mkMask 45 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row46 : ∀ lo : Fin 128, classified (mkMask 46 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row47 : ∀ lo : Fin 128, classified (mkMask 47 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row48 : ∀ lo : Fin 128, classified (mkMask 48 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row49 : ∀ lo : Fin 128, classified (mkMask 49 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row50 : ∀ lo : Fin 128, classified (mkMask 50 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row51 : ∀ lo : Fin 128, classified (mkMask 51 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row52 : ∀ lo : Fin 128, classified (mkMask 52 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row53 : ∀ lo : Fin 128, classified (mkMask 53 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row54 : ∀ lo : Fin 128, classified (mkMask 54 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row55 : ∀ lo : Fin 128, classified (mkMask 55 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row56 : ∀ lo : Fin 128, classified (mkMask 56 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row57 : ∀ lo : Fin 128, classified (mkMask 57 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row58 : ∀ lo : Fin 128, classified (mkMask 58 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row59 : ∀ lo : Fin 128, classified (mkMask 59 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row60 : ∀ lo : Fin 128, classified (mkMask 60 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row61 : ∀ lo : Fin 128, classified (mkMask 61 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row62 : ∀ lo : Fin 128, classified (mkMask 62 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row63 : ∀ lo : Fin 128, classified (mkMask 63 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row64 : ∀ lo : Fin 128, classified (mkMask 64 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row65 : ∀ lo : Fin 128, classified (mkMask 65 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row66 : ∀ lo : Fin 128, classified (mkMask 66 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row67 : ∀ lo : Fin 128, classified (mkMask 67 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row68 : ∀ lo : Fin 128, classified (mkMask 68 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row69 : ∀ lo : Fin 128, classified (mkMask 69 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row70 : ∀ lo : Fin 128, classified (mkMask 70 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row71 : ∀ lo : Fin 128, classified (mkMask 71 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row72 : ∀ lo : Fin 128, classified (mkMask 72 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row73 : ∀ lo : Fin 128, classified (mkMask 73 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row74 : ∀ lo : Fin 128, classified (mkMask 74 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row75 : ∀ lo : Fin 128, classified (mkMask 75 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row76 : ∀ lo : Fin 128, classified (mkMask 76 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row77 : ∀ lo : Fin 128, classified (mkMask 77 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row78 : ∀ lo : Fin 128, classified (mkMask 78 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row79 : ∀ lo : Fin 128, classified (mkMask 79 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row80 : ∀ lo : Fin 128, classified (mkMask 80 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row81 : ∀ lo : Fin 128, classified (mkMask 81 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row82 : ∀ lo : Fin 128, classified (mkMask 82 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row83 : ∀ lo : Fin 128, classified (mkMask 83 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row84 : ∀ lo : Fin 128, classified (mkMask 84 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row85 : ∀ lo : Fin 128, classified (mkMask 85 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row86 : ∀ lo : Fin 128, classified (mkMask 86 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row87 : ∀ lo : Fin 128, classified (mkMask 87 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row88 : ∀ lo : Fin 128, classified (mkMask 88 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row89 : ∀ lo : Fin 128, classified (mkMask 89 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row90 : ∀ lo : Fin 128, classified (mkMask 90 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row91 : ∀ lo : Fin 128, classified (mkMask 91 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row92 : ∀ lo : Fin 128, classified (mkMask 92 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row93 : ∀ lo : Fin 128, classified (mkMask 93 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row94 : ∀ lo : Fin 128, classified (mkMask 94 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row95 : ∀ lo : Fin 128, classified (mkMask 95 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row96 : ∀ lo : Fin 128, classified (mkMask 96 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row97 : ∀ lo : Fin 128, classified (mkMask 97 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row98 : ∀ lo : Fin 128, classified (mkMask 98 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row99 : ∀ lo : Fin 128, classified (mkMask 99 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row100 : ∀ lo : Fin 128, classified (mkMask 100 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row101 : ∀ lo : Fin 128, classified (mkMask 101 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row102 : ∀ lo : Fin 128, classified (mkMask 102 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row103 : ∀ lo : Fin 128, classified (mkMask 103 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row104 : ∀ lo : Fin 128, classified (mkMask 104 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row105 : ∀ lo : Fin 128, classified (mkMask 105 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row106 : ∀ lo : Fin 128, classified (mkMask 106 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row107 : ∀ lo : Fin 128, classified (mkMask 107 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row108 : ∀ lo : Fin 128, classified (mkMask 108 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row109 : ∀ lo : Fin 128, classified (mkMask 109 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row110 : ∀ lo : Fin 128, classified (mkMask 110 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row111 : ∀ lo : Fin 128, classified (mkMask 111 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row112 : ∀ lo : Fin 128, classified (mkMask 112 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row113 : ∀ lo : Fin 128, classified (mkMask 113 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row114 : ∀ lo : Fin 128, classified (mkMask 114 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row115 : ∀ lo : Fin 128, classified (mkMask 115 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row116 : ∀ lo : Fin 128, classified (mkMask 116 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row117 : ∀ lo : Fin 128, classified (mkMask 117 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row118 : ∀ lo : Fin 128, classified (mkMask 118 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row119 : ∀ lo : Fin 128, classified (mkMask 119 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row120 : ∀ lo : Fin 128, classified (mkMask 120 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row121 : ∀ lo : Fin 128, classified (mkMask 121 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row122 : ∀ lo : Fin 128, classified (mkMask 122 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row123 : ∀ lo : Fin 128, classified (mkMask 123 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row124 : ∀ lo : Fin 128, classified (mkMask 124 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row125 : ∀ lo : Fin 128, classified (mkMask 125 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row126 : ∀ lo : Fin 128, classified (mkMask 126 lo) := by
  unfold classified
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma row127 : ∀ lo : Fin 128, classified (mkMask 127 lo) := by
  unfold classified
  decide +kernel

lemma classified_all (m : Fin 16384) : classified m := by
  obtain ⟨hi,lo,rfl⟩ := splitMask m
  fin_cases hi
  · exact row0 lo
  · exact row1 lo
  · exact row2 lo
  · exact row3 lo
  · exact row4 lo
  · exact row5 lo
  · exact row6 lo
  · exact row7 lo
  · exact row8 lo
  · exact row9 lo
  · exact row10 lo
  · exact row11 lo
  · exact row12 lo
  · exact row13 lo
  · exact row14 lo
  · exact row15 lo
  · exact row16 lo
  · exact row17 lo
  · exact row18 lo
  · exact row19 lo
  · exact row20 lo
  · exact row21 lo
  · exact row22 lo
  · exact row23 lo
  · exact row24 lo
  · exact row25 lo
  · exact row26 lo
  · exact row27 lo
  · exact row28 lo
  · exact row29 lo
  · exact row30 lo
  · exact row31 lo
  · exact row32 lo
  · exact row33 lo
  · exact row34 lo
  · exact row35 lo
  · exact row36 lo
  · exact row37 lo
  · exact row38 lo
  · exact row39 lo
  · exact row40 lo
  · exact row41 lo
  · exact row42 lo
  · exact row43 lo
  · exact row44 lo
  · exact row45 lo
  · exact row46 lo
  · exact row47 lo
  · exact row48 lo
  · exact row49 lo
  · exact row50 lo
  · exact row51 lo
  · exact row52 lo
  · exact row53 lo
  · exact row54 lo
  · exact row55 lo
  · exact row56 lo
  · exact row57 lo
  · exact row58 lo
  · exact row59 lo
  · exact row60 lo
  · exact row61 lo
  · exact row62 lo
  · exact row63 lo
  · exact row64 lo
  · exact row65 lo
  · exact row66 lo
  · exact row67 lo
  · exact row68 lo
  · exact row69 lo
  · exact row70 lo
  · exact row71 lo
  · exact row72 lo
  · exact row73 lo
  · exact row74 lo
  · exact row75 lo
  · exact row76 lo
  · exact row77 lo
  · exact row78 lo
  · exact row79 lo
  · exact row80 lo
  · exact row81 lo
  · exact row82 lo
  · exact row83 lo
  · exact row84 lo
  · exact row85 lo
  · exact row86 lo
  · exact row87 lo
  · exact row88 lo
  · exact row89 lo
  · exact row90 lo
  · exact row91 lo
  · exact row92 lo
  · exact row93 lo
  · exact row94 lo
  · exact row95 lo
  · exact row96 lo
  · exact row97 lo
  · exact row98 lo
  · exact row99 lo
  · exact row100 lo
  · exact row101 lo
  · exact row102 lo
  · exact row103 lo
  · exact row104 lo
  · exact row105 lo
  · exact row106 lo
  · exact row107 lo
  · exact row108 lo
  · exact row109 lo
  · exact row110 lo
  · exact row111 lo
  · exact row112 lo
  · exact row113 lo
  · exact row114 lo
  · exact row115 lo
  · exact row116 lo
  · exact row117 lo
  · exact row118 lo
  · exact row119 lo
  · exact row120 lo
  · exact row121 lo
  · exact row122 lo
  · exact row123 lo
  · exact row124 lo
  · exact row125 lo
  · exact row126 lo
  · exact row127 lo

lemma six_two_iff (S : Finset V) :
    (S.card = 6 ∧ (uncovered S).card = 2) ↔ S ∈ optimalSix := by
  constructor
  · intro h
    have hc := classified_all (toMask S)
    dsimp only [classified] at hc
    rw [of_toMask] at hc
    exact hc.1 h
  · intro h
    simp only [optimalSix, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl | rfl | rfl <;> decide +kernel

lemma five_four_iff (S : Finset V) :
    (S.card = 5 ∧ (uncovered S).card = 4) ↔ S ∈ optimalFive := by
  constructor
  · intro h
    have hc := classified_all (toMask S)
    dsimp only [classified] at hc
    rw [of_toMask] at hc
    exact hc.2.1 h
  · intro h
    simp only [optimalFive, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl <;> decide +kernel

lemma seven_zero_iff (S : Finset V) :
    (S.card = 7 ∧ (uncovered S).card = 0) ↔ S ∈ optimalSeven := by
  constructor
  · intro h
    have hc := classified_all (toMask S)
    dsimp only [classified] at hc
    rw [of_toMask] at hc
    exact hc.2.2.1 h
  · intro h
    simp only [optimalSeven, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl <;> decide +kernel

lemma six_three_iff (S : Finset V) :
    (S.card = 6 ∧ (uncovered S).card = 3) ↔ S ∈ sixThree := by
  constructor
  · intro h
    have hc := classified_all (toMask S)
    dsimp only [classified] at hc
    rw [of_toMask] at hc
    exact hc.2.2.2 h
  · intro h
    simp only [sixThree, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

lemma six_two_star (S : Finset V) (hS : S.card = 6) (hu : (uncovered S).card = 2) :
    ∃ v ∈ ({0,1,7,9} : Finset V), v ∉ S ∧ uncovered S = incident v := by
  have hs := (six_two_iff S).mp ⟨hS,hu⟩
  simp only [optimalSix, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl <;> decide +kernel

lemma remove_one_preserves_cover_floor (D : Finset E) (hD : D.card ≤ 1)
    (S : Finset V) (hcover : Finset.univ \ D ⊆ covered S) : 7 ≤ S.card := by
  have hsub : uncovered S ⊆ D := by
    intro e he
    by_contra hn
    have hc := hcover (Finset.mem_sdiff.mpr ⟨Finset.mem_univ e,hn⟩)
    exact (Finset.mem_sdiff.mp he).2 hc
  have hc := Finset.card_le_card hsub
  obtain ⟨h1,h2⟩ := cover_profile S
  omega

lemma sixThree_size : sixThree.card = 37 := by decide +kernel
lemma optimalSix_size : optimalSix.card = 4 := by decide +kernel
lemma optimalFive_size : optimalFive.card = 2 := by decide +kernel
lemma optimalSeven_size : optimalSeven.card = 2 := by decide +kernel

end PEqualNP.Outside.L_meta_9811.GraphProfile
