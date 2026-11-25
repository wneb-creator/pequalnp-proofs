import PEqualNP.Defs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
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


theorem q5_singleton_0_0 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 0,q5_mask 0,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_0_1 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 0,q5_mask 1,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_0_2 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 0,q5_mask 2,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_0_3 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 0,q5_mask 3,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_0_4 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 0,q5_mask 4,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_0_5 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 0,q5_mask 5,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_0_6 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 0,q5_mask 6,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_0_7 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 0,q5_mask 7,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_1_0 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 1,q5_mask 0,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_1_1 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 1,q5_mask 1,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_1_2 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 1,q5_mask 2,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_1_3 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 1,q5_mask 3,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_1_4 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 1,q5_mask 4,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_1_5 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 1,q5_mask 5,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_1_6 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 1,q5_mask 6,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_1_7 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 1,q5_mask 7,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_2_0 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 2,q5_mask 0,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_2_1 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 2,q5_mask 1,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_2_2 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 2,q5_mask 2,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_2_3 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 2,q5_mask 3,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_2_4 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 2,q5_mask 4,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_2_5 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 2,q5_mask 5,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_2_6 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 2,q5_mask 6,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_2_7 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 2,q5_mask 7,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_3_0 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 3,q5_mask 0,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_3_1 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 3,q5_mask 1,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_3_2 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 3,q5_mask 2,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_3_3 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 3,q5_mask 3,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_3_4 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 3,q5_mask 4,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_3_5 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 3,q5_mask 5,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_3_6 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 3,q5_mask 6,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_3_7 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 3,q5_mask 7,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_4_0 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 4,q5_mask 0,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_4_1 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 4,q5_mask 1,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_4_2 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 4,q5_mask 2,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_4_3 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 4,q5_mask 3,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_4_4 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 4,q5_mask 4,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_4_5 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 4,q5_mask 5,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_4_6 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 4,q5_mask 6,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_4_7 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 4,q5_mask 7,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_5_0 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 5,q5_mask 0,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_5_1 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 5,q5_mask 1,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_5_2 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 5,q5_mask 2,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_5_3 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 5,q5_mask 3,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_5_4 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 5,q5_mask 4,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_5_5 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 5,q5_mask 5,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_5_6 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 5,q5_mask 6,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_5_7 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 5,q5_mask 7,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_6_0 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 6,q5_mask 0,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_6_1 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 6,q5_mask 1,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_6_2 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 6,q5_mask 2,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_6_3 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 6,q5_mask 3,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_6_4 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 6,q5_mask 4,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_6_5 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 6,q5_mask 5,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_6_6 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 6,q5_mask 6,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_6_7 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 6,q5_mask 7,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_7_0 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 7,q5_mask 0,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_7_1 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 7,q5_mask 1,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_7_2 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 7,q5_mask 2,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_7_3 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 7,q5_mask 3,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_7_4 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 7,q5_mask 4,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_7_5 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 7,q5_mask 5,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_7_6 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 7,q5_mask 6,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_7_7 : ∀ c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask 7,q5_mask 7,q5_mask c,q5_mask d,q5_mask e] := by
  decide +kernel

theorem q5_singleton_certificate : ∀ a b c d e : Fin 8,
    ¬ q5_constraints ![q5_mask 1,q5_mask a,q5_mask b,q5_mask c,q5_mask d,q5_mask e] := by
  intro a b
  fin_cases a

  · fin_cases b

    · exact q5_singleton_0_0

    · exact q5_singleton_0_1

    · exact q5_singleton_0_2

    · exact q5_singleton_0_3

    · exact q5_singleton_0_4

    · exact q5_singleton_0_5

    · exact q5_singleton_0_6

    · exact q5_singleton_0_7

  · fin_cases b

    · exact q5_singleton_1_0

    · exact q5_singleton_1_1

    · exact q5_singleton_1_2

    · exact q5_singleton_1_3

    · exact q5_singleton_1_4

    · exact q5_singleton_1_5

    · exact q5_singleton_1_6

    · exact q5_singleton_1_7

  · fin_cases b

    · exact q5_singleton_2_0

    · exact q5_singleton_2_1

    · exact q5_singleton_2_2

    · exact q5_singleton_2_3

    · exact q5_singleton_2_4

    · exact q5_singleton_2_5

    · exact q5_singleton_2_6

    · exact q5_singleton_2_7

  · fin_cases b

    · exact q5_singleton_3_0

    · exact q5_singleton_3_1

    · exact q5_singleton_3_2

    · exact q5_singleton_3_3

    · exact q5_singleton_3_4

    · exact q5_singleton_3_5

    · exact q5_singleton_3_6

    · exact q5_singleton_3_7

  · fin_cases b

    · exact q5_singleton_4_0

    · exact q5_singleton_4_1

    · exact q5_singleton_4_2

    · exact q5_singleton_4_3

    · exact q5_singleton_4_4

    · exact q5_singleton_4_5

    · exact q5_singleton_4_6

    · exact q5_singleton_4_7

  · fin_cases b

    · exact q5_singleton_5_0

    · exact q5_singleton_5_1

    · exact q5_singleton_5_2

    · exact q5_singleton_5_3

    · exact q5_singleton_5_4

    · exact q5_singleton_5_5

    · exact q5_singleton_5_6

    · exact q5_singleton_5_7

  · fin_cases b

    · exact q5_singleton_6_0

    · exact q5_singleton_6_1

    · exact q5_singleton_6_2

    · exact q5_singleton_6_3

    · exact q5_singleton_6_4

    · exact q5_singleton_6_5

    · exact q5_singleton_6_6

    · exact q5_singleton_6_7

  · fin_cases b

    · exact q5_singleton_7_0

    · exact q5_singleton_7_1

    · exact q5_singleton_7_2

    · exact q5_singleton_7_3

    · exact q5_singleton_7_4

    · exact q5_singleton_7_5

    · exact q5_singleton_7_6

    · exact q5_singleton_7_7

theorem q5_pair_0_0 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 0,q5_mask 0,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_0_1 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 0,q5_mask 1,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_0_2 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 0,q5_mask 2,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_0_3 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 0,q5_mask 3,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_0_4 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 0,q5_mask 4,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_0_5 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 0,q5_mask 5,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_0_6 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 0,q5_mask 6,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_0_7 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 0,q5_mask 7,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_1_0 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 1,q5_mask 0,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_1_1 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 1,q5_mask 1,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_1_2 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 1,q5_mask 2,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_1_3 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 1,q5_mask 3,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_1_4 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 1,q5_mask 4,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_1_5 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 1,q5_mask 5,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_1_6 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 1,q5_mask 6,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_1_7 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 1,q5_mask 7,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_2_0 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 2,q5_mask 0,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_2_1 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 2,q5_mask 1,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_2_2 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 2,q5_mask 2,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_2_3 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 2,q5_mask 3,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_2_4 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 2,q5_mask 4,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_2_5 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 2,q5_mask 5,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_2_6 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 2,q5_mask 6,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_2_7 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 2,q5_mask 7,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_3_0 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 3,q5_mask 0,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_3_1 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 3,q5_mask 1,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_3_2 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 3,q5_mask 2,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_3_3 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 3,q5_mask 3,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_3_4 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 3,q5_mask 4,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_3_5 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 3,q5_mask 5,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_3_6 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 3,q5_mask 6,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_3_7 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 3,q5_mask 7,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_4_0 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 4,q5_mask 0,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_4_1 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 4,q5_mask 1,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_4_2 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 4,q5_mask 2,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_4_3 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 4,q5_mask 3,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_4_4 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 4,q5_mask 4,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_4_5 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 4,q5_mask 5,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_4_6 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 4,q5_mask 6,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_4_7 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 4,q5_mask 7,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_5_0 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 5,q5_mask 0,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_5_1 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 5,q5_mask 1,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_5_2 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 5,q5_mask 2,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_5_3 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 5,q5_mask 3,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_5_4 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 5,q5_mask 4,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_5_5 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 5,q5_mask 5,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_5_6 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 5,q5_mask 6,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_5_7 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 5,q5_mask 7,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_6_0 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 6,q5_mask 0,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_6_1 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 6,q5_mask 1,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_6_2 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 6,q5_mask 2,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_6_3 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 6,q5_mask 3,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_6_4 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 6,q5_mask 4,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_6_5 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 6,q5_mask 5,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_6_6 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 6,q5_mask 6,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_6_7 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 6,q5_mask 7,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_7_0 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 7,q5_mask 0,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_7_1 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 7,q5_mask 1,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_7_2 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 7,q5_mask 2,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_7_3 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 7,q5_mask 3,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_7_4 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 7,q5_mask 4,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_7_5 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 7,q5_mask 5,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_7_6 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 7,q5_mask 6,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_7_7 : ∀ c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask 7,q5_mask 7,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  decide +kernel

theorem q5_pair_certificate : ∀ a b c d e : Fin 8,
    q5_constraints ![q5_mask 3,q5_mask a,q5_mask b,q5_mask c,q5_mask d,q5_mask e] → e = 7 := by
  intro a b
  fin_cases a

  · fin_cases b

    · exact q5_pair_0_0

    · exact q5_pair_0_1

    · exact q5_pair_0_2

    · exact q5_pair_0_3

    · exact q5_pair_0_4

    · exact q5_pair_0_5

    · exact q5_pair_0_6

    · exact q5_pair_0_7

  · fin_cases b

    · exact q5_pair_1_0

    · exact q5_pair_1_1

    · exact q5_pair_1_2

    · exact q5_pair_1_3

    · exact q5_pair_1_4

    · exact q5_pair_1_5

    · exact q5_pair_1_6

    · exact q5_pair_1_7

  · fin_cases b

    · exact q5_pair_2_0

    · exact q5_pair_2_1

    · exact q5_pair_2_2

    · exact q5_pair_2_3

    · exact q5_pair_2_4

    · exact q5_pair_2_5

    · exact q5_pair_2_6

    · exact q5_pair_2_7

  · fin_cases b

    · exact q5_pair_3_0

    · exact q5_pair_3_1

    · exact q5_pair_3_2

    · exact q5_pair_3_3

    · exact q5_pair_3_4

    · exact q5_pair_3_5

    · exact q5_pair_3_6

    · exact q5_pair_3_7

  · fin_cases b

    · exact q5_pair_4_0

    · exact q5_pair_4_1

    · exact q5_pair_4_2

    · exact q5_pair_4_3

    · exact q5_pair_4_4

    · exact q5_pair_4_5

    · exact q5_pair_4_6

    · exact q5_pair_4_7

  · fin_cases b

    · exact q5_pair_5_0

    · exact q5_pair_5_1

    · exact q5_pair_5_2

    · exact q5_pair_5_3

    · exact q5_pair_5_4

    · exact q5_pair_5_5

    · exact q5_pair_5_6

    · exact q5_pair_5_7

  · fin_cases b

    · exact q5_pair_6_0

    · exact q5_pair_6_1

    · exact q5_pair_6_2

    · exact q5_pair_6_3

    · exact q5_pair_6_4

    · exact q5_pair_6_5

    · exact q5_pair_6_6

    · exact q5_pair_6_7

  · fin_cases b

    · exact q5_pair_7_0

    · exact q5_pair_7_1

    · exact q5_pair_7_2

    · exact q5_pair_7_3

    · exact q5_pair_7_4

    · exact q5_pair_7_5

    · exact q5_pair_7_6

    · exact q5_pair_7_7

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
