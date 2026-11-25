import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6659_aux

def p10_mask (m : Fin 4) : Finset (Fin 2) := ![∅, {0}, {1}, {0, 1}] m

def p10_nb (i : Fin 4) : Finset (Fin 7) :=
  ![{0, 1, 3}, {0, 2, 6}, {1, 5, 6}, {0, 4, 5}] i

def p10_nonempty_subset (a b : Fin 4) : Bool :=
  ![![false, false, false, false],
    ![false, true, false, true],
    ![false, false, true, true],
    ![false, false, false, true]] a b

def p10_adj (i : Fin 4) (t : Fin 7) : Bool :=
  ![![true, true, false, true, false, false, false],
    ![true, false, true, false, false, false, true],
    ![false, true, false, false, false, true, true],
    ![true, false, false, false, true, true, false]] i t

def p10_force (r : Fin 7 → Fin 4) (i : Fin 4) (t : Fin 7) : Bool :=
  p10_adj i t ||
    ![p10_nonempty_subset (r 0) (r t) || p10_nonempty_subset (r 1) (r t) ||
        p10_nonempty_subset (r 3) (r t),
      p10_nonempty_subset (r 0) (r t) || p10_nonempty_subset (r 2) (r t) ||
        p10_nonempty_subset (r 6) (r t),
      p10_nonempty_subset (r 1) (r t) || p10_nonempty_subset (r 5) (r t) ||
        p10_nonempty_subset (r 6) (r t),
      p10_nonempty_subset (r 0) (r t) || p10_nonempty_subset (r 4) (r t) ||
        p10_nonempty_subset (r 5) (r t)] i

def p10_card (m : Fin 4) : Nat := ![0, 1, 1, 2] m

def p10_count (r : Fin 7 → Fin 4) (t : Fin 7) : Nat :=
  (p10_force r 0 t).toNat + (p10_force r 1 t).toNat +
    (p10_force r 2 t).toNat + (p10_force r 3 t).toNat +
    if t = 0 then 0 else 1

def p10_budget (r : Fin 7 → Fin 4) (t : Fin 7) : Bool :=
  decide (p10_count r t ≤ 2 + p10_card (r t))

def p10_constraintsB (r : Fin 7 → Fin 4) : Bool :=
  p10_budget r 0 && p10_budget r 1 && p10_budget r 2 && p10_budget r 3 &&
    p10_budget r 4 && p10_budget r 5 && p10_budget r 6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_0_0_0 : ∀ d e f g : Fin 4,
    p10_constraintsB ![0, 0, 0, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_0_0_1 : ∀ d e f g : Fin 4,
    p10_constraintsB ![0, 0, 1, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_0_0_2 : ∀ d e f g : Fin 4,
    p10_constraintsB ![0, 0, 2, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_0_0_3 : ∀ d e f g : Fin 4,
    p10_constraintsB ![0, 0, 3, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_0_1_0 : ∀ d e f g : Fin 4,
    p10_constraintsB ![0, 1, 0, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_0_1_1 : ∀ d e f g : Fin 4,
    p10_constraintsB ![0, 1, 1, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_0_1_2 : ∀ d e f g : Fin 4,
    p10_constraintsB ![0, 1, 2, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_0_1_3 : ∀ d e f g : Fin 4,
    p10_constraintsB ![0, 1, 3, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_0_2_0 : ∀ d e f g : Fin 4,
    p10_constraintsB ![0, 2, 0, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_0_2_1 : ∀ d e f g : Fin 4,
    p10_constraintsB ![0, 2, 1, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_0_2_2 : ∀ d e f g : Fin 4,
    p10_constraintsB ![0, 2, 2, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_0_2_3 : ∀ d e f g : Fin 4,
    p10_constraintsB ![0, 2, 3, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_0_3_0 : ∀ d e f g : Fin 4,
    p10_constraintsB ![0, 3, 0, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_0_3_1 : ∀ d e f g : Fin 4,
    p10_constraintsB ![0, 3, 1, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_0_3_2 : ∀ d e f g : Fin 4,
    p10_constraintsB ![0, 3, 2, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_0_3_3 : ∀ d e f g : Fin 4,
    p10_constraintsB ![0, 3, 3, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_1_0_0 : ∀ d e f g : Fin 4,
    p10_constraintsB ![1, 0, 0, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_1_0_1 : ∀ d e f g : Fin 4,
    p10_constraintsB ![1, 0, 1, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_1_0_2 : ∀ d e f g : Fin 4,
    p10_constraintsB ![1, 0, 2, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_1_0_3 : ∀ d e f g : Fin 4,
    p10_constraintsB ![1, 0, 3, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_1_1_0 : ∀ d e f g : Fin 4,
    p10_constraintsB ![1, 1, 0, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_1_1_1 : ∀ d e f g : Fin 4,
    p10_constraintsB ![1, 1, 1, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_1_1_2 : ∀ d e f g : Fin 4,
    p10_constraintsB ![1, 1, 2, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_1_1_3 : ∀ d e f g : Fin 4,
    p10_constraintsB ![1, 1, 3, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_1_2_0 : ∀ d e f g : Fin 4,
    p10_constraintsB ![1, 2, 0, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_1_2_1 : ∀ d e f g : Fin 4,
    p10_constraintsB ![1, 2, 1, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_1_2_2 : ∀ d e f g : Fin 4,
    p10_constraintsB ![1, 2, 2, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_1_2_3 : ∀ d e f g : Fin 4,
    p10_constraintsB ![1, 2, 3, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_1_3_0 : ∀ d e f g : Fin 4,
    p10_constraintsB ![1, 3, 0, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_1_3_1 : ∀ d e f g : Fin 4,
    p10_constraintsB ![1, 3, 1, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_1_3_2 : ∀ d e f g : Fin 4,
    p10_constraintsB ![1, 3, 2, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_1_3_3 : ∀ d e f g : Fin 4,
    p10_constraintsB ![1, 3, 3, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_2_0_0 : ∀ d e f g : Fin 4,
    p10_constraintsB ![2, 0, 0, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_2_0_1 : ∀ d e f g : Fin 4,
    p10_constraintsB ![2, 0, 1, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_2_0_2 : ∀ d e f g : Fin 4,
    p10_constraintsB ![2, 0, 2, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_2_0_3 : ∀ d e f g : Fin 4,
    p10_constraintsB ![2, 0, 3, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_2_1_0 : ∀ d e f g : Fin 4,
    p10_constraintsB ![2, 1, 0, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_2_1_1 : ∀ d e f g : Fin 4,
    p10_constraintsB ![2, 1, 1, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_2_1_2 : ∀ d e f g : Fin 4,
    p10_constraintsB ![2, 1, 2, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_2_1_3 : ∀ d e f g : Fin 4,
    p10_constraintsB ![2, 1, 3, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_2_2_0 : ∀ d e f g : Fin 4,
    p10_constraintsB ![2, 2, 0, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_2_2_1 : ∀ d e f g : Fin 4,
    p10_constraintsB ![2, 2, 1, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_2_2_2 : ∀ d e f g : Fin 4,
    p10_constraintsB ![2, 2, 2, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_2_2_3 : ∀ d e f g : Fin 4,
    p10_constraintsB ![2, 2, 3, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_2_3_0 : ∀ d e f g : Fin 4,
    p10_constraintsB ![2, 3, 0, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_2_3_1 : ∀ d e f g : Fin 4,
    p10_constraintsB ![2, 3, 1, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_2_3_2 : ∀ d e f g : Fin 4,
    p10_constraintsB ![2, 3, 2, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_2_3_3 : ∀ d e f g : Fin 4,
    p10_constraintsB ![2, 3, 3, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_3_0_0 : ∀ d e f g : Fin 4,
    p10_constraintsB ![3, 0, 0, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_3_0_1 : ∀ d e f g : Fin 4,
    p10_constraintsB ![3, 0, 1, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_3_0_2 : ∀ d e f g : Fin 4,
    p10_constraintsB ![3, 0, 2, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_3_0_3 : ∀ d e f g : Fin 4,
    p10_constraintsB ![3, 0, 3, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_3_1_0 : ∀ d e f g : Fin 4,
    p10_constraintsB ![3, 1, 0, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_3_1_1 : ∀ d e f g : Fin 4,
    p10_constraintsB ![3, 1, 1, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_3_1_2 : ∀ d e f g : Fin 4,
    p10_constraintsB ![3, 1, 2, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_3_1_3 : ∀ d e f g : Fin 4,
    p10_constraintsB ![3, 1, 3, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_3_2_0 : ∀ d e f g : Fin 4,
    p10_constraintsB ![3, 2, 0, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_3_2_1 : ∀ d e f g : Fin 4,
    p10_constraintsB ![3, 2, 1, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_3_2_2 : ∀ d e f g : Fin 4,
    p10_constraintsB ![3, 2, 2, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_3_2_3 : ∀ d e f g : Fin 4,
    p10_constraintsB ![3, 2, 3, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_3_3_0 : ∀ d e f g : Fin 4,
    p10_constraintsB ![3, 3, 0, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_3_3_1 : ∀ d e f g : Fin 4,
    p10_constraintsB ![3, 3, 1, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_3_3_2 : ∀ d e f g : Fin 4,
    p10_constraintsB ![3, 3, 2, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_certificate_3_3_3 : ∀ d e f g : Fin 4,
    p10_constraintsB ![3, 3, 3, d, e, f, g] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_no_constraints_codes (a b c d e f g : Fin 4) :
    p10_constraintsB ![a, b, c, d, e, f, g] = false := by
  fin_cases a <;> fin_cases b <;> fin_cases c
  · exact p10_certificate_0_0_0 d e f g
  · exact p10_certificate_0_0_1 d e f g
  · exact p10_certificate_0_0_2 d e f g
  · exact p10_certificate_0_0_3 d e f g
  · exact p10_certificate_0_1_0 d e f g
  · exact p10_certificate_0_1_1 d e f g
  · exact p10_certificate_0_1_2 d e f g
  · exact p10_certificate_0_1_3 d e f g
  · exact p10_certificate_0_2_0 d e f g
  · exact p10_certificate_0_2_1 d e f g
  · exact p10_certificate_0_2_2 d e f g
  · exact p10_certificate_0_2_3 d e f g
  · exact p10_certificate_0_3_0 d e f g
  · exact p10_certificate_0_3_1 d e f g
  · exact p10_certificate_0_3_2 d e f g
  · exact p10_certificate_0_3_3 d e f g
  · exact p10_certificate_1_0_0 d e f g
  · exact p10_certificate_1_0_1 d e f g
  · exact p10_certificate_1_0_2 d e f g
  · exact p10_certificate_1_0_3 d e f g
  · exact p10_certificate_1_1_0 d e f g
  · exact p10_certificate_1_1_1 d e f g
  · exact p10_certificate_1_1_2 d e f g
  · exact p10_certificate_1_1_3 d e f g
  · exact p10_certificate_1_2_0 d e f g
  · exact p10_certificate_1_2_1 d e f g
  · exact p10_certificate_1_2_2 d e f g
  · exact p10_certificate_1_2_3 d e f g
  · exact p10_certificate_1_3_0 d e f g
  · exact p10_certificate_1_3_1 d e f g
  · exact p10_certificate_1_3_2 d e f g
  · exact p10_certificate_1_3_3 d e f g
  · exact p10_certificate_2_0_0 d e f g
  · exact p10_certificate_2_0_1 d e f g
  · exact p10_certificate_2_0_2 d e f g
  · exact p10_certificate_2_0_3 d e f g
  · exact p10_certificate_2_1_0 d e f g
  · exact p10_certificate_2_1_1 d e f g
  · exact p10_certificate_2_1_2 d e f g
  · exact p10_certificate_2_1_3 d e f g
  · exact p10_certificate_2_2_0 d e f g
  · exact p10_certificate_2_2_1 d e f g
  · exact p10_certificate_2_2_2 d e f g
  · exact p10_certificate_2_2_3 d e f g
  · exact p10_certificate_2_3_0 d e f g
  · exact p10_certificate_2_3_1 d e f g
  · exact p10_certificate_2_3_2 d e f g
  · exact p10_certificate_2_3_3 d e f g
  · exact p10_certificate_3_0_0 d e f g
  · exact p10_certificate_3_0_1 d e f g
  · exact p10_certificate_3_0_2 d e f g
  · exact p10_certificate_3_0_3 d e f g
  · exact p10_certificate_3_1_0 d e f g
  · exact p10_certificate_3_1_1 d e f g
  · exact p10_certificate_3_1_2 d e f g
  · exact p10_certificate_3_1_3 d e f g
  · exact p10_certificate_3_2_0 d e f g
  · exact p10_certificate_3_2_1 d e f g
  · exact p10_certificate_3_2_2 d e f g
  · exact p10_certificate_3_2_3 d e f g
  · exact p10_certificate_3_3_0 d e f g
  · exact p10_certificate_3_3_1 d e f g
  · exact p10_certificate_3_3_2 d e f g
  · exact p10_certificate_3_3_3 d e f g

theorem p10_no_constraints (r : Fin 7 → Fin 4) : p10_constraintsB r = false := by
  have h : r = ![r 0, r 1, r 2, r 3, r 4, r 5, r 6] := by
    funext t
    fin_cases t <;> rfl
  rw [h]
  exact p10_no_constraints_codes _ _ _ _ _ _ _

end PEqualNP.Outside.L_meta_6659_aux
