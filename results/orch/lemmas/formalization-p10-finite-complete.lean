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

def p10_forcedSet (r : Fin 7 → Finset (Fin 2)) (i : Fin 4) : Finset (Fin 7) :=
  p10_nb i ∪ Finset.univ.filter (fun t => ∃ x ∈ p10_nb i, (r x).Nonempty ∧ r x ⊆ r t)

def p10_constraints (r : Fin 7 → Finset (Fin 2)) : Prop :=
  ∀ t : Fin 7, (Finset.univ.filter (fun i : Fin 4 => t ∈ p10_forcedSet r i)).card +
    (if t = 0 then 0 else 1) ≤ 2 + (r t).card

lemma p10_mask_subset_correct : ∀ a b : Fin 4,
    p10_nonempty_subset a b = true ↔ (p10_mask a).Nonempty ∧ p10_mask a ⊆ p10_mask b := by
  decide +kernel

lemma p10_mask_card_correct : ∀ a : Fin 4, p10_card a = (p10_mask a).card := by
  decide +kernel

lemma p10_adj_correct : ∀ i : Fin 4, ∀ t : Fin 7, p10_adj i t = true ↔ t ∈ p10_nb i := by
  decide +kernel

lemma p10_filter_card_four : ∀ f : Fin 4 → Bool,
    (Finset.univ.filter (fun i => f i = true)).card =
      (f 0).toNat + (f 1).toNat + (f 2).toNat + (f 3).toNat := by
  decide +kernel

lemma p10_forced_correct (r : Fin 7 → Fin 4) (i : Fin 4) (t : Fin 7) :
    p10_force r i t = true ↔ t ∈ p10_forcedSet (fun x => p10_mask (r x)) i := by
  fin_cases i <;> simp [p10_force,p10_forcedSet,p10_adj_correct,p10_mask_subset_correct,p10_nb,or_assoc]

lemma p10_count_correct (r : Fin 7 → Fin 4) (t : Fin 7) :
    p10_count r t =
      (Finset.univ.filter (fun i : Fin 4 => t ∈ p10_forcedSet (fun x => p10_mask (r x)) i)).card +
        (if t = 0 then 0 else 1) := by
  have eq : Finset.univ.filter (fun i : Fin 4 => t ∈ p10_forcedSet (fun x => p10_mask (r x)) i) =
      Finset.univ.filter (fun i : Fin 4 => p10_force r i t = true) := by
    ext i
    simp [p10_forced_correct]
  rw [eq,p10_filter_card_four]
  rfl

lemma p10_bool_of_constraints (r : Fin 7 → Fin 4)
    (hc : p10_constraints (fun t => p10_mask (r t))) : p10_constraintsB r = true := by
  have hb (t : Fin 7) : p10_budget r t = true := by
    simp only [p10_budget,decide_eq_true_eq,p10_count_correct,p10_mask_card_correct]
    exact hc t
  simp only [p10_constraintsB,hb,Bool.and_self]

lemma p10_mask_surjective : ∀ s : Finset (Fin 2), ∃ a : Fin 4, p10_mask a = s := by
  decide +kernel

theorem p10_no_finset_constraints (r : Fin 7 → Finset (Fin 2)) : ¬ p10_constraints r := by
  classical
  intro hc
  choose m hm using (fun t : Fin 7 => p10_mask_surjective (r t))
  have eq : (fun t => p10_mask (m t)) = r := funext hm
  have hb := p10_bool_of_constraints m (by rw [eq]; exact hc)
  rw [p10_no_constraints] at hb
  exact Bool.noConfusion hb

end PEqualNP.Outside.L_meta_6659_aux
