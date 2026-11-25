import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6659_aux

def m9_mask (m : Fin 8) : Finset (Fin 3) :=
  ![∅,{0},{1},{0,1},{2},{0,2},{1,2},{0,1,2}] m

def m9_sub (a b : Fin 8) : Bool :=
  ![![true,true,true,true,true,true,true,true],
    ![false,true,false,true,false,true,false,true],
    ![false,false,true,true,false,false,true,true],
    ![false,false,false,true,false,false,false,true],
    ![false,false,false,false,true,true,true,true],
    ![false,false,false,false,false,true,false,true],
    ![false,false,false,false,false,false,true,true],
    ![false,false,false,false,false,false,false,true]] a b

def m9_card (a : Fin 8) : ℕ := ![0,1,1,2,1,2,2,3] a

def m9_bit (a : Fin 8) (k : Fin 3) : Bool :=
  ![![false,false,false],![true,false,false],![false,true,false],![true,true,false],
    ![false,false,true],![true,false,true],![false,true,true],![true,true,true]] a k

def m9_extra2 (a : Fin 3) : Fin 6 := ![0,2,4] a
def m9_extra5 (b : Fin 3) : Fin 6 := ![0,1,3] b

def m9_force (r : Fin 6 → Fin 8) (a b : Fin 3) (i : Fin 4) (t : Fin 6) : Bool :=
  ![m9_sub (r 0) (r t) || m9_sub (r 1) (r t) || m9_sub (r 2) (r t),
    m9_sub (r 0) (r t) || m9_sub (r 3) (r t) || m9_sub (r 4) (r t),
    m9_sub (r 1) (r t) || m9_sub (r 3) (r t) || m9_sub (r 5) (r t) || decide (t = m9_extra2 a),
    m9_sub (r 2) (r t) || m9_sub (r 4) (r t) || m9_sub (r 5) (r t) || decide (t = m9_extra5 b)] i

def m9_count (r : Fin 6 → Fin 8) (a b : Fin 3) (t : Fin 6) : ℕ :=
  (m9_force r a b 0 t).toNat + (m9_force r a b 1 t).toNat +
    (m9_force r a b 2 t).toNat + (m9_force r a b 3 t).toNat

def m9_full (r : Fin 6 → Fin 8) (a b : Fin 3) (i : Fin 2) : Bool :=
  ![decide (m9_count r a b 0 = 1+m9_card (r 0)) ||
      decide (m9_count r a b 1 = 1+m9_card (r 1)) ||
      decide (m9_count r a b 2 = 1+m9_card (r 2)),
    decide (m9_count r a b 0 = 1+m9_card (r 0)) ||
      decide (m9_count r a b 3 = 1+m9_card (r 3)) ||
      decide (m9_count r a b 4 = 1+m9_card (r 4))] i

def m9_unitMask (r : Fin 6 → Fin 8) (k : Fin 3) : ℕ :=
  (m9_bit (r 0) k).toNat + 2*(m9_bit (r 1) k).toNat +
    4*(m9_bit (r 2) k).toNat + 8*(m9_bit (r 3) k).toNat +
    16*(m9_bit (r 4) k).toNat + 32*(m9_bit (r 5) k).toNat

def m9_normal (r : Fin 6 → Fin 8) (a b : Fin 3) : Bool :=
  decide (r 0 ≠ 0 ∧ r 0 ≠ 7) && decide (r 1 ≠ 0 ∧ r 1 ≠ 7) &&
  decide (r 2 ≠ 0 ∧ r 2 ≠ 7) && decide (r 3 ≠ 0 ∧ r 3 ≠ 7) &&
  decide (r 4 ≠ 0 ∧ r 4 ≠ 7) && decide (r 5 ≠ 0 ∧ r 5 ≠ 7) &&
  decide (m9_unitMask r 0 ≠ 42 ∧ m9_unitMask r 0 ≠ 52) &&
  decide (m9_unitMask r 1 ≠ 42 ∧ m9_unitMask r 1 ≠ 52) &&
  decide (m9_unitMask r 2 ≠ 42 ∧ m9_unitMask r 2 ≠ 52) &&
  decide (m9_count r a b 0 ≤ 1+m9_card (r 0)) &&
  decide (m9_count r a b 1 ≤ 1+m9_card (r 1)) &&
  decide (m9_count r a b 2 ≤ 1+m9_card (r 2)) &&
  decide (m9_count r a b 3 ≤ 1+m9_card (r 3)) &&
  decide (m9_count r a b 4 ≤ 1+m9_card (r 4)) &&
  decide (m9_count r a b 5 ≤ 1+m9_card (r 5)) &&
  (!m9_full r a b 0 || (!m9_force r a b 0 3 && !m9_force r a b 0 4 && !m9_force r a b 0 5)) &&
  (!m9_full r a b 1 || (!m9_force r a b 1 1 && !m9_force r a b 1 2 && !m9_force r a b 1 5))

def m9_pointForce (r : Fin 6 → Fin 8) (T : Fin 8) (i : Fin 4) : Bool :=
  ![m9_sub (r 0) T || m9_sub (r 1) T || m9_sub (r 2) T,
    m9_sub (r 0) T || m9_sub (r 3) T || m9_sub (r 4) T,
    m9_sub (r 1) T || m9_sub (r 3) T || m9_sub (r 5) T,
    m9_sub (r 2) T || m9_sub (r 4) T || m9_sub (r 5) T] i

def m9_pointAllowed (r : Fin 6 → Fin 8) (a b : Fin 3) (T : Fin 8) : Bool :=
  decide (T ≠ 0) &&
  (!(m9_full r a b 0 && m9_pointForce r T 0)) &&
  (!(m9_full r a b 1 && m9_pointForce r T 1)) &&
  decide ((m9_pointForce r T 0).toNat + (m9_pointForce r T 1).toNat +
    (m9_pointForce r T 2).toNat + (m9_pointForce r T 3).toNat ≤ m9_card T) &&
  decide (m9_count r a b 0 + (m9_sub T (r 0)).toNat ≤ 1+m9_card (r 0)) &&
  decide (m9_count r a b 1 + (m9_sub T (r 1)).toNat ≤ 1+m9_card (r 1)) &&
  decide (m9_count r a b 2 + (m9_sub T (r 2)).toNat ≤ 1+m9_card (r 2)) &&
  decide (m9_count r a b 3 + (m9_sub T (r 3)).toNat ≤ 1+m9_card (r 3)) &&
  decide (m9_count r a b 4 + (m9_sub T (r 4)).toNat ≤ 1+m9_card (r 4)) &&
  decide (m9_count r a b 5 + (m9_sub T (r 5)).toNat ≤ 1+m9_card (r 5))

def m9_good (r : Fin 6 → Fin 8) (a b : Fin 3) : Bool :=
  m9_full r a b 0 && m9_full r a b 1 &&
    !m9_pointAllowed r a b 1 && !m9_pointAllowed r a b 2 && !m9_pointAllowed r a b 3 &&
    !m9_pointAllowed r a b 4 && !m9_pointAllowed r a b 5 && !m9_pointAllowed r a b 6 &&
    !m9_pointAllowed r a b 7

def m9_bad (r : Fin 6 → Fin 8) : Bool :=
  (m9_normal r 0 0 && !m9_good r 0 0) || (m9_normal r 0 1 && !m9_good r 0 1) ||
  (m9_normal r 0 2 && !m9_good r 0 2) || (m9_normal r 1 0 && !m9_good r 1 0) ||
  (m9_normal r 1 1 && !m9_good r 1 1) || (m9_normal r 1 2 && !m9_good r 1 2) ||
  (m9_normal r 2 0 && !m9_good r 2 0) || (m9_normal r 2 1 && !m9_good r 2 1) ||
  (m9_normal r 2 2 && !m9_good r 2 2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_0_0 : ∀ c d e : Fin 8, m9_bad ![1,0,0,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_0_1 : ∀ c d e : Fin 8, m9_bad ![1,0,1,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_0_2 : ∀ c d e : Fin 8, m9_bad ![1,0,2,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_0_3 : ∀ c d e : Fin 8, m9_bad ![1,0,3,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_0_4 : ∀ c d e : Fin 8, m9_bad ![1,0,4,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_0_5 : ∀ c d e : Fin 8, m9_bad ![1,0,5,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_0_6 : ∀ c d e : Fin 8, m9_bad ![1,0,6,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_0_7 : ∀ c d e : Fin 8, m9_bad ![1,0,7,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_1_0 : ∀ c d e : Fin 8, m9_bad ![1,1,0,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_1_1 : ∀ c d e : Fin 8, m9_bad ![1,1,1,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_1_2 : ∀ c d e : Fin 8, m9_bad ![1,1,2,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_1_3 : ∀ c d e : Fin 8, m9_bad ![1,1,3,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_1_4 : ∀ c d e : Fin 8, m9_bad ![1,1,4,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_1_5 : ∀ c d e : Fin 8, m9_bad ![1,1,5,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_1_6 : ∀ c d e : Fin 8, m9_bad ![1,1,6,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_1_7 : ∀ c d e : Fin 8, m9_bad ![1,1,7,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_2_0 : ∀ c d e : Fin 8, m9_bad ![1,2,0,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_2_1 : ∀ c d e : Fin 8, m9_bad ![1,2,1,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_2_2 : ∀ c d e : Fin 8, m9_bad ![1,2,2,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_2_3 : ∀ c d e : Fin 8, m9_bad ![1,2,3,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_2_4 : ∀ c d e : Fin 8, m9_bad ![1,2,4,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_2_5 : ∀ c d e : Fin 8, m9_bad ![1,2,5,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_2_6 : ∀ c d e : Fin 8, m9_bad ![1,2,6,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_2_7 : ∀ c d e : Fin 8, m9_bad ![1,2,7,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_3_0 : ∀ c d e : Fin 8, m9_bad ![1,3,0,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_3_1 : ∀ c d e : Fin 8, m9_bad ![1,3,1,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_3_2 : ∀ c d e : Fin 8, m9_bad ![1,3,2,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_3_3 : ∀ c d e : Fin 8, m9_bad ![1,3,3,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_3_4 : ∀ c d e : Fin 8, m9_bad ![1,3,4,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_3_5 : ∀ c d e : Fin 8, m9_bad ![1,3,5,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_3_6 : ∀ c d e : Fin 8, m9_bad ![1,3,6,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_3_7 : ∀ c d e : Fin 8, m9_bad ![1,3,7,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_4_0 : ∀ c d e : Fin 8, m9_bad ![1,4,0,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_4_1 : ∀ c d e : Fin 8, m9_bad ![1,4,1,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_4_2 : ∀ c d e : Fin 8, m9_bad ![1,4,2,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_4_3 : ∀ c d e : Fin 8, m9_bad ![1,4,3,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_4_4 : ∀ c d e : Fin 8, m9_bad ![1,4,4,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_4_5 : ∀ c d e : Fin 8, m9_bad ![1,4,5,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_4_6 : ∀ c d e : Fin 8, m9_bad ![1,4,6,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_4_7 : ∀ c d e : Fin 8, m9_bad ![1,4,7,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_5_0 : ∀ c d e : Fin 8, m9_bad ![1,5,0,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_5_1 : ∀ c d e : Fin 8, m9_bad ![1,5,1,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_5_2 : ∀ c d e : Fin 8, m9_bad ![1,5,2,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_5_3 : ∀ c d e : Fin 8, m9_bad ![1,5,3,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_5_4 : ∀ c d e : Fin 8, m9_bad ![1,5,4,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_5_5 : ∀ c d e : Fin 8, m9_bad ![1,5,5,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_5_6 : ∀ c d e : Fin 8, m9_bad ![1,5,6,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_5_7 : ∀ c d e : Fin 8, m9_bad ![1,5,7,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_6_0 : ∀ c d e : Fin 8, m9_bad ![1,6,0,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_6_1 : ∀ c d e : Fin 8, m9_bad ![1,6,1,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_6_2 : ∀ c d e : Fin 8, m9_bad ![1,6,2,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_6_3 : ∀ c d e : Fin 8, m9_bad ![1,6,3,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_6_4 : ∀ c d e : Fin 8, m9_bad ![1,6,4,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_6_5 : ∀ c d e : Fin 8, m9_bad ![1,6,5,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_6_6 : ∀ c d e : Fin 8, m9_bad ![1,6,6,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_6_7 : ∀ c d e : Fin 8, m9_bad ![1,6,7,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_7_0 : ∀ c d e : Fin 8, m9_bad ![1,7,0,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_7_1 : ∀ c d e : Fin 8, m9_bad ![1,7,1,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_7_2 : ∀ c d e : Fin 8, m9_bad ![1,7,2,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_7_3 : ∀ c d e : Fin 8, m9_bad ![1,7,3,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_7_4 : ∀ c d e : Fin 8, m9_bad ![1,7,4,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_7_5 : ∀ c d e : Fin 8, m9_bad ![1,7,5,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_7_6 : ∀ c d e : Fin 8, m9_bad ![1,7,6,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_1_7_7 : ∀ c d e : Fin 8, m9_bad ![1,7,7,c,d,e] = false := by
  intro c d e; rfl

theorem m9_certificate_1 : ∀ a b c d e : Fin 8, m9_bad ![1,a,b,c,d,e] = false := by
  intro a b
  fin_cases a <;> fin_cases b
  · exact m9_block_1_0_0
  · exact m9_block_1_0_1
  · exact m9_block_1_0_2
  · exact m9_block_1_0_3
  · exact m9_block_1_0_4
  · exact m9_block_1_0_5
  · exact m9_block_1_0_6
  · exact m9_block_1_0_7
  · exact m9_block_1_1_0
  · exact m9_block_1_1_1
  · exact m9_block_1_1_2
  · exact m9_block_1_1_3
  · exact m9_block_1_1_4
  · exact m9_block_1_1_5
  · exact m9_block_1_1_6
  · exact m9_block_1_1_7
  · exact m9_block_1_2_0
  · exact m9_block_1_2_1
  · exact m9_block_1_2_2
  · exact m9_block_1_2_3
  · exact m9_block_1_2_4
  · exact m9_block_1_2_5
  · exact m9_block_1_2_6
  · exact m9_block_1_2_7
  · exact m9_block_1_3_0
  · exact m9_block_1_3_1
  · exact m9_block_1_3_2
  · exact m9_block_1_3_3
  · exact m9_block_1_3_4
  · exact m9_block_1_3_5
  · exact m9_block_1_3_6
  · exact m9_block_1_3_7
  · exact m9_block_1_4_0
  · exact m9_block_1_4_1
  · exact m9_block_1_4_2
  · exact m9_block_1_4_3
  · exact m9_block_1_4_4
  · exact m9_block_1_4_5
  · exact m9_block_1_4_6
  · exact m9_block_1_4_7
  · exact m9_block_1_5_0
  · exact m9_block_1_5_1
  · exact m9_block_1_5_2
  · exact m9_block_1_5_3
  · exact m9_block_1_5_4
  · exact m9_block_1_5_5
  · exact m9_block_1_5_6
  · exact m9_block_1_5_7
  · exact m9_block_1_6_0
  · exact m9_block_1_6_1
  · exact m9_block_1_6_2
  · exact m9_block_1_6_3
  · exact m9_block_1_6_4
  · exact m9_block_1_6_5
  · exact m9_block_1_6_6
  · exact m9_block_1_6_7
  · exact m9_block_1_7_0
  · exact m9_block_1_7_1
  · exact m9_block_1_7_2
  · exact m9_block_1_7_3
  · exact m9_block_1_7_4
  · exact m9_block_1_7_5
  · exact m9_block_1_7_6
  · exact m9_block_1_7_7

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_0_0 : ∀ c d e : Fin 8, m9_bad ![3,0,0,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_0_1 : ∀ c d e : Fin 8, m9_bad ![3,0,1,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_0_2 : ∀ c d e : Fin 8, m9_bad ![3,0,2,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_0_3 : ∀ c d e : Fin 8, m9_bad ![3,0,3,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_0_4 : ∀ c d e : Fin 8, m9_bad ![3,0,4,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_0_5 : ∀ c d e : Fin 8, m9_bad ![3,0,5,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_0_6 : ∀ c d e : Fin 8, m9_bad ![3,0,6,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_0_7 : ∀ c d e : Fin 8, m9_bad ![3,0,7,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_1_0 : ∀ c d e : Fin 8, m9_bad ![3,1,0,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_1_1 : ∀ c d e : Fin 8, m9_bad ![3,1,1,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_1_2 : ∀ c d e : Fin 8, m9_bad ![3,1,2,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_1_3 : ∀ c d e : Fin 8, m9_bad ![3,1,3,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_1_4 : ∀ c d e : Fin 8, m9_bad ![3,1,4,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_1_5 : ∀ c d e : Fin 8, m9_bad ![3,1,5,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_1_6 : ∀ c d e : Fin 8, m9_bad ![3,1,6,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_1_7 : ∀ c d e : Fin 8, m9_bad ![3,1,7,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_2_0 : ∀ c d e : Fin 8, m9_bad ![3,2,0,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_2_1 : ∀ c d e : Fin 8, m9_bad ![3,2,1,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_2_2 : ∀ c d e : Fin 8, m9_bad ![3,2,2,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_2_3 : ∀ c d e : Fin 8, m9_bad ![3,2,3,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_2_4 : ∀ c d e : Fin 8, m9_bad ![3,2,4,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_2_5 : ∀ c d e : Fin 8, m9_bad ![3,2,5,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_2_6 : ∀ c d e : Fin 8, m9_bad ![3,2,6,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_2_7 : ∀ c d e : Fin 8, m9_bad ![3,2,7,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_3_0 : ∀ c d e : Fin 8, m9_bad ![3,3,0,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_3_1 : ∀ c d e : Fin 8, m9_bad ![3,3,1,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_3_2 : ∀ c d e : Fin 8, m9_bad ![3,3,2,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_3_3 : ∀ c d e : Fin 8, m9_bad ![3,3,3,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_3_4 : ∀ c d e : Fin 8, m9_bad ![3,3,4,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_3_5 : ∀ c d e : Fin 8, m9_bad ![3,3,5,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_3_6 : ∀ c d e : Fin 8, m9_bad ![3,3,6,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_3_7 : ∀ c d e : Fin 8, m9_bad ![3,3,7,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_4_0 : ∀ c d e : Fin 8, m9_bad ![3,4,0,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_4_1 : ∀ c d e : Fin 8, m9_bad ![3,4,1,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_4_2 : ∀ c d e : Fin 8, m9_bad ![3,4,2,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_4_3 : ∀ c d e : Fin 8, m9_bad ![3,4,3,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_4_4 : ∀ c d e : Fin 8, m9_bad ![3,4,4,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_4_5 : ∀ c d e : Fin 8, m9_bad ![3,4,5,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_4_6 : ∀ c d e : Fin 8, m9_bad ![3,4,6,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_4_7 : ∀ c d e : Fin 8, m9_bad ![3,4,7,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_5_0 : ∀ c d e : Fin 8, m9_bad ![3,5,0,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_5_1 : ∀ c d e : Fin 8, m9_bad ![3,5,1,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_5_2 : ∀ c d e : Fin 8, m9_bad ![3,5,2,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_5_3 : ∀ c d e : Fin 8, m9_bad ![3,5,3,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_5_4 : ∀ c d e : Fin 8, m9_bad ![3,5,4,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_5_5 : ∀ c d e : Fin 8, m9_bad ![3,5,5,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_5_6 : ∀ c d e : Fin 8, m9_bad ![3,5,6,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_5_7 : ∀ c d e : Fin 8, m9_bad ![3,5,7,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_6_0 : ∀ c d e : Fin 8, m9_bad ![3,6,0,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_6_1 : ∀ c d e : Fin 8, m9_bad ![3,6,1,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_6_2 : ∀ c d e : Fin 8, m9_bad ![3,6,2,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_6_3 : ∀ c d e : Fin 8, m9_bad ![3,6,3,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_6_4 : ∀ c d e : Fin 8, m9_bad ![3,6,4,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_6_5 : ∀ c d e : Fin 8, m9_bad ![3,6,5,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_6_6 : ∀ c d e : Fin 8, m9_bad ![3,6,6,c,d,e] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_6_7 : ∀ c d e : Fin 8, m9_bad ![3,6,7,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_7_0 : ∀ c d e : Fin 8, m9_bad ![3,7,0,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_7_1 : ∀ c d e : Fin 8, m9_bad ![3,7,1,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_7_2 : ∀ c d e : Fin 8, m9_bad ![3,7,2,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_7_3 : ∀ c d e : Fin 8, m9_bad ![3,7,3,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_7_4 : ∀ c d e : Fin 8, m9_bad ![3,7,4,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_7_5 : ∀ c d e : Fin 8, m9_bad ![3,7,5,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_7_6 : ∀ c d e : Fin 8, m9_bad ![3,7,6,c,d,e] = false := by
  intro c d e; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m9_block_3_7_7 : ∀ c d e : Fin 8, m9_bad ![3,7,7,c,d,e] = false := by
  intro c d e; rfl

theorem m9_certificate_3 : ∀ a b c d e : Fin 8, m9_bad ![3,a,b,c,d,e] = false := by
  intro a b
  fin_cases a <;> fin_cases b
  · exact m9_block_3_0_0
  · exact m9_block_3_0_1
  · exact m9_block_3_0_2
  · exact m9_block_3_0_3
  · exact m9_block_3_0_4
  · exact m9_block_3_0_5
  · exact m9_block_3_0_6
  · exact m9_block_3_0_7
  · exact m9_block_3_1_0
  · exact m9_block_3_1_1
  · exact m9_block_3_1_2
  · exact m9_block_3_1_3
  · exact m9_block_3_1_4
  · exact m9_block_3_1_5
  · exact m9_block_3_1_6
  · exact m9_block_3_1_7
  · exact m9_block_3_2_0
  · exact m9_block_3_2_1
  · exact m9_block_3_2_2
  · exact m9_block_3_2_3
  · exact m9_block_3_2_4
  · exact m9_block_3_2_5
  · exact m9_block_3_2_6
  · exact m9_block_3_2_7
  · exact m9_block_3_3_0
  · exact m9_block_3_3_1
  · exact m9_block_3_3_2
  · exact m9_block_3_3_3
  · exact m9_block_3_3_4
  · exact m9_block_3_3_5
  · exact m9_block_3_3_6
  · exact m9_block_3_3_7
  · exact m9_block_3_4_0
  · exact m9_block_3_4_1
  · exact m9_block_3_4_2
  · exact m9_block_3_4_3
  · exact m9_block_3_4_4
  · exact m9_block_3_4_5
  · exact m9_block_3_4_6
  · exact m9_block_3_4_7
  · exact m9_block_3_5_0
  · exact m9_block_3_5_1
  · exact m9_block_3_5_2
  · exact m9_block_3_5_3
  · exact m9_block_3_5_4
  · exact m9_block_3_5_5
  · exact m9_block_3_5_6
  · exact m9_block_3_5_7
  · exact m9_block_3_6_0
  · exact m9_block_3_6_1
  · exact m9_block_3_6_2
  · exact m9_block_3_6_3
  · exact m9_block_3_6_4
  · exact m9_block_3_6_5
  · exact m9_block_3_6_6
  · exact m9_block_3_6_7
  · exact m9_block_3_7_0
  · exact m9_block_3_7_1
  · exact m9_block_3_7_2
  · exact m9_block_3_7_3
  · exact m9_block_3_7_4
  · exact m9_block_3_7_5
  · exact m9_block_3_7_6
  · exact m9_block_3_7_7

theorem m9_certificate (r : Fin 6 → Fin 8) (first : r 0 = 1 ∨ r 0 = 3) :
    m9_bad r = false := by
  have vector : r = ![r 0,r 1,r 2,r 3,r 4,r 5] := by
    funext t
    fin_cases t <;> rfl
  rw [vector]
  rcases first with first | first
  · rw [first]
    exact m9_certificate_1 _ _ _ _ _
  · rw [first]
    exact m9_certificate_3 _ _ _ _ _

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem m9_good_from_checked (r : Fin 6 → Fin 8) (a b : Fin 3)
    (checked : m9_bad r = false) (normal : m9_normal r a b = true) : m9_good r a b = true := by
  fin_cases a <;> fin_cases b
  · change m9_normal r 0 0 = true at normal
    change m9_good r 0 0 = true
    cases good : m9_good r 0 0
    · have impossible : m9_bad r = true := by
        simp only [m9_bad,normal,good,Bool.not_false,Bool.and_true,Bool.true_or,Bool.or_true]
      rw [checked] at impossible
      contradiction
    · rfl
  · change m9_normal r 0 1 = true at normal
    change m9_good r 0 1 = true
    cases good : m9_good r 0 1
    · have impossible : m9_bad r = true := by
        simp only [m9_bad,normal,good,Bool.not_false,Bool.and_true,Bool.true_or,Bool.or_true]
      rw [checked] at impossible
      contradiction
    · rfl
  · change m9_normal r 0 2 = true at normal
    change m9_good r 0 2 = true
    cases good : m9_good r 0 2
    · have impossible : m9_bad r = true := by
        simp only [m9_bad,normal,good,Bool.not_false,Bool.and_true,Bool.true_or,Bool.or_true]
      rw [checked] at impossible
      contradiction
    · rfl
  · change m9_normal r 1 0 = true at normal
    change m9_good r 1 0 = true
    cases good : m9_good r 1 0
    · have impossible : m9_bad r = true := by
        simp only [m9_bad,normal,good,Bool.not_false,Bool.and_true,Bool.true_or,Bool.or_true]
      rw [checked] at impossible
      contradiction
    · rfl
  · change m9_normal r 1 1 = true at normal
    change m9_good r 1 1 = true
    cases good : m9_good r 1 1
    · have impossible : m9_bad r = true := by
        simp only [m9_bad,normal,good,Bool.not_false,Bool.and_true,Bool.true_or,Bool.or_true]
      rw [checked] at impossible
      contradiction
    · rfl
  · change m9_normal r 1 2 = true at normal
    change m9_good r 1 2 = true
    cases good : m9_good r 1 2
    · have impossible : m9_bad r = true := by
        simp only [m9_bad,normal,good,Bool.not_false,Bool.and_true,Bool.true_or,Bool.or_true]
      rw [checked] at impossible
      contradiction
    · rfl
  · change m9_normal r 2 0 = true at normal
    change m9_good r 2 0 = true
    cases good : m9_good r 2 0
    · have impossible : m9_bad r = true := by
        simp only [m9_bad,normal,good,Bool.not_false,Bool.and_true,Bool.true_or,Bool.or_true]
      rw [checked] at impossible
      contradiction
    · rfl
  · change m9_normal r 2 1 = true at normal
    change m9_good r 2 1 = true
    cases good : m9_good r 2 1
    · have impossible : m9_bad r = true := by
        simp only [m9_bad,normal,good,Bool.not_false,Bool.and_true,Bool.true_or,Bool.or_true]
      rw [checked] at impossible
      contradiction
    · rfl
  · change m9_normal r 2 2 = true at normal
    change m9_good r 2 2 = true
    cases good : m9_good r 2 2
    · have impossible : m9_bad r = true := by
        simp only [m9_bad,normal,good,Bool.not_false,Bool.and_true,Bool.true_or,Bool.or_true]
      rw [checked] at impossible
      contradiction
    · rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem m9_point_from_good (r : Fin 6 → Fin 8) (a b : Fin 3) (T : Fin 8)
    (good : m9_good r a b = true) : m9_pointAllowed r a b T = false := by
  simp only [m9_good,Bool.and_eq_true,Bool.not_eq_true'] at good
  fin_cases T
  · rfl
  · change m9_pointAllowed r a b 1 = false
    exact good.1.1.1.1.1.1.2
  · change m9_pointAllowed r a b 2 = false
    exact good.1.1.1.1.1.2
  · change m9_pointAllowed r a b 3 = false
    exact good.1.1.1.1.2
  · change m9_pointAllowed r a b 4 = false
    exact good.1.1.1.2
  · change m9_pointAllowed r a b 5 = false
    exact good.1.1.2
  · change m9_pointAllowed r a b 6 = false
    exact good.1.2
  · change m9_pointAllowed r a b 7 = false
    exact good.2

theorem m9_good_of_normal (r : Fin 6 → Fin 8) (a b : Fin 3)
    (first : r 0 = 1 ∨ r 0 = 3) (normal : m9_normal r a b = true) :
    m9_good r a b = true :=
  m9_good_from_checked r a b (m9_certificate r first) normal

theorem m9_point_empty (r : Fin 6 → Fin 8) (a b : Fin 3) (T : Fin 8)
    (first : r 0 = 1 ∨ r 0 = 3) (normal : m9_normal r a b = true) :
    m9_pointAllowed r a b T = false :=
  m9_point_from_good r a b T (m9_good_of_normal r a b first normal)

end PEqualNP.Outside.L_meta_6659_aux
