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


end PEqualNP.Outside.L_meta_6659_aux
