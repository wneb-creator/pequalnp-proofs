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


def m9_neighbors (i : Fin 4) : Finset (Fin 6) :=
  ![{0,1,2},{0,3,4},{1,3,5},{2,4,5}] i

def m9_protected (i : Fin 2) : Fin 4 := Fin.castLE (by decide) i

def m9_forced (r : Fin 6 → Finset (Fin 3)) (a b : Fin 3) (i : Fin 4) : Finset (Fin 6) :=
  Finset.univ.filter (fun t => (∃ x ∈ m9_neighbors i, r x ⊆ r t) ∨
    (i = 2 ∧ t = m9_extra2 a) ∨ (i = 3 ∧ t = m9_extra5 b))

def m9_consumers (r : Fin 6 → Finset (Fin 3)) (a b : Fin 3) (t : Fin 6) : Finset (Fin 4) :=
  Finset.univ.filter (fun i => t ∈ m9_forced r a b i)

def m9_saturated (r : Fin 6 → Finset (Fin 3)) (a b : Fin 3) (i : Fin 2) : Prop :=
  ∃ x ∈ m9_neighbors (m9_protected i), (m9_consumers r a b x).card = 1 + (r x).card

def m9_unit_support (r : Fin 6 → Finset (Fin 3)) (k : Fin 3) : Finset (Fin 6) :=
  Finset.univ.filter (fun t => k ∈ r t)

abbrev m9_constraints (r : Fin 6 → Finset (Fin 3)) (a b : Fin 3) : Prop :=
  (∀ t, (r t).Nonempty ∧ r t ≠ Finset.univ) ∧
  (∀ k, m9_unit_support r k ≠ m9_neighbors 2 ∧ m9_unit_support r k ≠ m9_neighbors 3) ∧
  (∀ t, (m9_consumers r a b t).card ≤ 1 + (r t).card) ∧
  (∀ i, m9_saturated r a b i → m9_forced r a b (m9_protected i) ⊆ m9_neighbors (m9_protected i))

def m9_point_forced (r : Fin 6 → Finset (Fin 3)) (T : Finset (Fin 3)) : Finset (Fin 4) :=
  Finset.univ.filter (fun i => ∃ x ∈ m9_neighbors i, r x ⊆ T)

abbrev m9_point_constraints (r : Fin 6 → Finset (Fin 3)) (a b : Fin 3)
    (T : Finset (Fin 3)) : Prop :=
  T.Nonempty ∧
  (∀ i, m9_saturated r a b i → m9_protected i ∉ m9_point_forced r T) ∧
  (m9_point_forced r T).card ≤ T.card ∧
  (∀ t, (m9_consumers r a b t).card + (if T ⊆ r t then 1 else 0) ≤ 1 + (r t).card)

theorem m9_sub_correct : ∀ a b : Fin 8, m9_sub a b = true ↔ m9_mask a ⊆ m9_mask b := by
  decide +kernel

theorem m9_card_correct : ∀ a : Fin 8, m9_card a = (m9_mask a).card := by decide +kernel

theorem m9_bit_correct : ∀ a : Fin 8, ∀ k : Fin 3, m9_bit a k = true ↔ k ∈ m9_mask a := by
  decide +kernel

theorem m9_mask_nonempty : ∀ a : Fin 8, a ≠ 0 ↔ (m9_mask a).Nonempty := by decide +kernel

theorem m9_mask_proper : ∀ a : Fin 8, a ≠ 7 ↔ m9_mask a ≠ Finset.univ := by decide +kernel

theorem m9_filter_four : ∀ f : Fin 4 → Bool,
    (Finset.univ.filter (fun i => f i = true)).card =
      (f 0).toNat + (f 1).toNat + (f 2).toNat + (f 3).toNat := by decide +kernel

theorem m9_force_correct (r : Fin 6 → Fin 8) (a b : Fin 3) (i : Fin 4) (t : Fin 6) :
    m9_force r a b i t = true ↔ t ∈ m9_forced (fun x => m9_mask (r x)) a b i := by
  fin_cases i <;> simp [m9_force,m9_forced,m9_neighbors,m9_sub_correct,or_assoc]

theorem m9_count_correct (r : Fin 6 → Fin 8) (a b : Fin 3) (t : Fin 6) :
    m9_count r a b t = (m9_consumers (fun x => m9_mask (r x)) a b t).card := by
  have equal : m9_consumers (fun x => m9_mask (r x)) a b t =
      Finset.univ.filter (fun i => m9_force r a b i t = true) := by
    ext i
    simp [m9_consumers,m9_force_correct]
  rw [equal,m9_filter_four]
  rfl

theorem m9_full_correct (r : Fin 6 → Fin 8) (a b : Fin 3) (i : Fin 2) :
    m9_full r a b i = true ↔ m9_saturated (fun x => m9_mask (r x)) a b i := by
  fin_cases i <;>
    simp [m9_full,m9_saturated,m9_neighbors,m9_protected,m9_count_correct,m9_card_correct,or_assoc]

theorem m9_pointForce_correct (r : Fin 6 → Fin 8) (T : Fin 8) (i : Fin 4) :
    m9_pointForce r T i = true ↔ i ∈ m9_point_forced (fun x => m9_mask (r x)) (m9_mask T) := by
  unfold m9_point_forced
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ,true_and]
  fin_cases i <;> simp [m9_pointForce,m9_neighbors,m9_sub_correct,or_assoc]

theorem m9_pointCount_correct (r : Fin 6 → Fin 8) (T : Fin 8) :
    (m9_pointForce r T 0).toNat + (m9_pointForce r T 1).toNat +
      (m9_pointForce r T 2).toNat + (m9_pointForce r T 3).toNat =
      (m9_point_forced (fun x => m9_mask (r x)) (m9_mask T)).card := by
  have equal : m9_point_forced (fun x => m9_mask (r x)) (m9_mask T) =
      Finset.univ.filter (fun i => m9_pointForce r T i = true) := by
    ext i
    simp [m9_pointForce_correct]
  rw [equal,m9_filter_four]

theorem m9_unit_code_two : ∀ f : Fin 6 → Bool,
    (f 0).toNat + 2*(f 1).toNat + 4*(f 2).toNat + 8*(f 3).toNat +
      16*(f 4).toNat + 32*(f 5).toNat = 42 ↔
      Finset.univ.filter (fun t => f t = true) = m9_neighbors 2 := by decide +kernel

theorem m9_unit_code_five : ∀ f : Fin 6 → Bool,
    (f 0).toNat + 2*(f 1).toNat + 4*(f 2).toNat + 8*(f 3).toNat +
      16*(f 4).toNat + 32*(f 5).toNat = 52 ↔
      Finset.univ.filter (fun t => f t = true) = m9_neighbors 3 := by decide +kernel

theorem m9_unitMask_correct (r : Fin 6 → Fin 8) (k : Fin 3) :
    (m9_unitMask r k = 42 ↔ m9_unit_support (fun x => m9_mask (r x)) k = m9_neighbors 2) ∧
    (m9_unitMask r k = 52 ↔ m9_unit_support (fun x => m9_mask (r x)) k = m9_neighbors 3) := by
  have equal : Finset.univ.filter (fun t => m9_bit (r t) k = true) =
      m9_unit_support (fun x => m9_mask (r x)) k := by
    ext t
    simp [m9_unit_support,m9_bit_correct]
  constructor
  · simpa only [m9_unitMask,equal] using m9_unit_code_two (fun t => m9_bit (r t) k)
  · simpa only [m9_unitMask,equal] using m9_unit_code_five (fun t => m9_bit (r t) k)

theorem m9_bool_imp (a b : Bool) (h : a = true → b = true) : (!a || b) = true := by
  cases a <;> simp_all

theorem m9_not_both (a b : Bool) (h : a = true → b = true → False) : !(a && b) = true := by
  cases a <;> cases b <;> simp_all

theorem m9_normal_of_constraints (r : Fin 6 → Fin 8) (a b : Fin 3)
    (hc : m9_constraints (fun t => m9_mask (r t)) a b) : m9_normal r a b = true := by
  have proper (t : Fin 6) : r t ≠ 0 ∧ r t ≠ 7 :=
    ⟨(m9_mask_nonempty _).2 (hc.1 t).1,(m9_mask_proper _).2 (hc.1 t).2⟩
  have missing (k : Fin 3) : m9_unitMask r k ≠ 42 ∧ m9_unitMask r k ≠ 52 :=
    ⟨fun equal => (hc.2.1 k).1 ((m9_unitMask_correct r k).1.1 equal),
      fun equal => (hc.2.1 k).2 ((m9_unitMask_correct r k).2.1 equal)⟩
  have budget (t : Fin 6) : m9_count r a b t ≤ 1 + m9_card (r t) := by
    rw [m9_count_correct,m9_card_correct]
    exact hc.2.2.1 t
  have outside (i : Fin 2) (full : m9_full r a b i = true) (t : Fin 6)
      (notNeighbor : t ∉ m9_neighbors (m9_protected i)) :
      m9_force r a b (m9_protected i) t = false := by
    cases value : m9_force r a b (m9_protected i) t with
    | false => rfl
    | true =>
      exact False.elim (notNeighbor (hc.2.2.2 i ((m9_full_correct r a b i).1 full)
        ((m9_force_correct r a b _ t).1 value)))
  have full0 : (!m9_full r a b 0 ||
      (!m9_force r a b 0 3 && !m9_force r a b 0 4 && !m9_force r a b 0 5)) = true := by
    apply m9_bool_imp
    intro full
    have h3 := outside 0 full 3 (by decide)
    have h4 := outside 0 full 4 (by decide)
    have h5 := outside 0 full 5 (by decide)
    change m9_force r a b 0 3 = false at h3
    change m9_force r a b 0 4 = false at h4
    change m9_force r a b 0 5 = false at h5
    simp [h3,h4,h5]
  have full1 : (!m9_full r a b 1 ||
      (!m9_force r a b 1 1 && !m9_force r a b 1 2 && !m9_force r a b 1 5)) = true := by
    apply m9_bool_imp
    intro full
    have h1 := outside 1 full 1 (by decide)
    have h2 := outside 1 full 2 (by decide)
    have h5 := outside 1 full 5 (by decide)
    change m9_force r a b 1 1 = false at h1
    change m9_force r a b 1 2 = false at h2
    change m9_force r a b 1 5 = false at h5
    simp [h1,h2,h5]
  have p0 := proper 0
  have p1 := proper 1
  have p2 := proper 2
  have p3 := proper 3
  have p4 := proper 4
  have p5 := proper 5
  have u0 := missing 0
  have u1 := missing 1
  have u2 := missing 2
  have b0 := budget 0
  have b1 := budget 1
  have b2 := budget 2
  have b3 := budget 3
  have b4 := budget 4
  have b5 := budget 5
  simp only [m9_normal,full0,full1,Bool.and_true,Bool.and_eq_true,decide_eq_true_eq]
  tauto

theorem m9_sub_toNat : ∀ a b : Fin 8,
    (m9_sub a b).toNat = if m9_mask a ⊆ m9_mask b then 1 else 0 := by decide +kernel

theorem m9_pointAllowed_of_constraints (r : Fin 6 → Fin 8) (a b : Fin 3) (T : Fin 8)
    (hc : m9_point_constraints (fun t => m9_mask (r t)) a b (m9_mask T)) :
    m9_pointAllowed r a b T = true := by
  have nonempty : T ≠ 0 := (m9_mask_nonempty T).2 hc.1
  have absent (i : Fin 2) : !(m9_full r a b i && m9_pointForce r T (m9_protected i)) = true := by
    apply m9_not_both
    intro full forced
    exact hc.2.1 i ((m9_full_correct r a b i).1 full)
      ((m9_pointForce_correct r T (m9_protected i)).1 forced)
  have count : (m9_pointForce r T 0).toNat + (m9_pointForce r T 1).toNat +
      (m9_pointForce r T 2).toNat + (m9_pointForce r T 3).toNat ≤ m9_card T := by
    rw [m9_pointCount_correct,m9_card_correct]
    exact hc.2.2.1
  have budget (t : Fin 6) : m9_count r a b t + (m9_sub T (r t)).toNat ≤ 1+m9_card (r t) := by
    rw [m9_count_correct,m9_sub_toNat,m9_card_correct]
    exact hc.2.2.2 t
  have a0 := absent 0
  have a1 := absent 1
  change (!(m9_full r a b 0 && m9_pointForce r T 0)) = true at a0
  change (!(m9_full r a b 1 && m9_pointForce r T 1)) = true at a1
  have b0 := budget 0
  have b1 := budget 1
  have b2 := budget 2
  have b3 := budget 3
  have b4 := budget 4
  have b5 := budget 5
  simp only [m9_pointAllowed,Bool.and_eq_true,decide_eq_true_eq]
  tauto

end PEqualNP.Outside.L_meta_6659_aux
