import Mathlib.Data.Fin.Basic

namespace PEqualNP.Outside.L_meta_9033_aux.K2R1BPayloadUpper

def seed (row sa sc mask : Nat) : Bool :=
  (row &&& mask != 0) ||
    (row.testBit 0 && (sa &&& mask == sa)) ||
    (row.testBit 2 && (sc &&& mask == sc))

def outputUpper (hp leaf1 leaf2 : Nat × Nat) (sa sc row : Nat) : Bool :=
  let h := seed row sa sc hp.1 && seed row sa sc hp.2
  let q := row.testBit 1 || h
  let port := fun mask => seed row sa sc mask || (mask.testBit 1 && q)
  (port leaf1.1 && port leaf1.2) || (port leaf2.1 && port leaf2.2)

lemma left_misses_EG (sa sc : Nat) :
    outputUpper (64, 176) (8, 162) (18, 32) sa sc 80 = false := by
  rfl

lemma right_misses_EG (sa sc : Nat) :
    outputUpper (16, 224) (8, 162) (32, 66) sa sc 80 = false := by
  rfl

lemma C_irrelevant_AG (sa sc : Nat) :
    outputUpper (88, 160) (2, 40) (16, 64) sa sc 65 =
      outputUpper (88, 160) (2, 40) (16, 64) sa 0 65 := by
  rfl

lemma C_irrelevant_AH (sa sc : Nat) :
    outputUpper (88, 160) (2, 40) (16, 64) sa sc 129 =
      outputUpper (88, 160) (2, 40) (16, 64) sa 0 129 := by
  rfl

lemma middle_finite : ∀ sa : Fin 256, sa.val ≠ 0 →
    outputUpper (88, 160) (2, 40) (16, 64) sa.val 0 65 = false ∨
      outputUpper (88, 160) (2, 40) (16, 64) sa.val 0 129 = false := by
  decide +kernel

lemma middle_misses_A_edge (sa : Fin 256) (hsa : sa.val ≠ 0) (sc : Nat) :
    outputUpper (88, 160) (2, 40) (16, 64) sa.val sc 65 = false ∨
      outputUpper (88, 160) (2, 40) (16, 64) sa.val sc 129 = false := by
  rw [C_irrelevant_AG, C_irrelevant_AH]
  exact middle_finite sa hsa

def maskLE (a b : Nat) : Prop := a &&& b = a

lemma maskLE_refl (a : Nat) : maskLE a a := Nat.and_self a

lemma maskLE_trans {a b c : Nat} (hab : maskLE a b) (hbc : maskLE b c) :
    maskLE a c := by
  unfold maskLE at *
  calc
    a &&& c = (a &&& b) &&& c := by rw [hab]
    _ = a &&& (b &&& c) := Nat.and_assoc a b c
    _ = a &&& b := by rw [hbc]
    _ = a := hab

lemma maskLE_union_left (a b : Nat) : maskLE a (a ||| b) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_or]
  cases a.testBit i <;> cases b.testBit i <;> rfl

lemma maskLE_union_right (a b : Nat) : maskLE b (a ||| b) := by
  rw [Nat.or_comm]
  exact maskLE_union_left b a

lemma maskLE_bit {m n i : Nat} (hmn : maskLE m n) (hi : m.testBit i = true) :
    n.testBit i = true := by
  have h := congrArg (fun z : Nat => z.testBit i) hmn
  simp only [Nat.testBit_and, hi, Bool.true_and] at h
  exact h

lemma raw_hit_mono {row m n : Nat} (hmn : maskLE m n)
    (h : row &&& m ≠ 0) : row &&& n ≠ 0 := by
  intro hz
  apply h
  calc
    row &&& m = (row &&& m) &&& n := by
      rw [Nat.and_assoc, hmn]
    _ = (row &&& n) &&& m := by
      rw [Nat.and_assoc, Nat.and_comm m n, ← Nat.and_assoc]
    _ = 0 := by rw [hz, Nat.zero_and]

lemma seed_mono {row sa sc m n : Nat} (hmn : maskLE m n)
    (h : seed row sa sc m = true) : seed row sa sc n = true := by
  simp only [seed, Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at h ⊢
  rcases h with (h | ⟨ha, hsa⟩) | ⟨hc, hsc⟩
  · exact Or.inl (Or.inl (raw_hit_mono hmn h))
  · exact Or.inl (Or.inr ⟨ha, maskLE_trans hsa hmn⟩)
  · exact Or.inr ⟨hc, maskLE_trans hsc hmn⟩

def portUpper (row sa sc : Nat) (hp : Nat × Nat) (mask : Nat) : Bool :=
  seed row sa sc mask ||
    (mask.testBit 1 &&
      (row.testBit 1 || (seed row sa sc hp.1 && seed row sa sc hp.2)))

lemma portUpper_mono {row sa sc : Nat} {hp : Nat × Nat} {m n : Nat}
    (hmn : maskLE m n) (h : portUpper row sa sc hp m = true) :
    portUpper row sa sc hp n = true := by
  simp only [portUpper, Bool.or_eq_true, Bool.and_eq_true] at h ⊢
  rcases h with h | ⟨hb, hq⟩
  · exact Or.inl (seed_mono hmn h)
  · exact Or.inr ⟨maskLE_bit hmn hb, hq⟩

lemma portUpper_no_B (row sa sc : Nat) (hp : Nat × Nat) {mask : Nat}
    (hm : mask.testBit 1 = false) :
    portUpper row sa sc hp mask = seed row sa sc mask := by
  simp [portUpper, hm]

lemma portUpper_of_raw {row sa sc : Nat} {hp : Nat × Nat} {mask : Nat}
    (h : row &&& mask ≠ 0) : portUpper row sa sc hp mask = true := by
  simp only [portUpper, seed, Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, beq_iff_eq]
  exact Or.inl (Or.inl (Or.inl h))

lemma portUpper_of_A {row sa sc : Nat} {hp : Nat × Nat} {mask : Nat}
    (ha : row.testBit 0 = true) (hs : maskLE sa mask) :
    portUpper row sa sc hp mask = true := by
  simp only [portUpper, seed, Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, beq_iff_eq]
  exact Or.inl (Or.inl (Or.inr ⟨ha, hs⟩))

lemma portUpper_of_C {row sa sc : Nat} {hp : Nat × Nat} {mask : Nat}
    (hc : row.testBit 2 = true) (hs : maskLE sc mask) :
    portUpper row sa sc hp mask = true := by
  simp only [portUpper, seed, Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, beq_iff_eq]
  exact Or.inl (Or.inr ⟨hc, hs⟩)

lemma portUpper_or {row sa sc : Nat} {hp : Nat × Nat} {m n : Nat}
    {u v : Bool}
    (hu : u = true → portUpper row sa sc hp m = true)
    (hv : v = true → portUpper row sa sc hp n = true)
    (h : (u || v) = true) : portUpper row sa sc hp (m ||| n) = true := by
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · exact portUpper_mono (maskLE_union_left m n) (hu h)
  · exact portUpper_mono (maskLE_union_right m n) (hv h)

lemma portUpper_B_event {row sa sc : Nat} {hp : Nat × Nat} {mask : Nat}
    {u v : Bool} (hB : mask.testBit 1 = true)
    (hpL : hp.1.testBit 1 = false) (hpR : hp.2.testBit 1 = false)
    (hu : u = true → portUpper row sa sc hp hp.1 = true)
    (hv : v = true → portUpper row sa sc hp hp.2 = true)
    (h : (row.testBit 1 || (u && v)) = true) :
    portUpper row sa sc hp mask = true := by
  simp only [portUpper, hB, Bool.true_and, Bool.or_eq_true, Bool.and_eq_true]
  apply Or.inr
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · exact Or.inl h
  · simp only [Bool.and_eq_true] at h
    obtain ⟨hul, hvr⟩ := h
    exact Or.inr ⟨by simpa only [portUpper_no_B row sa sc hp hpL] using hu hul,
      by simpa only [portUpper_no_B row sa sc hp hpR] using hv hvr⟩

/-- A causal true-wire decomposition. The last alternative uses the two inputs
of the dirty AND h directly, so no bound on h itself is assumed. Zero-mask wires
need not satisfy the invariant. -/
lemma causal_payload_transport (N row sa sc : Nat) (hp : Nat × Nat)
    (masks : Nat → Nat) (values : Nat → Bool)
    (hpL : hp.1.testBit 1 = false) (hpR : hp.2.testBit 1 = false)
    (local_step : ∀ i, i < N → masks i ≠ 0 → values i = true →
      row &&& masks i ≠ 0 ∨
      (row.testBit 0 = true ∧ maskLE sa (masks i)) ∨
      (row.testBit 2 = true ∧ maskLE sc (masks i)) ∨
      (∃ j, j < i ∧ masks j ≠ 0 ∧ maskLE (masks j) (masks i) ∧ values j = true) ∨
      ((masks i).testBit 1 = true) ∧
        (row.testBit 1 = true ∨
          ∃ p q, p < i ∧ q < i ∧ masks p ≠ 0 ∧ masks q ≠ 0 ∧
            masks p = hp.1 ∧ masks q = hp.2 ∧ values p = true ∧ values q = true)) :
    ∀ i, i < N → masks i ≠ 0 → values i = true →
      portUpper row sa sc hp (masks i) = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hi hmi hvi
    rcases local_step i hi hmi hvi with hraw | ⟨ha, hsa⟩ | ⟨hc, hsc⟩ |
      ⟨j, hji, hmj, hmji, hvj⟩ | ⟨hB, hq⟩
    · exact portUpper_of_raw hraw
    · exact portUpper_of_A ha hsa
    · exact portUpper_of_C hc hsc
    · exact portUpper_mono hmji (ih j hji (Nat.lt_trans hji hi) hmj hvj)
    · rcases hq with hb | ⟨p, q, hpi, hqi, hmp, hmq, hpe, hqe, hvp, hvq⟩
      · simp only [portUpper, hB, hb, Bool.true_or, Bool.and_true, Bool.or_true]
      · have hup : portUpper row sa sc hp hp.1 = true := by
          rw [← hpe]
          exact ih p hpi (Nat.lt_trans hpi hi) hmp hvp
        have huq : portUpper row sa sc hp hp.2 = true := by
          rw [← hqe]
          exact ih q hqi (Nat.lt_trans hqi hi) hmq hvq
        exact portUpper_B_event (u := values p) (v := values q) hB hpL hpR (fun _ => hup) (fun _ => huq)
          (by simp only [hvp, hvq, Bool.true_and, Bool.or_true])

lemma outputUpper_of_ports {row sa sc : Nat} {hp leaf1 leaf2 : Nat × Nat}
    {a b c d : Bool}
    (ha : a = true → portUpper row sa sc hp leaf1.1 = true)
    (hb : b = true → portUpper row sa sc hp leaf1.2 = true)
    (hc : c = true → portUpper row sa sc hp leaf2.1 = true)
    (hd : d = true → portUpper row sa sc hp leaf2.2 = true)
    (h : ((a && b) || (c && d)) = true) :
    outputUpper hp leaf1 leaf2 sa sc row = true := by
  change ((portUpper row sa sc hp leaf1.1 && portUpper row sa sc hp leaf1.2) ||
    (portUpper row sa sc hp leaf2.1 && portUpper row sa sc hp leaf2.2)) = true
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h ⊢
  rcases h with ⟨ha', hb'⟩ | ⟨hc', hd'⟩
  · exact Or.inl ⟨ha ha', hb hb'⟩
  · exact Or.inr ⟨hc hc', hd hd'⟩

end PEqualNP.Outside.L_meta_9033_aux.K2R1BPayloadUpper
