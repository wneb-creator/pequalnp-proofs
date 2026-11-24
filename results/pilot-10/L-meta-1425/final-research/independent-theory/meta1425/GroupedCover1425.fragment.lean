def collectBits (f : Nat → Nat) : List Nat → Nat
  | [] => 0
  | w :: ws => f w ||| collectBits f ws

theorem collectBits_testBit (f : Nat → Nat) (ws : List Nat) (j : Nat) :
    (collectBits f ws).testBit j = true ↔ ∃ w ∈ ws, (f w).testBit j = true := by
  induction ws with
  | nil => simp [collectBits]
  | cons w ws ih => simp [collectBits, Nat.testBit_or, Bool.or_eq_true, ih]

def diffCov (m i : Nat) (ws : List Nat) : Nat :=
  collectBits (fun w => if w.testBit i then w ^^^ m else w) ws

def dirCov (i : Nat) (ws : List Nat) : Nat :=
  collectBits (fun w => if w.testBit i then 0 else w) ws

theorem diffCov_testBit {m i j : Nat} (hm : m.testBit j = true) (ws : List Nat) :
    (diffCov m i ws).testBit j = true ↔
      ∃ w ∈ ws, w.testBit i ≠ w.testBit j := by
  rw [diffCov, collectBits_testBit]
  apply exists_congr
  intro w
  cases hi : w.testBit i <;> cases hj : w.testBit j <;>
    simp [hi, hj, Nat.testBit_xor, hm]

theorem dirCov_testBit (i j : Nat) (ws : List Nat) :
    (dirCov i ws).testBit j = true ↔
      ∃ w ∈ ws, w.testBit i = false ∧ w.testBit j = true := by
  rw [dirCov, collectBits_testBit]
  apply exists_congr
  intro w
  cases hi : w.testBit i <;> cases hj : w.testBit j <;> simp [hi, hj]

theorem maskCovered_of_bits {a mask : Nat}
    (h : ∀ j, mask.testBit j = true → a.testBit j = true) : a &&& mask = mask := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and]
  cases hm : mask.testBit j with
  | false => simp [hm]
  | true => simp [hm, h j hm]

def diffCover (m : Nat) (groups : List (Nat × Nat)) (ws : List Nat) : Bool :=
  groups.all fun p => (diffCov m p.1 ws &&& p.2) == p.2

def dirCover (groups : List (Nat × Nat)) (ws : List Nat) : Bool :=
  groups.all fun p => (dirCov p.1 ws &&& p.2) == p.2

theorem diffCover_ok {m y s ws} (h : NatRun m y s ws)
    (groups : List (Nat × Nat))
    (hpairs : ∀ p ∈ groups, ∀ j, p.2.testBit j = true →
      m.testBit p.1 = m.testBit j ∧ m.testBit j = true ∧
      y.testBit p.1 ≠ y.testBit j) : diffCover m groups ws = true := by
  apply List.all_eq_true.2
  intro p hp
  apply beq_iff_eq.2
  apply maskCovered_of_bits
  intro j hj
  obtain ⟨he, hm, hy⟩ := hpairs p hp j hj
  apply (diffCov_testBit hm ws).2
  by_contra! hn
  exact hy (run_bits h p.1 j he hn)

theorem dirCover_of_witness (groups : List (Nat × Nat)) (ws : List Nat)
    (hw : ∀ p ∈ groups, ∀ j, p.2.testBit j = true →
      ∃ w ∈ ws, w.testBit p.1 = false ∧ w.testBit j = true) :
    dirCover groups ws = true := by
  apply List.all_eq_true.2
  intro p hp
  apply beq_iff_eq.2
  apply maskCovered_of_bits
  intro j hj
  exact (dirCov_testBit p.1 j ws).2 (hw p hp j hj)

def diffGroupsGood (width m y : Nat) (groups : List (Nat × Nat)) : Bool :=
  groups.all fun p => (p.2 < 2 ^ width) &&
    (List.range width).all fun j => !p.2.testBit j ||
      ((m.testBit p.1 == m.testBit j) && m.testBit j &&
        decide (y.testBit p.1 ≠ y.testBit j))

theorem mask_bit_lt {mask width j : Nat}
    (hm : mask < 2 ^ width) (hj : mask.testBit j = true) : j < width := by
  by_contra hn
  have hle : width ≤ j := by omega
  have hp : 2 ^ width ≤ 2 ^ j := by gcongr
  have he := Nat.testBit_eq_false_of_lt (hm.trans_le hp)
  rw [he] at hj
  contradiction

theorem diffGroupsGood_sound {width m y : Nat} {groups : List (Nat × Nat)}
    (hg : diffGroupsGood width m y groups = true) :
    ∀ p ∈ groups, ∀ j, p.2.testBit j = true →
      m.testBit p.1 = m.testBit j ∧ m.testBit j = true ∧
      y.testBit p.1 ≠ y.testBit j := by
  intro p hp j hj
  have hp' := List.all_eq_true.1 hg p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp'
  have hlt := mask_bit_lt hp'.1 hj
  have hc := List.all_eq_true.1 hp'.2 j (List.mem_range.2 hlt)
  simpa only [hj, Bool.not_true, Bool.false_or, Bool.and_eq_true,
    beq_iff_eq, decide_eq_true_eq, and_assoc] using hc

theorem diffCover_ok_of_good {width m y s ws groups}
    (h : NatRun m y s ws) (hg : diffGroupsGood width m y groups = true) :
    diffCover m groups ws = true :=
  diffCover_ok h groups (diffGroupsGood_sound hg)
