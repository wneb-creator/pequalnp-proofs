import Fast982

namespace PEqualNP.Outside.L_meta_982_aux.Finite.Symmetry

def putBits (bs : List Bool) (tail : Nat) : Nat := bs.foldr Nat.bit tail

theorem putBits_testBit (bs : List Bool) (tail j : Nat) :
    (putBits bs tail).testBit j =
      if j < bs.length then bs.getD j false else tail.testBit (j-bs.length) := by
  induction bs generalizing j with
  | nil => simp [putBits]
  | cons b bs ih =>
    cases j with
    | zero => simp [putBits]
    | succ j => simpa [putBits, Nat.testBit_bit_succ] using ih j

def permWord (width : Nat) (p : Nat → Nat) (w : Nat) : Nat :=
  putBits ((List.range width).map fun j => w.testBit (p j)) (w >>> width)

theorem permWord_testBit (width : Nat) (p : Nat → Nat) (w j : Nat) :
    (permWord width p w).testBit j = w.testBit (if j < width then p j else j) := by
  rw [permWord, putBits_testBit]
  by_cases hj : j < width
  · simp [hj]
  · simp [hj, Nat.testBit_shiftRight, Nat.add_sub_of_le (by omega : width ≤ j)]

theorem permWord_and (width : Nat) (p : Nat → Nat) (a b : Nat) :
    permWord width p (a &&& b) = permWord width p a &&& permWord width p b := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [permWord_testBit, Nat.testBit_and]

theorem permWord_or (width : Nat) (p : Nat → Nat) (a b : Nat) :
    permWord width p (a ||| b) = permWord width p a ||| permWord width p b := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [permWord_testBit, Nat.testBit_or]

theorem permWord_injective (width : Nat) (p q : Nat → Nat)
    (hq : ∀ j < width, q j < width)
    (hpq : ∀ j < width, p (q j) = j) : Function.Injective (permWord width p) := by
  intro a b h
  apply Nat.eq_of_testBit_eq
  intro j
  have hh := congrArg (fun w => (permWord width q w).testBit j) h
  simp only [permWord_testBit] at hh
  by_cases hj : j < width
  · simpa [hj, hq j hj, hpq j hj] using hh
  · simpa [hj] using hh


theorem permWord_xor (width : Nat) (p : Nat → Nat) (a b : Nat) :
    permWord width p (a ^^^ b) = permWord width p a ^^^ permWord width p b := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [permWord_testBit, Nat.testBit_xor]

theorem permWord_mask (width : Nat) (p : Nat → Nat)
    (hp : ∀ j < width, p j < width) :
    permWord width p (2^width-1) = 2^width-1 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [permWord_testBit]
  by_cases hj : j < width
  · simp [hj, Nat.testBit_two_pow_sub_one, hp j hj]
  · simp [hj]

theorem halfGoal_testBit (k j : Nat) :
    ((2^k-1) <<< k).testBit j = decide (k ≤ j ∧ j < k+k) := by
  rw [Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  apply Bool.eq_iff_iff.2
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem permWord_halfGoal (k : Nat) (p : Nat → Nat)
    (hp : ∀ j < k+k, p j < k+k)
    (hhalf : ∀ j < k+k, k ≤ p j ↔ k ≤ j) :
    permWord (k+k) p ((2^k-1) <<< k) = (2^k-1) <<< k := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [permWord_testBit]
  by_cases hj : j < k+k
  · rw [if_pos hj, halfGoal_testBit, halfGoal_testBit]
    simp [hp j hj, hj, hhalf j hj]
  · simp [hj]

def liftHalf (k : Nat) (p : Nat → Nat) (j : Nat) : Nat :=
  if j < k then p j else k + p (j-k)

theorem liftHalf_bound (k : Nat) (p : Nat → Nat)
    (hp : ∀ j < k, p j < k) (j : Nat) (hj : j < k+k) :
    liftHalf k p j < k+k := by
  unfold liftHalf
  split_ifs with h
  · have := hp j h
    omega
  · have := hp (j-k) (by omega)
    omega

theorem liftHalf_preserves (k : Nat) (p : Nat → Nat)
    (hp : ∀ j < k, p j < k) (j : Nat) (hj : j < k+k) :
    k ≤ liftHalf k p j ↔ k ≤ j := by
  unfold liftHalf
  split_ifs with h
  · have := hp j h
    omega
  · omega

theorem liftHalf_inverse (k : Nat) (p q : Nat → Nat)
    (hq : ∀ j < k, q j < k) (hpq : ∀ j < k, p (q j) = j)
    (j : Nat) (hj : j < k+k) : liftHalf k p (liftHalf k q j) = j := by
  by_cases h : j < k
  · simp [liftHalf, h, hq j h, hpq j h]
  · have hs : j-k < k := by omega
    simp only [liftHalf, h, ↓reduceIte]
    rw [if_neg (by omega : ¬ k + q (j-k) < k)]
    simp only [Nat.add_sub_cancel_left, hpq (j-k) hs]
    omega

theorem permWord_liftHalf_injective (k : Nat) (p q : Nat → Nat)
    (hq : ∀ j < k, q j < k) (hpq : ∀ j < k, p (q j) = j) :
    Function.Injective (permWord (k+k) (liftHalf k p)) :=
  permWord_injective (k+k) (liftHalf k p) (liftHalf k q)
    (liftHalf_bound k q hq) (liftHalf_inverse k p q hq hpq)

theorem permWord_liftHalf_mask (k : Nat) (p : Nat → Nat)
    (hp : ∀ j < k, p j < k) :
    permWord (k+k) (liftHalf k p) (2^(k+k)-1) = 2^(k+k)-1 :=
  permWord_mask (k+k) (liftHalf k p) (liftHalf_bound k p hp)

theorem permWord_liftHalf_goal (k : Nat) (p : Nat → Nat)
    (hp : ∀ j < k, p j < k) :
    permWord (k+k) (liftHalf k p) ((2^k-1) <<< k) = (2^k-1) <<< k :=
  permWord_halfGoal k (liftHalf k p) (liftHalf_bound k p hp) (liftHalf_preserves k p hp)

def pairPerm (cols : Nat) (p q : Nat → Nat) (j : Nat) : Nat :=
  p (j / cols) * cols + q (j % cols)

theorem pairPerm_bound (rows cols : Nat) (p q : Nat → Nat) (hc : 0 < cols)
    (hp : ∀ j < rows, p j < rows) (hq : ∀ j < cols, q j < cols)
    (j : Nat) (hj : j < rows*cols) : pairPerm cols p q j < rows*cols := by
  have hjp : j / cols < rows := (Nat.div_lt_iff_lt_mul hc).2 hj
  have hjq : j % cols < cols := Nat.mod_lt j hc
  have h1 := Nat.mul_le_mul_right cols (Nat.succ_le_of_lt (hp _ hjp))
  have h2 := hq _ hjq
  simp only [Nat.succ_mul] at h1
  unfold pairPerm
  omega

theorem pairPerm_inverse (rows cols : Nat) (p q pi qi : Nat → Nat) (hc : 0 < cols)
    (hpi : ∀ j < rows, pi j < rows) (hqi : ∀ j < cols, qi j < cols)
    (hp : ∀ j < rows, p (pi j) = j) (hq : ∀ j < cols, q (qi j) = j)
    (j : Nat) (hj : j < rows*cols) :
    pairPerm cols p q (pairPerm cols pi qi j) = j := by
  have hjp : j / cols < rows := (Nat.div_lt_iff_lt_mul hc).2 hj
  have hjq : j % cols < cols := Nat.mod_lt j hc
  have hq' := hqi _ hjq
  have hdiv : (pi (j / cols) * cols + qi (j % cols)) / cols = pi (j / cols) := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hc, Nat.div_eq_of_lt hq']
    simp
  have hmod : (pi (j / cols) * cols + qi (j % cols)) % cols = qi (j % cols) := by
    rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hq']
  simp only [pairPerm, hdiv, hmod, hp _ hjp, hq _ hjq]
  simpa [Nat.mul_comm] using Nat.div_add_mod j cols

end PEqualNP.Outside.L_meta_982_aux.Finite.Symmetry


namespace PEqualNP.Outside.L_meta_982_aux.Finite.Symmetry

open PEqualNP.Outside.L_meta_982_aux.Finite.Reduced

theorem run_map {pool : List Nat} {m y s : Nat} {ws : List Nat}
    (e : Nat → Nat) (he : Function.Injective e)
    (hi : ∀ a, e (a ^^^ m) = e a ^^^ m)
    (ha : ∀ a b, e (a &&& b) = e a &&& e b)
    (ho : ∀ a b, e (a ||| b) = e a ||| e b)
    (hy : e y = y) (hpool : pool.Subset (pool.map e))
    (h : RNatRun pool m y s ws) : RNatRun pool m y s (ws.map e) := by
  have hh : RNatRun (pool.map e) m (e y) s (ws.map e) := h.map e he hi ha ho
  rw [hy] at hh
  exact RRun.forbidden_mono hpool hh

theorem permWord_liftHalf_run (k : Nat) (p q : Nat → Nat)
    (hp : ∀ j < k, p j < k) (hq : ∀ j < k, q j < k)
    (hpq : ∀ j < k, p (q j) = j)
    {pool : List Nat} {s : Nat} {ws : List Nat}
    (hpool : pool.Subset (pool.map (permWord (k+k) (liftHalf k p))))
    (h : RNatRun pool (2^(k+k)-1) ((2^k-1) <<< k) s ws) :
    RNatRun pool (2^(k+k)-1) ((2^k-1) <<< k) s
      (ws.map (permWord (k+k) (liftHalf k p))) := by
  apply run_map (permWord (k+k) (liftHalf k p))
    (permWord_liftHalf_injective k p q hq hpq) _
    (permWord_and _ _) (permWord_or _ _) (permWord_liftHalf_goal k p hp) hpool h
  intro a
  rw [permWord_xor, permWord_liftHalf_mask k p hp]

end PEqualNP.Outside.L_meta_982_aux.Finite.Symmetry


namespace PEqualNP.Outside.L_meta_982_aux.Finite.Symmetry

theorem getD_map_lt {α β : Type} (l : List α) (f : α → β) (da : α) (db : β)
    (j : Nat) (hj : j < l.length) : (l.map f).getD j db = f (l.getD j da) := by
  rw [List.getD_eq_getElem (l.map f) db (by simpa using hj), List.getD_eq_getElem l da hj]
  simp

def fastHalfPerm (k : Nat) (p : List Nat) (word : Nat) : Nat :=
  let coordinates := p ++ p.map (fun i => k+i)
  (coordinates.map (fun i => Fast.bit word i)).foldr Nat.bit (word / 2^(k+k))

theorem halfCoords_getD (k : Nat) (p : List Nat) (hp : p.length = k)
    (j : Nat) (hj : j < k+k) :
    (p ++ p.map (fun i => k+i)).getD j 0 = liftHalf k (fun i => p.getD i 0) j := by
  by_cases hk : j < k
  · rw [List.getD_append _ _ _ _ (by omega)]
    simp [liftHalf, hk]
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    rw [getD_map_lt p (fun i => k+i) 0 0 (j-p.length) (by omega)]
    simp [liftHalf, hk, hp]

theorem fastHalfPerm_eq (k : Nat) (p : List Nat) (hp : p.length = k) (word : Nat) :
    fastHalfPerm k p word = permWord (k+k) (liftHalf k (fun i => p.getD i 0)) word := by
  apply Nat.eq_of_testBit_eq
  intro j
  change (putBits ((p ++ p.map (fun i => k+i)).map (fun i => Fast.bit word i))
    (word / 2^(k+k))).testBit j = _
  rw [putBits_testBit, permWord_testBit]
  simp only [List.length_map, List.length_append, hp]
  by_cases hj : j < k+k
  · rw [if_pos hj, if_pos hj]
    rw [getD_map_lt _ (fun i => Fast.bit word i) 0 false j (by simpa [hp] using hj)]
    rw [Fast.bit_eq, halfCoords_getD k p hp j hj]
  · rw [if_neg hj, if_neg hj, ←Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight]
    congr 1
    omega

end PEqualNP.Outside.L_meta_982_aux.Finite.Symmetry
