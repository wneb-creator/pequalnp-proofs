import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Int.Basic
import Mathlib.Computability.NFA
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.Count
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib

namespace PEqualNP.Outside.L_meta_29956_aux

def rot (k d x : Nat) : Nat :=
  ((x <<< (d % k)) ||| (x >>> (k - d % k))) % 2 ^ k

def chi (k x : Nat) : Nat :=
  (List.range k).foldl (fun acc i =>
    acc ||| ((xor (x.testBit i)
      (!(x.testBit ((i + 1) % k)) && x.testBit ((i + 2) % k))).toNat <<< i)) 0

lemma rot_lt (k d x : Nat) : rot k d x < 2 ^ k :=
  Nat.mod_lt _ (Nat.two_pow_pos k)

lemma rotate_bit {k d x i : Nat} (hx : x < 2 ^ k) (hi : i < k) :
    (rot k d x).testBit i = x.testBit ((i + k - d % k) % k) := by
  have hk : 0 < k := by omega
  have hd : d % k < k := Nat.mod_lt _ hk
  simp only [rot, Nat.testBit_mod_two_pow, hi, decide_true, Bool.true_and,
    Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  by_cases h : d % k ≤ i
  · have hz : x.testBit (k - d % k + i) = false :=
      Nat.testBit_lt_two_pow
        (hx.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))
    have he : (i + k - d % k) % k = i - d % k := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    simp [h, hz, he]
  · have he : (i + k - d % k) % k = k - d % k + i := by
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    simp [h, he]

lemma flip_bit (f : Nat → Bool) (i j : Nat) :
    ((f i).toNat <<< i).testBit j = (if j = i then f i else false) := by
  rw [Nat.testBit_shiftLeft, Nat.testBit_bool_toNat]
  rcases lt_trichotomy j i with hl | he | hg
  · simp [Nat.not_le.mpr hl, Nat.ne_of_lt hl]
  · simp [he]
  · simp [Nat.le_of_lt hg, show j-i ≠ 0 by omega, Nat.ne_of_gt hg]

lemma pack_bit (f : Nat → Bool) (l : List Nat) (acc j : Nat) :
    (l.foldl (fun z i => z ||| ((f i).toNat <<< i)) acc).testBit j =
      (acc.testBit j || (decide (j ∈ l) && f j)) := by
  induction l generalizing acc with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih, Nat.testBit_or, flip_bit]
    by_cases h : j = x
    · subst x
      cases f j <;> simp
    · simp [h]

lemma chi_bit {k j : Nat} (h : j < k) (x : Nat) :
    (chi k x).testBit j =
      xor (x.testBit j) (!(x.testBit ((j+1) % k)) && x.testBit ((j+2) % k)) := by
  simp [chi, pack_bit, h]

lemma chi_lt (k x : Nat) : chi k x < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  simp [chi, pack_bit, Nat.not_lt_of_ge hj]

def idx (k : Nat) (j : Int) : Nat := (j % (k : Int)).toNat

def bits (k x : Nat) (j : Int) : Bool := x.testBit (idx k j)

lemma idx_lt {k : Nat} (hk : 0 < k) (j : Int) : idx k j < k := by
  have h := Int.emod_lt_of_pos j (show (0 : Int) < k by omega)
  unfold idx
  omega

lemma idx_nat {k i : Nat} (hi : i < k) : idx k (i : Int) = i := by
  unfold idx
  rw [Int.emod_eq_of_lt (by omega) (by omega)]
  rfl

lemma idx_sub_small {k s : Nat} (hs : s < k) (j : Int) :
    idx k (j - (s : Int)) =
      if idx k j < s then k - s + idx k j else idx k j - s := by
  have hp : (0 : Int) < k := by omega
  have a := Int.emod_nonneg j (show (k : Int) ≠ 0 by omega)
  have b := Int.emod_lt_of_pos j hp
  unfold idx
  rw [← Int.emod_sub_emod j (k : Int) (s : Int)]
  split
  · next h =>
    rw [← Int.add_emod_left, Int.emod_eq_of_lt (by omega) (by omega)]
    omega
  · next h =>
    rw [Int.emod_eq_of_lt (by omega) (by omega)]
    omega

lemma idx_sub_mod (k s : Nat) (j : Int) :
    idx k (j - (s : Int)) = idx k (j - ((s % k : Nat) : Int)) := by
  unfold idx
  rw [Int.sub_emod, Int.sub_emod]
  simp

lemma bits_rot {k d x : Nat} (hk : 0 < k) (hx : x < 2 ^ k) (j : Int) :
    bits k (rot k d x) j = bits k x (j - (d : Int)) := by
  unfold bits
  rw [rotate_bit hx (idx_lt hk j), idx_sub_mod k d j, idx_sub_small (Nat.mod_lt d hk)]
  congr 1
  have hi := idx_lt hk j
  have hd := Nat.mod_lt d hk
  split
  · next h =>
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · next h =>
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

lemma idx_add {k : Nat} (hk : 0 < k) (j : Int) (s : Nat) :
    (idx k j + s) % k = idx k (j + (s : Int)) := by
  have a := Int.emod_nonneg j (show (k : Int) ≠ 0 by omega)
  unfold idx
  rw [← Int.emod_add_emod j (k : Int) (s : Int)]
  have eq : (j % (k : Int) + (s : Int)).toNat = (j % (k : Int)).toNat + s := by omega
  rw [@Int.toNat_emod (j % (k : Int) + (s : Int)) (k : Int) (by omega) (by omega), eq]
  rfl

lemma bits_chi {k : Nat} (hk : 0 < k) (x : Nat) (j : Int) :
    bits k (chi k x) j =
      xor (bits k x j) (!(bits k x (j+1)) && bits k x (j+2)) := by
  unfold bits
  rw [chi_bit (idx_lt hk _), idx_add hk j 1, idx_add hk j 2]
  rfl

lemma bits_xor (k x y : Nat) (j : Int) :
    bits k (x ^^^ y) j = xor (bits k x j) (bits k y j) := Nat.testBit_xor ..

lemma idx_sub_inverse {k d : Nat} (hk : 0 < k) (j : Int) :
    idx k (j - ((k - d % k : Nat) : Int)) = idx k (j + (d : Int)) := by
  have hd := Nat.mod_lt d hk
  have h : j - ((k - d % k : Nat) : Int) = j + ((d % k : Nat) : Int) - (k : Int) := by
    omega
  unfold idx
  rw [h, Int.sub_emod_right]
  simp [Int.add_emod]

lemma bits_rot_inverse {k d x : Nat} (hk : 0 < k) (hx : x < 2 ^ k) (j : Int) :
    bits k (rot k (k - d % k) x) j = bits k x (j + (d : Int)) := by
  rw [bits_rot hk hx]
  unfold bits
  rw [idx_sub_inverse hk]

def wordRun (k r : Nat) (masks : Nat → Fin (2 ^ k)) (col : Bool)
    (key name n : Nat) : Nat :=
  (List.range n).foldl (fun z j =>
    let gap : Nat := if col then 2 else 1
    let mixed := z ^^^ rot k gap z ^^^ rot k (k - gap % k) z
    chi k mixed ^^^ rot k (if col then 3 * (j + 1) + 1 else 2 * j) key ^^^
      (masks (if col then r + j else j)).val) (rot k (if col then 3 else 1) key ^^^ name)

lemma wordRun_succ (k r : Nat) (masks : Nat → Fin (2 ^ k)) (col : Bool)
    (key name n : Nat) :
    wordRun k r masks col key name (n+1) =
      let gap : Nat := if col then 2 else 1
      let z := wordRun k r masks col key name n
      let mixed := z ^^^ rot k gap z ^^^ rot k (k-gap % k) z
      chi k mixed ^^^ rot k (if col then 3*(n+1)+1 else 2*n) key ^^^
        (masks (if col then r+n else n)).val := by
  simp [wordRun, List.range_succ]

lemma wordRun_lt (k r : Nat) (masks : Nat → Fin (2 ^ k)) (col : Bool)
    (key name n : Nat) (hn : name < 2 ^ k) : wordRun k r masks col key name n < 2 ^ k := by
  cases n with
  | zero => exact Nat.xor_lt_two_pow (rot_lt ..) hn
  | succ n =>
    rw [wordRun_succ]
    exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (chi_lt ..) (rot_lt ..)) (masks _).isLt

def streamGap (col : Bool) : Int := if col then 2 else 1

def streamInitialShift (col : Bool) : Int := if col then 3 else 1

def streamScheduledShift (col : Bool) (n : Nat) : Int :=
  if col then 3 * ((n : Int) + 1) + 1 else 2 * (n : Int)

def streamMix (col : Bool) (z : Int → Bool) (i : Int) : Bool :=
  xor (xor (z i) (z (i - streamGap col))) (z (i + streamGap col))

def streamRun (col : Bool) (key name : Int → Bool) (salt : Nat → Int → Bool) :
    Nat → Int → Bool
  | 0, i => xor (key (i - streamInitialShift col)) (name i)
  | n+1, i =>
    let mixed := streamMix col (streamRun col key name salt n)
    xor (xor (xor (mixed i) (!(mixed (i+1)) && mixed (i+2)))
      (key (i - streamScheduledShift col n))) (salt n i)

lemma bits_wordRun {k : Nat} (hk : 0 < k) (r : Nat) (masks : Nat → Fin (2 ^ k))
    (col : Bool) (key name : Nat) (hkey : key < 2 ^ k) (hname : name < 2 ^ k)
    (n : Nat) (i : Int) :
    bits k (wordRun k r masks col key name n) i =
      streamRun col (bits k key) (bits k name)
        (fun j => bits k (masks (if col then r+j else j)).val) n i := by
  induction n generalizing i with
  | zero =>
    change bits k (rot k (if col then 3 else 1) key ^^^ name) i = _
    rw [bits_xor, bits_rot hk hkey]
    cases col <;> rfl
  | succ n ih =>
    rw [wordRun_succ]
    dsimp only
    rw [bits_xor, bits_xor, bits_chi hk, bits_rot hk hkey]
    have hm (j : Int) :
        bits k (wordRun k r masks col key name n ^^^
          rot k (if col then 2 else 1) (wordRun k r masks col key name n) ^^^
          rot k (k - (if col then 2 else 1) % k) (wordRun k r masks col key name n)) j =
          streamMix col (streamRun col (bits k key) (bits k name)
            (fun a => bits k (masks (if col then r+a else a)).val) n) j := by
      rw [bits_xor, bits_xor, bits_rot hk (wordRun_lt _ _ _ _ _ _ _ hname),
        bits_rot_inverse hk (wordRun_lt _ _ _ _ _ _ _ hname)]
      rw [ih, ih, ih]
      cases col <;> rfl
    simp only [hm]
    unfold streamRun
    congr 2
    congr 1
    cases col <;> simp [streamScheduledShift, Int.natCast_add, Int.natCast_mul]

end PEqualNP.Outside.L_meta_29956_aux

namespace PEqualNP.Outside.L_meta_29956_aux

lemma high_eq_iff {k h x a : Nat} (hh : h ≤ k) (hx : x < 2 ^ k) (ha : a < 2 ^ h) :
    x >>> (k-h) = a ↔
      ∀ i : Nat, i < k → k-h ≤ i → x.testBit i = a.testBit (i-(k-h)) := by
  constructor
  · intro he i hi hlow
    have hb := congrArg (fun z : Nat => z.testBit (i-(k-h))) he
    rw [Nat.testBit_shiftRight] at hb
    have hs : k-h + (i-(k-h)) = i := by omega
    simpa only [hs] using hb
  · intro he
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_shiftRight]
    by_cases hj : j < h
    · have hjk : k-h+j < k := by omega
      have hs : k-h+j-(k-h) = j := by omega
      simpa only [hs] using he (k-h+j) hjk (by omega)
    · have h1 : x.testBit (k-h+j) = false :=
        Nat.testBit_lt_two_pow (hx.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))
      have h2 : a.testBit j = false :=
        Nat.testBit_lt_two_pow (ha.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))
      rw [h1, h2]

lemma idx_nat_sub {k pos d : Nat} (hpos : pos < k) :
    idx k ((pos : Int) - (d : Int)) = (pos+k-d % k) % k := by
  have hk : 0 < k := by omega
  have hd := Nat.mod_lt d hk
  rw [idx_sub_mod k d, idx_sub_small hd, idx_nat hpos]
  symm
  split
  · next h =>
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · next h =>
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

lemma idx_sub_idx {k : Nat} (hk : 0 < k) (i d : Int) :
    idx k ((idx k i : Int) - d) = idx k (i-d) := by
  have hn := Int.emod_nonneg i (show (k : Int) ≠ 0 by omega)
  simp only [idx, Int.toNat_of_nonneg hn, Int.emod_sub_emod]

lemma high_eq_cyclic_iff {k h x a : Nat} (hk : 0 < k) (hh : h ≤ k)
    (hx : x < 2 ^ k) (ha : a < 2 ^ h) (d : Nat) :
    x >>> (k-h) = a ↔
      ∀ pos : Nat, pos < k →
        k-h ≤ (pos+k-d % k) % k →
          bits k x ((pos : Int) - (d : Int)) = a.testBit ((pos+k-d % k) % k-(k-h)) := by
  rw [high_eq_iff hh hx ha]
  constructor
  · intro he pos hpos hlow
    simpa only [bits, idx_nat_sub hpos] using he ((pos+k-d % k) % k) (Nat.mod_lt _ hk) hlow
  · intro he i hi hlow
    let pos : Nat := idx k ((i : Int) + (d : Int))
    have hpos : pos < k := idx_lt hk _
    have heq : idx k ((pos : Int) - (d : Int)) = i := by
      rw [idx_sub_idx hk, Int.add_sub_cancel, idx_nat hi]
    have hsite : (pos+k-d % k) % k = i := by
      rw [← idx_nat_sub hpos, heq]
    have hz := he pos hpos (by simpa only [hsite] using hlow)
    simpa only [bits, heq, hsite] using hz

lemma output_wordRun_iff {k h : Nat} (hk : 0 < k) (hh : h ≤ k)
    (r : Nat) (masks : Nat → Fin (2 ^ k)) (col : Bool)
    (key name : Fin (2 ^ k)) (target : Fin (2 ^ h)) :
    wordRun k r masks col key.val name.val r >>> (k-h) = target.val ↔
      ∀ pos : Nat, pos < k →
        k-h ≤ (pos+k-(4*r) % k) % k →
          streamRun col (bits k key.val) (bits k name.val)
            (fun j => bits k (masks (if col then r+j else j)).val)
            r ((pos : Int) - ((4*r : Nat) : Int)) =
              target.val.testBit ((pos+k-(4*r) % k) % k-(k-h)) := by
  rw [high_eq_cyclic_iff hk hh (wordRun_lt _ _ _ _ _ _ _ name.isLt) target.isLt (4*r)]
  simp only [bits_wordRun hk r masks col key.val name.val key.isLt name.isLt]

lemma shared_row_iff {k h : Nat} (hk : 0 < k) (hh : h ≤ k)
    (r : Nat) (masks : Nat → Fin (2 ^ k))
    (x y : Fin (2 ^ k)) (a c : Fin (2 ^ h)) :
    (∃ key : Fin (2 ^ k),
      wordRun k r masks false key.val x.val r >>> (k-h) = a.val ∧
      wordRun k r masks true key.val y.val r >>> (k-h) = c.val) ↔
    ∃ key : Fin (2 ^ k), ∀ pos : Nat, pos < k →
      k-h ≤ (pos+k-(4*r) % k) % k →
        streamRun false (bits k key.val) (bits k x.val)
          (fun j => bits k (masks j).val) r ((pos : Int) - ((4*r : Nat) : Int)) =
            a.val.testBit ((pos+k-(4*r) % k) % k-(k-h)) ∧
        streamRun true (bits k key.val) (bits k y.val)
          (fun j => bits k (masks (r+j)).val) r ((pos : Int) - ((4*r : Nat) : Int)) =
            c.val.testBit ((pos+k-(4*r) % k) % k-(k-h)) := by
  simp only [output_wordRun_iff hk hh, Bool.false_eq_true, ite_false, ite_true]
  constructor
  · rintro ⟨key, hx, hy⟩
    exact ⟨key, fun pos hpos hactive => ⟨hx pos hpos hactive, hy pos hpos hactive⟩⟩
  · rintro ⟨key, hkey⟩
    exact ⟨key, fun pos hpos hactive => (hkey pos hpos hactive).1,
      fun pos hpos hactive => (hkey pos hpos hactive).2⟩

end PEqualNP.Outside.L_meta_29956_aux

namespace PEqualNP.Outside.L_meta_29956_aux

def h6Gap (col : Bool) : Int := if col then 2 else 1

def h6InitialShift (col : Bool) : Int := if col then 3 else 1

def h6ScheduledShift (col : Bool) (n : Nat) : Int :=
  if col then 3 * (n + 1 : Nat) + 1 else 2 * n

def h6Mix (col : Bool) (z : Int → Bool) (i : Int) : Bool :=
  xor (xor (z i) (z (i - h6Gap col))) (z (i + h6Gap col))

def h6Run (col : Bool) (key name : Int → Bool) (salt : Nat → Int → Bool) :
    Nat → Int → Bool
  | 0, i => xor (key (i - h6InitialShift col)) (name i)
  | n + 1, i =>
    let mixed := h6Mix col (h6Run col key name salt n)
    xor (xor (xor (mixed i) (!(mixed (i + 1)) && mixed (i + 2)))
      (key (i - h6ScheduledShift col n))) (salt n i)

lemma h6Run_local (col : Bool) (key name key' name' : Int → Bool)
    (salt salt' : Nat → Int → Bool) (n : Nat) (i : Int)
    (hkey : ∀ j, i - (3 * (n : Int) + 3) ≤ j → j ≤ i + 4 * (n : Int) →
      key j = key' j)
    (hname : ∀ j, i - 2 * (n : Int) ≤ j → j ≤ i + 4 * (n : Int) →
      name j = name' j)
    (hsalt : ∀ m < n, ∀ j,
      i - (3 * (n : Int) + 3) ≤ j → j ≤ i + 4 * (n : Int) →
      salt m j = salt' m j) :
    h6Run col key name salt n i = h6Run col key' name' salt' n i := by
  induction n generalizing i with
  | zero =>
    simp only [h6Run]
    rw [hkey (i - h6InitialShift col), hname i]
    all_goals cases col <;> simp [h6InitialShift] <;> omega
  | succ n ih =>
    have hz : ∀ j, i - 2 ≤ j → j ≤ i + 4 →
        h6Run col key name salt n j = h6Run col key' name' salt' n j := by
      intro j hj₁ hj₂
      apply ih
      · intro t ht₁ ht₂
        apply hkey <;> omega
      · intro t ht₁ ht₂
        apply hname <;> omega
      · intro m hm t ht₁ ht₂
        apply hsalt m (by omega) <;> omega
    have hmix : ∀ j, i ≤ j → j ≤ i + 2 →
        h6Mix col (h6Run col key name salt n) j =
          h6Mix col (h6Run col key' name' salt' n) j := by
      intro j hj₁ hj₂
      unfold h6Mix
      rw [hz j (by omega) (by omega), hz (j - h6Gap col), hz (j + h6Gap col)]
      all_goals cases col <;> simp [h6Gap] <;> omega
    simp only [h6Run]
    rw [hmix i (by omega) (by omega), hmix (i + 1) (by omega) (by omega),
      hmix (i + 2) (by omega) (by omega),
      hkey (i - h6ScheduledShift col n), hsalt n (by omega) i]
    all_goals cases col <;> simp [h6ScheduledShift] <;> omega

lemma h6Run_window (col : Bool) (key name key' name' : Int → Bool)
    (salt salt' : Nat → Int → Bool) (r : Nat) (t : Int)
    (hkey : ∀ d : Nat, d ≤ 7 * r + 3 → key (t - d) = key' (t - d))
    (hname : ∀ d : Nat, d ≤ 6 * r → name (t - d) = name' (t - d))
    (hsalt : ∀ m < r, ∀ d : Nat, d ≤ 7 * r + 3 →
      salt m (t - d) = salt' m (t - d)) :
    h6Run col key name salt r (t - 4 * r) =
      h6Run col key' name' salt' r (t - 4 * r) := by
  apply h6Run_local
  · intro j hj₁ hj₂
    have hd : 0 ≤ t - j := by omega
    have heq : t - ((t - j).toNat : Int) = j := by omega
    simpa only [heq] using hkey (t - j).toNat (by omega)
  · intro j hj₁ hj₂
    have hd : 0 ≤ t - j := by omega
    have heq : t - ((t - j).toNat : Int) = j := by omega
    simpa only [heq] using hname (t - j).toNat (by omega)
  · intro m hm j hj₁ hj₂
    have hd : 0 ≤ t - j := by omega
    have heq : t - ((t - j).toNat : Int) = j := by omega
    simpa only [heq] using hsalt m hm (t - j).toNat (by omega)

def h6WindowExtend (width : Nat) (w : Fin (width + 1) → Bool) (i : Int) : Bool :=
  if hi : (-i).toNat ≤ width then w ⟨(-i).toNat, by omega⟩ else false

lemma h6WindowExtend_at (width d : Nat) (w : Fin (width + 1) → Bool)
    (hd : d ≤ width) :
    h6WindowExtend width w (-(d : Int)) = w ⟨d, by omega⟩ := by
  simp [h6WindowExtend, hd]

def h6LocalEval (r : Nat) (col : Bool)
    (key : Fin (7 * r + 3 + 1) → Bool) (name : Fin (6 * r + 1) → Bool)
    (salt : Fin r → Fin (7 * r + 3 + 1) → Bool) : Bool :=
  h6Run col (h6WindowExtend (7 * r + 3) key) (h6WindowExtend (6 * r) name)
    (fun j i => if hj : j < r then h6WindowExtend (7 * r + 3) (salt ⟨j, hj⟩) i
      else false) r (-4 * (r : Int))

lemma h6LocalEval_correct_zero (r : Nat) (col : Bool)
    (key name : Int → Bool) (salt : Nat → Int → Bool) :
    h6LocalEval r col (fun d => key (-(d.val : Int)))
      (fun d => name (-(d.val : Int)))
      (fun j d => salt j.val (-(d.val : Int))) =
      h6Run col key name salt r (-4 * (r : Int)) := by
  unfold h6LocalEval
  have h := h6Run_window col
    (h6WindowExtend (7 * r + 3) (fun d => key (-(d.val : Int))))
    (h6WindowExtend (6 * r) (fun d => name (-(d.val : Int)))) key name
    (fun j i => if hj : j < r then
      h6WindowExtend (7 * r + 3) (fun d => salt j (-(d.val : Int))) i else false)
    salt r 0
  have hpos : (0 : Int) - 4 * r = -4 * (r : Int) := by omega
  rw [hpos] at h
  apply h
  · intro d hd
    simp only [Int.zero_sub]
    exact h6WindowExtend_at _ _ _ hd
  · intro d hd
    simp only [Int.zero_sub]
    exact h6WindowExtend_at _ _ _ hd
  · intro j hj d hd
    simp only [dite_eq_left hj, Int.zero_sub]
    exact h6WindowExtend_at _ _ _ hd

lemma h6Run_translate (col : Bool) (key name : Int → Bool)
    (salt : Nat → Int → Bool) (t : Int) (n : Nat) (i : Int) :
    h6Run col (fun j => key (t + j)) (fun j => name (t + j))
      (fun m j => salt m (t + j)) n i = h6Run col key name salt n (t + i) := by
  induction n generalizing i with
  | zero =>
    simp [h6Run, Int.add_sub_assoc]
  | succ n ih =>
    have hm : ∀ j,
        h6Mix col (h6Run col (fun j => key (t + j)) (fun j => name (t + j))
          (fun m j => salt m (t + j)) n) j =
        h6Mix col (h6Run col key name salt n) (t + j) := by
      intro j
      simp only [h6Mix, ih, Int.add_sub_assoc, Int.add_assoc]
    simp only [h6Run, hm, Int.add_sub_assoc, Int.add_assoc]

lemma h6LocalEval_correct (r : Nat) (col : Bool)
    (key name : Int → Bool) (salt : Nat → Int → Bool) (t : Int) :
    h6LocalEval r col (fun d => key (t - d.val))
      (fun d => name (t - d.val))
      (fun j d => salt j.val (t - d.val)) =
      h6Run col key name salt r (t - 4 * r) := by
  have h := h6LocalEval_correct_zero r col (fun i => key (t + i))
    (fun i => name (t + i)) (fun j i => salt j (t + i))
  rw [h6Run_translate] at h
  simpa only [Int.neg_mul, Int.sub_eq_add_neg] using h

def h6CurrentWindow (width : Nat) (history : Fin width → Bool) (incoming : Bool) :
    Fin (width + 1) → Bool := Fin.cases incoming history

lemma h6CurrentWindow_sample (width : Nat) (s : Int → Bool) (t : Int) :
    h6CurrentWindow width (fun d => s (t - (d.val + 1))) (s t) =
      fun d => s (t - d.val) := by
  funext d
  cases d using Fin.cases with
  | zero => simp [h6CurrentWindow]
  | succ d => simp [h6CurrentWindow]

abbrev h6History (r : Nat) :=
  (Fin (6 * r) → Bool) × (Fin (6 * r) → Bool) × (Fin (7 * r + 3) → Bool)

def h6SampleHistory (r : Nat) (key rowName colName : Int → Bool) (t : Int) :
    h6History r :=
  (fun d => rowName (t - (d.val + 1)),
    fun d => colName (t - (d.val + 1)), fun d => key (t - (d.val + 1)))

def h6Valid (r : Nat) (salt : Fin (2 * r) → Fin (7 * r + 3 + 1) → Bool)
    (active a c : Bool) (history : h6History r) (rowBit colBit keyBit : Bool) : Bool :=
  if active then
    (h6LocalEval r false (h6CurrentWindow _ history.2.2 keyBit)
        (h6CurrentWindow _ history.1 rowBit)
        (fun j => salt ⟨j.val, by omega⟩) == a) &&
    (h6LocalEval r true (h6CurrentWindow _ history.2.2 keyBit)
        (h6CurrentWindow _ history.2.1 colBit)
        (fun j => salt ⟨r + j.val, by omega⟩) == c)
  else true

lemma h6Valid_sample (r : Nat) (key rowName colName : Int → Bool)
    (masks : Nat → Int → Bool) (t : Int) (active a c : Bool) :
    h6Valid r (fun bank off => masks bank.val (t - off.val)) active a c
      (h6SampleHistory r key rowName colName t) (rowName t) (colName t) (key t) =
    if active then
      (h6Run false key rowName masks r (t - 4 * r) == a) &&
      (h6Run true key colName (fun j => masks (r + j)) r (t - 4 * r) == c)
    else true := by
  unfold h6Valid h6SampleHistory
  simp only [h6CurrentWindow_sample, h6LocalEval_correct]
  rw [h6LocalEval_correct r true key colName (fun j => masks (r + j)) t]

end PEqualNP.Outside.L_meta_29956_aux

namespace PEqualNP.Outside.L_meta_29956_aux

lemma h6Run_eq_streamRun (col : Bool) (key name : Int → Bool)
    (salt : Nat → Int → Bool) (n : Nat) (i : Int) :
    h6Run col key name salt n i = streamRun col key name salt n i := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    simp only [h6Run, streamRun, h6Mix, streamMix, ih]
    cases col <;> simp [h6ScheduledShift, streamScheduledShift, h6Gap, streamGap]

lemma h6Valid_wordRun {k : Nat} (hk : 0 < k) (r : Nat)
    (masks : Nat → Fin (2 ^ k)) (key rowName colName : Fin (2 ^ k))
    (t : Int) (active a c : Bool) :
    h6Valid r (fun bank off => bits k (masks bank.val).val (t - off.val)) active a c
      (h6SampleHistory r (bits k key.val) (bits k rowName.val) (bits k colName.val) t)
      (bits k rowName.val t) (bits k colName.val t) (bits k key.val t) =
    if active then
      (bits k (wordRun k r masks false key.val rowName.val r) (t - 4 * r) == a) &&
      (bits k (wordRun k r masks true key.val colName.val r) (t - 4 * r) == c)
    else true := by
  rw [h6Valid_sample r (bits k key.val) (bits k rowName.val) (bits k colName.val)
    (fun j => bits k (masks j).val) t active a c]
  simp only [h6Run_eq_streamRun]
  rw [bits_wordRun hk r masks false key.val rowName.val key.isLt rowName.isLt,
    bits_wordRun hk r masks true key.val colName.val key.isLt colName.isLt]
  rfl

lemma h6_idx_prev {k pos : Nat} (hpos : pos < k) (d : Nat) :
    idx k ((pos : Int) - (d : Int)) = (pos + k - d % k) % k := by
  have hk : 0 < k := by omega
  have hd : d % k < k := Nat.mod_lt _ hk
  rw [idx_sub_mod k d (pos : Int), idx_sub_small hd, idx_nat hpos]
  split
  · next h =>
    rw [Nat.mod_eq_of_lt (show pos + k - d % k < k by omega)]
    omega
  · next h =>
    have heq : pos + k - d % k = (pos - d % k) + k := by omega
    have hsmall : pos - d % k < k := by omega
    rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt hsmall]

lemma h6_bits_prev {k pos : Nat} (hpos : pos < k) (d x : Nat) :
    bits k x ((pos : Int) - (d : Int)) = x.testBit ((pos + k - d % k) % k) := by
  unfold bits
  rw [h6_idx_prev hpos]

lemma h6SampleHistory_nat {k pos : Nat} (hpos : pos < k) (r key rowName colName : Nat) :
    h6SampleHistory r (bits k key) (bits k rowName) (bits k colName) (pos : Int) =
      ((fun d => rowName.testBit ((pos + k - (d.val + 1) % k) % k)),
        (fun d => colName.testBit ((pos + k - (d.val + 1) % k) % k)),
        (fun d => key.testBit ((pos + k - (d.val + 1) % k) % k))) := by
  unfold h6SampleHistory
  apply Prod.ext
  · funext d
    simpa only [Int.natCast_add, Int.natCast_one] using
      h6_bits_prev hpos (d.val + 1) rowName
  · apply Prod.ext
    · funext d
      simpa only [Int.natCast_add, Int.natCast_one] using
        h6_bits_prev hpos (d.val + 1) colName
    · funext d
      simpa only [Int.natCast_add, Int.natCast_one] using
        h6_bits_prev hpos (d.val + 1) key

lemma h6Valid_nat {k pos : Nat} (hpos : pos < k) (r : Nat)
    (masks : Nat → Fin (2 ^ k)) (key rowName colName : Fin (2 ^ k))
    (active a c : Bool) :
    h6Valid r (fun bank off => (masks bank.val).val.testBit ((pos + k - off.val % k) % k))
      active a c
      ((fun d => rowName.val.testBit ((pos + k - (d.val + 1) % k) % k)),
        (fun d => colName.val.testBit ((pos + k - (d.val + 1) % k) % k)),
        (fun d => key.val.testBit ((pos + k - (d.val + 1) % k) % k)))
      (rowName.val.testBit pos) (colName.val.testBit pos) (key.val.testBit pos) =
    if active then
      ((wordRun k r masks false key.val rowName.val r).testBit ((pos + k - (4*r) % k) % k) == a) &&
      ((wordRun k r masks true key.val colName.val r).testBit ((pos + k - (4*r) % k) % k) == c)
    else true := by
  have h := h6Valid_wordRun (by omega : 0 < k) r masks key rowName colName
    (pos : Int) active a c
  rw [h6SampleHistory_nat hpos] at h
  have hb (x : Nat) : bits k x (pos : Int) = x.testBit pos := by
    simp only [bits, idx_nat hpos]
  have hout (x : Nat) : bits k x ((pos : Int) - 4 * (r : Int)) =
      x.testBit ((pos + k - (4*r) % k) % k) := by
    simpa [Int.natCast_mul] using h6_bits_prev hpos (4*r) x
  simpa only [h6_bits_prev hpos, hb, hout] using h


end PEqualNP.Outside.L_meta_29956_aux

namespace PEqualNP.Outside.L_meta_29956_aux

def physicalValid {k h : Nat} (r : Nat) (masks : Nat → Fin (2 ^ k))
    (a c : Fin (2 ^ h)) (key rowName colName : Fin (2 ^ k)) (pos : Nat) : Bool :=
  let site := (pos+k-(4*r) % k) % k
  h6Valid r
    (fun bank off => (masks bank.val).val.testBit ((pos+k-off.val % k) % k))
    (decide (k-h ≤ site)) (a.val.testBit (site-(k-h))) (c.val.testBit (site-(k-h)))
    (h6SampleHistory r (bits k key.val) (bits k rowName.val) (bits k colName.val) (pos : Int))
    (rowName.val.testBit pos) (colName.val.testBit pos) (key.val.testBit pos)

lemma physicalValid_iff {k h : Nat} (r : Nat) (masks : Nat → Fin (2 ^ k))
    (a c : Fin (2 ^ h)) (key rowName colName : Fin (2 ^ k)) (pos : Nat) (hpos : pos < k) :
    physicalValid r masks a c key rowName colName pos = true ↔
      k-h ≤ (pos+k-(4*r) % k) % k →
        streamRun false (bits k key.val) (bits k rowName.val)
          (fun j => bits k (masks j).val) r ((pos : Int) - ((4*r : Nat) : Int)) =
            a.val.testBit ((pos+k-(4*r) % k) % k-(k-h)) ∧
        streamRun true (bits k key.val) (bits k colName.val)
          (fun j => bits k (masks (r+j)).val) r ((pos : Int) - ((4*r : Nat) : Int)) =
            c.val.testBit ((pos+k-(4*r) % k) % k-(k-h)) := by
  have he := h6Valid_sample r (bits k key.val) (bits k rowName.val) (bits k colName.val)
    (fun j => bits k (masks j).val) (pos : Int)
    (decide (k-h ≤ (pos+k-(4*r) % k) % k))
    (a.val.testBit ((pos+k-(4*r) % k) % k-(k-h)))
    (c.val.testBit ((pos+k-(4*r) % k) % k-(k-h)))
  rw [h6Run_eq_streamRun, h6Run_eq_streamRun] at he
  have hcast : (4 : Int) * (r : Int) = ((4*r : Nat) : Int) := by omega
  rw [hcast] at he
  have hvalid : physicalValid r masks a c key rowName colName pos =
      if decide (k-h ≤ (pos+k-(4*r) % k) % k) then
        (streamRun false (bits k key.val) (bits k rowName.val)
          (fun j => bits k (masks j).val) r ((pos : Int) - ((4*r : Nat) : Int)) ==
            a.val.testBit ((pos+k-(4*r) % k) % k-(k-h))) &&
        (streamRun true (bits k key.val) (bits k colName.val)
          (fun j => bits k (masks (r+j)).val) r ((pos : Int) - ((4*r : Nat) : Int)) ==
            c.val.testBit ((pos+k-(4*r) % k) % k-(k-h)))
      else true := by
    simpa only [physicalValid, bits, idx_nat_sub hpos, idx_nat hpos] using he
  rw [hvalid]
  by_cases hactive : k-h ≤ (pos+k-(4*r) % k) % k <;> simp [hactive]

lemma row_iff_physicalValid {k h : Nat} (hk : 0 < k) (hh : h ≤ k)
    (r : Nat) (masks : Nat → Fin (2 ^ k)) (x y : Fin (2 ^ k)) (a c : Fin (2 ^ h)) :
    (∃ key : Fin (2 ^ k),
      wordRun k r masks false key.val x.val r >>> (k-h) = a.val ∧
      wordRun k r masks true key.val y.val r >>> (k-h) = c.val) ↔
    ∃ key : Fin (2 ^ k), ∀ pos : Nat, pos < k →
      physicalValid r masks a c key x y pos = true := by
  rw [shared_row_iff hk hh]
  constructor
  · rintro ⟨key, hkey⟩
    exact ⟨key, fun pos hpos => (physicalValid_iff r masks a c key x y pos hpos).mpr
      (hkey pos hpos)⟩
  · rintro ⟨key, hkey⟩
    exact ⟨key, fun pos hpos => (physicalValid_iff r masks a c key x y pos hpos).mp
      (hkey pos hpos)⟩

end PEqualNP.Outside.L_meta_29956_aux

namespace PEqualNP.Outside.L_meta_29956_aux

def helper4Run {A B H : Type} (next : H → A → B → H)
    (valid : H → A → B → Prop) : List A → H → H → Prop
  | [], s, t => s = t
  | a :: w, s, t => ∃ b, valid s a b ∧ helper4Run next valid w (next s a b) t

def helper4CycleNFA {A B H : Type} (next : H → A → B → H)
    (valid : H → A → B → Prop) : NFA A (H × H) where
  step s a := {t | t.1 = s.1 ∧ ∃ b, valid s.2 a b ∧ t.2 = next s.2 a b}
  start := {s | s.1 = s.2}
  accept := {s | s.1 = s.2}

lemma helper4CycleNFA_eval {A B H : Type} (next : H → A → B → H)
    (valid : H → A → B → Prop) (w : List A) (h h' s t : H) :
    (h', t) ∈ (helper4CycleNFA next valid).evalFrom {(h, s)} w ↔
      h' = h ∧ helper4Run next valid w s t := by
  induction w generalizing h h' s t with
  | nil => simp [helper4Run, eq_comm]
  | cons a w ih =>
    rw [NFA.evalFrom_cons, NFA.stepSet_singleton, NFA.mem_evalFrom_iff_exists]
    constructor
    · rintro ⟨q, hq, ht⟩
      rcases hq with ⟨hqh, b, hb, hqb⟩
      rcases (ih q.1 h' q.2 t).mp ht with ⟨hh', hrun⟩
      exact ⟨hh'.trans hqh, b, hb, hqb ▸ hrun⟩
    · rintro ⟨hh', b, hb, hrun⟩
      refine ⟨(h, next s a b), ?_, ?_⟩
      · exact ⟨rfl, b, hb, rfl⟩
      · exact (ih h h' (next s a b) t).mpr ⟨hh', hrun⟩

lemma helper4CycleNFA_accepts {A B H : Type} (next : H → A → B → H)
    (valid : H → A → B → Prop) (w : List A) :
    w ∈ (helper4CycleNFA next valid).accepts ↔
      ∃ h, helper4Run next valid w h h := by
  rw [NFA.mem_accepts]
  constructor
  · rintro ⟨⟨i, t⟩, hit, hpath⟩
    rcases NFA.mem_evalFrom_iff_exists.mp hpath with ⟨⟨j, s⟩, hjs, hpath⟩
    have hit : i = t := hit
    have hjs : j = s := hjs
    rcases (helper4CycleNFA_eval next valid w j i s t).mp hpath with ⟨hij, hrun⟩
    have hst : s = t := hjs.symm.trans (hij.symm.trans hit)
    exact ⟨s, hst.symm ▸ hrun⟩
  · rintro ⟨h, hrun⟩
    refine ⟨(h, h), rfl, ?_⟩
    apply NFA.mem_evalFrom_iff_exists.mpr
    refine ⟨(h, h), rfl, ?_⟩
    exact (helper4CycleNFA_eval next valid w h h h h).mpr ⟨rfl, hrun⟩

lemma helper4CycleDFA_accepts {A B H : Type} (next : H → A → B → H)
    (valid : H → A → B → Prop) (w : List A) :
    w ∈ (helper4CycleNFA next valid).toDFA.accepts ↔
      ∃ h, helper4Run next valid w h h := by
  rw [NFA.toDFA_correct, helper4CycleNFA_accepts]

lemma helper4CycleDFA_card (H : Type) [Fintype H] :
    Fintype.card (Set (H × H)) = 2 ^ (Fintype.card H * Fintype.card H) := by
  simp

lemma helper4Run_trace {A B H : Type} (next : H → A → B → H)
    (valid : H → A → B → Prop) :
    ∀ (n : ℕ) (word : Fin n → A) (s t : H),
    helper4Run next valid (List.ofFn word) s t ↔
      ∃ (bits : Fin n → B) (hist : Fin (n + 1) → H),
        hist 0 = s ∧ hist (Fin.last n) = t ∧
        ∀ i : Fin n, valid (hist i.castSucc) (word i) (bits i) ∧
          hist i.succ = next (hist i.castSucc) (word i) (bits i) := by
  intro n
  induction n with
  | zero =>
    intro word s t
    simp only [List.ofFn_zero, helper4Run]
    constructor
    · intro h
      exact ⟨Fin.elim0, fun _ => s, rfl, h, fun i => Fin.elim0 i⟩
    · rintro ⟨bits, hist, hs, ht, hstep⟩
      exact hs.symm.trans ht
  | succ n ih =>
    intro word s t
    rw [List.ofFn_succ]
    change (∃ b, valid s (word 0) b ∧
      helper4Run next valid (List.ofFn (fun i => word i.succ)) (next s (word 0) b) t) ↔ _
    constructor
    · rintro ⟨b, hb, hrun⟩
      rcases (ih (fun i => word i.succ) (next s (word 0) b) t).mp hrun with
        ⟨bits, hist, hs, ht, hstep⟩
      refine ⟨Fin.cons b bits, Fin.cons s hist, by simp, by simpa using ht, ?_⟩
      intro i
      refine Fin.cases ?_ ?_ i
      · constructor
        · simpa using hb
        · simpa using hs
      · intro j
        simpa using hstep j
    · rintro ⟨bits, hist, hs, ht, hstep⟩
      have hzero := hstep 0
      refine ⟨bits 0, ?_, ?_⟩
      · simpa [hs] using hzero.1
      · apply (ih (fun i => word i.succ) (next s (word 0) (bits 0)) t).mpr
        refine ⟨Fin.tail bits, Fin.tail hist, ?_, ?_, ?_⟩
        · simpa [Fin.tail, hs] using hzero.2
        · simpa [Fin.tail] using ht
        · intro j
          simpa [Fin.tail] using hstep j.succ



lemma h4_cyclic_window_forward
    {α : Type*} (k n : ℕ) (hk : 0 < k)
    (window : ℕ → ℕ → α)
    (hshift : ∀ t d, t < k → d < n →
      window ((t + 1) % k) (d + 1) = window t d) :
    ∀ d, d ≤ n → ∀ t, t < k →
      window ((t + d) % k) d = window t 0 := by
  intro d hd
  induction d with
  | zero =>
      intro t ht
      simp [Nat.mod_eq_of_lt ht]
  | succ d ih =>
      intro t ht
      have hdn : d < n := by omega
      have hmod : (t + (d + 1)) % k = (((t + d) % k) + 1) % k := by
        rw [← Nat.add_assoc, Nat.mod_add_mod]
      rw [hmod, hshift ((t + d) % k) d (Nat.mod_lt _ hk) hdn]
      exact ih (by omega) t ht

lemma h4_prev_add_mod
    (k pos d : ℕ) (hk : 0 < k) (hpos : pos < k) :
    (((pos + k - d % k) % k) + d) % k = pos := by
  have hsub : d % k ≤ pos + k := by
    have := Nat.mod_lt d hk
    omega
  calc
    (((pos + k - d % k) % k) + d) % k =
        ((pos + k - d % k) + d % k) % k := by
          simp [Nat.add_mod]
    _ = (pos + k) % k := by rw [Nat.sub_add_cancel hsub]
    _ = pos := by simp [Nat.mod_eq_of_lt hpos]

lemma h4_cyclic_window_backward
    {α : Type*} (k n : ℕ) (hk : 0 < k)
    (window : ℕ → ℕ → α)
    (hshift : ∀ t d, t < k → d < n →
      window ((t + 1) % k) (d + 1) = window t d)
    (pos d : ℕ) (hpos : pos < k) (hd : d ≤ n) :
    window pos d = window ((pos + k - d % k) % k) 0 := by
  have h := h4_cyclic_window_forward k n hk window hshift d hd
    ((pos + k - d % k) % k) (Nat.mod_lt _ hk)
  rwa [h4_prev_add_mod k pos d hk hpos] at h

lemma h4_closed_window_path
    {α : Type*} (k n : ℕ) (hk : 0 < k)
    (states : ℕ → ℕ → α) (bits : ℕ → α)
    (hclosure : states k = states 0)
    (hstep : ∀ t d, t < k → d < n →
      states (t + 1) d = if d = 0 then bits t else states t (d - 1))
    (pos d : ℕ) (hpos : pos < k) (hd : d < n) :
    states pos d = bits ((pos + k - (d + 1) % k) % k) := by
  let window := fun t d => if d = 0 then bits t else states t (d - 1)
  have hwrap (t : ℕ) (ht : t < k) :
      states ((t + 1) % k) = states (t + 1) := by
    by_cases hlt : t + 1 < k
    · rw [Nat.mod_eq_of_lt hlt]
    · have heq : t + 1 = k := by omega
      rw [heq, Nat.mod_self]
      exact hclosure.symm
  have hshift : ∀ t d, t < k → d < n →
      window ((t + 1) % k) (d + 1) = window t d := by
    intro t d ht hd
    dsimp [window]
    rw [hwrap t ht]
    exact hstep t d ht hd
  have h := h4_cyclic_window_backward k n hk window hshift pos (d + 1) hpos
    (by omega)
  simpa [window] using h

lemma h4_prev_succ
    (k pos d : ℕ) (hk : 0 < k) :
    ((pos + 1 + k - (d + 1) % k) % k) =
      ((pos + k - d % k) % k) := by
  have hca : (d + 1) % k ≤ pos + 1 + k := by
    have := Nat.mod_lt (d + 1) hk
    omega
  have hdb : d % k + 1 ≤ pos + k + 1 := by
    have := Nat.mod_lt d hk
    omega
  have hab : Nat.ModEq k (pos + 1 + k) (pos + k + 1) := by
    congr 1
    omega
  have hcd : Nat.ModEq k ((d + 1) % k) (d % k + 1) := by
    simp [Nat.ModEq, Nat.add_mod]
  have h := Nat.ModEq.sub hca hdb hab hcd
  change ((pos + 1 + k - (d + 1) % k) % k) =
      ((pos + k + 1 - (d % k + 1)) % k) at h
  simpa only [Nat.add_sub_add_right] using h

lemma h4_prev_period
    (k pos d : ℕ) (hk : 0 < k) :
    ((pos + k + k - d % k) % k) =
      ((pos + k - d % k) % k) := by
  have hm : d % k < k := Nat.mod_lt _ hk
  have heq : pos + k + k - d % k = (pos + k - d % k) + k := by omega
  rw [heq, Nat.add_mod]
  simp

lemma h4_closed_window_path_exists
    {α : Type*} (k n : ℕ) (hk : 0 < k) (bits : ℕ → α) :
    ∃ states : ℕ → ℕ → α,
      states k = states 0 ∧
      ∀ t d, t < k → d < n →
        states (t + 1) d = if d = 0 then bits t else states t (d - 1) := by
  let states := fun t d => bits ((t + k - (d + 1) % k) % k)
  refine ⟨states, ?_, ?_⟩
  · funext d
    dsimp [states]
    simpa using congrArg bits (h4_prev_period k 0 (d + 1) hk)
  · intro t d ht hd
    cases d with
    | zero =>
        dsimp [states]
        rw [h4_prev_succ k t 0 hk]
        simp [Nat.mod_eq_of_lt ht]
    | succ d =>
        dsimp [states]
        rw [h4_prev_succ k t (d + 1) hk]

lemma h4_closed_fin_window_path
    {α : Type*} (k n : ℕ) (hk : 0 < k)
    (hist : Fin (k + 1) → Fin n → α) (bits : Fin k → α)
    (hclosure : hist (Fin.last k) = hist 0)
    (hstep : ∀ (t : Fin k) (d : Fin n),
      hist t.succ d = if _hd : d.val = 0 then bits t
        else hist t.castSucc ⟨d.val - 1, by omega⟩)
    (pos : Fin k) (d : Fin n) :
    hist pos.castSucc d =
      bits ⟨(pos.val + k - (d.val + 1) % k) % k, Nat.mod_lt _ hk⟩ := by
  let input := fun t => if ht : t < k then bits ⟨t, ht⟩ else bits ⟨0, hk⟩
  let states := fun t j => if ht : t < k + 1 then
      if hj : j < n then hist ⟨t, ht⟩ ⟨j, hj⟩ else bits ⟨0, hk⟩
    else bits ⟨0, hk⟩
  have hclose : states k = states 0 := by
    funext j
    by_cases hj : j < n
    · simpa [states, hj, Fin.last] using congrFun hclosure ⟨j, hj⟩
    · simp [states, hj]
  have hshift : ∀ t j, t < k → j < n →
      states (t + 1) j = if j = 0 then input t else states t (j - 1) := by
    intro t j ht hj
    have htle : t ≤ k := Nat.le_of_lt ht
    have ht' : t < k + 1 := by omega
    have hts : t + 1 < k + 1 := by omega
    have hj' : j - 1 < n := by omega
    by_cases hz : j = 0
    · subst j
      simpa [states, input, ht, htle, ht', hts, hj] using
        hstep ⟨t, ht⟩ ⟨0, hj⟩
    · simpa [states, input, ht, htle, ht', hts, hj, hj', hz] using
        hstep ⟨t, ht⟩ ⟨j, hj⟩
  have h := h4_closed_window_path k n hk states input hclose hshift
    pos.val d.val pos.isLt d.isLt
  have hp : pos.val < k + 1 := by omega
  have h' : hist ⟨pos.val, hp⟩ d =
      bits ⟨(pos.val + k - (d.val + 1) % k) % k, Nat.mod_lt _ hk⟩ := by
    simpa [states, input, hp, d.isLt, Nat.mod_lt _ hk] using h
  have hc : (⟨pos.val, hp⟩ : Fin (k + 1)) = pos.castSucc := by
    apply Fin.ext
    rfl
  rwa [hc] at h'

lemma h4_closed_fin_window_path_exists
    {α : Type*} (k n : ℕ) (hk : 0 < k) (bits : Fin k → α) :
    ∃ hist : Fin (k + 1) → Fin n → α,
      hist (Fin.last k) = hist 0 ∧
      ∀ (t : Fin k) (d : Fin n),
        hist t.succ d = if _hd : d.val = 0 then bits t
          else hist t.castSucc ⟨d.val - 1, by omega⟩ := by
  let hist := fun (t : Fin (k + 1)) (d : Fin n) =>
    bits ⟨(t.val + k - (d.val + 1) % k) % k, Nat.mod_lt _ hk⟩
  refine ⟨hist, ?_, ?_⟩
  · funext d
    apply congrArg bits
    apply Fin.ext
    simpa [Fin.last] using h4_prev_period k 0 (d.val + 1) hk
  · intro t d
    by_cases hz : d.val = 0
    · simp only [dite_eq_left hz]
      apply congrArg bits
      apply Fin.ext
      change (t.val + 1 + k - (d.val + 1) % k) % k = t.val
      rw [hz, h4_prev_succ k t.val 0 hk]
      simp [Nat.mod_eq_of_lt t.isLt]
    · simp only [dite_eq_right hz]
      apply congrArg bits
      apply Fin.ext
      change (t.val + 1 + k - (d.val + 1) % k) % k =
        (t.val + k - (d.val - 1 + 1) % k) % k
      have hp : d.val - 1 + 1 = d.val := by omega
      rw [h4_prev_succ k t.val d.val hk, hp]

def h4TrackShift {I : Type} {width : I → ℕ} {beta : I → Type}
    (hist : (i : I) → Fin (width i) → beta i) (incoming : (i : I) → beta i) :
    (i : I) → Fin (width i) → beta i :=
  fun i d => if hd : d.val = 0 then incoming i
    else hist i ⟨d.val - 1, by omega⟩

def h4TrackHistory {A B I : Type} {width : I → ℕ} {beta : I → Type}
    {k : ℕ} (hk : 0 < k) (raw : A → B → (i : I) → beta i)
    (word : Fin k → A) (bits : Fin k → B) (pos : ℕ) :
    (i : I) → Fin (width i) → beta i :=
  fun i d =>
    let t : Fin k := ⟨(pos + k - (d.val + 1) % k) % k, Nat.mod_lt _ hk⟩
    raw (word t) (bits t) i

lemma h4TrackHistory_step {A B I : Type} {width : I → ℕ} {beta : I → Type}
    {k : ℕ} (hk : 0 < k) (raw : A → B → (i : I) → beta i)
    (word : Fin k → A) (bits : Fin k → B) (pos : Fin k) :
    h4TrackHistory (width := width) hk raw word bits (pos.val + 1) =
      h4TrackShift (h4TrackHistory hk raw word bits pos.val) (raw (word pos) (bits pos)) := by
  funext i d
  dsimp [h4TrackHistory, h4TrackShift]
  split_ifs with hd
  · simp [hd, h4_prev_succ k pos.val 0 hk, Nat.mod_eq_of_lt pos.isLt]
  · have heq : d.val - 1 + 1 = d.val := by omega
    simp only [h4_prev_succ k pos.val d.val hk, heq]

lemma h4TrackHistory_closed {A B I : Type} {width : I → ℕ} {beta : I → Type}
    {k : ℕ} (hk : 0 < k) (raw : A → B → (i : I) → beta i)
    (word : Fin k → A) (bits : Fin k → B) :
    h4TrackHistory (width := width) hk raw word bits k =
      h4TrackHistory hk raw word bits 0 := by
  funext i d
  have heq := h4_prev_period k 0 (d.val + 1) hk
  simpa [h4TrackHistory] using
    congrArg (fun t : ℕ => raw (word ⟨t % k, Nat.mod_lt _ hk⟩)
      (bits ⟨t % k, Nat.mod_lt _ hk⟩) i) heq


def h4RegisterNFA {A B I : Type} {width : I → ℕ} {beta : I → Type}
    (raw : A → B → (i : I) → beta i)
    (valid : ((i : I) → Fin (width i) → beta i) → A → B → Prop) :
    NFA A (((i : I) → Fin (width i) → beta i) × ((i : I) → Fin (width i) → beta i)) :=
  helper4CycleNFA (fun hist a b => h4TrackShift hist (raw a b)) valid

lemma h4RegisterNFA_accepts {A B I : Type} {width : I → ℕ} {beta : I → Type}
    {k : ℕ} (hk : 0 < k) (raw : A → B → (i : I) → beta i)
    (valid : ((i : I) → Fin (width i) → beta i) → A → B → Prop)
    (word : Fin k → A) :
    List.ofFn word ∈ (h4RegisterNFA raw valid).toDFA.accepts ↔
      ∃ bits : Fin k → B, ∀ pos : Fin k,
        valid (h4TrackHistory hk raw word bits pos.val) (word pos) (bits pos) := by
  unfold h4RegisterNFA
  rw [helper4CycleDFA_accepts]
  constructor
  · rintro ⟨s, hrun⟩
    rcases (helper4Run_trace (fun hist a b => h4TrackShift hist (raw a b)) valid
      k word s s).mp hrun with ⟨bits, hist, hs, ht, hstep⟩
    have hcl : hist (Fin.last k) = hist 0 := ht.trans hs.symm
    have hhist (pos : Fin k) : hist pos.castSucc = h4TrackHistory hk raw word bits pos.val := by
      funext i d
      apply h4_closed_fin_window_path k (width i) hk (fun t => hist t i)
        (fun t => raw (word t) (bits t) i) (congrFun hcl i)
      intro t d
      exact congrFun (congrFun (hstep t).2 i) d
    refine ⟨bits, ?_⟩
    intro pos
    have h := (hstep pos).1
    rwa [hhist pos] at h
  · rintro ⟨bits, hvalid⟩
    refine ⟨h4TrackHistory hk raw word bits 0, ?_⟩
    apply (helper4Run_trace (fun hist a b => h4TrackShift hist (raw a b)) valid k word
      (h4TrackHistory hk raw word bits 0) (h4TrackHistory hk raw word bits 0)).mpr
    refine ⟨bits, (fun t => h4TrackHistory hk raw word bits t.val), rfl, ?_, ?_⟩
    · exact h4TrackHistory_closed hk raw word bits
    · intro pos
      exact ⟨hvalid pos, h4TrackHistory_step hk raw word bits pos⟩

end PEqualNP.Outside.L_meta_29956_aux

namespace PEqualNP.Outside.L_meta_29956_aux

def h4TrackWidth (r : ℕ) (i : Fin 3) : ℕ :=
  if i = 2 then 7 * r + 3 else 6 * r

abbrev h4Memory (r : ℕ) :=
  (i : Fin 3) → Fin (h4TrackWidth r i) → Bool

lemma h4TrackWidth_zero (r : ℕ) : h4TrackWidth r 0 = 6 * r := by
  simp [h4TrackWidth]

lemma h4TrackWidth_one (r : ℕ) : h4TrackWidth r 1 = 6 * r := by
  simp [h4TrackWidth]

lemma h4TrackWidth_two (r : ℕ) : h4TrackWidth r 2 = 7 * r + 3 := by
  simp [h4TrackWidth]

def h4MemoryEquiv (r : ℕ) :
    h4Memory r ≃
      (Fin (6 * r) → Bool) × (Fin (6 * r) → Bool) × (Fin (7 * r + 3) → Bool) where
  toFun h := (h 0, h 1, h 2)
  invFun p i := Fin.cases p.1 (Fin.cases p.2.1 (Fin.cases p.2.2 (fun j => Fin.elim0 j))) i
  left_inv h := by
    funext i
    fin_cases i <;> rfl
  right_inv p := by
    rfl

lemma h4MemoryEquiv_apply (r : ℕ) (hist : h4Memory r) :
    h4MemoryEquiv r hist = (hist 0, hist 1, hist 2) := rfl

lemma h4MemoryEquiv_fst (r : ℕ) (hist : h4Memory r) :
    (h4MemoryEquiv r hist).1 = hist 0 := rfl

lemma h4MemoryEquiv_snd_fst (r : ℕ) (hist : h4Memory r) :
    (h4MemoryEquiv r hist).2.1 = hist 1 := rfl

lemma h4MemoryEquiv_snd_snd (r : ℕ) (hist : h4Memory r) :
    (h4MemoryEquiv r hist).2.2 = hist 2 := rfl

lemma h4MemoryEquiv_symm_zero (r : ℕ)
    (p : (Fin (6 * r) → Bool) × (Fin (6 * r) → Bool) × (Fin (7 * r + 3) → Bool)) :
    (h4MemoryEquiv r).symm p 0 = p.1 := rfl

lemma h4MemoryEquiv_symm_one (r : ℕ)
    (p : (Fin (6 * r) → Bool) × (Fin (6 * r) → Bool) × (Fin (7 * r + 3) → Bool)) :
    (h4MemoryEquiv r).symm p 1 = p.2.1 := rfl

lemma h4MemoryEquiv_symm_two (r : ℕ)
    (p : (Fin (6 * r) → Bool) × (Fin (6 * r) → Bool) × (Fin (7 * r + 3) → Bool)) :
    (h4MemoryEquiv r).symm p 2 = p.2.2 := rfl

lemma h4Memory_card (r : ℕ) :
    Fintype.card (h4Memory r) = 2 ^ (19 * r + 3) := by
  rw [Fintype.card_congr (h4MemoryEquiv r)]
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  rw [← pow_add, ← pow_add]
  congr 1
  omega

lemma h4RawState_card (r : ℕ) :
    Fintype.card (h4Memory r × h4Memory r) = 2 ^ (38 * r + 6) := by
  rw [Fintype.card_prod, h4Memory_card, ← pow_add]
  congr 1
  omega

lemma h4DetState_card (r : ℕ) :
    Fintype.card (Set (h4Memory r × h4Memory r)) = 2 ^ (2 ^ (38 * r + 6)) := by
  rw [Fintype.card_set, h4RawState_card]

end PEqualNP.Outside.L_meta_29956_aux

namespace PEqualNP.Outside.L_meta_29956_aux

abbrev h4Salt (r : ℕ) := Fin (2 * r) → Fin (7 * r + 3 + 1) → Bool

abbrev h4External (r : ℕ) := h4Salt r × Bool × Bool × Bool

abbrev h4RelationLetter (r : ℕ) := h4External r × Bool × Bool

def h4RawLetter (r : ℕ) (a : h4RelationLetter r) (key : Bool) : Fin 3 → Bool :=
  Fin.cases a.2.1 (Fin.cases a.2.2 (Fin.cases key (fun j => Fin.elim0 j)))

def h4PhysicalValid (r : ℕ) (hist : h4Memory r) (a : h4RelationLetter r)
    (key : Bool) : Prop :=
  h6Valid r a.1.1 a.1.2.1 a.1.2.2.1 a.1.2.2.2
    (h4MemoryEquiv r hist) a.2.1 a.2.2 key = true

def h4GraphDFA (r : ℕ) :
    DFA (h4RelationLetter r) (Set (h4Memory r × h4Memory r)) :=
  (h4RegisterNFA (width := h4TrackWidth r) (beta := fun _ => Bool)
    (h4RawLetter r) (h4PhysicalValid r)).toDFA

def h4PhysicalHistory (r : ℕ) {k : ℕ} (hk : 0 < k)
    (row col key : Fin k → Bool) (pos : Fin k) : h6History r :=
  (fun d => row ⟨(pos.val + k - (d.val + 1) % k) % k, Nat.mod_lt _ hk⟩,
    fun d => col ⟨(pos.val + k - (d.val + 1) % k) % k, Nat.mod_lt _ hk⟩,
    fun d => key ⟨(pos.val + k - (d.val + 1) % k) % k, Nat.mod_lt _ hk⟩)

lemma h4GraphDFA_accepts (r : ℕ) {k : ℕ} (hk : 0 < k)
    (inputData : Fin k → h4External r) (row col : Fin k → Bool) :
    List.ofFn (fun pos => (inputData pos, row pos, col pos)) ∈ (h4GraphDFA r).accepts ↔
      ∃ key : Fin k → Bool, ∀ pos : Fin k,
        h6Valid r (inputData pos).1 (inputData pos).2.1
          (inputData pos).2.2.1 (inputData pos).2.2.2
          (h4PhysicalHistory r hk row col key pos) (row pos) (col pos) (key pos) = true := by
  unfold h4GraphDFA
  rw [h4RegisterNFA_accepts hk]
  rfl

end PEqualNP.Outside.L_meta_29956_aux

namespace PEqualNP.Outside.L_meta_29956_aux

lemma h7_pow_two_le_factorial (n : ℕ) (hn : 4 ≤ n) :
    2 ^ n ≤ n.factorial := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => norm_num [Nat.factorial]
  | succ k ih =>
      calc
        2 ^ (4 + (k + 1)) = 2 ^ (4 + k) * 2 := by
          rw [← Nat.add_assoc, pow_succ]
        _ ≤ (4 + k).factorial * (4 + k + 1) :=
          Nat.mul_le_mul (ih (by omega)) (by omega)
        _ = (4 + (k + 1)).factorial := by
          rw [← Nat.add_assoc, Nat.factorial_succ]
          exact Nat.mul_comm _ _

lemma h7_factorial_le_stirling_sum (n : ℕ) :
    n.factorial ≤ (Finset.range (n + 1)).sum (fun u =>
      u.factorial * (Nat.stirlingSecond (n + 1) (u + 1)) ^ 2) := by
  rw [Finset.sum_range_succ]
  simp only [Nat.stirlingSecond_self, one_pow, mul_one]
  omega

lemma h7_pow_two_le_stirling_sum (n : ℕ) (hn : 2 ≤ n) :
    2 ^ n ≤ (Finset.range (n + 1)).sum (fun u =>
      u.factorial * (Nat.stirlingSecond (n + 1) (u + 1)) ^ 2) := by
  by_cases h4 : 4 ≤ n
  · exact (h7_pow_two_le_factorial n h4).trans (h7_factorial_le_stirling_sum n)
  · have hs : n = 2 ∨ n = 3 := by omega
    rcases hs with rfl | rfl <;>
      norm_num [Finset.sum_range_succ, Nat.stirlingSecond, Nat.factorial]

lemma h7_tables_le_stirling_sum (q n : ℕ) (hn : 2 ≤ n) (hq : q * q ≤ n) :
    2 ^ (q * q) ≤ (Finset.range (n + 1)).sum (fun u =>
      u.factorial * (Nat.stirlingSecond (n + 1) (u + 1)) ^ 2) := by
  exact (Nat.pow_le_pow_right (by omega) hq).trans (h7_pow_two_le_stirling_sum n hn)

lemma h7_comparison_state_bound (t p : ℕ) (ht : t ≤ p) :
    2 * t * 2 ^ t ≤ 2 * p * 2 ^ p := by
  exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 ht)
    (Nat.pow_le_pow_right (by omega) ht)

lemma h7_name_offset_bound (r : ℕ) : 6 * r ≤ (7 * r + 3) - 1 := by
  omega

lemma h7_key_offset_bound (r : ℕ) (hr : 0 < r) :
    6 * r + 3 ≤ (7 * r + 3) - 1 ∧ 7 * r + 1 ≤ (7 * r + 3) - 1 := by
  omega

lemma h7_double_exp_square_le (s t : ℕ) (hst : s + 1 ≤ t) :
    2 ^ (2 ^ s) * 2 ^ (2 ^ s) ≤ 2 ^ (2 ^ t) := by
  have he : 2 ^ s + 2 ^ s ≤ 2 ^ t := by
    calc
      2 ^ s + 2 ^ s = 2 ^ (s + 1) := by rw [pow_succ]; omega
      _ ≤ 2 ^ t := Nat.pow_le_pow_right (by omega) hst
  calc
    2 ^ (2 ^ s) * 2 ^ (2 ^ s) = 2 ^ (2 ^ s + 2 ^ s) :=
      (pow_add 2 (2 ^ s) (2 ^ s)).symm
    _ ≤ 2 ^ (2 ^ t) := Nat.pow_le_pow_right (by omega) he

lemma h7_short_window_square_le (b : ℕ) (hb : 1 ≤ b) :
    2 ^ (2 ^ (6 * b - 4)) * 2 ^ (2 ^ (6 * b - 4)) ≤
      2 ^ (2 ^ (6 * b)) := by
  exact h7_double_exp_square_le (6 * b - 4) (6 * b) (by omega)

lemma h7_window_card (b : ℕ) (hb : 1 ≤ b) :
    Fintype.card
      (((Fin (b - 1) → Bool) × (Fin (b - 1) → Bool) × (Fin b → Bool)) ×
       ((Fin (b - 1) → Bool) × (Fin (b - 1) → Bool) × (Fin b → Bool))) =
      2 ^ (6 * b - 4) := by
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  repeat rw [← pow_add]
  congr 1
  omega


abbrev helper7Table (q : ℕ) := Fin q → Fin q → Bool

abbrev helper7State (q : ℕ) := Bool × helper7Table q × Set (helper7Table q)

lemma helper7_card_table (q : ℕ) :
    Fintype.card (helper7Table q) = 2 ^ (q * q) := by
  simp [helper7Table, Nat.pow_mul]

lemma helper7_card_state (q : ℕ) :
    Fintype.card (helper7State q) =
      2 * (2 ^ (q * q)) * 2 ^ (2 ^ (q * q)) := by
  classical
  simp [helper7State, helper7Table, Nat.pow_mul, Nat.mul_assoc]

noncomputable def helper7_state_equiv_fin (q : ℕ) :
    helper7State q ≃ Fin (2 * (2 ^ (q * q)) * 2 ^ (2 ^ (q * q))) := by
  classical
  exact (Fintype.equivFin (helper7State q)).trans (finCongr (helper7_card_state q))

lemma helper7_state_bound (q N P : ℕ) (hq : q * q ≤ N)
    (hP : 2 ^ N ≤ P) :
    2 * (2 ^ (q * q)) * 2 ^ (2 ^ (q * q)) ≤ 2 * P * 2 ^ P := by
  have htable : 2 ^ (q * q) ≤ P :=
    le_trans (Nat.pow_le_pow_right (by decide) hq) hP
  exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 htable)
    (Nat.pow_le_pow_right (by decide) htable)

def helper7Transfer {S : Type*} [Fintype S]
    (weight : S → S → ℕ) (v : S → ℕ) : S → ℕ :=
  fun dst => ∑ src, v src * weight src dst

lemma helper7_transfer_relabel {S T : Type*} [Fintype S] [Fintype T]
    (e : S ≃ T) (weight : S → S → ℕ) (v : S → ℕ) :
    helper7Transfer (fun src dst => weight (e.symm src) (e.symm dst))
      (fun state => v (e.symm state)) =
        fun state => helper7Transfer weight v (e.symm state) := by
  funext dst
  exact e.symm.sum_comp (fun src => v src * weight src (e.symm dst))

def helper7Run {S A : Type*} [Fintype S]
    (weight : A → S → S → ℕ) (word : List A) (v : S → ℕ) : S → ℕ :=
  word.foldl (fun counts letter => helper7Transfer (weight letter) counts) v

lemma helper7_run_relabel {S T A : Type*} [Fintype S] [Fintype T]
    (e : S ≃ T) (weight : A → S → S → ℕ) (word : List A) (v : S → ℕ) :
    helper7Run (fun letter src dst => weight letter (e.symm src) (e.symm dst))
      word (fun state => v (e.symm state)) =
        fun state => helper7Run weight word v (e.symm state) := by
  induction word generalizing v with
  | nil => rfl
  | cons letter word ih =>
    simp only [helper7Run, List.foldl_cons]
    rw [helper7_transfer_relabel]
    exact ih (helper7Transfer (weight letter) v)

lemma helper7_finish_relabel {S T : Type*} [Fintype S] [Fintype T]
    (e : S ≃ T) (finish : S → Bool) (counts : S → ℕ) :
    (∑ state : T, if finish (e.symm state) then counts (e.symm state) else 0) =
      ∑ state : S, if finish state then counts state else 0 := by
  exact e.symm.sum_comp (fun state => if finish state then counts state else 0)

lemma helper7_start_relabel {S T : Type*} [DecidableEq S] [DecidableEq T]
    (e : S ≃ T) (start : S) :
    (fun state : T => (decide (state = e start)).toNat) =
      fun state => (decide (e.symm state = start)).toNat := by
  funext state
  simp only [Equiv.symm_apply_eq]

lemma helper7_accepted_relabel {S T A : Type*} [Fintype S] [Fintype T]
    [DecidableEq S] [DecidableEq T] (e : S ≃ T) (start : S)
    (finish : S → Bool) (weight : A → S → S → Fin 3) (word : List A) :
    (∑ state : T, if finish (e.symm state) then
      helper7Run (fun letter src dst => (weight letter (e.symm src) (e.symm dst)).val)
        word (fun state : T => (decide (state = e start)).toNat) state else 0) =
      ∑ state : S, if finish state then
        helper7Run (fun letter src dst => (weight letter src dst).val)
          word (fun state : S => (decide (state = start)).toNat) state else 0 := by
  rw [helper7_start_relabel,
    helper7_run_relabel e (fun letter src dst => (weight letter src dst).val) word
      (fun state : S => (decide (state = start)).toNat)]
  exact helper7_finish_relabel e finish _

lemma helper7_fin_realization {S A : Type*} [Fintype S] [DecidableEq S]
    (start : S) (finish : S → Bool) (weight : A → S → S → Fin 3) :
    ∃ (start' : Fin (Fintype.card S)) (finish' : Fin (Fintype.card S) → Bool)
      (weight' : A → Fin (Fintype.card S) → Fin (Fintype.card S) → Fin 3),
      ∀ word : List A,
        (∑ state : Fin (Fintype.card S), if finish' state then
          helper7Run (fun letter src dst => (weight' letter src dst).val)
            word (fun state => (decide (state = start')).toNat) state else 0) =
          ∑ state : S, if finish state then
            helper7Run (fun letter src dst => (weight letter src dst).val)
              word (fun state : S => (decide (state = start)).toNat) state else 0 := by
  let e := Fintype.equivFin S
  refine ⟨e start, fun state => finish (e.symm state),
    fun letter src dst => weight letter (e.symm src) (e.symm dst), ?_⟩
  intro word
  exact helper7_accepted_relabel e start finish weight word

abbrev h7History (r : ℕ) :=
  (Fin (6 * r) → Bool) × (Fin (6 * r) → Bool) × (Fin (7 * r + 3) → Bool)

abbrev h7RawState (r : ℕ) := h7History r × h7History r

abbrev h7DetState (r : ℕ) := Set (h7RawState r)

abbrev h7FullTable (r : ℕ) := h7DetState r → h7DetState r → Bool

abbrev h7FullState (r : ℕ) := Bool × h7FullTable r × Set (h7FullTable r)

lemma h7_raw_card (r : ℕ) : Fintype.card (h7RawState r) = 2 ^ (38 * r + 6) := by
  simp only [h7RawState, h7History, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_bool]
  repeat rw [← pow_add]
  congr 1
  omega

lemma h7_det_card (r : ℕ) : Fintype.card (h7DetState r) = 2 ^ (2 ^ (38 * r + 6)) := by
  rw [Fintype.card_set, h7_raw_card]

lemma h7_full_table_card (r : ℕ) : Fintype.card (h7FullTable r) =
    2 ^ ((2 ^ (2 ^ (38 * r + 6))) * (2 ^ (2 ^ (38 * r + 6)))) := by
  rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_bool, h7_det_card, ← Nat.pow_mul]

set_option synthInstance.maxSize 4096 in
lemma h7_full_state_card (r : ℕ) : Fintype.card (h7FullState r) =
    2 * Fintype.card (h7FullTable r) * 2 ^ Fintype.card (h7FullTable r) := by
  classical
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_bool, Fintype.card_set]
  exact (Nat.mul_assoc _ _ _).symm

set_option synthInstance.maxSize 4096 in
lemma h7_full_dimension_bound (r : ℕ) :
    let b := 7 * r + 3
    let N := 2 ^ (2 ^ (6 * b))
    let P := (Finset.range (N + 1)).sum (fun u =>
      u.factorial * (Nat.stirlingSecond (N + 1) (u + 1)) ^ 2)
    Fintype.card (h7FullState r) ≤ 2 * P * 2 ^ P := by
  dsimp only
  rw [h7_full_state_card]
  apply h7_comparison_state_bound
  rw [h7_full_table_card]
  apply h7_tables_le_stirling_sum
  · have hi : 1 ≤ 2 ^ (6 * (7 * r + 3)) := Nat.one_le_pow _ _ (by decide)
    calc
      2 = 2 ^ 1 := by decide
      _ ≤ 2 ^ (2 ^ (6 * (7 * r + 3))) :=
        Nat.pow_le_pow_right (by decide) hi
  · exact h7_double_exp_square_le (38 * r + 6) (6 * (7 * r + 3)) (by omega)

set_option synthInstance.maxSize 4096 in
lemma h7_full_fin_realization {A : Type*} (r : ℕ)
    (start : h7FullState r) (finish : h7FullState r → Bool)
    (weight : A → h7FullState r → h7FullState r → Fin 3) :
    let b := 7 * r + 3
    let N := 2 ^ (2 ^ (6 * b))
    let P := (Finset.range (N + 1)).sum (fun u =>
      u.factorial * (Nat.stirlingSecond (N + 1) (u + 1)) ^ 2)
    ∃ (D : ℕ) (start' : Fin D) (finish' : Fin D → Bool)
      (weight' : A → Fin D → Fin D → Fin 3),
      D ≤ 2 * P * 2 ^ P ∧ ∀ word : List A,
      (∑ state : Fin D, if finish' state then
        helper7Run (fun letter src dst => (weight' letter src dst).val)
          word (fun state => (decide (state = start')).toNat) state else 0) =
        ∑ state : h7FullState r, if finish state then
          helper7Run (fun letter src dst => (weight letter src dst).val)
            word (fun state => (decide (state = start)).toNat) state else 0 := by
  classical
  obtain ⟨start', finish', weight', heq⟩ := helper7_fin_realization start finish weight
  exact ⟨Fintype.card (h7FullState r), start', finish', weight',
    h7_full_dimension_bound r, heq⟩

end PEqualNP.Outside.L_meta_29956_aux

namespace PEqualNP.Outside.L_meta_29956_aux

abbrev h7ComparisonState (Q : Type*) := Bool × (Q → Q → Bool) × Set (Q → Q → Bool)

set_option synthInstance.maxSize 4096 in
lemma h7_comparison_card {Q : Type*} [Fintype Q] [DecidableEq Q] :
    Fintype.card (h7ComparisonState Q) =
      2 * (2 ^ (Fintype.card Q * Fintype.card Q)) *
        2 ^ (2 ^ (Fintype.card Q * Fintype.card Q)) := by
  classical
  simp only [h7ComparisonState, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_set, Fintype.card_bool, ← Nat.pow_mul]
  exact (Nat.mul_assoc _ _ _).symm

set_option synthInstance.maxSize 4096 in
lemma h7_generic_dimension_bound {Q : Type*} [Fintype Q] [DecidableEq Q] (r : ℕ)
    (hq : Fintype.card Q ≤ 2 ^ (2 ^ (38 * r + 6))) :
    let b := 7 * r + 3
    let N := 2 ^ (2 ^ (6 * b))
    let P := (Finset.range (N + 1)).sum (fun u =>
      u.factorial * (Nat.stirlingSecond (N + 1) (u + 1)) ^ 2)
    Fintype.card (h7ComparisonState Q) ≤ 2 * P * 2 ^ P := by
  dsimp only
  rw [h7_comparison_card]
  apply h7_comparison_state_bound
  apply h7_tables_le_stirling_sum
  · have hi : 1 ≤ 2 ^ (6 * (7 * r + 3)) := Nat.one_le_pow _ _ (by decide)
    calc
      2 = 2 ^ 1 := by decide
      _ ≤ 2 ^ (2 ^ (6 * (7 * r + 3))) := Nat.pow_le_pow_right (by decide) hi
  · exact (Nat.mul_le_mul hq hq).trans
      (h7_double_exp_square_le (38 * r + 6) (6 * (7 * r + 3)) (by omega))

set_option synthInstance.maxSize 4096 in
lemma h7_generic_fin_realization {A Q : Type*} [Fintype Q] [DecidableEq Q] (r : ℕ)
    (hq : Fintype.card Q ≤ 2 ^ (2 ^ (38 * r + 6)))
    (start : h7ComparisonState Q) (finish : h7ComparisonState Q → Bool)
    (weight : A → h7ComparisonState Q → h7ComparisonState Q → Fin 3) :
    let b := 7 * r + 3
    let N := 2 ^ (2 ^ (6 * b))
    let P := (Finset.range (N + 1)).sum (fun u =>
      u.factorial * (Nat.stirlingSecond (N + 1) (u + 1)) ^ 2)
    ∃ (D : ℕ) (start' : Fin D) (finish' : Fin D → Bool)
      (weight' : A → Fin D → Fin D → Fin 3),
      D ≤ 2 * P * 2 ^ P ∧ ∀ word : List A,
      (∑ state : Fin D, if finish' state then
        helper7Run (fun letter src dst => (weight' letter src dst).val)
          word (fun state => (decide (state = start')).toNat) state else 0) =
        ∑ state : h7ComparisonState Q, if finish state then
          helper7Run (fun letter src dst => (weight letter src dst).val)
            word (fun state => (decide (state = start)).toNat) state else 0 := by
  classical
  obtain ⟨start', finish', weight', heq⟩ := helper7_fin_realization start finish weight
  exact ⟨Fintype.card (h7ComparisonState Q), start', finish', weight',
    h7_generic_dimension_bound r hq, heq⟩

lemma h7_pi_history_card {I : Type*} [Fintype I] [DecidableEq I] (width : I → ℕ) :
    Fintype.card ((i : I) → Fin (width i) → Bool) = 2 ^ (∑ i, width i) := by
  rw [Fintype.card_pi]
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  exact Finset.prod_pow_eq_pow_sum Finset.univ width 2

lemma h7_determinization_bound {H : Type*} [Fintype H] [DecidableEq H] (r : ℕ)
    (hH : Fintype.card H ≤ 2 ^ (19 * r + 3)) :
    Fintype.card (Set (H × H)) ≤ 2 ^ (2 ^ (38 * r + 6)) := by
  rw [Fintype.card_set, Fintype.card_prod]
  apply Nat.pow_le_pow_right (by decide)
  calc
    Fintype.card H * Fintype.card H ≤ 2 ^ (19 * r + 3) * 2 ^ (19 * r + 3) :=
      Nat.mul_le_mul hH hH
    _ = 2 ^ (38 * r + 6) := by
      rw [← pow_add]
      congr 1
      omega

lemma h7_pi_determinization_bound {I : Type*} [Fintype I] [DecidableEq I]
    (r : ℕ) (width : I → ℕ) (hwidth : (∑ i, width i) ≤ 19 * r + 3) :
    Fintype.card (Set ((((i : I) → Fin (width i) → Bool)) ×
      (((i : I) → Fin (width i) → Bool)))) ≤ 2 ^ (2 ^ (38 * r + 6)) := by
  apply h7_determinization_bound
  rw [h7_pi_history_card]
  exact Nat.pow_le_pow_right (by decide) hwidth

end PEqualNP.Outside.L_meta_29956_aux

namespace PEqualNP.Outside.L_meta_29956_aux

def pnp29956_comparisonStep {Q : Type*} (left right : Bool → Q → Q)
    (E : Q → Q → Prop) : Q → Q → Prop :=
  fun q q' => ∀ bit : Bool, E (left bit q) (right bit q')

def pnp29956_reverseRun {A Q : Type*} (delta : A → Bool → Q → Q) :
    List A → List Bool → Q → Q
  | [], _, q => q
  | a :: rest, bit :: bits, q => delta a bit (pnp29956_reverseRun delta rest bits q)
  | a :: rest, [], q => delta a false (pnp29956_reverseRun delta rest [] q)

lemma pnp29956_comparison_foldl {A Q : Type*}
    (left right : A → Bool → Q → Q) (letters : List A)
    (E : Q → Q → Prop) (q q' : Q) :
    (letters.foldl (fun F a => pnp29956_comparisonStep (left a) (right a) F) E) q q' ↔
      ∀ bits : List Bool, bits.length = letters.length →
        E (pnp29956_reverseRun left letters bits q)
          (pnp29956_reverseRun right letters bits q') := by
  induction letters generalizing E with
  | nil =>
      simp [pnp29956_reverseRun]
  | cons a rest ih =>
      simp only [List.foldl_cons]
      rw [ih]
      constructor
      · intro h bits hlen
        cases bits with
        | nil => simp at hlen
        | cons bit bits =>
            have hlen' : bits.length = rest.length := by simpa using hlen
            exact h bits hlen' bit
      · intro h bits hlen bit
        exact h (bit :: bits) (by simpa using hlen)

def pnp29956_reverseLess : List Bool → List Bool → Prop
  | [], _ => False
  | _, [] => False
  | bit :: bits, top :: tops =>
      pnp29956_reverseLess bits tops ∨ (bits = tops ∧ bit = false ∧ top = true)

lemma pnp29956_reverseLess_length {bits tops : List Bool}
    (h : pnp29956_reverseLess bits tops) : bits.length = tops.length := by
  induction bits generalizing tops with
  | nil => exact False.elim h
  | cons bit bits ih =>
      cases tops with
      | nil => exact False.elim h
      | cons top tops =>
          rcases h with h | ⟨rfl, _, _⟩
          · simpa using ih h
          · rfl

lemma pnp29956_reverseLess_irrefl (bits : List Bool) :
    ¬ pnp29956_reverseLess bits bits := by
  induction bits with
  | nil => exact id
  | cons bit bits ih =>
      intro h
      rcases h with h | ⟨_, hfalse, htrue⟩
      · exact ih h
      · simp_all

def pnp29956_comparisonTable {A Q : Type*}
    (delta : A → Bool → Bool → Q → Q) (E : Q → Q → Prop) :
    List (A × Bool) → List Bool → Q → Q → Prop
  | [], _ => E
  | _ :: _, [] => E
  | (symbol, bit) :: word, rival :: rivals =>
      pnp29956_comparisonStep (delta symbol bit) (delta symbol rival)
        (pnp29956_comparisonTable delta E word rivals)

def pnp29956_rivalTables {A Q : Type*}
    (delta : A → Bool → Bool → Q → Q) (E : Q → Q → Prop)
    (word : List (A × Bool)) : Set (Q → Q → Prop) :=
  {F | ∃ rival : List Bool, pnp29956_reverseLess rival (word.map Prod.snd) ∧
    F = pnp29956_comparisonTable delta E word rival}

lemma pnp29956_equalTable_cons {A Q : Type*}
    (delta : A → Bool → Bool → Q → Q) (E : Q → Q → Prop)
    (word : List (A × Bool)) (symbol : A) (bit : Bool) :
    pnp29956_comparisonTable delta E ((symbol, bit) :: word)
      (((symbol, bit) :: word).map Prod.snd) =
    pnp29956_comparisonStep (delta symbol bit) (delta symbol bit)
      (pnp29956_comparisonTable delta E word (word.map Prod.snd)) := by
  rfl

lemma pnp29956_rivalTables_cons {A Q : Type*}
    (delta : A → Bool → Bool → Q → Q) (E : Q → Q → Prop)
    (word : List (A × Bool)) (symbol : A) (bit : Bool) (F : Q → Q → Prop) :
    F ∈ pnp29956_rivalTables delta E ((symbol, bit) :: word) ↔
      (∃ G ∈ pnp29956_rivalTables delta E word, ∃ rival : Bool,
        F = pnp29956_comparisonStep (delta symbol bit) (delta symbol rival) G) ∨
      (bit = true ∧ F = pnp29956_comparisonStep (delta symbol true) (delta symbol false)
        (pnp29956_comparisonTable delta E word (word.map Prod.snd))) := by
  constructor
  · rintro ⟨rival, hless, rfl⟩
    cases rival with
    | nil => exact False.elim hless
    | cons rival rivals =>
        rcases hless with hless | ⟨hrivals, hrival, hbit⟩
        · left
          exact ⟨pnp29956_comparisonTable delta E word rivals,
            ⟨rivals, hless, rfl⟩, rival, rfl⟩
        · right
          subst rivals
          subst rival
          change bit = true at hbit
          subst bit
          exact ⟨rfl, rfl⟩
  · rintro (⟨G, ⟨rivals, hless, rfl⟩, rival, rfl⟩ | ⟨hbit, rfl⟩)
    · exact ⟨rival :: rivals, Or.inl hless, rfl⟩
    · subst bit
      exact ⟨false :: word.map Prod.snd, Or.inr ⟨rfl, rfl, rfl⟩, rfl⟩

lemma pnp29956_rivalTables_nil {A Q : Type*}
    (delta : A → Bool → Bool → Q → Q) (E : Q → Q → Prop) :
    pnp29956_rivalTables delta E [] = ∅ := by
  ext F
  constructor
  · rintro ⟨rival, hless, _⟩
    cases rival <;> exact False.elim hless
  · intro h
    exact False.elim h

def pnp29956_forwardRun {A Q : Type*}
    (delta : A → Bool → Bool → Q → Q) : List (A × Bool) → List Bool → Q → Q
  | [], _, q => q
  | (symbol, bit) :: word, column :: columns, q =>
      pnp29956_forwardRun delta word columns (delta symbol bit column q)
  | (symbol, bit) :: word, [], q =>
      pnp29956_forwardRun delta word [] (delta symbol bit false q)

lemma pnp29956_comparisonTable_semantics {A Q : Type*}
    (delta : A → Bool → Bool → Q → Q) (E : Q → Q → Prop)
    (word : List (A × Bool)) (rival : List Bool) (hlen : rival.length = word.length)
    (q q' : Q) :
    pnp29956_comparisonTable delta E word rival q q' ↔
      ∀ columns : List Bool, columns.length = word.length →
        E (pnp29956_forwardRun delta word columns q)
          (pnp29956_forwardRun delta (List.zip (word.map Prod.fst) rival) columns q') := by
  induction word generalizing rival q q' with
  | nil =>
      have hrival : rival = [] := by simpa using hlen
      subst rival
      simp [pnp29956_comparisonTable, pnp29956_forwardRun]
  | cons letter word ih =>
      rcases letter with ⟨symbol, bit⟩
      cases rival with
      | nil => simp at hlen
      | cons rival rivals =>
          have hlen' : rivals.length = word.length := by simpa using hlen
          constructor
          · intro h columns hcolumns
            cases columns with
            | nil => simp at hcolumns
            | cons column columns =>
                have hcolumns' : columns.length = word.length := by simpa using hcolumns
                exact (ih rivals hlen' (delta symbol bit column q)
                  (delta symbol rival column q')).mp (h column) columns hcolumns'
          · intro h column
            apply (ih rivals hlen' (delta symbol bit column q)
              (delta symbol rival column q')).mpr
            intro columns hcolumns
            exact h (column :: columns) (by simpa using hcolumns)

lemma pnp29956_noRival_iff_least {A Q : Type*}
    (delta : A → Bool → Bool → Q → Q) (finish : Q → Bool)
    (word : List (A × Bool)) (start : Q) :
    (∀ F ∈ pnp29956_rivalTables delta (fun q q' => finish q = finish q') word,
      ¬ F start start) ↔
    ¬ ∃ rival : List Bool, pnp29956_reverseLess rival (word.map Prod.snd) ∧
      ∀ columns : List Bool, columns.length = word.length →
        finish (pnp29956_forwardRun delta word columns start) =
          finish (pnp29956_forwardRun delta (List.zip (word.map Prod.fst) rival)
            columns start) := by
  constructor
  · intro h ⟨rival, hless, hequal⟩
    have hlen : rival.length = word.length := by
      simpa using pnp29956_reverseLess_length hless
    exact h (pnp29956_comparisonTable delta (fun q q' => finish q = finish q') word rival)
      ⟨rival, hless, rfl⟩
      ((pnp29956_comparisonTable_semantics delta (fun q q' => finish q = finish q')
        word rival hlen start start).mpr hequal)
  · rintro h F ⟨rival, hless, rfl⟩ htable
    have hlen : rival.length = word.length := by
      simpa using pnp29956_reverseLess_length hless
    exact h ⟨rival, hless,
      (pnp29956_comparisonTable_semantics delta (fun q q' => finish q = finish q')
        word rival hlen start start).mp htable⟩

def pnp29956_comparisonState {A Q : Type*}
    (delta : A → Bool → Bool → Q → Q) (E : Q → Q → Prop)
    (word : List (A × Bool)) : (Q → Q → Prop) × Set (Q → Q → Prop) :=
  (pnp29956_comparisonTable delta E word (word.map Prod.snd),
    pnp29956_rivalTables delta E word)

def pnp29956_stateStep {A Q : Type*}
    (delta : A → Bool → Bool → Q → Q)
    (state : (Q → Q → Prop) × Set (Q → Q → Prop)) (letter : A × Bool) :
    (Q → Q → Prop) × Set (Q → Q → Prop) :=
  (pnp29956_comparisonStep (delta letter.1 letter.2) (delta letter.1 letter.2) state.1,
    {F | (∃ G ∈ state.2, ∃ rival : Bool,
      F = pnp29956_comparisonStep (delta letter.1 letter.2) (delta letter.1 rival) G) ∨
      (letter.2 = true ∧ F =
        pnp29956_comparisonStep (delta letter.1 true) (delta letter.1 false) state.1)})

lemma pnp29956_stateStep_semantics {A Q : Type*}
    (delta : A → Bool → Bool → Q → Q) (E : Q → Q → Prop)
    (word : List (A × Bool)) (letter : A × Bool) :
    pnp29956_stateStep delta (pnp29956_comparisonState delta E word) letter =
      pnp29956_comparisonState delta E (letter :: word) := by
  rcases letter with ⟨symbol, bit⟩
  apply Prod.ext
  · rfl
  · apply Set.ext
    intro F
    exact (pnp29956_rivalTables_cons delta E word symbol bit F).symm

lemma pnp29956_stateFold_semantics {A Q : Type*}
    (delta : A → Bool → Bool → Q → Q) (E : Q → Q → Prop)
    (letters word : List (A × Bool)) :
    letters.foldl (pnp29956_stateStep delta) (pnp29956_comparisonState delta E word) =
      pnp29956_comparisonState delta E (letters.reverse ++ word) := by
  induction letters generalizing word with
  | nil => rfl
  | cons letter letters ih =>
      rw [List.foldl_cons, pnp29956_stateStep_semantics, ih]
      simp

lemma pnp29956_stateFold_initial {A Q : Type*}
    (delta : A → Bool → Bool → Q → Q) (E : Q → Q → Prop)
    (letters : List (A × Bool)) :
    letters.foldl (pnp29956_stateStep delta) (E, ∅) =
      pnp29956_comparisonState delta E letters.reverse := by
  have hinit : (E, (∅ : Set (Q → Q → Prop))) =
      pnp29956_comparisonState delta E [] := by
    apply Prod.ext
    · rfl
    · exact (pnp29956_rivalTables_nil delta E).symm
  rw [hinit, pnp29956_stateFold_semantics]
  simp

end PEqualNP.Outside.L_meta_29956_aux

namespace PEqualNP.Outside.L_meta_29956_aux

def meta29956_wordValue : List Bool → Nat
  | [] => 0
  | a :: w => a.toNat * 2 ^ w.length + meta29956_wordValue w

lemma meta29956_wordValue_lt (w : List Bool) :
    meta29956_wordValue w < 2 ^ w.length := by
  induction w with
  | nil => simp [meta29956_wordValue]
  | cons a w ih =>
    cases a <;> simp only [meta29956_wordValue, List.length_cons,
      Bool.toNat_false, Bool.toNat_true, Nat.zero_mul, Nat.one_mul,
      Nat.zero_add, Nat.pow_succ] <;> omega

def meta29956_boundStep (q : Option Bool) (p : Bool × Bool) : Option Bool :=
  match q with
  | none => none
  | some true => some true
  | some false =>
    if p.1 then (if p.2 then some false else none)
    else (if p.2 then some true else some false)

def meta29956_boundRun (x y : List Bool) : Option Bool :=
  (x.zip y).foldl meta29956_boundStep (some false)

lemma meta29956_boundStep_fold_none (w : List (Bool × Bool)) :
    w.foldl meta29956_boundStep none = none := by
  induction w with
  | nil => rfl
  | cons p w ih => simpa [meta29956_boundStep] using ih

lemma meta29956_boundStep_fold_true (w : List (Bool × Bool)) :
    w.foldl meta29956_boundStep (some true) = some true := by
  induction w with
  | nil => rfl
  | cons p w ih => simpa [meta29956_boundStep] using ih

lemma meta29956_boundRun_correct (x y : List Bool) (hlen : x.length = y.length) :
    meta29956_boundRun x y =
      if meta29956_wordValue x < meta29956_wordValue y then some true
      else if meta29956_wordValue x = meta29956_wordValue y then some false
      else none := by
  induction x generalizing y with
  | nil =>
    cases y with
    | nil => simp [meta29956_boundRun, meta29956_wordValue]
    | cons b y => simp at hlen
  | cons a x ih =>
    cases y with
    | nil => simp at hlen
    | cons b y =>
      have hlen' : x.length = y.length := by simpa using hlen
      have hx := meta29956_wordValue_lt x
      have hy := meta29956_wordValue_lt y
      rw [hlen'] at hx
      have ih' := ih y hlen'
      cases a <;> cases b
      · simpa [meta29956_boundRun, meta29956_boundStep, meta29956_wordValue] using ih'
      · have hlt : meta29956_wordValue x < 2 ^ y.length + meta29956_wordValue y := by omega
        simp [meta29956_boundRun, meta29956_boundStep, meta29956_wordValue,
          meta29956_boundStep_fold_true, hlt]
      · have hlt : ¬ (2 ^ y.length + meta29956_wordValue x < meta29956_wordValue y) := by omega
        have hne : 2 ^ y.length + meta29956_wordValue x ≠ meta29956_wordValue y := by omega
        simp [meta29956_boundRun, meta29956_boundStep, meta29956_wordValue,
          meta29956_boundStep_fold_none, hlen', hlt, hne]
      · simpa [meta29956_boundRun, meta29956_boundStep, meta29956_wordValue,
          hlen'] using ih'

lemma meta29956_boundRun_accepts (x y : List Bool) (hlen : x.length = y.length) :
    meta29956_boundRun x y ≠ none ↔ meta29956_wordValue x ≤ meta29956_wordValue y := by
  rw [meta29956_boundRun_correct x y hlen]
  split <;> rename_i h
  · simp only [ne_eq, reduceCtorEq, not_false_eq_true, true_iff]
    omega
  · split <;> rename_i heq
    · simp only [ne_eq, reduceCtorEq, not_false_eq_true, true_iff]
      omega
    · simp only [ne_eq, not_true_eq_false, false_iff]
      omega

lemma meta29956_boundRun_strict (x y : List Bool) (hlen : x.length = y.length) :
    meta29956_boundRun x y = some true ↔ meta29956_wordValue x < meta29956_wordValue y := by
  rw [meta29956_boundRun_correct x y hlen]
  split <;> rename_i h
  · simp [h]
  · split <;> simp_all

lemma meta29956_boundRun_equal (x y : List Bool) (hlen : x.length = y.length) :
    meta29956_boundRun x y = some false ↔ meta29956_wordValue x = meta29956_wordValue y := by
  rw [meta29956_boundRun_correct x y hlen]
  split <;> rename_i h
  · simp only [Option.some.injEq, Bool.true_eq_false, false_iff]
    omega
  · split <;> simp_all

def meta29956_wordBits (k n : Nat) : List Bool :=
  (List.range k).reverse.map n.testBit

lemma meta29956_wordBits_length (k n : Nat) :
    (meta29956_wordBits k n).length = k := by
  simp [meta29956_wordBits]

lemma meta29956_wordBits_value (k n : Nat) :
    meta29956_wordValue (meta29956_wordBits k n) = n % 2 ^ k := by
  induction k with
  | zero => simp [meta29956_wordBits, meta29956_wordValue, Nat.mod_one]
  | succ k ih =>
    simp only [meta29956_wordBits, List.range_succ, List.reverse_append,
      List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append, List.map_cons, meta29956_wordValue,
      List.length_map, List.length_reverse, List.length_range]
    change (n.testBit k).toNat * 2 ^ k + meta29956_wordValue (meta29956_wordBits k n) = _
    rw [ih, Nat.toNat_testBit, Nat.pow_succ, Nat.mod_mul]
    simp [Nat.mul_comm, Nat.add_comm]

lemma meta29956_wordBits_value_of_lt (k n : Nat) (hn : n < 2 ^ k) :
    meta29956_wordValue (meta29956_wordBits k n) = n := by
  rw [meta29956_wordBits_value, Nat.mod_eq_of_lt hn]

lemma meta29956_boundRun_bits_accepts (k x y : Nat) (hx : x < 2 ^ k) (hy : y < 2 ^ k) :
    meta29956_boundRun (meta29956_wordBits k x) (meta29956_wordBits k y) ≠ none ↔ x ≤ y := by
  rw [meta29956_boundRun_accepts _ _ (by simp [meta29956_wordBits_length]),
    meta29956_wordBits_value_of_lt k x hx, meta29956_wordBits_value_of_lt k y hy]

lemma meta29956_boundRun_bits_strict (k x y : Nat) (hx : x < 2 ^ k) (hy : y < 2 ^ k) :
    meta29956_boundRun (meta29956_wordBits k x) (meta29956_wordBits k y) = some true ↔ x < y := by
  rw [meta29956_boundRun_strict _ _ (by simp [meta29956_wordBits_length]),
    meta29956_wordBits_value_of_lt k x hx, meta29956_wordBits_value_of_lt k y hy]

def meta29956_boundAllowed (less a b : Bool) : Bool :=
  less || !a || b

def meta29956_boundNext (less a b : Bool) : Bool :=
  less || (!a && b)

lemma meta29956_boundStep_live (less a b : Bool) :
    meta29956_boundStep (some less) (a, b) =
      if meta29956_boundAllowed less a b then
        some (meta29956_boundNext less a b) else none := by
  cases less <;> cases a <;> cases b <;> rfl

lemma meta29956_boundRun_bits_fold (k x y : Nat) :
    meta29956_boundRun (meta29956_wordBits k x) (meta29956_wordBits k y) =
      (List.range k).reverse.foldl
        (fun q pos => meta29956_boundStep q (x.testBit pos, y.testBit pos)) (some false) := by
  simp only [meta29956_boundRun, meta29956_wordBits, List.zip_eq_zipWith,
    List.zipWith_map, List.zipWith_self, List.foldl_map]

lemma meta29956_boundFold_accepts (k x y : Nat) (hx : x < 2 ^ k) (hy : y < 2 ^ k) :
    (List.range k).reverse.foldl
      (fun q pos => meta29956_boundStep q (x.testBit pos, y.testBit pos)) (some false) ≠ none
      ↔ x ≤ y := by
  rw [← meta29956_boundRun_bits_fold]
  exact meta29956_boundRun_bits_accepts k x y hx hy

lemma meta29956_boundFold_strict (k x y : Nat) (hx : x < 2 ^ k) (hy : y < 2 ^ k) :
    (List.range k).reverse.foldl
      (fun q pos => meta29956_boundStep q (x.testBit pos, y.testBit pos)) (some false) = some true
      ↔ x < y := by
  rw [← meta29956_boundRun_bits_fold]
  exact meta29956_boundRun_bits_strict k x y hx hy

lemma meta29956_wordValue_append (x y : List Bool) :
    meta29956_wordValue (x ++ y) =
      meta29956_wordValue x * 2 ^ y.length + meta29956_wordValue y := by
  induction x with
  | nil => simp [meta29956_wordValue]
  | cons a x ih =>
      simp [meta29956_wordValue, ih, Nat.pow_add, Nat.add_mul,
        Nat.mul_assoc, Nat.add_assoc]

lemma meta29956_wordValue_snoc (x : List Bool) (a : Bool) :
    meta29956_wordValue (x ++ [a]) = 2 * meta29956_wordValue x + a.toNat := by
  simp [meta29956_wordValue_append, meta29956_wordValue, Nat.mul_comm]

lemma meta29956_wordValue_injective_of_length (x y : List Bool)
    (hlen : x.length = y.length) (hval : meta29956_wordValue x = meta29956_wordValue y) :
    x = y := by
  induction x generalizing y with
  | nil =>
      cases y with
      | nil => rfl
      | cons b y => simp at hlen
  | cons a x ih =>
      cases y with
      | nil => simp at hlen
      | cons b y =>
          have hlen' : x.length = y.length := by simpa using hlen
          have hx := meta29956_wordValue_lt x
          have hy := meta29956_wordValue_lt y
          rw [hlen'] at hx
          cases a <;> cases b
          · simp only [meta29956_wordValue, Bool.toNat_false,
              Nat.zero_mul, Nat.zero_add] at hval
            rw [ih y hlen' hval]
          · simp only [meta29956_wordValue, Bool.toNat_false, Bool.toNat_true,
              Nat.zero_mul, Nat.one_mul, Nat.zero_add] at hval
            omega
          · simp only [meta29956_wordValue, Bool.toNat_false, Bool.toNat_true,
              Nat.zero_mul, Nat.one_mul, Nat.zero_add, hlen'] at hval
            omega
          · simp only [meta29956_wordValue, Bool.toNat_true, Nat.one_mul, hlen',
              Nat.add_left_cancel_iff] at hval
            rw [ih y hlen' hval]

end PEqualNP.Outside.L_meta_29956_aux

namespace PEqualNP.Outside.L_meta_29956_aux

lemma meta29956_reverseLess_wordValue (x y : List Bool) (hlen : x.length = y.length) :
    pnp29956_reverseLess x y ↔
      meta29956_wordValue x.reverse < meta29956_wordValue y.reverse := by
  induction x generalizing y with
  | nil =>
      cases y with
      | nil => simp [pnp29956_reverseLess, meta29956_wordValue]
      | cons b y => simp at hlen
  | cons a x ih =>
      cases y with
      | nil => simp at hlen
      | cons b y =>
          have hlen' : x.length = y.length := by simpa using hlen
          have ih' := ih y hlen'
          have heq : x = y ↔ meta29956_wordValue x.reverse = meta29956_wordValue y.reverse := by
            constructor
            · intro h
              rw [h]
            · intro h
              have hrev := meta29956_wordValue_injective_of_length x.reverse y.reverse
                (by simpa using hlen') h
              simpa using hrev
          cases a <;> cases b <;>
            simp only [pnp29956_reverseLess, ih', heq, List.reverse_cons,
              meta29956_wordValue_snoc, Bool.toNat_false, Bool.toNat_true,
              Bool.false_eq_true, Bool.true_eq_false, and_false, and_true,
              or_false, Nat.add_zero] <;> omega

lemma meta29956_reverseLess_bits (k x y : Nat) (hx : x < 2 ^ k) (hy : y < 2 ^ k) :
    pnp29956_reverseLess ((List.range k).map x.testBit) ((List.range k).map y.testBit) ↔
      x < y := by
  rw [meta29956_reverseLess_wordValue _ _ (by simp)]
  have hreverse (n : Nat) : ((List.range k).map n.testBit).reverse = meta29956_wordBits k n := by
    simp [meta29956_wordBits]
  rw [hreverse x, hreverse y, meta29956_wordBits_value_of_lt k x hx,
    meta29956_wordBits_value_of_lt k y hy]

end PEqualNP.Outside.L_meta_29956_aux

namespace PEqualNP.Outside.L_meta_29956_aux

def pnp29956_boolComparisonStep {Q : Type*} (left right : Bool → Q → Q)
    (E : Q → Q → Bool) : Q → Q → Bool :=
  fun q q' => E (left false q) (right false q') && E (left true q) (right true q')

def pnp29956_decodeBoolTable {Q : Type*} (E : Q → Q → Bool) : Q → Q → Prop :=
  fun q q' => E q q' = true

def pnp29956_decodeBoolState {Q : Type*}
    (state : (Q → Q → Bool) × Set (Q → Q → Bool)) :
    (Q → Q → Prop) × Set (Q → Q → Prop) :=
  (pnp29956_decodeBoolTable state.1, pnp29956_decodeBoolTable '' state.2)

def pnp29956_boolStateStep {A Q : Type*}
    (delta : A → Bool → Bool → Q → Q)
    (state : (Q → Q → Bool) × Set (Q → Q → Bool)) (letter : A × Bool) :
    (Q → Q → Bool) × Set (Q → Q → Bool) :=
  (pnp29956_boolComparisonStep (delta letter.1 letter.2) (delta letter.1 letter.2) state.1,
    {F | (∃ G ∈ state.2, ∃ rival : Bool,
      F = pnp29956_boolComparisonStep (delta letter.1 letter.2) (delta letter.1 rival) G) ∨
      (letter.2 = true ∧ F =
        pnp29956_boolComparisonStep (delta letter.1 true) (delta letter.1 false) state.1)})

lemma pnp29956_decodeBoolTable_step {Q : Type*} (left right : Bool → Q → Q)
    (E : Q → Q → Bool) :
    pnp29956_decodeBoolTable (pnp29956_boolComparisonStep left right E) =
      pnp29956_comparisonStep left right (pnp29956_decodeBoolTable E) := by
  funext q q'
  apply propext
  change (Bool.and _ _ = true) ↔ ∀ bit : Bool, _
  rw [Bool.and_eq_true]
  constructor
  · rintro ⟨hf, ht⟩ bit
    cases bit
    · exact hf
    · exact ht
  · intro h
    exact ⟨h false, h true⟩

lemma pnp29956_decodeBoolTable_injective {Q : Type*} :
    Function.Injective (@pnp29956_decodeBoolTable Q) := by
  intro E F h
  funext q q'
  have h' := congrFun (congrFun h q) q'
  change (E q q' = true) = (F q q' = true) at h'
  cases hE : E q q' <;> cases hF : F q q' <;> simp_all

lemma pnp29956_decodeBoolState_step {A Q : Type*}
    (delta : A → Bool → Bool → Q → Q)
    (state : (Q → Q → Bool) × Set (Q → Q → Bool)) (letter : A × Bool) :
    pnp29956_decodeBoolState (pnp29956_boolStateStep delta state letter) =
      pnp29956_stateStep delta (pnp29956_decodeBoolState state) letter := by
  apply Prod.ext
  · exact pnp29956_decodeBoolTable_step _ _ _
  · apply Set.ext
    intro F
    constructor
    · rintro ⟨B, hB, rfl⟩
      rcases hB with ⟨G, hG, rival, rfl⟩ | ⟨hbit, rfl⟩
      · left
        exact ⟨pnp29956_decodeBoolTable G, ⟨G, hG, rfl⟩, rival,
          pnp29956_decodeBoolTable_step _ _ _⟩
      · right
        exact ⟨hbit, pnp29956_decodeBoolTable_step _ _ _⟩
    · rintro (⟨G, ⟨B, hB, rfl⟩, rival, rfl⟩ | ⟨hbit, rfl⟩)
      · exact ⟨pnp29956_boolComparisonStep (delta letter.1 letter.2)
          (delta letter.1 rival) B,
          Or.inl ⟨B, hB, rival, rfl⟩, pnp29956_decodeBoolTable_step _ _ _⟩
      · exact ⟨pnp29956_boolComparisonStep (delta letter.1 true)
          (delta letter.1 false) state.1,
          Or.inr ⟨hbit, rfl⟩, pnp29956_decodeBoolTable_step _ _ _⟩

lemma pnp29956_decodeBoolState_fold {A Q : Type*}
    (delta : A → Bool → Bool → Q → Q)
    (letters : List (A × Bool)) (state : (Q → Q → Bool) × Set (Q → Q → Bool)) :
    pnp29956_decodeBoolState (letters.foldl (pnp29956_boolStateStep delta) state) =
      letters.foldl (pnp29956_stateStep delta) (pnp29956_decodeBoolState state) := by
  induction letters generalizing state with
  | nil => rfl
  | cons letter letters ih =>
      rw [List.foldl_cons, List.foldl_cons, ih, pnp29956_decodeBoolState_step]

lemma pnp29956_decodeBoolState_initial {Q : Type*} (finish : Q → Bool) :
    pnp29956_decodeBoolState ((fun q q' => decide (finish q = finish q')), ∅) =
      ((fun q q' => finish q = finish q'), ∅) := by
  apply Prod.ext
  · funext q q'
    simp [pnp29956_decodeBoolState, pnp29956_decodeBoolTable]
  · apply Set.ext
    intro F
    constructor
    · rintro ⟨B, hB, _⟩
      exact False.elim hB
    · intro h
      exact False.elim h

lemma pnp29956_boolStateFold_semantics {A Q : Type*}
    (delta : A → Bool → Bool → Q → Q) (finish : Q → Bool)
    (letters : List (A × Bool)) :
    pnp29956_decodeBoolState (letters.foldl (pnp29956_boolStateStep delta)
      ((fun q q' => decide (finish q = finish q')), ∅)) =
      pnp29956_comparisonState delta (fun q q' => finish q = finish q') letters.reverse := by
  rw [pnp29956_decodeBoolState_fold, pnp29956_decodeBoolState_initial,
    pnp29956_stateFold_initial]

lemma pnp29956_boolState_noRival {Q : Type*}
    (state : (Q → Q → Bool) × Set (Q → Q → Bool)) (start : Q) :
    (∀ B ∈ state.2, B start start = false) ↔
      (∀ F ∈ (pnp29956_decodeBoolState state).2, ¬ F start start) := by
  constructor
  · intro h F hF
    rcases hF with ⟨B, hB, rfl⟩
    change ¬ B start start = true
    rw [h B hB]
    decide
  · intro h B hB
    have hfalse : ¬ B start start = true := h _ ⟨B, hB, rfl⟩
    cases hval : B start start
    · rfl
    · exact False.elim (hfalse hval)

lemma pnp29956_boolStateFold_noRival_iff_least {A Q : Type*}
    (delta : A → Bool → Bool → Q → Q) (finish : Q → Bool)
    (letters : List (A × Bool)) (start : Q) :
    (∀ B ∈ (letters.foldl (pnp29956_boolStateStep delta)
      ((fun q q' => decide (finish q = finish q')), ∅)).2, B start start = false) ↔
    ¬ ∃ rival : List Bool,
      pnp29956_reverseLess rival (letters.reverse.map Prod.snd) ∧
      ∀ columns : List Bool, columns.length = letters.reverse.length →
        finish (pnp29956_forwardRun delta letters.reverse columns start) =
          finish (pnp29956_forwardRun delta
            (List.zip (letters.reverse.map Prod.fst) rival) columns start) := by
  rw [pnp29956_boolState_noRival, pnp29956_boolStateFold_semantics]
  exact pnp29956_noRival_iff_least delta finish letters.reverse start

end PEqualNP.Outside.L_meta_29956_aux

namespace PEqualNP.Outside.L_meta_29956_aux

def pnp29956_coupledStep {A B S : Type*}
    (control : B → A → Option B) (update : S → A → S)
    (state : Option (B × S)) (letter : A) : Option (B × S) :=
  state.bind (fun bs => (control bs.1 letter).map (fun b => (b, update bs.2 letter)))

lemma pnp29956_coupledFold {A B S : Type*}
    (control : B → A → Option B) (update : S → A → S)
    (letters : List A) (controlState : Option B) (state : S) :
    letters.foldl (pnp29956_coupledStep control update)
      (controlState.map (fun b => (b, state))) =
    (letters.foldl (fun ob a => ob.bind (fun b => control b a)) controlState).map
      (fun b => (b, letters.foldl update state)) := by
  induction letters generalizing controlState state with
  | nil => rfl
  | cons a letters ih =>
      cases controlState with
      | none =>
          simpa [pnp29956_coupledStep] using ih none (update state a)
      | some b =>
          simpa [pnp29956_coupledStep] using ih (control b a) (update state a)

lemma pnp29956_coupledFold_accepts {A B S : Type*}
    (control : B → A → Option B) (update : S → A → S)
    (letters : List A) (controlState : Option B) (state : S) (finish : S → Prop) :
    (∃ bs, letters.foldl (pnp29956_coupledStep control update)
      (controlState.map (fun b => (b, state))) = some bs ∧ finish bs.2) ↔
    (letters.foldl (fun ob a => ob.bind (fun b => control b a)) controlState ≠ none ∧
      finish (letters.foldl update state)) := by
  rw [pnp29956_coupledFold]
  cases letters.foldl (fun ob a => ob.bind (fun b => control b a)) controlState <;> simp

end PEqualNP.Outside.L_meta_29956_aux

namespace PEqualNP.Outside.L_meta_29956_aux

def pnp29956_machineStep {A Q : Type*}
    (delta : A → Bool → Bool → Q → Q)
    (letter : A × Bool) (rowBit : Bool)
    (state : Bool × (Q → Q → Bool) × Set (Q → Q → Bool)) :
    Option (Bool × (Q → Q → Bool) × Set (Q → Q → Bool)) :=
  if meta29956_boundAllowed state.1 rowBit letter.2 then
    some (meta29956_boundNext state.1 rowBit letter.2,
      pnp29956_boolStateStep delta state.2 (letter.1, rowBit))
  else none

lemma pnp29956_machineStep_coupled {A Q : Type*}
    (delta : A → Bool → Bool → Q → Q)
    (letter : (A × Bool) × Bool)
    (state : Option (Bool × (Q → Q → Bool) × Set (Q → Q → Bool))) :
    state.bind (pnp29956_machineStep delta letter.1 letter.2) =
      pnp29956_coupledStep
        (fun lower z => meta29956_boundStep (some lower) (z.2, z.1.2))
        (fun s z => pnp29956_boolStateStep delta s (z.1.1, z.2)) state letter := by
  cases state with
  | none => rfl
  | some state =>
      simp only [Option.bind_some, pnp29956_coupledStep, meta29956_boundStep_live,
        pnp29956_machineStep]
      split <;> rfl

lemma pnp29956_machineRun_accepts {A Q : Type*}
    (delta : A → Bool → Bool → Q → Q)
    (letters : List ((A × Bool) × Bool))
    (initial : (Q → Q → Bool) × Set (Q → Q → Bool)) (finish :
      ((Q → Q → Bool) × Set (Q → Q → Bool)) → Prop) :
    (∃ s, letters.foldl (fun state z =>
      state.bind (pnp29956_machineStep delta z.1 z.2)) (some (false, initial)) = some s ∧
      finish s.2) ↔
    (meta29956_boundRun (letters.map (fun z => z.2))
        (letters.map (fun z => z.1.2)) ≠ none ∧
      finish ((letters.map (fun z => (z.1.1, z.2))).foldl
        (pnp29956_boolStateStep delta) initial)) := by
  have hstep : (fun (state : Option (Bool × (Q → Q → Bool) × Set (Q → Q → Bool)))
      (z : (A × Bool) × Bool) =>
      state.bind (pnp29956_machineStep delta z.1 z.2)) =
      pnp29956_coupledStep
        (fun lower (z : (A × Bool) × Bool) =>
          meta29956_boundStep (some lower) (z.2, z.1.2))
        (fun s z => pnp29956_boolStateStep delta s (z.1.1, z.2)) := by
    funext state z
    exact pnp29956_machineStep_coupled delta z state
  rw [hstep]
  have h := pnp29956_coupledFold_accepts
    (fun lower (z : (A × Bool) × Bool) =>
      meta29956_boundStep (some lower) (z.2, z.1.2))
    (fun s z => pnp29956_boolStateStep delta s (z.1.1, z.2))
    letters (some false) initial finish
  have hb : (fun (ob : Option Bool) (z : (A × Bool) × Bool) =>
      ob.bind (fun lower => meta29956_boundStep (some lower) (z.2, z.1.2))) =
      fun ob z => meta29956_boundStep ob (z.2, z.1.2) := by
    funext ob z
    cases ob <;> rfl
  simpa only [Option.map_some, hb, meta29956_boundRun, List.zip_eq_zipWith,
    List.zipWith_map, List.zipWith_self, List.foldl_map] using h

end PEqualNP.Outside.L_meta_29956_aux

namespace PEqualNP.Outside.L_meta_29956_aux

lemma meta29956_wordBits_inverse (w : List Bool) :
    meta29956_wordBits w.length (meta29956_wordValue w) = w := by
  apply meta29956_wordValue_injective_of_length
  · exact meta29956_wordBits_length _ _
  · exact meta29956_wordBits_value_of_lt _ _ (meta29956_wordValue_lt w)

def meta29956_lowBits (k n : Nat) : List Bool :=
  (List.range k).map n.testBit

lemma meta29956_lowBits_length (k n : Nat) :
    (meta29956_lowBits k n).length = k := by
  simp [meta29956_lowBits]

lemma meta29956_lowBits_reverse (k n : Nat) :
    (meta29956_lowBits k n).reverse = meta29956_wordBits k n := by
  simp [meta29956_lowBits, meta29956_wordBits]

lemma meta29956_lowBits_value (k n : Nat) :
    meta29956_wordValue (meta29956_lowBits k n).reverse = n % 2 ^ k := by
  rw [meta29956_lowBits_reverse, meta29956_wordBits_value]

lemma meta29956_lowBits_value_of_lt (k n : Nat) (hn : n < 2 ^ k) :
    meta29956_wordValue (meta29956_lowBits k n).reverse = n := by
  rw [meta29956_lowBits_value, Nat.mod_eq_of_lt hn]

lemma meta29956_lowBits_inverse (w : List Bool) :
    meta29956_lowBits w.length (meta29956_wordValue w.reverse) = w := by
  apply List.reverse_injective
  rw [meta29956_lowBits_reverse]
  simpa only [List.length_reverse] using meta29956_wordBits_inverse w.reverse

lemma meta29956_lowBits_inverse_of_length (k : Nat) (w : List Bool) (hlen : w.length = k) :
    meta29956_lowBits k (meta29956_wordValue w.reverse) = w := by
  rw [← hlen]
  exact meta29956_lowBits_inverse w

def meta29956_bitWordsEquiv (k : Nat) :
    {w : List Bool // w.length = k} ≃ Fin (2 ^ k) where
  toFun w := ⟨meta29956_wordValue w.val.reverse, by
    simpa only [List.length_reverse, w.property] using meta29956_wordValue_lt w.val.reverse⟩
  invFun n := ⟨meta29956_lowBits k n.val, meta29956_lowBits_length k n.val⟩
  left_inv w := by
    apply Subtype.ext
    exact meta29956_lowBits_inverse_of_length k w.val w.property
  right_inv n := by
    apply Fin.ext
    exact meta29956_lowBits_value_of_lt k n.val n.isLt

lemma meta29956_forall_lowBits (k : Nat) (P : List Bool → Prop) :
    (∀ w : List Bool, w.length = k → P w) ↔
      ∀ n : Fin (2 ^ k), P (meta29956_lowBits k n.val) := by
  constructor
  · intro h n
    exact h _ (meta29956_lowBits_length k n.val)
  · intro h w hlen
    let n : Fin (2 ^ k) := ⟨meta29956_wordValue w.reverse, by
      simpa only [List.length_reverse, hlen] using meta29956_wordValue_lt w.reverse⟩
    have hn := h n
    change P (meta29956_lowBits k (meta29956_wordValue w.reverse)) at hn
    rwa [meta29956_lowBits_inverse_of_length k w hlen] at hn

lemma meta29956_exists_lowBits (k : Nat) (P : List Bool → Prop) :
    (∃ w : List Bool, w.length = k ∧ P w) ↔
      ∃ n : Fin (2 ^ k), P (meta29956_lowBits k n.val) := by
  constructor
  · rintro ⟨w, hlen, hw⟩
    refine ⟨⟨meta29956_wordValue w.reverse, ?_⟩, ?_⟩
    · simpa only [List.length_reverse, hlen] using meta29956_wordValue_lt w.reverse
    · simpa only [meta29956_lowBits_inverse_of_length k w hlen] using hw
  · rintro ⟨n, hn⟩
    exact ⟨_, meta29956_lowBits_length k n.val, hn⟩

end PEqualNP.Outside.L_meta_29956_aux

namespace PEqualNP.Outside.L_meta_29956_aux

lemma pnp29956_least_representatives_card {α β : Type*}
    [Fintype α] [LinearOrder α] [DecidableEq β] (f : α → β) (bound : α) :
    (Finset.univ.filter (fun x => x ≤ bound ∧ ∀ y, y < x → f y ≠ f x)).card =
      ((Finset.univ.filter (fun x => x ≤ bound)).image f).card := by
  classical
  let S := Finset.univ.filter (fun x => x ≤ bound ∧ ∀ y, y < x → f y ≠ f x)
  let T := Finset.univ.filter (fun x => x ≤ bound)
  have hinj : Set.InjOn f S := by
    intro x hx y hy hxy
    have hx' := (Finset.mem_filter.mp hx).2.2
    have hy' := (Finset.mem_filter.mp hy).2.2
    rcases lt_trichotomy x y with hlt | heq | hgt
    · exact False.elim (hy' x hlt hxy)
    · exact heq
    · exact False.elim (hx' y hgt hxy.symm)
  have himage : S.image f = T.image f := by
    apply Finset.ext
    intro v
    constructor
    · intro hv
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
      apply Finset.mem_image.mpr
      exact ⟨x, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2.1⟩, rfl⟩
    · intro hv
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
      let C := Finset.univ.filter (fun y => f y = f x)
      have hC : C.Nonempty := ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
      let m := C.min' hC
      have hmC : m ∈ C := Finset.min'_mem C hC
      have hmf : f m = f x := (Finset.mem_filter.mp hmC).2
      have hmx : m ≤ x := Finset.min'_le C x
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)
      have hmS : m ∈ S := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, le_trans hmx (Finset.mem_filter.mp hx).2, ?_⟩
        intro y hym hyf
        have hyC : y ∈ C := Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hyf.trans hmf⟩
        exact (not_lt_of_ge (Finset.min'_le C y hyC)) hym
      exact Finset.mem_image.mpr ⟨m, hmS, hmf⟩
  calc
    S.card = (S.image f).card := (Finset.card_image_of_injOn hinj).symm
    _ = (T.image f).card := congrArg Finset.card himage

end PEqualNP.Outside.L_meta_29956_aux

namespace PEqualNP.Outside.L_meta_29956_aux

open Finset

lemma sum_count_mul {S : Type*} [Fintype S] [DecidableEq S]
    (states : List S) (f : S → ℕ) :
    (∑ q : S, states.count q * f q) = (states.map f).sum := by
  induction states with
  | nil => simp
  | cons q qs ih =>
    simp only [List.count_cons, Nat.add_mul, Finset.sum_add_distrib]
    rw [ih]
    simp [add_comm]

lemma count_flatMap_eq {S : Type*} [Fintype S] [DecidableEq S]
    (states : List S) (next : S → List S) (dst : S) :
    (∑ src : S, states.count src * (next src).count dst) =
      (states.flatMap next).count dst := by
  rw [sum_count_mul]
  induction states with
  | nil => simp
  | cons q qs ih => simp [ih, List.flatMap_cons, List.count_append]

lemma fold_counts_eq {A S : Type*} [Fintype S] [DecidableEq S]
    (next : A → S → List S) (letters : List A) (states : List S) :
    letters.foldl (fun v a dst => ∑ src : S, v src * (next a src).count dst)
        (fun q => states.count q) =
      fun q => (letters.foldl (fun qs a => qs.flatMap (next a)) states).count q := by
  induction letters generalizing states with
  | nil => rfl
  | cons a letters ih =>
    simp only [List.foldl_cons]
    have h : (fun dst => ∑ src : S, states.count src * (next a src).count dst) =
        (fun dst => (states.flatMap (next a)).count dst) := by
      funext dst
      exact count_flatMap_eq states (next a) dst
    rw [h]
    exact ih _

lemma sum_count_filter {S : Type*} [Fintype S] [DecidableEq S]
    (states : List S) (finish : S → Bool) :
    (∑ q : S, if finish q then states.count q else 0) =
      (states.filter finish).length := by
  have h : (∑ q : S, if finish q then states.count q else 0) =
      ∑ q : S, states.count q * (if finish q then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro q _
    cases finish q <;> simp
  rw [h, sum_count_mul]
  clear h
  induction states with
  | nil => simp
  | cons q qs ih => cases hq : finish q <;> simp [hq, ih, add_comm]

lemma transfer_counts_eq {A S : Type*} [Fintype S] [DecidableEq S]
    (next : A → S → List S) (letters : List A) (start : S) (finish : S → Bool) :
    let counts := letters.foldl
      (fun v a dst => ∑ src : S, v src * (next a src).count dst)
      (fun q => (decide (q = start)).toNat)
    (∑ q : S, if finish q then counts q else 0) =
      ((letters.foldl (fun qs a => qs.flatMap (next a)) [start]).filter finish).length := by
  dsimp only
  have h : (fun q : S => (decide (q = start)).toNat) =
      (fun q => [start].count q) := by
    funext q
    by_cases hq : q = start
    · subst q
      simp
    · have hs : start ≠ q := Ne.symm hq
      simp only [List.count_cons, List.count_nil]
      simp [hq, hs]
  rw [h, fold_counts_eq]
  exact sum_count_filter _ _

def bitSuccessors {A S : Type*} (step : A → Bool → S → Option S)
    (letter : A) (state : S) : List S :=
  [false, true].filterMap (fun bit => step letter bit state)

lemma bitSuccessors_length {A S : Type*} (step : A → Bool → S → Option S)
    (letter : A) (state : S) : (bitSuccessors step letter state).length ≤ 2 := by
  exact List.length_filterMap_le _ _

def bitWeight {A S : Type*} [DecidableEq S] (step : A → Bool → S → Option S)
    (letter : A) (src dst : S) : Fin 3 :=
  ⟨(bitSuccessors step letter src).count dst,
    Nat.lt_succ_of_le (List.count_le_length.trans (bitSuccessors_length step letter src))⟩

lemma bit_transfer_counts_eq {A S : Type*} [Fintype S] [DecidableEq S]
    (step : A → Bool → S → Option S) (letters : List A) (start : S)
    (finish : S → Bool) :
    let counts := letters.foldl
      (fun v a dst => ∑ src : S, v src * (bitWeight step a src dst).val)
      (fun q => (decide (q = start)).toNat)
    (∑ q : S, if finish q then counts q else 0) =
      ((letters.foldl (fun qs a => qs.flatMap (bitSuccessors step a)) [start]).filter
        finish).length :=
  transfer_counts_eq (bitSuccessors step) letters start finish

end PEqualNP.Outside.L_meta_29956_aux

namespace PEqualNP.Outside.L_meta_29956_aux

def enumBitWords : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (enumBitWords n).map (false :: ·) ++ (enumBitWords n).map (true :: ·)

def runBitWord {A S : Type*} (step : A → Bool → S → Option S) :
    List A → List Bool → S → Option S
  | [], [], s => some s
  | a :: letters, bit :: bits, s =>
      (step a bit s).bind (runBitWord step letters bits)
  | _, _, _ => none

def bitBranches {A S : Type*} (step : A → Bool → S → Option S) : List A → S → List S
  | [], s => [s]
  | a :: letters, s =>
      ([false, true].filterMap (fun bit => step a bit s)).flatMap (bitBranches step letters)

lemma bitBranches_eq_filterMap {A S : Type*} (step : A → Bool → S → Option S)
    (letters : List A) (start : S) :
    bitBranches step letters start =
      (enumBitWords letters.length).filterMap (fun bits => runBitWord step letters bits start) := by
  induction letters generalizing start with
  | nil => simp [bitBranches, enumBitWords, runBitWord]
  | cons a letters ih =>
    cases h0 : step a false start <;> cases h1 : step a true start <;>
      simp [bitBranches, enumBitWords, runBitWord, h0, h1, ih, Function.comp_def]

lemma branches_fold_append {A S : Type*} (next : A → S → List S)
    (letters : List A) (xs ys : List S) :
    letters.foldl (fun qs a => qs.flatMap (next a)) (xs ++ ys) =
      letters.foldl (fun qs a => qs.flatMap (next a)) xs ++
        letters.foldl (fun qs a => qs.flatMap (next a)) ys := by
  induction letters generalizing xs ys with
  | nil => rfl
  | cons a letters ih => simp only [List.foldl_cons, List.flatMap_append, ih]

lemma branches_fold_nil {A S : Type*} (next : A → S → List S) (letters : List A) :
    letters.foldl (fun qs a => qs.flatMap (next a)) [] = [] := by
  induction letters with
  | nil => rfl
  | cons a letters ih => simpa using ih

lemma branches_fold_flatMap {A S : Type*} (next : A → S → List S)
    (letters : List A) (states : List S) :
    letters.foldl (fun qs a => qs.flatMap (next a)) states =
      states.flatMap (fun s => letters.foldl (fun qs a => qs.flatMap (next a)) [s]) := by
  induction states with
  | nil => simp [branches_fold_nil]
  | cons s states ih =>
    change letters.foldl _ ([s] ++ states) = _
    rw [branches_fold_append, ih]
    rfl

lemma bit_fold_eq_branches {A S : Type*} (step : A → Bool → S → Option S)
    (letters : List A) (start : S) :
    letters.foldl
        (fun qs a => qs.flatMap (fun s => [false, true].filterMap (fun bit => step a bit s)))
        [start] = bitBranches step letters start := by
  induction letters generalizing start with
  | nil => rfl
  | cons a letters ih =>
    simp only [List.foldl_cons, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [branches_fold_flatMap]
    simp only [ih, bitBranches]

lemma mem_enumBitWords (n : ℕ) (bits : List Bool) :
    bits ∈ enumBitWords n ↔ bits.length = n := by
  induction n generalizing bits with
  | zero => simp [enumBitWords]
  | succ n ih =>
    cases bits with
    | nil => simp [enumBitWords]
    | cons bit bits => cases bit <;> simp [enumBitWords, ih]

lemma enumBitWords_nodup (n : ℕ) : (enumBitWords n).Nodup := by
  induction n with
  | zero => simp [enumBitWords]
  | succ n ih =>
    rw [enumBitWords, List.nodup_append]
    refine ⟨ih.map (by intro a b h; simpa using h),
      ih.map (by intro a b h; simpa using h), ?_⟩
    simp

end PEqualNP.Outside.L_meta_29956_aux

namespace PEqualNP.Outside.L_meta_29956_aux

lemma bit_transfer_eq_words {A S : Type*} [Fintype S] [DecidableEq S]
    (step : A → Bool → S → Option S) (letters : List A) (start : S)
    (finish : S → Bool) :
    let counts := letters.foldl
      (fun v a dst => ∑ src : S, v src * (bitWeight step a src dst).val)
      (fun q => (decide (q = start)).toNat)
    (∑ q : S, if finish q then counts q else 0) =
      ((enumBitWords letters.length).filter (fun bits =>
        ((runBitWord step letters bits start).map finish).getD false)).length := by
  dsimp only
  rw [bit_transfer_counts_eq]
  change (List.filter finish (letters.foldl
    (fun qs a => qs.flatMap (fun s => [false, true].filterMap (fun bit => step a bit s)))
    [start])).length = _
  rw [bit_fold_eq_branches, bitBranches_eq_filterMap]
  rw [← List.countP_eq_length_filter, List.countP_filterMap, List.countP_eq_length_filter]

end PEqualNP.Outside.L_meta_29956_aux

namespace PEqualNP.Outside.L_meta_29956_aux

def pnp29956_finiteRowWord {A : Type*} {k : Nat} (symbols : Fin k → A)
    (x : Fin (2 ^ k)) : List (A × Bool) :=
  List.ofFn (fun i : Fin k => (symbols i, x.val.testBit i.val))

lemma pnp29956_finiteRowWord_length {A : Type*} {k : Nat} (symbols : Fin k → A)
    (x : Fin (2 ^ k)) : (pnp29956_finiteRowWord symbols x).length = k := by
  simp [pnp29956_finiteRowWord]

lemma pnp29956_finiteRowWord_snd {A : Type*} {k : Nat} (symbols : Fin k → A)
    (x : Fin (2 ^ k)) :
    (pnp29956_finiteRowWord symbols x).map Prod.snd = meta29956_lowBits k x.val := by
  apply List.ext_getElem
  · simp [pnp29956_finiteRowWord, meta29956_lowBits]
  · intro i hi hj
    simp [pnp29956_finiteRowWord, meta29956_lowBits]

lemma pnp29956_finiteRowWord_zip {A : Type*} {k : Nat} (symbols : Fin k → A)
    (x z : Fin (2 ^ k)) :
    List.zip ((pnp29956_finiteRowWord symbols x).map Prod.fst) (meta29956_lowBits k z.val) =
      pnp29956_finiteRowWord symbols z := by
  apply List.ext_getElem
  · simp [pnp29956_finiteRowWord, meta29956_lowBits]
  · intro i hi hj
    simp [pnp29956_finiteRowWord, meta29956_lowBits]

def pnp29956_finiteRow {A Q : Type*} {k : Nat}
    (delta : A → Bool → Bool → Q → Q) (finish : Q → Bool) (start : Q)
    (symbols : Fin k → A) (x y : Fin (2 ^ k)) : Bool :=
  finish (pnp29956_forwardRun delta (pnp29956_finiteRowWord symbols x)
    (meta29956_lowBits k y.val) start)

lemma pnp29956_finiteRow_eq_iff {A Q : Type*} {k : Nat}
    (delta : A → Bool → Bool → Q → Q) (finish : Q → Bool) (start : Q)
    (symbols : Fin k → A) (x z : Fin (2 ^ k)) :
    (∀ columns : List Bool, columns.length = k →
      finish (pnp29956_forwardRun delta (pnp29956_finiteRowWord symbols x) columns start) =
        finish (pnp29956_forwardRun delta
          (List.zip ((pnp29956_finiteRowWord symbols x).map Prod.fst)
            (meta29956_lowBits k z.val)) columns start)) ↔
      pnp29956_finiteRow delta finish start symbols x =
        pnp29956_finiteRow delta finish start symbols z := by
  rw [pnp29956_finiteRowWord_zip]
  rw [meta29956_forall_lowBits]
  constructor
  · intro h
    funext y
    exact h y
  · intro h y
    exact congrFun h y

lemma pnp29956_boolStateFold_noRival_iff_finiteLeast {A Q : Type*} {k : Nat}
    (delta : A → Bool → Bool → Q → Q) (finish : Q → Bool) (start : Q)
    (symbols : Fin k → A) (x : Fin (2 ^ k)) :
    (∀ B ∈ ((pnp29956_finiteRowWord symbols x).reverse.foldl
      (pnp29956_boolStateStep delta)
      ((fun q q' => decide (finish q = finish q')), ∅)).2, B start start = false) ↔
      ∀ z : Fin (2 ^ k), z < x →
        pnp29956_finiteRow delta finish start symbols z ≠
          pnp29956_finiteRow delta finish start symbols x := by
  rw [pnp29956_boolStateFold_noRival_iff_least]
  simp only [List.reverse_reverse, pnp29956_finiteRowWord_length]
  constructor
  · intro h z hz hequal
    apply h
    refine ⟨meta29956_lowBits k z.val, ?_, ?_⟩
    · rw [pnp29956_finiteRowWord_snd]
      exact (meta29956_reverseLess_bits k z.val x.val z.isLt x.isLt).mpr hz
    · exact (pnp29956_finiteRow_eq_iff delta finish start symbols x z).mpr hequal.symm
  · rintro h ⟨rival, hless, hequal⟩
    have hlen : rival.length = k := by
      have hlen' := pnp29956_reverseLess_length hless
      simpa only [List.length_map, pnp29956_finiteRowWord_length] using hlen'
    let z : Fin (2 ^ k) := ⟨meta29956_wordValue rival.reverse, by
      simpa only [List.length_reverse, hlen] using meta29956_wordValue_lt rival.reverse⟩
    have hzbits : meta29956_lowBits k z.val = rival :=
      meta29956_lowBits_inverse_of_length k rival hlen
    have hzlt : z < x := by
      apply (meta29956_reverseLess_bits k z.val x.val z.isLt x.isLt).mp
      change pnp29956_reverseLess (meta29956_lowBits k z.val) (meta29956_lowBits k x.val)
      rw [hzbits]
      simpa only [pnp29956_finiteRowWord_snd] using hless
    apply h z hzlt
    apply Eq.symm
    apply (pnp29956_finiteRow_eq_iff delta finish start symbols x z).mp
    rwa [hzbits]

end PEqualNP.Outside.L_meta_29956_aux

namespace PEqualNP.Outside.L_meta_29956_aux

lemma pnp29956_foldBind_none {A S : Type*}
    (step : A → Bool → S → Option S) (letters : List (A × Bool)) :
    letters.foldl (fun state z => state.bind (step z.1 z.2)) none = none := by
  induction letters with
  | nil => rfl
  | cons z letters ih => simpa using ih

lemma pnp29956_runBitWord_eq_zipFold {A S : Type*}
    (step : A → Bool → S → Option S) (letters : List A) (bits : List Bool)
    (hlen : bits.length = letters.length) (start : S) :
    runBitWord step letters bits start =
      (letters.zip bits).foldl (fun state z => state.bind (step z.1 z.2)) (some start) := by
  induction letters generalizing bits start with
  | nil =>
      have hb : bits = [] := by simpa using hlen
      subst bits
      rfl
  | cons a letters ih =>
      cases bits with
      | nil => simp at hlen
      | cons bit bits =>
          have hl : bits.length = letters.length := by simpa using hlen
          simp only [runBitWord, List.zip_cons_cons, List.foldl_cons, Option.bind_some]
          cases hs : step a bit start with
          | none => simp [pnp29956_foldBind_none]
          | some state => simpa using ih bits hl state

end PEqualNP.Outside.L_meta_29956_aux

namespace PEqualNP.Outside.L_meta_29956_aux

def pnp29956_machineWord {A : Type*} {k : Nat}
    (symbolsNat : Nat → A) (bound x : Fin (2 ^ k)) : List ((A × Bool) × Bool) :=
  (List.range k).reverse.map
    (fun pos => ((symbolsNat pos, bound.val.testBit pos), x.val.testBit pos))

lemma pnp29956_machineWord_rowBits {A : Type*} {k : Nat}
    (symbolsNat : Nat → A) (bound x : Fin (2 ^ k)) :
    (pnp29956_machineWord symbolsNat bound x).map (fun z => z.2) =
      meta29956_wordBits k x.val := by
  simp only [pnp29956_machineWord, meta29956_wordBits, List.map_map, Function.comp_def]

lemma pnp29956_machineWord_boundBits {A : Type*} {k : Nat}
    (symbolsNat : Nat → A) (bound x : Fin (2 ^ k)) :
    (pnp29956_machineWord symbolsNat bound x).map (fun z => z.1.2) =
      meta29956_wordBits k bound.val := by
  simp only [pnp29956_machineWord, meta29956_wordBits, List.map_map, Function.comp_def]

lemma pnp29956_finiteRowWord_ofNat {A : Type*} {k : Nat}
    (symbolsNat : Nat → A) (x : Fin (2 ^ k)) :
    pnp29956_finiteRowWord (fun i : Fin k => symbolsNat i.val) x =
      (List.range k).map (fun pos => (symbolsNat pos, x.val.testBit pos)) := by
  apply List.ext_getElem
  · simp [pnp29956_finiteRowWord]
  · intro i hi hj
    simp [pnp29956_finiteRowWord]

lemma pnp29956_machineWord_rowWord {A : Type*} {k : Nat}
    (symbolsNat : Nat → A) (bound x : Fin (2 ^ k)) :
    (pnp29956_machineWord symbolsNat bound x).map (fun z => (z.1.1, z.2)) =
      (pnp29956_finiteRowWord (fun i : Fin k => symbolsNat i.val) x).reverse := by
  rw [pnp29956_finiteRowWord_ofNat]
  simp only [pnp29956_machineWord, List.map_map, Function.comp_def, List.map_reverse]

lemma pnp29956_machineNumeric_accepts {A Q : Type*} {k : Nat}
    (delta : A → Bool → Bool → Q → Q) (finish : Q → Bool) (start : Q)
    (symbolsNat : Nat → A) (bound x : Fin (2 ^ k)) :
    (∃ s, (pnp29956_machineWord symbolsNat bound x).foldl
      (fun state z => state.bind (pnp29956_machineStep delta z.1 z.2))
      (some (false, (fun q q' => decide (finish q = finish q')), ∅)) = some s ∧
      ∀ B ∈ s.2.2, B start start = false) ↔
      x ≤ bound ∧ ∀ z : Fin (2 ^ k), z < x →
        pnp29956_finiteRow delta finish start (fun i : Fin k => symbolsNat i.val) z ≠
          pnp29956_finiteRow delta finish start (fun i : Fin k => symbolsNat i.val) x := by
  rw [pnp29956_machineRun_accepts delta (pnp29956_machineWord symbolsNat bound x)
    ((fun q q' => decide (finish q = finish q')), ∅)
    (fun s => ∀ B ∈ s.2, B start start = false)]
  rw [pnp29956_machineWord_rowBits, pnp29956_machineWord_boundBits,
    meta29956_boundRun_bits_accepts k x.val bound.val x.isLt bound.isLt,
    pnp29956_machineWord_rowWord,
    pnp29956_boolStateFold_noRival_iff_finiteLeast]
  rfl

def pnp29956_machineLetters {A : Type*} {k : Nat}
    (symbolsNat : Nat → A) (bound : Fin (2 ^ k)) : List (A × Bool) :=
  (List.range k).reverse.map (fun pos => (symbolsNat pos, bound.val.testBit pos))

lemma pnp29956_machineLetters_zip {A : Type*} {k : Nat}
    (symbolsNat : Nat → A) (bound x : Fin (2 ^ k)) :
    (pnp29956_machineLetters symbolsNat bound).zip (meta29956_wordBits k x.val) =
      pnp29956_machineWord symbolsNat bound x := by
  simp only [pnp29956_machineLetters, meta29956_wordBits, List.zip_eq_zipWith,
    List.zipWith_map, List.zipWith_self, pnp29956_machineWord]

lemma pnp29956_machineBitWord_accepts {A Q : Type*} {k : Nat}
    (delta : A → Bool → Bool → Q → Q) (finish : Q → Bool) (start : Q)
    (symbolsNat : Nat → A) (bound x : Fin (2 ^ k)) :
    (∃ s, runBitWord (pnp29956_machineStep delta)
      (pnp29956_machineLetters symbolsNat bound) (meta29956_wordBits k x.val)
      (false, (fun q q' => decide (finish q = finish q')), ∅) = some s ∧
      ∀ B ∈ s.2.2, B start start = false) ↔
      x ≤ bound ∧ ∀ z : Fin (2 ^ k), z < x →
        pnp29956_finiteRow delta finish start (fun i : Fin k => symbolsNat i.val) z ≠
          pnp29956_finiteRow delta finish start (fun i : Fin k => symbolsNat i.val) x := by
  rw [pnp29956_runBitWord_eq_zipFold _ _ _
    (by simp [pnp29956_machineLetters, meta29956_wordBits_length]),
    pnp29956_machineLetters_zip]
  exact pnp29956_machineNumeric_accepts delta finish start symbolsNat bound x

end PEqualNP.Outside.L_meta_29956_aux

namespace PEqualNP.Outside.L_meta_29956_aux

def helper9Bits (k : ℕ) (x : Fin (2 ^ k)) : Fin k → Bool :=
  fun i => x.val.testBit i.val

lemma helper9_bits_above (k : ℕ) (x : Fin (2 ^ k)) (i : ℕ) (hi : k ≤ i) :
    x.val.testBit i = false := by
  apply Nat.testBit_eq_false_of_lt
  exact x.isLt.trans_le (Nat.pow_le_pow_right (by omega) hi)

lemma helper9_bits_injective (k : ℕ) : Function.Injective (helper9Bits k) := by
  intro x y h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < k
  · exact congrFun h ⟨i, hi⟩
  · rw [helper9_bits_above k x i (by omega), helper9_bits_above k y i (by omega)]

lemma helper9_bits_bijective (k : ℕ) : Function.Bijective (helper9Bits k) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  exact ⟨helper9_bits_injective k, by simp⟩

noncomputable def helper9BitsEquiv (k : ℕ) : Fin (2 ^ k) ≃ (Fin k → Bool) :=
  Equiv.ofBijective (helper9Bits k) (helper9_bits_bijective k)

def helper9Word (k : ℕ) (x : Fin (2 ^ k)) : {w : List Bool // w.length = k} :=
  ⟨List.ofFn (helper9Bits k x), List.length_ofFn⟩

lemma helper9_word_bijective (k : ℕ) : Function.Bijective (helper9Word k) := by
  constructor
  · intro x y h
    apply helper9_bits_injective k
    apply List.ofFn_injective
    exact congrArg Subtype.val h
  · rintro ⟨w, hw⟩
    subst k
    obtain ⟨x, hx⟩ := (helper9_bits_bijective w.length).2 w.get
    refine ⟨x, Subtype.ext ?_⟩
    change List.ofFn (helper9Bits w.length x) = w
    rw [hx, List.ofFn_get]

noncomputable def helper9WordEquiv (k : ℕ) :
    Fin (2 ^ k) ≃ {w : List Bool // w.length = k} :=
  Equiv.ofBijective (helper9Word k) (helper9_word_bijective k)

def helper9Value : List Bool → ℕ
  | [] => 0
  | bit :: bits => bit.toNat + 2 * helper9Value bits

lemma helper9_value_word (k : ℕ) (x : Fin (2 ^ k)) :
    helper9Value (helper9Word k x).val = x.val := by
  change helper9Value (List.ofFn (helper9Bits k x)) = x.val
  induction k with
  | zero =>
    simp [helper9Value]
  | succ k ih =>
    let y : Fin (2 ^ k) := ⟨x.val / 2, by
      have hx : x.val < 2 ^ k * 2 := by simpa only [pow_succ] using x.isLt
      omega⟩
    rw [List.ofFn_succ, helper9Value]
    have htail : (fun i : Fin k => helper9Bits (k + 1) x i.succ) = helper9Bits k y := by
      funext i
      exact Nat.testBit_succ x.val i.val
    rw [htail, ih y]
    change (x.val.testBit 0).toNat + 2 * (x.val / 2) = x.val
    rw [show (x.val.testBit 0).toNat = x.val % 2 from (Nat.mod_two_of_bodd _).symm]
    omega

lemma helper9_lt_of_high_bit (k : ℕ) (x y : Fin (2 ^ k)) (i : Fin k)
    (hx : helper9Bits k x i = false) (hy : helper9Bits k y i = true)
    (hhigh : ∀ j : Fin k, i < j → helper9Bits k x j = helper9Bits k y j) :
    x < y := by
  apply Nat.lt_of_testBit i.val hx hy
  intro j hj
  by_cases hjk : j < k
  · exact hhigh ⟨j, hjk⟩ hj
  · rw [helper9_bits_above k x j (by omega), helper9_bits_above k y j (by omega)]

lemma helper9_lt_iff_high_bit (k : ℕ) (x y : Fin (2 ^ k)) :
    x < y ↔ ∃ i : Fin k,
      helper9Bits k x i = false ∧ helper9Bits k y i = true ∧
      ∀ j : Fin k, i < j → helper9Bits k x j = helper9Bits k y j := by
  classical
  constructor
  · intro hxy
    let s : Finset (Fin k) := Finset.univ.filter fun i => helper9Bits k x i ≠ helper9Bits k y i
    have hs : s.Nonempty := by
      by_contra hn
      have he : helper9Bits k x = helper9Bits k y := by
        funext i
        by_contra hi
        exact hn ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
      have := helper9_bits_injective k he
      exact (ne_of_lt hxy) this
    let i := s.max' hs
    have hi : helper9Bits k x i ≠ helper9Bits k y i :=
      (Finset.mem_filter.mp (s.max'_mem hs)).2
    have hhigh : ∀ j : Fin k, i < j → helper9Bits k x j = helper9Bits k y j := by
      intro j hij
      by_contra hne
      have hj : j ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
      exact (not_le_of_gt hij) (s.le_max' j hj)
    refine ⟨i, ?_, ?_, hhigh⟩
    · cases hx : helper9Bits k x i with
      | false => rfl
      | true =>
        have hy : helper9Bits k y i = false := by cases hy : helper9Bits k y i <;> simp_all
        exact False.elim ((not_lt_of_gt hxy)
          (helper9_lt_of_high_bit k y x i hy hx (fun j hj => (hhigh j hj).symm)))
    · cases hy : helper9Bits k y i with
      | true => rfl
      | false =>
        have hx : helper9Bits k x i = true := by cases hx : helper9Bits k x i <;> simp_all
        exact False.elim ((not_lt_of_gt hxy)
          (helper9_lt_of_high_bit k y x i hy hx (fun j hj => (hhigh j hj).symm)))
  · rintro ⟨i, hx, hy, hhigh⟩
    exact helper9_lt_of_high_bit k x y i hx hy hhigh

end PEqualNP.Outside.L_meta_29956_aux

namespace PEqualNP.Outside.L_meta_29956_aux.Assembly

def width (r : ℕ) : ℕ := 7*r+3

def baseStates (r : ℕ) : ℕ := 2^(2^(6*width r))

def tableStates (r : ℕ) : ℕ :=
  (Finset.range (baseStates r+1)).sum (fun u =>
    u.factorial * (Nat.stirlingSecond (baseStates r+1) (u+1))^2)

def stateBudget (r : ℕ) : ℕ := 2*tableStates r*2^(tableStates r)

def Salt (r : ℕ) := Fin (2*r) → Fin (width r+1) → Bool

def Letter (r : ℕ) := Salt r × Bool × Bool × Bool × Bool

def prev (k pos d : ℕ) : ℕ := (pos+k-d % k) % k

def rot (k d x : ℕ) : ℕ := ((x <<< (d % k)) ||| (x >>> (k-d % k))) % 2^k

def chi (k x : ℕ) : ℕ :=
  (List.range k).foldl (fun (acc i : ℕ) =>
    acc ||| ((xor (x.testBit i)
      (!(x.testBit ((i+1) % k)) && x.testBit ((i+2) % k))).toNat <<< i)) 0

def run (r k : ℕ) (masks : ℕ → Fin (2^k)) (col : Bool) (key name : ℕ) : ℕ :=
  let gap : ℕ := if col then 2 else 1
  (List.range r).foldl (fun z j =>
    let mixed := z ^^^ rot k gap z ^^^ rot k (k-gap % k) z
    chi k mixed ^^^ rot k (if col then 3*(j+1)+1 else 2*j) key ^^^
      (masks (if col then r+j else j)).val) (rot k (if col then 3 else 1) key ^^^ name)

def row (r k h : ℕ) (masks : ℕ → Fin (2^k)) (a c : Fin (2^h))
    (x y : Fin (2^k)) : Bool :=
  decide (∃ key : Fin (2^k), run r k masks false key.val x.val >>> (k-h) = a.val ∧
    run r k masks true key.val y.val >>> (k-h) = c.val)

def input (r k h : ℕ) (masks : ℕ → Fin (2^k)) (a c : Fin (2^h))
    (bound : Fin (2^k)) (pos : ℕ) : Letter r :=
  let site := prev k pos (4*r)
  (fun bank off => (masks bank.val).val.testBit (prev k pos off.val),
    decide (k-h ≤ site), a.val.testBit (site-(k-h)),
    c.val.testBit (site-(k-h)), bound.val.testBit pos)

def inputWord (r k h : ℕ) (masks : ℕ → Fin (2^k)) (a c : Fin (2^h))
    (bound : Fin (2^k)) : List (Letter r) :=
  (List.range k).reverse.map (input r k h masks a c bound)

def transfer {A S : Type} [Fintype S] (weight : A → S → S → Fin 3)
    (v : S → ℕ) (letter : A) : S → ℕ :=
  fun dst => ∑ src : S, v src * (weight letter src dst).val

noncomputable def wordCounts {A S : Type} [Fintype S]
    (weight : A → S → S → Fin 3) (start : S) (word : List A) : S → ℕ := by
  classical
  exact word.foldl (transfer weight) (fun state => (decide (state = start)).toNat)

def finishCount {S : Type} [Fintype S] (finish : S → Bool) (counts : S → ℕ) : ℕ :=
  ∑ state : S, if finish state then counts state else 0

noncomputable def neighborhoodCount (r k h : ℕ) (masks : ℕ → Fin (2^k))
    (a c : Fin (2^h)) (bound : Fin (2^k)) : ℕ := by
  classical
  exact ((Finset.univ.filter (fun x : Fin (2^k) => x ≤ bound)).image (row r k h masks a c)).card

def Realization (r : ℕ) : Prop :=
  ∃ (S : Type) (fs : Fintype S) (start : S) (finish : S → Bool)
    (weight : Letter r → S → S → Fin 3),
    @Fintype.card S fs ≤ stateBudget r ∧
    ∀ (k h : ℕ), 0 < h → h ≤ k →
      ∀ (masks : ℕ → Fin (2^k)) (a c : Fin (2^h)) (bound : Fin (2^k)),
        @finishCount S fs finish
          (@wordCounts (Letter r) S fs weight start (inputWord r k h masks a c bound)) =
        neighborhoodCount r k h masks a c bound

lemma transfer_reindex {A S T : Type} [Fintype S] [Fintype T]
    (e : S ≃ T) (weight : A → S → S → Fin 3) (v : S → ℕ) (letter : A) :
    transfer (fun a i j => weight a (e.symm i) (e.symm j))
      (fun i => v (e.symm i)) letter =
      fun i => transfer weight v letter (e.symm i) := by
  funext dst
  exact e.symm.sum_comp (fun src => v src * (weight letter src (e.symm dst)).val)

lemma fold_transfer_reindex {A S T : Type} [Fintype S] [Fintype T]
    (e : S ≃ T) (weight : A → S → S → Fin 3) (v : S → ℕ) (word : List A) :
    word.foldl (transfer (fun a i j => weight a (e.symm i) (e.symm j)))
      (fun i => v (e.symm i)) =
      fun i => word.foldl (transfer weight) v (e.symm i) := by
  induction word generalizing v with
  | nil => rfl
  | cons letter word ih =>
    simp only [List.foldl_cons, transfer_reindex]
    exact ih (transfer weight v letter)

lemma counts_reindex {A S T : Type} [Fintype S] [Fintype T]
    (e : S ≃ T) (weight : A → S → S → Fin 3) (start : S) (word : List A) :
    wordCounts (fun a i j => weight a (e.symm i) (e.symm j)) (e start) word =
      fun i => wordCounts weight start word (e.symm i) := by
  classical
  unfold wordCounts
  have hinit : (fun i : T => (decide (i = e start)).toNat) =
      fun i => (decide (e.symm i = start)).toNat := by
    funext i
    simp only [Equiv.symm_apply_eq]
  rw [hinit]
  exact fold_transfer_reindex e weight (fun state => (decide (state = start)).toNat) word

lemma finish_reindex {S T : Type} [Fintype S] [Fintype T]
    (e : S ≃ T) (finish : S → Bool) (counts : S → ℕ) :
    finishCount (fun i => finish (e.symm i)) (fun i => counts (e.symm i)) =
      finishCount finish counts := by
  exact e.symm.sum_comp (fun i => if finish i then counts i else 0)

lemma assemble (realize : ∀ r, Realization r) :
∀ r : ℕ,
  let b := 7*r+3
  let N := 2^(2^(6*b))
  let P := (Finset.range (N+1)).sum (fun u =>
    u.factorial * (Nat.stirlingSecond (N+1) (u+1))^2)
  let Salt := Fin (2*r) → Fin (b+1) → Bool
  ∃ (D : ℕ) (start : Fin D) (finish : Fin D → Bool)
    (weight : Salt → Bool → Bool → Bool → Bool → Fin D → Fin D → Fin 3),
    D ≤ 2*P*2^P ∧
    ∀ (k h : ℕ), 0 < h → h ≤ k →
    ∀ (masks : ℕ → Fin (2^k)) (a c : Fin (2^h)) (bound : Fin (2^k)),
      let prev := fun (pos d : ℕ) => (pos+k-d % k) % k
      let rot := fun (d x : ℕ) => ((x <<< (d % k)) ||| (x >>> (k-d % k))) % 2^k
      let chi := fun (x : ℕ) => (List.range k).foldl (fun (acc i : ℕ) =>
        acc ||| ((xor (x.testBit i) (!(x.testBit ((i+1) % k)) && x.testBit ((i+2) % k))).toNat <<< i)) 0
      let run := fun (col : Bool) (key name : ℕ) =>
        let gap : ℕ := if col then 2 else 1
        (List.range r).foldl (fun z j =>
          let mixed := z ^^^ rot gap z ^^^ rot (k-gap % k) z
          chi mixed ^^^ rot (if col then 3*(j+1)+1 else 2*j) key ^^^
            (masks (if col then r+j else j)).val) (rot (if col then 3 else 1) key ^^^ name)
      let row := fun (x y : Fin (2^k)) =>
        decide (∃ key : Fin (2^k), run false key.val x.val >>> (k-h) = a.val ∧
          run true key.val y.val >>> (k-h) = c.val)
      let counts := (List.range k).reverse.foldl (fun (v : Fin D → ℕ) pos =>
        let site := prev pos (4*r)
        let salt : Salt := fun bank off => (masks bank.val).val.testBit (prev pos off.val)
        let M := weight salt (decide (k-h ≤ site)) (a.val.testBit (site-(k-h)))
          (c.val.testBit (site-(k-h))) (bound.val.testBit pos)
        fun dst => ∑ src : Fin D, v src * (M src dst).val)
        (fun state => (decide (state = start)).toNat)
      (∑ state : Fin D, if finish state then counts state else 0) =
        ((Finset.univ.filter (fun x : Fin (2^k) => x ≤ bound)).image row).card := by
  classical
  intro r
  dsimp only
  obtain ⟨S, fs, start, finish, weight, hdim, hcorrect⟩ := realize r
  let : Fintype S := fs
  let e : S ≃ Fin (Fintype.card S) := Fintype.equivFin S
  refine ⟨Fintype.card S, e start, (fun i => finish (e.symm i)),
    (fun salt active a c bound src dst => weight (salt, active, a, c, bound)
      (e.symm src) (e.symm dst)), hdim, ?_⟩
  intro k h hh hhk masks a c bound
  have htransport := finish_reindex e finish
    (wordCounts weight start (inputWord r k h masks a c bound))
  rw [← counts_reindex e weight start] at htransport
  have hanswer := htransport.trans (hcorrect k h hh hhk masks a c bound)
  simp only [wordCounts, inputWord, List.foldl_map] at hanswer
  convert hanswer using 1
  · unfold finishCount transfer input prev
    congr! 8
  · rfl

end PEqualNP.Outside.L_meta_29956_aux.Assembly

namespace PEqualNP.Outside.L_meta_29956_aux

lemma helper2_enum_filter_card {α : Type*} [Fintype α] (k : ℕ)
    (e : α ≃ {w : List Bool // w.length = k}) (p : List Bool → Bool) :
    ((enumBitWords k).filter p).length =
      (Finset.univ.filter (fun x : α => p (e x).val)).card := by
  classical
  let f : α → List Bool := fun x => (e x).val
  have hf : Function.Injective f := by
    intro x y h
    exact e.injective (Subtype.ext h)
  have heq : (Finset.univ.filter (fun x : α => p (f x))).image f =
      ((enumBitWords k).filter p).toFinset := by
    ext w
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      List.mem_toFinset, List.mem_filter]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(mem_enumBitWords k (f x)).mpr (e x).property, hx⟩
    · rintro ⟨hw, hp⟩
      obtain ⟨x, hx⟩ := e.surjective ⟨w, (mem_enumBitWords k w).mp hw⟩
      have hxv : f x = w := congrArg Subtype.val hx
      exact ⟨x, hxv.symm ▸ hp, hxv⟩
  calc
    ((enumBitWords k).filter p).length = ((enumBitWords k).filter p).toFinset.card :=
      (List.toFinset_card_of_nodup ((enumBitWords_nodup k).filter p)).symm
    _ = ((Finset.univ.filter (fun x : α => p (f x))).image f).card :=
      congrArg Finset.card heq.symm
    _ = (Finset.univ.filter (fun x : α => p (e x).val)).card :=
      Finset.card_image_of_injOn hf.injOn

def helper2ReverseWordEquiv (k : ℕ) :
    {w : List Bool // w.length = k} ≃ {w : List Bool // w.length = k} where
  toFun w := ⟨w.val.reverse, by simp [w.property]⟩
  invFun w := ⟨w.val.reverse, by simp [w.property]⟩
  left_inv w := Subtype.ext (List.reverse_reverse w.val)
  right_inv w := Subtype.ext (List.reverse_reverse w.val)

noncomputable def helper2MSBWordEquiv (k : ℕ) :
    Fin (2^k) ≃ {w : List Bool // w.length = k} :=
  (helper9WordEquiv k).trans (helper2ReverseWordEquiv k)

lemma helper2_enum_filter_fin_card (k : ℕ) (p : List Bool → Bool) :
    ((enumBitWords k).filter p).length =
      (Finset.univ.filter (fun x : Fin (2^k) => p (helper9Word k x).val)).card :=
  helper2_enum_filter_card k (helper9WordEquiv k) p

lemma helper2_enum_filter_msb_card (k : ℕ) (p : List Bool → Bool) :
    ((enumBitWords k).filter p).length =
      (Finset.univ.filter (fun x : Fin (2^k) => p (helper9Word k x).val.reverse)).card :=
  helper2_enum_filter_card k (helper2MSBWordEquiv k) p

lemma helper2_enum_filter_image_card {β : Type*} [DecidableEq β]
    (k : ℕ) (f : Fin (2^k) → β) (bound : Fin (2^k))
    (accept : List Bool → Bool)
    (haccept : ∀ x : Fin (2^k), accept (helper9Word k x).val.reverse = true ↔
      x ≤ bound ∧ ∀ y, y < x → f y ≠ f x) :
    ((enumBitWords k).filter accept).length =
      ((Finset.univ.filter (fun x : Fin (2^k) => x ≤ bound)).image f).card := by
  classical
  rw [helper2_enum_filter_msb_card]
  have heq : Finset.univ.filter (fun x : Fin (2^k) => accept (helper9Word k x).val.reverse) =
      Finset.univ.filter (fun x : Fin (2^k) => x ≤ bound ∧ ∀ y, y < x → f y ≠ f x) := by
    ext x
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using haccept x
  rw [heq]
  simpa only [Fin.le_def, Fin.lt_def] using pnp29956_least_representatives_card f bound

lemma helper2_enum_filter_image_card_equiv {α β : Type*}
    [Fintype α] [LinearOrder α] [DecidableEq β]
    (k : ℕ) (e : α ≃ {w : List Bool // w.length = k})
    (f : α → β) (bound : α) (accept : List Bool → Bool)
    (haccept : ∀ x : α, accept (e x).val = true ↔
      x ≤ bound ∧ ∀ y, y < x → f y ≠ f x) :
    ((enumBitWords k).filter accept).length =
      ((Finset.univ.filter (fun x : α => x ≤ bound)).image f).card := by
  classical
  rw [helper2_enum_filter_card k e]
  have heq : Finset.univ.filter (fun x : α => accept (e x).val) =
      Finset.univ.filter (fun x : α => x ≤ bound ∧ ∀ y, y < x → f y ≠ f x) := by
    ext x
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using haccept x
  rw [heq]
  exact pnp29956_least_representatives_card f bound

lemma helper2_word_val_eq_range_map (k : ℕ) (x : Fin (2^k)) :
    (helper9Word k x).val = (List.range k).map x.val.testBit := by
  apply List.ext_getElem
  · simp [helper9Word]
  · intro i hi hj
    simp [helper9Word, helper9Bits]

lemma helper2_msbWord_eq_range_map (k : ℕ) (x : Fin (2^k)) :
    (helper9Word k x).val.reverse = (List.range k).reverse.map x.val.testBit := by
  rw [helper2_word_val_eq_range_map, List.map_reverse]

lemma helper2_enum_filter_range_image_card {β : Type*} [DecidableEq β]
    (k : ℕ) (f : Fin (2^k) → β) (bound : Fin (2^k))
    (accept : List Bool → Bool)
    (haccept : ∀ x : Fin (2^k),
      accept ((List.range k).reverse.map x.val.testBit) = true ↔
        x ≤ bound ∧ ∀ y, y < x → f y ≠ f x) :
    ((enumBitWords k).filter accept).length =
      ((Finset.univ.filter (fun x : Fin (2^k) => x ≤ bound)).image f).card := by
  apply helper2_enum_filter_image_card k f bound accept
  intro x
  simpa only [helper2_msbWord_eq_range_map] using haccept x

end PEqualNP.Outside.L_meta_29956_aux

namespace PEqualNP.Outside.L_meta_29956_aux

lemma h1_prev_eq_idx {k pos : Nat} (hk : 0 < k) (hpos : pos < k) (d : Nat) :
    (pos + k - d % k) % k = idx k ((pos : Int) - (d : Int)) := by
  rw [idx_sub_mod, idx_sub_small (Nat.mod_lt d hk), idx_nat hpos]
  have hd := Nat.mod_lt d hk
  split
  · next h =>
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · next h =>
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

lemma h1_prev_testBit {k pos : Nat} (hk : 0 < k) (hpos : pos < k) (x d : Nat) :
    x.testBit ((pos + k - d % k) % k) = bits k x ((pos : Int) - (d : Int)) := by
  unfold bits
  rw [h1_prev_eq_idx hk hpos]

lemma h1_current_samples {k pos m : Nat} (hk : 0 < k) (hpos : pos < k) (x : Nat) :
    Fin.cases (x.testBit pos)
      (fun i : Fin m => x.testBit ((pos + k - (i.val + 1) % k) % k)) =
      fun i : Fin (m + 1) => bits k x ((pos : Int) - (i.val : Int)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [bits, idx_nat hpos]
  · simp only [Fin.cases_succ, Fin.val_succ]
    exact h1_prev_testBit hk hpos x (j.val + 1)

lemma h1_mask_samples {k pos r b : Nat} (hk : 0 < k) (hpos : pos < k)
    (masks : Nat → Fin (2 ^ k)) :
    (fun (bank : Fin (2 * r)) (off : Fin (b + 1)) =>
      (masks bank.val).val.testBit ((pos + k - off.val % k) % k)) =
    fun bank off => bits k (masks bank.val).val ((pos : Int) - (off.val : Int)) := by
  funext bank off
  exact h1_prev_testBit hk hpos (masks bank.val).val off.val

def h1Pack {k : Nat} (z : Fin k → Bool) : Nat :=
  (List.range k).foldl (fun acc i =>
    acc ||| ((if hi : i < k then z ⟨i, hi⟩ else false).toNat <<< i)) 0

lemma h1Pack_lt {k : Nat} (z : Fin k → Bool) : h1Pack z < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  simp [h1Pack, pack_bit, Nat.not_lt_of_ge hj]

def h1Key {k : Nat} (z : Fin k → Bool) : Fin (2 ^ k) := ⟨h1Pack z, h1Pack_lt z⟩

lemma h1Key_bit {k : Nat} (z : Fin k → Bool) (i : Fin k) :
    (h1Key z).val.testBit i.val = z i := by
  simp [h1Key, h1Pack, pack_bit, i.isLt]

lemma h1Key_bits {k : Nat} (hk : 0 < k) (z : Fin k → Bool) (t : Int) :
    bits k (h1Key z).val t = z ⟨idx k t, idx_lt hk t⟩ := by
  exact h1Key_bit z ⟨idx k t, idx_lt hk t⟩

lemma h1_exists_key_iff {k : Nat} (P : (Fin k → Bool) → Prop) :
    (∃ z : Fin k → Bool, P z) ↔
      ∃ key : Fin (2 ^ k), P (fun i => key.val.testBit i.val) := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨h1Key z, ?_⟩
    simpa only [h1Key_bit] using hz
  · rintro ⟨key, hkey⟩
    exact ⟨fun i => key.val.testBit i.val, hkey⟩

end PEqualNP.Outside.L_meta_29956_aux

namespace PEqualNP.Outside.L_meta_29956_aux

def pnp29956_machineInitial {Q : Type*} (finish : Q → Bool) :
    Bool × (Q → Q → Bool) × Set (Q → Q → Bool) :=
  (false, (fun q q' => decide (finish q = finish q')), ∅)

noncomputable def pnp29956_machineFinish {Q : Type*} (start : Q)
    (state : Bool × (Q → Q → Bool) × Set (Q → Q → Bool)) : Bool := by
  classical
  exact decide (∀ B ∈ state.2.2, B start start = false)

lemma pnp29956_machineFinish_iff {Q : Type*} (start : Q)
    (state : Bool × (Q → Q → Bool) × Set (Q → Q → Bool)) :
    pnp29956_machineFinish start state = true ↔
      ∀ B ∈ state.2.2, B start start = false := by
  classical
  simp only [pnp29956_machineFinish, decide_eq_true_eq]

end PEqualNP.Outside.L_meta_29956_aux

namespace PEqualNP.Outside.L_meta_29956_aux

abbrev pnp29956_machineState (Q : Type*) :=
  Bool × (Q → Q → Bool) × Set (Q → Q → Bool)

noncomputable def pnp29956_machineWeight {A Q : Type*} [Fintype Q]
    (delta : A → Bool → Bool → Q → Q) (letter : A × Bool)
    (src dst : pnp29956_machineState Q) : Fin 3 := by
  classical
  exact bitWeight (pnp29956_machineStep delta) letter src dst

noncomputable def pnp29956_machineCount {A Q : Type*} [Fintype Q]
    (delta : A → Bool → Bool → Q → Q) (finish : Q → Bool) (start : Q)
    (letters : List (A × Bool)) : Nat := by
  classical
  let counts := letters.foldl
    (fun v a dst => ∑ src : pnp29956_machineState Q,
      v src * (pnp29956_machineWeight delta a src dst).val)
    (fun q => (decide (q = pnp29956_machineInitial finish)).toNat)
  exact ∑ q : pnp29956_machineState Q,
    if pnp29956_machineFinish start q then counts q else 0

noncomputable def pnp29956_acceptWord {A Q : Type*}
    (delta : A → Bool → Bool → Q → Q) (finish : Q → Bool) (start : Q)
    (letters : List (A × Bool)) (word : List Bool) : Bool :=
  ((runBitWord (pnp29956_machineStep delta) letters word (pnp29956_machineInitial finish)).map
    (pnp29956_machineFinish start)).getD false

lemma pnp29956_machineCount_eq_words {A Q : Type*} [Fintype Q]
    (delta : A → Bool → Bool → Q → Q) (finish : Q → Bool) (start : Q)
    (letters : List (A × Bool)) :
    pnp29956_machineCount delta finish start letters =
      ((enumBitWords letters.length).filter
        (pnp29956_acceptWord delta finish start letters)).length := by
  classical
  exact bit_transfer_eq_words (pnp29956_machineStep delta) letters
    (pnp29956_machineInitial finish) (pnp29956_machineFinish start)

lemma pnp29956_acceptWord_bits {A Q : Type*} {k : Nat}
    (delta : A → Bool → Bool → Q → Q) (finish : Q → Bool) (start : Q)
    (symbolsNat : Nat → A) (bound x : Fin (2 ^ k)) :
    pnp29956_acceptWord delta finish start (pnp29956_machineLetters symbolsNat bound)
      (meta29956_wordBits k x.val) = true ↔
      x ≤ bound ∧ ∀ z : Fin (2 ^ k), z < x →
        pnp29956_finiteRow delta finish start (fun i : Fin k => symbolsNat i.val) z ≠
          pnp29956_finiteRow delta finish start (fun i : Fin k => symbolsNat i.val) x := by
  rw [← pnp29956_machineBitWord_accepts delta finish start symbolsNat bound x]
  unfold pnp29956_acceptWord pnp29956_machineInitial
  cases hrun : runBitWord (pnp29956_machineStep delta)
    (pnp29956_machineLetters symbolsNat bound) (meta29956_wordBits k x.val)
    (false, (fun q q' => decide (finish q = finish q')), ∅) with
  | none => simp
  | some s => simp [pnp29956_machineFinish_iff]

lemma pnp29956_machineCount_eq_rowImage {A Q : Type*} [Fintype Q] {k : Nat}
    (delta : A → Bool → Bool → Q → Q) (finish : Q → Bool) (start : Q)
    (symbolsNat : Nat → A) (bound : Fin (2 ^ k)) :
    pnp29956_machineCount delta finish start (pnp29956_machineLetters symbolsNat bound) =
      ((Finset.univ.filter (fun x : Fin (2 ^ k) => x ≤ bound)).image
        (pnp29956_finiteRow delta finish start (fun i : Fin k => symbolsNat i.val))).card := by
  classical
  rw [pnp29956_machineCount_eq_words]
  have hlen : (pnp29956_machineLetters symbolsNat bound).length = k := by
    simp [pnp29956_machineLetters]
  rw [hlen]
  apply helper2_enum_filter_image_card_equiv k
    ((meta29956_bitWordsEquiv k).symm.trans (helper2ReverseWordEquiv k))
  intro x
  change pnp29956_acceptWord delta finish start (pnp29956_machineLetters symbolsNat bound)
    (meta29956_lowBits k x.val).reverse = true ↔ _
  rw [meta29956_lowBits_reverse]
  exact pnp29956_acceptWord_bits delta finish start symbolsNat bound x

end PEqualNP.Outside.L_meta_29956_aux

namespace PEqualNP.Outside.L_meta_29956_aux.Assembly

def External (r : ℕ) := Salt r × Bool × Bool × Bool

def inputData (r k h : ℕ) (masks : ℕ → Fin (2^k)) (a c : Fin (2^h))
    (pos : ℕ) : External r :=
  let site := prev k pos (4*r)
  (fun bank off => (masks bank.val).val.testBit (prev k pos off.val),
    decide (k-h ≤ site), a.val.testBit (site-(k-h)), c.val.testBit (site-(k-h)))

def splitLetter {r : ℕ} (a : Letter r) : External r × Bool :=
  ((a.1, a.2.1, a.2.2.1, a.2.2.2.1), a.2.2.2.2)

lemma inputWord_split (r k h : ℕ) (masks : ℕ → Fin (2^k)) (a c : Fin (2^h))
    (bound : Fin (2^k)) :
    (inputWord r k h masks a c bound).map splitLetter =
      (List.ofFn (fun i : Fin k => (inputData r k h masks a c i.val,
        bound.val.testBit i.val))).reverse := by
  unfold inputWord
  rw [List.map_map, List.map_reverse]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [input, splitLetter, inputData]

lemma wordCounts_map {A B S : Type} [Fintype S]
    (f : A → B) (weight : B → S → S → Fin 3) (start : S) (word : List A) :
    wordCounts (fun a => weight (f a)) start word =
      wordCounts weight start (word.map f) := by
  classical
  simp only [wordCounts, List.foldl_map]
  rfl

lemma paired_count_to_realization (r : ℕ)
    (S : Type) [Fintype S] (start : S) (finish : S → Bool)
    (weight : (External r × Bool) → S → S → Fin 3)
    (hdim : Fintype.card S ≤ stateBudget r)
    (hcorrect : ∀ (k h : ℕ), 0 < h → h ≤ k →
      ∀ (masks : ℕ → Fin (2^k)) (a c : Fin (2^h)) (bound : Fin (2^k)),
        finishCount finish (wordCounts weight start
          (List.ofFn (fun i : Fin k => (inputData r k h masks a c i.val,
            bound.val.testBit i.val))).reverse) =
          neighborhoodCount r k h masks a c bound) : Realization r := by
  refine ⟨S, inferInstance, start, finish, fun a => weight (splitLetter a), hdim, ?_⟩
  intro k h hh hhk masks a c bound
  rw [wordCounts_map, inputWord_split]
  exact hcorrect k h hh hhk masks a c bound

end PEqualNP.Outside.L_meta_29956_aux.Assembly

namespace PEqualNP.Outside.L_meta_29956_aux

def h4GraphInput (r k h : ℕ) (masks : ℕ → Fin (2 ^ k))
    (a c : Fin (2 ^ h)) (pos : Fin k) : h4External r :=
  let site := (pos.val + k - (4*r) % k) % k
  ((fun bank off => (masks bank.val).val.testBit ((pos.val + k - off.val % k) % k)),
    decide (k-h ≤ site), a.val.testBit (site-(k-h)), c.val.testBit (site-(k-h)))

lemma h4GraphDFA_word (r : ℕ) {k h : ℕ} (hk : 0 < k) (hh : h ≤ k)
    (masks : ℕ → Fin (2 ^ k)) (a c : Fin (2 ^ h)) (x y : Fin (2 ^ k)) :
    List.ofFn (fun pos => (h4GraphInput r k h masks a c pos,
      x.val.testBit pos.val, y.val.testBit pos.val)) ∈ (h4GraphDFA r).accepts ↔
      ∃ key : Fin (2 ^ k),
        wordRun k r masks false key.val x.val r >>> (k-h) = a.val ∧
        wordRun k r masks true key.val y.val r >>> (k-h) = c.val := by
  rw [h4GraphDFA_accepts r hk, h1_exists_key_iff, row_iff_physicalValid hk hh]
  apply exists_congr
  intro key
  constructor
  · intro hall pos hpos
    have hp := hall ⟨pos, hpos⟩
    simpa only [h4GraphInput, h4PhysicalHistory, physicalValid, h6SampleHistory_nat hpos] using hp
  · intro hall pos
    have hp := hall pos.val pos.isLt
    simpa only [h4GraphInput, h4PhysicalHistory, physicalValid, h6SampleHistory_nat pos.isLt] using hp

end PEqualNP.Outside.L_meta_29956_aux

namespace PEqualNP.Outside.L_meta_29956_aux.Assembly

abbrev GraphQ (r : ℕ) := Set (h4Memory r × h4Memory r)

def graphDelta (r : ℕ) (a : External r) (x y : Bool) (q : GraphQ r) : GraphQ r :=
  (h4GraphDFA r).step q (a, x, y)

noncomputable def graphFinish (r : ℕ) (q : GraphQ r) : Bool := by
  classical
  exact decide (q ∈ (h4GraphDFA r).accept)

lemma forwardRun_dfa {A Q : Type} (M : DFA (A × Bool × Bool) Q)
    (k : ℕ) (symbols : Fin k → A) (row col : Fin k → Bool) (q : Q) :
    pnp29956_forwardRun (fun a x y q => M.step q (a, x, y))
      (List.ofFn (fun i => (symbols i, row i))) (List.ofFn col) q =
        M.evalFrom q (List.ofFn (fun i => (symbols i, row i, col i))) := by
  induction k generalizing q with
  | zero => simp [pnp29956_forwardRun]
  | succ k ih =>
    simp only [List.ofFn_succ, pnp29956_forwardRun, DFA.evalFrom_cons]
    exact ih (fun i => symbols i.succ) (fun i => row i.succ) (fun i => col i.succ)
      (M.step q (symbols 0, row 0, col 0))

lemma finiteRow_graph (r k h : ℕ) (hk : 0 < k) (hh : h ≤ k)
    (masks : ℕ → Fin (2^k)) (a c : Fin (2^h)) :
    pnp29956_finiteRow (graphDelta r) (graphFinish r) (h4GraphDFA r).start
      (fun i : Fin k => inputData r k h masks a c i.val) = row r k h masks a c := by
  classical
  funext x y
  have hy : meta29956_lowBits k y.val = List.ofFn (fun i : Fin k => y.val.testBit i.val) := by
    apply List.ext_getElem
    · simp [meta29956_lowBits]
    · intro i hi hj
      simp [meta29956_lowBits]
  unfold pnp29956_finiteRow pnp29956_finiteRowWord
  rw [hy]
  change graphFinish r (pnp29956_forwardRun
    (fun a x y q => (h4GraphDFA r).step q (a,x,y))
    (List.ofFn (fun i : Fin k => (h4GraphInput r k h masks a c i, x.val.testBit i.val)))
    (List.ofFn (fun i : Fin k => y.val.testBit i.val)) (h4GraphDFA r).start) = _
  rw [forwardRun_dfa]
  apply Bool.eq_iff_iff.mpr
  change decide ((h4GraphDFA r).evalFrom (h4GraphDFA r).start
      (List.ofFn (fun i : Fin k =>
        (h4GraphInput r k h masks a c i, x.val.testBit i.val, y.val.testBit i.val)))
      ∈ (h4GraphDFA r).accept) = true ↔ row r k h masks a c x y = true
  rw [decide_eq_true_eq]
  change (List.ofFn (fun i : Fin k =>
      (h4GraphInput r k h masks a c i, x.val.testBit i.val, y.val.testBit i.val)))
      ∈ (h4GraphDFA r).accepts ↔ row r k h masks a c x y = true
  rw [h4GraphDFA_word r hk hh]
  simp only [row, decide_eq_true_eq]
  rfl

lemma machineLetters_ofFn (r k h : ℕ) (masks : ℕ → Fin (2^k)) (a c : Fin (2^h))
    (bound : Fin (2^k)) :
    pnp29956_machineLetters (inputData r k h masks a c) bound =
      (List.ofFn (fun i : Fin k => (inputData r k h masks a c i.val,
        bound.val.testBit i.val))).reverse := by
  unfold pnp29956_machineLetters
  rw [List.map_reverse]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

set_option synthInstance.maxSize 4096 in
lemma completeRealization (r : ℕ) : Realization r := by
  classical
  apply paired_count_to_realization r
    (pnp29956_machineState (GraphQ r))
    (pnp29956_machineInitial (graphFinish r))
    (pnp29956_machineFinish (h4GraphDFA r).start)
    (pnp29956_machineWeight (graphDelta r))
  · exact h7_generic_dimension_bound r (h4DetState_card r).le
  · intro k h hh hhk masks a c bound
    have hc := pnp29956_machineCount_eq_rowImage
      (graphDelta r) (graphFinish r) (h4GraphDFA r).start
      (inputData r k h masks a c) bound
    rw [finiteRow_graph r k h (by omega) hhk masks a c,
      machineLetters_ofFn] at hc
    convert hc using 1
    · unfold pnp29956_machineCount finishCount wordCounts transfer
      congr! 8
    · rfl

end PEqualNP.Outside.L_meta_29956_aux.Assembly

theorem PEqualNP.Outside.L_meta_29956 : ∀ r : ℕ,
  let b := 7*r+3
  let N := 2^(2^(6*b))
  let P := (Finset.range (N+1)).sum (fun u =>
    u.factorial * (Nat.stirlingSecond (N+1) (u+1))^2)
  let Salt := Fin (2*r) → Fin (b+1) → Bool
  ∃ (D : ℕ) (start : Fin D) (finish : Fin D → Bool)
    (weight : Salt → Bool → Bool → Bool → Bool → Fin D → Fin D → Fin 3),
    D ≤ 2*P*2^P ∧
    ∀ (k h : ℕ), 0 < h → h ≤ k →
    ∀ (masks : ℕ → Fin (2^k)) (a c : Fin (2^h)) (bound : Fin (2^k)),
      let prev := fun (pos d : ℕ) => (pos+k-d % k) % k
      let rot := fun (d x : ℕ) => ((x <<< (d % k)) ||| (x >>> (k-d % k))) % 2^k
      let chi := fun (x : ℕ) => (List.range k).foldl (fun (acc i : ℕ) =>
        acc ||| ((xor (x.testBit i) (!(x.testBit ((i+1) % k)) && x.testBit ((i+2) % k))).toNat <<< i)) 0
      let run := fun (col : Bool) (key name : ℕ) =>
        let gap : ℕ := if col then 2 else 1
        (List.range r).foldl (fun z j =>
          let mixed := z ^^^ rot gap z ^^^ rot (k-gap % k) z
          chi mixed ^^^ rot (if col then 3*(j+1)+1 else 2*j) key ^^^
            (masks (if col then r+j else j)).val) (rot (if col then 3 else 1) key ^^^ name)
      let row := fun (x y : Fin (2^k)) =>
        decide (∃ key : Fin (2^k), run false key.val x.val >>> (k-h) = a.val ∧
          run true key.val y.val >>> (k-h) = c.val)
      let counts := (List.range k).reverse.foldl (fun (v : Fin D → ℕ) pos =>
        let site := prev pos (4*r)
        let salt : Salt := fun bank off => (masks bank.val).val.testBit (prev pos off.val)
        let M := weight salt (decide (k-h ≤ site)) (a.val.testBit (site-(k-h)))
          (c.val.testBit (site-(k-h))) (bound.val.testBit pos)
        fun dst => ∑ src : Fin D, v src * (M src dst).val)
        (fun state => (decide (state = start)).toNat)
      (∑ state : Fin D, if finish state then counts state else 0) =
        ((Finset.univ.filter (fun x : Fin (2^k) => x ≤ bound)).image row).card := by
  exact PEqualNP.Outside.L_meta_29956_aux.Assembly.assemble
    PEqualNP.Outside.L_meta_29956_aux.Assembly.completeRealization
