import Mathlib

namespace PEqualNP.Outside.L_meta_984.Threshold

def value6 (a b c d e f : Bool) : Nat :=
  let x := b.toNat+c.toNat
  let y := (!e).toNat+(!f).toNat
  if a then (if d then y else max x (max y (x+y-1))) else (if d then 0 else x)

def diff (a b : Nat) : Nat := a ^^^ (a &&& b)

def row {α : Type} (xs : List α) (p : α → Bool) : Nat :=
  match xs with
  | [] => 0
  | x :: xs => Nat.bit (p x) (row xs p)

def pop : Nat → Nat → Nat
  | 0, _ => 0
  | n+1, a => a.bodd.toNat + pop n a.div2

theorem pop_zero (n : Nat) : pop n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [pop] using ih

theorem row_lt {α : Type} (xs : List α) (p : α → Bool) :
    row xs p < 2 ^ xs.length := by
  induction xs with
  | nil => simp [row]
  | cons x xs ih =>
    simp only [row, List.length_cons, pow_succ]
    cases h : p x <;> simp [Nat.bit] <;> omega

theorem pop_row {α : Type} (xs : List α) (p : α → Bool) (n : Nat)
    (hn : xs.length ≤ n) : pop n (row xs p) = (xs.map (fun x => (p x).toNat)).sum := by
  induction xs generalizing n with
  | nil => simp [row, pop_zero]
  | cons x xs ih =>
    cases n with
    | zero => simp at hn
    | succ n =>
      simp only [row, pop, Nat.bodd_bit, Nat.div2_bit, List.map_cons, List.sum_cons]
      rw [ih n (by simpa using hn)]

theorem row_and {α : Type} (xs : List α) (p q : α → Bool) :
    row xs p &&& row xs q = row xs (fun x => p x && q x) := by
  induction xs with
  | nil => simp [row]
  | cons x xs ih => simp only [row, Nat.land_bit, ih]

theorem row_or {α : Type} (xs : List α) (p q : α → Bool) :
    row xs p ||| row xs q = row xs (fun x => p x || q x) := by
  induction xs with
  | nil => simp [row]
  | cons x xs ih => simp only [row, Nat.lor_bit, ih]

theorem row_diff {α : Type} (xs : List α) (p q : α → Bool) :
    diff (row xs p) (row xs q) = row xs (fun x => p x && !q x) := by
  induction xs with
  | nil => simp [row, diff]
  | cons x xs ih =>
    unfold diff at ih ⊢
    simp only [row, Nat.land_bit, Nat.xor_bit, ih]
    congr 1
    cases p x <;> cases q x <;> rfl

theorem value6_additive : ∀ a b c d e f : Bool,
    value6 a b c d e f + ((a && (b || c)) && !(d || (e && f))).toNat =
      (b && !d).toNat + (c && !d).toNat + (a && !e).toNat + (a && !f).toNat := by
  decide +kernel

def swar (x : Nat) : Nat :=
  let x := x - ((x >>> 1) &&& 21845)
  let x := (x &&& 13107) + ((x >>> 2) &&& 13107)
  let x := (x + (x >>> 4)) &&& 3855
  ((x * 257) >>> 8) &&& 31

theorem swar_blocks : ∀ hi : Fin 16, ∀ lo : Fin 256,
    swar (256 * hi.val + lo.val) = pop 12 (256 * hi.val + lo.val) := by
  decide +kernel

theorem swar_correct (x : Fin 4096) : swar x.val = pop 12 x.val := by
  have h := swar_blocks ⟨x.val / 256, by omega⟩ ⟨x.val % 256, by omega⟩
  have he : 256 * (x.val / 256) + x.val % 256 = x.val := by omega
  simpa only [he] using h

theorem swar_row {α : Type} (xs : List α) (p : α → Bool) (hn : xs.length ≤ 12) :
    swar (row xs p) = (xs.map (fun x => (p x).toNat)).sum := by
  have h : row xs p < 4096 := lt_of_lt_of_le (row_lt xs p) (by
    change 2 ^ xs.length ≤ 2 ^ 12
    exact Nat.pow_le_pow_right (by omega) hn)
  exact (swar_correct ⟨row xs p,h⟩).trans (pop_row xs p 12 hn)

def sum6 (a b c d e f : Nat) : Nat :=
  swar (diff b d) + swar (diff c d) + swar (diff a e) + swar (diff a f) -
    swar (diff (a &&& (b ||| c)) (d ||| (e &&& f)))

theorem sum6_row {α : Type} (xs : List α) (a b c d e f : α → Bool)
    (hn : xs.length ≤ 12) :
    sum6 (row xs a) (row xs b) (row xs c) (row xs d) (row xs e) (row xs f) =
      (xs.map (fun x => value6 (a x) (b x) (c x) (d x) (e x) (f x))).sum := by
  have hadd :
      (xs.map (fun x => value6 (a x) (b x) (c x) (d x) (e x) (f x))).sum +
      (xs.map (fun x => ((a x && (b x || c x)) && !(d x || (e x && f x))).toNat)).sum =
      (xs.map (fun x => (b x && !d x).toNat)).sum +
      (xs.map (fun x => (c x && !d x).toNat)).sum +
      (xs.map (fun x => (a x && !e x).toNat)).sum +
      (xs.map (fun x => (a x && !f x).toNat)).sum := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      have ih := ih (by simp only [List.length_cons] at hn; omega)
      have hv := value6_additive (a x) (b x) (c x) (d x) (e x) (f x)
      omega
  unfold sum6
  simp only [row_and, row_or, row_diff, swar_row xs _ hn]
  omega

def low6 (a b c d e f : Bool) : Bool :=
  ((b || c) && !d) || (a && !(e && f))

def mid6 (a b c d e f : Bool) : Bool :=
  ((b && c) && !d) || (a && !(e || f))

def high6 (a b c d e f : Bool) : Bool :=
  ((b && c) && !d) && (a && !(e || f))

theorem value6_tiers : ∀ a b c d e f : Bool,
    value6 a b c d e f = (low6 a b c d e f).toNat +
      (mid6 a b c d e f).toNat + (high6 a b c d e f).toNat := by
  decide +kernel

theorem tiers_order : ∀ a b c d e f : Bool,
    (high6 a b c d e f).toNat ≤ (mid6 a b c d e f).toNat ∧
    (mid6 a b c d e f).toNat ≤ (low6 a b c d e f).toNat := by
  decide +kernel

def clear1 (x : Nat) : Nat := x &&& (x-1)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem clear1_blocks : ∀ hi : Fin 16, ∀ lo : Fin 256,
    (pop 12 (256*hi.val+lo.val) = 0 ↔ 256*hi.val+lo.val = 0) ∧
    (pop 12 (256*hi.val+lo.val) ≤ 1 ↔ clear1 (256*hi.val+lo.val) = 0) ∧
    (pop 12 (256*hi.val+lo.val) ≤ 2 ↔ clear1 (clear1 (256*hi.val+lo.val)) = 0) := by
  decide +kernel

theorem clear1_correct (x : Fin 4096) :
    (pop 12 x.val = 0 ↔ x.val = 0) ∧
    (pop 12 x.val ≤ 1 ↔ clear1 x.val = 0) ∧
    (pop 12 x.val ≤ 2 ↔ clear1 (clear1 x.val) = 0) := by
  have h := clear1_blocks ⟨x.val / 256, by omega⟩ ⟨x.val % 256, by omega⟩
  have he : 256 * (x.val / 256) + x.val % 256 = x.val := by omega
  simpa only [he] using h

theorem clear1_row {α : Type} (xs : List α) (p : α → Bool) (hn : xs.length ≤ 12) :
    ((xs.map fun x => (p x).toNat).sum = 0 ↔ row xs p = 0) ∧
    ((xs.map fun x => (p x).toNat).sum ≤ 1 ↔ clear1 (row xs p) = 0) ∧
    ((xs.map fun x => (p x).toNat).sum ≤ 2 ↔ clear1 (clear1 (row xs p)) = 0) := by
  have hl : row xs p < 4096 := lt_of_lt_of_le (row_lt xs p) (by
    change 2 ^ xs.length ≤ 2 ^ 12
    exact Nat.pow_le_pow_right (by omega) hn)
  have h := clear1_correct ⟨row xs p,hl⟩
  simpa only [pop_row xs p 12 hn] using h

theorem sum_tiers {α : Type} (xs : List α) (a b c d e f : α → Bool) :
    (xs.map (fun x => value6 (a x) (b x) (c x) (d x) (e x) (f x))).sum =
      (xs.map (fun x => (low6 (a x) (b x) (c x) (d x) (e x) (f x)).toNat)).sum +
      (xs.map (fun x => (mid6 (a x) (b x) (c x) (d x) (e x) (f x)).toNat)).sum +
      (xs.map (fun x => (high6 (a x) (b x) (c x) (d x) (e x) (f x)).toNat)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons]
    have h := value6_tiers (a x) (b x) (c x) (d x) (e x) (f x)
    omega

theorem sum_tiers_order {α : Type} (xs : List α) (a b c d e f : α → Bool) :
    (xs.map (fun x => (high6 (a x) (b x) (c x) (d x) (e x) (f x)).toNat)).sum ≤
      (xs.map (fun x => (mid6 (a x) (b x) (c x) (d x) (e x) (f x)).toNat)).sum ∧
    (xs.map (fun x => (mid6 (a x) (b x) (c x) (d x) (e x) (f x)).toNat)).sum ≤
      (xs.map (fun x => (low6 (a x) (b x) (c x) (d x) (e x) (f x)).toNat)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons]
    have h := tiers_order (a x) (b x) (c x) (d x) (e x) (f x)
    omega

theorem tier_count_threshold {p q r : Nat} (hrq : r ≤ q) (hqp : q ≤ p) :
    p+q+r < 3 ↔ r=0 ∧ p≤2 ∧ (q=0 ∨ p≤1) := by omega

def lowMask (a b c d e f : Nat) : Nat := diff (b ||| c) d ||| diff a (e &&& f)
def midMask (a b c d e f : Nat) : Nat := diff (b &&& c) d ||| diff a (e ||| f)
def highMask (a b c d e f : Nat) : Nat := diff (b &&& c) d &&& diff a (e ||| f)

theorem lowMask_row {α : Type} (xs : List α) (a b c d e f : α → Bool) :
    lowMask (row xs a) (row xs b) (row xs c) (row xs d) (row xs e) (row xs f) =
      row xs (fun x => low6 (a x) (b x) (c x) (d x) (e x) (f x)) := by
  simp only [lowMask,row_and,row_or,row_diff,low6]

theorem midMask_row {α : Type} (xs : List α) (a b c d e f : α → Bool) :
    midMask (row xs a) (row xs b) (row xs c) (row xs d) (row xs e) (row xs f) =
      row xs (fun x => mid6 (a x) (b x) (c x) (d x) (e x) (f x)) := by
  simp only [midMask,row_and,row_or,row_diff,mid6]

theorem highMask_row {α : Type} (xs : List α) (a b c d e f : α → Bool) :
    highMask (row xs a) (row xs b) (row xs c) (row xs d) (row xs e) (row xs f) =
      row xs (fun x => high6 (a x) (b x) (c x) (d x) (e x) (f x)) := by
  simp only [highMask,row_and,row_or,row_diff,high6]

def threshold (a b c d e f : Nat) : Bool :=
  let x := diff (b &&& c) d
  let y := diff a (e ||| f)
  (x &&& y == 0) &&
    (let p := diff (b ||| c) d ||| diff a (e &&& f)
     let p1 := clear1 p
     (clear1 p1 == 0) && ((x ||| y == 0) || (p1 == 0)))

theorem threshold_row_iff {α : Type} (xs : List α) (a b c d e f : α → Bool)
    (hn : xs.length ≤ 12) :
    threshold (row xs a) (row xs b) (row xs c) (row xs d) (row xs e) (row xs f) = true ↔
      (xs.map (fun x => value6 (a x) (b x) (c x) (d x) (e x) (f x))).sum < 3 := by
  change (highMask (row xs a) (row xs b) (row xs c) (row xs d) (row xs e) (row xs f) == 0) &&
    ((clear1 (clear1 (lowMask (row xs a) (row xs b) (row xs c) (row xs d) (row xs e) (row xs f))) == 0) &&
      ((midMask (row xs a) (row xs b) (row xs c) (row xs d) (row xs e) (row xs f) == 0) ||
        (clear1 (lowMask (row xs a) (row xs b) (row xs c) (row xs d) (row xs e) (row xs f)) == 0))) = true ↔ _
  rw [highMask_row,lowMask_row,midMask_row]
  simp only [Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq]
  rw [← (clear1_row xs (fun x => high6 (a x) (b x) (c x) (d x) (e x) (f x)) hn).1,
    ← (clear1_row xs (fun x => low6 (a x) (b x) (c x) (d x) (e x) (f x)) hn).2.2,
    ← (clear1_row xs (fun x => mid6 (a x) (b x) (c x) (d x) (e x) (f x)) hn).1,
    ← (clear1_row xs (fun x => low6 (a x) (b x) (c x) (d x) (e x) (f x)) hn).2.1,
    sum_tiers xs a b c d e f]
  exact (tier_count_threshold (sum_tiers_order xs a b c d e f).1
    (sum_tiers_order xs a b c d e f).2).symm

theorem threshold_row {α : Type} (xs : List α) (a b c d e f : α → Bool)
    (hn : xs.length ≤ 12) :
    threshold (row xs a) (row xs b) (row xs c) (row xs d) (row xs e) (row xs f) =
      decide ((xs.map (fun x => value6 (a x) (b x) (c x) (d x) (e x) (f x))).sum < 3) := by
  apply Bool.eq_iff_iff.2
  simpa only [decide_eq_true_eq] using threshold_row_iff xs a b c d e f hn

theorem threshold_sum6 {α : Type} (xs : List α) (a b c d e f : α → Bool)
    (hn : xs.length ≤ 12) :
    threshold (row xs a) (row xs b) (row xs c) (row xs d) (row xs e) (row xs f) =
      decide (sum6 (row xs a) (row xs b) (row xs c) (row xs d) (row xs e) (row xs f) < 3) := by
  rw [sum6_row xs a b c d e f hn]
  exact threshold_row xs a b c d e f hn

end PEqualNP.Outside.L_meta_984.Threshold
