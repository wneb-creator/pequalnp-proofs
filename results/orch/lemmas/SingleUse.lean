import Mathlib.Data.List.Count

namespace PEqualNP.Outside.L_meta_10760_aux.SingleUse

def usesBelow (reads : List ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => usesBelow reads n + reads.count n

lemma usesBelow_cons (a : ℕ) (reads : List ℕ) (n : ℕ) :
    usesBelow (a :: reads) n = usesBelow reads n + if a < n then 1 else 0 := by
  induction n with
  | zero => simp [usesBelow]
  | succ n ih =>
    simp only [usesBelow, List.count_cons, beq_iff_eq, ih]
    split_ifs <;> omega

lemma usesBelow_le_length (reads : List ℕ) (n : ℕ) :
    usesBelow reads n ≤ reads.length := by
  induction reads with
  | nil =>
    have zero : usesBelow [] n = 0 := by
      induction n with
      | zero => rfl
      | succ n ih => simp [usesBelow, ih]
    simp [zero]
  | cons a reads ih =>
    rw [usesBelow_cons, List.length_cons]
    split_ifs <;> omega

lemma usesBelow_lower (reads : List ℕ) (c n : ℕ)
    (lower : ∀ i < n, c ≤ reads.count i) : c * n ≤ usesBelow reads n := by
  induction n with
  | zero => simp [usesBelow]
  | succ n ih =>
    have before := ih (fun i hi => lower i (by omega))
    have last := lower n (by omega)
    simp only [usesBelow, Nat.mul_succ]
    omega

lemma usesBelow_interval (reads : List ℕ) (a n : ℕ)
    (lower : ∀ i < n, 1 ≤ reads.count (a + i)) :
    usesBelow reads a + n ≤ usesBelow reads (a + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have before := ih (fun i hi => lower i (by omega))
    have last := lower n (by omega)
    change usesBelow reads a + (n + 1) ≤
      usesBelow reads (a + n) + reads.count (a + n)
    omega

lemma single_input_use (reads : List ℕ)
    (slots : reads.length ≤ 25)
    (inputs : ∀ i < 7, 0 < reads.count i)
    (internal : ∀ i, 7 ≤ i → i < 19 → 0 < reads.count i) :
    ∃ i < 7, reads.count i = 1 := by
  by_cases h : ∃ i < 7, reads.count i = 1
  · exact h
  have twice : ∀ i < 7, 2 ≤ reads.count i := by
    intro i hi
    have positive := inputs i hi
    have ne : reads.count i ≠ 1 := fun eq => h ⟨i, hi, eq⟩
    omega
  have first := usesBelow_lower reads 2 7 twice
  have rest := usesBelow_interval reads 7 12 (by
    intro i hi
    have positive := internal (7 + i) (by omega) (by omega)
    omega)
  change usesBelow reads 7 + 12 ≤ usesBelow reads 19 at rest
  have upper := usesBelow_le_length reads 19
  omega

end PEqualNP.Outside.L_meta_10760_aux.SingleUse
