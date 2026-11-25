import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10760

open PEqualNP.CircuitLowerBounds

def edgeFunction (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 2) || (x 1 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 5 && x 6)

def monotoneWitness : List Gate :=
  [
    ⟨GateOp.or, [0, 2]⟩,
    ⟨GateOp.or, [3, 5]⟩,
    ⟨GateOp.or, [7, 8]⟩,
    ⟨GateOp.and, [6, 9]⟩,
    ⟨GateOp.or, [1, 5]⟩,
    ⟨GateOp.and, [3, 11]⟩,
    ⟨GateOp.or, [0, 1]⟩,
    ⟨GateOp.or, [4, 5]⟩,
    ⟨GateOp.and, [13, 14]⟩,
    ⟨GateOp.or, [0, 4]⟩,
    ⟨GateOp.and, [2, 16]⟩,
    ⟨GateOp.or, [10, 12]⟩,
    ⟨GateOp.or, [15, 17]⟩,
    ⟨GateOp.or, [18, 19]⟩
  ]

lemma witness_size : monotoneWitness.length = 14 := rfl

lemma witness_allowed : ∀ g ∈ monotoneWitness,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  simp [monotoneWitness]

set_option maxHeartbeats 2000000 in
lemma witness_eval : ∀ x : Fin 7 → Bool,
    Circuit.eval ⟨monotoneWitness, 20⟩ (List.ofFn x) = edgeFunction x := by
  decide +kernel

set_option maxHeartbeats 2000000 in
lemma edgeFunction_posted : ∀ x : Fin 7 → Bool,
    decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) = edgeFunction x := by
  decide +kernel


def pairInput (i j : Fin 7) : Fin 7 → Bool :=
  fun k => decide (k = i ∨ k = j)

set_option maxHeartbeats 8000000 in
lemma positive_pair : ∀ x : Fin 7 → Bool, edgeFunction x = true →
    ∃ i j : Fin 7, i ≠ j ∧ pairInput i j ≤ x ∧ edgeFunction (pairInput i j) = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
lemma negative_pair : ∀ x : Fin 7 → Bool, edgeFunction x = false →
    ∃ i j : Fin 7, i ≠ j ∧ x ≤ pairInput i j ∧ edgeFunction (pairInput i j) = false := by
  decide +kernel

lemma pair_table_suffices (g : (Fin 7 → Bool) → Bool) (hg : Monotone g)
    (hpair : ∀ i j : Fin 7, i ≠ j → g (pairInput i j) = edgeFunction (pairInput i j)) :
    ∀ x : Fin 7 → Bool, g x = edgeFunction x := by
  intro x
  cases hx : edgeFunction x with
  | false =>
    obtain ⟨i, j, hij, hle, hf⟩ := negative_pair x hx
    have h := hg hle
    rw [hpair i j hij, hf] at h
    exact Bool.eq_false_of_le_false h
  | true =>
    obtain ⟨i, j, hij, hle, hf⟩ := positive_pair x hx
    have h := hg hle
    rw [hpair i j hij, hf] at h
    exact Bool.eq_true_of_true_le h

lemma monotone_target_order {α β : Type*} [Preorder β]
    (target : α → Bool) (F : β → Bool) (hF : Monotone F)
    (u v : α → β) (hcorrect : ∀ x, F (u x) = target x)
    (hpositive : ∀ x, target x = true → u x ≤ v x)
    (hnegative : ∀ x, target x = false → v x ≤ u x) :
    ∀ x, F (v x) = target x := by
  intro x
  cases hx : target x with
  | false =>
    have h := hF (hnegative x hx)
    rw [hcorrect x, hx] at h
    exact Bool.eq_false_of_le_false h
  | true =>
    have h := hF (hpositive x hx)
    rw [hcorrect x, hx] at h
    exact Bool.eq_true_of_true_le h

lemma replace_dominated_signal {α : Type*} {n : ℕ}
    (target : α → Bool) (F : (Fin n → Bool) → Bool) (hF : Monotone F)
    (w : α → Fin n → Bool) (i j : Fin n)
    (hcorrect : ∀ x, F (w x) = target x)
    (hpositive : ∀ x, target x = true → w x i ≤ w x j)
    (hnegative : ∀ x, target x = false → w x j ≤ w x i) :
    ∀ x, F (fun k => if k = i then w x j else w x k) = target x := by
  apply monotone_target_order target F hF w _ hcorrect
  · intro x hx k
    by_cases hk : k = i
    · simpa [hk] using hpositive x hx
    · simp [hk]
  · intro x hx k
    by_cases hk : k = i
    · simpa [hk] using hnegative x hx
    · simp [hk]

namespace NatFlip

lemma xor_pow_of_testBit_false {r i : Nat} (hr : r.testBit i = false) :
    r ^^^ 2 ^ i = r + 2 ^ i := by
  have hpow : 0 < 2 ^ i := Nat.two_pow_pos i
  have hbit : (r / 2 ^ i).testBit 0 = false := by
    simpa only [Nat.testBit_div_two_pow, Nat.zero_add] using hr
  have heven : Even (r / 2 ^ i) :=
    Nat.even_iff.mpr (Nat.mod_two_eq_zero_iff_testBit_zero.mpr hbit)
  have hdiv : (r ^^^ 2 ^ i) / 2 ^ i = r / 2 ^ i + 1 := by
    rw [Nat.xor_div_two_pow, Nat.div_self hpow, Nat.xor_one_of_even heven]
  have hmod : (r ^^^ 2 ^ i) % 2 ^ i = r % 2 ^ i := by
    rw [Nat.xor_mod_two_pow, Nat.mod_self, Nat.xor_zero]
  calc
    r ^^^ 2 ^ i = (r ^^^ 2 ^ i) % 2 ^ i + 2 ^ i * ((r ^^^ 2 ^ i) / 2 ^ i) :=
      (Nat.mod_add_div _ _).symm
    _ = r % 2 ^ i + 2 ^ i * (r / 2 ^ i + 1) := by rw [hmod, hdiv]
    _ = r + 2 ^ i := by
      rw [Nat.mul_add, Nat.mul_one, ← Nat.add_assoc, Nat.mod_add_div]

lemma xor_pow_of_testBit_true {r i : Nat} (hr : r.testBit i = true) :
    r ^^^ 2 ^ i = r - 2 ^ i := by
  have hbit : (r ^^^ 2 ^ i).testBit i = false := by
    simp [Nat.testBit_xor, hr]
  have h := xor_pow_of_testBit_false hbit
  rw [Nat.xor_xor_cancel_right] at h
  omega

lemma testBit_sub_pow {r i : Nat} (h : 2 ^ i ≤ r) :
    (r - 2 ^ i).testBit i = !r.testBit i := by
  have hflip := Nat.testBit_two_pow_add_eq (r - 2 ^ i) i
  rw [Nat.add_sub_of_le h] at hflip
  simpa using (congrArg Bool.not hflip).symm

def flipCoordinate (B mask i : Nat) : Nat :=
  ((B &&& mask) <<< (2 ^ i)) ||| ((B >>> (2 ^ i)) &&& mask)

lemma flipCoordinate_testBit (B mask i N r : Nat)
    (hmask : ∀ t < N, mask.testBit t = !t.testBit i)
    (hr : r < N) :
    (flipCoordinate B mask i).testBit r = B.testBit (r ^^^ 2 ^ i) := by
  simp only [flipCoordinate, Nat.testBit_or, Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight, Nat.testBit_and]
  have hm := hmask r hr
  cases hbit : r.testBit i with
  | false =>
    rw [xor_pow_of_testBit_false hbit]
    by_cases hle : 2 ^ i ≤ r
    · have hs : r - 2 ^ i < N := (Nat.sub_le r _).trans_lt hr
      have hms := hmask (r - 2 ^ i) hs
      have hsub := testBit_sub_pow hle
      simp [hle, hm, hms, hsub, hbit, Nat.add_comm]
    · simp [hle, hm, hbit, Nat.add_comm]
  | true =>
    rw [xor_pow_of_testBit_true hbit]
    have hle : 2 ^ i ≤ r := Nat.ge_two_pow_of_testBit hbit
    have hs : r - 2 ^ i < N := (Nat.sub_le r _).trans_lt hr
    have hms := hmask (r - 2 ^ i) hs
    have hsub := testBit_sub_pow hle
    simp [hle, hm, hms, hsub, hbit]

lemma flipCoordinate_testBit_of_mask (B mask m i r : Nat)
    (hmask : ∀ t, mask.testBit t = decide (t < 2 ^ m ∧ t.testBit i = false))
    (hr : r < 2 ^ m) :
    (flipCoordinate B mask i).testBit r = B.testBit (r ^^^ 2 ^ i) := by
  apply flipCoordinate_testBit B mask i (2 ^ m) r ?_ hr
  intro t ht
  simp [hmask, ht]

end NatFlip

end PEqualNP.Outside.L_meta_10760
