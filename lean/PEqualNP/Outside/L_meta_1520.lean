import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1520_aux

def enc (n : Fin 8192) : Fin 13 → Bool := fun v => n.val.testBit v.val

theorem enc_inj : Function.Injective enc := by
  intro n m h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 13
  · exact congrFun h ⟨i, hi⟩
  · have h1 : n.val < 2 ^ i := lt_of_lt_of_le n.isLt (by
      have : (8192 : Nat) = 2 ^ 13 := by norm_num
      rw [this]; exact Nat.pow_le_pow_right (by norm_num) (by omega))
    have h2 : m.val < 2 ^ i := lt_of_lt_of_le m.isLt (by
      have : (8192 : Nat) = 2 ^ 13 := by norm_num
      rw [this]; exact Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.testBit_eq_false_of_lt h1, Nat.testBit_eq_false_of_lt h2]

theorem enc_bij : Function.Bijective enc := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨enc_inj, ?_⟩
  simp

theorem all_iff (P : (Fin 13 → Bool) → Prop) : (∀ x, P x) ↔ ∀ n, P (enc n) := by
  constructor
  · intro h n; exact h _
  · intro h x
    obtain ⟨n, rfl⟩ := enc_bij.2 x
    exact h n

theorem card_eq (P : (Fin 13 → Bool) → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card = (Finset.univ.filter (fun n => P (enc n))).card := by
  rw [← Finset.card_map ⟨enc, enc_inj⟩]
  apply congrArg Finset.card
  ext x
  obtain ⟨n, rfl⟩ := enc_bij.2 x
  simp

def Ln (t : Fin 13) : Finset (Fin 13) := {t, t + 1, t + 3, t + 9}

def lineB (s v : Fin 13) : Bool := v == s || v == s + 1 || v == s + 3 || v == s + 9
def b4 (n : Nat) : Bool := (List.finRange 13).any fun s => (List.finRange 13).all fun v => n.testBit v.val || lineB s v
def b1 (n : Nat) : Bool := (n.testBit 0 || n.testBit 1 || n.testBit 3) || b4 n
def bq (n : Nat) : Bool := (n.testBit 0 || n.testBit 1 || n.testBit 3) || n == 7668 || n == 8180

theorem t4 : (Finset.univ.filter (fun n : Fin 8192 => b4 n.val = true)).card = 157 := by decide +kernel
theorem t2 : (Finset.univ.filter (fun n : Fin 8192 => b1 n.val = true)).card = 7170 := by decide +kernel
theorem t3 : (List.range 8192).all (fun n => b1 n == bq n) = true := by decide +kernel
theorem t3b : ∀ n : Fin 8192, b1 n.val = bq n.val := by
  intro n
  have := List.all_eq_true.1 t3 n.val (List.mem_range.2 n.isLt)
  simpa using this

theorem hA (n : Fin 8192) : (∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), enc n v = true) ↔
    (n.val.testBit 0 || n.val.testBit 1 || n.val.testBit 3) = true := by
  simp [enc, or_assoc]

theorem hB (n : Fin 8192) : (∃ s : Fin 13, ∀ v : Fin 13, enc n v = false → v ∈ Ln s) ↔ b4 n.val = true := by
  simp only [b4, List.any_eq_true, List.all_eq_true, List.mem_finRange, true_and, forall_const,
    Bool.or_eq_true, lineB, beq_iff_eq, Ln, Finset.mem_insert, Finset.mem_singleton, enc]
  apply exists_congr
  intro s
  apply forall_congr'
  intro v
  cases n.val.testBit v.val <;> simp [or_assoc]

theorem hE1 (n : Fin 8192) : enc n = (fun v : Fin 13 => decide (v ∉ Ln 0)) ↔ n.val = 7668 := by
  have h : (fun v : Fin 13 => decide (v ∉ Ln 0)) = enc ⟨7668, by norm_num⟩ := by
    funext v; revert v; decide +kernel
  rw [h, enc_inj.eq_iff, Fin.ext_iff]

theorem hE2 (n : Fin 8192) : enc n = (fun v : Fin 13 => decide (v ∉ Ln 0 ∨ v = 9)) ↔ n.val = 8180 := by
  have h : (fun v : Fin 13 => decide (v ∉ Ln 0 ∨ v = 9)) = enc ⟨8180, by norm_num⟩ := by
    funext v; revert v; decide +kernel
  rw [h, enc_inj.eq_iff, Fin.ext_iff]

theorem part1 (x : Fin 13 → Bool) : ((∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), x v = true) ∨ ∃ s : Fin 13, ∀ v : Fin 13, x v = false → v ∈ Ln s) ↔
      ((∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), x v = true) ∨ x = (fun v : Fin 13 => decide (v ∉ Ln 0)) ∨ x = (fun v : Fin 13 => decide (v ∉ Ln 0 ∨ v = 9))) := by
  revert x
  rw [all_iff]
  intro n
  rw [hA, hB, hE1, hE2]
  have h : (b1 n.val = true) ↔ (bq n.val = true) := by rw [t3b]
  simpa [b1, bq, or_assoc] using h

theorem key (y : Fin 13 → Bool) (hy : ∀ v, v ∉ Ln 0 → y v = true) :
    ((∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), y v = true) ∨ y = (fun v : Fin 13 => decide (v ∉ Ln 0)) ∨ y = (fun v : Fin 13 => decide (v ∉ Ln 0 ∨ v = 9))) := by
  by_cases h0 : y 0 = true
  · left; exact ⟨0, by decide, h0⟩
  by_cases h1 : y 1 = true
  · left; exact ⟨1, by decide, h1⟩
  by_cases h3 : y 3 = true
  · left; exact ⟨3, by decide, h3⟩
  simp only [Bool.not_eq_true] at h0 h1 h3
  right
  by_cases h9 : y 9 = true
  · right
    funext v
    by_cases hv : v ∈ Ln 0
    · simp only [Ln, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl
      all_goals (simp only [zero_add, h0, h1, h3, h9]; decide)
    · rw [hy v hv]; simp [hv]
  · left
    simp only [Bool.not_eq_true] at h9
    funext v
    by_cases hv : v ∈ Ln 0
    · simp only [Ln, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl
      all_goals (simp only [zero_add, h0, h1, h3, h9]; decide)
    · rw [hy v hv]; simp [hv]

end PEqualNP.Outside.L_meta_1520_aux

open PEqualNP.Outside.L_meta_1520_aux in
theorem PEqualNP.Outside.L_meta_1520 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    (∀ x : Fin 13 → Bool, ((∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), x v = true) ∨ ∃ s : Fin 13, ∀ v : Fin 13, x v = false → v ∈ L s) ↔
      ((∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), x v = true) ∨ x = (fun v : Fin 13 => decide (v ∉ L 0)) ∨ x = (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 9)))) ∧
    (∀ x : Fin 13 → Bool, (∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), x v = true) → x ≠ (fun v : Fin 13 => decide (v ∉ L 0)) ∧ x ≠ (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 9))) ∧
    (Finset.univ.filter (fun x : Fin 13 → Bool => ((∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), x v = true) ∨ ∃ s : Fin 13, ∀ v : Fin 13, x v = false → v ∈ L s))).card = 7170 ∧
    (Finset.univ.filter (fun x : Fin 13 → Bool => ∃ s : Fin 13, ∀ v : Fin 13, x v = false → v ∈ L s)).card = 157 ∧
    (∀ x y : Fin 13 → Bool, ((∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), x v = true) ∨ ∃ s : Fin 13, ∀ v : Fin 13, x v = false → v ∈ L s) → (∀ v : Fin 13, x v = true → y v = true) → ((∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), y v = true) ∨ ∃ s : Fin 13, ∀ v : Fin 13, y v = false → v ∈ L s)) := by
  intro L hL
  obtain rfl : L = Ln := funext hL
  refine ⟨part1, ?_, ?_, ?_, ?_⟩
  · rw [all_iff]
    intro n h
    rw [hA] at h
    constructor
    · intro he
      rw [hE1] at he
      have hn : n = ⟨7668, by norm_num⟩ := Fin.ext he
      subst hn
      exact absurd h (by decide)
    · intro he
      rw [hE2] at he
      have hn : n = ⟨8180, by norm_num⟩ := Fin.ext he
      subst hn
      exact absurd h (by decide)
  · rw [card_eq]
    simp only [hA, hB]
    rw [← t2]
    simp [b1]
  · rw [card_eq]
    simp only [hB]
    exact t4
  · intro x y hx hxy
    apply (part1 y).2
    rcases (part1 x).1 hx with h | h | h
    · left
      obtain ⟨v, hv, hxv⟩ := h
      exact ⟨v, hv, hxy v hxv⟩
    · apply key
      intro v hv
      apply hxy v
      rw [h]; simp [hv]
    · apply key
      intro v hv
      apply hxy v
      rw [h]; simp [hv]
