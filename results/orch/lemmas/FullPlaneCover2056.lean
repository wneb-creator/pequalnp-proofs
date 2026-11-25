import PEqualNP.Defs
import Mathlib

namespace PEqualNP.Outside.L_meta_2056_aux.FullPlaneCover

open scoped BigOperators

def Incident (p l : Fin 13) : Prop :=
  (p.val + l.val) % 13 = 0 ∨ (p.val + l.val) % 13 = 1 ∨
  (p.val + l.val) % 13 = 3 ∨ (p.val + l.val) % 13 = 9

instance (p l : Fin 13) : Decidable (Incident p l) := inferInstanceAs
  (Decidable ((p.val + l.val) % 13 = 0 ∨ (p.val + l.val) % 13 = 1 ∨
    (p.val + l.val) % 13 = 3 ∨ (p.val + l.val) % 13 = 9))

def hit (p l : Fin 13) : ℕ := if Incident p l then 1 else 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem hit_sum : ∀ p : Fin 13, ∑ l : Fin 13, hit p l = 4 := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem hit_dot : ∀ p q : Fin 13,
    ∑ l : Fin 13, hit p l * hit q l = if p = q then 4 else 1 := by decide

def degree (S : Finset (Fin 13)) (l : Fin 13) : ℕ := ∑ p ∈ S, hit p l

theorem degree_sum (S : Finset (Fin 13)) :
    ∑ l : Fin 13, degree S l = 4 * S.card := by
  unfold degree
  rw [Finset.sum_comm]
  simp [hit_sum, Nat.mul_comm]

theorem degree_square_sum (S : Finset (Fin 13)) :
    ∑ l : Fin 13, degree S l ^ 2 = S.card ^ 2 + 3 * S.card := by
  classical
  have inner (p : Fin 13) (hp : p ∈ S) :
      (∑ q ∈ S, if p = q then 4 else 1 : ℕ) = S.card + 3 := by
    calc
      _ = ∑ q ∈ S, (1 + if q = p then 3 else 0 : ℕ) := by
        apply Finset.sum_congr rfl
        intro q hq
        by_cases h : q = p
        · simp [h]
        · simp [h, Ne.symm h]
      _ = S.card + 3 := by simp [Finset.sum_add_distrib, hp]
  calc
    _ = ∑ p ∈ S, ∑ q ∈ S, ∑ l : Fin 13, hit p l * hit q l := by
      simp only [degree, pow_two, Finset.sum_mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_comm]
    _ = ∑ p ∈ S, ∑ q ∈ S, if p = q then 4 else 1 := by simp_rw [hit_dot]
    _ = ∑ p ∈ S, (S.card + 3) := Finset.sum_congr rfl inner
    _ = S.card ^ 2 + 3 * S.card := by simp; ring

theorem independent_moment_bound (S T : Finset (Fin 13)) (hS : S.Nonempty)
    (hI : ∀ p ∈ S, ∀ l ∈ T, ¬ Incident p l) :
    S.card * T.card + 3 * (S.card + T.card) ≤ 39 := by
  classical
  have hz (l : Fin 13) (hl : l ∈ T) : degree S l = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    simp [hit, hI p hp l hl]
  have hs : ∑ l ∈ Tᶜ, degree S l = 4 * S.card := by
    have h := Finset.sum_add_sum_compl T (degree S)
    have h0 : ∑ l ∈ T, degree S l = 0 := Finset.sum_eq_zero hz
    rw [h0, degree_sum] at h
    simpa using h
  have hsq : ∑ l ∈ Tᶜ, degree S l ^ 2 = S.card ^ 2 + 3 * S.card := by
    have h := Finset.sum_add_sum_compl T (fun l => degree S l ^ 2)
    have h0 : ∑ l ∈ T, degree S l ^ 2 = 0 := by
      apply Finset.sum_eq_zero
      intro l hl
      simp [hz l hl]
    rw [h0, degree_square_sum] at h
    simpa using h
  have hc : (4 * S.card) ^ 2 ≤ (S.card ^ 2 + 3 * S.card) * Tᶜ.card := by
    simpa [hs, hsq] using
      (Finset.sum_mul_sq_le_sq_mul_sq Tᶜ (degree S) (fun _ => (1 : ℕ)))
  have ht : T.card + Tᶜ.card = 13 := by
    simpa using Finset.sum_add_sum_compl T (fun _ => (1 : ℕ))
  have hp : 0 < S.card := Finset.card_pos.mpr hS
  have hm : S.card * (S.card * T.card + 3 * (S.card + T.card)) ≤ S.card * 39 := by
    have he := congrArg (fun z : ℕ => z * (S.card ^ 2 + 3 * S.card)) ht
    nlinarith
  by_contra hn
  have h40 : 40 ≤ S.card * T.card + 3 * (S.card + T.card) := by omega
  have hh := Nat.mul_le_mul_left S.card h40
  nlinarith

theorem independent_total (S T : Finset (Fin 13)) (hS : S.Nonempty) (hT : T.Nonempty)
    (hI : ∀ p ∈ S, ∀ l ∈ T, ¬ Incident p l) : S.card + T.card ≤ 10 := by
  have h := independent_moment_bound S T hS hI
  obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt (Finset.card_pos.mpr hS))
  obtain ⟨b, hb⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt (Finset.card_pos.mpr hT))
  rw [ha, hb] at h ⊢
  nlinarith [Nat.zero_le (a * b)]

theorem independent_equality (S T : Finset (Fin 13)) (hS : S.Nonempty)
    (hT : T.Nonempty) (hI : ∀ p ∈ S, ∀ l ∈ T, ¬ Incident p l)
    (he : S.card + T.card = 10) :
    (S.card = 1 ∧ T.card = 9) ∨ (S.card = 9 ∧ T.card = 1) := by
  have h := independent_moment_bound S T hS hI
  obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt (Finset.card_pos.mpr hS))
  obtain ⟨b, hb⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt (Finset.card_pos.mpr hT))
  have hab : a * b = 0 := by rw [ha, hb] at h he; nlinarith
  rcases Nat.mul_eq_zero.mp hab with h0 | h0
  · left
    constructor <;> omega
  · right
    constructor <;> omega

theorem proper_cover_size (P L : Finset (Fin 13)) (hP : P ≠ Finset.univ)
    (hL : L ≠ Finset.univ)
    (hcover : ∀ p l : Fin 13, Incident p l → p ∈ P ∨ l ∈ L) :
    16 ≤ P.card + L.card := by
  classical
  have hnP : Pᶜ.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by simpa using hP)
  have hnL : Lᶜ.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by simpa using hL)
  have hind : ∀ p ∈ Pᶜ, ∀ l ∈ Lᶜ, ¬ Incident p l := by
    intro p hp l hl hi
    have hh := hcover p l hi
    simp only [Finset.mem_compl] at hp hl
    tauto
  have hh := independent_total Pᶜ Lᶜ hnP hnL hind
  have hp : P.card + Pᶜ.card = 13 := by
    simpa using Finset.sum_add_sum_compl P (fun _ => (1 : ℕ))
  have hl : L.card + Lᶜ.card = 13 := by
    simpa using Finset.sum_add_sum_compl L (fun _ => (1 : ℕ))
  omega

end PEqualNP.Outside.L_meta_2056_aux.FullPlaneCover
