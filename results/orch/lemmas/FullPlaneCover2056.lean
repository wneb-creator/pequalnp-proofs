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

theorem independent_small_side (S T : Finset (Fin 13))
    (hI : ∀ p ∈ S, ∀ l ∈ T, ¬ Incident p l) : S.card ≤ 3 ∨ T.card ≤ 3 := by
  by_cases hs : S.Nonempty
  · have h := independent_moment_bound S T hs hI
    by_contra hn
    have hp : 4 ≤ S.card := by omega
    have hl : 4 ≤ T.card := by omega
    have hm := Nat.mul_le_mul hp hl
    omega
  · left
    have h0 : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [h0]

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma getD_le {a b : List Bool} (h : List.Forall₂ (· ≤ ·) a b) (i : ℕ) :
    a.getD i false ≤ b.getD i false := by
  induction h generalizing i with
  | nil => exact le_rfl
  | cons hhead htail ih =>
    cases i with
    | zero => exact hhead
    | succ i => exact ih i

lemma all_map_le (is : List ℕ) (f g : ℕ → Bool) (h : ∀ i, f i ≤ g i) :
    (is.map f).all id ≤ (is.map g).all id := by
  apply Bool.le_iff_imp.mpr
  intro hf
  change (is.map f).all id = true at hf
  rw [List.all_eq_true] at hf ⊢
  intro b hb
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
  exact Bool.le_iff_imp.mp (h i) (hf (f i) (List.mem_map.mpr ⟨i, hi, rfl⟩))

lemma any_map_le (is : List ℕ) (f g : ℕ → Bool) (h : ∀ i, f i ≤ g i) :
    (is.map f).any id ≤ (is.map g).any id := by
  apply Bool.le_iff_imp.mpr
  intro hf
  change (is.map f).any id = true at hf
  rw [List.any_eq_true] at hf ⊢
  obtain ⟨b, hb, htrue⟩ := hf
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
  exact ⟨g i, List.mem_map.mpr ⟨i, hi, rfl⟩, Bool.le_iff_imp.mp (h i) htrue⟩

lemma gate_eval_le (g : Gate) (basis : g.op = GateOp.and ∨ g.op = GateOp.or)
    {a b : List Bool} (h : List.Forall₂ (· ≤ ·) a b) :
    g.op.eval (g.inputs.map fun i => a.getD i false) ≤
      g.op.eval (g.inputs.map fun i => b.getD i false) := by
  rcases basis with hand | hor
  · rw [hand]
    exact all_map_le _ _ _ (getD_le h)
  · rw [hor]
    exact any_map_le _ _ _ (getD_le h)

lemma wires_le (C : Circuit) (mono : Monotone2 C) {a b : List Bool}
    (h : List.Forall₂ (· ≤ ·) a b) : List.Forall₂ (· ≤ ·) (C.wires a) (C.wires b) := by
  rcases C with ⟨gs, out⟩
  induction gs generalizing a b with
  | nil => exact h
  | cons g gs ih =>
    apply ih
    · exact List.rel_append h (List.Forall₂.cons
        (gate_eval_le g (mono g List.mem_cons_self).1 h) List.Forall₂.nil)
    · intro q hq
      exact mono q (List.mem_cons_of_mem g hq)

lemma eval_le (C : Circuit) (mono : Monotone2 C) {a b : List Bool}
    (h : List.Forall₂ (· ≤ ·) a b) : C.eval a ≤ C.eval b :=
  getD_le (wires_le C mono h) C.output

lemma ofFn_le {n : ℕ} {x y : Fin n → Bool} (h : x ≤ y) :
    List.Forall₂ (· ≤ ·) (List.ofFn x) (List.ofFn y) := by
  apply List.forall₂_iff_get.mpr
  constructor
  · simp
  · intro i hi hj
    simpa using h ⟨i, by simpa using hi⟩

def row (S T : Finset (Fin 13)) (i : Fin 26) : Bool :=
  if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ S)
  else decide (Fin.ofNat 13 i.val ∈ T)

def off (S : Finset (Fin 13)) : Finset (Fin 13) :=
  Finset.univ.filter fun l => ∀ p ∈ S, ¬ Incident p l

lemma incident_symm (p l : Fin 13) : Incident p l ↔ Incident l p := by
  simp [Incident, Nat.add_comm]

lemma row_left (S T : Finset (Fin 13)) (p : Fin 13) :
    row S T (Fin.castAdd 13 p) = decide (p ∈ S) := by
  have h : Fin.ofNat 13 p.val = p := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt p.isLt
  simp [row, p.isLt, h]

lemma row_right (S T : Finset (Fin 13)) (l : Fin 13) :
    row S T (Fin.natAdd 13 l) = decide (l ∈ T) := by
  have h : Fin.ofNat 13 (13 + l.val) = l := by
    apply Fin.ext
    change (13 + l.val) % 13 = l.val
    omega
  have hn : ¬ 13 + l.val < 13 := by omega
  change (if 13 + l.val < 13 then decide (Fin.ofNat 13 (13 + l.val) ∈ S)
    else decide (Fin.ofNat 13 (13 + l.val) ∈ T)) = decide (l ∈ T)
  simp only [if_neg hn, h]

def Tests (f : (Fin 26 → Bool) → Bool) : Prop :=
  (∀ p l : Fin 13, Incident p l → f (row {p} {l}) = true) ∧
    ∀ S : Finset (Fin 13), S.card ≤ 3 →
      f (row S (off S)) = false ∧ f (row (off S) S) = false

lemma tests_determine (f : (Fin 26 → Bool) → Bool) (hm : Monotone f) (ht : Tests f)
    (x : Fin 26 → Bool) :
    f x = decide (∃ p l : Fin 13, Incident p l ∧
      x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) := by
  classical
  by_cases he : ∃ p l : Fin 13, Incident p l ∧
      x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
  · simp only [he, decide_true]
    obtain ⟨p, l, hi, hp, hl⟩ := he
    have hr : row {p} {l} ≤ x := by
      intro i
      refine Fin.addCases (m := 13) (n := 13) ?_ ?_ i
      · intro q
        rw [row_left]
        apply Bool.le_iff_imp.mpr
        intro hq
        have hqp : q = p := by simpa using hq
        simpa [hqp] using hp
      · intro m
        rw [row_right]
        apply Bool.le_iff_imp.mpr
        intro hq
        have hml : m = l := by simpa using hq
        simpa [hml] using hl
    exact Bool.le_iff_imp.mp (hm hr) (ht.1 p l hi)
  · simp only [he, decide_false]
    let S : Finset (Fin 13) := Finset.univ.filter fun p => x (Fin.castAdd 13 p) = true
    let T : Finset (Fin 13) := Finset.univ.filter fun l => x (Fin.natAdd 13 l) = true
    have hn : ∀ p ∈ S, ∀ l ∈ T, ¬ Incident p l := by
      intro p hp l hl hi
      apply he
      exact ⟨p, l, hi, (Finset.mem_filter.mp hp).2, (Finset.mem_filter.mp hl).2⟩
    rcases independent_small_side S T hn with hs | htl
    · have hx : x ≤ row S (off S) := by
        intro i
        refine Fin.addCases (m := 13) (n := 13) ?_ ?_ i
        · intro p
          rw [row_left]
          apply Bool.le_iff_imp.mpr
          intro hp
          simpa [S] using hp
        · intro l
          rw [row_right]
          apply Bool.le_iff_imp.mpr
          intro hl
          apply decide_eq_true
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          intro p hp
          exact hn p hp l (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩)
      have h := hm hx
      rw [(ht.2 S hs).1] at h
      exact le_antisymm h (Bool.le_iff_imp.mpr (by intro hf; cases hf))
    · have hx : x ≤ row (off T) T := by
        intro i
        refine Fin.addCases (m := 13) (n := 13) ?_ ?_ i
        · intro p
          rw [row_left]
          apply Bool.le_iff_imp.mpr
          intro hp
          apply decide_eq_true
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          intro l hl hi
          exact hn p (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩) l hl
            ((incident_symm p l).mpr hi)
        · intro l
          rw [row_right]
          apply Bool.le_iff_imp.mpr
          intro hl
          simpa [T] using hl
      have h := hm hx
      rw [(ht.2 T htl).2] at h
      exact le_antisymm h (Bool.le_iff_imp.mpr (by intro hf; cases hf))

theorem circuit_tests_determine (C : Circuit) (hC : Monotone2 C)
    (ht : Tests (fun x => C.eval (List.ofFn x))) (x : Fin 26 → Bool) :
    C.eval (List.ofFn x) = decide (∃ p l : Fin 13, Incident p l ∧
      x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) := by
  apply tests_determine _ ?_ ht x
  intro a b hab
  exact eval_le C hC (ofFn_le hab)

theorem posted_tests_determine (C : Circuit) (hC : Monotone2 C)
    (ht :
      let I : Fin 13 → Fin 13 → Prop := fun p l => (p.val + l.val) % 13 ∈ [0, 1, 3, 9]
      let r : Finset (Fin 13) → Finset (Fin 13) → Fin 26 → Bool := fun S T i =>
        if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ S)
        else decide (Fin.ofNat 13 i.val ∈ T)
      let o : Finset (Fin 13) → Finset (Fin 13) := fun S =>
        Finset.univ.filter fun l => ∀ p ∈ S, ¬ I p l
      (∀ p l : Fin 13, I p l → C.eval (List.ofFn (r {p} {l})) = true) ∧
        ∀ S : Finset (Fin 13), S.card ≤ 3 →
          C.eval (List.ofFn (r S (o S))) = false ∧
          C.eval (List.ofFn (r (o S) S)) = false)
    (x : Fin 26 → Bool) :
    C.eval (List.ofFn x) = decide (∃ p l : Fin 13,
      (p.val + l.val) % 13 ∈ [0, 1, 3, 9] ∧
      x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) := by
  have hh : Tests (fun x => C.eval (List.ofFn x)) := by
    simpa [Tests, row, off, Incident] using ht
  simpa [Incident] using circuit_tests_determine C hC hh x

end PEqualNP.Outside.L_meta_2056_aux.FullPlaneCover
