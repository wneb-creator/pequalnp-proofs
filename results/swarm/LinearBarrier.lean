import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2590_aux.LinearBarrier

def combine (t a b : Bool) : Bool := if t then a && b else a || b

lemma combine_true (a b : Bool) : combine true a b = (a && b) := rfl

lemma combine_false (a b : Bool) : combine false a b = (a || b) := rfl

def linear {n : ℕ} {α : Type} (input : Fin n → α → Bool)
    (s : Finset (Fin n)) (r : α) : Bool := decide (∃ v ∈ s, input v r = true)

lemma linear_union {n : ℕ} {α : Type} (input : Fin n → α → Bool)
    (s t : Finset (Fin n)) (r : α) :
    linear input (s ∪ t) r = (linear input s r || linear input t r) := by
  apply Bool.eq_iff_iff.mpr
  simp [linear, or_and_right, exists_or]

lemma linear_on_nonempty {n m d : ℕ} {α : Type}
    (input : Fin d → α → Bool) (value : α → ℕ → Bool)
    (label : ℕ → Finset (Fin d)) (left right : ℕ → ℕ) (tag : ℕ → Bool)
    (hpast : ∀ j < m, left j < n + j ∧ right j < n + j)
    (hbase : ∀ w < n, ∀ r, value r w = linear input (label w) r)
    (hvalue : ∀ j < m, ∀ r, value r (n + j) =
      combine (tag j) (value r (left j)) (value r (right j)))
    (hand : ∀ j < m, tag j = true → label (n + j) = ∅)
    (hor : ∀ j < m, tag j = false →
      (label (left j)).Nonempty ∧ (label (right j)).Nonempty ∧
      label (n + j) = label (left j) ∪ label (right j)) :
    ∀ w < n + m, (label w).Nonempty →
      ∀ r, value r w = linear input (label w) r := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hn r
    by_cases hinput : w < n
    · exact hbase w hinput r
    · let j := w - n
      have hj : j < m := by omega
      have hwj : w = n + j := by omega
      rw [hwj] at hn ⊢
      cases ht : tag j with
      | true =>
        rw [hand j hj ht] at hn
        exact (Finset.not_nonempty_empty hn).elim
      | false =>
        obtain ⟨ha, hb, hl⟩ := hor j hj ht
        obtain ⟨hleft, hright⟩ := hpast j hj
        rw [hvalue j hj r, ht, combine_false,
          ih (left j) (by omega) (by omega) ha r,
          ih (right j) (by omega) (by omega) hb r, hl, linear_union]

lemma positive_rows_force_all {n m d : ℕ} {α : Type}
    (positive : α → Prop) (input : Fin d → α → Bool)
    (value : α → ℕ → Bool) (label : ℕ → Finset (Fin d))
    (left right : ℕ → ℕ) (tag : ℕ → Bool)
    (hpast : ∀ j < m, left j < n + j ∧ right j < n + j)
    (hbase : ∀ w < n, ∀ r, value r w = linear input (label w) r)
    (hvalue : ∀ j < m, ∀ r, value r (n + j) =
      combine (tag j) (value r (left j)) (value r (right j)))
    (hand : ∀ j < m, tag j = true → label (n + j) = ∅)
    (hor : ∀ j < m, tag j = false →
      (label (left j)).Nonempty ∧ (label (right j)).Nonempty ∧
      label (n + j) = label (left j) ∪ label (right j))
    (hlabels : ∀ w < n + m,
      (∀ r, positive r → linear input (label w) r = true) →
      ∀ r, linear input (label w) r = true) :
    ∀ w < n + m, (∀ r, positive r → value r w = true) →
      ∀ r, value r w = true := by
  have hlinear := linear_on_nonempty input value label left right tag
    hpast hbase hvalue hand hor
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hp r
    by_cases hinput : w < n
    · rw [hbase w hinput r]
      exact hlabels w hw (fun q hq => by rw [← hbase w hinput q]; exact hp q hq) r
    · let j := w - n
      have hj : j < m := by omega
      have hwj : w = n + j := by omega
      cases ht : tag j with
      | true =>
        have hp' : ∀ q, positive q →
            value q (left j) = true ∧ value q (right j) = true := by
          intro q hq
          have hh := hp q hq
          rw [hwj, hvalue j hj q, ht, combine_true, Bool.and_eq_true] at hh
          exact hh
        have ha := ih (left j) (by have := (hpast j hj).1; omega)
          (by have := (hpast j hj).1; omega) (fun q hq => (hp' q hq).1) r
        have hb := ih (right j) (by have := (hpast j hj).2; omega)
          (by have := (hpast j hj).2; omega) (fun q hq => (hp' q hq).2) r
        rw [hwj, hvalue j hj r, ht, combine_true, ha, hb]
        rfl
      | false =>
        obtain ⟨ha, hb, hl⟩ := hor j hj ht
        have hn : (label w).Nonempty := by
          rw [hwj, hl]
          exact ha.mono Finset.subset_union_left
        rw [hlinear w hw hn r]
        exact hlabels w hw (fun q hq => by rw [← hlinear w hw hn q]; exact hp q hq) r

def sevenInput (v : Fin 6) (r : Fin 7) : Bool :=
  (([3, 20, 40, 14, 37, 25, 50] : List ℕ).getD r.val 0).testBit v.val

def mask (k : ℕ) : Finset (Fin 6) := Finset.univ.filter (fun v => k.testBit v.val)

lemma seven_linear_barrier : ∀ s : Finset (Fin 6),
    s.card ≤ 2 ∨ s ∈ ({mask 14, mask 37, mask 25, mask 50} : Finset (Finset (Fin 6))) →
    (∀ r : Fin 7, r.val < 3 → linear sevenInput s r = true) →
    ∀ r : Fin 7, linear sevenInput s r = true := by
  decide +kernel

lemma seven_target_impossible {n m d : ℕ}
    (input : Fin d → Fin 7 → Bool) (value : Fin 7 → ℕ → Bool)
    (label : ℕ → Finset (Fin d)) (left right : ℕ → ℕ) (tag : ℕ → Bool)
    (hpast : ∀ j < m, left j < n + j ∧ right j < n + j)
    (hbase : ∀ w < n, ∀ r, value r w = linear input (label w) r)
    (hvalue : ∀ j < m, ∀ r, value r (n + j) =
      combine (tag j) (value r (left j)) (value r (right j)))
    (hand : ∀ j < m, tag j = true → label (n + j) = ∅)
    (hor : ∀ j < m, tag j = false →
      (label (left j)).Nonempty ∧ (label (right j)).Nonempty ∧
      label (n + j) = label (left j) ∪ label (right j))
    (hlabels : ∀ w < n + m,
      (∀ r : Fin 7, r.val < 3 → linear input (label w) r = true) →
      ∀ r, linear input (label w) r = true)
    (out : ℕ) (hout : out < n + m)
    (hcorrect : ∀ r : Fin 7, value r out = decide (r.val < 3)) : False := by
  have hh := positive_rows_force_all (fun r : Fin 7 => r.val < 3)
    input value label left right tag hpast hbase hvalue hand hor hlabels
    out hout (fun r hr => by simp [hcorrect, hr]) (3 : Fin 7)
  rw [hcorrect] at hh
  contradiction

end PEqualNP.Outside.L_meta_2590_aux.LinearBarrier
