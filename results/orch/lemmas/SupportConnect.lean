import Mathlib.Data.Finset.Basic

namespace PEqualNP.Outside.L_meta_2602_aux.SupportConnect

def BitMonotone {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true

def singleton {n : ℕ} (i : Fin n) : Fin n → Bool := fun j => decide (j = i)

def Below {n : ℕ} (A : Finset (Fin n)) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x, f x = true → ∃ i ∈ A, x i = true

lemma and_below {n : ℕ} (A : Finset (Fin n)) (f g : (Fin n → Bool) → Bool)
    (hf : BitMonotone f) (hg : BitMonotone g)
    (hfg : Below A (fun x => f x && g x)) : Below A f ∨ Below A g := by
  let z : Fin n → Bool := fun i => decide (i ∉ A)
  have hzero : (f z && g z) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have := hfg z h
    simp [z] at this
  have recover (h : (Fin n → Bool) → Bool) (hm : BitMonotone h)
      (hz : h z = false) : Below A h := by
    intro x hx
    by_contra hno
    have hle : ∀ i, x i = true → z i = true := by
      intro i hi
      simp only [z, decide_eq_true_eq]
      exact fun hiA => hno ⟨i, hiA, hi⟩
    have ht := hm x z hle hx
    rw [hz] at ht
    contradiction
  cases hF : f z
  · exact Or.inl (recover f hf hF)
  · exact Or.inr (recover g hg (by simpa [hF] using hzero))

lemma support_connected (n k : ℕ) (A : Finset (Fin n))
    (F : ℕ → (Fin n → Bool) → Bool) (op : Fin k → Bool)
    (a b : Fin k → ℕ) (rep : ℕ → Fin n) (R : Fin n → Fin n → Prop)
    (hR : Equivalence R)
    (hinput : ∀ i (hi : i < n) x, F i x = x ⟨i, hi⟩)
    (hgate : ∀ j x, F (n + j.val) x =
      if op j then F (a j) x || F (b j) x else F (a j) x && F (b j) x)
    (ha : ∀ j, a j < n + j.val) (hb : ∀ j, b j < n + j.val)
    (hmono : ∀ i < n + k, BitMonotone (F i))
    (hrep : ∀ i < n + k, (∃ p, F i (singleton p) = true) → F i (singleton (rep i)) = true)
    (hjoin : ∀ j, op j = true → Below A (F (n + j.val)) →
      (∃ p, F (a j) (singleton p) = true) → (∃ p, F (b j) (singleton p) = true) →
      R (rep (a j)) (rep (b j))) :
    ∀ i < n + k, Below A (F i) →
      ∀ p q, F i (singleton p) = true → F i (singleton q) = true → R p q := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hi hbelow p q hp hq
    by_cases hin : i < n
    · rw [hinput i hin] at hp hq
      simp only [singleton, decide_eq_true_eq] at hp hq
      rw [← hp, ← hq]
      exact hR.refl _
    · let j : Fin k := ⟨i - n, by omega⟩
      have hij : n + j.val = i := by dsimp [j]; omega
      have haj : a j < i := by have := ha j; omega
      have hbj : b j < i := by have := hb j; omega
      have hak : a j < n + k := by omega
      have hbk : b j < n + k := by omega
      have hp' : F (n + j.val) (singleton p) = true := by simpa [hij] using hp
      have hq' : F (n + j.val) (singleton q) = true := by simpa [hij] using hq
      cases hop : op j
      · rw [hgate j, hop] at hp' hq'
        obtain ⟨hpa, hpb⟩ := Bool.and_eq_true_iff.mp hp'
        obtain ⟨hqa, hqb⟩ := Bool.and_eq_true_iff.mp hq'
        have hs : Below A (fun x => F (a j) x && F (b j) x) := by
          intro x hx
          apply hbelow x
          rw [← hij, hgate j, hop]
          exact hx
        rcases and_below A (F (a j)) (F (b j)) (hmono _ hak) (hmono _ hbk) hs with h | h
        · exact ih (a j) haj hak h p q hpa hqa
        · exact ih (b j) hbj hbk h p q hpb hqb
      · rw [hgate j, hop] at hp' hq'
        have hba : Below A (F (a j)) := by
          intro x hx
          apply hbelow x
          rw [← hij, hgate j, hop]
          simp [hx]
        have hbb : Below A (F (b j)) := by
          intro x hx
          apply hbelow x
          rw [← hij, hgate j, hop]
          simp [hx]
        have cross (u v : Fin n) (hu : F (a j) (singleton u) = true)
            (hv : F (b j) (singleton v) = true) : R u v := by
          have ra := hrep (a j) hak ⟨u, hu⟩
          have rb := hrep (b j) hbk ⟨v, hv⟩
          have bridge := hjoin j hop (by simpa [hij] using hbelow) ⟨u, hu⟩ ⟨v, hv⟩
          exact hR.trans (ih (a j) haj hak hba u (rep (a j)) hu ra)
            (hR.trans bridge (ih (b j) hbj hbk hbb (rep (b j)) v rb hv))
        rcases Bool.or_eq_true_iff.mp hp' with hp | hp <;>
          rcases Bool.or_eq_true_iff.mp hq' with hq | hq
        · exact ih (a j) haj hak hba p q hp hq
        · exact cross p q hp hq
        · exact hR.symm (cross q p hq hp)
        · exact ih (b j) hbj hbk hbb p q hp hq

end PEqualNP.Outside.L_meta_2602_aux.SupportConnect
