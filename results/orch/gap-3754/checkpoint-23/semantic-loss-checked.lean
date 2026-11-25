import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3754.Loss

lemma and_false {a b : Bool} (h : (a && b) = false) : a = false ∨ b = false := by
  cases a <;> cases b <;> simp_all

lemma or_false {a b : Bool} (h : (a || b) = false) : a = false ∧ b = false := by
  cases a <;> cases b <;> simp_all

lemma loss_propagates_label
    (n N j B g : ℕ) (a b : ℕ → ℕ) (isAnd : ℕ → Bool)
    (old now : ℕ → Bool) (label : ℕ → Prop)
    (hback : ∀ k < N, a k < n+k ∧ b k < n+k)
    (hraw : ∀ w < n, old w = now w)
    (hstart : label (n+j))
    (hB : now (n+B) = true) (hg : now (n+g) = true)
    (hgate : ∀ k < N, k ≠ j → k ≠ B → k ≠ g →
      old (n+k) = (if isAnd k then old (a k) && old (b k) else old (a k) || old (b k)) ∧
      now (n+k) = (if isAnd k then now (a k) && now (b k) else now (a k) || now (b k)))
    (hor : ∀ k < N, isAnd k = false → label (a k) ∨ label (b k) → label (n+k))
    (hand : ∀ k < N, k ≠ j → k ≠ B → k ≠ g → isAnd k = true →
      (label (a k) → old (b k) = false) ∧ (label (b k) → old (a k) = false)) :
    ∀ w < n+N, old w = true → now w = false → label w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw ho hn
    by_cases hwi : w < n
    · have h := hraw w hwi
      rw [ho,hn] at h
      cases h
    obtain ⟨k,rfl⟩ : ∃ k, w = n+k := ⟨w-n,by omega⟩
    have hk : k < N := by omega
    by_cases hkj : k = j
    · simpa [hkj] using hstart
    by_cases hkB : k = B
    · subst k; rw [hB] at hn; cases hn
    by_cases hkg : k = g
    · subst k; rw [hg] at hn; cases hn
    obtain ⟨ha,hb⟩ := hback k hk
    obtain ⟨hgo,hgn⟩ := hgate k hk hkj hkB hkg
    cases hop : isAnd k
    · rw [hgo,hop] at ho
      rw [hgn,hop] at hn
      have hv : old (a k) = true ∨ old (b k) = true := by simpa using ho
      have hn' : now (a k) = false ∧ now (b k) = false := or_false (by simpa using hn)
      apply hor k hk hop
      rcases hv with hv | hv
      · exact Or.inl (ih (a k) ha (by omega) hv hn'.1)
      · exact Or.inr (ih (b k) hb (by omega) hv hn'.2)
    · rw [hgo,hop] at ho
      rw [hgn,hop] at hn
      have hv : old (a k) = true ∧ old (b k) = true := by simpa using ho
      have hn' : now (a k) = false ∨ now (b k) = false := and_false (by simpa using hn)
      obtain ⟨hga,hgb⟩ := hand k hk hkj hkB hkg hop
      exfalso
      rcases hn' with hn' | hn'
      · have h := hga (ih (a k) ha (by omega) hv.1 hn')
        rw [hv.2] at h
        cases h
      · have h := hgb (ih (b k) hb (by omega) hv.2 hn')
        rw [hv.1] at h
        cases h

end PEqualNP.Outside.L_meta_3754.Loss
