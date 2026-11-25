import PEqualNP.Library.LRAT.Promise

/-!
# The representing lower bound at every `n` by `m`

`rep_lower` is `rep_lower44` for `n` left and `m` right vertices; `rep_lower_mask` takes the graph
as a number whose bit `m * u + v` says whether left `u` and right `v` are joined.
-/

namespace PEqualNP.Library.LRAT.Promise

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Library.LRAT
  PEqualNP.Library.LRAT.Link PEqualNP.Represents

/-- The row with left vertex `u` and right vertex `v` on. -/
def repRow (n u v : ℕ) : ℕ := 2 ^ u + 2 ^ (n + v)

theorem repRow_testBit {n u : ℕ} (hu : u < n) (v i : ℕ) :
    (repRow n u v).testBit i = (decide (i = u) || decide (i = n + v)) := by
  have h : repRow n u v = 2 ^ (n + v) ||| 2 ^ u := by
    have := Nat.two_pow_add_eq_or_of_lt (i := n + v) (b := 2 ^ u)
      (Nat.pow_lt_pow_right (by norm_num) (by omega)) 1
    rw [mul_one] at this
    rw [← this, repRow, add_comm]
  rw [h, Nat.testBit_or, Nat.testBit_two_pow, Nat.testBit_two_pow, Bool.or_comm]
  congr 1 <;> exact decide_eq_decide.mpr eq_comm

theorem repRow_eq {n m : ℕ} (u : Fin n) (v : Fin m) :
    (List.ofFn fun i : Fin (n + m) => (repRow n u v).testBit i) = oneEach u v := by
  have hu := u.2
  apply List.ext_getElem
  · simp [oneEach]
  · intro i h1 h2
    rw [List.getElem_ofFn, repRow_testBit hu]
    simp only [oneEach, List.getElem_append, List.length_ofFn, List.getElem_ofFn]
    split_ifs with h
    · have hne : ¬ i = n + (v : ℕ) := by omega
      simp [Fin.ext_iff, hne]
    · have hne : ¬ i = (u : ℕ) := by omega
      have hiff : i = n + (v : ℕ) ↔ i - n = (v : ℕ) := by omega
      simp [Fin.ext_iff, hne, hiff]

/-- The rows of the representing problem. -/
def repRows (n m : ℕ) : List ℕ :=
  (List.finRange n).flatMap fun u => (List.finRange m).map fun v => repRow n u v

theorem rep_lower {n m : ℕ} (A : Fin n → Fin m → Bool) (s : ℕ) (g : ℕ → Bool)
    (hg : ∀ (u : Fin n) (v : Fin m), g (repRow n u v) = A u v)
    (hU : ¬ FormulaSat (enc2 (n + m) s g (repRows n m))) : ¬ RepSizeAtMost A s := by
  rintro ⟨C, hC, hs, hr⟩
  have hmem : ∀ r ∈ repRows n m, ∃ (u : Fin n) (v : Fin m), repRow n u v = r := by
    intro r hr'
    simpa [repRows] using hr'
  have hrow : ∀ r ∈ repRows n m, r < 2 ^ (n + m) := by
    intro r hr'
    obtain ⟨u, v, rfl⟩ := hmem r hr'
    refine Nat.lt_pow_two_of_testBit _ fun i hi => ?_
    rw [repRow_testBit u.2]
    have := u.2; have := v.2
    simp; omega
  have := promise_lower (n + m) s g (repRows n m) hrow hU C hC (by
    intro r hr'
    obtain ⟨u, v, rfl⟩ := hmem r hr'
    rw [repRow_eq, hr, hg])
  omega

/-- The value at a row, read off the mask `M`. -/
def gMask (n m M r : ℕ) : Bool := M.testBit (m * Nat.log2 (r % 2 ^ n) + Nat.log2 (r / 2 ^ n))

theorem gMask_row {n m : ℕ} (M : ℕ) (u : Fin n) (v : Fin m) :
    gMask n m M (repRow n u v) = M.testBit (m * u + v) := by
  have hlt : 2 ^ (u : ℕ) < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) u.2
  have h1 : repRow n u v % 2 ^ n = 2 ^ (u : ℕ) := by
    rw [repRow, pow_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  have h2 : repRow n u v / 2 ^ n = 2 ^ (v : ℕ) := by
    rw [repRow, pow_add, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hlt, zero_add]
  rw [gMask, h1, h2, Nat.log2_two_pow, Nat.log2_two_pow]

theorem rep_lower_mask (n m M s : ℕ)
    (hU : ¬ FormulaSat (enc2 (n + m) s (gMask n m M) (repRows n m))) :
    ¬ RepSizeAtMost (fun (u : Fin n) (v : Fin m) => M.testBit (m * u + v)) s :=
  rep_lower (n := n) (m := m) (fun u v => M.testBit (m * u + v)) s (gMask n m M)
    (fun u v => gMask_row (n := n) (m := m) M u v) hU

end PEqualNP.Library.LRAT.Promise
