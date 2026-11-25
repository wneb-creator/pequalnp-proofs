import PEqualNP.Library.LRAT.Link

/-!
# The link with a lexicographic order of adjacent independent gates

`enc2 n s g rows = enc n s g rows ++ fLex n s`. The new family `fLex` says: if gate `j` is not
padding and gate `j + 1` reads neither of its sources from wire `n + j`, then the triple
`(first source, second source, operation)` of gate `j` is lexicographically below that of gate
`j + 1` (with both operations AND or OR, the last case is AND before OR).

Justification (`exists_nf2`): among valid models take one of least `meas2`, where
`meas2 = B ^ s * muf (ind) + word`, `word` the base-`B` word of the gate keys
`key j = s1 j * 3 (n + s + 1) + s2 j * 3 + op j` (`B = 3 (n + s + 1) ^ 2` bounds every key). The
moves of `Link` lower it (moving a gate to the front lowers `muf`, swapping the sources of a gate
lowers its key), and so does the new move `xsw`: two adjacent gates, the later one not reading
the earlier, exchanged, later readers renamed by the transposition of their wires. Two adjacent
independent gates with equal keys are impossible: the later one is a copy of the earlier.

`link2` and `lower_of_unsat2` are `link` and `lower_of_unsat` for `enc2`: every clause of `enc2`
is covered by the satisfiability theorem `enc2_sat`.
-/

namespace PEqualNP.Library.LRAT.Link

open PEqualNP.Library.LRAT

/-! ## Words in base `B` -/

/-- The base-`B` word of `a 0, ..., a (m - 1)`, most significant first. -/
def lexWord (B : ℕ) (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => lexWord B a m * B + a m

theorem lexWord_lt {B : ℕ} {a : ℕ → ℕ} : ∀ m, (∀ i < m, a i < B) → lexWord B a m < B ^ m
  | 0, _ => by simp [lexWord]
  | m + 1, h => by
    have ih := lexWord_lt m (fun i hi => h i (by omega))
    have hm := h m (by omega)
    have h2 : (lexWord B a m + 1) * B ≤ B ^ m * B := Nat.mul_le_mul_right _ ih
    rw [Nat.add_mul, Nat.one_mul] at h2
    simp only [lexWord, pow_succ]
    omega

theorem lexWord_congr {B : ℕ} {a b : ℕ → ℕ} :
    ∀ m, (∀ i < m, a i = b i) → lexWord B a m = lexWord B b m
  | 0, _ => rfl
  | m + 1, h => by
    simp only [lexWord, lexWord_congr m (fun i hi => h i (by omega)), h m (by omega)]

theorem lexWord_lt_of {B : ℕ} {a b : ℕ → ℕ} {j : ℕ} (hab : ∀ i < j, a i = b i) (hj : b j < a j) :
    ∀ m, j < m → (∀ i < m, b i < B) → lexWord B b m < lexWord B a m
  | 0, h, _ => by omega
  | m + 1, hjm, hb => by
    by_cases h : m = j
    · subst h
      simp only [lexWord, lexWord_congr m hab]
      omega
    · have ih := lexWord_lt_of hab hj m (by omega) (fun i hi => hb i (by omega))
      have hm := hb m (by omega)
      have h2 : (lexWord B b m + 1) * B ≤ lexWord B a m * B := Nat.mul_le_mul_right _ ih
      rw [Nat.add_mul, Nat.one_mul] at h2
      simp only [lexWord]
      omega

/-! ## Keys and the measure -/

/-- The key of gate `j`: its triple `(s1, s2, op)` read as one number. -/
def lexKey (n s : ℕ) (M : Model) (j : ℕ) : ℕ := M.s1 j * (3 * (n + s + 1)) + M.s2 j * 3 + M.op j

/-- The base: every key of a valid model is below it. -/
def lexB (n s : ℕ) : ℕ := 3 * (n + s + 1) * (n + s + 1)

/-- Comparing keys lexicographically. -/
theorem lex3 (K x1 y1 z1 x2 y2 z2 : ℕ) (hy : y1 * 3 + z1 < K) (hz : z1 < 3)
    (h : x1 < x2 ∨ (x1 = x2 ∧ (y1 < y2 ∨ (y1 = y2 ∧ z1 < z2)))) :
    x1 * K + y1 * 3 + z1 < x2 * K + y2 * 3 + z2 := by
  rcases h with h | ⟨rfl, h | ⟨rfl, h⟩⟩
  · have : (x1 + 1) * K ≤ x2 * K := Nat.mul_le_mul_right _ h
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  · omega
  · omega

section keys
variable {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model}

theorem lexKey_lt (hv : Valid n s g R M) {j : ℕ} (hj : j < s) : lexKey n s M j < lexB n s := by
  have h1 := hv.s1_le j hj
  have h2 := hv.s2_le j hj
  have h3 := hv.op_lt j hj
  have : M.s1 j * (3 * (n + s + 1)) ≤ (n + s) * (3 * (n + s + 1)) :=
    Nat.mul_le_mul_right _ (by omega)
  have e : (n + s) * (3 * (n + s + 1)) + 3 * (n + s + 1) = 3 * (n + s + 1) * (n + s + 1) := by
    ring
  unfold lexKey lexB
  omega

/-- The measure. -/
def meas2 (n s : ℕ) (M : Model) : ℕ :=
  lexB n s ^ s * muf s (ind n M) + lexWord (lexB n s) (lexKey n s M) s

theorem lexWord_lt_pow (hv : Valid n s g R M) :
    lexWord (lexB n s) (lexKey n s M) s < lexB n s ^ s :=
  lexWord_lt s fun _ hi => lexKey_lt hv hi

end keys

theorem meas2_mv {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {d t : ℕ}
    (hv : Valid n s g R M) (hv' : Valid n s g R (mv n s M d t)) (hd : d < s)
    (hpos : ¬ M.pad n d ∨ ∃ i < d, ¬ M.pad n i) : meas2 n s (mv n s M d t) < meas2 n s M := by
  have hlt : muf s (ind n (mv n s M d t)) < muf s (ind n M) := by
    apply muf_lt s (ind n M) (ind n (mv n s M d t)) d hd
    · simp [ind, pad_mv0]
    · intro i hi; simp only [ind, pad_mv_shift hv hi hd]
    · intro j hj _
      unfold ind
      by_cases h1 : (mv n s M d t).pad n j
      · simp [h1]
      · have h2 : ¬ M.pad n j := fun h => h1 (pad_mv_later hj h)
        simp [h1, h2]
    · rcases hpos with h | ⟨i, hi, h⟩
      · left; simp [ind, h]
      · right; exact ⟨i, hi, by simp [ind, h]⟩
  have b1 := lexWord_lt_pow hv'
  have : lexB n s ^ s * muf s (ind n (mv n s M d t)) + lexB n s ^ s ≤
      lexB n s ^ s * muf s (ind n M) := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
  unfold meas2
  omega

theorem meas2_sw {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {j : ℕ}
    (hv : Valid n s g R M) (hj : j < s) (hlt : M.s2 j < M.s1 j) :
    meas2 n s (sw M j) < meas2 n s M := by
  have hind : ind n (sw M j) = ind n M := by funext i; simp [ind, pad_sw]
  unfold meas2
  rw [hind]
  have hk : lexKey n s (sw M j) j < lexKey n s M j := by
    have h1 := hv.s1_le j hj
    have : (M.s2 j + 1) * (3 * (n + s + 1)) ≤ M.s1 j * (3 * (n + s + 1)) :=
      Nat.mul_le_mul_right _ hlt
    rw [Nat.add_mul, Nat.one_mul] at this
    simp only [lexKey, sw, if_pos rfl, ↓reduceIte]
    omega
  have := lexWord_lt_of (B := lexB n s) (a := lexKey n s M) (b := lexKey n s (sw M j)) (j := j)
    (fun i hi => by simp [lexKey, sw, show i ≠ j by omega]) hk s hj
    (fun i hi => lexKey_lt (valid_sw hv j) hi)
  omega

/-! ## Exchanging two adjacent independent gates -/

/-- The transposition of wires `n + j` and `n + j + 1`. -/
def tsw (n j k : ℕ) : ℕ := if k = n + j then n + j + 1 else if k = n + j + 1 then n + j else k

/-- Gates `j` and `j + 1` exchanged; later readers and the output renamed by `tsw`. -/
def xsw (n : ℕ) (M : Model) (j : ℕ) : Model where
  op i := if i = j then M.op (j + 1) else if i = j + 1 then M.op j else M.op i
  s1 i := if i = j then M.s1 (j + 1) else if i = j + 1 then M.s1 j
    else if j + 1 < i then tsw n j (M.s1 i) else M.s1 i
  s2 i := if i = j then M.s2 (j + 1) else if i = j + 1 then M.s2 j
    else if j + 1 < i then tsw n j (M.s2 i) else M.s2 i
  so := tsw n j M.so
  w i r := if i = j then M.w (j + 1) r else if i = j + 1 then M.w j r else M.w i r

section xsw
variable {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {j : ℕ}

theorem sv_xsw_low {i i' k r : ℕ} (hk : k < n + j) (hi : j ≤ i) (hi' : j ≤ i') :
    (xsw n M j).sv n i k r = M.sv n i' k r := by
  unfold Model.sv
  by_cases h6 : k < n
  · simp [h6]
  · simp only [if_neg h6, if_pos (show k < n + i by omega), if_pos (show k < n + i' by omega),
      xsw, if_neg (show k - n ≠ j by omega), if_neg (show k - n ≠ j + 1 by omega)]

theorem sv_xsw_early {i k r : ℕ} (hi : i < j) : (xsw n M j).sv n i k r = M.sv n i k r := by
  unfold Model.sv
  by_cases h6 : k < n
  · simp [h6]
  · by_cases h7 : k < n + i
    · simp only [if_neg h6, if_pos h7, xsw, if_neg (show k - n ≠ j by omega),
        if_neg (show k - n ≠ j + 1 by omega)]
    · simp only [if_neg h6, if_neg h7]

theorem sv_xsw_late {i k r : ℕ} (hi : j + 1 < i) :
    (xsw n M j).sv n i (tsw n j k) r = M.sv n i k r := by
  unfold tsw
  by_cases h1 : k = n + j
  · subst h1
    simp only [if_pos rfl, ↓reduceIte]
    unfold Model.sv
    simp only [if_neg (show ¬ n + j + 1 < n by omega), if_pos (show n + j + 1 < n + i by omega),
      if_neg (show ¬ n + j < n by omega), if_pos (show n + j < n + i by omega), xsw,
      show n + j + 1 - n = j + 1 by omega, show n + j - n = j by omega,
      if_neg (show j + 1 ≠ j by omega), if_pos rfl, ↓reduceIte]
  · by_cases h2 : k = n + j + 1
    · subst h2
      simp only [if_neg h1, if_pos rfl, ↓reduceIte]
      unfold Model.sv
      simp only [if_neg (show ¬ n + j + 1 < n by omega), if_pos (show n + j + 1 < n + i by omega),
        if_neg (show ¬ n + j < n by omega), if_pos (show n + j < n + i by omega), xsw,
        show n + j + 1 - n = j + 1 by omega, show n + j - n = j by omega, if_pos rfl, ↓reduceIte]
    · simp only [if_neg h1, if_neg h2]
      unfold Model.sv
      by_cases h6 : k < n
      · simp [h6]
      · by_cases h7 : k < n + i
        · simp only [if_neg h6, if_pos h7, xsw, if_neg (show k - n ≠ j by omega),
            if_neg (show k - n ≠ j + 1 by omega)]
        · simp only [if_neg h6, if_neg h7]

theorem tsw_le {i k : ℕ} (hi : j + 1 ≤ i) (hk : k ≤ n + i) : tsw n j k ≤ n + i := by
  unfold tsw; split_ifs <;> omega

theorem tsw_eq_iff {i k : ℕ} (hi : j + 1 < i) : tsw n j k = n + i ↔ k = n + i := by
  unfold tsw; split_ifs <;> omega

variable (hv : Valid n s g R M) (hj : j + 1 < s) (h1 : M.s1 j < n + j) (h2 : M.s2 j < n + j)
  (h3 : M.s1 (j + 1) < n + j) (h4 : M.s2 (j + 1) < n + j)
include hv hj h1 h2 h3 h4

theorem valid_xsw : Valid n s g R (xsw n M j) where
  op_lt i hi := by
    simp only [xsw]; split_ifs
    · exact hv.op_lt _ hj
    · exact hv.op_lt _ (by omega)
    · exact hv.op_lt _ hi
  s1_le i hi := by
    simp only [xsw]; split_ifs with a b c
    · omega
    · omega
    · exact tsw_le (by omega) (hv.s1_le i hi)
    · exact hv.s1_le i hi
  s2_le i hi := by
    simp only [xsw]; split_ifs with a b c
    · omega
    · omega
    · exact tsw_le (by omega) (hv.s2_le i hi)
    · exact hv.s2_le i hi
  so_le := tsw_le (by omega) hv.so_le
  w_eq i hi r hr := by
    by_cases a : i = j
    · subst a
      have e1 : (xsw n M i).s1 i = M.s1 (i + 1) := by simp [xsw]
      have e2 : (xsw n M i).s2 i = M.s2 (i + 1) := by simp [xsw]
      have e3 : (xsw n M i).op i = M.op (i + 1) := by simp [xsw]
      have e4 : (xsw n M i).w i r = M.w (i + 1) r := by simp [xsw]
      rw [e1, e2, e3, e4, sv_xsw_low h3 le_rfl (Nat.le_succ i),
        sv_xsw_low h4 le_rfl (Nat.le_succ i)]
      exact hv.w_eq (i + 1) hj r hr
    · by_cases b : i = j + 1
      · subst b
        have e1 : (xsw n M j).s1 (j + 1) = M.s1 j := by simp [xsw]
        have e2 : (xsw n M j).s2 (j + 1) = M.s2 j := by simp [xsw]
        have e3 : (xsw n M j).op (j + 1) = M.op j := by simp [xsw]
        have e4 : (xsw n M j).w (j + 1) r = M.w j r := by simp [xsw]
        rw [e1, e2, e3, e4, sv_xsw_low h1 (Nat.le_succ j) le_rfl,
          sv_xsw_low h2 (Nat.le_succ j) le_rfl]
        exact hv.w_eq j (by omega) r hr
      · by_cases c : j + 1 < i
        · have e1 : (xsw n M j).s1 i = tsw n j (M.s1 i) := by simp [xsw, a, b, c]
          have e2 : (xsw n M j).s2 i = tsw n j (M.s2 i) := by simp [xsw, a, b, c]
          have e3 : (xsw n M j).op i = M.op i := by simp [xsw, a, b]
          have e4 : (xsw n M j).w i r = M.w i r := by simp [xsw, a, b]
          rw [e1, e2, e3, e4, sv_xsw_late c, sv_xsw_late c]
          exact hv.w_eq i hi r hr
        · have e1 : (xsw n M j).s1 i = M.s1 i := by simp [xsw, a, b, c]
          have e2 : (xsw n M j).s2 i = M.s2 i := by simp [xsw, a, b, c]
          have e3 : (xsw n M j).op i = M.op i := by simp [xsw, a, b]
          have e4 : (xsw n M j).w i r = M.w i r := by simp [xsw, a, b]
          rw [e1, e2, e3, e4, sv_xsw_early (by omega), sv_xsw_early (by omega)]
          exact hv.w_eq i hi r hr
  out_eq r hr := by
    have e : (xsw n M j).so = tsw n j M.so := rfl
    rw [e, sv_xsw_late hj]
    exact hv.out_eq r hr

omit hv hj in
theorem ind_xsw : ind n (xsw n M j) = ind n M := by
  funext i
  unfold ind
  have hp : (xsw n M j).pad n i ↔ M.pad n i := by
    by_cases a : i = j
    · subst a
      simp only [Model.pad, xsw, if_pos rfl, ↓reduceIte]
      omega
    · by_cases b : i = j + 1
      · subst b
        simp only [Model.pad, xsw, if_neg a, if_pos rfl, ↓reduceIte]
        omega
      · by_cases c : j + 1 < i
        · simp only [Model.pad, xsw, if_neg a, if_neg b, if_pos c, tsw_eq_iff c]
        · simp only [Model.pad, xsw, if_neg a, if_neg b, if_neg c]
  by_cases h : M.pad n i
  · simp [h, hp.2 h]
  · have h' : ¬ (xsw n M j).pad n i := fun h' => h (hp.1 h')
    simp [h, h']

theorem meas2_xsw (hlt : lexKey n s M (j + 1) < lexKey n s M j) :
    meas2 n s (xsw n M j) < meas2 n s M := by
  unfold meas2
  rw [ind_xsw h1 h2 h3 h4]
  have hk : lexKey n s (xsw n M j) j = lexKey n s M (j + 1) := by simp [lexKey, xsw]
  have := lexWord_lt_of (B := lexB n s) (a := lexKey n s M) (b := lexKey n s (xsw n M j))
    (j := j)
    (fun i hi => by
      simp [lexKey, xsw, show i ≠ j by omega, show i ≠ j + 1 by omega,
        show ¬ j + 1 < i by omega])
    (by rw [hk]; exact hlt) s (by omega)
    (fun i hi => lexKey_lt (valid_xsw hv hj h1 h2 h3 h4) hi)
  omega

end xsw

/-! ## A least model is in normal form and lexicographically ordered -/

/-- The lexicographic order of adjacent independent gates. -/
def LexNF (n s : ℕ) (M : Model) : Prop :=
  ∀ j, j + 1 < s → ¬ M.pad n j → M.s1 (j + 1) ≠ n + j → M.s2 (j + 1) ≠ n + j →
    M.s1 j < M.s1 (j + 1) ∨ (M.s1 j = M.s1 (j + 1) ∧ (M.s2 j < M.s2 (j + 1) ∨
      (M.s2 j = M.s2 (j + 1) ∧ M.op j = 0 ∧ M.op (j + 1) = 1)))

/-- A model of least `meas2` is in normal form (the argument of `exists_nf`, with `meas2`). -/
theorem nf_of_min2 {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    (hmin : ∀ M', Valid n s g R M' → meas2 n s M' < meas2 n s M → False) : NF n s M := by
  classical
  have hmv : ∀ d t, d < s → TgtOk n d t →
      (M.Read n s d → ∀ r, R r → M.w d r = tval n M d t r) →
      (¬ M.pad n d ∨ ∃ i < d, ¬ M.pad n i) → False := by
    intro d t hd ht htr hpos
    have hv' := valid_mv hv hd ht htr
    exact hmin _ hv' (meas2_mv hv hv' hd hpos)
  have htriv : ∀ d < s, ¬ M.pad n d →
      (∃ t, TgtOk n d t ∧ ∀ r, R r → M.w d r = tval n M d t r) → False := by
    intro d hd hnp ⟨t, ht, hw⟩
    exact hmv d t hd ht (fun _ => hw) (Or.inl hnp)
  have padOp : ∀ j < s, M.op j = 2 → M.pad n j := by
    intro j hj h2
    by_contra hnp
    exact htriv j hj hnp (op2_triv hv hj h2)
  have noF : ∀ j < s, ¬ M.pad n j → M.s1 j ≠ n + j ∧ M.s2 j ≠ n + j := by
    intro j hj hnp
    by_contra hc
    have hF : M.s1 j = n + j ∨ M.s2 j = n + j := by tauto
    refine htriv j hj hnp (false_src hv hj ?_)
    rcases hF with h | h
    · exact Or.inl fun r _ => by rw [h]; simp [Model.sv]
    · exact Or.inr fun r _ => by rw [h]; simp [Model.sv]
  have padRd : ∀ j < s, ∀ i < j, M.pad n i → M.s1 j ≠ n + i ∧ M.s2 j ≠ n + i := by
    intro j hj i hi hpi
    by_contra hc
    have hT : M.s1 j = n + i ∨ M.s2 j = n + i := by tauto
    have hnp : ¬ M.pad n j := fun hp' => by
      rcases hT with h | h
      · have := hp'.2.1; omega
      · have := hp'.2.2; omega
    have e : ∀ r, R r → M.sv n j (n + i) r = true := by
      intro r hr
      unfold Model.sv
      simp only [if_neg (show ¬ n + i < n by omega), if_pos (show n + i < n + j by omega),
        show n + i - n = i by omega]
      exact pad_w hv (by omega) hpi hr
    refine htriv j hj hnp (true_src hv hj ?_)
    rcases hT with h | h
    · exact Or.inl fun r hr => by rw [h]; exact e r hr
    · exact Or.inr fun r hr => by rw [h]; exact e r hr
  have ord : ∀ j < s, ¬ M.pad n j → M.s1 j < M.s2 j := by
    intro j hj hnp
    by_contra hc
    by_cases he : M.s1 j = M.s2 j
    · exact htriv j hj hnp (same_src hv hj he)
    · exact hmin _ (valid_sw hv j) (meas2_sw hv hj (by omega))
  have pre : ∀ j, j + 1 < s → M.pad n (j + 1) → M.pad n j := by
    intro j hj hp1
    by_contra hnp
    exact hmv (j + 1) 1 hj (Or.inr (Or.inl rfl))
      (fun _ r hr => by rw [pad_w hv hj hp1 hr]; simp [tval]) (Or.inr ⟨j, by omega, hnp⟩)
  have rd : ∀ j < s, ¬ M.pad n j → M.Read n s j := by
    intro j hj hnp
    by_contra hc
    exact hmv j 0 hj (Or.inl rfl) (fun h => absurd h hc) (Or.inl hnp)
  refine {
    pre := pre
    padOp := padOp
    noF := noF
    noPadRd := padRd
    ord := ord
    used := ?_
    out := ?_ }
  · intro j hj hnp
    rcases rd j (by omega) hnp with h | h
    · exact h
    · exfalso
      by_cases hl : M.pad n (s - 1)
      · have hall : ∀ m, m < s → M.pad n (s - 1 - m) := by
          intro m
          induction m with
          | zero => intro _; simpa using hl
          | succ m ih =>
            intro hm
            have := pre (s - 1 - (m + 1)) (by omega)
              (by rw [show s - 1 - (m + 1) + 1 = s - 1 - m by omega]; exact ih (by omega))
            exact this
        exact hnp (by
          have := hall (s - 1 - j) (by omega)
          rwa [show s - 1 - (s - 1 - j) = j by omega] at this)
      · rcases rd (s - 1) (by omega) hl with ⟨i, hi1, hi2, _⟩ | h'
        · omega
        · omega
  · intro hs
    by_cases h6 : M.pad n (s - 1)
    · exact Or.inr h6
    · rcases rd (s - 1) (by omega) h6 with ⟨j, hj1, hj2, _⟩ | h
      · omega
      · left; omega

/-- A model of least `meas2` is lexicographically ordered. -/
theorem lex_of_min2 {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    (hmin : ∀ M', Valid n s g R M' → meas2 n s M' < meas2 n s M → False) : LexNF n s M := by
  have hnf := nf_of_min2 hv hmin
  intro j hj hnp ha hb
  have hnp1 : ¬ M.pad n (j + 1) := fun h => hnp (hnf.pre j hj h)
  have f0 := hnf.noF j (by omega) hnp
  have f1 := hnf.noF (j + 1) hj hnp1
  have l1 := hv.s1_le j (by omega)
  have l2 := hv.s2_le j (by omega)
  have l3 := hv.s1_le (j + 1) hj
  have l4 := hv.s2_le (j + 1) hj
  have h1 : M.s1 j < n + j := by omega
  have h2 : M.s2 j < n + j := by omega
  have h3 : M.s1 (j + 1) < n + j := by omega
  have h4 : M.s2 (j + 1) < n + j := by omega
  have o0 := hv.op_lt j (by omega)
  have o1 := hv.op_lt (j + 1) hj
  have o0' : M.op j ≠ 2 := fun h => hnp (hnf.padOp j (by omega) h)
  have o1' : M.op (j + 1) ≠ 2 := fun h => hnp1 (hnf.padOp (j + 1) hj h)
  -- a strictly smaller key at `j + 1` contradicts minimality through `xsw`
  have hx : lexKey n s M (j + 1) < lexKey n s M j → False := fun hlt =>
    hmin _ (valid_xsw hv hj h1 h2 h3 h4) (meas2_xsw hv hj h1 h2 h3 h4 hlt)
  have hK : ∀ y z : ℕ, y < n + j → z < 3 → y * 3 + z < 3 * (n + s + 1) := by
    intro y z hy hz; omega
  by_contra hc
  rcases lt_trichotomy (M.s1 j) (M.s1 (j + 1)) with e1 | e1 | e1
  · exact hc (Or.inl e1)
  · rcases lt_trichotomy (M.s2 j) (M.s2 (j + 1)) with e2 | e2 | e2
    · exact hc (Or.inr ⟨e1, Or.inl e2⟩)
    · by_cases e3 : M.op j = M.op (j + 1)
      · -- gate `j + 1` is a copy of wire `n + j`
        have hw : ∀ r, R r → M.w (j + 1) r = M.sv n (j + 1) (n + j) r := by
          intro r hr
          have hs : ∀ k, k < n + j → M.sv n (j + 1) k r = M.sv n j k r := by
            intro k hk
            unfold Model.sv
            by_cases h6 : k < n
            · simp [h6]
            · simp only [if_neg h6, if_pos hk, if_pos (show k < n + (j + 1) by omega)]
          rw [hv.w_eq (j + 1) hj r hr, hs _ h3, hs _ h4, ← e1, ← e2, ← e3,
            ← hv.w_eq j (by omega) r hr]
          unfold Model.sv
          simp only [if_neg (show ¬ n + j < n by omega), if_pos (show n + j < n + (j + 1) by omega),
            show n + j - n = j by omega]
        obtain ⟨t, ht, htw⟩ := copy_tgt hv hj (k := n + j) (by omega) hw
        have hv' := valid_mv hv hj ht (fun _ => htw)
        exact hmin _ hv' (meas2_mv hv hv' hj (Or.inl hnp1))
      · have : M.op j = 0 ∧ M.op (j + 1) = 1 ∨ M.op (j + 1) < M.op j := by omega
        rcases this with h | h
        · exact hc (Or.inr ⟨e1, Or.inr ⟨e2, h⟩⟩)
        · apply hx
          unfold lexKey
          exact lex3 _ _ _ _ _ _ _ (hK _ _ h4 o1) o1 (Or.inr ⟨e1.symm, Or.inr ⟨e2.symm, h⟩⟩)
    · apply hx
      unfold lexKey
      exact lex3 _ _ _ _ _ _ _ (hK _ _ h4 o1) o1 (Or.inr ⟨e1.symm, Or.inl e2⟩)
  · apply hx
    unfold lexKey
    exact lex3 _ _ _ _ _ _ _ (hK _ _ h4 o1) o1 (Or.inl e1)

/-- Among valid models there is one in normal form and lexicographically ordered. -/
theorem exists_nf2 {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} (h : ∃ M, Valid n s g R M) :
    ∃ M, Valid n s g R M ∧ NF n s M ∧ LexNF n s M := by
  classical
  have hex : ∃ m, ∃ M, Valid n s g R M ∧ meas2 n s M = m := by
    obtain ⟨M, h1⟩ := h
    exact ⟨_, M, h1, rfl⟩
  obtain ⟨M, hv, hm⟩ := Nat.find_spec hex
  have hmin : ∀ M', Valid n s g R M' → meas2 n s M' < meas2 n s M → False := by
    intro M' h1 h3
    exact Nat.find_min hex (hm ▸ h3) ⟨M', h1, rfl⟩
  exact ⟨M, hv, nf_of_min2 hv hmin, lex_of_min2 hv hmin⟩

/-! ## The formula `enc2` -/

section formula
variable (n s : ℕ)

/-- The escape literals of the order at `j`: gate `j` is padding, or gate `j + 1` reads `n + j`. -/
def lexBase (j : ℕ) : List ℕ :=
  [P (ix n s 7 j 0), P (ix n s 1 (j + 1) (n + j)), P (ix n s 2 (j + 1) (n + j))]

/-- The order: unless gate `j` is padding or gate `j + 1` reads wire `n + j`, the triple
`(s1, s2, op)` of gate `j` is lexicographically below that of gate `j + 1`. -/
def fLex : List (List ℕ) :=
  (List.range (s - 1)).flatMap fun j =>
    (List.range (n + j + 1)).flatMap fun a =>
      ((List.range a).map fun b => [Q (ix n s 1 j a), Q (ix n s 1 (j + 1) b)] ++ lexBase n s j) ++
      (List.range (n + j + 1)).flatMap fun c =>
        ((List.range c).map fun d =>
          [Q (ix n s 1 j a), Q (ix n s 1 (j + 1) a), Q (ix n s 2 j c), Q (ix n s 2 (j + 1) d)] ++
            lexBase n s j) ++
        [[Q (ix n s 1 j a), Q (ix n s 1 (j + 1) a), Q (ix n s 2 j c), Q (ix n s 2 (j + 1) c),
            Q (ix n s 0 j 1)] ++ lexBase n s j,
         [Q (ix n s 1 j a), Q (ix n s 1 (j + 1) a), Q (ix n s 2 j c), Q (ix n s 2 (j + 1) c),
            Q (ix n s 0 (j + 1) 0)] ++ lexBase n s j]

/-- The formula `enc` with the order of adjacent independent gates. -/
def enc2 (g : ℕ → Bool) (rows : List ℕ) : List (List ℕ) := enc n s g rows ++ fLex n s

end formula

theorem s_fLex {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    (hn : NF n s M) (hl : LexNF n s M) : ∀ c ∈ fLex n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fLex, List.mem_flatMap, List.mem_append, List.mem_map, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  obtain ⟨j, hj, a, ha, hc⟩ := hc
  have hj1 : j + 1 < s := Nat.add_lt_of_lt_sub hj
  have hj0 : j < s := Nat.lt_of_succ_lt hj1
  have hb1 : ClauseSat (val n s M) (lexBase n s j) ↔
      M.pad n j ∨ M.s1 (j + 1) = n + j ∨ M.s2 (j + 1) = n + j := by
    simp (disch := wdt) only [lexBase, cs_cons, cs_nil, litVal_P, v_pad, v_s1, v_s2, or_false,
      beq_iff_eq, decide_eq_true_eq]
  have happ : ∀ c', ClauseSat (val n s M) (lexBase n s j) →
      ClauseSat (val n s M) (c' ++ lexBase n s j) := fun c' ⟨l, hl', hv'⟩ =>
    ⟨l, List.mem_append_right _ hl', hv'⟩
  have hfront : ∀ c', (∃ l ∈ c', litVal (val n s M) l = true) →
      ClauseSat (val n s M) (c' ++ lexBase n s j) := fun c' ⟨l, hl', hv'⟩ =>
    ⟨l, List.mem_append_left _ hl', hv'⟩
  by_cases hesc : M.pad n j ∨ M.s1 (j + 1) = n + j ∨ M.s2 (j + 1) = n + j
  · rcases hc with ⟨b, hb, rfl⟩ | ⟨c', hc', ⟨d, hd, rfl⟩ | rfl | rfl⟩ <;>
      exact happ _ (hb1.2 hesc)
  have hnp : ¬ M.pad n j := fun h => hesc (Or.inl h)
  have L := hl j hj1 hnp (fun h => hesc (Or.inr (Or.inl h)))
    (fun h => hesc (Or.inr (Or.inr h)))
  have hop0 := hn.padOp j hj0
  rcases hc with ⟨b, hb, rfl⟩ | ⟨c', hc', ⟨d, hd, rfl⟩ | rfl | rfl⟩ <;> apply hfront <;>
    simp (disch := wdt) only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
      exists_eq_left, litVal_Q, v_s1, v_s2, v_op, Bool.not_eq_true', beq_eq_false_iff_ne,
      ne_eq] <;> omega

/-- A valid model in normal form, lexicographically ordered, satisfies every clause of `enc2`. -/
theorem enc2_sat {n s : ℕ} {g : ℕ → Bool} {rows : List ℕ} {M : Model}
    (hrows : ∀ r ∈ rows, r < 2 ^ n) (hv : Valid n s g (· ∈ rows) M) (hn : NF n s M)
    (hl : LexNF n s M) : ∀ c ∈ enc2 n s g rows, ClauseSat (val n s M) c := by
  intro c hc
  rcases List.mem_append.1 hc with h | h
  · exact enc_sat hrows hv hn c h
  · exact s_fLex hv hn hl c h

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
/-- If a circuit of AND and OR gates of fan-in at most two with at most `s` gates computes `f`
on `n` inputs, then `enc2 n s (rowFun n f) rows` is satisfiable, for every list of rows below
`2 ^ n`. -/
theorem link2 (n s : ℕ) (f : (Fin n → Bool) → Bool) (rows : List ℕ)
    (hrows : ∀ r ∈ rows, r < 2 ^ n) (C : Circuit) (hC : Monotone2 C) (hsz : C.size ≤ s)
    (hev : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) :
    FormulaSat (enc2 n s (rowFun n f) rows) := by
  have hv := valid_ofCirc n s (rowFun n f) (· ∈ rows) C hC hsz (fun r _ => hev _)
  obtain ⟨M, hM, hnf, hlx⟩ := exists_nf2 ⟨_, hv⟩
  exact ⟨val n s M, enc2_sat hrows hM hnf hlx⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
/-- If `enc2 n s (rowFun n f) rows` is unsatisfiable, every circuit of AND and OR gates of
fan-in at most two computing `f` on `n` inputs has at least `s + 1` gates. -/
theorem lower_of_unsat2 (n s : ℕ) (f : (Fin n → Bool) → Bool) (rows : List ℕ)
    (hrows : ∀ r ∈ rows, r < 2 ^ n) (hU : ¬ FormulaSat (enc2 n s (rowFun n f) rows)) :
    ∀ C : Circuit, Monotone2 C → (∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) →
      s + 1 ≤ C.size := by
  intro C hC hev
  by_contra h
  exact hU (link2 n s f rows hrows C hC (by omega) hev)

end PEqualNP.Library.LRAT.Link
