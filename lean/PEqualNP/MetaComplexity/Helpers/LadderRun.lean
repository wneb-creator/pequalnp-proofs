import Mathlib

/-!
# Ladder, steps 3 and 6 (hub row L-meta-1048): the run argument and the chain costs

Conjecture until checked. Mathlib only.

* `lr_runs_le` (step 3): a map from the levels `0 .. M-1` to `Fin t → Bool` whose fibres are
  intervals bounds the minimum over cuts (written exactly as in the row's term) by any bound
  that holds on every pair of levels with the same image.
* `lr_chain_cost` (step 6): for the plane and chain of the row, levels `u ≤ v < h + 3`
  (`lr_level`: 0 the empty set, `1 .. h+1` the chain sets, `h + 2` all points), the sum over
  lines missing level `u` and meeting level `v` in at least two points of
  `(|line ∩ level v| - 1)` equals the cost written in the row's term.
-/

namespace PEqualNP.MetaComplexity.Ladder

open Finset

/-! ## Step 3: the run argument -/

theorem lr_untopD_min_le {s : Finset ℕ} {a B : ℕ} (ha : a ∈ s) (hB : a ≤ B) :
    WithTop.untopD 0 s.min ≤ B := by
  have hmin := Finset.min_le ha
  generalize s.min = m at hmin ⊢
  induction m using WithTop.recTopCoe with
  | top => exact absurd hmin (by simp)
  | coe m =>
    rw [WithTop.untopD_coe]
    exact le_trans (WithTop.coe_le_coe.1 hmin) hB

theorem lr_runs_le (M t : ℕ) (f : ℕ → (Fin t → Bool))
    (hf : ∀ u w v : ℕ, u ≤ w → w ≤ v → v < M → f u = f v → f w = f u)
    (c : ℕ × ℕ → ℕ) (B : ℕ)
    (hc : ∀ u v : ℕ, u ≤ v → v < M → f u = f v → c (u, v) ≤ B) :
    WithTop.untopD 0 (((Finset.range M).powerset.filter
      (fun P : Finset ℕ => P.card + 1 ≤ 2 ^ t)).image (fun P : Finset ℕ =>
        ((Finset.range M ×ˢ Finset.range M).filter (fun uv : ℕ × ℕ =>
          uv.1 ≤ uv.2 ∧ ∀ w ∈ P, ¬ (uv.1 < w ∧ w ≤ uv.2))).sup c)).min ≤ B := by
  classical
  set P : Finset ℕ := (Finset.range M).filter (fun u => 1 ≤ u ∧ f u ≠ f (u - 1)) with hP
  have hrun : ∀ u v, u ≤ v → v < M → (∀ w ∈ P, ¬ (u < w ∧ w ≤ v)) → f u = f v := by
    intro u v huv
    induction v, huv using Nat.le_induction with
    | base => intro _ _; rfl
    | succ v huv ih =>
      intro hvM hno
      have h1 : f (v + 1) = f v := by
        by_contra hne
        exact hno (v + 1)
          (Finset.mem_filter.2 ⟨Finset.mem_range.2 hvM, by omega, by simpa using hne⟩)
          ⟨by omega, le_rfl⟩
      rw [h1]
      exact ih (by omega) (fun w hw hw' => hno w hw ⟨hw'.1, by omega⟩)
  have hcard : P.card + 1 ≤ 2 ^ t := by
    have h0 : (0 : ℕ) ∉ P := by simp [hP]
    have key : ∀ u u', u' ∈ P → u < u' → f u ≠ f u' := by
      intro u u' hu' hlt heq
      obtain ⟨hu'M, _, hne⟩ := Finset.mem_filter.1 hu'
      apply hne
      have := hf u (u' - 1) u' (by omega) (by omega) (Finset.mem_range.1 hu'M) heq
      rw [this, heq]
    have hinj : Set.InjOn f (insert 0 P : Finset ℕ) := by
      intro u hu u' hu' heq
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hu hu'
      rcases lt_trichotomy u u' with h | h | h
      · exfalso
        rcases hu' with rfl | hu'
        · omega
        · exact key u u' hu' h heq
      · exact h
      · exfalso
        rcases hu with rfl | hu
        · omega
        · exact key u' u hu h heq.symm
    have := Finset.card_le_card_of_injOn f (t := (Finset.univ : Finset (Fin t → Bool)))
      (fun a _ => by simp) hinj
    rw [Finset.card_insert_of_notMem h0, Finset.card_univ, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin] at this
    exact this
  apply lr_untopD_min_le (Finset.mem_image_of_mem _
    (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.filter_subset _ _), hcard⟩))
  apply Finset.sup_le
  intro uv huv
  obtain ⟨hmem, hle, hno⟩ := Finset.mem_filter.1 huv
  obtain ⟨_, h2⟩ := Finset.mem_product.1 hmem
  have := hc uv.1 uv.2 hle (Finset.mem_range.1 h2)
    (hrun uv.1 uv.2 hle (Finset.mem_range.1 h2) hno)
  simpa using this

/-! ## Step 6: the chain costs -/

/-- Level `u` of the ladder: `0` is the empty set, `1 .. h+1` are `K 0 .. K h`, and every
higher level (in use: `h + 2`) is the set of all points. -/
def lr_level (h : ℕ) {n : ℕ} (K : Fin (h + 1) → Finset (Fin n)) (u : ℕ) : Finset (Fin n) :=
  if u = 0 then ∅ else if hu : u - 1 < h + 1 then K ⟨u - 1, hu⟩ else Finset.univ

/-- Every point of the plane lies on exactly `q + 1` lines. -/
theorem lr_lines_through (q n : ℕ) (S : Fin n → Finset (Fin n)) (hq : 1 ≤ q)
    (hn : n = q * q + q + 1)
    (hS : ∀ i : Fin n, (S i).card = q + 1)
    (hSS : ∀ i j : Fin n, i ≠ j → (S i ∩ S j).card = 1)
    (hcov : ∀ p p' : Fin n, p ≠ p' → ∃ i : Fin n, p ∈ S i ∧ p' ∈ S i) (p : Fin n) :
    (Finset.univ.filter (fun i => p ∈ S i)).card = q + 1 := by
  classical
  set T := Finset.univ.filter (fun i => p ∈ S i) with hT
  have hcover : (Finset.univ.erase p) = T.biUnion (fun i => (S i).erase p) := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_biUnion, hT,
      Finset.mem_filter, true_and]
    constructor
    · intro hx
      obtain ⟨i, hpi, hxi⟩ := hcov p x (Ne.symm hx)
      exact ⟨i, hpi, hx, hxi⟩
    · rintro ⟨i, _, hx, _⟩
      exact hx
  have hdisj : (T : Set (Fin n)).PairwiseDisjoint (fun i => (S i).erase p) := by
    intro i hi j hj hij
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, hT] at hi hj
    rw [Function.onFun, Finset.disjoint_left]
    intro x hxi hxj
    rw [Finset.mem_erase] at hxi hxj
    have h1 := hSS i j hij
    have hle : (S i ∩ S j).card ≤ 1 := h1.le
    rw [Finset.card_le_one] at hle
    exact hxi.1 (hle x (Finset.mem_inter.2 ⟨hxi.2, hxj.2⟩) p (Finset.mem_inter.2 ⟨hi, hj⟩))
  have hc := congrArg Finset.card hcover
  rw [Finset.card_biUnion hdisj, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, Fintype.card_fin] at hc
  have hsum : ∑ i ∈ T, ((S i).erase p).card = ∑ i ∈ T, q := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.card_erase_of_mem (Finset.mem_filter.1 hi).2, hS i]
    simp
  rw [hsum, Finset.sum_const, smul_eq_mul] at hc
  have : T.card * q = (q + 1) * q := by rw [← hc, hn]; ring_nf; omega
  exact Nat.eq_of_mul_eq_mul_right hq this

/-- Double count: the lines meet a point set `A` in `(q + 1) |A|` incidences. -/
theorem lr_double_count (q n : ℕ) (S : Fin n → Finset (Fin n))
    (hthrough : ∀ p : Fin n, (Finset.univ.filter (fun i => p ∈ S i)).card = q + 1)
    (A : Finset (Fin n)) :
    ∑ i, (S i ∩ A).card = (q + 1) * A.card := by
  classical
  have h1 : ∀ i, (S i ∩ A).card = ∑ p ∈ A, if p ∈ S i then 1 else 0 := by
    intro i
    rw [← Finset.card_filter]
    congr 1
    ext x
    simp [and_comm]
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ p ∈ A, (∑ i, if p ∈ S i then 1 else 0) = q + 1 := by
    intro p _
    rw [← Finset.card_filter, hthrough p]
  rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, mul_comm]

/-- A set met by every line in `0` or `s` points: `s` times the number of lines meeting it is
`(q + 1) |A|`. -/
theorem lr_missing_eq (q n : ℕ) (S : Fin n → Finset (Fin n))
    (hthrough : ∀ p : Fin n, (Finset.univ.filter (fun i => p ∈ S i)).card = q + 1)
    (A : Finset (Fin n)) (s : ℕ) (hA : ∀ i, (S i ∩ A).card = 0 ∨ (S i ∩ A).card = s) :
    s * (n - (Finset.univ.filter (fun i => S i ∩ A = ∅)).card) = (q + 1) * A.card := by
  classical
  rw [← lr_double_count q n S hthrough A]
  have h1 : ∀ i, (S i ∩ A).card = if S i ∩ A = ∅ then 0 else s := by
    intro i
    split_ifs with h
    · rw [h]; rfl
    · rcases hA i with h' | h'
      · exact absurd (Finset.card_eq_zero.1 h') h
      · exact h'
  simp_rw [h1]
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul, mul_comm]
  congr 1
  have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun i => S i ∩ A = ∅)
  rw [Finset.card_univ, Fintype.card_fin] at this
  omega

/-- The sum of step 5 for two nested sets, the bigger met by every line in `0` or `s` points. -/
theorem lr_sum_eq (n : ℕ) (S : Fin n → Finset (Fin n)) (A B : Finset (Fin n)) (hAB : A ⊆ B)
    (s : ℕ) (hB : ∀ i, (S i ∩ B).card = 0 ∨ (S i ∩ B).card = s) :
    ∑ w ∈ Finset.univ.filter (fun w => S w ∩ A = ∅ ∧ 2 ≤ (S w ∩ B).card),
        ((S w ∩ B).card - 1)
      = ((Finset.univ.filter (fun i => S i ∩ A = ∅)).card
          - (Finset.univ.filter (fun i => S i ∩ B = ∅)).card) * (s - 1) := by
  classical
  by_cases hs : s ≤ 1
  · have : Finset.univ.filter (fun w => S w ∩ A = ∅ ∧ 2 ≤ (S w ∩ B).card) = ∅ := by
      apply Finset.filter_false_of_mem
      intro w _ ⟨_, h2⟩
      rcases hB w with h | h <;> omega
    rw [this, Finset.sum_empty]
    have : s - 1 = 0 := by omega
    rw [this, mul_zero]
  · push_neg at hs
    have hfil : Finset.univ.filter (fun w => S w ∩ A = ∅ ∧ 2 ≤ (S w ∩ B).card)
        = (Finset.univ.filter (fun i => S i ∩ A = ∅)).filter (fun i => ¬ S i ∩ B = ∅) := by
      rw [Finset.filter_filter]
      apply Finset.filter_congr
      intro w _
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, fun h => ?_⟩
        rw [h] at h2
        simp at h2
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        rcases hB w with h | h
        · exact absurd (Finset.card_eq_zero.1 h) h2
        · omega
    rw [hfil]
    have hconst : ∀ w ∈ (Finset.univ.filter (fun i => S i ∩ A = ∅)).filter
        (fun i => ¬ S i ∩ B = ∅), (S w ∩ B).card - 1 = s - 1 := by
      intro w hw
      have h2 := (Finset.mem_filter.1 hw).2
      rcases hB w with h | h
      · exact absurd (Finset.card_eq_zero.1 h) h2
      · rw [h]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul]
    congr 1
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := Finset.univ.filter (fun i => S i ∩ A = ∅)) (fun i => S i ∩ B = ∅)
    have hsub : (Finset.univ.filter (fun i => S i ∩ A = ∅)).filter (fun i => S i ∩ B = ∅)
        = Finset.univ.filter (fun i => S i ∩ B = ∅) := by
      rw [Finset.filter_filter]
      apply Finset.filter_congr
      intro w _
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨?_, h⟩
        apply Finset.subset_empty.1
        intro x hx
        rw [← h]
        exact Finset.mem_inter.2 ⟨(Finset.mem_inter.1 hx).1, hAB (Finset.mem_inter.1 hx).2⟩
    rw [hsub] at hsplit
    omega

/-- The levels are nested. -/
theorem lr_level_mono (h n : ℕ) (K : Fin (h + 1) → Finset (Fin n))
    (hmono : ∀ j j' : Fin (h + 1), j ≤ j' → K j ⊆ K j') (u v : ℕ) (huv : u ≤ v) :
    lr_level h K u ⊆ lr_level h K v := by
  unfold lr_level
  by_cases hu : u = 0
  · simp [hu]
  · have hv : v ≠ 0 := by omega
    rw [if_neg hu, if_neg hv]
    by_cases hu' : u - 1 < h + 1
    · rw [dif_pos hu']
      by_cases hv' : v - 1 < h + 1
      · rw [dif_pos hv']
        apply hmono
        rw [Fin.mk_le_mk]
        omega
      · rw [dif_neg hv']
        exact Finset.subset_univ _
    · have hv' : ¬ v - 1 < h + 1 := by omega
      rw [dif_neg hu', dif_neg hv']

/-- The data of one level: the line meets it in `0` or `s` points, the number of lines
missing it, and `s - 1`, both as written in the row's term. -/
theorem lr_level_data (h q n : ℕ) (S : Fin n → Finset (Fin n)) (K : Fin (h + 1) → Finset (Fin n))
    (hq : q = 2 ^ h) (hn : n = q * q + q + 1)
    (hS : ∀ i : Fin n, (S i).card = q + 1)
    (hSS : ∀ i j : Fin n, i ≠ j → (S i ∩ S j).card = 1)
    (hcov : ∀ p p' : Fin n, p ≠ p' → ∃ i : Fin n, p ∈ S i ∧ p' ∈ S i)
    (hK : ∀ j : Fin (h + 1), (K j).card = (2 ^ (j : ℕ) - 1) * q + 2 ^ (j : ℕ))
    (hKS : ∀ (j : Fin (h + 1)) (i : Fin n),
      (S i ∩ K j).card = 0 ∨ (S i ∩ K j).card = 2 ^ (j : ℕ))
    (v : ℕ) (hv : v < h + 3) :
    ∃ s : ℕ, (∀ i, (S i ∩ lr_level h K v).card = 0 ∨ (S i ∩ lr_level h K v).card = s) ∧
      (Finset.univ.filter (fun i => S i ∩ lr_level h K v = ∅)).card
        = (if v = 0 then n else if v = h + 2 then 0 else q * (q + 1) / 2 ^ (v - 1) - q) ∧
      s - 1 = (if v = h + 2 then q else 2 ^ (v - 1) - 1) := by
  classical
  have hq1 : 1 ≤ q := by rw [hq]; exact Nat.one_le_two_pow
  by_cases h0 : v = 0
  · subst h0
    refine ⟨0, fun i => Or.inl (by simp [lr_level]), ?_, ?_⟩
    · simp [lr_level]
    · have : (0 : ℕ) ≠ h + 2 := by omega
      simp [this]
  by_cases htop : v = h + 2
  · subst htop
    have hl : lr_level h K (h + 2) = Finset.univ := by
      unfold lr_level
      rw [if_neg (by omega), dif_neg (by omega)]
    refine ⟨q + 1, fun i => Or.inr (by rw [hl, Finset.inter_univ, hS i]), ?_, ?_⟩
    · rw [if_neg (by omega), if_pos rfl, hl]
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro i _ hi
      rw [Finset.inter_univ] at hi
      have := hS i
      rw [hi] at this
      simp at this
    · rw [if_pos rfl]; omega
  -- a chain level
  have hj : v - 1 < h + 1 := by omega
  have hl : lr_level h K v = K ⟨v - 1, hj⟩ := by
    unfold lr_level
    rw [if_neg h0, dif_pos hj]
  have hthrough := lr_lines_through q n S hq1 hn hS hSS hcov
  refine ⟨2 ^ (v - 1), fun i => by rw [hl]; exact hKS _ i, ?_, ?_⟩
  · rw [if_neg h0, if_neg htop, hl]
    have hm := lr_missing_eq q n S hthrough (K ⟨v - 1, hj⟩) (2 ^ (v - 1)) (hKS _)
    rw [hK] at hm
    simp only at hm
    set m := (Finset.univ.filter (fun i => S i ∩ K ⟨v - 1, hj⟩ = ∅)).card with hmdef
    have hmn : m ≤ n := by
      rw [hmdef]
      calc _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
        _ = n := by simp
    -- q = a * r with a = 2^(v-1), r = 2^(h - (v-1))
    set a := 2 ^ (v - 1) with ha
    set r := 2 ^ (h - (v - 1)) with hr
    have hqar : q = a * r := by
      rw [hq, ha, hr, ← pow_add]
      congr 1
      omega
    have ha1 : 1 ≤ a := Nat.one_le_two_pow
    obtain ⟨b, hb⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    have hab : a - 1 = b := by omega
    rw [hab] at hm
    -- cancel a
    have hd : n - m = (q + 1) * (b * r + 1) := by
      apply Nat.eq_of_mul_eq_mul_left (show 0 < a by omega)
      rw [hm, hqar, hb]
      ring
    have hdiv : q * (q + 1) / a = r * (q + 1) := by
      rw [hqar]
      rw [show a * r * (a * r + 1) = a * (r * (a * r + 1)) by ring]
      exact Nat.mul_div_cancel_left _ (by omega)
    rw [hdiv]
    have hz : (m : ℤ) + q = (q + 1) * r := by
      have e1 : (m : ℤ) + ((q + 1) * (b * r + 1) : ℕ) = n := by
        rw [← hd]; push_cast [hmn]; ring
      have e2 : (q : ℤ) = (b + 1) * r := by rw [hqar, hb]; push_cast; ring
      push_cast at e1
      rw [hn] at e1
      push_cast at e1
      linear_combination e1 + (q + 1) * e2
    have hz' : m + q = (q + 1) * r := by exact_mod_cast hz
    rw [mul_comm r]
    omega
  · rw [if_neg htop]

/-- Step 6, the chain costs: for levels `u ≤ v < h + 3`, the sum over lines missing level `u`
that meet level `v` in at least two points of `(|line ∩ level v| - 1)` is the cost of the pair
`(u, v)` as written in the row's term. -/
theorem lr_chain_cost (h q n : ℕ) (S : Fin n → Finset (Fin n))
    (K : Fin (h + 1) → Finset (Fin n))
    (hq : q = 2 ^ h) (hn : n = q * q + q + 1)
    (hS : ∀ i : Fin n, (S i).card = q + 1)
    (hSS : ∀ i j : Fin n, i ≠ j → (S i ∩ S j).card = 1)
    (hcov : ∀ p p' : Fin n, p ≠ p' → ∃ i : Fin n, p ∈ S i ∧ p' ∈ S i)
    (hK : ∀ j : Fin (h + 1), (K j).card = (2 ^ (j : ℕ) - 1) * q + 2 ^ (j : ℕ))
    (hKS : ∀ (j : Fin (h + 1)) (i : Fin n),
      (S i ∩ K j).card = 0 ∨ (S i ∩ K j).card = 2 ^ (j : ℕ))
    (hmono : ∀ j j' : Fin (h + 1), j ≤ j' → K j ⊆ K j')
    (u v : ℕ) (huv : u ≤ v) (hv : v < h + 3) :
    ∑ w ∈ Finset.univ.filter (fun w => S w ∩ lr_level h K u = ∅ ∧
        2 ≤ (S w ∩ lr_level h K v).card), ((S w ∩ lr_level h K v).card - 1)
      = ((if u = 0 then n else if u = h + 2 then 0 else q * (q + 1) / 2 ^ (u - 1) - q) -
          (if v = 0 then n else if v = h + 2 then 0 else q * (q + 1) / 2 ^ (v - 1) - q)) *
        (if v = h + 2 then q else 2 ^ (v - 1) - 1) := by
  obtain ⟨s, hsv, hmv, hs1⟩ := lr_level_data h q n S K hq hn hS hSS hcov hK hKS v hv
  obtain ⟨s', _, hmu, _⟩ := lr_level_data h q n S K hq hn hS hSS hcov hK hKS u (by omega)
  rw [lr_sum_eq n S _ _ (lr_level_mono h n K hmono u v huv) s hsv, hmv, hmu, hs1]

end PEqualNP.MetaComplexity.Ladder
