import Mathlib
import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_29742_aux

lemma width_exists (k : ℕ) (hk : 64 ≤ k) :
    ∃ t : ℕ, 512 * k ≤ 2 ^ t ∧ 2 ^ t < 1024 * k := by
  have h1 : 1 < 512 * k := by omega
  refine ⟨Nat.clog 2 (512 * k), Nat.le_pow_clog (by norm_num) (512 * k), ?_⟩
  have hpos : 0 < Nat.clog 2 (512 * k) := Nat.clog_pos (by norm_num) h1
  have hlt : 2 ^ (Nat.clog 2 (512 * k) - 1) < 512 * k := Nat.pow_pred_clog_lt_self 2 h1
  have hsucc : 2 ^ Nat.clog 2 (512 * k) = 2 * 2 ^ (Nat.clog 2 (512 * k) - 1) := by
    rw [← pow_succ']; congr 1; omega
  omega

end PEqualNP.Outside.L_meta_29742_aux


namespace PEqualNP.Outside.L_meta_29742_aux.Tape

private lemma zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · left; rfl
  · right; rfl

private lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  rcases zmod2_eq_zero_or_one x with rfl | rfl <;> decide

private lemma pow_succ_mul_sub_le (B : ℕ) : ∀ t : ℕ, t ≤ B → (B + 1) ^ t * (B - t) ≤ B ^ (t + 1) := by
  intro t
  induction t with
  | zero =>
    intro _
    simp
  | succ t ih =>
    intro ht
    have ht' : t ≤ B := by omega
    have hih := ih ht'
    have hstep : (B + 1) * (B - (t + 1)) ≤ (B - t) * B := by
      zify [ht, ht']
      nlinarith
    calc (B + 1) ^ (t + 1) * (B - (t + 1))
        = (B + 1) ^ t * ((B + 1) * (B - (t + 1))) := by ring
      _ ≤ (B + 1) ^ t * ((B - t) * B) := Nat.mul_le_mul_left _ hstep
      _ = ((B + 1) ^ t * (B - t)) * B := by ring
      _ ≤ B ^ (t + 1) * B := Nat.mul_le_mul_right B hih
      _ = B ^ (t + 2) := by ring

private lemma nat_le_of_pow_le_pow_left {a b n : ℕ} (hn : n ≠ 0) (h : a ^ n ≤ b ^ n) : a ≤ b := by
  by_contra hlt
  have hgt : b < a := Nat.lt_of_not_le hlt
  have hpow : b ^ n < a ^ n := Nat.pow_lt_pow_left hgt hn
  omega

private lemma sum_pow_eq_sum_prod {α : Type*} (s : Finset α) (g : α → ℕ) (r : ℕ) :
    (∑ a ∈ s, g a) ^ r = ∑ f : Fin r → s, ∏ t : Fin r, g (f t).1 := by
  have hps := Fintype.prod_sum (fun (_ : Fin r) (a : s) => g a.1)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hps
  rw [← Finset.sum_coe_sort s g]
  exact hps

private lemma pow_half_le_two_mul (k : ℕ) (hk : 0 < k) :
    (2 * k + 1) ^ k ≤ 2 * (2 * k) ^ k := by
  have h := pow_succ_mul_sub_le (2 * k) k (by omega)
  have hsub : 2 * k - k = k := by omega
  rw [hsub] at h
  have h2 : (2 * k + 1) ^ k * k ≤ (2 * (2 * k) ^ k) * k := by
    calc (2 * k + 1) ^ k * k
        ≤ (2 * k) ^ (k + 1) := h
      _ = (2 * (2 * k) ^ k) * k := by ring
  exact Nat.le_of_mul_le_mul_right h2 hk

private def wt {m : ℕ} (y : Fin m → ZMod 2) : ℕ :=
  (Finset.univ.filter (fun j : Fin m => y j = 1)).card

private lemma wt_le {m : ℕ} (y : Fin m → ZMod 2) : wt y ≤ m := by
  calc wt y ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_filter_le _ _
    _ = m := by simp

private lemma wt_add_one {m : ℕ} (y : Fin m → ZMod 2) :
    wt (fun j => y j + 1) = m - wt y := by
  have hdisj : Disjoint (Finset.univ.filter (fun j : Fin m => y j = 1))
      (Finset.univ.filter (fun j : Fin m => y j + 1 = 1)) := by
    rw [Finset.disjoint_left]
    intro j h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    rw [h1] at h2
    exact absurd h2 (by decide)
  have hunion : Finset.univ.filter (fun j : Fin m => y j = 1) ∪
      Finset.univ.filter (fun j : Fin m => y j + 1 = 1) = Finset.univ := by
    ext j
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    rcases zmod2_eq_zero_or_one (y j) with h | h
    · right; rw [h]; decide
    · left; exact h
  have hsum : wt y + wt (fun j => y j + 1) = m := by
    change (Finset.univ.filter (fun j : Fin m => y j = 1)).card +
      (Finset.univ.filter (fun j : Fin m => y j + 1 = 1)).card = m
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
  omega

private lemma sum_pow_wt (m A B : ℕ) :
    ∑ y : Fin m → ZMod 2, A ^ wt y * B ^ (m - wt y) = (A + B) ^ m := by
  induction m with
  | zero =>
    have huniq : (Finset.univ : Finset (Fin 0 → ZMod 2)) = {Fin.elim0} := by
      ext y
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      funext i; exact Fin.elim0 i
    rw [huniq, Finset.sum_singleton]
    simp [wt]
  | succ m ih =>
    have hwt_cons : ∀ (b : ZMod 2) (y : Fin m → ZMod 2),
        wt (Fin.cons (α := fun _ => ZMod 2) b y) = (if b = 1 then 1 else 0) + wt y := by
      intro b y
      unfold wt
      have hsplit : (Finset.univ.filter (fun j : Fin (m + 1) => Fin.cons (α := fun _ => ZMod 2) b y j = 1)).card =
          (if b = 1 then 1 else 0) +
          ((Finset.univ.filter (fun j : Fin m => y j = 1)).image Fin.succ).card := by
        have hdisj : Disjoint (if b = 1 then ({0} : Finset (Fin (m + 1))) else ∅)
            ((Finset.univ.filter (fun j : Fin m => y j = 1)).image Fin.succ) := by
          split_ifs
          · rw [Finset.disjoint_singleton_left]
            simp
          · exact Finset.disjoint_empty_left _
        have heq : Finset.univ.filter (fun j : Fin (m + 1) => Fin.cons (α := fun _ => ZMod 2) b y j = 1) =
            (if b = 1 then ({0} : Finset (Fin (m + 1))) else ∅) ∪
            (Finset.univ.filter (fun j : Fin m => y j = 1)).image Fin.succ := by
          ext j
          refine Fin.cases ?_ ?_ j
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.cons_zero,
              Finset.mem_union, Finset.mem_image, Fin.succ_ne_zero, and_false, exists_false, or_false]
            split_ifs with hb <;> simp [hb]
          · intro i
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.cons_succ,
              Finset.mem_union, Finset.mem_image]
            constructor
            · intro hy; right; exact ⟨i, hy, rfl⟩
            · rintro (h0 | ⟨i', hi', hsucc⟩)
              · split_ifs at h0
                · rw [Finset.mem_singleton] at h0; exact absurd h0 (Fin.succ_ne_zero i)
                · exact absurd h0 (Finset.notMem_empty _)
              · cases Fin.succ_injective _ hsucc; exact hi'
        rw [heq, Finset.card_union_of_disjoint hdisj]
        congr 1
        split_ifs <;> simp
      rw [hsplit, Finset.card_image_of_injective _ (Fin.succ_injective m)]
    have hbij : ∑ y : Fin (m + 1) → ZMod 2, A ^ wt y * B ^ (m + 1 - wt y) =
        ∑ p : ZMod 2 × (Fin m → ZMod 2),
          A ^ wt (Fin.cons p.1 p.2) * B ^ (m + 1 - wt (Fin.cons p.1 p.2)) := by
      symm
      apply Finset.sum_bij (fun p _ => Fin.cons p.1 p.2)
      · intro _ _; exact Finset.mem_univ _
      · intro p1 _ p2 _ h
        have h0 : p1.1 = p2.1 := by
          have := congrFun h 0
          simpa using this
        have htl : p1.2 = p2.2 := by
          funext i
          have := congrFun h i.succ
          simpa using this
        exact Prod.ext h0 htl
      · intro y _
        refine ⟨(y 0, fun i => y i.succ), Finset.mem_univ _, ?_⟩
        funext j
        refine Fin.cases ?_ ?_ j
        · simp
        · intro i; simp
      · intro _ _; rfl
    rw [hbij, Fintype.sum_prod_type]
    have huniv2 : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
    rw [huniv2, Finset.sum_pair (by decide : (0 : ZMod 2) ≠ 1)]
    have h0 : ∑ y : Fin m → ZMod 2,
        A ^ wt (Fin.cons 0 y) * B ^ (m + 1 - wt (Fin.cons 0 y)) = B * (A + B) ^ m := by
      have hterm : ∀ y : Fin m → ZMod 2,
          A ^ wt (Fin.cons 0 y) * B ^ (m + 1 - wt (Fin.cons 0 y)) =
          B * (A ^ wt y * B ^ (m - wt y)) := by
        intro y
        rw [hwt_cons]
        have h01 : (0 : ZMod 2) ≠ 1 := by decide
        simp only [h01, ↓reduceIte, zero_add]
        have hle := wt_le y
        have hsub : m + 1 - wt y = (m - wt y) + 1 := by omega
        rw [hsub, pow_succ]
        ring
      simp_rw [hterm, ← Finset.mul_sum, ih]
    have h1 : ∑ y : Fin m → ZMod 2,
        A ^ wt (Fin.cons 1 y) * B ^ (m + 1 - wt (Fin.cons 1 y)) = A * (A + B) ^ m := by
      have hterm : ∀ y : Fin m → ZMod 2,
          A ^ wt (Fin.cons 1 y) * B ^ (m + 1 - wt (Fin.cons 1 y)) =
          A * (A ^ wt y * B ^ (m - wt y)) := by
        intro y
        rw [hwt_cons]
        simp only [↓reduceIte]
        have hsub : m + 1 - (1 + wt y) = m - wt y := by omega
        rw [hsub, Nat.add_comm 1 (wt y), pow_succ]
        ring
      simp_rw [hterm, ← Finset.mul_sum, ih]
    rw [h0, h1, pow_succ]
    ring

private lemma card_toBits_bijective (N : ℕ) :
    Function.Bijective (fun (s : Fin (2 ^ N)) (t : Fin N) =>
      if s.val.testBit t.val then (1 : ZMod 2) else 0) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, ?_⟩
  · intro s1 s2 h
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < N
    · have hi' := congrFun h ⟨i, hi⟩
      dsimp only at hi'
      cases hb1 : s1.val.testBit i <;> cases hb2 : s2.val.testBit i
      · rfl
      · simp [hb1, hb2] at hi'
      · simp [hb1, hb2] at hi'
      · rfl
    · have h1 : s1.val.testBit i = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le s1.isLt (Nat.pow_le_pow_right (by omega) (Nat.le_of_not_lt hi)))
      have h2 : s2.val.testBit i = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le s2.isLt (Nat.pow_le_pow_right (by omega) (Nat.le_of_not_lt hi)))
      rw [h1, h2]
  · simp [Fintype.card_fin, ZMod.card]

private lemma card_shift_linear_fiber (n L : ℕ) (hn : 0 < n) (hL : 0 < L)
    (c : Fin n → ZMod 2) (hc : c ≠ 0) (y : Fin L → ZMod 2) :
    (Finset.univ.filter (fun v : Fin (n + L - 1) → ZMod 2 =>
      (fun j : Fin L => ∑ i : Fin n, c i * v ⟨j.val + i.val, by omega⟩) = y)).card = 2 ^ (n - 1) := by
  let N := n + L - 1
  have hN : N = n + L - 1 := rfl
  let Sc : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => c i = 1)
  have hSc_ne : Sc.Nonempty := by
    by_contra hempty
    apply hc
    funext i
    rcases zmod2_eq_zero_or_one (c i) with h0 | h1
    · exact h0
    · exfalso
      exact hempty ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, h1⟩⟩
  let p : Fin n := Sc.max' hSc_ne
  have hcp : c p = 1 := (Finset.mem_filter.mp (Finset.max'_mem Sc hSc_ne)).2
  have hc_gt : ∀ i : Fin n, p < i → c i = 0 := by
    intro i hgt
    rcases zmod2_eq_zero_or_one (c i) with h0 | h1
    · exact h0
    · exfalso
      have hmem : i ∈ Sc := Finset.mem_filter.mpr ⟨Finset.mem_univ i, h1⟩
      have hle : i ≤ p := Finset.le_max' Sc i hmem
      exact not_le_of_gt hgt hle
  let Φ : (Fin N → ZMod 2) → (Fin L → ZMod 2) :=
    fun v j => ∑ i : Fin n, c i * v ⟨j.val + i.val, by omega⟩
  let Out := { t : Fin N // ¬ (p.val ≤ t.val ∧ t.val < p.val + L) }
  have hOut_card : Fintype.card Out = n - 1 := by
    let InS : Finset (Fin N) := Finset.univ.filter (fun t : Fin N => p.val ≤ t.val ∧ t.val < p.val + L)
    have hIn_card : InS.card = L := by
      have hbij : InS.card = (Finset.univ : Finset (Fin L)).card := by
        symm
        apply Finset.card_bij (fun (j : Fin L) _ => (⟨p.val + j.val, by omega⟩ : Fin N))
        · intro j _
          simp only [InS, Finset.mem_filter, Finset.mem_univ, true_and]
          omega
        · intro j1 _ j2 _ h
          have hv : p.val + j1.val = p.val + j2.val := congrArg Fin.val h
          exact Fin.ext (by omega)
        · intro t ht
          simp only [InS, Finset.mem_filter, Finset.mem_univ, true_and] at ht
          refine ⟨⟨t.val - p.val, by omega⟩, Finset.mem_univ _, Fin.ext (by dsimp only; omega)⟩
      rw [hbij, Finset.card_univ, Fintype.card_fin]
    have hcomp : InS.card + (Finset.univ.filter (fun t : Fin N => ¬ (p.val ≤ t.val ∧ t.val < p.val + L))).card = N := by
      have hdisj : Disjoint InS (Finset.univ.filter (fun t : Fin N => ¬ (p.val ≤ t.val ∧ t.val < p.val + L))) := by
        rw [Finset.disjoint_left]
        intro t h1 h2
        simp only [InS, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
        exact h2 h1
      have hunion : InS ∪ Finset.univ.filter (fun t : Fin N => ¬ (p.val ≤ t.val ∧ t.val < p.val + L)) = Finset.univ := by
        ext t
        simp only [InS, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        exact em _
      rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
    rw [Fintype.card_subtype]
    omega
  let ψ : (Fin N → ZMod 2) → (Fin L → ZMod 2) × (Out → ZMod 2) :=
    fun v => (Φ v, fun t => v t.1)
  have hψ_bij : Function.Bijective ψ := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, ?_⟩
    · intro v1 v2 hψ
      have hΦ : Φ v1 = Φ v2 := congrArg Prod.fst hψ
      have hOut : ∀ t : Out, v1 t.1 = v2 t.1 := fun t => congrFun (congrArg Prod.snd hψ) t
      have hall : ∀ k : ℕ, ∀ hk : k < N, v1 ⟨k, hk⟩ = v2 ⟨k, hk⟩ := by
        intro k
        induction k using Nat.strong_induction_on with
        | ind k ih =>
          intro hk
          by_cases hwin : p.val ≤ k ∧ k < p.val + L
          · let j : Fin L := ⟨k - p.val, by omega⟩
            have hj := congrFun hΦ j
            dsimp only [Φ] at hj
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p),
                ← Finset.add_sum_erase _ _ (Finset.mem_univ p)] at hj
            have hrest : ∑ i ∈ Finset.univ.erase p, c i * v1 ⟨j.val + i.val, by omega⟩ =
                ∑ i ∈ Finset.univ.erase p, c i * v2 ⟨j.val + i.val, by omega⟩ := by
              refine Finset.sum_congr rfl (fun i hi => ?_)
              have hne : i ≠ p := Finset.ne_of_mem_erase hi
              rcases lt_or_gt_of_ne hne with hlt | hgt
              · have hlt_k : j.val + i.val < k := by dsimp only [j]; omega
                rw [ih (j.val + i.val) hlt_k (by omega)]
              · rw [hc_gt i hgt, zero_mul, zero_mul]
            rw [hrest, hcp, one_mul, one_mul] at hj
            have heq_idx : (⟨j.val + p.val, by omega⟩ : Fin N) = ⟨k, hk⟩ := Fin.ext (by dsimp only [j]; omega)
            rw [heq_idx] at hj
            exact add_right_cancel hj
          · exact hOut ⟨⟨k, hk⟩, hwin⟩
      funext t
      exact hall t.val t.isLt
    · rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_fun,
          Fintype.card_fin, Fintype.card_fin, hOut_card, ZMod.card, ← pow_add]
      congr 1
      omega
  have hbij : (Finset.univ.filter (fun v : Fin N → ZMod 2 => Φ v = y)).card =
      (Finset.univ : Finset (Out → ZMod 2)).card := by
    apply Finset.card_bij (fun v _ => (ψ v).2)
    · intro _ _; exact Finset.mem_univ _
    · intro v1 hv1 v2 hv2 heq
      have h1 := (Finset.mem_filter.mp hv1).2
      have h2 := (Finset.mem_filter.mp hv2).2
      exact hψ_bij.1 (Prod.ext (h1.trans h2.symm) heq)
    · intro r _
      rcases hψ_bij.2 (y, r) with ⟨v, hv⟩
      refine ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, congrArg Prod.fst hv⟩, congrArg Prod.snd hv⟩
  rw [hbij, Finset.card_univ, Fintype.card_fun, hOut_card, ZMod.card]

private lemma card_bias_high_bound (k m : ℕ) (hk : 64 ≤ k) (hm : 512 * k ≤ m) :
    2 ^ (k / 16 + k + 2) *
      (Finset.univ.filter (fun y : Fin m → ZMod 2 => 15 * m < 28 * wt y)).card ≤ 2 ^ m := by
  let H : Finset (Fin m → ZMod 2) := Finset.univ.filter (fun y => 15 * m < 28 * wt y)
  have h28 : H.card ^ 28 * (15 ^ (15 * m) * 13 ^ (13 * m)) ≤ (28 ^ 28) ^ m := by
    have hstep1 : H.card ^ 28 * (15 ^ (15 * m) * 13 ^ (13 * m)) =
        ∑ _f : Fin 28 → H, (15 ^ (15 * m) * 13 ^ (13 * m)) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_coe, Fintype.card_fin, smul_eq_mul]
    have hstep2 : ∑ _f : Fin 28 → H, (15 ^ (15 * m) * 13 ^ (13 * m)) ≤
        ∑ f : Fin 28 → H, ∏ t : Fin 28, (15 ^ wt (f t).1 * 13 ^ (m - wt (f t).1)) := by
      refine Finset.sum_le_sum (fun f _ => ?_)
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum]
      let W : ℕ := ∑ t : Fin 28, wt (f t).1
      have hW_lo : 15 * m ≤ W := by
        have hsum_lo : ∑ _t : Fin 28, (15 * m) ≤ ∑ t : Fin 28, (28 * wt (f t).1) := by
          refine Finset.sum_le_sum (fun t _ => ?_)
          have ht := (Finset.mem_filter.mp (f t).2).2
          omega
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, ← Finset.mul_sum] at hsum_lo
        exact Nat.le_of_mul_le_mul_left hsum_lo (by decide)
      have hW_comp : W + ∑ t : Fin 28, (m - wt (f t).1) = 28 * m := by
        rw [← Finset.sum_add_distrib]
        calc ∑ t : Fin 28, (wt (f t).1 + (m - wt (f t).1))
            = ∑ _t : Fin 28, m := Finset.sum_congr rfl (fun t _ => by have := wt_le (f t).1; omega)
          _ = 28 * m := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      let rem : ℕ := ∑ t : Fin 28, (m - wt (f t).1)
      have hrem_eq : rem + (W - 15 * m) = 13 * m := by omega
      have hW_eq : W = 15 * m + (W - 15 * m) := by omega
      calc 15 ^ (15 * m) * 13 ^ (13 * m)
          = 15 ^ (15 * m) * (13 ^ rem * 13 ^ (W - 15 * m)) := by rw [← pow_add, hrem_eq]
        _ = 15 ^ (15 * m) * 13 ^ (W - 15 * m) * 13 ^ rem := by ring
        _ ≤ 15 ^ (15 * m) * 15 ^ (W - 15 * m) * 13 ^ rem := by
              refine Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by decide) _))
        _ = 15 ^ W * 13 ^ rem := by rw [← pow_add, ← hW_eq]
    have hstep3 : ∑ f : Fin 28 → H, ∏ t : Fin 28, (15 ^ wt (f t).1 * 13 ^ (m - wt (f t).1)) =
        (∑ y ∈ H, 15 ^ wt y * 13 ^ (m - wt y)) ^ 28 :=
      (sum_pow_eq_sum_prod H (fun y => 15 ^ wt y * 13 ^ (m - wt y)) 28).symm
    have hstep4 : ∑ y ∈ H, 15 ^ wt y * 13 ^ (m - wt y) ≤ 28 ^ m := by
      calc ∑ y ∈ H, 15 ^ wt y * 13 ^ (m - wt y)
          ≤ ∑ y : Fin m → ZMod 2, 15 ^ wt y * 13 ^ (m - wt y) :=
            Finset.sum_le_sum_of_subset (Finset.subset_univ H)
        _ = (15 + 13) ^ m := sum_pow_wt m 15 13
        _ = 28 ^ m := by norm_num
    calc H.card ^ 28 * (15 ^ (15 * m) * 13 ^ (13 * m))
        ≤ (∑ y ∈ H, 15 ^ wt y * 13 ^ (m - wt y)) ^ 28 := by rw [hstep1, ← hstep3]; exact hstep2
      _ ≤ (28 ^ m) ^ 28 := Nat.pow_le_pow_left hstep4 28
      _ = (28 ^ 28) ^ m := by rw [← pow_mul, Nat.mul_comm, pow_mul]
  have hbase : 28 ^ 28 * 16 ≤ 15 ^ 15 * 13 ^ 13 * 2 ^ 28 * 15 := by norm_num
  have hbase_m : (28 ^ 28) ^ m * 16 ^ m ≤ (15 ^ (15 * m) * 13 ^ (13 * m)) * (2 ^ m) ^ 28 * 15 ^ m := by
    have hp := Nat.pow_le_pow_left hbase m
    calc (28 ^ 28) ^ m * 16 ^ m
        = (28 ^ 28 * 16) ^ m := by rw [mul_pow]
      _ ≤ (15 ^ 15 * 13 ^ 13 * 2 ^ 28 * 15) ^ m := hp
      _ = (15 ^ 15) ^ m * (13 ^ 13) ^ m * (2 ^ 28) ^ m * 15 ^ m := by simp only [mul_pow]
      _ = (15 ^ (15 * m) * 13 ^ (13 * m)) * (2 ^ m) ^ 28 * 15 ^ m := by
            simp only [← pow_mul, Nat.mul_comm 28 m]
  have h1516 : 15 ^ 11 * 2 ≤ 16 ^ 11 := by norm_num
  have hpow42 : 15 ^ m * 2 ^ (42 * k) ≤ 16 ^ m := by
    have h462 : 11 * (42 * k) ≤ m := by omega
    have hp1 : 15 ^ (11 * (42 * k)) * 2 ^ (42 * k) ≤ 16 ^ (11 * (42 * k)) := by
      calc 15 ^ (11 * (42 * k)) * 2 ^ (42 * k)
          = (15 ^ 11 * 2) ^ (42 * k) := by rw [mul_pow, ← pow_mul]
        _ ≤ (16 ^ 11) ^ (42 * k) := Nat.pow_le_pow_left h1516 (42 * k)
        _ = 16 ^ (11 * (42 * k)) := by rw [← pow_mul]
    have hp2 : 15 ^ (m - 11 * (42 * k)) ≤ 16 ^ (m - 11 * (42 * k)) :=
      Nat.pow_le_pow_left (by decide) _
    have hm_split : 11 * (42 * k) + (m - 11 * (42 * k)) = m := by omega
    calc 15 ^ m * 2 ^ (42 * k)
        = (15 ^ (11 * (42 * k)) * 2 ^ (42 * k)) * 15 ^ (m - 11 * (42 * k)) := by
            conv_lhs => rw [← hm_split, pow_add]
            ring
      _ ≤ 16 ^ (11 * (42 * k)) * 16 ^ (m - 11 * (42 * k)) := Nat.mul_le_mul hp1 hp2
      _ = 16 ^ m := by rw [← pow_add, hm_split]
  have hcomb : H.card ^ 28 * 2 ^ (42 * k) ≤ (2 ^ m) ^ 28 := by
    have hpos : 0 < (15 ^ (15 * m) * 13 ^ (13 * m)) * 16 ^ m := by positivity
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc H.card ^ 28 * 2 ^ (42 * k) * ((15 ^ (15 * m) * 13 ^ (13 * m)) * 16 ^ m)
        = (H.card ^ 28 * (15 ^ (15 * m) * 13 ^ (13 * m))) * 16 ^ m * 2 ^ (42 * k) := by ring
      _ ≤ (28 ^ 28) ^ m * 16 ^ m * 2 ^ (42 * k) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h28)
      _ ≤ ((15 ^ (15 * m) * 13 ^ (13 * m)) * (2 ^ m) ^ 28 * 15 ^ m) * 2 ^ (42 * k) :=
            Nat.mul_le_mul_right _ hbase_m
      _ = (2 ^ m) ^ 28 * (15 ^ (15 * m) * 13 ^ (13 * m)) * (15 ^ m * 2 ^ (42 * k)) := by ring
      _ ≤ (2 ^ m) ^ 28 * (15 ^ (15 * m) * 13 ^ (13 * m)) * 16 ^ m :=
            Nat.mul_le_mul_left _ hpow42
      _ = (2 ^ m) ^ 28 * ((15 ^ (15 * m) * 13 ^ (13 * m)) * 16 ^ m) := by ring
  have hexp : 28 * (k / 16 + k + 2) ≤ 42 * k := by omega
  have hpow_final : (2 ^ (k / 16 + k + 2) * H.card) ^ 28 ≤ (2 ^ m) ^ 28 := by
    calc (2 ^ (k / 16 + k + 2) * H.card) ^ 28
        = H.card ^ 28 * 2 ^ (28 * (k / 16 + k + 2)) := by
            rw [mul_pow, ← pow_mul, Nat.mul_comm 28, Nat.mul_comm]
      _ ≤ H.card ^ 28 * 2 ^ (42 * k) :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hexp)
      _ ≤ (2 ^ m) ^ 28 := hcomb
  exact nat_le_of_pow_le_pow_left (by decide : 28 ≠ 0) hpow_final

private lemma card_short_tail_bound (m g B : ℕ) (hg : g ≤ m) (hB : 0 < B) :
    (Finset.univ.filter (fun y : Fin m → ZMod 2 => wt y ≤ g)).card * B ^ m ≤
      (B + 1) ^ m * B ^ g := by
  let T : Finset (Fin m → ZMod 2) := Finset.univ.filter (fun y => wt y ≤ g)
  have hsum : T.card * B ^ (m - g) ≤ (B + 1) ^ m := by
    calc T.card * B ^ (m - g)
        = ∑ _y ∈ T, B ^ (m - g) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ y ∈ T, 1 ^ wt y * B ^ (m - wt y) := by
            refine Finset.sum_le_sum (fun y hy => ?_)
            rw [one_pow, one_mul]
            have hwy := (Finset.mem_filter.mp hy).2
            exact Nat.pow_le_pow_right hB (by omega)
      _ ≤ ∑ y : Fin m → ZMod 2, 1 ^ wt y * B ^ (m - wt y) :=
            Finset.sum_le_sum_of_subset (Finset.subset_univ T)
      _ = (1 + B) ^ m := sum_pow_wt m 1 B
      _ = (B + 1) ^ m := by rw [Nat.add_comm]
  have hm_eq : m - g + g = m := by omega
  calc T.card * B ^ m
      = (T.card * B ^ (m - g)) * B ^ g := by rw [Nat.mul_assoc, ← pow_add, hm_eq]
    _ ≤ (B + 1) ^ m * B ^ g := Nat.mul_le_mul_right _ hsum

private lemma card_short_product_bound (k m : ℕ) (hk : 64 ≤ k) (hm_lo : 512 * k ≤ m) (hm_hi : m ≤ 1024 * k) :
    let g := k / 32
    2 ^ (k / 16 + 2) *
      (Finset.univ.filter (fun S : Finset (Fin m) => 0 < S.card ∧ S.card ≤ g)).card *
      (Finset.univ.filter (fun z : Fin k → ZMod 2 => wt z ≤ g)).card ≤ 2 ^ k := by
  intro g
  let NS := (Finset.univ.filter (fun S : Finset (Fin m) => 0 < S.card ∧ S.card ≤ g)).card
  let Tm := (Finset.univ.filter (fun y : Fin m → ZMod 2 => wt y ≤ g)).card
  let Tk := (Finset.univ.filter (fun z : Fin k → ZMod 2 => wt z ≤ g)).card
  have hNS_le : NS ≤ Tm := by
    apply Finset.card_le_card_of_injOn (fun (S : Finset (Fin m)) (j : Fin m) => if j ∈ S then (1 : ZMod 2) else 0)
    · intro S hS
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
      have hwt_eq : wt (fun j : Fin m => if j ∈ S then (1 : ZMod 2) else 0) = S.card := by
        unfold wt
        congr 1
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases hj : j ∈ S
        · simp [hj]
        · simp [hj]
      rw [hwt_eq]
      exact hS.2
    · intro S1 _ S2 _ heq
      ext j
      have hj := congrFun heq j
      dsimp only at hj
      by_cases h1 : j ∈ S1 <;> by_cases h2 : j ∈ S2 <;> simp [h1, h2] at hj ⊢
  have hTm_step : Tm ^ 16 ≤ 2 ^ (4 * k + 208 * g) := by
    have h1 := card_short_tail_bound m g 8192 (by omega) (by decide)
    have h16 := Nat.pow_le_pow_left h1 16
    have h8193 : 8193 ^ 4096 ≤ 2 * 8192 ^ 4096 := by
      simpa only [show 2 * 4096 + 1 = 8193 from rfl, show 2 * 4096 = 8192 from rfl] using
        pow_half_le_two_mul 4096 (by decide)
    have hm16 : 16 * m ≤ 4096 * (4 * k) := by omega
    have h8193_m : 8193 ^ (16 * m) ≤ 2 ^ (4 * k) * 8192 ^ (16 * m) := by
      have hpos : 0 < 8192 ^ (4096 * (4 * k) - 16 * m) := by positivity
      refine Nat.le_of_mul_le_mul_right ?_ hpos
      have hsplit : 16 * m + (4096 * (4 * k) - 16 * m) = 4096 * (4 * k) := by omega
      calc 8193 ^ (16 * m) * 8192 ^ (4096 * (4 * k) - 16 * m)
          ≤ 8193 ^ (16 * m) * 8193 ^ (4096 * (4 * k) - 16 * m) :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by decide) _)
        _ = (8193 ^ 4096) ^ (4 * k) := by rw [← pow_add, hsplit, pow_mul]
        _ ≤ (2 * 8192 ^ 4096) ^ (4 * k) := Nat.pow_le_pow_left h8193 (4 * k)
        _ = 2 ^ (4 * k) * 8192 ^ (4096 * (4 * k)) := by rw [mul_pow, ← pow_mul]
        _ = 2 ^ (4 * k) * 8192 ^ (16 * m) * 8192 ^ (4096 * (4 * k) - 16 * m) := by
              rw [Nat.mul_assoc, ← pow_add, hsplit]
    have h8192_pow : (8192 ^ g) ^ 16 = 2 ^ (208 * g) := by
      have h8 : (8192 : ℕ) = 2 ^ 13 := by norm_num
      rw [h8, ← pow_mul, ← pow_mul]
      congr 1
      omega
    have hpos : 0 < 8192 ^ (16 * m) := by positivity
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc Tm ^ 16 * 8192 ^ (16 * m)
        = (Tm * 8192 ^ m) ^ 16 := by rw [mul_pow, ← pow_mul, Nat.mul_comm m 16]
      _ ≤ (8193 ^ m * 8192 ^ g) ^ 16 := h16
      _ = 8193 ^ (16 * m) * (8192 ^ g) ^ 16 := by rw [mul_pow, ← pow_mul, Nat.mul_comm m 16]
      _ ≤ (2 ^ (4 * k) * 8192 ^ (16 * m)) * 2 ^ (208 * g) := by
            rw [h8192_pow]; exact Nat.mul_le_mul_right _ h8193_m
      _ = 2 ^ (4 * k + 208 * g) * 8192 ^ (16 * m) := by rw [pow_add]; ring
  have hTk_step : Tk ^ 16 ≤ 2 ^ (k + 80 * g) := by
    have h1 := card_short_tail_bound k g 32 (by omega) (by decide)
    have h16 := Nat.pow_le_pow_left h1 16
    have h33 : 33 ^ 16 ≤ 2 * 32 ^ 16 := by
      simpa only [show 2 * 16 + 1 = 33 from rfl, show 2 * 16 = 32 from rfl] using
        pow_half_le_two_mul 16 (by decide)
    have h33_k : 33 ^ (16 * k) ≤ 2 ^ k * 32 ^ (16 * k) := by
      calc 33 ^ (16 * k)
          = (33 ^ 16) ^ k := by rw [pow_mul]
        _ ≤ (2 * 32 ^ 16) ^ k := Nat.pow_le_pow_left h33 k
        _ = 2 ^ k * 32 ^ (16 * k) := by rw [mul_pow, ← pow_mul]
    have h32_pow : (32 ^ g) ^ 16 = 2 ^ (80 * g) := by
      have h32 : (32 : ℕ) = 2 ^ 5 := by norm_num
      rw [h32, ← pow_mul, ← pow_mul]
      congr 1
      omega
    have hpos : 0 < 32 ^ (16 * k) := by positivity
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc Tk ^ 16 * 32 ^ (16 * k)
        = (Tk * 32 ^ k) ^ 16 := by rw [mul_pow, ← pow_mul, Nat.mul_comm k 16]
      _ ≤ (33 ^ k * 32 ^ g) ^ 16 := h16
      _ = 33 ^ (16 * k) * (32 ^ g) ^ 16 := by rw [mul_pow, ← pow_mul, Nat.mul_comm k 16]
      _ ≤ (2 ^ k * 32 ^ (16 * k)) * 2 ^ (80 * g) := by
            rw [h32_pow]; exact Nat.mul_le_mul_right _ h33_k
      _ = 2 ^ (k + 80 * g) * 32 ^ (16 * k) := by rw [pow_add]; ring
  have hpow16 : (2 ^ (k / 16 + 2) * NS * Tk) ^ 16 ≤ (2 ^ k) ^ 16 := by
    have hNS16 : NS ^ 16 ≤ 2 ^ (4 * k + 208 * g) :=
      le_trans (Nat.pow_le_pow_left hNS_le 16) hTm_step
    have hexp : 16 * (k / 16 + 2) + (4 * k + 208 * g) + (k + 80 * g) ≤ 16 * k := by omega
    calc (2 ^ (k / 16 + 2) * NS * Tk) ^ 16
        = 2 ^ (16 * (k / 16 + 2)) * NS ^ 16 * Tk ^ 16 := by
            rw [mul_pow, mul_pow, ← pow_mul, Nat.mul_comm (k / 16 + 2) 16]
      _ ≤ 2 ^ (16 * (k / 16 + 2)) * 2 ^ (4 * k + 208 * g) * 2 ^ (k + 80 * g) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ hNS16) hTk_step
      _ = 2 ^ (16 * (k / 16 + 2) + (4 * k + 208 * g) + (k + 80 * g)) := by rw [← pow_add, ← pow_add]
      _ ≤ 2 ^ (16 * k) := Nat.pow_le_pow_right (by decide) hexp
      _ = (2 ^ k) ^ 16 := by rw [Nat.mul_comm 16 k, pow_mul]
  exact nat_le_of_pow_le_pow_left (by decide : 16 ≠ 0) hpow16

lemma good_count :
    (∀ k m : ℕ, 64 ≤ k → 512*k ≤ m → m ≤ 1024*k →
  let F := ZMod 2
  let V := Fin k → F
  let Seed := Fin (2^(k+m-1))
  let win := fun (s : Seed) (j : Fin m) (i : Fin k) =>
    if s.val.testBit (j.val+i.val) then (1 : F) else 0
  let g := k/32
  let good := fun s : Seed =>
    (∀ a : V, a ≠ 0 →
      let w := ((Finset.univ : Finset (Fin m)).filter (fun j =>
        (∑ i : Fin k, a i * win s j i) = 1)).card
      13*m ≤ 28*w ∧ 28*w ≤ 15*m) ∧
    (∀ S : Finset (Fin m), 0 < S.card → S.card ≤ g →
      let w := ((Finset.univ : Finset (Fin k)).filter (fun i =>
        (∑ j ∈ S, win s j i) = 1)).card
      g < w ∧ w+g < k)
  2^(k/16)*((Finset.univ : Finset Seed).filter (fun s => ¬ good s)).card ≤ 2^(k+m-1)) := by
  intro k m hk hm_lo hm_hi
  dsimp only
  let F := ZMod 2
  let V := Fin k → F
  let N := k + m - 1
  let Seed := Fin (2 ^ N)
  let win : Seed → Fin m → Fin k → F := fun s j i =>
    if s.val.testBit (j.val + i.val) then (1 : F) else 0
  let g := k / 32
  let toBits : Seed → (Fin N → F) := fun s t =>
    if s.val.testBit t.val then (1 : F) else 0
  have htoBits_bij : Function.Bijective toBits := card_toBits_bijective N
  let good := fun s : Seed =>
    (∀ a : V, a ≠ 0 →
      let w := ((Finset.univ : Finset (Fin m)).filter (fun j =>
        (∑ i : Fin k, a i * win s j i) = 1)).card
      13 * m ≤ 28 * w ∧ 28 * w ≤ 15 * m) ∧
    (∀ S : Finset (Fin m), 0 < S.card → S.card ≤ g →
      let w := ((Finset.univ : Finset (Fin k)).filter (fun i =>
        (∑ j ∈ S, win s j i) = 1)).card
      g < w ∧ w + g < k)
  let badA : V → Finset Seed := fun a =>
    Finset.univ.filter (fun s =>
      let w := ((Finset.univ : Finset (Fin m)).filter (fun j =>
        (∑ i : Fin k, a i * win s j i) = 1)).card
      ¬ (13 * m ≤ 28 * w ∧ 28 * w ≤ 15 * m))
  let badS : Finset (Fin m) → Finset Seed := fun S =>
    Finset.univ.filter (fun s =>
      let w := ((Finset.univ : Finset (Fin k)).filter (fun i =>
        (∑ j ∈ S, win s j i) = 1)).card
      ¬ (g < w ∧ w + g < k))
  let Aset : Finset V := Finset.univ.filter (fun a : V => a ≠ 0)
  let Sset : Finset (Finset (Fin m)) := Finset.univ.filter (fun S : Finset (Fin m) => 0 < S.card ∧ S.card ≤ g)
  have hsub : Finset.univ.filter (fun s : Seed => ¬ good s) ⊆
      Aset.biUnion badA ∪ Sset.biUnion badS := by
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, good, not_and_or,
      not_forall] at hs
    rw [Finset.mem_union]
    rcases hs with ⟨a, ha, hbad⟩ | ⟨S, hS1, hS2, hbad⟩
    · left
      rw [Finset.mem_biUnion]
      exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ s, not_and_or.mpr hbad⟩⟩
    · right
      rw [Finset.mem_biUnion]
      exact ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_univ S, hS1, hS2⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ s, not_and_or.mpr hbad⟩⟩
  let Hbias : Finset (Fin m → F) := Finset.univ.filter (fun y => 15 * m < 28 * wt y)
  let Lbias : Finset (Fin m → F) := Finset.univ.filter (fun y => 28 * wt y < 13 * m)
  have hLbias_eq : Lbias.card = Hbias.card := by
    apply Finset.card_bij (fun (y : Fin m → F) _ j => y j + 1)
    · intro y hy
      simp only [Lbias, Hbias, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      rw [wt_add_one y]
      have := wt_le y
      omega
    · intro y1 _ y2 _ heq
      funext j
      have hj := congrFun heq j
      exact add_right_cancel hj
    · intro y hy
      refine ⟨fun j => y j + 1, ?_, ?_⟩
      · simp only [Lbias, Hbias, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
        rw [wt_add_one y]
        have := wt_le y
        omega
      · funext j
        dsimp only
        rw [add_assoc, zmod2_add_self, add_zero]
  have hbadA_card : ∀ a ∈ Aset, (badA a).card ≤ 2 * Hbias.card * 2 ^ (k - 1) := by
    intro a ha
    have ha0 : a ≠ 0 := (Finset.mem_filter.mp ha).2
    let φA : Seed → (Fin m → F) := fun s j => ∑ i : Fin k, a i * win s j i
    have hmaps : ∀ s ∈ badA a, φA s ∈ Lbias ∪ Hbias := by
      intro s hs
      have hbad := (Finset.mem_filter.mp hs).2
      simp only [Finset.mem_union, Lbias, Hbias, Finset.mem_filter, Finset.mem_univ, true_and]
      change ¬ (13 * m ≤ 28 * wt (φA s) ∧ 28 * wt (φA s) ≤ 15 * m) at hbad
      omega
    have hfiber : ∀ y : Fin m → F, ((badA a).filter (fun s => φA s = y)).card ≤ 2 ^ (k - 1) := by
      intro y
      have hle1 : ((badA a).filter (fun s => φA s = y)).card ≤
          (Finset.univ.filter (fun s : Seed => φA s = y)).card :=
        Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
      have heq2 : (Finset.univ.filter (fun s : Seed => φA s = y)).card =
          (Finset.univ.filter (fun v : Fin N → F =>
            (fun j : Fin m => ∑ i : Fin k, a i * v ⟨j.val + i.val, by omega⟩) = y)).card := by
        apply Finset.card_bij (fun s _ => toBits s)
        · intro s hs
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
          exact hs
        · intro s1 _ s2 _ h; exact htoBits_bij.1 h
        · intro v hv
          rcases htoBits_bij.2 v with ⟨s, hs⟩
          refine ⟨s, ?_, hs⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
          rw [← hs] at hv
          exact hv
      rw [heq2] at hle1
      have hfib := card_shift_linear_fiber k m (by omega) (by omega) a ha0 y
      rw [hfib] at hle1
      exact hle1
    calc (badA a).card
        = ∑ y ∈ Lbias ∪ Hbias, ((badA a).filter (fun s => φA s = y)).card := by
            rw [Finset.card_eq_sum_card_fiberwise hmaps]
      _ ≤ ∑ _y ∈ Lbias ∪ Hbias, 2 ^ (k - 1) := Finset.sum_le_sum (fun y _ => hfiber y)
      _ = (Lbias ∪ Hbias).card * 2 ^ (k - 1) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ (Lbias.card + Hbias.card) * 2 ^ (k - 1) :=
            Nat.mul_le_mul_right _ (Finset.card_union_le Lbias Hbias)
      _ = 2 * Hbias.card * 2 ^ (k - 1) := by rw [hLbias_eq]; ring
  let TkSet : Finset (Fin k → F) := Finset.univ.filter (fun z => wt z ≤ g)
  let HkSet : Finset (Fin k → F) := Finset.univ.filter (fun z => k ≤ wt z + g)
  have hHk_eq : HkSet.card = TkSet.card := by
    apply Finset.card_bij (fun (z : Fin k → F) _ i => z i + 1)
    · intro z hz
      simp only [HkSet, TkSet, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      rw [wt_add_one z]
      have := wt_le z
      omega
    · intro z1 _ z2 _ heq
      funext i
      exact add_right_cancel (congrFun heq i)
    · intro z hz
      refine ⟨fun i => z i + 1, ?_, ?_⟩
      · simp only [HkSet, TkSet, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
        rw [wt_add_one z]
        have := wt_le z
        omega
      · funext i
        dsimp only
        rw [add_assoc, zmod2_add_self, add_zero]
  have hbadS_card : ∀ S ∈ Sset, (badS S).card ≤ 2 * TkSet.card * 2 ^ (m - 1) := by
    intro S hS
    have hSpos : 0 < S.card := (Finset.mem_filter.mp hS).2.1
    let cS : Fin m → F := fun j => if j ∈ S then 1 else 0
    have hcS0 : cS ≠ 0 := by
      intro hc
      rcases Finset.card_pos.mp hSpos with ⟨j, hj⟩
      have h0 := congrFun hc j
      simp [cS, hj] at h0
    let φS : Seed → (Fin k → F) := fun s i => ∑ j ∈ S, win s j i
    have hmaps : ∀ s ∈ badS S, φS s ∈ TkSet ∪ HkSet := by
      intro s hs
      have hbad := (Finset.mem_filter.mp hs).2
      simp only [Finset.mem_union, TkSet, HkSet, Finset.mem_filter, Finset.mem_univ, true_and]
      change ¬ (g < wt (φS s) ∧ wt (φS s) + g < k) at hbad
      omega
    have hfiber : ∀ z : Fin k → F, ((badS S).filter (fun s => φS s = z)).card ≤ 2 ^ (m - 1) := by
      intro z
      have hle1 : ((badS S).filter (fun s => φS s = z)).card ≤
          (Finset.univ.filter (fun s : Seed => φS s = z)).card :=
        Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
      have hN_comm : m + k - 1 = N := by omega
      have heq2 : (Finset.univ.filter (fun s : Seed => φS s = z)).card =
          (Finset.univ.filter (fun v : Fin (m + k - 1) → F =>
            (fun i : Fin k => ∑ j : Fin m, cS j * v ⟨i.val + j.val, by omega⟩) = z)).card := by
        apply Finset.card_bij (fun s _ t => toBits s ⟨t.val, by omega⟩)
        · intro s hs
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
          rw [← hs]
          funext i
          dsimp only [φS, cS, win, toBits]
          have hsum_eq : ∑ j : Fin m, (if j ∈ S then (1 : F) else 0) *
              (if s.val.testBit (i.val + j.val) then (1 : F) else 0) =
              ∑ j ∈ S, (if s.val.testBit (j.val + i.val) then (1 : F) else 0) := by
            rw [← Finset.sum_subset (Finset.subset_univ S)]
            · refine Finset.sum_congr rfl (fun j hj => ?_)
              simp only [hj, ↓reduceIte, one_mul, Nat.add_comm i.val j.val]
            · intro j _ hj
              simp only [hj, ↓reduceIte, zero_mul]
          exact hsum_eq
        · intro s1 _ s2 _ h
          apply htoBits_bij.1
          funext t
          exact congrFun h ⟨t.val, by omega⟩
        · intro v hv
          rcases htoBits_bij.2 (fun t : Fin N => v ⟨t.val, by omega⟩) with ⟨s, hs⟩
          refine ⟨s, ?_, ?_⟩
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
            rw [← hv]
            funext i
            dsimp only [φS, cS, win]
            have hsum_eq : ∑ j ∈ S, (if s.val.testBit (j.val + i.val) then (1 : F) else 0) =
                ∑ j : Fin m, (if j ∈ S then (1 : F) else 0) * v ⟨i.val + j.val, by omega⟩ := by
              rw [← Finset.sum_subset (Finset.subset_univ S)]
              · refine Finset.sum_congr rfl (fun j hj => ?_)
                have hbit := congrFun hs ⟨j.val + i.val, by omega⟩
                dsimp only [toBits] at hbit
                have hidx : (⟨j.val + i.val, by omega⟩ : Fin (m + k - 1)) = ⟨i.val + j.val, by omega⟩ :=
                  Fin.ext (Nat.add_comm j.val i.val)
                rw [hidx] at hbit
                simp only [hj, ↓reduceIte, one_mul, hbit]
              · intro j _ hj
                simp only [hj, ↓reduceIte, zero_mul]
            exact hsum_eq
          · funext t
            exact congrFun hs ⟨t.val, by omega⟩
      rw [heq2] at hle1
      have hfib := card_shift_linear_fiber m k (by omega) (by omega) cS hcS0 z
      rw [hfib] at hle1
      exact hle1
    calc (badS S).card
        = ∑ z ∈ TkSet ∪ HkSet, ((badS S).filter (fun s => φS s = z)).card := by
            rw [Finset.card_eq_sum_card_fiberwise hmaps]
      _ ≤ ∑ _z ∈ TkSet ∪ HkSet, 2 ^ (m - 1) := Finset.sum_le_sum (fun z _ => hfiber z)
      _ = (TkSet ∪ HkSet).card * 2 ^ (m - 1) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ (TkSet.card + HkSet.card) * 2 ^ (m - 1) :=
            Nat.mul_le_mul_right _ (Finset.card_union_le TkSet HkSet)
      _ = 2 * TkSet.card * 2 ^ (m - 1) := by rw [hHk_eq]; ring
  have hA_total : (Aset.biUnion badA).card ≤ 2 ^ k * (2 * Hbias.card * 2 ^ (k - 1)) := by
    calc (Aset.biUnion badA).card
        ≤ ∑ a ∈ Aset, (badA a).card := Finset.card_biUnion_le
      _ ≤ ∑ _a ∈ Aset, (2 * Hbias.card * 2 ^ (k - 1)) := Finset.sum_le_sum hbadA_card
      _ = Aset.card * (2 * Hbias.card * 2 ^ (k - 1)) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ 2 ^ k * (2 * Hbias.card * 2 ^ (k - 1)) := by
            refine Nat.mul_le_mul_right _ ?_
            calc Aset.card ≤ (Finset.univ : Finset V).card := Finset.card_filter_le _ _
              _ = 2 ^ k := by simp [V, F, Fintype.card_fin, ZMod.card]
  have hS_total : (Sset.biUnion badS).card ≤ Sset.card * (2 * TkSet.card * 2 ^ (m - 1)) := by
    calc (Sset.biUnion badS).card
        ≤ ∑ S ∈ Sset, (badS S).card := Finset.card_biUnion_le
      _ ≤ ∑ _S ∈ Sset, (2 * TkSet.card * 2 ^ (m - 1)) := Finset.sum_le_sum hbadS_card
      _ = Sset.card * (2 * TkSet.card * 2 ^ (m - 1)) := by rw [Finset.sum_const, smul_eq_mul]
  have htotal : (Finset.univ.filter (fun s : Seed => ¬ good s)).card ≤
      2 ^ k * (2 * Hbias.card * 2 ^ (k - 1)) + Sset.card * (2 * TkSet.card * 2 ^ (m - 1)) :=
    le_trans (Finset.card_le_card hsub)
      (le_trans (Finset.card_union_le _ _) (Nat.add_le_add hA_total hS_total))
  have hboundA : 2 * (2 ^ (k / 16) * (2 ^ k * (2 * Hbias.card * 2 ^ (k - 1)))) ≤ 2 ^ (k + m - 1) := by
    have hb := card_bias_high_bound k m hk hm_lo
    have hpow_eq : 2 ^ m * 2 ^ (k - 1) = 2 ^ (k + m - 1) := by
      rw [← pow_add]
      congr 1
      omega
    calc 2 * (2 ^ (k / 16) * (2 ^ k * (2 * Hbias.card * 2 ^ (k - 1))))
        = (2 ^ (k / 16 + k + 2) * Hbias.card) * 2 ^ (k - 1) := by
            simp only [pow_add]
            ring
      _ ≤ 2 ^ m * 2 ^ (k - 1) := Nat.mul_le_mul_right _ hb
      _ = 2 ^ (k + m - 1) := hpow_eq
  have hboundS : 2 * (2 ^ (k / 16) * (Sset.card * (2 * TkSet.card * 2 ^ (m - 1)))) ≤ 2 ^ (k + m - 1) := by
    have hs := card_short_product_bound k m hk hm_lo hm_hi
    have hpow_eq : 2 ^ k * 2 ^ (m - 1) = 2 ^ (k + m - 1) := by
      rw [← pow_add]
      congr 1
      omega
    calc 2 * (2 ^ (k / 16) * (Sset.card * (2 * TkSet.card * 2 ^ (m - 1))))
        = (2 ^ (k / 16 + 2) * Sset.card * TkSet.card) * 2 ^ (m - 1) := by
            simp only [pow_add]
            ring
      _ ≤ 2 ^ k * 2 ^ (m - 1) := Nat.mul_le_mul_right _ hs
      _ = 2 ^ (k + m - 1) := hpow_eq
  have h2mul : 2 * (2 ^ (k / 16) * (Finset.univ.filter (fun s : Seed => ¬ good s)).card) ≤
      2 * 2 ^ (k + m - 1) := by
    calc 2 * (2 ^ (k / 16) * (Finset.univ.filter (fun s : Seed => ¬ good s)).card)
        ≤ 2 * (2 ^ (k / 16) * (2 ^ k * (2 * Hbias.card * 2 ^ (k - 1)) +
            Sset.card * (2 * TkSet.card * 2 ^ (m - 1)))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ htotal)
      _ = 2 * (2 ^ (k / 16) * (2 ^ k * (2 * Hbias.card * 2 ^ (k - 1)))) +
          2 * (2 ^ (k / 16) * (Sset.card * (2 * TkSet.card * 2 ^ (m - 1)))) := by ring
      _ ≤ 2 ^ (k + m - 1) + 2 ^ (k + m - 1) := Nat.add_le_add hboundA hboundS
      _ = 2 * 2 ^ (k + m - 1) := by ring
  exact Nat.le_of_mul_le_mul_left h2mul (by decide)


lemma exists_of_count {α : Type} [Fintype α] [Nonempty α] (p : α → Prop)
    [DecidablePred p] (c : ℕ) (hc : 2 ≤ c)
    (h : c * (Finset.univ.filter (fun s => ¬ p s)).card ≤ Fintype.card α) :
    ∃ s, p s := by
  by_contra hne
  have hall : Finset.univ.filter (fun s => ¬ p s) = Finset.univ :=
    Finset.filter_true_of_mem (fun s _ => not_exists.mp hne s)
  rw [hall, Finset.card_univ] at h
  have hpos : 0 < Fintype.card α := Fintype.card_pos
  nlinarith

lemma exists_bias_tape (k m : ℕ) (hk : 64 ≤ k) (hmlo : 512 * k ≤ m)
    (hmhi : m ≤ 1024 * k) :
    ∃ s : Fin (2 ^ (k + m - 1)),
      ∀ a : Fin k → ZMod 2, a ≠ 0 →
        14 * |∑ j : Fin m, (if dotProduct a
          (fun i : Fin k => if s.val.testBit (j.val + i.val) then (1 : ZMod 2) else 0) = 0
            then (1 : ℤ) else -1)| ≤ (m : ℤ) := by
  classical
  have htwo : 2 ≤ 2 ^ (k / 16) := by
    calc 2 = 2 ^ 1 := by norm_num
         _ ≤ 2 ^ (k / 16) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : Nonempty (Fin (2 ^ (k + m - 1))) := ⟨⟨0, by positivity⟩⟩
  obtain ⟨s, hA, _⟩ := exists_of_count _ (2 ^ (k / 16)) htwo
    (by rw [Fintype.card_fin]; exact good_count k m hk hmlo hmhi)
  refine ⟨s, ?_⟩
  intro a ha
  let v : Fin m → Fin k → ZMod 2 := fun j i =>
    if s.val.testBit (j.val + i.val) then 1 else 0
  let w := ((Finset.univ : Finset (Fin m)).filter (fun j => dotProduct a (v j) = 1)).card
  have hw : 13 * m ≤ 28 * w ∧ 28 * w ≤ 15 * m := hA a ha
  have hs : (∑ j : Fin m, (if dotProduct a (v j) = 0 then (1 : ℤ) else -1)) =
      (m : ℤ) - 2 * (w : ℤ) := by
    have ht : ∀ j : Fin m, (if dotProduct a (v j) = 0 then (1 : ℤ) else -1) =
        1 - 2 * (if dotProduct a (v j) = 1 then (1 : ℤ) else 0) := by
      intro j
      rcases zmod2_eq_zero_or_one (dotProduct a (v j)) with h | h <;> simp [h]
    simp_rw [ht, Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp [w]
  change 14 * |∑ j : Fin m, (if dotProduct a (v j) = 0 then (1 : ℤ) else -1)| ≤ (m : ℤ)
  rw [hs]
  have hlo : 13 * (m : ℤ) ≤ 28 * (w : ℤ) := by exact_mod_cast hw.1
  have hhi : 28 * (w : ℤ) ≤ 15 * (m : ℤ) := by exact_mod_cast hw.2
  rcases le_total ((m : ℤ) - 2 * (w : ℤ)) 0 with hneg | hpos
  · rw [abs_of_nonpos hneg]; linarith
  · rw [abs_of_nonneg hpos]; linarith

end PEqualNP.Outside.L_meta_29742_aux.Tape


namespace PEqualNP.Outside.L_meta_29742_aux.H6

open PEqualNP.CircuitLowerBounds

abbrev F := ZMod 2
abbrev Vec (n : ℕ) := Fin n → F
abbrev Form (n : ℕ) := Vec n →ₗ[F] F

def bit (b : Bool) : F := if b then 1 else 0

def IsAffine {Z : Type*} {m : ℕ} (f : Z → Vec m → Bool) : Prop :=
  ∃ (l : Form m) (a : Z → F), ∀ z x, bit (f z x) = l x + a z

def goodGate (g : Gate) : Prop :=
  g.inputs.length ≤ 2 ∧ (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))

noncomputable def charged (g : Gate) : Bool :=
  @decide ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) (Classical.propDecidable _)

def gateValue (g : Gate) (W : Z → Vec m → List Bool) (z : Z) (x : Vec m) : Bool :=
  g.op.eval (g.inputs.map fun i => (W z x).getD i false)

lemma charged_eq_true (g : Gate) :
    charged g = true ↔ (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 := by
  unfold charged
  exact @decide_eq_true_iff _ (Classical.propDecidable _)

private lemma gateAffine_const {Z : Type*} {m : ℕ} (f : Z → Bool) :
    IsAffine (fun z (_ : Vec m) => f z) := by
  exact ⟨0, fun z => bit (f z), by simp⟩

private lemma gateBit_not (a : Bool) :
    bit (GateOp.not.eval [a]) = 1 + bit a := by
  cases a <;> decide

private lemma gateBit_mod1 (a : Bool) :
    bit ((GateOp.mod 2).eval [a]) = 1 + bit a := by
  cases a <;> decide

private lemma gateBit_mod2 (a b : Bool) :
    bit ((GateOp.mod 2).eval [a, b]) = 1 + bit a + bit b := by
  cases a <;> cases b <;> decide

private lemma gateBit_and1 (a : Bool) : GateOp.and.eval [a] = a := by
  cases a <;> rfl

private lemma gateBit_or1 (a : Bool) : GateOp.or.eval [a] = a := by
  cases a <;> rfl

lemma gate_affine {Z : Type*} {m : ℕ} {g : Gate} {W : Z → Vec m → List Bool}
    (hg : goodGate g) (hc : charged g = false)
    (hW : ∀ i : ℕ, IsAffine (fun z x => (W z x).getD i false)) :
    IsAffine (gateValue g W) := by
  rcases g with ⟨op, inputs⟩
  rcases hg with ⟨hlen, hop⟩
  change inputs.length ≤ 2 at hlen
  have hnot : ¬ ((op = .and ∨ op = .or) ∧ inputs.length = 2) := by
    intro h
    have ht := (charged_eq_true ⟨op, inputs⟩).2 h
    rw [hc] at ht
    contradiction
  change op = .and ∨ op = .or ∨ op = .mod 2 ∨ (op = .not ∧ inputs.length = 1) at hop
  rcases inputs with _ | ⟨i, _ | ⟨j, _ | ⟨k, rest⟩⟩⟩
  · exact gateAffine_const (fun _ => op.eval [])
  · rcases hop with rfl | rfl | rfl | ⟨rfl, _⟩
    · change IsAffine (fun z x => GateOp.and.eval [(W z x).getD i false])
      simpa only [gateBit_and1] using hW i
    · change IsAffine (fun z x => GateOp.or.eval [(W z x).getD i false])
      simpa only [gateBit_or1] using hW i
    · obtain ⟨l, a, ha⟩ := hW i
      refine ⟨l, fun z => 1 + a z, fun z x => ?_⟩
      change bit ((GateOp.mod 2).eval [(W z x).getD i false]) = _
      rw [gateBit_mod1, ha]
      ring
    · obtain ⟨l, a, ha⟩ := hW i
      refine ⟨l, fun z => 1 + a z, fun z x => ?_⟩
      change bit (GateOp.not.eval [(W z x).getD i false]) = _
      rw [gateBit_not, ha]
      ring
  · have hi : (op = .and ∨ op = .or) → False := fun h => hnot ⟨h, rfl⟩
    rcases hop with h | h | rfl | ⟨_, hn⟩
    · exact (hi (Or.inl h)).elim
    · exact (hi (Or.inr h)).elim
    · obtain ⟨l, a, ha⟩ := hW i
      obtain ⟨r, c, hc⟩ := hW j
      refine ⟨l + r, fun z => 1 + a z + c z, fun z x => ?_⟩
      change bit ((GateOp.mod 2).eval [(W z x).getD i false, (W z x).getD j false]) = _
      rw [gateBit_mod2, ha, hc, LinearMap.add_apply]
      ring
    · simp at hn
  · simp only [List.length_cons] at hlen
    omega

private lemma gateBit_and2 (a b : Bool) :
    bit (GateOp.and.eval [a, b]) = bit a * bit b + 0 * (bit a + bit b) := by
  cases a <;> cases b <;> decide

private lemma gateBit_or2 (a b : Bool) :
    bit (GateOp.or.eval [a, b]) = bit a * bit b + 1 * (bit a + bit b) := by
  cases a <;> cases b <;> decide

private lemma gateBinary_cut {Z : Type*} {n : ℕ} {f g : Z → Vec (n + 1) → Bool}
    {v : Z → Vec (n + 1) → Bool} {ε : F}
    (hv : ∀ z x, bit (v z x) = bit (f z x) * bit (g z x) + ε * (bit (f z x) + bit (g z x)))
    (hf : IsAffine f) (hg : IsAffine g) :
    ∃ ℓ : Form (n + 1), ∃ c : Z → F, ℓ ≠ 0 ∧
      ∀ b : F, ∃ l : Form (n + 1), ∃ a : Z → F,
        ∀ z x, ℓ x + c z = b → bit (v z x) = l x + a z := by
  obtain ⟨l, a, ha⟩ := hf
  obtain ⟨r, c, hc⟩ := hg
  by_cases hl : l = 0
  · by_cases hr : r = 0
    · let p : Form (n + 1) := LinearMap.proj (0 : Fin (n + 1))
      have hp : p ≠ 0 := by
        intro h
        have he := DFunLike.congr_fun h (fun _ => (1 : F))
        have hf : (1 : F) = 0 := he
        exact one_ne_zero hf
      refine ⟨p, fun _ => 0, hp, fun _ => ⟨0, fun z => a z * c z + ε * (a z + c z), ?_⟩⟩
      intro z x _
      simp [hv, ha, hc, hl, hr]
    · refine ⟨r, c, hr, fun b => ⟨(b + ε) • l, fun z => a z * b + ε * (a z + b), ?_⟩⟩
      intro z x h
      rw [hv, ha, hc, h, LinearMap.smul_apply, smul_eq_mul]
      ring
  · refine ⟨l, a, hl, fun b => ⟨(b + ε) • r, fun z => b * c z + ε * (b + c z), ?_⟩⟩
    intro z x h
    rw [hv, ha, hc, h, LinearMap.smul_apply, smul_eq_mul]
    ring

lemma gate_affine_on_cut {Z : Type*} {m : ℕ} {g : Gate} {W : Z → Vec (m + 1) → List Bool}
    (hc : charged g = true)
    (hW : ∀ i : ℕ, IsAffine (fun z x => (W z x).getD i false)) :
    ∃ ℓ : Form (m + 1), ∃ c : Z → F, ℓ ≠ 0 ∧
      ∀ b : F, ∃ l : Form (m + 1), ∃ a : Z → F,
        ∀ z x, ℓ x + c z = b → bit (gateValue g W z x) = l x + a z := by
  obtain ⟨hop, hlen⟩ := (charged_eq_true g).1 hc
  rcases g with ⟨op, inputs⟩
  change op = .and ∨ op = .or at hop
  change inputs.length = 2 at hlen
  rcases inputs with _ | ⟨i, _ | ⟨j, _ | ⟨k, rest⟩⟩⟩
  · simp at hlen
  · simp at hlen
  · rcases hop with rfl | rfl
    · exact gateBinary_cut (fun z x => gateBit_and2 _ _) (hW i) (hW j)
    · exact gateBinary_cut (fun z x => gateBit_or2 _ _) (hW i) (hW j)
  · simp only [List.length_cons] at hlen
    omega

lemma wires_extend {Z : Type*} {m n : ℕ} {W : Z → Vec m → List Bool}
    {v : Z → Vec m → Bool} (hlen : ∀ z x, (W z x).length = n)
    (hW : ∀ i : ℕ, IsAffine (fun z x => (W z x).getD i false))
    (hv : IsAffine v) (i : ℕ) :
    IsAffine (fun z x => (W z x ++ [v z x]).getD i false) := by
  by_cases hi : i < n
  · have h : (fun z x => (W z x ++ [v z x]).getD i false) =
        (fun z x => (W z x).getD i false) := by
      funext z x
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by simpa [hlen] using hi)]
    simpa only [h] using hW i
  · by_cases he : i = n
    · subst i
      have h : (fun z x => (W z x ++ [v z x]).getD n false) = v := by
        funext z x
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp [hlen])]
        simp [hlen]
      simpa only [h] using hv
    · have h : (fun z x => (W z x ++ [v z x]).getD i false) = (fun _ _ => false) := by
        funext z x
        rw [List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by simp [hlen]; omega)]
        rfl
      rw [h]
      exact gateAffine_const (fun _ => false)

private lemma cut_pivot {m : ℕ} (ℓ : Form (m + 1)) (hℓ : ℓ ≠ 0) :
    ∃ j : Fin (m + 1), ℓ (Pi.single j 1) = 1 := by
  by_contra! h
  apply hℓ
  apply LinearMap.pi_ext
  intro j a
  have hj : ℓ (Pi.single j 1) = 0 := by
    exact (show ∀ t : F, t ≠ 1 → t = 0 by decide) _ (h j)
  have ha : (Pi.single j a : Vec (m + 1)) = a • Pi.single j 1 := by
    ext i
    by_cases hi : i = j
    · subst i
      simp
    · simp [Pi.single_eq_of_ne hi]
  rw [ha, map_smul, hj, smul_zero, LinearMap.zero_apply]

lemma cut_exists_split {m : ℕ} (ℓ : Form (m + 1)) (hℓ : ℓ ≠ 0) :
    ∃ E : (F × Vec m) ≃ₗ[F] Vec (m + 1), ∀ e x, ℓ (E (e, x)) = e := by
  classical
  obtain ⟨j, hj⟩ := cut_pivot ℓ hℓ
  let w : Vec (m + 1) := Pi.single j 1
  change ℓ w = 1 at hj
  let u := finSuccAboveEquiv j
  let drop : Vec (m + 1) →ₗ[F] Vec m :=
    { toFun := fun v i => v (u i).1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let p := ℓ.prod drop
  have hdw : drop w = 0 := by
    ext i
    exact Pi.single_eq_of_ne (u i).2 _
  have hinj : Function.Injective p := by
    intro x y hxy
    have hl : ℓ x = ℓ y := congrArg Prod.fst hxy
    have hd : drop x = drop y := congrArg Prod.snd hxy
    have hxy' : x - y = (x j - y j) • w := by
      ext i
      by_cases hi : i = j
      · subst i
        simp [w]
      · have he : x i = y i := by
          have h := congrFun hd (u.symm ⟨i, hi⟩)
          change x (u (u.symm ⟨i, hi⟩)).1 = y (u (u.symm ⟨i, hi⟩)).1 at h
          simpa only [Equiv.apply_symm_apply] using h
        simp [w, Pi.single_eq_of_ne hi, he]
    have hs := congrArg ℓ hxy'
    simp [map_sub, hl, hj] at hs
    apply sub_eq_zero.mp
    rw [hxy', ← hs, zero_smul]
  have hsurj : Function.Surjective p := by
    rintro ⟨e, x⟩
    let base : Vec (m + 1) := fun i => if hi : i = j then 0 else x (u.symm ⟨i, hi⟩)
    have hbase : drop base = x := by
      ext i
      change base (u i).1 = x i
      simp [base, dite_eq_right (u i).2]
    refine ⟨base + (e - ℓ base) • w, Prod.ext ?_ ?_⟩
    · change ℓ (base + (e - ℓ base) • w) = e
      simp [hj]
    · change drop (base + (e - ℓ base) • w) = x
      simp [hdw, hbase]
  let E := LinearEquiv.ofBijective p ⟨hinj, hsurj⟩
  refine ⟨E.symm, fun e x => ?_⟩
  exact congrArg Prod.fst (E.apply_symm_apply (e, x))

private def walshSign (x : F) : ℤ := if x = 0 then 1 else -1

private lemma walshSign_add_one (x : F) : walshSign (x + 1) = -walshSign x := by
  fin_cases x <;> decide

private lemma walshSign_agreement (q : Bool) (x : F) :
    walshSign (bit q - x) = (if q = decide (x = 1) then 2 else 0) - 1 := by
  cases q <;> fin_cases x <;> decide

private lemma walshSign_natAbs (x : F) : (walshSign x).natAbs = 1 := by
  fin_cases x <;> decide

private lemma walsh_eq_agreement {k : ℕ} (f : Vec k → Bool) (v : Vec k) :
    (∑ x : Vec k, walshSign (bit (f x) - dotProduct v x)) =
    2 * ((((Finset.univ : Finset (Vec k)).filter
      (fun x => f x = decide (dotProduct v x = 1))).card : ℕ) : ℤ) - (2:ℤ)^k := by
  simp_rw [walshSign_agreement]
  rw [Finset.sum_sub_distrib, ← Finset.sum_filter]
  simp [ZMod.card, mul_comm]

open Classical in
private lemma walshSign_sum {m : ℕ} (g : Form m) (c : F) :
    (∑ y : Vec m, walshSign (c + g y)).natAbs = if g = 0 then 2^m else 0 := by
  classical
  by_cases hg : g = 0
  · simp [hg, ZMod.card, Int.natAbs_mul, walshSign_natAbs]
  · rw [ite_eq_right hg]
    have hex : ∃ w : Vec m, g w ≠ 0 := by
      by_contra! h
      exact hg (LinearMap.ext fun x => h x)
    obtain ⟨w, hw⟩ := hex
    have hw' : g w = 1 := by
      have h01 (x : F) : x = 0 ∨ x = 1 := by
        fin_cases x
        · exact Or.inl rfl
        · exact Or.inr rfl
      rcases h01 (g w) with h | h
      · exact (hw h).elim
      · exact h
    have h := Equiv.sum_comp (Equiv.addRight w) fun y : Vec m => walshSign (c + g y)
    change (∑ y : Vec m, walshSign (c + g (y + w))) =
      ∑ y : Vec m, walshSign (c + g y) at h
    simp_rw [map_add, hw', ← add_assoc, walshSign_add_one, Finset.sum_neg_distrib] at h
    have hz : (∑ y : Vec m, walshSign (c + g y)) = 0 := by omega
    simp [hz]

private def walshRestriction {k m : ℕ} (L : Vec m →ₗ[F] Vec k) : Vec k →ₗ[F] Form m :=
  (Module.Dual.transpose L).comp (dotProductEquiv F (Fin k)).toLinearMap

private lemma walshRestriction_apply {k m : ℕ} (L : Vec m →ₗ[F] Vec k)
    (v : Vec k) (y : Vec m) : walshRestriction L v y = dotProduct v (L y) := rfl

private lemma walshRestriction_surjective {k m : ℕ} (L : Vec m →ₗ[F] Vec k)
    (R : Vec k →ₗ[F] Vec m) (hRL : Function.LeftInverse R L) :
    Function.Surjective (walshRestriction L) := by
  intro ℓ
  refine ⟨(dotProductEquiv F (Fin k)).symm (ℓ.comp R), ?_⟩
  apply LinearMap.ext
  intro y
  rw [walshRestriction_apply]
  change dotProductEquiv F (Fin k) ((dotProductEquiv F (Fin k)).symm (ℓ.comp R)) (L y) = ℓ y
  rw [LinearEquiv.apply_symm_apply, LinearMap.comp_apply, hRL y]

private lemma walshRestriction_ker_finrank {k b : ℕ} (hb : b ≤ k)
    (L : Vec (k-b) →ₗ[F] Vec k) (R : Vec k →ₗ[F] Vec (k-b))
    (hRL : Function.LeftInverse R L) : Module.finrank F (LinearMap.ker (walshRestriction L)) = b := by
  have hdim (n : ℕ) : Module.finrank F (Vec n) = n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have h := (walshRestriction L).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (walshRestriction_surjective L R hRL), finrank_top,
    ← (dotProductEquiv F (Fin (k-b))).finrank_eq, hdim, hdim] at h
  omega

lemma walshCover {k b : ℕ} {Z : Type*} (hb : b ≤ k) (f : Z → Vec k → Bool)
    (L : Fin (2^b) → Vec (k-b) →ₗ[F] Vec k)
    (R : Fin (2^b) → Vec k →ₗ[F] Vec (k-b))
    (hRL : ∀ i, Function.LeftInverse (R i) (L i))
    (p : Fin (2^b) → Z → Vec k) (ℓ : Fin (2^b) → Form (k-b))
    (a : Fin (2^b) → Z → F)
    (hf : ∀ i z y, bit (f z (p i z + L i y)) = ℓ i y + a i z)
    (hsum : ∀ z (h : Vec k → ℤ), ∑ x, h x = ∑ i, ∑ y, h (p i z + L i y)) :
    ∃ (D : Fin (2^b) → Submodule F (Vec k)) (aa : Fin (2^b) → Vec k),
      (∀ i, Module.finrank F (D i) = b) ∧
      ∀ z v,
        let H := ((Finset.univ : Finset (Vec k)).filter
          (fun x => f z x = decide (dotProduct v x = 1))).card
        2^b * (2 * (H : ℤ) - (2:ℤ)^k).natAbs ≤
          2^k * ((Finset.univ : Finset (Fin (2^b))).filter
            (fun i => @decide (v-aa i ∈ D i) (Classical.propDecidable _))).card := by
  classical
  choose aa haa using fun i => walshRestriction_surjective (L i) (R i) (hRL i) (ℓ i)
  refine ⟨fun i => LinearMap.ker (walshRestriction (L i)), aa,
    fun i => walshRestriction_ker_finrank hb (L i) (R i) (hRL i), ?_⟩
  intro z v
  dsimp only
  rw [← walsh_eq_agreement (f z) v, hsum z]
  let W (i : Fin (2^b)) : ℤ :=
    ∑ y, walshSign (bit (f z (p i z + L i y)) - dotProduct v (p i z + L i y))
  change 2^b * (∑ i, W i).natAbs ≤ _
  have hW (i : Fin (2^b)) : (W i).natAbs =
      if v - aa i ∈ LinearMap.ker (walshRestriction (L i)) then 2^(k-b) else 0 := by
    have hterm (y : Vec (k-b)) :
        bit (f z (p i z + L i y)) - dotProduct v (p i z + L i y) =
          (a i z - dotProduct v (p i z)) + (ℓ i - walshRestriction (L i) v) y := by
      rw [hf, dotProduct_add, LinearMap.sub_apply, walshRestriction_apply]
      abel
    simp_rw [W, hterm, walshSign_sum]
    have hc : ℓ i - walshRestriction (L i) v = 0 ↔
        v - aa i ∈ LinearMap.ker (walshRestriction (L i)) := by
      rw [LinearMap.mem_ker, map_sub, haa, sub_eq_zero, sub_eq_zero]
      exact eq_comm
    simp only [hc]
  have hbound : (∑ i, W i).natAbs ≤ ∑ i, (W i).natAbs := by
    exact Int.natAbs_sum_le _ _
  refine (Nat.mul_le_mul_left _ hbound).trans_eq ?_
  simp_rw [hW, decide_eq_true_eq]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rw [mul_comm _ (2^(k-b)), ← mul_assoc, ← pow_add, Nat.add_sub_of_le hb]
  rfl

private def Frame (k : ℕ) (Z : Type) (m : ℕ) :=
  Σ linear : Vec m →ₗ[F] Vec k,
    Σ retract : Vec k →ₗ[F] Vec m,
      { _offset : Z → Vec k // Function.LeftInverse retract linear }

private def Frame.linear (T : Frame k Z m) : Vec m →ₗ[F] Vec k := T.1

private def Frame.retract (T : Frame k Z m) : Vec k →ₗ[F] Vec m := T.2.1

private lemma Frame.left_inv (T : Frame k Z m) : Function.LeftInverse T.retract T.linear :=
  T.2.2.property

private def Frame.offset (T : Frame k Z m) : Z → Vec k := T.2.2.val

private def Frame.point (T : Frame k Z m) (z : Z) (x : Vec m) : Vec k :=
  T.offset z + T.linear x

private def cutLinear (E : (F × Vec m) ≃ₗ[F] Vec (m+1)) : Vec m →ₗ[F] Vec (m+1) :=
  E.toLinearMap.comp (LinearMap.inr F F (Vec m))

private lemma split_add (E : (F × Vec m) ≃ₗ[F] Vec (m+1)) (a : F) (x : Vec m) :
    E (a,x) = E (a,0) + E (0,x) := by
  rw [← map_add]
  simp

private def Frame.cut (T : Frame k Z (m+1)) (E : (F × Vec m) ≃ₗ[F] Vec (m+1))
    (c : Z → F) (e : F) : Frame k Z m :=
  ⟨T.linear.comp (cutLinear E),
    (LinearMap.snd F F (Vec m)).comp (E.symm.toLinearMap.comp T.retract),
    (fun z => T.offset z + T.linear (E (e+c z,0))), by
      intro x
      change (E.symm (T.retract (T.linear (E (0,x))))).2 = x
      rw [T.left_inv,E.symm_apply_apply]⟩

private lemma Frame.cut_point (T : Frame k Z (m+1)) (E : (F × Vec m) ≃ₗ[F] Vec (m+1))
    (c : Z → F) (e : F) (z : Z) (x : Vec m) :
    (T.cut E c e).point z x = T.point z (E (e+c z,x)) := by
  change T.offset z + T.linear (E (e+c z,0)) + T.linear (E (0,x)) = _
  simp only [Frame.point, split_add E (e+c z) x, map_add, add_assoc]

private lemma sum_cut (E : (F × Vec m) ≃ₗ[F] Vec (m+1)) (a : F)
    (f : Vec (m+1) → ℤ) :
    (∑ q, f q) = ∑ e : F, ∑ x : Vec m, f (E (e+a,x)) := by
  let Q := (Equiv.prodCongr (Equiv.addRight a) (Equiv.refl (Vec m))).trans E.toEquiv
  rw [← Equiv.sum_comp Q f]
  rw [Fintype.sum_prod_type]
  rfl

private def consEquiv (m : ℕ) : F × Vec m ≃ Vec (m+1) where
  toFun p := Fin.cons p.1 p.2
  invFun q := (q 0, Fin.tail q)
  left_inv p := by simp
  right_inv q := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

private lemma sum_cons (f : Vec (m+1) → ℤ) :
    (∑ q, f q) = ∑ e : F, ∑ x : Vec m, f (Fin.cons e x) := by
  rw [← Equiv.sum_comp (consEquiv m) f, Fintype.sum_prod_type]
  rfl

private lemma affine_reparam (E : (F × Vec m) ≃ₗ[F] Vec (m+1)) (c : Z → F)
    (e : F) (l : Form (m+1)) (a : Z → F)
    (f : Z → Vec (m+1) → Bool)
    (h : ∀ z y, bit (f z (E (e+c z,y))) = l (E (e+c z,y)) + a z) :
    IsAffine (fun z y => f z (E (e+c z,y))) := by
  refine ⟨l.comp (cutLinear E),fun z => l (E (e+c z,0)) + a z, ?_⟩
  intro z y
  rw [h,split_add E (e+c z) y,map_add]
  change l (E (e+c z,0)) + l (E (0,y)) + a z = l (E (0,y)) + (l (E (e+c z,0)) + a z)
  ac_rfl

private def step (g : Gate) (w : List Bool) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def finalValue (gs : List Gate) (W : Z → Vec k → List Bool)
    (out : ℕ) (z : Z) (x : Vec k) : Bool :=
  (gs.foldl (fun w g => step g w) (W z x)).getD out false

private def Cell (k : ℕ) (Z : Type) (m : ℕ) :=
  Frame k Z m × Form m × (Z → F)

private def Cell.toFrame (T : Cell k Z m) : Frame k Z m := T.1

private def Cell.slope (T : Cell k Z m) : Form m := T.2.1

private def Cell.phase (T : Cell k Z m) : Z → F := T.2.2

private def Cell.linear (T : Cell k Z m) : Vec m →ₗ[F] Vec k := T.toFrame.linear

private def Cell.retract (T : Cell k Z m) : Vec k →ₗ[F] Vec m := T.toFrame.retract

private def Cell.offset (T : Cell k Z m) : Z → Vec k := T.toFrame.offset

private lemma Cell.left_inv (T : Cell k Z m) : Function.LeftInverse T.retract T.linear :=
  T.toFrame.left_inv

private lemma partition (gs : List Gate) (hg : ∀ g ∈ gs, goodGate g)
    (s : ℕ) (hs : gs.countP charged = s) (T : Frame k Z (m+s))
    (W : Z → Vec k → List Bool) (out n : ℕ) (hwlength : ∀ z x, (W z x).length = n)
    (hwaffine : ∀ i : ℕ, IsAffine (fun z x => (W z (T.point z x)).getD i false)) :
    ∃ cells : Vec s → Cell k Z m,
      (∀ i z x, bit (finalValue gs W out z ((cells i).toFrame.point z x)) =
        (cells i).slope x + (cells i).phase z) ∧
      ∀ z (f : Vec k → ℤ),
        (∑ x, f (T.point z x)) = ∑ i, ∑ x, f ((cells i).toFrame.point z x) := by
  induction gs generalizing s n W out with
  | nil =>
      have hzero : s = 0 := by simpa using hs.symm
      clear hs
      subst s
      obtain ⟨l,a,ha⟩ := hwaffine out
      refine ⟨fun _ => ⟨T,l,a⟩, ?_, ?_⟩
      · intro i z x
        exact ha z x
      · intro z f
        have hcard : Fintype.card (Vec 0) = 1 := by simp [Vec,F]
        change (∑ x, f (T.point z x)) = ∑ _ : Vec 0, ∑ x, f (T.point z x)
        simp only [Finset.sum_const,Finset.card_univ,hcard,one_nsmul]
  | cons g gs ih =>
      have hgate := hg g (by simp)
      have hgs (a : Gate) (ha : a ∈ gs) := hg a (by simp [ha])
      let W' z x := step g (W z x)
      have hW' (z : Z) (x : Vec k) : (W' z x).length = n+1 := by
        simp [W',step,hwlength]
      cases hch : charged g
      · have hs' : gs.countP charged = s := by simpa [List.countP_cons,hch] using hs
        let localW := fun z x => W z (T.point z x)
        have ha := gate_affine (g := g) (W := localW) hgate hch hwaffine
        have hall : ∀ i, IsAffine (fun z x => (W' z (T.point z x)).getD i false) :=
          fun i => wires_extend (W := localW) (fun z x => hwlength z _) hwaffine ha i
        obtain ⟨cells,hcells,hsum⟩ := ih hgs s hs' T W' out (n+1) hW' hall
        exact ⟨cells,hcells,hsum⟩
      · have hs' : gs.countP charged + 1 = s := by simpa [List.countP_cons,hch] using hs
        cases s with
        | zero => omega
        | succ s =>
          have htail : gs.countP charged = s := by omega
          let localW := fun z x => W z (T.point z x)
          obtain ⟨l,c,hl,hcut⟩ := gate_affine_on_cut (g := g) (W := localW) hch hwaffine
          obtain ⟨E,hE⟩ := cut_exists_split l hl
          let C (e : F) := T.cut E c e
          have hchild (e : F) :
              ∀ i, IsAffine (fun z x => (W' z ((C e).point z x)).getD i false) := by
            let childW := fun z x => W z ((C e).point z x)
            have ha (i : ℕ) : IsAffine (fun z x => (childW z x).getD i false) := by
              obtain ⟨l,a,ha⟩ := hwaffine i
              have hv := affine_reparam E c e l a
                (fun z x => (W z (T.point z x)).getD i false) (fun z y => ha z _)
              simpa only [childW,C,Frame.cut_point] using hv
            obtain ⟨l',a',hcut'⟩ := hcut e
            have hv := affine_reparam E c e l' a' (gateValue g localW) (by
              intro z y
              apply hcut'
              rw [hE]
              exact (by decide : ∀ x y : F, x+y+y=x) _ _)
            have hb : IsAffine (gateValue g childW) := by
              change IsAffine (fun z y => gateValue g childW z y)
              simpa only [gateValue,childW,C,Frame.cut_point,localW] using hv
            exact wires_extend (W := childW) (fun z x => hwlength z _) ha hb
          have hbranch (e : F) := ih hgs s htail (C e) W' out (n+1) hW' (hchild e)
          choose cells he hsum using hbranch
          refine ⟨(fun i : Vec (s+1) => cells (i 0) (Fin.tail i)),?_,?_⟩
          · intro i z x
            exact he _ _ z x
          · intro z f
            calc
              (∑ x, f (T.point z x)) =
                  ∑ e : F, ∑ x, f ((C e).point z x) := by
                erw [sum_cut E (c z) (fun x => f (T.point z x))]
                apply Finset.sum_congr rfl
                intro e _
                apply Finset.sum_congr rfl
                intro x _
                rw [show (C e).point z x = T.point z (E (e+c z,x)) from T.cut_point E c e z x]
              _ = ∑ e : F, ∑ i : Vec s, ∑ x, f ((cells e i).toFrame.point z x) := by
                exact Finset.sum_congr rfl fun e _ => hsum e z f
              _ = ∑ i : Vec (s+1), ∑ x, f ((cells (i 0) (Fin.tail i)).toFrame.point z x) := by
                rw [sum_cons]
                simp

private def inputs (z : Fin t → Bool) (x : Vec k) : List Bool :=
  List.ofFn (fun j : Fin k => decide (x j = 1)) ++ List.ofFn z

private lemma bit_decide (x : F) : bit (decide (x = 1)) = x :=
  (by decide : ∀ y : F, bit (decide (y = 1)) = y) x

private lemma inputs_affine {k t : ℕ} (i : ℕ) :
    IsAffine (fun (z : Fin t → Bool) (x : Vec k) => (inputs z x).getD i false) := by
  by_cases hi : i < k
  · refine ⟨LinearMap.proj ⟨i,hi⟩,fun _ => 0,?_⟩
    intro z x
    change bit ((inputs z x).getD i false) = _
    rw [inputs,List.getD_eq_getElem?_getD,List.getElem?_append_left (by simp [hi])]
    simp only [List.getElem?_ofFn, dif_pos hi, Option.getD_some, bit_decide,
      LinearMap.proj_apply, add_zero]
  · refine ⟨0,fun z => bit ((List.ofFn z).getD (i-k) false),?_⟩
    intro z x
    change bit ((inputs z x).getD i false) = _
    rw [inputs,List.getD_eq_getElem?_getD,List.getElem?_append_right (by simp; omega)]
    simp [List.getD_eq_getElem?_getD]

private def standard (h : m = k) : Frame k Z m := by
  subst m
  exact ⟨LinearMap.id,LinearMap.id,fun _ => 0,fun _ => rfl⟩

private lemma standard_affine {m k t : ℕ} (h : m = k) (i : ℕ) :
    IsAffine (fun (z : Fin t → Bool) x => (inputs z ((standard h).point z x)).getD i false) := by
  subst m
  simpa [standard,Frame.point,Frame.offset,Frame.linear] using inputs_affine (k := k) (t := t) i

private lemma standard_sum {m k : ℕ} {Z : Type} (h : m = k) (z : Z) (f : Vec k → ℤ) :
    (∑ x, f ((standard h).point z x)) = ∑ x, f x := by
  subst m
  simp [standard,Frame.point,Frame.offset,Frame.linear]

private def boundAt (b : ℕ) (f : Z → Vec k → Bool) : Prop :=
  ∃ (D : Fin (2^b) → Submodule F (Vec k)) (a : Fin (2^b) → Vec k),
    (∀ i, Module.finrank F (D i) = b) ∧
    ∀ z v,
      let H := ((Finset.univ : Finset (Vec k)).filter (fun x =>
        f z x = decide (dotProduct v x = 1))).card
      2^b * (2*(H : ℤ)-(2:ℤ)^k).natAbs ≤
        2^k * ((Finset.univ : Finset (Fin (2^b))).filter (fun l =>
          @decide (v-a l ∈ D l) (Classical.propDecidable _))).card

private lemma fullCover (f : Z → Vec k → Bool) : boundAt k f := by
  classical
  refine ⟨fun _ => ⊤,fun _ => 0,fun i => ?_,?_⟩
  · rw [finrank_top, Module.finrank_fin_fun]
  · intro z v
    dsimp only
    rw [← walsh_eq_agreement (f z) v]
    have h : (∑ x : Vec k, walshSign (bit (f z x) - dotProduct v x)).natAbs ≤ 2^k := by
      calc
        _ ≤ ∑ x : Vec k, (walshSign (bit (f z x) - dotProduct v x)).natAbs :=
          Int.natAbs_sum_le _ _
        _ = _ := by simp [walshSign_natAbs,ZMod.card]
    simpa [Submodule.mem_top, Fintype.card_fin] using Nat.mul_le_mul_left (2^k) h

private lemma circuit_cover {k t s : ℕ} (C : Circuit) (hs : C.gates.countP charged = s)
    (hle : s ≤ k) (hgood : ∀ g ∈ C.gates, goodGate g) :
    boundAt s (fun (z : Fin t → Bool) (x : Vec k) => C.eval (inputs z x)) := by
  classical
  let m := k-s
  have hm : m+s=k := Nat.sub_add_cancel hle
  let T : Frame k (Fin t → Bool) (m+s) := standard hm
  obtain ⟨C₀,hC,hsum⟩ := partition C.gates hgood s hs T inputs C.output (k+t)
    (by intro z x; simp [inputs]) (fun i => standard_affine hm i)
  let ind : Vec s ≃ Fin (2^s) := Fintype.equivFinOfCardEq (by simp [Vec,F,ZMod.card])
  let C₁ (j : Fin (2^s)) := C₀ (ind.symm j)
  apply walshCover hle (fun (z : Fin t → Bool) (x : Vec k) => C.eval (inputs z x))
    (fun i => (C₁ i).linear) (fun i => (C₁ i).retract) (fun i => (C₁ i).left_inv)
    (fun i => (C₁ i).offset) (fun i => (C₁ i).slope) (fun i => (C₁ i).phase)
  · intro i z y
    exact hC (ind.symm i) z y
  · intro z f
    calc
      (∑ x, f x) = ∑ x, f (T.point z x) := (standard_sum hm z f).symm
      _ = ∑ i, ∑ x, f ((C₀ i).toFrame.point z x) := hsum z f
      _ = ∑ i : Fin (2^s), ∑ x, f ((C₁ i).toFrame.point z x) :=
        (Equiv.sum_comp ind.symm _).symm

lemma standard_affine_general {m k : ℕ} {Z : Type}
    (h : m = k) (W : Z → Vec k → List Bool)
    (hwaffine : ∀ i : ℕ, IsAffine (fun z x => (W z x).getD i false)) (i : ℕ) :
    IsAffine (fun z x => (W z ((standard h).point z x)).getD i false) := by
  subst m
  simpa [standard,Frame.point,Frame.offset,Frame.linear] using hwaffine i

lemma circuit_cover_affine {k s r : ℕ} {Z : Type} (C : Circuit)
    (hs : C.gates.countP charged = s) (hle : s ≤ k)
    (hgood : ∀ g ∈ C.gates, goodGate g)
    (W : Z → Vec k → List Bool)
    (hwlength : ∀ z x, (W z x).length = r)
    (hwaffine : ∀ i : ℕ, IsAffine (fun z x => (W z x).getD i false)) :
    boundAt s (fun z x => C.eval (W z x)) := by
  classical
  let m := k-s
  have hm : m+s=k := Nat.sub_add_cancel hle
  let T : Frame k Z (m+s) := standard hm
  have ha (i : ℕ) : IsAffine (fun z x => (W z (T.point z x)).getD i false) := by
    exact standard_affine_general hm W hwaffine i
  obtain ⟨C₀,hC,hsum⟩ := partition C.gates hgood s hs T W C.output r hwlength ha
  let ind : Vec s ≃ Fin (2^s) := Fintype.equivFinOfCardEq (by simp [Vec,F,ZMod.card])
  let C₁ (j : Fin (2^s)) := C₀ (ind.symm j)
  apply walshCover hle (fun z x => C.eval (W z x))
    (fun i => (C₁ i).linear) (fun i => (C₁ i).retract) (fun i => (C₁ i).left_inv)
    (fun i => (C₁ i).offset) (fun i => (C₁ i).slope) (fun i => (C₁ i).phase)
  · intro i z y
    exact hC (ind.symm i) z y
  · intro z f
    calc
      (∑ x, f x) = ∑ x, f (T.point z x) := (standard_sum hm z f).symm
      _ = ∑ i, ∑ x, f ((C₀ i).toFrame.point z x) := hsum z f
      _ = ∑ i : Fin (2^s), ∑ x, f ((C₁ i).toFrame.point z x) :=
        (Equiv.sum_comp ind.symm _).symm

lemma affine_inputs {k n t : ℕ} (B : Vec n →ₗ[F] Vec k) (p : Vec k) (i : ℕ) :
    IsAffine (fun (z : Fin t → Bool) (y : Vec n) => (inputs z (p+B y)).getD i false) := by
  by_cases hi : i < k
  · refine ⟨(LinearMap.proj ⟨i,hi⟩).comp B,fun _ => p ⟨i,hi⟩,?_⟩
    intro z y
    change bit ((inputs z (p+B y)).getD i false) = _
    rw [inputs,List.getD_eq_getElem?_getD,List.getElem?_append_left (by simp [hi])]
    simp only [List.getElem?_ofFn, dif_pos hi, Option.getD_some, bit_decide,
      LinearMap.comp_apply, LinearMap.proj_apply, Pi.add_apply]
    exact add_comm _ _
  · refine ⟨0,fun z => bit ((List.ofFn z).getD (i-k) false),?_⟩
    intro z y
    change bit ((inputs z (p+B y)).getD i false) = _
    rw [inputs,List.getD_eq_getElem?_getD,List.getElem?_append_right (by simp; omega)]
    simp [List.getD_eq_getElem?_getD]

lemma affine_circuit_cover {k n t : ℕ} (B : Vec n →ₗ[F] Vec k) (p : Vec k)
    (C : Circuit) (hgood : ∀ g ∈ C.gates, goodGate g) :
    boundAt (min (C.gates.countP charged) n)
      (fun (z : Fin t → Bool) (y : Vec n) => C.eval (inputs z (p+B y))) := by
  classical
  by_cases h : C.gates.countP charged ≤ n
  · rw [Nat.min_eq_left h]
    exact circuit_cover_affine (r := k+t) C rfl h hgood (fun z y => inputs z (p+B y))
      (by intro z y; simp [inputs]) (affine_inputs B p)
  · rw [Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge h))]
    exact fullCover _


end PEqualNP.Outside.L_meta_29742_aux.H6


namespace PEqualNP.Outside.L_meta_29742_aux.H7
abbrev F2 := ZMod 2
def chi (a : F2) : ℤ := if a = 0 then 1 else -1

lemma zmod2_eq_zero_or_one (a : F2) : a = 0 ∨ a = 1 := by
  decide +revert

lemma zmod2_add_self (a : F2) : a + a = 0 := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;> decide

lemma zmod2_sub_eq_add (a b : F2) : a - b = a + b := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;>
  rcases zmod2_eq_zero_or_one b with rfl | rfl <;> decide

lemma chi_zero : chi 0 = 1 := by decide

lemma chi_one : chi 1 = -1 := by decide

lemma chi_add (a b : F2) : chi (a + b) = chi a * chi b := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;>
  rcases zmod2_eq_zero_or_one b with rfl | rfl <;> decide

lemma chi_mul_self (a : F2) : chi a * chi a = 1 := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;> decide

lemma abs_chi (a : F2) : |chi a| = 1 := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;> decide

def boolToF2 (b : Bool) : F2 := if b then 1 else 0

lemma decide_boolToF2 (b : Bool) : decide (boolToF2 b = 1) = b := by
  cases b <;> decide

lemma boolToF2_decide (a : F2) : boolToF2 (decide (a = 1)) = a := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;> decide

lemma boolToF2_not (b : Bool) : boolToF2 (!b) = 1 + boolToF2 b := by
  cases b <;> decide

lemma boolToF2_xor (a b : Bool) : boolToF2 (a ^^ b) = boolToF2 a + boolToF2 b := by
  cases a <;> cases b <;> decide

lemma boolToF2_and (a b : Bool) : boolToF2 (a && b) = boolToF2 a * boolToF2 b := by
  cases a <;> cases b <;> decide

lemma dotProduct_add_left {n : ℕ} (x y z : Fin n → F2) :
    dotProduct (x + y) z = dotProduct x z + dotProduct y z := by
  simp only [dotProduct, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma dotProduct_add_right {n : ℕ} (x y z : Fin n → F2) :
    dotProduct x (y + z) = dotProduct x y + dotProduct x z := by
  simp only [dotProduct, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma dotProduct_zero_left {n : ℕ} (z : Fin n → F2) : dotProduct 0 z = 0 := by
  simp [dotProduct]

lemma dotProduct_zero_right {n : ℕ} (x : Fin n → F2) : dotProduct x 0 = 0 := by
  simp [dotProduct]

lemma sum_chi_dotProduct {d : ℕ} (u : Fin d → F2) :
    (∑ y : Fin d → F2, chi (dotProduct y u)) = if u = 0 then (2 ^ d : ℤ) else 0 := by
  split_ifs with hu
  · subst hu
    simp only [dotProduct_zero_right, chi_zero, Finset.sum_const, Finset.card_univ,
      Fintype.card_fun, Fintype.card_fin, ZMod.card, nsmul_eq_mul, mul_one, Nat.cast_pow,
      Nat.cast_ofNat]
  · have hne : ∃ i : Fin d, u i ≠ 0 := by
      by_contra h
      push Not at h
      exact hu (funext h)
    rcases hne with ⟨i₀, hi₀⟩
    have hui : u i₀ = 1 := by
      rcases zmod2_eq_zero_or_one (u i₀) with h0 | h1
      · exact (hi₀ h0).elim
      · exact h1
    let e : Fin d → F2 := fun i => if i = i₀ then 1 else 0
    have heu : dotProduct e u = 1 := by
      simp only [dotProduct, e, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true, hui]
    have hshift : (∑ y : Fin d → F2, chi (dotProduct (y + e) u)) =
        ∑ y : Fin d → F2, chi (dotProduct y u) :=
      Fintype.sum_equiv (Equiv.addRight e) _ _ (fun _ => rfl)
    have hneg : (∑ y : Fin d → F2, chi (dotProduct (y + e) u)) =
        -(∑ y : Fin d → F2, chi (dotProduct y u)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [dotProduct_add_left, heu, chi_add, chi_one]
      ring
    linarith

lemma funct (k h : ℕ) (A : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin h → ZMod 2))
    (hA : Function.Surjective A) (u : Fin h → ZMod 2) (hu : u ≠ 0) :
    ∃ a : Fin k → ZMod 2, a ≠ 0 ∧ ∀ x, ∑ c, u c * A x c = ∑ i, a i * x i := by
  refine ⟨fun i => ∑ c, u c * A (fun j => if i = j then 1 else 0) c, ?_, ?_⟩
  · intro h0
    have hf : ∀ x, ∑ c, u c * A x c = 0 := by
      intro x
      have e : ∀ x : Fin k → ZMod 2, ∑ c, u c * A x c =
          ∑ i, (∑ c, u c * A (fun j => if i = j then 1 else 0) c) * x i := by
        intro x
        conv_lhs => rw [LinearMap.pi_apply_eq_sum_univ A x]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun c _ => ?_))
        ring
      rw [e]
      simp [congrFun h0]
    obtain ⟨c0, hc0⟩ : ∃ c0, u c0 = 1 := by
      by_contra hn
      simp only [not_exists] at hn
      apply hu
      funext c
      rcases zmod2_eq_zero_or_one (u c) with h | h
      · simpa using h
      · exact absurd h (hn c)
    obtain ⟨x, hx⟩ := hA (fun c => if c0 = c then 1 else 0)
    have := hf x
    rw [hx] at this
    simp [hc0] at this
  · intro x
    conv_lhs => rw [LinearMap.pi_apply_eq_sum_univ A x]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun c _ => ?_))
    ring

lemma smallBias_fiber_count (k m h : ℕ) (v : Fin m → Fin k → F2)
    (hbias : ∀ a : Fin k → F2, a ≠ 0 →
      14 * |∑ j : Fin m, chi (dotProduct a (v j))| ≤ (m : ℤ))
    (A : (Fin k → F2) →ₗ[F2] (Fin h → F2))
    (hAs : Function.Surjective A) (z : Fin h → F2) :
    14 * 2 ^ h * (Finset.univ.filter (fun j : Fin m => A (v j) = z)).card ≤
      (2 ^ h + 13) * m := by
  classical
  have hz : ∀ y : Fin h → F2, y + z = 0 ↔ y = z := by
    intro y
    constructor
    · intro hy
      funext c
      have hc := congrFun hy c
      simp only [Pi.add_apply, Pi.zero_apply] at hc
      rcases zmod2_eq_zero_or_one (y c) with h0 | h1 <;>
        rcases zmod2_eq_zero_or_one (z c) with h2 | h3 <;>
        simp_all
    · intro hy
      subst y
      funext c
      exact zmod2_add_self (z c)
  have hfilter : (2 ^ h : ℤ) *
      ((Finset.univ.filter (fun j : Fin m => A (v j) = z)).card : ℤ) =
      ∑ u : Fin h → F2, chi (dotProduct u z) *
        ∑ j : Fin m, chi (dotProduct u (A (v j))) := by
    have e1 : (2 ^ h : ℤ) *
        ((Finset.univ.filter (fun j : Fin m => A (v j) = z)).card : ℤ) =
        ∑ j : Fin m, (if A (v j) = z then (2 ^ h : ℤ) else 0) := by
      rw [Finset.card_filter]
      push_cast
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by split_ifs <;> simp)
    rw [e1]
    have e2 : ∀ j : Fin m, (if A (v j) = z then (2 ^ h : ℤ) else 0) =
        ∑ u : Fin h → F2, chi (dotProduct u z) * chi (dotProduct u (A (v j))) := by
      intro j
      have ho := sum_chi_dotProduct (A (v j) + z)
      simp only [hz] at ho
      rw [← ho]
      refine Finset.sum_congr rfl (fun u _ => ?_)
      rw [dotProduct_add_right, chi_add, mul_comm]
    rw [Finset.sum_congr rfl (fun j _ => e2 j), Finset.sum_comm]
    exact Finset.sum_congr rfl (fun u _ => by rw [Finset.mul_sum])
  have hbound : ∀ u : Fin h → F2,
      14 * (chi (dotProduct u z) * ∑ j : Fin m, chi (dotProduct u (A (v j)))) ≤
        (m : ℤ) + if u = 0 then (13 : ℤ) * m else 0 := by
    intro u
    by_cases hu : u = 0
    · subst u
      simp [chi_zero]
      ring_nf
      exact le_rfl
    · rw [ite_eq_right hu, add_zero]
      obtain ⟨a, ha0, hfa⟩ := funct k h A hAs u hu
      have he : ∀ j : Fin m, dotProduct u (A (v j)) = dotProduct a (v j) :=
        fun j => hfa (v j)
      simp only [he]
      calc
        14 * (chi (dotProduct u z) * ∑ j : Fin m, chi (dotProduct a (v j))) ≤
            14 * |chi (dotProduct u z) * ∑ j : Fin m, chi (dotProduct a (v j))| := by
          exact mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num)
        _ = 14 * |∑ j : Fin m, chi (dotProduct a (v j))| := by
          rw [abs_mul, abs_chi, one_mul]
        _ ≤ m := hbias a ha0
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun u _ => hbound u)
  rw [← Finset.mul_sum, ← hfilter, Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    ZMod.card, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hsum
  have hres : (14 : ℤ) * 2 ^ h *
      ((Finset.univ.filter (fun j : Fin m => A (v j) = z)).card : ℤ) ≤
      (2 ^ h + 13) * (m : ℤ) := by nlinarith [hsum]
  exact_mod_cast hres

lemma smallBias_of_counts (k m : ℕ) (v : Fin m → Fin k → F2)
    (a : Fin k → F2)
    (hlo : 13 * m ≤ 28 * (Finset.univ.filter
      (fun j : Fin m => dotProduct a (v j) = 1)).card)
    (hhi : 28 * (Finset.univ.filter
      (fun j : Fin m => dotProduct a (v j) = 1)).card ≤ 15 * m) :
    14 * |∑ j : Fin m, chi (dotProduct a (v j))| ≤ (m : ℤ) := by
  classical
  set w := (Finset.univ.filter (fun j : Fin m => dotProduct a (v j) = 1)).card with hw
  have hsum : ∑ j : Fin m, chi (dotProduct a (v j)) = (m : ℤ) - 2 * (w : ℤ) := by
    have he : ∀ j : Fin m, chi (dotProduct a (v j)) =
        1 - 2 * (if dotProduct a (v j) = 1 then (1 : ℤ) else 0) := by
      intro j
      rcases zmod2_eq_zero_or_one (dotProduct a (v j)) with h | h <;> simp [chi, h]
    rw [Finset.sum_congr rfl (fun j _ => he j), Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [Finset.sum_boole, hw]
    simp
  rw [hsum]
  have hlo' : (13 * m : ℤ) ≤ 28 * w := by exact_mod_cast hlo
  have hhi' : (28 * w : ℤ) ≤ 15 * m := by exact_mod_cast hhi
  rcases le_total 0 ((m : ℤ) - 2 * (w : ℤ)) with h | h
  · rw [abs_of_nonneg h]
    nlinarith
  · rw [abs_of_nonpos h]
    nlinarith





lemma h7_flat_mass_mono
    (p q C m : Nat) (hpq : p ≤ q)
    (hbound : 14 * q * C ≤ (q + 13) * m) :
    14 * p * C ≤ (p + 13) * m := by
  by_cases hsmall : 14 * C ≤ m
  · calc
      14 * p * C = p * (14 * C) := by
        simp only [← Nat.mul_assoc, Nat.mul_comm p 14]
      _ ≤ p * m := Nat.mul_le_mul_left p hsmall
      _ ≤ (p + 13) * m := Nat.mul_le_mul_right m (by omega)
  · have hd : (14 * C - m) + m = 14 * C :=
      Nat.sub_add_cancel (by omega)
    have hqd := congrArg (fun z : Nat => q * z) hd
    have hpd := congrArg (fun z : Nat => p * z) hd
    rw [Nat.mul_add] at hqd hpd
    have hbound' : q * (14 * C) ≤ q * m + 13 * m := by
      simpa only [Nat.add_mul, ← Nat.mul_assoc, Nat.mul_comm q 14] using hbound
    have hdelta : q * (14 * C - m) ≤ 13 * m := by omega
    have hmono := Nat.mul_le_mul_right (14 * C - m) hpq
    have hresult : p * (14 * C) ≤ p * m + 13 * m := by omega
    simpa only [Nat.add_mul, ← Nat.mul_assoc, Nat.mul_comm p 14] using hresult

lemma h7_flat_mass_pow_mono
    (h d C m : Nat) (hhd : h ≤ d)
    (hbound : 14 * 2 ^ d * C ≤ (2 ^ d + 13) * m) :
    14 * 2 ^ h * C ≤ (2 ^ h + 13) * m := by
  exact h7_flat_mass_mono (2 ^ h) (2 ^ d) C m
    (Nat.pow_le_pow_of_le (by decide) hhd) hbound

lemma smallBias_flat_count {n m h : ℕ}
    (v : Fin m → Fin n → F2)
    (hbias : ∀ u : Fin n → F2, u ≠ 0 →
      14 * |∑ j : Fin m, chi (dotProduct u (v j))| ≤ (m : ℤ))
    (D : Submodule F2 (Fin n → F2)) (a : Fin n → F2)
    (hd : Module.finrank F2 D + h ≤ n) :
    14 * 2 ^ h * (Finset.univ.filter (fun j : Fin m => @decide (v j - a ∈ D) (Classical.propDecidable _))).card ≤
      (2 ^ h + 13) * m := by
  classical
  let d := Module.finrank F2 ((Fin n → F2) ⧸ D)
  have hdim : d + Module.finrank F2 D = n := by
    simpa only [d, Module.finrank_fin_fun] using D.finrank_quotient_add_finrank
  have hhd : h ≤ d := by omega
  let E := LinearEquiv.ofFinrankEq ((Fin n → F2) ⧸ D) (Fin d → F2)
    (R := F2) (by simp only [Module.finrank_fin_fun, d])
  let A := E.toLinearMap ∘ₗ D.mkQ
  have hA : Function.Surjective A := E.surjective.comp D.mkQ_surjective
  have hmass := smallBias_fiber_count n m d v hbias A hA (A a)
  have hcard : (Finset.univ.filter (fun j : Fin m => @decide (v j - a ∈ D) (Classical.propDecidable _))).card ≤
      (Finset.univ.filter (fun j : Fin m => A (v j) = A a)).card := by
    apply Finset.card_le_card
    intro j hj
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have hjD : v j - a ∈ D := of_decide_eq_true (Finset.mem_filter.mp hj).2
    have hzero : A (v j - a) = 0 := by
      change E (D.mkQ (v j - a)) = 0
      have hq : D.mkQ (v j - a) = 0 := (Submodule.Quotient.mk_eq_zero D).mpr hjD
      rw [hq, map_zero]
    exact sub_eq_zero.mp ((map_sub A (v j) a).symm.trans hzero)
  have hmass' : 14 * 2 ^ d *
      (Finset.univ.filter (fun j : Fin m => @decide (v j - a ∈ D) (Classical.propDecidable _))).card ≤ (2 ^ d + 13) * m :=
    (Nat.mul_le_mul_left _ hcard).trans hmass
  exact h7_flat_mass_pow_mono h d _ m hhd hmass'

end PEqualNP.Outside.L_meta_29742_aux.H7


namespace PEqualNP.Outside.L_meta_29742_aux.PhaseReview

lemma phase_abs_agreement {α : Type*} [Fintype α]
    (f : α → Bool) (g : α → ZMod 2) (b : ZMod 2) :
    (2 * (((Finset.univ : Finset α).filter (fun x =>
      f x = decide (g x + b = 1))).card : ℤ) - Fintype.card α).natAbs =
    (2 * (((Finset.univ : Finset α).filter (fun x =>
      f x = decide (g x = 1))).card : ℤ) - Fintype.card α).natAbs := by
  classical
  have hb : b = 0 ∨ b = 1 := by
    fin_cases b
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hb with rfl | rfl
  · simp
  · have hx (x : α) : (f x = decide (g x + 1 = 1)) ↔
        ¬ (f x = decide (g x = 1)) := by
      generalize f x = u
      generalize g x = v
      cases u <;> fin_cases v <;> decide
    simp_rw [hx]
    have hc := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset α)) (p := fun x => f x = decide (g x = 1))
    have hz : (2 * (((Finset.univ : Finset α).filter (fun x =>
        ¬ f x = decide (g x = 1))).card : ℤ) - Fintype.card α) =
        -(2 * (((Finset.univ : Finset α).filter (fun x =>
        f x = decide (g x = 1))).card : ℤ) - Fintype.card α) := by
      simp only [Finset.card_univ] at hc
      omega
    rw [hz, Int.natAbs_neg]

end PEqualNP.Outside.L_meta_29742_aux.PhaseReview


namespace PEqualNP.Outside.L_meta_29742_aux.BiasTransport

abbrev F := ZMod 2
abbrev Vec (n : ℕ) := Fin n → F

def restrictedMask {k n : ℕ} (B : Vec n →ₗ[F] Vec k) (v : Vec k) : Vec n :=
  fun i => dotProduct v (B (Pi.single i 1))

lemma map_eq_sum_basis {k n : ℕ} (B : Vec n →ₗ[F] Vec k) (y : Vec n) :
    B y = ∑ i, y i • B (Pi.single i 1) := by
  conv_lhs => rw [pi_eq_sum_univ' y]
  simp only [map_sum, map_smul]

lemma restrictedMask_dot {k n : ℕ} (B : Vec n →ₗ[F] Vec k)
    (v : Vec k) (y : Vec n) :
    dotProduct (restrictedMask B v) y = dotProduct v (B y) := by
  rw [map_eq_sum_basis B y, dotProduct_sum]
  simp only [dotProduct_smul, smul_eq_mul]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

lemma restrictedMask_affine_dot {k n : ℕ} (B : Vec n →ₗ[F] Vec k)
    (v p : Vec k) (y : Vec n) :
    dotProduct v (p + B y) =
      dotProduct v p + dotProduct (restrictedMask B v) y := by
  rw [restrictedMask_dot]
  simp only [dotProduct, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma restrictedMask_bias {k n m : ℕ} (B : Vec n →ₗ[F] Vec k)
    (hB : Function.Injective B) (v : Fin m → Vec k) (χ : F → ℤ)
    (hbias : ∀ a : Vec k, a ≠ 0 →
      14 * |∑ j : Fin m, χ (dotProduct (v j) a)| ≤ m) :
    ∀ a : Vec n, a ≠ 0 →
      14 * |∑ j : Fin m,
        χ (dotProduct (restrictedMask B (v j)) a)| ≤ m := by
  intro a ha
  have hBa : B a ≠ 0 := by
    intro hz
    apply ha
    apply hB
    simpa using hz
  simpa only [restrictedMask_dot] using hbias (B a) hBa

end PEqualNP.Outside.L_meta_29742_aux.BiasTransport


namespace PEqualNP.Outside.L_meta_29742_aux.MasterSummation

lemma incidence_sum {m : ℕ} {I : Type*} [Fintype I]
    (R : Fin m → I → Prop) [∀ j i, Decidable (R j i)] (K : Finset (Fin m)) :
    (∑ j ∈ K, ((Finset.univ : Finset I).filter (R j)).card) =
      ∑ i : I, (K.filter (fun j => R j i)).card := by
  classical
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

lemma master_of_common_cover {m : ℕ} {I : Type*} [Fintype I]
    (N A L U : ℕ) (hA : 0 < A) (hI : Fintype.card I = A)
    (H : Fin m → ℕ) (R : Fin m → I → Prop) [∀ j i, Decidable (R j i)]
    (hpoint : ∀ j, A * (2 * (H j : ℤ) - (N : ℤ)).natAbs ≤
      N * ((Finset.univ : Finset I).filter (R j)).card)
    (hmass : ∀ i, L * ((Finset.univ : Finset (Fin m)).filter (fun j => R j i)).card ≤ U * m)
    (K : Finset (Fin m)) :
    L * (2 * (∑ j ∈ K, H j) - N * K.card) ≤ U * N * m := by
  classical
  let G : Fin m → ℕ := fun j => (2 * (H j : ℤ) - (N : ℤ)).natAbs
  have hrow : ∀ j, 2 * H j ≤ N + G j := by
    intro j
    have hj := @Int.le_natAbs (2 * (H j : ℤ) - (N : ℤ))
    dsimp only [G]
    omega
  have hsum : 2 * (∑ j ∈ K, H j) ≤ N * K.card + ∑ j ∈ K, G j := by
    calc
      2 * (∑ j ∈ K, H j) = ∑ j ∈ K, 2 * H j := Finset.mul_sum _ _ _
      _ ≤ ∑ j ∈ K, (N + G j) := Finset.sum_le_sum (fun j _ => hrow j)
      _ = N * K.card + ∑ j ∈ K, G j := by simp [Finset.sum_add_distrib, Nat.mul_comm]
  have hgain : 2 * (∑ j ∈ K, H j) - N * K.card ≤ ∑ j ∈ K, G j := by omega
  have hpointSum : A * (∑ j ∈ K, G j) ≤
      N * (∑ j ∈ K, ((Finset.univ : Finset I).filter (R j)).card) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => hpoint j)
  have hmassK : ∀ i, L * (K.filter (fun j => R j i)).card ≤ U * m := by
    intro i
    apply le_trans (Nat.mul_le_mul_left L (Finset.card_le_card ?_)) (hmass i)
    exact Finset.filter_subset_filter _ (Finset.subset_univ K)
  have hmassSum : L * (∑ j ∈ K, ((Finset.univ : Finset I).filter (R j)).card) ≤
      A * (U * m) := by
    rw [incidence_sum R K, Finset.mul_sum]
    calc
      (∑ i : I, L * (K.filter (fun j => R j i)).card) ≤ ∑ _i : I, U * m :=
        Finset.sum_le_sum (fun i _ => hmassK i)
      _ = A * (U * m) := by simp [hI]
  have hscaled : A * (L * (2 * (∑ j ∈ K, H j) - N * K.card)) ≤ A * (U * N * m) := by
    calc
      A * (L * (2 * (∑ j ∈ K, H j) - N * K.card)) =
          L * (A * (2 * (∑ j ∈ K, H j) - N * K.card)) := by ring
      _ ≤ L * (A * ∑ j ∈ K, G j) :=
        Nat.mul_le_mul_left L (Nat.mul_le_mul_left A hgain)
      _ ≤ L * (N * ∑ j ∈ K, ((Finset.univ : Finset I).filter (R j)).card) :=
        Nat.mul_le_mul_left L hpointSum
      _ = N * (L * ∑ j ∈ K, ((Finset.univ : Finset I).filter (R j)).card) := by ring
      _ ≤ N * (A * (U * m)) := Nat.mul_le_mul_left N hmassSum
      _ = A * (U * N * m) := by ring
  exact Nat.le_of_mul_le_mul_left hscaled hA

lemma master_of_spectral_flats (n m b h : ℕ)
    (u : Fin m → Fin n → ZMod 2)
    (D : Fin (2 ^ b) → Submodule (ZMod 2) (Fin n → ZMod 2))
    (a : Fin (2 ^ b) → Fin n → ZMod 2) (H : Fin m → ℕ)
    (hpoint : ∀ j,
      2 ^ b * (2 * (H j : ℤ) - (2 : ℤ) ^ n).natAbs ≤
        2 ^ n * ((Finset.univ : Finset (Fin (2 ^ b))).filter (fun i =>
          @decide (u j - a i ∈ D i) (Classical.propDecidable _))).card)
    (hmass : ∀ i,
      14 * 2 ^ h * ((Finset.univ : Finset (Fin m)).filter (fun j =>
        @decide (u j - a i ∈ D i) (Classical.propDecidable _))).card ≤
          (2 ^ h + 13) * m)
    (K : Finset (Fin m)) :
    14 * 2 ^ h * (2 * (∑ j ∈ K, H j) - 2 ^ n * K.card) ≤
      (2 ^ h + 13) * 2 ^ n * m := by
  classical
  apply master_of_common_cover (2 ^ n) (2 ^ b) (14 * 2 ^ h) (2 ^ h + 13)
    (by positivity) (by simp) H (fun j i => u j - a i ∈ D i)
  · intro j
    simpa using hpoint j
  · intro i
    simpa using hmass i

end PEqualNP.Outside.L_meta_29742_aux.MasterSummation


namespace PEqualNP.Outside.L_meta_29742_aux

open PEqualNP.CircuitLowerBounds

lemma master_from_flat_mass (k n t h : ℕ)
    (B : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2))
    (p : Fin k → ZMod 2) (v : Fin (2 ^ t) → Fin k → ZMod 2)
    (C : Circuit) (hgood : ∀ g ∈ C.gates, H6.goodGate g)
    (hcost : C.gates.countP H6.charged + h ≤ n)
    (hmass : ∀ (D : Submodule (ZMod 2) (Fin n → ZMod 2)) (a : Fin n → ZMod 2),
      Module.finrank (ZMod 2) D + h ≤ n →
      14 * 2 ^ h * ((Finset.univ : Finset (Fin (2 ^ t))).filter (fun j =>
        @decide (BiasTransport.restrictedMask B (v j) - a ∈ D)
          (Classical.propDecidable _))).card ≤ (2 ^ h + 13) * 2 ^ t)
    (K : Finset (Fin (2 ^ t))) :
    14 * 2 ^ h * (2 * (∑ j ∈ K,
      ((Finset.univ : Finset (Fin n → ZMod 2)).filter (fun y =>
        C.eval (List.ofFn (fun i : Fin k => decide ((p + B y) i = 1)) ++
          List.ofFn (fun l : Fin t => j.val.testBit l.val)) =
            decide (dotProduct (v j) (p + B y) = 1))).card) - 2 ^ n * K.card) ≤
      (2 ^ h + 13) * 2 ^ n * 2 ^ t := by
  classical
  let b := min (C.gates.countP H6.charged) n
  let u := fun j => BiasTransport.restrictedMask B (v j)
  let addr := fun (j : Fin (2 ^ t)) (l : Fin t) => j.val.testBit l.val
  let f := fun (j : Fin (2 ^ t)) (y : Fin n → ZMod 2) =>
    C.eval (List.ofFn (fun i : Fin k => decide ((p + B y) i = 1)) ++ List.ofFn (addr j))
  let H := fun j => ((Finset.univ : Finset (Fin n → ZMod 2)).filter (fun y =>
    f j y = decide (dotProduct (v j) (p + B y) = 1))).card
  obtain ⟨D, a, hD, hp⟩ := H6.affine_circuit_cover (t := t) B p C hgood
  have hpoint : ∀ j,
      2 ^ b * (2 * (H j : ℤ) - (2 : ℤ) ^ n).natAbs ≤
        2 ^ n * ((Finset.univ : Finset (Fin (2 ^ b))).filter (fun i =>
          @decide (u j - a i ∈ D i) (Classical.propDecidable _))).card := by
    intro j
    have hphase := PhaseReview.phase_abs_agreement (f j)
      (fun y => dotProduct (u j) y) (dotProduct (v j) p)
    have hcount : (2 * (H j : ℤ) - (2 : ℤ) ^ n).natAbs =
        (2 * (((Finset.univ : Finset (Fin n → ZMod 2)).filter (fun y =>
          f j y = decide (dotProduct (u j) y = 1))).card : ℤ) - (2 : ℤ) ^ n).natAbs := by
      dsimp only [H]
      simp_rw [BiasTransport.restrictedMask_affine_dot, add_comm (dotProduct (v j) p)]
      simpa only [u, Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.cast_pow,
        Nat.cast_ofNat] using hphase
    rw [hcount]
    exact hp (addr j) (u j)
  apply MasterSummation.master_of_spectral_flats n (2 ^ t) b h u D a H hpoint
  intro i
  apply hmass (D i) (a i)
  rw [hD i]
  exact le_trans (Nat.add_le_add_right (Nat.min_le_left _ _) h) hcost

end PEqualNP.Outside.L_meta_29742_aux


namespace PEqualNP.Outside.L_meta_29742_aux.Arithmetic

lemma h7_two_thirds_consequence
    (n c N m q hits : Nat) (hN : 0 < N) (hm : 0 < m)
    (hmaster : ∀ h : Nat, c + h ≤ n →
      14 * 2 ^ h * (2 * hits - N * q) ≤ (2 ^ h + 13) * N * m)
    (hhalf : m ≤ 2 * q) (hhits : 2 * N * q ≤ 3 * hits) :
    n ≤ c + 3 := by
  apply Nat.le_of_not_gt
  intro hbad
  have hfour : c + 4 ≤ n := by omega
  have hbound := hmaster 4 hfour
  change 224 * (2 * hits - N * q) ≤ 29 * N * m at hbound
  rw [Nat.mul_assoc] at hbound hhits
  have hq : 0 < q := by omega
  have hprod : 0 < N * q := Nat.mul_pos hN hq
  have hsub : N * q ≤ 2 * hits := by omega
  have hcancel := Nat.sub_add_cancel hsub
  have hscaled : N * m ≤ 2 * (N * q) := by
    calc
      N * m ≤ N * (2 * q) := Nat.mul_le_mul_left N hhalf
      _ = 2 * (N * q) := by simp only [← Nat.mul_assoc, Nat.mul_comm N 2]
  omega

lemma h7_exact_consequence
    (n c N m hits : Nat) (hN : 0 < N) (hm : 0 < m)
    (hmaster : ∀ h : Nat, c + h ≤ n →
      14 * 2 ^ h * (2 * hits - N * m) ≤ (2 ^ h + 13) * N * m)
    (hhits : hits = N * m) : n ≤ c := by
  apply Nat.le_of_not_gt
  intro hbad
  have hone : c + 1 ≤ n := by omega
  have hbound := hmaster 1 hone
  change 28 * (2 * hits - N * m) ≤ 15 * N * m at hbound
  rw [Nat.mul_assoc] at hbound
  have hprod : 0 < N * m := Nat.mul_pos hN hm
  have hsub : 2 * hits - N * m = N * m := by omega
  rw [hsub] at hbound
  omega

end PEqualNP.Outside.L_meta_29742_aux.Arithmetic


namespace PEqualNP.Outside.L_meta_29742_aux.H8

open PEqualNP.CircuitLowerBounds

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl stp w

lemma run_append (g1 g2 : List Gate) (w : List Bool) :
    run (g1 ++ g2) w = run g2 (run g1 w) := by
  unfold run; rw [List.foldl_append]

lemma run_length (gs : List Gate) : ∀ w : List Bool, (run gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [run]
  | cons g gs ih =>
    intro w
    show (run gs (stp w g)).length = _
    rw [ih]; simp [stp]; omega

lemma run_getD_lt (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (run gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    show (run gs (stp w g)).getD i false = _
    rw [ih _ _ (by simp [stp]; omega)]
    simp only [stp]
    rw [List.getD_append _ _ _ _ hi]

lemma getD_snoc (l : List Bool) (b : Bool) (n : ℕ) :
    (l ++ [b]).getD n false = if n = l.length then b else l.getD n false := by
  split_ifs with h
  · subst h; rw [List.getD_append_right _ _ _ _ le_rfl]; simp
  · rcases Nat.lt_or_ge n l.length with h' | h'
    · rw [List.getD_append _ _ _ _ h']
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ h']

lemma run_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length)
    (hrb : ∀ i ∈ (gs[j]).inputs, i < w.length + j) :
    (run gs w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i => (run gs w).getD i false) := by
  have hlen : (gs.take j).length = j := by simp; omega
  have hsplit : gs = gs.take j ++ (gs[j] :: gs.drop (j+1)) := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  have hW1len : (run (gs.take j) w).length = w.length + j := by rw [run_length, hlen]
  have hrun : run gs w = run (gs.drop (j+1)) (stp (run (gs.take j) w) gs[j]) := by
    conv_lhs => rw [hsplit]
    rw [run_append]; rfl
  have hpres : ∀ i < (run (gs.take j) w).length,
      (run gs w).getD i false = (run (gs.take j) w).getD i false := by
    intro i hi
    rw [hrun, run_getD_lt _ _ _ (by simp [stp]; omega)]
    simp only [stp]; rw [List.getD_append _ _ _ _ hi]
  have hmap : (gs[j]).inputs.map (fun i => (run gs w).getD i false) =
      (gs[j]).inputs.map (fun i => (run (gs.take j) w).getD i false) := by
    apply List.map_congr_left; intro i hi; exact hpres i (by rw [hW1len]; exact hrb i hi)
  rw [hmap, hrun, run_getD_lt _ _ _ (by simp [stp]; omega)]
  simp only [stp]
  rw [getD_snoc, if_pos hW1len.symm]



noncomputable def counted (g : Gate) : Bool :=
  @decide ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) (Classical.propDecidable _)

def legalG (g : Gate) : Prop :=
  g.inputs.length ≤ 2 ∧
    (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))

lemma eval_mod2_two (p q : Bool) : GateOp.eval (.mod 2) [p, q] = !(xor p q) := by
  cases p <;> cases q <;> rfl

lemma eval_mod2_one (p : Bool) : GateOp.eval (.mod 2) [p] = !p := by
  cases p <;> rfl

lemma eval_and_two (p q : Bool) : GateOp.eval .and [p, q] = (p && q) := by
  cases p <;> cases q <;> rfl

lemma eval_or_two (p q : Bool) : GateOp.eval .or [p, q] = (p || q) := by
  cases p <;> cases q <;> rfl
lemma z2_bit (x : ZMod 2) : (if decide (x = 1) = true then (1 : ZMod 2) else 0) = x := by
  revert x; decide
def inp (k t : ℕ) (x : Fin k → ZMod 2) (a : Fin t → Bool) : List Bool :=
  List.ofFn (fun l : Fin k => decide (x l = 1)) ++ List.ofFn a

lemma inp_length (k t : ℕ) (x : Fin k → ZMod 2) (a : Fin t → Bool) :
    (inp k t x a).length = k + t := by simp [inp]
def b2f (b : Bool) : ZMod 2 := if b then 1 else 0

lemma b2f_xnor (p q : Bool) : b2f (!(xor p q)) = b2f p + b2f q + 1 := by
  cases p <;> cases q <;> decide

lemma b2f_not (p : Bool) : b2f (!p) = b2f p + 1 := by cases p <;> decide

lemma eq_decide_of_b2f (b : Bool) (z : ZMod 2) (h : b2f b = z) : b = decide (z = 1) := by
  subst h; cases b <;> decide

lemma eval_not_one (p : Bool) : GateOp.eval .not [p] = !p := rfl

lemma sel_lemma (y0 y1 bit : Bool) :
    (!(!(xor y0 (bit && !(!(xor y0 y1)))))) = if bit then y1 else y0 := by
  cases y0 <;> cases y1 <;> cases bit <;> rfl

def xOf (k : ℕ) (W : List Bool) : Fin k → ZMod 2 := fun l => b2f (W.getD l false)

def aOf (k t : ℕ) (W : List Bool) : Fin t → Bool := fun l => W.getD (k + l) false

def Consistent (gs : List Gate) (o : ℕ) (Wf : List Bool) : Prop :=
  ∀ j (hj : j < gs.length), Wf.getD (o + j) false =
    (gs[j]).op.eval ((gs[j]).inputs.map fun i => Wf.getD i false)

def ReadsFrom (gs : List Gate) (o : ℕ) : Prop :=
  ∀ j (hj : j < gs.length), ∀ i ∈ (gs[j]).inputs, i < o + j

def Block (k t m : ℕ) (v : Fin m → (Fin k → ZMod 2)) (e : Fin m → ZMod 2)
    (addr : Fin m → (Fin t → Bool)) (S : Finset (Fin m)) (o : ℕ) (gs : List Gate) (out : ℕ) :
    Prop :=
  (∀ g ∈ gs, legalG g) ∧ ReadsFrom gs o ∧ out < o + gs.length ∧
  gs.countP counted + 1 ≤ S.card ∧
  ∃ leaf : (Fin t → Bool) → Fin m, (∀ a, leaf a ∈ S) ∧ (∀ i ∈ S, leaf (addr i) = i) ∧
    ∀ Wf, Consistent gs o Wf → Wf.getD out false =
      decide (v (leaf (aOf k t Wf)) ⬝ᵥ xOf k Wf + e (leaf (aOf k t Wf)) = 1)

lemma consistent_append {A B : List Gate} {o : ℕ} {Wf : List Bool}
    (h : Consistent (A ++ B) o Wf) : Consistent A o Wf ∧ Consistent B (o + A.length) Wf := by
  constructor
  · intro j hj
    have := h j (by simp; omega)
    rwa [List.getElem_append_left hj] at this
  · intro j hj
    have := h (A.length + j) (by simp; omega)
    rw [List.getElem_append_right (by omega)] at this
    simp only [Nat.add_sub_cancel_left] at this
    rw [show o + A.length + j = o + (A.length + j) by omega]
    exact this

lemma reads_append {A B : List Gate} {o : ℕ} (hA : ReadsFrom A o)
    (hB : ReadsFrom B (o + A.length)) : ReadsFrom (A ++ B) o := by
  intro j hj i hi
  by_cases h : j < A.length
  · rw [List.getElem_append_left h] at hi; exact hA j h i hi
  · rw [List.getElem_append_right (by omega)] at hi
    have := hB (j - A.length) (by simp at hj; omega) i hi
    omega

def leafGates (k : ℕ) (vi : Fin k → ZMod 2) (ei : ZMod 2) (o : ℕ) : List Gate :=
  ⟨if decide (ei + (k : ZMod 2) = 1) then .and else .or, []⟩ ::
  (List.range k).map (fun j => ⟨.mod 2,
    if (if h : j < k then vi ⟨j, h⟩ else 0) = 1 then [o + j, j] else [o + j]⟩)

lemma leaf_block (k t m : ℕ) (v : Fin m → (Fin k → ZMod 2)) (e : Fin m → ZMod 2)
    (addr : Fin m → (Fin t → Bool)) (i : Fin m) (o : ℕ) :
    Block k t m v e addr {i} o (leafGates k (v i) (e i) o) (o + k) := by
  have hlen : (leafGates k (v i) (e i) o).length = k + 1 := by simp [leafGates]
  refine ⟨?_, ?_, ?_, ?_, fun _ => i, fun _ => Finset.mem_singleton_self _, ?_, ?_⟩
  · intro g hg
    simp only [leafGates, List.mem_cons, List.mem_map, List.mem_range] at hg
    rcases hg with rfl | ⟨j, hj, rfl⟩
    · refine ⟨by simp, ?_⟩
      split_ifs <;> simp
    · refine ⟨by split_ifs <;> simp, Or.inr (Or.inr (Or.inl rfl))⟩
  · intro j hj i' hi'
    cases j with
    | zero => simp [leafGates] at hi'
    | succ j =>
      simp only [leafGates, List.getElem_cons_succ, List.getElem_map, List.getElem_range] at hi'
      have key : ∀ L : List ℕ, (L = [o + j, j] ∨ L = [o + j]) → i' ∈ L → i' < o + (j + 1) := by
        rintro L (rfl | rfl) h <;> simp at h <;> omega
      exact key _ (by
        by_cases hv : (if h : j < k then v i ⟨j, h⟩ else 0) = 1
        · rw [if_pos hv]; exact Or.inl rfl
        · rw [if_neg hv]; exact Or.inr rfl) hi'
  · rw [hlen]; omega
  · have : (leafGates k (v i) (e i) o).countP counted = 0 := by
      rw [List.countP_eq_zero]
      intro g hg
      simp only [leafGates, List.mem_cons, List.mem_map, List.mem_range] at hg
      rcases hg with rfl | ⟨j, hj, rfl⟩
      · simp [counted]
      · simp [counted]
    rw [this]; simp
  · intro i' hi'; rw [Finset.mem_singleton] at hi'; exact hi'.symm
  · intro Wf hW
    have hstep : ∀ j, j ≤ k → b2f (Wf.getD (o + j) false) =
        b2f (decide (e i + (k : ZMod 2) = 1)) +
          ∑ l ∈ Finset.range j,
            ((if h : l < k then v i ⟨l, h⟩ else 0) * b2f (Wf.getD l false) + 1) := by
      intro j
      induction j with
      | zero =>
        intro _
        have := hW 0 (by rw [hlen]; omega)
        simp only [leafGates, List.getElem_cons_zero, List.map_nil, Nat.add_zero] at this
        simp only [Finset.range_zero, Finset.sum_empty, add_zero, Nat.add_zero]
        rw [this]
        cases decide (e i + (k : ZMod 2) = 1) <;> rfl
      | succ j ih =>
        intro hj
        have := hW (j + 1) (by rw [hlen]; omega)
        simp only [leafGates, List.getElem_cons_succ, List.getElem_map,
          List.getElem_range] at this
        rw [this, Finset.sum_range_succ, ← add_assoc, ← ih (by omega)]
        by_cases hv : (if h : j < k then v i ⟨j, h⟩ else 0) = 1
        · rw [if_pos hv]
          simp only [List.map_cons, List.map_nil, eval_mod2_two, b2f_xnor, hv, one_mul]
          ring
        · rw [if_neg hv]
          simp only [List.map_cons, List.map_nil, eval_mod2_one, b2f_not]
          have h0 : (if h : j < k then v i ⟨j, h⟩ else 0) = 0 := by
            generalize (if h : j < k then v i ⟨j, h⟩ else 0) = z at hv ⊢
            revert z; decide
          rw [h0, zero_mul, zero_add]
    have hk := hstep k le_rfl
    apply eq_decide_of_b2f
    rw [hk, Finset.sum_range
      (fun l => (if h : l < k then v i ⟨l, h⟩ else 0) * b2f (Wf.getD l false) + 1)]
    simp only [Fin.is_lt, ↓reduceDIte, Fin.eta]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [show b2f (decide (e i + (k : ZMod 2) = 1)) = e i + k by unfold b2f; exact z2_bit _]
    simp only [dotProduct, xOf]
    have hkk : (k : ZMod 2) + k = 0 := by
      generalize (k : ZMod 2) = z; revert z; decide
    linear_combination hkk

def combGates (k b out0 out1 o2 : ℕ) : List Gate :=
  [⟨.mod 2, [out0, out1]⟩, ⟨.not, [o2]⟩, ⟨.and, [k + b, o2 + 1]⟩, ⟨.mod 2, [out0, o2 + 2]⟩,
    ⟨.not, [o2 + 3]⟩]

lemma comb_block (k t m : ℕ) (v : Fin m → (Fin k → ZMod 2)) (e : Fin m → ZMod 2)
    (addr : Fin m → (Fin t → Bool)) (S S0 S1 : Finset (Fin m)) (b : Fin t)
    (h0sub : S0 ⊆ S) (h1sub : S1 ⊆ S) (hcard : S0.card + S1.card = S.card)
    (hS0 : ∀ i ∈ S, addr i b = false → i ∈ S0) (hS1 : ∀ i ∈ S, addr i b = true → i ∈ S1)
    (o : ℕ) (ho : k + t ≤ o) (gs0 gs1 : List Gate) (out0 out1 : ℕ)
    (h0 : Block k t m v e addr S0 o gs0 out0)
    (h1 : Block k t m v e addr S1 (o + gs0.length) gs1 out1) :
    Block k t m v e addr S o
      (gs0 ++ gs1 ++ combGates k b out0 out1 (o + gs0.length + gs1.length))
      (o + gs0.length + gs1.length + 4) := by
  obtain ⟨l0, r0, o0, c0, leaf0, m0, f0, s0⟩ := h0
  obtain ⟨l1, r1, o1, c1, leaf1, m1, f1, s1⟩ := h1
  have hb := b.isLt
  refine ⟨?_, ?_, ?_, ?_, fun a => if a b then leaf1 a else leaf0 a, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append] at hg
    rcases hg with (hg | hg) | hg
    · exact l0 g hg
    · exact l1 g hg
    · simp only [combGates, List.mem_cons, List.mem_nil_iff, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp [legalG]
  · apply reads_append (reads_append r0 r1)
    intro j hj i hi
    simp only [combGates, List.length_cons, List.length_nil] at hj
    simp only [List.length_append]
    interval_cases j <;> simp [combGates] at hi <;> omega
  · simp [combGates]; omega
  · simp only [List.countP_append]
    have : (combGates k b out0 out1 (o + gs0.length + gs1.length)).countP counted = 1 := by
      simp [combGates, counted, List.countP_cons]
    omega
  · intro a
    by_cases h : a b = true
    · simp only [h, ↓reduceIte]; exact h1sub (m1 a)
    · simp only [h, ↓reduceIte]; exact h0sub (m0 a)
  · intro i hi
    by_cases h : addr i b = true
    · simp only [h, ↓reduceIte]; exact f1 i (hS1 i hi h)
    · simp only [h, ↓reduceIte]
      exact f0 i (hS0 i hi (by simpa using h))
  · intro Wf hW
    obtain ⟨hW01, hWc⟩ := consistent_append hW
    obtain ⟨hW0, hW1⟩ := consistent_append hW01
    have y0 := s0 Wf hW0
    have y1 := s1 Wf hW1
    have hN : o + (gs0 ++ gs1).length = o + gs0.length + gs1.length := by
      simp only [List.length_append]; omega
    rw [hN] at hWc
    have e0 := hWc 0 (by simp [combGates])
    have e1 := hWc 1 (by simp [combGates])
    have e2 := hWc 2 (by simp [combGates])
    have e3 := hWc 3 (by simp [combGates])
    have e4 := hWc 4 (by simp [combGates])
    simp only [combGates, List.getElem_cons_zero, List.getElem_cons_succ, List.map_cons,
      List.map_nil, add_zero] at e0 e1 e2 e3 e4
    rw [eval_mod2_two] at e0 e3
    rw [eval_and_two] at e2
    rw [eval_not_one] at e1 e4
    have hab : Wf.getD (k + ↑b) false = aOf k t Wf b := rfl
    rw [e4, e3, e2, e1, e0, hab, sel_lemma]
    beta_reduce
    by_cases h : aOf k t Wf b = true
    · simp only [h, ↓reduceIte]; exact y1
    · simp only [h, ↓reduceIte, Bool.false_eq_true]; exact y0

lemma build (k t m : ℕ) (v : Fin m → (Fin k → ZMod 2)) (e : Fin m → ZMod 2)
    (addr : Fin m → (Fin t → Bool)) (hinj : Function.Injective addr) (S : Finset (Fin m)) :
    S.Nonempty → ∀ o, k + t ≤ o → ∃ gs out, Block k t m v e addr S o gs out := by
  classical
  refine Finset.strongInduction
    (p := fun S => S.Nonempty → ∀ o, k + t ≤ o → ∃ gs out, Block k t m v e addr S o gs out)
    ?_ S
  intro S ih hne o ho
  by_cases h1 : S.card = 1
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp h1
    exact ⟨_, _, leaf_block k t m v e addr i o⟩
  · have h2 : 1 < S.card := by
      have := Finset.card_pos.mpr hne; omega
    obtain ⟨i1, hi1, i2, hi2, hne12⟩ := Finset.one_lt_card.mp h2
    have hadd : addr i1 ≠ addr i2 := fun h => hne12 (hinj h)
    obtain ⟨b, hb⟩ := Function.ne_iff.mp hadd
    have key : (addr i1 b = true ∧ addr i2 b = false) ∨ (addr i1 b = false ∧ addr i2 b = true) := by
      revert hb; cases addr i1 b <;> cases addr i2 b <;> simp
    have hS1ne : (S.filter (fun i => addr i b = true)).Nonempty := by
      rcases key with ⟨ha, _⟩ | ⟨_, ha⟩
      · exact ⟨i1, Finset.mem_filter.mpr ⟨hi1, ha⟩⟩
      · exact ⟨i2, Finset.mem_filter.mpr ⟨hi2, ha⟩⟩
    have hS0ne : (S.filter (fun i => ¬ addr i b = true)).Nonempty := by
      rcases key with ⟨_, ha⟩ | ⟨ha, _⟩
      · exact ⟨i2, Finset.mem_filter.mpr ⟨hi2, by simp [ha]⟩⟩
      · exact ⟨i1, Finset.mem_filter.mpr ⟨hi1, by simp [ha]⟩⟩
    have hS1ss : S.filter (fun i => addr i b = true) ⊂ S := by
      rw [Finset.filter_ssubset]
      obtain ⟨x, hx⟩ := hS0ne
      exact ⟨x, (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩
    have hS0ss : S.filter (fun i => ¬ addr i b = true) ⊂ S := by
      rw [Finset.filter_ssubset]
      obtain ⟨x, hx⟩ := hS1ne
      exact ⟨x, (Finset.mem_filter.mp hx).1, not_not.mpr (Finset.mem_filter.mp hx).2⟩
    have hcard := Finset.card_filter_add_card_filter_not (s := S) (fun i => addr i b = true)
    obtain ⟨gs0, out0, h0⟩ := ih _ hS0ss hS0ne o ho
    obtain ⟨gs1, out1, h1⟩ := ih _ hS1ss hS1ne (o + gs0.length) (by omega)
    refine ⟨_, _, comb_block k t m v e addr S _ _ b (Finset.filter_subset _ _)
      (Finset.filter_subset _ _) (by omega) ?_ ?_ o ho gs0 gs1 out0 out1 h0 h1⟩
    · intro i hi h
      exact Finset.mem_filter.mpr ⟨hi, by simp [h]⟩
    · intro i hi h
      exact Finset.mem_filter.mpr ⟨hi, h⟩

lemma bit_address_injective (t : ℕ) :
    Function.Injective (fun (j : Fin (2^t)) (l : Fin t) => j.val.testBit l.val) := by
  intro a b hab
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < t
  · exact congrFun hab ⟨i, hi⟩
  · have ha : a.val < 2 ^ i :=
      lt_of_lt_of_le a.isLt (Nat.pow_le_pow_right (by omega) (by omega))
    have hb : b.val < 2 ^ i :=
      lt_of_lt_of_le b.isLt (Nat.pow_le_pow_right (by omega) (by omega))
    rw [Nat.testBit_lt_two_pow ha, Nat.testBit_lt_two_pow hb]

lemma full_lookup (k t : ℕ) (v : Fin (2^t) → Fin k → ZMod 2) :
    ∃ C : Circuit,
      (PEqualNP.MetaComplexity.NestedCover.ReadsBack (k+t) C ∧
        ∀ g ∈ C.gates, legalG g) ∧
      C.output < k+t+C.size ∧ C.gates.countP counted ≤ 2^t-1 ∧
      ∀ (x : Fin k → ZMod 2) (j : Fin (2^t)),
        C.eval (List.ofFn (fun l : Fin k => decide (x l = 1)) ++
          List.ofFn (fun l : Fin t => j.val.testBit l.val)) =
        decide (dotProduct (v j) x = 1) := by
  classical
  let addr := fun (j : Fin (2^t)) (l : Fin t) => j.val.testBit l.val
  have hne : (Finset.univ : Finset (Fin (2^t))).Nonempty := by
    exact ⟨⟨0, Nat.two_pow_pos t⟩, Finset.mem_univ _⟩
  obtain ⟨gs, out, hl, hr, hout, hc, leaf, hleafS, hleaf, hsem⟩ :=
    build k t (2^t) v (fun _ => 0) addr (bit_address_injective t)
      Finset.univ hne (k+t) le_rfl
  refine ⟨⟨gs, out⟩, ⟨?_, hl⟩, hout, ?_, ?_⟩
  · intro j hj i hi
    simp only [PEqualNP.MetaComplexity.NestedCover.gateAt] at hi
    rw [List.getD_eq_getElem _ _ hj] at hi
    exact hr j hj i hi
  · simp only [Finset.card_univ, Fintype.card_fin] at hc
    change gs.countP counted ≤ 2^t-1
    omega
  · intro x j
    have hW := hsem (run gs (inp k t x (addr j))) (fun l hl => by
      have := run_getD_gate gs (inp k t x (addr j)) l hl
        (by rw [inp_length]; exact hr l hl)
      rw [inp_length] at this
      exact this)
    have ha : aOf k t (run gs (inp k t x (addr j))) = addr j := by
      funext l
      unfold aOf
      rw [run_getD_lt _ _ _ (by rw [inp_length]; omega)]
      unfold inp
      rw [List.getD_append_right _ _ _ _ (by simp)]
      simp [List.getD_eq_getElem?_getD]
    have hx : xOf k (run gs (inp k t x (addr j))) = x := by
      funext l
      have hg : (inp k t x (addr j)).getD l false = decide (x l = 1) := by
        unfold inp
        rw [List.getD_append _ _ _ _ (by simp)]
        simp [List.getD_eq_getElem?_getD]
      unfold xOf
      rw [run_getD_lt _ _ _ (by rw [inp_length]; omega), hg]
      exact z2_bit _
    rw [ha, hx, hleaf j (Finset.mem_univ _), add_zero] at hW
    exact hW

end PEqualNP.Outside.L_meta_29742_aux.H8

theorem PEqualNP.Outside.L_meta_29742 : ∀ k : ℕ, 64 ≤ k →
  let F := ZMod 2
  let V := Fin k → F
  ∃ t : ℕ, let m := 2^t
    512*k ≤ m ∧ m < 1024*k ∧
    ∃ s : Fin (2^(k+m-1)),
      let v := fun (j : Fin m) (i : Fin k) =>
        if s.val.testBit (j.val+i.val) then (1 : F) else 0
      let inp := fun (x : V) (j : Fin m) =>
        List.ofFn (fun i : Fin k => decide (x i = 1)) ++ List.ofFn (fun l : Fin t => j.val.testBit l.val)
      let legal := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (k+t) C ∧
        (∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
          (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1)))
      let cost := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
        C.gates.countP (fun z => @decide
          ((z.op = .and ∨ z.op = .or) ∧ z.inputs.length = 2) (Classical.propDecidable _))
      (∃ H, legal H ∧ H.output < k+t+H.size ∧ cost H ≤ m-1 ∧
        ∀ x j, H.eval (inp x j) = decide (dotProduct (v j) x = 1)) ∧
      ∀ (n : ℕ) (B : (Fin n → F) →ₗ[F] V), Function.Injective B →
      ∀ (p : V) (K : Finset (Fin m)) (C : PEqualNP.CircuitLowerBounds.Circuit), legal C →
        let hits := ∑ j ∈ K, ((Finset.univ : Finset (Fin n → F)).filter (fun y =>
          C.eval (inp (p+B y) j) = decide (dotProduct (v j) (p+B y) = 1))).card
        let N := 2^n
        (∀ h : ℕ, cost C+h ≤ n →
          14*2^h*(2*hits-N*K.card) ≤ (2^h+13)*N*m) ∧
        (m ≤ 2*K.card → 2*N*K.card ≤ 3*hits → n ≤ cost C+3) ∧
        (K = Finset.univ → hits = N*K.card → n ≤ cost C) := by
  classical
  intro k hk F V
  obtain ⟨t, hmlo, hmhi⟩ := PEqualNP.Outside.L_meta_29742_aux.width_exists k hk
  refine ⟨t, hmlo, hmhi, ?_⟩
  obtain ⟨s, hs⟩ := PEqualNP.Outside.L_meta_29742_aux.Tape.exists_bias_tape k (2 ^ t) hk hmlo hmhi.le
  refine ⟨s, ?_⟩
  intro v inp legal cost
  refine ⟨?_, ?_⟩
  · exact PEqualNP.Outside.L_meta_29742_aux.H8.full_lookup k t v
  · intro n B hB p K C hC hits N
    have hbias : ∀ a : Fin k → ZMod 2, a ≠ 0 →
        14 * |∑ j : Fin (2 ^ t), PEqualNP.Outside.L_meta_29742_aux.H7.chi
          (dotProduct a (v j))| ≤ ((2 ^ t : ℕ) : ℤ) := by
      intro a ha
      exact hs a ha
    have hu := PEqualNP.Outside.L_meta_29742_aux.BiasTransport.restrictedMask_bias B hB v
      PEqualNP.Outside.L_meta_29742_aux.H7.chi
      (by intro a ha; simpa only [dotProduct_comm] using hbias a ha)
    have hu' : ∀ a : Fin n → ZMod 2, a ≠ 0 →
        14 * |∑ j : Fin (2 ^ t), PEqualNP.Outside.L_meta_29742_aux.H7.chi
          (dotProduct a (PEqualNP.Outside.L_meta_29742_aux.BiasTransport.restrictedMask B (v j)))|
            ≤ ((2 ^ t : ℕ) : ℤ) := by
      intro a ha
      simpa only [dotProduct_comm] using hu a ha
    have hmaster : ∀ h : ℕ, cost C + h ≤ n →
        14 * 2 ^ h * (2 * hits - N * K.card) ≤ (2 ^ h + 13) * N * 2 ^ t := by
      intro h hh
      exact PEqualNP.Outside.L_meta_29742_aux.master_from_flat_mass k n t h B p v C hC.2 hh
        (fun D a hd => PEqualNP.Outside.L_meta_29742_aux.H7.smallBias_flat_count
          (fun j => PEqualNP.Outside.L_meta_29742_aux.BiasTransport.restrictedMask B (v j))
          hu' D a hd) K
    refine ⟨hmaster, ?_, ?_⟩
    · intro hhalf hagree
      exact PEqualNP.Outside.L_meta_29742_aux.Arithmetic.h7_two_thirds_consequence
        n (cost C) N (2 ^ t) K.card hits (by positivity) (by positivity)
        hmaster hhalf hagree
    · intro hK hagree
      have hcard : K.card = 2 ^ t := by rw [hK]; simp
      apply PEqualNP.Outside.L_meta_29742_aux.Arithmetic.h7_exact_consequence
        n (cost C) N (2 ^ t) hits (by positivity) (by positivity)
      · intro h hh
        simpa only [hcard] using hmaster h hh
      · simpa only [hcard] using hagree
