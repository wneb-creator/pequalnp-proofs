import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29742_aux

namespace Tape

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

abbrev F2 := ZMod 2

def chi (a : F2) : ℤ := if a = 1 then -1 else 1

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
      push_neg at h
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

lemma exists_pow2_window (k : ℕ) (hk : 64 ≤ k) :
    ∃ t : ℕ, 512 * k ≤ 2 ^ t ∧ 2 ^ t < 1024 * k := by
  have hex : ∃ t : ℕ, 512 * k ≤ 2 ^ t := ⟨512 * k, le_of_lt Nat.lt_two_pow_self⟩
  classical
  let t := Nat.find hex
  have ht : 512 * k ≤ 2 ^ t := Nat.find_spec hex
  have ht0 : 0 < t := by
    by_contra h0
    have hteq : t = 0 := by omega
    rw [hteq] at ht
    omega
  have hprev : 2 ^ (t - 1) < 512 * k := Nat.lt_of_not_ge (Nat.find_min hex (by omega))
  have hpow : 2 ^ t = 2 * 2 ^ (t - 1) := by
    have : t = (t - 1) + 1 := by omega
    conv_lhs => rw [this, pow_succ]
    ring
  exact ⟨t, ht, by omega⟩

def bitsToNat : ∀ {N : ℕ}, (Fin N → F2) → ℕ
  | 0, _ => 0
  | _ + 1, b => (if b 0 = 1 then 1 else 0) + 2 * bitsToNat (fun i => b i.succ)

lemma bitsToNat_lt {N : ℕ} (b : Fin N → F2) : bitsToNat b < 2 ^ N := by
  induction N with
  | zero => simp [bitsToNat]
  | succ n ih =>
    simp only [bitsToNat, pow_succ]
    have h := ih (fun i => b i.succ)
    split_ifs <;> omega

lemma bitsToNat_testBit {N : ℕ} (b : Fin N → F2) (r : ℕ) (hr : r < N) :
    (bitsToNat b).testBit r = decide (b ⟨r, hr⟩ = 1) := by
  induction N generalizing r with
  | zero => omega
  | succ n ih =>
    simp only [bitsToNat]
    cases r with
    | zero =>
      rw [Nat.testBit_zero]
      split_ifs with h
      · have hmod : (1 + 2 * bitsToNat (fun i => b i.succ)) % 2 = 1 := by omega
        simp [hmod, h]
      · have hmod : (0 + 2 * bitsToNat (fun i => b i.succ)) % 2 = 0 := by omega
        simp [hmod, h]
    | succ r' =>
      rw [Nat.testBit_succ]
      have hdiv : ((if b 0 = 1 then 1 else 0) + 2 * bitsToNat (fun i => b i.succ)) / 2 =
          bitsToNat (fun i => b i.succ) := by
        split_ifs <;> omega
      rw [hdiv]
      exact ih (fun i => b i.succ) r' (by omega)

lemma bitsToNat_fin_testBit {N : ℕ} (b : Fin N → F2) (r : ℕ) (hr : r < N) :
    (if (⟨bitsToNat b, bitsToNat_lt b⟩ : Fin (2 ^ N)).val.testBit r then (1 : F2) else 0) =
      b ⟨r, hr⟩ := by
  change (if (bitsToNat b).testBit r then (1 : F2) else 0) = b ⟨r, hr⟩
  rw [bitsToNat_testBit b r hr]
  exact boolToF2_decide (b ⟨r, hr⟩)

lemma linear_surj_fiber_card {A B : ℕ} (f : (Fin A → F2) → (Fin B → F2))
    (hadd : ∀ x y, f (x + y) = f x + f y)
    (hsurj : Function.Surjective f) (y : Fin B → F2) :
    (Finset.univ.filter (fun x => f x = y)).card =
      (Finset.univ.filter (fun x => f x = 0)).card := by
  rcases hsurj y with ⟨x₀, hx₀⟩
  refine Finset.card_bij (fun x _ => x + x₀) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [hadd, hx, hx₀]
    ext i
    exact zmod2_add_self (y i)
  · intro x₁ _ x₂ _ h
    have h' : x₁ + x₀ + x₀ = x₂ + x₀ + x₀ := congrArg (· + x₀) h
    ext i
    have hi := congrFun h' i
    simp only [Pi.add_apply, add_assoc, zmod2_add_self, add_zero] at hi
    exact hi
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    refine ⟨z + x₀, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hadd, hz, hx₀, zero_add]
    · ext i
      simp only [Pi.add_apply, add_assoc, zmod2_add_self, add_zero]

lemma add_surj_preimage_card {A B : ℕ} (f : (Fin A → F2) → (Fin B → F2))
    (hadd : ∀ x y, f (x + y) = f x + f y)
    (hsurj : Function.Surjective f) (P : (Fin B → F2) → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun x => P (f x))).card * 2 ^ B =
      (Finset.univ.filter P).card * 2 ^ A := by
  let K := (Finset.univ.filter (fun x => f x = 0)).card
  have hfib : ∀ y : Fin B → F2, (Finset.univ.filter (fun x => f x = y)).card = K :=
    linear_surj_fiber_card f hadd hsurj
  have hpart : ∀ S : Finset (Fin B → F2),
      (Finset.univ.filter (fun x => f x ∈ S)).card = S.card * K := by
    intro S
    have hbi := Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ.filter (fun x => f x ∈ S)) (t := S) (f := f)
      (fun x hx => (Finset.mem_filter.mp hx).2)
    rw [hbi]
    have hcongr : ∀ y ∈ S,
        ((Finset.univ.filter (fun x => f x ∈ S)).filter (fun x => f x = y)).card = K := by
      intro y hy
      have heq : (Finset.univ.filter (fun x => f x ∈ S)).filter (fun x => f x = y) =
          Finset.univ.filter (fun x => f x = y) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => h.2, fun h => ⟨h ▸ hy, h⟩⟩
      rw [heq, hfib y]
    rw [Finset.sum_congr rfl hcongr, Finset.sum_const, smul_eq_mul]
  have htot := hpart Finset.univ
  have huniv : Finset.univ.filter (fun x : Fin A → F2 => f x ∈ (Finset.univ : Finset (Fin B → F2))) =
      Finset.univ := by ext x; simp
  rw [huniv] at htot
  have hcardA : (Finset.univ : Finset (Fin A → F2)).card = 2 ^ A := by
    simp [Fintype.card_fun, ZMod.card]
  have hcardB : (Finset.univ : Finset (Fin B → F2)).card = 2 ^ B := by
    simp [Fintype.card_fun, ZMod.card]
  rw [hcardA, hcardB] at htot
  have hP := hpart (Finset.univ.filter P)
  have hPeq : Finset.univ.filter (fun x => f x ∈ Finset.univ.filter P) =
      Finset.univ.filter (fun x => P (f x)) := by ext x; simp
  rw [hPeq] at hP
  calc
    (Finset.univ.filter (fun x => P (f x))).card * 2 ^ B
        = (Finset.univ.filter P).card * K * 2 ^ B := by rw [hP]
    _ = (Finset.univ.filter P).card * (2 ^ B * K) := by ring
    _ = (Finset.univ.filter P).card * 2 ^ A := by rw [← htot]

def tapeVec (k m : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m) (b : Fin (k + m - 1) → F2)
    (j : Fin m) (i : Fin k) : F2 :=
  b ⟨j.val + i.val, by omega⟩

lemma sum_pow_split (m a c : ℕ) :
    (∑ z : Fin m → F2,
      a ^ (Finset.univ.filter (fun j : Fin m => z j = 0)).card *
      c ^ (Finset.univ.filter (fun j : Fin m => z j = 1)).card) = (a + c) ^ m := by
  induction m with
  | zero =>
    simp
  | succ n ih =>
    let e : (Fin (n + 1) → F2) ≃ F2 × (Fin n → F2) :=
      { toFun := fun z => (z 0, fun i => z i.succ)
        invFun := fun p => Fin.cons p.1 p.2
        left_inv := fun z => by
          ext i
          refine Fin.cases ?_ ?_ i <;> simp
        right_inv := fun p => by
          ext <;> simp }
    rw [Fintype.sum_equiv e _ (fun p =>
      a ^ ((if p.1 = 0 then 1 else 0) + (Finset.univ.filter (fun j : Fin n => p.2 j = 0)).card) *
      c ^ ((if p.1 = 1 then 1 else 0) + (Finset.univ.filter (fun j : Fin n => p.2 j = 1)).card))]
    · rw [Fintype.sum_prod_type]
      have hsum2 : ∀ g : F2 → ℕ, (∑ x : F2, g x) = g 0 + g 1 := by
        intro g
        exact Fin.sum_univ_two g
      rw [hsum2]
      have h0 : (∑ y : Fin n → F2,
          a ^ ((if (0 : F2) = 0 then 1 else 0) + (Finset.univ.filter (fun j => y j = 0)).card) *
          c ^ ((if (0 : F2) = 1 then 1 else 0) + (Finset.univ.filter (fun j => y j = 1)).card)) =
          a * (a + c) ^ n := by
        rw [← ih, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        have h01 : (0 : F2) ≠ 1 := by decide
        simp only [ite_true, h01, ite_false, zero_add]
        rw [pow_add, pow_one]
        ring
      have h1 : (∑ y : Fin n → F2,
          a ^ ((if (1 : F2) = 0 then 1 else 0) + (Finset.univ.filter (fun j => y j = 0)).card) *
          c ^ ((if (1 : F2) = 1 then 1 else 0) + (Finset.univ.filter (fun j => y j = 1)).card)) =
          c * (a + c) ^ n := by
        rw [← ih, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        have h10 : (1 : F2) ≠ 0 := by decide
        simp only [ite_true, h10, ite_false, zero_add]
        rw [pow_add, pow_one]
        ring
      rw [h0, h1, pow_succ]
      ring
    · intro z
      have hcard : ∀ v : F2,
          (Finset.univ.filter (fun j : Fin (n + 1) => z j = v)).card =
            (if z 0 = v then 1 else 0) +
              (Finset.univ.filter (fun j : Fin n => z j.succ = v)).card := by
        intro v
        rw [Fin.card_filter_univ_succ]
        split_ifs <;> omega
      rw [hcard 0, hcard 1]
      rfl

lemma bias_pos_card_bound (m : ℕ) :
    let q := m / 28
    (Finset.univ.filter (fun z : Fin m → F2 =>
      m < 14 * (∑ j : Fin m, chi (z j)))).card *
      15 ^ (15 * q) * 13 ^ (m - 15 * q) ≤ 28 ^ m := by
  intro q
  let S := Finset.univ.filter (fun z : Fin m → F2 => m < 14 * (∑ j : Fin m, chi (z j)))
  have hle : ∀ z ∈ S,
      15 ^ (15 * q) * 13 ^ (m - 15 * q) ≤
        15 ^ (Finset.univ.filter (fun j : Fin m => z j = 0)).card *
        13 ^ (Finset.univ.filter (fun j : Fin m => z j = 1)).card := by
    intro z hz
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    let c0 := (Finset.univ.filter (fun j : Fin m => z j = 0)).card
    let c1 := (Finset.univ.filter (fun j : Fin m => z j = 1)).card
    have hsum_c : c0 + c1 = m := by
      have hunion : Finset.univ.filter (fun j : Fin m => z j = 0) ∪
          Finset.univ.filter (fun j : Fin m => z j = 1) = Finset.univ := by
        ext j
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        exact zmod2_eq_zero_or_one (z j)
      have hdisj : Disjoint (Finset.univ.filter (fun j : Fin m => z j = 0))
          (Finset.univ.filter (fun j : Fin m => z j = 1)) := by
        rw [Finset.disjoint_filter]
        intro j _ h0 h1
        rw [h0] at h1
        exact absurd h1 (by decide)
      have h := Finset.card_union_of_disjoint hdisj
      rw [hunion, Finset.card_univ, Fintype.card_fin] at h
      exact h.symm
    have hchi_sum : (∑ j : Fin m, chi (z j)) = (c0 : ℤ) - (c1 : ℤ) := by
      have h1 : ∀ j : Fin m, chi (z j) = (if z j = 0 then (1 : ℤ) else 0) -
          (if z j = 1 then (1 : ℤ) else 0) := by
        intro j
        rcases zmod2_eq_zero_or_one (z j) with h0 | h1
        · simp [h0, chi_zero]
        · simp [h1, chi_one]
      simp_rw [h1, Finset.sum_sub_distrib, Finset.sum_boole]
      rfl
    have hc0 : 15 * q ≤ c0 := by
      rw [hchi_sum] at hz
      have hq : 28 * q ≤ m := Nat.mul_div_le m 28
      omega
    have hdiff : c0 - 15 * q + c1 = m - 15 * q := by omega
    calc
      15 ^ (15 * q) * 13 ^ (m - 15 * q)
          = 15 ^ (15 * q) * 13 ^ (c0 - 15 * q + c1) := by rw [hdiff]
      _ = 15 ^ (15 * q) * 13 ^ (c0 - 15 * q) * 13 ^ c1 := by rw [pow_add]; ring
      _ ≤ 15 ^ (15 * q) * 15 ^ (c0 - 15 * q) * 13 ^ c1 := by
            gcongr; norm_num
      _ = 15 ^ (15 * q + (c0 - 15 * q)) * 13 ^ c1 := by rw [pow_add]
      _ = 15 ^ c0 * 13 ^ c1 := by rw [Nat.add_sub_cancel' hc0]
  calc
    S.card * 15 ^ (15 * q) * 13 ^ (m - 15 * q)
        = S.card * (15 ^ (15 * q) * 13 ^ (m - 15 * q)) := by ring
    _ = ∑ _z ∈ S, (15 ^ (15 * q) * 13 ^ (m - 15 * q)) := by
          rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ z ∈ S,
          15 ^ (Finset.univ.filter (fun j : Fin m => z j = 0)).card *
          13 ^ (Finset.univ.filter (fun j : Fin m => z j = 1)).card :=
          Finset.sum_le_sum hle
    _ ≤ ∑ z : Fin m → F2,
          15 ^ (Finset.univ.filter (fun j : Fin m => z j = 0)).card *
          13 ^ (Finset.univ.filter (fun j : Fin m => z j = 1)).card :=
          Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
    _ = (15 + 13) ^ m := sum_pow_split m 15 13
    _ = 28 ^ m := by norm_num

lemma bias_abs_card_bound (m : ℕ) :
    (Finset.univ.filter (fun z : Fin m → F2 =>
      (m : ℤ) < 14 * |∑ j : Fin m, chi (z j)|)).card ≤
      2 * (Finset.univ.filter (fun z : Fin m → F2 =>
        (m : ℤ) < 14 * (∑ j : Fin m, chi (z j)))).card := by
  let Spos := Finset.univ.filter (fun z : Fin m → F2 => (m : ℤ) < 14 * (∑ j : Fin m, chi (z j)))
  let Sneg := Finset.univ.filter (fun z : Fin m → F2 => (m : ℤ) < 14 * -(∑ j : Fin m, chi (z j)))
  have hsub : Finset.univ.filter (fun z : Fin m → F2 => (m : ℤ) < 14 * |∑ j : Fin m, chi (z j)|) ⊆
      Spos ∪ Sneg := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Spos, Sneg] at hz ⊢
    rcases le_or_gt 0 (∑ j : Fin m, chi (z j)) with hge | hlt
    · left; rwa [abs_of_nonneg hge] at hz
    · right; rwa [abs_of_neg hlt] at hz
  have hneg_eq : Sneg.card = Spos.card := by
    refine Finset.card_bij (fun z _ => fun j => z j + 1) ?_ ?_ ?_
    · intro z hz
      simp only [Sneg, Spos, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      have hflip : (∑ j : Fin m, chi (z j + 1)) = -(∑ j : Fin m, chi (z j)) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [chi_add, chi_one]; ring
      rwa [hflip]
    · intro z₁ _ z₂ _ h
      ext j
      have hj := congrFun h j
      have hj' : z₁ j + 1 + 1 = z₂ j + 1 + 1 := congrArg (· + 1) hj
      simp only [add_assoc, zmod2_add_self, add_zero] at hj'
      exact hj'
    · intro z hz
      refine ⟨fun j => z j + 1, ?_, ?_⟩
      · simp only [Sneg, Spos, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
        have hflip : (∑ j : Fin m, chi (z j + 1)) = -(∑ j : Fin m, chi (z j)) := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [chi_add, chi_one]; ring
        rw [hflip, neg_neg]
        exact hz
      · ext j
        simp only [add_assoc, zmod2_add_self, add_zero]
  calc
    (Finset.univ.filter (fun z : Fin m → F2 => (m : ℤ) < 14 * |∑ j : Fin m, chi (z j)|)).card
        ≤ (Spos ∪ Sneg).card := Finset.card_le_card hsub
    _ ≤ Spos.card + Sneg.card := Finset.card_union_le _ _
    _ = 2 * Spos.card := by rw [hneg_eq]; ring

lemma bias_arith_helper (k m : ℕ) (hk : 64 ≤ k) (hm : 512 * k ≤ m) :
    let q := m / 28
    4 * 2 ^ k * 28 ^ m < 2 ^ m * 15 ^ (15 * q) * 13 ^ (m - 15 * q) := by
  intro q
  let r := m % 28
  have hmr : m = 28 * q + r := (Nat.div_add_mod m 28).symm
  have hrlt : r < 28 := Nat.mod_lt m (by norm_num)
  have hsub : m - 15 * q = 13 * q + r := by omega
  have hq : 18 * k ≤ q := by omega
  have h1 : 16 * 14 ^ 28 ≤ 15 * (15 ^ 15 * 13 ^ 13) := by norm_num
  have h2 : 3 * 15 ^ 18 ≤ 16 ^ 18 := by norm_num
  have h3 : 14 ^ 27 < 8 * 13 ^ 27 := by norm_num
  have h4 : 32 * 2 ^ 10 < 3 ^ 10 := by norm_num
  have hr_pow : 14 ^ r ≤ 8 * 13 ^ r := by
    have hstep : 14 ^ r * 13 ^ (27 - r) ≤ 14 ^ r * 14 ^ (27 - r) := by
      gcongr; norm_num
    have hmul : 14 ^ r * 13 ^ (27 - r) < 8 * 13 ^ r * 13 ^ (27 - r) := by
      calc
        14 ^ r * 13 ^ (27 - r) ≤ 14 ^ r * 14 ^ (27 - r) := hstep
        _ = 14 ^ (r + (27 - r)) := (pow_add 14 r (27 - r)).symm
        _ = 14 ^ 27 := by rw [Nat.add_sub_cancel' (by omega)]
        _ < 8 * 13 ^ 27 := h3
        _ = 8 * 13 ^ (r + (27 - r)) := by rw [Nat.add_sub_cancel' (by omega)]
        _ = 8 * 13 ^ r * 13 ^ (27 - r) := by rw [pow_add]; ring
    exact le_of_lt (Nat.lt_of_mul_lt_mul_right hmul)
  have hq_pow : 16 ^ q * (14 ^ 28) ^ q ≤ 15 ^ q * (15 ^ 15 * 13 ^ 13) ^ q := by
    rw [← mul_pow, ← mul_pow]
    exact Nat.pow_le_pow_left h1 q
  have h15_16 : 3 ^ k * 15 ^ q ≤ 16 ^ q := by
    have h18 : 3 ^ k * (15 ^ 18) ^ k ≤ (16 ^ 18) ^ k := by
      rw [← mul_pow]
      exact Nat.pow_le_pow_left h2 k
    have hle : 15 ^ (q - 18 * k) ≤ 16 ^ (q - 18 * k) := Nat.pow_le_pow_left (by norm_num) _
    calc
      3 ^ k * 15 ^ q = 3 ^ k * 15 ^ (18 * k + (q - 18 * k)) := by
            rw [Nat.add_sub_cancel' hq]
      _ = (3 ^ k * (15 ^ 18) ^ k) * 15 ^ (q - 18 * k) := by rw [pow_add, pow_mul]; ring
      _ ≤ (16 ^ 18) ^ k * 16 ^ (q - 18 * k) := Nat.mul_le_mul h18 hle
      _ = 16 ^ (18 * k + (q - 18 * k)) := by rw [← pow_mul, ← pow_add]
      _ = 16 ^ q := by rw [Nat.add_sub_cancel' hq]
  have hk_pow : 32 * 2 ^ k < 3 ^ k := by
    have hrem : 2 ^ (k - 10) ≤ 3 ^ (k - 10) := Nat.pow_le_pow_left (by norm_num) _
    calc
      32 * 2 ^ k = 32 * 2 ^ (10 + (k - 10)) := by rw [Nat.add_sub_cancel' (by omega)]
      _ = (32 * 2 ^ 10) * 2 ^ (k - 10) := by rw [pow_add]; ring
      _ < 3 ^ 10 * 3 ^ (k - 10) := Nat.mul_lt_mul_of_lt_of_le h4 hrem (by positivity)
      _ = 3 ^ (10 + (k - 10)) := (pow_add 3 10 (k - 10)).symm
      _ = 3 ^ k := by rw [Nat.add_sub_cancel' (by omega)]
  have hmain : 4 * 2 ^ k * 14 ^ m < 15 ^ (15 * q) * 13 ^ (m - 15 * q) := by
    have hpos16 : 0 < 16 ^ q := by positivity
    suffices hs : 16 ^ q * (4 * 2 ^ k * 14 ^ m) < 16 ^ q * (15 ^ (15 * q) * 13 ^ (m - 15 * q)) by
      exact Nat.lt_of_mul_lt_mul_left hs
    rw [hsub]
    have h14m : 14 ^ m = (14 ^ 28) ^ q * 14 ^ r := by
      conv_lhs => rw [hmr, pow_add, pow_mul]
    have h1513 : 15 ^ (15 * q) * 13 ^ (13 * q + r) = (15 ^ 15 * 13 ^ 13) ^ q * 13 ^ r := by
      rw [pow_add, mul_pow, ← pow_mul, ← pow_mul]; ring
    rw [h14m, h1513]
    calc
      16 ^ q * (4 * 2 ^ k * ((14 ^ 28) ^ q * 14 ^ r))
          = (4 * 2 ^ k * 14 ^ r) * (16 ^ q * (14 ^ 28) ^ q) := by ring
      _ ≤ (4 * 2 ^ k * (8 * 13 ^ r)) * (15 ^ q * (15 ^ 15 * 13 ^ 13) ^ q) := by
            exact Nat.mul_le_mul (by gcongr) hq_pow
      _ = (32 * 2 ^ k) * (15 ^ q * ((15 ^ 15 * 13 ^ 13) ^ q * 13 ^ r)) := by ring
      _ < 3 ^ k * (15 ^ q * ((15 ^ 15 * 13 ^ 13) ^ q * 13 ^ r)) := by
            exact Nat.mul_lt_mul_of_pos_right hk_pow (by positivity)
      _ = (3 ^ k * 15 ^ q) * ((15 ^ 15 * 13 ^ 13) ^ q * 13 ^ r) := by ring
      _ ≤ 16 ^ q * ((15 ^ 15 * 13 ^ 13) ^ q * 13 ^ r) := by
            exact Nat.mul_le_mul_right _ h15_16
  have h28 : 28 ^ m = 2 ^ m * 14 ^ m := by
    have : (28 : ℕ) = 2 * 14 := by norm_num
    rw [this, mul_pow]
  rw [h28]
  calc
    4 * 2 ^ k * (2 ^ m * 14 ^ m) = 2 ^ m * (4 * 2 ^ k * 14 ^ m) := by ring
    _ < 2 ^ m * (15 ^ (15 * q) * 13 ^ (m - 15 * q)) :=
          Nat.mul_lt_mul_of_pos_left hmain (by positivity)
    _ = 2 ^ m * 15 ^ (15 * q) * 13 ^ (m - 15 * q) := by ring

def psiBuild (k m : ℕ) (w : Fin k → F2) (i₀ : Fin k) (z : Fin m → F2) (n : ℕ) : F2 :=
  if h1 : i₀.val ≤ n ∧ n < i₀.val + m then
    z ⟨n - i₀.val, by omega⟩ +
      (Finset.univ.filter (fun i : Fin k => i.val < i₀.val)).attach.sum (fun p =>
        w p.1 * psiBuild k m w i₀ z (n - i₀.val + p.1.val))
  else 0
termination_by n
decreasing_by
  have hi := (Finset.mem_filter.mp p.2).2
  omega

lemma psiMap_surj (k m : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m) (w : Fin k → F2) (hw : w ≠ 0) :
    Function.Surjective (fun b : Fin (k + m - 1) → F2 =>
      fun j : Fin m => dotProduct w (tapeVec k m hk hm b j)) := by
  have hex : ∃ i : Fin k, w i = 1 := by
    by_contra h
    push_neg at h
    apply hw
    ext i
    rcases zmod2_eq_zero_or_one (w i) with h0 | h1
    · exact h0
    · exact (h i h1).elim
  let supp := Finset.univ.filter (fun i : Fin k => w i = 1)
  have hsupp_ne : supp.Nonempty := by
    rcases hex with ⟨i, hi⟩
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  let i₀ : Fin k := supp.max' hsupp_ne
  have hi₀_mem : w i₀ = 1 := (Finset.mem_filter.mp (Finset.max'_mem supp hsupp_ne)).2
  have hi₀_max : ∀ i : Fin k, i₀ < i → w i = 0 := by
    intro i hi
    rcases zmod2_eq_zero_or_one (w i) with h0 | h1
    · exact h0
    · have hle : i ≤ i₀ := Finset.le_max' supp i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h1⟩)
      exact absurd hi (not_lt_of_ge hle)
  intro z
  let build : ℕ → F2 := psiBuild k m w i₀ z
  let b : Fin (k + m - 1) → F2 := fun r => build r.val
  refine ⟨b, ?_⟩
  ext j
  change dotProduct w (tapeVec k m hk hm b j) = z j
  simp only [dotProduct, tapeVec, b]
  have hsplit : (∑ i : Fin k, w i * build (j.val + i.val)) =
      w i₀ * build (j.val + i₀.val) +
        ∑ i ∈ Finset.univ.filter (fun i : Fin k => i.val < i₀.val),
          w i * build (j.val + i.val) := by
    have hzero : ∀ i : Fin k, i₀.val < i.val → w i * build (j.val + i.val) = 0 := by
      intro i hi
      rw [hi₀_max i hi, zero_mul]
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.filter (fun i : Fin k => i.val ≤ i₀.val)))]
    · have heq : Finset.univ.filter (fun i : Fin k => i.val ≤ i₀.val) =
          insert i₀ (Finset.univ.filter (fun i : Fin k => i.val < i₀.val)) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
        omega
      rw [heq, Finset.sum_insert]
      simp
    · intro i _ hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hi
      exact hzero i hi
  rw [hsplit, hi₀_mem, one_mul]
  have hbuild_eq : build (j.val + i₀.val) =
      z j + ∑ i ∈ Finset.univ.filter (fun i : Fin k => i.val < i₀.val),
        w i * build (j.val + i.val) := by
    dsimp only [build]
    rw [psiBuild]
    have hcond : i₀.val ≤ j.val + i₀.val ∧ j.val + i₀.val < i₀.val + m := ⟨by omega, by omega⟩
    rw [dif_pos hcond]
    have hj_sub : (⟨j.val + i₀.val - i₀.val, by omega⟩ : Fin m) = j := by
      ext; simp
    rw [hj_sub]
    congr 1
    rw [← Finset.sum_attach (Finset.univ.filter (fun i : Fin k => i.val < i₀.val))]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    have hidx : j.val + i₀.val - i₀.val + p.1.val = j.val + p.1.val := by omega
    rw [hidx]
  rw [hbuild_eq, add_assoc, zmod2_add_self, add_zero]

lemma exists_good_tape (k m : ℕ) (hk : 64 ≤ k) (hm1 : 512 * k ≤ m) :
    ∃ s : Fin (2 ^ (k + m - 1)),
      let v : Fin m → Fin k → F2 := fun j i => if s.val.testBit (j.val + i.val) then 1 else 0
      ∀ w : Fin k → F2, w ≠ 0 →
        14 * |∑ j : Fin m, chi (dotProduct w (v j))| ≤ (m : ℤ) := by
  have hk1 : 1 ≤ k := by omega
  have hm0 : 1 ≤ m := by omega
  let N := k + m - 1
  let badBias : Finset (Fin N → F2) :=
    Finset.univ.filter (fun b =>
      ∃ w : Fin k → F2, w ≠ 0 ∧
        (m : ℤ) < 14 * |∑ j : Fin m, chi (dotProduct w (tapeVec k m hk1 hm0 b j))|)
  have hbadBias : badBias.card * 2 < 2 ^ N := by
    let badW : (Fin k → F2) → Finset (Fin N → F2) := fun w =>
      Finset.univ.filter (fun b => (m : ℤ) < 14 * |∑ j : Fin m, chi (dotProduct w (tapeVec k m hk1 hm0 b j))|)
    have hsub : badBias ⊆ (Finset.univ.filter (fun w : Fin k → F2 => w ≠ 0)).biUnion badW := by
      intro b hb
      simp only [badBias, Finset.mem_filter, Finset.mem_univ, true_and] at hb
      rcases hb with ⟨w, hw, hgt⟩
      exact Finset.mem_biUnion.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ w, hw⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ b, hgt⟩⟩
    have hperW : ∀ w : Fin k → F2, w ≠ 0 →
        (badW w).card * 2 ^ m =
          (Finset.univ.filter (fun z : Fin m → F2 => (m : ℤ) < 14 * |∑ j : Fin m, chi (z j)|)).card *
            2 ^ N := by
      intro w hw
      have hadd : ∀ b₁ b₂ : Fin N → F2,
          (fun j : Fin m => dotProduct w (tapeVec k m hk1 hm0 (b₁ + b₂) j)) =
          (fun j : Fin m => dotProduct w (tapeVec k m hk1 hm0 b₁ j)) +
          (fun j : Fin m => dotProduct w (tapeVec k m hk1 hm0 b₂ j)) := by
        intro b₁ b₂; ext j
        simp only [Pi.add_apply, dotProduct, tapeVec, mul_add, Finset.sum_add_distrib]
      exact add_surj_preimage_card _ hadd (psiMap_surj k m hk1 hm0 w hw)
        (fun z : Fin m → F2 => (m : ℤ) < 14 * |∑ j : Fin m, chi (z j)|)
    let Mabs := (Finset.univ.filter (fun z : Fin m → F2 => (m : ℤ) < 14 * |∑ j : Fin m, chi (z j)|)).card
    let Mpos := (Finset.univ.filter (fun z : Fin m → F2 => (m : ℤ) < 14 * (∑ j : Fin m, chi (z j)))).card
    have hsum_le : badBias.card * 2 ^ m ≤ 2 ^ k * (Mabs * 2 ^ N) := by
      calc
        badBias.card * 2 ^ m
            ≤ ((Finset.univ.filter (fun w : Fin k → F2 => w ≠ 0)).biUnion badW).card * 2 ^ m :=
              Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
        _ ≤ (∑ w ∈ Finset.univ.filter (fun w : Fin k → F2 => w ≠ 0), (badW w).card) * 2 ^ m :=
              Nat.mul_le_mul_right _ Finset.card_biUnion_le
        _ = ∑ w ∈ Finset.univ.filter (fun w : Fin k → F2 => w ≠ 0), ((badW w).card * 2 ^ m) :=
              Finset.sum_mul _ _ _
        _ = ∑ w ∈ Finset.univ.filter (fun w : Fin k → F2 => w ≠ 0), (Mabs * 2 ^ N) := by
              refine Finset.sum_congr rfl (fun w hw => ?_)
              exact hperW w (Finset.mem_filter.mp hw).2
        _ = (Finset.univ.filter (fun w : Fin k → F2 => w ≠ 0)).card * (Mabs * 2 ^ N) := by
              rw [Finset.sum_const, smul_eq_mul]
        _ ≤ 2 ^ k * (Mabs * 2 ^ N) := by
              refine Nat.mul_le_mul_right _ ?_
              calc
                (Finset.univ.filter (fun w : Fin k → F2 => w ≠ 0)).card
                    ≤ (Finset.univ : Finset (Fin k → F2)).card := Finset.card_filter_le _ _
                _ = 2 ^ k := by simp [Fintype.card_fun, ZMod.card]
    let q := m / 28
    have hMabs : Mabs ≤ 2 * Mpos := bias_abs_card_bound m
    have hMpos : Mpos * 15 ^ (15 * q) * 13 ^ (m - 15 * q) ≤ 28 ^ m := bias_pos_card_bound m
    have harith := bias_arith_helper k m hk hm1
    have hprod_lt : badBias.card * 2 * (2 ^ m * 15 ^ (15 * q) * 13 ^ (m - 15 * q)) <
        2 ^ N * (2 ^ m * 15 ^ (15 * q) * 13 ^ (m - 15 * q)) := by
      calc
        badBias.card * 2 * (2 ^ m * 15 ^ (15 * q) * 13 ^ (m - 15 * q))
            = (badBias.card * 2 ^ m) * (2 * 15 ^ (15 * q) * 13 ^ (m - 15 * q)) := by ring
        _ ≤ (2 ^ k * (Mabs * 2 ^ N)) * (2 * 15 ^ (15 * q) * 13 ^ (m - 15 * q)) :=
              Nat.mul_le_mul_right _ hsum_le
        _ ≤ (2 ^ k * (2 * Mpos * 2 ^ N)) * (2 * 15 ^ (15 * q) * 13 ^ (m - 15 * q)) := by gcongr
        _ = 2 ^ N * (4 * 2 ^ k * (Mpos * 15 ^ (15 * q) * 13 ^ (m - 15 * q))) := by ring
        _ ≤ 2 ^ N * (4 * 2 ^ k * 28 ^ m) := by gcongr
        _ < 2 ^ N * (2 ^ m * 15 ^ (15 * q) * 13 ^ (m - 15 * q)) :=
              Nat.mul_lt_mul_of_pos_left harith (by positivity)
    exact Nat.lt_of_mul_lt_mul_right hprod_lt
  have hbad_lt : badBias.card < (Finset.univ : Finset (Fin N → F2)).card := by
    have hcard : (Finset.univ : Finset (Fin N → F2)).card = 2 ^ N := by
      simp [Fintype.card_fun, ZMod.card]
    rw [hcard]
    omega
  have hne : (Finset.univ \ badBias).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hsub : (Finset.univ : Finset (Fin N → F2)) ⊆ badBias :=
      Finset.sdiff_eq_empty_iff_subset.mp hemp
    exact not_le_of_gt hbad_lt (Finset.card_le_card hsub)
  rcases hne with ⟨b, hb⟩
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hb
  let s : Fin (2 ^ N) := ⟨bitsToNat b, bitsToNat_lt b⟩
  refine ⟨s, ?_⟩
  dsimp only
  intro w hw
  simp only [badBias, Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_and,
    not_lt] at hb
  have hvec : ∀ (j : Fin m) (i : Fin k),
      (if s.val.testBit (j.val + i.val) then (1 : F2) else 0) =
      tapeVec k m hk1 hm0 b j i := fun j i => bitsToNat_fin_testBit b (j.val + i.val) (by omega)
  have hres := hb w hw
  have heq : (∑ j : Fin m, chi (dotProduct w (fun i => if s.val.testBit (j.val + i.val) then (1 : F2) else 0))) =
      ∑ j : Fin m, chi (dotProduct w (tapeVec k m hk1 hm0 b j)) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    congr 2; ext i; exact hvec j i
  rw [heq]
  exact hres

end Tape

namespace Partition

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


lemma add_add_self {k : ℕ} (x d : Fin k → ZMod 2) : x + d + d = x := by
  funext l
  simp only [Pi.add_apply]
  generalize x l = a; generalize d l = b
  revert a b; decide

lemma half_card {k : ℕ} (Q : Finset (Fin k → ZMod 2)) (d : Fin k → ZMod 2)
    (P : (Fin k → ZMod 2) → Prop) [DecidablePred P]
    (hQ : ∀ x ∈ Q, x + d ∈ Q) (hP : ∀ x ∈ Q, (P (x + d) ↔ ¬ P x)) :
    2 * (Q.filter P).card = Q.card := by
  have h1 : (Q.filter P).card = (Q.filter (fun x => ¬ P x)).card := by
    apply Finset.card_bij' (fun x _ => x + d) (fun x _ => x + d)
    · intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hQ x hx.1, by rw [hP x hx.1]; exact not_not.mpr hx.2⟩
    · intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      refine ⟨hQ x hx.1, ?_⟩
      have := hP x hx.1
      tauto
    · intro x _; exact add_add_self x d
    · intro x _; exact add_add_self x d
  have h2 := Finset.card_filter_add_card_filter_not (s := Q) P
  omega


lemma sep {k : ℕ} (D : Submodule (ZMod 2) (Fin k → ZMod 2)) (u : Fin k → ZMod 2) (hu : u ∉ D) :
    ∃ d : Fin k → ZMod 2, (∀ δ ∈ D, δ ⬝ᵥ d = 0) ∧ u ⬝ᵥ d ≠ 0 := by
  obtain ⟨f, hf, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hu inferInstance
  have key : ∀ z : Fin k → ZMod 2,
      z ⬝ᵥ (fun i => f (fun j => if i = j then 1 else 0)) = f z := by
    intro z
    rw [LinearMap.pi_apply_eq_sum_univ f z]
    simp [dotProduct, smul_eq_mul]
  refine ⟨fun i => f (fun j => if i = j then 1 else 0), ?_, ?_⟩
  · intro δ hδ
    rw [key]
    have : f δ ∈ D.map f := Submodule.mem_map_of_mem hδ
    rw [hmap] at this
    simpa using this
  · rw [key]; exact hf


lemma z2_neg (a c : ZMod 2) : (!decide (a + c = 1)) = decide (a + (c + 1) = 1) := by
  revert a c; decide

lemma z2_xnor (a b c c' : ZMod 2) :
    (!(xor (decide (a + c = 1)) (decide (b + c' = 1)))) = decide (a + b + (c + c' + 1) = 1) := by
  revert a b c c'; decide

lemma z2_three (α β γ c : ZMod 2) (b : Bool) (h1 : decide (α + c = 1) = b)
    (h2 : decide (β + c = 1) = b) (h3 : decide (γ + c = 1) = b) :
    decide (α + β + γ + c = 1) = b := by
  revert h1 h2 h3; revert α β γ c b; decide

lemma z2_flip (α β γ c : ZMod 2) (h : decide (β + c = 1) ≠ decide (γ + c = 1)) :
    decide (α + (β + γ) + c = 1) = !decide (α + c = 1) := by
  revert h; revert α β γ c; decide

lemma z2_nc (α β c : ZMod 2) (h : decide (α + c = 1) = decide (α + β + c = 1)) (hb : β ≠ 0) :
    False := by
  revert h hb; revert α β c; decide

lemma z2_agree (α β γ δ c e : ZMod 2) (h : δ - β ≠ 0) :
    (decide (α + β + c = 1) = decide (γ + δ + e = 1)) ↔
      ¬ (decide (α + c = 1) = decide (γ + e = 1)) := by
  revert h; revert α β γ δ c e; decide

lemma z2_bit (x : ZMod 2) : (if decide (x = 1) = true then (1 : ZMod 2) else 0) = x := by
  revert x; decide


def AffOn {k : ℕ} (Q : Finset (Fin k → ZMod 2)) (f : (Fin k → ZMod 2) → Bool) (r : Fin k → ZMod 2)
    (D : Submodule (ZMod 2) (Fin k → ZMod 2)) : Prop :=
  ∃ (lam : Fin k → ZMod 2) (c : ZMod 2), lam - r ∈ D ∧ ∀ x ∈ Q, f x = decide (lam ⬝ᵥ x + c = 1)

lemma AffOn.mono {k : ℕ} {Q Q' : Finset (Fin k → ZMod 2)} {f : (Fin k → ZMod 2) → Bool}
    {r : Fin k → ZMod 2} {D D' : Submodule (ZMod 2) (Fin k → ZMod 2)}
    (h : AffOn Q f r D) (hQ : Q' ⊆ Q) (hD : D ≤ D') : AffOn Q' f r D' := by
  obtain ⟨lam, c, h1, h2⟩ := h
  exact ⟨lam, c, hD h1, fun x hx => h2 x (hQ hx)⟩

lemma AffOn.congr {k : ℕ} {Q : Finset (Fin k → ZMod 2)} {f f' : (Fin k → ZMod 2) → Bool}
    {r : Fin k → ZMod 2} {D : Submodule (ZMod 2) (Fin k → ZMod 2)}
    (h : AffOn Q f' r D) (he : ∀ x ∈ Q, f x = f' x) : AffOn Q f r D := by
  obtain ⟨lam, c, h1, h2⟩ := h
  exact ⟨lam, c, h1, fun x hx => (he x hx).trans (h2 x hx)⟩

lemma AffOn.shift {k : ℕ} {Q : Finset (Fin k → ZMod 2)} {f : (Fin k → ZMod 2) → Bool}
    {r r' : Fin k → ZMod 2} {D : Submodule (ZMod 2) (Fin k → ZMod 2)}
    (h : AffOn Q f r D) (hr : r - r' ∈ D) : AffOn Q f r' D := by
  obtain ⟨lam, c, h1, h2⟩ := h
  refine ⟨lam, c, ?_, h2⟩
  have : lam - r' = (lam - r) + (r - r') := by abel
  rw [this]; exact D.add_mem h1 hr

lemma AffOn.const {k : ℕ} (Q : Finset (Fin k → ZMod 2)) (f : (Fin k → ZMod 2) → Bool)
    (r : Fin k → ZMod 2) (D : Submodule (ZMod 2) (Fin k → ZMod 2)) (b : Bool)
    (hf : ∀ x ∈ Q, f x = b) (hr : r ∈ D) : AffOn Q f r D := by
  refine ⟨0, if b then 1 else 0, by simpa using D.neg_mem hr, fun x hx => ?_⟩
  rw [hf x hx]; cases b <;> simp

lemma AffOn.neg {k : ℕ} {Q : Finset (Fin k → ZMod 2)} {f : (Fin k → ZMod 2) → Bool}
    {r : Fin k → ZMod 2} {D : Submodule (ZMod 2) (Fin k → ZMod 2)}
    (h : AffOn Q f r D) : AffOn Q (fun x => !(f x)) r D := by
  obtain ⟨lam, c, h1, h2⟩ := h
  refine ⟨lam, c + 1, h1, fun x hx => ?_⟩
  show (!(f x)) = _
  rw [h2 x hx]
  exact z2_neg _ _

lemma AffOn.xnor {k : ℕ} {Q : Finset (Fin k → ZMod 2)} {f f' : (Fin k → ZMod 2) → Bool}
    {r r' : Fin k → ZMod 2} {D : Submodule (ZMod 2) (Fin k → ZMod 2)}
    (h : AffOn Q f r D) (h' : AffOn Q f' r' D) :
    AffOn Q (fun x => !(xor (f x) (f' x))) (r + r') D := by
  obtain ⟨lam, c, h1, h2⟩ := h
  obtain ⟨lam', c', h1', h2'⟩ := h'
  refine ⟨lam + lam', c + c' + 1, ?_, fun x hx => ?_⟩
  · have : lam + lam' - (r + r') = (lam - r) + (lam' - r') := by abel
    rw [this]; exact D.add_mem h1 h1'
  · show (!(xor (f x) (f' x))) = _
    rw [h2 x hx, h2' x hx, add_dotProduct]
    exact z2_xnor _ _ _ _


def inp (k t : ℕ) (x : Fin k → ZMod 2) (a : Fin t → Bool) : List Bool :=
  List.ofFn (fun l : Fin k => decide (x l = 1)) ++ List.ofFn a

lemma inp_length (k t : ℕ) (x : Fin k → ZMod 2) (a : Fin t → Bool) :
    (inp k t x a).length = k + t := by simp [inp]

def wv {k t : ℕ} (I : (Fin k → ZMod 2) → (Fin t → Bool) → List Bool) (gs : List Gate) (a : Fin t → Bool) (w : ℕ) (x : Fin k → ZMod 2) : Bool :=
  (run gs (I x a)).getD w false

def Inv {k t : ℕ} (I : (Fin k → ZMod 2) → (Fin t → Bool) → List Bool) (gs : List Gate) (i : ℕ) : Prop :=
  ∃ (Q : (Fin t → Bool) → (Fin i → Bool) → Finset (Fin k → ZMod 2))
    (wt : (Fin t → Bool) → (Fin i → Bool) → ℕ)
    (D : (Fin i → Bool) → Submodule (ZMod 2) (Fin k → ZMod 2))
    (r : (Fin i → Bool) → ℕ → (Fin k → ZMod 2)),
    (∀ ξ, Module.finrank (ZMod 2) (D ξ) ≤ i) ∧
    (∀ a ξ, ∀ x ∈ Q a ξ, ∀ y ∈ Q a ξ, ∀ z ∈ Q a ξ, x + y + z ∈ Q a ξ) ∧
    (∀ a ξ, ∀ x ∈ Q a ξ, ∀ d : Fin k → ZMod 2, (∀ δ ∈ D ξ, δ ⬝ᵥ d = 0) → x + d ∈ Q a ξ) ∧
    (∀ a ξ, wt a ξ * (Q a ξ).card = 2^k) ∧
    (∀ a (φ : (Fin k → ZMod 2) → ℕ), 2^i * ∑ x, φ x = ∑ ξ, wt a ξ * ∑ x ∈ Q a ξ, φ x) ∧
    (∀ a ξ w, AffOn (Q a ξ) (wv I gs a w) (r ξ w) (D ξ))

lemma card_fun_zmod (k : ℕ) : (Finset.univ : Finset (Fin k → ZMod 2)).card = 2^k := by
  rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]

lemma inv_nil {k t : ℕ} (I : (Fin k → ZMod 2) → (Fin t → Bool) → List Bool)
    (r : ℕ → Fin k → ZMod 2)
    (hinit : ∀ a w, AffOn Finset.univ (fun x => (I x a).getD w false) (r w) ⊥) :
    Inv I [] 0 := by
  refine ⟨fun _ _ => Finset.univ, fun _ _ => 1, fun _ => ⊥, fun _ => r, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ξ; simp
  · intro a ξ x _ y _ z _; exact Finset.mem_univ _
  · intro a ξ x _ d _; exact Finset.mem_univ _
  · intro a ξ; rw [one_mul, card_fun_zmod]
  · intro a φ; simp
  · intro a ξ w; exact hinit a w


lemma free_aff {k : ℕ} (g : Gate) (hl : legalG g) (hc : counted g = false)
    (Q : Finset (Fin k → ZMod 2)) (f : ℕ → (Fin k → ZMod 2) → Bool) (r : ℕ → (Fin k → ZMod 2))
    (D : Submodule (ZMod 2) (Fin k → ZMod 2)) (h : ∀ w, AffOn Q (f w) (r w) D) :
    AffOn Q (fun x => g.op.eval (g.inputs.map fun i => f i x)) (g.inputs.map r).sum D := by
  obtain ⟨hlen, hop⟩ := hl
  have hc' : ¬ ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) := by
    simpa [counted] using hc
  obtain ⟨op, ins⟩ := g
  simp only at hlen hop hc' ⊢
  rcases ins with _ | ⟨p, _ | ⟨q, _ | ⟨z, rest⟩⟩⟩
  · exact AffOn.const _ _ _ _ (op.eval []) (fun x _ => rfl) (by simp)
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rcases hop with rfl | rfl | rfl | ⟨rfl, _⟩
    · exact (h p).congr (fun x _ => by simp [GateOp.eval])
    · exact (h p).congr (fun x _ => by simp [GateOp.eval])
    · exact (h p).neg.congr (fun x _ => eval_mod2_one _)
    · exact (h p).neg.congr (fun x _ => rfl)
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rcases hop with rfl | rfl | rfl | ⟨rfl, h1⟩
    · exact absurd ⟨Or.inl rfl, rfl⟩ hc'
    · exact absurd ⟨Or.inr rfl, rfl⟩ hc'
    · exact ((h p).xnor (h q)).congr (fun x _ => eval_mod2_two _ _)
    · simp at h1
  · simp at hlen

lemma run_snoc (gs : List Gate) (g : Gate) (W : List Bool) :
    run (gs ++ [g]) W = stp (run gs W) g := by
  rw [run_append]; rfl

lemma wv_snoc {k t : ℕ} (I : (Fin k → ZMod 2) → (Fin t → Bool) → List Bool)
    (L : ℕ) (hI : ∀ x a, (I x a).length = L) (gs : List Gate) (g : Gate) (a : Fin t → Bool) (w : ℕ)
    (x : Fin k → ZMod 2) :
    wv I (gs ++ [g]) a w x = if w = L + gs.length then
      g.op.eval (g.inputs.map fun i => wv I gs a i x) else wv I gs a w x := by
  unfold wv
  rw [run_snoc, stp, getD_snoc, run_length, hI]

lemma inv_free {k t : ℕ} (I : (Fin k → ZMod 2) → (Fin t → Bool) → List Bool)
    (L : ℕ) (hI : ∀ x a, (I x a).length = L) (gs : List Gate) (g : Gate) (i : ℕ) (hl : legalG g)
    (hc : counted g = false) (hinv : Inv I gs i) : Inv I (gs ++ [g]) i := by
  obtain ⟨Q, wt, D, r, hD, hflat, hperp, hwt, hsum, haff⟩ := hinv
  refine ⟨Q, wt, D, fun ξ w => if w = L + gs.length then (g.inputs.map (r ξ)).sum else r ξ w,
    hD, hflat, hperp, hwt, hsum, ?_⟩
  intro a ξ w
  by_cases hw : w = L + gs.length
  · simp only [if_pos hw]
    refine (free_aff g hl hc _ (fun i x => wv I gs a i x) _ _ (fun w => haff a ξ w)).congr ?_
    intro x _
    rw [wv_snoc I L hI, if_pos hw]
  · simp only [if_neg hw]
    refine (haff a ξ w).congr ?_
    intro x _
    rw [wv_snoc I L hI, if_neg hw]

lemma finrank_sup_span_le {k : ℕ} (D : Submodule (ZMod 2) (Fin k → ZMod 2)) (u : Fin k → ZMod 2) :
    Module.finrank (ZMod 2) ↥(D ⊔ Submodule.span (ZMod 2) {u}) ≤ Module.finrank (ZMod 2) D + 1 := by
  have h1 := Submodule.finrank_add_le_finrank_add_finrank D (Submodule.span (ZMod 2) {u})
  have h2 : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) ({u} : Set (Fin k → ZMod 2))) ≤ 1 := by
    have := finrank_span_le_card (R := ZMod 2) ({u} : Set (Fin k → ZMod 2))
    simpa using this
  omega

lemma sum_cons_bool {i : ℕ} (G : (Fin (i+1) → Bool) → ℕ) :
    ∑ ξ', G ξ' = ∑ ξ : Fin i → Bool, (G (Fin.cons true ξ) + G (Fin.cons false ξ)) := by
  rw [← (Fin.consEquiv (fun _ => Bool)).sum_comp, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl (fun ξ _ => ?_)
  rw [Fintype.sum_bool]; rfl

lemma aff_gate_split {k : ℕ} {Q Q' : Finset (Fin k → ZMod 2)} (hsub : Q' ⊆ Q)
    {D D' : Submodule (ZMod 2) (Fin k → ZMod 2)} (hDD : D ≤ D')
    (pv qv val : (Fin k → ZMod 2) → Bool) (ia pc : Bool) (rq ref : Fin k → ZMod 2)
    (hq : AffOn Q qv rq D) (hpc : ∀ x ∈ Q', pv x = pc)
    (hval : ∀ x ∈ Q', val x = if ia then (pv x && qv x) else (pv x || qv x))
    (href1 : ia = pc → rq - ref ∈ D') (href2 : ia ≠ pc → ref ∈ D') : AffOn Q' val ref D' := by
  cases ia <;> cases pc
  · exact ((hq.mono hsub hDD).shift (href1 rfl)).congr
      (fun x hx => by rw [hval x hx, hpc x hx]; simp)
  · exact AffOn.const _ _ _ _ true (fun x hx => by rw [hval x hx, hpc x hx]; simp)
      (href2 (by decide))
  · exact AffOn.const _ _ _ _ false (fun x hx => by rw [hval x hx, hpc x hx]; simp)
      (href2 (by decide))
  · exact ((hq.mono hsub hDD).shift (href1 rfl)).congr
      (fun x hx => by rw [hval x hx, hpc x hx]; simp)

lemma inv_counted {k t : ℕ} (I : (Fin k → ZMod 2) → (Fin t → Bool) → List Bool)
    (L : ℕ) (hI : ∀ x a, (I x a).length = L) (gs : List Gate) (g : Gate) (i : ℕ) (hc : counted g = true)
    (hinv : Inv I gs i) : Inv I (gs ++ [g]) (i+1) := by
  classical
  obtain ⟨Q, wt, D, r, hD, hflat, hperp, hwt, hsum, haff⟩ := hinv
  have hc' : (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 := by simpa [counted] using hc
  obtain ⟨hop, hlen⟩ := hc'
  obtain ⟨p, q, hpq⟩ : ∃ p q, g.inputs = [p, q] := by
    rcases h : g.inputs with _ | ⟨p, _ | ⟨q, _ | ⟨_, _⟩⟩⟩ <;> rw [h] at hlen <;> simp at hlen
    exact ⟨p, q, rfl⟩
  have hval : ∀ a x, wv I (gs ++ [g]) a (L + gs.length) x =
      if decide (g.op = .and) then (wv I gs a p x && wv I gs a q x)
      else (wv I gs a p x || wv I gs a q x) := by
    intro a x
    rw [wv_snoc I L hI, if_pos rfl, hpq]
    rcases hop with h | h <;> simp [h, eval_and_two, eval_or_two]
  let isC : (Fin t → Bool) → (Fin i → Bool) → Prop := fun a ξ =>
    ∀ x ∈ Q a ξ, ∀ y ∈ Q a ξ, wv I gs a p x = wv I gs a p y
  let selD : (Fin i → Bool) → (Fin k → ZMod 2) := fun ξ => if r ξ p ∈ D ξ then r ξ q else r ξ p
  have hrp : ∀ ξ, r ξ p ∈ D ξ ⊔ Submodule.span (ZMod 2) {selD ξ} := by
    intro ξ
    by_cases h : r ξ p ∈ D ξ
    · exact Submodule.mem_sup_left h
    · apply Submodule.mem_sup_right
      simp only [selD, if_neg h]
      exact Submodule.mem_span_singleton_self _
  have hnc : ∀ a ξ, r ξ p ∉ D ξ → ¬ isC a ξ := by
    intro a ξ hA hC
    obtain ⟨lam, c, h1, h2⟩ := haff a ξ p
    have hlam : lam ∉ D ξ := by
      intro hl
      apply hA
      have : r ξ p = lam - (lam - r ξ p) := by abel
      rw [this]; exact (D ξ).sub_mem hl h1
    obtain ⟨d, hd, hld⟩ := sep (D ξ) lam hlam
    have hne : (Q a ξ).Nonempty := by
      rw [← Finset.card_pos]
      have := hwt a ξ
      by_contra h0
      push_neg at h0
      rw [Nat.le_zero.mp h0, mul_zero] at this
      exact absurd this (by positivity)
    obtain ⟨x0, hx0⟩ := hne
    have hx1 := hperp a ξ x0 hx0 d hd
    have := hC x0 hx0 _ hx1
    rw [h2 _ hx0, h2 _ hx1, dotProduct_add] at this
    exact z2_nc _ _ _ this hld
  have hsub : ∀ a (ξ' : Fin (i+1) → Bool), (if isC a (Fin.tail ξ') then Q a (Fin.tail ξ')
      else (Q a (Fin.tail ξ')).filter (fun x => wv I gs a p x = ξ' 0)) ⊆ Q a (Fin.tail ξ') := by
    intro a ξ'
    split_ifs
    · exact subset_rfl
    · exact Finset.filter_subset _ _
  refine ⟨fun a ξ' => if isC a (Fin.tail ξ') then Q a (Fin.tail ξ')
      else (Q a (Fin.tail ξ')).filter (fun x => wv I gs a p x = ξ' 0),
    fun a ξ' => if isC a (Fin.tail ξ') then wt a (Fin.tail ξ') else 2 * wt a (Fin.tail ξ'),
    fun ξ' => D (Fin.tail ξ') ⊔ Submodule.span (ZMod 2) {selD (Fin.tail ξ')},
    fun ξ' w => if w = L + gs.length then
      (if r (Fin.tail ξ') p ∈ D (Fin.tail ξ') then 0
        else if ξ' 0 = decide (g.op = .and) then r (Fin.tail ξ') q else 0)
      else r (Fin.tail ξ') w,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ξ'
    show Module.finrank (ZMod 2)
      ↥(D (Fin.tail ξ') ⊔ Submodule.span (ZMod 2) {selD (Fin.tail ξ')}) ≤ i + 1
    have := hD (Fin.tail ξ')
    have := finrank_sup_span_le (D (Fin.tail ξ')) (selD (Fin.tail ξ'))
    omega
  · intro a ξ' x hx y hy z hz
    by_cases hC : isC a (Fin.tail ξ')
    · simp only [hC, ↓reduceIte] at hx hy hz ⊢
      exact hflat a _ x hx y hy z hz
    · simp only [hC, ↓reduceIte, Finset.mem_filter] at hx hy hz ⊢
      obtain ⟨lam, c, -, h2⟩ := haff a (Fin.tail ξ') p
      have hm := hflat a _ x hx.1 y hy.1 z hz.1
      refine ⟨hm, ?_⟩
      have ex := hx.2; have ey := hy.2; have ez := hz.2
      rw [h2 _ hm, dotProduct_add, dotProduct_add]
      rw [h2 _ hx.1] at ex; rw [h2 _ hy.1] at ey; rw [h2 _ hz.1] at ez
      exact z2_three _ _ _ _ _ ex ey ez
  · intro a ξ' x hx d hd
    have hdD : ∀ δ ∈ D (Fin.tail ξ'), δ ⬝ᵥ d = 0 :=
      fun δ hδ => hd δ (Submodule.mem_sup_left hδ)
    by_cases hC : isC a (Fin.tail ξ')
    · simp only [hC, ↓reduceIte] at hx ⊢
      exact hperp a _ x hx d hdD
    · simp only [hC, ↓reduceIte, Finset.mem_filter] at hx ⊢
      obtain ⟨lam, c, h1, h2⟩ := haff a (Fin.tail ξ') p
      have hm := hperp a _ x hx.1 d hdD
      refine ⟨hm, ?_⟩
      have hl : lam ⬝ᵥ d = 0 := by
        have e1 : lam = (lam - r (Fin.tail ξ') p) + r (Fin.tail ξ') p := by abel
        rw [e1, add_dotProduct, hdD _ h1, hd _ (hrp _), add_zero]
      have ex := hx.2
      rw [h2 _ hx.1] at ex
      rw [h2 _ hm, dotProduct_add, hl, add_zero]
      exact ex
  · intro a ξ'
    by_cases hC : isC a (Fin.tail ξ')
    · simp only [hC, ↓reduceIte]; exact hwt a _
    · simp only [hC, ↓reduceIte]
      have hC' := hC
      simp only [isC, not_forall] at hC'
      obtain ⟨y, hy, z, hz, hyz⟩ := hC'
      obtain ⟨lam, c, -, h2⟩ := haff a (Fin.tail ξ') p
      have hflip : ∀ x ∈ Q a (Fin.tail ξ'),
          wv I gs a p (x + (y + z)) = !(wv I gs a p x) := by
        intro x hx
        have hm : x + (y + z) ∈ Q a (Fin.tail ξ') := by
          rw [← add_assoc]; exact hflat a _ x hx y hy z hz
        rw [h2 _ hm, h2 _ hx, dotProduct_add, dotProduct_add]
        rw [h2 _ hy, h2 _ hz] at hyz
        exact z2_flip _ _ _ _ hyz
      have hh := half_card (Q a (Fin.tail ξ')) (y + z) (fun x => wv I gs a p x = ξ' 0)
        (fun x hx => by rw [← add_assoc]; exact hflat a _ x hx y hy z hz)
        (fun x hx => by
          simp only [hflip x hx]
          generalize wv I gs a p x = u
          generalize ξ' 0 = b
          cases u <;> cases b <;> decide)
      rw [← hwt a (Fin.tail ξ'), ← hh]; ring
  · intro a φ
    rw [sum_cons_bool, pow_succ, mul_comm (2^i) 2, mul_assoc, hsum a φ, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ξ _ => ?_)
    simp only [Fin.tail_cons, Fin.cons_zero]
    by_cases hC : isC a ξ
    · simp only [hC, ↓reduceIte]; ring
    · simp only [hC, ↓reduceIte]
      rw [← Finset.sum_filter_add_sum_filter_not (Q a ξ) (fun x => wv I gs a p x = true) φ]
      have : (Q a ξ).filter (fun x => ¬ wv I gs a p x = true) =
          (Q a ξ).filter (fun x => wv I gs a p x = false) := by
        apply Finset.filter_congr; intro x _; simp
      rw [this]; ring
  · intro a ξ' w
    by_cases hw : w = L + gs.length
    · subst hw
      simp only [↓reduceIte]
      by_cases hA : r (Fin.tail ξ') p ∈ D (Fin.tail ξ')
      · simp only [hA, ↓reduceIte]
        have hrqm : r (Fin.tail ξ') q ∈
            D (Fin.tail ξ') ⊔ Submodule.span (ZMod 2) {selD (Fin.tail ξ')} := by
          apply Submodule.mem_sup_right
          simp only [selD, if_pos hA]
          exact Submodule.mem_span_singleton_self _
        by_cases hC : isC a (Fin.tail ξ')
        · by_cases hne : (Q a (Fin.tail ξ')).Nonempty
          · obtain ⟨x0, hx0⟩ := hne
            refine aff_gate_split (hsub a ξ') le_sup_left (wv I gs a p) (wv I gs a q) _
              (decide (g.op = .and)) (wv I gs a p x0) _ _ (haff a _ q) ?_
              (fun x _ => hval a x) (fun _ => by simpa using hrqm) (fun _ => Submodule.zero_mem _)
            intro x hx
            simp only [hC, ↓reduceIte] at hx
            exact hC x hx x0 hx0
          · refine AffOn.const _ _ _ _ false (fun x hx => ?_) (Submodule.zero_mem _)
            simp only [hC, ↓reduceIte] at hx
            exact absurd ⟨x, hx⟩ hne
        · refine aff_gate_split (hsub a ξ') le_sup_left (wv I gs a p) (wv I gs a q) _
            (decide (g.op = .and)) (ξ' 0) _ _ (haff a _ q) ?_ (fun x _ => hval a x)
            (fun _ => by simpa using hrqm) (fun _ => Submodule.zero_mem _)
          intro x hx
          simp only [hC, ↓reduceIte, Finset.mem_filter] at hx
          exact hx.2
      · simp only [hA, ↓reduceIte]
        have hC := hnc a _ hA
        refine aff_gate_split (hsub a ξ') le_sup_left (wv I gs a p) (wv I gs a q) _
          (decide (g.op = .and)) (ξ' 0) _ _ (haff a _ q) ?_ (fun x _ => hval a x) ?_ ?_
        · intro x hx
          simp only [hC, ↓reduceIte, Finset.mem_filter] at hx
          exact hx.2
        · intro h; rw [if_pos h.symm, sub_self]; exact Submodule.zero_mem _
        · intro h; rw [if_neg (Ne.symm h)]; exact Submodule.zero_mem _
    · simp only [hw, ↓reduceIte]
      refine ((haff a (Fin.tail ξ') w).mono (hsub a ξ') le_sup_left).congr ?_
      intro x _
      rw [wv_snoc I L hI, if_neg hw]

lemma inv_all {k t : ℕ} (I : (Fin k → ZMod 2) → (Fin t → Bool) → List Bool)
    (L : ℕ) (hI : ∀ x a, (I x a).length = L)
    (r : ℕ → Fin k → ZMod 2)
    (hinit : ∀ a w, AffOn Finset.univ (fun x => (I x a).getD w false) (r w) ⊥)
    (gs : List Gate) (hgs : ∀ g ∈ gs, legalG g) :
    Inv I gs (gs.countP counted) := by
  induction gs using List.reverseRecOn with
  | nil => exact inv_nil I r hinit
  | append_singleton gs g ih =>
    have hg : legalG g := hgs g (by simp)
    have ih' := ih (fun g' hg' => hgs g' (by simp [hg']))
    rw [List.countP_append]
    cases hc : counted g
    · have := inv_free I L hI gs g _ hg hc ih'
      simpa [hc] using this
    · have := inv_counted I L hI gs g _ hc ih'
      simpa [hc] using this

def agr {k t : ℕ} (I : (Fin k → ZMod 2) → (Fin t → Bool) → List Bool) (C : Circuit) (a : Fin t → Bool) (vj : Fin k → ZMod 2) (ej : ZMod 2)
    (s : Finset (Fin k → ZMod 2)) : Finset (Fin k → ZMod 2) :=
  s.filter (fun x => C.eval (I x a) =
    decide (dotProduct vj x + ej = 1))

lemma eval_eq_wv {k t : ℕ} (I : (Fin k → ZMod 2) → (Fin t → Bool) → List Bool) (C : Circuit) (x : Fin k → ZMod 2) (a : Fin t → Bool) :
    C.eval (I x a) =
      wv I C.gates a C.output x := rfl

noncomputable def maskSet {k m : ℕ} (v : Fin m → Fin k → ZMod 2)
    (D : Submodule (ZMod 2) (Fin k → ZMod 2)) (r : Fin k → ZMod 2) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun j => v j - r ∈ D)

lemma gain_core {k t : ℕ} (I : (Fin k → ZMod 2) → (Fin t → Bool) → List Bool) (m : ℕ) (v : Fin m → (Fin k → ZMod 2)) (addr : Fin m → (Fin t → Bool))
    (e : Fin m → ZMod 2) (w : Fin m → ℕ)
    (C : Circuit) (i : ℕ) (hinv : Inv I C.gates i) :
    ∃ (D : Submodule (ZMod 2) (Fin k → ZMod 2)) (r : Fin k → ZMod 2),
      Module.finrank (ZMod 2) D ≤ i ∧
      2 * (∑ j : Fin m, w j * (agr I C (addr j) (v j) (e j) Finset.univ).card) -
        2^k * (∑ j : Fin m, w j) ≤ 2^k * (∑ j ∈ maskSet v D r, w j) := by
  classical
  obtain ⟨Q, wt, D, r, hD, hflat, hperp, hwt, hsum, haff⟩ := hinv
  let Sx : (Fin i → Bool) → Finset (Fin m) := fun ξ =>
    Finset.univ.filter (fun j => v j - r ξ C.output ∈ D ξ)
  obtain ⟨ξs, -, hξs⟩ := Finset.exists_max_image Finset.univ (fun ξ => ∑ j ∈ Sx ξ, w j)
    Finset.univ_nonempty
  refine ⟨D ξs, r ξs C.output, hD ξs, ?_⟩
  have hper : ∀ j : Fin m, 2^i * (2 * (agr I C (addr j) (v j) (e j) Finset.univ).card) ≤
      2^k * (2^i + ∑ ξ, if j ∈ Sx ξ then 1 else 0) := by
    intro j
    have h1 := hsum (addr j) (fun x =>
      if C.eval (I x (addr j)) =
        decide (dotProduct (v j) x + e j = 1) then 1 else 0)
    simp only [← Finset.card_filter] at h1
    change 2^i * (agr I C (addr j) (v j) (e j) Finset.univ).card =
      ∑ ξ, wt (addr j) ξ * (agr I C (addr j) (v j) (e j) (Q (addr j) ξ)).card at h1
    have hQ : ∀ ξ, 2 * (agr I C (addr j) (v j) (e j) (Q (addr j) ξ)).card ≤
        (Q (addr j) ξ).card * (1 + if j ∈ Sx ξ then 1 else 0) := by
      intro ξ
      by_cases hj : j ∈ Sx ξ
      · rw [if_pos hj]
        have := Finset.card_filter_le (Q (addr j) ξ) (fun x =>
          C.eval (I x (addr j)) =
            decide (dotProduct (v j) x + e j = 1))
        unfold agr
        omega
      · rw [if_neg hj, add_zero, mul_one]
        obtain ⟨lam, c, hl1, hl2⟩ := haff (addr j) ξ C.output
        have hvl : v j - lam ∉ D ξ := by
          intro hm
          apply hj
          simp only [Sx, Finset.mem_filter, Finset.mem_univ, true_and]
          have : v j - r ξ C.output = (v j - lam) + (lam - r ξ C.output) := by abel
          rw [this]; exact (D ξ).add_mem hm hl1
        obtain ⟨d, hd, hvd⟩ := sep (D ξ) _ hvl
        apply le_of_eq
        apply half_card _ d _ (fun x hx => hperp _ _ x hx d hd)
        intro x hx
        have hx' := hperp _ _ x hx d hd
        rw [eval_eq_wv, eval_eq_wv, hl2 _ hx, hl2 _ hx', dotProduct_add, dotProduct_add]
        rw [sub_dotProduct] at hvd
        exact z2_agree _ _ _ _ _ _ hvd
    calc 2^i * (2 * (agr I C (addr j) (v j) (e j) Finset.univ).card)
        = 2 * (2^i * (agr I C (addr j) (v j) (e j) Finset.univ).card) := by ring
      _ = 2 * ∑ ξ, wt (addr j) ξ * (agr I C (addr j) (v j) (e j) (Q (addr j) ξ)).card := by
          rw [h1]
      _ = ∑ ξ, wt (addr j) ξ * (2 * (agr I C (addr j) (v j) (e j) (Q (addr j) ξ)).card) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun ξ _ => by ring)
      _ ≤ ∑ ξ, wt (addr j) ξ * ((Q (addr j) ξ).card * (1 + if j ∈ Sx ξ then 1 else 0)) :=
          Finset.sum_le_sum (fun ξ _ => Nat.mul_le_mul_left _ (hQ ξ))
      _ = ∑ ξ, 2^k * (1 + if j ∈ Sx ξ then 1 else 0) := by
          refine Finset.sum_congr rfl (fun ξ _ => ?_); rw [← mul_assoc, hwt]
      _ = 2^k * (2^i + ∑ ξ, if j ∈ Sx ξ then 1 else 0) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
          simp [Finset.card_univ, Fintype.card_fun, Fintype.card_bool]
  have hswap : ∑ ξ, ∑ j ∈ Sx ξ, w j = ∑ j, w j * ∑ ξ, (if j ∈ Sx ξ then 1 else 0) := by
    calc ∑ ξ, ∑ j ∈ Sx ξ, w j = ∑ ξ, ∑ j, (if j ∈ Sx ξ then w j else 0) := by
          refine Finset.sum_congr rfl (fun ξ _ => ?_)
          rw [Finset.sum_ite_mem, Finset.univ_inter]
      _ = ∑ j, ∑ ξ, (if j ∈ Sx ξ then w j else 0) := Finset.sum_comm
      _ = ∑ j, w j * ∑ ξ, (if j ∈ Sx ξ then 1 else 0) := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun ξ _ => by rw [mul_boole])
  have hmax : ∑ ξ, ∑ j ∈ Sx ξ, w j ≤ 2^i * ∑ j ∈ Sx ξs, w j := by
    calc ∑ ξ, ∑ j ∈ Sx ξ, w j ≤ ∑ _ξ : Fin i → Bool, ∑ j ∈ Sx ξs, w j :=
          Finset.sum_le_sum (fun ξ _ => hξs ξ (Finset.mem_univ _))
      _ = 2^i * ∑ j ∈ Sx ξs, w j := by
          simp [Finset.card_univ, Fintype.card_fun, Fintype.card_bool]
  have hB : ∑ j, w j * (2^k * (2^i + ∑ ξ, if j ∈ Sx ξ then 1 else 0)) =
      2^k * 2^i * ∑ j, w j + 2^k * ∑ j, w j * ∑ ξ, (if j ∈ Sx ξ then 1 else 0) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have htot : 2^i * (2 * ∑ j, w j * (agr I C (addr j) (v j) (e j) Finset.univ).card) ≤
      2^i * (2^k * (∑ j, w j) + 2^k * ∑ j ∈ Sx ξs, w j) := by
    calc 2^i * (2 * ∑ j, w j * (agr I C (addr j) (v j) (e j) Finset.univ).card)
        = ∑ j, w j * (2^i * (2 * (agr I C (addr j) (v j) (e j) Finset.univ).card)) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun j _ => by ring)
      _ ≤ ∑ j, w j * (2^k * (2^i + ∑ ξ, if j ∈ Sx ξ then 1 else 0)) :=
          Finset.sum_le_sum (fun j _ => Nat.mul_le_mul_left _ (hper j))
      _ = 2^k * 2^i * ∑ j, w j + 2^k * ∑ ξ, ∑ j ∈ Sx ξ, w j := by rw [hB, hswap]
      _ ≤ 2^k * 2^i * ∑ j, w j + 2^k * (2^i * ∑ j ∈ Sx ξs, w j) := by
          exact Nat.add_le_add_left (Nat.mul_le_mul_left (2^k) hmax) _
      _ = 2^i * (2^k * (∑ j, w j) + 2^k * ∑ j ∈ Sx ξs, w j) := by ring
  have h2 := Nat.le_of_mul_le_mul_left htot (by positivity)
  rw [Nat.sub_le_iff_le_add, add_comm]
  exact h2


lemma gain_subset {k t : ℕ} (I : (Fin k → ZMod 2) → (Fin t → Bool) → List Bool)
    (m : ℕ) (v : Fin m → (Fin k → ZMod 2)) (addr : Fin m → (Fin t → Bool))
    (e : Fin m → ZMod 2) (K : Finset (Fin m))
    (C : Circuit) (i : ℕ) (hinv : Inv I C.gates i) :
    ∃ (D : Submodule (ZMod 2) (Fin k → ZMod 2)) (r : Fin k → ZMod 2),
      Module.finrank (ZMod 2) D ≤ i ∧
      2 * (∑ j ∈ K, (agr I C (addr j) (v j) (e j) Finset.univ).card) -
        2^k * K.card ≤ 2^k * (maskSet v D r).card := by
  classical
  obtain ⟨D, r, hD, hg⟩ := gain_core I m v addr e (fun j => if j ∈ K then 1 else 0) C i hinv
  refine ⟨D, r, hD, ?_⟩
  have hleft : ∑ j : Fin m, (if j ∈ K then 1 else 0) *
      (agr I C (addr j) (v j) (e j) Finset.univ).card =
      ∑ j ∈ K, (agr I C (addr j) (v j) (e j) Finset.univ).card := by
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]
  have hcard : ∑ j : Fin m, (if j ∈ K then 1 else 0) = K.card := by simp
  rw [hleft, hcard] at hg
  refine hg.trans (Nat.mul_le_mul_left _ ?_)
  calc ∑ j ∈ maskSet v D r, (if j ∈ K then 1 else 0)
      ≤ ∑ _j ∈ maskSet v D r, 1 :=
        Finset.sum_le_sum (fun j _ => by split_ifs <;> omega)
    _ = _ := by simp

lemma basis_single {n : ℕ} (i : Fin n) :
    (fun j => if i = j then (1 : ZMod 2) else 0) = Pi.single i 1 := by
  funext j
  simp [Pi.single_apply, eq_comm]

def pull {n k : ℕ} (B : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2))
    (v : Fin k → ZMod 2) : Fin n → ZMod 2 :=
  fun i => v ⬝ᵥ B (Pi.single i 1)

lemma pull_dot {n k : ℕ} (B : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2))
    (v : Fin k → ZMod 2) (y : Fin n → ZMod 2) :
    pull B v ⬝ᵥ y = v ⬝ᵥ B y := by
  conv_rhs => rw [LinearMap.pi_apply_eq_sum_univ B y, dotProduct_sum]
  simp only [basis_single, dotProduct_smul, smul_eq_mul]
  unfold pull dotProduct
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

lemma coord_dot {n k : ℕ} (B : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2))
    (l : Fin k) (y : Fin n → ZMod 2) :
    (fun i => B (Pi.single i 1) l) ⬝ᵥ y = B y l := by
  conv_rhs => rw [LinearMap.pi_apply_eq_sum_univ B y]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, basis_single]
  unfold dotProduct
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

lemma affine_init {n k t : ℕ}
    (B : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2)) (p : Fin k → ZMod 2) :
    ∃ r : ℕ → Fin n → ZMod 2, ∀ a w,
      AffOn Finset.univ (fun y => (inp k t (p + B y) a).getD w false) (r w) ⊥ := by
  refine ⟨fun w => if h : w < k then (fun i => B (Pi.single i 1) ⟨w, h⟩) else 0, ?_⟩
  intro a w
  dsimp only
  by_cases hw : w < k
  · rw [dif_pos hw]
    refine ⟨(fun i => B (Pi.single i 1) ⟨w, hw⟩), p ⟨w, hw⟩, by simp, fun y _ => ?_⟩
    show (inp k t (p+B y) a).getD w false = _
    rw [inp, List.getD_append _ _ _ _ (by simpa using hw)]
    simp [List.getD_eq_getElem?_getD, hw, coord_dot, add_comm]
  · rw [dif_neg hw]
    by_cases hw2 : w < k + t
    · refine AffOn.const _ _ _ _ (a ⟨w - k, by omega⟩) (fun y _ => ?_) (Submodule.zero_mem _)
      rw [inp, List.getD_append_right _ _ _ _ (by simp; omega)]
      simp [List.getD_eq_getElem?_getD, show w - k < t by omega]
    · refine AffOn.const _ _ _ _ false (fun y _ => ?_) (Submodule.zero_mem _)
      rw [List.getD_eq_default _ _ (by rw [inp_length]; omega)]

lemma affine_inv {n k t : ℕ}
    (B : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2)) (p : Fin k → ZMod 2)
    (C : Circuit) (hg : ∀ g ∈ C.gates, legalG g) :
    Inv (fun y a => inp k t (p + B y) a) C.gates (C.gates.countP counted) := by
  obtain ⟨r, hr⟩ := affine_init (t := t) B p
  exact inv_all _ (k+t) (fun y a => inp_length k t (p+B y) a) r hr C.gates hg

lemma affine_gain {n k t m : ℕ}
    (B : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2)) (p : Fin k → ZMod 2)
    (v : Fin m → Fin k → ZMod 2) (addr : Fin m → Fin t → Bool) (K : Finset (Fin m))
    (C : Circuit) (hg : ∀ g ∈ C.gates, legalG g) :
    ∃ (D : Submodule (ZMod 2) (Fin n → ZMod 2)) (r : Fin n → ZMod 2),
      Module.finrank (ZMod 2) D ≤ C.gates.countP counted ∧
      2 * (∑ j ∈ K, (Finset.univ.filter (fun y =>
        C.eval (inp k t (p + B y) (addr j)) = decide (v j ⬝ᵥ (p + B y) = 1))).card) -
        2^n * K.card ≤ 2^n * (maskSet (fun j => pull B (v j)) D r).card := by
  classical
  have h := gain_subset (fun y a => inp k t (p + B y) a) m (fun j => pull B (v j)) addr
    (fun j => v j ⬝ᵥ p) K C _ (affine_inv B p C hg)
  simpa only [agr, pull_dot, dotProduct_add, add_comm] using h

end Partition

namespace Spectral

open scoped Classical

abbrev F2 := ZMod 2

def chi (a : F2) : ℤ := if a = 1 then -1 else 1

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

lemma chi_sub (a b : F2) : chi (a - b) = chi a * chi b := by
  rw [zmod2_sub_eq_add, chi_add]

noncomputable def weight {k : ℕ} (D : Submodule F2 (Fin k → F2))
    (x : Fin k → F2) : ℤ := by
  classical
  exact ∑ d : D, chi (dotProduct x (d : Fin k → F2))

lemma weight_zero {k : ℕ} (D : Submodule F2 (Fin k → F2)) :
    weight D 0 = (2 : ℤ) ^ Module.finrank F2 D := by
  classical
  simp only [weight, dotProduct_zero_left, chi_zero, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [Module.card_eq_pow_finrank (K := F2), ZMod.card, Nat.cast_pow, Nat.cast_ofNat]

lemma weight_nonneg {k : ℕ} (D : Submodule F2 (Fin k → F2)) (x : Fin k → F2) :
    0 ≤ weight D x := by
  classical
  by_cases hall : ∀ d : D, dotProduct x (d : Fin k → F2) = 0
  · simp only [weight, hall, chi_zero, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one]
    positivity
  · push Not at hall
    obtain ⟨d, hd⟩ := hall
    have hd1 : dotProduct x (d : Fin k → F2) = 1 :=
      (zmod2_eq_zero_or_one _).resolve_left hd
    have hshift : (∑ e : D, chi (dotProduct x ((e + d : D) : Fin k → F2))) =
        ∑ e : D, chi (dotProduct x (e : Fin k → F2)) :=
      Fintype.sum_equiv (Equiv.addRight d) _ _ (fun _ => rfl)
    have hneg : (∑ e : D, chi (dotProduct x ((e + d : D) : Fin k → F2))) =
        -(∑ e : D, chi (dotProduct x (e : Fin k → F2))) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro e _
      change chi (dotProduct x ((e : Fin k → F2) + (d : Fin k → F2))) = _
      rw [dotProduct_add_right, hd1, chi_add, chi_one]
      ring
    unfold weight
    linarith

lemma weight_total {k : ℕ} (D : Submodule F2 (Fin k → F2)) :
    (∑ x : Fin k → F2, weight D x) = (2 : ℤ) ^ k := by
  classical
  simp only [weight]
  rw [Finset.sum_comm]
  simp_rw [sum_chi_dotProduct]
  have heq : ∀ d : D, ((d : Fin k → F2) = 0) ↔ d = 0 := by
    intro d
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  simp_rw [heq]
  simp

lemma filter_identity {k : ℕ} (D : Submodule F2 (Fin k → F2)) (u : Fin k → F2) :
    (∑ x : Fin k → F2, weight D x * chi (dotProduct x u)) =
      if u ∈ D then (2 : ℤ) ^ k else 0 := by
  classical
  simp only [weight, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hexpand : ∀ d : D, (∑ x : Fin k → F2,
      chi (dotProduct x (d : Fin k → F2)) * chi (dotProduct x u)) =
      if (d : Fin k → F2) = u then (2 : ℤ) ^ k else 0 := by
    intro d
    simp_rw [← chi_sub, ← dotProduct_sub]
    rw [sum_chi_dotProduct]
    simp only [sub_eq_zero]
  simp_rw [hexpand]
  by_cases hu : u ∈ D
  · let d : D := ⟨u, hu⟩
    have heq : ∀ e : D, (e : Fin k → F2) = u ↔ e = d := by
      intro e
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    simp_rw [heq]
    simp [hu]
  · have heq : ∀ e : D, (e : Fin k → F2) ≠ u := by
      intro e h
      exact hu (h ▸ e.property)
    simp [hu, heq]

lemma coset_fourier {k m : ℕ} (v : Fin m → Fin k → F2)
    (D : Submodule F2 (Fin k → F2)) (r : Fin k → F2) :
    (2 : ℤ) ^ k * (Finset.univ.filter (fun j => v j - r ∈ D)).card =
      ∑ x : Fin k → F2, weight D x * chi (dotProduct x r) *
        ∑ j : Fin m, chi (dotProduct x (v j)) := by
  classical
  calc
    (2 : ℤ) ^ k * (Finset.univ.filter (fun j => v j - r ∈ D)).card =
        ∑ j : Fin m, if v j - r ∈ D then (2 : ℤ) ^ k else 0 := by
      simp [Finset.sum_ite, Finset.sum_const, mul_comm]
    _ = ∑ j : Fin m, ∑ x : Fin k → F2, weight D x * chi (dotProduct x (v j - r)) := by
      simp_rw [filter_identity]
    _ = ∑ x : Fin k → F2, ∑ j : Fin m, weight D x * chi (dotProduct x (v j - r)) :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [dotProduct_sub, chi_sub]
      ring

lemma coset_bound_full {k m : ℕ} (v : Fin m → Fin k → F2)
    (hbias : ∀ x : Fin k → F2, x ≠ 0 →
      14 * |∑ j : Fin m, chi (dotProduct x (v j))| ≤ (m : ℤ))
    (D : Submodule F2 (Fin k → F2)) (r : Fin k → F2) :
    14 * (2 : ℤ) ^ k * (Finset.univ.filter (fun j => v j - r ∈ D)).card ≤
      ((2 : ℤ) ^ k + 13 * (2 : ℤ) ^ Module.finrank F2 D) * m := by
  classical
  let f : (Fin k → F2) → ℤ := fun x => weight D x * chi (dotProduct x r) *
    ∑ j : Fin m, chi (dotProduct x (v j))
  have hterm : ∀ x : Fin k → F2, 14 * f x ≤
      weight D x * m + if x = 0 then 13 * weight D 0 * m else 0 := by
    intro x
    by_cases hx : x = 0
    · subst x
      simp [f, chi_zero]
      ring_nf
      rfl
    · rw [ite_eq_right hx, add_zero]
      have habs : chi (dotProduct x r) * (∑ j : Fin m, chi (dotProduct x (v j))) ≤
          |∑ j : Fin m, chi (dotProduct x (v j))| := by
        calc
          _ ≤ |chi (dotProduct x r) * (∑ j : Fin m, chi (dotProduct x (v j)))| := le_abs_self _
          _ = _ := by rw [abs_mul, abs_chi, one_mul]
      have hb := hbias x hx
      have hbound : 14 * (chi (dotProduct x r) * ∑ j : Fin m,
          chi (dotProduct x (v j))) ≤ (m : ℤ) := by linarith
      have hw := mul_le_mul_of_nonneg_left hbound (weight_nonneg D x)
      dsimp [f]
      nlinarith only [hw]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun x _ => hterm x)
  rw [← Finset.mul_sum] at hsum
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] at hsum
  rw [weight_total, weight_zero] at hsum
  have hid := coset_fourier v D r
  change (2 : ℤ) ^ k * _ = ∑ x, f x at hid
  rw [← hid] at hsum
  nlinarith only [hsum]

lemma coset_bound {k m : ℕ} (v : Fin m → Fin k → F2)
    (hbias : ∀ x : Fin k → F2, x ≠ 0 →
      14 * |∑ j : Fin m, chi (dotProduct x (v j))| ≤ (m : ℤ))
    (D : Submodule F2 (Fin k → F2)) (r : Fin k → F2) (h : ℕ)
    (hdim : Module.finrank F2 D + h ≤ k) :
    14 * 2 ^ h * (Finset.univ.filter (fun j => v j - r ∈ D)).card ≤
      (2 ^ h + 13) * m := by
  classical
  have hfull := coset_bound_full v hbias D r
  have hp : (2 : ℤ) ^ h * (2 : ℤ) ^ Module.finrank F2 D ≤ (2 : ℤ) ^ k := by
    rw [← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hm : (0 : ℤ) ≤ m := Int.natCast_nonneg m
  have hpow : (0 : ℤ) < 2 ^ k := by positivity
  have hq : (0 : ℤ) ≤ 2 ^ h := by positivity
  have hfull' := mul_le_mul_of_nonneg_left hfull hq
  have hp' := mul_le_mul_of_nonneg_right hp hm
  have ht : (2 : ℤ) ^ k * (14 * 2 ^ h *
      (Finset.univ.filter (fun j => v j - r ∈ D)).card) ≤
        (2 : ℤ) ^ k * ((2 ^ h + 13) * m) := by
    nlinarith only [hfull', hp']
  have ht' := (mul_le_mul_iff_right₀ hpow).mp ht
  exact_mod_cast ht'


def maskB {k n : ℕ} (B : (Fin n → F2) →ₗ[F2] (Fin k → F2))
    (v : Fin k → F2) : Fin n → F2 :=
  fun i => dotProduct v (B (Pi.single i 1))

lemma maskB_dotProduct {k n : ℕ} (B : (Fin n → F2) →ₗ[F2] (Fin k → F2))
    (v : Fin k → F2) (y : Fin n → F2) :
    dotProduct (maskB B v) y = dotProduct v (B y) := by
  rw [LinearMap.pi_apply_eq_sum_univ B y]
  simp only [dotProduct, maskB, Finset.sum_apply, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  have hs : (fun j : Fin n => if i = j then (1 : F2) else 0) = Pi.single i 1 := by
    ext j
    simp [Pi.single_apply, eq_comm]
  rw [hs]
  ring

lemma small_bias_maskB {k m n : ℕ} (v : Fin m → Fin k → F2)
    (hbias : ∀ x : Fin k → F2, x ≠ 0 →
      14 * |∑ j : Fin m, chi (dotProduct x (v j))| ≤ (m : ℤ))
    (B : (Fin n → F2) →ₗ[F2] (Fin k → F2)) (hB : Function.Injective B) :
    ∀ x : Fin n → F2, x ≠ 0 →
      14 * |∑ j : Fin m, chi (dotProduct x (maskB B (v j)))| ≤ (m : ℤ) := by
  intro x hx
  have hBx : B x ≠ 0 := by
    intro h
    exact hx (hB (h.trans B.map_zero.symm))
  have hh := hbias (B x) hBx
  have heq : ∀ j, dotProduct x (maskB B (v j)) = dotProduct (B x) (v j) := by
    intro j
    rw [dotProduct_comm x, maskB_dotProduct, dotProduct_comm (v j)]
  simpa only [heq] using hh

end Spectral

namespace Upper

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


lemma exists_full_lookup (k t m : ℕ) (hm : 0 < m)
    (v : Fin m → (Fin k → ZMod 2)) (addr : Fin m → (Fin t → Bool))
    (hinj : Function.Injective addr) :
    ∃ C : Circuit, (PEqualNP.MetaComplexity.NestedCover.ReadsBack (k+t) C ∧
        ∀ g ∈ C.gates, legalG g) ∧
      C.output < k + t + C.size ∧ C.gates.countP counted ≤ m - 1 ∧
      ∀ (x : Fin k → ZMod 2) (j : Fin m),
        C.eval (List.ofFn (fun l : Fin k => decide (x l = 1)) ++ List.ofFn (addr j)) =
          decide (dotProduct (v j) x = 1) := by
  classical
  have hS : (Finset.univ : Finset (Fin m)).Nonempty := by
    exact ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  obtain ⟨gs, out, hl, hr, hout, hc, leaf, hleafS, hleaf, hsem⟩ :=
    build k t m v (fun _ => 0) addr hinj Finset.univ hS (k+t) le_rfl
  have hcard : (Finset.univ : Finset (Fin m)).card = m := by simp
  rw [hcard] at hc
  refine ⟨⟨gs, out⟩, ⟨?_, hl⟩, hout, by dsimp; omega, ?_⟩
  · intro j hj i hi
    simp only [PEqualNP.MetaComplexity.NestedCover.gateAt] at hi
    rw [List.getD_eq_getElem _ _ hj] at hi
    exact hr j hj i hi
  · intro x j
    have hW := hsem (run gs (inp k t x (addr j))) (fun a ha => by
      have h := run_getD_gate gs (inp k t x (addr j)) a ha
        (by rw [inp_length]; exact hr a ha)
      rw [inp_length] at h
      exact h)
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
    rw [ha, hx, hleaf j (Finset.mem_univ _)] at hW
    change (run gs (inp k t x (addr j))).getD out false = _
    simpa only [add_zero] using hW


def address (t : ℕ) (j : Fin (2^t)) : Fin t → Bool := fun i => j.val.testBit i.val

lemma address_injective (t : ℕ) : Function.Injective (address t) := by
  intro a b h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < t
  · exact congrFun h ⟨i, hi⟩
  · have hpow : 2^t ≤ 2^i := by gcongr; omega
    have ha : a.val < 2^i := a.isLt.trans_le hpow
    have hb : b.val < 2^i := b.isLt.trans_le hpow
    rw [Nat.testBit_lt_two_pow ha, Nat.testBit_lt_two_pow hb]

lemma exists_full_address_lookup (k t : ℕ) (v : Fin (2^t) → (Fin k → ZMod 2)) :
    ∃ C : Circuit, (PEqualNP.MetaComplexity.NestedCover.ReadsBack (k+t) C ∧
        ∀ g ∈ C.gates, legalG g) ∧
      C.output < k + t + C.size ∧ C.gates.countP counted ≤ 2^t - 1 ∧
      ∀ (x : Fin k → ZMod 2) (j : Fin (2^t)),
        C.eval (List.ofFn (fun l : Fin k => decide (x l = 1)) ++ List.ofFn (address t j)) =
          decide (dotProduct (v j) x = 1) :=
  exists_full_lookup k t (2^t) (by positivity) v (address t) (address_injective t)

end Upper

namespace Arithmetic

lemma two_thirds (n c N m R hits : ℕ) (hN : 0 < N) (hm : 0 < m)
    (hbound : ∀ h : ℕ, c+h ≤ n →
      14*2^h*(2*hits-N*R) ≤ (2^h+13)*N*m)
    (hhalf : m ≤ 2*R) (happrox : 2*N*R ≤ 3*hits) : n ≤ c+3 := by
  by_contra hn
  have hb := hbound 4 (by omega)
  norm_num at hb
  have hbase : N*R ≤ 2*hits := by nlinarith
  have heq : (2*hits-N*R)+N*R = 2*hits := Nat.sub_add_cancel hbase
  have hK : N*m ≤ 2*(N*R) := by nlinarith [Nat.mul_le_mul_left N hhalf]
  have hgain : N*m ≤ 6*(2*hits-N*R) := by nlinarith
  have hp := Nat.mul_pos hN hm
  nlinarith

lemma exact_case (n c N m hits : ℕ) (hN : 0 < N) (hm : 0 < m)
    (hbound : ∀ h : ℕ, c+h ≤ n →
      14*2^h*(2*hits-N*m) ≤ (2^h+13)*N*m)
    (hhits : hits = N*m) : n ≤ c := by
  by_contra hn
  have hb := hbound 1 (by omega)
  rw [hhits] at hb
  have hdiff : 2*(N*m)-N*m = N*m := by omega
  rw [hdiff] at hb
  norm_num at hb
  have hp := Nat.mul_pos hN hm
  nlinarith

end Arithmetic

end PEqualNP.Outside.L_meta_29742_aux

open PEqualNP.Outside.L_meta_29742_aux


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
  obtain ⟨t, hmlo, hmhi⟩ := Tape.exists_pow2_window k hk
  refine ⟨t, hmlo, hmhi, ?_⟩
  obtain ⟨s, hbias⟩ := Tape.exists_good_tape k (2^t) hk hmlo
  refine ⟨s, ?_⟩
  intro v inp legal cost
  constructor
  · obtain ⟨H, hleg, hout, hc, he⟩ := Upper.exists_full_address_lookup k t v
    refine ⟨H, ?_, hout, ?_, ?_⟩
    · simpa only [legal, Upper.legalG] using hleg
    · change H.gates.countP Upper.counted ≤ 2^t-1
      exact hc
    · intro x j
      change H.eval (List.ofFn (fun i : Fin k => decide (x i = 1)) ++
        List.ofFn (Upper.address t j)) = decide (dotProduct (v j) x = 1)
      exact he x j
  · intro n B hB p K C hC hits N
    have hbiasv : ∀ x : Fin k → ZMod 2, x ≠ 0 →
        14 * |∑ j : Fin (2^t), Spectral.chi (dotProduct x (v j))| ≤ (2^t : ℤ) := by
      simpa only [v, Tape.chi, Spectral.chi, Nat.cast_pow, Nat.cast_ofNat] using hbias
    have hbiasB := Spectral.small_bias_maskB v hbiasv B hB
    obtain ⟨D, r, hD, hgain⟩ := Partition.affine_gain B p v (Upper.address t) K C
      (by simpa only [legal, Partition.legalG] using hC.2)
    have hdim : Module.finrank (ZMod 2) D ≤ cost C := by
      change Module.finrank (ZMod 2) D ≤ C.gates.countP Partition.counted
      exact hD
    have hgain' : 2*hits-N*K.card ≤
        N*(Finset.univ.filter (fun j => Spectral.maskB B (v j)-r ∈ D)).card := by
      change 2 * (∑ j ∈ K, (Finset.univ.filter (fun y =>
        C.eval (Partition.inp k t (p+B y) (Upper.address t j)) =
          decide (dotProduct (v j) (p+B y) = 1))).card) - 2^n*K.card ≤
        2^n*(Partition.maskSet (fun j => Partition.pull B (v j)) D r).card
      exact hgain
    have hmain : ∀ h : ℕ, cost C+h ≤ n →
        14*2^h*(2*hits-N*K.card) ≤ (2^h+13)*N*(2^t) := by
      intro h hh
      have hmask := Spectral.coset_bound (fun j => Spectral.maskB B (v j)) hbiasB D r h
        ((Nat.add_le_add_right hdim h).trans hh)
      calc
        14*2^h*(2*hits-N*K.card) ≤
            14*2^h*(N*(Finset.univ.filter (fun j => Spectral.maskB B (v j)-r ∈ D)).card) :=
          Nat.mul_le_mul_left _ hgain'
        _ = N*(14*2^h*(Finset.univ.filter (fun j => Spectral.maskB B (v j)-r ∈ D)).card) := by ring
        _ ≤ N*((2^h+13)*(2^t)) := Nat.mul_le_mul_left N hmask
        _ = (2^h+13)*N*(2^t) := by ring
    refine ⟨hmain, ?_, ?_⟩
    · intro hK hhits
      exact Arithmetic.two_thirds n (cost C) N (2^t) K.card hits
        (by dsimp [N]; positivity) (by positivity) hmain hK hhits
    · intro hK hhits
      have hcard : K.card = 2^t := by rw [hK]; simp
      apply Arithmetic.exact_case n (cost C) N (2^t) hits
        (by dsimp [N]; positivity) (by positivity)
      · intro h hh
        simpa only [hcard] using hmain h hh
      · simpa only [hcard] using hhits
