import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5104

def x2List : List ℕ :=
  [917681504273, 14878052356, 31886295704066, 257731462272, 42884715528480,
   82789891049544, 248671168364547, 198670308868108, 158476001083504, 238332533539200,
   176488259259904, 212188564320256, 280375465312256, 271282175737871, 280357743624591]

def x3List : List ℕ :=
  [63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864,
   55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436,
   229736628138025984, 270286071508633728, 288160007407550752, 191866593364673099, 193001360500003407]

def eqPairs : List (ℕ × ℕ) :=
  [(3, 0), (4, 4), (5, 15), (6, 2), (7, 12), (8, 16), (9, 1), (10, 9), (11, 13),
   (12, 7), (13, 10), (14, 17), (15, 5), (16, 8), (17, 14), (18, 3), (19, 6), (20, 11)]

def domPairs : List (ℕ × ℕ) :=
  [(21, 18), (22, 19), (23, 20), (24, 21), (25, 22), (26, 23), (27, 24), (28, 25),
   (29, 26), (30, 27), (31, 28), (32, 29), (33, 30), (34, 31), (35, 33), (36, 32),
   (37, 33), (38, 34), (39, 35), (40, 36), (41, 37), (42, 37), (43, 38), (44, 39),
   (45, 39), (46, 40), (47, 41), (48, 42), (49, 44), (50, 43), (51, 44), (52, 45),
   (53, 45), (54, 46), (55, 46), (56, 47), (57, 47)]

def evalStep (d : ℕ) (xs : List ℕ) (g : Bool × ℕ × ℕ) : List ℕ :=
  xs ++ [if g.1 = Bool.true then xs.getD g.2.1 d ||| xs.getD g.2.2 d else xs.getD g.2.1 d &&& xs.getD g.2.2 d]

lemma getD_append_self (xs : List ℕ) (v d : ℕ) :
    (xs ++ [v]).getD xs.length d = v := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_append_gt (xs : List ℕ) (v d i : ℕ) (hi : xs.length < i) :
    (xs ++ [v]).getD i d = d := by
  have hle : (xs ++ [v]).length ≤ i := by
    simp
    omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hle]
  rfl

lemma foldl_rel (P : ℕ → ℕ → Prop) (d3 d2 : ℕ)
    (hd : P d3 d2)
    (hor : ∀ a3 a2 b3 b2, P a3 a2 → P b3 b2 → P (a3 ||| b3) (a2 ||| b2))
    (hand : ∀ a3 a2 b3 b2, P a3 a2 → P b3 b2 → P (a3 &&& b3) (a2 &&& b2))
    (gates : List (Bool × ℕ × ℕ)) (xs3 xs2 : List ℕ)
    (hlen : xs3.length = xs2.length)
    (hinit : ∀ i, P (xs3.getD i d3) (xs2.getD i d2)) :
    (List.foldl (evalStep d3) xs3 gates).length = (List.foldl (evalStep d2) xs2 gates).length ∧
    ∀ i, P ((List.foldl (evalStep d3) xs3 gates).getD i d3)
           ((List.foldl (evalStep d2) xs2 gates).getD i d2) := by
  induction gates generalizing xs3 xs2 with
  | nil => exact ⟨hlen, hinit⟩
  | cons g gs ih =>
    apply ih
    · simp [evalStep, hlen]
    · intro i
      dsimp only [evalStep]
      have hv : P (if g.1 = Bool.true then xs3.getD g.2.1 d3 ||| xs3.getD g.2.2 d3 else xs3.getD g.2.1 d3 &&& xs3.getD g.2.2 d3)
                  (if g.1 = Bool.true then xs2.getD g.2.1 d2 ||| xs2.getD g.2.2 d2 else xs2.getD g.2.1 d2 &&& xs2.getD g.2.2 d2) := by
        cases g.1
        · exact hand _ _ _ _ (hinit g.2.1) (hinit g.2.2)
        · exact hor _ _ _ _ (hinit g.2.1) (hinit g.2.2)
      rcases lt_trichotomy i xs3.length with hi | rfl | hi
      · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (hlen ▸ hi)]
        exact hinit i
      · rw [getD_append_self, hlen, getD_append_self]
        exact hv
      · rw [getD_append_gt _ _ _ _ hi, getD_append_gt _ _ _ _ (hlen ▸ hi)]
        exact hd

lemma getD_of_zipWith_all (f : ℕ → ℕ → Bool) (l1 l2 : List ℕ)
    (hlen : l1.length = l2.length) (hne : 0 < l1.length)
    (hz : (List.zipWith f l1 l2).all id = true) :
    ∀ i, f (l1.getD i (l1.headD 0)) (l2.getD i (l2.headD 0)) = true := by
  have hall : ∀ k (hk : k < l1.length), f l1[k] l2[k] = true := by
    intro k hk
    have hk2 : k < l2.length := hlen ▸ hk
    have hzk : k < (List.zipWith f l1 l2).length := by
      simpa [List.length_zipWith, ← hlen] using hk
    have hmem : f l1[k] l2[k] ∈ List.zipWith f l1 l2 := by
      have hget : (List.zipWith f l1 l2)[k] = f l1[k] l2[k] := by
        simp [List.getElem_zipWith]
      rw [← hget]
      exact List.getElem_mem hzk
    simpa using (List.all_eq_true.mp hz) _ hmem
  have hhead1 : l1.headD 0 = l1[0] := by
    cases l1 with
    | nil => simp at hne
    | cons a as => rfl
  have hne2 : 0 < l2.length := hlen ▸ hne
  have hhead2 : l2.headD 0 = l2[0] := by
    cases l2 with
    | nil => simp at hne2
    | cons a as => rfl
  intro i
  by_cases hi : i < l1.length
  · have hi2 : i < l2.length := hlen ▸ hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi2]
    exact hall i hi
  · have hle1 : l1.length ≤ i := Nat.le_of_not_lt hi
    have hle2 : l2.length ≤ i := hlen ▸ hle1
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hle1,
        List.getD_eq_getElem?_getD, List.getElem?_eq_none hle2]
    change f (l1.headD 0) (l2.headD 0) = true
    rw [hhead1, hhead2]
    exact hall 0 hne

lemma getD_lt_of_all (l : List ℕ) (M : ℕ) (hne : 0 < l.length) (hall : l.all (· < M) = true) :
    ∀ i, l.getD i (l.headD 0) < M := by
  have hm : ∀ k (hk : k < l.length), l[k] < M := by
    intro k hk
    have := (List.all_eq_true.mp hall) l[k] (List.getElem_mem hk)
    simpa using this
  have hhead : l.headD 0 = l[0] := by
    cases l with
    | nil => simp at hne
    | cons a as => rfl
  intro i
  by_cases hi : i < l.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    exact hm i hi
  · have hle : l.length ≤ i := Nat.le_of_not_lt hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hle]
    change l.headD 0 < M
    rw [hhead]
    exact hm 0 hne

lemma eq_check :
    (eqPairs.all fun p => (List.zipWith (fun a b => a.testBit p.1 == b.testBit p.2) x3List x2List).all id) = true := by
  decide

lemma dom_check :
    (domPairs.all fun p => (List.zipWith (fun a b => !(a.testBit p.1) || b.testBit p.2) x3List x2List).all id) = true := by
  decide

lemma lt58_check :
    x3List.all (· < 2 ^ 58) = true := by
  decide

lemma eq_range_check :
    (List.range' 3 18).all (fun k => eqPairs.any fun p => p.1 == k && decide (p.2 < 18)) = true := by
  decide

lemma dom_range_check :
    (List.range' 21 37).all (fun k => domPairs.any fun p => p.1 == k && decide (18 ≤ p.2)) = true := by
  decide

lemma low_bits_check :
    (List.range 3).all (fun k => (7 : ℕ).testBit k && (2097151 : ℕ).testBit k) = true := by
  decide

lemma mid_262143_check :
    (List.range 18).all (fun b => (262143 : ℕ).testBit b) = true := by
  decide

lemma mid_2097151_check :
    (List.range' 3 18).all (fun k => (2097151 : ℕ).testBit k) = true := by
  decide

lemma bit_eq_of_mem (gates : List (Bool × ℕ × ℕ)) (idx : ℕ) (p : ℕ × ℕ) (hp : p ∈ eqPairs) :
    ((List.foldl (evalStep (x3List.headD 0)) x3List gates).getD idx (x3List.headD 0)).testBit p.1 =
    ((List.foldl (evalStep (x2List.headD 0)) x2List gates).getD idx (x2List.headD 0)).testBit p.2 := by
  have hz : (List.zipWith (fun a b => a.testBit p.1 == b.testBit p.2) x3List x2List).all id = true :=
    List.all_eq_true.mp eq_check p hp
  have hinit := getD_of_zipWith_all (fun a b => a.testBit p.1 == b.testBit p.2) x3List x2List rfl (by decide) hz
  have hinit' : ∀ i, (x3List.getD i (x3List.headD 0)).testBit p.1 = (x2List.getD i (x2List.headD 0)).testBit p.2 := by
    intro i
    simpa using hinit i
  have hres := foldl_rel (fun a b => a.testBit p.1 = b.testBit p.2)
    (x3List.headD 0) (x2List.headD 0)
    (hinit' 0)
    (fun a3 a2 b3 b2 ha hb => by simp [ha, hb])
    (fun a3 a2 b3 b2 ha hb => by simp [ha, hb])
    gates x3List x2List rfl hinit'
  exact hres.2 idx

lemma bit_dom_of_mem (gates : List (Bool × ℕ × ℕ)) (idx : ℕ) (p : ℕ × ℕ) (hp : p ∈ domPairs) :
    ((List.foldl (evalStep (x3List.headD 0)) x3List gates).getD idx (x3List.headD 0)).testBit p.1 = true →
    ((List.foldl (evalStep (x2List.headD 0)) x2List gates).getD idx (x2List.headD 0)).testBit p.2 = true := by
  have hz : (List.zipWith (fun a b => !(a.testBit p.1) || b.testBit p.2) x3List x2List).all id = true :=
    List.all_eq_true.mp dom_check p hp
  have hinit := getD_of_zipWith_all (fun a b => !(a.testBit p.1) || b.testBit p.2) x3List x2List rfl (by decide) hz
  have hinit' : ∀ i, (x3List.getD i (x3List.headD 0)).testBit p.1 = true → (x2List.getD i (x2List.headD 0)).testBit p.2 = true := by
    intro i hi
    have := hinit i
    rw [hi] at this
    simpa using this
  have hres := foldl_rel (fun a b => a.testBit p.1 = true → b.testBit p.2 = true)
    (x3List.headD 0) (x2List.headD 0)
    (hinit' 0)
    (fun a3 a2 b3 b2 ha hb h => by
      simp only [Nat.testBit_lor, Bool.or_eq_true] at h ⊢
      rcases h with h | h
      · exact Or.inl (ha h)
      · exact Or.inr (hb h))
    (fun a3 a2 b3 b2 ha hb h => by
      simp only [Nat.testBit_land, Bool.and_eq_true] at h ⊢
      exact ⟨ha h.1, hb h.2⟩)
    gates x3List x2List rfl hinit'
  exact hres.2 idx

lemma bit_high_zero (gates : List (Bool × ℕ × ℕ)) (idx : ℕ) (k : ℕ) (hk : 58 ≤ k) :
    ((List.foldl (evalStep (x3List.headD 0)) x3List gates).getD idx (x3List.headD 0)).testBit k = false := by
  have hlt := getD_lt_of_all x3List (2 ^ 58) (by decide) lt58_check
  have hpow : 2 ^ 58 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
  have hinit : ∀ i, (x3List.getD i (x3List.headD 0)).testBit k = false := by
    intro i
    exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (hlt i) hpow)
  have hres := foldl_rel (fun a _ => a.testBit k = false)
    (x3List.headD 0) (x2List.headD 0)
    (hinit 0)
    (fun a3 a2 b3 b2 ha hb => by simp [ha, hb])
    (fun a3 a2 b3 b2 ha hb => by simp [ha, hb])
    gates x3List x2List rfl hinit
  exact hres.2 idx

end PEqualNP.Outside.L_meta_5104

theorem PEqualNP.Outside.L_meta_5104 : have x1 : List ℕ → List (Bool × ℕ × ℕ) → ℕ → ℕ := fun (x1 : List ℕ) (x2 : List (Bool × ℕ × ℕ)) (x3 : ℕ) =>   have x4 : ℕ := x1.headD (0 : ℕ);   (List.foldl         (fun (x5 : List ℕ) (x6 : Bool × ℕ × ℕ) =>           have x7 : ℕ → ℕ := fun (x7 : ℕ) => x5.getD x7 x4;           x5 ++ [if x6.1 = Bool.true then x7 x6.2.1 ||| x7 x6.2.2 else x7 x6.2.1 &&& x7 x6.2.2])         x1 x2).getD     x3 x4; have x2 : List ℕ := [(917681504273 : ℕ), (14878052356 : ℕ), (31886295704066 : ℕ), (257731462272 : ℕ), (42884715528480 : ℕ), (82789891049544 : ℕ), (248671168364547 : ℕ), (198670308868108 : ℕ), (158476001083504 : ℕ), (238332533539200 : ℕ), (176488259259904 : ℕ), (212188564320256 : ℕ), (280375465312256 : ℕ), (271282175737871 : ℕ), (280357743624591 : ℕ)]; have x3 : List ℕ := [(63038587666488 : ℕ), (256462815680 : ℕ), (4292497062759936 : ℕ), (8521481482240 : ℕ), (14003410187812864 : ℕ), (55389823207997440 : ℕ), (189297016294081033 : ℕ), (155696362464477250 : ℕ), (218994303132270608 : ℕ), (183565875465490436 : ℕ), (229736628138025984 : ℕ), (270286071508633728 : ℕ), (288160007407550752 : ℕ), (191866593364673099 : ℕ), (193001360500003407 : ℕ)]; ∀ (x4 : List (Bool × ℕ × ℕ)) (x5 : ℕ), x1 x2 x4 x5 = (262143 : ℕ) → x1 x3 x4 x5 ||| (7 : ℕ) = (2097151 : ℕ) := by
  intro x1 x2 x3 x4 x5 hx2
  change (List.foldl (PEqualNP.Outside.L_meta_5104.evalStep (PEqualNP.Outside.L_meta_5104.x2List.headD 0)) PEqualNP.Outside.L_meta_5104.x2List x4).getD x5 (PEqualNP.Outside.L_meta_5104.x2List.headD 0) = 262143 at hx2
  change (List.foldl (PEqualNP.Outside.L_meta_5104.evalStep (PEqualNP.Outside.L_meta_5104.x3List.headD 0)) PEqualNP.Outside.L_meta_5104.x3List x4).getD x5 (PEqualNP.Outside.L_meta_5104.x3List.headD 0) ||| 7 = 2097151
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_lor]
  by_cases hk3 : k < 3
  · have hmem : k ∈ List.range 3 := List.mem_range.mpr hk3
    have hboth := List.all_eq_true.mp PEqualNP.Outside.L_meta_5104.low_bits_check k hmem
    simp only [Bool.and_eq_true] at hboth
    simp [hboth.1, hboth.2]
  · have hk3ge : 3 ≤ k := Nat.le_of_not_lt hk3
    have h7 : (7 : ℕ).testBit k = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (by decide : (7 : ℕ) < 2 ^ 3) (Nat.pow_le_pow_right (by decide) hk3ge))
    rw [h7, Bool.or_false]
    by_cases hk21 : k < 21
    · have hmem : k ∈ List.range' 3 18 := by
        rw [List.mem_range']
        exact ⟨k - 3, by omega, by omega⟩
      have h2097151 : (2097151 : ℕ).testBit k = true :=
        List.all_eq_true.mp PEqualNP.Outside.L_meta_5104.mid_2097151_check k hmem
      have hex := List.all_eq_true.mp PEqualNP.Outside.L_meta_5104.eq_range_check k hmem
      rw [List.any_eq_true] at hex
      rcases hex with ⟨p, hp, hcond⟩
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
      rcases hcond with ⟨rfl, hb18⟩
      have heq := PEqualNP.Outside.L_meta_5104.bit_eq_of_mem x4 x5 p hp
      have hbmem : p.2 ∈ List.range 18 := List.mem_range.mpr hb18
      have h262143 : (262143 : ℕ).testBit p.2 = true :=
        List.all_eq_true.mp PEqualNP.Outside.L_meta_5104.mid_262143_check p.2 hbmem
      rw [heq, hx2, h262143, h2097151]
    · have hk21ge : 21 ≤ k := Nat.le_of_not_lt hk21
      have h2097151 : (2097151 : ℕ).testBit k = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (by decide : (2097151 : ℕ) < 2 ^ 21) (Nat.pow_le_pow_right (by decide) hk21ge))
      rw [h2097151]
      by_cases hk58 : k < 58
      · have hmem : k ∈ List.range' 21 37 := by
          rw [List.mem_range']
          exact ⟨k - 21, by omega, by omega⟩
        have hex := List.all_eq_true.mp PEqualNP.Outside.L_meta_5104.dom_range_check k hmem
        rw [List.any_eq_true] at hex
        rcases hex with ⟨p, hp, hcond⟩
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
        rcases hcond with ⟨rfl, hb18⟩
        cases hbit : ((List.foldl (PEqualNP.Outside.L_meta_5104.evalStep (PEqualNP.Outside.L_meta_5104.x3List.headD 0)) PEqualNP.Outside.L_meta_5104.x3List x4).getD x5 (PEqualNP.Outside.L_meta_5104.x3List.headD 0)).testBit p.1
        · rfl
        · have hdom := PEqualNP.Outside.L_meta_5104.bit_dom_of_mem x4 x5 p hp hbit
          rw [hx2] at hdom
          have hfalse : (262143 : ℕ).testBit p.2 = false :=
            Nat.testBit_lt_two_pow (lt_of_lt_of_le (by decide : (262143 : ℕ) < 2 ^ 18) (Nat.pow_le_pow_right (by decide) hb18))
          rw [hfalse] at hdom
          cases hdom
      · exact PEqualNP.Outside.L_meta_5104.bit_high_zero x4 x5 k (Nat.le_of_not_lt hk58)
