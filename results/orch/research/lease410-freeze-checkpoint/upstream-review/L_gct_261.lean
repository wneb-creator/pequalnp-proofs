import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.Linarith
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_261

-- Each pair of natural numbers encloses a nonnegative value after scaling.
-- Squaring and multiplication round outward, so the signs use only integer arithmetic.

def covers (s : ℕ) (b : ℕ × ℕ) (x : ℝ) : Prop :=
  (b.1 : ℝ) ≤ (s : ℝ) * x ∧ (s : ℝ) * x ≤ (b.2 : ℝ)

def boxMul (s : ℕ) (a b : ℕ × ℕ) : ℕ × ℕ :=
  (a.1 * b.1 / s, a.2 * b.2 / s + 1)

lemma boxMul_ok {s : ℕ} (hs : 0 < s) {a b : ℕ × ℕ} {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (ha : covers s a x) (hb : covers s b y) :
    covers s (boxMul s a b) (x*y) := by
  have sp : 0 < (s : ℝ) := by exact_mod_cast hs
  have lower : (a.1 * b.1 / s) * s ≤ a.1 * b.1 := Nat.div_mul_le_self _ _
  have upper : a.2 * b.2 ≤ (a.2 * b.2 / s + 1) * s := by
    have h := Nat.mod_add_div (a.2 * b.2) s
    have hrem := Nat.mod_lt (a.2 * b.2) hs
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (a.2 * b.2 / s)]
    omega
  constructor
  · apply le_of_mul_le_mul_right (a := (s : ℝ)) _ sp
    calc
      ((a.1 * b.1 / s : ℕ) : ℝ) * s ≤ (a.1 : ℝ) * b.1 := by exact_mod_cast lower
      _ ≤ ((s : ℝ) * x) * ((s : ℝ) * y) :=
        mul_le_mul ha.1 hb.1 (by positivity) (mul_nonneg sp.le hx)
      _ = ((s : ℝ) * (x*y)) * s := by ring
  · apply le_of_mul_le_mul_right (a := (s : ℝ)) _ sp
    calc
      ((s : ℝ) * (x*y)) * s = ((s : ℝ) * x) * ((s : ℝ) * y) := by ring
      _ ≤ (a.2 : ℝ) * b.2 :=
        mul_le_mul ha.2 hb.2 (mul_nonneg sp.le hy) (by positivity)
      _ ≤ ((a.2 * b.2 / s + 1 : ℕ) : ℝ) * s := by exact_mod_cast upper

def powerBox (s base : ℕ) : ℕ → ℕ → ℕ × ℕ
  | 0, _ => (s,s)
  | k+1, n =>
    let u := powerBox s base k (n/2)
    let v := boxMul s u u
    if n % 2 = 0 then v else boxMul s v (base,base)

lemma powerBox_ok {s b : ℕ} (hs : 0 < s) (k n : ℕ) (hn : n < 2^k) :
    covers s (powerBox s b k n) (((b : ℝ) / s)^n) := by
  have sp : 0 < (s : ℝ) := by exact_mod_cast hs
  have xp : 0 ≤ (b : ℝ)/s := by positivity
  have base : covers s (b,b) ((b : ℝ)/s) := by
    unfold covers
    rw [mul_div_cancel₀ _ sp.ne']
    exact ⟨le_rfl,le_rfl⟩
  induction k generalizing n with
  | zero =>
    have hn0 : n = 0 := by simpa using hn
    subst n
    simp [powerBox,covers]
  | succ k ih =>
    have half : n / 2 < 2^k := by rw [pow_succ] at hn; omega
    have h := ih (n/2) half
    have sq := boxMul_ok hs (pow_nonneg xp _) (pow_nonneg xp _) h h
    rw [← pow_add] at sq
    by_cases even : n % 2 = 0
    · simp only [powerBox,even,ite_true]
      convert sq using 2; omega
    · simp only [powerBox,even,ite_false]
      have step := boxMul_ok hs (pow_nonneg xp _) xp sq base
      rw [← pow_succ] at step
      convert step using 2; omega

open Polynomial

def weightedBox (s b : ℕ) : List (ℕ × ℕ) → ℕ × ℕ
  | [] => (0,0)
  | t :: ts =>
    let z := powerBox s b 42 t.2
    let tail := weightedBox s b ts
    (t.1 * z.1 + tail.1, t.1 * z.2 + tail.2)

def weightedEval (x : ℝ) : List (ℕ × ℕ) → ℝ
  | [] => 0
  | t :: ts => (t.1 : ℝ) * x^t.2 + weightedEval x ts

lemma weighted_ok {s b : ℕ} (hs : 0 < s) (ts : List (ℕ × ℕ))
    (h : ∀ t ∈ ts, t.2 < 2^42) :
    covers s (weightedBox s b ts) (weightedEval ((b : ℝ)/s) ts) := by
  induction ts with
  | nil => simp [covers, weightedBox, weightedEval]
  | cons t ts ih =>
    have ht := powerBox_ok (b := b) hs 42 t.2 (h t (by simp))
    have hz := ih (fun u hu => h u (by simp [hu]))
    rcases ht with ⟨tl,tu⟩
    rcases hz with ⟨zl,zu⟩
    have coef : (0 : ℝ) ≤ t.1 := by positivity
    simp only [covers, weightedBox, weightedEval, Nat.cast_add, Nat.cast_mul]
    constructor
    · nlinarith only [mul_le_mul_of_nonneg_left tl coef,zl]
    · nlinarith only [mul_le_mul_of_nonneg_left tu coef,zu]

def scale : ℕ := 20 * 10^32
def base (i : ℕ) : ℕ := (19999999999997 + 6*i)*10^20
noncomputable def point (i : ℕ) : ℝ := (base i : ℝ)/scale
def den : ℕ := 1000000000000

noncomputable def tri (a b c : ℝ) (i j k : ℕ) : Polynomial ℝ :=
  monomial i a + monomial j b + monomial k c

lemma tri_sparse (a b c : ℝ) (i j k : ℕ) : (tri a b c i j k).support.card ≤ 3 := by
  have one (z : ℝ) (n : ℕ) : (monomial n z).support.card ≤ 1 := by
    simpa using Finset.card_le_card (support_monomial_subset n z)
  have sum_le (p q : Polynomial ℝ) : (p+q).support.card ≤ p.support.card + q.support.card :=
    (Finset.card_le_card (support_add ..)).trans (Finset.card_union_le _ _)
  unfold tri
  exact (sum_le _ _).trans (by
    have ab := sum_le (monomial i a) (monomial j b)
    have ha := one a i
    have hb := one b j
    have hc := one c k
    omega)

noncomputable def polyF : Polynomial ℝ :=
  tri 1 (-43365112862 / (den : ℝ)) (1397048929 / (den : ℝ))
    46227877 448900690055 987294467927

noncomputable def polyG : Polynomial ℝ :=
  tri (-1000331817298 / (den : ℝ)) (-43584165131 / (den : ℝ)) (109442842 / (den : ℝ))
    0 454650486655 1454650486655

def posTerms : List (ℕ × ℕ) :=
  [(den * den,0),
   (den * 109442842,46227877 + 1454650486655),
   (43365112862 * 1000331817298,448900690055),
   (43365112862 * 43584165131,448900690055 + 454650486655),
   (1397048929 * 109442842,987294467927 + 1454650486655)]

def negTerms : List (ℕ × ℕ) :=
  [(den * 1000331817298,46227877),
   (den * 43584165131,46227877 + 454650486655),
   (43365112862 * 109442842,448900690055 + 1454650486655),
   (1397048929 * 1000331817298,987294467927),
   (1397048929 * 43584165131,987294467927 + 454650486655)]

lemma eval_eq (x : ℝ) : (den : ℝ)^2 * (polyF * polyG + 1).eval x =
    weightedEval x posTerms - weightedEval x negTerms := by
  simp only [polyF,polyG,tri,eval_add,eval_mul,eval_one,eval_monomial,
    posTerms,negTerms,weightedEval,den,Nat.cast_mul,Nat.cast_ofNat,pow_zero,pow_add]
  ring

lemma pos_size : ∀ t ∈ posTerms, t.2 < 2^42 := by decide
lemma neg_size : ∀ t ∈ negTerms, t.2 < 2^42 := by decide

def boxesCheck (i : ℕ) (p n : ℕ × ℕ) : Bool :=
  if i%2 = 0 then decide (n.2 < p.1) else decide (p.2 < n.1)

def checkPoint (i : ℕ) : Bool :=
  boxesCheck i (weightedBox scale (base i) posTerms) (weightedBox scale (base i) negTerms)

lemma points_checked : ∀ i : Fin 9, checkPoint i.val = true := by decide +kernel

lemma sign_from_boxes (i s : ℕ) (p n : ℕ × ℕ) (a b v d : ℝ)
    (hs : 0 < s) (hd : 0 < d) (hp : covers s p a) (hn : covers s n b)
    (hv : d * v = a - b) (hc : boxesCheck i p n = true) :
    if i%2=0 then 0<v else v<0 := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  by_cases h : i%2 = 0
  · simp only [h,ite_true]
    simp only [boxesCheck,h,ite_true,decide_eq_true_eq] at hc
    have hR : (n.2 : ℝ) < p.1 := by exact_mod_cast hc
    have hba := (mul_lt_mul_iff_right₀ hsR).mp (hn.2.trans_lt (hR.trans_le hp.1))
    exact pos_of_mul_pos_right (hv.symm ▸ sub_pos.mpr hba) hd.le
  · simp only [h,ite_false]
    simp only [boxesCheck,h,ite_false,decide_eq_true_eq] at hc
    have hR : (p.2 : ℝ) < n.1 := by exact_mod_cast hc
    have hab := (mul_lt_mul_iff_right₀ hsR).mp (hp.2.trans_lt (hR.trans_le hn.1))
    exact neg_of_mul_neg_right (hv.symm ▸ sub_neg.mpr hab) hd.le

lemma point_sign (i : ℕ) (hi : i < 9) :
    if i%2=0 then 0 < (polyF * polyG + 1).eval (point i)
    else (polyF * polyG + 1).eval (point i) < 0 :=
  sign_from_boxes i scale (weightedBox scale (base i) posTerms) (weightedBox scale (base i) negTerms)
    (weightedEval (point i) posTerms) (weightedEval (point i) negTerms)
    ((polyF * polyG + 1).eval (point i)) ((den : ℝ)^2)
    (by decide) (by norm_num [den])
    (weighted_ok (b := base i) (by decide : 0 < scale) posTerms pos_size)
    (weighted_ok (b := base i) (by decide : 0 < scale) negTerms neg_size)
    (eval_eq (point i)) (points_checked ⟨i,hi⟩)

open Polynomial

theorem eightRoots (P : Polynomial ℝ) (point : ℕ → ℝ)
    (hpos : ∀ n ≤ 8, 0 < point n)
    (hinc : ∀ n < 8, point n < point (n + 1))
    (hcross : ∀ n < 8, P.eval (point n) * P.eval (point (n + 1)) < 0) :
    7 < (P.roots.toFinset.filter (fun x : ℝ => 0 < x)).card := by
  classical
  have hp : P ≠ 0 := by
    intro hp
    have h := hcross 0 (by omega)
    simp [hp] at h
  have hz (n : ℕ) (hn : n < 8) :
      ∃ x : ℝ, point n < x ∧ x < point (n + 1) ∧ P.eval x = 0 := by
    have hs := (mul_neg_iff.mp (hcross n hn))
    rcases hs with h | h
    · obtain ⟨x, hx, he⟩ := intermediate_value_Ioo' (hinc n hn).le P.continuous.continuousOn
        (show (0 : ℝ) ∈ Set.Ioo (P.eval (point (n + 1))) (P.eval (point n)) from ⟨h.2, h.1⟩)
      exact ⟨x, hx.1, hx.2, he⟩
    · obtain ⟨x, hx, he⟩ := intermediate_value_Ioo (hinc n hn).le P.continuous.continuousOn
        (show (0 : ℝ) ∈ Set.Ioo (P.eval (point n)) (P.eval (point (n + 1))) from ⟨h.1, h.2⟩)
      exact ⟨x, hx.1, hx.2, he⟩
  let root : Fin 8 → ℝ := fun i => Classical.choose (hz i.val i.isLt)
  have hroot (i : Fin 8) :
      point i.val < root i ∧ root i < point (i.val + 1) ∧ P.eval (root i) = 0 :=
    Classical.choose_spec (hz i.val i.isLt)
  have hmono : StrictMonoOn point (Set.Iic 8) :=
    strictMonoOn_Iic_of_lt_succ (by simpa using hinc)
  have hri : StrictMono root := by
    intro i j hij
    have hij' : i.val + 1 ≤ j.val := by omega
    have hh : point (i.val + 1) ≤ point j.val := by
      rcases eq_or_lt_of_le hij' with he | he
      · rw [he]
      · exact (hmono (by simp) (by simp) he).le
    exact lt_of_lt_of_le (hroot i).2.1 (le_trans hh (hroot j).1.le)
  have hcard : 8 ≤ (P.roots.toFinset.filter (fun x : ℝ => 0 < x)).card := by
    have hc := Finset.card_le_card_of_injOn root
      (s := Finset.univ)
      (t := P.roots.toFinset.filter (fun x : ℝ => 0 < x))
      (by
        intro i hi
        apply Finset.mem_filter.mpr
        constructor
        · apply Multiset.mem_toFinset.mpr
          exact (Polynomial.mem_roots hp).mpr (hroot i).2.2
        · exact lt_trans (hpos i.val (by omega)) (hroot i).1)
      (by
        intro i hi j hj h
        exact hri.injective h)
    simpa using hc
  omega

lemma point_pos (n : ℕ) : 0 < point n := by
  have hb : 0 < base n := by unfold base; positivity
  have hs : 0 < scale := by decide
  exact div_pos (by exact_mod_cast hb) (by exact_mod_cast hs)

lemma point_inc (n : ℕ) : point n < point (n+1) := by
  have hs : (0 : ℝ) < scale := by norm_num [scale]
  apply (div_lt_div_iff_of_pos_right hs).mpr
  have h : 19999999999997 + 6*n < 19999999999997 + 6*(n+1) := by omega
  exact_mod_cast (Nat.mul_lt_mul_of_pos_right h (by decide : 0 < 10^20))

lemma crossing (n : ℕ) (hn : n < 8) :
    (polyF*polyG+1).eval (point n) * (polyF*polyG+1).eval (point (n+1)) < 0 := by
  have hl := point_sign n (by omega)
  have hr := point_sign (n+1) (by omega)
  by_cases he : n%2 = 0
  · have ho : ¬ (n+1)%2 = 0 := by omega
    rw [ite_eq_left he] at hl
    rw [ite_eq_right ho] at hr
    exact mul_neg_of_pos_of_neg hl hr
  · have ho : (n+1)%2 = 0 := by omega
    rw [ite_eq_right he] at hl
    rw [ite_eq_left ho] at hr
    exact mul_neg_of_neg_of_pos hl hr

end PEqualNP.Outside.L_gct_261

theorem PEqualNP.Outside.L_gct_261 : ¬ (∀ f g : Polynomial ℝ, (f.support.card ≤ 3 ∧ g.support.card ≤ 3) → ((f * g + 1).roots.toFinset.filter (fun x : ℝ => 0 < x)).card ≤ 7) := by
  intro bound
  have h := bound PEqualNP.Outside.L_gct_261.polyF PEqualNP.Outside.L_gct_261.polyG
    ⟨PEqualNP.Outside.L_gct_261.tri_sparse .., PEqualNP.Outside.L_gct_261.tri_sparse ..⟩
  exact (not_lt_of_ge h) (PEqualNP.Outside.L_gct_261.eightRoots _ PEqualNP.Outside.L_gct_261.point
    (fun n _ => PEqualNP.Outside.L_gct_261.point_pos n) (fun n _ => PEqualNP.Outside.L_gct_261.point_inc n) PEqualNP.Outside.L_gct_261.crossing)
