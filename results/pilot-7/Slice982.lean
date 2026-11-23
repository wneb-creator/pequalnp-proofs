import EarlyUpper982
namespace PEqualNP.Outside.L_meta_982_aux.Finite.Slice
open PEqualNP.Outside.L_meta_982_aux.Finite.Live

def c0 (a b c d e f : Bool) : Bool :=
  ((!a) && d) || ((!a) && (!d) && (!b) && (!c)) ||
  (a && d && e && f) || (a && (!d) && (!b) && (!c) && e && f)
def c1 (a b c d e f : Bool) : Bool :=
  ((!a) && (!d) && (b != c)) || (a && d && (e != f)) ||
  (a && (!d) && (!(b && c)) && (e || f) && ((b != c) || (e != f)))
def c2 (a b c d e f : Bool) : Bool :=
  ((!a) && (!d) && b && c) || (a && d && (!e) && (!f)) ||
  (a && (!d) && ((b && c) != ((!e) && (!f))))

theorem c0_eq : ∀ a b c d e f : Bool, c0 a b c d e f = decide (value6 a b c d e f = 0) := by decide +kernel
theorem c1_eq : ∀ a b c d e f : Bool, c1 a b c d e f = decide (value6 a b c d e f = 1) := by decide +kernel
theorem c2_eq : ∀ a b c d e f : Bool, c2 a b c d e f = decide (value6 a b c d e f = 2) := by decide +kernel

def cls (m a b c d e f : Nat) : Nat × Nat × Nat :=
  let na := a ^^^ m
  let nb := b ^^^ m
  let nc := c ^^^ m
  let nd := d ^^^ m
  let ne := e ^^^ m
  let nf := f ^^^ m
  let x1 := b ^^^ c
  let y1 := e ^^^ f
  let x2 := b &&& c
  let y2 := ne &&& nf
  ((na &&& d) ||| (na &&& nd &&& nb &&& nc) |||
     (a &&& d &&& e &&& f) ||| (a &&& nd &&& nb &&& nc &&& e &&& f),
   (na &&& nd &&& x1) ||| (a &&& d &&& y1) |||
     (a &&& nd &&& (x2 ^^^ m) &&& (e ||| f) &&& (x1 ||| y1)),
   (na &&& nd &&& x2) ||| (a &&& d &&& y2) ||| (a &&& nd &&& (x2 ^^^ y2)))

theorem cls_bits (m a b c d e f i : Nat) (hm : m.testBit i = true) :
    (cls m a b c d e f).1.testBit i = decide (value6 (a.testBit i) (b.testBit i) (c.testBit i) (d.testBit i) (e.testBit i) (f.testBit i) = 0) ∧
    (cls m a b c d e f).2.1.testBit i = decide (value6 (a.testBit i) (b.testBit i) (c.testBit i) (d.testBit i) (e.testBit i) (f.testBit i) = 1) ∧
    (cls m a b c d e f).2.2.testBit i = decide (value6 (a.testBit i) (b.testBit i) (c.testBit i) (d.testBit i) (e.testBit i) (f.testBit i) = 2) := by
  simp only [cls,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,hm,Bool.xor_true]
  constructor
  · simpa only [c0,Bool.and_assoc] using c0_eq (a.testBit i) (b.testBit i) (c.testBit i) (d.testBit i) (e.testBit i) (f.testBit i)
  constructor
  · simpa only [c1,Bool.and_assoc] using c1_eq (a.testBit i) (b.testBit i) (c.testBit i) (d.testBit i) (e.testBit i) (f.testBit i)
  · simpa only [c2,Bool.and_assoc] using c2_eq (a.testBit i) (b.testBit i) (c.testBit i) (d.testBit i) (e.testBit i) (f.testBit i)

def fld (v start width : Nat) : Nat := (v / 2^start) % 2^width

theorem fld_bit (v start width i : Nat) (hi : i < width) :
    (fld v start width).testBit i = v.testBit (i+start) := by
  simp [fld,Nat.testBit_mod_two_pow,Nat.testBit_div_two_pow,hi]

def profile (k p v : Nat) : Nat × Nat × Nat :=
  cls (lo p) (fld v k p) (fld v (k+p) p) (fld v (k+2*p) p)
    (fld v 0 p) (fld v p p) (fld v (2*p) p)
def scoreAt (k p i v : Nat) : Nat :=
  eval6 (i+k) (i+(k+p)) (i+(k+2*p)) i (i+p) (i+2*p) v

theorem profile_bits (k p v i : Nat) (hi : i < p) :
    (profile k p v).1.testBit i = decide (scoreAt k p i v = 0) ∧
    (profile k p v).2.1.testBit i = decide (scoreAt k p i v = 1) ∧
    (profile k p v).2.2.testBit i = decide (scoreAt k p i v = 2) := by
  have h := cls_bits (lo p) (fld v k p) (fld v (k+p) p) (fld v (k+2*p) p)
    (fld v 0 p) (fld v p p) (fld v (2*p) p) i (by simp [lo,Nat.testBit_two_pow_sub_one,hi])
  have he : value6 ((fld v k p).testBit i) ((fld v (k+p) p).testBit i)
      ((fld v (k+2*p) p).testBit i) ((fld v 0 p).testBit i)
      ((fld v p p).testBit i) ((fld v (2*p) p).testBit i) = scoreAt k p i v := by
    simp only [scoreAt,eval6,fld_bit _ _ _ _ hi,Nat.add_zero]
  rw [he] at h
  exact h

def step (r q : Nat × Nat × Nat) : Nat × Nat × Nat :=
  (r.1 &&& q.1,
   (r.2.1 &&& q.1) ||| (r.1 &&& q.2.1),
   (r.2.2 &&& q.1) ||| (r.2.1 &&& q.2.1) ||| (r.1 &&& q.2.2))

def Bits (r : Nat × Nat × Nat) (i a : Nat) : Prop :=
  r.1.testBit i = decide (a=0) ∧ r.2.1.testBit i = decide (a=1) ∧ r.2.2.testBit i = decide (a=2)

theorem step_bits {r q i a b} (hr : Bits r i a) (hq : Bits q i b) :
    Bits (step r q) i (a+b) := by
  rcases hr with ⟨h0,h1,h2⟩
  rcases hq with ⟨g0,g1,g2⟩
  simp only [Bits,step,Nat.testBit_and,Nat.testBit_or,h0,h1,h2,g0,g1,g2]
  constructor
  · apply Bool.eq_iff_iff.2
    simp only [Bool.and_eq_true,decide_eq_true_eq]
    omega
  constructor
  · apply Bool.eq_iff_iff.2
    simp only [Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq]
    omega
  · apply Bool.eq_iff_iff.2
    simp only [Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq]
    omega

def union (r : Nat × Nat × Nat) : Nat := r.1 ||| r.2.1 ||| r.2.2

def roll (k p : Nat) : Nat × Nat × Nat → List Nat → Nat × Nat × Nat
  | r,[] => r
  | r,v::ws => roll k p (step r (profile k p v)) ws

theorem roll_bits (k p i : Nat) (hi : i < p) (ws : List Nat)
    (r : Nat × Nat × Nat) (a : Nat) (hr : Bits r i a) :
    Bits (roll k p r ws) i (a + (ws.map (scoreAt k p i)).sum) := by
  induction ws generalizing r a with
  | nil => simpa [roll] using hr
  | cons v ws ih =>
    have h := ih (step r (profile k p v)) (a+scoreAt k p i v)
      (step_bits hr (profile_bits k p v i hi))
    simpa only [roll,List.map_cons,List.sum_cons,Nat.add_assoc] using h

theorem roll_outside (k p i : Nat) (ws : List Nat) (r : Nat × Nat × Nat)
    (hr : r.1.testBit i = false ∧ r.2.1.testBit i = false ∧ r.2.2.testBit i = false) :
    (roll k p r ws).1.testBit i = false ∧
    (roll k p r ws).2.1.testBit i = false ∧ (roll k p r ws).2.2.testBit i = false := by
  induction ws generalizing r with
  | nil => exact hr
  | cons v ws ih =>
    apply ih
    simp [step,Nat.testBit_and,Nat.testBit_or,hr.1,hr.2.1,hr.2.2]

theorem roll_zero (k p : Nat) (ws : List Nat) : roll k p (0,0,0) ws = (0,0,0) := by
  induction ws with
  | nil => rfl
  | cons v ws ih => simpa [roll,step] using ih

def fastRoll (k p : Nat) : Nat × Nat × Nat → List Nat → Nat × Nat × Nat
  | r,[] => r
  | r,v::ws => if union r = 0 then r else fastRoll k p (step r (profile k p v)) ws

theorem fastRoll_eq (k p : Nat) (r : Nat × Nat × Nat) (ws : List Nat) :
    fastRoll k p r ws = roll k p r ws := by
  induction ws generalizing r with
  | nil => rfl
  | cons v ws ih =>
    simp only [fastRoll]
    split
    · rename_i hz
      rcases r with ⟨z,o,t⟩
      simp only [union,Nat.or_eq_zero_iff] at hz
      rcases hz with ⟨⟨rfl,rfl⟩,rfl⟩
      simp [roll_zero]
    · exact ih _

def scr (k p s : Nat) (ws : List Nat) : Bool :=
  ws.length == s+1 && !(union (fastRoll k p (lo p,0,0) ws) == 0)

theorem goal_score (k p i : Nat) (hk : 3*p ≤ k) (hi : i < p) :
    scoreAt k p i (goal k) = 3 := by
  have hi0 : i < k := by omega
  have hi1 : i+p < k := by omega
  have hi2 : i+2*p < k := by omega
  have ha0 : k ≤ i+k := by omega
  have ha1 : k ≤ i+(k+p) := by omega
  have ha2 : k ≤ i+(k+2*p) := by omega
  simp [scoreAt,eval6,goal,lo,Nat.testBit_shiftLeft,Nat.testBit_two_pow_sub_one,
    hi0,hi1,hi2,ha0,ha1,ha2,Nat.not_le.mpr hi0,Nat.not_le.mpr hi1,Nat.not_le.mpr hi2,show i+k-k=i by omega,
    show i+(k+p)-k=i+p by omega,show i+(k+2*p)-k=i+2*p by omega,value6]

theorem scr_no {k p s ws} (hk : 3*p ≤ k) (h : NatRun (mask k) (goal k) s ws) :
    scr k p s ws = false := by
  by_cases hl : ws.length = s+1
  · have hz : union (roll k p (lo p,0,0) ws) = 0 := by
      apply Nat.eq_of_testBit_eq
      intro i
      by_cases hi : i < p
      · have hb := roll_bits k p i hi ws (lo p,0,0) 0 (by
          simp [Bits,lo,Nat.testBit_two_pow_sub_one,hi])
        have hn := eval6_bound h hl (i+k) (i+(k+p)) (i+(k+2*p)) i (i+p) (i+2*p)
        have hs : 3 ≤ (ws.map (scoreAt k p i)).sum := by
          change scoreAt k p i (goal k) ≤ (ws.map (scoreAt k p i)).sum at hn
          rwa [goal_score k p i hk hi] at hn
        rcases hb with ⟨h0,h1,h2⟩
        simp only [Nat.zero_add] at h0 h1 h2
        have hne0 : (ws.map (scoreAt k p i)).sum ≠ 0 := by omega
        have hne1 : (ws.map (scoreAt k p i)).sum ≠ 1 := by omega
        have hne2 : (ws.map (scoreAt k p i)).sum ≠ 2 := by omega
        simp [union,Nat.testBit_or,h0,h1,h2,hne0,hne1,hne2]
      · have hb := roll_outside k p i ws (lo p,0,0) (by
          simp [lo,Nat.testBit_two_pow_sub_one,hi])
        simp [union,Nat.testBit_or,hb.1,hb.2.1,hb.2.2]
    simp [scr,fastRoll_eq,hz]
  · simp [scr,hl]

theorem scr_no_le {k p t s ws} (hk : 3*p ≤ k)
    (h : NatRun (mask k) (goal k) t ws) (ht : t ≤ s) : scr k p s ws = false := by
  by_cases hl : ws.length = s+1
  · have hr := run_len h
    have he : t = s := by omega
    subst t
    exact scr_no hk h
  · simp [scr,hl]

end PEqualNP.Outside.L_meta_982_aux.Finite.Slice
