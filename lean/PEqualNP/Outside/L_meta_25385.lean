import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

-- The checker of live-state certificates with cofactor cuts (the generic part, up to the data) is the one of the checked
-- V_meta_9945__k9 (same repository, Apache-2.0); the certificates below are new.

namespace PEqualNP.Outside.L_meta_25385_aux

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def mask256 : Nat := 2 ^ 256 - 1

def negD (d w : Nat) : Nat := (w ^^^ mask256) &&& d
def andD (d a b : Nat) : Nat := (a &&& b) &&& d
def orD (d a b : Nat) : Nat := (a ||| b) &&& d
def binD (d : Nat) (isOr : Bool) (a b : Nat) : Nat := if isOr then orD d a b else andD d a b

def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

def RunD (d y : Nat) (t : ℕ) (ws : List Nat) : Prop :=
  ∀ P : ℕ → List Nat → Prop, P 0 [y] →
    (∀ {s xs zs}, List.Perm xs zs → P s xs → P s zs) →
    (∀ {s a r} (save : Bool),
      negD d a ≠ 0 → negD d a ≠ d → negD d a ∉ (a :: r) →
      P s (negD d a :: kept save a r) → P (s + 1) (a :: r)) →
    (∀ {s a b r} (c ka kb : Bool),
      (if c then andD d a b else orD d a b) ≠ 0 →
      (if c then andD d a b else orD d a b) ≠ d →
      (if c then andD d a b else orD d a b) ∉ (a :: b :: r) →
      P s ((if c then andD d a b else orD d a b) :: kept ka a (kept kb b r)) →
      P (s + 1) (a :: b :: r)) → P t ws

section RunFacts
variable {d y : Nat}

theorem Run.done : RunD d y 0 [y] := fun _ dn _ _ _ => dn
theorem Run.perm {s xs zs} (p : List.Perm xs zs) (h : RunD d y s xs) :
    RunD d y s zs := fun P dn q u b => q p (h P dn q u b)
theorem Run.one {s a r} (save : Bool)
    (h0 : negD d a ≠ 0) (hd : negD d a ≠ d) (hm : negD d a ∉ (a :: r))
    (h : RunD d y s (negD d a :: kept save a r)) :
    RunD d y (s + 1) (a :: r) := fun P dn q u b => u save h0 hd hm (h P dn q u b)
theorem Run.two {s a b r} (c ka kb : Bool)
    (h0 : (if c then andD d a b else orD d a b) ≠ 0)
    (hd : (if c then andD d a b else orD d a b) ≠ d)
    (hm : (if c then andD d a b else orD d a b) ∉ (a :: b :: r))
    (h : RunD d y s ((if c then andD d a b else orD d a b) :: kept ka a (kept kb b r))) :
    RunD d y (s + 1) (a :: b :: r) := fun P dn q u v => v c ka kb h0 hd hm (h P dn q u v)

theorem Run.fold {P : ∀ t ws, RunD d y t ws → Prop}
    (done : P 0 [y] Run.done)
    (perm : ∀ {s xs zs} (hp : List.Perm xs zs) (h : RunD d y s xs),
      P s xs h → P s zs (Run.perm hp h))
    (one : ∀ {s a r} (save : Bool)
      (h0 : negD d a ≠ 0) (hd : negD d a ≠ d) (hm : negD d a ∉ (a :: r))
      (h : RunD d y s (negD d a :: kept save a r)),
      P _ _ h → P _ _ (Run.one save h0 hd hm h))
    (two : ∀ {s a b r} (c ka kb : Bool)
      (h0 : (if c then andD d a b else orD d a b) ≠ 0)
      (hd : (if c then andD d a b else orD d a b) ≠ d)
      (hm : (if c then andD d a b else orD d a b) ∉ (a :: b :: r))
      (h : RunD d y s ((if c then andD d a b else orD d a b) :: kept ka a (kept kb b r))),
      P _ _ h → P _ _ (Run.two c ka kb h0 hd hm h))
    {t ws} (h : RunD d y t ws) : P t ws h := by
  have hex := h (fun s xs => ∃ h' : RunD d y s xs, P s xs h')
    ⟨Run.done, done⟩
    (fun hp ⟨h', ih⟩ => ⟨Run.perm hp h', perm hp h' ih⟩)
    (fun k h0 hd hm ⟨h', ih⟩ => ⟨Run.one k h0 hd hm h', one k h0 hd hm h' ih⟩)
    (fun c a b h0 hd hm ⟨h', ih⟩ => ⟨Run.two c a b h0 hd hm h', two c a b h0 hd hm h' ih⟩)
  exact hex.elim fun _ hp => hp
end RunFacts

theorem kept_map {α β : Type} (e : α → β) (b : Bool) (x : α) (xs : List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e) := by cases b <;> simp [kept]

theorem mem_kept {α : Type} (b : Bool) (x a : α) (xs : List α) :
    a ∈ kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs := by cases b <;> simp [kept]

theorem nodup_kept {α : Type} (b : Bool) (x : α) (xs : List α) (h : xs.Nodup) (hx : x ∉ xs) :
    (kept b x xs).Nodup := by
  cases b
  · simpa [kept] using h
  · simpa [kept] using And.intro hx h

theorem keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys) := by cases b <;> simpa [kept] using p

theorem run_len {d y s xs} (h : RunD d y s xs) :
    xs.length ≤ s + 1 := by
  induction h using Run.fold with
  | done => simp
  | perm hp _ ih => rwa [← hp.length_eq]
  | one save _ _ _ _ ih => cases save <;> simp_all [kept] <;> omega
  | two conj ka kb _ _ _ _ ih => cases ka <;> cases kb <;> simp_all [kept] <;> omega

theorem zero_done {d y t ws} (h : RunD d y t ws) :
    t = 0 → ws = [y] := by
  induction h using Run.fold with
  | done => simp
  | perm p _ ih => intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | one => simp
  | two => simp

def IsConst (d w : Nat) : Prop := (w &&& d) = 0 ∨ (w &&& d) = d
def isConstB (d w : Nat) : Bool := (w &&& d == 0) || (w &&& d == d)

theorem isConstB_iff (d w : Nat) : isConstB d w = true ↔ IsConst d w := by
  simp [isConstB, IsConst]

def Avail (d : Nat) (bank : List Nat) (w : Nat) : Prop :=
  IsConst d w ∨ ∃ v ∈ bank, (v &&& d) = (w &&& d)

def availB (d : Nat) (bank : List Nat) (w : Nat) : Bool :=
  let m := w &&& d
  m == 0 || m == d || bank.any (fun v => (v &&& d) == m)

theorem availB_iff (d : Nat) (bank : List Nat) (w : Nat) :
    availB d bank w = true ↔ Avail d bank w := by
  simp [availB, Avail, IsConst, or_assoc]

def NatReach (d : Nat) (roots : List Nat) : Nat → List Nat → Prop
  | 0, bank => bank = roots
  | p + 1, bank =>
    (∃ b a, bank = negD d a :: b ∧ NatReach d roots p b ∧ Avail d b a) ∨
    (∃ b a c op, bank = binD d op a c :: b ∧ NatReach d roots p b ∧ Avail d b a ∧ Avail d b c)

def Lower (d : Nat) (roots : List Nat) (T : Nat) (L : Nat) : Prop :=
  ∀ p bank, NatReach d roots p bank → Avail d bank T → L ≤ p

theorem mask256_bit (i : Nat) : mask256.testBit i = decide (i < 256) := by
  rw [mask256, Nat.testBit_two_pow_sub_one]

theorem negD_and_sub {d d1 : Nat} (hd : d &&& mask256 = d) (hsub : d &&& d1 = d) (a : Nat) :
    negD d1 a &&& d = negD d a := by
  apply Nat.eq_of_testBit_eq; intro i
  have h1 := congrArg (fun v => v.testBit i) hd
  have h2 := congrArg (fun v => v.testBit i) hsub
  simp only [negD, Nat.testBit_and, Nat.testBit_xor] at *
  cases hi : d.testBit i <;> simp_all

theorem andD_and_sub {d d1 : Nat} (hsub : d &&& d1 = d) (a b : Nat) :
    andD d1 a b &&& d = andD d a b := by
  apply Nat.eq_of_testBit_eq; intro i
  have h2 := congrArg (fun v => v.testBit i) hsub
  simp only [andD, Nat.testBit_and] at *
  cases hi : d.testBit i <;> simp_all

theorem orD_and_sub {d d1 : Nat} (hsub : d &&& d1 = d) (a b : Nat) :
    orD d1 a b &&& d = orD d a b := by
  apply Nat.eq_of_testBit_eq; intro i
  have h2 := congrArg (fun v => v.testBit i) hsub
  simp only [orD, Nat.testBit_and, Nat.testBit_or] at *
  cases hi : d.testBit i <;> simp_all

theorem negD_const {d : Nat} (hd : d &&& mask256 = d) {a : Nat} (hc : IsConst d a) :
    IsConst d (negD d a) := by
  rcases hc with h0 | h1
  · right; apply Nat.eq_of_testBit_eq; intro i
    have h0i := congrArg (fun v => v.testBit i) h0
    have hdi := congrArg (fun v => v.testBit i) hd
    simp only [negD, Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit] at *
    cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
  · left; apply Nat.eq_of_testBit_eq; intro i
    have h1i := congrArg (fun v => v.testBit i) h1
    have hdi := congrArg (fun v => v.testBit i) hd
    simp only [negD, Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit] at *
    cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all

theorem binD_const_left {d : Nat} {a b : Nat} (op : Bool) (hc : IsConst d a) :
    (binD d op a b &&& d = 0) ∨ (binD d op a b &&& d = d) ∨ (binD d op a b &&& d = b &&& d) := by
  rcases hc with h0 | h1
  · cases op
    · left; apply Nat.eq_of_testBit_eq; intro i
      have h0i := congrArg (fun v => v.testBit i) h0
      simp only [binD, andD, Nat.testBit_and, Nat.zero_testBit, ite_false] at *
      cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
    · right; right; apply Nat.eq_of_testBit_eq; intro i
      have h0i := congrArg (fun v => v.testBit i) h0
      simp only [binD, orD, Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit, ite_true] at *
      cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
  · cases op
    · right; right; apply Nat.eq_of_testBit_eq; intro i
      have h1i := congrArg (fun v => v.testBit i) h1
      simp only [binD, andD, Nat.testBit_and, ite_false] at *
      cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
    · right; left; apply Nat.eq_of_testBit_eq; intro i
      have h1i := congrArg (fun v => v.testBit i) h1
      simp only [binD, orD, Nat.testBit_and, Nat.testBit_or, ite_true] at *
      cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all

theorem binD_comm (d : Nat) (op : Bool) (a b : Nat) : binD d op a b = binD d op b a := by
  cases op <;> simp [binD, andD, orD, Nat.and_comm, Nat.or_comm]

theorem avail_cons {d : Nat} {bank : List Nat} (z w : Nat) (h : Avail d bank w) :
    Avail d (z :: bank) w := by
  rcases h with hc | ⟨v, hv, he⟩
  · exact Or.inl hc
  · exact Or.inr ⟨v, List.mem_cons_of_mem _ hv, he⟩

theorem avail_of_eq {d : Nat} {bank : List Nat} {v w : Nat}
    (he : v &&& d = w &&& d) (h : Avail d bank v) : Avail d bank w := by
  rcases h with (h0 | h1) | ⟨u, hu, hue⟩
  · exact Or.inl (Or.inl (he.symm.trans h0))
  · exact Or.inl (Or.inr (he.symm.trans h1))
  · exact Or.inr ⟨u, hu, hue.trans he⟩

theorem countP_kept_ge {α : Type} (p : α → Bool) (b : Bool) (a : α) (xs : List α) :
    xs.countP p ≤ (kept b a xs).countP p := by
  cases b <;> simp [kept, List.countP_cons] <;> split <;> omega

theorem contraction {d d1 T : Nat} (hd : d &&& mask256 = d) (hsub : d &&& d1 = d)
    (hnc : ¬ IsConst d T) {s ws} (h : RunD d1 T s ws) {roots p bank}
    (hp : NatReach d roots p bank) (hs : ∀ w ∈ ws, Avail d bank w) :
    ∃ q next, NatReach d roots q next ∧ Avail d next T ∧
      q + ws.countP (isConstB d) ≤ p + s := by
  induction h using Run.fold generalizing p bank with
  | done =>
    have hfalse : isConstB d T = false := by
      cases hc : isConstB d T with
      | false => rfl
      | true => exact absurd ((isConstB_iff d T).1 hc) hnc
    exact ⟨p, bank, hp, hs T (by simp), by simp [hfalse]⟩
  | perm eq _ ih =>
    obtain ⟨q, next, hq, ht, hle⟩ := ih hp (fun w hw => hs w (eq.mem_iff.1 hw))
    rw [eq.countP_eq] at hle
    exact ⟨q, next, hq, ht, hle⟩
  | @one s a r save _ _ _ _ ih =>
    have ha := hs a List.mem_cons_self
    by_cases hca : IsConst d a
    · have hc_neg : IsConst d (negD d1 a) := by
        have e := negD_and_sub hd hsub a
        rcases negD_const hd hca with h0 | h1
        · exact Or.inl (e.trans (by simpa [negD, Nat.and_assoc, Nat.and_self] using h0))
        · exact Or.inr (e.trans (by simpa [negD, Nat.and_assoc, Nat.and_self] using h1))
      have hs' : ∀ w ∈ negD d1 a :: kept save a r, Avail d bank w := by
        intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact Or.inl hc_neg
        · exact hs w (by rw [mem_kept] at hw; rcases hw with ⟨_, rfl⟩ | hw <;> simp [hw])
      obtain ⟨q, next, hq, ht, hle⟩ := ih hp hs'
      have h1 : isConstB d (negD d1 a) = true := (isConstB_iff _ _).2 hc_neg
      have h2 : isConstB d a = true := (isConstB_iff _ _).2 hca
      have hk := countP_kept_ge (isConstB d) save a r
      simp only [List.countP_cons, h1, h2, ite_true] at hle ⊢
      exact ⟨q, next, hq, ht, by omega⟩
    · have hreach' : NatReach d roots (p + 1) (negD d a :: bank) := Or.inl ⟨bank, a, rfl, hp, ha⟩
      have hneg_av : Avail d (negD d a :: bank) (negD d1 a) :=
        Or.inr ⟨negD d a, List.mem_cons_self, by rw [negD_and_sub hd hsub a]; simp [negD, Nat.and_assoc, Nat.and_self]⟩
      have hs' : ∀ w ∈ negD d1 a :: kept save a r, Avail d (negD d a :: bank) w := by
        intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact hneg_av
        · exact avail_cons _ _ (hs w (by rw [mem_kept] at hw; rcases hw with ⟨_, rfl⟩ | hw <;> simp [hw]))
      obtain ⟨q, next, hq, ht, hle⟩ := ih hreach' hs'
      have h2 : isConstB d a = false := by
        cases h : isConstB d a with | false => rfl | true => exact absurd ((isConstB_iff _ _).1 h) hca
      have hk := countP_kept_ge (isConstB d) save a r
      simp only [List.countP_cons, h2, Bool.false_eq_true, ite_false] at hle ⊢
      exact ⟨q, next, hq, ht, by omega⟩
  | @two s a b r conj ka kb _ _ _ _ ih =>
    have ha := hs a List.mem_cons_self
    have hb := hs b (List.mem_cons_of_mem _ List.mem_cons_self)
    set z1 := if conj then andD d1 a b else orD d1 a b
    set z0 := binD d (!conj) a b
    have hz_eq : z1 &&& d = z0 &&& d := by
      cases conj
      · simp only [z1, z0, Bool.false_eq_true, ite_false, Bool.not_false, binD, ite_true]
        rw [orD_and_sub hsub]; simp [orD, Nat.and_assoc, Nat.and_self]
      · simp only [z1, z0, ite_true, Bool.not_true, Bool.false_eq_true, binD, ite_false]
        rw [andD_and_sub hsub]; simp [andD, Nat.and_assoc, Nat.and_self]
    by_cases hcab : IsConst d a ∨ IsConst d b
    · have hz_av : Avail d bank z1 := by
        apply avail_of_eq hz_eq.symm
        rcases hcab with hca | hcb
        · rcases binD_const_left (!conj) hca with h0 | h1 | he
          · exact Or.inl (Or.inl h0)
          · exact Or.inl (Or.inr h1)
          · exact avail_of_eq he.symm hb
        · dsimp only [z0]; rw [binD_comm]
          rcases binD_const_left (!conj) hcb with h0 | h1 | he
          · exact Or.inl (Or.inl h0)
          · exact Or.inl (Or.inr h1)
          · exact avail_of_eq he.symm ha
      have hs' : ∀ w ∈ z1 :: kept ka a (kept kb b r), Avail d bank w := by
        intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact hz_av
        · rw [mem_kept, mem_kept] at hw
          rcases hw with ⟨_, rfl⟩ | ⟨_, rfl⟩ | hw
          · exact ha
          · exact hb
          · exact hs w (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw))
      obtain ⟨q, next, hq, ht, hle⟩ := ih hp hs'
      have hkr : r.countP (isConstB d) ≤ (kept ka a (kept kb b r)).countP (isConstB d) :=
        le_trans (countP_kept_ge _ kb b r) (countP_kept_ge _ ka a _)
      have hcost : (if isConstB d a = true then 1 else 0) + (if isConstB d b = true then 1 else 0)
          ≤ 1 + (if isConstB d z1 = true then 1 else 0) := by
        rcases hcab with hca | hcb
        · have ha1 : isConstB d a = true := (isConstB_iff _ _).2 hca
          rcases binD_const_left (!conj) hca with h0 | h1 | he
          · have hz1 : isConstB d z1 = true := (isConstB_iff _ _).2 (Or.inl (hz_eq.trans h0))
            simp [ha1, hz1]; split <;> omega
          · have hz1 : isConstB d z1 = true := (isConstB_iff _ _).2 (Or.inr (hz_eq.trans h1))
            simp [ha1, hz1]; split <;> omega
          · have hzb : isConstB d z1 = isConstB d b := by
              simp only [isConstB, hz_eq.trans he]
            simp [ha1, hzb]
        · have hb1 : isConstB d b = true := (isConstB_iff _ _).2 hcb
          have hz_eq' : z1 &&& d = binD d (!conj) b a &&& d := by rw [hz_eq, binD_comm]
          rcases binD_const_left (!conj) hcb with h0 | h1 | he
          · have hz1 : isConstB d z1 = true := (isConstB_iff _ _).2 (Or.inl (hz_eq'.trans h0))
            simp [hb1, hz1]; split <;> omega
          · have hz1 : isConstB d z1 = true := (isConstB_iff _ _).2 (Or.inr (hz_eq'.trans h1))
            simp [hb1, hz1]; split <;> omega
          · have hza : isConstB d z1 = isConstB d a := by
              simp only [isConstB, hz_eq'.trans he]
            simp [hb1, hza]
      simp only [List.countP_cons] at hle ⊢
      exact ⟨q, next, hq, ht, by omega⟩
    · have hna : isConstB d a = false := by
        cases h : isConstB d a with | false => rfl | true => exact absurd (Or.inl ((isConstB_iff _ _).1 h)) hcab
      have hnb : isConstB d b = false := by
        cases h : isConstB d b with | false => rfl | true => exact absurd (Or.inr ((isConstB_iff _ _).1 h)) hcab
      have hreach' : NatReach d roots (p + 1) (z0 :: bank) := Or.inr ⟨bank, a, b, !conj, rfl, hp, ha, hb⟩
      have hz_av : Avail d (z0 :: bank) z1 := Or.inr ⟨z0, List.mem_cons_self, hz_eq.symm⟩
      have hs' : ∀ w ∈ z1 :: kept ka a (kept kb b r), Avail d (z0 :: bank) w := by
        intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact hz_av
        · rw [mem_kept, mem_kept] at hw
          rcases hw with ⟨_, rfl⟩ | ⟨_, rfl⟩ | hw
          · exact avail_cons _ _ ha
          · exact avail_cons _ _ hb
          · exact avail_cons _ _ (hs w (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw)))
      obtain ⟨q, next, hq, ht, hle⟩ := ih hreach' hs'
      have hkr : r.countP (isConstB d) ≤ (kept ka a (kept kb b r)).countP (isConstB d) :=
        le_trans (countP_kept_ge _ kb b r) (countP_kept_ge _ ka a _)
      simp only [List.countP_cons, hna, hnb, Bool.false_eq_true, ite_false] at hle ⊢
      exact ⟨q, next, hq, ht, by omega⟩

-- Backward extraction: NatReach d roots p bank + Avail d bank T -> RunD d (T &&& d) s ws!
theorem mask_idemp (d w : Nat) : (w &&& d) &&& d = w &&& d := by
  simp [Nat.and_assoc, Nat.and_self]

theorem negD_mask (d a : Nat) : negD d (a &&& d) = negD d a := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [negD, Nat.testBit_and, Nat.testBit_xor]
  cases d.testBit i <;> simp

theorem andD_mask (d a b : Nat) : andD d (a &&& d) (b &&& d) = andD d a b := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [andD, Nat.testBit_and]
  cases d.testBit i <;> simp

theorem orD_mask (d a b : Nat) : orD d (a &&& d) (b &&& d) = orD d a b := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [orD, Nat.testBit_and, Nat.testBit_or]
  cases d.testBit i <;> simp

theorem pull_one {d Y k ws} (hd : d &&& mask256 = d) (hnd : ws.Nodup)
    (hprop : ∀ w ∈ ws, w ≠ 0 ∧ w ≠ d) (h : RunD d Y k ws)
    {b : List Nat} {a : Nat} (ha : Avail d b a) (hsub : ∀ w ∈ ws, w ∈ negD d a :: b.map (· &&& d)) :
    ∃ k' ws', k' ≤ k + 1 ∧ ws'.Nodup ∧ (∀ w ∈ ws', w ≠ 0 ∧ w ≠ d) ∧
      (∀ w ∈ ws', w ∈ b.map (· &&& d)) ∧ RunD d Y k' ws' := by
  set z := negD d a
  by_cases hzm : z ∈ ws
  · by_cases hzb : z ∈ b.map (· &&& d)
    · exact ⟨k, ws, by omega, hnd, hprop, fun w hw => by
        rcases List.mem_cons.1 (hsub w hw) with rfl | hm
        · exact hzb
        · exact hm, h⟩
    · have hzp := hprop z hzm
      have ha_nc : ¬ IsConst d a := by
        intro hc
        rcases negD_const hd hc with h0 | h1
        · exact hzp.1 (by simpa [z, negD, Nat.and_assoc, Nat.and_self] using h0)
        · exact hzp.2 (by simpa [z, negD, Nat.and_assoc, Nat.and_self] using h1)
      obtain ⟨v, hv, hve⟩ := ha.resolve_left ha_nc
      set a' := a &&& d
      have ha'_mem : a' ∈ b.map (· &&& d) := List.mem_map.2 ⟨v, hv, hve⟩
      have ha'_prop : a' ≠ 0 ∧ a' ≠ d := ⟨fun e => ha_nc (Or.inl e), fun e => ha_nc (Or.inr e)⟩
      set rest := ws.erase z
      have hrest_nd : rest.Nodup := hnd.erase z
      have hrest_sub : ∀ w ∈ rest, w ∈ b.map (· &&& d) := by
        intro w hw
        have ⟨hne, hm⟩ := hnd.mem_erase_iff.1 hw
        rcases List.mem_cons.1 (hsub w hm) with rfl | hmb
        · exact absurd rfl hne
        · exact hmb
      have hrest_prop : ∀ w ∈ rest, w ≠ 0 ∧ w ≠ d := fun w hw => hprop w (List.mem_of_mem_erase hw)
      have hp1 : ws.Perm (z :: rest) := List.perm_cons_erase hzm
      have ez : negD d a' = z := negD_mask d a
      have h1 : RunD d Y k (negD d a' :: rest) := by
        rw [ez]; exact Run.perm hp1 h
      have hne0 : negD d a' ≠ 0 := ez.symm ▸ hzp.1
      have hned : negD d a' ≠ d := ez.symm ▸ hzp.2
      by_cases ham : a' ∈ rest
      · have hp2 : rest.Perm (a' :: rest.erase a') := List.perm_cons_erase ham
        have h2 : RunD d Y k (negD d a' :: kept true a' (rest.erase a')) :=
          Run.perm (hp2.cons _) h1
        have hnm : negD d a' ∉ (a' :: rest.erase a') := by
          rw [ez, List.mem_cons]; rintro (e | hm)
          · exact hzb (e ▸ ha'_mem)
          · exact hnd.not_mem_erase (List.mem_of_mem_erase hm)
        refine ⟨k + 1, rest, le_rfl, hrest_nd, hrest_prop, hrest_sub, ?_⟩
        exact Run.perm hp2.symm (Run.one true hne0 hned hnm h2)
      · have h2 : RunD d Y k (negD d a' :: kept false a' rest) := h1
        have hnm : negD d a' ∉ (a' :: rest) := by
          rw [ez, List.mem_cons]; rintro (e | hm)
          · exact hzb (e ▸ ha'_mem)
          · exact hnd.not_mem_erase hm
        refine ⟨k + 1, a' :: rest, le_rfl, List.nodup_cons.2 ⟨ham, hrest_nd⟩, ?_, ?_, Run.one false hne0 hned hnm h2⟩
        · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
          · exact ha'_prop
          · exact hrest_prop w hw
        · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
          · exact ha'_mem
          · exact hrest_sub w hw
  · exact ⟨k, ws, by omega, hnd, hprop, fun w hw => by
      rcases List.mem_cons.1 (hsub w hw) with rfl | hm
      · exact absurd hw hzm
      · exact hm, h⟩

theorem pull_two {d Y k ws} (hnd : ws.Nodup)
    (hprop : ∀ w ∈ ws, w ≠ 0 ∧ w ≠ d) (h : RunD d Y k ws)
    {b : List Nat} {a c : Nat} (op : Bool) (ha : Avail d b a) (hc : Avail d b c)
    (hsub : ∀ w ∈ ws, w ∈ binD d op a c :: b.map (· &&& d)) :
    ∃ k' ws', k' ≤ k + 1 ∧ ws'.Nodup ∧ (∀ w ∈ ws', w ≠ 0 ∧ w ≠ d) ∧
      (∀ w ∈ ws', w ∈ b.map (· &&& d)) ∧ RunD d Y k' ws' := by
  set z := binD d op a c
  have hz_mask : z &&& d = z := by cases op <;> simp [z, binD, andD, orD, Nat.and_assoc, Nat.and_self]
  by_cases hzm : z ∈ ws
  · by_cases hzb : z ∈ b.map (· &&& d)
    · exact ⟨k, ws, by omega, hnd, hprop, fun w hw => by
        rcases List.mem_cons.1 (hsub w hw) with rfl | hm
        · exact hzb
        · exact hm, h⟩
    · have hzp := hprop z hzm
      have ha_nc : ¬ IsConst d a := by
        intro hca
        rcases binD_const_left op hca with h0 | h1 | he
        · exact hzp.1 (hz_mask.symm.trans h0)
        · exact hzp.2 (hz_mask.symm.trans h1)
        · rcases hc with hcc | ⟨v, hv, hve⟩
          · rcases hcc with h0 | h1
            · exact hzp.1 (hz_mask.symm.trans (he.trans h0))
            · exact hzp.2 (hz_mask.symm.trans (he.trans h1))
          · exact hzb (List.mem_map.2 ⟨v, hv, hve.trans (he.symm.trans hz_mask)⟩)
      have hc_nc : ¬ IsConst d c := by
        intro hcc
        have hz' : z = binD d op c a := binD_comm d op a c
        rcases binD_const_left op hcc with h0 | h1 | he
        · exact hzp.1 (hz_mask.symm.trans (by rw [hz']; exact h0))
        · exact hzp.2 (hz_mask.symm.trans (by rw [hz']; exact h1))
        · rcases ha with hca | ⟨v, hv, hve⟩
          · exact absurd hca ha_nc
          · have he' : z &&& d = a &&& d := hz'.symm ▸ he
            exact hzb (List.mem_map.2 ⟨v, hv, hve.trans (he'.symm.trans hz_mask)⟩)
      obtain ⟨va, hva, hvae⟩ := ha.resolve_left ha_nc
      obtain ⟨vc, hvc, hvce⟩ := hc.resolve_left hc_nc
      set a' := a &&& d
      set c' := c &&& d
      have ha'_mem : a' ∈ b.map (· &&& d) := List.mem_map.2 ⟨va, hva, hvae⟩
      have hc'_mem : c' ∈ b.map (· &&& d) := List.mem_map.2 ⟨vc, hvc, hvce⟩
      have ha'_prop : a' ≠ 0 ∧ a' ≠ d := ⟨fun e => ha_nc (Or.inl e), fun e => ha_nc (Or.inr e)⟩
      have hc'_prop : c' ≠ 0 ∧ c' ≠ d := ⟨fun e => hc_nc (Or.inl e), fun e => hc_nc (Or.inr e)⟩
      have hne_ac : a' ≠ c' := by
        intro heq
        dsimp only [a', c'] at heq
        have hz_eq : z = a' := by
          cases op
          · simp only [z, binD, Bool.false_eq_true, ite_false]; rw [← andD_mask, ← heq]; simp [andD, a', Nat.and_assoc, Nat.and_self]
          · simp only [z, binD, ite_true]; rw [← orD_mask, ← heq]; simp [orD, a', Nat.and_assoc, Nat.and_self]
        exact hzb (hz_eq ▸ ha'_mem)
      set rest := ws.erase z
      have hrest_nd : rest.Nodup := hnd.erase z
      have hrest_sub : ∀ w ∈ rest, w ∈ b.map (· &&& d) := by
        intro w hw
        have ⟨hne, hm⟩ := hnd.mem_erase_iff.1 hw
        rcases List.mem_cons.1 (hsub w hm) with rfl | hmb
        · exact absurd rfl hne
        · exact hmb
      have hrest_prop : ∀ w ∈ rest, w ≠ 0 ∧ w ≠ d := fun w hw => hprop w (List.mem_of_mem_erase hw)
      have hp1 : ws.Perm (z :: rest) := List.perm_cons_erase hzm
      have ez : (if !op then andD d a' c' else orD d a' c') = z := by
        cases op
        · simp [z, binD, a', c', andD_mask]
        · simp [z, binD, a', c', orD_mask]
      have h1 : RunD d Y k ((if !op then andD d a' c' else orD d a' c') :: rest) := by
        rw [ez]; exact Run.perm hp1 h
      set ka := decide (a' ∈ rest)
      set kb := decide (c' ∈ rest)
      set tail := (rest.erase a').erase c'
      have htail_nd : tail.Nodup := (hrest_nd.erase a').erase c'
      have hna_tail : a' ∉ tail := by
        intro hm; exact hrest_nd.not_mem_erase (List.mem_of_mem_erase hm)
      have hnc_tail : c' ∉ tail := (hrest_nd.erase a').not_mem_erase
      have hna_mid : a' ∉ kept kb c' tail := by
        rw [mem_kept]; rintro (⟨_, h⟩ | h)
        · exact hne_ac h
        · exact hna_tail h
      have hrest_perm : rest.Perm (kept ka a' (kept kb c' tail)) := by
        refine (List.perm_ext_iff_of_nodup hrest_nd (nodup_kept ka a' _ (nodup_kept kb c' _ htail_nd hnc_tail) hna_mid)).2 ?_
        intro x
        rw [mem_kept, mem_kept, (hrest_nd.erase a').mem_erase_iff, hrest_nd.mem_erase_iff]
        by_cases hxa : x = a' <;> by_cases hxc : x = c' <;> by_cases hxr : x ∈ rest <;>
          simp_all [ka, kb]
      have h2 := Run.perm (hrest_perm.cons _) h1
      have hne0 : (if !op then andD d a' c' else orD d a' c') ≠ 0 := ez.symm ▸ hzp.1
      have hned : (if !op then andD d a' c' else orD d a' c') ≠ d := ez.symm ▸ hzp.2
      have hnm : (if !op then andD d a' c' else orD d a' c') ∉ (a' :: c' :: tail) := by
        rw [ez, List.mem_cons, List.mem_cons]; rintro (e | e | hm)
        · exact hzb (e ▸ ha'_mem)
        · exact hzb (e ▸ hc'_mem)
        · exact hnd.not_mem_erase (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
      have h3 : RunD d Y (k + 1) (a' :: c' :: tail) := Run.two (!op) ka kb hne0 hned hnm h2
      have hnd3 : (a' :: c' :: tail).Nodup :=
        List.nodup_cons.2 ⟨by simp [hne_ac, hna_tail], List.nodup_cons.2 ⟨hnc_tail, htail_nd⟩⟩
      refine ⟨k + 1, a' :: c' :: tail, le_rfl, hnd3, ?_, ?_, h3⟩
      · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact ha'_prop
        · rcases List.mem_cons.1 hw with rfl | hw
          · exact hc'_prop
          · exact hrest_prop w (List.mem_of_mem_erase (List.mem_of_mem_erase hw))
      · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact ha'_mem
        · rcases List.mem_cons.1 hw with rfl | hw
          · exact hc'_mem
          · exact hrest_sub w (List.mem_of_mem_erase (List.mem_of_mem_erase hw))
  · exact ⟨k, ws, by omega, hnd, hprop, fun w hw => by
      rcases List.mem_cons.1 (hsub w hw) with rfl | hm
      · exact absurd hw hzm
      · exact hm, h⟩

theorem reach_to_run_aux {d : Nat} {roots : List Nat} {p bank} (hd : d &&& mask256 = d)
    (hr : NatReach d roots p bank) :
    ∀ {Y k ws}, ws.Nodup → (∀ w ∈ ws, w ≠ 0 ∧ w ≠ d) →
      (∀ w ∈ ws, w ∈ bank.map (· &&& d)) → RunD d Y k ws →
      ∃ k' ws', k' ≤ p + k ∧ ws'.Nodup ∧ (∀ w ∈ ws', w ≠ 0 ∧ w ≠ d) ∧
        (∀ w ∈ ws', w ∈ roots.map (· &&& d)) ∧ RunD d Y k' ws' := by
  induction p generalizing bank with
  | zero =>
    intro Y k ws hnd hprop hsub hrun
    subst hr
    exact ⟨k, ws, by omega, hnd, hprop, hsub, hrun⟩
  | succ p ih =>
    intro Y k ws hnd hprop hsub hrun
    rcases hr with ⟨b, a, rfl, hrb, ha⟩ | ⟨b, a, c, op, rfl, hrb, ha, hc⟩
    · have hsub' : ∀ w ∈ ws, w ∈ negD d a :: b.map (· &&& d) := by
        intro w hw; have := hsub w hw; simp only [List.map_cons, negD, Nat.and_assoc, Nat.and_self] at this; exact this
      obtain ⟨k1, ws1, hk1, hnd1, hprop1, hsub1, hrun1⟩ := pull_one hd hnd hprop hrun ha hsub'
      obtain ⟨k2, ws2, hk2, hnd2, hprop2, hsub2, hrun2⟩ := ih hrb hnd1 hprop1 hsub1 hrun1
      exact ⟨k2, ws2, by omega, hnd2, hprop2, hsub2, hrun2⟩
    · have hsub' : ∀ w ∈ ws, w ∈ binD d op a c :: b.map (· &&& d) := by
        intro w hw; have := hsub w hw
        have ez : binD d op a c &&& d = binD d op a c := by cases op <;> simp [binD, andD, orD, Nat.and_assoc, Nat.and_self]
        simpa [List.map_cons, ez] using this
      obtain ⟨k1, ws1, hk1, hnd1, hprop1, hsub1, hrun1⟩ := pull_two hnd hprop hrun op ha hc hsub'
      obtain ⟨k2, ws2, hk2, hnd2, hprop2, hsub2, hrun2⟩ := ih hrb hnd1 hprop1 hsub1 hrun1
      exact ⟨k2, ws2, by omega, hnd2, hprop2, hsub2, hrun2⟩

theorem reach_to_run {d : Nat} {roots : List Nat} {T : Nat} {p bank} (hd : d &&& mask256 = d)
    (hnc : ¬ IsConst d T) (hr : NatReach d roots p bank) (ha : Avail d bank T) :
    ∃ s ws, s ≤ p ∧ ws.Nodup ∧ (∀ w ∈ ws, w ∈ roots.map (· &&& d)) ∧ RunD d (T &&& d) s ws := by
  obtain ⟨v, hv, hve⟩ := ha.resolve_left hnc
  have hprop : ∀ w ∈ [T &&& d], w ≠ 0 ∧ w ≠ d := by
    intro w hw; rw [List.mem_singleton.1 hw]
    exact ⟨fun e => hnc (Or.inl e), fun e => hnc (Or.inr e)⟩
  have hsub : ∀ w ∈ [T &&& d], w ∈ bank.map (· &&& d) := by
    intro w hw; rw [List.mem_singleton.1 hw]; exact List.mem_map.2 ⟨v, hv, hve⟩
  obtain ⟨s, ws, hs, hnd, _, hsub', hrun⟩ := reach_to_run_aux hd hr (List.nodup_singleton _) hprop hsub Run.done
  exact ⟨s, ws, by omega, hnd, hsub', hrun⟩

-- Essential variable lemma + lower_slice + lower_base + lower_iso!
theorem runD_bits {d y s ws} (hd : d &&& mask256 = d) (h : RunD d y s ws) (i j : Nat)
    (hi : d.testBit i = true) (hj : d.testBit j = true)
    (hw : ∀ w ∈ ws, w.testBit i = w.testBit j) : y.testBit i = y.testBit j := by
  have hmi : mask256.testBit i = true := by
    have := congrArg (fun v => v.testBit i) hd; simp [Nat.testBit_and, hi] at this; exact this
  have hmj : mask256.testBit j = true := by
    have := congrArg (fun v => v.testBit j) hd; simp [Nat.testBit_and, hj] at this; exact this
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | one save _ _ _ _ ih =>
    apply ih; have ha := hw _ List.mem_cons_self
    intro w hm; cases save <;> simp only [kept, Bool.false_eq_true, ite_false, ite_true, List.mem_cons] at hm
    · rcases hm with rfl | hr
      · simp [negD, ha, hi, hj, hmi, hmj]
      · exact hw _ (by simp [hr])
    · rcases hm with rfl | rfl | hr
      · simp [negD, ha, hi, hj, hmi, hmj]
      · exact ha
      · exact hw _ (by simp [hr])
  | two conj ka kb _ _ _ _ ih =>
    apply ih; have ha := hw _ List.mem_cons_self; have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hm; cases conj <;> cases ka <;> cases kb <;>
      simp only [kept, Bool.false_eq_true, ite_false, ite_true, List.mem_cons] at hm <;>
      rcases hm with rfl | hr <;>
      first | simp [andD, orD, ha, hb, hi, hj] | exact hw _ (by simp only [List.mem_cons]; tauto)

theorem runD_bits_le {d y s ws} (h : RunD d y s ws) (hl : ws.length = s + 1) (i j : Nat)
    (hi : d.testBit i = true) (hj : d.testBit j = true)
    (hw : ∀ w ∈ ws, w.testBit i ≤ w.testBit j) : y.testBit i ≤ y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (hp.length_eq.trans hl) (fun w h => hw w (hp.mem_iff.1 h))
  | one save _ _ _ h _ => have hh := run_len h; cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb _ _ _ h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    apply ih (by simp [kept]; omega)
    have ha := hw _ List.mem_cons_self; have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hm; simp only [kept, Bool.false_eq_true, ite_false, List.mem_cons] at hm
    rcases hm with rfl | hr
    · cases conj <;> simp only [andD, orD, ite_true, Bool.false_eq_true, ite_false, Nat.testBit_and, Nat.testBit_or, hi, hj, Bool.and_true] <;> grind
    · exact hw _ (by simp [hr])

theorem lower_base {d : Nat} {roots : List Nat} {T : Nat} (h : availB d roots T = false) :
    Lower d roots T 1 := by
  intro p bank hr ha
  cases p with
  | zero =>
    dsimp only [NatReach] at hr; rw [hr] at ha
    have ht := (availB_iff d roots T).2 ha
    rw [h] at ht; contradiction
  | succ p => omega

-- moveBits & lower_iso!
def moveBits (tag d w : Nat) : Nat :=
  ((w &&& tag) <<< d) ||| ((w >>> d) &&& tag) |||
    (w ^^^ ((w &&& tag) ||| (w &&& (tag <<< d))))

theorem moved (tag d i w : Nat) (h : (tag &&& (tag <<< d)) = 0) :
    (moveBits tag d w).testBit i =
      (if tag.testBit i then w.testBit (d + i)
       else if (tag <<< d).testBit i then w.testBit (i - d) else w.testBit i) := by
  have ht := congrArg (fun v : Nat => v.testBit i) h
  simp only [Nat.testBit_and, Nat.zero_testBit] at ht
  simp only [moveBits, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_and,
    Nat.testBit_shiftRight, Nat.testBit_xor] at *
  by_cases hi : d ≤ i <;> simp [hi] at * <;> grind

theorem move_hom (tag d : Nat) (h : (tag &&& (tag <<< d)) = 0) (a b : Nat) :
    moveBits tag d (a &&& b) = (moveBits tag d a &&& moveBits tag d b) ∧
    moveBits tag d (a ||| b) = (moveBits tag d a ||| moveBits tag d b) ∧
    moveBits tag d (a ^^^ b) = (moveBits tag d a ^^^ moveBits tag d b) := by
  refine ⟨?_, ?_, ?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, moved tag d i _ h] <;>
    split_ifs <;> simp

theorem move_zero (tag d : Nat) (h : (tag &&& (tag <<< d)) = 0) : moveBits tag d 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro i; rw [moved tag d i 0 h]; split_ifs <;> simp

def applyMoves (ms : List (Nat × Nat)) (w : Nat) : Nat :=
  ms.foldl (fun acc p => moveBits p.1 p.2 acc) w

def moveOK256 (p : Nat × Nat) : Bool :=
  (p.1 &&& (p.1 <<< p.2) == 0) && (moveBits p.1 p.2 mask256 == mask256)

theorem applyMoves_hom (ms : List (Nat × Nat)) (hok : ms.all moveOK256 = true) :
    (∀ a b, applyMoves ms (a &&& b) = applyMoves ms a &&& applyMoves ms b) ∧
    (∀ a b, applyMoves ms (a ||| b) = applyMoves ms a ||| applyMoves ms b) ∧
    (∀ a b, applyMoves ms (a ^^^ b) = applyMoves ms a ^^^ applyMoves ms b) ∧
    applyMoves ms 0 = 0 ∧ applyMoves ms mask256 = mask256 := by
  induction ms with
  | nil => exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩
  | cons p ps ih =>
    simp only [List.all_cons, Bool.and_eq_true, moveOK256, beq_iff_eq] at hok
    obtain ⟨⟨hz, hm⟩, hps⟩ := hok
    obtain ⟨hand, hor, hxor, h0, h256⟩ := ih hps
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro a b; simp only [applyMoves, List.foldl_cons, (move_hom p.1 p.2 hz a b).1]; exact hand _ _
    · intro a b; simp only [applyMoves, List.foldl_cons, (move_hom p.1 p.2 hz a b).2.1]; exact hor _ _
    · intro a b; simp only [applyMoves, List.foldl_cons, (move_hom p.1 p.2 hz a b).2.2]; exact hxor _ _
    · simp only [applyMoves, List.foldl_cons, move_zero p.1 p.2 hz]; exact h0
    · simp only [applyMoves, List.foldl_cons, hm]; exact h256

theorem move_invol (tag d w : Nat) (h : (tag &&& (tag <<< d)) = 0) :
    moveBits tag d (moveBits tag d w) = w := by
  apply Nat.eq_of_testBit_eq; intro i
  have ht := congrArg (fun v : Nat => v.testBit i) h
  simp only [Nat.testBit_and, Nat.zero_testBit] at ht
  rw [moved tag d i _ h]
  by_cases h1 : tag.testBit i = true
  · simp only [h1, ite_true, moved tag d (d + i) w h]
    have h2 : tag.testBit (d + i) = false := by
      have htd := congrArg (fun v : Nat => v.testBit (d + i)) h
      simp only [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.zero_testBit] at htd
      have hge : d ≤ d + i := Nat.le_add_right d i
      have hsub : d + i - d = i := Nat.add_sub_cancel_left d i
      simp [hge, hsub, h1] at htd; exact htd
    have h3 : (tag <<< d).testBit (d + i) = true := by
      simp [Nat.testBit_shiftLeft, Nat.le_add_right, Nat.add_sub_cancel_left, h1]
    simp [h2, h3, Nat.add_sub_cancel_left]
  · simp only [h1, ite_false]
    by_cases h2 : (tag <<< d).testBit i = true
    · simp only [h2, ite_true, moved tag d (i - d) w h]
      rw [Nat.testBit_shiftLeft] at h2
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
      simp [h2.2, Nat.add_sub_of_le h2.1]
    · simp [h1, h2, moved tag d i w h]

theorem applyMoves_inj (ms : List (Nat × Nat)) (hok : ms.all moveOK256 = true) :
    Function.Injective (applyMoves ms) := by
  induction ms with
  | nil => intro a b h; exact h
  | cons p ps ih =>
    simp only [List.all_cons, Bool.and_eq_true, moveOK256, beq_iff_eq] at hok
    intro a b h
    simp only [applyMoves, List.foldl_cons] at h
    have h1 := ih hok.2 h
    have := congrArg (moveBits p.1 p.2) h1
    rwa [move_invol p.1 p.2 a hok.1.1, move_invol p.1 p.2 b hok.1.1] at this

theorem applyMoves_runD {d Y s} (ms : List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    (hd : applyMoves ms d = d) (hY : applyMoves ms Y = Y) {ws} (h : RunD d Y s ws) :
    RunD d Y s (ws.map (applyMoves ms)) := by
  obtain ⟨hand, hor, hxor, h0, h256⟩ := applyMoves_hom ms hok
  have hinj := applyMoves_inj ms hok
  have hneg : ∀ a, applyMoves ms (negD d a) = negD d (applyMoves ms a) := fun a => by
    simp only [negD, hand, hxor, h256, hd]
  have hand' : ∀ a b, applyMoves ms (andD d a b) = andD d (applyMoves ms a) (applyMoves ms b) := fun a b => by
    simp only [andD, hand, hd]
  have hor' : ∀ a b, applyMoves ms (orD d a b) = orD d (applyMoves ms a) (applyMoves ms b) := fun a b => by
    simp only [orD, hand, hor, hd]
  rw [← hY]
  induction h using Run.fold with
  | done => exact Run.done
  | perm hp _ ih => exact Run.perm (hp.map _) ih
  | @one s a r save hne0 hned hnm _ ih =>
    have e1 : (negD d a :: kept save a r).map (applyMoves ms) =
        negD d (applyMoves ms a) :: kept save (applyMoves ms a) (r.map (applyMoves ms)) := by
      simp [kept_map, hneg]
    rw [e1] at ih
    refine Run.one save ?_ ?_ ?_ ih
    · intro e; rw [← hneg] at e; exact hne0 (hinj (e.trans h0.symm))
    · intro e; rw [← hneg] at e; exact hned (hinj (e.trans hd.symm))
    · rw [← hneg, ← List.map_cons, List.mem_map]; rintro ⟨x, hx, he⟩; exact hnm (hinj he ▸ hx)
  | @two s a b r conj ka kb hne0 hned hnm _ ih =>
    have eop : applyMoves ms (if conj then andD d a b else orD d a b) =
        (if conj then andD d (applyMoves ms a) (applyMoves ms b) else orD d (applyMoves ms a) (applyMoves ms b)) := by
      cases conj <;> simp [hand', hor']
    have e1 : ((if conj then andD d a b else orD d a b) :: kept ka a (kept kb b r)).map (applyMoves ms) =
        (if conj then andD d (applyMoves ms a) (applyMoves ms b) else orD d (applyMoves ms a) (applyMoves ms b)) ::
          kept ka (applyMoves ms a) (kept kb (applyMoves ms b) (r.map (applyMoves ms))) := by
      simp [kept_map, eop]
    rw [e1] at ih
    refine Run.two conj ka kb ?_ ?_ ?_ ih
    · intro e; rw [← eop] at e; exact hne0 (hinj (e.trans h0.symm))
    · intro e; rw [← eop] at e; exact hned (hinj (e.trans hd.symm))
    · rw [← eop, ← List.map_cons, ← List.map_cons, List.mem_map]; rintro ⟨x, hx, he⟩; exact hnm (hinj he ▸ hx)

theorem reach_map_moves (ms : List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    {d1 d2 : Nat} (hd : applyMoves ms d2 = d1)
    {roots1 roots2 : List Nat} (hroots : ∀ r ∈ roots2, Avail d1 roots1 (applyMoves ms r)) :
    ∀ {p bank}, NatReach d2 roots2 p bank →
      ∃ bank', NatReach d1 roots1 p bank' ∧ ∀ v ∈ bank, Avail d1 bank' (applyMoves ms v) := by
  obtain ⟨hand, hor, hxor, h0, h256⟩ := applyMoves_hom ms hok
  have hav : ∀ {b b' w}, (∀ v ∈ b, Avail d1 b' (applyMoves ms v)) →
      Avail d2 b w → Avail d1 b' (applyMoves ms w) := by
    intro b b' w hbb hw
    rcases hw with (hz | h1) | ⟨v, hv, he⟩
    · exact Or.inl (Or.inl (by rw [← hd, ← hand, hz, h0]))
    · exact Or.inl (Or.inr (by rw [← hd, ← hand, h1]))
    · have hve : applyMoves ms v &&& d1 = applyMoves ms w &&& d1 := by rw [← hd, ← hand, ← hand, he]
      exact avail_of_eq hve (hbb v hv)
  intro p
  induction p with
  | zero =>
    intro bank hr; subst hr
    exact ⟨roots1, rfl, hroots⟩
  | succ p ih =>
    intro bank hr
    rcases hr with ⟨b, a, rfl, hrb, ha⟩ | ⟨b, a, c, op, rfl, hrb, ha, hc⟩
    · obtain ⟨b', hrb', hbb⟩ := ih hrb
      have ha' := hav hbb ha
      refine ⟨negD d1 (applyMoves ms a) :: b', Or.inl ⟨b', applyMoves ms a, rfl, hrb', ha'⟩, ?_⟩
      intro v hv; rcases List.mem_cons.1 hv with rfl | hv
      · exact Or.inr ⟨negD d1 (applyMoves ms a), List.mem_cons_self, by simp only [negD, hand, hxor, h256, hd]⟩
      · exact avail_cons _ _ (hbb v hv)
    · obtain ⟨b', hrb', hbb⟩ := ih hrb
      have ha' := hav hbb ha; have hc' := hav hbb hc
      refine ⟨binD d1 op (applyMoves ms a) (applyMoves ms c) :: b',
        Or.inr ⟨b', applyMoves ms a, applyMoves ms c, op, rfl, hrb', ha', hc'⟩, ?_⟩
      intro v hv; rcases List.mem_cons.1 hv with rfl | hv
      · exact Or.inr ⟨binD d1 op (applyMoves ms a) (applyMoves ms c), List.mem_cons_self, by
          cases op <;> simp only [binD, andD, orD, hand, hor, hd, ite_true, ite_false, Bool.false_eq_true]⟩
      · exact avail_cons _ _ (hbb v hv)

theorem lower_iso {d1 d2 T1 T2 L : Nat} {roots1 roots2 : List Nat}
    (ms : List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    (hd : applyMoves ms d2 = d1) (hT : applyMoves ms T2 = T1)
    (hroots : roots2.all (fun r => availB d1 roots1 (applyMoves ms r)) = true)
    (h1 : Lower d1 roots1 T1 L) : Lower d2 roots2 T2 L := by
  obtain ⟨hand, _, _, h0, _⟩ := applyMoves_hom ms hok
  have hr : ∀ r ∈ roots2, Avail d1 roots1 (applyMoves ms r) := fun r hr =>
    (availB_iff _ _ _).1 (List.all_eq_true.1 hroots r hr)
  intro p bank hreach ha
  obtain ⟨bank', hrb', hbb⟩ := reach_map_moves ms hok hd hr hreach
  apply h1 p bank' hrb'
  rcases ha with (hz | ho) | ⟨v, hv, he⟩
  · exact Or.inl (Or.inl (by rw [← hT, ← hd, ← hand, hz, h0]))
  · exact Or.inl (Or.inr (by rw [← hT, ← hd, ← hand, ho]))
  · have hve : applyMoves ms v &&& d1 = T1 &&& d1 := by rw [← hT, ← hd, ← hand, ← hand, he]
    exact avail_of_eq hve (hbb v hv)

-- lower_slice!
def pairOK (d T : Nat) (p : Nat × Nat) : Bool :=
  d.testBit p.1 && d.testBit p.2 && (T.testBit p.1 != T.testBit p.2)

def essOK (d T : Nat) (roots : List Nat) (a : Nat) (p : Nat × Nat) : Bool :=
  pairOK d T p && roots.all (fun v => (v == a) || (v.testBit p.1 == v.testBit p.2))

theorem countP_ge_sublist (p : Nat → Bool) {xs ys : List Nat}
    (hnd : xs.Nodup) (hsub : ∀ a ∈ xs, a ∈ ys) (hall : ∀ a ∈ xs, p a = true) :
    xs.length ≤ ys.countP p := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    have ⟨hna, hnd'⟩ := List.nodup_cons.1 hnd
    have ham : a ∈ ys := hsub a List.mem_cons_self
    have hperm : ys.Perm (a :: ys.erase a) := List.perm_cons_erase ham
    rw [hperm.countP_eq, List.countP_cons, hall a List.mem_cons_self]
    have ih' := ih hnd' (fun x hx => by
      have hne : x ≠ a := fun e => hna (e ▸ hx)
      exact (List.mem_erase_of_ne hne).2 (hsub x (List.mem_cons_of_mem _ hx)))
      (fun x hx => hall x (List.mem_cons_of_mem _ hx))
    simp only [ite_true, List.length_cons]
    omega

theorem lower_slice {d dSub T TSub L : Nat} {roots rootsSub : List Nat}
    (hd : d &&& mask256 = d) (hdSub : dSub &&& mask256 = dSub) (hsub : dSub &&& d = dSub)
    (hT : T &&& dSub = TSub &&& dSub)
    (hnc : isConstB d T = false) (hncSub : isConstB dSub TSub = false)
    (hcov : roots.all (availB dSub rootsSub) = true)
    (singles : List (Nat × Nat × Nat))
    (hs_nd : (singles.map Prod.fst).Nodup)
    (hs_ok : singles.all (fun e => isConstB dSub e.1 && essOK d (T &&& d) (roots.map (· &&& d)) e.1 e.2) = true)
    (hprior : Lower dSub rootsSub TSub L) :
    Lower d roots T (L + singles.length) := by
  have hnc' : ¬ IsConst d T := fun h => by rw [(isConstB_iff _ _).2 h] at hnc; contradiction
  have hncSub' : ¬ IsConst dSub (T &&& d) := by
    intro h
    have e : (T &&& d) &&& dSub = TSub &&& dSub := by
      rw [Nat.and_assoc, Nat.and_comm d dSub, hsub, hT]
    rcases h with h0 | h1
    · exact absurd ((isConstB_iff _ _).2 (Or.inl (e.symm.trans h0))) (by simp [hncSub])
    · exact absurd ((isConstB_iff _ _).2 (Or.inr (e.symm.trans h1))) (by simp [hncSub])
  intro p bank hr ha
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run hd hnc' hr ha
  have hws_av : ∀ w ∈ ws, Avail dSub rootsSub w := by
    intro w hw
    obtain ⟨r, hr_m, rfl⟩ := List.mem_map.1 (hws_sub w hw)
    have hav := (availB_iff _ _ _).1 (List.all_eq_true.1 hcov r hr_m)
    exact avail_of_eq (by rw [Nat.and_assoc, Nat.and_comm d dSub, hsub]) hav
  obtain ⟨q, next, hq, ht, hle⟩ := contraction hdSub hsub hncSub' hrun (p := 0) (bank := rootsSub) rfl hws_av
  have hTSub_av : Avail dSub next TSub := avail_of_eq (by
    rw [Nat.and_assoc, Nat.and_comm d dSub, hsub, hT]) ht
  have hL : L ≤ q := hprior q next hq hTSub_av
  have hsin_mem : ∀ a ∈ singles.map Prod.fst, a ∈ ws := by
    intro a ha
    obtain ⟨⟨a', r1, r2⟩, hm, rfl⟩ := List.mem_map.1 ha
    have hok := List.all_eq_true.1 hs_ok (a', r1, r2) hm
    simp only [Bool.and_eq_true, essOK, pairOK, bne_iff_ne, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at hok
    obtain ⟨_, ⟨⟨hr1, hr2⟩, hdiff⟩, hiso⟩ := hok
    by_contra hnot
    apply hdiff
    apply runD_bits hd hrun r1 r2 hr1 hr2
    intro w hw
    rcases hiso w (hws_sub w hw) with rfl | heq
    · exact absurd hw hnot
    · exact heq
  have hsin_const : ∀ a ∈ singles.map Prod.fst, isConstB dSub a = true := by
    intro a ha
    obtain ⟨⟨a', r1, r2⟩, hm, rfl⟩ := List.mem_map.1 ha
    have hok := List.all_eq_true.1 hs_ok _ hm
    simp only [Bool.and_eq_true] at hok
    exact hok.1
  have hcnt := countP_ge_sublist (isConstB dSub) hs_nd hsin_mem hsin_const
  simp only [List.length_map] at hcnt
  omega

-- poolCut (compact 52-bit hint!) + covers + eval6 + bar!
def runChoices (d : Nat) (pool : List Nat) : Nat → Nat → Option (List Nat)
  | 0, _ => some pool
  | p + 1, bits =>
    let code := bits &&& 1023
    let op := code &&& 3
    let ia := (code >>> 2) &&& 15
    let ib := (code >>> 6) &&& 15
    if ia < pool.length && (op == 2 || ib < pool.length) then
      let a := pool.getD ia 0
      let b := pool.getD ib 0
      let w := if op == 2 then negD d a else binD d (op == 1) a b
      runChoices d (pool ++ [w]) p (bits >>> 10)
    else none

theorem getD_mem {xs : List Nat} {i : Nat} (hi : i < xs.length) : xs.getD i 0 ∈ xs := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact List.getElem_mem hi

theorem runChoices_sound {d : Nat} {roots : List Nat} :
    ∀ (p bits q : Nat) (bank pool result : List Nat),
      NatReach d roots q bank →
      (∀ v ∈ pool, Avail d bank v) →
      runChoices d pool p bits = some result →
      ∃ bank', NatReach d roots (q + p) bank' ∧ ∀ v ∈ result, Avail d bank' v
  | 0, _, q, bank, pool, result, hr, hsup, hok => by
    simp only [runChoices, Option.some.injEq] at hok; subst hok; exact ⟨bank, hr, hsup⟩
  | p + 1, bits, q, bank, pool, result, hr, hsup, hok => by
    simp only [runChoices] at hok
    split at hok
    · rename_i hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at hcond
      obtain ⟨hia, hopb⟩ := hcond
      set code := bits &&& 1023
      set op := code &&& 3
      set ia := (code >>> 2) &&& 15
      set ib := (code >>> 6) &&& 15
      set a := pool.getD ia 0
      set b := pool.getD ib 0
      set w := if op == 2 then negD d a else binD d (op == 1) a b
      have ha : Avail d bank a := hsup a (getD_mem hia)
      have hr1 : NatReach d roots (q + 1) (w :: bank) := by
        by_cases h2 : op = 2
        · simp only [w, h2, beq_self_eq_true, ite_true]
          exact Or.inl ⟨bank, a, rfl, hr, ha⟩
        · have hib : ib < pool.length := hopb.resolve_left h2
          have hb : Avail d bank b := hsup b (getD_mem hib)
          simp only [w, h2, beq_iff_eq, ite_false]
          exact Or.inr ⟨bank, a, b, (op == 1), rfl, hr, ha, hb⟩
      have hsup1 : ∀ v ∈ pool ++ [w], Avail d (w :: bank) v := by
        intro v hv; rcases List.mem_append.1 hv with hv | hv
        · exact avail_cons _ _ (hsup v hv)
        · rw [List.mem_singleton.1 hv]; exact Or.inr ⟨w, List.mem_cons_self, rfl⟩
      obtain ⟨bank', hrb', hsb'⟩ := runChoices_sound p (bits >>> 10) (q + 1) (w :: bank) (pool ++ [w]) result hr1 hsup1 hok
      exact ⟨bank', by simpa [Nat.add_assoc, Nat.add_comm 1] using hrb', hsb'⟩
    · contradiction

def checkCutEntry (dSub : Nat) (rootsSub : List Nat) (LSub s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  let p := (hint >>> 8) &&& 15
  decide (s + p < LSub + ws.countP (isConstB dSub)) &&
  match runChoices dSub rootsSub p (hint >>> 12) with
  | none => false
  | some pool => ws.all (availB dSub pool)

theorem checkCutEntry_sound {d dSub T TSub LSub s : Nat} {rootsSub ws : List Nat}
    (hdSub : dSub &&& mask256 = dSub) (hsub : dSub &&& d = dSub)
    (hT : T &&& dSub = TSub &&& dSub) (hncSub : isConstB dSub TSub = false)
    (hprior : Lower dSub rootsSub TSub LSub) (hint : Nat)
    (hchk : checkCutEntry dSub rootsSub LSub s ws hint = true) :
    ¬ RunD d (T &&& d) s ws := by
  intro hrun
  simp only [checkCutEntry, Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨hineq, hmatch⟩ := hchk
  cases hrc : runChoices dSub rootsSub ((hint >>> 8) &&& 15) (hint >>> 12) with
  | none => rw [hrc] at hmatch; contradiction
  | some pool =>
    rw [hrc] at hmatch
    have hsup0 : ∀ v ∈ rootsSub, Avail dSub rootsSub v := fun v hv => Or.inr ⟨v, hv, rfl⟩
    obtain ⟨bank, hrb, hsb⟩ := runChoices_sound _ _ 0 rootsSub rootsSub pool rfl hsup0 hrc
    simp only [Nat.zero_add] at hrb
    have hws_av : ∀ w ∈ ws, Avail dSub bank w := by
      intro w hw
      have hav := (availB_iff _ _ _).1 (List.all_eq_true.1 hmatch w hw)
      rcases hav with hc | ⟨v, hv, he⟩
      · exact Or.inl hc
      · exact avail_of_eq he (hsb v hv)
    have hnc' : ¬ IsConst dSub (T &&& d) := by
      intro h; have e : (T &&& d) &&& dSub = TSub &&& dSub := by rw [Nat.and_assoc, Nat.and_comm d dSub, hsub, hT]
      rcases h with h0 | h1
      · exact absurd ((isConstB_iff _ _).2 (Or.inl (e.symm.trans h0))) (by simp [hncSub])
      · exact absurd ((isConstB_iff _ _).2 (Or.inr (e.symm.trans h1))) (by simp [hncSub])
    obtain ⟨q, next, hq, ht, hle⟩ := contraction hdSub hsub hnc' hrun hrb hws_av
    have hL := hprior q next hq (avail_of_eq (by rw [Nat.and_assoc, Nat.and_comm d dSub, hsub, hT]) ht)
    omega

-- covers, eval6, hw256, hk, bsr, bar, bar_all!
def coversP (pairs : List (Nat × Nat)) (s : Nat) (ws : List Nat) : Bool :=
  if ws.length == s + 1 then
    pairs.all (fun p => ws.any (fun w => !w.testBit p.1 && w.testBit p.2))
  else
    pairs.all (fun p => ws.any (fun w => w.testBit p.1 != w.testBit p.2))

theorem coversP_ok {d T s : Nat} (hd : d &&& mask256 = d)
    (pairs : List (Nat × Nat))
    (hpairs : pairs.all (fun p => d.testBit p.1 && d.testBit p.2 && !(T &&& d).testBit p.1 && (T &&& d).testBit p.2) = true)
    {ws : List Nat} (h : RunD d (T &&& d) s ws) : coversP pairs s ws = true := by
  unfold coversP
  by_cases hl : ws.length = s + 1
  · simp only [hl, beq_self_eq_true, ite_true, List.all_eq_true, List.any_eq_true]
    intro ⟨u, v⟩ hm
    have hp := List.all_eq_true.1 hpairs (u, v) hm
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
    by_contra! hall
    have hle := runD_bits_le h hl v u hp.1.1.2 hp.1.1.1 (fun w hw => by
      have hbad := hall w hw
      cases hu : w.testBit u <;> cases hv : w.testBit v <;> simp_all)
    rw [hp.1.2, hp.2] at hle; contradiction
  · simp only [hl, beq_iff_eq, ite_false, List.all_eq_true, List.any_eq_true, bne_iff_ne]
    intro ⟨u, v⟩ hm
    have hp := List.all_eq_true.1 hpairs (u, v) hm
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
    by_contra! hall
    have heq := runD_bits hd h u v hp.1.1.1 hp.1.1.2 hall
    rw [hp.1.2, hp.2] at heq; contradiction

def unorientedCov (pairs : List (Nat × Nat)) (ws : List Nat) : Bool :=
  pairs.all (fun p => ws.any (fun w => w.testBit p.1 != w.testBit p.2))

theorem unorientedCov_ok {d T s : Nat} (hd : d &&& mask256 = d)
    (pairs : List (Nat × Nat))
    (hpairs : pairs.all (fun p => d.testBit p.1 && d.testBit p.2 && !(T &&& d).testBit p.1 && (T &&& d).testBit p.2) = true)
    {ws : List Nat} (h : RunD d (T &&& d) s ws) : unorientedCov pairs ws = true := by
  simp only [unorientedCov, List.all_eq_true, List.any_eq_true, bne_iff_ne]
  intro ⟨u, v⟩ hm
  have hp := List.all_eq_true.1 hpairs (u, v) hm
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
  by_contra! hall
  have heq := runD_bits hd h u v hp.1.1.1 hp.1.1.2 hall
  rw [hp.1.2, hp.2] at heq; contradiction

-- Fast bitmask-decorated covers (150x faster than per-pair testBit!)
def maskP (m : Nat) : Nat := 2 ^ m - 1

def projBit (rs : List Nat) (w : Nat) : Nat :=
  rs.foldr (fun r acc => (acc <<< 1) ||| (if w.testBit r then 1 else 0)) 0

theorem projBit_testBit (rs : List Nat) (w : Nat) (i : Nat) :
    (projBit rs w).testBit i = if h : i < rs.length then w.testBit rs[i] else false := by
  induction rs generalizing i with
  | nil => simp [projBit]
  | cons r rs ih =>
    cases i with
    | zero =>
      simp only [projBit, List.foldr_cons, Nat.testBit_or, Nat.testBit_shiftLeft,
        Nat.not_le.2 Nat.zero_lt_one, decide_false, Bool.false_and, Bool.false_or,
        List.length_cons, Nat.zero_lt_succ, dite_true, List.getElem_cons_zero]
      cases w.testBit r <;> simp
    | succ i =>
      simp only [projBit, List.foldr_cons, Nat.testBit_or, Nat.testBit_shiftLeft,
        Nat.succ_le_succ (Nat.zero_le i), decide_true, Bool.true_and, Nat.add_sub_cancel,
        List.length_cons, Nat.succ_lt_succ_iff, List.getElem_cons_succ]
      have h1 : (if w.testBit r = true then 1 else 0).testBit (i + 1) = false := by
        cases w.testBit r <;> simp [Nat.testBit_succ]
      rw [h1, Bool.or_false]; exact ih i

theorem projBit_negD {dm : Nat} (hd : dm &&& mask256 = dm) {rs : List Nat}
    (hrs : ∀ r ∈ rs, dm.testBit r = true) (w : Nat) :
    projBit rs (negD dm w) = projBit rs w ^^^ maskP rs.length := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [projBit_testBit, Nat.testBit_xor, projBit_testBit, maskP, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < rs.length
  · have hdr := hrs rs[i] (List.getElem_mem hi)
    have hmr : mask256.testBit rs[i] = true := by
      have := congrArg (fun v => v.testBit rs[i]) hd; simp [Nat.testBit_and, hdr] at this; exact this
    simp [hi, negD, hdr, hmr]
  · simp [hi]

theorem projBit_andD {dm : Nat} {rs : List Nat} (hrs : ∀ r ∈ rs, dm.testBit r = true) (a b : Nat) :
    projBit rs (andD dm a b) = projBit rs a &&& projBit rs b := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [projBit_testBit, Nat.testBit_and, projBit_testBit, projBit_testBit]
  by_cases hi : i < rs.length
  · simp [hi, andD, hrs rs[i] (List.getElem_mem hi)]
  · simp [hi]

theorem projBit_orD {dm : Nat} {rs : List Nat} (hrs : ∀ r ∈ rs, dm.testBit r = true) (a b : Nat) :
    projBit rs (orD dm a b) = projBit rs a ||| projBit rs b := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [projBit_testBit, Nat.testBit_or, projBit_testBit, projBit_testBit]
  by_cases hi : i < rs.length
  · simp [hi, orD, hrs rs[i] (List.getElem_mem hi)]
  · simp [hi]

theorem foldl_or_testBit {α : Type} (g : α → Nat) (xs : List α) (acc i : Nat) :
    (xs.foldl (fun a x => a ||| g x) acc).testBit i = (acc.testBit i || xs.any (fun x => (g x).testBit i)) := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, Nat.testBit_or, List.any_cons, Bool.or_assoc]

def coversD (mp s : Nat) (dws : List (Nat × Nat × Nat)) : Bool :=
  if dws.length == s + 1 then
    dws.foldl (fun acc d => acc ||| ((d.2.1 ^^^ mp) &&& d.2.2)) 0 == mp
  else
    dws.foldl (fun acc d => acc ||| (d.2.1 ^^^ d.2.2)) 0 == mp

theorem coversD_eq (pairs : List (Nat × Nat)) (s : Nat) (ws : List Nat) :
    coversD (maskP pairs.length) s (ws.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w))) =
      coversP pairs s ws := by
  set r1s := pairs.map Prod.fst
  set r2s := pairs.map Prod.snd
  set mp := maskP pairs.length
  have hr1 : r1s.length = pairs.length := List.length_map _
  have hr2 : r2s.length = pairs.length := List.length_map _
  unfold coversD coversP
  simp only [List.length_map]
  split
  · apply Bool.eq_iff_iff.2
    rw [beq_iff_eq, List.all_eq_true]
    constructor
    · intro heq pr hpr
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hpr
      have hb := congrArg (fun v => v.testBit i) heq
      rw [foldl_or_testBit, Nat.zero_testBit, Bool.false_or, List.any_map] at hb
      simp only [mp, maskP, Nat.testBit_two_pow_sub_one, hi, decide_true] at hb
      obtain ⟨w, hw, hwt⟩ := List.any_eq_true.1 hb
      simp only [Function.comp_def, Nat.testBit_and, Nat.testBit_xor, projBit_testBit, hr1, hr2, hi, dite_true,
        Nat.testBit_two_pow_sub_one, decide_true, Bool.xor_true] at hwt
      exact List.any_eq_true.2 ⟨w, hw, by simpa [r1s, r2s] using hwt⟩
    · intro hall
      apply Nat.eq_of_testBit_eq; intro i
      rw [foldl_or_testBit, Nat.zero_testBit, Bool.false_or, List.any_map]
      simp only [mp, maskP, Nat.testBit_two_pow_sub_one]
      by_cases hi : i < pairs.length
      · simp only [hi, decide_true]
        obtain ⟨w, hw, hwt⟩ := List.any_eq_true.1 (hall pairs[i] (List.getElem_mem hi))
        exact List.any_eq_true.2 ⟨w, hw, by
          simp only [Function.comp_def, Nat.testBit_and, Nat.testBit_xor, projBit_testBit, hr1, hr2, hi, dite_true,
            Nat.testBit_two_pow_sub_one, decide_true, Bool.xor_true, r1s, r2s, List.getElem_map]
          exact hwt⟩
      · simp only [hi, decide_false, List.any_eq_false]
        intro w _
        simp only [Function.comp_def, Nat.testBit_and, Nat.testBit_xor, projBit_testBit, hr1, hr2, hi, dite_false,
          Nat.testBit_two_pow_sub_one, decide_false, Bool.xor_false, Bool.and_false, not_false_eq_true, Bool.false_eq_true]
  · apply Bool.eq_iff_iff.2
    rw [beq_iff_eq, List.all_eq_true]
    constructor
    · intro heq pr hpr
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hpr
      have hb := congrArg (fun v => v.testBit i) heq
      rw [foldl_or_testBit, Nat.zero_testBit, Bool.false_or, List.any_map] at hb
      simp only [mp, maskP, Nat.testBit_two_pow_sub_one, hi, decide_true] at hb
      obtain ⟨w, hw, hwt⟩ := List.any_eq_true.1 hb
      simp only [Function.comp_def, Nat.testBit_xor, projBit_testBit, hr1, hr2, hi, dite_true] at hwt
      exact List.any_eq_true.2 ⟨w, hw, by simpa [r1s, r2s, bne] using hwt⟩
    · intro hall
      apply Nat.eq_of_testBit_eq; intro i
      rw [foldl_or_testBit, Nat.zero_testBit, Bool.false_or, List.any_map]
      simp only [mp, maskP, Nat.testBit_two_pow_sub_one]
      by_cases hi : i < pairs.length
      · simp only [hi, decide_true]
        obtain ⟨w, hw, hwt⟩ := List.any_eq_true.1 (hall pairs[i] (List.getElem_mem hi))
        exact List.any_eq_true.2 ⟨w, hw, by
          simp only [Function.comp_def, Nat.testBit_xor, projBit_testBit, hr1, hr2, hi, dite_true, r1s, r2s, List.getElem_map]
          simpa [bne] using hwt⟩
      · simp only [hi, decide_false, List.any_eq_false]
        intro w _
        simp only [Function.comp_def, Nat.testBit_xor, projBit_testBit, hr1, hr2, hi, dite_false,
          Bool.xor_false, Bool.false_eq_true, not_false_eq_true]

theorem erase_map_inj {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (f : α → β) (hinj : Function.Injective f) (xs : List α) (a : α) :
    (xs.map f).erase (f a) = (xs.erase a).map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.erase_cons]
    by_cases h : x = a
    · subst h; simp
    · have hf : (f x == f a) = false := beq_false_of_ne (fun e => h (hinj e))
      have hx : (x == a) = false := beq_false_of_ne h
      simp [hf, hx, ih]

def value6 (a b c d e f : Bool) : Nat :=
  let x := b.toNat + c.toNat
  let y := (!e).toNat + (!f).toNat
  if a then (if d then y else max x (max y (x + y - 1))) else (if d then 0 else x)

theorem value6_and : ∀ a b c d e f g h i j l m : Bool,
    value6 (a && g) (b && h) (c && i) (d && j) (e && l) (f && m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem value6_or : ∀ a b c d e f g h i j l m : Bool,
    value6 (a || g) (b || h) (c || i) (d || j) (e || l) (f || m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem score_bound {d y s ws} (h : RunD d y s ws) (hl : ws.length = s + 1)
    (v : Nat → Nat) (hand : ∀ a b, v (andD d a b) ≤ v a + v b)
    (hor : ∀ a b, v (orD d a b) ≤ v a + v b) : v y ≤ (ws.map v).sum := by
  induction h using Run.fold with
  | done => simp
  | perm p _ ih => rw [← (p.map v).sum_eq]; exact ih (p.length_eq.trans hl)
  | one save _ _ _ h _ => have hh := run_len h; cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb _ _ _ h ih =>
    have hh := run_len h; cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    have ih' := ih (by simp [kept]; omega)
    cases conj <;> simp [kept] at ih' ⊢ <;>
      first | grw [← Nat.add_assoc, ← hand]; exact ih' | grw [← Nat.add_assoc, ← hor]; exact ih'

def eval6 (a b c d e f v : Nat) := value6 (v.testBit a) (v.testBit b) (v.testBit c)
    (v.testBit d) (v.testBit e) (v.testBit f)

theorem eval6_bound {dm y s ws} (h : RunD dm y s ws) (hl : ws.length = s + 1)
    (a b c d e f : Nat)
    (ha : dm.testBit a = true) (hb : dm.testBit b = true) (hc : dm.testBit c = true)
    (hd : dm.testBit d = true) (he : dm.testBit e = true) (hf : dm.testBit f = true) :
    eval6 a b c d e f y ≤ (ws.map (eval6 a b c d e f)).sum := by
  apply score_bound h hl
  · intro v w
    simpa only [eval6, andD, Nat.testBit_and, ha, hb, hc, hd, he, hf, Bool.and_true] using value6_and
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)
  · intro v w
    simpa only [eval6, orD, Nat.testBit_and, Nat.testBit_or, ha, hb, hc, hd, he, hf, Bool.and_true] using value6_or
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)

def sumBelow (v : Nat → Nat) : List Nat → Nat → Bool
  | [], n => n != 0
  | w :: ws, n => decide (v w < n) && sumBelow v ws (n - v w)

theorem sumBelow_iff (v : Nat → Nat) (ws : List Nat) (n : Nat) :
    sumBelow v ws n = true ↔ (ws.map v).sum < n := by
  induction ws generalizing n with
  | nil => simp [sumBelow]
  | cons w ws ih => rw [sumBelow, Bool.and_eq_true, decide_eq_true_eq, ih, List.map_cons, List.sum_cons]; omega

def scoreCheck (dm y s : Nat) (ws : List Nat) (code : Nat) : Bool :=
  let a := code &&& 255
  let b := (code >>> 8) &&& 255
  let c := (code >>> 16) &&& 255
  let d := (code >>> 24) &&& 255
  let e := (code >>> 32) &&& 255
  let f := (code >>> 40) &&& 255
  dm.testBit a && dm.testBit b && dm.testBit c && dm.testBit d && dm.testBit e && dm.testBit f &&
    ws.length == s + 1 && sumBelow (eval6 a b c d e f) ws (eval6 a b c d e f y)

theorem scoreCheck_no {dm y s ws} (h : RunD dm y s ws) (code : Nat) :
    scoreCheck dm y s ws code = false := by
  unfold scoreCheck
  by_cases hok : dm.testBit (code &&& 255) = true ∧ dm.testBit ((code >>> 8) &&& 255) = true ∧
      dm.testBit ((code >>> 16) &&& 255) = true ∧ dm.testBit ((code >>> 24) &&& 255) = true ∧
      dm.testBit ((code >>> 32) &&& 255) = true ∧ dm.testBit ((code >>> 40) &&& 255) = true ∧
      ws.length = s + 1
  · obtain ⟨ha, hb, hc, hd, he, hf, hl⟩ := hok
    simp only [ha, hb, hc, hd, he, hf, hl, beq_self_eq_true, Bool.true_and]
    by_contra hbad
    have hsum := (sumBelow_iff _ _ _).1 (Bool.eq_true_of_not_eq_false hbad)
    exact (Nat.not_lt_of_ge (eval6_bound h hl _ _ _ _ _ _ ha hb hc hd he hf)) hsum
  · by_contra hbad
    have ht := Bool.eq_true_of_not_eq_false hbad
    simp only [Bool.and_eq_true, beq_iff_eq] at ht
    exact hok ⟨ht.1.1.1.1.1.1.1, ht.1.1.1.1.1.1.2, ht.1.1.1.1.1.2, ht.1.1.1.1.2, ht.1.1.1.2, ht.1.1.2, ht.1.2⟩

def scr (dm y s : Nat) (pool : List Nat) (zs : List Nat) : Bool :=
  zs.length == s + 1 && pool.any (scoreCheck dm y s zs)

theorem scr_no {dm y s : Nat} (pool : List Nat) {zs : List Nat}
    (h : RunD dm y s zs) : scr dm y s pool zs = false := by
  unfold scr; rw [Bool.and_eq_false_iff]; right; rw [List.any_eq_false]
  intro x _; rw [scoreCheck_no h x]; simp

def nextD (dm : Nat) (slack : Nat) (ws : List Nat) (f : List Nat → Bool) : Bool :=
  ws.any fun a =>
    let ra := ws.erase a
    (slack ≥ 1 &&
      (let w := negD dm a
       w != 0 && w != dm && !(ws.contains w) &&
         (f (w :: ra) || (slack ≥ 2 && f (w :: a :: ra))))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        [false, true].any fun conj =>
          let w := if conj then andD dm a b else orD dm a b
          w != 0 && w != dm && !(ws.contains w) &&
            (f (w :: r) || (slack ≥ 1 && (f (w :: a :: r) || f (w :: b :: r))) ||
              (slack ≥ 2 && f (w :: a :: b :: r))))

theorem nextD_one {dm y a rest} {save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h0 : negD dm a ≠ 0) (hd : negD dm a ≠ dm) (hnm : negD dm a ∉ (a :: rest))
    (h : RunD dm y s (negD dm a :: kept save a rest))
    (f : List Nat → Bool) (hf : ∀ ys, RunD dm y s ys → f ys = true) :
    nextD dm (s + 2 - ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a) := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hh := run_len h; have hl := p.length_eq; simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s + 2 - ws.length := by cases save <;> simp [kept] at hh <;> omega
  have hnc : ws.contains (negD dm a) = false := by
    cases h : ws.contains (negD dm a) with
    | false => rfl
    | true => exact absurd (p.mem_iff.2 (by simpa using h)) hnm
  have h0b : (negD dm a != 0) = true := bne_iff_ne.2 h0
  have hdb : (negD dm a != dm) = true := bne_iff_ne.2 hd
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; left; rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl, ?_⟩
  simp only [h0b, hdb, hnc, Bool.not_false, Bool.true_and]
  have ht := hf _ (Run.perm ((keep_perm pr save a).cons _) h)
  cases save with
  | false => simp [kept] at ht; simp [ht]
  | true => simp [kept] at ht hh; simp [ht, show 2 ≤ s + 2 - ws.length by omega]

theorem nextD_two_sorted {dm y a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h0 : (if conj then andD dm a b else orD dm a b) ≠ 0)
    (hd : (if conj then andD dm a b else orD dm a b) ≠ dm)
    (hnm : (if conj then andD dm a b else orD dm a b) ∉ (a :: b :: rest))
    (h : RunD dm y s ((if conj then andD dm a b else orD dm a b) :: kept ka a (kept kb b rest)))
    (f : List Nat → Bool) (hf : ∀ ys, RunD dm y s ys → f ys = true) :
    nextD dm (s + 2 - ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pp := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hb := pp.mem_iff.1 List.mem_cons_self
  have pr := (pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh := run_len h; have hl := p.length_eq; simp only [List.length_cons] at hl hh
  have hnc : ws.contains (if conj then andD dm a b else orD dm a b) = false := by
    cases h : ws.contains (if conj then andD dm a b else orD dm a b) with
    | false => rfl
    | true => exact absurd (p.mem_iff.2 (by simpa using h)) hnm
  have h0b : ((if conj then andD dm a b else orD dm a b) != 0) = true := bne_iff_ne.2 h0
  have hdb : ((if conj then andD dm a b else orD dm a b) != dm) = true := bne_iff_ne.2 hd
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; right; apply List.any_eq_true.2 ⟨b, hb, ?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab, ?_⟩
  apply List.any_eq_true.2 ⟨conj, by cases conj <;> simp, ?_⟩
  simp only [h0b, hdb, hnc, Bool.not_false, Bool.true_and]
  have ht := hf _ (Run.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht, Bool.true_or, Bool.or_true, Bool.and_true] <;>
    first | (simp [show 2 ≤ s + 2 - ws.length by omega]) | (simp [show 1 ≤ s + 2 - ws.length by omega])

theorem nextD_two {dm y a b rest} {conj ka kb : Bool} {s ws} (p : (a :: b :: rest).Perm ws)
    (h0 : (if conj then andD dm a b else orD dm a b) ≠ 0)
    (hd : (if conj then andD dm a b else orD dm a b) ≠ dm)
    (hnm : (if conj then andD dm a b else orD dm a b) ∉ (a :: b :: rest))
    (h : RunD dm y s ((if conj then andD dm a b else orD dm a b) :: kept ka a (kept kb b rest)))
    (f : List Nat → Bool) (hf : ∀ ys, RunD dm y s ys → f ys = true) :
    nextD dm (s + 2 - ws.length) ws f = true := by
  rcases le_total a b with hab | hba
  · exact nextD_two_sorted hab p h0 hd hnm h f hf
  · have he : (if conj then andD dm a b else orD dm a b) = (if conj then andD dm b a else orD dm b a) := by
      cases conj <;> simp [andD, orD, Nat.and_comm, Nat.or_comm]
    have hnm' : (if conj then andD dm b a else orD dm b a) ∉ (b :: a :: rest) := by
      rw [← he]; intro hm; exact hnm ((List.Perm.swap _ _ _).mem_iff.1 hm)
    apply nextD_two_sorted (conj := conj) (ka := kb) (kb := ka) hba ((List.Perm.swap _ _ _).trans p)
      (he ▸ h0) (he ▸ hd) hnm' _ f hf
    rw [he] at h; apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]; exact List.Perm.swap _ _ _

theorem nextD_complete {dm y t ws} (h : RunD dm y t ws) :
    ∀ s, t = s + 1 → ∀ zs, ws.Perm zs → ∀ f : List Nat → Bool,
      (∀ ys, RunD dm y s ys → f ys = true) →
      nextD dm (s + 2 - zs.length) zs f = true := by
  induction h using Run.fold with
  | done => simp
  | perm p _ ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one save h0 hd hnm h _ => intro s he zs p f hf; cases he; exact nextD_one p h0 hd hnm h f hf
  | two conj ka kb h0 hd hnm h _ => intro s he zs p f hf; cases he; exact nextD_two p h0 hd hnm h f hf

def span (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n + 1, i => f i && span f n (i + 1)

theorem span_ok {f n o} (h : span f n o = true) : ∀ i, o ≤ i → i < o + n → f i = true := by
  induction n generalizing o with
  | zero => omega
  | succ n ih =>
    simp only [span, Bool.and_eq_true] at h; intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)

theorem range_split {P : Nat → Prop} {lo mid hi : Nat}
    (h1 : ∀ i, lo ≤ i → i < mid → P i) (h2 : ∀ i, mid ≤ i → i < hi → P i) :
    ∀ i, lo ≤ i → i < hi → P i := fun i hlo hhi =>
  if h : i < mid then h1 i hlo h else h2 i (Nat.le_of_not_lt h) hhi

def fld (T w i : Nat) : Nat :=
  (T >>> (w * i)) &&& (if w == 32 then 4294967295 else if w == 52 then 4503599627370495 else if w == 256 then mask256 else 2 ^ w - 1)

def bsr (read : Nat → Nat) (h : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if lo + 1 < hi then
      (if read ((lo + hi) / 2) ≤ h then bsr read h f ((lo + hi) / 2) hi
       else bsr read h f lo ((lo + hi) / 2))
    else lo

def hw256 (seed w : Nat) : Nat :=
  let x := (((w % 170141183460469231731687303715884105727) ^^^ seed) * 0x9e3779b97f4a7c15f39cc0605cedc835) &&& 0xffffffffffffffffffffffffffffffff
  let y := ((x ^^^ (x >>> 61)) * 0xc2b2ae3d27d4eb4f165667b19e3779f9) &&& 0xffffffffffffffffffffffffffffffff
  y >>> 96

def hz (seed : Nat) : List Nat → Nat
  | [] => 0
  | w :: t => hw256 seed w + hz seed t

def hk (seed : Nat) (zs : List Nat) : Nat := hz seed zs &&& 4294967295

def found (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat)
    (s : Nat) (zs : List Nat) : Bool :=
  decide (idx s zs < N s) && zs.isPerm (S s (idx s zs))

def foundH (S : Nat → Nat → List Nat) (N : Nat → Nat) (htAt : Nat → Nat → Nat)
    (idxH : Nat → Nat → Nat) (s h : Nat) (zs : List Nat) : Bool :=
  let i := idxH s h
  decide (i < N s) && (htAt s i == h) && zs.isPerm (S s i)

def nextD_decor (dm mp : Nat) (slack : Nat) (dws : List (Nat × Nat × Nat))
    (f : List (Nat × Nat × Nat) → Bool) : Bool :=
  dws.any fun da =>
    let a := da.1
    let ra := dws.erase da
    (slack ≥ 1 &&
      (let w := negD dm a
       w != 0 && w != dm && !(dws.any (fun x => x.1 == w)) &&
         let dw := (w, da.2.1 ^^^ mp, da.2.2 ^^^ mp)
         (f (dw :: ra) || (slack ≥ 2 && f (dw :: da :: ra))))) ||
    ra.any fun db =>
      let b := db.1
      a ≤ b && (let r := ra.erase db
        [false, true].any fun conj =>
          let w := if conj then andD dm a b else orD dm a b
          w != 0 && w != dm && !(dws.any (fun x => x.1 == w)) &&
            let dw := if conj then (w, da.2.1 &&& db.2.1, da.2.2 &&& db.2.2)
                      else (w, da.2.1 ||| db.2.1, da.2.2 ||| db.2.2)
            (f (dw :: r) || (slack ≥ 1 && (f (dw :: da :: r) || f (dw :: db :: r))) ||
              (slack ≥ 2 && f (dw :: da :: db :: r))))

theorem nextD_decor_gen (dm mp : Nat) (dec : Nat → Nat × Nat × Nat)
    (hfst : ∀ w, (dec w).1 = w)
    (hneg : ∀ a, (negD dm a, (dec a).2.1 ^^^ mp, (dec a).2.2 ^^^ mp) = dec (negD dm a))
    (hbin : ∀ (c : Bool) a b,
      (if c then (if c then andD dm a b else orD dm a b, (dec a).2.1 &&& (dec b).2.1, (dec a).2.2 &&& (dec b).2.2)
       else (if c then andD dm a b else orD dm a b, (dec a).2.1 ||| (dec b).2.1, (dec a).2.2 ||| (dec b).2.2)) =
      dec (if c then andD dm a b else orD dm a b))
    (slack : Nat) (ws : List Nat) (g : List (Nat × Nat × Nat) → Bool) :
    nextD_decor dm mp slack (ws.map dec) g = nextD dm slack ws (fun zs => g (zs.map dec)) := by
  have hinj : Function.Injective dec := fun x y h => by rw [← hfst x, ← hfst y, h]
  have herase : ∀ (l : List Nat) x, (l.map dec).erase (dec x) = (l.erase x).map dec :=
    fun l x => erase_map_inj dec hinj l x
  have hcont : ∀ (l : List Nat) w, (l.map dec).any (fun x => x.1 == w) = l.contains w := by
    intro l w; apply Bool.eq_iff_iff.2; simp [hfst]
  unfold nextD_decor nextD
  simp only [List.any_map, Function.comp_def, hfst, herase, hcont, hneg, hbin, List.map_cons]

theorem nextD_decor_eq {dm : Nat} (hd : dm &&& mask256 = dm)
    (pairs : List (Nat × Nat))
    (hr1 : ∀ r ∈ pairs.map Prod.fst, dm.testBit r = true)
    (hr2 : ∀ r ∈ pairs.map Prod.snd, dm.testBit r = true)
    (slack : Nat) (ws : List Nat) (g : List (Nat × Nat × Nat) → Bool) :
    let dec := fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w)
    nextD_decor dm (maskP pairs.length) slack (ws.map dec) g =
      nextD dm slack ws (fun zs => g (zs.map dec)) := by
  intro dec
  apply nextD_decor_gen
  · intro w; rfl
  · intro a
    simp only [dec, projBit_negD hd hr1, projBit_negD hd hr2, List.length_map]
  · intro c a b
    cases c <;> simp only [dec, ↓reduceIte, Bool.false_eq_true, projBit_andD hr1, projBit_andD hr2,
      projBit_orD hr1, projBit_orD hr2]

def colB (mp : Nat) (d : Bool) (p : Nat × Nat) : Nat :=
  if d then (p.1 ^^^ mp) &&& p.2 else p.1 ^^^ p.2

def addC (x : Nat) (c : Nat × Nat × Nat) : Nat × Nat × Nat :=
  (c.1 ||| x, c.2.1 ||| (c.1 &&& x), c.2.2 ||| (c.2.1 &&& x))

def cov3 (mp : Nat) (d : Bool) (dws : List (Nat × Nat × Nat)) : Nat × Nat × Nat :=
  dws.foldl (fun c dw => addC (colB mp d dw.2) c) (0, 0, 0)

def takeOne (c : Nat × Nat × Nat) (x : Nat) : Nat := (c.1 ^^^ x) ||| c.2.1
def takeTwo (c : Nat × Nat × Nat) (x y : Nat) : Nat :=
  (c.1 ^^^ (x ||| y)) ||| (c.2.1 &&& (x ^^^ y)) ||| c.2.2

theorem cov3_bit (mp : Nat) (d : Bool) (dws : List (Nat × Nat × Nat)) (i : Nat) :
    let k := dws.countP (fun dw => (colB mp d dw.2).testBit i)
    (cov3 mp d dws).1.testBit i = decide (1 ≤ k) ∧
    (cov3 mp d dws).2.1.testBit i = decide (2 ≤ k) ∧
    (cov3 mp d dws).2.2.testBit i = decide (3 ≤ k) := by
  have hgen : ∀ (xs : List (Nat × Nat × Nat)) (c : Nat × Nat × Nat) (k0 : Nat),
      (c.1.testBit i = decide (1 ≤ k0) ∧ c.2.1.testBit i = decide (2 ≤ k0) ∧ c.2.2.testBit i = decide (3 ≤ k0)) →
      let k := k0 + xs.countP (fun dw => (colB mp d dw.2).testBit i)
      (xs.foldl (fun acc dw => addC (colB mp d dw.2) acc) c).1.testBit i = decide (1 ≤ k) ∧
      (xs.foldl (fun acc dw => addC (colB mp d dw.2) acc) c).2.1.testBit i = decide (2 ≤ k) ∧
      (xs.foldl (fun acc dw => addC (colB mp d dw.2) acc) c).2.2.testBit i = decide (3 ≤ k) := by
    intro xs
    induction xs with
    | nil => intro c k0 ⟨h1, h2, h3⟩; simp [h1, h2, h3]
    | cons dw xs ih =>
      intro c k0 ⟨h1, h2, h3⟩
      simp only [List.foldl_cons, List.countP_cons]
      have hc : (addC (colB mp d dw.2) c).1.testBit i =
            decide (1 ≤ k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) ∧
          (addC (colB mp d dw.2) c).2.1.testBit i =
            decide (2 ≤ k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) ∧
          (addC (colB mp d dw.2) c).2.2.testBit i =
            decide (3 ≤ k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) := by
        simp only [addC, Nat.testBit_or, Nat.testBit_and, h1, h2, h3]
        cases hb : (colB mp d dw.2).testBit i <;>
          rcases k0 with _ | _ | _ | k0 <;>
          simp [hb, Nat.le_add_left]
      have ih' := ih (addC (colB mp d dw.2) c) (k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) hc
      cases hb : (colB mp d dw.2).testBit i <;> simp only [hb, ↓reduceIte, Bool.false_eq_true, Nat.add_zero] at ih' ⊢
      · exact ih'
      · simpa only [Nat.add_assoc, Nat.add_comm 1] using ih'
  simpa only [cov3, Nat.zero_testBit, Nat.zero_add] using hgen dws (0, 0, 0) 0 (by simp)

theorem cov3_perm (mp : Nat) (d : Bool) {xs ys : List (Nat × Nat × Nat)} (p : xs.Perm ys) :
    cov3 mp d xs = cov3 mp d ys := by
  have heq : ∀ i, (cov3 mp d xs).1.testBit i = (cov3 mp d ys).1.testBit i ∧
      (cov3 mp d xs).2.1.testBit i = (cov3 mp d ys).2.1.testBit i ∧
      (cov3 mp d xs).2.2.testBit i = (cov3 mp d ys).2.2.testBit i := by
    intro i
    obtain ⟨a1, a2, a3⟩ := cov3_bit mp d xs i
    obtain ⟨b1, b2, b3⟩ := cov3_bit mp d ys i
    rw [p.countP_eq] at a1 a2 a3
    exact ⟨a1.trans b1.symm, a2.trans b2.symm, a3.trans b3.symm⟩
  apply Prod.ext
  · exact Nat.eq_of_testBit_eq (fun i => (heq i).1)
  · apply Prod.ext
    · exact Nat.eq_of_testBit_eq (fun i => (heq i).2.1)
    · exact Nat.eq_of_testBit_eq (fun i => (heq i).2.2)

theorem takeOne_eq (mp : Nat) (d : Bool) (a : Nat × Nat × Nat) (rest : List (Nat × Nat × Nat)) :
    takeOne (cov3 mp d (a :: rest)) (colB mp d a.2) = (cov3 mp d rest).1 := by
  apply Nat.eq_of_testBit_eq; intro i
  obtain ⟨h1, h2, _⟩ := cov3_bit mp d (a :: rest) i
  obtain ⟨r1, _, _⟩ := cov3_bit mp d rest i
  simp only [takeOne, Nat.testBit_or, Nat.testBit_xor, h1, h2, r1, List.countP_cons]
  set k := rest.countP (fun dw => (colB mp d dw.2).testBit i)
  cases ha : (colB mp d a.2).testBit i <;> simp only [ha, Bool.false_eq_true, ↓reduceIte] <;>
    rcases k with _ | _ | _ | k
  · decide
  · decide
  · decide
  · simp only [show 1 ≤ k + 3 by omega, show 2 ≤ k + 3 by omega, decide_true, Bool.xor_false, Bool.or_true]
  · decide
  · decide
  · decide
  · simp only [show 1 ≤ k + 3 + 1 by omega, show 2 ≤ k + 3 + 1 by omega, show 1 ≤ k + 3 by omega,
      decide_true, Bool.xor_true, Bool.or_true, Bool.or_false]

theorem takeTwo_eq (mp : Nat) (d : Bool) (a b : Nat × Nat × Nat) (rest : List (Nat × Nat × Nat)) :
    takeTwo (cov3 mp d (a :: b :: rest)) (colB mp d a.2) (colB mp d b.2) = (cov3 mp d rest).1 := by
  apply Nat.eq_of_testBit_eq; intro i
  obtain ⟨h1, h2, h3⟩ := cov3_bit mp d (a :: b :: rest) i
  obtain ⟨r1, _, _⟩ := cov3_bit mp d rest i
  simp only [takeTwo, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor, h1, h2, h3, r1, List.countP_cons]
  set k := rest.countP (fun dw => (colB mp d dw.2).testBit i)
  cases ha : (colB mp d a.2).testBit i <;> cases hb : (colB mp d b.2).testBit i <;>
    simp only [ha, hb, Bool.false_eq_true, ↓reduceIte] <;>
    rcases k with _ | _ | _ | k <;>
    (first | decide | simp only [
      show 1 ≤ k + 3 by omega, show 2 ≤ k + 3 by omega, show 3 ≤ k + 3 by omega,
      show 1 ≤ k + 3 + 1 by omega, show 2 ≤ k + 3 + 1 by omega, show 3 ≤ k + 3 + 1 by omega,
      show 1 ≤ k + 3 + 1 + 1 by omega, show 2 ≤ k + 3 + 1 + 1 by omega, show 3 ≤ k + 3 + 1 + 1 by omega,
      decide_true, Bool.xor_true, Bool.xor_false, Bool.or_true, Bool.or_false, Bool.and_true, Bool.and_false])

theorem cov3_coversD (mp s : Nat) (dw : Nat × Nat × Nat) (rest : List (Nat × Nat × Nat)) :
    let d := (dw :: rest).length == s + 1
    ((cov3 mp d rest).1 ||| colB mp d dw.2 == mp) = coversD mp s (dw :: rest) := by
  intro d
  have e : ∀ b : Bool, ((cov3 mp b rest).1 ||| colB mp b dw.2) =
      (dw :: rest).foldl (fun acc x => acc ||| colB mp b x.2) 0 := by
    intro b; apply Nat.eq_of_testBit_eq; intro i
    obtain ⟨h1, _, _⟩ := cov3_bit mp b rest i
    rw [foldl_or_testBit, Nat.zero_testBit, Bool.false_or, Nat.testBit_or, h1, List.any_cons]
    have hp : decide (1 ≤ rest.countP (fun dw => (colB mp b dw.2).testBit i)) =
        rest.any (fun x => (colB mp b x.2).testBit i) := by
      rw [Bool.eq_iff_iff, decide_eq_true_eq, Nat.succ_le_iff, List.countP_pos_iff, List.any_eq_true]
    rw [hp, Bool.or_comm]
  have hf : ∀ b : Bool, (cov3 mp b rest).1 ||| colB mp b dw.2 =
      (dw :: rest).foldl (fun acc x => acc ||| (if b then (x.2.1 ^^^ mp) &&& x.2.2 else x.2.1 ^^^ x.2.2)) 0 := by
    intro b; simpa only [colB] using e b
  unfold coversD
  dsimp only [d]
  cases (dw :: rest).length == s + 1
  · simpa only [Bool.false_eq_true, ↓reduceIte] using congrArg (· == mp) (hf false)
  · simpa only [↓reduceIte] using congrArg (· == mp) (hf true)

def nextD_cov (dm mp s slack : Nat) (dws : List (Nat × Nat × Nat))
    (f : List (Nat × Nat × Nat) → Bool) : Bool :=
  let len := dws.length
  let covF := cov3 mp false dws
  let covT := cov3 mp true dws
  let du0 := len == s + 1
  let du1 := len + 1 == s + 1
  let db0 := len - 1 == s + 1
  let db1 := len == s + 1
  let db2 := len + 1 == s + 1
  dws.any fun da =>
    let a := da.1
    (slack ≥ 1 &&
      (let pneg := (da.2.1 ^^^ mp, da.2.2 ^^^ mp)
       let uok0 := (takeOne (if du0 then covT else covF) (colB mp du0 da.2) ||| colB mp du0 pneg) == mp
       let uok1 := slack ≥ 2 && (((if du1 then covT.1 else covF.1) ||| colB mp du1 pneg) == mp)
       (uok0 || uok1) &&
       (let w := negD dm a
        w != 0 && w != dm && !(dws.any (fun x => x.1 == w)) &&
          let dw := (w, pneg)
          let ra := dws.erase da
          ((uok0 && f (dw :: ra)) || (uok1 && f (dw :: da :: ra)))))) ||
    (dws.erase da).any fun db =>
      let b := db.1
      a ≤ b &&
        [false, true].any fun conj =>
          let pz := if conj then (da.2.1 &&& db.2.1, da.2.2 &&& db.2.2)
                    else (da.2.1 ||| db.2.1, da.2.2 ||| db.2.2)
          let ok0 := (takeTwo (if db0 then covT else covF) (colB mp db0 da.2) (colB mp db0 db.2) ||| colB mp db0 pz) == mp
          let ok1a := slack ≥ 1 && ((takeOne (if db1 then covT else covF) (colB mp db1 db.2) ||| colB mp db1 pz) == mp)
          let ok1b := slack ≥ 1 && ((takeOne (if db1 then covT else covF) (colB mp db1 da.2) ||| colB mp db1 pz) == mp)
          let ok2 := slack ≥ 2 && (((if db2 then covT.1 else covF.1) ||| colB mp db2 pz) == mp)
          (ok0 || ok1a || ok1b || ok2) &&
          (let w := if conj then andD dm a b else orD dm a b
           w != 0 && w != dm && !(dws.any (fun x => x.1 == w)) &&
             let dw := (w, pz)
             let r := (dws.erase da).erase db
             ((ok0 && f (dw :: r)) || (ok1a && f (dw :: da :: r)) || (ok1b && f (dw :: db :: r)) || (ok2 && f (dw :: da :: db :: r))))

theorem nextD_cov_eq (dm mp s slack : Nat) (dws : List (Nat × Nat × Nat))
    (g : List (Nat × Nat × Nat) → Bool) :
    nextD_cov dm mp s slack dws g =
      nextD_decor dm mp slack dws (fun dzs => coversD mp s dzs && g dzs) := by
  unfold nextD_cov nextD_decor
  dsimp only
  apply Bool.eq_iff_iff.2; simp only [List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨da, hda, hrest⟩
    refine ⟨da, hda, ?_⟩
    rcases hrest with ⟨hsl, _, ⟨⟨hw0, hwdm⟩, hnw⟩, hfx⟩ | ⟨db, hdb, hab, conj, hcj, _, ⟨⟨hw0, hwdm⟩, hnw⟩, hfx⟩
    · left
      refine ⟨hsl, ⟨⟨hw0, hwdm⟩, hnw⟩, ?_⟩
      set dw := (negD dm da.1, da.2.1 ^^^ mp, da.2.2 ^^^ mp)
      set ra := dws.erase da
      have hp : dws.Perm (da :: ra) := List.perm_cons_erase hda
      have hcov0 : ((takeOne (if dws.length == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length == s + 1) da.2) ||| colB mp (dws.length == s + 1) (da.2.1 ^^^ mp, da.2.2 ^^^ mp)) == mp) =
          coversD mp s (dw :: ra) := by
        have hl : (dw :: ra).length = dws.length := by simp [hp.length_eq]
        have hc : ∀ d, cov3 mp d dws = cov3 mp d (da :: ra) := fun d => cov3_perm mp d hp
        have hc0 := cov3_coversD mp s dw ra
        rw [hl] at hc0
        cases hd : (dws.length == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hc0 ⊢
        · rw [hc false, takeOne_eq, hc0]
        · rw [hc true, takeOne_eq, hc0]
      have hcov1 :
          (((if dws.length + 1 == s + 1 then (cov3 mp true dws).1 else (cov3 mp false dws).1) |||
            colB mp (dws.length + 1 == s + 1) (da.2.1 ^^^ mp, da.2.2 ^^^ mp)) == mp) =
          coversD mp s (dw :: da :: ra) := by
        have hl : (dw :: da :: ra).length = dws.length + 1 := by simp [hp.length_eq]
        have hc : ∀ d, cov3 mp d dws = cov3 mp d (da :: ra) := fun d => cov3_perm mp d hp
        have hc1 := cov3_coversD mp s dw (da :: ra)
        rw [hl] at hc1
        cases hd : (dws.length + 1 == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hc1 ⊢
        · rw [hc false, hc1]
        · rw [hc true, hc1]
      rcases hfx with ⟨hu0, hf0⟩ | ⟨⟨hsl2, hu1⟩, hf1⟩
      · left; exact ⟨hcov0 ▸ hu0, hf0⟩
      · right; exact ⟨hsl2, hcov1 ▸ hu1, hf1⟩
    · right
      refine ⟨db, hdb, hab, conj, hcj, ⟨⟨hw0, hwdm⟩, hnw⟩, ?_⟩
      set pz := if conj then (da.2.1 &&& db.2.1, da.2.2 &&& db.2.2) else (da.2.1 ||| db.2.1, da.2.2 ||| db.2.2)
      set w := if conj then andD dm da.1 db.1 else orD dm da.1 db.1
      set dw := (w, pz)
      have hdw : (if conj = true then (w, da.2.1 &&& db.2.1, da.2.2 &&& db.2.2)
                  else (w, da.2.1 ||| db.2.1, da.2.2 ||| db.2.2)) = dw := by cases conj <;> rfl
      simp only [hdw]
      set ra := dws.erase da
      set r := ra.erase db
      have hp : dws.Perm (da :: db :: r) := (List.perm_cons_erase hda).trans (List.Perm.cons _ (List.perm_cons_erase hdb))
      have hlen_r : (dw :: r).length = dws.length - 1 := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hlen_a : (dw :: da :: r).length = dws.length := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hlen_b : (dw :: db :: r).length = dws.length := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hlen_ab : (dw :: da :: db :: r).length = dws.length + 1 := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hc2 : ∀ d, cov3 mp d dws = cov3 mp d (da :: db :: r) := fun d => cov3_perm mp d hp
      have hcov0 := cov3_coversD mp s dw r
      rw [hlen_r] at hcov0
      have hcov0' : ((takeTwo (if dws.length - 1 == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length - 1 == s + 1) da.2) (colB mp (dws.length - 1 == s + 1) db.2) |||
          colB mp (dws.length - 1 == s + 1) pz) == mp) = coversD mp s (dw :: r) := by
        cases hd : (dws.length - 1 == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov0 ⊢
        · rw [hc2 false, takeTwo_eq, hcov0]
        · rw [hc2 true, takeTwo_eq, hcov0]
      have hc_a : ∀ d, cov3 mp d dws = cov3 mp d (db :: da :: r) :=
        fun d => cov3_perm mp d (hp.trans (List.Perm.swap _ _ _))
      have hcov1a := cov3_coversD mp s dw (da :: r)
      rw [hlen_a] at hcov1a
      have hcov1a' : ((takeOne (if dws.length == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length == s + 1) db.2) ||| colB mp (dws.length == s + 1) pz) == mp) = coversD mp s (dw :: da :: r) := by
        cases hd : (dws.length == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov1a ⊢
        · rw [hc_a false, takeOne_eq, hcov1a]
        · rw [hc_a true, takeOne_eq, hcov1a]
      have hcov1b := cov3_coversD mp s dw (db :: r)
      rw [hlen_b] at hcov1b
      have hcov1b' : ((takeOne (if dws.length == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length == s + 1) da.2) ||| colB mp (dws.length == s + 1) pz) == mp) = coversD mp s (dw :: db :: r) := by
        cases hd : (dws.length == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov1b ⊢
        · rw [hc2 false, takeOne_eq, hcov1b]
        · rw [hc2 true, takeOne_eq, hcov1b]
      have hcov2 := cov3_coversD mp s dw (da :: db :: r)
      rw [hlen_ab] at hcov2
      have hcov2' : (((if dws.length + 1 == s + 1 then (cov3 mp true dws).1 else (cov3 mp false dws).1) |||
          colB mp (dws.length + 1 == s + 1) pz) == mp) = coversD mp s (dw :: da :: db :: r) := by
        cases hd : (dws.length + 1 == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov2 ⊢
        · rw [hc2 false, hcov2]
        · rw [hc2 true, hcov2]
      rcases hfx with ((⟨hu0, hf0⟩ | ⟨⟨hsl1, hu1a⟩, hf1a⟩) | ⟨⟨hsl1, hu1b⟩, hf1b⟩) | ⟨⟨hsl2, hu2⟩, hf2⟩
      · left; left; exact ⟨hcov0' ▸ hu0, hf0⟩
      · left; right; exact ⟨hsl1, Or.inl ⟨hcov1a' ▸ hu1a, hf1a⟩⟩
      · left; right; exact ⟨hsl1, Or.inr ⟨hcov1b' ▸ hu1b, hf1b⟩⟩
      · right; exact ⟨hsl2, hcov2' ▸ hu2, hf2⟩
  · rintro ⟨da, hda, hrest⟩
    refine ⟨da, hda, ?_⟩
    rcases hrest with ⟨hsl, ⟨⟨hw0, hwdm⟩, hnw⟩, hfx⟩ | ⟨db, hdb, hab, conj, hcj, ⟨⟨hw0, hwdm⟩, hnw⟩, hfx⟩
    · left
      set dw := (negD dm da.1, da.2.1 ^^^ mp, da.2.2 ^^^ mp)
      set ra := dws.erase da
      have hp : dws.Perm (da :: ra) := List.perm_cons_erase hda
      have hcov0 : ((takeOne (if dws.length == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length == s + 1) da.2) ||| colB mp (dws.length == s + 1) (da.2.1 ^^^ mp, da.2.2 ^^^ mp)) == mp) =
          coversD mp s (dw :: ra) := by
        have hl : (dw :: ra).length = dws.length := by simp [hp.length_eq]
        have hc : ∀ d, cov3 mp d dws = cov3 mp d (da :: ra) := fun d => cov3_perm mp d hp
        have hc0 := cov3_coversD mp s dw ra; rw [hl] at hc0
        cases hd : (dws.length == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hc0 ⊢
        · rw [hc false, takeOne_eq, hc0]
        · rw [hc true, takeOne_eq, hc0]
      have hcov1 : (((if dws.length + 1 == s + 1 then (cov3 mp true dws).1 else (cov3 mp false dws).1) |||
            colB mp (dws.length + 1 == s + 1) (da.2.1 ^^^ mp, da.2.2 ^^^ mp)) == mp) =
          coversD mp s (dw :: da :: ra) := by
        have hl : (dw :: da :: ra).length = dws.length + 1 := by simp [hp.length_eq]
        have hc : ∀ d, cov3 mp d dws = cov3 mp d (da :: ra) := fun d => cov3_perm mp d hp
        have hc1 := cov3_coversD mp s dw (da :: ra); rw [hl] at hc1
        cases hd : (dws.length + 1 == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hc1 ⊢
        · rw [hc false, hc1]
        · rw [hc true, hc1]
      rcases hfx with ⟨hc0, hg0⟩ | ⟨hsl2, hc1, hg1⟩
      · have hu0 : ((takeOne _ _ ||| _) == mp) = true := hcov0.symm ▸ hc0
        exact ⟨hsl, Or.inl hu0, ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inl ⟨hu0, hg0⟩⟩
      · have hu1 : ((_ ||| _) == mp) = true := hcov1.symm ▸ hc1
        exact ⟨hsl, Or.inr ⟨hsl2, hu1⟩, ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inr ⟨⟨hsl2, hu1⟩, hg1⟩⟩
    · right
      refine ⟨db, hdb, hab, conj, hcj, ?_⟩
      set pz := if conj then (da.2.1 &&& db.2.1, da.2.2 &&& db.2.2) else (da.2.1 ||| db.2.1, da.2.2 ||| db.2.2)
      set w := if conj then andD dm da.1 db.1 else orD dm da.1 db.1
      set dw := (w, pz)
      have hdw : (if conj = true then (w, da.2.1 &&& db.2.1, da.2.2 &&& db.2.2)
                  else (w, da.2.1 ||| db.2.1, da.2.2 ||| db.2.2)) = dw := by cases conj <;> rfl
      simp only [hdw] at hfx
      set ra := dws.erase da
      set r := ra.erase db
      have hp : dws.Perm (da :: db :: r) := (List.perm_cons_erase hda).trans (List.Perm.cons _ (List.perm_cons_erase hdb))
      have hlen_r : (dw :: r).length = dws.length - 1 := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hlen_a : (dw :: da :: r).length = dws.length := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hlen_b : (dw :: db :: r).length = dws.length := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hlen_ab : (dw :: da :: db :: r).length = dws.length + 1 := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hc2 : ∀ d, cov3 mp d dws = cov3 mp d (da :: db :: r) := fun d => cov3_perm mp d hp
      have hcov0 := cov3_coversD mp s dw r; rw [hlen_r] at hcov0
      have hcov0' : ((takeTwo (if dws.length - 1 == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length - 1 == s + 1) da.2) (colB mp (dws.length - 1 == s + 1) db.2) |||
          colB mp (dws.length - 1 == s + 1) pz) == mp) = coversD mp s (dw :: r) := by
        cases hd : (dws.length - 1 == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov0 ⊢
        · rw [hc2 false, takeTwo_eq, hcov0]
        · rw [hc2 true, takeTwo_eq, hcov0]
      have hc_a : ∀ d, cov3 mp d dws = cov3 mp d (db :: da :: r) :=
        fun d => cov3_perm mp d (hp.trans (List.Perm.swap _ _ _))
      have hcov1a := cov3_coversD mp s dw (da :: r); rw [hlen_a] at hcov1a
      have hcov1a' : ((takeOne (if dws.length == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length == s + 1) db.2) ||| colB mp (dws.length == s + 1) pz) == mp) = coversD mp s (dw :: da :: r) := by
        cases hd : (dws.length == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov1a ⊢
        · rw [hc_a false, takeOne_eq, hcov1a]
        · rw [hc_a true, takeOne_eq, hcov1a]
      have hcov1b := cov3_coversD mp s dw (db :: r); rw [hlen_b] at hcov1b
      have hcov1b' : ((takeOne (if dws.length == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length == s + 1) da.2) ||| colB mp (dws.length == s + 1) pz) == mp) = coversD mp s (dw :: db :: r) := by
        cases hd : (dws.length == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov1b ⊢
        · rw [hc2 false, takeOne_eq, hcov1b]
        · rw [hc2 true, takeOne_eq, hcov1b]
      have hcov2 := cov3_coversD mp s dw (da :: db :: r); rw [hlen_ab] at hcov2
      have hcov2' : (((if dws.length + 1 == s + 1 then (cov3 mp true dws).1 else (cov3 mp false dws).1) |||
          colB mp (dws.length + 1 == s + 1) pz) == mp) = coversD mp s (dw :: da :: db :: r) := by
        cases hd : (dws.length + 1 == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov2 ⊢
        · rw [hc2 false, hcov2]
        · rw [hc2 true, hcov2]
      rcases hfx with (⟨hc0, hg0⟩ | ⟨hsl1, ⟨hc1a, hg1a⟩ | ⟨hc1b, hg1b⟩⟩) | ⟨hsl2, hc2', hg2⟩
      · have u0 : ((takeTwo _ _ _ ||| _) == mp) = true := hcov0'.symm ▸ hc0
        exact ⟨Or.inl (Or.inl (Or.inl u0)), ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inl (Or.inl (Or.inl ⟨u0, hg0⟩))⟩
      · have u1a : ((takeOne _ _ ||| _) == mp) = true := hcov1a'.symm ▸ hc1a
        exact ⟨Or.inl (Or.inl (Or.inr ⟨hsl1, u1a⟩)), ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inl (Or.inl (Or.inr ⟨⟨hsl1, u1a⟩, hg1a⟩))⟩
      · have u1b : ((takeOne _ _ ||| _) == mp) = true := hcov1b'.symm ▸ hc1b
        exact ⟨Or.inl (Or.inr ⟨hsl1, u1b⟩), ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inl (Or.inr ⟨⟨hsl1, u1b⟩, hg1b⟩)⟩
      · have u2 : ((_ ||| _) == mp) = true := hcov2'.symm ▸ hc2'
        exact ⟨Or.inr ⟨hsl2, u2⟩, ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inr ⟨⟨hsl2, u2⟩, hg2⟩⟩

def bar (dm Y : Nat) (pairs : List (Nat × Nat)) (r1s r2s : List Nat) (mp : Nat)
    (SD : Nat → Nat → List (Nat × Nat × Nat)) (S : Nat → Nat → List Nat)
    (N : Nat → Nat) (htAt idxH : Nat → Nat → Nat)
    (ori : List Nat → List Nat) (seed : Nat) (pool : List Nat) (cutHitH : Nat → Nat → List Nat → Bool) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [Y])
  | s + 1, i =>
    let dws := SD (s + 1) i
    !(nextD_cov dm mp s (s + 2 - dws.length) dws fun dzs =>
        let zs := dzs.map Prod.fst
        !(scr dm Y s pool zs) &&
        (let cz := ori zs
         let h := hk seed cz
         !(cutHitH s h cz) && !(foundH S N htAt idxH s h cz)))

theorem bar_all {dm T : Nat} {pairs r1s r2s mp SD S N htAt idxH ori seed pool cutHitH cap}
    (hd : dm &&& mask256 = dm)
    (hr1_eq : r1s = pairs.map Prod.fst) (hr2_eq : r2s = pairs.map Prod.snd) (hmp_eq : mp = maskP pairs.length)
    (hSD : ∀ s j, SD s j = (S s j).map (fun w => (w, projBit r1s w, projBit r2s w)))
    (hpairs : pairs.all (fun p => dm.testBit p.1 && dm.testBit p.2 && !(T &&& dm).testBit p.1 && (T &&& dm).testBit p.2) = true)
    (hr : ∀ {u ys}, RunD dm (T &&& dm) u ys → RunD dm (T &&& dm) u (ori ys))
    (hcut : ∀ {u ys}, cutHitH u (hk seed ys) ys = true → ¬ RunD dm (T &&& dm) u ys)
    (hc : ∀ s ≤ cap, ∀ i < N s, bar dm (T &&& dm) pairs r1s r2s mp SD S N htAt idxH ori seed pool cutHitH s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ RunD dm (T &&& dm) s (S s i) := by
  subst hr1_eq hr2_eq hmp_eq
  have hr1 : ∀ r ∈ pairs.map Prod.fst, dm.testBit r = true := by
    intro r hr'; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr'
    have h := List.all_eq_true.1 hpairs p hp; simp only [Bool.and_eq_true] at h; exact h.1.1.1
  have hr2 : ∀ r ∈ pairs.map Prod.snd, dm.testBit r = true := by
    intro r hr'; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr'
    have h := List.all_eq_true.1 hpairs p hp; simp only [Bool.and_eq_true] at h; exact h.1.1.2
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    have hb := hc s hs i hi
    cases s with
    | zero => simp [bar, zero_done hh rfl] at hb
    | succ s =>
      by_contra! hn
      let F (zs : List Nat) :=
        coversP pairs s zs && !(scr dm (T &&& dm) s pool zs) &&
        (let cz := ori zs
         let h := hk seed cz
         !(cutHitH s h cz) && !(foundH S N htAt idxH s h cz))
      have hF (zs) (hz : RunD dm (T &&& dm) s zs) : F zs = true := by
        have hcz := hr hz
        have hcutf : cutHitH s (hk seed (ori zs)) (ori zs) = false := by
          cases h : cutHitH s (hk seed (ori zs)) (ori zs) with
          | false => rfl
          | true => exact absurd hcz (hcut h)
        simp only [F, coversP_ok hd pairs hpairs hz, scr_no pool hz, hcutf, Bool.not_false, Bool.true_and, foundH]
        simp only [Bool.not_eq_true', Bool.and_eq_false_imp, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
        rintro ⟨hj, _⟩
        by_contra! hp
        have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
        exact ih s (by omega) (by omega) _ hj (Run.perm p hcz)
      have hN := nextD_complete hh s rfl _ (List.Perm.refl _) F hF
      dsimp only [bar] at hb
      rw [hSD, List.length_map, nextD_cov_eq, nextD_decor_eq hd pairs hr1 hr2] at hb
      have hFeq : (fun zs => coversD (maskP pairs.length) s (zs.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w))) &&
          (let zs' := (zs.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w))).map Prod.fst
           !(scr dm (T &&& dm) s pool zs') &&
           (let cz := ori zs'
            let h := hk seed cz
            !(cutHitH s h cz) && !(foundH S N htAt idxH s h cz)))) = F := by
        funext zs
        have hfst : (zs.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w))).map Prod.fst = zs := by
          simp [List.map_map, Function.comp_def]
        rw [coversD_eq, hfst]
        simp only [F, Bool.and_assoc]
      rw [hFeq, hN] at hb
      contradiction
end PEqualNP.Outside.L_meta_25385_aux

namespace PEqualNP.Outside.L_meta_25385_aux

def Signed (d : Nat) (ws zs : List Nat) : Prop :=
  List.Forall₂ (fun w z => z = w ∨ z = negD d w) ws zs

def PosControls (d y : Nat) (zs : List Nat) : Prop :=
  ∀ i j, d.testBit i = true → d.testBit j = true →
    (∀ w ∈ zs, w.testBit i ≤ w.testBit j) → y.testBit i ≤ y.testBit j

lemma signed_self (d : Nat) (ws : List Nat) : Signed d ws ws := by
  induction ws with
  | nil => exact List.Forall₂.nil
  | cons w ws ih => exact List.Forall₂.cons (Or.inl rfl) ih

lemma signed_cons {d a z : Nat} {ws zs : List Nat}
    (ha : z = a ∨ z = negD d a) (hs : Signed d ws zs) :
    Signed d (a :: ws) (z :: zs) := List.Forall₂.cons ha hs

lemma signed_perm {d : Nat} {ws xs zs : List Nat}
    (hp : ws.Perm xs) (hs : Signed d ws zs) :
    ∃ ys, Signed d xs ys ∧ ys.Perm zs := by
  exact List.perm_comp_forall₂ hp.symm hs

lemma mono_bin {d a b i j : Nat} (c : Bool)
    (hi : d.testBit i = true) (hj : d.testBit j = true)
    (ha : a.testBit i ≤ a.testBit j) (hb : b.testBit i ≤ b.testBit j) :
    (if c then andD d a b else orD d a b).testBit i ≤
      (if c then andD d a b else orD d a b).testBit j := by
  cases c <;> simp only [andD, orD, Nat.testBit_and, Nat.testBit_or,
    hi, hj, Bool.and_true, Bool.false_eq_true, ite_false, ite_true] <;> grind

lemma neg_mono_bin {d a b i j : Nat} (hd : d &&& mask256 = d) (c : Bool)
    (hi : d.testBit i = true) (hj : d.testBit j = true)
    (ha : (negD d a).testBit i ≤ (negD d a).testBit j)
    (hb : (negD d b).testBit i ≤ (negD d b).testBit j) :
    (negD d (if c then andD d a b else orD d a b)).testBit i ≤
      (negD d (if c then andD d a b else orD d a b)).testBit j := by
  have hmi : mask256.testBit i = true := by
    have := congrArg (fun w => w.testBit i) hd
    simpa [Nat.testBit_and, hi] using this
  have hmj : mask256.testBit j = true := by
    have := congrArg (fun w => w.testBit j) hd
    simpa [Nat.testBit_and, hj] using this
  cases c <;>
    simp only [negD, andD, orD, Nat.testBit_and, Nat.testBit_or,
      Nat.testBit_xor, hi, hj, hmi, hmj, Bool.and_true,
      Bool.false_eq_true, ite_false, ite_true] at * <;>
    cases hai : a.testBit i <;> cases haj : a.testBit j <;>
    cases hbi : b.testBit i <;> cases hbj : b.testBit j <;> simp_all

lemma run_unate {d y s ws} (hd : d &&& mask256 = d) (h : RunD d y s ws)
    (hl : s ≤ ws.length) : ∃ zs, Signed d ws zs ∧ PosControls d y zs := by
  induction h using Run.fold with
  | done =>
    exact ⟨[y], signed_self _ _, fun i j hi hj hw => hw _ (by simp)⟩
  | perm hp h ih =>
    obtain ⟨zs, hz, hc⟩ := ih (by simpa only [hp.length_eq] using hl)
    obtain ⟨ys, hy, he⟩ := signed_perm hp hz
    exact ⟨ys, hy, fun i j hi hj hw => hc i j hi hj (fun w hm => hw w (he.mem_iff.mpr hm))⟩
  | @one t a r save h0 hd0 hm h ih =>
    have hlen := run_len h
    cases save with
    | true => simp [kept] at hl hlen; omega
    | false =>
      have he : (negD d a :: kept false a r).length = t + 1 := by
        simp [kept] at hl hlen ⊢; omega
      refine ⟨negD d a :: r, signed_cons (Or.inr rfl) (signed_self _ _), ?_⟩
      intro i j hi hj hw
      exact runD_bits_le h he i j hi hj (by simpa [kept] using hw)
  | @two t a b r c ka kb h0 hd0 hm h ih =>
    have hlen := run_len h
    cases ka <;> cases kb
    · obtain ⟨zs, hz, hc⟩ := ih (by simp [kept] at hl ⊢; omega)
      change List.Forall₂ _ (_ :: r) zs at hz
      cases hz with
      | @cons _ z _ zs hz hzs =>
        rcases hz with rfl | rfl
        · refine ⟨a :: b :: zs, signed_cons (Or.inl rfl) (signed_cons (Or.inl rfl) hzs), ?_⟩
          intro i j hi hj hw
          apply hc i j hi hj
          intro w hm
          simp only [List.mem_cons] at hm
          rcases hm with rfl | hm
          · exact mono_bin c hi hj (hw a (by simp)) (hw b (by simp))
          · exact hw w (by simp [hm])
        · refine ⟨negD d a :: negD d b :: zs,
            signed_cons (Or.inr rfl) (signed_cons (Or.inr rfl) hzs), ?_⟩
          intro i j hi hj hw
          apply hc i j hi hj
          intro w hm
          simp only [List.mem_cons] at hm
          rcases hm with rfl | hm
          · exact neg_mono_bin hd c hi hj (hw _ (by simp)) (hw _ (by simp))
          · exact hw w (by simp [hm])
    · refine ⟨a :: b :: r, signed_self _ _, ?_⟩
      intro i j hi hj hw
      apply runD_bits_le h (by simp [kept] at hl hlen ⊢; omega) i j hi hj
      intro w hm
      simp only [kept, Bool.false_eq_true, ite_false, ite_true, List.mem_cons] at hm
      rcases hm with rfl | rfl | hm
      · exact mono_bin c hi hj (hw a (by simp)) (hw b (by simp))
      · exact hw w (by simp)
      · exact hw w (by simp [hm])
    · refine ⟨a :: b :: r, signed_self _ _, ?_⟩
      intro i j hi hj hw
      apply runD_bits_le h (by simp [kept] at hl hlen ⊢; omega) i j hi hj
      intro w hm
      simp only [kept, Bool.false_eq_true, ite_false, ite_true, List.mem_cons] at hm
      rcases hm with rfl | rfl | hm
      · exact mono_bin c hi hj (hw a (by simp)) (hw b (by simp))
      · exact hw w (by simp)
      · exact hw w (by simp [hm])
    · simp [kept] at hl hlen; omega

def signedLists (d : Nat) : List Nat → List (List Nat)
  | [] => [[]]
  | w :: ws => (signedLists d ws).flatMap (fun zs => [w :: zs, negD d w :: zs])

lemma signed_mem_lists {d : Nat} {ws zs : List Nat} (h : Signed d ws zs) :
    zs ∈ signedLists d ws := by
  induction h with
  | nil => simp [signedLists]
  | @cons w z ws zs hz h ih =>
    apply List.mem_flatMap.mpr
    refine ⟨zs, ih, ?_⟩
    rcases hz with rfl | rfl <;> simp

def positiveCover (pairs : List (Nat × Nat)) (zs : List Nat) : Bool :=
  pairs.all (fun p => zs.any (fun w => !w.testBit p.1 && w.testBit p.2))

lemma controls_cover {d y : Nat} {pairs : List (Nat × Nat)} {zs : List Nat}
    (hpairs : pairs.all (fun p => d.testBit p.1 && d.testBit p.2 &&
      !y.testBit p.1 && y.testBit p.2) = true)
    (h : PosControls d y zs) : positiveCover pairs zs = true := by
  apply List.all_eq_true.mpr
  intro p hp
  have hh := List.all_eq_true.mp hpairs p hp
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hh
  by_contra hn
  have hnone : ∀ w ∈ zs, (!w.testBit p.1 && w.testBit p.2) = false :=
    fun w hw => Bool.eq_false_of_not_eq_true
      (List.any_eq_false.mp (Bool.eq_false_of_not_eq_true hn) w hw)
  have ho : ∀ w ∈ zs, w.testBit p.2 ≤ w.testBit p.1 := by
    intro w hw
    have hx := hnone w hw
    cases h1 : w.testBit p.1 <;> cases h2 : w.testBit p.2 <;> simp_all
  have hy := h p.2 p.1 hh.1.1.2 hh.1.1.1 ho
  rw [hh.1.2, hh.2] at hy
  contradiction

def unateBad (d : Nat) (pairs : List (Nat × Nat)) (s : Nat) (ws : List Nat) : Bool :=
  (ws.length == s) && !(signedLists d ws).any (positiveCover pairs)

lemma unateBad_no {d y : Nat} {pairs : List (Nat × Nat)} {s : Nat} {ws : List Nat}
    (hd : d &&& mask256 = d)
    (hpairs : pairs.all (fun p => d.testBit p.1 && d.testBit p.2 &&
      !y.testBit p.1 && y.testBit p.2) = true)
    (hbad : unateBad d pairs s ws = true) : ¬ RunD d y s ws := by
  intro h
  have hb := hbad
  simp only [unateBad, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hb
  obtain ⟨zs, hz, hc⟩ := run_unate hd h (by omega)
  have hyes : (signedLists d ws).any (positiveCover pairs) = true :=
    List.any_eq_true.mpr ⟨zs, signed_mem_lists hz, controls_cover hpairs hc⟩
  rw [hyes] at hb
  exact Bool.noConfusion hb.2

end PEqualNP.Outside.L_meta_25385_aux

namespace PEqualNP.Outside.L_meta_25385_aux

def signedCoverMasks (mp : Nat) : List (Nat × Nat) → List Nat
  | [] => [0]
  | p :: ps => (signedCoverMasks mp ps).flatMap fun v =>
      [((p.1 ^^^ mp) &&& p.2) ||| v, (p.1 &&& (p.2 ^^^ mp)) ||| v]

def unateBadD (mp s : Nat) (dws : List (Nat × Nat × Nat)) : Bool :=
  (dws.length == s) && !(signedCoverMasks mp (dws.map Prod.snd)).any (· == mp)

def projectedCover (pairs : List (Nat × Nat)) (zs : List Nat) : Nat :=
  zs.foldr (fun w acc =>
    ((projBit (pairs.map Prod.fst) w ^^^ maskP pairs.length) &&&
      projBit (pairs.map Prod.snd) w) ||| acc) 0

lemma foldr_or_testBit {α : Type} (g : α → Nat) (xs : List α) (i : Nat) :
    (xs.foldr (fun x a => g x ||| a) 0).testBit i =
      xs.any (fun x => (g x).testBit i) := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.foldr_cons, Nat.testBit_or, ih, List.any_cons]

lemma projectedCover_eq {pairs : List (Nat × Nat)} {zs : List Nat}
    (hc : positiveCover pairs zs = true) :
    projectedCover pairs zs = maskP pairs.length := by
  have hall := List.all_eq_true.mp hc
  apply Nat.eq_of_testBit_eq
  intro i
  rw [projectedCover, foldr_or_testBit]
  simp only [maskP, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < pairs.length
  · simp only [hi, decide_true]
    obtain ⟨w, hw, hwt⟩ := List.any_eq_true.mp (hall pairs[i] (List.getElem_mem hi))
    apply List.any_eq_true.mpr
    refine ⟨w, hw, ?_⟩
    simpa only [Nat.testBit_and, Nat.testBit_xor, projBit_testBit,
      List.length_map, hi, dite_true, Nat.testBit_two_pow_sub_one, decide_true,
      Bool.xor_true, List.getElem_map] using hwt
  · simp only [hi, decide_false, List.any_eq_false]
    intro w _
    simp only [Nat.testBit_and, Nat.testBit_xor, projBit_testBit,
      List.length_map, hi, dite_false, Nat.testBit_two_pow_sub_one, decide_false,
      Bool.xor_false, Bool.and_false, Bool.false_eq_true, not_false_eq_true]

lemma projectedCover_mem {d : Nat} {pairs : List (Nat × Nat)} {ws zs : List Nat}
    (hd : d &&& mask256 = d)
    (h1 : ∀ r ∈ pairs.map Prod.fst, d.testBit r = true)
    (h2 : ∀ r ∈ pairs.map Prod.snd, d.testBit r = true)
    (hs : Signed d ws zs) :
    projectedCover pairs zs ∈ signedCoverMasks (maskP pairs.length)
      (ws.map (fun w => (projBit (pairs.map Prod.fst) w,
        projBit (pairs.map Prod.snd) w))) := by
  induction hs with
  | nil => simp [projectedCover, signedCoverMasks]
  | @cons w z ws zs hz hs ih =>
    apply List.mem_flatMap.mpr
    refine ⟨projectedCover pairs zs, ih, ?_⟩
    rcases hz with rfl | rfl
    · simp [projectedCover]
    · simp [projectedCover, projBit_negD hd h1, projBit_negD hd h2,
        Nat.xor_assoc]

lemma unateBadD_no {d y : Nat} {pairs : List (Nat × Nat)} {s : Nat} {ws : List Nat}
    (hd : d &&& mask256 = d)
    (hpairs : pairs.all (fun p => d.testBit p.1 && d.testBit p.2 &&
      !y.testBit p.1 && y.testBit p.2) = true)
    (hbad : unateBadD (maskP pairs.length) s
      (ws.map (fun w => (w, projBit (pairs.map Prod.fst) w,
        projBit (pairs.map Prod.snd) w))) = true) :
    ¬ RunD d y s ws := by
  intro h
  have hb := hbad
  simp only [unateBadD, List.length_map, Bool.and_eq_true, beq_iff_eq,
    Bool.not_eq_true'] at hb
  obtain ⟨zs, hz, hc⟩ := run_unate hd h (by omega)
  have h1 : ∀ r ∈ pairs.map Prod.fst, d.testBit r = true := by
    intro r hr
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
    have hh := List.all_eq_true.mp hpairs p hp
    simp only [Bool.and_eq_true] at hh
    exact hh.1.1.1
  have h2 : ∀ r ∈ pairs.map Prod.snd, d.testBit r = true := by
    intro r hr
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
    have hh := List.all_eq_true.mp hpairs p hp
    simp only [Bool.and_eq_true] at hh
    exact hh.1.1.2
  have hm := projectedCover_mem hd h1 h2 hz
  rw [projectedCover_eq (controls_cover hpairs hc)] at hm
  have hyes : (signedCoverMasks (maskP pairs.length)
      ((ws.map (fun w => (w, projBit (pairs.map Prod.fst) w,
        projBit (pairs.map Prod.snd) w))).map Prod.snd)).any
      (· == maskP pairs.length) = true := by
    apply List.any_eq_true.mpr
    exact ⟨maskP pairs.length, by simpa only [List.map_map, Function.comp_def] using hm, by simp⟩
  rw [hyes] at hb
  exact Bool.noConfusion hb.2

end PEqualNP.Outside.L_meta_25385_aux

namespace PEqualNP.Outside.L_meta_25385_aux

def barFast (dm Y : Nat) (pairs : List (Nat × Nat)) (r1s r2s : List Nat) (mp : Nat)
    (SD : Nat → Nat → List (Nat × Nat × Nat)) (S : Nat → Nat → List Nat)
    (N : Nat → Nat) (htAt idxH : Nat → Nat → Nat)
    (ori : List Nat → List Nat) (seed : Nat) (pool : List Nat) (cutHitH : Nat → Nat → List Nat → Bool) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [Y])
  | s + 1, i =>
    let dws := SD (s + 1) i
    !(nextD_cov dm mp s (s + 2 - dws.length) dws fun dzs =>
        let zs := dzs.map Prod.fst
        !(unateBadD mp s dzs) && !(scr dm Y s pool zs) &&
        (let cz := ori zs
         let h := hk seed cz
         !(cutHitH s h cz) && !(foundH S N htAt idxH s h cz)))

theorem barFast_all {dm T : Nat} {pairs r1s r2s mp SD S N htAt idxH ori seed pool cutHitH cap}
    (hd : dm &&& mask256 = dm)
    (hr1_eq : r1s = pairs.map Prod.fst) (hr2_eq : r2s = pairs.map Prod.snd) (hmp_eq : mp = maskP pairs.length)
    (hSD : ∀ s j, SD s j = (S s j).map (fun w => (w, projBit r1s w, projBit r2s w)))
    (hpairs : pairs.all (fun p => dm.testBit p.1 && dm.testBit p.2 && !(T &&& dm).testBit p.1 && (T &&& dm).testBit p.2) = true)
    (hr : ∀ {u ys}, RunD dm (T &&& dm) u ys → RunD dm (T &&& dm) u (ori ys))
    (hcut : ∀ {u ys}, cutHitH u (hk seed ys) ys = true → ¬ RunD dm (T &&& dm) u ys)
    (hc : ∀ s ≤ cap, ∀ i < N s, barFast dm (T &&& dm) pairs r1s r2s mp SD S N htAt idxH ori seed pool cutHitH s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ RunD dm (T &&& dm) s (S s i) := by
  subst hr1_eq hr2_eq hmp_eq
  have hr1 : ∀ r ∈ pairs.map Prod.fst, dm.testBit r = true := by
    intro r hr'; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr'
    have h := List.all_eq_true.1 hpairs p hp; simp only [Bool.and_eq_true] at h; exact h.1.1.1
  have hr2 : ∀ r ∈ pairs.map Prod.snd, dm.testBit r = true := by
    intro r hr'; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr'
    have h := List.all_eq_true.1 hpairs p hp; simp only [Bool.and_eq_true] at h; exact h.1.1.2
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    have hb := hc s hs i hi
    cases s with
    | zero => simp [barFast, zero_done hh rfl] at hb
    | succ s =>
      by_contra! hn
      let F (zs : List Nat) :=
        coversP pairs s zs && !(unateBadD (maskP pairs.length) s (zs.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w)))) &&
        !(scr dm (T &&& dm) s pool zs) &&
        (let cz := ori zs
         let h := hk seed cz
         !(cutHitH s h cz) && !(foundH S N htAt idxH s h cz))
      have hF (zs) (hz : RunD dm (T &&& dm) s zs) : F zs = true := by
        have hcz := hr hz
        have huf : unateBadD (maskP pairs.length) s (zs.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w))) = false := by
          cases hu : unateBadD (maskP pairs.length) s (zs.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w))) with
          | false => rfl
          | true => exact absurd hz (unateBadD_no hd hpairs hu)
        have hcutf : cutHitH s (hk seed (ori zs)) (ori zs) = false := by
          cases h : cutHitH s (hk seed (ori zs)) (ori zs) with
          | false => rfl
          | true => exact absurd hcz (hcut h)
        simp only [F, coversP_ok hd pairs hpairs hz, scr_no pool hz, hcutf, huf, Bool.not_false, Bool.true_and, foundH]
        simp only [Bool.not_eq_true', Bool.and_eq_false_imp, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
        rintro ⟨hj, _⟩
        by_contra! hp
        have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
        exact ih s (by omega) (by omega) _ hj (Run.perm p hcz)
      have hN := nextD_complete hh s rfl _ (List.Perm.refl _) F hF
      dsimp only [barFast] at hb
      rw [hSD, List.length_map, nextD_cov_eq, nextD_decor_eq hd pairs hr1 hr2] at hb
      have hFeq : (fun zs => coversD (maskP pairs.length) s (zs.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w))) &&
          (let zs' := (zs.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w))).map Prod.fst
           !(unateBadD (maskP pairs.length) s (zs.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w)))) && !(scr dm (T &&& dm) s pool zs') &&
           (let cz := ori zs'
            let h := hk seed cz
            !(cutHitH s h cz) && !(foundH S N htAt idxH s h cz)))) = F := by
        funext zs
        have hfst : (zs.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w))).map Prod.fst = zs := by
          simp [List.map_map, Function.comp_def]
        rw [coversD_eq, hfst]
        simp only [F, Bool.and_assoc]
      rw [hFeq, hN] at hb
      contradiction

end PEqualNP.Outside.L_meta_25385_aux

namespace PEqualNP.Outside.L_meta_25385_aux

def totalMasks (mp : Nat) : List (Nat × Nat) → Nat
  | [] => 0
  | p :: ps => ((p.1 ^^^ mp) &&& p.2) ||| (p.1 &&& (p.2 ^^^ mp)) ||| totalMasks mp ps

def chooseCoverGuard (mp : Nat) : List (Nat × Nat) → Nat → Bool
  | [], acc => acc == mp
  | p :: ps, acc =>
      let rest := totalMasks mp ps
      let pos := acc ||| ((p.1 ^^^ mp) &&& p.2)
      let neg := acc ||| (p.1 &&& (p.2 ^^^ mp))
      ((((pos ||| rest) &&& mp) == mp) && chooseCoverGuard mp ps pos) ||
      ((((neg ||| rest) &&& mp) == mp) && chooseCoverGuard mp ps neg)

def unateBadGuard (mp s : Nat) (dws : List (Nat × Nat × Nat)) : Bool :=
  (dws.length == s) && !chooseCoverGuard mp (dws.map Prod.snd) 0

lemma signedCoverMasks_sub {mp : Nat} {ps : List (Nat × Nat)} {v : Nat}
    (hv : v ∈ signedCoverMasks mp ps) (i : Nat) (hi : v.testBit i = true) :
    (totalMasks mp ps).testBit i = true := by
  induction ps generalizing v with
  | nil =>
    simp only [signedCoverMasks, List.mem_singleton] at hv
    subst v
    simp at hi
  | cons p ps ih =>
    obtain ⟨w, hw, hv⟩ := List.mem_flatMap.mp hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · rw [Nat.testBit_or, Bool.or_eq_true] at hi
      rcases hi with hp | hwbit
      · simp [totalMasks, Nat.testBit_or, hp]
      · simp [totalMasks, Nat.testBit_or, ih hw hwbit]
    · rw [Nat.testBit_or, Bool.or_eq_true] at hi
      rcases hi with hp | hwbit
      · simp [totalMasks, Nat.testBit_or, hp]
      · simp [totalMasks, Nat.testBit_or, ih hw hwbit]

lemma coverGuard_true {mp acc v : Nat} {ps : List (Nat × Nat)}
    (hv : v ∈ signedCoverMasks mp ps) (he : acc ||| v = mp) :
    (((acc ||| totalMasks mp ps) &&& mp) == mp) = true := by
  apply beq_iff_eq.mpr
  apply Nat.eq_of_testBit_eq
  intro i
  have hs := signedCoverMasks_sub hv i
  have hb := congrArg (fun w => w.testBit i) he
  simp only [Nat.testBit_and, Nat.testBit_or] at hb ⊢
  cases ha : acc.testBit i <;> cases hv : v.testBit i <;>
    cases hr : (totalMasks mp ps).testBit i <;> cases hm : mp.testBit i <;> simp_all

lemma chooseCoverGuard_complete {mp : Nat} {ps : List (Nat × Nat)} {v acc : Nat}
    (hv : v ∈ signedCoverMasks mp ps) (hacc : acc ||| v = mp) :
    chooseCoverGuard mp ps acc = true := by
  induction ps generalizing v acc with
  | nil =>
    simp only [signedCoverMasks, List.mem_singleton] at hv
    subst v
    simpa only [chooseCoverGuard, Nat.or_zero, beq_iff_eq] using hacc
  | cons p ps ih =>
    obtain ⟨w, hw, hv⟩ := List.mem_flatMap.mp hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    change (_ || _) = true
    rw [Bool.or_eq_true]
    rcases hv with rfl | rfl
    · left
      rw [Bool.and_eq_true]
      have he : (acc ||| ((p.1 ^^^ mp) &&& p.2)) ||| w = mp := by
        simpa only [Nat.or_assoc] using hacc
      exact ⟨coverGuard_true hw he, ih hw he⟩
    · right
      rw [Bool.and_eq_true]
      have he : (acc ||| (p.1 &&& (p.2 ^^^ mp))) ||| w = mp := by
        simpa only [Nat.or_assoc] using hacc
      exact ⟨coverGuard_true hw he, ih hw he⟩

lemma unateBadGuard_imp {mp s : Nat} {dws : List (Nat × Nat × Nat)}
    (h : unateBadGuard mp s dws = true) : unateBadD mp s dws = true := by
  simp only [unateBadGuard, unateBadD, Bool.and_eq_true, Bool.not_eq_true'] at *
  refine ⟨h.1, List.any_eq_false.mpr ?_⟩
  intro v hv he
  have heq : v = mp := by simpa only [beq_iff_eq] using he
  have ht := chooseCoverGuard_complete hv (acc := 0) (by simp [heq])
  rw [ht] at h
  exact Bool.noConfusion h.2

lemma unateBadGuard_no {d y : Nat} {pairs : List (Nat × Nat)} {s : Nat} {ws : List Nat}
    (hd : d &&& mask256 = d)
    (hpairs : pairs.all (fun p => d.testBit p.1 && d.testBit p.2 &&
      !y.testBit p.1 && y.testBit p.2) = true)
    (hbad : unateBadGuard (maskP pairs.length) s
      (ws.map (fun w => (w, projBit (pairs.map Prod.fst) w,
        projBit (pairs.map Prod.snd) w))) = true) :
    ¬ RunD d y s ws := unateBadD_no hd hpairs (unateBadGuard_imp hbad)

end PEqualNP.Outside.L_meta_25385_aux

namespace PEqualNP.Outside.L_meta_25385_aux

def barGuard (dm Y : Nat) (pairs : List (Nat × Nat)) (r1s r2s : List Nat) (mp : Nat)
    (SD : Nat → Nat → List (Nat × Nat × Nat)) (S : Nat → Nat → List Nat)
    (N : Nat → Nat) (htAt idxH : Nat → Nat → Nat)
    (ori : List Nat → List Nat) (seed : Nat) (pool : List Nat) (cutHitH : Nat → Nat → List Nat → Bool) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [Y])
  | s + 1, i =>
    let dws := SD (s + 1) i
    !(nextD_cov dm mp s (s + 2 - dws.length) dws fun dzs =>
        let zs := dzs.map Prod.fst
        !(unateBadGuard mp s dzs) && !(scr dm Y s pool zs) &&
        (let cz := ori zs
         let h := hk seed cz
         !(cutHitH s h cz) && !(foundH S N htAt idxH s h cz)))

theorem barGuard_all {dm T : Nat} {pairs r1s r2s mp SD S N htAt idxH ori seed pool cutHitH cap}
    (hd : dm &&& mask256 = dm)
    (hr1_eq : r1s = pairs.map Prod.fst) (hr2_eq : r2s = pairs.map Prod.snd) (hmp_eq : mp = maskP pairs.length)
    (hSD : ∀ s j, SD s j = (S s j).map (fun w => (w, projBit r1s w, projBit r2s w)))
    (hpairs : pairs.all (fun p => dm.testBit p.1 && dm.testBit p.2 && !(T &&& dm).testBit p.1 && (T &&& dm).testBit p.2) = true)
    (hr : ∀ {u ys}, RunD dm (T &&& dm) u ys → RunD dm (T &&& dm) u (ori ys))
    (hcut : ∀ {u ys}, cutHitH u (hk seed ys) ys = true → ¬ RunD dm (T &&& dm) u ys)
    (hc : ∀ s ≤ cap, ∀ i < N s, barGuard dm (T &&& dm) pairs r1s r2s mp SD S N htAt idxH ori seed pool cutHitH s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ RunD dm (T &&& dm) s (S s i) := by
  subst hr1_eq hr2_eq hmp_eq
  have hr1 : ∀ r ∈ pairs.map Prod.fst, dm.testBit r = true := by
    intro r hr'; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr'
    have h := List.all_eq_true.1 hpairs p hp; simp only [Bool.and_eq_true] at h; exact h.1.1.1
  have hr2 : ∀ r ∈ pairs.map Prod.snd, dm.testBit r = true := by
    intro r hr'; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr'
    have h := List.all_eq_true.1 hpairs p hp; simp only [Bool.and_eq_true] at h; exact h.1.1.2
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    have hb := hc s hs i hi
    cases s with
    | zero => simp [barGuard, zero_done hh rfl] at hb
    | succ s =>
      by_contra! hn
      let F (zs : List Nat) :=
        coversP pairs s zs && !(unateBadGuard (maskP pairs.length) s (zs.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w)))) &&
        !(scr dm (T &&& dm) s pool zs) &&
        (let cz := ori zs
         let h := hk seed cz
         !(cutHitH s h cz) && !(foundH S N htAt idxH s h cz))
      have hF (zs) (hz : RunD dm (T &&& dm) s zs) : F zs = true := by
        have hcz := hr hz
        have huf : unateBadGuard (maskP pairs.length) s (zs.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w))) = false := by
          cases hu : unateBadGuard (maskP pairs.length) s (zs.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w))) with
          | false => rfl
          | true => exact absurd hz (unateBadGuard_no hd hpairs hu)
        have hcutf : cutHitH s (hk seed (ori zs)) (ori zs) = false := by
          cases h : cutHitH s (hk seed (ori zs)) (ori zs) with
          | false => rfl
          | true => exact absurd hcz (hcut h)
        simp only [F, coversP_ok hd pairs hpairs hz, scr_no pool hz, hcutf, huf, Bool.not_false, Bool.true_and, foundH]
        simp only [Bool.not_eq_true', Bool.and_eq_false_imp, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
        rintro ⟨hj, _⟩
        by_contra! hp
        have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
        exact ih s (by omega) (by omega) _ hj (Run.perm p hcz)
      have hN := nextD_complete hh s rfl _ (List.Perm.refl _) F hF
      dsimp only [barGuard] at hb
      rw [hSD, List.length_map, nextD_cov_eq, nextD_decor_eq hd pairs hr1 hr2] at hb
      have hFeq : (fun zs => coversD (maskP pairs.length) s (zs.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w))) &&
          (let zs' := (zs.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w))).map Prod.fst
           !(unateBadGuard (maskP pairs.length) s (zs.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w)))) && !(scr dm (T &&& dm) s pool zs') &&
           (let cz := ori zs'
            let h := hk seed cz
            !(cutHitH s h cz) && !(foundH S N htAt idxH s h cz)))) = F := by
        funext zs
        have hfst : (zs.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w))).map Prod.fst = zs := by
          simp [List.map_map, Function.comp_def]
        rw [coversD_eq, hfst]
        simp only [F, Bool.and_assoc]
      rw [hFeq, hN] at hb
      contradiction

end PEqualNP.Outside.L_meta_25385_aux

namespace PEqualNP.Outside.L_meta_25385_aux.Backup
def pairsG : List (Nat × Nat) := [(2,0),(2,1),(2,4),(2,5),(2,7),(2,9),(2,10),(3,0),(3,1),(3,4),(3,5),(3,7),(3,9),(3,10),(6,0),(6,1),(6,4),(6,5),(6,7),(6,9),(6,10),(8,0),(8,1),(8,4),(8,5),(8,7),(8,9),(8,10),(11,0),(11,1),(11,4),(11,5),(11,7),(11,9),(11,10),(12,0),(12,1),(12,4),(12,5),(12,7),(12,9),(12,10),(13,0),(13,1),(13,4),(13,5),(13,7),(13,9),(13,10),(14,0),(14,1),(14,4),(14,5),(14,7),(14,9),(14,10)]
def r1sG : List Nat := [2,2,2,2,2,2,2,3,3,3,3,3,3,3,6,6,6,6,6,6,6,8,8,8,8,8,8,8,11,11,11,11,11,11,11,12,12,12,12,12,12,12,13,13,13,13,13,13,13,14,14,14,14,14,14,14]
def r2sG : List Nat := [0,1,4,5,7,9,10,0,1,4,5,7,9,10,0,1,4,5,7,9,10,0,1,4,5,7,9,10,0,1,4,5,7,9,10,0,1,4,5,7,9,10,0,1,4,5,7,9,10,0,1,4,5,7,9,10]
def mpG : Nat := 72057594037927935
def rootsG : List Nat := [31,482,3652,13448,26896]
def NN : Nat → Nat
  | 3 => 6
  | 4 => 95
  | 5 => 947
  | 6 => 2709
  | 7 => 944
  | 8 => 42
  | 9 => 1
  | _ => 0
def dictB : Nat → Nat
  | 0 => 0x6b54d67dacc358a6b10d3a9a6fb4cc6994d321a4fb49d6938d269a4c348e6918d229a443480683ed075a0431ea6354c27d844304c6010bfb97a72f445d88b97d72a2e4c5c88a78948729005180a07d40628004bc4955120fa414481090010ffa1f243d4878908fa10a4200827d0442080403e804100420003dde7b30bf796ff2dde5bb8b7696eb2dd05b9cb7016cc2d5e59bcb0f960d2c185800af514ea293e5220a0412ef217e42ac85190881ffe3fdc7fb0fee1fcc3f887f00fc41ea83d307a30f441dbe3b307630ec41cce397c72f0e5c1cae395872a0e4e1c9839187220e401c3e38747020e001bc4360060f8c181800295c52209ff13e427984f10944123e244048409061200238842f88441080207c40b88101010201040007440dfe1b98370064c0c8817fc2f505e60bc4127c244048008be11282220440083e1020202040007ce09fc1338260040a07fc0fd81fa03ee07d80f981f203de07b80f501e803ce07980f181e203c007000df81bb0344067c0cc018002fe05dc0b1015f02a8050008f811702200420081010001fe03dc07780e201c0037c06600c20180027c04b80880104020002f80570098012002200420080008c00f801d0038006c00d0018002e005800a801400260048008000f001c00300050008000e00180020002
  | 1 => 0x7ffefffbffefffc7ff7ffebffcfff87fefffd9ffafff57fe8ffcfff93ff17fe0ffb9ff23fdfffbbff51fe83fbfff77fec1fcfff8fff1dfe39fc43f847efffdd1fb83f4efe88fcbbf913f0ffe1dfc39f867f0afe0dfc11f803efd7dd8fb3ff673ecd7d98fb21f623ec07d18f931f063dfffbf7f7c1e877cddf9b3f331e47fc8cf7ffefd1df83b7ff61deb77d6a3acc71ffe3f7c78b8dff1bbe373c6cf8d8f1abe347c6838cc713be177c07f80cf000dfffbfdb7ea6f77debfbd7b7ae6f56dea9bd337a26f40dca9b7cb6c86d50da3fb46368a6d10d7efaddf58ae9ffd3f5a7df4fb69f3d3e5a7c34f469e2d3c1a7434cfe998d325a6434afe954d2a5a5434a26933d23fa47748e691bd235a46348be916d22ba453489e912d223a4434846904d201a0430f96110bfff7fdeff05e1da37746ce7fbcf779ea939565fbcbe296ff2dde5bacb7396cf2d8259bca77942b28024fbc9f2923f245e488490086ef07ce099c0117fdcff31f6fbedc7d9cfb31f643e8c7c98f831ef53d887990f27de4c3c8c7910dbfdb77b6ee6dd0db31affb5fa6bdcd7a9af435c8
  | _ => 0
def dictP1B : Nat → Nat
  | 0 => 0x1fff80fe03f8001fff80fe03fff01fff80fe03f8001fff80fe03f8001fff80fe03f8001fff8001fff8001fff8001fffff01fff8001fffff01fff8001fff8001fff8001fff8001fff800003fff01fff800003fff01fff800003fff01fff800003f8001fff800003f8001fff800003fff01fff800003fff01fff800003f8001fff800003f8001fff80000000001fff800003fff01fff800003fff01fff800003f8001fff80fffff8001fff80fe03f8001fff800003fff01fff800003f8001fff8001fffff01fff800003f8001fc07ffffffff01fc07ffffffff01fc07ffffc07f01fc07f01fc07f01fc07f01fffff01fc07f01fc07f01fc07f01fffff01fc07f01fc07f01fc07ffffc00001fc07ffe03fff01fc07ffe0000001fc07f01fc00001fc07f0003fff01fc07f0003fff01fc07f000000001fc000fffc00001fc000fffc07f01fc0000003fff01fc000000007f01fc0000003f8001fc000000000001fc000fffffff01fc000fffc00001fc000fffff8001fc000fffc00001fc000fe03fff01fc000fe03f8001fc000fe0000001fc0000003fff01fc0000003f8001fc000000000001fc0000003fff01fc000000000001fc0000003f8001fc00000000000003fff01fffff0003fff01fffff0003f80fffffff0003f8001fffff0003f8001fffff0003f8001fffff0003f8001fffff0003f8001fff800003f8001fff800003f8001fc07f0003f8001fc0000003f8001fffff0003f800003fff0003f8001fffff0003f800003fff0003f800003fff0003f800003fff0003f8000000000003f80fffff800003f8001fff800003f800003fff0003f800003f800003f800003f800003f8001fffff0003f800003fff0003f800003f800003f8000000000003f800003f80000007ffffffff000007ffffc07f000007ffffc07f000007ffffffff000007ffffc07f000007ffffc000000007ffffc000000007ffffc07f000007ffffc07f000007ffffffff000007ffffc07f000007ffffc07f000007f01fffff000007f01fffff000007f01fc07f000007f01fc07f000007f01fc07f000007f01fffff000007f01fffff000007f01fffff000007f01fc07f000007f01fc07f000007f01fc07f000007f01fffff000007f01fffff000007f01fc07f000007f01fc07f000007f01fc000000007f0003fff000007f0003fff000007f000007f000007f0000000000007ffffc000000007ffe00000000007f0003fff000007f0003f80000007f0000000000007f01fc07f000007f01fc07f000007ffffffff000007ffffc000000007ffffc07f000007ffffc000000007ffffc07f000007ffe03fff000007ffe00000000007ffe03f80000007ffe0007f000007ffe00000000007f01fc000000007f01fffff000007f01fc07f000007f01fc000000007f0003fff000007f000007f000007f0000000000007f0003f80000007f000007f000007f00000000000000fffc07f000000001fffff000000001fc07f000000001fc000000000001fffff000000001fc07f0000000fffffff0000000fffff800000000fffc07f0000000fffc00000000000003fff00000000003f8000000000000000000000001fffff000000001fff80000000001fc07f000000001fc00000000000003fff00000000003f800000000000007f000000000000000000000fffc07f000000001fffff000000001fc07f000000001fc0000000000000007f0000000fffffff0000000fffff800000000fffff800000000fffc07f0000000fffc07f0000000fffc0000000000fffc0000000000fffffff0000000fffffff0000000fffff800000000fffff800000000fffc07f0000000fffc07f0000000fffc0000000000fffc0000000000fffc0000000000fffc0000000000fe03fff0000000fe03f800000000fe000000000000fe03fff0000000fe03f800000000fe000000000000fffffff0000000fffc07f0000000fffc0000000000fffffff0000000fffc07f0000000fffc0000000000fe03fff0000000fe0007f0000000fe000000000000fe03f800000000fe000000000000fe00000000000001fffff000000001fc07f000000001fffff000000001fc000000000001fc000000000001fffff000000001fffff000000001fc000000000001fc00000000000003fff0000000000007f00000000003f800000000000000000000000000000000000001fffff000000001fc07f000000001fffff000000001fff80000000001fc07f000000001fc000000000001fc0000000000000000000000000003fff00000000003fff00000000003fff00000000003f8000000000003f8000000000003f800000000000007f0000000000007f0000000000007f0000000000007f00000000000000000000000000000000000000000000000000003fff00000000003fff00000000003fff00000000003f8000000000003f800000000000007f0000000000007f0000000000007f00000000000000
  | 1 => 0xffffffffffffffffffffffffffffffffffffffff80ffffffffffff80ffffffffffc07fffffffffffc07fffffffffffc000ffffffffffc000ffffffffffffffffffffffffffffffffffffffff80ffffffffffff80ffffffffffff80ffffffffffc07fffffffffffc07fffffffffffc000ffffffffffc000ffffffffffffffffffffffffff80ffffffffe03fffffffffffe03f80ffffffffe03f80ffffffffe00000ffffffffffffffffffffffffc07fffffffffffc000ffffffffe03fffffffffffe03fffffffffffe03fffffffffffe03fffffffffffe00000ffffffffe03f80fffffff01ffffffffffff01fff80fffffff01fc000fffffff0003ffffffffff0003f80fffffff01ffffffffffff01fc07ffffffff0003ffffffffff0003ffffffffff0003ffffffffff0003f80fffffff000007ffffffff0003ffffffffff0003f80fffffff0000000ffffffffffff80ffffffffffff80ffffffffe03fffffffffffe03fffffffffffe03f80ffffffffe03f80ffffffffe00000ffffffffe03f80ffffffffe00000ffffffffe03f80fffffff0003f80fffffff0003f80ffffffffffffffffffffffffc07fffffffffffc000fffffff0003fffffffffffe03f80ffffffffe00000ffffffffe03f80ffffffffe03fffffffffffe03f80fffff80ffffffffffff80fffff80fffff80fffc000fffff8001ffffffffff800003ffffffff80fe03f80fffff80fe03f80fffff80fe03f80fffff80ffffffffffff80fffff80fffff80fffc000fffff80fe03ffffffff80fe03f80fffff80fe03f80fffff80fe00000fffff80fe00000fffff80fe03f80fffff80fe00000fffff80fe00000fffff80fe03f80fffff80fe03f80fffff800003f80fffff800003ffffffff800003f80fffff800000000fffc07fffffffffffc07ffffc07ffffc07ffffc07ffffc07ffffc07ffffc07fffffffffffc07fffffffffffc07fffffffffffc07ffffc07ffffc07ffffc07ffffc07fffffffffffc07ffffc07ffffc07ffffc000fffc07f01fc07ffffc07ffffc000fffc07ffe00000fffc07ffffc000fffc07ffe03ffffffc07ffe03f80fffc07ffe0007ffffc07ffe00000fffc07ffffc07ffffc07ffffc07ffffc07ffe0007ffffc07fffffffffffc07ffffff80fffc07ffffc07ffffc07ffffc07ffffc07ffffc000fffc07ffffc000fffc07ffffc000fffc07ffffff80fffc07ffffc000fffc07ffffc000fffc07ffffc000fffc07ffe03ffffffc07ffe03f80fffc07ffe00000fffc07ffe00000fffc07fffffffffffc07ffffc07ffffc07ffffc000fffc07ffffc000fffc07ffffc07ffffc07ffe00000fffc07ffe03ffffffc07ffe03ffffffc07ffe03ffffffc07ffe03f80fffc07ffe03f80fffc07ffe03f80fffc07ffe0007ffffc07ffe0007ffffc07ffe0007ffffc07ffe0007ffffc07ffe00000fffc07ffe00000fffc07ffe00000fffc07ffe00000fffc07ffe03f80fffc07ffe0007ffffc07ffe00000fffc07f0000000fffc000fffc000fffc000fe00000fe03fffffffffffe03ffffffc07ffe03ffffffc000fe03fff0003ffffe03f80fe03f80fe03f80fe00000fe0007ffffc07ffe0007ffffc07ffe0007ffffc07ffe0007f01fc07ffe0007ffffc07ffe0007ffffc000fe0007fffffffffe0007ffffc07ffe0007ffffc07ffe0007ffffc000fe0007ffffc07ffe0007ffffc000fe0007ffe0007ffe0007f01fc07ffe0007f000007ffe0007f0000000fe0007ffffc07ffe0007ffffc000fe0007ffe03ffffe0007ffe0007ffe0007ffe00000fe0007ffe00000fe00000fffc07ffe00000fffc000fe00000fe00000fe00000000000001ffffffffffff01ffffffffffff01fffff01fffff01fffff01fffff01fffff01fffff01fffff01fffff01fffff01fff8001fffff0003fff01fffff01fffff01fffff0003fff01ffffffffff8001ffffffe03f8001fffff01fff8001fffff0003fff01fffff0003f8001fffff0003fff01fffff0003f8001fff8001fffff01fff8001fffff01fff8001fffff01fff8001fff8001fff8001fffff01fff80fffffff01fff80fffff8001fff80fffffff01fff80fffff8001fff80fffff8001fff80fffff80
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0xb56ad5ab56ad5aaf5ebd7af5ebd7a952a54a952a54a54a952a54a952a142850a142850b56ad5ab56ad5aaf5ebd7af5ebd7a142850a142850a54a952a54a952a142850a142850af5ebd7af5ebd7ab56ad5ab56ad5a952a54a952a54ad5ab56ad5ab56a952a54a952a54a54a952a54a952a142850a142850a54a952a54a952a142850a142850a142850a1428508f1e3c78f1e3c78b162c58b162c5810204081020403468d1a3468d1a3468d1a3468d1a2e5cb972e5cb97204081020408100000000000000000000000000000f5ebd7af5ebd7ac58b162c58b162c183060c183060e1c3870e1c3870cf9f3e7cf9f3e7c993264c993264c183060c183060c183060c1830603468d1a3468d1a0408102040810200000000000000204081020408100e1c3870e1c3870000000000000000000000000000b56ad5ab56ad5a891224489122448f1e3c78f1e3c78912244891224481020408102040810204081020403e7cf9f3e7cf9f3c78f1e3c78f1e3468d1a3468d1a3468d1a3468d1a0e1c3870e1c38704081020408102000000000000002e5cb972e5cb9720408102040810204081020408100e1c3870e1c387081020408102040000000000000000000000000000f7efdfbf7efdfbe1c3870e1c3870f7efdfbf7efdfbfffffffffffffff7efdfbf7efdfbf5ebd7af5ebd7af3e7cf9f3e7cf9f7efdfbf7efdfbf1e3c78f1e3c78f7efdfbf7efdfbf1e3c78f1e3c78e1c3870e1c3870f7efdfbf7efdfbd7af5ebd7af5ebcf9f3e7cf9f3e7c3870e1c3870e1c183060c183060c183060c183060b56ad5ab56ad5ab56ad5ab56ad5aaf5ebd7af5ebd7a142850a1428508102040810204076eddbb76eddbb3e7cf9f3e7cf9f366cd9b366cd9b366cd9b366cd9b20408102040810fffffffffffffffffffffffffffffdfbf7efdfbf7ef5ebd7af5ebd7af5ebd7af5ebd7af5ebd7af5ebd7af1e3c78f1e3c78e1c3870e1c3870c993264c993264c183060c183060c58b162c58b162c183060c183060efdfbf7efdfbf7e1c3870e1c3870e5cb972e5cb972e1c3870e1c3870d7af5ebd7af5ebcf9f3e7cf9f3e7cd9b366cd9b366c993264c993264cf9f3e7cf9f3e7cd9b366cd9b366c993264c993264c58b162c58b162c183060c183060c58b162c58b162c183060c183060c183060c183060cf9f3e7cf9f3e7cb972e5cb972e5c183060c183060c183060c183060b56ad5ab56ad5aa142850a1428508f1e3c78f1e3c789122448912244810204081020404e9d3a74e9d3a7408102040810203e7cf9f3e7cf9f3c78f1e3c78f1e3468d1a3468d1a3468d1a3468d1a000000000000000e1c3870e1c387081020408102040000000000000004081020408102000000000000003468d1a3468d1a0e1c3870e1c38700000000000000000000000000000e1c3870e1c3870e1c3870e1c38708102040810204000000000000000000000000000000000000000000c183060c183060fffffffffffffff5ebd7af5ebd7af1e3c78f1e3c78c183060c183060c183060c183060bf7efdfbf7efdfb56ad5ab56ad5ab56ad5ab56ad5ab56ad5ab56ad5aaf5ebd7af5ebd7a142850a142850a142850a1428508f1e3c78f1e3c7850a142850a14281020408102040810204081020408f1e3c78f1e3c781020408102040810204081020408102040810204076eddbb76eddbb5ebd7af5ebd7af56ad5ab56ad5ab50a142850a142842850a142850a13e7cf9f3e7cf9f3e7cf9f3e7cf9f3c78f1e3c78f1e3e7cf9f3e7cf9f3c78f1e3c78f1e3e7cf9f3e7cf9f3c78f1e3c78f1e366cd9b366cd9b3468d1a3468d1a3468d1a3468d1a3060c183060c18366cd9b366cd9b3468d1a3468d1a366cd9b366cd9b3468d1a3468d1a3060c183060c18204081020408103e7cf9f3e7cf9f3e7cf9f3e7cf9f3468d1a3468d1a2e5cb972e5cb972850a142850a14204081020408101e3c78f1e3c78f1e3c78f1e3c78f142850a142850a0e1c3870e1c38708102040810204000000000000000e1c3870e1c3870e1c3870e1c387081020408102040000000000000004081020408102000000000000003e7cf9f3e7cf9f3e7cf9f3e7cf9f366cd9b366cd9b3468d1a3468d1a3060c183060c182e5cb972e5cb972040810204081024489122448912204081020408102e5cb972e5cb972e5cb972e5cb972040810204081024489122448912204081020408100e1c3870e1c3870e1c3870e1c3870000000000000000000000000000000000000000000408102040810200000000000000162c58b162c58b0e1c3870e1c3870a142850a14285081020408102040e1c3870e1c3870c183060c18306081020408102040e1c3870e1c3870c183060c183060a142850a14285081020408102040e1c3870e1c3870c183060c1830608102040810204060c183060c18304081020408102000000000000000408102040810200000000000000060c183060c183040810204081020000000000000004081020408102
  | 1 => 0xfdfbf7efdfbf7efbf7efdfbf7efdfffffffffffffff9f3e7cf9f3e7cfffffffffffffffbf7efdfbf7efdfffffffffffffff9f3e7cf9f3e7cf7efdfbf7efdfbf1e3c78f1e3c78f7efdfbf7efdfbf5ebd7af5ebd7af1e3c78f1e3c78f7efdfbf7efdfbf1e3c78f1e3c78f5ebd7af5ebd7af1e3c78f1e3c78e9d3a74e9d3a74e1c3870e1c3870fffffffffffffffffffffffffffff1e3c78f1e3c78f1e3c78f1e3c78dfbf7efdfbf7efdfbf7efdfbf7efd1a3468d1a3468dfbf7efdfbf7efcf9f3e7cf9f3e7cb972e5cb972e5c993264c993264c993264c993264c183060c183060fffffffffffffff1e3c78f1e3c78f1e3c78f1e3c78ebd7af5ebd7af5e1c3870e1c3870cb972e5cb972e5c183060c183060cf9f3e7cf9f3e7cb972e5cb972e5c993264c993264cb972e5cb972e5cb972e5cb972e5c3870e1c3870e1c183060c183060c183060c183060bd7af5ebd7af5ea952a54a952a54af5ebd7af5ebd7a952a54a952a54ad5ab56ad5ab56a952a54a952a54a952a54a952a54a142850a142850a142850a14285089122448912244a952a54a952a54891224489122447efdfbf7efdfbf7efdfbf7efdfbf70e1c3870e1c384a952a54a952a53e7cf9f3e7cf9f3e7cf9f3e7cf9f2850a142850a140e1c3870e1c3870a142850a14285fffffffffffffff1e3c78f1e3c78f1e3c78f1e3c78ffffffffffffffcb972e5cb972e5bf7efdfbf7efdfb162c58b162c58a952a54a952a543e7cf9f3e7cf9f3e7cf9f3e7cf9f3468d1a3468d1a3e7cf9f3e7cf9f3e7cf9f3e7cf9f3a74e9d3a74e9d3e7cf9f3e7cf9f3a74e9d3a74e9d366cd9b366cd9b366cd9b366cd9b3060c183060c182850a142850a141e3c78f1e3c78f3e7cf9f3e7cf9f0e1c3870e1c3870a142850a1428500000000000000fffffffffffffffdfbf7efdfbf7ee9d3a74e9d3a74dfbf7efdfbf7efcf9f3e7cf9f3e7cd9b366cd9b366c993264c993264cd9b366cd9b366c993264c993264c183060c183060c183060c183060c183060c183060c993264c993264bd7af5ebd7af5ea952a54a952a54891224489122448f1e3c78f1e3c78912244891224489122448912244891224489122447efdfbf7efdfbf5ebd7af5ebd7af4a952a54a952a53e7cf9f3e7cf9f3c78f1e3c78f1e3e7cf9f3e7cf9f3c78f1e3c78f1e3e7cf9f3e7cf9f3c78f1e3c78f1e3870e1c3870e1c3060c183060c183468d1a3468d1a3060c183060c182850a142850a142e5cb972e5cb972850a142850a142c58b162c58b162850a142850a140e1c3870e1c387081020408102040c183060c1830608102040810204000000000000001e3c78f1e3c78f0e1c3870e1c3870a142850a14285081020408102040e1c3870e1c3870c183060c18306081020408102040e1c3870e1c3870c183060c183060a142850a14285081020408102040e1c3870e1c3870c183060c183060a142850a1428508102040810204000000000000000000000000000000000000000000081020408102043c78f1e3c78f1e08102040810204fffffffffffffffffffffffffffff1e3c78f1e3c78cb972e5cb972e53e7cf9f3e7cf9f3e7cf9f3e7cf9fffffffffffffffdfbf7efdfbf7efc993264c993264cb972e5cb972e57efdfbf7efdfbf74e9d3a74e9d3a5ebd7af5ebd7af5ebd7af5ebd7af5ab56ad5ab56ad5ebd7af5ebd7af56ad5ab56ad5ab50a142850a14285ebd7af5ebd7af5ebd7af5ebd7af4a952a54a952a5408102040810203e7cf9f3e7cf9f3c78f1e3c78f1e0e1c3870e1c3870e1c3870e1c38708102040810204000000000000005ebd7af5ebd7af3e7cf9f3e7cf9f1e3c78f1e3c78f0a142850a14285f5ebd7af5ebd7ae1c3870e1c3870efdfbf7efdfbf7e9d3a74e9d3a74e5cb972e5cb972e1c3870e1c3870e1c3870e1c3870e1c3870e1c3870c183060c183060c183060c183060b56ad5ab56ad5aa142850a142850a142850a142850af5ebd7af5ebd7a952a54a952a54a142850a142850a142850a142850fffffffffffffff7efdfbf7efdfbf5ebd7af5ebd7af1e3c78f1e3c78e1c3870e1c3870bf7efdfbf7efdfbd7af5ebd7af5eb56ad5ab56ad5ab56ad5ab56ad5ab162c58b162c58a142850a142850
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 256)) 15 (i % 256)
def p1At (i : Nat) : Nat := fld (dictP1B (i / 256)) 56 (i % 256)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 256)) 56 (i % 256)
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 473 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireSAt (i : Nat) : Nat := if i < 473 then wireAt i else 0
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 473 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢
    rw [ih]
    rfl

theorem wireDAt_eq (i : Nat) : wireDAt i =
    (wireSAt i, projBit r1sG (wireSAt i), projBit r2sG (wireSAt i)) := by
  unfold wireDAt wireSAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) hi
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, v => wireDAt (v &&& 511) :: stateWiresD n (v >>> 9)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, v => wireSAt (v &&& 511) :: stateWiresS n (v >>> 9)
theorem stateWiresD_eq (n v : Nat) : stateWiresD n v =
    (stateWiresS n v).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireDAt_eq, ih]
def stateW : Nat → Nat
  | 3 => 31
  | 4 => 40
  | 5 => 49
  | 6 => 58
  | 7 => 67
  | 8 => 58
  | 9 => 49
  | _ => 0
def stateB : Nat → Nat → Nat
  | 3, 0 => 0x172b21509c8153a8bb53e74f89a1cc0063151000c82b2
  | 4, 0 => 0x71ee15f300224e64b3004fd164e3a7ba512874005769e89300732bea63a927c2a0640018c5604300509122a3a7c4d24404005cec810300509304b300730c6283002ed122a3a144d244e400732e75f3aa3b53e09476af13e1940060e844e3a7c4d0a154aac593e1d4a127c3615400509344e30057d4a153001905015300732e75e30057e04d23aa4593e1540022ce64e3004ce480f3a13e0b8154006e6848939fbb53e194a127c320f4005cd600f300732e35f3a144d0e1540071ae75f3a138c32154a128c36154d853e26924005d560153a8bb51240400505124e3aac59244e4a123c96194006ae7e893a128832154005cebe0d3005091a4b30053e24923005cd5e153a128036154aa46d3e4e400509162b30059282893002ed162b30057e2ca7300736e75f300509204e3002f1124b3aac593e1547699832154002ed204e30057d4c0f3a144d0c15476a7cf04e4a127c3a1b40018c500f30071ebea73005cebe0f3aa46d3e154005291a4e3aa3e13e154005cec0153e65093e19400732e6b03a1288320f4005d6be153004fd124b3005dabe153a14d432154003652440376a7cf0154002f1164e3005ca9e40300224ea4e3005c2bf16300732e35c3aac5924404006aa8490300722eb5f30053e3c923cabb432154a12489c1b4
  | 5, 0 => 0x5cebe8b0aa0029f25448552849f449182aa00e450916454e65093a892028036142448350014a459002a94f7422480155003b4c6280aa509124e2006d401ccb9aec80800d8d09120f4a14093e190aa8027e892003d0015f76a9d4c94289a4880155005cebeed682002c9426e0550015f532902a800b9c096015400509da941320024289200d9001cca0a248094f76a489c19500732e75fa12002e75f768550017376ac018800a12249c2e4002d5124007a00369b0a122500173ad3b42a800a7c6d24404006f2848b0aa50924892009540143449002a800afd2916154bd509da700aabb5789f44939401c9b9d7dda9c4a13b53e1550054a62890aa002e74a2705500173afbb5a2800a7c3124404005cebeee0aa00284f84913900188a112c2a800b9d7e361540052916450aa00284a520055001427aa2c9c800b9d7e00154005cebf027aa00311212003d00000bad7c2a600c1d0880154006d2849f44a50946892001940188a14782a800e3dcebe0c4007328c892020029ede6e101001424813820800d841d12154a13b53e1904a803114920055001c89fa2c80800d8509123640050934400aa00311422704100173afcb818800ad3b512264005929e8b0aa002e75f76889000ed5aa2456800a12409c154aa3b53e890aa802428b2005500173afa241e800b9d7ddaa74005cebf0b0aa002eb63a105500173afa902a800a5224800f400722beed532002eb5f0a811001424490038800cbc5880154005ce844b202549da9f0a805400ed3190056800d2458be1540073311421fa54a2c922005540173af85422800a123080154005ce844b07a53e2c89200894015ba7bb512800a127d123640050a2cf52fa00357424490100109459002a800de509120f4006c3114207a003415f448550014f8b2489c80092c8912154a92248015032803995ba1225001cdd850912800d5d09120f4002ed18400aa002850269101000aa318a02a8005a224501540057e848c0aa50944892003d69ecb4922480a00e4692e75f4005cebec50aa001da983b90100182a7c5880800a13709c40400509b8c320200361424585500173afbc42a80076af112424005cec615022002e75f5505500173afc160480092485120f4005cebced0aa0022cb549101001a4a12709c8009fa249c0440054dda9f0aa003914a45901001075e22480800e43b4c62840060a8516272002848a2003d001424493826800e65091a40400509124b0aa002b4ed4a055001b05da2c2a800d853db8154005929e8907a0039173afbb5000ac319002a95476a2480095005092c40112002eb5f4485529e9f459002aa0090a24800f400733614f44a54e2c92200554010a83a24809b0a7c4d1215576af112400ca802851e448550014276a709c8005da2496154005cebe1507a00292892005500173ac1382a9424fa2c9c1550022ce6400aa0039999a110100142449382094f76a250e405006ee84890aa509da9f0e86540188911002a800d2509204e40061a84400aa0023cbb448550015276a502a80084a24800f4005ce2cd70aa53dda9f0c8556ab16449003aa00883d512404a1224801b0aa802bf4944855000bb4493820800e6509123f4a12489c1902280284dc6585500173af9142a800c32ec80154005cebf022720030d5fa10550014276a409c800a1224861540050916280aa00361424483d2848b2710036b424fa24960f5a14593e190aacfdda9f44939401a2a7a2480800e6549124040050a664007a002eb4227055001738b2c02a800e62ed123f40050a610244a0039988a1101001afb9d082a800a118c800f4005cebef30aa00284892583500171a7bb480800b9d7dca1540061a84450aa3b512652005540177b24582a800ac2589c404002ed16280aa00360bb4483d001cfa12208094f8b24880185003e8c6400aa5253e892003d4013f8b22080800e450918404a7a7d124007a80399885d9010019976a9c80800e65c684404002ecc64007a0039988afd09284e944a182aa00a1329161540073284db2020038d73a11012849f449381ea007698c52154005ce84410aa00398bc4490100089399001e800c753d12404007316e89202002c7424585500173a81002a800e650912794005cec9160aa002e35f768550015fa5a242a800e46c2848b4005929f16492002848b21055001c8b9d79da800a1259244e4
  | 5, 1 => 0x7329e891fa002e75f6785500186a11382a800b9d7c2a044005091a4007a003115fa505500142892242a800b1509120f40053db8cb0aa0028464200550014293a2496800d850916144006d1768920253dd28942855401a0582242a800d8525120f4a12249c1b0aad0a6a892705540142449242a94f98a4912405006b6848b0aa003614f4483d001424fa2496800a122496354005cebf020620036f4244901001cca122484800c45288a154005362c922025093e8912855401ccc453c80800892ed1215400509248925a509da940c8554014276b4880800a7bb512264002ecc8400aa50a629244939400bc459002a800ccd08800f40041d12400aa57ea8ed44855400ed449489c800a12bd121540050912401b2002eb637685500170a145880800a122cf2154aa3e112400aa8030b42200550014279a2494800449d48015400529124e04a00292924490100106318a02a99676a2480155bd509da190aaf328489200657914276a7c32a00a12247e0f4002ed12401b2003917376ac10014244a009c800d85ce9415400691ea8d2020039175a11010015476a7c9c800a122c9c0940051512400aa002a4892003d00171ae3b42a800afbb5122b400622844007a0039b42449011da9f3993832a00a13d5124b400509da940ea00348ed4e139001424490060800b9d089c134005ce844b0aa5093e8927119401b0a12402a800c42ec800f4003b4c62b0aa002948b27101001c8e3dcebe800a122c80154a123d124b202802e767af855001b4d8d0912800b9c59b415400732848925a00378ed3185500122449382a800c457e840f400735768920250a049f2706540175b9d7c2a800afd291215400509b64007a002e74f200410014a449202a800e6d7e84894005cebef20aa0039173afcb900173a14782a800e4509163f4002f1124007a002e75f76b0d001aba12242a8005ba24800f4005cebea90aa0039973af90100173afbec2a800e4d091640400509127907a001768b20055284a2449002ab4f65a7d121550053db8400aa002e7422704100173af85426800e652512404005cebec10aa0029489228550015fa122c2a800a222c80154007329e89202002848b240550014a812249c94251a2c80155a7c4d12400aa802848d2701129f027aa7d12bcca1279124050050a3c920aa003614f8b249001426e1382a800bad7e94154006aa851649200348ed481390015f562242a94247a249c40500722e75f02200391428922528513449382aa00e65ce843f40050916450aa002bebb4585532aed449382aa00afd3db81540050a048b272002e75f0a841284892590032a00b9d7c4015400732bf4f44a003995ca122500142922241e800bad288a1540050916401120038f70a1101001b0b9d081e9424492c320f50050a26850aa001768b2285500122492248080000509204e30050a04f54aa003910744901000ba449002a800d13d51240400501da89202002848b270b1284ed4f9c02aa00a1224800f4005cecd5f0aa6229ee82005569f16491003ca00b9d8e941540050914450aa00220893b901001d8b9d7c2a800b9d2c8015400509c2400aa0039b3f449010014f459382a9428b2489c1e50065d4c400aa00176892003d001cca129880800d257d4c154bdd3dda700aa802bf424483d00144449001e800a1224900f400722e35c76a0036342458550013f459002a800a1409124a4a122c9c1b0aa803554245901000b5459002a800b9d7e2c0c4006c2848b2720029a89230550015f5da241e800913d5124040057ddaa60aa509d28943855401494492c1e800a7a24960f4005612c4e0aa53dda892f101401c8a122c80800d85d684154002f1124e0220039f4f44901001c8afd2912800b050912154aabb53e890ead09da9f12855401c8d5d0912800e65096089400549d2890aa002a8ed4f85500198a11002a800b9d7dda13400721768b202002e95f768550014f4922c80800005cebe0f3005cebe1502a002e6b62005500173afcb81e800e453db8404005093e8b272003914a44915001c8afd0916800e65727e894d853dd29244a802cb5f44855001a47aa2490800a1241124e4006a6e6b00aa0032f73200551da9f398642aa00e65ce8440400692e75f0aa0028492459390014f9b1002a94276970321550058a92890aa0029e892703d00186a11388094f4fa248a155
  | 5, 2 => 0x4ce424007a0029edc4910100162a12242a800a1495121540072282892020028516539010015fa4a241e8008322450154006aa84890820036149448550014a582242a800afd3d120f4003b4c62b142002e6b0548553614f76a250ea00a145924264005d6844e2025093e170a819401b0c35082a800bad8c2a04400509244e12a002e75f9385500173a51002a800a12c11615400529b8400aa0039973afa25001cdb9d0880800e46a6e75f4a7b89b8400aa803994a44901000ed449b850800a7bb5122b4a146d3e4e0ca8029f164908d001c8a7a2c808005b22c80154005d6be400aa5093e200c8554015f8b2982a800d25ccae404005cebf4a0aa00391424593900173afbd82a800e45cebf024005094c4007a509ca400c855401ccde50912800e66c3114240053deadc20200284902005500142481302a800e66ae848940051d12400aa509f0ed4f85540173a51142a80076a60dc40400592848b0aa00284893690100173afc3c2a800d7d091215476a24cc4e0aa80176902005529ea0459002aa00a7c75244040053ddab144a002ef5f8b0550015fa12402a94274a243215500732848a202002e75f76839001a29522480800b9d7cac15400665da280aa00244892003d00173b19002a800b253db8154a1281164e0aa8029f1649101001428ea489c93f76a751240500529164e0aa002848925825001ccb253d12800a6a2c80154005cebeed2ba0016e892005500142582241e800b9d7e3a1540073242892020038d4244901001c3a1224808008b18c501540050912410aa002851649139001ccb9d7c2a800a322c801540050912440aa002beed4c13900173afc582a800b9d8ebe154006c244890aa0038f425390129f16491002ea00afd3e2c924005ce844007a002e75a8b05500173afbcc1880076ac14c15400459769227200399094490100133923b42a800b9d7c2c1540051d124006a002851649119001a176a249c800b9aec800f40036512400aa50946190a81140188a11001a954a13b53e155005cebee90aa002e75fa103d28534200642ab4298a243215500509d2890ea001f46314055001b0a13702a9424492c32155005ceb0400aa002e74281129001ccd850912800e5d09124e400722e74a2020036988a1101001424494c9c800afbd5daa6400509166e2020038f5f53055001a4b9ac02a800e6508c6404a1289124b20280284ed4f8cd00173afbb428800ad459122640054a2c9f0aa00399b05da2529edc4f9002aa00c450a241540053d18400aa50944892583d401428122496800a5234801540057e5ca60aa0027f15449013994f4fa2480a00e62ecc640400509164e202002e75f2885500123449001e94276a7c3215500519124007a002e6ed58055001c7b9d7c26800e450920404a7bb52e89202f32849f44939401cc449cc80800bad08801540050922400aa0038f77af8552ab16449002aa0090a2496404006220e400aa0028489258b100188a11006c800afa982a044002ed164e202002e75f988550014f6e30c808ed5da7c32155006c29e8b0aa002853144875001214492c1e800a52249c45400509122b022001da983c855001a4b9d902a800a7bed124e4a128d164e202803554245855000ed341002a800d45cebe154005d576400aa50a369f0c855401738b35880800a4a2496154003d5da63142509f09f0c8554014f4492c2a800bad7e84154a7ba52489202802bf4248855001c7a12489c800a122c8031400726848922a002848b27115000bb448ac08800b9d7deaed40071ee75f0aa0039942448a10012e318a02a800bb50880154007216e89202509d292449394014f6aa4880800a532d121540051112450aa0038f73ad0550014f8f2242a800bad088a15400732e75f76a0028489200350016a449842a800a5a3080154005cebf2e0aa002e15f76a2500142458fc2a800e6722e75f40057e04e00aa002848920085001c8a122488800e45cebf16400737114220200361424492d001cc5da245095576a4912405003b512720aa53dda923810140149449382a942449003a1b50061a9e400aa00369424490100152459002a8005da24800d40018c5015022002c9428b249001ccd84fd12800c9d0912404006a6e75f062002e75f76b19001ada52242a800afd09120d4a145924400ea803994265225001cca12608094f9aa2480155
  | 5, 3 => 0x555da92449394014f76a609c800a14593e1d4a7b8d12400aa802c5494483d0014f892242a94f492248a40500722848925a002448920055284924491880b428b2489c1d5004ce5d240aa002848922851284e3449382aa00a1224500f4006a6bea60aa002e75f0a819001c8a147912800b9d7dda0f4007336173a125522c8920055401c8a4a2480800e64fd123f4004fdda8921200176891403d29f164f85c2aa00b9d289c40400509b8400aa003614a45855001a0812242a800c450896404007230d4220200349024a055001074489c2a800e6509124040057e04a60aa002e75f9a0550014fa0a248080083a249c154006f1da893726c28513490554014f8b2244c800afbb54c0c400622844b07a00284ca4483d001424c1001e800e66227e404a13d5da9f0ca802c94244841001737abb560800e3dcd601540037176400aa0039d73afbb50015f5b2242a800a1459cc4040050512400aa002bf426e055001cc5da248093f76a24801950053d127e20250a5c9f0c85540142813a912800b9d7dde154005ce5cb00aa003995fa1225001cca2224809427697c3215500622924007a00284892103d001cca122490800a12409c40400732e33f202003114f2003d00173afca9da8005b2248a1540050a24890a2002e75f79bb5001428b2484a800bad7d16154005cebe4f0aa002848b20075001a9b9d7c2a800c35288015400732bebb44a0034973af831284a24492c2aa00e648112404a127c32150228029e8b20055001735805408800bc5cebe15400692be89112002eb5f76855000893993808800a1281164e400408c6280aa50912400c83d401bcccbb42a80083a4912404005091e8925a002e75f973d500142459382a800b9d08800d4005cebf020aa002e770afbb500173afbb4189424590036155000039973af9bb51267200554015fa6a242a94f81224ae4056ca7d12400aa802bf4f45855001c8b8d7dda80090a2496154005251e892020036973a1101001b0a12302a8005da2c9c1540053db84e0aa0029e8f449010015fa7a2422800afbb54e89400509da8d25253e2cf54f901401584b1002a800a7a24800b4007329e89272509468b27055401b0d5d0912800a7a2c8a15400722448920200284892590127eed4f22480a00a122c8c154bed09da190aa802d55f4485500173a14482a800cf509124e4005cec6ed0aa00294a620055001424492c1e800b9ad08015400733634244a003993f449012c94f76a48e0a006e2d480154a7bb546190aa803a973af85500163a522c2a8005da2496404005cebe4007a00398b54490100173ac1388080084224801540050a24920aa509ca401e055401077aa2480800a122c80144002ed124b07a002a5024f8552aaed4fa242aa00a4a24800f4b9d7ea8ed0aa80391426e10129eed4f9c02ab5476a7c32155003b51282272002e742200d9284924593880a00a12609c0440053d124007a003995f9fa2500173a13cc949428b27c3a15500732bd4244a0029ee120055001429b1002a800d8485120f4
  | 6, 0 => 0x3b576891585540000a147912154003b5768b200554014f76b7080155006ba84ed44855401428b2c1121550062284ef2005540199a14088015500002928920055001bc76aed12155006c7554276a25401499722480155006c310ed5d85540173a13b4ae40500529da8922855401427ea249c1550050a62890b8554015fa13b5161550064a84ed44901400e55da2480155005ce851d200554014280a2480155007329eed4490140142812248031500692428920055401b0d3bb512155a13b53e8921055801c8a7bb5124e50053e5c89200554012490bb51215500733914f4490140188a14a9da4050050a2c891308d401c7a12249c15500002848927041001c7a12247c1550073284f5449014015f76a2450155c453dda9f200558015fa1395121550075284892710140173a13b49c155005ce84ed1f0554014297224ae405006c284ed6d855401c8a7c591240500549da9f44855401ccb9d0880155005cec95f76855401a4c43d5da405007228501448fd4014276b29124e50050916400f055401b076af11215500509daca61a2540000c350880154a1459ea89271018014276a609c40500509da8a2005540173a145880155007231142729014015fa7bd5da89500509f69820055401a9c4508801550050a5c8927055401b0974851215500723634276a254015676a249c15500733914244939401c89fbb5124050053e8516491014014f6aa248015500509da8b22855401427abb4b2405005cebe400a8117114276a7c9c156004ce5d212005540173afd3dda15500621da73200554014289224801550050912400e811401c8a13c51240500732851644901401428ea4880155005ce84f320031401c8a1459124e500509dab144855401c8a12a912405003b578632005540187a13b480155005929eed44855401568b2248015500693112e2005540142813d5121f50050a6a892005540000e6509123f40050a088920055401a4a1224800f50069e54ed44901401c876ad512405005cddabb270554012176a24801550057e9f2e448554014246224801550053d9e8920055401a484a24801550053d12400a811401424b22480155003b5768a200554014276a249c425005ce2cbb20055401428b248801550054a0489200554014274a250a155004b976892705540173a11002c1550050912401c85540173a13b480345a7bb5127020055801427cbb51240500622852e7a90140150a12248015500509dc8a200556a8ed44900321560053d96c144855401427aba5124050057e84ed4505540173afd0a2c15500511da8a200554014294a24801550062285022005540000d8509120f4006c284890a815401b0a14b9120f5006a7115fa10554015f76a60801550072176aa44901401999e3b4801550061a84400a811401c8afcfdda8950059285164485540173a13a4801550050a04892d90140188a7bb4801250062284ed2003140142449382a04500509da9b27055401a476a2480145000039988a110128516449003a156006229ec1200554014276a24f840500722bd4276a2540142449002a06500732848944101401c8b43b51240500509da892003d4014276b6912155006c2850244851401b0d2509121550050a088924055401165da48801550062298ed200554014276a6080315a13b53e170a805801c8a1224800f5006228516271014010976a2480155005b20489200554015fa7a242a0450062284ed1405540188a13b49c1250050a34982005568516491002e1560069e5cf5449014015fa1459241550062204bb20055401caa13b51040500509eaed53101400ed449e4e61550050a2c89200996851651a4880156006c2848b44855401c7a1298801550050a4e892710140180a13b48015500692846320055400bb449382a045c4509da401e05580173a13b4801450070284892710140188afd0a041550069e32ed4490140142449002a07500685da89200554014276a589c405002ed12400a8194016a44958801550050a04db200554014244938802550062684ed200494014d8b22480155003b576892003d401b0d22ed12155a128d124e0a811801429a22480155004097889200554014297224801450050a5ca620055684892005c2a0660057e84890a8194014f449142a04500519da89270554018876aec50155a14d1124e200558015fa13b5120f5006c284ed448556852e492249c4060050a3089200554014281224f21550072e8489200554014299bb4801550051a2c8920055401a45d98c8015500561da8920055401c8b9d7dda895005ce845120055401cea13b512405005091253200556c94f76a491240600753114220055401c8a53b51240500509da632005540188a1138401550052a848927101401c8a12248a4050050912400f03d400ed5e224501550071ee7422004d401427b2249c405003b51251200554014276b351215500509da893085540188a13b594155004d176892005540163a52242a0450050a0aed2c901401c9d8509da89500509de8920055401c7bbd0880155006c2df427685540164a13b52489500692848941855401b076aed121550057e8534448554014298bd512405
  | 6, 1 => 0x6229ef5769014014676a24800c5005ce84ed21055401b6a13b512405002ed12280a811401aaa13b512405a1459da9f27055801c8a122d124050050a688927101401b3a13b50a155003b56a892005540173afbb580155003b5125020055401c89fbb5123f5a7bb546892705580142769649c15500723614297225401b0a13b5124e5006c284ed61a25401429722484155007267eed4490169f16449002e156007336142449014018872aec801550057e9f1644855401b0a13ed12155005ce84ed200cd40149a1224800f50072348bb4490140188a7cb88015500561da8927101401b176aed1215500509dad6449014014f74a24801550053e84892003d40188afd09ca155003c576892005540142652242a045003b5128220055401b0a13b51a15500692849f44939401165da249c15500509cce544901401424c1002a04500723495fa12254015fa131512155002ed548920055401427698c9c4050041604bb44901401c8a13b5124050057e7eed44855401428c234801550041dda8920055401b0a130512155006a9dabb44901400ed449449c40500509dacd61a254015fa13c51215500509da89200d94014244930801550058e84890a8114014297a24800f50057e84aa448554014278a24901550059a4289200554015fa14160489500509de89271014014293bd5124050057a84ed4485540188a14b89c1550069284924493940177afbb512155a13d5da8920065801c8c44fdda40500509d289270554016876a2480155006c1dabb449394015f76ad5121550063e84e52005540173a149c80155003b5728920055401428b2248c155b9d09da400c85580142449002a0f500622c94f76855401ccb9d091240500692e75f44855401c8d14fd12405005092c4e20081401c8d850912045a12491256271018018890bb4801550050912420a811400ed5d98c9c40500721dabb449014014f76a491240500002848c200552852e449003215600691ec8920055400ed449d880155006229e400a8114016b76a24ae405a13b53e400c855a9eed492249c4060072284ee449014016d76a248015500509da9f449394015f5daa91215500722bf4276a25401a9a12249c40500555da8920055401c8a23b51240500732849f44901401b0ccd09da155a7b053e89200558017376ac08015576a7d127420055801c8a13b512485e4509daa344901801c8b8cfdda405006c284890a8414014281224dc4050072284ed4497d684ed44a1880156bf509da89200558014a45a2480155006c28489100554014274a242e15500722851b44901400ed449cc9c40500519da892002540166a1224800f500509da89270514014276a989c15500509da89200f5400ed4498c50155006c284ed448c5400bb449002a0f5005611240100554014276a49124e5006925c892710140168afbb51215500732849244901401427b3d51240500622844e0a811401428b224801450050a2ca6200554018da122480155005a1da892f8554015fa12242a0f5005ce954220055401a4a122c80155005ce84f620055401c7b9d089c4050062284400a81940158a12249c15500722e7428110140173afbb5121550062284ed2003d4016976a2480155d8509da8943855801bcd250912155a1459248927101801c8a13b512455006c34988a1055400ed5da7d124e5a7bb524892005d801c8afbb5768950057e9eed492254014a76a2480155005ce8516118554018884bb4801550050912452005569eed51a491240600509125127055401cda13b512405a122480190a8118014276a24940c576a8d12762005580142812249c40500519da8921055401bc76a24d21550050a04c34490140173a14b89c4050073791424490140173afbb560155003b576924493940000d850916154003b5708920055401428da7d124e500691da89200754014f98a2480155c1509da8927101801b0b35091215500692e74f200554014f61b05124050050a74892005540142812348015500409b08920055401c8a142d124050050a2cd7448554014276a34800c5006c294890a811401b0a93b512155006228534200554014276a245615500509da8b200554014274a24801450053ddab0448554014279a2480155005cebef576901401428b24846155002ed124520055401c8a122c8015500002848925855001c7b9d7c80155a127d124e100558014297224961550050a208920055401a476a249c1050050a628927055401bca13b51215500409768927101401b0c4509da1550059912512005540177a145880155006fe84ed449014014272a248015500691da892b9014015fa53b51215500692e74227055401b0a7c09121550057e84892285540173a13b4801d5000039173afbb5284e544938801560057e85024493940175a53b480155005ce84ed20039401a4a122880155a140946892710180173a1158801550000242892003d00173afcb880155004ba42892003d4014276a24f879500691da89270554014f7abb51240500691da891f05540173a113880045005092689200554014297224801d50053df88920055401b0a122c2a04500621da51200554014293c1512405
  | 6, 2 => 0x57e84ed4485540142449384a155005092489270814014476a24801550050916892285568516449003215600509968920055401a476a24800c500722948920011401c8a93b51240500509da8924055684ed51a2480156a14b93e892705580142319002a045005c67eed200554014276a24be155e44fdda9f4490180178b9d088015500509daae44855401a4a1224802250050a3689200554012e449cc80155005d684ed20055401c876aed123f50056a84ed4485540188a1399ca40500672848920055401a676a2480155a13b5125f27055801caa13b5124e50062176aa20055401c8c4509da40500509f089200554014f7b22480155007339542449016c94f76a7d121560050a008920055401c976aed12405007229f0244901401427abb52a40500509127e2005540142813d512405006c176890a81140173a14b9ea40500691da891405540173a1408801550053e2c8911855401a074a248015500726bf4276a2540188b43b480155006a6e75fa105540173b8509da4050071e848920031401c8d150912405003b512662005569e9f449002a04600509da8922855400ee5da24801550053deac1449014014f76a24f41550057ddabb44855684ed4fa249c426005ce84ed200314014286224801550062284400a83d401c8a122c800450052a848927055400bc5522480155003b57689240555dabb51a2480156002ecc6400a811401427b2249c1550066a84ed44855401cca140912405003b576892f85540000e65ce844040046d76892005540000d25cebe154006c28ced448554014da122480155a13b53e890e8558015fa13b91215500509da92449094012076a24801550053db8c120055401447722480155006f2beed448554014fa122c801550057e88ed44855401cda122480155006c2850576a25401c8c43b576405006229eed49101401427abb51228500722e3427690140173afbb59c1550050a5c892003140142642248015500539da89200514015fa146d1215500509da8920089401c8d3bb51240500409eabb44901401ada122480155a127d124e0a81180173a14589c4050050a691d2005540188a13b53e4e5005ce84ed1405540089399002a04500509408b20055401c8c457e84ed50067e8489200554014273a2480155006c285144485540173812ec801550050a2289200556849f449002a0660066684e5200554014276a9d124050050a1689200554015fa1409ea8950072284ed6d90140000a522c80154003b57689228554014f76a64801550062284ed200f5401c7b9d7dda15500509488920055400007698c50154005cddabb200314014677a248015500721dabc4490140173afd0a041550062284ed491394014297224501550053dda8920075401cde4d091240500509da893115d401b0d0509121550070a84ed44901401c89748512405006371142200554012176a249c405005cebf4276831401429a45880155005aa848920055400f576aed122850053d125620055401c8a13b51279500509da892003540188b9d7dda155003b5768920089401cca1224802c500002e75f76855001424b2249c4050072284ed4488d40173afcb9da15500691da9820055401b4d5509124050050a3d1d44855401428b2489c405005cddabb1405540142449002a115005929ec1448556849f449002a0760050912572b10140173afbb49c15500509124e200e540188a53b4801550057e84ed4488940188a111480155006c74942448554014276a249c1d50042d7689200554014276a2494405005cebeed0a80140188a14089c4050050a0c63200554014f76a24ae405005cebf1620055684ed44a10801560053e3a89200554012e5da2450155005091256270554015fa142d121550050a2c89200754014282bb53e89500752e74220055401427abb594895006ab49424490140173afbb42a015005cdda893c855401428f4591215500509eaed4c10140173a1138401550053dda89138556fb4f76a24801560053e7eed44901401b4a13b512405a14091257200558014a459002a04500509124e200194014f76a249c155005ce84ed65055401a6a322480155005ce7ced20055401bea13b512155007329e8920055401c8a1224800550072361a476a2540142448a02a045006c3494244939401a476a248415500509da892b9394014f8b224801550050a3a89270554010976a249c405006c284ed4a05540173afbb42e155006c284ed449b9401429732912155a7c59da9f200558014247a24801550050a02891f855401bcc4509da155004197663200554014297260801550057e84890a8454019ea122480155bed09da892705580173afbb42a0450062284e5200554014276b3112155a1459ea9f20055801cca14fd124050050a24ed448554015f76a9912155007234942449014014262a2480155006c684ed4485540142449002a0b5007328489270554013f76a248015500509dadd200557114272938801560051a048920055401427abb51242500509e28920055401428b2249c1550050a2c891f0554015f76afd1215500509548920055401c8d85ce84ed50069310ed270554014282c0912405
  | 6, 3 => 0x6c2848928855401428b3b53e4e500722b74276a25401b076aed12145005cebef576855400bb459002a045005929f2e4485540199769005815500509548927101400ed5e22480155a127d12400a83d801a4a12248013500691da892003d40188a1409ea405004ba4289200554014a449142a045004fdda89200054015fa122c2a04500665daa620055401428b2245015500509e28d20055401428b3b5244e500509da893c85569eed4fa491240600509ea89270114014276a24461550062284ed2285540142449002a0d500509daa30c85540188afbb576155005ce844e0a8114017376a24dc40500509da8926855401428132512405005cebf1676855400ed6daec80155003056a89200554018ea122480155003b5127720055401d4a7a248015500429da892005540173a11002a065006c28531448554014f44938401550050914400a811400bb552249c40500425eaed4490140173a13b4800f5005095a8920055401b0d25ce84155a13b53e92449398015fa13b5b61550072284fb449014014f76b29121550054dda892005540188a13b480225007227e89200114014f76a60801550050916450a811401429340912405004597689140554015f76af1121550069e04f54490140188a139c80155003b576893c85540188a1224800f500509da892004d4016876a249c4050000284892003d001b4a122480155005929e890a81140142449002a0550072284ed469014014297224800f5003b576891185540188a142c801550050a448920055401b0d23b512155007528489270557614f76a250a1560072284c1449014014244938800f50048512400a8114012e84a2480155b253dda893805580142449001e00500509da98270554014b812248015500509dadf2005540142491002a06500732848920025401a47698c80155002ed5a89200554014281224801450050a04a620055401a4a122480155005ce853420055401428b32912155006aa848920081401c8d853dda89500692848926055400ed449d89c405a13b5126220055801b0a13d5da8950050a2c982005540142449001e0150053dda892105540142923b512155a13b53e4e20065801c7d850912155a12491245200558014298c9d1215500509daa620031401428b3948015500691de8920055401b0b9d09da155a1409248927101801cca1224d24050000176892003d001c8d5509da895002ed12400a815401427d22450155004b976892003d401b0a12249c205005091689200554014f60a4912405007234942448fd4013f76a247e15500561124e20081401427abb4c64050050912400b83d6848b449388015600002bf424483d001a4953b5124050050a62891a8554015fa12242a0550053e0e8920055401ceb9d09da405005096c8920055401ccd8509da8950057e852e4483d40142449002a035005cebeed37855400f576a24a2405006c2852e44855401b0ab3b5121550073391b0a1225401c9d2509124050072333427690140142449001e0450050a672e20055401c8a1224801050072284892008140188a7bb49c155006917689200554017ab9d7dda1550072361428b22540109449002a045006c1eaed5da25684ed449003a1960057e84ed6f855401428b2248415500509dad04490140173a13bc8015500509dacd65225401a9a12c1121550065e8489200554014a76a249c4050050a5c632005540188a7c588015500692bf4244855401b0b9bb576155006928889200554014276a248015500509124e22901400fa5da245015500509da8926055401a4a122490155a7bd5da9f449018012e44944801550050a22893c855400bb45a2480155a12249c400c811801a4a1224be1550050a16893c8554014276b80801550053db889200554014260224800f500509dad3448554014276a24f8155005ce852a769014014f93a2480155003d5dabb3190140199b9bb4801550050912401b05569eed449003215600691da8941855401c8d262284405005ce84f376901401b1c4509da1550062e84ed1d85540000afbb54c154006227eed200554014d449002a0650057e848b44855401b0972ed121550052982892005540161a13b5121550072284ed448fd4014276a24c01550062284f12005569f4276a8d12406005d6848b2005540188a14589c155005ce2cd42005540188a12a8801550050a5d2a4490140188a141604405a7cb93e8920055a84f576a7d124e6006ab114276901401c9a13b512405003d5da893990140000e450916404006a6e74220055400ed449e45815500509de9220055401424fa249c2050068a7e89200554016fa13b480155006928489228554018876ad480155006c284890a8114014276a2c9c4050050a2c8913055401cca12ed12405004b9766320055401a4afaed1215500692e7422003169eed4497c801560072a9eed44901400ed5da2480155006925cf544901401c8b350912405007028489270554014276bad124050050a04b044855401b0c4509da4e500509ec89200754014276a589c15500723614274a2540142813b52815500509dad1449014014272a249c40500509dc892005540189a145880155
  | 6, 4 => 0x57e84fb4485540188a13b49a155005cebef576a254014276a7080155006aa84ed44855401427ba248015500722848920011401b0a147512155003b5768d200554014276a24be4e50071ee75f44855401428da249c405005a5eaed44901401429a2249c1550050912612b05540149a12248015500305768920055401a4a12247e1550053dda63200554014a7abb5124050050a5c92449394014276a508022500509da8921025400ed5e22480085e2509da8920055801427c2249c40500569da89200554015fa13b51a155005cec8ed448554014276a34901550073361424485540173a53b4801550057e84c14485540199a13b4801550050912460a819401a476a2c80155005ce8445200554014f77a2480155005cddabd2005540142449002a10500561da892705540164a7bb5248950050912401005540142449302a1050061284ed200554014285a24dc405005ce84ed250314011b6c22480155005cebf2e44855401425022480155005ce8502271014014276a2480315006c285164485540000c4508800f40062284400a815401bcd23b51215500622852e2003d401b0d2621da155005cebeed4f855400ed5da245628500727554276a25401428d2248015500509da8940901401a9b9d7c8015500509da63270554014a972248015500509da9f448754014f953b51240500692849020055401aa76aed1215500721768920011400ed449449c1550053d24892001140000e6d091240400692a489200554014277a249c1550050a2c632005540173afbb524155005093e8927011401d5e45091240500722bf4244811684ed44a1c80156003b5126e200b1401a4c4508801550050a630244855401bca13d5da895006c311427abb54019976aec80155006928489200e940173a13cc8015500509da891f855684ed492249c1d6002ed12400a841400bb4490040155007228ced44901401bcb9d09da155003b57689200c569eed4fa249c156006c22cbb4485540142492249c04500732852a449014014285a249c405005ce84e52005540199afd09da155005092c4e1005540188a122c80155a13b512400c82580000a122c801540050a5c8b200554015fa12242a105003b57663270554015fa12244015500509248920019401b0d250912145007479942449014011076a2480155a7c593e8920055a84a3449004015600509164e2005540166a122480155003b56489200554019772a2480155006f2852e44855401b0c450a5c155005cebf022005540173afa242a04500509dacb4485540000afd2912154006c284e94485540142459002a005004597663200554014281224801d500722848922811401a48b3d51240500509da9020055401d8a122480155005cebeed20031401a4c42ec801550072684ed448fd4014281a24801550052912400a8114015276a24801550050a2c8912855400ed449cc9c1559fbb53e8920055801a476a2880155003b576891f855401b0d3bd5da8950050916400a80540197c45088015500509da8912055401a4972249c1550053e5cf5449014013190a248015500693115fa105540188a13b480155a14593e8927055a9eed4fa242e15600459127320055684ed2a100321560053e0489200554014276a24803a500509124510055400005da2c801540069284db20055401c8a145512405006a6bf4f44855684ed449083215600509da892d90140000a7b70801540073284892a101401428fa24801550071ee7422705540142449ac8015576ad53e8920055801c7b9d087c155d853dda92449018014f8cbb51240500509da89200dd401665da24801550050a04892b90140000a52248a1540050916400b85540109449448015500002bf42458552a4ed449002a0160068a848920055401b074aed1215500003994f44901001427abb51440500509da9f0c055401c8c4509da3f5006c284eb74a257554276a4912406006c284ed44851401b0a13b54c1550050916400a81140166afd0912155004ba492144855401b3a13b5124e5005091240110814015fa7bb5120a50069284893c85540163a55091215500727114276901401a4a122446155005b1da892005540173a14b89c1550053ddabc44901401bca12242a045006c311420a811401d8afd0912155d8509da92449398014f76a2450155006b684ed4485540164a7bd5da8950057e94890a8114015fa93b51215500621dabb200554017da13b5124e5005c684ed200554014ba1224801550057dda89270b1401a776a24801550050a5c8a2005540175a51002a0450069204890f0554014f60a249c15500485eaed4490140188a13949c4050050a62892003d40188a13b880155006b284ed4485540188afd09da15500509808b2005540188a23b4801550050a2c89200314014262a249c405006c684ed44939401c89fcb9124050053e2ced49101401424492c800f500002848b228550013f76a249c40500509dae64490140188a13b490155c4509daa3200558015fa7c09121550062284ed2f8554014276b6c80155a145924400c055801a4a7a248009500622851b20055401c8a13b5284050050a0459200554014278a249c405
  | 6, 5 => 0xa9bb5248920055800ed5e2249c40500509f2f6449014014276a24e240500509de8921055401b0d03b5121550050a2c8b200554012e90a249c40500509ca892705540161a33b512155a13b53e8927025801428a22480155005a9da89200554014249224800f50050912450a81140188a11002a105003b530732005540173a13b4944050000284892003500188a1100401550057d76890a81140173afbb46415500509da893c939401bca1459121550050a04892701140000b9d7e5c1540062284ed200c5401429cbb512405006c311428b055401c8a1224a240500409768914055400ed5e22480015002ed56aa449014015976a24802250053deaed44939401b1d23b51215500682848920055401b0a149d12155d8509da890c8558010576aed1240500509124011011401428aa2480155b2509da9244901801428322480155006928494200554015fa33b5121550053e2cf544901401a4a1224dc40500691548920055401aad23b51240500521da89200554014f76a2880155005ce9f162005540000da50912404002ed12450a81140188a13b47e1550050a04ca448554014f972249c15500509eaed6622540173afbb4581550050a049820055401b1a13d5da8950057e84ed449c54013f7abb51240500509eaed6e901401b4a12249c40500509124e200154014276a249640500722853144901401b0d23b5124e5006c284ed75225401428ba2880155005cebeed53055401c8d25ce84405006c6e74276855684ed449004a15600509c6892005540142449385804500622cd422005540197c439480155005ce84f12005540173a14589c15500509da892583d40000b9d7c2a044006f284e944855401065da2480155003d5dab54490140173a12a880155006c311427485540173a1416044050050a687d200554014276a24c4405003d5da8928101401cc9fbb5124050072284ed5822540000a1449121540072348ed44901401aab9d09da405007227eed44939401b1a14b912155005bad0ed44855401a4a12249c405004fe5c89200554015476a24801550050a6eed2005540188a51002a04500622a4ed20055401a5a12248015500733913f449014015276a243c155006c2954244855401428b22880155b257e84ed492258014f8b2488015500569da8911855401b0a13d9121550073f9142449014014276a5080155a14591240110558014276a24dc405007236142812254015ba13b512155007227f1644901401428122484155006c2e742769397194276a2480156006aa852e449016851676a8c80156005091689271014014276a24f86e500692848d20055401428b3b4be155006229f02200554012176a249c155004b96a8920055684ed4fa243215600722b93f76a2540164a7c59121550050a5a8920055401424497480155007238f42449014014f449382a045005cddab044855401424b2249c155006c2852e4493940167a122480155006d3554244855401218b224801550050a2c9227055401735daa88015500722e742769014014976a24800f5006f684ed448554014f449002a06500509124e1c855401bca13b512145006c3114276851401a45da249c405bdd3dda892005580164a131512155005d684892005540142813a512155005a1eaed449014014f76a24800f500509da8925055400ed5da508015500691da9f44939400ed5da24dc405005dee75f76855401427aa24800f500509e48920055401c8a14b912405000020e89200550014276a249c40500509da893117d401c8ab3b51240500509dac344901401a5a22248015500509528920055401424490034155005dec8ed44855401a4a12708015500509f68920055401aad250912155006c684890a81140000a1224803640050a2c9f0b8554013f449002a0450069f10ed200554014297224803650057e84ed4a05540173a11002a0f50057e84ed449b94016476ad512155e4509da9d44901a9eed492248018600509124e0a819401a476a49124e5004fdda8944101401424493880365005e684ed200554016897224801550062284ed73101401b0b9d7dda1550060a8516200554014276a3480155a7c09da9244901801cca1224800f500722e6ed5d901685024490032156006aa848920011401b0a13b5121d50050a048c2005540142449002a13500693334220055400ed6c2248015500509828920055400b5449002a04500425da89270554018876af080155a128d125d2005580167afd09121550050a2c892003d401428b36912155006928489200c540173a13b53e4e50053e688920055401c8b9d7e84ed5006c284892b055401889748480155006c2848927011401a4a122502405007225cbb449014011684a24801550053e5c9244901400ed5da249c405006a1ec8920055401c8b2509da895003b586bb449014014290a24800f50062284ed3c855400fb5da2480155006c29eed448554014f76a7d244050053e84892004140188a13b4461550050a5c9f4493940173a13b5244e500509da89158a140142772249c4050057e84f244855401c8afd0a5c8950057e84ed61a254015fa12a512155006c284ed4495d401ccafd0912405
  | 6, 6 => 0x5093e8b200554014276a9d4c405007229eed449014015c9fbb512155003b56c892005540000e66c28489400509eaed44901401b0a7b0512155005ce84ed68101401c8d1bb512405006aa8516449014015fa14c512155005094ca420055401c7a122480155006c285134485540173afbb42a09500509f88920055401428118c801550072748ed4490169eed4497080156004596a89200557914276a79124060066684ed27101401a4b9d7e841550050920892005540173a13b48015500509dadc20055401c8a14751240500509124e20041400ed5dac11215500509124e20081401a4b25091215500509248b2005540149449002a0f50050a0b022c901401b0a1459124e5005ce84ed69855401427da24803150074a848920055401a477224801550065dda89200555da9f449cc9c1560053dda9235101401424493812045006f1dab044855401427abb512605005cebeed34855401cca13b5124050053d12400a83d401b0812ed12155002ed548927055401d4a1224800f50072284ed449394016876a24ae4050050a2cd6449014014297224801550053d24892b1014015576a24801d500691da89240554015676a2480155007339142449017614274a491215600691da892f855401c8b9d09da3f500509125a20055684ed449709c1560050a5502449014014aa122c80155006ea84ed4485569f024fa2480156a93b5248920055a84ed4ea248015600722851644901401427698c50155003d5dabb44901401c8d2621da40500726e742769014016876a249c15500693114227101401c75da2480155006c684e944855401025d98c80155006c2e7420a811401a4813d512405005cddabb200554014276a249c38500722852e448fd401427abb91240500722bf4f76a25401c8ae509da89500509da89270fd40142449382a0f50062284ed371014015fa13d5da895002ed124e20081401447abb512405007328489200fd4014249224ac4e50071ebf4244855401427abb51248500509aa892005540173a13b5a2405c662284ed20055801427abb5125f5005ce84ee20055401c9a14b912405005cebf4276855401a476a248a15500002848b2710100173a23b48015500731dabb44901685024fa249c156005ce84ed24055401c876aed124e500509da9f0c8554014f76a49124e5004b976892005540102449cc80155005ce84ed2f85540164a13b5121550073390bb4490140173a146c8015500509124017055401aaa1224401550059a848927101400ed449d89c15500002e6ed580550014276b1912405a13b53e4e0c855801ccafd09da89500565da8920055401b0a13a5124e5007222cbb449014015fa14b9121550053e2c9244901400ed5d98c50155005125c8920055401d4d85091215500733915fa122540173a140080155005099e8920055401429722490155a14b94689200558014a449388004500549da892710140173a1409ea405006c284892003d401a476a24802250050a5c892f85540142449002a04500002eb4220055001428b27d124e500509da9b20055401b1a13b51214500722bf428b225684ed49138321560057deaed5da25401584493840155006c284ed4c055401c8c450a5c4050053d124520055401c7b9d08800c5a13b512702005580188a13b49c405006928c892005540188a13b5864050072284e94490140173a13b48a155005091246200555dabc4fa24801560050996c14485540188a13ec801550073284892007940173afbb57615500692be890f055401207abb5124050060a9eed44901401428b249124e500509da89200994019ba13b51240500591dabb44855401c8a12247e0450050a369220055401a9b9d7dda1550072344ed4490140142972248a1550050a6489200554014276a249c3b5003b56a92449014014281224800c5007268489200114015f972ed121550053e748920055401424595880155005ce852e2003140188a13048015500529da892705540173a13b48022500509164e2001140173afc59121550057e84ed63225400bb449002a0450050a16f54490168489270642a04600535da89200557174f76a24801560050912450a801401cde650912405003b51277399014014f76a2c801550060a84ed449395da9f449dc80156005ce84892003d4014a8b224801550073284ec449014014276a24f26e5005ce84ed5390140173a142c8015500621dabb271014014276a5046155007568489200554015fa12242a04500509ea8b2005540144449002a0450050a5c8920089401bca7bb512155005ce84a420055401b0c453dda15500559da892008940142449202a045005de9f1620055684a3449002a0460050a0489140554012376a24801550072284ed531014014f72a2480155005d684400a8116bf4276a24e01560050956aa44901401b0a73b51215500519da8920055401427822480155a13b51a8927101801b5a13a512155006ab11427685540000b9d7deaed4007231142200114014276b6c9c40500509dadb61901401424fa24800f5000038f73af8550014282bb5124050050912401a83d4014276a2c9c1550050920400a84140173afc09da155
  | 6, 7 => 0x733934244901401d8b9d08801550050912692003d4015fa1475121550050a68892003d401427abb512245005ce94400a81140173a93b480155003b576892705540199a11002a045006c348ed44851401c8c453dda40500509da892f95d40188a13d5da40500731768920055401b0a12242a06500726851644901401c7c4508801550053e04f544901401424490062045006c284ed4483d40000a12408015400509124e22811401165da248015500511da892705540188a11388020500732bf42448554015297224801550050912400b0554014276a2480345006c212ed448554014276b35124050053dda89228554015276a7c8015500509dac944901401a4a1224801450069284a62005540197c43b4801550057e8516448554014276a248c1550053e188920055401ccc4509da405005122c892005540163afd091215500723114276939401427c2249c1550050a2c892405540188a14b880155a145946892005580142459005815500622aced20055401cce46228440500509d28920055401d4a522480155006c2e742768514015aa14591215500425da6320055401c8c450a2c4050050a5c89200dd401887abb57640500509123f0a81140142933b5124050053d9089200554014f76a248022500689da8920055401a77abb512405005cebf5276855401c8a149d12405006c285344485540188afd09eaed5006c2852e44851401428122880155e4509da8920065801a476a24f215500509f489200554014f85a24801550058e94ed44855401a476a244615500509eaed6d901401428b2248a155007227f02449014015f8b2ed12155005ce85162003140188972ec801550052dda8920055400f576af11240500622c94276855401429422480155003a5768920055401d4a122c80155005cebeed0a829401a797224801550050976892003d40173afbb4a8155a145924400f05580152449002a04500509d6e9449014014276a248014500509daa6200554012e90bd512405005adda8920055401427f3b51240500622bf42970554014f76a249c2c5000029f16491010015fa13a512155004860489200554015476a249c4050050a2c8920089401427abb5127950050a168927055401b0a13b4c61550050a5cdb2005540188a11002a04500509eaed4488d684ed492249c4060071e848911855401b076a24a215500509da9427101401bc9f3b51215500509da891485540173a13b4f215500691ea89200254012e5e22480155005ce84ed1185540158a122480155003e9768920055401a476a2480135006c284ef44855401a497224800f500429eaed449016f564a13b5121560072295424490140000a1459244e4005cebeed0a831401428127c2e15500509125d27101401c8a13d9124050050a5c893c855401b0a1224280450050a5c89118556bf4f76a491240600509125120055401b0a14a9da895003b5768920051400ed5da9880155d853dda9f4485580188a13b49c3b500509daab44901401a4a12c112155005ce9eed2002540000b9d7e2c154006c1dabb31855401c8a145912235006b684890a811401885d9002a045006c348f576a25401c7a1224801350057e84ed448514015fa13b54c15500509dad74485571788a7bb480156d5509da9f448559dabb492249c406006c2848b20055400ed5da2452155006c284f476a254014281224800f5005ce84ed2004d40174a13b48015500002e7422003d00173a11002a055005ce852e2003d40188afd082a045006c35342448556f94276a248015600509f6892710140173a522480155afd09da9244939801098122480155006229ee520055401426d9002a045c5509da8920055801b076a24e6155005968489200554014f62a2480155006c69eed4485540188a33b48015500489da8920055401b0d24b912155002ed125120055400bc449002a04500509da8d271014014298a24801550050a56892005568502449388019600622850576901401424492c80155005098289271014014f8b2249c15500692e742200554016ea13b5121550050986c144901400ed5daad124050055dda89200554014f5522480155006fa851644855401b0b9d09eaed5006922c54200554015fa1224a21550071f6173a105540142449e42a0450062284e527055401ccd25091240500722e75f76901401a8a1224801550062284450a8114014276ac112155007234942449394014262a249c15500425da8914055401a476a24801550050a2c9220019401424492c2a0f5004fdda892705540173a122c801550050a1a8920055401a476a2498155a13b5125e20055a9eed44a14801560050a388920055401cc9fa2480155006c2852e7aa2540142974911215500509e28927055401cfa122480155005d288ed200554014244900580f5006c285024485540142552249c1550050a2d1244855401b1a145912155006c2e74297055401c8a1224ac405004fe2c8920055401428b3d4a84050050a3c89200554014276a244c235003b56a8913855401315da2480155006c284ed44831401427ea2480155003b56a8927055401c8d23b5123f500692e6bb20055401a4a12249c385
  | 6, 8 => 0x509dadb270554014f76a24461550050a1ced44901401b0a12248a155003b57689200ad40142459002a0950050a5c94200556f55fa7bb5121560050a5c89371014015676a508015500622bf428b055401275da2480155006c2850244939401c8e3dce84405003b57889270555dabb44900321560050a2cdb20055401428ea24461550062284e920055401a476a348015500509fa89271014012e90a249c1550057e85274485540175b9d0880155afd09da890c855801165e22480155005ce84ed250554014255224501550052a84892005540142459a48015500509ec8920055401c7a12249c405003b578b5449016c94276a7d1215600509f6f544901401c8a1459104050050912542003d401c8a1409124050069f10f576901401c8d4d7e848950000292892003d001c8b9d0a5c405005265c892003d40173a13b49c405005cebeed6205540173a13b586405005ce84fb20055401a4b9d7c80155006c284ed45855401428b224f2155003b53e8939939684f84490032156000029e892003d001b0a13a5121450053d12400a8154014f97224800f50053e448920055401428b2244615500692848920075401427abb51a405007229ec144901401688122480155a7bb5248920079801a5772248015500509da893d0554015fa13b51c1550050a5c8927101401b0a1395121550050a5cc3449014015676a249c40500691da9c20055401aad23b512155005ce84400a84d40173a13048015500509b8c12005540188a13b4801450050a7aed44855400bb552245015500529768920055401a9b9d7d121550072284ed448a140142449b880045005e6aced20055400f65da2480155006d28489270554014276a2496155006c29ef576a25400ed31900501550050a5c8d20055401c8812ed124050053e049244901401a4a12249c1050050a1e8920055401a4ccbb480155005cddabb271017114276a489c406005093e8922855684ed492249c1e60069284892b9014015fa5509121550057e84f644855401428b22480135bdd929eed44855801428127d124e500691da89200c5401165da244615500722bf42812254014f45a2480155005d69542200554014276a648015500691da894090140142562248015500509da893105540142742248015500509da9f27065401aab9d09da155004b9768927101401c8b9d0880045005cebeed200554012176a24800f500692848927055401a4a12247c155006c29f2e448554014276a24801d50062284512005540199a13d5da4050050a3ced44855401425da2c80155005097c8920055401c876aed122850053e84dc200554014276a24800e50061a848b2005540142449588015500509da9227065401aaa14b912155a33b53e892005580142449388004500509168927055401a776a491240500525da89200554014aa12248a155005ce84400a8414014276a6c9c405005cebf024485540173a110040155003b5668920055401a476a247e1550059284c144855401cca7d091240500606848920055401a4afd3d12155005ce84ed200c5401b0a13b514155006c2e7428b0554014f76a24801550050a4e8920035401a376a2480155005cebeed448314014276a249c1050057e850f448554014a812248015500723613f76a2540000b9d28801540075391424490140199a14b880155002ed588920055401428742d12405a13b53c892005580110449cc80155005091a400a8114014276a24ae40500736850244901401c8a12249c205006c2851244855401428ea2480155006917689270554013490a24801550050a2e892005540142972248031500692cc8920055400ed5da24801d50072284ed65225684ed4495c9c40600622853120055401c8a13b5304050061a84ed20055401c8a7bb5123f500509da8913855400be5da248015500509eaed448fd401a476a408015500509da8927055401b090bb51215500509da891f055400bb4495880155006a2a489200554015fa13b5121d5a7c09da9f44855801cca122480155002ed124e2001140142449f4800f5004ce42ed2005540173a13b47e1550064284ed44855401b0a7a242a04500692e654200554015fa13b5120e5a1409ea9f4485580142449386c1550050a2c89200554015fa1224ac155a7bb5124e0c855801b0a1459241550062284ed5805540163a1224801550069310ed20055400ed5ea24501550050a048b2005540142449001e095a128d125620055800ed54224801550073284ed448fd401a476a24803a5a128d124e20011801aaa12242a0450053ddc8920055401b0a13d5d2895003b576892b901690ed4fa24801560050a5c891f855401075aa24801550057e9eed448554015ca13b512155006f28502448554011d5da2480155007339142448fd40173b350880155006c311428105540164a12244015500519da89271014014279a24800c50053d9689200554014f76a2490155a7bb546892005580142769648015500549eaed449014014b449002a0550053dda892f855401b0b9d09d21550053ddaae44855401c9a13b5124e50053e368920055401c8a13b5124250057e84ed4495d401c8a1459123f5
  | 6, 9 => 0x531da89200554014a76a2c80155004aa40ed449014014247a24800f500732848920001401c7b9d7e8415500509164520055401c9a14091240500722c94f76a25401428b2249c405004b9eabb44901401428b30d1240500509da8914055401a4c43b49c40500509da89270494014276a349c15500409768920055401c890bb512405006a6bebb4485540173972ec801550050982892705540173b2509da1550057e852e7aa25684e9492248015600732848920005400ed5da24800c5006aa9eed44855401429622480155a13b512401e055801c8a7a248004500509da5927101401428b23480155002d912400a811400ed31900581550057e850244855401527b2248015500512048920055401a4a132912155005cebf4297055401c8a1459244050000398bb44901001166c224801550050a048924055401a4a126080155a1459da922710180173a133c8015500722e75f768554010955224801550057e84ed4483140173a11002a04500592852e4485540188a55088015500509da893b90140188a13d8801550073284892005d40121449002a0f5006c2e73e7685540000e657e84894007231142811014015fa7b0512155006669eed20055400ed4c1a480155004597689271014014f4490040155003b5768914055400ed5f98c8015500732848920011401c8a12249c045006c29f164485540188a14584615500645da8920055401c8a122480065006c33d424485540188a14b89c405006c31142728554014276a24f6155006aa8516448554015f812ed1215500509d2892710140173a1408800c50072361a4a1225401b09fbb512155006920aed4490140199a13b49c15500752848920055401a4a12248415500622853d7685540142449382a10500509124e10055401735d9002a0450072212ed44901401cca130112405006c284f1448554015a8b22480155000035373af855001b0a12a91215500509daca44855401b0a141604895006668516200554014276a6080155006c3554276a254014f76a247e15500509165420055401428122480225005cebf420a811401b076ad5121550074e848920055401467abb5124050050a2c89200c540164a12242a045aa509da8920055801c8d0bb51240500549da892007540163a13b512155000029e8b2005500188a13a08015500757994244901401425518c801550050968892005540173afbb43c1550069311422705540166a7a2480155005ce85057690140188a13b4801d50050918400a8154014276a243c1d500722853444901401d45da2480155004ba4689200554014f76b2d12155006c29ee9448554014276a989c40500509da8923855400bb449384015500509fcfb44901401cca12247e1550051a5c89200554015f9e3b51215500622845620055401b05daa912155003b594bb44855401c8d8509da89500752bf424485540188a113880045003b576982005569eed4a2248015600002848b2705500142974151240500509da892105540173a11142a045a7c09125420055801427b224461550050a048920035401428b2247e1550057e84892003d40000b9d7e0415400623034220055401427fa2480155006229eed20055401d19fbb5124050056284892710140166a12249c1550057e84ed4c05540000b9d7dda0c4006c2d0ed448554014e76a24801550062284ed2b901400bb5518c801550072284ed3190168531492248015600622851d20055400bb5a2248015500509da89200cd4014a449382a04500549da89270554014283a2480155006c284890a83d401c876a24a240500509125127101684ed4a2249c156d9509da8920055800ed5da248e155a7c5912400f055800ed44948801550072284ef449014014f459002a045006aa84ed4fa2540142449848015500681da892005540188a13b49c15500752848922855401528b224801550072360ed5da25401ccc450880155006c29eed49225400ed5da248415500691da9420055401428b2244815500691da89371014014276a244c1550057ddaa6200556f54f76a2480156006228516200557914f76a7d12406006aa84ed49225401737698c801550051912400a811401426e22480155d8509da8943055a8516449383c15600509da89200ad401c876aecc64050052912400a82540188afd3dda1550053e3316449014014293a248015500509164e0a811684ed449003215600509da8c2005540000a1224964040050a5c8925901401c0a1224801550053ddadb200554014298a249c4050050916400a8194014276a5880155004fe048920055401427abb52840500723534244901401a4b9d089c405006c28516448516f54276a249c156005091240128554018876aec9c155e4509da9f44939801a776a249c15500509128020055401c876a24e64050000284892583d399c8a127d124060050a5c892583d68492449388020600509da892f10140000e64fd12404006aa850244901401888b2ec8015500723492e44901401a476a249c40500509daea449014014276a3880155004096a8920055401a476b0d124050053dda893c85540142582a51215500695da8920055401b0a53b512155
  | 6, 10 => 0x1b0a13b5d6895a13b5248920075801577abb5124050050912400a01140142531002a045006c284ee44855684892008032156005ce85312005540142953b512405a7bb53e8920055801b0a23b51215500509e6ed44901401424b10040155d8509daa344855801c8a13b5164050050a068921055401b0a146d12155b9d92beed44855800ed5d98c80155a1249124e20011801427abb56089500691eaed4490140000912248015400622bf3c768554012e912248015500723794276a2540186a122480155007236188a13b54014276a244a15500509e8ed44901401424493c801550062284ed21055401c8a1395124050053dda942005540173a13b5601550053dda89371014015fa13b4c6155003bd768920055401a9a122480155006c285027aa254017fa13b4801550062284ff20055684ed4fa249c156006928489200314015fa522480155003b5127320055799424fa2480156006c2e74281055401b0d03a5121550057e84ef448554014276b6d941550073348ed44901401a876a24801550072348ed4493940142972c112155005cebeed27101401a49722480155004a9dabb44901401a6a12248015500551da89270554014276a2506155006c2e74276831684f876a24801560057e04c744855401cfe65091240500509da9427055401bda7bb51215500509da893713940178a122480155005ce84f576901401a677a24801550057e852a76a25401c7b9d0880155005929ec5448556bf4f76a7d1215600509125627101401a4a1224501550056a2c8911855684ed4ba24801560050a60ed44901401c8a140512405006c29ced44851401a476a249c385a7c6d3e8920055801b0a13b512225005ce844e20081401428b224dc4050057ddabb31855401a95da2480155007229f2e449014014a449148015500509125d2705540142973d51240500519da92449014015fa122c801550053ddac344901401567abb51240576aed3e8927055800ed449a4501550053df689200554015fa12249e155006c33f42448554014276a54801550050a2c8820055401ccb9d09da40500692e75f7685540142812248015500722e74276939401b0a142d12155006a6bf424485540173a14b880155005c284ed4490140000a137080154005ceaced20055401cce45ce844050050a3a892710140188a149c801550050a04e0200554014f76a248012500509da8920031711427690032156a13b5121e0c855801c8a13b51440500722e7428b101401ccc45091240576a8d12732005580000e650912404a146d3e8927055801737abb5764050053d828920055401cca14b91240500509da940b855400ed449d0801550071ee6bb20055401c8a14b9124e50046d1273200554014289a24801550071e849220055401a45da245015500509dac3449394015697224801550050a04f54fa25401cca12249c4050050960890a811401427da249c155a13b542892005580173afd09eaed500655da8920055401429c3b512155
  | 7, 0 => 0x622bf4276a242ac00a13b512400b855801427abb512400f3000015fa13b5121550057e852e76a242ac0000511da8920055400ed5da248015003000014276a249015500509dabb448a02ac00a13b54689200558014276b6d12400ab000014276a24be1550057e84ed449382ac000050a3689200554014276a248015023002e742769003c156a13b54689271002ae00a13b912400a801801c8a12248015023002bf4276a242a006000039188a13b480a00a23b512400a801800ed5da24801500b003914276a25104060057e8516449002ac00a14f1da892005580000a1409ea892028031f4276a24801560050a5c89200782ac00ab3b512400f055a84ed449002e1500b802bf4276a242a01600002e742811002aa00a13b580892005580000a13b512450aa802853e76a2480156003b576892005c2ac000057ddabb448554014276a2480310ab0000173a13b4800c5003b576892005408c00afd09da890b8558015fa13b51215023000014276a248022500002850b449002aa0076b017689200558014281224802c0ab0028489200782a0460057e84ed602242ac00c453e84ed200558014276a248a150230029eed4495080156000000173afbb42a800a13b512572a101801b0b9d09da890ab00284ed449509c1560069e9eed449002ac00d8509da9f4485580000a7bb5124e0aa802851644950801560062f1142769002ac00d8509da890a85180000a7c5912400aa803614276a491215600509da892005410c000062284e5200557914276a7d12400ab80001c8d25091240500003634276a242aa00004fdda8920055401a4a13b5124e20300285198b2248015600509dab0449002ac0000509e2892005540000a1459124e0aa800014255224801550000285058122480a00006aa84ed44901401b0a140912400ab00000ed5aa2480155006aa84ed4493880c00a13b53040160558014276a250a400ab00001b0a13b5124e5003b576892005410c0076a7d127320055801c8c4509da8920300000bb552248015500003914276a2480a00e450a5ced449018015fa13b560890ab00284fb76a248015600692beed449002ac00a13b51240168558014276a24b8400ab003914276a249c4060053dda892005412c00b9d0a048920055801c8a13b51240003000016876a2480155006929f42449002ac00a149e04892005580173a13b512400630000142449002a0f500509dac1449002ac00a145912400a8198014297224801507b0034942449002a1060072284ed4490002d4276a4912400f055c014f76a24d2400ab00284ed4a1003c1560057e84f576a2480c00a14093e892005580000e43b57689202800014f76a491240500509da892705412c00b9d7e84ed2005580000a13b53e89272802c94276a24801560072284ed449002ec0000722bf4276a25401428b224801504b00361427abb5121560050a0492449002ac00e4509da89200118014276a24d24e0ab002bf42972248015600691da893f9002ac0000509da92449394014276a249c4017b0029f4276a24801560050a2c89349002ac00a7bb5126a200558014276a249c400f300284ed449002a10600509da89200802ac00005cebeed44855401c8a13b5808920300361428b3b5121560050a5eed449002ac0000529da892005540000a12248a400aa8000142812249c40500592bf4276a242ac00a14a9eaed449018014f76aed12400ab0034988a13b4801560057e84892005408c00afd3e84ed44855801a476a24a8400ab003914276a247e1560062e84ed449002ac0000509da8b20055401c9a13b512400ab00284ed5da249c1560059a84ed449002ac00006f284ed4485540000d862284ed0aa803714276a24801560062284e5449002ac0000509ca8920055401b0a13b5d2890ab00285165da248015600509eaed4495080c00a53b512400a811801424491480150230034fa476a2480156005ce84ed2a1002ac0000691da892705540000a7bd5da892028029f0276a2480156007231142769002ac00a1409ea89200558014297224a8400ab00285197abb5124060069e84f576a2480c000053e5c89200554014276a2c8015023002e742769002a0c60050a04ed449382ac00005ce84ed270554014281224b0400ab002851681224801560000284ed451002aa00005ce8516200554014276a2480220ab0000142972249c15500003913f76a2480a00a7bb51240160558014276a2880150030000164a7bb5121550050912542005408c0000485da89200554012e90bb512400ab0031142769003c156000029e892005408a00a13b5124e1605580000a145924400aa80348ed449002a0960070684ed449002ac00e8509da892005580188a13b4803b0ab00285164490058156000031142811002aa0000509124e0a811401a476a24d2400ab0000142449002a065afd09da92449002ae00a13d5da892002580000a13b5124007a80284ed449002a0560050a5ced449001ec00006c349424485540173a13b4801504b000010976a24801550050a5c893e9002ac00bbd3dda8920055801427abb5126920300284f576a24aa4060053ddab5449002ac00a14b912400a8258014276a249c400cb002e742769a4801560069284ed449002ac00e4692848920055801b0a7bb512400ab002852e449a4801560057e84ed4493880c000050a6889200554014276a2d12400ab002853497224801560050a0b02449002ac00d5509da8920055801c8a7d09da892030036188a13b51215600003614276a242aa00d250912401c055801b0a14b9da890ab003614276a249c15600691dabb449002ac00a1459da5420055801b0a13b5121500300361428b224801560000284ed319002aa00d4e91da8920055801a4afd09da890ab00000ed44944801550055a84ed449002ac00a122480150481180173a7bb512400ab003914276a2480156006c284ed4485402c0000509de8920055401427abb5768920300001b076aed12155
  | 7, 1 => 0x509dab5449002ac0000519da892005540000a1415da892028034973a122480156006c284ed449002ac00a1415da892710180188a13d5da400ab00284c0449002a046005cdda89349002ac000050912450a811401425daa912400ab0028ced449002a01600692849f449002ac00b4509da8920055801a4a124912400ab00360ed5da24801560067684ed449002ac00c450a2ced2005580173a13b512400ab003615fa13b5121560050a4eed449002ac00d3bd5da8920055801c8a13b576892035ce84ed44938801570053e84ed4922480c00a13b53e89200558014276a2480350ab509da9f44938801570000391a476a2480a00006928489271014014276a2480150a3002e6ed5da24801560072b914276a2480c00a13b524892005580000a13b528400aa800014276a24dc405a13b52489271002ae00b9d7e84ed44855a84ed4fa24801500b802954276a2480156003b5769f449002ac00a13d9da89200558014276af512400ab0039142813b512406000039173a13b480a00afd09da9f44855801a9afd0912400ab002851676a2446156a13b5469f449002ae0076aed248920055801428da7d12400ab00001c8a14b9124050062284ed4493880c0000509da892710140142973b5124e203000014276b0d124050000284fb449002ab4276a4912400b855c015fa13b524890ab00284ed449002a026a13b54692449002ae00a13b5124e20001801a4a7bb512400ab001dabd5da24801560000284ed469002aa00a13b5124014055801a4a13d512400ab000014260a248015500691da892005420c00a13b5124e20005801b0a13b512540ab003914276a24802c600001dabb4493880a00afd0a048920055801a4a13b5124e0ab0029f427abb51240600003614f76a242aa00a13b5124e2005d80173a7d09da400ab00349428b2248015600509daa34493880c00d9ec284ed448558014276a24ac400ab00001aaa13b5121550000391424490008a00a13b5124e20011800ed5da2480280ab003554276a249c1560053e852e449002ac00e453dda892005580199c4509da400ab0000199a13b48015500509eaed449002ac000050912400a84140000a122480200aa802851d76a2480156006c7614276a242ac0000509da89200c540000d850a2c890aa80284ed602249c40600509dac36022480c00a14be5c8920055801424493880200ab00284ed652248015600722853f76a2480c00e6509da89200558014276a24b0400ab003914276a249c156007339142449002ac00a1459da892005580000d262284400aa802c94fa13b512156007228516449002ac007abb5768920055a851676a249c400ab800014276a247e1550050a42ed449002ac00afd09eaed448558014fa122480150230000000a122c8015400723614276a2480c00a13b512422005580000b350912400aa802cd42972248015600003614274a242aa00a7bb512400f0558011676aed12400ab000014a449002a04500002a4ed449002aa00a13b52889200558014281224a8400ab002bf428b3b5121560071684ed449002ac000062284ed200554014276a249c2f0ab0031142973b48015600509dae9449002ac00a13b5128820055801b0a13b5121504b000014f81224801550050a3716449002ac00c4509da4e200558014276a249c1e0ab0031142769002a0060050a12ed449002ac00e45ce84ed44901801428b224801e0ab0031142769002a126006c284ed449a42ac00a13b5126f2005580000d8509da890a28000142459002a045006d7614276a242ac00c4509da400a805801a4a1224a2400ab002f54276a248015600549da892005c2ac0000621dabb20055401c8a13b53e8920300001a776a24801550062284ed2005c2ac0000622bf42768554014276a243c170ab00212ed5da248015600509da8d449002ac0000509dadb2005540188a13b48015023003914276a491240600001dabc449002aa00a1415da892005580188a14f1da400ab000012e90a24801550057e84ed449bc2ac00c7e2284ed2005580000a13b512790aa800014276a24461550062284ed601002ac00a13b51251200558017aafd09da890ab003614276aed121560050a04c7449002ac00a1459124011855801bcd8509da890ab53e84ed4fa24801570066684ed449002ac00a13b57663200558000000509124007a00349427abb512406000028489200540aa000050a5c892003d40000d8691da890aa8038fa4a1224801560050a2cd4449002ac00a14c5da89200558014281224801504b0034973a13b48015600509da89399002ac00a13b5b6c0200558014281224d2400ab0034988a122480156000034942449002aa00d250a5c892005580000d8509eaed44a80391a476a24801560059284ed4493880c00d2509124e200558014276b3912400ab0036142813b512156000036173a13b42aa00d250912400a8018014276a24dc400ab000014245a24801550053e84ed4493880c00d23b512401c055801a4a1224801500b00001b0a14b9121550071e84ed449002ac00e4509eaed4490180000d22ed12400aa80284ed449388020600722e742769002ac00a13b5126c20055801a4a122480170ab00001a4afd09121550053e84c1449002ac00c4509da892005580000a13b512400aa802852e76a248015600509dac2449002ac00e672284ed44901801c8a14b912400ab0034942449002a046c4509da89271002ae00a13b5124e200558014276b0d12400ab00391428b3b512406006c284ed448b02ac00a13b512400a80180142812ed12400ab00001c8a13b5123f500509da892005424c00d23b512400f0558014245a24801502300284ed449002a0160050a04ed4fa242ac000072684ed449014015fa7bb512400ab003534281224801560069284c0449002ac00006c284890a8114018876aed12400ab00000ed5da248015500509da89270642ac00973b5768920055800ed5da249c400ab00001427722480155
  | 7, 2 => 0x69284892a1002ac00c4509da692005580142953b512400ab0028492449002a04600509da98449002ac00e8d09da8920055801a47abb512400ab00284ed72a248015600509ec892005c2ac00a550912400a81180152a13b512400ab00284ed44938802c60069f4942449002ac00a13ed12401605580000b9d7dda400aa80001a4a12249c1550000284ed449003aa00a7d0a048920055801a48b3b512400ab0000142449588015500509da892005414c00a13b512542005580173a13d5da400ab00001424493880045a13b51254271002ae00c453dda892005580000a7bb512400aa8029f2e76a24801560053dda89271002ac00a14b9ea892005580000a13b51257202803674276a248015600002851d449002aa00a1459eaed449018014f76a248015003003114276aec801560071e8516449002adb0a13b5248920055c01428cbb512400ab0034f4276a248015600509da893c9a42ac00b9d0a2ced200558014276a248015063002fb4276a24801560057dda89200b02ac00c4509da892705580000a13b5124e0aa80284ed449003a1760050a5ced449382ac0076aed1254200558014f76a24801500b00001cca122480155006c684ed449002ac00c450a2c892005580000a145912400aa802bf4276a242a0a60057e84ed449502ac00a14ba2c892005580000d2621da400aa80284ed449382a00600509dabc449002ac00a1459da9f200558014276a24be540ab002851644938801560053dda892005c2ac000057e9eed4485540189a13b512400ab00284ed44900622c60050a5d21449002ac00a145912400a8018014276a249c1500b0029eed449002a0460050a2ced491002ac00003b5768927055401427aa248015023003614276a249c4060000311427abb480a00a145912400a805801a4a1224801504b0031142813b48015600509da892705c2ac00a1409da890f055800008b2ed12400aa80284ed51a249c156003b578bb449002ac00a7bb58089200558014276a249c150230034942449a4801560053e84ed4490012c00a145912400b85580000afd0a2c890aad09da9f492248015700509da89200540cc0000622852e2005540000a13a512400aa803294276a248015600509dac7449002ac00a145912400a811801b0d2509da890ab00284ed449f48015600509dac0449382ac000069deaed4490140173a13b5124e203002f573a13b48015600509da892005412c00a1459808920055801a476a24a2400ab003114276900581560050a0af576a2480c00a13b53e8927101801c8afd09da8920300284ed449a48015600509da892a9002ac0000509da892005140000a13b54c400aa802853476a2480156006d684ed449002ad4276a7d12400a809c0000c4508801502280284ed492249c40600723614276a242ac0076aed12400a825801a4a12ed12400ab002e75f76a24801560057e84ed4485412c00d4e928489200558014276a24901504b00284ed4922480016003b57689349002ac00005091251200554014276a24d4400ab00284ef76a24801560057e84ed449a42ac00a140912400a815a84f576a7d12400ab80284ed5da24801560071f48ed449002ac000050a628920055401d1e4509da8920300285319722480156006928502449002ac0000692e74220055401a9a13b512400ab003794276a2480156006c31142769002ac00a2509da8920055801b0a13b5121e0ab002e74276b38801560069310ed449002ac0000509dab04485540000d23b512400aa803492e76a248015600509da892007c2ac00e5509da8920055801a476a249c400ab00001b0a1409121550071ee742769002ac00e4509da892a101801a476a248015003002850b449a48015600509da89200602ac00007229eed4490140188a13d5da89203002bf4276aed121560000284f576a2480a00a14b9eaed44901801a476a24801500b00001c7a12248015500509eaed6122480c00b43b51254200558014f76a24802d0ab002850276a248015600622e742769002ac00a13d5da892710180000b9d09da400aa80349424490058156006a6bf4276a242ac00b9d0a5ced2005580000a12249c401028039142812248015600509eaed4490000c00b9d09da4e2005580000e6509da8920280348ed449002e156005ce84ed2005400c00a7bb58289200558014276a2480320ab001da89349005815600003914276a249ca00c450a5c892005580000a14b912400aa800015676a24801550000399c8a122480a00a13d5da892000580188a13b53e400ab00348ed449002a0460050a5c89271002ac000072285164490140173a13b4801500b00000f576aed124050050a2ced4493880c00a14b912400a8018010276aed12400ab002c94f76a248015600002e6ed5d9002aa00c4509da9220055801427abb512400bb000015fa13d5da8950050a5c892005402c00d23b58089200558015fa1409da890ab00284f576a2480046005ce84ed2005c2ac00005cebf42768554014276a24802c0ab002853b76a2480156000025cbb449002aa00a146e04892005580000b2509da890aa802e742769002a04600509daa6449002ac00b2509da89270558014278a24801504b002852e449002e15600002bf42972242aa00a13b512400e8558014276a48801500b00284ed4f9002e1560062284892005408c00a140912400f05580000a1224801502280284ed5fa24801560050a5c892005408c00a13d5dac044901801424493880150230000188a13b49c405005ce84ed601002ac00a7d09da892705580142449002a04003001dabb44900581560075284ed449002ac00a13b5124e100558014fa145912400ab00361a4a12248015600509da892b9002ac00a14b98089200558015fa13b5122c0ab002848920054080160072284ed4490012c00002ed12400a811400ed5faed12400ab002853f76a24801560050912400b85408c000057e84890a811401c8a13b51269203002ef4276a2480156
  | 7, 3 => 0x50912692005408c00b9d09dabb20055801a4a1224801e0ab0000142953b512405006c284ed4485c2ac00eb509da89200558014f76a7d12400ab00284ed449007015600509da89200fc2ac00b9d09da89270558014249224ac400ab003614276a242a04600001dabb319002aa00e4f2284ed4490180000d23d5da8920280284ef449002a0160050a5cbb449002ac00a13d5da892007d8014276a2912400ab002e7428b2248015600721dabb449002ac00a7bb5248920055801a4813b512400ab00284ee76a2480156000035342449002aa00a13b53e8927055801b0a13a512400ab003915fa13b51215600001da89399002aa00a146dda8920055801b0a13b580890ab00001a49722480155006c2853e76a242ac00a13b5124017855801428b27d12400ab00284ed492249c1560050a04f576a2480c00005ce84f5769014014276a24801e0ab00001c7b9d088015500509da892a13880c00b9d0a04ed20055801428b24912400ab0000142973d51240500509da89200ec2ac00a13b53e890b85580188a140912400ab00284bb449002a046000028502449002aa00b9d09da4019055801429740912400ab00348ed4490058156006c284ed4490028c00006a6bf424485540000b9d0a5c400aa802850244938801560000284ed4490018a00a13b5d8892005580182a13b512400ab0028502449002a0060000001cca1224808000053d828920055400ed5da24801e0ab0028d4276a24801560050a16ed449002ac00c457e84ed20055801427abb51240163002bf4276a243c1560050a04892005402c000050a2c892710140000a13b512280aa802e74276900581560000204bb449002aa00b9d09daa620055801428122480170ab000015fa140912155a13b53e892005412e00a14b91240160558014276a24f2400ab0028502449002a04600002e7422005408a00a13b51240118558014f7abb512400ab00000ed5da245015500509dad4449002ac00a14098089200558014276a2480220f300284ed449b8d24060075e84ed449002ac0000752848920055401427abb5124e0ab00284ed4498c80156000028489270802aa00a7c59da8920055801b0d23b512400ab000014276b29121550050a2cf5449002ac0000509da982005540188a13b5ca400ab0028489200b02a0460050a3b16449002ac00a13b5124e20025801c8d2509da89203002ef73a13b48015600509dac4449002ac00d8509da8942855801c89fbb512400ab00284f176a24801560050a2ced449382ac00d8509eaed449018014276aa912400ab0028505813b51240600509da8d2005412c00a13b51269271018014276a24800900b001dabb4498c80156006c2e742769002ac00c4509da542005580000e46c284ed44a800014276a248415500692e6ed449002ac00ea50912400a811801b0a14b912400ab0000188a7bb480155003b576aa449002ac00d23b53e89200558015fa13b588890ab002e7427abb51240600692bf42449002ac00a13b512420a805801c7b9d0912400ab0000188a13b49c15500691da92449002ac00a13b594c0448558014276a24801507b0000188a14588015500509eaed4fa2480c00e4509da89200fd80173a14b912400ab0031388a13b480156000028527449002aa00b9d09da9f200558014276a2480190ab00284ed5da249c406006c284892005408d4276a4912400c055c01b0a7d09da890ab00284f576a4912406a13b5124e200642af42813b5248920055c01429727d12400ab002e74276a48801560050a5c89200d42ac00afd09da8920055801a4a1224fe400ab00284ed449208015600509da892f9002ac0000691da8927101401429724912400ab003914276a24801e600509da9f491002ac00a1415da892705580173a12248015023000014aa12248015500509da89229002ac0000509ec89200554015f76aed12400ab00001c8a1409124050050a04ed4493880c00005ce84ed2710140188a13b4801504b003914276bb1124060000285164488c2aa00a13b5127f20055801424fa2480150230000142972249c405
  | 8, 0 => 0xa13b512400f055801428122480155afd09da8920055a84ed44950801560053dda89200554014276a249c1550050a2c8920055684ed449002a096a13b5126920055a84ed5da248015600691da8920055401427abb512405a1409da892005580173a13b4801550050a5c8920055684ed44900581560050912400a8117614276a2480156b9d09da8920055a84ed4fa2480156a13b52489200558014276a249c405a13d5da8920055a851676a24801560062284ed20055401a4a122480155c4509da89200558014276a2480155a14b9da8920055a84ed4493880156a13b512400a801a84ed449002a016003b5768920055684ed449002e1560057e84ed44855684ed449002a046a13b5808920055801c8a13b512405a7d09da8920055b494276a2480156006c284ed448557914276a2480156
  | 9, 0 => 0x14276a2480155
  | _, _ => 0
def SD (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (stateB s (j / 256)) (stateW s) (j % 256)
  stateWiresD (v &&& 15) (v >>> 4)
def SS (s j : Nat) : List Nat :=
  let v := fld (stateB s (j / 256)) (stateW s) (j % 256)
  stateWiresS (v &&& 15) (v >>> 4)
theorem SD_eq (s j : Nat) : SD s j =
    (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := stateWiresD_eq _ _
def HT : Nat → Nat → Nat
  | 3, 0 => 0x961e516f9585580d54cec09a458376c538adeb8624d59d13
  | 4, 0 => 0xfc8466b4f6d39514f6ab81d5f50610e4f3171119f1fc7b9ceb1bca60e92ac0c7e7e26806e5aaf044e46be5a7e3f62fbde3789485e2e3ed7ee24009d6e0bf112adfede794de5f37f4d7310cf9d70bbb9ed6c6754fd6a8c38ad3f87c76d1d21dd2c6eaa767c39d000abfcf4602bb53995fba67ec20b57c679fb4259e21b32c2949b1cdade7a820c7eca7363978a28ea350a08a8bf0a04d062e9e99dd1999689c6e9845097e93bc596091d4062e91018c1b89e5c6d885cb3d8081128b1080d319a27d14d0987a64f0be7a371b4b73f6ff9e73b74eea710f57b16d47a00c69a03a6e684925846790c95d616844026049d4955fa8b4d65e0749d85d2240085b4b5a0d5ac4134556d7fe3153f3cf2b4f67ef014c402c2e49f94f094986a8d342f73fcb42bc9e6e41ea1582401f6af03f5930433e6ea1cf3a4d6dab360cc8bb33172ac92c7063cf2874811e267dde7325dbb745233d0be220183e431f8703f91a1be108186f6826176f5fda14bb7db0140838f30da26cd807a6e4410287408a
  | 5, 0 => 0x4410e52a43f3a26c43b78962437f4aa542e5df4a42e4fa7c42ca678e4272a14e425cb28141c62104416f3db3415d34cd4145342741357bbc4111e3f040b2056f4099f814408e97ee40801873405aa5b34052b3834028b87d402644143ffd18ab3fecc5e33fa32f263f44c5413f3eb53f3eb991523e6b6ef63e1114de3d9825013ce00d173cdf085a3cdc202e3c4975363bf4a6643b9899133b8ea4bb3b5e45333b2f12cd3a570f38397fd6de397d1f52396809753920144a390855dd381df67d37a986cc3780c4e336b6588b36a0bbdc36464b6c3614a9c2360cc8bb35a30892356e4acd3519da3634dfd9ba34d4db3334cb98e534a4ad4133fbc06033b2a5e733aebd5f339d9f923318eda632ec6c2e326a780f3203e06231d976f831cc58cc319b1dec3189fc033178fc823132372c311eb319307b20b83028e3782fd4797e2fd373e22f71389b2f42ae012ee265dc2edc09d02e86bbb12df4360d2de337572da112702d16a8522cd1bbac2cc670ba2ca86fe32c01485b2bbb174e2b91b4062b79b5912b787b042b3e22e129ef4805294d79782923dc50290373a828f80b6528d85d7328bf552e286ae593282be97128210ff427611a1027386de626fc7f712693397e257ded132570cf02251682da2510c1ae251067cc24c816ee2449a75b244801d5242e218a23a1ca9e23919a83236373ab233ed4692336feac2336451f22bd02e722b74ba722a27cf222a18a2922811e06221008fe21ff4f2521c31f10214266fb20c5d7c620682b1b205822b92036e430201a98921fbc1e361fbbaa081f86cb211f682b541e4059e11df4e9431db31c3a1d9e9f5e1d6ecf841cf32d281cc0f5981caf03601cad112b1c931f061c70887a1c6a007f1c38553c1be239101b647d881b5e4efe1b5447281a8850991a6f0b6a1a1c14d619bf4b3219422abd18d9e7b918857f7d188255a61822324f175df60b16fc79b616dd84a1168bb6ee166289a0165fd47615248dc9151b71f6143021e0141e9bab13cbbae313c3798113ae091e139b227e1383db1e1326e52712fee3d9118ec8191175878711640f1810c32cf40fe197480fe0aef10f7eb52e0f5caa600f56d2b70f2876bf0f2827ba0f146f2a0f070f060efc749e0efad66f0e9bb1350e31d6ca0e29e0b60e286a9f0e0938db0d76ac900d1909eb0cb5f1b60c9e2bde0c8f46ef0c1a53320b5f6cb70b41a8de0b2af6820aab03d80a8028fa0a5e2fd80a58582f0a1c1db209e9d40809c365be09bd716f0995062f098d243e08c50f7908783208086d3318083d4a6107b7772e06f5ba38065a9850064ac0bb0616556d05fbad3f055a290b054602610534f52104ff6e2004f1e60704c338dd04a7eef7045a83fe0351f763030bc32a021057ba0172c14c01729f9d013a44a1010993e600dfd6c9007c8e3e00559acc
  | 5, 1 => 0x8908329388f100a988d8f09e888647c0888341b18868aa3787f2fd7187c1f9b78770158587606cef8700ee2686f5494086d2db34868e55bd866ee5d3863082198624701c85ade23d85abf88b8599ca30853843448538202384c5711a84abbda4849d1a84843f198384303d6e83c8bbcd83c7dfa38376f2588357f9fc82f482e9828bd63482882d318276072b826454128261f267822ee3c281af077b814d172681188cad8100cbb080eb682580ac1df0805252f47fda5e3e7fca88197fbb5c857eef5b167ed465967e43bde87df8ff927d4fe7f17d211fe97cfefefb7ce800997cc286247c5e75d77c38be777bee7cd07b53d86c7b4e30037a9acd1d7a7ac17479b851a679b6e0047894905a788c914d77c8139177c26e18775386227657911b763e4439749e54ac748a92af7322017f72de04a5726874c8725b06e47234b49d71ff618871cfa1487155e968713fc9b171300ac470e27f7470de45f570a4bb2f708e37a17077c9ef7071d10c7061cd4f703987816fe015386fd260e36fbd51e16f9fda246f5d4c0d6f2799c76ee71f7b6edded166e65d27b6e653e436e1d62546de693b66de2e1ba6dd6e5656dd1eeba6dc705c96d8d20346d822b686d6f86a06d5ef8a56d4924a96d3652276c9030c46bd35ad36ba640a76b9613c36b6000ec6b5ad0096afaec0d6af809256aced1366abe005a6a4731116a23c8d769fcc08269d66f4069a1e79f6994d67e698b9ca369481fd66910e50568fa9e9368b0b6b668a98203688e97cf67efe99b676029d366fb414266f4dc9166f4a4f366c038f26681b7f865ee6da965dd3968659f7b8e6583da6d65254e4f64e0456064d9ddb164d17fda63be40956391d00c6391ab0e63557ce86354f45262cb24a062c03b69628b880c62330dc561cf691e616a732d612a6e3260855fe5606104f86049d4956026a9275f13fce55ec51a965e710b6e5e63343c5dfd63a75d6f6e7f5cbcb97d5c593a995bf42c0a5bd9d09d5b9671095b7f63c75b5312635b122bec5a6c285c5a40ab5c591716eb58fc6f99586eea2f57cd778e57be3ef557ab22ad578ba19557068ad9563bc7255614bed055b9e5ed554ef65a5545367f551d7d6e5450a7185386c5d7532e7c3052a19304526c55875156ec4f51452f4c513d4c9d50f7304350e09998500d260f4fdace8c4ee26c964ede78124ea5ebda4ea02b674e5589064e54a91d4da925524ce28fb34cd489424c918f094c6b920f4b7d9ba04b23c0214ac2d3004a7c787449c2f11b49a680ea49a1b0df499262f9498b13ae4986a8d3497988d0497154d94961c58b495640414859c8264842a149481f390f47cdb69147c7a39d47c32b2246eef5e246ec0f3a469c3c0f46900d1c46727ac9466db83b464e372346202d4045cc79eb452155164521551045146de7447aa1864429daae
  | 5, 2 => 0xce7216bece5fdb1cce47a5aece125500cd6ef7eccd3f706ecd157687cd05c6c2ccf3fec1ccb62e10cc96b020cc1d1491cb89aaddcb0e894acabc4b89caa55a96c9d387b2c9af2002c8fca2dac8bd76d8c8b334b3c86eda66c7e0a83ac7d3597cc79f2efcc7614bcfc716eb13c6e81ba2c6bc18c0c61ace33c60924f5c55d7219c4d02d7cc4aaa1f5c48178d3c45b142dc296dc3ac22bca27c1b7ba83c1627f4bc15fb5e2c1169265c105537ac0a68546c072ba56c05c96bfc03073bcc010c5cabef60667bebbd02ebe8034debe34e7c8bd6f33d9bcd871a6bcbfc778bca8fcf7bbb9d080bb92ba01bb63857abaa07384ba5ba127b9bd55a6b9bb9c8bb956e6d5b919aec3b914fc2fb83addd6b8267268b75300e9b74cdfcbb72154bab6f97a7ab6f3d7f1b6d64deeb6cd2370b66fe55ab650b61db5f47e95b5ec0067b55a5ceeb540ce8cb4f83a41b4eb8491b45969a9b43684f6b3f53297b3eb57cab3dcb851b3cb875db38316d8b34fac1eb333d36cb2bc5ebab2899827b1a773c1b17b3240b0e1466eb09a77d8b07a5011b04c3118aff6131fafa7f61aaf8d88d2af738c3daf354fe4aee835c9ae903154ae902a3dad8b1d9fac53da4dab98edf2aad1c683aa77afa7aa614c87aa3bdbfeaa36d55caa1b0e05a9e03fbda9cc6bfea9aa2d2da911213aa8b45d8ca8b3ceeaa892b235a87c49dca87b54efa8139bd7a7f01f24a748e434a6c93d7fa68f3b0ea6606566a5dc1872a552e078a4fa97c3a47bcff6a44a65dca420402fa3fdc7c8a3ee5a0da37c2a58a35d6288a359a3fda2a379b7a1b0cfc2a190c086a181d899a174882da1730172a154cd79a13d28cea12e9a07a124dbf4a11e63199ffd77d09eefdf859ebcd3159e8f15c09e73f4929e3d4e3f9d93308e9d52bfcb9ce627819cb740669ca120049c9291629c2a4e5e9bbb6fcc9b9076989b7d81db9b0c8f6c9afee1929a9a17699a690c9b99d3ddb099c3b23299be588d997d61079944c117993ed3b7992021d598e889a998d784b3985f48f7985f3d479819f3a097e43ecc97dbb4a497a3b489978ccb48973466bb96e8784996bcf54496b81596967a40f896607a8395f7e8df95aaeb4d9568188d953a7d74952d8a63950f844094f21dd3942af7f9940cfa47939bf2539360c2bf933e658492e2d5bd92ad110592a0f4dd921f0ae091f0a2cf91c2a3f5918003fd917d574f91798a059150bb75913f9c6a909a8f0a9055eb86904ae1429046c5049042e0878fe771828fe6fac28fd67e828fa2e3f98f65a8708f1884b48edcb6a68e75c0498e1fdf688dc295438dae967d8d3a79948d3669368cb8d1ed8c927bd48c6d34958c43d70c8bd155bc8baa6fca8b4c66ba8b3fcb1b8b28467a8b07fd4d8ae6a01f8adeb0e08a0b9cff89fb99e889c9eeea89babf37899b2760894ce9078918c8ab
  | 5, 3 => 0xffb0e092ffa058d6ff6a469eff3e24a6fe9ba919fdd44addfd91f0b0fd823b59fd5bf9e5fd1f9f64fc312635fbdd304efbd7f989fbd33e38fb74a8aefa2a15dcf9e54aaff959bf36f91d832ff907d175f858def3f817850ef79fa766f6a4bb12f6762e26f62572d0f5f8c020f579829df56480c8f554f44bf4aa06c5f45df9d8f43aecb6f4054563f3f521d4f3e87f80f3b6a4e2f39a2742f38ef3abf38c87acf34c1ea9f33b74fdf2d29f0ef282a9e6f262bf09f21480b0f1ef6ecff1d8849df12103f9f0edf629f0926662f07b0815f077d59bf077cc1aef97540aef7387b4eef89045eef6a74ceed2f37bee962c70ee81909bee720681ee030f70ed970227ed742f7ced4d2727ed447632ed17f39becf7d517ecf24e44ecd3e814ecb60ca0ec1f91a5ebeeaed0ebd7ddb0eba97248eb4ca3a3ea20b57dea11591be98f0de4e963e6a6e8ecab6ae88835ffe875b4f4e8403c99e7da7970e730eeefe72066d9e686089be635d865e5bf3709e5bc6d99e5a3a317e57f895be5685386e5649869e5260d80e4773aa8e41d97c0e4042422e382a7e0e31b222de2c377a9e2ab150ee25f9129e195349ce1105ed9e0bf112ae093db2be0762196e055c8f4e0421695e0051643df6e3184df5d30aade996dd7de49ec23de2bcd40de1ca7a5ddd13707dda10be1dd692075dd5be317dd0f4964dcb1b270dc681114dc5680dbdc4cd63edc0203a1dbbdf58adb6527d9db576a1ddb287c09db25345adaf2d68ddae59826da9c3ad7da6b93d8d9f8fe61d9d9ea4dd91e12acd9011f2ad8d72a10d8959d24d86de413d7cde73ed7765a72d6de748fd6a3d4a7d680305dd62a0181d610bc52d5f1f9a9d560fc1ad5466cb4d53e3076d4bacd17d4b3c30bd45b3006d402a4a2d3e194bfd3d26392d39668dfd3796217d374f2d5d350bbebd2e5cc77d2d5c514d2cae95bd2aa40bfd2a22404d29e06e9d1ecf1bbd0bc544fd052a935d0521e5cd021f8c8cfeb2c7fcf2d3840
  | 6, 0 => 0x1b660cbc1b5e4efe1b3d1b031af1aa651aeb3f211adeff081abaaad61a7183611a1c14d61a1617301a037c2119f7318e19f6693e19e52c0719de0b6d19cc133b19c2686f19baa33319b2b6f4199702d9198b5f6219753f89196d499c19676282195aad5619499ff2193b63fa192c647218fecf9818be107c18ba420f18a64a36189a5e70188f4d65188255a6187c6b521878bac9186c9b6f1863208818148b0917f1fd3717c83d3517b55b2217b0d7fc17948ca3178d1e5f177be97c17561ad2174257f6170a2e8a16a2731416975d42168a0d37167da5561669366a166289a0164c119616491ee916371ee51628f7221612785515d4d14215c42a0415a446d01593e92a158e00ef15752b581560b1e8154f5ba1154d72471522334e151d338f151ab4c915197eeb15105b3f14f83a1a14d2df6d14b2314b148ff716147d10f0147b83e114687f8e14631d1b145dfc00143ed865142237f11420c3ee13e8cc8913dcc45513d0151613cfa28d13c16bd513b33a88138859c013377b3f1326e527130bbcb012fe9bd612fb066212d187dd12c9c2ad12afa559127ddd401233eeab12085ebf11e30046119da5d6117c63601138a45d112c7350112a7c9a10fb93c010e6da5310ad085110956ea210806d941071951a1070afa81056017f104e6e05103a4346100715b50ffbf9340feb120b0feaa3ec0fe268420fb62c8d0fa804ca0f8f24380f6e6fad0f62b0740f56d2b70f49b2b40f31ef6f0f2354780f0c73710eea52010ee2189a0edc7c960ecc7fef0ec5760c0ebfc84b0e706a0e0e6aa3750e4cd0020e32bf680db1ae760da3e2470d76ac900d57eec90d56e92c0d52a8fc0d31ac900d1b5b590ceba2450caa76370c5393d90c3fcab60c31b3c90c1e61070c08e9200bfd19380be5774c0bb743cd0ba9fdf40ba08c4c0b4a035d0b37f8490b33e43f0b1cb37e0b12b9bd0affbd070af490780a949dfd0a8eff720a7aa1680a6435ec0a5b6a9b0a2a77070a250db009e43b1009e2753409e10f0e09cee74009bd02f609ae9662097d8006093444e0092254e709084b0e08ff722308e1be1c08d7865108b8874908add79708891afd081ce0d1080a52df0802595107f2152d07be4cd007650f3507551951071fe67f0719a0dc06ecb58c06eb720406d3f70306d3830506b46596069a6901067cc51406261ddf06143f3505ed300905d2a1810573590a052307bc0503702a04f7c70e04d260ff04b837880486d7cc047f057e046728290440da03043dbcd103ade645036c935c035ec11f035b700d02fa5c6702d2780902bfad7202adde7202a7086902a20b85029b7b4d0294ce9202537c0a022e4c0d021381790202d7a50200d01801ee3b040197cd980175b071015ece9f0139201a012c28ec01162f5000f36034009c52b20074de82006bc334004ea80f
  | 6, 1 => 0x35d74e5635a1bc57358cf1d13580b9263575cd13356300d1354270003542660c3504cd723500958c34d617a534b6315434869eef347f359a3417d5ae33f4af8b33b30b9e338b70f0335d4a1833589dc6333d77a4332ab86433194e8d33188d953310bbcf33067c0b32db3e8332c41d9832813d7d32805a54327f400f327b409832583e5f32287f5031cbbba2319615c5316e94ce31625df63147c0ad3139e13e313954c431284d31311eab5531141f9d30fec5ad30fd202730eee1c930ea8fef30da131430d4b00830d10fb730c9f85e30af6709308e2a3e30648649304663f32ffd72872fec1cfe2fe92d502f90dda32f7221392f6d5c2b2f6c69f92f6a3bc62f65b0cc2f579b442f5138002f40216e2f363c582f1573e62effb9de2ee015e92eddca312ecefd032ebd98e22eaf05ff2e8cf6682e55254d2e2d76ed2e1d81772e13e6ae2dfe7c192dbb2a3a2da51c142d512d492d0ff2e02cf071c82c77bc402c7796e52c51e1dc2c3510b42c3130152bf774042bec15672bd635802bbf984f2b91b4062b86d62f2b4f91c42b245b5d2b1f30922b1cfc8b2ac761be2ac012cc2a998a572a8ee2762a8e4cc72a6def712a53bdb02a3ad3fa2a356e812a2cb55b2a1c2a642a03b6b329fc670029dcd34a29d85d2c29d1dc7829bb917c29959ad4298e6a792986d0652978cd0c2976b9bb2975cde9296ca2332961d4f2295628a2294f775f292684402921260129099f4c29061ba52905a7a728fef94f28feed2628f995d428a6a18c2855a4112854b1e12849c7b2282e13a727e28f7e27d69a8227b44a242766d59227666194275cd58227532303272429bc270e5cf326e69d8826b3fa8b26a994b4269ce6152674698426552c57264569cb25d51e9525cedab825c360b425bf99b525b5e64b25b3cf46259febc3258fd23f2558a28c25554328253ea5f724feec2f24df1a8224b9830524ab983124a679c3243b8d6824352f082425ac6d2423293d240b3cd123f93d9e23ead27b23d1fec423cb16c623ae30792382277b235be0f223563759233ed469233d0e492309141e22ac98e72294bf1d228c11692229647d21de2ba021bf4f7e21b76b0721a7adec211b56c82104f4c420e540322091cd7a207c1e0320790da5206e404820648744203b958b1ffda6bb1fe92b891fd43c881fc879031fb1b7201fad1da91f888dfe1f86cb211f6ce93c1f652b461f61e7d91f55f7dc1f2d5da21f29d8af1f1491b81efac3161ef4e3c61ee457801ec3a3401ebd118c1e957d611e80c3401e7df9d71e7345321e5c8c5e1e2aa5d91e1101ae1d9e9f5e1d95f7de1d784b461d77f6871cfb86dc1ce226e21ce01f121ca8218b1c931f061c7185011c6e3bbe1c694a521c63d46e1c55c39a1c50f25b1c4d06b71c2e88ef1bdcada31bd692df1bb8c75f1bafd6c91b9c52f4
  | 6, 2 => 0x4c584d784c5064454c432dc94c3145234c2615124c19b4be4be1be6f4bdf72e64bdd75014bda64a34bd66c404bc021444bbaf1ba4bb590a34b9a2a9c4b7d5cd44b747ad74b6dde1a4b6b1e894b6b14aa4b5407274b52aeb64b524a284b07f8d34ac633304aa036114a96e3c94a839ece4a7dd7514a7d8bcd4a706c854a563ac44a46dcde4a1cb1904a0b696a49f6ab1d49d6cc8649c63add49bde35c49a8d6be499d419b497c5c164957f71c49314ef148a55ca14859bc1f4847d187484513f64843c30d483090bb481a6023480e383a480aebdd47fefa0147e53a2947c4ae6647b85f0e479f9f97477094ce475f66bc4759d2f047537be04743dbad473901784726a6d0471a1e5d470c2d8a46f7a89d46d7f1b846c1a6bc46b7161b46b1cb224699cf4c4693e218467ee24c466db83b46558c9f464e37234649d01b4624c8a7461dc2ef461d27c74619667d46150ceb460c7b9945f61f7245effe2645b3bd5445b052cb4586b743456ac0ee4557c03c4541230b452c655f451cd8954514fb8b450f87a244fa6eeb44d4af2844d314cf44c00cad44aaf6f0447de18e446001084459c7f844410f08441ade6e440fd7834409c56843f184f443da4f1f43d5486c438b3f614388de63437291bb435b419743427775434263e94325db0a430a8a284309848c42fb69be42f5e3a142ca678e42b9e48642aa84c44280840b4279b0194278beab425cb28142456125420f972b41defc5441d8c9c741d63c9d41d5715d4179b8b341722cd841354eef410815794105971340ef57ed40de603e40c7bd3f40c2e95540b8762e404ae1e8402dead74010d8903feb515e3fe1bb9e3fc6f4873fc192253fbfc5e53fa32f263f947b463f8ad3683f7e4bde3f4534a33f4379543f2eb2853f13aba63f0b4ae03ef127f83eea73c13edf8fd93ec2e0f43ea3a9a33e89ad003e8076eb3e3f1a553e2d22ed3e24c31d3e0ed2453e0b0a043dd2d4af3dc1abe33d7ac85a3d74c4833d4de30c3d0463903cf703743cf416673cd6f6d53ca5f2223c8892343c6f8c323c6d9cc53c527bb83c1a7bba3c0e08ce3be028a13bdcfd793bcc4a453bcc3d613bb6b91d3ba745f23b89dfb33b78a19d3b6830183b5cde1f3b445a843b33733f3b30f43a3af7dbc33af0f03c3ae0689b3acba3533abed1d73aab09b23a82f6e23a74479b3a3678ed3a28890a39e2fc9e3991ae2739892ff93950102f394305e7393c3963391903b738c387b838ad566e38a8210c38a702dc38961c74387649fb3875495f387035a0386af9fa381ef945381d221c3817081d37d348d337b8c79b379b98cc3789d7cd3782d43d377fb805377e127f3779bb20375d96063753eb693752020f373f4c163717829a36b79cc936af91c8366d0f563626c7b93613e5a635ff5a7635ed5c5135e75fa935e55f2a35d88d9c
  | 6, 3 => 0x645f3fa4645a0d696440a844642b53596426c81b6420339d6413e4e964068cd16405743763e38c1c63cc24a4638799916367c17962fde6d262f3e7b562c1240762a698f3629dbbcd6294243e62684fec6233978a6220728361efe12661e6a0df61cdf5c6618f63306139e9ca613343d960fd272360db5dac60ab55cf606c06d060631147605b783560112a6d5ffbf8e15ff0e8d95fca4e085fbebcee5fbb32bd5fb3b63d5f93f1c05f4d8aeb5f1f70225f1a377f5f06f9af5ed32ea75ecc2a405ebfb2a65e96f76e5e7bba715e7981115e67d3095e6092c85e47ac8f5e4197695e308ae15e12546f5dfdcd635debf6275d69d5645d6299c45d52a2fe5d0a691f5cf1669e5ce07ede5cdc91945cc71de55cbcb97d5cb9b8535cb2bb275caf997a5c9b383c5c97d6355c90e8a85c8b0f485c89ae9e5c8786aa5c504c4f5c4490625bef813c5bbd33fa5b92bdf35b7c3aa55b6b16d05adb363a5aa76e015a9252395a78fa185a668e5e5a4ef38b59e6a5a959c1381e59979a8f59972691598447cd59654bf35956664759517cb9595016ae5948ac7d593c7343592c0c9e590e8f68590827ee58f9b2f858f5a8d658e7aaf358df79a458b2ffa1589905db588be3ce5881461f58613e03584d4dba57ebef7157e6ab4857e0439957be3ef557bcc02157b11ef257afd16f57995bad5779ecd85746f5d456da698356b17b585683c562566dbbf7566dae675655c3ba56477051563bc7255638ed1a5636b34c562ea72256278ed256267cac5626732b5626156a5616e3dd55fd765e55f8dd4455c9826b55b79b665584642455730ddd556fbd6255650db15536ac7354fc79e454efc17754c32bf054b27ef65485cd45544f6f9b5445ea2d541b10e3541014e05401bf4a53f807c053eb7c5553d008be53b1b681535b37ed53515a6153452b6e531704155316ba65531338e35303557552ed74e952dc4d2052d93fd052c3b01752b156e7529da4805281743d527ccc2a52728e69525918cb52487b4c523dc453522864d1522025e2520c699951fd0aae51cfbbab51c92b9451b0f814519d55e15186387c516f33df5156b9cc513ab58b5123e13f51057855510142c150fb4ab450fb45dc50e99cc850e0999850d38ccb50d009d350c6037c50b920de5019bd63501299b65006735b4ff4e0ae4fee9a124fe6c0d24fc0002c4fa852754fa3d7264f6ee70d4f6901d64f5a18584f25d8284f11e5bc4ee48b8d4ec4b5654ea9a2b84ea02b674e9b527b4e8cd07e4e84531f4e7cc8af4e7c4c084e7c16164e63670b4e57a2614e5671a44e53ad714e428a284e245c054e183fdd4e04daed4deee3aa4de8bdbf4de8723b4ddac5484dcce62a4d8abb7b4d5dc13b4d4b6cf94d0fc4054d0cfbac4cfa8f9b4ce76a154cdcbb564cbd99724cb5e7884cad95474c9e1a1f4c66e23e
  | 6, 4 => 0x79eb707979e49c0379e0a02979c642c179c14fe979bf976e79b7c8a279ace23579a14d7c799574ba79851062796c1f0d796a111679631c8a795922f97949c98f78f5967c78b60b2078b3c575789a228d7898f43d788fb98a7885ca8a788456f378638ac7785ef4c4782291f6781ed5ac77db7174779cf47477779da57777829677731eac77699d79776976b7774fc32b77242e98771a6d867716285c76f4513f76dd8f2776d4ada076c7bbb876b8b5ef76b64adb76af2f39769bbfa4768e38377689ac277677f9647671d405765f7c9a764a79f5763e4439763124367628bf58761960f17609116675ca37b675bfacd575acc57e759cc945759965907576bee97548df0775432e8b7535605875060ce674fdb28774c2d56174b94e1a74a4b30b74a2b0e9749e54ac7489fc6873af871873a998f473909cd073716561733e7ba17336d64a7329477a731bd9d57305d28972c81e7672afc81672901a24726b22f172535b15724cd2ef720b032371fc3fef71f5d6b771c9413071ab2719718d281f716102127157fcca714bff6d7137ca7b7129041571219c72710e13c870e8ab2170d5e5fd70c8809070b402f370a4bb2f707fd7e770735ee7704a647f7046c9607020666c6fd4d5de6fc45e5b6fbf1d7f6fb8b6b76fae9d2c6fa535ac6f8f4b436f6f39f86f6a8ea26f58d4146f3926226f35288d6f2882656eee854c6ee71f7b6ee14b1e6ec337ec6eab1e6c6ea0512f6e96e7e06e5fc4b96e52aa8a6e483c966e1f481b6e0758016df678b86df4e42c6de204c96ddef46b6dbde50f6d84d3586d790a9f6d4b4c856d0c889b6ce4d6506ce1b4aa6cc6b62a6cc2bb0f6ca816ca6c9a05f66c89d73a6c84e0316c5aca8c6c4dd0496bf08c8a6be58d456be2f42b6bc273246ba853186ba6daf66ba640a76ba57b666b8973a96b8317286b7daf6d6b6884266b5ad0096b37bcd16b340e0c6b07e3cc6aff1d466afd20356af501b96ae3c5086ae28cd56ad520446a90d0bb6a747b886a4731116a3dc56c6a23dee36a23c8d76a1bede66a0389c969e2d09669d66f4069d2554369c94faf6987fe176953784769506e7b6929cde1692959e3691eae25690e58eb690252d868cafe2b68ae889568a5cfe7689ae923684b8f5b68464021683a6b2d682bfe57680c7f91680a2baa67f7aa5267d7fc6067c74a3e6778de9a67727c6d676cc7e5676ad8eb67611271675e0213675c5004673696ae6721685d672146ae670d54b666af86b8667b6141665b0f21665091e1664bc56e664adbb7662f2003662dc5ba661fa4db65dc785965d9d83465b7bd5d65b2cfdf65a2663165962a656591d3066591b4a3658b58f1658b32a96583da6d656a19f565626dc46557f6fc6541ac00654180cc64fee79064fa736964f0e93364d7045964d591e364a45ce564862e756485273c
  | 6, 5 => 0x92351a3991fba40291b09259918b876e91743bb491713b1c9112b676910bff9b910be45f90e910c790e81e7e90d8788190b4078b90aa2727909b77a89075dbfb9066338d904b6b16904ae14290494674903ceb8a902e219f9007f90c8febb2a38fe91d158fe771828fe107568fdd4c688fcc04b18fc096a28f9a9a618f3823008eef71938eee88718ecc2a988e8de8c08e6dfc3f8e3f044a8ddcad0d8dd22d2c8da325478d8e03718d7d73b38d7b8c4a8d53f4aa8d2ec4898d2ce4858d29f27a8d0189f18c772e718c2a0e928c186c518c0a448e8bd155bc8b9cfd208b8c8ddf8b872b448b7536968b6e7f318b6dd3378b38eceb8b14f17e8b0a95168aed386d8ada82748ad1d0398ac7b1608abf56658aaee1e98a9f9e908a8e4d528a0c960c89fb6aa489f84e6c89f251878970d7a3895cd73a891500e28910d5ff88ec195e88e5a5bd889f5e208897f986888647c0888283cc887d11c288714e038865f2b88862d5da8851240388469f378843aa078821d54d8804be6f88034e5587f2fd7187e8dda887db973887c3d94587bdfd7c87bd6f34879c5fb38796446b8781be088771830187638f8587607f278756a8cd8751b6e2873a32f4872fdfc6870e3fd086fc815b86dce12c86d8b55686d57d5e86abaab586a8ecad867f902f867eea7d8676af2a8645380c86249332861c41528604075785accec785a7432d858be1e6855f0dba8556a2c1854ad00185491d768543fde085260c57851a5a0184df88e484ad44c584a6c378845569c4844bd7b28414569f84140cd483f4fa7083f2ca5e83cfb34c83adda9983a1c86c8386c6448371fabe83677830834d466f832d433b8314fa8b82fca8c582e7fc1882cb068f82ab589d829de52b829764ba829327d0825daa71825bdea9824a3c5d8234e145823123c781aa722581a27a6781806ff58158ac5081405272811ca4608118f26481188cad80f157b680e7c70b80e5bb2280c330de80aeae208095094f8094c3de80761d9280714abe806c62d1806c57e6805cd3ba805252f48044256480351aa980311174802d6fac8027fa55801db27b7ffdf8257feb2cf67fc56d7e7fb4edc27f91c2577f68df817f601fe97f52cd717f342f317ef3485b7ee3f8807ec75bdf7ea8dfc97e9fc8047e5e58937e57d8747e4ecbe77e4a79bb7e46196b7e3284817e30744a7e2e19cf7e14a5767e1370e07df411047db9303f7dae5f477d6516d87d32b9267d2ce8417d2ab4c47d16eba17d0a84977d06e32e7cce02f87ccc54177cc9a45e7c7572717c6e898a7c446d8d7c1a77dc7c0f19347c03daab7bf2dd2e7be9d2ea7be9c5597bc4b6567bc0d3bf7b716be27b6de8497b54a6767b44663a7b1af0cd7b10edec7ad28f237acd48487abe275d7ab632057a9bb2087a98000c7a423e867a1416f77a06aeda79fe42fb
  | 6, 6 => 0xa6cbc3bfa6c08b01a6b5fd74a6b1d48da68f98cea68f3b0ea674762ea66f77aaa6489f25a63e374aa63a21bca6327f59a62ebf84a618e667a600eba4a5fd00dda5f54573a5da5df1a5d8e305a5c59ca3a5ad3890a59044eaa581b55fa57bebdca55e0ad3a551d637a5105cf9a50e3933a50c6925a5096395a4dfd39ea4995d1ea49228d9a47ecb76a47d9659a46291dba441c1fba3f29f9ba3dcc402a3b247bfa3ae5111a3abdbe8a3a9fda5a3a42e88a39f8ecba390170ca38e50eba38bfc30a3866980a37cc46aa36548c7a354395aa34b1706a3425bcfa32f5f4aa31d822ca315e3a3a2f499f8a2ea99e0a2ea4aeaa2d8f4a3a2ceb8c8a2918a74a27f09c2a275bb60a25ab635a22ca562a1f81c47a1f545eea1e97bb4a1cc6215a1c9fd46a1abd0f3a18a673aa175fba6a16a6864a13d4bcca1256cfda11dea6fa11a6bdfa0e7ad34a0dbe369a0cf080ba09089b6a0535bafa04d9dbfa04ab5b7a039507da0350b1ca0348286a0231b09a01b8312a00075399ff383d69fe159169fcc7b819fb0f8a69faafd359f97f40f9f71a29e9f3be6239f2e7def9f2e59839f1893329f16b0869f08f7c19ed0e3df9ecc8cae9ebcd3159ea9db8a9e8d81a89e7e95469e4f02a79e4c9c7e9e3d4e3f9e35ff4d9e1f07a49e1652429df5f33b9dee55219dda7a1b9dcc9d8e9db0b0d89dafcbd19da763299d9ac25b9d52bfcb9d41ada99d3dc8bc9d0b09d89d07bb949cf963049cad566b9c9c8fd49c96b93a9c8becb29c75877f9c73fe8b9c58024b9c4f62ed9c2711539c1aae9c9c0463a09bfa1caf9bf70c519bf4f27d9be0e6369bd43a4d9bc19f309bbc586a9bbb6fcc9b656db29b3b47789b302ff79b2ade9b9b042dd69af5094e9acc0b0f9acb203d9a9a7d209a8ce59d9a8382449a74b4139a72e2729a5abede9a44bb9a9a42a21c9a30f5759a1a94519a0a94ac9a09568099eded8d99da73dc99d2695799baf2c499b04349996ce458992bd2cc990d1a25990c583798efda9998e98bf5989f3a2c988385c698681fa497fca16a97f7e1e097e95d0c97db22b897d32b2e97a7cdff979e154c9798b8739791e0df97881e0997759bc09775532d9738a3149736c60b971c8ab696c0bb5196bddde296a4baea969c136b968dee4a96751f839640016f963973a396393b9a961ce2f79601fdea95e5c57e95d78a8995d60d1a95c85d5095958bd39583208f95821af3957467ea955f100d95430b69953b66129528542495145dbd95044f0994f5df2494f1551294d6313294d117c794b984da94a4f0ac94a339de949914e994907ae5948ab0e19476cacd943562c293f3c1bb93edec1b93b8538b93afb6e1935a3fef935a1a8f9359830b9342daa5933e65849339535e93128b4f92e4647792e3c20d92e2d5bd92d0a7b492ca0e9792b1fc89926dbbf99241ef6a
  | 6, 7 => 0xc0c8fa00c0c0d2fdc0a7db42c091d6a3c0670995c05df16dc05a9b30c0578ad2c0512c46c04cb613c03dfb81c0378830c010b2a4bff600eabfdf09e3bfb57493bf9bd650bf9a7123bf5da982bf429534beedad13bebbd02ebeb38f8ebeb1e633bea7ac21be615e5abe5c9213be2336c7be07d72dbdf81941bdd21183bdb53261bd99ac7abd63c256bd53924dbd3abca4bd3a48a6bd2fdbcdbd2f6e63bd275b2ebd1a4ee4bd0d86ecbd08660ebd014f6abccca1c2bcbd43dcbcad8d2bbc9f0ce8bc97422fbc6f5f40bc6bd5a6bc5a7f5fbc4731e4bbff91b0bba26448bb9d541bbb313082bb2d5bafbb1962a0baf78662baee1bbdbae4103fbadbbc57baa15a19ba6caf6cba4abd16b9d6987ab9a05b48b986cec6b9750e92b96e103db93f04cdb93e040bb9040ec6b8f7e23eb8ead1f8b8b4b4feb8a390d0b895a9c7b88f7ff9b855582fb830f3dbb81afc98b7a09260b78a6c51b77ec27ab76fdfddb75db791b748b75cb73c3b0cb6f7c6c0b6f3c914b6ebf3aeb6e5ca23b6e0e5c8b6c20d05b6b95f0db68fb4a7b68f40a9b68f1e13b689a6bbb684fabfb61e1a90b61335b4b5f47e95b5c63f8cb5b78b41b599d5eeb5972d98b58b1784b57feb8ab56c9143b53eb5c5b53de326b52a998eb4dec560b4cf09c7b4c86547b4c10493b4a3241cb47a7ee1b468778db44b9b29b427ce78b407f997b3fe0286b3f967b6b3f0bf34b3d33954b3ac03d5b34eec9bb29a9596b29136c4b2899827b27d9733b274ea61b263ef98b236d45cb2342382b20ce67bb1d3a58cb1c8b976b1c5266ab1bed8b4b1913a1fb190c621b17baf06b16ae7c8b0d9cf9ab0b2e61ab0a492c3b07a5011b06e16bbb061f453b04fe07fb03f689eb022bd08b01c382bb00ec24fb00e4e51b00e1f47aff6aa3fafe85879afe04ad8afc8e7e8af7c0459af65f69eaf5b79c1af5527fbaf410a0aaf354fe4af282fe1af106c9caebcf0ceaebcd54eae9215e8ae847ab7ae82e2dfae5dd308ae3fde31adf85589addd8c03adad83d2ada88594ad71d233ad5f5febad5b088cad31419dacf2d441accbc906acc6abe2acc6a4b6acb7dfeaacb371b1aca79251ac6291a1ac523270ac10dea0ac0c28eaac081525abfcde34abe7a905abde0212abdb5512abd82e93abcea9bdaba2c43eab8725cfab64eeb3ab443412ab2b9608aad2f9c0aa8d6f1baa37042daa28b2ddaa1e88f3aa1d0264aa07de1da9f61f03a9f4797da9efe77aa9ed6d70a9ec270ea9e981c1a9c8690da9bf8c3ba9bc8691a9b1d220a9ad0105a9aa7728a958bf01a95646aaa952d1c4a92bed4fa8e37654a8b03a7da8990f5da8875d8ea87b3ef2a863c34fa860f8b8a850dc0ba83031cda82afb5ca82922faa7ebf771a7e8627da7c33d85a7c2d05ba7b4f729a7655e80a755ac3da74c7ea3a71aa0fba6fe63aca6f8a5bc
  | 6, 8 => 0xd770da67d770b09cd76e0579d745b16bd707bda4d6fe8ce6d6ed2f09d6e5db59d6c32cd9d6b9f7c7d6b0f91fd6a67088d69356d8d68ced06d659f31ad644194bd5d19454d5c8ec5bd5c8bca0d5b3f5a4d56dc423d56a4eb3d523f8b8d4d640d8d4c1a17bd4baad07d4a9ba2ed4a54b82d495c68cd48fdcf4d43b6424d430fe4dd425b613d4155db1d407992fd40016bfd3ff547ad3dc95f0d3cc47d2d39d39f4d39668dfd39188cbd3718597d369ee1dd35d5ff6d33bc745d2e4f938d2d84aa2d2d5aec5d2c70211d2c37951d2b030e1d29e06e9d297bff5d290e6e6d27923a1d26afc0ad266841bd2437344d23afe62d1d0cea8d1b6ebe7d1a4ea57d184a8bfd17e1950d16aac31d1359a12d12f969bd107733ad10262d0d0da7061d0d57d89d0a6b036d06ca76bd02b2e2dd0113f63cff70f38cfa6d0facf974c04cf8ee60fcf8c9f39cf620317cf453a4bcf3ce99ccf301f51cf1da57dceefdcd4cee6c600cee40a60cede1b68cec77e37cec437ffce999624ce7dcb19ce6b7395ce60501cce488d42ce3a03e9ce179d9dce14d434cdba71cccdb3b27fcdac7a0bcd9632afcd73aa3acd680993cd5ba398cd284340cd0ed0e4ccc93758ccad9330cca34c04cca1f91fcc9153e2cc556625cc39e650cc371f8acc305f09cc2d42a5cc29f962cbfaaecbcbe7ccb8cb98e8d2cb986b47cb46b126cb04d3d7caf5295acad3f560caaace96ca8e24b1ca8884c2ca82f075ca671a00ca2f8b24ca1bcb3fca059245c9d6bf71c9d47050c9bd5cd2c9b491cbc9b2ef32c974e5cac96ce7a6c9535f5ec94d4fb3c940521fc93ed1fec91f30c3c9092655c90423f9c8f7fa2ec8e4a2e1c8d81301c8d1381fc8c3105cc8ba8d3cc8ad66dec842c712c8376f41c8193002c818a3ccc806d217c7e78b81c7e0a83ac7d55589c7addfd5c7a4d17cc79e4a35c794d4b2c78b2466c782e09ec76c95a0c73d14f0c73992eec7172a2ac712c8fbc6fc3443c6c31b15c6aeb6f7c6a3bef6c6a378e3c699f0bfc67ab594c66d101dc634fc6dc62c773bc5f963fcc5e7c0c7c5c5f886c5ac540ec5a63981c566d82ac54fa6cec549be93c53cc4bbc531109cc5243d8ec51778efc4f64291c4dd846bc4d5f5c8c4b8ddcdc48e9d11c483998ac45c970ac437bf10c411c478c401fe1dc401b3bec3b11c89c3b060bbc3ae98ccc39a483dc395acfac38968d9c38241c2c36ef82cc3558126c3437b73c3168b34c3166c98c2e77a1cc2bdbf83c2bc80b8c2bb51c4c2a46883c27f678bc27c817cc26e1b18c2511722c24f457fc243193bc2399ae4c239124ec21c77a0c2144e73c20ab7f6c207e1aac1fcc9aec1dcd109c1c7cec7c1c641fec1c30bdbc1b7b9acc1a16eb0c17e488dc17a2ac9c160c5fbc15eaa40c159e185c14c6bf5c13b1c63c1355493c10fcba2c0eba348c0dd9446
  | 6, 9 => 0xf263ec90f26141eaf2608c95f2227515f2139e91f2108a76f20dedecf1cc9b4df1cb12c5f1c878a1f1ba3e02f19a51c9f1912f01f1871012f17e324bf1162f02f0e2ab30f0ab1591f0a34f34f0979e0bf06a7802f066eb88f037c632f0349f8ef0321b4fefcccabeefa29d55efa21a31efa0ca2bef99160eef966073ef76e8efef72b168ef6f6761ef603360ef4118bfef392b0bef2a4d59ef15263beef703f8eef6a74ceeea91cbeede5228eedc0f00eeaa8602ee9fa7baee8701f5ee4c14caee4a52eeee34eed1ee32977dee175148ee040f10edbceee0ed8e2c11ed7b819ded7a81d5ed742f7ced5e20aced546c18ed4aeae5ecee740fecc9fe19eca90924ec92b479ec798507ec6f14caec2e2fa0ec2bc761ebe80ed7ebdb9153eb16cb91eb051334eab724ceeab12157eaa9f510ea9870d4ea61b8d8ea5f49caea4bc195ea19d13fe9ec1b49e9e4d554e9e00477e9d9e551e9bf6367e97899f4e96ab83de93e22b6e9367449e9336881e9082402e9072890e8f9b2e1e8ecab6ae887758be87f455ce872a6d6e840be64e8310703e7fd1a0be7ec508fe7e7562ce7c7f295e7b3fc79e77030dfe76a69bee74aed3fe7369d85e6d16dbbe6af72c1e6a947cfe69e1fe2e68f089fe686089be612de9ee5f5c7c9e5e6948ae58c4862e588812ee57c3987e57098afe5493e1be519f603e4fee80ce4f3a9d0e4e825c4e4db6ac9e4d4bd41e4cfd2b8e4c2988ae4a7588fe4846c2ee43fa82ee4181dc0e40f47bee3f3f93de3d0c899e3b115e0e388fb03e380cad4e36ec942e358f2f9e355fb0ce3328c7be32c74bee31b222de314ea10e3145b6ae3140e0fe3050e21e2f18784e2e9a186e2e2240ee2c5daa4e2ab150ee27984eae2771d88e23c17f8e238dbffe2161a6ce205b241e1b014abe195349ce1491f39e11e3a51e0ee205ce0e81a02e0cde841e0a0df5be09453b7e08dcddae062a81ce0586bc7e0555b69e0464166e03f354ee029bc45dfdd3e50dfc18e50dfa022ebdf85f1a6df77002fdf5d63bedf349052defffb91defff5e2def610c8ded721e2ded1318adeb9048fdeb61556de704ebade5f0f27de59b189de15e0e2ddbd1a4ddd99dbfadd93181ddd6b693ddd6aad17dd66cdb1dd31eb77dcdd0604dcc65afcdcbf945cdc92cf7bdc1bbd42dc10d2f5dc0c19c1dc06382cdbcf6db9dbc1e38adbbb25a0dbb9adc0dba4eb10db951523db4293d3db288e62db287c09db0398c1dae75a3ddadbc0d5dacb8997da7db114da710317da59e7f7da44230bda1e2c4cda14f61ada00eeccd9fbe743d9d9fd47d9d2b702d9721f96d925edb6d90cc8b6d909dc92d9011f2ad8fffd33d8dc3be2d8cd4148d8c49e6ed86de413d86ae6b9d83370efd82d2004d8058556d7f43418d7eb9e89d7ddfd8dd7d75e7ed7d12e92d7c3a79cd7bfce70d7990569
  | 6, 10 => 0xffe58633ff85d8f1ff7364f1ff72cd41ff725943ff383359ff310fbbff2c0818ff24bf7afee195ccfecb5e5dfe82b44dfe5f7efffe5a3a7efe3705c3fe2fffc6fdee2061fde4929bfdd3fd81fdc1ddfafda3147bfd88a3cefd5bf9e5fd525355fd37169dfd1001f0fd04c445fcf053fefce6c424fccbdd64fcc51e8efc95e626fc90ed99fc8a3a19fc807484fc6037e9fc5185b1fc3aa592fc22bc14fc167550fc06dd6dfbf8a844fb76af5efb764d43fb7132fafb0e6c5afb048cfbfaf3d559fadf2d30fab82dc2faa078f5faa029d0fa87ae96fa5f44a6fa4c2079fa455a8bfa31afccfa2644f2fa1a792bf9f82506f9f14ab5f9ddf4e7f9ddb73af988a7d1f962f6ddf91f53abf8f647f7f8f5517bf8f547b3f8ed0c95f8e37f18f8a3cd22f8917ccef874753cf860a374f847a30af83c36fef7afd641f7a8352ff78b6672f770afc1f76ec862f761cb5ff75c5d23f75a25e7f7586a05f7560b68f7530b29f724418cf6fa3fd0f6d14490f6c23eb0f6b8b88af6b4c1f4f6addc56f6a47e4af6858148f67834d6f64e9c0df64db03df6442c36f625589bf60da060f604a687f6049297f5e5117ff5e125b8f5c3ad6df5a39dc6f5a1c9bcf5961893f595a1d3f579829df562e151f5518b0af52ae0e1f52675ccf5144f81f4e918b9f4cb4546f4c41e8ff49dd25cf4328f1df424675af418e735f3f54dcef3f521d4f3f176b5f3ee920df3d55e70f3d03e8cf3b7e36bf3b1549cf3930246f38f5962f38933b1f366d26af364196cf33dbc76f33997dcf32e8d46f3195127f2f59c51f2eaf6b7f2e2c9cff2c269bff26c1a3df269de62f2666c78
  | 7, 0 => 0x4c7c12d94c724a0d4c59c8364c584d784c336a304c3145234bf942054bd66c404bc069324bc021444b9cae0e4b7d5cd44b58c7f54b5407274b5332c64b37283f4ac09bc14abc96dc4aa02b394a76ca354a563ac44a4fc1e04a17bec349cb307949b981e2497f6faa497c5c16491374014902d43448cf9cf248af4388489546f34859bc1f47ec41fe47b85f0e479586ed4773cf854759d2f04747df314743dbad4654b83e45f157b544d2406e44c00cad4309848c42edc77641abc9c941a1aa72416b4fa64169ccb1403252043ffd28393fa32f263eaf309d3e8e2a163c9241cb3bbe88dd3b9a619a3b30f43a3af2fbb83a155cd33a1230783991ae273960c6b438626d3e3817081d37e41b2f377fb8053779bb203752020f37333a0f36c0c2eb3691f19c366d0f563626c7b935ed5c5135d88d9c356300d13505527134d617a534637b4e33fbab1433c929bc338b70f03363f2b6313574ea30f8756930eee1c930d4b00830afccc03010ff4430033d2d2ff68e972fe7b9d82fe44f372fd52a852f145ef32efbf6c42ef32cc52eaf05ff2e9349f22e43ab542de616522da51c142d8aeb602d8956a02d8038cc2d3633982d11a9832cabff822ca5af012c8e3eb52c7d97552c082e482bd635802bbf984f2ba978852b5af75e2a8e4cc72a7868a02a6dba452a53bdb02a0a327229f6f1ff29ce9362294ea2fe293ac8932926a353291f1b152854b1e127fc043f27e841f5279b828027472d3726d6a9be268b2b9b265e9614264569cb25e7b23625e154512589e27e24feec2f24ab983123f93d9e23f7764823a8586f22e9c76d229cace521c5799121674f9d2130086d20eed5f22093d217203b958b1fad17fc1f7ee0ff1f26259f1f1491b81ef4e3c61ec5b2d21eb942c21e957d611e78257a1ddf9aec1db7112b1d78df251d258b271cf169111c9471341c63d46e1c55c39a1b594d801b3e9d5b1a64bead1a601d291984d85e197871cf18fecf9818b58881182c3e4417ee671217c83d3517713459164f20ff16371ee51628f72215a86f441593e92a154d72471485314d14559ba213cfa28d12fef36712afa559128ac21112401c94119da5d6111a4adf10fb93c010473f27100a102e0ff8d7b90fdce3610f7b04cc0f62b0740e32bf680dd88f350d1b5b590ccfcea10cce47e50c5393d90c4673d60c2eb0910c1e61070baba7ee0b37f8490b19a67c0a700a660a5f97f30a52d21709e519ca097753e3095aabb9093cf7fc091b222908681a9c07deb9f50708a3f106fa78dd06ecb58c06ddd03006c7d24406c0f033064b636805e3b22d05971e6b0573590a056aa155054e75c20473d387041ca7a103e79b6f0391d5c702d48d7402d2780902cdc410029a2fd1022e4c0d0217ffa302162a2101d55e4801bd129f01b052850139201a00a3b05f0074de82
  | 7, 1 => 0x9403cc5e93afb6e192d0a7b4929f18d991fd6c8991d1223190de638190cf5a9890b17de8909b77a8901c96828fecb05c8fab505d8ddcbab88d71b5778cfef2018ce8fc948cc8c5d38bf410dc8b7c7a318b3bc56c8b331fad8b03ea398af48b598aed4d088900486088e694ea8800c2dd87e8dda8879c5fb38778173e86f5965486eaf79e86c6ad7a86a8ecad867eea7d85c727f785731e84853d41db842ca0e88401cdd883d23e8083cb46ae8373704c834d466f827f5608822bdd3b81fd5e7781e729d481c832f2817b0fb78118f26481151d1780f157b680cc746e80c330de806c62d1805fb7b78045bb227fc6026a7fad8eee7f0fd4737efc6f957ecccc267e9fc8047e1b42807e07e0c27df411047d9f593b7d2e51317cb5f4077c9f54197bf2dd2e7bea46df7b9189277b8378537b54a6767a8a61f37a60d85c79f2431479d8392a79d712fe79c6658079c14fe979b7c8a2796b4aac791cc7f878c1ca66782c8451779e600b778d62da77699d79775cd8c576f4513f76c7bbb876a9a357769de7d9765f7c9a764a79f5760459e475d6330c75ce24da75c83635750958db747b270074745ec774694e717433799d73c1573a73473b177305d28972fd57467294338a725e5e3d7247b594720b032371dd5a1270dbe66d70cb5a8f70a4bb2f6ff8dcc16f9e6ee96f8f4b436f6a67fb6ee14b1e6e9fdf446e48c08f6de204c96ddef46b6d4b27526d23c0b56cc648bf6cbfa3656c5aca8c6c5a53576c35e7446bde0c406bcfc0416bcd2ac16bc273246bc2026e6b5b45096b34f8d66a7947496a65ad0269ef81146995b2c36971b8a0695e7acf692eedee6929cde1691eae25690fbdb06897c407680708c3678580456777fea8675c500466fbb89866af86b865f3d4c965d9d83465cd88966567327a654202a964fa736964d4bd8264c21db263e38c1c63b90a4b6300fa6662f3e7b562adfb966294febd61efe126618f6330616dccba615c00c661048ded5fa2933b5f374ee25ef0979a5e38be715e0f4a855e0bd81e5d01b23a5cbcb97d5cb658875caf997a5c97d6355c8786aa5c5ac8c05c58f5785c4a4c0d5c3af76f5b93b8905a3c21135a0d759759cc477d59a80d2e598447cd595f6485590e8f6858d1403f589080865884c24a584b0c355812194e57ebef7157a2c48a57674d145746f5d4560059db55d3c6f855c1414855b79b6655afc0c3555848fd5485cd455476adfa5435a9065366c8be531d520a530355755303132952fd053152d93fd052b45c8852711c37526fceff520154fb51fe3ac351fd7fae51d9ba4d51ab93755142ab4f513dfd1b50f7bc8d50105fe95006735b4ff02de44fd2bf784fc0e8ca4f16394b4f14f5254ec4b5654ec3ae634ec17c584e9749fb4e5671a44dfe8aa94ddac5484db8fad14db5e2004cdb3fc54c9e1a1f
  | 7, 2 => 0xd0c6e2cad045ec51d00d2211cfa9c614ced341a8cea87c57ce710665ce2c57bdcdd46e61cd0fb982cd0ca924ccbbfbc7cc88436ecc3706e2cc2d42a5cbfaaecbcb986b47caf027ddca5b68b7ca2f8b24ca2dd76aca1bdacdc9d56f2cc9d47050c91c554ac8de529dc8ba8d3cc895a9f4c7bb07b9c7a11b21c76c95a0c73cf9c4c712c8fbc6e27175c6d909f9c68a04bdc686e1aec5eada33c5e9a200c5dd3b71c5db02ebc5bfd17ec5b3a7ddc5a89247c57f504fc5736c2fc54fa6cec5317584c52ac386c51d6045c4f786b7c4dd846bc403ce9fc3d4261cc3b060bbc3ace512c39ae875c38b7d73c36ef82cc36e238bc31140d5c2cc0902c2bff7d1c2b0db38c2539779c2399ae4c231fbf8c22a20abc2219c6ec1cedd78c18ca049c1348032c0926e1cc0512c46c03ff15fc015846fbff600eabfed5a36bfde1984bef98ad0bee8b10bbed33e9dbeb1e633be368842be12c64dbdcd8f6abdc999c4bd6f6992bd59b115bd496af8bd2f6e63bcedb60abcb235b5bc9f0ce8bc4731e4bc431b40bc2f68fabc2a53b1bbb53b63bad56420ba62a8fcba4abd16ba0c28c2b9fe16acb9331187b8c362e9b8702e66b8256e9db75440a9b7186046b6ddd12fb6c46195b6b79bb9b68fb4a7b68f40a9b6838fe8b675a476b5ed0afab53de326b4dec560b4572bd9b43496ffb3b381feb2cf7d4ab2b21f2fb2649e6db2303df7b21b445eb1c5e70db1c5266ab165dfcbb0cffa76b0436f3daf4e59bead83e155ad087a01acc3ee63acb371b1aca3ec8fac8e8e69ac230811abfcde34abb99670ab9ea537ab7ef745ab5ef9dcab58ab12aac3a29caa1132d1aa07de1da9ed6d70a9c88a28a96f50f9a8ef8766a8ede7eda87b3ef2a828572aa8174b05a80bea2da6f4a651a6ce9543a6b5fd74a6983b8fa68787a9a674762ea64f92e6a62a66eba618e667a60c5295a5f1a0fca5c90744a5780014a5759b98a574f0aba551d637a54eebdea538a418a52cf2efa4dfd39ea4c4f887a492f2eba45250b4a38bfc30a38677ada37052f4a36c38cca3643249a36150eda34b1706a341478da31d822ca2ea4aeaa2d8f4a3a2b16fa9a281d31ca2676066a21dfca9a1abd0f3a18ecfb2a175fba6a15f52fda13bfee9a079858ca059b60ca0535bafa0483836a00d806b9ff383d69f5a7ba79f006f9e9ef70dbc9eee69249eeae0749ed0e3df9ea3e3e19ea061f39e1f07a49df2c76b9dee55219dcbc92d9d317b4e9ceecf9e9cc6e10d9cb68c699c9c8fd49c80cdde9c616c509bf717f89be01dcb9bc677c09bbc586a9bae01879b9775229b87785c9abcd2e79a72e2729a64d8659a5ea8f399dad52799a569599970bfad98d4fd1298bf62e098a874869854f8379830845a9822f18997f951e5972e81bf96bddde296af86ff967fb6c8955562a7953b661294bfd1cd948ebcfa
  | 7, 3 => 0xffa77a2fff811068ff6999d5ff24bf7aff0c6347ff003989fee195ccfebf9958fe9516a2fe6a77dafe1cf8cefded4c00fdd3fd81fda88834fd88a3cefd761995fd4cbc5dfd0a8757fcd9598afccb31c7fcbe9817fca7fae6fc8c2db4fc34f47bfc22bc14fb76af5efb6b5e9dfb3c2047fb0e6c5afaeae183fa865b38fa31afccfa2fa027f9e3ec59f9d7694bf93d1478f9133672f8ed0c95f8be91d8f8917ccef833f2b3f7f0967bf79dce65f6b8b88af65b58a5f60f3f1ef604eb19f5eb929bf5e125b8f5dcc8b0f5bc4270f5b81181f5b3e160f5a1c9bcf5961893f4e1a035f4cb4546f4ac7b4cf473f983f3ffa275f3f521d4f3d55e70f3c01750f2dd6b9af2a05ee8f263ebb3f23f1a3ff23d9f80f21e1f33f1c878a1f1912f01f11c7a48f0e2ab30efaa11b5ef7a2ff5ef603360ef5a1a17eee8263dee79f4a5ee5b18aeee34eed1ee1976afed3e2631ec92b479eb81d48deaf427e6eaa55eb5ea6a0c42ea252bdfe9d9e551e9d33fc3e974b2aee93e22b6e9288883e9119a29e87f455ce833f9b0e8310703e7ade279e786fc7be780c442e74b296de7169261e7075361e69370a0e66342f6e635d4dee603e9b2e5bda215e598a2e7e58436ade56f67f8e4f999bbe4dc797be487a86be4763826e47602f0e39d6589e36ec942e3145b6ae3083e7ce253d847e241aee5e23c17f8e085bc25e0147600e0127e48df8f473adf8d68f4df5154e5df33b773ded1318adddadb1add92478add3bf670dd31eb77dc9b7ebedc9086dadc385338dbb386b4dba4eb10db78dec7db4293d3db2091e7dae08523dabc02edda825b2fda61e3d8da430e50d9656dbed9448abcd93f43e1d92ad746d8e260f7d8b5f572d8607fbfd8077053d8058556d70aefd6d6ba0210d64b7b65d62f7149d4d72976d495c68cd442728dd43b6424d3e3e66fd3dc95f0d39017fad369ee1dd2b49c43d2a7eb84d266841bd20aed75d1e360fad1359a12
  | 8, 0 => 0xf8be91d8f5e125b8d8e260f7ca1bdacdc8ba8d3cc54fa6cec3b060bbb9331187b6c46195ad087a01a9ed6d70a674762ea5780014a551d637a31d822c9ea3e3e19bbc586a91fd6c898bf410dc8900486086c6ad7a80f157b6775cd8c573473b176c5aca8c598447cd52fd053152d93fd052b45c8851d9ba4d50f7bc8d4f16394b4ddac5484c724a0d4c584d784b5332c647ec41fe30d4b00827e841f5091b22290573590a01bd129f
  | 9, 0 => 0x52d93fd0
  | _, _ => 0
def htAt (s i : Nat) : Nat := fld (HT s (i / 256)) 32 (i % 256)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 14 0 (NN s)
def cutHitH (_ _ : Nat) (_ : List Nat) : Bool := false
def Z (s : Nat) := barGuard 32767 1715 pairsG r1sG r2sG mpG SD SS NN htAt idxH id 0 [] cutHitH s
theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z3_0 : ∀ i, 0 ≤ i → i < 6 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 6 0 = true)
theorem z3 : ∀ i, 0 ≤ i → i < 6 → Z 3 i = true := z3_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z4_0 : ∀ i, 0 ≤ i → i < 32 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 32 0 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z4_32 : ∀ i, 32 ≤ i → i < 64 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 32 32 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z4_64 : ∀ i, 64 ≤ i → i < 95 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 31 64 = true)
theorem z4 : ∀ i, 0 ≤ i → i < 95 → Z 4 i = true := (range_split z4_0 (range_split z4_32 z4_64))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z5_0 : ∀ i, 0 ≤ i → i < 32 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 32 0 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z5_32 : ∀ i, 32 ≤ i → i < 64 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 32 32 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z5_64 : ∀ i, 64 ≤ i → i < 96 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 32 64 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z5_96 : ∀ i, 96 ≤ i → i < 128 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 32 96 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z5_128 : ∀ i, 128 ≤ i → i < 160 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 32 128 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z5_160 : ∀ i, 160 ≤ i → i < 192 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 32 160 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z5_192 : ∀ i, 192 ≤ i → i < 224 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 32 192 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z5_224 : ∀ i, 224 ≤ i → i < 256 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 32 224 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z5_256 : ∀ i, 256 ≤ i → i < 288 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 32 256 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z5_288 : ∀ i, 288 ≤ i → i < 320 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 32 288 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z5_320 : ∀ i, 320 ≤ i → i < 352 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 32 320 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z5_352 : ∀ i, 352 ≤ i → i < 384 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 32 352 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z5_384 : ∀ i, 384 ≤ i → i < 416 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 32 384 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z5_416 : ∀ i, 416 ≤ i → i < 448 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 32 416 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z5_448 : ∀ i, 448 ≤ i → i < 480 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 32 448 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z5_480 : ∀ i, 480 ≤ i → i < 512 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 32 480 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z5_512 : ∀ i, 512 ≤ i → i < 544 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 32 512 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z5_544 : ∀ i, 544 ≤ i → i < 576 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 32 544 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z5_576 : ∀ i, 576 ≤ i → i < 608 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 32 576 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z5_608 : ∀ i, 608 ≤ i → i < 640 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 32 608 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z5_640 : ∀ i, 640 ≤ i → i < 672 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 32 640 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z5_672 : ∀ i, 672 ≤ i → i < 704 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 32 672 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z5_704 : ∀ i, 704 ≤ i → i < 736 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 32 704 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z5_736 : ∀ i, 736 ≤ i → i < 768 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 32 736 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z5_768 : ∀ i, 768 ≤ i → i < 800 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 32 768 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z5_800 : ∀ i, 800 ≤ i → i < 832 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 32 800 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z5_832 : ∀ i, 832 ≤ i → i < 864 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 32 832 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z5_864 : ∀ i, 864 ≤ i → i < 896 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 32 864 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z5_896 : ∀ i, 896 ≤ i → i < 928 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 32 896 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z5_928 : ∀ i, 928 ≤ i → i < 947 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 19 928 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 947 → Z 5 i = true := (range_split (range_split (range_split (range_split z5_0 (range_split z5_32 z5_64)) (range_split (range_split z5_96 z5_128) (range_split z5_160 z5_192))) (range_split (range_split (range_split z5_224 z5_256) (range_split z5_288 z5_320)) (range_split (range_split z5_352 z5_384) (range_split z5_416 z5_448)))) (range_split (range_split (range_split z5_480 (range_split z5_512 z5_544)) (range_split (range_split z5_576 z5_608) (range_split z5_640 z5_672))) (range_split (range_split (range_split z5_704 z5_736) (range_split z5_768 z5_800)) (range_split (range_split z5_832 z5_864) (range_split z5_896 z5_928)))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_0 : ∀ i, 0 ≤ i → i < 32 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 0 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_32 : ∀ i, 32 ≤ i → i < 64 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 32 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_64 : ∀ i, 64 ≤ i → i < 96 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 64 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_96 : ∀ i, 96 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 96 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_128 : ∀ i, 128 ≤ i → i < 160 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 128 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_160 : ∀ i, 160 ≤ i → i < 192 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 160 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_192 : ∀ i, 192 ≤ i → i < 224 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 192 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_224 : ∀ i, 224 ≤ i → i < 256 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 224 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_256 : ∀ i, 256 ≤ i → i < 288 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 256 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_288 : ∀ i, 288 ≤ i → i < 320 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 288 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_320 : ∀ i, 320 ≤ i → i < 352 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 320 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_352 : ∀ i, 352 ≤ i → i < 384 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 352 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_384 : ∀ i, 384 ≤ i → i < 416 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 384 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_416 : ∀ i, 416 ≤ i → i < 448 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 416 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_448 : ∀ i, 448 ≤ i → i < 480 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 448 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_480 : ∀ i, 480 ≤ i → i < 512 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 480 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_512 : ∀ i, 512 ≤ i → i < 544 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 512 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_544 : ∀ i, 544 ≤ i → i < 576 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 544 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_576 : ∀ i, 576 ≤ i → i < 608 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 576 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_608 : ∀ i, 608 ≤ i → i < 640 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 608 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_640 : ∀ i, 640 ≤ i → i < 672 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 640 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_672 : ∀ i, 672 ≤ i → i < 704 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 672 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_704 : ∀ i, 704 ≤ i → i < 736 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 704 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_736 : ∀ i, 736 ≤ i → i < 768 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 736 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_768 : ∀ i, 768 ≤ i → i < 800 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 768 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_800 : ∀ i, 800 ≤ i → i < 832 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 800 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_832 : ∀ i, 832 ≤ i → i < 864 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 832 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_864 : ∀ i, 864 ≤ i → i < 896 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 864 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_896 : ∀ i, 896 ≤ i → i < 928 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 896 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_928 : ∀ i, 928 ≤ i → i < 960 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 928 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_960 : ∀ i, 960 ≤ i → i < 992 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 960 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_992 : ∀ i, 992 ≤ i → i < 1024 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 992 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_1024 : ∀ i, 1024 ≤ i → i < 1056 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 1024 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_1056 : ∀ i, 1056 ≤ i → i < 1088 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 1056 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_1088 : ∀ i, 1088 ≤ i → i < 1120 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 1088 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_1120 : ∀ i, 1120 ≤ i → i < 1152 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 1120 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_1152 : ∀ i, 1152 ≤ i → i < 1184 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 1152 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_1184 : ∀ i, 1184 ≤ i → i < 1216 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 1184 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_1216 : ∀ i, 1216 ≤ i → i < 1248 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 1216 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_1248 : ∀ i, 1248 ≤ i → i < 1280 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 1248 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_1280 : ∀ i, 1280 ≤ i → i < 1312 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 1280 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_1312 : ∀ i, 1312 ≤ i → i < 1344 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 1312 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_1344 : ∀ i, 1344 ≤ i → i < 1376 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 1344 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_1376 : ∀ i, 1376 ≤ i → i < 1408 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 1376 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_1408 : ∀ i, 1408 ≤ i → i < 1440 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 1408 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_1440 : ∀ i, 1440 ≤ i → i < 1472 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 1440 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_1472 : ∀ i, 1472 ≤ i → i < 1504 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 1472 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_1504 : ∀ i, 1504 ≤ i → i < 1536 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 1504 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_1536 : ∀ i, 1536 ≤ i → i < 1568 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 1536 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_1568 : ∀ i, 1568 ≤ i → i < 1600 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 1568 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_1600 : ∀ i, 1600 ≤ i → i < 1632 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 1600 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_1632 : ∀ i, 1632 ≤ i → i < 1664 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 1632 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_1664 : ∀ i, 1664 ≤ i → i < 1696 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 1664 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_1696 : ∀ i, 1696 ≤ i → i < 1728 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 1696 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_1728 : ∀ i, 1728 ≤ i → i < 1760 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 1728 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_1760 : ∀ i, 1760 ≤ i → i < 1792 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 1760 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_1792 : ∀ i, 1792 ≤ i → i < 1824 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 1792 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_1824 : ∀ i, 1824 ≤ i → i < 1856 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 1824 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_1856 : ∀ i, 1856 ≤ i → i < 1888 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 1856 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_1888 : ∀ i, 1888 ≤ i → i < 1920 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 1888 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_1920 : ∀ i, 1920 ≤ i → i < 1952 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 1920 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_1952 : ∀ i, 1952 ≤ i → i < 1984 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 1952 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_1984 : ∀ i, 1984 ≤ i → i < 2016 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 1984 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_2016 : ∀ i, 2016 ≤ i → i < 2048 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 2016 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_2048 : ∀ i, 2048 ≤ i → i < 2080 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 2048 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_2080 : ∀ i, 2080 ≤ i → i < 2112 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 2080 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_2112 : ∀ i, 2112 ≤ i → i < 2144 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 2112 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_2144 : ∀ i, 2144 ≤ i → i < 2176 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 2144 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_2176 : ∀ i, 2176 ≤ i → i < 2208 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 2176 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_2208 : ∀ i, 2208 ≤ i → i < 2240 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 2208 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_2240 : ∀ i, 2240 ≤ i → i < 2272 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 2240 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_2272 : ∀ i, 2272 ≤ i → i < 2304 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 2272 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_2304 : ∀ i, 2304 ≤ i → i < 2336 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 2304 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_2336 : ∀ i, 2336 ≤ i → i < 2368 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 2336 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_2368 : ∀ i, 2368 ≤ i → i < 2400 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 2368 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_2400 : ∀ i, 2400 ≤ i → i < 2432 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 2400 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_2432 : ∀ i, 2432 ≤ i → i < 2464 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 2432 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_2464 : ∀ i, 2464 ≤ i → i < 2496 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 2464 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_2496 : ∀ i, 2496 ≤ i → i < 2528 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 2496 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_2528 : ∀ i, 2528 ≤ i → i < 2560 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 2528 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_2560 : ∀ i, 2560 ≤ i → i < 2592 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 2560 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_2592 : ∀ i, 2592 ≤ i → i < 2624 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 2592 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_2624 : ∀ i, 2624 ≤ i → i < 2656 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 2624 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_2656 : ∀ i, 2656 ≤ i → i < 2688 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 2656 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z6_2688 : ∀ i, 2688 ≤ i → i < 2709 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 21 2688 = true)
theorem z6 : ∀ i, 0 ≤ i → i < 2709 → Z 6 i = true := (range_split (range_split (range_split (range_split (range_split (range_split z6_0 z6_32) (range_split z6_64 (range_split z6_96 z6_128))) (range_split (range_split z6_160 z6_192) (range_split z6_224 (range_split z6_256 z6_288)))) (range_split (range_split (range_split z6_320 z6_352) (range_split z6_384 (range_split z6_416 z6_448))) (range_split (range_split z6_480 (range_split z6_512 z6_544)) (range_split z6_576 (range_split z6_608 z6_640))))) (range_split (range_split (range_split (range_split z6_672 z6_704) (range_split z6_736 (range_split z6_768 z6_800))) (range_split (range_split z6_832 z6_864) (range_split z6_896 (range_split z6_928 z6_960)))) (range_split (range_split (range_split z6_992 z6_1024) (range_split z6_1056 (range_split z6_1088 z6_1120))) (range_split (range_split z6_1152 (range_split z6_1184 z6_1216)) (range_split z6_1248 (range_split z6_1280 z6_1312)))))) (range_split (range_split (range_split (range_split (range_split z6_1344 z6_1376) (range_split z6_1408 (range_split z6_1440 z6_1472))) (range_split (range_split z6_1504 z6_1536) (range_split z6_1568 (range_split z6_1600 z6_1632)))) (range_split (range_split (range_split z6_1664 z6_1696) (range_split z6_1728 (range_split z6_1760 z6_1792))) (range_split (range_split z6_1824 (range_split z6_1856 z6_1888)) (range_split z6_1920 (range_split z6_1952 z6_1984))))) (range_split (range_split (range_split (range_split z6_2016 z6_2048) (range_split z6_2080 (range_split z6_2112 z6_2144))) (range_split (range_split z6_2176 (range_split z6_2208 z6_2240)) (range_split z6_2272 (range_split z6_2304 z6_2336)))) (range_split (range_split (range_split z6_2368 z6_2400) (range_split z6_2432 (range_split z6_2464 z6_2496))) (range_split (range_split z6_2528 (range_split z6_2560 z6_2592)) (range_split z6_2624 (range_split z6_2656 z6_2688)))))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z7_0 : ∀ i, 0 ≤ i → i < 32 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 32 0 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z7_32 : ∀ i, 32 ≤ i → i < 64 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 32 32 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z7_64 : ∀ i, 64 ≤ i → i < 96 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 32 64 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z7_96 : ∀ i, 96 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 32 96 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z7_128 : ∀ i, 128 ≤ i → i < 160 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 32 128 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z7_160 : ∀ i, 160 ≤ i → i < 192 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 32 160 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z7_192 : ∀ i, 192 ≤ i → i < 224 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 32 192 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z7_224 : ∀ i, 224 ≤ i → i < 256 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 32 224 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z7_256 : ∀ i, 256 ≤ i → i < 288 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 32 256 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z7_288 : ∀ i, 288 ≤ i → i < 320 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 32 288 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z7_320 : ∀ i, 320 ≤ i → i < 352 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 32 320 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z7_352 : ∀ i, 352 ≤ i → i < 384 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 32 352 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z7_384 : ∀ i, 384 ≤ i → i < 416 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 32 384 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z7_416 : ∀ i, 416 ≤ i → i < 448 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 32 416 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z7_448 : ∀ i, 448 ≤ i → i < 480 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 32 448 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z7_480 : ∀ i, 480 ≤ i → i < 512 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 32 480 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z7_512 : ∀ i, 512 ≤ i → i < 544 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 32 512 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z7_544 : ∀ i, 544 ≤ i → i < 576 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 32 544 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z7_576 : ∀ i, 576 ≤ i → i < 608 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 32 576 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z7_608 : ∀ i, 608 ≤ i → i < 640 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 32 608 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z7_640 : ∀ i, 640 ≤ i → i < 672 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 32 640 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z7_672 : ∀ i, 672 ≤ i → i < 704 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 32 672 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z7_704 : ∀ i, 704 ≤ i → i < 736 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 32 704 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z7_736 : ∀ i, 736 ≤ i → i < 768 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 32 736 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z7_768 : ∀ i, 768 ≤ i → i < 800 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 32 768 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z7_800 : ∀ i, 800 ≤ i → i < 832 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 32 800 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z7_832 : ∀ i, 832 ≤ i → i < 864 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 32 832 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z7_864 : ∀ i, 864 ≤ i → i < 896 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 32 864 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z7_896 : ∀ i, 896 ≤ i → i < 928 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 32 896 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z7_928 : ∀ i, 928 ≤ i → i < 944 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 928 = true)
theorem z7 : ∀ i, 0 ≤ i → i < 944 → Z 7 i = true := (range_split (range_split (range_split (range_split z7_0 (range_split z7_32 z7_64)) (range_split (range_split z7_96 z7_128) (range_split z7_160 z7_192))) (range_split (range_split (range_split z7_224 z7_256) (range_split z7_288 z7_320)) (range_split (range_split z7_352 z7_384) (range_split z7_416 z7_448)))) (range_split (range_split (range_split z7_480 (range_split z7_512 z7_544)) (range_split (range_split z7_576 z7_608) (range_split z7_640 z7_672))) (range_split (range_split (range_split z7_704 z7_736) (range_split z7_768 z7_800)) (range_split (range_split z7_832 z7_864) (range_split z7_896 z7_928)))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z8_0 : ∀ i, 0 ≤ i → i < 32 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 32 0 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z8_32 : ∀ i, 32 ≤ i → i < 42 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 10 32 = true)
theorem z8 : ∀ i, 0 ≤ i → i < 42 → Z 8 i = true := (range_split z8_0 z8_32)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z9_0 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := z9_0
theorem checked (s : Nat) (hs : s ≤ 9) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
  · exact fun i hi => z6 i (Nat.zero_le i) hi
  · exact fun i hi => z7 i (Nat.zero_le i) hi
  · exact fun i hi => z8 i (Nat.zero_le i) hi
  · exact fun i hi => z9 i (Nat.zero_le i) hi
theorem closure (s : Nat) (hs : s ≤ 9) (i : Nat) (hi : i < NN s) :
    ¬ RunD 32767 1715 s (SS s i) := by
  exact barGuard_all (dm := 32767) (T := 1715) (pairs := pairsG)
    (r1s := r1sG) (r2s := r2sG) (mp := mpG) (SD := SD) (S := SS)
    (N := NN) (htAt := htAt) (idxH := idxH) (ori := id) (seed := 0)
    (pool := []) (cutHitH := cutHitH) (cap := 9)
    (by decide) rfl rfl (by decide) SD_eq (by decide)
    (fun h => h) (by intro u ys h; cases h) checked s hs i hi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem roots_eq : SS 9 0 = rootsG := by decide +kernel
theorem roots9_no : ¬ RunD 32767 1715 9 rootsG := by
  rw [← roots_eq]
  exact closure 9 (by decide) 0 (by decide)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def RootG (s : Nat) : Bool :=
  !(coversP pairsG s rootsG) || unateBad 32767 pairsG s rootsG ||
    found SS NN idx s rootsG

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 6 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem properFail : ∀ zs ∈ rootsG.sublists, zs ≠ rootsG →
    unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : RunD 32767 1715 s rootsG) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h
    change 5 ≤ s + 1 at hl
    omega
  have hr := span_ok rootChecked s hmin (by omega)
  have hcov := coversP_ok (T := 1715) (by decide : 32767 &&& mask256 = 32767)
    pairsG (by decide) h
  have hu : unateBad 32767 pairsG s rootsG = false := by
    apply Bool.eq_false_of_not_eq_true
    intro htrue
    exact unateBad_no (y := 1715) (by decide : 32767 &&& mask256 = 32767) (by decide) htrue h
  unfold RootG at hr
  rw [hcov, Bool.not_true, Bool.false_or, hu, Bool.false_or] at hr
  rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hr
  exact closure s hs _ hr.1 (Run.perm hr.2 h)

theorem lower10 : Lower 32767 rootsG 1715 10 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst 32767 1715 := by unfold IsConst; decide +kernel
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ :=
    reach_to_run (by decide : 32767 &&& mask256 = 32767) hnc hr ha
  change (∀ w ∈ ws, w ∈ rootsG) at hws_sub
  change RunD 32767 1715 s ws at hrun
  have hperm_sub : ∃ zs, zs.Sublist rootsG ∧ ws.Perm zs := by
    refine ⟨rootsG.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd
      (List.Nodup.filter _ (by decide +kernel : rootsG.Nodup))).2 ?_
    intro x
    simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub
  have hrun' := Run.perm hpz hrun
  by_cases heq : zs = rootsG
  · subst heq
    exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (T := 1715) (by decide : 32767 &&& mask256 = 32767)
      pairsG (by decide) hrun'
    have hbad := properFail zs (List.mem_sublists.2 hsub) heq
    rw [hcov] at hbad
    exact Bool.noConfusion hbad

end PEqualNP.Outside.L_meta_25385_aux.Backup

namespace PEqualNP.Outside.L_meta_25385_aux
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def gvN (w : List Nat) (g : Gate) : Nat :=
  match g.op with
  | .and => g.inputs.foldr (fun i acc => andD mask256 (w.getD i 0) acc) mask256
  | .or  => g.inputs.foldr (fun i acc => orD mask256 (w.getD i 0) acc) 0
  | .not => match g.inputs with | [] => mask256 | i :: _ => negD mask256 (w.getD i 0)
  | _ => 0

def execN (gs : List Gate) (w : List Nat) : List Nat :=
  gs.foldl (fun l g => l ++ [gvN l g]) w

theorem gvN_bit (w : List Nat) (g : Gate) (r : Nat) (hr : r < 256)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    (gvN w g).testBit r = g.op.eval (g.inputs.map fun i => (w.map (·.testBit r)).getD i false) := by
  have hm : mask256.testBit r = true := by simp [mask256_bit, hr]
  have hgd : ∀ i, (w.map (·.testBit r)).getD i false = (w.getD i 0).testBit r := by
    intro i; simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases w[i]? with | none => simp | some v => rfl
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with h | h | h
  · simp only [gvN, GateOp.eval, h]
    induction g.inputs with
    | nil => simp [hm]
    | cons i l ih =>
      rw [List.foldr_cons, List.map_cons, List.all_cons, id_eq, andD, Nat.testBit_and, Nat.testBit_and, hm, Bool.and_true, hgd, ih]
  · simp only [gvN, GateOp.eval, h]
    induction g.inputs with
    | nil => simp
    | cons i l ih =>
      rw [List.foldr_cons, List.map_cons, List.any_cons, id_eq, orD, Nat.testBit_and, Nat.testBit_or, hm, Bool.and_true, hgd, ih]
  · simp only [gvN, GateOp.eval, h]
    cases g.inputs with
    | nil => simp [hm]
    | cons i l => simp only [List.map_cons, List.headD_cons, negD, Nat.testBit_and, Nat.testBit_xor, hm, Bool.and_true, Bool.xor_true, hgd]

theorem execN_bit (gs : List Gate) (w : List Nat) (r : Nat) (hr : r < 256)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    (execN gs w).map (·.testBit r) =
      gs.foldl (fun l g => l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)]) (w.map (·.testBit r)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [execN, List.foldl_cons] at ih ⊢
    rw [ih _ (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg'))]
    simp [gvN_bit w g r hr (hfan g List.mem_cons_self)]

theorem execN_reach (gs : List Gate) (roots : List Nat)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ (p : Nat) (w bank : List Nat), NatReach mask256 roots p bank →
      (∀ v ∈ w, Avail mask256 bank v) →
      ∃ p' bank', p' ≤ p + gs.length ∧ NatReach mask256 roots p' bank' ∧
        ∀ v ∈ execN gs w, Avail mask256 bank' v := by
  induction gs with
  | nil => intro p w bank hr hsup; exact ⟨p, bank, by omega, hr, hsup⟩
  | cons g gs ih =>
    intro p w bank hr hsup
    have hav_gd : ∀ i, Avail mask256 bank (w.getD i 0) := by
      intro i; by_cases hi : i < w.length
      · exact hsup _ (getD_mem hi)
      · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
    -- Use gvN_step directly on roots=roots:
    have hstep : ∃ p1 bank1, p1 ≤ p + 1 ∧ NatReach mask256 roots p1 bank1 ∧
        (∀ v ∈ w ++ [gvN w g], Avail mask256 bank1 v) := by
      have hg := hfan g List.mem_cons_self
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      obtain ⟨hop, hlen⟩ := hg
      have hand_m : ∀ a, andD mask256 a mask256 &&& mask256 = a &&& mask256 := fun a => by
        simp [andD, Nat.and_assoc, Nat.and_self]
      have hor_0 : ∀ a, orD mask256 a 0 &&& mask256 = a &&& mask256 := fun a => by
        simp [orD, Nat.and_assoc, Nat.and_self]
      have lift_w : ∀ z, (∀ v ∈ w, Avail mask256 (z :: bank) v) := fun z v hv => avail_cons z v (hsup v hv)
      rcases hop with h | h | h
      · rcases hgi : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨k, l⟩⟩⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inr (by simp [gvN, h, hgi]))⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi, List.foldr_cons, List.foldr_nil]
              exact avail_of_eq (hand_m _).symm (hav_gd i)⟩
        · refine ⟨p + 1, binD mask256 false (w.getD i 0) (w.getD j 0) :: bank, le_rfl,
            Or.inr ⟨bank, _, _, false, rfl, hr, hav_gd i, hav_gd j⟩, fun v hv => ?_⟩
          rcases List.mem_append.1 hv with hv | hv; · exact lift_w _ v hv
          · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi, List.foldr_cons, List.foldr_nil]
            exact Or.inr ⟨_, List.mem_cons_self, by simp [binD, andD, Nat.and_assoc, Nat.and_self]⟩
        · rw [hgi] at hlen; simp at hlen
      · rcases hgi : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨k, l⟩⟩⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inl (by simp [gvN, h, hgi]))⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi, List.foldr_cons, List.foldr_nil]
              exact avail_of_eq (hor_0 _).symm (hav_gd i)⟩
        · refine ⟨p + 1, binD mask256 true (w.getD i 0) (w.getD j 0) :: bank, le_rfl,
            Or.inr ⟨bank, _, _, true, rfl, hr, hav_gd i, hav_gd j⟩, fun v hv => ?_⟩
          rcases List.mem_append.1 hv with hv | hv; · exact lift_w _ v hv
          · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi, List.foldr_cons, List.foldr_nil]
            exact Or.inr ⟨_, List.mem_cons_self, by apply Nat.eq_of_testBit_eq; intro r; simp [binD, orD]; cases mask256.testBit r <;> simp⟩
        · rw [hgi] at hlen; simp at hlen
      · rcases hgi : g.inputs with _ | ⟨i, l⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inr (by simp [gvN, h, hgi]))⟩
        · refine ⟨p + 1, negD mask256 (w.getD i 0) :: bank, le_rfl,
            Or.inl ⟨bank, _, rfl, hr, hav_gd i⟩, fun v hv => ?_⟩
          rcases List.mem_append.1 hv with hv | hv; · exact lift_w _ v hv
          · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi]; exact Or.inr ⟨_, List.mem_cons_self, rfl⟩
    obtain ⟨p1, bank1, hp1, hr1, hsup1⟩ := hstep
    obtain ⟨p2, bank2, hp2, hr2, hsup2⟩ := ih (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg')) p1 _ bank1 hr1 hsup1
    exact ⟨p2, bank2, by simp; omega, hr2, hsup2⟩

def promiseMask : Nat := 2 ^ 21 - 1

lemma promiseMask_bit (r : Nat) : promiseMask.testBit r = decide (r < 21) := by
  rw [promiseMask, Nat.testBit_two_pow_sub_one]

lemma lower_to_promise21 (roots : List Nat) (rows : Fin 21 → List Bool) (T lb : Nat)
    (hrows : ∀ r : Fin 21, roots.map (·.testBit r.val) = rows r)
    (hncT : ¬ IsConst promiseMask T)
    (hlow : Lower promiseMask roots T lb)
    (C : Circuit) (hfan : FanInTwo C)
    (hev : ∀ r : Fin 21, C.eval (rows r) = T.testBit r.val) : lb ≤ C.size := by
  have hsup0 : ∀ v ∈ roots, Avail mask256 roots v := fun v hv => Or.inr ⟨v, hv, rfl⟩
  obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach C.gates roots hfan 0 roots roots rfl hsup0
  set out := (execN C.gates roots).getD C.output 0
  have hout : out &&& promiseMask = T &&& promiseMask := by
    apply Nat.eq_of_testBit_eq
    intro r
    rw [Nat.testBit_and, Nat.testBit_and, promiseMask_bit]
    by_cases hlt : r < 21
    · simp only [hlt, decide_true, Bool.and_true]
      have h1 := execN_bit C.gates roots r (by omega) (fun g hg => (hfan g hg).1)
      have h2 := congrArg (fun l => l.getD C.output false) h1
      rw [hrows ⟨r, hlt⟩] at h2
      have hgd : ((execN C.gates roots).map (·.testBit r)).getD C.output false =
          out.testBit r := by
        simp only [out, List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (execN C.gates roots)[C.output]? with
        | none => simp
        | some v => rfl
      rw [hgd] at h2
      exact h2.trans (hev ⟨r, hlt⟩)
    · simp [hlt]
  have hav_out : Avail mask256 bank out := by
    by_cases hi : C.output < (execN C.gates roots).length
    · exact hsup _ (getD_mem hi)
    · rw [show out = 0 from List.getD_eq_default _ _ (by omega)]
      exact Or.inl (Or.inl (by simp))
  have hd : promiseMask &&& mask256 = promiseMask := by decide +kernel
  have hm256 : mask256 &&& mask256 = mask256 := Nat.and_self _
  have houtm : (out &&& mask256) &&& promiseMask = T &&& promiseMask := by
    rw [Nat.and_assoc, Nat.and_comm mask256 promiseMask, hd, hout]
  have hnc_m : ¬ IsConst promiseMask (out &&& mask256) := fun hc => hncT (by
    rcases hc with h0 | h1
    · exact Or.inl (houtm.symm.trans h0)
    · exact Or.inr (houtm.symm.trans h1))
  have hnc_256 : ¬ IsConst mask256 out := fun hc => hnc_m (by
    rcases hc with h0 | h1
    · exact Or.inl (by rw [h0]; simp)
    · exact Or.inr (by rw [h1, Nat.and_comm, hd]))
  obtain ⟨s, ws, hs, _, hws, hrun⟩ := reach_to_run hm256 hnc_256 hr hav_out
  have hws21 : ∀ w ∈ ws, Avail promiseMask roots w := fun w hw => by
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 (hws w hw)
    exact Or.inr ⟨u, hu, by rw [Nat.and_assoc, Nat.and_comm mask256 promiseMask, hd]⟩
  obtain ⟨q, next, hq, hav_q, hqp⟩ := contraction hd hd hnc_m hrun
    (show NatReach promiseMask roots 0 roots from rfl) hws21
  have hL := hlow q next hq (avail_of_eq houtm hav_q)
  change lb ≤ C.gates.length
  omega

def graphRoots25385 : List Nat := [63, 1986, 30852, 233736, 860688, 1721376]

def rowFirst25385 (r : Fin 21) : Fin 6 :=
  ([0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 4, 4, 5] : List (Fin 6)).getD r.val 0

def rowSecond25385 (r : Fin 21) : Fin 6 :=
  ([0, 1, 2, 3, 4, 5, 1, 2, 3, 4, 5, 2, 3, 4, 5, 3, 4, 5, 4, 5, 5] : List (Fin 6)).getD r.val 0

def graphRows25385 (r : Fin 21) : List Bool :=
  List.ofFn fun k : Fin 6 => decide (k = rowFirst25385 r ∨ k = rowSecond25385 r)

lemma graphRoots25385_bits :
    ∀ r : Fin 21, graphRoots25385.map (·.testBit r.val) = graphRows25385 r := by
  decide +kernel

lemma graphTarget25385_bits : ∀ r : Fin 21,
    (109807 : Nat).testBit r.val =
      (6375855 : Nat).testBit
        (6 * min (rowFirst25385 r).val (rowSecond25385 r).val +
          max (rowFirst25385 r).val (rowSecond25385 r).val) := by
  decide +kernel

lemma graphLower25385_implies_refutation
    (hlow : Lower (2 ^ 21 - 1) [63, 1986, 30852, 233736, 860688, 1721376] 109807 11) :
    ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧
      ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
        (6375855 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  rintro ⟨C, hfan, hsize, hev⟩
  have hb : 11 ≤ C.size := lower_to_promise21 graphRoots25385 graphRows25385 109807 11
    graphRoots25385_bits (by unfold IsConst promiseMask; decide +kernel) hlow C hfan (by
      intro r
      exact (hev (rowFirst25385 r) (rowSecond25385 r)).trans (graphTarget25385_bits r).symm)
  omega

lemma deletedZeroLower_implies_fullLower
    (hsmall : Lower 2097088 [1984, 30848, 233728, 860672, 1721344] 109760 10) :
    Lower 2097151 [63, 1986, 30852, 233736, 860688, 1721376] 109807 11 := by
  exact lower_slice (d := 2097151) (dSub := 2097088) (T := 109807) (TSub := 109760)
    (L := 10) (roots := [63, 1986, 30852, 233736, 860688, 1721376])
    (rootsSub := [1984, 30848, 233728, 860672, 1721344])
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(63, 5, 20)] (by decide +kernel) (by decide +kernel) hsmall

lemma deletedZeroLower_implies_refutation
    (hsmall : Lower 2097088 [1984, 30848, 233728, 860672, 1721344] 109760 10) :
    ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧
      ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
        (6375855 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact graphLower25385_implies_refutation (deletedZeroLower_implies_fullLower hsmall)

lemma compressedLower_implies_projectedLower
    (hsmall : Lower 32767 [31, 482, 3652, 13448, 26896] 1715 10) :
    Lower 2097088 [1984, 30848, 233728, 860672, 1721344] 109760 10 := by
  exact lower_iso (d1 := 32767) (d2 := 2097088) (T1 := 1715) (T2 := 109760)
    (L := 10) (roots1 := [31, 482, 3652, 13448, 26896])
    (roots2 := [1984, 30848, 233728, 860672, 1721344])
    [(63, 6), (4032, 6), (28672, 6)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) hsmall

lemma compressedLower_implies_refutation
    (hsmall : Lower 32767 [31, 482, 3652, 13448, 26896] 1715 10) :
    ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧
      ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
        (6375855 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact deletedZeroLower_implies_refutation (compressedLower_implies_projectedLower hsmall)

end PEqualNP.Outside.L_meta_25385_aux

theorem PEqualNP.Outside.L_meta_25385 :
    ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧
      ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
        (6375855 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact PEqualNP.Outside.L_meta_25385_aux.compressedLower_implies_refutation
    PEqualNP.Outside.L_meta_25385_aux.Backup.lower10
