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

section RunBlock
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
end RunBlock

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

def pickMin (seed : Nat) (orig : List Nat) : List (List (Nat × Nat)) → List Nat → Nat → List Nat
  | [], best, _ => best
  | ms :: rest, best, bestH =>
    let img := orig.map (applyMoves ms)
    let h := hk seed img
    if h < bestH then pickMin seed orig rest img h else pickMin seed orig rest best bestH

theorem pickMin_runD {dm Y u} (seed : Nat) (orig : List Nat) (h0 : RunD dm Y u orig) :
    ∀ (syms : List (List (Nat × Nat))) (best : List Nat) (bestH : Nat),
      syms.all (fun ms => ms.all moveOK256 && (applyMoves ms dm == dm) && (applyMoves ms Y == Y)) = true →
      RunD dm Y u best →
      RunD dm Y u (pickMin seed orig syms best bestH)
  | [], _, _, _, hb => hb
  | ms :: rest, best, bestH, hok, hb => by
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at hok
    unfold pickMin; dsimp only; split
    · exact pickMin_runD seed orig h0 rest _ _ hok.2 (applyMoves_runD ms hok.1.1.1 hok.1.1.2 hok.1.2 h0)
    · exact pickMin_runD seed orig h0 rest best bestH hok.2 hb

-- Bridge: HasCircuitSize 8 fG s -> Lower mask256 xs256 (enc256 fG) lb -> lb <= s!
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

namespace SmallCert

def dm : Nat := 2097088

def goalM : Nat := 109760

def xsM : List Nat := [1984, 30848, 233728, 860672, 1721344]

def pairsG : List (Nat × Nat) := [(8, 6), (8, 7), (8, 10), (8, 11), (8, 13), (8, 15), (8, 16), (9, 6), (9, 7), (9, 10), (9, 11), (9, 13), (9, 15), (9, 16), (12, 6), (12, 7), (12, 10), (12, 11), (12, 13), (12, 15), (12, 16), (14, 6), (14, 7), (14, 10), (14, 11), (14, 13), (14, 15), (14, 16), (17, 6), (17, 7), (17, 10), (17, 11), (17, 13), (17, 15), (17, 16), (18, 6), (18, 7), (18, 10), (18, 11), (18, 13), (18, 15), (18, 16), (19, 6), (19, 7), (19, 10), (19, 11), (19, 13), (19, 15), (19, 16), (20, 6), (20, 7), (20, 10), (20, 11), (20, 13), (20, 15), (20, 16)]

def r1sG : List Nat := pairsG.map Prod.fst

def r2sG : List Nat := pairsG.map Prod.snd

def mpG : Nat := 72057594037927935

def NN : Nat → Nat
  | 3 => 6
  | 4 => 95
  | 5 => 947
  | 6 => 2709
  | 7 => 944
  | 8 => 42
  | 9 => 1
  | _ => 0

def seed : Nat := 0

def stateB (s j : Nat) : Nat :=
  match s with
  | 3 => if j < 1 then 0x63151002e5642a13902a74f89a1cc0064159545da9f3 else 0
  | 4 => if j < 3 then (if j < 1 then 0x18c56043aa3b53e094aac59244e4005091a4b3005cec81030053e249230057d4c0f3a127c36154cabb432154a144d0e154a127c3a1b40071ae75f3006ae7e8930057e04d23004ce480f3a128c36154004fd164e3a123c9619400732e75f3002ed162b3002f1164e3a7c4d244040057d4a1539fbb53e194005cd600f30057e2ca73aa4593e15476af13e194005d560153a927c2a06400722eb5f3a8bb512404 else (if j < 2 then 0x5d6be1530060e844e3005cec0153a144d0c1540019050153005ca9e4037699832154a128036154005291a4e300736e75f300224e64b30071ebea73aa46d3e15400509162b376a7cf04e4002ed204e3005cd5e15300732e6b03a14d432154a127c320f400732e35c300505124e300509304b30018c500f3aa46d3e4e4005c2bf163a138c32154aa3e13e154006aa8490300509344e3006e68489300509122a3 else 0x59282893a7ba51287400509204e300732e75e3004fd124b30071ee15f300224ea4e3005769e893a7c4d0a154002f1124b3002ed122a3e65093e1940053e3c92300732e35f300730c6283a12489c1b4005dabe153d853e26924a13e0b8154a1288320f40036524403aac593e1540022ce64e3005cebe0d300732bea63aac593e1d4005cebe0f3aac592440476a7cf0154a144d244e4a128832154)) else 0
  | 5 => if j < 30 then (if j < 15 then (if j < 7 then (if j < 3 then (if j < 1 then 0x71ae7422020028492459390014076a2480800b9d7e5c0f4aabb524892028036122448550015fa7a2c2a800afd09120f4004ce48ed0aa0031d4f44901001ccae5091294f76a48e0405003b4c6290aa002e76376855001a476a409c800e6509b640400489ea89202002e75f8585529ee8449002ab4289a48801550050a2cf52fa00399464490100173afba42a800b9d7ca215400622844e0820029f1649101001aaa145924800bad7c2a0440053dc2400aa002e75f8b031001b1a122c2a800cba9880154 else (if j < 2 then 0x6c1768907a509eaed4f865401c9a122c809428da7c32155a13b53e700aa803995ba12250014a65a242a800d2509204e4a1224801d0da802848c20055001735d9001e800d25cd601540057e9e8907a00112732701100173ac13880800e4692e75f40057e848906a0028489200d9001a4812502a800afd3512154006c2928907a002e7422583d0014298a243a800d550916404006c1768b0aa003614248055001cca92248080090a2480364006c6848907a555da9f44875401c9a12248a8007abb4c6284 else 0x50912440aa002e75f7d85527eed4ea2480a00459cc801540060a9f1620200294dc20055001428b2484a800b9d7ddaa74006b6848b0aa00311492005500173afbb444800b2509b8154aabb53e890aa80311428905529eed4f9c02aa00cc508801540050a4e8925a002e75f628550013f8aa2480800e65cebe15400682be890aa0029e8c2005500173afbc82a800e650912794005d6844e0aa00348f544921001c8c3508808005d99080154a122c9c400da802bf4a448552849f100642aa00bad8dda154)) else (if j < 5 then (if j < 4 then 0x2dd12400aa0039988a7901001165da489c800a4a3d1240400722848b202003110720055001ccafcfd129cca7a7d12405000039973af9802c9428b24900089399001e800e450a3c894005929edc0aa53e04f54fa2572aed449382aa00a1491120f400509ea8b272002e75f97031284892006c2aa00ac2589c154005e2e75f0aa002ef648b055001c7a12489c800e66228440400492428907a00284a62003d001ccb9d7dda800c450896154005362c9220200284892704100175b1d082a80088224ee404 else 0x5ceb5160aa001768b27101001ada52242a964a7bb52470500509204e20200284892704d00173afbcc2a800b9d08964040050a2ce6202003914f4590100173afc3c2a800a5298801540057e84dc0aa002e716580550017376ac018800b253e2c92400509204c0aa0038f73af84d001a9b9d7c18800e45cebf1640057e948b0aa002851244851000ba449002a800a123d124b40072282892020039973afd09284ed4f8942aa00a137196154005093e8925a509468b27055401107aa24808005b2248a154) else (if j < 6 then 0xa122c801b0aad093e8927119401afb9d082a800de3b5126e4a4a7d124007a80292892005500143449002a800a144912154aa3b5124004a802e75f79bb500188911002a800a13cd124a40057e04a60aa5ea84ed380554015fa7b702a800b9d289c15400722848b22a002e75f0a84500173afbb5a08007698c802b4007328489212002c5424485500177afc582a800d8509124b40057ddaa60aa0016c8b2005529f164910030a00b9d60801540053db8cb0aa0036175a1055001b4d8d0912800bad7d12154 else 0x509124b162002e7166d055001885d9001e800a1409d4894005cebea90aa53ddaa30c855400b5459002a800b9d8c80154005c28516202002849620089001074489c2a800afd3e2c924005ce9e4008200311422583d0014f892242a800b9d8e94154007357689202551f08920055401cca1224809428127c9c1950042a0e892025093e892583d4014276a504c9424922c9c40500509124b0aa002e75f45855000ac319002a800e648512404005c69eed202002e75f9885500188a49001e80090a2496154))) else (if j < 11 then (if j < 9 then (if j < 8 then 0x762e75f0aa509d28943055401a4afa982a800e45c6b8ed4005ce5cb00aa509da9f0e8654015fa12302a800e657a8489400509126d2020039173afcb90014244a009c9424913832045a12491246202801127520055001c8a52248a800a22248a154005d6be8b0aa0036f424490100142449242a8005aa24800f4002dd124007a001da8939055001428122496800a1449241540061976400aa003994f44901284e3449382aa00a7a2496154006c2e74207a00399204490100107449002a800b9d7d120f4 else 0x408c6280aa003917376ac100149449001e800e350912404005cebf027aa001768b20055001c8d4dcebe8007d18c80154005cebe200aa00284902005500173afbc42a8007698c501540072284dc20250912400c83d401c7b9d7c2a800b9d7deaed4007317663202002e75f8d85500142451142a8008f2ed121540050a4a890aa003914a4590100144459002a8007698c562840058a848907a0024489200551da89339002aa00e65091a404006c2e74a0aa0037742448550014245900449424fa2c9c155) else (if j < 10 then 0xa13b53e190aa80398bb448fd000bb449001e9424fa248c1550073e84882020029ede6e101001ccc457e84800b8d7dda154003b578892120030d4227055001424fa2c9c800a13b53e334007229edc2020029e892002d001cca122450800a1224960f40053e4a890aa002e7428112900144449001e9429aa249c155006f2848b0aa0039973af901001735805408800b9d7cac15400732828920200242892583d001c8b9d7c08800a1224801c40057d6c890aa002eb42271012849f449381ea00d4dcd60154 else 0xa7bb53e190aa8027f164410100109459002a800d8509164e400509144007a00284b045855000bb459142a8005da24800d4005612c4e202003915fa122d284f876a7c2aa00a122486154005cebeee0aa0029e892583d2a8ed4f8642aa00ccbb45015400509163f0aa0032f1620055001bca12241e800a13b5384e400509125327250a049f0c8554015f532902a80099cba48154005cebe1508200284892583500188a112c80800b9d7ddac34006922c5f0aa00284632003d2848f4492c80b4274a49124e5)) else (if j < 13 then (if j < 12 then 0x732c94f44a0032f7320055000dc5a9002a800e65093040400509164e0aa00333422003d001424492c6a800e6dce8440400425124007a002e75f76b450015f8b2982a800afbb54c0c4005cecf5f0aa002e7630a8110014f8624880800a12c1120f4006c3574244a509468b271014015f76a9d128008322450154a7bb5125e2028038f425390100142448fc1e800e65c67e404007329489202002848b24055000bb448ac08800b9d7de60c4007367e89202551da9f448554013f76a24848005e2249c044 else 0x689ea89202002e75f76839001165aa4880800d861a8415400509948b0aa003915fa5225001428122c9c800b9d7dda1340058e848b0aa001788b2005500173afc9c2a800b9d289c4040053d164e0aa0029e9245901001b0c45081e8005da2c5015400509164e162003574244855000fa318a02a94f8b2248022500722848c202002bf494485500173af3b42a80076a25044e400691da9c2720027e8927011001cdd8509129425122496155005cebe1509a00244892003d00142449201e94274a2432155) else (if j < 14 then 0x732e6bb2020039142449112f542768642aa00e657e9e8940050a610244a0027e8b2005500173afc002a800c2d088015400509948907a003614245851000bc449001e800b9dc2beed40052912480aa0029eed58a250014f449381e800b9d7e044e40064e848920200340b044855001424492c80800d2509384e4002ed122807a002e763af85500175a11002a800e6722e75f400733634244a0024289259012848f4493880a00bad8c2a0440052960890aa003995fa122500142489002a8ed449989c155 else 0x53e36922020039973a10fd00173a11001e800d5509121040052a0489272002bf2e530550014f9b1002a800e42dd12404003b5307720200284904493900175a11142a800d8509161540057e96890aa003993f448fd0013f449001e800ad3b5122640053dda8915a50a2c9227075401584b1002a800d7d0912154006d1768920200399b05da2529f16491002ea00d257d122240057e04e00aa00285362005500173afcd02a9b0a7bb5128750037176400aa509da940c85540173a14782a9b0a7ba524895)))) else (if j < 22 then (if j < 18 then (if j < 16 then 0x5ce2cd70aa001dab053055001b0a12241a800e6224e64040053dda9827250a629244939401a9afa982a9558b224801d500722beed53250a68400c855401735a1002a800b9d7dec15400691ea8d202002e75f768511da9f3993832a00d5d09120f4005ce844006a002848b230550015fa4a241e800b9d7c2a05400508c8400aa002bebb45855001cca129880800d853d16154006c2848907a002bf424805500142459006294251a2c80155a1289124b07a80361214483d00116318a02a800e3dcebe0c4 else (if j < 17 then 0x5cebf020aa50a26892705569ee944a142aa00a922c801540056e9eed44a0029a892305529e924491480a00e1d0912404002ed12401b2002e75f76855284ed2f8642aa00e4509124b4a128c32150228039b88a1101001428ea489c800a3a2480154005cebecf0aa0030d42271011b29f449002aa00afd3d1211400509b84e0aa00391494490100146459002a800b9d2880154a1459244e0f2802948b270550015f5da241e800e450a24894a7c593e170aa803614f4483d0015f53054089428b27c32155 else 0x5928489082002848b27101001738b35880800b9d08821540050916790aa0025c631405500173afcb9ea800a7c59244e4005d6beed0aa50924892009540165afa242a800bb50880154002a8c6280aa0039f4f4490100152449001e800d25cec81540050a04892525cebf547685540173a51142a9558b22480155a14c512190aa803910744901001428b2489c800b9ac15215400509b64007a001768c2005532ced449002aa00a7b709c1540053db892202002c74a45855284a0459382aa00a3224800f4)) else (if j < 20 then (if j < 19 then 0x7238f73afa002e75f0b05500173af8541e800bad288a15400509127907a002a5024f855001b0a522c2a800d5d0912404005cecd5f0aa0034102448550015fa12442a800da5ce844040051512400aa00399b0b9d0900188a14782a800e44891240400732e75f44a0029e8f4490129e9f449142aa0084224801540073310bb2020000175af854eaaed492249ca005da249c1040052d18400aa50944892590169ee3449002aa00da5093e89400733613f44a0039d73afbb5001425022c9c97da13b432155 else 0x6c29edc0aa00311422003d00162a4a242a800e3ddebe154005cebeed07a0029ef56e101000ed4c1e42a800e3dceb4154a7a7d16400aa802848b2711500188909001e800a7c592423400732e3422020039b4244901000d9449002a9424f85c2a06500692e75f0aa000c6280a811001cc5aa2480800a13b51a4a4006d3614244a00390bb45901001cc5ba2480800e3dcd6015476a7ce6190aa802e6f576ac100175afd082a9429727c32155005aabe890aa003914248101001c87698c50800d8509b8154) else (if j < 21 then 0x509124b04a00292892585529f35449002aa00b9d922c154006229e4007a73284892006568489258642aa00e4509163f400622844006a6c29f13448554015274a242a94f4fa24800f500551da9f2725093e190a81140173afc1604800d25ccae40400732b93f44a0000173af83cc0147449001a800a1371864040050916400ea732849e4490140186a11002a800ad45912264e4509da9f0ca802849a2005500182a14589c800afbb54ea6400722e35f76a5093e8912855401424491428800e6622843f4 else 0x5ce84401b200176892585529eed44a1c80a00ad3b528154005cebea40aa509da5c0c85540173afca9da9424493836155a7ba5248920280399424492d2a516491002aa00a7bb512264005c2beed44a00378ed31855001cca22248094f65a4912405d850a26920aa8038f70a1101001428b2488c800a122480214005093e891b20029edc6190100186a79002a800a122c84154005cebf4207a00224bb44855001b0a7c59249cca127d124e50050916400a2003994944901001424813820800a12489c254))) else (if j < 26 then (if j < 24 then (if j < 23 then 0x6f332ed0aa53dda9744901684e5200f02aaed4499480155005cebf160aa002e75f7683100121449001e800a7c7912154003b4d0400aa0028289200550015276a502a800e46ae84894005091a4e02200361424605500173afd282a800e45cebced400732848a202002848b3710100142459002a800e66f284894006c284891b200294892711500142449081e800b9d7e3a154007328463202002428b20055001c8a122c9c80076a24dc2840050a3c890aa00332ed5390100186a11142a800e62ed12404 else 0x3b5306e202003994f448fd284a3449000ca00a7a24800f400525124e0aa003994244921001494922480800a122c8a154005ce844e082002a6ed4f85500142449001a800cf509124e4005095e890aa0039175a1101001428f2482a94f65a7d12155007333342202003990944901001ccc44fc80800d153d124040073284b044a002e6b62005500162a4a241e800b9d609c15400509b84e202002e75f81031001cca12247e800a7a2c8015400509124007a0035542458550014a4593880800c45288a154) else (if j < 25 then 0x41d124e0aa50a2c9220075400bb4492c1e80091a24800f40041d2489202002a5164f855001c8d850916800b5224c21540057dda8915a53db89f20055684ed4f86412a00a14cc800f400551da9f0aa0029e8b2285529ee26e1002ab52449002a065005cebe4f0aa00176902005500133909001e800bad7c80154005cebe450aa0036988a1101001ccd862284800a12245604400525124b07a00284924492d0014274a243a800b9d7dda574005d6bf4a0aa509164e0d855401c89fa2c809424492c320f5 else 0x9fbb53c89202802e75f55055001424c13808800a7bed124e400692e75f0625522c892005540175b9d7c2a800e5d09124e40057d58890aa3b5789f4493940142529002a800a122c50154002ecc64007a0029f4144901284f84f8642aa00d14a9124040073284ca44a5094489200555dabb4f8642aa00b9d089c134bdd3dda700aa80398bc449011dabc4490032a00e653d124e4005091a4007a002e75f60855001c9b9d7dda800a14594e404aa509da9f0aa80342ed44939001cc5da2450800c352880154)) else (if j < 28 then (if j < 27 then 0xa7bb5244e0cacfdda9f4493940142449042a800a52348015400489124e0aa0024492449010015298a242a800c457e840f4005c6b8ed0aa54e2c9220055799424ea2480a00e64fd124040057dda9827200284891403d27eed4490032b4274a250e155c453dd0400aa802848b2702500173afcb82a800a13b5281d4005ce85120aa002e95f7685500125912242a800b9d7c800f40053516400aa0038f5f530550015f7abb54c800b9d09e64a400736bf4244a0028513428552bf5476a242aa00a52248a154 else 0xa7cc52489202803694244901001ccd850912800d4dcebe15400509dad220200168891405500142449385c800b9d7c2a064003b4c62b0aa0039173afbb500173a81002a800a13708015400752e75f0aa50a2c9f0e85540188a11006c800a13d5124b4e2509da9f0aa801768b2705500160a12242a800a522c8015400509f09227200284902705500106318a02a800e65ce844040061abf420aa50a369f27065401b0a4a242a800b9d7dca154005ce844b0aa002c94245855001c8b9d288080076ad5122b4) else (if j < 29 then 0x28490271803995f5da250014f8ea4880800a13848015400733614f44a0029e893f10100183a11002a800a7b7080154006c20e890aa003115fa505500173ad3b42a800a1259244e40041d7889202002e75f7785529f16491003ca0083bd51240400529124007a002e75f76b1929f024495c80a00b9c096015400509da9027200285027aa55284892590032a00a7c5912264005929e8b0aa00285026910100173af85408800e66ae8489400722e75f8120035173af8550017376ac02a95276a7c2a015 else 0x50944892003d69ea0459002aa00afd0916154a139480190aa80176892590129f167aa7c80a00b9d2c8015400509124018253e268920055401755d9002a800a52249c0940053daa92202001da8929139284892710036a00a14593e1d40052916450aa002c94f4483d001428b2484c800a1260800f4))))) else 0
  | 6 => if j < 85 then (if j < 42 then (if j < 21 then (if j < 10 then (if j < 5 then (if j < 2 then (if j < 1 then 0x692bf4f44855400ed5e22480085c6509da89200558019772a24801550060a84ed4493940142459148015576ad53e89200558014288a248015500509ca89200554014277a24841550053dda8920049401b0c4509eaed500509da9f0c0554014d8b22480155005ce848b2005540177a7c58801550053d54892005540173a14c4801550040912732005540000a7c592440400509dc8a2005540173a13b49c155c4509da922710180188a14b8800f50050912420a811400ed6daec801550069684892005540142449004a15500622e75f76855401428b2244a1550057e84ed4483d401424490028045 else 0x3b576891485540142449002a065005cddabb14055401c8a13b51240500509da942710140168afbb51215500509da89200d140182a145880155007234988a11014018fa139480155007528489200554015676a50801550053e851649101401b0a122d121550053e5c8920055401aaa14b9121550057e850581225401b0a14c5121550069284892b9014018876ad48015500002bf424483d001c890bb51240500509da89200d94016b76a24ae40500509124e10055401d5e450912405006928492449394014298bd51240500509e28927055401a4b9aec801550072748ed44901401c7a12249c155) else (if j < 3 then 0xa1409124e200658014f7abb5124e500509126e20011401165da249c155005099089200554015676a2480225000028489200d90014f72a2480155005ce84ed650554014262a249c405003d5dabb448a140142449002a045006915489200554014a8b2248015500722850244901401339748480155005cec8ed44855401584493880205006a284892005540173a1224800f5007328489271014014276a3080155006c29ced4485140173afbb5881550050912562705540164a145912155006ab494244901401b0d22ed121550050a06892105540121449002a045006a6848920055401c8a12249c045 else (if j < 4 then 0x50a2c9820055401c8a7bb51240500723554276a25401c9d2509124050072344ed4490140000a12308015400509f68927101401c89fcb9124050057e852a76a2540142481002a105006925c8920055401275da2480155007529e89200554014274a2480145003b5125120055401b076af11215500509eaed652254015fa53b51215500509de89200554014f44938401550050a672e20055684ed44a1880156a1409ea9f44855801424490034155006c29eed49225400f576af112405005092c4e1005540173afbb42a0950050a5c89228554014276b19124050050a048c20055401428b2247c155 else 0xc5d3dda8920055800ed5da249c4050050a5c8d200554014f449002a0450050916400a8054014281a2480155006aa84890a8114015fa13b530155007229f0244901400ed5da24f215500722850144901401ccc45088015500529124e20011711427690032156006c2e74276851401424497480155002ed5463200554014296a2480155005a1da892b90140142449382a105bf509da892005580164a7c591215500509dac3449394014f49224ac4050061a84400a81140175a122c80155004ba46892005540173a13b446155e65093e892005580173afbb42e155a93b52489200558014f449002a065))) else (if j < 7 then (if j < 6 then 0xa1459daa3200558014676a49124050072284ed44915401429722c8015500665daa6200554014276a24c2155004b97663200557614f76a250a1560069284a620055401025da249c4050062284ed200897114276a7c9c1560053dde892005540142449007215500509da6327101401d4a12248a155006c29ced448556c94f76a24e01560073f9942449014014276b3112155003b56c8920055401cce42ed1240500722e742971014015876a249c15500509f0892710169eed51a249c1560071e8489118554015fa1475121550053d90892005540000afd291215400509eaed4488d69eed51a4912406 else 0x509daca61a2540142449001e0150050a04f54fa254014273a248015500509548914055401a7953b51240500509d28920055401ccc4509da405005091251200554014276b6c9c155005291245200554014298c09121550050912450a8114015fa55091215500509968920055401b09fbb5121550050a2c8920031401c8af509da8950064284ed44855401c8d23b51240500722848b200554014276a249c1050072361429722540188a23b480155005ce94892005540188a13ec8015500509da89270e1401d8b9d0880155004fdeaed449014014676a249c15500509126b2005540142491002a065) else (if j < 8 then 0x549da8927055401a477a2480155005ce84ed69855401cca127d12405006c2e74276855684ed449003a196005ce844010055401caa13b5104050050a16893710140173afbb51215500692e74227055685164910030156004d176892005540173afbb4a8155005092c892710140173a13c48015500637114220055401c8a13b51a4050071ee742200554014285a2480155005ce84f5769014014277a4880155005cebf2e200554018876aec80155005ce851b20055401c89fa2480045004ba42892003d4015fa1459121550057e84ed44831401c8d1509124050062294400a811401165da2446155 else (if j < 9 then 0x72284892003d401c8b9d0880045006c284f576a25401b0b9d0a041550074a848920055401b0a146d12155a122d124e2005580142459002a065005096c8920055401c8a13b516405005cebf024485540000e662284404006f3114276855401b0a14491215500721dabb3190140164a13051215500509da89270fd400ed5aa244e155003b512502005540158a12249c155005091a400a81140188afd0a5c155afd09da893805580173a1409ea40500752848b20055401c8b3509124050062204bb2005540000a12249c104a13b5248927101801429722450155006c68516448554014297224800f5 else 0x509da5927055401428b249124e5a13b51a8927101801738b2ec80155005cddabb20031401697abb51240500509dadb650554015fa7c5912155002ed56aa4490140199a13b49c405006c285027aa254015a76a2446155003b56a8920055401427ea24801550050916400a8114010976a249c4050062284ed4f939400bb319002a04500645da8920055401429741512405006c28489100554014f74a2480155005ce8456200554014a60a24801550050a2c89200994015f76afd121550053d12450a811401b0a13c512155a1409248927101801cce4509123f50071f6142448554014f65a2480155)))) else (if j < 15 then (if j < 12 then (if j < 11 then 0x5929ec144855401429d22480155005cddab0200554014f8cc5912405003b5768920075400ed6c22480155006c2df4276855401427abb52a405003b576892f855401d4a1224800f5005cebeed5d855401c8c450a2c40500733614244901401689722480155a7bb524892710180188a13fc80155006a6e75f2005540000e4509164040053e5c892003d401c8b9d7dda405006c284892b055401025aa2480155a13b512420c85580171a13b480155006c2851444855401c8d8509120450059912512005540173a13b48031500699da89200554014f85a248015500622bf4272855401c8d250912405 else 0x53d16400a81140142449001e0450062284ed580554015fa12249e1550057e8516490556f94276a248015600721dabb448fd4015fa12248a15500592852e44855401026c22480155005094ca42005540173a11002a105006a7115fa10554015f7abb5768950067a848920055401c8c457e84ed500691da892704140173a13b586405006c284ed448c5400bb552249c155005cebe400a811401a476a249c385006c29ef576a257614276a8d12156006c284ed75225684a344900401560062284ed1f855401aaa145912405006c22cbb448554015fa13b5125750072284ed448a14014276a2484095) else (if j < 13 then 0x73799424490140173afbb4de15500509da9420055401427abb912405006c284890a841400ed5da24801450053512400a81940142974a912405006c7554276a254015c9fbb51215500509168927101401b0a13b586895007339142449394014276a24803350069e32ed449014012e5da249c1550050a628927101684ed4f93832156a128d12562005580173afbb52415500622bf420a8114014a9722480155002ed12400a8154014276b7c8015500509da893d055684ed4f224801560062212ed20055401b0c4509da4e500622844e2008140173a13b88015500559da892705540142448a02a045 else (if j < 14 then 0x5ce84f320031401429726080155006f684ed4485540188afcf1da155007328489200794014262a2480155006c348f576a2540142459142a0450050a24ed4485540158449004015500509da9b27101401a6a1224801550057dda8914055401c8b43b5124050073284892005568489270642a046a13b512400c855801a45da249c405005a9125620055401b0a13b912155007268516449014014265b05121550053e74892005540188a13b490155003b4c64016055684ed2a10032156003b576892105540142792248015576a7d127720055801a497224800f5006d3554244901400f65da2480155 else 0x62284ed27055401a4a12249c10500509eaed6d901401d4a5224801550050a687d20055690ed4fa2480156006928489270e1401c8d8509d289500509daa744901401c8b2509da8950050a568920055684f876a248015600757994244901401b0a33b5121550057e848b200554014f76a24f4155aa3b512400c8558014276a248022500002beed53055284ed4fa249c15600509da89389014014244938120450057e84c144855684ed49224801d600519eaed4490168502449003215600726bf4276a2540164a7cb91215500525da89200554015276a7d12155003b5307320055401bca13b512145))) else (if j < 18 then (if j < 16 then 0x57e84ed5305540000a4a2480154007329e8920055401428b22448155a7bb512400c8558014f65b05121550073284ed44901401a176a2480155003b57689200ad401cca1224802c500721dabb4493940164a12242a0450000285124485500173a93b48015500509daca44939401c8b8cfdda40500622848b200554014276a2496155006c284ed6d8554014f76a508015500702848927101401429a2249c1550072294ed4490140173a13b5a240500511da8920055401428b2988015500509daa62003140188a14c4801550050a048920089401427da2480155a14093e8927055800ed5e2249c405 else (if j < 17 then 0x52d12400a8154014f76a2480225006c284ed75a25401b0a93b512155a7bb53e892705580116449cc80155005dee75f768554015fa7b0512155003b576893710169eed4fa491240600509da9f270654018da1224801550050a5c8920031401427c22480155006c34973a1055401cca140912405005ce84400a84d7054276a249c40600692e75f44855400bb449382a045003b57689200554014276a8c32155006b6848920055401bda7bb512155005e2848920055401527abb5124050053d8a8920055401429a474801550057e84aa448554014a449002a0450069310bb20055401448122480155 else 0x62284ed65055401a476a5080155005929e890a811400bb562248015500509daae448554014281325124050062284892003d401424c1002a0450050a0463200554018876af08015500526848920055401997690058155000039942449010010776a24801550053df68920055401bca13b512155005ce85162705540188a7bb49c1550057e852e44855401cba122480155006229eed4910140000a12249615400722851d44901401025da248015500621dabb14055401c8b253dda8950057e84892003d4014276b251240576af13e8920055801426e3048015500509da6320055401c8a13b530405)) else (if j < 19 then 0x53dda63200554014276a24f61550050a048a20055401424b22480155d853dda92449018014293bd5124050050916400a825401428127d124e50050a62891a85540173a13b4800e50057e84e54485540186a12248015500509dadb61901401c8a550912405006a9dabb4485540173a13b480135005cd76aa20055401cce44fd124050050a69162005540174a23b48015500509da8a200554014276a249c1d5005cebeed0a8014014276a7d124e5005ce8527200556a6ed4922480156006f285024485569f024495080156004fdda8927101401b1a14b91215500509eaed2c901401cca7bb512405 else (if j < 20 then 0x53ddaae4485540142459002e1550054284892005567eed4fa248015600559eaed44901401b0c4509da1450050a1e89200554014276a247e155007339173a1101401a4c43b49c155a7c59da9f20055801b05daa91215500549da890f0554014297249124e500752bf424485540000e653d12404006f29eed4485540173972ec80155006f1da89348554015fa7cb912155005ce84ed2710140188a13b4461550071e84892004d401b0a149d121550072285164490140173a13b4f215500509fe8920055401a476a2480225000020e89200550014f6e30480155005ceaced200554015f76a6080155 else 0x6c284ed44939401424493880205006c284f476a254014f76a2880155006227eed2005540161a33b5121550052dda89200554012e7aaed1240500509dab04485540142449002a0b50073348ed449014014278a249c4050072311429710140173afbd5da155005cee14276901400ed5da248a1550069e5c8920055401c7a12249c40500509da9244909401b0ab3b51215500509ec892705540173a14089c4050050a3689271014014a449142a045006a6bf42448554014279a2480155a13b53e890e8558014276a249c14500509eaed449e54015fa12242a0650050a5c892b901401c8afd09da895))))) else (if j < 31 then (if j < 26 then (if j < 23 then (if j < 22 then 0x71ee7421f05540173a13b494155005095a8920055401427abb51260500426048920055401b0a1409124e50068dda89200554014276a38801550052e0489200554015fa13b58c895007329f4244901401428b3b4be15500509124007825401cca1224d24050050a04b04485540173a140080155006c33f424485540149449002a0f5006d684e944855401a4a1250801550073391b0a1225401428622480155006aa852e44901401b0972ed121550057e9489200554015fa12242a0450066684ed20055401425f2248015500723634276a25401c8afd0a048950050a0e89200554010976a2480155 else 0x6a6bf4f44855401424492c2a0f50057e78ed44855401c8afd3dda895003b512772005540142449002e0f5005ce8534200554014279bb512405006f348ed44855400ed5da3480155003b550892005569eed49224801e60053dda891f855401c8c4509ca40500509daab4490140142449589c40500489da89200554014276a24901550056a84ed4485540142449002a115005ce851611855401d3a12248015500509dae02005540142449005c155006c684890a81140199a14088015500691da6320055401c8a7c591240500509dad0449014015fa13bd1215500681d2892005540180a13b480155) else (if j < 24 then 0x6228440100554015fa7a242a045006669eed20055400ed5da2c8015500691da8a20055401a4c45089c1550050a1ced4490140142449302a1050053e0e8920055401a476a7d124e500726852e4490140188a13c4801550052916400a8114013190a24801550071f1142200554014299224801550050a02891f855401424b138802050053ddab04485540188a13d5da405005997689200554014276a40801550073284892003d4012176a249c15500622851b20055401c7b9d7dda1550050a048924055401165da249c40500692848920089401c8b9bb5764050050a04e0200554016476ad512155 else (if j < 25 then 0x53dda8924055401424493880105007231142200114014276b358689500509da9f44875401b0c450a0415500521da89200554014ba12248015500429eaed449014014245a248015500733494244901401c8d83b576895005091654200554014276a24dc4e50050a6289200554000091224801540072285164910140188a1409ea405006c2853444855401c8a12248a4050050a0c89200554014276a249c1550050912612005540142492249c045002ed12400a83d6850251a249c406005cd76400a811401a4a22248015500525da892003d4014f8622480155006c3114276855401c8d3bb512405 else 0x292892003d001888b2ec8015500692846320055400005da2c8015400561da89271017614f76a7d12156006ea84ed44855684ed449788015600509ec8911855400ed5da2456285004ba492144855401429729880155007227eed448fd6f54276a249c15600509da9b20055401a4a7a248009500539da8920051401a476a247e15500509dc892710169f0276a4912406006aa848920011401b05da242a04500509da892583d4015476a249c1550000284902005529ef576a7d1240600001da6314055001a45da2480155000038f73af85529f1b4fa24801560062284562005540000b9d7deaed4))) else (if j < 28 then (if j < 27 then 0xa1459248927101801428b248800650069332ed200554014f76a4912405006aa84ed492254014276a589c155006f34942448554014254a2480155006c2e7428b055401b0b9d09da0c5006c348ed44939401b0c453dda1550061a848b20055400ed5da24501550050a5d2444855400ed5da24800f5005cebf164485540173afbb5120c5a13b52889270558015976a24801550052912400a82540188a13b480315005ce84ed200754015fa13a5121550073284c044901401c7b9d08800c50050a4489200554015fa1224a2155005ce84ed2f855400ed4494880155006229ef5769017114276a8c80156 else 0x509768b200554014276b6c9c405006c284ed448756bf4276a49124e600692848a200554015fa14b9120f500509daca448554014f812491240500692849f44939401428e224801550000284892583d001c0a122480155004097689140554012e449cc801550050a049f0b8554014f45a248015500722e742768fd40163a13b51215500509da63140554014244950800f5006c684e944855401427abb5125f5003b5788920055401c7b9d7e841550057e850b44855401c8a1305124050053e62892005540173afd09eaed500519da8927101400fa5da248015500622beed5d8554014f76a249c155) else (if j < 29 then 0x53dda89270b168ced4fa24801560072284aa44901401a4b9d089c4050069310f576901401a476a40801550072284ed5310140173a13b4841550053e4489200554014276a7c32155005ce84f62005540105812ed124050050a348920055401cca14a9124050000176892003d001428132912155005ce84ed2005140188a13b8801550056a2c8911855401165aa2480155005ce852e270554015576a24801d50040978892005540149a1224800f500691da892405540188a11002a1050072684892001140173a11002a05500509dada4485540164a13151215500415dabb4490140188a13b586405 else (if j < 30 then 0x509da892f1014014f76b29121550069284b044855401b0a13d912155005094c400a811401b0a13b512145006228ced20055401427abb51242500459b08920055401c89fbb5124e500562848927101401a476a249c15500723495fa122569eed44a1480156007229ec144901401c8974851240500509ecf54490140142972248036500509248b20055401b0d2621da1550069284891f8554014e76a2480155005091689228554014276a24461550050a2a89200554015f76ad512155006c284890a8154015276a249c40500509da893b9014015fa122c2a04500509da8d24055685164490044156 else 0x69284892405540166a12249c155005ce84cf200554012a76aed1240500425da89140554015f76a9880155007628489200556f74f76a248015600224e6400a811401427da6080155004fe048920055401c8b9d09da4e500509da59271014014276a243c1d5006b684890a8114014276a349c155005ba84ed44855401b0a140912145005cebeed58055684ed4ea2480156004fdda8920055401c876a24e640500693334220055401b074aed1215500591dabb44855401c8a14b91240500692128920055401b0d2509124e5005929ec544855401425da24800f50062298ed20055401b0b9cf9da155)))) else (if j < 36 then (if j < 33 then (if j < 32 then 0x57e84ed4a055401428b44912155003b5769820055401b090bb51215500509da892d901400bb552249c40500692849020055401c8a12249c205a7c5912400b855a85344493880156a13b53e8927109a85164490032156004b91251200554014293a249c40500509d2890b8554014276ac51215500485eaed44901401577abb51240500509124e0a83d40173a11382a045a7c09da9f4485580173a13b4801550057e84ed6f8554014249224800f50072284e5449014014276a2c9c1550041976632005540188a93b480155003b5766327055401b0d3bd5da8950053dda891185540188a13b5cc405 else 0x6c284ed449b94015fa131512155007235342449014014276b4d12155007228489200194014276a24f24e50050a04892d901401b0a13b51215500509fced449014014244900401550050a2c8920089401a4a12249c155a14593e8927055801ccafd091215500559da89271016bf4276a243215600509e28920055401b0d26228415500753914244901400bb5a224801550071e8489200554015fa13c91215500509ea8927011401427abb5124050047576892005540173a140880155007229f2e4490140189a1458801550050a368920055401caa7bb5124050050a24892005540142449142a005) else (if j < 34 then 0x6c348ed448514015fa13ed1215500622852720055401207abb512405005cebeed670556848927100320460073285164490168516491002e156005091256200554014298a24800f500529768920055401a476a2446155006aae74276855401424492c801550050a2889200554016976a2480155007228489200117614276a250e15600441da89200555da9f449d080156006c2850244855401448b224801550057e84ed448894015fa13b512715006228516270554012e5da249c405d8509d2924485580000a122c9c154a13b53e4e2006580173afbb49c1550050a04f5449014015576a2480155 else (if j < 35 then 0x53d124010055401aaa12244015500519da892105540142459002a005005092c40100554014276a2480315a13b5125f270558014276a24561550053ddabc4490140173afbb54c15500723492e44901401ccafd09da895a1459ea8927101800c15aa248015500691768914055684a3449382a04600549da89200754014276a54801550053deaed44901684ed51a248015600509daea44901401427abb5ba40500459768920055400ed5da24800c500721da89289014014f8da24801550060a9eed44901401885daa880155005cebf5276855401c8a13bd12405005be84ed200554015fa23b512155 else 0x57e84ed31855401c8a7a248004500509da89238554014276a2496405007339188a1101401b0a7c09121550050a68892710140173a14b9ea405006f285164485540188972ec80155005dec8ed44855401a29fa24801550050a2e8920055401737698c80155005d684ed2005540173a13b48a15500509da892305540188a14f5da1550069284ca44855401428122480315005a9da892005540188a13b49c4050053e04f5449014015f76aed121550062284ed3c855799c8a127d124060057e94890a811401428b18c8015500622aced20055401b0a7bb51215500596848920055401b3a13b5124e5))) else (if j < 39 then (if j < 37 then 0x6c2852e7aa25401c2a13b51240500561da8920055401428822480155a7bb5468920055801424491440155002ed124e20011400ed5f98c8015500569da892005540173afbb42a0a50050a04c344901401527b224801550071e8492200554014277224801550050a2c8a20055401428da48801550050a2c9f4493940000e657e848940073ae742769016852e492249c406003b578891405540188a14089c405006c2e742970554014f44958801550050912400a841401b176aed12155003e97689140554015f812ed12155005cebf2e448554014276b0d12405005a1da89270554014276b3594895 else (if j < 38 then 0x50a2c891f8554014a45a2480155005cecd4220055401c8a13a51240500722848928901401a4813d51240500519da89200554014f9fbb51240500732e74244901400ed5da49124e5005ce85162710140188a14584615500509da893e1b9401c8a12248a045004b96a89200554014a76a249c15500723613f76a2540000a122496404006c3494244851401b0d23b51215500509da893e0554014276a502e155b9d92beed4485580000bad08801540057e84ed4505540142449001e005002d912400a8114018872aec8015500691eaed44901401a4a12244615500509ea8b2005540164a13b524895 else 0x6a6e75f448554014f77224801550057e850f44855401c8b9d7dda895006f27ced448554016aa1224801550045976922005540173afbb53e1550050a2cb044855400bb44914801550057284ed44855401b0a13b51a155007238f73a1101401c8a142d124050058684ed448554014276a24be4e5005ce84400b055401468122480155005ce84400a83d401426e2248015500509dadb20055401c8c43b57640500509e689200314014278a348015500722bf428b225401cce4d09124050053ddac3449014014c76a24801550062285342005568516449383c15600509eaed46901400ed5da24ae405)) else (if j < 40 then 0x509daeb449014015276a2480155005ce84ed25031401b0a12242a0f5006c2e7420a81140173afa242a04500666e6ed200554014276b9912405005cddabd20055401a4b9d0880155006c284ed458554014276b4512405c453dda9f200558014276a24803a5bed09da892705580167a12248015500691da89200c5401b076aecc61550050a3a8927055401427aa24800f5005cddab044855401885d9002a045005929eed49225401428136c80155006c2cd42448554014276a609c15500666851620055400f576aecc6405006a9dabb449014011684a2480155006c2851644939401c8d85ce84ed5 else (if j < 41 then 0x50a5c9420055401b0d2509121550053db8892005540142449002a135a7bb5248920061801a476b0d124050057e84890a8454014f76b6c801550071eef4220055401427b2249c405005091656200554014276a2452155005ce84ed1405540173a13b4800f50054a048920055401cca12251040500721dab5449014014282bb53e89500722848b20011400ed449d89c1550057e84ed47055401bea13b512155003b512791605540163a53b51215500562848920055401a4c43b49c4050050a2c8924055401424493880055005e6aced200554015aa145912155a1249124e2001180199afd09da155 else 0x5265c892005540188a13b49c125a1249124520055801a4b9d3c80155006c284ed4483d40188afd09eaed5005bad0ed4485540173a1415da4050050a2c892705540142769648015500509eaed448a1401b0c450a2c15500691dc8920055401a4812243c15500003614245855000b5449002a045006c2e75f768556852e449003215600509daa75310140188a13b4801d500722e34276901400c15da24801550062284ed2f855401c976aed1240500655da8920055400ed3190050155005debeed448554014aa12249c1550071ee75f200554014276a249c4250062684ed2004940173afbd5da405)))))) else (if j < 63 then (if j < 52 then (if j < 47 then (if j < 44 then (if j < 43 then 0x50a349820055401449722480155006c2850576a257914276a791240600509da892004d400bb5522480155006928489200c5401424492c800f50057e848b44855684ed4fa248415600622852e270554014276a2498155003b576a6200554015fa14c5121550050a4e8920055400ed449d0801550062284400a815401cca122480015005ce850581101401a677a248015500002e7422003d00142811648015576a7d127327055a9f4276a8d124060050a5c89200896852e4fa249c156d5509da92449018015ba13b51215500509da89200dd684892005c2a066007231142768fd40173a13b494405 else 0x50a3a89118554014276b351215500509da89271014014fa1224801050053e2c9244901401687abb51240500509e8ed44901401b0a141604895004597689140554014276a24f21550072284ed4a101401428b27c2e1550000361424483d00187a13b4801550069688892005540163a550912155006931142271014015676a248015500722b93f76a25401b4a12249c155bdd929eed44855801cca14b9124050050954632005540188a13b48415500692bebb448554017da13b5124e50062284f6200554014276a24800e50050a5c89258554012176a249c4050062284ed20051401427ba2480155) else (if j < 45 then 0x6c284f574a254017376aec9c1550053e4e8920055401cfa122480155005c284ed44901401428b369121550050a5c632005540142812249c405005ce94ed200554015fa7bb5248950050a2cca44855401c9a13b5123f50057e84a9448554014281224f2155003b572892005540173afbb43c1550066a84ed448554019fa1224801550058e848920055401a476a24803a50062284e527055401b0b43b51215500733914244901401165e22480155e4509da8920065801b0b9d09d2155004b976892005540173b2509da155a13b53e400c855801429ebb5121550053e2c89270554014276a24f26e5 else (if j < 46 then 0x6928c8920055401428b2489c1550071e84891f0554014276a2494155006ba84ed44855401b0a53b51215500509124011011401c8a23b512405a127d124e0a811801c8a13ed1240500509da893e1e54018890bb4801550050a008920055401c8c4509da4e50069dda8927055400e55da24801550069dda92449014014a7abb512405005928489100554014276a24ae4e5005ce84a420055401bca14b912155005ce852a7690140142822249015500509da89300554014276a24c4155005ce84ed1f0557914276a7d124e60057ddabc448554015476a249c4050069f10f57690168489200642a046 else 0x509eaed4c101400bb449002a06500721dabb4490140173afc09da15500722948920011401429a22480155003b570892005540144449002a0450062284ed37101401a4a136c80155006c2851644851401d45da248015500509ec8920075401cce453d124050065f10ed2005540188a11382a045005ce851d2005540188a13b48015500002e74a20055001b0a14a9da8950072342ed44901400ed4fa24e64e500509d28942855400ed59224801550050a2c8911855401429722880155002ed124e10055401429727d124e5005cebeed160554014276a589c4050053dda893c8554013490a2480155))) else (if j < 49 then (if j < 48 then 0x72684ed44939401c8de509da8950057e7eed44855401428b3b5244e5a7bb53e8920055b554276a7d12156005091889200554014298a242e155005ce954220055401a4a92248015500722bf429722540000b9d7dda1540050a70ed448554014247a2480155002ed12400a811401a476a2480135006928489200e9401c8812ed12405006c2851d4485540142972247e15500691da8926055401c8a13b4c640500429da8920055401b0a13b5301550042554892005540173a14b89c405004fe2c892005540164a7bd5da89500622850220055401cca122480045006c340ed44855401a95da2480155 else 0x509da98200c540188a7c08801550050a2cf52a1014014244a00801550062284ed200f5401b0a550912155005eae75f76855401c8a13b5144050053e688920055401d8afd0912155006f284890a81169f024fa2480156005d694ed2005540199a14b880155005ce85162005540173a13b4800c500691da892710140188a7bb48015500509164e20055401aac4509da15500509da891308d40000b9d7e04154004ba128920055401b0a14b9124e50050956aa44901401a476a24f2155a13b5125c270558014f8b22446155003bd76892005540142972c11215500508c6400a8114014260a249c155) else (if j < 50 then 0x72284ed448fd40188a13b49a1550057e84f144855401428b248461550053d8292449014014281224801d5006f2beed44855401b0d0509121550059a8489271014014276a249c1250071ebf42448554015fa13d5da895006c6e7427685540173afd0a041550057e851b4485540199a139480155005095489270554014276a989c155006c2851644855401b0a13b5120c5000028516491390014276a349c4050065f11422005540142451002a045004ba448920055401429722490155005093e89270114014276a24801d50071e8489200314014276a24be155005cebf427685540173a1408800c5 else (if j < 51 then 0x509123f0a81140142972249c155006a684b044855401c8c44fdda40500509124e1b055401a4c43b4801550072284ed582254014997224800f50069284892004d401b0c450a5c155006c684f576a254015fa1409ea8950050912400a81540173a7c588015500509124e2003d40173a113880045006928489260554014271a248015500723535fa1225684ed50a248015600509da8b27101401d1e650912405003b57663271014014294a24801550057e84891005540188a14b9ea405e44fdda9f449018014f60a249c155004ba42892705540188a13b48a155a13b53e170a8059daa3449d880156 else 0x72346ed44901400bb449448015500692848927101401ccafd09124050050960890a811401428b224803150053dda892007540173a13b5244e500509da89210556849f449002a0760050a0aed2c901401739f3b480155006aa84ed4fa25400bb449142a0450053dda892f8554015fa1224ac1550069284893c8554014f8b3d512405a145946892005580142449384a155005cebf4f7685540173afbb4d215500509ec8920055400ed449b8802c5005093e8922855401c8afd0912045007233342769014014276a24801450050a2c8820055400ed449cc9c1550072212ed4490140179a13b480155)))) else (if j < 57 then (if j < 54 then (if j < 53 then 0xa127d12400a83d801c7b9aec801550042d768920055401c8a7bb5123f50050a2c8923055401737abb57640500509ca8927055401ccc4509124050050a04892105540188a14589c4050050a0b022c901400bc55224801550057e9ef576a2540000a122c9c4040057e2cbb448556c94276a4912406006c3114272855401c8a13b512485005cebeed27101401b0a13add28950050a5c892583d40199a11002a045005ce84ed2b9014014286a24801550050a048920051401cda122480155006c29f164485540109449002a045006c2848927011400bb5522450155005d6954220055400e95da2480155 else 0x509da8913855401d5a122480155006c34eed44855401c99fbb512405004b9788920055401d4a12249c1550054dda89200554014293a24800d50053e5c8927055401b0a13b5125750050a60ed44901401c8a1405123f50062284400a83d4014f97249124050069deaed449014016d76a248015576aed24892710180142449202a045004b97689140554012e5da24800f500509dad7448554014f449002a0550050a2cc344901401bca13a51215500509125a2005540142492249c205006aae74276901401b0b9bb57615500622cd422005540173a1114801550050a4f0544901401424491880155) else (if j < 55 then 0x691da8920075401424fa2c80155006c3554276a25401cda13b512405006aa848920081401a476a24be155005099e89200554014249224ac4e5006922cf544901401c8a14c51240500623034220055401a4b9d7dda1550053dda8921055401b0a1459241550050a5cca44855401a7813d51240500509da89200ad401b0a12248a15500485da89200554015776a24801550057e84890a84140142449382a0650072284ed44939684a344938800460053dec89200554015a8b224801550057e84ed61a25401424922480065006c1eaed5da25401c8d862284ed5006b284ed44855401999e3b480155 else (if j < 56 then 0x50a5c8911855401428b36c80155005cebeed60055684ed44a1c801560057e04c7448554014277a249c1550050a04892005540188a13b4501550062284ed2003d4016876a249c4050072348ed448fd40173a130480155a13a5248920055801c9b9d09da405007368502449014014276a244c15500509da8937101401c8d22ed124050051a2c89200554014676a24800c5003b57889200054019776a248015500509124e0a81140121812248015500509da89200556c94f76a4912406006c311420a811401424495cac405002ed16400a8114015fa13b91215500693114220055401c8a122d12405 else 0x691ec8920055401b0a13a5124e5006c284c1448554015fa13b5b615500425125120055401c9d8509da895007229eed4493940142562248015500732848920025401a476a2480145a13b512400c82580142449002a035006c2852e448514014f76a7d244050053dda8913855401c876aed12285000039b4244901001a4972249c155a14594692200558013f76a2510405000034973af8550014276a508022500551da8920055401429a224800f50050a048937101401428b39480155003b5125127055401429cbb51240500509da9c200554015fa33b512155003b5127739901401424494c80155))) else (if j < 60 then (if j < 58 then 0x73284ec449014014f449382a045a13b53e89270258014f76a2480155006aa84ed448554014276b7480155005ce84aa20055401a276a24801550053d2489200114014a76a249c4050054a2c8920055401c8a13b59489500509125d270554014247a24800f500509da9620055400bb448a02a045006c2848b20055401424493858045004fe5c89200554014276a24f840500692e74220031401b0a144d1215500691da8921055401b3a13b50a155005d6e742200554014297a24800f5005093e892003d40188a1415da4050053d9e8920055401c876af11240500481da892005540186a13b480155 else (if j < 59 then 0x30d422005500173a14b8801550065e848920055401b0a13b54c1550057ddaa64485540174a13b480155004fdda892000540188b43b48015500509124e1c8554014f8122480155003b57694200554014280a24801550071e84a62005540142652242a0450057ea4ed44855401a4a1224801d500509eaed5310140142812249c0450050a3089200554014276a24803d50069284892f855401a4b9d7e841550059ebf42448556a94276a24801560058e84890a811401bea1459121550050a6a8920055400bc449002a045006228505811014014f76a24dc4050073284892005d40000c4508800f4 else 0x509125127055401075aa24801550046d1273200554014299bb480155a13b52e892005580142973d512405a7bb5288920055801b0c4509d215500622c9427685540184a13b48015500509da89228554014276a249a1550072348ed44939401428ea249c405006c29ec144855401b09748512155d9509da8920055801c8d2509123f500509da9827101401c8a13b51223500722851544901684f844900321560057dda89270b14013390bb48015500731768920055401427abb5122450053deac1449016c94276a7d12156004ba42f5449016f54f76a2480156006c284aa448555dabb4490032156)) else (if j < 61 then 0x69284892105540188a14a9da4050050916400f055401c7b9d089c1550050a168927055400fb5da248015500691da893710171142729388015600621dabb27055401b0a1224280450050986c144901400ed449d89c4050073a84ed4490140173a139480155e4509da9d44901801c89fbb51240500509da8940901401a4a122480145006c1da89398554015ea13b51215500691da8920055401428742d124050062294ed20055401b0a14b9121550062284e672901401aaa7bb512155003b57689200894014274a249c155003d5da89399014014276a24c45f5006c284892003d5dabb4fa249c156 else (if j < 62 then 0x5a1da892f855401cca1224a84050062284ed270ed40142449002a0750050a3ced44855401b0a139512155005ce84ed200d1401428b224f2155003b51282200554015f5daa912155a13b51257271018014276a34801550055a2c8920055401d4b9d0880155b253dda9f448558019ca1224801550059a428920055401a476a7080155a13b5126220055801a577224801550057e852744855401cc76aed12405004fd12400a811401c89fc09124050068a8489200554014aa12249c405005ce844e100554014276b5912405afd3dda9244901801428b224801350048dda8920055401424493080155 else 0x73284891f85540142449002c1550050912400a83d401aad23b512155005ce84400a811401c8b9d0a04405003b56a8927055401427ea249c15500722851b4490140142459382a045006c29f2e448554014276a2c80155003b56a9244901400ed5d98c80155005091640160554014297224803150050a048d200555daa3449cc80156005cdda893c8554014f973d512405a14b946892005580166a12248015500622851d2005540188b253dda1550053dda892285540173afbb42a0c50048512400a83d4015fa13b5120e5006a6e7422005540173a11002a0650050a2c8927101401c8b9d09da405))))) else (if j < 74 then (if j < 68 then (if j < 65 then (if j < 64 then 0x6d284892710140188a550880155005fe84ed200554016b76a24801550050a5cc34490140181a12248015500002851e44855001b1a13b5124e50057e85024493940173a13bc801550050a5c8925901401428122c8015500409766320055401b0d4d09121550053dda923510140163afd0912155006c284890a819401c8d8509da8950072284892008140142449003c0f50069242892005540000e62ed12404006f1dabb44855401c8d2509124e500622852e27101401cce457e848950053d86c1449014015f972ed1215500511da8a20055401c8a13c512405007238f4244901401d4d850912155 else 0x50912401603d6a4ed449002a016006925cf544901401b0a13bd121550073284bb4490140110449cc80155d8509da8943055801a476a248a1550050912400a835401428c234801550062284e527101400f576a24a24050059a9e89200556851676a489c4060062285162005540188a13b4800c500002848b20055001c8a1224ac405005cebeed200554014276a2456285005cebf16768554014276b351240500485da892003d401a4a1224dc40500509da8925031400ed5da2880155006c284890a811401c8d850a04895003b5769f4493968516449003a156006928489200557894276a2480156) else (if j < 66 then 0x509da9427055401a9afaed12155a128d12400a811801c8afbb57689500509f2f6449014014276a244a1550050a0489140554014281224800f50057e853444855400ed5da247e15500723614f76a254014697224801550050a6eed20055400ed59a248015500691da89409014014276a24c44050050a04f54487d401427d2248015500622bf42768554017376aec9c405006c3492e448554014f449002a0f5e4509daa34490180173afc0880155007222cbb44901401b0a13a512145006c1da8928855401cca13b5123f500509da89140554014f76a2c8015500509da892003d401a4a127080155 else (if j < 67 then 0x29e8b2005500000a1224800f4007228489200414015f5da242a04500665dabb20055401584493840155002f97689200554014d76a248015500691da8d20055401cca12249c155006c1dabb4493969eed4922480176002ed124e20081401427abb59889500732849244901401b0a7a242a0450050a2c92271014014276a2494405003b576b04485540142449388a4050050a5cdb2005569f164fa248015600723453f44901401aad2509121550050912460a819401424490062045006c711427685540188afd0a041550050a0aed4490140000b9d7e2c15400002e75f768310000090a24800f4 else 0x622bf4f76855400ed44998801550050a42892003d4015297224801550050a048920035401a476a2c80155005a1da8920055400bb56a24801550053dda8914055400ed449a4501550053dda892003d684ed492249c1d6005ce84e920055401c8a13b912405a13b53e9244939801d19fbb512405005ce845120055401a4b32248015500425da632005540175a11002a045afd3dda9f4485580173a11142a045005098a892705540173a1458800c500509da893115d40188a7c58801550050a0b0244901401428b2244c23500622844e200114014276a2c8a155000039942448fd0014276a24800d5))) else (if j < 71 then (if j < 69 then 0xa7bb5124e0c855801c8a1459123f5005098289271014015fa13b5121d500621eaed5d90140000a122c8a15400002848920035001a7c43b4801550050912612b055401b0a13a5121550059284ed44855401c8a33b512405005ce852e2003d401b0a1224a2155a7bb5125f200558014fa122c801550050916692005540188a13b4ae40500511da8927055401c8d8691da89500509f6892705540168812248015500692848922855684a3449748015600509eae94490140173a142c801550050a2c892007540188a13b5244e5003b576ab4490140173afd0a2c155005cebf4276831400ed5da2490155 else (if j < 70 then 0x5cebeed1905540142953b51240500509f08927055401315da248015500509da891f055401065da248015500722b94276a254018ba13b476155a1395124e20055800ed5da249c1550050920892005540146449002a04500565da8920089401c7d85ce84155006c2850b44855400ed4498c50155005c67eed20055401b0b9d09eaed50071ee75f44855401c8a13b5b6405006ab1142769014014a449382a045006c310ed5d85540000a7a24800f4005cebef576a25401427cbb51240500529da89200554014273395124050057e9eed44829401a4a122502405006228445200554014285bd512405 else 0x509da941185540142552249c405a1459da9f270558014276a249c3b500722a4ed449014014276a989c40500549da9f20055401429540912405007234973a1101401a076a2480155005ce2cd420055401428b22484155005368489200554015fa12242a05500519de8920055401b6a13b51240500509b6400a811401a4a1234801550050a5c89200dd401428318c8015500691da8914055401427698c9c15500691da892003d4014a81224801550050a2c89200517614276a49124e6a1249124e20081af564a13b512156006c2852e4483d400f576a24a0405002ed168920055401425222480155)) else (if j < 72 then 0x50a2cd7448554014297224f21550072361a4a12254014276a24be575005092689200554015697224801550050a049820055401b1a13b512145004aa40ed4490140152449002a0450062284c120055401c9c4509da405006a2a48920055401b076ad512155006c2848b0a8114012e90a249c405006920aed44901401425a22480155a1249125627101801a4a122c80155003b578b544901401a45d98c801550050a3a8920055401b0a7ba512155005929eed44855684ed49138321560057e84f644855400f576ad5124050053e84892003d40142449a4800f500509da98200554015fa13b512145 else (if j < 73 then 0x509da992005568531492248015600692e75f200554014276a2506155a7bb53e890b855800ed5e18c80155004862c89200554014aa12248015500722851644939401426022c8015500509124e20095400ed652ed12155a13b53e890c855b11427690078156007327e8920055401cca122480005005092c8927055401cce550912405a7c5912400f055800ed5d98c50155006fe84ed44901400ed449cc9c4050046db089200554014f953b512405003b5127620055401426aa24801550050a5c892710140163a52242a045003b51279398554014244938803650059a84892003d6c95fa13b524896 else 0x72176aa44901401a0a12248015500693115fa105540188a7b0480155006225d21200556e74276900321560066e84ed44901401428b2244c1550050a2c8937101401425022480155003b57a8914055401c8a149d12405bed3dda8920055801a4a1224501550069284892003d4014272a249c40500529da89228554014f8ea24801550050a2c89200554014276a24800c50062284aa200554014276b2d121550050a22893c85540173afbb42a015006c33d424485569ec14fa2480156a13b52489270798014f76a6080155c5509da8920055800ed4c1a480155005ce84ed200cd401c8add09da895)))) else (if j < 79 then (if j < 76 then (if j < 75 then 0x50980892003d401424493880065005ce84ed20089401cca13d5124050050a2ced4f93940188769cc801550072284ed449e5401a4953b512405a13d5da8920065801cc9fbb512405006c284ed4a055401a476a247c155006c1dabb4485140188a14b88015500722aced44901684ed449c080156007528489271014015fa13b5126e50050a04e9448554014f6aa2480155005cebf2e7685540199a13b49c155a145924400f0558017376a24dc40500509eaed4a1014015fa13b5121550050a048920031400ed5da244615500425da892705540188a13a080155a1409125720055801ccb9d0880155 else 0x50912401108140188a7bb48012500509d6e9449016849f449384015600509da8920099401cfe4509124050053e2c8920055401a476a6080155006aa8516448554014244938800450053ddacb4485540173a23b480155a13d5da9f4493980173a13ec801550050912790a8116851b4fa249c1560050a3a92200554014f76a6480155006d284892005540000a52248a1540073361424485540142449f880155007225cbb4490140173a13b54e405d8509da890c855a8489200803215600722e75f76855401b1a13b51215500509da9227065401a9a12249c40500509f489140554015fa140912155) else (if j < 77 then 0x50a508920055401a4972249c405006229f2e200554014aa12248a155a7bb5127020055801b0a23b51215500509dadc200556849f449002a066006c284fb44855401427f3ed1240500509da92449394017376aec80155003b512512710140178b9d088015500622844e10055685167aa7c801560057e9eed4485540173a51002a04500509e0892005540000e64fd1240400509de8927101401447abb51240500509f6f5449014014a76a2c80155a7cb93e8920055b1988a13b4801560065f10e520055401ccb9d09da40500002e75f97055001b0a13b5122250062284e52005540142582a512155 else (if j < 78 then 0x3c576892005540173afd0a5c1550053e32ed44901401a476a25061550050a2c8922855401c75da2480155006d3554244855401a9c450880155003d5dabb4490140173b257dda155005ce04bb2005540188a11002a06500723114276901401cde4d09124050046d768920055401b4a13b5124050069dda8920055401428f4751215500733614276a25401a4afa243c155006c69eed448554015fa7c0912155006a6e75f768554014245a249c1550050a4ced44901401c8a14591223500509da892b901401d4c4508801550050a628927055401a4b250912155005ce9eed2002540173a14b8800c5 else 0x409eabb4490140188a11002a045a13b5121e0c85580192a13b51240500723114281101401a48b1508015500691ea8920025401427abb4c640500509da9b2705540000a522c8015400732853f4490140142449006a0f5005cebeed0a811401a4a12247c1550050a4d0244901401aaa13b512405006c1dabb44855400bb44900401550050a5c89200754014298c9d121550050a04892b90140000e65ce84404006f2e74276855401a45da249c15500509125d271016f55fa7bb5121560050a5c892f855401424493c801550050a2c9220055401c8a14d112405006c294890a811401424491480155))) else (if j < 82 then (if j < 80 then 0x621da512005540000da509124040053ddadc20055401c8afcfdda89500509127d2003d401a4a126080155e453dda9f4490180000e66c284894002ed1256200554014f76a49124e5000035373af85500188a13bc80155000039173afbb50018ea1224801550050a2cd6449014013f76a247e15500509f689200c5401c85da248004500509124e200e5401c8a14b9123f5006aa850244901401b0812ed12155006f284f576a2540173a13b53e4e50000284dc20055001b0a13b4c61550057e852e7aa25401428222480155a13b512842005580188a7b9480155007227f1644901401a476a24800c5 else (if j < 81 then 0x509d289271014014260a24801550053e2c922005540142449449c4050072684ed44901401b0a13b5141550053d124520055400ed5da2480315003b57689158554016c76a2480155a7a7d12400a81180142449388a0450071ee7422004d401424fa249c205006c748ed448555dabb51a248015600722e7428b10140142972248014500002e75f0a811001c8c453dda40500702848927055401428f224801550052a848b20055401428f4591215500509eaed45101401428b2348015500509da8d20031401a4c44b880155003b57889270554014f76a24ae4050050a369f4493940000b9bb560154 else 0x692848941855401c8d850a2c895005ce84ed5805540000a7b70801540071ee742271014014285a249c4050059abf4244855401c9a14091240500511dc89200554016c8122480155c5e229eed200558018876aec9c4050050a3e892005540175a51002a0450050a16893c855401425022c801550072284ed4497d401a9b9d7e84155005ce84f32005540188a79002a04500722e75fa13b5401a6a3224801550050a2c8b20055401165d98c801550050a26892005540142813b52815500695da892005540173a13b47e1550057e84ed4685540142972248415500509f88920055401a87b22480155)) else (if j < 83 then 0x5cebf162005540173afbb4800c500692e65420055401c8a122480055005ce84ed68101401097abb51240500691da892b901401bc76ac112155005de851620055401425522480155a13b5124012855800ee5da248015500509eaed582254012490bb51215500509daa620055401a7973d51240500692848920031401a476a49124e50050912400e81140175a122480155002ed12400a8414015fa12242a0f5005cebf420a811400ed61aed124050057e84ed45855401b0b9d09da4e5005ce844e200814015f76aecc615500509eaed448fd400ed5da248e155a13b512401e0558014676a2480095 else (if j < 84 then 0x509fa8927101401428b224800f50062284e7200554014245938800450062284e92005569eed4497080156006c333427685540188a1144801550050a04a620055401c8a1459104050053e84dc2005540142461002a055004fdda89270554014274224801550050a48ed448554014f7e2248015500692bf4244855401b084bb5121550050a5889200554014276a24481550062284450a811401b0a12249c2050053d8289200554012e90a24801550072284891f811401c8a14b9124e50072a84ed4493940173a13b49015500727554276a25401c8d2621da4050053e2ced4910140199a13d5da405 else 0x14297224dc4050073791424490140188a142c8015500509e28924055401b0d03a512155006a1da8920055400ed449cc80155006c7494244855401427abb5124850050a5c892005540188afd0a2c1550050912401b055401c8a13b5124250050a2e8a2005540000afd0916154007328489200fd401c8a13d912405006ab48ed44901401ada13b512155005ce84f376901401428b22450155))))))) else 0
  | 7 => if j < 30 then (if j < 15 then (if j < 7 then (if j < 3 then (if j < 1 then 0x62284ed2005412c00a13bdda892005580173a13b4801500300001d4a122480155000029f2e449002aa0076aed124e20055801a476a24801500b00001424493840155a13b53e892005412e00d4d0a0489200558014276a2480150230039142813b5124060050912401605408c00a13b51273200558014276a48801500b000014272a2480155006c284e9449002ac00b2509da8920055801c8a7bb512400ab00284ed4493880176006a684ed449002ac00a13b512400a819a84ed449509c400ab803914276a24802c6005dee742769002ac00a7d09828920055801429748512400ab0000173a13b49c1550075284ed449002ac00d3e91da8920055801a4b9d0912400ab0029f2e76a2480156 else (if j < 2 then 0xa13b52489271002ae00a14b912400a83d80000e453dda8920280284ed449509c40600003492e449002aa00b350a5c892005580173a13d5da400ab00000ed4494480155006c284ed44a142ac0000509de89200554014f76a2480150230034fa4a12248015600509daa3449382ac00a7d0a5c89200558014297224d2400ab003614276a242a0060072348ed449002ac00c5d09da892005580188a13b480170ab002c94f76a24801560050a3b16449002ac000050912400a81140000e450a048920280284f576a24800060057dda89200b02ac00a13b5124e20065801a4973b512400ab00001a9a122480155000028489200540ca000072284ed44901401b5a13b512400ab0028502449002a046 else 0x509dc892005400c00a13b576892710180000e4691da89202803634276a24801560053e84892005408c00afd0a04892005580142449a48015023003114276a24801560050a5ced449001ec00c4509da5420055801c8d250912400ab0038f73a13b4801560050a16ed449002ac00a13b512400e85d8015fa13b512400ab002853c76a2480156007229f4276a2480c00e4509da8934901801a476a248015023002bf428b3b51215600692852e449002ac00a13b5d289200558014276a24a2400ab00000ed5da249c40500509da892285408c00d8509eaed44855801a9d23b512400ab000014f449002a0450062284ed200ec2ac00a14662c8920055801d1a13b512400ab0034942449002a016)) else (if j < 5 then (if j < 4 then 0x509da892f9502ac00d83b57689200558014276a50801e0ab00284ed62224801560062284ed5d9002ac00d250912400a81180000d8509eaed44a802e7428b22480156005ce84ed4490018c00c453dda8920055801b8a13b512400ab00353a4a12248015600509da924493880c00e469284ed4490180000a14b9124007a802bf4f76a2480156000036173a13b42aa00a13d912400b85580000b9d7dda890aa80284ed459002a046000038f73a11002aa000050a16892005540000b9d09eaed202800018876aec801550063f1142769002ac000057e85164485540188a140912400ab000014274a2480155003b5769f449002ac0000509125120055401429730112400ab0000142449142a045 else 0x509da89361002ac00a13edda8920055801427da24802c0ab000014276a5080155d8509da92449002ae0076aed12400f0558014f76a24801504b0028502449002e1560050a1689349002ac00e6509da8920055801428b35112400ab003498876a248015600509dab5449002ac00a13b512400b8558014276bb112400ab002852e449f4801560050a04892005412c00c4509da92200558014276a2480220f300379b0a13b51215600692beed449002ac00a130112400a8118014276a2480220ab509da9f492248015700509da892005412c00d23b512512005580000e46928489202802852e449006a1560072284ed6022480c00003b56a892005540173afd09da890ab0000142459002a045) else (if j < 6 then 0x722bf4276a242ac00d23b512400b85580000a522480150228038b4276a2480156a13b52489200782ae00a140912542005580000e6509da89202802e74276938801560057e852e76a242ac00e450a2c89200558010276aed12400ab000014476a248015500691da892005412c0000509f689200554014276a24a8400ab0000188a13b49c155006931142449002ac00a14ba2c89200558015fa13b5121500b001dabb44900581560000284ed4490044a00a13b53e89270558014a76a24801502300284ed449388000600692bf42449002ac00a145912400a8058014f76ad512400ab0029eed449002e15600509da89200ec2ac00d250912512005580000e650912400aa80284ed4490032156 else 0x50a04bb449002ac00b9d0a5c8920055801a4a1224801504b50a04ed4922480157006a6bf4276a242ac00a145912400a81180000a13b514400aad09eaed4fa24801570000284ed4fa249ca00a7d09da8920025a84ed4fa24801501380284ed5da24801560052a84892005408c00a145912400a819801c8a1459da89203002851676a7c801560000001cca122480800006f284ed448554014f76a24a8400ab002e74276a988015600002bf42972242aa0000409768920055401b0a13b5124e0ab002848927100401560000284ed319002aa00a2509da892005580188a13b48015003002e74276b388015600509eaed4493880c00a13b51a400a8258000076aed12400aa8031f4276a2480156))) else (if j < 11 then (if j < 9 then (if j < 8 then 0x50a62ed449002ac0000509da89240554014f76a4912400ab00284ed449385815600722e74276a2480c00b9d09da9f200558014276a3512400ab000015fa12242a045000033342769002aa0000425da892005540000d8509da89272800014244938802050000284ed582242aa00a140924892005580000d4d7e84890aa8029eed5da2480156003b57689349002ac0000722bf4276a254014276a24de400ab00284ed449383c15600691da892a1002ac0000509da891f855401a4a122480170ab0000173a13b49c40500509da92449002ac00a13b512400f85580000e450a2c89202802bf4276a242a04600509da892710040c00c4509eaed20055a84ed51a249c400ab802c95fa13b512156 else 0x622bf4276a242ac00d8509eaed44901801b0a13b512150a3509daa34fa24801570000348bb449002aa00d23b5248920055801c8a13b51288203001dac05da2480156006228516449002ac00d85ce84ed2005580000a122d12400aa802e75f76a2480156000028531449002aa00bbd09da892005580000a13b5124e0aa802852e449002a0160057e8516449002ac00006c3114276855401a4a1224a8400ab0000188a13d5da40500691dabb449002ac00d8509da9f448558014276a8d124e2030028489229002a0460050a04ed449382ac00a1425da892005580173a1224801502300284f576a7d124060050a369f449002ac00a13b5168920055800ed5da24c6400ab00393c8a13b512406) else (if j < 10 then 0x509de892005402c00d2509248920055801428b224801504b00284ed5e224801560053dda892005400c00afd09dac444855801427abb512400ab0029f4276a249c1560060a84ed449002ac00a13b51269270558014fa13b524892030039142973b51240600509da892005404c00a13b576891405580142449002a0400b002e742769003c156005a1da892a1002ac0000509daca44855401c8a13b5124000b001dabd5da24801560069284bb449002ac00003b57889200554014281224801500300284ed44a1480156005de9eed449002ac000053dda892705540000a7bb5248920280000ed5da245015500509da892005400c00e450a5c8920055801caa13b512400ab00284ed449002a086 else 0x75284892005408c00a1409eaed44901801428dc0912400ab00348ed449002a006a13b53e89271002ae00a13b51240100558014276a6112400ab002850576a249c15600509da89200c42ac00d2509da8927055801b0a13b5122c0ab0029ef576a248015600509e2ed449002ac00e3d09da892005580173a1409da400ab002851b76a24801560057e84ed4485c2ac00a13d5da89200b1800009fbb512400aa80001c8a14b9124050072284892005408c00a145912400b85580173a13b4802c0ab00001b0a13b5121450057e84ed4485412c0000691da8927055401b0a13b5121e0ab002850276a7d121560050a04f5449002ac00a14b912400a81180000a13b512230aa80284f576a24801e6)) else (if j < 13 then (if j < 12 then 0x22cbb449002aa00a13b512400a841801a4a1224801500300284ed44900701560057e84ed449502ac00de509da89200558015fa14b912400ab000014244958801550000391424490008a00006c2850244855401428b224a8400ab00348f576a24801560000285027aa2480a00a13b51240188b18011676aed12400ab002f573a13b48015600003614276a242aa000050912401005540000d2509124e0aa800014278a2480155000038f42449002aa0000509eaed449014014276b01124e0ab0000173a14088015500002851b449002aa00a13b58689200558014276a24ac400ab003914276a2480046006c2850276a242ac00a14fdda892005580188a13b49c400ab0000173a13b480155 else 0x57e84ed5da242ac00d4d7e848920055801c8afd09da89203002e6ed5da24801560000284ee449002aa00d853e84ed44855801b0a13b512690ab00349427aa2480156a13b512400b85402e00a13b512401f8558014fa13d5da8920300284f576a24d24060000284892005420a00a145976892005580188a139512400ab000014276b0d124050000311427693880a00e3e91da8920055801d1e4509da89203002e74fa13b480156005ce84ed349002ac000057ddabb448554014276b2980890ab00001b0a7bb51215500509dced449002ac00a1409da890f0558014276a7d124e203000014276a2480315a13b52489200602ae000053deaed449014014276a8d12400ab00311429722480156) else (if j < 14 then 0x51a84ed449002ac00d9ec284ed448558014276a24800900b002e74276b00801560050a5c892005c2ac00a14098e8920055801a476a24801508300361a4a13b5121560057e84ed449bc2ac00d23b512401c055801c7d250912400ab00285057abb5124060069284f576a2480c00a13b5124e1785580000a13b5b6400aa802bf4276a491215600509dac7449002ac00a13b512482005580188a12248015023002852e449002a09600692e742769002ac0000519da8920055400ed5faed12400ab002851649224801560000361a476a242aa00afd0912400a811801c8c4509da89203003614276a249c4060062284ed4f9002ac00a13b560892005580000d23d5da8920280284ed4495ca8406 else 0x53dda89271002ac00d250912401c055801aaa13b5124e0ab002852a7abb512406003b57689200a02ac00e4509da892005d8014276a249c4016300284ed4f9002e1560072284ed7622480c00a12248015048118014276a9912400ab00001428b2249c1550050a4f02449002ac00a9509da8920055800ed5da24801500b001dabb55224801560072284ed4490012c00a13b59c89200558014293bb512400ab00001b0d2509121550050a0489271002ac00d8509dac0448558014276a249c400f300399c8a12248015600509eaed6022480c00ab3b512400f0558014276a249c400ab002851676a249c1560074284ed449002ac00d862284ed2005580000a93b512400aa80001a4b9d0880155)))) else (if j < 22 then (if j < 18 then (if j < 16 then 0x55a84ed449002ac00d8509da8920051801429a3b512400ab002e742769002a0c600691da89271002ac000050a04892710140188a13b4802c0ab00284bb552248015600509da892008c2ac00a1459da891185580000e67228489202802bf4276a242a006000025cbb449002aa0000509da892710140173a13b5124e0ab00284ed61b011240600509da892005414c00a13d5dac24490180000a13b512790aa800015676a24801550050a2c892005400c00e43b57689200558014276b2912400ab0031142769003c1560000176aa449002aa00a14b912542005580142813b5124e20300284892005c2a046000028527449002aa00d250912400a841801cce4509da892030025ced5da2480156 else (if j < 17 then 0x53dda9f449002ac0000002e75f76855001c7a145912400ab0029f4276a249c4060050a2cf576a2480c00a13b5126927101800005da248015022802851b8b2248015600509da892005428c00a13b5127934855801428cbd5da89203002852e4922480156000031142811002aa00b9d0a2ced2005580000e43b5768920280001429a224801550072284ed448fc2ac00a1224a8400a811801428127d12400ab002bf427abb512156000031142769002aa00a13b5b6c02005580000a145912230aa801dabb449002a04600509eaed4495480c00a13b512400e8558014297bb512400ab00284ed4fa24801560072284ed4495080c00a14b9768920055801428b3d512400ab0031142813b480156 else 0x2bf427abb512a00d2509da892710180188a7d09da400ab0031142769a4801560072284ed449382ac00e4509da92449018014276a7d24400ab0028502449002a05600509eced449002ac00006c28516448554014298cb912400ab000014276a24801d5a7d09da9f449002ae00d3bd5da892005580000a13b5125f0aa802852e76a249c15600002e75fa13b42aa00a12ed12400a81180189c4509da400ab00284ed449002a0560070684ed449002ac00d850a04892005580000b9d0a2c400aa8000173a13b4800c50000348ed4493880a00006229eed200554014276a249c1500b003914276aed1240600509da924490002c00d8509da8920055801b0a1459da890ab00349424493880156)) else (if j < 20 then (if j < 19 then 0x53dda89200782ac00a122d12400a81180000d3bd5da8920280284ed449382a046006c348ed449002ac00a14b912400a8018014276a24802c0ab0034988a13b4801560059284ed449382ac00b9d09da40190558014281224801e0ab0036173a13b5121560000349424493880a00a13b5126a2005580000a13b512420aa80001427b224801550071ee742449002ac00a13b580892710180173a13d5da8920300310ed5da24801560000284ed4490028a00a13b512400f05580000a14b9124e0aa80284ed449b880156000034988769002aa000050912400a81540142492248015023002beed5da2480156006c29eed449002ac00d23b53e892005580000e4509da891fa802850576a249c406 else 0x6671142769002ac00d23b512400f0558014f813b512400ab002f54276a24801560075e84ed449002ac00e44fdda8920055801c8a13b51240003002852176a24801560072b914276a2480c000050a04892005540173a13b4801500b50a2ced44938801570053dda89200b02ac0076a24d2401605580142973d512400ab001dabb449002a0960000284ed449b880a00afd09dab044855801a7a13d5da892030000142449382a0450000284ed449002aa00d850a7ced4485580000d262284400aa803294276a24801560053dda89351002ac00c4509dac0200558000090bb512400aa80001c8a13b5124e5afd09da92449002ae00d25093e892005580142813b512400ab00285024490058156) else (if j < 21 then 0x50a2ced4493880c00a13b512792005580000a14b9ea89202800014276a248a15500509da89371a480c00eb509da8920055801427aa248015023003114276a249c1560053e84ed449002ac00a13b5126920055801a4813b512400ab00391b0a13b51215600002e742971002aa00e4509eaed449018015fa13b5124e0ab00284ed44938802f6000029f02449002aa00d23b5124016055801b0a14b9da890ab003134276a24801560050a5cf576a2480c00a1459124e20055801c8b9d09da400ab000014f76a248015500003554276a242aa00d8509da890a8058014276a5112400ab00284892005408006005ce852e769002ac00d8692848920055801427abb5124000b001dabb449002e156 else 0x6228516769002ac0000509da8b200554015fa13b5121505300285164490046156006aa84ed4493880c00003b5766320055401b3a13b512400ab003614276a242a04600002cd42449002aa00e450a7eed449018014282bb512400ab003494276a2480156006928489200b02ac000050a2c892710140000e45ce84ed2028029eed449a48015600509eaed4490008c00a13b512480a82580000a13b51a400aa80284ed4498c8015600509da89200541ec00b9d09da400a811800ed5da24a8400ab00001c89fbb5124050000348ed449002aa00b3509da892005580000d850a5c890aa8034942449003c1560053e8502449002ac00a1409126920055a84ed4922480170abdce84ed4493880157))) else (if j < 26 then (if j < 24 then (if j < 23 then 0x509dabd449002ac0000622bf4276855400ed5da4912400ab0028505813b5124060000284ed448a02aa0000509da892003d4015fa13b53e890ab0000188a145880155006929eed449002ac00d23b5126920055800000050916400aa0000173afbb48015500509da892705c2ac00a14098089200558014276aecc6400ab002e74276a249c4060000361424485408a0000692848920055401428b27d12400ab0028502449608015600509dac0449002ac00a13b5124e0a82580000e46c284ed44a80284ed449fc80156006d7614276a242ac00a13b51489200558014282c0912400ab00284ed4496080156006928502449002ac000050912400a83d4014676a24801500b0000173a11002a045 else 0x2c94276a242aa00d23b58089200558010976aed12400ab00348ed449fc8015600509da892a1382ac00d8ec284ed44855801b0c4509da890ab003494fa122480156006928489349002ac00a14b9124e200558014276a24fa400ab00311427abb51240600002d0ed449002aa00a13b5848920055801b0afd09da890ab003914276a24803f60000285058122480a00afd09eaed449018000000509124007a0033b4276a248015600622e742769002ac00d8509dae9448558014276a24802d0ab00284ed449006a156006c28516449002ac00a13b5124e0c85580000a1415da8920280284ed4497c80156005cebf42769002ac00a7bb580892005580142953b512400ab003334276a2480156) else (if j < 25 then 0x50a32ed449002ac0076aed12400a8018017da13b512400ab00284ed5da249c156a13b53e892005402e000050a3a892005540000b253dda890aa801dabb449002a0860072284ed4493880c00a5509da892005580000a13b530400aa802e742769002a0960057e84ed448782ac00a13b53e890b8558014276a2480180ab00288ed449002a0060050a5ced4493880c00a13b5124017855801428b224801e0ab0000142953b5124050062284ed2005424c00a13b51255200558000076aed124e0aa80284ed449002a0c60050a3aed449002ac0000529da89200554014f76a24802d0ab00284ed4493880016005a284ed449002ac00a13b53040160558014276a2484400ab00001b0a13a512155 else 0x50a5c9f449002ac0076af1768920055800f576aed12400ab0039188a13b48015600509da8a2005400c00b2509da892710180000a145912400aa800014276a24800c50057e850276a242ac00a13b5125720055801429a4b912400ab003614276a242e156e4509da9f449002ae00a13b524892705580188a14b9da400ab002c94fa13b512156000029542449002aa00a13d5da892005d801428b40912400ab002bf4276a24581560069284c0449002ac000050a5c8927101401b0a13b5121504b0031142769002a01600509124e2005408c00d2509127f2005580173a13b480170ab00284f1449002a0960050a2ced449002ac00a1459da5420055801428b224802c0ab00284f576a2480096)) else (if j < 28 then (if j < 27 then 0x509dabf449002ac00d8509da892a05580000a13b52489272800017376aec8015500002bf4f76a242aa00d2459da892005580188a13b4801502300361429722480156005ce8502449002ac00a13d5da892a1018014276a243c170ab003934276a2480156000031142729002aa00a1459da92200558014276a248a400ab002853b76a2480156000029f16449002aa0000509124e200117114276a249c400ab802e74276a2480156005ce84ed2a1002ac00bd57e84ed4485580000d8d09da890aa800015fa140912155000031142971002aa00c4509dae52005580000afd09da890aa801da9f449cc80156006aa84ed449002ac00a7c59da89200558014276a249c40023002852f9722480156 else 0x6c284ed5da242ac00e46c284ed44901801427abb576892030034f4276a24801560057e84ed4493880c00a13b5124e0a8018018bc4509da400ab00284ed44a208015600509da892005424c00a13b58289200558014276b5112400ab002e74276aec801560050a7ced449002ac000062284400a8114015fa7d09da890ab002bf4276a24d215600003554276a2480a00006c1dabb4485540173a7bb512400ab002e6ed449a480156000028516491002aa0000509124520055401424fa24801502300000f576aed12405000039188a13b480a00a13b512420a80580000d3bb512400aa8029f428b224801560050a2c89349002ac0000509da892b9014014276a2480320ab003914276a7d12406) else (if j < 29 then 0x50a5d02449002ac00afd09dac044855801c8a13b512400ab000014255224801550000284ed531002aa00c457e84ed2005580188a14f1da400ab002852e76a24801560050a2cc0449002ac00d3d3dda89200558014297224802c0ab003614276a49121560050a04892005402c00a13b5124014055801427abb5124e0ab00284f576a491240600509eaed449003ec00d257e84ed448558014f76b0512400ab0025d2176a248015600692e6ed449002ac00a13b512400a8058014276a24b8400ab002a4ed449002e15600509daaa449002ac00d850912400a81180000a130512400aa80001c9a13b512405005ce84ed491002ac00d250a2c89200558014297224801e0ab003114276a249c406 else 0x509da89270802ac00a1224801e0a8118000076a24e6400aa80284ed449388009600002852e449002ab4276a8d248920055c01c8a140912400ab00284ed72a24801560053dda892005402c00a13b5b68920055a84ed4493880190ab803914276a24801e600003495fa12242aa000053d828920055400009748512400aa80284924495880156))))) else 0
  | 8 => if j < 2 then (if j < 1 then 0xd2509da8920055801a476a2480155a7d09da8920055a84ed449a4801560053dda892005540142812248015500509da89200556850276a2480156a13b5124016055a84ed449003c156d8509da892005580188a13b480155a13b53e89200558014276a249c405a13b5124e20055801b0a13b51215500509eaed4490140173a13b480155a13d5da8920055a84ed449002a00600509da8927055684ed4922480156a13b5768920055800ed5da2480155a13b5125420055a84ed449002e156a13b512400a825b114276a2480156afd09da892005580142449002a0450072284ed44901684ed449002a046 else 0x50a5c89200557914276a2480156a14b9da8920055a84ed449002a016b9d09da89200558015fa13b5121550050a2c89200556851676a248015600692848920055684ed6022480156) else 0
  | 9 => if j < 1 then 0x14276a2480155 else 0
  | _ => 0


def stateW : Nat → Nat
  | 3 => 31
  | 4 => 40
  | 5 => 49
  | 6 => 58
  | 7 => 67
  | 8 => 58
  | 9 => 49
  | _ => 0

def HT (s j : Nat) : Nat :=
  match s with
  | 3 => if j < 1 then 0xe5875aa9b90edee97afd389a5501eddd508b49ac30838d89 else 0
  | 4 => if j < 3 then (if j < 1 then 0x5e0b73845d9e1a4b564053d45611d3bc552f19685309c9f65100bee24b35ce0548fcfed441ab13893ae8a8863a5d1afd2abe62a92854c961281dbbdd2806b4872494b238225565f0225522f61cb4574f1ae6c19b173407fa1695fbf11605ee9a15d419ce132a1a71106d94b40c57fdfd05f462a104c77611049e85e0048059b4 else (if j < 2 then 0xa75f3912a4f3784ea18f60efa0de363ba0a32b559d86f7cd9997ba0b9942157c98e9d73f98e4ff1f98340d6c964238ce92f9023f92d483858ec34708850f1f0a8314e10f80ea4c857cbc8a9e7a37b5097828a2a976c9b24871aa2b2170c14de4707e87fc6eadfde567d1e14464a4845061e80a6160dbf8115ffbec605ee6452a else 0xfe1b1cebfd30186dfb2f4b40f8d80a00f579064ff1c61c42f0f4489eef85cb0aee836bc6ebcb15b2e8c618f4e54de7c0e45247d9e3b298f9dbd7809bd930070ad2f1651cd18e14adc9573db0c86c279fc85f5b3dc8461acfc74fb955bce351b7bc16f199b7f8f550b73ef03fb5d47452b13dc14bb06af770ab863888)) else 0
  | 5 => if j < 30 then (if j < 15 then (if j < 7 then (if j < 3 then (if j < 1 then 0x6bb9afb065f62ba063479e50614a4ca060d3f50060bbced05cc0e3f05caf16a05b84dec055dd0d805572dd1052f038304e605c704d8922e04cb989e04c6dfc004b5dcbb04986da004724ed803dd2da602ef7e2802b5d5460244dc4e021dae3601d0721a01be0d8c01adbc2301a72f720177635301417d840101f51b00c13bf2 else (if j < 2 then 0x1162dee810d6739910ac8e6a1091b451106bb9f4104ebb1b0fa9869d0f4b8a750ee574b10edf2f9a0d7d44070d0a69ec0cffe1760be593d50bc623030bb48d2b0b6f52e20b129cad0af243fb0aecdc940ab433460a9fbfb60a74fe7c0a3370120a2f0bb108fb8e2908f3b0f908d9b75b0835c8520831c04e07f8a7ae07600c74 else 0x1b37ac3d1b1d54f21b0c85a91ac1ef8b1a7c251a1a7b6a331a104bfb19d75741194767ae18daf9a618d2f3c618ca40de187ee5cd17aa0ebc17a0aa00179547831763a975175b6fbc1754f1b8163338ae1615a65e16141fa6157e1641152cc26b1429989213cd85ec12d8b8dd128c3822126a3bcd125375cd121c091111deca18)) else (if j < 5 then (if j < 4 then 0x250fe91824dae35824d4d0cc23e58682233478022322b48422f2e15b22dbdba2225522f6224667a521f5c2c220cb17431fff30ea1fce26b81fc1e22c1f9a2a361f6537371f62b13b1f329a301eea51351e96677e1e22b8ab1e0d1b5f1da5f34c1d6144e41d5f3ee01cd5a41c1cac20f71c90f7c11c69aff01c5ebbef1b73447c else 0x2d99d8eb2d5a84bb2d03bf482cec4da82c2707332b3959b62af814012ad376da2acc76192a69680e29fc86f129e7c34329aee9b829a2ab8b29a2a765297b57b128c34af828b00b39288f9c1d284cceca280591ad27ce9fe727ca862327b6add3277b354c275595f32745aebd2704fa8826cf03892699abac263f1af425bab709) else (if j < 6 then 0x34e4b610347765073470f37a340f62c333c1e1073374377c336b4bc932434c92319ae676319a7f6f31187264310e9d0230fccc2130e9b0aa30e3d9c43091d4223032ad263004c0a62f7f9c772f3bba3d2f0f94602f081f5b2f0761852eb911bb2e9b50f12e6e9dc52e6969c82e409d462e39ea942e17c5c32de6f01f2dcc03be else 0x3d8cbe223caad9a33c6f945f3c6128be3be602763bd81da63b962dc83b4fccfb3b0c7de33aeec70b3aa0a1733a60008b39a7324c3992100e39783c9e38c6f77f38aee11538a1507b383f312237b94805379a4605379308583777fa7f37571ead37455ecd3677e7b43628db9b36064bd035ec52a335cfd1c235c0e8bd350c797b))) else (if j < 11 then (if j < 9 then (if j < 8 then 0x499a71cc490c60cb48370f0047ec4ecf47c3df42478521994781229947640b2b46bdbe88466e028145f372014593f557448038cd44667ed443ef04c043be9a0b437e1f9e431cd84a42e5e19b42ca00ff41f5d82f408a4a744049456b3fb2efa23f793fd93f74212e3e96c49c3e7a4ed93df77cf03ddae2c03dbbf25a3dabbaeb else 0x50bd5b2350adf8ab505a269350472929503f29ff4fd4fefe4f9aed634f72b5d74f2344474ea181764e65f2114e5bdff34e4c43874e3481344e25a0594dddaecf4dc08d684d98ef874d98b13a4d6b9e3f4cded7d94ca2eb7c4c7280c74c32f4374bee0e724bb1b03a4b8d3cdd4ae9bbc94a8001534a296a5749ee9cac49c8c52a) else (if j < 10 then 0x57d24718572f57335708d23556f1df4a568fff20567a19555647e64b5636f8515619aa9d56054b9155eaaf7255b5a99a55813393554f820955366b1c542b4de45413c7e553c5f85153a653fe53816df6536db591534cdee95336211752c7588952380a4c51f2689251e044565167fdb6515e74e451433ecd50fc986150f0ca24 else 0x5f0737245e45387a5dd574af5dd4bda45d806b2d5d2c47c25cd334225cad33ad5c03f7705bd66b015bb234bf5ba04ca05b6e2b7f5b603df05b4517cf5b1e4c8b5b057d7b5ad2b1a55aa188c85a6c0d305a397db35a33c2485a17f8a25a0d815159f1d7fa59cfaf5c59c5c7325990cd9759071ddf58ca86e758ae69c658992200)) else (if j < 13 then (if j < 12 then 0x67316b5366ff6d4f66adf94d6682132e66610ab6658cf37f6582b68b65437f1d650947e664e4ed4264cf509f64cf4c7964bcee9364a007686464ba6d64601af963fe6e1563b351e76362e56f6356631562d6283362a0b8cc623950b26222d63161ada49c615fa913614a31cf612c0f8960e0ca8560a65fb25fc79b3a5f7c9c1b else 0x704687ef703c6676702a20146ff378c26f95ffd96f92c29b6f64f1546f63ed2e6e962e136e58f7d16e5561886dab7a5d6d95fac26d2873446ce9cd486ccc38f86ca86a0b6c8abb276c69efd16c25f1ac6c1e7c686c162a7b6b5c69586a7185706987d968692a8cb8692919fe68e18bd768c181c068979f5168937c4a6842b150) else (if j < 14 then 0x789376be7876f90b78503dce7816142d780983617806e86e77eca95a77b2bba076c9d31075da8b3c758ccb08755b3ab5751c00ad750b1f6474c9cdf974c0833b74bbf82674aacfed745f05087407cb3f74000c2f73f1bffa73bdb9107372857c734bfb0972261fb67217f9cf71a63f5270e89f5c70e1242170af7599705c9d63 else 0x84497b1783c3f53b839d703d83226f11832148ee82f08456826fb109824f35e6823e5592819c15ec80bbee34804f37e7804904327f6140a37f3abba57ef465577ed7d8d77e85ed3b7e7e71b37dfc81a87cb9fa027c79119f7c478ea37bfa40037bc8032f7b3ac0fd7b3440ee7b1687137aecca837a807f5c7a003c4779bc3f3d)))) else (if j < 22 then (if j < 18 then (if j < 16 then 0x8d833c148d307a808d276c968d0bf5798cc92c5c8c2417748c1d6f388bf5c17b8bda9dbf8bbd07378bb025b88b0dd6928b0d92b48a64d5a38a24912c8970aa3e8941d1b5893c40b688fc199288bba88e88ac64588876f1fd88757197878427f387830b1e8743747586b9f434862dcc2a85c77aee854a25cc848fdfa184599be1 else (if j < 17 then 0x973afd7e96d96a1896b1965696a9ab0b9629f4c79591ff17956c487b953456d094f2707794d9824e94c2d4c29484ab9b946aa2d49435cf7593dbc751938e23f893482213931ef1cc9235885991e79c259178d63b90b3844a906bcf589025f4a09007ff308fcf7e308faac5348f8299608eb935208eb7fb2a8e62c62b8e0646c6 else 0xa3bb1a93a37ab0f1a378050fa30df312a2e2bc7da2b11358a232e234a229ed0ea1dfba38a0c051c69ff3308c9f4fe51a9ef4c6a89eaaee5c9ddd7e429d9097839d51867f9d4cc6029d2429c49c42e6fa9bcda6c49afb3f289af4fd029a7b2c0599b0ad0998bf036498af326a98adc64798403ec99804a18d97d50ca1979fa28f)) else (if j < 20 then (if j < 19 then 0xab64ed27ab3ee02bab1d05f7aa2a61aeaa168fb4a9dcbf56a9bdab61a9a46162a95e6492a95df3c2a9516898a94e980aa92cb538a90dafa7a8f28c9fa8f0fd08a8c1eda2a7e94e66a7ddeef8a7d79ca6a785c716a75f3912a6791ed2a64983baa6433179a5fb3212a55fd526a54a24b9a4aafb0fa437974fa3f6f6e9a3ebc094 else 0xb29bf378b28fc095b2394783b21f7fe2b1bf7165b1461346b0f390d2b0b1f748b091d5b4b078e615b056db43b03e97cbb01118f7aecf0d4baecdcde5ae9c7751ae75405dae23552dade033b6ad9a95f6ad3432ebad144bccad0c0ae6acbac9e8ac9f0b6fac72d85eac5fac0fac277a7dabed87ccabe0ce44ab9b2cc1ab67036c) else (if j < 21 then 0xbaa9e412ba7686f5ba4a7e80ba28d922b9c4b0a1b94ab3ebb850e196b844ca49b834220db7fc8755b7ebae5eb7c5a8ebb7bf1ac3b799bc52b7981e7fb769bde6b768eb0bb73ef03fb6187487b5c44202b5a805b5b59f842cb5996c0fb5286505b51193e6b44e2e47b3b31490b39925e4b376451fb331f843b2cc97cdb2b64593 else 0xc1870e7fc1253297c0bc7a60c09a8f77c05629ffbff7d12fbfd19ee9bf9e79b2bf62328abf41809bbf1bb30fbf03c27fbee6c8e3bedd3056bebc86b5be661726be373a59be249c40bdd03302bdc162a7bd829b2ebcf9320ebcce5c1bbcc58e72bc3f633cbc23205cbc181a3fbc12cb18bb807e89bb70594abac82212babf669c))) else (if j < 26 then (if j < 24 then (if j < 23 then 0xcb9f9ceecb9a8d5ccb460c75cb1fd253cb0d81fccb0d7dd6caf01919cac0ba81ca7d9684ca3be87eca297c6ac9ca07f5c9c35a25c9393c4dc8c7e79fc89bb626c8969de4c6c8e61dc5f52b34c5b7bb7fc56ca960c4353dafc3f961a9c3f44c4bc3e0b99ec3bc45e2c3a05784c38e1260c38bca75c324e784c297a133c21f04ec else 0xd4d9ba72d4847375d46a4da3d45dee77d3e016fed3a9af01d3728f80d2f36058d2de21c2d2d58f2dd2cd5fe3d2c03c30d1a0e23ad0fd05ded0fb6d85d0d7bda3d0a32636d01f7a9dcfb7b086cf99a8bfcf764db0cf30f3b7cf1f369aceac7cc8ce927c76cd6ef906cd4f8369cd2a1b40cd28fe6bcd19c9d7cce9246bcc167a1c) else (if j < 25 then 0xde27d1dcde1a0db9de0b21aeddcec5b4ddba4a5eddaf43d4dd8e84b5dd38bd7bdc3c24c0dba9a139db36cc5ddaad030fda399506da285064d944c558d8c4423cd885a619d8815540d8741dbdd856f505d84ef23fd840e862d7ffffffd76a5e05d75c760cd743b6d1d6ea0908d66ff2d6d5ce1f89d5509592d546353cd536d0ad else 0xe6578b06e5726903e55bb18ae4ca1cf4e4a93be5e46a60dfe4407590e438ac50e329461ee31ce155e2f47befe2ec652ee2aa5ab1e29335cfe23d3662e23a7809e1e005c7e1df3c5ee1b21ae2e1adcb88e1a28027e0a2fdbfe054ca28dfe000b0dfd38912dfc7e0c9df90e584df889a6fdf3a0803df31a92bdf163ee6df07df89)) else (if j < 28 then (if j < 27 then 0xed017029eccad1f2ec998140ec5c0d75ec1d8fbcebb0083eeb76a3d2eb31b394eaad0201ea75fe16ea547ecfea50ee5cea2d7845ea203865ea02bac5e9d93e19e9d91102e9c58ffbe92eb5b3e927d714e8b7be64e884589de84d78bfe836ac32e7fd0575e7e76efce79f7d72e7830ed4e771004ae74e7bbae6d85430e6afb7f2 else 0xf2ed27fef2da2638f2993dd5f25ba095f251ce2ff232ede0f22fd9aff225b439f2221402f218cf1cf1e996fdf10cf6b9f0f5630ef08bb436f0795ed7f0498b4ef042569ff040de80f01b621aef639eaeef2bec9eef0d60f8eef7eb91eeb3a2f4ee3b5f0eee173a0eedce442fedc30caaedb9d09fedb27559ed65416eed43eb5f) else (if j < 29 then 0xfb2f4b40fac0f7ebfaa4d7dbfa427347f9ce2de1f9abfca7f865ae84f841e6c5f815ff0df7ba37f7f765d93df75f8d19f7421c3cf6dd7e7ef6d10fbaf6c01edbf69771e5f5f69621f5f06c3ef5d0270df5afcc66f57f1f51f56a87d1f537c22df4e76565f4b3495ff4a0f788f486dcf5f47a4a4cf42fee0cf36eabddf345e837 else 0xfec52b75fe9e1d2bfe971e33fe4bd2f3fe3ed8d2fe2b9c7dfe1b8305fdead006fda27aa2fd9d8cdafd81e795fd7a2c9ffcfea5b6fcb81fedfcad9e7efc61d3d2fc1b389cfb727531fb6be077))))) else 0
  | 6 => if j < 85 then (if j < 42 then (if j < 21 then (if j < 10 then (if j < 5 then (if j < 2 then (if j < 1 then 0x4363194040db776040c6b8903f506ff03ebdf8e03eb1c4b03cc4d8203c0bc0303ad1ad60397efe8038ee6d203888bd80372208b02ff6a6902d667b2029ad18f0291673b022e51c001f1d00101be0d8c01afa66d01a3e1ce018c461d01657520015b68f2012b12e200d5ff7700c1f9c200ad0f24007ebea3004b729000165909 else 0x824c412080fc265080f10100802dd4807f23e4307aa163c077be9ea07254ac607055d81070469a906df713a06d5f05d06be808906bc0293064db3eb063d628206241faa0613eca105f5bf1105cb553805caf16a05c9f7f605931dd3058e040b057931f504ddf45b04c9860f04be0c6f04bbdfbf04b394250496bfe8047b8e07) else (if j < 3 then 0xbb614300b688c890b5ec09d0b4343740b2cd3730b2639c90b129cad0ae20ae20ad8d6f10acb03a50a9ecabf0a8b05b40a7843670a6603a20a6458780a63e3310a61a4200a1bf4500a19fc380a0a3ae909a2cc97095fb0c00952667f092c5c63091d463708b4da4d089d936708992f06088ae1fd085220620845aec108363204 else (if j < 4 then 0xf3a72340f37cd540f277beb0f16b1bf0f0229620edf2f9a0e8ce8db0e69cde70e5da0140e3a58480e3490170e1f437e0e1461460dba3dcf0d87ca8b0d8169ca0d6891a00cd3f6f30cc78caa0cae22010c9cc8830c98c2be0c774c640c55944d0c50e53d0c2b89980c2b78340c1c1d4b0c16f9030be0a44d0bc12bf00bb8aa4d else 0x122bbc961228ea0111c34e8611bff5c011bfcf4511ba7ebf11afa45711a86585119948841190f58d11853cc411840904117efeeb1135d56d111d6254111c672910ddd37510cef447109e93c51047c5a8101eab3b0fe9ca590fe6bb450fe4aec50fe1626f0fdc9f9c0fbe8b280fb88c8b0f85014e0f6303650f547e0d0f44b271))) else (if j < 7 then (if j < 6 then 0x1543e79815388ca21501126c14cadfbf14ca1db214b0b928149a2025149804fc14958efe148a65311423c41c13fdec9a13fc7cb613f3926d13ea9eb313dda65e13c7132a135ac050135035d6134e5f0c133d030b133c677212cc827f12b88c1c12b40581129d00fe129038c412804d761261c37f125375cd1248473a122f7980 else 0x191bb06818f3a27c189936ac187527031853b129183a6678182eea7a182674721807bc6217b71e9a17a773e517a4205117893ad81753e8ca1732cf16172f5a67172b8bb01727b7511726ab1e171ea98017128dba16ea311616b21d6016a7a8371692bf4c166e25481641e6a915f8f1ca15d97a3515a6142015a277a6157f6575) else (if j < 8 then 0x1be3efd31be358e21bdb7e141ba6eb961b920eff1b81edc41b81c4451b5ca9df1b5636b51b464cfa1b3f9fdd1b128f741afe22e41aee6ba41ae7a5fc1ac4720f1abdbb281aad67ef1a8420571a827bcc1a3c2ecd1a372fba1a2671a61a0a266e19f76f8519dc0fbc19c5cda41999832719997f0119821b3919603b581957ee31 else (if j < 9 then 0x1e4660f11e3ec4541e21c9ae1df38a2f1df216701ddd0a661dc591551dc1de451dbcf4e21db4f9281da7c82a1da5f34c1da2dd011d9515381d84398e1d6f391a1d59687e1d4942271d3f745d1d387df31d35905b1d2179081d0a791e1c9da9fd1c918d1a1c87bf8c1c6ba19e1c69aff01c2583f31c0ffdd91c045a0f1bfeb2f6 else 0x218a61092161c7ae21606b8a214bd5c4214bd19e20f957a520ec13bd20ce733320bf496820ad0b4b208344de2069ad9d2064930e20609da3203d219420295fb2201fd6e2200c61fa200802aa1f75e4e01f675f261f63da861f25d8871f20626f1efa8e141eedaaf21ebe2ae41eaa0cf01e86ff231e6ce5ef1e69bb381e67bf22)))) else (if j < 15 then (if j < 12 then (if j < 11 then 0x24a42926246c2a11246667d0245b251d24563ec524548ed3244f1f9c241560142403f06f23c5605123b9c915239d9f202390f9c8235d56a2235a73ff23559d9c23535c88233478022333a30223108b0f230b736822c60e3e229f76812295784f225c506c22245f35220caccf21fccb4c21dbd3ad21b76bd821b5cfff219e9b57 else 0x277211a02770f4cb27616f322711a7442709263726fd39af26f3035926daf36a26d60e0426b60a03267678a0265057f8264e63ea264983c426327266260b92712605fd4e25ef4d9525e2662d25a82a7b2598b37b255db2e12556b9ba25563e23255176342545f369253aa4eb2535d506253170a524fbf40124fa174224f878fd) else (if j < 13 then 0x2aa944d12a9d5e6e2a6cb8862a5c662c2a35f2d92a2eb7992a179ca62a10e07a2a0e9f3f29ed4a6329e77b9d29d4e87629c8732a29b275c52970eec62964772b293f65ab2935e28d28ea07ab28b5f00a2893badd2887375928858a84287839472838a4182823e384280a9c1f2809e51427f99a5a27ccab7d2798a7d327823fae else (if j < 14 then 0x2d8a8f872d5ba5eb2d54f0f22d5297e82d5233502d457de82d3d95e62d3b56b82cc3cdb82c966e932c7ffc022c5bc5842c5406692c47700b2c1d46da2c0267ff2bcf13432bc4a8102bb9ec2e2bb2465e2baef35e2ba9f2c42ba11a1d2b94d0832b8a1b062b7731ed2b73c7822b68246d2b4143b22b1a7f2e2af680ce2ad7b888 else 0x309632263085ef25304f6b99304de4b4303e385b301782aa2fdda4b82fc843fb2fc1656d2fc0276d2fb09cee2faf00ea2f9ac95b2f9441512f8eda262f6d94242f41e3fa2ebd01f22e9b50f12e972a702e82b07f2e5b6a7b2e53e1f42e52d8b72e3e611f2e308e732e1ce6af2e0afe102df4b8a22de80ed22dd336dd2dc76e2c))) else (if j < 18 then (if j < 16 then 0x339bc3ee3374377c335236e6332b4c9e3304034f32dee2d032bfb24832a3df61327a78883264a62f324e909432484fd932434c9231ec822331e9eadc31e6825731c8b80a31c5dff331a54bcb31a1a892319e2da9318a2e9c317150c231436d403140e60d312dd09d312dcc773120a218311e7d223107631e30f8a5a030ace2d4 else (if j < 17 then 0x3609b89935f1f1fe35e43ee035d21d0435cc1a7c35c4547f35b49e553588d20035771f2d355e92fe3557ccd53556f8fe354cbf67352e7fc4352dcd0e35212d78352001be34e39b8134e20b0934d6b90034a3644434a32d9a348d07c13489e0fe348075aa347c3cd2347a6df4344ccf9133fe6a2e33f9792e33a5e47d33a2613d else 0x39cb2749398884be397d3fe5396799e6394a84673912be3338fc8b4138cde7c038c69426388e1f413874aa79384c879e383f3122383c7380383c532a383c1ad737d7e17c37cb223237bab6de37aae286375d9ab437455ecd371da7453704df743701606836f5177936c2ad5d36b14303368f178b367bd65a366518f63645bf54)) else (if j < 19 then 0x3d9a09023d8956b73d7c786c3d62203f3d48a1303d439c353d37c6313d1a8fe83cdd91713c9ae6743c4f0dd53c0636bb3c028a613bf142993bc802e73bc26d2c3bb0bccb3b6e50e23b6605423b602e2e3b1afd3c3ae24a7d3abed4563ab914b83ab3e1863aaec9143a9d96073a6ee50c3a5ad3713a258dc63a22ae0839f4a254 else (if j < 20 then 0x407f7473407eac4b40759828403d08284030f4d2400fb2ac3fe6951d3fd3e2c13fd1057a3fb1fe5e3fa7f1223f9657ac3f93568c3f82fb653f8164393f74212e3f710ae33f6d097b3f657a873eefa6ea3ebd88093eaadce33e9a19653e997c673e36dcf63e2593953deedb723dd8ce2a3dbbf25a3db0c6663da13a233d9fae7b else 0x42a322ea4292d830426103ec424fed48423c0fde423338184227925941fcc42a41faad0841f8a7b541db7e8041d585fa41bed2d741bbc48741b9bab341a1996841977d424195344241924bbc4186d5044163c440411f03394108837040f7ae5240e7a1c040e2222d40c47f3440bac35140b54e4440b1b56440af346740a4d047))))) else (if j < 31 then (if j < 26 then (if j < 23 then (if j < 22 then 0x45453a7c454292d9452634ab45145a324505552545049e1a44cc55b4448d29fd44890d894482974c4474942b446bd2cd446b9968446903cf445c2838444b2958443ed4ff44383c4b440e987c4408769543b6a05b439e3d09435708bd4352a45c434b31c0432cf8b34327858e4322208a430fa72f43064b7742bc655742a3d9f5 else 0x481c91cc4809639c47ebd5be47d9c05347d9893e47b27f824792c0ec47848d9b4757e70f474deeeb47113ab34709dab84708d2cd465329ce46468ee94636ec7246323160462e0e5945f1da6845eeced245ec8c3945d5e84645c507fd45a20fe54597cf9b458900be4580e52e456bcd024569aaa345697fa9455f8e85455986d2) else (if j < 24 then 0x4a74149d4a61e8bf4a5c759a4a5580244a36c9744a31f0354a0b1f5249fdafa849f1556349d4e0f049d0271549b6c26749ab950e4980fa9c497670af496a2ebc4956423d49451e6f492f9d14492e7f25492846884922029c490335f148f68aaa48e9bfdd48a6217f488f8989485ce9af4858c001485722e44826832d4821dd33 else (if j < 25 then 0x4d62fe654d616be34d3114ac4d148aec4ce6697c4ce5da874cafc8364ca784304c83b3614c61f5e04c5b70574c3cbdc54c0a148a4c032ae54bb9dfee4bb1b03a4ba680064b8ffa554b785bcd4b784d394b5f9c184b2f6ffc4b27f3f54af53d3a4ae6e7ed4ae3325d4adf4b504adca41c4adaa7b94ad32d154a845f574a8196ab else 0x505a2693503e261c5000d7054fd4fefe4fd232574fba47ad4f9a44704f7f4ddf4f786efd4f71b2824f510a584f4f04544f24ecc94f1521264efa76454ef8c3da4ef859cc4eefaef94eddbf684ed8d4e04ec94a924ec4e6314eabcf0a4ea240b34ea181764e64677b4e5bdff34e3f22534e25a0594e1fa8334e1828df4dddaecf))) else (if j < 28 then (if j < 27 then 0x525983a15255d091524351c651f6d88a51e6872151e1b63b51d7d8e651d010a251c60ead51c60a8751beef2251b94f6351b8529b519a9e3e5189efaa5189535b517a4ca8517a4882514562b45102075650f41dcb50ef1ba450eadccd50d0dd7950ccc33250b81bdf50b2233750a9af6150988e775070dbec50636f315062f39a else 0x54d571fb54d0c4d554d077ae54c776f254b6bb4b54a0a5f55464651f545853ba5454d2c75439d579542b4de45418a7ec53fc196e53e5883653b1c0965396e5ec5387a16153649359535c52f0533de7c1533bb4615328492653275d175326135653246ecb52f13bc352eecffa52de21cc52bfba5b52b1742252ac196d52646008) else (if j < 29 then 0x58abbf5d58a1ef12589bc3fd58594618584a4b5d583dced458391dbd5808658a57e7134357d24718576c569057620075575ff324571563755708d23556c5e04f56c355a156befbd5569dad4b569892bc55f9153355c1c1cd5588d847555a99905549da915542a850554268ea551a288c5502db205502c80d5500854554e19ded else (if j < 30 then 0x5ba138275b99552b5b966b175b51f1715ac146295aa8f0825aa0f6c85a9820395a888e815a807a045a52242e5a4b3c345a408e565a3df8495a262bcf5a1f2b5b59fc113f59e8513859d198f059a02b8f596fa0d0596d067759602b0459441ab959214a365906860d58ffc36d58fd960e58fbe68358df149358d8990058cf1758 else 0x5fc9cc685fb452405fa6a2115f9b80df5f9b13ef5f930ce45f847ff85f6211215f57ca0b5f4a452a5f36c8e45ee32e9c5ea407445e91b1365ddd422e5dd9faa35d6240765d0a6bb25d085acf5cd8de275cd54db45ccfa19f5cc3439d5c68caf75c60ae695c5810ad5c3f98045c3ee0f95c37b8195c0945325bf316df5bcf3e19)))) else (if j < 36 then (if j < 33 then (if j < 32 then 0x630eab8562f7cd6662e6465062e4b7db62cca18c62c1d0b662bdc0ab62b87ec362b6014b6281ea8f628133e9620312f161dcfdf061c4f57161c0af9e61b44510618ed7a96185e2fe6172f3a5616b5708614a7b5d6138024c611a2c4661056c2760ec67a460e18bdc60e0f85e60ded27b60b0cc4260a0831160790ac5606c0341 else 0x65f1581665e770e76584fb8f65670c42654f0f336536a780652e1cbc651d9d2d651c0afb650d527364f101a064cb2e0b64cb2a1e64bf39d964b24e0e647106426450003d64201d66641ebe08641bfaad640fae85640a176c63fb11b763c7bcfb63be2e4163997d7c638d00b9638bc7f96382fdb36377991b633b088563269680) else (if j < 34 then 0x69c4bcba69a9561d69a631de69636e99695a0372691c0e3a68f3b1f668f0b44f68b166b5689fcf056891c995685fe6f1685ca0ef683d1ac0680243b967f52b2467ca528267bfacbf67bb6f9967852efc677f185d6774e5bb675ef4f16724a37e66ca31d4667e1d66666564e966610ab6664f88c8663d1dc36629382b660ee74c else (if j < 35 then 0x6c42427f6c31f1166c0a97dc6bda7d3c6bbf98b26b88597a6b87b81a6b80fe836b7eaa686b7c8d6f6b73dce56b61a5476b5f581e6b52f1896b365c4d6b2f862c6b2aead26b1133936afcad076afc31706af769816aea4c736ad763f26ad75fcc6ac717596ab7edbf6ab4f0186aa30d236a8e75226a06d97869f512e969e2d90c else 0x6f070bf56eff428e6ef4a3bf6edf862e6ec355d26eb408696ea3d4d76e9162326e701a856e5f59d36e5b83a96e548ba56e4f6a6c6e45e2776e3e3a366e3637706e0aa5fc6e03a1026e00232e6de9d4aa6dcc15f36dafd8616d5e28376d4557436d17e3ed6cc44e1c6c9b6c2d6c9918a46c938a7b6c528d396c51b08a6c50aae9))) else (if j < 39 then (if j < 37 then 0x7276fd13727609f8724cac9a723b61707231217c720b879771f05f3b71ed406f71e9235e71e491b571dc56f371ac6495717f5195715839ab714efcea70f2a0c370ed146670e124217096174d707ab758701e9711701153916fe742646fe656c16fdbe6266fb02e2b6fa8ae1c6fa6d2736f9b805f6f7adbc36f7402bf6f17ba83 else (if j < 38 then 0x7607e26f75d0695a75bce490756e37487547093075450463753a349e752c9b0575206da0750d9bca74f187b774dedc9174d49bfb74c887a674b9c673749de376746ea735745f05087444ae91743969657400e11273fe7daa73fb531273bdb91073bcf03b730e50737304784572f3b0ca72e3893372dfd8c872d76d6d727f32a3 else 0x78c86b41788d29b77888881c788599c8787949f1784c07ca7847070278413cc2782eacb67818d43577db8d2977c827d477c36d2577c1c89a77bc93f477a9a262779d6029779bafce777b85f57779c165774b3f187749733c77161db576fa8ae476d8cff576d4aa1076afcbcf768c54b576851144767671d8767247a27639d4cc)) else (if j < 40 then 0x7b8a322d7b7810517b768e617b6120d67b5984397b0dc2347b084f0f7b0541177b00982e7ad3c05b7acfb90d7acefb6e7ac6fd247ab770be7ab0a3ec7aa6fcbf7aa425b27a9ef9737a4a39f97a0b40a479db768979d19ba879b422af79acba4879a27f7179725208795b853c7949194178e1a92278d7d9a378d7229878d15bcd else (if j < 41 then 0x7ec1ebeb7eb95b3c7eaeb1717eab8fec7ea234c67e96a7fb7e90c1d17e802f247e7dffe07e7d6a7b7e6382957e44f0487e2f3c467e1df1637dd98b817dc5fc9e7da3dfdc7d90affc7d7c6e627d4798747d2f1cfc7ceb2b977cd623d37cd306d37ccc9e717ccba4997c620e077c2b3c777c280b637c25da167becf92d7bc9788d else 0x8249ec07822c987282156e278208b06782038c4481d0722481a6d3398195234d81636faa811e818780bef6f580b85f05807405e3805c1e1d804f37e7802c0848802b4af4802446a87ff7a5e27fdd2d257fd4c51d7f91c2bf7f8adecf7f5ac77a7f5602aa7f539be67f402c837f1dd54d7f1d5c4c7f1979757eee2e977ed56ac2)))))) else (if j < 63 then (if j < 52 then (if j < 47 then (if j < 44 then (if j < 43 then 0x85a2d53085961972857abe2e85633052854dfb5a853c4af985241789852309d78503e8df84fbae2c84eb658b84e559fc84d9a4b9845bd2ed843f6fb4841d7488840c78e48409d53383f69e7d83dfcfdd839d703d837ffcb78363eec783537ec18312355782ec5dd582de431482d31a7382ac20218299437c8279f1b9825c3914 else 0x885ee4b6885d3fa38849163788333377882ad838880c4fbe8806f73987dc395e87ce9dec87b121c387ac05548784451487830b1e877d1d228753550a8752f8aa874b9670872cc851872c973187241b72871f5b468714e5ad86fdffab86fab5e286e1155286d28e34865ea6e8862674a2861b1358861030e585b5a5f985b15512) else (if j < 45 then 0x8b8d23ae8b83b5988b745fc08b5414088b4548e18b36dace8aba4c5b8aaa91678aa675c68a98cb898a9864cd8a8b45f78a7203a18a129cf38a0c166589ec847c89e757b289e4c84c89dbce2689d33cf6897fbc8289622ff0895c93a8895b5cc5890e601188fd68ff88f897a988f54c7188ca030b889cded888985fb68884dcac else (if j < 46 then 0x8ed5f2ad8ed312ba8ed0c8aa8ece21078ea525cf8e8c10a78e84772c8e8032db8e5e9faa8e46afec8e0818968df16d528dd6b7868dd57ef48dae295f8d8ceea08d40a1e18d3630758cca9c988cc5e0848cb4a9fd8c914e3c8c301ee78c1d2d3f8c102db18c00c2628bf91c718bd6773e8bc950168bbbe6ee8bad38888b96887d else 0x920a9f0791ef962f91e2b11291bb7ea49138c5fc911e4f1a9109f20f91085b4790fe0d8d90e6fd2790dcf03090bf450490aabf3f909183b490723ecd905da7609052cc49902a52a49025f4a09015b9c88fe32c2f8f85d90f8f7ca64a8f7a562d8f781a678f7030a18f5905bf8f0e481d8efef75b8efb5c768ee611cf8ee569c8))) else (if j < 49 then (if j < 48 then 0x95e6d332957b67a5957740b395757e2895603afa954fe991954bfa46954ba5129526679d9513ce6094fa03ac94d9824e94c711dd94927412946ad97e9469c79294532ecd94442c429438672a942916269401263493a465c4937f86e093607f39933cc0aa9312bb6e93094d6292b9f72c928bcdd492872782924e41389225828b else 0x99cb3b8699c0bde099a3db539965a8379932ee49990c027e98bf3378985a4a0a98533f26982672f79803901197c1b62a97acadb0977cb8f3976c01fa976bfdd49764e26f975f42b09758c6a9974ef147974718a5973afd7e96f90d5a96f8564f96df759e96ccedfb96bcb48796ad0a7396a76074964fe06d962c8e30961dce77) else (if j < 50 then 0x9d132f8f9cf991bf9cf1f33c9ce7bd779ce537059cd7e62b9cd556cc9cce330f9ccdf87b9cc5d6489cb1a1849c69affa9c44cc339c3b707b9c24f0b29c110fea9bc856b19b65b0719b519cdb9b5198b59af4fd029af3a0de9af230a49ae272769a8764c59a8341be9a8089f29a766afb9a43aa0d9a241ca599d9f54b99cd7904 else (if j < 51 then 0x9f9b57fb9f84a3619f7ccb4f9f7b5cac9f5c91e79f461edc9f39f9d69f2fdb1e9ee9b9699ed992bc9ed486e29ecb2b2a9ea5b6ba9ea0f2069e8c99e09e84fd439e81180b9e2ae51a9e26ee8e9e2095e69dfb32179dd6970b9dca727d9dc20e089daf45729d83b28a9d7c54f69d52be839d4bbe0f9d2887c89d1ae9779d1459e8 else 0xa20ba282a1e7902ca1e4d446a1d8e014a1c22242a1bc5928a1ab5b07a1a239d2a193f3b8a1856b4da17ba288a1753166a171d3d9a1690ea2a1590cb1a15359b4a14cdfd2a130acb5a130311ea12dd944a10ee557a10354fba0f7e4bea0bc4d73a0a8feeca06c4581a066d25ca04ee3cfa01190f89ffc34539fe326c39fbed38c)))) else (if j < 57 then (if j < 54 then (if j < 53 then 0xa46ece97a463f421a4624f96a4481f9ba43ea5aaa41c0297a418fa58a412bdf8a3f56ee8a3e3d80fa3dd1db8a3c043cca39ea006a37ab0f1a37956f1a376ee96a36de9b3a36d5b27a356c3fea34f98e0a301026fa2eefac8a2ce72d4a2c77b76a2b05effa2ad2303a2868ce7a26b4f2fa26a9824a23384f3a22c9f87a20ebe44 else 0xa7a83f93a79ea78da79c5690a78cb0eaa77c907ca74b50bca6d25b58a6c9c043a6b9936da6b40db5a69fc424a6958f0ba66dd64da64c0befa646765ea611a23da60557bda5f58393a5efd1a3a5de86c0a5db3d91a5daa6c6a5aedb71a5a774d7a59483a2a57789f9a576472aa571e2c9a4af34e8a4ad723da49c90b5a481e0c9) else (if j < 55 then 0xa9923733a95ce5a8a95be20ba94f8e71a94b9751a93fe8dda932303fa91b9e3ba91788e1a8f92cbca8f7bc9ea8f5c183a8c8e3c4a8c13feba8b99884a8a7f18ea89aa4bea8930d1ea88aab28a881b67da87dd925a87ba1e7a86ebccaa8492c67a82cd4caa81d230ca81ccec2a80e1a69a8019d78a7c3ac25a7b23325a7add7d3 else (if j < 56 then 0xad994e1ead7f3ec6ad67145ead65a00cad3be7f8ad336c2cad250baaad218c9ead1041bbac8da8faac2efbc7ac2660c7ac0b5836abef6582abb109a1abace82bab974b63ab7e6f21ab6e344cab6e3026ab13eb70ab0b7ca3aaf6e536aaec2658aac3907aaaabdea2aa4bd491aa47d73daa1cf55ea9fa2caaa9c610b3a9a142ae else 0xb013b0f6b00e7ceab00bfba8afed3217afe805ddafd50063afa3acd6af87c61caf81cc1faf6ab007af339888af30a7beaefe23e7aef1c852aedd2f9faed9eb0caecf0d4baea06f99ae9fd42eae7e0378ae75405dae6629feae366131ae043e31adf8c693adf4d0feadf3aa0dadebf0d8adde4366addc279dadc8aadaadabb3e9))) else (if j < 60 then (if j < 58 then 0xb26ef21eb22bd542b1fbafb5b1f88086b1e82f1db1e61ff2b1d0e901b1c2dc94b1be4dc4b1b789b1b1ac0fffb1a3b1edb18846abb1786329b175d6b9b1621378b146f3dab13e448bb12a8119b11a874db107bbe3b0c79749b0afbff0b0a3d243b09ef58eb095c73bb090b8dfb08773a5b067204bb066a9e5b05f4218b019ed35 else (if j < 59 then 0xb5996c0fb58d35b1b58b6e7ab553dda2b5081b9db4e2d89bb4c1dc0db46ee567b45f71efb459fbb6b44c8c50b445eff6b445eefab42bda59b41a0350b412290ab3fdfd70b3facbd4b3f3b72bb3cc2c1fb3bfdab4b375b35ab348efbeb336d42eb32c0893b31f2b45b3158e74b2eed251b2e8eed5b2cc3b6fb2c8b239b28fc095 else 0xb8739be4b85d67ebb84fc20ab847951eb843b308b81cf060b80e733eb7efb957b7e79cc9b7d0e459b7c1c59eb792cf95b78a8902b763e034b740ebb4b739eb40b6e0061eb6aeed9eb68bf843b6836787b6609704b63a028db6100b46b60eafccb5fd1aa4b5fb7971b5eb0b82b5e89513b5e40b0eb5de31b0b5b683e2b5aee70d)) else (if j < 61 then 0xbb2fb1c7bb226f3fbb082d62baefffd9baee5b4ebae736e8bab3179bba777875ba7605f0ba7065bcba693a3eba613eafba21a57bba218ca8ba182af5ba149a82ba071173b9eaa1deb9ea6184b9e86a83b9df5cb2b9ca0aa4b998c61eb972d092b9558d9db91d1f29b89cd5bcb89ac9fcb8948152b87af4c8b87ac711b876fe3a else (if j < 62 then 0xbe68af68be541a78be395ff2be1db0d9be0c4b9bbe072789bdf05bbcbde52171bde3bba6bdde3df8bdbd9c77bd6e1b21bd60c7ffbd53e30cbd1d851fbd1286acbd0f8d6cbcfa0f9ebcf87e55bceab6d1bce162b3bc9f8612bc9cc2eebc7615b2bc42ce6bbc377b88bbeda3c7bbd0068cbb90877cbb81fb08bb6957c3bb5c94c9 else 0xc12d9921c128ee57c1071423c103fb55c0ff7786c0d8ca4ac0d07290c0cc7d25c0c24a81c0a90116c0a7c09ec075ac5ac062eb12c044ecc0c01aa041bfdd8cdfbfcf9651bfc8f5c7bf91eb44bf51e06cbf5164d5bf4872bebf451ca1bf1c8cd5bef6b5aabeeb938ebece2ed1bec867a1beba2093be843437be7d15e5be774f1a))))) else (if j < 74 then (if j < 68 then (if j < 65 then (if j < 64 then 0xc43dc1adc418b7f5c4129d8ac3f79383c3d00f28c390fa74c38bca75c355e01ec34c8466c33bfe7cc334b993c2d7278ac2a667f0c29fbb74c2838d9cc27dc125c269cf18c25ce9fbc24c9f41c23c0099c2266937c21f04ecc21beea1c20a7ad9c2050bc6c1fe86a7c19e2a4ac19a8aa8c19852cfc18f4d0bc14efb53c1397ded else 0xc74e7378c742b462c738bc98c721995dc71f77e9c70825c7c6f2cf71c6dd91d6c6ab759bc69e41d2c69962bdc68bf70cc67d62cac66d3a1bc65e5252c65e4e2cc5f52b34c5f0b383c5d13e41c591deb8c58e0322c576e5dec5709a3fc5330972c5021c8fc4fad106c4e51267c4be652bc498e882c4888061c45f4e89c43f22ca) else (if j < 66 then 0xcad89808cac7758acac3a6aaca84a411ca70d26fca4abef5ca1c45a4ca0afac1c9c04219c9b3b68bc991da07c98f6803c9507d7ec92c2ee3c922ddabc91a689dc8ebad08c8d1a058c8cc45a3c89d5bd3c88e9ccac83c042fc83b7e3ec832b971c816b0c0c8144a82c7e1d73ec7d0048fc7baca74c7aa9c66c7a97f91c77a0175 else (if j < 67 then 0xcd2a1b40cd28fe6bcd1b32f4cd0ccc7dcd075958cd024e15cd01f454cccb6abbcc89e759cc89265ccc82f6b4cc8059a1cc72abfacc528b8dcc1b9edecc1a0273cbecb8f5cbe7c742cbda80d2cbbe8628cba0727dcb943aa8cb93d873cb83ed2ccb56d7e7cb4fceb4cb371c8bcb2dc0d3cb20b17bcb0d81fccb0d7dd6caf01919 else 0xd00135afcff0bde1cff08c16cfcd43b6cfaf5c39cf917892cf08233dcf060875ceefba80cee42a24cede6f9dcebeb839cea35c4cce978679ce958274ce8e9de5ce7c2e34ce643ef6ce456271ce05af70ce022df9cdfdacaacdb15d6acd9ffd82cd9732eacd93425ecd822cabcd7b1853cd774d9bcd73e17ecd4f8369cd4de109))) else (if j < 71 then (if j < 69 then 0xd36fe2d1d3472f3dd33774b2d3185dfad30e52efd2f36058d2cd5fe3d2a90c07d29e8f63d288f72dd280da9fd279816cd27324c8d261c915d250c8a4d22a8e3dd21efde1d1c0c32cd1acc58fd178b633d17342a0d1699e6dd15d83add155081fd13316fbd0f6ed9ed0aa6aa9d0948a2ad02662b3d00df4f9d00df0d3d00de223 else (if j < 70 then 0xd62a1c79d5bbad15d59a5f46d599b3b8d584aa9fd53f6fe2d51ad9f7d513896fd510b64bd50f43c6d50e4c22d501a9d8d4fb78ced4de2d0ad4dc887fd4c8aa9fd4a73589d4963b80d4926b05d48a8be6d4689782d46558b0d4643321d45dee77d44a797bd43c7e2bd43203f4d3eecb73d3c76d34d3a2cf82d39fc295d386a84d else 0xd8ed42c5d8e1fcecd8dee098d8d29dc8d8b75d1fd87f56acd8730019d81d2845d8130d29d7f43485d7d671d2d7c7f366d74b5c92d747a9b9d73e30ced7339c05d712b452d709d930d7015386d7012494d6d696acd6d0f878d6c54bc9d6937f24d682e37dd67f90a6d66f45ecd6668bc9d658bfa9d643a0ded641c9aad640382b)) else (if j < 72 then 0xdc0f3d3fdc065528dbf8a80adbba8d2ddb832312db81fbb6db67edb6db5badb6db575eb3db3f858bdb18b11fdae1b5dadace7c0fdabe9fc1da972e47da65644ada3c7db3da3c26e3da135a2eda116a69d9eabcf0d9e0aacfd9de5a77d9bde739d9b5caabd9aa95d5d999d7bdd968bf8fd95e6174d952d118d9067286d8f0d6ce else (if j < 73 then 0xe00b5889df964daadf6cfc50deff245edef2001edec8e593debeaad6deb1f5cbdea2bc78de82bd44de477f7fde4438e9de3f11c4de300eefde2f0414de24832addcdffc1dd9c5f6fdd3f8262dd3c26badd3b7ef7dd15da8edd13fc0cdcf09d21dcdbb8f2dcb3af3bdc9e499cdc9a7c0ddc7de61adc763822dc2e61d5dc18e195 else 0xe27b97c7e274265ce26803b2e24da12be246a0b7e2438515e1f67585e1e0e7d9e1cb4b11e1b7113fe1836056e17ebc82e179b476e1568883e1453da0e132a093e1303918e1134a83e0f79028e0f78c02e0c33959e0bb9449e0ae4d4ce0a4265fe08c7f19e04e9975e040ca2ee03b6292e03a550ee02fd236e026e797e0126741)))) else (if j < 79 then (if j < 76 then (if j < 75 then 0xe5b6907be5954822e53173c4e521735be500cae0e4f716fbe4f06e91e4d7794de4d33fc4e4d16f82e4c6c539e4a076d7e488c44ce47f8609e46c151fe468861fe464f6f7e4393e62e4192adde3e89f47e3af36d9e3936510e37a3566e37814e4e370e507e3658379e3590732e323ee83e30fb977e2a420f6e29991eae291b8ac else 0xe906c3ebe8f5a8fce8f58c2de8e0ec69e8c68e66e89360d6e82c8034e8223ebee81c2ecbe8108b71e7f08455e7b557dfe79b56f1e77bd4f0e77896fde75697a9e74dfd87e7404895e6b83bf0e6afb7f2e677538de6552253e637e477e635d73fe6291ff6e618d53ce5f6e4d4e5d05a61e5cc801de5cb347ee5c8da52e5c6fea9) else (if j < 77 then 0xebbeb34aebba15d4ebb47615ebb02aefeb9d762beb9af2c0eb8d77dfeb777cd9eb616fd1eb5fdd9feb2dc800eb17d616eb0d5048eaf4e77ceadff41fead4c229ea9a7385ea6deb00ea6d972cea50ee5cea4d1267ea45128eea0b8f9fe9e41fd4e9b56e5fe9732db3e95bc929e934241ae92eb5b3e9170ea5e913dd00e9072d30 else (if j < 78 then 0xee2fd407ee2f28b0ee27256fee1af096edf5c54cedef824feddcda93edac70ebeda790c5ed8e8866ed795146ed76848fed699f72ed648639ed62d17ded5aa75eed4249dded271598ed19befbed13d0b9ed054a6decfbeeb5ecdc21bbeccdd562ecbbd0c9ecb76735ec5a0102ec463364ec25bf70ec1c98aeebd1779debc13139 else 0xf0090bf5eff1c7deefea597eefd53ddcefcb1aa2efbb7b0aefa5a30aef694577ef6655c7ef639eaeef516159ef446be1ef2178aeef2068aeef1d4bf9ef01d558eefd70f7eeed263deecb9e60eebe845beebb7c32eeb3a2f4eeb08ca9eeab01d5eea1ece6ee8024afee79500aee6fb445ee673338ee5d9be8ee5385e1ee39006b))) else (if j < 82 then (if j < 80 then 0xf2ee8cb5f2da2638f2c267ebf2b68d81f2b5b258f2a23095f29f87c8f2993dd5f2913a7ff262b80cf25ba095f22e4ed4f218cf1cf206f684f204063af1e59ffbf1cc2c1ef1aa264cf179182af16862f4f1635088f15eec27f1404758f12d868af10cf6b9f0bf25a9f0bee35ff0b2af60f0a12d52f048cd0cf0489a30f013583a else (if j < 81 then 0xf5b47037f5b1eef5f59c2344f58d421ff57af3b0f57509eff56df077f5682d44f560d24df5406866f527b034f50ec095f50e8b37f502d6b1f4ec2699f4dc053af4ab4ec8f4a41734f4a0f788f49e8f7ef484876ef4838668f46411abf4404b49f41f29bdf3a21acff3a216a9f39b5241f3933c99f38ef10ef37881f1f36eabdd else 0xf89ae26df890e9a9f86f1edaf841e6c5f809a614f8080189f7ea65bdf7dc6ee0f7d58f3ef7a1e396f7927ec0f78fac2bf775b10af77422eaf7700d15f7692d1ff7636973f75c1392f75693fff726b7eaf7194219f6d269a8f6a9ac08f678ec6ef66d8a96f656f8e9f6560da0f6485493f6100e20f5e9271df5dbd552f5ce5ea5)) else (if j < 83 then 0xfc053deffc0539c9fbe836b4fbe50388fbde1c75fba80676fb75cd3afb6a805bfb65e183fb5c772ffb427ae8fb380d75fafed989fafbd6f3faf9d0effa9ba9c3fa934a11fa499438fa3de035fa2a83bcf9bbb9f0f9a90722f9a16a85f95aaf8df9179f59f91794bcf9074a02f8e6dfbff8d80f42f8d47789f8c94cc5f89eb9e3 else (if j < 84 then 0xfde62360fddd7f3ffddbe92dfdc2a751fd95aca4fd85c511fd819241fd6e7e8cfd5b4c1ffd50ddc6fd4259c2fd41d700fd412d36fd3d5eccfd34bc45fd10c55efd014188fcfde6a8fcfa9083fcf74cf0fceffd02fcece4e3fce6df01fcdfde8dfcdaa4c9fcc3f02ffcae8891fca2802bfc9f9253fc856baafc3e8eb2fc2bb20f else 0xffec7ec8ffec6fd1ffe93df6ffba7e1cffb99b38ff9a0a61ff9054d1ff6c1870ff323adaff18c3dfff004551fef0b265fed34086fea6d72efe971e33fe473f5cfe37318cfe1da190fe15ccf4fdf8ff6dfdeeca22))))))) else 0
  | 7 => if j < 30 then (if j < 15 then (if j < 7 then (if j < 3 then (if j < 1 then 0x76ceda107480dd0071d545406df713a064db3eb0606ffb905aa00c3057931f5056de5eb0527ab17050b86da04e4d99e04b07ac10490c7ce03fdd79b03ad1ad60380b320037896920315e30c02d2974e02c62fe70290438b023c15450228525502131e5301e751fe01e0518a01a3e1ce015ff260015e891201408b0700ce3511 else (if j < 2 then 0x100399ab0fdcc8ae0f37cd540e5dff8d0e3490170e1e27490e1a44850d87ca8b0d6314f00cc78caa0c4076e60bde7ae90b6810f20b4e26e80b42968c0b02ef350afcbf380af6cc8a0ab3d3bb0aad869e0a92db4b0a8b05b40a64587809ad0f030982417c0954990008b5113d0845aec1080fc2650802dd48079afa6f076d020a else 0x173d8bb317295cfe171ea98016c8165416c068bd16beba9c16b4d86116971d50167f341c163f3bfa157cb10f1504a17d1502fcf214ffec12145d3f6c144a55bc14384051142caff514275312141a044d1335031412af6ba012883d881228ea011209bbfe11ffdf6611e1fc1f11bff5c011ab962811044ac9105af6631029f29a)) else (if j < 5 then (if j < 4 then 0x203905fb1ff52cea1f7fbab41f166a8f1f0a996b1ea744e91e21c9ae1dd8cca61dd8c8801dcc0d5c1c6a195f1c61edf61c2583f31c1f1c7d1bfeb2f61b922f781b920eff1b8165d51b464cfa1abda2ba1a8420571a827bcc1a3c2ecd1a0a266e19ee6c231999832718f89880182eea7a180b1eb81807bc6217a655ef17893ad8 else 0x2b9fafed2b87e4442b2cd82b2a6cb88629f1c6dc29b66672293b1b8327ae8cc126ac4e79269dc800266272fd25b2e9882565060b254d119124f3517624a577cc2467a6a72406c06023d00420238de37d23790ba4231897c4229b17aa2207b8aa22062b7721a409c0219e9b572134315520906f582064930e2046bff7203d2194) else (if j < 6 then 0x3482e5ff3468ddc933f9792e33bc88d433b300643339f50032bfb248329b9dc1323b38043214f2ae3185609a3140e60d3121f7af3107631e30d879d0309632263032db5f2fcd44b32f30278a2ec8d9512ebd01f22e972a702e79fa542e2e683f2df8fd7b2cc234392c99f6172c82019d2c44d3fe2c23fb972c1d46da2bcf1343 else 0x3c0552713bfa005d3ba1e9863b81fa8c3b6822e63b3f86883b1afd3c3b0d8d273ab914b83a5d78c83a11a47639a3d74138f9ec2b38c4433938b75e1c38730116383f3122383c1ad7380d69dc37db0d6d37bab6de3704df74368138a23670ede8366518f63641590a360fa4ac35b88370352b587034b0b61e34a364443487a9f9))) else (if j < 11 then (if j < 9 then (if j < 8 then 0x463a6114462e0e5945d4ee424554e50944e419c6449fbcc043dae5cd432cf8b34327858e42a3d9f542a322ea4292d83041faad084101796640e7a1c040d8c74d40cd36f140a4d04740876c9a4042722a3ff446083fd3e2c13ee8cfa03ebd88093e9ffe363e7dc14a3e36dcf63dad79d93d1359563d0c94dd3c5fcce53c1a8991 else 0x4f39104f4f1985a14e87063a4e63ebe44e3f22534dbbca6e4d89a8c44d30f6544ccb1cfe4c89caf24c61f5e04c3e08ed4bb9dfee4b9eac814b2f6ffc4ae367f04a913f1a4a845f574a7437df492e7f2548bfa379488557a14881b72d4880f6cb48116c5247a44cf2476c4232472f776f46eab82746e2770646b1b76c46985636) else (if j < 10 then 0x589230bb583bbc45583a2b255827d01457ddd28e57b85d8e57a5d2b35764d305575e15c4575942a956f74b8756d891d356a9ea02569b113b5655a9c5564b047a551d0c935464651f53cd8159536c6d23533f955053275d17530a5db25309083d52d39c8d5264600851f6d88a519a9e3e50a8e282503626655020bec74f880091 else 0x6127679a60a9b9516064fa095fc4aeba5f8ee6635f8dd3995f733d325f6aa6b55f666f325f4baf315f43123a5edac2bf5ed081635e902fab5e19fea25e037ed95def04905ded32085cd54db45c5810ad5ba8683a5b81113f5b5d77595aa8f0825aa81e765a4b3c345a309f5b5a158b515a074de35960ba3f59441ab958dabf29)) else (if j < 13 then (if j < 12 then 0x6ad763f26a5c674c6a44a09169b41cdf697a6ccf6933d6ca68b272d168b166b567ca5282677f185d670c797e66c19eeb6629382b65adce876557e518651db376651d9d2d650d527364cb2e0b6450003d640fae8563c7bcfb63bd020c63997d7c6382fdb36358f17b6331e7db624ad3a861ff998361d5c0b1618dee196138024c else 0x7245ca4071df5db3719c8c3a7184a0c2715839ab7153003671476fda714190c27117b5a270cb9eb46ffd20046ff18fa86fdbe6266fd7d6ef6f80a7ac6f7adbc36dafd8616dabfbe36d9a43316d6d65556d61d4f96d4557436cf1f72f6c528d396bd8bad16bc0d30b6bb0d0ab6b88597a6b4b5a726afcad076afc31706aec50b5) else (if j < 14 then 0x7a3aa79b7a1cedd279f2b9d079c5945c79a244f6799a67f6797833847939dc6279295f9978cfe917782bedba7802f3b477e3fc307776a479774b3f187741f1357738ecc67725ca4c765e928a765b5edc75544181753a349e752bfeba74d3fde4743969657424b4a673d66a1e739adedd73920d1872f268fb72e38933726eea58 else 0x835c1bfb834fdaee834bca92829def4e82925a31828c5e5f826e8b448248015982329e4481cda0b181669b9b81636faa81216c0a8078834e806e08557fbccc1f7f4578457f44119e7ebff0da7eb95b3c7e88a71f7dab2f3d7d5c18657d3aa9607c554f0b7c3fca7f7c272bef7be3f0d07be334b97b7c1b4a7b7810517ad3c05b)))) else (if j < 22 then (if j < 18 then (if j < 16 then 0x8c2d3b4e8ba0ac758b9ed0408b4a138c8b42f8278aaa91678a4fc7b18a3cbdf68a3bd6ac89f89b8d895c93a8894ad58188f897a9884916378810ac7a88086dd387ce9fe187c5c6ad87b121c3872cc85186dce23085c0c6ca855c2112853d54d2853c4af9852dad35852b128d851486cb843f6fb483f8255b83dd14ce837918cf else (if j < 17 then 0x95603afa94d9824e94c42f59947e7940947c3dcf9472e8e4946ad97e94377e87942cf98793daf47093d4779c92f5319b928bcdd491ec832091e2b112911e4f1a90f14547909fef0a908cc61e9047c5b2902a52a48fd8d1288f781a678eeb5aa48e77b8cb8e5480b38e30594a8e2b4aee8e17c69e8df90aa68dd9d2618d0c4efa else 0x9c69affa9c65556c9c5fb5ad9c5425519c4cd2829bdf4b049b9aedfe9b87b3109b7865e49b519cdb9a8f94799a766afb9a60adf79a248c169a241ca59a05248799d9f54b996b4c7b992b5521992637e098d87e839876d450976c01fa976bfdd49764e26f975f42b096fa140d96e3240f968c8c8f9615592095d21e0195c2e9fe)) else (if j < 20 then (if j < 19 then 0xa70b82b4a6a9ec40a646765ea577665ca5312558a4fe15e7a4e90587a44691d9a3e47614a2889c77a2380dd8a1fed9aba1e4d446a1bd1038a193f3b8a0f7e4bea0f0eb03a0d6a847a0a8f979a076f11aa04ee3cf9fd692a89f84a3619f75611b9f461edc9ea5b6ba9e6773709e3d13369d4a492c9d4717269d132f8f9c844cf0 else 0xaefb1264aef25ee0aeda7cdcaea941a4ae534f0badf2b03aade82f50ad8b1e25ad600b95ad250baaad02a65dacdbacc3ac1df593ac126537abfb0618abe5ff41ab974b63ab945bfaab46e95baaf6e536aac3907aaa5b3f44a9c610b3a91b0ae6a8f20044a8b7e4b4a88aab28a86ebccaa839ad28a7c708fda7a58cd0a74a80b7) else (if j < 21 then 0xb8fd970bb8a8ddb6b81cf060b7c1c59eb7c11e10b7adf98fb76d47edb702fcd2b6f8f383b6ed6327b6c15908b63affb3b58d35b1b4e51f81b4c91eeeb4904ab4b459fbb6b404d1bfb3f351b8b3c492f7b29d7186b25b2b9db25564d2b1f88086b1e82f1db0e8413eb0d98332b07057bcb00db6d7afb1172faf92610caf2ce55b else 0xc0ded378c075ac5ac07092e0c06fd65ac06570cdc044ecc0bfc2e11fbf65938dbf4872bebf150d7fbefec733bedfcfafbe84c396be7d15e5be774f1abe225333be0fb35bbd70a956bd6e1b21bcd1e3a2bb879549bb7ff8acbab84d9aba149a82b9df5cb2b9c8f3e4b972d092b97250b7b95a6eb3b94ede57b9297f4db908686d))) else (if j < 26 then (if j < 24 then (if j < 23 then 0xc98c9959c8cc45a3c87fd200c802add1c7baca74c7a97f91c6cd3dedc65e5252c614bfbbc6092f5fc5f52b34c5d13e41c5b8f113c5b29dbac5455fbdc52a52b5c4e51267c45f4e89c45f4a9cc3a858b7c351228ac2720af9c25ce9fbc246d506c1f50722c187c7e8c1604263c146dd87c1414adfc1071423c104d8afc0ff7786 else 0xd280da9fd26ceec2d18420bcd162a13ed1445952d1222307d0f12a03d094b192d0892136d07c5f54d0504467cf9b49d1cf08233dcec19a2cceb74c1fce0aeb82cd822cabcd616bedcd28fe6bcd179f10cd0b8f22cd097853ccdf91ceccdefdf0cc4958cecc3af2c5cb20b17bcb1bd898cad1b13eca861296c999c2cdc994503a) else (if j < 25 then 0xdad04b1bda88b64cda44c46ada0fb6c3d9f5eeffd9de5a77d9b5caabd967d45bd96678bdd93276f1d9067286d87a9d49d87885a7d7bd1012d76eecb6d7263815d71ecac2d70ac4f7d60a9256d5bbad15d59ecea8d5738c4ad50f43c6d4d5a1bad45edb9dd43203f4d41481dad413ba48d408963ad32be793d28bafabd288f72d else 0xe2807e53e207a3dee185a67de147b52ae1004f44e0fe1c4fe0f79028e0f78c02e0477fcfe03816badff403a5dfa71e44df48ad74df0bddb8df00072fdeb63da8deb1f5cbde513e12ddd98c7edd8af886dcece099dc9e499cdc60382adbf4f6b5dbeea129dbe29315dbc18363db929b3adb78114edb202ff8db1d0535db0a57f8)) else (if j < 28 then (if j < 27 then 0xeb4c2af0eb328683eb2dc800eb17d616ea9a7385ea93dd86ea724904ea6a8c85ea064828e9dca651e96857cce9590968e913dd00e8e7b45ee8b98191e8435262e82c8034e8108b71e7fab8c5e7a4ccf8e74ceba2e74b34a3e5d05a61e5c6fea9e47f8609e3945e26e3658379e2f80f45e2dfeb10e2ad015ae2910c97e2858caf else 0xf3fde3f4f354a5eef2a803c2f242bcdaf1e2c529f114c204f05d8eb4f04a5bf6f0380c7ef032701bf02e734ff0184913f0013291eff1c7deef9ae682ef8f5626ef01d558eefd70f7eed9bd04eece2ca8ee673338ee39006bedf2c028eda790c5ed699f72ed5e97c9ed4249dded2cf331ed2162d5ec5a0102ec142aa5eb6a97bc) else (if j < 29 then 0xfbfac035fbf31589fbe0f300fb5c772ffaf9d0eff9c40196f9b117e6f9994505f9852238f977ace6f93e38ecf8fa0ae9f8efafbbf8b28667f811b235f7a42ab7f781edcbf781c2aef7676027f7605fb3f6c09930f68e348bf650d505f6019168f5dcf855f5dcce5af5b1eef5f57af3b0f5147008f513cf5df42bc60df41ca30d else 0xfff9b31bff9e07e2ff9054d1ff8bb134ff18c3dffed89f2cfe426e30fe2d9bfcfdc32497fdb809c4fd32aeb8fd15df76fd014188fce6df01fcdfde8dfc8dd471))))) else 0
  | 8 => if j < 2 then (if j < 1 then 0xbedfcfafb9df5cb2b6f8f383b6ed6327b1f88086ad250baaaac3907aa7a58cd0a4e905879fd692a896155920902a52a48e2b4aee884916377c272bef651d9d2d63c7bcfb6138024c57a5d2b350a8e2824b2f6ffc3e9ffe3639a3d74134a3644430d879d0254d119122062b7716971d50145d3f6c0a8b05b40802dd48050b86da else 0xff18c3dffbe0f300f9994505f68e348be7a4ccf8e3658379e0f79028db78114ec45f4e89c351228a) else 0
  | 9 => if j < 1 then 0xaac3907a else 0
  | _ => 0


def dictB (j : Nat) : Nat :=
  if j < 15 then (if j < 7 then (if j < 3 then (if j < 1 then 0x104000800002f80015c00098000480002200010800080000230000f800074000380001b0000d0000600002e000160000a80005000026000120000800003c0001c0000c000050000200000e00006000020000080 else (if j < 2 then 0x3c0001c0000df8006ec003440019f000cc000600002fe00177000b100057c002a8001400008f80045c002200010800081000400001fe000f700077800388001c0000df00066000308001800009f0004b8002200 else 0xbc40049f00244001200008be0044a002220011000083e0040800202001000007ce0027f001338009800040a001ff000fd8007e8003ee001f6000f98007c8003de001ee000f50007a0003ce001e6000f18007880)) else (if j < 5 then (if j < 4 then 0x180000a57005220027fc013e4009e6004f10025100123e009100048400241801200008e20042f802110010800081f0040b802040010100080400400001d1000dfe006e60037000193000c88005ff002f50017980 else 0x1fcc00fe2007f0003f1001ea800f4c007a3003d1001dbe00ecc00763003b1001cce00e5f0072f00397001cae00e560072a00393801c9800e460072200390001c3e00e1d0070200380001bc400d800060f8030600) else (if j < 6 then 0x3dde01ecc00bf7805bfc02dde016ee00b76805bac02dd0016e700b70005b3002d5e0166f00b0f80583402c180160000af50053a80293e0148800a04004bbc0217e010ab0085180422001ffe00ff7007fb003fb80 else 0x5d8802e5f0172a00b93005c88029e20148700a400051800281f0140600a00004bc4025540120f8090500481002400010ff8087c8043d4021e20108f808428042000209f010440082000403e02010010040080000))) else (if j < 11 then (if j < 9 then (if j < 8 then 0x6b540359f01acc00d62806b10034ea01a6f80d33006994034c801a4f80d274069380349a01a4c00d238069180348a01a4400d2000683e0341d01a0400c7a8063540309f0184400c1300601002fee017a700bd100 else 0x86ee041f30209981004407fdc03fcc01f6f80fb7007d9c03ecc01f6400fa3007c9803e0c01ef500f6200799003c9f01e4c00f23007910036ff01b7780dbb806dd0036cc01aff80d7e806bdc035ea01af400d7200) else (if j < 10 then 0xd20006810030f90184400bffe05ff702ff00178740a376051b3027fb813ddc09ea804e55025fb812f88096fe04b77025ba812dcc096ce04b600259b8129dc0942a04a00024fb8127c80923e04917024880124000 else 0xd3e4069f0034f401a7880d3c0069d0034cf81a6600d32406990034af81a5500d2a406950034a201a4cc0d23e0691d0348e01a46c0d234069180348b81a4580d22a069140348981a4480d222069100348401a4100)) else (if j < 13 then (if j < 12 then 0xe1760701f0380c81c0000dffe06ff6037ea01bddc0debe06f5e037ae01bd580dea806f4c037a201bd000dca806df2036c801b5400da3e06d180368a01b4400d7ee06b770358a81a7fc0d3f4069f7034fb01a7cc0 else 0xf93007c1803dff81efdc0f7c007a1d03cdd81e6cc0f3300791f03c8c81dffc0efd0077e003b7f81d8740eb76075a803acc01c7fc0e3f6071e2038df81c6ec0e372071b3038d881c6ac0e346071a0038cc01c4ec0) else (if j < 14 then 0xfec007f3f03f8f81fc740fe3807f1003f8401fbfc0fdd007ee003f4e81fa200fcba07e4403f0f81f8740fc3807e1903f0a81f8340fc1007e0003efd01f7600fb3e07d9c03ecd01f6600fb2007d8803ec001f4600 else 0x1fff80fffa07ffb03ffc01ffdc0ffea07ff303ff801ffbc0ffd807feb03ff501ffa00ffce07fe403ff101ff800ffb807fc803fdf81feec0ff5007fa003fbf81fddc0)))) else 0


def dictP1B (j : Nat) : Nat :=
  if j < 15 then (if j < 7 then (if j < 3 then (if j < 1 then 0x1fffff000000001fc07f000000001fffff000000001fff80000000001fc07f000000001fc000000000001fc0000000000000000000000000003fff00000000003fff00000000003fff00000000003f8000000000003f8000000000003f800000000000007f0000000000007f0000000000007f0000000000007f00000000000000000000000000000000000000000000000000003fff00000000003fff00000000003fff00000000003f8000000000003f800000000000007f0000000000007f0000000000007f00000000000000 else (if j < 2 then 0xfffc0000000000fffc0000000000fe03fff0000000fe03f800000000fe000000000000fe03fff0000000fe03f800000000fe000000000000fffffff0000000fffc07f0000000fffc0000000000fffffff0000000fffc07f0000000fffc0000000000fe03fff0000000fe0007f0000000fe000000000000fe03f800000000fe000000000000fe00000000000001fffff000000001fc07f000000001fffff000000001fc000000000001fc000000000001fffff000000001fffff000000001fc000000000001fc00000000000003fff0000000000007f00000000003f80 else 0xfffc00000000000003fff00000000003f8000000000000000000000001fffff000000001fff80000000001fc07f000000001fc00000000000003fff00000000003f800000000000007f000000000000000000000fffc07f000000001fffff000000001fc07f000000001fc0000000000000007f0000000fffffff0000000fffff800000000fffff800000000fffc07f0000000fffc07f0000000fffc0000000000fffc0000000000fffffff0000000fffffff0000000fffff800000000fffff800000000fffc07f0000000fffc07f0000000fffc0000000000fffc000)) else (if j < 5 then (if j < 4 then 0x7f0000000000007f01fc07f000007f01fc07f000007ffffffff000007ffffc000000007ffffc07f000007ffffc000000007ffffc07f000007ffe03fff000007ffe00000000007ffe03f80000007ffe0007f000007ffe00000000007f01fc000000007f01fffff000007f01fc07f000007f01fc000000007f0003fff000007f000007f000007f0000000000007f0003f80000007f000007f000007f00000000000000fffc07f000000001fffff000000001fc07f000000001fc000000000001fffff000000001fc07f0000000fffffff0000000fffff800000000fffc07f else 0x7ffffc07f000007ffffc000000007ffffc000000007ffffc07f000007ffffc07f000007ffffffff000007ffffc07f000007ffffc07f000007f01fffff000007f01fffff000007f01fc07f000007f01fc07f000007f01fc07f000007f01fffff000007f01fffff000007f01fffff000007f01fc07f000007f01fc07f000007f01fc07f000007f01fffff000007f01fffff000007f01fc07f000007f01fc07f000007f01fc000000007f0003fff000007f0003fff000007f000007f000007f0000000000007ffffc000000007ffe00000000007f0003fff000007f0003f80) else (if j < 6 then 0x3fff01fffff0003fff01fffff0003f80fffffff0003f8001fffff0003f8001fffff0003f8001fffff0003f8001fffff0003f8001fff800003f8001fff800003f8001fc07f0003f8001fc0000003f8001fffff0003f800003fff0003f8001fffff0003f800003fff0003f800003fff0003f800003fff0003f8000000000003f80fffff800003f8001fff800003f800003fff0003f800003f800003f800003f800003f8001fffff0003f800003fff0003f800003f800003f8000000000003f800003f80000007ffffffff000007ffffc07f000007ffffc07f000007ffffffff else 0x1fc07f01fc07f01fc07f01fffff01fc07f01fc07f01fc07f01fffff01fc07f01fc07f01fc07ffffc00001fc07ffe03fff01fc07ffe0000001fc07f01fc00001fc07f0003fff01fc07f0003fff01fc07f000000001fc000fffc00001fc000fffc07f01fc0000003fff01fc000000007f01fc0000003f8001fc000000000001fc000fffffff01fc000fffc00001fc000fffff8001fc000fffc00001fc000fe03fff01fc000fe03f8001fc000fe0000001fc0000003fff01fc0000003f8001fc000000000001fc0000003fff01fc000000000001fc0000003f8001fc0000000000))) else (if j < 11 then (if j < 9 then (if j < 8 then 0x1fff80fe03f8001fff80fe03fff01fff80fe03f8001fff80fe03f8001fff80fe03f8001fff8001fff8001fff8001fffff01fff8001fffff01fff8001fff8001fff8001fff8001fff800003fff01fff800003fff01fff800003fff01fff800003f8001fff800003f8001fff800003fff01fff800003fff01fff800003f8001fff800003f8001fff80000000001fff800003fff01fff800003fff01fff800003f8001fff80fffff8001fff80fe03f8001fff800003fff01fff800003f8001fff8001fffff01fff800003f8001fc07ffffffff01fc07ffffffff01fc07ffffc07f else 0xfe00000fffc07ffe00000fffc000fe00000fe00000fe00000000000001ffffffffffff01ffffffffffff01fffff01fffff01fffff01fffff01fffff01fffff01fffff01fffff01fffff01fff8001fffff0003fff01fffff01fffff01fffff0003fff01ffffffffff8001ffffffe03f8001fffff01fff8001fffff0003fff01fffff0003f8001fffff0003fff01fffff0003f8001fff8001fffff01fff8001fffff01fff8001fffff01fff8001fff8001fff8001fffff01fff80fffffff01fff80fffff8001fff80fffffff01fff80fffff8001fff80fffff8001fff80fffff80) else (if j < 10 then 0xfffc07ffe00000fffc07f0000000fffc000fffc000fffc000fe00000fe03fffffffffffe03ffffffc07ffe03ffffffc000fe03fff0003ffffe03f80fe03f80fe03f80fe00000fe0007ffffc07ffe0007ffffc07ffe0007ffffc07ffe0007f01fc07ffe0007ffffc07ffe0007ffffc000fe0007fffffffffe0007ffffc07ffe0007ffffc07ffe0007ffffc000fe0007ffffc07ffe0007ffffc000fe0007ffe0007ffe0007f01fc07ffe0007f000007ffe0007f0000000fe0007ffffc07ffe0007ffffc000fe0007ffe03ffffe0007ffe0007ffe0007ffe00000fe0007ffe00000 else 0xfffc07ffffc000fffc07ffffc000fffc07ffffff80fffc07ffffc000fffc07ffffc000fffc07ffffc000fffc07ffe03ffffffc07ffe03f80fffc07ffe00000fffc07ffe00000fffc07fffffffffffc07ffffc07ffffc07ffffc000fffc07ffffc000fffc07ffffc07ffffc07ffe00000fffc07ffe03ffffffc07ffe03ffffffc07ffe03ffffffc07ffe03f80fffc07ffe03f80fffc07ffe03f80fffc07ffe0007ffffc07ffe0007ffffc07ffe0007ffffc07ffe0007ffffc07ffe00000fffc07ffe00000fffc07ffe00000fffc07ffe00000fffc07ffe03f80fffc07ffe0007f)) else (if j < 13 then (if j < 12 then 0xfffff800003f80fffff800003ffffffff800003f80fffff800000000fffc07fffffffffffc07ffffc07ffffc07ffffc07ffffc07ffffc07ffffc07fffffffffffc07fffffffffffc07fffffffffffc07ffffc07ffffc07ffffc07ffffc07fffffffffffc07ffffc07ffffc07ffffc000fffc07f01fc07ffffc07ffffc000fffc07ffe00000fffc07ffffc000fffc07ffe03ffffffc07ffe03f80fffc07ffe0007ffffc07ffe00000fffc07ffffc07ffffc07ffffc07ffffc07ffe0007ffffc07fffffffffffc07ffffff80fffc07ffffc07ffffc07ffffc07ffffc07ffffc000 else 0xfffffff0003f80fffffff0003f80ffffffffffffffffffffffffc07fffffffffffc000fffffff0003fffffffffffe03f80ffffffffe00000ffffffffe03f80ffffffffe03fffffffffffe03f80fffff80ffffffffffff80fffff80fffff80fffc000fffff8001ffffffffff800003ffffffff80fe03f80fffff80fe03f80fffff80fe03f80fffff80ffffffffffff80fffff80fffff80fffc000fffff80fe03ffffffff80fe03f80fffff80fe03f80fffff80fe00000fffff80fe00000fffff80fe03f80fffff80fe00000fffff80fe00000fffff80fe03f80fffff80fe03f80) else (if j < 14 then 0xffffffffffc000ffffffffe03fffffffffffe03fffffffffffe03fffffffffffe03fffffffffffe00000ffffffffe03f80fffffff01ffffffffffff01fff80fffffff01fc000fffffff0003ffffffffff0003f80fffffff01ffffffffffff01fc07ffffffff0003ffffffffff0003ffffffffff0003ffffffffff0003f80fffffff000007ffffffff0003ffffffffff0003f80fffffff0000000ffffffffffff80ffffffffffff80ffffffffe03fffffffffffe03fffffffffffe03f80ffffffffe03f80ffffffffe00000ffffffffe03f80ffffffffe00000ffffffffe03f80 else 0xffffffffffffffffffffffffffffffffffffffff80ffffffffffff80ffffffffffc07fffffffffffc07fffffffffffc000ffffffffffc000ffffffffffffffffffffffffffffffffffffffff80ffffffffffff80ffffffffffff80ffffffffffc07fffffffffffc07fffffffffffc000ffffffffffc000ffffffffffffffffffffffffff80ffffffffe03fffffffffffe03f80ffffffffe03f80ffffffffe00000ffffffffffffffffffffffffc07f)))) else 0


def dictP2B (j : Nat) : Nat :=
  if j < 15 then (if j < 7 then (if j < 3 then (if j < 1 then 0x24489122448912204081020408100e1c3870e1c3870e1c3870e1c3870000000000000000000000000000000000000000000408102040810200000000000000162c58b162c58b0e1c3870e1c3870a142850a14285081020408102040e1c3870e1c3870c183060c18306081020408102040e1c3870e1c3870c183060c183060a142850a14285081020408102040e1c3870e1c3870c183060c1830608102040810204060c183060c18304081020408102000000000000000408102040810200000000000000060c183060c183040810204081020000000000000004081020408102 else (if j < 2 then 0x3060c183060c18204081020408103e7cf9f3e7cf9f3e7cf9f3e7cf9f3468d1a3468d1a2e5cb972e5cb972850a142850a14204081020408101e3c78f1e3c78f1e3c78f1e3c78f142850a142850a0e1c3870e1c38708102040810204000000000000000e1c3870e1c3870e1c3870e1c387081020408102040000000000000004081020408102000000000000003e7cf9f3e7cf9f3e7cf9f3e7cf9f366cd9b366cd9b3468d1a3468d1a3060c183060c182e5cb972e5cb972040810204081024489122448912204081020408102e5cb972e5cb972e5cb972e5cb9720408102040810 else 0xb56ad5ab56ad5aaf5ebd7af5ebd7a142850a142850a142850a1428508f1e3c78f1e3c7850a142850a14281020408102040810204081020408f1e3c78f1e3c781020408102040810204081020408102040810204076eddbb76eddbb5ebd7af5ebd7af56ad5ab56ad5ab50a142850a142842850a142850a13e7cf9f3e7cf9f3e7cf9f3e7cf9f3c78f1e3c78f1e3e7cf9f3e7cf9f3c78f1e3c78f1e3e7cf9f3e7cf9f3c78f1e3c78f1e366cd9b366cd9b3468d1a3468d1a3468d1a3468d1a3060c183060c18366cd9b366cd9b3468d1a3468d1a366cd9b366cd9b3468d1a3468d1a)) else (if j < 5 then (if j < 4 then 0x810204081020404e9d3a74e9d3a7408102040810203e7cf9f3e7cf9f3c78f1e3c78f1e3468d1a3468d1a3468d1a3468d1a000000000000000e1c3870e1c387081020408102040000000000000004081020408102000000000000003468d1a3468d1a0e1c3870e1c38700000000000000000000000000000e1c3870e1c3870e1c3870e1c38708102040810204000000000000000000000000000000000000000000c183060c183060fffffffffffffff5ebd7af5ebd7af1e3c78f1e3c78c183060c183060c183060c183060bf7efdfbf7efdfb56ad5ab56ad5ab56ad5ab56ad5a else 0xf5ebd7af5ebd7af5ebd7af5ebd7af1e3c78f1e3c78e1c3870e1c3870c993264c993264c183060c183060c58b162c58b162c183060c183060efdfbf7efdfbf7e1c3870e1c3870e5cb972e5cb972e1c3870e1c3870d7af5ebd7af5ebcf9f3e7cf9f3e7cd9b366cd9b366c993264c993264cf9f3e7cf9f3e7cd9b366cd9b366c993264c993264c58b162c58b162c183060c183060c58b162c58b162c183060c183060c183060c183060cf9f3e7cf9f3e7cb972e5cb972e5c183060c183060c183060c183060b56ad5ab56ad5aa142850a1428508f1e3c78f1e3c789122448912244) else (if j < 6 then 0xf7efdfbf7efdfbe1c3870e1c3870f7efdfbf7efdfbfffffffffffffff7efdfbf7efdfbf5ebd7af5ebd7af3e7cf9f3e7cf9f7efdfbf7efdfbf1e3c78f1e3c78f7efdfbf7efdfbf1e3c78f1e3c78e1c3870e1c3870f7efdfbf7efdfbd7af5ebd7af5ebcf9f3e7cf9f3e7c3870e1c3870e1c183060c183060c183060c183060b56ad5ab56ad5ab56ad5ab56ad5aaf5ebd7af5ebd7a142850a1428508102040810204076eddbb76eddbb3e7cf9f3e7cf9f366cd9b366cd9b366cd9b366cd9b20408102040810fffffffffffffffffffffffffffffdfbf7efdfbf7ef5ebd7af5ebd7a else 0xe1c3870e1c3870cf9f3e7cf9f3e7c993264c993264c183060c183060c183060c1830603468d1a3468d1a0408102040810200000000000000204081020408100e1c3870e1c3870000000000000000000000000000b56ad5ab56ad5a891224489122448f1e3c78f1e3c78912244891224481020408102040810204081020403e7cf9f3e7cf9f3c78f1e3c78f1e3468d1a3468d1a3468d1a3468d1a0e1c3870e1c38704081020408102000000000000002e5cb972e5cb9720408102040810204081020408100e1c3870e1c387081020408102040000000000000000000000000000))) else (if j < 11 then (if j < 9 then (if j < 8 then 0xb56ad5ab56ad5aaf5ebd7af5ebd7a952a54a952a54a54a952a54a952a142850a142850b56ad5ab56ad5aaf5ebd7af5ebd7a142850a142850a54a952a54a952a142850a142850af5ebd7af5ebd7ab56ad5ab56ad5a952a54a952a54ad5ab56ad5ab56a952a54a952a54a54a952a54a952a142850a142850a54a952a54a952a142850a142850a142850a1428508f1e3c78f1e3c78b162c58b162c5810204081020403468d1a3468d1a3468d1a3468d1a2e5cb972e5cb97204081020408100000000000000000000000000000f5ebd7af5ebd7ac58b162c58b162c183060c183060 else 0x5ebd7af5ebd7af3e7cf9f3e7cf9f1e3c78f1e3c78f0a142850a14285f5ebd7af5ebd7ae1c3870e1c3870efdfbf7efdfbf7e9d3a74e9d3a74e5cb972e5cb972e1c3870e1c3870e1c3870e1c3870e1c3870e1c3870c183060c183060c183060c183060b56ad5ab56ad5aa142850a142850a142850a142850af5ebd7af5ebd7a952a54a952a54a142850a142850a142850a142850fffffffffffffff7efdfbf7efdfbf5ebd7af5ebd7af1e3c78f1e3c78e1c3870e1c3870bf7efdfbf7efdfbd7af5ebd7af5eb56ad5ab56ad5ab56ad5ab56ad5ab162c58b162c58a142850a142850) else (if j < 10 then 0x81020408102043c78f1e3c78f1e08102040810204fffffffffffffffffffffffffffff1e3c78f1e3c78cb972e5cb972e53e7cf9f3e7cf9f3e7cf9f3e7cf9fffffffffffffffdfbf7efdfbf7efc993264c993264cb972e5cb972e57efdfbf7efdfbf74e9d3a74e9d3a5ebd7af5ebd7af5ebd7af5ebd7af5ab56ad5ab56ad5ebd7af5ebd7af56ad5ab56ad5ab50a142850a14285ebd7af5ebd7af5ebd7af5ebd7af4a952a54a952a5408102040810203e7cf9f3e7cf9f3c78f1e3c78f1e0e1c3870e1c3870e1c3870e1c3870810204081020400000000000000 else 0x3c78f1e3c78f1e3870e1c3870e1c3060c183060c183468d1a3468d1a3060c183060c182850a142850a142e5cb972e5cb972850a142850a142c58b162c58b162850a142850a140e1c3870e1c387081020408102040c183060c1830608102040810204000000000000001e3c78f1e3c78f0e1c3870e1c3870a142850a14285081020408102040e1c3870e1c3870c183060c18306081020408102040e1c3870e1c3870c183060c183060a142850a14285081020408102040e1c3870e1c3870c183060c183060a142850a14285081020408102040000000000000000000000000000)) else (if j < 13 then (if j < 12 then 0x3e7cf9f3e7cf9f0e1c3870e1c3870a142850a1428500000000000000fffffffffffffffdfbf7efdfbf7ee9d3a74e9d3a74dfbf7efdfbf7efcf9f3e7cf9f3e7cd9b366cd9b366c993264c993264cd9b366cd9b366c993264c993264c183060c183060c183060c183060c183060c183060c993264c993264bd7af5ebd7af5ea952a54a952a54891224489122448f1e3c78f1e3c78912244891224489122448912244891224489122447efdfbf7efdfbf5ebd7af5ebd7af4a952a54a952a53e7cf9f3e7cf9f3c78f1e3c78f1e3e7cf9f3e7cf9f3c78f1e3c78f1e3e7cf9f3e7cf9f else 0xa952a54a952a54891224489122447efdfbf7efdfbf7efdfbf7efdfbf70e1c3870e1c384a952a54a952a53e7cf9f3e7cf9f3e7cf9f3e7cf9f2850a142850a140e1c3870e1c3870a142850a14285fffffffffffffff1e3c78f1e3c78f1e3c78f1e3c78ffffffffffffffcb972e5cb972e5bf7efdfbf7efdfb162c58b162c58a952a54a952a543e7cf9f3e7cf9f3e7cf9f3e7cf9f3468d1a3468d1a3e7cf9f3e7cf9f3e7cf9f3e7cf9f3a74e9d3a74e9d3e7cf9f3e7cf9f3a74e9d3a74e9d366cd9b366cd9b366cd9b366cd9b3060c183060c182850a142850a141e3c78f1e3c78f) else (if j < 14 then 0xd1a3468d1a3468dfbf7efdfbf7efcf9f3e7cf9f3e7cb972e5cb972e5c993264c993264c993264c993264c183060c183060fffffffffffffff1e3c78f1e3c78f1e3c78f1e3c78ebd7af5ebd7af5e1c3870e1c3870cb972e5cb972e5c183060c183060cf9f3e7cf9f3e7cb972e5cb972e5c993264c993264cb972e5cb972e5cb972e5cb972e5c3870e1c3870e1c183060c183060c183060c183060bd7af5ebd7af5ea952a54a952a54af5ebd7af5ebd7a952a54a952a54ad5ab56ad5ab56a952a54a952a54a952a54a952a54a142850a142850a142850a14285089122448912244 else 0xfdfbf7efdfbf7efbf7efdfbf7efdfffffffffffffff9f3e7cf9f3e7cfffffffffffffffbf7efdfbf7efdfffffffffffffff9f3e7cf9f3e7cf7efdfbf7efdfbf1e3c78f1e3c78f7efdfbf7efdfbf5ebd7af5ebd7af1e3c78f1e3c78f7efdfbf7efdfbf1e3c78f1e3c78f5ebd7af5ebd7af1e3c78f1e3c78e9d3a74e9d3a74e1c3870e1c3870fffffffffffffffffffffffffffff1e3c78f1e3c78f1e3c78f1e3c78dfbf7efdfbf7efdfbf7efdfbf7ef)))) else 0


def wireAt (i : Nat) : Nat := fld (dictB (i / 32)) 21 (i % 32)

def p1At (i : Nat) : Nat := fld (dictP1B (i / 32)) 56 (i % 32)

def p2At (i : Nat) : Nat := fld (dictP2B (i / 32)) 56 (i % 32)

def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 473 then (wireAt i, p1At i, p2At i) else (0, 0, 0)

def wireSAt (i : Nat) : Nat := if i < 473 then wireAt i else 0

def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in

theorem wireD_ok_all : span wireDOK 473 0 = true := by decide +kernel

theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := wireSAt i; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt wireSAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) hi
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]

def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 9 0) :: stateWiresD n (ids >>> 9)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 9 0) :: stateWiresS n (ids >>> 9)
def SD (s j : Nat) : List (Nat × Nat × Nat) :=
  let packed := fld (stateB s (j / 32)) (stateW s) (j % 32)
  stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 32)) (stateW s) (j % 32)
  stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) : SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _
def htAt (s i : Nat) : Nat := fld (HT s (i / 32)) 32 (i % 32)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 17 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk seed zs)
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dm goalM u ys) : RunD dm goalM u (ori ys) := h
def cutHitH (s _ : Nat) (ws : List Nat) : Bool := unateBad dm pairsG s ws
theorem cutHitH_sound {u ys} (h : cutHitH u (hk seed ys) ys = true) : ¬ RunD dm goalM u ys :=
  unateBad_no (d := dm) (y := goalM) (pairs := pairsG) (s := u) (ws := ys)
    (by decide +kernel) (by decide +kernel) h
def Z (s : Nat) := barFast dm goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori seed [] cutHitH s


end SmallCert
end PEqualNP.Outside.L_meta_25385_aux

namespace PEqualNP.Outside.L_meta_25385_aux.SmallCert

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_4_0 : ∀ i, 0 ≤ i → i < 8 → Z 4 i = true :=
  span_ok (by decide +kernel : span (Z 4) 8 0 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_4_32 : ∀ i, 32 ≤ i → i < 40 → Z 4 i = true :=
  span_ok (by decide +kernel : span (Z 4) 8 32 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_4_64 : ∀ i, 64 ≤ i → i < 72 → Z 4 i = true :=
  span_ok (by decide +kernel : span (Z 4) 8 64 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_24 : ∀ i, 24 ≤ i → i < 32 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 24 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_56 : ∀ i, 56 ≤ i → i < 64 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 56 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_88 : ∀ i, 88 ≤ i → i < 96 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 88 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_120 : ∀ i, 120 ≤ i → i < 128 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 120 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_152 : ∀ i, 152 ≤ i → i < 160 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 152 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_184 : ∀ i, 184 ≤ i → i < 192 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 184 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_216 : ∀ i, 216 ≤ i → i < 224 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 216 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_248 : ∀ i, 248 ≤ i → i < 256 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 248 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_280 : ∀ i, 280 ≤ i → i < 288 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 280 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_312 : ∀ i, 312 ≤ i → i < 320 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 312 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_344 : ∀ i, 344 ≤ i → i < 352 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 344 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_376 : ∀ i, 376 ≤ i → i < 384 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 376 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_408 : ∀ i, 408 ≤ i → i < 416 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 408 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_440 : ∀ i, 440 ≤ i → i < 448 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 440 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_472 : ∀ i, 472 ≤ i → i < 480 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 472 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_504 : ∀ i, 504 ≤ i → i < 512 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 504 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_536 : ∀ i, 536 ≤ i → i < 544 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 536 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_568 : ∀ i, 568 ≤ i → i < 576 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 568 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_600 : ∀ i, 600 ≤ i → i < 608 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 600 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_632 : ∀ i, 632 ≤ i → i < 640 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 632 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_664 : ∀ i, 664 ≤ i → i < 672 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 664 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_696 : ∀ i, 696 ≤ i → i < 704 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 696 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_728 : ∀ i, 728 ≤ i → i < 736 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 728 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_760 : ∀ i, 760 ≤ i → i < 768 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 760 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_792 : ∀ i, 792 ≤ i → i < 800 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 792 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_824 : ∀ i, 824 ≤ i → i < 832 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 824 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_856 : ∀ i, 856 ≤ i → i < 864 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 856 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_888 : ∀ i, 888 ≤ i → i < 896 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 888 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_920 : ∀ i, 920 ≤ i → i < 928 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 920 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_16 : ∀ i, 16 ≤ i → i < 24 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 16 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_48 : ∀ i, 48 ≤ i → i < 56 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 48 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_80 : ∀ i, 80 ≤ i → i < 88 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 80 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_112 : ∀ i, 112 ≤ i → i < 120 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 112 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_144 : ∀ i, 144 ≤ i → i < 152 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 144 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_176 : ∀ i, 176 ≤ i → i < 184 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 176 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_208 : ∀ i, 208 ≤ i → i < 216 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 208 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_240 : ∀ i, 240 ≤ i → i < 248 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 240 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_272 : ∀ i, 272 ≤ i → i < 280 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 272 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_304 : ∀ i, 304 ≤ i → i < 312 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 304 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_336 : ∀ i, 336 ≤ i → i < 344 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 336 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_368 : ∀ i, 368 ≤ i → i < 376 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 368 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_400 : ∀ i, 400 ≤ i → i < 408 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 400 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_432 : ∀ i, 432 ≤ i → i < 440 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 432 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_464 : ∀ i, 464 ≤ i → i < 472 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 464 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_496 : ∀ i, 496 ≤ i → i < 504 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 496 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_528 : ∀ i, 528 ≤ i → i < 536 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 528 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_560 : ∀ i, 560 ≤ i → i < 568 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 560 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_592 : ∀ i, 592 ≤ i → i < 600 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 592 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_624 : ∀ i, 624 ≤ i → i < 632 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 624 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_656 : ∀ i, 656 ≤ i → i < 664 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 656 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_688 : ∀ i, 688 ≤ i → i < 696 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 688 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_720 : ∀ i, 720 ≤ i → i < 728 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 720 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_752 : ∀ i, 752 ≤ i → i < 760 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 752 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_784 : ∀ i, 784 ≤ i → i < 792 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 784 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_816 : ∀ i, 816 ≤ i → i < 824 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 816 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_848 : ∀ i, 848 ≤ i → i < 856 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 848 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_880 : ∀ i, 880 ≤ i → i < 888 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 880 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_912 : ∀ i, 912 ≤ i → i < 920 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 912 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_944 : ∀ i, 944 ≤ i → i < 952 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 944 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_976 : ∀ i, 976 ≤ i → i < 984 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 976 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1008 : ∀ i, 1008 ≤ i → i < 1016 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1008 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1040 : ∀ i, 1040 ≤ i → i < 1048 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1040 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1072 : ∀ i, 1072 ≤ i → i < 1080 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1072 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1104 : ∀ i, 1104 ≤ i → i < 1112 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1104 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1136 : ∀ i, 1136 ≤ i → i < 1144 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1136 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1168 : ∀ i, 1168 ≤ i → i < 1176 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1168 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1200 : ∀ i, 1200 ≤ i → i < 1208 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1200 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1232 : ∀ i, 1232 ≤ i → i < 1240 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1232 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1264 : ∀ i, 1264 ≤ i → i < 1272 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1264 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1296 : ∀ i, 1296 ≤ i → i < 1304 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1296 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1328 : ∀ i, 1328 ≤ i → i < 1336 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1328 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1360 : ∀ i, 1360 ≤ i → i < 1368 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1360 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1392 : ∀ i, 1392 ≤ i → i < 1400 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1392 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1424 : ∀ i, 1424 ≤ i → i < 1432 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1424 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1456 : ∀ i, 1456 ≤ i → i < 1464 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1456 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1488 : ∀ i, 1488 ≤ i → i < 1496 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1488 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1520 : ∀ i, 1520 ≤ i → i < 1528 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1520 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1552 : ∀ i, 1552 ≤ i → i < 1560 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1552 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1584 : ∀ i, 1584 ≤ i → i < 1592 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1584 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1616 : ∀ i, 1616 ≤ i → i < 1624 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1616 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1648 : ∀ i, 1648 ≤ i → i < 1656 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1648 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1680 : ∀ i, 1680 ≤ i → i < 1688 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1680 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1712 : ∀ i, 1712 ≤ i → i < 1720 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1712 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1744 : ∀ i, 1744 ≤ i → i < 1752 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1744 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1776 : ∀ i, 1776 ≤ i → i < 1784 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1776 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1808 : ∀ i, 1808 ≤ i → i < 1816 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1808 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1840 : ∀ i, 1840 ≤ i → i < 1848 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1840 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1872 : ∀ i, 1872 ≤ i → i < 1880 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1872 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1904 : ∀ i, 1904 ≤ i → i < 1912 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1904 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1936 : ∀ i, 1936 ≤ i → i < 1944 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1936 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1968 : ∀ i, 1968 ≤ i → i < 1976 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1968 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2000 : ∀ i, 2000 ≤ i → i < 2008 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2000 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2032 : ∀ i, 2032 ≤ i → i < 2040 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2032 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2064 : ∀ i, 2064 ≤ i → i < 2072 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2064 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2096 : ∀ i, 2096 ≤ i → i < 2104 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2096 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2128 : ∀ i, 2128 ≤ i → i < 2136 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2128 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2160 : ∀ i, 2160 ≤ i → i < 2168 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2160 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2192 : ∀ i, 2192 ≤ i → i < 2200 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2192 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2224 : ∀ i, 2224 ≤ i → i < 2232 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2224 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2256 : ∀ i, 2256 ≤ i → i < 2264 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2256 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2288 : ∀ i, 2288 ≤ i → i < 2296 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2288 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2320 : ∀ i, 2320 ≤ i → i < 2328 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2320 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2352 : ∀ i, 2352 ≤ i → i < 2360 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2352 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2384 : ∀ i, 2384 ≤ i → i < 2392 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2384 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2416 : ∀ i, 2416 ≤ i → i < 2424 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2416 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2448 : ∀ i, 2448 ≤ i → i < 2456 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2448 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2480 : ∀ i, 2480 ≤ i → i < 2488 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2480 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2512 : ∀ i, 2512 ≤ i → i < 2520 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2512 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2544 : ∀ i, 2544 ≤ i → i < 2552 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2544 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2576 : ∀ i, 2576 ≤ i → i < 2584 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2576 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2608 : ∀ i, 2608 ≤ i → i < 2616 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2608 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2640 : ∀ i, 2640 ≤ i → i < 2648 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2640 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2672 : ∀ i, 2672 ≤ i → i < 2680 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2672 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2704 : ∀ i, 2704 ≤ i → i < 2709 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 5 2704 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_8 : ∀ i, 8 ≤ i → i < 16 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 8 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_40 : ∀ i, 40 ≤ i → i < 48 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 40 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_72 : ∀ i, 72 ≤ i → i < 80 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 72 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_104 : ∀ i, 104 ≤ i → i < 112 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 104 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_136 : ∀ i, 136 ≤ i → i < 144 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 136 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_168 : ∀ i, 168 ≤ i → i < 176 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 168 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_200 : ∀ i, 200 ≤ i → i < 208 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 200 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_232 : ∀ i, 232 ≤ i → i < 240 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 232 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_264 : ∀ i, 264 ≤ i → i < 272 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 264 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_296 : ∀ i, 296 ≤ i → i < 304 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 296 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_328 : ∀ i, 328 ≤ i → i < 336 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 328 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_360 : ∀ i, 360 ≤ i → i < 368 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 360 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_392 : ∀ i, 392 ≤ i → i < 400 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 392 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_424 : ∀ i, 424 ≤ i → i < 432 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 424 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_456 : ∀ i, 456 ≤ i → i < 464 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 456 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_488 : ∀ i, 488 ≤ i → i < 496 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 488 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_520 : ∀ i, 520 ≤ i → i < 528 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 520 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_552 : ∀ i, 552 ≤ i → i < 560 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 552 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_584 : ∀ i, 584 ≤ i → i < 592 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 584 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_616 : ∀ i, 616 ≤ i → i < 624 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 616 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_648 : ∀ i, 648 ≤ i → i < 656 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 648 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_680 : ∀ i, 680 ≤ i → i < 688 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 680 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_712 : ∀ i, 712 ≤ i → i < 720 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 712 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_744 : ∀ i, 744 ≤ i → i < 752 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 744 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_776 : ∀ i, 776 ≤ i → i < 784 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 776 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_808 : ∀ i, 808 ≤ i → i < 816 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 808 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_840 : ∀ i, 840 ≤ i → i < 848 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 840 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_872 : ∀ i, 872 ≤ i → i < 880 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 872 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_904 : ∀ i, 904 ≤ i → i < 912 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 904 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_936 : ∀ i, 936 ≤ i → i < 944 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 936 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_8_0 : ∀ i, 0 ≤ i → i < 8 → Z 8 i = true :=
  span_ok (by decide +kernel : span (Z 8) 8 0 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_8_32 : ∀ i, 32 ≤ i → i < 40 → Z 8 i = true :=
  span_ok (by decide +kernel : span (Z 8) 8 32 = true)

end PEqualNP.Outside.L_meta_25385_aux.SmallCert

namespace PEqualNP.Outside.L_meta_25385_aux.SmallCert

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_4_8 : ∀ i, 8 ≤ i → i < 16 → Z 4 i = true :=
  span_ok (by decide +kernel : span (Z 4) 8 8 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_4_40 : ∀ i, 40 ≤ i → i < 48 → Z 4 i = true :=
  span_ok (by decide +kernel : span (Z 4) 8 40 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_4_72 : ∀ i, 72 ≤ i → i < 80 → Z 4 i = true :=
  span_ok (by decide +kernel : span (Z 4) 8 72 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_0 : ∀ i, 0 ≤ i → i < 8 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 0 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_32 : ∀ i, 32 ≤ i → i < 40 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 32 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_64 : ∀ i, 64 ≤ i → i < 72 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 64 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_96 : ∀ i, 96 ≤ i → i < 104 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 96 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_128 : ∀ i, 128 ≤ i → i < 136 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 128 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_160 : ∀ i, 160 ≤ i → i < 168 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 160 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_192 : ∀ i, 192 ≤ i → i < 200 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 192 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_224 : ∀ i, 224 ≤ i → i < 232 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 224 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_256 : ∀ i, 256 ≤ i → i < 264 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 256 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_288 : ∀ i, 288 ≤ i → i < 296 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 288 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_320 : ∀ i, 320 ≤ i → i < 328 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 320 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_352 : ∀ i, 352 ≤ i → i < 360 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 352 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_384 : ∀ i, 384 ≤ i → i < 392 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 384 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_416 : ∀ i, 416 ≤ i → i < 424 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 416 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_448 : ∀ i, 448 ≤ i → i < 456 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 448 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_480 : ∀ i, 480 ≤ i → i < 488 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 480 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_512 : ∀ i, 512 ≤ i → i < 520 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 512 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_544 : ∀ i, 544 ≤ i → i < 552 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 544 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_576 : ∀ i, 576 ≤ i → i < 584 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 576 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_608 : ∀ i, 608 ≤ i → i < 616 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 608 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_640 : ∀ i, 640 ≤ i → i < 648 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 640 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_672 : ∀ i, 672 ≤ i → i < 680 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 672 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_704 : ∀ i, 704 ≤ i → i < 712 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 704 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_736 : ∀ i, 736 ≤ i → i < 744 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 736 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_768 : ∀ i, 768 ≤ i → i < 776 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 768 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_800 : ∀ i, 800 ≤ i → i < 808 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 800 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_832 : ∀ i, 832 ≤ i → i < 840 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 832 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_864 : ∀ i, 864 ≤ i → i < 872 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 864 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_896 : ∀ i, 896 ≤ i → i < 904 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 896 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_928 : ∀ i, 928 ≤ i → i < 936 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 928 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_24 : ∀ i, 24 ≤ i → i < 32 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 24 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_56 : ∀ i, 56 ≤ i → i < 64 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 56 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_88 : ∀ i, 88 ≤ i → i < 96 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 88 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_120 : ∀ i, 120 ≤ i → i < 128 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 120 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_152 : ∀ i, 152 ≤ i → i < 160 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 152 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_184 : ∀ i, 184 ≤ i → i < 192 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 184 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_216 : ∀ i, 216 ≤ i → i < 224 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 216 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_248 : ∀ i, 248 ≤ i → i < 256 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 248 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_280 : ∀ i, 280 ≤ i → i < 288 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 280 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_312 : ∀ i, 312 ≤ i → i < 320 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 312 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_344 : ∀ i, 344 ≤ i → i < 352 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 344 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_376 : ∀ i, 376 ≤ i → i < 384 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 376 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_408 : ∀ i, 408 ≤ i → i < 416 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 408 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_440 : ∀ i, 440 ≤ i → i < 448 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 440 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_472 : ∀ i, 472 ≤ i → i < 480 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 472 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_504 : ∀ i, 504 ≤ i → i < 512 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 504 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_536 : ∀ i, 536 ≤ i → i < 544 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 536 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_568 : ∀ i, 568 ≤ i → i < 576 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 568 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_600 : ∀ i, 600 ≤ i → i < 608 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 600 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_632 : ∀ i, 632 ≤ i → i < 640 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 632 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_664 : ∀ i, 664 ≤ i → i < 672 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 664 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_696 : ∀ i, 696 ≤ i → i < 704 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 696 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_728 : ∀ i, 728 ≤ i → i < 736 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 728 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_760 : ∀ i, 760 ≤ i → i < 768 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 760 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_792 : ∀ i, 792 ≤ i → i < 800 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 792 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_824 : ∀ i, 824 ≤ i → i < 832 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 824 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_856 : ∀ i, 856 ≤ i → i < 864 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 856 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_888 : ∀ i, 888 ≤ i → i < 896 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 888 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_920 : ∀ i, 920 ≤ i → i < 928 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 920 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_952 : ∀ i, 952 ≤ i → i < 960 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 952 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_984 : ∀ i, 984 ≤ i → i < 992 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 984 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1016 : ∀ i, 1016 ≤ i → i < 1024 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1016 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1048 : ∀ i, 1048 ≤ i → i < 1056 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1048 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1080 : ∀ i, 1080 ≤ i → i < 1088 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1080 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1112 : ∀ i, 1112 ≤ i → i < 1120 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1112 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1144 : ∀ i, 1144 ≤ i → i < 1152 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1144 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1176 : ∀ i, 1176 ≤ i → i < 1184 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1176 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1208 : ∀ i, 1208 ≤ i → i < 1216 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1208 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1240 : ∀ i, 1240 ≤ i → i < 1248 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1240 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1272 : ∀ i, 1272 ≤ i → i < 1280 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1272 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1304 : ∀ i, 1304 ≤ i → i < 1312 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1304 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1336 : ∀ i, 1336 ≤ i → i < 1344 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1336 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1368 : ∀ i, 1368 ≤ i → i < 1376 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1368 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1400 : ∀ i, 1400 ≤ i → i < 1408 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1400 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1432 : ∀ i, 1432 ≤ i → i < 1440 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1432 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1464 : ∀ i, 1464 ≤ i → i < 1472 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1464 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1496 : ∀ i, 1496 ≤ i → i < 1504 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1496 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1528 : ∀ i, 1528 ≤ i → i < 1536 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1528 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1560 : ∀ i, 1560 ≤ i → i < 1568 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1560 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1592 : ∀ i, 1592 ≤ i → i < 1600 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1592 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1624 : ∀ i, 1624 ≤ i → i < 1632 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1624 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1656 : ∀ i, 1656 ≤ i → i < 1664 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1656 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1688 : ∀ i, 1688 ≤ i → i < 1696 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1688 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1720 : ∀ i, 1720 ≤ i → i < 1728 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1720 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1752 : ∀ i, 1752 ≤ i → i < 1760 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1752 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1784 : ∀ i, 1784 ≤ i → i < 1792 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1784 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1816 : ∀ i, 1816 ≤ i → i < 1824 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1816 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1848 : ∀ i, 1848 ≤ i → i < 1856 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1848 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1880 : ∀ i, 1880 ≤ i → i < 1888 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1880 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1912 : ∀ i, 1912 ≤ i → i < 1920 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1912 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1944 : ∀ i, 1944 ≤ i → i < 1952 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1944 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1976 : ∀ i, 1976 ≤ i → i < 1984 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1976 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2008 : ∀ i, 2008 ≤ i → i < 2016 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2008 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2040 : ∀ i, 2040 ≤ i → i < 2048 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2040 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2072 : ∀ i, 2072 ≤ i → i < 2080 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2072 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2104 : ∀ i, 2104 ≤ i → i < 2112 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2104 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2136 : ∀ i, 2136 ≤ i → i < 2144 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2136 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2168 : ∀ i, 2168 ≤ i → i < 2176 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2168 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2200 : ∀ i, 2200 ≤ i → i < 2208 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2200 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2232 : ∀ i, 2232 ≤ i → i < 2240 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2232 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2264 : ∀ i, 2264 ≤ i → i < 2272 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2264 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2296 : ∀ i, 2296 ≤ i → i < 2304 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2296 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2328 : ∀ i, 2328 ≤ i → i < 2336 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2328 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2360 : ∀ i, 2360 ≤ i → i < 2368 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2360 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2392 : ∀ i, 2392 ≤ i → i < 2400 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2392 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2424 : ∀ i, 2424 ≤ i → i < 2432 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2424 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2456 : ∀ i, 2456 ≤ i → i < 2464 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2456 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2488 : ∀ i, 2488 ≤ i → i < 2496 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2488 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2520 : ∀ i, 2520 ≤ i → i < 2528 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2520 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2552 : ∀ i, 2552 ≤ i → i < 2560 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2552 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2584 : ∀ i, 2584 ≤ i → i < 2592 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2584 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2616 : ∀ i, 2616 ≤ i → i < 2624 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2616 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2648 : ∀ i, 2648 ≤ i → i < 2656 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2648 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2680 : ∀ i, 2680 ≤ i → i < 2688 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2680 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_16 : ∀ i, 16 ≤ i → i < 24 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 16 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_48 : ∀ i, 48 ≤ i → i < 56 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 48 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_80 : ∀ i, 80 ≤ i → i < 88 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 80 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_112 : ∀ i, 112 ≤ i → i < 120 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 112 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_144 : ∀ i, 144 ≤ i → i < 152 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 144 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_176 : ∀ i, 176 ≤ i → i < 184 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 176 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_208 : ∀ i, 208 ≤ i → i < 216 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 208 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_240 : ∀ i, 240 ≤ i → i < 248 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 240 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_272 : ∀ i, 272 ≤ i → i < 280 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 272 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_304 : ∀ i, 304 ≤ i → i < 312 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 304 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_336 : ∀ i, 336 ≤ i → i < 344 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 336 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_368 : ∀ i, 368 ≤ i → i < 376 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 368 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_400 : ∀ i, 400 ≤ i → i < 408 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 400 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_432 : ∀ i, 432 ≤ i → i < 440 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 432 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_464 : ∀ i, 464 ≤ i → i < 472 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 464 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_496 : ∀ i, 496 ≤ i → i < 504 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 496 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_528 : ∀ i, 528 ≤ i → i < 536 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 528 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_560 : ∀ i, 560 ≤ i → i < 568 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 560 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_592 : ∀ i, 592 ≤ i → i < 600 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 592 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_624 : ∀ i, 624 ≤ i → i < 632 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 624 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_656 : ∀ i, 656 ≤ i → i < 664 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 656 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_688 : ∀ i, 688 ≤ i → i < 696 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 688 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_720 : ∀ i, 720 ≤ i → i < 728 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 720 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_752 : ∀ i, 752 ≤ i → i < 760 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 752 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_784 : ∀ i, 784 ≤ i → i < 792 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 784 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_816 : ∀ i, 816 ≤ i → i < 824 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 816 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_848 : ∀ i, 848 ≤ i → i < 856 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 848 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_880 : ∀ i, 880 ≤ i → i < 888 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 880 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_912 : ∀ i, 912 ≤ i → i < 920 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 912 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_8_8 : ∀ i, 8 ≤ i → i < 16 → Z 8 i = true :=
  span_ok (by decide +kernel : span (Z 8) 8 8 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_8_40 : ∀ i, 40 ≤ i → i < 42 → Z 8 i = true :=
  span_ok (by decide +kernel : span (Z 8) 2 40 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_9_0 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true :=
  span_ok (by decide +kernel : span (Z 9) 1 0 = true)

end PEqualNP.Outside.L_meta_25385_aux.SmallCert

namespace PEqualNP.Outside.L_meta_25385_aux.SmallCert

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_4_16 : ∀ i, 16 ≤ i → i < 24 → Z 4 i = true :=
  span_ok (by decide +kernel : span (Z 4) 8 16 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_4_48 : ∀ i, 48 ≤ i → i < 56 → Z 4 i = true :=
  span_ok (by decide +kernel : span (Z 4) 8 48 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_4_80 : ∀ i, 80 ≤ i → i < 88 → Z 4 i = true :=
  span_ok (by decide +kernel : span (Z 4) 8 80 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_8 : ∀ i, 8 ≤ i → i < 16 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 8 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_40 : ∀ i, 40 ≤ i → i < 48 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 40 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_72 : ∀ i, 72 ≤ i → i < 80 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 72 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_104 : ∀ i, 104 ≤ i → i < 112 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 104 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_136 : ∀ i, 136 ≤ i → i < 144 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 136 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_168 : ∀ i, 168 ≤ i → i < 176 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 168 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_200 : ∀ i, 200 ≤ i → i < 208 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 200 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_232 : ∀ i, 232 ≤ i → i < 240 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 232 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_264 : ∀ i, 264 ≤ i → i < 272 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 264 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_296 : ∀ i, 296 ≤ i → i < 304 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 296 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_328 : ∀ i, 328 ≤ i → i < 336 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 328 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_360 : ∀ i, 360 ≤ i → i < 368 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 360 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_392 : ∀ i, 392 ≤ i → i < 400 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 392 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_424 : ∀ i, 424 ≤ i → i < 432 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 424 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_456 : ∀ i, 456 ≤ i → i < 464 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 456 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_488 : ∀ i, 488 ≤ i → i < 496 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 488 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_520 : ∀ i, 520 ≤ i → i < 528 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 520 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_552 : ∀ i, 552 ≤ i → i < 560 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 552 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_584 : ∀ i, 584 ≤ i → i < 592 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 584 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_616 : ∀ i, 616 ≤ i → i < 624 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 616 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_648 : ∀ i, 648 ≤ i → i < 656 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 648 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_680 : ∀ i, 680 ≤ i → i < 688 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 680 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_712 : ∀ i, 712 ≤ i → i < 720 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 712 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_744 : ∀ i, 744 ≤ i → i < 752 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 744 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_776 : ∀ i, 776 ≤ i → i < 784 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 776 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_808 : ∀ i, 808 ≤ i → i < 816 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 808 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_840 : ∀ i, 840 ≤ i → i < 848 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 840 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_872 : ∀ i, 872 ≤ i → i < 880 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 872 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_904 : ∀ i, 904 ≤ i → i < 912 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 904 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_936 : ∀ i, 936 ≤ i → i < 944 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 936 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_0 : ∀ i, 0 ≤ i → i < 8 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 0 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_32 : ∀ i, 32 ≤ i → i < 40 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 32 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_64 : ∀ i, 64 ≤ i → i < 72 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 64 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_96 : ∀ i, 96 ≤ i → i < 104 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 96 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_128 : ∀ i, 128 ≤ i → i < 136 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 128 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_160 : ∀ i, 160 ≤ i → i < 168 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 160 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_192 : ∀ i, 192 ≤ i → i < 200 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 192 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_224 : ∀ i, 224 ≤ i → i < 232 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 224 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_256 : ∀ i, 256 ≤ i → i < 264 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 256 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_288 : ∀ i, 288 ≤ i → i < 296 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 288 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_320 : ∀ i, 320 ≤ i → i < 328 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 320 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_352 : ∀ i, 352 ≤ i → i < 360 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 352 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_384 : ∀ i, 384 ≤ i → i < 392 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 384 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_416 : ∀ i, 416 ≤ i → i < 424 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 416 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_448 : ∀ i, 448 ≤ i → i < 456 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 448 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_480 : ∀ i, 480 ≤ i → i < 488 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 480 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_512 : ∀ i, 512 ≤ i → i < 520 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 512 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_544 : ∀ i, 544 ≤ i → i < 552 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 544 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_576 : ∀ i, 576 ≤ i → i < 584 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 576 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_608 : ∀ i, 608 ≤ i → i < 616 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 608 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_640 : ∀ i, 640 ≤ i → i < 648 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 640 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_672 : ∀ i, 672 ≤ i → i < 680 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 672 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_704 : ∀ i, 704 ≤ i → i < 712 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 704 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_736 : ∀ i, 736 ≤ i → i < 744 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 736 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_768 : ∀ i, 768 ≤ i → i < 776 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 768 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_800 : ∀ i, 800 ≤ i → i < 808 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 800 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_832 : ∀ i, 832 ≤ i → i < 840 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 832 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_864 : ∀ i, 864 ≤ i → i < 872 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 864 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_896 : ∀ i, 896 ≤ i → i < 904 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 896 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_928 : ∀ i, 928 ≤ i → i < 936 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 928 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_960 : ∀ i, 960 ≤ i → i < 968 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 960 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_992 : ∀ i, 992 ≤ i → i < 1000 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 992 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1024 : ∀ i, 1024 ≤ i → i < 1032 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1024 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1056 : ∀ i, 1056 ≤ i → i < 1064 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1056 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1088 : ∀ i, 1088 ≤ i → i < 1096 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1088 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1120 : ∀ i, 1120 ≤ i → i < 1128 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1120 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1152 : ∀ i, 1152 ≤ i → i < 1160 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1152 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1184 : ∀ i, 1184 ≤ i → i < 1192 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1184 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1216 : ∀ i, 1216 ≤ i → i < 1224 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1216 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1248 : ∀ i, 1248 ≤ i → i < 1256 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1248 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1280 : ∀ i, 1280 ≤ i → i < 1288 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1280 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1312 : ∀ i, 1312 ≤ i → i < 1320 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1312 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1344 : ∀ i, 1344 ≤ i → i < 1352 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1344 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1376 : ∀ i, 1376 ≤ i → i < 1384 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1376 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1408 : ∀ i, 1408 ≤ i → i < 1416 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1408 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1440 : ∀ i, 1440 ≤ i → i < 1448 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1440 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1472 : ∀ i, 1472 ≤ i → i < 1480 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1472 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1504 : ∀ i, 1504 ≤ i → i < 1512 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1504 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1536 : ∀ i, 1536 ≤ i → i < 1544 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1536 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1568 : ∀ i, 1568 ≤ i → i < 1576 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1568 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1600 : ∀ i, 1600 ≤ i → i < 1608 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1600 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1632 : ∀ i, 1632 ≤ i → i < 1640 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1632 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1664 : ∀ i, 1664 ≤ i → i < 1672 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1664 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1696 : ∀ i, 1696 ≤ i → i < 1704 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1696 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1728 : ∀ i, 1728 ≤ i → i < 1736 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1728 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1760 : ∀ i, 1760 ≤ i → i < 1768 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1760 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1792 : ∀ i, 1792 ≤ i → i < 1800 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1792 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1824 : ∀ i, 1824 ≤ i → i < 1832 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1824 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1856 : ∀ i, 1856 ≤ i → i < 1864 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1856 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1888 : ∀ i, 1888 ≤ i → i < 1896 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1888 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1920 : ∀ i, 1920 ≤ i → i < 1928 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1920 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1952 : ∀ i, 1952 ≤ i → i < 1960 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1952 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1984 : ∀ i, 1984 ≤ i → i < 1992 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1984 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2016 : ∀ i, 2016 ≤ i → i < 2024 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2016 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2048 : ∀ i, 2048 ≤ i → i < 2056 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2048 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2080 : ∀ i, 2080 ≤ i → i < 2088 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2080 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2112 : ∀ i, 2112 ≤ i → i < 2120 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2112 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2144 : ∀ i, 2144 ≤ i → i < 2152 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2144 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2176 : ∀ i, 2176 ≤ i → i < 2184 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2176 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2208 : ∀ i, 2208 ≤ i → i < 2216 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2208 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2240 : ∀ i, 2240 ≤ i → i < 2248 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2240 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2272 : ∀ i, 2272 ≤ i → i < 2280 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2272 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2304 : ∀ i, 2304 ≤ i → i < 2312 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2304 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2336 : ∀ i, 2336 ≤ i → i < 2344 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2336 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2368 : ∀ i, 2368 ≤ i → i < 2376 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2368 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2400 : ∀ i, 2400 ≤ i → i < 2408 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2400 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2432 : ∀ i, 2432 ≤ i → i < 2440 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2432 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2464 : ∀ i, 2464 ≤ i → i < 2472 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2464 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2496 : ∀ i, 2496 ≤ i → i < 2504 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2496 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2528 : ∀ i, 2528 ≤ i → i < 2536 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2528 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2560 : ∀ i, 2560 ≤ i → i < 2568 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2560 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2592 : ∀ i, 2592 ≤ i → i < 2600 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2592 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2624 : ∀ i, 2624 ≤ i → i < 2632 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2624 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2656 : ∀ i, 2656 ≤ i → i < 2664 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2656 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2688 : ∀ i, 2688 ≤ i → i < 2696 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2688 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_24 : ∀ i, 24 ≤ i → i < 32 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 24 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_56 : ∀ i, 56 ≤ i → i < 64 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 56 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_88 : ∀ i, 88 ≤ i → i < 96 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 88 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_120 : ∀ i, 120 ≤ i → i < 128 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 120 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_152 : ∀ i, 152 ≤ i → i < 160 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 152 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_184 : ∀ i, 184 ≤ i → i < 192 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 184 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_216 : ∀ i, 216 ≤ i → i < 224 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 216 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_248 : ∀ i, 248 ≤ i → i < 256 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 248 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_280 : ∀ i, 280 ≤ i → i < 288 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 280 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_312 : ∀ i, 312 ≤ i → i < 320 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 312 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_344 : ∀ i, 344 ≤ i → i < 352 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 344 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_376 : ∀ i, 376 ≤ i → i < 384 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 376 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_408 : ∀ i, 408 ≤ i → i < 416 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 408 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_440 : ∀ i, 440 ≤ i → i < 448 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 440 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_472 : ∀ i, 472 ≤ i → i < 480 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 472 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_504 : ∀ i, 504 ≤ i → i < 512 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 504 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_536 : ∀ i, 536 ≤ i → i < 544 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 536 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_568 : ∀ i, 568 ≤ i → i < 576 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 568 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_600 : ∀ i, 600 ≤ i → i < 608 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 600 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_632 : ∀ i, 632 ≤ i → i < 640 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 632 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_664 : ∀ i, 664 ≤ i → i < 672 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 664 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_696 : ∀ i, 696 ≤ i → i < 704 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 696 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_728 : ∀ i, 728 ≤ i → i < 736 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 728 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_760 : ∀ i, 760 ≤ i → i < 768 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 760 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_792 : ∀ i, 792 ≤ i → i < 800 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 792 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_824 : ∀ i, 824 ≤ i → i < 832 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 824 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_856 : ∀ i, 856 ≤ i → i < 864 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 856 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_888 : ∀ i, 888 ≤ i → i < 896 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 888 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_920 : ∀ i, 920 ≤ i → i < 928 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 920 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_8_16 : ∀ i, 16 ≤ i → i < 24 → Z 8 i = true :=
  span_ok (by decide +kernel : span (Z 8) 8 16 = true)

end PEqualNP.Outside.L_meta_25385_aux.SmallCert

namespace PEqualNP.Outside.L_meta_25385_aux.SmallCert

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_3_0 : ∀ i, 0 ≤ i → i < 6 → Z 3 i = true :=
  span_ok (by decide +kernel : span (Z 3) 6 0 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_4_24 : ∀ i, 24 ≤ i → i < 32 → Z 4 i = true :=
  span_ok (by decide +kernel : span (Z 4) 8 24 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_4_56 : ∀ i, 56 ≤ i → i < 64 → Z 4 i = true :=
  span_ok (by decide +kernel : span (Z 4) 8 56 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_4_88 : ∀ i, 88 ≤ i → i < 95 → Z 4 i = true :=
  span_ok (by decide +kernel : span (Z 4) 7 88 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_16 : ∀ i, 16 ≤ i → i < 24 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 16 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_48 : ∀ i, 48 ≤ i → i < 56 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 48 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_80 : ∀ i, 80 ≤ i → i < 88 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 80 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_112 : ∀ i, 112 ≤ i → i < 120 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 112 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_144 : ∀ i, 144 ≤ i → i < 152 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 144 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_176 : ∀ i, 176 ≤ i → i < 184 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 176 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_208 : ∀ i, 208 ≤ i → i < 216 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 208 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_240 : ∀ i, 240 ≤ i → i < 248 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 240 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_272 : ∀ i, 272 ≤ i → i < 280 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 272 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_304 : ∀ i, 304 ≤ i → i < 312 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 304 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_336 : ∀ i, 336 ≤ i → i < 344 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 336 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_368 : ∀ i, 368 ≤ i → i < 376 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 368 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_400 : ∀ i, 400 ≤ i → i < 408 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 400 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_432 : ∀ i, 432 ≤ i → i < 440 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 432 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_464 : ∀ i, 464 ≤ i → i < 472 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 464 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_496 : ∀ i, 496 ≤ i → i < 504 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 496 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_528 : ∀ i, 528 ≤ i → i < 536 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 528 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_560 : ∀ i, 560 ≤ i → i < 568 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 560 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_592 : ∀ i, 592 ≤ i → i < 600 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 592 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_624 : ∀ i, 624 ≤ i → i < 632 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 624 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_656 : ∀ i, 656 ≤ i → i < 664 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 656 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_688 : ∀ i, 688 ≤ i → i < 696 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 688 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_720 : ∀ i, 720 ≤ i → i < 728 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 720 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_752 : ∀ i, 752 ≤ i → i < 760 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 752 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_784 : ∀ i, 784 ≤ i → i < 792 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 784 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_816 : ∀ i, 816 ≤ i → i < 824 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 816 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_848 : ∀ i, 848 ≤ i → i < 856 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 848 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_880 : ∀ i, 880 ≤ i → i < 888 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 880 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_912 : ∀ i, 912 ≤ i → i < 920 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 8 912 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_5_944 : ∀ i, 944 ≤ i → i < 947 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 3 944 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_8 : ∀ i, 8 ≤ i → i < 16 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 8 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_40 : ∀ i, 40 ≤ i → i < 48 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 40 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_72 : ∀ i, 72 ≤ i → i < 80 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 72 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_104 : ∀ i, 104 ≤ i → i < 112 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 104 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_136 : ∀ i, 136 ≤ i → i < 144 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 136 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_168 : ∀ i, 168 ≤ i → i < 176 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 168 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_200 : ∀ i, 200 ≤ i → i < 208 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 200 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_232 : ∀ i, 232 ≤ i → i < 240 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 232 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_264 : ∀ i, 264 ≤ i → i < 272 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 264 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_296 : ∀ i, 296 ≤ i → i < 304 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 296 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_328 : ∀ i, 328 ≤ i → i < 336 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 328 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_360 : ∀ i, 360 ≤ i → i < 368 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 360 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_392 : ∀ i, 392 ≤ i → i < 400 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 392 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_424 : ∀ i, 424 ≤ i → i < 432 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 424 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_456 : ∀ i, 456 ≤ i → i < 464 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 456 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_488 : ∀ i, 488 ≤ i → i < 496 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 488 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_520 : ∀ i, 520 ≤ i → i < 528 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 520 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_552 : ∀ i, 552 ≤ i → i < 560 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 552 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_584 : ∀ i, 584 ≤ i → i < 592 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 584 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_616 : ∀ i, 616 ≤ i → i < 624 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 616 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_648 : ∀ i, 648 ≤ i → i < 656 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 648 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_680 : ∀ i, 680 ≤ i → i < 688 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 680 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_712 : ∀ i, 712 ≤ i → i < 720 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 712 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_744 : ∀ i, 744 ≤ i → i < 752 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 744 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_776 : ∀ i, 776 ≤ i → i < 784 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 776 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_808 : ∀ i, 808 ≤ i → i < 816 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 808 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_840 : ∀ i, 840 ≤ i → i < 848 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 840 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_872 : ∀ i, 872 ≤ i → i < 880 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 872 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_904 : ∀ i, 904 ≤ i → i < 912 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 904 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_936 : ∀ i, 936 ≤ i → i < 944 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 936 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_968 : ∀ i, 968 ≤ i → i < 976 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 968 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1000 : ∀ i, 1000 ≤ i → i < 1008 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1000 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1032 : ∀ i, 1032 ≤ i → i < 1040 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1032 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1064 : ∀ i, 1064 ≤ i → i < 1072 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1064 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1096 : ∀ i, 1096 ≤ i → i < 1104 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1096 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1128 : ∀ i, 1128 ≤ i → i < 1136 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1128 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1160 : ∀ i, 1160 ≤ i → i < 1168 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1160 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1192 : ∀ i, 1192 ≤ i → i < 1200 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1192 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1224 : ∀ i, 1224 ≤ i → i < 1232 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1224 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1256 : ∀ i, 1256 ≤ i → i < 1264 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1256 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1288 : ∀ i, 1288 ≤ i → i < 1296 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1288 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1320 : ∀ i, 1320 ≤ i → i < 1328 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1320 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1352 : ∀ i, 1352 ≤ i → i < 1360 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1352 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1384 : ∀ i, 1384 ≤ i → i < 1392 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1384 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1416 : ∀ i, 1416 ≤ i → i < 1424 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1416 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1448 : ∀ i, 1448 ≤ i → i < 1456 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1448 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1480 : ∀ i, 1480 ≤ i → i < 1488 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1480 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1512 : ∀ i, 1512 ≤ i → i < 1520 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1512 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1544 : ∀ i, 1544 ≤ i → i < 1552 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1544 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1576 : ∀ i, 1576 ≤ i → i < 1584 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1576 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1608 : ∀ i, 1608 ≤ i → i < 1616 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1608 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1640 : ∀ i, 1640 ≤ i → i < 1648 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1640 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1672 : ∀ i, 1672 ≤ i → i < 1680 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1672 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1704 : ∀ i, 1704 ≤ i → i < 1712 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1704 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1736 : ∀ i, 1736 ≤ i → i < 1744 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1736 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1768 : ∀ i, 1768 ≤ i → i < 1776 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1768 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1800 : ∀ i, 1800 ≤ i → i < 1808 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1800 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1832 : ∀ i, 1832 ≤ i → i < 1840 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1832 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1864 : ∀ i, 1864 ≤ i → i < 1872 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1864 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1896 : ∀ i, 1896 ≤ i → i < 1904 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1896 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1928 : ∀ i, 1928 ≤ i → i < 1936 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1928 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1960 : ∀ i, 1960 ≤ i → i < 1968 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1960 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_1992 : ∀ i, 1992 ≤ i → i < 2000 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 1992 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2024 : ∀ i, 2024 ≤ i → i < 2032 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2024 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2056 : ∀ i, 2056 ≤ i → i < 2064 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2056 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2088 : ∀ i, 2088 ≤ i → i < 2096 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2088 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2120 : ∀ i, 2120 ≤ i → i < 2128 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2120 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2152 : ∀ i, 2152 ≤ i → i < 2160 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2152 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2184 : ∀ i, 2184 ≤ i → i < 2192 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2184 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2216 : ∀ i, 2216 ≤ i → i < 2224 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2216 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2248 : ∀ i, 2248 ≤ i → i < 2256 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2248 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2280 : ∀ i, 2280 ≤ i → i < 2288 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2280 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2312 : ∀ i, 2312 ≤ i → i < 2320 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2312 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2344 : ∀ i, 2344 ≤ i → i < 2352 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2344 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2376 : ∀ i, 2376 ≤ i → i < 2384 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2376 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2408 : ∀ i, 2408 ≤ i → i < 2416 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2408 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2440 : ∀ i, 2440 ≤ i → i < 2448 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2440 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2472 : ∀ i, 2472 ≤ i → i < 2480 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2472 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2504 : ∀ i, 2504 ≤ i → i < 2512 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2504 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2536 : ∀ i, 2536 ≤ i → i < 2544 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2536 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2568 : ∀ i, 2568 ≤ i → i < 2576 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2568 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2600 : ∀ i, 2600 ≤ i → i < 2608 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2600 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2632 : ∀ i, 2632 ≤ i → i < 2640 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2632 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2664 : ∀ i, 2664 ≤ i → i < 2672 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2664 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_6_2696 : ∀ i, 2696 ≤ i → i < 2704 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 2696 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_0 : ∀ i, 0 ≤ i → i < 8 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 0 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_32 : ∀ i, 32 ≤ i → i < 40 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 32 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_64 : ∀ i, 64 ≤ i → i < 72 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 64 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_96 : ∀ i, 96 ≤ i → i < 104 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 96 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_128 : ∀ i, 128 ≤ i → i < 136 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 128 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_160 : ∀ i, 160 ≤ i → i < 168 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 160 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_192 : ∀ i, 192 ≤ i → i < 200 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 192 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_224 : ∀ i, 224 ≤ i → i < 232 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 224 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_256 : ∀ i, 256 ≤ i → i < 264 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 256 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_288 : ∀ i, 288 ≤ i → i < 296 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 288 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_320 : ∀ i, 320 ≤ i → i < 328 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 320 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_352 : ∀ i, 352 ≤ i → i < 360 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 352 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_384 : ∀ i, 384 ≤ i → i < 392 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 384 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_416 : ∀ i, 416 ≤ i → i < 424 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 416 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_448 : ∀ i, 448 ≤ i → i < 456 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 448 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_480 : ∀ i, 480 ≤ i → i < 488 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 480 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_512 : ∀ i, 512 ≤ i → i < 520 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 512 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_544 : ∀ i, 544 ≤ i → i < 552 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 544 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_576 : ∀ i, 576 ≤ i → i < 584 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 576 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_608 : ∀ i, 608 ≤ i → i < 616 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 608 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_640 : ∀ i, 640 ≤ i → i < 648 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 640 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_672 : ∀ i, 672 ≤ i → i < 680 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 672 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_704 : ∀ i, 704 ≤ i → i < 712 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 704 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_736 : ∀ i, 736 ≤ i → i < 744 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 736 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_768 : ∀ i, 768 ≤ i → i < 776 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 768 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_800 : ∀ i, 800 ≤ i → i < 808 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 800 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_832 : ∀ i, 832 ≤ i → i < 840 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 832 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_864 : ∀ i, 864 ≤ i → i < 872 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 864 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_896 : ∀ i, 896 ≤ i → i < 904 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 896 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_7_928 : ∀ i, 928 ≤ i → i < 936 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 8 928 = true)

set_option maxRecDepth 40000 in

set_option maxHeartbeats 0 in

theorem checked_8_24 : ∀ i, 24 ≤ i → i < 32 → Z 8 i = true :=
  span_ok (by decide +kernel : span (Z 8) 8 24 = true)

end PEqualNP.Outside.L_meta_25385_aux.SmallCert

namespace PEqualNP.Outside.L_meta_25385_aux.SmallCert

theorem checked_budget_3 : ∀ i, 0 ≤ i → i < 6 → Z 3 i = true :=
  checked_3_0

theorem checked_budget_4 : ∀ i, 0 ≤ i → i < 95 → Z 4 i = true :=
  (range_split (range_split (range_split checked_4_0 (range_split checked_4_8 checked_4_16)) (range_split checked_4_24 (range_split checked_4_32 checked_4_40))) (range_split (range_split checked_4_48 (range_split checked_4_56 checked_4_64)) (range_split checked_4_72 (range_split checked_4_80 checked_4_88))))

theorem checked_budget_5 : ∀ i, 0 ≤ i → i < 947 → Z 5 i = true :=
  (range_split (range_split (range_split (range_split (range_split (range_split checked_5_0 (range_split checked_5_8 checked_5_16)) (range_split (range_split checked_5_24 checked_5_32) (range_split checked_5_40 checked_5_48))) (range_split (range_split checked_5_56 (range_split checked_5_64 checked_5_72)) (range_split (range_split checked_5_80 checked_5_88) (range_split checked_5_96 checked_5_104)))) (range_split (range_split (range_split checked_5_112 (range_split checked_5_120 checked_5_128)) (range_split (range_split checked_5_136 checked_5_144) (range_split checked_5_152 checked_5_160))) (range_split (range_split (range_split checked_5_168 checked_5_176) (range_split checked_5_184 checked_5_192)) (range_split (range_split checked_5_200 checked_5_208) (range_split checked_5_216 checked_5_224))))) (range_split (range_split (range_split (range_split checked_5_232 (range_split checked_5_240 checked_5_248)) (range_split (range_split checked_5_256 checked_5_264) (range_split checked_5_272 checked_5_280))) (range_split (range_split (range_split checked_5_288 checked_5_296) (range_split checked_5_304 checked_5_312)) (range_split (range_split checked_5_320 checked_5_328) (range_split checked_5_336 checked_5_344)))) (range_split (range_split (range_split checked_5_352 (range_split checked_5_360 checked_5_368)) (range_split (range_split checked_5_376 checked_5_384) (range_split checked_5_392 checked_5_400))) (range_split (range_split (range_split checked_5_408 checked_5_416) (range_split checked_5_424 checked_5_432)) (range_split (range_split checked_5_440 checked_5_448) (range_split checked_5_456 checked_5_464)))))) (range_split (range_split (range_split (range_split (range_split checked_5_472 (range_split checked_5_480 checked_5_488)) (range_split (range_split checked_5_496 checked_5_504) (range_split checked_5_512 checked_5_520))) (range_split (range_split (range_split checked_5_528 checked_5_536) (range_split checked_5_544 checked_5_552)) (range_split (range_split checked_5_560 checked_5_568) (range_split checked_5_576 checked_5_584)))) (range_split (range_split (range_split checked_5_592 (range_split checked_5_600 checked_5_608)) (range_split (range_split checked_5_616 checked_5_624) (range_split checked_5_632 checked_5_640))) (range_split (range_split (range_split checked_5_648 checked_5_656) (range_split checked_5_664 checked_5_672)) (range_split (range_split checked_5_680 checked_5_688) (range_split checked_5_696 checked_5_704))))) (range_split (range_split (range_split (range_split checked_5_712 (range_split checked_5_720 checked_5_728)) (range_split (range_split checked_5_736 checked_5_744) (range_split checked_5_752 checked_5_760))) (range_split (range_split (range_split checked_5_768 checked_5_776) (range_split checked_5_784 checked_5_792)) (range_split (range_split checked_5_800 checked_5_808) (range_split checked_5_816 checked_5_824)))) (range_split (range_split (range_split checked_5_832 (range_split checked_5_840 checked_5_848)) (range_split (range_split checked_5_856 checked_5_864) (range_split checked_5_872 checked_5_880))) (range_split (range_split (range_split checked_5_888 checked_5_896) (range_split checked_5_904 checked_5_912)) (range_split (range_split checked_5_920 checked_5_928) (range_split checked_5_936 checked_5_944)))))))

theorem checked_budget_6 : ∀ i, 0 ≤ i → i < 2709 → Z 6 i = true :=
  (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split checked_6_0 checked_6_8) (range_split checked_6_16 (range_split checked_6_24 checked_6_32))) (range_split (range_split checked_6_40 checked_6_48) (range_split checked_6_56 (range_split checked_6_64 checked_6_72)))) (range_split (range_split (range_split checked_6_80 checked_6_88) (range_split checked_6_96 (range_split checked_6_104 checked_6_112))) (range_split (range_split checked_6_120 (range_split checked_6_128 checked_6_136)) (range_split checked_6_144 (range_split checked_6_152 checked_6_160))))) (range_split (range_split (range_split (range_split checked_6_168 checked_6_176) (range_split checked_6_184 (range_split checked_6_192 checked_6_200))) (range_split (range_split checked_6_208 checked_6_216) (range_split checked_6_224 (range_split checked_6_232 checked_6_240)))) (range_split (range_split (range_split checked_6_248 checked_6_256) (range_split checked_6_264 (range_split checked_6_272 checked_6_280))) (range_split (range_split checked_6_288 (range_split checked_6_296 checked_6_304)) (range_split checked_6_312 (range_split checked_6_320 checked_6_328)))))) (range_split (range_split (range_split (range_split (range_split checked_6_336 checked_6_344) (range_split checked_6_352 (range_split checked_6_360 checked_6_368))) (range_split (range_split checked_6_376 checked_6_384) (range_split checked_6_392 (range_split checked_6_400 checked_6_408)))) (range_split (range_split (range_split checked_6_416 checked_6_424) (range_split checked_6_432 (range_split checked_6_440 checked_6_448))) (range_split (range_split checked_6_456 (range_split checked_6_464 checked_6_472)) (range_split checked_6_480 (range_split checked_6_488 checked_6_496))))) (range_split (range_split (range_split (range_split checked_6_504 checked_6_512) (range_split checked_6_520 (range_split checked_6_528 checked_6_536))) (range_split (range_split checked_6_544 checked_6_552) (range_split checked_6_560 (range_split checked_6_568 checked_6_576)))) (range_split (range_split (range_split checked_6_584 checked_6_592) (range_split checked_6_600 (range_split checked_6_608 checked_6_616))) (range_split (range_split checked_6_624 (range_split checked_6_632 checked_6_640)) (range_split checked_6_648 (range_split checked_6_656 checked_6_664))))))) (range_split (range_split (range_split (range_split (range_split (range_split checked_6_672 checked_6_680) (range_split checked_6_688 (range_split checked_6_696 checked_6_704))) (range_split (range_split checked_6_712 checked_6_720) (range_split checked_6_728 (range_split checked_6_736 checked_6_744)))) (range_split (range_split (range_split checked_6_752 checked_6_760) (range_split checked_6_768 (range_split checked_6_776 checked_6_784))) (range_split (range_split checked_6_792 (range_split checked_6_800 checked_6_808)) (range_split checked_6_816 (range_split checked_6_824 checked_6_832))))) (range_split (range_split (range_split (range_split checked_6_840 checked_6_848) (range_split checked_6_856 (range_split checked_6_864 checked_6_872))) (range_split (range_split checked_6_880 checked_6_888) (range_split checked_6_896 (range_split checked_6_904 checked_6_912)))) (range_split (range_split (range_split checked_6_920 checked_6_928) (range_split checked_6_936 (range_split checked_6_944 checked_6_952))) (range_split (range_split checked_6_960 (range_split checked_6_968 checked_6_976)) (range_split checked_6_984 (range_split checked_6_992 checked_6_1000)))))) (range_split (range_split (range_split (range_split (range_split checked_6_1008 checked_6_1016) (range_split checked_6_1024 (range_split checked_6_1032 checked_6_1040))) (range_split (range_split checked_6_1048 checked_6_1056) (range_split checked_6_1064 (range_split checked_6_1072 checked_6_1080)))) (range_split (range_split (range_split checked_6_1088 checked_6_1096) (range_split checked_6_1104 (range_split checked_6_1112 checked_6_1120))) (range_split (range_split checked_6_1128 (range_split checked_6_1136 checked_6_1144)) (range_split checked_6_1152 (range_split checked_6_1160 checked_6_1168))))) (range_split (range_split (range_split (range_split checked_6_1176 checked_6_1184) (range_split checked_6_1192 (range_split checked_6_1200 checked_6_1208))) (range_split (range_split checked_6_1216 (range_split checked_6_1224 checked_6_1232)) (range_split checked_6_1240 (range_split checked_6_1248 checked_6_1256)))) (range_split (range_split (range_split checked_6_1264 checked_6_1272) (range_split checked_6_1280 (range_split checked_6_1288 checked_6_1296))) (range_split (range_split checked_6_1304 (range_split checked_6_1312 checked_6_1320)) (range_split checked_6_1328 (range_split checked_6_1336 checked_6_1344)))))))) (range_split (range_split (range_split (range_split (range_split (range_split (range_split checked_6_1352 checked_6_1360) (range_split checked_6_1368 (range_split checked_6_1376 checked_6_1384))) (range_split (range_split checked_6_1392 checked_6_1400) (range_split checked_6_1408 (range_split checked_6_1416 checked_6_1424)))) (range_split (range_split (range_split checked_6_1432 checked_6_1440) (range_split checked_6_1448 (range_split checked_6_1456 checked_6_1464))) (range_split (range_split checked_6_1472 (range_split checked_6_1480 checked_6_1488)) (range_split checked_6_1496 (range_split checked_6_1504 checked_6_1512))))) (range_split (range_split (range_split (range_split checked_6_1520 checked_6_1528) (range_split checked_6_1536 (range_split checked_6_1544 checked_6_1552))) (range_split (range_split checked_6_1560 checked_6_1568) (range_split checked_6_1576 (range_split checked_6_1584 checked_6_1592)))) (range_split (range_split (range_split checked_6_1600 checked_6_1608) (range_split checked_6_1616 (range_split checked_6_1624 checked_6_1632))) (range_split (range_split checked_6_1640 (range_split checked_6_1648 checked_6_1656)) (range_split checked_6_1664 (range_split checked_6_1672 checked_6_1680)))))) (range_split (range_split (range_split (range_split (range_split checked_6_1688 checked_6_1696) (range_split checked_6_1704 (range_split checked_6_1712 checked_6_1720))) (range_split (range_split checked_6_1728 checked_6_1736) (range_split checked_6_1744 (range_split checked_6_1752 checked_6_1760)))) (range_split (range_split (range_split checked_6_1768 checked_6_1776) (range_split checked_6_1784 (range_split checked_6_1792 checked_6_1800))) (range_split (range_split checked_6_1808 (range_split checked_6_1816 checked_6_1824)) (range_split checked_6_1832 (range_split checked_6_1840 checked_6_1848))))) (range_split (range_split (range_split (range_split checked_6_1856 checked_6_1864) (range_split checked_6_1872 (range_split checked_6_1880 checked_6_1888))) (range_split (range_split checked_6_1896 (range_split checked_6_1904 checked_6_1912)) (range_split checked_6_1920 (range_split checked_6_1928 checked_6_1936)))) (range_split (range_split (range_split checked_6_1944 checked_6_1952) (range_split checked_6_1960 (range_split checked_6_1968 checked_6_1976))) (range_split (range_split checked_6_1984 (range_split checked_6_1992 checked_6_2000)) (range_split checked_6_2008 (range_split checked_6_2016 checked_6_2024))))))) (range_split (range_split (range_split (range_split (range_split (range_split checked_6_2032 checked_6_2040) (range_split checked_6_2048 (range_split checked_6_2056 checked_6_2064))) (range_split (range_split checked_6_2072 checked_6_2080) (range_split checked_6_2088 (range_split checked_6_2096 checked_6_2104)))) (range_split (range_split (range_split checked_6_2112 checked_6_2120) (range_split checked_6_2128 (range_split checked_6_2136 checked_6_2144))) (range_split (range_split checked_6_2152 (range_split checked_6_2160 checked_6_2168)) (range_split checked_6_2176 (range_split checked_6_2184 checked_6_2192))))) (range_split (range_split (range_split (range_split checked_6_2200 checked_6_2208) (range_split checked_6_2216 (range_split checked_6_2224 checked_6_2232))) (range_split (range_split checked_6_2240 checked_6_2248) (range_split checked_6_2256 (range_split checked_6_2264 checked_6_2272)))) (range_split (range_split (range_split checked_6_2280 checked_6_2288) (range_split checked_6_2296 (range_split checked_6_2304 checked_6_2312))) (range_split (range_split checked_6_2320 (range_split checked_6_2328 checked_6_2336)) (range_split checked_6_2344 (range_split checked_6_2352 checked_6_2360)))))) (range_split (range_split (range_split (range_split (range_split checked_6_2368 checked_6_2376) (range_split checked_6_2384 (range_split checked_6_2392 checked_6_2400))) (range_split (range_split checked_6_2408 checked_6_2416) (range_split checked_6_2424 (range_split checked_6_2432 checked_6_2440)))) (range_split (range_split (range_split checked_6_2448 checked_6_2456) (range_split checked_6_2464 (range_split checked_6_2472 checked_6_2480))) (range_split (range_split checked_6_2488 (range_split checked_6_2496 checked_6_2504)) (range_split checked_6_2512 (range_split checked_6_2520 checked_6_2528))))) (range_split (range_split (range_split (range_split checked_6_2536 checked_6_2544) (range_split checked_6_2552 (range_split checked_6_2560 checked_6_2568))) (range_split (range_split checked_6_2576 (range_split checked_6_2584 checked_6_2592)) (range_split checked_6_2600 (range_split checked_6_2608 checked_6_2616)))) (range_split (range_split (range_split checked_6_2624 checked_6_2632) (range_split checked_6_2640 (range_split checked_6_2648 checked_6_2656))) (range_split (range_split checked_6_2664 (range_split checked_6_2672 checked_6_2680)) (range_split checked_6_2688 (range_split checked_6_2696 checked_6_2704)))))))))

theorem checked_budget_7 : ∀ i, 0 ≤ i → i < 944 → Z 7 i = true :=
  (range_split (range_split (range_split (range_split (range_split (range_split checked_7_0 (range_split checked_7_8 checked_7_16)) (range_split (range_split checked_7_24 checked_7_32) (range_split checked_7_40 checked_7_48))) (range_split (range_split checked_7_56 (range_split checked_7_64 checked_7_72)) (range_split (range_split checked_7_80 checked_7_88) (range_split checked_7_96 checked_7_104)))) (range_split (range_split (range_split checked_7_112 (range_split checked_7_120 checked_7_128)) (range_split (range_split checked_7_136 checked_7_144) (range_split checked_7_152 checked_7_160))) (range_split (range_split (range_split checked_7_168 checked_7_176) (range_split checked_7_184 checked_7_192)) (range_split (range_split checked_7_200 checked_7_208) (range_split checked_7_216 checked_7_224))))) (range_split (range_split (range_split (range_split checked_7_232 (range_split checked_7_240 checked_7_248)) (range_split (range_split checked_7_256 checked_7_264) (range_split checked_7_272 checked_7_280))) (range_split (range_split (range_split checked_7_288 checked_7_296) (range_split checked_7_304 checked_7_312)) (range_split (range_split checked_7_320 checked_7_328) (range_split checked_7_336 checked_7_344)))) (range_split (range_split (range_split checked_7_352 (range_split checked_7_360 checked_7_368)) (range_split (range_split checked_7_376 checked_7_384) (range_split checked_7_392 checked_7_400))) (range_split (range_split (range_split checked_7_408 checked_7_416) (range_split checked_7_424 checked_7_432)) (range_split (range_split checked_7_440 checked_7_448) (range_split checked_7_456 checked_7_464)))))) (range_split (range_split (range_split (range_split (range_split checked_7_472 (range_split checked_7_480 checked_7_488)) (range_split (range_split checked_7_496 checked_7_504) (range_split checked_7_512 checked_7_520))) (range_split (range_split checked_7_528 (range_split checked_7_536 checked_7_544)) (range_split (range_split checked_7_552 checked_7_560) (range_split checked_7_568 checked_7_576)))) (range_split (range_split (range_split checked_7_584 (range_split checked_7_592 checked_7_600)) (range_split (range_split checked_7_608 checked_7_616) (range_split checked_7_624 checked_7_632))) (range_split (range_split (range_split checked_7_640 checked_7_648) (range_split checked_7_656 checked_7_664)) (range_split (range_split checked_7_672 checked_7_680) (range_split checked_7_688 checked_7_696))))) (range_split (range_split (range_split (range_split checked_7_704 (range_split checked_7_712 checked_7_720)) (range_split (range_split checked_7_728 checked_7_736) (range_split checked_7_744 checked_7_752))) (range_split (range_split (range_split checked_7_760 checked_7_768) (range_split checked_7_776 checked_7_784)) (range_split (range_split checked_7_792 checked_7_800) (range_split checked_7_808 checked_7_816)))) (range_split (range_split (range_split checked_7_824 (range_split checked_7_832 checked_7_840)) (range_split (range_split checked_7_848 checked_7_856) (range_split checked_7_864 checked_7_872))) (range_split (range_split (range_split checked_7_880 checked_7_888) (range_split checked_7_896 checked_7_904)) (range_split (range_split checked_7_912 checked_7_920) (range_split checked_7_928 checked_7_936)))))))

theorem checked_budget_8 : ∀ i, 0 ≤ i → i < 42 → Z 8 i = true :=
  (range_split (range_split checked_8_0 (range_split checked_8_8 checked_8_16)) (range_split checked_8_24 (range_split checked_8_32 checked_8_40)))

theorem checked_budget_9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true :=
  checked_9_0

theorem allChecked (s : Nat) (hs : s ≤ 9) : ∀ i, i < NN s → Z s i = true := by

  interval_cases s

  · intro i hi; simp [NN] at hi

  · intro i hi; simp [NN] at hi

  · intro i hi; simp [NN] at hi

  · intro i hi; exact checked_budget_3 i (Nat.zero_le i) hi

  · intro i hi; exact checked_budget_4 i (Nat.zero_le i) hi

  · intro i hi; exact checked_budget_5 i (Nat.zero_le i) hi

  · intro i hi; exact checked_budget_6 i (Nat.zero_le i) hi

  · intro i hi; exact checked_budget_7 i (Nat.zero_le i) hi

  · intro i hi; exact checked_budget_8 i (Nat.zero_le i) hi

  · intro i hi; exact checked_budget_9 i (Nat.zero_le i) hi

end PEqualNP.Outside.L_meta_25385_aux.SmallCert


namespace PEqualNP.Outside.L_meta_25385_aux.SmallCert

def RootG (s : Nat) : Bool :=
  !(coversP pairsG s xsM) || cutHitH s (hk seed xsM) xsM || found SS NN idx s xsM

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 6 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG :
    ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by
  have checked : xsM.sublists.all (fun zs =>
      (zs == xsM) || !(unorientedCov pairsG zs)) = true := by decide +kernel
  intro zs hz hne
  have h := List.all_eq_true.mp checked zs hz
  simpa only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', hne, false_or] using h

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem noRunFull
    (checked : ∀ s, s ≤ 9 → ∀ i, i < NN s → Z s i = true)
    (s : Nat) (hs : s ≤ 9) (h : RunD dm goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h
    change 5 ≤ s + 1 at hl
    omega
  have hr := span_ok rootChecked s hmin (by omega)
  have hcov := coversP_ok (T := goalM) (by decide +kernel : dm &&& mask256 = dm)
    pairsG (by decide +kernel) h
  unfold RootG at hr
  rw [hcov, Bool.not_true, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHitH_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact barFast_all (dm := dm) (T := goalM) (pairs := pairsG)
      (r1s := r1sG) (r2s := r2sG) (mp := mpG) (SD := SD) (S := SS) (N := NN)
      (htAt := htAt) (idxH := idxH) (ori := ori) (seed := seed) (pool := [])
      (cutHitH := cutHitH) (cap := 9)
      (by decide +kernel) rfl rfl (by decide +kernel) SD_eq
      (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 h)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem certificate_implies_lower
    (checked : ∀ s, s ≤ 9 → ∀ i, i < NN s → Z s i = true) :
    Lower dm xsM goalM 10 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dm goalM := by
    have h0 : isConstB dm goalM = false := by decide +kernel
    intro h
    rw [(isConstB_iff _ _).2 h] at h0
    exact Bool.noConfusion h0
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ :=
    reach_to_run (d := dm) (roots := xsM) (T := goalM) (p := p) (bank := bank)
      (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd
      (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x
    simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub
  have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq
    exact noRunFull checked s (by omega) hrun'
  · have hcov := unorientedCov_ok (T := goalM) (by decide +kernel) pairsG
      (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq
    rw [hcov] at hbad
    exact Bool.noConfusion hbad

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem certificate_implies_full_lower
    (checked : ∀ s, s ≤ 9 → ∀ i, i < NN s → Z s i = true) :
    Lower 2097151 [63, 1986, 30852, 233736, 860688, 1721376] 109807 11 := by
  have prior := certificate_implies_lower checked
  have lifted := lower_slice
    (d := 2097151) (dSub := dm) (T := 109807) (TSub := goalM) (L := 10)
    (roots := [63, 1986, 30852, 233736, 860688, 1721376]) (rootsSub := xsM)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) [(63, 5, 20)] (by decide +kernel) (by decide +kernel) prior
  simpa using lifted

end PEqualNP.Outside.L_meta_25385_aux.SmallCert

namespace PEqualNP.Outside.L_meta_25385_aux

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

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


end PEqualNP.Outside.L_meta_25385_aux

theorem PEqualNP.Outside.L_meta_25385 :
    ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧
      ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
        (6375855 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact PEqualNP.Outside.L_meta_25385_aux.graphLower25385_implies_refutation
    (PEqualNP.Outside.L_meta_25385_aux.SmallCert.certificate_implies_full_lower
      PEqualNP.Outside.L_meta_25385_aux.SmallCert.allChecked)
