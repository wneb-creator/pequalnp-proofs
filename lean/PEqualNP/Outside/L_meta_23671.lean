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


namespace PEqualNP.Outside.L_meta_23671_aux

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

section part1
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
end part1

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

def careDom : Nat := 0x101170117177e
def careGoal : Nat := 0x600061242
def careRoots : List Nat := [0x20002022a, 0x40004044c, 0x1000101070, 0x10001001700, 0x1000001170000, 0x1011700000000]

def carePoint (r : Nat) : Fin 6 → Bool := fun i => r.testBit i.val

set_option maxRecDepth 40000 in
lemma careRoots_bits : ∀ r : Fin 64, careDom.testBit r.val = true →
    careRoots.map (·.testBit r.val) = List.ofFn (carePoint r.val) := by
  decide +kernel

set_option maxRecDepth 40000 in
lemma carePairs : ∀ r : Fin 64, careDom.testBit r.val = true →
    ∃ i j : Fin 6,
      List.ofFn (carePoint r.val) = (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) ∧
      careGoal.testBit r.val = (36153 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

lemma care_lower_to_circuit (hlow : Lower careDom careRoots careGoal 9) :
    ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧
      C.size ≤ 8 ∧ ∀ i j : Fin 6,
      C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (36153 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  rintro ⟨C, hfan, hsz, hev⟩
  have hsup0 : ∀ v ∈ careRoots, Avail mask256 careRoots v := fun v hv => Or.inr ⟨v, hv, rfl⟩
  obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach C.gates careRoots hfan 0 careRoots careRoots rfl hsup0
  set out := (execN C.gates careRoots).getD C.output 0
  have hout : out &&& careDom = careGoal &&& careDom := by
    apply Nat.eq_of_testBit_eq
    intro r
    rw [Nat.testBit_and, Nat.testBit_and]
    by_cases hd : careDom.testBit r = true
    · rw [hd, Bool.and_true, Bool.and_true]
      have hlt : r < 64 := by
        by_contra h
        have hf : careDom.testBit r = false := by
          apply Nat.testBit_lt_two_pow
          exact lt_of_lt_of_le (by decide : careDom < 2 ^ 64)
            (Nat.pow_le_pow_right (by omega) (by omega))
        rw [hd] at hf
        contradiction
      have h1 := execN_bit C.gates careRoots r (by omega) (fun g hg => (hfan g hg).1)
      have h2 := congrArg (fun l => l.getD C.output false) h1
      rw [careRoots_bits ⟨r, hlt⟩ hd] at h2
      have hgd : ((execN C.gates careRoots).map (·.testBit r)).getD C.output false =
          out.testBit r := by
        simp only [out, List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (execN C.gates careRoots)[C.output]? with
        | none => simp
        | some v => rfl
      rw [hgd] at h2
      obtain ⟨i, j, hij, hgoal⟩ := carePairs ⟨r, hlt⟩ hd
      change out.testBit r = C.eval (List.ofFn (carePoint r)) at h2
      rw [hij] at h2
      exact h2.trans ((hev i j).trans hgoal.symm)
    · have hf : careDom.testBit r = false := Bool.eq_false_iff.mpr hd
      rw [hf, Bool.and_false, Bool.and_false]
  have hav_out : Avail mask256 bank out := by
    by_cases hi : C.output < (execN C.gates careRoots).length
    · exact hsup _ (getD_mem hi)
    · rw [show out = 0 from List.getD_eq_default _ _ (by omega)]
      exact Or.inl (Or.inl (by simp))
  have hd256 : careDom &&& mask256 = careDom := by decide +kernel
  have hm256 : mask256 &&& mask256 = mask256 := by decide +kernel
  have houtm : (out &&& mask256) &&& careDom = careGoal &&& careDom := by
    rw [Nat.and_assoc, Nat.and_comm mask256 careDom, hd256, hout]
  have hncT : ¬ IsConst careDom careGoal := by unfold IsConst; decide +kernel
  have hnc_m : ¬ IsConst careDom (out &&& mask256) := fun hc => hncT (by
    rcases hc with h0 | h1
    · exact Or.inl (houtm.symm.trans h0)
    · exact Or.inr (houtm.symm.trans h1))
  have hnc_256 : ¬ IsConst mask256 out := fun hc => hnc_m (by
    rcases hc with h0 | h1
    · exact Or.inl (by rw [h0]; simp)
    · exact Or.inr (by rw [h1, Nat.and_comm, hd256]))
  obtain ⟨s, ws, hs, _, hws, hrun⟩ := reach_to_run hm256 hnc_256 hr hav_out
  have hwsCare : ∀ w ∈ ws, Avail careDom careRoots w := fun w hw => by
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 (hws w hw)
    exact Or.inr ⟨u, hu, by rw [Nat.and_assoc, Nat.and_comm mask256 careDom, hd256]⟩
  obtain ⟨q, next, hq, hav_q, hqp⟩ := contraction hd256 hd256 hnc_m hrun
    (show NatReach careDom careRoots 0 careRoots from rfl) hwsCare
  have hL := hlow q next hq (avail_of_eq houtm hav_q)
  have : C.gates.length ≤ 8 := hsz
  omega

def careSepPairs : List (Nat × Nat) := [(2, 1), (2, 6), (2, 9), (2, 12), (2, 17), (2, 18), (2, 33), (2, 34), (3, 1), (3, 6), (3, 9), (3, 12), (3, 17), (3, 18), (3, 33), (3, 34), (4, 1), (4, 6), (4, 9), (4, 12), (4, 17), (4, 18), (4, 33), (4, 34), (5, 1), (5, 6), (5, 9), (5, 12), (5, 17), (5, 18), (5, 33), (5, 34), (8, 1), (8, 6), (8, 9), (8, 12), (8, 17), (8, 18), (8, 33), (8, 34), (10, 1), (10, 6), (10, 9), (10, 12), (10, 17), (10, 18), (10, 33), (10, 34), (16, 1), (16, 6), (16, 9), (16, 12), (16, 17), (16, 18), (16, 33), (16, 34), (20, 1), (20, 6), (20, 9), (20, 12), (20, 17), (20, 18), (20, 33), (20, 34), (24, 1), (24, 6), (24, 9), (24, 12), (24, 17), (24, 18), (24, 33), (24, 34), (32, 1), (32, 6), (32, 9), (32, 12), (32, 17), (32, 18), (32, 33), (32, 34), (36, 1), (36, 6), (36, 9), (36, 12), (36, 17), (36, 18), (36, 33), (36, 34), (40, 1), (40, 6), (40, 9), (40, 12), (40, 17), (40, 18), (40, 33), (40, 34), (48, 1), (48, 6), (48, 9), (48, 12), (48, 17), (48, 18), (48, 33), (48, 34)]

def careR1 : List Nat := careSepPairs.map Prod.fst
def careR2 : List Nat := careSepPairs.map Prod.snd
def careMP : Nat := 0xffffffffffffffffffffffffff

def careNN : Nat → Nat
  | 3 => 4
  | 4 => 80
  | 5 => 573
  | 6 => 583
  | 7 => 64
  | 8 => 1
  | _ => 0

def careDict : Nat → Nat
  | 0 => 0x70e000000000000044c00000000000004000000000000000200000000000000007e000000000000004000000000000000200000000000000008
  | 1 => 0x15540000000000001400000000000000120000000000000010700000000000001060000000000000104000000000000010200000000000001000
  | 2 => 0x404000000000000040040000000000004000800000000000400000000000000020000000000000000177e000000000000174c0000000000001700
  | 3 => 0x17007e000000000014000000000000001010700000000000101000000000000010000000000000000600000000000000041000000000000004044c
  | 4 => 0x113177e000000000107070e000000000104174c00000000010410400000000001040000000000000100170000000000010010000000000001000000
  | 5 => 0x20002020a0000000200020202000000020002020000000002000200000000000200000000000000000117177e00000000011700000000000001151554
  | 6 => 0x20002177e000000020002122a000000020002066e000000020002062a000000020002027e000000020002026a000000020002022a0000000200020222
  | 7 => 0x40000004000000004000000080000000400000000000000020117177e000000020102022a000000020012022a000000020006066e000000020006022a
  | 8 => 0x40004004c00000004000400480000000400040040000000040004000800000004000400000000000400001000000000040000044c0000000400000400
  | 9 => 0x40006044c000000040004146c000000040004144c0000000400041000000000040004064c000000040004046c000000040004044c0000000400040400
  | 10 => 0x600060000000000060004044c000000060002066e000000060002022a0000000600000000000000040104044c000000040014144c000000040014044c
  | 11 => 0x1000100000000000100000107000000010000010000000001000000000000000060006166e000000060006066e000000060006044c000000060006022a
  | 12 => 0x1000121070000000100010177e000000100010147000000010001012700000001000101078000000100010107000000010001010000000001000100070
  | 13 => 0x120012022a0000001200101070000000120002022a000000100117177e0000001001101070000000100014147000000010001410780000001000141070
  | 14 => 0x1400101070000000140004144c000000140004044c0000001400000000000000120016127a000000120012127a0000001200121070000000120012027a
  | 15 => 0x1400141470000000140014144c00000014001410780000001400141070000000140014044c000000140014000000000014001014700000001400101078
  | 16 => 0x1000000170000000100000010000000010000000000000000170000007e000000160016167e000000160016127a000000160012127a000000140014147c
  | 17 => 0x10001001720000001000100170e000001000100170800000100010017000000010001001500000001000100130000000100010010000000010001000000
  | 18 => 0x10001101700000001000107170e000001000104174c00000100010417000000010001021700000001000100177e000001000100174c0000010001001740
  | 19 => 0x104000010400000010400000000000001020102172a0000010201021700000001020102022a0000010201001700000001020002022a000001000117177e
  | 20 => 0x104010417000000010401041040000001040104044c0000010401040000000001040100174c0000010401001700000001040004044c000001040000174c
  | 21 => 0x11001101700000001100110107000000110010017000000011000101070000001070100170e000001070000070e000001060106176e000001040104174c
  | 22 => 0x1170100177e000001170010177e000001170002177e000001170000177e00000117000000000000011500001554000001130000177e0000011001101770
  | 23 => 0x10000011700200001000001170008000100000117000000010000011500000001000001070000000100000017000000010000000400000001000000000000
  | 24 => 0x100020117022a0001000201170000000100020002022a000100000117177e0001000001171000000100000117040000010000011702000001000001170040
  | 25 => 0x1000601170000000100040117044c0001000401170400000100040117004000010004011700080001000401170000000100040004044c0001000400000000
  | 26 => 0x100120117127a000100100117107000010010011700700001001001170000000100100017007000010010001410700001001000101070000100060117022a
  | 27 => 0x10017001000700001001700000000000100150015005400010014011710700001001401170000000100140010107000010013011700320001001300130032
  | 28 => 0x100170117007e00010017011700700001001701170000000100170017047e000100170017027e000100170017007e00010017001700700001001700170000
  | 29 => 0x101030107070e0001010301031702000101030103070e0001010301030302000101020117172a000101000117170000010100011700000001010001001700
  | 30 => 0x1010701070000000101070103070e00010107000000000001010501050504000101040117174c000101040117170000010104011700000001010301170302
  | 31 => 0x1011301131332000101130113033200010111011111100001011001171770000101070117070e0001010701170000000101070107170e000101070107070e
  | 32 => 0x1011501151554000101150115150000010115011500000001011500000000000101130117177e0001011301171332000101130113177e0001011301131732
  | 33 => 0x1011700000200000101170000004000010117000000200001011700000008000101170000000000010115011700000001011501151574000101150115155c
  | 34 => 0x101170004004000010117000400080001011700040000000101170002022a0001011700020000000101170000177e00010117000010000001011700000400
  | 35 => 0x101170012127a000101170010107000010117001000700001011700100000000101170006022a0001011700060000000101170004044c0001011700040400
  | 36 => 0x10117010017000001011701000000000101170017007e00010117001700700001011700170000000101170014107000010117001400000001011700130032
  | 37 => 0x1011701101770000101170107070e0001011701070000000101170104174c000101170104170000010117010400000001011701030302000101170102172a
  | 38 => 0x101170117004000010117011700320001011701170020000101170117000800010117011700000001011701150000000101170113177e0001011701131332
  | 39 => 0x101170117070e000101170117044c00010117011704000001011701170302000101170117022a0001011701170200000101170117007e0001011701170070
  | 40 => 0x101170117174c000101170117172a00010117011717000001011701171332000101170117127a00010117011710700001011701171000000101170117077e
  | 41 => 0x1011701171770
  | _ => 0

def careP1Dict : Nat → Nat
  | 0 => 0xffff0000ffff00000000000000ff000000ffff00000000000000ff000000000000000000000000000000000000000000000000000000ffffffff00000000000000000000000000000000000000000000ff0000000000000000000000000000ff00
  | 1 => 0xffff00ff00ff00000000000000ff000000000000000000000000000000000000000000000000000000ffff0000000000000000000000ff00000000000000000000000000000000000000000000000000ff00000000000000000000000000000000
  | 2 => 0xff0000000000000000000000000000000000000000000000000000000000ff00000000000000000000000000000000000000000000000000000000000000000000ffffffffffff00000000000000ffff0000ffff00000000000000ffff00000000
  | 3 => 0xffff0000ffffffff0000000000ff000000000000000000000000ff000000ffff00000000000000ff000000000000000000000000ff00000000000000000000000000000000000000000000000000000000000000000000000000000000ff000000ffff
  | 4 => 0xffffffffffffffffff00000000ff00ffffff0000ffff00000000ff0000ffff0000ffff00000000ff000000000000000000000000ff000000000000000000000000ff0000ffff0000000000000000ff000000000000000000000000ff0000000000000000
  | 5 => 0xff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffff00000000ffffff00000000000000000000ffffffffff00ff00ff
  | 6 => 0xffffffffffff000000000000000000ff00ff0000000000000000ff00ff00ffff00000000000000ff00ff00ff00000000000000000000ffffffff000000000000000000ff00ff00000000000000000000ff00ff00000000000000000000ff000000
  | 7 => 0xff000000000000000000000000000000000000ffffffffffffffffff00000000ff00000000ff00ff000000000000ff000000ff00ff0000000000000000ff00ff00ffff000000000000000000ff00ff00
  | 8 => 0xffff0000000000000000000000ff00000000000000000000000000000000000000000000000000ff00000000000000000000000000000000000000000000000000000000000000000000ff000000ffff00000000000000ff0000000000
  | 9 => 0xff000000ffff00000000000000ff00ff00ffff00000000000000ff000000ffff0000000000000000000000000000000000000000ff000000ffff00000000000000ff00ff00ffff00000000000000ff000000ffff00000000000000ff0000000000
  | 10 => 0xff000000ffff00000000000000ff00ff00ffff000000000000000000ff00ff000000000000000000000000000000000000ff0000ff000000ffff0000000000ff00ff000000ffff0000000000ff00ff000000ffff
  | 11 => 0xff0000ff000000000000000000ff000000000000ffff00000000ff000000000000000000000000ff0000000000000000000000000000000000ff00ff00ffff00000000000000ff00ff00ffff00000000000000ff000000ffff000000000000000000ff00ff00
  | 12 => 0xff0000ff000000ffff00000000ff0000ff00ffffffffffff0000ff0000ff00ff00ffff00000000ff0000ff000000ffff00000000ff0000ff000000ffffff000000ff0000ff000000ffff00000000ff0000ff000000000000000000ff0000ff000000ffff0000
  | 13 => 0xff0000ff000000ff00ff000000ff0000ff000000ffff00000000ff000000000000ff00ff000000ff00ffffffffffffffffff0000ff00ffff000000ffff00000000ff0000ff00ff00ffff00000000ff0000ff000000ffffff000000ff0000ff000000ffff0000
  | 14 => 0xff0000ff000000ffff00000000ff00000000ff000000ffff0000ff00000000ff000000ffff0000ff000000000000000000000000ff0000ff000000ffffff000000ff0000ff000000ffffff000000ff0000ff000000ffff00000000ff0000ff000000ffffff00
  | 15 => 0xff0000ff00ff00ffff00000000ff0000ff00ff000000ffff0000ff0000ff000000ffffff000000ff0000ff000000ffff00000000ff0000ff00ff000000ffff0000ff0000ff000000000000000000ff0000ff00ff00ffff00000000ff0000ff000000ffffff00
  | 16 => 0xff0000000000ffff0000000000ff000000000000000000000000ff00000000000000000000000000ffff0000000000ffffffff0000ff0000ff00ff00ffffffff0000ff0000ff000000ffffff000000ff0000ff000000ffffff000000ff0000ff00ff00ffffffff
  | 17 => 0xff0000ff0000ffffff00000000ff0000ff0000ffff0000ffff00ff0000ff0000ffff0000ff0000ff0000ff0000ffff0000000000ff0000ff0000ffff0000000000ff0000ff000000ff0000000000ff0000ff000000000000000000ff0000ff0000000000000000
  | 18 => 0xff0000ffff00ffff0000000000ff0000ff00ffffff0000ffff00ff0000ff0000ffff0000ffff00ff0000ff0000ffff0000000000ff0000ff0000ffff0000000000ff0000ff0000ffffffffffff00ff0000ff0000ffff0000ffff00ff0000ff0000ffff00000000
  | 19 => 0xff000000000000000000000000ff000000000000000000000000ff0000ff0000ffffff00ff0000ff0000ff0000ffff0000000000ff0000ff00000000ff00ff0000ff0000ff0000ffff0000000000ff00000000000000ff00ff0000ff0000ffffffffffffffffff
  | 20 => 0xff0000ff0000ffff0000000000ff0000ff000000000000000000ff0000ff0000ff000000ffff00ff0000ff000000000000000000ff0000ff0000ffff0000ffff00ff0000ff0000ffff0000000000ff0000000000ff000000ffff00ff0000000000ffff0000ffff
  | 21 => 0xffff00ffff00ffff0000000000ffff00ffff000000ffff000000ffff00ff0000ffff0000000000ffff0000ff000000ffff000000ff00ffff0000ffff0000ffff00ff00ff000000ffff0000ffff00ff0000ff0000ffffff00ffff00ff0000ff0000ffff0000ffff
  | 22 => 0xffffffff0000ffffffffffff00ffffff00ff00ffffffffffff00ffffff000000ffffffffffff00ffffff000000ffffffffffff00ffffff00000000000000000000ffffff000000ffff00ff00ff00ffffff000000ffffffffffff00ffff00ffff00ffffffff0000
  | 23 => 0xff000000ffffff0000ff000000ff000000ffffff00000000ff00ff000000ffffff000000000000ff000000ffffff000000000000ff000000ff00ff000000000000ff00000000ffff000000000000ff000000000000000000000000ff000000000000000000000000
  | 24 => 0xff000000ffffff0000ff00ff00ff000000ffffff000000000000ff0000000000000000ff00ff00ff000000ffffffffffffffffffff000000ffffff000000000000ff000000ffffffff0000000000ff000000ffffff000000000000ff000000ffffff000000000000
  | 25 => 0xff000000ffffff000000000000ff000000ffffffff000000ffffff000000ffffffff0000000000ff000000ffffff000000000000ff000000ffffff00000000ff00ff000000ffffff000000000000ff000000000000ff000000ffffff000000000000000000000000
  | 26 => 0xff00ff00ffffff0000ffffff00ff00ff00ffffff0000ffff0000ff00ff00ffffff0000ffff0000ff00ff00ffffff000000000000ff00ff0000ffff0000ffff0000ff00ff0000ff000000ffff0000ff00ff0000ff000000ffff0000ff000000ffffff0000ff00ff00
  | 27 => 0xff00ffff00ff000000ffff0000ff00ffff000000000000000000ff00ffff00ffff000000ff00ffff00ff00ffffff0000ffff0000ff00ff00ffffff000000000000ff00ff0000ff000000ffff0000ff00ffffffffff0000ffff0000ff00ffff00ffff0000ffff0000
  | 28 => 0xff00ffffffffff0000ffffffffff00ffffffffff0000ffff0000ff00ffffffffff000000000000ff00ffff00ffffff00ffffffffff00ffff00ffff0000ffffffffff00ffff00ffff0000ffffffffff00ffff00ffff0000ffff0000ff00ffff00ffff000000000000
  | 29 => 0xffff00ffff00ffffff0000ffffffff00ffff00ffffff00000000ffff00ffff00ffffff0000ffffffff00ffff00ff00ff00000000ffff0000ffffffffffff00ff00ffff0000ffffffffff00000000ffff0000ffffff000000000000ffff0000ff0000ffff00000000
  | 30 => 0xffff00ffff00ff000000000000ffff00ffff00ffffff0000ffffffff00ff000000000000000000ffff00ffff00ffffff000000ffffff0000ffffffffff0000ffffffff0000ffffffffff00000000ffff0000ffffff000000000000ffff00ffffffff00ff00000000
  | 31 => 0xffffffffffffff00ffffff0000ffffffffffffff00ffffff0000ffffffffffffff00ff00ff0000ffffff00ffffffffffffff0000ffff00ffffffffffff0000ffffffff00ffffffff000000000000ffff00ffff00ffffff0000ffffffff00ffff00ffffff0000ffff
  | 32 => 0xffffffffffffffffff00ff00ffffffffffffffffffff00000000ffffffffffffff000000000000ffffffff000000000000000000ffffffffffffffffffffffffffffffffffffffff00ffffff0000ffffffffffffffffffffffffffffffffffffffffffffffff0000
  | 33 => 0xffffffff000000000000000000ffffffff000000000000000000ffffffff0000000000ff000000ffffffff00000000000000ff00ffffffff000000000000000000ffffffffffffff000000000000ffffffffffffffffffffff00ffffffffffffffffffff00ffffff
  | 34 => 0xffffffff000000000000000000ffffffff00000000000000ff00ffffffff000000000000000000ffffffff0000000000ff00ff00ffffffff000000000000000000ffffffff000000ffffffffffffffffffff000000000000000000ffffffff000000ff0000000000
  | 35 => 0xffffffff00ff000000ffffff00ffffffff00ff000000ffff0000ffffffff00ff000000ffff0000ffffffff00ff00000000000000ffffffff0000000000ff00ff00ffffffff000000000000000000ffffffff000000ff000000ffffffffffff000000ff0000000000
  | 36 => 0xffffffffff0000ffff00000000ffffffffff0000000000000000ffffffff00ffff0000ffffffffffffffff00ffff0000ffff0000ffffffff00ffff000000000000ffffffff00ff000000ffff0000ffffffff00ff00000000000000ffffffff00ffff0000ffff0000
  | 37 => 0xffffffffffff00ffffffff0000ffffffffff00ffffff0000ffffffffffffff00ff000000000000ffffffffff0000ffff0000ffffffffffffff0000ffff00000000ffffffffff0000000000000000ffffffffff00ff00ff00000000ffffffffff0000ffffff00ff00
  | 38 => 0xffffffffffffff000000000000ffffffffffffff0000ffff0000ffffffffffffff0000ff000000ffffffffffffff00000000ff00ffffffffffffff000000000000ffffffffffffff000000000000ffffffffffffffffffffffffffffffffffffffff00ffffff0000
  | 39 => 0xffffffffffffffffff0000ffffffffffffffffffff000000ffffffffffffffffffff0000000000ffffffffffffff00ff00000000ffffffffffffff0000ff00ff00ffffffffffffff000000000000ffffffffffffff0000ffffffffffffffffffffff0000ffff0000
  | 40 => 0xffffffffffffffffff0000ffffffffffffffffffffffff00ff00ffffffffffffffffff00000000ffffffffffffff00ffffff0000ffffffffffffff0000ffffff00ffffffffffffff0000ffff0000ffffffffffffff000000000000ffffffffffffffffffffffffff
  | 41 => 0xffffffffffffffffffffff0000
  | _ => 0

def careP2Dict : Nat → Nat
  | 0 => 0x505050505050505050505050502020202020202020202020202000000000000000000000000000404040404040404040404040403030303030303030303030303020202020202020202020202020000000000000000000000000000000000000000000000000000
  | 1 => 0xa0a0a0a0a0a0a0a0a0a0a0a0a080808080808080808080808080c0c0c0c0c0c0c0c0c0c0c0c0c0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0808080808080808080808080808080808080808080808080808
  | 2 => 0x20202020202020202020202020222222222222222222222222222020202020202020202020202020202020202020202020202020101010101010101010101010100f0f0f0f0f0f0f0f0f0f0f0f0f0e0e0e0e0e0e0e0e0e0e0e0e0e0c0c0c0c0c0c0c0c0c0c0c0c0c
  | 3 => 0x33333333333333333333333333202020202020202020202020200a0a0a0a0a0a0a0a0a0a0a0a0a0808080808080808080808080800000000000000000000000000303030303030303030303030302828282828282828282828282822222222222222222222222222
  | 4 => 0x1f1f1f1f1f1f1f1f1f1f1f1f1f353535353535353535353535352e2e2e2e2e2e2e2e2e2e2e2e2e2a2a2a2a2a2a2a2a2a2a2a2a2a202020202020202020202020200c0c0c0c0c0c0c0c0c0c0c0c0c0808080808080808080808080800000000000000000000000000
  | 5 => 0x55555555555555555555555555555555555555555555555555555454545454545454545454545450505050505050505050505050404040404040404040404040403f3f3f3f3f3f3f3f3f3f3f3f3f303030303030303030303030302a2a2a2a2a2a2a2a2a2a2a2a2a
  | 6 => 0x5f5f5f5f5f5f5f5f5f5f5f5f5f5d5d5d5d5d5d5d5d5d5d5d5d5d575757575757575757575757575555555555555555555555555557575757575757575757575757575757575757575757575757575555555555555555555555555555555555555555555555555555
  | 7 => 0x8282828282828282828282828280808080808080808080808080808080808080808080808080807f7f7f7f7f7f7f7f7f7f7f7f7f55555555555555555555555555555555555555555555555555557777777777777777777777777775757575757575757575757575
  | 8 => 0xa2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0888888888888888888888888888282828282828282828282828280808080808080808080808080
  | 9 => 0xb2b2b2b2b2b2b2b2b2b2b2b2b2aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa8a8a8a8a8a8a8a8a8a8a8a8a8a6a6a6a6a6a6a6a6a6a6a6a6a6a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a0a0a0a0a0a0a0a0a0a0a0a0a0
  | 10 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0e2e2e2e2e2e2e2e2e2e2e2e2e2d7d7d7d7d7d7d7d7d7d7d7d7d7d5d5d5d5d5d5d5d5d5d5d5d5d5c0c0c0c0c0c0c0c0c0c0c0c0c0a2a2a2a2a2a2a2a2a2a2a2a2a2aaaaaaaaaaaaaaaaaaaaaaaaaaa2a2a2a2a2a2a2a2a2a2a2a2a2
  | 11 => 0xa0a0a0a0a0a0a0a0a0a0a0a0a0808080808080808080808080800000000000000000000000000fffffffffffffffffffffffffff7f7f7f7f7f7f7f7f7f7f7f7f7f2f2f2f2f2f2f2f2f2f2f2f2f2f5f5f5f5f5f5f5f5f5f5f5f5f5
  | 12 => 0x1a1a1a1a1a1a1a1a1a1a1a1a1a0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a0a0a0a0a0a0e0e0e0e0e0e0e0e0e0e0e0e0e0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0808080808080808080808080802020202020202020202020202
  | 13 => 0x555555555555555555555555554a4a4a4a4a4a4a4a4a4a4a4a4a555555555555555555555555553f3f3f3f3f3f3f3f3f3f3f3f3f0a0a0a0a0a0a0a0a0a0a0a0a0a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a
  | 14 => 0x8a8a8a8a8a8a8a8a8a8a8a8a8aaaaaaaaaaaaaaaaaaaaaaaaaaaa2a2a2a2a2a2a2a2a2a2a2a2a2808080808080808080808080807f7f7f7f7f7f7f7f7f7f7f7f7f5f5f5f5f5f5f5f5f5f5f5f5f5f5a5a5a5a5a5a5a5a5a5a5a5a5a57575757575757575757575757
  | 15 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa2a2a2a2a2a2a2a2a2a2a2a2a2a0a0a0a0a0a0a0a0a0a0a0a0a08a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a
  | 16 => 0xc0c0c0c0c0c0c0c0c0c0c0c0c0808080808080808080808080800000000000000000000000000c3c3c3c3c3c3c3c3c3c3c3c3c3ffffffffffffffffffffffffffffffffffffffffffffffffffffdfdfdfdfdfdfdfdfdfdfdfdfdfaaaaaaaaaaaaaaaaaaaaaaaaaa
  | 17 => 0xc0c0c0c0c0c0c0c0c0c0c0c0c0d0d0d0d0d0d0d0d0d0d0d0d0d0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c080808080808080808080808080c0c0c0c0c0c0c0c0c0c0c0c0c0808080808080808080808080800000000000000000000000000
  | 18 => 0xc0c0c0c0c0c0c0c0c0c0c0c0c3d3d3d3d3d3d3d3d3d3d3d3d3d2e2e2e2e2e2e2e2e2e2e2e2e2e2c2c2c2c2c2c2c2c2c2c2c2c2c1c1c1c1c1c1c1c1c1c1c1c1c1c0f0f0f0f0f0f0f0f0f0f0f0f0f0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e
  | 19 => 0x8a8a8a8a8a8a8a8a8a8a8a8a8a808080808080808080808080805d5d5d5d5d5d5d5d5d5d5d5d5d5c5c5c5c5c5c5c5c5c5c5c5c5c555555555555555555555555554c4c4c4c4c4c4c4c4c4c4c4c4c555555555555555555555555553f3f3f3f3f3f3f3f3f3f3f3f3f
  | 20 => 0xacacacacacacacacacacacacacaaaaaaaaaaaaaaaaaaaaaaaaaaa2a2a2a2a2a2a2a2a2a2a2a2a2a0a0a0a0a0a0a0a0a0a0a0a0a08e8e8e8e8e8e8e8e8e8e8e8e8e8c8c8c8c8c8c8c8c8c8c8c8c8ca2a2a2a2a2a2a2a2a2a2a2a2a28e8e8e8e8e8e8e8e8e8e8e8e8e
  | 21 => 0xc0c0c0c0c0c0c0c0c0c0c0c0c0a0a0a0a0a0a0a0a0a0a0a0a0a0c0c0c0c0c0c0c0c0c0c0c0c0c0a0a0a0a0a0a0a0a0a0a0a0a0acdcdcdcdcdcdcdcdcdcdcdcdcdc5c5c5c5c5c5c5c5c5c5c5c5c5ffffffffffffffffffffffffffaeaeaeaeaeaeaeaeaeaeaeaeae
  | 22 => 0xcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfdfdfdfdfdfdfdfdfdfdfdfdfdfcfcfcfcfcfcfcfcfcfcfcfcfcfc0c0c0c0c0c0c0c0c0c0c0c0c08a8a8a8a8a8a8a8a8a8a8a8a8a4f4f4f4f4f4f4f4f4f4f4f4f4f0e0e0e0e0e0e0e0e0e0e0e0e0e
  | 23 => 0x3030303030303030303030303030303030303030303030303030303030303030303030303030302020202020202020202020202030303030303030303030303030303030303030303030303030302020202020202020202020202000000000000000000000000000
  | 24 => 0x7575757575757575757575757570707070707070707070707070555555555555555555555555553f3f3f3f3f3f3f3f3f3f3f3f3f38383838383838383838383838303030303030303030303030303434343434343434343434343432323232323232323232323232
  | 25 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0b2b2b2b2b2b2b2b2b2b2b2b2b2b0b0b0b0b0b0b0b0b0b0b0b0b0b2b2b2b2b2b2b2b2b2b2b2b2b2b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0a2a2a2a2a2a2a2a2a2a2a2a2a280808080808080808080808080
  | 26 => 0x7f7f7f7f7f7f7f7f7f7f7f7f7f3a3a3a3a3a3a3a3a3a3a3a3a3a3232323232323232323232323230303030303030303030303030323232323232323232323232322a2a2a2a2a2a2a2a2a2a2a2a2a0a0a0a0a0a0a0a0a0a0a0a0a0af5f5f5f5f5f5f5f5f5f5f5f5f5
  | 27 => 0xc2c2c2c2c2c2c2c2c2c2c2c2c2c0c0c0c0c0c0c0c0c0c0c0c0c0a2a2a2a2a2a2a2a2a2a2a2a2a2bababababababababababababab0b0b0b0b0b0b0b0b0b0b0b0b08a8a8a8a8a8a8a8a8a8a8a8a8a7171717171717171717171717151515151515151515151515151
  | 28 => 0xf3f3f3f3f3f3f3f3f3f3f3f3f3f2f2f2f2f2f2f2f2f2f2f2f2f2f0f0f0f0f0f0f0f0f0f0f0f0f0f3f3f3f3f3f3f3f3f3f3f3f3f3f7f7f7f7f7f7f7f7f7f7f7f7f7f3f3f3f3f3f3f3f3f3f3f3f3f3f2f2f2f2f2f2f2f2f2f2f2f2f2f0f0f0f0f0f0f0f0f0f0f0f0f0
  | 29 => 0x757575757575757575757575755d5d5d5d5d5d5d5d5d5d5d5d5d55555555555555555555555555555555555555555555555555557d7d7d7d7d7d7d7d7d7d7d7d7d3c3c3c3c3c3c3c3c3c3c3c3c3c303030303030303030303030300c0c0c0c0c0c0c0c0c0c0c0c0c
  | 30 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0d5d5d5d5d5d5d5d5d5d5d5d5d5c0c0c0c0c0c0c0c0c0c0c0c0c0a0a0a0a0a0a0a0a0a0a0a0a0a0bebebebebebebebebebebebebebcbcbcbcbcbcbcbcbcbcbcbcbcb0b0b0b0b0b0b0b0b0b0b0b0b075757575757575757575757575
  | 31 => 0x5d5d5d5d5d5d5d5d5d5d5d5d5d55555555555555555555555555080808080808080808080808083e3e3e3e3e3e3e3e3e3e3e3e3ef5f5f5f5f5f5f5f5f5f5f5f5f5f0f0f0f0f0f0f0f0f0f0f0f0f0fdfdfdfdfdfdfdfdfdfdfdfdfdf5f5f5f5f5f5f5f5f5f5f5f5f5
  | 32 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaaa8a8a8a8a8a8a8a8a8a8a8a8a8a0a0a0a0a0a0a0a0a0a0a0a0a0808080808080808080808080807f7f7f7f7f7f7f7f7f7f7f7f7f7d7d7d7d7d7d7d7d7d7d7d7d7d5f5f5f5f5f5f5f5f5f5f5f5f5f5d5d5d5d5d5d5d5d5d5d5d5d5d
  | 33 => 0xc4c4c4c4c4c4c4c4c4c4c4c4c4c2c2c2c2c2c2c2c2c2c2c2c2c2c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0b0b0b0b0b0b0b0b0b0b0b0b0b0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
  | 34 => 0xe2e2e2e2e2e2e2e2e2e2e2e2e2e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0d5d5d5d5d5d5d5d5d5d5d5d5d5d0d0d0d0d0d0d0d0d0d0d0d0d0cfcfcfcfcfcfcfcfcfcfcfcfcfc8c8c8c8c8c8c8c8c8c8c8c8c8c0c0c0c0c0c0c0c0c0c0c0c0c0
  | 35 => 0xdfdfdfdfdfdfdfdfdfdfdfdfdfcacacacacacacacacacacacacac2c2c2c2c2c2c2c2c2c2c2c2c2c0c0c0c0c0c0c0c0c0c0c0c0c0f5f5f5f5f5f5f5f5f5f5f5f5f5f0f0f0f0f0f0f0f0f0f0f0f0f0e2e2e2e2e2e2e2e2e2e2e2e2e2e0e0e0e0e0e0e0e0e0e0e0e0e0
  | 36 => 0xccccccccccccccccccccccccccc0c0c0c0c0c0c0c0c0c0c0c0c0f3f3f3f3f3f3f3f3f3f3f3f3f3f2f2f2f2f2f2f2f2f2f2f2f2f2f0f0f0f0f0f0f0f0f0f0f0f0f0eaeaeaeaeaeaeaeaeaeaeaeaeae0e0e0e0e0e0e0e0e0e0e0e0e0d1d1d1d1d1d1d1d1d1d1d1d1d1
  | 37 => 0xcececececececececececececef5f5f5f5f5f5f5f5f5f5f5f5f5f0f0f0f0f0f0f0f0f0f0f0f0f0eeeeeeeeeeeeeeeeeeeeeeeeeeececececececececececececece0e0e0e0e0e0e0e0e0e0e0e0e0d5d5d5d5d5d5d5d5d5d5d5d5d5dddddddddddddddddddddddddd
  | 38 => 0xf2f2f2f2f2f2f2f2f2f2f2f2f2f1f1f1f1f1f1f1f1f1f1f1f1f1f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0e0e0e0e0e0e0e0e0e0e0e0e0e0dfdfdfdfdfdfdfdfdfdfdfdfdfdddddddddddddddddddddddddd
  | 39 => 0xf5f5f5f5f5f5f5f5f5f5f5f5f5f2f2f2f2f2f2f2f2f2f2f2f2f2f0f0f0f0f0f0f0f0f0f0f0f0f0f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f4f4f4f4f4f4f4f4f4f4f4f4f4f3f3f3f3f3f3f3f3f3f3f3f3f3f2f2f2f2f2f2f2f2f2f2f2f2f2
  | 40 => 0xfefefefefefefefefefefefefefdfdfdfdfdfdfdfdfdfdfdfdfdfcfcfcfcfcfcfcfcfcfcfcfcfcfdfdfdfdfdfdfdfdfdfdfdfdfdfffffffffffffffffffffffffffafafafafafafafafafafafafaf8f8f8f8f8f8f8f8f8f8f8f8f8f7f7f7f7f7f7f7f7f7f7f7f7f7
  | 41 => 0xfefefefefefefefefefefefefe
  | _ => 0

def careWireAt (i : Nat) : Nat := fld (careDict (i / 8)) 64 (i % 8)
def careP1At (i : Nat) : Nat := fld (careP1Dict (i / 8)) 104 (i % 8)
def careP2At (i : Nat) : Nat := fld (careP2Dict (i / 8)) 104 (i % 8)

def careWireDAt (i : Nat) : Nat × Nat × Nat := if i < 329 then (careWireAt i, careP1At i, careP2At i) else (0, 0, 0)
def careWireDOK (i : Nat) : Bool := (careP1At i == projBit careR1 (careWireAt i)) && (careP2At i == projBit careR2 (careWireAt i))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careWireDChecked : span careWireDOK 329 0 = true := by decide +kernel

lemma careProjBitZero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl

lemma careWireDAt_eq (i : Nat) :
    careWireDAt i = (let w := if i < 329 then careWireAt i else 0; (w, projBit careR1 w, projBit careR2 w)) := by
  unfold careWireDAt
  split
  · next hi =>
    have h := span_ok careWireDChecked i (Nat.zero_le i) (by omega)
    simp only [careWireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [careProjBitZero]
def careWireSAt (i : Nat) : Nat := if i < 329 then careWireAt i else 0

def careStateB : Nat → Nat → Nat
  | 3, 0 => 0x5089c3130000000002a0fa313000000000299003130000000001f09a313
  | 4, 0 => 0x9d9889a3140000000a14f9185a40000000999d8c4314000000099988b44d4000000031124621140000000311346212400000004e9f0923140000000461f092314
  | 4, 1 => 0x461f0b4494000000099988b64d4000000053188923140000000a14cc9a3140000000651889a3140000000999889a364000000083230c4494000000099c18c4494
  | 4, 2 => 0xa11889a3140000000461fc92314000000099be09a31400000009d9889236400000008f3589a314000000099be4e44940000000461f49231400000008f2f49c314
  | 4, 3 => 0x711f09231400000004618892354000000099bf8c4314000013346188922e5000000085b589c314000000031134863140000000539f09231400000007fa30f8314
  | 4, 4 => 0x99c789a314000000099b589a314000000046188b40640000000a1124620940000133771889231500000003e124620840000000541f092314000000054230f8314
  | 4, 5 => 0xa12a1003140000000999889c31400000004e988b0494000000099924620b40000000a09889a3140000000a2230c45a400000003113092314000000082a2cc4494
  | 4, 6 => 0xa0988923640000000709889231400000004898892314000000099988a23140000000859a09a314000000092188923140000000999f8c4314000000099c1cc44d4
  | 4, 7 => 0x83a30f849400000005e9dc9a314000000054188883140000000999c8c44d4000000099ac15072400000008a9889a3140000000999c0c449400000009c18892314
  | 4, 8 => 0x46188923340000000471889231400000007318892314000000099988923340000000461888c3140000000999889a314000000099968920b40000000461c8c4464
  | 4, 9 => 0x461f0e44940000000461f0b049400000009b18892314000000053988b0494000000076a30923140000000999c8c0494000000046208f8494000013c4618892315
  | 5, 0 => 0x127752a0c43150000000461f09231400000bd461f09231500000f154230c4315000010b461ccd04950000146461889231500001334619c92315000010b3412462085
  | 5, 1 => 0x133461ac9231500000ca461c8c449500001278a9889231500001074618892435000013331124620d5000013346188923450000133562309231500001464e98892315
  | 5, 2 => 0x13353988923150000133939c8c4495000010b5e9c8c04950000145999c8c4495000008c31160923150000133461889631500001337fa30c431500001334612462075
  | 5, 3 => 0x145461c8c4495000012b8a98892315000011554230c431500001157118892315000010b6b2a1003150000133461f09231500000f1541889231500001337fa74c4315
  | 5, 4 => 0x8c311249031500001184618892315000011b4618892315000008c3b9246214500000ca461dc92315000013375988923150000133461889236500000a74618892315
  | 5, 5 => 0x13346188922d5000012a461889231500000bd54230ee31500000e25e9dc9231500001155418892315000012d7c23092315000013354230e46250000133711c8c4495
  | 5, 6 => 0x133541c8c4495000013331124620e50000123461889231500000ca4e98892315000014299a30923150000115311246208500000ca4618892315000011d5e98892315
  | 5, 7 => 0xa852230c4315000011e6b230e4495000011e6b2189231500001333918892085000013393988923150000145999889231500001277c3a892315000014299a7492315
  | 5, 8 => 0x1454e988923150000145461889231500000bd3b92462085000010b50188923150000133311809231500000bd541dc9231500001337fa28c431500000bd3112484315
  | 5, 9 => 0x1337c230e449500000bd461dca8495000013331124620950000133461889232500000a8521889231500001157c23092315000013354230c431500001337118892315
  | 5, 10 => 0x8c3112462075000013331124620850000142461c8c44950000142431889231500001335418892315000008c311689212500001334498892315000012b4618892315
  | 5, 11 => 0xbd4b1889231500000bd4e988a8495000011e6b27492315000011e6b23092315000010b6a98892315000013383b5918495000013331124621f500001334598892315
  | 5, 12 => 0x8c311609243500000dc5ea309231500000bd4a988923150000133461d4c4315000008c3e188923150000133751c8c449500001115e9889236500001338f41d18495
  | 5, 13 => 0x11463a74c44950000133311246221500001334398892315000013346188a8495000010b461f09231500000ea5e9dc9231500001339298892315000010b6923092315
  | 5, 14 => 0x10b5e988b44d500001337c27492315000013354988b449500000e2701889231500001334d1889231500001337c23092315000010b619889236500000bd311347a315
  | 5, 15 => 0x133751889231500000ea461dc9231500001424e9889231500001145e9889a3150000117461889231500001424618892315000008c3918892435000013346188ac315
  | 5, 16 => 0x1424620092315000010b6b339185a5000011e461a09231500000f74618892315000008c34124622a5000013368a3092315000010b5e9d8c431500000c7461dc92315
  | 5, 17 => 0x10b461a092385000013354200c4315000013346124621d5000009d311248631500001333118492315000010b5598892315000008c311248631500000ff4618862125
  | 5, 18 => 0x14246124621250000116461889231500001469d9889231500000dc461dc9231500001337fa30c45a50000143461c8c449500000d6461246226500001335698892315
  | 5, 19 => 0xca46188b4495000013331124621c50000127311246212500001339723092315000014531124621250000133579889231500000dc4618892315000011e8caf5185a5
  | 5, 20 => 0x1337c230922f5000010782a30c44950000143461889231500000fa4618892315000014299a30b4495000011e8aa30923150000133469889231500001335723092315
  | 5, 21 => 0xe231124621250000127421889231500001338f21892315000013b7fa30c4315000013393988b4495000010b5e9889a36500001333113462085000014599988b4495
  | 5, 22 => 0x133941889231500001334998892315000014546188b44950000092461889231500001154618892385000008c311246206500001274a1889231500000a84618862125
  | 5, 23 => 0x133461949231500000a83112462125000013380230c431500001336c230c4315000013b759889231500000cc4618892315000013371188b4495000008c31124620f5
  | 5, 24 => 0x1336b2309231500000f24618892315000010b3113462145000013346188a43150000133461b89231500000ca51188923150000062248c424085000010b83a30d0495
  | 5, 25 => 0x1336b27492315000013396188923150000133311689208500001334617892315000010b5e988b64d500001336c18892315000010b81230c45a5000013354188b4495
  | 5, 26 => 0x1338f2749231500001145e988923650000133711888e3150000115461a092315000013b939889231500001459d98892315000011e6b230b449500001338f23092315
  | 5, 27 => 0x10b7caf4e44950000133461889238500001334618c92315000012783ba8c449500000f84612462125000014446188923150000101461889231500216f04618892316
  | 5, 28 => 0x147999889231500000bd4618892395000010b46188b4415000013358230e4495000013b54230c4315000013b711889231500001305ea30c45a500001334da30c4495
  | 5, 29 => 0x8c3112488315000011583a30c4495000014299bfd1831500000ea3112462125000008c33188923150000141999889231500000ff65230c431500001337c230b4495
  | 5, 30 => 0xdb461889231500001414618892315000013346188923b5000013393bfcc4315000010b461a492315000013b5418892315000014599bfcc4315000014246188b4495
  | 5, 31 => 0x10b7c2f49a3150000133461a09231500000cd461889231500001457fa30c431500001336e98892315000013375188b449500000bd51188a8495000013b3112462085
  | 5, 32 => 0xd6461dc923150000133311246c3150000134461889231500001337c9889231500001337fb88c4315000013367230c45a50000122461a09231500001075ea30ee495
  | 5, 33 => 0x14299c9c92315000008c31168924350000145a14cc9231500000cb4618892315000013b7c23092315000014599988922d500001277598892315000008c3115c92315
  | 5, 34 => 0x1334612462265000013383a30c4495000011e7fb5918315000014546188922d500001337f98862085000013a4618892315000010b6c9889231500001337faa0c4315
  | 5, 35 => 0x1237118892315000014299aa118315000014299b8892315000013b7518892315000013383a74c449500000ca54230c431500000e26518892315000012a54230c4315
  | 5, 36 => 0x12a5418892315000008c3112462275000013384a30c4495000013346188b2315000010b639889a3150000133461889e31500000ea51188923150000133311246c085
  | 5, 37 => 0xca3112462085000010b461c8d049500000e5461889231500001374618892315000014299a2492315000013346188923a500001337fbe11831500000ca5418892315
  | 5, 38 => 0x1427fa30c4315000010b4e9889238500001429992462085000010b3112462195000014299aa092315000014554230c43150000145711889231500001333112462035
  | 5, 39 => 0x133461889230500001337218892315000008c31124620350000105461889231500001337418892315000013331124621050000133712a0c431500001228aa3092315
  | 5, 40 => 0x13081230c431500000ca46188a8495000013d4618892315000008c311246e315000010b7f2f4c431500001337fba8c431500000cf461889231500216bd46188922e6
  | 5, 41 => 0xef5ea3092315000014599be092315000010b461a092315000011e6b2a118315000011e71358923150000127751c8c449500000f8652309231500000dc6523092315
  | 5, 42 => 0x11e461246212500000ea651889231500000ff4618886315000010b4e9a092315000013331124620a500000d64612462125000013393be09231500001337ea30c4495
  | 5, 43 => 0xbd4f98892315000011e6b12462085000014299ba8923150000115461c8c449500001457c23092315000008c3e12486315000011e6b2a09231500000a73112486315
  | 5, 44 => 0xf1461889231500001338f230b449500216ee5e9889231600001334ca30c449500001337c2a11831500001337c38892315000012d461889231500001336b230b4495
  | 5, 45 => 0x13b941889231500000bd31134622a500000bd461dce449500001277518892315000011a4618892315000014254230c431500001427118892315000010b6998892315
  | 5, 46 => 0x10b6b2f49a31500001334618894315000013346188b049500001337c1246208500000bd461e492315000011e5e9889a315000011e6b1246221500001337c2a092315
  | 5, 47 => 0x1423112462085000011e85af49a3150000142541889231500266ec46188923160000142449889231500000d04618892315000013283a30c4495000013350a30c4315
  | 5, 48 => 0xe231124863150000133461c8c4495000013343188923150000135461889231500001338ca30c45a500001154e988923150000133461c49231500001154618892315
  | 5, 49 => 0x1427c230923150000140999889231500000b4461dc9231500000bd4e9dc923150000142311246221500000ea31124621f500000bd461dc9231500000a84618886315
  | 5, 50 => 0x13384230c449500001337c3a8923150000133461dc9231500000bd46204ee49500000622490c6208500000a4461889231500000a83112486315000011e5523092315
  | 5, 51 => 0x133619889231500000f87ba309231500001337fb59183150000107461889212500000c746188a849500001333112462225000010b6398892365000008c31168ae495
  | 5, 52 => 0x1334e9889231500000b146188923150000122461889231500001338f3fd18315000010b46188aa495000012875988923150000133461889231500001205e98892315
  | 5, 53 => 0x13e99a30c45a5000010b5e924620b500001337a230c449500000f8461248631500000f26518892315000012285a309231500001447fa30c431500000bd46188b4185
  | 5, 54 => 0x13393b5892315000014599b5892315000010b83af4c44d5000010b51988923150000062248c42410500000d66523092315000010b4a18892385000010b5e9889c315
  | 5, 55 => 0x133461b4c449500000cf46188b449500001334518892315000013393c7892315000010b6b1889a31500001337998892315000014599c789231500001144618892385
  | 5, 56 => 0x1336b2a11831500001337135892315000011e5e9246209500000e046188923150000139999889231500001334e18892315000013b83a30c4495000013346124620c5
  | 5, 57 => 0x10b461a0b449500000da5ea309231500000fa7c23092315000010b4a1a09231500001338f2a11831500001338f38892315000010a83a30c4495000008c341247a315
  | 5, 58 => 0x1337da309231500001338f1246208500001338f2a09231500001336b1246208500252bd46188923160000114461a09231500001336b2a09231500001334619092315
  | 5, 59 => 0x11a46188b4495000013346188922f5000010b5e988a23150000133461ecc431500000df5e98892315000013388988923150000133461bcc4495000013383bfd18625
  | 5, 60 => 0x1334798892315000008c311248a3150000000999889a31400001335e9889a31500001116198892315000012775188b449500001336b1246221500001333117492315
  | 5, 61 => 0x14299c1d18495000011546188b4495000008c3918892125000010765230c449500001154a18892315000012875188923150000127461a09231500001324618892315
  | 5, 62 => 0x1214618892315000010b311246224500001334620cc4495000013393c1cc4495000014599c1cc449500001337fa30c43050000133753589231500001413112462085
  | 5, 63 => 0x10b5e9c0c449500001335523092315000010b461a89231500000bd461dcb4495000010b7b23092315000014583a30c449500001338f3a8923150000133461889a315
  | 5, 64 => 0xbd461e092315000010b5eac15072500001337198892315000011e5eaa100315000010b7fa30d031500001333113492315000013383aa118625000013383b88c4495
  | 5, 65 => 0x1334a18892315000013383aa0c44950000133739889231500001334218892315000009d3112462125000010b6b12462095000010b5e9c8c44d5000008c3112462125
  | 5, 66 => 0x1337cbe092315000013346188b449500000e57118892315000011e83b591849500000bd3112462255000013383a2cc449500001429f2309231500001338398892085
  | 5, 67 => 0x13383be11849500001335498892315000010b5e968920b50000127859a09231500000bd511dc9231500001277fba8c4315000013b461c8c449500001334e988b4495
  | 5, 68 => 0x10b5a1889a315000008c3d1889231500001157fa30c43150000133461888e3150000133582a0c431500001484618892315000010b5e9889a31500001334818892315
  | 5, 69 => 0x133511889231500001337fa30e4625000010b54230d0315000010b711a092315000014283a30c449500001115e9889a315000008c248c4240c5000013339188920d5
  | 5, 70 => 0x10b619889a315000013f99a309231500000ff5ea30ee315000013b4e98892315000013383ba8c4495000013b4618892315000013346188a03150000133859889a315
  | 5, 71 => 0x13352a30c4315000010a4618892315000010b541a0923150000146999889231500001334b98892315
  | 6, 0 => 0x1d48c31124622a600216bd55230923160024f0b6b18892316002851e85a3092316002168c31124621a600228bd461c8c4496002773346188923160017a8c3a18892316
  | 6, 1 => 0x216f85da30923160017a8c3b9247a31600216bd31134923160018e8c31124622a60017a8c311247e31600217075eaa1186260021707712f4c44960017aa84f230c4316
  | 6, 2 => 0x1337fa30c431500266ff5ea30c43160022a8c31124621460017a8c248c4541d600216e9461889231600216e35e988923160023cc746188923160023cea4618892316
  | 6, 3 => 0x216bd42188923160017aa84f188923160023d0b63a30923160017a8c311247a3160023d0b752309231600216d654230c431600216e26b188923160017a8c31168a6496
  | 6, 4 => 0x24ebd461c8c449600217075ea2cc4496001688c311247a31600217075e988920860017a9d311247a31600216bd4a1889231600217075eaa0c449600216e75e98892316
  | 6, 5 => 0x216b446188b449600216d6541889231600216bd4e988b4496002168c311246212600216f97c2f49231600216ba4618892316002668c311246204600216bd46188b4496
  | 6, 6 => 0x228b4461889231600228bd4e98892316002168c31124621e6002168c311246216600216d66723092316002668c311247a31600216d6311246208600228bd4618892316
  | 6, 7 => 0x2168c4218892316000014299a309231500285335ea3092316002670b46188b449600000ca461889231500194bd461889231600216c2461889231600216c14618892316
  | 6, 8 => 0x28b335e9889231600216bd4818892316002668c391889231600217077c2f51849600208bd46188923160026714461889231600216bd549889231600216944618892316
  | 6, 9 => 0x216bd39188920d600216d6311246221600266ff461889231600216bd461888e3160000133939889231500267275e9889231600216bd582a0c431600001459998892315
  | 6, 10 => 0x216bd511889231600216ff5ea30e4626002668c31124622060024ebd461889231600216f86b23092316000014546188923150028abd4618892316002668c3112462146
  | 6, 11 => 0x13354230c43150000133711889231500266bd54230c431600266e25e988923160024eb446188923160021707752f4c449600216bd46188a03160024ebd4e98892316
  | 6, 12 => 0x216bd4619c923160000133541889231500266bd5418892316002770b4618892316002672746188923160028b33461889231600216bd4b988923160023d195ea3092316
  | 6, 13 => 0x216bd56230923160023cbd46124622a6000011e6b230923150023cd65ea309231600216be46188923160000133311246208500266bd3112462086001acbd46124622a6
  | 6, 14 => 0x17a8c31124621f600216aa4618892316002170763a30c449600266e24618892316002170775230c449600216bd461ac9231600216bd31124620d600216bd4618892346
  | 6, 15 => 0x1f0f55ea3092316002168c391889214600216ff5a230c4316002668c311246205600216ff5ea74c43160024f0b5e9c8c449600216bd461889631600216ff5ea30c4316
  | 6, 16 => 0x2670b7fa30c431600216eb5e9889231600001337c2309231500266f85ea309231600216bd4618892366002668c311246208600266a84618892316002668c3117c92316
  | 6, 17 => 0x266ea5e98892316002170246188923160017a8c31124803160000142461889231500216d7461c8c449600284bd461889231600216bd54230e462600216e25e9c8c4496
  | 6, 18 => 0x2853346188923160024f0b5e988923160028b0b5e9889231600216bd541c8c449600216bd31124620e6002850b5ea309231600190bd461889231600001337518892315
  | 6, 19 => 0x2168c3112462146002168c311246223600216ca461889231600216bd31180923160024f0b5a1889231600216ff5ea28c431600216eb461889231600216bd3918892086
  | 6, 20 => 0x2168c311248231600267278598892316002168c31168921a60028b33859889231600260bd4618892316002169d3112462146002853385a309231600216eb4e98892316
  | 6, 21 => 0x216e25a1889231600266c7461889231600216d7461889231600266ea4618892316000008c31124863150017a8c311248631600216bd54230c431600216e25e98892316
  | 6, 22 => 0x20ebd46188922a600216c95ea30c431600216f85ea30e449600216b746188923160028b0b461889231600216bd311246209600216bd461889232600216b454230c4316
  | 6, 23 => 0x216bd45988923160017a8c31168923d600216bd3112462086002668c31124863160023d075ea30c4496002670b54230c4316002670b711889231600216bd5418892316
  | 6, 24 => 0x216ea5e9c8c449600222bd31124620860023d0b83af51849600216b43112462086001ac8c31124622a600216b4541889231600217076b2f51849600216bd31124621f6
  | 6, 25 => 0x23d0b6b23092316002670b311246208600216b546188923160024b0b5e98892316002670b541889231600216bd461d4c43160023cd6461889231600266ce4618892316
  | 6, 26 => 0x216bd54988b449600216bd4d1889231600216f85ea309231600216b4439889231600216c3311246208600216bd311246221600216bd439889231600216bd46188a8496
  | 6, 27 => 0x2670b7c230923160017aa2311247a31600216c7461c8c449600216ea461c8c449600216bd46188ac31600266f8461889231600216f85a2309231600216f85ea7492316
  | 6, 28 => 0x250bd4e98892316002668c31124622b600250bd4618892316002850b461889231600216ea5a1889231600216d15ea30923160024ebd46188b449600216ea5e98892316
  | 6, 29 => 0x1338f23092315002671e5ea30923160027714461889231600216ea4618892316002668c311689231600001336b2309231500266d65ea3092316002670b7518892316
  | 6, 30 => 0x216bd54200c431600216bd46124621d600216c74e9889231600206bd461889231600216ea4e98892316001febd461887a316002168c311246215600216c74618892316
  | 6, 31 => 0x25d0b5ea309231600217076b230c449600226bd461889231600228ff5ea30c4316002168c311248631600216ff5ea30c45a600216bd5698892316002168c3112462176
  | 6, 32 => 0x1948c311247a31600216f85ea30922f60024eff5ea30c43160023cbd461c8c449600216bd46988923160023cbd431889231600216bd31124621c60017a8c39188922a6
  | 6, 33 => 0x1c4bd311247a316002168c31168921460024f145e988923160023d0b5ea1892316002169431124621460024f0b5e988b449600216bd31134620860011862248f462146
  | 6, 34 => 0x216d85ea30c431600216e25e988b44960017a62248c454226002288c31124621460024cbd4618892316002510b5e9889231600216bd49988923160017aa8461887a316
  | 6, 35 => 0x17a8c31124622a6002671946188923160017aa8311247a31600228bd54230c431600228e25e9889231600216bd461949231600217005ea30c431600216e25d18892316
  | 6, 36 => 0x1688c31124622a60017a9d31124622a60023cbd461889231600216bd46188a4316000013383a30c449500267075ea30c449600216bd461b8923160017a62248f462086
  | 6, 37 => 0x2590b5e9889231600216bd311689208600216bd46178923160023cb4461889231600216d85e988923160023cbd4e9889231600216bd54188b449600216d65ea3092316
  | 6, 38 => 0x24e8c311246214600216b44617892316002668c31124622a600266d6461889231600228bd54188923160023d0b5ea309231600216d65a2309231600216d65ea7492316
  | 6, 39 => 0x216bd4618c92316002670b6b230923160017a8c31150923d6002671e46188923160023d0b5a230923160023d0b5ea749231600228bd311246208600216e25e9888e316
  | 6, 40 => 0x28b27461889231600216bd58230e44960023cbd4620092316001f0bd461247a316002671e85a30923160024ebd54230c43160024ee25e9889231600216bd4618892386
  | 6, 41 => 0x1d4bd311247a31600188bd461889231600228f85ea3092316001bcbd461889231600216f85ea30b449600216d4461889231600217027fa30c431600276c74618892316
  | 6, 42 => 0x260ff5ea30c431600216dd5e9889231600216ea5e988b449600216ff461886214600216bd46188923b60017a8c31124621860024f0b7faf4c431600216bb4618892316
  | 6, 43 => 0x216f95e9889231600216d6461c8c449600216ff712f4c431600216ce5ea30c45a60027d334618892316000010b461a09231500216bd461a09231600228ea5e98892316
  | 6, 44 => 0x2668c31124621b600266b046188923160018e8c311247a3160024ef85ea3092316001d48c311247a3160017a8c3115092316002668c311709231600216bd311246c316
  | 6, 45 => 0x228c746188923160028aea5e98892316002630b461889231600228ea461889231600216ff5e988620860017a8c311246226600216ea46188b449600216ff5eaa0c4316
  | 6, 46 => 0x217075a230c449600217075ea74c44960024f0b311246214600216bd461246226600217075ea30c4496000012775188923150024eea5e988923160017a9e4618892316
  | 6, 47 => 0x21ebd461889231600216d64e988923160011862248c45429600216bd461889e3160017a8c311247c31600216d6461889231600216bd311246c0860017a8c3618892316
  | 6, 48 => 0x216a8461886214600216e2311246214600216a84618862236002250b4618892316000011546188923150022abd461889231600217095ea30c4496002670b83a30c4496
  | 6, 49 => 0x266bd461c8c44960024ec746188923160024eea46188923160028aea46188923160028b27859889231600216bd46188923a600216ff7c2f51831600238bd4618892316
  | 6, 50 => 0x216bd461889230600216a8311246214600216a8311246223600216e45e9889231600216e85e9889231600216e25eaa0c43160021abd46188923160000133461c8c4495
  | 6, 51 => 0x2668c311246200600216b2461889231600216d6462009231600216fc46188923160021662248c42808600216ff752f4c43160017a8c311246228600000bd461dc92315
  | 6, 52 => 0x266bd461889231600216bd31124620a6001eabd46188923160024f0b7c2f49231600216fd5ea30c449600251145e9889231600216bf4618892316002668c3112462026
  | 6, 53 => 0x266bd4e9889231600216ff63a30c43160017a8c31168922a600216f84612462146001acbd461247a31600216ff75230c431600001334618892315002168c3418892316
  | 6, 54 => 0x216bd4ca30c449600266b8461889231600216f85eaa11831600216f8712f49231600216d65ea30b44960023cbd46188b449600266b4461889231600001334e98892315
  | 6, 55 => 0x2669d461889231600216f85eaa09231600217075e230c449600216c55ea30c449600216eb639889231600228d65ea30923160023d0b5ea30b44960021cbd4618892316
  | 6, 56 => 0x24ed65ea30923160024f0b63988923160024f0b751889231642dd8bd461889231700216bd50a30c4316002668c311246213600216bd461889431600216f85e92462086
  | 6, 57 => 0x216b4461c8c449600216ea54230c431600216ea711889231600168b3461889231600216bd461c8c449600216bd43188923160017ab34618892316002330b5ea30c45a6
  | 6, 58 => 0x216c75418892316002670b461c8c44960017a8c3b98892316002810b5e9889231600216b9461889231600216c754230c43160022b0b461889231600216e26398892316
  | 6, 59 => 0x216c6461889231600216bd311246222600216c73112462086001febd46188622a600217085ea30c449600216f8752f49231600216bd461dc923160017a8c3114c92316
  | 6, 60 => 0x23d0b7faf5183160017a98461889231600216bd461889231600216c35e988923160020ebd46188923d600216ff6b2f5183160025ebd46188923160023cff5ea30c4316
  | 6, 61 => 0x2670b461889231600216f8752309231600229075ea30c449600216b44e98892316001ac8c311247a31600222bd461889231600216b4461889231600216bd4e98892316
  | 6, 62 => 0x24ebd31124622a600216c3461889231600228d64618892316002670b4e9889231600284d65ea309231600216f45ea30c449600216f863a309231600216d646188b4496
  | 6, 63 => 0x23c8c3112462146002668c40188923160023ebd461c8c44960024f0b6b2f49231600216ea63988923160011862248c45414600216c046188923160020f045ea30c4496
  | 6, 64 => 0x23d0b46124621460017aa846188622a6001c4bd31124622a600216bd461b4c449600216bd45188923160024f075ea30c44960024f1e85af49231600216f35e98892316
  | 6, 65 => 0x23d0b712f492316000008c31124621250017a8c311246212600216d65eaa11831600216e26b2f4923160024ed646188923160023cbd54230c43160023ce25e98892316
  | 6, 66 => 0x23cbd311246208600216bd4619092316002670746188923160023cbd54188923160017a62248c454086002168c31124701460017aa831124622a60023d0b5eaa118316
  | 6, 67 => 0x23d0b5eaa092316002668c31124621260023ebd461889231600216d65e92462086000013346188b449500216b6461889231600266bd46188b449600216d65eaa092316
  | 6, 68 => 0x216ff6b230c4316002168c3112470316002668c31124622c6002230b5e98892316001c4de5e9889231600217077faf51862600216fb5ea30923160023d0b5e92462086
  | 6, 69 => 0x23cf85ea3092316000010b5e9889a31500216d65e9246221600216bd3117492316002668c311246201600216bc461889231600216bd46188922f6001f0bd46124622a6
  | 6, 70 => 0x13b461889231500276bd4618892316002668c4418892316001d4bd31124622a6002168c311246229600216bd479889231600220bd4618892316002168c3412462146
  | 6, 71 => 0x24f0b83af4c449600218bd461889231600216ff5ea30c430600216ea6b2f4923160017a8c39188923d6002668c429889231600284d646188923160023cea5e98892316
  | 6, 72 => 0x2170746188921460023d0b752f49231600216bd461889a3160017a8c3112478316002851e46188923160017aa2461889231600216bd4620cc4496
  | 7, 0 => 0x42d7a8c42988923170024ebd461889231642d7a8c311246201700228bd461889231600216bd46188b449642e0ebd46188923170017a8c311247a31642d7a8c4018892317
  | 7, 1 => 0x42d7a8c311246214742dfebd46188923170024f0b5e9889231642d7a8c391889231745216bd461889231742d7a8c311247a31742d7a8c311246204700216ff5ea30c4316
  | 7, 2 => 0x42dc4bd461889231700216bd311246208600216bd541889231649e16bd461889231700216bd54230c431600216e25e9889231642d7a8c3112462207002168c3112462146
  | 7, 3 => 0x42d8ebd461889231700216ea461889231642dd4bd461889231700216ea5e9889231600216f85ea309231642d7a8c311246208742d7aa8461889231742d7a8c3112462057
  | 7, 4 => 0x42d7a8c311689231700216d65ea30923160023cbd461889231642d7a8c31124622b70017a8c31124622a642df0bd461889231742d9cbd461889231700216c74618892316
  | 7, 5 => 0x266bd461889231647a16bd461889231742d7a8c31124622a700216d6461889231642dacbd461889231700217075ea30c449646616bd46188923170023d0b5ea3092316
  | 7, 6 => 0x216bd461889231642d7a8c311246202742d7a8c311246200700216bd461c8c449642d7a8c31124621b742d7ab0461889231742d7a8c311709231700001334618892315
  | 7, 7 => 0x42d7a8c311246213742d7a9d4618892317002670b46188923164ce16bd461889231742d7ab8461889231700216b4461889231642d7ab4461889231700216bd4e98892316
  | 8, 0 => 0x216bd4618892316
  | _, _ => 0

def careStateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => careWireDAt (fld ids 9 0) :: careStateWiresD n (ids >>> 9)
def careStateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => careWireSAt (fld ids 9 0) :: careStateWiresS n (ids >>> 9)
def careSD (s j : Nat) : List (Nat × Nat × Nat) :=
  let packed := fld (careStateB s (j / 8)) 68 (j % 8)
  careStateWiresD (packed &&& 15) (packed >>> 4)
def careSS (s j : Nat) : List Nat :=
  let packed := fld (careStateB s (j / 8)) 68 (j % 8)
  careStateWiresS (packed &&& 15) (packed >>> 4)
lemma careStateWiresD_eq (n ids : Nat) :
    careStateWiresD n ids = (careStateWiresS n ids).map (fun w => (w, projBit careR1 w, projBit careR2 w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [careStateWiresD, careStateWiresS, careWireSAt, careWireDAt_eq, ih]
lemma careSD_eq (s j : Nat) :
    careSD s j = (careSS s j).map (fun w => (w, projBit careR1 w, projBit careR2 w)) := careStateWiresD_eq _ _

def careHT : Nat → Nat → Nat
  | 3, 0 => 0xf56704aba096628e35f60c1925879972
  | 4, 0 => 0xcb19788ec9f953e0c8efb9e5c73e57a0c523d655c3825c47c2f551bdbc734df9bb7f1ef7b7355b72b38f9d75b32f6331b1d2fda7b17200fea98c9ff89c6346699abd78a69a30390e993315f498d157838d63067c8ab0411c888fb207872567757feb00d37dceb5417b87a65d79f8c4c07684707173df975672a704016cc413446cc047d26af37821687109e46718d98463d88b2f5eccd6ec596ec67e583eca8252428744518951e34f1a0fac4b43b0654601965842785da140cd9ab33fc15a553d1570503c66f6dc3a9a854635882851340614542ec01a5d28d74af024e38e601d2797ea151e7b24138eaf7d0e5f3e2b0b0bdf4b0995040004b5c96e0328b0d4
  | 4, 1 => 0xf5f489c5ee99f622ee6f8e1dedec1304edb829fde79c20a4e65f4725e378a3abe0bf887fdf9b0b41df809b02dccbcbefda207af2d4727eafd2be16ffccec53e3
  | 5, 0 => 0x167dd970166e86ab1622da1b15965584155f8cff1503642614cfd0f214b6584d145dc22f133beebc1335f7ae1334445013293fb311da5a2b11a72bb6115fa18a1158d9621152441c1135cdb21132024010a1c6d6108c59bb0e7ad1720e7706000d9897460d90c4550d7752ad0d4355e80d1561c40cef968e0c6131bf0c4d684b0bc2f9a70aef63e00abed6190abb0aa7092eff2a09078ed908c428c708b6c8590859abbb082b65f007dfb95b07cf3d1707b95287075bf2900729afbf06543558048de7f4047304a7046f6a97045eb6080453807504433e3c0428e02103fa1e1c03c3a2650328b0d403202dfc02e1380a02b5374f026d0582015e0f9c002afb8b
  | 5, 1 => 0x32e88c77324a7f153170b74030cf84db30a5b4d92fe39ea62f39c73f2f237d522ea2d6e22e483fa82de995f82d59f1ef2d1e9f4e2cbb270e2bdb20512b8870b02b46b6962aaeaf212a18038d2999a4102953aa68286f61a828493ea32812867327df339c26ca6080261607a3260e935f25c1edcc25b46568259444ad257cdfef2552b298253f5bcd252fc65423a2adba2362a5c12360945d2326f8bf2321c622230e944b22ca7c9322af77972263cb072191e93e2122dade20f96a791fd342d81f86ffff1f2079411ec1f9231de6657e1c60ca2d1bcb04a61baef8811bab2d0f1a84395018f720b6185151c41786924c176984ab1718be6f16d1c3b416ba2a29
  | 5, 2 => 0x5710624156b46e8f567d903355fb466c55a4afc9559deae25597ec8b54dba88a5358e6135331206552e3e03252085bb451a6ffd0515072335148709750d17dd250cdb260509703b0500c44964fdec8fa4f4c4c7b4f03b3144efbffc64ef023a24e2410e04e1b544b4e184e604d3c7bd04d15ff2f4c9bf5cd4c9b59ec4c49afb34b93eb324b529ad54a8212504a30229e4a25e97749bafbc2496c20504889c2e2484bc50447b9fcb2472e622d44da565e41166f3b40e4275140ab8e7b4069759c3ff7a1303f86ad093f2f0f063dfb06e83dcfe9173dcecc633c6dee4e3c4c35103af4b0cb39e25467375ada913606d42d35e214283428e9ab33d2483432f6c22e
  | 5, 3 => 0x6f5da8636f27f97a6e17c37d6e0d3a646dde6b676cd54bf36b95ef626b7f95ce6b4cfef46b041dde6a8534f96a75a6ad6a51023d6a4702796a197dd469d05e226926f20a69143b63683f5961680b11c8673002156710614e66bd456466a7e68a669c49246694811b65fcc4e2655b0e7a646411bc6460464a643d5d1c6437986062bbf658629722386223e2ab621907af61ddac5f60790cf2602fa85b5f5f780c5f1930cf5eeb9d565eca18fb5e37d7125e14a63a5db87d615d8f6d365d8c18355cfce53d5ce5c2375cb73c0f5cb001ef5caa8f935bde37295bc196d95b7ea8ba5b6fcca35b56b7e95a5f020c59f2757959a47838598ad7e557ed01e45764dcc3
  | 5, 4 => 0x87434890868cd70f866e10fd862a8c91861bde2585ea93a085468f7f853a016a84f9b8548470566183e0263582b6841582a792e082928326828eb7b4827a546d825e1238823fedfa821cdb3b8210285e820f141b81eafcfe81d140bc81257ee380d0974980a2806c803f2661801ef1c180126e527ee75cd57ebff5367d1818417ccd8eac7cc4a2237cc0d6b17b9da5b27b9176657b428e267b3ec2b47aeda68c7a94f8f67a045dcb78b8c768783c640777e096417789eb757729be4176a802ec767536a1765aadca76190dc87589544a757040497448a777742f4a0c73b3fc72739861a472a1ec577293a5477245c1a870c146bd703a02466ff8e62e6f8b32fc
  | 5, 5 => 0xa09a8528a02e998a9f61f1d39f2e51969ec9730e9e3ee0ea9e36b3c49e27493c9e124df89d9489469d84db5f9d720d909cc319659c9cdcee9c3dc6ca9c397a3b9c0dff4e9b2416859a6644339a283ff599d6be3e997f0116997b35a4996ce9a19945d59a9778d7b196c8092896c3bbc29656897e9652be0c95e4c8be955c8c1f94d344679459943c93fe361993ef4c9a939eb1b39361e716932100e792b403f892ae9d86927c221c918407fc91012da390c4bcc5909251f490071dfc8ffdcc6e8ff5d5ed8faaf5238f7415098d3e102a8d3a44b88cf418e68c4ebcb38c4557028983d187892d39b5891b11a488bf292f88b4a29b87fea62587edf59a875c723b
  | 5, 6 => 0xc20a1cb1c1dab516c1bbaa06c0d80f23c0b40dc8c0a13eb4c07be64abefcab3cbebbc391be5f9ab8bca6df20bc850163bb0d18f1bb036248bad864cfba73d1c5b9e7af87b914f03ab83de349b7157f4bb6f690feb6763f61b58f26a0b4ff5320b3a0aeabb39e4d2eb2e482c5b2a231e3b24bfe88b228a320b2139611b1e79080b1416914b0ae652ab085e651af26e31caf0e9a1fae8847b1ae2e86cdada0bbeead972edfad901d74ad81cc1fad5788c7ad24d4d0ace27700abec417bab6157d2aa8b2fa3a9e5d75fa98c4b63a92783dca87eb7b6a7efabb5a79a6b42a60950bea605854ca4df6f02a493c272a40e8ab2a2f8a19ba2b08c43a16e178ea12373a9
  | 5, 7 => 0xe338ea74e32e76bbe1c07e06e1872abee16774fde0e7e870de610e9bde451944ddf6edb3ddbd459bdd74d5e8dd5054b9dcf42be0dc59623edc44c309dbbb0460db1a076ddb103325da01f453d997f370d9189ab1d8219909d667acf8d645ec0ad5d36d6dd53cdcdcd4727eafd469fbd7d44f996fd414ff71d40ae5b3d405820dd3c37dbad37c7fe3d372fbe8d35d3d68d1a1a509d12e09dccf8ac370cf1a7779cebad60dce42feb7cd0a6b62cc26b325cb9984b0cb8d827ecaee1fd0ca49df54c960d485c8f45ce0c7e40ccdc7693c11c7277aa5c723af33c6eb7643c6466e53c50b2f13c50763a1c4531a6ac3c25af1c3291daec2f485a0c2b97706c20ed80f
  | 5, 8 => 0xff1b8c8ffefaae89fef26836fe7948f2fe4942c4fdbf07d6fd258667fcb084f0fc55c7e6fad95431fac8af4cfaad4d57fa9d7843f9f74240f9f588b0f90f7779f90bac07f7d46660f7782c32f7315d60f71f5966f6a7f787f68e820bf6398d57f53281fdf4f13a5cf4ce764cf4b61766f4b3575ff4abeec8f3fcd67cf301afb6f2c00bf7ef7e1771ef3e59a3ed94883ded8d6e27eced52a5ec00558debb47239eb937574eb3f9b2beb128ddceae746faeabb444dea08bd19e982b0f8e9722f6ee9575032e8c333fce86a4b44e781f057e7361b62e6a85c2ee5676f0ce56606b1e517ce50e48a2eb7e4280a01e39fc03be39bf4c9
  | 6, 0 => 0x1376065613293fb31320bcdb122b4f2111a72bb6119ea8de112a9d6611072ac610627c5e0ffdb4d70fe8b4d70fb8ba420fab203d0f10e8ef0f0c0bac0e709c3d0e35ce650dd378570dd106de0d6114f60d30eb5c0d2544a30c5b8c710c43ee440c169fa80b5626930b1b68330afedd040ab6a0ac0a4c55d009c649af09b5c825099ae8e9095a4dfe092c07d809298812087fc4bf07f0879a07ecbc280759b1600729afbf07212ce706c3db7705e0a6dc05d410bd05a99f68059a4b3c04ee082304df72300497be20046ba2b8042184d303f24f5203e358f203df8d8003775d41037541ba03720f7201a11c1801871a5e01663ab8013c752e00a78d510051eb87
  | 6, 1 => 0x2af7acbe2acbf25f295f28972956310e28fa6110286efea7279f8b47276d4876271232772613cf4225a44d6e257dc7a424f80a5524d180ab2497192c2486d6f3246c78d8243db00b23a2adba239a2ae2230e6dbd22ca7c9322c1f9bb2221647921a1a8532191e93e2189666620f3a8e01f3227941ed5febb1e8cdb7b1e528eb81baef8811bab2d0f1ba675a91ba2aa371b3ca6d81b1cece81af0e60e1ad7df511a3adaf71a39216719f86a77194ac6b718fcb62718f720b618ee9dde17b3fddf1762f21d16f03e3a16df3b1115761ab4155f8cff15570a271534d3131503642614fae14e14f6f01614f2c42f14ef877f14e667461457fd1a14406f331427733d
  | 6, 2 => 0x43655ed94316478e430e154a424ccc53422ebc0a41d9f21541d626a341d581f540b5f5a140a860343fca98b63fb55d503f221a4a3f0591da3e29fe353de471593de0a5e73d676a253d1179d63cbb270c3c6dee4e3c656b763bf291383beec5c63bc590b83b8a86933b52fa343b2e5dba3a0628f2398d320839543947389b654c3800196e37dfafc337d2254a37ad1d62379505d737155c6b370e4cb235d9ee3b35c27cab35a325b63546fcdd34a15ae6337f8773336cd86a3334a7bc32e88c7732e0099f318a62af3116e8ae2fe39ea62fdd52c72fdb1bce2ebe6a292eba9eb72d54a9532d332f452cbb270e2cb2a4362ca4ca762c9d17282b6483d32b110923
  | 6, 3 => 0x6a73bb556645ece463eb4f596386b5eb6298e7e2615a07f260ad0e535fd130815fca45c05f72a7bd5f409e4e5f2d91695e945b355e3fa1c05dfe2d295db385b45d8c18355d83955d5d0d16555d07429b5c13aaba5b6fcca35b6749cb5913860b58d138655892872857441fcb560e983a551e054f546c826253378633532c252e52e620a2510d3441507f5ea54fd31b8c4f6716094f5464064ef09fe64e8bd85f4e2d2eaf4d6238054cfebfc54c4d7c654c1705ba4af247d84a5b9c4449dd3cc749cda74e48f5762748d03875488cd75a47bce2d246522c16463beab24602ce1c45f7fe1f45d02a1645c078a644fff56b44c3244943c7621643a42d14436a9176
  | 6, 4 => 0x82677b62819ac63780af96118025552d7fc1910d7f5cc9867f2782bf7f0db1b27ef3b15d7ee57ac77eac8ec47e09099b7deeef6a7dcfb0ec7da5457b7d407df47d295aee7cfad4c67cf39aa67c2fd4717c21cfe07bcb0cea7bc241717bb3655a7ab70e087a5246817a3df4507a360e307a045dcb79fbdaf379e810ef79e06e9478c52de778c16d7178a7db3f780bfead7808333b7753faf876c128ea76bcdba1763edf2375db85427539df87741986e373c8cda4739c7eca7374b91c72c4ea8272c11f1071ecd8ea71bc932b704fdd4d6ff540766f8fe5326f3f987d6ed272b86ea47e946e67a9976e60e0656d09cd416cdef2a36cbe20b16b96338c6b9106d8
  | 6, 5 => 0xa01c60bf9fe23dc49fa967dc9f2af58c9e998dec9e55252a9d5bb0f89cadfc1d9c39d6a39bd50f1c9b4c105c9ad891ad9a47f6829a283ff59a1fbd1d99dbfad199ccf32999c3944499338fd29920b01098242ef89746d51196f4021796eb9ba395e1f7be952872819485defe93f257b493d99be593c598609354855d92e5850e92895a5f9120fe1b9104df74907d9afd8fb07b5d8f7415098f6b92318f4592a38f1c42a08e22041e8d18e4aa8d16331c8ac8cdb08ac81ef68ab93f648a37e13389fe7e788997d25389182d3a878a443686eb7f4186b41fd586a07c5d861c83608615b239859ea731854f067583d1190f83b711c982e6292782e25db582dabaef
  | 6, 6 => 0xbd734940bc7d12f2bc0dc447bbbbbf03b88f8631b7ccd2cfb7bc7068b70a9ae1b7075479b6a5d78fb69a2235b69656c3b5a024d6b42ab3ccb3fcf35ab3a0aeabb3982bd3b2c99f62b2b1ed63b2a7aa6bb285bea4b21d5c49b2139611b20d5201b20b1339b108557cb0501bc1b04ab6b3b0416525afb5ec3facd60da5abaca04eaa8d8907a9ec9a02a966374fa9305ea0a8b6fff0a8423edca82e963ba79a6b42a786e147a77e6c9ba75e02f0a6d06fc6a65f76dca58a2836a5882cbda4df6f02a4d6ec2aa4a71da3a3fada8aa39eb1b1a26e1138a22e95b5a214d973a2143947a19b7bdea197b06ca17b1233a1560cc6a12373a9a11af0d1a082bf18a02f575f
  | 6, 7 => 0xdfe6def6dfbde52edfb4d27ddeff5c48de887c1ade6e188ddd4b4353dcd72f00dc1124d5db601f38da6e929fd9cba83fd9375260d8817c00d85b16b1d841e4a6d83e8fa5d7aed398d66163f7d5d62783d5277e74d5194394d4490ee9d3e44762d2e5ca9ad2e355e8d2572ec8d18501cbd11a4fccd0c97f08cf868c20cf540dfecee95baececbe068ce6a6c36cddb4795cddac796cdd3b62bcdc564d6cd6cf1e4cd31d8e1cb0a6896ca33a83aca297016c9fadbd3c74ee824c74e6d3dc74b1cb2c714e7dac6a2a50bc69ed999c5712531c52307b9c4d75b29c37f4510c33c3a52c2a6fd49c0ff7ca2c0533989bf71ea4dbe6ae1f3be3d68bebdd821fdbdb5a647
  | 6, 8 => 0xfd93ed70fd32f802fc9cfaf5fc885bc0fbf56103fbebfd66fbd91230fb12eab6fac8af4cfac02c74f9fee6c2f99a244df93b68bdf6170624f5ccb312f5147cd7f4e5854df4b61766f44e7e6af4491ac4f42d254af41cfc8df3c0189af36cbee4f36b3ed8f2f692f4f23078daf171a293f121db34ef5e1030eefe6ec4ee86976eed4e0419ed14f967ece8f98cec6a4bdcec00558debfcfb5cebf7d2b5eb31b887eaf4dad2ea8d780bea17b2f8e9bc477de97c1469e883a595e8438114e76b135ce76747eae7361b62e72d988ae54ec7cae54afc58e548bd19e3d956c0e3d58b4ee3789b92e2609057e25cc4e5e24db568e1ff42bde13b8e71e11ba7dae0e4d76b
  | 6, 9 => 0xfff0e128fea4a752fe88b1fbfe2470ebfdf55dc2fde27bf8fdb86e9f
  | 7, 0 => 0xde810175ddb6e1f7d83e8fa5d8360ccdd6e97046d4490ee9d4408c11d3e44762d2572ec8cbf03905cad121bec52307b9b6259075b56c0b38b3981e14b2139611b20b1339a068ede49ef0277b9e55252a9e4ca2529a47f682990506287dcfb0ec7c5743717bb3655a7a3df45078d61fdf78c52de76f97fcbd664666d35db385b45dab02dc5d07429b5cfebfc3532c252e4cfebfc54ce0afdf4ba81c8a4999c9c545c1605b430e154a41d581f53f75c04b3bf291383beec5c63a3c032e3800196e37f796963722d3c835a325b635365ce6349b95d12f5481a62c9f2528276d48761c2f961d194ac6b71470be010e709c3d0c43ee440a5b4baf0929881200017de5
  | 8, 0 => 0xd2572ec8
  | _, _ => 0

def careHtAt (s i : Nat) : Nat := fld (careHT s (i / 64)) 32 (i % 64)
def careIdxH (s h : Nat) : Nat := bsr (careHtAt s) h 11 0 (careNN s)
def careIdx (s : Nat) (zs : List Nat) : Nat := careIdxH s (hk 0 zs)
def careZ (s : Nat) := bar careDom (careGoal &&& careDom) careSepPairs careR1 careR2 careMP careSD careSS careNN careHtAt careIdxH id 0 [] (fun _ _ _ => false) s

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ3_0 : span (careZ 3) 4 0 = true := by decide +kernel

lemma careZ3 : ∀ i, 0 ≤ i → i < 4 → careZ 3 i = true := by

  exact span_ok careZ3_0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ4_0 : span (careZ 4) 16 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ4_16 : span (careZ 4) 16 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ4_32 : span (careZ 4) 16 32 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ4_48 : span (careZ 4) 16 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ4_64 : span (careZ 4) 16 64 = true := by decide +kernel

lemma careZ4 : ∀ i, 0 ≤ i → i < 80 → careZ 4 i = true := by

  refine range_split (P := fun i => careZ 4 i = true) (lo := 0) (mid := 32) (hi := 80) ?_ ?_

  ·

    refine range_split (P := fun i => careZ 4 i = true) (lo := 0) (mid := 16) (hi := 32) ?_ ?_

    ·

      exact span_ok careZ4_0

    ·

      exact span_ok careZ4_16

  ·

    refine range_split (P := fun i => careZ 4 i = true) (lo := 32) (mid := 48) (hi := 80) ?_ ?_

    ·

      exact span_ok careZ4_32

    ·

      refine range_split (P := fun i => careZ 4 i = true) (lo := 48) (mid := 64) (hi := 80) ?_ ?_

      ·

        exact span_ok careZ4_48

      ·

        exact span_ok careZ4_64

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ5_0 : span (careZ 5) 16 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ5_16 : span (careZ 5) 16 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ5_32 : span (careZ 5) 16 32 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ5_48 : span (careZ 5) 16 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ5_64 : span (careZ 5) 16 64 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ5_80 : span (careZ 5) 16 80 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ5_96 : span (careZ 5) 16 96 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ5_112 : span (careZ 5) 16 112 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ5_128 : span (careZ 5) 16 128 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ5_144 : span (careZ 5) 16 144 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ5_160 : span (careZ 5) 16 160 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ5_176 : span (careZ 5) 16 176 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ5_192 : span (careZ 5) 16 192 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ5_208 : span (careZ 5) 16 208 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ5_224 : span (careZ 5) 16 224 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ5_240 : span (careZ 5) 16 240 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ5_256 : span (careZ 5) 16 256 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ5_272 : span (careZ 5) 16 272 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ5_288 : span (careZ 5) 16 288 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ5_304 : span (careZ 5) 16 304 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ5_320 : span (careZ 5) 16 320 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ5_336 : span (careZ 5) 16 336 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ5_352 : span (careZ 5) 16 352 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ5_368 : span (careZ 5) 16 368 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ5_384 : span (careZ 5) 16 384 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ5_400 : span (careZ 5) 16 400 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ5_416 : span (careZ 5) 16 416 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ5_432 : span (careZ 5) 16 432 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ5_448 : span (careZ 5) 16 448 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ5_464 : span (careZ 5) 16 464 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ5_480 : span (careZ 5) 16 480 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ5_496 : span (careZ 5) 16 496 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ5_512 : span (careZ 5) 16 512 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ5_528 : span (careZ 5) 16 528 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ5_544 : span (careZ 5) 16 544 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ5_560 : span (careZ 5) 13 560 = true := by decide +kernel

lemma careZ5 : ∀ i, 0 ≤ i → i < 573 → careZ 5 i = true := by

  refine range_split (P := fun i => careZ 5 i = true) (lo := 0) (mid := 288) (hi := 573) ?_ ?_

  ·

    refine range_split (P := fun i => careZ 5 i = true) (lo := 0) (mid := 144) (hi := 288) ?_ ?_

    ·

      refine range_split (P := fun i => careZ 5 i = true) (lo := 0) (mid := 64) (hi := 144) ?_ ?_

      ·

        refine range_split (P := fun i => careZ 5 i = true) (lo := 0) (mid := 32) (hi := 64) ?_ ?_

        ·

          refine range_split (P := fun i => careZ 5 i = true) (lo := 0) (mid := 16) (hi := 32) ?_ ?_

          ·

            exact span_ok careZ5_0

          ·

            exact span_ok careZ5_16

        ·

          refine range_split (P := fun i => careZ 5 i = true) (lo := 32) (mid := 48) (hi := 64) ?_ ?_

          ·

            exact span_ok careZ5_32

          ·

            exact span_ok careZ5_48

      ·

        refine range_split (P := fun i => careZ 5 i = true) (lo := 64) (mid := 96) (hi := 144) ?_ ?_

        ·

          refine range_split (P := fun i => careZ 5 i = true) (lo := 64) (mid := 80) (hi := 96) ?_ ?_

          ·

            exact span_ok careZ5_64

          ·

            exact span_ok careZ5_80

        ·

          refine range_split (P := fun i => careZ 5 i = true) (lo := 96) (mid := 112) (hi := 144) ?_ ?_

          ·

            exact span_ok careZ5_96

          ·

            refine range_split (P := fun i => careZ 5 i = true) (lo := 112) (mid := 128) (hi := 144) ?_ ?_

            ·

              exact span_ok careZ5_112

            ·

              exact span_ok careZ5_128

    ·

      refine range_split (P := fun i => careZ 5 i = true) (lo := 144) (mid := 208) (hi := 288) ?_ ?_

      ·

        refine range_split (P := fun i => careZ 5 i = true) (lo := 144) (mid := 176) (hi := 208) ?_ ?_

        ·

          refine range_split (P := fun i => careZ 5 i = true) (lo := 144) (mid := 160) (hi := 176) ?_ ?_

          ·

            exact span_ok careZ5_144

          ·

            exact span_ok careZ5_160

        ·

          refine range_split (P := fun i => careZ 5 i = true) (lo := 176) (mid := 192) (hi := 208) ?_ ?_

          ·

            exact span_ok careZ5_176

          ·

            exact span_ok careZ5_192

      ·

        refine range_split (P := fun i => careZ 5 i = true) (lo := 208) (mid := 240) (hi := 288) ?_ ?_

        ·

          refine range_split (P := fun i => careZ 5 i = true) (lo := 208) (mid := 224) (hi := 240) ?_ ?_

          ·

            exact span_ok careZ5_208

          ·

            exact span_ok careZ5_224

        ·

          refine range_split (P := fun i => careZ 5 i = true) (lo := 240) (mid := 256) (hi := 288) ?_ ?_

          ·

            exact span_ok careZ5_240

          ·

            refine range_split (P := fun i => careZ 5 i = true) (lo := 256) (mid := 272) (hi := 288) ?_ ?_

            ·

              exact span_ok careZ5_256

            ·

              exact span_ok careZ5_272

  ·

    refine range_split (P := fun i => careZ 5 i = true) (lo := 288) (mid := 432) (hi := 573) ?_ ?_

    ·

      refine range_split (P := fun i => careZ 5 i = true) (lo := 288) (mid := 352) (hi := 432) ?_ ?_

      ·

        refine range_split (P := fun i => careZ 5 i = true) (lo := 288) (mid := 320) (hi := 352) ?_ ?_

        ·

          refine range_split (P := fun i => careZ 5 i = true) (lo := 288) (mid := 304) (hi := 320) ?_ ?_

          ·

            exact span_ok careZ5_288

          ·

            exact span_ok careZ5_304

        ·

          refine range_split (P := fun i => careZ 5 i = true) (lo := 320) (mid := 336) (hi := 352) ?_ ?_

          ·

            exact span_ok careZ5_320

          ·

            exact span_ok careZ5_336

      ·

        refine range_split (P := fun i => careZ 5 i = true) (lo := 352) (mid := 384) (hi := 432) ?_ ?_

        ·

          refine range_split (P := fun i => careZ 5 i = true) (lo := 352) (mid := 368) (hi := 384) ?_ ?_

          ·

            exact span_ok careZ5_352

          ·

            exact span_ok careZ5_368

        ·

          refine range_split (P := fun i => careZ 5 i = true) (lo := 384) (mid := 400) (hi := 432) ?_ ?_

          ·

            exact span_ok careZ5_384

          ·

            refine range_split (P := fun i => careZ 5 i = true) (lo := 400) (mid := 416) (hi := 432) ?_ ?_

            ·

              exact span_ok careZ5_400

            ·

              exact span_ok careZ5_416

    ·

      refine range_split (P := fun i => careZ 5 i = true) (lo := 432) (mid := 496) (hi := 573) ?_ ?_

      ·

        refine range_split (P := fun i => careZ 5 i = true) (lo := 432) (mid := 464) (hi := 496) ?_ ?_

        ·

          refine range_split (P := fun i => careZ 5 i = true) (lo := 432) (mid := 448) (hi := 464) ?_ ?_

          ·

            exact span_ok careZ5_432

          ·

            exact span_ok careZ5_448

        ·

          refine range_split (P := fun i => careZ 5 i = true) (lo := 464) (mid := 480) (hi := 496) ?_ ?_

          ·

            exact span_ok careZ5_464

          ·

            exact span_ok careZ5_480

      ·

        refine range_split (P := fun i => careZ 5 i = true) (lo := 496) (mid := 528) (hi := 573) ?_ ?_

        ·

          refine range_split (P := fun i => careZ 5 i = true) (lo := 496) (mid := 512) (hi := 528) ?_ ?_

          ·

            exact span_ok careZ5_496

          ·

            exact span_ok careZ5_512

        ·

          refine range_split (P := fun i => careZ 5 i = true) (lo := 528) (mid := 544) (hi := 573) ?_ ?_

          ·

            exact span_ok careZ5_528

          ·

            refine range_split (P := fun i => careZ 5 i = true) (lo := 544) (mid := 560) (hi := 573) ?_ ?_

            ·

              exact span_ok careZ5_544

            ·

              exact span_ok careZ5_560

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ6_0 : span (careZ 6) 16 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ6_16 : span (careZ 6) 16 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ6_32 : span (careZ 6) 16 32 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ6_48 : span (careZ 6) 16 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ6_64 : span (careZ 6) 16 64 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ6_80 : span (careZ 6) 16 80 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ6_96 : span (careZ 6) 16 96 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ6_112 : span (careZ 6) 16 112 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ6_128 : span (careZ 6) 16 128 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ6_144 : span (careZ 6) 16 144 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ6_160 : span (careZ 6) 16 160 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ6_176 : span (careZ 6) 16 176 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ6_192 : span (careZ 6) 16 192 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ6_208 : span (careZ 6) 16 208 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ6_224 : span (careZ 6) 16 224 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ6_240 : span (careZ 6) 16 240 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ6_256 : span (careZ 6) 16 256 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ6_272 : span (careZ 6) 16 272 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ6_288 : span (careZ 6) 16 288 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ6_304 : span (careZ 6) 16 304 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ6_320 : span (careZ 6) 16 320 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ6_336 : span (careZ 6) 16 336 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ6_352 : span (careZ 6) 16 352 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ6_368 : span (careZ 6) 16 368 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ6_384 : span (careZ 6) 16 384 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ6_400 : span (careZ 6) 16 400 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ6_416 : span (careZ 6) 16 416 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ6_432 : span (careZ 6) 16 432 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ6_448 : span (careZ 6) 16 448 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ6_464 : span (careZ 6) 16 464 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ6_480 : span (careZ 6) 16 480 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ6_496 : span (careZ 6) 16 496 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ6_512 : span (careZ 6) 16 512 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ6_528 : span (careZ 6) 16 528 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ6_544 : span (careZ 6) 16 544 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ6_560 : span (careZ 6) 16 560 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ6_576 : span (careZ 6) 7 576 = true := by decide +kernel

lemma careZ6 : ∀ i, 0 ≤ i → i < 583 → careZ 6 i = true := by

  refine range_split (P := fun i => careZ 6 i = true) (lo := 0) (mid := 288) (hi := 583) ?_ ?_

  ·

    refine range_split (P := fun i => careZ 6 i = true) (lo := 0) (mid := 144) (hi := 288) ?_ ?_

    ·

      refine range_split (P := fun i => careZ 6 i = true) (lo := 0) (mid := 64) (hi := 144) ?_ ?_

      ·

        refine range_split (P := fun i => careZ 6 i = true) (lo := 0) (mid := 32) (hi := 64) ?_ ?_

        ·

          refine range_split (P := fun i => careZ 6 i = true) (lo := 0) (mid := 16) (hi := 32) ?_ ?_

          ·

            exact span_ok careZ6_0

          ·

            exact span_ok careZ6_16

        ·

          refine range_split (P := fun i => careZ 6 i = true) (lo := 32) (mid := 48) (hi := 64) ?_ ?_

          ·

            exact span_ok careZ6_32

          ·

            exact span_ok careZ6_48

      ·

        refine range_split (P := fun i => careZ 6 i = true) (lo := 64) (mid := 96) (hi := 144) ?_ ?_

        ·

          refine range_split (P := fun i => careZ 6 i = true) (lo := 64) (mid := 80) (hi := 96) ?_ ?_

          ·

            exact span_ok careZ6_64

          ·

            exact span_ok careZ6_80

        ·

          refine range_split (P := fun i => careZ 6 i = true) (lo := 96) (mid := 112) (hi := 144) ?_ ?_

          ·

            exact span_ok careZ6_96

          ·

            refine range_split (P := fun i => careZ 6 i = true) (lo := 112) (mid := 128) (hi := 144) ?_ ?_

            ·

              exact span_ok careZ6_112

            ·

              exact span_ok careZ6_128

    ·

      refine range_split (P := fun i => careZ 6 i = true) (lo := 144) (mid := 208) (hi := 288) ?_ ?_

      ·

        refine range_split (P := fun i => careZ 6 i = true) (lo := 144) (mid := 176) (hi := 208) ?_ ?_

        ·

          refine range_split (P := fun i => careZ 6 i = true) (lo := 144) (mid := 160) (hi := 176) ?_ ?_

          ·

            exact span_ok careZ6_144

          ·

            exact span_ok careZ6_160

        ·

          refine range_split (P := fun i => careZ 6 i = true) (lo := 176) (mid := 192) (hi := 208) ?_ ?_

          ·

            exact span_ok careZ6_176

          ·

            exact span_ok careZ6_192

      ·

        refine range_split (P := fun i => careZ 6 i = true) (lo := 208) (mid := 240) (hi := 288) ?_ ?_

        ·

          refine range_split (P := fun i => careZ 6 i = true) (lo := 208) (mid := 224) (hi := 240) ?_ ?_

          ·

            exact span_ok careZ6_208

          ·

            exact span_ok careZ6_224

        ·

          refine range_split (P := fun i => careZ 6 i = true) (lo := 240) (mid := 256) (hi := 288) ?_ ?_

          ·

            exact span_ok careZ6_240

          ·

            refine range_split (P := fun i => careZ 6 i = true) (lo := 256) (mid := 272) (hi := 288) ?_ ?_

            ·

              exact span_ok careZ6_256

            ·

              exact span_ok careZ6_272

  ·

    refine range_split (P := fun i => careZ 6 i = true) (lo := 288) (mid := 432) (hi := 583) ?_ ?_

    ·

      refine range_split (P := fun i => careZ 6 i = true) (lo := 288) (mid := 352) (hi := 432) ?_ ?_

      ·

        refine range_split (P := fun i => careZ 6 i = true) (lo := 288) (mid := 320) (hi := 352) ?_ ?_

        ·

          refine range_split (P := fun i => careZ 6 i = true) (lo := 288) (mid := 304) (hi := 320) ?_ ?_

          ·

            exact span_ok careZ6_288

          ·

            exact span_ok careZ6_304

        ·

          refine range_split (P := fun i => careZ 6 i = true) (lo := 320) (mid := 336) (hi := 352) ?_ ?_

          ·

            exact span_ok careZ6_320

          ·

            exact span_ok careZ6_336

      ·

        refine range_split (P := fun i => careZ 6 i = true) (lo := 352) (mid := 384) (hi := 432) ?_ ?_

        ·

          refine range_split (P := fun i => careZ 6 i = true) (lo := 352) (mid := 368) (hi := 384) ?_ ?_

          ·

            exact span_ok careZ6_352

          ·

            exact span_ok careZ6_368

        ·

          refine range_split (P := fun i => careZ 6 i = true) (lo := 384) (mid := 400) (hi := 432) ?_ ?_

          ·

            exact span_ok careZ6_384

          ·

            refine range_split (P := fun i => careZ 6 i = true) (lo := 400) (mid := 416) (hi := 432) ?_ ?_

            ·

              exact span_ok careZ6_400

            ·

              exact span_ok careZ6_416

    ·

      refine range_split (P := fun i => careZ 6 i = true) (lo := 432) (mid := 512) (hi := 583) ?_ ?_

      ·

        refine range_split (P := fun i => careZ 6 i = true) (lo := 432) (mid := 464) (hi := 512) ?_ ?_

        ·

          refine range_split (P := fun i => careZ 6 i = true) (lo := 432) (mid := 448) (hi := 464) ?_ ?_

          ·

            exact span_ok careZ6_432

          ·

            exact span_ok careZ6_448

        ·

          refine range_split (P := fun i => careZ 6 i = true) (lo := 464) (mid := 480) (hi := 512) ?_ ?_

          ·

            exact span_ok careZ6_464

          ·

            refine range_split (P := fun i => careZ 6 i = true) (lo := 480) (mid := 496) (hi := 512) ?_ ?_

            ·

              exact span_ok careZ6_480

            ·

              exact span_ok careZ6_496

      ·

        refine range_split (P := fun i => careZ 6 i = true) (lo := 512) (mid := 544) (hi := 583) ?_ ?_

        ·

          refine range_split (P := fun i => careZ 6 i = true) (lo := 512) (mid := 528) (hi := 544) ?_ ?_

          ·

            exact span_ok careZ6_512

          ·

            exact span_ok careZ6_528

        ·

          refine range_split (P := fun i => careZ 6 i = true) (lo := 544) (mid := 560) (hi := 583) ?_ ?_

          ·

            exact span_ok careZ6_544

          ·

            refine range_split (P := fun i => careZ 6 i = true) (lo := 560) (mid := 576) (hi := 583) ?_ ?_

            ·

              exact span_ok careZ6_560

            ·

              exact span_ok careZ6_576

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ7_0 : span (careZ 7) 16 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ7_16 : span (careZ 7) 16 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ7_32 : span (careZ 7) 16 32 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ7_48 : span (careZ 7) 16 48 = true := by decide +kernel

lemma careZ7 : ∀ i, 0 ≤ i → i < 64 → careZ 7 i = true := by

  refine range_split (P := fun i => careZ 7 i = true) (lo := 0) (mid := 32) (hi := 64) ?_ ?_

  ·

    refine range_split (P := fun i => careZ 7 i = true) (lo := 0) (mid := 16) (hi := 32) ?_ ?_

    ·

      exact span_ok careZ7_0

    ·

      exact span_ok careZ7_16

  ·

    refine range_split (P := fun i => careZ 7 i = true) (lo := 32) (mid := 48) (hi := 64) ?_ ?_

    ·

      exact span_ok careZ7_32

    ·

      exact span_ok careZ7_48

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careZ8_0 : span (careZ 8) 1 0 = true := by decide +kernel

lemma careZ8 : ∀ i, 0 ≤ i → i < 1 → careZ 8 i = true := by

  exact span_ok careZ8_0

lemma careChecked (s : Nat) (hs : s ≤ 8) : ∀ i < careNN s, careZ s i = true := by
  intro i hi
  interval_cases s

  · simp [careNN] at hi

  · simp [careNN] at hi

  · simp [careNN] at hi

  · exact careZ3 i (by omega) (by simpa [careNN] using hi)

  · exact careZ4 i (by omega) (by simpa [careNN] using hi)

  · exact careZ5 i (by omega) (by simpa [careNN] using hi)

  · exact careZ6 i (by omega) (by simpa [careNN] using hi)

  · exact careZ7 i (by omega) (by simpa [careNN] using hi)

  · exact careZ8 i (by omega) (by simpa [careNN] using hi)

def careRootG (s : Nat) : Bool := !coversP careSepPairs s careRoots || found careSS careNN careIdx s careRoots

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careRootChecked : span careRootG 4 5 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma careProperFail : ∀ zs ∈ careRoots.sublists, zs ≠ careRoots → unorientedCov careSepPairs zs = false := by decide +kernel

lemma careNoRunFull (s : Nat) (hs : s ≤ 8) (h : RunD careDom (careGoal &&& careDom) s careRoots) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok careRootChecked s hmin (by omega)
  unfold careRootG at hr
  rw [coversP_ok (by decide +kernel) careSepPairs (by decide +kernel) h, Bool.not_true, Bool.false_or] at hr
  rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hr
  exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) careSD_eq (by decide +kernel) (fun h => h) (by simp) careChecked s hs _ hr.1 (Run.perm hr.2 h)
lemma careLower : Lower careDom careRoots careGoal 9 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst careDom careGoal := by
    have h0 : isConstB careDom careGoal = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hroots : careRoots.map (· &&& careDom) = careRoots := by decide +kernel
  rw [hroots] at hws_sub
  have hperm_sub : ∃ zs, zs.Sublist careRoots ∧ ws.Perm zs := by
    refine ⟨careRoots.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : careRoots.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub
  have hrun' := Run.perm hpz hrun
  by_cases heq : zs = careRoots
  · subst heq; exact careNoRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) careSepPairs (by decide +kernel) hrun'
    have hbad := careProperFail zs (List.mem_sublists.2 hsub) heq
    rw [hcov] at hbad; contradiction

end PEqualNP.Outside.L_meta_23671_aux

theorem PEqualNP.Outside.L_meta_23671 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (36153 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) :=
  PEqualNP.Outside.L_meta_23671_aux.care_lower_to_circuit
    PEqualNP.Outside.L_meta_23671_aux.careLower
