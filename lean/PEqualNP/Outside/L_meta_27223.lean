import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
import Mathlib

namespace PEqualNP.Outside.L_meta_27223_aux

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

section RunCore
variable {d y : Nat}

lemma Run.done : RunD d y 0 [y] := fun _ dn _ _ _ => dn
lemma Run.perm {s xs zs} (p : List.Perm xs zs) (h : RunD d y s xs) :
    RunD d y s zs := fun P dn q u b => q p (h P dn q u b)
lemma Run.one {s a r} (save : Bool)
    (h0 : negD d a ≠ 0) (hd : negD d a ≠ d) (hm : negD d a ∉ (a :: r))
    (h : RunD d y s (negD d a :: kept save a r)) :
    RunD d y (s + 1) (a :: r) := fun P dn q u b => u save h0 hd hm (h P dn q u b)
lemma Run.two {s a b r} (c ka kb : Bool)
    (h0 : (if c then andD d a b else orD d a b) ≠ 0)
    (hd : (if c then andD d a b else orD d a b) ≠ d)
    (hm : (if c then andD d a b else orD d a b) ∉ (a :: b :: r))
    (h : RunD d y s ((if c then andD d a b else orD d a b) :: kept ka a (kept kb b r))) :
    RunD d y (s + 1) (a :: b :: r) := fun P dn q u v => v c ka kb h0 hd hm (h P dn q u v)

lemma Run.fold {P : ∀ t ws, RunD d y t ws → Prop}
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
end RunCore

lemma kept_map {α β : Type} (e : α → β) (b : Bool) (x : α) (xs : List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e) := by cases b <;> simp [kept]

lemma mem_kept {α : Type} (b : Bool) (x a : α) (xs : List α) :
    a ∈ kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs := by cases b <;> simp [kept]

lemma nodup_kept {α : Type} (b : Bool) (x : α) (xs : List α) (h : xs.Nodup) (hx : x ∉ xs) :
    (kept b x xs).Nodup := by
  cases b
  · simpa [kept] using h
  · simpa [kept] using And.intro hx h

lemma keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys) := by cases b <;> simpa [kept] using p

lemma run_len {d y s xs} (h : RunD d y s xs) :
    xs.length ≤ s + 1 := by
  induction h using Run.fold with
  | done => simp
  | perm hp _ ih => rwa [← hp.length_eq]
  | one save _ _ _ _ ih => cases save <;> simp_all [kept] <;> omega
  | two conj ka kb _ _ _ _ ih => cases ka <;> cases kb <;> simp_all [kept] <;> omega

lemma zero_done {d y t ws} (h : RunD d y t ws) :
    t = 0 → ws = [y] := by
  induction h using Run.fold with
  | done => simp
  | perm p _ ih => intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | one => simp
  | two => simp

def IsConst (d w : Nat) : Prop := (w &&& d) = 0 ∨ (w &&& d) = d
def isConstB (d w : Nat) : Bool := (w &&& d == 0) || (w &&& d == d)

lemma isConstB_iff (d w : Nat) : isConstB d w = true ↔ IsConst d w := by
  simp [isConstB, IsConst]

def Avail (d : Nat) (bank : List Nat) (w : Nat) : Prop :=
  IsConst d w ∨ ∃ v ∈ bank, (v &&& d) = (w &&& d)

def availB (d : Nat) (bank : List Nat) (w : Nat) : Bool :=
  let m := w &&& d
  m == 0 || m == d || bank.any (fun v => (v &&& d) == m)

lemma availB_iff (d : Nat) (bank : List Nat) (w : Nat) :
    availB d bank w = true ↔ Avail d bank w := by
  simp [availB, Avail, IsConst, or_assoc]

def NatReach (d : Nat) (roots : List Nat) : Nat → List Nat → Prop
  | 0, bank => bank = roots
  | p + 1, bank =>
    (∃ b a, bank = negD d a :: b ∧ NatReach d roots p b ∧ Avail d b a) ∨
    (∃ b a c op, bank = binD d op a c :: b ∧ NatReach d roots p b ∧ Avail d b a ∧ Avail d b c)

def Lower (d : Nat) (roots : List Nat) (T : Nat) (L : Nat) : Prop :=
  ∀ p bank, NatReach d roots p bank → Avail d bank T → L ≤ p

lemma mask256_bit (i : Nat) : mask256.testBit i = decide (i < 256) := by
  rw [mask256, Nat.testBit_two_pow_sub_one]

lemma negD_and_sub {d d1 : Nat} (hd : d &&& mask256 = d) (hsub : d &&& d1 = d) (a : Nat) :
    negD d1 a &&& d = negD d a := by
  apply Nat.eq_of_testBit_eq; intro i
  have h1 := congrArg (fun v => v.testBit i) hd
  have h2 := congrArg (fun v => v.testBit i) hsub
  simp only [negD, Nat.testBit_and, Nat.testBit_xor] at *
  cases hi : d.testBit i <;> simp_all

lemma andD_and_sub {d d1 : Nat} (hsub : d &&& d1 = d) (a b : Nat) :
    andD d1 a b &&& d = andD d a b := by
  apply Nat.eq_of_testBit_eq; intro i
  have h2 := congrArg (fun v => v.testBit i) hsub
  simp only [andD, Nat.testBit_and] at *
  cases hi : d.testBit i <;> simp_all

lemma orD_and_sub {d d1 : Nat} (hsub : d &&& d1 = d) (a b : Nat) :
    orD d1 a b &&& d = orD d a b := by
  apply Nat.eq_of_testBit_eq; intro i
  have h2 := congrArg (fun v => v.testBit i) hsub
  simp only [orD, Nat.testBit_and, Nat.testBit_or] at *
  cases hi : d.testBit i <;> simp_all

lemma negD_const {d : Nat} (hd : d &&& mask256 = d) {a : Nat} (hc : IsConst d a) :
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

lemma binD_const_left {d : Nat} {a b : Nat} (op : Bool) (hc : IsConst d a) :
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

lemma binD_comm (d : Nat) (op : Bool) (a b : Nat) : binD d op a b = binD d op b a := by
  cases op <;> simp [binD, andD, orD, Nat.and_comm, Nat.or_comm]

lemma avail_cons {d : Nat} {bank : List Nat} (z w : Nat) (h : Avail d bank w) :
    Avail d (z :: bank) w := by
  rcases h with hc | ⟨v, hv, he⟩
  · exact Or.inl hc
  · exact Or.inr ⟨v, List.mem_cons_of_mem _ hv, he⟩

lemma avail_of_eq {d : Nat} {bank : List Nat} {v w : Nat}
    (he : v &&& d = w &&& d) (h : Avail d bank v) : Avail d bank w := by
  rcases h with (h0 | h1) | ⟨u, hu, hue⟩
  · exact Or.inl (Or.inl (he.symm.trans h0))
  · exact Or.inl (Or.inr (he.symm.trans h1))
  · exact Or.inr ⟨u, hu, hue.trans he⟩


lemma mask_idemp (d w : Nat) : (w &&& d) &&& d = w &&& d := by
  simp [Nat.and_assoc, Nat.and_self]

lemma negD_mask (d a : Nat) : negD d (a &&& d) = negD d a := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [negD, Nat.testBit_and, Nat.testBit_xor]
  cases d.testBit i <;> simp

lemma andD_mask (d a b : Nat) : andD d (a &&& d) (b &&& d) = andD d a b := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [andD, Nat.testBit_and]
  cases d.testBit i <;> simp

lemma orD_mask (d a b : Nat) : orD d (a &&& d) (b &&& d) = orD d a b := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [orD, Nat.testBit_and, Nat.testBit_or]
  cases d.testBit i <;> simp

lemma pull_one {d Y k ws} (hd : d &&& mask256 = d) (hnd : ws.Nodup)
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

lemma pull_two {d Y k ws} (hnd : ws.Nodup)
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

lemma reach_to_run_aux {d : Nat} {roots : List Nat} {p bank} (hd : d &&& mask256 = d)
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

lemma reach_to_run {d : Nat} {roots : List Nat} {T : Nat} {p bank} (hd : d &&& mask256 = d)
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

lemma runD_bits {d y s ws} (hd : d &&& mask256 = d) (h : RunD d y s ws) (i j : Nat)
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

lemma getD_mem {xs : List Nat} {i : Nat} (hi : i < xs.length) : xs.getD i 0 ∈ xs := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact List.getElem_mem hi

def gvN (w : List Nat) (g : Gate) : Nat :=
  match g.op with
  | .and => g.inputs.foldr (fun i acc => andD mask256 (w.getD i 0) acc) mask256
  | .or  => g.inputs.foldr (fun i acc => orD mask256 (w.getD i 0) acc) 0
  | .not => match g.inputs with | [] => mask256 | i :: _ => negD mask256 (w.getD i 0)
  | _ => 0

def execN (gs : List Gate) (w : List Nat) : List Nat :=
  gs.foldl (fun l g => l ++ [gvN l g]) w

lemma gvN_bit (w : List Nat) (g : Gate) (r : Nat) (hr : r < 256)
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

lemma execN_bit (gs : List Gate) (w : List Nat) (r : Nat) (hr : r < 256)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    (execN gs w).map (·.testBit r) =
      gs.foldl (fun l g => l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)]) (w.map (·.testBit r)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [execN, List.foldl_cons] at ih ⊢
    rw [ih _ (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg'))]
    simp [gvN_bit w g r hr (hfan g List.mem_cons_self)]

lemma execN_reach (gs : List Gate) (roots : List Nat)
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

def xs256 : List Nat :=
  [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
   0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,
   0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
   0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,
   0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,
   0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,
   0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,
   0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]

def pt8 (r : Nat) : Fin 8 → Bool := fun i => r.testBit i.val

lemma xs256_bits : ∀ r : Fin 256, xs256.map (·.testBit r.val) = List.ofFn (pt8 r.val) := by
  decide +kernel

lemma lower_to_circuit (f : (Fin 8 → Bool) → Bool) (T lb : Nat)
    (hT : ∀ r : Fin 256, T.testBit r.val = f (pt8 r.val))
    (hlow : Lower mask256 xs256 T lb) :
    ∀ t : ℕ, HasCircuitSize 8 f t → lb ≤ t := by
  rintro t ⟨C, hfan, hsz, hev⟩
  have hsup0 : ∀ v ∈ xs256, Avail mask256 xs256 v := fun v hv => Or.inr ⟨v, hv, rfl⟩
  obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach C.gates xs256 hfan 0 xs256 xs256 rfl hsup0
  have hout : (execN C.gates xs256).getD C.output 0 &&& mask256 = T &&& mask256 := by
    apply Nat.eq_of_testBit_eq; intro r
    rw [Nat.testBit_and, Nat.testBit_and, mask256_bit]
    by_cases hlt : r < 256
    · simp only [hlt, decide_true, Bool.and_true]
      have h1 := execN_bit C.gates xs256 r hlt (fun g hg => (hfan g hg).1)
      have h2 := congrArg (fun l => l.getD C.output false) h1
      rw [xs256_bits ⟨r, hlt⟩] at h2
      have hgd : ((execN C.gates xs256).map (·.testBit r)).getD C.output false =
          ((execN C.gates xs256).getD C.output 0).testBit r := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (execN C.gates xs256)[C.output]? with | none => simp | some v => rfl
      rw [hgd] at h2
      have h3 : (C.wires (List.ofFn (pt8 r))).getD C.output false = f (pt8 r) := hev (pt8 r)
      exact h2.trans (h3.trans (hT ⟨r, hlt⟩).symm)
    · simp [hlt]
  have hav_out : Avail mask256 bank ((execN C.gates xs256).getD C.output 0) := by
    by_cases hi : C.output < (execN C.gates xs256).length
    · exact hsup _ (getD_mem hi)
    · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
  have hL := hlow p bank hr (avail_of_eq hout hav_out)
  show lb ≤ t
  have : C.gates.length ≤ t := hsz
  omega

lemma circuit_to_run (f : (Fin 8 → Bool) → Bool) (T : Nat)
    (hT : ∀ r : Fin 256, T.testBit r.val = f (pt8 r.val))
    (hnc : ¬ IsConst mask256 T) :
    ∀ t : ℕ, HasCircuitSize 8 f t →
      ∃ s ws, s ≤ t ∧ ws.Nodup ∧
        (∀ w ∈ ws, w ∈ xs256.map (· &&& mask256)) ∧
        RunD mask256 (T &&& mask256) s ws := by
  rintro t ⟨C, hfan, hsz, hev⟩
  have hsup0 : ∀ v ∈ xs256, Avail mask256 xs256 v := fun v hv => Or.inr ⟨v, hv, rfl⟩
  obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach C.gates xs256 hfan 0 xs256 xs256 rfl hsup0
  have hout : (execN C.gates xs256).getD C.output 0 &&& mask256 = T &&& mask256 := by
    apply Nat.eq_of_testBit_eq; intro r
    rw [Nat.testBit_and, Nat.testBit_and, mask256_bit]
    by_cases hlt : r < 256
    · simp only [hlt, decide_true, Bool.and_true]
      have h1 := execN_bit C.gates xs256 r hlt (fun g hg => (hfan g hg).1)
      have h2 := congrArg (fun l => l.getD C.output false) h1
      rw [xs256_bits ⟨r, hlt⟩] at h2
      have hgd : ((execN C.gates xs256).map (·.testBit r)).getD C.output false =
          ((execN C.gates xs256).getD C.output 0).testBit r := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (execN C.gates xs256)[C.output]? with | none => simp | some v => rfl
      rw [hgd] at h2
      have h3 : (C.wires (List.ofFn (pt8 r))).getD C.output false = f (pt8 r) := hev (pt8 r)
      exact h2.trans (h3.trans (hT ⟨r, hlt⟩).symm)
    · simp [hlt]
  have hav_out : Avail mask256 bank ((execN C.gates xs256).getD C.output 0) := by
    by_cases hi : C.output < (execN C.gates xs256).length
    · exact hsup _ (getD_mem hi)
    · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
  obtain ⟨s, ws, hs, hnd, hsub, hrun⟩ :=
    reach_to_run (by simp) hnc hr (avail_of_eq hout hav_out)
  refine ⟨s, ws, ?_, hnd, hsub, hrun⟩
  have : C.gates.length ≤ t := hsz
  omega

def pairOK (d T : Nat) (p : Nat × Nat) : Bool :=
  d.testBit p.1 && d.testBit p.2 && (T.testBit p.1 != T.testBit p.2)

def essOK (d T : Nat) (roots : List Nat) (a : Nat) (p : Nat × Nat) : Bool :=
  pairOK d T p && roots.all (fun v => (v == a) || (v.testBit p.1 == v.testBit p.2))

lemma runD_roots_perm {d T : Nat} {roots ws : List Nat} {s : Nat}
    (hd : d &&& mask256 = d) (hnd : ws.Nodup) (hrnd : roots.Nodup)
    (hsub : ∀ w ∈ ws, w ∈ roots)
    (hess : ∀ a ∈ roots, ∃ p, essOK d T roots a p = true)
    (hrun : RunD d T s ws) : ws.Perm roots := by
  apply (List.perm_ext_iff_of_nodup hnd hrnd).2
  intro a
  refine ⟨hsub a, ?_⟩
  intro ha
  obtain ⟨⟨i, j⟩, hp⟩ := hess a ha
  simp only [essOK, pairOK, Bool.and_eq_true, bne_iff_ne,
    List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at hp
  obtain ⟨⟨⟨hi, hj⟩, hdiff⟩, hiso⟩ := hp
  by_contra hnot
  apply hdiff
  apply runD_bits hd hrun i j hi hj
  intro w hw
  rcases hiso w (hsub w hw) with rfl | heq
  · exact absurd hw hnot
  · exact heq

def f8 : (Fin 8 → Bool) → Bool := fun x =>
  (x 0 && x 2 && x 7) || (x 0 && x 4 && x 5) ||
  (x 1 && x 2 && x 6) || (x 1 && x 3 && x 5)

def goalF8 : Nat := 0xeeeaece0e0e0e0e0eeaaeca0a0a0a0a0eeeaccc0c0c0c0c0eeaacc0000000000

lemma f8_bits : ∀ r : Fin 256, goalF8.testBit r.val = f8 (pt8 r.val) := by
  decide +kernel

lemma xs256_mask : xs256.map (· &&& mask256) = xs256 := by decide +kernel

lemma goalF8_mask : goalF8 &&& mask256 = goalF8 := by decide +kernel

lemma xs256_essential (a : Nat) (ha : a ∈ xs256) :
    ∃ p, essOK mask256 goalF8 xs256 a p = true := by
  simp only [xs256, List.mem_cons, List.mem_nil_iff, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨(132, 133), by decide +kernel⟩
  · exact ⟨(68, 70), by decide +kernel⟩
  · exact ⟨(129, 133), by decide +kernel⟩
  · exact ⟨(34, 42), by decide +kernel⟩
  · exact ⟨(33, 49), by decide +kernel⟩
  · exact ⟨(17, 49), by decide +kernel⟩
  · exact ⟨(6, 70), by decide +kernel⟩
  · exact ⟨(5, 133), by decide +kernel⟩

lemma f8_hasCircuit_run (t : Nat) (ht : HasCircuitSize 8 f8 t) :
    ∃ s, s ≤ t ∧ RunD mask256 goalF8 s xs256 := by
  have hnc : ¬ IsConst mask256 goalF8 := by unfold IsConst; decide +kernel
  obtain ⟨s, ws, hs, hnd, hsub, hrun⟩ := circuit_to_run f8 goalF8 f8_bits hnc t ht
  rw [xs256_mask] at hsub
  rw [goalF8_mask] at hrun
  have hperm := runD_roots_perm (by simp) hnd
    (by decide +kernel : xs256.Nodup) hsub xs256_essential hrun
  exact ⟨s, hs, Run.perm hperm hrun⟩


def normW (ws : List Nat) : List Nat := ws.insertionSort (· ≤ ·)

lemma normW_perm (ws : List Nat) : (normW ws).Perm ws := List.perm_insertionSort _ _

lemma normW_eq {ws zs : List Nat} (h : ws.Perm zs) : normW ws = normW zs := by
  exact ((normW_perm ws).trans (h.trans (normW_perm zs).symm)).eq_of_pairwise'
    (List.pairwise_insertionSort (· ≤ ·) ws) (List.pairwise_insertionSort (· ≤ ·) zs)

def covered (d y : Nat) (pairs : List (Nat × Nat)) (ws : List Nat) : Bool :=
  pairs.all fun p => !(pairOK d y p) || ws.any (fun w => w.testBit p.1 != w.testBit p.2)

lemma covered_run {d y t ws} (hd : d &&& mask256 = d) (h : RunD d y t ws)
    (pairs : List (Nat × Nat)) : covered d y pairs ws = true := by
  apply List.all_eq_true.mpr
  intro p hp
  simp only [Bool.or_eq_true, Bool.not_eq_true']
  by_cases hok : pairOK d y p = true
  · right
    by_contra hn
    have heq : ∀ w ∈ ws, w.testBit p.1 = w.testBit p.2 := by
      intro w hw
      have hf : (ws.any (fun w => w.testBit p.1 != w.testBit p.2)) = false :=
        Bool.eq_false_iff.mpr hn
      have hh := List.any_eq_false.mp hf w hw
      simpa only [bne_iff_ne, not_not] using hh
    have hh := runD_bits hd h p.1 p.2
    simp only [pairOK, Bool.and_eq_true, bne_iff_ne] at hok
    exact hok.2 (hh hok.1.1 hok.1.2 heq)
  · left
    exact Bool.eq_false_iff.mpr hok

def nextW (d : Nat) (ws : List Nat) : List (List Nat) :=
  ws.flatMap fun a =>
    let ra := ws.erase a
    let na := negD d a
    (if na != 0 && na != d && !(ws.contains na) then
      [na :: ra, na :: a :: ra] else []) ++
    ws.flatMap fun b =>
      if a == b then [] else
      let r := ra.erase b
      [andD d a b, orD d a b].flatMap fun w =>
        if w != 0 && w != d && !(ws.contains w) then
          [w :: r, w :: a :: r, w :: b :: r, w :: a :: b :: r] else []

def possibleW (d y : Nat) (pairs : List (Nat × Nat)) : Nat → Nat → List Nat → Bool
  | fuel, budget, ws =>
    let zs := normW ws
    decide (zs.length ≤ budget + 1) && covered d y pairs zs &&
    (match fuel with
    | 0 => true
    | fuel + 1 =>
      zs.contains y ||
      match budget with
      | 0 => false
      | budget + 1 => (nextW d zs).any (possibleW d y pairs fuel budget))

lemma possibleW_perm (d y : Nat) (pairs : List (Nat × Nat)) (fuel budget : Nat)
    {ws zs : List Nat} (h : ws.Perm zs) :
    possibleW d y pairs fuel budget ws = possibleW d y pairs fuel budget zs := by
  cases fuel <;> simp only [possibleW, normW_eq h]

lemma nextW_one {d a : Nat} {r ws : List Nat} (hperm : ws.Perm (a :: r))
    (h0 : negD d a ≠ 0) (hd : negD d a ≠ d) (hm : negD d a ∉ ws) (save : Bool) :
    ∃ zs ∈ nextW d ws, zs.Perm (negD d a :: kept save a r) := by
  have ha : a ∈ ws := hperm.mem_iff.mpr (by simp)
  have hr : (ws.erase a).Perm r := by simpa using hperm.erase a
  have hg : (negD d a != 0 && negD d a != d && !(ws.contains (negD d a))) = true := by
    simp [h0, hd, hm]
  cases save
  · refine ⟨negD d a :: ws.erase a, ?_, hr.cons _⟩
    simp only [nextW, List.mem_flatMap]
    refine ⟨a, ha, ?_⟩
    exact List.mem_append_left _ (by simp only [hg, ↓reduceIte]; simp)
  · refine ⟨negD d a :: a :: ws.erase a, ?_, (hr.cons _).cons _⟩
    simp only [nextW, List.mem_flatMap]
    refine ⟨a, ha, ?_⟩
    exact List.mem_append_left _ (by simp only [hg, ↓reduceIte]; simp)

lemma nextW_two {d a b : Nat} {r ws : List Nat} (hperm : ws.Perm (a :: b :: r))
    (hab : a ≠ b) (c ka kb : Bool)
    (h0 : (if c then andD d a b else orD d a b) ≠ 0)
    (hd : (if c then andD d a b else orD d a b) ≠ d)
    (hm : (if c then andD d a b else orD d a b) ∉ ws) :
    ∃ zs ∈ nextW d ws,
      zs.Perm ((if c then andD d a b else orD d a b) :: kept ka a (kept kb b r)) := by
  let w := if c then andD d a b else orD d a b
  have ha : a ∈ ws := hperm.mem_iff.mpr (by simp)
  have hb : b ∈ ws := hperm.mem_iff.mpr (by simp)
  have hr : ((ws.erase a).erase b).Perm r := by
    have hh := (hperm.erase a).erase b
    simpa using hh
  have hw : w ∈ [andD d a b, orD d a b] := by cases c <;> simp [w]
  have hg : (w != 0 && w != d && !(ws.contains w)) = true := by
    simp [w, h0, hd, hm]
  have mem : ∀ z ∈ [w :: (ws.erase a).erase b,
      w :: a :: (ws.erase a).erase b,
      w :: b :: (ws.erase a).erase b,
      w :: a :: b :: (ws.erase a).erase b], z ∈ nextW d ws := by
    intro z hz
    simp only [nextW, List.mem_flatMap]
    refine ⟨a, ha, List.mem_append_right _ ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨b, hb, ?_⟩
    simp only [show (a == b) = false by simp [hab], Bool.false_eq_true, ↓reduceIte,
      List.mem_flatMap]
    exact ⟨w, hw, by simpa only [hg, ↓reduceIte] using hz⟩
  cases ka <;> cases kb
  · exact ⟨w :: (ws.erase a).erase b, mem _ (by simp), hr.cons _⟩
  · exact ⟨w :: b :: (ws.erase a).erase b, mem _ (by simp), (hr.cons _).cons _⟩
  · exact ⟨w :: a :: (ws.erase a).erase b, mem _ (by simp), (hr.cons _).cons _⟩
  · exact ⟨w :: a :: b :: (ws.erase a).erase b, mem _ (by simp), ((hr.cons _).cons _).cons _⟩


lemma possibleW_zero {d y t ws} (hd : d &&& mask256 = d) (h : RunD d y t ws)
    (pairs : List (Nat × Nat)) {budget : Nat} (hb : t ≤ budget) :
    possibleW d y pairs 0 budget ws = true := by
  have hc := covered_run hd (Run.perm (normW_perm ws).symm h) pairs
  have hl : (normW ws).length ≤ budget + 1 := by
    rw [(normW_perm ws).length_eq]
    exact (run_len h).trans (by omega)
  simp only [possibleW, hc, decide_eq_true hl, Bool.true_and, Bool.and_true]

lemma possibleW_goal {d y t ws} (hd : d &&& mask256 = d) (h : RunD d y t ws)
    (pairs : List (Nat × Nat)) (fuel : Nat) {budget : Nat} (hb : t ≤ budget)
    (hy : y ∈ ws) : possibleW d y pairs fuel budget ws = true := by
  cases fuel with
  | zero => exact possibleW_zero hd h pairs hb
  | succ fuel =>
    have hc := covered_run hd (Run.perm (normW_perm ws).symm h) pairs
    have hl : (normW ws).length ≤ budget + 1 := by
      rw [(normW_perm ws).length_eq]
      exact (run_len h).trans (by omega)
    have hy' : y ∈ normW ws := (normW_perm ws).mem_iff.mpr hy
    simp only [possibleW, hc, decide_eq_true hl, Bool.true_and]
    simp [hy']

lemma possibleW_step {d y t ws} (hd : d &&& mask256 = d) (h : RunD d y t ws)
    (pairs : List (Nat × Nat)) (fuel budget : Nat) (hb : t ≤ budget + 1)
    (hn : ∃ zs ∈ nextW d (normW ws), possibleW d y pairs fuel budget zs = true) :
    possibleW d y pairs (fuel + 1) (budget + 1) ws = true := by
  have hc := covered_run hd (Run.perm (normW_perm ws).symm h) pairs
  have hl : (normW ws).length ≤ budget + 1 + 1 := by
    rw [(normW_perm ws).length_eq]
    exact (run_len h).trans (by omega)
  simp only [possibleW, hc, decide_eq_true hl, Bool.true_and]
  simp only [Bool.or_eq_true]
  exact Or.inr (List.any_eq_true.mpr hn)

lemma possibleW_run {d y t ws} (hd : d &&& mask256 = d) (h : RunD d y t ws)
    (pairs : List (Nat × Nat)) :
    ∀ fuel budget, t ≤ budget → ws.Nodup → possibleW d y pairs fuel budget ws = true := by
  induction h using Run.fold with
  | done =>
    intro fuel budget ht hnd
    exact possibleW_goal hd Run.done pairs fuel ht (by simp)
  | perm hp h ih =>
    intro fuel budget ht hnd
    rw [← possibleW_perm d y pairs fuel budget hp]
    exact ih fuel budget ht (hp.nodup_iff.mpr hnd)
  | @one s a r save h0 hdm hm h ih =>
    intro fuel budget ht hnd
    have hrun := Run.one save h0 hdm hm h
    cases fuel with
    | zero => exact possibleW_zero hd hrun pairs ht
    | succ fuel =>
      cases budget with
      | zero => omega
      | succ budget =>
        apply possibleW_step hd hrun pairs fuel budget ht
        have hnm : negD d a ∉ normW (a :: r) := fun hx => hm ((normW_perm _).mem_iff.mp hx)
        obtain ⟨zs, hzs, hp⟩ := nextW_one (normW_perm (a :: r)) h0 hdm hnm save
        refine ⟨zs, hzs, ?_⟩
        rw [possibleW_perm d y pairs fuel budget hp]
        apply ih fuel budget (by omega)
        cases save <;> simp_all [kept, List.nodup_cons]
  | @two s a b r c ka kb h0 hdm hm h ih =>
    intro fuel budget ht hnd
    have hrun := Run.two c ka kb h0 hdm hm h
    cases fuel with
    | zero => exact possibleW_zero hd hrun pairs ht
    | succ fuel =>
      cases budget with
      | zero => omega
      | succ budget =>
        apply possibleW_step hd hrun pairs fuel budget ht
        have hab : a ≠ b := by
          intro he
          subst b
          simp at hnd
        have hnm : (if c then andD d a b else orD d a b) ∉ normW (a :: b :: r) :=
          fun hx => hm ((normW_perm _).mem_iff.mp hx)
        obtain ⟨zs, hzs, hp⟩ := nextW_two (normW_perm (a :: b :: r)) hab c ka kb h0 hdm hnm
        refine ⟨zs, hzs, ?_⟩
        rw [possibleW_perm d y pairs fuel budget hp]
        apply ih fuel budget (by omega)
        cases ka <;> cases kb <;> simp_all [kept, List.nodup_cons]


def f8Pairs : List (Nat × Nat) := [(14, 78), (50, 58), (97, 113), (74, 106), (56, 58), (50, 51), (7, 135), (68, 70), (132, 133), (17, 49), (35, 43), (37, 53), (37, 165), (129, 133), (7, 71), (98, 102), (38, 46), (21, 149), (69, 197), (22, 86), (35, 51), (38, 102), (41, 57), (134, 198), (161, 177), (162, 170), (14, 46), (41, 43), (98, 106), (13, 141), (56, 57), (74, 78), (82, 86), (112, 113), (138, 170), (168, 170)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma f8_check : possibleW mask256 goalF8 f8Pairs 3 8 xs256 = false := by
  decide +kernel

lemma f8_lower (t : Nat) (ht : HasCircuitSize 8 f8 t) : 9 ≤ t := by
  obtain ⟨s, hs, hrun⟩ := f8_hasCircuit_run t ht
  by_contra hlt
  have hb : s ≤ 8 := by omega
  have hp := possibleW_run (by simp : mask256 &&& mask256 = mask256)
    hrun f8Pairs 3 8 hb (by decide +kernel : xs256.Nodup)
  rw [f8_check] at hp
  contradiction

end PEqualNP.Outside.L_meta_27223_aux

namespace PEqualNP.Outside.L_meta_27223_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

lemma getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

lemma getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

lemma normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

lemma normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate]

lemma wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

abbrev Stat := Sum Bool ℕ

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

lemma simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      (simp [simpAnd] at hg; all_goals (subst hg; simp [Ok]))
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      (simp [simpOr] at hg; all_goals (subst hg; simp [Ok]))
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      (simp [simpNot] at hg; all_goals (subst hg; simp [Ok]))
  · simp at hg
  · simp at hg

lemma simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

lemma simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · rcases a with c | j <;> rcases b with d | k
      · cases c <;> cases d <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
      · cases c <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
      · cases d <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
      · simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · rcases a with c | j <;> rcases b with d | k
      · cases c <;> cases d <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
      · cases c <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
      · cases d <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
      · simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

lemma getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

lemma toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

lemma elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

lemma Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

lemma Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

lemma inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2


def readsSet (S : Finset ℕ) (g : Gate) : Bool :=
  g.inputs.any (fun k => decide (k ∈ S))

lemma readsSet_iff (S : Finset ℕ) (g : Gate) :
    readsSet S g = true ↔ ∃ k ∈ S, k ∈ g.inputs := by
  simp only [readsSet, List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨k, hk, hS⟩; exact ⟨k, hS, hk⟩
  · rintro ⟨k, hS, hk⟩; exact ⟨k, hk, hS⟩

lemma elim_len_add_count_set_le (n : ℕ) (S : Finset ℕ) (gs : List Gate) :
    ∀ acc : List Stat × List Gate,
      (∀ g ∈ gs, NOk g) →
      (∀ k ∈ S, k < acc.1.length ∧ ∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
      (elim n gs acc).2.length + gs.countP (readsSet S)
        ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _; simp [elim]
  | cons g gs ih =>
    intro acc hok hc
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3]
    have hok' : ∀ g' ∈ gs, NOk g' := fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')
    have hc' : ∀ k ∈ S, k < (elimStep n acc g).1.length ∧
        ∃ c, (elimStep n acc g).1.getD k (Sum.inl false) = Sum.inl c := by
      intro k hk
      obtain ⟨hkl, c, hc⟩ := hc k hk
      refine ⟨by simp [elimStep]; omega, c, ?_⟩
      simp only [elimStep]
      rw [getD_snoc_ne _ _ _ _ (by omega)]
      exact hc
    have hih := ih (elimStep n acc g) hok' hc'
    by_cases hkg : readsSet S g = true
    · have hcnt : (g :: gs).countP (readsSet S) = gs.countP (readsSet S) + 1 := by
        rw [List.countP_cons]; simp [hkg]
      have hsim : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact (hok g List.mem_cons_self).1.1
        · simpa using (hok g List.mem_cons_self).1.2
        · intro h; simpa using (hok g List.mem_cons_self).2 h
        · obtain ⟨k, hkS, hkg⟩ := (readsSet_iff S g).1 hkg
          obtain ⟨_, c, hc⟩ := hc k hkS
          exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        simp only [elimStep, List.length_append]
        rw [hsim]; simp
      rw [hcnt, List.length_cons]
      omega
    · have hcnt : (g :: gs).countP (readsSet S) = gs.countP (readsSet S) := by
        rw [List.countP_cons]; simp [hkg]
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      rw [hcnt, List.length_cons]
      omega


def zeroInput (i : Fin 2) (y : Fin 8 → Bool) : Fin 9 → Bool :=
  if i = 0 then ![false, y 0, y 1, y 2, y 3, y 4, y 5, y 6, y 7]
  else ![y 0, false, y 1, y 2, y 3, y 4, y 5, y 6, y 7]

def prefixStats (i : Fin 2) : List Stat :=
  if i = 0 then
    [Sum.inl false, Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3, Sum.inr 4,
      Sum.inr 5, Sum.inr 6, Sum.inr 7, Sum.inl false, Sum.inl true]
  else
    [Sum.inr 0, Sum.inl false, Sum.inr 1, Sum.inr 2, Sum.inr 3, Sum.inr 4,
      Sum.inr 5, Sum.inr 6, Sum.inr 7, Sum.inl false, Sum.inl true]

def prefixGates : List Gate := [⟨GateOp.and, [0, 1]⟩, ⟨GateOp.not, [9]⟩]

lemma zero_prefix_wires (i : Fin 2) (y : Fin 8 → Bool) :
    wiresFrom prefixGates (List.ofFn (zeroInput i y)) =
      List.ofFn (zeroInput i y) ++ [false, true] := by
  fin_cases i <;> simp [prefixGates, wiresFrom, zeroInput, List.ofFn_succ, GateOp.eval]

lemma prefix_inv (i : Fin 2) (y : Fin 8 → Bool) :
    Inv 8 (List.ofFn y) (List.ofFn (zeroInput i y) ++ [false, true])
      (prefixStats i, []) := by
  constructor
  · fin_cases i <;> simp [prefixStats]
  · intro j
    by_cases hj : j < 11
    · interval_cases j <;> fin_cases i <;>
        simp [prefixStats, zeroInput, List.ofFn_succ, Stat.Valid, Stat.val, wiresFrom]
    · have hst : (prefixStats i).length = 11 := by fin_cases i <;> rfl
      have hw : (List.ofFn (zeroInput i y) ++ [false, true]).length = 11 := by simp
      change ((prefixStats i).getD j (Sum.inl false)).Valid (8 + 0) ∧
        ((prefixStats i).getD j (Sum.inl false)).val (wiresFrom [] (List.ofFn y)) = _
      rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      simp [Stat.Valid, Stat.val]

lemma prefix_constants (i : Fin 2) :
    ∀ k ∈ ({i.val, 10} : Finset ℕ), k < (prefixStats i).length ∧
      ∃ c, (prefixStats i).getD k (Sum.inl false) = Sum.inl c := by
  intro k hk
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl <;> fin_cases i <;> simp [prefixStats]

lemma readsSet_pair (i : Fin 2) (g : Gate) :
    readsSet {i.val, 10} g = decide (i.val ∈ g.inputs ∨ 10 ∈ g.inputs) := by
  apply Bool.eq_iff_iff.2
  rw [readsSet_iff]
  simp

lemma zero_prefix_reduce (i : Fin 2) (G : List Gate) (o : ℕ)
    (hG : ∀ g ∈ G, NOk g)
    (hcnt : 2 ≤ G.countP (fun g => decide (i.val ∈ g.inputs ∨ 10 ∈ g.inputs)))
    (hnc : ∃ x y : Fin 8 → Bool,
      (wiresFrom (prefixGates ++ G) (List.ofFn (zeroInput i x))).getD o false ≠
      (wiresFrom (prefixGates ++ G) (List.ofFn (zeroInput i y))).getD o false) :
    ∃ D : Circuit, FanInTwo D ∧ D.size + 4 ≤ G.length + 2 ∧
      ∀ y : Fin 8 → Bool, D.eval (List.ofFn y) =
        (wiresFrom (prefixGates ++ G) (List.ofFn (zeroInput i y))).getD o false := by
  let result := elim 8 G (prefixStats i, [])
  have hInv (y : Fin 8 → Bool) :
      Inv 8 (List.ofFn y) (wiresFrom (prefixGates ++ G) (List.ofFn (zeroInput i y))) result := by
    rw [wiresFrom_append, zero_prefix_wires]
    exact inv_elim 8 (List.ofFn y) (by simp) G _ _ (fun g hg => (hG g hg).1) (prefix_inv i y)
  have hsize : result.2.length + 2 ≤ G.length := by
    have hc := elim_len_add_count_set_le 8 {i.val, 10} G (prefixStats i, []) hG
      (prefix_constants i)
    have heq : G.countP (readsSet {i.val, 10}) =
        G.countP (fun g => decide (i.val ∈ g.inputs ∨ 10 ∈ g.inputs)) := by
      congr 1
      funext g
      exact readsSet_pair i g
    rw [heq] at hc
    simp only [List.length_nil, Nat.zero_add] at hc
    dsimp [result]
    omega
  cases hs : result.1.getD o (Sum.inl false) with
  | inl b =>
    obtain ⟨x, y, hxy⟩ := hnc
    have hx := ((hInv x).2 o).2
    have hy := ((hInv y).2 o).2
    rw [hs] at hx hy
    exact (hxy (hx.symm.trans hy)).elim
  | inr j =>
    refine ⟨⟨result.2, j⟩, ?_, ?_, ?_⟩
    · exact elim_ok 8 G (prefixStats i, []) (by simp)
    · change result.2.length + 4 ≤ G.length + 2
      omega
    · intro y
      have hv := ((hInv y).2 o).2
      rw [hs] at hv
      exact hv


def pm3Reduction (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
    (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

def cofactorReduction (y : Fin 8 → Bool) : Bool :=
  (y 0 && y 2 && y 7) || (y 0 && y 4 && y 5) ||
    (y 1 && y 2 && y 6) || (y 1 && y 3 && y 5)

def perm8 : Fin 8 → Fin 8 := ![0, 1, 3, 2, 4, 6, 5, 7]

def renameInput8 (y : Fin 8 → Bool) : Fin 8 → Bool := fun j => y (perm8 j)

lemma zero0_cofactor (y : Fin 8 → Bool) :
    pm3Reduction (zeroInput 0 y) = cofactorReduction y := by
  simp [pm3Reduction, zeroInput, cofactorReduction]

lemma zero1_cofactor (y : Fin 8 → Bool) :
    pm3Reduction (zeroInput 1 (renameInput8 y)) = cofactorReduction y := by
  simp [pm3Reduction, zeroInput, cofactorReduction, renameInput8, perm8,
    Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]

lemma zero_cofactor_nonconst (i : Fin 2) :
    ∃ x y : Fin 8 → Bool, pm3Reduction (zeroInput i x) ≠ pm3Reduction (zeroInput i y) := by
  refine ⟨fun _ => false, fun _ => true, ?_⟩
  fin_cases i <;> decide

def renameWire8 (k : ℕ) : ℕ := if h : k < 8 then (perm8 ⟨k, h⟩).val else k

def renameGate8 (g : Gate) : Gate := ⟨g.op, g.inputs.map renameWire8⟩

def renameCircuit8 (C : Circuit) : Circuit :=
  ⟨C.gates.map renameGate8, renameWire8 C.output⟩

lemma renameWire8_ge (k : ℕ) (hk : 8 ≤ k) : renameWire8 k = k := by
  simp [renameWire8, not_lt.mpr hk]

lemma renameWire8_lt (k : ℕ) (hk : k < 8) : renameWire8 k < 8 := by
  simp only [renameWire8, dif_pos hk]
  exact (perm8 ⟨k, hk⟩).isLt

lemma rename_relation_append (w w' : List Bool) (hl : w.length = w'.length)
    (hn : 8 ≤ w.length) (hrel : ∀ k, w.getD k false = w'.getD (renameWire8 k) false)
    (b : Bool) :
    ∀ k, (w ++ [b]).getD k false = (w' ++ [b]).getD (renameWire8 k) false := by
  intro k
  by_cases hk : k < 8
  · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by
      have := renameWire8_lt k hk
      omega)]
    exact hrel k
  · have hk8 : 8 ≤ k := by omega
    rw [renameWire8_ge k hk8]
    by_cases hkl : k = w.length
    · subst k
      rw [getD_snoc_eq, hl, getD_snoc_eq]
    · rw [getD_snoc_ne _ _ _ _ hkl, getD_snoc_ne _ _ _ _ (by omega)]
      simpa [renameWire8_ge k hk8] using hrel k

lemma rename_wiresFrom (G : List Gate) :
    ∀ w w' : List Bool, w.length = w'.length → 8 ≤ w.length →
      (∀ k, w.getD k false = w'.getD (renameWire8 k) false) →
      ∀ k, (wiresFrom G w).getD k false =
        (wiresFrom (G.map renameGate8) w').getD (renameWire8 k) false := by
  induction G with
  | nil => intro w w' _ _ hrel; exact hrel
  | cons g G ih =>
    intro w w' hl hn hrel
    have hgate : g.op.eval (g.inputs.map (fun k => w.getD k false)) =
        (renameGate8 g).op.eval ((renameGate8 g).inputs.map (fun k => w'.getD k false)) := by
      dsimp [renameGate8]
      rw [List.map_map]
      congr 1
      exact List.map_congr_left (fun k _ => hrel k)
    change ∀ k, (wiresFrom G (w ++ [g.op.eval (g.inputs.map (fun k => w.getD k false))])).getD k false =
      (wiresFrom (G.map renameGate8)
        (w' ++ [(renameGate8 g).op.eval ((renameGate8 g).inputs.map (fun k => w'.getD k false))])).getD
          (renameWire8 k) false
    rw [hgate]
    apply ih
    · simp [hl]
    · simp; omega
    · exact rename_relation_append w w' hl hn hrel _

lemma rename_input_relation (y : Fin 8 → Bool) :
    ∀ k, (List.ofFn (renameInput8 y)).getD k false =
      (List.ofFn y).getD (renameWire8 k) false := by
  intro k
  by_cases hk : k < 8
  · interval_cases k <;> simp [renameWire8, renameInput8, perm8, List.ofFn_succ]
  · have hk8 : 8 ≤ k := by omega
    rw [renameWire8_ge k hk8, List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]

lemma renameCircuit8_eval (C : Circuit) (y : Fin 8 → Bool) :
    (renameCircuit8 C).eval (List.ofFn y) = C.eval (List.ofFn (renameInput8 y)) := by
  exact (rename_wiresFrom C.gates _ _ (by simp) (by simp)
    (rename_input_relation y) C.output).symm

lemma renameCircuit8_size (C : Circuit) : (renameCircuit8 C).size = C.size := by
  simp [renameCircuit8, Circuit.size]

lemma renameCircuit8_fanInTwo (C : Circuit) (hC : FanInTwo C) : FanInTwo (renameCircuit8 C) := by
  intro g hg
  obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
  simpa [renameGate8] using hC g' hg'

lemma normalize_zero_cofactor (i : Fin 2) (C : Circuit)
    (hC : FanInTwo C)
    (hf : ∀ y : Fin 8 → Bool, C.eval (List.ofFn y) = pm3Reduction (zeroInput i y)) :
    ∃ D : Circuit, FanInTwo D ∧ D.size = C.size ∧
      ∀ y : Fin 8 → Bool, D.eval (List.ofFn y) = cofactorReduction y := by
  fin_cases i
  · refine ⟨C, hC, rfl, ?_⟩
    intro y
    rw [hf]
    exact zero0_cofactor y
  · refine ⟨renameCircuit8 C, renameCircuit8_fanInTwo C hC, renameCircuit8_size C, ?_⟩
    intro y
    rw [renameCircuit8_eval, hf]
    exact zero1_cofactor y

lemma pm3_zero_prefix_reduce (i : Fin 2) (G : List Gate) (o : ℕ)
    (hG : ∀ g ∈ G, NOk g)
    (hcnt : 2 ≤ G.countP (fun g => decide (i.val ∈ g.inputs ∨ 10 ∈ g.inputs)))
    (hf : ∀ x : Fin 9 → Bool,
      (wiresFrom (prefixGates ++ G) (List.ofFn x)).getD o false = pm3Reduction x) :
    ∃ D : Circuit, FanInTwo D ∧ D.size + 4 ≤ G.length + 2 ∧
      ∀ y : Fin 8 → Bool, D.eval (List.ofFn y) = cofactorReduction y := by
  have hnc : ∃ x y : Fin 8 → Bool,
      (wiresFrom (prefixGates ++ G) (List.ofFn (zeroInput i x))).getD o false ≠
      (wiresFrom (prefixGates ++ G) (List.ofFn (zeroInput i y))).getD o false := by
    simpa only [hf] using zero_cofactor_nonconst i
  obtain ⟨C, hC, hs, he⟩ := zero_prefix_reduce i G o hG hcnt hnc
  have hfC : ∀ y : Fin 8 → Bool, C.eval (List.ofFn y) = pm3Reduction (zeroInput i y) := by
    intro y
    rw [he, hf]
  obtain ⟨D, hD, hsize, hfun⟩ := normalize_zero_cofactor i C hC hfC
  exact ⟨D, hD, by omega, hfun⟩

end PEqualNP.Outside.L_meta_27223_aux


namespace PEqualNP.Outside.L_meta_27223_aux.Prefix

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

lemma wiresFrom_agree_off {n : ℕ} (gs : List Gate)
    (hno : ∀ g ∈ gs, n ∉ g.inputs) :
    ∀ w w' : List Bool, w.length = w'.length →
      (∀ i, i ≠ n → w.getD i false = w'.getD i false) →
      ∀ j, j ≠ n → (wiresFrom gs w).getD j false = (wiresFrom gs w').getD j false := by
  induction gs with
  | nil =>
    intro w w' _ hagree j hj
    exact hagree j hj
  | cons g gs ih =>
    intro w w' hlen hagree j hj
    have hno' : ∀ g' ∈ gs, n ∉ g'.inputs :=
      fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')
    have hgn : n ∉ g.inputs := hno g List.mem_cons_self
    have hlen1 : (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length
        = (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)]).length := by
      simp [hlen]
    have hagree1 : ∀ i, i ≠ n →
        (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).getD i false
        = (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)]).getD i false := by
      intro i hi
      by_cases hlt : i < w.length
      · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (by omega)]
        exact hagree i hi
      · by_cases heq : i = w.length
        · subst heq
          rw [getD_snoc_len w _ _ w.length rfl, getD_snoc_len w' _ _ w.length hlen.symm]
          congr 1
          apply List.map_congr_left
          intro a ha
          exact hagree a (fun e => hgn (e ▸ ha))
        · have hwl : i ≠ w'.length := by omega
          rw [getD_snoc_ne _ _ _ _ heq, getD_snoc_ne _ _ _ _ hwl]
          exact hagree i hi
    exact ih hno'
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
      hlen1 hagree1 j hj

lemma two_le_countP_of_two_getElem {α : Type} (p : α → Bool) (l : List α)
    (i j : ℕ) (hi : i < l.length) (hj : j < l.length) (hij : i ≠ j)
    (hpi : p l[i] = true) (hpj : p l[j] = true) : 2 ≤ l.countP p := by
  induction l generalizing i j with
  | nil => simp at hi
  | cons a l ih =>
    match i, j with
    | 0, 0 => exact absurd rfl hij
    | 0, j + 1 =>
      have ha : p a = true := by simpa using hpi
      have hj' : j < l.length := by simpa using hj
      have hpj' : p l[j] = true := by simpa using hpj
      rw [List.countP_cons, ite_eq_left ha]
      have hpos : 1 ≤ l.countP p := by
        rw [List.one_le_countP_iff]
        exact ⟨l[j], List.getElem_mem hj', hpj'⟩
      omega
    | i + 1, 0 =>
      have ha : p a = true := by simpa using hpj
      have hi' : i < l.length := by simpa using hi
      have hpi' : p l[i] = true := by simpa using hpi
      rw [List.countP_cons, ite_eq_left ha]
      have hpos : 1 ≤ l.countP p := by
        rw [List.one_le_countP_iff]
        exact ⟨l[i], List.getElem_mem hi', hpi'⟩
      omega
    | i + 1, j + 1 =>
      have hi' : i < l.length := by simpa using hi
      have hj' : j < l.length := by simpa using hj
      have hij' : i ≠ j := by omega
      have hpi' : p l[i] = true := by simpa using hpi
      have hpj' : p l[j] = true := by simpa using hpj
      have hrec := ih i j hi' hj' hij' hpi' hpj'
      rw [List.countP_cons]
      have hle : l.countP p ≤ l.countP p + (if p a then 1 else 0) := Nat.le_add_right _ _
      omega

def pm3 (x : Fin 9 → Bool) : Bool :=
  ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) ||
   (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) ||
   (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))

def circuit (G : List Gate) (o : ℕ) : Circuit :=
  ⟨⟨GateOp.and, [0, 1]⟩ :: ⟨GateOp.not, [9]⟩ :: G, o⟩

def witness (i : Fin 2) (b : Bool) : Fin 9 → Bool :=
  if i = 0 then ![b, false, false, false, true, false, false, false, true]
  else ![false, b, false, true, false, false, false, false, true]

def initial (i : Fin 2) (b : Bool) : List Bool :=
  List.ofFn (witness i b) ++ [false, true]

lemma witness_value : ∀ (i : Fin 2) (b : Bool), pm3 (witness i b) = b := by
  decide +kernel

lemma initial_agree : ∀ (i : Fin 2) (j : Fin 11), j.val ≠ i.val →
    (initial i false).getD j.val false = (initial i true).getD j.val false := by
  decide +kernel

lemma initial_length (i : Fin 2) (b : Bool) : (initial i b).length = 11 := by
  simp [initial]

lemma initial_agree_nat (i : Fin 2) (j : ℕ) (h : j ≠ i.val) :
    (initial i false).getD j false = (initial i true).getD j false := by
  by_cases hj : j < 11
  · exact initial_agree i ⟨j, hj⟩ h
  · rw [List.getD_eq_default _ _ (by rw [initial_length]; omega),
      List.getD_eq_default _ _ (by rw [initial_length]; omega)]

lemma circuit_witness (G : List Gate) (o : ℕ) (i : Fin 2) (b : Bool) :
    (circuit G o).eval (List.ofFn (witness i b)) =
      (wiresFrom G (initial i b)).getD o false := by
  fin_cases i <;> cases b <;>
    simp [circuit, Circuit.eval, Circuit.wires, wiresFrom, witness, initial, GateOp.eval]

lemma input_read (G : List Gate) (o : ℕ) (i : Fin 2)
    (ho : o + 1 = 11 + G.length)
    (hf : ∀ x : Fin 9 → Bool, (circuit G o).eval (List.ofFn x) = pm3 x) :
    ∃ g ∈ G, i.val ∈ g.inputs := by
  by_contra h
  push Not at h
  have hag := wiresFrom_agree_off G h (initial i false) (initial i true)
    (by rw [initial_length, initial_length]) (initial_agree_nat i) o (by omega)
  have hfalse := hf (witness i false)
  have htrue := hf (witness i true)
  rw [circuit_witness, witness_value] at hfalse htrue
  rw [hfalse, htrue] at hag
  contradiction

lemma two_le_count_mem {α : Type} (p : α → Bool) (l : List α) (a b : α)
    (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b) (hpa : p a = true) (hpb : p b = true) :
    2 ≤ l.countP p := by
  induction l with
  | nil => simp at ha
  | cons c l ih =>
    by_cases hac : a = c
    · subst a
      have hb' : b ∈ l := (List.mem_cons.mp hb).resolve_left (Ne.symm hne)
      have hpos : 1 ≤ l.countP p := List.one_le_countP_iff.mpr ⟨b, hb', hpb⟩
      rw [List.countP_cons]
      simp only [hpa, ite_true]
      omega
    · have ha' : a ∈ l := (List.mem_cons.mp ha).resolve_left hac
      by_cases hbc : b = c
      · subst b
        have hpos : 1 ≤ l.countP p := List.one_le_countP_iff.mpr ⟨a, ha', hpa⟩
        rw [List.countP_cons]
        simp only [hpb, ite_true]
        omega
      · have hb' : b ∈ l := (List.mem_cons.mp hb).resolve_left hbc
        have hrec := ih ha' hb'
        rw [List.countP_cons]
        omega

lemma miss_raw (l : List ℕ) (hlen : l.length ≤ 2) (hq : 10 ∈ l) :
    ∃ i : Fin 2, i.val ∉ l := by
  by_cases h0 : 0 ∈ l
  · by_cases h1 : 1 ∈ l
    · have hsub : ({0, 1, 10} : Finset ℕ) ⊆ l.toFinset := by
        intro a ha
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with rfl | rfl | rfl
        · simpa using h0
        · simpa using h1
        · simpa using hq
      have hcard := Finset.card_le_card hsub
      have hlen' := List.toFinset_card_le l
      norm_num at hcard
      omega
    · exact ⟨1, h1⟩
  · exact ⟨0, h0⟩

lemma readers (G : List Gate) (o : ℕ)
    (ho : o + 1 = 11 + G.length)
    (hf : ∀ x : Fin 9 → Bool, (circuit G o).eval (List.ofFn x) = pm3 x)
    (hlen : ∀ g ∈ G, g.inputs.length ≤ 2)
    (hq : ∃ g ∈ G, 10 ∈ g.inputs) :
    ∃ i : Fin 2, 2 ≤ G.countP (fun g => decide (i.val ∈ g.inputs ∨ 10 ∈ g.inputs)) := by
  obtain ⟨g, hg, hgq⟩ := hq
  obtain ⟨i, hgi⟩ := miss_raw g.inputs (hlen g hg) hgq
  obtain ⟨g', hg', hgi'⟩ := input_read G o i ho hf
  refine ⟨i, two_le_count_mem _ G g g' hg hg' ?_ ?_ ?_⟩
  · intro heq
    exact hgi (heq ▸ hgi')
  · simp only [decide_eq_true_eq]
    exact Or.inr hgq
  · simp only [decide_eq_true_eq]
    exact Or.inl hgi'

lemma readers_of_live (G : List Gate) (o : ℕ)
    (ho : o + 1 = 11 + G.length)
    (hf : ∀ x : Fin 9 → Bool, (circuit G o).eval (List.ofFn x) = pm3 x)
    (hlen : ∀ g ∈ G, g.inputs.length ≤ 2)
    (hlive : ∀ j : Fin (circuit G o).gates.length,
      j.val + 1 < (circuit G o).gates.length →
      ∃ k : Fin (circuit G o).gates.length, j.val < k.val ∧
        9 + j.val ∈ ((circuit G o).gates.get k).inputs) :
    ∃ i : Fin 2, 2 ≤ G.countP (fun g => decide (i.val ∈ g.inputs ∨ 10 ∈ g.inputs)) := by
  have hpos : 0 < G.length := by
    obtain ⟨g, hg, _⟩ := input_read G o 0 ho hf
    exact List.length_pos_of_mem hg
  obtain ⟨k, _, hk⟩ := hlive ⟨1, by simp [circuit]⟩ (by simp [circuit]; omega)
  apply readers G o ho hf hlen
  let g := (circuit G o).gates.get k
  have hg : g ∈ (circuit G o).gates := List.get_mem _ _
  change 10 ∈ g.inputs at hk
  simp only [circuit, List.mem_cons] at hg
  rcases hg with h | h | h
  · rw [h] at hk
    norm_num at hk
  · rw [h] at hk
    norm_num at hk
  · exact ⟨g, h, hk⟩

def normal (C : Circuit) : Prop :=
  ∀ j : Fin C.gates.length,
    ((C.gates.get j).op = GateOp.not ∧
      ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
    (((C.gates.get j).op = GateOp.and ∨ (C.gates.get j).op = GateOp.or) ∧
      ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])

lemma normal_nok (G : List Gate) (o : ℕ) (hn : normal (circuit G o)) :
    ∀ g ∈ G,
      (g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        g.inputs.length ≤ 2) ∧ (g.op = GateOp.not → g.inputs.length ≤ 1) := by
  intro g hg
  have hgall : g ∈ (circuit G o).gates := by simp [circuit, hg]
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hgall
  have hjn := hn j
  rw [hj] at hjn
  rcases hjn with ⟨hop, a, _, hins⟩ | ⟨hop, a, b, _, _, hins⟩
  · simp [hop, hins]
  · rcases hop with hop | hop <;> simp [hop, hins]

end PEqualNP.Outside.L_meta_27223_aux.Prefix

namespace PEqualNP.Outside.L_meta_27223_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma gap_reduction (h : ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [9]⟩) :
    ∃ D : Circuit, FanInTwo D ∧ D.size ≤ 8 ∧
      ∀ y : Fin 8 → Bool, D.eval (List.ofFn y) = cofactorReduction y := by
  obtain ⟨⟨gates, o⟩, hfan, hsize, hf, ho, hn, hu, hl, hfirst, hsecond⟩ := h
  cases gates with
  | nil => simp at hfirst
  | cons g gs =>
    change some g = some ⟨GateOp.and, [0, 1]⟩ at hfirst
    have hg := Option.some.inj hfirst
    subst g
    cases gs with
    | nil => simp at hsecond
    | cons g G =>
      change some g = some ⟨GateOp.not, [9]⟩ at hsecond
      have hg := Option.some.inj hsecond
      subst g
      have hfn : ∀ x : Fin 9 → Bool,
          (Prefix.circuit G o).eval (List.ofFn x) = Prefix.pm3 x := hf
      have hon : o + 1 = 11 + G.length := by
        simpa [Circuit.size, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ho
      have hnn : Prefix.normal (Prefix.circuit G o) := hn
      have hG : ∀ g ∈ G, NOk g := Prefix.normal_nok G o hnn
      obtain ⟨i, hi⟩ := Prefix.readers_of_live G o hon hfn
        (fun g hg => (hG g hg).1.2) hl
      have hfr : ∀ x : Fin 9 → Bool,
          (wiresFrom (prefixGates ++ G) (List.ofFn x)).getD o false = pm3Reduction x := hf
      obtain ⟨D, hD, hs, hdf⟩ := pm3_zero_prefix_reduce i G o hG hi hfr
      refine ⟨D, hD, ?_, hdf⟩
      change G.length + 2 ≤ 12 at hsize
      omega

end PEqualNP.Outside.L_meta_27223_aux

theorem PEqualNP.Outside.L_meta_27223 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [9]⟩) := by
  intro h
  obtain ⟨C, hfan, hsize, heval⟩ := PEqualNP.Outside.L_meta_27223_aux.gap_reduction h
  have hc : PEqualNP.MetaComplexity.HasCircuitSize 8 PEqualNP.Outside.L_meta_27223_aux.f8 8 := by
    refine ⟨C, hfan, hsize, ?_⟩
    simpa only [PEqualNP.Outside.L_meta_27223_aux.f8, PEqualNP.Outside.L_meta_27223_aux.cofactorReduction] using heval
  have hb := PEqualNP.Outside.L_meta_27223_aux.f8_lower 8 hc
  omega
