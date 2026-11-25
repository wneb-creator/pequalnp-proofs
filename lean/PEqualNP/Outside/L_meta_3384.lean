import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3384

-- search functions, written with recursors so that the kernel runs them quickly
def mem (w : ℕ) (l : List ℕ) : Bool :=
  List.rec false (fun a _ ih => cond (Nat.beq a w) true ih) l
def del (w : ℕ) (l : List ℕ) : List ℕ :=
  List.rec [] (fun a l ih => cond (Nat.beq a w) l (a :: ih)) l
def cat (m l : List ℕ) : List ℕ :=
  List.rec m (fun a _ ih => a :: ih) l
def ne (l : List (ℕ × ℕ)) : Bool := List.rec false (fun _ _ _ => true) l
def capp (m l : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  List.rec m (fun a _ ih => a :: ih) l
def hit (a c : ℕ) (l : List (ℕ × ℕ)) : Bool :=
  List.rec true (fun p _ ih => cond (cond (Nat.beq p.1 a) true (cond (Nat.beq p.2 a) true
    (cond (Nat.beq p.1 c) true (Nat.beq p.2 c)))) ih false) l

def sp (T M k w : ℕ) : ℕ :=
  cond (Nat.beq k 0) (Nat.land (Nat.land w M) (Nat.xor (Nat.shiftRight w T) M))
    (Nat.land (Nat.xor w (Nat.shiftRight w T)) M)

def occ1 (s o1 o2 o3 : ℕ) (ih : ℕ → ℕ → ℕ → Bool) : Bool :=
  ih (Nat.lor o1 s) (Nat.lor o2 (Nat.land o1 s)) (Nat.lor o3 (Nat.land o2 s))
def occ (T M k : ℕ) (q : ℕ → ℕ → ℕ → Bool) (l : List ℕ) : ℕ → ℕ → ℕ → Bool :=
  List.rec (fun o1 o2 o3 => q o1 o2 o3) (fun w _ ih o1 o2 o3 => occ1 (sp T M k w) o1 o2 o3 ih) l

def gv (T M G k e w : ℕ) : ℕ := Nat.land (Nat.add (Nat.land (sp T M k w) e) M) G
def gl (T M G k e : ℕ) (l : List ℕ) : List (ℕ × ℕ) :=
  List.rec [] (fun w _ ih => (w, gv T M G k e w) :: ih) l
def cfl (P r : ℕ) : Bool := cond (Nat.ble P r) (cond (Nat.beq (Nat.mod r P) 0) false true) false
def ed1 (P w g : ℕ) (l : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  List.rec [] (fun h _ ih => cond (cfl P (Nat.land g h.2)) ((w, h.1) :: ih) ih) l
def ed (P : ℕ) (l : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  List.rec [] (fun h t ih => capp ih (ed1 P h.1 h.2 t)) l

abbrev Pf := List (ℕ × ℕ × ℕ × ℕ)
abbrev Sty := ℕ → ℕ → ℕ → List ℕ → List ℕ → ℕ → List ℕ → Bool → ℕ → ℕ → List (ℕ × ℕ) → Pf → Bool

def nd3 (S : Sty) (k b sl : ℕ) (pf : Pf) (A T' : List ℕ) (c : ℕ) (B : List ℕ) (nt : Bool)
    (e1 e2 : ℕ) (K : List (ℕ × ℕ)) : Bool :=
  cond (cond (Nat.beq sl 0) (ne K) false) true (S k b sl A T' c B nt e1 e2 K pf)
def nd2 (T M G P : ℕ) (S : Sty) (k b sl : ℕ) (pf : Pf) (A T' : List ℕ) (c : ℕ) (B : List ℕ) (nt : Bool)
    (L : List ℕ) (e1 e2 : ℕ) : Bool :=
  nd3 S k b sl pf A T' c B nt e1 e2 (ed P (gl T M G k e1 L))
def nd1 (T M G P : ℕ) (S : Sty) (k b sl : ℕ) (pf : Pf) (A T' : List ℕ) (c : ℕ) (B : List ℕ) (nt : Bool)
    (L : List ℕ) : Bool :=
  occ T M k (fun o1 o2 o3 => cond (Nat.beq o1 M)
    (nd2 T M G P S k b sl pf A T' c B nt L (Nat.xor o1 o2) (Nat.xor o2 o3)) true) L 0 0 0
def nd (T M G P : ℕ) (S : Sty) (k b sl : ℕ) (pf : Pf) (A T' : List ℕ) (c : ℕ) (B : List ℕ) (nt : Bool) : Bool :=
  nd1 T M G P S k b sl pf A T' c B nt (cat (c :: B) A)

def nh (T M G P : ℕ) (S : Sty) (k b sl : ℕ) (pf : Pf) (A B : List ℕ) : Bool :=
  List.rec true (fun c' B' _ => nd T M G P S k b sl pf A A c' B' true) B

def wf (ta tc tu h : Bool) (sl : ℕ) (kb ka kc k0 : Bool) : Bool :=
  cond (cond ta (cond tc (cond tu k0 true) true) true)
    (cond (Nat.beq sl 0) true
      (cond (cond (Nat.beq sl 1) h true)
        (cond (cond ta ka true) (cond (cond tc kc true)
          (cond (Nat.beq sl 1) true (cond (cond (Nat.beq sl 2) h true) kb true)) false) false) true)) false

def wd (T M G P : ℕ) (S : Sty) (k b sl : ℕ) (A T1 T2 : List ℕ) (a c : ℕ) (B : List ℕ)
    (K : List (ℕ × ℕ)) (pf : Pf) (w : ℕ) (ta tc tu : Bool) : Bool :=
  cond (cond (Nat.ble 2 sl) true (cond ta true tc))
    (cond (mem w A) true (cond (Nat.beq w c) true (cond (mem w B) true
      (wf ta tc tu (hit a c K) sl
        (nd T M G P S k b (Nat.sub sl 2) pf A T1 c (cat [w] B) false)
        (nd T M G P S k b (Nat.sub sl 1) pf (del a A) T2 c (cat [w] B) false)
        (nh T M G P S k b (Nat.sub sl 1) pf A (cat [w] B))
        (nh T M G P S k b sl pf (del a A) (cat [w] B)))))) true

def sub (e s : ℕ) : Bool := Nat.beq (Nat.land s e) e
def we1 (T M G P : ℕ) (S : Sty) (k b sl : ℕ) (A T1 T2 : List ℕ) (a c : ℕ) (B : List ℕ)
    (K : List (ℕ × ℕ)) (pf : Pf) (ea ec u w sw : ℕ) : Bool :=
  wd T M G P S k b sl A T1 T2 a c B K pf w (sub ea sw) (sub ec sw) (sub u sw)
def we (T M G P : ℕ) (S : Sty) (k b sl : ℕ) (A T1 T2 : List ℕ) (a c : ℕ) (B : List ℕ) (e2 : ℕ)
    (K : List (ℕ × ℕ)) (pf : Pf) (ea ec op w : ℕ) : Bool :=
  we1 T M G P S k b sl A T1 T2 a c B K ((op, a, c, w) :: pf) ea ec
    (Nat.land e2 (Nat.land (sp T M k a) (sp T M k c))) w (sp T M k w)

def orB (Xt b a c : ℕ) (f : ℕ → Bool) : Bool :=
  cond (cond (Nat.beq a Xt) true (Nat.beq c Xt)) (cond (Nat.beq b 0) true (f (Nat.pred b))) (f b)

def pr (T M G P Xt : ℕ) (S : Sty) (k b sl : ℕ) (A T1 T2 : List ℕ) (a c : ℕ) (B : List ℕ) (e2 : ℕ)
    (K : List (ℕ × ℕ)) (pf : Pf) (ea ec : ℕ) : Bool :=
  cond (we T M G P S k b sl A T1 T2 a c B e2 K pf ea ec 0 (Nat.land a c))
    (orB Xt b a c fun b' => we T M G P S k b' sl A T1 T2 a c B e2 K pf ea ec 1 (Nat.lor a c)) false

def nt1 (T M G P : ℕ) (S : Sty) (k b sl : ℕ) (A T1 : List ℕ) (c : ℕ) (B : List ℕ) (pf : Pf) (w : ℕ) : Bool :=
  cond (mem w A) true (cond (Nat.beq w c) true (cond (mem w B) true
    (cond (nh T M G P S (Nat.pred k) b sl ((2, c, c, w) :: pf) A (cat [w] B))
      (cond (Nat.beq sl 0) true
        (nd T M G P S (Nat.pred k) b (Nat.pred sl) ((2, c, c, w) :: pf) A T1 c (cat [w] B) false)) false)))

def Lv (T M G P MM Xt : ℕ) (C : Sty) (fu : ℕ) : Sty :=
  Nat.rec (fun _ _ _ _ _ _ _ _ _ _ _ _ => false) (fun _ S k b sl A T1 c B nt e1 e2 K pf =>
   cond nt (cond (cond (Nat.beq k 0) true (nt1 T M G P C k b sl A T1 c B pf (Nat.xor c MM)))
     (S k b sl A T1 c B false e1 e2 K pf) false) <|
   List.rec
    (List.rec true (fun c' B' _ => S k b sl (cat [c] A) (cat [c] A) c' B' true e1 e2 K pf) B)
    (fun a T2 _ =>
     cond (pr T M G P Xt C k b sl A T1 T2 a c B e2 K pf (Nat.land e1 (sp T M k a)) (Nat.land e1 (sp T M k c)))
       (S k b sl A T2 c B nt e1 e2 K pf) false) T1) fu

def Sr (T M G P MM Xt : ℕ) (ck : Pf → Bool) (n : ℕ) : Sty :=
  Nat.rec (fun _ _ _ _ _ _ _ _ _ _ _ pf => ck pf) (fun _ ih => Lv T M G P MM Xt ih 200) n

def hd (N : ℕ) (pf : Pf) : ℕ := List.rec 0 (fun e _ _ => Nat.mod e.2.2.2 N) pf
def Ft (N i : ℕ) (C : Sty) : Sty := fun k b sl A T1 c B nt e1 e2 K pf =>
  cond (Nat.beq (hd N pf) i) (C k b sl A T1 c B nt e1 e2 K pf) true

-- list helper facts
theorem beqf {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  rw [← Bool.not_eq_true, Nat.beq_eq]; exact h

theorem mem_iff (w : ℕ) (l : List ℕ) : mem w l = true ↔ w ∈ l := by
  induction l with
  | nil => simp [mem]
  | cons a l ih =>
    have h : mem w (a :: l) = cond (Nat.beq a w) true (mem w l) := rfl
    rw [h]
    by_cases e : a = w
    · subst e; simp
    · have : Nat.beq a w = false := beqf e
      rw [this, Bool.cond_false, ih]
      have e' : w ≠ a := fun h => e h.symm
      simp [e']

theorem del_eq (w : ℕ) (l : List ℕ) : del w l = l.erase w := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have h : del w (a :: l) = cond (Nat.beq a w) l (a :: del w l) := rfl
    rw [h]
    by_cases e : a = w
    · subst e; simp
    · have : Nat.beq a w = false := beqf e
      rw [this, Bool.cond_false, ih, List.erase_cons_tail (by simpa using e)]

theorem cat_eq (m l : List ℕ) : cat m l = l ++ m := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have h : cat m (a :: l) = a :: cat m l := rfl
    rw [h, ih, List.cons_append]

theorem capp_eq (m l : List (ℕ × ℕ)) : capp m l = l ++ m := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have h : capp m (a :: l) = a :: capp m l := rfl
    rw [h, ih, List.cons_append]

theorem hit_of (a c : ℕ) (l : List (ℕ × ℕ))
    (h : ∀ p ∈ l, p.1 = a ∨ p.2 = a ∨ p.1 = c ∨ p.2 = c) : hit a c l = true := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    have e : hit a c (p :: l) = cond (cond (Nat.beq p.1 a) true (cond (Nat.beq p.2 a) true
      (cond (Nat.beq p.1 c) true (Nat.beq p.2 c)))) (hit a c l) false := rfl
    rw [e, ih (fun q hq => h q (List.mem_cons_of_mem _ hq))]
    have := h p List.mem_cons_self
    rcases this with h | h | h | h <;> simp [h]

theorem nodup_sub_len {l m : List ℕ} (h : l.Nodup) (s : ∀ z ∈ l, z ∈ m) : l.length ≤ m.length :=
  (List.subperm_of_subset h s).length_le

theorem two_le_countP {l : List ℕ} {p : ℕ → Bool} {a b : ℕ} (hab : a ≠ b)
    (ha : a ∈ l) (hb : b ∈ l) (pa : p a = true) (pb : p b = true) : 2 ≤ l.countP p := by
  rw [List.countP_eq_length_filter]
  have : [a, b].length ≤ (l.filter p).length := nodup_sub_len (by simp [hab]) (by
    intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl <;> simp [*])
  simpa using this

theorem three_le_countP {l : List ℕ} {p : ℕ → Bool} {a b c : ℕ} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (ha : a ∈ l) (hb : b ∈ l) (hc : c ∈ l)
    (pa : p a = true) (pb : p b = true) (pc : p c = true) : 3 ≤ l.countP p := by
  rw [List.countP_eq_length_filter]
  have : [a, b, c].length ≤ (l.filter p).length := nodup_sub_len (by simp [hab, hac, hbc]) (by
    intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl <;> simp [*])
  simpa using this

-- occurrence counting
theorem occ_spec (T M k : ℕ) (l : List ℕ) : ∀ (o1 o2 o3 : ℕ) (cn : ℕ → ℕ),
    (∀ p, o1.testBit p = decide (1 ≤ cn p)) → (∀ p, o2.testBit p = decide (2 ≤ cn p)) →
    (∀ p, o3.testBit p = decide (3 ≤ cn p)) →
    ∃ r1 r2 r3, (∀ q, occ T M k q l o1 o2 o3 = q r1 r2 r3) ∧
      (∀ p, r1.testBit p = decide (1 ≤ cn p + l.countP (fun w => (sp T M k w).testBit p))) ∧
      (∀ p, r2.testBit p = decide (2 ≤ cn p + l.countP (fun w => (sp T M k w).testBit p))) ∧
      (∀ p, r3.testBit p = decide (3 ≤ cn p + l.countP (fun w => (sp T M k w).testBit p))) := by
  induction l with
  | nil => intro o1 o2 o3 cn h1 h2 h3; exact ⟨o1, o2, o3, fun _ => rfl, by simpa using h1, by simpa using h2, by simpa using h3⟩
  | cons w l ih =>
    intro o1 o2 o3 cn h1 h2 h3
    obtain ⟨r1, r2, r3, hr, a1, a2, a3⟩ := ih (Nat.lor o1 (sp T M k w))
      (Nat.lor o2 (Nat.land o1 (sp T M k w))) (Nat.lor o3 (Nat.land o2 (sp T M k w)))
      (fun p => cn p + if (sp T M k w).testBit p then 1 else 0)
      (by
        intro p
        show (o1 ||| sp T M k w).testBit p = _
        rw [Nat.testBit_or, h1]
        cases (sp T M k w).testBit p <;> simp)
      (by
        intro p
        show (o2 ||| (o1 &&& sp T M k w)).testBit p = _
        rw [Nat.testBit_or, Nat.testBit_and, h1, h2]
        cases (sp T M k w).testBit p
        · simp
        · simp; by_cases h : 2 ≤ cn p <;> by_cases h' : 1 ≤ cn p <;> simp [h, h'] <;> omega)
      (by
        intro p
        show (o3 ||| (o2 &&& sp T M k w)).testBit p = _
        rw [Nat.testBit_or, Nat.testBit_and, h2, h3]
        cases (sp T M k w).testBit p
        · simp
        · simp; by_cases h : 3 ≤ cn p <;> by_cases h' : 2 ≤ cn p <;> simp [h, h'] <;> omega)
    have key : ∀ p, (cn p + if (sp T M k w).testBit p then 1 else 0) +
        l.countP (fun w => (sp T M k w).testBit p) =
        cn p + (w :: l).countP (fun w => (sp T M k w).testBit p) := by
      intro p
      rw [List.countP_cons]
      cases (sp T M k w).testBit p <;> simp <;> omega
    exact ⟨r1, r2, r3, hr, fun p => by rw [a1 p, key], fun p => by rw [a2 p, key], fun p => by rw [a3 p, key]⟩

theorem occ_zero (T M k : ℕ) (l : List ℕ) :
    ∃ r1 r2 r3, (∀ q, occ T M k q l 0 0 0 = q r1 r2 r3) ∧
      (∀ p, r1.testBit p = decide (1 ≤ l.countP (fun w => (sp T M k w).testBit p))) ∧
      (∀ p, r2.testBit p = decide (2 ≤ l.countP (fun w => (sp T M k w).testBit p))) ∧
      (∀ p, r3.testBit p = decide (3 ≤ l.countP (fun w => (sp T M k w).testBit p))) := by
  have := occ_spec T M k l 0 0 0 (fun _ => 0) (by simp) (by simp) (by simp)
  simpa using this

theorem sp_sub (T M k w p : ℕ) (h : (sp T M k w).testBit p = true) : M.testBit p = true := by
  unfold sp at h
  cases hk : Nat.beq k 0 <;> rw [hk] at h
  · change ((w ^^^ (w >>> T)) &&& M).testBit p = true at h
    rw [Nat.testBit_and] at h; simp at h; exact h.2
  · change ((w &&& M) &&& ((w >>> T) ^^^ M)).testBit p = true at h
    rw [Nat.testBit_and, Nat.testBit_and] at h; simp at h; exact h.1.2

theorem sub_of (e s : ℕ) (h : ∀ p, e.testBit p = true → s.testBit p = true) : sub e s = true := by
  unfold sub
  have : Nat.land s e = e := by
    apply Nat.eq_of_testBit_eq
    intro p
    change (s &&& e).testBit p = _
    rw [Nat.testBit_and]
    cases he : e.testBit p
    · simp
    · simp [h p he]
  rw [this]; simp

theorem ed1_mem (P w g : ℕ) (l : List (ℕ × ℕ)) (e : ℕ × ℕ) (h : e ∈ ed1 P w g l) :
    e.1 = w ∧ ∃ h2 ∈ l, e.2 = h2.1 ∧ cfl P (Nat.land g h2.2) = true := by
  induction l with
  | nil => simp [ed1] at h
  | cons x l ih =>
    have e1 : ed1 P w g (x :: l) = cond (cfl P (Nat.land g x.2)) ((w, x.1) :: ed1 P w g l) (ed1 P w g l) := rfl
    rw [e1] at h
    cases hc : cfl P (Nat.land g x.2) <;> rw [hc] at h
    · obtain ⟨a, h2, b, c⟩ := ih h
      exact ⟨a, h2, List.mem_cons_of_mem _ b, c⟩
    · rcases List.mem_cons.1 h with rfl | h
      · exact ⟨rfl, x, List.mem_cons_self, rfl, hc⟩
      · obtain ⟨a, h2, b, c⟩ := ih h
        exact ⟨a, h2, List.mem_cons_of_mem _ b, c⟩

theorem ed_mem (P : ℕ) (l : List (ℕ × ℕ)) (hl : (l.map Prod.fst).Nodup) (e : ℕ × ℕ) (h : e ∈ ed P l) :
    e.1 ≠ e.2 ∧ ∃ x ∈ l, ∃ y ∈ l, e.1 = x.1 ∧ e.2 = y.1 ∧ cfl P (Nat.land x.2 y.2) = true := by
  induction l with
  | nil => simp [ed] at h
  | cons x l ih =>
    have e1 : ed P (x :: l) = capp (ed P l) (ed1 P x.1 x.2 l) := rfl
    rw [e1, capp_eq, List.mem_append] at h
    rw [List.map_cons, List.nodup_cons] at hl
    rcases h with h | h
    · obtain ⟨a, y, b, c, d⟩ := ed1_mem _ _ _ _ _ h
      refine ⟨?_, x, List.mem_cons_self, y, List.mem_cons_of_mem _ b, a, c, d⟩
      rw [a, c]; intro he; exact hl.1 (he ▸ List.mem_map_of_mem b)
    · obtain ⟨n, a, b, c, d, e, f, g⟩ := ih hl.2 h
      exact ⟨n, a, List.mem_cons_of_mem _ b, c, List.mem_cons_of_mem _ d, e, f, g⟩

theorem gl_eq (T M G k e : ℕ) (l : List ℕ) : gl T M G k e l = l.map (fun w => (w, gv T M G k e w)) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have h : gl T M G k e (a :: l) = (a, gv T M G k e a) :: gl T M G k e l := rfl
    rw [h, ih, List.map_cons]

section Core
variable (val : ℕ → (Fin 7 → Bool) → Bool) (op l r : ℕ → ℕ) (F : ℕ)
variable (T M MM Xt : ℕ) (xr yr : ℕ → Fin 7 → Bool)

def Sem (z : ℕ) : Prop := ∀ p, M.testBit p = true →
  z.testBit p = val z (xr p) ∧ z.testBit (T + p) = val z (yr p)

def GateOk (w : ℕ) : Prop :=
  (op w = 0 ∧ w = Nat.land (l w) (r w) ∧ (∀ x, val w x = (val (l w) x && val (r w) x)) ∧ l w ≠ r w) ∨
  (op w = 1 ∧ w = Nat.lor (l w) (r w) ∧ (∀ x, val w x = (val (l w) x || val (r w) x)) ∧ l w ≠ r w) ∨
  (op w = 2 ∧ w = Nat.xor (l w) MM ∧ (∀ x, val w x = !val (l w) x) ∧ r w = l w)

def Valid : List ℕ → List ℕ → Prop
  | _, [] => True
  | L, w :: t => l w ∈ L ∧ r w ∈ L ∧ Valid (w :: L) t

def Used (z : ℕ) (rest : List ℕ) : Prop := z = F ∨ ∃ w ∈ rest, l w = z ∨ r w = z

def cN (rest : List ℕ) : ℕ := rest.countP (fun w => Nat.beq (op w) 2)
def cO (rest : List ℕ) : ℕ :=
  rest.countP (fun w => Nat.beq (op w) 1 && (Nat.beq (l w) Xt || Nat.beq (r w) Xt))

def Inv (L rest : List ℕ) (k b : ℕ) : Prop :=
  Valid l r L rest ∧ (L ++ rest).Nodup ∧ (∀ z ∈ L ++ rest, Sem val T M xr yr z) ∧
  (∀ w ∈ rest, GateOk val op l r MM w) ∧ (∀ z ∈ L ++ rest, Used l r F z rest) ∧ F ∈ L ++ rest ∧
  k = cN op rest ∧ cO op l r Xt rest ≤ b

variable {val op l r F T M MM Xt xr yr}

theorem Valid.mono {rest : List ℕ} : ∀ {L L' : List ℕ}, (∀ z ∈ L, z ∈ L') → Valid l r L rest → Valid l r L' rest := by
  induction rest with
  | nil => intro L L' _ _; trivial
  | cons w t ih =>
    intro L L' h ⟨a, b, c⟩
    refine ⟨h _ a, h _ b, ih ?_ c⟩
    intro z hz
    rcases List.mem_cons.1 hz with rfl | hz
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (h z hz)

theorem Valid.restrict {rest : List ℕ} : ∀ {L L' : List ℕ},
    (∀ z ∈ L, (∃ w ∈ rest, l w = z ∨ r w = z) → z ∈ L') → Valid l r L rest → Valid l r L' rest := by
  induction rest with
  | nil => intro L L' _ _; trivial
  | cons w t ih =>
    intro L L' h ⟨a, b, c⟩
    refine ⟨h _ a ⟨w, List.mem_cons_self, Or.inl rfl⟩, h _ b ⟨w, List.mem_cons_self, Or.inr rfl⟩, ih ?_ c⟩
    intro z hz ⟨w', hw', hu⟩
    rcases List.mem_cons.1 hz with rfl | hz
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (h z hz ⟨w', List.mem_cons_of_mem _ hw', hu⟩)

theorem Valid.front {w : ℕ} {rest : List ℕ} : ∀ {L : List ℕ}, w ∈ rest → l w ∈ L → r w ∈ L →
    Valid l r L rest → Valid l r (w :: L) (rest.erase w) := by
  induction rest with
  | nil => intro L h; simp at h
  | cons v t ih =>
    intro L hw ha hb ⟨a, b, c⟩
    by_cases e : v = w
    · subst e; rw [List.erase_cons_head]; exact c
    · rw [List.erase_cons_tail (by simpa using e)]
      have hwt : w ∈ t := by
        rcases List.mem_cons.1 hw with h | h
        · exact absurd h.symm e
        · exact h
      refine ⟨List.mem_cons_of_mem _ a, List.mem_cons_of_mem _ b, ?_⟩
      refine Valid.mono ?_ (ih (L := v :: L) hwt (List.mem_cons_of_mem _ ha) (List.mem_cons_of_mem _ hb) c)
      intro z hz
      simp only [List.mem_cons] at hz ⊢
      tauto

theorem erase_perm {w : ℕ} {rest : List ℕ} (h : w ∈ rest) : rest.Perm (w :: rest.erase w) :=
  List.perm_cons_erase h

theorem GateOk.ops {w : ℕ} (h : GateOk val op l r MM w) : op w = 0 ∨ op w = 1 ∨ op w = 2 := by
  rcases h with h | h | h
  · exact Or.inl h.1
  · exact Or.inr (Or.inl h.1)
  · exact Or.inr (Or.inr h.1)

theorem Inv.step {L rest : List ℕ} {k b : ℕ} (H : Inv val op l r F T M MM Xt xr yr L rest k b)
    {w : ℕ} (hw : w ∈ rest) (ha : l w ∈ L) (hb : r w ∈ L) {L' : List ℕ} (nd' : L'.Nodup)
    (hL : ∀ z, z ∈ L' ↔ (z ∈ L ∨ z = w) ∧ Used l r F z (rest.erase w)) :
    Inv val op l r F T M MM Xt xr yr L' (rest.erase w) (k - (if op w = 2 then 1 else 0))
      (b - (if op w = 1 ∧ (l w = Xt ∨ r w = Xt) then 1 else 0)) ∧ w ∈ L' ∧
      (if op w = 2 then 1 else 0) ≤ k ∧ (if op w = 1 ∧ (l w = Xt ∨ r w = Xt) then 1 else 0) ≤ b := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := H
  have pm := erase_perm hw
  have nr : rest.Nodup := (List.nodup_append.1 h2).2.1
  have dj : ∀ z ∈ L, z ∉ rest := fun z hz hr => (List.nodup_append.1 h2).2.2 z hz z hr rfl
  have nw : w ∉ rest.erase w := by
    intro h; exact (List.nodup_cons.1 (pm.nodup_iff.1 nr)).1 h
  have hmem : ∀ z, z ∈ rest ↔ z = w ∨ z ∈ rest.erase w := by
    intro z; rw [pm.mem_iff, List.mem_cons]
  have usedE : ∀ z ∈ rest, Used l r F z (rest.erase w) := by
    intro z hz
    rcases h5 z (List.mem_append_right _ hz) with h | ⟨v, hv, hu⟩
    · exact Or.inl h
    · refine Or.inr ⟨v, ?_, hu⟩
      rcases (hmem v).1 hv with rfl | h
      · exfalso
        rcases hu with rfl | rfl
        · exact dj _ ha hz
        · exact dj _ hb hz
      · exact h
  have wL : w ∈ L' := (hL w).2 ⟨Or.inr rfl, usedE w hw⟩
  have c1 : cN op rest = (if op w = 2 then 1 else 0) + cN op (rest.erase w) := by
    unfold cN; rw [pm.countP_eq, List.countP_cons]
    by_cases h : op w = 2
    · simp [h]; omega
    · simp [h]
  have c2 : cO op l r Xt rest = (if op w = 1 ∧ (l w = Xt ∨ r w = Xt) then 1 else 0) +
      cO op l r Xt (rest.erase w) := by
    unfold cO; rw [pm.countP_eq, List.countP_cons]
    by_cases h : op w = 1 ∧ (l w = Xt ∨ r w = Xt)
    · simp [h]; omega
    · simp [h]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, wL, ?_, ?_⟩
  · refine Valid.restrict ?_ (Valid.front hw ha hb h1)
    intro z hz hu
    refine (hL z).2 ⟨?_, Or.inr hu⟩
    rcases List.mem_cons.1 hz with h | h
    · exact Or.inr h
    · exact Or.inl h
  · rw [List.nodup_append]
    refine ⟨nd', nr.erase _, ?_⟩
    rintro z hz z' hz' rfl
    rcases ((hL z).1 hz).1 with h | rfl
    · exact dj z h ((hmem z).2 (Or.inr hz'))
    · exact nw hz'
  · intro z hz
    apply h3
    rcases List.mem_append.1 hz with h | h
    · rcases ((hL z).1 h).1 with h | rfl
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ hw
    · exact List.mem_append_right _ ((hmem z).2 (Or.inr h))
  · exact fun v hv => h4 v ((hmem v).2 (Or.inr hv))
  · intro z hz
    rcases List.mem_append.1 hz with h | h
    · exact ((hL z).1 h).2
    · exact usedE z ((hmem z).2 (Or.inr h))
  · rcases List.mem_append.1 h6 with h | h
    · exact List.mem_append_left _ ((hL F).2 ⟨Or.inl h, Or.inl rfl⟩)
    · rcases (hmem F).1 h with h | h
      · exact List.mem_append_left _ ((hL F).2 ⟨Or.inr h, Or.inl rfl⟩)
      · exact List.mem_append_right _ h
  · omega
  · omega
  · omega
  · omega

open Classical in
theorem Inv.next {L rest : List ℕ} {k b : ℕ} (H : Inv val op l r F T M MM Xt xr yr L rest k b)
    {w : ℕ} (hw : w ∈ rest) : ∃ L' : List ℕ, L'.Nodup ∧
    (∀ z, z ∈ L' ↔ (z ∈ L ∨ z = w) ∧ Used l r F z (rest.erase w)) := by
  have dj : ∀ z ∈ L, z ∉ rest := fun z hz hr => (List.nodup_append.1 H.2.1).2.2 z hz z hr rfl
  refine ⟨(w :: L).filter (fun z => decide (Used l r F z (rest.erase w))), ?_, ?_⟩
  · apply List.Nodup.filter
    exact List.nodup_cons.2 ⟨fun h => dj w h hw, (List.nodup_append.1 H.2.1).1⟩
  · intro z
    rw [List.mem_filter, List.mem_cons, decide_eq_true_eq]
    tauto

theorem Inv.len_step {L rest : List ℕ} {k b : ℕ} (H : Inv val op l r F T M MM Xt xr yr L rest k b)
    {w : ℕ} (hw : w ∈ rest) {L' : List ℕ} (wL : w ∈ L')
    (hL : ∀ z, z ∈ L' ↔ (z ∈ L ∨ z = w) ∧ Used l r F z (rest.erase w)) :
    (∀ z ∈ w :: L, z ∈ l w :: r w :: L') ∧ (w :: L).Nodup := by
  have dj : ∀ z ∈ L, z ∉ rest := fun z hz hr => (List.nodup_append.1 H.2.1).2.2 z hz z hr rfl
  constructor
  · intro z hz
    rcases List.mem_cons.1 hz with rfl | hz
    · simp [wL]
    · by_cases h1 : z = l w
      · simp [h1]
      · by_cases h2 : z = r w
        · simp [h2]
        · simp only [List.mem_cons]
          refine Or.inr (Or.inr ((hL z).2 ⟨Or.inl hz, ?_⟩))
          rcases H.2.2.2.2.1 z (List.mem_append_left _ hz) with h | ⟨v, hv, hu⟩
          · exact Or.inl h
          · refine Or.inr ⟨v, ?_, hu⟩
            rcases List.mem_cons.1 ((erase_perm hw).mem_iff.1 hv) with rfl | h
            · rcases hu with h | h
              · exact absurd h.symm h1
              · exact absurd h.symm h2
            · exact h
  · exact List.nodup_cons.2 ⟨fun h => dj w h hw, (List.nodup_append.1 H.2.1).1⟩

theorem Inv.size : ∀ (n : ℕ) {L rest : List ℕ} {k b : ℕ}, rest.length = n →
    Inv val op l r F T M MM Xt xr yr L rest k b → L.length + k ≤ rest.length + 1 := by
  intro n
  induction n with
  | zero =>
    intro L rest k b hn H
    obtain rfl := List.length_eq_zero_iff.1 hn
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := H
    have : L.length ≤ [F].length := nodup_sub_len (List.nodup_append.1 h2).1 (by
      intro z hz
      rcases h5 z (List.mem_append_left _ hz) with h | ⟨w, hw, _⟩
      · simp [h]
      · simp at hw)
    have hk : k = 0 := by rw [h7]; rfl
    simp at this
    simp [hk]; omega
  | succ n ih =>
    intro L rest k b hn H
    obtain ⟨w, t, rfl⟩ : ∃ w t, rest = w :: t := by
      cases rest with
      | nil => simp at hn
      | cons w t => exact ⟨w, t, rfl⟩
    have hw : w ∈ w :: t := List.mem_cons_self
    obtain ⟨L', nd', hL⟩ := H.next hw
    obtain ⟨H', wL, hk, _⟩ := H.step hw H.1.1 H.1.2.1 nd' hL
    obtain ⟨hs, hd⟩ := H.len_step hw wL hL
    have e : (w :: t).erase w = t := List.erase_cons_head ..
    rw [e] at H' hL
    have hl := ih (by simpa using hn) H'
    simp only [List.length_cons] at hn ⊢
    by_cases h2 : op w = 2
    · have hg := H.2.2.2.1 w hw
      have hr : r w = l w := by
        rcases hg with h | h | h
        · exact absurd h.1 (by omega)
        · exact absurd h.1 (by omega)
        · exact h.2.2.2
      have : (w :: L).length ≤ (l w :: L').length := nodup_sub_len hd (by
        intro z hz; have := hs z hz; rw [hr] at this; simpa using this)
      simp only [List.length_cons] at this
      rw [if_pos h2] at hl hk
      omega
    · have : (w :: L).length ≤ (l w :: r w :: L').length := nodup_sub_len hd hs
      simp only [List.length_cons] at this
      rw [if_neg h2] at hl hk
      omega

theorem cov_any {x y : Fin 7 → Bool} : ∀ {rest L : List ℕ}, Valid l r L rest → (∀ w ∈ rest, GateOk val op l r MM w) →
    ∀ z ∈ L ++ rest, val z x ≠ val z y → ∃ z' ∈ L, val z' x ≠ val z' y := by
  intro rest
  induction rest with
  | nil => intro L _ _ z hz h; exact ⟨z, by simpa using hz, h⟩
  | cons w t ih =>
    intro L ⟨a, b, c⟩ hg z hz h
    have hz' : z ∈ (w :: L) ++ t := by simp at hz ⊢; tauto
    obtain ⟨z', hz', h'⟩ := ih c (fun v hv => hg v (List.mem_cons_of_mem _ hv)) z hz' h
    rcases List.mem_cons.1 hz' with rfl | hz'
    · by_contra hn
      push Not at hn
      have ea := hn _ a
      have eb := hn _ b
      apply h'
      rcases hg z' List.mem_cons_self with g | g | g
      · rw [g.2.2.1, g.2.2.1, ea, eb]
      · rw [g.2.2.1, g.2.2.1, ea, eb]
      · rw [g.2.2.1, g.2.2.1, ea]
    · exact ⟨z', hz', h'⟩

theorem cov_pos {x y : Fin 7 → Bool} : ∀ {rest L : List ℕ}, Valid l r L rest → (∀ w ∈ rest, GateOk val op l r MM w) →
    (∀ w ∈ rest, op w ≠ 2) →
    ∀ z ∈ L ++ rest, val z x = true → val z y = false → ∃ z' ∈ L, val z' x = true ∧ val z' y = false := by
  intro rest
  induction rest with
  | nil => intro L _ _ _ z hz h h2; exact ⟨z, by simpa using hz, h, h2⟩
  | cons w t ih =>
    intro L ⟨a, b, c⟩ hg hn z hz h h2
    have hz' : z ∈ (w :: L) ++ t := by simp at hz ⊢; tauto
    obtain ⟨z', hz', h', h2'⟩ := ih c (fun v hv => hg v (List.mem_cons_of_mem _ hv))
      (fun v hv => hn v (List.mem_cons_of_mem _ hv)) z hz' h h2
    rcases List.mem_cons.1 hz' with rfl | hz'
    · rcases hg z' List.mem_cons_self with g | g | g
      · rw [g.2.2.1] at h' h2'
        simp only [Bool.and_eq_true, Bool.and_eq_false_iff] at h' h2'
        rcases h2' with q | q
        · exact ⟨_, a, h'.1, q⟩
        · exact ⟨_, b, h'.2, q⟩
      · rw [g.2.2.1] at h' h2'
        simp only [Bool.or_eq_true, Bool.or_eq_false_iff] at h' h2'
        rcases h' with q | q
        · exact ⟨_, a, q, h2'.1⟩
        · exact ⟨_, b, q, h2'.2⟩
      · exact absurd g.1 (hn z' List.mem_cons_self)
    · exact ⟨z', hz', h', h2'⟩

-- semantic separation used for k pending NOT gates
def Sp (val : ℕ → (Fin 7 → Bool) → Bool) (k : ℕ) (z : ℕ) (x y : Fin 7 → Bool) : Prop :=
  if k = 0 then val z x = true ∧ val z y = false else val z x ≠ val z y

theorem sp_sem {z : ℕ} (h : Sem val T M xr yr z) (k p : ℕ) :
    (sp T M k z).testBit p = true ↔ M.testBit p = true ∧ Sp val k z (xr p) (yr p) := by
  unfold sp Sp
  by_cases hk : k = 0
  · subst hk
    change ((z &&& M) &&& ((z >>> T) ^^^ M)).testBit p = true ↔ _
    rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_shiftRight]
    cases hm : M.testBit p
    · simp
    · obtain ⟨a, b⟩ := h p hm
      rw [a, b]; simp
  · rw [beqf hk, if_neg hk]
    change ((z ^^^ (z >>> T)) &&& M).testBit p = true ↔ _
    rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_shiftRight]
    cases hm : M.testBit p
    · simp
    · obtain ⟨a, b⟩ := h p hm
      rw [a, b]; simp

theorem Inv.noNot {L rest : List ℕ} {b : ℕ} (H : Inv val op l r F T M MM Xt xr yr L rest 0 b) :
    ∀ w ∈ rest, op w ≠ 2 := by
  intro w hw h
  have : 0 < cN op rest := by
    unfold cN; rw [List.countP_pos_iff]; exact ⟨w, hw, by simp [h]⟩
  have := H.2.2.2.2.2.2.1
  omega

theorem Inv.cover {L rest : List ℕ} {k b : ℕ} (H : Inv val op l r F T M MM Xt xr yr L rest k b)
    {x y : Fin 7 → Bool} (hx : val F x = true) (hy : val F y = false) : ∃ z ∈ L, Sp val k z x y := by
  unfold Sp
  by_cases hk : k = 0
  · subst hk
    simp only [if_true]
    exact cov_pos H.1 H.2.2.2.1 H.noNot F H.2.2.2.2.2.1 hx hy
  · simp only [if_neg hk]
    exact cov_any H.1 H.2.2.2.1 F H.2.2.2.2.2.1 (by rw [hx, hy]; simp)

-- read-once form
def RO (val : ℕ → (Fin 7 → Bool) → Bool) (F : ℕ) (L : List ℕ) (k : ℕ) : Prop :=
  ∃ (A : ℕ → ℕ → Prop) (s : ℕ → Bool) (P Q : (Fin 7 → Bool) → ℕ → Prop),
    (∀ x, val F x = true → ∀ i, P x i → i ∈ L ∧ val i x = s i) ∧
    (∀ y, val F y = false → ∀ i, Q y i → i ∈ L ∧ val i y = !s i) ∧
    (∀ x, val F x = true → ∀ i j, i ≠ j → P x i → P x j → A i j) ∧
    (∀ y, val F y = false → ∀ i j, i ≠ j → Q y i → Q y j → ¬ A i j) ∧
    (∀ x y, val F x = true → val F y = false → ∃ i, P x i ∧ Q y i) ∧
    (k = 0 → ∀ i ∈ L, s i = true)

theorem RO.base (L : List ℕ) (k : ℕ) (hF : F ∈ L) (hL : ∀ z ∈ L, z = F) : RO val F L k := by
  refine ⟨fun _ _ => True, fun _ => true, fun _ i => i = F, fun _ i => i = F, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro x hx i rfl; exact ⟨hF, hx⟩
  · rintro x hx i rfl; exact ⟨hF, by simpa using hx⟩
  · intros; trivial
  · rintro y _ i j hij rfl rfl; exact absurd rfl hij
  · intro x y _ _; exact ⟨F, rfl, rfl⟩
  · intros; rfl

theorem RO.bin {L L1 : List ℕ} {k w a c : ℕ} (hac : a ≠ c) (ha : a ∈ L) (hc : c ∈ L) (ha1 : a ∉ L1) (hc1 : c ∉ L1)
    (hsub : ∀ z ∈ L1, z = w ∨ z ∈ L) (hw : w ∉ L) (hw1 : w ∈ L1) (hsup : ∀ z ∈ L, z ≠ a → z ≠ c → z ∈ L1)
    (hg : (∀ x, val w x = (val a x && val c x)) ∨ (∀ x, val w x = (val a x || val c x)))
    (R : RO val F L1 k) : RO val F L k := by
  obtain ⟨A, s, P, Q, h1, h2, h3, h4, h5, h6⟩ := R
  -- v : conjunction in the literal of w
  obtain ⟨v, hv⟩ : ∃ v : Bool, ∀ x, (val w x = s w → (v = true → val a x = s w ∧ val c x = s w) ∧
      (v = false → val a x = s w ∨ val c x = s w)) ∧ (val w x = !s w →
      (v = true → val a x = (!s w) ∨ val c x = (!s w)) ∧ (v = false → val a x = (!s w) ∧ val c x = (!s w))) := by
    rcases hg with hg | hg
    · refine ⟨s w, fun x => ?_⟩
      rw [hg x]
      cases val a x <;> cases val c x <;> cases s w <;> simp
    · refine ⟨!s w, fun x => ?_⟩
      rw [hg x]
      cases val a x <;> cases val c x <;> cases s w <;> simp
  let φ : ℕ → ℕ := fun z => if z = a ∨ z = c then w else z
  have φa : φ a = w := by simp [φ]
  have φc : φ c = w := by simp [φ]
  have φo : ∀ z, z ≠ a → z ≠ c → φ z = z := by intro z h h'; simp [φ, h, h']
  have wa : w ≠ a := fun h => hw (h ▸ ha)
  have wc : w ≠ c := fun h => hw (h ▸ hc)
  have nL1 : ∀ z ∈ L1, z ≠ a ∧ z ≠ c := fun z hz => ⟨fun h => ha1 (h ▸ hz), fun h => hc1 (h ▸ hz)⟩
  -- choice sets
  let PP : (Fin 7 → Bool) → ℕ → Prop := fun x i => (i ≠ w ∧ P x i) ∨ (P x w ∧ (i = a ∨ i = c) ∧ val i x = s w ∧
    (v = false → (i = a ∨ val a x ≠ s w)))
  let QQ : (Fin 7 → Bool) → ℕ → Prop := fun y i => (i ≠ w ∧ Q y i) ∨ (Q y w ∧ (i = a ∨ i = c) ∧ val i y = (!s w) ∧
    (v = true → (i = a ∨ val a y ≠ !s w)))
  refine ⟨fun i j => if φ i = φ j then v = true else A (φ i) (φ j), fun z => s (φ z), PP, QQ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro x hx i (⟨hi, hp⟩ | ⟨hp, hi, hval, _⟩)
    · obtain ⟨m, e⟩ := h1 x hx i hp
      have := nL1 i m
      refine ⟨?_, by simp only [φo i this.1 this.2]; exact e⟩
      rcases hsub i m with h | h
      · exact absurd h hi
      · exact h
    · rcases hi with rfl | rfl
      · exact ⟨ha, by simp only [φa]; exact hval⟩
      · exact ⟨hc, by simp only [φc]; exact hval⟩
  · rintro x hx i (⟨hi, hp⟩ | ⟨hp, hi, hval, _⟩)
    · obtain ⟨m, e⟩ := h2 x hx i hp
      have := nL1 i m
      refine ⟨?_, by simp only [φo i this.1 this.2]; exact e⟩
      rcases hsub i m with h | h
      · exact absurd h hi
      · exact h
    · rcases hi with rfl | rfl
      · exact ⟨ha, by simp only [φa]; exact hval⟩
      · exact ⟨hc, by simp only [φc]; exact hval⟩
  · rintro x hx i j hij (⟨hi, hp⟩ | ⟨hp, hi, hval, hone⟩) (⟨hj, hq⟩ | ⟨hq, hj, hval', hone'⟩)
    · have ni := nL1 i (h1 x hx i hp).1
      have nj := nL1 j (h1 x hx j hq).1
      simp only [φo i ni.1 ni.2, φo j nj.1 nj.2]
      rw [if_neg hij]; exact h3 x hx i j hij hp hq
    · have ni := nL1 i (h1 x hx i hp).1
      have : φ j = w := by rcases hj with rfl | rfl <;> simp [φ]
      simp only [φo i ni.1 ni.2, this]
      rw [if_neg hi]; exact h3 x hx i w hi hp hq
    · have nj := nL1 j (h1 x hx j hq).1
      have : φ i = w := by rcases hi with rfl | rfl <;> simp [φ]
      simp only [φo j nj.1 nj.2, this]
      rw [if_neg (Ne.symm hj)]; exact h3 x hx w j (Ne.symm hj) hp hq
    · have e1 : φ i = w := by rcases hi with rfl | rfl <;> simp [φ]
      have e2 : φ j = w := by rcases hj with rfl | rfl <;> simp [φ]
      simp only [e1, e2, if_true]
      cases hvv : v
      · exfalso
        have o1 := hone hvv
        have o2 := hone' hvv
        rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
        · exact hij rfl
        · rcases o2 with h | h
          · exact hac h.symm
          · exact h hval
        · rcases o1 with h | h
          · exact hac h.symm
          · exact h hval'
        · exact hij rfl
      · rfl
  · rintro x hx i j hij (⟨hi, hp⟩ | ⟨hp, hi, hval, hone⟩) (⟨hj, hq⟩ | ⟨hq, hj, hval', hone'⟩)
    · have ni := nL1 i (h2 x hx i hp).1
      have nj := nL1 j (h2 x hx j hq).1
      simp only [φo i ni.1 ni.2, φo j nj.1 nj.2]
      rw [if_neg hij]; exact h4 x hx i j hij hp hq
    · have ni := nL1 i (h2 x hx i hp).1
      have : φ j = w := by rcases hj with rfl | rfl <;> simp [φ]
      simp only [φo i ni.1 ni.2, this]
      rw [if_neg hi]; exact h4 x hx i w hi hp hq
    · have nj := nL1 j (h2 x hx j hq).1
      have : φ i = w := by rcases hi with rfl | rfl <;> simp [φ]
      simp only [φo j nj.1 nj.2, this]
      rw [if_neg (Ne.symm hj)]; exact h4 x hx w j (Ne.symm hj) hp hq
    · have e1 : φ i = w := by rcases hi with rfl | rfl <;> simp [φ]
      have e2 : φ j = w := by rcases hj with rfl | rfl <;> simp [φ]
      simp only [e1, e2, if_true]
      cases hvv : v
      · simp
      · exfalso
        have o1 := hone hvv
        have o2 := hone' hvv
        rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
        · exact hij rfl
        · rcases o2 with h | h
          · exact hac h.symm
          · exact h hval
        · rcases o1 with h | h
          · exact hac h.symm
          · exact h hval'
        · exact hij rfl
  · intro x y hx hy
    obtain ⟨i, hp, hq⟩ := h5 x y hx hy
    by_cases hi : i = w
    · subst hi
      have vx := ((hv x).1 (h1 x hx _ hp).2)
      have vy := ((hv y).2 (h2 y hy _ hq).2)
      cases hvv : v
      · obtain ⟨ya, yc⟩ := vy.2 hvv
        by_cases xa : val a x = s i
        · exact ⟨a, Or.inr ⟨hp, Or.inl rfl, xa, fun _ => Or.inl rfl⟩, Or.inr ⟨hq, Or.inl rfl, ya, fun _ => Or.inl rfl⟩⟩
        · have xc : val c x = s i := (vx.2 hvv).resolve_left xa
          exact ⟨c, Or.inr ⟨hp, Or.inr rfl, xc, fun _ => Or.inr xa⟩,
            Or.inr ⟨hq, Or.inr rfl, yc, fun h => by rw [hvv] at h; exact absurd h (by simp)⟩⟩
      · obtain ⟨xa, xc⟩ := vx.1 hvv
        by_cases ya : val a y = !s i
        · exact ⟨a, Or.inr ⟨hp, Or.inl rfl, xa, fun _ => Or.inl rfl⟩, Or.inr ⟨hq, Or.inl rfl, ya, fun _ => Or.inl rfl⟩⟩
        · have yc : val c y = !s i := (vy.1 hvv).resolve_left ya
          exact ⟨c, Or.inr ⟨hp, Or.inr rfl, xc, fun h => by rw [hvv] at h; exact absurd h (by simp)⟩,
            Or.inr ⟨hq, Or.inr rfl, yc, fun _ => Or.inr ya⟩⟩
    · exact ⟨i, Or.inl ⟨hi, hp⟩, Or.inl ⟨hi, hq⟩⟩
  · intro hk i hi
    by_cases h1a : i = a ∨ i = c
    · have e : φ i = w := by rcases h1a with rfl | rfl <;> simp [φ]
      simp only [e]
      exact h6 hk w hw1
    · push Not at h1a
      simp only [φo i h1a.1 h1a.2]
      exact h6 hk i (hsup i hi h1a.1 h1a.2)

theorem RO.neg {L L1 : List ℕ} {k w a : ℕ} (ha : a ∈ L) (ha1 : a ∉ L1)
    (hsub : ∀ z ∈ L1, z = w ∨ z ∈ L) (hw : w ∉ L)
    (hg : ∀ x, val w x = !val a x) (hk0 : k ≠ 0)
    (R : RO val F L1 (k - 1)) : RO val F L k := by
  obtain ⟨A, s, P, Q, h1, h2, h3, h4, h5, h6⟩ := R
  let φ : ℕ → ℕ := fun z => if z = a then w else z
  have φa : φ a = w := by simp [φ]
  have φo : ∀ z, z ≠ a → φ z = z := by intro z h; simp [φ, h]
  have wa : w ≠ a := fun h => hw (h ▸ ha)
  have nL1 : ∀ z ∈ L1, z ≠ a := fun z hz h => ha1 (h ▸ hz)
  refine ⟨fun i j => A (φ i) (φ j), fun z => if z = a then !s w else s z, fun x i => (i ≠ w ∧ P x i) ∨ (i = a ∧ P x w),
    fun x i => (i ≠ w ∧ Q x i) ∨ (i = a ∧ Q x w), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro x hx i (⟨hi, hp⟩ | ⟨rfl, hp⟩)
    · obtain ⟨m, e⟩ := h1 x hx i hp
      refine ⟨(hsub i m).resolve_left hi, ?_⟩
      simp only [if_neg (nL1 i m)]; exact e
    · refine ⟨ha, ?_⟩
      have := (h1 x hx w hp).2
      rw [hg] at this
      simp only [if_true]; rw [← this]; simp
  · rintro x hx i (⟨hi, hp⟩ | ⟨rfl, hp⟩)
    · obtain ⟨m, e⟩ := h2 x hx i hp
      refine ⟨(hsub i m).resolve_left hi, ?_⟩
      simp only [if_neg (nL1 i m)]; exact e
    · refine ⟨ha, ?_⟩
      have := (h2 x hx w hp).2
      rw [hg] at this
      simp only [if_true]; rw [← this]; simp
  · rintro x hx i j hij (⟨hi, hp⟩ | ⟨rfl, hp⟩) (⟨hj, hq⟩ | ⟨rfl, hq⟩)
    · rw [φo i (nL1 i (h1 x hx i hp).1), φo j (nL1 j (h1 x hx j hq).1)]; exact h3 x hx i j hij hp hq
    · rw [φo i (nL1 i (h1 x hx i hp).1), φa]; exact h3 x hx i w hi hp hq
    · rw [φo j (nL1 j (h1 x hx j hq).1), φa]; exact h3 x hx w j (Ne.symm hj) hp hq
    · exact absurd rfl hij
  · rintro x hx i j hij (⟨hi, hp⟩ | ⟨rfl, hp⟩) (⟨hj, hq⟩ | ⟨rfl, hq⟩)
    · show ¬ A (φ i) (φ j); rw [φo i (nL1 i (h2 x hx i hp).1), φo j (nL1 j (h2 x hx j hq).1)]; exact h4 x hx i j hij hp hq
    · show ¬ A (φ i) (φ j); rw [φo i (nL1 i (h2 x hx i hp).1), φa]; exact h4 x hx i w hi hp hq
    · show ¬ A (φ i) (φ j); rw [φo j (nL1 j (h2 x hx j hq).1), φa]; exact h4 x hx w j (Ne.symm hj) hp hq
    · exact absurd rfl hij
  · intro x y hx hy
    obtain ⟨i, hp, hq⟩ := h5 x y hx hy
    by_cases hi : i = w
    · subst hi; exact ⟨a, Or.inr ⟨rfl, hp⟩, Or.inr ⟨rfl, hq⟩⟩
    · exact ⟨i, Or.inl ⟨hi, hp⟩, Or.inl ⟨hi, hq⟩⟩
  · intro h; exact absurd h hk0

theorem Inv.tight : ∀ (n : ℕ) {L rest : List ℕ} {k b : ℕ}, rest.length = n →
    Inv val op l r F T M MM Xt xr yr L rest k b → L.length + k = rest.length + 1 → RO val F L k := by
  intro n
  induction n with
  | zero =>
    intro L rest k b hn H _
    obtain rfl := List.length_eq_zero_iff.1 hn
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := H
    refine RO.base L k (by simpa using h6) ?_
    intro z hz
    rcases h5 z (List.mem_append_left _ hz) with h | ⟨w, hw, _⟩
    · exact h
    · simp at hw
  | succ n ih =>
    intro L rest k b hn H ht
    obtain ⟨w, t, rfl⟩ : ∃ w t, rest = w :: t := by
      cases rest with
      | nil => simp at hn
      | cons w t => exact ⟨w, t, rfl⟩
    have hw : w ∈ w :: t := List.mem_cons_self
    obtain ⟨L', nd', hL⟩ := H.next hw
    obtain ⟨H', wL, hk, _⟩ := H.step hw H.1.1 H.1.2.1 nd' hL
    obtain ⟨hs, hd⟩ := H.len_step hw wL hL
    have e : (w :: t).erase w = t := List.erase_cons_head ..
    rw [e] at H' hL
    have hn' : t.length = n := by simpa using hn
    have hl := Inv.size n hn' H'
    have wnL : w ∉ L := (List.nodup_cons.1 hd).1
    have hsub : ∀ z ∈ L', z = w ∨ z ∈ L := fun z hz => ((hL z).1 hz).1.symm
    simp only [List.length_cons] at hn ht
    have len2 : (∀ z ∈ w :: L, z ∈ L') → False ∨ (w :: L).length ≤ L'.length := fun h => Or.inr (nodup_sub_len hd h)
    rcases H.2.2.2.1 w hw with hg | hg | hg
    all_goals have opw := hg.1
    · rw [opw] at hl hk H'
      simp only [show ¬ ((0 : ℕ) = 2) by omega, if_false, Nat.sub_zero] at hl hk H'
      have q : (w :: L).length ≤ (l w :: r w :: L').length := nodup_sub_len hd hs
      simp only [List.length_cons] at q
      have na : l w ∉ L' := by
        intro h
        have : (w :: L).length ≤ (r w :: L').length := nodup_sub_len hd (by
          intro z hz
          have := hs z hz
          simp only [List.mem_cons] at this ⊢
          rcases this with rfl | h' | h'
          · exact Or.inr h
          · exact Or.inl h'
          · exact Or.inr h')
        simp only [List.length_cons] at this; omega
      have nb : r w ∉ L' := by
        intro h
        have : (w :: L).length ≤ (l w :: L').length := nodup_sub_len hd (by
          intro z hz
          have := hs z hz
          simp only [List.mem_cons] at this ⊢
          rcases this with h' | rfl | h'
          · exact Or.inl h'
          · exact Or.inr h
          · exact Or.inr h')
        simp only [List.length_cons] at this; omega
      refine RO.bin hg.2.2.2 H.1.1 H.1.2.1 na nb hsub wnL wL ?_ (Or.inl hg.2.2.1) (ih hn' H' (by omega))
      intro z hz h1 h2
      have := hs z (List.mem_cons_of_mem _ hz)
      simp only [List.mem_cons, h1, h2, false_or] at this
      exact this
    · rw [opw] at hl hk H'
      simp only [show ¬ ((1 : ℕ) = 2) by omega, if_false, Nat.sub_zero] at hl hk H'
      have q : (w :: L).length ≤ (l w :: r w :: L').length := nodup_sub_len hd hs
      simp only [List.length_cons] at q
      have na : l w ∉ L' := by
        intro h
        have : (w :: L).length ≤ (r w :: L').length := nodup_sub_len hd (by
          intro z hz
          have := hs z hz
          simp only [List.mem_cons] at this ⊢
          rcases this with rfl | h' | h'
          · exact Or.inr h
          · exact Or.inl h'
          · exact Or.inr h')
        simp only [List.length_cons] at this; omega
      have nb : r w ∉ L' := by
        intro h
        have : (w :: L).length ≤ (l w :: L').length := nodup_sub_len hd (by
          intro z hz
          have := hs z hz
          simp only [List.mem_cons] at this ⊢
          rcases this with h' | rfl | h'
          · exact Or.inl h'
          · exact Or.inr h
          · exact Or.inr h')
        simp only [List.length_cons] at this; omega
      refine RO.bin hg.2.2.2 H.1.1 H.1.2.1 na nb hsub wnL wL ?_ (Or.inr hg.2.2.1) (ih hn' H' (by omega))
      intro z hz h1 h2
      have := hs z (List.mem_cons_of_mem _ hz)
      simp only [List.mem_cons, h1, h2, false_or] at this
      exact this
    · have hr : r w = l w := hg.2.2.2
      rw [opw] at hl hk H'
      simp only [if_true] at hl hk H'
      have q : (w :: L).length ≤ (l w :: L').length := nodup_sub_len hd (by
        intro z hz; have := hs z hz; rw [hr] at this; simpa using this)
      simp only [List.length_cons] at q
      have na : l w ∉ L' := by
        intro h
        have : (w :: L).length ≤ L'.length := nodup_sub_len hd (by
          intro z hz
          have := hs z hz
          rw [hr] at this
          simp only [List.mem_cons] at this
          rcases this with rfl | rfl | h'
          · exact h
          · exact h
          · exact h')
        simp only [List.length_cons] at this; omega
      exact RO.neg H.1.1 na hsub wnL hg.2.2.1 (by omega) (ih hn' H' (by omega))

-- essential separation and conflicts
def Ess (val : ℕ → (Fin 7 → Bool) → Bool) (k : ℕ) (L : List ℕ) (i : ℕ) (x y : Fin 7 → Bool) : Prop :=
  val F x = true ∧ val F y = false ∧ Sp val k i x y ∧ ∀ z ∈ L, Sp val k z x y → z = i

def Conf (val : ℕ → (Fin 7 → Bool) → Bool) (F k : ℕ) (L : List ℕ) (i j : ℕ) : Prop :=
  i ≠ j ∧ i ∈ L ∧ j ∈ L ∧
  (∃ x y y', Ess (F := F) val k L i x y ∧ Ess (F := F) val k L j x y') ∧
  (∃ y x x', Ess (F := F) val k L i x y ∧ Ess (F := F) val k L j x' y)

theorem RO.ess {L : List ℕ} {k : ℕ} {A : ℕ → ℕ → Prop} {s : ℕ → Bool} {P Q : (Fin 7 → Bool) → ℕ → Prop}
    (h1 : ∀ x, val F x = true → ∀ i, P x i → i ∈ L ∧ val i x = s i)
    (h2 : ∀ y, val F y = false → ∀ i, Q y i → i ∈ L ∧ val i y = !s i)
    (h5 : ∀ x y, val F x = true → val F y = false → ∃ i, P x i ∧ Q y i)
    (h6 : k = 0 → ∀ i ∈ L, s i = true) {i : ℕ} {x y : Fin 7 → Bool} (hE : Ess (F := F) val k L i x y) :
    P x i ∧ Q y i := by
  obtain ⟨hx, hy, _, hu⟩ := hE
  obtain ⟨z, hp, hq⟩ := h5 x y hx hy
  have a := h1 x hx z hp
  have c := h2 y hy z hq
  have : Sp val k z x y := by
    unfold Sp
    by_cases hk : k = 0
    · rw [if_pos hk]
      have := h6 hk z a.1
      rw [a.2, c.2, this]; simp
    · rw [if_neg hk, a.2, c.2]; cases s z <;> simp
  have := hu z a.1 this
  subst this
  exact ⟨hp, hq⟩

theorem RO.noConf {L : List ℕ} {k i j : ℕ} (R : RO val F L k) : ¬ Conf val F k L i j := by
  rintro ⟨hij, _, _, ⟨x, y, y', e1, e2⟩, ⟨v, u, u', e3, e4⟩⟩
  obtain ⟨A, s, P, Q, h1, h2, h3, h4, h5, h6⟩ := R
  have q1 := RO.ess (A := A) h1 h2 h5 h6 e1
  have q2 := RO.ess (A := A) h1 h2 h5 h6 e2
  have q3 := RO.ess (A := A) h1 h2 h5 h6 e3
  have q4 := RO.ess (A := A) h1 h2 h5 h6 e4
  exact h4 v e3.2.1 i j hij q3.2 q4.2 (h3 x e1.1 i j hij q1.1 q2.1)

theorem Ess.keep {L L' : List ℕ} {k i w a c : ℕ} {x y : Fin 7 → Bool} (hE : Ess (F := F) val k L i x y)
    (hsub : ∀ z ∈ L', z = w ∨ z ∈ L) (ha : a ∈ L) (hc : c ∈ L) (hia : i ≠ a) (hic : i ≠ c)
    (hg : (∀ x, val w x = (val a x && val c x)) ∨ (∀ x, val w x = (val a x || val c x))) :
    Ess (F := F) val k L' i x y := by
  obtain ⟨hx, hy, hs, hu⟩ := hE
  refine ⟨hx, hy, hs, ?_⟩
  intro z hz h
  rcases hsub z hz with rfl | hz
  · exfalso
    have na : ¬ Sp val k a x y := fun h => hia (hu a ha h).symm
    have nc : ¬ Sp val k c x y := fun h => hic (hu c hc h).symm
    unfold Sp at h na nc
    by_cases hk : k = 0
    · rw [if_pos hk] at h na nc
      rcases hg with g | g <;> rw [g x, g y] at h <;> revert h na nc <;>
        cases val a x <;> cases val a y <;> cases val c x <;> cases val c y <;> simp
    · rw [if_neg hk] at h na nc
      rcases hg with g | g <;> rw [g x, g y] at h <;> revert h na nc <;>
        cases val a x <;> cases val a y <;> cases val c x <;> cases val c y <;> simp
  · exact hu z hz h

theorem Conf.keep {L L' : List ℕ} {k i j w a c : ℕ} (hE : Conf val F k L i j)
    (hsub : ∀ z ∈ L', z = w ∨ z ∈ L) (hi' : i ∈ L') (hj' : j ∈ L') (ha : a ∈ L) (hc : c ∈ L)
    (hia : i ≠ a) (hic : i ≠ c) (hja : j ≠ a) (hjc : j ≠ c)
    (hg : (∀ x, val w x = (val a x && val c x)) ∨ (∀ x, val w x = (val a x || val c x))) :
    Conf val F k L' i j := by
  obtain ⟨hij, _, _, ⟨x, y, y', e1, e2⟩, ⟨v, u, u', e3, e4⟩⟩ := hE
  exact ⟨hij, hi', hj', ⟨x, y, y', e1.keep hsub ha hc hia hic hg, e2.keep hsub ha hc hja hjc hg⟩,
    ⟨v, u, u', e3.keep hsub ha hc hia hic hg, e4.keep hsub ha hc hja hjc hg⟩⟩

def wds (pf : Pf) : List ℕ := pf.map (fun e => e.2.2.2)

def PfV (XS : List ℕ) : Pf → Prop
  | [] => True
  | e :: t => (e.2.1 ∈ XS ∨ e.2.1 ∈ wds t) ∧ (e.2.2.1 ∈ XS ∨ e.2.2.1 ∈ wds t) ∧ PfV XS t

def PfI (op l r : ℕ → ℕ) (XS gs : List ℕ) (pf : Pf) (L rest : List ℕ) : Prop :=
  (∀ e ∈ pf, op e.2.2.2 = e.1 ∧ ((l e.2.2.2 = e.2.1 ∧ r e.2.2.2 = e.2.2.1) ∨ (l e.2.2.2 = e.2.2.1 ∧ r e.2.2.2 = e.2.1))) ∧
  (wds pf ++ rest).Perm gs ∧ PfV XS pf ∧ (∀ z ∈ L, z ∈ XS ∨ z ∈ wds pf)

def Excl (op l r : ℕ → ℕ) (A T1 : List ℕ) (c : ℕ) (B : List ℕ) (nt : Bool) (rest : List ℕ) : Prop :=
  ∀ w ∈ rest, l w ∈ A ++ c :: B → r w ∈ A ++ c :: B →
    (l w ∈ B ∨ r w ∈ B) ∨ (l w = c ∧ r w ∈ T1) ∨ (r w = c ∧ l w ∈ T1) ∨ (op w = 2 ∧ l w = c ∧ nt = true)

variable (val op l r F T M MM Xt xr yr)
def Node (XS gs : List ℕ) (n k b sl : ℕ) (A T1 : List ℕ) (c : ℕ) (B : List ℕ) (nt : Bool) (e1 e2 : ℕ)
    (K : List (ℕ × ℕ)) (pf : Pf) (rest : List ℕ) : Prop :=
  rest.length = n ∧ Inv val op l r F T M MM Xt xr yr (A ++ c :: B) rest k b ∧
  (A ++ c :: B).length + k + sl = n + 1 ∧ ((∀ a ∈ T1, a ∈ A) ∧ T1.Nodup) ∧ Excl op l r A T1 c B nt rest ∧
  (∀ p, e1.testBit p = decide ((A ++ c :: B).countP (fun w => (sp T M k w).testBit p) = 1)) ∧
  (∀ p, e2.testBit p = decide ((A ++ c :: B).countP (fun w => (sp T M k w).testBit p) = 2)) ∧
  (∀ e ∈ K, Conf val F k (A ++ c :: B) e.1 e.2) ∧ PfI op l r XS gs pf (A ++ c :: B) rest

def Good (XS gs : List ℕ) (n : ℕ) {ι : Type} (C : ι → Sty) : Prop :=
  ∀ k b sl A T1 c B nt e1 e2 K pf rest, (∀ i, C i k b sl A T1 c B nt e1 e2 K pf = true) →
    Node val op l r F T M MM Xt xr yr XS gs n k b sl A T1 c B nt e1 e2 K pf rest → False

variable {val op l r F T M MM Xt xr yr}

def CtxF (val : ℕ → (Fin 7 → Bool) → Bool) (F M : ℕ) (xr yr : ℕ → Fin 7 → Bool) : Prop :=
  ∀ p, M.testBit p = true → val F (xr p) = true ∧ val F (yr p) = false
def CtxC (M G P : ℕ) (xr yr : ℕ → Fin 7 → Bool) : Prop :=
  ∀ e e' : ℕ, (∀ p, e.testBit p = true → M.testBit p = true) → (∀ p, e'.testBit p = true → M.testBit p = true) →
    cfl P (Nat.land (Nat.land (Nat.add e M) G) (Nat.land (Nat.add e' M) G)) = true →
    (∃ p p', e.testBit p = true ∧ e'.testBit p' = true ∧ xr p = xr p') ∧
    (∃ p p', e.testBit p = true ∧ e'.testBit p' = true ∧ yr p = yr p')

theorem ess_of_bit {L rest : List ℕ} {k b : ℕ} (H : Inv val op l r F T M MM Xt xr yr L rest k b)
    (hF : CtxF val F M xr yr) {e1 : ℕ} (he : ∀ p, e1.testBit p = decide (L.countP (fun w => (sp T M k w).testBit p) = 1))
    {i p : ℕ} (hi : i ∈ L) (h1 : e1.testBit p = true) (h2 : (sp T M k i).testBit p = true) :
    Ess (F := F) val k L i (xr p) (yr p) := by
  have hS : ∀ z ∈ L, Sem val T M xr yr z := fun z hz => H.2.2.1 z (List.mem_append_left _ hz)
  have hm := sp_sub _ _ _ _ _ h2
  refine ⟨(hF p hm).1, (hF p hm).2, ((sp_sem (hS i hi) k p).1 h2).2, ?_⟩
  intro z hz hs
  by_contra hne
  have hz2 := (sp_sem (hS z hz) k p).2 ⟨hm, hs⟩
  have := two_le_countP (l := L) (p := fun w => (sp T M k w).testBit p) hne hz hi hz2 h2
  rw [he] at h1
  simp only [decide_eq_true_eq] at h1
  omega

theorem conf_of_ed {L rest : List ℕ} {k b G P : ℕ} (H : Inv val op l r F T M MM Xt xr yr L rest k b)
    (hF : CtxF val F M xr yr) (hC : CtxC M G P xr yr) {e1 : ℕ}
    (he : ∀ p, e1.testBit p = decide (L.countP (fun w => (sp T M k w).testBit p) = 1))
    {e : ℕ × ℕ} (h : e ∈ ed P (gl T M G k e1 L)) : Conf val F k L e.1 e.2 := by
  rw [gl_eq] at h
  have hnd : L.Nodup := (List.nodup_append.1 H.2.1).1
  obtain ⟨hne, x, hx, y, hy, e1', e2', hc⟩ := ed_mem P _ (by
    rw [List.map_map]; simpa [Function.comp_def] using hnd) e h
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
  simp only at e1' e2' hc
  have sb : ∀ z p, (Nat.land (sp T M k z) e1).testBit p = true →
      e1.testBit p = true ∧ (sp T M k z).testBit p = true := by
    intro z p hp
    change ((sp T M k z) &&& e1).testBit p = true at hp
    rw [Nat.testBit_and] at hp; simp at hp; exact ⟨hp.2, hp.1⟩
  obtain ⟨⟨p, p', a1, a2, a3⟩, ⟨q, q', b1, b2, b3⟩⟩ := hC _ _
    (fun p hp => sp_sub _ _ _ _ _ (sb i p hp).2) (fun p hp => sp_sub _ _ _ _ _ (sb j p hp).2) hc
  rw [e1', e2'] at hne ⊢
  have E := fun {z p} hz hp => ess_of_bit H hF he (i := z) (p := p) hz (sb z p hp).1 (sb z p hp).2
  refine ⟨hne, hi, hj, ⟨xr p, yr p, yr p', E hi a1, ?_⟩, ⟨yr q, xr q, xr q', E hi b1, ?_⟩⟩
  · rw [a3]; exact E hj a2
  · rw [b3]; exact E hj b2

theorem xd (m n : ℕ) : (decide (m ≤ n) ^^ decide (m + 1 ≤ n)) = decide (n = m) := by
  rcases lt_trichotomy n m with h | h | h
  · have a : ¬ m ≤ n := by omega
    have b : ¬ m + 1 ≤ n := by omega
    have c : ¬ n = m := by omega
    simp only [a, b, c]; rfl
  · subst h; simp
  · have a : m ≤ n := by omega
    have b : m + 1 ≤ n := by omega
    have c : ¬ n = m := by omega
    simp only [a, b, c]; rfl

theorem nd_good {XS gs : List ℕ} {n G P : ℕ} {ι : Type} {C : ι → Sty}
    (hG : Good val op l r F T M MM Xt xr yr XS gs n C)
    (hF : CtxF val F M xr yr) (hC : CtxC M G P xr yr)
    {k b sl : ℕ} {A T1 : List ℕ} {c : ℕ} {B : List ℕ} {nt : Bool} {pf : Pf} {rest : List ℕ}
    (h : ∀ i, nd T M G P (C i) k b sl pf A T1 c B nt = true) (hn : rest.length = n)
    (H : Inv val op l r F T M MM Xt xr yr (A ++ c :: B) rest k b)
    (hs : (A ++ c :: B).length + k + sl = n + 1) (hT : (∀ a ∈ T1, a ∈ A) ∧ T1.Nodup)
    (hE : Excl op l r A T1 c B nt rest) (hp : PfI op l r XS gs pf (A ++ c :: B) rest) : False := by
  have hcat : cat (c :: B) A = A ++ c :: B := cat_eq _ _
  obtain ⟨r1, r2, r3, hq, b1, b2, b3⟩ := occ_zero T M k (A ++ c :: B)
  have hS : ∀ z ∈ A ++ c :: B, Sem val T M xr yr z := fun z hz => H.2.2.1 z (List.mem_append_left _ hz)
  have hr1 : r1 = M := by
    apply Nat.eq_of_testBit_eq
    intro p
    rw [b1]
    by_cases hm : M.testBit p = true
    · rw [hm, decide_eq_true_eq]
      obtain ⟨z, hz, hsz⟩ := H.cover (hF p hm).1 (hF p hm).2
      have : 0 < (A ++ c :: B).countP (fun w => (sp T M k w).testBit p) :=
        List.countP_pos_iff.2 ⟨z, hz, (sp_sem (hS z hz) k p).2 ⟨hm, hsz⟩⟩
      omega
    · rw [Bool.not_eq_true] at hm
      rw [hm, decide_eq_false_iff_not]
      intro hh
      obtain ⟨z, hz, hsz⟩ := List.countP_pos_iff.1 (show 0 < _ from hh)
      rw [sp_sub _ _ _ _ _ hsz] at hm
      exact absurd hm (by simp)
  have c1 : ∀ p, (Nat.xor r1 r2).testBit p = decide ((A ++ c :: B).countP (fun w => (sp T M k w).testBit p) = 1) := by
    intro p
    change (r1 ^^^ r2).testBit p = _
    rw [Nat.testBit_xor, b1, b2]; exact xd 1 _
  have c2 : ∀ p, (Nat.xor r2 r3).testBit p = decide ((A ++ c :: B).countP (fun w => (sp T M k w).testBit p) = 2) := by
    intro p
    change (r2 ^^^ r3).testBit p = _
    rw [Nat.testBit_xor, b2, b3]; exact xd 2 _
  have hK : ∀ e ∈ ed P (gl T M G k (Nat.xor r1 r2) (A ++ c :: B)), Conf val F k (A ++ c :: B) e.1 e.2 :=
    fun e he => conf_of_ed H hF hC c1 he
  refine hG k b sl A T1 c B nt (Nat.xor r1 r2) (Nat.xor r2 r3) (ed P (gl T M G k (Nat.xor r1 r2) (A ++ c :: B))) pf rest
    ?_ ⟨hn, H, hs, hT, hE, c1, c2, hK, hp⟩
  intro i
  have hi := h i
  unfold nd nd1 at hi
  have hb : Nat.beq r1 M = true := by rw [hr1]; exact Nat.beq_refl M
  rw [hcat, hq, hb, Bool.cond_true] at hi
  unfold nd2 nd3 at hi
  by_cases hsl : sl = 0
  · have R := Inv.tight n hn H (by omega)
    have hne : ne (ed P (gl T M G k (Nat.xor r1 r2) (A ++ c :: B))) = false := by
      cases hh : ed P (gl T M G k (Nat.xor r1 r2) (A ++ c :: B)) with
      | nil => rfl
      | cons e t => exact absurd (hK e (by rw [hh]; exact List.mem_cons_self)) R.noConf
    rw [hsl] at hi ⊢
    rw [hne] at hi
    simpa using hi
  · rw [beqf hsl] at hi
    simpa using hi

theorem nh_good {XS gs : List ℕ} {n G P : ℕ} {ι : Type} {C : ι → Sty}
    (hG : Good val op l r F T M MM Xt xr yr XS gs n C)
    (hF : CtxF val F M xr yr) (hC : CtxC M G P xr yr)
    {k b sl : ℕ} {A B : List ℕ} {pf : Pf} {rest : List ℕ} (hB : B ≠ [])
    (h : ∀ i, nh T M G P (C i) k b sl pf A B = true) (hn : rest.length = n)
    (H : Inv val op l r F T M MM Xt xr yr (A ++ B) rest k b)
    (hs : (A ++ B).length + k + sl = n + 1)
    (hE : ∀ w ∈ rest, l w ∈ A → r w ∈ A → False) (hp : PfI op l r XS gs pf (A ++ B) rest) : False := by
  cases B with
  | nil => exact hB rfl
  | cons c B =>
    refine nd_good hG hF hC (c := c) (B := B) (nt := true) (T1 := A) (fun i => h i) hn H hs ⟨fun a h => h, (List.nodup_append.1 (List.nodup_append.1 H.2.1).1).1⟩ ?_ hp
    intro w hw ha hb
    have hg := H.2.2.2.1 w hw
    have e := hE w hw
    simp only [List.mem_append, List.mem_cons] at ha hb
    rcases ha with ha | ha | ha
    · rcases hb with hb | hb | hb
      · exact absurd hb (fun h => e ha h)
      · exact Or.inr (Or.inr (Or.inl ⟨hb, ha⟩))
      · exact Or.inl (Or.inr hb)
    · rcases hb with hb | hb | hb
      · exact Or.inr (Or.inl ⟨ha, hb⟩)
      · refine Or.inr (Or.inr (Or.inr ⟨?_, ha, rfl⟩))
        rcases hg with g | g | g
        · exact absurd (ha.trans hb.symm) g.2.2.2
        · exact absurd (ha.trans hb.symm) g.2.2.2
        · exact g.1
      · exact Or.inl (Or.inr hb)
    · exact Or.inl (Or.inl ha)

theorem PfI.step {XS gs : List ℕ} {pf : Pf} {L rest L' : List ℕ} (h : PfI op l r XS gs pf L rest)
    {w a c : ℕ} (hw : w ∈ rest) (ha : a ∈ L) (hc : c ∈ L)
    (hac : (l w = a ∧ r w = c) ∨ (l w = c ∧ r w = a)) (hL : ∀ z ∈ L', z = w ∨ z ∈ L) :
    PfI op l r XS gs ((op w, a, c, w) :: pf) L' (rest.erase w) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ⟨h4 a ha, h4 c hc, h3⟩, ?_⟩
  · intro e he
    rcases List.mem_cons.1 he with rfl | he
    · exact ⟨rfl, hac⟩
    · exact h1 e he
  · refine List.Perm.trans ?_ h2
    show (w :: wds pf ++ rest.erase w).Perm _
    refine List.Perm.trans ?_ (List.Perm.append_left _ (erase_perm hw).symm)
    exact List.perm_middle.symm
  · intro z hz
    rcases hL z hz with rfl | hz
    · exact Or.inr List.mem_cons_self
    · rcases h4 z hz with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)

theorem wf_k0 {h : Bool} {sl : ℕ} {kb ka kc k0 : Bool} (e : wf true true true h sl kb ka kc k0 = true) : k0 = true := by
  unfold wf at e; cases k0 <;> simp_all
theorem wf_ka {tc tu h : Bool} {sl : ℕ} {kb ka kc k0 : Bool} (e : wf true tc tu h sl kb ka kc k0 = true)
    (h0 : 1 ≤ sl) (h1 : sl = 1 → h = true) : ka = true := by
  unfold wf at e
  rw [beqf (show sl ≠ 0 by omega)] at e
  by_cases hs : sl = 1
  · rw [h1 hs, hs] at e; cases ka <;> simp_all
  · rw [beqf hs] at e; cases ka <;> simp_all
theorem wf_kc {ta tu h : Bool} {sl : ℕ} {kb ka kc k0 : Bool} (e : wf ta true tu h sl kb ka kc k0 = true)
    (h0 : 1 ≤ sl) (h1 : sl = 1 → h = true) : kc = true := by
  unfold wf at e
  rw [beqf (show sl ≠ 0 by omega)] at e
  by_cases hs : sl = 1
  · rw [h1 hs, hs] at e; cases ta <;> cases ka <;> cases kc <;> simp_all
  · rw [beqf hs] at e; cases ta <;> cases ka <;> cases kc <;> simp_all
theorem wf_kb {ta tc tu h : Bool} {sl : ℕ} {kb ka kc k0 : Bool} (e : wf ta tc tu h sl kb ka kc k0 = true)
    (h0 : 2 ≤ sl) (h1 : sl = 2 → h = true) : kb = true := by
  unfold wf at e
  rw [beqf (show sl ≠ 0 by omega), beqf (show sl ≠ 1 by omega)] at e
  by_cases hs : sl = 2
  · rw [h1 hs, hs] at e; cases ta <;> cases tc <;> cases ka <;> cases kc <;> cases kb <;> simp_all
  · rw [beqf hs] at e; cases ta <;> cases tc <;> cases ka <;> cases kc <;> cases kb <;> simp_all

theorem cnd {a b : Bool} (h : cond a b false = true) : a = true ∧ b = true := by
  cases a <;> simp_all
theorem cnt {a b : Bool} (h : cond a true b = true) (ha : a = false) : b = true := by
  subst ha; exact h

theorem r1 {a c b w : Prop} (h : a ∨ c ∨ b ∨ w) : (a ∨ c ∨ b) ∨ w := by tauto
theorem r2 {a c b w : Prop} (h : a ∨ c ∨ b ∨ w) (hw : ¬ w) : a ∨ c ∨ b := by tauto
theorem r3 {a c b w u : Prop} (h : ((a ∨ c ∨ b) ∨ w) ∧ u) : a ∨ c ∨ b ∨ w := by tauto
theorem s1 {a c b w : Prop} (h : a ∨ b ∨ w) : (a ∨ c ∨ b) ∨ w := by tauto
theorem s2 {a c b w : Prop} (h : a ∨ b ∨ w) (hw : ¬ w) : a ∨ c ∨ b := by tauto
theorem s3 {a c b w : Prop} (h : (a ∨ c ∨ b) ∨ w) (hc : ¬ c) : a ∨ b ∨ w := by tauto
theorem t1 {a n c b w : Prop} (h : (a ∧ n) ∨ c ∨ b ∨ w) : (a ∨ c ∨ b) ∨ w := by tauto
theorem t2 {a n c b w : Prop} (h : (a ∧ n) ∨ c ∨ b ∨ w) (hw : ¬ w) : a ∨ c ∨ b := by tauto
theorem t3 {a n c b w : Prop} (h : (a ∨ c ∨ b) ∨ w) (hn : n) : (a ∧ n) ∨ c ∨ b ∨ w := by tauto
theorem u1 {a n c b w : Prop} (h : (a ∧ n) ∨ b ∨ w) : (a ∨ c ∨ b) ∨ w := by tauto
theorem u2 {a n c b w : Prop} (h : (a ∧ n) ∨ b ∨ w) (hw : ¬ w) : a ∨ c ∨ b := by tauto
theorem u3 {a n c b w : Prop} (h : (a ∨ c ∨ b) ∨ w) (hn : n) (hc : ¬ c) : (a ∧ n) ∨ b ∨ w := by tauto

theorem mem_f {w : ℕ} {l : List ℕ} (h : w ∉ l) : mem w l = false := by
  rw [← Bool.not_eq_true, mem_iff]; exact h

-- one gate with operands a, c is chosen and moved to the front
set_option maxHeartbeats 8000000 in
theorem pair_step {XS gs : List ℕ} {n G P : ℕ} {ι : Type} {C : ι → Sty}
    (hG : Good val op l r F T M MM Xt xr yr XS gs n C)
    (hF : CtxF val F M xr yr) (hC : CtxC M G P xr yr)
    {k b sl : ℕ} {A : List ℕ} {a : ℕ} {T2 : List ℕ} {c : ℕ} {B : List ℕ} {e1 e2 : ℕ} {K : List (ℕ × ℕ)}
    {pf : Pf} {rest : List ℕ}
    (N : Node val op l r F T M MM Xt xr yr XS gs (n + 1) k b sl A (a :: T2) c B false e1 e2 K pf rest)
    {w : ℕ} (hw : w ∈ rest) (hac : (l w = a ∧ r w = c) ∨ (l w = c ∧ r w = a)) (o2 : op w ≠ 2) {b' : ℕ}
    (hb' : b' = b - (if op w = 1 ∧ (l w = Xt ∨ r w = Xt) then 1 else 0))
    (h : ∀ i, we T M G P (C i) k b' sl A (a :: T2) T2 a c B e2 K pf (Nat.land e1 (sp T M k a))
      (Nat.land e1 (sp T M k c)) (op w) w = true) : False := by
  obtain ⟨hn, H, hs, ⟨hT, hT1⟩, hE, c1, c2, hK, hp⟩ := N
  have aA : a ∈ A := hT a List.mem_cons_self
  have ndAll := (List.nodup_append.1 H.2.1).1
  have ndA : A.Nodup := (List.nodup_append.1 ndAll).1
  have ndcB : (c :: B).Nodup := (List.nodup_append.1 ndAll).2.1
  have djA : ∀ z ∈ A, z ∉ c :: B := fun z hz hz' => (List.nodup_append.1 ndAll).2.2 z hz z hz' rfl
  have dj : ∀ z ∈ A ++ c :: B, z ∉ rest := fun z hz hr => (List.nodup_append.1 H.2.1).2.2 z hz z hr rfl
  have aL : a ∈ A ++ c :: B := List.mem_append_left _ aA
  have cL : c ∈ A ++ c :: B := List.mem_append_right _ List.mem_cons_self
  have cB : c ∉ B := (List.nodup_cons.1 ndcB).1
  have ndB : B.Nodup := (List.nodup_cons.1 ndcB).2
  have ac : a ≠ c := fun h => djA a aA (h ▸ List.mem_cons_self)
  have cA : c ∉ A := fun h => djA c h List.mem_cons_self
  have aB : a ∉ B := fun h => djA a aA (List.mem_cons_of_mem _ h)
  have wL : w ∉ A ++ c :: B := fun h => dj w h hw
  have wA : w ∉ A := fun h => wL (List.mem_append_left _ h)
  have wc : w ≠ c := fun h => wL (h ▸ cL)
  have wa : w ≠ a := fun h => wL (h ▸ aL)
  have wB : w ∉ B := fun h => wL (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have la : l w ∈ A ++ c :: B := by rcases hac with h | h <;> rw [h.1] <;> assumption
  have ra : r w ∈ A ++ c :: B := by rcases hac with h | h <;> rw [h.2] <;> assumption
  have hg := H.2.2.2.1 w hw
  have hgv : (∀ x, val w x = (val a x && val c x)) ∨ (∀ x, val w x = (val a x || val c x)) := by
    rcases hg with g | g | g
    · left; intro x; rw [g.2.2.1]
      rcases hac with h | h <;> rw [h.1, h.2]
      exact Bool.and_comm _ _
    · right; intro x; rw [g.2.2.1]
      rcases hac with h | h <;> rw [h.1, h.2]
      exact Bool.or_comm _ _
    · exact absurd g.1 o2
  let U : ℕ → Prop := fun z => Used l r F z (rest.erase w)
  have hU : ∀ z ∈ A ++ c :: B, z ≠ a → z ≠ c → U z := by
    intro z hz h1 h2
    rcases H.2.2.2.2.1 z (List.mem_append_left _ hz) with h | ⟨v, hv, hu⟩
    · exact Or.inl h
    · refine Or.inr ⟨v, ?_, hu⟩
      rcases List.mem_cons.1 ((erase_perm hw).mem_iff.1 hv) with rfl | h
      · exfalso
        rcases hac with g | g <;> rcases hu with q | q <;> rw [← q] at h1 h2 <;> simp [g] at h1 h2
      · exact h
  have hUw : U w := by
    obtain ⟨L0, n0, e0⟩ := H.next hw
    exact ((e0 w).1 (H.step hw la ra n0 e0).2.1).2
  have lenr : (rest.erase w).length = n := by rw [List.length_erase_of_mem hw]; omega
  have mB : ∀ z, z ∈ cat [w] B ↔ z ∈ B ∨ z = w := by intro z; rw [cat_eq]; simp
  have lB : (cat [w] B).length = B.length + 1 := by rw [cat_eq]; simp
  have nB : (cat [w] B).Nodup := by
    rw [cat_eq, List.nodup_append]
    exact ⟨ndB, by simp, by rintro z hz z' hz' rfl; simp at hz'; exact wB (hz' ▸ hz)⟩
  have mD : ∀ z, z ∈ del a A ↔ z ∈ A ∧ z ≠ a := by
    intro z; rw [del_eq, ndA.mem_erase_iff]; tauto
  have nD : (del a A).Nodup := by rw [del_eq]; exact ndA.erase _
  have lD : (del a A).length + 1 = A.length := by
    rw [del_eq, List.length_erase_of_mem aA]
    have := List.length_pos_of_mem aA; omega
  have mk : ∀ (L' : List ℕ), L'.Nodup → (∀ z, z ∈ L' ↔ (z ∈ A ++ c :: B ∨ z = w) ∧ U z) →
      Inv val op l r F T M MM Xt xr yr L' (rest.erase w) k b' ∧ L'.length + k ≤ n + 1 ∧
      PfI op l r XS gs ((op w, a, c, w) :: pf) L' (rest.erase w) := by
    intro L' n' e'
    have q := (H.step hw la ra n' e').1
    rw [if_neg o2, ← hb'] at q
    refine ⟨q, ?_, hp.step hw aL cL hac (fun z hz => ((e' z).1 hz).1.symm)⟩
    have := Inv.size n lenr q
    omega
  have cov : ∀ (L' : List ℕ), (∀ z, z ∈ L' ↔ (z ∈ A ++ c :: B ∨ z = w) ∧ U z) → L'.Nodup →
      ∀ p, M.testBit p = true → (∀ z ∈ A ++ c :: B, U z → (sp T M k z).testBit p = false) →
      (sp T M k w).testBit p = true := by
    intro L' e' n' p hm hz
    have q := (mk L' n' e').1
    obtain ⟨z, hz1, hz2⟩ := q.cover (hF p hm).1 (hF p hm).2
    have hb := (sp_sem (q.2.2.1 z (List.mem_append_left _ hz1)) k p).2 ⟨hm, hz2⟩
    obtain ⟨h1 | rfl, h2⟩ := (e' z).1 hz1
    · rw [hz z h1 h2] at hb; exact absurd hb (by simp)
    · exact hb
  have uniq : ∀ p u z, u ∈ A ++ c :: B → z ∈ A ++ c :: B → (Nat.land e1 (sp T M k u)).testBit p = true →
      (sp T M k z).testBit p = true → z = u := by
    intro p u z hu hz h1 h2
    change (e1 &&& sp T M k u).testBit p = true at h1
    rw [Nat.testBit_and, Bool.and_eq_true] at h1
    exact (ess_of_bit H hF c1 hu h1.1 h1.2).2.2.2 z hz
      ((sp_sem (H.2.2.1 z (List.mem_append_left _ hz)) k p).1 h2).2
  have mbit : ∀ p u, (Nat.land e1 (sp T M k u)).testBit p = true → M.testBit p = true := by
    intro p u h1
    change (e1 &&& sp T M k u).testBit p = true at h1
    rw [Nat.testBit_and, Bool.and_eq_true] at h1
    exact sp_sub _ _ _ _ _ h1.2
  -- the three containment tests
  have tS : ∀ u, u ∈ A ++ c :: B → ¬ U u → sub (Nat.land e1 (sp T M k u)) (sp T M k w) = true := by
    intro u hu hnu
    obtain ⟨L0, n0, e0⟩ := H.next hw
    refine sub_of _ _ (fun p hp1 => cov L0 e0 n0 p (mbit p u hp1) ?_)
    intro z hz hUz
    by_contra hb
    rw [Bool.not_eq_false] at hb
    exact hnu (uniq p u z hu hz hp1 hb ▸ hUz)
  have tU : ¬ U a → ¬ U c → sub (Nat.land e2 (Nat.land (sp T M k a) (sp T M k c))) (sp T M k w) = true := by
    intro ha hc
    obtain ⟨L0, n0, e0⟩ := H.next hw
    refine sub_of _ _ (fun p hp1 => ?_)
    change (e2 &&& (sp T M k a &&& sp T M k c)).testBit p = true at hp1
    rw [Nat.testBit_and, Nat.testBit_and, Bool.and_eq_true, Bool.and_eq_true] at hp1
    refine cov L0 e0 n0 p (sp_sub _ _ _ _ _ hp1.2.1) ?_
    intro z hz hUz
    by_contra hb
    rw [Bool.not_eq_false] at hb
    have q1 : z ≠ a := fun h => ha (h ▸ hUz)
    have q2 : z ≠ c := fun h => hc (h ▸ hUz)
    have := three_le_countP (l := A ++ c :: B) (p := fun w => (sp T M k w).testBit p) q1 q2 ac hz aL cL hb hp1.2.1 hp1.2.2
    have e := hp1.1
    rw [c2, decide_eq_true_eq] at e
    omega
  -- conflicts must be hit when the next state is tight
  have hH : ∀ (L' : List ℕ), L'.Nodup → (∀ z, z ∈ L' ↔ (z ∈ A ++ c :: B ∨ z = w) ∧ U z) → L'.length + k = n + 1 →
      hit a c K = true := by
    intro L' n' e' ht
    apply hit_of
    intro e he
    by_contra hcon
    push Not at hcon
    obtain ⟨p1, p2, p3, p4⟩ := hcon
    have q := hK e he
    have R := Inv.tight n lenr (mk L' n' e').1 (by omega)
    refine RO.noConf R (q.keep (L' := L') (fun z hz => ((e' z).1 hz).1.symm) ?_ ?_ aL cL p1 p3 p2 p4 hgv)
    · exact (e' _).2 ⟨Or.inl q.2.1, hU _ q.2.1 p1 p3⟩
    · exact (e' _).2 ⟨Or.inl q.2.2.1, hU _ q.2.2.1 p2 p4⟩
  have exc : ∀ v ∈ rest.erase w, l v ∈ A ++ c :: B → r v ∈ A ++ c :: B →
      (l v ∈ B ∨ r v ∈ B) ∨ (l v = c ∧ r v ∈ a :: T2) ∨ (r v = c ∧ l v ∈ a :: T2) := by
    intro v hv h1 h2
    rcases hE v (List.mem_of_mem_erase hv) h1 h2 with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact absurd h.2.2 (by simp)
  have memL : ∀ z, z ∈ A ++ c :: B ↔ z ∈ A ∨ z = c ∨ z ∈ B := by intro z; simp
  simp only [List.length_append, List.length_cons] at hs
  have wdE : ∀ i, (2 ≤ sl ∨ ¬ U a ∨ ¬ U c) → wf (sub (Nat.land e1 (sp T M k a)) (sp T M k w)) (sub (Nat.land e1 (sp T M k c)) (sp T M k w))
      (sub (Nat.land e2 (Nat.land (sp T M k a) (sp T M k c))) (sp T M k w)) (hit a c K) sl
        (nd T M G P (C i) k b' (Nat.sub sl 2) ((op w, a, c, w) :: pf) A (a :: T2) c (cat [w] B) false)
        (nd T M G P (C i) k b' (Nat.sub sl 1) ((op w, a, c, w) :: pf) (del a A) T2 c (cat [w] B) false)
        (nh T M G P (C i) k b' (Nat.sub sl 1) ((op w, a, c, w) :: pf) A (cat [w] B))
        (nh T M G P (C i) k b' sl ((op w, a, c, w) :: pf) (del a A) (cat [w] B)) = true := by
    intro i hor
    have hi := h i
    unfold we we1 wd at hi
    rw [mem_f wA, mem_f wB, beqf wc] at hi
    have g : cond (Nat.ble 2 sl) true (cond (sub (Nat.land e1 (sp T M k a)) (sp T M k w)) true
        (sub (Nat.land e1 (sp T M k c)) (sp T M k w))) = true := by
      rcases hor with q | q | q
      · rw [show Nat.ble 2 sl = true from Nat.ble_eq.mpr q]; rfl
      · rw [tS a aL q]; cases Nat.ble 2 sl <;> rfl
      · rw [tS c cL q]; cases Nat.ble 2 sl <;> cases sub (Nat.land e1 (sp T M k a)) (sp T M k w) <;> rfl
    rw [g] at hi
    simpa only [Bool.cond_true, Bool.cond_false] using hi
  by_cases ua : U a <;> by_cases uc : U c
  · -- both kept
    have n' : (A ++ c :: cat [w] B).Nodup := by
      rw [List.nodup_append, List.nodup_cons]
      refine ⟨ndA, ⟨?_, nB⟩, ?_⟩
      · rw [mB]; rintro (h | h)
        · exact cB h
        · exact wc h.symm
      · rintro z hz z' hz' rfl
        rcases List.mem_cons.1 hz' with rfl | h
        · exact cA hz
        · rcases (mB z).1 h with h | rfl
          · exact djA z hz (List.mem_cons_of_mem _ h)
          · exact wA hz
    have e' : ∀ z, z ∈ A ++ c :: cat [w] B ↔ (z ∈ A ++ c :: B ∨ z = w) ∧ U z := by
      intro z
      rw [memL, List.mem_append, List.mem_cons, mB]
      constructor
      · intro hz
        refine ⟨r1 hz, ?_⟩
        by_cases z1 : z = a
        · exact z1 ▸ ua
        · by_cases z2 : z = c
          · exact z2 ▸ uc
          · by_cases z3 : z = w
            · exact z3 ▸ hUw
            · exact hU z ((memL z).2 (r2 hz z3)) z1 z2
      · exact r3
    obtain ⟨q1, q2, q3⟩ := mk _ n' e'
    have hh := hH _ n' e'
    simp only [List.length_append, List.length_cons, lB] at q2 hh
    have sl2 : 2 ≤ sl := by omega
    refine nd_good hG hF hC (fun i => wf_kb (wdE i (Or.inl sl2)) sl2 (fun h => hh (by omega))) lenr q1 ?_ ⟨hT, hT1⟩ ?_ q3
    · simp only [List.length_append, List.length_cons, lB]
      show _ + (sl - 2) = _
      omega
    · intro v hv h1 h2
      rw [List.mem_append, List.mem_cons, mB] at h1 h2
      by_cases lw : l v = w
      · exact Or.inl (Or.inl ((mB _).2 (Or.inr lw)))
      · by_cases rw' : r v = w
        · exact Or.inl (Or.inr ((mB _).2 (Or.inr rw')))
        · rcases exc v hv ((memL _).2 (r2 h1 lw)) ((memL _).2 (r2 h2 rw')) with (h | h) | h | h
          · exact Or.inl (Or.inl ((mB _).2 (Or.inl h)))
          · exact Or.inl (Or.inr ((mB _).2 (Or.inl h)))
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inl h))
  · -- c dropped
    have n' : (A ++ cat [w] B).Nodup := by
      rw [List.nodup_append]
      refine ⟨ndA, nB, ?_⟩
      rintro z hz z' hz' rfl
      rcases (mB z).1 hz' with h | rfl
      · exact djA z hz (List.mem_cons_of_mem _ h)
      · exact wA hz
    have e' : ∀ z, z ∈ A ++ cat [w] B ↔ (z ∈ A ++ c :: B ∨ z = w) ∧ U z := by
      intro z
      rw [memL, List.mem_append, mB]
      constructor
      · intro hz
        refine ⟨s1 hz, ?_⟩
        by_cases z1 : z = a
        · exact z1 ▸ ua
        · by_cases z3 : z = w
          · exact z3 ▸ hUw
          · have z2 : z ≠ c := by
              rintro rfl
              rcases hz with h | h | h
              · exact cA h
              · exact cB h
              · exact z3 h
            exact hU z ((memL z).2 (s2 hz z3)) z1 z2
      · rintro ⟨hz, hu⟩
        have z2 : z ≠ c := fun h => uc (h ▸ hu)
        exact s3 hz z2
    obtain ⟨q1, q2, q3⟩ := mk _ n' e'
    have hh := hH _ n' e'
    simp only [List.length_append, lB] at q2 hh
    have sl1 : 1 ≤ sl := by omega
    refine nh_good hG hF hC (by rw [cat_eq]; simp) (fun i => by
      have := wdE i (Or.inr (Or.inr uc))
      rw [tS c cL uc] at this
      exact wf_kc this sl1 (fun h => hh (by omega))) lenr q1 ?_ ?_ q3
    · simp only [List.length_append, lB]
      show _ + (sl - 1) = _
      omega
    · intro v hv h1 h2
      rcases exc v hv ((memL _).2 (Or.inl h1)) ((memL _).2 (Or.inl h2)) with (h | h) | h | h
      · exact djA _ h1 (List.mem_cons_of_mem _ h)
      · exact djA _ h2 (List.mem_cons_of_mem _ h)
      · exact cA (h.1 ▸ h1)
      · exact cA (h.1 ▸ h2)
  · -- a dropped
    have n' : (del a A ++ c :: cat [w] B).Nodup := by
      rw [List.nodup_append, List.nodup_cons]
      refine ⟨nD, ⟨?_, nB⟩, ?_⟩
      · rw [mB]; rintro (h | h)
        · exact cB h
        · exact wc h.symm
      · rintro z hz z' hz' rfl
        have hz := ((mD z).1 hz).1
        rcases List.mem_cons.1 hz' with rfl | h
        · exact cA hz
        · rcases (mB z).1 h with h | rfl
          · exact djA z hz (List.mem_cons_of_mem _ h)
          · exact wA hz
    have e' : ∀ z, z ∈ del a A ++ c :: cat [w] B ↔ (z ∈ A ++ c :: B ∨ z = w) ∧ U z := by
      intro z
      rw [memL, List.mem_append, List.mem_cons, mB, mD]
      constructor
      · intro hz
        refine ⟨t1 hz, ?_⟩
        by_cases z2 : z = c
        · exact z2 ▸ uc
        · by_cases z3 : z = w
          · exact z3 ▸ hUw
          · have z1 : z ≠ a := by
              rintro rfl
              rcases hz with h | h | h | h
              · exact h.2 rfl
              · exact ac h
              · exact aB h
              · exact wa h.symm
            exact hU z ((memL z).2 (t2 hz z3)) z1 z2
      · rintro ⟨hz, hu⟩
        have z1 : z ≠ a := fun h => ua (h ▸ hu)
        exact t3 hz z1
    obtain ⟨q1, q2, q3⟩ := mk _ n' e'
    have hh := hH _ n' e'
    simp only [List.length_append, List.length_cons, lB] at q2 hh
    have sl1 : 1 ≤ sl := by omega
    refine nd_good hG hF hC (fun i => by
      have := wdE i (Or.inr (Or.inl ua))
      rw [tS a aL ua] at this
      exact wf_ka this sl1 (fun h => hh (by omega))) lenr q1 ?_ ?_ ?_ q3
    · simp only [List.length_append, List.length_cons, lB]
      show _ + (sl - 1) = _
      omega
    · refine ⟨fun z hz => ?_, (List.nodup_cons.1 hT1).2⟩
      refine (mD z).2 ⟨hT z (List.mem_cons_of_mem _ hz), ?_⟩
      rintro rfl
      exact (List.nodup_cons.1 hT1).1 hz
    · intro v hv h1 h2
      rw [List.mem_append, List.mem_cons, mB, mD] at h1 h2
      by_cases lw : l v = w
      · exact Or.inl (Or.inl ((mB _).2 (Or.inr lw)))
      · by_cases rw' : r v = w
        · exact Or.inl (Or.inr ((mB _).2 (Or.inr rw')))
        · rcases exc v hv ((memL _).2 (t2 h1 lw)) ((memL _).2 (t2 h2 rw')) with (h | h) | h | h
          · exact Or.inl (Or.inl ((mB _).2 (Or.inl h)))
          · exact Or.inl (Or.inr ((mB _).2 (Or.inl h)))
          · refine Or.inr (Or.inl ⟨h.1, ?_⟩)
            rcases List.mem_cons.1 h.2 with g | g
            · exfalso
              rw [g] at h2
              rcases h2 with q | q | q | q
              · exact q.2 rfl
              · exact ac q
              · exact aB q
              · exact wa q.symm
            · exact g
          · refine Or.inr (Or.inr (Or.inl ⟨h.1, ?_⟩))
            rcases List.mem_cons.1 h.2 with g | g
            · exfalso
              rw [g] at h1
              rcases h1 with q | q | q | q
              · exact q.2 rfl
              · exact ac q
              · exact aB q
              · exact wa q.symm
            · exact g
  · -- both dropped
    have n' : (del a A ++ cat [w] B).Nodup := by
      rw [List.nodup_append]
      refine ⟨nD, nB, ?_⟩
      rintro z hz z' hz' rfl
      have hz := ((mD z).1 hz).1
      rcases (mB z).1 hz' with h | rfl
      · exact djA z hz (List.mem_cons_of_mem _ h)
      · exact wA hz
    have e' : ∀ z, z ∈ del a A ++ cat [w] B ↔ (z ∈ A ++ c :: B ∨ z = w) ∧ U z := by
      intro z
      rw [memL, List.mem_append, mB, mD]
      constructor
      · intro hz
        refine ⟨u1 hz, ?_⟩
        by_cases z3 : z = w
        · exact z3 ▸ hUw
        · have z1 : z ≠ a := by
            rintro rfl
            rcases hz with h | h | h
            · exact h.2 rfl
            · exact aB h
            · exact wa h.symm
          have z2 : z ≠ c := by
            rintro rfl
            rcases hz with h | h | h
            · exact cA h.1
            · exact cB h
            · exact z3 h
          exact hU z ((memL z).2 (u2 hz z3)) z1 z2
      · rintro ⟨hz, hu⟩
        have z1 : z ≠ a := fun h => ua (h ▸ hu)
        have z2 : z ≠ c := fun h => uc (h ▸ hu)
        exact u3 hz z1 z2
    obtain ⟨q1, q2, q3⟩ := mk _ n' e'
    simp only [List.length_append, lB] at q2
    refine nh_good hG hF hC (by rw [cat_eq]; simp) (fun i => by
      have := wdE i (Or.inr (Or.inr uc))
      rw [tS c cL uc, tS a aL ua, tU ua uc] at this
      exact wf_k0 this) lenr q1 ?_ ?_ q3
    · simp only [List.length_append, lB]
      omega
    · intro v hv h1 h2
      have h1 := ((mD _).1 h1).1
      have h2 := ((mD _).1 h2).1
      rcases exc v hv ((memL _).2 (Or.inl h1)) ((memL _).2 (Or.inl h2)) with (h | h) | h | h
      · exact djA _ h1 (List.mem_cons_of_mem _ h)
      · exact djA _ h2 (List.mem_cons_of_mem _ h)
      · exact cA (h.1 ▸ h1)
      · exact cA (h.1 ▸ h2)

set_option maxHeartbeats 2000000 in
theorem not_step {XS gs : List ℕ} {n G P : ℕ} {ι : Type} {C : ι → Sty}
    (hG : Good val op l r F T M MM Xt xr yr XS gs n C)
    (hF : CtxF val F M xr yr) (hC : CtxC M G P xr yr)
    {k b sl : ℕ} {A T1 : List ℕ} {c : ℕ} {B : List ℕ} {nt : Bool} {e1 e2 : ℕ} {K : List (ℕ × ℕ)}
    {pf : Pf} {rest : List ℕ}
    (N : Node val op l r F T M MM Xt xr yr XS gs (n + 1) k b sl A T1 c B nt e1 e2 K pf rest)
    {w : ℕ} (hw : w ∈ rest) (hlc : l w = c) (o2 : op w = 2)
    (h : ∀ i, nt1 T M G P (C i) k b sl A T1 c B pf w = true) : False := by
  obtain ⟨hn, H, hs, hT, hE, c1, c2, hK, hp⟩ := N
  have ndAll := (List.nodup_append.1 H.2.1).1
  have ndA : A.Nodup := (List.nodup_append.1 ndAll).1
  have ndcB : (c :: B).Nodup := (List.nodup_append.1 ndAll).2.1
  have djA : ∀ z ∈ A, z ∉ c :: B := fun z hz hz' => (List.nodup_append.1 ndAll).2.2 z hz z hz' rfl
  have dj : ∀ z ∈ A ++ c :: B, z ∉ rest := fun z hz hr => (List.nodup_append.1 H.2.1).2.2 z hz z hr rfl
  have cL : c ∈ A ++ c :: B := List.mem_append_right _ List.mem_cons_self
  have cB : c ∉ B := (List.nodup_cons.1 ndcB).1
  have ndB : B.Nodup := (List.nodup_cons.1 ndcB).2
  have cA : c ∉ A := fun h => djA c h List.mem_cons_self
  have wL : w ∉ A ++ c :: B := fun h => dj w h hw
  have wA : w ∉ A := fun h => wL (List.mem_append_left _ h)
  have wc : w ≠ c := fun h => wL (h ▸ cL)
  have wB : w ∉ B := fun h => wL (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have gn : ∀ v ∈ rest, op v = 2 → v = Nat.xor (l v) MM ∧ r v = l v := by
    intro v hv o
    rcases H.2.2.2.1 v hv with g | g | g
    · exact absurd g.1 (by omega)
    · exact absurd g.1 (by omega)
    · exact ⟨g.2.1, g.2.2.2⟩
  have hrc : r w = c := (gn w hw o2).2.trans hlc
  have la : l w ∈ A ++ c :: B := hlc ▸ cL
  have ra : r w ∈ A ++ c :: B := hrc ▸ cL
  let U : ℕ → Prop := fun z => Used l r F z (rest.erase w)
  have hU : ∀ z ∈ A ++ c :: B, z ≠ c → U z := by
    intro z hz h2
    rcases H.2.2.2.2.1 z (List.mem_append_left _ hz) with h | ⟨v, hv, hu⟩
    · exact Or.inl h
    · refine Or.inr ⟨v, ?_, hu⟩
      rcases List.mem_cons.1 ((erase_perm hw).mem_iff.1 hv) with rfl | h
      · exfalso
        rcases hu with q | q
        · exact h2 (q.symm.trans hlc)
        · exact h2 (q.symm.trans hrc)
      · exact h
  have hUw : U w := by
    obtain ⟨L0, n0, e0⟩ := H.next hw
    exact ((e0 w).1 (H.step hw la ra n0 e0).2.1).2
  have lenr : (rest.erase w).length = n := by rw [List.length_erase_of_mem hw]; omega
  have mB : ∀ z, z ∈ cat [w] B ↔ z ∈ B ∨ z = w := by intro z; rw [cat_eq]; simp
  have lB : (cat [w] B).length = B.length + 1 := by rw [cat_eq]; simp
  have nB : (cat [w] B).Nodup := by
    rw [cat_eq, List.nodup_append]
    exact ⟨ndB, by simp, by rintro z hz z' hz' rfl; simp at hz'; exact wB (hz' ▸ hz)⟩
  have mk : ∀ (L' : List ℕ), L'.Nodup → (∀ z, z ∈ L' ↔ (z ∈ A ++ c :: B ∨ z = w) ∧ U z) →
      Inv val op l r F T M MM Xt xr yr L' (rest.erase w) (k - 1) b ∧ L'.length + (k - 1) ≤ n + 1 ∧
      PfI op l r XS gs ((2, c, c, w) :: pf) L' (rest.erase w) ∧ 1 ≤ k := by
    intro L' n' e'
    have q := (H.step hw la ra n' e')
    rw [if_pos o2, if_neg (by omega), Nat.sub_zero] at q
    refine ⟨q.1, ?_, o2 ▸ hp.step hw cL cL (Or.inl ⟨hlc, hrc⟩) (fun z hz => ((e' z).1 hz).1.symm), q.2.2.1⟩
    have := Inv.size n lenr q.1
    omega
  have memL : ∀ z, z ∈ A ++ c :: B ↔ z ∈ A ∨ z = c ∨ z ∈ B := by intro z; simp
  simp only [List.length_append, List.length_cons] at hs
  have hE' : ∀ i, nh T M G P (C i) (k - 1) b sl ((2, c, c, w) :: pf) A (cat [w] B) = true ∧
      cond (Nat.beq sl 0) true (nd T M G P (C i) (k - 1) b (sl - 1) ((2, c, c, w) :: pf) A T1 c (cat [w] B) false) = true := by
    intro i
    have hi := h i
    unfold nt1 at hi
    rw [mem_f wA, mem_f wB, beqf wc] at hi
    exact cnd hi
  by_cases uc : U c
  · have n' : (A ++ c :: cat [w] B).Nodup := by
      rw [List.nodup_append, List.nodup_cons]
      refine ⟨ndA, ⟨?_, nB⟩, ?_⟩
      · rw [mB]; rintro (h | h)
        · exact cB h
        · exact wc h.symm
      · rintro z hz z' hz' rfl
        rcases List.mem_cons.1 hz' with rfl | h
        · exact cA hz
        · rcases (mB z).1 h with h | rfl
          · exact djA z hz (List.mem_cons_of_mem _ h)
          · exact wA hz
    have e' : ∀ z, z ∈ A ++ c :: cat [w] B ↔ (z ∈ A ++ c :: B ∨ z = w) ∧ U z := by
      intro z
      rw [memL, List.mem_append, List.mem_cons, mB]
      constructor
      · intro hz
        refine ⟨r1 hz, ?_⟩
        by_cases z2 : z = c
        · exact z2 ▸ uc
        · by_cases z3 : z = w
          · exact z3 ▸ hUw
          · exact hU z ((memL z).2 (r2 hz z3)) z2
      · exact r3
    obtain ⟨q1, q2, q3, q4⟩ := mk _ n' e'
    simp only [List.length_append, List.length_cons, lB] at q2
    have sl1 : sl ≠ 0 := by omega
    refine nd_good hG hF hC (fun i => by
      have := (hE' i).2
      rw [beqf sl1] at this
      exact this) lenr q1 ?_ hT ?_ q3
    · simp only [List.length_append, List.length_cons, lB]
      omega
    · intro v hv h1 h2
      rw [List.mem_append, List.mem_cons, mB] at h1 h2
      by_cases lw : l v = w
      · exact Or.inl (Or.inl ((mB _).2 (Or.inr lw)))
      · by_cases rw' : r v = w
        · exact Or.inl (Or.inr ((mB _).2 (Or.inr rw')))
        · have hv' := List.mem_of_mem_erase hv
          rcases hE v hv' ((memL _).2 (r2 h1 lw)) ((memL _).2 (r2 h2 rw')) with (h | h) | h | h | h
          · exact Or.inl (Or.inl ((mB _).2 (Or.inl h)))
          · exact Or.inl (Or.inr ((mB _).2 (Or.inl h)))
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inl h))
          · exfalso
            have e1 := (gn v hv' h.1).1
            have e2 := (gn w hw o2).1
            rw [h.2.1] at e1
            rw [hlc] at e2
            have : v = w := e1.trans e2.symm
            rw [this] at hv
            have nr : rest.Nodup := (List.nodup_append.1 H.2.1).2.1
            exact (List.nodup_cons.1 ((erase_perm hw).nodup_iff.1 nr)).1 hv
  · have n' : (A ++ cat [w] B).Nodup := by
      rw [List.nodup_append]
      refine ⟨ndA, nB, ?_⟩
      rintro z hz z' hz' rfl
      rcases (mB z).1 hz' with h | rfl
      · exact djA z hz (List.mem_cons_of_mem _ h)
      · exact wA hz
    have e' : ∀ z, z ∈ A ++ cat [w] B ↔ (z ∈ A ++ c :: B ∨ z = w) ∧ U z := by
      intro z
      rw [memL, List.mem_append, mB]
      constructor
      · intro hz
        refine ⟨s1 hz, ?_⟩
        by_cases z3 : z = w
        · exact z3 ▸ hUw
        · have z2 : z ≠ c := by
            rintro rfl
            rcases hz with h | h | h
            · exact cA h
            · exact cB h
            · exact z3 h
          exact hU z ((memL z).2 (s2 hz z3)) z2
      · rintro ⟨hz, hu⟩
        have z2 : z ≠ c := fun h => uc (h ▸ hu)
        exact s3 hz z2
    obtain ⟨q1, q2, q3, q4⟩ := mk _ n' e'
    simp only [List.length_append, lB] at q2
    refine nh_good hG hF hC (by rw [cat_eq]; simp) (fun i => (hE' i).1) lenr q1 ?_ ?_ q3
    · simp only [List.length_append, lB]
      omega
    · intro v hv h1 h2
      rcases hE v (List.mem_of_mem_erase hv) ((memL _).2 (Or.inl h1)) ((memL _).2 (Or.inl h2)) with (h | h) | h | h | h
      · exact djA _ h1 (List.mem_cons_of_mem _ h)
      · exact djA _ h2 (List.mem_cons_of_mem _ h)
      · exact cA (h.1 ▸ h1)
      · exact cA (h.1 ▸ h2)
      · exact cA (h.2.1 ▸ h1)

theorem Lv_good {XS gs : List ℕ} {n G P : ℕ} {ι : Type} [Nonempty ι] {C : ι → Sty}
    (hG : Good val op l r F T M MM Xt xr yr XS gs n C)
    (hF : CtxF val F M xr yr) (hC : CtxC M G P xr yr) : ∀ fu : ℕ,
    Good val op l r F T M MM Xt xr yr XS gs (n + 1) (fun i => Lv T M G P MM Xt (C i) fu) := by
  intro fu
  induction fu with
  | zero =>
    intro k b sl A T1 c B nt e1 e2 K pf rest h _
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact absurd (h i) (by simp [Lv])
  | succ fu ih =>
    intro k b sl A T1 c B nt e1 e2 K pf rest h N
    have N0 := N
    obtain ⟨hn, H, hs, hT, hE, c1, c2, hK, hp⟩ := N
    cases nt with
    | true =>
      have h' : ∀ i, cond (cond (Nat.beq k 0) true (nt1 T M G P (C i) k b sl A T1 c B pf (Nat.xor c MM)))
          (Lv T M G P MM Xt (C i) fu k b sl A T1 c B false e1 e2 K pf) false = true := h
      by_cases hex : ∃ w ∈ rest, op w = 2 ∧ l w = c
      · obtain ⟨w, hw, o2, hlc⟩ := hex
        have hk : k ≠ 0 := by
          have : 0 < cN op rest := by
            unfold cN; rw [List.countP_pos_iff]; exact ⟨w, hw, by simp [o2]⟩
          have := H.2.2.2.2.2.2.1
          omega
        have ew : w = Nat.xor c MM := by
          rcases H.2.2.2.1 w hw with g | g | g
          · exact absurd g.1 (by omega)
          · exact absurd g.1 (by omega)
          · rw [← hlc]; exact g.2.1
        refine not_step hG hF hC N0 hw hlc o2 (fun i => ?_)
        have := (cnd (h' i)).1
        rw [beqf hk] at this
        rw [ew]; exact this
      · refine ih k b sl A T1 c B false e1 e2 K pf rest (fun i => (cnd (h' i)).2) ⟨hn, H, hs, hT, ?_, c1, c2, hK, hp⟩
        intro w hw h1 h2
        rcases hE w hw h1 h2 with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact absurd ⟨w, hw, h.1, h.2.1⟩ hex
    | false =>
      cases T1 with
      | nil =>
        cases B with
        | nil =>
          obtain ⟨w, t, rfl⟩ : ∃ w t, rest = w :: t := by
            cases rest with
            | nil => simp at hn
            | cons w t => exact ⟨w, t, rfl⟩
          rcases hE w List.mem_cons_self H.1.1 H.1.2.1 with (h | h) | h | h | h
          · simp at h
          · simp at h
          · simp at h
          · simp at h
          · exact absurd h.2.2 (by simp)
        | cons c' B' =>
          have h' : ∀ i, Lv T M G P MM Xt (C i) fu k b sl (cat [c] A) (cat [c] A) c' B' true e1 e2 K pf = true := h
          rw [cat_eq] at h'
          have eL : (A ++ [c]) ++ c' :: B' = A ++ c :: c' :: B' := by simp
          refine ih k b sl (A ++ [c]) (A ++ [c]) c' B' true e1 e2 K pf rest h' ⟨hn, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [eL]; exact H
          · rw [eL]; exact hs
          · refine ⟨fun a h => h, ?_⟩
            have := (List.nodup_append.1 H.2.1).1
            rw [← eL] at this
            exact (List.nodup_append.1 this).1
          · intro w hw ha hb
            rw [eL] at ha hb
            rcases hE w hw ha hb with h | h | h | h
            · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha hb ⊢
              have hg := H.2.2.2.1 w hw
              by_cases l1 : l w = c'
              · by_cases l2 : r w = c'
                · refine Or.inr (Or.inr (Or.inr ⟨?_, l1, trivial⟩))
                  rcases hg with g | g | g
                  · exact absurd (l1.trans l2.symm) g.2.2.2
                  · exact absurd (l1.trans l2.symm) g.2.2.2
                  · exact g.1
                · rcases hb with hb | hb | hb | hb
                  · exact Or.inr (Or.inl ⟨l1, Or.inl hb⟩)
                  · exact Or.inr (Or.inl ⟨l1, Or.inr hb⟩)
                  · exact absurd hb l2
                  · exact Or.inl (Or.inr hb)
              · by_cases l2 : r w = c'
                · rcases ha with ha | ha | ha | ha
                  · exact Or.inr (Or.inr (Or.inl ⟨l2, Or.inl ha⟩))
                  · exact Or.inr (Or.inr (Or.inl ⟨l2, Or.inr ha⟩))
                  · exact absurd ha l1
                  · exact Or.inl (Or.inl ha)
                · left
                  simp only [List.mem_cons, l1, l2, false_or] at h
                  exact h
            · simp at h
            · simp at h
            · exact absurd h.2.2 (by simp)
          · rw [eL]; exact c1
          · rw [eL]; exact c2
          · rw [eL]; exact hK
          · rw [eL]; exact hp
      | cons a T2 =>
        have h' : ∀ i, cond (pr T M G P Xt (C i) k b sl A (a :: T2) T2 a c B e2 K pf (Nat.land e1 (sp T M k a)) (Nat.land e1 (sp T M k c)))
          (Lv T M G P MM Xt (C i) fu k b sl A T2 c B false e1 e2 K pf) false = true := h
        by_cases hex : ∃ w ∈ rest, (l w = a ∧ r w = c) ∨ (l w = c ∧ r w = a)
        · obtain ⟨w, hw, hac⟩ := hex
          have aA : a ∈ A := hT.1 a List.mem_cons_self
          have ndAll := (List.nodup_append.1 H.2.1).1
          have ac : a ≠ c := by
            rintro rfl
            exact (List.nodup_append.1 ndAll).2.2 a aA a List.mem_cons_self rfl
          have hg := H.2.2.2.1 w hw
          have aL : a ∈ A ++ c :: B := List.mem_append_left _ aA
          have cL : c ∈ A ++ c :: B := List.mem_append_right _ List.mem_cons_self
          have la : l w ∈ A ++ c :: B := by rcases hac with h | h <;> rw [h.1] <;> assumption
          have ra : r w ∈ A ++ c :: B := by rcases hac with h | h <;> rw [h.2] <;> assumption
          rcases hg with g | g | g
          · have ew : w = Nat.land a c := by
              rcases hac with q | q
              · rw [← q.1, ← q.2]; exact g.2.1
              · rw [← q.1, ← q.2]; exact g.2.1.trans (Nat.land_comm _ _)
            refine pair_step hG hF hC N0 hw hac (by omega) (b' := b) (by rw [if_neg (by omega)]; rfl) (fun i => ?_)
            have := (cnd (cnd (h' i)).1).1
            rw [g.1, ew]; exact this
          · have ew : w = Nat.lor a c := by
              rcases hac with q | q
              · rw [← q.1, ← q.2]; exact g.2.1
              · rw [← q.1, ← q.2]; exact g.2.1.trans (Nat.lor_comm _ _)
            obtain ⟨L0, n0, e0⟩ := H.next hw
            have hb := (H.step hw la ra n0 e0).2.2.2
            have hor : (l w = Xt ∨ r w = Xt) ↔ (a = Xt ∨ c = Xt) := by
              rcases hac with q | q <;> rw [q.1, q.2]
              exact or_comm
            refine pair_step hG hF hC N0 hw hac (by omega) rfl (fun i => ?_)
            have := (cnd (cnd (h' i)).1).2
            rw [g.1, ew]
            unfold orB at this
            rw [← ew]
            by_cases hx : a = Xt ∨ c = Xt
            · have e : cond (Nat.beq a Xt) true (Nat.beq c Xt) = true := by
                rcases hx with q | q
                · rw [q]; simp
                · rw [q]; cases Nat.beq a Xt <;> simp
              rw [if_pos ⟨g.1, hor.2 hx⟩] at hb
              rw [e, beqf (show b ≠ 0 by omega), ← ew] at this
              rw [if_pos ⟨rfl, hor.2 hx⟩]
              exact this
            · have e : cond (Nat.beq a Xt) true (Nat.beq c Xt) = false := by
                push Not at hx
                rw [beqf hx.1, beqf hx.2]; rfl
              rw [e, ← ew] at this
              rw [if_neg (fun q => hx (hor.1 q.2))]
              exact this
          · exfalso
            have := g.2.2.2
            rcases hac with q | q
            · rw [q.1, q.2] at this; exact ac this.symm
            · rw [q.1, q.2] at this; exact ac this
        · refine ih k b sl A T2 c B false e1 e2 K pf rest (fun i => (cnd (h' i)).2)
            ⟨hn, H, hs, ⟨fun z hz => hT.1 z (List.mem_cons_of_mem _ hz), (List.nodup_cons.1 hT.2).2⟩, ?_, c1, c2, hK, hp⟩
          intro w hw h1 h2
          rcases hE w hw h1 h2 with h | h | h | h
          · exact Or.inl h
          · rcases List.mem_cons.1 h.2 with q | q
            · exact absurd ⟨w, hw, Or.inr ⟨h.1, q⟩⟩ hex
            · exact Or.inr (Or.inl ⟨h.1, q⟩)
          · rcases List.mem_cons.1 h.2 with q | q
            · exact absurd ⟨w, hw, Or.inl ⟨q, h.1⟩⟩ hex
            · exact Or.inr (Or.inr (Or.inl ⟨h.1, q⟩))
          · exact absurd h.2.2 (by simp)

theorem Sr_good {XS gs : List ℕ} {G P : ℕ} {ι : Type} [Nonempty ι] {ck : ι → Pf → Bool}
    (hck : ∀ pf L, PfI op l r XS gs pf L [] → (∀ i, ck i pf = true) → False)
    (hF : CtxF val F M xr yr) (hC : CtxC M G P xr yr) : ∀ n : ℕ,
    Good val op l r F T M MM Xt xr yr XS gs n (fun i : ι => Sr T M G P MM Xt (ck i) n) := by
  intro n
  induction n with
  | zero =>
    intro k b sl A T1 c B nt e1 e2 K pf rest h N
    obtain ⟨hn, H, hs, hT, hE, c1, c2, hK, hp⟩ := N
    obtain rfl := List.length_eq_zero_iff.1 hn
    exact hck pf _ hp h
  | succ n ih => exact Lv_good ih hF hC 200

theorem hd_lt {N : ℕ} (hN : 0 < N) (pf : Pf) : hd N pf < N := by
  cases pf with
  | nil => exact hN
  | cons e t => exact Nat.mod_lt _ hN

theorem Ft_good {XS gs : List ℕ} {n N : ℕ} (hN : 0 < N) {κ : Fin N → Type} {C : (h : Fin N) → κ h → Sty}
    (hG : ∀ h, Good val op l r F T M MM Xt xr yr XS gs n (C h)) :
    Good val op l r F T M MM Xt xr yr XS gs n (fun i : (Σ h : Fin N, κ h) => Ft N i.1 (C i.1 i.2)) := by
  intro k b sl A T1 c B nt e1 e2 K pf rest h N1
  refine hG ⟨hd N pf, hd_lt hN pf⟩ k b sl A T1 c B nt e1 e2 K pf rest (fun j => ?_) N1
  have := h ⟨⟨hd N pf, hd_lt hN pf⟩, j⟩
  simp only [Ft] at this
  simpa using this

-- search with three levels of splitting and a split of the final check
def hs (N : ℕ) (pf : Pf) : ℕ := Nat.mod (List.rec 0 (fun e _ ih => Nat.add e.2.2.2 ih) pf) N
def ckL (ck : Pf → Bool) (N x : ℕ) (pf : Pf) : Bool := cond (Nat.beq (hs N pf) x) (ck pf) true
def srch3 (T M G P MM Xt : ℕ) (ck : Pf → Bool) (X : List ℕ) (N1 k b sl : ℕ) (h n2 j n3 x n4 y : ℕ) : Bool :=
  nh T M G P (Lv T M G P MM Xt (Ft N1 h (Lv T M G P MM Xt (Ft n2 j (Lv T M G P MM Xt (Ft n3 x
    (Sr T M G P MM Xt (ckL ck n4 y) 8)) 200)) 200)) 200) k b sl [] [] X

theorem s3_good {XS gs : List ℕ} {G P : ℕ} {ck : Pf → Bool}
    (hck : ∀ pf L, PfI op l r XS gs pf L [] → ck pf = true → False)
    (hF : CtxF val F M xr yr) (hC : CtxC M G P xr yr) {N1 : ℕ} (hN1 : 0 < N1) (n2 : ℕ → ℕ) (hn2 : ∀ h, 0 < n2 h)
    (n3 : ℕ → ℕ → ℕ) (hn3 : ∀ h j, 0 < n3 h j)
    (n4 : ℕ → ℕ → ℕ → ℕ) (hn4 : ∀ h j x, 0 < n4 h j x) :
    Good val op l r F T M MM Xt xr yr XS gs 11 (fun i : (Σ h : Fin N1, Σ j : Fin (n2 h), Σ x : Fin (n3 h j), Fin (n4 h j x)) =>
      Lv T M G P MM Xt (Ft N1 i.1 (Lv T M G P MM Xt (Ft (n2 i.1) i.2.1 (Lv T M G P MM Xt (Ft (n3 i.1 i.2.1) i.2.2.1
        (Sr T M G P MM Xt (ckL ck (n4 i.1 i.2.1 i.2.2.1) i.2.2.2) 8)) 200)) 200)) 200) := by
  have ne4 : ∀ h j x, Nonempty (Fin (n4 h j x)) := fun h j x => ⟨⟨0, hn4 h j x⟩⟩
  have ne3 : ∀ h j : ℕ, Nonempty (Σ x : Fin (n3 h j), Fin (n4 h j x)) := fun h j => ⟨⟨⟨0, hn3 h j⟩, ⟨0, hn4 h j 0⟩⟩⟩
  have ne2 : ∀ h : ℕ, Nonempty (Σ j : Fin (n2 h), Σ x : Fin (n3 h j), Fin (n4 h j x)) := fun h => ⟨⟨⟨0, hn2 h⟩, ⟨⟨0, hn3 h 0⟩, ⟨0, hn4 h 0 0⟩⟩⟩⟩
  have ne1 : Nonempty (Σ h : Fin N1, Σ j : Fin (n2 h), Σ x : Fin (n3 h j), Fin (n4 h j x)) :=
    ⟨⟨⟨0, hN1⟩, ⟨⟨0, hn2 0⟩, ⟨⟨0, hn3 0 0⟩, ⟨0, hn4 0 0 0⟩⟩⟩⟩⟩
  refine Lv_good (C := fun i : (Σ h : Fin N1, Σ j : Fin (n2 h), Σ x : Fin (n3 h j), Fin (n4 h j x)) =>
      Ft N1 i.1 (Lv T M G P MM Xt (Ft (n2 i.1) i.2.1 (Lv T M G P MM Xt (Ft (n3 i.1 i.2.1) i.2.2.1
        (Sr T M G P MM Xt (ckL ck (n4 i.1 i.2.1 i.2.2.1) i.2.2.2) 8)) 200)) 200)) ?_ hF hC 200
  refine Ft_good (κ := fun h : Fin N1 => Σ j : Fin (n2 h), Σ x : Fin (n3 h j), Fin (n4 h j x))
    (C := fun (h : Fin N1) (y : Σ j : Fin (n2 h), Σ x : Fin (n3 h j), Fin (n4 h j x)) =>
      Lv T M G P MM Xt (Ft (n2 h) y.1 (Lv T M G P MM Xt (Ft (n3 h y.1) y.2.1 (Sr T M G P MM Xt (ckL ck (n4 h y.1 y.2.1) y.2.2) 8)) 200)) 200) hN1 ?_
  intro h
  have := ne2 h
  refine Lv_good (C := fun y : (Σ j : Fin (n2 h), Σ x : Fin (n3 h j), Fin (n4 h j x)) => Ft (n2 h) y.1
    (Lv T M G P MM Xt (Ft (n3 h y.1) y.2.1 (Sr T M G P MM Xt (ckL ck (n4 h y.1 y.2.1) y.2.2) 8)) 200)) ?_ hF hC 200
  refine Ft_good (κ := fun j : Fin (n2 h) => Σ x : Fin (n3 h j), Fin (n4 h j x))
    (C := fun (j : Fin (n2 h)) (y : Σ x : Fin (n3 h j), Fin (n4 h j x)) =>
      Lv T M G P MM Xt (Ft (n3 h j) y.1 (Sr T M G P MM Xt (ckL ck (n4 h j y.1) y.2) 8)) 200) (hn2 h) ?_
  intro j
  have := ne3 h j
  refine Lv_good (C := fun y : (Σ x : Fin (n3 h j), Fin (n4 h j x)) => Ft (n3 h j) y.1 (Sr T M G P MM Xt (ckL ck (n4 h j y.1) y.2) 8)) ?_ hF hC 200
  refine Ft_good (κ := fun x : Fin (n3 h j) => Fin (n4 h j x))
    (C := fun (x : Fin (n3 h j)) (y : Fin (n4 h j x)) => Sr T M G P MM Xt (ckL ck (n4 h j x) y) 8) (hn3 h j) ?_
  intro x
  have := ne4 h j x
  refine Sr_good (ck := fun y : Fin (n4 h j x) => ckL ck (n4 h j x) y) ?_ hF hC 8
  intro pf L hp hall
  apply hck pf L hp
  have hx := hall ⟨hs (n4 h j x) pf, Nat.mod_lt _ (hn4 h j x)⟩
  simp only [ckL] at hx
  simpa using hx

end Core

-- concrete layout of the row pairs
section Layout
variable (Pl Nl : List ℕ) (K1 np nn T M G : ℕ)

def asg (m : ℕ) : Fin 7 → Bool := fun i => m.testBit i
def xr (p : ℕ) : Fin 7 → Bool :=
  asg (cond (Nat.blt p K1) (Pl.getD (p / (nn + 1)) 0) (Pl.getD ((p - K1) % (np + 1)) 0))
def yr (p : ℕ) : Fin 7 → Bool :=
  asg (cond (Nat.blt p K1) (Nl.getD (p % (nn + 1)) 0) (Nl.getD ((p - K1) / (np + 1)) 0))

def encB (h : (Fin 7 → Bool) → Bool) (i : ℕ) : Bool :=
  cond (Nat.blt i T) (M.testBit i && h (xr Pl K1 np nn i)) (M.testBit (i - T) && h (yr Nl K1 np nn (i - T)))
def bitsV (f : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => bitsV f n + cond (f n) (2 ^ n) 0
def enc (h : (Fin 7 → Bool) → Bool) : ℕ := bitsV (encB Pl Nl K1 np nn T M h) (2 * T)

theorem bitsV_lt (f : ℕ → Bool) (n : ℕ) : bitsV f n < 2 ^ n := by
  induction n with
  | zero => simp [bitsV]
  | succ n ih =>
    rw [bitsV, pow_succ]
    cases f n <;> simp <;> omega

theorem bitsV_bit (f : ℕ → Bool) (n i : ℕ) : (bitsV f n).testBit i = (decide (i < n) && f i) := by
  induction n with
  | zero => simp [bitsV]
  | succ n ih =>
    rw [bitsV]
    have hlt := bitsV_lt f n
    cases hf : f n
    · simp only [Bool.cond_false, Nat.add_zero, ih]
      by_cases h : i = n
      · subst h; simp [hf]
      · have : decide (i < n) = decide (i < n + 1) := by
          apply decide_eq_decide.2; omega
        rw [this]
    · simp only [Bool.cond_true]
      rcases lt_trichotomy i n with h | h | h
      · rw [Nat.add_comm, Nat.testBit_two_pow_add_gt h, ih]
        have a : i < n + 1 := by omega
        simp [h, a]
      · subst h
        rw [Nat.add_comm, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt]
        simp [hf]
      · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (b := 2 ^ (n + 1)) (by rw [pow_succ]; omega) (Nat.pow_le_pow_right (by omega) h))]
        have a : ¬ i < n + 1 := by omega
        simp [a]

theorem enc_bit (h : (Fin 7 → Bool) → Bool) (i : ℕ) :
    (enc Pl Nl K1 np nn T M h).testBit i = (decide (i < 2 * T) && encB Pl Nl K1 np nn T M h i) := bitsV_bit _ _ _

theorem enc_sem (hM : M < 2 ^ T) (h : (Fin 7 → Bool) → Bool) (p : ℕ) (hp : M.testBit p = true) :
    (enc Pl Nl K1 np nn T M h).testBit p = h (xr Pl K1 np nn p) ∧
    (enc Pl Nl K1 np nn T M h).testBit (T + p) = h (yr Nl K1 np nn p) := by
  have hpT : p < T := by
    by_contra hc
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hM (Nat.pow_le_pow_right (by omega) (not_lt.1 hc)))] at hp
    exact absurd hp (by simp)
  rw [enc_bit, enc_bit]
  unfold encB
  have a : Nat.blt p T = true := by simpa [Nat.blt_eq] using hpT
  have b : Nat.blt (T + p) T = false := by
    rw [← Bool.not_eq_true, Nat.blt_eq]; omega
  have c : p < 2 * T := by omega
  have d : T + p < 2 * T := by omega
  rw [a, b, Nat.add_sub_cancel_left, hp]
  simp [c, d]

theorem enc_and (h1 h2 : (Fin 7 → Bool) → Bool) : enc Pl Nl K1 np nn T M (fun x => h1 x && h2 x) =
    Nat.land (enc Pl Nl K1 np nn T M h1) (enc Pl Nl K1 np nn T M h2) := by
  apply Nat.eq_of_testBit_eq
  intro i
  change _ = (enc Pl Nl K1 np nn T M h1 &&& enc Pl Nl K1 np nn T M h2).testBit i
  rw [Nat.testBit_and, enc_bit, enc_bit, enc_bit]
  unfold encB
  cases Nat.blt i T <;> cases decide (i < 2 * T) <;> simp <;>
    cases M.testBit _ <;> simp

theorem enc_or (h1 h2 : (Fin 7 → Bool) → Bool) : enc Pl Nl K1 np nn T M (fun x => h1 x || h2 x) =
    Nat.lor (enc Pl Nl K1 np nn T M h1) (enc Pl Nl K1 np nn T M h2) := by
  apply Nat.eq_of_testBit_eq
  intro i
  change _ = (enc Pl Nl K1 np nn T M h1 ||| enc Pl Nl K1 np nn T M h2).testBit i
  rw [Nat.testBit_or, enc_bit, enc_bit, enc_bit]
  unfold encB
  cases Nat.blt i T <;> cases decide (i < 2 * T) <;> simp <;>
    cases M.testBit _ <;> simp

theorem enc_not (h : (Fin 7 → Bool) → Bool) : enc Pl Nl K1 np nn T M (fun x => !h x) =
    Nat.xor (enc Pl Nl K1 np nn T M h) (enc Pl Nl K1 np nn T M (fun _ => true)) := by
  apply Nat.eq_of_testBit_eq
  intro i
  change _ = (enc Pl Nl K1 np nn T M h ^^^ enc Pl Nl K1 np nn T M (fun _ => true)).testBit i
  rw [Nat.testBit_xor, enc_bit, enc_bit, enc_bit]
  unfold encB
  cases Nat.blt i T <;> cases decide (i < 2 * T) <;> simp <;>
    cases M.testBit _ <;> simp

theorem enc_congr {h1 h2 : (Fin 7 → Bool) → Bool} (h : ∀ x, h1 x = h2 x) :
    enc Pl Nl K1 np nn T M h1 = enc Pl Nl K1 np nn T M h2 := by
  rw [show h1 = h2 from funext h]

-- carry projection: a guard bit of e + M is set only if the field of e below it is not empty
theorem carry (e M s t : ℕ) (hst : s ≤ t) (hM : M.testBit t = false) (he : e &&& M = e)
    (hlow : 2 * (M % 2 ^ s) < 2 ^ s) (h : ∀ p, s ≤ p → p < t → e.testBit p = false) :
    (e + M).testBit t = false := by
  have e0 : ∀ p, s ≤ p → p ≤ t → e.testBit p = false := by
    intro p h1 h2
    rcases Nat.lt_or_ge p t with h3 | h3
    · exact h p h1 h3
    · have : p = t := by omega
      subst this
      rw [← he, Nat.testBit_and, hM]; simp
  have hes : e % 2 ^ s ≤ M % 2 ^ s := by
    have : e % 2 ^ s = (e % 2 ^ s) &&& (M % 2 ^ s) := by rw [← Nat.and_mod_two_pow, he]
    rw [this]; exact Nat.and_le_right
  have het : e % 2 ^ (t + 1) = e % 2 ^ s := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
    by_cases hi : i < s
    · have : i < t + 1 := by omega
      simp [hi, this]
    · by_cases hi2 : i < t + 1
      · rw [e0 i (by omega) (by omega)]; simp
      · simp [hi, hi2]
  have hMt : M % 2 ^ (t + 1) = M % 2 ^ t := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
    by_cases hi : i = t
    · subst hi; simp [hM]
    · have : decide (i < t + 1) = decide (i < t) := decide_eq_decide.2 (by omega)
      rw [this]
  have hMt2 : M % 2 ^ t + 2 ^ s ≤ 2 ^ t + M % 2 ^ s := by
    have hdvd : 2 ^ s ∣ 2 ^ t := pow_dvd_pow 2 hst
    have e1 : M % 2 ^ t % 2 ^ s = M % 2 ^ s := Nat.mod_mod_of_dvd _ hdvd
    have hlt : M % 2 ^ t < 2 ^ t := Nat.mod_lt _ (by positivity)
    obtain ⟨q, hq⟩ := hdvd
    have e2 := Nat.div_add_mod (M % 2 ^ t) (2 ^ s)
    rw [e1] at e2
    have : M % 2 ^ t / 2 ^ s < q := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]
      rw [mul_comm]; omega
    have h3 : 2 ^ s * (M % 2 ^ t / 2 ^ s + 1) ≤ 2 ^ s * q := Nat.mul_le_mul_left _ this
    rw [mul_add, mul_one] at h3
    omega
  have hsum : (e + M) % 2 ^ (t + 1) < 2 ^ t := by
    rw [Nat.add_mod, het, hMt]
    refine lt_of_le_of_lt (Nat.mod_le _ _) ?_
    omega
  have : ((e + M) % 2 ^ (t + 1)).testBit t = (e + M).testBit t := by
    rw [Nat.testBit_mod_two_pow]; simp
  rw [← this, Nat.testBit_lt_two_pow hsum]

def chkC : Bool :=
  (List.range T).all fun t => !(G.testBit t) ||
    (!(M.testBit t) &&
     (cond (Nat.blt t K1)
      (Nat.ble nn t && Nat.blt (2 * (M % 2 ^ (t - nn))) (2 ^ (t - nn)) &&
        (List.range nn).all fun d => Nat.blt (t - nn + d) K1 && Nat.beq ((t - nn + d) / (nn + 1)) (t / (nn + 1)))
      (Nat.ble np t && Nat.blt (2 * (M % 2 ^ (t - np))) (2 ^ (t - np)) &&
        (List.range np).all fun d => !(Nat.blt (t - np + d) K1) &&
          Nat.beq ((t - np + d - K1) / (np + 1)) ((t - K1) / (np + 1)))))

variable {Pl Nl K1 np nn T M G}

theorem fieldbit (hc : chkC K1 np nn T M G = true) (hG : G < 2 ^ T) {e t : ℕ}
    (he : ∀ p, e.testBit p = true → M.testBit p = true)
    (ht : (Nat.land (Nat.add e M) G).testBit t = true) :
    ∃ p, e.testBit p = true ∧ (t < K1 → p < K1 ∧ p / (nn + 1) = t / (nn + 1)) ∧
      (K1 ≤ t → K1 ≤ p ∧ (p - K1) / (np + 1) = (t - K1) / (np + 1)) := by
  change ((e + M) &&& G).testBit t = true at ht
  rw [Nat.testBit_and, Bool.and_eq_true] at ht
  have htT : t < T := by
    by_contra h
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hG (Nat.pow_le_pow_right (by omega) (not_lt.1 h)))] at ht
    exact absurd ht.2 (by simp)
  have he' : e &&& M = e := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    cases h : e.testBit i
    · simp
    · simp [he i h]
  unfold chkC at hc
  have hc := List.all_eq_true.1 hc t (List.mem_range.2 htT)
  rw [ht.2] at hc
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true'] at hc
  obtain ⟨hMt, hc⟩ := hc
  by_cases hk : t < K1
  · have hb : Nat.blt t K1 = true := by simpa [Nat.blt_eq] using hk
    rw [hb] at hc
    simp only [Bool.cond_true, Bool.and_eq_true, List.all_eq_true, List.mem_range, Nat.blt_eq, Nat.beq_eq] at hc
    obtain ⟨⟨h1, h2⟩, h3⟩ := hc
    have h1 : nn ≤ t := Nat.ble_eq.mp h1
    by_contra hcon
    push Not at hcon
    have := carry e M (t - nn) t (by omega) hMt he' h2 (by
      intro p hp1 hp2
      by_contra hb
      rw [Bool.not_eq_false] at hb
      have q := h3 (p - (t - nn)) (by omega)
      rw [show t - nn + (p - (t - nn)) = p by omega] at q
      exact absurd (hcon p hb (fun _ => q) ).1 (by omega))
    rw [this] at ht
    exact absurd ht.1 (by simp)
  · have hb : Nat.blt t K1 = false := by rw [← Bool.not_eq_true, Nat.blt_eq]; exact hk
    rw [hb] at hc
    simp only [Bool.cond_false, Bool.and_eq_true, List.all_eq_true, List.mem_range, Nat.blt_eq, Nat.beq_eq,
      Bool.not_eq_true'] at hc
    obtain ⟨⟨h1, h2⟩, h3⟩ := hc
    have h1 : np ≤ t := Nat.ble_eq.mp h1
    by_contra hcon
    push Not at hcon
    have := carry e M (t - np) t (by omega) hMt he' h2 (by
      intro p hp1 hp2
      by_contra hb
      rw [Bool.not_eq_false] at hb
      have q := h3 (p - (t - np)) (by omega)
      rw [show t - np + (p - (t - np)) = p by omega, ← Bool.not_eq_true, Nat.blt_eq] at q
      have r := hcon p hb (fun h => absurd h hk)
      exact r.2 (by omega) q.2)
    rw [this] at ht
    exact absurd ht.1 (by simp)

theorem ctxC_of (hc : chkC K1 np nn T M G = true) (hG : G < 2 ^ T) :
    CtxC M G (2 ^ K1) (xr Pl K1 np nn) (yr Nl K1 np nn) := by
  intro e e' he he' hcf
  set g := Nat.land (Nat.add e M) G with hg
  set g' := Nat.land (Nat.add e' M) G with hg'
  unfold cfl at hcf
  have h1 : Nat.ble (2 ^ K1) (Nat.land g g') = true := by
    cases h : Nat.ble (2 ^ K1) (Nat.land g g')
    · rw [h] at hcf; simp at hcf
    · rfl
  rw [h1] at hcf
  have h2 : Nat.land g g' % 2 ^ K1 ≠ 0 := by
    intro h
    have : Nat.beq (Nat.mod (Nat.land g g') (2 ^ K1)) 0 = true := by
      rw [Nat.beq_eq]; exact h
    rw [this] at hcf
    simp at hcf
  have h1 : 2 ^ K1 ≤ Nat.land g g' := Nat.ble_eq.mp h1
  constructor
  · obtain ⟨t, ht⟩ := Nat.exists_testBit_of_ne_zero h2
    rw [Nat.testBit_mod_two_pow, Bool.and_eq_true, decide_eq_true_eq] at ht
    obtain ⟨hk, ht⟩ := ht
    change (g &&& g').testBit t = true at ht
    rw [Nat.testBit_and, Bool.and_eq_true] at ht
    obtain ⟨p, p1, p2, _⟩ := fieldbit hc hG he ht.1
    obtain ⟨q, q1, q2, _⟩ := fieldbit hc hG he' ht.2
    refine ⟨p, q, p1, q1, ?_⟩
    have a : Nat.blt p K1 = true := by simpa [Nat.blt_eq] using (p2 hk).1
    have b : Nat.blt q K1 = true := by simpa [Nat.blt_eq] using (q2 hk).1
    unfold xr
    rw [a, b, (p2 hk).2, (q2 hk).2]
    rfl
  · have : Nat.land g g' / 2 ^ K1 ≠ 0 := by
      have := Nat.div_pos h1 (by positivity)
      omega
    obtain ⟨t, ht⟩ := Nat.exists_testBit_of_ne_zero this
    rw [Nat.testBit_div_two_pow] at ht
    change (g &&& g').testBit (t + K1) = true at ht
    rw [Nat.testBit_and, Bool.and_eq_true] at ht
    obtain ⟨p, p1, _, p2⟩ := fieldbit hc hG he ht.1
    obtain ⟨q, q1, _, q2⟩ := fieldbit hc hG he' ht.2
    refine ⟨p, q, p1, q1, ?_⟩
    have p2 := p2 (by omega)
    have q2 := q2 (by omega)
    have a : Nat.blt p K1 = false := by rw [← Bool.not_eq_true, Nat.blt_eq]; omega
    have b : Nat.blt q K1 = false := by rw [← Bool.not_eq_true, Nat.blt_eq]; omega
    unfold yr
    rw [a, b, p2.2, q2.2]
    rfl

end Layout

-- runs of words
abbrev Tr := ℕ × ℕ × ℕ
def outW (MM : ℕ) (t : Tr) : ℕ :=
  if t.1 = 0 then Nat.land t.2.1 t.2.2 else if t.1 = 1 then Nat.lor t.2.1 t.2.2 else Nat.xor t.2.1 MM
def WRun (MM q : ℕ) : List ℕ → List Tr → Prop
  | _, [] => True
  | L, t :: ts => t.1 ≤ q ∧ t.2.1 ∈ L ∧ t.2.2 ∈ L ∧ (2 ≤ t.1 → t.2.2 = t.2.1) ∧ WRun MM q (outW MM t :: L) ts
def Rch (MM q F : ℕ) (X : List ℕ) (n : ℕ) : Prop :=
  ∃ ts : List Tr, WRun MM q X ts ∧ ts.length = n ∧ F ∈ X ++ ts.map (outW MM)

theorem WRun.mono {MM q : ℕ} {ts : List Tr} : ∀ {L L' : List ℕ}, (∀ z ∈ L, z ∈ L') → WRun MM q L ts → WRun MM q L' ts := by
  induction ts with
  | nil => intro L L' _ _; trivial
  | cons t ts ih =>
    intro L L' h ⟨a, b, c, d, e⟩
    refine ⟨a, h _ b, h _ c, d, ih ?_ e⟩
    intro z hz
    rcases List.mem_cons.1 hz with rfl | hz
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (h z hz)

theorem WRun.restrict {MM q : ℕ} {ts : List Tr} : ∀ {L L' : List ℕ},
    (∀ z ∈ L, (∃ t ∈ ts, t.2.1 = z ∨ t.2.2 = z) → z ∈ L') → WRun MM q L ts → WRun MM q L' ts := by
  induction ts with
  | nil => intro L L' _ _; trivial
  | cons t ts ih =>
    intro L L' h ⟨a, b, c, d, e⟩
    refine ⟨a, h _ b ⟨t, List.mem_cons_self, Or.inl rfl⟩, h _ c ⟨t, List.mem_cons_self, Or.inr rfl⟩, d, ih ?_ e⟩
    intro z hz ⟨w', hw', hu⟩
    rcases List.mem_cons.1 hz with rfl | hz
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (h z hz ⟨w', List.mem_cons_of_mem _ hw', hu⟩)

theorem WRun.split {MM q : ℕ} {a b : List Tr} : ∀ {L : List ℕ}, WRun MM q L (a ++ b) →
    WRun MM q L a ∧ WRun MM q (L ++ a.map (outW MM)) b := by
  induction a with
  | nil => intro L h; exact ⟨trivial, by simpa using h⟩
  | cons t a ih =>
    intro L ⟨h1, h2, h3, h4, h5⟩
    obtain ⟨p, p'⟩ := ih h5
    refine ⟨⟨h1, h2, h3, h4, p⟩, p'.mono ?_⟩
    intro z hz; simp only [List.map_cons, List.mem_append, List.mem_cons] at hz ⊢; tauto

theorem WRun.join {MM q : ℕ} {a b : List Tr} : ∀ {L : List ℕ}, WRun MM q L a →
    WRun MM q (L ++ a.map (outW MM)) b → WRun MM q L (a ++ b) := by
  induction a with
  | nil => intro L _ h; simpa using h
  | cons t a ih =>
    intro L ⟨h1, h2, h3, h4, h5⟩ h
    refine ⟨h1, h2, h3, h4, ih h5 (h.mono ?_)⟩
    intro z hz; simp only [List.map_cons, List.mem_append, List.mem_cons] at hz ⊢; tauto

theorem nodup_splits {l : List ℕ} : ∀ {X : List ℕ}, X.Nodup → (∀ a t b, l = a ++ t :: b → t ∉ X ++ a) → (X ++ l).Nodup := by
  induction l with
  | nil => intro X h _; simpa using h
  | cons t l ih =>
    intro X hX h
    have e : X ++ t :: l = (X ++ [t]) ++ l := by simp
    rw [e]
    apply ih
    · rw [List.nodup_append]
      refine ⟨hX, by simp, ?_⟩
      rintro z hz z' hz' rfl
      simp only [List.mem_singleton] at hz'
      have := h [] t l rfl
      rw [List.append_nil] at this
      exact this (hz' ▸ hz)
    · rintro a t' b rfl
      have := h (t :: a) t' b rfl
      simpa using this

section RunInv
variable (Pl Nl : List ℕ) (K1 np nn T M : ℕ)

def IsEnc (z : ℕ) : Prop := ∃ h, enc Pl Nl K1 np nn T M h = z

open Classical in
noncomputable def idx (p0 : ℕ) (x : Fin 7 → Bool) : ℕ :=
  if h : ∃ p, M.testBit p = true ∧ xr Pl K1 np nn p = x then Classical.choose h
  else if h : ∃ p, M.testBit p = true ∧ yr Nl K1 np nn p = x then T + Classical.choose h else p0

noncomputable def vl (p0 z : ℕ) (x : Fin 7 → Bool) : Bool := z.testBit (idx Pl Nl K1 np nn T M p0 x)

variable {Pl Nl K1 np nn T M}

theorem idx_enc (hM : M < 2 ^ T) {p0 : ℕ} (h0 : M.testBit p0 = true) (x : Fin 7 → Bool) :
    (enc Pl Nl K1 np nn T M (fun _ => true)).testBit (idx Pl Nl K1 np nn T M p0 x) = true := by
  unfold idx
  split_ifs with h h2
  · exact (enc_sem Pl Nl K1 np nn T M hM _ _ (Classical.choose_spec h).1).1
  · exact (enc_sem Pl Nl K1 np nn T M hM _ _ (Classical.choose_spec h2).1).2
  · exact (enc_sem Pl Nl K1 np nn T M hM _ _ h0).1

theorem sem_of_enc (hM : M < 2 ^ T) {p0 z : ℕ} (hz : IsEnc Pl Nl K1 np nn T M z) :
    Sem (vl Pl Nl K1 np nn T M p0) T M (xr Pl K1 np nn) (yr Nl K1 np nn) z := by
  obtain ⟨h, rfl⟩ := hz
  intro p hp
  have key : ∀ x, ((∃ p, M.testBit p = true ∧ xr Pl K1 np nn p = x) ∨ (∃ p, M.testBit p = true ∧ yr Nl K1 np nn p = x)) →
      vl Pl Nl K1 np nn T M p0 (enc Pl Nl K1 np nn T M h) x = h x := by
    intro x hx
    unfold vl idx
    split_ifs with h1 h2
    · have := Classical.choose_spec h1
      rw [(enc_sem Pl Nl K1 np nn T M hM _ _ this.1).1, this.2]
    · have := Classical.choose_spec h2
      rw [(enc_sem Pl Nl K1 np nn T M hM _ _ this.1).2, this.2]
    · exact absurd hx (not_or.2 ⟨h1, h2⟩)
  obtain ⟨a, b⟩ := enc_sem Pl Nl K1 np nn T M hM h p hp
  rw [a, b, key _ (Or.inl ⟨p, hp, rfl⟩), key _ (Or.inr ⟨p, hp, rfl⟩)]
  exact ⟨rfl, rfl⟩

theorem isEnc_out {MM : ℕ} (hMM : enc Pl Nl K1 np nn T M (fun _ => true) = MM) {t : Tr}
    (h1 : IsEnc Pl Nl K1 np nn T M t.2.1) (h2 : IsEnc Pl Nl K1 np nn T M t.2.2) :
    IsEnc Pl Nl K1 np nn T M (outW MM t) := by
  obtain ⟨f, hf⟩ := h1
  obtain ⟨g, hg⟩ := h2
  unfold outW
  split_ifs
  · exact ⟨fun x => f x && g x, by rw [enc_and, hf, hg]⟩
  · exact ⟨fun x => f x || g x, by rw [enc_or, hf, hg]⟩
  · exact ⟨fun x => !f x, by rw [enc_not, hf, hMM]⟩

theorem isEnc_run {MM q : ℕ} (hMM : enc Pl Nl K1 np nn T M (fun _ => true) = MM) {ts : List Tr} :
    ∀ {L : List ℕ}, (∀ z ∈ L, IsEnc Pl Nl K1 np nn T M z) → WRun MM q L ts →
    ∀ z ∈ L ++ ts.map (outW MM), IsEnc Pl Nl K1 np nn T M z := by
  induction ts with
  | nil => intro L h _ z hz; exact h z (by simpa using hz)
  | cons t ts ih =>
    intro L h ⟨_, b, c, _, e⟩ z hz
    refine ih (L := outW MM t :: L) ?_ e z ?_
    · intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · exact isEnc_out hMM (h _ b) (h _ c)
      · exact h z hz
    · simp only [List.map_cons, List.mem_append, List.mem_cons] at hz ⊢; tauto

def tro (MM : ℕ) (ts : List Tr) (w : ℕ) : Tr := (ts.find? (fun t => Nat.beq (outW MM t) w)).getD (0, 0, 0)

theorem tro_eq {MM : ℕ} {ts : List Tr} (hn : (ts.map (outW MM)).Nodup) {t : Tr} (ht : t ∈ ts) :
    tro MM ts (outW MM t) = t := by
  unfold tro
  cases h : ts.find? (fun s => Nat.beq (outW MM s) (outW MM t)) with
  | none =>
    have := List.find?_eq_none.1 h t ht
    simp at this
  | some s =>
    have h1 := List.mem_of_find?_eq_some h
    have h2 := List.find?_some h
    simp only [Nat.beq_eq] at h2
    simp only [Option.getD_some]
    exact List.inj_on_of_nodup_map hn h1 ht h2

theorem run_irr {MM q : ℕ} {ts : List Tr} : ∀ {L : List ℕ}, WRun MM q L ts → (L ++ ts.map (outW MM)).Nodup →
    ∀ t ∈ ts, outW MM t ≠ t.2.1 ∧ outW MM t ≠ t.2.2 ∧ t.1 ≤ q ∧ (2 ≤ t.1 → t.2.2 = t.2.1) := by
  induction ts with
  | nil => intro L _ _ t h; simp at h
  | cons s ts ih =>
    intro L ⟨a, b, c, d, e⟩ hn t ht
    rw [List.map_cons] at hn
    have hd := (List.nodup_append.1 hn).2.2
    rcases List.mem_cons.1 ht with rfl | ht
    · exact ⟨fun h => hd _ b _ List.mem_cons_self h.symm, fun h => hd _ c _ List.mem_cons_self h.symm, a, d⟩
    · refine ih (L := outW MM s :: L) e ?_ t ht
      exact (List.perm_middle (l₁ := L)).nodup_iff.1 hn

theorem least_nodup {MM q F n : ℕ} {X : List ℕ} (hX : X.Nodup) (hl : ∀ m < n, ¬ Rch MM q F X m) {ts : List Tr}
    (hr : WRun MM q X ts) (hn : ts.length = n) (hF : F ∈ X ++ ts.map (outW MM)) :
    (X ++ ts.map (outW MM)).Nodup := by
  apply nodup_splits hX
  intro a w b hab hw
  obtain ⟨a', c, rfl, ha, hc⟩ := List.map_eq_append_iff.1 hab
  obtain ⟨t, b', rfl, ht, hb⟩ := List.map_eq_cons_iff.1 hc
  obtain ⟨r1, r2⟩ := hr.split
  subst ht ha hb
  refine hl (a'.length + b'.length) (by rw [← hn]; simp) ⟨a' ++ b', ?_, by simp, ?_⟩
  · refine r1.join (r2.2.2.2.2.mono ?_)
    intro z hz
    rcases List.mem_cons.1 hz with rfl | hz
    · exact hw
    · exact hz
  · simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons] at hF hw ⊢
    rcases hF with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · rw [h]; rcases hw with q | q
      · exact Or.inl q
      · exact Or.inr (Or.inl q)
    · exact Or.inr (Or.inr h)

theorem least_used {MM q F n : ℕ} {X : List ℕ} (hl : ∀ m < n, ¬ Rch MM q F X m) {ts : List Tr}
    (hr : WRun MM q X ts) (hn : ts.length = n) (hF : F ∈ X ++ ts.map (outW MM)) :
    ∀ t ∈ ts, outW MM t = F ∨ ∃ s ∈ ts, s.2.1 = outW MM t ∨ s.2.2 = outW MM t := by
  intro t ht
  by_contra hcon
  push Not at hcon
  obtain ⟨hne, hno⟩ := hcon
  obtain ⟨a, b, rfl⟩ := List.append_of_mem ht
  obtain ⟨r1, r2⟩ := hr.split
  refine hl (a.length + b.length) (by rw [← hn]; simp) ⟨a ++ b, ?_, by simp, ?_⟩
  · refine r1.join (r2.2.2.2.2.restrict ?_)
    rintro z hz ⟨s, hs, hu⟩
    rcases List.mem_cons.1 hz with rfl | hz
    · exfalso
      have := hno s (by simp [hs])
      rcases hu with h | h
      · exact this.1 h
      · exact this.2 h
    · exact hz
  · simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons] at hF ⊢
    rcases hF with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact absurd h.symm hne
    · exact Or.inr (Or.inr h)

def depChk (T M kk : ℕ) (X : List ℕ) : Bool :=
  X.all fun z => !(Nat.beq ((X.erase z).foldr (fun w s => Nat.lor (sp T M kk w) s) 0) M)

theorem fold_bit (T M kk : ℕ) (l : List ℕ) (p : ℕ) (h : ∀ z ∈ l, (sp T M kk z).testBit p = false) :
    (l.foldr (fun w s => Nat.lor (sp T M kk w) s) 0).testBit p = false := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.foldr_cons]
    change (sp T M kk a ||| _).testBit p = false
    rw [Nat.testBit_or, h a List.mem_cons_self, ih (fun z hz => h z (List.mem_cons_of_mem _ hz))]; rfl

theorem fold_sub (T M kk : ℕ) (l : List ℕ) (p : ℕ)
    (h : (l.foldr (fun w s => Nat.lor (sp T M kk w) s) 0).testBit p = true) : ∃ z ∈ l, (sp T M kk z).testBit p = true := by
  by_contra hcon
  push Not at hcon
  rw [fold_bit T M kk l p (fun z hz => by simpa using hcon z hz)] at h
  exact absurd h (by simp)

theorem run_inv (hM : M < 2 ^ T) {p0 : ℕ} (h0 : M.testBit p0 = true)
    {MM : ℕ} (hMM : enc Pl Nl K1 np nn T M (fun _ => true) = MM)
    {X : List ℕ} (hX : X.Nodup) (hXe : ∀ z ∈ X, IsEnc Pl Nl K1 np nn T M z) {q n : ℕ} (hq : q ≤ 2)
    {kk : ℕ} (hkk : kk = 0 → q ≤ 1) (hdep : depChk T M kk X = true)
    (hl : ∀ m < n, ¬ Rch MM q M X m) {ts : List Tr}
    (hr : WRun MM q X ts) (hn : ts.length = n) (hF : M ∈ X ++ ts.map (outW MM)) {Xt b : ℕ}
    (hb : cO (fun w => (tro MM ts w).1) (fun w => (tro MM ts w).2.1) (fun w => (tro MM ts w).2.2) Xt (ts.map (outW MM)) ≤ b) :
    Inv (vl Pl Nl K1 np nn T M p0) (fun w => (tro MM ts w).1) (fun w => (tro MM ts w).2.1) (fun w => (tro MM ts w).2.2)
      M T M MM Xt (xr Pl K1 np nn) (yr Nl K1 np nn) X (ts.map (outW MM))
      (cN (fun w => (tro MM ts w).1) (ts.map (outW MM))) b := by
  have hnd := least_nodup hX hl hr hn hF
  have hus := least_used hl hr hn hF
  have hirr := run_irr hr hnd
  have hno : (ts.map (outW MM)).Nodup := (List.nodup_append.1 hnd).2.1
  have htr : ∀ t ∈ ts, tro MM ts (outW MM t) = t := fun t ht => tro_eq hno ht
  have hval : ∀ (us : List Tr) (L : List ℕ), WRun MM q L us → (∀ t ∈ us, tro MM ts (outW MM t) = t) →
      Valid (fun w => (tro MM ts w).2.1) (fun w => (tro MM ts w).2.2) L (us.map (outW MM)) := by
    intro us
    induction us with
    | nil => intro L _ _; trivial
    | cons u us ih =>
      intro L ⟨a, b, c, d, e⟩ ht
      have hu := ht u List.mem_cons_self
      refine ⟨?_, ?_, ih _ e (fun t h => ht t (List.mem_cons_of_mem _ h))⟩
      · show (tro MM ts (outW MM u)).2.1 ∈ L
        rw [hu]; exact b
      · show (tro MM ts (outW MM u)).2.2 ∈ L
        rw [hu]; exact c
  have henc := isEnc_run hMM hXe hr
  have hgate : ∀ w ∈ ts.map (outW MM), GateOk (vl Pl Nl K1 np nn T M p0) (fun w => (tro MM ts w).1)
      (fun w => (tro MM ts w).2.1) (fun w => (tro MM ts w).2.2) MM w := by
    intro w hw
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hw
    obtain ⟨i1, i2, i3, i4⟩ := hirr t ht
    unfold GateOk
    simp only [htr t ht]
    have hne : t.1 = 0 ∨ t.1 = 1 → t.2.1 ≠ t.2.2 := by
      intro h e
      apply i1
      unfold outW
      rcases h with h | h
      · rw [if_pos h, ← e]; exact Nat.and_self _
      · rw [if_neg (by omega), if_pos h, ← e]; exact Nat.or_self _
    rcases (by omega : t.1 = 0 ∨ t.1 = 1 ∨ t.1 = 2) with h | h | h
    · refine Or.inl ⟨h, by unfold outW; rw [if_pos h], ?_, hne (Or.inl h)⟩
      intro x
      unfold vl outW
      rw [if_pos h]
      exact Nat.testBit_and _ _ _
    · refine Or.inr (Or.inl ⟨h, by unfold outW; rw [if_neg (by omega), if_pos h], ?_, hne (Or.inr h)⟩)
      intro x
      unfold vl outW
      rw [if_neg (by omega), if_pos h]
      exact Nat.testBit_or _ _ _
    · refine Or.inr (Or.inr ⟨h, by unfold outW; rw [if_neg (by omega), if_neg (by omega)], ?_, i4 (by omega)⟩)
      intro x
      unfold vl outW
      rw [if_neg (by omega), if_neg (by omega)]
      have := idx_enc (Pl := Pl) (Nl := Nl) (K1 := K1) (np := np) (nn := nn) hM h0 x
      rw [hMM] at this
      show (t.2.1 ^^^ MM).testBit _ = _
      rw [Nat.testBit_xor, this]; simp
  have hsem : ∀ z ∈ X ++ ts.map (outW MM), Sem (vl Pl Nl K1 np nn T M p0) T M (xr Pl K1 np nn) (yr Nl K1 np nn) z :=
    fun z hz => sem_of_enc hM (henc z hz)
  have hMlt : ∀ p, M.testBit (T + p) = false := fun p =>
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hM (Nat.pow_le_pow_right (by omega) (by omega)))
  have hVF : ∀ p, M.testBit p = true → vl Pl Nl K1 np nn T M p0 M (xr Pl K1 np nn p) = true ∧
      vl Pl Nl K1 np nn T M p0 M (yr Nl K1 np nn p) = false := by
    intro p hp
    obtain ⟨a, b⟩ := hsem M hF p hp
    rw [← a, ← b]; exact ⟨hp, hMlt p⟩
  refine ⟨hval ts X hr htr, hnd, hsem, hgate, ?_, hF, rfl, hb⟩
  intro z hz
  rcases List.mem_append.1 hz with hz | hz
  · by_contra hcon
    unfold Used at hcon
    push Not at hcon
    obtain ⟨hz1, hz2⟩ := hcon
    have hc := List.all_eq_true.1 hdep z hz
    simp only [Bool.not_eq_true'] at hc
    have : (X.erase z).foldr (fun w s => Nat.lor (sp T M kk w) s) 0 ≠ M := by
      intro h; rw [h, Nat.beq_refl] at hc; exact absurd hc (by simp)
    apply this
    apply Nat.eq_of_testBit_eq
    intro p
    cases hp : M.testBit p
    · rw [fold_bit]
      intro z hz
      by_contra h
      rw [Bool.not_eq_false] at h
      rw [sp_sub _ _ _ _ _ h] at hp
      exact absurd hp (by simp)
    · by_contra hfalse
      rw [Bool.not_eq_true] at hfalse
      have hvalid : Valid (fun w => (tro MM ts w).2.1) (fun w => (tro MM ts w).2.2) (X.erase z) (ts.map (outW MM)) := by
        refine (hval ts X hr htr).restrict ?_
        rintro v hv ⟨w, hw, hu⟩
        rw [hX.mem_erase_iff]
        refine ⟨?_, hv⟩
        rintro rfl
        rcases hu with h | h
        · exact (hz2 w hw).1 h
        · exact (hz2 w hw).2 h
      have hF' : M ∈ X.erase z ++ ts.map (outW MM) := by
        rcases List.mem_append.1 hF with h | h
        · exact List.mem_append_left _ (hX.mem_erase_iff.2 ⟨fun e => hz1 e.symm, h⟩)
        · exact List.mem_append_right _ h
      obtain ⟨v1, v2⟩ := hVF p hp
      have : ∃ z' ∈ X.erase z, Sp (vl Pl Nl K1 np nn T M p0) kk z' (xr Pl K1 np nn p) (yr Nl K1 np nn p) := by
        unfold Sp
        by_cases hk : kk = 0
        · simp only [if_pos hk]
          refine cov_pos hvalid hgate ?_ M hF' v1 v2
          intro w hw h2
          obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hw
          simp only [htr t ht] at h2
          have := (hirr t ht).2.2.1
          have := hkk hk
          omega
        · simp only [if_neg hk]
          exact cov_any hvalid hgate M hF' (by rw [v1, v2]; simp)
      obtain ⟨z', hz', hs⟩ := this
      have hb1 := (sp_sem (hsem z' (List.mem_append_left _ (List.mem_of_mem_erase hz'))) kk p).2 ⟨hp, hs⟩
      have : ((X.erase z).foldr (fun w s => Nat.lor (sp T M kk w) s) 0).testBit p = true := by
        by_contra h
        rw [Bool.not_eq_true] at h
        have key : ∀ l : List ℕ, z' ∈ l → (l.foldr (fun w s => Nat.lor (sp T M kk w) s) 0).testBit p = true := by
          intro l
          induction l with
          | nil => intro h; simp at h
          | cons a l ih =>
            intro h
            rw [List.foldr_cons]
            change (sp T M kk a ||| _).testBit p = true
            rw [Nat.testBit_or]
            rcases List.mem_cons.1 h with rfl | h
            · rw [hb1]; rfl
            · rw [ih h]; simp
        rw [key _ hz'] at h
        exact absurd h (by simp)
      rw [this] at hfalse
      exact absurd hfalse (by simp)
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hz
    rcases hus t ht with h | ⟨s, hs, h⟩
    · exact Or.inl h
    · refine Or.inr ⟨outW MM s, List.mem_map_of_mem hs, ?_⟩
      simp only [htr s hs]
      exact h

-- a successful search refutes every state with the given parameters
theorem search_false {val : ℕ → (Fin 7 → Bool) → Bool} {op l r : ℕ → ℕ} {F T M MM Xt G P : ℕ} {xr yr : ℕ → Fin 7 → Bool}
    {X rest : List ℕ} {k b sl n : ℕ} {ι : Type} {C : ι → Sty} (hX : X ≠ [])
    (hG : Good val op l r F T M MM Xt xr yr X rest n C) (hF : CtxF val F M xr yr) (hC : CtxC M G P xr yr)
    (H : Inv val op l r F T M MM Xt xr yr X rest k b) (hn : rest.length = n) (hs : X.length + k + sl = n + 1)
    (h : ∀ i, nh T M G P (C i) k b sl [] [] X = true) : False := by
  refine nh_good hG hF hC hX h hn (by simpa using H) (by simpa using hs) (fun w _ ha => by simp at ha) ?_
  refine ⟨by simp, by simp [wds], trivial, ?_⟩
  intro z hz
  exact Or.inl (by simpa using hz)

end RunInv

-- final check of a complete gate list against the shifted circuit
def px (XS : List ℕ) (u : ℕ) : ℕ := List.rec 0 (fun a _ ih => cond (Nat.beq a u) 0 (Nat.succ ih)) XS
def ln (pf : Pf) : ℕ := List.rec 7 (fun _ _ ih => Nat.succ ih) pf
def ps (XS : List ℕ) (u : ℕ) (pf : Pf) : ℕ :=
  List.rec (px XS u) (fun e t ih => cond (Nat.beq e.2.2.2 u) (ln t) ih) pf
def lt2 (ch : List ℕ) : Bool := List.rec true (fun _ t _ => List.rec true (fun _ _ _ => false) t) ch
def rdO (full v : ℕ) (ch : List ℕ) (u : ℕ) (k : ℕ → List ℕ → Bool) : Bool :=
  cond (k v ch) (cond (mem u ch) (k full ch) (cond (lt2 ch) (k full (u :: ch)) true)) false
def gt (env p : ℕ) : ℕ := Nat.land (Nat.shiftRight env (Nat.mul 8 p)) 255
def dst (XS : List ℕ) (e : ℕ × ℕ × ℕ × ℕ) (t : Pf) (full : ℕ) (k : ℕ → List ℕ → Bool) (env : ℕ) (ch : List ℕ) : Bool :=
  rdO full (gt env (ps XS e.2.1 t)) ch e.2.1 fun x ch1 => rdO full (gt env (ps XS e.2.2.1 t)) ch1 e.2.2.1 fun y ch2 =>
    k (Nat.lor env (Nat.shiftLeft (cond (Nat.beq e.1 0) (Nat.land x y) (Nat.lor x y)) (Nat.mul 8 (ln t)))) ch2
def Dc (XS : List ℕ) (full : ℕ) (env0 : ℕ) (pf : Pf) : (ℕ → List ℕ → Bool) → Bool :=
  List.rec (fun k => k env0 []) (fun e t ih k => ih (dst XS e t full k)) pf
def ckD (XS : List ℕ) (full tgt F : ℕ) (env0 : ℕ) (pf : Pf) : Bool :=
  Dc XS full env0 pf fun env _ => cond (Nat.beq (gt env (ps XS F pf)) tgt) false true

theorem ps_cons (XS : List ℕ) (u : ℕ) (e : ℕ × ℕ × ℕ × ℕ) (t : Pf) :
    ps XS u (e :: t) = cond (Nat.beq e.2.2.2 u) (ln t) (ps XS u t) := rfl
theorem ln_cons (e : ℕ × ℕ × ℕ × ℕ) (t : Pf) : ln (e :: t) = ln t + 1 := rfl
theorem px_lt {XS : List ℕ} {u : ℕ} (h : u ∈ XS) : px XS u < XS.length := by
  induction XS with
  | nil => simp at h
  | cons a l ih =>
    have e : px (a :: l) u = cond (Nat.beq a u) 0 (Nat.succ (px l u)) := rfl
    rw [e]
    by_cases h' : a = u
    · subst h'; simp
    · rw [beqf h']
      have := ih (by rcases List.mem_cons.1 h with q | q; exact absurd q.symm h'; exact q)
      simp only [Bool.cond_false, List.length_cons]; omega
theorem ps_lt {XS : List ℕ} (h7 : XS.length = 7) {u : ℕ} {pf : Pf} (h : u ∈ XS ∨ u ∈ wds pf) : ps XS u pf < ln pf := by
  induction pf with
  | nil =>
    rcases h with h | h
    · have := px_lt h; rw [h7] at this; exact this
    · simp [wds] at h
  | cons e t ih =>
    rw [ps_cons, ln_cons]
    by_cases h' : e.2.2.2 = u
    · rw [h']; simp
    · rw [beqf h']
      have := ih (by
        rcases h with q | q
        · exact Or.inl q
        · rcases List.mem_cons.1 q with q | q
          · exact absurd q.symm h'
          · exact Or.inr q)
      simp only [Bool.cond_false]; omega

theorem gt_bit (env p i : ℕ) : (gt env p).testBit i = (env.testBit (8 * p + i) && decide (i < 8)) := by
  change ((env >>> (8 * p)) &&& 255).testBit i = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight, show (255 : ℕ) = 2 ^ 8 - 1 from rfl, Nat.testBit_two_pow_sub_one]

theorem gt_old {env v p m : ℕ} (hp : p < m) : gt (Nat.lor env (Nat.shiftLeft v (Nat.mul 8 m))) p = gt env p := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [gt_bit, gt_bit]
  change ((env ||| (v <<< (8 * m))).testBit (8 * p + i) && _) = _
  rw [Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases hi : i < 8
  · have : ¬ (8 * p + i ≥ 8 * m) := by omega
    simp [this]
  · simp [hi]

theorem gt_new {env v m : ℕ} (he : env < 2 ^ (8 * m)) (hv : v < 256) : gt (Nat.lor env (Nat.shiftLeft v (Nat.mul 8 m))) m = v := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [gt_bit]
  change ((env ||| (v <<< (8 * m))).testBit (8 * m + i) && _) = _
  rw [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_lt_two_pow (lt_of_lt_of_le he (Nat.pow_le_pow_right (by omega) (by omega)))]
  by_cases hi : i < 8
  · have : 8 * m + i ≥ 8 * m := by omega
    simp [hi]
  · have : v.testBit i = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le (b := 2 ^ 8) (by omega) (Nat.pow_le_pow_right (by omega) (by omega)))
    simp [hi, this]

theorem env_lt {env v m : ℕ} (he : env < 2 ^ (8 * m)) (hv : v < 256) : Nat.lor env (Nat.shiftLeft v (Nat.mul 8 m)) < 2 ^ (8 * (m + 1)) := by
  change env ||| (v <<< (8 * m)) < _
  apply Nat.or_lt_two_pow
  · exact lt_of_lt_of_le he (Nat.pow_le_pow_right (by omega) (by omega))
  · rw [Nat.shiftLeft_eq, show 8 * (m + 1) = 8 + 8 * m by ring, pow_add]
    exact Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)

theorem lt2_of {ch : List ℕ} (h : ch.length < 2) : lt2 ch = true := by
  match ch, h with
  | [], _ => rfl
  | [_], _ => rfl

section Dpart
variable (dv : ℕ → ℕ) (full wa wb : ℕ)
def Rd (z u : ℕ) : Prop := u = dv z ∨ (u = full ∧ (z = wa ∨ z = wb))
def ChOk (ch : List ℕ) : Prop := ch.Nodup ∧ ∀ z ∈ ch, z = wa ∨ z = wb
variable {dv full wa wb}

theorem rdO_ok {vv : ℕ} {ch : List ℕ} {u v : ℕ} {k : ℕ → List ℕ → Bool} (hc : ChOk wa wb ch)
    (he : vv = dv u) (hr : Rd dv full wa wb u v) (h : rdO full vv ch u k = true) :
    ∃ ch', ChOk wa wb ch' ∧ k v ch' = true := by
  unfold rdO at h
  obtain ⟨h1, h2⟩ := cnd h
  rcases hr with rfl | ⟨rfl, hu⟩
  · exact ⟨ch, hc, he ▸ h1⟩
  · by_cases hm : u ∈ ch
    · rw [(mem_iff u ch).2 hm] at h2
      exact ⟨ch, hc, h2⟩
    · rw [mem_f hm] at h2
      have hlen : ch.length < 2 := by
        have : (u :: ch).length ≤ [wa, wb].length := nodup_sub_len (List.nodup_cons.2 ⟨hm, hc.1⟩) (by
          intro z hz
          rcases List.mem_cons.1 hz with rfl | hz
          · simpa using hu
          · simpa using hc.2 z hz)
        simp at this; omega
      rw [lt2_of hlen] at h2
      refine ⟨u :: ch, ⟨List.nodup_cons.2 ⟨hm, hc.1⟩, ?_⟩, h2⟩
      intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · exact hu
      · exact hc.2 z hz

theorem Dc_ok {XS : List ℕ} {env0 : ℕ} (h7 : XS.length = 7) (hlt : ∀ z, dv z < 256) (he0 : env0 < 2 ^ (8 * 7))
    (h0 : ∀ z ∈ XS, gt env0 (px XS z) = dv z) : ∀ (pf : Pf)
    (k : ℕ → List ℕ → Bool), PfV XS pf → (XS ++ wds pf).Nodup →
    (∀ e ∈ pf, ∃ x y, Rd dv full wa wb e.2.1 x ∧ Rd dv full wa wb e.2.2.1 y ∧
      dv e.2.2.2 = cond (Nat.beq e.1 0) (Nat.land x y) (Nat.lor x y)) →
    Dc XS full env0 pf k = true → ∃ env ch, ChOk wa wb ch ∧ env < 2 ^ (8 * ln pf) ∧
      (∀ z, z ∈ XS ∨ z ∈ wds pf → gt env (ps XS z pf) = dv z) ∧ k env ch = true := by
  intro pf
  induction pf with
  | nil =>
    intro k _ _ _ h
    exact ⟨env0, [], ⟨List.nodup_nil, by simp⟩, he0, by intro z hz; rcases hz with hz | hz; exact h0 z hz; simp [wds] at hz, h⟩
  | cons e t ih =>
    intro k hv hn hg h
    obtain ⟨hv1, hv2, hv3⟩ := hv
    have hn' : (XS ++ wds t).Nodup := by
      have : (XS ++ wds (e :: t)).Perm (e.2.2.2 :: (XS ++ wds t)) := List.perm_middle
      exact (List.nodup_cons.1 (this.nodup_iff.1 hn)).2
    have hw : e.2.2.2 ∉ XS ++ wds t := by
      have : (XS ++ wds (e :: t)).Perm (e.2.2.2 :: (XS ++ wds t)) := List.perm_middle
      exact (List.nodup_cons.1 (this.nodup_iff.1 hn)).1
    have h' : Dc XS full env0 t (dst XS e t full k) = true := h
    obtain ⟨env, ch, hc, hel, henv, hk⟩ := ih _ hv3 hn' (fun e he => hg e (List.mem_cons_of_mem _ he)) h'
    obtain ⟨x, y, hx, hy, hxy⟩ := hg e List.mem_cons_self
    unfold dst at hk
    obtain ⟨ch1, hc1, hk1⟩ := rdO_ok hc (henv _ hv1) hx hk
    obtain ⟨ch2, hc2, hk2⟩ := rdO_ok hc1 (henv _ hv2) hy hk1
    rw [← hxy] at hk2
    refine ⟨_, ch2, hc2, env_lt hel (hlt _), ?_, hk2⟩
    intro z hz
    rw [ps_cons]
    by_cases hzw : e.2.2.2 = z
    · subst hzw; rw [Nat.beq_refl, Bool.cond_true]; exact gt_new hel (hlt _)
    · rw [beqf hzw, Bool.cond_false]
      have hz' : z ∈ XS ∨ z ∈ wds t := by
        rcases hz with hz | hz
        · exact Or.inl hz
        · rcases List.mem_cons.1 hz with rfl | hz
          · exact absurd rfl hzw
          · exact Or.inr hz
      show gt (Nat.lor env (Nat.shiftLeft (dv e.2.2.2) (Nat.mul 8 (ln t)))) (ps XS z t) = _
      rw [gt_old (ps_lt h7 hz')]
      exact henv z hz'

theorem ckD_ok {op l r : ℕ → ℕ} {XS gs L : List ℕ} {pf : Pf} {env0 : ℕ} {tgt F : ℕ} (h7 : XS.length = 7) (hlt : ∀ z, dv z < 256) (he0 : env0 < 2 ^ (8 * 7))
    (hp : PfI op l r XS gs pf L []) (hn : (XS ++ gs).Nodup) (h0 : ∀ z ∈ XS, gt env0 (px XS z) = dv z)
    (hg : ∀ w ∈ gs, ∃ x y, Rd dv full wa wb (l w) x ∧ Rd dv full wa wb (r w) y ∧
      dv w = cond (Nat.beq (op w) 0) (Nat.land x y) (Nat.lor x y))
    (hF : F ∈ XS ++ gs) (hd : dv F = tgt) (h : ckD XS full tgt F env0 pf = true) : False := by
  obtain ⟨h1, h2, h3, _⟩ := hp
  rw [List.append_nil] at h2
  have hn' : (XS ++ wds pf).Nodup := (List.Perm.append_left XS h2).nodup_iff.2 hn
  obtain ⟨env, ch, _, _, henv, hk⟩ := Dc_ok h7 hlt he0 h0 pf _ h3 hn' (by
    intro e he
    have hm : e.2.2.2 ∈ gs := h2.mem_iff.1 (List.mem_map_of_mem he)
    obtain ⟨x, y, hx, hy, hxy⟩ := hg _ hm
    obtain ⟨ho, hlr⟩ := h1 e he
    rw [ho] at hxy
    rcases hlr with q | q
    · exact ⟨x, y, q.1 ▸ hx, q.2 ▸ hy, hxy⟩
    · refine ⟨y, x, q.2 ▸ hy, q.1 ▸ hx, ?_⟩
      rw [hxy]
      cases Nat.beq e.1 0
      · exact Nat.lor_comm _ _
      · exact Nat.land_comm _ _) h
  have : gt env (ps XS F pf) = tgt := by
    rw [henv F ?_, hd]
    rcases List.mem_append.1 hF with q | q
    · exact Or.inl q
    · exact Or.inr (h2.mem_iff.2 q)
  rw [this, Nat.beq_refl] at hk
  exact absurd hk (by simp)
end Dpart

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

-- wires of a circuit (adapted from PEqualNP/MetaComplexity/Helpers/Shannon.lean, Apache-2.0)
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]
theorem wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
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
theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
  rw [ht]; simp [hl]
theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_start gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem gate_val (C : Circuit) (x : List Bool) (a b : List Gate) (g : Gate) (h : C.gates = a ++ g :: b) :
    (C.wires x).getD (x.length + a.length) false = g.op.eval (g.inputs.map fun j =>
      if j < x.length + a.length then (C.wires x).getD j false else false) := by
  have e : C.wires x = wiresFrom b (wiresFrom a x ++ [g.op.eval (g.inputs.map fun i => (wiresFrom a x).getD i false)]) := by
    show wiresFrom C.gates x = _
    rw [h, wiresFrom_append]; rfl
  have la := length_wiresFrom a x
  rw [e, getD_wiresFrom _ _ _ (by simp [la])]
  have : (wiresFrom a x ++ [g.op.eval (g.inputs.map fun i => (wiresFrom a x).getD i false)]).getD (x.length + a.length) false
      = g.op.eval (g.inputs.map fun i => (wiresFrom a x).getD i false) := by
    rw [← la, List.getD_append_right _ _ _ _ (le_refl _)]; simp
  rw [this]
  congr 1
  apply List.map_congr_left
  intro j _
  by_cases hj : j < x.length + a.length
  · have hh := getD_wiresFrom b (wiresFrom a x ++ [g.op.eval (g.inputs.map fun i => (wiresFrom a x).getD i false)]) j
      (by rw [List.length_append, la]; omega)
    rw [if_pos hj, hh, List.getD_append _ _ _ _ (by omega)]
  · rw [if_neg hj, List.getD_eq_default _ _ (by omega)]

theorem wire_in (C : Circuit) (x : List Bool) (j : ℕ) (h : j < x.length) :
    (C.wires x).getD j false = x.getD j false := getD_wiresFrom C.gates x j h
theorem wire_out (C : Circuit) (x : List Bool) (j : ℕ) (h : x.length + C.gates.length ≤ j) :
    (C.wires x).getD j false = false := by
  rw [List.getD_eq_default]
  have := length_wiresFrom C.gates x
  show (wiresFrom C.gates x).length ≤ j
  omega

section Circ
variable (Pl Nl : List ℕ) (K1 np nn T M : ℕ)

def fnw (C : Circuit) (j : ℕ) (x : Fin 7 → Bool) : Bool := (C.wires (List.ofFn x)).getD j false
def Wd (C : Circuit) (j : ℕ) : ℕ := enc Pl Nl K1 np nn T M (fnw C j)
def trip (W : ℕ → ℕ) (g : Gate) : Tr :=
  match g.op, g.inputs with
  | GateOp.and, [p, q] => (0, W p, W q)
  | GateOp.or, [p, q] => (1, W p, W q)
  | GateOp.not, p :: _ => (2, W p, W p)
  | _, _ => (0, 0, 0)

variable {Pl Nl K1 np nn T M}

theorem enc_false : enc Pl Nl K1 np nn T M (fun _ => false) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [enc_bit]; unfold encB
  cases Nat.blt i T <;> simp

theorem land_MM (f : (Fin 7 → Bool) → Bool) : Nat.land (enc Pl Nl K1 np nn T M (fun _ => true)) (enc Pl Nl K1 np nn T M f) =
    enc Pl Nl K1 np nn T M f := by
  rw [← enc_and]; simp
theorem lor_MM (f : (Fin 7 → Bool) → Bool) : Nat.lor (enc Pl Nl K1 np nn T M (fun _ => true)) (enc Pl Nl K1 np nn T M f) =
    enc Pl Nl K1 np nn T M (fun _ => true) := by
  rw [← enc_or]; simp

-- form of a gate whose word is new
theorem gate_form {MM : ℕ} (hMM : enc Pl Nl K1 np nn T M (fun _ => true) = MM) {A : List ℕ} (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) (hlen : g.inputs.length ≤ 2)
    (wf : ℕ → (Fin 7 → Bool) → Bool) (w : ℕ → ℕ) (hw : ∀ j, enc Pl Nl K1 np nn T M (wf j) = w j)
    (hin : ∀ j, w j = 0 ∨ w j = MM ∨ w j ∈ A) (v : ℕ)
    (hv : v = enc Pl Nl K1 np nn T M (fun x => g.op.eval (g.inputs.map fun j => wf j x)))
    (hnew : v ≠ 0 ∧ v ≠ MM ∧ v ∉ A) :
    (∃ p q, g.inputs = [p, q] ∧ w p ∈ A ∧ w q ∈ A ∧ ((g.op = GateOp.and ∧ v = Nat.land (w p) (w q)) ∨
      (g.op = GateOp.or ∧ v = Nat.lor (w p) (w q)))) ∨
    (∃ p t, g.inputs = p :: t ∧ w p ∈ A ∧ g.op = GateOp.not ∧ v = Nat.xor (w p) MM) := by
  obtain ⟨n0, n1, n2⟩ := hnew
  have copy : ∀ j, v ≠ w j := by
    intro j h
    rcases hin j with q | q | q
    · exact n0 (h.trans q)
    · exact n1 (h.trans q)
    · exact n2 (h ▸ q)
  rcases hop with h | h | h
  · rw [h] at hv
    rcases hi : g.inputs with _ | ⟨p, _ | ⟨q, _ | ⟨s, t⟩⟩⟩
    · rw [hi] at hv; exact absurd (hv.trans hMM) n1
    · rw [hi] at hv
      refine absurd (hv.trans ?_) (copy p)
      rw [← hw p]; exact enc_congr _ _ _ _ _ _ _ (fun x => by simp [GateOp.eval])
    · rw [hi] at hv
      have hv' : v = Nat.land (w p) (w q) := by
        rw [hv, ← hw p, ← hw q, ← enc_and]; exact enc_congr _ _ _ _ _ _ _ (fun x => by simp [GateOp.eval])
      left
      refine ⟨p, q, rfl, ?_, ?_, Or.inl ⟨h, hv'⟩⟩
      · rcases hin p with z | z | z
        · rw [z] at hv'; exact absurd (hv'.trans (Nat.zero_and _)) n0
        · rw [z, ← hw q, ← hMM, land_MM, hw q] at hv'; exact absurd hv' (copy q)
        · exact z
      · rcases hin q with z | z | z
        · rw [z] at hv'; exact absurd (hv'.trans (Nat.and_zero _)) n0
        · rw [z, ← hw p, ← hMM, show ∀ x y, Nat.land x y = Nat.land y x from Nat.land_comm, land_MM, hw p] at hv'; exact absurd hv' (copy p)
        · exact z
    · rw [hi] at hlen; simp at hlen
  · rw [h] at hv
    rcases hi : g.inputs with _ | ⟨p, _ | ⟨q, _ | ⟨s, t⟩⟩⟩
    · rw [hi] at hv; exact absurd (hv.trans enc_false) n0
    · rw [hi] at hv
      refine absurd (hv.trans ?_) (copy p)
      rw [← hw p]; exact enc_congr _ _ _ _ _ _ _ (fun x => by simp [GateOp.eval])
    · rw [hi] at hv
      have hv' : v = Nat.lor (w p) (w q) := by
        rw [hv, ← hw p, ← hw q, ← enc_or]; exact enc_congr _ _ _ _ _ _ _ (fun x => by simp [GateOp.eval])
      left
      refine ⟨p, q, rfl, ?_, ?_, Or.inr ⟨h, hv'⟩⟩
      · rcases hin p with z | z | z
        · rw [z] at hv'; exact absurd (hv'.trans (Nat.zero_or _)) (copy q)
        · rw [z, ← hw q, ← hMM, lor_MM, hMM] at hv'; exact absurd hv' n1
        · exact z
      · rcases hin q with z | z | z
        · rw [z] at hv'; exact absurd (hv'.trans (Nat.or_zero _)) (copy p)
        · rw [z, ← hw p, ← hMM, show ∀ x y, Nat.lor x y = Nat.lor y x from Nat.lor_comm, lor_MM, hMM] at hv'; exact absurd hv' n1
        · exact z
    · rw [hi] at hlen; simp at hlen
  · have h : g.op = GateOp.not := h
    rw [h] at hv
    rcases hi : g.inputs with _ | ⟨p, t⟩
    · rw [hi] at hv
      refine absurd (hv.trans ?_) n1
      rw [← hMM]; exact enc_congr _ _ _ _ _ _ _ (fun x => by simp [GateOp.eval])
    · rw [hi] at hv
      have hv' : v = Nat.xor (w p) MM := by
        rw [hv, ← hw p, ← hMM, ← enc_not]; exact enc_congr _ _ _ _ _ _ _ (fun x => by simp [GateOp.eval])
      right
      refine ⟨p, t, rfl, ?_, h, hv'⟩
      rcases hin p with z | z | z
      · rw [z] at hv'; exact absurd (hv'.trans (Nat.zero_xor _)) n1
      · rw [z] at hv'; exact absurd (hv'.trans (Nat.xor_self _)) n0
      · exact z

variable {MM q : ℕ} {X : List ℕ} {C : Circuit}

def Cov (MM q : ℕ) (X : List ℕ) (W : ℕ → ℕ) (m i : ℕ) : Prop :=
  ∃ ts : List Tr, WRun MM q X ts ∧ ts.length ≤ m ∧ ∀ j < 7 + i, W j = 0 ∨ W j = MM ∨ W j ∈ X ++ ts.map (outW MM)

def Pos (C : Circuit) (a : List Gate) (g : Gate) (b : List Gate) : Prop := C.gates = a ++ g :: b

theorem word_gate (hMM : enc Pl Nl K1 np nn T M (fun _ => true) = MM)
    {a b : List Gate} {g : Gate} (h : C.gates = a ++ g :: b) :
    Wd Pl Nl K1 np nn T M C (7 + a.length) = enc Pl Nl K1 np nn T M (fun x => g.op.eval (g.inputs.map fun j =>
      (fun j x => if j < 7 + a.length then fnw C j x else false) j x)) := by
  unfold Wd
  apply enc_congr
  intro x
  have := gate_val C (List.ofFn x) a b g h
  rw [List.length_ofFn] at this
  exact this

theorem word_low (j m : ℕ) : enc Pl Nl K1 np nn T M ((fun j x => if j < m then fnw C j x else false) j) =
    if j < m then Wd Pl Nl K1 np nn T M C j else 0 := by
  by_cases h : j < m
  · rw [if_pos h]; exact enc_congr _ _ _ _ _ _ _ (fun x => if_pos h)
  · rw [if_neg h, ← enc_false (Pl := Pl) (Nl := Nl) (K1 := K1) (np := np) (nn := nn) (T := T) (M := M)]
    exact enc_congr _ _ _ _ _ _ _ (fun x => if_neg h)

theorem cov_step (hMM : enc Pl Nl K1 np nn T M (fun _ => true) = MM)
    (hok : FanInTwo C) (hq : ∀ g ∈ C.gates, g.op = GateOp.not → 2 ≤ q) (hq1 : 1 ≤ q)
    {a b : List Gate} {g : Gate} (h : C.gates = a ++ g :: b) {m : ℕ}
    (hc : Cov MM q X (Wd Pl Nl K1 np nn T M C) m a.length) :
    Cov MM q X (Wd Pl Nl K1 np nn T M C) (m + 1) (a.length + 1) := by
  obtain ⟨ts, hr, hl, hW⟩ := hc
  have hg : g ∈ C.gates := by rw [h]; simp
  by_cases hnew : Wd Pl Nl K1 np nn T M C (7 + a.length) = 0 ∨ Wd Pl Nl K1 np nn T M C (7 + a.length) = MM ∨
      Wd Pl Nl K1 np nn T M C (7 + a.length) ∈ X ++ ts.map (outW MM)
  · refine ⟨ts, hr, by omega, ?_⟩
    intro j hj
    by_cases e : j = 7 + a.length
    · rw [e]; exact hnew
    · exact hW j (by omega)
  · push Not at hnew
    have key : ∃ t : Tr, t.1 ≤ q ∧ t.2.1 ∈ X ++ ts.map (outW MM) ∧ t.2.2 ∈ X ++ ts.map (outW MM) ∧ (2 ≤ t.1 → t.2.2 = t.2.1) ∧
        outW MM t = Wd Pl Nl K1 np nn T M C (7 + a.length) := by
      rcases gate_form hMM (A := X ++ ts.map (outW MM)) g (hok g hg).1 (hok g hg).2 _ _ (fun j => word_low j (7 + a.length)) (by
        intro j
        by_cases hj : j < 7 + a.length
        · rw [if_pos hj]; exact hW j hj
        · rw [if_neg hj]; exact Or.inl rfl) _ (word_gate hMM h) hnew with ⟨p, p', _, h1, h2, h3⟩ | ⟨p, t, _, h1, h2, h3⟩
      · rcases h3 with ⟨_, h3⟩ | ⟨_, h3⟩
        · exact ⟨(0, _, _), by simp, h1, h2, by simp, by rw [h3]; rfl⟩
        · exact ⟨(1, _, _), hq1, h1, h2, by simp, by rw [h3]; rfl⟩
      · exact ⟨(2, _, _), hq g hg h2, h1, h1, by simp, by rw [h3]; rfl⟩
    obtain ⟨t, t1, t2, t3, t4, t5⟩ := key
    refine ⟨ts ++ [t], hr.join ⟨t1, t2, t3, t4, trivial⟩, by simp; omega, ?_⟩
    intro j hj
    by_cases e : j = 7 + a.length
    · rw [e, ← t5]; simp
    · rcases hW j (by omega) with q | q | q
      · exact Or.inl q
      · exact Or.inr (Or.inl q)
      · refine Or.inr (Or.inr ?_)
        simp only [List.map_append, List.mem_append] at q ⊢
        tauto

theorem cov_all (hMM : enc Pl Nl K1 np nn T M (fun _ => true) = MM)
    (hok : FanInTwo C) (hq : ∀ g ∈ C.gates, g.op = GateOp.not → 2 ≤ q) (hq1 : 1 ≤ q) : ∀ (b a c : List Gate),
    C.gates = a ++ (b ++ c) → ∀ m, Cov MM q X (Wd Pl Nl K1 np nn T M C) m a.length →
    Cov MM q X (Wd Pl Nl K1 np nn T M C) (m + b.length) (a.length + b.length) := by
  intro b
  induction b with
  | nil => intro a c _ m h; exact h
  | cons g b ih =>
    intro a c h m hc
    have hh : C.gates = a ++ g :: (b ++ c) := h
    have := ih (a ++ [g]) c (hh.trans (by simp)) (m + 1) (by
      rw [List.length_append]; exact cov_step hMM hok hq hq1 hh hc)
    rw [List.length_append] at this
    rw [List.length_cons, show m + (b.length + 1) = m + 1 + b.length by omega,
      show a.length + (b.length + 1) = a.length + [g].length + b.length by simp; omega]
    exact this

theorem wd_high {j : ℕ} (h : 7 + C.gates.length ≤ j) : Wd Pl Nl K1 np nn T M C j = 0 := by
  rw [← enc_false (Pl := Pl) (Nl := Nl) (K1 := K1) (np := np) (nn := nn) (T := T) (M := M)]
  unfold Wd
  apply enc_congr
  intro x
  exact wire_out C _ j (by rw [List.length_ofFn]; exact h)

theorem cov_final (hok : FanInTwo C) (hM0 : M ≠ 0) (hMM' : M ≠ MM)
    (hF : Wd Pl Nl K1 np nn T M C C.output = M) {m : ℕ}
    (hc : Cov MM q X (Wd Pl Nl K1 np nn T M C) m C.gates.length) : ∃ m' ≤ m, Rch MM q M X m' := by
  obtain ⟨ts, hr, hl, hW⟩ := hc
  refine ⟨ts.length, hl, ts, hr, rfl, ?_⟩
  by_cases ho : C.output < 7 + C.gates.length
  · have := hW _ ho
    rw [hF] at this
    rcases this with h | h | h
    · exact absurd h hM0
    · exact absurd h hMM'
    · exact h
  · rw [wd_high (by omega)] at hF
    exact absurd hF.symm hM0

theorem cov_zero (hX : ∀ j < 7, Wd Pl Nl K1 np nn T M C j ∈ X) : Cov MM q X (Wd Pl Nl K1 np nn T M C) 0 0 :=
  ⟨[], trivial, by simp, fun j hj => Or.inr (Or.inr (by simpa using hX j (by simpa using hj)))⟩

-- a circuit of least size has only new words
theorem all_new (hMM : enc Pl Nl K1 np nn T M (fun _ => true) = MM)
    (hok : FanInTwo C) (hq : ∀ g ∈ C.gates, g.op = GateOp.not → 2 ≤ q) (hq1 : 1 ≤ q)
    (hX : ∀ j < 7, Wd Pl Nl K1 np nn T M C j ∈ X) (hM0 : M ≠ 0) (hMM' : M ≠ MM)
    (hF : Wd Pl Nl K1 np nn T M C C.output = M)
    (hl : ∀ m < C.gates.length, ¬ Rch MM q M X m)
    {a b : List Gate} {g : Gate} (h : C.gates = a ++ g :: b) :
    Wd Pl Nl K1 np nn T M C (7 + a.length) ≠ 0 ∧ Wd Pl Nl K1 np nn T M C (7 + a.length) ≠ MM ∧
    ∀ j < 7 + a.length, Wd Pl Nl K1 np nn T M C j ≠ Wd Pl Nl K1 np nn T M C (7 + a.length) := by
  by_contra hcon
  have c1 := cov_all hMM hok hq hq1 a [] (g :: b) (by simpa using h) 0 (cov_zero (MM := MM) (q := q) hX)
  simp only [List.length_nil, Nat.zero_add] at c1
  have c2 : Cov MM q X (Wd Pl Nl K1 np nn T M C) a.length (a ++ [g]).length := by
    obtain ⟨ts, hr, hlen, hW⟩ := c1
    refine ⟨ts, hr, hlen, ?_⟩
    intro j hj
    rw [List.length_append, List.length_singleton] at hj
    by_cases e : j = 7 + a.length
    · rw [e]
      by_contra hno
      push Not at hno
      apply hcon
      refine ⟨hno.1, hno.2.1, ?_⟩
      intro j hj heq
      rcases hW j hj with q | q | q
      · exact hno.1 (heq ▸ q)
      · exact hno.2.1 (heq ▸ q)
      · exact hno.2.2 (heq ▸ q)
    · exact hW j (by omega)
  have c3 := cov_all hMM hok hq hq1 b (a ++ [g]) [] (by rw [h]; simp) a.length c2
  have e : (a ++ [g]).length + b.length = C.gates.length := by rw [h]; simp; omega
  rw [e] at c3
  obtain ⟨m', hm', hR⟩ := cov_final hok hM0 hMM' hF c3
  refine hl m' ?_ hR
  rw [h]; simp; omega

theorem shape (hMM : enc Pl Nl K1 np nn T M (fun _ => true) = MM)
    (hok : FanInTwo C) (hq : ∀ g ∈ C.gates, g.op = GateOp.not → 2 ≤ q) (hq1 : 1 ≤ q)
    (hX : ∀ j < 7, Wd Pl Nl K1 np nn T M C j ∈ X) (hX0 : ∀ z ∈ X, z ≠ 0) (hM0 : M ≠ 0) (hMM' : M ≠ MM)
    (hF : Wd Pl Nl K1 np nn T M C C.output = M)
    (hl : ∀ m < C.gates.length, ¬ Rch MM q M X m)
    {a b : List Gate} {g : Gate} (h : C.gates = a ++ g :: b) :
    (∃ p p', g.inputs = [p, p'] ∧ p < 7 + a.length ∧ p' < 7 + a.length ∧
      ((g.op = GateOp.and ∧ Wd Pl Nl K1 np nn T M C (7 + a.length) = Nat.land (Wd Pl Nl K1 np nn T M C p) (Wd Pl Nl K1 np nn T M C p')) ∨
      (g.op = GateOp.or ∧ Wd Pl Nl K1 np nn T M C (7 + a.length) = Nat.lor (Wd Pl Nl K1 np nn T M C p) (Wd Pl Nl K1 np nn T M C p')))) ∨
    (∃ p t, g.inputs = p :: t ∧ p < 7 + a.length ∧ g.op = GateOp.not ∧
      Wd Pl Nl K1 np nn T M C (7 + a.length) = Nat.xor (Wd Pl Nl K1 np nn T M C p) MM) := by
  have hg : g ∈ C.gates := by rw [h]; simp
  obtain ⟨n0, n1, n2⟩ := all_new hMM hok hq hq1 hX hM0 hMM' hF hl h
  have nz : ∀ j < 7 + a.length, Wd Pl Nl K1 np nn T M C j ≠ 0 := by
    intro j hj
    by_cases h7 : j < 7
    · exact hX0 _ (hX j h7)
    · have hi : j - 7 < C.gates.length := by rw [h]; simp; omega
      have e : C.gates = C.gates.take (j - 7) ++ C.gates[j - 7] :: C.gates.drop (j - 7 + 1) := by simp
      have := (all_new hMM hok hq hq1 hX hM0 hMM' hF hl e).1
      rw [List.length_take, min_eq_left (by omega), show 7 + (j - 7) = j by omega] at this
      exact this
  have inA : ∀ p, (if p < 7 + a.length then Wd Pl Nl K1 np nn T M C p else 0) ∈
      (List.range (7 + a.length)).map (Wd Pl Nl K1 np nn T M C) → p < 7 + a.length := by
    intro p hp
    by_contra hn
    rw [if_neg hn] at hp
    obtain ⟨j, hj, hj2⟩ := List.mem_map.1 hp
    exact nz j (List.mem_range.1 hj) hj2
  rcases gate_form hMM (A := (List.range (7 + a.length)).map (Wd Pl Nl K1 np nn T M C)) g (hok g hg).1 (hok g hg).2 _ _
    (fun j => word_low j (7 + a.length)) (by
      intro j
      by_cases hj : j < 7 + a.length
      · rw [if_pos hj]; exact Or.inr (Or.inr (List.mem_map_of_mem (List.mem_range.2 hj)))
      · rw [if_neg hj]; exact Or.inl rfl) _ (word_gate hMM h) ⟨n0, n1, by
        intro hm
        obtain ⟨j, hj, hj2⟩ := List.mem_map.1 hm
        exact n2 j (List.mem_range.1 hj) hj2⟩ with ⟨p, p', e, h1, h2, h3⟩ | ⟨p, t, e, h1, h2, h3⟩
  · left
    refine ⟨p, p', e, inA p h1, inA p' h2, ?_⟩
    rw [if_pos (inA p h1), if_pos (inA p' h2)] at h3
    exact h3
  · right
    refine ⟨p, t, e, inA p h1, h2, ?_⟩
    rw [if_pos (inA p h1)] at h3
    exact h3

theorem trip_out (hMM : enc Pl Nl K1 np nn T M (fun _ => true) = MM)
    (hok : FanInTwo C) (hq : ∀ g ∈ C.gates, g.op = GateOp.not → 2 ≤ q) (hq1 : 1 ≤ q)
    (hX : ∀ j < 7, Wd Pl Nl K1 np nn T M C j ∈ X) (hX0 : ∀ z ∈ X, z ≠ 0) (hM0 : M ≠ 0) (hMM' : M ≠ MM)
    (hF : Wd Pl Nl K1 np nn T M C C.output = M)
    (hl : ∀ m < C.gates.length, ¬ Rch MM q M X m)
    {a b : List Gate} {g : Gate} (h : C.gates = a ++ g :: b) :
    outW MM (trip (Wd Pl Nl K1 np nn T M C) g) = Wd Pl Nl K1 np nn T M C (7 + a.length) := by
  rcases shape hMM hok hq hq1 hX hX0 hM0 hMM' hF hl h with ⟨p, p', e, _, _, ⟨o, w⟩ | ⟨o, w⟩⟩ | ⟨p, t, e, _, o, w⟩
  · rw [w]; unfold trip; rw [o, e]; rfl
  · rw [w]; unfold trip; rw [o, e]; rfl
  · rw [w]; unfold trip; rw [o, e]; rfl

theorem exact_run (hMM : enc Pl Nl K1 np nn T M (fun _ => true) = MM)
    (hok : FanInTwo C) (hq : ∀ g ∈ C.gates, g.op = GateOp.not → 2 ≤ q) (hq1 : 1 ≤ q)
    (hX : ∀ j < 7, Wd Pl Nl K1 np nn T M C j ∈ X) (hX0 : ∀ z ∈ X, z ≠ 0) (hM0 : M ≠ 0) (hMM' : M ≠ MM)
    (hF : Wd Pl Nl K1 np nn T M C C.output = M)
    (hl : ∀ m < C.gates.length, ¬ Rch MM q M X m) : ∀ (b a : List Gate), C.gates = a ++ b →
    WRun MM q ((List.range (7 + a.length)).map (Wd Pl Nl K1 np nn T M C)) (b.map (trip (Wd Pl Nl K1 np nn T M C))) ∧
    (b.map (trip (Wd Pl Nl K1 np nn T M C))).map (outW MM) =
      (List.range b.length).map (fun i => Wd Pl Nl K1 np nn T M C (7 + a.length + i)) := by
  intro b
  induction b with
  | nil => intro a _; exact ⟨trivial, rfl⟩
  | cons g b ih =>
    intro a h
    obtain ⟨i1, i2⟩ := ih (a ++ [g]) (by rw [h]; simp)
    have ho := trip_out hMM hok hq hq1 hX hX0 hM0 hMM' hF hl h
    have memr : ∀ p, p < 7 + a.length → Wd Pl Nl K1 np nn T M C p ∈ (List.range (7 + a.length)).map (Wd Pl Nl K1 np nn T M C) :=
      fun p hp => List.mem_map_of_mem (List.mem_range.2 hp)
    have hg : g ∈ C.gates := by rw [h]; simp
    constructor
    · rw [List.map_cons]
      have hs : (trip (Wd Pl Nl K1 np nn T M C) g).1 ≤ q ∧
          (trip (Wd Pl Nl K1 np nn T M C) g).2.1 ∈ (List.range (7 + a.length)).map (Wd Pl Nl K1 np nn T M C) ∧
          (trip (Wd Pl Nl K1 np nn T M C) g).2.2 ∈ (List.range (7 + a.length)).map (Wd Pl Nl K1 np nn T M C) ∧
          (2 ≤ (trip (Wd Pl Nl K1 np nn T M C) g).1 → (trip (Wd Pl Nl K1 np nn T M C) g).2.2 = (trip (Wd Pl Nl K1 np nn T M C) g).2.1) := by
        rcases shape hMM hok hq hq1 hX hX0 hM0 hMM' hF hl h with ⟨p, p', e, l1, l2, ⟨o, w⟩ | ⟨o, w⟩⟩ | ⟨p, t, e, l1, o, w⟩
        · unfold trip; rw [o, e]; exact ⟨Nat.zero_le _, memr p l1, memr p' l2, by simp⟩
        · unfold trip; rw [o, e]; exact ⟨hq1, memr p l1, memr p' l2, by simp⟩
        · unfold trip; rw [o, e]; exact ⟨hq g hg o, memr p l1, memr p l1, by simp⟩
      refine ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2, i1.mono ?_⟩
      intro z hz
      rw [List.length_append, List.length_singleton, ← Nat.add_assoc, List.range_succ, List.map_append] at hz
      rw [ho]
      simp only [List.map_cons, List.map_nil, List.mem_append, List.mem_singleton] at hz
      rcases hz with hz | hz
      · exact List.mem_cons_of_mem _ hz
      · rw [hz]; exact List.mem_cons_self
    · rw [List.map_cons, List.map_cons, i2, ho, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      simp only [List.length_append, List.length_singleton, Function.comp_apply]
      congr 1; omega

end Circ

def ff : (Fin 7 → Bool) → Bool := fun x1 => [(1 : ℕ), (12 : ℕ), (4 : ℕ), (15 : ℕ), (26 : ℕ), (35 : ℕ), (46 : ℕ), (36 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (7 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (7 : ℕ) (x2 % (10 : ℕ)))

section Final
variable {Pl Nl : List ℕ} {K1 np nn T M G P MM Xt : ℕ} {X : List ℕ}

-- no run shorter than eleven
theorem noRch (hM : M < 2 ^ T) {p0 : ℕ} (h0 : M.testBit p0 = true)
    (hMM : enc Pl Nl K1 np nn T M (fun _ => true) = MM)
    (hX : X.Nodup) (hX7 : X.length = 7) (hXe : ∀ z ∈ X, IsEnc Pl Nl K1 np nn T M z) {q : ℕ} (hq : q ≤ 2)
    {kk : ℕ} (hkk : kk = 0 → q ≤ 1) (hdep : depChk T M kk X = true)
    (hC : CtxC M G P (xr Pl K1 np nn) (yr Nl K1 np nn))
    (hs : ∀ n k, n < 11 → (k = 0 ∨ 2 ≤ q) → 7 + k ≤ n + 1 →
      nh T M G P (Sr T M G P MM Xt (fun _ => false) n) k 99 (n + 1 - 7 - k) [] [] X = true) :
    ∀ m, m < 11 → ¬ Rch MM q M X m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm ⟨ts, hr, hn, hF⟩
    have hl : ∀ m' < m, ¬ Rch MM q M X m' := fun m' h => ih m' h (by omega)
    have H := run_inv (Xt := Xt) (b := 99) hM h0 hMM hX hXe hq hkk hdep hl hr hn hF (by
      refine le_trans List.countP_le_length ?_
      rw [List.length_map]; omega)
    have hrest : (ts.map (outW MM)).length = m := by rw [List.length_map]; exact hn
    have hsz := Inv.size m hrest H
    rw [hrest, hX7] at hsz
    have hFc : CtxF (vl Pl Nl K1 np nn T M p0) M M (xr Pl K1 np nn) (yr Nl K1 np nn) := by
      intro p hp
      have hsem := H.2.2.1 M hF
      obtain ⟨a, b⟩ := hsem p hp
      rw [← a, ← b]
      exact ⟨hp, Nat.testBit_lt_two_pow (lt_of_lt_of_le hM (Nat.pow_le_pow_right (by omega) (by omega)))⟩
    have hk : cN (fun w => (tro MM ts w).1) (ts.map (outW MM)) = 0 ∨ 2 ≤ q := by
      by_contra hcon
      push Not at hcon
      apply hcon.1
      unfold cN
      rw [List.countP_eq_zero]
      intro w hw
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hw
      have hnd := least_nodup hX hl hr hn hF
      show ¬ Nat.beq (tro MM ts (outW MM t)).1 2 = true
      rw [tro_eq (List.nodup_append.1 hnd).2.1 ht]
      have := (run_irr hr hnd t ht).2.2.1
      simp only [Nat.beq_eq]
      omega
    exact search_false (ι := Unit) (by intro h; rw [h] at hX7; simp at hX7)
      (Sr_good (ι := Unit) (ck := fun _ _ => false) (fun _ _ _ h => by have := h (); simp at this) hFc hC m) hFc hC H hrest (by omega)
      (fun _ => hs m _ hm hk hsz)

variable {C : Circuit} {q : ℕ}

-- the run of a circuit of least size, as a search state
theorem circ_inv (hM : M < 2 ^ T) {p0 : ℕ} (h0 : M.testBit p0 = true)
    (hMM : enc Pl Nl K1 np nn T M (fun _ => true) = MM)
    (hX : X.Nodup) (hXe : ∀ z ∈ X, IsEnc Pl Nl K1 np nn T M z) (hX0 : ∀ z ∈ X, z ≠ 0) (hq2 : q ≤ 2)
    {kk : ℕ} (hkk : kk = 0 → q ≤ 1) (hdep : depChk T M kk X = true) (hMM' : M ≠ MM)
    (hok : FanInTwo C) (h11 : C.gates.length = 11) (hq : ∀ g ∈ C.gates, g.op = GateOp.not → 2 ≤ q) (hq1 : 1 ≤ q)
    (hW : (List.range 7).map (Wd Pl Nl K1 np nn T M C) = X)
    (hF : Wd Pl Nl K1 np nn T M C C.output = M)
    (hl : ∀ m < 11, ¬ Rch MM q M X m) :
    let W := Wd Pl Nl K1 np nn T M C
    let ts := C.gates.map (trip W)
    WRun MM q X ts ∧ ts.length = 11 ∧ ts.map (outW MM) = (List.range 11).map (fun i => W (7 + i)) ∧
    M ∈ X ++ ts.map (outW MM) ∧ (X ++ ts.map (outW MM)).Nodup ∧ ((List.range 18).map W).Nodup ∧ C.output < 18 ∧
    (∀ (b : ℕ), cO (fun w => (tro MM ts w).1) (fun w => (tro MM ts w).2.1) (fun w => (tro MM ts w).2.2) Xt (ts.map (outW MM)) ≤ b →
      Inv (vl Pl Nl K1 np nn T M p0) (fun w => (tro MM ts w).1) (fun w => (tro MM ts w).2.1) (fun w => (tro MM ts w).2.2)
        M T M MM Xt (xr Pl K1 np nn) (yr Nl K1 np nn) X (ts.map (outW MM)) (cN (fun w => (tro MM ts w).1) (ts.map (outW MM))) b) ∧
    CtxF (vl Pl Nl K1 np nn T M p0) M M (xr Pl K1 np nn) (yr Nl K1 np nn) := by
  intro W ts
  have hM0 : M ≠ 0 := by rintro rfl; simp at h0
  have hX' : ∀ j < 7, W j ∈ X := fun j hj => by rw [← hW]; exact List.mem_map_of_mem (List.mem_range.2 hj)
  have hl' : ∀ m < C.gates.length, ¬ Rch MM q M X m := by rw [h11]; exact hl
  obtain ⟨e1, e2⟩ := exact_run hMM hok hq hq1 hX' hX0 hM0 hMM' hF hl' C.gates [] rfl
  simp only [List.length_nil, Nat.add_zero] at e1 e2
  rw [hW] at e1
  rw [h11] at e2
  have hlen : ts.length = 11 := by rw [List.length_map]; exact h11
  have hsplit : X ++ ts.map (outW MM) = (List.range 18).map W := by
    rw [e2, ← hW, show (18 : ℕ) = 7 + 11 from rfl, List.range_add, List.map_append, List.map_map]
    rfl
  have ho : C.output < 18 := by
    by_contra hcon
    rw [wd_high (by omega)] at hF
    exact hM0 hF.symm
  have hFin : M ∈ X ++ ts.map (outW MM) := by
    rw [hsplit, ← hF]; exact List.mem_map_of_mem (List.mem_range.2 ho)
  have hnd := least_nodup hX hl e1 hlen hFin
  have hI : ∀ (b : ℕ), cO (fun w => (tro MM ts w).1) (fun w => (tro MM ts w).2.1) (fun w => (tro MM ts w).2.2) Xt (ts.map (outW MM)) ≤ b →
      Inv (vl Pl Nl K1 np nn T M p0) (fun w => (tro MM ts w).1) (fun w => (tro MM ts w).2.1) (fun w => (tro MM ts w).2.2)
        M T M MM Xt (xr Pl K1 np nn) (yr Nl K1 np nn) X (ts.map (outW MM)) (cN (fun w => (tro MM ts w).1) (ts.map (outW MM))) b :=
    fun b hb => run_inv hM h0 hMM hX hXe hq2 hkk hdep hl e1 hlen hFin hb
  refine ⟨e1, hlen, e2, hFin, hnd, hsplit ▸ hnd, ho, hI, ?_⟩
  intro p hp
  have hsem := (hI _ (le_refl _)).2.2.1 M hFin
  obtain ⟨a, b⟩ := hsem p hp
  rw [← a, ← b]
  exact ⟨hp, Nat.testBit_lt_two_pow (lt_of_lt_of_le hM (Nat.pow_le_pow_right (by omega) (by omega)))⟩

theorem fnw_in (C : Circuit) (j : Fin 7) (x : Fin 7 → Bool) : fnw C j x = x j := by
  unfold fnw
  rw [wire_in C _ _ (by rw [List.length_ofFn]; exact j.isLt)]
  have : (j : ℕ) < (List.ofFn x).length := by rw [List.length_ofFn]; exact j.isLt
  rw [List.getD_eq_getElem _ _ this, List.getElem_ofFn]

theorem wd_in (C : Circuit) (j : Fin 7) : Wd Pl Nl K1 np nn T M C j = enc Pl Nl K1 np nn T M (fun x => x j) :=
  enc_congr _ _ _ _ _ _ _ (fun x => fnw_in C j x)

theorem wd_inputs (C : Circuit) (h : (List.finRange 7).map (fun j => enc Pl Nl K1 np nn T M (fun x => x j)) = X) :
    (List.range 7).map (Wd Pl Nl K1 np nn T M C) = X := by
  rw [← h]
  rw [show List.range 7 = (List.finRange 7).map Fin.val from by decide, List.map_map]
  apply List.map_congr_left
  intro j _
  exact wd_in C j

theorem isEnc_inputs (h : (List.finRange 7).map (fun j => enc Pl Nl K1 np nn T M (fun x => x j)) = X) :
    ∀ z ∈ X, IsEnc Pl Nl K1 np nn T M z := by
  intro z hz
  rw [← h] at hz
  obtain ⟨j, _, rfl⟩ := List.mem_map.1 hz
  exact ⟨_, rfl⟩

end Final

section Const

def PlA : List ℕ := [3, 6, 17, 34, 40, 68, 72, 80]
def NlA : List ℕ := [13, 26, 28, 37, 52, 66, 97]
def MA : ℕ := 84904113077142180218338557544867266431
def GA : ℕ := 85237070383327051513348746171016839296
def QA : ℕ := 18446744073709551616
def MMA : ℕ := 14445686279606472521039285449801757833320720431059568463047934415961216483199
def XA : List ℕ := [14417472156010154432556996410883984432688714074205913240950831240637421912191, 28159125095315269872493295464132181749577188523913786662059433130144595839, 55105919541120979369820697474152812262528158544557208815939698993168128, 210212400676367373025655954992472816368272477881927594633490071552, 54998501412587835697871210714931978371329330767007670029469953055195136, 14417527154301354619716326909069043409663624996064307017996868550969968820224, 14445631173686521630834013501347209967377888182056771718930560760943327838208]
abbrev xrA : ℕ → Fin 7 → Bool := xr PlA 64 8 7
abbrev yrA : ℕ → Fin 7 → Bool := yr NlA 64 8 7
abbrev layA (h : (Fin 7 → Bool) → Bool) : ℕ := enc PlA NlA 64 8 7 127 MA h
set_option maxRecDepth 100000 in
theorem eMA : layA (fun _ => true) = MMA := by decide +kernel
set_option maxRecDepth 100000 in
theorem eFA : layA ff = MA := by decide +kernel
set_option maxRecDepth 100000 in
theorem eXA : (List.finRange 7).map (fun j => layA (fun x => x j)) = XA := by decide +kernel
set_option maxRecDepth 100000 in
theorem eCA : chkC 64 8 7 127 MA GA = true := by decide +kernel
theorem eLA : MA < 2 ^ 127 := by decide +kernel
theorem eGA : GA < 2 ^ 127 := by decide +kernel
theorem eQA : QA = 2 ^ 64 := by decide +kernel
theorem e0A : MA.testBit 0 = true := by decide +kernel
theorem eDA : XA.Nodup := by decide +kernel
theorem eWA : XA.length = 7 := by decide +kernel
theorem eZA : ∀ z ∈ XA, z ≠ 0 := by decide +kernel
theorem eNA : MA ≠ MMA := by decide +kernel
set_option maxRecDepth 100000 in
theorem eHA : depChk 127 MA 0 XA = true := by decide +kernel
theorem eKA : CtxC MA GA QA xrA yrA := by
  rw [eQA]; exact ctxC_of eCA eGA

def PlB : List ℕ := [3, 6, 17, 34, 40, 68, 72, 80, 11, 21, 22, 41, 44, 49, 50, 56, 67, 69, 74, 82, 98, 100]
def NlB : List ℕ := [13, 26, 28, 37, 52, 66, 97, 5, 9, 10, 18, 20, 33, 36, 48, 65, 96]
def MB : ℕ := 406983254271880875117262964573394121945345224839295586984138265000598091335119852269132205883844193548103455379245501353304124959663940661583480527001959727165258752520256350295766406228964992486513694544321339814928776264773421640843263
def GB : ℕ := 406983351304273211074125193473634417745177031302783045876733049912004110546915312711511373324109211083601855972491954755813160398504927146078061959854831049945966537947763004985371079844254492954033792776953880153539332626520091700363264
def QB : ℕ := 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336
def MMB : ℕ := 331270778006019687843840408661188412953266972544587950823996428196708646572808332248334042151785307666673142379401382209767272334361875732790654177232796889260810584372845807131356557104417313927400229514558218893867578063726525106047004027913540846869560720043795718784680149790210046199699900320652095728440135117462617854875265656181958254528101907992793118617837321224702393357777319871432320634185953506832219874386671152214393420522230895598696974744331178533401264127
def XB : List ℕ := [39490549387391280271079980924959993209588266425375809847917835959968400450199413821228153798879349158771579823905168314803339256473411306867718822324223738699668629454437856276008789923729814935357537631331978245858260169659816184561737865651276604925062769088537921945168395183141648774939223478856613316247209617509376869211448293508414401849059957143468441121415701830145918189219801181462101854310538121852258252769200006070566896470609678714941887730316531073023, 950700508150817133186893746803502049161811800169905768338323767598815027763426593209159045644669913918289045874984498448401354629220831010295809724608668592555388390966466137230548808667829350193792472182365425083493851111089448502309406577545122412451052343706499531653304129863607743693767132529562686769105669630941317980518436398867894083588057386522788312054826009058551776797024328336789707236882123177755220265274275432103935, 561194459967734949621459592479225970149978902814447092962234796594903960801352592696342081455187558180168148706565846128993164835183863546326744281954928616144859164301085011091021053423046142584964325722950226850141806783744034673572148983139875970043927135966739651515366513482251780283794091928430588497317099929601916345554550339381781394425548805168123769782901280508211127735792387880512845776853314880643461642137183248214541491049732265534554112, 113332332152225629471170156813085320743862666922665407559883400422861917424542964519447574820651671983947466788194332422318044611330597647705221440124179323914727917579946897137891049418495669052744393604029441774039660042334348979565444822355870134923625365378417441280257138391444272240418646059186447664607298581896192071508395723878498871615227498920907408660794876080235374981042754550288405070963659675618159929336004608, 4707640336440954240689275375954514282603964974505001394063465692253269976359957687119883036937471276343357459487171609876682355331862099108285717294803678366482671806526009176850353227167755036631130196470509769503259395592822327625913968842927852656048814909614811513547319336278425426073825810159074154655695299952846138072336465525066188670668957463212334412110195280400238558988989245723137466719167570023842048292262821705353063393857064353519352456151040, 331270738515470300452560137648107072890806956416732597025283830141407244720785120209836311158070640622987870215272001802927376752859237461621782886211247238374686006367761050630111992593256118204681339319050128071996192841330238674108859193631127403399880730766479209299980609360625658644107618730084291213652322898286246270871527603902805771377021965453536203842469844941799740681555433678616028663256678759531555117891508555615826476937902936290147078822543741633144291328, 331270778006014980202942773180080403830735414276793566162489281906747796231330115817505577873629850150150946656776095007550891942157228151009177355444192898473166705111003711983129846054675712606224078430380724591754171145610114758453490569807228285438901107391451183684235454448387310284951880490891626089051486956519311351586844850593835164426390857806093507917945525257174290639595614295788711987099374572057505925817350189297819193413372251261223083045627367762151079936]
abbrev xrB : ℕ → Fin 7 → Bool := xr PlB 396 22 17
abbrev yrB : ℕ → Fin 7 → Bool := yr NlB 396 22 17
abbrev layB (h : (Fin 7 → Bool) → Bool) : ℕ := enc PlB NlB 396 22 17 787 MB h
set_option maxRecDepth 100000 in
theorem eMB : layB (fun _ => true) = MMB := by decide +kernel
set_option maxRecDepth 100000 in
theorem eFB : layB ff = MB := by decide +kernel
set_option maxRecDepth 100000 in
theorem eXB : (List.finRange 7).map (fun j => layB (fun x => x j)) = XB := by decide +kernel
set_option maxRecDepth 100000 in
theorem eCB : chkC 396 22 17 787 MB GB = true := by decide +kernel
theorem eLB : MB < 2 ^ 787 := by decide +kernel
theorem eGB : GB < 2 ^ 787 := by decide +kernel
theorem eQB : QB = 2 ^ 396 := by decide +kernel
theorem e0B : MB.testBit 0 = true := by decide +kernel
theorem eDB : XB.Nodup := by decide +kernel
theorem eWB : XB.length = 7 := by decide +kernel
theorem eZB : ∀ z ∈ XB, z ≠ 0 := by decide +kernel
theorem eNB : MB ≠ MMB := by decide +kernel
set_option maxRecDepth 100000 in
theorem eHB : depChk 787 MB 1 XB = true := by decide +kernel
theorem eKB : CtxC MB GB QB xrB yrB := by
  rw [eQB]; exact ctxC_of eCB eGB
end Const
def XtA : ℕ := 55105919541120979369820697474152812262528158544557208815939698993168128
def envA : ℕ := 36099303270254594
def ckA : Pf → Bool := ckD XA 255 6 MA envA
def sA (n : ℕ) : Bool := nh 127 MA GA QA (Sr 127 MA GA QA MMA XtA (fun _ => false) n) 0 99 (n + 1 - 7 - 0) [] [] XA
def sB (n k : ℕ) : Bool := nh 787 MB GB QB (Sr 787 MB GB QB MMB 0 (fun _ => false) n) k 99 (n + 1 - 7 - k) [] [] XB
def cA (h n2 j n3 x n4 y : ℕ) : Bool := srch3 127 MA GA QA MMA XtA ckA XA 23 0 1 5 h n2 j n3 x n4 y
def cB1 (h n2 j n3 x n4 y : ℕ) : Bool := srch3 787 MB GB QB MMB 0 (fun _ => false) XB 23 1 99 4 h n2 j n3 x n4 y
def cB2 (h n2 j n3 x n4 y : ℕ) : Bool := srch3 787 MB GB QB MMB 0 (fun _ => false) XB 23 2 99 3 h n2 j n3 x n4 y
def nA2 (h : ℕ) : ℕ := if h = 3 then 7 else if h = 4 then 7 else if h = 5 then 7 else if h = 6 then 7 else if h = 9 then 7 else if h = 10 then 7 else if h = 12 then 7 else if h = 19 then 7 else if h = 21 then 7 else if h = 18 then 3 else if h = 7 then 2 else 1
def nA3 (h j : ℕ) : ℕ := if h = 4 ∧ j = 1 then 11 else if h = 6 ∧ j = 2 then 11 else if h = 3 ∧ j = 2 then 3 else if h = 5 ∧ j = 2 then 3 else 1
def nA4 (h j x : ℕ) : ℕ := if h = 4 ∧ j = 1 ∧ x = 5 then 2 else if h = 4 ∧ j = 1 ∧ x = 7 then 4 else if h = 6 ∧ j = 2 ∧ x = 10 then 4 else 1
theorem nA2_pos (h : ℕ) : 0 < nA2 h := by
  unfold nA2
  first | exact Nat.one_pos | (split_ifs <;> omega)
theorem nA3_pos (h j : ℕ) : 0 < nA3 h j := by
  unfold nA3
  first | exact Nat.one_pos | (split_ifs <;> omega)
theorem nA4_pos (h j x : ℕ) : 0 < nA4 h j x := by
  unfold nA4
  first | exact Nat.one_pos | (split_ifs <;> omega)
def nB2 (h : ℕ) : ℕ := 1
def nB3 (h j : ℕ) : ℕ := 1
def nB4 (h j x : ℕ) : ℕ := 1
theorem nB2_pos (h : ℕ) : 0 < nB2 h := by
  unfold nB2
  first | exact Nat.one_pos | (split_ifs <;> omega)
theorem nB3_pos (h j : ℕ) : 0 < nB3 h j := by
  unfold nB3
  first | exact Nat.one_pos | (split_ifs <;> omega)
theorem nB4_pos (h j x : ℕ) : 0 < nB4 h j x := by
  unfold nB4
  first | exact Nat.one_pos | (split_ifs <;> omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem smallA (n : ℕ) (h1 : n < 11) (h2 : 7 ≤ n + 1) : sA n = true := by
  have hn : 6 ≤ n := by omega
  interval_cases n
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem smallB (n k : ℕ) (h1 : n < 11) (h2 : 7 + k ≤ n + 1) : sB n k = true := by
  have hk : k < 5 := by omega
  have hn : 6 ≤ n := by omega
  interval_cases n
  · have hk : k < 1 := by omega
    interval_cases k
    · decide +kernel
  · have hk : k < 2 := by omega
    interval_cases k
    · decide +kernel
    · decide +kernel
  · have hk : k < 3 := by omega
    interval_cases k
    · decide +kernel
    · decide +kernel
    · decide +kernel
  · have hk : k < 4 := by omega
    interval_cases k
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
  · have hk : k < 5 := by omega
    interval_cases k
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sB11 (k : ℕ) (h1 : 3 ≤ k) (h2 : k ≤ 5) : sB 11 k = true := by
  interval_cases k
  · decide +kernel
  · decide +kernel
  · decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem arow : ∀ h, h < 23 → ∀ j, j < nA2 h → ∀ x, x < nA3 h j → ∀ y, y < nA4 h j x → cA h (nA2 h) j (nA3 h j) x (nA4 h j x) y = true := by
  intro h hh
  interval_cases h
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 0 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 1 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 2 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 7 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 3 7 0 1 0 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 3 7 1 1 0 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 3 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 3 7 2 3 0 1 0 = true := by decide +kernel
          exact this
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 3 7 2 3 1 1 0 = true := by decide +kernel
          exact this
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 3 7 2 3 2 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 3 7 3 1 0 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 3 7 4 1 0 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 3 7 5 1 0 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 3 7 6 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 7 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 4 7 0 1 0 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 11 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 4 7 1 11 0 1 0 = true := by decide +kernel
          exact this
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 4 7 1 11 1 1 0 = true := by decide +kernel
          exact this
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 4 7 1 11 2 1 0 = true := by decide +kernel
          exact this
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 4 7 1 11 3 1 0 = true := by decide +kernel
          exact this
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 4 7 1 11 4 1 0 = true := by decide +kernel
          exact this
      · intro y hy
        have hy : y < 2 := hy
        interval_cases y
        · have : cA 4 7 1 11 5 2 0 = true := by decide +kernel
          exact this
        · have : cA 4 7 1 11 5 2 1 = true := by decide +kernel
          exact this
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 4 7 1 11 6 1 0 = true := by decide +kernel
          exact this
      · intro y hy
        have hy : y < 4 := hy
        interval_cases y
        · have : cA 4 7 1 11 7 4 0 = true := by decide +kernel
          exact this
        · have : cA 4 7 1 11 7 4 1 = true := by decide +kernel
          exact this
        · have : cA 4 7 1 11 7 4 2 = true := by decide +kernel
          exact this
        · have : cA 4 7 1 11 7 4 3 = true := by decide +kernel
          exact this
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 4 7 1 11 8 1 0 = true := by decide +kernel
          exact this
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 4 7 1 11 9 1 0 = true := by decide +kernel
          exact this
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 4 7 1 11 10 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 4 7 2 1 0 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 4 7 3 1 0 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 4 7 4 1 0 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 4 7 5 1 0 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 4 7 6 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 7 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 5 7 0 1 0 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 5 7 1 1 0 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 3 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 5 7 2 3 0 1 0 = true := by decide +kernel
          exact this
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 5 7 2 3 1 1 0 = true := by decide +kernel
          exact this
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 5 7 2 3 2 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 5 7 3 1 0 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 5 7 4 1 0 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 5 7 5 1 0 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 5 7 6 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 7 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 6 7 0 1 0 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 6 7 1 1 0 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 11 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 6 7 2 11 0 1 0 = true := by decide +kernel
          exact this
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 6 7 2 11 1 1 0 = true := by decide +kernel
          exact this
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 6 7 2 11 2 1 0 = true := by decide +kernel
          exact this
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 6 7 2 11 3 1 0 = true := by decide +kernel
          exact this
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 6 7 2 11 4 1 0 = true := by decide +kernel
          exact this
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 6 7 2 11 5 1 0 = true := by decide +kernel
          exact this
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 6 7 2 11 6 1 0 = true := by decide +kernel
          exact this
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 6 7 2 11 7 1 0 = true := by decide +kernel
          exact this
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 6 7 2 11 8 1 0 = true := by decide +kernel
          exact this
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 6 7 2 11 9 1 0 = true := by decide +kernel
          exact this
      · intro y hy
        have hy : y < 4 := hy
        interval_cases y
        · have : cA 6 7 2 11 10 4 0 = true := by decide +kernel
          exact this
        · have : cA 6 7 2 11 10 4 1 = true := by decide +kernel
          exact this
        · have : cA 6 7 2 11 10 4 2 = true := by decide +kernel
          exact this
        · have : cA 6 7 2 11 10 4 3 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 6 7 3 1 0 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 6 7 4 1 0 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 6 7 5 1 0 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 6 7 6 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 2 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 7 2 0 1 0 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 7 2 1 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 8 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 7 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 9 7 0 1 0 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 9 7 1 1 0 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 9 7 2 1 0 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 9 7 3 1 0 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 9 7 4 1 0 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 9 7 5 1 0 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 9 7 6 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 7 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 10 7 0 1 0 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 10 7 1 1 0 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 10 7 2 1 0 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 10 7 3 1 0 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 10 7 4 1 0 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 10 7 5 1 0 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 10 7 6 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 11 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 7 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 12 7 0 1 0 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 12 7 1 1 0 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 12 7 2 1 0 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 12 7 3 1 0 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 12 7 4 1 0 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 12 7 5 1 0 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 12 7 6 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 13 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 14 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 15 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 16 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 17 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 3 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 18 3 0 1 0 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 18 3 1 1 0 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 18 3 2 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 7 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 19 7 0 1 0 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 19 7 1 1 0 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 19 7 2 1 0 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 19 7 3 1 0 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 19 7 4 1 0 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 19 7 5 1 0 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 19 7 6 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 20 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 7 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 21 7 0 1 0 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 21 7 1 1 0 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 21 7 2 1 0 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 21 7 3 1 0 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 21 7 4 1 0 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 21 7 5 1 0 1 0 = true := by decide +kernel
          exact this
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 21 7 6 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cA 22 1 0 1 0 1 0 = true := by decide +kernel
          exact this
theorem aall : ∀ i : (Σ h : Fin 23, Σ j : Fin (nA2 h), Σ x : Fin (nA3 h j), Fin (nA4 h j x)), cA i.1 (nA2 i.1) i.2.1 (nA3 i.1 i.2.1) i.2.2.1 (nA4 i.1 i.2.1 i.2.2.1) i.2.2.2 = true := by
  rintro ⟨⟨h, hh⟩, ⟨j, hj⟩, ⟨x, hx⟩, ⟨y, hy⟩⟩
  exact arow h hh j hj x hx y hy
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem brow : ∀ h, h < 23 → ∀ j, j < nB2 h → ∀ x, x < nB3 h j → ∀ y, y < nB4 h j x → cB1 h (nB2 h) j (nB3 h j) x (nB4 h j x) y = true := by
  intro h hh
  interval_cases h
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cB1 0 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cB1 1 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cB1 2 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cB1 3 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cB1 4 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cB1 5 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cB1 6 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cB1 7 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cB1 8 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cB1 9 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cB1 10 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cB1 11 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cB1 12 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cB1 13 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cB1 14 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cB1 15 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cB1 16 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cB1 17 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cB1 18 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cB1 19 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cB1 20 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cB1 21 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cB1 22 1 0 1 0 1 0 = true := by decide +kernel
          exact this
theorem ball : ∀ i : (Σ h : Fin 23, Σ j : Fin (nB2 h), Σ x : Fin (nB3 h j), Fin (nB4 h j x)), cB1 i.1 (nB2 i.1) i.2.1 (nB3 i.1 i.2.1) i.2.2.1 (nB4 i.1 i.2.1 i.2.2.1) i.2.2.2 = true := by
  rintro ⟨⟨h, hh⟩, ⟨j, hj⟩, ⟨x, hx⟩, ⟨y, hy⟩⟩
  exact brow h hh j hj x hx y hy
def nC2 (h : ℕ) : ℕ := 1
def nC3 (h j : ℕ) : ℕ := 1
def nC4 (h j x : ℕ) : ℕ := 1
theorem nC2_pos (h : ℕ) : 0 < nC2 h := by
  unfold nC2
  first | exact Nat.one_pos | (split_ifs <;> omega)
theorem nC3_pos (h j : ℕ) : 0 < nC3 h j := by
  unfold nC3
  first | exact Nat.one_pos | (split_ifs <;> omega)
theorem nC4_pos (h j x : ℕ) : 0 < nC4 h j x := by
  unfold nC4
  first | exact Nat.one_pos | (split_ifs <;> omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem erow : ∀ h, h < 23 → ∀ j, j < nC2 h → ∀ x, x < nC3 h j → ∀ y, y < nC4 h j x → cB2 h (nC2 h) j (nC3 h j) x (nC4 h j x) y = true := by
  intro h hh
  interval_cases h
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cB2 0 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cB2 1 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cB2 2 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cB2 3 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cB2 4 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cB2 5 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cB2 6 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cB2 7 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cB2 8 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cB2 9 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cB2 10 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cB2 11 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cB2 12 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cB2 13 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cB2 14 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cB2 15 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cB2 16 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cB2 17 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cB2 18 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cB2 19 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cB2 20 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cB2 21 1 0 1 0 1 0 = true := by decide +kernel
          exact this
  · intro j hj
    have hj : j < 1 := hj
    interval_cases j
    · intro x hx
      have hx : x < 1 := hx
      interval_cases x
      · intro y hy
        have hy : y < 1 := hy
        interval_cases y
        · have : cB2 22 1 0 1 0 1 0 = true := by decide +kernel
          exact this
theorem eall : ∀ i : (Σ h : Fin 23, Σ j : Fin (nC2 h), Σ x : Fin (nC3 h j), Fin (nC4 h j x)), cB2 i.1 (nC2 i.1) i.2.1 (nC3 i.1 i.2.1) i.2.2.1 (nC4 i.1 i.2.1 i.2.2.1) i.2.2.2 = true := by
  rintro ⟨⟨h, hh⟩, ⟨j, hj⟩, ⟨x, hx⟩, ⟨y, hy⟩⟩
  exact erow h hh j hj x hx y hy

theorem neA : XA ≠ [] := by decide +kernel
theorem neB : XB ≠ [] := by decide +kernel
section Big
variable {val : ℕ → (Fin 7 → Bool) → Bool} {op l r : ℕ → ℕ} {rest : List ℕ}
set_option maxRecDepth 100000 in
theorem bigA (hFc : CtxF val MA MA xrA yrA) (H : Inv val op l r MA 127 MA MMA XtA xrA yrA XA rest 0 1) (hn : rest.length = 11)
    (hck : ∀ pf L, PfI op l r XA rest pf L [] → ckA pf = true → False) : False :=
  search_false (sl := 5) neA (s3_good hck hFc eKA (N1 := 23) (by omega) nA2 nA2_pos nA3 nA3_pos nA4 nA4_pos) hFc eKA H hn (by rw [eWA]) aall
set_option maxRecDepth 100000 in
theorem bigB {k : ℕ} (hFc : CtxF val MB MB xrB yrB) (H : Inv val op l r MB 787 MB MMB 0 xrB yrB XB rest k 99) (hn : rest.length = 11)
    (hk : k ≠ 0) (hs : 7 + k ≤ 12) : False := by
  have hu : ∀ k', k' = k → sB 11 k' = true → False := fun k' e h => by
    subst e
    exact search_false (ι := Unit) neB (Sr_good (ι := Unit) (ck := fun _ _ => false)
      (fun _ _ _ h => by have := h (); simp at this) hFc eKB 11) hFc eKB H hn (by rw [eWB]; omega) (fun _ => h)
  have hk5 : k < 6 := by omega
  interval_cases k
  · exact hk rfl
  · exact search_false (sl := 4) neB (s3_good (ck := fun _ => false) (fun _ _ _ h => by simp at h) hFc eKB (N1 := 23) (by omega) nB2 nB2_pos nB3 nB3_pos nB4 nB4_pos) hFc eKB H hn (by rw [eWB]) ball
  · exact search_false (sl := 3) neB (s3_good (ck := fun _ => false) (fun _ _ _ h => by simp at h) hFc eKB (N1 := 23) (by omega) nC2 nC2_pos nC3 nC3_pos nC4 nC4_pos) hFc eKB H hn (by rw [eWB]) eall
  · exact hu 3 rfl (sB11 3 (by omega) (by omega))
  · exact hu 4 rfl (sB11 4 (by omega) (by omega))
  · exact hu 5 rfl (sB11 5 (by omega) (by omega))
end Big
section Assembly
-- rows for the shifted circuit
def R8 : List ℕ := [0, 1, 8, 2, 4, 16, 32, 64]
def dwj (D : Circuit) (j : ℕ) : ℕ :=
  bitsV (fun k => (D.wires (true :: List.ofFn (asg (R8.getD k 0)))).getD j false) 8

theorem bitsV_congr {f g : ℕ → Bool} (n : ℕ) (h : ∀ i < n, f i = g i) : bitsV f n = bitsV g n := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [bitsV_bit, bitsV_bit]
  by_cases hi : i < n
  · rw [h i hi]
  · simp [hi]

theorem bitsV_and (f g : ℕ → Bool) (n : ℕ) : bitsV (fun k => f k && g k) n = Nat.land (bitsV f n) (bitsV g n) := by
  apply Nat.eq_of_testBit_eq
  intro i
  change _ = (bitsV f n &&& bitsV g n).testBit i
  rw [Nat.testBit_and, bitsV_bit, bitsV_bit, bitsV_bit]
  cases decide (i < n) <;> simp

theorem bitsV_or (f g : ℕ → Bool) (n : ℕ) : bitsV (fun k => f k || g k) n = Nat.lor (bitsV f n) (bitsV g n) := by
  apply Nat.eq_of_testBit_eq
  intro i
  change _ = (bitsV f n ||| bitsV g n).testBit i
  rw [Nat.testBit_or, bitsV_bit, bitsV_bit, bitsV_bit]
  cases decide (i < n) <;> simp

theorem dwj_gate {D : Circuit} {a b : List Gate} {g : Gate} (h : D.gates = a ++ g :: b) {s s' : ℕ}
    (hi : g.inputs = [s, s']) (h1 : s < 8 + a.length) (h2 : s' < 8 + a.length) :
    (g.op = GateOp.and → dwj D (8 + a.length) = Nat.land (dwj D s) (dwj D s')) ∧
    (g.op = GateOp.or → dwj D (8 + a.length) = Nat.lor (dwj D s) (dwj D s')) := by
  have key : ∀ k, (D.wires (true :: List.ofFn (asg (R8.getD k 0)))).getD (8 + a.length) false =
      g.op.eval [(D.wires (true :: List.ofFn (asg (R8.getD k 0)))).getD s false,
        (D.wires (true :: List.ofFn (asg (R8.getD k 0)))).getD s' false] := by
    intro k
    have hv := gate_val D (true :: List.ofFn (asg (R8.getD k 0))) a b g h
    have hlen : (true :: List.ofFn (asg (R8.getD k 0))).length = 8 := by simp
    rw [hlen] at hv
    rw [hv, hi]
    simp only [List.map_cons, List.map_nil, if_pos h1, if_pos h2]
  constructor
  · intro ho
    unfold dwj
    rw [← bitsV_and]
    apply bitsV_congr
    intro k _
    rw [key k, ho]; simp [GateOp.eval]
  · intro ho
    unfold dwj
    rw [← bitsV_or]
    apply bitsV_congr
    intro k _
    rw [key k, ho]; simp [GateOp.eval]

theorem dwj_zero (D : Circuit) : dwj D 0 = 255 := by
  unfold dwj
  rw [show (255 : ℕ) = bitsV (fun _ => true) 8 by decide +kernel]
  apply bitsV_congr
  intro k _
  rw [wire_in D _ 0 (by simp)]; rfl

theorem dwj_in (D : Circuit) (j : Fin 7) : dwj D (j + 1) = bitsV (fun k => asg (R8.getD k 0) j) 8 := by
  unfold dwj
  apply bitsV_congr
  intro k _
  rw [wire_in D _ _ (by have := j.isLt; simp; omega)]
  have : (j : ℕ) < (List.ofFn (asg (R8.getD k 0))).length := by rw [List.length_ofFn]; exact j.isLt
  rw [List.getD_cons_succ, List.getD_eq_getElem _ _ this, List.getElem_ofFn]

theorem forall2_split {α β : Type} {R : α → β → Prop} {a b : List α} {g : α} : ∀ {m : List β},
    List.Forall₂ R (a ++ g :: b) m → ∃ a' g' b', m = a' ++ g' :: b' ∧ a'.length = a.length ∧ R g g' := by
  induction a with
  | nil =>
    intro m h
    cases h with
    | cons h1 h2 => exact ⟨[], _, _, rfl, rfl, h1⟩
  | cons x a ih =>
    intro m h
    cases h with
    | cons h1 h2 =>
      obtain ⟨a', g', b', e, l, r⟩ := ih h2
      exact ⟨_ :: a', g', b', by rw [e]; rfl, by simp [l], r⟩

theorem getElem_split {C : Circuit} {i : ℕ} (hi : i < C.gates.length) :
    C.gates = C.gates.take i ++ C.gates[i] :: C.gates.drop (i + 1) ∧ (C.gates.take i).length = i := by
  constructor
  · simp
  · rw [List.length_take, min_eq_left (by omega)]

theorem mem_split {C : Circuit} {g : Gate} (hg : g ∈ C.gates) : ∃ a b, C.gates = a ++ g :: b := List.append_of_mem hg

-- shorter runs do not exist
theorem noRchA : ∀ m, m < 11 → ¬ Rch MMA 1 MA XA m :=
  noRch (Xt := XtA) eLA e0A eMA eDA eWA (isEnc_inputs eXA) (by omega) (kk := 0) (fun _ => le_refl _) eHA eKA
    (by
      intro n k hn hk hs
      have hk0 : k = 0 := by omega
      subst hk0
      exact smallA n (by omega) (by omega))

theorem noRchB : ∀ m, m < 11 → ¬ Rch MMB 2 MB XB m :=
  noRch (Xt := 0) eLB e0B eMB eDB eWB (isEnc_inputs eXB) (le_refl _) (kk := 1) (fun h => absurd h (by omega)) eHB eKB
    (by
      intro n k hn _ hs
      exact smallB n k hn hs)

variable {C : Circuit}

set_option maxRecDepth 100000 in
theorem noNot (hok : FanInTwo C) (h11 : C.gates.length = 11) (hf : ∀ x, fnw C C.output x = ff x) :
    ∀ g ∈ C.gates, g.op ≠ GateOp.not := by
  have hFB : Wd PlB NlB 396 22 17 787 MB C C.output = MB := by
    exact (enc_congr _ _ _ _ _ _ _ hf).trans eFB
  have hWB := wd_inputs C eXB
  have hX' : ∀ j < 7, Wd PlB NlB 396 22 17 787 MB C j ∈ XB := fun j hj => by
    rw [← hWB]; exact List.mem_map_of_mem (List.mem_range.2 hj)
  have hM0 : MB ≠ 0 := by intro h; have := e0B; rw [h] at this; simp at this
  obtain ⟨hr, hlen, hout, hFin, hnd, hnd18, ho, hI, hFc⟩ := circ_inv (Xt := 0) (q := 2) eLB e0B eMB eDB (isEnc_inputs eXB) eZB (le_refl _)
    (kk := 1) (fun h => absurd h (by omega)) eHB eNB hok h11 (fun _ _ _ => le_refl _) (by omega) hWB hFB noRchB
  have H := hI 99 (by
    refine le_trans List.countP_le_length ?_
    rw [List.length_map, hlen]; omega)
  have hrest : ((C.gates.map (trip (Wd PlB NlB 396 22 17 787 MB C))).map (outW MMB)).length = 11 := by rw [List.length_map]; exact hlen
  have hsz := Inv.size 11 hrest H
  rw [hrest, eWB] at hsz
  have hk0 : cN (fun w => (tro MMB (C.gates.map (trip (Wd PlB NlB 396 22 17 787 MB C))) w).1)
      ((C.gates.map (trip (Wd PlB NlB 396 22 17 787 MB C))).map (outW MMB)) = 0 := by
    by_contra hne
    exact bigB hFc H hrest hne (by omega)
  intro g hg hop
  have ht : trip (Wd PlB NlB 396 22 17 787 MB C) g ∈ C.gates.map (trip (Wd PlB NlB 396 22 17 787 MB C)) := List.mem_map_of_mem hg
  unfold cN at hk0
  rw [List.countP_eq_zero] at hk0
  have := hk0 _ (List.mem_map_of_mem (f := outW MMB) ht)
  simp only [tro_eq (List.nodup_append.1 hnd).2.1 ht] at this
  obtain ⟨a, b, hab⟩ := mem_split hg
  rcases shape eMB hok (fun _ _ _ => le_refl 2) (by omega) hX' eZB hM0 eNB hFB (by rw [h11]; exact noRchB) hab with
    ⟨p, p', e, _, _, ⟨o, _⟩ | ⟨o, _⟩⟩ | ⟨p, t, e, _, o, _⟩
  · rw [hop] at o; exact absurd o (by simp)
  · rw [hop] at o; exact absurd o (by simp)
  · unfold trip at this
    rw [o, e] at this
    simp at this

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem main (D : Circuit) (x4 x5 : ℕ) (hok : FanInTwo C) (h11 : C.gates.length = 11) (hf : ∀ x, fnw C C.output x = ff x)
    (hD : List.Forall₂ (fun (x9 x10 : Gate) => x9.op = x10.op ∧ List.Forall₂ (fun (x11 x12 : ℕ) =>
      x12 = x11 + (1 : ℕ) ∨ x12 = (0 : ℕ) ∧ (x11 = x4 ∨ x11 = x5)) x9.inputs x10.inputs) C.gates D.gates)
    (hDv : ∀ x : Fin 7 → Bool, (D.wires (true :: List.ofFn x)).getD (C.output + 1) false = (ff x || x 0 || x 3))
    (hcount : (List.filter (fun (g : Gate) => g.op.eval [true, false] && g.inputs.contains 2) C.gates).length ≤ 1) : False := by
  have hnn := noNot hok h11 hf
  have hq : ∀ g ∈ C.gates, g.op = GateOp.not → 2 ≤ 1 := fun g hg h => absurd h (hnn g hg)
  have hFA : Wd PlA NlA 64 8 7 127 MA C C.output = MA := by
    exact (enc_congr _ _ _ _ _ _ _ hf).trans eFA
  have hWA := wd_inputs C eXA
  have hX' : ∀ j < 7, Wd PlA NlA 64 8 7 127 MA C j ∈ XA := fun j hj => by
    rw [← hWA]; exact List.mem_map_of_mem (List.mem_range.2 hj)
  have hM0 : MA ≠ 0 := by intro h; have := e0A; rw [h] at this; simp at this
  obtain ⟨hr, hlen, hout, hFin, hnd, hnd18, ho, hI, hFc⟩ := circ_inv (Xt := XtA) (q := 1) eLA e0A eMA eDA (isEnc_inputs eXA) eZA (by omega)
    (kk := 0) (fun _ => le_refl _) eHA eNA hok h11 hq (le_refl _) hWA hFA noRchA
  set W := Wd PlA NlA 64 8 7 127 MA C with hWdef
  set ts := C.gates.map (trip W) with htsdef
  have hno : (ts.map (outW MMA)).Nodup := (List.nodup_append.1 hnd).2.1
  have hinj : ∀ i j, i < 18 → j < 18 → W i = W j → i = j := fun i j hi hj h =>
    List.inj_on_of_nodup_map hnd18 (List.mem_range.2 hi) (List.mem_range.2 hj) h
  have hshape := fun {a b : List Gate} {g : Gate} (h : C.gates = a ++ g :: b) =>
    shape eMA hok hq (le_refl 1) hX' eZA hM0 eNA hFA (by rw [h11]; exact noRchA) h
  have htout := fun {a b : List Gate} {g : Gate} (h : C.gates = a ++ g :: b) =>
    trip_out eMA hok hq (le_refl 1) hX' eZA hM0 eNA hFA (by rw [h11]; exact noRchA) h
  have hW2 : W 2 = XtA := by
    have : ((List.range 7).map W)[2]? = XA[2]? := by rw [hWA]
    have h2 : XA[2]? = some XtA := by decide +kernel
    rw [List.getElem?_map, h2] at this
    simpa using this
  -- the number of OR readers of input two
  have hcO : cO (fun w => (tro MMA ts w).1) (fun w => (tro MMA ts w).2.1) (fun w => (tro MMA ts w).2.2) XtA (ts.map (outW MMA)) ≤ 1 := by
    refine le_trans ?_ hcount
    rw [← List.countP_eq_length_filter]
    unfold cO
    rw [htsdef, List.map_map, List.countP_map]
    apply List.countP_mono_left
    intro g hg h
    have ht : trip W g ∈ ts := List.mem_map_of_mem hg
    simp only [Function.comp_apply] at h
    rw [← htsdef, tro_eq hno ht] at h
    obtain ⟨a, b, hab⟩ := mem_split hg
    have hal : a.length < 11 := by rw [← h11, hab]; simp
    rcases hshape hab with ⟨p, p', e, l1, l2, ⟨o, w⟩ | ⟨o, w⟩⟩ | ⟨p, t, e, l1, o, w⟩
    · unfold trip at h; rw [o, e] at h; simp at h
    · unfold trip at h; rw [o, e] at h
      simp only [Nat.beq_refl, Bool.true_and, Bool.or_eq_true, Nat.beq_eq] at h
      rw [o, e]
      rcases h with h | h
      · have := hinj p 2 (by omega) (by omega) (h.trans hW2.symm)
        subst this; simp [GateOp.eval]
      · have := hinj p' 2 (by omega) (by omega) (h.trans hW2.symm)
        subst this; simp [GateOp.eval]
    · exact absurd o (hnn g hg)
  have H := hI 1 hcO
  have hrest : (ts.map (outW MMA)).length = 11 := by rw [List.length_map]; exact hlen
  have hk0 : cN (fun w => (tro MMA ts w).1) (ts.map (outW MMA)) = 0 := by
    unfold cN
    rw [List.countP_eq_zero]
    intro w hw
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hw
    show ¬ Nat.beq (tro MMA ts (outW MMA t)).1 2 = true
    rw [tro_eq hno ht]
    have := (run_irr hr hnd t ht).2.2.1
    simp only [Nat.beq_eq]
    omega
  rw [hk0] at H
  -- values of the shifted circuit
  let dv : ℕ → ℕ := fun w => dwj D (((List.range 18).find? (fun j => Nat.beq (W j) w)).getD 0 + 1)
  have hdv : ∀ j, j < 18 → dv (W j) = dwj D (j + 1) := by
    intro j hj
    show dwj D (((List.range 18).find? (fun i => Nat.beq (W i) (W j))).getD 0 + 1) = _
    cases hfi : (List.range 18).find? (fun i => Nat.beq (W i) (W j)) with
    | none =>
      have := List.find?_eq_none.1 hfi j (List.mem_range.2 hj)
      simp at this
    | some s =>
      have h1 := List.mem_of_find?_eq_some hfi
      have h2 := List.find?_some hfi
      simp only [Nat.beq_eq] at h2
      rw [Option.getD_some, hinj s j (List.mem_range.1 h1) hj h2]
  refine bigA hFc H hrest (fun pf L hp hck => ?_)
  have hlt : ∀ z, dv z < 256 := fun z => bitsV_lt _ 8
  refine ckD_ok (dv := dv) (wa := W x4) (wb := W x5) eWA hlt (by decide +kernel) hp hnd ?_ ?_ hFin ?_ hck
  · -- inputs
    have e1 : XA = (List.finRange 7).map (fun j : Fin 7 => W j) := by
      rw [← hWA, show List.range 7 = (List.finRange 7).map Fin.val from by decide, List.map_map]; rfl
    have e2 : ∀ j : Fin 7, dv (W j) = [2, 8, 16, 4, 32, 64, 128].getD (j : ℕ) 0 := by
      intro j
      rw [hdv j (by have := j.isLt; omega), dwj_in]
      revert j; decide +kernel
    have e3 : ∀ j : Fin 7, gt envA (px XA (XA.getD j 0)) = [2, 8, 16, 4, 32, 64, 128].getD (j : ℕ) 0 := by decide +kernel
    have e4 : ∀ j : Fin 7, XA.getD j 0 = W j := by
      intro j
      rw [← hWA]
      have : (j : ℕ) < ((List.range 7).map W).length := by simp
      rw [List.getD_eq_getElem _ _ this]; simp
    intro z hz
    rw [e1] at hz
    obtain ⟨j, _, rfl⟩ := List.mem_map.1 hz
    rw [e2 j, ← e4 j, e3 j]
  · intro w hw
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hw
    simp only [tro_eq hno ht]
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 ht
    obtain ⟨a, b, hab⟩ := mem_split hg
    have hal : a.length < 11 := by rw [← h11, hab]; simp
    rw [htout hab]
    rw [hab] at hD
    obtain ⟨a', g', b', hD', hl', hop, hin⟩ := forall2_split hD
    have hwv : dv (W (7 + a.length)) = dwj D (8 + a'.length) := by
      rw [hdv _ (by omega), hl']; congr 1; omega
    have rd : ∀ p s, p < 7 + a.length → (s = p + 1 ∨ s = 0 ∧ (p = x4 ∨ p = x5)) →
        Rd dv 255 (W x4) (W x5) (W p) (dwj D s) ∧ s < 8 + a'.length := by
      intro p s hp hs
      rcases hs with rfl | ⟨rfl, hs⟩
      · exact ⟨Or.inl (hdv p (by omega)).symm, by omega⟩
      · refine ⟨Or.inr ⟨dwj_zero D, ?_⟩, by omega⟩
        rcases hs with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
    rcases hshape hab with ⟨p, p', e, l1, l2, hh⟩ | ⟨p, t, e, l1, o, w⟩
    · rw [e] at hin
      obtain ⟨s, s', hs, hs', e'⟩ : ∃ s s', (s = p + 1 ∨ s = 0 ∧ (p = x4 ∨ p = x5)) ∧
          (s' = p' + 1 ∨ s' = 0 ∧ (p' = x4 ∨ p' = x5)) ∧ g'.inputs = [s, s'] := by
        revert hin
        generalize g'.inputs = li
        intro hin
        cases hin with
        | cons h1 h2 =>
          cases h2 with
          | cons h3 h4 =>
            cases h4
            exact ⟨_, _, h1, h3, rfl⟩
      obtain ⟨r1, q1⟩ := rd p s l1 hs
      obtain ⟨r2, q2⟩ := rd p' s' l2 hs'
      have hd := dwj_gate hD' e' q1 q2
      rcases hh with ⟨o, _⟩ | ⟨o, _⟩
      · refine ⟨dwj D s, dwj D s', ?_, ?_, ?_⟩
        · unfold trip; rw [o, e]; exact r1
        · unfold trip; rw [o, e]; exact r2
        · rw [hwv, hd.1 (hop ▸ o)]; unfold trip; rw [o, e]; rfl
      · refine ⟨dwj D s, dwj D s', ?_, ?_, ?_⟩
        · unfold trip; rw [o, e]; exact r1
        · unfold trip; rw [o, e]; exact r2
        · rw [hwv, hd.2 (hop ▸ o)]; unfold trip; rw [o, e]; rfl
    · exact absurd o (hnn g hg)
  · rw [← hFA, hdv _ ho]
    unfold dwj
    rw [show (6 : ℕ) = bitsV (fun k => (ff (asg (R8.getD k 0)) || asg (R8.getD k 0) 0 || asg (R8.getD k 0) 3)) 8 by decide +kernel]
    apply bitsV_congr
    intro k _
    exact hDv _

end Assembly

end PEqualNP.Outside.L_meta_3384

open PEqualNP.Outside.L_meta_3384 in
theorem PEqualNP.Outside.L_meta_3384 : have x1 : (Fin (7 : ℕ) → Bool) → Bool := fun (x1 : Fin (7 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (4 : ℕ), (15 : ℕ), (26 : ℕ), (35 : ℕ), (46 : ℕ), (36 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (7 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (7 : ℕ) (x2 % (10 : ℕ))); ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size = (11 : ℕ) → PEqualNP.MetaComplexity.circuitFun (7 : ℕ) x2 = x1 → List.Forall₂ (fun (x9 x10 : PEqualNP.CircuitLowerBounds.Gate) => x9.op = x10.op ∧ List.Forall₂ (fun (x11 x12 : ℕ) => x12 = x11 + (1 : ℕ) ∨ x12 = (0 : ℕ) ∧ (x11 = x4 ∨ x11 = x5)) x9.inputs x10.inputs) x2.gates x3.gates → (∀ (x10 : Fin (7 : ℕ) → Bool), (x3.wires (Bool.true :: List.ofFn x10)).getD (x2.output + (1 : ℕ)) Bool.false = (x1 x10 || x10 (0 : Fin (7 : ℕ)) || x10 (3 : Fin (7 : ℕ)))) → (List.filter (fun (x11 : PEqualNP.CircuitLowerBounds.Gate) => x11.op.eval [Bool.true, Bool.false] && x11.inputs.contains (2 : ℕ)) x2.gates).length ≥ (2 : ℕ) := by
  intro x1 x2 x3 x4 x5 hok hsz hf hD hDv
  by_contra hlt
  exact main x3 x4 x5 hok hsz (fun x => congrFun hf x) hD hDv (by omega)
