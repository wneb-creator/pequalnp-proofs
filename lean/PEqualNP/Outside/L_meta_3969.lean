import Mathlib.Data.Finset.Card
import Mathlib.Data.Tree.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.Bitwise
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3969

def domN (w d : ℕ) : Bool :=
  Nat.beq (Nat.land (Nat.land w 4095) (Nat.sub 16777215 d)) 0 &&
  Nat.beq (Nat.land (Nat.land d (Nat.sub 16777215 w)) 16773120) 0

def blk (m : Bool) (w d : ℕ) : Bool := cond m (domN w d) (Nat.beq w d)

def base10 : List ℕ :=
  [120900, 467977, 1593992, 3236112, 5382182, 8949779, 10846368, 12976960, 16256000, 16292883]

def base12 : List ℕ := 0 :: 16777215 :: base10

theorem land_compl (w : ℕ) : w &&& (16777215 - w) = 0 := by
  rcases lt_or_ge w (2 ^ 24) with h | h
  · apply Nat.eq_of_testBit_eq
    intro i
    have e : 16777215 - w = 2 ^ 24 - (w + 1) := by omega
    rw [e, Nat.testBit_and, Nat.testBit_two_pow_sub_succ h]
    cases w.testBit i <;> simp
  · have e : 16777215 - w = 0 := by omega
    simp [e]

theorem domN_refl (w : ℕ) : domN w w = true := by
  have h := land_compl w
  have h1 : Nat.land (Nat.land w 4095) (Nat.sub 16777215 w) = 0 := by
    show (w &&& 4095) &&& (16777215 - w) = 0
    rw [Nat.and_right_comm, h]; simp
  have h2 : Nat.land (Nat.land w (Nat.sub 16777215 w)) 16773120 = 0 := by
    show (w &&& (16777215 - w)) &&& 16773120 = 0
    rw [h]; simp
  unfold domN
  rw [h1, h2]
  rfl

theorem blk_refl (m : Bool) (w : ℕ) : blk m w w = true := by
  cases m
  · simp [blk]
  · simp [blk, domN_refl]

inductive Reach (m : Bool) : Finset ℕ → ℕ → Prop
  | done (k : ℕ) : Reach m {4095} k
  | step (D : Finset ℕ) (k u v w : ℕ) (ka kb : Bool) :
      u ∈ D → v ∈ D → (w = u &&& v ∨ w = u ||| v) →
      (∀ d ∈ D, blk m w d = false) → (∀ d ∈ base12, blk m w d = false) →
      Reach m (insert w (D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v)))) k →
      Reach m D (k + 1)

theorem Reach.mono {m : Bool} {D : Finset ℕ} {k : ℕ} (h : Reach m D k) : Reach m D (k + 1) := by
  induction h with
  | done k => exact Reach.done _
  | step D k u v w ka kb hu hv hw hd hb _ ih => exact Reach.step D (k + 1) u v w ka kb hu hv hw hd hb ih

theorem Reach.mono_le {m : Bool} {D : Finset ℕ} {k k' : ℕ} (hk : k ≤ k') (h : Reach m D k) :
    Reach m D k' := by
  induction hk with
  | refl => exact h
  | step _ ih => exact ih.mono

theorem Reach.zero {m : Bool} {D : Finset ℕ} (h : Reach m D 0) : D = {4095} := by
  cases h
  rfl

theorem Reach.inv' {m : Bool} {D : Finset ℕ} {k' : ℕ} (h : Reach m D k') : ∀ k : ℕ, k' = k + 1 →
    D = {4095} ∨ ∃ (u v w : ℕ) (ka kb : Bool), u ∈ D ∧ v ∈ D ∧ (w = u &&& v ∨ w = u ||| v) ∧
      (∀ d ∈ D, blk m w d = false) ∧ (∀ d ∈ base12, blk m w d = false) ∧
      Reach m (insert w (D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v)))) k := by
  induction h with
  | done k0 => intro _ _; exact Or.inl rfl
  | step D k0 u v w ka kb hu hv hw hd hb hr _ =>
    intro k hk
    obtain rfl : k0 = k := by omega
    exact Or.inr ⟨u, v, w, ka, kb, hu, hv, hw, hd, hb, hr⟩

theorem Reach.inv {m : Bool} {D : Finset ℕ} {k : ℕ} (h : Reach m D (k + 1)) :
    D = {4095} ∨ ∃ (u v w : ℕ) (ka kb : Bool), u ∈ D ∧ v ∈ D ∧ (w = u &&& v ∨ w = u ||| v) ∧
      (∀ d ∈ D, blk m w d = false) ∧ (∀ d ∈ base12, blk m w d = false) ∧
      Reach m (insert w (D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v)))) k :=
  h.inv' k rfl

theorem Reach.card {m : Bool} {D : Finset ℕ} {k : ℕ} (h : Reach m D k) : D.card ≤ k + 1 := by
  induction h with
  | done k => simp
  | step D k u v w ka kb hu hv hw hd hb _ ih =>
    have hwD : w ∉ D := fun hm => by
      have := hd w hm
      rw [blk_refl] at this
      exact Bool.noConfusion this
    have hwF : w ∉ D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v)) :=
      fun hm => hwD (Finset.mem_of_mem_filter _ hm)
    rw [Finset.card_insert_of_notMem hwF] at ih
    have hsub : D ⊆ insert u (insert v
        (D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v)))) := by
      intro x hx
      by_cases h1 : x = u
      · simp [h1]
      by_cases h2 : x = v
      · simp [h2]
      simp [hx, h1, h2]
    have h2 := Finset.card_le_card hsub
    have h3 := Finset.card_insert_le u (insert v
        (D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v))))
    have h4 := Finset.card_insert_le v
        (D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v)))
    omega

theorem tb4095 (i : ℕ) : (4095 : ℕ).testBit i = decide (i < 12) := by
  have e : (4095 : ℕ) = 2 ^ 12 - 1 := by norm_num
  rw [e, Nat.testBit_two_pow_sub_one]

theorem Reach.sep {m : Bool} {D : Finset ℕ} {k : ℕ} (h : Reach m D k) (e i : ℕ) (he : e < 12)
    (hi : 12 ≤ i) : ∃ w ∈ D, w.testBit e = true ∧ w.testBit i = false := by
  induction h with
  | done k =>
    refine ⟨4095, by simp, ?_, ?_⟩
    · rw [tb4095]; simpa using he
    · rw [tb4095]; simpa using hi
  | step D k u v w ka kb hu hv hw hd hb _ ih =>
    obtain ⟨x, hx, h1, h2⟩ := ih
    rcases Finset.mem_insert.mp hx with hxw | hx
    · subst hxw
      rcases hw with hw | hw
      · subst hw
        rw [Nat.testBit_and] at h1 h2
        cases hum : u.testBit i
        · exact ⟨u, hu, by simp_all, hum⟩
        · exact ⟨v, hv, by simp_all, by simp_all⟩
      · subst hw
        rw [Nat.testBit_or] at h1 h2
        cases hue : u.testBit e
        · exact ⟨v, hv, by simp_all, by simp_all⟩
        · exact ⟨u, hu, hue, by simp_all⟩
    · exact ⟨x, Finset.mem_of_mem_filter _ hx, h1, h2⟩

def tb (w e : ℕ) : Bool := !(Nat.beq (Nat.land (Nat.shiftRight w e) 1) 0)

theorem tb_eq (w e : ℕ) : tb w e = w.testBit e := by
  have h : Nat.land (Nat.shiftRight w e) 1 = 1 &&& (w >>> e) := Nat.and_comm _ _
  unfold tb Nat.testBit
  rw [h]
  generalize (1 &&& w >>> e) = X
  cases X <;> rfl

def rect (x J : ℕ) : ℕ → ℕ
  | 0 => 0
  | e + 1 => Nat.lor (cond (tb x e) (Nat.shiftLeft J (Nat.mul 12 e)) 0) (rect x J e)

def rectW (x : ℕ) : ℕ := rect x (Nat.xor (Nat.shiftRight x 12) 4095) 12

theorem rect_tb (x J i : ℕ) (hJ : J.testBit i = true) : ∀ n e : ℕ, e < n → x.testBit e = true →
    (rect x J n).testBit (12 * e + i) = true := by
  intro n
  induction n with
  | zero => intro e he; omega
  | succ n ih =>
    intro e he hx
    show ((cond (tb x n) (J <<< (12 * n)) 0) ||| rect x J n).testBit (12 * e + i) = true
    rw [Nat.testBit_or]
    by_cases hen : e = n
    · subst hen
      rw [tb_eq, hx]
      simp [Nat.testBit_shiftLeft, hJ]
    · rw [ih e (by omega) hx]
      simp

theorem rectW_tb (x e i : ℕ) (he : e < 12) (hi : i < 12) (h1 : x.testBit e = true)
    (h2 : x.testBit (12 + i) = false) : (rectW x).testBit (12 * e + i) = true := by
  apply rect_tb _ _ _ _ 12 e he h1
  show ((x >>> 12) ^^^ 4095).testBit i = true
  rw [Nat.testBit_xor, Nat.testBit_shiftRight, h2, tb4095]
  simp [hi]

theorem sep_bit {m : Bool} {D : Finset ℕ} {k : ℕ} (hR : Reach m D k) (p : ℕ) (hp : p < 144) :
    ∃ x ∈ D, (rectW x).testBit p = true := by
  obtain ⟨x, hx, h1, h2⟩ := hR.sep (p / 12) (12 + p % 12) (by omega) (by omega)
  refine ⟨x, hx, ?_⟩
  have := rectW_tb x (p / 12) (p % 12) (by omega) (Nat.mod_lt _ (by norm_num)) h1 h2
  rwa [Nat.div_add_mod] at this

def full : ℕ := 22300745198530623141535718272648361505980415

theorem full_eq : full = 2 ^ 144 - 1 := by norm_num [full]

def covR (c : ℕ) : Bool := Nat.beq (Nat.land c full) full

theorem covR_of (c : ℕ) (h : ∀ p, p < 144 → c.testBit p = true) : covR c = true := by
  have e : Nat.land c full = full := by
    show c &&& full = full
    rw [full_eq]
    apply Nat.eq_of_testBit_eq
    intro p
    rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one]
    by_cases hp : p < 144
    · simp [hp, h p hp]
    · simp [hp]
  unfold covR
  rw [e]
  exact Nat.beq_refl _

def orR : List ℕ → ℕ
  | [] => 0
  | x :: l => Nat.lor (rectW x) (orR l)

theorem orR_tb (p : ℕ) : ∀ l : List ℕ, ∀ x ∈ l, (rectW x).testBit p = true →
    (orR l).testBit p = true := by
  intro l
  induction l with
  | nil => intro x hx; simp at hx
  | cons a l ih =>
    intro x hx h
    show (rectW a ||| orR l).testBit p = true
    rw [Nat.testBit_or]
    rcases List.mem_cons.mp hx with hxa | hx
    · rw [← hxa, h]; rfl
    · rw [ih x hx h]; simp

theorem cover_sound {m : Bool} {l : List ℕ} {k : ℕ} (h : covR (orR l) = false) :
    ¬ Reach m l.toFinset k := by
  intro hR
  have : covR (orR l) = true := by
    apply covR_of
    intro p hp
    obtain ⟨x, hx, hb⟩ := sep_bit hR p hp
    exact orR_tb p l x (List.mem_toFinset.mp hx) hb
  rw [h] at this
  exact Bool.noConfusion this

def allFinal : List ℕ → Bool
  | [] => true
  | a :: l => Nat.beq a 4095 && allFinal l

theorem allFinal_of : ∀ l : List ℕ, (∀ a ∈ l, a = 4095) → allFinal l = true := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a l ih =>
    intro h
    have ha := h a (List.mem_cons_self)
    simp only [allFinal, ha, Bool.and_eq_true]
    exact ⟨rfl, ih (fun b hb => h b (List.mem_cons_of_mem _ hb))⟩

theorem notFinal {l : List ℕ} (h : allFinal l = false) : l.toFinset ≠ {4095} := by
  intro he
  have : allFinal l = true := by
    apply allFinal_of
    intro a ha
    have : a ∈ l.toFinset := List.mem_toFinset.mpr ha
    rw [he] at this
    exact Finset.mem_singleton.mp this
  rw [h] at this
  exact Bool.noConfusion this

def ins (w : ℕ) : List ℕ → List ℕ
  | [] => [w]
  | a :: l => cond (Nat.blt w a) (w :: a :: l) (a :: ins w l)

theorem ins_perm (w : ℕ) : ∀ l : List ℕ, (ins w l).Perm (w :: l) := by
  intro l
  induction l with
  | nil => exact List.Perm.refl _
  | cons a l ih =>
    unfold ins
    cases Nat.blt w a
    · exact (List.Perm.cons a ih).trans (List.Perm.swap w a l)
    · exact List.Perm.refl _

def sortedFrom (a : ℕ) : List ℕ → Bool
  | [] => true
  | b :: l => Nat.blt a b && sortedFrom b l

def sortedB : List ℕ → Bool
  | [] => true
  | a :: l => sortedFrom a l

theorem sortedFrom_lt : ∀ (l : List ℕ) (a : ℕ), sortedFrom a l = true → ∀ x ∈ l, a < x := by
  intro l
  induction l with
  | nil => intro a _ x hx; simp at hx
  | cons b l ih =>
    intro a h x hx
    simp only [sortedFrom, Bool.and_eq_true] at h
    have hab : a < b := by simpa [Nat.blt_eq] using h.1
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hab
    · exact lt_trans hab (ih b h.2 x hx)

theorem sortedFrom_nodup : ∀ (l : List ℕ) (a : ℕ), sortedFrom a l = true → (a :: l).Nodup := by
  intro l
  induction l with
  | nil => intro a _; simp
  | cons b l ih =>
    intro a h
    have hlt := sortedFrom_lt (b :: l) a h
    simp only [sortedFrom, Bool.and_eq_true] at h
    refine List.nodup_cons.mpr ⟨fun hm => lt_irrefl a (hlt a hm), ih b h.2⟩

theorem sortedB_nodup {l : List ℕ} (h : sortedB l = true) : l.Nodup := by
  cases l with
  | nil => simp
  | cons a l => exact sortedFrom_nodup l a h

abbrev Tree : Type := BinaryTree (List ℕ)

def lcmp : List ℕ → List ℕ → Ordering
  | [], [] => Ordering.eq
  | [], _ :: _ => Ordering.lt
  | _ :: _, [] => Ordering.gt
  | a :: x, b :: y => cond (Nat.blt a b) Ordering.lt (cond (Nat.blt b a) Ordering.gt (lcmp x y))

theorem lcmp_eq : ∀ (x y : List ℕ), lcmp x y = Ordering.eq → x = y := by
  intro x
  induction x with
  | nil => intro y h; cases y with
    | nil => rfl
    | cons b y => simp [lcmp] at h
  | cons a x ih =>
    intro y h
    cases y with
    | nil => simp [lcmp] at h
    | cons b y =>
      unfold lcmp at h
      cases h1 : Nat.blt a b
      · cases h2 : Nat.blt b a
        · rw [h1, h2] at h
          have e1 : ¬ a < b := by rw [← Nat.blt_eq, h1]; simp
          have e2 : ¬ b < a := by rw [← Nat.blt_eq, h2]; simp
          have : a = b := by omega
          rw [this, ih y h]
        · rw [h1, h2] at h; simp at h
      · rw [h1] at h; simp at h

def thas : Tree → List ℕ → Bool
  | BinaryTree.nil, _ => false
  | BinaryTree.node key l r, x =>
    match lcmp x key with
    | Ordering.lt => thas l x
    | Ordering.eq => true
    | Ordering.gt => thas r x

def tall (p : List ℕ → Bool) : Tree → Bool
  | BinaryTree.nil => true
  | BinaryTree.node key l r => p key && tall p l && tall p r

theorem thas_all (p : List ℕ → Bool) : ∀ (t : Tree) (x : List ℕ), tall p t = true →
    thas t x = true → p x = true := by
  intro t
  induction t with
  | nil => intro x _ h; simp [thas] at h
  | node key l r ihl ihr =>
    intro x ha hh
    simp only [tall, Bool.and_eq_true] at ha
    unfold thas at hh
    cases hc : lcmp x key
    · rw [hc] at hh; exact ihl x ha.1.2 hh
    · rw [lcmp_eq x key hc]; exact ha.1.1
    · rw [hc] at hh; exact ihr x ha.2 hh

def closed (prev : Tree) (k : ℕ) (l : List ℕ) : Bool :=
  Nat.blt (Nat.succ k) l.length || !(covR (orR l)) || (Nat.beq k 0 && !(allFinal l)) || thas prev l

def Inv (m : Bool) (prev : Tree) (k : ℕ) : Prop :=
  ∀ x : List ℕ, thas prev x = true → ¬ Reach m x.toFinset k

theorem closed_sound {m : Bool} {prev : Tree} {k : ℕ} {l : List ℕ} (hnd : l.Nodup)
    (hinv : Inv m prev k) (h : closed prev k l = true) : ¬ Reach m l.toFinset k := by
  intro hR
  simp only [closed, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
  rcases h with ((h | h) | h) | h
  · have h1 : k + 1 < l.length := by simpa [Nat.blt_eq] using h
    have h2 := hR.card
    rw [List.toFinset_card_of_nodup hnd] at h2
    omega
  · exact cover_sound h hR
  · have hk : k = 0 := Nat.eq_of_beq_eq_true h.1
    subst hk
    exact notFinal h.2 hR.zero
  · exact hinv l h hR

theorem beq_false_iff (x u : ℕ) : Nat.beq x u = false ↔ x ≠ u := by
  constructor
  · intro h he
    rw [he, Nat.beq_refl] at h
    exact Bool.noConfusion h
  · intro h
    cases hb : Nat.beq x u
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hb) h

def remF (ka kb : Bool) (u v x : ℕ) : Bool := (ka || !(Nat.beq x u)) && (kb || !(Nat.beq x v))

def PruneOK (m : Bool) (P : List ℕ → ℕ → Bool) : Prop :=
  ∀ (l : List ℕ) (k : ℕ), l.Nodup → Reach m l.toFinset k → P l k = true

theorem PruneOK.and {m : Bool} {P Q : List ℕ → ℕ → Bool} (hP : PruneOK m P) (hQ : PruneOK m Q) :
    PruneOK m (fun l k => P l k && Q l k) := by
  intro l k hnd hR
  simp only [hP l k hnd hR, hQ l k hnd hR, Bool.and_self]

def lastOK (P : List ℕ → ℕ → Bool) (prev : Tree) (k : ℕ) (l : List ℕ) : Bool :=
  (Nat.beq k 0 && !(allFinal l)) || thas prev l || !(P l k)

theorem lastOK_sound {m : Bool} {P : List ℕ → ℕ → Bool} {prev : Tree} {k : ℕ} {l : List ℕ}
    (hP : PruneOK m P) (hnd : l.Nodup)
    (hinv : Inv m prev k) (h : lastOK P prev k l = true) : ¬ Reach m l.toFinset k := by
  intro hR
  simp only [lastOK, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
  rcases h with (h | h) | h
  · have hk : k = 0 := Nat.eq_of_beq_eq_true h.1
    subst hk
    exact notFinal h.2 hR.zero
  · exact hinv l h hR
  · rw [hP l k hnd hR] at h; exact Bool.noConfusion h

def sOK (P : List ℕ → ℕ → Bool) (prev : Tree) (k : ℕ) (l : List ℕ) (u v w : ℕ) (sz : Bool) (c : ℕ) (ka kb : Bool) : Bool :=
  sz || !(covR c) || lastOK P prev k (ins w (l.filter (remF ka kb u v)))

def blkAny (m : Bool) (w : ℕ) : List ℕ → Bool
  | [] => false
  | d :: l => blk m w d || blkAny m w l

theorem blkAny_false (m : Bool) (w : ℕ) : ∀ l : List ℕ, (∀ d ∈ l, blk m w d = false) →
    blkAny m w l = false := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a l ih =>
    intro h
    simp only [blkAny, h a List.mem_cons_self, Bool.false_or]
    exact ih (fun d hd => h d (List.mem_cons_of_mem _ hd))

def opOK2 (P : List ℕ → ℕ → Bool) (prev : Tree) (k : ℕ) (l : List ℕ) (u ru v rv w c : ℕ) : Bool :=
  sOK P prev k l u v w (Nat.blt (Nat.add k 2) l.length) c false false &&
  sOK P prev k l u v w (Nat.blt (Nat.succ k) l.length) (Nat.lor c rv) false true &&
  sOK P prev k l u v w (Nat.blt (Nat.succ k) l.length) (Nat.lor c ru) true false &&
  sOK P prev k l u v w (Nat.blt k l.length) (Nat.lor c (Nat.lor ru rv)) true true

def opOK (m : Bool) (P : List ℕ → ℕ → Bool) (prev : Tree) (k : ℕ) (l : List ℕ) (u ru v rv ro w : ℕ) : Bool :=
  blkAny m w base12 || blkAny m w l || opOK2 P prev k l u ru v rv w (Nat.lor (rectW w) ro)

def orEx (u v : ℕ) : List ℕ → ℕ
  | [] => 0
  | x :: l => cond (Nat.beq x u || Nat.beq x v) (orEx u v l) (Nat.lor (rectW x) (orEx u v l))

theorem orEx_tb (u v p : ℕ) : ∀ l : List ℕ, ∀ x : ℕ, x ∈ l → x ≠ u → x ≠ v →
    (rectW x).testBit p = true → (orEx u v l).testBit p = true := by
  intro l
  induction l with
  | nil => intro x hx; simp at hx
  | cons y l ih =>
    intro x hx hxu hxv h
    unfold orEx
    rcases List.mem_cons.mp hx with hxa | hx
    · subst hxa
      rw [(beq_false_iff x u).mpr hxu, (beq_false_iff x v).mpr hxv]
      show (rectW x ||| orEx u v l).testBit p = true
      rw [Nat.testBit_or, h]; rfl
    · have := ih x hx hxu hxv h
      cases (Nat.beq y u || Nat.beq y v)
      · show (rectW y ||| orEx u v l).testBit p = true
        rw [Nat.testBit_or, this]; simp
      · exact this

def pairOK (m : Bool) (P : List ℕ → ℕ → Bool) (prev : Tree) (k : ℕ) (l : List ℕ) (u v : ℕ) : Bool :=
  opOK m P prev k l u (rectW u) v (rectW v) (orEx u v l) (Nat.land u v) &&
  opOK m P prev k l u (rectW u) v (rectW v) (orEx u v l) (Nat.lor u v)

def allB {α : Type} (f : α → Bool) : List α → Bool
  | [] => true
  | a :: l => f a && allB f l

theorem allB_mem {α : Type} (f : α → Bool) : ∀ l : List α, allB f l = true →
    ∀ x ∈ l, f x = true := by
  intro l
  induction l with
  | nil => intro _ x hx; simp at hx
  | cons a l ih =>
    intro h x hx
    simp only [allB, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact ih h.2 x hx

def pairsAll {α : Type} (f : α → α → Bool) : List α → Bool
  | [] => true
  | a :: l => allB (f a) l && pairsAll f l

theorem pairsAll_mem {α : Type} (f : α → α → Bool) : ∀ l : List α, pairsAll f l = true →
    ∀ u ∈ l, ∀ v ∈ l, u ≠ v → f u v = true ∨ f v u = true := by
  intro l
  induction l with
  | nil => intro _ u hu; simp at hu
  | cons a l ih =>
    intro h u hu v hv huv
    simp only [pairsAll, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hu with hua | hu
    · rcases List.mem_cons.mp hv with hva | hv
      · exact absurd (hua.trans hva.symm) huv
      · rw [hua]; exact Or.inl (allB_mem _ l h.1 v hv)
    · rcases List.mem_cons.mp hv with hva | hv
      · rw [hva]; exact Or.inr (allB_mem _ l h.1 u hu)
      · exact ih h.2 u hu v hv huv

theorem size_lb (D : Finset ℕ) (u v : ℕ) (ka kb : Bool) :
    D.card ≤ (D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v))).card +
      (cond ka 0 1 + cond kb 0 1) := by
  have hsub : D ⊆ (D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v))) ∪
      ((cond ka ∅ {u}) ∪ (cond kb ∅ {v})) := by
    intro x hx
    by_cases h1 : x = u <;> by_cases h2 : x = v <;> cases ka <;> cases kb <;> simp_all
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v)))
    ((cond ka ∅ {u}) ∪ (cond kb ∅ {v}))
  have h3 := Finset.card_union_le (cond ka (∅ : Finset ℕ) {u}) (cond kb ∅ {v})
  have h4 : (cond ka (∅ : Finset ℕ) {u}).card = cond ka 0 1 := by cases ka <;> simp
  have h5 : (cond kb (∅ : Finset ℕ) {v}).card = cond kb 0 1 := by cases kb <;> simp
  omega

theorem pair_sound {m : Bool} {P : List ℕ → ℕ → Bool} {prev : Tree} {k : ℕ} {l : List ℕ} {u v : ℕ}
    (hP : PruneOK m P) (hinv : Inv m prev k) (hnd : l.Nodup) (hp : pairOK m P prev k l u v = true)
    (hu : u ∈ l) (hv : v ∈ l)
    (ka kb : Bool) (w : ℕ) (hw : w = u &&& v ∨ w = u ||| v)
    (hd : ∀ d ∈ l, blk m w d = false) (hb : ∀ d ∈ base12, blk m w d = false) :
    ¬ Reach m (insert w (l.toFinset.filter
      (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v)))) k := by
  intro hR
  simp only [pairOK, Bool.and_eq_true] at hp
  have hop : opOK m P prev k l u (rectW u) v (rectW v) (orEx u v l) w = true := by
    rcases hw with rfl | rfl
    · exact hp.1
    · exact hp.2
  simp only [opOK, blkAny_false m w base12 hb, blkAny_false m w l hd, Bool.false_or, opOK2,
    Bool.and_eq_true] at hop
  have hwl : w ∉ l := fun hm => by
    have := hd w hm
    rw [blk_refl] at this
    exact Bool.noConfusion this

  have hsz : l.length ≤ k + (cond ka 0 1 + cond kb 0 1) := by
    have h1 := hR.card
    have hwF : w ∉ l.toFinset.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v)) :=
      fun hm => hwl (List.mem_toFinset.mp (Finset.mem_of_mem_filter _ hm))
    rw [Finset.card_insert_of_notMem hwF] at h1
    have h2 := size_lb l.toFinset u v ka kb
    rw [List.toFinset_card_of_nodup hnd] at h2
    omega

  have hbit : ∀ p, p < 144 → ((rectW w).testBit p = true ∨ (orEx u v l).testBit p = true) ∨
      (ka = true ∧ (rectW u).testBit p = true) ∨ (kb = true ∧ (rectW v).testBit p = true) := by
    intro p hp
    obtain ⟨x, hx, hxb⟩ := sep_bit hR p hp
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Or.inl (Or.inl hxb)
    · obtain ⟨hxl, h1, h2⟩ := Finset.mem_filter.mp hx
      by_cases hxu : x = u
      · exact Or.inr (Or.inl ⟨h1.resolve_right (fun h => h hxu), hxu ▸ hxb⟩)
      · by_cases hxv : x = v
        · exact Or.inr (Or.inr ⟨h2.resolve_right (fun h => h hxv), hxv ▸ hxb⟩)
        · exact Or.inl (Or.inr (orEx_tb u v p _ x (List.mem_toFinset.mp hxl) hxu hxv hxb))
  have hfs : (ins w (l.filter (remF ka kb u v))).toFinset =
      insert w (l.toFinset.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v))) := by
    ext x
    rw [List.mem_toFinset, (ins_perm w _).mem_iff]
    simp [remF, List.mem_filter, beq_false_iff]
  have key : ∀ (sz : Bool) (c : ℕ), sOK P prev k l u v w sz c ka kb = true →
      (sz = true → False) → (∀ p, p < 144 → c.testBit p = true) → False := by
    intro sz c h h1 h2
    simp only [sOK, Bool.or_eq_true, Bool.not_eq_true'] at h
    rcases h with (h | h) | h
    · exact h1 h
    · rw [covR_of c h2] at h; exact Bool.noConfusion h
    · rw [← hfs] at hR
      refine lastOK_sound hP ?_ hinv h hR
      rw [(ins_perm w _).nodup_iff]
      exact List.nodup_cons.mpr ⟨fun hm => hwl (List.mem_filter.mp hm).1, hnd.filter _⟩
  cases ka <;> cases kb
  · refine key _ _ hop.1.1.1 (fun h => ?_) (fun p hp => ?_)
    · have : k + 2 < l.length := by simpa [Nat.blt_eq] using h
      simp at hsz; omega
    · have := hbit p hp
      show (rectW w ||| orEx u v l).testBit p = true
      rw [Nat.testBit_or]; simp at this; simpa using this
  · refine key _ _ hop.1.1.2 (fun h => ?_) (fun p hp => ?_)
    · have : k + 1 < l.length := by simpa [Nat.blt_eq] using h
      simp at hsz; omega
    · have := hbit p hp
      show ((rectW w ||| orEx u v l) ||| rectW v).testBit p = true
      rw [Nat.testBit_or, Nat.testBit_or]; simp at this; simpa using this
  · refine key _ _ hop.1.2 (fun h => ?_) (fun p hp => ?_)
    · have : k + 1 < l.length := by simpa [Nat.blt_eq] using h
      simp at hsz; omega
    · have := hbit p hp
      show ((rectW w ||| orEx u v l) ||| rectW u).testBit p = true
      rw [Nat.testBit_or, Nat.testBit_or]; simp at this; simpa using this
  · refine key _ _ hop.2 (fun h => ?_) (fun p hp => ?_)
    · have : k < l.length := by simpa [Nat.blt_eq] using h
      simp at hsz; omega
    · have := hbit p hp
      show ((rectW w ||| orEx u v l) ||| (rectW u ||| rectW v)).testBit p = true
      rw [Nat.testBit_or, Nat.testBit_or, Nat.testBit_or]; simp at this; simpa using this

def expOK (m : Bool) (P : List ℕ → ℕ → Bool) (prev : Tree) (k : ℕ) (l : List ℕ) : Bool :=
  sortedB l && !(allFinal l) && pairsAll (pairOK m P prev k l) l

theorem expOK_sound {m : Bool} {P : List ℕ → ℕ → Bool} {prev : Tree} {k : ℕ} {l : List ℕ}
    (hP : PruneOK m P) (hinv : Inv m prev k)
    (h : expOK m P prev k l = true) : ¬ Reach m l.toFinset (k + 1) := by
  intro hR
  simp only [expOK, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hs, hf⟩, hp⟩ := h
  have hnd := sortedB_nodup hs
  rcases hR.inv with he | ⟨u, v, w, ka, kb, hu, hv, hw, hd, hb, hR'⟩
  · exact notFinal hf he
  · have hd' : ∀ d ∈ l, blk m w d = false := fun d hdm => hd d (List.mem_toFinset.mpr hdm)
    have hu' := List.mem_toFinset.mp hu
    have hv' := List.mem_toFinset.mp hv
    have huv : u ≠ v := by
      rintro rfl
      have hwu : w = u := by
        rcases hw with hw | hw
        · rw [hw, Nat.and_self]
        · rw [hw, Nat.or_self]
      have := hd u hu
      rw [hwu, blk_refl] at this
      exact Bool.noConfusion this
    rcases pairsAll_mem _ _ hp u hu' v hv' huv with h1 | h1
    · exact pair_sound hP hinv hnd h1 hu' hv' ka kb w hw hd' hb hR'
    · have hw2 : w = v &&& u ∨ w = v ||| u := by
        rw [Nat.and_comm v u, Nat.or_comm v u]; exact hw
      have hfe : (l.toFinset.filter (fun x => (kb = true ∨ x ≠ v) ∧ (ka = true ∨ x ≠ u))) =
          (l.toFinset.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v))) := by
        ext x
        simp only [Finset.mem_filter]
        tauto
      have := pair_sound hP hinv hnd h1 hv' hu' kb ka w hw2 hd' hb
      rw [hfe] at this
      exact this hR'

def subsAll : List ℕ → (List ℕ → Bool) → Bool
  | [], p => p []
  | a :: l, p => subsAll l p && subsAll l (fun s => p (a :: s))

theorem subsAll_sub : ∀ (l : List ℕ) (p : List ℕ → Bool), subsAll l p = true →
    ∀ s : List ℕ, s.Sublist l → p s = true := by
  intro l
  induction l with
  | nil =>
    intro p h s hs
    rw [List.sublist_nil.mp hs]; exact h
  | cons a l ih =>
    intro p h s hs
    simp only [subsAll, Bool.and_eq_true] at h
    cases hs with
    | cons _ hs' => exact ih p h.1 s hs'
    | cons_cons _ hs' => exact ih _ h.2 _ hs'

def bor (a b : Bool) : Bool := @Bool.rec (fun _ => Bool) b true a
def band (a b : Bool) : Bool := @Bool.rec (fun _ => Bool) false b a
def bnot (a : Bool) : Bool := @Bool.rec (fun _ => Bool) true false a

theorem bor_eq (a b : Bool) : bor a b = (a || b) := by cases a <;> rfl
theorem band_eq (a b : Bool) : band a b = (a && b) := by cases a <;> rfl
theorem bnot_eq (a : Bool) : bnot a = !a := by cases a <;> rfl

def domN' (w d : ℕ) : Bool :=
  band (Nat.beq (Nat.land (Nat.land w 4095) (Nat.sub 16777215 d)) 0)
    (Nat.beq (Nat.land (Nat.land d (Nat.sub 16777215 w)) 16773120) 0)

theorem domN'_eq (w d : ℕ) : domN' w d = domN w d := by
  unfold domN' domN; rw [band_eq]

def blk' (m : Bool) (w d : ℕ) : Bool := @Bool.rec (fun _ => Bool) (Nat.beq w d) (domN' w d) m

theorem blk'_eq (m : Bool) (w d : ℕ) : blk' m w d = blk m w d := by
  cases m
  · rfl
  · show domN' w d = domN w d
    exact domN'_eq w d

def blkAny' (m : Bool) (w : ℕ) (l : List ℕ) : Bool :=
  @List.rec ℕ (fun _ => Bool) false (fun d _ ih => bor (blk' m w d) ih) l

theorem blkAny'_eq (m : Bool) (w : ℕ) (l : List ℕ) : blkAny' m w l = blkAny m w l := by
  induction l with
  | nil => rfl
  | cons d l ih =>
    show bor (blk' m w d) (blkAny' m w l) = (blk m w d || blkAny m w l)
    rw [ih, bor_eq, blk'_eq]

def tb' (w e : ℕ) : Bool := bnot (Nat.beq (Nat.land (Nat.shiftRight w e) 1) 0)

theorem tb'_eq (w e : ℕ) : tb' w e = tb w e := by
  unfold tb' tb; rw [bnot_eq]

def rect' (x J n : ℕ) : ℕ :=
  @Nat.rec (fun _ => ℕ) 0
    (fun e ih => Nat.lor (@Bool.rec (fun _ => ℕ) 0 (Nat.shiftLeft J (Nat.mul 12 e)) (tb' x e)) ih) n

theorem rect'_eq (x J n : ℕ) : rect' x J n = rect x J n := by
  induction n with
  | zero => rfl
  | succ e ih =>
    show Nat.lor (@Bool.rec (fun _ => ℕ) 0 (Nat.shiftLeft J (Nat.mul 12 e)) (tb' x e)) (rect' x J e) =
      Nat.lor (cond (tb x e) (Nat.shiftLeft J (Nat.mul 12 e)) 0) (rect x J e)
    rw [ih, tb'_eq]
    cases tb x e <;> rfl

def rectW' (x : ℕ) : ℕ := rect' x (Nat.xor (Nat.shiftRight x 12) 4095) 12

theorem rectW'_eq (x : ℕ) : rectW' x = rectW x := rect'_eq _ _ _

def orEx' (u v : ℕ) (l : List ℕ) : ℕ :=
  @List.rec ℕ (fun _ => ℕ) 0
    (fun x _ ih => @Bool.rec (fun _ => ℕ) (Nat.lor (rectW' x) ih) ih
      (bor (Nat.beq x u) (Nat.beq x v))) l

theorem orEx'_eq (u v : ℕ) (l : List ℕ) : orEx' u v l = orEx u v l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    show @Bool.rec (fun _ => ℕ) (Nat.lor (rectW' x) (orEx' u v l)) (orEx' u v l)
      (bor (Nat.beq x u) (Nat.beq x v)) =
      cond (Nat.beq x u || Nat.beq x v) (orEx u v l) (Nat.lor (rectW x) (orEx u v l))
    rw [ih, bor_eq, rectW'_eq]
    cases (Nat.beq x u || Nat.beq x v) <;> rfl

def allFinal' (l : List ℕ) : Bool :=
  @List.rec ℕ (fun _ => Bool) true (fun a _ ih => band (Nat.beq a 4095) ih) l

theorem allFinal'_eq (l : List ℕ) : allFinal' l = allFinal l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    show band (Nat.beq a 4095) (allFinal' l) = (Nat.beq a 4095 && allFinal l)
    rw [ih, band_eq]

def ins' (w : ℕ) (l : List ℕ) : List ℕ :=
  @List.rec ℕ (fun _ => List ℕ) [w]
    (fun a t ih => @Bool.rec (fun _ => List ℕ) (a :: ih) (w :: a :: t) (Nat.blt w a)) l

theorem ins'_eq (w : ℕ) (l : List ℕ) : ins' w l = ins w l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    show @Bool.rec (fun _ => List ℕ) (a :: ins' w l) (w :: a :: l) (Nat.blt w a) =
      cond (Nat.blt w a) (w :: a :: l) (a :: ins w l)
    rw [ih]
    cases Nat.blt w a <;> rfl

def filt' (ka kb : Bool) (u v : ℕ) (l : List ℕ) : List ℕ :=
  @List.rec ℕ (fun _ => List ℕ) []
    (fun x _ ih => @Bool.rec (fun _ => List ℕ) ih (x :: ih)
      (band (bor ka (bnot (Nat.beq x u))) (bor kb (bnot (Nat.beq x v))))) l

theorem filt'_eq (ka kb : Bool) (u v : ℕ) (l : List ℕ) :
    filt' ka kb u v l = l.filter (remF ka kb u v) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    show @Bool.rec (fun _ => List ℕ) (filt' ka kb u v l) (x :: filt' ka kb u v l)
      (band (bor ka (bnot (Nat.beq x u))) (bor kb (bnot (Nat.beq x v)))) = _
    rw [ih, band_eq, bor_eq, bor_eq, bnot_eq, bnot_eq, List.filter_cons]
    show _ = if remF ka kb u v x = true then _ else _
    unfold remF
    cases ((ka || !Nat.beq x u) && (kb || !Nat.beq x v)) <;> rfl

def lcmp' (x y : List ℕ) : Ordering :=
  @List.rec ℕ (fun _ => List ℕ → Ordering)
    (fun y => @List.rec ℕ (fun _ => Ordering) Ordering.eq (fun _ _ _ => Ordering.lt) y)
    (fun a _ ih y => @List.rec ℕ (fun _ => Ordering) Ordering.gt
      (fun b y' _ => @Bool.rec (fun _ => Ordering)
        (@Bool.rec (fun _ => Ordering) (ih y') Ordering.gt (Nat.blt b a)) Ordering.lt (Nat.blt a b)) y)
    x y

theorem lcmp'_eq (x : List ℕ) : ∀ y : List ℕ, lcmp' x y = lcmp x y := by
  induction x with
  | nil => intro y; cases y <;> rfl
  | cons a x ih =>
    intro y
    cases y with
    | nil => rfl
    | cons b y =>
      show @Bool.rec (fun _ => Ordering)
        (@Bool.rec (fun _ => Ordering) (lcmp' x y) Ordering.gt (Nat.blt b a)) Ordering.lt (Nat.blt a b) =
        cond (Nat.blt a b) Ordering.lt (cond (Nat.blt b a) Ordering.gt (lcmp x y))
      rw [ih y]
      cases Nat.blt a b <;> cases Nat.blt b a <;> rfl

noncomputable def has' (t : Tree) (x : List ℕ) : Bool :=
  @BinaryTree.rec (List ℕ) (fun _ => Bool) false
    (fun key _ _ ihl ihr => @Ordering.rec (fun _ => Bool) ihl true ihr (lcmp' x key)) t

theorem has'_eq (t : Tree) (x : List ℕ) : has' t x = thas t x := by
  induction t with
  | nil => rfl
  | node key l r ihl ihr =>
    show @Ordering.rec (fun _ => Bool) (has' l x) true (has' r x) (lcmp' x key) =
      thas (BinaryTree.node key l r) x
    rw [ihl, ihr, lcmp'_eq]
    cases h : lcmp x key <;> rw [thas, h]

noncomputable def lastOK' (P : List ℕ → ℕ → Bool) (prev : Tree) (k : ℕ) (l : List ℕ) : Bool :=
  bor (bor (band (Nat.beq k 0) (bnot (allFinal' l))) (has' prev l)) (bnot (P l k))

theorem lastOK'_eq (P : List ℕ → ℕ → Bool) (prev : Tree) (k : ℕ) (l : List ℕ) : lastOK' P prev k l = lastOK P prev k l := by
  unfold lastOK' lastOK
  rw [bor_eq, bor_eq, band_eq, bnot_eq, bnot_eq, allFinal'_eq, has'_eq]

def covR' (c : ℕ) : Bool := Nat.beq (Nat.land c full) full

def forceN (x : ℕ) (f : ℕ → Bool) : Bool :=
  @Nat.rec (fun _ => Bool) (f 0) (fun p _ => f (Nat.succ p)) x

theorem forceN_eq (x : ℕ) (f : ℕ → Bool) : forceN x f = f x := by
  cases x <;> rfl

def forceL (l : List ℕ) (c : List ℕ → Bool) : Bool :=
  @List.rec ℕ (fun _ => (List ℕ → Bool) → Bool) (fun c => c [])
    (fun x _ ih c => forceN x (fun x' => ih (fun t => c (x' :: t)))) l c

theorem forceL_eq (l : List ℕ) : ∀ c : List ℕ → Bool, forceL l c = c l := by
  induction l with
  | nil => intro c; rfl
  | cons x l ih =>
    intro c
    show forceN x (fun x' => forceL l (fun t => c (x' :: t))) = c (x :: l)
    rw [forceN_eq, ih]

noncomputable def sOK' (P : List ℕ → ℕ → Bool) (prev : Tree) (k : ℕ) (l : List ℕ) (u v w : ℕ) (sz : Bool) (c : ℕ) (ka kb : Bool) : Bool :=
  bor (bor sz (bnot (covR' c))) (forceL (ins' w (filt' ka kb u v l)) (lastOK' P prev k))

theorem sOK'_eq (P : List ℕ → ℕ → Bool) (prev : Tree) (k : ℕ) (l : List ℕ) (u v w : ℕ) (sz : Bool) (c : ℕ) (ka kb : Bool) :
    sOK' P prev k l u v w sz c ka kb = sOK P prev k l u v w sz c ka kb := by
  unfold sOK' sOK
  rw [bor_eq, bor_eq, bnot_eq, forceL_eq, lastOK'_eq, ins'_eq, filt'_eq]
  rfl

def len' (l : List ℕ) : ℕ := @List.rec ℕ (fun _ => ℕ) 0 (fun _ _ ih => Nat.succ ih) l

theorem len'_eq (l : List ℕ) : len' l = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => show Nat.succ (len' l) = _; rw [ih]; rfl

noncomputable def opOK2' (P : List ℕ → ℕ → Bool) (prev : Tree) (k : ℕ) (l : List ℕ) (u ru v rv w c : ℕ) : Bool :=
  band (band (band
    (sOK' P prev k l u v w (Nat.blt (Nat.add k 2) (len' l)) c false false)
    (sOK' P prev k l u v w (Nat.blt (Nat.succ k) (len' l)) (Nat.lor c rv) false true))
    (sOK' P prev k l u v w (Nat.blt (Nat.succ k) (len' l)) (Nat.lor c ru) true false))
    (sOK' P prev k l u v w (Nat.blt k (len' l)) (Nat.lor c (Nat.lor ru rv)) true true)

theorem opOK2'_eq (P : List ℕ → ℕ → Bool) (prev : Tree) (k : ℕ) (l : List ℕ) (u ru v rv w c : ℕ) :
    opOK2' P prev k l u ru v rv w c = opOK2 P prev k l u ru v rv w c := by
  unfold opOK2' opOK2
  simp only [band_eq, sOK'_eq, len'_eq]

noncomputable def opOK' (m : Bool) (P : List ℕ → ℕ → Bool) (prev : Tree) (k : ℕ) (l : List ℕ) (u ru v rv ro w : ℕ) : Bool :=
  bor (bor (blkAny' m w base12) (blkAny' m w l))
    (opOK2' P prev k l u ru v rv w (Nat.lor (rectW' w) ro))

theorem opOK'_eq (m : Bool) (P : List ℕ → ℕ → Bool) (prev : Tree) (k : ℕ) (l : List ℕ) (u ru v rv ro w : ℕ) :
    opOK' m P prev k l u ru v rv ro w = opOK m P prev k l u ru v rv ro w := by
  unfold opOK' opOK
  simp only [bor_eq, blkAny'_eq, opOK2'_eq, rectW'_eq]

noncomputable def pairOK' (m : Bool) (P : List ℕ → ℕ → Bool) (prev : Tree) (k : ℕ) (l : List ℕ) (u v : ℕ) : Bool :=
  band (opOK' m P prev k l u (rectW' u) v (rectW' v) (orEx' u v l) (Nat.land u v))
    (opOK' m P prev k l u (rectW' u) v (rectW' v) (orEx' u v l) (Nat.lor u v))

theorem pairOK'_eq (m : Bool) (P : List ℕ → ℕ → Bool) (prev : Tree) (k : ℕ) (l : List ℕ) (u v : ℕ) :
    pairOK' m P prev k l u v = pairOK m P prev k l u v := by
  unfold pairOK' pairOK
  simp only [band_eq, opOK'_eq, rectW'_eq, orEx'_eq]

def allB' (f : ℕ → Bool) (l : List ℕ) : Bool :=
  @List.rec ℕ (fun _ => Bool) true (fun a _ ih => band (f a) ih) l

theorem allB'_eq (f : ℕ → Bool) (l : List ℕ) : allB' f l = allB f l := by
  induction l with
  | nil => rfl
  | cons a l ih => show band (f a) (allB' f l) = (f a && allB f l); rw [ih, band_eq]

def pairsAll' (f : ℕ → ℕ → Bool) (l : List ℕ) : Bool :=
  @List.rec ℕ (fun _ => Bool) true (fun a t ih => band (allB' (f a) t) ih) l

theorem pairsAll'_eq (f : ℕ → ℕ → Bool) (l : List ℕ) : pairsAll' f l = pairsAll f l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    show band (allB' (f a) l) (pairsAll' f l) = (allB (f a) l && pairsAll f l)
    rw [ih, band_eq, allB'_eq]

noncomputable def expOK' (m : Bool) (P : List ℕ → ℕ → Bool) (prev : Tree) (k : ℕ) (l : List ℕ) : Bool :=
  band (band (sortedB l) (bnot (allFinal' l))) (pairsAll' (pairOK' m P prev k l) l)

theorem expOK'_eq (m : Bool) (P : List ℕ → ℕ → Bool) (prev : Tree) (k : ℕ) (l : List ℕ) :
    expOK' m P prev k l = expOK m P prev k l := by
  unfold expOK' expOK
  have : pairOK' m P prev k l = pairOK m P prev k l := by
    funext u v; exact pairOK'_eq m P prev k l u v
  rw [band_eq, band_eq, bnot_eq, allFinal'_eq, pairsAll'_eq, this]

noncomputable def expFastSub :
    {f : Bool → (List ℕ → ℕ → Bool) → Tree → ℕ → List ℕ → Bool // f = expOK'} := by
  refine ⟨?f, ?h⟩
  case h =>
    delta expOK' pairsAll' allB' pairOK' opOK' opOK2' sOK' len' covR' lastOK' has' lcmp' filt' ins'
      allFinal' orEx' rectW' rect' tb' blkAny' blk' domN' band bor bnot full base12 base10 forceL forceN
    beta_reduce
    exact rfl

noncomputable def expFast : Bool → (List ℕ → ℕ → Bool) → Tree → ℕ → List ℕ → Bool :=
  expFastSub.1

theorem expFast_eq (m : Bool) (P : List ℕ → ℕ → Bool) (prev : Tree) (k : ℕ) :
    expFast m P prev k = expOK m P prev k := by
  funext l
  have : expFast = expOK' := expFastSub.2
  rw [this]
  exact expOK'_eq m P prev k l

theorem level_fast {m : Bool} {P : List ℕ → ℕ → Bool} {prev T : Tree} {k : ℕ}
    (hP : PruneOK m P) (hinv : Inv m prev k)
    (h : tall (expFast m P prev k) T = true) : Inv m T (k + 1) := by
  rw [expFast_eq] at h
  intro x hx
  exact expOK_sound hP hinv (thas_all _ T x h hx)

theorem tall_node (p : List ℕ → Bool) (l r : Tree) (key : List ℕ) (h1 : tall p l = true)
    (h2 : p key = true) (h3 : tall p r = true) : tall p (BinaryTree.node key l r) = true := by
  simp only [tall, h1, h2, h3]; rfl

theorem inv_leaf (m : Bool) : Inv m BinaryTree.nil 0 := by
  intro x hx
  simp [thas] at hx

def NoStart (m : Bool) (n : ℕ) : Prop :=
  ∀ L : Finset ℕ, (∀ x ∈ L, x ∈ base10) → ¬ Reach m L n

theorem start_sound {m : Bool} {prev : Tree} {n : ℕ} (hinv : Inv m prev n)
    (h : subsAll base10 (closed prev n) = true) : NoStart m n := by
  intro L hL
  have hs : (base10.filter (fun x => decide (x ∈ L))).Sublist base10 := List.filter_sublist
  have he : (base10.filter (fun x => decide (x ∈ L))).toFinset = L := by
    ext x
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hL x h, h⟩⟩
  have hnd : (base10.filter (fun x => decide (x ∈ L))).Nodup := List.Nodup.sublist hs (by decide)
  have := closed_sound hnd hinv (subsAll_sub base10 _ h _ hs)
  rw [he] at this
  exact this

inductive ReachH (m : Bool) : Finset ℕ → Finset ℕ → ℕ → Prop
  | done (H : Finset ℕ) (k : ℕ) : ReachH m H {4095} k
  | step (H D : Finset ℕ) (k u v w : ℕ) (ka kb : Bool) :
      u ∈ D → v ∈ D → (w = u &&& v ∨ w = u ||| v) →
      (∀ d ∈ H, blk m w d = false) →
      (∀ d ∈ D, blk m w d = false) → (∀ d ∈ base12, blk m w d = false) →
      ReachH m (insert w H)
        (insert w (D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v)))) k →
      ReachH m H D (k + 1)

theorem ReachH.toReach {m : Bool} {H D : Finset ℕ} {k : ℕ} (h : ReachH m H D k) : Reach m D k := by
  induction h with
  | done H k => exact Reach.done k
  | step H D k u v w ka kb hu hv hw _ hd hb _ ih => exact Reach.step D k u v w ka kb hu hv hw hd hb ih

theorem ReachH.anti {m : Bool} {H D : Finset ℕ} {k : ℕ} (h : ReachH m H D k) :
    ∀ H' : Finset ℕ, H' ⊆ H → ReachH m H' D k := by
  induction h with
  | done H k => intro H' _; exact ReachH.done H' k
  | step H D k u v w ka kb hu hv hw hH hd hb _ ih =>
    intro H' hsub
    exact ReachH.step H' D k u v w ka kb hu hv hw (fun d hd' => hH d (hsub hd')) hd hb
      (ih _ (Finset.insert_subset_insert w hsub))

theorem ReachH.mono {m : Bool} {H D : Finset ℕ} {k : ℕ} (h : ReachH m H D k) :
    ReachH m H D (k + 1) := by
  induction h with
  | done H k => exact ReachH.done _ _
  | step H D k u v w ka kb hu hv hw hH hd hb _ ih =>
    exact ReachH.step H D (k + 1) u v w ka kb hu hv hw hH hd hb ih

theorem ReachH.mono_le {m : Bool} {H D : Finset ℕ} {k k' : ℕ} (hk : k ≤ k') (h : ReachH m H D k) :
    ReachH m H D k' := by
  induction hk with
  | refl => exact h
  | step _ ih => exact ih.mono

theorem ReachH.inv' {m : Bool} {H D : Finset ℕ} {k' : ℕ} (h : ReachH m H D k') : ∀ k : ℕ,
    k' = k + 1 →
    D = {4095} ∨ ∃ (u v w : ℕ) (ka kb : Bool), u ∈ D ∧ v ∈ D ∧ (w = u &&& v ∨ w = u ||| v) ∧
      (∀ d ∈ H, blk m w d = false) ∧
      (∀ d ∈ D, blk m w d = false) ∧ (∀ d ∈ base12, blk m w d = false) ∧
      ReachH m (insert w H)
        (insert w (D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v)))) k := by
  induction h with
  | done H k0 => intro _ _; exact Or.inl rfl
  | step H D k0 u v w ka kb hu hv hw hH hd hb hr _ =>
    intro k hk
    obtain rfl : k0 = k := by omega
    exact Or.inr ⟨u, v, w, ka, kb, hu, hv, hw, hH, hd, hb, hr⟩

inductive Tr (m : Bool) : List ℕ → Prop
  | nil : Tr m []
  | snoc (s : List ℕ) (w : ℕ) : Tr m s → w < 16777216 →
      (∀ d ∈ base12 ++ s, blk m w d = false) →
      (∃ u ∈ base12 ++ s, ∃ v ∈ base12 ++ s, w = u &&& v ∨ w = u ||| v) → Tr m (s ++ [w])

theorem Tr.bound {m : Bool} {s : List ℕ} (h : Tr m s) : ∀ x ∈ s, x < 16777216 := by
  induction h with
  | nil => intro x hx; simp at hx
  | snoc s w _ hw _ _ ih =>
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact ih x hx
    · rw [List.mem_singleton.mp hx]; exact hw

theorem ones_and (v : ℕ) (hv : v < 16777216) : 16777215 &&& v = v := by
  have e : (16777215 : ℕ) = 2 ^ 24 - 1 := by norm_num
  rw [Nat.and_comm, e, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt hv

theorem ones_or (v : ℕ) (hv : v < 16777216) : 16777215 ||| v = 16777215 := by
  have e : (16777215 : ℕ) = 2 ^ 24 - 1 := by norm_num
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, e, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < 24
  · simp [hi]
  · have : v.testBit i = false := by
      apply Nat.testBit_lt_two_pow
      exact lt_of_lt_of_le hv (by
        have : (2 : ℕ) ^ 24 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega)
    simp [hi, this]

theorem absorb (S : List ℕ) (h0 : 0 ∈ S) (h1 : 16777215 ∈ S) (hb : ∀ x ∈ S, x < 16777216)
    (u v : ℕ) (hu : u ∈ S) (hv : v ∈ S) (hz : u = 0 ∨ u = 16777215 ∨ u = v) :
    u &&& v ∈ S ∧ u ||| v ∈ S := by
  rcases hz with rfl | rfl | rfl
  · simpa using ⟨h0, hv⟩
  · rw [ones_and v (hb v hv), ones_or v (hb v hv)]; exact ⟨hv, h1⟩
  · simpa using hu

theorem base12_lt : ∀ x ∈ base12, x < 16777216 := by decide

theorem mem12 {x : ℕ} (h : x ∈ base12) : x = 0 ∨ x = 16777215 ∨ x ∈ base10 := by
  simpa [base12] using h

theorem Tr.reach {m : Bool} {s : List ℕ} (h : Tr m s) : ∀ (L : Finset ℕ) (k : ℕ),
    (∀ x ∈ L, x ∈ base10 ∨ x ∈ s) → ReachH m s.toFinset L k →
    ∃ L0 : Finset ℕ, (∀ x ∈ L0, x ∈ base10) ∧ ReachH m ∅ L0 (k + s.length) := by
  induction h with
  | nil =>
    intro L k hL hR
    exact ⟨L, fun x hx => (hL x hx).resolve_right (by simp), by simpa using hR⟩
  | snoc s w hs hwlt hdom hop ih =>
    intro L k hL hR
    have hlen : k + (s ++ [w]).length = k + s.length + 1 := by simp; omega
    rw [hlen]
    by_cases hwL : w ∈ L
    · obtain ⟨u, hu, v, hv, hw⟩ := hop
      have hne : ∀ x ∈ base12 ++ s, w ≠ x := fun x hx he => by
        have := hdom x hx
        rw [← he, blk_refl] at this
        exact Bool.noConfusion this
      have hbd : ∀ x ∈ base12 ++ s, x < 16777216 := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact base12_lt x hx
        · exact hs.bound x hx
      have h0 : (0 : ℕ) ∈ base12 ++ s := List.mem_append_left _ (by simp [base12])
      have h1 : (16777215 : ℕ) ∈ base12 ++ s := List.mem_append_left _ (by simp [base12])
      have hwS : ¬ (w ∈ base12 ++ s) := fun hm => hne w hm rfl
      have hu0 : ¬ (u = 0 ∨ u = 16777215 ∨ u = v) := fun hz => by
        have := absorb _ h0 h1 hbd u v hu hv hz
        rcases hw with hw | hw
        · exact hwS (hw ▸ this.1)
        · exact hwS (hw ▸ this.2)
      have hv0 : ¬ (v = 0 ∨ v = 16777215) := fun hz => by
        have := absorb _ h0 h1 hbd v u hv hu (by tauto)
        rw [Nat.and_comm, Nat.or_comm] at this
        rcases hw with hw | hw
        · exact hwS (hw ▸ this.1)
        · exact hwS (hw ▸ this.2)
      have hu' : u ∈ base10 ∨ u ∈ s := by
        rcases List.mem_append.mp hu with hx | hx
        · rcases mem12 hx with h | h | h
          · exact absurd (Or.inl h) hu0
          · exact absurd (Or.inr (Or.inl h)) hu0
          · exact Or.inl h
        · exact Or.inr hx
      have hv' : v ∈ base10 ∨ v ∈ s := by
        rcases List.mem_append.mp hv with hx | hx
        · rcases mem12 hx with h | h | h
          · exact absurd (Or.inl h) hv0
          · exact absurd (Or.inr h) hv0
          · exact Or.inl h
        · exact Or.inr hx
      have hwu : w ≠ u := hne u hu
      have hwv : w ≠ v := hne v hv
      have hL' : ∀ x ∈ insert u (insert v (L.erase w)), x ∈ base10 ∨ x ∈ s := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hu'
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hv'
        have hx2 := Finset.mem_erase.mp hx
        rcases hL x hx2.2 with h | h
        · exact Or.inl h
        · rcases List.mem_append.mp h with h | h
          · exact Or.inr h
          · exact absurd (List.mem_singleton.mp h) hx2.1
      have hsub : ∀ x, (x ∈ base10 ∨ x ∈ s) → x ∈ base12 ++ s := by
        intro x hx
        rcases hx with h | h
        · exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
        · exact List.mem_append_right _ h
      have hEq : insert w ((insert u (insert v (L.erase w))).filter
          (fun x => (decide (u ∈ L) = true ∨ x ≠ u) ∧ (decide (v ∈ L) = true ∨ x ≠ v))) = L := by
        ext x
        simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_erase, decide_eq_true_eq]
        constructor
        · rintro (rfl | ⟨hx, h1, h2⟩)
          · exact hwL
          · rcases hx with rfl | rfl | hx
            · exact h1.resolve_right (fun h => h rfl)
            · exact h2.resolve_right (fun h => h rfl)
            · exact hx.2
        · intro hx
          by_cases hxw : x = w
          · exact Or.inl hxw
          · refine Or.inr ⟨Or.inr (Or.inr ⟨hxw, hx⟩), ?_, ?_⟩
            · by_cases hxu : x = u
              · exact Or.inl (hxu ▸ hx)
              · exact Or.inr hxu
            · by_cases hxv : x = v
              · exact Or.inl (hxv ▸ hx)
              · exact Or.inr hxv
      have hT : (s ++ [w]).toFinset = insert w s.toFinset := by
        ext x; simp [or_comm]
      have hR' : ReachH m s.toFinset (insert u (insert v (L.erase w))) (k + 1) := by
        refine ReachH.step _ _ k u v w (decide (u ∈ L)) (decide (v ∈ L)) (by simp) (by simp) hw
          (fun d hd => hdom d (List.mem_append_right _ (List.mem_toFinset.mp hd)))
          (fun d hd => hdom d (hsub d (hL' d hd)))
          (fun d hd => hdom d (List.mem_append_left _ hd)) ?_
        rw [hEq, ← hT]; exact hR
      obtain ⟨L0, hL0, hR0⟩ := ih _ (k + 1) hL' hR'
      refine ⟨L0, hL0, ?_⟩
      have e : k + 1 + s.length = k + s.length + 1 := by omega
      rw [← e]; exact hR0
    · have hL' : ∀ x ∈ L, x ∈ base10 ∨ x ∈ s := by
        intro x hx
        rcases hL x hx with h | h
        · exact Or.inl h
        · rcases List.mem_append.mp h with h | h
          · exact Or.inr h
          · exact absurd (List.mem_singleton.mp h ▸ hx) hwL
      obtain ⟨L0, hL0, hR0⟩ := ih L k hL' (hR.anti _ (by
        intro x hx
        rw [List.mem_toFinset] at hx ⊢
        exact List.mem_append_left _ hx))
      exact ⟨L0, hL0, hR0.mono⟩

def NoStartH (m : Bool) (n : ℕ) : Prop :=
  ∀ L : Finset ℕ, (∀ x ∈ L, x ∈ base10) → ¬ ReachH m ∅ L n

theorem NoStart.toH {m : Bool} {n : ℕ} (h : NoStart m n) : NoStartH m n :=
  fun L hL hR => h L hL hR.toReach

theorem no_trace {m : Bool} {n : ℕ} (h : NoStartH m n) {s : List ℕ}
    (hs : Tr m s) (hlen : s.length ≤ n) : 4095 ∉ s := by
  intro hmem
  obtain ⟨L0, hL0, hR0⟩ := hs.reach {4095} 0
    (fun x hx => Or.inr (Finset.mem_singleton.mp hx ▸ hmem)) (ReachH.done _ 0)
  exact h L0 hL0 (hR0.mono_le (by omega))

def sD (rec : ℕ → List ℕ → Bool) (k : ℕ) (l : List ℕ) (u v w : ℕ) (sz : Bool) (c : ℕ)
    (ka kb : Bool) : Bool :=
  sz || !(covR c) || rec k (w :: l.filter (remF ka kb u v))

def opD2 (rec : ℕ → List ℕ → Bool) (k : ℕ) (l : List ℕ) (u ru v rv w c : ℕ) : Bool :=
  sD rec k l u v w (Nat.blt (Nat.add k 2) l.length) c false false &&
  sD rec k l u v w (Nat.blt (Nat.succ k) l.length) (Nat.lor c rv) false true &&
  sD rec k l u v w (Nat.blt (Nat.succ k) l.length) (Nat.lor c ru) true false &&
  sD rec k l u v w (Nat.blt k l.length) (Nat.lor c (Nat.lor ru rv)) true true

def opD (m : Bool) (rec : ℕ → List ℕ → Bool) (k : ℕ) (l : List ℕ) (u ru v rv ro w : ℕ) : Bool :=
  blkAny m w base12 || blkAny m w l || opD2 rec k l u ru v rv w (Nat.lor (rectW w) ro)

def pairD (m : Bool) (rec : ℕ → List ℕ → Bool) (k : ℕ) (l : List ℕ) (u v : ℕ) : Bool :=
  opD m rec k l u (rectW u) v (rectW v) (orEx u v l) (Nat.land u v) &&
  opD m rec k l u (rectW u) v (rectW v) (orEx u v l) (Nat.lor u v)

def node (m : Bool) (P : List ℕ → ℕ → Bool) (rec : ℕ → List ℕ → Bool) (k : ℕ) (l : List ℕ) : Bool :=
  !(P l k) || (!(allFinal l) && (Nat.beq k 0 || pairsAll (pairD m rec (Nat.pred k) l) l))

theorem ite_p {c : Prop} [Decidable c] (a b : ℕ) (h : c) : (if c then a else b) = a := by
  split
  · rfl
  · contradiction

theorem ite_n {c : Prop} [Decidable c] (a b : ℕ) (h : ¬ c) : (if c then a else b) = b := by
  split
  · contradiction
  · rfl

theorem pw_forall {α : Type} {R : α → α → Prop} (hs : ∀ a b, R a b → R b a) :
    ∀ l : List α, l.Pairwise R → ∀ a ∈ l, ∀ b ∈ l, a ≠ b → R a b := by
  intro l
  induction l with
  | nil => intro _ a ha; simp at ha
  | cons x l ih =>
    intro h a ha b hb hab
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.mp ha with ha' | ha'
    · rcases List.mem_cons.mp hb with hb' | hb'
      · exact absurd (ha'.trans hb'.symm) hab
      · rw [ha']; exact h.1 b hb'
    · rcases List.mem_cons.mp hb with hb' | hb'
      · rw [hb']; exact hs _ _ (h.1 a ha')
      · exact ih h.2 a ha' b hb' hab

theorem kw_step (D D' : Finset ℕ) (u v w : ℕ) (c : ℕ → ℕ → Bool) (f : ℕ → ℕ → ℕ)
    (hu : u ∈ D) (hv : v ∈ D) (huv : u ≠ v) (huD : u ∉ D') (hvD : v ∉ D')
    (hsub : ∀ x ∈ D', x ≠ w → x ∈ D)
    (hf : ∀ e i, e < 12 → 12 ≤ i →
      f e i ∈ D' ∧ (f e i).testBit e = true ∧ (f e i).testBit i = false)
    (hr : ∀ e i e' i', e < 12 → e' < 12 → 12 ≤ i → 12 ≤ i' → f e i = f e' i' → f e i' = f e i)
    (hcu : ∀ e i, w.testBit e = true → w.testBit i = false → c e i = true →
      u.testBit e = true ∧ u.testBit i = false)
    (hcv : ∀ e i, w.testBit e = true → w.testBit i = false → c e i = false →
      v.testBit e = true ∧ v.testBit i = false)
    (hc : ∀ e i e' i', c e i = c e' i' → c e i' = c e i) :
    ∃ g : ℕ → ℕ → ℕ,
      (∀ e i, e < 12 → 12 ≤ i →
        g e i ∈ D ∧ (g e i).testBit e = true ∧ (g e i).testBit i = false) ∧
      (∀ e i e' i', e < 12 → e' < 12 → 12 ≤ i → 12 ≤ i' → g e i = g e' i' → g e i' = g e i) := by
  have hg : ∀ e i, e < 12 → 12 ≤ i → f e i = w →
      ((if f e i = w then (cond (c e i) u v) else f e i) = u ∧ c e i = true) ∨
      ((if f e i = w then (cond (c e i) u v) else f e i) = v ∧ c e i = false) := by
    intro e i _ _ h
    rw [ite_p _ _ (h)]
    cases c e i
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
  refine ⟨fun e i => if f e i = w then (cond (c e i) u v) else f e i, ?_, ?_⟩
  · intro e i he hi
    obtain ⟨h1, h2, h3⟩ := hf e i he hi
    show (if f e i = w then (cond (c e i) u v) else f e i) ∈ D ∧
      (if f e i = w then (cond (c e i) u v) else f e i).testBit e = true ∧
      (if f e i = w then (cond (c e i) u v) else f e i).testBit i = false
    by_cases hw : f e i = w
    · rw [hw] at h2 h3
      rcases hg e i he hi hw with ⟨hx, hcc⟩ | ⟨hx, hcc⟩
      · rw [hx]; exact ⟨hu, hcu e i h2 h3 hcc⟩
      · rw [hx]; exact ⟨hv, hcv e i h2 h3 hcc⟩
    · rw [ite_n _ _ (hw)]; exact ⟨hsub _ h1 hw, h2, h3⟩
  · intro e i e' i' he he' hi hi' heq
    show (if f e i' = w then (cond (c e i') u v) else f e i') =
      (if f e i = w then (cond (c e i) u v) else f e i)
    have heq' : (if f e i = w then (cond (c e i) u v) else f e i) =
      (if f e' i' = w then (cond (c e' i') u v) else f e' i') := heq
    by_cases h1 : f e i = w
    · by_cases h2 : f e' i' = w
      · have h3 : f e i' = w := (hr e i e' i' he he' hi hi' (h1.trans h2.symm)).trans h1
        have hcc : c e i = c e' i' := by
          rcases hg e i he hi h1 with ⟨hx, hx'⟩ | ⟨hx, hx'⟩ <;>
            rcases hg e' i' he' hi' h2 with ⟨hy, hy'⟩ | ⟨hy, hy'⟩
          · rw [hx', hy']
          · exact absurd (hx.symm.trans (heq'.trans hy)) huv
          · exact absurd (hy.symm.trans (heq'.symm.trans hx)) huv
          · rw [hx', hy']
        rw [ite_p _ _ (h3), ite_p _ _ (h1), hc e i e' i' hcc]
      · exfalso
        rw [ite_n _ _ (h2)] at heq'
        have hm := (hf e' i' he' hi').1
        rcases hg e i he hi h1 with ⟨hx, _⟩ | ⟨hx, _⟩
        · exact huD (by rw [← hx, heq']; exact hm)
        · exact hvD (by rw [← hx, heq']; exact hm)
    · by_cases h2 : f e' i' = w
      · exfalso
        rw [ite_n _ _ (h1)] at heq'
        have hm := (hf e i he hi).1
        rcases hg e' i' he' hi' h2 with ⟨hx, _⟩ | ⟨hx, _⟩
        · exact huD (by rw [← hx, ← heq']; exact hm)
        · exact hvD (by rw [← hx, ← heq']; exact hm)
      · have h1n : (if f e i = w then (cond (c e i) u v) else f e i) = f e i := ite_n _ _ h1
        have h2n : (if f e' i' = w then (cond (c e' i') u v) else f e' i') = f e' i' := ite_n _ _ h2
        rw [h1n, h2n] at heq'
        have h3 := hr e i e' i' he he' hi hi' heq'
        have h3n : ¬ f e i' = w := by rw [h3]; exact h1
        rw [h1n, ite_n _ _ (h3n)]
        exact h3

theorem size_lb2 (D : Finset ℕ) (u v : ℕ) (ka kb : Bool) :
    D.card ≤ (D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v))).card +
      (cond ka 0 1 + cond kb 0 1) := by
  have hsub : D ⊆ (D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v))) ∪
      ((cond ka ∅ {u}) ∪ (cond kb ∅ {v})) := by
    intro x hx
    by_cases h1 : x = u <;> by_cases h2 : x = v <;> cases ka <;> cases kb <;> simp_all
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v)))
    ((cond ka ∅ {u}) ∪ (cond kb ∅ {v}))
  have h3 := Finset.card_union_le (cond ka (∅ : Finset ℕ) {u}) (cond kb ∅ {v})
  have h4 : (cond ka (∅ : Finset ℕ) {u}).card = cond ka 0 1 := by cases ka <;> simp
  have h5 : (cond kb (∅ : Finset ℕ) {v}).card = cond kb 0 1 := by cases kb <;> simp
  omega

theorem and_cu (u v e i : ℕ) (h1 : (u &&& v).testBit e = true) (_h2 : (u &&& v).testBit i = false)
    (h3 : (!(u.testBit i)) = true) : u.testBit e = true ∧ u.testBit i = false := by
  rw [Nat.testBit_and] at h1
  cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all

theorem and_cv (u v e i : ℕ) (h1 : (u &&& v).testBit e = true) (h2 : (u &&& v).testBit i = false)
    (h3 : (!(u.testBit i)) = false) : v.testBit e = true ∧ v.testBit i = false := by
  rw [Nat.testBit_and] at h1 h2
  cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all

theorem or_cu (u v e i : ℕ) (_h1 : (u ||| v).testBit e = true) (h2 : (u ||| v).testBit i = false)
    (h3 : u.testBit e = true) : u.testBit e = true ∧ u.testBit i = false := by
  rw [Nat.testBit_or] at h2
  cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all

theorem or_cv (u v e i : ℕ) (h1 : (u ||| v).testBit e = true) (h2 : (u ||| v).testBit i = false)
    (h3 : u.testBit e = false) : v.testBit e = true ∧ v.testBit i = false := by
  rw [Nat.testBit_or] at h1 h2
  cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all

theorem Reach.kw {m : Bool} {D : Finset ℕ} {k : ℕ} (h : Reach m D k) (ht : D.card = k + 1) :
    ∃ f : ℕ → ℕ → ℕ,
      (∀ e i, e < 12 → 12 ≤ i →
        f e i ∈ D ∧ (f e i).testBit e = true ∧ (f e i).testBit i = false) ∧
      (∀ e i e' i', e < 12 → e' < 12 → 12 ≤ i → 12 ≤ i' → f e i = f e' i' → f e i' = f e i) := by
  induction h with
  | done k =>
    refine ⟨fun _ _ => 4095, ?_, ?_⟩
    · intro e i he hi
      refine ⟨by simp, ?_, ?_⟩
      · rw [tb4095]; simpa using he
      · rw [tb4095]; simpa using hi
    · intros; rfl
  | step D k u v w ka kb hu hv hw hd hb hR ih =>
    have hwD : w ∉ D := fun hm => by
      have := hd w hm
      rw [blk_refl] at this
      exact Bool.noConfusion this
    have hwu : w ≠ u := fun h => hwD (h ▸ hu)
    have hwv : w ≠ v := fun h => hwD (h ▸ hv)
    have huv : u ≠ v := by
      rintro rfl
      rcases hw with hw | hw
      · rw [Nat.and_self] at hw; exact hwu hw
      · rw [Nat.or_self] at hw; exact hwu hw
    have hwF : w ∉ D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v)) :=
      fun hm => hwD (Finset.mem_of_mem_filter _ hm)
    have hkk : ka = false ∧ kb = false := by
      have h1 := hR.card
      rw [Finset.card_insert_of_notMem hwF] at h1
      have h2 := size_lb2 D u v ka kb
      generalize (D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v))).card = c at h1 h2
      cases ka <;> cases kb
      · exact ⟨rfl, rfl⟩
      · exfalso
        have h2' : D.card ≤ c + (1 + 0) := h2
        omega
      · exfalso
        have h2' : D.card ≤ c + (0 + 1) := h2
        omega
      · exfalso
        have h2' : D.card ≤ c + (0 + 0) := h2
        omega
    obtain ⟨rfl, rfl⟩ := hkk
    have h1 := hR.card
    rw [Finset.card_insert_of_notMem hwF] at h1
    have h2 : D.card ≤ (D.filter
        (fun x => (false = true ∨ x ≠ u) ∧ (false = true ∨ x ≠ v))).card + (1 + 1) :=
      size_lb2 D u v false false
    have hc : (insert w (D.filter
        (fun x => (false = true ∨ x ≠ u) ∧ (false = true ∨ x ≠ v)))).card = k + 1 := by
      rw [Finset.card_insert_of_notMem hwF]; omega
    obtain ⟨f, hf, hr⟩ := ih hc
    have huD : u ∉ insert w (D.filter
        (fun x => (false = true ∨ x ≠ u) ∧ (false = true ∨ x ≠ v))) := by
      intro hm
      rcases Finset.mem_insert.mp hm with h | h
      · exact hwu h.symm
      · have := (Finset.mem_filter.mp h).2.1
        simp at this
    have hvD : v ∉ insert w (D.filter
        (fun x => (false = true ∨ x ≠ u) ∧ (false = true ∨ x ≠ v))) := by
      intro hm
      rcases Finset.mem_insert.mp hm with h | h
      · exact hwv h.symm
      · have := (Finset.mem_filter.mp h).2.2
        simp at this
    have hsub : ∀ x ∈ insert w (D.filter
        (fun x => (false = true ∨ x ≠ u) ∧ (false = true ∨ x ≠ v))), x ≠ w → x ∈ D := by
      intro x hx hxw
      rcases Finset.mem_insert.mp hx with h | h
      · exact absurd h hxw
      · exact Finset.mem_of_mem_filter _ h
    rcases hw with rfl | rfl
    · exact kw_step D _ u v (u &&& v) (fun _ i => !(u.testBit i)) f hu hv huv huD hvD hsub hf hr
        (fun e i h1 h2 h3 => and_cu u v e i h1 h2 h3) (fun e i h1 h2 h3 => and_cv u v e i h1 h2 h3)
        (fun e i e' i' h => h.symm)
    · exact kw_step D _ u v (u ||| v) (fun e _ => u.testBit e) f hu hv huv huD hvD hsub hf hr
        (fun e i h1 h2 h3 => or_cu u v e i h1 h2 h3) (fun e i h1 h2 h3 => or_cv u v e i h1 h2 h3)
        (fun e i e' i' _ => rfl)

theorem tb_land (a b q : ℕ) : (Nat.land a b).testBit q = (a.testBit q && b.testBit q) :=
  Nat.testBit_and a b q

theorem tb_lor (a b q : ℕ) : (Nat.lor a b).testBit q = (a.testBit q || b.testBit q) :=
  Nat.testBit_or a b q

theorem tb_xor (a b q : ℕ) : (Nat.xor a b).testBit q = Bool.xor (a.testBit q) (b.testBit q) :=
  Nat.testBit_xor a b q

theorem full_tb (q : ℕ) : full.testBit q = decide (q < 144) := by
  rw [full_eq, Nat.testBit_two_pow_sub_one]

theorem land_sub (h a : ℕ) (H : ∀ q, h.testBit q = true → a.testBit q = true) :
    Nat.land h a = h := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [tb_land]
  cases hh : h.testBit q
  · rfl
  · rw [H q hh]; rfl

theorem land_disj (a h : ℕ) (H : ∀ q, a.testBit q = true → h.testBit q = true → False) :
    Nat.land a h = 0 := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [tb_land, Nat.zero_testBit]
  cases ha : a.testBit q
  · rfl
  · cases hh : h.testBit q
    · rfl
    · exact (H q ha hh).elim

def orS (x s : ℕ) : ℕ := Nat.lor x (Nat.shiftRight x s)

def orSL (x s : ℕ) : ℕ := Nat.lor x (Nat.shiftLeft x s)

theorem orS_tb (x s q : ℕ) : (orS x s).testBit q = (x.testBit q || x.testBit (s + q)) := by
  show (x ||| x >>> s).testBit q = _
  rw [Nat.testBit_or, Nat.testBit_shiftRight]

theorem orSL_tb (x s q : ℕ) :
    (orSL x s).testBit q = (x.testBit q || (decide (s ≤ q) && x.testBit (q - s))) := by
  show (x ||| x <<< s).testBit q = _
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft, ge_iff_le]

theorem orS_ex (k p x n s : ℕ)
    (hx : ∀ q, x.testBit q = true → ∃ j, j < n ∧ p.testBit (k * j + q) = true) (q : ℕ)
    (h : (orS x (k * s)).testBit q = true) : ∃ j, j < n + s ∧ p.testBit (k * j + q) = true := by
  rw [orS_tb, Bool.or_eq_true] at h
  rcases h with h | h
  · obtain ⟨j, hj, hp⟩ := hx q h
    exact ⟨j, by omega, hp⟩
  · obtain ⟨j, hj, hp⟩ := hx _ h
    refine ⟨j + s, by omega, ?_⟩
    rw [Nat.mul_add, Nat.add_assoc]; exact hp

theorem orSL_ex (k p x n s : ℕ)
    (hx : ∀ q, x.testBit q = true → ∃ j, j < n ∧ k * j ≤ q ∧ p.testBit (q - k * j) = true)
    (q : ℕ) (h : (orSL x (k * s)).testBit q = true) :
    ∃ j, j < n + s ∧ k * j ≤ q ∧ p.testBit (q - k * j) = true := by
  rw [orSL_tb, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with h | ⟨hs, h⟩
  · obtain ⟨j, hj, hq, hp⟩ := hx q h
    exact ⟨j, by omega, hq, hp⟩
  · obtain ⟨j, hj, hq, hp⟩ := hx _ h
    have e : q - k * (j + s) = q - k * s - k * j := by rw [Nat.mul_add]; omega
    refine ⟨j + s, by omega, ?_, ?_⟩
    · rw [Nat.mul_add]; omega
    · rw [e]; exact hp

def rowM : ℕ := 5445847423328601499764522166702896582657

theorem rowM_tb (q : ℕ) (h : rowM.testBit q = true) : q < 144 ∧ q % 12 = 0 := by
  have hlt : q < 144 := by
    by_contra hq
    have h0 : rowM.testBit q = false := by
      apply Nat.testBit_lt_two_pow
      have h1 : rowM < 2 ^ 144 := by norm_num [rowM]
      have h2 : (2 : ℕ) ^ 144 ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [h0] at h
    exact Bool.noConfusion h
  have hall : ∀ q : ℕ, q < 144 → rowM.testBit q = true → q % 12 = 0 := by decide +kernel
  exact ⟨hlt, hall q hlt h⟩

def rowsOf (p : ℕ) : ℕ := Nat.land (orS (orS (orS (orS p 6) 3) 1) 1) rowM

def colsOf (p : ℕ) : ℕ := Nat.land (orS (orS (orS (orS p 96) 48) 24) 12) 4095

def hullC (p : ℕ) : ℕ :=
  Nat.land (orSL (orSL (orSL (orSL (rowsOf p) 6) 3) 1) 1)
    (orSL (orSL (orSL (orSL (colsOf p) 96) 48) 24) 12)

def hull (p : ℕ) : ℕ := hullC (Nat.land p full)

theorem rowsOf_tb (p q : ℕ) (h : (rowsOf p).testBit q = true) :
    (q < 144 ∧ q % 12 = 0) ∧ ∃ j, j < 12 ∧ p.testBit (j + q) = true := by
  unfold rowsOf at h
  rw [tb_land, Bool.and_eq_true] at h
  refine ⟨rowM_tb q h.2, ?_⟩
  have h0 : ∀ q, p.testBit q = true → ∃ j, j < 1 ∧ p.testBit (1 * j + q) = true :=
    fun q hq => ⟨0, by norm_num, by simpa using hq⟩
  have h1 := orS_ex 1 p _ 1 6 h0
  have h2 := orS_ex 1 p _ _ 3 h1
  have h3 := orS_ex 1 p _ _ 1 h2
  have h4 := orS_ex 1 p _ _ 1 h3
  obtain ⟨j, hj, hp⟩ := h4 q h.1
  exact ⟨j, by omega, by simpa using hp⟩

theorem colsOf_tb (p q : ℕ) (h : (colsOf p).testBit q = true) :
    q < 12 ∧ ∃ j, j < 16 ∧ p.testBit (12 * j + q) = true := by
  unfold colsOf at h
  rw [tb_land, Bool.and_eq_true, tb4095, decide_eq_true_eq] at h
  refine ⟨h.2, ?_⟩
  have h0 : ∀ q, p.testBit q = true → ∃ j, j < 1 ∧ p.testBit (12 * j + q) = true :=
    fun q hq => ⟨0, by norm_num, by simpa using hq⟩
  have h1 := orS_ex 12 p _ 1 8 h0
  have h2 := orS_ex 12 p _ _ 4 h1
  have h3 := orS_ex 12 p _ _ 2 h2
  have h4 := orS_ex 12 p _ _ 1 h3
  obtain ⟨j, hj, hp⟩ := h4 q h.1
  exact ⟨j, by omega, hp⟩

theorem hullC_spec (p : ℕ) (hp : ∀ q, p.testBit q = true → q < 144) (q : ℕ)
    (h : (hullC p).testBit q = true) :
    q < 144 ∧ ∃ i e', i < 12 ∧ e' < 12 ∧ p.testBit (12 * (q / 12) + i) = true ∧
      p.testBit (12 * e' + q % 12) = true := by
  unfold hullC at h
  rw [tb_land, Bool.and_eq_true] at h
  obtain ⟨hR, hC⟩ := h
  have r0 : ∀ q, (rowsOf p).testBit q = true →
      ∃ j, j < 1 ∧ 1 * j ≤ q ∧ (rowsOf p).testBit (q - 1 * j) = true :=
    fun q hq => ⟨0, by norm_num, by omega, by simpa using hq⟩
  have r1 := orSL_ex 1 (rowsOf p) _ 1 6 r0
  have r2 := orSL_ex 1 (rowsOf p) _ _ 3 r1
  have r3 := orSL_ex 1 (rowsOf p) _ _ 1 r2
  have r4 := orSL_ex 1 (rowsOf p) _ _ 1 r3
  obtain ⟨j, hj, hjq, hr⟩ := r4 q hR
  obtain ⟨⟨hb, hm⟩, i, hi, hpi⟩ := rowsOf_tb p _ hr
  have c0 : ∀ q, (colsOf p).testBit q = true →
      ∃ j, j < 1 ∧ 12 * j ≤ q ∧ (colsOf p).testBit (q - 12 * j) = true :=
    fun q hq => ⟨0, by norm_num, by omega, by simpa using hq⟩
  have c1 := orSL_ex 12 (colsOf p) _ 1 8 c0
  have c2 := orSL_ex 12 (colsOf p) _ _ 4 c1
  have c3 := orSL_ex 12 (colsOf p) _ _ 2 c2
  have c4 := orSL_ex 12 (colsOf p) _ _ 1 c3
  obtain ⟨j', hj', hjq', hc⟩ := c4 q hC
  obtain ⟨hlt, e', he', hpe⟩ := colsOf_tb p _ hc
  have e1 : i + (q - 1 * j) = 12 * (q / 12) + i := by omega
  have e2 : q - 12 * j' = q % 12 := by omega
  rw [e1] at hpi
  rw [e2] at hpe
  have hb' := hp _ hpe
  exact ⟨by omega, i, e', hi, by omega, hpi, hpe⟩

theorem hull_spec (p q : ℕ) (h : (hull p).testBit q = true) :
    q < 144 ∧ ∃ i e', i < 12 ∧ e' < 12 ∧ p.testBit (12 * (q / 12) + i) = true ∧
      p.testBit (12 * e' + q % 12) = true := by
  have hp : ∀ q, (Nat.land p full).testBit q = true → q < 144 := by
    intro q hq
    rw [tb_land, full_tb, Bool.and_eq_true, decide_eq_true_eq] at hq
    exact hq.2
  obtain ⟨h1, i, e', hi, he, ha, hb⟩ := hullC_spec _ hp q h
  rw [tb_land, Bool.and_eq_true] at ha hb
  exact ⟨h1, i, e', hi, he, ha.1, hb.1⟩

def tw : List ℕ → ℕ → ℕ → ℕ
  | [], _, t => t
  | a :: l, o, t => tw l (Nat.lor o a) (Nat.lor t (Nat.land o a))

def priv (t a : ℕ) : ℕ := hull (Nat.land a (Nat.xor t full))

def hullsOK (t : ℕ) : List ℕ → ℕ → Bool
  | [], _ => true
  | a :: l, acc => Nat.beq (Nat.land (priv t a) a) (priv t a) &&
      (Nat.beq (Nat.land acc (priv t a)) 0 && hullsOK t l (Nat.lor acc (priv t a)))

def avOK1 (as : List ℕ) : Bool := hullsOK (tw as 0 0) as 0

def orL : List ℕ → ℕ
  | [] => 0
  | a :: l => Nat.lor a (orL l)

def rectOK1 (l : List ℕ) : Bool := avOK1 (l.map rectW)

def IsRect (R : ℕ → Prop) : Prop :=
  ∀ e i e' i' : ℕ, e < 12 → i < 12 → e' < 12 → i' < 12 →
    R (12 * e + i) → R (12 * e' + i') → R (12 * e + i')

structure Part (zs : List ((ℕ → Prop) × ℕ)) : Prop where
  rect : ∀ z ∈ zs, IsRect z.1
  bnd : ∀ z ∈ zs, ∀ q, z.1 q → q < 144
  disj : zs.Pairwise (fun z z' => ∀ q, z.1 q → z'.1 q → False)
  cov : ∀ q, q < 144 → ∃ z ∈ zs, z.1 q
  sub : ∀ z ∈ zs, ∀ q, z.1 q → z.2.testBit q = true

theorem tw_spec (q : ℕ) : ∀ (as : List ℕ) (o t : ℕ), (tw as o t).testBit q = false →
    t.testBit q = false ∧ (o.testBit q = true → ∀ a ∈ as, a.testBit q = false) ∧
    as.Pairwise (fun a b => ¬ (a.testBit q = true ∧ b.testBit q = true)) := by
  intro as
  induction as with
  | nil => intro o t h; exact ⟨h, fun _ a ha => by simp at ha, List.Pairwise.nil⟩
  | cons a l ih =>
    intro o t h
    obtain ⟨h1, h2, h3⟩ := ih (Nat.lor o a) (Nat.lor t (Nat.land o a)) h
    rw [tb_lor, Bool.or_eq_false_iff, tb_land] at h1
    refine ⟨h1.1, ?_, ?_⟩
    · intro ho b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · have h4 := h1.2
        rw [ho] at h4
        simpa using h4
      · exact h2 (by rw [tb_lor, ho]; rfl) b hb
    · refine List.pairwise_cons.mpr ⟨?_, h3⟩
      intro b hb hab
      have h4 := h2 (by rw [tb_lor, hab.1]; simp) b hb
      rw [h4] at hab
      exact Bool.noConfusion hab.2

theorem priv_in {zs : List ((ℕ → Prop) × ℕ)} (hP : Part zs) : ∀ z ∈ zs, ∀ q,
    (priv (tw (zs.map Prod.snd) 0 0) z.2).testBit q = true → z.1 q := by
  intro z hz q hq
  obtain ⟨hq144, i, e', hi, he', ha, hb⟩ := hull_spec _ q hq
  have key : ∀ x, x < 144 →
      (Nat.land z.2 (Nat.xor (tw (zs.map Prod.snd) 0 0) full)).testBit x = true → z.1 x := by
    intro x hx hbit
    rw [tb_land, tb_xor, full_tb, Bool.and_eq_true] at hbit
    obtain ⟨hzx, ht⟩ := hbit
    have ht' : (tw (zs.map Prod.snd) 0 0).testBit x = false := by simpa [hx] using ht
    obtain ⟨_, _, hpw⟩ := tw_spec x _ 0 0 ht'
    rw [List.pairwise_map] at hpw
    obtain ⟨z', hz', hzq⟩ := hP.cov x hx
    by_cases hzz : z' = z
    · rw [← hzz]; exact hzq
    · exfalso
      exact pw_forall (fun a b h h' => h ⟨h'.2, h'.1⟩) zs hpw z' hz' z hz hzz
        ⟨hP.sub z' hz' x hzq, hzx⟩
  have h1 := key _ (by omega) ha
  have h2 := key _ (by omega) hb
  have h3 := hP.rect z hz (q / 12) i e' (q % 12) (by omega) hi he' (Nat.mod_lt _ (by norm_num))
    h1 h2
  rwa [Nat.div_add_mod] at h3

theorem hullsOK_sound (t : ℕ) : ∀ (zs : List ((ℕ → Prop) × ℕ)) (acc : ℕ),
    (∀ z ∈ zs, ∀ q, (priv t z.2).testBit q = true → z.1 q) →
    (∀ z ∈ zs, ∀ q, z.1 q → z.2.testBit q = true) →
    zs.Pairwise (fun z z' => ∀ q, z.1 q → z'.1 q → False) →
    (∀ q, acc.testBit q = true → ∀ z ∈ zs, ¬ z.1 q) →
    hullsOK t (zs.map Prod.snd) acc = true := by
  intro zs
  induction zs with
  | nil => intros; rfl
  | cons z zs ih =>
    intro acc hh hs hd ha
    rw [List.pairwise_cons] at hd
    have hz := hh z List.mem_cons_self
    have e1 := land_sub _ _ (fun q hq => hs z List.mem_cons_self q (hz q hq))
    have e2 := land_disj acc (priv t z.2) (fun q h1 h2 => ha q h1 z List.mem_cons_self (hz q h2))
    have e3 := ih (Nat.lor acc (priv t z.2)) (fun z' hz' => hh z' (List.mem_cons_of_mem _ hz'))
      (fun z' hz' => hs z' (List.mem_cons_of_mem _ hz')) hd.2 (fun q hq z' hz' hz'q => by
        rw [tb_lor, Bool.or_eq_true] at hq
        rcases hq with hq | hq
        · exact ha q hq z' (List.mem_cons_of_mem _ hz') hz'q
        · exact hd.1 z' hz' q (hz q hq) hz'q)
    show (Nat.beq (Nat.land (priv t z.2) z.2) (priv t z.2) &&
      (Nat.beq (Nat.land acc (priv t z.2)) 0 &&
        hullsOK t (zs.map Prod.snd) (Nat.lor acc (priv t z.2)))) = true
    rw [e1, e2, e3, Nat.beq_refl]
    rfl

theorem avOK1_sound {zs : List ((ℕ → Prop) × ℕ)} (hP : Part zs) :
    avOK1 (zs.map Prod.snd) = true :=
  hullsOK_sound _ zs 0 (priv_in hP) hP.sub hP.disj (fun q hq => by simp at hq)

theorem orL_tb' (q : ℕ) : ∀ as : List ℕ, ∀ a ∈ as, a.testBit q = true →
    (orL as).testBit q = true := by
  intro as
  induction as with
  | nil => intro a ha; simp at ha
  | cons b l ih =>
    intro a ha h
    show (Nat.lor b (orL l)).testBit q = true
    rw [tb_lor]
    rcases List.mem_cons.mp ha with rfl | ha
    · rw [h]; rfl
    · rw [ih a ha h]; simp

theorem Part.covR {zs : List ((ℕ → Prop) × ℕ)} (hP : Part zs) :
    covR (orL (zs.map Prod.snd)) = true := by
  apply covR_of
  intro q hq
  obtain ⟨z, hz, hzq⟩ := hP.cov q hq
  exact orL_tb' q _ z.2 (List.mem_map.mpr ⟨z, hz, rfl⟩) (hP.sub z hz q hzq)

theorem part_of_reach {m : Bool} {l : List ℕ} {k : ℕ} (hnd : l.Nodup) (hlen : l.length = k + 1)
    (hR : Reach m l.toFinset k) :
    ∃ zs : List ((ℕ → Prop) × ℕ), zs.map Prod.snd = l.map rectW ∧ Part zs := by
  have hc : l.toFinset.card = k + 1 := by rw [List.toFinset_card_of_nodup hnd, hlen]
  obtain ⟨f, hf, hr⟩ := hR.kw hc
  refine ⟨l.map (fun w => ((fun q => q < 144 ∧ f (q / 12) (12 + q % 12) = w), rectW w)), ?_, ?_⟩
  · rw [List.map_map]
    rfl
  · constructor
    · intro z hz
      obtain ⟨w, _, rfl⟩ := List.mem_map.mp hz
      intro e i e' i' he hi he' hi' h1 h2
      have h1' : f ((12 * e + i) / 12) (12 + (12 * e + i) % 12) = w := h1.2
      have h2' : f ((12 * e' + i') / 12) (12 + (12 * e' + i') % 12) = w := h2.2
      have e1 : (12 * e + i) / 12 = e := by omega
      have e2 : (12 * e + i) % 12 = i := by omega
      have e3 : (12 * e' + i') / 12 = e' := by omega
      have e4 : (12 * e' + i') % 12 = i' := by omega
      have e5 : (12 * e + i') / 12 = e := by omega
      have e6 : (12 * e + i') % 12 = i' := by omega
      rw [e1, e2] at h1'
      rw [e3, e4] at h2'
      show 12 * e + i' < 144 ∧ f ((12 * e + i') / 12) (12 + (12 * e + i') % 12) = w
      rw [e5, e6]
      exact ⟨by omega, (hr e (12 + i) e' (12 + i') he he' (by omega) (by omega)
        (h1'.trans h2'.symm)).trans h1'⟩
    · intro z hz q hq
      obtain ⟨w, _, rfl⟩ := List.mem_map.mp hz
      exact hq.1
    · rw [List.pairwise_map]
      exact List.Pairwise.imp (fun hne q h1 h2 => hne (h1.2.symm.trans h2.2)) hnd
    · intro q hq
      have h := (hf (q / 12) (12 + q % 12) (by omega) (by omega)).1
      exact ⟨_, List.mem_map.mpr ⟨_, List.mem_toFinset.mp h, rfl⟩, hq, rfl⟩
    · intro z hz q hq
      obtain ⟨w, _, rfl⟩ := List.mem_map.mp hz
      have hq1 : q < 144 := hq.1
      have hq2 : f (q / 12) (12 + q % 12) = w := hq.2
      have h := hf (q / 12) (12 + q % 12) (by omega) (by omega)
      rw [hq2] at h
      have h3 := rectW_tb w (q / 12) (q % 12) (by omega) (Nat.mod_lt _ (by norm_num)) h.2.1 h.2.2
      rwa [Nat.div_add_mod] at h3

theorem rectOK1_sound {m : Bool} {l : List ℕ} {k : ℕ} (hnd : l.Nodup) (hlen : l.length = k + 1)
    (hR : Reach m l.toFinset k) : rectOK1 l = true := by
  obtain ⟨zs, he, hP⟩ := part_of_reach hnd hlen hR
  unfold rectOK1
  rw [← he]
  exact avOK1_sound hP

def rectP1 (l : List ℕ) (k : ℕ) : Bool := !(Nat.beq l.length (Nat.succ k)) || rectOK1 l

theorem rectP1_ok (m : Bool) : PruneOK m rectP1 := by
  intro l k hnd hR
  unfold rectP1
  cases h : Nat.beq l.length (Nat.succ k)
  · rfl
  · rw [rectOK1_sound hnd (Nat.eq_of_beq_eq_true h) hR]
    rfl

def tw' (l : List ℕ) : ℕ → ℕ → ℕ :=
  @List.rec ℕ (fun _ => ℕ → ℕ → ℕ) (fun _ t => t)
    (fun a _ ih o t => ih (Nat.lor o a) (Nat.lor t (Nat.land o a))) l

theorem tw'_eq (l : List ℕ) : ∀ o t : ℕ, tw' l o t = tw l o t := by
  induction l with
  | nil => intro o t; rfl
  | cons a l ih =>
    intro o t
    show tw' l (Nat.lor o a) (Nat.lor t (Nat.land o a)) = tw l (Nat.lor o a) (Nat.lor t (Nat.land o a))
    exact ih _ _

def hullsOK' (t : ℕ) (l : List ℕ) : ℕ → Bool :=
  @List.rec ℕ (fun _ => ℕ → Bool) (fun _ => true)
    (fun a _ ih acc => (fun h => band (Nat.beq (Nat.land h a) h)
      (band (Nat.beq (Nat.land acc h) 0) (ih (Nat.lor acc h)))) (priv t a)) l

theorem hullsOK'_eq (t : ℕ) (l : List ℕ) : ∀ acc : ℕ, hullsOK' t l acc = hullsOK t l acc := by
  induction l with
  | nil => intro acc; rfl
  | cons a l ih =>
    intro acc
    show band (Nat.beq (Nat.land (priv t a) a) (priv t a))
      (band (Nat.beq (Nat.land acc (priv t a)) 0) (hullsOK' t l (Nat.lor acc (priv t a)))) =
      (Nat.beq (Nat.land (priv t a) a) (priv t a) &&
        (Nat.beq (Nat.land acc (priv t a)) 0 && hullsOK t l (Nat.lor acc (priv t a))))
    rw [ih, band_eq, band_eq]

def mapW' (l : List ℕ) : List ℕ :=
  @List.rec ℕ (fun _ => List ℕ) [] (fun x _ ih => rectW' x :: ih) l

theorem mapW'_eq (l : List ℕ) : mapW' l = l.map rectW := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    show rectW' x :: mapW' l = rectW x :: l.map rectW
    rw [ih, rectW'_eq]

def rectP1' (l : List ℕ) (k : ℕ) : Bool :=
  bor (bnot (Nat.beq (len' l) (Nat.succ k)))
    ((fun as => hullsOK' (tw' as 0 0) as 0) (mapW' l))

theorem rectP1'_eq (l : List ℕ) (k : ℕ) : rectP1' l k = rectP1 l k := by
  show bor (bnot (Nat.beq (len' l) (Nat.succ k))) (hullsOK' (tw' (mapW' l) 0 0) (mapW' l) 0) =
    (!(Nat.beq l.length (Nat.succ k)) || hullsOK (tw (l.map rectW) 0 0) (l.map rectW) 0)
  rw [bor_eq, bnot_eq, len'_eq, mapW'_eq, hullsOK'_eq, tw'_eq]

theorem rectP1'_ok (m : Bool) : PruneOK m rectP1' := by
  intro l k hnd hR
  rw [rectP1'_eq]
  exact rectP1_ok m l k hnd hR

def Pc (x e i : ℕ) : Prop := x.testBit e = true ∧ x.testBit i = false

def IsRect2 (S : ℕ → ℕ → Prop) : Prop := ∀ e i e' i' : ℕ, S e i → S e' i' → S e i'

theorem pc_rect (x : ℕ) : IsRect2 (Pc x) := fun _ _ _ _ h1 h2 => ⟨h1.1, h2.2⟩

structure KS (D : Finset ℕ) (j : ℕ) (f : ℕ → ℕ → ℕ) (env : ℕ → ℕ → ℕ → Prop) (c : ℕ → ℕ)
    (Pi : ℕ → ℕ → ℕ → Prop) : Prop where
  own : ∀ e i, e < 12 → 12 ≤ i → f e i ∈ D ∧ env (f e i) e i
  envR : ∀ x ∈ D, IsRect2 (env x)
  envP : ∀ x ∈ D, ∀ e i, env x e i → Pc x e i
  s1 : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → c x = c y → ∀ e i, env x e i → env y e i → False
  s2 : ∀ x ∈ D, 1 ≤ c x → ∀ e i, env x e i → Pi (c x) e i
  piR : ∀ n, IsRect2 (Pi n)
  s3 : ∀ n e i, 1 ≤ n → Pi n e i → ∃ y ∈ D, 1 ≤ c y ∧ c y ≤ n ∧ Pc y e i
  lab : ∀ x ∈ D, c x ≤ j

theorem ks_done : KS {4095} 0 (fun _ _ => 4095) (fun _ e i => Pc 4095 e i) (fun _ => 0)
    (fun _ _ _ => False) := by
  constructor
  · intro e i he hi
    refine ⟨by simp, ?_, ?_⟩
    · rw [tb4095]; simpa using he
    · rw [tb4095]; simpa using hi
  · intro x _; exact pc_rect 4095
  · intro x hx e i h
    rw [Finset.mem_singleton.mp hx]; exact h
  · intro x hx y hy hxy
    exact absurd ((Finset.mem_singleton.mp hx).trans (Finset.mem_singleton.mp hy).symm) hxy
  · intro x _ h; omega
  · intro n e i e' i' h; exact h.elim
  · intro n e i _ h; exact h.elim
  · intro x _; exact le_rfl

def shiftL (c : ℕ → ℕ) (x y : ℕ) : ℕ := if y = x then 1 else if c y = 0 then 0 else c y + 1

theorem shiftL_self (c : ℕ → ℕ) (x : ℕ) : shiftL c x x = 1 := by
  unfold shiftL; exact ite_p _ _ rfl

theorem shiftL_ne (c : ℕ → ℕ) (x y : ℕ) (h : y ≠ x) :
    (c y = 0 ∧ shiftL c x y = 0) ∨ (1 ≤ c y ∧ shiftL c x y = c y + 1) := by
  unfold shiftL
  rw [ite_n _ _ h]
  by_cases h0 : c y = 0
  · rw [ite_p _ _ h0]; exact Or.inl ⟨h0, rfl⟩
  · rw [ite_n _ _ h0]; exact Or.inr ⟨by omega, rfl⟩

theorem KS.promote {D : Finset ℕ} {j : ℕ} {f : ℕ → ℕ → ℕ} {env : ℕ → ℕ → ℕ → Prop} {c : ℕ → ℕ}
    {Pi : ℕ → ℕ → ℕ → Prop} (h : KS D j f env c Pi) (x : ℕ) (hxD : x ∈ D) :
    KS D (j + 1) f (fun y e i => (y = x ∧ Pc x e i) ∨ (y ≠ x ∧ env y e i)) (shiftL c x)
      (fun n e i => (n = 1 ∧ Pc x e i) ∨ (2 ≤ n ∧ Pi (n - 1) e i)) := by
  constructor
  · intro e i he hi
    obtain ⟨h1, h2⟩ := h.own e i he hi
    refine ⟨h1, ?_⟩
    by_cases hx : f e i = x
    · exact Or.inl ⟨hx, hx ▸ h.envP _ h1 e i h2⟩
    · exact Or.inr ⟨hx, h2⟩
  · intro y hy e i e' i' h1 h2
    rcases h1 with ⟨hx, h1⟩ | ⟨hx, h1⟩ <;> rcases h2 with ⟨hx', h2⟩ | ⟨hx', h2⟩
    · exact Or.inl ⟨hx, pc_rect x e i e' i' h1 h2⟩
    · exact absurd hx hx'
    · exact absurd hx' hx
    · exact Or.inr ⟨hx, h.envR y hy e i e' i' h1 h2⟩
  · intro y hy e i h1
    rcases h1 with ⟨hx, h1⟩ | ⟨hx, h1⟩
    · rw [hx]; exact h1
    · exact h.envP y hy e i h1
  · intro y hy z hz hyz hc e i h1 h2
    by_cases hyx : y = x
    · have hzx : z ≠ x := fun hh => hyz (hyx.trans hh.symm)
      rw [hyx, shiftL_self] at hc
      rcases shiftL_ne c x z hzx with ⟨_, h3⟩ | ⟨_, h3⟩ <;> omega
    · by_cases hzx : z = x
      · rw [hzx, shiftL_self] at hc
        rcases shiftL_ne c x y hyx with ⟨_, h3⟩ | ⟨_, h3⟩ <;> omega
      · have hcc : c y = c z := by
          rcases shiftL_ne c x y hyx with ⟨_, h3⟩ | ⟨_, h3⟩ <;>
            rcases shiftL_ne c x z hzx with ⟨_, h4⟩ | ⟨_, h4⟩ <;> omega
        rcases h1 with ⟨hx, _⟩ | ⟨_, h1⟩
        · exact hyx hx
        · rcases h2 with ⟨hx, _⟩ | ⟨_, h2⟩
          · exact hzx hx
          · exact h.s1 y hy z hz hyz hcc e i h1 h2
  · intro y hy hc e i h1
    rcases h1 with ⟨hx, h1⟩ | ⟨hx, h1⟩
    · rw [hx, shiftL_self]; exact Or.inl ⟨rfl, h1⟩
    · rcases shiftL_ne c x y hx with ⟨_, h3⟩ | ⟨h4, h3⟩
      · omega
      · rw [h3]
        refine Or.inr ⟨by omega, ?_⟩
        rw [Nat.add_sub_cancel]
        exact h.s2 y hy h4 e i h1
  · intro n e i e' i' h1 h2
    rcases h1 with ⟨hn, h1⟩ | ⟨hn, h1⟩ <;> rcases h2 with ⟨hn', h2⟩ | ⟨hn', h2⟩
    · exact Or.inl ⟨hn, pc_rect x e i e' i' h1 h2⟩
    · omega
    · omega
    · exact Or.inr ⟨hn, h.piR _ e i e' i' h1 h2⟩
  · intro n e i hn h1
    rcases h1 with ⟨hn1, h1⟩ | ⟨hn2, h1⟩
    · exact ⟨x, hxD, by rw [shiftL_self], by rw [shiftL_self]; omega, h1⟩
    · obtain ⟨y, hy, h3, h4, h5⟩ := h.s3 (n - 1) e i (by omega) h1
      by_cases hyx : y = x
      · exact ⟨y, hy, by rw [hyx, shiftL_self], by rw [hyx, shiftL_self]; omega, h5⟩
      · rcases shiftL_ne c x y hyx with ⟨_, h6⟩ | ⟨_, h6⟩
        · omega
        · exact ⟨y, hy, by omega, by omega, h5⟩
  · intro y hy
    have := h.lab y hy
    by_cases hyx : y = x
    · rw [hyx, shiftL_self]; omega
    · rcases shiftL_ne c x y hyx with ⟨_, h6⟩ | ⟨_, h6⟩ <;> omega

def Prom (env : ℕ → ℕ → ℕ → Prop) (c : ℕ → ℕ) (w x : ℕ) : Prop :=
  (∀ e i, Pc x e i → env x e i) ∧ 1 ≤ c x ∧ (1 ≤ c w → c x ≤ c w)

theorem prom_self (env : ℕ → ℕ → ℕ → Prop) (c : ℕ → ℕ) (w x : ℕ) :
    Prom (fun y e i => (y = x ∧ Pc x e i) ∨ (y ≠ x ∧ env y e i)) (shiftL c x) w x := by
  refine ⟨fun e i h => Or.inl ⟨rfl, h⟩, by rw [shiftL_self], fun h => by rw [shiftL_self]; exact h⟩

theorem prom_other (env : ℕ → ℕ → ℕ → Prop) (c : ℕ → ℕ) (w x y : ℕ) (hyx : y ≠ x) (hwx : w ≠ x)
    (h : Prom env c w y) :
    Prom (fun y e i => (y = x ∧ Pc x e i) ∨ (y ≠ x ∧ env y e i)) (shiftL c x) w y := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun e i hp => Or.inr ⟨hyx, h1 e i hp⟩, ?_, ?_⟩
  · rcases shiftL_ne c x y hyx with ⟨_, h6⟩ | ⟨_, h6⟩ <;> omega
  · intro hw
    rcases shiftL_ne c x y hyx with ⟨_, h6⟩ | ⟨_, h6⟩ <;>
      rcases shiftL_ne c x w hwx with ⟨_, h7⟩ | ⟨_, h7⟩ <;> omega

theorem ks_prom {D' : Finset ℕ} {j : ℕ} {f : ℕ → ℕ → ℕ} {env : ℕ → ℕ → ℕ → Prop} {c : ℕ → ℕ}
    {Pi : ℕ → ℕ → ℕ → Prop} (hK : KS D' j f env c Pi) (u v w : ℕ) (_huw : u ≠ w) (hvw : v ≠ w)
    (huv : u ≠ v) (ka kb : Bool) (hua : u ∈ D' ↔ ka = true) (hvb : v ∈ D' ↔ kb = true) :
    ∃ (j2 : ℕ) (env2 : ℕ → ℕ → ℕ → Prop) (c2 : ℕ → ℕ) (Pi2 : ℕ → ℕ → ℕ → Prop),
      KS D' j2 f env2 c2 Pi2 ∧ j2 = j + (cond ka 1 0 + cond kb 1 0) ∧
      (u ∈ D' → Prom env2 c2 w u) ∧ (v ∈ D' → Prom env2 c2 w v) := by
  cases ka <;> cases kb
  · exact ⟨j, env, c, Pi, hK, rfl, fun h => Bool.noConfusion (hua.mp h),
      fun h => Bool.noConfusion (hvb.mp h)⟩
  · exact ⟨_, _, _, _, hK.promote v (hvb.mpr rfl), rfl, fun h => Bool.noConfusion (hua.mp h),
      fun _ => prom_self env c w v⟩
  · exact ⟨_, _, _, _, hK.promote u (hua.mpr rfl), rfl, fun _ => prom_self env c w u,
      fun h => Bool.noConfusion (hvb.mp h)⟩
  · exact ⟨_, _, _, _, (hK.promote u (hua.mpr rfl)).promote v (hvb.mpr rfl), rfl,
      fun _ => prom_other _ _ w v u huv (Ne.symm hvw) (prom_self env c w u),
      fun _ => prom_self _ _ w v⟩

theorem KS.step {D D' : Finset ℕ} {j : ℕ} {f : ℕ → ℕ → ℕ} {env : ℕ → ℕ → ℕ → Prop} {c : ℕ → ℕ}
    {Pi : ℕ → ℕ → ℕ → Prop} (h : KS D' j f env c Pi) (u v w : ℕ) (hu : u ∈ D) (hv : v ∈ D)
    (huv : u ≠ v) (hwD : w ∉ D) (hw : w ∈ D') (hD' : ∀ x ∈ D', x ≠ w → x ∈ D)
    (cc : ℕ → ℕ → Bool)
    (hcu : ∀ e i, Pc w e i → cc e i = true → Pc u e i)
    (hcv : ∀ e i, Pc w e i → cc e i = false → Pc v e i)
    (hcr : ∀ (b : Bool) (e i e' i' : ℕ), cc e i = b → cc e' i' = b → cc e i' = b)
    (hku : u ∈ D' → Prom env c w u) (hkv : v ∈ D' → Prom env c w v) :
    ∃ (f2 : ℕ → ℕ → ℕ) (env2 : ℕ → ℕ → ℕ → Prop) (c2 : ℕ → ℕ), KS D j f2 env2 c2 Pi := by
  have hc2a : ∀ x, x ∈ D' → (if x ∈ D' then c x else c w) = c x := fun x hx => ite_p _ _ hx
  have hc2b : ∀ x, x ∉ D' → (if x ∈ D' then c x else c w) = c w := fun x hx => ite_n _ _ hx
  refine ⟨fun e i => if f e i = w then cond (cc e i) u v else f e i,
    fun x e i => (x ∈ D' ∧ env x e i) ∨
      (x ∉ D' ∧ env w e i ∧ ((x = u ∧ cc e i = true) ∨ (x = v ∧ cc e i = false))),
    fun x => if x ∈ D' then c x else c w, ?_⟩
  constructor
  · intro e i he hi
    obtain ⟨h1, h2⟩ := h.own e i he hi
    show (if f e i = w then cond (cc e i) u v else f e i) ∈ D ∧
      (((if f e i = w then cond (cc e i) u v else f e i) ∈ D' ∧
        env (if f e i = w then cond (cc e i) u v else f e i) e i) ∨
      ((if f e i = w then cond (cc e i) u v else f e i) ∉ D' ∧ env w e i ∧
        (((if f e i = w then cond (cc e i) u v else f e i) = u ∧ cc e i = true) ∨
         ((if f e i = w then cond (cc e i) u v else f e i) = v ∧ cc e i = false))))
    by_cases hfw : f e i = w
    · rw [ite_p _ _ hfw]
      rw [hfw] at h2
      have hpw := h.envP w hw e i h2
      cases hcc : cc e i
      · refine ⟨hv, ?_⟩
        by_cases hvD : v ∈ D'
        · exact Or.inl ⟨hvD, (hkv hvD).1 e i (hcv e i hpw hcc)⟩
        · exact Or.inr ⟨hvD, h2, Or.inr ⟨rfl, rfl⟩⟩
      · refine ⟨hu, ?_⟩
        by_cases huD : u ∈ D'
        · exact Or.inl ⟨huD, (hku huD).1 e i (hcu e i hpw hcc)⟩
        · exact Or.inr ⟨huD, h2, Or.inl ⟨rfl, rfl⟩⟩
    · rw [ite_n _ _ hfw]
      exact ⟨hD' _ h1 hfw, Or.inl ⟨h1, h2⟩⟩
  · intro x _ e i e' i' h1 h2
    rcases h1 with ⟨hx, h1⟩ | ⟨hx, h1, h1c⟩ <;> rcases h2 with ⟨hx', h2⟩ | ⟨hx', h2, h2c⟩
    · exact Or.inl ⟨hx, h.envR x hx e i e' i' h1 h2⟩
    · exact absurd hx hx'
    · exact absurd hx' hx
    · refine Or.inr ⟨hx, h.envR w hw e i e' i' h1 h2, ?_⟩
      rcases h1c with ⟨hxu, hc1⟩ | ⟨hxv, hc1⟩ <;> rcases h2c with ⟨hxu', hc2⟩ | ⟨hxv', hc2⟩
      · exact Or.inl ⟨hxu, hcr true e i e' i' hc1 hc2⟩
      · exact absurd (hxu.symm.trans hxv') huv
      · exact absurd (hxu'.symm.trans hxv) huv
      · exact Or.inr ⟨hxv, hcr false e i e' i' hc1 hc2⟩
  · intro x _ e i h1
    rcases h1 with ⟨hx, h1⟩ | ⟨_, h1, h1c⟩
    · exact h.envP x hx e i h1
    · have hpw := h.envP w hw e i h1
      rcases h1c with ⟨hxu, hc1⟩ | ⟨hxv, hc1⟩
      · rw [hxu]; exact hcu e i hpw hc1
      · rw [hxv]; exact hcv e i hpw hc1
  · intro x hx y hy hxy hc e i h1 h2
    have hxw : x ≠ w := fun hh => hwD (hh ▸ hx)
    have hyw : y ≠ w := fun hh => hwD (hh ▸ hy)
    have hc' : (if x ∈ D' then c x else c w) = (if y ∈ D' then c y else c w) := hc
    rcases h1 with ⟨hx', h1⟩ | ⟨hx', h1, h1c⟩ <;> rcases h2 with ⟨hy', h2⟩ | ⟨hy', h2, h2c⟩
    · rw [hc2a x hx', hc2a y hy'] at hc'
      exact h.s1 x hx' y hy' hxy hc' e i h1 h2
    · rw [hc2a x hx', hc2b y hy'] at hc'
      exact h.s1 x hx' w hw hxw hc' e i h1 h2
    · rw [hc2b x hx', hc2a y hy'] at hc'
      exact h.s1 w hw y hy' (Ne.symm hyw) hc' e i h1 h2
    · rcases h1c with ⟨hxu, hc1⟩ | ⟨hxv, hc1⟩ <;> rcases h2c with ⟨hyu, hc2⟩ | ⟨hyv, hc2⟩
      · exact hxy (hxu.trans hyu.symm)
      · rw [hc1] at hc2; exact Bool.noConfusion hc2
      · rw [hc1] at hc2; exact Bool.noConfusion hc2
      · exact hxy (hxv.trans hyv.symm)
  · intro x _ hc e i h1
    have hc' : 1 ≤ (if x ∈ D' then c x else c w) := hc
    show Pi (if x ∈ D' then c x else c w) e i
    rcases h1 with ⟨hx', h1⟩ | ⟨hx', h1, _⟩
    · rw [hc2a x hx'] at hc' ⊢
      exact h.s2 x hx' hc' e i h1
    · rw [hc2b x hx'] at hc' ⊢
      exact h.s2 w hw hc' e i h1
  · exact h.piR
  · intro n e i hn h1
    obtain ⟨y, hy, h3, h4, h5⟩ := h.s3 n e i hn h1
    show ∃ y ∈ D, 1 ≤ (if y ∈ D' then c y else c w) ∧ (if y ∈ D' then c y else c w) ≤ n ∧ Pc y e i
    by_cases hyw : y = w
    · rw [hyw] at h3 h4 h5
      cases hcc : cc e i
      · refine ⟨v, hv, ?_, ?_, hcv e i h5 hcc⟩
        · by_cases hvD : v ∈ D'
          · rw [hc2a v hvD]; exact (hkv hvD).2.1
          · rw [hc2b v hvD]; exact h3
        · by_cases hvD : v ∈ D'
          · rw [hc2a v hvD]; exact le_trans ((hkv hvD).2.2 h3) h4
          · rw [hc2b v hvD]; exact h4
      · refine ⟨u, hu, ?_, ?_, hcu e i h5 hcc⟩
        · by_cases huD : u ∈ D'
          · rw [hc2a u huD]; exact (hku huD).2.1
          · rw [hc2b u huD]; exact h3
        · by_cases huD : u ∈ D'
          · rw [hc2a u huD]; exact le_trans ((hku huD).2.2 h3) h4
          · rw [hc2b u huD]; exact h4
    · exact ⟨y, hD' y hy hyw, by rw [hc2a y hy]; exact h3, by rw [hc2a y hy]; exact h4, h5⟩
  · intro x _
    show (if x ∈ D' then c x else c w) ≤ j
    by_cases hx' : x ∈ D'
    · rw [hc2a x hx']; exact h.lab x hx'
    · rw [hc2b x hx']; exact h.lab w hw

theorem cond_sum (b : Bool) : (cond b 1 0 : ℕ) + cond b 0 1 = 1 := by cases b <;> rfl

theorem Reach.ks {m : Bool} {D : Finset ℕ} {k : ℕ} (h : Reach m D k) :
    ∃ (j : ℕ) (f : ℕ → ℕ → ℕ) (env : ℕ → ℕ → ℕ → Prop) (c : ℕ → ℕ) (Pi : ℕ → ℕ → ℕ → Prop),
      KS D j f env c Pi ∧ j + D.card ≤ k + 1 := by
  induction h with
  | done k => exact ⟨0, _, _, _, _, ks_done, by simp⟩
  | step D k u v w ka kb hu hv hw hd hb hR ih =>
    obtain ⟨j, f, env, c, Pi, hK, hj⟩ := ih
    have hwD : w ∉ D := fun hm => by
      have := hd w hm
      rw [blk_refl] at this
      exact Bool.noConfusion this
    have hwu : w ≠ u := fun h => hwD (h ▸ hu)
    have hwv : w ≠ v := fun h => hwD (h ▸ hv)
    have huv : u ≠ v := by
      rintro rfl
      rcases hw with hw | hw
      · rw [Nat.and_self] at hw; exact hwu hw
      · rw [Nat.or_self] at hw; exact hwu hw
    have hwF : w ∉ D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v)) :=
      fun hm => hwD (Finset.mem_of_mem_filter _ hm)
    rw [Finset.card_insert_of_notMem hwF] at hj
    have hsz := size_lb2 D u v ka kb
    have hua : u ∈ insert w (D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v))) ↔
        ka = true := by
      rw [Finset.mem_insert, Finset.mem_filter]
      constructor
      · rintro (h | ⟨_, h, _⟩)
        · exact absurd h.symm hwu
        · exact h.resolve_right (fun hh => hh rfl)
      · intro h
        exact Or.inr ⟨hu, Or.inl h, Or.inr huv⟩
    have hvb : v ∈ insert w (D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v))) ↔
        kb = true := by
      rw [Finset.mem_insert, Finset.mem_filter]
      constructor
      · rintro (h | ⟨_, _, h⟩)
        · exact absurd h.symm hwv
        · exact h.resolve_right (fun hh => hh rfl)
      · intro h
        exact Or.inr ⟨hv, Or.inr (Ne.symm huv), Or.inl h⟩
    obtain ⟨j2, env2, c2, Pi2, hK2, hj2, hpu, hpv⟩ :=
      ks_prom hK u v w (Ne.symm hwu) (Ne.symm hwv) huv ka kb hua hvb
    have hD' : ∀ x ∈ insert w (D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v))),
        x ≠ w → x ∈ D := by
      intro x hx hxw
      rcases Finset.mem_insert.mp hx with h | h
      · exact absurd h hxw
      · exact Finset.mem_of_mem_filter _ h
    have hfin : ∃ (f2 : ℕ → ℕ → ℕ) (env3 : ℕ → ℕ → ℕ → Prop) (c3 : ℕ → ℕ),
        KS D j2 f2 env3 c3 Pi2 := by
      rcases hw with rfl | rfl
      · exact hK2.step u v (u &&& v) hu hv huv hwD (Finset.mem_insert_self _ _) hD'
          (fun _ i => !(u.testBit i))
          (fun e i h1 h3 => and_cu u v e i h1.1 h1.2 h3)
          (fun e i h1 h3 => and_cv u v e i h1.1 h1.2 h3)
          (fun b e i e' i' _ h2 => h2) hpu hpv
      · exact hK2.step u v (u ||| v) hu hv huv hwD (Finset.mem_insert_self _ _) hD'
          (fun e _ => u.testBit e)
          (fun e i h1 h3 => or_cu u v e i h1.1 h1.2 h3)
          (fun e i h1 h3 => or_cv u v e i h1.1 h1.2 h3)
          (fun b e i e' i' h1 _ => h1) hpu hpv
    obtain ⟨f2, env3, c3, hK3⟩ := hfin
    refine ⟨j2, f2, env3, c3, Pi2, hK3, ?_⟩
    have e1 := cond_sum ka
    have e2 := cond_sum kb
    omega

structure MS (l : List ℕ) (j : ℕ) (Env : ℕ → ℕ → Prop) (c : ℕ → ℕ) (PiM : ℕ → ℕ → Prop) : Prop where
  own : ∀ q, q < 144 → ∃ x ∈ l, Env x q
  envR : ∀ x ∈ l, IsRect (Env x)
  envB : ∀ x ∈ l, ∀ q, Env x q → q < 144 ∧ (rectW x).testBit q = true
  s1 : ∀ x ∈ l, ∀ y ∈ l, x ≠ y → c x = c y → ∀ q, Env x q → Env y q → False
  s2 : ∀ x ∈ l, 1 ≤ c x → ∀ q, Env x q → PiM (c x) q
  piR : ∀ n, IsRect (PiM n)
  s3 : ∀ n q, 1 ≤ n → PiM n q → ∃ y ∈ l, 1 ≤ c y ∧ c y ≤ n ∧ (rectW y).testBit q = true
  lab : ∀ x ∈ l, c x ≤ j

theorem rect_conv (S : ℕ → ℕ → Prop) (hS : IsRect2 S) :
    IsRect (fun q => q < 144 ∧ S (q / 12) (12 + q % 12)) := by
  intro e i e' i' he hi he' hi' h1 h2
  have h1' : S ((12 * e + i) / 12) (12 + (12 * e + i) % 12) := h1.2
  have h2' : S ((12 * e' + i') / 12) (12 + (12 * e' + i') % 12) := h2.2
  have e1 : (12 * e + i) / 12 = e := by omega
  have e2 : (12 * e + i) % 12 = i := by omega
  have e3 : (12 * e' + i') / 12 = e' := by omega
  have e4 : (12 * e' + i') % 12 = i' := by omega
  have e5 : (12 * e + i') / 12 = e := by omega
  have e6 : (12 * e + i') % 12 = i' := by omega
  rw [e1, e2] at h1'
  rw [e3, e4] at h2'
  show 12 * e + i' < 144 ∧ S ((12 * e + i') / 12) (12 + (12 * e + i') % 12)
  rw [e5, e6]
  exact ⟨by omega, hS _ _ _ _ h1' h2'⟩

theorem pc_bit (x q : ℕ) (hq : q < 144) (h : Pc x (q / 12) (12 + q % 12)) :
    (rectW x).testBit q = true := by
  have h3 := rectW_tb x (q / 12) (q % 12) (by omega) (Nat.mod_lt _ (by norm_num)) h.1 h.2
  rwa [Nat.div_add_mod] at h3

theorem KS.toMS {l : List ℕ} {j : ℕ} {f : ℕ → ℕ → ℕ} {env : ℕ → ℕ → ℕ → Prop} {c : ℕ → ℕ}
    {Pi : ℕ → ℕ → ℕ → Prop} (h : KS l.toFinset j f env c Pi) :
    MS l j (fun x q => q < 144 ∧ env x (q / 12) (12 + q % 12)) c
      (fun n q => q < 144 ∧ Pi n (q / 12) (12 + q % 12)) := by
  constructor
  · intro q hq
    obtain ⟨h1, h2⟩ := h.own (q / 12) (12 + q % 12) (by omega) (by omega)
    exact ⟨_, List.mem_toFinset.mp h1, hq, h2⟩
  · intro x hx
    exact rect_conv _ (h.envR x (List.mem_toFinset.mpr hx))
  · intro x hx q hq
    exact ⟨hq.1, pc_bit x q hq.1 (h.envP x (List.mem_toFinset.mpr hx) _ _ hq.2)⟩
  · intro x hx y hy hxy hc q h1 h2
    exact h.s1 x (List.mem_toFinset.mpr hx) y (List.mem_toFinset.mpr hy) hxy hc _ _ h1.2 h2.2
  · intro x hx hc q h1
    exact ⟨h1.1, h.s2 x (List.mem_toFinset.mpr hx) hc _ _ h1.2⟩
  · intro n
    exact rect_conv _ (h.piR n)
  · intro n q hn h1
    obtain ⟨y, hy, h3, h4, h5⟩ := h.s3 n _ _ hn h1.2
    exact ⟨y, List.mem_toFinset.mp hy, h3, h4, pc_bit y q h1.1 h5⟩
  · intro x hx
    exact h.lab x (List.mem_toFinset.mpr hx)

theorem MS.priv_env {l : List ℕ} {j : ℕ} {Env : ℕ → ℕ → Prop} {c : ℕ → ℕ} {PiM : ℕ → ℕ → Prop}
    (hM : MS l j Env c PiM) : ∀ y ∈ l, ∀ q,
    (priv (tw (l.map rectW) 0 0) (rectW y)).testBit q = true → Env y q := by
  intro y hy q hq
  obtain ⟨hq144, i, e', hi, he', ha, hb⟩ := hull_spec _ q hq
  have key : ∀ x, x < 144 →
      (Nat.land (rectW y) (Nat.xor (tw (l.map rectW) 0 0) full)).testBit x = true → Env y x := by
    intro x hx hbit
    rw [tb_land, tb_xor, full_tb, Bool.and_eq_true] at hbit
    obtain ⟨hzx, ht⟩ := hbit
    have ht' : (tw (l.map rectW) 0 0).testBit x = false := by simpa [hx] using ht
    obtain ⟨_, _, hpw⟩ := tw_spec x _ 0 0 ht'
    rw [List.pairwise_map] at hpw
    obtain ⟨z, hz, hzq⟩ := hM.own x hx
    by_cases hzz : z = y
    · rw [← hzz]; exact hzq
    · exfalso
      exact pw_forall (fun a b h h' => h ⟨h'.2, h'.1⟩) l hpw z hz y hy hzz
        ⟨(hM.envB z hz x hzq).2, hzx⟩
  have h1 := key _ (by omega) ha
  have h2 := key _ (by omega) hb
  have h3 := hM.envR y hy (q / 12) i e' (q % 12) (by omega) hi he' (Nat.mod_lt _ (by norm_num))
    h1 h2
  rwa [Nat.div_add_mod] at h3

def ValidLab (l : List ℕ) (K : ℕ) (c : ℕ → ℕ) : Prop :=
  (∀ x ∈ l, c x ≤ K) ∧
  (∀ x ∈ l, ∀ y ∈ l, x ≠ y → c x = c y →
    Nat.land (priv (tw (l.map rectW) 0 0) (rectW x)) (priv (tw (l.map rectW) 0 0) (rectW y)) = 0) ∧
  (∀ i U : ℕ, 1 ≤ i →
    (∀ q, U.testBit q = true →
      ∃ x ∈ l, c x = i ∧ (priv (tw (l.map rectW) 0 0) (rectW x)).testBit q = true) →
    ∀ q, (hull U).testBit q = true → ∃ y ∈ l, 1 ≤ c y ∧ c y ≤ i ∧ (rectW y).testBit q = true) ∧
  (∀ x ∈ l, ∀ q, (priv (tw (l.map rectW) 0 0) (rectW x)).testBit q = true →
    (rectW x).testBit q = true)

theorem MS.validLab {l : List ℕ} {j : ℕ} {Env : ℕ → ℕ → Prop} {c : ℕ → ℕ} {PiM : ℕ → ℕ → Prop}
    (hM : MS l j Env c PiM) (K : ℕ) (hK : j ≤ K) : ValidLab l K c := by
  refine ⟨fun x hx => le_trans (hM.lab x hx) hK, ?_, ?_, ?_⟩
  · intro x hx y hy hxy hc
    exact land_disj _ _ (fun q h1 h2 =>
      hM.s1 x hx y hy hxy hc q (hM.priv_env x hx q h1) (hM.priv_env y hy q h2))
  · intro i U hi hU q hq
    obtain ⟨_, a, e', ha, he', h1, h2⟩ := hull_spec _ q hq
    obtain ⟨x1, hx1, hc1, hb1⟩ := hU _ h1
    obtain ⟨x2, hx2, hc2, hb2⟩ := hU _ h2
    have hp1 := hM.s2 x1 hx1 (by omega) _ (hM.priv_env x1 hx1 _ hb1)
    have hp2 := hM.s2 x2 hx2 (by omega) _ (hM.priv_env x2 hx2 _ hb2)
    rw [hc1] at hp1
    rw [hc2] at hp2
    have h3 := hM.piR i (q / 12) a e' (q % 12) (by omega) ha he' (Nat.mod_lt _ (by norm_num))
      hp1 hp2
    rw [Nat.div_add_mod] at h3
    exact hM.s3 i q hi h3
  · intro x hx q hq
    exact (hM.envB x hx q (hM.priv_env x hx q hq)).2

theorem reach_validLab {m : Bool} {l : List ℕ} {k : ℕ} (hnd : l.Nodup) (hR : Reach m l.toFinset k) :
    ∃ c : ℕ → ℕ, ValidLab l (Nat.sub (Nat.succ k) l.length) c := by
  obtain ⟨j, f, env, c, Pi, hK, hj⟩ := hR.ks
  rw [List.toFinset_card_of_nodup hnd] at hj
  exact ⟨c, hK.toMS.validLab _ (by
    show j ≤ (k + 1) - l.length
    omega)⟩

def fld (x i : ℕ) : ℕ := Nat.land (Nat.shiftRight x (Nat.mul 144 i)) full

def put (x i v : ℕ) : ℕ := Nat.lor x (Nat.shiftLeft v (Nat.mul 144 i))

def subM (h c : ℕ) : Bool := Nat.beq (Nat.land h c) h

def chkA (bc hs cs K : ℕ) : ℕ → ℕ → Bool
  | 0, _ => true
  | n + 1, pre =>
    subM (fld hs (Nat.sub K n)) (Nat.lor bc (Nat.lor pre (fld cs (Nat.sub K n)))) &&
    chkA bc hs cs K n (Nat.lor pre (fld cs (Nat.sub K n)))

def tryL (K bc a h : ℕ) (cont : ℕ → ℕ → ℕ → Bool) (us hs cs : ℕ) : ℕ → Bool
  | 0 => false
  | n + 1 =>
    (Nat.beq (Nat.land (fld us (Nat.sub K n)) h) 0 &&
      (chkA bc (put hs (Nat.sub K n) (hull (Nat.lor (fld us (Nat.sub K n)) h)))
          (put cs (Nat.sub K n) a) K K 0 &&
        cont (put us (Nat.sub K n) h)
          (put hs (Nat.sub K n) (hull (Nat.lor (fld us (Nat.sub K n)) h)))
          (put cs (Nat.sub K n) a))) ||
    tryL K bc a h cont us hs cs n

def orA : List ℕ → ℕ
  | [] => 0
  | it :: r => Nat.lor (fld it 0) (orA r)

def go (K base : ℕ) : List ℕ → ℕ → ℕ → ℕ → Bool
  | [] => fun _ _ _ => true
  | it :: rest => fun us hs cs =>
    tryL K (Nat.lor base (orA rest)) (fld it 0) (fld it 1) (go K base rest) us hs cs (Nat.succ K)

def vs (t t2 : ℕ) : List ℕ → List ℕ
  | [] => []
  | a :: l => cond (Nat.beq (Nat.land (priv t a) t2) 0) (vs t t2 l)
      (put (Nat.land a full) 1 (priv t a) :: vs t t2 l)

def fcov (t t2 : ℕ) : List ℕ → ℕ
  | [] => 0
  | a :: l => cond (Nat.beq (Nat.land (priv t a) t2) 0) (Nat.lor a (fcov t t2 l)) (fcov t t2 l)

def degI (x : ℕ) : List ℕ → ℕ
  | [] => 0
  | y :: l => cond (Nat.beq (Nat.land (fld y 1) (fld x 1)) 0) (degI x l) (Nat.succ (degI x l))

def insD (all : List ℕ) (x : ℕ) : List ℕ → List ℕ
  | [] => [x]
  | y :: l => cond (Nat.blt (degI y all) (degI x all)) (x :: y :: l) (y :: insD all x l)

def sortD (all : List ℕ) : List ℕ → List ℕ
  | [] => []
  | x :: l => insD all x (sortD all l)

theorem insD_perm (all : List ℕ) (x : ℕ) : ∀ l : List ℕ, (insD all x l).Perm (x :: l) := by
  intro l
  induction l with
  | nil => exact List.Perm.refl _
  | cons y l ih =>
    unfold insD
    cases Nat.blt (degI y all) (degI x all)
    · exact (List.Perm.cons y ih).trans (List.Perm.swap x y l)
    · exact List.Perm.refl _

theorem sortD_perm (all : List ℕ) : ∀ l : List ℕ, (sortD all l).Perm l := by
  intro l
  induction l with
  | nil => exact List.Perm.refl _
  | cons x l ih => exact (insD_perm all x _).trans (List.Perm.cons x ih)

def classP3 (K t t2 : ℕ) (as : List ℕ) : Bool :=
  go K (fcov t t2 as)
    (cond (Nat.blt 1 K) (sortD (vs t t2 as) (vs t t2 as)) (vs t t2 as)) 0 0 0

def classP2 (K : ℕ) (as : List ℕ) (t : ℕ) : Bool := classP3 K t (tw (as.map (priv t)) 0 0) as

def classP (l : List ℕ) (k : ℕ) : Bool :=
  classP2 (Nat.sub (Nat.succ k) l.length) (l.map rectW) (tw (l.map rectW) 0 0)

def chkA' (bc hs cs K n : ℕ) : ℕ → Bool :=
  @Nat.rec (fun _ => ℕ → Bool) (fun _ => true)
    (fun n ih pre => band (subM (fld hs (Nat.sub K n)) (Nat.lor bc (Nat.lor pre (fld cs (Nat.sub K n)))))
      (ih (Nat.lor pre (fld cs (Nat.sub K n))))) n

theorem chkA'_eq (bc hs cs K n : ℕ) : ∀ pre : ℕ, chkA' bc hs cs K n pre = chkA bc hs cs K n pre := by
  induction n with
  | zero => intro pre; rfl
  | succ n ih =>
    intro pre
    show band (subM (fld hs (Nat.sub K n)) (Nat.lor bc (Nat.lor pre (fld cs (Nat.sub K n)))))
      (chkA' bc hs cs K n (Nat.lor pre (fld cs (Nat.sub K n)))) =
      (subM (fld hs (Nat.sub K n)) (Nat.lor bc (Nat.lor pre (fld cs (Nat.sub K n)))) &&
        chkA bc hs cs K n (Nat.lor pre (fld cs (Nat.sub K n))))
    rw [ih, band_eq]

def tryL' (K bc a h : ℕ) (cont : ℕ → ℕ → ℕ → Bool) (us hs cs n : ℕ) : Bool :=
  @Nat.rec (fun _ => Bool) false
    (fun n ih => bor
      (band (Nat.beq (Nat.land (fld us (Nat.sub K n)) h) 0)
        (band (chkA' bc (put hs (Nat.sub K n) (hull (Nat.lor (fld us (Nat.sub K n)) h)))
            (put cs (Nat.sub K n) a) K K 0)
          (cont (put us (Nat.sub K n) h)
            (put hs (Nat.sub K n) (hull (Nat.lor (fld us (Nat.sub K n)) h)))
            (put cs (Nat.sub K n) a))))
      ih) n

theorem tryL'_eq (K bc a h : ℕ) (cont : ℕ → ℕ → ℕ → Bool) (us hs cs n : ℕ) :
    tryL' K bc a h cont us hs cs n = tryL K bc a h cont us hs cs n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show bor
      (band (Nat.beq (Nat.land (fld us (Nat.sub K n)) h) 0)
        (band (chkA' bc (put hs (Nat.sub K n) (hull (Nat.lor (fld us (Nat.sub K n)) h)))
            (put cs (Nat.sub K n) a) K K 0)
          (cont (put us (Nat.sub K n) h)
            (put hs (Nat.sub K n) (hull (Nat.lor (fld us (Nat.sub K n)) h)))
            (put cs (Nat.sub K n) a))))
      (tryL' K bc a h cont us hs cs n) = tryL K bc a h cont us hs cs (n + 1)
    rw [ih, bor_eq, band_eq, band_eq, chkA'_eq]
    rfl

def orA' (l : List ℕ) : ℕ := @List.rec ℕ (fun _ => ℕ) 0 (fun it _ ih => Nat.lor (fld it 0) ih) l

theorem orA'_eq (l : List ℕ) : orA' l = orA l := by
  induction l with
  | nil => rfl
  | cons it r ih => show Nat.lor (fld it 0) (orA' r) = Nat.lor (fld it 0) (orA r); rw [ih]

def go' (K base : ℕ) (l : List ℕ) : ℕ → ℕ → ℕ → Bool :=
  @List.rec ℕ (fun _ => ℕ → ℕ → ℕ → Bool) (fun _ _ _ => true)
    (fun it rest ih us hs cs =>
      tryL' K (Nat.lor base (orA' rest)) (fld it 0) (fld it 1) ih us hs cs (Nat.succ K)) l

theorem go'_eq (K base : ℕ) (l : List ℕ) : go' K base l = go K base l := by
  induction l with
  | nil => rfl
  | cons it rest ih =>
    funext us hs cs
    show tryL' K (Nat.lor base (orA' rest)) (fld it 0) (fld it 1) (go' K base rest) us hs cs
      (Nat.succ K) = tryL K (Nat.lor base (orA rest)) (fld it 0) (fld it 1) (go K base rest) us hs cs
      (Nat.succ K)
    rw [ih, orA'_eq, tryL'_eq]

def vs' (t t2 : ℕ) (l : List ℕ) : List ℕ :=
  @List.rec ℕ (fun _ => List ℕ) []
    (fun a _ ih => @Bool.rec (fun _ => List ℕ) (put (Nat.land a full) 1 (priv t a) :: ih) ih
      (Nat.beq (Nat.land (priv t a) t2) 0)) l

theorem vs'_eq (t t2 : ℕ) (l : List ℕ) : vs' t t2 l = vs t t2 l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    show @Bool.rec (fun _ => List ℕ) (put (Nat.land a full) 1 (priv t a) :: vs' t t2 l) (vs' t t2 l)
      (Nat.beq (Nat.land (priv t a) t2) 0) =
      cond (Nat.beq (Nat.land (priv t a) t2) 0) (vs t t2 l)
        (put (Nat.land a full) 1 (priv t a) :: vs t t2 l)
    rw [ih]
    cases Nat.beq (Nat.land (priv t a) t2) 0 <;> rfl

def fcov' (t t2 : ℕ) (l : List ℕ) : ℕ :=
  @List.rec ℕ (fun _ => ℕ) 0
    (fun a _ ih => @Bool.rec (fun _ => ℕ) ih (Nat.lor a ih) (Nat.beq (Nat.land (priv t a) t2) 0)) l

theorem fcov'_eq (t t2 : ℕ) (l : List ℕ) : fcov' t t2 l = fcov t t2 l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    show @Bool.rec (fun _ => ℕ) (fcov' t t2 l) (Nat.lor a (fcov' t t2 l))
      (Nat.beq (Nat.land (priv t a) t2) 0) =
      cond (Nat.beq (Nat.land (priv t a) t2) 0) (Nat.lor a (fcov t t2 l)) (fcov t t2 l)
    rw [ih]
    cases Nat.beq (Nat.land (priv t a) t2) 0 <;> rfl

def degI' (x : ℕ) (l : List ℕ) : ℕ :=
  @List.rec ℕ (fun _ => ℕ) 0
    (fun y _ ih => @Bool.rec (fun _ => ℕ) (Nat.succ ih) ih
      (Nat.beq (Nat.land (fld y 1) (fld x 1)) 0)) l

theorem degI'_eq (x : ℕ) (l : List ℕ) : degI' x l = degI x l := by
  induction l with
  | nil => rfl
  | cons y l ih =>
    show @Bool.rec (fun _ => ℕ) (Nat.succ (degI' x l)) (degI' x l)
      (Nat.beq (Nat.land (fld y 1) (fld x 1)) 0) =
      cond (Nat.beq (Nat.land (fld y 1) (fld x 1)) 0) (degI x l) (Nat.succ (degI x l))
    rw [ih]
    cases Nat.beq (Nat.land (fld y 1) (fld x 1)) 0 <;> rfl

def insD' (all : List ℕ) (x : ℕ) (l : List ℕ) : List ℕ :=
  @List.rec ℕ (fun _ => List ℕ) [x]
    (fun y t ih => @Bool.rec (fun _ => List ℕ) (y :: ih) (x :: y :: t)
      (Nat.blt (degI' y all) (degI' x all))) l

theorem insD'_eq (all : List ℕ) (x : ℕ) (l : List ℕ) : insD' all x l = insD all x l := by
  induction l with
  | nil => rfl
  | cons y l ih =>
    show @Bool.rec (fun _ => List ℕ) (y :: insD' all x l) (x :: y :: l)
      (Nat.blt (degI' y all) (degI' x all)) =
      cond (Nat.blt (degI y all) (degI x all)) (x :: y :: l) (y :: insD all x l)
    rw [ih, degI'_eq, degI'_eq]
    cases Nat.blt (degI y all) (degI x all) <;> rfl

def sortD' (all : List ℕ) (l : List ℕ) : List ℕ :=
  @List.rec ℕ (fun _ => List ℕ) [] (fun x _ ih => insD' all x ih) l

theorem sortD'_eq (all : List ℕ) (l : List ℕ) : sortD' all l = sortD all l := by
  induction l with
  | nil => rfl
  | cons x l ih => show insD' all x (sortD' all l) = insD all x (sortD all l); rw [ih, insD'_eq]

def mapP' (t : ℕ) (l : List ℕ) : List ℕ :=
  @List.rec ℕ (fun _ => List ℕ) [] (fun a _ ih => priv t a :: ih) l

theorem mapP'_eq (t : ℕ) (l : List ℕ) : mapP' t l = l.map (priv t) := by
  induction l with
  | nil => rfl
  | cons a l ih => show priv t a :: mapP' t l = priv t a :: l.map (priv t); rw [ih]

def classQ (K : ℕ) (as : List ℕ) : Bool :=
  (fun t => (fun t2 => (fun items =>
      go' K (fcov' t t2 as)
        (@Bool.rec (fun _ => List ℕ) items (sortD' items items) (Nat.blt 1 K)) 0 0 0)
    (vs' t t2 as)) (tw' (mapP' t as) 0 0)) (tw' as 0 0)

def classP' (l : List ℕ) (k : ℕ) : Bool := classQ (Nat.sub (Nat.succ k) (len' l)) (mapW' l)

theorem classP'_eq (l : List ℕ) (k : ℕ) : classP' l k = classP l k := by
  show go' _ (fcov' _ _ (mapW' l))
    (@Bool.rec (fun _ => List ℕ) (vs' _ _ (mapW' l)) (sortD' (vs' _ _ (mapW' l)) (vs' _ _ (mapW' l)))
      (Nat.blt 1 (Nat.sub (Nat.succ k) (len' l)))) 0 0 0 = classP l k
  rw [mapW'_eq, len'_eq, tw'_eq, mapP'_eq, tw'_eq, go'_eq, fcov'_eq, vs'_eq, sortD'_eq]
  unfold classP classP2 classP3
  cases Nat.blt 1 (Nat.sub (Nat.succ k) l.length) <;> rfl

def privH (l : List ℕ) (x : ℕ) : ℕ := priv (tw (l.map rectW) 0 0) (rectW x)

def t2Of (l : List ℕ) : ℕ := tw ((l.map rectW).map (priv (tw (l.map rectW) 0 0))) 0 0

def isConf (l : List ℕ) (x : ℕ) : Prop := Nat.land (privH l x) (t2Of l) ≠ 0

structure ClassLab (l : List ℕ) (K : ℕ) (c : ℕ → ℕ) : Prop where
  le : ∀ x ∈ l, isConf l x → c x ≤ K
  ne : l.Pairwise (fun x y => isConf l x → isConf l y → c x = c y →
        Nat.land (privH l x) (privH l y) = 0)
  cov : ∀ i U : ℕ, 1 ≤ i → i ≤ K →
        (∀ r, U.testBit r = true →
          ∃ x ∈ l, isConf l x ∧ c x = i ∧ (privH l x).testBit r = true) →
        ∀ q, (hull U).testBit q = true →
        ∃ y ∈ l, (rectW y).testBit q = true ∧ (isConf l y → 1 ≤ c y ∧ c y ≤ i)

theorem ValidLab.classLab {l : List ℕ} {K : ℕ} {c : ℕ → ℕ} (hnd : l.Nodup)
    (h : ValidLab l K c) : ClassLab l K c := by
  obtain ⟨h1, h2, h3, _⟩ := h
  refine ⟨fun x hx _ => h1 x hx, ?_, ?_⟩
  · have hnd' : l.Pairwise (fun x y => x ≠ y) := hnd
    exact List.Pairwise.imp_of_mem (fun hx hy hxy _ _ hc => h2 _ hx _ hy hxy hc) hnd'
  · intro i U hi1 _ hU q hq
    obtain ⟨y, hy, hc1, hc2, hb⟩ :=
      h3 i U hi1 (fun r hr => (hU r hr).imp (fun x hx => ⟨hx.1, hx.2.2⟩)) q hq
    exact ⟨y, hy, hb, fun _ => ⟨hc1, hc2⟩⟩

theorem fld_tb (x i q : ℕ) :
    (fld x i).testBit q = (x.testBit (144 * i + q) && decide (q < 144)) := by
  unfold fld
  rw [tb_land, full_tb]
  show ((x >>> (144 * i)).testBit q && decide (q < 144)) = _
  rw [Nat.testBit_shiftRight]

theorem put_tb (x i v r : ℕ) :
    (put x i v).testBit r = (x.testBit r || (decide (144 * i ≤ r) && v.testBit (r - 144 * i))) := by
  unfold put
  rw [tb_lor]
  show (x.testBit r || (v <<< (144 * i)).testBit r) = _
  rw [Nat.testBit_shiftLeft]

theorem fld_lt (x i q : ℕ) (h : (fld x i).testBit q = true) : q < 144 := by
  rw [fld_tb, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

theorem fld_zero (j q : ℕ) : (fld 0 j).testBit q = false := by
  rw [fld_tb, Nat.zero_testBit]
  rfl

theorem fld_put_same (x i v q : ℕ) (hv : ∀ r, v.testBit r = true → r < 144) :
    (fld (put x i v) i).testBit q = ((fld x i).testBit q || v.testBit q) := by
  rw [fld_tb, put_tb, fld_tb]
  have e : 144 * i + q - 144 * i = q := by omega
  have e2 : decide (144 * i ≤ 144 * i + q) = true := decide_eq_true (by omega)
  rw [e, e2]
  cases h : v.testBit q
  · simp
  · have e3 : decide (q < 144) = true := decide_eq_true (hv q h)
    rw [e3]
    simp

theorem fld_put_ne (x i j v q : ℕ) (hv : ∀ r, v.testBit r = true → r < 144) (hij : j ≠ i) :
    (fld (put x i v) j).testBit q = (fld x j).testBit q := by
  rw [fld_tb, put_tb, fld_tb]
  by_cases hq : q < 144
  · have e : (decide (144 * i ≤ 144 * j + q) && v.testBit (144 * j + q - 144 * i)) = false := by
      by_cases hle : 144 * i ≤ 144 * j + q
      · have hb : v.testBit (144 * j + q - 144 * i) = false := by
          cases hc : v.testBit (144 * j + q - 144 * i)
          · rfl
          · have := hv _ hc
            omega
        rw [hb]
        exact Bool.and_false _
      · rw [decide_eq_false hle]
        rfl
    rw [e, Bool.or_false]
  · rw [decide_eq_false hq, Bool.and_false, Bool.and_false]

theorem land_zero_tb (a b q : ℕ) (h : Nat.land a b = 0) (ha : a.testBit q = true)
    (hb : b.testBit q = true) : False := by
  have e := tb_land a b q
  rw [h, ha, hb, Nat.zero_testBit] at e
  exact Bool.noConfusion e

theorem chkA_true (bc hs cs K : ℕ)
    (G : ∀ i, 1 ≤ i → i ≤ K → ∀ q, (fld hs i).testBit q = true →
      bc.testBit q = true ∨ ∃ j, 1 ≤ j ∧ j ≤ i ∧ (fld cs j).testBit q = true) :
    ∀ n pre : ℕ, n ≤ K →
      (∀ j, 1 ≤ j → j + n ≤ K → ∀ q, (fld cs j).testBit q = true → pre.testBit q = true) →
      chkA bc hs cs K n pre = true := by
  intro n
  induction n with
  | zero => intro pre _ _; rfl
  | succ n ih =>
    intro pre hn hpre
    show (subM (fld hs (K - n)) (Nat.lor bc (Nat.lor pre (fld cs (K - n)))) &&
      chkA bc hs cs K n (Nat.lor pre (fld cs (K - n)))) = true
    rw [Bool.and_eq_true]
    constructor
    · have e : Nat.land (fld hs (K - n)) (Nat.lor bc (Nat.lor pre (fld cs (K - n)))) =
          fld hs (K - n) := by
        apply land_sub
        intro q hq
        rw [tb_lor, tb_lor]
        rcases G (K - n) (by omega) (by omega) q hq with h | ⟨j, hj1, hj2, hj⟩
        · rw [h]; rfl
        · by_cases hj' : j = K - n
          · subst hj'; rw [hj]; simp
          · rw [hpre j hj1 (by omega) q hj]; simp
      unfold subM
      rw [e]
      exact Nat.beq_refl _
    · apply ih _ (by omega)
      intro j hj1 hj2 q hq
      rw [tb_lor]
      by_cases hj' : j = K - n
      · subst hj'; rw [hq]; simp
      · rw [hpre j hj1 (by omega) q hq]; simp

theorem tryL_true (K bc a h : ℕ) (cont : ℕ → ℕ → ℕ → Bool) (us hs cs j : ℕ)
    (h1 : Nat.land (fld us j) h = 0)
    (h2 : chkA bc (put hs j (hull (Nat.lor (fld us j) h))) (put cs j a) K K 0 = true)
    (h3 : cont (put us j h) (put hs j (hull (Nat.lor (fld us j) h))) (put cs j a) = true) :
    ∀ n : ℕ, j ≤ K → K - j < n → tryL K bc a h cont us hs cs n = true := by
  intro n
  induction n with
  | zero => intro _ hn; omega
  | succ n ih =>
    intro hj hn
    show ((Nat.beq (Nat.land (fld us (K - n)) h) 0 &&
      (chkA bc (put hs (K - n) (hull (Nat.lor (fld us (K - n)) h)))
          (put cs (K - n) a) K K 0 &&
        cont (put us (K - n) h)
          (put hs (K - n) (hull (Nat.lor (fld us (K - n)) h)))
          (put cs (K - n) a))) ||
      tryL K bc a h cont us hs cs n) = true
    by_cases e : K - j = n
    · have e2 : K - n = j := by omega
      rw [e2, h1, h2, h3]
      rfl
    · rw [ih hj (by omega)]
      exact Bool.or_true _

theorem orA_tb (q : ℕ) : ∀ (rest : List (ℕ × ℕ)), ∀ p ∈ rest, (fld p.1 0).testBit q = true →
    (orA (rest.map Prod.fst)).testBit q = true := by
  intro rest
  induction rest with
  | nil => intro p hp; simp at hp
  | cons r rest ih =>
    intro p hp hb
    show (Nat.lor (fld r.1 0) (orA (rest.map Prod.fst))).testBit q = true
    rw [tb_lor]
    rcases List.mem_cons.mp hp with rfl | hp
    · rw [hb]; rfl
    · rw [ih p hp hb]; exact Bool.or_true _

theorem go_inv (K base : ℕ) (M : ℕ × ℕ → Prop)
    (h2 : ∀ i, 1 ≤ i → i ≤ K → ∀ q,
      (∃ U : ℕ, (∀ r, U.testBit r = true → ∃ p, M p ∧ p.2 = i ∧ (fld p.1 1).testBit r = true) ∧
        (hull U).testBit q = true) →
      base.testBit q = true ∨ ∃ p, M p ∧ 1 ≤ p.2 ∧ p.2 ≤ i ∧ (fld p.1 0).testBit q = true) :
    ∀ (rest : List (ℕ × ℕ)) (us hs cs : ℕ),
      (∀ p ∈ rest, M p) → (∀ p ∈ rest, p.2 ≤ K) →
      rest.Pairwise (fun p r => p.2 = r.2 → Nat.land (fld p.1 1) (fld r.1 1) = 0) →
      (∀ r ∈ rest, ∀ q, (fld us r.2).testBit q = true → (fld r.1 1).testBit q = true → False) →
      (∀ j q, (fld us j).testBit q = true → ∃ p, M p ∧ p.2 = j ∧ (fld p.1 1).testBit q = true) →
      (∀ j q, (fld hs j).testBit q = true →
        ∃ U : ℕ, (∀ r, U.testBit r = true → ∃ p, M p ∧ p.2 = j ∧ (fld p.1 1).testBit r = true) ∧
          (hull U).testBit q = true) →
      (∀ p, M p → p ∈ rest ∨ ∀ q, (fld p.1 0).testBit q = true → (fld cs p.2).testBit q = true) →
      go K base (rest.map Prod.fst) us hs cs = true := by
  intro rest
  induction rest with
  | nil => intro us hs cs _ _ _ _ _ _ _; rfl
  | cons it rest ih =>
    intro us hs cs hM hK hP Ius Ius2 Ihs Ics
    show tryL K (Nat.lor base (orA (rest.map Prod.fst))) (fld it.1 0) (fld it.1 1)
      (go K base (rest.map Prod.fst)) us hs cs (Nat.succ K) = true
    have hit : it ∈ it :: rest := List.mem_cons_self
    have bh : ∀ r, (fld it.1 1).testBit r = true → r < 144 := fun r => fld_lt _ _ r
    have ba : ∀ r, (fld it.1 0).testBit r = true → r < 144 := fun r => fld_lt _ _ r
    have bH : ∀ r, (hull (Nat.lor (fld us it.2) (fld it.1 1))).testBit r = true → r < 144 :=
      fun r hr => (hull_spec _ r hr).1
    have Fus : ∀ j q, (fld (put us it.2 (fld it.1 1)) j).testBit q = true →
        ∃ p, M p ∧ p.2 = j ∧ (fld p.1 1).testBit q = true := by
      intro j q hq
      by_cases hj : j = it.2
      · subst hj
        rw [fld_put_same _ _ _ _ bh, Bool.or_eq_true] at hq
        rcases hq with hq | hq
        · exact Ius2 _ q hq
        · exact ⟨it, hM it hit, rfl, hq⟩
      · rw [fld_put_ne _ _ _ _ _ bh hj] at hq
        exact Ius2 j q hq
    have Fhs : ∀ j q,
        (fld (put hs it.2 (hull (Nat.lor (fld us it.2) (fld it.1 1)))) j).testBit q = true →
        ∃ U : ℕ, (∀ r, U.testBit r = true → ∃ p, M p ∧ p.2 = j ∧ (fld p.1 1).testBit r = true) ∧
          (hull U).testBit q = true := by
      intro j q hq
      by_cases hj : j = it.2
      · subst hj
        rw [fld_put_same _ _ _ _ bH, Bool.or_eq_true] at hq
        rcases hq with hq | hq
        · exact Ihs _ q hq
        · refine ⟨Nat.lor (fld us it.2) (fld it.1 1), ?_, hq⟩
          intro r hr
          rw [tb_lor, Bool.or_eq_true] at hr
          rcases hr with hr | hr
          · exact Ius2 _ r hr
          · exact ⟨it, hM it hit, rfl, hr⟩
      · rw [fld_put_ne _ _ _ _ _ bH hj] at hq
        exact Ihs j q hq
    have Fcs : ∀ p, M p → p ∈ rest ∨
        ∀ q, (fld p.1 0).testBit q = true →
          (fld (put cs it.2 (fld it.1 0)) p.2).testBit q = true := by
      intro p hp
      have key : (∀ q, (fld p.1 0).testBit q = true → (fld cs p.2).testBit q = true) →
          ∀ q, (fld p.1 0).testBit q = true →
            (fld (put cs it.2 (fld it.1 0)) p.2).testBit q = true := by
        intro hold q hq
        by_cases hj : p.2 = it.2
        · rw [hj, fld_put_same _ _ _ _ ba, ← hj, hold q hq]
          rfl
        · rw [fld_put_ne _ _ _ _ _ ba hj]
          exact hold q hq
      rcases Ics p hp with hin | hold
      · rcases List.mem_cons.mp hin with rfl | hin
        · right
          intro q hq
          rw [fld_put_same _ _ _ _ ba, hq]
          exact Bool.or_true _
        · exact Or.inl hin
      · exact Or.inr (key hold)
    have hP' := List.pairwise_cons.mp hP
    apply tryL_true K _ _ _ _ us hs cs it.2 ?_ ?_ ?_ (Nat.succ K) (hK it hit)
      (Nat.lt_succ_of_le (Nat.sub_le _ _))
    · exact land_disj _ _ (Ius it hit)
    · apply chkA_true _ _ _ _ ?_ K 0 (Nat.le_refl _)
      · intro j hj1 hj2; omega
      · intro i hi1 hi2 q hq
        rcases h2 i hi1 hi2 q (Fhs i q hq) with hb | ⟨p, hp, hp1, hp2, hpq⟩
        · left
          rw [tb_lor, hb]
          rfl
        · rcases Fcs p hp with hin | hc
          · left
            rw [tb_lor, orA_tb q rest p hin hpq]
            exact Bool.or_true _
          · exact Or.inr ⟨p.2, hp1, hp2, hc q hpq⟩
    · apply ih _ _ _ (fun p hp => hM p (List.mem_cons_of_mem _ hp))
        (fun p hp => hK p (List.mem_cons_of_mem _ hp)) hP'.2 ?_ Fus Fhs Fcs
      intro r hr q hq hrq
      by_cases hj : r.2 = it.2
      · rw [hj, fld_put_same _ _ _ _ bh, Bool.or_eq_true] at hq
        rcases hq with hq | hq
        · rw [← hj] at hq
          exact Ius r (List.mem_cons_of_mem _ hr) q hq hrq
        · exact land_zero_tb _ _ q (hP'.1 r hr hj.symm) hq hrq
      · rw [fld_put_ne _ _ _ _ _ bh hj] at hq
        exact Ius r (List.mem_cons_of_mem _ hr) q hq hrq

theorem perm_map_lift {α β : Type} (f : α → β) {l1 l2 : List β} (h : l1.Perm l2) :
    ∀ ps : List α, ps.map f = l1 → ∃ ps' : List α, ps'.Perm ps ∧ ps'.map f = l2 := by
  induction h with
  | nil => intro ps hps; exact ⟨ps, List.Perm.refl _, hps⟩
  | cons x _ ih =>
    intro ps hps
    rcases ps with _ | ⟨p, ps⟩
    · simp at hps
    · rw [List.map_cons, List.cons.injEq] at hps
      obtain ⟨qs, hq1, hq2⟩ := ih ps hps.2
      refine ⟨p :: qs, List.Perm.cons p hq1, ?_⟩
      rw [List.map_cons, hq2, hps.1]
  | swap x y l =>
    intro ps hps
    rcases ps with _ | ⟨p, _ | ⟨q, r⟩⟩
    · simp at hps
    · rw [List.map_cons, List.cons.injEq] at hps
      simp at hps
    · rw [List.map_cons, List.map_cons, List.cons.injEq, List.cons.injEq] at hps
      refine ⟨q :: p :: r, List.Perm.swap _ _ _, ?_⟩
      rw [List.map_cons, List.map_cons, hps.1, hps.2.1, hps.2.2]
  | trans _ _ ih1 ih2 =>
    intro ps hps
    obtain ⟨qs, a, b⟩ := ih1 ps hps
    obtain ⟨rs, c, d⟩ := ih2 qs b
    exact ⟨rs, c.trans a, d⟩

theorem go_complete (K base : ℕ) (all : List (ℕ × ℕ)) (its : List ℕ)
    (hperm : its.Perm (all.map Prod.fst))
    (hK : ∀ p ∈ all, p.2 ≤ K)
    (h1 : all.Pairwise (fun p r => p.2 = r.2 → Nat.land (fld p.1 1) (fld r.1 1) = 0))
    (h2 : ∀ i, 1 ≤ i → i ≤ K → ∀ q,
      (∃ U : ℕ, (∀ r, U.testBit r = true →
          ∃ p, p ∈ all ∧ p.2 = i ∧ (fld p.1 1).testBit r = true) ∧
        (hull U).testBit q = true) →
      base.testBit q = true ∨
        ∃ p, p ∈ all ∧ 1 ≤ p.2 ∧ p.2 ≤ i ∧ (fld p.1 0).testBit q = true) :
    go K base its 0 0 0 = true := by
  obtain ⟨ps, hps, hmap⟩ := perm_map_lift Prod.fst hperm.symm all rfl
  rw [← hmap]
  have hsym : ∀ {p r : ℕ × ℕ}, (p.2 = r.2 → Nat.land (fld p.1 1) (fld r.1 1) = 0) →
      (r.2 = p.2 → Nat.land (fld r.1 1) (fld p.1 1) = 0) := by
    intro p r h e
    have h' := h e.symm
    apply land_disj
    intro q ha hb
    exact land_zero_tb _ _ q h' hb ha
  apply go_inv K base (fun p => p ∈ all) h2 ps 0 0 0
  · exact fun p hp => hps.mem_iff.mp hp
  · exact fun p hp => hK p (hps.mem_iff.mp hp)
  · exact (hps.pairwise_iff hsym).mpr h1
  · intro r _ q hq
    rw [fld_zero] at hq
    exact Bool.noConfusion hq
  · intro j q hq
    rw [fld_zero] at hq
    exact Bool.noConfusion hq
  · intro j q hq
    rw [fld_zero] at hq
    exact Bool.noConfusion hq
  · exact fun p hp => Or.inl (hps.mem_iff.mpr hp)

theorem vs_eq (t t2 : ℕ) : ∀ l : List ℕ, vs t t2 (l.map rectW) =
    (l.filter (fun x => !(Nat.beq (Nat.land (priv t (rectW x)) t2) 0))).map
      (fun x => put (Nat.land (rectW x) full) 1 (priv t (rectW x))) := by
  intro l
  induction l with
  | nil => rfl
  | cons x l ih =>
    show cond (Nat.beq (Nat.land (priv t (rectW x)) t2) 0) (vs t t2 (l.map rectW))
      (put (Nat.land (rectW x) full) 1 (priv t (rectW x)) :: vs t t2 (l.map rectW)) = _
    rw [ih]
    cases hb : Nat.beq (Nat.land (priv t (rectW x)) t2) 0
    · rw [List.filter_cons_of_pos (by rw [hb]; rfl)]
      rfl
    · rw [List.filter_cons_of_neg (by rw [hb]; exact Bool.noConfusion)]
      rfl

theorem fcov_tb (t t2 q : ℕ) : ∀ as : List ℕ, ∀ a ∈ as,
    Nat.beq (Nat.land (priv t a) t2) 0 = true → a.testBit q = true →
    (fcov t t2 as).testBit q = true := by
  intro as
  induction as with
  | nil => intro a ha; simp at ha
  | cons b as ih =>
    intro a ha hb hq
    show (cond (Nat.beq (Nat.land (priv t b) t2) 0) (Nat.lor b (fcov t t2 as))
      (fcov t t2 as)).testBit q = true
    rcases List.mem_cons.mp ha with rfl | ha
    · rw [hb]
      show (Nat.lor a (fcov t t2 as)).testBit q = true
      rw [tb_lor, hq]
      rfl
    · have := ih a ha hb hq
      cases Nat.beq (Nat.land (priv t b) t2) 0
      · exact this
      · show (Nat.lor b (fcov t t2 as)).testBit q = true
        rw [tb_lor, this]
        exact Bool.or_true _

theorem item_tb1 (a h q : ℕ) (hh : (fld (put (Nat.land a full) 1 h) 1).testBit q = true) :
    h.testBit q = true := by
  rw [fld_tb, put_tb, tb_land, full_tb] at hh
  have e : 144 * 1 + q - 144 * 1 = q := by omega
  have e1 : decide (144 * 1 + q < 144) = false := decide_eq_false (by omega)
  rw [e, e1, Bool.and_false, Bool.false_or, Bool.and_eq_true, Bool.and_eq_true] at hh
  exact hh.1.2

theorem item_tb0 (a h q : ℕ) (hq : q < 144) (ha : a.testBit q = true) :
    (fld (put (Nat.land a full) 1 h) 0).testBit q = true := by
  rw [fld_tb, put_tb, tb_land, full_tb]
  have e : 144 * 0 + q = q := by omega
  rw [e, ha, decide_eq_true hq]
  rfl

theorem beq0_false {n : ℕ} (h : Nat.beq n 0 = false) : n ≠ 0 := by
  intro e
  rw [e] at h
  exact Bool.noConfusion h

theorem classP3_of_lab (K t t2 : ℕ) (l : List ℕ) (c : ℕ → ℕ)
    (hle : ∀ x ∈ l, Nat.land (priv t (rectW x)) t2 ≠ 0 → c x ≤ K)
    (hne : l.Pairwise (fun x y => Nat.land (priv t (rectW x)) t2 ≠ 0 →
      Nat.land (priv t (rectW y)) t2 ≠ 0 → c x = c y →
      Nat.land (priv t (rectW x)) (priv t (rectW y)) = 0))
    (hcov : ∀ i U : ℕ, 1 ≤ i → i ≤ K →
      (∀ r, U.testBit r = true → ∃ x ∈ l, Nat.land (priv t (rectW x)) t2 ≠ 0 ∧ c x = i ∧
        (priv t (rectW x)).testBit r = true) →
      ∀ q, (hull U).testBit q = true → ∃ y ∈ l, (rectW y).testBit q = true ∧
        (Nat.land (priv t (rectW y)) t2 ≠ 0 → 1 ≤ c y ∧ c y ≤ i)) :
    classP3 K t t2 (l.map rectW) = true := by
  have hmem : ∀ p : ℕ × ℕ,
      p ∈ (l.filter (fun x => !(Nat.beq (Nat.land (priv t (rectW x)) t2) 0))).map
        (fun x => (put (Nat.land (rectW x) full) 1 (priv t (rectW x)), c x)) →
      ∃ x ∈ l, Nat.land (priv t (rectW x)) t2 ≠ 0 ∧
        p = (put (Nat.land (rectW x) full) 1 (priv t (rectW x)), c x) := by
    intro p hp
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
    obtain ⟨hx1, hx2⟩ := List.mem_filter.mp hx
    refine ⟨x, hx1, ?_, rfl⟩
    apply beq0_false
    cases hb : Nat.beq (Nat.land (priv t (rectW x)) t2) 0
    · rfl
    · rw [hb] at hx2
      exact Bool.noConfusion hx2
  unfold classP3
  apply go_complete K _
    ((l.filter (fun x => !(Nat.beq (Nat.land (priv t (rectW x)) t2) 0))).map
      (fun x => (put (Nat.land (rectW x) full) 1 (priv t (rectW x)), c x)))
  · have e : ((l.filter (fun x => !(Nat.beq (Nat.land (priv t (rectW x)) t2) 0))).map
        (fun x => (put (Nat.land (rectW x) full) 1 (priv t (rectW x)), c x))).map Prod.fst =
        vs t t2 (l.map rectW) := by
      rw [vs_eq, List.map_map]
      rfl
    rw [e]
    cases Nat.blt 1 K
    · exact List.Perm.refl _
    · exact sortD_perm _ _
  · intro p hp
    obtain ⟨x, hx, hc, rfl⟩ := hmem p hp
    exact hle x hx hc
  · rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ (List.Pairwise.filter _ hne)
    intro x y hx hy hxy hc
    have hx' := hmem _ (List.mem_map_of_mem (f := fun x =>
      (put (Nat.land (rectW x) full) 1 (priv t (rectW x)), c x)) hx)
    have hy' := hmem _ (List.mem_map_of_mem (f := fun x =>
      (put (Nat.land (rectW x) full) 1 (priv t (rectW x)), c x)) hy)
    obtain ⟨x', _, hcx, ex⟩ := hx'
    obtain ⟨y', _, hcy, ey⟩ := hy'
    have ex1 := congrArg Prod.fst ex
    have ey1 := congrArg Prod.fst ey
    have ex2 := congrArg Prod.snd ex
    have ey2 := congrArg Prod.snd ey
    have hcx' : Nat.land (priv t (rectW x)) t2 ≠ 0 := by
      have hx2 := (List.mem_filter.mp hx).2
      apply beq0_false
      cases hb : Nat.beq (Nat.land (priv t (rectW x)) t2) 0
      · rfl
      · rw [hb] at hx2
        exact Bool.noConfusion hx2
    have hcy' : Nat.land (priv t (rectW y)) t2 ≠ 0 := by
      have hy2 := (List.mem_filter.mp hy).2
      apply beq0_false
      cases hb : Nat.beq (Nat.land (priv t (rectW y)) t2) 0
      · rfl
      · rw [hb] at hy2
        exact Bool.noConfusion hy2
    have h0 := hxy hcx' hcy' hc
    apply land_disj
    intro q ha hb
    exact land_zero_tb _ _ q h0 (item_tb1 _ _ q ha) (item_tb1 _ _ q hb)
  · intro i hi1 hi2 q hq
    obtain ⟨U, hU, hUq⟩ := hq
    have hq144 : q < 144 := (hull_spec U q hUq).1
    obtain ⟨y, hy, hyq, hyc⟩ := hcov i U hi1 hi2 (by
      intro r hr
      obtain ⟨p, hp, hpi, hpr⟩ := hU r hr
      obtain ⟨x, hx, hc, rfl⟩ := hmem p hp
      exact ⟨x, hx, hc, hpi, item_tb1 _ _ r hpr⟩) q hUq
    cases hb : Nat.beq (Nat.land (priv t (rectW y)) t2) 0
    · right
      have hc := hyc (beq0_false hb)
      refine ⟨(put (Nat.land (rectW y) full) 1 (priv t (rectW y)), c y), ?_, hc.1, hc.2,
        item_tb0 _ _ q hq144 hyq⟩
      apply List.mem_map_of_mem
      apply List.mem_filter.mpr
      refine ⟨hy, ?_⟩
      rw [hb]
      rfl
    · left
      exact fcov_tb t t2 q _ (rectW y) (List.mem_map_of_mem hy) hb hyq

theorem classP_of_classLab (l : List ℕ) (k : ℕ) (c : ℕ → ℕ)
    (h : ClassLab l (Nat.sub (Nat.succ k) l.length) c) : classP l k = true :=
  classP3_of_lab _ _ _ l c h.le h.ne h.cov

theorem classP_of_validLab (l : List ℕ) (k : ℕ) (c : ℕ → ℕ) (hnd : l.Nodup)
    (h : ValidLab l (Nat.sub (Nat.succ k) l.length) c) : classP l k = true :=
  classP_of_classLab l k c (h.classLab hnd)

theorem classP'_of_validLab (l : List ℕ) (k : ℕ) (c : ℕ → ℕ) (hnd : l.Nodup)
    (h : ValidLab l (Nat.sub (Nat.succ k) l.length) c) : classP' l k = true := by
  rw [classP'_eq]
  exact classP_of_validLab l k c hnd h

theorem classP'_sound (m : Bool) : PruneOK m classP' := by
  intro l k hnd hR
  obtain ⟨c, hc⟩ := reach_validLab hnd hR
  exact classP'_of_validLab l k c hnd hc

def dsw (mk d x : ℕ) : ℕ :=
  Nat.xor (Nat.xor x (Nat.land (Nat.xor (Nat.shiftRight x d) x) mk))
    (Nat.shiftLeft (Nat.land (Nat.xor (Nat.shiftRight x d) x) mk) d)

def letN (x : ℕ) (f : ℕ → ℕ) : ℕ := @Nat.rec (fun _ => ℕ) (f 0) (fun p _ => f (Nat.succ p)) x

theorem letN_eq (x : ℕ) (f : ℕ → ℕ) : letN x f = f x := by
  cases x <;> rfl

def sig1 (x : ℕ) : ℕ :=
  dsw 0 1 x

def BitPerm (f : ℕ → ℕ) : Prop :=
  ∃ p : ℕ → ℕ, (∀ j, ∃ i, p i = j) ∧ (∀ i, p i < 12 ↔ i < 12) ∧ (∀ i, p i < 24 ↔ i < 24) ∧
    ∀ x i, (f x).testBit i = x.testBit (p i)

theorem BitPerm.comp {f g : ℕ → ℕ} (hf : BitPerm f) (hg : BitPerm g) :
    BitPerm (fun x => f (g x)) := by
  obtain ⟨p, ps, p12, p24, pe⟩ := hf
  obtain ⟨q, qs, q12, q24, qe⟩ := hg
  refine ⟨fun i => q (p i), ?_, fun i => (q12 (p i)).trans (p12 i),
    fun i => (q24 (p i)).trans (p24 i), fun x i => by rw [pe, qe]⟩
  intro j
  obtain ⟨i, hi⟩ := qs j
  obtain ⟨i', hi'⟩ := ps i
  exact ⟨i', by show q (p i') = j; rw [hi', hi]⟩

def dpi (mk d i : ℕ) : ℕ :=
  if mk.testBit i = true then i + d else if d ≤ i ∧ mk.testBit (i - d) = true then i - d else i

theorem dpi_a (mk d i : ℕ) (h : mk.testBit i = true) : dpi mk d i = i + d := by
  simp only [dpi, h, ite_true]

theorem dpi_b (mk d i : ℕ) (h : mk.testBit i = false) (h2 : d ≤ i) (h3 : mk.testBit (i - d) = true) :
    dpi mk d i = i - d := by
  simp only [dpi, h, h2, h3, Bool.false_eq_true, ite_false, and_self, ite_true]

theorem dpi_c (mk d i : ℕ) (h : mk.testBit i = false) (h2 : ¬ (d ≤ i ∧ mk.testBit (i - d) = true)) :
    dpi mk d i = i := by
  simp only [dpi, h, h2, Bool.false_eq_true, ite_false]

theorem dsw_perm (mk d : ℕ) (h1 : mk < 16777216)
    (h2 : ∀ i, i < 24 → mk.testBit i = true →
      (i + d < 12 ∨ (12 ≤ i ∧ i + d < 24)) ∧ mk.testBit (i + d) = false) : BitPerm (dsw mk d) := by
  have hm : ∀ i, mk.testBit i = true → i < 24 := by
    intro i hi
    by_contra hc
    have h3 : mk < 2 ^ i :=
      lt_of_lt_of_le h1 (le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (not_lt.mp hc)))
    rw [Nat.testBit_lt_two_pow h3] at hi
    exact Bool.noConfusion hi
  have key : ∀ i, mk.testBit i = true →
      (i + d < 12 ∨ (12 ≤ i ∧ i + d < 24)) ∧ mk.testBit (i + d) = false :=
    fun i hi => h2 i (hm i hi) hi
  have key2 : ∀ i, mk.testBit i = true → d ≤ i → mk.testBit (i - d) = false := by
    intro i hi hd
    cases hc : mk.testBit (i - d)
    · rfl
    · have h3 := (key (i - d) hc).2
      rw [Nat.sub_add_cancel hd, hi] at h3
      exact Bool.noConfusion h3

  have cases3 : ∀ i, (mk.testBit i = true ∧ (d ≤ i → mk.testBit (i - d) = false)) ∨
      (mk.testBit i = false ∧ d ≤ i ∧ mk.testBit (i - d) = true) ∨
      (mk.testBit i = false ∧ ¬ (d ≤ i ∧ mk.testBit (i - d) = true)) := by
    intro i
    cases hi : mk.testBit i
    · by_cases hi2 : d ≤ i ∧ mk.testBit (i - d) = true
      · exact Or.inr (Or.inl ⟨rfl, hi2⟩)
      · exact Or.inr (Or.inr ⟨rfl, hi2⟩)
    · exact Or.inl ⟨rfl, key2 i hi⟩
  refine ⟨dpi mk d, ?_, ?_, ?_, ?_⟩
  · intro j
    rcases cases3 j with ⟨hj, _⟩ | ⟨hj, hd, hj2⟩ | ⟨hj, hj2⟩
    · refine ⟨j + d, ?_⟩
      rw [dpi_b mk d (j + d) (key j hj).2 (Nat.le_add_left d j) (by rw [Nat.add_sub_cancel]; exact hj),
        Nat.add_sub_cancel]
    · refine ⟨j - d, ?_⟩
      rw [dpi_a mk d (j - d) hj2, Nat.sub_add_cancel hd]
    · exact ⟨j, dpi_c mk d j hj hj2⟩
  · intro i
    rcases cases3 i with ⟨hi, _⟩ | ⟨hi, hd, hi2⟩ | ⟨hi, hi2⟩
    · rw [dpi_a mk d i hi]
      have h3 := (key i hi).1
      omega
    · rw [dpi_b mk d i hi hd hi2]
      have h3 := (key (i - d) hi2).1
      omega
    · rw [dpi_c mk d i hi hi2]
  · intro i
    rcases cases3 i with ⟨hi, _⟩ | ⟨hi, hd, hi2⟩ | ⟨hi, hi2⟩
    · rw [dpi_a mk d i hi]
      have h3 := (key i hi).1
      omega
    · rw [dpi_b mk d i hi hd hi2]
      have h3 := (key (i - d) hi2).1
      omega
    · rw [dpi_c mk d i hi hi2]
  · intro x i
    show ((x ^^^ ((x >>> d ^^^ x) &&& mk)) ^^^ (((x >>> d ^^^ x) &&& mk) <<< d)).testBit i =
      x.testBit (dpi mk d i)
    rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_shiftRight,
      Nat.testBit_shiftLeft, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_shiftRight]
    rcases cases3 i with ⟨hi, hi2⟩ | ⟨hi, hd, hi2⟩ | ⟨hi, hi2⟩
    · rw [dpi_a mk d i hi, hi, Nat.add_comm d i]
      by_cases hd : d ≤ i
      · rw [hi2 hd]
        cases x.testBit i <;> cases x.testBit (i + d) <;> simp
      · have e : decide (i ≥ d) = false := by simpa using hd
        rw [e]
        cases x.testBit i <;> cases x.testBit (i + d) <;> simp
    · have e : decide (i ≥ d) = true := by simpa using hd
      rw [dpi_b mk d i hi hd hi2, hi, hi2, e, Nat.add_sub_cancel' hd]
      cases x.testBit i <;> cases x.testBit (i - d) <;> simp
    · rw [dpi_c mk d i hi hi2, hi]
      by_cases hd : d ≤ i
      · have h3 : mk.testBit (i - d) = false := by
          cases hc : mk.testBit (i - d)
          · rfl
          · exact absurd ⟨hd, hc⟩ hi2
        rw [h3]; simp
      · have e : decide (i ≥ d) = false := by simpa using hd
        rw [e]; simp

theorem BitPerm.and {f : ℕ → ℕ} (hf : BitPerm f) (a b : ℕ) : f (a &&& b) = f a &&& f b := by
  obtain ⟨p, _, _, _, pe⟩ := hf
  apply Nat.eq_of_testBit_eq
  intro i
  rw [pe, Nat.testBit_and, Nat.testBit_and, pe, pe]

theorem BitPerm.or {f : ℕ → ℕ} (hf : BitPerm f) (a b : ℕ) : f (a ||| b) = f a ||| f b := by
  obtain ⟨p, _, _, _, pe⟩ := hf
  apply Nat.eq_of_testBit_eq
  intro i
  rw [pe, Nat.testBit_or, Nat.testBit_or, pe, pe]

theorem BitPerm.xor {f : ℕ → ℕ} (hf : BitPerm f) (a b : ℕ) : f (a ^^^ b) = f a ^^^ f b := by
  obtain ⟨p, _, _, _, pe⟩ := hf
  apply Nat.eq_of_testBit_eq
  intro i
  rw [pe, Nat.testBit_xor, Nat.testBit_xor, pe, pe]

theorem BitPerm.inj {f : ℕ → ℕ} (hf : BitPerm f) {a b : ℕ} (h : f a = f b) : a = b := by
  obtain ⟨p, ps, _, _, pe⟩ := hf
  apply Nat.eq_of_testBit_eq
  intro j
  obtain ⟨i, rfl⟩ := ps j
  rw [← pe, ← pe, h]

theorem BitPerm.zero {f : ℕ → ℕ} (hf : BitPerm f) : f 0 = 0 := by
  obtain ⟨p, _, _, _, pe⟩ := hf
  apply Nat.eq_of_testBit_eq
  intro i
  rw [pe, Nat.zero_testBit, Nat.zero_testBit]

theorem BitPerm.target {f : ℕ → ℕ} (hf : BitPerm f) : f 4095 = 4095 := by
  obtain ⟨p, _, p12, _, pe⟩ := hf
  apply Nat.eq_of_testBit_eq
  intro i
  rw [pe, tb4095, tb4095, decide_eq_decide]
  exact p12 i

theorem tbOnes (i : ℕ) : (16777215 : ℕ).testBit i = decide (i < 24) := by
  have e : (16777215 : ℕ) = 2 ^ 24 - 1 := by norm_num
  rw [e, Nat.testBit_two_pow_sub_one]

theorem BitPerm.ones {f : ℕ → ℕ} (hf : BitPerm f) : f 16777215 = 16777215 := by
  obtain ⟨p, _, _, p24, pe⟩ := hf
  apply Nat.eq_of_testBit_eq
  intro i
  rw [pe, tbOnes, tbOnes, decide_eq_decide]
  exact p24 i

theorem BitPerm.hi {f : ℕ → ℕ} (hf : BitPerm f) : f 16773120 = 16773120 := by
  have e : (16773120 : ℕ) = 16777215 ^^^ 4095 := by decide
  rw [e, hf.xor, hf.ones, hf.target]

theorem lt24_iff (x : ℕ) : x < 16777216 ↔ ∀ i, 24 ≤ i → x.testBit i = false := by
  have e : (16777216 : ℕ) = 2 ^ 24 := by norm_num
  rw [e]
  constructor
  · intro h i hi
    exact Nat.testBit_lt_two_pow (lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) hi))
  · intro h
    exact Nat.lt_pow_two_of_testBit x h

theorem BitPerm.lt {f : ℕ → ℕ} (hf : BitPerm f) (x : ℕ) : f x < 16777216 ↔ x < 16777216 := by
  obtain ⟨p, ps, _, p24, pe⟩ := hf
  rw [lt24_iff, lt24_iff]
  constructor
  · intro h j hj
    obtain ⟨i, rfl⟩ := ps j
    rw [← pe]
    refine h i ?_
    by_contra hc
    have := (p24 i).mpr (not_le.mp hc)
    omega
  · intro h i hi
    rw [pe]
    refine h (p i) ?_
    by_contra hc
    have := (p24 i).mp (not_le.mp hc)
    omega

theorem sub_xor (d : ℕ) (h : d < 16777216) : 16777215 - d = 16777215 ^^^ d := by
  have e : 16777215 - d = 2 ^ 24 - (d + 1) := by omega
  have h' : d < 2 ^ 24 := by omega
  apply Nat.eq_of_testBit_eq
  intro i
  rw [e, Nat.testBit_two_pow_sub_succ h', Nat.testBit_xor, tbOnes]
  by_cases hi : i < 24
  · simp [hi]
  · have h3 : d.testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le h' (Nat.pow_le_pow_right (by norm_num) (not_lt.mp hi)))
    simp [hi, h3]

theorem BitPerm.sub {f : ℕ → ℕ} (hf : BitPerm f) (d : ℕ) : f (16777215 - d) = 16777215 - f d := by
  by_cases h : d < 16777216
  · rw [sub_xor d h, sub_xor (f d) ((hf.lt d).mpr h), hf.xor, hf.ones]
  · have h2 : ¬ f d < 16777216 := fun hc => h ((hf.lt d).mp hc)
    have e1 : 16777215 - d = 0 := by omega
    have e2 : 16777215 - f d = 0 := by omega
    rw [e1, e2, hf.zero]

theorem BitPerm.beq {f : ℕ → ℕ} (hf : BitPerm f) (a b : ℕ) : Nat.beq (f a) (f b) = Nat.beq a b := by
  by_cases h : a = b
  · rw [h, Nat.beq_refl, Nat.beq_refl]
  · rw [(beq_false_iff a b).mpr h, (beq_false_iff (f a) (f b)).mpr (fun e => h (hf.inj e))]

theorem BitPerm.beq0 {f : ℕ → ℕ} (hf : BitPerm f) (a : ℕ) : Nat.beq (f a) 0 = Nat.beq a 0 := by
  have := hf.beq a 0
  rwa [hf.zero] at this

theorem BitPerm.domN {f : ℕ → ℕ} (hf : BitPerm f) (w d : ℕ) : domN (f w) (f d) = domN w d := by
  have e1 : Nat.land (Nat.land (f w) 4095) (Nat.sub 16777215 (f d)) =
      f (Nat.land (Nat.land w 4095) (Nat.sub 16777215 d)) := by
    show (f w &&& 4095) &&& (16777215 - f d) = f ((w &&& 4095) &&& (16777215 - d))
    rw [hf.and, hf.and, hf.target, hf.sub]
  have e2 : Nat.land (Nat.land (f d) (Nat.sub 16777215 (f w))) 16773120 =
      f (Nat.land (Nat.land d (Nat.sub 16777215 w)) 16773120) := by
    show (f d &&& (16777215 - f w)) &&& 16773120 = f ((d &&& (16777215 - w)) &&& 16773120)
    rw [hf.and, hf.and, hf.hi, hf.sub]
  unfold PEqualNP.Outside.L_meta_3969.domN
  rw [e1, e2, hf.beq0, hf.beq0]

theorem BitPerm.blk {f : ℕ → ℕ} (hf : BitPerm f) (m : Bool) (w d : ℕ) :
    blk m (f w) (f d) = blk m w d := by
  cases m
  · exact hf.beq w d
  · exact hf.domN w d

def BaseOK (f : ℕ → ℕ) : Prop := ∀ d ∈ base12, ∃ d' ∈ base12, f d' = d

theorem Reach.image {f : ℕ → ℕ} (hf : BitPerm f) (hb : BaseOK f) {m : Bool} {D : Finset ℕ} {k : ℕ}
    (h : Reach m D k) : Reach m (D.image f) k := by
  induction h with
  | done k =>
    rw [Finset.image_singleton, hf.target]
    exact Reach.done k
  | step D k u v w ka kb hu hv hw hd hbase _ ih =>
    have hfil : (insert w (D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v)))).image f =
        insert (f w) ((D.image f).filter (fun x => (ka = true ∨ x ≠ f u) ∧ (kb = true ∨ x ≠ f v))) := by
      ext y
      simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_filter]
      constructor
      · rintro ⟨x, hx | ⟨hxD, h1, h2⟩, rfl⟩
        · exact Or.inl (by rw [hx])
        · exact Or.inr ⟨⟨x, hxD, rfl⟩, h1.imp_right (fun h e => h (hf.inj e)),
            h2.imp_right (fun h e => h (hf.inj e))⟩
      · rintro (rfl | ⟨⟨x, hxD, rfl⟩, h1, h2⟩)
        · exact ⟨w, Or.inl rfl, rfl⟩
        · exact ⟨x, Or.inr ⟨hxD, h1.imp_right (fun h e => h (by rw [e])),
            h2.imp_right (fun h e => h (by rw [e]))⟩, rfl⟩
    rw [hfil] at ih
    refine Reach.step (D.image f) k (f u) (f v) (f w) ka kb (Finset.mem_image_of_mem f hu)
      (Finset.mem_image_of_mem f hv) ?_ ?_ ?_ ih
    · rcases hw with hw | hw
      · exact Or.inl (by rw [hw, hf.and])
      · exact Or.inr (by rw [hw, hf.or])
    · intro d hdm
      obtain ⟨d', hd', rfl⟩ := Finset.mem_image.mp hdm
      rw [hf.blk]
      exact hd d' hd'
    · intro d hdm
      obtain ⟨d', hd', rfl⟩ := hb d hdm
      rw [hf.blk]
      exact hbase d' hd'

theorem sig1_perm : BitPerm sig1 := by
  have e : sig1 = fun x => dsw 0 1 x := by
    funext x; simp only [sig1, letN_eq]
  rw [e]
  exact dsw_perm 0 1 (by decide) (by decide)

theorem sig1_base : BaseOK sig1 := by unfold BaseOK; decide +kernel

def map' (f : ℕ → ℕ) (l : List ℕ) : List ℕ :=
  @List.rec ℕ (fun _ => List ℕ) [] (fun a _ ih => f a :: ih) l

theorem map'_eq (f : ℕ → ℕ) (l : List ℕ) : map' f l = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => show f a :: map' f l = _; rw [ih]; rfl

def sort' (l : List ℕ) : List ℕ :=
  @List.rec ℕ (fun _ => List ℕ) [] (fun a _ ih => ins' a ih) l

theorem sort'_perm (l : List ℕ) : (sort' l).Perm l := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons a l ih =>
    show (ins' a (sort' l)).Perm (a :: l)
    rw [ins'_eq]
    exact (ins_perm a _).trans (List.Perm.cons a ih)

noncomputable def symHas1 (f : ℕ → ℕ) (prev : Tree) (l : List ℕ) : Bool :=
  forceL (map' f l) (fun l1 => forceL (sort' l1) (has' prev))

theorem symHas1_sound {m : Bool} {f : ℕ → ℕ} {prev : Tree} {k : ℕ} {l : List ℕ} (hf : BitPerm f)
    (hb : BaseOK f) (hinv : Inv m prev k) (h : symHas1 f prev l = true) : ¬ Reach m l.toFinset k := by
  intro hR
  unfold symHas1 at h
  rw [forceL_eq, forceL_eq, has'_eq, map'_eq] at h
  have h2 := hinv _ h
  have e : (sort' (l.map f)).toFinset = l.toFinset.image f := by
    rw [List.toFinset_eq_of_perm _ _ (sort'_perm _)]
    ext y
    simp only [List.mem_toFinset, List.mem_map, Finset.mem_image]
  rw [e] at h2
  exact h2 (hR.image hf hb)

noncomputable def symHas (prev : Tree) (l : List ℕ) : Bool :=
  symHas1 sig1 prev l

theorem symHas_sound {m : Bool} {prev : Tree} {k : ℕ} {l : List ℕ}
    (hinv : Inv m prev k) (h : symHas prev l = true) : ¬ Reach m l.toFinset k := by
  unfold symHas at h
  exact symHas1_sound sig1_perm sig1_base hinv h

noncomputable def symP (P : List ℕ → ℕ → Bool) (prev : Tree) (k0 : ℕ) (l : List ℕ) (k : ℕ) : Bool :=
  band (P l k) (bnot (band (Nat.beq k k0) (symHas prev l)))

theorem symP_ok {m : Bool} {P : List ℕ → ℕ → Bool} {prev : Tree} {k0 : ℕ}
    (hP : PruneOK m P) (hinv : Inv m prev k0) : PruneOK m (symP P prev k0) := by
  intro l k hnd hR
  unfold symP
  rw [band_eq, bnot_eq, band_eq, hP l k hnd hR]
  cases hk : Nat.beq k k0
  · rfl
  · have e : k = k0 := Nat.eq_of_beq_eq_true hk
    subst e
    cases hs : symHas prev l
    · rfl
    · exact absurd hR (symHas_sound hinv hs)

theorem level_sym {m : Bool} {P : List ℕ → ℕ → Bool} {prev T : Tree} {k : ℕ}
    (hP : PruneOK m P) (hinv : Inv m prev k)
    (h : tall (expFast m (symP P prev k) prev k) T = true) : Inv m T (k + 1) :=
  level_fast (symP_ok hP hinv) hinv h

noncomputable def closedS (prev : Tree) (k : ℕ) (l : List ℕ) : Bool :=
  bor (closed prev k l) (symHas prev l)

theorem start_sym {m : Bool} {prev : Tree} {n : ℕ} (hinv : Inv m prev n)
    (h : subsAll base10 (closedS prev n) = true) : NoStart m n := by
  intro L hL
  have hs : (base10.filter (fun x => decide (x ∈ L))).Sublist base10 := List.filter_sublist
  have he : (base10.filter (fun x => decide (x ∈ L))).toFinset = L := by
    ext x
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hL x h, h⟩⟩
  have hnd : (base10.filter (fun x => decide (x ∈ L))).Nodup := List.Nodup.sublist hs (by decide)
  have h2 := subsAll_sub base10 _ h _ hs
  unfold closedS at h2
  rw [bor_eq, Bool.or_eq_true] at h2
  rw [← he]
  rcases h2 with h2 | h2
  · exact closed_sound hnd hinv h2
  · exact symHas_sound hinv h2
noncomputable def minL (a b : List ℕ) : List ℕ := @Ordering.rec (fun _ => List ℕ) a a b (lcmp' a b)

theorem minL_cases (a b : List ℕ) : minL a b = a ∨ minL a b = b := by
  unfold minL
  cases lcmp' a b
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

noncomputable def img (f : ℕ → ℕ) (l : List ℕ) : List ℕ := sort' (map' f l)

noncomputable def canon (l : List ℕ) : List ℕ := minL l (img sig1 l)

theorem img_reach {m : Bool} {f : ℕ → ℕ} (hf : BitPerm f) (hb : BaseOK f) {l : List ℕ} {k : ℕ}
    (hnd : l.Nodup) (hR : Reach m l.toFinset k) :
    (img f l).Nodup ∧ Reach m (img f l).toFinset k := by
  unfold img
  rw [map'_eq]
  have hp := sort'_perm (l.map f)
  refine ⟨hp.nodup_iff.mpr (List.Nodup.map (fun a b h => hf.inj h) hnd), ?_⟩
  have e : (sort' (l.map f)).toFinset = l.toFinset.image f := by
    rw [List.toFinset_eq_of_perm _ _ hp]
    ext y
    simp only [List.mem_toFinset, List.mem_map, Finset.mem_image]
  rw [e]
  exact hR.image hf hb

theorem canon_reach {m : Bool} {l : List ℕ} {k : ℕ} (hnd : l.Nodup) (hR : Reach m l.toFinset k) :
    (canon l).Nodup ∧ Reach m (canon l).toFinset k := by
  have h1 := img_reach sig1_perm sig1_base hnd hR
  have c0 : l.Nodup ∧ Reach m l.toFinset k := ⟨hnd, hR⟩
  have c1 : (minL l (img sig1 l)).Nodup ∧ Reach m (minL l (img sig1 l)).toFinset k := by
    rcases minL_cases l (img sig1 l) with e | e <;> rw [e]
    · exact c0
    · exact h1
  exact c1

noncomputable def RP (P : List ℕ → ℕ → Bool) (T R : Tree) (k0 : ℕ) (l : List ℕ) (k : ℕ) : Bool :=
  @Bool.rec (fun _ => Bool) (symP P T k0 l k)
    (forceL (canon l) (fun c => band (bnot (bor (has' T c) (has' R c))) (P c k)))
    (band (Nat.beq k k0) (Nat.ble 2 (Nat.sub (Nat.succ k) (len' l))))

theorem RP_ok {m : Bool} {P : List ℕ → ℕ → Bool} {T R : Tree} {k0 : ℕ}
    (hP : PruneOK m P) (hT : Inv m T k0) (hRi : Inv m R k0) : PruneOK m (RP P T R k0) := by
  intro l k hnd hR
  unfold RP
  cases hb : band (Nat.beq k k0) (Nat.ble 2 (Nat.sub (Nat.succ k) (len' l)))
  · exact symP_ok hP hT l k hnd hR
  · show forceL (canon l) (fun c => band (bnot (bor (has' T c) (has' R c))) (P c k)) = true
    rw [forceL_eq]
    rw [band_eq, Bool.and_eq_true] at hb
    have e : k = k0 := Nat.eq_of_beq_eq_true hb.1
    subst e
    obtain ⟨hnd', hR'⟩ := canon_reach hnd hR
    have hTf : has' T (canon l) = false := by
      cases h : has' T (canon l)
      · rfl
      · rw [has'_eq] at h; exact absurd hR' (hT _ h)
    have hRf : has' R (canon l) = false := by
      cases h : has' R (canon l)
      · rfl
      · rw [has'_eq] at h; exact absurd hR' (hRi _ h)
    rw [hTf, hRf, hP _ k hnd' hR']
    rfl

theorem level_R {m : Bool} {P : List ℕ → ℕ → Bool} {prev R T : Tree} {k : ℕ}
    (hP : PruneOK m P) (hinv : Inv m prev k) (hRi : Inv m R k)
    (h : tall (expFast m (RP P prev R k) prev k) T = true) : Inv m T (k + 1) :=
  level_fast (RP_ok hP hinv hRi) hinv h

def refOK (P : List ℕ → ℕ → Bool) (k : ℕ) (x : List ℕ) : Bool := band (sortedB x) (bnot (P x k))

theorem refuted {m : Bool} {P : List ℕ → ℕ → Bool} {R : Tree} {k : ℕ} (hP : PruneOK m P)
    (h : tall (refOK P k) R = true) : Inv m R k := by
  intro x hx hR
  have h1 := thas_all _ R x h hx
  unfold refOK at h1
  rw [band_eq, bnot_eq, Bool.and_eq_true] at h1
  have h2 := hP x k (sortedB_nodup h1.1) hR
  rw [h2] at h1
  exact Bool.noConfusion h1.2

theorem inv_nil (m : Bool) (k : ℕ) : Inv m BinaryTree.nil k := by
  intro x hx
  simp [thas] at hx

noncomputable def cpSub : {f : List ℕ → ℕ → Bool // f = classP'} := by
  refine ⟨?f, ?h⟩
  case h =>
    delta classP' classQ go' tryL' chkA' fld put subM hull hullC rowsOf colsOf orS orSL rowM full
      band bor bnot vs' fcov' priv tw' mapP' mapW' rectW' rect' tb' len' orA' sortD' insD' degI'
    beta_reduce
    exact rfl

noncomputable def cpF : List ℕ → ℕ → Bool := cpSub.1

theorem cpF_sound (m : Bool) : PruneOK m cpF := by
  have e : cpF = classP' := cpSub.2
  rw [e]
  exact classP'_sound m

noncomputable def PR (l : List ℕ) (k : ℕ) : Bool := rectP1' l k && cpF l k

theorem PR_sound : PruneOK false PR := PruneOK.and (rectP1'_ok false) (cpF_sound false)

def T1 : Tree := .nil
theorem T1_ok : tall (expFast false (RP PR BinaryTree.nil BinaryTree.nil 0) BinaryTree.nil 0) T1 = true := by decide +kernel
def T2 : Tree := .nil
theorem T2_ok : tall (expFast false (RP PR T1 BinaryTree.nil 1) T1 1) T2 = true := by decide +kernel
def T3 : Tree := .nil
theorem T3_ok : tall (expFast false (RP PR T2 BinaryTree.nil 2) T2 2) T3 = true := by decide +kernel
def T4 : Tree := .nil
theorem T4_ok : tall (expFast false (RP PR T3 BinaryTree.nil 3) T3 3) T4 = true := by decide +kernel
def T5 : Tree := .nil
theorem T5_ok : tall (expFast false (RP PR T4 BinaryTree.nil 4) T4 4) T5 = true := by decide +kernel
def T6 : Tree := .nil
theorem T6_ok : tall (expFast false (RP PR T5 BinaryTree.nil 5) T5 5) T6 = true := by decide +kernel
def T7 : Tree := (.node [467995,1593992,3275092,5382182,10846368,12979012,16292883] (.node [120934,1595017,3236112,8949779,10986665,12976960,16395302] .nil .nil) .nil)
theorem T7_ok : tall (expFast false (RP PR T6 BinaryTree.nil 6) T6 6) T7 = true := by decide +kernel
def T8a : Tree := (.node [1033,120934,1593992,3236112,8949779,10846368,12976960,16395302] (.node [38,120900,1595017,3236112,8949779,10986665,12976960,16256000] (.node [34,120900,1595017,3236112,8949779,10986665,12976960,16395302] (.node [18,467977,1593992,3275092,5382182,10846368,12979012,16292883] .nil .nil) (.node [38,120900,1595017,3236112,8949779,10846368,12976960,13051721,16256000] .nil .nil)) (.node [1033,120934,1593992,3236112,8949779,10846368,12976960,14033766,16256000] (.node [1025,120934,1593992,3236112,8949779,10986665,12976960,16395302] .nil .nil) .nil)) (.node [1059,120900,1593992,3236112,8949779,10986665,12976960,16395302] (.node [1033,121668,1593992,3236112,5382182,8949779,10846368,16650048] (.node [1033,121668,1593992,3236112,5382182,8949779,10846368,14033766,16256000] .nil .nil) .nil) (.node [1063,120900,1593992,3236112,8949779,10986665,12976960,16256000] (.node [1063,120900,1593992,3236112,8949779,10846368,12976960,13051721,16256000] .nil .nil) .nil)))
theorem T8a_ok : tall (expFast false (RP PR T7 BinaryTree.nil 7) T7 7) T8a = true := by decide +kernel
def T8b : Tree := (.node [2070,467977,1593992,3275092,5382182,10846368,12976960,16292883] (.node [1801,120900,1593992,3236112,5382182,8949779,10846368,16650048] (.node [1071,120900,1593992,3236112,8949779,10846368,12976960,16256000] (.node [1067,120900,1593992,3236112,8949779,10846368,12976960,16395302] .nil .nil) (.node [1801,120900,1593992,3236112,5382182,8949779,10846368,14033766,16256000] .nil .nil)) (.node [2052,467995,1593992,3275092,5382182,10846368,12976960,16292883] (.node [1865,120900,1593992,3236112,5382182,8949779,10846368,16256000] .nil .nil) .nil)) (.node [120900,467995,1593992,3236112,5382182,10846368,12979012,16292883] (.node [2134,467977,1593992,3236112,5382182,10846368,12976960,16292883] (.node [2116,467995,1593992,3236112,5382182,10846368,12976960,16292883] .nil .nil) .nil) (.node [120934,1595017,3236112,5382182,8949779,10986665,12976960,16256000] (.node [120934,467977,1595017,3236112,8949779,10846368,12976960,16395302] .nil .nil) .nil)))
theorem T8b_ok : tall (expFast false (RP PR T7 BinaryTree.nil 7) T7 7) T8b = true := by decide +kernel
def T8 : Tree := .node [1067,120900,1593992,3236112,8949779,10846368,12976960,14033766,16256000] T8a T8b
theorem T8_ok : tall (expFast false (RP PR T7 BinaryTree.nil 7) T7 7) T8 = true :=
  tall_node _ _ _ _ T8a_ok (by decide +kernel) T8b_ok
def T9aa : Tree := (.node [34,1033,120900,1593992,3236112,8949779,10846368,12976960,14033766,16256000] (.node [18,120900,467977,1593992,3236112,5382182,10846368,12979012,16292883] (.node [18,2116,467977,1593992,3236112,5382182,10846368,12976960,16292883] (.node [18,2052,467977,1593992,3275092,5382182,10846368,12976960,16292883] .nil .nil) .nil) (.node [34,1025,120900,1593992,3236112,8949779,10986665,12976960,16395302] .nil .nil)) (.node [34,120900,1595017,3236112,5382182,8949779,10986665,12976960,16256000] (.node [34,120900,467977,1595017,3236112,8949779,10846368,12976960,16395302] (.node [34,1033,120900,1593992,3236112,8949779,10846368,12976960,16395302] .nil .nil) .nil) (.node [38,1025,120900,1593992,3236112,8949779,10846368,12976960,13051721,16256000] .nil .nil)))
theorem T9aa_ok : tall (expFast false (RP PR T8 BinaryTree.nil 8) T8 8) T9aa = true := by decide +kernel
def T9ab : Tree := (.node [832,1033,120900,1593992,3236112,5382182,8949779,10846368,16256000] (.node [768,1033,120900,1593992,3236112,5382182,8949779,10846368,14033766,16256000] (.node [38,120900,467977,1595017,3236112,8949779,10846368,12976960,16256000] (.node [38,1033,120900,1593992,3236112,8949779,10846368,12976960,16256000] .nil .nil) .nil) (.node [768,1033,120900,1593992,3236112,5382182,8949779,10846368,16650048] .nil .nil)) (.node [1033,120934,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [1025,120934,1593992,3236112,5382182,8949779,10986665,12976960,16256000] (.node [1025,120934,467977,1593992,3236112,8949779,10846368,12976960,16395302] .nil .nil) .nil) (.node [1033,121668,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil)))
theorem T9ab_ok : tall (expFast false (RP PR T8 BinaryTree.nil 8) T8 8) T9ab = true := by decide +kernel
def T9a : Tree := .node [38,1025,120900,1593992,3236112,8949779,10986665,12976960,16256000] T9aa T9ab
theorem T9a_ok : tall (expFast false (RP PR T8 BinaryTree.nil 8) T8 8) T9a = true :=
  tall_node _ _ _ _ T9aa_ok (by decide +kernel) T9ab_ok
def T9ba : Tree := (.node [2052,120900,467995,1593992,3236112,5382182,10846368,12976960,16292883] (.node [1067,120900,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [1063,120900,467977,1593992,3236112,8949779,10846368,12976960,16256000] (.node [1059,120900,1593992,3236112,5382182,8949779,10986665,12976960,16256000] .nil .nil) .nil) (.node [1801,120900,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil)) (.node [120900,467995,1593992,3236112,5382182,10846368,12976960,16292883,16658278] (.node [2116,467977,1593992,3236112,5382182,10015387,10846368,13538131,14033766,16292883] (.node [2070,120900,467977,1593992,3236112,5382182,10846368,12976960,16292883] .nil .nil) .nil) (.node [120900,467995,1593992,3275092,5382182,10846368,12976960,16292883,16395302] .nil .nil)))
theorem T9ba_ok : tall (expFast false (RP PR T8 BinaryTree.nil 8) T8 8) T9ba = true := by decide +kernel
def T9bb : Tree := (.node [120934,467977,1593992,3236112,8949779,10986665,12976960,16292883,16395302] (.node [120934,467977,1593992,3236112,8949779,10846368,12976960,14033766,16256000,16309915] (.node [120900,1595017,3236112,5382182,8949779,10986665,11393271,12976960,16256000] (.node [120900,1595017,3236112,5382182,8949779,10986665,11374771,12976960,16395302] .nil .nil) .nil) (.node [120934,467977,1593992,3236112,8949779,10846368,12976960,16309915,16395302] .nil .nil)) (.node [121668,467977,1593992,3236112,5382182,8949779,10846368,16309915,16650048] (.node [121668,467977,1593992,3236112,5382182,8949779,10846368,14033766,16256000,16309915] (.node [120934,467977,1595017,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil) (.node [467977,1593992,3275092,5382182,7561526,8949779,10846368,12979012,16292883] .nil .nil)))
theorem T9bb_ok : tall (expFast false (RP PR T8 BinaryTree.nil 8) T8 8) T9bb = true := by decide +kernel
def T9b : Tree := .node [120900,1595017,3236112,5382182,8949779,10846368,11393271,12976960,13051721,16256000] T9ba T9bb
theorem T9b_ok : tall (expFast false (RP PR T8 BinaryTree.nil 8) T8 8) T9b = true :=
  tall_node _ _ _ _ T9ba_ok (by decide +kernel) T9bb_ok
def T9 : Tree := .node [1059,120900,467977,1593992,3236112,8949779,10846368,12976960,16395302] T9a T9b
theorem T9_ok : tall (expFast false (RP PR T8 BinaryTree.nil 8) T8 8) T9 = true :=
  tall_node _ _ _ _ T9a_ok (by decide +kernel) T9b_ok
def T10aaaaa : Tree := (.node [18,120900,467977,1593992,3236112,5382182,10846368,12976960,16292883,16658278] (.node [18,2052,120900,467977,1593992,3236112,5382182,10846368,12976960,16292883] .nil .nil) (.node [18,120900,467977,1593992,3275092,5382182,10846368,12976960,16292883,16395302] .nil .nil))
theorem T10aaaaa_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10aaaaa = true := by decide +kernel
def T10aaaab : Tree := (.node [34,1025,120900,1593992,3236112,5382182,8949779,10986665,12976960,16256000] (.node [34,1025,120900,467977,1593992,3236112,8949779,10846368,12976960,16395302] .nil .nil) (.node [34,1033,120900,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil))
theorem T10aaaab_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10aaaab = true := by decide +kernel
def T10aaaa : Tree := .node [19,120900,467977,1593992,1694412,3236112,5382182,5710895,10846368,12976960,16256000] T10aaaaa T10aaaab
theorem T10aaaa_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10aaaa = true :=
  tall_node _ _ _ _ T10aaaaa_ok (by decide +kernel) T10aaaab_ok
def T10aaab : Tree := (.node [38,1025,120900,467977,1593992,3236112,8949779,10846368,12976960,16256000] (.node [34,120900,467977,1593992,3236112,8949779,10986665,12976960,16292883,16395302] (.node [34,120900,467977,1593992,3236112,8949779,10846368,12976960,16309915,16395302] .nil .nil) (.node [34,120900,467977,1595017,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil)) (.node [38,120900,467977,1593992,3236112,8949779,10846368,12976960,13051721,16256000,16292883] (.node [38,120900,467977,1593992,3236112,8949779,9033815,10846368,12976960,13051721,16256000] .nil .nil) (.node [38,120900,467977,1593992,3236112,8949779,10846368,12976960,16256000,16309915] .nil .nil)))
theorem T10aaab_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10aaab = true := by decide +kernel
def T10aaa : Tree := .node [34,120900,467977,1593992,3236112,8949779,10846368,12976960,14033766,16256000,16309915] T10aaaa T10aaab
theorem T10aaa_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10aaa = true :=
  tall_node _ _ _ _ T10aaaa_ok (by decide +kernel) T10aaab_ok
def T10aaba : Tree := (.node [160,120900,467977,1593992,3236112,5382182,8949779,9033815,12976960,13051721,16256000] (.node [38,120900,467977,1593992,3236112,9033815,10986665,12976960,16256000,16292883] (.node [38,120900,467977,1593992,3236112,9033815,10846368,12976960,13051721,16256000,16292883] .nil .nil) (.node [160,120900,467977,523341,1593992,3236112,5382182,8949779,12976960,13538131,16256000] .nil .nil)) (.node [272,120900,467977,1593992,1694412,5382182,5710895,8949779,10846368,12976960,16256000] (.node [272,120900,467977,523341,1593992,5382182,5927598,8949779,10846368,12976960,16256000] .nil .nil) (.node [648,120900,467977,3236112,5382182,8949779,9033815,10846368,12976960,13051721,16256000] .nil .nil)))
theorem T10aaba_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10aaba = true := by decide +kernel
def T10aabb : Tree := (.node [832,120900,467977,1593992,3236112,5382182,8949779,10846368,16256000,16309915] (.node [768,120900,467977,1593992,3236112,5382182,8949779,10846368,16309915,16650048] (.node [768,120900,467977,1593992,3236112,5382182,8949779,10846368,14033766,16256000,16309915] .nil .nil) (.node [832,120900,467977,1593992,1694412,3236112,5382182,5710895,8949779,10846368,16256000] .nil .nil)) (.node [1025,120900,1593992,3236112,5382182,8949779,10986665,11374771,12976960,16395302] (.node [1025,120900,1593992,3236112,5382182,8949779,10846368,11393271,12976960,13051721,16256000] .nil .nil) .nil))
theorem T10aabb_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10aabb = true := by decide +kernel
def T10aab : Tree := .node [768,1033,120900,1593992,3236112,5382182,8949779,10846368,12976960,16256000] T10aaba T10aabb
theorem T10aab_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10aab = true :=
  tall_node _ _ _ _ T10aaba_ok (by decide +kernel) T10aabb_ok
def T10aa : Tree := .node [38,120900,467977,1593992,3236112,8949779,10986665,12976960,16256000,16292883] T10aaa T10aab
theorem T10aa_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10aa = true :=
  tall_node _ _ _ _ T10aaa_ok (by decide +kernel) T10aab_ok
def T10abaa : Tree := (.node [1033,120900,1593992,3236112,3800028,5382182,8949779,10846368,12976960,16256000] (.node [1033,120900,1593992,3236112,3765144,5382182,8949779,10846368,12976960,14033766,16256000] (.node [1025,120934,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil) (.node [1033,120900,1593992,3236112,3765144,5382182,8949779,10846368,12976960,16650048] .nil .nil)) (.node [1033,120900,1593992,3236112,5382182,8949779,10846368,11374771,12976960,14033766,16256000] (.node [1033,120900,1593992,3236112,5382182,8949779,10015387,10846368,12976960,14033766,16256000] .nil .nil) (.node [1033,120900,1593992,3236112,5382182,8949779,10846368,11374771,12976960,16395302] .nil .nil)))
theorem T10abaa_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10abaa = true := by decide +kernel
def T10abab : Tree := (.node [2116,467977,1593992,3236112,5382182,7561526,8949779,10846368,12976960,16292883] (.node [1059,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [1033,120900,1593992,3236112,5382182,8949779,10846368,11919792,12976960,14033766,16256000] .nil .nil) (.node [2052,467977,1593992,3275092,5382182,7561526,8949779,10846368,12976960,16292883] .nil .nil)) (.node [2116,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,14033766,16292883] (.node [2116,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,14033766,16256000] .nil .nil) (.node [2116,467977,1593992,3236112,5382182,8949779,10846368,13538131,14033766,16292883] .nil .nil)))
theorem T10abab_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10abab = true := by decide +kernel
def T10aba : Tree := .node [1033,120900,1593992,3236112,5382182,8949779,10846368,11393271,12976960,16256000] T10abaa T10abab
theorem T10aba_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10aba = true :=
  tall_node _ _ _ _ T10abaa_ok (by decide +kernel) T10abab_ok
def T10abb : Tree := (.node [120900,467977,1593992,1694412,3236112,5382198,5710911,8949779,10846368,12976960,16256000] (.node [120900,467977,1593992,1694412,3236112,5382182,5710895,8950035,10846368,12976960,16256000] (.node [3072,120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,14033766] (.node [3072,120900,467977,1593992,3236112,5382182,5927598,8949779,10846368,12976960,13538131] .nil .nil) (.node [120900,467977,1593992,1694412,3236112,5382182,5710895,8949779,10846368,12976976,16256000] .nil .nil)) (.node [120900,467977,1593992,1694412,3236112,5382182,7808063,8949779,10846368,12976960,16256000] (.node [120900,467977,1593992,1694412,3236112,5382182,5710911,8949779,10846368,12976960,16256000] .nil .nil) (.node [120900,467977,1593992,1694412,3236112,5382198,5710895,8949779,10846368,12976960,16256000] .nil .nil))) (.node [120900,467977,1593992,3236112,5382182,8949779,9033815,10846368,12976960,13051849,16256000] (.node [120900,467977,1593992,1694668,3236112,5382182,5710895,8949779,10846368,12976960,16256000] (.node [120900,467977,1593992,1694412,3236112,5710895,7479350,8949779,10846368,12976960,16256000] .nil .nil) (.node [120900,467977,1593992,3236112,5382182,7561526,8949779,10846368,12979012,16292883] .nil .nil)) (.node [120900,467977,1593992,3236112,5382182,8949779,9033815,10846368,12977088,13051849,16256000] (.node [120900,467977,1593992,3236112,5382182,8949779,9033815,10846368,12977088,13051721,16256000] .nil .nil) .nil)))
theorem T10abb_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10abb = true := by decide +kernel
def T10ab : Tree := .node [2116,467977,1593992,3236112,7561526,8949779,10846368,12976960,14033766,16292883] T10aba T10abb
theorem T10ab_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10ab = true :=
  tall_node _ _ _ _ T10aba_ok (by decide +kernel) T10abb_ok
def T10a : Tree := .node [1025,120900,1593992,3236112,5382182,8949779,10986665,11393271,12976960,16256000] T10aa T10ab
theorem T10a_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10a = true :=
  tall_node _ _ _ _ T10aa_ok (by decide +kernel) T10ab_ok
def T10baa : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,13540179,14035814,16292883] (.node [120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12979008,14035814,16256000] (.node [120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,14035814,16292883] (.node [120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,14035814,16256000] .nil .nil) (.node [120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12979008,14033766,16256000] .nil .nil)) (.node [120900,467977,1593992,3236112,5382182,8949779,10016411,10846368,12976960,14033766,16256000] (.node [120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12979008,14035814,16292883] .nil .nil) (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,13538131,14035814,16292883] .nil .nil))) (.node [120900,467977,1593992,3236112,5382182,8950803,10016411,10846368,12976960,14033766,16256000] (.node [120900,467977,1593992,3236112,5382182,8949811,9033847,10846368,12976960,13051721,16256000] (.node [120900,467977,1593992,3236112,5382182,8949811,9033815,10846368,12976960,13051721,16256000] .nil .nil) (.node [120900,467977,1593992,3236112,5382182,8950803,10015387,10846368,12976960,14033766,16256000] .nil .nil)) (.node [120900,467977,1593992,3236112,5382182,10015387,10846368,13538131,14033766,16292883,16658278] (.node [120900,467977,1593992,3236112,5382182,10015387,10846368,13538131,14033766,16292883,16650048] .nil .nil) (.node [120900,467977,1593992,3236112,5382310,8949779,9033815,10846368,12976960,13051721,16256000] .nil .nil))))
theorem T10baa_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10baa = true := by decide +kernel
def T10baba : Tree := (.node [120900,467977,1594024,3236112,5382182,8949779,9033815,10846368,12976960,13051721,16256000] (.node [120900,467977,1593992,3236112,5384230,8949779,10015387,10846368,12976960,14035814,16292883] (.node [120900,467977,1593992,3236112,5384230,8949779,10015387,10846368,12976960,14035814,16256000] .nil .nil) (.node [120900,467977,1593992,3236112,5384230,8949779,10846368,13538131,14035814,16292883] .nil .nil)) (.node [120900,467977,1594248,1694668,3236112,5382182,5710895,8949779,10846368,12976960,16256000] (.node [120900,467977,1594248,1694412,3236112,5382182,5710895,8949779,10846368,12976960,16256000] .nil .nil) (.node [120900,467977,1595016,3236112,5382182,8949779,10015387,10846368,12976960,14033766,16256000] .nil .nil)))
theorem T10baba_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10baba = true := by decide +kernel
def T10babb : Tree := (.node [120900,467977,1595017,3236112,5382182,8949779,10846368,11393271,12976960,16256000] (.node [120900,467977,1595017,3236112,5382182,8949779,10016411,10846368,12976960,14033766,16256000] (.node [120900,467977,1595017,3236112,5382182,8949779,10015387,10846368,12976960,14033766,16256000] .nil .nil) (.node [120900,467977,1595017,3236112,5382182,8949779,10846368,11374771,12976960,16395302] .nil .nil)) (.node [120900,467993,1593992,1694412,3236112,5382182,5710911,8949779,10846368,12976960,16256000] (.node [120900,467993,1593992,1694412,3236112,5382182,5710895,8949779,10846368,12976960,16256000] .nil .nil) .nil))
theorem T10babb_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10babb = true := by decide +kernel
def T10bab : Tree := .node [120900,467977,1595016,3236112,5382182,8949779,10016411,10846368,12976960,14033766,16256000] T10baba T10babb
theorem T10bab_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10bab = true :=
  tall_node _ _ _ _ T10baba_ok (by decide +kernel) T10babb_ok
def T10ba : Tree := .node [120900,467977,1593992,3236112,5384230,8949779,10015387,10846368,12976960,14033766,16256000] T10baa T10bab
theorem T10ba_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10ba = true :=
  tall_node _ _ _ _ T10baa_ok (by decide +kernel) T10bab_ok
def T10bbaaa : Tree := (.node [120900,467995,1593992,3236112,5382182,10846368,12976960,16292883,16650048] (.node [120900,467995,1593992,3236112,5382182,10846368,12976960,16292883,16395302] .nil .nil) (.node [120900,467995,1593992,3275092,5382182,10846368,12976960,16256000,16292883] .nil .nil))
theorem T10bbaaa_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10bbaaa = true := by decide +kernel
def T10bbaab : Tree := (.node [120900,470025,1593992,3236112,5382182,8949779,10015387,10846368,12976960,14033766,16256000] (.node [120900,468105,1593992,3236112,5382182,8949779,9033815,10846368,12976960,13051849,16256000] .nil .nil) (.node [120900,470025,1593992,3236112,5382182,8949779,10015387,10846368,12976960,14033766,16292883] .nil .nil))
theorem T10bbaab_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10bbaab = true := by decide +kernel
def T10bbaa : Tree := .node [120900,468105,1593992,3236112,5382182,8949779,9033815,10846368,12976960,13051721,16256000] T10bbaaa T10bbaab
theorem T10bbaa_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10bbaa = true :=
  tall_node _ _ _ _ T10bbaaa_ok (by decide +kernel) T10bbaab_ok
def T10bbaba : Tree := (.node [120900,1595017,3236112,5382182,8949779,9033815,10846368,12976960,13051721,16256000] (.node [120900,1595017,3236112,5382182,8949779,9033815,10846368,10986665,12976960,16256000] .nil .nil) (.node [120900,1595017,3236112,5382182,8949779,10846368,10868964,12976960,13051721,16256000] .nil .nil))
theorem T10bbaba_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10bbaba = true := by decide +kernel
def T10bbabb : Tree := (.node [120900,1595017,3236112,5382182,8949779,10868964,10986665,12976960,16256000] (.node [120900,1595017,3236112,5382182,8949779,10846368,11374771,12976960,13051721,16256000] .nil .nil) .nil)
theorem T10bbabb_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10bbabb = true := by decide +kernel
def T10bbab : Tree := .node [120900,1595017,3236112,5382182,8949779,10846368,10986665,12976960,16395302] T10bbaba T10bbabb
theorem T10bbab_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10bbab = true :=
  tall_node _ _ _ _ T10bbaba_ok (by decide +kernel) T10bbabb_ok
def T10bba : Tree := .node [120900,470025,1593992,3236112,5382182,8949779,10846368,13538131,14033766,16292883] T10bbaa T10bbab
theorem T10bba_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10bba = true :=
  tall_node _ _ _ _ T10bbaa_ok (by decide +kernel) T10bbab_ok
def T10bbba : Tree := (.node [120934,467977,1593992,3236112,5382182,8949779,10986665,12976960,16256000,16292883] (.node [120932,467977,1593992,3236112,5382182,8949779,9033847,10846368,12976960,13051721,16256000] (.node [120932,467977,1593992,3236112,5382182,8949779,9033815,10846368,12976960,13051721,16256000] .nil .nil) (.node [120934,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16309915] .nil .nil)) (.node [120934,467977,1593992,3236112,8949779,10846368,12976960,16292883,16395302] (.node [120934,467977,1593992,3236112,8949779,10846368,12976960,14033766,16256000,16292883] .nil .nil) (.node [121156,467977,1593992,1694412,3236112,5382182,5710895,8949779,10846368,12976960,16256000] .nil .nil)))
theorem T10bbba_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10bbba = true := by decide +kernel
def T10bbbba : Tree := (.node [121668,467977,1593992,3236112,5382182,8949779,10846368,14033766,16256000,16292883] (.node [121668,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16309915] .nil .nil) (.node [121668,467977,1593992,3236112,5382182,8949779,10846368,16292883,16650048] .nil .nil))
theorem T10bbbba_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10bbbba = true := by decide +kernel
def T10bbbbb : Tree := (.node [467977,1593992,3236112,3275092,5382182,8949779,10846368,12979012,16292883] (.node [121925,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,14033766,16256000] .nil .nil) .nil)
theorem T10bbbbb_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10bbbbb = true := by decide +kernel
def T10bbbb : Tree := .node [121924,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,14033766,16256000] T10bbbba T10bbbbb
theorem T10bbbb_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10bbbb = true :=
  tall_node _ _ _ _ T10bbbba_ok (by decide +kernel) T10bbbbb_ok
def T10bbb : Tree := .node [121156,467977,1593992,1694668,3236112,5382182,5710895,8949779,10846368,12976960,16256000] T10bbba T10bbbb
theorem T10bbb_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10bbb = true :=
  tall_node _ _ _ _ T10bbba_ok (by decide +kernel) T10bbbb_ok
def T10bb : Tree := .node [120900,1595017,3236112,5382182,8949779,10986665,11374771,12976960,16256000] T10bba T10bbb
theorem T10bb_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10bb = true :=
  tall_node _ _ _ _ T10bba_ok (by decide +kernel) T10bbb_ok
def T10b : Tree := .node [120900,467995,1593992,3236112,5382182,10846368,12976960,14033766,16256000,16292883] T10ba T10bb
theorem T10b_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10b = true :=
  tall_node _ _ _ _ T10ba_ok (by decide +kernel) T10bb_ok
def T10 : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,9033847,10846368,12976960,13051721,16256000] T10a T10b
theorem T10_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10 = true :=
  tall_node _ _ _ _ T10a_ok (by decide +kernel) T10b_ok
def R10 : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12979008,16309915] (.node [1033,120900,1595017,3236112,5382182,8949779,10846368,12976960,16650048] (.node [1033,120900,1595017,3236112,5382182,8949779,10846368,12976960,16395302] (.node [1033,120900,1593992,3236112,5382182,8949779,10846368,12976960,16658278] .nil .nil) .nil) (.node [2116,467977,1593992,3236112,5384294,8949779,10846368,12976960,16292883] (.node [2116,467977,1593992,3236112,5382182,8949779,10846368,12979012,16292883] .nil .nil) .nil)) (.node [120900,470025,1593992,3236112,5382182,8949779,10846368,12976960,16309915] (.node [120900,467977,1595017,3236112,5382182,8949779,10846368,12976960,16658278] (.node [120900,467977,1593992,3236112,5384230,8949779,10846368,12976960,16309915] .nil .nil) .nil) (.node [120900,1595017,3236112,5382182,8949779,10846368,13051721,16650048] (.node [120900,1595017,3236112,5382182,8949779,10846368,12976960,13051721,16395302] .nil .nil) .nil)))
theorem R10_ok : tall (refOK cpF 10) R10 = true := by decide +kernel
def T11aaaaaaa : Tree := (.node [18,120900,467977,1593992,3236112,5382182,10846368,12976960,14033766,16256000,16292883] (.node [16,120900,467977,1593992,1694412,3236112,5382182,5710895,8949779,10846368,12976960,16256000] .nil .nil) .nil)
theorem T11aaaaaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaaaaaa = true := by decide +kernel
def T11aaaaaab : Tree := (.node [18,120900,467977,1593992,3236112,5382182,10846368,12976960,16292883,16650048] .nil .nil)
theorem T11aaaaaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaaaaab = true := by decide +kernel
def T11aaaaaa : Tree := .node [18,120900,467977,1593992,3236112,5382182,10846368,12976960,16292883,16395302] T11aaaaaaa T11aaaaaab
theorem T11aaaaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaaaaa = true :=
  tall_node _ _ _ _ T11aaaaaaa_ok (by decide +kernel) T11aaaaaab_ok
def T11aaaaaba : Tree := (.node [32,120900,467977,1593992,3236112,5382182,8949779,9033815,10846368,12976960,13051721,16256000] (.node [19,120900,467977,1593992,3236112,5382182,5710895,10846368,12976960,16256000] .nil .nil) .nil)
theorem T11aaaaaba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaaaaba = true := by decide +kernel
def T11aaaaabb : Tree := (.node [34,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16309915] .nil .nil)
theorem T11aaaaabb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaaaabb = true := by decide +kernel
def T11aaaaab : Tree := .node [34,1025,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] T11aaaaaba T11aaaaabb
theorem T11aaaaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaaaab = true :=
  tall_node _ _ _ _ T11aaaaaba_ok (by decide +kernel) T11aaaaabb_ok
def T11aaaaa : Tree := .node [18,120900,467977,1593992,3275092,5382182,10846368,12976960,16256000,16292883] T11aaaaaa T11aaaaab
theorem T11aaaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaaaa = true :=
  tall_node _ _ _ _ T11aaaaaa_ok (by decide +kernel) T11aaaaab_ok
def T11aaaabaa : Tree := (.node [34,120900,467977,1593992,3236112,8949779,10846368,12976960,16292883,16395302] (.node [34,120900,467977,1593992,3236112,8949779,10846368,12976960,14033766,16256000,16292883] .nil .nil) .nil)
theorem T11aaaabaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaaabaa = true := by decide +kernel
def T11aaaabab : Tree := (.node [38,120900,467977,1593992,3236112,8949779,10846368,12976960,16256000,16292883] .nil .nil)
theorem T11aaaabab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaaabab = true := by decide +kernel
def T11aaaaba : Tree := .node [38,120900,467977,1593992,3236112,8949779,9033815,10846368,12976960,16256000] T11aaaabaa T11aaaabab
theorem T11aaaaba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaaaba = true :=
  tall_node _ _ _ _ T11aaaabaa_ok (by decide +kernel) T11aaaabab_ok
def T11aaaabba : Tree := (.node [160,120900,467977,523341,1593992,3236112,5382182,8949779,12976960,16256000] (.node [128,120900,467977,1593992,3236112,5382182,8949779,9033815,10846368,12976960,13051721,16256000] .nil .nil) .nil)
theorem T11aaaabba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaaabba = true := by decide +kernel
def T11aaaabbb : Tree := (.node [160,120900,467977,1593992,3236112,3765144,5382182,8949779,12976960,16256000,16292883] .nil .nil)
theorem T11aaaabbb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaaabbb = true := by decide +kernel
def T11aaaabb : Tree := .node [160,120900,467977,1593992,3236112,3275092,5382182,8949779,12976960,16256000,16292883] T11aaaabba T11aaaabbb
theorem T11aaaabb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaaabb = true :=
  tall_node _ _ _ _ T11aaaabba_ok (by decide +kernel) T11aaaabbb_ok
def T11aaaab : Tree := .node [38,120900,467977,1593992,3236112,9033815,10846368,12976960,16256000,16292883] T11aaaaba T11aaaabb
theorem T11aaaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaaab = true :=
  tall_node _ _ _ _ T11aaaaba_ok (by decide +kernel) T11aaaabb_ok
def T11aaaa : Tree := .node [34,120900,467977,1593992,3236112,5382182,8949779,10986665,12976960,16256000,16292883] T11aaaaa T11aaaab
theorem T11aaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaaa = true :=
  tall_node _ _ _ _ T11aaaaa_ok (by decide +kernel) T11aaaab_ok
def T11aaabaaa : Tree := (.node [160,120900,467977,1593992,3236112,5382182,8949779,12976960,13538131,16256000] (.node [160,120900,467977,1593992,3236112,5382182,8949779,12976960,13051721,16256000] .nil .nil) .nil)
theorem T11aaabaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaabaaa = true := by decide +kernel
def T11aaabaab : Tree := (.node [272,120900,467977,523341,1593992,5382182,8949779,10846368,12976960,16256000] .nil .nil)
theorem T11aaabaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaabaab = true := by decide +kernel
def T11aaabaa : Tree := .node [256,120900,467977,1593992,1694412,3236112,5382182,5710895,8949779,10846368,12976960,16256000] T11aaabaaa T11aaabaab
theorem T11aaabaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaabaa = true :=
  tall_node _ _ _ _ T11aaabaaa_ok (by decide +kernel) T11aaabaab_ok
def T11aaababa : Tree := (.node [272,120900,467977,1593992,5382182,5927598,8949779,10846368,12976960,16256000] (.node [272,120900,467977,1593992,5382182,5710895,8949779,10846368,12976960,16256000] .nil .nil) .nil)
theorem T11aaababa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaababa = true := by decide +kernel
def T11aaababb : Tree := (.node [272,120900,467977,1593992,5382182,8949779,10846368,12976960,14033766,16256000,16292883] .nil .nil)
theorem T11aaababb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaababb = true := by decide +kernel
def T11aaabab : Tree := .node [272,120900,467977,1593992,5382182,8949779,10846368,10868964,12976960,16256000,16292883] T11aaababa T11aaababb
theorem T11aaabab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaabab = true :=
  tall_node _ _ _ _ T11aaababa_ok (by decide +kernel) T11aaababb_ok
def T11aaaba : Tree := .node [272,120900,467977,1593992,1694412,5382182,8949779,10846368,12976960,16256000] T11aaabaa T11aaabab
theorem T11aaaba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaaba = true :=
  tall_node _ _ _ _ T11aaabaa_ok (by decide +kernel) T11aaabab_ok
def T11aaabbaa : Tree := (.node [648,120900,467977,3236112,5382182,8949779,10846368,12976960,13051721,16256000] (.node [272,120900,467977,1593992,5382182,10846368,11374771,12976960,16256000,16292883] .nil .nil) .nil)
theorem T11aaabbaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaabbaa = true := by decide +kernel
def T11aaabbab : Tree := (.node [768,120900,467977,1593992,3236112,5382182,8949779,10846368,14033766,16256000,16292883] .nil .nil)
theorem T11aaabbab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaabbab = true := by decide +kernel
def T11aaabba : Tree := .node [768,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16309915] T11aaabbaa T11aaabbab
theorem T11aaabba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaabba = true :=
  tall_node _ _ _ _ T11aaabbaa_ok (by decide +kernel) T11aaabbab_ok
def T11aaabbba : Tree := (.node [832,120900,467977,1593992,1694412,3236112,5382182,8949779,10846368,16256000] .nil .nil)
theorem T11aaabbba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaabbba = true := by decide +kernel
def T11aaabbbb : Tree := (.node [1024,120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,14033766,16256000] .nil .nil)
theorem T11aaabbbb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaabbbb = true := by decide +kernel
def T11aaabbb : Tree := .node [832,120900,467977,1593992,3236112,5382182,8949779,10846368,16256000,16292883] T11aaabbba T11aaabbbb
theorem T11aaabbb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaabbb = true :=
  tall_node _ _ _ _ T11aaabbba_ok (by decide +kernel) T11aaabbbb_ok
def T11aaabb : Tree := .node [768,120900,467977,1593992,3236112,5382182,8949779,10846368,16292883,16650048] T11aaabba T11aaabbb
theorem T11aaabb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaabb = true :=
  tall_node _ _ _ _ T11aaabba_ok (by decide +kernel) T11aaabbb_ok
def T11aaab : Tree := .node [272,120900,467977,1593992,5382182,8949779,10846368,12976960,16292883,16650048] T11aaaba T11aaabb
theorem T11aaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaab = true :=
  tall_node _ _ _ _ T11aaaba_ok (by decide +kernel) T11aaabb_ok
def T11aaa : Tree := .node [160,120900,467977,1593992,3236112,5382182,8949779,9033815,12976960,16256000] T11aaaa T11aaab
theorem T11aaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaa = true :=
  tall_node _ _ _ _ T11aaaa_ok (by decide +kernel) T11aaab_ok
def T11aabaaa : Tree := (.node [1025,120900,1593992,3236112,5382182,8949779,9033815,10846368,10986665,12976960,16256000] (.node [1025,120900,467977,1593992,3236112,5382182,8949779,10846368,11393271,12976960,16256000] (.node [1025,120900,467977,1593992,3236112,5382182,8949779,10846368,11374771,12976960,16395302] .nil .nil) .nil) (.node [1025,120900,1593992,3236112,5382182,8949779,9033815,10846368,12976960,13051721,16256000] .nil .nil))
theorem T11aabaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aabaaa = true := by decide +kernel
def T11aabaaba : Tree := (.node [1025,120900,1593992,3236112,5382182,8949779,10846368,11374771,12976960,13051721,16256000] (.node [1025,120900,1593992,3236112,5382182,8949779,10846368,10986665,12976960,16395302] .nil .nil) .nil)
theorem T11aabaaba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aabaaba = true := by decide +kernel
def T11aabaabb : Tree := (.node [1025,120900,1593992,3236112,5382182,8949779,10986665,11374771,12976960,16256000] .nil .nil)
theorem T11aabaabb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aabaabb = true := by decide +kernel
def T11aabaab : Tree := .node [1025,120900,1593992,3236112,5382182,8949779,10868964,10986665,12976960,16256000] T11aabaaba T11aabaabb
theorem T11aabaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aabaab = true :=
  tall_node _ _ _ _ T11aabaaba_ok (by decide +kernel) T11aabaabb_ok
def T11aabaa : Tree := .node [1025,120900,1593992,3236112,5382182,8949779,10846368,10868964,12976960,13051721,16256000] T11aabaaa T11aabaab
theorem T11aabaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aabaa = true :=
  tall_node _ _ _ _ T11aabaaa_ok (by decide +kernel) T11aabaab_ok
def T11aababaa : Tree := (.node [1033,120900,1593992,3236112,3765144,5382182,8949779,10846368,12976960,16256000] (.node [1033,120900,1593992,3236112,3275092,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil)
theorem T11aababaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aababaa = true := by decide +kernel
def T11aababab : Tree := (.node [1033,120900,1593992,3236112,5382182,8949779,10015387,10846368,12976960,16256000] .nil .nil)
theorem T11aababab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aababab = true := by decide +kernel
def T11aababa : Tree := .node [1033,120900,1593992,3236112,5382182,8949779,9033815,10846368,12976960,16256000] T11aababaa T11aababab
theorem T11aababa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aababa = true :=
  tall_node _ _ _ _ T11aababaa_ok (by decide +kernel) T11aababab_ok
def T11aababbaa : Tree := (.node [1033,120900,1593992,3236112,5382182,8949779,10846368,11374771,12976960,16256000] .nil .nil)
theorem T11aababbaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aababbaa = true := by decide +kernel
def T11aababbab : Tree := .nil
theorem T11aababbab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aababbab = true := by decide +kernel
def T11aababba : Tree := .node [1033,120900,1593992,3236112,5382182,8949779,10846368,11919792,12976960,16256000] T11aababbaa T11aababbab
theorem T11aababba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aababba = true :=
  tall_node _ _ _ _ T11aababbaa_ok (by decide +kernel) T11aababbab_ok
def T11aababbb : Tree := (.node [1033,120900,1593992,3236112,5382182,8949779,10846368,12976960,16395302] .nil .nil)
theorem T11aababbb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aababbb = true := by decide +kernel
def T11aababb : Tree := .node [1033,120900,1593992,3236112,5382182,8949779,10846368,12976960,14033766,16256000] T11aababba T11aababbb
theorem T11aababb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aababb = true :=
  tall_node _ _ _ _ T11aababba_ok (by decide +kernel) T11aababbb_ok
def T11aabab : Tree := .node [1033,120900,1593992,3236112,5382182,8949779,10846368,10868964,12976960,16256000] T11aababa T11aababb
theorem T11aabab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aabab = true :=
  tall_node _ _ _ _ T11aababa_ok (by decide +kernel) T11aababb_ok
def T11aaba : Tree := .node [1033,120900,1593992,1694412,3236112,5382182,8949779,10846368,12976960,16256000] T11aabaa T11aabab
theorem T11aaba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaba = true :=
  tall_node _ _ _ _ T11aabaa_ok (by decide +kernel) T11aabab_ok
def T11aabbaa : Tree := (.node [2048,120900,467977,1593992,3236112,5382182,8949779,10846368,13538131,14033766,16292883] (.node [2048,120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,14033766,16292883] (.node [2048,120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,14033766,16256000] .nil .nil) .nil) (.node [2052,120900,467977,1593992,3236112,5382182,7561526,8949779,10846368,12976960,16292883] .nil .nil))
theorem T11aabbaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aabbaa = true := by decide +kernel
def T11aabbaba : Tree := (.node [2116,467977,1593992,3236112,5382182,8949779,10846368,12976960,14033766,16292883] (.node [2116,467977,1593992,3236112,5382182,8949779,10846368,12976960,14033766,16256000] .nil .nil) .nil)
theorem T11aabbaba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aabbaba = true := by decide +kernel
def T11aabbabb : Tree := (.node [3072,120900,467977,1593992,3236112,5382182,5927598,8949779,10846368,12976960] .nil .nil)
theorem T11aabbabb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aabbabb = true := by decide +kernel
def T11aabbab : Tree := .node [2116,467977,1593992,3236112,5382182,8949779,10846368,12976960,16292883] T11aabbaba T11aabbabb
theorem T11aabbab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aabbab = true :=
  tall_node _ _ _ _ T11aabbaba_ok (by decide +kernel) T11aabbabb_ok
def T11aabba : Tree := .node [2052,467977,1593992,3236112,3275092,5382182,8949779,10846368,12976960,16292883] T11aabbaa T11aabbab
theorem T11aabba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aabba = true :=
  tall_node _ _ _ _ T11aabbaa_ok (by decide +kernel) T11aabbab_ok
def T11aabbbaa : Tree := (.node [3072,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,14033766] (.node [3072,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,13538131] .nil .nil) .nil)
theorem T11aabbbaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aabbbaa = true := by decide +kernel
def T11aabbbab : Tree := (.node [120900,121156,467977,1593992,3236112,5382182,5710895,8949779,10846368,12976960,16256000] .nil .nil)
theorem T11aabbbab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aabbbab = true := by decide +kernel
def T11aabbba : Tree := .node [120900,120932,467977,1593992,3236112,5382182,8949779,10846368,12976960,13051721,16256000] T11aabbbaa T11aabbbab
theorem T11aabbba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aabbba = true :=
  tall_node _ _ _ _ T11aabbbaa_ok (by decide +kernel) T11aabbbab_ok
def T11aabbbb : Tree := (.node [120900,467977,523341,1593992,3236112,5382182,5927598,8949779,10846368,12976960,13538131,16256000] (.node [120900,467977,468105,1593992,3236112,5382182,8949779,9033815,10846368,12976960,16256000] .nil .nil) (.node [120900,467977,523341,1593992,3236112,5382182,8949779,10015387,10846368,12976960,14033766,16256000] .nil .nil))
theorem T11aabbbb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aabbbb = true := by decide +kernel
def T11aabbb : Tree := .node [120900,467977,467993,1593992,1694412,3236112,5382182,8949779,10846368,12976960,16256000] T11aabbba T11aabbbb
theorem T11aabbb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aabbb = true :=
  tall_node _ _ _ _ T11aabbba_ok (by decide +kernel) T11aabbbb_ok
def T11aabb : Tree := .node [3072,120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960] T11aabba T11aabbb
theorem T11aabb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aabb = true :=
  tall_node _ _ _ _ T11aabba_ok (by decide +kernel) T11aabbb_ok
def T11aab : Tree := .node [1033,120900,1593992,3236112,5382182,8949779,10846368,12976960,16650048] T11aaba T11aabb
theorem T11aab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aab = true :=
  tall_node _ _ _ _ T11aaba_ok (by decide +kernel) T11aabb_ok
def T11aa : Tree := .node [1025,120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,14033766,16256000] T11aaa T11aab
theorem T11aa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aa = true :=
  tall_node _ _ _ _ T11aaa_ok (by decide +kernel) T11aab_ok
def T11abaaaa : Tree := (.node [120900,467977,1593992,1594248,3236112,5382182,8949779,10846368,12976960,14033766,16256000,16292883] (.node [120900,467977,1593992,1594248,3236112,5382182,5710895,8949779,10846368,12976960,16256000] (.node [120900,467977,1593992,1594024,3236112,3275092,5382182,8949779,10846368,12976960,16256000,16292883] .nil .nil) .nil) (.node [120900,467977,1593992,1594248,3236112,5382182,8949779,10846368,12976960,16292883,16650048] .nil .nil))
theorem T11abaaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abaaaa = true := by decide +kernel
def T11abaaaba : Tree := (.node [120900,467977,1593992,1595017,3236112,3275092,5382182,8949779,10846368,12976960,16256000] (.node [120900,467977,1593992,1595016,3236112,5382182,8949779,10846368,12976960,14033766,16256000] .nil .nil) .nil)
theorem T11abaaaba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abaaaba = true := by decide +kernel
def T11abaaabb : Tree := (.node [120900,467977,1593992,1595017,3236112,5382182,8949779,10846368,12976960,16650048] .nil .nil)
theorem T11abaaabb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abaaabb = true := by decide +kernel
def T11abaaab : Tree := .node [120900,467977,1593992,1595017,3236112,5382182,8949779,10846368,12976960,14033766,16256000] T11abaaaba T11abaaabb
theorem T11abaaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abaaab = true :=
  tall_node _ _ _ _ T11abaaaba_ok (by decide +kernel) T11abaaabb_ok
def T11abaaa : Tree := .node [120900,467977,1593992,1594312,3236112,5382182,8949779,10846368,12976960,16256000,16292883] T11abaaaa T11abaaab
theorem T11abaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abaaa = true :=
  tall_node _ _ _ _ T11abaaaa_ok (by decide +kernel) T11abaaab_ok
def T11abaaba : Tree := (.node [120900,467977,1593992,1694412,3236112,3275092,5382182,5710895,8949779,10846368,12976960,16256000] (.node [120900,467977,1593992,1694412,3146769,3236112,5382182,8949779,10846368,12976960,16256000] (.node [120900,467977,1593992,1694412,3145744,3236112,5382182,5710895,8949779,10846368,12976960,16256000] .nil .nil) .nil) (.node [120900,467977,1593992,1694412,3236112,3613721,5382182,8949779,10846368,12976960,16256000] .nil .nil))
theorem T11abaaba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abaaba = true := by decide +kernel
def T11abaabb : Tree := (.node [120900,467977,1593992,1694412,3236112,5382182,5382198,8949779,10846368,12976960,16256000] (.node [120900,467977,1593992,1694412,3236112,3800028,5382182,5710895,8949779,10846368,12976960,16256000] (.node [120900,467977,1593992,1694412,3236112,3765144,5382182,5710895,8949779,10846368,12976960,16256000] .nil .nil) .nil) (.node [120900,467977,1593992,1694412,3236112,5382182,5710895,7561526,8949779,10846368,12976960,16256000] .nil .nil))
theorem T11abaabb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abaabb = true := by decide +kernel
def T11abaab : Tree := .node [120900,467977,1593992,1694412,3236112,3630361,5382182,5710895,8949779,10846368,12976960,16256000] T11abaaba T11abaabb
theorem T11abaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abaab = true :=
  tall_node _ _ _ _ T11abaaba_ok (by decide +kernel) T11abaabb_ok
def T11abaa : Tree := .node [120900,467977,1593992,1602440,3236112,5382182,8949779,10846368,12976960,14033766,16256000,16292883] T11abaaa T11abaab
theorem T11abaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abaa = true :=
  tall_node _ _ _ _ T11abaaa_ok (by decide +kernel) T11abaab_ok
def T11ababaaa : Tree := (.node [120900,467977,1593992,1694412,3236112,5382182,7479350,8949779,10846368,12976960,16256000] (.node [120900,467977,1593992,1694412,3236112,5382182,5710895,8949779,10846368,12976960,13538131,16256000] .nil .nil) .nil)
theorem T11ababaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11ababaaa = true := by decide +kernel
def T11ababaab : Tree := (.node [120900,467977,1593992,1694412,3236112,5382182,8949779,10846368,12976976,16256000] .nil .nil)
theorem T11ababaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11ababaab = true := by decide +kernel
def T11ababaa : Tree := .node [120900,467977,1593992,1694412,3236112,5382182,8949779,10846368,12976960,14100335,16256000] T11ababaaa T11ababaab
theorem T11ababaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11ababaa = true :=
  tall_node _ _ _ _ T11ababaaa_ok (by decide +kernel) T11ababaab_ok
def T11abababa : Tree := (.node [120900,467977,1593992,1694668,3236112,5382182,8949779,10846368,12976960,16256000] (.node [120900,467977,1593992,1694412,3236112,5382198,8949779,10846368,12976960,16256000] .nil .nil) .nil)
theorem T11abababa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abababa = true := by decide +kernel
def T11abababb : Tree := (.node [120900,467977,1593992,3146769,3236112,5382182,8949779,10846368,12976960,16650048] .nil .nil)
theorem T11abababb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abababb = true := by decide +kernel
def T11ababab : Tree := .node [120900,467977,1593992,3146769,3236112,5382182,8949779,10846368,12976960,14033766,16256000] T11abababa T11abababb
theorem T11ababab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11ababab = true :=
  tall_node _ _ _ _ T11abababa_ok (by decide +kernel) T11abababb_ok
def T11ababa : Tree := .node [120900,467977,1593992,1694412,3236112,5382182,8950035,10846368,12976960,16256000] T11ababaa T11ababab
theorem T11ababa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11ababa = true :=
  tall_node _ _ _ _ T11ababaa_ok (by decide +kernel) T11ababab_ok
def T11ababbaa : Tree := (.node [120900,467977,1593992,3236112,3275092,5382182,5384230,8949779,10846368,12976960,16292883] (.node [120900,467977,1593992,3148096,3236112,5382182,8949779,10846368,12976960,16292883] .nil .nil) .nil)
theorem T11ababbaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11ababbaa = true := by decide +kernel
def T11ababbab : Tree := (.node [120900,467977,1593992,3236112,3275092,5382182,8949779,10846368,12979008,16292883] .nil .nil)
theorem T11ababbab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11ababbab = true := by decide +kernel
def T11ababba : Tree := .node [120900,467977,1593992,3236112,3275092,5382182,7481382,8949779,10846368,12976960,16292883] T11ababbaa T11ababbab
theorem T11ababba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11ababba = true :=
  tall_node _ _ _ _ T11ababbaa_ok (by decide +kernel) T11ababbab_ok
def T11ababbb : Tree := (.node [120900,467977,1593992,3236112,3691400,5382182,8949779,10846368,12976960,16292883,16650048] (.node [120900,467977,1593992,3236112,3275092,5384230,8949779,10846368,12976960,16292883] .nil .nil) (.node [120900,467977,1593992,3236112,3765144,5382182,8949779,10846368,12976960,14033766,16256000,16309915] .nil .nil))
theorem T11ababbb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11ababbb = true := by decide +kernel
def T11ababb : Tree := .node [120900,467977,1593992,3236112,3275092,5382182,8949811,10846368,12976960,16256000,16292883] T11ababba T11ababbb
theorem T11ababb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11ababb = true :=
  tall_node _ _ _ _ T11ababba_ok (by decide +kernel) T11ababbb_ok
def T11abab : Tree := .node [120900,467977,1593992,3146769,3275092,5382182,8949779,10846368,12976960,16256000] T11ababa T11ababb
theorem T11abab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abab = true :=
  tall_node _ _ _ _ T11ababa_ok (by decide +kernel) T11ababb_ok
def T11aba : Tree := .node [120900,467977,1593992,1694412,3236112,5382182,5710895,7824703,8949779,10846368,12976960,16256000] T11abaa T11abab
theorem T11aba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aba = true :=
  tall_node _ _ _ _ T11abaa_ok (by decide +kernel) T11abab_ok
def T11abbaaaa : Tree := (.node [120900,467977,1593992,3236112,5382182,5382198,8949779,10846368,12976960,16292883,16650048] (.node [120900,467977,1593992,3236112,3800028,5382182,8949779,10846368,12976960,16256000,16309915] .nil .nil) .nil)
theorem T11abbaaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abbaaaa = true := by decide +kernel
def T11abbaaab : Tree := (.node [120900,467977,1593992,3236112,5382182,5384230,8949779,10015387,10846368,12976960,16292883] .nil .nil)
theorem T11abbaaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abbaaab = true := by decide +kernel
def T11abbaaa : Tree := .node [120900,467977,1593992,3236112,5382182,5384230,8949779,10015387,10846368,12976960,16256000] T11abbaaaa T11abbaaab
theorem T11abbaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abbaaa = true :=
  tall_node _ _ _ _ T11abbaaaa_ok (by decide +kernel) T11abbaaab_ok
def T11abbaaba : Tree := (.node [120900,467977,1593992,3236112,5382182,5710895,8949779,10083039,10846368,12976960,16256000] (.node [120900,467977,1593992,3236112,5382182,5384294,8949779,10846368,12976960,16292883] .nil .nil) .nil)
theorem T11abbaaba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abbaaba = true := by decide +kernel
def T11abbaabb : Tree := (.node [120900,467977,1593992,3236112,5382182,5710895,8950035,10846368,12976960,16256000] .nil .nil)
theorem T11abbaabb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abbaabb = true := by decide +kernel
def T11abbaab : Tree := .node [120900,467977,1593992,3236112,5382182,5710895,8949779,10846368,12976976,16256000] T11abbaaba T11abbaabb
theorem T11abbaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abbaab = true :=
  tall_node _ _ _ _ T11abbaaba_ok (by decide +kernel) T11abbaabb_ok
def T11abbaa : Tree := .node [120900,467977,1593992,3236112,5382182,5384230,8949779,10846368,12976960,13538131,16292883] T11abbaaa T11abbaab
theorem T11abbaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abbaa = true :=
  tall_node _ _ _ _ T11abbaaa_ok (by decide +kernel) T11abbaab_ok
def T11abbaba : Tree := (.node [120900,467977,1593992,3236112,5382182,7561526,8949779,10846368,12976960,16292883,16658278] (.node [120900,467977,1593992,3236112,5382182,7479350,8949779,10846368,12976960,16292883,16650048] (.node [120900,467977,1593992,3236112,5382182,5927598,8949779,9033815,10846368,12976960,13051721,16256000] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5382182,7808063,8949779,10846368,12976960,16256000] .nil .nil))
theorem T11abbaba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abbaba = true := by decide +kernel
def T11abbabb : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,9033815,10846368,10986665,12976960,13051721,16256000] (.node [120900,467977,1593992,3236112,5382182,8949779,9033815,10846368,10868964,12976960,13051721,16256000] (.node [120900,467977,1593992,3236112,5382182,8949779,8950803,10846368,12976960,14033766,16256000] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5382182,8949779,9033815,10846368,11374771,12976960,13051721,16256000] .nil .nil))
theorem T11abbabb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abbabb = true := by decide +kernel
def T11abbab : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,8949811,10846368,12976960,13051721,16256000] T11abbaba T11abbabb
theorem T11abbab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abbab = true :=
  tall_node _ _ _ _ T11abbaba_ok (by decide +kernel) T11abbabb_ok
def T11abba : Tree := .node [120900,467977,1593992,3236112,5382182,5710911,8949779,10846368,12976960,16256000] T11abbaa T11abbab
theorem T11abba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abba = true :=
  tall_node _ _ _ _ T11abbaa_ok (by decide +kernel) T11abbab_ok
def T11abbbaa : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,9033815,10846368,12976960,13051721,15181801,16256000] (.node [120900,467977,1593992,3236112,5382182,8949779,9033815,10846368,12976960,13051721,15172576,16256000] (.node [120900,467977,1593992,3236112,5382182,8949779,9033815,10846368,12976960,12977088,16256000] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5382182,8949779,9033815,10846368,12976960,14100335,16256000] .nil .nil))
theorem T11abbbaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abbbaa = true := by decide +kernel
def T11abbbaba : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,9982602,10846368,12976960,14033766,16256000,16292883] (.node [120900,467977,1593992,3236112,5382182,8949779,9033847,10846368,12976960,16256000] .nil .nil) .nil)
theorem T11abbbaba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abbbaba = true := by decide +kernel
def T11abbbabb : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,12979008,16292883] .nil .nil)
theorem T11abbbabb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abbbabb = true := by decide +kernel
def T11abbbab : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,12979008,16256000] T11abbbaba T11abbbabb
theorem T11abbbab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abbbab = true :=
  tall_node _ _ _ _ T11abbbaba_ok (by decide +kernel) T11abbbabb_ok
def T11abbba : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,9033815,10846368,12977088,16256000] T11abbbaa T11abbbab
theorem T11abbba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abbba = true :=
  tall_node _ _ _ _ T11abbbaa_ok (by decide +kernel) T11abbbab_ok
def T11abbbb : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,14033766,16292883,16395302] (.node [120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,14033766,16256000,16650048] (.node [120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,14033766,16256000,16395302] (.node [120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,14033766,16256000,16309915] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,14033766,16256000,16658278] .nil .nil)) (.node [120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,14033766,16292883,16658278] (.node [120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,14033766,16292883,16650048] .nil .nil) (.node [120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,14100335,16256000] .nil .nil)))
theorem T11abbbb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abbbb = true := by decide +kernel
def T11abbb : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,14033766,16256000,16277128] T11abbba T11abbbb
theorem T11abbb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abbb = true :=
  tall_node _ _ _ _ T11abbba_ok (by decide +kernel) T11abbbb_ok
def T11abb : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,9033815,10846368,11393271,12976960,13051721,16256000] T11abba T11abbb
theorem T11abb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abb = true :=
  tall_node _ _ _ _ T11abba_ok (by decide +kernel) T11abbb_ok
def T11ab : Tree := .node [120900,467977,1593992,3236112,3765144,5382182,8949779,10846368,12976960,16309915,16650048] T11aba T11abb
theorem T11ab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11ab = true :=
  tall_node _ _ _ _ T11aba_ok (by decide +kernel) T11abb_ok
def T11a : Tree := .node [120900,467977,1593992,1593994,3236112,5382182,8949779,10846368,12976960,14033766,16256000,16292883] T11aa T11ab
theorem T11a_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11a = true :=
  tall_node _ _ _ _ T11aa_ok (by decide +kernel) T11ab_ok
def T11baaaaaa : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10016411,10846368,12976960,16256000] (.node [120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12979008,16292883] .nil .nil) .nil)
theorem T11baaaaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baaaaaa = true := by decide +kernel
def T11baaaaab : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10083039,10846368,12976960,14033766,16256000] .nil .nil)
theorem T11baaaaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baaaaab = true := by decide +kernel
def T11baaaaa : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10083039,10846368,12976960,13051721,16256000] T11baaaaaa T11baaaaab
theorem T11baaaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baaaaa = true :=
  tall_node _ _ _ _ T11baaaaaa_ok (by decide +kernel) T11baaaaab_ok
def T11baaaab : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,11393271,12976960,16256000,16309915] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,11393271,12976960,13051721,16256000,16292883] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,11374771,12976960,16309915,16395302] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,11919792,12976960,14033766,16256000,16309915] .nil .nil))
theorem T11baaaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baaaab = true := by decide +kernel
def T11baaaa : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,11374771,12976960,14033766,16256000,16309915] T11baaaaa T11baaaab
theorem T11baaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baaaa = true :=
  tall_node _ _ _ _ T11baaaaa_ok (by decide +kernel) T11baaaab_ok
def T11baaabaa : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,14035814,16292883] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,14035814,16256000] .nil .nil) .nil)
theorem T11baaabaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baaabaa = true := by decide +kernel
def T11baaabab : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976976,14033782,16256000,16292883] .nil .nil)
theorem T11baaabab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baaabab = true := by decide +kernel
def T11baaaba : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976976,14033766,16256000,16292883] T11baaabaa T11baaabab
theorem T11baaaba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baaaba = true :=
  tall_node _ _ _ _ T11baaabaa_ok (by decide +kernel) T11baaabab_ok
def T11baaabba : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12977088,13051721,16256000] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976976,16292883,16650064] .nil .nil) .nil)
theorem T11baaabba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baaabba = true := by decide +kernel
def T11baaabbb : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12979008,13538131,16292883] .nil .nil)
theorem T11baaabbb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baaabbb = true := by decide +kernel
def T11baaabb : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12977088,13051849,16256000] T11baaabba T11baaabbb
theorem T11baaabb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baaabb = true :=
  tall_node _ _ _ _ T11baaabba_ok (by decide +kernel) T11baaabbb_ok
def T11baaab : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976976,16292883,16650048] T11baaaba T11baaabb
theorem T11baaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baaab = true :=
  tall_node _ _ _ _ T11baaaba_ok (by decide +kernel) T11baaabb_ok
def T11baaa : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,13051849,16256000] T11baaaa T11baaab
theorem T11baaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baaa = true :=
  tall_node _ _ _ _ T11baaaa_ok (by decide +kernel) T11baaab_ok
def T11baabaaa : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12979008,14035814,16256000] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12979008,14033766,16256000] .nil .nil) .nil)
theorem T11baabaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baabaaa = true := by decide +kernel
def T11baabaab : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12979012,16292883] .nil .nil)
theorem T11baabaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baabaab = true := by decide +kernel
def T11baabaa : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12979008,14035814,16292883] T11baabaaa T11baabaab
theorem T11baabaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baabaa = true :=
  tall_node _ _ _ _ T11baabaaa_ok (by decide +kernel) T11baabaab_ok
def T11baababa : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846370,12976960,14033766,16256000,16292883] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,13538131,14033766,16292883,16658278] .nil .nil) .nil)
theorem T11baababa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baababa = true := by decide +kernel
def T11baababb : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846374,12976960,16256000,16292883] .nil .nil)
theorem T11baababb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baababb = true := by decide +kernel
def T11baabab : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846370,12976960,16292883,16395302] T11baababa T11baababb
theorem T11baabab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baabab = true :=
  tall_node _ _ _ _ T11baababa_ok (by decide +kernel) T11baababb_ok
def T11baaba : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,13538131,14033766,16292883,16650048] T11baabaa T11baabab
theorem T11baaba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baaba = true :=
  tall_node _ _ _ _ T11baabaa_ok (by decide +kernel) T11baabab_ok
def T11baabbaa : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10986665,11393271,12976960,16256000,16292883] (.node [120900,467977,1593992,3236112,5382182,8949779,10986665,11374771,12976960,16292883,16395302] .nil .nil) .nil)
theorem T11baabbaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baabbaa = true := by decide +kernel
def T11baabbab : Tree := (.node [120900,467977,1593992,3236112,5382182,8949811,9033847,10846368,12976960,16256000] .nil .nil)
theorem T11baabbab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baabbab = true := by decide +kernel
def T11baabba : Tree := .node [120900,467977,1593992,3236112,5382182,8949811,9033815,10846368,12976960,16256000] T11baabbaa T11baabbab
theorem T11baabba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baabba = true :=
  tall_node _ _ _ _ T11baabbaa_ok (by decide +kernel) T11baabbab_ok
def T11baabbba : Tree := (.node [120900,467977,1593992,3236112,5382182,8950035,10846368,12976960,14033766,16256000,16292883] .nil .nil)
theorem T11baabbba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baabbba = true := by decide +kernel
def T11baabbbb : Tree := (.node [120900,467977,1593992,3236112,5382182,8950803,10015387,10846368,12976960,16256000] .nil .nil)
theorem T11baabbbb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baabbbb = true := by decide +kernel
def T11baabbb : Tree := .node [120900,467977,1593992,3236112,5382182,8950035,10846368,12976960,16292883,16650048] T11baabbba T11baabbbb
theorem T11baabbb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baabbb = true :=
  tall_node _ _ _ _ T11baabbba_ok (by decide +kernel) T11baabbbb_ok
def T11baabb : Tree := .node [120900,467977,1593992,3236112,5382182,8949811,10846368,12976960,13051721,16256000] T11baabba T11baabbb
theorem T11baabb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baabb = true :=
  tall_node _ _ _ _ T11baabba_ok (by decide +kernel) T11baabbb_ok
def T11baab : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846624,12976960,14033766,16256000,16292883] T11baaba T11baabb
theorem T11baab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baab = true :=
  tall_node _ _ _ _ T11baaba_ok (by decide +kernel) T11baabb_ok
def T11baa : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12979008,13540179,16292883] T11baaa T11baab
theorem T11baa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baa = true :=
  tall_node _ _ _ _ T11baaa_ok (by decide +kernel) T11baab_ok
def T11babaaa : Tree := (.node [120900,467977,1593992,3236112,5382182,9033815,10015387,10846368,12976960,14033766,16256000,16292883] (.node [120900,467977,1593992,3236112,5382182,8951827,9033815,10846368,12976960,13051721,16256000] (.node [120900,467977,1593992,3236112,5382182,8950803,10846368,12976960,14033766,16256000] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5382182,9033815,10846368,11374771,12976960,13051721,16256000,16292883] .nil .nil))
theorem T11babaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11babaaa = true := by decide +kernel
def T11babaab : Tree := (.node [120900,467977,1593992,3236112,5382182,9033815,10986665,11393271,12976960,16256000,16292883] (.node [120900,467977,1593992,3236112,5382182,9033815,10986665,11374771,12976960,16256000,16292883] (.node [120900,467977,1593992,3236112,5382182,9033815,10846368,11393271,12976960,13051721,16256000,16292883] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5382182,9417755,10015387,10846368,12976960,14033766,16256000,16292883] .nil .nil))
theorem T11babaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11babaab = true := by decide +kernel
def T11babaa : Tree := .node [120900,467977,1593992,3236112,5382182,9033815,10846368,11374771,12976960,16256000,16309915] T11babaaa T11babaab
theorem T11babaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11babaa = true :=
  tall_node _ _ _ _ T11babaaa_ok (by decide +kernel) T11babaab_ok
def T11bababa : Tree := (.node [120900,467977,1593992,3236112,5382182,10015387,10846368,12976960,13538131,14033766,16256000,16292883] (.node [120900,467977,1593992,3236112,5382182,10015387,10846368,11393271,12976960,16256000,16292883] (.node [120900,467977,1593992,3236112,5382182,10015387,10846368,11374771,12976960,16292883,16395302] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5382182,10015387,10846368,12976960,13538131,16292883,16650048] .nil .nil))
theorem T11bababa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bababa = true := by decide +kernel
def T11bababba : Tree := (.node [120900,467977,1593992,3236112,5382198,5710895,8949779,10846368,12976960,16256000] (.node [120900,467977,1593992,3236112,5382182,10846368,11374771,12976976,16256000,16292883] .nil .nil) .nil)
theorem T11bababba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bababba = true := by decide +kernel
def T11bababbb : Tree := (.node [120900,467977,1593992,3236112,5382198,8949779,10846368,12976960,14033766,16256000,16292883] .nil .nil)
theorem T11bababbb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bababbb = true := by decide +kernel
def T11bababb : Tree := .node [120900,467977,1593992,3236112,5382198,5710911,8949779,10846368,12976960,16256000] T11bababba T11bababbb
theorem T11bababb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bababb = true :=
  tall_node _ _ _ _ T11bababba_ok (by decide +kernel) T11bababbb_ok
def T11babab : Tree := .node [120900,467977,1593992,3236112,5382182,10015387,10846368,13538131,14033766,16256000,16292883] T11bababa T11bababb
theorem T11babab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11babab = true :=
  tall_node _ _ _ _ T11bababa_ok (by decide +kernel) T11bababb_ok
def T11baba : Tree := .node [120900,467977,1593992,3236112,5382182,10015387,10846368,11374771,12976960,14033766,16256000,16292883] T11babaa T11babab
theorem T11baba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baba = true :=
  tall_node _ _ _ _ T11babaa_ok (by decide +kernel) T11babab_ok
def T11babbaaa : Tree := (.node [120900,467977,1593992,3236112,5382198,10846368,11374771,12976960,16256000,16292883] (.node [120900,467977,1593992,3236112,5382198,8949779,10846368,12976960,16292883,16650048] .nil .nil) .nil)
theorem T11babbaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11babbaaa = true := by decide +kernel
def T11babbaab : Tree := (.node [120900,467977,1593992,3236112,5382310,8949779,10846368,12976960,13051721,16256000] .nil .nil)
theorem T11babbaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11babbaab = true := by decide +kernel
def T11babbaa : Tree := .node [120900,467977,1593992,3236112,5382310,8949779,9033815,10846368,12976960,16256000] T11babbaaa T11babbaab
theorem T11babbaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11babbaa = true :=
  tall_node _ _ _ _ T11babbaaa_ok (by decide +kernel) T11babbaab_ok
def T11babbaba : Tree := (.node [120900,467977,1593992,3236112,5384230,8949779,10846368,12976960,13538131,16292883] (.node [120900,467977,1593992,3236112,5384230,8949779,10015387,10846368,12976960,16292883] .nil .nil) .nil)
theorem T11babbaba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11babbaba = true := by decide +kernel
def T11babbabb : Tree := (.node [120900,467977,1593992,3236112,5384230,8949779,10846368,12976960,14035814,16256000] .nil .nil)
theorem T11babbabb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11babbabb = true := by decide +kernel
def T11babbab : Tree := .node [120900,467977,1593992,3236112,5384230,8949779,10846368,12976960,14033766,16256000] T11babbaba T11babbabb
theorem T11babbab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11babbab = true :=
  tall_node _ _ _ _ T11babbaba_ok (by decide +kernel) T11babbabb_ok
def T11babba : Tree := .node [120900,467977,1593992,3236112,5384230,8949779,10015387,10846368,12976960,16256000] T11babbaa T11babbab
theorem T11babba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11babba = true :=
  tall_node _ _ _ _ T11babbaa_ok (by decide +kernel) T11babbab_ok
def T11babbbaa : Tree := (.node [120900,467977,1593992,3236112,5710895,7479350,8949779,10846368,12976960,16256000] (.node [120900,467977,1593992,3236112,5384294,8949779,10846368,12976960,16292883] .nil .nil) .nil)
theorem T11babbbaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11babbbaa = true := by decide +kernel
def T11babbbab : Tree := (.node [120900,467977,1593992,3236112,7561526,8949779,10846368,12976960,14033766,16292883,16395302] .nil .nil)
theorem T11babbbab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11babbbab = true := by decide +kernel
def T11babbba : Tree := .node [120900,467977,1593992,3236112,7479350,8949779,10846368,12976960,14033766,16256000,16292883] T11babbbaa T11babbbab
theorem T11babbba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11babbba = true :=
  tall_node _ _ _ _ T11babbbaa_ok (by decide +kernel) T11babbbab_ok
def T11babbbb : Tree := (.node [120900,467977,1593992,3236114,5382182,8949779,10846368,12976960,16292883,16395302] (.node [120900,467977,1593992,3236114,5382182,8949779,10846368,12976960,14033766,16256000,16292883] .nil .nil) (.node [120900,467977,1593992,3275092,5382182,5382198,8949779,10846368,12976960,16256000,16292883] .nil .nil))
theorem T11babbbb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11babbbb = true := by decide +kernel
def T11babbb : Tree := .node [120900,467977,1593992,3236112,7561526,8949779,10846368,12976960,14033766,16292883,16658278] T11babbba T11babbbb
theorem T11babbb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11babbb = true :=
  tall_node _ _ _ _ T11babbba_ok (by decide +kernel) T11babbbb_ok
def T11babb : Tree := .node [120900,467977,1593992,3236112,5384230,8949779,10846368,12976960,14035814,16292883] T11babba T11babbb
theorem T11babb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11babb = true :=
  tall_node _ _ _ _ T11babba_ok (by decide +kernel) T11babbb_ok
def T11bab : Tree := .node [120900,467977,1593992,3236112,5382198,8949779,10846368,12976960,14033782,16256000,16292883] T11baba T11babb
theorem T11bab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bab = true :=
  tall_node _ _ _ _ T11baba_ok (by decide +kernel) T11babb_ok
def T11ba : Tree := .node [120900,467977,1593992,3236112,5382182,8950803,10016411,10846368,12976960,16256000] T11baa T11bab
theorem T11ba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11ba = true :=
  tall_node _ _ _ _ T11baa_ok (by decide +kernel) T11bab_ok
def T11bbaaaaa : Tree := (.node [120900,467977,1593992,3275092,5382182,8949779,10846368,12976976,16256000,16292883] (.node [120900,467977,1593992,3275092,5382182,7561526,8949779,10846368,12976960,16292883,16395302] .nil .nil) .nil)
theorem T11bbaaaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbaaaaa = true := by decide +kernel
def T11bbaaaab : Tree := (.node [120900,467977,1593994,3236112,5382182,8949779,10846368,12976960,14033766,16256000,16292883] .nil .nil)
theorem T11bbaaaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbaaaab = true := by decide +kernel
def T11bbaaaa : Tree := .node [120900,467977,1593992,3275092,5382198,8949779,10846368,12976960,16256000,16292883] T11bbaaaaa T11bbaaaab
theorem T11bbaaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbaaaa = true :=
  tall_node _ _ _ _ T11bbaaaaa_ok (by decide +kernel) T11bbaaaab_ok
def T11bbaaaba : Tree := (.node [120900,467977,1594024,3236112,5382182,8949779,10846368,12976960,13051721,16256000] (.node [120900,467977,1594024,3236112,5382182,8949779,9033815,10846368,12976960,16256000] .nil .nil) .nil)
theorem T11bbaaaba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbaaaba = true := by decide +kernel
def T11bbaaabb : Tree := (.node [120900,467977,1594248,1694668,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil)
theorem T11bbaaabb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbaaabb = true := by decide +kernel
def T11bbaaab : Tree := .node [120900,467977,1594248,1694412,3236112,5382182,8949779,10846368,12976960,16256000] T11bbaaaba T11bbaaabb
theorem T11bbaaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbaaab = true :=
  tall_node _ _ _ _ T11bbaaaba_ok (by decide +kernel) T11bbaaabb_ok
def T11bbaaa : Tree := .node [120900,467977,1594024,3236112,3275092,5382182,8949779,10846368,12976960,16256000,16292883] T11bbaaaa T11bbaaab
theorem T11bbaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbaaa = true :=
  tall_node _ _ _ _ T11bbaaaa_ok (by decide +kernel) T11bbaaab_ok
def T11bbaabaa : Tree := (.node [120900,467977,1594248,3236112,5382182,8949779,10846368,12976960,16292883,16650048] (.node [120900,467977,1594248,3236112,5382182,8949779,10846368,12976960,14033766,16256000,16292883] .nil .nil) .nil)
theorem T11bbaabaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbaabaa = true := by decide +kernel
def T11bbaabab : Tree := (.node [120900,467977,1595016,3236112,5382182,8949779,10015387,10846368,12976960,16256000] .nil .nil)
theorem T11bbaabab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbaabab = true := by decide +kernel
def T11bbaaba : Tree := .node [120900,467977,1594312,3236112,5382182,8949779,10846368,12976960,16256000,16292883] T11bbaabaa T11bbaabab
theorem T11bbaaba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbaaba = true :=
  tall_node _ _ _ _ T11bbaabaa_ok (by decide +kernel) T11bbaabab_ok
def T11bbaabba : Tree := (.node [120900,467977,1595017,1694412,3236112,5382182,8949779,10846368,12976960,16256000] (.node [120900,467977,1595016,3236112,5382182,8949779,10846368,12976960,14033766,16256000] .nil .nil) .nil)
theorem T11bbaabba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbaabba = true := by decide +kernel
def T11bbaabbb : Tree := (.node [120900,467977,1595017,3236112,3275092,5382182,8949779,10846368,12976960,16256000] .nil .nil)
theorem T11bbaabbb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbaabbb = true := by decide +kernel
def T11bbaabb : Tree := .node [120900,467977,1595017,1695437,3236112,5382182,8949779,10846368,12976960,16256000] T11bbaabba T11bbaabbb
theorem T11bbaabb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbaabb = true :=
  tall_node _ _ _ _ T11bbaabba_ok (by decide +kernel) T11bbaabbb_ok
def T11bbaab : Tree := .node [120900,467977,1595016,3236112,5382182,8949779,10016411,10846368,12976960,16256000] T11bbaaba T11bbaabb
theorem T11bbaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbaab = true :=
  tall_node _ _ _ _ T11bbaaba_ok (by decide +kernel) T11bbaabb_ok
def T11bbaa : Tree := .node [120900,467977,1594248,3236112,5382182,5710895,8949779,10846368,12976960,16256000] T11bbaaa T11bbaab
theorem T11bbaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbaa = true :=
  tall_node _ _ _ _ T11bbaaa_ok (by decide +kernel) T11bbaab_ok
def T11bbabaaaa : Tree := (.node [120900,467977,1595017,3236112,5382182,8949779,10015387,10846368,12976960,16256000] .nil .nil)
theorem T11bbabaaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbabaaaa = true := by decide +kernel
def T11bbabaaab : Tree := .nil
theorem T11bbabaaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbabaaab = true := by decide +kernel
def T11bbabaaa : Tree := .node [120900,467977,1595017,3236112,5382182,8949779,10016411,10846368,12976960,16256000] T11bbabaaaa T11bbabaaab
theorem T11bbabaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbabaaa = true :=
  tall_node _ _ _ _ T11bbabaaaa_ok (by decide +kernel) T11bbabaaab_ok
def T11bbabaab : Tree := (.node [120900,467977,1595017,3236112,5382182,8949779,10846368,11374771,12976960,16256000] .nil .nil)
theorem T11bbabaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbabaab = true := by decide +kernel
def T11bbabaa : Tree := .node [120900,467977,1595017,3236112,5382182,8949779,10846368,10868964,12976960,16256000] T11bbabaaa T11bbabaab
theorem T11bbabaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbabaa = true :=
  tall_node _ _ _ _ T11bbabaaa_ok (by decide +kernel) T11bbabaab_ok
def T11bbababaa : Tree := (.node [120900,467977,1595017,3236112,5382182,8949779,10846368,12976960,16395302] .nil .nil)
theorem T11bbababaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbababaa = true := by decide +kernel
def T11bbababab : Tree := .nil
theorem T11bbababab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbababab = true := by decide +kernel
def T11bbababa : Tree := .node [120900,467977,1595017,3236112,5382182,8949779,10846368,12976960,16650048] T11bbababaa T11bbababab
theorem T11bbababa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbababa = true :=
  tall_node _ _ _ _ T11bbababaa_ok (by decide +kernel) T11bbababab_ok
def T11bbababb : Tree := (.node [120900,467979,1593992,3236112,5382182,8949779,10846368,12976960,14033766,16256000,16292883] .nil .nil)
theorem T11bbababb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbababb = true := by decide +kernel
def T11bbabab : Tree := .node [120900,467977,1694412,3236112,3765144,5382182,8949779,10846368,12976960,16256000,16309915] T11bbababa T11bbababb
theorem T11bbabab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbabab = true :=
  tall_node _ _ _ _ T11bbababa_ok (by decide +kernel) T11bbababb_ok
def T11bbaba : Tree := .node [120900,467977,1595017,3236112,5382182,8949779,10846368,12976960,14033766,16256000] T11bbabaa T11bbabab
theorem T11bbaba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbaba = true :=
  tall_node _ _ _ _ T11bbabaa_ok (by decide +kernel) T11bbabab_ok
def T11bbabbaa : Tree := (.node [120900,467993,1593992,3236112,5382182,5710895,8949779,10846368,12976960,16256000] (.node [120900,467993,1593992,1694412,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil)
theorem T11bbabbaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbabbaa = true := by decide +kernel
def T11bbabbab : Tree := (.node [120900,467993,1593992,3236112,5382182,8949779,10846368,12976960,14033766,16256000,16292883] .nil .nil)
theorem T11bbabbab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbabbab = true := by decide +kernel
def T11bbabba : Tree := .node [120900,467993,1593992,3236112,5382182,5710911,8949779,10846368,12976960,16256000] T11bbabbaa T11bbabbab
theorem T11bbabba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbabba = true :=
  tall_node _ _ _ _ T11bbabbaa_ok (by decide +kernel) T11bbabbab_ok
def T11bbabbba : Tree := (.node [120900,467993,1593992,3236112,5382182,10846368,11374771,12976960,16256000,16292883] .nil .nil)
theorem T11bbabbba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbabbba = true := by decide +kernel
def T11bbabbbb : Tree := (.node [120900,467995,1593992,3236112,5382182,10846368,12976960,16256000,16292883] .nil .nil)
theorem T11bbabbbb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbabbbb = true := by decide +kernel
def T11bbabbb : Tree := .node [120900,467993,1593992,3275092,5382182,8949779,10846368,12976960,16256000,16292883] T11bbabbba T11bbabbbb
theorem T11bbabbb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbabbb = true :=
  tall_node _ _ _ _ T11bbabbba_ok (by decide +kernel) T11bbabbbb_ok
def T11bbabb : Tree := .node [120900,467993,1593992,3236112,5382182,8949779,10846368,12976960,16292883,16650048] T11bbabba T11bbabbb
theorem T11bbabb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbabb = true :=
  tall_node _ _ _ _ T11bbabba_ok (by decide +kernel) T11bbabbb_ok
def T11bbab : Tree := .node [120900,467979,1593992,3236112,5382182,8949779,10846368,12976960,16292883,16395302] T11bbaba T11bbabb
theorem T11bbab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbab = true :=
  tall_node _ _ _ _ T11bbaba_ok (by decide +kernel) T11bbabb_ok
def T11bba : Tree := .node [120900,467977,1595017,3236112,5382182,8949779,9033815,10846368,12976960,16256000] T11bbaa T11bbab
theorem T11bba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bba = true :=
  tall_node _ _ _ _ T11bbaa_ok (by decide +kernel) T11bbab_ok
def T11bbbaaaa : Tree := (.node [120900,468105,1593992,3236112,5382182,8949779,10846368,12976960,13051849,16256000] (.node [120900,468105,1593992,3236112,5382182,8949779,10846368,12976960,13051721,16256000] .nil .nil) .nil)
theorem T11bbbaaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbaaaa = true := by decide +kernel
def T11bbbaaab : Tree := (.node [120900,468233,1593992,3236112,5382182,8949779,10846368,12976960,16292883,16650048] .nil .nil)
theorem T11bbbaaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbaaab = true := by decide +kernel
def T11bbbaaa : Tree := .node [120900,468233,1593992,3236112,5382182,8949779,10846368,12976960,14033766,16256000,16292883] T11bbbaaaa T11bbbaaab
theorem T11bbbaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbaaa = true :=
  tall_node _ _ _ _ T11bbbaaaa_ok (by decide +kernel) T11bbbaaab_ok
def T11bbbaaba : Tree := (.node [120900,470025,1593992,3236112,5382182,8949779,10015387,10846368,12976960,16292883] (.node [120900,470025,1593992,3236112,5382182,8949779,10015387,10846368,12976960,16256000] .nil .nil) .nil)
theorem T11bbbaaba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbaaba = true := by decide +kernel
def T11bbbaabb : Tree := (.node [120900,470025,1593992,3236112,5382182,8949779,10846368,12976960,14033766,16256000] .nil .nil)
theorem T11bbbaabb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbaabb = true := by decide +kernel
def T11bbbaab : Tree := .node [120900,470025,1593992,3236112,5382182,8949779,10846368,12976960,13538131,16292883] T11bbbaaba T11bbbaabb
theorem T11bbbaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbaab = true :=
  tall_node _ _ _ _ T11bbbaaba_ok (by decide +kernel) T11bbbaabb_ok
def T11bbbaa : Tree := .node [120900,470025,1593992,3236112,3275092,5382182,8949779,10846368,12976960,16292883] T11bbbaaa T11bbbaab
theorem T11bbbaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbaa = true :=
  tall_node _ _ _ _ T11bbbaaa_ok (by decide +kernel) T11bbbaab_ok
def T11bbbabaa : Tree := (.node [120900,1593992,3236112,3630361,5382182,9417755,10846368,12976960,16292883,16650048] (.node [120900,1593992,3236112,3275092,5382182,5710895,9417755,10846368,12976960,16256000,16292883] .nil .nil) .nil)
theorem T11bbbabaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbabaa = true := by decide +kernel
def T11bbbabab : Tree := (.node [120900,1595017,3236112,5382182,8949779,10846368,10986665,12976960,16256000] .nil .nil)
theorem T11bbbabab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbabab = true := by decide +kernel
def T11bbbaba : Tree := .node [120900,1593992,3275092,3630361,5382182,9417755,10846368,12976960,16256000,16292883] T11bbbabaa T11bbbabab
theorem T11bbbaba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbaba = true :=
  tall_node _ _ _ _ T11bbbabaa_ok (by decide +kernel) T11bbbabab_ok
def T11bbbabb : Tree := (.node [120902,467977,1593992,3236112,5382182,8949779,10846368,12976960,16292883,16395302] (.node [120902,467977,1593992,3236112,5382182,8949779,10846368,12976960,14033766,16256000,16292883] .nil .nil) (.node [120916,467977,1593992,3236112,5382182,8949779,10846368,12976960,14033766,16256000,16292883] .nil .nil))
theorem T11bbbabb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbabb = true := by decide +kernel
def T11bbbab : Tree := .node [120900,1595017,3236112,5382182,8949779,10846368,12976960,13051721,16256000] T11bbbaba T11bbbabb
theorem T11bbbab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbab = true :=
  tall_node _ _ _ _ T11bbbaba_ok (by decide +kernel) T11bbbabb_ok
def T11bbba : Tree := .node [120900,470025,1593992,3236112,5382182,8949779,10846368,12976960,14033766,16292883] T11bbbaa T11bbbab
theorem T11bbba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbba = true :=
  tall_node _ _ _ _ T11bbbaa_ok (by decide +kernel) T11bbbab_ok
def T11bbbbaaa : Tree := (.node [120932,467977,1593992,3236112,3275124,5382182,8949779,10846368,12976960,16256000,16292883] (.node [120932,467977,1593992,3236112,3275092,5382182,8949779,10846368,12976960,16256000,16292883] .nil .nil) .nil)
theorem T11bbbbaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbbaaa = true := by decide +kernel
def T11bbbbaab : Tree := (.node [120932,467977,1593992,3236112,5382182,8949779,9033847,10846368,12976960,16256000] .nil .nil)
theorem T11bbbbaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbbaab = true := by decide +kernel
def T11bbbbaa : Tree := .node [120932,467977,1593992,3236112,5382182,8949779,9033815,10846368,12976960,16256000] T11bbbbaaa T11bbbbaab
theorem T11bbbbaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbbaa = true :=
  tall_node _ _ _ _ T11bbbbaaa_ok (by decide +kernel) T11bbbbaab_ok
def T11bbbbaba : Tree := (.node [121156,467977,1593992,1694412,3236112,5382182,8949779,10846368,12976960,16256000] (.node [120934,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16292883] .nil .nil) .nil)
theorem T11bbbbaba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbbaba = true := by decide +kernel
def T11bbbbabb : Tree := (.node [121156,467977,1593992,3236112,5382182,5710895,8949779,10846368,12976960,16256000] .nil .nil)
theorem T11bbbbabb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbbabb = true := by decide +kernel
def T11bbbbab : Tree := .node [121156,467977,1593992,1694668,3236112,5382182,8949779,10846368,12976960,16256000] T11bbbbaba T11bbbbabb
theorem T11bbbbab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbbab = true :=
  tall_node _ _ _ _ T11bbbbaba_ok (by decide +kernel) T11bbbbabb_ok
def T11bbbba : Tree := .node [120932,467977,1593992,3236112,5382182,8949779,10846368,12976960,13051721,16256000] T11bbbbaa T11bbbbab
theorem T11bbbba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbba = true :=
  tall_node _ _ _ _ T11bbbbaa_ok (by decide +kernel) T11bbbbab_ok
def T11bbbbbaa : Tree := (.node [121668,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16292883] (.node [121156,467977,1593992,3236112,5382182,8949779,10846368,12976960,16292883,16650048] .nil .nil) .nil)
theorem T11bbbbbaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbbbaa = true := by decide +kernel
def T11bbbbbab : Tree := (.node [121924,467977,1593992,3236112,5382182,8949779,10846368,12976960,14033766,16256000] .nil .nil)
theorem T11bbbbbab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbbbab = true := by decide +kernel
def T11bbbbba : Tree := .node [121924,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,16256000] T11bbbbbaa T11bbbbbab
theorem T11bbbbba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbbba = true :=
  tall_node _ _ _ _ T11bbbbbaa_ok (by decide +kernel) T11bbbbbab_ok
def T11bbbbbba : Tree := (.node [121925,467977,1593992,3236112,5382182,8949779,10846368,12976960,14033766,16256000] .nil .nil)
theorem T11bbbbbba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbbbba = true := by decide +kernel
def T11bbbbbbb : Tree := (.node [467977,1593992,3236112,3275092,5382182,8949779,10846368,13097796,16292883,16650048] .nil .nil)
theorem T11bbbbbbb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbbbbb = true := by decide +kernel
def T11bbbbbb : Tree := .node [467977,1593992,3236112,3275092,5382182,8949779,10846368,13097796,14033766,16256000,16292883] T11bbbbbba T11bbbbbbb
theorem T11bbbbbb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbbbb = true :=
  tall_node _ _ _ _ T11bbbbbba_ok (by decide +kernel) T11bbbbbbb_ok
def T11bbbbb : Tree := .node [121925,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,16256000] T11bbbbba T11bbbbbb
theorem T11bbbbb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbbb = true :=
  tall_node _ _ _ _ T11bbbbba_ok (by decide +kernel) T11bbbbbb_ok
def T11bbbb : Tree := .node [121156,467977,1593992,3236112,5382182,8949779,10846368,12976960,14033766,16256000,16292883] T11bbbba T11bbbbb
theorem T11bbbb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbb = true :=
  tall_node _ _ _ _ T11bbbba_ok (by decide +kernel) T11bbbbb_ok
def T11bbb : Tree := .node [120916,467977,1593992,3236112,5382182,8949779,10846368,12976960,16292883,16650048] T11bbba T11bbbb
theorem T11bbb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbb = true :=
  tall_node _ _ _ _ T11bbba_ok (by decide +kernel) T11bbbb_ok
def T11bb : Tree := .node [120900,468105,1593992,3236112,5382182,8949779,9033815,10846368,12976960,16256000] T11bba T11bbb
theorem T11bb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bb = true :=
  tall_node _ _ _ _ T11bba_ok (by decide +kernel) T11bbb_ok
def T11b : Tree := .node [120900,467977,1593992,3275092,5382182,7479350,8949779,10846368,12976960,16256000,16292883] T11ba T11bb
theorem T11b_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11b = true :=
  tall_node _ _ _ _ T11ba_ok (by decide +kernel) T11bb_ok
def T11 : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12979008,16256000] T11a T11b
theorem T11_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11 = true :=
  tall_node _ _ _ _ T11a_ok (by decide +kernel) T11b_ok
def R11aa : Tree := (.node [64,120932,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [2,120900,467977,1593992,3236112,5384230,8949779,10846368,12976960,16256000] (.node [2,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [1,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil) (.node [2,120900,467977,1593992,3236112,5382182,8950803,10846368,12976960,16256000] .nil .nil)) (.node [17,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [4,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil) (.node [64,120900,467977,1593992,3236112,5382182,8949779,10846368,12977088,16256000] .nil .nil))) (.node [272,120900,467977,1593992,5382182,8949779,10846368,12976976,16256000] (.node [160,120900,467977,1593992,3236112,5382310,8949779,12976960,16256000] (.node [128,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil) (.node [160,120900,467977,1594024,3236112,5382182,8949779,12976960,16256000] .nil .nil)) (.node [512,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [272,120900,467977,1593992,5382182,8950035,10846368,12976960,16256000] .nil .nil) (.node [1025,2052,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960] .nil .nil))))
theorem R11aa_ok : tall (refOK cpF 11) R11aa = true := by decide +kernel
def R11ab : Tree := (.node [2112,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16309915] (.node [1025,120900,1593992,3236112,5382182,8949779,10846368,13051721,16650048] (.node [1025,120900,467977,1593992,3236112,5382182,8949779,10846368,13097796,16650048] (.node [1025,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16658278] .nil .nil) (.node [1025,120900,1593992,3236112,5382182,8949779,10846368,12976960,13051721,16395302] .nil .nil)) (.node [2048,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16292883] (.node [1033,120900,1595017,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil) (.node [2052,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16309915] .nil .nil))) (.node [20480,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [3072,120900,470025,1593992,3236112,5382182,8949779,10846368,12976960] (.node [2112,120900,467977,1593992,3236112,5382182,9417755,10846368,12976960,16292883] .nil .nil) (.node [3072,121924,467977,1593992,3236112,5382182,8949779,10846368,12976960] .nil .nil)) (.node [65536,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [36864,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil) (.node [120900,139264,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil))))
theorem R11ab_ok : tall (refOK cpF 11) R11ab = true := by decide +kernel
def R11a : Tree := .node [1025,2112,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960] R11aa R11ab
theorem R11a_ok : tall (refOK cpF 11) R11a = true :=
  tall_node _ _ _ _ R11aa_ok (by decide +kernel) R11ab_ok
def R11ba : Tree := (.node [120900,467977,1593992,3236112,5382182,8388608,8949779,10846368,12976960,16256000] (.node [120900,467977,1593992,1694412,3236112,5382182,8949779,10846368,12976960,16256001] (.node [120900,467977,1048576,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [120900,467977,528384,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil) (.node [120900,467977,1576960,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil)) (.node [120900,467977,1593992,3236112,3275092,5382182,8950803,10846368,12976960,16256000] (.node [120900,467977,1593992,2061961,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil) (.node [120900,467977,1593992,3236112,4325376,5382182,8949779,10846368,12976960,16256000] .nil .nil))) (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16292883,16650064] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256002] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16375519] .nil .nil) (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16277128,16658278] .nil .nil)) (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16309915,16658278] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16309915,16395302] .nil .nil) (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12979008,13097796,16292883] .nil .nil))))
theorem R11ba_ok : tall (refOK cpF 11) R11ba = true := by decide +kernel
def R11bb : Tree := (.node [120900,467977,1593992,3236112,5382182,9417755,10846368,12976960,16292883,16658278] (.node [120900,467977,1593992,3236112,5382182,8949779,10868964,12976960,15181801,16256000] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,13097796,16309915,16650048] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,13097796,16292883,16658278] .nil .nil) (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,13538131,14100335,16256000] .nil .nil)) (.node [120900,467977,1593992,3236112,5382182,8950803,10846368,12976960,16395302] (.node [120900,467977,1593992,3236112,5382182,8949779,10986665,11393271,12976960,16256000] .nil .nil) (.node [120900,467977,1593992,3236112,5382182,8950803,10846368,12976960,16650048] .nil .nil))) (.node [120900,467977,1593992,3275092,5382182,8949779,10846368,12976960,16292883,16477494] (.node [120900,467977,1593992,3236112,5382182,10083039,10846368,12976960,13538131,16256000] (.node [120900,467977,1593992,3236112,5382182,9417755,10846368,13097796,16292883,16650048] .nil .nil) (.node [120900,467977,1593992,3238160,3275092,5382182,8949779,10846368,12976960,16292883] .nil .nil)) (.node [121925,467977,1593992,3236112,5382182,8949779,10846368,12976960,16650048] (.node [121925,467977,1593992,3236112,5382182,8949779,10846368,12976960,16395302] .nil .nil) (.node [121925,1593992,3236112,5382182,8949779,10846368,12976960,13051721,16256000] .nil .nil))))
theorem R11bb_ok : tall (refOK cpF 11) R11bb = true := by decide +kernel
def R11b : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12979008,16292883] R11ba R11bb
theorem R11b_ok : tall (refOK cpF 11) R11b = true :=
  tall_node _ _ _ _ R11ba_ok (by decide +kernel) R11bb_ok
def R11 : Tree := .node [120900,393216,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] R11a R11b
theorem R11_ok : tall (refOK cpF 11) R11 = true :=
  tall_node _ _ _ _ R11a_ok (by decide +kernel) R11b_ok
def T12aaaaaaa : Tree := (.node [2,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16292883,16395302] (.node [2,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,14033766,16256000,16292883] .nil .nil) .nil)
theorem T12aaaaaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaaaaaa = true := by decide +kernel
def T12aaaaaab : Tree := (.node [16,120900,467977,1593992,1694412,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil)
theorem T12aaaaaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaaaaab = true := by decide +kernel
def T12aaaaaa : Tree := .node [6,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16292883] T12aaaaaaa T12aaaaaab
theorem T12aaaaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaaaaa = true :=
  tall_node _ _ _ _ T12aaaaaaa_ok (by decide +kernel) T12aaaaaab_ok
def T12aaaaaba : Tree := (.node [16,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,14033766,16256000,16292883] .nil .nil)
theorem T12aaaaaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaaaaba = true := by decide +kernel
def T12aaaaabb : Tree := (.node [16,120900,467977,1593992,3236112,5382182,10846368,11374771,12976960,16256000,16292883] .nil .nil)
theorem T12aaaaabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaaaabb = true := by decide +kernel
def T12aaaaab : Tree := .node [16,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16292883,16650048] T12aaaaaba T12aaaaabb
theorem T12aaaaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaaaab = true :=
  tall_node _ _ _ _ T12aaaaaba_ok (by decide +kernel) T12aaaaabb_ok
def T12aaaaa : Tree := .node [16,120900,467977,1593992,3236112,5382182,5710895,8949779,10846368,12976960,16256000] T12aaaaaa T12aaaaab
theorem T12aaaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaaaa = true :=
  tall_node _ _ _ _ T12aaaaaa_ok (by decide +kernel) T12aaaaab_ok
def T12aaaabaa : Tree := (.node [18,120900,467977,1593992,3236112,5382182,10846368,12976960,16256000,16292883] .nil .nil)
theorem T12aaaabaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaaabaa = true := by decide +kernel
def T12aaaabab : Tree := (.node [32,120900,467977,1593992,3236112,5382182,8949779,9033815,10846368,12976960,16256000] .nil .nil)
theorem T12aaaabab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaaabab = true := by decide +kernel
def T12aaaaba : Tree := .node [32,120900,467977,1593992,3236112,3275092,5382182,8949779,10846368,12976960,16256000,16292883] T12aaaabaa T12aaaabab
theorem T12aaaaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaaaba = true :=
  tall_node _ _ _ _ T12aaaabaa_ok (by decide +kernel) T12aaaabab_ok
def T12aaaabba : Tree := (.node [34,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16292883] .nil .nil)
theorem T12aaaabba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaaabba = true := by decide +kernel
def T12aaaabbb : Tree := (.node [128,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,13051721,16256000] .nil .nil)
theorem T12aaaabbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaaabbb = true := by decide +kernel
def T12aaaabb : Tree := .node [128,120900,467977,1593992,3236112,5382182,8949779,9033815,10846368,12976960,16256000] T12aaaabba T12aaaabbb
theorem T12aaaabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaaabb = true :=
  tall_node _ _ _ _ T12aaaabba_ok (by decide +kernel) T12aaaabbb_ok
def T12aaaab : Tree := .node [32,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,13051721,16256000] T12aaaaba T12aaaabb
theorem T12aaaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaaab = true :=
  tall_node _ _ _ _ T12aaaaba_ok (by decide +kernel) T12aaaabb_ok
def T12aaaa : Tree := .node [16,120900,467977,1593992,3275092,5382182,8949779,10846368,12976960,16256000,16292883] T12aaaaa T12aaaab
theorem T12aaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaaa = true :=
  tall_node _ _ _ _ T12aaaaa_ok (by decide +kernel) T12aaaab_ok
def T12aaabaaaa : Tree := (.node [160,120900,467977,1593992,3236112,5382182,8949779,12976960,16256000,16292883] .nil .nil)
theorem T12aaabaaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaabaaaa = true := by decide +kernel
def T12aaabaaab : Tree := .nil
theorem T12aaabaaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaabaaab = true := by decide +kernel
def T12aaabaaa : Tree := .node [256,120900,467977,1593992,1694412,3236112,5382182,8949779,10846368,12976960,16256000] T12aaabaaaa T12aaabaaab
theorem T12aaabaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaabaaa = true :=
  tall_node _ _ _ _ T12aaabaaaa_ok (by decide +kernel) T12aaabaaab_ok
def T12aaabaab : Tree := (.node [256,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,14033766,16256000,16292883] .nil .nil)
theorem T12aaabaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaabaab = true := by decide +kernel
def T12aaabaa : Tree := .node [256,120900,467977,1593992,3236112,5382182,5710895,8949779,10846368,12976960,16256000] T12aaabaaa T12aaabaab
theorem T12aaabaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaabaa = true :=
  tall_node _ _ _ _ T12aaabaaa_ok (by decide +kernel) T12aaabaab_ok
def T12aaababa : Tree := (.node [272,120900,467977,1593992,5382182,8949779,10846368,12976960,16256000] .nil .nil)
theorem T12aaababa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaababa = true := by decide +kernel
def T12aaababb : Tree := (.node [320,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16292883] .nil .nil)
theorem T12aaababb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaababb = true := by decide +kernel
def T12aaabab : Tree := .node [272,120900,467977,1593992,5382182,8949779,10846368,12976960,16256000,16292883] T12aaababa T12aaababb
theorem T12aaabab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaabab = true :=
  tall_node _ _ _ _ T12aaababa_ok (by decide +kernel) T12aaababb_ok
def T12aaaba : Tree := .node [256,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16292883,16650048] T12aaabaa T12aaabab
theorem T12aaaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaaba = true :=
  tall_node _ _ _ _ T12aaabaa_ok (by decide +kernel) T12aaabab_ok
def T12aaabbaa : Tree := (.node [1024,120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,16256000] .nil .nil)
theorem T12aaabbaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaabbaa = true := by decide +kernel
def T12aaabbab : Tree := (.node [1025,120900,467977,1593992,1694412,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil)
theorem T12aaabbab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaabbab = true := by decide +kernel
def T12aaabba : Tree := .node [1024,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,14033766,16256000] T12aaabbaa T12aaabbab
theorem T12aaabba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaabba = true :=
  tall_node _ _ _ _ T12aaabbaa_ok (by decide +kernel) T12aaabbab_ok
def T12aaabbba : Tree := (.node [1025,120900,467977,1593992,3236112,5382182,8949779,9033815,10846368,12976960,16256000] .nil .nil)
theorem T12aaabbba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaabbba = true := by decide +kernel
def T12aaabbbb : Tree := (.node [1025,120900,467977,1593992,3236112,5382182,8949779,10846368,10868964,12976960,16256000] .nil .nil)
theorem T12aaabbbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaabbbb = true := by decide +kernel
def T12aaabbb : Tree := .node [1025,120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,16256000] T12aaabbba T12aaabbbb
theorem T12aaabbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaabbb = true :=
  tall_node _ _ _ _ T12aaabbba_ok (by decide +kernel) T12aaabbbb_ok
def T12aaabb : Tree := .node [1025,120900,467977,1593992,3236112,3275092,5382182,8949779,10846368,12976960,16256000] T12aaabba T12aaabbb
theorem T12aaabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaabb = true :=
  tall_node _ _ _ _ T12aaabba_ok (by decide +kernel) T12aaabbb_ok
def T12aaab : Tree := .node [768,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16292883] T12aaaba T12aaabb
theorem T12aaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaab = true :=
  tall_node _ _ _ _ T12aaaba_ok (by decide +kernel) T12aaabb_ok
def T12aaa : Tree := .node [160,120900,467977,1593992,3236112,5382182,8949779,12976960,16256000] T12aaaa T12aaab
theorem T12aaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaa = true :=
  tall_node _ _ _ _ T12aaaa_ok (by decide +kernel) T12aaab_ok
def T12aabaaaaa : Tree := (.node [1025,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,14033766,16256000] .nil .nil)
theorem T12aabaaaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabaaaaa = true := by decide +kernel
def T12aabaaaab : Tree := .nil
theorem T12aabaaaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabaaaab = true := by decide +kernel
def T12aabaaaa : Tree := .node [1025,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16395302] T12aabaaaaa T12aabaaaab
theorem T12aabaaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabaaaa = true :=
  tall_node _ _ _ _ T12aabaaaaa_ok (by decide +kernel) T12aabaaaab_ok
def T12aabaaab : Tree := (.node [1025,120900,1593992,3236112,5382182,8949779,10846368,10986665,12976960,16256000] .nil .nil)
theorem T12aabaaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabaaab = true := by decide +kernel
def T12aabaaa : Tree := .node [1025,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16650048] T12aabaaaa T12aabaaab
theorem T12aabaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabaaa = true :=
  tall_node _ _ _ _ T12aabaaaa_ok (by decide +kernel) T12aabaaab_ok
def T12aabaaba : Tree := (.node [1033,120900,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil)
theorem T12aabaaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabaaba = true := by decide +kernel
def T12aabaabb : Tree := (.node [2048,120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,16256000] .nil .nil)
theorem T12aabaabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabaabb = true := by decide +kernel
def T12aabaab : Tree := .node [2048,120900,467977,1593992,3236112,3275092,5382182,8949779,10846368,12976960,16292883] T12aabaaba T12aabaabb
theorem T12aabaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabaab = true :=
  tall_node _ _ _ _ T12aabaaba_ok (by decide +kernel) T12aabaabb_ok
def T12aabaa : Tree := .node [1025,120900,1593992,3236112,5382182,8949779,10846368,12976960,13051721,16256000] T12aabaaa T12aabaab
theorem T12aabaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabaa = true :=
  tall_node _ _ _ _ T12aabaaa_ok (by decide +kernel) T12aabaab_ok
def T12aababaa : Tree := (.node [2048,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,13538131,16292883] .nil .nil)
theorem T12aababaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aababaa = true := by decide +kernel
def T12aababab : Tree := (.node [2048,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,14033766,16292883] .nil .nil)
theorem T12aababab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aababab = true := by decide +kernel
def T12aababa : Tree := .node [2048,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,14033766,16256000] T12aababaa T12aababab
theorem T12aababa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aababa = true :=
  tall_node _ _ _ _ T12aababaa_ok (by decide +kernel) T12aababab_ok
def T12aababba : Tree := (.node [2112,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16292883] .nil .nil)
theorem T12aababba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aababba = true := by decide +kernel
def T12aababbb : Tree := (.node [120900,120932,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil)
theorem T12aababbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aababbb = true := by decide +kernel
def T12aababb : Tree := .node [3072,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960] T12aababba T12aababbb
theorem T12aababb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aababb = true :=
  tall_node _ _ _ _ T12aababba_ok (by decide +kernel) T12aababbb_ok
def T12aabab : Tree := .node [2052,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16292883] T12aababa T12aababb
theorem T12aabab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabab = true :=
  tall_node _ _ _ _ T12aababa_ok (by decide +kernel) T12aababb_ok
def T12aaba : Tree := .node [2048,120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,16292883] T12aabaa T12aabab
theorem T12aaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaba = true :=
  tall_node _ _ _ _ T12aabaa_ok (by decide +kernel) T12aabab_ok
def T12aabbaaa : Tree := (.node [120900,121156,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil)
theorem T12aabbaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabbaaa = true := by decide +kernel
def T12aabbaab : Tree := (.node [120900,467977,467993,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil)
theorem T12aabbaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabbaab = true := by decide +kernel
def T12aabbaa : Tree := .node [120900,121156,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16292883] T12aabbaaa T12aabbaab
theorem T12aabbaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabbaa = true :=
  tall_node _ _ _ _ T12aabbaaa_ok (by decide +kernel) T12aabbaab_ok
def T12aabbaba : Tree := (.node [120900,467977,523341,1593992,3236112,5382182,5927598,8949779,10846368,12976960,16256000] .nil .nil)
theorem T12aabbaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabbaba = true := by decide +kernel
def T12aabbabb : Tree := (.node [120900,467977,523341,1593992,3236112,5382182,8949779,10846368,12976960,13538131,16256000] .nil .nil)
theorem T12aabbabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabbabb = true := by decide +kernel
def T12aabbab : Tree := .node [120900,467977,523341,1593992,3236112,5382182,8949779,10015387,10846368,12976960,16256000] T12aabbaba T12aabbabb
theorem T12aabbab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabbab = true :=
  tall_node _ _ _ _ T12aabbaba_ok (by decide +kernel) T12aabbabb_ok
def T12aabba : Tree := .node [120900,467977,468105,1593992,3236112,5382182,8949779,10846368,12976960,16256000] T12aabbaa T12aabbab
theorem T12aabba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabba = true :=
  tall_node _ _ _ _ T12aabbaa_ok (by decide +kernel) T12aabbab_ok
def T12aabbbaa : Tree := (.node [120900,467977,1057024,1593992,3236112,5382182,8949779,10846368,12976960,14033766,16256000,16292883] .nil .nil)
theorem T12aabbbaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabbbaa = true := by decide +kernel
def T12aabbbab : Tree := (.node [120900,467977,1593992,1594024,3236112,5382182,8949779,10846368,12976960,16256000,16292883] .nil .nil)
theorem T12aabbbab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabbbab = true := by decide +kernel
def T12aabbba : Tree := .node [120900,467977,1593992,1593994,3236112,5382182,8949779,10846368,12976960,16256000,16292883] T12aabbbaa T12aabbbab
theorem T12aabbba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabbba = true :=
  tall_node _ _ _ _ T12aabbbaa_ok (by decide +kernel) T12aabbbab_ok
def T12aabbbba : Tree := (.node [120900,467977,1593992,1594248,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil)
theorem T12aabbbba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabbbba = true := by decide +kernel
def T12aabbbbb : Tree := (.node [120900,467977,1593992,1595016,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil)
theorem T12aabbbbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabbbbb = true := by decide +kernel
def T12aabbbb : Tree := .node [120900,467977,1593992,1594248,3236112,5382182,8949779,10846368,12976960,16256000,16292883] T12aabbbba T12aabbbbb
theorem T12aabbbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabbbb = true :=
  tall_node _ _ _ _ T12aabbbba_ok (by decide +kernel) T12aabbbbb_ok
def T12aabbb : Tree := .node [120900,467977,1593992,1594056,3236112,5382182,8949779,10846368,12976960,16256000,16292883] T12aabbba T12aabbbb
theorem T12aabbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabbb = true :=
  tall_node _ _ _ _ T12aabbba_ok (by decide +kernel) T12aabbbb_ok
def T12aabb : Tree := .node [120900,467977,523341,1593992,3236112,5382182,8949779,10846368,12976960,14033766,16256000] T12aabba T12aabbb
theorem T12aabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabb = true :=
  tall_node _ _ _ _ T12aabba_ok (by decide +kernel) T12aabbb_ok
def T12aab : Tree := .node [120900,120932,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16292883] T12aaba T12aabb
theorem T12aab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aab = true :=
  tall_node _ _ _ _ T12aaba_ok (by decide +kernel) T12aabb_ok
def T12aa : Tree := .node [1025,120900,467977,1593992,3236112,5382182,8949779,10846368,11374771,12976960,16256000] T12aaa T12aab
theorem T12aa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aa = true :=
  tall_node _ _ _ _ T12aaa_ok (by decide +kernel) T12aab_ok
def T12abaaaaaa : Tree := (.node [120900,467977,1593992,1694412,3145744,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil)
theorem T12abaaaaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abaaaaaa = true := by decide +kernel
def T12abaaaaab : Tree := .nil
theorem T12abaaaaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abaaaaab = true := by decide +kernel
def T12abaaaaa : Tree := .node [120900,467977,1593992,1694412,3236112,3275092,5382182,8949779,10846368,12976960,16256000] T12abaaaaaa T12abaaaaab
theorem T12abaaaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abaaaaa = true :=
  tall_node _ _ _ _ T12abaaaaaa_ok (by decide +kernel) T12abaaaaab_ok
def T12abaaaab : Tree := (.node [120900,467977,1593992,1694412,3236112,3630361,5382182,8949779,10846368,12976960,16256000,16292883] .nil .nil)
theorem T12abaaaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abaaaab = true := by decide +kernel
def T12abaaaa : Tree := .node [120900,467977,1593992,1694412,3236112,3630361,5382182,8949779,10846368,12976960,16256000] T12abaaaaa T12abaaaab
theorem T12abaaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abaaaa = true :=
  tall_node _ _ _ _ T12abaaaaa_ok (by decide +kernel) T12abaaaab_ok
def T12abaaaba : Tree := (.node [120900,467977,1593992,1694412,3236112,3765144,5382182,8949779,10846368,12976960,16256000,16292883] .nil .nil)
theorem T12abaaaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abaaaba = true := by decide +kernel
def T12abaaabb : Tree := (.node [120900,467977,1593992,1694412,3236112,5382182,5710895,8949779,10846368,12976960,16256000] .nil .nil)
theorem T12abaaabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abaaabb = true := by decide +kernel
def T12abaaab : Tree := .node [120900,467977,1593992,1694412,3236112,3800028,5382182,8949779,10846368,12976960,16256000] T12abaaaba T12abaaabb
theorem T12abaaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abaaab = true :=
  tall_node _ _ _ _ T12abaaaba_ok (by decide +kernel) T12abaaabb_ok
def T12abaaa : Tree := .node [120900,467977,1593992,1694412,3236112,3765144,5382182,8949779,10846368,12976960,16256000] T12abaaaa T12abaaab
theorem T12abaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abaaa = true :=
  tall_node _ _ _ _ T12abaaaa_ok (by decide +kernel) T12abaaab_ok
def T12abaabaa : Tree := (.node [120900,467977,1593992,1694412,3236112,5382182,7561526,8949779,10846368,12976960,16256000] .nil .nil)
theorem T12abaabaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abaabaa = true := by decide +kernel
def T12abaabab : Tree := (.node [120900,467977,1593992,1694412,3236112,5382182,8949779,10846368,12976960,13538131,16256000] .nil .nil)
theorem T12abaabab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abaabab = true := by decide +kernel
def T12abaaba : Tree := .node [120900,467977,1593992,1694412,3236112,5382182,8949779,10846368,12976960,13051721,16256000] T12abaabaa T12abaabab
theorem T12abaaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abaaba = true :=
  tall_node _ _ _ _ T12abaabaa_ok (by decide +kernel) T12abaabab_ok
def T12abaabba : Tree := (.node [120900,467977,1593992,1694412,3236112,5382182,8949779,10846368,12976960,16256000,16309915] .nil .nil)
theorem T12abaabba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abaabba = true := by decide +kernel
def T12abaabbb : Tree := (.node [120900,467977,1593992,3145744,3236112,5382182,5710895,8949779,10846368,12976960,16256000] .nil .nil)
theorem T12abaabbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abaabbb = true := by decide +kernel
def T12abaabb : Tree := .node [120900,467977,1593992,1694412,3236112,5382182,8949779,10846368,12976960,16292883,16722953] T12abaabba T12abaabbb
theorem T12abaabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abaabb = true :=
  tall_node _ _ _ _ T12abaabba_ok (by decide +kernel) T12abaabbb_ok
def T12abaab : Tree := .node [120900,467977,1593992,1694412,3236112,5382182,8949779,10846368,12976960,14033766,16256000] T12abaaba T12abaabb
theorem T12abaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abaab = true :=
  tall_node _ _ _ _ T12abaaba_ok (by decide +kernel) T12abaabb_ok
def T12abaa : Tree := .node [120900,467977,1593992,1694412,3236112,5382182,5710895,8949779,10846368,12976960,16256000,16292883] T12abaaa T12abaab
theorem T12abaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abaa = true :=
  tall_node _ _ _ _ T12abaaa_ok (by decide +kernel) T12abaab_ok
def T12ababaaaa : Tree := (.node [120900,467977,1593992,3145744,3236112,5382182,8949779,10846368,12976960,16292883,16650048] .nil .nil)
theorem T12ababaaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12ababaaaa = true := by decide +kernel
def T12ababaaab : Tree := .nil
theorem T12ababaaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12ababaaab = true := by decide +kernel
def T12ababaaa : Tree := .node [120900,467977,1593992,3145744,3275092,5382182,8949779,10846368,12976960,16256000,16292883] T12ababaaaa T12ababaaab
theorem T12ababaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12ababaaa = true :=
  tall_node _ _ _ _ T12ababaaaa_ok (by decide +kernel) T12ababaaab_ok
def T12ababaab : Tree := (.node [120900,467977,1593992,3146769,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil)
theorem T12ababaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12ababaab = true := by decide +kernel
def T12ababaa : Tree := .node [120900,467977,1593992,3145984,3236112,5382182,8949779,10846368,12976960,16292883,16650048] T12ababaaa T12ababaab
theorem T12ababaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12ababaa = true :=
  tall_node _ _ _ _ T12ababaaa_ok (by decide +kernel) T12ababaab_ok
def T12abababa : Tree := (.node [120900,467977,1593992,3236112,3236176,5382182,8949779,10846368,12976960,16256000,16292883] .nil .nil)
theorem T12abababa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abababa = true := by decide +kernel
def T12abababb : Tree := (.node [120900,467977,1593992,3236112,3275092,5382182,5710895,8949779,10846368,12976960,16256000,16292883] .nil .nil)
theorem T12abababb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abababb = true := by decide +kernel
def T12ababab : Tree := .node [120900,467977,1593992,3236112,3275092,5382182,5710895,8949779,10846368,12976960,16256000] T12abababa T12abababb
theorem T12ababab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12ababab = true :=
  tall_node _ _ _ _ T12abababa_ok (by decide +kernel) T12abababb_ok
def T12ababa : Tree := .node [120900,467977,1593992,3147776,3236112,3275092,5382182,8949779,10846368,12976960,16292883] T12ababaa T12ababab
theorem T12ababa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12ababa = true :=
  tall_node _ _ _ _ T12ababaa_ok (by decide +kernel) T12ababab_ok
def T12ababbaa : Tree := (.node [120900,467977,1593992,3236112,3275092,5382182,8949779,10846368,12976960,14033766,16256000,16292883] .nil .nil)
theorem T12ababbaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12ababbaa = true := by decide +kernel
def T12ababbab : Tree := (.node [120900,467977,1593992,3236112,3275092,5382182,8949779,10846368,12976960,16292883,16395302] .nil .nil)
theorem T12ababbab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12ababbab = true := by decide +kernel
def T12ababba : Tree := .node [120900,467977,1593992,3236112,3275092,5382182,8949779,10846368,12976960,16256000,16309915] T12ababbaa T12ababbab
theorem T12ababba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12ababba = true :=
  tall_node _ _ _ _ T12ababbaa_ok (by decide +kernel) T12ababbab_ok
def T12ababbba : Tree := (.node [120900,467977,1593992,3236112,3275092,5382182,9417755,10846368,12976960,16256000,16292883] .nil .nil)
theorem T12ababbba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12ababbba = true := by decide +kernel
def T12ababbbb : Tree := (.node [120900,467977,1593992,3236112,3630361,5382182,5710895,8949779,10846368,12976960,16256000] .nil .nil)
theorem T12ababbbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12ababbbb = true := by decide +kernel
def T12ababbb : Tree := .node [120900,467977,1593992,3236112,3613721,5382182,8949779,10846368,12976960,16256000] T12ababbba T12ababbbb
theorem T12ababbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12ababbb = true :=
  tall_node _ _ _ _ T12ababbba_ok (by decide +kernel) T12ababbbb_ok
def T12ababb : Tree := .node [120900,467977,1593992,3236112,3275092,5382182,8949779,10846368,12976960,16292883,16650048] T12ababba T12ababbb
theorem T12ababb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12ababb = true :=
  tall_node _ _ _ _ T12ababba_ok (by decide +kernel) T12ababbb_ok
def T12abab : Tree := .node [120900,467977,1593992,3236112,3275092,5382182,5927598,8949779,10846368,12976960,16256000,16292883] T12ababa T12ababb
theorem T12abab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abab = true :=
  tall_node _ _ _ _ T12ababa_ok (by decide +kernel) T12ababb_ok
def T12aba : Tree := .node [120900,467977,1593992,3145744,3236112,5382182,8949779,10846368,12976960,14033766,16256000,16292883] T12abaa T12abab
theorem T12aba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aba = true :=
  tall_node _ _ _ _ T12abaa_ok (by decide +kernel) T12abab_ok
def T12abbaaaaa : Tree := (.node [120900,467977,1593992,3236112,3630361,5382182,8949779,10846368,12976960,16256000,16650048] .nil .nil)
theorem T12abbaaaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbaaaaa = true := by decide +kernel
def T12abbaaaab : Tree := .nil
theorem T12abbaaaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbaaaab = true := by decide +kernel
def T12abbaaaa : Tree := .node [120900,467977,1593992,3236112,3630361,5382182,8949779,10846368,12976960,16292883,16650048] T12abbaaaaa T12abbaaaab
theorem T12abbaaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbaaaa = true :=
  tall_node _ _ _ _ T12abbaaaaa_ok (by decide +kernel) T12abbaaaab_ok
def T12abbaaab : Tree := (.node [120900,467977,1593992,3236112,3765144,5382182,5927598,8949779,10846368,12976960,16256000,16292883] .nil .nil)
theorem T12abbaaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbaaab = true := by decide +kernel
def T12abbaaa : Tree := .node [120900,467977,1593992,3236112,3765144,5382182,5710895,8949779,10846368,12976960,16256000] T12abbaaaa T12abbaaab
theorem T12abbaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbaaa = true :=
  tall_node _ _ _ _ T12abbaaaa_ok (by decide +kernel) T12abbaaab_ok
def T12abbaaba : Tree := (.node [120900,467977,1593992,3236112,3765144,5382182,8949779,10846368,12976960,14033766,16256000,16292883] .nil .nil)
theorem T12abbaaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbaaba = true := by decide +kernel
def T12abbaabb : Tree := (.node [120900,467977,1593992,3236112,3765144,5382182,8949779,10846368,12976960,16292883,16650048] .nil .nil)
theorem T12abbaabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbaabb = true := by decide +kernel
def T12abbaab : Tree := .node [120900,467977,1593992,3236112,3765144,5382182,8949779,10846368,12976960,16256000,16309915] T12abbaaba T12abbaabb
theorem T12abbaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbaab = true :=
  tall_node _ _ _ _ T12abbaaba_ok (by decide +kernel) T12abbaabb_ok
def T12abbaa : Tree := .node [120900,467977,1593992,3236112,3765144,5382182,8949779,10846368,11374771,12976960,16256000] T12abbaaa T12abbaab
theorem T12abbaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbaa = true :=
  tall_node _ _ _ _ T12abbaaa_ok (by decide +kernel) T12abbaab_ok
def T12abbabaa : Tree := (.node [120900,467977,1593992,3236112,5382182,5382198,8949779,10846368,12976960,16256000] .nil .nil)
theorem T12abbabaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbabaa = true := by decide +kernel
def T12abbabab : Tree := (.node [120900,467977,1593992,3236112,5382182,5382246,8949779,10846368,12976960,16256000,16292883] .nil .nil)
theorem T12abbabab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbabab = true := by decide +kernel
def T12abbaba : Tree := .node [120900,467977,1593992,3236112,5382182,5382198,8949779,10846368,12976960,16256000,16292883] T12abbabaa T12abbabab
theorem T12abbaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbaba = true :=
  tall_node _ _ _ _ T12abbabaa_ok (by decide +kernel) T12abbabab_ok
def T12abbabba : Tree := (.node [120900,467977,1593992,3236112,5382182,5384230,8949779,10846368,12976960,16292883] .nil .nil)
theorem T12abbabba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbabba = true := by decide +kernel
def T12abbabbb : Tree := (.node [120900,467977,1593992,3236112,5382182,5710895,7824703,8949779,10846368,12976960,16256000] .nil .nil)
theorem T12abbabbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbabbb = true := by decide +kernel
def T12abbabb : Tree := .node [120900,467977,1593992,3236112,5382182,5710895,7561526,8949779,10846368,12976960,16256000] T12abbabba T12abbabbb
theorem T12abbabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbabb = true :=
  tall_node _ _ _ _ T12abbabba_ok (by decide +kernel) T12abbabbb_ok
def T12abbab : Tree := .node [120900,467977,1593992,3236112,5382182,5384230,8949779,10846368,12976960,16256000] T12abbaba T12abbabb
theorem T12abbab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbab = true :=
  tall_node _ _ _ _ T12abbaba_ok (by decide +kernel) T12abbabb_ok
def T12abba : Tree := .node [120900,467977,1593992,3236112,3800028,5382182,8949779,10846368,12976960,16256000,16292883] T12abbaa T12abbab
theorem T12abba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abba = true :=
  tall_node _ _ _ _ T12abbaa_ok (by decide +kernel) T12abbab_ok
def T12abbbaaa : Tree := (.node [120900,467977,1593992,3236112,5382182,5710895,8949779,10015387,10846368,12976960,16256000] .nil .nil)
theorem T12abbbaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbbaaa = true := by decide +kernel
def T12abbbaab : Tree := (.node [120900,467977,1593992,3236112,5382182,5927598,8949779,9033815,10846368,12976960,16256000] .nil .nil)
theorem T12abbbaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbbaab = true := by decide +kernel
def T12abbbaa : Tree := .node [120900,467977,1593992,3236112,5382182,5710895,8949779,10846368,12976960,13538131,16256000] T12abbbaaa T12abbbaab
theorem T12abbbaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbbaa = true :=
  tall_node _ _ _ _ T12abbbaaa_ok (by decide +kernel) T12abbbaab_ok
def T12abbbaba : Tree := (.node [120900,467977,1593992,3236112,5382182,5927598,8949779,10846368,12976960,13538131,16256000] .nil .nil)
theorem T12abbbaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbbaba = true := by decide +kernel
def T12abbbabb : Tree := (.node [120900,467977,1593992,3236112,5382182,7479350,8949779,10846368,12976960,16256000,16292883] .nil .nil)
theorem T12abbbabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbbabb = true := by decide +kernel
def T12abbbab : Tree := .node [120900,467977,1593992,3236112,5382182,7479350,8949779,10846368,12976960,16256000] T12abbbaba T12abbbabb
theorem T12abbbab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbbab = true :=
  tall_node _ _ _ _ T12abbbaba_ok (by decide +kernel) T12abbbabb_ok
def T12abbba : Tree := .node [120900,467977,1593992,3236112,5382182,5927598,8949779,10846368,12976960,13051721,16256000] T12abbbaa T12abbbab
theorem T12abbba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbba = true :=
  tall_node _ _ _ _ T12abbbaa_ok (by decide +kernel) T12abbbab_ok
def T12abbbbaa : Tree := (.node [120900,467977,1593992,3236112,5382182,7561526,8949779,10846368,12976960,15172576,16256000] .nil .nil)
theorem T12abbbbaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbbbaa = true := by decide +kernel
def T12abbbbab : Tree := (.node [120900,467977,1593992,3236112,5382182,7561526,8949779,10846368,12976960,16292883,16650048] .nil .nil)
theorem T12abbbbab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbbbab = true := by decide +kernel
def T12abbbba : Tree := .node [120900,467977,1593992,3236112,5382182,7561526,8949779,10846368,12976960,16292883,16395302] T12abbbbaa T12abbbbab
theorem T12abbbba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbbba = true :=
  tall_node _ _ _ _ T12abbbbaa_ok (by decide +kernel) T12abbbbab_ok
def T12abbbbba : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,8949811,10846368,12976960,16256000] .nil .nil)
theorem T12abbbbba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbbbba = true := by decide +kernel
def T12abbbbbb : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,9033815,10846368,10868964,12976960,16256000] .nil .nil)
theorem T12abbbbbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbbbbb = true := by decide +kernel
def T12abbbbb : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,8950803,10846368,12976960,16256000] T12abbbbba T12abbbbbb
theorem T12abbbbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbbbb = true :=
  tall_node _ _ _ _ T12abbbbba_ok (by decide +kernel) T12abbbbbb_ok
def T12abbbb : Tree := .node [120900,467977,1593992,3236112,5382182,8388610,8949779,10846368,12976960,14033766,16256000,16292883] T12abbbba T12abbbbb
theorem T12abbbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbbb = true :=
  tall_node _ _ _ _ T12abbbba_ok (by decide +kernel) T12abbbbb_ok
def T12abbb : Tree := .node [120900,467977,1593992,3236112,5382182,7561526,8949779,10846368,12976960,14033766,16256000,16292883] T12abbba T12abbbb
theorem T12abbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbb = true :=
  tall_node _ _ _ _ T12abbba_ok (by decide +kernel) T12abbbb_ok
def T12abb : Tree := .node [120900,467977,1593992,3236112,5382182,5710895,8949779,9033815,10846368,12976960,16256000] T12abba T12abbb
theorem T12abb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abb = true :=
  tall_node _ _ _ _ T12abba_ok (by decide +kernel) T12abbb_ok
def T12ab : Tree := .node [120900,467977,1593992,3236112,3630361,5382182,8949779,10846368,12976960,14033766,16256000,16292883] T12aba T12abb
theorem T12ab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12ab = true :=
  tall_node _ _ _ _ T12aba_ok (by decide +kernel) T12abb_ok
def T12a : Tree := .node [120900,467977,1593992,1595017,3236112,5382182,8949779,10846368,12976960,16256000] T12aa T12ab
theorem T12a_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12a = true :=
  tall_node _ _ _ _ T12aa_ok (by decide +kernel) T12ab_ok
def T12baaaaaaa : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,9033815,10846368,10986665,12976960,16256000,16292883] .nil .nil)
theorem T12baaaaaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baaaaaaa = true := by decide +kernel
def T12baaaaaab : Tree := .nil
theorem T12baaaaaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baaaaaab = true := by decide +kernel
def T12baaaaaa : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,9033815,10846368,11374771,12976960,16256000] T12baaaaaaa T12baaaaaab
theorem T12baaaaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baaaaaa = true :=
  tall_node _ _ _ _ T12baaaaaaa_ok (by decide +kernel) T12baaaaaab_ok
def T12baaaaab : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,9033815,10846368,12976960,13051721,16256000] .nil .nil)
theorem T12baaaaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baaaaab = true := by decide +kernel
def T12baaaaa : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,9033815,10846368,11393271,12976960,16256000] T12baaaaaa T12baaaaab
theorem T12baaaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baaaaa = true :=
  tall_node _ _ _ _ T12baaaaaa_ok (by decide +kernel) T12baaaaab_ok
def T12baaaaba : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,9033815,10846368,12976960,14033766,16256000] .nil .nil)
theorem T12baaaaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baaaaba = true := by decide +kernel
def T12baaaabb : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,9033815,10846368,12976960,15172576,16256000] .nil .nil)
theorem T12baaaabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baaaabb = true := by decide +kernel
def T12baaaab : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,9033815,10846368,12976960,14033766,16256000,16292883] T12baaaaba T12baaaabb
theorem T12baaaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baaaab = true :=
  tall_node _ _ _ _ T12baaaaba_ok (by decide +kernel) T12baaaabb_ok
def T12baaaa : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,9033815,10846368,12976960,13051721,16256000,16292883] T12baaaaa T12baaaab
theorem T12baaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baaaa = true :=
  tall_node _ _ _ _ T12baaaaa_ok (by decide +kernel) T12baaaab_ok
def T12baaabaa : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,9417755,10846368,12976960,14033766,16256000,16292883] .nil .nil)
theorem T12baaabaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baaabaa = true := by decide +kernel
def T12baaabab : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,13051721,16256000] .nil .nil)
theorem T12baaabab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baaabab = true := by decide +kernel
def T12baaaba : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,10868964,12976960,16256000,16292883] T12baaabaa T12baaabab
theorem T12baaaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baaaba = true :=
  tall_node _ _ _ _ T12baaabaa_ok (by decide +kernel) T12baaabab_ok
def T12baaabba : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,14033766,16256000,16292883] .nil .nil)
theorem T12baaabba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baaabba = true := by decide +kernel
def T12baaabbb : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,16256000,16309915] .nil .nil)
theorem T12baaabbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baaabbb = true := by decide +kernel
def T12baaabb : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,16256000,16277128] T12baaabba T12baaabbb
theorem T12baaabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baaabb = true :=
  tall_node _ _ _ _ T12baaabba_ok (by decide +kernel) T12baaabbb_ok
def T12baaab : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,14033766,16256000] T12baaaba T12baaabb
theorem T12baaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baaab = true :=
  tall_node _ _ _ _ T12baaaba_ok (by decide +kernel) T12baaabb_ok
def T12baaa : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,9033815,10846368,12976960,16256000,16309915] T12baaaa T12baaab
theorem T12baaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baaa = true :=
  tall_node _ _ _ _ T12baaaa_ok (by decide +kernel) T12baaab_ok
def T12baabaaaa : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,16256000,16650048] .nil .nil)
theorem T12baabaaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baabaaaa = true := by decide +kernel
def T12baabaaab : Tree := .nil
theorem T12baabaaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baabaaab = true := by decide +kernel
def T12baabaaa : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,16292883,16395302] T12baabaaaa T12baabaaab
theorem T12baabaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baabaaa = true :=
  tall_node _ _ _ _ T12baabaaaa_ok (by decide +kernel) T12baabaaab_ok
def T12baabaab : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10083039,10846368,12976960,16256000] .nil .nil)
theorem T12baabaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baabaab = true := by decide +kernel
def T12baabaa : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,16292883,16650048] T12baabaaa T12baabaab
theorem T12baabaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baabaa = true :=
  tall_node _ _ _ _ T12baabaaa_ok (by decide +kernel) T12baabaab_ok
def T12baababa : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,10868964,12976960,13051721,16256000,16292883] .nil .nil)
theorem T12baababa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baababa = true := by decide +kernel
def T12baababb : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,10868964,12976960,16256000,16277128] .nil .nil)
theorem T12baababb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baababb = true := by decide +kernel
def T12baabab : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,10868964,12976960,13538131,16256000,16292883] T12baababa T12baababb
theorem T12baabab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baabab = true :=
  tall_node _ _ _ _ T12baababa_ok (by decide +kernel) T12baababb_ok
def T12baaba : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,10868964,12976960,13051721,16256000] T12baabaa T12baabab
theorem T12baaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baaba = true :=
  tall_node _ _ _ _ T12baabaa_ok (by decide +kernel) T12baabab_ok
def T12baabbaa : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,10986665,12976960,13051721,16256000] .nil .nil)
theorem T12baabbaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baabbaa = true := by decide +kernel
def T12baabbab : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,10986665,12976960,16292883,16395302] .nil .nil)
theorem T12baabbab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baabbab = true := by decide +kernel
def T12baabba : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,10986665,12976960,16256000,16395302] T12baabbaa T12baabbab
theorem T12baabba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baabba = true :=
  tall_node _ _ _ _ T12baabbaa_ok (by decide +kernel) T12baabbab_ok
def T12baabbba : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,11374771,12976960,13051721,16256000,16292883] .nil .nil)
theorem T12baabbba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baabbba = true := by decide +kernel
def T12baabbbb : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,11374771,12976960,16256000,16309915] .nil .nil)
theorem T12baabbbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baabbbb = true := by decide +kernel
def T12baabbb : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,11374771,12976960,14033766,16256000,16292883] T12baabbba T12baabbbb
theorem T12baabbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baabbb = true :=
  tall_node _ _ _ _ T12baabbba_ok (by decide +kernel) T12baabbbb_ok
def T12baabb : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,11374771,12976960,13051721,16256000] T12baabba T12baabbb
theorem T12baabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baabb = true :=
  tall_node _ _ _ _ T12baabba_ok (by decide +kernel) T12baabbb_ok
def T12baab : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,10868964,12976960,16256000,16309915] T12baaba T12baabb
theorem T12baab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baab = true :=
  tall_node _ _ _ _ T12baaba_ok (by decide +kernel) T12baabb_ok
def T12baa : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,16256000,16395302] T12baaa T12baab
theorem T12baa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baa = true :=
  tall_node _ _ _ _ T12baaa_ok (by decide +kernel) T12baab_ok
def T12babaaaaa : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,11393271,12976960,16256000,16292883] .nil .nil)
theorem T12babaaaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babaaaaa = true := by decide +kernel
def T12babaaaab : Tree := .nil
theorem T12babaaaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babaaaab = true := by decide +kernel
def T12babaaaa : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,11919792,12976960,14033766,16256000,16292883] T12babaaaaa T12babaaaab
theorem T12babaaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babaaaa = true :=
  tall_node _ _ _ _ T12babaaaaa_ok (by decide +kernel) T12babaaaab_ok
def T12babaaab : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,11919792,12976960,16292883,16650048] .nil .nil)
theorem T12babaaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babaaab = true := by decide +kernel
def T12babaaa : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,11919792,12976960,16256000,16309915] T12babaaaa T12babaaab
theorem T12babaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babaaa = true :=
  tall_node _ _ _ _ T12babaaaa_ok (by decide +kernel) T12babaaab_ok
def T12babaaba : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,12976976,16256000,16292883] .nil .nil)
theorem T12babaaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babaaba = true := by decide +kernel
def T12babaabb : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,12979008,16256000] .nil .nil)
theorem T12babaabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babaabb = true := by decide +kernel
def T12babaab : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,12977088,16256000] T12babaaba T12babaabb
theorem T12babaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babaab = true :=
  tall_node _ _ _ _ T12babaaba_ok (by decide +kernel) T12babaabb_ok
def T12babaa : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12185875,12976960,14033766,16256000,16292883] T12babaaa T12babaab
theorem T12babaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babaa = true :=
  tall_node _ _ _ _ T12babaaa_ok (by decide +kernel) T12babaab_ok
def T12bababaa : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,13051721,15172576,16256000] .nil .nil)
theorem T12bababaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bababaa = true := by decide +kernel
def T12bababab : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,13538131,14033766,16256000,16292883] .nil .nil)
theorem T12bababab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bababab = true := by decide +kernel
def T12bababa : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,13051721,15181801,16256000] T12bababaa T12bababab
theorem T12bababa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bababa = true :=
  tall_node _ _ _ _ T12bababaa_ok (by decide +kernel) T12bababab_ok
def T12bababba : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,14033766,16256000,16277128] .nil .nil)
theorem T12bababba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bababba = true := by decide +kernel
def T12bababbb : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,14033766,16256000,16395302] .nil .nil)
theorem T12bababbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bababbb = true := by decide +kernel
def T12bababb : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,14033766,16256000,16309915] T12bababba T12bababbb
theorem T12bababb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bababb = true :=
  tall_node _ _ _ _ T12bababba_ok (by decide +kernel) T12bababbb_ok
def T12babab : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,13538131,16292883,16650048] T12bababa T12bababb
theorem T12babab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babab = true :=
  tall_node _ _ _ _ T12bababa_ok (by decide +kernel) T12bababb_ok
def T12baba : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,12979008,16292883] T12babaa T12babab
theorem T12baba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baba = true :=
  tall_node _ _ _ _ T12babaa_ok (by decide +kernel) T12babab_ok
def T12babbaaa : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,14033766,16256000,16658278] .nil .nil)
theorem T12babbaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babbaaa = true := by decide +kernel
def T12babbaab : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,14033766,16292883,16650048] .nil .nil)
theorem T12babbaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babbaab = true := by decide +kernel
def T12babbaa : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,14033766,16292883,16395302] T12babbaaa T12babbaab
theorem T12babbaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babbaa = true :=
  tall_node _ _ _ _ T12babbaaa_ok (by decide +kernel) T12babbaab_ok
def T12babbaba : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,14100335,16256000] .nil .nil)
theorem T12babbaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babbaba = true := by decide +kernel
def T12babbabb : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16277128,16395302] .nil .nil)
theorem T12babbabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babbabb = true := by decide +kernel
def T12babbab : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256064,16292883] T12babbaba T12babbabb
theorem T12babbab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babbab = true :=
  tall_node _ _ _ _ T12babbaba_ok (by decide +kernel) T12babbabb_ok
def T12babba : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,14033766,16292883,16658278] T12babbaa T12babbab
theorem T12babba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babba = true :=
  tall_node _ _ _ _ T12babbaa_ok (by decide +kernel) T12babbab_ok
def T12babbbaa : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16309915,16395302] .nil .nil)
theorem T12babbbaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babbbaa = true := by decide +kernel
def T12babbbab : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976976,16256000] .nil .nil)
theorem T12babbbab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babbbab = true := by decide +kernel
def T12babbba : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16309915,16650048] T12babbbaa T12babbbab
theorem T12babbba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babbba = true :=
  tall_node _ _ _ _ T12babbbaa_ok (by decide +kernel) T12babbbab_ok
def T12babbbba : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12977088,16256000] .nil .nil)
theorem T12babbbba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babbbba = true := by decide +kernel
def T12babbbbb : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12979008,16292883] .nil .nil)
theorem T12babbbbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babbbbb = true := by decide +kernel
def T12babbbb : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12979008,16256000] T12babbbba T12babbbbb
theorem T12babbbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babbbb = true :=
  tall_node _ _ _ _ T12babbbba_ok (by decide +kernel) T12babbbbb_ok
def T12babbb : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976976,16256000,16292883] T12babbba T12babbbb
theorem T12babbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babbb = true :=
  tall_node _ _ _ _ T12babbba_ok (by decide +kernel) T12babbbb_ok
def T12babb : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16292883,16658278] T12babba T12babbb
theorem T12babb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babb = true :=
  tall_node _ _ _ _ T12babba_ok (by decide +kernel) T12babbb_ok
def T12bab : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,14033766,16256000,16650048] T12baba T12babb
theorem T12bab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bab = true :=
  tall_node _ _ _ _ T12baba_ok (by decide +kernel) T12babb_ok
def T12ba : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,11374771,12976960,16292883,16395302] T12baa T12bab
theorem T12ba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12ba = true :=
  tall_node _ _ _ _ T12baa_ok (by decide +kernel) T12bab_ok
def T12bbaaaaaa : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,13097796,16292883,16650048] .nil .nil)
theorem T12bbaaaaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbaaaaaa = true := by decide +kernel
def T12bbaaaaab : Tree := .nil
theorem T12bbaaaaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbaaaaab = true := by decide +kernel
def T12bbaaaaa : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,13538131,14033766,16256000,16292883] T12bbaaaaaa T12bbaaaaab
theorem T12bbaaaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbaaaaa = true :=
  tall_node _ _ _ _ T12bbaaaaaa_ok (by decide +kernel) T12bbaaaaab_ok
def T12bbaaaab : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846624,12976960,16256000,16292883] .nil .nil)
theorem T12bbaaaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbaaaab = true := by decide +kernel
def T12bbaaaa : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846370,12976960,16256000,16292883] T12bbaaaaa T12bbaaaab
theorem T12bbaaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbaaaa = true :=
  tall_node _ _ _ _ T12bbaaaaa_ok (by decide +kernel) T12bbaaaab_ok
def T12bbaaaba : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10868964,10986665,12976960,16256000,16292883] .nil .nil)
theorem T12bbaaaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbaaaba = true := by decide +kernel
def T12bbaaabb : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,11374771,12976960,15172576,16256000] .nil .nil)
theorem T12bbaaabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbaaabb = true := by decide +kernel
def T12bbaaab : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10986665,11374771,12976960,16256000,16292883] T12bbaaaba T12bbaaabb
theorem T12bbaaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbaaab = true :=
  tall_node _ _ _ _ T12bbaaaba_ok (by decide +kernel) T12bbaaabb_ok
def T12bbaaa : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10868964,10986665,12976960,16256000] T12bbaaaa T12bbaaab
theorem T12bbaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbaaa = true :=
  tall_node _ _ _ _ T12bbaaaa_ok (by decide +kernel) T12bbaaab_ok
def T12bbaabaa : Tree := (.node [120900,467977,1593992,3236112,5382182,8949811,10846368,12976960,16256000,16292883] .nil .nil)
theorem T12bbaabaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbaabaa = true := by decide +kernel
def T12bbaabab : Tree := (.node [120900,467977,1593992,3236112,5382182,8950035,10846368,12976960,16256000,16292883] .nil .nil)
theorem T12bbaabab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbaabab = true := by decide +kernel
def T12bbaaba : Tree := .node [120900,467977,1593992,3236112,5382182,8950035,10846368,12976960,16256000] T12bbaabaa T12bbaabab
theorem T12bbaaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbaaba = true :=
  tall_node _ _ _ _ T12bbaabaa_ok (by decide +kernel) T12bbaabab_ok
def T12bbaabba : Tree := (.node [120900,467977,1593992,3236112,5382182,8951827,9033815,10846368,12976960,16256000] .nil .nil)
theorem T12bbaabba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbaabba = true := by decide +kernel
def T12bbaabbb : Tree := (.node [120900,467977,1593992,3236112,5382182,9033815,10846368,10986665,12976960,16256000,16292883] .nil .nil)
theorem T12bbaabbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbaabbb = true := by decide +kernel
def T12bbaabb : Tree := .node [120900,467977,1593992,3236112,5382182,9033815,10015387,10846368,12976960,16256000,16292883] T12bbaabba T12bbaabbb
theorem T12bbaabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbaabb = true :=
  tall_node _ _ _ _ T12bbaabba_ok (by decide +kernel) T12bbaabbb_ok
def T12bbaab : Tree := .node [120900,467977,1593992,3236112,5382182,8950803,10846368,12976960,16256000] T12bbaaba T12bbaabb
theorem T12bbaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbaab = true :=
  tall_node _ _ _ _ T12bbaaba_ok (by decide +kernel) T12bbaabb_ok
def T12bbaa : Tree := .node [120900,467977,1593992,3236112,5382182,8949811,10846368,12976960,16256000] T12bbaaa T12bbaab
theorem T12bbaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbaa = true :=
  tall_node _ _ _ _ T12bbaaa_ok (by decide +kernel) T12bbaab_ok
def T12bbabaaa : Tree := (.node [120900,467977,1593992,3236112,5382182,9033815,10846368,11393271,12976960,16256000,16292883] .nil .nil)
theorem T12bbabaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbabaaa = true := by decide +kernel
def T12bbabaab : Tree := (.node [120900,467977,1593992,3236112,5382182,9033815,10846368,12976960,14033766,16256000,16292883] .nil .nil)
theorem T12bbabaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbabaab = true := by decide +kernel
def T12bbabaa : Tree := .node [120900,467977,1593992,3236112,5382182,9033815,10846368,12976960,13051721,16256000,16292883] T12bbabaaa T12bbabaab
theorem T12bbabaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbabaa = true :=
  tall_node _ _ _ _ T12bbabaaa_ok (by decide +kernel) T12bbabaab_ok
def T12bbababa : Tree := (.node [120900,467977,1593992,3236112,5382182,9417755,10846368,12976960,14033766,16256000,16292883] .nil .nil)
theorem T12bbababa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbababa = true := by decide +kernel
def T12bbababb : Tree := (.node [120900,467977,1593992,3236112,5382182,10015387,10846368,11374771,12976960,16256000,16292883] .nil .nil)
theorem T12bbababb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbababb = true := by decide +kernel
def T12bbabab : Tree := .node [120900,467977,1593992,3236112,5382182,9417755,10846368,12976960,16292883,16650048] T12bbababa T12bbababb
theorem T12bbabab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbabab = true :=
  tall_node _ _ _ _ T12bbababa_ok (by decide +kernel) T12bbababb_ok
def T12bbaba : Tree := .node [120900,467977,1593992,3236112,5382182,9417755,10015387,10846368,12976960,16256000,16292883] T12bbabaa T12bbabab
theorem T12bbaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbaba = true :=
  tall_node _ _ _ _ T12bbabaa_ok (by decide +kernel) T12bbabab_ok
def T12bbabbaa : Tree := (.node [120900,467977,1593992,3236112,5382182,10846368,11374771,12976960,13538131,16256000,16292883] .nil .nil)
theorem T12bbabbaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbabbaa = true := by decide +kernel
def T12bbabbab : Tree := (.node [120900,467977,1593992,3236112,5382198,8949779,10846368,12976960,16256000,16292883] .nil .nil)
theorem T12bbabbab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbabbab = true := by decide +kernel
def T12bbabba : Tree := .node [120900,467977,1593992,3236112,5382198,8949779,10846368,12976960,16256000] T12bbabbaa T12bbabbab
theorem T12bbabba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbabba = true :=
  tall_node _ _ _ _ T12bbabbaa_ok (by decide +kernel) T12bbabbab_ok
def T12bbabbba : Tree := (.node [120900,467977,1593992,3236112,5382310,8949779,10846368,12976960,16256000] .nil .nil)
theorem T12bbabbba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbabbba = true := by decide +kernel
def T12bbabbbb : Tree := (.node [120900,467977,1593992,3236112,5384230,8949779,10846368,12976960,16292883] .nil .nil)
theorem T12bbabbbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbabbbb = true := by decide +kernel
def T12bbabbb : Tree := .node [120900,467977,1593992,3236112,5384230,8949779,10846368,12976960,16256000] T12bbabbba T12bbabbbb
theorem T12bbabbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbabbb = true :=
  tall_node _ _ _ _ T12bbabbba_ok (by decide +kernel) T12bbabbbb_ok
def T12bbabb : Tree := .node [120900,467977,1593992,3236112,5382246,8949779,10846368,12976960,16256000,16292883] T12bbabba T12bbabbb
theorem T12bbabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbabb = true :=
  tall_node _ _ _ _ T12bbabba_ok (by decide +kernel) T12bbabbb_ok
def T12bbab : Tree := .node [120900,467977,1593992,3236112,5382182,10015387,10846368,12976960,13538131,16256000,16292883] T12bbaba T12bbabb
theorem T12bbab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbab = true :=
  tall_node _ _ _ _ T12bbaba_ok (by decide +kernel) T12bbabb_ok
def T12bba : Tree := .node [120900,467977,1593992,3236112,5382182,9033815,10846368,11374771,12976960,16256000,16292883] T12bbaa T12bbab
theorem T12bba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bba = true :=
  tall_node _ _ _ _ T12bbaa_ok (by decide +kernel) T12bbab_ok
def T12bbbaaaaa : Tree := (.node [120900,467977,1593992,3236114,5382182,8949779,10846368,12976960,16256000,16292883] .nil .nil)
theorem T12bbbaaaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbaaaaa = true := by decide +kernel
def T12bbbaaaab : Tree := .nil
theorem T12bbbaaaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbaaaab = true := by decide +kernel
def T12bbbaaaa : Tree := .node [120900,467977,1593992,3236176,5382182,8949779,10846368,12976960,16256000,16292883] T12bbbaaaaa T12bbbaaaab
theorem T12bbbaaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbaaaa = true :=
  tall_node _ _ _ _ T12bbbaaaaa_ok (by decide +kernel) T12bbbaaaab_ok
def T12bbbaaab : Tree := (.node [120900,467977,1593992,3275092,3630361,5382182,8949779,10846368,12976960,16256000,16292883] .nil .nil)
theorem T12bbbaaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbaaab = true := by decide +kernel
def T12bbbaaa : Tree := .node [120900,467977,1593992,3275092,3630361,5382182,8949779,10846368,12976960,16256000] T12bbbaaaa T12bbbaaab
theorem T12bbbaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbaaa = true :=
  tall_node _ _ _ _ T12bbbaaaa_ok (by decide +kernel) T12bbbaaab_ok
def T12bbbaaba : Tree := (.node [120900,467977,1593992,3765144,5382182,7561526,8949779,10846368,12976960,16256000] .nil .nil)
theorem T12bbbaaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbaaba = true := by decide +kernel
def T12bbbaabb : Tree := (.node [120900,467977,1594024,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil)
theorem T12bbbaabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbaabb = true := by decide +kernel
def T12bbbaab : Tree := .node [120900,467977,1593994,3236112,5382182,8949779,10846368,12976960,16256000,16292883] T12bbbaaba T12bbbaabb
theorem T12bbbaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbaab = true :=
  tall_node _ _ _ _ T12bbbaaba_ok (by decide +kernel) T12bbbaabb_ok
def T12bbbaa : Tree := .node [120900,467977,1593992,3275092,5382182,7561526,8949779,10846368,12976960,16256000,16292883] T12bbbaaa T12bbbaab
theorem T12bbbaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbaa = true :=
  tall_node _ _ _ _ T12bbbaaa_ok (by decide +kernel) T12bbbaab_ok
def T12bbbabaa : Tree := (.node [120900,467977,1594056,3236112,5382182,8949779,10846368,12976960,16256000,16292883] .nil .nil)
theorem T12bbbabaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbabaa = true := by decide +kernel
def T12bbbabab : Tree := (.node [120900,467977,1594248,3236112,5382182,8949779,10846368,12976960,16256000,16292883] .nil .nil)
theorem T12bbbabab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbabab = true := by decide +kernel
def T12bbbaba : Tree := .node [120900,467977,1594248,3236112,5382182,8949779,10846368,12976960,16256000] T12bbbabaa T12bbbabab
theorem T12bbbaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbaba = true :=
  tall_node _ _ _ _ T12bbbabaa_ok (by decide +kernel) T12bbbabab_ok
def T12bbbabba : Tree := (.node [120900,467977,1595017,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil)
theorem T12bbbabba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbabba = true := by decide +kernel
def T12bbbabbb : Tree := (.node [120900,467993,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil)
theorem T12bbbabbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbabbb = true := by decide +kernel
def T12bbbabb : Tree := .node [120900,467979,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16292883] T12bbbabba T12bbbabbb
theorem T12bbbabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbabb = true :=
  tall_node _ _ _ _ T12bbbabba_ok (by decide +kernel) T12bbbabbb_ok
def T12bbbab : Tree := .node [120900,467977,1595016,3236112,5382182,8949779,10846368,12976960,16256000] T12bbbaba T12bbbabb
theorem T12bbbab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbab = true :=
  tall_node _ _ _ _ T12bbbaba_ok (by decide +kernel) T12bbbabb_ok
def T12bbba : Tree := .node [120900,467977,1594024,3236112,5382182,8949779,10846368,12976960,16256000,16292883] T12bbbaa T12bbbab
theorem T12bbba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbba = true :=
  tall_node _ _ _ _ T12bbbaa_ok (by decide +kernel) T12bbbab_ok
def T12bbbbaaa : Tree := (.node [120900,468105,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil)
theorem T12bbbbaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbbaaa = true := by decide +kernel
def T12bbbbaab : Tree := (.node [120900,470025,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil)
theorem T12bbbbaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbbaab = true := by decide +kernel
def T12bbbbaa : Tree := .node [120900,468233,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16292883] T12bbbbaaa T12bbbbaab
theorem T12bbbbaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbbaa = true :=
  tall_node _ _ _ _ T12bbbbaaa_ok (by decide +kernel) T12bbbbaab_ok
def T12bbbbaba : Tree := (.node [120900,1593992,3236112,3630361,5382182,9417755,10846368,12976960,16256000,16292883] .nil .nil)
theorem T12bbbbaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbbaba = true := by decide +kernel
def T12bbbbabb : Tree := (.node [120902,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16292883] .nil .nil)
theorem T12bbbbabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbbabb = true := by decide +kernel
def T12bbbbab : Tree := .node [120900,1593992,3236112,5382182,5710895,9417755,10846368,12976960,16256000,16292883] T12bbbbaba T12bbbbabb
theorem T12bbbbab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbbab = true :=
  tall_node _ _ _ _ T12bbbbaba_ok (by decide +kernel) T12bbbbabb_ok
def T12bbbba : Tree := .node [120900,470025,1593992,3236112,5382182,8949779,10846368,12976960,16292883] T12bbbbaa T12bbbbab
theorem T12bbbba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbba = true :=
  tall_node _ _ _ _ T12bbbbaa_ok (by decide +kernel) T12bbbbab_ok
def T12bbbbbaa : Tree := (.node [120932,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil)
theorem T12bbbbbaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbbbaa = true := by decide +kernel
def T12bbbbbab : Tree := (.node [121156,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil)
theorem T12bbbbbab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbbbab = true := by decide +kernel
def T12bbbbba : Tree := .node [120932,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16292883] T12bbbbbaa T12bbbbbab
theorem T12bbbbba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbbba = true :=
  tall_node _ _ _ _ T12bbbbbaa_ok (by decide +kernel) T12bbbbbab_ok
def T12bbbbbba : Tree := (.node [121924,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil)
theorem T12bbbbbba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbbbba = true := by decide +kernel
def T12bbbbbbb : Tree := (.node [467977,1593992,3236112,3275092,5382182,8949779,10846368,12976960,13097796,16256000,16292883] .nil .nil)
theorem T12bbbbbbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbbbbb = true := by decide +kernel
def T12bbbbbb : Tree := .node [121925,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] T12bbbbbba T12bbbbbbb
theorem T12bbbbbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbbbb = true :=
  tall_node _ _ _ _ T12bbbbbba_ok (by decide +kernel) T12bbbbbbb_ok
def T12bbbbb : Tree := .node [121156,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16292883] T12bbbbba T12bbbbbb
theorem T12bbbbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbbb = true :=
  tall_node _ _ _ _ T12bbbbba_ok (by decide +kernel) T12bbbbbb_ok
def T12bbbb : Tree := .node [120916,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16292883] T12bbbba T12bbbbb
theorem T12bbbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbb = true :=
  tall_node _ _ _ _ T12bbbba_ok (by decide +kernel) T12bbbbb_ok
def T12bbb : Tree := .node [120900,467993,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16292883] T12bbba T12bbbb
theorem T12bbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbb = true :=
  tall_node _ _ _ _ T12bbba_ok (by decide +kernel) T12bbbb_ok
def T12bb : Tree := .node [120900,467977,1593992,3236112,7561526,8949779,10846368,12976960,14033766,16256000,16292883] T12bba T12bbb
theorem T12bb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bb = true :=
  tall_node _ _ _ _ T12bba_ok (by decide +kernel) T12bbb_ok
def T12b : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,13097796,14033766,16256000,16292883] T12ba T12bb
theorem T12b_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12b = true :=
  tall_node _ _ _ _ T12ba_ok (by decide +kernel) T12bb_ok
def T12 : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,9033815,10846368,10986665,12976960,16256000] T12a T12b
theorem T12_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12 = true :=
  tall_node _ _ _ _ T12a_ok (by decide +kernel) T12b_ok
def R12aaaaa : Tree := (.node [3,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [1,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [1,120900,467977,1593992,3236112,3275092,5382182,8949779,10846368,12976960,16256000] (.node [1,120900,467977,1593992,3145744,3236112,5382182,8949779,10846368,12976960,16256000] (.node [1,120900,467977,1593992,1694412,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil) (.node [1,120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,16256000] (.node [1,120900,467977,1593992,3236112,3630361,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil)) (.node [2,120900,467977,523341,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [2,2048,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [1,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16292883,16722953] .nil .nil) .nil) (.node [2,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16277128] .nil .nil))) (.node [4,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16277128] (.node [4,120900,467977,1593992,3236112,3630361,5382182,8949779,10846368,12976960,16256000] (.node [4,120900,467977,523341,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [4,2048,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil) (.node [4,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,13051721,16256000] (.node [4,120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,16256000] .nil .nil) .nil)) (.node [8,1025,120900,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [6,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [4,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16292883,16722953] .nil .nil) .nil) (.node [8,2048,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil))))
theorem R12aaaaa_ok : tall (refOK cpF 12) R12aaaaa = true := by decide +kernel
def R12aaaaba : Tree := (.node [16,256,120900,467977,1593992,5382182,8949779,10846368,12976960,16256000] (.node [8,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16292883,16722953] (.node [8,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,15172576,16256000] (.node [8,120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,16256000] .nil .nil) .nil) (.node [9,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [9,120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,16256000] .nil .nil) .nil)) (.node [16,120900,467977,1593992,3236112,5382182,8949779,10846384,12976960,16256000] (.node [16,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [16,120900,467977,1593992,3145744,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil) (.node [16,120900,467977,1593992,3236112,5382198,8949779,10846368,12976960,16256000] .nil .nil)))
theorem R12aaaaba_ok : tall (refOK cpF 12) R12aaaaba = true := by decide +kernel
def R12aaaabb : Tree := (.node [17,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [16,120900,467993,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [16,120900,467977,1594008,3236112,5382182,8949779,10846368,12976960,16256000] (.node [16,120900,467977,1593992,3765144,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil) (.node [16,120916,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil)) (.node [32,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16292883,16722953] (.node [32,128,120900,467977,1593992,3236112,5382182,8949779,12976960,16256000] (.node [18,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil) (.node [32,120900,467977,1593992,3236112,5382182,8949779,10986665,12976960,16256000] .nil .nil)))
theorem R12aaaabb_ok : tall (refOK cpF 12) R12aaaabb = true := by decide +kernel
def R12aaaab : Tree := .node [16,120900,467977,1593992,3275092,5382182,8949779,10846368,12976960,16256000] R12aaaaba R12aaaabb
theorem R12aaaab_ok : tall (refOK cpF 12) R12aaaab = true :=
  tall_node _ _ _ _ R12aaaaba_ok (by decide +kernel) R12aaaabb_ok
def R12aaaa : Tree := .node [8,120900,467977,523341,1593992,3236112,5382182,8949779,10846368,12976960,16256000] R12aaaaa R12aaaab
theorem R12aaaa_ok : tall (refOK cpF 12) R12aaaa = true :=
  tall_node _ _ _ _ R12aaaaa_ok (by decide +kernel) R12aaaab_ok
def R12aaabaa : Tree := (.node [34,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [32,120900,467977,1594024,3236112,5382182,8949779,10846368,12976960,16256000] (.node [32,120900,467977,1593992,3236144,5382182,8949779,10846368,12976960,16256000] (.node [32,120900,467977,1593992,3236112,5382182,8949811,10846368,12976960,16256000] .nil .nil) .nil) (.node [32,120932,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [32,120900,468009,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil)) (.node [64,120900,467977,523341,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [64,2048,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [36,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil) (.node [64,120900,467977,1593992,3145744,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil)))
theorem R12aaabaa_ok : tall (refOK cpF 12) R12aaabaa = true := by decide +kernel
def R12aaabab : Tree := (.node [128,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16292883,16722953] (.node [64,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16292883,16722953] (.node [64,120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,16256000] (.node [64,120900,467977,1593992,3236112,5382182,5710895,8949779,10846368,12976960,16256000] .nil .nil) .nil) (.node [68,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [64,120900,467977,1593992,3236112,5382182,9417755,10846368,12976960,16256000,16292883] .nil .nil) .nil)) (.node [128,120900,467977,1593992,3236112,5382182,8949779,11374771,12976960,16256000] (.node [128,120900,467977,1593992,3236112,5382182,8949779,10868964,12976960,16256000] (.node [128,120900,467977,1593992,3236112,5382182,8949779,10846368,12977088,16256000] .nil .nil) .nil) (.node [128,120900,467977,1593992,3236112,5382182,8949907,10846368,12976960,16256000] .nil .nil)))
theorem R12aaabab_ok : tall (refOK cpF 12) R12aaabab = true := by decide +kernel
def R12aaaba : Tree := .node [64,120900,467977,1593992,3236112,3630361,5382182,8949779,10846368,12976960,16256000] R12aaabaa R12aaabab
theorem R12aaaba_ok : tall (refOK cpF 12) R12aaaba = true :=
  tall_node _ _ _ _ R12aaabaa_ok (by decide +kernel) R12aaabab_ok
def R12aaabbaa : Tree := (.node [128,121028,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [128,120900,468105,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [128,120900,467977,1593992,3236240,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil) (.node [160,120900,467977,1593992,3236112,5382182,5927598,8949779,12976960,16256000] (.node [136,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil))
theorem R12aaabbaa_ok : tall (refOK cpF 12) R12aaabbaa = true := by decide +kernel
def R12aaabbab : Tree := (.node [256,120900,467977,1593992,3236112,5382438,8949779,10846368,12976960,16256000] (.node [256,120900,467977,1593992,3236112,5382182,8950035,10846368,12976960,16256000] (.node [256,120900,467977,1593992,3145744,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil) (.node [256,120900,467977,1593992,3630361,5382182,8949779,10846368,12976960,16256000] .nil .nil))
theorem R12aaabbab_ok : tall (refOK cpF 12) R12aaabbab = true := by decide +kernel
def R12aaabba : Tree := .node [160,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] R12aaabbaa R12aaabbab
theorem R12aaabba_ok : tall (refOK cpF 12) R12aaabba = true :=
  tall_node _ _ _ _ R12aaabbaa_ok (by decide +kernel) R12aaabbab_ok
def R12aaabbb : Tree := (.node [272,120900,467977,1593992,5382182,8949779,10846368,12976960,13538131,16256000] (.node [256,121156,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [256,120900,468233,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [256,120900,467977,1594248,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil) (.node [272,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil)) (.node [512,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16292883,16722953] (.node [512,2048,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [320,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil) (.node [520,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil)))
theorem R12aaabbb_ok : tall (refOK cpF 12) R12aaabbb = true := by decide +kernel
def R12aaabb : Tree := .node [256,120900,467977,1593992,5382182,7561526,8949779,10846368,12976960,16256000] R12aaabba R12aaabbb
theorem R12aaabb_ok : tall (refOK cpF 12) R12aaabb = true :=
  tall_node _ _ _ _ R12aaabba_ok (by decide +kernel) R12aaabbb_ok
def R12aaab : Tree := .node [128,120900,467977,1593992,3236112,5382310,8949779,10846368,12976960,16256000] R12aaaba R12aaabb
theorem R12aaab_ok : tall (refOK cpF 12) R12aaab = true :=
  tall_node _ _ _ _ R12aaaba_ok (by decide +kernel) R12aaabb_ok
def R12aaa : Tree := .node [32,120900,467977,1593992,3236112,5382182,8949779,12976960,15172576,16256000] R12aaaa R12aaab
theorem R12aaa_ok : tall (refOK cpF 12) R12aaa = true :=
  tall_node _ _ _ _ R12aaaa_ok (by decide +kernel) R12aaab_ok
def R12aabaaaa : Tree := (.node [1024,2048,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960] (.node [768,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [640,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil) (.node [1024,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16650048] (.node [1024,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16395302] .nil .nil) .nil))
theorem R12aabaaaa_ok : tall (refOK cpF 12) R12aabaaaa = true := by decide +kernel
def R12aabaaab : Tree := (.node [1024,121924,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [1024,120900,467977,1595016,3236112,5382182,8949779,10846368,12976960,16256000] (.node [1024,120900,467977,1593992,3237136,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil) (.node [1025,2048,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960] .nil .nil))
theorem R12aabaaab_ok : tall (refOK cpF 12) R12aabaaab = true := by decide +kernel
def R12aabaaa : Tree := .node [1024,120900,467977,1593992,3236112,5383206,8949779,10846368,12976960,16256000] R12aabaaaa R12aabaaab
theorem R12aabaaa_ok : tall (refOK cpF 12) R12aabaaa = true :=
  tall_node _ _ _ _ R12aabaaaa_ok (by decide +kernel) R12aabaaab_ok
def R12aabaaba : Tree := (.node [1025,120900,467977,1593992,3236112,5382182,8949779,10846368,12977985,16256000] (.node [1025,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16292883,16722953] (.node [1025,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256001] .nil .nil) .nil) (.node [1025,120900,467977,1593992,3236112,5382182,8950803,10846368,12976960,16256000] (.node [1025,120900,467977,1593992,3236112,5382182,8949779,10847393,12976960,16256000] .nil .nil) .nil))
theorem R12aabaaba_ok : tall (refOK cpF 12) R12aabaaba = true := by decide +kernel
def R12aabaabb : Tree := (.node [1025,121925,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [1025,120900,467977,1595017,3236112,5382182,8949779,10846368,12976960,16256000] (.node [1025,120900,467977,1593992,3237137,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil) (.node [1032,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil))
theorem R12aabaabb_ok : tall (refOK cpF 12) R12aabaabb = true := by decide +kernel
def R12aabaab : Tree := .node [1025,120900,467977,1593992,3236112,5383207,8949779,10846368,12976960,16256000] R12aabaaba R12aabaabb
theorem R12aabaab_ok : tall (refOK cpF 12) R12aabaab = true :=
  tall_node _ _ _ _ R12aabaaba_ok (by decide +kernel) R12aabaabb_ok
def R12aabaa : Tree := .node [1025,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,13097796,16256000] R12aabaaa R12aabaab
theorem R12aabaa_ok : tall (refOK cpF 12) R12aabaa = true :=
  tall_node _ _ _ _ R12aabaaa_ok (by decide +kernel) R12aabaab_ok
def R12aababa : Tree := (.node [2048,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,13051721,16256000] (.node [2048,120900,467977,1593992,2061961,3236112,5382182,8949779,10846368,12976960,16256000] (.node [2048,120900,467977,470025,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [1033,120900,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16309915] .nil .nil) .nil) (.node [2048,120900,467977,1593992,3236112,5382182,8949779,9033815,10846368,12976960,16256000] (.node [2048,120900,467977,1593992,3236112,5382182,5503078,8949779,10846368,12976960,16256000] .nil .nil) .nil)) (.node [2048,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16277128] (.node [2048,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,14570440,16256000] (.node [2048,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,14331959,16256000] .nil .nil) .nil) (.node [2048,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16395302] .nil .nil)))
theorem R12aababa_ok : tall (refOK cpF 12) R12aababa = true := by decide +kernel
def R12aababba : Tree := (.node [2048,120900,467977,1593992,3236112,5382182,8949779,10848416,12976960,16256000] (.node [2048,120900,467977,1593992,3236112,5382182,8949779,10846368,12979008,16256000] (.node [2048,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16309915] .nil .nil) .nil) (.node [2048,120900,467977,1593992,3236112,5382182,8951827,10846368,12976960,16256000] .nil .nil))
theorem R12aababba_ok : tall (refOK cpF 12) R12aababba = true := by decide +kernel
def R12aababbb : Tree := (.node [2048,120900,467977,1593992,3238160,5382182,8949779,10846368,12976960,16256000] (.node [2048,120900,467977,1593992,3236112,5384230,8949779,10846368,12976960,16256000] (.node [2048,120900,467977,1593992,3236112,5382182,9417755,10846368,12976960,16292883] .nil .nil) .nil) (.node [2048,120900,467977,1596040,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil))
theorem R12aababbb_ok : tall (refOK cpF 12) R12aababbb = true := by decide +kernel
def R12aababb : Tree := .node [2048,120900,467977,1593992,3236112,5382182,9033815,10846368,12976960,16292883] R12aababba R12aababbb
theorem R12aababb_ok : tall (refOK cpF 12) R12aababb = true :=
  tall_node _ _ _ _ R12aababba_ok (by decide +kernel) R12aababbb_ok
def R12aabab : Tree := .node [2048,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16277128] R12aababa R12aababb
theorem R12aabab_ok : tall (refOK cpF 12) R12aabab = true :=
  tall_node _ _ _ _ R12aababa_ok (by decide +kernel) R12aababb_ok
def R12aaba : Tree := .node [1033,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] R12aabaa R12aabab
theorem R12aaba_ok : tall (refOK cpF 12) R12aaba = true :=
  tall_node _ _ _ _ R12aabaa_ok (by decide +kernel) R12aabab_ok
def R12aabbaa : Tree := (.node [3072,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [2052,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [2048,120900,470025,1593992,3236112,5382182,8949779,10846368,12976960,16292883] (.node [2048,120900,470025,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil) (.node [3072,120900,467977,523341,1593992,3236112,5382182,8949779,10846368,12976960] (.node [2112,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil)) (.node [20480,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,13051721,16256000] (.node [20480,120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,16256000] (.node [20480,120900,467977,1593992,3236112,3630361,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil) (.node [20480,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16277128] .nil .nil)))
theorem R12aabbaa_ok : tall (refOK cpF 12) R12aabbaa = true := by decide +kernel
def R12aabbab : Tree := (.node [22528,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16277128] (.node [20608,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [20488,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [20484,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil) (.node [22528,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil)) (.node [36864,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,13051721,16256000] (.node [36864,120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,16256000] (.node [36864,120900,467977,1593992,3236112,3630361,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil) (.node [36864,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16277128] .nil .nil)))
theorem R12aabbab_ok : tall (refOK cpF 12) R12aabbab = true := by decide +kernel
def R12aabba : Tree := .node [20480,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16292883,16722953] R12aabbaa R12aabbab
theorem R12aabba_ok : tall (refOK cpF 12) R12aabba = true :=
  tall_node _ _ _ _ R12aabbaa_ok (by decide +kernel) R12aabbab_ok
def R12aabbba : Tree := (.node [53248,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [36928,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [36880,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [36865,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil) (.node [53248,120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,16256000] (.node [38912,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16292883,16722953] .nil .nil) .nil)) (.node [65536,120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,16256000] (.node [65536,120900,467977,1593992,3236112,3630361,5382182,8949779,10846368,12976960,16256000] (.node [55296,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil) (.node [65536,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,13051721,16256000] .nil .nil)))
theorem R12aabbba_ok : tall (refOK cpF 12) R12aabbba = true := by decide +kernel
def R12aabbbb : Tree := (.node [65600,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [65540,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [65537,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [65536,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16292883,16722953] .nil .nil) .nil) (.node [65544,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil)) (.node [73728,120900,467977,1593992,3236112,3275092,5382182,8949779,10846368,12976960,16256000] (.node [67584,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16292883,16722953] (.node [67584,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16292883] .nil .nil) .nil) (.node [73728,120900,467977,1593992,3236112,3630361,5382182,8949779,10846368,12976960,16256000] .nil .nil)))
theorem R12aabbbb_ok : tall (refOK cpF 12) R12aabbbb = true := by decide +kernel
def R12aabbb : Tree := .node [65536,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16277128] R12aabbba R12aabbbb
theorem R12aabbb_ok : tall (refOK cpF 12) R12aabbb = true :=
  tall_node _ _ _ _ R12aabbba_ok (by decide +kernel) R12aabbbb_ok
def R12aabb : Tree := .node [36864,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16292883,16722953] R12aabba R12aabbb
theorem R12aabb_ok : tall (refOK cpF 12) R12aabb = true :=
  tall_node _ _ _ _ R12aabba_ok (by decide +kernel) R12aabbb_ok
def R12aab : Tree := .node [2048,120900,467977,1596040,3236112,5382182,8949779,10846368,12976960,16292883] R12aaba R12aabb
theorem R12aab_ok : tall (refOK cpF 12) R12aab = true :=
  tall_node _ _ _ _ R12aaba_ok (by decide +kernel) R12aabb_ok
def R12aa : Tree := .node [576,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] R12aaa R12aab
theorem R12aa_ok : tall (refOK cpF 12) R12aa = true :=
  tall_node _ _ _ _ R12aaa_ok (by decide +kernel) R12aab_ok
def R12abaaaa : Tree := (.node [81920,120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,16256000] (.node [73736,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [73728,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16292883,16722953] (.node [73728,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil) (.node [81920,120900,467977,1593992,3236112,3630361,5382182,8949779,10846368,12976960,16256000] (.node [73984,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil)) (.node [81920,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16277128] (.node [81920,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [81920,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,13051721,16256000] .nil .nil) .nil) (.node [81920,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16292883,16722953] .nil .nil)))
theorem R12abaaaa_ok : tall (refOK cpF 12) R12abaaaa = true := by decide +kernel
def R12abaaab : Tree := (.node [98304,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [90112,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [86016,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [81936,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil) (.node [98304,120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,16256000] (.node [98304,120900,467977,1593992,3236112,3630361,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil)) (.node [98368,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [98304,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16292883,16722953] (.node [98304,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16277128] .nil .nil) .nil) (.node [98432,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil)))
theorem R12abaaab_ok : tall (refOK cpF 12) R12abaaab = true := by decide +kernel
def R12abaaa : Tree := .node [81924,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] R12abaaaa R12abaaab
theorem R12abaaa_ok : tall (refOK cpF 12) R12abaaa = true :=
  tall_node _ _ _ _ R12abaaaa_ok (by decide +kernel) R12abaaab_ok
def R12abaabaa : Tree := (.node [120900,121924,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [120900,121028,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [120900,120916,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil) (.node [120900,139264,467977,1593992,3236112,3630361,5382182,8949779,10846368,12976960,16256000] (.node [120900,121925,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil))
theorem R12abaabaa_ok : tall (refOK cpF 12) R12abaabaa = true := by decide +kernel
def R12abaabab : Tree := (.node [120900,139272,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [120900,139268,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [120900,139264,467977,1593992,3236112,5382182,8949779,10846368,12976960,16292883,16722953] .nil .nil) .nil) (.node [120900,139296,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil))
theorem R12abaabab_ok : tall (refOK cpF 12) R12abaabab = true := by decide +kernel
def R12abaaba : Tree := .node [120900,139264,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,16256000] R12abaabaa R12abaabab
theorem R12abaaba_ok : tall (refOK cpF 12) R12abaaba = true :=
  tall_node _ _ _ _ R12abaabaa_ok (by decide +kernel) R12abaabab_ok
def R12abaabb : Tree := (.node [120900,327681,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [120900,327680,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,16256000] (.node [120900,327680,467977,1593992,3236112,3630361,5382182,8949779,10846368,12976960,16256000] (.node [120900,204800,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil) (.node [120900,327680,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil)) (.node [120900,393216,467977,1593992,3236112,3630361,5382182,8949779,10846368,12976960,16256000] (.node [120900,360448,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [120900,327712,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil) (.node [120900,393216,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,16256000] .nil .nil)))
theorem R12abaabb_ok : tall (refOK cpF 12) R12abaabb = true := by decide +kernel
def R12abaab : Tree := .node [120900,140288,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] R12abaaba R12abaabb
theorem R12abaab_ok : tall (refOK cpF 12) R12abaab = true :=
  tall_node _ _ _ _ R12abaaba_ok (by decide +kernel) R12abaabb_ok
def R12abaa : Tree := .node [102400,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] R12abaaa R12abaab
theorem R12abaa_ok : tall (refOK cpF 12) R12abaa = true :=
  tall_node _ _ _ _ R12abaaa_ok (by decide +kernel) R12abaab_ok
def R12ababaaa : Tree := (.node [120900,394240,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [120900,393472,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [120900,393280,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil) (.node [120900,458752,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [120900,401408,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil))
theorem R12ababaaa_ok : tall (refOK cpF 12) R12ababaaa = true := by decide +kernel
def R12ababaab : Tree := (.node [120900,467977,470025,1593992,3236112,5382182,8949779,10846368,12976960,16292883] (.node [120900,467977,470025,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [120900,467977,468233,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil) (.node [120900,467977,523341,1593992,1694412,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil))
theorem R12ababaab_ok : tall (refOK cpF 12) R12ababaab = true := by decide +kernel
def R12ababaa : Tree := .node [120900,467977,468009,1593992,3236112,5382182,8949779,10846368,12976960,16256000] R12ababaaa R12ababaab
theorem R12ababaa_ok : tall (refOK cpF 12) R12ababaa = true :=
  tall_node _ _ _ _ R12ababaaa_ok (by decide +kernel) R12ababaab_ok
def R12ababab : Tree := (.node [120900,467977,528400,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [120900,467977,523341,1593992,3236112,5382182,8949779,10846368,12976960,16292883,16722953] (.node [120900,467977,523341,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16374852] (.node [120900,467977,523341,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16277128] .nil .nil) .nil) (.node [120900,467977,528384,1593992,3236112,5382182,8949779,10015387,10846368,12976960,16256000] (.node [120900,467977,528384,1593992,3236112,3630361,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil)) (.node [120900,467977,1048576,1593992,3145744,3236112,5382182,8949779,10846368,12976960,16256000] (.node [120900,467977,561152,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [120900,467977,528512,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil) (.node [120900,467977,1048576,1593992,3236112,3630361,5382182,8949779,10846368,12976960,16256000] .nil .nil)))
theorem R12ababab_ok : tall (refOK cpF 12) R12ababab = true := by decide +kernel
def R12ababa : Tree := .node [120900,467977,523341,1593992,3236112,5382182,5503078,8949779,10846368,12976960,16256000] R12ababaa R12ababab
theorem R12ababa_ok : tall (refOK cpF 12) R12ababa = true :=
  tall_node _ _ _ _ R12ababaa_ok (by decide +kernel) R12ababab_ok
def R12ababbaa : Tree := (.node [120900,467977,1048580,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [120900,467977,1048578,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [120900,467977,1048576,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil) (.node [120900,467977,1049088,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [120900,467977,1048584,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil))
theorem R12ababbaa_ok : tall (refOK cpF 12) R12ababbaa = true := by decide +kernel
def R12ababbab : Tree := (.node [120900,467977,1064960,1593992,3236112,3630361,5382182,8949779,10846368,12976960,16256000] (.node [120900,467977,1057024,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [120900,467977,1056772,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil) (.node [120900,467977,1064960,1593992,3236112,5382182,7561526,8949779,10846368,12976960,16256000] .nil .nil))
theorem R12ababbab_ok : tall (refOK cpF 12) R12ababbab = true := by decide +kernel
def R12ababba : Tree := .node [120900,467977,1056768,1593992,3236112,5382182,8949779,10846368,12976960,16256000] R12ababbaa R12ababbab
theorem R12ababba_ok : tall (refOK cpF 12) R12ababba = true :=
  tall_node _ _ _ _ R12ababbaa_ok (by decide +kernel) R12ababbab_ok
def R12ababbba : Tree := (.node [120900,467977,1064976,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [120900,467977,1064968,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [120900,467977,1064960,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil) (.node [120900,467977,1069056,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil))
theorem R12ababbba_ok : tall (refOK cpF 12) R12ababbba = true := by decide +kernel
def R12ababbbb : Tree := (.node [120900,467977,1187840,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [120900,467977,1130496,1593992,3236112,5382182,8949779,10846368,12976960,16256000] (.node [120900,467977,1122304,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil) (.node [120900,467977,1572864,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil))
theorem R12ababbbb_ok : tall (refOK cpF 12) R12ababbbb = true := by decide +kernel
def R12ababbb : Tree := .node [120900,467977,1073152,1593992,3236112,5382182,8949779,10846368,12976960,16256000] R12ababbba R12ababbbb
theorem R12ababbb_ok : tall (refOK cpF 12) R12ababbb = true :=
  tall_node _ _ _ _ R12ababbba_ok (by decide +kernel) R12ababbbb_ok
def R12ababb : Tree := .node [120900,467977,1064960,1593992,3236112,5382182,8949779,10015387,10846368,12976960,16256000] R12ababba R12ababbb
theorem R12ababb_ok : tall (refOK cpF 12) R12ababb = true :=
  tall_node _ _ _ _ R12ababba_ok (by decide +kernel) R12ababbb_ok
def R12abab : Tree := .node [120900,467977,1048576,1593992,3236112,5382182,8949779,10015387,10846368,12976960,16256000] R12ababa R12ababb
theorem R12abab_ok : tall (refOK cpF 12) R12abab = true :=
  tall_node _ _ _ _ R12ababa_ok (by decide +kernel) R12ababb_ok
def R12aba : Tree := .node [120900,393217,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] R12abaa R12abab
theorem R12aba_ok : tall (refOK cpF 12) R12aba = true :=
  tall_node _ _ _ _ R12abaa_ok (by decide +kernel) R12abab_ok
def R12abbaaa : Tree := (.node [120900,467977,1593992,1694412,3236112,5382182,8949779,9033815,10846368,12976960,16256000] (.node [120900,467977,1593992,1594024,3236112,5382182,8949779,10846368,12976960,16256000] (.node [120900,467977,1593992,1594008,3236112,5382182,8949779,10846368,12976960,16256000] (.node [120900,467977,1574912,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil) (.node [120900,467977,1593992,1694412,3236112,5382182,5503078,8949779,10846368,12976960,16256000] (.node [120900,467977,1593992,1596040,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil)) (.node [120900,467977,1593992,1694412,3236112,5382182,8949779,10083039,10846368,12976960,16256000] (.node [120900,467977,1593992,1694412,3236112,5382182,8949779,10015387,10846368,12976960,16256000] (.node [120900,467977,1593992,1694412,3236112,5382182,8949779,9417755,10846368,12976960,16256000] .nil .nil) .nil) (.node [120900,467977,1593992,1694412,3236112,5382182,8949779,10846368,12185875,12976960,16256000] .nil .nil)))
theorem R12abbaaa_ok : tall (refOK cpF 12) R12abbaaa = true := by decide +kernel
def R12abbaab : Tree := (.node [120900,467977,1593992,2096845,3236112,5382182,8949779,10846368,12976960,16256000] (.node [120900,467977,1593992,1694412,3236112,5382182,9033815,10846368,12976960,16256000,16292883] (.node [120900,467977,1593992,1694412,3236112,5382182,8949779,10846368,12976960,16256000,16374852] (.node [120900,467977,1593992,1694412,3236112,5382182,8949779,10846368,12976960,16256000,16346384] .nil .nil) .nil) (.node [120900,467977,1593992,2061961,3236112,5382182,8949779,10846368,12976960,16292883,16722953] (.node [120900,467977,1593992,2061961,3236112,5382182,8949779,10846368,12976960,15172576,16256000] .nil .nil) .nil)) (.node [120900,467977,1593992,2162720,3236112,5382182,8949779,10846368,12976960,16256000] (.node [120900,467977,1593992,2162704,3236112,5382182,8949779,10846368,12976960,16256000] (.node [120900,467977,1593992,2097152,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil) (.node [120900,467977,1593992,2162816,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil)))
theorem R12abbaab_ok : tall (refOK cpF 12) R12abbaab = true := by decide +kernel
def R12abbaa : Tree := .node [120900,467977,1593992,1694412,3236112,5382182,8949779,10846368,12976960,14331959,16256000] R12abbaaa R12abbaab
theorem R12abbaa_ok : tall (refOK cpF 12) R12abbaa = true :=
  tall_node _ _ _ _ R12abbaaa_ok (by decide +kernel) R12abbaab_ok
def R12abbaba : Tree := (.node [120900,467977,1593992,3145728,3236112,5382182,8949779,10846368,12976960,16256000] (.node [120900,467977,1593992,2195456,3236112,5382182,8949779,10846368,12976960,16256000] (.node [120900,467977,1593992,2179072,3236112,5382182,8949779,10846368,12976960,16256000] (.node [120900,467977,1593992,2170880,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil) (.node [120900,467977,1593992,3145728,3145744,3236112,5382182,8949779,10846368,12976960,16256000] (.node [120900,467977,1593992,2424832,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil)) (.node [120900,467977,1593992,3145744,3236112,5382182,8949779,9417755,10846368,12976960,16256000] (.node [120900,467977,1593992,3145744,3236112,3630361,5382182,8949779,10846368,12976960,16256000] (.node [120900,467977,1593992,3145744,3236112,3275092,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil) (.node [120900,467977,1593992,3145744,3236112,5382182,8949779,10846368,12976960,13097796,16256000] .nil .nil)))
theorem R12abbaba_ok : tall (refOK cpF 12) R12abbaba = true := by decide +kernel
def R12abbabb : Tree := (.node [120900,467977,1593992,3145984,3236112,5382182,8949779,10846368,12976960,16256000] (.node [120900,467977,1593992,3145744,3275092,5382182,8949779,10846368,12976960,16256000] (.node [120900,467977,1593992,3145744,3236112,5382182,8949779,10846368,12976960,16256016] (.node [120900,467977,1593992,3145744,3236112,5382182,8949779,10846368,12976960,16256000,16374852] .nil .nil) .nil) (.node [120900,467977,1593992,3145744,3765144,5382182,8949779,10846368,12976960,16256000] .nil .nil)) (.node [120900,467977,1593992,3153920,3236112,5382182,8949779,10846368,12976960,16256000] (.node [120900,467977,1593992,3147776,3236112,5382182,8949779,10846368,12976960,16256000] (.node [120900,467977,1593992,3146752,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil) (.node [120900,467977,1593992,3162112,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil)))
theorem R12abbabb_ok : tall (refOK cpF 12) R12abbabb = true := by decide +kernel
def R12abbab : Tree := .node [120900,467977,1593992,3145744,3236112,5382182,8949779,10846368,12976960,14033766,16256000] R12abbaba R12abbabb
theorem R12abbab_ok : tall (refOK cpF 12) R12abbab = true :=
  tall_node _ _ _ _ R12abbaba_ok (by decide +kernel) R12abbabb_ok
def R12abba : Tree := .node [120900,467977,1593992,2162944,3236112,5382182,8949779,10846368,12976960,16256000] R12abbaa R12abbab
theorem R12abba_ok : tall (refOK cpF 12) R12abba = true :=
  tall_node _ _ _ _ R12abbaa_ok (by decide +kernel) R12abbab_ok
def R12abbbaa : Tree := (.node [120900,467977,1593992,3236112,3238160,5382182,8949779,10846368,12976960,16292883] (.node [120900,467977,1593992,3236112,3237136,5382182,8949779,10846368,12976960,16256000] (.node [120900,467977,1593992,3236112,3236240,5382182,8949779,10846368,12976960,16256000] (.node [120900,467977,1593992,3236112,3236144,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,3238160,5382182,8949779,10846368,12976960,16256000] (.node [120900,467977,1593992,3236112,3237137,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil)) (.node [120900,467977,1593992,3236112,3275092,5382182,8949779,10015387,10846368,12976960,16256000] (.node [120900,467977,1593992,3236112,3275092,3630361,5382182,8949779,10846368,12976960,16256000] (.node [120900,467977,1593992,3236112,3266644,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,3275092,5382182,8949779,10846368,12976960,16292883,16722953] .nil .nil)))
theorem R12abbbaa_ok : tall (refOK cpF 12) R12abbbaa = true := by decide +kernel
def R12abbbab : Tree := (.node [120900,467977,1593992,3236112,3630361,5382182,8949779,10846368,12976960,16292883,16722953] (.node [120900,467977,1593992,3236112,3630361,5382182,8949779,10846368,12976960,13097796,16256000] (.node [120900,467977,1593992,3236112,3630361,5382182,5503078,8949779,10846368,12976960,16256000] (.node [120900,467977,1593992,3236112,3630361,4159385,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,3630361,5382182,8949779,10846368,12976960,16256000,16346384] .nil .nil)) (.node [120900,467977,1593992,3236112,3765144,5382182,8949779,10846368,12976960,16292883,16395302] (.node [120900,467977,1593992,3236112,3691160,5382182,8949779,10846368,12976960,16256000] (.node [120900,467977,1593992,3236112,3669341,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,3765144,5382182,8949779,10846368,12976960,16292883,16722953] .nil .nil)))
theorem R12abbbab_ok : tall (refOK cpF 12) R12abbbab = true := by decide +kernel
def R12abbba : Tree := .node [120900,467977,1593992,3236112,3630361,3669341,5382182,8949779,10846368,12976960,16256000] R12abbbaa R12abbbab
theorem R12abbba_ok : tall (refOK cpF 12) R12abbba = true :=
  tall_node _ _ _ _ R12abbbaa_ok (by decide +kernel) R12abbbab_ok
def R12abbbbaa : Tree := (.node [120900,467977,1593992,3236112,4325632,5382182,8949779,10846368,12976960,16256000] (.node [120900,467977,1593992,3236112,4325408,5382182,8949779,10846368,12976960,16256000] (.node [120900,467977,1593992,3236112,4159385,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,4587520,5382182,8949779,10846368,12976960,16256000] (.node [120900,467977,1593992,3236112,4333568,5382182,8949779,10846368,12976960,16256000] .nil .nil) .nil))
theorem R12abbbbaa_ok : tall (refOK cpF 12) R12abbbbaa = true := by decide +kernel
def R12abbbbab : Tree := (.node [120900,467977,1593992,3236112,5243907,5382182,8949779,10846368,12976960,16256000] (.node [120900,467977,1593992,3236112,5243904,5382182,8949779,10846368,12976960,16256000] (.node [120900,467977,1593992,3236112,5242880,5382182,8949779,10846368,12976960,16256000,16277128] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5373952,5382182,8949779,10846368,12976960,16256000] .nil .nil))
theorem R12abbbbab_ok : tall (refOK cpF 12) R12abbbbab = true := by decide +kernel
def R12abbbba : Tree := .node [120900,467977,1593992,3236112,5242880,5382182,8949779,10846368,12976960,16256000] R12abbbbaa R12abbbbab
theorem R12abbbba_ok : tall (refOK cpF 12) R12abbbba = true :=
  tall_node _ _ _ _ R12abbbbaa_ok (by decide +kernel) R12abbbbab_ok
def R12abbbbb : Tree := (.node [120900,467977,1593992,3236112,5382182,5503078,8949779,10846368,12976960,13051721,16256000] (.node [120900,467977,1593992,3236112,5382182,5383207,8949779,10846368,12976960,16256000] (.node [120900,467977,1593992,3236112,5382182,5383206,8949779,10846368,12976960,16256000] (.node [120900,467977,1593992,3236112,5382182,5382438,8949779,10846368,12976960,16256000] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5382182,5503078,8949779,10015387,10846368,12976960,16256000] .nil .nil)) (.node [120900,467977,1593992,3236112,5382182,5710895,8949779,10846368,12976960,13051721,16256000] (.node [120900,467977,1593992,3236112,5382182,5503078,8949779,10846368,12976960,16292883,16722953] (.node [120900,467977,1593992,3236112,5382182,5503078,8949779,10846368,12976960,16256000,16277128] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5382182,5710895,8949779,10846368,12976960,14033766,16256000] .nil .nil)))
theorem R12abbbbb_ok : tall (refOK cpF 12) R12abbbbb = true := by decide +kernel
def R12abbbb : Tree := .node [120900,467977,1593992,3236112,5382182,5382310,8949779,10846368,12976960,16256000] R12abbbba R12abbbbb
theorem R12abbbb_ok : tall (refOK cpF 12) R12abbbb = true :=
  tall_node _ _ _ _ R12abbbba_ok (by decide +kernel) R12abbbbb_ok
def R12abbb : Tree := .node [120900,467977,1593992,3236112,3800028,5382182,8949779,10846368,12976960,16256000] R12abbba R12abbbb
theorem R12abbb_ok : tall (refOK cpF 12) R12abbb = true :=
  tall_node _ _ _ _ R12abbba_ok (by decide +kernel) R12abbbb_ok
def R12abb : Tree := .node [120900,467977,1593992,3162128,3236112,5382182,8949779,10846368,12976960,16256000] R12abba R12abbb
theorem R12abb_ok : tall (refOK cpF 12) R12abb = true :=
  tall_node _ _ _ _ R12abba_ok (by decide +kernel) R12abbb_ok
def R12ab : Tree := .node [120900,467977,1572872,1593992,3236112,5382182,8949779,10846368,12976960,16292883,16722953] R12aba R12abb
theorem R12ab_ok : tall (refOK cpF 12) R12ab = true :=
  tall_node _ _ _ _ R12aba_ok (by decide +kernel) R12abb_ok
def R12a : Tree := .node [73728,120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,16256000] R12aa R12ab
theorem R12a_ok : tall (refOK cpF 12) R12a = true :=
  tall_node _ _ _ _ R12aa_ok (by decide +kernel) R12ab_ok
def R12baaaaa : Tree := (.node [120900,467977,1593992,3236112,5382182,7340032,8949779,10846368,12976960,16256000] (.node [120900,467977,1593992,3236112,5382182,5927598,8949779,10846368,12976960,16292883,16722953] (.node [120900,467977,1593992,3236112,5382182,5927598,8949779,10846368,12976960,16292883,16650048] (.node [120900,467977,1593992,3236112,5382182,5766255,8949779,10846368,12976960,16256000] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5382182,6256303,8949779,10846368,12976960,16256000] (.node [120900,467977,1593992,3236112,5382182,6028014,8949779,10846368,12976960,16256000] .nil .nil) .nil)) (.node [120900,467977,1593992,3236112,5382182,7600502,8949779,10846368,12976960,16256000] (.node [120900,467977,1593992,3236112,5382182,7561526,8949779,10846368,12976960,13051721,16256000] (.node [120900,467977,1593992,3236112,5382182,7561526,8949779,9033815,10846368,12976960,16256000] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5382182,7824703,8949779,10846368,12976960,16256000] .nil .nil)))
theorem R12baaaaa_ok : tall (refOK cpF 12) R12baaaaa = true := by decide +kernel
def R12baaaaba : Tree := (.node [120900,467977,1593992,3236112,5382182,8388609,8949779,10846368,12976960,16256000] (.node [120900,467977,1593992,3236112,5382182,8090558,8949779,10846368,12976960,16256000,16292883] (.node [120900,467977,1593992,3236112,5382182,8090558,8949779,10846368,12976960,16256000] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5382182,8388672,8949779,10846368,12976960,16256000] (.node [120900,467977,1593992,3236112,5382182,8388610,8949779,10846368,12976960,16256000] .nil .nil) .nil))
theorem R12baaaaba_ok : tall (refOK cpF 12) R12baaaaba = true := by decide +kernel
def R12baaaabb : Tree := (.node [120900,467977,1593992,3236112,5382182,8421377,8949779,10846368,12976960,16256000] (.node [120900,467977,1593992,3236112,5382182,8421376,8949779,10846368,12976960,16256000] (.node [120900,467977,1593992,3236112,5382182,8421376,8949779,10846368,12976960,15172576,16256000] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5382182,8421504,8949779,10846368,12976960,16256000] .nil .nil))
theorem R12baaaabb_ok : tall (refOK cpF 12) R12baaaabb = true := by decide +kernel
def R12baaaab : Tree := .node [120900,467977,1593992,3236112,5382182,8389120,8949779,10846368,12976960,16256000] R12baaaaba R12baaaabb
theorem R12baaaab_ok : tall (refOK cpF 12) R12baaaab = true :=
  tall_node _ _ _ _ R12baaaaba_ok (by decide +kernel) R12baaaabb_ok
def R12baaaa : Tree := .node [120900,467977,1593992,3236112,5382182,7824703,8949779,10846368,12976960,16256000,16292883] R12baaaaa R12baaaab
theorem R12baaaa_ok : tall (refOK cpF 12) R12baaaa = true :=
  tall_node _ _ _ _ R12baaaaa_ok (by decide +kernel) R12baaaab_ok
def R12baaabaa : Tree := (.node [120900,467977,1593992,3236112,5382182,8650816,8949779,10846368,12976960,16256000] (.node [120900,467977,1593992,3236112,5382182,8650784,8949779,10846368,12976960,16256000] (.node [120900,467977,1593992,3236112,5382182,8650752,8949779,10846368,12976960,16256000] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5382182,8716288,8949779,10846368,12976960,16256000] (.node [120900,467977,1593992,3236112,5382182,8683520,8949779,10846368,12976960,16256000] .nil .nil) .nil))
theorem R12baaabaa_ok : tall (refOK cpF 12) R12baaabaa = true := by decide +kernel
def R12baaabab : Tree := (.node [120900,467977,1593992,3236112,5382182,8916992,8949779,10846368,12976960,16256000] (.node [120900,467977,1593992,3236112,5382182,8914944,9033815,10846368,12976960,16292883] (.node [120900,467977,1593992,3236112,5382182,8912896,8949779,10846368,12976960,16256000] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5382182,8949779,8951827,10846368,12976960,16256000] .nil .nil))
theorem R12baaabab_ok : tall (refOK cpF 12) R12baaabab = true := by decide +kernel
def R12baaaba : Tree := .node [120900,467977,1593992,3236112,5382182,8781824,8949779,10846368,12976960,16256000] R12baaabaa R12baaabab
theorem R12baaaba_ok : tall (refOK cpF 12) R12baaaba = true :=
  tall_node _ _ _ _ R12baaabaa_ok (by decide +kernel) R12baaabab_ok
def R12baaabb : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,9417755,10846368,12976960,14033766,16256000] (.node [120900,467977,1593992,3236112,5382182,8949779,9033815,10846368,12976960,16292883,16722953] (.node [120900,467977,1593992,3236112,5382182,8949779,9033815,10846368,12976960,16256000,16374871] (.node [120900,467977,1593992,3236112,5382182,8949779,9033815,10846368,12976960,16256000,16277128] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5382182,8949779,9417755,10846368,12976960,13051721,16256000] .nil .nil)) (.node [120900,467977,1593992,3236112,5382182,8949779,10015387,10083039,10846368,12976960,16256000] (.node [120900,467977,1593992,3236112,5382182,8949779,9961472,10846368,12976960,16256000] (.node [120900,467977,1593992,3236112,5382182,8949779,9436255,10846368,12976960,16256000] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5382182,8949779,10015387,10483355,10846368,12976960,16256000] .nil .nil)))
theorem R12baaabb_ok : tall (refOK cpF 12) R12baaabb = true := by decide +kernel
def R12baaab : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,9033815,10015387,10846368,12976960,16256000] R12baaaba R12baaabb
theorem R12baaab_ok : tall (refOK cpF 12) R12baaab = true :=
  tall_node _ _ _ _ R12baaaba_ok (by decide +kernel) R12baaabb_ok
def R12baaa : Tree := .node [120900,467977,1593992,3236112,5382182,8425472,8949779,10846368,12976960,16256000] R12baaaa R12baaab
theorem R12baaa_ok : tall (refOK cpF 12) R12baaa = true :=
  tall_node _ _ _ _ R12baaaa_ok (by decide +kernel) R12baaab_ok
def R12baabaa : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,16256000,16616608] (.node [120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12440251,12976960,16256000] (.node [120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12440232,12976960,16256000] (.node [120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,11919792,12976960,16256000] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,16256000,16374852] (.node [120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,13097796,16256000] .nil .nil) .nil)) (.node [120900,467977,1593992,3236112,5382182,8949779,10083039,10846368,12976960,16256000,16292883] (.node [120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,16292883,16722953] (.node [120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,16256000,16722953] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5382182,8949779,10483355,10846368,12976960,16256000] .nil .nil)))
theorem R12baabaa_ok : tall (refOK cpF 12) R12baabaa = true := by decide +kernel
def R12baabab : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,10846624,12976960,16256000] (.node [120900,467977,1593992,3236112,5382182,8949779,10518656,10846368,12976960,16256000] (.node [120900,467977,1593992,3236112,5382182,8949779,10487808,10846368,12976960,16256000] (.node [120900,467977,1593992,3236112,5382182,8949779,10485888,10846368,12976960,16256000] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,10846384,12976960,16256000] (.node [120900,467977,1593992,3236112,5382182,8949779,10747904,10846368,12976960,16256000] .nil .nil) .nil)) (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,10868964,10986665,12976960,16256000] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,10848416,12976960,16256000] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,10847392,12976960,16256000] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,10868964,12976960,16292883,16722953] .nil .nil)))
theorem R12baabab_ok : tall (refOK cpF 12) R12baabab = true := by decide +kernel
def R12baaba : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10485792,10846368,12976960,16256000] R12baabaa R12baabab
theorem R12baaba_ok : tall (refOK cpF 12) R12baaba = true :=
  tall_node _ _ _ _ R12baabaa_ok (by decide +kernel) R12baabab_ok
def R12baabba : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,11374771,12976960,16292883,16722953] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,11009261,12976960,16256000] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,10986665,12976960,16292883,16722953] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,10986665,12976960,15172576,16256000] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,11374771,12976960,16256000,16620723] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,11010048,12976960,16256000] .nil .nil) .nil)) (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,11515067,12976960,16256000,16292883] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,11515067,12976960,16256000] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,11393271,12976960,16256000] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,11894960,12976960,16256000] .nil .nil)))
theorem R12baabba_ok : tall (refOK cpF 12) R12baabba = true := by decide +kernel
def R12baabbb : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12186523,12976960,16256000] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12051897,12976960,16256000,16292883] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12051897,12976960,16256000] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,11926004,12976960,16256000,16292883] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12095507,12976960,16256000] .nil .nil)) (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12187991,12976960,16256000,16292883] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12187991,12976960,16256000] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12186523,12976960,16256000,16292883] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12440251,12976960,16256000] .nil .nil)))
theorem R12baabbb_ok : tall (refOK cpF 12) R12baabbb = true := by decide +kernel
def R12baabb : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,11926004,12976960,16256000] R12baabba R12baabbb
theorem R12baabb_ok : tall (refOK cpF 12) R12baabb = true :=
  tall_node _ _ _ _ R12baabba_ok (by decide +kernel) R12baabbb_ok
def R12baab : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,10986665,12976960,14033766,16256000] R12baaba R12baabb
theorem R12baab_ok : tall (refOK cpF 12) R12baab = true :=
  tall_node _ _ _ _ R12baaba_ok (by decide +kernel) R12baabb_ok
def R12baa : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,10868964,12976960,16256000] R12baaa R12baab
theorem R12baa_ok : tall (refOK cpF 12) R12baa = true :=
  tall_node _ _ _ _ R12baaa_ok (by decide +kernel) R12baab_ok
def R12babaaa : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12580521,12976960,16256000] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12448696,12976960,16256000] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12448179,12976960,16256000,16292883] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12448179,12976960,16256000] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12580123,12976960,16256000,16292883] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12580123,12976960,16256000] .nil .nil) .nil)) (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12713984,12976960,16256000] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12583936,12976960,16256000] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12583424,12976960,16256000] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,13051721,14033766,16256000] .nil .nil)))
theorem R12babaaa_ok : tall (refOK cpF 12) R12babaaa = true := by decide +kernel
def R12babaab : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,13051721,16256000,16722953] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,13051721,16256000,16346384] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,13051721,16228518,16256000] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,13051721,14331959,16256000] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,13051721,16256000,16616608] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,13051721,16256000,16395302] .nil .nil) .nil)) (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,13051721,16292883,16722953] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,13051721,16292883,16395302] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,13051721,16256000,16723785] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,13097796,16292883,16722953] .nil .nil)))
theorem R12babaab_ok : tall (refOK cpF 12) R12babaab = true := by decide +kernel
def R12babaa : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,13051721,14100335,16256000] R12babaaa R12babaab
theorem R12babaa_ok : tall (refOK cpF 12) R12babaa = true :=
  tall_node _ _ _ _ R12babaaa_ok (by decide +kernel) R12babaab_ok
def R12bababa : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,13622103,16256000,16292883] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,13612891,16256000] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,13538131,16256000,16686931] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,13107200,16256000] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,13622103,16256000] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,13612891,16256000,16292883] .nil .nil) .nil)) (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,14033766,16292883,16722953] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,14033766,14100335,16256000] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,13631488,16256000] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,14100335,16256000,16292883] .nil .nil)))
theorem R12bababa_ok : tall (refOK cpF 12) R12bababa = true := by decide +kernel
def R12bababb : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,14594935,16256000] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,14570440,16292883,16722953] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,14348991,16256000] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,14331959,16256000,16277128] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,14578670,16256000] .nil .nil)) (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,14660671,16256000] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,14645193,16256000] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,14603227,16256000] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,14670796,16256000] .nil .nil)))
theorem R12bababb_ok : tall (refOK cpF 12) R12bababb = true := by decide +kernel
def R12babab : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,14154598,16256000] R12bababa R12bababb
theorem R12babab_ok : tall (refOK cpF 12) R12babab = true :=
  tall_node _ _ _ _ R12bababa_ok (by decide +kernel) R12bababb_ok
def R12baba : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,13107021,16256000] R12babaa R12babab
theorem R12baba_ok : tall (refOK cpF 12) R12baba = true :=
  tall_node _ _ _ _ R12babaa_ok (by decide +kernel) R12babab_ok
def R12babbaa : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16212816,16256000,16277128] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,15195108,16256000] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,15181801,16256000] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,15172576,16292883,16722953] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16122704,16256000] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,15700979,16256000] .nil .nil) .nil)) (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16228518,16292883,16722953] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16213849,16256000] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16212854,16256000] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16229350,16256000] .nil .nil)))
theorem R12babbaa_ok : tall (refOK cpF 12) R12babbaa = true := by decide +kernel
def R12babbab : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16256016] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16251110,16256000] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16245744,16256000] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16245174,16256000] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16251732,16256000] .nil .nil)) (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16277128,16395302] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16277128,16375500] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16277128,16374852] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16292883,16686931] .nil .nil)))
theorem R12babbab_ok : tall (refOK cpF 12) R12babbab = true := by decide +kernel
def R12babba : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16229551,16256000] R12babbaa R12babbab
theorem R12babba_ok : tall (refOK cpF 12) R12babba = true :=
  tall_node _ _ _ _ R12babbaa_ok (by decide +kernel) R12babbab_ok
def R12babbbaa : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16375500] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16374871] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16351128] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16383316] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16375519] .nil .nil) .nil))
theorem R12babbbaa_ok : tall (refOK cpF 12) R12babbbaa = true := by decide +kernel
def R12babbbab : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16449215] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16432183] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16416430] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16477494] .nil .nil))
theorem R12babbbab_ok : tall (refOK cpF 12) R12babbbab = true := by decide +kernel
def R12babbba : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16383899] R12babbbaa R12babbbab
theorem R12babbba_ok : tall (refOK cpF 12) R12babbba = true :=
  tall_node _ _ _ _ R12babbbaa_ok (by decide +kernel) R12babbbab_ok
def R12babbbb : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16658278] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16637608] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16620723] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16514150] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16650048,16686931] .nil .nil)) (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16703451] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16686931] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16670664] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16722991] .nil .nil)))
theorem R12babbbb_ok : tall (refOK cpF 12) R12babbbb = true := by decide +kernel
def R12babbb : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16511287] R12babbba R12babbbb
theorem R12babbb_ok : tall (refOK cpF 12) R12babbb = true :=
  tall_node _ _ _ _ R12babbba_ok (by decide +kernel) R12babbbb_ok
def R12babb : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16309915] R12babba R12babbb
theorem R12babb_ok : tall (refOK cpF 12) R12babb = true :=
  tall_node _ _ _ _ R12babba_ok (by decide +kernel) R12babbb_ok
def R12bab : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,14680064,16256000] R12baba R12babb
theorem R12bab_ok : tall (refOK cpF 12) R12bab = true :=
  tall_node _ _ _ _ R12baba_ok (by decide +kernel) R12babb_ok
def R12ba : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12442348,12976960,16256000] R12baa R12bab
theorem R12ba_ok : tall (refOK cpF 12) R12ba = true :=
  tall_node _ _ _ _ R12baa_ok (by decide +kernel) R12bab_ok
def R12bbaaaaa : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16741336] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16740176] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16739609] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16748512] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16744073] .nil .nil) .nil))
theorem R12bbaaaaa_ok : tall (refOK cpF 12) R12bbaaaaa = true := by decide +kernel
def R12bbaaaab : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16760667] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16759871] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16756919] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16765928] .nil .nil))
theorem R12bbaaaab_ok : tall (refOK cpF 12) R12bbaaaab = true := by decide +kernel
def R12bbaaaa : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16755878] R12bbaaaaa R12bbaaaab
theorem R12bbaaaa_ok : tall (refOK cpF 12) R12bbaaaa = true :=
  tall_node _ _ _ _ R12bbaaaaa_ok (by decide +kernel) R12bbaaaab_ok
def R12bbaaabaa : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16776269] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16773971] .nil .nil) .nil)
theorem R12bbaaabaa_ok : tall (refOK cpF 12) R12bbaaabaa = true := by decide +kernel
def R12bbaaabab : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256001,16292883,16722953] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256001,16292883] .nil .nil) .nil)
theorem R12bbaaabab_ok : tall (refOK cpF 12) R12bbaaabab = true := by decide +kernel
def R12bbaaaba : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256001] R12bbaaabaa R12bbaaabab
theorem R12bbaaaba_ok : tall (refOK cpF 12) R12bbaaaba = true :=
  tall_node _ _ _ _ R12bbaaabaa_ok (by decide +kernel) R12bbaaabab_ok
def R12bbaaabbaa : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256002] .nil .nil)
theorem R12bbaaabbaa_ok : tall (refOK cpF 12) R12bbaaabbaa = true := by decide +kernel
def R12bbaaabbab : Tree := .nil
theorem R12bbaaabbab_ok : tall (refOK cpF 12) R12bbaaabbab = true := by decide +kernel
def R12bbaaabba : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256002,16292883] R12bbaaabbaa R12bbaaabbab
theorem R12bbaaabba_ok : tall (refOK cpF 12) R12bbaaabba = true :=
  tall_node _ _ _ _ R12bbaaabbaa_ok (by decide +kernel) R12bbaaabbab_ok
def R12bbaaabbb : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256016,16292883] .nil .nil)
theorem R12bbaaabbb_ok : tall (refOK cpF 12) R12bbaaabbb = true := by decide +kernel
def R12bbaaabb : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256016] R12bbaaabba R12bbaaabbb
theorem R12bbaaabb_ok : tall (refOK cpF 12) R12bbaaabb = true :=
  tall_node _ _ _ _ R12bbaaabba_ok (by decide +kernel) R12bbaaabbb_ok
def R12bbaaab : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256001,16722953] R12bbaaaba R12bbaaabb
theorem R12bbaaab_ok : tall (refOK cpF 12) R12bbaaab = true :=
  tall_node _ _ _ _ R12bbaaaba_ok (by decide +kernel) R12bbaaabb_ok
def R12bbaaa : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16768836] R12bbaaaa R12bbaaab
theorem R12bbaaa_ok : tall (refOK cpF 12) R12bbaaa = true :=
  tall_node _ _ _ _ R12bbaaaa_ok (by decide +kernel) R12bbaaab_ok
def R12bbaabaaaa : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256128] .nil .nil)
theorem R12bbaabaaaa_ok : tall (refOK cpF 12) R12bbaabaaaa = true := by decide +kernel
def R12bbaabaaab : Tree := .nil
theorem R12bbaabaaab_ok : tall (refOK cpF 12) R12bbaabaaab = true := by decide +kernel
def R12bbaabaaa : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256256] R12bbaabaaaa R12bbaabaaab
theorem R12bbaabaaa_ok : tall (refOK cpF 12) R12bbaabaaa = true :=
  tall_node _ _ _ _ R12bbaabaaaa_ok (by decide +kernel) R12bbaabaaab_ok
def R12bbaabaab : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16277128,16722953] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16277128,16650048] .nil .nil) .nil)
theorem R12bbaabaab_ok : tall (refOK cpF 12) R12bbaabaab = true := by decide +kernel
def R12bbaabaa : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16277128,16616608] R12bbaabaaa R12bbaabaab
theorem R12bbaabaa_ok : tall (refOK cpF 12) R12bbaabaa = true :=
  tall_node _ _ _ _ R12bbaabaaa_ok (by decide +kernel) R12bbaabaab_ok
def R12bbaabab : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16292883,16432183,16722953] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16292883,16395302,16432183] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16292883,16374871,16722953] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16292883,16477494] .nil .nil))
theorem R12bbaabab_ok : tall (refOK cpF 12) R12bbaabab = true := by decide +kernel
def R12bbaaba : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16292883,16309915,16722953] R12bbaabaa R12bbaabab
theorem R12bbaaba_ok : tall (refOK cpF 12) R12bbaaba = true :=
  tall_node _ _ _ _ R12bbaabaa_ok (by decide +kernel) R12bbaabab_ok
def R12bbaabb : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16292883,16723785] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16292883,16722953,16776269] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16292883,16722953,16759835] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16292883,16686931,16722953] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16292883,16722991] .nil .nil)) (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16346384,16650048] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16309915,16722953] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16292883,16739609] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16374852,16395302] .nil .nil)))
theorem R12bbaabb_ok : tall (refOK cpF 12) R12bbaabb = true := by decide +kernel
def R12bbaab : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16292883,16650048,16686931] R12bbaaba R12bbaabb
theorem R12bbaab_ok : tall (refOK cpF 12) R12bbaab = true :=
  tall_node _ _ _ _ R12bbaaba_ok (by decide +kernel) R12bbaabb_ok
def R12bbaa : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256032] R12bbaaa R12bbaab
theorem R12bbaa_ok : tall (refOK cpF 12) R12bbaa = true :=
  tall_node _ _ _ _ R12bbaaa_ok (by decide +kernel) R12bbaab_ok
def R12bbabaaaa : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16383251,16650048] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16374871,16395302] .nil .nil) .nil)
theorem R12bbabaaaa_ok : tall (refOK cpF 12) R12bbabaaaa = true := by decide +kernel
def R12bbabaaaba : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16395302,16620723] .nil .nil)
theorem R12bbabaaaba_ok : tall (refOK cpF 12) R12bbabaaaba = true := by decide +kernel
def R12bbabaaabb : Tree := .nil
theorem R12bbabaaabb_ok : tall (refOK cpF 12) R12bbabaaabb = true := by decide +kernel
def R12bbabaaab : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976992,16256000] R12bbabaaaba R12bbabaaabb
theorem R12bbabaaab_ok : tall (refOK cpF 12) R12bbabaaab = true :=
  tall_node _ _ _ _ R12bbabaaaba_ok (by decide +kernel) R12bbabaaabb_ok
def R12bbabaaa : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16395302,16616608] R12bbabaaaa R12bbabaaab
theorem R12bbabaaa_ok : tall (refOK cpF 12) R12bbabaaa = true :=
  tall_node _ _ _ _ R12bbabaaaa_ok (by decide +kernel) R12bbabaaab_ok
def R12bbabaabaa : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12977985,16256000] .nil .nil)
theorem R12bbabaabaa_ok : tall (refOK cpF 12) R12bbabaabaa = true := by decide +kernel
def R12bbabaabab : Tree := .nil
theorem R12bbabaabab_ok : tall (refOK cpF 12) R12bbabaabab = true := by decide +kernel
def R12bbabaaba : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,13051721,13538131,16256000] R12bbabaabaa R12bbabaabab
theorem R12bbabaaba_ok : tall (refOK cpF 12) R12bbabaaba = true :=
  tall_node _ _ _ _ R12bbabaabaa_ok (by decide +kernel) R12bbabaabab_ok
def R12bbabaabb : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,13051721,16256000,16650048] .nil .nil)
theorem R12bbabaabb_ok : tall (refOK cpF 12) R12bbabaabb = true := by decide +kernel
def R12bbabaab : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,13051721,14570440,16256000] R12bbabaaba R12bbabaabb
theorem R12bbabaab_ok : tall (refOK cpF 12) R12bbabaab = true :=
  tall_node _ _ _ _ R12bbabaaba_ok (by decide +kernel) R12bbabaabb_ok
def R12bbabaa : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12977984,16256000] R12bbabaaa R12bbabaab
theorem R12bbabaa_ok : tall (refOK cpF 12) R12bbabaa = true :=
  tall_node _ _ _ _ R12bbabaaa_ok (by decide +kernel) R12bbabaab_ok
def R12bbababa : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,13097796,16256000,16292883,16650048] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,13097796,14033766,16256000] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,13051721,16292883,16650048] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,13538131,14033766,16256000] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,13097796,16256000,16650048] .nil .nil) .nil))
theorem R12bbababa_ok : tall (refOK cpF 12) R12bbababa = true := by decide +kernel
def R12bbababba : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,14570440,15172576,16256000] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,14033766,15172576,16256000] .nil .nil) .nil)
theorem R12bbababba_ok : tall (refOK cpF 12) R12bbababba = true := by decide +kernel
def R12bbababbb : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846624,12976960,16256000] .nil .nil)
theorem R12bbababbb_ok : tall (refOK cpF 12) R12bbababbb = true := by decide +kernel
def R12bbababb : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846384,12976960,16256000] R12bbababba R12bbababbb
theorem R12bbababb_ok : tall (refOK cpF 12) R12bbababb = true :=
  tall_node _ _ _ _ R12bbababba_ok (by decide +kernel) R12bbababbb_ok
def R12bbabab : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,13538131,16212816,16256000] R12bbababa R12bbababb
theorem R12bbabab_ok : tall (refOK cpF 12) R12bbabab = true :=
  tall_node _ _ _ _ R12bbababa_ok (by decide +kernel) R12bbababb_ok
def R12bbaba : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,13051721,16256000,16686931] R12bbabaa R12bbabab
theorem R12bbaba_ok : tall (refOK cpF 12) R12bbaba = true :=
  tall_node _ _ _ _ R12bbabaa_ok (by decide +kernel) R12bbabab_ok
def R12bbabbaaaa : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10847393,12976960,16256000] .nil .nil)
theorem R12bbabbaaaa_ok : tall (refOK cpF 12) R12bbabbaaaa = true := by decide +kernel
def R12bbabbaaab : Tree := .nil
theorem R12bbabbaaab_ok : tall (refOK cpF 12) R12bbabbaaab = true := by decide +kernel
def R12bbabbaaa : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10848416,12976960,16256000] R12bbabbaaaa R12bbabbaaab
theorem R12bbabbaaa_ok : tall (refOK cpF 12) R12bbabbaaa = true :=
  tall_node _ _ _ _ R12bbabbaaaa_ok (by decide +kernel) R12bbabbaaab_ok
def R12bbabbaab : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10868964,12976960,16256000,16616608] (.node [120900,467977,1593992,3236112,5382182,8949779,10868964,12976960,16228518,16256000] .nil .nil) .nil)
theorem R12bbabbaab_ok : tall (refOK cpF 12) R12bbabbaab = true := by decide +kernel
def R12bbabbaa : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10868964,12976960,15172576,16256000] R12bbabbaaa R12bbabbaab
theorem R12bbabbaa_ok : tall (refOK cpF 12) R12bbabbaa = true :=
  tall_node _ _ _ _ R12bbabbaaa_ok (by decide +kernel) R12bbabbaab_ok
def R12bbabbab : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10986665,12976960,16256000,16620723] (.node [120900,467977,1593992,3236112,5382182,8949779,10986665,12976960,16256000,16616608] (.node [120900,467977,1593992,3236112,5382182,8949779,10986665,12440232,12976960,16256000] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5382182,8949779,11374771,11919792,12976960,16256000] .nil .nil))
theorem R12bbabbab_ok : tall (refOK cpF 12) R12bbabbab = true := by decide +kernel
def R12bbabba : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10986665,11374771,12976960,16256000] R12bbabbaa R12bbabbab
theorem R12bbabba_ok : tall (refOK cpF 12) R12bbabba = true :=
  tall_node _ _ _ _ R12bbabbaa_ok (by decide +kernel) R12bbabbab_ok
def R12bbabbbaaa : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,12440232,12976960,15172576,16256000] .nil .nil)
theorem R12bbabbbaaa_ok : tall (refOK cpF 12) R12bbabbbaaa = true := by decide +kernel
def R12bbabbbaab : Tree := .nil
theorem R12bbabbbaab_ok : tall (refOK cpF 12) R12bbabbbaab = true := by decide +kernel
def R12bbabbbaa : Tree := .node [120900,467977,1593992,3236112,5382182,8949907,10846368,12976960,16256000] R12bbabbbaaa R12bbabbbaab
theorem R12bbabbbaa_ok : tall (refOK cpF 12) R12bbabbbaa = true :=
  tall_node _ _ _ _ R12bbabbbaaa_ok (by decide +kernel) R12bbabbbaab_ok
def R12bbabbbab : Tree := (.node [120900,467977,1593992,3236112,5382182,8950803,10846368,12976960,16256000,16292883] .nil .nil)
theorem R12bbabbbab_ok : tall (refOK cpF 12) R12bbabbbab = true := by decide +kernel
def R12bbabbba : Tree := .node [120900,467977,1593992,3236112,5382182,8950803,9417755,10846368,12976960,16256000] R12bbabbbaa R12bbabbbab
theorem R12bbabbba_ok : tall (refOK cpF 12) R12bbabbba = true :=
  tall_node _ _ _ _ R12bbabbbaa_ok (by decide +kernel) R12bbabbbab_ok
def R12bbabbbb : Tree := (.node [120900,467977,1593992,3236112,5382182,9033815,10846368,12976960,16256000,16292883,16374871] (.node [120900,467977,1593992,3236112,5382182,9033815,10846368,12976960,14331959,16256000] (.node [120900,467977,1593992,3236112,5382182,9033815,10846368,12976960,13538131,16256000] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5382182,9033815,10846368,12976960,16256000,16432183] .nil .nil))
theorem R12bbabbbb_ok : tall (refOK cpF 12) R12bbabbbb = true := by decide +kernel
def R12bbabbb : Tree := .node [120900,467977,1593992,3236112,5382182,8951827,10846368,12976960,16256000] R12bbabbba R12bbabbbb
theorem R12bbabbb_ok : tall (refOK cpF 12) R12bbabbb = true :=
  tall_node _ _ _ _ R12bbabbba_ok (by decide +kernel) R12bbabbbb_ok
def R12bbabb : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,11919792,12976960,15172576,16256000] R12bbabba R12bbabbb
theorem R12bbabb_ok : tall (refOK cpF 12) R12bbabb = true :=
  tall_node _ _ _ _ R12bbabba_ok (by decide +kernel) R12bbabbb_ok
def R12bbab : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10847392,12976960,16256000] R12bbaba R12bbabb
theorem R12bbab_ok : tall (refOK cpF 12) R12bbab = true :=
  tall_node _ _ _ _ R12bbaba_ok (by decide +kernel) R12bbabb_ok
def R12bba : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16374852,16650048] R12bbaa R12bbab
theorem R12bba_ok : tall (refOK cpF 12) R12bba = true :=
  tall_node _ _ _ _ R12bbaa_ok (by decide +kernel) R12bbab_ok
def R12bbbaaaa : Tree := (.node [120900,467977,1593992,3236112,5382182,9033815,10846368,12976960,16292883,16650048] (.node [120900,467977,1593992,3236112,5382182,9033815,10846368,12976960,16292883,16395302] (.node [120900,467977,1593992,3236112,5382182,9033815,10846368,12976960,16292883,16346384] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5382182,9417755,10015387,10846368,12976960,16256000] (.node [120900,467977,1593992,3236112,5382182,9033815,10846368,12976960,16292883,16722953] .nil .nil) .nil))
theorem R12bbbaaaa_ok : tall (refOK cpF 12) R12bbbaaaa = true := by decide +kernel
def R12bbbaaab : Tree := (.node [120900,467977,1593992,3236112,5382182,9417755,10846368,12976960,16256000,16309915] (.node [120900,467977,1593992,3236112,5382182,9417755,10846368,12976960,16256000,16292883,16759835] (.node [120900,467977,1593992,3236112,5382182,9417755,10846368,12976960,16256000,16292883,16650048] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5382182,9417755,10846368,12976960,16292883,16346384] .nil .nil))
theorem R12bbbaaab_ok : tall (refOK cpF 12) R12bbbaaab = true := by decide +kernel
def R12bbbaaa : Tree := .node [120900,467977,1593992,3236112,5382182,9417755,10846368,12976960,13097796,16256000,16292883] R12bbbaaaa R12bbbaaab
theorem R12bbbaaa_ok : tall (refOK cpF 12) R12bbbaaa = true :=
  tall_node _ _ _ _ R12bbbaaaa_ok (by decide +kernel) R12bbbaaab_ok
def R12bbbaaba : Tree := (.node [120900,467977,1593992,3236112,5382182,10015387,10846368,11374771,12976960,16256000] (.node [120900,467977,1593992,3236112,5382182,9436255,10846368,12976960,16256000,16292883] (.node [120900,467977,1593992,3236112,5382182,9417755,10846368,12976960,16292883,16722953] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5382182,10846368,11374771,12976960,14331959,16256000] (.node [120900,467977,1593992,3236112,5382182,10015387,10846368,12976960,13538131,16256000] .nil .nil) .nil))
theorem R12bbbaaba_ok : tall (refOK cpF 12) R12bbbaaba = true := by decide +kernel
def R12bbbaabbaa : Tree := (.node [120900,467977,1593992,3236112,5382438,8949779,10846368,12976960,16256000] .nil .nil)
theorem R12bbbaabbaa_ok : tall (refOK cpF 12) R12bbbaabbaa = true := by decide +kernel
def R12bbbaabbab : Tree := .nil
theorem R12bbbaabbab_ok : tall (refOK cpF 12) R12bbbaabbab = true := by decide +kernel
def R12bbbaabba : Tree := .node [120900,467977,1593992,3236112,5383206,8949779,10846368,12976960,16256000] R12bbbaabbaa R12bbbaabbab
theorem R12bbbaabba_ok : tall (refOK cpF 12) R12bbbaabba = true :=
  tall_node _ _ _ _ R12bbbaabbaa_ok (by decide +kernel) R12bbbaabbab_ok
def R12bbbaabbb : Tree := (.node [120900,467977,1593992,3236112,5503078,8949779,10846368,12976960,14033766,16256000] .nil .nil)
theorem R12bbbaabbb_ok : tall (refOK cpF 12) R12bbbaabbb = true := by decide +kernel
def R12bbbaabb : Tree := .node [120900,467977,1593992,3236112,5383207,8949779,10846368,12976960,16256000] R12bbbaabba R12bbbaabbb
theorem R12bbbaabb_ok : tall (refOK cpF 12) R12bbbaabb = true :=
  tall_node _ _ _ _ R12bbbaabba_ok (by decide +kernel) R12bbbaabbb_ok
def R12bbbaab : Tree := .node [120900,467977,1593992,3236112,5382182,10846368,12185875,12976960,13538131,16256000] R12bbbaaba R12bbbaabb
theorem R12bbbaab_ok : tall (refOK cpF 12) R12bbbaab = true :=
  tall_node _ _ _ _ R12bbbaaba_ok (by decide +kernel) R12bbbaabb_ok
def R12bbbaa : Tree := .node [120900,467977,1593992,3236112,5382182,9417755,10846368,12976960,16292883,16395302] R12bbbaaa R12bbbaab
theorem R12bbbaa_ok : tall (refOK cpF 12) R12bbbaa = true :=
  tall_node _ _ _ _ R12bbbaaa_ok (by decide +kernel) R12bbbaab_ok
def R12bbbabaa : Tree := (.node [120900,467977,1593992,3236112,5710895,8949779,10846368,12976960,14331959,16256000] (.node [120900,467977,1593992,3236112,5710895,5927598,8949779,10846368,12976960,16256000] (.node [120900,467977,1593992,3236112,5503078,8949779,10846368,12976960,16292883,16395302] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5710895,8949779,10846368,12976960,16292883,16395302] (.node [120900,467977,1593992,3236112,5710895,8949779,10846368,12976960,16256000,16395302] .nil .nil) .nil))
theorem R12bbbabaa_ok : tall (refOK cpF 12) R12bbbabaa = true := by decide +kernel
def R12bbbabab : Tree := (.node [120900,467977,1593992,3236112,7561526,8949779,10846368,12976960,14033766,16256000] (.node [120900,467977,1593992,3236112,5927598,8949779,10846368,12976960,16228518,16256000] (.node [120900,467977,1593992,3236112,5927598,8949779,10846368,12976960,14033766,16256000,16292883] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,7561526,8949779,10846368,12976960,14331959,16256000] .nil .nil))
theorem R12bbbabab_ok : tall (refOK cpF 12) R12bbbabab = true := by decide +kernel
def R12bbbaba : Tree := .node [120900,467977,1593992,3236112,5927598,8949779,10846368,12976960,14033766,16256000] R12bbbabaa R12bbbabab
theorem R12bbbaba_ok : tall (refOK cpF 12) R12bbbaba = true :=
  tall_node _ _ _ _ R12bbbabaa_ok (by decide +kernel) R12bbbabab_ok
def R12bbbabbaaa : Tree := (.node [120900,467977,1593992,3236240,5382182,8949779,10846368,12976960,16256000] .nil .nil)
theorem R12bbbabbaaa_ok : tall (refOK cpF 12) R12bbbabbaaa = true := by decide +kernel
def R12bbbabbaab : Tree := .nil
theorem R12bbbabbaab_ok : tall (refOK cpF 12) R12bbbabbaab = true := by decide +kernel
def R12bbbabbaa : Tree := .node [120900,467977,1593992,3237136,5382182,8949779,10846368,12976960,16256000] R12bbbabbaaa R12bbbabbaab
theorem R12bbbabbaa_ok : tall (refOK cpF 12) R12bbbabbaa = true :=
  tall_node _ _ _ _ R12bbbabbaaa_ok (by decide +kernel) R12bbbabbaab_ok
def R12bbbabbab : Tree := (.node [120900,467977,1593992,3238160,5382182,8949779,10846368,12976960,16256000] .nil .nil)
theorem R12bbbabbab_ok : tall (refOK cpF 12) R12bbbabbab = true := by decide +kernel
def R12bbbabba : Tree := .node [120900,467977,1593992,3237137,5382182,8949779,10846368,12976960,16256000] R12bbbabbaa R12bbbabbab
theorem R12bbbabba_ok : tall (refOK cpF 12) R12bbbabba = true :=
  tall_node _ _ _ _ R12bbbabbaa_ok (by decide +kernel) R12bbbabbab_ok
def R12bbbabbb : Tree := (.node [120900,467977,1593992,3275092,5382182,8949779,10846368,12976960,16256000,16346384] (.node [120900,467977,1593992,3275092,5382182,8949779,10846368,12976960,16212816,16256000] (.node [120900,467977,1593992,3275092,5382182,7561526,8949779,10846368,12976960,16256000] .nil .nil) .nil) (.node [120900,467977,1593992,3275092,5382182,8949779,10846368,12976960,16292883,16346384] .nil .nil))
theorem R12bbbabbb_ok : tall (refOK cpF 12) R12bbbabbb = true := by decide +kernel
def R12bbbabb : Tree := .node [120900,467977,1593992,3238160,5382182,8949779,10846368,12976960,16292883] R12bbbabba R12bbbabbb
theorem R12bbbabb_ok : tall (refOK cpF 12) R12bbbabb = true :=
  tall_node _ _ _ _ R12bbbabba_ok (by decide +kernel) R12bbbabbb_ok
def R12bbbab : Tree := .node [120900,467977,1593992,3236144,5382182,8949779,10846368,12976960,16256000] R12bbbaba R12bbbabb
theorem R12bbbab_ok : tall (refOK cpF 12) R12bbbab = true :=
  tall_node _ _ _ _ R12bbbaba_ok (by decide +kernel) R12bbbabb_ok
def R12bbba : Tree := .node [120900,467977,1593992,3236112,5503078,8949779,10846368,12976960,16256000,16395302] R12bbbaa R12bbbab
theorem R12bbba_ok : tall (refOK cpF 12) R12bbba = true :=
  tall_node _ _ _ _ R12bbbaa_ok (by decide +kernel) R12bbbab_ok
def R12bbbbaaaa : Tree := (.node [120900,467977,1593992,3630361,5382182,8949779,10846368,12976960,16256000,16346384] (.node [120900,467977,1593992,3630361,5382182,8949779,10846368,12185875,12976960,16256000] .nil .nil) .nil)
theorem R12bbbbaaaa_ok : tall (refOK cpF 12) R12bbbbaaaa = true := by decide +kernel
def R12bbbbaaaba : Tree := (.node [120900,467977,1593992,5382182,7561526,8949779,10846368,12185875,12976960,16256000] .nil .nil)
theorem R12bbbbaaaba_ok : tall (refOK cpF 12) R12bbbbaaaba = true := by decide +kernel
def R12bbbbaaabb : Tree := .nil
theorem R12bbbbaaabb_ok : tall (refOK cpF 12) R12bbbbaaabb = true := by decide +kernel
def R12bbbbaaab : Tree := .node [120900,467977,1594008,3236112,5382182,8949779,10846368,12976960,16256000] R12bbbbaaaba R12bbbbaaabb
theorem R12bbbbaaab_ok : tall (refOK cpF 12) R12bbbbaaab = true :=
  tall_node _ _ _ _ R12bbbbaaaba_ok (by decide +kernel) R12bbbbaaabb_ok
def R12bbbbaaa : Tree := .node [120900,467977,1593992,5382182,7561526,8949779,10846368,11919792,12976960,16256000] R12bbbbaaaa R12bbbbaaab
theorem R12bbbbaaa_ok : tall (refOK cpF 12) R12bbbbaaa = true :=
  tall_node _ _ _ _ R12bbbbaaaa_ok (by decide +kernel) R12bbbbaaab_ok
def R12bbbbaab : Tree := (.node [120900,467977,1694412,3236112,5382182,8949779,10846368,12976960,16256000,16277128] (.node [120900,467977,1694412,3236112,5382182,8949779,10846368,12976960,14570440,16256000] (.node [120900,467977,1694412,3236112,5382182,5927598,8949779,10846368,12976960,16256000] .nil .nil) .nil) (.node [120900,467977,2061961,3236112,5382182,8949779,10015387,10846368,12976960,16256000] .nil .nil))
theorem R12bbbbaab_ok : tall (refOK cpF 12) R12bbbbaab = true := by decide +kernel
def R12bbbbaa : Tree := .node [120900,467977,1596040,3236112,5382182,8949779,10846368,12976960,16256000] R12bbbbaaa R12bbbbaab
theorem R12bbbbaa_ok : tall (refOK cpF 12) R12bbbbaa = true :=
  tall_node _ _ _ _ R12bbbbaaa_ok (by decide +kernel) R12bbbbaab_ok
def R12bbbbaba : Tree := (.node [120900,467977,3236112,3765144,5382182,8949779,10846368,12976960,14570440,16256000] (.node [120900,467977,3236112,3765144,5382182,8949779,10015387,10846368,12976960,16256000] (.node [120900,467977,2061961,3236112,5382182,8949779,10846368,12976960,16256000,16309915] .nil .nil) .nil) (.node [120900,467977,3236112,5382182,5927598,8949779,10015387,10846368,12976960,16256000] .nil .nil))
theorem R12bbbbaba_ok : tall (refOK cpF 12) R12bbbbaba = true := by decide +kernel
def R12bbbbabbaa : Tree := (.node [120900,467977,3236112,5382182,5927598,8949779,10846368,12440232,12976960,16256000] .nil .nil)
theorem R12bbbbabbaa_ok : tall (refOK cpF 12) R12bbbbabbaa = true := by decide +kernel
def R12bbbbabbab : Tree := .nil
theorem R12bbbbabbab_ok : tall (refOK cpF 12) R12bbbbabbab = true := by decide +kernel
def R12bbbbabba : Tree := .node [120900,468009,1593992,3236112,5382182,8949779,10846368,12976960,16256000] R12bbbbabbaa R12bbbbabbab
theorem R12bbbbabba_ok : tall (refOK cpF 12) R12bbbbabba = true :=
  tall_node _ _ _ _ R12bbbbabbaa_ok (by decide +kernel) R12bbbbabbab_ok
def R12bbbbabbb : Tree := (.node [120900,523341,1593992,3236112,5382182,5710895,8949779,10846368,12976960,16256000] .nil .nil)
theorem R12bbbbabbb_ok : tall (refOK cpF 12) R12bbbbabbb = true := by decide +kernel
def R12bbbbabb : Tree := .node [120900,468233,1593992,3236112,5382182,8949779,10846368,12976960,16256000] R12bbbbabba R12bbbbabbb
theorem R12bbbbabb_ok : tall (refOK cpF 12) R12bbbbabb = true :=
  tall_node _ _ _ _ R12bbbbabba_ok (by decide +kernel) R12bbbbabbb_ok
def R12bbbbab : Tree := .node [120900,467977,3236112,5382182,5927598,8949779,10015387,10846368,12976960,16256000,16292883] R12bbbbaba R12bbbbabb
theorem R12bbbbab_ok : tall (refOK cpF 12) R12bbbbab = true :=
  tall_node _ _ _ _ R12bbbbaba_ok (by decide +kernel) R12bbbbabb_ok
def R12bbbba : Tree := .node [120900,467977,2061961,3236112,5382182,8949779,10846368,12976960,16256000,16277128] R12bbbbaa R12bbbbab
theorem R12bbbba_ok : tall (refOK cpF 12) R12bbbba = true :=
  tall_node _ _ _ _ R12bbbbaa_ok (by decide +kernel) R12bbbbab_ok
def R12bbbbbaa : Tree := (.node [120900,1593992,2061961,3236112,5382182,8949779,10846368,10986665,12976960,16256000] (.node [120900,523341,1593992,3236112,5382182,8949779,10846368,12976960,16292883,16722953] (.node [120900,523341,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16722953] .nil .nil) .nil) (.node [120900,1593992,3236112,3630361,5382182,8949779,9417755,10846368,12976960,16256000] (.node [120900,1593992,2061961,3236112,5382182,8949779,10846368,12976960,13051721,16256000] .nil .nil) .nil))
theorem R12bbbbbaa_ok : tall (refOK cpF 12) R12bbbbbaa = true := by decide +kernel
def R12bbbbbaba : Tree := (.node [120900,1593992,3236112,5382182,5710895,8949779,10846368,10986665,12976960,16256000] (.node [120900,1593992,3236112,5382182,5710895,8949779,9417755,10846368,12976960,16256000] .nil .nil) .nil)
theorem R12bbbbbaba_ok : tall (refOK cpF 12) R12bbbbbaba = true := by decide +kernel
def R12bbbbbabb : Tree := (.node [121028,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil)
theorem R12bbbbbabb_ok : tall (refOK cpF 12) R12bbbbbabb = true := by decide +kernel
def R12bbbbbab : Tree := .node [120916,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] R12bbbbbaba R12bbbbbabb
theorem R12bbbbbab_ok : tall (refOK cpF 12) R12bbbbbab = true :=
  tall_node _ _ _ _ R12bbbbbaba_ok (by decide +kernel) R12bbbbbabb_ok
def R12bbbbba : Tree := .node [120900,1593992,3236112,3630361,5382182,8949779,10846368,12976960,13051721,16256000] R12bbbbbaa R12bbbbbab
theorem R12bbbbba_ok : tall (refOK cpF 12) R12bbbbba = true :=
  tall_node _ _ _ _ R12bbbbbaa_ok (by decide +kernel) R12bbbbbab_ok
def R12bbbbbba : Tree := (.node [467977,1593992,1694412,3236112,5382182,8949779,10846368,10868964,12976960,16256000] (.node [467977,523341,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16374852] (.node [467977,523341,1593992,3236112,5382182,8949779,9033815,10846368,12976960,16256000] .nil .nil) .nil) (.node [467977,1593992,1694412,3236112,5382182,8949779,10846368,12976960,13097796,16256000] .nil .nil))
theorem R12bbbbbba_ok : tall (refOK cpF 12) R12bbbbbba = true := by decide +kernel
def R12bbbbbbb : Tree := (.node [467977,1593992,3236112,5382182,5503078,8949779,9033815,10846368,12976960,16256000] (.node [467977,1593992,3236112,3275092,5382182,9033815,10846368,12976960,16256000,16292883] (.node [467977,1593992,3236112,3275092,5382182,8949779,10846368,12976960,13097796,16256000] .nil .nil) .nil) (.node [467977,1593992,3236112,5382182,5503078,8949779,10846368,10868964,12976960,16256000] .nil .nil))
theorem R12bbbbbbb_ok : tall (refOK cpF 12) R12bbbbbbb = true := by decide +kernel
def R12bbbbbb : Tree := .node [467977,1593992,3236112,3275092,5382182,8949779,9033815,10846368,12976960,16256000] R12bbbbbba R12bbbbbbb
theorem R12bbbbbb_ok : tall (refOK cpF 12) R12bbbbbb = true :=
  tall_node _ _ _ _ R12bbbbbba_ok (by decide +kernel) R12bbbbbbb_ok
def R12bbbbb : Tree := .node [467977,523341,1593992,1694412,3236112,5382182,8949779,10846368,12976960,16256000] R12bbbbba R12bbbbbb
theorem R12bbbbb_ok : tall (refOK cpF 12) R12bbbbb = true :=
  tall_node _ _ _ _ R12bbbbba_ok (by decide +kernel) R12bbbbbb_ok
def R12bbbb : Tree := .node [120900,523341,1593992,3236112,5382182,8949779,10846368,12976960,13051721,16256000] R12bbbba R12bbbbb
theorem R12bbbb_ok : tall (refOK cpF 12) R12bbbb = true :=
  tall_node _ _ _ _ R12bbbba_ok (by decide +kernel) R12bbbbb_ok
def R12bbb : Tree := .node [120900,467977,1593992,3630361,3765144,5382182,8949779,10846368,12976960,16256000] R12bbba R12bbbb
theorem R12bbb_ok : tall (refOK cpF 12) R12bbb = true :=
  tall_node _ _ _ _ R12bbba_ok (by decide +kernel) R12bbbb_ok
def R12bb : Tree := .node [120900,467977,1593992,3236112,5382182,9033815,10846368,12976960,16256000,16686931] R12bba R12bbb
theorem R12bb_ok : tall (refOK cpF 12) R12bb = true :=
  tall_node _ _ _ _ R12bba_ok (by decide +kernel) R12bbb_ok
def R12b : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16723785] R12ba R12bb
theorem R12b_ok : tall (refOK cpF 12) R12b = true :=
  tall_node _ _ _ _ R12ba_ok (by decide +kernel) R12bb_ok
def R12 : Tree := .node [120900,467977,1593992,3236112,5382182,5710895,8949779,10846368,12976960,16292883,16722953] R12a R12b
theorem R12_ok : tall (refOK cpF 12) R12 = true :=
  tall_node _ _ _ _ R12a_ok (by decide +kernel) R12b_ok
def T13aaaaa : Tree := (.node [2,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16292883] .nil .nil)
theorem T13aaaaa_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13aaaaa = true := by decide +kernel
def T13aaaab : Tree := (.node [16,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16292883] .nil .nil)
theorem T13aaaab_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13aaaab = true := by decide +kernel
def T13aaaa : Tree := .node [16,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] T13aaaaa T13aaaab
theorem T13aaaa_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13aaaa = true :=
  tall_node _ _ _ _ T13aaaaa_ok (by decide +kernel) T13aaaab_ok
def T13aaaba : Tree := (.node [32,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16292883] .nil .nil)
theorem T13aaaba_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13aaaba = true := by decide +kernel
def T13aaabb : Tree := (.node [128,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil)
theorem T13aaabb_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13aaabb = true := by decide +kernel
def T13aaab : Tree := .node [64,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16292883] T13aaaba T13aaabb
theorem T13aaab_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13aaab = true :=
  tall_node _ _ _ _ T13aaaba_ok (by decide +kernel) T13aaabb_ok
def T13aaa : Tree := .node [32,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] T13aaaa T13aaab
theorem T13aaa_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13aaa = true :=
  tall_node _ _ _ _ T13aaaa_ok (by decide +kernel) T13aaab_ok
def T13aabaa : Tree := (.node [256,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16292883] .nil .nil)
theorem T13aabaa_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13aabaa = true := by decide +kernel
def T13aabab : Tree := (.node [1025,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil)
theorem T13aabab_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13aabab = true := by decide +kernel
def T13aaba : Tree := .node [1024,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] T13aabaa T13aabab
theorem T13aaba_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13aaba = true :=
  tall_node _ _ _ _ T13aabaa_ok (by decide +kernel) T13aabab_ok
def T13aabba : Tree := (.node [2048,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16292883] .nil .nil)
theorem T13aabba_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13aabba = true := by decide +kernel
def T13aabbb : Tree := (.node [120900,467977,1593992,1694412,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil)
theorem T13aabbb_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13aabbb = true := by decide +kernel
def T13aabb : Tree := .node [120900,467977,523341,1593992,3236112,5382182,8949779,10846368,12976960,16256000] T13aabba T13aabbb
theorem T13aabb_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13aabb = true :=
  tall_node _ _ _ _ T13aabba_ok (by decide +kernel) T13aabbb_ok
def T13aab : Tree := .node [2048,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] T13aaba T13aabb
theorem T13aab_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13aab = true :=
  tall_node _ _ _ _ T13aaba_ok (by decide +kernel) T13aabb_ok
def T13aa : Tree := .node [256,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] T13aaa T13aab
theorem T13aa_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13aa = true :=
  tall_node _ _ _ _ T13aaa_ok (by decide +kernel) T13aab_ok
def T13abaaa : Tree := (.node [120900,467977,1593992,3145744,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil)
theorem T13abaaa_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13abaaa = true := by decide +kernel
def T13abaab : Tree := (.node [120900,467977,1593992,3236112,3275092,5382182,8949779,10846368,12976960,16256000] .nil .nil)
theorem T13abaab_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13abaab = true := by decide +kernel
def T13abaa : Tree := .node [120900,467977,1593992,3145744,3236112,5382182,8949779,10846368,12976960,16256000,16292883] T13abaaa T13abaab
theorem T13abaa_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13abaa = true :=
  tall_node _ _ _ _ T13abaaa_ok (by decide +kernel) T13abaab_ok
def T13ababa : Tree := (.node [120900,467977,1593992,3236112,3630361,5382182,8949779,10846368,12976960,16256000] .nil .nil)
theorem T13ababa_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13ababa = true := by decide +kernel
def T13ababb : Tree := (.node [120900,467977,1593992,3236112,3765144,5382182,8949779,10846368,12976960,16256000] .nil .nil)
theorem T13ababb_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13ababb = true := by decide +kernel
def T13abab : Tree := .node [120900,467977,1593992,3236112,3630361,5382182,8949779,10846368,12976960,16256000,16292883] T13ababa T13ababb
theorem T13abab_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13abab = true :=
  tall_node _ _ _ _ T13ababa_ok (by decide +kernel) T13ababb_ok
def T13aba : Tree := .node [120900,467977,1593992,3236112,3275092,5382182,8949779,10846368,12976960,16256000,16292883] T13abaa T13abab
theorem T13aba_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13aba = true :=
  tall_node _ _ _ _ T13abaa_ok (by decide +kernel) T13abab_ok
def T13abbaa : Tree := (.node [120900,467977,1593992,3236112,5382182,5710895,8949779,10846368,12976960,16256000] .nil .nil)
theorem T13abbaa_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13abbaa = true := by decide +kernel
def T13abbab : Tree := (.node [120900,467977,1593992,3236112,5382182,5927598,8949779,10846368,12976960,16256000] .nil .nil)
theorem T13abbab_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13abbab = true := by decide +kernel
def T13abba : Tree := .node [120900,467977,1593992,3236112,5382182,5710895,8949779,10846368,12976960,16256000,16292883] T13abbaa T13abbab
theorem T13abba_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13abba = true :=
  tall_node _ _ _ _ T13abbaa_ok (by decide +kernel) T13abbab_ok
def T13abbba : Tree := (.node [120900,467977,1593992,3236112,5382182,7561526,8949779,10846368,12976960,16256000] .nil .nil)
theorem T13abbba_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13abbba = true := by decide +kernel
def T13abbbb : Tree := .nil
theorem T13abbbb_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13abbbb = true := by decide +kernel
def T13abbb : Tree := .node [120900,467977,1593992,3236112,5382182,7561526,8949779,10846368,12976960,16256000,16292883] T13abbba T13abbbb
theorem T13abbb_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13abbb = true :=
  tall_node _ _ _ _ T13abbba_ok (by decide +kernel) T13abbbb_ok
def T13abb : Tree := .node [120900,467977,1593992,3236112,5382182,5927598,8949779,10846368,12976960,16256000,16292883] T13abba T13abbb
theorem T13abb_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13abb = true :=
  tall_node _ _ _ _ T13abba_ok (by decide +kernel) T13abbb_ok
def T13ab : Tree := .node [120900,467977,1593992,3236112,3765144,5382182,8949779,10846368,12976960,16256000,16292883] T13aba T13abb
theorem T13ab_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13ab = true :=
  tall_node _ _ _ _ T13aba_ok (by decide +kernel) T13abb_ok
def T13a : Tree := .node [120900,467977,1593992,1694412,3236112,5382182,8949779,10846368,12976960,16256000,16292883] T13aa T13ab
theorem T13a_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13a = true :=
  tall_node _ _ _ _ T13aa_ok (by decide +kernel) T13ab_ok
def T13baaaa : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,9033815,10846368,12976960,16256000,16292883] .nil .nil)
theorem T13baaaa_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13baaaa = true := by decide +kernel
def T13baaab : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,16256000] .nil .nil)
theorem T13baaab_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13baaab = true := by decide +kernel
def T13baaa : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,9417755,10846368,12976960,16256000,16292883] T13baaaa T13baaab
theorem T13baaa_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13baaa = true :=
  tall_node _ _ _ _ T13baaaa_ok (by decide +kernel) T13baaab_ok
def T13baaba : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,10868964,12976960,16256000] .nil .nil)
theorem T13baaba_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13baaba = true := by decide +kernel
def T13baabb : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,10986665,12976960,16256000] .nil .nil)
theorem T13baabb_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13baabb = true := by decide +kernel
def T13baab : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,10868964,12976960,16256000,16292883] T13baaba T13baabb
theorem T13baab_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13baab = true :=
  tall_node _ _ _ _ T13baaba_ok (by decide +kernel) T13baabb_ok
def T13baa : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10015387,10846368,12976960,16256000,16292883] T13baaa T13baab
theorem T13baa_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13baa = true :=
  tall_node _ _ _ _ T13baaa_ok (by decide +kernel) T13baab_ok
def T13babaa : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,11374771,12976960,16256000] .nil .nil)
theorem T13babaa_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13babaa = true := by decide +kernel
def T13babab : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,11919792,12976960,16256000,16292883] .nil .nil)
theorem T13babab_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13babab = true := by decide +kernel
def T13baba : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,11374771,12976960,16256000,16292883] T13babaa T13babab
theorem T13baba_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13baba = true :=
  tall_node _ _ _ _ T13babaa_ok (by decide +kernel) T13babab_ok
def T13babba : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,13051721,16256000] .nil .nil)
theorem T13babba_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13babba = true := by decide +kernel
def T13babbb : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,13097796,16256000,16292883] .nil .nil)
theorem T13babbb_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13babbb = true := by decide +kernel
def T13babb : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,13051721,16256000,16292883] T13babba T13babbb
theorem T13babb_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13babb = true :=
  tall_node _ _ _ _ T13babba_ok (by decide +kernel) T13babbb_ok
def T13bab : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12185875,12976960,16256000,16292883] T13baba T13babb
theorem T13bab_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13bab = true :=
  tall_node _ _ _ _ T13baba_ok (by decide +kernel) T13babb_ok
def T13ba : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,10986665,12976960,16256000,16292883] T13baa T13bab
theorem T13ba_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13ba = true :=
  tall_node _ _ _ _ T13baa_ok (by decide +kernel) T13bab_ok
def T13bbaaa : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,13538131,16256000,16292883] .nil .nil)
theorem T13bbaaa_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13bbaaa = true := by decide +kernel
def T13bbaab : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,14033766,16256000,16292883] .nil .nil)
theorem T13bbaab_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13bbaab = true := by decide +kernel
def T13bbaa : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,14033766,16256000] T13bbaaa T13bbaab
theorem T13bbaa_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13bbaa = true :=
  tall_node _ _ _ _ T13bbaaa_ok (by decide +kernel) T13bbaab_ok
def T13bbaba : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16277128] .nil .nil)
theorem T13bbaba_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13bbaba = true := by decide +kernel
def T13bbabb : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16309915] .nil .nil)
theorem T13bbabb_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13bbabb = true := by decide +kernel
def T13bbab : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16292883,16650048] T13bbaba T13bbabb
theorem T13bbab_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13bbab = true :=
  tall_node _ _ _ _ T13bbaba_ok (by decide +kernel) T13bbabb_ok
def T13bba : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,15172576,16256000] T13bbaa T13bbab
theorem T13bba_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13bba = true :=
  tall_node _ _ _ _ T13bbaa_ok (by decide +kernel) T13bbab_ok
def T13bbbaa : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16650048] .nil .nil)
theorem T13bbbaa_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13bbbaa = true := by decide +kernel
def T13bbbab : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16292883,16650048] .nil .nil)
theorem T13bbbab_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13bbbab = true := by decide +kernel
def T13bbba : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16292883,16395302] T13bbbaa T13bbbab
theorem T13bbba_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13bbba = true :=
  tall_node _ _ _ _ T13bbbaa_ok (by decide +kernel) T13bbbab_ok
def T13bbbba : Tree := (.node [120900,467977,1593992,3236112,5382182,9033815,10846368,12976960,16256000,16292883] .nil .nil)
theorem T13bbbba_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13bbbba = true := by decide +kernel
def T13bbbbb : Tree := .nil
theorem T13bbbbb_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13bbbbb = true := by decide +kernel
def T13bbbb : Tree := .node [120900,467977,1593992,3236112,5382182,9417755,10846368,12976960,16256000,16292883] T13bbbba T13bbbbb
theorem T13bbbb_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13bbbb = true :=
  tall_node _ _ _ _ T13bbbba_ok (by decide +kernel) T13bbbbb_ok
def T13bbb : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16292883,16722953] T13bbba T13bbbb
theorem T13bbb_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13bbb = true :=
  tall_node _ _ _ _ T13bbba_ok (by decide +kernel) T13bbbb_ok
def T13bb : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16395302] T13bba T13bbb
theorem T13bb_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13bb = true :=
  tall_node _ _ _ _ T13bba_ok (by decide +kernel) T13bbb_ok
def T13b : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,13538131,16256000] T13ba T13bb
theorem T13b_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13b = true :=
  tall_node _ _ _ _ T13ba_ok (by decide +kernel) T13bb_ok
def T13 : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,9033815,10846368,12976960,16256000] T13a T13b
theorem T13_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13 = true :=
  tall_node _ _ _ _ T13a_ok (by decide +kernel) T13b_ok
def R13aaaaaa : Tree := (.node [1,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil)
theorem R13aaaaaa_ok : tall (refOK cpF 13) R13aaaaaa = true := by decide +kernel
def R13aaaaab : Tree := .nil
theorem R13aaaaab_ok : tall (refOK cpF 13) R13aaaaab = true := by decide +kernel
def R13aaaaa : Tree := .node [1,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16292883] R13aaaaaa R13aaaaab
theorem R13aaaaa_ok : tall (refOK cpF 13) R13aaaaa = true :=
  tall_node _ _ _ _ R13aaaaaa_ok (by decide +kernel) R13aaaaab_ok
def R13aaaaba : Tree := (.node [4,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil)
theorem R13aaaaba_ok : tall (refOK cpF 13) R13aaaaba = true := by decide +kernel
def R13aaaabb : Tree := .nil
theorem R13aaaabb_ok : tall (refOK cpF 13) R13aaaabb = true := by decide +kernel
def R13aaaab : Tree := .node [4,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16292883] R13aaaaba R13aaaabb
theorem R13aaaab_ok : tall (refOK cpF 13) R13aaaab = true :=
  tall_node _ _ _ _ R13aaaaba_ok (by decide +kernel) R13aaaabb_ok
def R13aaaa : Tree := .node [2,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] R13aaaaa R13aaaab
theorem R13aaaa_ok : tall (refOK cpF 13) R13aaaa = true :=
  tall_node _ _ _ _ R13aaaaa_ok (by decide +kernel) R13aaaab_ok
def R13aaabaa : Tree := (.node [8,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16292883] .nil .nil)
theorem R13aaabaa_ok : tall (refOK cpF 13) R13aaabaa = true := by decide +kernel
def R13aaabab : Tree := .nil
theorem R13aaabab_ok : tall (refOK cpF 13) R13aaabab = true := by decide +kernel
def R13aaaba : Tree := .node [64,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] R13aaabaa R13aaabab
theorem R13aaaba_ok : tall (refOK cpF 13) R13aaaba = true :=
  tall_node _ _ _ _ R13aaabaa_ok (by decide +kernel) R13aaabab_ok
def R13aaabba : Tree := (.node [512,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil)
theorem R13aaabba_ok : tall (refOK cpF 13) R13aaabba = true := by decide +kernel
def R13aaabbb : Tree := .nil
theorem R13aaabbb_ok : tall (refOK cpF 13) R13aaabbb = true := by decide +kernel
def R13aaabb : Tree := .node [512,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16292883] R13aaabba R13aaabbb
theorem R13aaabb_ok : tall (refOK cpF 13) R13aaabb = true :=
  tall_node _ _ _ _ R13aaabba_ok (by decide +kernel) R13aaabbb_ok
def R13aaab : Tree := .node [128,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16292883] R13aaaba R13aaabb
theorem R13aaab_ok : tall (refOK cpF 13) R13aaab = true :=
  tall_node _ _ _ _ R13aaaba_ok (by decide +kernel) R13aaabb_ok
def R13aaa : Tree := .node [8,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] R13aaaa R13aaab
theorem R13aaa_ok : tall (refOK cpF 13) R13aaa = true :=
  tall_node _ _ _ _ R13aaaa_ok (by decide +kernel) R13aaab_ok
def R13aabaa : Tree := (.node [2048,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16292883] (.node [1025,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16292883] .nil .nil) .nil)
theorem R13aabaa_ok : tall (refOK cpF 13) R13aabaa = true := by decide +kernel
def R13aababa : Tree := (.node [20480,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16292883] .nil .nil)
theorem R13aababa_ok : tall (refOK cpF 13) R13aababa = true := by decide +kernel
def R13aababb : Tree := .nil
theorem R13aababb_ok : tall (refOK cpF 13) R13aababb = true := by decide +kernel
def R13aabab : Tree := .node [36864,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] R13aababa R13aababb
theorem R13aabab_ok : tall (refOK cpF 13) R13aabab = true :=
  tall_node _ _ _ _ R13aababa_ok (by decide +kernel) R13aababb_ok
def R13aaba : Tree := .node [20480,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] R13aabaa R13aabab
theorem R13aaba_ok : tall (refOK cpF 13) R13aaba = true :=
  tall_node _ _ _ _ R13aabaa_ok (by decide +kernel) R13aabab_ok
def R13aabbaa : Tree := (.node [38912,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil)
theorem R13aabbaa_ok : tall (refOK cpF 13) R13aabbaa = true := by decide +kernel
def R13aabbab : Tree := .nil
theorem R13aabbab_ok : tall (refOK cpF 13) R13aabbab = true := by decide +kernel
def R13aabba : Tree := .node [38912,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16292883] R13aabbaa R13aabbab
theorem R13aabba_ok : tall (refOK cpF 13) R13aabba = true :=
  tall_node _ _ _ _ R13aabbaa_ok (by decide +kernel) R13aabbab_ok
def R13aabbba : Tree := (.node [65536,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16292883] .nil .nil)
theorem R13aabbba_ok : tall (refOK cpF 13) R13aabbba = true := by decide +kernel
def R13aabbbb : Tree := .nil
theorem R13aabbbb_ok : tall (refOK cpF 13) R13aabbbb = true := by decide +kernel
def R13aabbb : Tree := .node [73728,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] R13aabbba R13aabbbb
theorem R13aabbb_ok : tall (refOK cpF 13) R13aabbb = true :=
  tall_node _ _ _ _ R13aabbba_ok (by decide +kernel) R13aabbbb_ok
def R13aabb : Tree := .node [65536,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] R13aabba R13aabbb
theorem R13aabb_ok : tall (refOK cpF 13) R13aabb = true :=
  tall_node _ _ _ _ R13aabba_ok (by decide +kernel) R13aabbb_ok
def R13aab : Tree := .node [36864,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16292883] R13aaba R13aabb
theorem R13aab_ok : tall (refOK cpF 13) R13aab = true :=
  tall_node _ _ _ _ R13aaba_ok (by decide +kernel) R13aabb_ok
def R13aa : Tree := .node [1024,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16292883] R13aaa R13aab
theorem R13aa_ok : tall (refOK cpF 13) R13aa = true :=
  tall_node _ _ _ _ R13aaa_ok (by decide +kernel) R13aab_ok
def R13abaaaa : Tree := (.node [81920,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil)
theorem R13abaaaa_ok : tall (refOK cpF 13) R13abaaaa = true := by decide +kernel
def R13abaaab : Tree := .nil
theorem R13abaaab_ok : tall (refOK cpF 13) R13abaaab = true := by decide +kernel
def R13abaaa : Tree := .node [81920,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16292883] R13abaaaa R13abaaab
theorem R13abaaa_ok : tall (refOK cpF 13) R13abaaa = true :=
  tall_node _ _ _ _ R13abaaaa_ok (by decide +kernel) R13abaaab_ok
def R13abaaba : Tree := (.node [98304,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16292883] .nil .nil)
theorem R13abaaba_ok : tall (refOK cpF 13) R13abaaba = true := by decide +kernel
def R13abaabb : Tree := .nil
theorem R13abaabb_ok : tall (refOK cpF 13) R13abaabb = true := by decide +kernel
def R13abaab : Tree := .node [120900,139264,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] R13abaaba R13abaabb
theorem R13abaab_ok : tall (refOK cpF 13) R13abaab = true :=
  tall_node _ _ _ _ R13abaaba_ok (by decide +kernel) R13abaabb_ok
def R13abaa : Tree := .node [98304,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] R13abaaa R13abaab
theorem R13abaa_ok : tall (refOK cpF 13) R13abaa = true :=
  tall_node _ _ _ _ R13abaaa_ok (by decide +kernel) R13abaab_ok
def R13ababaa : Tree := (.node [120900,327680,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil)
theorem R13ababaa_ok : tall (refOK cpF 13) R13ababaa = true := by decide +kernel
def R13ababab : Tree := .nil
theorem R13ababab_ok : tall (refOK cpF 13) R13ababab = true := by decide +kernel
def R13ababa : Tree := .node [120900,327680,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16292883] R13ababaa R13ababab
theorem R13ababa_ok : tall (refOK cpF 13) R13ababa = true :=
  tall_node _ _ _ _ R13ababaa_ok (by decide +kernel) R13ababab_ok
def R13ababb : Tree := (.node [120900,467977,523341,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16292883] (.node [120900,393216,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16292883] .nil .nil) .nil)
theorem R13ababb_ok : tall (refOK cpF 13) R13ababb = true := by decide +kernel
def R13abab : Tree := .node [120900,393216,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] R13ababa R13ababb
theorem R13abab_ok : tall (refOK cpF 13) R13abab = true :=
  tall_node _ _ _ _ R13ababa_ok (by decide +kernel) R13ababb_ok
def R13aba : Tree := .node [120900,139264,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16292883] R13abaa R13abab
theorem R13aba_ok : tall (refOK cpF 13) R13aba = true :=
  tall_node _ _ _ _ R13abaa_ok (by decide +kernel) R13abab_ok
def R13abbaaa : Tree := (.node [120900,467977,1048576,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil)
theorem R13abbaaa_ok : tall (refOK cpF 13) R13abbaaa = true := by decide +kernel
def R13abbaab : Tree := .nil
theorem R13abbaab_ok : tall (refOK cpF 13) R13abbaab = true := by decide +kernel
def R13abbaa : Tree := .node [120900,467977,1056768,1593992,3236112,5382182,8949779,10846368,12976960,16256000] R13abbaaa R13abbaab
theorem R13abbaa_ok : tall (refOK cpF 13) R13abbaa = true :=
  tall_node _ _ _ _ R13abbaaa_ok (by decide +kernel) R13abbaab_ok
def R13abbaba : Tree := (.node [120900,467977,1064960,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16292883] .nil .nil)
theorem R13abbaba_ok : tall (refOK cpF 13) R13abbaba = true := by decide +kernel
def R13abbabb : Tree := .nil
theorem R13abbabb_ok : tall (refOK cpF 13) R13abbabb = true := by decide +kernel
def R13abbab : Tree := .node [120900,467977,1572864,1593992,3236112,5382182,8949779,10846368,12976960,16256000] R13abbaba R13abbabb
theorem R13abbab_ok : tall (refOK cpF 13) R13abbab = true :=
  tall_node _ _ _ _ R13abbaba_ok (by decide +kernel) R13abbabb_ok
def R13abba : Tree := .node [120900,467977,1064960,1593992,3236112,5382182,8949779,10846368,12976960,16256000] R13abbaa R13abbab
theorem R13abba_ok : tall (refOK cpF 13) R13abba = true :=
  tall_node _ _ _ _ R13abbaa_ok (by decide +kernel) R13abbab_ok
def R13abbbaa : Tree := (.node [120900,467977,1593992,2061961,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil)
theorem R13abbbaa_ok : tall (refOK cpF 13) R13abbbaa = true := by decide +kernel
def R13abbbab : Tree := .nil
theorem R13abbbab_ok : tall (refOK cpF 13) R13abbbab = true := by decide +kernel
def R13abbba : Tree := .node [120900,467977,1593992,2061961,3236112,5382182,8949779,10846368,12976960,16256000,16292883] R13abbbaa R13abbbab
theorem R13abbba_ok : tall (refOK cpF 13) R13abbba = true :=
  tall_node _ _ _ _ R13abbbaa_ok (by decide +kernel) R13abbbab_ok
def R13abbbb : Tree := (.node [120900,467977,1593992,3145728,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil)
theorem R13abbbb_ok : tall (refOK cpF 13) R13abbbb = true := by decide +kernel
def R13abbb : Tree := .node [120900,467977,1593992,2162688,3236112,5382182,8949779,10846368,12976960,16256000] R13abbba R13abbbb
theorem R13abbb_ok : tall (refOK cpF 13) R13abbb = true :=
  tall_node _ _ _ _ R13abbba_ok (by decide +kernel) R13abbbb_ok
def R13abb : Tree := .node [120900,467977,1576960,1593992,3236112,5382182,8949779,10846368,12976960,16256000] R13abba R13abbb
theorem R13abb_ok : tall (refOK cpF 13) R13abb = true :=
  tall_node _ _ _ _ R13abba_ok (by decide +kernel) R13abbb_ok
def R13ab : Tree := .node [120900,467977,528384,1593992,3236112,5382182,8949779,10846368,12976960,16256000] R13aba R13abb
theorem R13ab_ok : tall (refOK cpF 13) R13ab = true :=
  tall_node _ _ _ _ R13aba_ok (by decide +kernel) R13abb_ok
def R13a : Tree := .node [73728,120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16292883] R13aa R13ab
theorem R13a_ok : tall (refOK cpF 13) R13a = true :=
  tall_node _ _ _ _ R13aa_ok (by decide +kernel) R13ab_ok
def R13baaaaa : Tree := (.node [120900,467977,1593992,3236112,5242880,5382182,8949779,10846368,12976960,16256000] .nil .nil)
theorem R13baaaaa_ok : tall (refOK cpF 13) R13baaaaa = true := by decide +kernel
def R13baaaab : Tree := .nil
theorem R13baaaab_ok : tall (refOK cpF 13) R13baaaab = true := by decide +kernel
def R13baaaa : Tree := .node [120900,467977,1593992,3236112,5242882,5382182,8949779,10846368,12976960,16256000] R13baaaaa R13baaaab
theorem R13baaaa_ok : tall (refOK cpF 13) R13baaaa = true :=
  tall_node _ _ _ _ R13baaaaa_ok (by decide +kernel) R13baaaab_ok
def R13baaaba : Tree := (.node [120900,467977,1593992,3236112,5382182,5503078,8949779,10846368,12976960,16256000] .nil .nil)
theorem R13baaaba_ok : tall (refOK cpF 13) R13baaaba = true := by decide +kernel
def R13baaabb : Tree := .nil
theorem R13baaabb_ok : tall (refOK cpF 13) R13baaabb = true := by decide +kernel
def R13baaab : Tree := .node [120900,467977,1593992,3236112,5382182,5503078,8949779,10846368,12976960,16256000,16292883] R13baaaba R13baaabb
theorem R13baaab_ok : tall (refOK cpF 13) R13baaab = true :=
  tall_node _ _ _ _ R13baaaba_ok (by decide +kernel) R13baaabb_ok
def R13baaa : Tree := .node [120900,467977,1593992,3236112,5242882,5382182,8949779,10846368,12976960,16256000,16292883] R13baaaa R13baaab
theorem R13baaa_ok : tall (refOK cpF 13) R13baaa = true :=
  tall_node _ _ _ _ R13baaaa_ok (by decide +kernel) R13baaab_ok
def R13baabaa : Tree := (.node [120900,467977,1593992,3236112,5382182,8421376,8949779,10846368,12976960,16256000] .nil .nil)
theorem R13baabaa_ok : tall (refOK cpF 13) R13baabaa = true := by decide +kernel
def R13baabab : Tree := .nil
theorem R13baabab_ok : tall (refOK cpF 13) R13baabab = true := by decide +kernel
def R13baaba : Tree := .node [120900,467977,1593992,3236112,5382182,8650752,8949779,10846368,12976960,16256000] R13baabaa R13baabab
theorem R13baaba_ok : tall (refOK cpF 13) R13baaba = true :=
  tall_node _ _ _ _ R13baabaa_ok (by decide +kernel) R13baabab_ok
def R13baabba : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,9417755,10846368,12976960,16256000] .nil .nil)
theorem R13baabba_ok : tall (refOK cpF 13) R13baabba = true := by decide +kernel
def R13baabbb : Tree := .nil
theorem R13baabbb_ok : tall (refOK cpF 13) R13baabbb = true := by decide +kernel
def R13baabb : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10518528,10846368,12976960,16256000] R13baabba R13baabbb
theorem R13baabb_ok : tall (refOK cpF 13) R13baabb = true :=
  tall_node _ _ _ _ R13baabba_ok (by decide +kernel) R13baabbb_ok
def R13baab : Tree := .node [120900,467977,1593992,3236112,5382182,8912896,8949779,10846368,12976960,16256000] R13baaba R13baabb
theorem R13baab_ok : tall (refOK cpF 13) R13baab = true :=
  tall_node _ _ _ _ R13baaba_ok (by decide +kernel) R13baabb_ok
def R13baa : Tree := .node [120900,467977,1593992,3236112,5382182,8388608,8949779,10846368,12976960,16256000] R13baaa R13baab
theorem R13baa_ok : tall (refOK cpF 13) R13baa = true :=
  tall_node _ _ _ _ R13baaa_ok (by decide +kernel) R13baab_ok
def R13babaaa : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12185875,12976960,16256000] .nil .nil)
theorem R13babaaa_ok : tall (refOK cpF 13) R13babaaa = true := by decide +kernel
def R13babaab : Tree := .nil
theorem R13babaab_ok : tall (refOK cpF 13) R13babaab = true := by decide +kernel
def R13babaa : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12440232,12976960,16256000] R13babaaa R13babaab
theorem R13babaa_ok : tall (refOK cpF 13) R13babaa = true :=
  tall_node _ _ _ _ R13babaaa_ok (by decide +kernel) R13babaab_ok
def R13bababa : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12582912,12976960,16256000] .nil .nil)
theorem R13bababa_ok : tall (refOK cpF 13) R13bababa = true := by decide +kernel
def R13bababb : Tree := .nil
theorem R13bababb_ok : tall (refOK cpF 13) R13bababb = true := by decide +kernel
def R13babab : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12582912,12976960,16256000,16292883] R13bababa R13bababb
theorem R13babab_ok : tall (refOK cpF 13) R13babab = true :=
  tall_node _ _ _ _ R13bababa_ok (by decide +kernel) R13bababb_ok
def R13baba : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12440232,12976960,16256000,16292883] R13babaa R13babab
theorem R13baba_ok : tall (refOK cpF 13) R13baba = true :=
  tall_node _ _ _ _ R13babaa_ok (by decide +kernel) R13babab_ok
def R13babbaa : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,14331959,16256000] .nil .nil)
theorem R13babbaa_ok : tall (refOK cpF 13) R13babbaa = true := by decide +kernel
def R13babbab : Tree := .nil
theorem R13babbab_ok : tall (refOK cpF 13) R13babbab = true := by decide +kernel
def R13babba : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,14331959,16256000,16292883] R13babbaa R13babbab
theorem R13babba_ok : tall (refOK cpF 13) R13babba = true :=
  tall_node _ _ _ _ R13babbaa_ok (by decide +kernel) R13babbab_ok
def R13babbb : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,14570440,16256000,16292883] .nil .nil)
theorem R13babbb_ok : tall (refOK cpF 13) R13babbb = true := by decide +kernel
def R13babb : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,14570440,16256000] R13babba R13babbb
theorem R13babb_ok : tall (refOK cpF 13) R13babb = true :=
  tall_node _ _ _ _ R13babba_ok (by decide +kernel) R13babbb_ok
def R13bab : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,13097796,16256000] R13baba R13babb
theorem R13bab_ok : tall (refOK cpF 13) R13bab = true :=
  tall_node _ _ _ _ R13baba_ok (by decide +kernel) R13babb_ok
def R13ba : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,11919792,12976960,16256000] R13baa R13bab
theorem R13ba_ok : tall (refOK cpF 13) R13ba = true :=
  tall_node _ _ _ _ R13baa_ok (by decide +kernel) R13bab_ok
def R13bbaaaa : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16212816,16256000] .nil .nil)
theorem R13bbaaaa_ok : tall (refOK cpF 13) R13bbaaaa = true := by decide +kernel
def R13bbaaab : Tree := .nil
theorem R13bbaaab_ok : tall (refOK cpF 13) R13bbaaab = true := by decide +kernel
def R13bbaaa : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16212816,16256000,16292883] R13bbaaaa R13bbaaab
theorem R13bbaaa_ok : tall (refOK cpF 13) R13bbaaa = true :=
  tall_node _ _ _ _ R13bbaaaa_ok (by decide +kernel) R13bbaaab_ok
def R13bbaab : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16277128,16292883] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16228518,16256000,16292883] .nil .nil) .nil)
theorem R13bbaab_ok : tall (refOK cpF 13) R13bbaab = true := by decide +kernel
def R13bbaa : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16228518,16256000] R13bbaaa R13bbaab
theorem R13bbaa_ok : tall (refOK cpF 13) R13bbaa = true :=
  tall_node _ _ _ _ R13bbaaa_ok (by decide +kernel) R13bbaab_ok
def R13bbab : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16292883,16395302] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16292883,16374871] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16292883,16374852] .nil .nil) .nil) (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16292883,16759835] (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16292883,16722953] .nil .nil) .nil))
theorem R13bbab_ok : tall (refOK cpF 13) R13bbab = true := by decide +kernel
def R13bba : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16292883,16309915] R13bbaa R13bbab
theorem R13bba_ok : tall (refOK cpF 13) R13bba = true :=
  tall_node _ _ _ _ R13bbaa_ok (by decide +kernel) R13bbab_ok
def R13bbbaaa : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16374852] .nil .nil)
theorem R13bbbaaa_ok : tall (refOK cpF 13) R13bbbaaa = true := by decide +kernel
def R13bbbaab : Tree := .nil
theorem R13bbbaab_ok : tall (refOK cpF 13) R13bbbaab = true := by decide +kernel
def R13bbbaa : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16374871] R13bbbaaa R13bbbaab
theorem R13bbbaa_ok : tall (refOK cpF 13) R13bbbaa = true :=
  tall_node _ _ _ _ R13bbbaaa_ok (by decide +kernel) R13bbbaab_ok
def R13bbbaba : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16432183] .nil .nil)
theorem R13bbbaba_ok : tall (refOK cpF 13) R13bbbaba = true := by decide +kernel
def R13bbbabb : Tree := .nil
theorem R13bbbabb_ok : tall (refOK cpF 13) R13bbbabb = true := by decide +kernel
def R13bbbab : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16616608] R13bbbaba R13bbbabb
theorem R13bbbab_ok : tall (refOK cpF 13) R13bbbab = true :=
  tall_node _ _ _ _ R13bbbaba_ok (by decide +kernel) R13bbbabb_ok
def R13bbba : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16383251] R13bbbaa R13bbbab
theorem R13bbba_ok : tall (refOK cpF 13) R13bbba = true :=
  tall_node _ _ _ _ R13bbbaa_ok (by decide +kernel) R13bbbab_ok
def R13bbbbaa : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16686931] .nil .nil)
theorem R13bbbbaa_ok : tall (refOK cpF 13) R13bbbbaa = true := by decide +kernel
def R13bbbbab : Tree := .nil
theorem R13bbbbab_ok : tall (refOK cpF 13) R13bbbbab = true := by decide +kernel
def R13bbbba : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16722953] R13bbbbaa R13bbbbab
theorem R13bbbba_ok : tall (refOK cpF 13) R13bbbba = true :=
  tall_node _ _ _ _ R13bbbbaa_ok (by decide +kernel) R13bbbbab_ok
def R13bbbbb : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16292883,16346384] .nil .nil)
theorem R13bbbbb_ok : tall (refOK cpF 13) R13bbbbb = true := by decide +kernel
def R13bbbb : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16759835] R13bbbba R13bbbbb
theorem R13bbbb_ok : tall (refOK cpF 13) R13bbbb = true :=
  tall_node _ _ _ _ R13bbbba_ok (by decide +kernel) R13bbbbb_ok
def R13bbb : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16620723] R13bbba R13bbbb
theorem R13bbb_ok : tall (refOK cpF 13) R13bbb = true :=
  tall_node _ _ _ _ R13bbba_ok (by decide +kernel) R13bbbb_ok
def R13bb : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16346384] R13bba R13bbb
theorem R13bb_ok : tall (refOK cpF 13) R13bb = true :=
  tall_node _ _ _ _ R13bba_ok (by decide +kernel) R13bbb_ok
def R13b : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,15172576,16256000,16292883] R13ba R13bb
theorem R13b_ok : tall (refOK cpF 13) R13b = true :=
  tall_node _ _ _ _ R13ba_ok (by decide +kernel) R13bb_ok
def R13 : Tree := .node [120900,467977,1593992,3236112,4325376,5382182,8949779,10846368,12976960,16256000] R13a R13b
theorem R13_ok : tall (refOK cpF 13) R13 = true :=
  tall_node _ _ _ _ R13a_ok (by decide +kernel) R13b_ok
def T14a : Tree := (.node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000] .nil .nil)
theorem T14a_ok : tall (expFast false (RP PR T13 R13 13) T13 13) T14a = true := by decide +kernel
def T14b : Tree := .nil
theorem T14b_ok : tall (expFast false (RP PR T13 R13 13) T13 13) T14b = true := by decide +kernel
def T14 : Tree := .node [120900,467977,1593992,3236112,5382182,8949779,10846368,12976960,16256000,16292883] T14a T14b
theorem T14_ok : tall (expFast false (RP PR T13 R13 13) T13 13) T14 = true :=
  tall_node _ _ _ _ T14a_ok (by decide +kernel) T14b_ok
theorem start_ok : subsAll base10 (closedS T14 14) = true := by decide +kernel

theorem noStart : NoStart false 14 :=
  start_sym (level_R PR_sound (level_R PR_sound (level_R PR_sound (level_R PR_sound (level_R PR_sound (level_R PR_sound (level_R PR_sound (level_R PR_sound (level_R PR_sound (level_R PR_sound (level_R PR_sound (level_R PR_sound (level_R PR_sound (level_R PR_sound (inv_leaf false) (inv_nil false 0) T1_ok) (inv_nil false 1) T2_ok) (inv_nil false 2) T3_ok) (inv_nil false 3) T4_ok) (inv_nil false 4) T5_ok) (inv_nil false 5) T6_ok) (inv_nil false 6) T7_ok) (inv_nil false 7) T8_ok) (inv_nil false 8) T9_ok) (inv_nil false 9) T10_ok) (refuted (cpF_sound false) R10_ok) T11_ok) (refuted (cpF_sound false) R11_ok) T12_ok) (refuted (cpF_sound false) R12_ok) T13_ok) (refuted (cpF_sound false) R13_ok) T14_ok) start_ok

theorem noStartH : NoStartH false 14 := noStart.toH

def layL : List ℕ → ℕ → ℕ
  | [], _ => 0
  | p :: ps, x => Nat.bit (x.testBit p) (layL ps x)

theorem layL_tb : ∀ (ps : List ℕ) (x i : ℕ),
    (layL ps x).testBit i = (decide (i < ps.length) && x.testBit (ps.getD i 0)) := by
  intro ps
  induction ps with
  | nil => intro x i; simp [layL]
  | cons p ps ih =>
    intro x i
    cases i with
    | zero => simp [layL]
    | succ i => simp [layL, Nat.testBit_bit_succ, ih]

theorem layL_and (ps : List ℕ) (u v : ℕ) : layL ps (u &&& v) = layL ps u &&& layL ps v := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, layL_tb, layL_tb, layL_tb, Nat.testBit_and]
  cases decide (i < ps.length) <;> simp

theorem layL_or (ps : List ℕ) (u v : ℕ) : layL ps (u ||| v) = layL ps u ||| layL ps v := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, layL_tb, layL_tb, layL_tb, Nat.testBit_or]
  cases decide (i < ps.length) <;> simp

theorem layL_lt : ∀ (ps : List ℕ) (x : ℕ), layL ps x < 2 ^ ps.length := by
  intro ps
  induction ps with
  | nil => intro x; simp [layL]
  | cons p ps ih =>
    intro x
    have h := ih x
    show Nat.bit (x.testBit p) (layL ps x) < 2 ^ (ps.length + 1)
    rw [Nat.bit_val, Nat.pow_succ]
    cases x.testBit p <;> simp <;> omega

def psL : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def lay (x : BitVec 24) : ℕ := layL psL x.toNat

def baseW : List (BitVec 24) := [8949779, 467977, 1593992, 12976960, 3236112, 5382182, 16256000, 10846368, 120900, 16292883]

def baseS : List (BitVec 24) := 0 :: (16777215 : BitVec 24) :: baseW

theorem baseW_sub {y : BitVec 24} (h : y ∈ baseW) : y ∈ baseS :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)

theorem zero_mem : (0 : BitVec 24) ∈ baseS := by
  unfold baseS; simp

theorem ones_mem : (16777215 : BitVec 24) ∈ baseS := by
  unfold baseS; simp

theorem lay_and (u v : BitVec 24) : lay (u &&& v) = lay u &&& lay v := by
  unfold lay
  rw [BitVec.toNat_and, layL_and]

theorem lay_or (u v : BitVec 24) : lay (u ||| v) = lay u ||| lay v := by
  unfold lay
  rw [BitVec.toNat_or, layL_or]

theorem lay_lt (x : BitVec 24) : lay x < 16777216 := by
  have h := layL_lt psL x.toNat
  have e : psL.length = 24 := rfl
  rw [e] at h
  have e2 : (2 : ℕ) ^ 24 = 16777216 := by norm_num
  rw [e2] at h
  exact h

theorem lay_base_all : (baseS.all fun u => decide (lay u ∈ base12)) = true := by decide +kernel

theorem lay_base : ∀ u ∈ baseS, lay u ∈ base12 :=
  fun u hu => of_decide_eq_true (List.all_eq_true.mp lay_base_all u hu)

theorem lay_target : lay (4095 : BitVec 24) = 4095 := by decide +kernel

theorem free_key (t : List (BitVec 24))
    (h : ∀ (j : ℕ) (hj : j < t.length), ∃ u ∈ baseS ++ t.take j, ∃ v ∈ baseS ++ t.take j,
      t[j] = u &&& v ∨ t[j] = u ||| v) :
    ∀ k, k ≤ t.length → ∃ s : List ℕ, Tr false s ∧ s.length ≤ k ∧
      ∀ x ∈ t.take k, lay x ∈ base12 ++ s := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨[], Tr.nil, le_rfl, fun x hx => by simp at hx⟩
  | succ k ih =>
    intro hk
    obtain ⟨s, hs, hl, hm⟩ := ih (by omega)
    have hk' : k < t.length := by omega
    obtain ⟨u, hu, v, hv, hop⟩ := h k hk'
    have hmem : ∀ y ∈ baseS ++ t.take k, lay y ∈ base12 ++ s := by
      intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · exact List.mem_append_left _ (lay_base y hy)
      · exact hm y hy
    have hop' : lay t[k] = lay u &&& lay v ∨ lay t[k] = lay u ||| lay v := by
      rcases hop with e | e
      · left; rw [e, lay_and]
      · right; rw [e, lay_or]
    have htk : t.take (k + 1) = t.take k ++ [t[k]] := by
      rw [List.take_succ_eq_append_getElem hk']
    by_cases hin : lay t[k] ∈ base12 ++ s
    · refine ⟨s, hs, by omega, ?_⟩
      intro x hx
      rw [htk] at hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hm x hx
      · rw [List.mem_singleton.mp hx]; exact hin
    · refine ⟨s ++ [lay t[k]], ?_, by simp; omega, ?_⟩
      · refine Tr.snoc s _ hs (lay_lt _) ?_ ⟨lay u, hmem u hu, lay v, hmem v hv, hop'⟩
        intro d hd
        show Nat.beq _ d = false
        rw [beq_false_iff]
        intro he
        exact hin (he ▸ hd)
      · intro x hx
        rw [htk] at hx
        rcases List.mem_append.mp hx with hx | hx
        · rcases List.mem_append.mp (hm x hx) with h1 | h1
          · exact List.mem_append_left _ h1
          · exact List.mem_append_right _ (List.mem_append_left _ h1)
        · rw [List.mem_singleton.mp hx]
          exact List.mem_append_right _ (List.mem_append_right _ (List.mem_singleton.mpr rfl))

theorem free_main (hc : NoStartH false 14) (t : List (BitVec 24))
    (h : ∀ (j : ℕ) (hj : j < t.length), ∃ u ∈ baseS ++ t.take j, ∃ v ∈ baseS ++ t.take j,
      t[j] = u &&& v ∨ t[j] = u ||| v)
    (ht : (4095 : BitVec 24) ∈ t) : 14 + 1 ≤ t.length := by
  by_contra hlt
  obtain ⟨s, hs, hl, hm⟩ := free_key t h t.length le_rfl
  have h1 := hm (4095 : BitVec 24) (by rw [List.take_length]; exact ht)
  rw [lay_target] at h1
  rcases List.mem_append.mp h1 with h2 | h2
  · exact absurd h2 (by decide)
  · exact no_trace hc hs (by omega) h2

theorem freeN_key (t : List ℕ)
    (h : ∀ (j : ℕ) (hj : j < t.length), ∃ u ∈ base12 ++ t.take j, ∃ v ∈ base12 ++ t.take j,
      t[j] = u &&& v ∨ t[j] = u ||| v) :
    ∀ k, k ≤ t.length → ∃ s : List ℕ, Tr false s ∧ s.length ≤ k ∧
      ∀ x ∈ t.take k, x ∈ base12 ++ s := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨[], Tr.nil, le_rfl, fun x hx => by simp at hx⟩
  | succ k ih =>
    intro hk
    obtain ⟨s, hs, hl, hm⟩ := ih (by omega)
    have hk' : k < t.length := by omega
    obtain ⟨u, hu, v, hv, hop⟩ := h k hk'
    have hmem : ∀ y ∈ base12 ++ t.take k, y ∈ base12 ++ s := by
      intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · exact List.mem_append_left _ hy
      · exact hm y hy
    have hbd : ∀ y ∈ base12 ++ s, y < 16777216 := by
      intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · exact base12_lt y hy
      · exact hs.bound y hy
    have hlt : t[k] < 16777216 := by
      have hu' := hbd u (hmem u hu)
      have hv' := hbd v (hmem v hv)
      have e : (16777216 : ℕ) = 2 ^ 24 := by norm_num
      rcases hop with e1 | e1
      · rw [e1]; exact lt_of_le_of_lt Nat.and_le_left hu'
      · rw [e1, e]; rw [e] at hu' hv'; exact Nat.or_lt_two_pow hu' hv'
    have htk : t.take (k + 1) = t.take k ++ [t[k]] := by
      rw [List.take_succ_eq_append_getElem hk']
    by_cases hin : t[k] ∈ base12 ++ s
    · refine ⟨s, hs, by omega, ?_⟩
      intro x hx
      rw [htk] at hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hm x hx
      · rw [List.mem_singleton.mp hx]; exact hin
    · refine ⟨s ++ [t[k]], ?_, by simp; omega, ?_⟩
      · refine Tr.snoc s _ hs hlt ?_ ⟨u, hmem u hu, v, hmem v hv, hop⟩
        intro d hd
        show Nat.beq _ d = false
        rw [beq_false_iff]
        intro he
        exact hin (he ▸ hd)
      · intro x hx
        rw [htk] at hx
        rcases List.mem_append.mp hx with hx | hx
        · rcases List.mem_append.mp (hm x hx) with h1 | h1
          · exact List.mem_append_left _ h1
          · exact List.mem_append_right _ (List.mem_append_left _ h1)
        · rw [List.mem_singleton.mp hx]
          exact List.mem_append_right _ (List.mem_append_right _ (List.mem_singleton.mpr rfl))

theorem freeN_main (hc : NoStartH false 14) (t : List ℕ)
    (h : ∀ (j : ℕ) (hj : j < t.length), ∃ u ∈ base12 ++ t.take j, ∃ v ∈ base12 ++ t.take j,
      t[j] = u &&& v ∨ t[j] = u ||| v)
    (ht : 4095 ∈ t) : 14 + 1 ≤ t.length := by
  by_contra hlt
  obtain ⟨s, hs, hl, hm⟩ := freeN_key t h t.length le_rfl
  have h1 := hm 4095 (by rw [List.take_length]; exact ht)
  rcases List.mem_append.mp h1 with h2 | h2
  · exact absurd h2 (by decide)
  · exact no_trace hc hs (by omega) h2

def ofBools : List Bool → ℕ
  | [] => 0
  | b :: l => Nat.bit b (ofBools l)

theorem ofBools_tb : ∀ (l : List Bool) (i : ℕ), (ofBools l).testBit i = l.getD i false := by
  intro l
  induction l with
  | nil => intro i; simp [ofBools]
  | cons b l ih =>
    intro i
    cases i with
    | zero => simp [ofBools]
    | succ i => simp [ofBools, Nat.testBit_bit_succ, ih]

theorem map_getD {α : Type} (L : List α) (f : α → Bool) (i : ℕ) :
    (L.map f).getD i false = (L[i]?.map f).getD false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]

theorem ofBools_and {α : Type} (L : List α) (f g : α → Bool) :
    ofBools (L.map fun X => f X && g X) = ofBools (L.map f) &&& ofBools (L.map g) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, ofBools_tb, ofBools_tb, ofBools_tb, map_getD, map_getD, map_getD]
  cases L[i]? <;> simp

theorem ofBools_or {α : Type} (L : List α) (f g : α → Bool) :
    ofBools (L.map fun X => f X || g X) = ofBools (L.map f) ||| ofBools (L.map g) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, ofBools_tb, ofBools_tb, ofBools_tb, map_getD, map_getD, map_getD]
  cases L[i]? <;> simp

theorem ofBools_false {α : Type} (L : List α) : ofBools (L.map fun _ => false) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [ofBools_tb, map_getD]
  cases L[i]? <;> simp

theorem ofBools_true {α : Type} (L : List α) (hL : L.length = 24) :
    ofBools (L.map fun _ => true) = 16777215 := by
  apply Nat.eq_of_testBit_eq
  intro i
  have e : (16777215 : ℕ) = 2 ^ 24 - 1 := by norm_num
  rw [ofBools_tb, map_getD, e, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < 24
  · have h1 : i < L.length := by omega
    simp [h1, hi]
  · have h1 : L.length ≤ i := by omega
    simp [h1, hi]

def stepW (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem fold_app : ∀ (G : List PEqualNP.CircuitLowerBounds.Gate) (X : List Bool),
    ∃ t : List Bool, G.foldl stepW X = X ++ t ∧ t.length = G.length := by
  intro G
  induction G with
  | nil => intro X; exact ⟨[], by simp, rfl⟩
  | cons g G ih =>
    intro X
    obtain ⟨t, h1, h2⟩ := ih (stepW X g)
    refine ⟨g.op.eval (g.inputs.map fun i => X.getD i false) :: t, ?_, ?_⟩
    · show List.foldl stepW (stepW X g) G = _
      rw [h1]
      show (X ++ [_]) ++ t = _
      rw [List.append_assoc]
      rfl
    · rw [List.length_cons, List.length_cons, h2]

theorem getD_app_lt (X t : List Bool) (i : ℕ) (h : i < X.length) :
    (X ++ t).getD i false = X.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_ge (X : List Bool) (i : ℕ) (h : X.length ≤ i) : X.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

theorem wires_spec : ∀ (G : List PEqualNP.CircuitLowerBounds.Gate) (X : List Bool) (j : ℕ)
    (hj : j < G.length), (G.foldl stepW X).getD (X.length + j) false =
      G[j].op.eval (G[j].inputs.map fun i =>
        decide (i < X.length + j) && (G.foldl stepW X).getD i false) := by
  intro G
  induction G with
  | nil => intro X j hj; exact absurd hj (by simp)
  | cons g G ih =>
    intro X j hj
    obtain ⟨t, h1, h2⟩ := fold_app G (stepW X g)
    have hfold : List.foldl stepW X (g :: G) = List.foldl stepW (stepW X g) G := rfl
    have hY : (stepW X g).length = X.length + 1 := by
      unfold stepW
      rw [List.length_append, List.length_singleton]
    cases j with
    | zero =>
      have e1 : (List.foldl stepW X (g :: G)).getD (X.length + 0) false =
          g.op.eval (g.inputs.map fun i => X.getD i false) := by
        rw [hfold, h1, Nat.add_zero, getD_app_lt _ _ _ (by rw [hY]; omega)]
        unfold stepW
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]
        simp
      have e2 : (fun i => decide (i < X.length + 0) && (List.foldl stepW X (g :: G)).getD i false) =
          fun i => X.getD i false := by
        funext i
        rw [hfold, h1, Nat.add_zero]
        by_cases hi : i < X.length
        · rw [getD_app_lt _ _ _ (by rw [hY]; omega)]
          unfold stepW
          rw [getD_app_lt _ _ _ hi]
          simp [hi]
        · rw [getD_ge X i (by omega)]
          simp [hi]
      rw [e1]
      show _ = g.op.eval (g.inputs.map _)
      rw [e2]
    | succ j =>
      have hj' : j < G.length := by
        rw [List.length_cons] at hj
        omega
      have e : X.length + (j + 1) = (stepW X g).length + j := by rw [hY]; omega
      have := ih (stepW X g) j hj'
      rw [hfold, e]
      exact this

def inpF (b : Bool) (x : Fin 8 → Bool) : List Bool :=
  [x 1, x 0, x 4, x 7, x 5, x 2, b, x 6, x 3, x 1 || b]

def inpOf (a : ℕ) : List Bool := inpF (a.testBit 8) fun (i : Fin 8) => a.testBit ↑i

def eRows : List ℕ := [3, 6, 12, 17, 34, 68, 136, 80, 160, 144, 257, 264]

def nRows : List ℕ := [26, 37, 56, 74, 105, 133, 193, 274, 308, 352, 388, 450]

def rowsL : List (List Bool) := (eRows ++ nRows).map inpOf

theorem rowsL_len : rowsL.length = 24 := by decide

theorem rowsL_all : (rowsL.all fun X => decide (X.length = 10)) = true := by decide +kernel

theorem rowsL_m {X : List Bool} (h : X ∈ rowsL) : X.length = 10 :=
  of_decide_eq_true (List.all_eq_true.mp rowsL_all X h)

def col0 (i : ℕ) : ℕ := ofBools (rowsL.map fun X => X.getD i false)

theorem col0_all : ((List.range 10).all fun i => decide (col0 i ∈ base12)) = true := by
  decide +kernel

theorem col0_mem (i : ℕ) (h : i < 10) : col0 i ∈ base12 :=
  of_decide_eq_true (List.all_eq_true.mp col0_all i (List.mem_range.mpr h))

def colOf (G : List PEqualNP.CircuitLowerBounds.Gate) (k : ℕ) : ℕ :=
  ofBools (rowsL.map fun X => (G.foldl stepW X).getD k false)

theorem colOf_lt (G : List PEqualNP.CircuitLowerBounds.Gate) (i : ℕ) (h : i < 10) :
    colOf G i = col0 i := by
  unfold colOf col0
  congr 1
  apply List.map_congr_left
  intro X hX
  obtain ⟨t, h1, _⟩ := fold_app G X
  rw [h1, getD_app_lt _ _ _ (by rw [rowsL_m hX]; exact h)]

theorem colOf_ge (G : List PEqualNP.CircuitLowerBounds.Gate) (k : ℕ) (h : 10 + G.length ≤ k) :
    colOf G k = 0 := by
  unfold colOf
  rw [← ofBools_false rowsL]
  congr 1
  apply List.map_congr_left
  intro X hX
  obtain ⟨t, h1, h2⟩ := fold_app G X
  rw [h1]
  exact getD_ge _ _ (by rw [List.length_append, rowsL_m hX, h2]; exact h)

theorem gate_col {α : Type} (L : List α) (hL : L.length = 24)
    (g : PEqualNP.CircuitLowerBounds.Gate)
    (hop : g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or)
    (hlen : g.inputs.length ≤ 2) (c : ℕ → α → Bool) :
    ∃ u v : ℕ, (u = 0 ∨ u = 16777215 ∨ ∃ i, u = ofBools (L.map (c i))) ∧
      (v = 0 ∨ v = 16777215 ∨ ∃ i, v = ofBools (L.map (c i))) ∧
      (ofBools (L.map fun X => g.op.eval (g.inputs.map fun i => c i X)) = u &&& v ∨
       ofBools (L.map fun X => g.op.eval (g.inputs.map fun i => c i X)) = u ||| v) := by
  obtain ⟨op, inputs⟩ := g
  simp only at hop hlen
  rcases inputs with _ | ⟨i, _ | ⟨j, _ | ⟨k, rest⟩⟩⟩
  · rcases hop with hop | hop <;> subst hop
    · refine ⟨16777215, 16777215, Or.inr (Or.inl rfl), Or.inr (Or.inl rfl), Or.inl ?_⟩
      show ofBools (L.map fun _ => true) = _
      rw [ofBools_true L hL]
      decide
    · refine ⟨0, 0, Or.inl rfl, Or.inl rfl, Or.inr ?_⟩
      show ofBools (L.map fun _ => false) = _
      rw [ofBools_false L]
      decide
  · rcases hop with hop | hop <;> subst hop
    · refine ⟨_, _, Or.inr (Or.inr ⟨i, rfl⟩), Or.inr (Or.inr ⟨i, rfl⟩), Or.inl ?_⟩
      rw [← ofBools_and]
      congr 1
      apply List.map_congr_left
      intro X _
      simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
    · refine ⟨_, _, Or.inr (Or.inr ⟨i, rfl⟩), Or.inr (Or.inr ⟨i, rfl⟩), Or.inr ?_⟩
      rw [← ofBools_or]
      congr 1
      apply List.map_congr_left
      intro X _
      simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
  · rcases hop with hop | hop <;> subst hop
    · refine ⟨_, _, Or.inr (Or.inr ⟨i, rfl⟩), Or.inr (Or.inr ⟨j, rfl⟩), Or.inl ?_⟩
      rw [← ofBools_and]
      congr 1
      apply List.map_congr_left
      intro X _
      simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
    · refine ⟨_, _, Or.inr (Or.inr ⟨i, rfl⟩), Or.inr (Or.inr ⟨j, rfl⟩), Or.inr ?_⟩
      rw [← ofBools_or]
      congr 1
      apply List.map_congr_left
      intro X _
      simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
  · simp only [List.length_cons] at hlen
    omega


theorem circ_any (hc : NoStartH false 14) (G : List PEqualNP.CircuitLowerBounds.Gate)
    (hlen : G.length ≤ 14)
    (hmono : ∀ g ∈ G, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) (out : ℕ) :
    colOf G out ≠ 4095 := by
  intro htgt
  have hfree : ∀ (j : ℕ) (hj : j < ((List.range G.length).map fun j => colOf G (10 + j)).length),
      ∃ u ∈ base12 ++ ((List.range G.length).map fun j => colOf G (10 + j)).take j,
      ∃ v ∈ base12 ++ ((List.range G.length).map fun j => colOf G (10 + j)).take j,
        ((List.range G.length).map fun j => colOf G (10 + j))[j] = u &&& v ∨
        ((List.range G.length).map fun j => colOf G (10 + j))[j] = u ||| v := by
    intro j hj
    have hjG : j < G.length := by
      rw [List.length_map, List.length_range] at hj
      exact hj
    have e0 : ((List.range G.length).map fun j => colOf G (10 + j))[j]'hj = colOf G (10 + j) := by
      rw [List.getElem_map, List.getElem_range]
    have e1 : colOf G (10 + j) = ofBools (rowsL.map fun X => G[j].op.eval (G[j].inputs.map fun i =>
        decide (i < 10 + j) && (G.foldl stepW X).getD i false)) := by
      unfold colOf
      congr 1
      apply List.map_congr_left
      intro X hX
      have := wires_spec G X j hjG
      rw [rowsL_m hX] at this
      exact this
    obtain ⟨hop, hl2⟩ := hmono G[j] (List.getElem_mem hjG)
    obtain ⟨u, v, hu, hv, huv⟩ := gate_col rowsL rowsL_len G[j] hop hl2
      (fun i X => decide (i < 10 + j) && (G.foldl stepW X).getD i false)
    have hin : ∀ w : ℕ, (w = 0 ∨ w = 16777215 ∨ ∃ i, w = ofBools (rowsL.map
        (fun X => decide (i < 10 + j) && (G.foldl stepW X).getD i false))) →
        w ∈ base12 ++ ((List.range G.length).map fun j => colOf G (10 + j)).take j := by
      intro w hw
      rcases hw with hw | hw | ⟨i, hw⟩
      · rw [hw]; exact List.mem_append_left _ (by decide)
      · rw [hw]; exact List.mem_append_left _ (by decide)
      · by_cases hi : i < 10 + j
        · have e2 : w = colOf G i := by
            rw [hw]
            unfold colOf
            congr 1
            apply List.map_congr_left
            intro X _
            simp [hi]
          by_cases hi2 : i < 10
          · rw [e2, colOf_lt G i hi2]
            exact List.mem_append_left _ (col0_mem i hi2)
          · apply List.mem_append_right
            rw [e2, List.mem_take_iff_getElem]
            refine ⟨i - 10, by rw [List.length_map, List.length_range]; omega, ?_⟩
            rw [List.getElem_map, List.getElem_range]
            congr 1
            omega
        · have e2 : w = 0 := by
            rw [hw, ← ofBools_false rowsL]
            congr 1
            apply List.map_congr_left
            intro X _
            simp [hi]
          rw [e2]; exact List.mem_append_left _ (by decide)
    have e01 := e0.trans e1
    rcases huv with h | h
    · exact ⟨u, hin u hu, v, hin v hv, Or.inl (e01.trans h)⟩
    · exact ⟨u, hin u hu, v, hin v hv, Or.inr (e01.trans h)⟩
  have ht : 4095 ∈ (List.range G.length).map fun j => colOf G (10 + j) := by
    by_cases h1 : out < 10
    · have := col0_mem out h1
      rw [← colOf_lt G out h1, htgt] at this
      exact absurd this (by decide)
    · by_cases h3 : out < 10 + G.length
      · rw [List.mem_map]
        refine ⟨out - 10, List.mem_range.mpr (by omega), ?_⟩
        rw [← htgt]
        congr 1
        omega
      · have := colOf_ge G out (by omega)
        rw [htgt] at this
        exact absurd this (by decide)
  have := freeN_main hc _ hfree ht
  rw [List.length_map, List.length_range] at this
  omega

theorem shape_gen (hc : NoStartH false 14) (F0 F1 : (Fin 8 → Bool) → Bool)
    (Q1 Q2 : PEqualNP.CircuitLowerBounds.Circuit → Prop)
    (hF : ofBools ((eRows ++ nRows).map fun a =>
      bif a.testBit 8 then F1 fun (i : Fin 8) => a.testBit ↑i
      else F0 fun (i : Fin 8) => a.testBit ↑i) = 4095) :
    ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 →
      x4.size = 14 →
      List.countP (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => x7.op.eval [Bool.false]) x4.gates = 0 →
      Q1 x4 → Q2 x4 →
      (∀ (x10 : Fin 8 → Bool), x4.eval ([x10 1, x10 0, x10 4, x10 7, x10 5, x10 2, Bool.false, x10 6, x10 3, x10 1 || Bool.false]) = F0 x10) →
      ∃ (x11 : Fin 8 → Bool), x4.eval ([x11 1, x11 0, x11 4, x11 7, x11 5, x11 2, Bool.true, x11 6, x11 3, x11 1 || Bool.true]) ≠ F1 x11 := by
  intro C hfan hsize hcnt _ _ h0
  by_contra hne
  have h1 : ∀ x11 : Fin 8 → Bool, C.eval (inpF true x11) = F1 x11 := by
    intro x11
    by_contra h
    exact hne ⟨x11, h⟩
  have hm : ∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨hop, hl⟩ := hfan g hg
    have hn : ¬ (g.op.eval [false] = true) := List.countP_eq_zero.mp hcnt g hg
    have h3 : g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.not := by
      simpa using hop
    refine ⟨?_, hl⟩
    rcases h3 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      apply hn
      rw [h]
      rfl
  apply circ_any hc C.gates (le_of_eq hsize) hm C.output
  rw [← hF]
  unfold colOf rowsL
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro a _
  show C.eval (inpF (a.testBit 8) fun (i : Fin 8) => a.testBit ↑i) =
    bif a.testBit 8 then F1 fun (i : Fin 8) => a.testBit ↑i
    else F0 fun (i : Fin 8) => a.testBit ↑i
  cases a.testBit 8
  · exact h0 fun (i : Fin 8) => a.testBit ↑i
  · exact h1 fun (i : Fin 8) => a.testBit ↑i

theorem shape_sound (hc : NoStartH false 14) :
    have x1 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) => (if x1.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x1.inputs else x1.inputs).any fun (x2 : ℕ) => Decidable.decide (x2 = (6 : ℕ)); have x2 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x2 : Bool) (x3 : Fin (8 : ℕ) → Bool) => [x3 (1 : Fin (8 : ℕ)), x3 (0 : Fin (8 : ℕ)), x3 (4 : Fin (8 : ℕ)), x3 (7 : Fin (8 : ℕ)), x3 (5 : Fin (8 : ℕ)), x3 (2 : Fin (8 : ℕ)), x2, x3 (6 : Fin (8 : ℕ)), x3 (3 : Fin (8 : ℕ)), x3 (1 : Fin (8 : ℕ)) || x2]; have x3 : (Fin (8 : ℕ) → Bool) → Bool := fun (x3 : Fin (8 : ℕ) → Bool) => x3 (0 : Fin (8 : ℕ)) && x3 (1 : Fin (8 : ℕ)) || x3 (1 : Fin (8 : ℕ)) && x3 (2 : Fin (8 : ℕ)) || x3 (2 : Fin (8 : ℕ)) && x3 (3 : Fin (8 : ℕ)) || x3 (0 : Fin (8 : ℕ)) && x3 (4 : Fin (8 : ℕ)) || x3 (1 : Fin (8 : ℕ)) && x3 (5 : Fin (8 : ℕ)) || x3 (2 : Fin (8 : ℕ)) && x3 (6 : Fin (8 : ℕ)) || x3 (3 : Fin (8 : ℕ)) && x3 (7 : Fin (8 : ℕ)) || x3 (4 : Fin (8 : ℕ)) && x3 (6 : Fin (8 : ℕ)) || x3 (5 : Fin (8 : ℕ)) && x3 (7 : Fin (8 : ℕ)) || x3 (7 : Fin (8 : ℕ)) && x3 (4 : Fin (8 : ℕ)); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → x4.size = (14 : ℕ) → List.countP (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => x7.op.eval [Bool.false]) x4.gates = (0 : ℕ) → List.countP x1 x4.gates ≤ (1 : ℕ) → (∃ x9 ∈ x4.gates, x9.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (6 : ℕ) ∈ x9.inputs) → (∀ (x10 : Fin (8 : ℕ) → Bool), x4.eval (x2 Bool.false x10) = x3 x10) → ∃ (x11 : Fin (8 : ℕ) → Bool), x4.eval (x2 Bool.true x11) ≠ (x3 x11 || x11 (0 : Fin (8 : ℕ)) || x11 (3 : Fin (8 : ℕ))) :=
  shape_gen hc _ _ _ _ (by decide +kernel)

end PEqualNP.Outside.L_meta_3969

theorem PEqualNP.Outside.L_meta_3969 :
    have x1 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) => (if x1.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x1.inputs else x1.inputs).any fun (x2 : ℕ) => Decidable.decide (x2 = (6 : ℕ)); have x2 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x2 : Bool) (x3 : Fin (8 : ℕ) → Bool) => [x3 (1 : Fin (8 : ℕ)), x3 (0 : Fin (8 : ℕ)), x3 (4 : Fin (8 : ℕ)), x3 (7 : Fin (8 : ℕ)), x3 (5 : Fin (8 : ℕ)), x3 (2 : Fin (8 : ℕ)), x2, x3 (6 : Fin (8 : ℕ)), x3 (3 : Fin (8 : ℕ)), x3 (1 : Fin (8 : ℕ)) || x2]; have x3 : (Fin (8 : ℕ) → Bool) → Bool := fun (x3 : Fin (8 : ℕ) → Bool) => x3 (0 : Fin (8 : ℕ)) && x3 (1 : Fin (8 : ℕ)) || x3 (1 : Fin (8 : ℕ)) && x3 (2 : Fin (8 : ℕ)) || x3 (2 : Fin (8 : ℕ)) && x3 (3 : Fin (8 : ℕ)) || x3 (0 : Fin (8 : ℕ)) && x3 (4 : Fin (8 : ℕ)) || x3 (1 : Fin (8 : ℕ)) && x3 (5 : Fin (8 : ℕ)) || x3 (2 : Fin (8 : ℕ)) && x3 (6 : Fin (8 : ℕ)) || x3 (3 : Fin (8 : ℕ)) && x3 (7 : Fin (8 : ℕ)) || x3 (4 : Fin (8 : ℕ)) && x3 (6 : Fin (8 : ℕ)) || x3 (5 : Fin (8 : ℕ)) && x3 (7 : Fin (8 : ℕ)) || x3 (7 : Fin (8 : ℕ)) && x3 (4 : Fin (8 : ℕ)); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → x4.size = (14 : ℕ) → List.countP (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => x7.op.eval [Bool.false]) x4.gates = (0 : ℕ) → List.countP x1 x4.gates ≤ (1 : ℕ) → (∃ x9 ∈ x4.gates, x9.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (6 : ℕ) ∈ x9.inputs) → (∀ (x10 : Fin (8 : ℕ) → Bool), x4.eval (x2 Bool.false x10) = x3 x10) → ∃ (x11 : Fin (8 : ℕ) → Bool), x4.eval (x2 Bool.true x11) ≠ (x3 x11 || x11 (0 : Fin (8 : ℕ)) || x11 (3 : Fin (8 : ℕ))) :=
  PEqualNP.Outside.L_meta_3969.shape_sound PEqualNP.Outside.L_meta_3969.noStartH
