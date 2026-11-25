import Mathlib.Data.Finset.Card
import Mathlib.Data.Tree.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.Bitwise

namespace PEqualNP.Outside.L_meta_4883

def domN (w d : ℕ) : Bool :=
  Nat.beq (Nat.land (Nat.land w 4095) (Nat.sub 16777215 d)) 0 &&
  Nat.beq (Nat.land (Nat.land d (Nat.sub 16777215 w)) 16773120) 0

def blk (m : Bool) (w d : ℕ) : Bool := cond m (domN w d) (Nat.beq w d)

def base10 : List ℕ :=
  [113184, 430348, 902208, 3227782, 5521457, 7684279, 8532035, 11083800, 13501056, 15731968]

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
  letN (dsw 2097153 1 x) fun x => letN (dsw 65536 2 x) fun x => letN (dsw 276 3 x) fun x => letN (dsw 8192 4 x) fun x => dsw 8 6 x

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
  unfold PEqualNP.Outside.L_meta_4883.domN
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
  have e : sig1 = fun x => dsw 8 6 (dsw 8192 4 (dsw 276 3 (dsw 65536 2 (dsw 2097153 1 x)))) := by
    funext x; simp only [sig1, letN_eq]
  rw [e]
  exact (dsw_perm 8 6 (by decide) (by decide)).comp ((dsw_perm 8192 4 (by decide) (by decide)).comp ((dsw_perm 276 3 (by decide) (by decide)).comp ((dsw_perm 65536 2 (by decide) (by decide)).comp (dsw_perm 2097153 1 (by decide) (by decide)))))

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
def T6 : Tree := (.node [3395,506668,3275430,5689661,7684279,11083800,13501056] .nil .nil)
theorem T6_ok : tall (expFast false (RP PR T5 BinaryTree.nil 5) T5 5) T6 = true := by decide +kernel
def T7 : Tree := (.node [3395,113184,506668,3227782,5689661,7684279,11083800,13501056] (.node [67,3328,506668,3275430,5689661,7684279,11083800,13501056] .nil .nil) .nil)
theorem T7_ok : tall (expFast false (RP PR T6 BinaryTree.nil 6) T6 6) T7 = true := by decide +kernel
def T8 : Tree := (.node [79,113184,1037644,3227782,5521457,11083800,13501056,15731968] (.node [67,113184,1037644,3227782,5521457,11083800,13501056,15731980] (.node [67,113184,506668,902208,3227782,5521457,11083800,13501056,15731980] (.node [67,3328,113184,506668,3227782,5689661,7684279,11083800,13501056] .nil .nil) .nil) (.node [79,113184,506668,902208,3227782,5521457,11083800,13501056,15731968] (.node [67,506668,1048428,3275430,5689661,7684279,11083800,13501056,15731968] .nil .nil) .nil)) (.node [3328,506668,3275430,5689661,7684279,8242423,8532035,11083800,13501056] (.node [3328,113184,430348,902208,3227782,7684279,8532083,11083800,13501056] (.node [335,113184,902208,3227782,5521457,11083800,13501056,15731968] .nil .nil) .nil) (.node [3395,113184,430348,506668,3227782,5521457,7684279,11083800,13501056] (.node [3376,113184,430348,902208,3227782,7684279,8532035,11083800,13501056] .nil .nil) .nil)))
theorem T8_ok : tall (expFast false (RP PR T7 BinaryTree.nil 7) T7 7) T8 = true := by decide +kernel
def T9aa : Tree := (.node [67,113184,430348,507692,3227782,5521457,7684279,11083800,13501056,15731968] (.node [67,268,113184,902208,3227782,5521457,11083800,13501056,15731968] (.node [12,67,113184,1037644,3227782,5521457,11083800,13501056,15731968] (.node [12,67,113184,506668,902208,3227782,5521457,11083800,13501056,15731968] .nil .nil) (.node [48,3328,113184,430348,902208,3227782,7684279,8532035,11083800,13501056] .nil .nil)) (.node [67,66080,430348,506668,902208,3227782,5521457,11083800,13501056,15731968] (.node [67,3328,113184,430348,506668,3227782,5521457,7684279,11083800,13501056] .nil .nil) .nil)) (.node [67,113184,506668,1037644,3227782,5689661,7684279,11083800,13501056,15731968] (.node [67,113184,431372,507692,3227782,5521457,7684279,11083800,13501056,15731968] (.node [67,113184,430348,902208,3227782,5521457,11083800,13501056,15731980] .nil .nil) .nil) (.node [67,506668,902208,3275430,5689661,7684279,11083800,13501056,15731968] (.node [67,113184,506668,1048428,3227782,5689661,7684279,11083800,13501056,15731968] .nil .nil) .nil)))
theorem T9aa_ok : tall (expFast false (RP PR T8 BinaryTree.nil 8) T8 8) T9aa = true := by decide +kernel
def T9ab : Tree := (.node [3328,506668,902208,3275430,5689661,7684279,8532035,11083800,13501056] (.node [3328,113184,430348,506668,3227782,5521457,7684343,8532035,11083800,13501056] (.node [1091,113184,430348,506668,3227782,5521457,7684279,11083800,13501056,15731968] (.node [1088,506668,3275430,5689661,7684279,8532035,11083800,13501056,15731968] .nil .nil) (.node [3328,65668,113184,430348,902208,5521457,7684279,8532035,11083800,13501056] .nil .nil)) (.node [3328,113184,506668,3227782,5689661,7684279,8242423,8532035,11083800,13501056] (.node [3328,113184,506668,3227782,5689661,6145137,7684279,8532035,11083800,13501056] .nil .nil) .nil)) (.node [113184,430348,506668,902208,3227782,5521523,7684279,11083867,13501056,15731968] (.node [113184,430348,506668,902208,3227782,5521457,7687607,8535363,11083800,13501056] (.node [3392,113184,430348,506668,3227782,5521457,7684279,8532035,11083800,13501056] .nil .nil) .nil) (.node [113184,430348,506668,902211,3227782,5521457,7684279,11083800,13501056,15732035] (.node [113184,430348,506668,902208,3227782,5524785,7684279,8532035,11087128,13501056] .nil .nil) .nil)))
theorem T9ab_ok : tall (expFast false (RP PR T8 BinaryTree.nil 8) T8 8) T9ab = true := by decide +kernel
def T9a : Tree := .node [79,113184,430348,902208,3227782,5521457,11083800,13501056,15731968] T9aa T9ab
theorem T9a_ok : tall (expFast false (RP PR T8 BinaryTree.nil 8) T8 8) T9a = true :=
  tall_node _ _ _ _ T9aa_ok (by decide +kernel) T9ab_ok
def T9ba : Tree := (.node [113184,430348,507756,3227782,5521457,7684279,8532035,11083800,13501056,15732032] (.node [113184,430348,506671,902208,3227782,5521457,11083800,13501056,15875395,16076215] (.node [113184,430348,506668,3227782,5521457,7685367,8533059,11083800,13501056,15731968] (.node [113184,430348,506668,904512,3227782,5521457,7684279,8535363,11083800,13501056] .nil .nil) (.node [113184,430348,506668,3227782,5522545,7684279,8532035,11084888,13501056,15731968] .nil .nil)) (.node [113184,430348,507692,3227782,5521457,7684343,8532035,11083800,13501056,15731968] (.node [113184,430348,506735,902208,3227782,5521457,7684279,11083800,13501056,15732035] .nil .nil) .nil)) (.node [113184,430348,902208,3227782,5521457,7686583,8895343,11083800,13501056,15875395] (.node [113184,430348,902208,1048428,3227782,7684279,8532083,11083800,13501056,15731968] (.node [113184,430348,507756,3227782,5521457,7685367,8532035,11083800,13501056,15731968] .nil .nil) .nil) (.node [113184,430351,506671,902208,3227782,5521457,11083800,13501056,15875395,16076215] (.node [113184,430348,904512,3227782,5521457,7684279,8895343,11083800,13501056,15875395] .nil .nil) .nil)))
theorem T9ba_ok : tall (expFast false (RP PR T8 BinaryTree.nil 8) T8 8) T9ba = true := by decide +kernel
def T9bb : Tree := (.node [113184,431436,507756,3227782,5521457,7684279,8532035,11084888,13501056,15731968] (.node [113184,431372,507692,3227782,5521457,7684343,8532035,11083800,13501056,15731968] (.node [113184,430415,506735,902208,3227782,5521457,7684279,11083867,13501056,15731968] (.node [113184,430415,506735,902208,3227782,5521457,7684279,11083800,13501056,15732035] .nil .nil) .nil) (.node [113184,431436,507756,3227782,5521457,7684279,8532035,11083800,13501056,15732032] (.node [113184,431436,506668,3227782,5521457,7684279,8532035,11084888,13501056,15731968] .nil .nil) .nil)) (.node [113184,506668,902208,3227782,5521457,8242423,8532035,11083800,13501056,15731980] (.node [113184,433420,506668,902208,3227782,5521457,7684279,8532035,11087128,13501056] (.node [113184,431436,507756,3227782,5521457,7685367,8532035,11083800,13501056,15731968] .nil .nil) .nil) (.node [506668,1048428,3275430,5689661,7684279,8242423,8532035,11083800,13501056,15731968] (.node [113184,1037644,3227782,5521457,8242423,8532035,11083800,13501056,15731980] .nil .nil) .nil)))
theorem T9bb_ok : tall (expFast false (RP PR T8 BinaryTree.nil 8) T8 8) T9bb = true := by decide +kernel
def T9b : Tree := .node [113184,430415,506668,902208,3227782,5521457,7684279,11083867,13501056,15731968] T9ba T9bb
theorem T9b_ok : tall (expFast false (RP PR T8 BinaryTree.nil 8) T8 8) T9b = true :=
  tall_node _ _ _ _ T9ba_ok (by decide +kernel) T9bb_ok
def T9 : Tree := .node [113184,430348,506668,902211,3227782,5521457,11083800,13501056,15875395,16076215] T9a T9b
theorem T9_ok : tall (expFast false (RP PR T8 BinaryTree.nil 8) T8 8) T9 = true :=
  tall_node _ _ _ _ T9a_ok (by decide +kernel) T9b_ok
def T10aaaaa : Tree := (.node [12,67,113184,430348,902208,3227782,5521457,11083800,13501056,15731968] (.node [3,113184,430348,506668,902208,3227782,5521457,7684279,11083800,13501056,15732032] (.node [3,1088,113184,430348,506668,3227782,5521457,7684279,11083800,13501056,15731968] .nil .nil) (.node [3,113184,430348,506668,902208,3227782,5521457,11083800,13501056,15875395,16076215] .nil .nil)) (.node [12,113184,1037644,3227782,5521457,8242423,8532035,11083800,13501056,15731968] (.node [12,113184,506668,902208,3227782,5521457,8242423,8532035,11083800,13501056,15731968] .nil .nil) (.node [24,113184,430348,902208,3227782,3275430,5521457,8532035,13501056,15731968,15875395] .nil .nil)))
theorem T10aaaaa_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10aaaaa = true := by decide +kernel
def T10aaaab : Tree := (.node [64,113184,430348,507692,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [49,113184,430348,902208,3227782,8532035,8632931,11083800,13501056,15731968,15814022] (.node [48,113184,430348,902208,1048428,3227782,7684279,8532035,11083800,13501056,15731968] .nil .nil) (.node [64,3328,113184,430348,506668,3227782,5521457,7684279,8532035,11083800,13501056] .nil .nil)) (.node [67,1024,113184,430348,506668,3227782,5521457,7684279,11083800,13501056,15731968] (.node [64,113184,431372,507692,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) .nil))
theorem T10aaaab_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10aaaab = true := by decide +kernel
def T10aaaa : Tree := .node [24,113184,430348,902208,3227782,5521457,8532035,8632931,13501056,15731968,15814022] T10aaaaa T10aaaab
theorem T10aaaa_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10aaaa = true :=
  tall_node _ _ _ _ T10aaaaa_ok (by decide +kernel) T10aaaab_ok
def T10aaab : Tree := (.node [67,113184,430348,506668,902208,3227782,5521457,11083800,12148894,13501056,15731968] (.node [67,113184,430348,506668,902208,3227782,5521457,7684279,11083800,13501056,15732035] (.node [67,113184,327716,430348,506668,902208,3227782,5521457,11083800,13501056,15731968] (.node [67,113184,114208,430348,3227782,5521457,7684279,11083800,13501056,15731968] .nil .nil) (.node [67,113184,430348,506668,902208,3227782,5521457,7684279,11083800,13501056,15731968] .nil .nil)) (.node [67,113184,430348,506668,902208,3227782,5521457,7684343,11083800,13501056,15731968] (.node [67,113184,430348,506668,902208,3227782,5521457,7684279,11083800,13501123,15731968] .nil .nil) .nil)) (.node [67,113184,430348,506668,902208,3227782,5521523,7684279,11083800,13501056,15731968] (.node [67,113184,430348,506668,902208,3227782,5521457,11083800,13501056,15731968,16076215] (.node [67,113184,430348,506668,902208,3227782,5521457,11083800,13501056,15671960,15731968] .nil .nil) (.node [67,113184,430348,506668,902208,3227782,5521457,11083800,13501056,15731968,16605375] .nil .nil)) (.node [67,113184,430348,506668,902208,3227782,7684279,11083800,13501056,14566065,15731968] (.node [67,113184,430348,506668,902208,3227782,5689661,7684279,11083800,13501056,15731968] .nil .nil) .nil)))
theorem T10aaab_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10aaab = true := by decide +kernel
def T10aaa : Tree := .node [67,66080,113184,430348,902208,3227782,5521457,11083800,13501056,15731968] T10aaaa T10aaab
theorem T10aaa_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10aaa = true :=
  tall_node _ _ _ _ T10aaaa_ok (by decide +kernel) T10aaab_ok
def T10aabaa : Tree := (.node [67,113184,430348,902208,3227782,5521457,11083800,13501056,15731968,16346526] (.node [67,113184,430348,506668,1048428,3227782,5521457,7684279,11083800,13501056,15731968] (.node [67,113184,430348,506668,917088,3227782,5521457,7684279,11083800,13501056,15731968] .nil .nil) (.node [67,113184,430348,506735,902208,3227782,5521457,7684279,11083800,13501056,15731968] .nil .nil)) (.node [67,113184,430348,917088,3227782,5521457,11083800,13501056,14566065,15731968] (.node [67,113184,430348,902208,3275430,5689661,7684279,11083800,13501056,15731968] .nil .nil) .nil))
theorem T10aabaa_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10aabaa = true := by decide +kernel
def T10aabab : Tree := (.node [67,113184,431372,3227782,5521457,7684279,11083800,13501056,15731968] (.node [67,113184,430415,506668,902208,3227782,5521457,7684279,11083800,13501056,15731968] (.node [67,113184,430348,917088,3275430,5521457,7684279,11083800,13501056,15731968] .nil .nil) (.node [67,113184,430415,506735,902208,3227782,5521457,7684279,11083800,13501056,15731968] .nil .nil)) (.node [268,113184,902208,3227782,5521457,8242423,8532035,11083800,13501056,15731968] (.node [67,113184,506668,902208,3227782,5689661,7684279,11083800,13501056,15731968] .nil .nil) .nil))
theorem T10aabab_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10aabab = true := by decide +kernel
def T10aaba : Tree := .node [67,113184,430348,917088,3227782,7684279,11083800,13501056,14566065,15731968] T10aabaa T10aabab
theorem T10aaba_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10aaba = true :=
  tall_node _ _ _ _ T10aabaa_ok (by decide +kernel) T10aabab_ok
def T10aabb : Tree := (.node [1088,113184,430348,506668,3227782,5521457,7685367,8532035,11083800,13501056,15731968] (.node [1088,113184,430348,506668,3227782,5521457,7684279,8532035,11083800,13501056,15732032] (.node [1088,2304,113184,430348,506668,3227782,5521457,7684279,8532035,11083800,13501056] (.node [1024,113184,430348,506668,3227782,5521457,7684343,8532035,11083800,13501056,15731968] .nil .nil) (.node [1088,113184,430348,506668,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)) (.node [1088,113184,430348,506668,3227782,5521457,7684279,8533059,11083800,13501056,15731968] (.node [1088,113184,430348,506668,3227782,5521457,7684279,8532035,11083800,13502144,15731968] .nil .nil) .nil)) (.node [1088,113184,430348,3275430,5689661,7684279,8532035,11083800,13501056,15731968] (.node [1088,113184,430348,507756,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [1088,113184,430348,506668,3227782,5522545,7684279,8532035,11083800,13501056,15731968] .nil .nil) (.node [1088,113184,430348,3227782,3275430,5521457,5689661,8532035,11083800,13501056,15731968] .nil .nil)) (.node [1088,113184,431436,507756,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [1088,113184,431436,506668,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) .nil)))
theorem T10aabb_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10aabb = true := by decide +kernel
def T10aab : Tree := .node [268,113184,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731968,15814022] T10aaba T10aabb
theorem T10aab_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10aab = true :=
  tall_node _ _ _ _ T10aaba_ok (by decide +kernel) T10aabb_ok
def T10aa : Tree := .node [67,113184,430348,506668,902211,3227782,5521457,7684279,11083800,13501056,15731968] T10aaa T10aab
theorem T10aa_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10aa = true :=
  tall_node _ _ _ _ T10aaa_ok (by decide +kernel) T10aab_ok
def T10abaaa : Tree := (.node [3328,113184,327716,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056] (.node [2304,113184,430348,506668,902208,3227782,5521457,7684279,8533059,11083800,13501056] (.node [1091,113184,430348,3227782,5521457,7684279,11083800,13501056,15731968] .nil .nil) (.node [2304,113184,430348,902208,3227782,5521457,7684279,8895343,11083800,13501056,15875395] .nil .nil)) (.node [3328,113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13504384] (.node [3328,113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056] .nil .nil) (.node [3328,113184,430348,506668,902208,3227782,5521457,7684279,8535363,11083800,13501056] .nil .nil)))
theorem T10abaaa_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10abaaa = true := by decide +kernel
def T10abaab : Tree := (.node [3328,113184,430348,506668,3227782,5521457,7684279,8242423,8532035,11083800,13501056] (.node [3328,113184,430348,506668,904512,3227782,5521457,7684279,8532035,11083800,13501056] (.node [3328,113184,430348,506668,902208,3227782,5524785,7684279,8532035,11083800,13501056] .nil .nil) (.node [3328,113184,430348,506668,3227782,4048070,5521457,7684279,8532035,11083800,13501056] .nil .nil)) (.node [3328,113184,430348,902208,3227782,5521457,7684279,8532035,8895343,11083800,13501056] (.node [3328,113184,430348,507692,902208,3227782,5521457,7684279,8532035,11083800,13501056] .nil .nil) .nil))
theorem T10abaab_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10abaab = true := by decide +kernel
def T10abaa : Tree := .node [3328,113184,430348,506668,902208,3227782,5521457,7687607,8532035,11083800,13501056] T10abaaa T10abaab
theorem T10abaa_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10abaa = true :=
  tall_node _ _ _ _ T10abaaa_ok (by decide +kernel) T10abaab_ok
def T10ababa : Tree := (.node [3328,113184,433420,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056] (.node [3328,113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15671960] (.node [3328,113184,430348,902208,3227782,5521457,7684279,8532035,11083800,11516732,13501056] .nil .nil) (.node [3328,113184,431372,507692,902208,3227782,5521457,7684279,8532035,11083800,13501056] .nil .nil)) (.node [3328,113184,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,13538188] (.node [3328,113184,506668,902208,3227782,5521457,5689661,7684279,8532035,11083800,13501056] .nil .nil) .nil))
theorem T10ababa_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10ababa = true := by decide +kernel
def T10ababb : Tree := (.node [113184,113251,430348,902208,3227782,5521457,7684279,11083800,13501056,15732035] (.node [66080,430348,506668,902208,3227782,5521457,8242423,8532035,11083800,13501056,15731968] (.node [65668,113184,430348,902208,1048428,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,113187,430348,902208,3227782,5521457,11083800,13501056,15875395,16076215] .nil .nil)) (.node [113184,114208,430348,3227782,5521457,7684343,8532035,11083800,13501056,15731968] (.node [113184,113251,430348,902208,3227782,5521457,7684279,11083800,13501123,15731968] .nil .nil) .nil))
theorem T10ababb_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10ababb = true := by decide +kernel
def T10abab : Tree := .node [3328,113184,506668,902208,3227782,5689661,7684279,8532035,11083800,13501056] T10ababa T10ababb
theorem T10abab_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10abab = true :=
  tall_node _ _ _ _ T10ababa_ok (by decide +kernel) T10ababb_ok
def T10aba : Tree := .node [3328,113184,430348,902208,3227782,5521457,7684279,8532035,11083800,11123256,13501056] T10abaa T10abab
theorem T10aba_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10aba = true :=
  tall_node _ _ _ _ T10abaa_ok (by decide +kernel) T10abab_ok
def T10abbaa : Tree := (.node [113184,330020,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15875395] (.node [113184,114272,430348,3227782,5521457,7685367,8532035,11083800,13501056,15731968] (.node [113184,114272,430348,3227782,5521457,7684279,8532035,11083800,13502144,15731968] .nil .nil) (.node [113184,327719,430348,506668,902208,3227782,5521457,11083800,13501056,15731968,15875395] .nil .nil)) (.node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15732033] (.node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15732032] .nil .nil) .nil))
theorem T10abbaa_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10abbaa = true := by decide +kernel
def T10abbab : Tree := (.node [113184,430348,506668,902208,3227782,5521457,7684279,8533315,11083800,13501056,15731968] (.node [113184,430348,506668,902208,3227782,5521457,7684279,8533059,11083800,13501056,15731968] (.node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501120,15732032] .nil .nil) (.node [113184,430348,506668,902208,3227782,5521457,7684279,8533059,11083800,13502080,15731968] .nil .nil)) (.node [113184,430348,506668,902208,3227782,5521457,7684343,8532035,11083800,13501056,15731968] (.node [113184,430348,506668,902208,3227782,5521457,7684279,8535363,11083800,13501056,15731968] .nil .nil) .nil))
theorem T10abbab_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10abbab = true := by decide +kernel
def T10abba : Tree := .node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15732035] T10abbaa T10abbab
theorem T10abba_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10abba = true :=
  tall_node _ _ _ _ T10abbaa_ok (by decide +kernel) T10abbab_ok
def T10abbb : Tree := (.node [113184,430348,506668,902208,3227782,5521521,7684279,8532035,11083800,13501056,15732032] (.node [113184,430348,506668,902208,3227782,5521457,7686583,8532035,11083800,13501056,15875395] (.node [113184,430348,506668,902208,3227782,5521457,7685303,8533059,11083800,13501056,15731968] (.node [113184,430348,506668,902208,3227782,5521457,7684343,8532035,11083800,13501120,15731968] .nil .nil) (.node [113184,430348,506668,902208,3227782,5521457,7685367,8532035,11083800,13501056,15731968] .nil .nil)) (.node [113184,430348,506668,902208,3227782,5521521,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,506668,902208,3227782,5521457,8208631,8532035,11083800,13501056,15731968] .nil .nil) .nil)) (.node [113184,430348,506668,902208,3227782,5521523,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,506668,902208,3227782,5521521,7684279,8532035,11083864,13501056,15731968] (.node [113184,430348,506668,902208,3227782,5521521,7684279,8532035,11083800,13501120,15731968] .nil .nil) (.node [113184,430348,506668,902208,3227782,5521521,7684343,8532035,11083800,13501056,15731968] .nil .nil)) (.node [113184,430348,506668,902208,3227782,5522481,7684279,8533059,11083800,13501056,15731968] (.node [113184,430348,506668,902208,3227782,5522481,7684279,8532035,11084824,13501056,15731968] .nil .nil) .nil)))
theorem T10abbb_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10abbb = true := by decide +kernel
def T10abb : Tree := .node [113184,430348,506668,902208,3227782,5521457,7684343,8532035,11083800,13501056,15732032] T10abba T10abbb
theorem T10abb_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10abb = true :=
  tall_node _ _ _ _ T10abba_ok (by decide +kernel) T10abbb_ok
def T10ab : Tree := .node [113184,114272,430348,3227782,5521457,7684279,8532035,11083800,13501056,15732032] T10aba T10abb
theorem T10ab_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10ab = true :=
  tall_node _ _ _ _ T10aba_ok (by decide +kernel) T10abb_ok
def T10a : Tree := .node [1088,113184,506668,3227782,5689661,7684279,8532035,11083800,13501056,15731968] T10aa T10ab
theorem T10a_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10a = true :=
  tall_node _ _ _ _ T10aa_ok (by decide +kernel) T10ab_ok
def T10baaa : Tree := (.node [113184,430348,506668,917088,3227782,5521457,7684279,8532035,11083800,13501056,15732032] (.node [113184,430348,506668,902208,3227846,5521521,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,506668,902208,3227782,6045809,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,506668,902208,3227782,5554289,7684279,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,506668,902208,3227782,7684279,8532083,11083800,13501056,15731968] .nil .nil)) (.node [113184,430348,506668,902211,3227782,5521457,8532035,11083800,13501056,15731968,16076215] (.node [113184,430348,506668,902211,3227782,5521457,7684279,11083800,13501056,15731968,15875395] .nil .nil) (.node [113184,430348,506668,904512,3227782,5521457,7684279,8532035,11083800,13501056,15875395] .nil .nil))) (.node [113184,430348,506668,3227782,4048070,5521457,7684279,8533059,11083800,13501056,15731968] (.node [113184,430348,506668,1048428,3227782,5521457,7684279,8532035,11083800,13501056,15732032] (.node [113184,430348,506668,917088,3227782,5521457,7684343,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,506668,1048428,3227782,5521457,7684343,8532035,11083800,13501056,15731968] .nil .nil)) (.node [113184,430348,506671,902208,3227782,5521457,7684279,11083800,13501056,15731968,15875395] (.node [113184,430348,506668,3227782,5521457,7684279,8242423,8533059,11083800,13501056,15731968] .nil .nil) .nil)))
theorem T10baaa_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10baaa = true := by decide +kernel
def T10baab : Tree := (.node [113184,430348,507692,902208,3227782,5521457,7685303,8532035,11083800,13501056,15731968] (.node [113184,430348,507692,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,506732,902208,3227782,5521457,7684343,8532035,11083800,13501056,15731968] (.node [113184,430348,506732,902208,3227782,5521457,7684279,8532035,11083800,13501056,15732032] .nil .nil) (.node [113184,430348,506732,902208,3227782,5521521,7684279,8532035,11083800,13501056,15731968] .nil .nil)) (.node [113184,430348,507692,902208,3227782,5521457,7684279,8533059,11083800,13501056,15731968] (.node [113184,430348,507692,902208,3227782,5521457,7684279,8532035,11083800,13502080,15731968] .nil .nil) .nil)) (.node [113184,430348,507756,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,507692,3227782,4048070,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,507692,902208,3227782,5522481,7684279,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,507692,3227782,5521457,7684279,8242423,8532035,11083800,13501056,15731968] .nil .nil)) (.node [113184,430348,902208,917088,5521457,7684279,8532167,11083800,13501056,15731968] (.node [113184,430348,902208,917088,3227782,7684279,8532083,11083800,13501056,15731968] .nil .nil) .nil)))
theorem T10baab_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10baab = true := by decide +kernel
def T10baa : Tree := .node [113184,430348,506671,902208,3227782,5521457,8532035,11083800,13501056,15731968,16076215] T10baaa T10baab
theorem T10baa_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10baa = true :=
  tall_node _ _ _ _ T10baaa_ok (by decide +kernel) T10baab_ok
def T10babaa : Tree := (.node [113184,430348,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731976,15814022] (.node [113184,430348,902208,3227782,5521457,8242423,8532035,11083800,13501056,15731980] (.node [113184,430348,902208,3227782,5521457,7686583,8532035,8895343,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731968,15814030] .nil .nil)) (.node [113184,430348,902208,3227782,5521457,8532035,8632947,11083800,13501056,15731968,15814022] (.node [113184,430348,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731976,15814030] .nil .nil) .nil))
theorem T10babaa_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10babaa = true := by decide +kernel
def T10babab : Tree := (.node [113184,430348,902208,3227782,5521969,8532035,8827215,11083800,13501056,15731968,16010545] (.node [113184,430348,902208,3227782,5521465,8532035,8632931,11083800,13501056,15731968,15814022] (.node [113184,430348,902208,3227782,5521457,8532051,8632947,11083800,13501056,15731968,15814022] .nil .nil) (.node [113184,430348,902208,3227782,5521523,7684279,11083867,13501056,15731968] .nil .nil)) (.node [113184,430348,902208,3227782,5523761,7684279,8532035,8895343,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5521969,8532035,8827215,11083800,13501056,15731968,16011057] .nil .nil) .nil))
theorem T10babab_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10babab = true := by decide +kernel
def T10baba : Tree := .node [113184,430348,902208,3227782,5521457,8532051,8632931,11083800,13501056,15731968,15814022] T10babaa T10babab
theorem T10baba_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10baba = true :=
  tall_node _ _ _ _ T10babaa_ok (by decide +kernel) T10babab_ok
def T10babbaa : Tree := (.node [113184,430348,902208,3275430,5689661,8532035,11083800,13501056,15875395,16076215] (.node [113184,430348,902208,3275430,5689661,7684343,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,902211,3227782,5521457,7684279,11083800,13501056,15732035] .nil .nil))
theorem T10babbaa_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10babbaa = true := by decide +kernel
def T10babbab : Tree := (.node [113184,430348,917088,3275430,5521457,7684279,8532035,11083800,13501056,15732032] (.node [113184,430348,904512,3227782,5521457,7684279,8532035,8895343,11083800,13501056,15731968] .nil .nil) .nil)
theorem T10babbab_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10babbab = true := by decide +kernel
def T10babba : Tree := .node [113184,430348,902211,3227782,5521457,11083800,13501056,15875395,16076215] T10babbaa T10babbab
theorem T10babba_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10babba = true :=
  tall_node _ _ _ _ T10babbaa_ok (by decide +kernel) T10babbab_ok
def T10babbba : Tree := (.node [113184,430348,3227782,5522545,7684279,8532035,11084888,13501056,15731968] (.node [113184,430348,3227782,5521457,7685367,8533059,11083800,13501056,15731968] .nil .nil) (.node [113184,430351,506668,902208,3227782,5521457,8532035,11083800,13501056,15731968,16076215] .nil .nil))
theorem T10babbba_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10babbba = true := by decide +kernel
def T10babbbb : Tree := (.node [113184,430351,902208,3227782,5521457,11083800,13501056,15875395,16076215] (.node [113184,430351,506671,902208,3227782,5521457,8532035,11083800,13501056,15731968,16076215] .nil .nil) .nil)
theorem T10babbbb_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10babbbb = true := by decide +kernel
def T10babbb : Tree := .node [113184,430351,506671,902208,3227782,5521457,7684279,11083800,13501056,15731968,15875395] T10babbba T10babbbb
theorem T10babbb_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10babbb = true :=
  tall_node _ _ _ _ T10babbba_ok (by decide +kernel) T10babbbb_ok
def T10babb : Tree := .node [113184,430348,917088,3275430,5521457,7684343,8532035,11083800,13501056,15731968] T10babba T10babbb
theorem T10babb_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10babb = true :=
  tall_node _ _ _ _ T10babba_ok (by decide +kernel) T10babbb_ok
def T10bab : Tree := .node [113184,430348,902208,3275430,5689661,7684279,8532035,11083800,13501056,15732032] T10baba T10babb
theorem T10bab_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10bab = true :=
  tall_node _ _ _ _ T10baba_ok (by decide +kernel) T10babb_ok
def T10ba : Tree := .node [113184,430348,902208,1031980,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T10baa T10bab
theorem T10ba_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10ba = true :=
  tall_node _ _ _ _ T10baa_ok (by decide +kernel) T10bab_ok
def T10bbaaa : Tree := (.node [113184,430412,506668,902208,3227782,5521521,7684279,8532035,11083800,13501056,15731968] (.node [113184,430412,506668,902208,3227782,5521457,7684279,8532035,11083864,13501056,15731968] (.node [113184,430412,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15732032] .nil .nil) (.node [113184,430412,506668,902208,3227782,5521457,7684343,8532035,11083800,13501056,15731968] .nil .nil)) (.node [113184,430412,506732,902208,3227782,5521457,7684279,8532035,11083800,13501056,15732032] (.node [113184,430412,506668,902208,3227846,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) .nil))
theorem T10bbaaa_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10bbaaa = true := by decide +kernel
def T10bbaab : Tree := (.node [113184,430415,902208,3227782,5521457,7684279,11083800,13501056,15732035] (.node [113184,430412,506732,902208,3227782,5521521,7684279,8532035,11083800,13501056,15731968] (.node [113184,430412,506732,902208,3227782,5521457,7684343,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,430412,506732,902208,3227846,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)) (.node [113184,430476,902208,3227782,5521457,8532035,8827215,11083800,13501056,15731968,16010545] (.node [113184,430415,902208,3227782,5521457,7684279,11083867,13501056,15731968] .nil .nil) .nil))
theorem T10bbaab_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10bbaab = true := by decide +kernel
def T10bbaa : Tree := .node [113184,430412,506732,902208,3227782,5521457,7684279,8532035,11083864,13501056,15731968] T10bbaaa T10bbaab
theorem T10bbaa_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10bbaa = true :=
  tall_node _ _ _ _ T10bbaaa_ok (by decide +kernel) T10bbaab_ok
def T10bbab : Tree := (.node [113184,431372,506668,902208,3228806,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,431372,506668,902208,3227782,5521457,7684279,8533059,11083800,13501056,15731968] (.node [113184,431372,506668,902208,3227782,5521457,7684279,8532035,11083800,13502080,15731968] (.node [113184,431372,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,431372,506668,902208,3227782,5521457,7684279,8532035,11084824,13501056,15731968] .nil .nil)) (.node [113184,431372,506668,902208,3227782,5522481,7684279,8532035,11083800,13501056,15731968] (.node [113184,431372,506668,902208,3227782,5521457,7685303,8532035,11083800,13501056,15731968] .nil .nil) .nil)) (.node [113184,431372,507692,902208,3227782,5521457,7684279,8533059,11083800,13501056,15731968] (.node [113184,431372,507692,902208,3227782,5521457,7684279,8532035,11083800,13502080,15731968] (.node [113184,431372,507692,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,431372,507692,902208,3227782,5521457,7684279,8532035,11084824,13501056,15731968] .nil .nil)) (.node [113184,431372,507692,902208,3227782,5522481,7684279,8532035,11083800,13501056,15731968] (.node [113184,431372,507692,902208,3227782,5521457,7685303,8532035,11083800,13501056,15731968] .nil .nil) .nil)))
theorem T10bbab_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10bbab = true := by decide +kernel
def T10bba : Tree := .node [113184,430476,902208,3227782,5521457,8532035,8827343,11083800,13501056,15731968,16010545] T10bbaa T10bbab
theorem T10bba_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10bba = true :=
  tall_node _ _ _ _ T10bbaa_ok (by decide +kernel) T10bbab_ok
def T10bbbaa : Tree := (.node [113184,431372,3227782,5521457,7684343,8532035,11083800,13501056,15731968] (.node [113184,431372,507692,3227782,5521457,6145137,7684279,8532035,11083800,13501056,15731968] (.node [113184,431372,507692,3227782,4048070,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,431372,507692,3227782,5521457,7684279,8242423,8532035,11083800,13501056,15731968] .nil .nil)) (.node [113184,431436,507756,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,431436,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) .nil))
theorem T10bbbaa_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10bbbaa = true := by decide +kernel
def T10bbbab : Tree := (.node [113184,433420,507692,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,431436,3227782,5521457,7685367,8532035,11083800,13501056,15731968] (.node [113184,431436,3227782,5521457,7684279,8532035,11084888,13501056,15731968] .nil .nil) (.node [113184,433420,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)) (.node [113184,506668,902208,955660,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,447756,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) .nil))
theorem T10bbbab_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10bbbab = true := by decide +kernel
def T10bbba : Tree := .node [113184,431436,3227782,5521457,7684279,8532035,11083800,13501056,15732032] T10bbbaa T10bbbab
theorem T10bbba_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10bbba = true :=
  tall_node _ _ _ _ T10bbbaa_ok (by decide +kernel) T10bbbab_ok
def T10bbbba : Tree := (.node [113184,506668,1048428,3227782,5689661,7684279,8242423,8532035,11083800,13501056,15731968] (.node [113184,506668,1037644,3227782,5689661,7684279,8242423,8532035,11083800,13501056,15731968] (.node [113184,506668,1037644,3227782,5689661,6145137,7684279,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,506668,1048428,3227782,5689661,6145137,7684279,8532035,11083800,13501056,15731968] .nil .nil)) (.node [113184,902208,3227782,4624780,5521457,8532035,8827215,11083800,13501056,15731968,16010545] (.node [113184,902208,1037644,3227782,5521457,7684279,8532035,11083800,13501056,15731980] .nil .nil) .nil))
theorem T10bbbba_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10bbbba = true := by decide +kernel
def T10bbbbb : Tree := (.node [506668,902208,1048428,3275430,5689661,7684279,8532035,11083800,13501056,15731968] (.node [114208,431372,507692,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [114208,431372,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) (.node [327716,506668,902208,3275430,5689661,7684279,8532035,11083800,13501056,15731968] .nil .nil)) (.node [506668,902208,3275430,5689661,7684279,8532035,11083800,13501056,15731968,15875395] (.node [506668,902208,3275430,5689661,7684279,8242423,8532035,11083800,13501056,15731968] .nil .nil) .nil))
theorem T10bbbbb_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10bbbbb = true := by decide +kernel
def T10bbbb : Tree := .node [113184,902208,3275430,5689661,7684279,8827215,11083800,13501056,15731968,15875395] T10bbbba T10bbbbb
theorem T10bbbb_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10bbbb = true :=
  tall_node _ _ _ _ T10bbbba_ok (by decide +kernel) T10bbbbb_ok
def T10bbb : Tree := .node [113184,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731980] T10bbba T10bbbb
theorem T10bbb_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10bbb = true :=
  tall_node _ _ _ _ T10bbba_ok (by decide +kernel) T10bbbb_ok
def T10bb : Tree := .node [113184,431372,507692,902208,3228806,5521457,7684279,8532035,11083800,13501056,15731968] T10bba T10bbb
theorem T10bb_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10bb = true :=
  tall_node _ _ _ _ T10bba_ok (by decide +kernel) T10bbb_ok
def T10b : Tree := .node [113184,430364,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731968,15814022] T10ba T10bb
theorem T10b_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10b = true :=
  tall_node _ _ _ _ T10ba_ok (by decide +kernel) T10bb_ok
def T10 : Tree := .node [113184,430348,506668,902208,3227782,5522545,7684279,8532035,11083800,13501056,15731968] T10a T10b
theorem T10_ok : tall (expFast false (RP PR T9 BinaryTree.nil 9) T9 9) T10 = true :=
  tall_node _ _ _ _ T10a_ok (by decide +kernel) T10b_ok
def R10 : Tree := (.node [113184,430348,3227782,5521457,8242423,8533059,11083800,13501056,15731968] (.node [67,113184,430348,902208,3227782,5521457,11083800,13501056,15731968] (.node [24,506668,902208,3275430,5689661,7684279,8532035,13501056,15731968] .nil .nil) (.node [67,113184,430348,1048428,3227782,5521457,11083800,13501056,15731968] .nil .nil)) (.node [113184,431372,3227782,5521457,8242423,8532035,11083800,13501056,15731968] (.node [113184,430348,3227782,5522545,7684279,8533059,11083800,13501056,15731968] .nil .nil) (.node [113184,902208,3227782,5689661,8827215,11083800,13501056,15875395,16076215] .nil .nil)))
theorem R10_ok : tall (refOK cpF 10) R10 = true := by decide +kernel
def T11aaaaaaa : Tree := (.node [3,1088,113184,430348,3227782,5521457,7684279,11083800,13501056,15731968] (.node [3,64,113184,430348,506668,902208,3227782,5521457,7684279,11083800,13501056,15731968] .nil .nil) (.node [3,113184,430348,506668,902208,3227782,5521457,7684279,11083800,13501056,15731968,15875395] .nil .nil))
theorem T11aaaaaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaaaaaa = true := by decide +kernel
def T11aaaaaab : Tree := (.node [3,113184,430348,902208,3227782,5521457,11083800,13501056,15875395,16076215] (.node [3,113184,430348,902208,3227782,5521457,7684279,11083800,13501056,15732032] .nil .nil) (.node [8,113184,430348,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731968,15814022] .nil .nil))
theorem T11aaaaaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaaaaab = true := by decide +kernel
def T11aaaaaa : Tree := .node [3,113184,430348,506668,902208,3227782,5521457,8532035,11083800,13501056,15731968,16076215] T11aaaaaaa T11aaaaaab
theorem T11aaaaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaaaaa = true :=
  tall_node _ _ _ _ T11aaaaaaa_ok (by decide +kernel) T11aaaaaab_ok
def T11aaaaaba : Tree := (.node [12,113184,902208,1037644,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [12,113184,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) (.node [16,113184,430348,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731968,15814022] .nil .nil))
theorem T11aaaaaba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaaaaba = true := by decide +kernel
def T11aaaaabb : Tree := (.node [24,113184,430348,902208,3227782,3275430,5521457,8532035,13501056,15731968] (.node [24,113184,430348,902208,1037644,3227782,5521457,7684279,8532035,13501056,15731968] .nil .nil) .nil)
theorem T11aaaaabb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaaaabb = true := by decide +kernel
def T11aaaaab : Tree := .node [24,113184,430348,506668,902208,3227782,5521457,7684279,8532035,13501056,15731968] T11aaaaaba T11aaaaabb
theorem T11aaaaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaaaab = true :=
  tall_node _ _ _ _ T11aaaaaba_ok (by decide +kernel) T11aaaaabb_ok
def T11aaaaa : Tree := .node [12,113184,430348,902208,3227782,5521457,8242423,8532035,11083800,13501056,15731968] T11aaaaaa T11aaaaab
theorem T11aaaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaaaa = true :=
  tall_node _ _ _ _ T11aaaaaa_ok (by decide +kernel) T11aaaaab_ok
def T11aaaabaaa : Tree := (.node [24,113184,430348,902208,3227782,5521457,8532035,13501056,15731968,15814022] .nil .nil)
theorem T11aaaabaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaaabaaa = true := by decide +kernel
def T11aaaabaab : Tree := (.node [48,113184,430348,506668,902208,3227782,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T11aaaabaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaaabaab = true := by decide +kernel
def T11aaaabaa : Tree := .node [24,113184,430348,902208,3227782,5521457,8532035,13501056,15731968,15875395] T11aaaabaaa T11aaaabaab
theorem T11aaaabaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaaabaa = true :=
  tall_node _ _ _ _ T11aaaabaaa_ok (by decide +kernel) T11aaaabaab_ok
def T11aaaabab : Tree := (.node [49,113184,430348,902208,3227782,8532035,8632931,11083800,13501056,15731968] (.node [48,113184,430348,902208,1037644,3227782,7684279,8532035,11083800,13501056,15731968] .nil .nil) .nil)
theorem T11aaaabab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaaabab = true := by decide +kernel
def T11aaaaba : Tree := .node [48,113184,430348,902208,917088,3227782,7684279,8532035,11083800,13501056,15731968] T11aaaabaa T11aaaabab
theorem T11aaaaba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaaaba = true :=
  tall_node _ _ _ _ T11aaaabaa_ok (by decide +kernel) T11aaaabab_ok
def T11aaaabb : Tree := (.node [64,113184,430348,506668,902208,3227782,5521457,7684343,8532035,11083800,13501056,15731968] (.node [64,113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15732032] (.node [64,113184,114208,430348,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) (.node [64,113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501120,15731968] .nil .nil)) (.node [64,113184,430348,506668,917088,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [64,113184,430348,506668,902208,3227782,5521521,7684279,8532035,11083800,13501056,15731968] .nil .nil) .nil))
theorem T11aaaabb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaaabb = true := by decide +kernel
def T11aaaab : Tree := .node [64,1024,113184,430348,506668,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T11aaaaba T11aaaabb
theorem T11aaaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaaab = true :=
  tall_node _ _ _ _ T11aaaaba_ok (by decide +kernel) T11aaaabb_ok
def T11aaaa : Tree := .node [24,113184,430348,902208,3227782,5521457,8532035,8632931,13501056,15731968] T11aaaaa T11aaaab
theorem T11aaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaaa = true :=
  tall_node _ _ _ _ T11aaaaa_ok (by decide +kernel) T11aaaab_ok
def T11aaabaaa : Tree := (.node [64,113184,430348,902208,3275430,5689661,7684279,8532035,11083800,13501056,15731968] (.node [64,113184,430348,506732,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) (.node [64,113184,430348,917088,3275430,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil))
theorem T11aaabaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaabaaa = true := by decide +kernel
def T11aaabaab : Tree := (.node [64,113184,431372,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [64,113184,430412,506732,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) (.node [65,113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil))
theorem T11aaabaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaabaab = true := by decide +kernel
def T11aaabaa : Tree := .node [64,113184,430412,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T11aaabaaa T11aaabaab
theorem T11aaabaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaabaa = true :=
  tall_node _ _ _ _ T11aaabaaa_ok (by decide +kernel) T11aaabaab_ok
def T11aaababa : Tree := (.node [67,113184,430348,506668,902208,3227782,5521457,7684279,8242423,11083800,13501056,15731968] (.node [67,113184,113251,430348,902208,3227782,5521457,7684279,11083800,13501056,15731968] .nil .nil) (.node [67,113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil))
theorem T11aaababa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaababa = true := by decide +kernel
def T11aaababb : Tree := (.node [67,113184,430348,902208,3227782,5521457,7684279,11083800,13501056,15731968] (.node [67,113184,430348,506668,902208,3227782,5521457,11083800,13501056,15731968] .nil .nil) .nil)
theorem T11aaababb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaababb = true := by decide +kernel
def T11aaabab : Tree := .node [67,113184,430348,506668,902208,3227782,5521457,7684279,11083800,13501056,15731968] T11aaababa T11aaababb
theorem T11aaabab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaabab = true :=
  tall_node _ _ _ _ T11aaababa_ok (by decide +kernel) T11aaababb_ok
def T11aaaba : Tree := .node [67,1024,113184,430348,3227782,5521457,7684279,11083800,13501056,15731968] T11aaabaa T11aaabab
theorem T11aaaba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaaba = true :=
  tall_node _ _ _ _ T11aaabaa_ok (by decide +kernel) T11aaabab_ok
def T11aaabbaaa : Tree := (.node [67,113184,430348,902208,3227782,5521457,7684279,11083800,13501123,15731968] .nil .nil)
theorem T11aaabbaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaabbaaa = true := by decide +kernel
def T11aaabbaab : Tree := (.node [67,113184,430348,902208,3227782,5521457,11083800,12148894,13501056,15731968] .nil .nil)
theorem T11aaabbaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaabbaab = true := by decide +kernel
def T11aaabbaa : Tree := .node [67,113184,430348,902208,3227782,5521457,7684343,11083800,13501056,15731968] T11aaabbaaa T11aaabbaab
theorem T11aaabbaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaabbaa = true :=
  tall_node _ _ _ _ T11aaabbaaa_ok (by decide +kernel) T11aaabbaab_ok
def T11aaabbab : Tree := (.node [67,113184,430348,902208,3227782,5521457,11083800,13501056,15731968,16076215] (.node [67,113184,430348,902208,3227782,5521457,11083800,13501056,15731968,15814022] .nil .nil) .nil)
theorem T11aaabbab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaabbab = true := by decide +kernel
def T11aaabba : Tree := .node [67,113184,430348,902208,3227782,5521457,11083800,13501056,15671960,15731968] T11aaabbaa T11aaabbab
theorem T11aaabba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaabba = true :=
  tall_node _ _ _ _ T11aaabbaa_ok (by decide +kernel) T11aaabbab_ok
def T11aaabbbaa : Tree := (.node [67,113184,430348,902208,3227782,5521457,11083800,13501056,15731968,16605375] .nil .nil)
theorem T11aaabbbaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaabbbaa = true := by decide +kernel
def T11aaabbbab : Tree := (.node [67,113184,430348,902208,3227782,5689661,7684279,11083800,13501056,15731968] .nil .nil)
theorem T11aaabbbab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaabbbab = true := by decide +kernel
def T11aaabbba : Tree := .node [67,113184,430348,902208,3227782,5521523,7684279,11083800,13501056,15731968] T11aaabbbaa T11aaabbbab
theorem T11aaabbba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaabbba = true :=
  tall_node _ _ _ _ T11aaabbbaa_ok (by decide +kernel) T11aaabbbab_ok
def T11aaabbbb : Tree := (.node [67,113184,430348,917088,3227782,5521457,7684279,11083800,13501056,15731968] (.node [67,113184,430348,902211,3227782,5521457,7684279,11083800,13501056,15731968] .nil .nil) .nil)
theorem T11aaabbbb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaabbbb = true := by decide +kernel
def T11aaabbb : Tree := .node [67,113184,430348,902208,3227782,7684279,11083800,13501056,14566065,15731968] T11aaabbba T11aaabbbb
theorem T11aaabbb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaabbb = true :=
  tall_node _ _ _ _ T11aaabbba_ok (by decide +kernel) T11aaabbbb_ok
def T11aaabb : Tree := .node [67,113184,430348,902208,3227782,5521457,11083800,13501056,15731968,16330008] T11aaabba T11aaabbb
theorem T11aaabb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaabb = true :=
  tall_node _ _ _ _ T11aaabba_ok (by decide +kernel) T11aaabbb_ok
def T11aaab : Tree := .node [67,113184,430348,902208,3227782,5521457,7684279,11083800,13501056,15732035] T11aaaba T11aaabb
theorem T11aaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaab = true :=
  tall_node _ _ _ _ T11aaaba_ok (by decide +kernel) T11aaabb_ok
def T11aaa : Tree := .node [64,113184,430348,506668,1048428,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T11aaaa T11aaab
theorem T11aaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaa = true :=
  tall_node _ _ _ _ T11aaaa_ok (by decide +kernel) T11aaab_ok
def T11aabaaaaa : Tree := (.node [67,113184,430415,902208,3227782,5521457,7684279,11083800,13501056,15731968] .nil .nil)
theorem T11aabaaaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aabaaaaa = true := by decide +kernel
def T11aabaaaab : Tree := (.node [268,113184,902208,3227782,5521457,8532035,11083800,13501056,15731968,15814022] .nil .nil)
theorem T11aabaaaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aabaaaab = true := by decide +kernel
def T11aabaaaa : Tree := .node [268,113184,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T11aabaaaaa T11aabaaaab
theorem T11aabaaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aabaaaa = true :=
  tall_node _ _ _ _ T11aabaaaaa_ok (by decide +kernel) T11aabaaaab_ok
def T11aabaaab : Tree := (.node [1024,113184,430348,506668,902208,3227782,5521457,7684279,8533059,11083800,13501056,15731968] (.node [1024,113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13502080,15731968] .nil .nil) (.node [1024,113184,430348,506668,902208,3227782,5521457,7685303,8532035,11083800,13501056,15731968] .nil .nil))
theorem T11aabaaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aabaaab = true := by decide +kernel
def T11aabaaa : Tree := .node [1024,2304,113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056] T11aabaaaa T11aabaaab
theorem T11aabaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aabaaa = true :=
  tall_node _ _ _ _ T11aabaaaa_ok (by decide +kernel) T11aabaaab_ok
def T11aabaab : Tree := (.node [1024,113184,430348,3227782,5521457,7684343,8532035,11083800,13501056,15731968] (.node [1024,113184,430348,506668,3227782,5521457,7684279,8242423,8532035,11083800,13501056,15731968] (.node [1024,113184,430348,506668,3227782,4048070,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) (.node [1024,113184,430348,507692,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)) (.node [1024,113184,431372,507692,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [1024,113184,431372,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) .nil))
theorem T11aabaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aabaab = true := by decide +kernel
def T11aabaa : Tree := .node [1024,113184,430348,506668,902208,3227782,5522481,7684279,8532035,11083800,13501056,15731968] T11aabaaa T11aabaab
theorem T11aabaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aabaa = true :=
  tall_node _ _ _ _ T11aabaaa_ok (by decide +kernel) T11aabaab_ok
def T11aababaa : Tree := (.node [1088,113184,430348,506668,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [1088,113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) (.node [1088,113184,430348,506668,3227782,5521457,7684279,8532035,11083800,13501056,15731968,15875395] .nil .nil))
theorem T11aababaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aababaa = true := by decide +kernel
def T11aababab : Tree := (.node [1088,113184,430348,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [1088,113184,430348,3227782,3275430,5521457,8532035,11083800,13501056,15731968] .nil .nil) .nil)
theorem T11aababab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aababab = true := by decide +kernel
def T11aababa : Tree := .node [1088,113184,430348,506668,3227782,5521457,8532035,11083800,13501056,15731968] T11aababaa T11aababab
theorem T11aababa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aababa = true :=
  tall_node _ _ _ _ T11aababaa_ok (by decide +kernel) T11aababab_ok
def T11aababbaa : Tree := (.node [1088,113184,430348,3227782,5521457,7684279,8532035,11083800,13502144,15731968] .nil .nil)
theorem T11aababbaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aababbaa = true := by decide +kernel
def T11aababbab : Tree := (.node [1088,113184,430348,3227782,5521457,7685367,8532035,11083800,13501056,15731968] .nil .nil)
theorem T11aababbab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aababbab = true := by decide +kernel
def T11aababba : Tree := .node [1088,113184,430348,3227782,5521457,7684279,8533059,11083800,13501056,15731968] T11aababbaa T11aababbab
theorem T11aababba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aababba = true :=
  tall_node _ _ _ _ T11aababbaa_ok (by decide +kernel) T11aababbab_ok
def T11aababbb : Tree := (.node [1088,113184,431436,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [1088,113184,430348,3227782,5689661,7684279,8532035,11083800,13501056,15731968] .nil .nil) .nil)
theorem T11aababbb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aababbb = true := by decide +kernel
def T11aababb : Tree := .node [1088,113184,430348,3227782,5522545,7684279,8532035,11083800,13501056,15731968] T11aababba T11aababbb
theorem T11aababb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aababb = true :=
  tall_node _ _ _ _ T11aababba_ok (by decide +kernel) T11aababbb_ok
def T11aabab : Tree := .node [1088,113184,430348,3227782,5521457,7684279,8532035,11083800,13501056,15732032] T11aababa T11aababb
theorem T11aabab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aabab = true :=
  tall_node _ _ _ _ T11aababa_ok (by decide +kernel) T11aababb_ok
def T11aaba : Tree := .node [1088,113184,114272,430348,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T11aabaa T11aabab
theorem T11aaba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aaba = true :=
  tall_node _ _ _ _ T11aabaa_ok (by decide +kernel) T11aabab_ok
def T11aabbaaa : Tree := (.node [2304,113184,430348,902208,3227782,5521457,7684279,8532035,8895343,11083800,13501056,15731968] (.node [2304,113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15875395] .nil .nil) (.node [3328,113184,430348,506668,902208,1048428,3227782,5521457,7684279,8532035,11083800,13501056] .nil .nil))
theorem T11aabbaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aabbaaa = true := by decide +kernel
def T11aabbaab : Tree := (.node [3328,113184,430348,506668,902208,3227782,5521457,8532035,11083800,13501056] (.node [3328,113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) .nil)
theorem T11aabbaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aabbaab = true := by decide +kernel
def T11aabbaa : Tree := .node [3328,113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056] T11aabbaaa T11aabbaab
theorem T11aabbaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aabbaa = true :=
  tall_node _ _ _ _ T11aabbaaa_ok (by decide +kernel) T11aabbaab_ok
def T11aabbaba : Tree := (.node [66080,113184,430348,902208,3227782,5521457,8242423,8532035,11083800,13501056,15731968] (.node [65668,113184,430348,506668,902208,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) (.node [66080,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil))
theorem T11aabbaba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aabbaba = true := by decide +kernel
def T11aabbabb : Tree := (.node [81984,113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [73752,113184,430348,506668,902208,3227782,5521457,7684279,8532035,13501056,15731968] .nil .nil) .nil)
theorem T11aabbabb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aabbabb = true := by decide +kernel
def T11aabbab : Tree := .node [67616,113184,430348,902208,3227782,5521457,8532035,8827215,11083800,13501056,15731968,16076215] T11aabbaba T11aabbabb
theorem T11aabbab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aabbab = true :=
  tall_node _ _ _ _ T11aabbaba_ok (by decide +kernel) T11aabbabb_ok
def T11aabba : Tree := .node [3328,113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056] T11aabbaa T11aabbab
theorem T11aabba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aabba = true :=
  tall_node _ _ _ _ T11aabbaa_ok (by decide +kernel) T11aabbab_ok
def T11aabbbaa : Tree := (.node [99328,113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [98368,113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,113187,430348,902208,3227782,5521457,7684279,11083800,13501056,15731968,15875395] .nil .nil))
theorem T11aabbbaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aabbbaa = true := by decide +kernel
def T11aabbbab : Tree := (.node [113184,113188,430348,902208,1037644,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,113187,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16076215] .nil .nil) .nil)
theorem T11aabbbab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aabbbab = true := by decide +kernel
def T11aabbba : Tree := .node [113184,113187,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,15814022] T11aabbbaa T11aabbbab
theorem T11aabbba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aabbba = true :=
  tall_node _ _ _ _ T11aabbbaa_ok (by decide +kernel) T11aabbbab_ok
def T11aabbbba : Tree := (.node [113184,113248,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15732032] (.node [113184,113200,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,15814022] .nil .nil) (.node [113184,113248,430348,902208,3227782,5521457,7684279,8532035,11083800,13501120,15731968] .nil .nil))
theorem T11aabbbba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aabbbba = true := by decide +kernel
def T11aabbbbb : Tree := (.node [113184,113248,430348,902208,3227846,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,113248,430348,902208,3227782,5521521,7684279,8532035,11083800,13501056,15731968] .nil .nil) .nil)
theorem T11aabbbbb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aabbbbb = true := by decide +kernel
def T11aabbbb : Tree := .node [113184,113248,430348,902208,3227782,5521457,7684343,8532035,11083800,13501056,15731968] T11aabbbba T11aabbbbb
theorem T11aabbbb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aabbbb = true :=
  tall_node _ _ _ _ T11aabbbba_ok (by decide +kernel) T11aabbbbb_ok
def T11aabbb : Tree := .node [113184,113200,430348,902208,1037644,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T11aabbba T11aabbbb
theorem T11aabbb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aabbb = true :=
  tall_node _ _ _ _ T11aabbba_ok (by decide +kernel) T11aabbbb_ok
def T11aabb : Tree := .node [82944,113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T11aabba T11aabbb
theorem T11aabb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aabb = true :=
  tall_node _ _ _ _ T11aabba_ok (by decide +kernel) T11aabbb_ok
def T11aab : Tree := .node [1280,113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T11aaba T11aabb
theorem T11aab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aab = true :=
  tall_node _ _ _ _ T11aaba_ok (by decide +kernel) T11aabb_ok
def T11aa : Tree := .node [67,113184,430348,917088,3227782,5521457,11083800,13501056,15731968] T11aaa T11aab
theorem T11aa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aa = true :=
  tall_node _ _ _ _ T11aaa_ok (by decide +kernel) T11aab_ok
def T11abaaaaa : Tree := (.node [113184,114208,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,114208,430348,431372,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,114208,430348,507692,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil))
theorem T11abaaaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abaaaaa = true := by decide +kernel
def T11abaaaab : Tree := (.node [113184,114208,430348,902208,3227782,5521457,7684279,8532035,11084824,13501056,15731968] (.node [113184,114208,430348,902208,3227782,5521457,7684279,8532035,11083800,13502080,15731968] .nil .nil) (.node [113184,114208,430348,902208,3227782,5521457,7684279,8533059,11083800,13501056,15731968] .nil .nil))
theorem T11abaaaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abaaaab = true := by decide +kernel
def T11abaaaa : Tree := .node [113184,114208,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T11abaaaaa T11abaaaab
theorem T11abaaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abaaaa = true :=
  tall_node _ _ _ _ T11abaaaaa_ok (by decide +kernel) T11abaaaab_ok
def T11abaaaba : Tree := (.node [113184,114208,430348,902208,3228806,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,114208,430348,902208,3227782,5522481,7684279,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,114208,430348,3227782,4048070,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil))
theorem T11abaaaba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abaaaba = true := by decide +kernel
def T11abaaabb : Tree := (.node [113184,114208,431372,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,114208,430348,3227782,5521457,7684279,8242423,8532035,11083800,13501056,15731968] .nil .nil) .nil)
theorem T11abaaabb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abaaabb = true := by decide +kernel
def T11abaaab : Tree := .node [113184,114208,430348,3227782,5521457,6145137,7684279,8532035,11083800,13501056,15731968] T11abaaaba T11abaaabb
theorem T11abaaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abaaab = true :=
  tall_node _ _ _ _ T11abaaaba_ok (by decide +kernel) T11abaaabb_ok
def T11abaaa : Tree := .node [113184,114208,430348,902208,3227782,5521457,7685303,8532035,11083800,13501056,15731968] T11abaaaa T11abaaab
theorem T11abaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abaaa = true :=
  tall_node _ _ _ _ T11abaaaa_ok (by decide +kernel) T11abaaab_ok
def T11abaabaa : Tree := (.node [113184,130592,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,114464,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,327716,430348,506668,902208,3227782,5521457,8242423,8532035,11083800,13501056,15731968] .nil .nil))
theorem T11abaabaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abaabaa = true := by decide +kernel
def T11abaabab : Tree := (.node [113184,327719,430348,506668,902208,3227782,5521457,8532035,11083800,13501056,15731968] (.node [113184,327716,506668,902208,3227782,5689661,7684279,8532035,11083800,13501056,15731968] .nil .nil) .nil)
theorem T11abaabab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abaabab = true := by decide +kernel
def T11abaaba : Tree := .node [113184,327716,430348,902208,1048428,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T11abaabaa T11abaabab
theorem T11abaaba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abaaba = true :=
  tall_node _ _ _ _ T11abaabaa_ok (by decide +kernel) T11abaabab_ok
def T11abaabb : Tree := (.node [113184,361472,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,345088,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,344128,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,360512,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)) (.node [113184,375588,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,375332,430348,902208,1037644,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) .nil))
theorem T11abaabb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abaabb = true := by decide +kernel
def T11abaab : Tree := .node [113184,330020,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T11abaaba T11abaabb
theorem T11abaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abaab = true :=
  tall_node _ _ _ _ T11abaaba_ok (by decide +kernel) T11abaabb_ok
def T11abaa : Tree := .node [113184,114272,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T11abaaa T11abaab
theorem T11abaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abaa = true :=
  tall_node _ _ _ _ T11abaaa_ok (by decide +kernel) T11abaab_ok
def T11ababaa : Tree := (.node [113184,430348,506668,902208,902209,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,506668,589888,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,506668,507692,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,506668,590848,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)) (.node [113184,430348,506668,902208,902212,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,506668,902208,902211,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) .nil))
theorem T11ababaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11ababaa = true := by decide +kernel
def T11ababab : Tree := (.node [113184,430348,506668,902208,904512,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,506668,902208,902244,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,506668,902208,902224,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,506668,902208,902464,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)) (.node [113184,430348,506668,902208,910400,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,506668,902208,906304,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) .nil))
theorem T11ababab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11ababab = true := by decide +kernel
def T11ababa : Tree := .node [113184,430348,506668,902208,902216,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T11ababaa T11ababab
theorem T11ababa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11ababa = true :=
  tall_node _ _ _ _ T11ababaa_ok (by decide +kernel) T11ababab_ok
def T11ababba : Tree := (.node [113184,430348,506668,902208,1950784,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,506668,902208,1045568,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,506668,902208,914496,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,506668,902208,1048428,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)) (.node [113184,430348,506668,902208,2170904,3227782,5521457,7684279,8532035,13501056,15731968] (.node [113184,430348,506668,902208,2162712,3227782,5521457,7684279,8532035,13501056,15731968] .nil .nil) .nil))
theorem T11ababba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11ababba = true := by decide +kernel
def T11ababbb : Tree := (.node [113184,430348,506668,902208,3227782,4047936,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,506668,902208,3227782,3227846,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,506668,902208,2999376,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,506668,902208,3227782,3227846,5521457,8532035,11083800,13501056,15731968] .nil .nil)) (.node [113184,430348,506668,902208,3227782,5521457,7684279,8242240,8532035,11083800,13501056,15731968] (.node [113184,430348,506668,902208,3227782,5521457,7684279,7684343,8532035,11083800,13501056,15731968] .nil .nil) .nil))
theorem T11ababbb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11ababbb = true := by decide +kernel
def T11ababb : Tree := .node [113184,430348,506668,902208,2999360,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T11ababba T11ababbb
theorem T11ababb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11ababb = true :=
  tall_node _ _ _ _ T11ababba_ok (by decide +kernel) T11ababbb_ok
def T11abab : Tree := .node [113184,430348,506668,902208,910408,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T11ababa T11ababb
theorem T11abab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abab = true :=
  tall_node _ _ _ _ T11ababa_ok (by decide +kernel) T11ababb_ok
def T11aba : Tree := .node [113184,376352,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T11abaa T11abab
theorem T11aba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11aba = true :=
  tall_node _ _ _ _ T11abaa_ok (by decide +kernel) T11abab_ok
def T11abbaaa : Tree := (.node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,9290816,11083800,13501056,15731968] (.node [113184,430348,506668,902208,3227782,5521457,7684279,8389632,8532035,11083800,13501056,15731968] (.node [113184,430348,506668,902208,3227782,5521457,7684279,8388672,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,8533059,11083800,13501056,15731968] .nil .nil)) (.node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,15732032] (.node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731969] .nil .nil)))
theorem T11abbaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abbaaa = true := by decide +kernel
def T11abbaaba : Tree := (.node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731976] (.node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731972] .nil .nil) (.node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731984] .nil .nil))
theorem T11abbaaba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abbaaba = true := by decide +kernel
def T11abbaabb : Tree := (.node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15875395,16076215] (.node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15814022,15875395] .nil .nil) .nil)
theorem T11abbaabb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abbaabb = true := by decide +kernel
def T11abbaab : Tree := .node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15732032] T11abbaaba T11abbaabb
theorem T11abbaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abbaab = true :=
  tall_node _ _ _ _ T11abbaaba_ok (by decide +kernel) T11abbaabb_ok
def T11abbaa : Tree := .node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731971] T11abbaaa T11abbaab
theorem T11abbaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abbaa = true :=
  tall_node _ _ _ _ T11abbaaa_ok (by decide +kernel) T11abbaab_ok
def T11abbabaa : Tree := (.node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501058,15731968] (.node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501057,15731968] .nil .nil) (.node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501059,15731968] .nil .nil))
theorem T11abbabaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abbabaa = true := by decide +kernel
def T11abbabab : Tree := (.node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501072,15731968] (.node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501064,15731968] .nil .nil) .nil)
theorem T11abbabab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abbabab = true := by decide +kernel
def T11abbaba : Tree := .node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501060,15731968] T11abbabaa T11abbabab
theorem T11abbaba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abbaba = true :=
  tall_node _ _ _ _ T11abbabaa_ok (by decide +kernel) T11abbabab_ok
def T11abbabba : Tree := (.node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501312,15731968] (.node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501120,15731968] .nil .nil) (.node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13502080,15731968] .nil .nil))
theorem T11abbabba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abbabba = true := by decide +kernel
def T11abbabbb : Tree := (.node [113184,430348,506668,902208,3227782,5521457,7684279,8532039,11083800,13501056,15731968] (.node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13503360,15731968] .nil .nil) .nil)
theorem T11abbabbb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abbabbb = true := by decide +kernel
def T11abbabb : Tree := .node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13503104,15731968] T11abbabba T11abbabbb
theorem T11abbabb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abbabb = true :=
  tall_node _ _ _ _ T11abbabba_ok (by decide +kernel) T11abbabbb_ok
def T11abbab : Tree := .node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501088,15731968] T11abbaba T11abbabb
theorem T11abbab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abbab = true :=
  tall_node _ _ _ _ T11abbaba_ok (by decide +kernel) T11abbabb_ok
def T11abba : Tree := .node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15875395,16633152] T11abbaa T11abbab
theorem T11abba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abba = true :=
  tall_node _ _ _ _ T11abbaa_ok (by decide +kernel) T11abbab_ok
def T11abbbaaa : Tree := (.node [113184,430348,506668,902208,3227782,5521457,7684279,8532291,11083800,13501056,15731968] (.node [113184,430348,506668,902208,3227782,5521457,7684279,8532051,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,506668,902208,3227782,5521457,7684279,8533059,11083800,13501056,15731968] .nil .nil))
theorem T11abbbaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abbbaaa = true := by decide +kernel
def T11abbbaab : Tree := (.node [113184,430348,506668,902208,3227782,5521457,7684279,8895343,11083800,13501056,15731968,15875395] (.node [113184,430348,506668,902208,3227782,5521457,7684279,8632931,11083800,13501056,15731968,15875395] .nil .nil) .nil)
theorem T11abbbaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abbbaab = true := by decide +kernel
def T11abbbaa : Tree := .node [113184,430348,506668,902208,3227782,5521457,7684279,8534339,11083800,13501056,15731968] T11abbbaaa T11abbbaab
theorem T11abbbaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abbbaa = true :=
  tall_node _ _ _ _ T11abbbaaa_ok (by decide +kernel) T11abbbaab_ok
def T11abbbaba : Tree := (.node [113184,430348,506668,902208,3227782,5521457,7684343,8532035,11083800,13501056,15731968] (.node [113184,430348,506668,902208,3227782,5521457,7684287,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,506668,902208,3227782,5521457,7684535,8532035,11083800,13501056,15731968] .nil .nil))
theorem T11abbbaba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abbbaba = true := by decide +kernel
def T11abbbabb : Tree := (.node [113184,430348,506668,902208,3227782,5521457,8208567,8532035,11083800,13501056,15731968] (.node [113184,430348,506668,902208,3227782,5521457,7686583,8532035,11083800,13501056,15731968] .nil .nil) .nil)
theorem T11abbbabb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abbbabb = true := by decide +kernel
def T11abbbab : Tree := .node [113184,430348,506668,902208,3227782,5521457,7685303,8532035,11083800,13501056,15731968] T11abbbaba T11abbbabb
theorem T11abbbab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abbbab = true :=
  tall_node _ _ _ _ T11abbbaba_ok (by decide +kernel) T11abbbabb_ok
def T11abbba : Tree := .node [113184,430348,506668,902208,3227782,5521457,7684279,9434179,11083800,13501056,15731968,15875395] T11abbbaa T11abbbab
theorem T11abbba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abbba = true :=
  tall_node _ _ _ _ T11abbbaa_ok (by decide +kernel) T11abbbab_ok
def T11abbbba : Tree := (.node [113184,430348,506668,902208,3227782,5521457,8242423,8532035,11083800,13501056,15731968,16605375] (.node [113184,430348,506668,902208,3227782,5521457,8242423,8532035,11083800,13501056,15731968,16076215] (.node [113184,430348,506668,902208,3227782,5521457,8242423,8532035,11083800,13501056,15671960,15731968] .nil .nil) (.node [113184,430348,506668,902208,3227782,5521457,8242423,8532035,11083800,13501056,15731968,16216311] .nil .nil)) (.node [113184,430348,506668,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731968,16076215] (.node [113184,430348,506668,902208,3227782,5521457,8388611,8532035,11083800,13501056,15731968,16076215] .nil .nil) .nil))
theorem T11abbbba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abbbba = true := by decide +kernel
def T11abbbbbaa : Tree := (.node [113184,430348,506668,902208,3227782,5521457,8532035,11083800,13501056,15732032] .nil .nil)
theorem T11abbbbbaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abbbbbaa = true := by decide +kernel
def T11abbbbbab : Tree := (.node [113184,430348,506668,902208,3227782,5521457,8533059,11083800,13501056,15731968] .nil .nil)
theorem T11abbbbbab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abbbbbab = true := by decide +kernel
def T11abbbbba : Tree := .node [113184,430348,506668,902208,3227782,5521457,8532035,11083800,13501056,15875395,16076215] T11abbbbbaa T11abbbbbab
theorem T11abbbbba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abbbbba = true :=
  tall_node _ _ _ _ T11abbbbbaa_ok (by decide +kernel) T11abbbbbab_ok
def T11abbbbbb : Tree := (.node [113184,430348,506668,902208,3227782,5521465,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,506668,902208,3227782,5521461,7684279,8532035,11083800,13501056,15731968] .nil .nil) .nil)
theorem T11abbbbbb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abbbbbb = true := by decide +kernel
def T11abbbbb : Tree := .node [113184,430348,506668,902208,3227782,5521459,7684279,8532035,11083800,13501056,15731968] T11abbbbba T11abbbbbb
theorem T11abbbbb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abbbbb = true :=
  tall_node _ _ _ _ T11abbbbba_ok (by decide +kernel) T11abbbbbb_ok
def T11abbbb : Tree := .node [113184,430348,506668,902208,3227782,5521457,8532035,11083800,13501056,15731968,16076215] T11abbbba T11abbbbb
theorem T11abbbb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abbbb = true :=
  tall_node _ _ _ _ T11abbbba_ok (by decide +kernel) T11abbbbb_ok
def T11abbb : Tree := .node [113184,430348,506668,902208,3227782,5521457,8242423,8532035,11083800,12148894,13501056,15731968] T11abbba T11abbbb
theorem T11abbb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abbb = true :=
  tall_node _ _ _ _ T11abbba_ok (by decide +kernel) T11abbbb_ok
def T11abb : Tree := .node [113184,430348,506668,902208,3227782,5521457,7684279,8532043,11083800,13501056,15731968] T11abba T11abbb
theorem T11abb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11abb = true :=
  tall_node _ _ _ _ T11abba_ok (by decide +kernel) T11abbb_ok
def T11ab : Tree := .node [113184,430348,506668,902208,3227782,5521457,7684279,8242423,8532035,11083800,13501056,15731968] T11aba T11abb
theorem T11ab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11ab = true :=
  tall_node _ _ _ _ T11aba_ok (by decide +kernel) T11abb_ok
def T11a : Tree := .node [113184,113444,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T11aa T11ab
theorem T11a_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11a = true :=
  tall_node _ _ _ _ T11aa_ok (by decide +kernel) T11ab_ok
def T11baaaaaa : Tree := (.node [113184,430348,506668,902208,3227782,5521585,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,506668,902208,3227782,5521521,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,506668,902208,3227782,5521713,7684279,8532035,11083800,13501056,15731968] .nil .nil))
theorem T11baaaaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baaaaaa = true := by decide +kernel
def T11baaaaab : Tree := (.node [113184,430348,506668,902208,3227782,5523505,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,506668,902208,3227782,5522481,7684279,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,506668,902208,3227782,5523761,7684279,8532035,11083800,13501056,15731968] .nil .nil))
theorem T11baaaaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baaaaab = true := by decide +kernel
def T11baaaaa : Tree := .node [113184,430348,506668,902208,3227782,5521969,7684279,8532035,11083800,13501056,15731968] T11baaaaaa T11baaaaab
theorem T11baaaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baaaaa = true :=
  tall_node _ _ _ _ T11baaaaaa_ok (by decide +kernel) T11baaaaab_ok
def T11baaaab : Tree := (.node [113184,430348,506668,902208,3227782,5689661,7684279,8242423,8532035,11083800,13501056,15731968] (.node [113184,430348,506668,902208,3227782,5653041,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,506668,902208,3227782,5652529,7684279,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,506668,902208,3227782,5689661,6145137,7684279,8532035,11083800,13501056,15731968] .nil .nil)) (.node [113184,430348,506668,902208,3227782,6145137,7684279,8532035,11083800,13501056,14053491,15731968] (.node [113184,430348,506668,902208,3227782,6045745,7684279,8532035,11083800,13501056,15731968] .nil .nil) .nil))
theorem T11baaaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baaaab = true := by decide +kernel
def T11baaaa : Tree := .node [113184,430348,506668,902208,3227782,5554225,7684279,8532035,11083800,13501056,15731968] T11baaaaa T11baaaab
theorem T11baaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baaaa = true :=
  tall_node _ _ _ _ T11baaaaa_ok (by decide +kernel) T11baaaab_ok
def T11baaaba : Tree := (.node [113184,430348,506668,902208,3227782,7684279,8532035,11083800,13501056,13910065,15731968] (.node [113184,430348,506668,902208,3227782,7684279,8242423,8532035,11083800,13501056,14053491,15731968] (.node [113184,430348,506668,902208,3227782,6145137,7684279,8532035,11083800,13501056,15731968,16010545] .nil .nil) (.node [113184,430348,506668,902208,3227782,7684279,8242423,8532035,11083800,13501056,14566065,15731968] .nil .nil)) (.node [113184,430348,506668,902209,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,506668,902208,3227782,7684279,8532035,11083800,13501056,13918257,15731968] .nil .nil) .nil))
theorem T11baaaba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baaaba = true := by decide +kernel
def T11baaabba : Tree := (.node [113184,430348,506668,902216,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,506668,902212,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,506668,902224,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil))
theorem T11baaabba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baaabba = true := by decide +kernel
def T11baaabbb : Tree := (.node [113184,430348,506668,904512,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,506668,902464,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) .nil)
theorem T11baaabbb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baaabbb = true := by decide +kernel
def T11baaabb : Tree := .node [113184,430348,506668,902244,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T11baaabba T11baaabbb
theorem T11baaabb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baaabb = true :=
  tall_node _ _ _ _ T11baaabba_ok (by decide +kernel) T11baaabbb_ok
def T11baaab : Tree := .node [113184,430348,506668,902211,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T11baaaba T11baaabb
theorem T11baaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baaab = true :=
  tall_node _ _ _ _ T11baaaba_ok (by decide +kernel) T11baaabb_ok
def T11baaa : Tree := .node [113184,430348,506668,902208,3227782,6145137,7684279,8532035,11083800,13501056,14566065,15731968] T11baaaa T11baaab
theorem T11baaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baaa = true :=
  tall_node _ _ _ _ T11baaaa_ok (by decide +kernel) T11baaab_ok
def T11baabaaa : Tree := (.node [113184,430348,506668,917088,3227782,5521457,7684279,8242423,8532035,11083800,13501056,15731968] (.node [113184,430348,506668,917088,3227782,5521457,6145137,7684279,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,506668,1048428,3227782,4048070,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil))
theorem T11baabaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baabaaa = true := by decide +kernel
def T11baabaab : Tree := (.node [113184,430348,506671,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,506669,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,506684,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil))
theorem T11baabaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baabaab = true := by decide +kernel
def T11baabaa : Tree := .node [113184,430348,506668,1048428,3227782,5521457,7684279,8242423,8532035,11083800,13501056,15731968] T11baabaaa T11baabaab
theorem T11baabaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baabaa = true :=
  tall_node _ _ _ _ T11baabaaa_ok (by decide +kernel) T11baabaab_ok
def T11baababaa : Tree := (.node [113184,430348,507692,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T11baababaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baababaa = true := by decide +kernel
def T11baababab : Tree := (.node [113184,430348,591112,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T11baababab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baababab = true := by decide +kernel
def T11baababa : Tree := .node [113184,430348,507692,902208,3227782,5521457,8532035,11083800,13501056,15731968] T11baababaa T11baababab
theorem T11baababa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baababa = true :=
  tall_node _ _ _ _ T11baababaa_ok (by decide +kernel) T11baababab_ok
def T11baababb : Tree := (.node [113184,430348,902208,917088,3227782,4624780,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,900640,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) .nil)
theorem T11baababb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baababb = true := by decide +kernel
def T11baabab : Tree := .node [113184,430348,638496,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T11baababa T11baababb
theorem T11baabab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baabab = true :=
  tall_node _ _ _ _ T11baababa_ok (by decide +kernel) T11baababb_ok
def T11baaba : Tree := .node [113184,430348,506732,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T11baabaa T11baabab
theorem T11baaba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baaba = true :=
  tall_node _ _ _ _ T11baabaa_ok (by decide +kernel) T11baabab_ok
def T11baabbaa : Tree := (.node [113184,430348,902208,917088,3227782,5521457,7684279,8532035,11083800,13501056,15732480] (.node [113184,430348,902208,917088,3227782,5521457,7684279,8532035,11083800,13501056,15732096] .nil .nil) (.node [113184,430348,902208,917088,3227782,5521457,7684279,8532035,11083800,13501088,15731968] .nil .nil))
theorem T11baabbaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baabbaa = true := by decide +kernel
def T11baabbab : Tree := (.node [113184,430348,902208,917088,3227782,5521457,7684279,8532067,11083800,13501056,15731968] (.node [113184,430348,902208,917088,3227782,5521457,7684279,8532035,11083928,13501056,15731968] .nil .nil) .nil)
theorem T11baabbab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baabbab = true := by decide +kernel
def T11baabba : Tree := .node [113184,430348,902208,917088,3227782,5521457,7684279,8532035,11083832,13501056,15731968] T11baabbaa T11baabbab
theorem T11baabba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baabba = true :=
  tall_node _ _ _ _ T11baabbaa_ok (by decide +kernel) T11baabbab_ok
def T11baabbba : Tree := (.node [113184,430348,902208,917088,3227782,5521969,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,917088,3227782,5521457,7684279,8532547,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,902208,917088,3227782,6046257,7684279,8532035,11083800,13501056,15731968] .nil .nil))
theorem T11baabbba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baabbba = true := by decide +kernel
def T11baabbbb : Tree := (.node [113184,430348,902208,1030956,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,917088,5521457,7684279,11083800,11759815,13501056,13513411,15731968] .nil .nil) .nil)
theorem T11baabbbb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baabbbb = true := by decide +kernel
def T11baabbb : Tree := .node [113184,430348,902208,917088,3228294,5521457,7684279,8532035,11083800,13501056,15731968] T11baabbba T11baabbbb
theorem T11baabbb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baabbb = true :=
  tall_node _ _ _ _ T11baabbba_ok (by decide +kernel) T11baabbbb_ok
def T11baabb : Tree := .node [113184,430348,902208,917088,3227782,5521457,7684279,8532163,11083800,13501056,15731968] T11baabba T11baabbb
theorem T11baabb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baabb = true :=
  tall_node _ _ _ _ T11baabba_ok (by decide +kernel) T11baabbb_ok
def T11baab : Tree := .node [113184,430348,902208,917088,3227782,5521457,7684279,8532035,11083800,13501056,15732000] T11baaba T11baabb
theorem T11baab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baab = true :=
  tall_node _ _ _ _ T11baaba_ok (by decide +kernel) T11baabb_ok
def T11baa : Tree := .node [113184,430348,506668,917088,3227782,4048070,5521457,7684279,8532035,11083800,13501056,15731968] T11baaa T11baab
theorem T11baa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baa = true :=
  tall_node _ _ _ _ T11baaa_ok (by decide +kernel) T11baab_ok
def T11babaaaa : Tree := (.node [113184,430348,902208,1048428,3227782,5521457,7684279,8532035,11083800,11516732,13501056,15731968] (.node [113184,430348,902208,1048428,3227782,5521457,7684279,8532035,11083800,11123256,13501056,15731968] .nil .nil) (.node [113184,430348,902208,1048428,3227782,5521457,7684279,8532035,11083800,13501056,15671960,15731968] .nil .nil))
theorem T11babaaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11babaaaa = true := by decide +kernel
def T11babaaab : Tree := (.node [113184,430348,902208,2210352,3227782,5521457,8532035,11083800,13501056,15731968,15814022] (.node [113184,430348,902208,2162704,3227782,5521457,8532035,8632931,11083800,13501056,15731968,15814022] .nil .nil) (.node [113184,430348,902208,3227782,3227790,5521457,8532035,8632931,11083800,13501056,15731968] .nil .nil))
theorem T11babaaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11babaaab = true := by decide +kernel
def T11babaaa : Tree := .node [113184,430348,902208,1048428,3227782,5521457,7684279,8532035,11083800,13501056,15731968,16236332] T11babaaaa T11babaaab
theorem T11babaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11babaaa = true :=
  tall_node _ _ _ _ T11babaaaa_ok (by decide +kernel) T11babaaab_ok
def T11babaaba : Tree := (.node [113184,430348,902208,3227782,5521457,7684279,8390912,8532035,8895343,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,3275430,5521457,8532035,8827215,11083800,13501056,15731968,16010545] .nil .nil) (.node [113184,430348,902208,3227782,5521457,7684279,8532035,8895343,11083800,13501056,15731968] .nil .nil))
theorem T11babaaba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11babaaba = true := by decide +kernel
def T11babaabb : Tree := (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15732032] (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731980] .nil .nil) .nil)
theorem T11babaabb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11babaabb = true := by decide +kernel
def T11babaab : Tree := .node [113184,430348,902208,3227782,5521457,7684279,8532035,8895343,11083800,13501056,15731968,15814022] T11babaaba T11babaabb
theorem T11babaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11babaab = true :=
  tall_node _ _ _ _ T11babaaba_ok (by decide +kernel) T11babaabb_ok
def T11babaa : Tree := .node [113184,430348,902208,3227782,3275430,5521457,5689661,8532035,11083800,13501056,15731968,15875395] T11babaaa T11babaab
theorem T11babaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11babaa = true :=
  tall_node _ _ _ _ T11babaaa_ok (by decide +kernel) T11babaab_ok
def T11bababaaa : Tree := (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15732035] .nil .nil)
theorem T11bababaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bababaaa = true := by decide +kernel
def T11bababaab : Tree := (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13503136,15731968] .nil .nil)
theorem T11bababaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bababaab = true := by decide +kernel
def T11bababaa : Tree := .node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501120,15732032] T11bababaaa T11bababaab
theorem T11bababaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bababaa = true :=
  tall_node _ _ _ _ T11bababaaa_ok (by decide +kernel) T11bababaab_ok
def T11bababab : Tree := (.node [113184,430348,902208,3227782,5521457,7684279,8533315,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,7684279,8533059,11083800,13502080,15731968] .nil .nil) .nil)
theorem T11bababab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bababab = true := by decide +kernel
def T11bababa : Tree := .node [113184,430348,902208,3227782,5521457,7684279,8533059,11083800,13501056,15731968] T11bababaa T11bababab
theorem T11bababa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bababa = true :=
  tall_node _ _ _ _ T11bababaa_ok (by decide +kernel) T11bababab_ok
def T11bababbaa : Tree := (.node [113184,430348,902208,3227782,5521457,7684343,8532035,11083800,13501056,15731968] .nil .nil)
theorem T11bababbaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bababbaa = true := by decide +kernel
def T11bababbab : Tree := (.node [113184,430348,902208,3227782,5521457,7684343,8532035,11083800,13501120,15731968] .nil .nil)
theorem T11bababbab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bababbab = true := by decide +kernel
def T11bababba : Tree := .node [113184,430348,902208,3227782,5521457,7684343,8532035,11083800,13501056,15732032] T11bababbaa T11bababbab
theorem T11bababba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bababba = true :=
  tall_node _ _ _ _ T11bababbaa_ok (by decide +kernel) T11bababbab_ok
def T11bababbb : Tree := (.node [113184,430348,902208,3227782,5521457,8208631,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,7685367,8532035,11083800,13501056,15731968] .nil .nil) .nil)
theorem T11bababbb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bababbb = true := by decide +kernel
def T11bababb : Tree := .node [113184,430348,902208,3227782,5521457,7685303,8533059,11083800,13501056,15731968] T11bababba T11bababbb
theorem T11bababb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bababb = true :=
  tall_node _ _ _ _ T11bababba_ok (by decide +kernel) T11bababbb_ok
def T11babab : Tree := .node [113184,430348,902208,3227782,5521457,7684279,8895343,11083800,13501056,15731968,15875395] T11bababa T11bababb
theorem T11babab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11babab = true :=
  tall_node _ _ _ _ T11bababa_ok (by decide +kernel) T11bababb_ok
def T11baba : Tree := .node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15732033] T11babaa T11babab
theorem T11baba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11baba = true :=
  tall_node _ _ _ _ T11babaa_ok (by decide +kernel) T11babab_ok
def T11babbaa : Tree := (.node [113184,430348,902208,3227782,5521457,8532035,8632931,11083800,11219035,13501056,15731968,15814022] (.node [113184,430348,902208,3227782,5521457,8532035,8632931,8827215,11083800,13501056,15731968,16076215] (.node [113184,430348,902208,3227782,5521457,8532035,8532051,11083800,13501056,15731968,15814022] .nil .nil) (.node [113184,430348,902208,3227782,5521457,8532035,8632931,11083800,11123256,13501056,15731968,15814022] .nil .nil)) (.node [113184,430348,902208,3227782,5521457,8532035,8632931,11083800,12148894,13501056,15731968,15814022] (.node [113184,430348,902208,3227782,5521457,8532035,8632931,11083800,11254395,13501056,15731968,15814022] .nil .nil) .nil))
theorem T11babbaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11babbaa = true := by decide +kernel
def T11babbaba : Tree := (.node [113184,430348,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731968,15814022,16346526] (.node [113184,430348,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731968,15814022,16330008] .nil .nil) (.node [113184,430348,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731968,16076215] .nil .nil))
theorem T11babbaba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11babbaba = true := by decide +kernel
def T11babbabb : Tree := (.node [113184,430348,902208,3227782,5521457,8532035,8895343,11083800,13501056,15731968,15814022] (.node [113184,430348,902208,3227782,5521457,8532035,8632947,11083800,13501056,15731968] .nil .nil) .nil)
theorem T11babbabb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11babbabb = true := by decide +kernel
def T11babbab : Tree := .node [113184,430348,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731976] T11babbaba T11babbabb
theorem T11babbab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11babbab = true :=
  tall_node _ _ _ _ T11babbaba_ok (by decide +kernel) T11babbabb_ok
def T11babba : Tree := .node [113184,430348,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731968,15731976] T11babbaa T11babbab
theorem T11babba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11babba = true :=
  tall_node _ _ _ _ T11babbaa_ok (by decide +kernel) T11babbab_ok
def T11babbbaaa : Tree := (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731976,15814022] .nil .nil)
theorem T11babbbaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11babbbaaa = true := by decide +kernel
def T11babbbaab : Tree := (.node [113184,430348,902208,3227782,5521457,8532051,8632931,11083800,13501056,15731968] .nil .nil)
theorem T11babbbaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11babbbaab = true := by decide +kernel
def T11babbbaa : Tree := .node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731976,15814030] T11babbbaaa T11babbbaab
theorem T11babbbaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11babbbaa = true :=
  tall_node _ _ _ _ T11babbbaaa_ok (by decide +kernel) T11babbbaab_ok
def T11babbbab : Tree := (.node [113184,430348,902208,3227782,5521457,8632931,11083800,13501056,15875395,16076215] (.node [113184,430348,902208,3227782,5521457,8532051,11083800,13501056,15731968,15814022] .nil .nil) .nil)
theorem T11babbbab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11babbbab = true := by decide +kernel
def T11babbba : Tree := .node [113184,430348,902208,3227782,5521457,8532051,8632947,11083800,13501056,15731968] T11babbbaa T11babbbab
theorem T11babbba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11babbba = true :=
  tall_node _ _ _ _ T11babbbaa_ok (by decide +kernel) T11babbbab_ok
def T11babbbbaa : Tree := (.node [113184,430348,902208,3227782,5521465,8532035,11083800,13501056,15731968,15814022] .nil .nil)
theorem T11babbbbaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11babbbbaa = true := by decide +kernel
def T11babbbbab : Tree := (.node [113184,430348,902208,3227782,5521521,7684279,8532035,11083800,13501056,15732032] .nil .nil)
theorem T11babbbbab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11babbbbab = true := by decide +kernel
def T11babbbba : Tree := .node [113184,430348,902208,3227782,5521521,7684279,8532035,11083800,13501056,15731968] T11babbbbaa T11babbbbab
theorem T11babbbba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11babbbba = true :=
  tall_node _ _ _ _ T11babbbbaa_ok (by decide +kernel) T11babbbbab_ok
def T11babbbbb : Tree := (.node [113184,430348,902208,3227782,5521521,7684343,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5521521,7684279,8532035,11083864,13501056,15731968] .nil .nil) .nil)
theorem T11babbbbb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11babbbbb = true := by decide +kernel
def T11babbbb : Tree := .node [113184,430348,902208,3227782,5521521,7684279,8532035,11083800,13501120,15731968] T11babbbba T11babbbbb
theorem T11babbbb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11babbbb = true :=
  tall_node _ _ _ _ T11babbbba_ok (by decide +kernel) T11babbbbb_ok
def T11babbb : Tree := .node [113184,430348,902208,3227782,5521465,8532035,8632931,11083800,13501056,15731968] T11babbba T11babbbb
theorem T11babbb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11babbb = true :=
  tall_node _ _ _ _ T11babbba_ok (by decide +kernel) T11babbbb_ok
def T11babb : Tree := .node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,15814030] T11babba T11babbb
theorem T11babb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11babb = true :=
  tall_node _ _ _ _ T11babba_ok (by decide +kernel) T11babbb_ok
def T11bab : Tree := .node [113184,430348,902208,3227782,5521457,8242423,8532035,11083800,13501056,15731968,16346526] T11baba T11babb
theorem T11bab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bab = true :=
  tall_node _ _ _ _ T11baba_ok (by decide +kernel) T11babb_ok
def T11ba : Tree := .node [113184,430348,902208,1048428,3227782,5521457,7684279,8532035,8895343,11083800,13501056,15731968] T11baa T11bab
theorem T11ba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11ba = true :=
  tall_node _ _ _ _ T11baa_ok (by decide +kernel) T11bab_ok
def T11bbaaaaaa : Tree := (.node [113184,430348,902208,3227782,5521969,8532035,8827215,11083800,13501056,15731968] .nil .nil)
theorem T11bbaaaaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbaaaaaa = true := by decide +kernel
def T11bbaaaaab : Tree := (.node [113184,430348,902208,3227782,5521969,8532035,11083800,13501056,15731968,16011057] .nil .nil)
theorem T11bbaaaaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbaaaaab = true := by decide +kernel
def T11bbaaaaa : Tree := .node [113184,430348,902208,3227782,5521969,8532035,11083800,13501056,15731968,16010545] T11bbaaaaaa T11bbaaaaab
theorem T11bbaaaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbaaaaa = true :=
  tall_node _ _ _ _ T11bbaaaaaa_ok (by decide +kernel) T11bbaaaaab_ok
def T11bbaaaaba : Tree := (.node [113184,430348,902208,3227782,5522481,7684279,8533059,11083800,13501056,15731968] .nil .nil)
theorem T11bbaaaaba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbaaaaba = true := by decide +kernel
def T11bbaaaabb : Tree := (.node [113184,430348,902208,3227782,5524017,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T11bbaaaabb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbaaaabb = true := by decide +kernel
def T11bbaaaab : Tree := .node [113184,430348,902208,3227782,5522545,7684279,8532035,11083800,13501056,15731968] T11bbaaaaba T11bbaaaabb
theorem T11bbaaaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbaaaab = true :=
  tall_node _ _ _ _ T11bbaaaaba_ok (by decide +kernel) T11bbaaaabb_ok
def T11bbaaaa : Tree := .node [113184,430348,902208,3227782,5522481,7684279,8532035,11084824,13501056,15731968] T11bbaaaaa T11bbaaaab
theorem T11bbaaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbaaaa = true :=
  tall_node _ _ _ _ T11bbaaaaa_ok (by decide +kernel) T11bbaaaab_ok
def T11bbaaaba : Tree := (.node [113184,430348,902208,3227782,5689661,7684279,8532035,11083800,13501056,15732032] (.node [113184,430348,902208,3227782,5689661,7684279,8532035,8632931,11083800,13501056,15731968,15814022] .nil .nil) (.node [113184,430348,902208,3227782,5689661,7684279,8532035,11083800,13501056,15814022,15875395] .nil .nil))
theorem T11bbaaaba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbaaaba = true := by decide +kernel
def T11bbaaabb : Tree := (.node [113184,430348,902208,3227782,5689661,8532035,8632931,11083800,13501056,15731968,16076215] (.node [113184,430348,902208,3227782,5689661,7684343,8532035,11083800,13501056,15731968] .nil .nil) .nil)
theorem T11bbaaabb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbaaabb = true := by decide +kernel
def T11bbaaab : Tree := .node [113184,430348,902208,3227782,5689661,7684279,8632931,11083800,13501056,15731968,15875395] T11bbaaaba T11bbaaabb
theorem T11bbaaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbaaab = true :=
  tall_node _ _ _ _ T11bbaaaba_ok (by decide +kernel) T11bbaaabb_ok
def T11bbaaa : Tree := .node [113184,430348,902208,3227782,5554289,7684279,8532035,11083800,13501056,15731968] T11bbaaaa T11bbaaab
theorem T11bbaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbaaa = true :=
  tall_node _ _ _ _ T11bbaaaa_ok (by decide +kernel) T11bbaaab_ok
def T11bbaabaa : Tree := (.node [113184,430348,902208,3227782,6145137,7684279,8532035,11083800,13501056,15731968,16666545] (.node [113184,430348,902208,3227782,6045809,7684279,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,902208,3227782,7684279,8532035,8827215,11083800,13501056,14566065,15731968,16010545] .nil .nil))
theorem T11bbaabaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbaabaa = true := by decide +kernel
def T11bbaabab : Tree := (.node [113184,430348,902208,3227846,5521521,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,8242423,8532035,11083800,13501056,14566065,15731968,16010545] .nil .nil) .nil)
theorem T11bbaabab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbaabab = true := by decide +kernel
def T11bbaaba : Tree := .node [113184,430348,902208,3227782,7684279,8532083,11083800,13501056,15731968] T11bbaabaa T11bbaabab
theorem T11bbaaba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbaaba = true :=
  tall_node _ _ _ _ T11bbaabaa_ok (by decide +kernel) T11bbaabab_ok
def T11bbaabba : Tree := (.node [113184,430348,902208,3275430,5689661,7684279,8532035,11083800,13501056,15731968,15875395] (.node [113184,430348,902208,3275430,5689661,7684279,8242423,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,902208,3275430,5689661,8532035,11083800,13501056,15731968,16076215] .nil .nil))
theorem T11bbaabba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbaabba = true := by decide +kernel
def T11bbaabbb : Tree := (.node [113184,430348,902211,3227782,5521457,8532035,11083800,13501056,15731968,15814022] (.node [113184,430348,902211,3227782,5521457,8532035,11083800,12148894,13501056,15731968] .nil .nil) .nil)
theorem T11bbaabbb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbaabbb = true := by decide +kernel
def T11bbaabb : Tree := .node [113184,430348,902211,3227782,5521457,7684279,11083800,13501056,15731968,15875395] T11bbaabba T11bbaabbb
theorem T11bbaabb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbaabb = true :=
  tall_node _ _ _ _ T11bbaabba_ok (by decide +kernel) T11bbaabbb_ok
def T11bbaab : Tree := .node [113184,430348,902208,3227846,5689661,7684279,8532035,11083800,13501056,15731968] T11bbaaba T11bbaabb
theorem T11bbaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbaab = true :=
  tall_node _ _ _ _ T11bbaaba_ok (by decide +kernel) T11bbaabb_ok
def T11bbaa : Tree := .node [113184,430348,902208,3227782,5689661,8532035,11083800,13501056,15875395,16076215] T11bbaaa T11bbaab
theorem T11bbaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbaa = true :=
  tall_node _ _ _ _ T11bbaaa_ok (by decide +kernel) T11bbaab_ok
def T11bbabaaaa : Tree := (.node [113184,430348,917088,3227782,5521457,7684279,8532035,11083800,13501056,15732032] .nil .nil)
theorem T11bbabaaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbabaaaa = true := by decide +kernel
def T11bbabaaab : Tree := (.node [113184,430348,917088,3227782,5521457,8242423,8532035,11083800,13501056,14566065,15731968] .nil .nil)
theorem T11bbabaaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbabaaab = true := by decide +kernel
def T11bbabaaa : Tree := .node [113184,430348,917088,3227782,5521457,7684343,8532035,11083800,13501056,15731968] T11bbabaaaa T11bbabaaab
theorem T11bbabaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbabaaa = true :=
  tall_node _ _ _ _ T11bbabaaaa_ok (by decide +kernel) T11bbabaaab_ok
def T11bbabaab : Tree := (.node [113184,430348,917088,3275430,4048070,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,917088,3227782,7684279,8242423,8532035,11083800,13501056,14566065,15731968] .nil .nil) .nil)
theorem T11bbabaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbabaab = true := by decide +kernel
def T11bbabaa : Tree := .node [113184,430348,917088,3227782,6145137,7684279,8532035,11083800,13501056,14566065,15731968] T11bbabaaa T11bbabaab
theorem T11bbabaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbabaa = true :=
  tall_node _ _ _ _ T11bbabaaa_ok (by decide +kernel) T11bbabaab_ok
def T11bbababaa : Tree := (.node [113184,430348,3227782,4048070,5521457,7684279,8533059,11083800,13501056,15731968] .nil .nil)
theorem T11bbababaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbababaa = true := by decide +kernel
def T11bbababab : Tree := (.node [113184,430349,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T11bbababab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbababab = true := by decide +kernel
def T11bbababa : Tree := .node [113184,430348,3227782,5521457,7684279,8242423,8533059,11083800,13501056,15731968] T11bbababaa T11bbababab
theorem T11bbababa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbababa = true :=
  tall_node _ _ _ _ T11bbababaa_ok (by decide +kernel) T11bbababab_ok
def T11bbababb : Tree := (.node [113184,430350,506670,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,430350,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) .nil)
theorem T11bbababb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbababb = true := by decide +kernel
def T11bbabab : Tree := .node [113184,430349,506669,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T11bbababa T11bbababb
theorem T11bbabab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbabab = true :=
  tall_node _ _ _ _ T11bbababa_ok (by decide +kernel) T11bbababb_ok
def T11bbaba : Tree := .node [113184,430348,917088,3275430,5521457,7684279,8242423,8532035,11083800,13501056,15731968] T11bbabaa T11bbabab
theorem T11bbaba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbaba = true :=
  tall_node _ _ _ _ T11bbabaa_ok (by decide +kernel) T11bbabab_ok
def T11bbabbaaa : Tree := (.node [113184,430351,506671,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T11bbabbaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbabbaaa = true := by decide +kernel
def T11bbabbaab : Tree := (.node [113184,430351,902208,3227782,5521457,8532035,11083800,13501056,15731968,16010545] .nil .nil)
theorem T11bbabbaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbabbaab = true := by decide +kernel
def T11bbabbaa : Tree := .node [113184,430351,902208,3227782,5521457,7684279,11083800,13501056,15731968,15875395] T11bbabbaaa T11bbabbaab
theorem T11bbabbaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbabbaa = true :=
  tall_node _ _ _ _ T11bbabbaaa_ok (by decide +kernel) T11bbabbaab_ok
def T11bbabbab : Tree := (.node [113184,430364,506684,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,430364,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) .nil)
theorem T11bbabbab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbabbab = true := by decide +kernel
def T11bbabba : Tree := .node [113184,430351,902208,3227782,5521457,8532035,11083800,13501056,15731968,16076215] T11bbabbaa T11bbabbab
theorem T11bbabba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbabba = true :=
  tall_node _ _ _ _ T11bbabbaa_ok (by decide +kernel) T11bbabbab_ok
def T11bbabbbaa : Tree := (.node [113184,430364,902208,1037660,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T11bbabbbaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbabbbaa = true := by decide +kernel
def T11bbabbbab : Tree := (.node [113184,430364,902208,3227782,5521457,8532035,11083800,13501056,15731968,15814022] .nil .nil)
theorem T11bbabbbab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbabbbab = true := by decide +kernel
def T11bbabbba : Tree := .node [113184,430364,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731968] T11bbabbbaa T11bbabbbab
theorem T11bbabbba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbabbba = true :=
  tall_node _ _ _ _ T11bbabbbaa_ok (by decide +kernel) T11bbabbbab_ok
def T11bbabbbb : Tree := (.node [113184,430412,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,430380,902208,917088,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) .nil)
theorem T11bbabbbb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbabbbb = true := by decide +kernel
def T11bbabbb : Tree := .node [113184,430380,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T11bbabbba T11bbabbbb
theorem T11bbabbb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbabbb = true :=
  tall_node _ _ _ _ T11bbabbba_ok (by decide +kernel) T11bbabbbb_ok
def T11bbabb : Tree := .node [113184,430364,902208,1037644,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T11bbabba T11bbabbb
theorem T11bbabb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbabb = true :=
  tall_node _ _ _ _ T11bbabba_ok (by decide +kernel) T11bbabbb_ok
def T11bbab : Tree := .node [113184,430351,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T11bbaba T11bbabb
theorem T11bbab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbab = true :=
  tall_node _ _ _ _ T11bbaba_ok (by decide +kernel) T11bbabb_ok
def T11bba : Tree := .node [113184,430348,902211,3227782,5521457,8532035,11083800,13501056,15731968,16076215] T11bbaa T11bbab
theorem T11bba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bba = true :=
  tall_node _ _ _ _ T11bbaa_ok (by decide +kernel) T11bbab_ok
def T11bbbaaaaa : Tree := (.node [113184,430412,902208,3227782,5521457,7684279,8532035,11083800,13501056,15732032] .nil .nil)
theorem T11bbbaaaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbaaaaa = true := by decide +kernel
def T11bbbaaaab : Tree := (.node [113184,430412,902208,3227782,5521457,7684343,8532035,11083800,13501056,15731968] .nil .nil)
theorem T11bbbaaaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbaaaab = true := by decide +kernel
def T11bbbaaaa : Tree := .node [113184,430412,902208,3227782,5521457,7684279,8532035,11083864,13501056,15731968] T11bbbaaaaa T11bbbaaaab
theorem T11bbbaaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbaaaa = true :=
  tall_node _ _ _ _ T11bbbaaaaa_ok (by decide +kernel) T11bbbaaaab_ok
def T11bbbaaaba : Tree := (.node [113184,430412,902208,3227846,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T11bbbaaaba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbaaaba = true := by decide +kernel
def T11bbbaaabb : Tree := (.node [113184,430476,506796,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T11bbbaaabb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbaaabb = true := by decide +kernel
def T11bbbaaab : Tree := .node [113184,430476,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T11bbbaaaba T11bbbaaabb
theorem T11bbbaaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbaaab = true :=
  tall_node _ _ _ _ T11bbbaaaba_ok (by decide +kernel) T11bbbaaabb_ok
def T11bbbaaa : Tree := .node [113184,430412,902208,3227782,5521521,7684279,8532035,11083800,13501056,15731968] T11bbbaaaa T11bbbaaab
theorem T11bbbaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbaaa = true :=
  tall_node _ _ _ _ T11bbbaaaa_ok (by decide +kernel) T11bbbaaab_ok
def T11bbbaabaa : Tree := (.node [113184,430476,902208,3227782,5521457,8532035,8827215,11083800,13501056,15731968] .nil .nil)
theorem T11bbbaabaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbaabaa = true := by decide +kernel
def T11bbbaabab : Tree := (.node [113184,430476,902208,3227782,5521457,8532035,11083800,13501056,15731968,16010545] .nil .nil)
theorem T11bbbaabab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbaabab = true := by decide +kernel
def T11bbbaaba : Tree := .node [113184,430476,902208,3227782,5521457,8532035,8827343,11083800,13501056,15731968] T11bbbaabaa T11bbbaabab
theorem T11bbbaaba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbaaba = true :=
  tall_node _ _ _ _ T11bbbaabaa_ok (by decide +kernel) T11bbbaabab_ok
def T11bbbaabb : Tree := (.node [113184,431372,506668,902208,3227782,5521457,8532035,11083800,13501056,15731968] (.node [113184,431372,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) .nil)
theorem T11bbbaabb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbaabb = true := by decide +kernel
def T11bbbaab : Tree := .node [113184,430860,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T11bbbaaba T11bbbaabb
theorem T11bbbaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbaab = true :=
  tall_node _ _ _ _ T11bbbaaba_ok (by decide +kernel) T11bbbaabb_ok
def T11bbbaa : Tree := .node [113184,430476,902208,917088,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T11bbbaaa T11bbbaab
theorem T11bbbaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbaa = true :=
  tall_node _ _ _ _ T11bbbaaa_ok (by decide +kernel) T11bbbaab_ok
def T11bbbabaaa : Tree := (.node [113184,431372,507692,902208,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil)
theorem T11bbbabaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbabaaa = true := by decide +kernel
def T11bbbabaab : Tree := (.node [113184,431372,902208,3227782,5521457,7684279,8532035,11083800,13502080,15731968] .nil .nil)
theorem T11bbbabaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbabaab = true := by decide +kernel
def T11bbbabaa : Tree := .node [113184,431372,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T11bbbabaaa T11bbbabaab
theorem T11bbbabaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbabaa = true :=
  tall_node _ _ _ _ T11bbbabaaa_ok (by decide +kernel) T11bbbabaab_ok
def T11bbbabab : Tree := (.node [113184,431372,902208,3227782,5521457,7685303,8532035,11083800,13501056,15731968] (.node [113184,431372,902208,3227782,5521457,7684279,8533059,11083800,13501056,15731968] .nil .nil) .nil)
theorem T11bbbabab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbabab = true := by decide +kernel
def T11bbbaba : Tree := .node [113184,431372,902208,3227782,5521457,7684279,8532035,11084824,13501056,15731968] T11bbbabaa T11bbbabab
theorem T11bbbaba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbaba = true :=
  tall_node _ _ _ _ T11bbbabaa_ok (by decide +kernel) T11bbbabab_ok
def T11bbbabbaa : Tree := (.node [113184,431372,902208,3228806,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T11bbbabbaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbabbaa = true := by decide +kernel
def T11bbbabbab : Tree := (.node [113184,431372,3227782,5521457,6145137,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T11bbbabbab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbabbab = true := by decide +kernel
def T11bbbabba : Tree := .node [113184,431372,3227782,4048070,5521457,7684279,8532035,11083800,13501056,15731968] T11bbbabbaa T11bbbabbab
theorem T11bbbabba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbabba = true :=
  tall_node _ _ _ _ T11bbbabbaa_ok (by decide +kernel) T11bbbabbab_ok
def T11bbbabbb : Tree := (.node [113184,432396,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,431436,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) .nil)
theorem T11bbbabbb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbabbb = true := by decide +kernel
def T11bbbabb : Tree := .node [113184,431372,3227782,5521457,7684279,8242423,8532035,11083800,13501056,15731968] T11bbbabba T11bbbabbb
theorem T11bbbabb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbabb = true :=
  tall_node _ _ _ _ T11bbbabba_ok (by decide +kernel) T11bbbabbb_ok
def T11bbbab : Tree := .node [113184,431372,902208,3227782,5522481,7684279,8532035,11083800,13501056,15731968] T11bbbaba T11bbbabb
theorem T11bbbab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbab = true :=
  tall_node _ _ _ _ T11bbbaba_ok (by decide +kernel) T11bbbabb_ok
def T11bbba : Tree := .node [113184,431372,507692,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T11bbbaa T11bbbab
theorem T11bbba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbba = true :=
  tall_node _ _ _ _ T11bbbaa_ok (by decide +kernel) T11bbbab_ok
def T11bbbbaaa : Tree := (.node [113184,446732,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,433420,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,506668,902208,954636,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil))
theorem T11bbbbaaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbbaaa = true := by decide +kernel
def T11bbbbaab : Tree := (.node [113184,506668,902208,1037644,3227782,5521457,7684279,8532035,11083800,13501056,13538188,15731968] (.node [113184,506668,902208,1037644,3227782,5521457,7684279,8532035,8827215,11083800,13501056,15731968] .nil .nil) .nil)
theorem T11bbbbaab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbbaab = true := by decide +kernel
def T11bbbbaa : Tree := .node [113184,506668,902208,1037644,3227782,5521457,5689661,7684279,8532035,11083800,13501056,15731968] T11bbbbaaa T11bbbbaab
theorem T11bbbbaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbbaa = true :=
  tall_node _ _ _ _ T11bbbbaaa_ok (by decide +kernel) T11bbbbaab_ok
def T11bbbbab : Tree := (.node [113184,506668,902208,1048428,3227782,5521457,7684279,8532035,11083800,13501056,15731968,16162060] (.node [113184,506668,902208,1048428,3227782,5521457,5689661,7684279,8532035,11083800,13501056,15731968] (.node [113184,506668,902208,1037644,3227782,5689661,7684279,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,506668,902208,1048428,3227782,5521457,7684279,8532035,11083800,13501056,13538188,15731968] .nil .nil)) (.node [113184,506668,902208,3227782,4624652,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,506668,902208,1048428,3227782,5689661,7684279,8532035,11083800,13501056,15731968] .nil .nil) .nil))
theorem T11bbbbab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbbab = true := by decide +kernel
def T11bbbba : Tree := .node [113184,506668,902208,1037644,3227782,5521457,7684279,8532035,11083800,13501056,15731968,16162060] T11bbbbaa T11bbbbab
theorem T11bbbba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbba = true :=
  tall_node _ _ _ _ T11bbbbaa_ok (by decide +kernel) T11bbbbab_ok
def T11bbbbbaa : Tree := (.node [113184,506668,902208,3227782,5521457,7684279,8532035,10916108,11083800,13501056,15731968] (.node [113184,506668,902208,3227782,5521457,7684279,8532035,8818956,11083800,13501056,15731968] .nil .nil) (.node [113184,506668,902208,3227782,5689661,6145137,7684279,8532035,11083800,13501056,15731968] .nil .nil))
theorem T11bbbbbaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbbbaa = true := by decide +kernel
def T11bbbbbab : Tree := (.node [113184,506668,902208,3227782,5689661,8532035,11083800,13501056,15731968,16076215] (.node [113184,506668,902208,3227782,5689661,7684279,8532035,11083800,13501056,15731968,15875395] .nil .nil) .nil)
theorem T11bbbbbab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbbbab = true := by decide +kernel
def T11bbbbba : Tree := .node [113184,506668,902208,3227782,5689661,7684279,8242423,8532035,11083800,13501056,15731968] T11bbbbbaa T11bbbbbab
theorem T11bbbbba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbbba = true :=
  tall_node _ _ _ _ T11bbbbbaa_ok (by decide +kernel) T11bbbbbab_ok
def T11bbbbbbaa : Tree := (.node [113184,902208,3227782,5689661,7684279,8532035,8895343,11083800,13501056,15731968] .nil .nil)
theorem T11bbbbbbaa_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbbbbaa = true := by decide +kernel
def T11bbbbbbab : Tree := (.node [113184,902208,3227782,5689661,8532035,8827215,11083800,13501056,15731968,16076215] .nil .nil)
theorem T11bbbbbbab_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbbbbab = true := by decide +kernel
def T11bbbbbba : Tree := .node [113184,902208,3227782,5689661,7684279,8827215,11083800,13501056,15731968,15875395] T11bbbbbbaa T11bbbbbbab
theorem T11bbbbbba_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbbbba = true :=
  tall_node _ _ _ _ T11bbbbbbaa_ok (by decide +kernel) T11bbbbbbab_ok
def T11bbbbbbb : Tree := (.node [506668,902208,3275430,5689661,7684279,8532035,11083800,13501056,15731968] (.node [114208,431372,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) .nil)
theorem T11bbbbbbb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbbbbb = true := by decide +kernel
def T11bbbbbb : Tree := .node [113184,902208,3275430,5689661,7684279,8532035,8827215,11083800,13501056,15731968] T11bbbbbba T11bbbbbbb
theorem T11bbbbbb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbbbb = true :=
  tall_node _ _ _ _ T11bbbbbba_ok (by decide +kernel) T11bbbbbbb_ok
def T11bbbbb : Tree := .node [113184,902208,3227782,4624780,5521457,8532035,8827215,11083800,13501056,15731968] T11bbbbba T11bbbbbb
theorem T11bbbbb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbbb = true :=
  tall_node _ _ _ _ T11bbbbba_ok (by decide +kernel) T11bbbbbb_ok
def T11bbbb : Tree := .node [113184,506668,902208,3227782,4624780,5521457,7684279,8532035,11083800,13501056,15731968] T11bbbba T11bbbbb
theorem T11bbbb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbbb = true :=
  tall_node _ _ _ _ T11bbbba_ok (by decide +kernel) T11bbbbb_ok
def T11bbb : Tree := .node [113184,432428,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T11bbba T11bbbb
theorem T11bbb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bbb = true :=
  tall_node _ _ _ _ T11bbba_ok (by decide +kernel) T11bbbb_ok
def T11bb : Tree := .node [113184,430412,506732,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T11bba T11bbb
theorem T11bb_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11bb = true :=
  tall_node _ _ _ _ T11bba_ok (by decide +kernel) T11bbb_ok
def T11b : Tree := .node [113184,430348,902208,3227782,5521523,7684279,8532035,11083800,13501056,15731968] T11ba T11bb
theorem T11b_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11b = true :=
  tall_node _ _ _ _ T11ba_ok (by decide +kernel) T11bb_ok
def T11 : Tree := .node [113184,430348,506668,902208,3227782,5521521,7684279,8532035,11083800,13501056,15731968] T11a T11b
theorem T11_ok : tall (expFast false (RP PR T10 R10 10) T10 10) T11 = true :=
  tall_node _ _ _ _ T11a_ok (by decide +kernel) T11b_ok
def R11aaa : Tree := (.node [4,113184,430348,902208,3227846,5521457,8532035,11083800,13501056,15731968] (.node [4,1088,113184,430348,3227782,5521457,8532035,11083800,13501056,15731968] (.node [1,113184,430348,902208,3227782,5521969,8532035,11083800,13501056,15731968] (.node [1,113184,430348,902208,3227782,5521457,8532163,11083800,13501056,15731968] (.node [1,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil) .nil) (.node [3,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil)) (.node [4,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15732032] (.node [4,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil) (.node [4,113184,430348,902208,3227782,5521457,8533059,11083800,13501056,15731968] .nil .nil))) (.node [16,24,113184,430348,902208,3227782,5521457,8532035,13501056,15731968] (.node [8,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] (.node [4,113184,431372,902208,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil) (.node [8,113184,430476,902208,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil)) (.node [24,113184,430348,902208,3227782,5521465,7684279,8532035,13501056,15731968] (.node [16,113184,430348,902208,3227782,5521969,8532035,11083800,13501056,15731968] .nil .nil) (.node [24,113184,430348,902208,3227782,5521465,8532035,13501056,15731968] .nil .nil))))
theorem R11aaa_ok : tall (refOK cpF 11) R11aaa = true := by decide +kernel
def R11aab : Tree := (.node [67,113184,430348,902208,3227782,7684279,11083800,13501056,14053491,15731968] (.node [67,113184,430348,902208,917088,3227782,5521457,11083800,13501056,15731968] (.node [48,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] (.node [24,113184,430364,902208,3227782,5521457,8532035,13501056,15731968] .nil .nil) (.node [67,113184,113251,430348,902208,3227782,5521457,11083800,13501056,15731968] .nil .nil)) (.node [67,113184,430348,902208,3227782,5521457,11083800,13501123,15731968] (.node [67,113184,430348,902208,3227782,5521457,11083800,13501056,15731968,15843104] .nil .nil) (.node [67,113184,430348,902208,3227782,5521523,11083800,13501056,15731968] .nil .nil))) (.node [256,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15732480] (.node [67,113184,430415,902208,3227782,5521457,11083800,13501056,15731968] (.node [67,113184,430348,902211,3227782,5521457,11083800,13501056,15731968] .nil .nil) (.node [256,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil)) (.node [1024,113184,430348,3227782,5521521,7684279,8532035,11083800,13501056,15731968] (.node [256,113184,430476,902208,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil) (.node [1088,113184,430348,3227782,3658126,5521457,8532035,11083800,13501056,15731968] .nil .nil))))
theorem R11aab_ok : tall (refOK cpF 11) R11aab = true := by decide +kernel
def R11aa : Tree := .node [24,113184,430364,902208,3227782,5521457,7684279,8532035,13501056,15731968] R11aaa R11aab
theorem R11aa_ok : tall (refOK cpF 11) R11aa = true :=
  tall_node _ _ _ _ R11aaa_ok (by decide +kernel) R11aab_ok
def R11aba : Tree := (.node [36864,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] (.node [1088,113184,430348,3227782,5521457,8533059,11083800,13501056,15731968] (.node [1088,113184,430348,3227782,5521457,8532035,11083800,13501056,15875395,16076215] (.node [1088,113184,430348,3227782,5521457,8532035,11083800,13501056,15732032] (.node [1088,113184,430348,3227782,5521457,8532035,11083800,13501056,15731968,15843104] .nil .nil) .nil) (.node [1088,113184,430348,3227782,5521457,8532035,11083800,13502144,15731968] .nil .nil)) (.node [1088,113184,431436,3227782,5521457,8532035,11083800,13501056,15731968] (.node [1088,113184,430348,3227782,5522545,8532035,11083800,13501056,15731968] .nil .nil) (.node [12288,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil))) (.node [65568,113440,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] (.node [65568,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] (.node [65536,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil) (.node [65568,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731971] .nil .nil)) (.node [73728,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] (.node [67616,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil) (.node [81920,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil))))
theorem R11aba_ok : tall (refOK cpF 11) R11aba = true := by decide +kernel
def R11abb : Tree := (.node [113184,430348,902208,2162704,3227782,5521457,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,917088,3227782,5521457,8532035,11083800,13501056,15732032] (.node [113184,344064,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] (.node [113184,327684,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,344064,430348,902216,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil)) (.node [113184,430348,902208,1064960,3227782,5521457,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,917088,3227782,5521457,8533059,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,902208,2162688,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil))) (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501120,15731968] (.node [113184,430348,902208,3145728,3227782,5521457,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,2162704,3227782,5521457,8532035,11083800,13501056,15731971] .nil .nil) (.node [113184,430348,902208,3227782,5521457,7340032,8532035,11083800,13501056,15731968] .nil .nil)) (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13503104,15731968] (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13502080,15731968] .nil .nil) (.node [113184,430348,902208,3227782,5521457,7684287,8532035,11083800,13501056,15731968] .nil .nil))))
theorem R11abb_ok : tall (refOK cpF 11) R11abb = true := by decide +kernel
def R11ab : Tree := .node [98304,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] R11aba R11abb
theorem R11ab_ok : tall (refOK cpF 11) R11ab = true :=
  tall_node _ _ _ _ R11aba_ok (by decide +kernel) R11abb_ok
def R11a : Tree := .node [1088,113184,430348,3227782,5521457,8532035,11083800,11514140,13501056,15731968] R11aa R11ab
theorem R11a_ok : tall (refOK cpF 11) R11a = true :=
  tall_node _ _ _ _ R11aa_ok (by decide +kernel) R11ab_ok
def R11ba : Tree := (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16605375] (.node [113184,430348,902208,3227782,5521457,8256183,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,7732151,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,7731903,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,7731895,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,7685303,8532035,11083800,13502080,15731968] .nil .nil) .nil) (.node [113184,430348,902208,3227782,5521457,7731959,8532035,11083800,13501056,15731968] .nil .nil)) (.node [113184,430348,902208,3227782,5521457,7860671,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,7732919,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,902208,3227782,5521457,8242423,8532035,11083800,13501056,15731968] .nil .nil))) (.node [113184,430348,902208,3227782,5521457,8532035,11083800,12057583,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,8388608,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,8388607,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,902208,3227782,5521457,8388611,11083800,13501056,15875395,16076215] .nil .nil)) (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16076279] (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16076215] .nil .nil) (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16121783] .nil .nil)))) (.node [113184,430348,902208,3227782,5521457,8895343,11083800,13501056,15731968,15875395] (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15875395,16076215] (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16633335] (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16608703] .nil .nil) (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731971,16076215] .nil .nil)) (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13538188,15731968,16666545] (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501059,15731968,16076215] .nil .nil) (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13546447,14566065,15731968] .nil .nil))) (.node [113184,430348,902208,3227782,5521717,8532035,11083800,13501056,15731968,16076215] (.node [113184,430348,902208,3227782,5521585,8532035,8827215,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5521459,8532035,11083800,13501056,15731968,16076215] .nil .nil) (.node [113184,430348,902208,3227782,5521585,8532035,11083800,13501056,15731968,16010545] .nil .nil)) (.node [113184,430348,902208,3227782,5689661,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5522481,7685303,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,902208,3227782,5689661,7684279,8533059,11083800,13501056,15731968] .nil .nil)))))
theorem R11ba_ok : tall (refOK cpF 11) R11ba = true := by decide +kernel
def R11bb : Tree := (.node [113184,430349,902208,3227782,5521457,7852479,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,3275430,7684279,8532035,11083800,13501056,14086527,15731968] (.node [113184,430348,902208,3227782,7684279,8532035,11083800,13501056,14053491,15731968] (.node [113184,430348,902208,3227782,5689789,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5689725,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5689663,7684279,8532035,11083800,13501056,15731968] .nil .nil) .nil) (.node [113184,430348,902208,3227782,7684279,8532035,11083800,13501056,13910129,15731968] .nil .nil)) (.node [113184,430348,902208,3227782,7684279,8532035,11083800,13501056,14566065,15731968] (.node [113184,430348,902208,3227782,7684279,8532035,11083800,13501056,14054515,15731968] .nil .nil) (.node [113184,430348,902208,3227814,5689661,7684279,8532035,11083800,13501056,15731968] .nil .nil))) (.node [113184,430348,917088,3227782,5521457,8242423,8532035,11083800,13501056,15731968] (.node [113184,430348,902211,3227782,5521457,8532035,11083800,13501056,15731968,15843104] (.node [113184,430348,902211,917091,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,902212,3227782,5521457,8242423,8532035,11083800,13501056,15731968] .nil .nil)) (.node [113184,430348,1048428,3227782,5521457,8242423,8532035,11083800,13501056,15731968] (.node [113184,430348,917088,3227782,5521457,8532035,11083800,13501056,15732032] .nil .nil) (.node [113184,430348,3227782,4048070,5521457,8533059,11083800,13501056,15731968] .nil .nil)))) (.node [113184,506668,902208,3227782,7684279,8532035,11083800,13538188,14566065,15731968] (.node [113184,430380,902208,3227782,5689661,7684279,8532035,11083800,13501056,15731968] (.node [113184,430351,902208,3227782,5521457,8532035,8827215,11083800,13501056,15731968] (.node [113184,430349,902208,3227782,5689661,7684279,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,430380,902208,3227782,5521457,7852479,8532035,11083800,13501056,15731968] .nil .nil)) (.node [113184,430476,902208,3227782,5521457,7852479,8532035,11083800,13501056,15731968] (.node [113184,430476,902208,3227782,3658126,5521457,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,506668,902208,3227782,7684279,8532035,11083800,13501056,14603197,15731968] .nil .nil))) (.node [113184,902208,3275430,5689661,7684279,8532035,11083800,11514140,13501056,15731968] (.node [113184,506668,902208,5689661,7684279,8532035,11083800,11759815,13501056,15731968] (.node [113184,506668,902208,3275430,5689661,7684279,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,902208,3227782,5521457,5689661,8532035,8895343,11083800,13501056,15731968] .nil .nil)) (.node [113184,1037644,3227782,5521457,8242423,8532035,11083800,13501056,15731968,16162060] (.node [113184,1037644,3227782,5521457,8242423,8532035,8827215,11083800,13501056,15731968] .nil .nil) (.node [506668,902208,3227782,5689661,7684279,8532035,11083800,13501056,15731968,15843104] .nil .nil)))))
theorem R11bb_ok : tall (refOK cpF 11) R11bb = true := by decide +kernel
def R11b : Tree := .node [113184,430348,902208,3227782,5689661,8532035,11083800,13501056,15731968,16076215] R11ba R11bb
theorem R11b_ok : tall (refOK cpF 11) R11b = true :=
  tall_node _ _ _ _ R11ba_ok (by decide +kernel) R11bb_ok
def R11 : Tree := .node [113184,430348,902208,3227782,5521457,7685303,8532035,11083800,13501056,15731968] R11a R11b
theorem R11_ok : tall (refOK cpF 11) R11 = true :=
  tall_node _ _ _ _ R11a_ok (by decide +kernel) R11b_ok
def T12aaaaaaa : Tree := (.node [3,64,113184,430348,902208,3227782,5521457,7684279,11083800,13501056,15731968] (.node [1,113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) .nil)
theorem T12aaaaaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaaaaaa = true := by decide +kernel
def T12aaaaaaba : Tree := (.node [3,113184,430348,902208,3227782,5521457,7684279,11083800,13501056,15731968,15875395] .nil .nil)
theorem T12aaaaaaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaaaaaba = true := by decide +kernel
def T12aaaaaabb : Tree := .nil
theorem T12aaaaaabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaaaaabb = true := by decide +kernel
def T12aaaaaab : Tree := .node [3,113184,430348,902208,3227782,5521457,8532035,11083800,12148894,13501056,15731968] T12aaaaaaba T12aaaaaabb
theorem T12aaaaaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaaaaab = true :=
  tall_node _ _ _ _ T12aaaaaaba_ok (by decide +kernel) T12aaaaaabb_ok
def T12aaaaaa : Tree := .node [3,113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12aaaaaaa T12aaaaaab
theorem T12aaaaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaaaaa = true :=
  tall_node _ _ _ _ T12aaaaaaa_ok (by decide +kernel) T12aaaaaab_ok
def T12aaaaaba : Tree := (.node [4,113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [3,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16076215] .nil .nil) .nil)
theorem T12aaaaaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaaaaba = true := by decide +kernel
def T12aaaaabb : Tree := (.node [8,113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12aaaaabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaaaabb = true := by decide +kernel
def T12aaaaab : Tree := .node [4,113184,430348,902208,1037644,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12aaaaaba T12aaaaabb
theorem T12aaaaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaaaab = true :=
  tall_node _ _ _ _ T12aaaaaba_ok (by decide +kernel) T12aaaaabb_ok
def T12aaaaa : Tree := .node [3,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,15814022] T12aaaaaa T12aaaaab
theorem T12aaaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaaaa = true :=
  tall_node _ _ _ _ T12aaaaaa_ok (by decide +kernel) T12aaaaab_ok
def T12aaaabaaa : Tree := (.node [8,113184,430348,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731968] .nil .nil)
theorem T12aaaabaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaaabaaa = true := by decide +kernel
def T12aaaabaab : Tree := .nil
theorem T12aaaabaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaaabaab = true := by decide +kernel
def T12aaaabaa : Tree := .node [8,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,15814022] T12aaaabaaa T12aaaabaab
theorem T12aaaabaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaaabaa = true :=
  tall_node _ _ _ _ T12aaaabaaa_ok (by decide +kernel) T12aaaabaab_ok
def T12aaaabab : Tree := (.node [16,113184,430348,902208,1037644,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [16,113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) .nil)
theorem T12aaaabab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaaabab = true := by decide +kernel
def T12aaaaba : Tree := .node [12,113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12aaaabaa T12aaaabab
theorem T12aaaaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaaaba = true :=
  tall_node _ _ _ _ T12aaaabaa_ok (by decide +kernel) T12aaaabab_ok
def T12aaaabbaa : Tree := (.node [16,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,15814022] .nil .nil)
theorem T12aaaabbaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaaabbaa = true := by decide +kernel
def T12aaaabbab : Tree := .nil
theorem T12aaaabbab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaaabbab = true := by decide +kernel
def T12aaaabba : Tree := .node [24,113184,430348,902208,3227782,5521457,7684279,8532035,13501056,15731968] T12aaaabbaa T12aaaabbab
theorem T12aaaabba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaaabba = true :=
  tall_node _ _ _ _ T12aaaabbaa_ok (by decide +kernel) T12aaaabbab_ok
def T12aaaabbb : Tree := (.node [48,113184,430348,902208,3227782,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12aaaabbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaaabbb = true := by decide +kernel
def T12aaaabb : Tree := .node [24,113184,430348,902208,3227782,5521457,8532035,13501056,15731968] T12aaaabba T12aaaabbb
theorem T12aaaabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaaabb = true :=
  tall_node _ _ _ _ T12aaaabba_ok (by decide +kernel) T12aaaabbb_ok
def T12aaaab : Tree := .node [16,113184,430348,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731968] T12aaaaba T12aaaabb
theorem T12aaaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaaab = true :=
  tall_node _ _ _ _ T12aaaaba_ok (by decide +kernel) T12aaaabb_ok
def T12aaaa : Tree := .node [8,113184,430348,902208,1037644,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12aaaaa T12aaaab
theorem T12aaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaaa = true :=
  tall_node _ _ _ _ T12aaaaa_ok (by decide +kernel) T12aaaab_ok
def T12aaabaaa : Tree := (.node [64,113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [64,113184,113248,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) .nil)
theorem T12aaabaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaabaaa = true := by decide +kernel
def T12aaabaaba : Tree := (.node [64,113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15732032] .nil .nil)
theorem T12aaabaaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaabaaba = true := by decide +kernel
def T12aaabaabb : Tree := .nil
theorem T12aaabaabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaabaabb = true := by decide +kernel
def T12aaabaab : Tree := .node [64,113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501120,15731968] T12aaabaaba T12aaabaabb
theorem T12aaabaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaabaab = true :=
  tall_node _ _ _ _ T12aaabaaba_ok (by decide +kernel) T12aaabaabb_ok
def T12aaabaa : Tree := .node [64,113184,430348,506668,902208,3227782,5521457,8532035,11083800,13501056,15731968] T12aaabaaa T12aaabaab
theorem T12aaabaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaabaa = true :=
  tall_node _ _ _ _ T12aaabaaa_ok (by decide +kernel) T12aaabaab_ok
def T12aaababaa : Tree := (.node [64,113184,430348,902208,3227782,5521521,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12aaababaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaababaa = true := by decide +kernel
def T12aaababab : Tree := .nil
theorem T12aaababab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaababab = true := by decide +kernel
def T12aaababa : Tree := .node [64,113184,430348,902208,3227782,5689661,7684279,8532035,11083800,13501056,15731968] T12aaababaa T12aaababab
theorem T12aaababa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaababa = true :=
  tall_node _ _ _ _ T12aaababaa_ok (by decide +kernel) T12aaababab_ok
def T12aaababb : Tree := (.node [64,113184,430412,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12aaababb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaababb = true := by decide +kernel
def T12aaabab : Tree := .node [64,113184,430348,917088,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12aaababa T12aaababb
theorem T12aaabab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaabab = true :=
  tall_node _ _ _ _ T12aaababa_ok (by decide +kernel) T12aaababb_ok
def T12aaaba : Tree := .node [64,113184,430348,902208,3227782,5521457,7684343,8532035,11083800,13501056,15731968] T12aaabaa T12aaabab
theorem T12aaaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaaba = true :=
  tall_node _ _ _ _ T12aaabaa_ok (by decide +kernel) T12aaabab_ok
def T12aaabbaaa : Tree := (.node [67,113184,430348,902208,3227782,5521457,7684279,8242423,11083800,13501056,15731968] .nil .nil)
theorem T12aaabbaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaabbaaa = true := by decide +kernel
def T12aaabbaab : Tree := .nil
theorem T12aaabbaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaabbaab = true := by decide +kernel
def T12aaabbaa : Tree := .node [67,113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12aaabbaaa T12aaabbaab
theorem T12aaabbaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaabbaa = true :=
  tall_node _ _ _ _ T12aaabbaaa_ok (by decide +kernel) T12aaabbaab_ok
def T12aaabbaba : Tree := (.node [67,113184,430348,902208,3227782,5521457,11083800,13501056,15731968] .nil .nil)
theorem T12aaabbaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaabbaba = true := by decide +kernel
def T12aaabbabb : Tree := .nil
theorem T12aaabbabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaabbabb = true := by decide +kernel
def T12aaabbab : Tree := .node [256,113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12aaabbaba T12aaabbabb
theorem T12aaabbab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaabbab = true :=
  tall_node _ _ _ _ T12aaabbaba_ok (by decide +kernel) T12aaabbabb_ok
def T12aaabba : Tree := .node [67,113184,430348,902208,3227782,5521457,7684279,11083800,13501056,15731968] T12aaabbaa T12aaabbab
theorem T12aaabba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaabba = true :=
  tall_node _ _ _ _ T12aaabbaa_ok (by decide +kernel) T12aaabbab_ok
def T12aaabbbaa : Tree := (.node [264,113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12aaabbbaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaabbbaa = true := by decide +kernel
def T12aaabbbab : Tree := .nil
theorem T12aaabbbab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaabbbab = true := by decide +kernel
def T12aaabbba : Tree := .node [1024,113184,114208,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12aaabbbaa T12aaabbbab
theorem T12aaabbba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaabbba = true :=
  tall_node _ _ _ _ T12aaabbbaa_ok (by decide +kernel) T12aaabbbab_ok
def T12aaabbbb : Tree := (.node [1024,113184,430348,506668,902208,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12aaabbbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaabbbb = true := by decide +kernel
def T12aaabbb : Tree := .node [1024,113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12aaabbba T12aaabbbb
theorem T12aaabbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaabbb = true :=
  tall_node _ _ _ _ T12aaabbba_ok (by decide +kernel) T12aaabbbb_ok
def T12aaabb : Tree := .node [260,113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12aaabba T12aaabbb
theorem T12aaabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaabb = true :=
  tall_node _ _ _ _ T12aaabba_ok (by decide +kernel) T12aaabbb_ok
def T12aaab : Tree := .node [65,113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12aaaba T12aaabb
theorem T12aaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaab = true :=
  tall_node _ _ _ _ T12aaaba_ok (by decide +kernel) T12aaabb_ok
def T12aaa : Tree := .node [64,1024,113184,430348,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12aaaa T12aaab
theorem T12aaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaa = true :=
  tall_node _ _ _ _ T12aaaa_ok (by decide +kernel) T12aaab_ok
def T12aabaaaaa : Tree := (.node [1024,113184,430348,902208,3227782,5521457,7684279,8533059,11083800,13501056,15731968] .nil .nil)
theorem T12aabaaaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabaaaaa = true := by decide +kernel
def T12aabaaaab : Tree := .nil
theorem T12aabaaaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabaaaab = true := by decide +kernel
def T12aabaaaa : Tree := .node [1024,113184,430348,902208,3227782,5521457,7685303,8532035,11083800,13501056,15731968] T12aabaaaaa T12aabaaaab
theorem T12aabaaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabaaaa = true :=
  tall_node _ _ _ _ T12aabaaaaa_ok (by decide +kernel) T12aabaaaab_ok
def T12aabaaaba : Tree := (.node [1024,113184,430348,3227782,4048070,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12aabaaaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabaaaba = true := by decide +kernel
def T12aabaaabb : Tree := .nil
theorem T12aabaaabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabaaabb = true := by decide +kernel
def T12aabaaab : Tree := .node [1024,113184,430348,3227782,5521457,7684279,8242423,8532035,11083800,13501056,15731968] T12aabaaaba T12aabaaabb
theorem T12aabaaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabaaab = true :=
  tall_node _ _ _ _ T12aabaaaba_ok (by decide +kernel) T12aabaaabb_ok
def T12aabaaa : Tree := .node [1024,113184,430348,902208,3227782,5522481,7684279,8532035,11083800,13501056,15731968] T12aabaaaa T12aabaaab
theorem T12aabaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabaaa = true :=
  tall_node _ _ _ _ T12aabaaaa_ok (by decide +kernel) T12aabaaab_ok
def T12aabaabaa : Tree := (.node [1088,113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12aabaabaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabaabaa = true := by decide +kernel
def T12aabaabab : Tree := .nil
theorem T12aabaabab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabaabab = true := by decide +kernel
def T12aabaaba : Tree := .node [1088,113184,430348,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12aabaabaa T12aabaabab
theorem T12aabaaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabaaba = true :=
  tall_node _ _ _ _ T12aabaabaa_ok (by decide +kernel) T12aabaabab_ok
def T12aabaabb : Tree := (.node [1088,113184,430348,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12aabaabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabaabb = true := by decide +kernel
def T12aabaab : Tree := .node [1088,113184,430348,3227782,5521457,7684279,8532035,11083800,13501056,15731968,15875395] T12aabaaba T12aabaabb
theorem T12aabaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabaab = true :=
  tall_node _ _ _ _ T12aabaaba_ok (by decide +kernel) T12aabaabb_ok
def T12aabaa : Tree := .node [1024,113184,431372,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12aabaaa T12aabaab
theorem T12aabaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabaa = true :=
  tall_node _ _ _ _ T12aabaaa_ok (by decide +kernel) T12aabaab_ok
def T12aababaa : Tree := (.node [12288,113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [2304,113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) .nil)
theorem T12aababaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aababaa = true := by decide +kernel
def T12aababab : Tree := (.node [65540,113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [65536,113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) .nil)
theorem T12aababab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aababab = true := by decide +kernel
def T12aababa : Tree := .node [36864,113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12aababaa T12aababab
theorem T12aababa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aababa = true :=
  tall_node _ _ _ _ T12aababaa_ok (by decide +kernel) T12aababab_ok
def T12aababbaa : Tree := (.node [65568,113184,430348,902208,917088,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12aababbaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aababbaa = true := by decide +kernel
def T12aababbab : Tree := .nil
theorem T12aababbab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aababbab = true := by decide +kernel
def T12aababba : Tree := .node [65571,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] T12aababbaa T12aababbab
theorem T12aababba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aababba = true :=
  tall_node _ _ _ _ T12aababbaa_ok (by decide +kernel) T12aababbab_ok
def T12aababbb : Tree := (.node [67616,113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12aababbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aababbb = true := by decide +kernel
def T12aababb : Tree := .node [66080,113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12aababba T12aababbb
theorem T12aababb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aababb = true :=
  tall_node _ _ _ _ T12aababba_ok (by decide +kernel) T12aababbb_ok
def T12aabab : Tree := .node [65568,113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12aababa T12aababb
theorem T12aabab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabab = true :=
  tall_node _ _ _ _ T12aababa_ok (by decide +kernel) T12aababb_ok
def T12aaba : Tree := .node [1280,113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12aabaa T12aabab
theorem T12aaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aaba = true :=
  tall_node _ _ _ _ T12aabaa_ok (by decide +kernel) T12aabab_ok
def T12aabbaaa : Tree := (.node [73736,113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [73728,113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) .nil)
theorem T12aabbaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabbaaa = true := by decide +kernel
def T12aabbaaba : Tree := (.node [81984,113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12aabbaaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabbaaba = true := by decide +kernel
def T12aabbaabb : Tree := .nil
theorem T12aabbaabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabbaabb = true := by decide +kernel
def T12aabbaab : Tree := .node [82944,113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12aabbaaba T12aabbaabb
theorem T12aabbaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabbaab = true :=
  tall_node _ _ _ _ T12aabbaaba_ok (by decide +kernel) T12aabbaabb_ok
def T12aabbaa : Tree := .node [81920,113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12aabbaaa T12aabbaab
theorem T12aabbaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabbaa = true :=
  tall_node _ _ _ _ T12aabbaaa_ok (by decide +kernel) T12aabbaab_ok
def T12aabbabaa : Tree := (.node [98368,113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12aabbabaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabbabaa = true := by decide +kernel
def T12aabbabab : Tree := .nil
theorem T12aabbabab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabbabab = true := by decide +kernel
def T12aabbaba : Tree := .node [99328,113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12aabbabaa T12aabbabab
theorem T12aabbaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabbaba = true :=
  tall_node _ _ _ _ T12aabbabaa_ok (by decide +kernel) T12aabbabab_ok
def T12aabbabb : Tree := (.node [113184,113186,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12aabbabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabbabb = true := by decide +kernel
def T12aabbab : Tree := .node [113184,113185,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12aabbaba T12aabbabb
theorem T12aabbab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabbab = true :=
  tall_node _ _ _ _ T12aabbaba_ok (by decide +kernel) T12aabbabb_ok
def T12aabba : Tree := .node [98304,113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12aabbaa T12aabbab
theorem T12aabba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabba = true :=
  tall_node _ _ _ _ T12aabbaa_ok (by decide +kernel) T12aabbab_ok
def T12aabbbaaa : Tree := (.node [113184,113187,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12aabbbaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabbbaaa = true := by decide +kernel
def T12aabbbaab : Tree := .nil
theorem T12aabbbaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabbbaab = true := by decide +kernel
def T12aabbbaa : Tree := .node [113184,113188,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12aabbbaaa T12aabbbaab
theorem T12aabbbaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabbbaa = true :=
  tall_node _ _ _ _ T12aabbbaaa_ok (by decide +kernel) T12aabbbaab_ok
def T12aabbbaba : Tree := (.node [113184,113200,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12aabbbaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabbbaba = true := by decide +kernel
def T12aabbbabb : Tree := .nil
theorem T12aabbbabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabbbabb = true := by decide +kernel
def T12aabbbab : Tree := .node [113184,113200,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] T12aabbbaba T12aabbbabb
theorem T12aabbbab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabbbab = true :=
  tall_node _ _ _ _ T12aabbbaba_ok (by decide +kernel) T12aabbbabb_ok
def T12aabbba : Tree := .node [113184,113192,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12aabbbaa T12aabbbab
theorem T12aabbba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabbba = true :=
  tall_node _ _ _ _ T12aabbbaa_ok (by decide +kernel) T12aabbbab_ok
def T12aabbbbaa : Tree := (.node [113184,113312,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12aabbbbaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabbbbaa = true := by decide +kernel
def T12aabbbbab : Tree := .nil
theorem T12aabbbbab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabbbbab = true := by decide +kernel
def T12aabbbba : Tree := .node [113184,113440,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12aabbbbaa T12aabbbbab
theorem T12aabbbba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabbbba = true :=
  tall_node _ _ _ _ T12aabbbbaa_ok (by decide +kernel) T12aabbbbab_ok
def T12aabbbbb : Tree := (.node [113184,114208,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12aabbbbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabbbbb = true := by decide +kernel
def T12aabbbb : Tree := .node [113184,114208,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12aabbbba T12aabbbbb
theorem T12aabbbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabbbb = true :=
  tall_node _ _ _ _ T12aabbbba_ok (by decide +kernel) T12aabbbbb_ok
def T12aabbb : Tree := .node [113184,113248,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12aabbba T12aabbbb
theorem T12aabbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabbb = true :=
  tall_node _ _ _ _ T12aabbba_ok (by decide +kernel) T12aabbbb_ok
def T12aabb : Tree := .node [113184,113187,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12aabba T12aabbb
theorem T12aabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aabb = true :=
  tall_node _ _ _ _ T12aabba_ok (by decide +kernel) T12aabbb_ok
def T12aab : Tree := .node [67616,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16076215] T12aaba T12aabb
theorem T12aab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aab = true :=
  tall_node _ _ _ _ T12aaba_ok (by decide +kernel) T12aabb_ok
def T12aa : Tree := .node [1024,113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13502080,15731968] T12aaa T12aab
theorem T12aa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aa = true :=
  tall_node _ _ _ _ T12aaa_ok (by decide +kernel) T12aab_ok
def T12abaaaaaa : Tree := (.node [113184,143360,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12abaaaaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abaaaaaa = true := by decide +kernel
def T12abaaaaab : Tree := .nil
theorem T12abaaaaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abaaaaab = true := by decide +kernel
def T12abaaaaa : Tree := .node [113184,244256,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12abaaaaaa T12abaaaaab
theorem T12abaaaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abaaaaa = true :=
  tall_node _ _ _ _ T12abaaaaaa_ok (by decide +kernel) T12abaaaaab_ok
def T12abaaaab : Tree := (.node [113184,344128,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,344064,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) .nil)
theorem T12abaaaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abaaaab = true := by decide +kernel
def T12abaaaa : Tree := .node [113184,327716,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12abaaaaa T12abaaaab
theorem T12abaaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abaaaa = true :=
  tall_node _ _ _ _ T12abaaaaa_ok (by decide +kernel) T12abaaaab_ok
def T12abaaaba : Tree := (.node [113184,375328,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,360448,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) .nil)
theorem T12abaaaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abaaaba = true := by decide +kernel
def T12abaaabb : Tree := (.node [113184,430348,504076,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12abaaabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abaaabb = true := by decide +kernel
def T12abaaab : Tree := .node [113184,375332,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12abaaaba T12abaaabb
theorem T12abaaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abaaab = true :=
  tall_node _ _ _ _ T12abaaaba_ok (by decide +kernel) T12abaaabb_ok
def T12abaaa : Tree := .node [113184,345088,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12abaaaa T12abaaab
theorem T12abaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abaaa = true :=
  tall_node _ _ _ _ T12abaaaa_ok (by decide +kernel) T12abaaab_ok
def T12abaabaa : Tree := (.node [113184,430348,506668,902208,917088,3227782,5521457,8532035,11083800,13501056,15731968] (.node [113184,430348,506668,902208,917088,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) .nil)
theorem T12abaabaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abaabaa = true := by decide +kernel
def T12abaabab : Tree := (.node [113184,430348,506668,902208,1064960,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,506668,902208,1048428,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil) .nil)
theorem T12abaabab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abaabab = true := by decide +kernel
def T12abaaba : Tree := .node [113184,430348,506668,902208,1048428,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12abaabaa T12abaabab
theorem T12abaaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abaaba = true :=
  tall_node _ _ _ _ T12abaabaa_ok (by decide +kernel) T12abaabab_ok
def T12abaabba : Tree := (.node [113184,430348,506668,902208,3145728,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,506668,902208,2162704,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) .nil)
theorem T12abaabba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abaabba = true := by decide +kernel
def T12abaabbb : Tree := (.node [113184,430348,506668,902208,3227782,3658126,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12abaabbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abaabbb = true := by decide +kernel
def T12abaabb : Tree := .node [113184,430348,506668,902208,3227782,3275430,5521457,7684279,8532035,11083800,13501056,15731968] T12abaabba T12abaabbb
theorem T12abaabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abaabb = true :=
  tall_node _ _ _ _ T12abaabba_ok (by decide +kernel) T12abaabbb_ok
def T12abaab : Tree := .node [113184,430348,506668,902208,2162688,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12abaaba T12abaabb
theorem T12abaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abaab = true :=
  tall_node _ _ _ _ T12abaaba_ok (by decide +kernel) T12abaabb_ok
def T12abaa : Tree := .node [113184,430348,506668,589824,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12abaaa T12abaab
theorem T12abaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abaa = true :=
  tall_node _ _ _ _ T12abaaa_ok (by decide +kernel) T12abaab_ok
def T12ababaaaa : Tree := (.node [113184,430348,506668,902208,3227782,4048070,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12ababaaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12ababaaaa = true := by decide +kernel
def T12ababaaab : Tree := .nil
theorem T12ababaaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12ababaaab = true := by decide +kernel
def T12ababaaa : Tree := .node [113184,430348,506668,902208,3227782,4048070,5521457,8532035,11083800,13501056,15731968] T12ababaaaa T12ababaaab
theorem T12ababaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12ababaaa = true :=
  tall_node _ _ _ _ T12ababaaaa_ok (by decide +kernel) T12ababaaab_ok
def T12ababaab : Tree := (.node [113184,430348,506668,902208,3227782,5521457,7684279,7863231,8532035,11083800,13501056,15731968] (.node [113184,430348,506668,902208,3227782,5521457,7684279,7731895,8532035,11083800,13501056,15731968] .nil .nil) .nil)
theorem T12ababaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12ababaab = true := by decide +kernel
def T12ababaa : Tree := .node [113184,430348,506668,902208,3227782,5521457,7340032,7684279,8532035,11083800,13501056,15731968] T12ababaaa T12ababaab
theorem T12ababaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12ababaa = true :=
  tall_node _ _ _ _ T12ababaaa_ok (by decide +kernel) T12ababaab_ok
def T12abababa : Tree := (.node [113184,430348,506668,902208,3227782,5521457,7684279,8396800,8532035,11083800,13501056,15731968] (.node [113184,430348,506668,902208,3227782,5521457,7684279,8388608,8532035,11083800,13501056,15731968] .nil .nil) .nil)
theorem T12abababa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abababa = true := by decide +kernel
def T12abababb : Tree := (.node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,8895343,11083800,13501056,15731968] .nil .nil)
theorem T12abababb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abababb = true := by decide +kernel
def T12ababab : Tree := .node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,8632931,11083800,13501056,15731968] T12abababa T12abababb
theorem T12ababab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12ababab = true :=
  tall_node _ _ _ _ T12abababa_ok (by decide +kernel) T12abababb_ok
def T12ababa : Tree := .node [113184,430348,506668,902208,3227782,5521457,7684279,8242423,8532035,11083800,13501056,15731968] T12ababaa T12ababab
theorem T12ababa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12ababa = true :=
  tall_node _ _ _ _ T12ababaa_ok (by decide +kernel) T12ababab_ok
def T12ababbaa : Tree := (.node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,10485760,11083800,13501056,15731968] (.node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,9434179,11083800,13501056,15731968] .nil .nil) .nil)
theorem T12ababbaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12ababbaa = true := by decide +kernel
def T12ababbab : Tree := (.node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,11396184,13501056,15731968] (.node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,11219035,13501056,15731968] .nil .nil) .nil)
theorem T12ababbab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12ababbab = true := by decide +kernel
def T12ababba : Tree := .node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,11123256,13501056,15731968] T12ababbaa T12ababbab
theorem T12ababba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12ababba = true :=
  tall_node _ _ _ _ T12ababbaa_ok (by decide +kernel) T12ababbab_ok
def T12ababbba : Tree := (.node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,11759815,13501056,15731968] (.node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,11516732,13501056,15731968] .nil .nil) .nil)
theorem T12ababbba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12ababbba = true := by decide +kernel
def T12ababbbb : Tree := (.node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15671960,15731968] .nil .nil)
theorem T12ababbbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12ababbbb = true := by decide +kernel
def T12ababbb : Tree := .node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,12148894,13501056,15731968] T12ababbba T12ababbbb
theorem T12ababbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12ababbb = true :=
  tall_node _ _ _ _ T12ababbba_ok (by decide +kernel) T12ababbbb_ok
def T12ababb : Tree := .node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,11514140,13501056,15731968] T12ababba T12ababbb
theorem T12ababb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12ababb = true :=
  tall_node _ _ _ _ T12ababba_ok (by decide +kernel) T12ababbb_ok
def T12abab : Tree := .node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,8912896,11083800,13501056,15731968] T12ababa T12ababb
theorem T12abab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abab = true :=
  tall_node _ _ _ _ T12ababa_ok (by decide +kernel) T12ababb_ok
def T12aba : Tree := .node [113184,430348,506668,902208,3227782,3668910,5521457,7684279,8532035,11083800,13501056,15731968] T12abaa T12abab
theorem T12aba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12aba = true :=
  tall_node _ _ _ _ T12abaa_ok (by decide +kernel) T12abab_ok
def T12abbaaaa : Tree := (.node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,15875395] (.node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,15843104] .nil .nil) .nil)
theorem T12abbaaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbaaaa = true := by decide +kernel
def T12abbaaab : Tree := (.node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,16236332] (.node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,16216311] .nil .nil) .nil)
theorem T12abbaaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbaaab = true := by decide +kernel
def T12abbaaa : Tree := .node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,16076215] T12abbaaaa T12abbaaab
theorem T12abbaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbaaa = true :=
  tall_node _ _ _ _ T12abbaaaa_ok (by decide +kernel) T12abbaaab_ok
def T12abbaaba : Tree := (.node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,16605375] (.node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,16605241] .nil .nil) .nil)
theorem T12abbaaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbaaba = true := by decide +kernel
def T12abbaabb : Tree := (.node [113184,430348,506668,902208,3227782,5521457,8242423,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12abbaabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbaabb = true := by decide +kernel
def T12abbaab : Tree := .node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,16633152] T12abbaaba T12abbaabb
theorem T12abbaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbaab = true :=
  tall_node _ _ _ _ T12abbaaba_ok (by decide +kernel) T12abbaabb_ok
def T12abbaa : Tree := .node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,16330008] T12abbaaa T12abbaab
theorem T12abbaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbaa = true :=
  tall_node _ _ _ _ T12abbaaa_ok (by decide +kernel) T12abbaab_ok
def T12abbabaaa : Tree := (.node [113184,430348,506668,902208,3227782,5521457,8532035,11083800,13501056,15731968,15875395] .nil .nil)
theorem T12abbabaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbabaaa = true := by decide +kernel
def T12abbabaab : Tree := .nil
theorem T12abbabaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbabaab = true := by decide +kernel
def T12abbabaa : Tree := .node [113184,430348,506668,902208,3227782,5521457,8532035,11083800,13501056,15731968,16076215] T12abbabaaa T12abbabaab
theorem T12abbabaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbabaa = true :=
  tall_node _ _ _ _ T12abbabaaa_ok (by decide +kernel) T12abbabaab_ok
def T12abbababa : Tree := (.node [113184,430348,506668,902208,3227782,7684279,8532035,11083800,13501056,14053491,15731968] .nil .nil)
theorem T12abbababa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbababa = true := by decide +kernel
def T12abbababb : Tree := .nil
theorem T12abbababb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbababb = true := by decide +kernel
def T12abbabab : Tree := .node [113184,430348,506668,902208,3227782,7684279,8532035,11083800,13501056,14566065,15731968] T12abbababa T12abbababb
theorem T12abbabab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbabab = true :=
  tall_node _ _ _ _ T12abbababa_ok (by decide +kernel) T12abbababb_ok
def T12abbaba : Tree := .node [113184,430348,506668,902208,3227782,5689661,7684279,8532035,11083800,13501056,15731968] T12abbabaa T12abbabab
theorem T12abbaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbaba = true :=
  tall_node _ _ _ _ T12abbabaa_ok (by decide +kernel) T12abbabab_ok
def T12abbabbaa : Tree := (.node [113184,430348,589888,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12abbabbaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbabbaa = true := by decide +kernel
def T12abbabbab : Tree := .nil
theorem T12abbabbab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbabbab = true := by decide +kernel
def T12abbabba : Tree := .node [113184,430348,590848,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12abbabbaa T12abbabbab
theorem T12abbabba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbabba = true :=
  tall_node _ _ _ _ T12abbabbaa_ok (by decide +kernel) T12abbabbab_ok
def T12abbabbb : Tree := (.node [113184,430348,899616,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12abbabbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbabbb = true := by decide +kernel
def T12abbabb : Tree := .node [113184,430348,637472,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12abbabba T12abbabbb
theorem T12abbabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbabb = true :=
  tall_node _ _ _ _ T12abbabba_ok (by decide +kernel) T12abbabbb_ok
def T12abbab : Tree := .node [113184,430348,589832,902208,1037644,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12abbaba T12abbabb
theorem T12abbab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbab = true :=
  tall_node _ _ _ _ T12abbaba_ok (by decide +kernel) T12abbabb_ok
def T12abba : Tree := .node [113184,430348,506668,902208,3227782,5521457,8532035,11083800,13501056,15731968,15814022] T12abbaa T12abbab
theorem T12abba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abba = true :=
  tall_node _ _ _ _ T12abbaa_ok (by decide +kernel) T12abbab_ok
def T12abbbaaaa : Tree := (.node [113184,430348,902208,902211,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12abbbaaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbbaaaa = true := by decide +kernel
def T12abbbaaab : Tree := .nil
theorem T12abbbaaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbbaaab = true := by decide +kernel
def T12abbbaaa : Tree := .node [113184,430348,902208,902212,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12abbbaaaa T12abbbaaab
theorem T12abbbaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbbaaa = true :=
  tall_node _ _ _ _ T12abbbaaaa_ok (by decide +kernel) T12abbbaaab_ok
def T12abbbaaba : Tree := (.node [113184,430348,902208,902224,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12abbbaaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbbaaba = true := by decide +kernel
def T12abbbaabb : Tree := .nil
theorem T12abbbaabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbbaabb = true := by decide +kernel
def T12abbbaab : Tree := .node [113184,430348,902208,902464,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12abbbaaba T12abbbaabb
theorem T12abbbaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbbaab = true :=
  tall_node _ _ _ _ T12abbbaaba_ok (by decide +kernel) T12abbbaabb_ok
def T12abbbaa : Tree := .node [113184,430348,902208,902216,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12abbbaaa T12abbbaab
theorem T12abbbaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbbaa = true :=
  tall_node _ _ _ _ T12abbbaaa_ok (by decide +kernel) T12abbbaab_ok
def T12abbbabaa : Tree := (.node [113184,430348,902208,910400,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12abbbabaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbbabaa = true := by decide +kernel
def T12abbbabab : Tree := .nil
theorem T12abbbabab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbbabab = true := by decide +kernel
def T12abbbaba : Tree := .node [113184,430348,902208,914496,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12abbbabaa T12abbbabab
theorem T12abbbaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbbaba = true :=
  tall_node _ _ _ _ T12abbbabaa_ok (by decide +kernel) T12abbbabab_ok
def T12abbbabb : Tree := (.node [113184,430348,902208,917088,3227782,4456576,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12abbbabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbbabb = true := by decide +kernel
def T12abbbab : Tree := .node [113184,430348,902208,917088,3227782,3275430,5521457,7684279,8532035,11083800,13501056,15731968] T12abbbaba T12abbbabb
theorem T12abbbab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbbab = true :=
  tall_node _ _ _ _ T12abbbaba_ok (by decide +kernel) T12abbbabb_ok
def T12abbba : Tree := .node [113184,430348,902208,906304,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12abbbaa T12abbbab
theorem T12abbba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbba = true :=
  tall_node _ _ _ _ T12abbbaa_ok (by decide +kernel) T12abbbab_ok
def T12abbbbaa : Tree := (.node [113184,430348,902208,917088,3227782,5521457,7684279,8532035,11083800,13501056,13513411,15731968] (.node [113184,430348,902208,917088,3227782,5521457,7684279,8532035,11083800,11123256,13501056,15731968] .nil .nil) .nil)
theorem T12abbbbaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbbbaa = true := by decide +kernel
def T12abbbbab : Tree := (.node [113184,430348,902208,917088,3227782,5521457,7684279,8532035,11083800,13501056,14566065,15731968] (.node [113184,430348,902208,917088,3227782,5521457,7684279,8532035,11083800,13501056,13613728,15731968] .nil .nil) .nil)
theorem T12abbbbab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbbbab = true := by decide +kernel
def T12abbbba : Tree := .node [113184,430348,902208,917088,3227782,5521457,7684279,8532035,11083800,13501056,13538188,15731968] T12abbbbaa T12abbbbab
theorem T12abbbba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbbba = true :=
  tall_node _ _ _ _ T12abbbbaa_ok (by decide +kernel) T12abbbbab_ok
def T12abbbbba : Tree := (.node [113184,430348,902208,917088,3227782,5521457,7684279,8532035,11083800,13501056,15731968,16650112] (.node [113184,430348,902208,917088,3227782,5521457,7684279,8532035,11083800,13501056,15731968,15843104] .nil .nil) .nil)
theorem T12abbbbba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbbbba = true := by decide +kernel
def T12abbbbbb : Tree := (.node [113184,430348,902208,917088,3227782,7684279,8532035,11083800,13501056,14566065,15731968] .nil .nil)
theorem T12abbbbbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbbbbb = true := by decide +kernel
def T12abbbbb : Tree := .node [113184,430348,902208,917088,3227782,5521457,8532035,11083800,13501056,13513411,15731968] T12abbbbba T12abbbbbb
theorem T12abbbbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbbbb = true :=
  tall_node _ _ _ _ T12abbbbba_ok (by decide +kernel) T12abbbbbb_ok
def T12abbbb : Tree := .node [113184,430348,902208,917088,3227782,5521457,7684279,8532035,11083800,13501056,15671960,15731968] T12abbbba T12abbbbb
theorem T12abbbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbbb = true :=
  tall_node _ _ _ _ T12abbbba_ok (by decide +kernel) T12abbbbb_ok
def T12abbb : Tree := .node [113184,430348,902208,917088,3227782,5521457,7684279,8532035,8632931,11083800,13501056,15731968] T12abbba T12abbbb
theorem T12abbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abbb = true :=
  tall_node _ _ _ _ T12abbba_ok (by decide +kernel) T12abbbb_ok
def T12abb : Tree := .node [113184,430348,902208,902209,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12abba T12abbb
theorem T12abb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12abb = true :=
  tall_node _ _ _ _ T12abba_ok (by decide +kernel) T12abbb_ok
def T12ab : Tree := .node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,15814022] T12aba T12abb
theorem T12ab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12ab = true :=
  tall_node _ _ _ _ T12aba_ok (by decide +kernel) T12abb_ok
def T12a : Tree := .node [113184,129568,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12aa T12ab
theorem T12a_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12a = true :=
  tall_node _ _ _ _ T12aa_ok (by decide +kernel) T12ab_ok
def T12baaaaaaa : Tree := (.node [113184,430348,902208,917088,5521457,7684279,8532035,11083800,11759815,13501056,15731968] .nil .nil)
theorem T12baaaaaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baaaaaaa = true := by decide +kernel
def T12baaaaaab : Tree := .nil
theorem T12baaaaaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baaaaaab = true := by decide +kernel
def T12baaaaaa : Tree := .node [113184,430348,902208,1048428,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12baaaaaaa T12baaaaaab
theorem T12baaaaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baaaaaa = true :=
  tall_node _ _ _ _ T12baaaaaaa_ok (by decide +kernel) T12baaaaaab_ok
def T12baaaaaba : Tree := (.node [113184,430348,902208,2162704,3227782,5521457,8532035,8632931,11083800,13501056,15731968] .nil .nil)
theorem T12baaaaaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baaaaaba = true := by decide +kernel
def T12baaaaabb : Tree := .nil
theorem T12baaaaabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baaaaabb = true := by decide +kernel
def T12baaaaab : Tree := .node [113184,430348,902208,2162704,3227782,5521457,8532035,11083800,13501056,15731968,15814022] T12baaaaaba T12baaaaabb
theorem T12baaaaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baaaaab = true :=
  tall_node _ _ _ _ T12baaaaaba_ok (by decide +kernel) T12baaaaabb_ok
def T12baaaaa : Tree := .node [113184,430348,902208,1950784,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12baaaaaa T12baaaaab
theorem T12baaaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baaaaa = true :=
  tall_node _ _ _ _ T12baaaaaa_ok (by decide +kernel) T12baaaaab_ok
def T12baaaabaa : Tree := (.node [113184,430348,902208,2210336,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12baaaabaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baaaabaa = true := by decide +kernel
def T12baaaabab : Tree := .nil
theorem T12baaaabab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baaaabab = true := by decide +kernel
def T12baaaaba : Tree := .node [113184,430348,902208,2210352,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12baaaabaa T12baaaabab
theorem T12baaaaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baaaaba = true :=
  tall_node _ _ _ _ T12baaaabaa_ok (by decide +kernel) T12baaaabab_ok
def T12baaaabb : Tree := (.node [113184,430348,902208,2999360,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12baaaabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baaaabb = true := by decide +kernel
def T12baaaab : Tree := .node [113184,430348,902208,2210352,3227782,5521457,8532035,11083800,13501056,15731968] T12baaaaba T12baaaabb
theorem T12baaaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baaaab = true :=
  tall_node _ _ _ _ T12baaaaba_ok (by decide +kernel) T12baaaabb_ok
def T12baaaa : Tree := .node [113184,430348,902208,2162712,3227782,5521457,7684279,8532035,13501056,15731968] T12baaaaa T12baaaab
theorem T12baaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baaaa = true :=
  tall_node _ _ _ _ T12baaaaa_ok (by decide +kernel) T12baaaab_ok
def T12baaabaaa : Tree := (.node [113184,430348,902208,3227782,3227790,5521457,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12baaabaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baaabaaa = true := by decide +kernel
def T12baaabaab : Tree := .nil
theorem T12baaabaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baaabaab = true := by decide +kernel
def T12baaabaa : Tree := .node [113184,430348,902208,3227782,3227846,5521457,7684279,8532035,11083800,13501056,15731968] T12baaabaaa T12baaabaab
theorem T12baaabaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baaabaa = true :=
  tall_node _ _ _ _ T12baaabaaa_ok (by decide +kernel) T12baaabaab_ok
def T12baaababa : Tree := (.node [113184,430348,902208,3227782,3275430,5521457,5689661,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12baaababa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baaababa = true := by decide +kernel
def T12baaababb : Tree := .nil
theorem T12baaababb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baaababb = true := by decide +kernel
def T12baaabab : Tree := .node [113184,430348,902208,3227782,3275430,5521457,8532035,8827215,11083800,13501056,15731968] T12baaababa T12baaababb
theorem T12baaabab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baaabab = true :=
  tall_node _ _ _ _ T12baaababa_ok (by decide +kernel) T12baaababb_ok
def T12baaaba : Tree := .node [113184,430348,902208,3227782,3227846,5521457,8532035,11083800,13501056,15731968] T12baaabaa T12baaabab
theorem T12baaaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baaaba = true :=
  tall_node _ _ _ _ T12baaabaa_ok (by decide +kernel) T12baaabab_ok
def T12baaabbaa : Tree := (.node [113184,430348,902208,3227782,3275430,5521457,8532035,11083800,13501056,15731968,16010545] .nil .nil)
theorem T12baaabbaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baaabbaa = true := by decide +kernel
def T12baaabbab : Tree := .nil
theorem T12baaabbab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baaabbab = true := by decide +kernel
def T12baaabba : Tree := .node [113184,430348,902208,3227782,4047936,5521457,7684279,8532035,11083800,13501056,15731968] T12baaabbaa T12baaabbab
theorem T12baaabba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baaabba = true :=
  tall_node _ _ _ _ T12baaabbaa_ok (by decide +kernel) T12baaabbab_ok
def T12baaabbb : Tree := (.node [113184,430348,902208,3227782,4048070,5521457,8532035,11083800,13501056,15731968,16650112] .nil .nil)
theorem T12baaabbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baaabbb = true := by decide +kernel
def T12baaabb : Tree := .node [113184,430348,902208,3227782,4048070,5521457,7684279,8532035,11083800,13501056,15731968,16330008] T12baaabba T12baaabbb
theorem T12baaabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baaabb = true :=
  tall_node _ _ _ _ T12baaabba_ok (by decide +kernel) T12baaabbb_ok
def T12baaab : Tree := .node [113184,430348,902208,3227782,3275430,5521457,8532035,11083800,13501056,15731968,15875395] T12baaaba T12baaabb
theorem T12baaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baaab = true :=
  tall_node _ _ _ _ T12baaaba_ok (by decide +kernel) T12baaabb_ok
def T12baaa : Tree := .node [113184,430348,902208,2999376,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12baaaa T12baaab
theorem T12baaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baaa = true :=
  tall_node _ _ _ _ T12baaaa_ok (by decide +kernel) T12baaab_ok
def T12baabaaaa : Tree := (.node [113184,430348,902208,3227782,5521457,7684279,8242240,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12baabaaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baabaaaa = true := by decide +kernel
def T12baabaaab : Tree := .nil
theorem T12baabaaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baabaaab = true := by decide +kernel
def T12baabaaa : Tree := .node [113184,430348,902208,3227782,5521457,7684279,8242423,8532035,11083800,13501056,15731968] T12baabaaaa T12baabaaab
theorem T12baabaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baabaaa = true :=
  tall_node _ _ _ _ T12baabaaaa_ok (by decide +kernel) T12baabaaab_ok
def T12baabaaba : Tree := (.node [113184,430348,902208,3227782,5521457,7684279,8389632,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12baabaaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baabaaba = true := by decide +kernel
def T12baabaabb : Tree := .nil
theorem T12baabaabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baabaabb = true := by decide +kernel
def T12baabaab : Tree := .node [113184,430348,902208,3227782,5521457,7684279,8501792,8532035,11083800,13501056,15731968] T12baabaaba T12baabaabb
theorem T12baabaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baabaab = true :=
  tall_node _ _ _ _ T12baabaaba_ok (by decide +kernel) T12baabaabb_ok
def T12baabaa : Tree := .node [113184,430348,902208,3227782,5521457,7684279,8388672,8532035,11083800,13501056,15731968] T12baabaaa T12baabaab
theorem T12baabaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baabaa = true :=
  tall_node _ _ _ _ T12baabaaa_ok (by decide +kernel) T12baabaab_ok
def T12baababa : Tree := (.node [113184,430348,902208,3227782,5521457,7684279,8532035,8632931,8895343,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,7684279,8532035,8632931,8827215,11083800,13501056,15731968] .nil .nil) .nil)
theorem T12baababa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baababa = true := by decide +kernel
def T12baababb : Tree := (.node [113184,430348,902208,3227782,5521457,7684279,8532035,8632931,11083800,12148894,13501056,15731968] .nil .nil)
theorem T12baababb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baababb = true := by decide +kernel
def T12baabab : Tree := .node [113184,430348,902208,3227782,5521457,7684279,8532035,8632931,11083800,11514140,13501056,15731968] T12baababa T12baababb
theorem T12baabab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baabab = true :=
  tall_node _ _ _ _ T12baababa_ok (by decide +kernel) T12baababb_ok
def T12baaba : Tree := .node [113184,430348,902208,3227782,5521457,7684279,8532035,8533059,11083800,13501056,15731968] T12baabaa T12baabab
theorem T12baaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baaba = true :=
  tall_node _ _ _ _ T12baabaa_ok (by decide +kernel) T12baabab_ok
def T12baabbaa : Tree := (.node [113184,430348,902208,3227782,5521457,7684279,8532035,8632931,11083800,13501056,15731968,16076215] (.node [113184,430348,902208,3227782,5521457,7684279,8532035,8632931,11083800,13501056,15731968,16010545] .nil .nil) .nil)
theorem T12baabbaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baabbaa = true := by decide +kernel
def T12baabbaba : Tree := (.node [113184,430348,902208,3227782,5521457,7684279,8532035,8895343,11083800,13501056,15731968] .nil .nil)
theorem T12baabbaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baabbaba = true := by decide +kernel
def T12baabbabb : Tree := .nil
theorem T12baabbabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baabbabb = true := by decide +kernel
def T12baabbab : Tree := .node [113184,430348,902208,3227782,5521457,7684279,8532035,9290816,11083800,13501056,15731968] T12baabbaba T12baabbabb
theorem T12baabbab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baabbab = true :=
  tall_node _ _ _ _ T12baabbaba_ok (by decide +kernel) T12baabbabb_ok
def T12baabba : Tree := .node [113184,430348,902208,3227782,5521457,7684279,8532035,8632931,11083800,13501056,15731968,16633152] T12baabbaa T12baabbab
theorem T12baabba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baabba = true :=
  tall_node _ _ _ _ T12baabbaa_ok (by decide +kernel) T12baabbab_ok
def T12baabbbaa : Tree := (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,11084056,13501056,15731968] .nil .nil)
theorem T12baabbbaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baabbbaa = true := by decide +kernel
def T12baabbbab : Tree := .nil
theorem T12baabbbab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baabbbab = true := by decide +kernel
def T12baabbba : Tree := .node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,15732032] T12baabbbaa T12baabbbab
theorem T12baabbba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baabbba = true :=
  tall_node _ _ _ _ T12baabbbaa_ok (by decide +kernel) T12baabbbab_ok
def T12baabbbb : Tree := (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731969] .nil .nil)
theorem T12baabbbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baabbbb = true := by decide +kernel
def T12baabbb : Tree := .node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,16346526] T12baabbba T12baabbbb
theorem T12baabbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baabbb = true :=
  tall_node _ _ _ _ T12baabbba_ok (by decide +kernel) T12baabbbb_ok
def T12baabb : Tree := .node [113184,430348,902208,3227782,5521457,7684279,8532035,10916108,11083800,13501056,15731968] T12baabba T12baabbb
theorem T12baabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baabb = true :=
  tall_node _ _ _ _ T12baabba_ok (by decide +kernel) T12baabbb_ok
def T12baab : Tree := .node [113184,430348,902208,3227782,5521457,7684279,8532035,8632931,11083800,13501056,15731968,15814022] T12baaba T12baabb
theorem T12baab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baab = true :=
  tall_node _ _ _ _ T12baaba_ok (by decide +kernel) T12baabb_ok
def T12baa : Tree := .node [113184,430348,902208,3227782,5521457,7684279,7684343,8532035,11083800,13501056,15731968] T12baaa T12baab
theorem T12baa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baa = true :=
  tall_node _ _ _ _ T12baaa_ok (by decide +kernel) T12baab_ok
def T12babaaaaa : Tree := (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731972] .nil .nil)
theorem T12babaaaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babaaaaa = true := by decide +kernel
def T12babaaaab : Tree := .nil
theorem T12babaaaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babaaaab = true := by decide +kernel
def T12babaaaa : Tree := .node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731976] T12babaaaaa T12babaaaab
theorem T12babaaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babaaaa = true :=
  tall_node _ _ _ _ T12babaaaaa_ok (by decide +kernel) T12babaaaab_ok
def T12babaaaba : Tree := (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15732032] .nil .nil)
theorem T12babaaaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babaaaba = true := by decide +kernel
def T12babaaabb : Tree := .nil
theorem T12babaaabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babaaabb = true := by decide +kernel
def T12babaaab : Tree := .node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15814022,15875395] T12babaaaba T12babaaabb
theorem T12babaaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babaaab = true :=
  tall_node _ _ _ _ T12babaaaba_ok (by decide +kernel) T12babaaabb_ok
def T12babaaa : Tree := .node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731984] T12babaaaa T12babaaab
theorem T12babaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babaaa = true :=
  tall_node _ _ _ _ T12babaaaa_ok (by decide +kernel) T12babaaab_ok
def T12babaabaa : Tree := (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15875395,16633152] .nil .nil)
theorem T12babaabaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babaabaa = true := by decide +kernel
def T12babaabab : Tree := .nil
theorem T12babaabab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babaabab = true := by decide +kernel
def T12babaaba : Tree := .node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501057,15731968] T12babaabaa T12babaabab
theorem T12babaaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babaaba = true :=
  tall_node _ _ _ _ T12babaabaa_ok (by decide +kernel) T12babaabab_ok
def T12babaabb : Tree := (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501059,15731968] .nil .nil)
theorem T12babaabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babaabb = true := by decide +kernel
def T12babaab : Tree := .node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501058,15731968] T12babaaba T12babaabb
theorem T12babaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babaab = true :=
  tall_node _ _ _ _ T12babaaba_ok (by decide +kernel) T12babaabb_ok
def T12babaa : Tree := .node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15875395,16076215] T12babaaa T12babaab
theorem T12babaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babaa = true :=
  tall_node _ _ _ _ T12babaaa_ok (by decide +kernel) T12babaab_ok
def T12bababaaa : Tree := (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501064,15731968] .nil .nil)
theorem T12bababaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bababaaa = true := by decide +kernel
def T12bababaab : Tree := .nil
theorem T12bababaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bababaab = true := by decide +kernel
def T12bababaa : Tree := .node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501072,15731968] T12bababaaa T12bababaab
theorem T12bababaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bababaa = true :=
  tall_node _ _ _ _ T12bababaaa_ok (by decide +kernel) T12bababaab_ok
def T12babababa : Tree := (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501120,15731968] .nil .nil)
theorem T12babababa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babababa = true := by decide +kernel
def T12babababb : Tree := .nil
theorem T12babababb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babababb = true := by decide +kernel
def T12bababab : Tree := .node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501312,15731968] T12babababa T12babababb
theorem T12bababab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bababab = true :=
  tall_node _ _ _ _ T12babababa_ok (by decide +kernel) T12babababb_ok
def T12bababa : Tree := .node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501088,15731968] T12bababaa T12bababab
theorem T12bababa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bababa = true :=
  tall_node _ _ _ _ T12bababaa_ok (by decide +kernel) T12bababab_ok
def T12bababbaa : Tree := (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13503104,15731968] .nil .nil)
theorem T12bababbaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bababbaa = true := by decide +kernel
def T12bababbab : Tree := .nil
theorem T12bababbab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bababbab = true := by decide +kernel
def T12bababba : Tree := .node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13613728,15731968,16650112] T12bababbaa T12bababbab
theorem T12bababba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bababba = true :=
  tall_node _ _ _ _ T12bababbaa_ok (by decide +kernel) T12bababbab_ok
def T12bababbb : Tree := (.node [113184,430348,902208,3227782,5521457,7684279,8532043,11083800,13501056,15731968] .nil .nil)
theorem T12bababbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bababbb = true := by decide +kernel
def T12bababb : Tree := .node [113184,430348,902208,3227782,5521457,7684279,8532039,11083800,13501056,15731968] T12bababba T12bababbb
theorem T12bababb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bababb = true :=
  tall_node _ _ _ _ T12bababba_ok (by decide +kernel) T12bababbb_ok
def T12babab : Tree := .node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13502080,15731968] T12bababa T12bababb
theorem T12babab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babab = true :=
  tall_node _ _ _ _ T12bababa_ok (by decide +kernel) T12bababb_ok
def T12baba : Tree := .node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501060,15731968] T12babaa T12babab
theorem T12baba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12baba = true :=
  tall_node _ _ _ _ T12babaa_ok (by decide +kernel) T12babab_ok
def T12babbaaaa : Tree := (.node [113184,430348,902208,3227782,5521457,7684279,8532291,11083800,13501056,15731968] .nil .nil)
theorem T12babbaaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babbaaaa = true := by decide +kernel
def T12babbaaab : Tree := .nil
theorem T12babbaaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babbaaab = true := by decide +kernel
def T12babbaaa : Tree := .node [113184,430348,902208,3227782,5521457,7684279,8533059,11083800,13501056,15731968] T12babbaaaa T12babbaaab
theorem T12babbaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babbaaa = true :=
  tall_node _ _ _ _ T12babbaaaa_ok (by decide +kernel) T12babbaaab_ok
def T12babbaaba : Tree := (.node [113184,430348,902208,3227782,5521457,7684279,9434179,11083800,13501056,15731968,15875395] .nil .nil)
theorem T12babbaaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babbaaba = true := by decide +kernel
def T12babbaabb : Tree := .nil
theorem T12babbaabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babbaabb = true := by decide +kernel
def T12babbaab : Tree := .node [113184,430348,902208,3227782,5521457,7684287,8532035,11083800,13501056,15731968] T12babbaaba T12babbaabb
theorem T12babbaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babbaab = true :=
  tall_node _ _ _ _ T12babbaaba_ok (by decide +kernel) T12babbaabb_ok
def T12babbaa : Tree := .node [113184,430348,902208,3227782,5521457,7684279,8632931,11083800,13501056,15731968,15875395] T12babbaaa T12babbaab
theorem T12babbaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babbaa = true :=
  tall_node _ _ _ _ T12babbaaa_ok (by decide +kernel) T12babbaab_ok
def T12babbabaa : Tree := (.node [113184,430348,902208,3227782,5521457,7684535,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12babbabaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babbabaa = true := by decide +kernel
def T12babbabab : Tree := .nil
theorem T12babbabab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babbabab = true := by decide +kernel
def T12babbaba : Tree := .node [113184,430348,902208,3227782,5521457,7685303,8532035,11083800,13501056,15731968] T12babbabaa T12babbabab
theorem T12babbaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babbaba = true :=
  tall_node _ _ _ _ T12babbabaa_ok (by decide +kernel) T12babbabab_ok
def T12babbabb : Tree := (.node [113184,430348,902208,3227782,5521457,8242423,8532035,11083800,12148894,13501056,15731968] .nil .nil)
theorem T12babbabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babbabb = true := by decide +kernel
def T12babbab : Tree := .node [113184,430348,902208,3227782,5521457,8208567,8532035,11083800,13501056,15731968] T12babbaba T12babbabb
theorem T12babbab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babbab = true :=
  tall_node _ _ _ _ T12babbaba_ok (by decide +kernel) T12babbabb_ok
def T12babba : Tree := .node [113184,430348,902208,3227782,5521457,7684343,8532035,11083800,13501056,15731968] T12babbaa T12babbab
theorem T12babba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babba = true :=
  tall_node _ _ _ _ T12babbaa_ok (by decide +kernel) T12babbab_ok
def T12babbbaaa : Tree := (.node [113184,430348,902208,3227782,5521457,8242423,8532035,11083800,13501056,15731968,15814022] .nil .nil)
theorem T12babbbaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babbbaaa = true := by decide +kernel
def T12babbbaab : Tree := .nil
theorem T12babbbaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babbbaab = true := by decide +kernel
def T12babbbaa : Tree := .node [113184,430348,902208,3227782,5521457,8242423,8532035,11083800,13501056,15731968,16076215] T12babbbaaa T12babbbaab
theorem T12babbbaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babbbaa = true :=
  tall_node _ _ _ _ T12babbbaaa_ok (by decide +kernel) T12babbbaab_ok
def T12babbbaba : Tree := (.node [113184,430348,902208,3227782,5521457,8242423,8532035,11083800,13501056,15731968,16330008] .nil .nil)
theorem T12babbbaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babbbaba = true := by decide +kernel
def T12babbbabb : Tree := .nil
theorem T12babbbabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babbbabb = true := by decide +kernel
def T12babbbab : Tree := .node [113184,430348,902208,3227782,5521457,8242423,8532035,11083800,13501056,15731968,16605375] T12babbbaba T12babbbabb
theorem T12babbbab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babbbab = true :=
  tall_node _ _ _ _ T12babbbaba_ok (by decide +kernel) T12babbbabb_ok
def T12babbba : Tree := .node [113184,430348,902208,3227782,5521457,8242423,8532035,11083800,13501056,15731968,16216311] T12babbbaa T12babbbab
theorem T12babbba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babbba = true :=
  tall_node _ _ _ _ T12babbbaa_ok (by decide +kernel) T12babbbab_ok
def T12babbbbaa : Tree := (.node [113184,430348,902208,3227782,5521457,8532035,8532051,11083800,13501056,15731968] .nil .nil)
theorem T12babbbbaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babbbbaa = true := by decide +kernel
def T12babbbbab : Tree := .nil
theorem T12babbbbab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babbbbab = true := by decide +kernel
def T12babbbba : Tree := .node [113184,430348,902208,3227782,5521457,8532035,8632931,11083800,11123256,13501056,15731968] T12babbbbaa T12babbbbab
theorem T12babbbba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babbbba = true :=
  tall_node _ _ _ _ T12babbbbaa_ok (by decide +kernel) T12babbbbab_ok
def T12babbbbb : Tree := (.node [113184,430348,902208,3227782,5521457,8532035,8632931,11083800,11254395,13501056,15731968] .nil .nil)
theorem T12babbbbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babbbbb = true := by decide +kernel
def T12babbbb : Tree := .node [113184,430348,902208,3227782,5521457,8532035,8632931,11083800,11219035,13501056,15731968] T12babbbba T12babbbbb
theorem T12babbbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babbbb = true :=
  tall_node _ _ _ _ T12babbbba_ok (by decide +kernel) T12babbbbb_ok
def T12babbb : Tree := .node [113184,430348,902208,3227782,5521457,8388611,8532035,11083800,13501056,15731968,16076215] T12babbba T12babbbb
theorem T12babbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babbb = true :=
  tall_node _ _ _ _ T12babbba_ok (by decide +kernel) T12babbbb_ok
def T12babb : Tree := .node [113184,430348,902208,3227782,5521457,8242423,8532035,11083800,13501056,15671960,15731968] T12babba T12babbb
theorem T12babb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12babb = true :=
  tall_node _ _ _ _ T12babba_ok (by decide +kernel) T12babbb_ok
def T12bab : Tree := .node [113184,430348,902208,3227782,5521457,7684279,8532051,11083800,13501056,15731968] T12baba T12babb
theorem T12bab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bab = true :=
  tall_node _ _ _ _ T12baba_ok (by decide +kernel) T12babb_ok
def T12ba : Tree := .node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731971] T12baa T12bab
theorem T12ba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12ba = true :=
  tall_node _ _ _ _ T12baa_ok (by decide +kernel) T12bab_ok
def T12bbaaaaaa : Tree := (.node [113184,430348,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731968,15814022] .nil .nil)
theorem T12bbaaaaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbaaaaaa = true := by decide +kernel
def T12bbaaaaab : Tree := .nil
theorem T12bbaaaaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbaaaaab = true := by decide +kernel
def T12bbaaaaa : Tree := .node [113184,430348,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731968,16010545] T12bbaaaaaa T12bbaaaaab
theorem T12bbaaaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbaaaaa = true :=
  tall_node _ _ _ _ T12bbaaaaaa_ok (by decide +kernel) T12bbaaaaab_ok
def T12bbaaaaba : Tree := (.node [113184,430348,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731968,16330008] .nil .nil)
theorem T12bbaaaaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbaaaaba = true := by decide +kernel
def T12bbaaaabb : Tree := .nil
theorem T12bbaaaabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbaaaabb = true := by decide +kernel
def T12bbaaaab : Tree := .node [113184,430348,902208,3227782,5521457,8532035,8895343,11083800,13501056,15731968] T12bbaaaaba T12bbaaaabb
theorem T12bbaaaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbaaaab = true :=
  tall_node _ _ _ _ T12bbaaaaba_ok (by decide +kernel) T12bbaaaabb_ok
def T12bbaaaa : Tree := .node [113184,430348,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731968,16076215] T12bbaaaaa T12bbaaaab
theorem T12bbaaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbaaaa = true :=
  tall_node _ _ _ _ T12bbaaaaa_ok (by decide +kernel) T12bbaaaab_ok
def T12bbaaabaa : Tree := (.node [113184,430348,902208,3227782,5521457,8532035,11083800,11123256,13501056,15731968,15814022] .nil .nil)
theorem T12bbaaabaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbaaabaa = true := by decide +kernel
def T12bbaaabab : Tree := .nil
theorem T12bbaaabab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbaaabab = true := by decide +kernel
def T12bbaaaba : Tree := .node [113184,430348,902208,3227782,5521457,8532035,11083800,11219035,13501056,15731968,15814022] T12bbaaabaa T12bbaaabab
theorem T12bbaaaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbaaaba = true :=
  tall_node _ _ _ _ T12bbaaabaa_ok (by decide +kernel) T12bbaaabab_ok
def T12bbaaabb : Tree := (.node [113184,430348,902208,3227782,5521457,8532035,11083800,12148894,13501056,15731968,15814022] .nil .nil)
theorem T12bbaaabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbaaabb = true := by decide +kernel
def T12bbaaab : Tree := .node [113184,430348,902208,3227782,5521457,8532035,11083800,12148894,13501056,14566065,15731968] T12bbaaaba T12bbaaabb
theorem T12bbaaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbaaab = true :=
  tall_node _ _ _ _ T12bbaaaba_ok (by decide +kernel) T12bbaaabb_ok
def T12bbaaa : Tree := .node [113184,430348,902208,3227782,5521457,8532035,11083800,11123256,13501056,13538188,15731968] T12bbaaaa T12bbaaab
theorem T12bbaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbaaa = true :=
  tall_node _ _ _ _ T12bbaaaa_ok (by decide +kernel) T12bbaaab_ok
def T12bbaabaaa : Tree := (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,15814022,16330008] .nil .nil)
theorem T12bbaabaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbaabaaa = true := by decide +kernel
def T12bbaabaab : Tree := .nil
theorem T12bbaabaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbaabaab = true := by decide +kernel
def T12bbaabaa : Tree := .node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,15814022,16346526] T12bbaabaaa T12bbaabaab
theorem T12bbaabaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbaabaa = true :=
  tall_node _ _ _ _ T12bbaabaaa_ok (by decide +kernel) T12bbaabaab_ok
def T12bbaababa : Tree := (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731976] .nil .nil)
theorem T12bbaababa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbaababa = true := by decide +kernel
def T12bbaababb : Tree := .nil
theorem T12bbaababb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbaababb = true := by decide +kernel
def T12bbaabab : Tree := .node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15732032] T12bbaababa T12bbaababb
theorem T12bbaabab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbaabab = true :=
  tall_node _ _ _ _ T12bbaababa_ok (by decide +kernel) T12bbaababb_ok
def T12bbaaba : Tree := .node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16076215] T12bbaabaa T12bbaabab
theorem T12bbaaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbaaba = true :=
  tall_node _ _ _ _ T12bbaabaa_ok (by decide +kernel) T12bbaabab_ok
def T12bbaabbaa : Tree := (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13513411,15731968,16650112] .nil .nil)
theorem T12bbaabbaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbaabbaa = true := by decide +kernel
def T12bbaabbab : Tree := .nil
theorem T12bbaabbab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbaabbab = true := by decide +kernel
def T12bbaabba : Tree := .node [113184,430348,902208,3227782,5521457,8532035,11083800,13538188,14566065,15731968] T12bbaabbaa T12bbaabbab
theorem T12bbaabba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbaabba = true :=
  tall_node _ _ _ _ T12bbaabbaa_ok (by decide +kernel) T12bbaabbab_ok
def T12bbaabbb : Tree := (.node [113184,430348,902208,3227782,5521457,8533059,11083800,13501056,15731968] .nil .nil)
theorem T12bbaabbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbaabbb = true := by decide +kernel
def T12bbaabb : Tree := .node [113184,430348,902208,3227782,5521457,8532051,11083800,13501056,15731968] T12bbaabba T12bbaabbb
theorem T12bbaabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbaabb = true :=
  tall_node _ _ _ _ T12bbaabba_ok (by decide +kernel) T12bbaabbb_ok
def T12bbaab : Tree := .node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15875395,16076215] T12bbaaba T12bbaabb
theorem T12bbaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbaab = true :=
  tall_node _ _ _ _ T12bbaaba_ok (by decide +kernel) T12bbaabb_ok
def T12bbaa : Tree := .node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,15731976] T12bbaaa T12bbaab
theorem T12bbaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbaa = true :=
  tall_node _ _ _ _ T12bbaaa_ok (by decide +kernel) T12bbaab_ok
def T12bbabaaaa : Tree := (.node [113184,430348,902208,3227782,5521461,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12bbabaaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbabaaaa = true := by decide +kernel
def T12bbabaaab : Tree := .nil
theorem T12bbabaaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbabaaab = true := by decide +kernel
def T12bbabaaa : Tree := .node [113184,430348,902208,3227782,5521465,7684279,8532035,11083800,13501056,15731968] T12bbabaaaa T12bbabaaab
theorem T12bbabaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbabaaa = true :=
  tall_node _ _ _ _ T12bbabaaaa_ok (by decide +kernel) T12bbabaaab_ok
def T12bbabaaba : Tree := (.node [113184,430348,902208,3227782,5521521,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12bbabaaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbabaaba = true := by decide +kernel
def T12bbabaabb : Tree := .nil
theorem T12bbabaabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbabaabb = true := by decide +kernel
def T12bbabaab : Tree := .node [113184,430348,902208,3227782,5521521,8532035,11083800,13501056,15731968] T12bbabaaba T12bbabaabb
theorem T12bbabaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbabaab = true :=
  tall_node _ _ _ _ T12bbabaaba_ok (by decide +kernel) T12bbabaabb_ok
def T12bbabaa : Tree := .node [113184,430348,902208,3227782,5521465,8532035,11083800,13501056,15731968] T12bbabaaa T12bbabaab
theorem T12bbabaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbabaa = true :=
  tall_node _ _ _ _ T12bbabaaa_ok (by decide +kernel) T12bbabaab_ok
def T12bbababaa : Tree := (.node [113184,430348,902208,3227782,5521713,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12bbababaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbababaa = true := by decide +kernel
def T12bbababab : Tree := .nil
theorem T12bbababab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbababab = true := by decide +kernel
def T12bbababa : Tree := .node [113184,430348,902208,3227782,5521969,7684279,8532035,11083800,13501056,15731968] T12bbababaa T12bbababab
theorem T12bbababa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbababa = true :=
  tall_node _ _ _ _ T12bbababaa_ok (by decide +kernel) T12bbababab_ok
def T12bbababb : Tree := (.node [113184,430348,902208,3227782,5522481,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12bbababb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbababb = true := by decide +kernel
def T12bbabab : Tree := .node [113184,430348,902208,3227782,5521969,8532035,11083800,13501056,15731968] T12bbababa T12bbababb
theorem T12bbabab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbabab = true :=
  tall_node _ _ _ _ T12bbababa_ok (by decide +kernel) T12bbababb_ok
def T12bbaba : Tree := .node [113184,430348,902208,3227782,5521585,7684279,8532035,11083800,13501056,15731968] T12bbabaa T12bbabab
theorem T12bbaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbaba = true :=
  tall_node _ _ _ _ T12bbabaa_ok (by decide +kernel) T12bbabab_ok
def T12bbabbaaa : Tree := (.node [113184,430348,902208,3227782,5554225,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12bbabbaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbabbaaa = true := by decide +kernel
def T12bbabbaab : Tree := .nil
theorem T12bbabbaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbabbaab = true := by decide +kernel
def T12bbabbaa : Tree := .node [113184,430348,902208,3227782,5652529,7684279,8532035,11083800,13501056,15731968] T12bbabbaaa T12bbabbaab
theorem T12bbabbaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbabbaa = true :=
  tall_node _ _ _ _ T12bbabbaaa_ok (by decide +kernel) T12bbabbaab_ok
def T12bbabbaba : Tree := (.node [113184,430348,902208,3227782,5689661,6145137,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12bbabbaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbabbaba = true := by decide +kernel
def T12bbabbabb : Tree := .nil
theorem T12bbabbabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbabbabb = true := by decide +kernel
def T12bbabbab : Tree := .node [113184,430348,902208,3227782,5689661,7684279,8242423,8532035,11083800,13501056,15731968] T12bbabbaba T12bbabbabb
theorem T12bbabbab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbabbab = true :=
  tall_node _ _ _ _ T12bbabbaba_ok (by decide +kernel) T12bbabbabb_ok
def T12bbabba : Tree := .node [113184,430348,902208,3227782,5656625,7684279,8532035,11083800,13501056,15731968] T12bbabbaa T12bbabbab
theorem T12bbabba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbabba = true :=
  tall_node _ _ _ _ T12bbabbaa_ok (by decide +kernel) T12bbabbab_ok
def T12bbabbbaa : Tree := (.node [113184,430348,902208,3227782,5689661,7684279,8532035,11083800,13501056,15731968,15814022] .nil .nil)
theorem T12bbabbbaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbabbbaa = true := by decide +kernel
def T12bbabbbab : Tree := .nil
theorem T12bbabbbab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbabbbab = true := by decide +kernel
def T12bbabbba : Tree := .node [113184,430348,902208,3227782,5689661,7684279,8532035,11083800,13501056,15731968,15875395] T12bbabbbaa T12bbabbbab
theorem T12bbabbba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbabbba = true :=
  tall_node _ _ _ _ T12bbabbbaa_ok (by decide +kernel) T12bbabbbab_ok
def T12bbabbbb : Tree := (.node [113184,430348,902208,3227782,6045745,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12bbabbbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbabbbb = true := by decide +kernel
def T12bbabbb : Tree := .node [113184,430348,902208,3227782,5689661,8532035,11083800,13501056,15731968,16076215] T12bbabbba T12bbabbbb
theorem T12bbabbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbabbb = true :=
  tall_node _ _ _ _ T12bbabbba_ok (by decide +kernel) T12bbabbbb_ok
def T12bbabb : Tree := .node [113184,430348,902208,3227782,5689661,7684279,8532035,8632931,11083800,13501056,15731968] T12bbabba T12bbabbb
theorem T12bbabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbabb = true :=
  tall_node _ _ _ _ T12bbabba_ok (by decide +kernel) T12bbabbb_ok
def T12bbab : Tree := .node [113184,430348,902208,3227782,5523505,7684279,8532035,11083800,13501056,15731968] T12bbaba T12bbabb
theorem T12bbab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbab = true :=
  tall_node _ _ _ _ T12bbaba_ok (by decide +kernel) T12bbabb_ok
def T12bba : Tree := .node [113184,430348,902208,3227782,5521459,7684279,8532035,11083800,13501056,15731968] T12bbaa T12bbab
theorem T12bba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bba = true :=
  tall_node _ _ _ _ T12bbaa_ok (by decide +kernel) T12bbab_ok
def T12bbbaaaaa : Tree := (.node [113184,430348,902208,3227782,6145137,7684279,8532035,11083800,13501056,14566065,15731968] .nil .nil)
theorem T12bbbaaaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbaaaaa = true := by decide +kernel
def T12bbbaaaab : Tree := .nil
theorem T12bbbaaaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbaaaab = true := by decide +kernel
def T12bbbaaaa : Tree := .node [113184,430348,902208,3227782,6145137,7684279,8532035,11083800,13501056,15731968,16010545] T12bbbaaaaa T12bbbaaaab
theorem T12bbbaaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbaaaa = true :=
  tall_node _ _ _ _ T12bbbaaaaa_ok (by decide +kernel) T12bbbaaaab_ok
def T12bbbaaaba : Tree := (.node [113184,430348,902208,3227782,7684279,8242423,8532035,11083800,13501056,14566065,15731968] .nil .nil)
theorem T12bbbaaaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbaaaba = true := by decide +kernel
def T12bbbaaabb : Tree := .nil
theorem T12bbbaaabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbaaabb = true := by decide +kernel
def T12bbbaaab : Tree := .node [113184,430348,902208,3227782,7684279,8532035,8827215,11083800,13501056,14566065,15731968] T12bbbaaaba T12bbbaaabb
theorem T12bbbaaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbaaab = true :=
  tall_node _ _ _ _ T12bbbaaaba_ok (by decide +kernel) T12bbbaaabb_ok
def T12bbbaaa : Tree := .node [113184,430348,902208,3227782,7684279,8242423,8532035,11083800,13501056,14053491,15731968] T12bbbaaaa T12bbbaaab
theorem T12bbbaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbaaa = true :=
  tall_node _ _ _ _ T12bbbaaaa_ok (by decide +kernel) T12bbbaaab_ok
def T12bbbaabaa : Tree := (.node [113184,430348,902208,3227782,7684279,8532035,11083800,13501056,13918257,15731968] .nil .nil)
theorem T12bbbaabaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbaabaa = true := by decide +kernel
def T12bbbaabab : Tree := .nil
theorem T12bbbaabab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbaabab = true := by decide +kernel
def T12bbbaaba : Tree := .node [113184,430348,902208,3227782,7684279,8532035,11083800,13501056,14566065,15731968,16010545] T12bbbaabaa T12bbbaabab
theorem T12bbbaaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbaaba = true :=
  tall_node _ _ _ _ T12bbbaabaa_ok (by decide +kernel) T12bbbaabab_ok
def T12bbbaabb : Tree := (.node [113184,430348,902208,3275430,5689661,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12bbbaabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbaabb = true := by decide +kernel
def T12bbbaab : Tree := .node [113184,430348,902208,3227782,7684279,11083800,11219035,13501056,14053491,15731968] T12bbbaaba T12bbbaabb
theorem T12bbbaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbaab = true :=
  tall_node _ _ _ _ T12bbbaaba_ok (by decide +kernel) T12bbbaabb_ok
def T12bbbaa : Tree := .node [113184,430348,902208,3227782,7684279,8532035,11083800,13501056,13910065,15731968] T12bbbaaa T12bbbaab
theorem T12bbbaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbaa = true :=
  tall_node _ _ _ _ T12bbbaaa_ok (by decide +kernel) T12bbbaab_ok
def T12bbbabaaa : Tree := (.node [113184,430348,902211,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12bbbabaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbabaaa = true := by decide +kernel
def T12bbbabaab : Tree := .nil
theorem T12bbbabaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbabaab = true := by decide +kernel
def T12bbbabaa : Tree := .node [113184,430348,902211,3227782,5521457,8532035,11083800,13501056,15731968] T12bbbabaaa T12bbbabaab
theorem T12bbbabaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbabaa = true :=
  tall_node _ _ _ _ T12bbbabaaa_ok (by decide +kernel) T12bbbabaab_ok
def T12bbbababa : Tree := (.node [113184,430348,902216,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12bbbababa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbababa = true := by decide +kernel
def T12bbbababb : Tree := .nil
theorem T12bbbababb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbababb = true := by decide +kernel
def T12bbbabab : Tree := .node [113184,430348,902224,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12bbbababa T12bbbababb
theorem T12bbbabab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbabab = true :=
  tall_node _ _ _ _ T12bbbababa_ok (by decide +kernel) T12bbbababb_ok
def T12bbbaba : Tree := .node [113184,430348,902212,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12bbbabaa T12bbbabab
theorem T12bbbaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbaba = true :=
  tall_node _ _ _ _ T12bbbabaa_ok (by decide +kernel) T12bbbabab_ok
def T12bbbabbaa : Tree := (.node [113184,430348,917088,3227782,4048070,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12bbbabbaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbabbaa = true := by decide +kernel
def T12bbbabbab : Tree := .nil
theorem T12bbbabbab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbabbab = true := by decide +kernel
def T12bbbabba : Tree := .node [113184,430348,917088,3227782,4048070,5521457,8532035,11083800,13501056,15731968] T12bbbabbaa T12bbbabbab
theorem T12bbbabba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbabba = true :=
  tall_node _ _ _ _ T12bbbabbaa_ok (by decide +kernel) T12bbbabbab_ok
def T12bbbabbb : Tree := (.node [113184,430348,917088,3227782,5521457,7684279,8242423,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12bbbabbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbabbb = true := by decide +kernel
def T12bbbabb : Tree := .node [113184,430348,917088,3227782,5521457,6145137,7684279,8532035,11083800,13501056,15731968] T12bbbabba T12bbbabbb
theorem T12bbbabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbabb = true :=
  tall_node _ _ _ _ T12bbbabba_ok (by decide +kernel) T12bbbabbb_ok
def T12bbbab : Tree := .node [113184,430348,902464,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12bbbaba T12bbbabb
theorem T12bbbab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbab = true :=
  tall_node _ _ _ _ T12bbbaba_ok (by decide +kernel) T12bbbabb_ok
def T12bbba : Tree := .node [113184,430348,902209,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12bbbaa T12bbbab
theorem T12bbba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbba = true :=
  tall_node _ _ _ _ T12bbbaa_ok (by decide +kernel) T12bbbab_ok
def T12bbbbaaaa : Tree := (.node [113184,430349,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12bbbbaaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbbaaaa = true := by decide +kernel
def T12bbbbaaab : Tree := .nil
theorem T12bbbbaaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbbaaab = true := by decide +kernel
def T12bbbbaaa : Tree := .node [113184,430350,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12bbbbaaaa T12bbbbaaab
theorem T12bbbbaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbbaaa = true :=
  tall_node _ _ _ _ T12bbbbaaaa_ok (by decide +kernel) T12bbbbaaab_ok
def T12bbbbaaba : Tree := (.node [113184,430351,902208,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12bbbbaaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbbaaba = true := by decide +kernel
def T12bbbbaabb : Tree := .nil
theorem T12bbbbaabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbbaabb = true := by decide +kernel
def T12bbbbaab : Tree := .node [113184,430364,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12bbbbaaba T12bbbbaabb
theorem T12bbbbaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbbaab = true :=
  tall_node _ _ _ _ T12bbbbaaba_ok (by decide +kernel) T12bbbbaabb_ok
def T12bbbbaa : Tree := .node [113184,430351,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12bbbbaaa T12bbbbaab
theorem T12bbbbaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbbaa = true :=
  tall_node _ _ _ _ T12bbbbaaa_ok (by decide +kernel) T12bbbbaab_ok
def T12bbbbabaa : Tree := (.node [113184,430380,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12bbbbabaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbbabaa = true := by decide +kernel
def T12bbbbabab : Tree := .nil
theorem T12bbbbabab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbbabab = true := by decide +kernel
def T12bbbbaba : Tree := .node [113184,430412,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12bbbbabaa T12bbbbabab
theorem T12bbbbaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbbaba = true :=
  tall_node _ _ _ _ T12bbbbabaa_ok (by decide +kernel) T12bbbbabab_ok
def T12bbbbabb : Tree := (.node [113184,430476,902208,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12bbbbabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbbabb = true := by decide +kernel
def T12bbbbab : Tree := .node [113184,430476,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12bbbbaba T12bbbbabb
theorem T12bbbbab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbbab = true :=
  tall_node _ _ _ _ T12bbbbaba_ok (by decide +kernel) T12bbbbabb_ok
def T12bbbba : Tree := .node [113184,430364,902208,3227782,5521457,8532035,11083800,13501056,15731968] T12bbbbaa T12bbbbab
theorem T12bbbba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbba = true :=
  tall_node _ _ _ _ T12bbbbaa_ok (by decide +kernel) T12bbbbab_ok
def T12bbbbbaaa : Tree := (.node [113184,431372,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12bbbbbaaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbbbaaa = true := by decide +kernel
def T12bbbbbaab : Tree := .nil
theorem T12bbbbbaab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbbbaab = true := by decide +kernel
def T12bbbbbaa : Tree := .node [113184,431372,902208,3227782,5521457,8532035,11083800,13501056,15731968] T12bbbbbaaa T12bbbbbaab
theorem T12bbbbbaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbbbaa = true :=
  tall_node _ _ _ _ T12bbbbbaaa_ok (by decide +kernel) T12bbbbbaab_ok
def T12bbbbbaba : Tree := (.node [113184,506668,902208,3227782,5521457,5689661,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12bbbbbaba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbbbaba = true := by decide +kernel
def T12bbbbbabb : Tree := .nil
theorem T12bbbbbabb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbbbabb = true := by decide +kernel
def T12bbbbbab : Tree := .node [113184,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,13538188,15731968] T12bbbbbaba T12bbbbbabb
theorem T12bbbbbab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbbbab = true :=
  tall_node _ _ _ _ T12bbbbbaba_ok (by decide +kernel) T12bbbbbabb_ok
def T12bbbbba : Tree := .node [113184,432396,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12bbbbbaa T12bbbbbab
theorem T12bbbbba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbbba = true :=
  tall_node _ _ _ _ T12bbbbbaa_ok (by decide +kernel) T12bbbbbab_ok
def T12bbbbbbaa : Tree := (.node [113184,506668,902208,3227782,5689661,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T12bbbbbbaa_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbbbbaa = true := by decide +kernel
def T12bbbbbbab : Tree := .nil
theorem T12bbbbbbab_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbbbbab = true := by decide +kernel
def T12bbbbbba : Tree := .node [113184,902208,1037644,3227782,5521457,7684279,8532035,8827215,11083800,13501056,15731968] T12bbbbbbaa T12bbbbbbab
theorem T12bbbbbba_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbbbba = true :=
  tall_node _ _ _ _ T12bbbbbbaa_ok (by decide +kernel) T12bbbbbbab_ok
def T12bbbbbbb : Tree := (.node [113184,902208,3227782,5689661,7684279,8532035,8827215,11083800,13501056,15731968] .nil .nil)
theorem T12bbbbbbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbbbbb = true := by decide +kernel
def T12bbbbbb : Tree := .node [113184,902208,1037644,3227782,5521457,7684279,8532035,11083800,13501056,15731968,16162060] T12bbbbbba T12bbbbbbb
theorem T12bbbbbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbbbb = true :=
  tall_node _ _ _ _ T12bbbbbba_ok (by decide +kernel) T12bbbbbbb_ok
def T12bbbbb : Tree := .node [113184,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,16162060] T12bbbbba T12bbbbbb
theorem T12bbbbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbbb = true :=
  tall_node _ _ _ _ T12bbbbba_ok (by decide +kernel) T12bbbbbb_ok
def T12bbbb : Tree := .node [113184,430860,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12bbbba T12bbbbb
theorem T12bbbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbbb = true :=
  tall_node _ _ _ _ T12bbbba_ok (by decide +kernel) T12bbbbb_ok
def T12bbb : Tree := .node [113184,430348,917088,3227782,5521457,8242423,8532035,11083800,13501056,15731968] T12bbba T12bbbb
theorem T12bbb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bbb = true :=
  tall_node _ _ _ _ T12bbba_ok (by decide +kernel) T12bbbb_ok
def T12bb : Tree := .node [113184,430348,902208,3227782,6145137,7684279,8532035,11083800,13501056,14053491,15731968] T12bba T12bbb
theorem T12bb_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12bb = true :=
  tall_node _ _ _ _ T12bba_ok (by decide +kernel) T12bbb_ok
def T12b : Tree := .node [113184,430348,902208,3227782,5521457,8532035,8632931,11083800,12148894,13501056,15731968] T12ba T12bb
theorem T12b_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12b = true :=
  tall_node _ _ _ _ T12ba_ok (by decide +kernel) T12bb_ok
def T12 : Tree := .node [113184,430348,902208,917088,3275430,5521457,7684279,8532035,11083800,13501056,15731968] T12a T12b
theorem T12_ok : tall (expFast false (RP PR T11 R11 11) T11 11) T12 = true :=
  tall_node _ _ _ _ T12a_ok (by decide +kernel) T12b_ok
def R12aaaa : Tree := (.node [3,81920,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] (.node [3,16,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] (.node [1,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] (.node [1,113184,430348,902208,3227782,4456576,5521457,8532035,11083800,13501056,15731968] (.node [1,3,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil) (.node [1,113184,430348,902208,3227782,5521457,8242423,8532035,11083800,13501056,15731968] .nil .nil)) (.node [3,4,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] (.node [1,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16076215] .nil .nil) (.node [3,8,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil))) (.node [3,65536,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] (.node [3,256,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] (.node [3,64,113184,430348,902208,3227782,5521457,11083800,13501056,15731968] .nil .nil) (.node [3,12288,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil)) (.node [3,73728,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] (.node [3,65568,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil) .nil))) (.node [3,113184,430348,902208,3145728,3227782,5521457,8532035,11083800,13501056,15731968] (.node [3,113184,430348,902208,917088,3227782,5521457,8532035,11083800,13501056,15731968] (.node [3,113184,430348,506668,902208,3227782,5521457,8532035,11083800,13501056,15731968] (.node [3,98304,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil) (.node [3,113184,430348,589824,902208,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil)) (.node [3,113184,430348,902208,2162704,3227782,5521457,8532035,11083800,13501056,15731968] (.node [3,113184,430348,902208,2162688,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil) .nil)) (.node [3,113184,430348,902208,3227782,5521457,7731895,8532035,11083800,13501056,15731968] (.node [3,113184,430348,902208,3227782,3658126,5521457,8532035,11083800,13501056,15731968] (.node [3,113184,430348,902208,3227782,3275430,5521457,8532035,11083800,13501056,15731968] .nil .nil) (.node [3,113184,430348,902208,3227782,4048070,5521457,8532035,11083800,13501056,15731968] .nil .nil)) (.node [3,113184,430348,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731968] (.node [3,113184,430348,902208,3227782,5521457,8396800,8532035,11083800,13501056,15731968] .nil .nil) .nil))))
theorem R12aaaa_ok : tall (refOK cpF 12) R12aaaa = true := by decide +kernel
def R12aaaba : Tree := (.node [3,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16330008] (.node [3,113184,430348,902208,3227782,5521457,8532035,11083800,11514140,13501056,15731968] (.node [3,113184,430348,902208,3227782,5521457,8532035,11083800,11219035,13501056,15731968] (.node [3,113184,430348,902208,3227782,5521457,8532035,11083800,11123256,13501056,15731968] .nil .nil) (.node [3,113184,430348,902208,3227782,5521457,8532035,11083800,11396184,13501056,15731968] .nil .nil)) (.node [3,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,15843104] (.node [3,113184,430348,902208,3227782,5521457,8532035,11083800,11759815,13501056,15731968] .nil .nil) .nil)) (.node [3,113184,430348,902208,3227782,5521457,11083800,13501056,15731968,15875395] (.node [3,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16605375] (.node [3,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16605241] .nil .nil) (.node [3,113184,430348,902208,3227782,5521457,8532035,11083800,13501059,15731968] .nil .nil)) (.node [3,113184,430348,902208,3227782,5689661,7684279,8532035,11083800,13501056,15731968] (.node [3,113184,430348,902208,3227782,5521459,8532035,11083800,13501056,15731968] .nil .nil) .nil)))
theorem R12aaaba_ok : tall (refOK cpF 12) R12aaaba = true := by decide +kernel
def R12aaabb : Tree := (.node [8,16,113184,430348,902208,3227782,5521457,8532035,13501056,15731968] (.node [4,113184,430348,902208,3227782,5521457,8242423,8532035,11083800,13501056,15731968] (.node [3,113184,430351,902208,3227782,5521457,8532035,11083800,13501056,15731968] (.node [3,113184,430348,902208,3227782,7684279,8532035,11083800,13501056,14566065,15731968] .nil .nil) (.node [4,64,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil)) (.node [4,113184,430348,902208,3227782,7684279,8532035,11083800,13501056,14566065,15731968] (.node [4,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16076215] .nil .nil) .nil)) (.node [8,113184,430348,506668,902208,3227782,5521457,8532035,11083800,13501056,15731968] (.node [8,128,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] (.node [8,64,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil) (.node [8,1024,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil)) (.node [8,113184,430348,902208,3227782,5521457,8242423,8532035,11083800,13501056,15731968] (.node [8,113184,430348,902208,2162704,3227782,5521457,8532035,13501056,15731968] .nil .nil) .nil)))
theorem R12aaabb_ok : tall (refOK cpF 12) R12aaabb = true := by decide +kernel
def R12aaab : Tree := .node [3,113184,430348,902208,3227782,7684279,8532035,11083800,13501056,14053491,15731968] R12aaaba R12aaabb
theorem R12aaab_ok : tall (refOK cpF 12) R12aaab = true :=
  tall_node _ _ _ _ R12aaaba_ok (by decide +kernel) R12aaabb_ok
def R12aaa : Tree := .node [3,113184,430348,902208,3227782,5521457,8532035,10485760,11083800,13501056,15731968] R12aaaa R12aaab
theorem R12aaa_ok : tall (refOK cpF 12) R12aaa = true :=
  tall_node _ _ _ _ R12aaaa_ok (by decide +kernel) R12aaab_ok
def R12aabaa : Tree := (.node [16,113184,430348,902208,2162704,3227782,5521457,8532035,11083800,13501056,15731968] (.node [16,64,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] (.node [8,113184,430348,902208,3227782,5521457,8532035,11123256,13501056,15731968] (.node [8,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16076215] .nil .nil) (.node [8,113184,430348,902208,3227782,5521457,8532035,11219035,13501056,15731968] .nil .nil)) (.node [16,113184,430348,506668,902208,3227782,5521457,8532035,11083800,13501056,15731968] (.node [16,1024,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil) .nil)) (.node [16,113184,430348,902208,3227782,5521457,8532035,12148894,13501056,15731968] (.node [16,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,15875395] (.node [16,113184,430348,902208,3227782,5521457,8242423,8532035,11083800,13501056,15731968] .nil .nil) (.node [16,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16076215] .nil .nil)) (.node [16,113184,430348,902208,3227782,7684279,8532035,11083800,13501056,15731968,16010545] (.node [16,113184,430348,902208,3227782,5521457,8532035,13501056,15731968,16330008] .nil .nil) .nil)))
theorem R12aabaa_ok : tall (refOK cpF 12) R12aabaa = true := by decide +kernel
def R12aabab : Tree := (.node [64,113184,430348,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731968] (.node [64,113184,430348,902208,2162704,3227782,5521457,8532035,11083800,13501056,15731968] (.node [64,1024,113184,430348,3227782,5521457,8532035,11083800,13501056,15731968] (.node [16,113184,430348,902208,5521457,7684279,8532035,12148894,13501056,15731968] .nil .nil) (.node [64,113184,430348,902208,917088,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil)) (.node [64,113184,430348,902208,3227782,4048070,5521457,8532035,11083800,13501056,15731968] (.node [64,113184,430348,902208,3227782,3275430,5521457,8532035,11083800,13501056,15731968] .nil .nil) .nil)) (.node [64,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,15814022] (.node [64,113184,430348,902208,3227782,5521457,8532035,11083800,11219035,13501056,15731968] (.node [64,113184,430348,902208,3227782,5521457,8532035,11083800,11123256,13501056,15731968] .nil .nil) (.node [64,113184,430348,902208,3227782,5521457,8532035,11083800,12148894,13501056,15731968] .nil .nil)) (.node [64,113184,430348,902208,3227782,5521457,8532035,11083800,13501120,15731968] (.node [64,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16330008] .nil .nil) .nil)))
theorem R12aabab_ok : tall (refOK cpF 12) R12aabab = true := by decide +kernel
def R12aaba : Tree := .node [16,113184,430348,902208,5521457,7684279,8532035,11083800,12148894,13501056,15731968] R12aabaa R12aabab
theorem R12aaba_ok : tall (refOK cpF 12) R12aaba = true :=
  tall_node _ _ _ _ R12aabaa_ok (by decide +kernel) R12aabab_ok
def R12aabba : Tree := (.node [256,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16076215] (.node [64,113184,430412,902208,3227782,5521457,8532035,11083800,13501056,15731968] (.node [64,113184,430348,902208,3227782,7684279,8532035,11083800,13501056,14566065,15731968] (.node [64,113184,430348,902208,3227782,7684279,8532035,11083800,13501056,14053491,15731968] .nil .nil) (.node [64,113184,430348,917088,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil)) (.node [256,113184,430348,902208,3227782,5521457,8242423,8532035,11083800,13501056,15731968] (.node [256,113184,430348,902208,3227782,4456576,5521457,8532035,11083800,13501056,15731968] .nil .nil) .nil)) (.node [1024,113184,430348,902208,3227782,3275430,5521457,8532035,11083800,13501056,15731968] (.node [1024,113184,430348,902208,917088,3227782,5521457,8532035,11083800,13501056,15731968] (.node [256,113184,430348,902208,3227782,7684279,8532035,11083800,13501056,14566065,15731968] .nil .nil) (.node [1024,113184,430348,902208,2162704,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil)) (.node [1024,113184,430348,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731968] (.node [1024,113184,430348,902208,3227782,4048070,5521457,8532035,11083800,13501056,15731968] .nil .nil) .nil)))
theorem R12aabba_ok : tall (refOK cpF 12) R12aabba = true := by decide +kernel
def R12aabbb : Tree := (.node [1024,113184,430348,902208,3227782,5689661,7684279,8532035,11083800,13501056,15731968] (.node [1024,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16330008] (.node [1024,113184,430348,902208,3227782,5521457,8532035,11083800,12148894,13501056,15731968] (.node [1024,113184,430348,902208,3227782,5521457,8532035,11083800,11219035,13501056,15731968] .nil .nil) (.node [1024,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,15814022] .nil .nil)) (.node [1024,113184,430348,902208,3227782,5522481,8532035,11083800,13501056,15731968] (.node [1024,113184,430348,902208,3227782,5521457,8532035,11083800,13502080,15731968] .nil .nil) .nil)) (.node [1024,113184,430348,3227782,5521457,8242423,8532035,11083800,13501056,15731968] (.node [1024,113184,430348,902208,3227782,7684279,8532035,11083800,13501056,14566065,15731968] (.node [1024,113184,430348,902208,3227782,7684279,8532035,11083800,13501056,14053491,15731968] .nil .nil) (.node [1024,113184,430348,3227782,4048070,5521457,8532035,11083800,13501056,15731968] .nil .nil)) (.node [8192,113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [1024,113184,431372,902208,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil) .nil)))
theorem R12aabbb_ok : tall (refOK cpF 12) R12aabbb = true := by decide +kernel
def R12aabb : Tree := .node [1024,113184,430348,902208,3227782,5521457,8532035,11083800,11123256,13501056,15731968] R12aabba R12aabbb
theorem R12aabb_ok : tall (refOK cpF 12) R12aabb = true :=
  tall_node _ _ _ _ R12aabba_ok (by decide +kernel) R12aabbb_ok
def R12aab : Tree := .node [64,113184,430348,902208,3227782,5521521,8532035,11083800,13501056,15731968] R12aaba R12aabb
theorem R12aab_ok : tall (refOK cpF 12) R12aab = true :=
  tall_node _ _ _ _ R12aaba_ok (by decide +kernel) R12aabb_ok
def R12aa : Tree := .node [8,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,15875395] R12aaa R12aab
theorem R12aa_ok : tall (refOK cpF 12) R12aa = true :=
  tall_node _ _ _ _ R12aaa_ok (by decide +kernel) R12aab_ok
def R12abaaa : Tree := (.node [36864,113184,430348,902208,3227782,7684279,8532035,11083800,13501056,14053491,15731968] (.node [36864,113184,430348,902208,2162704,3227782,5521457,8532035,11083800,13501056,15731968] (.node [14336,113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [12288,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16076215] .nil .nil) (.node [14336,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil)) (.node [36864,113184,430348,902208,3227782,5689661,7684279,8532035,11083800,13501056,15731968] (.node [36864,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16076215] .nil .nil) .nil)) (.node [65536,113184,430348,902208,3227782,5521457,8242423,8532035,11083800,13501056,15731968] (.node [65536,113184,430348,902208,2162704,3227782,5521457,8532035,11083800,13501056,15731968] (.node [36864,113184,430348,902208,3227782,7684279,8532035,11083800,13501056,14566065,15731968] .nil .nil) (.node [65536,113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)) (.node [65536,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16076215] (.node [65536,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil) .nil)))
theorem R12abaaa_ok : tall (refOK cpF 12) R12abaaa = true := by decide +kernel
def R12abaab : Tree := (.node [67616,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] (.node [65568,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16076215] (.node [65568,113184,430348,902208,3227782,5521457,7340032,8532035,11083800,13501056,15731968] (.node [65568,113184,344064,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil) (.node [65568,113184,430348,902208,3227782,5521457,8242423,8532035,11083800,13501056,15731968] .nil .nil)) (.node [65568,113184,430348,902208,5521457,7684279,8532035,11083800,12148894,13501056,15731968] (.node [65568,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16216311] .nil .nil) .nil)) (.node [73736,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] (.node [73728,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16076215] (.node [73728,113184,430348,902208,3227782,5521457,8242423,8532035,11083800,13501056,15731968] .nil .nil) (.node [73728,113184,430348,902208,5521457,7684279,8532035,11083800,12148894,13501056,15731968] .nil .nil)) (.node [81920,113184,430348,902208,3227782,5521457,8242423,8532035,11083800,13501056,15731968] (.node [81920,113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) .nil)))
theorem R12abaab_ok : tall (refOK cpF 12) R12abaab = true := by decide +kernel
def R12abaa : Tree := .node [65540,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] R12abaaa R12abaab
theorem R12abaa_ok : tall (refOK cpF 12) R12abaa = true :=
  tall_node _ _ _ _ R12abaaa_ok (by decide +kernel) R12abaab_ok
def R12abab : Tree := (.node [113184,344064,430348,902208,3227782,7684279,8532035,11083800,13501056,14566065,15731968] (.node [113184,113248,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] (.node [98336,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] (.node [98304,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16076215] (.node [98304,113184,430348,902208,3227782,5521457,8242423,8532035,11083800,13501056,15731968] .nil .nil) (.node [98336,113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)) (.node [110592,113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [100352,113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) .nil)) (.node [113184,344064,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16605375] (.node [113184,344064,430348,902208,3227782,5521457,7731895,8532035,11083800,13501056,15731968] (.node [113184,344064,430348,902208,2162704,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,344064,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16076215] .nil .nil)) (.node [113184,344064,430348,902208,3227782,7684279,8532035,11083800,13501056,14053491,15731968] (.node [113184,344064,430348,902208,3227782,5689661,7684279,8532035,11083800,13501056,15731968] .nil .nil) .nil))) (.node [113184,430348,506668,902208,3227782,5521457,8532035,11083800,11759815,13501056,15731968] (.node [113184,430348,506668,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731968] (.node [113184,430348,506668,902208,2162704,3227782,5521457,8532035,11083800,13501056,15731968] (.node [113184,391712,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,506668,902208,3227782,3275430,5521457,8532035,11083800,13501056,15731968] .nil .nil)) (.node [113184,430348,506668,902208,3227782,5521457,8532035,11083800,11219035,13501056,15731968] (.node [113184,430348,506668,902208,3227782,5521457,8532035,11083800,11123256,13501056,15731968] .nil .nil) .nil)) (.node [113184,430348,589824,902208,3227782,5521457,8532035,11083800,13501056,15731968,16076215] (.node [113184,430348,506668,902208,3227782,5521457,8532035,11083800,13501056,15731968,16330008] (.node [113184,430348,506668,902208,3227782,5521457,8532035,11083800,12148894,13501056,15731968] .nil .nil) (.node [113184,430348,589824,902208,3227782,5521457,8242423,8532035,11083800,13501056,15731968] .nil .nil)) (.node [113184,430348,902208,917088,3227782,5521457,8242423,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,917088,3227782,4048070,5521457,8532035,11083800,13501056,15731968] .nil .nil) .nil))))
theorem R12abab_ok : tall (refOK cpF 12) R12abab = true := by decide +kernel
def R12aba : Tree := .node [81920,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16076215] R12abaa R12abab
theorem R12aba_ok : tall (refOK cpF 12) R12aba = true :=
  tall_node _ _ _ _ R12abaa_ok (by decide +kernel) R12abab_ok
def R12abba : Tree := (.node [113184,430348,902208,2162688,2162704,3227782,5521457,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,1064960,2162704,3227782,5521457,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,917088,3227782,7684279,8532035,11083800,13501056,14053491,15731968] (.node [113184,430348,902208,917088,3227782,5521457,8532035,11083800,13501056,15731968,16076215] (.node [113184,430348,902208,917088,3227782,5521457,8532035,11083800,13501056,15731968,15875395] .nil .nil) (.node [113184,430348,902208,917088,3227782,5689661,7684279,8532035,11083800,13501056,15731968] .nil .nil)) (.node [113184,430348,902208,1048428,3227782,5521457,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,917088,5521457,7684279,8532035,11083800,12148894,13501056,15731968] .nil .nil) .nil)) (.node [113184,430348,902208,1064960,3227782,7684279,8532035,11083800,13501056,14566065,15731968] (.node [113184,430348,902208,1064960,3227782,5689661,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,1064960,3227782,5521457,8532035,11083800,13501056,15731968,16076215] .nil .nil) (.node [113184,430348,902208,1064960,3227782,7684279,8532035,11083800,13501056,14053491,15731968] .nil .nil)) (.node [113184,430348,902208,2097152,3227782,5521457,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,2097152,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) .nil))) (.node [113184,430348,902208,2162704,3227782,5521457,8532035,8912896,11083800,13501056,15731968] (.node [113184,430348,902208,2162704,3227782,5521457,7340032,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,2162688,3227782,5521457,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,2162688,3227782,5521457,8242423,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,902208,2162688,3227782,5521457,8532035,11083800,13501056,15731968,16076215] .nil .nil)) (.node [113184,430348,902208,2162704,3227782,5521457,8388608,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,2162704,3227782,5521457,8242423,8532035,11083800,13501056,15731968] .nil .nil) .nil)) (.node [113184,430348,902208,2162704,3227782,5521457,8532035,11083800,13501056,15731968,15875395] (.node [113184,430348,902208,2162704,3227782,5521457,8532035,11083800,13501056,15671960,15731968] (.node [113184,430348,902208,2162704,3227782,5521457,8532035,9434179,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,902208,2162704,3227782,5521457,8532035,11083800,13501056,15731968,15843104] .nil .nil)) (.node [113184,430348,902208,2162704,3227782,5521457,8532035,11083800,13501056,15731968,16216311] (.node [113184,430348,902208,2162704,3227782,5521457,8532035,11083800,13501056,15731968,16076215] .nil .nil) .nil))))
theorem R12abba_ok : tall (refOK cpF 12) R12abba = true := by decide +kernel
def R12abbbaa : Tree := (.node [113184,430348,902208,2686992,3227782,5521457,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,2162704,3227782,5521457,8532035,13501056,15731968,16330008] (.node [113184,430348,902208,2162704,3227782,5521457,8532035,12148894,13501056,15731968] .nil .nil) (.node [113184,430348,902208,2162704,5521457,7684279,8532035,12148894,13501056,15731968] .nil .nil)) (.node [113184,430348,902208,3145728,3227782,5521457,8532035,11083800,13501056,15731968,16076215] (.node [113184,430348,902208,3145728,3227782,5521457,8242423,8532035,11083800,13501056,15731968] .nil .nil) .nil))
theorem R12abbbaa_ok : tall (refOK cpF 12) R12abbbaa = true := by decide +kernel
def R12abbbab : Tree := (.node [113184,430348,902208,3227782,3227798,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,3227783,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,3227648,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,902208,3227782,3227783,5521457,8532035,11083800,13501056,15731968] .nil .nil)) (.node [113184,430348,902208,3227782,3227814,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,3227798,5521457,8532035,11083800,13501056,15731968] .nil .nil) .nil))
theorem R12abbbab_ok : tall (refOK cpF 12) R12abbbab = true := by decide +kernel
def R12abbba : Tree := .node [113184,430348,902208,3145730,3227782,5521457,8532035,11083800,13501056,15731968] R12abbbaa R12abbbab
theorem R12abbba_ok : tall (refOK cpF 12) R12abbba = true :=
  tall_node _ _ _ _ R12abbbaa_ok (by decide +kernel) R12abbbab_ok
def R12abbbb : Tree := (.node [113184,430348,902208,3227782,3658126,5521457,8242423,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,3275430,7684279,8532035,11083800,13501056,14566065,15731968] (.node [113184,430348,902208,3227782,3275430,5521457,8242423,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,3275430,5521457,7731895,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,902208,3227782,3275430,5521457,8532035,11083800,13501056,15731968,16076215] .nil .nil)) (.node [113184,430348,902208,3227782,3489926,5521457,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,3489926,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) .nil)) (.node [113184,430348,902208,3227782,3668910,5521457,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,3658126,7684279,8532035,11083800,13501056,14566065,15731968] (.node [113184,430348,902208,3227782,3658126,5521457,8532035,11083800,13501056,15731968,16076215] .nil .nil) (.node [113184,430348,902208,3227782,3668910,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)) (.node [113184,430348,902208,3227782,4048070,5521457,8532035,11083800,13501056,15731968,15875395] (.node [113184,430348,902208,3227782,4048070,5521457,8242423,8532035,11083800,13501056,15731968] .nil .nil) .nil)))
theorem R12abbbb_ok : tall (refOK cpF 12) R12abbbb = true := by decide +kernel
def R12abbb : Tree := .node [113184,430348,902208,3227782,3228806,5521457,8532035,11083800,13501056,15731968] R12abbba R12abbbb
theorem R12abbb_ok : tall (refOK cpF 12) R12abbb = true :=
  tall_node _ _ _ _ R12abbba_ok (by decide +kernel) R12abbbb_ok
def R12abb : Tree := .node [113184,430348,902208,2162704,3227782,5521457,8532035,11083800,13501056,15731968,16633152] R12abba R12abbb
theorem R12abb_ok : tall (refOK cpF 12) R12abb = true :=
  tall_node _ _ _ _ R12abba_ok (by decide +kernel) R12abbb_ok
def R12ab : Tree := .node [113184,430348,902208,917088,3227782,5521457,8532035,8827215,11083800,13501056,15731968] R12aba R12abb
theorem R12ab_ok : tall (refOK cpF 12) R12ab = true :=
  tall_node _ _ _ _ R12aba_ok (by decide +kernel) R12abb_ok
def R12a : Tree := .node [12288,113184,430348,902208,3227782,5521457,8242423,8532035,11083800,13501056,15731968] R12aa R12ab
theorem R12a_ok : tall (refOK cpF 12) R12a = true :=
  tall_node _ _ _ _ R12aa_ok (by decide +kernel) R12ab_ok
def R12baaa : Tree := (.node [113184,430348,902208,3227782,5521457,7684279,8532035,9434447,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,7422086,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,4183502,5521457,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,4062950,5521457,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,4062950,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,902208,3227782,4183502,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)) (.node [113184,430348,902208,3227782,5521457,7340032,8532035,11083800,13501056,15731968,16076215] (.node [113184,430348,902208,3227782,5521457,7340032,7731895,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,902208,3227782,5521457,7340032,8532035,11083800,13501056,15731968,16605375] .nil .nil))) (.node [113184,430348,902208,3227782,5521457,7684279,8257271,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,7684145,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,7684145,7684279,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,902208,3227782,5521457,7684279,7731895,8532035,11083800,13501056,15731968] .nil .nil)) (.node [113184,430348,902208,3227782,5521457,7684279,8532035,8986624,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,7684279,8388608,8532035,11083800,13501056,15731968] .nil .nil) .nil))) (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,11531355,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,11402872,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,11254395,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11075584,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,11362328,13501056,15731968] .nil .nil)) (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,11516732,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,11514207,13501056,15731968] .nil .nil) .nil)) (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,12054991,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,11616390,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,11531612,13501056,15731968] .nil .nil) (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,11795175,13501056,15731968] .nil .nil)) (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,12284127,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,12188350,13501056,15731968] .nil .nil) .nil))))
theorem R12baaa_ok : tall (refOK cpF 12) R12baaa = true := by decide +kernel
def R12baab : Tree := (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,16367416] (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,15957447] (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15728640,15731968] (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,12580039,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,12579230,13501056,15731968] .nil .nil) (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15709084,15731968] .nil .nil)) (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,15859622] (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,15797504] .nil .nil) .nil)) (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,16219639] (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,16121649] (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,15974243] .nil .nil) (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,16121783] .nil .nil)) (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,16326680] (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,16249343] .nil .nil) .nil))) (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,16639097] (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,16608703] (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,16605375] (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,16465243] .nil .nil) (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,16608569] .nil .nil)) (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,16633335] (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,16633201] .nil .nil) .nil)) (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,16644799] (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,16641368] (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,16639231] .nil .nil) (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,16644665] .nil .nil)) (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,16736926] (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,16645984] .nil .nil) .nil))))
theorem R12baab_ok : tall (refOK cpF 12) R12baab = true := by decide +kernel
def R12baa : Tree := .node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,12444894,13501056,15731968] R12baaa R12baab
theorem R12baa_ok : tall (refOK cpF 12) R12baa = true :=
  tall_node _ _ _ _ R12baaa_ok (by decide +kernel) R12baab_ok
def R12baba : Tree := (.node [113184,430348,902208,3227782,5521457,7731895,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15814022,16162060] (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,16773567] (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,16760092] (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,16740607] .nil .nil) (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,16773437] .nil .nil)) (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,16776515] (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,16774391] .nil .nil) .nil)) (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,14566065,15671960,15731968] (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13538188,15671960,15731968] (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15814022,16650112] .nil .nil) (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13616832,15731968,16650112] .nil .nil)) (.node [113184,430348,902208,3227782,5521457,7731895,8532035,9434179,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,7731895,8242423,8532035,11083800,13501056,15731968] .nil .nil) .nil))) (.node [113184,430348,902208,3227782,5521457,8242423,8532035,11083800,11219035,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,8242423,8532035,8632931,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,7731895,8532035,11083800,13501056,15731968,16216311] (.node [113184,430348,902208,3227782,5521457,7731895,8532035,11083800,13501056,15731968,16076215] .nil .nil) (.node [113184,430348,902208,3227782,5521457,8242423,8396800,8532035,11083800,13501056,15731968] .nil .nil)) (.node [113184,430348,902208,3227782,5521457,8242423,8532035,11083800,11123256,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,8242423,8532035,10485760,11083800,13501056,15731968] .nil .nil) .nil)) (.node [113184,430348,902208,3227782,5521457,8242423,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,8242423,8532035,11083800,11514140,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,8242423,8532035,11083800,11396184,13501056,15731968] .nil .nil) (.node [113184,430348,902208,3227782,5521457,8242423,8532035,11083800,11759815,13501056,15731968] .nil .nil)) (.node [113184,430348,902208,3227782,5521457,8242423,8532035,11083800,13501056,15731968,16605241] (.node [113184,430348,902208,3227782,5521457,8242423,8532035,11083800,13501056,15731968,15843104] .nil .nil) .nil))))
theorem R12baba_ok : tall (refOK cpF 12) R12baba = true := by decide +kernel
def R12babba : Tree := (.node [113184,430348,902208,3227782,5521457,8532035,10485760,11083800,13501056,15731968,16076215] (.node [113184,430348,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731968,15875395] (.node [113184,430348,902208,3227782,5521457,8396800,8532035,11083800,13501056,15731968,16076215] (.node [113184,430348,902208,3227782,5521457,8388608,8532035,11083800,13501056,15731968,16076215] .nil .nil) (.node [113184,430348,902208,3227782,5521457,8532035,8632931,11083800,13501056,13538188,15731968] .nil .nil)) (.node [113184,430348,902208,3227782,5521457,8532035,9434447,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,8532035,8912896,11083800,13501056,15731968,16076215] .nil .nil) .nil)) (.node [113184,430348,902208,3227782,5521457,8532035,11083800,11083864,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,8532035,10551312,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,8532035,10493952,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,902208,3227782,5521457,8532035,11083800,11083803,13501056,15731968] .nil .nil)) (.node [113184,430348,902208,3227782,5521457,8532035,11083800,11123256,12148894,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,8532035,11083800,11084824,13501056,15731968] .nil .nil) .nil)))
theorem R12babba_ok : tall (refOK cpF 12) R12babba = true := by decide +kernel
def R12babbb : Tree := (.node [113184,430348,902208,3227782,5521457,8532035,11083800,11514140,13501056,15731968,16076215] (.node [113184,430348,902208,3227782,5521457,8532035,11083800,11254395,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,8532035,11083800,11219035,13501056,15731968,15875395] (.node [113184,430348,902208,3227782,5521457,8532035,11083800,11123256,13501056,15731968,16076215] .nil .nil) (.node [113184,430348,902208,3227782,5521457,8532035,11083800,11219035,13501056,15731968,16076215] .nil .nil)) (.node [113184,430348,902208,3227782,5521457,8532035,11083800,11402872,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,8532035,11083800,11396184,13501056,15731968,16076215] .nil .nil) .nil)) (.node [113184,430348,902208,3227782,5521457,8532035,11083800,11795175,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,8532035,11083800,11516732,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,8532035,11083800,11514207,13501056,15731968] .nil .nil) (.node [113184,430348,902208,3227782,5521457,8532035,11083800,11759815,13501056,15731968,16076215] .nil .nil)) (.node [113184,430348,902208,3227782,5521457,8532035,11083800,12148894,13501056,15731968,16010545] (.node [113184,430348,902208,3227782,5521457,8532035,11083800,12148894,13501056,15731968,15875395] .nil .nil) .nil)))
theorem R12babbb_ok : tall (refOK cpF 12) R12babbb = true := by decide +kernel
def R12babb : Tree := .node [113184,430348,902208,3227782,5521457,8532035,11083800,11123256,13501056,15731968,15875395] R12babba R12babbb
theorem R12babb_ok : tall (refOK cpF 12) R12babb = true :=
  tall_node _ _ _ _ R12babba_ok (by decide +kernel) R12babbb_ok
def R12bab : Tree := .node [113184,430348,902208,3227782,5521457,8257271,8532035,11083800,13501056,15731968] R12baba R12babb
theorem R12bab_ok : tall (refOK cpF 12) R12bab = true :=
  tall_node _ _ _ _ R12baba_ok (by decide +kernel) R12babb_ok
def R12ba : Tree := .node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,16740475] R12baa R12bab
theorem R12ba_ok : tall (refOK cpF 12) R12ba = true :=
  tall_node _ _ _ _ R12baa_ok (by decide +kernel) R12bab_ok
def R12bbaaaa : Tree := (.node [113184,430348,902208,3227782,5521457,8532035,11083800,12444894,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,8532035,11083800,12188350,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,8532035,11083800,12148894,13501056,15731968,16605375] .nil .nil) (.node [113184,430348,902208,3227782,5521457,8532035,11083800,12284127,13501056,15731968] .nil .nil)) (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,15814022,15875395] (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15671960,15731968,16076215] .nil .nil) .nil))
theorem R12bbaaaa_ok : tall (refOK cpF 12) R12bbaaaa = true := by decide +kernel
def R12bbaaab : Tree := (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,15957447] (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,15859622] (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,15843104,16076215] .nil .nil) (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,15875395,16330008] .nil .nil)) (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16072887] (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,15974243] .nil .nil) .nil))
theorem R12bbaaab_ok : tall (refOK cpF 12) R12bbaaab = true := by decide +kernel
def R12bbaaa : Tree := .node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,15814022,16076215] R12bbaaaa R12bbaaab
theorem R12bbaaa_ok : tall (refOK cpF 12) R12bbaaa = true :=
  tall_node _ _ _ _ R12bbaaaa_ok (by decide +kernel) R12bbaaab_ok
def R12bbaab : Tree := (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16121783] (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16076215,16605375] (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16076215,16330008] (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16076215,16216311] .nil .nil) (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16076215,16605241] .nil .nil)) (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16076215,16633152] (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16076215,16608703] .nil .nil) .nil)) (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16367416] (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16219639] (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16216311,16605375] .nil .nil) (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16346526] .nil .nil)) (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16605375] (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16465243] .nil .nil) .nil)))
theorem R12bbaab_ok : tall (refOK cpF 12) R12bbaab = true := by decide +kernel
def R12bbaa : Tree := .node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16076215,16121783] R12bbaaa R12bbaab
theorem R12bbaa_ok : tall (refOK cpF 12) R12bbaa = true :=
  tall_node _ _ _ _ R12bbaaa_ok (by decide +kernel) R12bbaab_ok
def R12bbabaa : Tree := (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16639231] (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16633201] (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16608703] .nil .nil) (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16633335] .nil .nil)) (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15814022,15875395] (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16774391] .nil .nil) .nil))
theorem R12bbabaa_ok : tall (refOK cpF 12) R12bbabaa = true := by decide +kernel
def R12bbababaa : Tree := (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501059,15731968] .nil .nil)
theorem R12bbababaa_ok : tall (refOK cpF 12) R12bbababaa = true := by decide +kernel
def R12bbababab : Tree := (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13502080,15731968] .nil .nil)
theorem R12bbababab_ok : tall (refOK cpF 12) R12bbababab = true := by decide +kernel
def R12bbababa : Tree := .node [113184,430348,902208,3227782,5521457,8532035,11083800,13501120,15731968] R12bbababaa R12bbababab
theorem R12bbababa_ok : tall (refOK cpF 12) R12bbababa = true :=
  tall_node _ _ _ _ R12bbababaa_ok (by decide +kernel) R12bbababab_ok
def R12bbababb : Tree := (.node [113184,430348,902208,3227782,5521457,8632931,11083800,13501056,13513411,15731968] (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13538188,15731968,16650112] .nil .nil) .nil)
theorem R12bbababb_ok : tall (refOK cpF 12) R12bbababb = true := by decide +kernel
def R12bbabab : Tree := .node [113184,430348,902208,3227782,5521457,8532035,11083800,13513411,14566065,15731968] R12bbababa R12bbababb
theorem R12bbabab_ok : tall (refOK cpF 12) R12bbabab = true :=
  tall_node _ _ _ _ R12bbababa_ok (by decide +kernel) R12bbababb_ok
def R12bbaba : Tree := .node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15814022,16650112] R12bbabaa R12bbabab
theorem R12bbaba_ok : tall (refOK cpF 12) R12bbaba = true :=
  tall_node _ _ _ _ R12bbabaa_ok (by decide +kernel) R12bbabab_ok
def R12bbabbaaa : Tree := (.node [113184,430348,902208,3227782,5521459,8532035,11083800,13501056,15731968] .nil .nil)
theorem R12bbabbaaa_ok : tall (refOK cpF 12) R12bbabbaaa = true := by decide +kernel
def R12bbabbaab : Tree := (.node [113184,430348,902208,3227782,5522481,8532035,11083800,13501056,15731968] .nil .nil)
theorem R12bbabbaab_ok : tall (refOK cpF 12) R12bbabbaab = true := by decide +kernel
def R12bbabbaa : Tree := .node [113184,430348,902208,3227782,5521585,8532035,11083800,13501056,15731968] R12bbabbaaa R12bbabbaab
theorem R12bbabbaa_ok : tall (refOK cpF 12) R12bbabbaa = true :=
  tall_node _ _ _ _ R12bbabbaaa_ok (by decide +kernel) R12bbabbaab_ok
def R12bbabbab : Tree := (.node [113184,430348,902208,3227782,5689661,7340032,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5634609,7684279,8532035,11083800,13501056,15731968,16010545] .nil .nil) .nil)
theorem R12bbabbab_ok : tall (refOK cpF 12) R12bbabbab = true := by decide +kernel
def R12bbabba : Tree := .node [113184,430348,902208,3227782,5558321,7684279,8532035,11083800,13501056,15731968] R12bbabbaa R12bbabbab
theorem R12bbabba_ok : tall (refOK cpF 12) R12bbabba = true :=
  tall_node _ _ _ _ R12bbabbaa_ok (by decide +kernel) R12bbabbab_ok
def R12bbabbb : Tree := (.node [113184,430348,902208,3227782,5689661,7684279,8532035,9434179,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5689661,7684279,8532035,8827215,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5689661,7684279,8388608,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,902208,3227782,5689661,7684279,8532035,8912896,11083800,13501056,15731968] .nil .nil)) (.node [113184,430348,902208,3227782,5689661,7684279,8532035,11083800,13501056,15731968,15843104] (.node [113184,430348,902208,3227782,5689661,7684279,8532035,11083800,13501056,15671960,15731968] .nil .nil) .nil))
theorem R12bbabbb_ok : tall (refOK cpF 12) R12bbabbb = true := by decide +kernel
def R12bbabb : Tree := .node [113184,430348,902208,3227782,5689661,7684279,7852479,8532035,11083800,13501056,15731968] R12bbabba R12bbabbb
theorem R12bbabb_ok : tall (refOK cpF 12) R12bbabb = true :=
  tall_node _ _ _ _ R12bbabba_ok (by decide +kernel) R12bbabbb_ok
def R12bbab : Tree := .node [113184,430348,902208,3227782,5521457,8632931,11083800,13501056,15731968,15875395] R12bbaba R12bbabb
theorem R12bbab_ok : tall (refOK cpF 12) R12bbab = true :=
  tall_node _ _ _ _ R12bbaba_ok (by decide +kernel) R12bbabb_ok
def R12bba : Tree := .node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16608569] R12bbaa R12bbab
theorem R12bba_ok : tall (refOK cpF 12) R12bba = true :=
  tall_node _ _ _ _ R12bbaa_ok (by decide +kernel) R12bbab_ok
def R12bbbaa : Tree := (.node [113184,430348,902208,3227782,7340032,7684279,8532035,11083800,13501056,14566065,15731968] (.node [113184,430348,902208,3227782,5689661,8532035,11083800,13501056,15731968,16010545] (.node [113184,430348,902208,3227782,5689661,7684279,8532035,11083800,13501056,15731968,16216311] (.node [113184,430348,902208,3227782,5689661,7684279,8532035,11083800,13501056,15731968,16076215] .nil .nil) (.node [113184,430348,902208,3227782,5689661,7684279,8532035,11083800,13501056,15731968,16633152] .nil .nil)) (.node [113184,430348,902208,3227782,7340032,7684279,8532035,11083800,13501056,14053491,15731968] (.node [113184,430348,902208,3227782,6145137,8532035,11083800,13501056,15731968,16010545] .nil .nil) .nil)) (.node [113184,430348,902208,3227782,7684279,8532035,8912896,11083800,13501056,14053491,15731968] (.node [113184,430348,902208,3227782,7684279,8388608,8532035,11083800,13501056,14566065,15731968] (.node [113184,430348,902208,3227782,7684279,8388608,8532035,11083800,13501056,14053491,15731968] .nil .nil) (.node [113184,430348,902208,3227782,7684279,8532035,8827215,11083800,13501056,14053491,15731968] .nil .nil)) (.node [113184,430348,902208,3227782,7684279,8532035,9434179,11083800,13501056,14053491,15731968] (.node [113184,430348,902208,3227782,7684279,8532035,8912896,11083800,13501056,14566065,15731968] .nil .nil) .nil)))
theorem R12bbbaa_ok : tall (refOK cpF 12) R12bbbaa = true := by decide +kernel
def R12bbbab : Tree := (.node [113184,430348,902208,3227782,7684279,8532035,11083800,13501056,14053491,15731968,16216311] (.node [113184,430348,902208,3227782,7684279,8532035,11083800,13501056,14053491,15731968,15875395] (.node [113184,430348,902208,3227782,7684279,8532035,11083800,13501056,14053491,15671960,15731968] (.node [113184,430348,902208,3227782,7684279,8532035,11083800,13501056,13538188,14566065,15731968] .nil .nil) (.node [113184,430348,902208,3227782,7684279,8532035,11083800,13501056,14053491,15731968,15814022] .nil .nil)) (.node [113184,430348,902208,3227782,7684279,8532035,11083800,13501056,14053491,15731968,16076215] (.node [113184,430348,902208,3227782,7684279,8532035,11083800,13501056,14053491,15731968,16010545] .nil .nil) .nil)) (.node [113184,430348,902208,3227782,7684279,8532035,11083800,13501056,14566065,15671960,15731968] (.node [113184,430348,902208,3227782,7684279,8532035,11083800,13501056,14086527,15731968] (.node [113184,430348,902208,3227782,7684279,8532035,11083800,13501056,14053491,15731968,16633152] .nil .nil) (.node [113184,430348,902208,3227782,7684279,8532035,11083800,13501056,14434353,15731968] .nil .nil)) (.node [113184,430348,902208,3227782,7684279,8532035,11083800,13501056,14566065,15731968,15875395] (.node [113184,430348,902208,3227782,7684279,8532035,11083800,13501056,14566065,15731968,15814022] .nil .nil) .nil)))
theorem R12bbbab_ok : tall (refOK cpF 12) R12bbbab = true := by decide +kernel
def R12bbba : Tree := .node [113184,430348,902208,3227782,7684279,8532035,9434179,11083800,13501056,14566065,15731968] R12bbbaa R12bbbab
theorem R12bbba_ok : tall (refOK cpF 12) R12bbba = true :=
  tall_node _ _ _ _ R12bbbaa_ok (by decide +kernel) R12bbbab_ok
def R12bbbbaa : Tree := (.node [113184,430348,902208,3227782,7684279,8532035,11083800,13501056,14566065,15731968,16728759] (.node [113184,430348,902208,3227782,7684279,8532035,11083800,13501056,14566065,15731968,16216311] (.node [113184,430348,902208,3227782,7684279,8532035,11083800,13501056,14566065,15731968,16162060] .nil .nil) (.node [113184,430348,902208,3227782,7684279,8532035,11083800,13501056,14566065,15731968,16633152] .nil .nil)) (.node [113184,430348,902208,3227782,7684279,8532035,11083800,13501056,14603197,15731968] (.node [113184,430348,902208,3227782,7684279,8532035,11083800,13501056,14578419,15731968] .nil .nil) .nil))
theorem R12bbbbaa_ok : tall (refOK cpF 12) R12bbbbaa = true := by decide +kernel
def R12bbbbab : Tree := (.node [113184,430348,902208,3227782,7684279,8632931,11083800,13501056,14053491,15731968] (.node [113184,430348,902208,3227782,7684279,8532035,11083800,13613728,14566065,15731968] (.node [113184,430348,902208,3227782,7684279,8532035,11083800,13538188,14566065,15731968] .nil .nil) (.node [113184,430348,902208,3227782,7684279,8532035,11083800,14566065,15671960,15731968] .nil .nil)) (.node [113184,430348,902208,3275430,7684279,8532035,11083800,13501056,14053491,15731968] (.node [113184,430348,902208,3227782,8242423,8532035,11083800,13501056,14053491,15731968] .nil .nil) .nil))
theorem R12bbbbab_ok : tall (refOK cpF 12) R12bbbbab = true := by decide +kernel
def R12bbbba : Tree := .node [113184,430348,902208,3227782,7684279,8532035,11083800,13513411,14566065,15731968] R12bbbbaa R12bbbbab
theorem R12bbbba_ok : tall (refOK cpF 12) R12bbbba = true :=
  tall_node _ _ _ _ R12bbbbaa_ok (by decide +kernel) R12bbbbab_ok
def R12bbbbba : Tree := (.node [113184,430348,917088,3227782,5521457,7684279,8532035,11083800,13501056,15731968,16633152] (.node [113184,430348,917088,3227782,5521457,6145137,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,7684279,8532035,11083800,11759815,13501056,14566065,15731968] .nil .nil) (.node [113184,430348,917088,3227782,5521457,7684279,8532035,11083800,13501056,13616832,15731968] .nil .nil)) (.node [113184,430348,3227782,5521457,8242423,8532035,9434179,11083800,13501056,15731968] (.node [113184,430348,3227782,4048070,5521457,7684279,8532035,9434179,11083800,13501056,15731968] .nil .nil) .nil))
theorem R12bbbbba_ok : tall (refOK cpF 12) R12bbbbba = true := by decide +kernel
def R12bbbbbb : Tree := (.node [113184,902208,1037644,3227782,5521457,8532035,8827215,11083800,13501056,15731968] (.node [113184,506668,902208,3227782,5521457,8532035,11083800,13501056,13538188,15731968] (.node [113184,506668,902208,3227782,5521457,5689661,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,506668,902208,3227782,5521457,8532035,11083800,13501056,15731968,16162060] .nil .nil)) (.node [113184,902208,3227782,5689661,7684279,8532035,11083800,11514140,13501056,15731968] (.node [113184,902208,3227782,5521457,5689661,8532035,8827215,11083800,13501056,15731968] .nil .nil) .nil))
theorem R12bbbbbb_ok : tall (refOK cpF 12) R12bbbbbb = true := by decide +kernel
def R12bbbbb : Tree := .node [113184,430412,902208,3227782,5521457,8532035,11083800,13501056,15731968] R12bbbbba R12bbbbbb
theorem R12bbbbb_ok : tall (refOK cpF 12) R12bbbbb = true :=
  tall_node _ _ _ _ R12bbbbba_ok (by decide +kernel) R12bbbbbb_ok
def R12bbbb : Tree := .node [113184,430348,902208,3275430,7684279,8532035,11083800,13501056,14566065,15731968] R12bbbba R12bbbbb
theorem R12bbbb_ok : tall (refOK cpF 12) R12bbbb = true :=
  tall_node _ _ _ _ R12bbbba_ok (by decide +kernel) R12bbbbb_ok
def R12bbb : Tree := .node [113184,430348,902208,3227782,7684279,8532035,11083800,13501056,14566065,15731968,16076215] R12bbba R12bbbb
theorem R12bbb_ok : tall (refOK cpF 12) R12bbb = true :=
  tall_node _ _ _ _ R12bbba_ok (by decide +kernel) R12bbbb_ok
def R12bb : Tree := .node [113184,430348,902208,3227782,5689661,7684279,8532035,11083800,13501056,15731968,16010545] R12bba R12bbb
theorem R12bb_ok : tall (refOK cpF 12) R12bb = true :=
  tall_node _ _ _ _ R12bba_ok (by decide +kernel) R12bbb_ok
def R12b : Tree := .node [113184,430348,902208,3227782,5521457,8532035,11083800,12148894,13501056,15731968,16076215] R12ba R12bb
theorem R12b_ok : tall (refOK cpF 12) R12b = true :=
  tall_node _ _ _ _ R12ba_ok (by decide +kernel) R12bb_ok
def R12 : Tree := .node [113184,430348,902208,3227782,4048070,5521457,8532035,11083800,13501056,15731968,16076215] R12a R12b
theorem R12_ok : tall (refOK cpF 12) R12 = true :=
  tall_node _ _ _ _ R12a_ok (by decide +kernel) R12b_ok
def T13aaaaaa : Tree := (.node [1,113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T13aaaaaa_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13aaaaaa = true := by decide +kernel
def T13aaaaab : Tree := .nil
theorem T13aaaaab_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13aaaaab = true := by decide +kernel
def T13aaaaa : Tree := .node [3,113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T13aaaaaa T13aaaaab
theorem T13aaaaa_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13aaaaa = true :=
  tall_node _ _ _ _ T13aaaaaa_ok (by decide +kernel) T13aaaaab_ok
def T13aaaab : Tree := (.node [4,113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T13aaaab_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13aaaab = true := by decide +kernel
def T13aaaa : Tree := .node [3,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] T13aaaaa T13aaaab
theorem T13aaaa_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13aaaa = true :=
  tall_node _ _ _ _ T13aaaaa_ok (by decide +kernel) T13aaaab_ok
def T13aaabaa : Tree := (.node [8,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil)
theorem T13aaabaa_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13aaabaa = true := by decide +kernel
def T13aaabab : Tree := .nil
theorem T13aaabab_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13aaabab = true := by decide +kernel
def T13aaaba : Tree := .node [16,113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T13aaabaa T13aaabab
theorem T13aaaba_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13aaaba = true :=
  tall_node _ _ _ _ T13aaabaa_ok (by decide +kernel) T13aaabab_ok
def T13aaabb : Tree := (.node [64,113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T13aaabb_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13aaabb = true := by decide +kernel
def T13aaab : Tree := .node [16,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] T13aaaba T13aaabb
theorem T13aaab_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13aaab = true :=
  tall_node _ _ _ _ T13aaaba_ok (by decide +kernel) T13aaabb_ok
def T13aaa : Tree := .node [8,113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T13aaaa T13aaab
theorem T13aaa_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13aaa = true :=
  tall_node _ _ _ _ T13aaaa_ok (by decide +kernel) T13aaab_ok
def T13aabaaa : Tree := (.node [256,113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T13aabaaa_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13aabaaa = true := by decide +kernel
def T13aabaab : Tree := .nil
theorem T13aabaab_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13aabaab = true := by decide +kernel
def T13aabaa : Tree := .node [1024,113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T13aabaaa T13aabaab
theorem T13aabaa_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13aabaa = true :=
  tall_node _ _ _ _ T13aabaaa_ok (by decide +kernel) T13aabaab_ok
def T13aabab : Tree := (.node [12288,113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T13aabab_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13aabab = true := by decide +kernel
def T13aaba : Tree := .node [1024,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] T13aabaa T13aabab
theorem T13aaba_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13aaba = true :=
  tall_node _ _ _ _ T13aabaa_ok (by decide +kernel) T13aabab_ok
def T13aabba : Tree := (.node [65536,113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T13aabba_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13aabba = true := by decide +kernel
def T13aabbb : Tree := (.node [73728,113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T13aabbb_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13aabbb = true := by decide +kernel
def T13aabb : Tree := .node [65568,113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T13aabba T13aabbb
theorem T13aabb_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13aabb = true :=
  tall_node _ _ _ _ T13aabba_ok (by decide +kernel) T13aabbb_ok
def T13aab : Tree := .node [36864,113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T13aaba T13aabb
theorem T13aab_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13aab = true :=
  tall_node _ _ _ _ T13aaba_ok (by decide +kernel) T13aabb_ok
def T13aa : Tree := .node [64,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] T13aaa T13aab
theorem T13aa_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13aa = true :=
  tall_node _ _ _ _ T13aaa_ok (by decide +kernel) T13aab_ok
def T13abaaaa : Tree := (.node [98304,113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T13abaaaa_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13abaaaa = true := by decide +kernel
def T13abaaab : Tree := .nil
theorem T13abaaab_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13abaaab = true := by decide +kernel
def T13abaaa : Tree := .node [113184,344064,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T13abaaaa T13abaaab
theorem T13abaaa_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13abaaa = true :=
  tall_node _ _ _ _ T13abaaaa_ok (by decide +kernel) T13abaaab_ok
def T13abaab : Tree := (.node [113184,430348,506668,902208,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil)
theorem T13abaab_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13abaab = true := by decide +kernel
def T13abaa : Tree := .node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T13abaaa T13abaab
theorem T13abaa_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13abaa = true :=
  tall_node _ _ _ _ T13abaaa_ok (by decide +kernel) T13abaab_ok
def T13ababa : Tree := (.node [113184,430348,902208,917088,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T13ababa_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13ababa = true := by decide +kernel
def T13ababb : Tree := (.node [113184,430348,902208,1064960,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T13ababb_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13ababb = true := by decide +kernel
def T13abab : Tree := .node [113184,430348,902208,917088,3227782,5521457,8532035,11083800,13501056,15731968] T13ababa T13ababb
theorem T13abab_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13abab = true :=
  tall_node _ _ _ _ T13ababa_ok (by decide +kernel) T13ababb_ok
def T13aba : Tree := .node [113184,430348,589824,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T13abaa T13abab
theorem T13aba_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13aba = true :=
  tall_node _ _ _ _ T13abaa_ok (by decide +kernel) T13abab_ok
def T13abbaaa : Tree := (.node [113184,430348,902208,2162704,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T13abbaaa_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13abbaaa = true := by decide +kernel
def T13abbaab : Tree := .nil
theorem T13abbaab_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13abbaab = true := by decide +kernel
def T13abbaa : Tree := .node [113184,430348,902208,2162704,3227782,5521457,8532035,11083800,13501056,15731968] T13abbaaa T13abbaab
theorem T13abbaa_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13abbaa = true :=
  tall_node _ _ _ _ T13abbaaa_ok (by decide +kernel) T13abbaab_ok
def T13abbab : Tree := (.node [113184,430348,902208,3227782,3275430,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T13abbab_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13abbab = true := by decide +kernel
def T13abba : Tree := .node [113184,430348,902208,3145728,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T13abbaa T13abbab
theorem T13abba_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13abba = true :=
  tall_node _ _ _ _ T13abbaa_ok (by decide +kernel) T13abbab_ok
def T13abbba : Tree := (.node [113184,430348,902208,3227782,3658126,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T13abbba_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13abbba = true := by decide +kernel
def T13abbbb : Tree := (.node [113184,430348,902208,3227782,4048070,5521457,8532035,11083800,13501056,15731968] .nil .nil)
theorem T13abbbb_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13abbbb = true := by decide +kernel
def T13abbb : Tree := .node [113184,430348,902208,3227782,4048070,5521457,7684279,8532035,11083800,13501056,15731968] T13abbba T13abbbb
theorem T13abbb_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13abbb = true :=
  tall_node _ _ _ _ T13abbba_ok (by decide +kernel) T13abbbb_ok
def T13abb : Tree := .node [113184,430348,902208,3227782,3275430,5521457,8532035,11083800,13501056,15731968] T13abba T13abbb
theorem T13abb_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13abb = true :=
  tall_node _ _ _ _ T13abba_ok (by decide +kernel) T13abbb_ok
def T13ab : Tree := .node [113184,430348,902208,2162688,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T13aba T13abb
theorem T13ab_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13ab = true :=
  tall_node _ _ _ _ T13aba_ok (by decide +kernel) T13abb_ok
def T13a : Tree := .node [81920,113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T13aa T13ab
theorem T13a_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13a = true :=
  tall_node _ _ _ _ T13aa_ok (by decide +kernel) T13ab_ok
def T13baaaaa : Tree := (.node [113184,430348,902208,3227782,5521457,7684279,7731895,8532035,11083800,13501056,15731968] .nil .nil)
theorem T13baaaaa_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13baaaaa = true := by decide +kernel
def T13baaaab : Tree := .nil
theorem T13baaaab_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13baaaab = true := by decide +kernel
def T13baaaa : Tree := .node [113184,430348,902208,3227782,5521457,7684279,8242423,8532035,11083800,13501056,15731968] T13baaaaa T13baaaab
theorem T13baaaa_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13baaaa = true :=
  tall_node _ _ _ _ T13baaaaa_ok (by decide +kernel) T13baaaab_ok
def T13baaab : Tree := (.node [113184,430348,902208,3227782,5521457,7684279,8396800,8532035,11083800,13501056,15731968] .nil .nil)
theorem T13baaab_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13baaab = true := by decide +kernel
def T13baaa : Tree := .node [113184,430348,902208,3227782,5521457,7684279,8388608,8532035,11083800,13501056,15731968] T13baaaa T13baaab
theorem T13baaa_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13baaa = true :=
  tall_node _ _ _ _ T13baaaa_ok (by decide +kernel) T13baaab_ok
def T13baabaa : Tree := (.node [113184,430348,902208,3227782,5521457,7684279,8532035,8912896,11083800,13501056,15731968] .nil .nil)
theorem T13baabaa_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13baabaa = true := by decide +kernel
def T13baabab : Tree := .nil
theorem T13baabab_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13baabab = true := by decide +kernel
def T13baaba : Tree := .node [113184,430348,902208,3227782,5521457,7684279,8532035,9434179,11083800,13501056,15731968] T13baabaa T13baabab
theorem T13baaba_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13baaba = true :=
  tall_node _ _ _ _ T13baabaa_ok (by decide +kernel) T13baabab_ok
def T13baabb : Tree := (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,11123256,13501056,15731968] .nil .nil)
theorem T13baabb_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13baabb = true := by decide +kernel
def T13baab : Tree := .node [113184,430348,902208,3227782,5521457,7684279,8532035,10485760,11083800,13501056,15731968] T13baaba T13baabb
theorem T13baab_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13baab = true :=
  tall_node _ _ _ _ T13baaba_ok (by decide +kernel) T13baabb_ok
def T13baa : Tree := .node [113184,430348,902208,3227782,5521457,7684279,8532035,8632931,11083800,13501056,15731968] T13baaa T13baab
theorem T13baa_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13baa = true :=
  tall_node _ _ _ _ T13baaa_ok (by decide +kernel) T13baab_ok
def T13babaaa : Tree := (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,11396184,13501056,15731968] .nil .nil)
theorem T13babaaa_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13babaaa = true := by decide +kernel
def T13babaab : Tree := .nil
theorem T13babaab_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13babaab = true := by decide +kernel
def T13babaa : Tree := .node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,11514140,13501056,15731968] T13babaaa T13babaab
theorem T13babaa_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13babaa = true :=
  tall_node _ _ _ _ T13babaaa_ok (by decide +kernel) T13babaab_ok
def T13babab : Tree := (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,12148894,13501056,15731968] .nil .nil)
theorem T13babab_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13babab = true := by decide +kernel
def T13baba : Tree := .node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,11759815,13501056,15731968] T13babaa T13babab
theorem T13baba_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13baba = true :=
  tall_node _ _ _ _ T13babaa_ok (by decide +kernel) T13babab_ok
def T13babba : Tree := (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,15814022] .nil .nil)
theorem T13babba_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13babba = true := by decide +kernel
def T13babbb : Tree := (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,15875395] .nil .nil)
theorem T13babbb_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13babbb = true := by decide +kernel
def T13babb : Tree := .node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,15843104] T13babba T13babbb
theorem T13babb_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13babb = true :=
  tall_node _ _ _ _ T13babba_ok (by decide +kernel) T13babbb_ok
def T13bab : Tree := .node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15671960,15731968] T13baba T13babb
theorem T13bab_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13bab = true :=
  tall_node _ _ _ _ T13baba_ok (by decide +kernel) T13babb_ok
def T13ba : Tree := .node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,11219035,13501056,15731968] T13baa T13bab
theorem T13ba_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13ba = true :=
  tall_node _ _ _ _ T13baa_ok (by decide +kernel) T13bab_ok
def T13bbaaaa : Tree := (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,16216311] .nil .nil)
theorem T13bbaaaa_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13bbaaaa = true := by decide +kernel
def T13bbaaab : Tree := .nil
theorem T13bbaaab_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13bbaaab = true := by decide +kernel
def T13bbaaa : Tree := .node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,16330008] T13bbaaaa T13bbaaab
theorem T13bbaaa_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13bbaaa = true :=
  tall_node _ _ _ _ T13bbaaaa_ok (by decide +kernel) T13bbaaab_ok
def T13bbaab : Tree := (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,16605375] .nil .nil)
theorem T13bbaab_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13bbaab = true := by decide +kernel
def T13bbaa : Tree := .node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,16605241] T13bbaaa T13bbaab
theorem T13bbaa_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13bbaa = true :=
  tall_node _ _ _ _ T13bbaaa_ok (by decide +kernel) T13bbaab_ok
def T13bbaba : Tree := (.node [113184,430348,902208,3227782,5521457,8242423,8532035,11083800,13501056,15731968] .nil .nil)
theorem T13bbaba_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13bbaba = true := by decide +kernel
def T13bbabb : Tree := (.node [113184,430348,902208,3227782,5521457,8532035,11083800,11123256,13501056,15731968] .nil .nil)
theorem T13bbabb_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13bbabb = true := by decide +kernel
def T13bbab : Tree := .node [113184,430348,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731968] T13bbaba T13bbabb
theorem T13bbab_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13bbab = true :=
  tall_node _ _ _ _ T13bbaba_ok (by decide +kernel) T13bbabb_ok
def T13bba : Tree := .node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,16633152] T13bbaa T13bbab
theorem T13bba_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13bba = true :=
  tall_node _ _ _ _ T13bbaa_ok (by decide +kernel) T13bbab_ok
def T13bbbaaa : Tree := (.node [113184,430348,902208,3227782,5521457,8532035,11083800,12148894,13501056,15731968] .nil .nil)
theorem T13bbbaaa_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13bbbaaa = true := by decide +kernel
def T13bbbaab : Tree := .nil
theorem T13bbbaab_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13bbbaab = true := by decide +kernel
def T13bbbaa : Tree := .node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,15814022] T13bbbaaa T13bbbaab
theorem T13bbbaa_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13bbbaa = true :=
  tall_node _ _ _ _ T13bbbaaa_ok (by decide +kernel) T13bbbaab_ok
def T13bbbab : Tree := (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16076215] .nil .nil)
theorem T13bbbab_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13bbbab = true := by decide +kernel
def T13bbba : Tree := .node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,15875395] T13bbbaa T13bbbab
theorem T13bbba_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13bbba = true :=
  tall_node _ _ _ _ T13bbbaa_ok (by decide +kernel) T13bbbab_ok
def T13bbbba : Tree := (.node [113184,430348,902208,3227782,5689661,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T13bbbba_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13bbbba = true := by decide +kernel
def T13bbbbb : Tree := (.node [113184,430348,902208,3227782,7684279,8532035,11083800,13501056,14566065,15731968] .nil .nil)
theorem T13bbbbb_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13bbbbb = true := by decide +kernel
def T13bbbb : Tree := .node [113184,430348,902208,3227782,7684279,8532035,11083800,13501056,14053491,15731968] T13bbbba T13bbbbb
theorem T13bbbb_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13bbbb = true :=
  tall_node _ _ _ _ T13bbbba_ok (by decide +kernel) T13bbbbb_ok
def T13bbb : Tree := .node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16330008] T13bbba T13bbbb
theorem T13bbb_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13bbb = true :=
  tall_node _ _ _ _ T13bbba_ok (by decide +kernel) T13bbbb_ok
def T13bb : Tree := .node [113184,430348,902208,3227782,5521457,8532035,11083800,11219035,13501056,15731968] T13bba T13bbb
theorem T13bb_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13bb = true :=
  tall_node _ _ _ _ T13bba_ok (by decide +kernel) T13bbb_ok
def T13b : Tree := .node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,16076215] T13ba T13bb
theorem T13b_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13b = true :=
  tall_node _ _ _ _ T13ba_ok (by decide +kernel) T13bb_ok
def T13 : Tree := .node [113184,430348,902208,3227782,5521457,7340032,7684279,8532035,11083800,13501056,15731968] T13a T13b
theorem T13_ok : tall (expFast false (RP PR T12 R12 12) T12 12) T13 = true :=
  tall_node _ _ _ _ T13a_ok (by decide +kernel) T13b_ok
def R13aaaa : Tree := (.node [1,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil)
theorem R13aaaa_ok : tall (refOK cpF 13) R13aaaa = true := by decide +kernel
def R13aaab : Tree := .nil
theorem R13aaab_ok : tall (refOK cpF 13) R13aaab = true := by decide +kernel
def R13aaa : Tree := .node [4,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] R13aaaa R13aaab
theorem R13aaa_ok : tall (refOK cpF 13) R13aaa = true :=
  tall_node _ _ _ _ R13aaaa_ok (by decide +kernel) R13aaab_ok
def R13aaba : Tree := (.node [12288,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil)
theorem R13aaba_ok : tall (refOK cpF 13) R13aaba = true := by decide +kernel
def R13aabb : Tree := .nil
theorem R13aabb_ok : tall (refOK cpF 13) R13aabb = true := by decide +kernel
def R13aab : Tree := .node [65536,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] R13aaba R13aabb
theorem R13aab_ok : tall (refOK cpF 13) R13aab = true :=
  tall_node _ _ _ _ R13aaba_ok (by decide +kernel) R13aabb_ok
def R13aa : Tree := .node [256,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] R13aaa R13aab
theorem R13aa_ok : tall (refOK cpF 13) R13aa = true :=
  tall_node _ _ _ _ R13aaa_ok (by decide +kernel) R13aab_ok
def R13abaa : Tree := (.node [73728,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil)
theorem R13abaa_ok : tall (refOK cpF 13) R13abaa = true := by decide +kernel
def R13abab : Tree := .nil
theorem R13abab_ok : tall (refOK cpF 13) R13abab = true := by decide +kernel
def R13aba : Tree := .node [81920,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] R13abaa R13abab
theorem R13aba_ok : tall (refOK cpF 13) R13aba = true :=
  tall_node _ _ _ _ R13abaa_ok (by decide +kernel) R13abab_ok
def R13abba : Tree := (.node [113184,430348,589824,902208,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil)
theorem R13abba_ok : tall (refOK cpF 13) R13abba = true := by decide +kernel
def R13abbb : Tree := .nil
theorem R13abbb_ok : tall (refOK cpF 13) R13abbb = true := by decide +kernel
def R13abb : Tree := .node [113184,430348,902208,2162688,3227782,5521457,8532035,11083800,13501056,15731968] R13abba R13abbb
theorem R13abb_ok : tall (refOK cpF 13) R13abb = true :=
  tall_node _ _ _ _ R13abba_ok (by decide +kernel) R13abbb_ok
def R13ab : Tree := .node [98304,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] R13aba R13abb
theorem R13ab_ok : tall (refOK cpF 13) R13ab = true :=
  tall_node _ _ _ _ R13aba_ok (by decide +kernel) R13abb_ok
def R13a : Tree := .node [65568,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] R13aa R13ab
theorem R13a_ok : tall (refOK cpF 13) R13a = true :=
  tall_node _ _ _ _ R13aa_ok (by decide +kernel) R13ab_ok
def R13baaa : Tree := (.node [113184,430348,902208,3227782,3658126,5521457,8532035,11083800,13501056,15731968] .nil .nil)
theorem R13baaa_ok : tall (refOK cpF 13) R13baaa = true := by decide +kernel
def R13baab : Tree := .nil
theorem R13baab_ok : tall (refOK cpF 13) R13baab = true := by decide +kernel
def R13baa : Tree := .node [113184,430348,902208,3227782,5521457,7731895,8532035,11083800,13501056,15731968] R13baaa R13baab
theorem R13baa_ok : tall (refOK cpF 13) R13baa = true :=
  tall_node _ _ _ _ R13baaa_ok (by decide +kernel) R13baab_ok
def R13baba : Tree := (.node [113184,430348,902208,3227782,5521457,8532035,10485760,11083800,13501056,15731968] .nil .nil)
theorem R13baba_ok : tall (refOK cpF 13) R13baba = true := by decide +kernel
def R13babb : Tree := .nil
theorem R13babb_ok : tall (refOK cpF 13) R13babb = true := by decide +kernel
def R13bab : Tree := .node [113184,430348,902208,3227782,5521457,8532035,11083800,11396184,13501056,15731968] R13baba R13babb
theorem R13bab_ok : tall (refOK cpF 13) R13bab = true :=
  tall_node _ _ _ _ R13baba_ok (by decide +kernel) R13babb_ok
def R13ba : Tree := .node [113184,430348,902208,3227782,5521457,8396800,8532035,11083800,13501056,15731968] R13baa R13bab
theorem R13ba_ok : tall (refOK cpF 13) R13ba = true :=
  tall_node _ _ _ _ R13baa_ok (by decide +kernel) R13bab_ok
def R13bbaa : Tree := (.node [113184,430348,902208,3227782,5521457,8532035,11083800,11759815,13501056,15731968] .nil .nil)
theorem R13bbaa_ok : tall (refOK cpF 13) R13bbaa = true := by decide +kernel
def R13bbab : Tree := .nil
theorem R13bbab_ok : tall (refOK cpF 13) R13bbab = true := by decide +kernel
def R13bba : Tree := .node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,15843104] R13bbaa R13bbab
theorem R13bba_ok : tall (refOK cpF 13) R13bba = true :=
  tall_node _ _ _ _ R13bbaa_ok (by decide +kernel) R13bbab_ok
def R13bbb : Tree := (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16605375] .nil .nil)
theorem R13bbb_ok : tall (refOK cpF 13) R13bbb = true := by decide +kernel
def R13bb : Tree := .node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16605241] R13bba R13bbb
theorem R13bb_ok : tall (refOK cpF 13) R13bb = true :=
  tall_node _ _ _ _ R13bba_ok (by decide +kernel) R13bbb_ok
def R13b : Tree := .node [113184,430348,902208,3227782,5521457,8532035,11083800,11514140,13501056,15731968] R13ba R13bb
theorem R13b_ok : tall (refOK cpF 13) R13b = true :=
  tall_node _ _ _ _ R13ba_ok (by decide +kernel) R13bb_ok
def R13 : Tree := .node [113184,430348,902208,3145728,3227782,5521457,8532035,11083800,13501056,15731968] R13a R13b
theorem R13_ok : tall (refOK cpF 13) R13 = true :=
  tall_node _ _ _ _ R13a_ok (by decide +kernel) R13b_ok
def T14a : Tree := (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)
theorem T14a_ok : tall (expFast false (RP PR T13 R13 13) T13 13) T14a = true := by decide +kernel
def T14b : Tree := .nil
theorem T14b_ok : tall (expFast false (RP PR T13 R13 13) T13 13) T14b = true := by decide +kernel
def T14 : Tree := .node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] T14a T14b
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

def psL : List ℕ := [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

def lay (x : BitVec 24) : ℕ := layL psL x.toNat

def baseW : List (BitVec 24) := [202052, 276515, 549652, 1097833, 101010, 10616859, 4456668, 2624736, 13635328, 751444]

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

theorem lay_target : lay (16773120 : BitVec 24) = 4095 := by decide +kernel

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
    (ht : (16773120 : BitVec 24) ∈ t) : 14 + 1 ≤ t.length := by
  by_contra hlt
  obtain ⟨s, hs, hl, hm⟩ := free_key t h t.length le_rfl
  have h1 := hm (16773120 : BitVec 24) (by rw [List.take_length]; exact ht)
  rw [lay_target] at h1
  rcases List.mem_append.mp h1 with h2 | h2
  · exact absurd h2 (by decide)
  · exact no_trace hc hs (by omega) h2

def gate2 : List (BitVec 24) := [375475, 474471, 650134, 786390, 1015671, 1166075, 1299821, 1374315, 1631101, 1832829, 2723570, 3722473, 4471039, 4557534, 4658652, 5208028, 5554429, 11714683, 13684585, 13733778, 13836100, 13897692, 13909795, 14384980]

theorem gate2_all : (gate2.all fun x => baseS.any fun u => baseS.any fun v =>
    (x == u &&& v) || (x == u ||| v)) = true := by decide +kernel

theorem gate2_step {x : BitVec 24} (hx : x ∈ gate2) :
    ∃ u ∈ baseS, ∃ v ∈ baseS, x = u &&& v ∨ x = u ||| v := by
  have h := List.all_eq_true.mp gate2_all x hx
  obtain ⟨u, hu, h⟩ := List.any_eq_true.mp h
  obtain ⟨v, hv, h⟩ := List.any_eq_true.mp h
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  exact ⟨u, hu, v, hv, h⟩

theorem shape_gen (hc : NoStartH false 14) (E Y : List (BitVec 24)) (TG : BitVec 24)
    (hE : E = gate2) (hY : Y = baseW) (hT : TG = (16773120 : BitVec 24)) :
    ∀ x1 ∈ E, ∀ (x3 : List (BitVec 24)), TG ∈ (Y ++ [x1]) ++ x3 →
      (∀ (x6 : Fin x3.length), ∃ x8 ∈ (Y ++ [x1]) ++ List.take (↑x6) x3,
        ∃ x9 ∈ (Y ++ [x1]) ++ List.take (↑x6) x3, x3.get x6 = x8 &&& x9 ∨ x3.get x6 = x8 ||| x9) →
      14 ≤ x3.length := by
  subst hE hY hT
  intro x1 hx1 x3 hmem hstep
  have hsub : ∀ (j : ℕ) (y : BitVec 24), y ∈ (baseW ++ [x1]) ++ x3.take j →
      y ∈ baseS ++ (x1 :: x3).take (j + 1) := by
    intro j y hy
    rw [List.take_succ_cons]
    rcases List.mem_append.mp hy with hy | hy
    · rcases List.mem_append.mp hy with hy | hy
      · exact List.mem_append_left _ (baseW_sub hy)
      · exact List.mem_append_right _ (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp hy)))
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ hy)
  have ht : (16773120 : BitVec 24) ∈ x1 :: x3 := by
    rcases List.mem_append.mp hmem with h | h
    · rcases List.mem_append.mp h with h | h
      · exact absurd h (by decide)
      · exact List.mem_cons.mpr (Or.inl (List.mem_singleton.mp h))
    · exact List.mem_cons_of_mem _ h
  have hfree : ∀ (j : ℕ) (hj : j < (x1 :: x3).length),
      ∃ u ∈ baseS ++ (x1 :: x3).take j, ∃ v ∈ baseS ++ (x1 :: x3).take j,
        (x1 :: x3)[j] = u &&& v ∨ (x1 :: x3)[j] = u ||| v := by
    intro j hj
    cases j with
    | zero =>
      obtain ⟨u, hu, v, hv, h⟩ := gate2_step hx1
      exact ⟨u, List.mem_append_left _ hu, v, List.mem_append_left _ hv, h⟩
    | succ j =>
      have hj' : j < x3.length := by
        rw [List.length_cons] at hj
        omega
      obtain ⟨x8, h8, x9, h9, hop⟩ := hstep ⟨j, hj'⟩
      exact ⟨x8, hsub j x8 h8, x9, hsub j x9 h9, hop⟩
  have := free_main hc (x1 :: x3) hfree ht
  rw [List.length_cons] at this
  omega

theorem shape_sound (hc : NoStartH false 14) :
    ∀ x1 ∈ [(375475 : BitVec (24 : ℕ)), (474471 : BitVec (24 : ℕ)), (650134 : BitVec (24 : ℕ)), (786390 : BitVec (24 : ℕ)), (1015671 : BitVec (24 : ℕ)), (1166075 : BitVec (24 : ℕ)), (1299821 : BitVec (24 : ℕ)), (1374315 : BitVec (24 : ℕ)), (1631101 : BitVec (24 : ℕ)), (1832829 : BitVec (24 : ℕ)), (2723570 : BitVec (24 : ℕ)), (3722473 : BitVec (24 : ℕ)), (4471039 : BitVec (24 : ℕ)), (4557534 : BitVec (24 : ℕ)), (4658652 : BitVec (24 : ℕ)), (5208028 : BitVec (24 : ℕ)), (5554429 : BitVec (24 : ℕ)), (11714683 : BitVec (24 : ℕ)), (13684585 : BitVec (24 : ℕ)), (13733778 : BitVec (24 : ℕ)), (13836100 : BitVec (24 : ℕ)), (13897692 : BitVec (24 : ℕ)), (13909795 : BitVec (24 : ℕ)), (14384980 : BitVec (24 : ℕ))],   ∀ (x3 : List (BitVec (24 : ℕ))),     have x4 : List (BitVec (24 : ℕ)) := [(202052 : BitVec (24 : ℕ)), (276515 : BitVec (24 : ℕ)), (549652 : BitVec (24 : ℕ)), (1097833 : BitVec (24 : ℕ)), (101010 : BitVec (24 : ℕ)), (10616859 : BitVec (24 : ℕ)), (4456668 : BitVec (24 : ℕ)), (2624736 : BitVec (24 : ℕ)), (13635328 : BitVec (24 : ℕ)), (751444 : BitVec (24 : ℕ))] ++ [x1];     (16773120 : BitVec (24 : ℕ)) ∈ x4 ++ x3 →       (∀ (x6 : Fin x3.length),           have x7 : List (BitVec (24 : ℕ)) := x4 ++ List.take (↑x6) x3;           ∃ x8 ∈ x7, ∃ x9 ∈ x7, x3.get x6 = x8 &&& x9 ∨ x3.get x6 = x8 ||| x9) →         (14 : ℕ) ≤ x3.length :=
  shape_gen hc _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_4883

theorem PEqualNP.Outside.L_meta_4883 :
    ∀ x1 ∈ [(375475 : BitVec (24 : ℕ)), (474471 : BitVec (24 : ℕ)), (650134 : BitVec (24 : ℕ)), (786390 : BitVec (24 : ℕ)), (1015671 : BitVec (24 : ℕ)), (1166075 : BitVec (24 : ℕ)), (1299821 : BitVec (24 : ℕ)), (1374315 : BitVec (24 : ℕ)), (1631101 : BitVec (24 : ℕ)), (1832829 : BitVec (24 : ℕ)), (2723570 : BitVec (24 : ℕ)), (3722473 : BitVec (24 : ℕ)), (4471039 : BitVec (24 : ℕ)), (4557534 : BitVec (24 : ℕ)), (4658652 : BitVec (24 : ℕ)), (5208028 : BitVec (24 : ℕ)), (5554429 : BitVec (24 : ℕ)), (11714683 : BitVec (24 : ℕ)), (13684585 : BitVec (24 : ℕ)), (13733778 : BitVec (24 : ℕ)), (13836100 : BitVec (24 : ℕ)), (13897692 : BitVec (24 : ℕ)), (13909795 : BitVec (24 : ℕ)), (14384980 : BitVec (24 : ℕ))],   ∀ (x3 : List (BitVec (24 : ℕ))),     have x4 : List (BitVec (24 : ℕ)) := [(202052 : BitVec (24 : ℕ)), (276515 : BitVec (24 : ℕ)), (549652 : BitVec (24 : ℕ)), (1097833 : BitVec (24 : ℕ)), (101010 : BitVec (24 : ℕ)), (10616859 : BitVec (24 : ℕ)), (4456668 : BitVec (24 : ℕ)), (2624736 : BitVec (24 : ℕ)), (13635328 : BitVec (24 : ℕ)), (751444 : BitVec (24 : ℕ))] ++ [x1];     (16773120 : BitVec (24 : ℕ)) ∈ x4 ++ x3 →       (∀ (x6 : Fin x3.length),           have x7 : List (BitVec (24 : ℕ)) := x4 ++ List.take (↑x6) x3;           ∃ x8 ∈ x7, ∃ x9 ∈ x7, x3.get x6 = x8 &&& x9 ∨ x3.get x6 = x8 ||| x9) →         (14 : ℕ) ≤ x3.length :=
  PEqualNP.Outside.L_meta_4883.shape_sound PEqualNP.Outside.L_meta_4883.noStartH
