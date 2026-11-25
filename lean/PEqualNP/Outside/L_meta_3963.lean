import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import PEqualNP.Defs

-- Adapted from c1emon’s proof of L-meta-3287 in PR 6629.
-- The two-negation certificate is due to rzr1331 in PR 6406.
-- Here the circuit in the existential supplies the hypotheses of that bound.
namespace PEqualNP.Outside.L_meta_3963

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Part 1: derivations. Negation is free: every wire is normalised to vanish at the zero input,
-- and a binary gate becomes one of four operations.

inductive Der {α : Type} (op : Fin 4 → α → α → α) : ℕ → Set α → α → Prop
  | here {W : Set α} {y : α} : y ∈ W → Der op 0 W y
  | weak {k : ℕ} {W : Set α} {y : α} : Der op k W y → Der op (k + 1) W y
  | step {k : ℕ} {W : Set α} {y : α} (t : Fin 4) (a b : α) : a ∈ W → b ∈ W →
      Der op k (insert (op t a b) W) y → Der op (k + 1) W y

theorem Der.mono {α : Type} {op : Fin 4 → α → α → α} {k : ℕ} {W : Set α} {y : α}
    (h : Der op k W y) : ∀ {W' : Set α}, W ⊆ W' → Der op k W' y := by
  induction h with
  | here hy => intro W' hs; exact Der.here (hs hy)
  | weak _ ih => intro W' hs; exact Der.weak (ih hs)
  | step t a b ha hb _ ih =>
    intro W' hs
    exact Der.step t a b (hs ha) (hs hb) (ih (Set.insert_subset_insert hs))

theorem Der.le {α : Type} {op : Fin 4 → α → α → α} {k k' : ℕ} {W : Set α} {y : α}
    (h : Der op k W y) (hk : k ≤ k') : Der op k' W y := by
  induction hk with
  | refl => exact h
  | step _ ih => exact Der.weak ih

theorem Der.map {α β : Type} {op : Fin 4 → α → α → α} {op' : Fin 4 → β → β → β} (e : α → β)
    (he : ∀ t a b, e (op t a b) = op' t (e a) (e b)) {k : ℕ} {W : Set α} {y : α}
    (h : Der op k W y) : Der op' k (e '' W) (e y) := by
  induction h with
  | here hy => exact Der.here ⟨_, hy, rfl⟩
  | weak _ ih => exact Der.weak ih
  | step t a b ha hb _ ih =>
    refine Der.step t (e a) (e b) ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ ?_
    rwa [Set.image_insert_eq, he] at ih

theorem Der.elim {α β : Type} {op : Fin 4 → α → α → α} {op' : Fin 4 → β → β → β} (e : α → β)
    (he : ∀ t a b, e (op t a b) = op' t (e a) (e b)) (x : α)
    (hl : ∀ t b, op' t (e x) b = e x ∨ op' t (e x) b = b)
    (hr : ∀ t b, op' t b (e x) = e x ∨ op' t b (e x) = b)
    {k : ℕ} {W : Set α} {y : α} (h : Der op k W y) :
    ∀ U : Set α, W ⊆ insert x U → y ≠ x → e x ∈ e '' U →
      Der op k U y ∨ ∃ k', k = k' + 1 ∧ Der op' k' (e '' U) (e y) := by
  induction h with
  | here hy =>
    intro U hs hne _
    exact Or.inl (Der.here ((hs hy).resolve_left hne))
  | weak _ ih =>
    intro U hs hne hx
    rcases ih U hs hne hx with h | ⟨k', rfl, h⟩
    · exact Or.inl (Der.weak h)
    · exact Or.inr ⟨_, rfl, Der.weak h⟩
  | @step k W y t a b ha hb h ih =>
    intro U hs hne hx
    have im (w : α) (hw : w ∈ W) : e w ∈ e '' U := by
      rcases hs hw with rfl | hw
      · exact hx
      · exact ⟨w, hw, rfl⟩
    by_cases hab : a ∈ U ∧ b ∈ U
    · have hs' : insert (op t a b) W ⊆ insert x (insert (op t a b) U) := by
        rintro w (rfl | hw)
        · exact Or.inr (Or.inl rfl)
        · rcases hs hw with rfl | hw
          · exact Or.inl rfl
          · exact Or.inr (Or.inr hw)
      have hx' : e x ∈ e '' insert (op t a b) U := by
        obtain ⟨u, hu, h⟩ := hx; exact ⟨u, Or.inr hu, h⟩
      rcases ih _ hs' hne hx' with hd | ⟨k', hk', hd⟩
      · exact Or.inl (Der.step t a b hab.1 hab.2 hd)
      · refine Or.inr ⟨k' + 1, by rw [hk'], ?_⟩
        rw [Set.image_insert_eq, he] at hd
        exact Der.step t (e a) (e b) ⟨a, hab.1, rfl⟩ ⟨b, hab.2, rfl⟩ hd
    · have hc : e (op t a b) ∈ e '' U := by
        rw [he]
        by_cases hau : a ∈ U
        · have hbx : b = x := by
            rcases hs hb with h | h
            · exact h
            · exact absurd ⟨hau, h⟩ hab
          subst hbx
          rcases hr t (e a) with h | h
          · rw [h]; exact hx
          · rw [h]; exact im a ha
        · have hax : a = x := by
            rcases hs ha with h | h
            · exact h
            · exact absurd h hau
          subst hax
          rcases hl t (e b) with h | h
          · rw [h]; exact hx
          · rw [h]; exact im b hb
      refine Or.inr ⟨k, rfl, (h.map e he).mono ?_⟩
      rintro _ ⟨w, rfl | hw, rfl⟩
      · exact hc
      · exact im w hw

def opB (t : Fin 4) (a b : Bool) : Bool :=
  match t with
  | 0 => a && b
  | 1 => a || b
  | 2 => a && !b
  | 3 => b && !a

def opF {Ω : Type} (t : Fin 4) (f g : Ω → Bool) : Ω → Bool := fun x => opB t (f x) (g x)

def opN (t : Fin 4) (a b : ℕ) : ℕ :=
  match t with
  | 0 => Nat.land a b
  | 1 => Nat.lor a b
  | 2 => Nat.xor a (Nat.land a b)
  | 3 => Nat.xor b (Nat.land a b)

lemma land_bit (x y i : ℕ) : (Nat.land x y).testBit i = (x.testBit i && y.testBit i) :=
  Nat.testBit_and x y i

lemma lor_bit (x y i : ℕ) : (Nat.lor x y).testBit i = (x.testBit i || y.testBit i) :=
  Nat.testBit_or x y i

lemma xor_bit (x y i : ℕ) : (Nat.xor x y).testBit i = (x.testBit i != y.testBit i) := by
  simpa [bne] using Nat.testBit_xor x y i

lemma shr_bit (x s i : ℕ) : (Nat.shiftRight x s).testBit i = x.testBit (s + i) := by
  have := Nat.testBit_shiftRight (x := x) (i := s) (j := i)
  simpa using this

lemma opN_bit (t : Fin 4) (a b i : ℕ) :
    (opN t a b).testBit i = opB t (a.testBit i) (b.testBit i) := by
  fin_cases t <;> simp only [opN, opB, land_bit, lor_bit, xor_bit] <;>
    cases a.testBit i <;> cases b.testBit i <;> rfl

lemma Der.agree {Ω : Type} {k : ℕ} {W : Set (Ω → Bool)} {y : Ω → Bool} (h : Der opF k W y)
    (p q : Ω) : (∀ w ∈ W, w p = w q) → y p = y q := by
  induction h with
  | here hy => intro hw; exact hw _ hy
  | weak _ ih => exact ih
  | step t a b ha hb _ ih =>
    intro hw
    refine ih ?_
    rintro w (rfl | hm)
    · simp only [opF, hw a ha, hw b hb]
    · exact hw w hm

-- Part 2: traces.

structure St where
  t : Fin 4
  a : ℕ
  b : ℕ

def St.val (s : St) : ℕ := opN s.t s.a s.b

def Valid (y : ℕ) : Set ℕ → List St → Prop
  | W, [] => y ∈ W
  | W, s :: l => s.a ∈ W ∧ s.b ∈ W ∧ s.val ∉ W ∧ Valid y (insert s.val W) l

def need (y : ℕ) : List St → Finset ℕ
  | [] => {y}
  | s :: l => insert s.a (insert s.b ((need y l).erase s.val))

def Useful (y : ℕ) : List St → Prop
  | [] => True
  | s :: l => s.val ∈ need y l ∧ Useful y l

def killB (m : ℕ) (s : St) : Bool := Nat.beq (Nat.land s.a m) 0 || Nat.beq (Nat.land s.b m) 0

def kills (m : ℕ) (l : List St) : ℕ := l.countP (killB m)

def Chain : ℕ → List St → Prop
  | _, [] => True
  | p, s :: l => (s.a = p ∨ s.b = p ∨ p ≤ s.val) ∧ Chain s.val l

lemma valid_of_der {k : ℕ} {W : Set ℕ} {y : ℕ} (h : Der opN k W y) :
    ∃ l, l.length ≤ k ∧ Valid y W l := by
  induction h with
  | here hy => exact ⟨[], by simp, hy⟩
  | weak _ ih => obtain ⟨l, h1, h2⟩ := ih; exact ⟨l, by omega, h2⟩
  | @step k W y t a b ha hb _ ih =>
    obtain ⟨l, h1, h2⟩ := ih
    by_cases hc : opN t a b ∈ W
    · rw [Set.insert_eq_of_mem hc] at h2; exact ⟨l, by omega, h2⟩
    · exact ⟨⟨t, a, b⟩ :: l, by simp; omega, ha, hb, hc, h2⟩

lemma need_sub {y : ℕ} (l : List St) : ∀ {W : Set ℕ}, Valid y W l → ∀ x ∈ need y l, x ∈ W := by
  induction l with
  | nil => intro W h x hx; rw [need, Finset.mem_singleton] at hx; rw [hx]; exact h
  | cons s l ih =>
    intro W h x hx
    obtain ⟨ha, hb, hc, hv⟩ := h
    rw [need, Finset.mem_insert, Finset.mem_insert, Finset.mem_erase] at hx
    rcases hx with rfl | rfl | ⟨h1, h2⟩
    · exact ha
    · exact hb
    · exact (ih hv x h2).resolve_left h1

lemma valid_drop {y c : ℕ} (l : List St) : ∀ {W : Set ℕ}, Valid y (insert c W) l →
    c ∉ need y l → Valid y W l := by
  induction l with
  | nil =>
    intro W h hc
    rw [need, Finset.mem_singleton] at hc
    exact h.resolve_left (fun e => hc e.symm)
  | cons s l ih =>
    intro W h hc
    obtain ⟨ha, hb, hf, hv⟩ := h
    rw [need, Finset.mem_insert, Finset.mem_insert, Finset.mem_erase] at hc
    push Not at hc
    obtain ⟨h1, h2, h3⟩ := hc
    have hne : c ≠ s.val := fun e => hf (Or.inl e.symm)
    refine ⟨ha.resolve_left (Ne.symm h1), hb.resolve_left (Ne.symm h2), fun h => hf (Or.inr h), ?_⟩
    rw [Set.insert_comm] at hv
    exact ih hv (h3 hne)

lemma useful_of_min {y : ℕ} (l : List St) : ∀ {W : Set ℕ}, Valid y W l →
    (∀ l', Valid y W l' → l.length ≤ l'.length) → Useful y l := by
  induction l with
  | nil => intro W _ _; trivial
  | cons s l ih =>
    intro W h hmin
    obtain ⟨ha, hb, hf, hv⟩ := h
    refine ⟨?_, ih hv fun l' hl' => ?_⟩
    · by_contra hc
      have := hmin l (valid_drop l hv hc)
      simp at this
    · have := hmin (s :: l') ⟨ha, hb, hf, hl'⟩
      simpa using this

lemma need_card {y : ℕ} (l : List St) (h : Useful y l) : (need y l).card ≤ l.length + 1 := by
  induction l with
  | nil => simp [need]
  | cons s l ih =>
    obtain ⟨h1, h2⟩ := h
    have e := Finset.card_erase_of_mem h1
    have i := ih h2
    have c1 := Finset.card_insert_le s.a (insert s.b ((need y l).erase s.val))
    have c2 := Finset.card_insert_le s.b ((need y l).erase s.val)
    have p := Finset.card_pos.mpr ⟨_, h1⟩
    rw [need, List.length_cons]
    omega

lemma need_next {y : ℕ} {s : St} {l : List St} {x : ℕ} (h : x ∈ need y l) :
    x = s.val ∨ x ∈ need y (s :: l) := by
  by_cases hx : x = s.val
  · exact Or.inl hx
  · right; rw [need]; simp [hx, h]

lemma need_agree {y i j : ℕ} (l : List St) (h : ∀ x ∈ need y l, x.testBit i = x.testBit j) :
    y.testBit i = y.testBit j := by
  induction l with
  | nil => exact h y (by simp [need])
  | cons s l ih =>
    refine ih fun x hx => ?_
    rcases need_next (s := s) hx with rfl | hx
    · rw [St.val, opN_bit, opN_bit, h s.a (by simp [need]), h s.b (by simp [need])]
    · exact h x hx

lemma kill_forced {y m x : ℕ} (hy : Nat.land y m ≠ 0) (l : List St) (hx : x ∈ need y l)
    (hm : Nat.land x m = 0) : 1 ≤ kills m l := by
  induction l with
  | nil => rw [need, Finset.mem_singleton] at hx; rw [hx] at hm; exact absurd hm hy
  | cons s l ih =>
    rw [need, Finset.mem_insert, Finset.mem_insert, Finset.mem_erase] at hx
    have hk : killB m s = true → 1 ≤ kills m (s :: l) := fun h => by
      rw [kills, List.countP_cons_of_pos h]; omega
    rcases hx with rfl | rfl | ⟨_, h2⟩
    · exact hk (by unfold killB; rw [hm]; rfl)
    · exact hk (by unfold killB; rw [hm]; exact Bool.or_true _)
    · have := ih h2
      have c : kills m l ≤ kills m (s :: l) := by
        rw [kills, kills, List.countP_cons]; omega
      omega

lemma land_op (t : Fin 4) (a b m : ℕ) :
    Nat.land (opN t a b) m = opN t (Nat.land a m) (Nat.land b m) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [land_bit, opN_bit]
  fin_cases t <;> cases a.testBit i <;> cases b.testBit i <;> cases m.testBit i <;> rfl

lemma opN_zero_left (t : Fin 4) (b : ℕ) : opN t 0 b = 0 ∨ opN t 0 b = b := by
  have key (c : Bool → Bool) (h : ∀ i, (opN t 0 b).testBit i = c (b.testBit i))
      (hc : c = (fun _ => false) ∨ c = id) : opN t 0 b = 0 ∨ opN t 0 b = b := by
    rcases hc with rfl | rfl
    · left; apply Nat.eq_of_testBit_eq; intro i; rw [h]; simp
    · right; apply Nat.eq_of_testBit_eq; intro i; rw [h]; rfl
  fin_cases t
  · exact key _ (fun i => by rw [opN_bit]; simp [opB]) (Or.inl rfl)
  · exact key id (fun i => by rw [opN_bit]; simp [opB]) (Or.inr rfl)
  · exact key (fun _ => false) (fun i => by rw [opN_bit]; simp [opB]) (Or.inl rfl)
  · exact key id (fun i => by rw [opN_bit]; simp [opB]) (Or.inr rfl)

def swapT : Fin 4 → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 3
  | 3 => 2

lemma opN_swap (t : Fin 4) (a b : ℕ) : opN t a b = opN (swapT t) b a := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [opN_bit, opN_bit]
  fin_cases t <;> cases a.testBit i <;> cases b.testBit i <;> rfl

lemma opN_zero_right (t : Fin 4) (b : ℕ) : opN t b 0 = 0 ∨ opN t b 0 = b := by
  rw [opN_swap]; exact opN_zero_left _ _

lemma opN_self (t : Fin 4) (a : ℕ) : opN t a a = 0 ∨ opN t a a = a := by
  have key (c : Bool → Bool) (h : ∀ i, (opN t a a).testBit i = c (a.testBit i))
      (hc : c = (fun _ => false) ∨ c = id) : opN t a a = 0 ∨ opN t a a = a := by
    rcases hc with rfl | rfl
    · left; apply Nat.eq_of_testBit_eq; intro i; rw [h]; simp
    · right; apply Nat.eq_of_testBit_eq; intro i; rw [h]; rfl
  fin_cases t
  · exact key id (fun i => by rw [opN_bit]; simp [opB]) (Or.inr rfl)
  · exact key id (fun i => by rw [opN_bit]; simp [opB]) (Or.inr rfl)
  · exact key (fun _ => false) (fun i => by rw [opN_bit]; simp [opB]) (Or.inl rfl)
  · exact key (fun _ => false) (fun i => by rw [opN_bit]; simp [opB]) (Or.inl rfl)

lemma der_masked {y m : ℕ} (l : List St) : ∀ {W : Set ℕ}, Valid y W l → 0 ∈ W →
    ∃ n, n + kills m l = l.length ∧ Der opN n ((fun w => Nat.land w m) '' W) (Nat.land y m) := by
  induction l with
  | nil => intro W h _; exact ⟨0, by simp [kills], Der.here ⟨y, h, rfl⟩⟩
  | cons s l ih =>
    intro W h h0
    obtain ⟨ha, hb, _, hv⟩ := h
    obtain ⟨n, hn, hd⟩ := ih hv (Or.inr h0)
    have im (w : ℕ) (hw : w ∈ W) : Nat.land w m ∈ (fun w => Nat.land w m) '' W := ⟨w, hw, rfl⟩
    have z : 0 ∈ (fun w => Nat.land w m) '' W := ⟨0, h0, by simp [Nat.land]⟩
    by_cases hk : killB m s = true
    · refine ⟨n, ?_, hd.mono ?_⟩
      · rw [kills, List.countP_cons_of_pos hk, List.length_cons]
        rw [kills] at hn; omega
      · rintro _ ⟨w, rfl | hw, rfl⟩
        · show Nat.land s.val m ∈ _
          rw [St.val, land_op]
          rw [killB, Bool.or_eq_true, Nat.beq_eq, Nat.beq_eq] at hk
          rcases hk with h | h
          · rw [h]
            rcases opN_zero_left s.t (Nat.land s.b m) with e | e
            · rw [e]; exact z
            · rw [e]; exact im _ hb
          · rw [h]
            rcases opN_zero_right s.t (Nat.land s.a m) with e | e
            · rw [e]; exact z
            · rw [e]; exact im _ ha
        · exact im w hw
    · refine ⟨n + 1, ?_, ?_⟩
      · rw [kills, List.countP_cons_of_neg hk, List.length_cons]
        rw [kills] at hn; omega
      · refine Der.step s.t _ _ (im _ ha) (im _ hb) ?_
        rw [Set.image_insert_eq] at hd
        have e : Nat.land s.val m = opN s.t (Nat.land s.a m) (Nat.land s.b m) := land_op _ _ _ _
        rw [← e]; exact hd

lemma valid_swap {y : ℕ} (s1 s2 : St) (post : List St) (h1 : s2.a ≠ s1.val) (h2 : s2.b ≠ s1.val)
    (pre : List St) : ∀ {W : Set ℕ}, Valid y W (pre ++ s1 :: s2 :: post) →
      Valid y W (pre ++ s2 :: s1 :: post) := by
  induction pre with
  | nil =>
    intro W h
    obtain ⟨ha, hb, hc, ha2, hb2, hc2, hv⟩ := h
    refine ⟨ha2.resolve_left h1, hb2.resolve_left h2, fun h => hc2 (Or.inr h), Or.inr ha, Or.inr hb,
      ?_, ?_⟩
    · rintro (e | h)
      · exact hc2 (Or.inl e.symm)
      · exact hc h
    · rw [Set.insert_comm]; exact hv
  | cons s pre ih =>
    intro W h
    obtain ⟨ha, hb, hc, hv⟩ := h
    exact ⟨ha, hb, hc, ih hv⟩

def keyN (l : List St) : ℕ := l.foldl (fun acc s => 2 * acc + s.val) 0

lemma fold_lt (l : List St) : ∀ {x x' : ℕ}, x < x' →
    l.foldl (fun acc s => 2 * acc + s.val) x < l.foldl (fun acc s => 2 * acc + s.val) x' := by
  induction l with
  | nil => intro x x' h; exact h
  | cons s l ih =>
    intro x x' h
    exact ih (show 2 * x + s.val < 2 * x' + s.val by omega)

lemma key_swap (pre post : List St) (s1 s2 : St) (h : s2.val < s1.val) :
    keyN (pre ++ s2 :: s1 :: post) < keyN (pre ++ s1 :: s2 :: post) := by
  unfold keyN
  rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons, List.foldl_cons,
    List.foldl_cons]
  exact fold_lt post (by omega)

lemma chain_of {l : List St} : ∀ (p : ℕ),
    (∀ s l', l = s :: l' → (s.a = p ∨ s.b = p ∨ p ≤ s.val)) →
    (∀ pre s1 s2 post, l = pre ++ s1 :: s2 :: post →
      (s2.a = s1.val ∨ s2.b = s1.val ∨ s1.val ≤ s2.val)) → Chain p l := by
  induction l with
  | nil => intro p _ _; trivial
  | cons s l ih =>
    intro p h1 h2
    refine ⟨h1 s l rfl, ih s.val (fun s' l' e => ?_) (fun pre s1 s2 post e => ?_)⟩
    · exact h2 [] s s' l' (by rw [e]; rfl)
    · exact h2 (s :: pre) s1 s2 post (by rw [e]; rfl)

lemma exists_min {α : Type} (S : Set α) (f : α → ℕ) (h : S.Nonempty) :
    ∃ l ∈ S, ∀ l' ∈ S, f l ≤ f l' := by
  obtain ⟨l, hl, hm⟩ := (measure f).wf.has_min S h
  exact ⟨l, hl, fun l' hl' => not_lt.mp (hm l' hl')⟩

def headV : List St → ℕ
  | [] => 0
  | s :: _ => s.val

-- a shortest trace, least by its first gate and then by its key
lemma exists_sorted {y : ℕ} {W : Set ℕ} {k : ℕ} (h : Der opN k W y) :
    ∃ l, l.length ≤ k ∧ Valid y W l ∧ Useful y l ∧ Chain 0 l ∧
      ∀ l', Valid y W l' → l'.length = l.length → headV l ≤ headV l' := by
  obtain ⟨l0, hk0, hv0⟩ := valid_of_der h
  obtain ⟨l1, hv1, hmin⟩ := exists_min {l | Valid y W l} List.length ⟨l0, hv0⟩
  obtain ⟨l2, ⟨hv2, hlen2⟩, hhead⟩ :=
    exists_min {l | Valid y W l ∧ l.length = l1.length} headV ⟨l1, hv1, rfl⟩
  obtain ⟨l, ⟨hv, hlen, hh⟩, hkey⟩ :=
    exists_min {l | Valid y W l ∧ l.length = l1.length ∧ headV l = headV l2} keyN ⟨l2, hv2, hlen2, rfl⟩
  refine ⟨l, ?_, hv, useful_of_min l hv (fun l' hl' => by rw [hlen]; exact hmin l' hl'), ?_, ?_⟩
  · rw [hlen]; exact (hmin l0 hv0).trans hk0
  · refine chain_of 0 (fun s l' _ => Or.inr (Or.inr (Nat.zero_le _))) ?_
    intro pre s1 s2 post e
    by_contra hc
    push Not at hc
    obtain ⟨c1, c2, c3⟩ := hc
    rw [e] at hv hlen hh hkey
    have sv := valid_swap s1 s2 post c1 c2 pre hv
    have sl : (pre ++ s2 :: s1 :: post).length = l1.length := by
      rw [← hlen]; simp
    cases pre with
    | nil =>
      have := hhead _ ⟨sv, sl⟩
      rw [← hh] at this
      change s1.val ≤ s2.val at this
      omega
    | cons p pre =>
      have := hkey _ ⟨sv, sl, by rw [← hh]; rfl⟩
      have := key_swap (p :: pre) post s1 s2 c3
      omega
  · intro l' hl' hl
    rw [hh]; exact hhead l' ⟨hl', by rw [hl, hlen]⟩

-- every trace step has distinct nonzero operands and a new nonzero value
lemma step_facts {y : ℕ} {W : Set ℕ} {s : St} {l : List St} (h : Valid y W (s :: l)) (h0 : 0 ∈ W) :
    s.a ≠ 0 ∧ s.b ≠ 0 ∧ s.a ≠ s.b ∧ s.val ≠ 0 ∧ s.val ≠ s.a ∧ s.val ≠ s.b ∧
      s.val ∉ need y (s :: l) := by
  have hn := need_sub (s :: l) h
  obtain ⟨ha, hb, hc, _⟩ := h
  refine ⟨?_, ?_, ?_, fun e => hc (e ▸ h0), fun e => hc (e ▸ ha), fun e => hc (e ▸ hb),
    fun hh => hc (hn _ hh)⟩
  · intro e
    rcases opN_zero_left s.t s.b with h | h
    · exact hc (by rw [St.val, e, h]; exact h0)
    · exact hc (by rw [St.val, e, h]; exact hb)
  · intro e
    rcases opN_zero_right s.t s.a with h | h
    · exact hc (by rw [St.val, e, h]; exact h0)
    · exact hc (by rw [St.val, e, h]; exact ha)
  · intro e
    rcases opN_self s.t s.a with h | h
    · exact hc (by rw [St.val, ← e, h]; exact h0)
    · exact hc (by rw [St.val, ← e, h]; exact ha)


-- Part 3: the search.

structure Wr where
  w : ℕ
  s : ℕ
  f : ℕ

def sepN (L w : ℕ) : ℕ := Nat.land (Nat.xor w (Nat.shiftRight w 143)) L

def covL : List Wr → ℕ
  | [] => 0
  | a :: l => Nat.lor a.s (covL l)

def flL : List Wr → ℕ
  | [] => 0
  | a :: l => Nat.lor a.f (flL l)

def lenL : List Wr → ℕ
  | [] => 0
  | _ :: l => Nat.succ (lenL l)

def absentL (g : ℕ) : List Wr → Bool
  | [] => true
  | x :: l => cond (Nat.beq x.w g) false (absentL g l)

def app : List Wr → List Wr → List Wr
  | [], m => m
  | a :: l, m => a :: app l m

def sub (a b : ℕ) : Bool := Nat.beq (Nat.land a b) a

def force (x : ℕ) (f : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (f 0) (fun n _ => f (Nat.succ n)) x

lemma force_eq (x : ℕ) (f : ℕ → Bool) : force x f = f x := by cases x <;> rfl

abbrev Next := List Wr → ℕ → ℕ → ℕ → ℕ → Bool

def tryG (L : ℕ) (r : Next) (k m : ℕ) (rest : List Wr) (cr c1 c2 c3 : ℕ) (a b : Wr) (last : ℕ)
    (uses : Bool) (g fg : ℕ) : Bool :=
  cond (Nat.beq g 0) false (cond (Nat.beq g a.w) false (cond (Nat.beq g b.w) false
    (cond (cond uses true (Nat.ble last g))
      (cond (sub fg c1)
        (force (sepN L g) fun sg =>
          force (Nat.lor cr sg) fun base =>
            (cond (Nat.beq base L) (cond (absentL g rest) (r (⟨g, sg, fg⟩ :: rest) c1 c2 c3 g) false)
              false) ||
            (cond (Nat.ble m (Nat.succ k))
              ((cond (sub a.f c1) (cond (Nat.beq (Nat.lor base a.s) L)
                  (cond (absentL g rest) (r (⟨g, sg, fg⟩ :: a :: rest) c1 c2 c3 g) false) false) false) ||
               (cond (sub b.f c1) (cond (Nat.beq (Nat.lor base b.s) L)
                  (cond (absentL g rest) (r (⟨g, sg, fg⟩ :: b :: rest) c1 c2 c3 g) false) false) false) ||
               (cond (Nat.ble m k) (cond (sub a.f c1) (cond (sub b.f c1)
                  (cond (absentL g rest) (r (⟨g, sg, fg⟩ :: a :: b :: rest) c1 c2 c3 g) false) false)
                  false) false))
              false))
        false)
      false)))

def tryP (L : ℕ) (r : Next) (k m c1 c2 c3 last : ℕ) (a b : Wr) (rest : List Wr) : Bool :=
  force (Nat.lor a.f b.f) fun K =>
    cond (sub K c1)
      (force (Nat.lor c2 (Nat.xor c1 (Nat.land c1 K))) fun d1 =>
       force (Nat.lor c3 (Nat.xor c2 (Nat.land c2 K))) fun d2 =>
       force (Nat.xor c3 (Nat.land c3 K)) fun d3 =>
        cond (sub (flL rest) d1)
          (force (covL rest) fun cr =>
            force (Nat.land a.w b.w) fun ab =>
              tryG L r k m rest cr d1 d2 d3 a b last (Nat.beq a.w last || Nat.beq b.w last) ab K ||
              (tryG L r k m rest cr d1 d2 d3 a b last (Nat.beq a.w last || Nat.beq b.w last)
                  (Nat.lor a.w b.w) (Nat.land a.f b.f) ||
              (tryG L r k m rest cr d1 d2 d3 a b last (Nat.beq a.w last || Nat.beq b.w last)
                  (Nat.xor a.w ab) a.f ||
              tryG L r k m rest cr d1 d2 d3 a b last (Nat.beq a.w last || Nat.beq b.w last)
                  (Nat.xor b.w ab) b.f)))
          false)
      false

def pairsB (a : Wr) : List Wr → List Wr → List (Wr × Wr × List Wr)
  | _, [] => []
  | acc, b :: l => (a, b, app acc l) :: pairsB a (b :: acc) l

def pairsA : List Wr → List Wr → List (Wr × Wr × List Wr)
  | _, [] => []
  | acc, a :: l => pairsB a acc l ++ pairsA (a :: acc) l

def anyP (p : Wr → Wr → List Wr → Bool) : List (Wr × Wr × List Wr) → Bool
  | [] => false
  | x :: l => p x.1 x.2.1 x.2.2 || anyP p l

def isT (y : ℕ) : List Wr → Bool
  | [a] => Nat.beq a.w y
  | _ => false

def search (L y : ℕ) : ℕ → Next
  | 0, v, _, _, _, _ => isT y v
  | k + 1, v, c1, c2, c3, last =>
    isT y v || anyP (tryP L (search L y k) k (lenL v) c1 c2 c3 last) (pairsA [] v)

-- correctness of the parts

lemma lenL_eq (v : List Wr) : lenL v = v.length := by
  induction v with
  | nil => rfl
  | cons a l ih => rw [lenL, ih]; rfl

lemma app_eq (a b : List Wr) : app a b = a ++ b := by
  induction a with
  | nil => rfl
  | cons x l ih => rw [app, ih]; rfl

lemma absent_true {g : ℕ} {l : List Wr} (h : ∀ x ∈ l, x.w ≠ g) : absentL g l = true := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have hx : Nat.beq x.w g = false := by
      rw [← Bool.not_eq_true, Nat.beq_eq]; exact h x (by simp)
    rw [absentL, hx]
    exact ih fun u hu => h u (by simp [hu])

lemma sub_true {a b : ℕ} (h : ∀ i, a.testBit i = true → b.testBit i = true) : sub a b = true := by
  rw [sub, Nat.beq_eq]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [land_bit]
  cases ha : a.testBit i
  · rfl
  · rw [h i ha]; rfl

lemma anyP_true {p : Wr → Wr → List Wr → Bool} {l : List (Wr × Wr × List Wr)} {a b : Wr}
    {r : List Wr} (hm : (a, b, r) ∈ l) (hp : p a b r = true) : anyP p l = true := by
  induction l with
  | nil => simp at hm
  | cons x l ih =>
    rw [anyP, Bool.or_eq_true]
    rcases List.mem_cons.mp hm with rfl | h
    · exact Or.inl hp
    · exact Or.inr (ih h)

lemma pairsB_spec (a b : Wr) (l : List Wr) : ∀ acc : List Wr, b ∈ l →
    ∃ r, (a, b, r) ∈ pairsB a acc l ∧ (acc ++ l).Perm (b :: r) := by
  induction l with
  | nil => intro acc h; simp at h
  | cons x l ih =>
    intro acc h
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨acc ++ l, by simp [pairsB, app_eq], List.perm_middle⟩
    · obtain ⟨r, h1, h2⟩ := ih (x :: acc) h
      exact ⟨r, by simp [pairsB, h1], List.perm_middle.trans h2⟩

lemma pairsA_spec (a b : Wr) (hab : a ≠ b) (l : List Wr) : ∀ acc : List Wr, a ∈ l → b ∈ l →
    ∃ r, ((a, b, r) ∈ pairsA acc l ∨ (b, a, r) ∈ pairsA acc l) ∧ (acc ++ l).Perm (a :: b :: r) := by
  induction l with
  | nil => intro acc h; simp at h
  | cons x l ih =>
    intro acc ha hb
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hb with e | hb'
      · exact absurd e.symm hab
      · obtain ⟨r, h1, h2⟩ := pairsB_spec a b l acc hb'
        exact ⟨r, Or.inl (by rw [pairsA]; exact List.mem_append_left _ h1),
          List.perm_middle.trans (h2.cons a)⟩
    · rcases List.mem_cons.mp hb with rfl | hb'
      · obtain ⟨r, h1, h2⟩ := pairsB_spec b a l acc ha'
        exact ⟨r, Or.inr (by rw [pairsA]; exact List.mem_append_left _ h1),
          (List.perm_middle.trans (h2.cons b)).trans (List.Perm.swap a b r)⟩
      · obtain ⟨r, h1, h2⟩ := ih (x :: acc) ha' hb'
        refine ⟨r, ?_, List.perm_middle.trans h2⟩
        rcases h1 with h | h
        · exact Or.inl (by rw [pairsA]; exact List.mem_append_right _ h)
        · exact Or.inr (by rw [pairsA]; exact List.mem_append_right _ h)

structure Rep (L H : ℕ) (mask : ℕ → ℕ) (v : List Wr) (S : Finset ℕ) : Prop where
  nd : (v.map Wr.w).Nodup
  mem : ∀ x, x ∈ S ↔ ∃ u ∈ v, u.w = x
  sep : ∀ u ∈ v, u.s = sepN L u.w
  fl : ∀ u ∈ v, ∀ h, u.f.testBit h = true → h < H ∧ Nat.land u.w (mask h) = 0

def Bud (H : ℕ) (mask : ℕ → ℕ) (c1 c2 c3 : ℕ) (l : List St) : Prop :=
  ∀ h < H, kills (mask h) l ≤ 3 ∧ (1 ≤ kills (mask h) l → c1.testBit h = true) ∧
    (2 ≤ kills (mask h) l → c2.testBit h = true) ∧ (3 ≤ kills (mask h) l → c3.testBit h = true)

lemma cov_bit (l : List Wr) (i : ℕ) : (covL l).testBit i = l.any fun a => a.s.testBit i := by
  induction l with
  | nil => simp [covL]
  | cons a l ih => rw [covL, lor_bit, ih, List.any_cons]

lemma fl_bit (l : List Wr) (i : ℕ) : (flL l).testBit i = l.any fun a => a.f.testBit i := by
  induction l with
  | nil => simp [flL]
  | cons a l ih => rw [flL, lor_bit, ih, List.any_cons]

lemma sepN_bit (L w i : ℕ) :
    (sepN L w).testBit i = ((w.testBit i != w.testBit (143 + i)) && L.testBit i) := by
  rw [sepN, land_bit, xor_bit, shr_bit]

lemma rep_cov {L H y : ℕ} {mask : ℕ → ℕ}
    (hL : ∀ i, L.testBit i = true → y.testBit i ≠ y.testBit (143 + i)) {v : List Wr} {l : List St}
    (hr : Rep L H mask v (need y l)) : covL v = L := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [cov_bit]
  cases hi : L.testBit i
  · rw [List.any_eq_false]
    intro u hu
    rw [hr.sep u hu, sepN_bit, hi]; simp
  · rw [List.any_eq_true]
    by_contra hc
    push Not at hc
    refine hL i hi (need_agree l fun x hx => ?_)
    obtain ⟨u, hu, rfl⟩ := (hr.mem x).mp hx
    have := hc u hu
    rw [hr.sep u hu, sepN_bit, hi] at this
    cases h1 : u.w.testBit i <;> cases h2 : u.w.testBit (143 + i) <;> simp_all

lemma rep_len {L H : ℕ} {mask : ℕ → ℕ} {v : List Wr} {S : Finset ℕ} (hr : Rep L H mask v S) :
    v.length = S.card := by
  have e : S = (v.map Wr.w).toFinset := by
    ext x; rw [hr.mem, List.mem_toFinset, List.mem_map]
  rw [e, List.toFinset_card_of_nodup hr.nd, List.length_map]

lemma flag_forced {H y : ℕ} {mask : ℕ → ℕ} (hy : ∀ h < H, Nat.land y (mask h) ≠ 0)
    {l : List St} {d1 d2 d3 : ℕ} (hb : Bud H mask d1 d2 d3 l) {f x : ℕ} (hx : x ∈ need y l)
    (hf : ∀ h, f.testBit h = true → h < H ∧ Nat.land x (mask h) = 0) : sub f d1 = true := by
  refine sub_true fun h hh => ?_
  obtain ⟨h1, h2⟩ := hf h hh
  exact (hb h h1).2.1 (kill_forced (hy h h1) l hx h2)

lemma tryG_true {L H y k : ℕ} {mask : ℕ → ℕ}
    (hy : ∀ h < H, Nat.land y (mask h) ≠ 0)
    (hL : ∀ i, L.testBit i = true → y.testBit i ≠ y.testBit (143 + i))
    {r : Next} {v rest : List Wr} {a b : Wr} {l : List St} {g fg last d1 d2 d3 m : ℕ} {uses : Bool}
    (hm : m = v.length) (hv : Rep L H mask v (insert a.w (insert b.w ((need y l).erase g))))
    (hp : v.Perm (a :: b :: rest)) (hg : g ∈ need y l) (hg0 : g ≠ 0) (hab : a.w ≠ b.w)
    (hgS : g ∉ insert a.w (insert b.w ((need y l).erase g)))
    (hfg : ∀ h, fg.testBit h = true → h < H ∧ Nat.land g (mask h) = 0)
    (hcard : (need y l).card ≤ k + 1) (hord : uses = true ∨ last ≤ g)
    (hb : Bud H mask d1 d2 d3 l)
    (hr : ∀ v', Rep L H mask v' (need y l) → r v' d1 d2 d3 g = true) :
    tryG L r k m rest (covL rest) d1 d2 d3 a b last uses g fg = true := by
  have hga : g ≠ a.w := fun e => hgS (by simp [e])
  have hgb : g ≠ b.w := fun e => hgS (by simp [e])
  have nd2 : ((a :: b :: rest).map Wr.w).Nodup := (hp.map Wr.w).nodup_iff.mp hv.nd
  simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or] at nd2
  obtain ⟨⟨_, har⟩, hbr, hrr⟩ := nd2
  have memr (x : ℕ) : x ∈ rest.map Wr.w ↔ x ∈ need y l ∧ x ≠ g ∧ x ≠ a.w ∧ x ≠ b.w := by
    have h1 : (x ∈ insert a.w (insert b.w ((need y l).erase g))) ↔ ∃ u ∈ a :: b :: rest, u.w = x := by
      rw [hv.mem]; exact ⟨fun ⟨u, hu, e⟩ => ⟨u, hp.mem_iff.mp hu, e⟩, fun ⟨u, hu, e⟩ => ⟨u, hp.mem_iff.mpr hu, e⟩⟩
    rw [List.mem_map]
    constructor
    · rintro ⟨u, hu, rfl⟩
      have h2 := h1.mpr ⟨u, by simp [hu], rfl⟩
      have n1 : u.w ≠ a.w := fun e => har (e ▸ List.mem_map_of_mem hu)
      have n2 : u.w ≠ b.w := fun e => hbr (e ▸ List.mem_map_of_mem hu)
      simp only [Finset.mem_insert, Finset.mem_erase] at h2
      rcases h2 with h | h | ⟨h3, h4⟩
      · exact absurd h n1
      · exact absurd h n2
      · exact ⟨h4, h3, n1, n2⟩
    · rintro ⟨h2, h3, h4, h5⟩
      obtain ⟨u, hu, e⟩ := h1.mp (by simp [h2, h3])
      simp only [List.mem_cons] at hu
      rcases hu with rfl | rfl | hu
      · exact absurd e.symm h4
      · exact absurd e.symm h5
      · exact ⟨u, hu, e⟩
  have hgr : g ∉ rest.map Wr.w := fun h => ((memr g).mp h).2.1 rfl
  have sepr : ∀ u ∈ rest, u.s = sepN L u.w := fun u hu => hv.sep u (hp.mem_iff.mpr (by simp [hu]))
  have flr : ∀ u ∈ rest, ∀ h, u.f.testBit h = true → h < H ∧ Nat.land u.w (mask h) = 0 :=
    fun u hu => hv.fl u (hp.mem_iff.mpr (by simp [hu]))
  have sepa := hv.sep a (hp.mem_iff.mpr (by simp))
  have sepb := hv.sep b (hp.mem_iff.mpr (by simp))
  have fla := hv.fl a (hp.mem_iff.mpr (by simp))
  have flb := hv.fl b (hp.mem_iff.mpr (by simp))
  have len : v.length = rest.length + 2 := by rw [hp.length_eq]; simp
  have b1 : Nat.beq g 0 = false := by rw [← Bool.not_eq_true, Nat.beq_eq]; exact hg0
  have b2 : Nat.beq g a.w = false := by rw [← Bool.not_eq_true, Nat.beq_eq]; exact hga
  have b3 : Nat.beq g b.w = false := by rw [← Bool.not_eq_true, Nat.beq_eq]; exact hgb
  have b4 : (cond uses true (Nat.ble last g)) = true := by
    rcases hord with h | h
    · rw [h]; rfl
    · cases uses
      · exact Nat.ble_eq.mpr h
      · rfl
  have b5 : sub fg d1 = true := flag_forced hy hb hg hfg
  have b6 : absentL g rest = true :=
    absent_true fun x hx e => hgr (e ▸ List.mem_map_of_mem hx)
  set G : Wr := ⟨g, sepN L g, fg⟩ with hG
  unfold tryG
  rw [b1, b2, b3, b4, b5, force_eq, force_eq, b6]
  simp only [cond_false, cond_true]
  by_cases hA : a.w ∈ need y l <;> by_cases hB : b.w ∈ need y l
  · have R : Rep L H mask (G :: a :: b :: rest) (need y l) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or]
        exact ⟨⟨hga, hgb, hgr⟩, ⟨hab, har⟩, hbr, hrr⟩
      · intro x
        constructor
        · intro hx
          by_cases e1 : x = g
          · exact ⟨G, by simp, e1.symm⟩
          by_cases e2 : x = a.w
          · exact ⟨a, by simp, e2.symm⟩
          by_cases e3 : x = b.w
          · exact ⟨b, by simp, e3.symm⟩
          obtain ⟨u, hu, e⟩ := List.mem_map.mp ((memr x).mpr ⟨hx, e1, e2, e3⟩)
          exact ⟨u, by simp [hu], e⟩
        · rintro ⟨u, hu, rfl⟩
          simp only [List.mem_cons] at hu
          rcases hu with rfl | rfl | rfl | hu
          · exact hg
          · exact hA
          · exact hB
          · exact ((memr _).mp (List.mem_map_of_mem hu)).1
      · intro u hu
        simp only [List.mem_cons] at hu
        rcases hu with rfl | rfl | rfl | hu
        · rfl
        · exact sepa
        · exact sepb
        · exact sepr u hu
      · intro u hu
        simp only [List.mem_cons] at hu
        rcases hu with rfl | rfl | rfl | hu
        · exact hfg
        · exact fla
        · exact flb
        · exact flr u hu
    have hl := rep_len R
    simp only [List.length_cons] at hl
    have c1 : Nat.ble m (Nat.succ k) = true := by rw [Nat.ble_eq]; omega
    have c2 : Nat.ble m k = true := by rw [Nat.ble_eq]; omega
    rw [c1, c2, flag_forced hy hb hA fla, flag_forced hy hb hB flb, hr _ R]
    simp
  · have R : Rep L H mask (G :: a :: rest) (need y l) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or]
        exact ⟨⟨hga, hgr⟩, har, hrr⟩
      · intro x
        constructor
        · intro hx
          by_cases e1 : x = g
          · exact ⟨G, by simp, e1.symm⟩
          by_cases e2 : x = a.w
          · exact ⟨a, by simp, e2.symm⟩
          by_cases e3 : x = b.w
          · exact absurd (e3 ▸ hx) hB
          obtain ⟨u, hu, e⟩ := List.mem_map.mp ((memr x).mpr ⟨hx, e1, e2, e3⟩)
          exact ⟨u, by simp [hu], e⟩
        · rintro ⟨u, hu, rfl⟩
          simp only [List.mem_cons] at hu
          rcases hu with rfl | rfl | hu
          · exact hg
          · exact hA
          · exact ((memr _).mp (List.mem_map_of_mem hu)).1
      · intro u hu
        simp only [List.mem_cons] at hu
        rcases hu with rfl | rfl | hu
        · rfl
        · exact sepa
        · exact sepr u hu
      · intro u hu
        simp only [List.mem_cons] at hu
        rcases hu with rfl | rfl | hu
        · exact hfg
        · exact fla
        · exact flr u hu
    have hl := rep_len R
    simp only [List.length_cons] at hl
    have c1 : Nat.ble m (Nat.succ k) = true := by rw [Nat.ble_eq]; omega
    have cv : Nat.beq (Nat.lor (Nat.lor (covL rest) (sepN L g)) a.s) L = true := by
      rw [Nat.beq_eq]
      refine Eq.trans ?_ (rep_cov hL R)
      apply Nat.eq_of_testBit_eq
      intro i
      simp only [covL, lor_bit, hG]
      cases (covL rest).testBit i <;> cases (sepN L g).testBit i <;> cases a.s.testBit i <;> rfl
    rw [c1, flag_forced hy hb hA fla, cv, hr _ R]
    simp
  · have R : Rep L H mask (G :: b :: rest) (need y l) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or]
        exact ⟨⟨hgb, hgr⟩, hbr, hrr⟩
      · intro x
        constructor
        · intro hx
          by_cases e1 : x = g
          · exact ⟨G, by simp, e1.symm⟩
          by_cases e2 : x = a.w
          · exact absurd (e2 ▸ hx) hA
          by_cases e3 : x = b.w
          · exact ⟨b, by simp, e3.symm⟩
          obtain ⟨u, hu, e⟩ := List.mem_map.mp ((memr x).mpr ⟨hx, e1, e2, e3⟩)
          exact ⟨u, by simp [hu], e⟩
        · rintro ⟨u, hu, rfl⟩
          simp only [List.mem_cons] at hu
          rcases hu with rfl | rfl | hu
          · exact hg
          · exact hB
          · exact ((memr _).mp (List.mem_map_of_mem hu)).1
      · intro u hu
        simp only [List.mem_cons] at hu
        rcases hu with rfl | rfl | hu
        · rfl
        · exact sepb
        · exact sepr u hu
      · intro u hu
        simp only [List.mem_cons] at hu
        rcases hu with rfl | rfl | hu
        · exact hfg
        · exact flb
        · exact flr u hu
    have hl := rep_len R
    simp only [List.length_cons] at hl
    have c1 : Nat.ble m (Nat.succ k) = true := by rw [Nat.ble_eq]; omega
    have cv : Nat.beq (Nat.lor (Nat.lor (covL rest) (sepN L g)) b.s) L = true := by
      rw [Nat.beq_eq]
      refine Eq.trans ?_ (rep_cov hL R)
      apply Nat.eq_of_testBit_eq
      intro i
      simp only [covL, lor_bit, hG]
      cases (covL rest).testBit i <;> cases (sepN L g).testBit i <;> cases b.s.testBit i <;> rfl
    rw [c1, flag_forced hy hb hB flb, cv, hr _ R]
    simp
  · have R : Rep L H mask (G :: rest) (need y l) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [List.map_cons, List.nodup_cons]
        exact ⟨hgr, hrr⟩
      · intro x
        constructor
        · intro hx
          by_cases e1 : x = g
          · exact ⟨G, by simp, e1.symm⟩
          by_cases e2 : x = a.w
          · exact absurd (e2 ▸ hx) hA
          by_cases e3 : x = b.w
          · exact absurd (e3 ▸ hx) hB
          obtain ⟨u, hu, e⟩ := List.mem_map.mp ((memr x).mpr ⟨hx, e1, e2, e3⟩)
          exact ⟨u, by simp [hu], e⟩
        · rintro ⟨u, hu, rfl⟩
          simp only [List.mem_cons] at hu
          rcases hu with rfl | hu
          · exact hg
          · exact ((memr _).mp (List.mem_map_of_mem hu)).1
      · intro u hu
        simp only [List.mem_cons] at hu
        rcases hu with rfl | hu
        · rfl
        · exact sepr u hu
      · intro u hu
        simp only [List.mem_cons] at hu
        rcases hu with rfl | hu
        · exact hfg
        · exact flr u hu
    have cv : Nat.beq (Nat.lor (covL rest) (sepN L g)) L = true := by
      rw [Nat.beq_eq]
      refine Eq.trans ?_ (rep_cov hL R)
      apply Nat.eq_of_testBit_eq
      intro i
      simp only [covL, lor_bit, hG]
      cases (covL rest).testBit i <;> cases (sepN L g).testBit i <;> rfl
    rw [cv, hr _ R]
    simp

lemma kills_cons (m : ℕ) (s : St) (l : List St) :
    kills m (s :: l) = kills m l + if killB m s = true then 1 else 0 := by
  rw [kills, kills, List.countP_cons]

lemma bud_next {H c1 c2 c3 K : ℕ} {mask : ℕ → ℕ} {s : St} {l : List St}
    (hb : Bud H mask c1 c2 c3 (s :: l))
    (hK : ∀ h, K.testBit h = true → h < H ∧ killB (mask h) s = true) :
    sub K c1 = true ∧ Bud H mask (Nat.lor c2 (Nat.xor c1 (Nat.land c1 K)))
      (Nat.lor c3 (Nat.xor c2 (Nat.land c2 K))) (Nat.xor c3 (Nat.land c3 K)) l := by
  constructor
  · refine sub_true fun h hh => ?_
    obtain ⟨h1, h2⟩ := hK h hh
    refine (hb h h1).2.1 ?_
    rw [kills_cons, if_pos h2]; omega
  · intro h hh
    obtain ⟨b0, b1, b2, b3⟩ := hb h hh
    rw [kills_cons] at b0 b1 b2 b3
    simp only [lor_bit, xor_bit, land_bit]
    cases hk : K.testBit h
    · refine ⟨by split_ifs at b0 <;> omega, fun h1 => ?_, fun h2 => ?_, fun h3 => ?_⟩
      · rw [b1 (by omega)]; simp
      · rw [b2 (by omega)]; simp
      · rw [b3 (by omega)]; simp
    · rw [if_pos (hK h hk).2] at b0 b1 b2 b3
      refine ⟨by omega, fun h1 => ?_, fun h2 => ?_, fun h3 => ?_⟩
      · rw [b2 (by omega)]; simp
      · rw [b3 (by omega)]; simp
      · omega

lemma tryP_true {L H y k : ℕ} {mask : ℕ → ℕ}
    (hy : ∀ h < H, Nat.land y (mask h) ≠ 0)
    (hL : ∀ i, L.testBit i = true → y.testBit i ≠ y.testBit (143 + i))
    {r : Next} {v rest : List Wr} {a b : Wr} {s : St} {l : List St} {last c1 c2 c3 m : ℕ} (t : Fin 4)
    (ht : opN t a.w b.w = s.val) (hm : m = v.length)
    (hv : Rep L H mask v (insert a.w (insert b.w ((need y l).erase s.val))))
    (hp : v.Perm (a :: b :: rest)) (hg : s.val ∈ need y l) (hg0 : s.val ≠ 0) (hab : a.w ≠ b.w)
    (hgS : s.val ∉ insert a.w (insert b.w ((need y l).erase s.val)))
    (hcard : (need y l).card ≤ k + 1) (hord : a.w = last ∨ b.w = last ∨ last ≤ s.val)
    (hkill : ∀ m, Nat.land a.w m = 0 ∨ Nat.land b.w m = 0 → killB m s = true)
    (hb : Bud H mask c1 c2 c3 (s :: l))
    (hr : ∀ v' d1 d2 d3, Rep L H mask v' (need y l) → Bud H mask d1 d2 d3 l →
      r v' d1 d2 d3 s.val = true) :
    tryP L r k m c1 c2 c3 last a b rest = true := by
  have fla := hv.fl a (hp.mem_iff.mpr (by simp))
  have flb := hv.fl b (hp.mem_iff.mpr (by simp))
  have hK : ∀ h, (Nat.lor a.f b.f).testBit h = true → h < H ∧ killB (mask h) s = true := by
    intro h hh
    rw [lor_bit, Bool.or_eq_true] at hh
    rcases hh with hh | hh
    · exact ⟨(fla h hh).1, hkill _ (Or.inl (fla h hh).2)⟩
    · exact ⟨(flb h hh).1, hkill _ (Or.inr (flb h hh).2)⟩
  obtain ⟨b1, hb'⟩ := bud_next hb hK
  have b2 : sub (flL rest) (Nat.lor c2 (Nat.xor c1 (Nat.land c1 (Nat.lor a.f b.f)))) = true := by
    refine sub_true fun h hh => ?_
    rw [fl_bit, List.any_eq_true] at hh
    obtain ⟨u, hu, hf⟩ := hh
    have uv := hp.mem_iff.mpr (show u ∈ a :: b :: rest by simp [hu])
    obtain ⟨h1, h2⟩ := hv.fl u uv h hf
    refine (hb' h h1).2.1 (kill_forced (hy h h1) l ?_ h2)
    have hS := (hv.mem u.w).mpr ⟨u, uv, rfl⟩
    have nd2 : ((a :: b :: rest).map Wr.w).Nodup := (hp.map Wr.w).nodup_iff.mp hv.nd
    simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or] at nd2
    obtain ⟨⟨_, har⟩, hbr, _⟩ := nd2
    simp only [Finset.mem_insert, Finset.mem_erase] at hS
    rcases hS with e | e | ⟨_, e⟩
    · exact absurd (e ▸ List.mem_map_of_mem hu) har
    · exact absurd (e ▸ List.mem_map_of_mem hu) hbr
    · exact e
  have hord' : (Nat.beq a.w last || Nat.beq b.w last) = true ∨ last ≤ s.val := by
    rcases hord with h | h | h
    · left; rw [h, Nat.beq_refl]; rfl
    · left; rw [h, Nat.beq_refl]; exact Bool.or_true _
    · exact Or.inr h
  have G (fg : ℕ) (hfg : ∀ h, fg.testBit h = true → h < H ∧ Nat.land s.val (mask h) = 0) :=
    tryG_true (m := m) (last := last) (uses := Nat.beq a.w last || Nat.beq b.w last) (fg := fg)
      hy hL hm hv hp hg hg0 hab hgS hfg hcard hord' hb' (fun v' hv' => hr v' _ _ _ hv' hb')
  have z (c x : ℕ) : Nat.land (opN t a.w b.w) c = opN t (Nat.land a.w c) (Nat.land b.w c) :=
    land_op t _ _ c
  unfold tryP
  rw [force_eq, b1]
  simp only [cond_true, force_eq]
  rw [b2]
  simp only [cond_true]
  rw [Bool.or_eq_true, Bool.or_eq_true, Bool.or_eq_true]
  fin_cases t
  · left
    have e : Nat.land a.w b.w = s.val := ht
    rw [e]
    refine G _ fun h hh => ?_
    rw [lor_bit, Bool.or_eq_true] at hh
    rw [← ht]
    refine ⟨(hK h (by rw [lor_bit, Bool.or_eq_true]; exact hh)).1, ?_⟩
    rw [z _ 0]
    rcases hh with hh | hh
    · rw [(fla h hh).2]
      rcases opN_zero_left 0 (Nat.land b.w (mask h)) with e | e
      · exact e
      · apply Nat.eq_of_testBit_eq; intro i; rw [opN_bit]; simp [opB]
    · rw [(flb h hh).2]
      apply Nat.eq_of_testBit_eq; intro i; rw [opN_bit]; simp [opB]
  · right; left
    have e : Nat.lor a.w b.w = s.val := ht
    rw [e]
    refine G _ fun h hh => ?_
    rw [land_bit, Bool.and_eq_true] at hh
    rw [← ht]
    refine ⟨(fla h hh.1).1, ?_⟩
    rw [z _ 0, (fla h hh.1).2, (flb h hh.2).2]
    apply Nat.eq_of_testBit_eq; intro i; rw [opN_bit]; simp [opB]
  · right; right; left
    have e : Nat.xor a.w (Nat.land a.w b.w) = s.val := ht
    rw [e]
    refine G _ fun h hh => ?_
    rw [← ht]
    refine ⟨(fla h hh).1, ?_⟩
    rw [z _ 0, (fla h hh).2]
    apply Nat.eq_of_testBit_eq; intro i; rw [opN_bit]; simp [opB]
  · right; right; right
    have e : Nat.xor b.w (Nat.land a.w b.w) = s.val := ht
    rw [e]
    refine G _ fun h hh => ?_
    rw [← ht]
    refine ⟨(flb h hh).1, ?_⟩
    rw [z _ 0, (flb h hh).2]
    apply Nat.eq_of_testBit_eq; intro i; rw [opN_bit]; simp [opB]

lemma level {L H y k : ℕ} {mask : ℕ → ℕ}
    (hy : ∀ h < H, Nat.land y (mask h) ≠ 0)
    (hL : ∀ i, L.testBit i = true → y.testBit i ≠ y.testBit (143 + i))
    {r : Next} {W : Set ℕ} {v : List Wr} {s : St} {l : List St} {last c1 c2 c3 : ℕ}
    (hV : Valid y W (s :: l)) (h0 : 0 ∈ W) (hU : Useful y (s :: l)) (hk : (s :: l).length ≤ k + 1)
    (hC : Chain last (s :: l)) (hv : Rep L H mask v (need y (s :: l)))
    (hb : Bud H mask c1 c2 c3 (s :: l))
    (hr : ∀ v' d1 d2 d3, Rep L H mask v' (need y l) → Bud H mask d1 d2 d3 l →
      r v' d1 d2 d3 s.val = true) :
    anyP (tryP L r k (lenL v) c1 c2 c3 last) (pairsA [] v) = true := by
  obtain ⟨fa, fb, fab, fv, _, _, fS⟩ := step_facts hV h0
  obtain ⟨ua, hua, ea⟩ := (hv.mem s.a).mp (by simp [need])
  obtain ⟨ub, hub, eb⟩ := (hv.mem s.b).mp (by simp [need])
  have hne : ua ≠ ub := fun e => fab (by rw [← ea, ← eb, e])
  obtain ⟨rest, hmem, hperm⟩ := pairsA_spec ua ub hne v [] hua hub
  have hcard : (need y l).card ≤ k + 1 := by
    have := need_card l hU.2
    simp only [List.length_cons] at hk
    omega
  have hg := hU.1
  have eN : need y (s :: l) = insert s.a (insert s.b ((need y l).erase s.val)) := rfl
  rcases hmem with hm | hm
  · refine anyP_true hm (tryP_true hy hL s.t (by rw [ea, eb]; rfl) (lenL_eq v) ?_ hperm hg fv
      (by rw [ea, eb]; exact fab) ?_ hcard ?_ ?_ hb hr)
    · rw [ea, eb]; exact hv
    · rw [ea, eb]; exact fS
    · rw [ea, eb]; exact hC.1
    · intro m h
      rw [ea, eb] at h
      unfold killB
      rcases h with h | h
      · rw [h]; rfl
      · rw [h]; exact Bool.or_true _
  · have hv2 : Rep L H mask v (insert ub.w (insert ua.w ((need y l).erase s.val))) := by
      rw [ea, eb, Finset.insert_comm]; exact hv
    refine anyP_true hm (tryP_true hy hL (swapT s.t) ?_ (lenL_eq v) hv2
      (hperm.trans (List.Perm.swap ub ua rest)) hg fv (by rw [ea, eb]; exact fab.symm) ?_ hcard ?_ ?_
      hb hr)
    · rw [ea, eb, ← opN_swap]; rfl
    · rw [ea, eb, Finset.insert_comm]; exact fS
    · rw [ea, eb]
      rcases hC.1 with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · intro m h
      rw [ea, eb] at h
      unfold killB
      rcases h with h | h
      · rw [h]; exact Bool.or_true _
      · rw [h]; rfl

lemma isT_true {L H y : ℕ} {mask : ℕ → ℕ} {v : List Wr} (hv : Rep L H mask v (need y [])) :
    isT y v = true := by
  have hl := rep_len hv
  rw [need, Finset.card_singleton] at hl
  obtain ⟨u, rfl⟩ := List.length_eq_one_iff.mp hl
  have : u.w ∈ need y [] := (hv.mem u.w).mpr ⟨u, by simp, rfl⟩
  rw [need, Finset.mem_singleton] at this
  rw [isT, this, Nat.beq_refl]

theorem search_complete {L H y : ℕ} {mask : ℕ → ℕ}
    (hy : ∀ h < H, Nat.land y (mask h) ≠ 0)
    (hL : ∀ i, L.testBit i = true → y.testBit i ≠ y.testBit (143 + i)) (k : ℕ) :
    ∀ (l : List St) (W : Set ℕ) (v : List Wr) (last c1 c2 c3 : ℕ), Valid y W l → 0 ∈ W →
      Useful y l → l.length ≤ k → Chain last l → Rep L H mask v (need y l) →
      Bud H mask c1 c2 c3 l → search L y k v c1 c2 c3 last = true := by
  induction k with
  | zero =>
    intro l W v last c1 c2 c3 hV h0 hU hk hC hv hb
    have : l = [] := List.length_eq_zero_iff.mp (by omega)
    subst this
    exact isT_true hv
  | succ k ih =>
    intro l W v last c1 c2 c3 hV h0 hU hk hC hv hb
    rw [search, Bool.or_eq_true]
    cases l with
    | nil => exact Or.inl (isT_true hv)
    | cons s l =>
      refine Or.inr (level hy hL hV h0 hU hk hC hv hb fun v' d1 d2 d3 hv' hb' => ?_)
      exact ih l _ v' s.val d1 d2 d3 hV.2.2.2 (Or.inr h0) hU.2 (by simpa using hk) hC.2 hv' hb'


-- Part 4: from derivations to the search, and the theta graph.

lemma need_ne_zero {y : ℕ} (hy : y ≠ 0) (l : List St) : ∀ {W : Set ℕ}, Valid y W l → 0 ∈ W →
    ∀ x ∈ need y l, x ≠ 0 := by
  induction l with
  | nil => intro W _ _ x hx; rw [need, Finset.mem_singleton] at hx; rw [hx]; exact hy
  | cons s l ih =>
    intro W h h0 x hx
    obtain ⟨fa, fb, _⟩ := step_facts h h0
    rw [need, Finset.mem_insert, Finset.mem_insert, Finset.mem_erase] at hx
    rcases hx with rfl | rfl | ⟨_, h2⟩
    · exact fa
    · exact fb
    · exact ih h.2.2.2 (Or.inr h0) x h2

def neededB (L : ℕ) (ws : List Wr) : Bool :=
  ws.all fun u => !(Nat.beq (covL (ws.filter fun x => !(Nat.beq x.w u.w))) L)

lemma root_rep {L H y : ℕ} {mask : ℕ → ℕ}
    (hL : ∀ i, L.testBit i = true → y.testBit i ≠ y.testBit (143 + i)) (hy : y ≠ 0)
    {ws : List Wr} (hnd : (ws.map Wr.w).Nodup) (hs : ∀ u ∈ ws, u.s = sepN L u.w)
    (hf : ∀ u ∈ ws, ∀ h, u.f.testBit h = true → h < H ∧ Nat.land u.w (mask h) = 0)
    (hn : neededB L ws = true) {W : Set ℕ} {l : List St} (hV : Valid y W l) (h0 : 0 ∈ W)
    (hW : ∀ x ∈ W, x = 0 ∨ ∃ u ∈ ws, u.w = x) : Rep L H mask ws (need y l) := by
  have hsub : ∀ x ∈ need y l, ∃ u ∈ ws, u.w = x := fun x hx =>
    (hW x (need_sub l hV x hx)).resolve_left (need_ne_zero hy l hV h0 x hx)
  refine ⟨hnd, fun x => ⟨hsub x, ?_⟩, hs, hf⟩
  rintro ⟨u, hu, rfl⟩
  by_contra hc
  have hc1 := List.all_eq_true.mp hn u hu
  have hc2 : covL (ws.filter fun x => !(Nat.beq x.w u.w)) = L := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [cov_bit]
    cases hi : L.testBit i
    · rw [List.any_eq_false]
      intro q hq
      rw [hs q (List.mem_of_mem_filter hq), sepN_bit, hi]; simp
    · rw [List.any_eq_true]
      by_contra hd
      push Not at hd
      refine hL i hi (need_agree l fun x hx => ?_)
      obtain ⟨q, hq, rfl⟩ := hsub x hx
      have hne : q.w ≠ u.w := fun e => hc (e ▸ hx)
      have hq' : q ∈ ws.filter fun x => !(Nat.beq x.w u.w) := by
        rw [List.mem_filter]
        refine ⟨hq, ?_⟩
        have : Nat.beq q.w u.w = false := by rw [← Bool.not_eq_true, Nat.beq_eq]; exact hne
        rw [this]; rfl
      have := hd q hq'
      rw [hs q hq, sepN_bit, hi] at this
      cases h1 : q.w.testBit i <;> cases h2 : q.w.testBit (143 + i) <;> simp_all
  rw [hc2, Nat.beq_refl] at hc1
  exact Bool.false_ne_true hc1

-- no derivation when the plain search fails
theorem refute {L y K : ℕ} (hL : ∀ i, L.testBit i = true → y.testBit i ≠ y.testBit (143 + i))
    (hy : y ≠ 0) {ws : List Wr} (hnd : (ws.map Wr.w).Nodup) (hs : ∀ u ∈ ws, u.s = sepN L u.w)
    (hf : ∀ u ∈ ws, u.f = 0) (hn : neededB L ws = true)
    (hsearch : search L y K ws 0 0 0 0 = false) {W : Set ℕ} (h0 : 0 ∈ W)
    (hW : ∀ x ∈ W, x = 0 ∨ ∃ u ∈ ws, u.w = x) : ¬ Der opN K W y := by
  intro h
  obtain ⟨l, hk, hV, hU, hC, _⟩ := exists_sorted h
  have hrep : Rep L 0 (fun _ => 0) ws (need y l) :=
    root_rep hL hy hnd hs (fun u hu h hh => by rw [hf u hu] at hh; simp at hh) hn hV h0 hW
  have := search_complete (H := 0) (mask := fun _ => 0) (fun h hh => by omega) hL K l W ws 0 0 0 0
    hV h0 hU hk hC hrep (fun h hh => by omega)
  rw [hsearch] at this
  exact Bool.false_ne_true this

lemma anyP_append (p : Wr → Wr → List Wr → Bool) (a b : List (Wr × Wr × List Wr)) :
    anyP p (a ++ b) = (anyP p a || anyP p b) := by
  induction a with
  | nil => rfl
  | cons x l ih => rw [List.cons_append, anyP, anyP, ih, Bool.or_assoc]

lemma anyP_chunks (p : Wr → Wr → List Wr → Bool) (m : ℕ) (n : ℕ) :
    ∀ l : List (Wr × Wr × List Wr), l.length ≤ m * n →
      (∀ i < n, anyP p ((l.drop (m * i)).take m) = false) → anyP p l = false := by
  induction n with
  | zero =>
    intro l hl _
    have : l = [] := List.length_eq_zero_iff.mp (by omega)
    rw [this]; rfl
  | succ n ih =>
    intro l hl h
    rw [← List.take_append_drop m l, anyP_append]
    have h1 := h 0 (by omega)
    rw [Nat.mul_zero, List.drop_zero] at h1
    rw [h1, Bool.false_or]
    refine ih _ (by rw [List.length_drop, Nat.mul_succ] at *; omega) fun i hi => ?_
    have := h (i + 1) (by omega)
    rw [List.drop_drop, show m + m * i = m * (i + 1) by ring]
    exact this

structure Kid where
  v : List Wr
  c1 : ℕ
  c2 : ℕ
  c3 : ℕ
  g : ℕ

def eqL : List Wr → List Wr → Bool
  | [], [] => true
  | a :: l, b :: m => Nat.beq a.w b.w && (Nat.beq a.s b.s && (Nat.beq a.f b.f && eqL l m))
  | _, _ => false

lemma eqL_eq (a : List Wr) : ∀ b, eqL a b = true → a = b := by
  induction a with
  | nil => intro b h; cases b with
    | nil => rfl
    | cons => simp [eqL] at h
  | cons x l ih =>
    intro b h
    cases b with
    | nil => simp [eqL] at h
    | cons y m =>
      rw [eqL, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.beq_eq,
        Nat.beq_eq] at h
      obtain ⟨h1, h2, h3, h4⟩ := h
      rw [ih m h4]
      cases x; cases y
      simp only at h1 h2 h3
      rw [h1, h2, h3]

def isKid (v : List Wr) (c1 c2 c3 g : ℕ) : List Kid → Bool
  | [] => false
  | q :: l => (Nat.beq q.g g && (Nat.beq q.c1 c1 && (Nat.beq q.c2 c2 && (Nat.beq q.c3 c3 &&
      eqL q.v v)))) || isKid v c1 c2 c3 g l

lemma isKid_mem {v : List Wr} {c1 c2 c3 g : ℕ} (ks : List Kid)
    (h : isKid v c1 c2 c3 g ks = true) : ⟨v, c1, c2, c3, g⟩ ∈ ks := by
  induction ks with
  | nil => simp [isKid] at h
  | cons q l ih =>
    rw [isKid, Bool.or_eq_true] at h
    rcases h with h | h
    · simp only [Bool.and_eq_true, Nat.beq_eq] at h
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      have := eqL_eq _ _ h5
      cases q
      simp only at h1 h2 h3 h4 this
      subst h1 h2 h3 h4 this
      simp
    · exact List.mem_cons_of_mem _ (ih h)

def memN (g : ℕ) : List ℕ → Bool
  | [] => false
  | x :: l => Nat.beq x g || memN g l

def rootNext (al : List ℕ) (ks : List Kid) : Next := fun v c1 c2 c3 g =>
  cond (memN g al) (!(isKid v c1 c2 c3 g ks)) false

-- row permutations

def Bdd (N x : ℕ) : Prop := ∀ i, N ≤ i → x.testBit i = false

lemma bdd_op {N : ℕ} (t : Fin 4) {a b : ℕ} (ha : Bdd N a) (hb : Bdd N b) : Bdd N (opN t a b) := by
  intro i hi
  rw [opN_bit, ha i hi, hb i hi]
  fin_cases t <;> rfl

def sIdx (T : ℕ) (i : ℕ) : ℕ :=
  cond (Nat.blt i 143) (Nat.land (Nat.shiftRight T (8 * i)) 255)
    (143 + Nat.land (Nat.shiftRight T (8 * (i - 143))) 255)

def sg (N T : ℕ) (w : ℕ) : ℕ := Nat.ofBits fun i : Fin N => w.testBit (sIdx T i.val)

lemma sg_bit (N T w i : ℕ) (hi : i < N) : (sg N T w).testBit i = w.testBit (sIdx T i) := by
  rw [sg, Nat.testBit_ofBits_lt _ _ hi]

lemma sg_bdd (N T w : ℕ) : Bdd N (sg N T w) := fun i hi => by rw [sg, Nat.testBit_ofBits_ge _ _ hi]

lemma sg_op (N T : ℕ) (t : Fin 4) (a b : ℕ) : sg N T (opN t a b) = opN t (sg N T a) (sg N T b) := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < N
  · rw [sg_bit _ _ _ _ hi, opN_bit, opN_bit, sg_bit _ _ _ _ hi, sg_bit _ _ _ _ hi]
  · rw [sg_bdd _ _ _ i (by omega), bdd_op t (sg_bdd N T a) (sg_bdd N T b) i (by omega)]

lemma sg_sg {N : ℕ} (T : ℕ) (hT : ∀ i < N, sIdx T i < N ∧ sIdx T (sIdx T i) = i) {w : ℕ} (hw : Bdd N w) :
    sg N T (sg N T w) = w := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < N
  · rw [sg_bit _ _ _ _ hi, sg_bit _ _ _ _ (hT i hi).1, (hT i hi).2]
  · rw [sg_bdd _ _ _ i (by omega), hw i (by omega)]

def mapSt (N T : ℕ) (s : St) : St := ⟨s.t, sg N T s.a, sg N T s.b⟩

lemma mapSt_val (N T : ℕ) (s : St) : (mapSt N T s).val = sg N T s.val := (sg_op N T _ _ _).symm

lemma valid_map {N : ℕ} (T : ℕ) (hT : ∀ i < N, sIdx T i < N ∧ sIdx T (sIdx T i) = i) {y : ℕ}
    (l : List St) : ∀ {W : Set ℕ}, (∀ x ∈ W, Bdd N x) → Valid y W l →
      Valid (sg N T y) (sg N T '' W) (l.map (mapSt N T)) := by
  induction l with
  | nil => intro W _ h; exact ⟨y, h, rfl⟩
  | cons s l ih =>
    intro W hb h
    obtain ⟨ha, hb', hc, hv⟩ := h
    have bv : Bdd N s.val := bdd_op s.t (hb _ ha) (hb _ hb')
    refine ⟨⟨s.a, ha, rfl⟩, ⟨s.b, hb', rfl⟩, ?_, ?_⟩
    · rw [mapSt_val]
      rintro ⟨x, hx, e⟩
      have := congrArg (sg N T) e
      rw [sg_sg T hT (hb x hx), sg_sg T hT bv] at this
      exact hc (this ▸ hx)
    · rw [mapSt_val, ← Set.image_insert_eq]
      refine ih ?_ hv
      rintro x (rfl | hx)
      · exact bv
      · exact hb x hx

lemma sg_eq {N T x x' : ℕ} (hx' : Bdd N x') (h : ∀ i < N, x'.testBit i = x.testBit (sIdx T i)) :
    sg N T x = x' := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < N
  · rw [sg_bit _ _ _ _ hi, h i hi]
  · rw [sg_bdd _ _ _ i (by omega), hx' i (by omega)]

lemma bdd_of_lt {N x : ℕ} (h : x < 2 ^ N) : Bdd N x := fun i hi =>
  Nat.testBit_lt_two_pow (lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega) hi))


-- Part 5: data of the theta graph and the searches.

def LO : ℕ := 0x7fffffffffffffffffffffffffffffffffff

def ipL : List ℕ := [0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f]

def ip (i : Fin 7) : ℕ := ipL.getD i.val 0

def maskL : List ℕ := [0x78f1e3c78f1e3c58a850404fffffffffffffffffffff01fc00000000000ffffffffffff, 0x39f3e7cf9f3e7cfa75ffffffad9022fffffffffffff80fe0000003ffffff000000ffffff, 0xe1c3870e1c38707fe005fffd26fff802ffffffffc07ffe03f8ffc001fff001fff000fff, 0x1ab56ad5ab56ad58fe2ff2bf87f0ffa5faaf80fe03ffffffffb1fc1fe03f0fe0ff03f00f, 0x3a74e9d3a74e9d3b7f7afbfb18f38f8e78faff01fffff01ffff6fce1e7c031e70f1cf1f0, 0x274e9d3a74e9d3af9fd33d63fb7fdd5a9d59fffe03f80fffffdf3f2678c7f6eb30253233, 0x35ebd7af5ebd7affa7ffadcdffbf71ffd7750001fc07ffffffff4fde1b1bff74c3d80cc0]

def mask (h : ℕ) : ℕ := maskL.getD h 0

def root : List Wr := [⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩]

def pm (p : Fin 3) (i : Fin 7) : Fin 7 :=
  match p with
  | 0 => ![3, 6, 2, 0, 5, 4, 1] i
  | 1 => ![4, 6, 2, 5, 0, 3, 1] i
  | 2 => ![5, 1, 2, 4, 3, 0, 6] i

def Tn (p : Fin 3) : ℕ :=
  match p with
  | 0 => 0x5d585a5b595c57726d6f706e716c6b666869676a65645f616260635e87828485838681807b7d7e7c7f7a797476777578738e898b8c8a8d884515123a3736082309212005044746494856171614132e2f2c2d3938533c3b5251240b0a2207063f403d3e110e0f10270c0d354f324d4c02031a1b1c1d00014443554241542b28292a252634334e5031304b4a1e1f1819
  | 1 => 0x6c6d6f706e717257585a5b595c5d7a7b7d7e7c7f805e5f616260636488898b8c8a8d8e65666869676a6b73747677757879818284858386871115103503023223091d1c0100434416172b484941422e2f292a3334240a0b1e1f533b3c5030313f400e0f453d3e12270c0d3a4f081a1b36374d4c2021040546475513142856542c2d252638394e220607181952514b4a
  | 2 => 0x81868584838287888d8c8b8a898e656a696867666b73787776757479575c5b5a59585d7a7f7e7d7c7b805e636261605f646c71706f6e6d722b5528241e1f224f4e1a1b1819161743441146471314403f0f0e0a0b35333403023a38390806072f2e2a29562d2c542726255323501d1c515221204c4d4a4b48491541421045123e3d0d0c3b3c09323031010037360504

def allowed : List ℕ := [0x3ffffc000000000000000000, 0x1fc07000000000ffe000000000, 0xfe00009031e183f000000000000, 0x81020408102040000400040400202102040000000000000000001800380810c0c20c0c, 0x8102040810204000040004048022a562a60001fc07f0000000000000000914cfdacdcc, 0x183060c183060c0008500002500007180000000000000000000031e0000ce0000e30000, 0x183060c183060c0008500002d90007fd000000003f8001fc00000000000ffe000fff000, 0x183060c183060c000850404a5002071870500fe00000fe00000031e183f000000e30e0f, 0x2040810204081000800000000408c0000000000000000000000b0000000008b3c000000, 0x2040810204081000800000000408e00288afffe03f80000000000000000008b3c27f33f, 0x40810204081020480000000420c50000000000000000000000900000000ce18f0000000, 0x40810204081020480000404c20c7000070500fe00000fe000090000183f0018f0000e0f, 0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000, 0x50a142850a1428400800400600c00500500000000000000000803001800c01800e00e00, 0x50a142850a1428480810400e30c5050850100fe00000fe0000903061807c60830210203, 0x58b162c58b162c480850404e70c70718705000000000fe00009031e181bce10c0c00c00, 0x58b162c58b162c480850404e70c7071870500fe00000000000000000000ce18f0e30e0f, 0x60c183060c183058a000000526fdd00000000000000001fffdf3c000000f6eb30000000, 0x60c183060c183058a000000526fdd00000000000007f0003f8ffc000000001fff000000, 0x78f1e3c78f1e3c58a850404f76ffd71870500fe0007ffffffffff1e183fffffffe30e0f, 0xe1c3870e1c38705da005232526fdf00288afffe03fff01ffffffc21e4e4ffffff27f33f, 0xf9f3e7cf9f3e7c4d8855636e74cfe71af8ffffe03f80fe00009b33ffcffce9bfce7ff3f, 0x1dbb76eddbb76ed4e0adc69ce78c72f5e7a700fffc07ffe00029c3df9f3fcf1cfffbcfcf, 0x25cb972e5cb972e781d50d44ff0f707b87557ffffc000fe0004f03fe1ffffe1ff0ff0fff, 0x31e3c78f1e3c78f801ffa0002d90007fd00000000000001fc07003de0000ff6000d80000, 0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f, 0x37efdfbf7efdfbfd8bffa0007fffdd7fd000000003fff01fffffffffe000fffffffff000, 0x3dfbf7efdfbf7ef761fccfdc7c8f22ff67f67f01fc07f000006ec3f99ff8f91fcffecffc]

def L0 : ℕ := 0xf1e3c78f003c00000000000ffffffffffff
def Y0 : ℕ := 0x7ffffffff01fc00000000000ffffffffffff
def ws0 : List Wr := [⟨0x60c183060c183058a000000526fdd00000000000007f01fc00000000000ffffff000000, 0xc1830603000c000000000005b2045000000, 0⟩, ⟨0x183060c183060c0008500002d90007fd000000003f8001fc00000000000ffe000fff000, 0x3060c603003000000000000a4c000005000, 0⟩, ⟨0x50a142850a1428500800400780f005a05507f01fc000000000000000000f01f00fc0ff0, 0x5141450a002800000000000000100480550, 0⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000000000000000000ce18f0e30e0f, 0xb082c58b002c00000000000000010000005, 0⟩, ⟨0x8102040810204000040004048022a562a60001fc07f0000000000000000914cfdacdcc, 0x1023808e00040000000000000148a900880, 0⟩, ⟨0x2040810204081000800000000408e00288afffe03f80000000000000000008b3c27f33f, 0xb1610584001000000000000000a2027a22a, 0⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sub0 : search L0 Y0 7 ws0 0 0 0 0 = false := by decide +kernel

def L1 : ℕ := 0x73e7cf980e60000003ffffff000000ffffff
def Y1 : ℕ := 0x7ffffff80fe0000003ffffff000000ffffff
def ws1 : List Wr := [⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe0000003ffffff000000000000, 0x70e1c38000600000010a0809000000000000, 0⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f80000000003ffe000000000fff000, 0x63c78c800c6000000000a000000000005000, 0⟩, ⟨0x2142850a142850a201d00d402800005a05507f01fc000000000003e01fc0000000fc0ff0, 0x3184c6100840000000400540000000480550, 0⟩, ⟨0x183060c183060c000850404a5002071870500fe00000fe00000031e183f000000e30e0f, 0x3e00c180e00000002141036000000000005, 0⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc000000000000d98738000000dacdcc, 0x316309880620000000800200000000900880, 0⟩, ⟨0x8102040810204005000523200000200288afffe03f8000000000021e4e400000027f33f, 0x63c64318020000000021408000000027a22a, 0⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sub1 : search L1 Y1 6 ws1 0 0 0 0 = false := by decide +kernel

def L2 : ℕ := 0x1c387001c3800e0ffc001fff001fff000fff
def Y2 : ℕ := 0x7ffffc07ffe03f8ffc001fff001fff000fff
def ws2 : List Wr := [⟨0x81020408102040274005bfb000000000000000000000fe03f8ffc001fff000000000000, 0x102040010180060b14000809000000000000, 0⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f0003f8ffc000000001fff000000, 0xc18300101800804e8000000000045000000, 0⟩, ⟨0x40810204081020700000d40500f000005507f01fc000000000e00001fc0001f00000ff0, 0x141050008100040000000540000100000550, 0⟩, ⟨0x40810204081020480000404c20c7000070500fe00000fe000090000183f0018f0000e0f, 0x82820008280040000001036000010000005, 0⟩, ⟨0x8102040810204006000429c0000228022a60001fc07f0000000c00007380014cf000dcc, 0x10203000c20008000000020000148a000880, 0⟩, ⟨0xa142850a14285005800523200408e00288afffe000000000000b00004e4000b3c00033f, 0x810500142800a0000000080000a2000022a, 0⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sub2 : search L2 Y2 7 ws2 0 0 0 0 = false := by decide +kernel

def L3 : ℕ := 0x6a01ab56ad5ab1fc1fe03f0fe0ff03f00f
def Y3 : ℕ := 0xfe03ffffffffb1fc1fe03f0fe0ff03f00f
def ws3 : List Wr := [⟨0x183060c183060c18742af2bb000000000000000000000fe03fb1fc1fe03f000000000000, 0x60018300ac0281140a0009000000000000, 0⟩, ⟨0x2040810204081008a0000000260dd00000000000007f01fffb1fc0000000fe0ff000000, 0x80023108c58b0e80000000b2045000000, 0⟩, ⟨0x10a142850a142858002fa00005900025d000000003f8001fc030001fe0000fe00003f000, 0x4200a2142510800000a00004c000005000, 0⟩, ⟨0x810204081020408005000487007021820500fe00000fe00001001e003f0e00f003000f, 0x6800081680408000140036000010000005, 0⟩, ⟨0x18b162c58b162c50602cc29c048022a562a600000007f0000020c01980380900cf02c00c, 0x620188462c58800000000000008a000000, 0⟩, ⟨0xa142850a14285005800523200408e00288a80fe03f800000000b001e02400803c03f00f, 0x42010942850a000001400000002003a00a, 0⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sub3 : search L3 Y3 7 ws3 0 0 0 0 = false := by decide +kernel

def L4 : ℕ := 0x7401d3a7401d3a76fce1e7c031e70f1cf1f0
def Y4 : ℕ := 0x7f01fffff01ffff6fce1e7c031e70f1cf1f0
def ws4 : List Wr := [⟨0x3870e1c3870e1c3a757afbfb0000000000000000000000003ff6fce1e7c0000000000000, 0x7001c387001c020214000000000000000000, 0⟩, ⟨0x2040810204081010a00000010638d00000000000007f01ffff6fc00000031e70f000000, 0x4001027001c3874e8000000112005000000, 0⟩, ⟨0x3060c183060c1838017aa0000890000e5000000003f8001fc07000e1e00031e0001cf000, 0x600180a6000530000000a00020c000005000, 0⟩, ⟨0x2040810204081023015009401803000a00507f01fc000000004600e007c03007001c01f0, 0x3400d2040010200000400540000100080150, 0⟩, ⟨0x183060c183060c106028c2980080028460a20001fc07f0000020c0c1870001040f18c1c0, 0x30011184400c18000080020000040a100080, 0⟩, ⟨0xa142850a14285005800523200408e00288aff0003f800000000b021e4c000830c04f130, 0x6000530140050a000021408000020004a020, 0⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sub4 : search L4 Y4 7 ws4 0 0 0 0 = false := by decide +kernel

def L5 : ℕ := 0x4e9c027009d3a75f3f2678c7f6eb30253233
def Y5 : ℕ := 0x7ffe03f80fffffdf3f2678c7f6eb30253233
def ws5 : List Wr := [⟨0x204081020408102a15523963000000000000000000000fe03fdf3f2678c7000000000000, 0x4080020001d0070b15020801000000000000, 0⟩, ⟨0x60c183060c183058a000000526fdd00000000000000001fffdf3c000000f6eb30000000, 0xc1800600190a15428000000522000000000, 0⟩, ⟨0x2142850a142850a801d320002910005a9000000003f8001fc05003266000f6e000253000, 0x428400600843210000002000a4c000001000, 0⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f0000000000004e032018c0f00b00240230, 0x49402500952a50000000040000100000010, 0⟩, ⟨0x50a142850a1428480810400e30c5050850100fe00000fe0000903061807c60830210203, 0xa8800500882850002041006000010000001, 0⟩, ⟨0x2040810204081001800102200408c000808fffe03f800000000302060c4008b30253233, 0x4a9402500081020000204080000a20252222, 0⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sub5 : search L5 Y5 7 ws5 0 0 0 0 = false := by decide +kernel

def L6 : ℕ := 0x1ac06bd7af5ff4fde1b1bff74c3d80cc0
def Y6 : ℕ := 0x1fc07ffffffff4fde1b1bff74c3d80cc0
def ws6 : List Wr := [⟨0x3060c183060c183a257aa9c9000000000000000000000fe03fff4fde1b1b000000000000, 0x180060178058b050a0809000000000000, 0⟩, ⟨0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000, 0x20063118f1f4480000005b2041000000, 0⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd00000000000001fc07003de0000ff6000d80000, 0x18c063c62318000000000a44000000000, 0⟩, ⟨0x254a952a54a952a701d00d40780f005a05500001fc000000004e03c01b00f01400d80cc0, 0x8404a952a50000400100000000480440, 0⟩, ⟨0x58b162c58b162c480850404e70c70718705000000000fe00009031e181bce10c0c00c00, 0x2c00bc02c58002141012000000000000, 0⟩, ⟨0x10a142850a142850202c808c048020a542240001fc07f000002040d803180914c3d80cc0, 0x12804a428508000800200001482900880, 0⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sub6 : search L6 Y6 6 ws6 0 0 0 0 = false := by decide +kernel

def kids : List Kid := [
  ⟨[⟨0x3ffffc000000000000000000, 0x3ffffc000000000000000000, 3⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 126, 64, 0x3ffffc000000000000000000⟩,
  ⟨[⟨0x183060c183060c0008500002d90007fd000000003f8001fc00000000000ffe000fff000, 0x3060fe0307f0180010a0000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 122, 66, 0x183060c183060c0008500002d90007fd000000003f8001fc00000000000ffe000fff000⟩,
  ⟨[⟨0xfe00009031e183f000000000000, 0xfe00009031e183f000000000000, 17⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 110, 66, 0xfe00009031e183f000000000000⟩,
  ⟨[⟨0x58b162c58b162c480850404e70c7071870500fe00000000000000000000ce18f0e30e0f, 0xbe82c58b162c589010a0809000010000005, 16⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 110, 66, 0x58b162c58b162c480850404e70c7071870500fe00000000000000000000ce18f0e30e0f⟩,
  ⟨[⟨0x8102040810204000040004048022a562a60001fc07f0000000000000000914cfdacdcc, 0x103f80fe02040800008000800148a900880, 32⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 94, 66, 0x8102040810204000040004048022a562a60001fc07f0000000000000000914cfdacdcc⟩,
  ⟨[⟨0x2040810204081000800000000408e00288afffe03f80000000000000000008b3c27f33f, 0x7bf613d84081020010000000000a2027a22a, 64⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩], 127, 126, 2, 0x2040810204081000800000000408e00288afffe03f80000000000000000008b3c27f33f⟩,
  ⟨[⟨0x1fc07000000000ffe000000000, 0x1fc07000000000ffe000000000, 6⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 123, 64, 0x1fc07000000000ffe000000000⟩,
  ⟨[⟨0x37efdfbf7efdfbfd8bffa0007fffdd7fd000000003fff01fffffffffe000fffffffff000, 0x6fdfbc810de40804e800a000000045005000, 0⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 123, 64, 0x37efdfbf7efdfbfd8bffa0007fffdd7fd000000003fff01fffffffffe000fffffffff000⟩,
  ⟨[⟨0x60c183060c183058a000000526fdd00000000000007f0003f8ffc000000001fff000000, 0xc18306731833984e8000000a4c045000000, 2⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 123, 64, 0x60c183060c183058a000000526fdd00000000000007f0003f8ffc000000001fff000000⟩,
  ⟨[⟨0x40810204081020480000000420c50000000000000000000000900000000ce18f0000000, 0x810204081020400000000004a0050000000, 18⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 111, 64, 0x40810204081020480000000420c50000000000000000000000900000000ce18f0000000⟩,
  ⟨[⟨0x78f1e3c78f1e3c58a850404f76ffd71870500fe0007ffffffffff1e183fffffffe30e0f, 0xfe03c7f0e1c3874ea141036112005000005, 0⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 111, 64, 0x78f1e3c78f1e3c58a850404f76ffd71870500fe0007ffffffffff1e183fffffffe30e0f⟩,
  ⟨[⟨0x183060c183060c000850404a5002071870500fe00000fe00000031e183f000000e30e0f, 0x3f80c183f80c180021410364a0040000005, 16⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 111, 64, 0x183060c183060c000850404a5002071870500fe00000fe00000031e183f000000e30e0f⟩,
  ⟨[⟨0x60c183060c183058a000000526fdd00000000000000001fffdf3c000000f6eb30000000, 0xc183060c19cf9d42800000052348a000000, 2⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 95, 64, 0x60c183060c183058a000000526fdd00000000000000001fffdf3c000000f6eb30000000⟩,
  ⟨[⟨0x2040810204081000800000000408c0000000000000000000000b0000000008b3c000000, 0x408102040810200a0000000000a24000000, 66⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩], 127, 127, 0, 0x2040810204081000800000000408c0000000000000000000000b0000000008b3c000000⟩,
  ⟨[⟨0xe1c3870e1c38705da005232526fdf00288afffe03fff01ffffffc21e4e4ffffff27f33f, 0x63c6731e3398f1f4482140805b204127a22a, 0⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩], 127, 127, 0, 0xe1c3870e1c38705da005232526fdf00288afffe03fff01ffffffc21e4e4ffffff27f33f⟩,
  ⟨[⟨0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000, 0x8102047711dfbf4480000005b2a61000000, 2⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩], 127, 127, 0, 0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000⟩,
  ⟨[⟨0x183060c183060c0008500002500007180000000000000000000031e0000ce0000e30000, 0x3060c183060c18002140000840000000000, 20⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 107, 66, 0x183060c183060c0008500002500007180000000000000000000031e0000ce0000e30000⟩,
  ⟨[⟨0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f, 0x6b29aca6b28535800000b03620c010005005, 0⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 107, 66, 0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f⟩,
  ⟨[⟨0x40810204081020480000404c20c7000070500fe00000fe000090000183f0018f0000e0f, 0x8ee20408ee2040000001036840010000005, 16⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 107, 66, 0x40810204081020480000404c20c7000070500fe00000fe000090000183f0018f0000e0f⟩,
  ⟨[⟨0x31e3c78f1e3c78f801ffa0002d90007fd00000000000001fc07003de0000ff6000d80000, 0x63c78f1e3c67318000214000a4400027a000, 4⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩], 127, 123, 2, 0x31e3c78f1e3c78f801ffa0002d90007fd00000000000001fc07003de0000ff6000d80000⟩,
  ⟨[⟨0x50a142850a1428400800400600c00500500000000000000000803001800c01800e00e00, 0xa142850a142850002001000000000400400, 24⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 103, 66, 0x50a142850a1428400800400600c00500500000000000000000803001800c01800e00e00⟩,
  ⟨[⟨0x25cb972e5cb972e781d50d44ff0f707b87557ffffc000fe0004f03fe1ffffe1ff0ff0fff, 0x3468d25cb692e58000540576000110080155, 0⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 103, 66, 0x25cb972e5cb972e781d50d44ff0f707b87557ffffc000fe0004f03fe1ffffe1ff0ff0fff⟩,
  ⟨[⟨0x3dfbf7efdfbf7ef761fccfdc7c8f22ff67f67f01fc07f000006ec3f99ff8f91fcffecffc, 0x4f613d84f7efd800000004000018a000010, 0⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 87, 66, 0x3dfbf7efdfbf7ef761fccfdc7c8f22ff67f67f01fc07f000006ec3f99ff8f91fcffecffc⟩,
  ⟨[⟨0x81020408102040000400040400202102040000000000000000001800380810c0c20c0c, 0x10204081020408000100030001080800804, 48⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 79, 66, 0x81020408102040000400040400202102040000000000000000001800380810c0c20c0c⟩,
  ⟨[⟨0x1dbb76eddbb76ed4e0adc69ce78c72f5e7a700fffc07ffe00029c3df9f3fcf1cfffbcfcf, 0x3b8911dc488edd800284120600041a100081, 0⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 79, 66, 0x1dbb76eddbb76ed4e0adc69ce78c72f5e7a700fffc07ffe00029c3df9f3fcf1cfffbcfcf⟩,
  ⟨[⟨0x50a142850a1428480810400e30c5050850100fe00000fe0000903061807c60830210203, 0xaea2850aea2850002041006001090800801, 16⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 79, 66, 0x50a142850a1428480810400e30c5050850100fe00000fe0000903061807c60830210203⟩,
  ⟨[⟨0xf9f3e7cf9f3e7c4d8855636e74cfe71af8ffffe03f80fe00009b33ffcffce9bfce7ff3f, 0x60c07f01fc07cf800235509200020004a020, 0⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩], 127, 111, 2, 0xf9f3e7cf9f3e7c4d8855636e74cfe71af8ffffe03f80fe00009b33ffcffce9bfce7ff3f⟩,
  ⟨[⟨0x58b162c58b162c480850404e70c70718705000000000fe00009031e181bce10c0c00c00, 0xb162c58be82c5800214101200082023020a, 16⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩], 127, 111, 2, 0x58b162c58b162c480850404e70c70718705000000000fe00009031e181bce10c0c00c00⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootSearch : anyP (tryP LO (rootNext allowed kids) 9 (lenL root) 127 127 66 0) (pairsA [] root) = false := by decide +kernel

def kv0 : List Wr := [⟨0x3ffffc000000000000000000, 0x3ffffc000000000000000000, 3⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid0 : search LO LO 9 kv0 127 126 64 0x3ffffc000000000000000000 = false := by decide +kernel

def kv1 : List Wr := [⟨0x183060c183060c0008500002d90007fd000000003f8001fc00000000000ffe000fff000, 0x3060fe0307f0180010a0000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid1 : search LO LO 9 kv1 127 122 66 0x183060c183060c0008500002d90007fd000000003f8001fc00000000000ffe000fff000 = false := by decide +kernel

def kv2 : List Wr := [⟨0xfe00009031e183f000000000000, 0xfe00009031e183f000000000000, 17⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid2 : search LO LO 9 kv2 127 110 66 0xfe00009031e183f000000000000 = false := by decide +kernel

def kv3 : List Wr := [⟨0x58b162c58b162c480850404e70c7071870500fe00000000000000000000ce18f0e30e0f, 0xbe82c58b162c589010a0809000010000005, 16⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid3 : search LO LO 9 kv3 127 110 66 0x58b162c58b162c480850404e70c7071870500fe00000000000000000000ce18f0e30e0f = false := by decide +kernel

def kv4 : List Wr := [⟨0x8102040810204000040004048022a562a60001fc07f0000000000000000914cfdacdcc, 0x103f80fe02040800008000800148a900880, 32⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid4 : search LO LO 9 kv4 127 94 66 0x8102040810204000040004048022a562a60001fc07f0000000000000000914cfdacdcc = false := by decide +kernel

def kv5 : List Wr := [⟨0x2040810204081000800000000408e00288afffe03f80000000000000000008b3c27f33f, 0x7bf613d84081020010000000000a2027a22a, 64⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid5_0 : anyP (tryP LO (search LO LO 8) 8 (lenL kv5) 127 126 2 0x2040810204081000800000000408e00288afffe03f80000000000000000008b3c27f33f) (((pairsA [] kv5).drop (6 * 0)).take 6) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid5_1 : anyP (tryP LO (search LO LO 8) 8 (lenL kv5) 127 126 2 0x2040810204081000800000000408e00288afffe03f80000000000000000008b3c27f33f) (((pairsA [] kv5).drop (6 * 1)).take 6) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid5_2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv5) 127 126 2 0x2040810204081000800000000408e00288afffe03f80000000000000000008b3c27f33f) (((pairsA [] kv5).drop (6 * 2)).take 6) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid5_3 : anyP (tryP LO (search LO LO 8) 8 (lenL kv5) 127 126 2 0x2040810204081000800000000408e00288afffe03f80000000000000000008b3c27f33f) (((pairsA [] kv5).drop (6 * 3)).take 6) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid5_4 : anyP (tryP LO (search LO LO 8) 8 (lenL kv5) 127 126 2 0x2040810204081000800000000408e00288afffe03f80000000000000000008b3c27f33f) (((pairsA [] kv5).drop (6 * 4)).take 6) = false := by decide +kernel

theorem kid5 : search LO LO 9 kv5 127 126 2 0x2040810204081000800000000408e00288afffe03f80000000000000000008b3c27f33f = false := by
  have h1 : isT LO kv5 = false := by decide +kernel
  have h2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv5) 127 126 2 0x2040810204081000800000000408e00288afffe03f80000000000000000008b3c27f33f) (pairsA [] kv5) = false := by
    refine anyP_chunks _ 6 5 _ (by decide +kernel) fun i hi => ?_
    interval_cases i
    · exact kid5_0
    · exact kid5_1
    · exact kid5_2
    · exact kid5_3
    · exact kid5_4
  rw [search, h1, h2]; rfl

def kv6 : List Wr := [⟨0x1fc07000000000ffe000000000, 0x1fc07000000000ffe000000000, 6⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid6 : search LO LO 9 kv6 127 123 64 0x1fc07000000000ffe000000000 = false := by decide +kernel

def kv7 : List Wr := [⟨0x37efdfbf7efdfbfd8bffa0007fffdd7fd000000003fff01fffffffffe000fffffffff000, 0x6fdfbc810de40804e800a000000045005000, 0⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_0 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 0x37efdfbf7efdfbfd8bffa0007fffdd7fd000000003fff01fffffffffe000fffffffff000) (((pairsA [] kv7).drop (1 * 0)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_1 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 0x37efdfbf7efdfbfd8bffa0007fffdd7fd000000003fff01fffffffffe000fffffffff000) (((pairsA [] kv7).drop (1 * 1)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 0x37efdfbf7efdfbfd8bffa0007fffdd7fd000000003fff01fffffffffe000fffffffff000) (((pairsA [] kv7).drop (1 * 2)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_3 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 0x37efdfbf7efdfbfd8bffa0007fffdd7fd000000003fff01fffffffffe000fffffffff000) (((pairsA [] kv7).drop (1 * 3)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_4 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 0x37efdfbf7efdfbfd8bffa0007fffdd7fd000000003fff01fffffffffe000fffffffff000) (((pairsA [] kv7).drop (1 * 4)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_5 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 0x37efdfbf7efdfbfd8bffa0007fffdd7fd000000003fff01fffffffffe000fffffffff000) (((pairsA [] kv7).drop (1 * 5)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_6 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 0x37efdfbf7efdfbfd8bffa0007fffdd7fd000000003fff01fffffffffe000fffffffff000) (((pairsA [] kv7).drop (1 * 6)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_7 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 0x37efdfbf7efdfbfd8bffa0007fffdd7fd000000003fff01fffffffffe000fffffffff000) (((pairsA [] kv7).drop (1 * 7)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_8 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 0x37efdfbf7efdfbfd8bffa0007fffdd7fd000000003fff01fffffffffe000fffffffff000) (((pairsA [] kv7).drop (1 * 8)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_9 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 0x37efdfbf7efdfbfd8bffa0007fffdd7fd000000003fff01fffffffffe000fffffffff000) (((pairsA [] kv7).drop (1 * 9)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_10 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 0x37efdfbf7efdfbfd8bffa0007fffdd7fd000000003fff01fffffffffe000fffffffff000) (((pairsA [] kv7).drop (1 * 10)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_11 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 0x37efdfbf7efdfbfd8bffa0007fffdd7fd000000003fff01fffffffffe000fffffffff000) (((pairsA [] kv7).drop (1 * 11)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_12 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 0x37efdfbf7efdfbfd8bffa0007fffdd7fd000000003fff01fffffffffe000fffffffff000) (((pairsA [] kv7).drop (1 * 12)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_13 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 0x37efdfbf7efdfbfd8bffa0007fffdd7fd000000003fff01fffffffffe000fffffffff000) (((pairsA [] kv7).drop (1 * 13)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_14 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 0x37efdfbf7efdfbfd8bffa0007fffdd7fd000000003fff01fffffffffe000fffffffff000) (((pairsA [] kv7).drop (1 * 14)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_15 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 0x37efdfbf7efdfbfd8bffa0007fffdd7fd000000003fff01fffffffffe000fffffffff000) (((pairsA [] kv7).drop (1 * 15)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_16 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 0x37efdfbf7efdfbfd8bffa0007fffdd7fd000000003fff01fffffffffe000fffffffff000) (((pairsA [] kv7).drop (1 * 16)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_17 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 0x37efdfbf7efdfbfd8bffa0007fffdd7fd000000003fff01fffffffffe000fffffffff000) (((pairsA [] kv7).drop (1 * 17)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_18 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 0x37efdfbf7efdfbfd8bffa0007fffdd7fd000000003fff01fffffffffe000fffffffff000) (((pairsA [] kv7).drop (1 * 18)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_19 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 0x37efdfbf7efdfbfd8bffa0007fffdd7fd000000003fff01fffffffffe000fffffffff000) (((pairsA [] kv7).drop (1 * 19)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_20 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 0x37efdfbf7efdfbfd8bffa0007fffdd7fd000000003fff01fffffffffe000fffffffff000) (((pairsA [] kv7).drop (1 * 20)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_21 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 0x37efdfbf7efdfbfd8bffa0007fffdd7fd000000003fff01fffffffffe000fffffffff000) (((pairsA [] kv7).drop (1 * 21)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_22 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 0x37efdfbf7efdfbfd8bffa0007fffdd7fd000000003fff01fffffffffe000fffffffff000) (((pairsA [] kv7).drop (1 * 22)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_23 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 0x37efdfbf7efdfbfd8bffa0007fffdd7fd000000003fff01fffffffffe000fffffffff000) (((pairsA [] kv7).drop (1 * 23)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_24 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 0x37efdfbf7efdfbfd8bffa0007fffdd7fd000000003fff01fffffffffe000fffffffff000) (((pairsA [] kv7).drop (1 * 24)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_25 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 0x37efdfbf7efdfbfd8bffa0007fffdd7fd000000003fff01fffffffffe000fffffffff000) (((pairsA [] kv7).drop (1 * 25)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_26 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 0x37efdfbf7efdfbfd8bffa0007fffdd7fd000000003fff01fffffffffe000fffffffff000) (((pairsA [] kv7).drop (1 * 26)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_27 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 0x37efdfbf7efdfbfd8bffa0007fffdd7fd000000003fff01fffffffffe000fffffffff000) (((pairsA [] kv7).drop (1 * 27)).take 1) = false := by decide +kernel

theorem kid7 : search LO LO 9 kv7 127 123 64 0x37efdfbf7efdfbfd8bffa0007fffdd7fd000000003fff01fffffffffe000fffffffff000 = false := by
  have h1 : isT LO kv7 = false := by decide +kernel
  have h2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 0x37efdfbf7efdfbfd8bffa0007fffdd7fd000000003fff01fffffffffe000fffffffff000) (pairsA [] kv7) = false := by
    refine anyP_chunks _ 1 28 _ (by decide +kernel) fun i hi => ?_
    interval_cases i
    · exact kid7_0
    · exact kid7_1
    · exact kid7_2
    · exact kid7_3
    · exact kid7_4
    · exact kid7_5
    · exact kid7_6
    · exact kid7_7
    · exact kid7_8
    · exact kid7_9
    · exact kid7_10
    · exact kid7_11
    · exact kid7_12
    · exact kid7_13
    · exact kid7_14
    · exact kid7_15
    · exact kid7_16
    · exact kid7_17
    · exact kid7_18
    · exact kid7_19
    · exact kid7_20
    · exact kid7_21
    · exact kid7_22
    · exact kid7_23
    · exact kid7_24
    · exact kid7_25
    · exact kid7_26
    · exact kid7_27
  rw [search, h1, h2]; rfl

def kv8 : List Wr := [⟨0x60c183060c183058a000000526fdd00000000000007f0003f8ffc000000001fff000000, 0xc18306731833984e8000000a4c045000000, 2⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid8_0 : anyP (tryP LO (search LO LO 8) 8 (lenL kv8) 127 123 64 0x60c183060c183058a000000526fdd00000000000007f0003f8ffc000000001fff000000) (((pairsA [] kv8).drop (5 * 0)).take 5) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid8_1 : anyP (tryP LO (search LO LO 8) 8 (lenL kv8) 127 123 64 0x60c183060c183058a000000526fdd00000000000007f0003f8ffc000000001fff000000) (((pairsA [] kv8).drop (5 * 1)).take 5) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid8_2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv8) 127 123 64 0x60c183060c183058a000000526fdd00000000000007f0003f8ffc000000001fff000000) (((pairsA [] kv8).drop (5 * 2)).take 5) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid8_3 : anyP (tryP LO (search LO LO 8) 8 (lenL kv8) 127 123 64 0x60c183060c183058a000000526fdd00000000000007f0003f8ffc000000001fff000000) (((pairsA [] kv8).drop (5 * 3)).take 5) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid8_4 : anyP (tryP LO (search LO LO 8) 8 (lenL kv8) 127 123 64 0x60c183060c183058a000000526fdd00000000000007f0003f8ffc000000001fff000000) (((pairsA [] kv8).drop (5 * 4)).take 5) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid8_5 : anyP (tryP LO (search LO LO 8) 8 (lenL kv8) 127 123 64 0x60c183060c183058a000000526fdd00000000000007f0003f8ffc000000001fff000000) (((pairsA [] kv8).drop (5 * 5)).take 5) = false := by decide +kernel

theorem kid8 : search LO LO 9 kv8 127 123 64 0x60c183060c183058a000000526fdd00000000000007f0003f8ffc000000001fff000000 = false := by
  have h1 : isT LO kv8 = false := by decide +kernel
  have h2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv8) 127 123 64 0x60c183060c183058a000000526fdd00000000000007f0003f8ffc000000001fff000000) (pairsA [] kv8) = false := by
    refine anyP_chunks _ 5 6 _ (by decide +kernel) fun i hi => ?_
    interval_cases i
    · exact kid8_0
    · exact kid8_1
    · exact kid8_2
    · exact kid8_3
    · exact kid8_4
    · exact kid8_5
  rw [search, h1, h2]; rfl

def kv9 : List Wr := [⟨0x40810204081020480000000420c50000000000000000000000900000000ce18f0000000, 0x810204081020400000000004a0050000000, 18⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid9 : search LO LO 9 kv9 127 111 64 0x40810204081020480000000420c50000000000000000000000900000000ce18f0000000 = false := by decide +kernel

def kv10 : List Wr := [⟨0x78f1e3c78f1e3c58a850404f76ffd71870500fe0007ffffffffff1e183fffffffe30e0f, 0xfe03c7f0e1c3874ea141036112005000005, 0⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_0 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 0x78f1e3c78f1e3c58a850404f76ffd71870500fe0007ffffffffff1e183fffffffe30e0f) (((pairsA [] kv10).drop (1 * 0)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_1 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 0x78f1e3c78f1e3c58a850404f76ffd71870500fe0007ffffffffff1e183fffffffe30e0f) (((pairsA [] kv10).drop (1 * 1)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 0x78f1e3c78f1e3c58a850404f76ffd71870500fe0007ffffffffff1e183fffffffe30e0f) (((pairsA [] kv10).drop (1 * 2)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_3 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 0x78f1e3c78f1e3c58a850404f76ffd71870500fe0007ffffffffff1e183fffffffe30e0f) (((pairsA [] kv10).drop (1 * 3)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_4 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 0x78f1e3c78f1e3c58a850404f76ffd71870500fe0007ffffffffff1e183fffffffe30e0f) (((pairsA [] kv10).drop (1 * 4)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_5 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 0x78f1e3c78f1e3c58a850404f76ffd71870500fe0007ffffffffff1e183fffffffe30e0f) (((pairsA [] kv10).drop (1 * 5)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_6 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 0x78f1e3c78f1e3c58a850404f76ffd71870500fe0007ffffffffff1e183fffffffe30e0f) (((pairsA [] kv10).drop (1 * 6)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_7 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 0x78f1e3c78f1e3c58a850404f76ffd71870500fe0007ffffffffff1e183fffffffe30e0f) (((pairsA [] kv10).drop (1 * 7)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_8 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 0x78f1e3c78f1e3c58a850404f76ffd71870500fe0007ffffffffff1e183fffffffe30e0f) (((pairsA [] kv10).drop (1 * 8)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_9 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 0x78f1e3c78f1e3c58a850404f76ffd71870500fe0007ffffffffff1e183fffffffe30e0f) (((pairsA [] kv10).drop (1 * 9)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_10 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 0x78f1e3c78f1e3c58a850404f76ffd71870500fe0007ffffffffff1e183fffffffe30e0f) (((pairsA [] kv10).drop (1 * 10)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_11 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 0x78f1e3c78f1e3c58a850404f76ffd71870500fe0007ffffffffff1e183fffffffe30e0f) (((pairsA [] kv10).drop (1 * 11)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_12 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 0x78f1e3c78f1e3c58a850404f76ffd71870500fe0007ffffffffff1e183fffffffe30e0f) (((pairsA [] kv10).drop (1 * 12)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_13 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 0x78f1e3c78f1e3c58a850404f76ffd71870500fe0007ffffffffff1e183fffffffe30e0f) (((pairsA [] kv10).drop (1 * 13)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_14 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 0x78f1e3c78f1e3c58a850404f76ffd71870500fe0007ffffffffff1e183fffffffe30e0f) (((pairsA [] kv10).drop (1 * 14)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_15 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 0x78f1e3c78f1e3c58a850404f76ffd71870500fe0007ffffffffff1e183fffffffe30e0f) (((pairsA [] kv10).drop (1 * 15)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_16 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 0x78f1e3c78f1e3c58a850404f76ffd71870500fe0007ffffffffff1e183fffffffe30e0f) (((pairsA [] kv10).drop (1 * 16)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_17 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 0x78f1e3c78f1e3c58a850404f76ffd71870500fe0007ffffffffff1e183fffffffe30e0f) (((pairsA [] kv10).drop (1 * 17)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_18 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 0x78f1e3c78f1e3c58a850404f76ffd71870500fe0007ffffffffff1e183fffffffe30e0f) (((pairsA [] kv10).drop (1 * 18)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_19 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 0x78f1e3c78f1e3c58a850404f76ffd71870500fe0007ffffffffff1e183fffffffe30e0f) (((pairsA [] kv10).drop (1 * 19)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_20 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 0x78f1e3c78f1e3c58a850404f76ffd71870500fe0007ffffffffff1e183fffffffe30e0f) (((pairsA [] kv10).drop (1 * 20)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_21 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 0x78f1e3c78f1e3c58a850404f76ffd71870500fe0007ffffffffff1e183fffffffe30e0f) (((pairsA [] kv10).drop (1 * 21)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_22 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 0x78f1e3c78f1e3c58a850404f76ffd71870500fe0007ffffffffff1e183fffffffe30e0f) (((pairsA [] kv10).drop (1 * 22)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_23 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 0x78f1e3c78f1e3c58a850404f76ffd71870500fe0007ffffffffff1e183fffffffe30e0f) (((pairsA [] kv10).drop (1 * 23)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_24 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 0x78f1e3c78f1e3c58a850404f76ffd71870500fe0007ffffffffff1e183fffffffe30e0f) (((pairsA [] kv10).drop (1 * 24)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_25 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 0x78f1e3c78f1e3c58a850404f76ffd71870500fe0007ffffffffff1e183fffffffe30e0f) (((pairsA [] kv10).drop (1 * 25)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_26 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 0x78f1e3c78f1e3c58a850404f76ffd71870500fe0007ffffffffff1e183fffffffe30e0f) (((pairsA [] kv10).drop (1 * 26)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_27 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 0x78f1e3c78f1e3c58a850404f76ffd71870500fe0007ffffffffff1e183fffffffe30e0f) (((pairsA [] kv10).drop (1 * 27)).take 1) = false := by decide +kernel

theorem kid10 : search LO LO 9 kv10 127 111 64 0x78f1e3c78f1e3c58a850404f76ffd71870500fe0007ffffffffff1e183fffffffe30e0f = false := by
  have h1 : isT LO kv10 = false := by decide +kernel
  have h2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 0x78f1e3c78f1e3c58a850404f76ffd71870500fe0007ffffffffff1e183fffffffe30e0f) (pairsA [] kv10) = false := by
    refine anyP_chunks _ 1 28 _ (by decide +kernel) fun i hi => ?_
    interval_cases i
    · exact kid10_0
    · exact kid10_1
    · exact kid10_2
    · exact kid10_3
    · exact kid10_4
    · exact kid10_5
    · exact kid10_6
    · exact kid10_7
    · exact kid10_8
    · exact kid10_9
    · exact kid10_10
    · exact kid10_11
    · exact kid10_12
    · exact kid10_13
    · exact kid10_14
    · exact kid10_15
    · exact kid10_16
    · exact kid10_17
    · exact kid10_18
    · exact kid10_19
    · exact kid10_20
    · exact kid10_21
    · exact kid10_22
    · exact kid10_23
    · exact kid10_24
    · exact kid10_25
    · exact kid10_26
    · exact kid10_27
  rw [search, h1, h2]; rfl

def kv11 : List Wr := [⟨0x183060c183060c000850404a5002071870500fe00000fe00000031e183f000000e30e0f, 0x3f80c183f80c180021410364a0040000005, 16⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid11 : search LO LO 9 kv11 127 111 64 0x183060c183060c000850404a5002071870500fe00000fe00000031e183f000000e30e0f = false := by decide +kernel

def kv12 : List Wr := [⟨0x60c183060c183058a000000526fdd00000000000000001fffdf3c000000f6eb30000000, 0xc183060c19cf9d42800000052348a000000, 2⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid12_0 : anyP (tryP LO (search LO LO 8) 8 (lenL kv12) 127 95 64 0x60c183060c183058a000000526fdd00000000000000001fffdf3c000000f6eb30000000) (((pairsA [] kv12).drop (5 * 0)).take 5) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid12_1 : anyP (tryP LO (search LO LO 8) 8 (lenL kv12) 127 95 64 0x60c183060c183058a000000526fdd00000000000000001fffdf3c000000f6eb30000000) (((pairsA [] kv12).drop (5 * 1)).take 5) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid12_2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv12) 127 95 64 0x60c183060c183058a000000526fdd00000000000000001fffdf3c000000f6eb30000000) (((pairsA [] kv12).drop (5 * 2)).take 5) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid12_3 : anyP (tryP LO (search LO LO 8) 8 (lenL kv12) 127 95 64 0x60c183060c183058a000000526fdd00000000000000001fffdf3c000000f6eb30000000) (((pairsA [] kv12).drop (5 * 3)).take 5) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid12_4 : anyP (tryP LO (search LO LO 8) 8 (lenL kv12) 127 95 64 0x60c183060c183058a000000526fdd00000000000000001fffdf3c000000f6eb30000000) (((pairsA [] kv12).drop (5 * 4)).take 5) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid12_5 : anyP (tryP LO (search LO LO 8) 8 (lenL kv12) 127 95 64 0x60c183060c183058a000000526fdd00000000000000001fffdf3c000000f6eb30000000) (((pairsA [] kv12).drop (5 * 5)).take 5) = false := by decide +kernel

theorem kid12 : search LO LO 9 kv12 127 95 64 0x60c183060c183058a000000526fdd00000000000000001fffdf3c000000f6eb30000000 = false := by
  have h1 : isT LO kv12 = false := by decide +kernel
  have h2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv12) 127 95 64 0x60c183060c183058a000000526fdd00000000000000001fffdf3c000000f6eb30000000) (pairsA [] kv12) = false := by
    refine anyP_chunks _ 5 6 _ (by decide +kernel) fun i hi => ?_
    interval_cases i
    · exact kid12_0
    · exact kid12_1
    · exact kid12_2
    · exact kid12_3
    · exact kid12_4
    · exact kid12_5
  rw [search, h1, h2]; rfl

def kv13 : List Wr := [⟨0x2040810204081000800000000408c0000000000000000000000b0000000008b3c000000, 0x408102040810200a0000000000a24000000, 66⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_0 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 0x2040810204081000800000000408c0000000000000000000000b0000000008b3c000000) (((pairsA [] kv13).drop (1 * 0)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_1 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 0x2040810204081000800000000408c0000000000000000000000b0000000008b3c000000) (((pairsA [] kv13).drop (1 * 1)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 0x2040810204081000800000000408c0000000000000000000000b0000000008b3c000000) (((pairsA [] kv13).drop (1 * 2)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_3 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 0x2040810204081000800000000408c0000000000000000000000b0000000008b3c000000) (((pairsA [] kv13).drop (1 * 3)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_4 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 0x2040810204081000800000000408c0000000000000000000000b0000000008b3c000000) (((pairsA [] kv13).drop (1 * 4)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_5 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 0x2040810204081000800000000408c0000000000000000000000b0000000008b3c000000) (((pairsA [] kv13).drop (1 * 5)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_6 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 0x2040810204081000800000000408c0000000000000000000000b0000000008b3c000000) (((pairsA [] kv13).drop (1 * 6)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_7 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 0x2040810204081000800000000408c0000000000000000000000b0000000008b3c000000) (((pairsA [] kv13).drop (1 * 7)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_8 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 0x2040810204081000800000000408c0000000000000000000000b0000000008b3c000000) (((pairsA [] kv13).drop (1 * 8)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_9 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 0x2040810204081000800000000408c0000000000000000000000b0000000008b3c000000) (((pairsA [] kv13).drop (1 * 9)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_10 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 0x2040810204081000800000000408c0000000000000000000000b0000000008b3c000000) (((pairsA [] kv13).drop (1 * 10)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_11 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 0x2040810204081000800000000408c0000000000000000000000b0000000008b3c000000) (((pairsA [] kv13).drop (1 * 11)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_12 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 0x2040810204081000800000000408c0000000000000000000000b0000000008b3c000000) (((pairsA [] kv13).drop (1 * 12)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_13 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 0x2040810204081000800000000408c0000000000000000000000b0000000008b3c000000) (((pairsA [] kv13).drop (1 * 13)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_14 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 0x2040810204081000800000000408c0000000000000000000000b0000000008b3c000000) (((pairsA [] kv13).drop (1 * 14)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_15 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 0x2040810204081000800000000408c0000000000000000000000b0000000008b3c000000) (((pairsA [] kv13).drop (1 * 15)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_16 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 0x2040810204081000800000000408c0000000000000000000000b0000000008b3c000000) (((pairsA [] kv13).drop (1 * 16)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_17 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 0x2040810204081000800000000408c0000000000000000000000b0000000008b3c000000) (((pairsA [] kv13).drop (1 * 17)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_18 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 0x2040810204081000800000000408c0000000000000000000000b0000000008b3c000000) (((pairsA [] kv13).drop (1 * 18)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_19 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 0x2040810204081000800000000408c0000000000000000000000b0000000008b3c000000) (((pairsA [] kv13).drop (1 * 19)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_20 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 0x2040810204081000800000000408c0000000000000000000000b0000000008b3c000000) (((pairsA [] kv13).drop (1 * 20)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_21 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 0x2040810204081000800000000408c0000000000000000000000b0000000008b3c000000) (((pairsA [] kv13).drop (1 * 21)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_22 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 0x2040810204081000800000000408c0000000000000000000000b0000000008b3c000000) (((pairsA [] kv13).drop (1 * 22)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_23 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 0x2040810204081000800000000408c0000000000000000000000b0000000008b3c000000) (((pairsA [] kv13).drop (1 * 23)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_24 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 0x2040810204081000800000000408c0000000000000000000000b0000000008b3c000000) (((pairsA [] kv13).drop (1 * 24)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_25 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 0x2040810204081000800000000408c0000000000000000000000b0000000008b3c000000) (((pairsA [] kv13).drop (1 * 25)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_26 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 0x2040810204081000800000000408c0000000000000000000000b0000000008b3c000000) (((pairsA [] kv13).drop (1 * 26)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_27 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 0x2040810204081000800000000408c0000000000000000000000b0000000008b3c000000) (((pairsA [] kv13).drop (1 * 27)).take 1) = false := by decide +kernel

theorem kid13 : search LO LO 9 kv13 127 127 0 0x2040810204081000800000000408c0000000000000000000000b0000000008b3c000000 = false := by
  have h1 : isT LO kv13 = false := by decide +kernel
  have h2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 0x2040810204081000800000000408c0000000000000000000000b0000000008b3c000000) (pairsA [] kv13) = false := by
    refine anyP_chunks _ 1 28 _ (by decide +kernel) fun i hi => ?_
    interval_cases i
    · exact kid13_0
    · exact kid13_1
    · exact kid13_2
    · exact kid13_3
    · exact kid13_4
    · exact kid13_5
    · exact kid13_6
    · exact kid13_7
    · exact kid13_8
    · exact kid13_9
    · exact kid13_10
    · exact kid13_11
    · exact kid13_12
    · exact kid13_13
    · exact kid13_14
    · exact kid13_15
    · exact kid13_16
    · exact kid13_17
    · exact kid13_18
    · exact kid13_19
    · exact kid13_20
    · exact kid13_21
    · exact kid13_22
    · exact kid13_23
    · exact kid13_24
    · exact kid13_25
    · exact kid13_26
    · exact kid13_27
  rw [search, h1, h2]; rfl

def kv14 : List Wr := [⟨0xe1c3870e1c38705da005232526fdf00288afffe03fff01ffffffc21e4e4ffffff27f33f, 0x63c6731e3398f1f4482140805b204127a22a, 0⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_0 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 0xe1c3870e1c38705da005232526fdf00288afffe03fff01ffffffc21e4e4ffffff27f33f) (((pairsA [] kv14).drop (1 * 0)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_1 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 0xe1c3870e1c38705da005232526fdf00288afffe03fff01ffffffc21e4e4ffffff27f33f) (((pairsA [] kv14).drop (1 * 1)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 0xe1c3870e1c38705da005232526fdf00288afffe03fff01ffffffc21e4e4ffffff27f33f) (((pairsA [] kv14).drop (1 * 2)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_3 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 0xe1c3870e1c38705da005232526fdf00288afffe03fff01ffffffc21e4e4ffffff27f33f) (((pairsA [] kv14).drop (1 * 3)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_4 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 0xe1c3870e1c38705da005232526fdf00288afffe03fff01ffffffc21e4e4ffffff27f33f) (((pairsA [] kv14).drop (1 * 4)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_5 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 0xe1c3870e1c38705da005232526fdf00288afffe03fff01ffffffc21e4e4ffffff27f33f) (((pairsA [] kv14).drop (1 * 5)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_6 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 0xe1c3870e1c38705da005232526fdf00288afffe03fff01ffffffc21e4e4ffffff27f33f) (((pairsA [] kv14).drop (1 * 6)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_7 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 0xe1c3870e1c38705da005232526fdf00288afffe03fff01ffffffc21e4e4ffffff27f33f) (((pairsA [] kv14).drop (1 * 7)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_8 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 0xe1c3870e1c38705da005232526fdf00288afffe03fff01ffffffc21e4e4ffffff27f33f) (((pairsA [] kv14).drop (1 * 8)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_9 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 0xe1c3870e1c38705da005232526fdf00288afffe03fff01ffffffc21e4e4ffffff27f33f) (((pairsA [] kv14).drop (1 * 9)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_10 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 0xe1c3870e1c38705da005232526fdf00288afffe03fff01ffffffc21e4e4ffffff27f33f) (((pairsA [] kv14).drop (1 * 10)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_11 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 0xe1c3870e1c38705da005232526fdf00288afffe03fff01ffffffc21e4e4ffffff27f33f) (((pairsA [] kv14).drop (1 * 11)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_12 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 0xe1c3870e1c38705da005232526fdf00288afffe03fff01ffffffc21e4e4ffffff27f33f) (((pairsA [] kv14).drop (1 * 12)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_13 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 0xe1c3870e1c38705da005232526fdf00288afffe03fff01ffffffc21e4e4ffffff27f33f) (((pairsA [] kv14).drop (1 * 13)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_14 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 0xe1c3870e1c38705da005232526fdf00288afffe03fff01ffffffc21e4e4ffffff27f33f) (((pairsA [] kv14).drop (1 * 14)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_15 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 0xe1c3870e1c38705da005232526fdf00288afffe03fff01ffffffc21e4e4ffffff27f33f) (((pairsA [] kv14).drop (1 * 15)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_16 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 0xe1c3870e1c38705da005232526fdf00288afffe03fff01ffffffc21e4e4ffffff27f33f) (((pairsA [] kv14).drop (1 * 16)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_17 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 0xe1c3870e1c38705da005232526fdf00288afffe03fff01ffffffc21e4e4ffffff27f33f) (((pairsA [] kv14).drop (1 * 17)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_18 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 0xe1c3870e1c38705da005232526fdf00288afffe03fff01ffffffc21e4e4ffffff27f33f) (((pairsA [] kv14).drop (1 * 18)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_19 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 0xe1c3870e1c38705da005232526fdf00288afffe03fff01ffffffc21e4e4ffffff27f33f) (((pairsA [] kv14).drop (1 * 19)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_20 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 0xe1c3870e1c38705da005232526fdf00288afffe03fff01ffffffc21e4e4ffffff27f33f) (((pairsA [] kv14).drop (1 * 20)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_21 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 0xe1c3870e1c38705da005232526fdf00288afffe03fff01ffffffc21e4e4ffffff27f33f) (((pairsA [] kv14).drop (1 * 21)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_22 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 0xe1c3870e1c38705da005232526fdf00288afffe03fff01ffffffc21e4e4ffffff27f33f) (((pairsA [] kv14).drop (1 * 22)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_23 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 0xe1c3870e1c38705da005232526fdf00288afffe03fff01ffffffc21e4e4ffffff27f33f) (((pairsA [] kv14).drop (1 * 23)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_24 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 0xe1c3870e1c38705da005232526fdf00288afffe03fff01ffffffc21e4e4ffffff27f33f) (((pairsA [] kv14).drop (1 * 24)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_25 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 0xe1c3870e1c38705da005232526fdf00288afffe03fff01ffffffc21e4e4ffffff27f33f) (((pairsA [] kv14).drop (1 * 25)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_26 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 0xe1c3870e1c38705da005232526fdf00288afffe03fff01ffffffc21e4e4ffffff27f33f) (((pairsA [] kv14).drop (1 * 26)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_27 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 0xe1c3870e1c38705da005232526fdf00288afffe03fff01ffffffc21e4e4ffffff27f33f) (((pairsA [] kv14).drop (1 * 27)).take 1) = false := by decide +kernel

theorem kid14 : search LO LO 9 kv14 127 127 0 0xe1c3870e1c38705da005232526fdf00288afffe03fff01ffffffc21e4e4ffffff27f33f = false := by
  have h1 : isT LO kv14 = false := by decide +kernel
  have h2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 0xe1c3870e1c38705da005232526fdf00288afffe03fff01ffffffc21e4e4ffffff27f33f) (pairsA [] kv14) = false := by
    refine anyP_chunks _ 1 28 _ (by decide +kernel) fun i hi => ?_
    interval_cases i
    · exact kid14_0
    · exact kid14_1
    · exact kid14_2
    · exact kid14_3
    · exact kid14_4
    · exact kid14_5
    · exact kid14_6
    · exact kid14_7
    · exact kid14_8
    · exact kid14_9
    · exact kid14_10
    · exact kid14_11
    · exact kid14_12
    · exact kid14_13
    · exact kid14_14
    · exact kid14_15
    · exact kid14_16
    · exact kid14_17
    · exact kid14_18
    · exact kid14_19
    · exact kid14_20
    · exact kid14_21
    · exact kid14_22
    · exact kid14_23
    · exact kid14_24
    · exact kid14_25
    · exact kid14_26
    · exact kid14_27
  rw [search, h1, h2]; rfl

def kv15 : List Wr := [⟨0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000, 0x8102047711dfbf4480000005b2a61000000, 2⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_0 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000) (((pairsA [] kv15).drop (1 * 0)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_1 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000) (((pairsA [] kv15).drop (1 * 1)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000) (((pairsA [] kv15).drop (1 * 2)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_3 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000) (((pairsA [] kv15).drop (1 * 3)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_4 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000) (((pairsA [] kv15).drop (1 * 4)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_5 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000) (((pairsA [] kv15).drop (1 * 5)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_6 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000) (((pairsA [] kv15).drop (1 * 6)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_7 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000) (((pairsA [] kv15).drop (1 * 7)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_8 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000) (((pairsA [] kv15).drop (1 * 8)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_9 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000) (((pairsA [] kv15).drop (1 * 9)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_10 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000) (((pairsA [] kv15).drop (1 * 10)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_11 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000) (((pairsA [] kv15).drop (1 * 11)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_12 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000) (((pairsA [] kv15).drop (1 * 12)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_13 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000) (((pairsA [] kv15).drop (1 * 13)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_14 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000) (((pairsA [] kv15).drop (1 * 14)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_15 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000) (((pairsA [] kv15).drop (1 * 15)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_16 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000) (((pairsA [] kv15).drop (1 * 16)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_17 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000) (((pairsA [] kv15).drop (1 * 17)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_18 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000) (((pairsA [] kv15).drop (1 * 18)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_19 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000) (((pairsA [] kv15).drop (1 * 19)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_20 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000) (((pairsA [] kv15).drop (1 * 20)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_21 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000) (((pairsA [] kv15).drop (1 * 21)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_22 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000) (((pairsA [] kv15).drop (1 * 22)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_23 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000) (((pairsA [] kv15).drop (1 * 23)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_24 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000) (((pairsA [] kv15).drop (1 * 24)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_25 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000) (((pairsA [] kv15).drop (1 * 25)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_26 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000) (((pairsA [] kv15).drop (1 * 26)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_27 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000) (((pairsA [] kv15).drop (1 * 27)).take 1) = false := by decide +kernel

theorem kid15 : search LO LO 9 kv15 127 127 0 0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000 = false := by
  have h1 : isT LO kv15 = false := by decide +kernel
  have h2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000) (pairsA [] kv15) = false := by
    refine anyP_chunks _ 1 28 _ (by decide +kernel) fun i hi => ?_
    interval_cases i
    · exact kid15_0
    · exact kid15_1
    · exact kid15_2
    · exact kid15_3
    · exact kid15_4
    · exact kid15_5
    · exact kid15_6
    · exact kid15_7
    · exact kid15_8
    · exact kid15_9
    · exact kid15_10
    · exact kid15_11
    · exact kid15_12
    · exact kid15_13
    · exact kid15_14
    · exact kid15_15
    · exact kid15_16
    · exact kid15_17
    · exact kid15_18
    · exact kid15_19
    · exact kid15_20
    · exact kid15_21
    · exact kid15_22
    · exact kid15_23
    · exact kid15_24
    · exact kid15_25
    · exact kid15_26
    · exact kid15_27
  rw [search, h1, h2]; rfl

def kv16 : List Wr := [⟨0x183060c183060c0008500002500007180000000000000000000031e0000ce0000e30000, 0x3060c183060c18002140000840000000000, 20⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid16 : search LO LO 9 kv16 127 107 66 0x183060c183060c0008500002500007180000000000000000000031e0000ce0000e30000 = false := by decide +kernel

def kv17 : List Wr := [⟨0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f, 0x6b29aca6b28535800000b03620c010005005, 0⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_0 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f) (((pairsA [] kv17).drop (1 * 0)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_1 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f) (((pairsA [] kv17).drop (1 * 1)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f) (((pairsA [] kv17).drop (1 * 2)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_3 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f) (((pairsA [] kv17).drop (1 * 3)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_4 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f) (((pairsA [] kv17).drop (1 * 4)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_5 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f) (((pairsA [] kv17).drop (1 * 5)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_6 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f) (((pairsA [] kv17).drop (1 * 6)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_7 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f) (((pairsA [] kv17).drop (1 * 7)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_8 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f) (((pairsA [] kv17).drop (1 * 8)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_9 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f) (((pairsA [] kv17).drop (1 * 9)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_10 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f) (((pairsA [] kv17).drop (1 * 10)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_11 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f) (((pairsA [] kv17).drop (1 * 11)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_12 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f) (((pairsA [] kv17).drop (1 * 12)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_13 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f) (((pairsA [] kv17).drop (1 * 13)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_14 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f) (((pairsA [] kv17).drop (1 * 14)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_15 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f) (((pairsA [] kv17).drop (1 * 15)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_16 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f) (((pairsA [] kv17).drop (1 * 16)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_17 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f) (((pairsA [] kv17).drop (1 * 17)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_18 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f) (((pairsA [] kv17).drop (1 * 18)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_19 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f) (((pairsA [] kv17).drop (1 * 19)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_20 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f) (((pairsA [] kv17).drop (1 * 20)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_21 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f) (((pairsA [] kv17).drop (1 * 21)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_22 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f) (((pairsA [] kv17).drop (1 * 22)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_23 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f) (((pairsA [] kv17).drop (1 * 23)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_24 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f) (((pairsA [] kv17).drop (1 * 24)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_25 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f) (((pairsA [] kv17).drop (1 * 25)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_26 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f) (((pairsA [] kv17).drop (1 * 26)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_27 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f) (((pairsA [] kv17).drop (1 * 27)).take 1) = false := by decide +kernel

theorem kid17 : search LO LO 9 kv17 127 107 66 0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f = false := by
  have h1 : isT LO kv17 = false := by decide +kernel
  have h2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f) (pairsA [] kv17) = false := by
    refine anyP_chunks _ 1 28 _ (by decide +kernel) fun i hi => ?_
    interval_cases i
    · exact kid17_0
    · exact kid17_1
    · exact kid17_2
    · exact kid17_3
    · exact kid17_4
    · exact kid17_5
    · exact kid17_6
    · exact kid17_7
    · exact kid17_8
    · exact kid17_9
    · exact kid17_10
    · exact kid17_11
    · exact kid17_12
    · exact kid17_13
    · exact kid17_14
    · exact kid17_15
    · exact kid17_16
    · exact kid17_17
    · exact kid17_18
    · exact kid17_19
    · exact kid17_20
    · exact kid17_21
    · exact kid17_22
    · exact kid17_23
    · exact kid17_24
    · exact kid17_25
    · exact kid17_26
    · exact kid17_27
  rw [search, h1, h2]; rfl

def kv18 : List Wr := [⟨0x40810204081020480000404c20c7000070500fe00000fe000090000183f0018f0000e0f, 0x8ee20408ee2040000001036840010000005, 16⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid18 : search LO LO 9 kv18 127 107 66 0x40810204081020480000404c20c7000070500fe00000fe000090000183f0018f0000e0f = false := by decide +kernel

def kv19 : List Wr := [⟨0x31e3c78f1e3c78f801ffa0002d90007fd00000000000001fc07003de0000ff6000d80000, 0x63c78f1e3c67318000214000a4400027a000, 4⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid19 : search LO LO 9 kv19 127 123 2 0x31e3c78f1e3c78f801ffa0002d90007fd00000000000001fc07003de0000ff6000d80000 = false := by decide +kernel

def kv20 : List Wr := [⟨0x50a142850a1428400800400600c00500500000000000000000803001800c01800e00e00, 0xa142850a142850002001000000000400400, 24⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid20 : search LO LO 9 kv20 127 103 66 0x50a142850a1428400800400600c00500500000000000000000803001800c01800e00e00 = false := by decide +kernel

def kv21 : List Wr := [⟨0x25cb972e5cb972e781d50d44ff0f707b87557ffffc000fe0004f03fe1ffffe1ff0ff0fff, 0x3468d25cb692e58000540576000110080155, 0⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_0 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 0x25cb972e5cb972e781d50d44ff0f707b87557ffffc000fe0004f03fe1ffffe1ff0ff0fff) (((pairsA [] kv21).drop (1 * 0)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_1 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 0x25cb972e5cb972e781d50d44ff0f707b87557ffffc000fe0004f03fe1ffffe1ff0ff0fff) (((pairsA [] kv21).drop (1 * 1)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 0x25cb972e5cb972e781d50d44ff0f707b87557ffffc000fe0004f03fe1ffffe1ff0ff0fff) (((pairsA [] kv21).drop (1 * 2)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_3 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 0x25cb972e5cb972e781d50d44ff0f707b87557ffffc000fe0004f03fe1ffffe1ff0ff0fff) (((pairsA [] kv21).drop (1 * 3)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_4 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 0x25cb972e5cb972e781d50d44ff0f707b87557ffffc000fe0004f03fe1ffffe1ff0ff0fff) (((pairsA [] kv21).drop (1 * 4)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_5 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 0x25cb972e5cb972e781d50d44ff0f707b87557ffffc000fe0004f03fe1ffffe1ff0ff0fff) (((pairsA [] kv21).drop (1 * 5)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_6 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 0x25cb972e5cb972e781d50d44ff0f707b87557ffffc000fe0004f03fe1ffffe1ff0ff0fff) (((pairsA [] kv21).drop (1 * 6)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_7 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 0x25cb972e5cb972e781d50d44ff0f707b87557ffffc000fe0004f03fe1ffffe1ff0ff0fff) (((pairsA [] kv21).drop (1 * 7)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_8 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 0x25cb972e5cb972e781d50d44ff0f707b87557ffffc000fe0004f03fe1ffffe1ff0ff0fff) (((pairsA [] kv21).drop (1 * 8)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_9 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 0x25cb972e5cb972e781d50d44ff0f707b87557ffffc000fe0004f03fe1ffffe1ff0ff0fff) (((pairsA [] kv21).drop (1 * 9)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_10 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 0x25cb972e5cb972e781d50d44ff0f707b87557ffffc000fe0004f03fe1ffffe1ff0ff0fff) (((pairsA [] kv21).drop (1 * 10)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_11 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 0x25cb972e5cb972e781d50d44ff0f707b87557ffffc000fe0004f03fe1ffffe1ff0ff0fff) (((pairsA [] kv21).drop (1 * 11)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_12 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 0x25cb972e5cb972e781d50d44ff0f707b87557ffffc000fe0004f03fe1ffffe1ff0ff0fff) (((pairsA [] kv21).drop (1 * 12)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_13 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 0x25cb972e5cb972e781d50d44ff0f707b87557ffffc000fe0004f03fe1ffffe1ff0ff0fff) (((pairsA [] kv21).drop (1 * 13)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_14 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 0x25cb972e5cb972e781d50d44ff0f707b87557ffffc000fe0004f03fe1ffffe1ff0ff0fff) (((pairsA [] kv21).drop (1 * 14)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_15 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 0x25cb972e5cb972e781d50d44ff0f707b87557ffffc000fe0004f03fe1ffffe1ff0ff0fff) (((pairsA [] kv21).drop (1 * 15)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_16 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 0x25cb972e5cb972e781d50d44ff0f707b87557ffffc000fe0004f03fe1ffffe1ff0ff0fff) (((pairsA [] kv21).drop (1 * 16)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_17 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 0x25cb972e5cb972e781d50d44ff0f707b87557ffffc000fe0004f03fe1ffffe1ff0ff0fff) (((pairsA [] kv21).drop (1 * 17)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_18 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 0x25cb972e5cb972e781d50d44ff0f707b87557ffffc000fe0004f03fe1ffffe1ff0ff0fff) (((pairsA [] kv21).drop (1 * 18)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_19 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 0x25cb972e5cb972e781d50d44ff0f707b87557ffffc000fe0004f03fe1ffffe1ff0ff0fff) (((pairsA [] kv21).drop (1 * 19)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_20 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 0x25cb972e5cb972e781d50d44ff0f707b87557ffffc000fe0004f03fe1ffffe1ff0ff0fff) (((pairsA [] kv21).drop (1 * 20)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_21 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 0x25cb972e5cb972e781d50d44ff0f707b87557ffffc000fe0004f03fe1ffffe1ff0ff0fff) (((pairsA [] kv21).drop (1 * 21)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_22 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 0x25cb972e5cb972e781d50d44ff0f707b87557ffffc000fe0004f03fe1ffffe1ff0ff0fff) (((pairsA [] kv21).drop (1 * 22)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_23 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 0x25cb972e5cb972e781d50d44ff0f707b87557ffffc000fe0004f03fe1ffffe1ff0ff0fff) (((pairsA [] kv21).drop (1 * 23)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_24 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 0x25cb972e5cb972e781d50d44ff0f707b87557ffffc000fe0004f03fe1ffffe1ff0ff0fff) (((pairsA [] kv21).drop (1 * 24)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_25 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 0x25cb972e5cb972e781d50d44ff0f707b87557ffffc000fe0004f03fe1ffffe1ff0ff0fff) (((pairsA [] kv21).drop (1 * 25)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_26 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 0x25cb972e5cb972e781d50d44ff0f707b87557ffffc000fe0004f03fe1ffffe1ff0ff0fff) (((pairsA [] kv21).drop (1 * 26)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_27 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 0x25cb972e5cb972e781d50d44ff0f707b87557ffffc000fe0004f03fe1ffffe1ff0ff0fff) (((pairsA [] kv21).drop (1 * 27)).take 1) = false := by decide +kernel

theorem kid21 : search LO LO 9 kv21 127 103 66 0x25cb972e5cb972e781d50d44ff0f707b87557ffffc000fe0004f03fe1ffffe1ff0ff0fff = false := by
  have h1 : isT LO kv21 = false := by decide +kernel
  have h2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 0x25cb972e5cb972e781d50d44ff0f707b87557ffffc000fe0004f03fe1ffffe1ff0ff0fff) (pairsA [] kv21) = false := by
    refine anyP_chunks _ 1 28 _ (by decide +kernel) fun i hi => ?_
    interval_cases i
    · exact kid21_0
    · exact kid21_1
    · exact kid21_2
    · exact kid21_3
    · exact kid21_4
    · exact kid21_5
    · exact kid21_6
    · exact kid21_7
    · exact kid21_8
    · exact kid21_9
    · exact kid21_10
    · exact kid21_11
    · exact kid21_12
    · exact kid21_13
    · exact kid21_14
    · exact kid21_15
    · exact kid21_16
    · exact kid21_17
    · exact kid21_18
    · exact kid21_19
    · exact kid21_20
    · exact kid21_21
    · exact kid21_22
    · exact kid21_23
    · exact kid21_24
    · exact kid21_25
    · exact kid21_26
    · exact kid21_27
  rw [search, h1, h2]; rfl

def kv22 : List Wr := [⟨0x3dfbf7efdfbf7ef761fccfdc7c8f22ff67f67f01fc07f000006ec3f99ff8f91fcffecffc, 0x4f613d84f7efd800000004000018a000010, 0⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_0 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 0x3dfbf7efdfbf7ef761fccfdc7c8f22ff67f67f01fc07f000006ec3f99ff8f91fcffecffc) (((pairsA [] kv22).drop (1 * 0)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_1 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 0x3dfbf7efdfbf7ef761fccfdc7c8f22ff67f67f01fc07f000006ec3f99ff8f91fcffecffc) (((pairsA [] kv22).drop (1 * 1)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 0x3dfbf7efdfbf7ef761fccfdc7c8f22ff67f67f01fc07f000006ec3f99ff8f91fcffecffc) (((pairsA [] kv22).drop (1 * 2)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_3 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 0x3dfbf7efdfbf7ef761fccfdc7c8f22ff67f67f01fc07f000006ec3f99ff8f91fcffecffc) (((pairsA [] kv22).drop (1 * 3)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_4 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 0x3dfbf7efdfbf7ef761fccfdc7c8f22ff67f67f01fc07f000006ec3f99ff8f91fcffecffc) (((pairsA [] kv22).drop (1 * 4)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_5 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 0x3dfbf7efdfbf7ef761fccfdc7c8f22ff67f67f01fc07f000006ec3f99ff8f91fcffecffc) (((pairsA [] kv22).drop (1 * 5)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_6 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 0x3dfbf7efdfbf7ef761fccfdc7c8f22ff67f67f01fc07f000006ec3f99ff8f91fcffecffc) (((pairsA [] kv22).drop (1 * 6)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_7 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 0x3dfbf7efdfbf7ef761fccfdc7c8f22ff67f67f01fc07f000006ec3f99ff8f91fcffecffc) (((pairsA [] kv22).drop (1 * 7)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_8 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 0x3dfbf7efdfbf7ef761fccfdc7c8f22ff67f67f01fc07f000006ec3f99ff8f91fcffecffc) (((pairsA [] kv22).drop (1 * 8)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_9 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 0x3dfbf7efdfbf7ef761fccfdc7c8f22ff67f67f01fc07f000006ec3f99ff8f91fcffecffc) (((pairsA [] kv22).drop (1 * 9)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_10 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 0x3dfbf7efdfbf7ef761fccfdc7c8f22ff67f67f01fc07f000006ec3f99ff8f91fcffecffc) (((pairsA [] kv22).drop (1 * 10)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_11 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 0x3dfbf7efdfbf7ef761fccfdc7c8f22ff67f67f01fc07f000006ec3f99ff8f91fcffecffc) (((pairsA [] kv22).drop (1 * 11)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_12 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 0x3dfbf7efdfbf7ef761fccfdc7c8f22ff67f67f01fc07f000006ec3f99ff8f91fcffecffc) (((pairsA [] kv22).drop (1 * 12)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_13 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 0x3dfbf7efdfbf7ef761fccfdc7c8f22ff67f67f01fc07f000006ec3f99ff8f91fcffecffc) (((pairsA [] kv22).drop (1 * 13)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_14 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 0x3dfbf7efdfbf7ef761fccfdc7c8f22ff67f67f01fc07f000006ec3f99ff8f91fcffecffc) (((pairsA [] kv22).drop (1 * 14)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_15 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 0x3dfbf7efdfbf7ef761fccfdc7c8f22ff67f67f01fc07f000006ec3f99ff8f91fcffecffc) (((pairsA [] kv22).drop (1 * 15)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_16 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 0x3dfbf7efdfbf7ef761fccfdc7c8f22ff67f67f01fc07f000006ec3f99ff8f91fcffecffc) (((pairsA [] kv22).drop (1 * 16)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_17 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 0x3dfbf7efdfbf7ef761fccfdc7c8f22ff67f67f01fc07f000006ec3f99ff8f91fcffecffc) (((pairsA [] kv22).drop (1 * 17)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_18 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 0x3dfbf7efdfbf7ef761fccfdc7c8f22ff67f67f01fc07f000006ec3f99ff8f91fcffecffc) (((pairsA [] kv22).drop (1 * 18)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_19 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 0x3dfbf7efdfbf7ef761fccfdc7c8f22ff67f67f01fc07f000006ec3f99ff8f91fcffecffc) (((pairsA [] kv22).drop (1 * 19)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_20 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 0x3dfbf7efdfbf7ef761fccfdc7c8f22ff67f67f01fc07f000006ec3f99ff8f91fcffecffc) (((pairsA [] kv22).drop (1 * 20)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_21 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 0x3dfbf7efdfbf7ef761fccfdc7c8f22ff67f67f01fc07f000006ec3f99ff8f91fcffecffc) (((pairsA [] kv22).drop (1 * 21)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_22 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 0x3dfbf7efdfbf7ef761fccfdc7c8f22ff67f67f01fc07f000006ec3f99ff8f91fcffecffc) (((pairsA [] kv22).drop (1 * 22)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_23 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 0x3dfbf7efdfbf7ef761fccfdc7c8f22ff67f67f01fc07f000006ec3f99ff8f91fcffecffc) (((pairsA [] kv22).drop (1 * 23)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_24 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 0x3dfbf7efdfbf7ef761fccfdc7c8f22ff67f67f01fc07f000006ec3f99ff8f91fcffecffc) (((pairsA [] kv22).drop (1 * 24)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_25 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 0x3dfbf7efdfbf7ef761fccfdc7c8f22ff67f67f01fc07f000006ec3f99ff8f91fcffecffc) (((pairsA [] kv22).drop (1 * 25)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_26 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 0x3dfbf7efdfbf7ef761fccfdc7c8f22ff67f67f01fc07f000006ec3f99ff8f91fcffecffc) (((pairsA [] kv22).drop (1 * 26)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_27 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 0x3dfbf7efdfbf7ef761fccfdc7c8f22ff67f67f01fc07f000006ec3f99ff8f91fcffecffc) (((pairsA [] kv22).drop (1 * 27)).take 1) = false := by decide +kernel

theorem kid22 : search LO LO 9 kv22 127 87 66 0x3dfbf7efdfbf7ef761fccfdc7c8f22ff67f67f01fc07f000006ec3f99ff8f91fcffecffc = false := by
  have h1 : isT LO kv22 = false := by decide +kernel
  have h2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 0x3dfbf7efdfbf7ef761fccfdc7c8f22ff67f67f01fc07f000006ec3f99ff8f91fcffecffc) (pairsA [] kv22) = false := by
    refine anyP_chunks _ 1 28 _ (by decide +kernel) fun i hi => ?_
    interval_cases i
    · exact kid22_0
    · exact kid22_1
    · exact kid22_2
    · exact kid22_3
    · exact kid22_4
    · exact kid22_5
    · exact kid22_6
    · exact kid22_7
    · exact kid22_8
    · exact kid22_9
    · exact kid22_10
    · exact kid22_11
    · exact kid22_12
    · exact kid22_13
    · exact kid22_14
    · exact kid22_15
    · exact kid22_16
    · exact kid22_17
    · exact kid22_18
    · exact kid22_19
    · exact kid22_20
    · exact kid22_21
    · exact kid22_22
    · exact kid22_23
    · exact kid22_24
    · exact kid22_25
    · exact kid22_26
    · exact kid22_27
  rw [search, h1, h2]; rfl

def kv23 : List Wr := [⟨0x81020408102040000400040400202102040000000000000000001800380810c0c20c0c, 0x10204081020408000100030001080800804, 48⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid23 : search LO LO 9 kv23 127 79 66 0x81020408102040000400040400202102040000000000000000001800380810c0c20c0c = false := by decide +kernel

def kv24 : List Wr := [⟨0x1dbb76eddbb76ed4e0adc69ce78c72f5e7a700fffc07ffe00029c3df9f3fcf1cfffbcfcf, 0x3b8911dc488edd800284120600041a100081, 0⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_0 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 0x1dbb76eddbb76ed4e0adc69ce78c72f5e7a700fffc07ffe00029c3df9f3fcf1cfffbcfcf) (((pairsA [] kv24).drop (1 * 0)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_1 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 0x1dbb76eddbb76ed4e0adc69ce78c72f5e7a700fffc07ffe00029c3df9f3fcf1cfffbcfcf) (((pairsA [] kv24).drop (1 * 1)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 0x1dbb76eddbb76ed4e0adc69ce78c72f5e7a700fffc07ffe00029c3df9f3fcf1cfffbcfcf) (((pairsA [] kv24).drop (1 * 2)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_3 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 0x1dbb76eddbb76ed4e0adc69ce78c72f5e7a700fffc07ffe00029c3df9f3fcf1cfffbcfcf) (((pairsA [] kv24).drop (1 * 3)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_4 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 0x1dbb76eddbb76ed4e0adc69ce78c72f5e7a700fffc07ffe00029c3df9f3fcf1cfffbcfcf) (((pairsA [] kv24).drop (1 * 4)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_5 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 0x1dbb76eddbb76ed4e0adc69ce78c72f5e7a700fffc07ffe00029c3df9f3fcf1cfffbcfcf) (((pairsA [] kv24).drop (1 * 5)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_6 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 0x1dbb76eddbb76ed4e0adc69ce78c72f5e7a700fffc07ffe00029c3df9f3fcf1cfffbcfcf) (((pairsA [] kv24).drop (1 * 6)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_7 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 0x1dbb76eddbb76ed4e0adc69ce78c72f5e7a700fffc07ffe00029c3df9f3fcf1cfffbcfcf) (((pairsA [] kv24).drop (1 * 7)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_8 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 0x1dbb76eddbb76ed4e0adc69ce78c72f5e7a700fffc07ffe00029c3df9f3fcf1cfffbcfcf) (((pairsA [] kv24).drop (1 * 8)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_9 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 0x1dbb76eddbb76ed4e0adc69ce78c72f5e7a700fffc07ffe00029c3df9f3fcf1cfffbcfcf) (((pairsA [] kv24).drop (1 * 9)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_10 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 0x1dbb76eddbb76ed4e0adc69ce78c72f5e7a700fffc07ffe00029c3df9f3fcf1cfffbcfcf) (((pairsA [] kv24).drop (1 * 10)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_11 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 0x1dbb76eddbb76ed4e0adc69ce78c72f5e7a700fffc07ffe00029c3df9f3fcf1cfffbcfcf) (((pairsA [] kv24).drop (1 * 11)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_12 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 0x1dbb76eddbb76ed4e0adc69ce78c72f5e7a700fffc07ffe00029c3df9f3fcf1cfffbcfcf) (((pairsA [] kv24).drop (1 * 12)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_13 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 0x1dbb76eddbb76ed4e0adc69ce78c72f5e7a700fffc07ffe00029c3df9f3fcf1cfffbcfcf) (((pairsA [] kv24).drop (1 * 13)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_14 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 0x1dbb76eddbb76ed4e0adc69ce78c72f5e7a700fffc07ffe00029c3df9f3fcf1cfffbcfcf) (((pairsA [] kv24).drop (1 * 14)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_15 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 0x1dbb76eddbb76ed4e0adc69ce78c72f5e7a700fffc07ffe00029c3df9f3fcf1cfffbcfcf) (((pairsA [] kv24).drop (1 * 15)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_16 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 0x1dbb76eddbb76ed4e0adc69ce78c72f5e7a700fffc07ffe00029c3df9f3fcf1cfffbcfcf) (((pairsA [] kv24).drop (1 * 16)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_17 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 0x1dbb76eddbb76ed4e0adc69ce78c72f5e7a700fffc07ffe00029c3df9f3fcf1cfffbcfcf) (((pairsA [] kv24).drop (1 * 17)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_18 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 0x1dbb76eddbb76ed4e0adc69ce78c72f5e7a700fffc07ffe00029c3df9f3fcf1cfffbcfcf) (((pairsA [] kv24).drop (1 * 18)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_19 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 0x1dbb76eddbb76ed4e0adc69ce78c72f5e7a700fffc07ffe00029c3df9f3fcf1cfffbcfcf) (((pairsA [] kv24).drop (1 * 19)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_20 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 0x1dbb76eddbb76ed4e0adc69ce78c72f5e7a700fffc07ffe00029c3df9f3fcf1cfffbcfcf) (((pairsA [] kv24).drop (1 * 20)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_21 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 0x1dbb76eddbb76ed4e0adc69ce78c72f5e7a700fffc07ffe00029c3df9f3fcf1cfffbcfcf) (((pairsA [] kv24).drop (1 * 21)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_22 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 0x1dbb76eddbb76ed4e0adc69ce78c72f5e7a700fffc07ffe00029c3df9f3fcf1cfffbcfcf) (((pairsA [] kv24).drop (1 * 22)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_23 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 0x1dbb76eddbb76ed4e0adc69ce78c72f5e7a700fffc07ffe00029c3df9f3fcf1cfffbcfcf) (((pairsA [] kv24).drop (1 * 23)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_24 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 0x1dbb76eddbb76ed4e0adc69ce78c72f5e7a700fffc07ffe00029c3df9f3fcf1cfffbcfcf) (((pairsA [] kv24).drop (1 * 24)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_25 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 0x1dbb76eddbb76ed4e0adc69ce78c72f5e7a700fffc07ffe00029c3df9f3fcf1cfffbcfcf) (((pairsA [] kv24).drop (1 * 25)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_26 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 0x1dbb76eddbb76ed4e0adc69ce78c72f5e7a700fffc07ffe00029c3df9f3fcf1cfffbcfcf) (((pairsA [] kv24).drop (1 * 26)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_27 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 0x1dbb76eddbb76ed4e0adc69ce78c72f5e7a700fffc07ffe00029c3df9f3fcf1cfffbcfcf) (((pairsA [] kv24).drop (1 * 27)).take 1) = false := by decide +kernel

theorem kid24 : search LO LO 9 kv24 127 79 66 0x1dbb76eddbb76ed4e0adc69ce78c72f5e7a700fffc07ffe00029c3df9f3fcf1cfffbcfcf = false := by
  have h1 : isT LO kv24 = false := by decide +kernel
  have h2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 0x1dbb76eddbb76ed4e0adc69ce78c72f5e7a700fffc07ffe00029c3df9f3fcf1cfffbcfcf) (pairsA [] kv24) = false := by
    refine anyP_chunks _ 1 28 _ (by decide +kernel) fun i hi => ?_
    interval_cases i
    · exact kid24_0
    · exact kid24_1
    · exact kid24_2
    · exact kid24_3
    · exact kid24_4
    · exact kid24_5
    · exact kid24_6
    · exact kid24_7
    · exact kid24_8
    · exact kid24_9
    · exact kid24_10
    · exact kid24_11
    · exact kid24_12
    · exact kid24_13
    · exact kid24_14
    · exact kid24_15
    · exact kid24_16
    · exact kid24_17
    · exact kid24_18
    · exact kid24_19
    · exact kid24_20
    · exact kid24_21
    · exact kid24_22
    · exact kid24_23
    · exact kid24_24
    · exact kid24_25
    · exact kid24_26
    · exact kid24_27
  rw [search, h1, h2]; rfl

def kv25 : List Wr := [⟨0x50a142850a1428480810400e30c5050850100fe00000fe0000903061807c60830210203, 0xaea2850aea2850002041006001090800801, 16⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid25 : search LO LO 9 kv25 127 79 66 0x50a142850a1428480810400e30c5050850100fe00000fe0000903061807c60830210203 = false := by decide +kernel

def kv26 : List Wr := [⟨0xf9f3e7cf9f3e7c4d8855636e74cfe71af8ffffe03f80fe00009b33ffcffce9bfce7ff3f, 0x60c07f01fc07cf800235509200020004a020, 0⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_0 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 0xf9f3e7cf9f3e7c4d8855636e74cfe71af8ffffe03f80fe00009b33ffcffce9bfce7ff3f) (((pairsA [] kv26).drop (1 * 0)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_1 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 0xf9f3e7cf9f3e7c4d8855636e74cfe71af8ffffe03f80fe00009b33ffcffce9bfce7ff3f) (((pairsA [] kv26).drop (1 * 1)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 0xf9f3e7cf9f3e7c4d8855636e74cfe71af8ffffe03f80fe00009b33ffcffce9bfce7ff3f) (((pairsA [] kv26).drop (1 * 2)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_3 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 0xf9f3e7cf9f3e7c4d8855636e74cfe71af8ffffe03f80fe00009b33ffcffce9bfce7ff3f) (((pairsA [] kv26).drop (1 * 3)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_4 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 0xf9f3e7cf9f3e7c4d8855636e74cfe71af8ffffe03f80fe00009b33ffcffce9bfce7ff3f) (((pairsA [] kv26).drop (1 * 4)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_5 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 0xf9f3e7cf9f3e7c4d8855636e74cfe71af8ffffe03f80fe00009b33ffcffce9bfce7ff3f) (((pairsA [] kv26).drop (1 * 5)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_6 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 0xf9f3e7cf9f3e7c4d8855636e74cfe71af8ffffe03f80fe00009b33ffcffce9bfce7ff3f) (((pairsA [] kv26).drop (1 * 6)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_7 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 0xf9f3e7cf9f3e7c4d8855636e74cfe71af8ffffe03f80fe00009b33ffcffce9bfce7ff3f) (((pairsA [] kv26).drop (1 * 7)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_8 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 0xf9f3e7cf9f3e7c4d8855636e74cfe71af8ffffe03f80fe00009b33ffcffce9bfce7ff3f) (((pairsA [] kv26).drop (1 * 8)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_9 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 0xf9f3e7cf9f3e7c4d8855636e74cfe71af8ffffe03f80fe00009b33ffcffce9bfce7ff3f) (((pairsA [] kv26).drop (1 * 9)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_10 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 0xf9f3e7cf9f3e7c4d8855636e74cfe71af8ffffe03f80fe00009b33ffcffce9bfce7ff3f) (((pairsA [] kv26).drop (1 * 10)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_11 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 0xf9f3e7cf9f3e7c4d8855636e74cfe71af8ffffe03f80fe00009b33ffcffce9bfce7ff3f) (((pairsA [] kv26).drop (1 * 11)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_12 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 0xf9f3e7cf9f3e7c4d8855636e74cfe71af8ffffe03f80fe00009b33ffcffce9bfce7ff3f) (((pairsA [] kv26).drop (1 * 12)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_13 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 0xf9f3e7cf9f3e7c4d8855636e74cfe71af8ffffe03f80fe00009b33ffcffce9bfce7ff3f) (((pairsA [] kv26).drop (1 * 13)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_14 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 0xf9f3e7cf9f3e7c4d8855636e74cfe71af8ffffe03f80fe00009b33ffcffce9bfce7ff3f) (((pairsA [] kv26).drop (1 * 14)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_15 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 0xf9f3e7cf9f3e7c4d8855636e74cfe71af8ffffe03f80fe00009b33ffcffce9bfce7ff3f) (((pairsA [] kv26).drop (1 * 15)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_16 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 0xf9f3e7cf9f3e7c4d8855636e74cfe71af8ffffe03f80fe00009b33ffcffce9bfce7ff3f) (((pairsA [] kv26).drop (1 * 16)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_17 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 0xf9f3e7cf9f3e7c4d8855636e74cfe71af8ffffe03f80fe00009b33ffcffce9bfce7ff3f) (((pairsA [] kv26).drop (1 * 17)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_18 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 0xf9f3e7cf9f3e7c4d8855636e74cfe71af8ffffe03f80fe00009b33ffcffce9bfce7ff3f) (((pairsA [] kv26).drop (1 * 18)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_19 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 0xf9f3e7cf9f3e7c4d8855636e74cfe71af8ffffe03f80fe00009b33ffcffce9bfce7ff3f) (((pairsA [] kv26).drop (1 * 19)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_20 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 0xf9f3e7cf9f3e7c4d8855636e74cfe71af8ffffe03f80fe00009b33ffcffce9bfce7ff3f) (((pairsA [] kv26).drop (1 * 20)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_21 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 0xf9f3e7cf9f3e7c4d8855636e74cfe71af8ffffe03f80fe00009b33ffcffce9bfce7ff3f) (((pairsA [] kv26).drop (1 * 21)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_22 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 0xf9f3e7cf9f3e7c4d8855636e74cfe71af8ffffe03f80fe00009b33ffcffce9bfce7ff3f) (((pairsA [] kv26).drop (1 * 22)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_23 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 0xf9f3e7cf9f3e7c4d8855636e74cfe71af8ffffe03f80fe00009b33ffcffce9bfce7ff3f) (((pairsA [] kv26).drop (1 * 23)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_24 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 0xf9f3e7cf9f3e7c4d8855636e74cfe71af8ffffe03f80fe00009b33ffcffce9bfce7ff3f) (((pairsA [] kv26).drop (1 * 24)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_25 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 0xf9f3e7cf9f3e7c4d8855636e74cfe71af8ffffe03f80fe00009b33ffcffce9bfce7ff3f) (((pairsA [] kv26).drop (1 * 25)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_26 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 0xf9f3e7cf9f3e7c4d8855636e74cfe71af8ffffe03f80fe00009b33ffcffce9bfce7ff3f) (((pairsA [] kv26).drop (1 * 26)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_27 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 0xf9f3e7cf9f3e7c4d8855636e74cfe71af8ffffe03f80fe00009b33ffcffce9bfce7ff3f) (((pairsA [] kv26).drop (1 * 27)).take 1) = false := by decide +kernel

theorem kid26 : search LO LO 9 kv26 127 111 2 0xf9f3e7cf9f3e7c4d8855636e74cfe71af8ffffe03f80fe00009b33ffcffce9bfce7ff3f = false := by
  have h1 : isT LO kv26 = false := by decide +kernel
  have h2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 0xf9f3e7cf9f3e7c4d8855636e74cfe71af8ffffe03f80fe00009b33ffcffce9bfce7ff3f) (pairsA [] kv26) = false := by
    refine anyP_chunks _ 1 28 _ (by decide +kernel) fun i hi => ?_
    interval_cases i
    · exact kid26_0
    · exact kid26_1
    · exact kid26_2
    · exact kid26_3
    · exact kid26_4
    · exact kid26_5
    · exact kid26_6
    · exact kid26_7
    · exact kid26_8
    · exact kid26_9
    · exact kid26_10
    · exact kid26_11
    · exact kid26_12
    · exact kid26_13
    · exact kid26_14
    · exact kid26_15
    · exact kid26_16
    · exact kid26_17
    · exact kid26_18
    · exact kid26_19
    · exact kid26_20
    · exact kid26_21
    · exact kid26_22
    · exact kid26_23
    · exact kid26_24
    · exact kid26_25
    · exact kid26_26
    · exact kid26_27
  rw [search, h1, h2]; rfl

def kv27 : List Wr := [⟨0x58b162c58b162c480850404e70c70718705000000000fe00009031e181bce10c0c00c00, 0xb162c58be82c5800214101200082023020a, 16⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid27 : search LO LO 9 kv27 127 111 2 0x58b162c58b162c480850404e70c70718705000000000fe00009031e181bce10c0c00c00 = false := by decide +kernel

theorem kids_false : ∀ q ∈ kids, search LO LO 9 q.v q.c1 q.c2 q.c3 q.g = false := by
  intro q hq
  simp only [kids, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact kid0
  · exact kid1
  · exact kid2
  · exact kid3
  · exact kid4
  · exact kid5
  · exact kid6
  · exact kid7
  · exact kid8
  · exact kid9
  · exact kid10
  · exact kid11
  · exact kid12
  · exact kid13
  · exact kid14
  · exact kid15
  · exact kid16
  · exact kid17
  · exact kid18
  · exact kid19
  · exact kid20
  · exact kid21
  · exact kid22
  · exact kid23
  · exact kid24
  · exact kid25
  · exact kid26
  · exact kid27


-- Part 6: the theta graph needs eleven binary gates, negations free.

def okL (L y : ℕ) : Bool :=
  Nat.blt L (2 ^ 143) && (List.range 143).all fun i => !(L.testBit i) || (y.testBit i != y.testBit (143 + i))

lemma okL_spec {L y : ℕ} (h : okL L y = true) (i : ℕ) (hi : L.testBit i = true) :
    y.testBit i ≠ y.testBit (143 + i) := by
  rw [okL, Bool.and_eq_true] at h
  have hlt : i < 143 := by
    by_contra hc
    have h1 : L < 2 ^ 143 := by simpa [Nat.blt_eq] using h.1
    have := Nat.testBit_lt_two_pow (lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by omega) (not_lt.mp hc)))
    rw [this] at hi
    exact Bool.false_ne_true hi
  have h2 := List.all_eq_true.mp h.2 i (List.mem_range.mpr hlt)
  rw [hi] at h2
  simpa using h2

def W0 : Set ℕ := {x | x = 0 ∨ ∃ i : Fin 7, x = ip i}

def LB (h : ℕ) : ℕ := [8, 7, 8, 8, 8, 8, 7].getD h 0

lemma subW (h : ℕ) (ws : List Wr)
    (hc : ∀ i : Fin 7, Nat.land (ip i) (mask h) = 0 ∨ ∃ u ∈ ws, u.w = Nat.land (ip i) (mask h))
    {W : Set ℕ} (hW : ∀ x ∈ W, x = 0 ∨ ∃ i : Fin 7, x = Nat.land (ip i) (mask h)) :
    ∀ x ∈ W, x = 0 ∨ ∃ u ∈ ws, u.w = x := by
  intro x hx
  rcases hW x hx with e | ⟨i, e⟩
  · exact Or.inl e
  · rw [e]; exact hc i

theorem subBound (h : ℕ) (hh : h < 7) {W : Set ℕ} (h0 : 0 ∈ W)
    (hW : ∀ x ∈ W, x = 0 ∨ ∃ i : Fin 7, x = Nat.land (ip i) (mask h)) :
    ¬ Der opN (LB h - 1) W (Nat.land LO (mask h)) := by
  interval_cases h
  · exact refute (L := L0) (y := Y0) (ws := ws0) (okL_spec (by decide +kernel)) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) sub0 h0
      (subW 0 ws0 (by decide +kernel) hW)
  · exact refute (L := L1) (y := Y1) (ws := ws1) (okL_spec (by decide +kernel)) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) sub1 h0
      (subW 1 ws1 (by decide +kernel) hW)
  · exact refute (L := L2) (y := Y2) (ws := ws2) (okL_spec (by decide +kernel)) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) sub2 h0
      (subW 2 ws2 (by decide +kernel) hW)
  · exact refute (L := L3) (y := Y3) (ws := ws3) (okL_spec (by decide +kernel)) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) sub3 h0
      (subW 3 ws3 (by decide +kernel) hW)
  · exact refute (L := L4) (y := Y4) (ws := ws4) (okL_spec (by decide +kernel)) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) sub4 h0
      (subW 4 ws4 (by decide +kernel) hW)
  · exact refute (L := L5) (y := Y5) (ws := ws5) (okL_spec (by decide +kernel)) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) sub5 h0
      (subW 5 ws5 (by decide +kernel) hW)
  · exact refute (L := L6) (y := Y6) (ws := ws6) (okL_spec (by decide +kernel)) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) sub6 h0
      (subW 6 ws6 (by decide +kernel) hW)

lemma root_ip : ∀ i : Fin 7, ∃ u ∈ root, u.w = ip i := by decide +kernel

lemma ip_root : ∀ u ∈ root, ∃ i : Fin 7, u.w = ip i := by decide +kernel

lemma ip_lt : ∀ i : Fin 7, ip i < 2 ^ 286 := by decide +kernel

lemma LO_lt : LO < 2 ^ 286 := by decide +kernel

lemma Tn_inv : ∀ p : Fin 3, ∀ i : Fin 286,
    sIdx (Tn p) i.val < 286 ∧ sIdx (Tn p) (sIdx (Tn p) i.val) = i.val := by decide +kernel

lemma Tn_ip : ∀ p : Fin 3, ∀ i : Fin 7, ∀ r : Fin 286,
    (ip (pm p i)).testBit r.val = (ip i).testBit (sIdx (Tn p) r.val) := by decide +kernel

lemma Tn_LO : ∀ p : Fin 3, ∀ r : Fin 286,
    LO.testBit r.val = LO.testBit (sIdx (Tn p) r.val) := by decide +kernel

lemma pm_inv : ∀ p : Fin 3, ∀ i : Fin 7, pm p (pm p i) = i := by decide

lemma allowed_spec : ∀ t : Fin 4, ∀ i j : Fin 7, i ≠ j →
    (∀ p : Fin 3, opN t (ip i) (ip j) ≤ opN t (ip (pm p i)) (ip (pm p j))) →
    memN (opN t (ip i) (ip j)) allowed = true := by decide +kernel

lemma sg_ip (p : Fin 3) (i : Fin 7) : sg 286 (Tn p) (ip i) = ip (pm p i) :=
  sg_eq (bdd_of_lt (ip_lt _)) fun r hr => Tn_ip p i ⟨r, hr⟩

lemma sg_LO (p : Fin 3) : sg 286 (Tn p) LO = LO :=
  sg_eq (bdd_of_lt LO_lt) fun r hr => Tn_LO p ⟨r, hr⟩

lemma sg_zero (N T : ℕ) : sg N T 0 = 0 :=
  sg_eq (fun i _ => Nat.zero_testBit i) fun r _ => by rw [Nat.zero_testBit, Nat.zero_testBit]

lemma sg_W0 (p : Fin 3) : sg 286 (Tn p) '' W0 = W0 := by
  ext x
  constructor
  · rintro ⟨w, rfl | ⟨i, rfl⟩, rfl⟩
    · exact Or.inl (sg_zero _ _)
    · exact Or.inr ⟨pm p i, sg_ip p i⟩
  · rintro (rfl | ⟨i, rfl⟩)
    · exact ⟨0, Or.inl rfl, sg_zero _ _⟩
    · exact ⟨ip (pm p i), Or.inr ⟨pm p i, rfl⟩, by rw [sg_ip, pm_inv]⟩

lemma bdd_W0 : ∀ x ∈ W0, Bdd 286 x := by
  rintro x (rfl | ⟨i, rfl⟩)
  · exact fun i _ => Nat.zero_testBit i
  · exact bdd_of_lt (ip_lt i)

theorem theta : ¬ Der opN 10 W0 LO := by
  intro h
  obtain ⟨l, hk, hV, hU, hC, hmin⟩ := exists_sorted h
  have h0 : (0 : ℕ) ∈ W0 := Or.inl rfl
  have hLO : LO ≠ 0 := by decide +kernel
  have hL : ∀ i, LO.testBit i = true → LO.testBit i ≠ LO.testBit (143 + i) :=
    fun i hi => okL_spec (L := LO) (y := LO) (by decide +kernel) i hi
  have caps : ∀ h < 7, kills (mask h) l + LB h ≤ 10 := by
    intro h hh
    obtain ⟨n, hn, hd⟩ := der_masked (m := mask h) l hV h0
    by_contra hc
    have hLB : 1 ≤ LB h := by interval_cases h <;> decide
    refine subBound h hh (W := (fun w => Nat.land w (mask h)) '' W0) ⟨0, h0, by simp [Nat.land]⟩ ?_
      (hd.le (by omega))
    rintro _ ⟨w, rfl | ⟨i, rfl⟩, rfl⟩
    · left; show Nat.land 0 (mask h) = 0; simp [Nat.land]
    · exact Or.inr ⟨i, rfl⟩
  have hy : ∀ h < 7, Nat.land LO (mask h) ≠ 0 := by
    intro h hh
    have key : ∀ h : Fin 7, Nat.land LO (mask h.val) ≠ 0 := by decide +kernel
    exact key ⟨h, hh⟩
  have hfl : ∀ u ∈ root, ∀ h, u.f.testBit h = true → h < 7 ∧ Nat.land u.w (mask h) = 0 := by
    have k1 : ∀ u ∈ root, u.f < 2 ^ 7 := by decide +kernel
    have k2 : ∀ u ∈ root, ∀ h : Fin 7, u.f.testBit h.val = true → Nat.land u.w (mask h.val) = 0 := by
      decide +kernel
    intro u hu h hb
    have hlt : h < 7 := by
      by_contra hc
      have := Nat.testBit_lt_two_pow (lt_of_lt_of_le (k1 u hu)
        (Nat.pow_le_pow_right (by omega) (not_lt.mp hc)))
      rw [this] at hb
      exact Bool.false_ne_true hb
    exact ⟨hlt, k2 u hu ⟨h, hlt⟩ hb⟩
  have hrep : Rep LO 7 mask root (need LO l) := by
    refine root_rep hL hLO (by decide +kernel) (by decide +kernel) hfl (by decide +kernel) hV h0 ?_
    rintro x (rfl | ⟨i, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr (root_ip i)
  have hbud : Bud 7 mask 127 127 66 l := by
    intro h hh
    have c := caps h hh
    interval_cases h <;> simp only [LB, List.getD_cons_zero, List.getD_cons_succ] at c <;>
      refine ⟨by omega, fun _ => by decide, fun _ => by decide, fun h3 => ?_⟩ <;>
      first | (exfalso; omega) | decide
  cases l with
  | nil =>
    have e : ∀ i : Fin 7, LO ≠ ip i := by decide +kernel
    rcases hV with h | ⟨i, h⟩
    · exact hLO h
    · exact e i h
  | cons s l =>
    have al : memN s.val allowed = true := by
      obtain ⟨fa, fb, fab, _⟩ := step_facts hV h0
      rcases hV.1 with e | ⟨i, ei⟩
      · exact absurd e fa
      rcases hV.2.1 with e | ⟨j, ej⟩
      · exact absurd e fb
      have hs : s.val = opN s.t (ip i) (ip j) := by rw [St.val, ei, ej]
      rw [hs]
      refine allowed_spec s.t i j (fun e => fab (by rw [ei, ej, e])) fun p => ?_
      have vm := valid_map (Tn p) (fun i hi => Tn_inv p ⟨i, hi⟩) (s :: l) bdd_W0 hV
      rw [sg_LO, sg_W0] at vm
      have := hmin _ vm (by simp)
      change s.val ≤ (mapSt 286 (Tn p) s).val at this
      rw [mapSt_val, hs, sg_op, sg_ip, sg_ip] at this
      exact this
    have := level (k := 9) (r := rootNext allowed kids) hy hL hV h0 hU (by simpa using hk) hC hrep hbud ?_
    · rw [rootSearch] at this
      exact Bool.false_ne_true this
    · intro v' d1 d2 d3 hv' hb'
      show cond (memN s.val allowed) (!(isKid v' d1 d2 d3 s.val kids)) false = true
      rw [al, cond_true]
      cases hkid : isKid v' d1 d2 d3 s.val kids
      · rfl
      · have hm := kids_false _ (isKid_mem kids hkid)
        have hs := search_complete hy hL 9 l _ v' s.val d1 d2 d3 hV.2.2.2 (Or.inr h0) hU.2
          (by simp only [List.length_cons] at hk; omega) hC.2 hv' hb'
        simp only at hm
        rw [hm] at hs
        exact absurd hs Bool.false_ne_true

-- Part 7: circuits.

abbrev Om := Fin 9 → Bool

def zr : Om := fun _ => false

def nrm (F : Om → Bool) : Om → Bool := fun x => F x != F zr

def bc (gs : List Gate) : ℕ := gs.countP fun g => !(g.op.eval [false])

def nc (gs : List Gate) : ℕ := gs.countP fun g => g.op.eval [false]

def runG (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

def OkG (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

lemma getD_snoc (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false = if i = w.length then b else w.getD i false := by
  by_cases h : i = w.length
  · subst h; simp [List.getD_eq_getElem?_getD]
  · rw [ite_eq_right h]
    by_cases h1 : i < w.length
    · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
    · have h2 : (w ++ [b]).length ≤ i := by simp; omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h2,
        List.getElem?_eq_none (by omega : w.length ≤ i)]

lemma nrm_const (c : Bool) : nrm (fun _ => c) = fun _ => false := by
  funext x; simp [nrm]

lemma nrm_not (F : Om → Bool) : nrm (fun x => !(F x)) = nrm F := by
  funext x; simp only [nrm]; cases F x <;> cases F zr <;> rfl

lemma nrm_bin (c : Bool) (F G : Om → Bool) : ∃ t : Fin 4,
    nrm (fun x => if c then (F x || G x) else (F x && G x)) = opF t (nrm F) (nrm G) := by
  cases hc : c <;> cases hF : F zr <;> cases hG : G zr
  · exact ⟨0, by funext x; simp [nrm, opF, opB, hF, hG]⟩
  · exact ⟨2, by funext x; simp [nrm, opF, opB, hF, hG]⟩
  · exact ⟨3, by funext x; simp [nrm, opF, opB, hF, hG]; cases F x <;> cases G x <;> rfl⟩
  · exact ⟨1, by funext x; simp [nrm, opF, opB, hF, hG]⟩
  · exact ⟨1, by funext x; simp [nrm, opF, opB, hF, hG]⟩
  · exact ⟨3, by funext x; simp [nrm, opF, opB, hF, hG]; cases F x <;> cases G x <;> rfl⟩
  · exact ⟨2, by funext x; simp [nrm, opF, opB, hF, hG]⟩
  · exact ⟨0, by funext x; simp [nrm, opF, opB, hF, hG]⟩

lemma circ (gs : List Gate) : ∀ (w : Om → List Bool) (m : ℕ) (U : Set (Om → Bool)),
    (∀ x, (w x).length = m) → (fun _ => false) ∈ U →
    (∀ i, nrm (fun x => (w x).getD i false) ∈ U) → (∀ g ∈ gs, OkG g) →
    ∀ o, Der opF (bc gs) U (nrm fun x => (runG gs (w x)).getD o false) := by
  induction gs with
  | nil => intro w m U _ _ hU _ o; exact Der.here (hU o)
  | cons g gs ih =>
    intro w m U hl h0 hU hg o
    obtain ⟨hop, hlen⟩ := hg g (by simp)
    have hgs : ∀ g' ∈ gs, OkG g' := fun g' h => hg g' (by simp [h])
    let v : Om → Bool := fun x => g.op.eval (g.inputs.map fun i => (w x).getD i false)
    let w' : Om → List Bool := fun x => w x ++ [v x]
    have hl' : ∀ x, (w' x).length = m + 1 := fun x => by simp [w', hl]
    have hw' (U' : Set (Om → Bool)) (hs : U ⊆ U') (hv : nrm v ∈ U') :
        ∀ i, nrm (fun x => (w' x).getD i false) ∈ U' := by
      intro i
      by_cases hi : i = m
      · have e : (fun x => (w' x).getD i false) = v := by
          funext x; simp only [w']; rw [getD_snoc, ite_eq_left (by rw [hl, hi])]
        rw [e]; exact hv
      · have e : (fun x => (w' x).getD i false) = fun x => (w x).getD i false := by
          funext x; simp only [w']; rw [getD_snoc, ite_eq_right (by rw [hl]; exact hi)]
        rw [e]; exact hs (hU i)
    have fin0 (hv : nrm v ∈ U) : Der opF (bc gs) U (nrm fun x => (runG (g :: gs) (w x)).getD o false) :=
      ih w' (m + 1) U hl' h0 (hw' U (fun _ h => h) hv) hgs o
    have bcle : bc gs ≤ bc (g :: gs) := by
      rw [bc, bc, List.countP_cons]; omega
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    have bin (c : Bool) (hb : bc (g :: gs) = bc gs + 1)
        (hev : ∀ l : List Bool, g.op.eval l = if c then l.any id else l.all id) :
        Der opF (bc (g :: gs)) U (nrm fun x => (runG (g :: gs) (w x)).getD o false) := by
      rcases hi : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨q, r⟩⟩⟩
      · refine (fin0 ?_).le bcle
        have e : v = fun _ => !c := by
          funext x; simp only [v, hi, hev]; cases c <;> rfl
        rw [e, nrm_const]; exact h0
      · refine (fin0 ?_).le bcle
        have e : v = fun x => (w x).getD i false := by
          funext x; simp only [v, hi, hev]; cases c <;> simp
        rw [e]; exact hU i
      · obtain ⟨t, ht⟩ := nrm_bin c (fun x => (w x).getD i false) (fun x => (w x).getD j false)
        have e : v = fun x => if c then ((w x).getD i false || (w x).getD j false)
            else ((w x).getD i false && (w x).getD j false) := by
          funext x; simp only [v, hi, hev]; cases c <;> simp
        have ev : nrm v = opF t (nrm fun x => (w x).getD i false) (nrm fun x => (w x).getD j false) := by
          rw [e]; exact ht
        rw [hb]
        refine Der.step t _ _ (hU i) (hU j) ?_
        refine ih w' (m + 1) _ hl' (Or.inr h0) (hw' _ (Set.subset_insert _ _) ?_) hgs o
        rw [ev]; exact Or.inl rfl
      · rw [hi] at hlen; simp at hlen
    rcases hop with h | h | h
    · refine bin false ?_ (fun l => by rw [h]; rfl)
      rw [bc, bc, List.countP_cons, h]; rfl
    · refine bin true ?_ (fun l => by rw [h]; rfl)
      rw [bc, bc, List.countP_cons, h]; rfl
    · refine (fin0 ?_).le bcle
      rcases hi : g.inputs with _ | ⟨i, r⟩
      · have e : v = fun _ => true := by funext x; simp only [v, hi, h]; rfl
        rw [e, nrm_const]; exact h0
      · have e : v = fun x => !((w x).getD i false) := by funext x; simp only [v, hi, h]; rfl
        rw [e, nrm_not]; exact hU i

def fG : Om → Bool := fun x =>
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) ||
  (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

def pin (j : Fin 9) (F : Om → Bool) : Om → Bool := fun x => F (Function.update x j false)

def rowTab (j : Fin 9) : ℕ := [0, ip 0, ip 1, ip 2, 0, ip 3, ip 4, ip 5, ip 6].getD j.val 0

def row (r : Fin 286) : Om := fun j => (rowTab j).testBit r.val

def encF (F : Om → Bool) : ℕ := Nat.ofBits fun r : Fin 286 => F (row r)

lemma encF_bit (F : Om → Bool) (i : ℕ) (hi : i < 286) : (encF F).testBit i = F (row ⟨i, hi⟩) := by
  rw [encF, Nat.testBit_ofBits_lt _ _ hi]

lemma encF_bdd (F : Om → Bool) : Bdd 286 (encF F) := fun i hi => by
  rw [encF, Nat.testBit_ofBits_ge _ _ hi]

lemma encF_op (t : Fin 4) (F G : Om → Bool) : encF (opF t F G) = opN t (encF F) (encF G) := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 286
  · rw [opN_bit, encF_bit _ _ hi, encF_bit _ _ hi, encF_bit _ _ hi]; rfl
  · rw [encF_bdd _ i (by omega), bdd_op t (encF_bdd F) (encF_bdd G) i (by omega)]

lemma encF_eq {F : Om → Bool} {x : ℕ} (hx : Bdd 286 x) (h : ∀ r : Fin 286, F (row r) = x.testBit r.val) :
    encF F = x := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 286
  · rw [encF_bit _ _ hi]; exact h ⟨i, hi⟩
  · rw [encF_bdd _ i (by omega), hx i (by omega)]

lemma fG_rows : ∀ r : Fin 286, pin 4 (pin 0 fG) (row r) = LO.testBit r.val := by decide +kernel

lemma opF_false_left (t : Fin 4) (F : Om → Bool) :
    opF t (fun _ => false) F = (fun _ => false) ∨ opF t (fun _ => false) F = F := by
  fin_cases t
  · left; funext x; simp [opF, opB]
  · right; funext x; simp [opF, opB]
  · left; funext x; simp [opF, opB]
  · right; funext x; simp [opF, opB]

lemma opF_false_right (t : Fin 4) (F : Om → Bool) :
    opF t F (fun _ => false) = (fun _ => false) ∨ opF t F (fun _ => false) = F := by
  fin_cases t
  · left; funext x; simp [opF, opB]
  · right; funext x; simp [opF, opB]
  · right; funext x; simp [opF, opB]
  · left; funext x; simp [opF, opB]

def pt (l : List (Fin 9)) : Om := fun j => l.contains j

theorem noDer (b : Fin 9) (hb : b = 2 ∨ b = 3) :
    ¬ Der opF 12 {F : Om → Bool | F = (fun _ => false) ∨ (∃ i : Fin 9, F = fun x => x i) ∨
      F = fun x => x 0 || x b} fG := by
  intro h
  have hb0 : b ≠ 0 := by rcases hb with rfl | rfl <;> decide
  have e0 : pin 0 (fun x : Om => x 0) = fun _ => false := by funext x; simp [pin]
  have e0z : pin 0 (fun _ : Om => false) = fun _ => false := rfl
  have e0i (i : Fin 9) (hi : i ≠ 0) : pin 0 (fun x : Om => x i) = fun x => x i := by
    funext x; simp [pin, Function.update_of_ne hi]
  have e0g : pin 0 (fun x : Om => x 0 || x b) = fun x => x b := by
    funext x; simp [pin, Function.update_of_ne hb0]
  have hE := h.elim (op' := opF) (pin 0) (fun _ _ _ => rfl) (fun x => x 0)
    (fun t F => by rw [e0]; exact opF_false_left t F) (fun t F => by rw [e0]; exact opF_false_right t F)
    {F : Om → Bool | F = (fun _ => false) ∨ (∃ i : Fin 9, i ≠ 0 ∧ F = fun x => x i) ∨
      F = fun x => x 0 || x b}
    (by
      rintro F (rfl | ⟨i, rfl⟩ | rfl)
      · exact Or.inr (Or.inl rfl)
      · by_cases hi : i = 0
        · subst hi; exact Or.inl rfl
        · exact Or.inr (Or.inr (Or.inl ⟨i, hi, rfl⟩))
      · exact Or.inr (Or.inr (Or.inr rfl)))
    (by
      intro e
      have := congrFun e (pt [0])
      revert this; decide)
    ⟨fun _ => false, Or.inl rfl, by rw [e0]; rfl⟩
  rcases hE with h | ⟨k', hk', h⟩
  · have := h.agree (pt [0, b, 5]) (pt [b, 5]) (by
      rintro F (rfl | ⟨i, hi, rfl⟩ | rfl)
      · rfl
      · revert hi; rcases hb with rfl | rfl <;> revert i <;> decide
      · rcases hb with rfl | rfl <;> decide)
    revert this; rcases hb with rfl | rfl <;> decide
  · have hk : k' = 11 := by omega
    subst hk
    have e4 : pin 4 (fun x : Om => x 4) = fun _ => false := by funext x; simp [pin]
    have e4i (i : Fin 9) (hi : i ≠ 4) : pin 4 (fun x : Om => x i) = fun x => x i := by
      funext x; simp [pin, Function.update_of_ne hi]
    have hE := h.elim (op' := opF) (pin 4) (fun _ _ _ => rfl) (fun x => x 4)
      (fun t F => by rw [e4]; exact opF_false_left t F)
      (fun t F => by rw [e4]; exact opF_false_right t F)
      {F : Om → Bool | F = (fun _ => false) ∨ ∃ i : Fin 9, i ≠ 0 ∧ i ≠ 4 ∧ F = fun x => x i}
      (by
        rintro _ ⟨F, hF, rfl⟩
        rcases hF with rfl | ⟨i, hi, rfl⟩ | rfl
        · exact Or.inr (Or.inl rfl)
        · rw [e0i i hi]
          by_cases h4 : i = 4
          · subst h4; exact Or.inl rfl
          · exact Or.inr (Or.inr ⟨i, hi, h4, rfl⟩)
        · rw [e0g]
          exact Or.inr (Or.inr ⟨b, hb0, by rcases hb with rfl | rfl <;> decide, rfl⟩))
      (by
        intro e
        have := congrFun e (pt [4])
        revert this; decide)
      ⟨fun _ => false, Or.inl rfl, by rw [e4]; rfl⟩
    rcases hE with h | ⟨k', hk', h⟩
    · have := h.agree (pt [3, 4]) (pt [3]) (by
        rintro F (rfl | ⟨i, h1, h2, rfl⟩)
        · rfl
        · revert h1 h2; revert i; decide)
      revert this; decide
    · have hk : k' = 10 := by omega
      subst hk
      have hN := h.map (op' := opN) encF encF_op
      rw [encF_eq (bdd_of_lt LO_lt) fG_rows] at hN
      refine theta (hN.mono ?_)
      rintro _ ⟨_, ⟨F, hF, rfl⟩, rfl⟩
      rcases hF with rfl | ⟨i, h1, h2, rfl⟩
      · left
        exact encF_eq (fun i _ => Nat.zero_testBit i) fun r => by rw [Nat.zero_testBit]; rfl
      · right
        rw [e4i i h2]
        have hr : ∀ i : Fin 9, i ≠ 0 → i ≠ 4 → ∃ j : Fin 7, rowTab i = ip j := by decide +kernel
        obtain ⟨j, hj⟩ := hr i h1 h2
        exact ⟨j, encF_eq (bdd_of_lt (ip_lt j)) fun r => by show (rowTab i).testBit _ = _; rw [hj]⟩

lemma ofFn_getD (n : ℕ) (y : Fin n → Bool) (i : ℕ) :
    (List.ofFn y).getD i false = if h : i < n then y ⟨i, h⟩ else false := by
  by_cases h : i < n
  · rw [dif_pos h]; simp [List.getD_eq_getElem?_getD, h]
  · rw [dif_neg h]; simp [List.getD_eq_getElem?_getD, h]

lemma two_count {α : Type} (p : α → Bool) (l : List α) (i j : ℕ) (hij : i < j) (hj : j < l.length)
    (h1 : p (l[i]'(by omega)) = true) (h2 : p l[j] = true) : 2 ≤ l.countP p := by
  rw [← List.take_append_drop j l, List.countP_append]
  have a1 : 1 ≤ (l.take j).countP p := by
    rw [Nat.succ_le_iff, List.countP_pos_iff]
    refine ⟨l[i]'(by omega), ?_, h1⟩
    rw [List.mem_take_iff_getElem]
    exact ⟨i, by omega, rfl⟩
  have a2 : 1 ≤ (l.drop j).countP p := by
    rw [Nat.succ_le_iff, List.countP_pos_iff]
    refine ⟨l[j], ?_, h2⟩
    rw [List.mem_drop_iff_getElem]
    exact ⟨0, by omega, by simp⟩
  omega

-- at most fifteen gates, first gate x0 or xb, at least two negations: impossible
theorem no15 (b : Fin 9) (hb : b = 2 ∨ b = 3) (C : Circuit) (hC : FanInTwo C) (hsize : C.size ≤ 15)
    (hw : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y b))
    (hn : 2 ≤ nc C.gates) (hf : circuitFun 9 C = fG) : False := by
  obtain ⟨gates, out⟩ := C
  cases gates with
  | nil => simp [nc] at hn
  | cons g gs =>
    have hlen : gs.length ≤ 14 := by
      have : (Circuit.mk (g :: gs) out).size = gs.length + 1 := rfl
      omega
    have hg0 := hC g (by simp)
    have hfirst (x : Om) : g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) = (x 0 || x b) := by
      have h := hw x
      change (runG gs (List.ofFn x ++ [_])).getD 9 false = _ at h
      have keep : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
          (runG gs w).getD i false = w.getD i false := by
        intro gs
        induction gs with
        | nil => intro w i _; rfl
        | cons q gs ih =>
          intro w i hi
          change (runG gs (w ++ [_])).getD i false = _
          rw [ih _ i (by simp; omega), getD_snoc, ite_eq_right (by omega)]
      rw [keep _ _ _ (by simp), getD_snoc, ite_eq_left (by simp)] at h
      exact h
    have hnot : g.op.eval [false] = false := by
      rcases hg0.1 with h | h | h
      · rw [h]; rfl
      · rw [h]; rfl
      · exfalso
        have := hfirst zr
        rw [h] at this
        have hz : ∀ i, (List.ofFn zr).getD i false = false := by
          intro i
          rw [ofFn_getD]
          split_ifs <;> rfl
        rcases hi : g.inputs with _ | ⟨i, r⟩
        · rw [hi] at this; revert this; simp [GateOp.eval, zr]
        · rw [hi] at this
          simp only [List.map_cons, hz] at this
          revert this; simp [GateOp.eval, zr]
    have hnc : nc (g :: gs) = nc gs := by
      rw [nc, nc, List.countP_cons, hnot]; rfl
    have hn' : 2 ≤ nc gs := by rw [← hnc]; exact hn
    have hsum : gs.length = nc gs + bc gs := by
      have := List.length_eq_countP_add_countP (fun g : Gate => g.op.eval [false]) (l := gs)
      rw [this, nc, bc]
      congr 1
    let U : Set (Om → Bool) := {F | F = (fun _ => false) ∨ (∃ i : Fin 9, F = fun x => x i) ∨
      F = fun x => x 0 || x b}
    have hD : Der opF (bc gs) U (nrm fun x => (runG gs (List.ofFn x ++ [x 0 || x b])).getD out false) := by
      refine circ gs (fun x => List.ofFn x ++ [x 0 || x b]) 10 U (fun x => by simp) (Or.inl rfl) ?_
        (fun q hq => hC q (by simp [hq])) out
      intro i
      by_cases h9 : i = 9
      · right; right
        funext x
        simp only [nrm, getD_snoc, List.length_ofFn, ite_eq_left h9]
        simp [zr]
      · by_cases hi : i < 9
        · right; left
          refine ⟨⟨i, hi⟩, ?_⟩
          funext x
          simp only [nrm, getD_snoc, List.length_ofFn, ite_eq_right h9, ofFn_getD, dif_pos hi]
          simp [zr]
        · left
          funext x
          simp only [nrm, getD_snoc, List.length_ofFn, ite_eq_right h9, ofFn_getD, dif_neg hi]
          rfl
    have he : (nrm fun x => (runG gs (List.ofFn x ++ [x 0 || x b])).getD out false) = fG := by
      have e : (fun x : Om => (runG gs (List.ofFn x ++ [x 0 || x b])).getD out false) = fG := by
        rw [← hf]
        funext x
        rw [← hfirst x]
        rfl
      rw [e]
      funext x
      have : fG zr = false := by decide
      simp [nrm, this]
    rw [he] at hD
    exact noDer b hb (hD.le (by omega))

lemma nc_two {gates : List Gate} (i j : Fin gates.length) (hij : i ≠ j)
    (hi : (gates.get i).op = GateOp.not) (hj : (gates.get j).op = GateOp.not) : 2 ≤ nc gates := by
  have pi : (gates[i.val]'i.isLt).op.eval [false] = true := by
    have : (gates[i.val]'i.isLt).op = GateOp.not := hi
    rw [this]; rfl
  have pj : (gates[j.val]'j.isLt).op.eval [false] = true := by
    have : (gates[j.val]'j.isLt).op = GateOp.not := hj
    rw [this]; rfl
  rcases lt_or_gt_of_ne (fun e => hij (Fin.ext e) : i.val ≠ j.val) with h | h
  · exact two_count _ gates i.val j.val h j.isLt pi pj
  · exact two_count _ gates j.val i.val h i.isLt pj pi

private theorem keep3287 (gs : List Gate) (w : List Bool) (k : Nat) (h : k < w.length) :
    ((Circuit.mk gs 0).wires w).getD k false = w.getD k false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change ((Circuit.mk gs 0).wires (w ++ [_])).getD k false = _
    rw [ih _ (by simp; omega)]
    simp [List.getD,List.getElem?_append,h]

end PEqualNP.Outside.L_meta_3963
open PEqualNP.Outside.L_meta_3963 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem PEqualNP.Outside.L_meta_3963 : ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 ∧ x1.size = (14 : ℕ) ∧ List.countP (fun (x2 : PEqualNP.CircuitLowerBounds.Gate) => x2.op.eval [Bool.false]) x1.gates = (2 : ℕ) ∧ (∀ x2 ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (4 : ℕ), (7 : ℕ), (8 : ℕ)], List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => x4.inputs.contains x2) x1.gates ≤ (1 : ℕ)) ∧ (∀ (x2 : Fin (10 : ℕ)), ∃ (x3 : Fin (10 : ℕ) → Bool) (x4 : Fin (10 : ℕ) → Bool), (∀ (x5 : Fin (10 : ℕ)), x5 ≠ x2 → x3 x5 = x4 x5) ∧ x1.eval (List.ofFn x3) ≠ x1.eval (List.ofFn x4)) ∧ (∀ (x2 : Fin (10 : ℕ)) (x3 : Bool), ∃ (x4 : Fin (10 : ℕ) → Bool) (x5 : Fin (10 : ℕ) → Bool), x4 x2 = x3 ∧ x5 x2 = x3 ∧ x1.eval (List.ofFn x4) ≠ x1.eval (List.ofFn x5)) ∧ ∀ (x2 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x2 ++ [x2 (0 : Fin (9 : ℕ)) || x2 (2 : Fin (9 : ℕ))]) = [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x3 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x2 x3.1 && x2 x3.2 := by
  rintro ⟨C, fan, size, hcount, _, _, _, agree⟩
  let g : Gate := ⟨.or,[0,2]⟩
  let D : Circuit := ⟨g :: C.gates,C.output⟩
  have gate (x : Fin 9 → Bool) : g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) = (x 0 || x 2) := by
    simp [g,GateOp.eval,List.getD]
  have fd : FanInTwo D := by
    intro a h
    rcases List.mem_cons.mp h with e|mem
    · subst a; simp [g]
    · exact fan _ mem
  apply no15 2 (Or.inl rfl) D fd
  · change C.gates.length + 1 ≤ 15
    change C.gates.length = 14 at size
    omega
  · intro x
    change ((Circuit.mk C.gates 0).wires (_ ++ [_])).getD 9 false = _
    rw [gate,keep3287 _ _ _ (by simp)]
    simp [List.getD]
  · simpa [D,g,nc,List.countP_cons,GateOp.eval] using hcount.ge
  · funext x
    change C.eval (List.ofFn x ++ [_]) = _
    rw [gate,agree]
    simp [fG,List.any,Bool.or_assoc]
