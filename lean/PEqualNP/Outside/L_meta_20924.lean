import Mathlib.Tactic
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def PEqualNP.Outside.L_meta_20924.stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

open PEqualNP.Outside.L_meta_20924

def PEqualNP.Outside.L_meta_20924.W (gs : List Gate) (x : List Bool) : List Bool := gs.foldl stp x

def PEqualNP.Outside.L_meta_20924.Good (g : Gate) : Prop := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

lemma PEqualNP.Outside.L_meta_20924.W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = stp (W gs x) g := by simp [W]

lemma PEqualNP.Outside.L_meta_20924.W_len (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => rw [W_snoc, stp]; simp [ih]; omega

lemma PEqualNP.Outside.L_meta_20924.getD_lt (l : List Bool) (b : Bool) (i : ℕ) (h : i < l.length) :
    (l ++ [b]).getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma PEqualNP.Outside.L_meta_20924.getD_len (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

lemma PEqualNP.Outside.L_meta_20924.getD_big (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

def PEqualNP.Outside.L_meta_20924.lf (i : ℕ) : ℕ := [31, 992, 31744, 1015808, 33825, 67650, 135300, 270600, 541200].getD i 0

def PEqualNP.Outside.L_meta_20924.X (p : ℕ) : List Bool :=
  oneEach (⟨p / 5 % 4, by omega⟩ : Fin 4) (⟨p % 5, by omega⟩ : Fin 5)

lemma PEqualNP.Outside.L_meta_20924.X_len (p : ℕ) : (X p).length = 9 := by simp [X, oneEach]

lemma PEqualNP.Outside.L_meta_20924.lf_X : ∀ i < 9, ∀ p < 20, (lf i).testBit p = (X p).getD i false := by decide +kernel

def PEqualNP.Outside.L_meta_20924.ev (gs : List Gate) (g : Gate) (x : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => (W gs x).getD i false)

def PEqualNP.Outside.L_meta_20924.Irr (gs : List Gate) : Prop := ∀ pre g post, gs = pre ++ g :: post →
  (∀ a < 9 + pre.length, ¬ ∀ p < 20, ev pre g (X p) = (W pre (X p)).getD a false) ∧
  ¬ ∀ p < 20, ev pre g (X p) = false

lemma PEqualNP.Outside.L_meta_20924.Irr_prefix (gs : List Gate) (g : Gate) (h : Irr (gs ++ [g])) : Irr gs := by
  intro pre g' post e
  exact h pre g' (post ++ [g]) (by rw [e]; simp)

def PEqualNP.Outside.L_meta_20924.rho (k a i : ℕ) : ℕ := if i < k then i else if i = k then a else i - 1

def PEqualNP.Outside.L_meta_20924.ren (k a : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (rho k a)⟩

lemma PEqualNP.Outside.L_meta_20924.ren_wires (pre : List Gate) (g : Gate) (x : List Bool) (hx : x.length = 9) (a L : ℕ)
    (ha : (a < 9 + pre.length ∧ ev pre g x = (W pre x).getD a false) ∨
      (a = 9 + pre.length + L ∧ ev pre g x = false)) (post : List Gate) : post.length ≤ L →
    ∀ i, (W (pre ++ post.map (ren (9 + pre.length) a)) x).getD (rho (9 + pre.length) a i) false =
      (W (pre ++ g :: post) x).getD i false := by
  set k := 9 + pre.length with hk
  induction post using List.reverseRecOn with
  | nil =>
    intro _ i
    have h1 : W (pre ++ [g]) x = W pre x ++ [ev pre g x] := by rw [W_snoc]; rfl
    have hl : (W pre x).length = k := by rw [W_len, hx]
    simp only [List.map_nil, List.append_nil]
    rw [h1]
    rcases lt_trichotomy i k with h | h | h
    · rw [rho, ite_eq_left h, getD_lt _ _ _ (by omega)]
    · rw [rho, ite_eq_right (by omega), ite_eq_left h]
      have h2 := getD_len (W pre x) (ev pre g x)
      rw [hl] at h2
      rw [h, h2]
      rcases ha with ⟨_, h3⟩ | ⟨h3, h4⟩
      · exact h3.symm
      · rw [h4, getD_big _ _ (by omega)]
    · rw [rho, ite_eq_right (by omega), ite_eq_right (by omega), getD_big _ _ (by omega),
        getD_big _ _ (by simp; omega)]
  | append_singleton post h ih =>
    intro hL i
    simp only [List.length_append, List.length_singleton] at hL
    have IH := ih (by omega)
    set w0 := W (pre ++ g :: post) x with hw0
    set w1 := W (pre ++ post.map (ren k a)) x with hw1
    have l0 : w0.length = k + 1 + post.length := by rw [hw0, W_len, hx]; simp; omega
    have l1 : w1.length = k + post.length := by rw [hw1, W_len, hx]; simp; omega
    have e0 : W (pre ++ g :: (post ++ [h])) x = w0 ++ [ev (pre ++ g :: post) h x] := by
      rw [show pre ++ g :: (post ++ [h]) = (pre ++ g :: post) ++ [h] by simp, W_snoc]; rfl
    have e1 : W (pre ++ (post ++ [h]).map (ren k a)) x =
        w1 ++ [ev (pre ++ post.map (ren k a)) (ren k a h) x] := by
      rw [show pre ++ (post ++ [h]).map (ren k a) =
        (pre ++ post.map (ren k a)) ++ [ren k a h] by simp, W_snoc]; rfl
    have ee : ev (pre ++ post.map (ren k a)) (ren k a h) x = ev (pre ++ g :: post) h x := by
      unfold ev ren
      simp only [List.map_map]
      congr 1
      apply List.map_congr_left
      intro j _
      exact IH j
    rw [e0, e1, ee]
    rcases lt_trichotomy i w0.length with hi | hi | hi
    · rw [getD_lt _ _ _ hi, ← IH i]
      rcases lt_trichotomy i k with h' | h' | h'
      · rw [rho, ite_eq_left h', getD_lt _ _ _ (by omega)]
      · rw [rho, ite_eq_right (by omega), ite_eq_left h']
        rcases ha with ⟨h3, _⟩ | ⟨h3, _⟩
        · rw [getD_lt _ _ _ (by omega)]
        · rw [getD_big _ _ (by simp; omega), getD_big _ _ (by omega)]
      · rw [rho, ite_eq_right (by omega), ite_eq_right (by omega), getD_lt _ _ _ (by omega)]
    · have h2 := getD_len w0 (ev (pre ++ g :: post) h x)
      rw [hi, h2, rho, ite_eq_right (by omega), ite_eq_right (by omega)]
      have h3 := getD_len w1 (ev (pre ++ g :: post) h x)
      rw [show w0.length - 1 = w1.length by omega, h3]
    · rw [rho, ite_eq_right (by omega), ite_eq_right (by omega), getD_big _ _ (by simp; omega),
        getD_big _ _ (by simp; omega)]

lemma PEqualNP.Outside.L_meta_20924.min_circ (A : Fin 4 → Fin 5 → Bool) (s : ℕ) (h : RepSizeAtMost A s) :
    ∃ C : Circuit, (∀ g ∈ C.gates, Good g) ∧ C.gates.length ≤ s ∧ Represents A C ∧ Irr C.gates := by
  classical
  have hex : ∃ t, ∃ C : Circuit, (∀ g ∈ C.gates, Good g) ∧ C.gates.length = t ∧ Represents A C := by
    obtain ⟨C, hC, _, hr⟩ := h
    exact ⟨_, C, fun g hg => by simpa [Good] using hC g hg, rfl, hr⟩
  obtain ⟨C, hC, hlen, hrep⟩ := Nat.find_spec hex
  have hle : C.gates.length ≤ s := by
    obtain ⟨C', hC', hs, hr⟩ := h
    rw [hlen]
    exact (Nat.find_min' hex ⟨C', fun g hg => by simpa [Good] using hC' g hg, rfl, hr⟩).trans hs
  refine ⟨C, hC, hle, hrep, ?_⟩

  have key : ∀ pre g post, C.gates = pre ++ g :: post → ∀ a,
      (∀ p < 20, (a < 9 + pre.length ∧ ev pre g (X p) = (W pre (X p)).getD a false) ∨
        (a = 9 + pre.length + post.length ∧ ev pre g (X p) = false)) → False := by
    intro pre g post e a ha
    have hnew : ∃ C' : Circuit, (∀ g ∈ C'.gates, Good g) ∧
        C'.gates.length = C.gates.length - 1 ∧ Represents A C' := by
      refine ⟨⟨pre ++ post.map (ren (9 + pre.length) a), rho (9 + pre.length) a C.output⟩,
        ?_, ?_, ?_⟩
      · intro g' hg'
        rcases List.mem_append.mp hg' with h1 | h1
        · exact hC g' (by rw [e]; simp [h1])
        · obtain ⟨h2, h3, rfl⟩ := List.mem_map.mp h1
          have := hC h2 (by rw [e]; simp [h3])
          exact ⟨this.1, by simpa [ren] using this.2⟩
      · rw [e]; simp
      · intro u v
        have hp : 5 * (u : ℕ) + v < 20 := by omega
        have hX : X (5 * (u : ℕ) + v) = oneEach u v := by
          unfold X
          congr 1 <;> apply Fin.ext <;> simp <;> omega
        have h1 := ren_wires pre g (X (5 * (u : ℕ) + v)) (X_len _) a post.length (ha _ hp) post
          le_rfl C.output
        rw [← e, hX] at h1
        exact h1.trans (hrep u v)
    have := Nat.find_min' hex hnew
    have hpos : 0 < C.gates.length := by rw [e]; simp
    omega
  intro pre g post e
  refine ⟨fun a ha hall => key pre g post e a (fun p hp => Or.inl ⟨ha, hall p hp⟩),
    fun hall => key pre g post e _ (fun p hp => Or.inr ⟨rfl, hall p hp⟩)⟩

def PEqualNP.Outside.L_meta_20924.MM : ℕ := 39902

def PEqualNP.Outside.L_meta_20924.FULL : ℕ := 2 ^ 20 - 1

def PEqualNP.Outside.L_meta_20924.RO (ng : Bool) (lv : ℕ → ℕ) (K S m : ℕ) : Prop :=
  ∀ Q : ℕ → ℕ → Prop, (∀ i < K, Q (2 ^ i) (lv i)) →
    (∀ A B a b, (∀ i, A.testBit i = true → B.testBit i = false) → Q A a → Q B b →
      Q (A ||| B) (a &&& b) ∧ Q (A ||| B) (a ||| b)) →
    (ng = true → ∀ A a, Q A a → Q A (FULL ^^^ a)) → Q S m

lemma PEqualNP.Outside.L_meta_20924.RO_leaf (ng : Bool) (lv : ℕ → ℕ) (K i : ℕ) (h : i < K) : RO ng lv K (2 ^ i) (lv i) :=
  fun _ h1 _ _ => h1 i h

lemma PEqualNP.Outside.L_meta_20924.RO_and {ng : Bool} {lv : ℕ → ℕ} {K A B a b : ℕ}
    (h : ∀ i, A.testBit i = true → B.testBit i = false)
    (ha : RO ng lv K A a) (hb : RO ng lv K B b) : RO ng lv K (A ||| B) (a &&& b) :=
  fun Q h1 h2 h3 => (h2 A B a b h (ha Q h1 h2 h3) (hb Q h1 h2 h3)).1

lemma PEqualNP.Outside.L_meta_20924.RO_or {ng : Bool} {lv : ℕ → ℕ} {K A B a b : ℕ}
    (h : ∀ i, A.testBit i = true → B.testBit i = false)
    (ha : RO ng lv K A a) (hb : RO ng lv K B b) : RO ng lv K (A ||| B) (a ||| b) :=
  fun Q h1 h2 h3 => (h2 A B a b h (ha Q h1 h2 h3) (hb Q h1 h2 h3)).2

lemma PEqualNP.Outside.L_meta_20924.RO_not {lv : ℕ → ℕ} {K A a : ℕ} (ha : RO true lv K A a) : RO true lv K A (FULL ^^^ a) :=
  fun Q h1 h2 h3 => h3 rfl A a (ha Q h1 h2 h3)

lemma PEqualNP.Outside.L_meta_20924.RO_true {ng : Bool} {lv : ℕ → ℕ} {K A a : ℕ} (ha : RO ng lv K A a) : RO true lv K A a :=
  fun Q h1 h2 h3 => ha Q h1 h2 (fun _ => h3 rfl)

lemma PEqualNP.Outside.L_meta_20924.FULL_bit (p : ℕ) (hp : p < 20) (m : ℕ) : (FULL ^^^ m).testBit p = !m.testBit p := by
  rw [Nat.testBit_xor]
  have : FULL.testBit p = true := by
    unfold FULL; rw [Nat.testBit_two_pow_sub_one]; simpa using hp
  rw [this]; simp

def PEqualNP.Outside.L_meta_20924.ext (lv : ℕ → ℕ) (K z i : ℕ) : ℕ := if i < K then lv i else z

lemma PEqualNP.Outside.L_meta_20924.RO_lift (ng : Bool) (lv : ℕ → ℕ) (K z S m : ℕ) (h : RO ng lv K S m) :
    RO ng (ext lv K z) (K + 2) S m := by
  intro Q h1 h2 h3
  refine h Q (fun i hi => ?_) h2 h3
  have := h1 i (by omega)
  simpa [ext, hi] using this

def PEqualNP.Outside.L_meta_20924.Fam (ng : Bool) (lv : ℕ → ℕ) (K : ℕ) (D : ℕ → Prop) (I : Finset ℕ) (val : ℕ → ℕ → Bool) : Prop :=
  ∃ S m : ℕ → ℕ, (∀ w ∈ I, RO ng lv K (S w) (m w)) ∧
    (∀ w ∈ I, ∀ p < 20, (m w).testBit p = val w p) ∧
    (∀ w ∈ I, ∀ w' ∈ I, w ≠ w' → ∀ i, (S w).testBit i = true → (S w').testBit i = false) ∧
    (∀ i, (∃ w ∈ I, (S w).testBit i = true) ↔ D i)

def PEqualNP.Outside.L_meta_20924.Sh (ng : Bool) : ℕ → (ℕ → ℕ) → ℕ → (ℕ → Prop) → Finset ℕ → (ℕ → ℕ → Bool) → Prop
  | 0, lv, K, D, I, val => Fam ng lv K D I val
  | j + 1, lv, K, D, I, val => ∃ Sc mc : ℕ, RO ng lv K Sc mc ∧ (∀ i, Sc.testBit i = true → D i) ∧
      Sh ng j (ext lv K mc) (K + 2) (fun i => (D i ∧ Sc.testBit i = false) ∨ i = K ∨ i = K + 1) I val

lemma PEqualNP.Outside.L_meta_20924.Sh_map (ng : Bool) (I I' : Finset ℕ) (val val' : ℕ → ℕ → Bool)
    (h : ∀ lv K D, Fam ng lv K D I val → Fam ng lv K D I' val') :
    ∀ j lv K D, Sh ng j lv K D I val → Sh ng j lv K D I' val' := by
  intro j
  induction j with
  | zero => exact h
  | succ j ih =>
    rintro lv K D ⟨Sc, mc, h1, h2, h3⟩
    exact ⟨Sc, mc, h1, h2, ih _ _ _ h3⟩

lemma PEqualNP.Outside.L_meta_20924.Fam_true (ng : Bool) (lv : ℕ → ℕ) (K : ℕ) (D : ℕ → Prop) (I : Finset ℕ)
    (val : ℕ → ℕ → Bool) (h : Fam ng lv K D I val) : Fam true lv K D I val := by
  obtain ⟨S, m, h1, h2⟩ := h
  exact ⟨S, m, fun w hw => RO_true (h1 w hw), h2⟩

lemma PEqualNP.Outside.L_meta_20924.Sh_true (ng : Bool) (I : Finset ℕ) (val : ℕ → ℕ → Bool) :
    ∀ j lv K D, Sh ng j lv K D I val → Sh true j lv K D I val := by
  intro j
  induction j with
  | zero => exact fun lv K D h => Fam_true ng lv K D I val h
  | succ j ih =>
    rintro lv K D ⟨Sc, mc, h1, h2, h3⟩
    exact ⟨Sc, mc, RO_true h1, h2, ih _ _ _ h3⟩

lemma PEqualNP.Outside.L_meta_20924.Fam_not (I : Finset ℕ) (val : ℕ → ℕ → Bool) (a e : ℕ) (ha : a ∈ I) (he : e ∉ I.erase a)
    (hv : ∀ p < 20, val e p = !val a p) (lv : ℕ → ℕ) (K : ℕ) (D : ℕ → Prop)
    (hF : Fam true lv K D I val) : Fam true lv K D (insert e (I.erase a)) val := by
  obtain ⟨S, m, hRO, hval, hdis, hun⟩ := hF
  have hR : ∀ w ∈ I.erase a, w ≠ e ∧ w ≠ a ∧ w ∈ I := by
    intro w hw
    have h1 := Finset.mem_erase.mp hw
    exact ⟨fun h => he (h ▸ hw), h1.1, h1.2⟩
  refine ⟨fun w => if w = e then S a else S w, fun w => if w = e then FULL ^^^ m a else m w,
    ?_, ?_, ?_, ?_⟩
  · intro w hw
    rcases Finset.mem_insert.mp hw with h | h
    · simp only [h, ↓reduceIte]; exact RO_not (hRO a ha)
    · simp only [(hR w h).1, ↓reduceIte]; exact hRO w (hR w h).2.2
  · intro w hw p hp
    rcases Finset.mem_insert.mp hw with h | h
    · simp only [h, ↓reduceIte]
      rw [FULL_bit p hp, hval a ha p hp, hv p hp]
    · simp only [(hR w h).1, ↓reduceIte]; exact hval w (hR w h).2.2 p hp
  · intro w hw w' hw' hww i hi
    rcases Finset.mem_insert.mp hw with h | h
    · rcases Finset.mem_insert.mp hw' with h' | h'
      · exact absurd (h.trans h'.symm) hww
      · obtain ⟨e1, e2, e3⟩ := hR w' h'
        simp only [h, ↓reduceIte] at hi
        simp only [e1, ↓reduceIte]
        exact hdis a ha w' e3 e2.symm i hi
    · obtain ⟨e1, e2, e3⟩ := hR w h
      simp only [e1, ↓reduceIte] at hi
      rcases Finset.mem_insert.mp hw' with h' | h'
      · simp only [h', ↓reduceIte]
        exact hdis w e3 a ha e2 i hi
      · obtain ⟨e1', e2', e3'⟩ := hR w' h'
        simp only [e1', ↓reduceIte]
        exact hdis w e3 w' e3' hww i hi
  · intro i
    rw [← hun i]
    constructor
    · rintro ⟨w, hw, hb'⟩
      rcases Finset.mem_insert.mp hw with h | h
      · simp only [h, ↓reduceIte] at hb'
        exact ⟨a, ha, hb'⟩
      · simp only [(hR w h).1, ↓reduceIte] at hb'
        exact ⟨w, (hR w h).2.2, hb'⟩
    · rintro ⟨w, hw, hb'⟩
      by_cases h1 : w = a
      · refine ⟨e, Finset.mem_insert_self _ _, ?_⟩
        simp only [↓reduceIte]; rw [← h1]; exact hb'
      · have hw' : w ∈ I.erase a := Finset.mem_erase.mpr ⟨h1, hw⟩
        refine ⟨w, Finset.mem_insert_of_mem hw', ?_⟩
        simp only [(hR w hw').1, ↓reduceIte]; exact hb'

lemma PEqualNP.Outside.L_meta_20924.Fam_congr (ng : Bool) (I : Finset ℕ) (val val' : ℕ → ℕ → Bool)
    (h : ∀ w ∈ I, ∀ p < 20, val w p = val' w p) (lv : ℕ → ℕ) (K : ℕ) (D : ℕ → Prop)
    (hF : Fam ng lv K D I val) : Fam ng lv K D I val' := by
  obtain ⟨S, m, h1, h2, h3, h4⟩ := hF
  exact ⟨S, m, h1, fun w hw p hp => by rw [h2 w hw p hp, h w hw p hp], h3, h4⟩

lemma PEqualNP.Outside.L_meta_20924.Fam_bin (ng : Bool) (I : Finset ℕ) (val : ℕ → ℕ → Bool) (a b e : ℕ) (ha : a ∈ I) (hb : b ∈ I)
    (hab : a ≠ b) (he : e ∉ (I.erase a).erase b)
    (hv : (∀ p < 20, val e p = (val a p && val b p)) ∨ (∀ p < 20, val e p = (val a p || val b p)))
    (lv : ℕ → ℕ) (K : ℕ) (D : ℕ → Prop) (hF : Fam ng lv K D I val) :
    Fam ng lv K D (insert e ((I.erase a).erase b)) val := by
  obtain ⟨S, m, hRO, hval, hdis, hun⟩ := hF
  have hSab := hdis a ha b hb hab
  obtain ⟨mk, hmk1, hmk2⟩ : ∃ mk, RO ng lv K (S a ||| S b) mk ∧ ∀ p < 20,
      mk.testBit p = val e p := by
    rcases hv with hv | hv
    · exact ⟨_, RO_and hSab (hRO a ha) (hRO b hb), fun p hp => by
        rw [hv p hp, Nat.testBit_and, hval a ha p hp, hval b hb p hp]⟩
    · exact ⟨_, RO_or hSab (hRO a ha) (hRO b hb), fun p hp => by
        rw [hv p hp, Nat.testBit_or, hval a ha p hp, hval b hb p hp]⟩
  have hR : ∀ w ∈ (I.erase a).erase b, w ≠ e ∧ w ≠ a ∧ w ≠ b ∧ w ∈ I := by
    intro w hw
    have h1 := Finset.mem_erase.mp hw
    have h2 := Finset.mem_erase.mp h1.2
    exact ⟨fun h => he (h ▸ hw), h2.1, h1.1, h2.2⟩
  refine ⟨fun w => if w = e then S a ||| S b else S w, fun w => if w = e then mk else m w,
    ?_, ?_, ?_, ?_⟩
  · intro w hw
    rcases Finset.mem_insert.mp hw with h | h
    · simp only [h, ↓reduceIte]; exact hmk1
    · simp only [(hR w h).1, ↓reduceIte]; exact hRO w (hR w h).2.2.2
  · intro w hw p hp
    rcases Finset.mem_insert.mp hw with h | h
    · simp only [h, ↓reduceIte]; exact hmk2 p hp
    · simp only [(hR w h).1, ↓reduceIte]; exact hval w (hR w h).2.2.2 p hp
  · intro w hw w' hw' hww i hi
    rcases Finset.mem_insert.mp hw with h | h
    · rcases Finset.mem_insert.mp hw' with h' | h'
      · exact absurd (h.trans h'.symm) hww
      · obtain ⟨e1, e2, e3, e4⟩ := hR w' h'
        simp only [h, ↓reduceIte, Nat.testBit_or, Bool.or_eq_true] at hi
        simp only [e1, ↓reduceIte]
        rcases hi with hi | hi
        · exact hdis a ha w' e4 e2.symm i hi
        · exact hdis b hb w' e4 e3.symm i hi
    · obtain ⟨e1, e2, e3, e4⟩ := hR w h
      simp only [e1, ↓reduceIte] at hi
      rcases Finset.mem_insert.mp hw' with h' | h'
      · simp only [h', ↓reduceIte, Nat.testBit_or, Bool.or_eq_false_iff]
        exact ⟨hdis w e4 a ha e2 i hi, hdis w e4 b hb e3 i hi⟩
      · obtain ⟨e1', e2', e3', e4'⟩ := hR w' h'
        simp only [e1', ↓reduceIte]
        exact hdis w e4 w' e4' hww i hi
  · intro i
    rw [← hun i]
    constructor
    · rintro ⟨w, hw, hb'⟩
      rcases Finset.mem_insert.mp hw with h | h
      · simp only [h, ↓reduceIte, Nat.testBit_or, Bool.or_eq_true] at hb'
        rcases hb' with hb' | hb'
        · exact ⟨a, ha, hb'⟩
        · exact ⟨b, hb, hb'⟩
      · simp only [(hR w h).1, ↓reduceIte] at hb'
        exact ⟨w, (hR w h).2.2.2, hb'⟩
    · rintro ⟨w, hw, hb'⟩
      by_cases h1 : w = a ∨ w = b
      · refine ⟨e, Finset.mem_insert_self _ _, ?_⟩
        simp only [↓reduceIte, Nat.testBit_or, Bool.or_eq_true]
        rcases h1 with rfl | rfl
        · exact Or.inl hb'
        · exact Or.inr hb'
      · rw [not_or] at h1
        have hw' : w ∈ (I.erase a).erase b :=
          Finset.mem_erase.mpr ⟨h1.2, Finset.mem_erase.mpr ⟨h1.1, hw⟩⟩
        refine ⟨w, Finset.mem_insert_of_mem hw', ?_⟩
        simp only [(hR w hw').1, ↓reduceIte]; exact hb'

lemma PEqualNP.Outside.L_meta_20924.Fam_dup (ng : Bool) (I : Finset ℕ) (val : ℕ → ℕ → Bool) (a e : ℕ) (ha : a ∈ I) (he : e ∉ I)
    (hv : ∀ p < 20, val e p = val a p) (lv : ℕ → ℕ) (K : ℕ) (D : ℕ → Prop)
    (hDK : ∀ i, D i → i < K) (hF : Fam ng lv K D I val) : Sh ng 1 lv K D (insert e I) val := by
  obtain ⟨S, m, hRO, hval, hdis, hun⟩ := hF
  have hlt : ∀ w ∈ I, ∀ i, (S w).testBit i = true → i < K := fun w hw i hi =>
    hDK i ((hun i).mp ⟨w, hw, hi⟩)
  refine ⟨S a, m a, hRO a ha, fun i hi => (hun i).mp ⟨a, ha, hi⟩, ?_⟩
  have hRK : RO ng (ext lv K (m a)) (K + 2) (2 ^ K) (m a) := by
    have := RO_leaf ng (ext lv K (m a)) (K + 2) K (by omega)
    simpa [ext] using this
  have hRK1 : RO ng (ext lv K (m a)) (K + 2) (2 ^ (K + 1)) (m a) := by
    have := RO_leaf ng (ext lv K (m a)) (K + 2) (K + 1) (by omega)
    simpa [ext] using this
  have hb0 : ∀ i, (2 ^ K : ℕ).testBit i = true ↔ i = K := by
    intro i; rw [Nat.testBit_two_pow]; simp [eq_comm]
  have hb1 : ∀ i, (2 ^ (K + 1) : ℕ).testBit i = true ↔ i = K + 1 := by
    intro i; rw [Nat.testBit_two_pow]; simp [eq_comm]
  have hea : e ≠ a := fun h => he (h ▸ ha)
  set SS : ℕ → ℕ := fun w => if w = e then 2 ^ (K + 1) else if w = a then 2 ^ K else S w with hSS
  have eE : SS e = 2 ^ (K + 1) := by simp [hSS]
  have eA : SS a = 2 ^ K := by simp [hSS, hea.symm]
  have eO : ∀ w, w ≠ e → w ≠ a → SS w = S w := fun w h1 h2 => by simp [hSS, h1, h2]
  have key : ∀ w ∈ insert e I, ∀ i, (SS w).testBit i = true →
      (w = e ∧ i = K + 1) ∨ (w = a ∧ i = K) ∨ (w ≠ e ∧ w ≠ a ∧ w ∈ I ∧ (S w).testBit i = true) := by
    intro w hw i hi
    by_cases h1 : w = e
    · rw [h1, eE, hb1] at hi; exact Or.inl ⟨h1, hi⟩
    · by_cases h2 : w = a
      · rw [h2, eA, hb0] at hi; exact Or.inr (Or.inl ⟨h2, hi⟩)
      · rw [eO w h1 h2] at hi
        exact Or.inr (Or.inr ⟨h1, h2, (Finset.mem_insert.mp hw).resolve_left h1, hi⟩)
  refine ⟨SS, fun w => if w = e then m a else m w, ?_, ?_, ?_, ?_⟩
  · intro w hw
    by_cases h1 : w = e
    · rw [h1, eE]; simp only [↓reduceIte]; exact hRK1
    · simp only [h1, ↓reduceIte]
      by_cases h2 : w = a
      · rw [h2, eA]; exact hRK
      · rw [eO w h1 h2]
        exact RO_lift _ _ _ _ _ _ (hRO w ((Finset.mem_insert.mp hw).resolve_left h1))
  · intro w hw p hp
    by_cases h1 : w = e
    · simp only [h1, ↓reduceIte]; rw [hv p hp]; exact hval a ha p hp
    · simp only [h1, ↓reduceIte]
      exact hval w ((Finset.mem_insert.mp hw).resolve_left h1) p hp
  · intro w hw w' hw' hww i hi
    by_contra hne
    have k1 := key w hw i hi
    have k2 := key w' hw' i (by simpa using hne)
    rcases k1 with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2, e3, e4⟩
    · rcases k2 with ⟨f1, f2⟩ | ⟨f1, f2⟩ | ⟨f1, f2, f3, f4⟩
      · exact hww (e1.trans f1.symm)
      · omega
      · have := hlt w' f3 i f4; omega
    · rcases k2 with ⟨f1, f2⟩ | ⟨f1, f2⟩ | ⟨f1, f2, f3, f4⟩
      · omega
      · exact hww (e1.trans f1.symm)
      · have := hlt w' f3 i f4; omega
    · rcases k2 with ⟨f1, f2⟩ | ⟨f1, f2⟩ | ⟨f1, f2, f3, f4⟩
      · have := hlt w e3 i e4; omega
      · have := hlt w e3 i e4; omega
      · have := hdis w e3 w' f3 hww i e4
        rw [this] at f4; exact absurd f4 (by simp)
  · intro i
    constructor
    · rintro ⟨w, hw, hi⟩
      rcases key w hw i hi with ⟨_, e2⟩ | ⟨_, e2⟩ | ⟨e1, e2, e3, e4⟩
      · exact Or.inr (Or.inr e2)
      · exact Or.inr (Or.inl e2)
      · exact Or.inl ⟨(hun i).mp ⟨w, e3, e4⟩, hdis w e3 a ha e2 i e4⟩
    · rintro (⟨hiD, hia⟩ | rfl | rfl)
      · obtain ⟨w, hw, hi⟩ := (hun i).mpr hiD
        have h2 : w ≠ a := by
          rintro rfl; rw [hi] at hia; exact absurd hia (by simp)
        have h1 : w ≠ e := fun h => he (h ▸ hw)
        exact ⟨w, Finset.mem_insert_of_mem hw, by rw [eO w h1 h2]; exact hi⟩
      · exact ⟨a, Finset.mem_insert_of_mem ha, by rw [eA, hb0]⟩
      · exact ⟨e, Finset.mem_insert_self _ _, by rw [eE, hb1]⟩

lemma PEqualNP.Outside.L_meta_20924.Sh_dup (ng : Bool) (I : Finset ℕ) (val : ℕ → ℕ → Bool) (a e : ℕ) (ha : a ∈ I) (he : e ∉ I)
    (hv : ∀ p < 20, val e p = val a p) : ∀ j lv K (D : ℕ → Prop), (∀ i, D i → i < K) →
    Sh ng j lv K D I val → Sh ng (j + 1) lv K D (insert e I) val := by
  intro j
  induction j with
  | zero => intro lv K D hDK h; exact Fam_dup ng I val a e ha he hv lv K D hDK h
  | succ j ih =>
    rintro lv K D hDK ⟨Sc, mc, h1, h2, h3⟩
    refine ⟨Sc, mc, h1, h2, ih _ _ _ ?_ h3⟩
    rintro i (⟨h, _⟩ | h | h)
    · have := hDK i h; omega
    · omega
    · omega

def PEqualNP.Outside.L_meta_20924.Det (gs : List Gate) (pend D : Finset ℕ) : Prop :=
  ∀ x y : List Bool, x.length = 9 → y.length = 9 →
    (∀ i ∈ D, x.getD i false = y.getD i false) →
    ∀ w ∈ pend, (W gs x).getD w false = (W gs y).getD w false

def PEqualNP.Outside.L_meta_20924.vl (gs : List Gate) (w p : ℕ) : Bool := (W gs (X p)).getD w false

lemma PEqualNP.Outside.L_meta_20924.main (gs : List Gate) : (∀ g ∈ gs, Good g) → Irr gs → ∀ pend : Finset ℕ,
    (∀ w ∈ pend, w < 9 + gs.length) → (∀ w ∈ pend, ∃ p < 20, vl gs w p = false) →
    ∃ D : Finset ℕ, D ⊆ Finset.range 9 ∧ Det gs pend D ∧
      ∃ j, D.card + j ≤ pend.card + gs.length ∧ Sh false j lf 9 (· ∈ D) pend (vl gs) := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ _ pend hp _
    refine ⟨pend, fun w hw => by simpa using hp w hw, fun x y _ _ h w hw => by
      simpa [W] using h w hw, 0, by simp, fun w => 2 ^ w, lf,
      fun w hw => RO_leaf false lf 9 w (by simpa using hp w hw),
      fun w hw p hpp => by simpa [W, vl] using lf_X w (by simpa using hp w hw) p hpp,
      fun w hw w' hw' hne i hi => ?_, fun i => ?_⟩
    · rw [Nat.testBit_two_pow] at hi ⊢
      have : w = i := by simpa using hi
      simp only [decide_eq_false_iff_not]
      omega
    · simp [Nat.testBit_two_pow]
  | append_singleton gs g ih =>
    intro hg hirr pend hp hnt
    have hg' : ∀ g ∈ gs, Good g := fun g' h => hg g' (by simp [h])
    have hgg : Good g := hg g (by simp)
    have hlen : (gs ++ [g]).length = gs.length + 1 := by simp
    have IH := ih hg' (Irr_prefix gs g hirr)
    have hI := hirr gs g [] rfl
    set k := 9 + gs.length with hk
    have hlo : ∀ x : List Bool, x.length = 9 → ∀ w, w < k →
        (W (gs ++ [g]) x).getD w false = (W gs x).getD w false := by
      intro x hx w hw
      rw [W_snoc, stp, getD_lt _ _ _ (by rw [W_len, hx]; exact hw)]
    have hto : ∀ x : List Bool, x.length = 9 →
        (W (gs ++ [g]) x).getD k false = ev gs g x := by
      intro x hx
      have h := getD_len (W gs x) (ev gs g x)
      rw [W_len, hx] at h
      rw [W_snoc]; exact h
    have hvlo : ∀ w, w < k → ∀ p, vl (gs ++ [g]) w p = vl gs w p := fun w hw p =>
      hlo _ (X_len p) w hw
    have hvto : ∀ p, vl (gs ++ [g]) k p = ev gs g (X p) := fun p => hto _ (X_len p)
    have hpk : ∀ w ∈ pend, w ≠ k → w < k := by
      intro w hw hwk
      have h1 := hp w hw
      rw [hlen] at h1; omega
    have hbig : ∀ x : List Bool, x.length = 9 → ∀ i, k ≤ i → (W gs x).getD i false = false := by
      intro x hx i hi
      exact getD_big _ _ (by rw [W_len, hx]; omega)
    by_cases hkp : k ∈ pend
    swap
    · have hp' : ∀ w ∈ pend, w < k := fun w hw => hpk w hw (fun h => hkp (h ▸ hw))
      obtain ⟨D, h1, h2, j, h3, h4⟩ := IH pend hp' (fun w hw => by
        obtain ⟨p, hpp, h⟩ := hnt w hw
        exact ⟨p, hpp, by rw [← hvlo w (hp' w hw) p]; exact h⟩)
      refine ⟨D, h1, ?_, j, by rw [hlen]; omega, ?_⟩
      · intro x y hx hy hxy w hw
        rw [hlo x hx w (hp' w hw), hlo y hy w (hp' w hw)]
        exact h2 x y hx hy hxy w hw
      · exact Sh_map false _ _ _ _ (Fam_congr false pend _ _ fun w hw p _ => (hvlo w (hp' w hw) p).symm)
          _ _ _ _ h4
    ·
      obtain ⟨a, b, hak, hbk, hab, hev⟩ : ∃ a b, a < k ∧ b < k ∧ a ≠ b ∧
          ((∀ x : List Bool, x.length = 9 → ev gs g x = ((W gs x).getD a false && (W gs x).getD b false)) ∨
           (∀ x : List Bool, x.length = 9 → ev gs g x = ((W gs x).getD a false || (W gs x).getD b false))) := by
        have hcopy : ∀ a < k, (∀ x : List Bool, x.length = 9 → ev gs g x = (W gs x).getD a false) →
            False := fun a ha h => hI.1 a ha (fun p _ => h _ (X_len p))
        have hfalse : (∀ x : List Bool, x.length = 9 → ev gs g x = false) → False :=
          fun h => hI.2 (fun p _ => h _ (X_len p))
        have hl2 := hgg.2
        rcases hins : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨t, l⟩⟩⟩
        · exfalso
          rcases hgg.1 with ho | ho
          · obtain ⟨p, _, h⟩ := hnt k hkp
            rw [hvto p] at h
            simp [ev, hins, ho, GateOp.eval] at h
          · apply hfalse; intro x _
            simp [ev, hins, ho, GateOp.eval]
        · exfalso
          have he : ∀ x, ev gs g x = (W gs x).getD a false := by
            intro x
            rcases hgg.1 with ho | ho <;> simp [ev, hins, ho, GateOp.eval]
          by_cases hak : a < k
          · exact hcopy a hak (fun x _ => he x)
          · exact hfalse (fun x hx => by rw [he x, hbig x hx a (by omega)])
        · rcases hgg.1 with ho | ho
          · have he : ∀ x, ev gs g x = ((W gs x).getD a false && (W gs x).getD b false) := by
              intro x; simp [ev, hins, ho, GateOp.eval]
            by_cases hak : a < k
            · by_cases hbk : b < k
              · by_cases hab : a = b
                · exact (hcopy b hbk fun x _ => by rw [he x, hab, Bool.and_self]).elim
                · exact ⟨a, b, hak, hbk, hab, Or.inl fun x _ => he x⟩
              · exact (hfalse fun x hx => by
                  rw [he x, hbig x hx b (by omega), Bool.and_false]).elim
            · exact (hfalse fun x hx => by
                rw [he x, hbig x hx a (by omega), Bool.false_and]).elim
          · have he : ∀ x, ev gs g x = ((W gs x).getD a false || (W gs x).getD b false) := by
              intro x; simp [ev, hins, ho, GateOp.eval]
            by_cases hak : a < k
            · by_cases hbk : b < k
              · by_cases hab : a = b
                · exact (hcopy b hbk fun x _ => by rw [he x, hab, Bool.or_self]).elim
                · exact ⟨a, b, hak, hbk, hab, Or.inr fun x _ => he x⟩
              · exact (hcopy a hak fun x hx => by
                  rw [he x, hbig x hx b (by omega), Bool.or_false]).elim
            · by_cases hbk : b < k
              · exact (hcopy b hbk fun x hx => by
                  rw [he x, hbig x hx a (by omega), Bool.false_or]).elim
              · exact (hfalse fun x hx => by
                  rw [he x, hbig x hx a (by omega), hbig x hx b (by omega)]; rfl).elim
        · rw [hins] at hl2; simp at hl2

      obtain ⟨p0, hp0, hk0⟩ := hnt k hkp
      rw [hvto p0] at hk0
      have hant : (∃ p < 20, vl gs a p = false) ∧ (∃ p < 20, vl gs b p = false) := by
        rcases hev with hev | hev
        · constructor
          · by_contra hne
            push_neg at hne
            exact hI.1 b hbk fun p hpp => by
              have h1 := hne p hpp
              rw [hev _ (X_len p)]
              have h2 : (W gs (X p)).getD a false = true := by simpa [vl] using h1
              rw [h2, Bool.true_and]
          · by_contra hne
            push_neg at hne
            exact hI.1 a hak fun p hpp => by
              have h1 := hne p hpp
              rw [hev _ (X_len p)]
              have h2 : (W gs (X p)).getD b false = true := by simpa [vl] using h1
              rw [h2, Bool.and_true]
        · rw [hev _ (X_len p0), Bool.or_eq_false_iff] at hk0
          exact ⟨⟨p0, hp0, hk0.1⟩, ⟨p0, hp0, hk0.2⟩⟩
      set E := pend.erase k with hE
      have hEc : E.card + 1 = pend.card := Finset.card_erase_add_one hkp
      have hElt : ∀ w ∈ E, w < k := fun w hw =>
        hpk w (Finset.mem_of_mem_erase hw) (Finset.ne_of_mem_erase hw)
      have hEnt : ∀ w ∈ E, ∃ p < 20, vl gs w p = false := by
        intro w hw
        obtain ⟨p, hpp, h⟩ := hnt w (Finset.mem_of_mem_erase hw)
        exact ⟨p, hpp, by rw [← hvlo w (hElt w hw) p]; exact h⟩
      have hpE : pend = insert k E := (Finset.insert_erase hkp).symm

      have hdet : ∀ (P : Finset ℕ) D, (∀ w ∈ E, w ∈ P) → a ∈ P → b ∈ P → Det gs P D →
          Det (gs ++ [g]) pend D := by
        intro P D hEP haP hbP hD x y hx hy hxy w hw
        by_cases hwk : w = k
        · rw [hwk, hto x hx, hto y hy]
          have h1 := hD x y hx hy hxy a haP
          have h2 := hD x y hx hy hxy b hbP
          rcases hev with hev | hev <;> rw [hev x hx, hev y hy, h1, h2]
        · have hwe : w ∈ E := Finset.mem_erase.mpr ⟨hwk, hw⟩
          rw [hlo x hx w (hElt w hwe), hlo y hy w (hElt w hwe)]
          exact hD x y hx hy hxy w (hEP w hwe)
      set v' : ℕ → ℕ → Bool := fun w p => if w = k + 1 then vl gs a p else
        if w = k + 2 then vl gs b p else vl (gs ++ [g]) w p with hv'
      have v'1 : ∀ p, v' (k + 1) p = vl gs a p := fun p => by simp [hv']
      have v'2 : ∀ p, v' (k + 2) p = vl gs b p := fun p => by simp [hv']
      have v'k : ∀ p, v' k p = ev gs g (X p) := fun p => by
        simp only [hv']
        rw [ite_eq_right (by omega), ite_eq_right (by omega), hvto p]
      have v'l : ∀ w, w < k → ∀ p, v' w p = vl gs w p := fun w hw p => by
        simp only [hv']
        rw [ite_eq_right (by omega), ite_eq_right (by omega), hvlo w hw p]
      have hstart : ∀ (P : Finset ℕ) D j, (∀ w ∈ P, w < k) → Sh false j lf 9 D P (vl gs) →
          Sh false j lf 9 D P v' := fun P D j hP h =>
        Sh_map false _ _ _ _ (Fam_congr false P _ _ fun w hw p _ => (v'l w (hP w hw) p).symm) _ _ _ _ h
      have hend : ∀ D j, Sh false j lf 9 D (insert k E) v' → Sh false j lf 9 D pend (vl (gs ++ [g])) := by
        intro D j h
        rw [hpE]
        refine Sh_map false _ _ _ _ (Fam_congr false _ _ _ fun w hw p _ => ?_) _ _ _ _ h
        rcases Finset.mem_insert.mp hw with rfl | hw
        · rw [v'k, hvto]
        · rw [v'l w (hElt w hw), hvlo w (hElt w hw)]
      have hcomb : ∀ (P : Finset ℕ) D j c d, c ∈ P → d ∈ P → c ≠ d → (P.erase c).erase d = E →
          (∀ p, v' c p = vl gs a p) → (∀ p, v' d p = vl gs b p) → Sh false j lf 9 D P v' →
          Sh false j lf 9 D pend (vl (gs ++ [g])) := by
        intro P D j c d hc hd hcd hPE hvc hvd h
        apply hend
        rw [← hPE]
        refine Sh_map false _ _ _ _ (Fam_bin false P v' c d k hc hd hcd ?_ ?_) _ _ _ _ h
        · rw [hPE]; exact Finset.notMem_erase _ _
        · rcases hev with hev | hev
          · left; intro p _
            rw [v'k, hvc, hvd, hev _ (X_len p)]; rfl
          · right; intro p _
            rw [v'k, hvc, hvd, hev _ (X_len p)]; rfl
      have hD8 : ∀ D : Finset ℕ, D ⊆ Finset.range 9 → ∀ i, i ∈ D → i < 9 := fun D hD i hi => by
        simpa using hD hi
      have hk1E : k + 1 ∉ E := fun h => by have := hElt _ h; omega
      have hk2E : k + 2 ∉ E := fun h => by have := hElt _ h; omega
      by_cases haE : a ∈ E
      · by_cases hbE : b ∈ E
        ·
          obtain ⟨D, h1, h2, j, h3, h4⟩ := IH E hElt hEnt
          refine ⟨D, h1, hdet E D (fun w hw => hw) haE hbE h2, j + 2, by rw [hlen]; omega, ?_⟩
          have s1 := hstart E _ j hElt h4
          have s2 := Sh_dup false E v' a (k + 1) haE hk1E (fun p _ => by rw [v'1, v'l a hak]) j lf 9 _
            (hD8 D h1) s1
          have s3 := Sh_dup false (insert (k + 1) E) v' b (k + 2) (Finset.mem_insert_of_mem hbE)
            (by simp [hk2E]) (fun p _ => by rw [v'2, v'l b hbk]) (j + 1) lf 9 _ (hD8 D h1) s2
          refine hcomb (insert (k + 2) (insert (k + 1) E)) _ _ (k + 1) (k + 2) (by simp) (by simp)
            (by omega) ?_ v'1 v'2 s3
          ext w
          simp only [Finset.mem_erase, Finset.mem_insert]
          constructor
          · rintro ⟨n2, n1, h | h | h⟩
            · exact absurd h n2
            · exact absurd h n1
            · exact h
          · intro h
            have := hElt w h
            exact ⟨by omega, by omega, Or.inr (Or.inr h)⟩
        ·
          have hP : ∀ w ∈ insert b E, w < k := by
            intro w hw
            rcases Finset.mem_insert.mp hw with rfl | hw
            · exact hbk
            · exact hElt w hw
          obtain ⟨D, h1, h2, j, h3, h4⟩ := IH (insert b E) hP (by
            intro w hw
            rcases Finset.mem_insert.mp hw with rfl | hw
            · exact hant.2
            · exact hEnt w hw)
          rw [Finset.card_insert_of_notMem hbE] at h3
          refine ⟨D, h1, hdet (insert b E) D (fun w hw => Finset.mem_insert_of_mem hw)
            (Finset.mem_insert_of_mem haE) (Finset.mem_insert_self _ _) h2, j + 1,
            by rw [hlen]; omega, ?_⟩
          have s1 := hstart (insert b E) _ j hP h4
          have s2 := Sh_dup false (insert b E) v' a (k + 1) (Finset.mem_insert_of_mem haE)
            (by rw [Finset.mem_insert, not_or]; exact ⟨by omega, hk1E⟩)
            (fun p _ => by rw [v'1, v'l a hak]) j lf 9 _ (hD8 D h1) s1
          refine hcomb (insert (k + 1) (insert b E)) _ _ (k + 1) b (by simp) (by simp)
            (by omega) ?_ v'1 (v'l b hbk) s2
          ext w
          simp only [Finset.mem_erase, Finset.mem_insert]
          constructor
          · rintro ⟨n2, n1, h | h | h⟩
            · exact absurd h n1
            · exact absurd h n2
            · exact h
          · intro h
            have := hElt w h
            exact ⟨fun h' => hbE (h' ▸ h), by omega, Or.inr (Or.inr h)⟩
      · have hP : ∀ w ∈ insert a E, w < k := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · exact hak
          · exact hElt w hw
        by_cases hbE : b ∈ E
        ·
          obtain ⟨D, h1, h2, j, h3, h4⟩ := IH (insert a E) hP (by
            intro w hw
            rcases Finset.mem_insert.mp hw with rfl | hw
            · exact hant.1
            · exact hEnt w hw)
          rw [Finset.card_insert_of_notMem haE] at h3
          refine ⟨D, h1, hdet (insert a E) D (fun w hw => Finset.mem_insert_of_mem hw)
            (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hbE) h2, j + 1,
            by rw [hlen]; omega, ?_⟩
          have s1 := hstart (insert a E) _ j hP h4
          have s2 := Sh_dup false (insert a E) v' b (k + 2) (Finset.mem_insert_of_mem hbE)
            (by rw [Finset.mem_insert, not_or]; exact ⟨by omega, hk2E⟩)
            (fun p _ => by rw [v'2, v'l b hbk]) j lf 9 _ (hD8 D h1) s1
          refine hcomb (insert (k + 2) (insert a E)) _ _ a (k + 2) (by simp) (by simp)
            (by omega) ?_ (v'l a hak) v'2 s2
          ext w
          simp only [Finset.mem_erase, Finset.mem_insert]
          constructor
          · rintro ⟨n2, n1, h | h | h⟩
            · exact absurd h n2
            · exact absurd h n1
            · exact h
          · intro h
            have := hElt w h
            exact ⟨by omega, fun h' => haE (h' ▸ h), Or.inr (Or.inr h)⟩
        ·
          have hbaE : b ∉ insert a E := by
            rw [Finset.mem_insert, not_or]; exact ⟨fun h => hab h.symm, hbE⟩
          have hP2 : ∀ w ∈ insert b (insert a E), w < k := by
            intro w hw
            rcases Finset.mem_insert.mp hw with rfl | hw
            · exact hbk
            · exact hP w hw
          obtain ⟨D, h1, h2, j, h3, h4⟩ := IH (insert b (insert a E)) hP2 (by
            intro w hw
            rcases Finset.mem_insert.mp hw with rfl | hw
            · exact hant.2
            · rcases Finset.mem_insert.mp hw with rfl | hw
              · exact hant.1
              · exact hEnt w hw)
          rw [Finset.card_insert_of_notMem hbaE, Finset.card_insert_of_notMem haE] at h3
          refine ⟨D, h1, hdet _ D (fun w hw => Finset.mem_insert_of_mem
            (Finset.mem_insert_of_mem hw)) (by simp) (by simp) h2, j, by rw [hlen]; omega, ?_⟩
          have s1 := hstart _ _ j hP2 h4
          refine hcomb (insert b (insert a E)) _ _ a b (by simp) (by simp) hab ?_ (v'l a hak)
            (v'l b hbk) s1
          ext w
          simp only [Finset.mem_erase, Finset.mem_insert]
          constructor
          · rintro ⟨n2, n1, h | h | h⟩
            · exact absurd h n2
            · exact absurd h n1
            · exact h
          · intro h
            exact ⟨fun h' => hbE (h' ▸ h), fun h' => haE (h' ▸ h), Or.inr (Or.inr h)⟩

lemma PEqualNP.Outside.L_meta_20924.mono (gs : List Gate) : (∀ g ∈ gs, Good g) → ∀ x y : List Bool, x.length = y.length →
    (∀ i, x.getD i false = true → y.getD i false = true) →
    ∀ i, (W gs x).getD i false = true → (W gs y).getD i false = true := by
  induction gs using List.reverseRecOn with
  | nil => intro _ x y _ h i hi; exact h i hi
  | append_singleton gs g ih =>
    intro hg x y hxy h i hi
    have IH := ih (fun g' h => hg g' (by simp [h])) x y hxy h
    have hgg : Good g := hg g (by simp)
    have hL : (W gs x).length = (W gs y).length := by rw [W_len, W_len, hxy]
    rw [W_snoc, stp] at hi ⊢
    rcases lt_trichotomy i (W gs x).length with h1 | h1 | h1
    · rw [getD_lt _ _ _ h1] at hi
      rw [getD_lt _ _ _ (hL ▸ h1)]
      exact IH i hi
    · rw [h1, getD_len] at hi
      rw [h1, hL, getD_len]
      rcases hgg.1 with ho | ho
      · rw [ho] at hi ⊢
        simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id] at hi ⊢
        exact fun j hj => IH j (hi j hj)
      · rw [ho] at hi ⊢
        simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id] at hi ⊢
        obtain ⟨j, hj, hj'⟩ := hi
        exact ⟨j, hj, IH j hj'⟩
    · rw [getD_big _ _ (by simp; omega)] at hi
      exact absurd hi (by simp)

def PEqualNP.Outside.L_meta_20924.ro (v : Fin 5) : List Bool := List.replicate 4 false ++ List.ofFn (fun j : Fin 5 => decide (j = v))
def PEqualNP.Outside.L_meta_20924.lo (u : Fin 4) : List Bool := List.ofFn (fun j : Fin 4 => decide (j = u)) ++ List.replicate 5 false

lemma PEqualNP.Outside.L_meta_20924.agree1 : ∀ (u : Fin 4) (v : Fin 5), ∀ i < 9, i ≠ (u : ℕ) →
    (oneEach u v).getD i false = (ro v).getD i false := by decide +kernel
lemma PEqualNP.Outside.L_meta_20924.agree2 : ∀ (u : Fin 4) (v : Fin 5), ∀ i < 9, i ≠ 4 + (v : ℕ) →
    (oneEach u v).getD i false = (lo u).getD i false := by decide +kernel
lemma PEqualNP.Outside.L_meta_20924.below1 : ∀ (u : Fin 4) (v : Fin 5), ∀ i < 9, (ro v).getD i false = true →
    (oneEach u v).getD i false = true := by decide +kernel
lemma PEqualNP.Outside.L_meta_20924.below2 : ∀ (u : Fin 4) (v : Fin 5), ∀ i < 9, (lo u).getD i false = true →
    (oneEach u v).getD i false = true := by decide +kernel
lemma PEqualNP.Outside.L_meta_20924.oe_len : ∀ (u : Fin 4) (v : Fin 5), (oneEach u v).length = 9 := by decide +kernel
lemma PEqualNP.Outside.L_meta_20924.ro_len : ∀ v : Fin 5, (ro v).length = 9 := by decide +kernel
lemma PEqualNP.Outside.L_meta_20924.lo_len : ∀ v : Fin 4, (lo v).length = 9 := by decide +kernel

lemma PEqualNP.Outside.L_meta_20924.below_of (x y : List Bool) (hx : x.length = 9)
    (h : ∀ i < 9, x.getD i false = true → y.getD i false = true) :
    ∀ i, x.getD i false = true → y.getD i false = true := by
  intro i hi
  by_cases h8 : i < 9
  · exact h i h8 hi
  · rw [getD_big _ _ (by omega)] at hi; exact absurd hi (by simp)

lemma PEqualNP.Outside.L_meta_20924.row_in (C : Circuit) (hC : ∀ g ∈ C.gates, Good g) (A : Fin 4 → Fin 5 → Bool)
    (hrep : Represents A C) (D : Finset ℕ) (hD8 : D ⊆ Finset.range 9)
    (hD : ∀ x y : List Bool, x.length = 9 → y.length = 9 →
      (∀ i ∈ D, x.getD i false = y.getD i false) → C.eval x = C.eval y) (u : Fin 4)
    (hu : (u : ℕ) ∉ D) : ∀ u' v, A u v = true → A u' v = true := by
  intro u' v h
  rw [← hrep u v, hD (oneEach u v) (ro v) (oe_len u v) (ro_len v) (fun i hi =>
    agree1 u v i (by simpa using hD8 hi) (fun h => hu (h ▸ hi)))] at h
  rw [← hrep u' v]
  exact mono C.gates hC (ro v) (oneEach u' v) (by rw [ro_len, oe_len])
    (below_of _ _ (ro_len v) (below1 u' v)) C.output h

lemma PEqualNP.Outside.L_meta_20924.col_in (C : Circuit) (hC : ∀ g ∈ C.gates, Good g) (A : Fin 4 → Fin 5 → Bool)
    (hrep : Represents A C) (D : Finset ℕ) (hD8 : D ⊆ Finset.range 9)
    (hD : ∀ x y : List Bool, x.length = 9 → y.length = 9 →
      (∀ i ∈ D, x.getD i false = y.getD i false) → C.eval x = C.eval y) (v : Fin 5)
    (hv : 4 + (v : ℕ) ∉ D) : ∀ v' u, A u v = true → A u v' = true := by
  intro v' u h
  rw [← hrep u v, hD (oneEach u v) (lo u) (oe_len u v) (lo_len u) (fun i hi =>
    agree2 u v i (by simpa using hD8 hi) (fun h => hv (h ▸ hi)))] at h
  rw [← hrep u v']
  exact mono C.gates hC (lo u) (oneEach u v') (by rw [lo_len, oe_len])
    (below_of _ _ (lo_len u) (below2 u v')) C.output h

def PEqualNP.Outside.L_meta_20924.OO : List ℕ := [1, 2, 3, 4, 6, 7, 8, 9, 11, 12, 15]
def PEqualNP.Outside.L_meta_20924.ZZ : List ℕ := [0, 5, 10, 13, 14, 16, 17, 18, 19]

def PEqualNP.Outside.L_meta_20924.po (i : ℕ) : ℕ := OO.getD (i / 32) 0
def PEqualNP.Outside.L_meta_20924.zo (i : ℕ) : ℕ := ZZ.getD (i % 32) 0
def PEqualNP.Outside.L_meta_20924.V (i : ℕ) : Prop := i / 32 < OO.length ∧ i % 32 < ZZ.length

lemma PEqualNP.Outside.L_meta_20924.OO_ok : ∀ r < OO.length, OO.getD r 0 < 20 ∧ MM.testBit (OO.getD r 0) = true := by decide +kernel
lemma PEqualNP.Outside.L_meta_20924.ZZ_ok : ∀ r < ZZ.length, ZZ.getD r 0 < 20 ∧ MM.testBit (ZZ.getD r 0) = false := by decide +kernel
lemma PEqualNP.Outside.L_meta_20924.ZZ_len : ZZ.length ≤ 16 := by decide

def PEqualNP.Outside.L_meta_20924.dn (j x : ℕ) : ℕ := Nat.lor x (Nat.shiftRight x j)
def PEqualNP.Outside.L_meta_20924.up (j x : ℕ) : ℕ := Nat.lor x (Nat.shiftLeft x j)
def PEqualNP.Outside.L_meta_20924.ONE : ℕ := 3121748551042830955846434448392195761173861469553377210925551749450926617608515916953419850934372115559970022585814835838873106672153732883415041
def PEqualNP.Outside.L_meta_20924.rowf (x : ℕ) : ℕ := up 8 (up 4 (up 2 (up 1 (Nat.land (dn 8 (dn 4 (dn 2 (dn 1 x)))) ONE))))
def PEqualNP.Outside.L_meta_20924.colf (x : ℕ) : ℕ := up 256 (up 128 (up 64 (up 32 (dn 256 (dn 128 (dn 64 (dn 32 x)))))))

lemma PEqualNP.Outside.L_meta_20924.dn_bit (j x i : ℕ) (h : (dn j x).testBit i = true) :
    x.testBit i = true ∨ x.testBit (i + j) = true := by
  have h : (x ||| x >>> j).testBit i = true := h
  rw [Nat.testBit_or, Nat.testBit_shiftRight, Bool.or_eq_true, Nat.add_comm] at h
  exact h

lemma PEqualNP.Outside.L_meta_20924.up_bit (j x i : ℕ) (h : (up j x).testBit i = true) :
    x.testBit i = true ∨ (j ≤ i ∧ x.testBit (i - j) = true) := by
  have h : (x ||| x <<< j).testBit i = true := h
  rw [Nat.testBit_or, Nat.testBit_shiftLeft, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at h
  exact h

lemma PEqualNP.Outside.L_meta_20924.ONE_bit (i : ℕ) (h : ONE.testBit i = true) : i % 32 = 0 := by
  by_cases hi : i < 512
  · have : ∀ i < 512, ONE.testBit i = true → i % 32 = 0 := by decide +kernel
    exact this i hi h
  · have h1 : ONE.testBit i = false := by
      apply Nat.testBit_lt_two_pow
      calc ONE < 2 ^ 512 := by decide +kernel
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [h1] at h; exact absurd h (by simp)

lemma PEqualNP.Outside.L_meta_20924.land_bit (x y i : ℕ) (h : (Nat.land x y).testBit i = true) :
    x.testBit i = true ∧ y.testBit i = true := by
  have h : (x &&& y).testBit i = true := h
  rwa [Nat.testBit_and, Bool.and_eq_true] at h

lemma PEqualNP.Outside.L_meta_20924.rowf_bit (x i : ℕ) (h : (rowf x).testBit i = true) :
    ∃ j, x.testBit j = true ∧ j / 32 = i / 32 := by
  have u : ∀ n j y c : ℕ, (∀ i, y.testBit i = true → ∃ a, a ≤ c ∧ a ≤ i ∧ (i - a) % 32 = 0 ∧
      n.testBit (i - a) = true) → ∀ i, (up j y).testBit i = true → ∃ a, a ≤ c + j ∧ a ≤ i ∧
      (i - a) % 32 = 0 ∧ n.testBit (i - a) = true := by
    intro n j y c hy i hi
    rcases up_bit _ _ _ hi with hi | ⟨hl, hi⟩
    · obtain ⟨a, h1, h2, h3, h4⟩ := hy i hi
      exact ⟨a, by omega, h2, h3, h4⟩
    · obtain ⟨a, h1, h2, h3, h4⟩ := hy _ hi
      exact ⟨a + j, by omega, by omega, by rw [show i - (a + j) = i - j - a by omega]; exact h3,
        by rw [show i - (a + j) = i - j - a by omega]; exact h4⟩
  have d : ∀ j y c : ℕ, (∀ i, y.testBit i = true → ∃ a, a ≤ c ∧ x.testBit (i + a) = true) →
      ∀ i, (dn j y).testBit i = true → ∃ a, a ≤ c + j ∧ x.testBit (i + a) = true := by
    intro j y c hy i hi
    rcases dn_bit _ _ _ hi with hi | hi
    · obtain ⟨a, h1, h2⟩ := hy i hi
      exact ⟨a, by omega, h2⟩
    · obtain ⟨a, h1, h2⟩ := hy _ hi
      exact ⟨j + a, by omega, by rw [← Nat.add_assoc]; exact h2⟩
  set n := dn 8 (dn 4 (dn 2 (dn 1 x))) with hn
  have h0 : ∀ i, (Nat.land n ONE).testBit i = true → ∃ a, a ≤ 0 ∧ a ≤ i ∧ (i - a) % 32 = 0 ∧
      n.testBit (i - a) = true := by
    intro i hi
    have h1 := land_bit _ _ _ hi
    exact ⟨0, le_refl _, by omega, by simpa using ONE_bit i h1.2, by simpa using h1.1⟩
  obtain ⟨a, h1, h2, h3, h4⟩ := u n 8 _ _ (u n 4 _ _ (u n 2 _ _ (u n 1 _ _ h0))) i h
  obtain ⟨b, h5, h6⟩ := d 8 _ _ (d 4 _ _ (d 2 _ _ (d 1 x 0 (fun i hi => ⟨0, le_refl _, hi⟩)))) _ h4
  exact ⟨i - a + b, h6, by omega⟩

lemma PEqualNP.Outside.L_meta_20924.colf_bit (x i : ℕ) (h : (colf x).testBit i = true) :
    ∃ j, x.testBit j = true ∧ j % 32 = i % 32 := by
  have hd : ∀ j y : ℕ, j % 32 = 0 →
      (∀ n, y.testBit n = true → ∃ t, x.testBit t = true ∧ t % 32 = n % 32) →
      ∀ n, (dn j y).testBit n = true → ∃ t, x.testBit t = true ∧ t % 32 = n % 32 := by
    intro j y hj hy n hn
    rcases dn_bit _ _ _ hn with hn | hn
    · exact hy n hn
    · obtain ⟨t, h1, h2⟩ := hy _ hn
      exact ⟨t, h1, by omega⟩
  have hu : ∀ j y : ℕ, j % 32 = 0 →
      (∀ n, y.testBit n = true → ∃ t, x.testBit t = true ∧ t % 32 = n % 32) →
      ∀ n, (up j y).testBit n = true → ∃ t, x.testBit t = true ∧ t % 32 = n % 32 := by
    intro j y hj hy n hn
    rcases up_bit _ _ _ hn with hn | ⟨hl, hn⟩
    · exact hy n hn
    · obtain ⟨t, h1, h2⟩ := hy _ hn
      exact ⟨t, h1, by omega⟩
  exact hu 256 _ rfl (hu 128 _ rfl (hu 64 _ rfl (hu 32 _ rfl (hd 256 _ rfl (hd 128 _ rfl
    (hd 64 _ rfl (hd 32 x rfl (fun n hn => ⟨n, hn, rfl⟩)))))))) i h

def PEqualNP.Outside.L_meta_20924.cz : List ℕ → ℕ → ℕ
  | [], _ => 0
  | z :: l, x => Nat.add (Nat.mul 2 (cz l x)) (bif Nat.testBit x z then 1 else 0)

lemma PEqualNP.Outside.L_meta_20924.cz_bit (x : ℕ) : ∀ (l : List ℕ) (t : ℕ), (cz l x).testBit t = true →
    t < l.length ∧ x.testBit (l.getD t 0) = true := by
  intro l
  induction l with
  | nil => intro t h; simp [cz] at h
  | cons z l ih =>
    intro t h
    have e : cz (z :: l) x = 2 * cz l x + (bif Nat.testBit x z then 1 else 0) := rfl
    rw [e] at h
    cases t with
    | zero =>
      rw [Nat.testBit_zero, decide_eq_true_eq] at h
      refine ⟨by simp, ?_⟩
      cases hz : Nat.testBit x z
      · rw [hz] at h; simp at h
      · simpa using hz
    | succ t =>
      rw [Nat.testBit_succ] at h
      have e2 : (2 * cz l x + (bif Nat.testBit x z then 1 else 0)) / 2 = cz l x := by
        cases Nat.testBit x z <;> simp <;> omega
      rw [e2] at h
      have := ih t h
      exact ⟨by simpa using this.1, by simpa using this.2⟩

lemma PEqualNP.Outside.L_meta_20924.cz_of (x : ℕ) : ∀ (l : List ℕ) (t : ℕ), t < l.length → x.testBit (l.getD t 0) = true →
    (cz l x).testBit t = true := by
  intro l
  induction l with
  | nil => intro t h; simp at h
  | cons z l ih =>
    intro t h h2
    have e : cz (z :: l) x = 2 * cz l x + (bif Nat.testBit x z then 1 else 0) := rfl
    rw [e]
    cases t with
    | zero =>
      rw [Nat.testBit_zero, decide_eq_true_eq]
      have hz : Nat.testBit x z = true := by simpa using h2
      rw [hz]; simp
    | succ t =>
      rw [Nat.testBit_succ]
      have e2 : (2 * cz l x + (bif Nat.testBit x z then 1 else 0)) / 2 = cz l x := by
        cases Nat.testBit x z <;> simp <;> omega
      rw [e2]
      exact ih t (by simpa using h) (by simpa using h2)

def PEqualNP.Outside.L_meta_20924.FZ : ℕ := 2 ^ ZZ.length - 1

def PEqualNP.Outside.L_meta_20924.matL : List ℕ → ℕ
  | [] => 0
  | r :: l => Nat.lor r (Nat.shiftLeft (matL l) 32)

lemma PEqualNP.Outside.L_meta_20924.matL_bit : ∀ (l : List ℕ), (∀ r ∈ l, ∀ t, r.testBit t = true → t < 32) → ∀ i,
    (matL l).testBit i = true → i / 32 < l.length ∧ (l.getD (i / 32) 0).testBit (i % 32) = true := by
  intro l
  induction l with
  | nil => intro _ i h; simp [matL] at h
  | cons r l ih =>
    intro hl i h
    have h : (r ||| (matL l) <<< 32).testBit i = true := h
    rw [Nat.testBit_or, Nat.testBit_shiftLeft, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq] at h
    rcases h with h | ⟨h1, h2⟩
    · have hi := hl r List.mem_cons_self i h
      rw [Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]
      exact ⟨by simp, by simpa using h⟩
    · have := ih (fun r hr => hl r (List.mem_cons_of_mem _ hr)) _ h2
      have e1 : i / 32 = (i - 32) / 32 + 1 := by omega
      have e2 : i % 32 = (i - 32) % 32 := by omega
      rw [e1, e2]
      exact ⟨by simpa using this.1, by simpa using this.2⟩

def PEqualNP.Outside.L_meta_20924.ns (x : ℕ) : ℕ := matL (OO.map fun p => bif Nat.testBit x p then cz ZZ x else FZ)
def PEqualNP.Outside.L_meta_20924.nsp (x : ℕ) : ℕ := matL (OO.map fun p => bif Nat.testBit x p then cz ZZ x else Nat.xor FZ (cz ZZ x))
def PEqualNP.Outside.L_meta_20924.P0 : ℕ := matL (OO.map fun _ => FZ)

lemma PEqualNP.Outside.L_meta_20924.FZ_bit (t : ℕ) (h : FZ.testBit t = true) : t < ZZ.length := by
  unfold FZ at h
  rw [Nat.testBit_two_pow_sub_one] at h
  simpa using h

lemma PEqualNP.Outside.L_meta_20924.ns_bit (x i : ℕ) (h : (ns x).testBit i = true) : V i ∧
    ¬ (x.testBit (po i) = true ∧ x.testBit (zo i) = false) := by
  have hr : ∀ r ∈ OO.map (fun p => bif Nat.testBit x p then cz ZZ x else FZ), ∀ t,
      r.testBit t = true → t < ZZ.length := by
    intro r hr t ht
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hr
    cases hp : Nat.testBit x p
    · rw [hp] at ht; exact FZ_bit t ht
    · rw [hp] at ht; exact (cz_bit x ZZ t ht).1
  obtain ⟨h1, h2⟩ := matL_bit _ (fun r hr' t ht => by
    have := hr r hr' t ht; have := ZZ_len; omega) i h
  rw [List.length_map] at h1
  have e : (OO.map (fun p => bif Nat.testBit x p then cz ZZ x else FZ)).getD (i / 32) 0 =
      (bif Nat.testBit x (po i) then cz ZZ x else FZ) := by
    unfold po
    rw [List.getD_eq_getElem _ _ (by simpa using h1), List.getD_eq_getElem _ _ h1, List.getElem_map]
  have hlt : i % 32 < ZZ.length := by
    apply hr _ _ _ h2
    rw [List.getD_eq_getElem _ _ (by simpa using h1)]
    exact List.getElem_mem _
  refine ⟨⟨h1, hlt⟩, ?_⟩
  rintro ⟨h3, h4⟩
  rw [e, h3] at h2
  have := (cz_bit x ZZ _ h2).2
  unfold zo at h4
  rw [h4] at this; exact absurd this (by simp)

lemma PEqualNP.Outside.L_meta_20924.nsp_bit (x i : ℕ) (h : (nsp x).testBit i = true) : V i ∧
    x.testBit (po i) = x.testBit (zo i) := by
  have hx : ∀ t, (Nat.xor FZ (cz ZZ x)).testBit t = (FZ.testBit t ^^ (cz ZZ x).testBit t) := fun t =>
    Nat.testBit_xor ..
  have hr : ∀ r ∈ OO.map (fun p => bif Nat.testBit x p then cz ZZ x else Nat.xor FZ (cz ZZ x)), ∀ t,
      r.testBit t = true → t < ZZ.length := by
    intro r hr t ht
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hr
    cases hp : Nat.testBit x p
    · rw [hp, Bool.cond_false, hx t] at ht
      cases hF : FZ.testBit t
      · rw [hF, Bool.false_xor] at ht; exact (cz_bit x ZZ t ht).1
      · exact FZ_bit t hF
    · rw [hp] at ht; exact (cz_bit x ZZ t ht).1
  obtain ⟨h1, h2⟩ := matL_bit _ (fun r hr' t ht => by
    have := hr r hr' t ht; have := ZZ_len; omega) i h
  rw [List.length_map] at h1
  have e : (OO.map (fun p => bif Nat.testBit x p then cz ZZ x else Nat.xor FZ (cz ZZ x))).getD (i / 32) 0 =
      (bif Nat.testBit x (po i) then cz ZZ x else Nat.xor FZ (cz ZZ x)) := by
    unfold po
    rw [List.getD_eq_getElem _ _ (by simpa using h1), List.getD_eq_getElem _ _ h1, List.getElem_map]
  have hlt : i % 32 < ZZ.length := by
    apply hr _ _ _ h2
    rw [List.getD_eq_getElem _ _ (by simpa using h1)]
    exact List.getElem_mem _
  refine ⟨⟨h1, hlt⟩, ?_⟩
  rw [e] at h2
  cases hp : x.testBit (po i)
  · rw [hp, Bool.cond_false, hx] at h2
    have hF : FZ.testBit (i % 32) = true := by
      unfold FZ; rw [Nat.testBit_two_pow_sub_one]; simpa using hlt
    rw [hF, Bool.true_xor, Bool.not_eq_true'] at h2
    cases hz : x.testBit (zo i)
    · rfl
    · exfalso
      have := cz_of x ZZ (i % 32) hlt hz
      rw [this] at h2; exact absurd h2 (by simp)
  · rw [hp, Bool.cond_true] at h2
    exact ((cz_bit x ZZ _ h2).2).symm

lemma PEqualNP.Outside.L_meta_20924.P0_bit (i : ℕ) (h : P0.testBit i = true) : V i := by
  have hr : ∀ r ∈ OO.map (fun _ : ℕ => FZ), ∀ t, r.testBit t = true → t < ZZ.length := by
    intro r hr t ht
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hr
    exact FZ_bit t ht
  obtain ⟨h1, h2⟩ := matL_bit _ (fun r hr' t ht => by
    have := hr r hr' t ht; have := ZZ_len; omega) i h
  refine ⟨by simpa using h1, hr _ ?_ _ h2⟩
  rw [List.getD_eq_getElem _ _ h1]
  exact List.getElem_mem _

def PEqualNP.Outside.L_meta_20924.nsl (l : List ℕ) : ℕ := l.foldr (fun x acc => Nat.land x acc) (2 ^ 512 - 1)

lemma PEqualNP.Outside.L_meta_20924.nsl_bit (l : List ℕ) (i : ℕ) (h : (nsl l).testBit i = true) :
    ∀ x ∈ l, x.testBit i = true := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have h' := land_bit x (nsl l) i h
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact h'.1
    · exact ih h'.2 y hy

def PEqualNP.Outside.L_meta_20924.frc {α : Type} (x : ℕ) (k : ℕ → α) : α :=
  match x with
  | 0 => k 0
  | n + 1 => k (Nat.succ n)

lemma PEqualNP.Outside.L_meta_20924.frc_eq {α : Type} (x : ℕ) (k : ℕ → α) : frc x k = k x := by cases x <;> rfl

def PEqualNP.Outside.L_meta_20924.frcl {α : Type} : List ℕ → (List ℕ → α) → α
  | [], k => k []
  | x :: l, k => frc x fun x => frcl l fun l => k (x :: l)

lemma PEqualNP.Outside.L_meta_20924.frcl_eq {α : Type} : ∀ (l : List ℕ) (k : List ℕ → α), frcl l k = k l := by
  intro l
  induction l with
  | nil => intro k; rfl
  | cons x l ih => intro k; simp only [frcl, frc_eq, ih]

def PEqualNP.Outside.L_meta_20924.splits : List ℕ → List (List ℕ × List ℕ)
  | [] => [([], [])]
  | x :: l => (splits l).flatMap fun s => [(x :: s.1, s.2), (s.1, x :: s.2)]

lemma PEqualNP.Outside.L_meta_20924.mem_splits (c : ℕ → Bool) (v : ℕ → ℕ) (l : List ℕ) :
    ((l.filter c).map v, (l.filter fun i => !c i).map v) ∈ splits (l.map v) := by
  induction l with
  | nil => simp [splits]
  | cons x l ih =>
    simp only [List.map_cons, splits, List.mem_flatMap]
    refine ⟨_, ih, ?_⟩
    cases hx : c x <;> simp [hx]

def PEqualNP.Outside.L_meta_20924.rowc (P a b : ℕ) : Bool := Nat.beq (Nat.land (rowf (Nat.land P a)) (rowf (Nat.land P b))) 0
def PEqualNP.Outside.L_meta_20924.colc (P a b : ℕ) : Bool := Nat.beq (Nat.land (colf (Nat.land P a)) (colf (Nat.land P b))) 0

def PEqualNP.Outside.L_meta_20924.go (rec : List ℕ → ℕ → Bool) (P : ℕ) : List ℕ → List ℕ → ℕ → List ℕ → ℕ → Bool
  | [], A, a, B, b => !B.isEmpty &&
      ((rowc P a b && (rec A (Nat.land P (rowf (Nat.land P b))) &&
          rec B (Nat.land P (rowf (Nat.land P a))))) ||
       (colc P a b && (rec A (Nat.land P (colf (Nat.land P b))) &&
          rec B (Nat.land P (colf (Nat.land P a))))))
  | x :: l, A, a, B, b =>
      (rowc P (Nat.land a (nsl (x :: l))) (Nat.land b (nsl (x :: l))) ||
       colc P (Nat.land a (nsl (x :: l))) (Nat.land b (nsl (x :: l)))) &&
      (go rec P l (x :: A) (Nat.land x a) B b || go rec P l A a (x :: B) (Nat.land x b))

def PEqualNP.Outside.L_meta_20924.q : ℕ → List ℕ → ℕ → Bool
  | 0, _, _ => false
  | _ + 1, [], _ => false
  | f + 1, x :: l, P =>
    Nat.beq P 0 || (Nat.beq (Nat.land P (nsl (x :: l))) 0 && (l.isEmpty ||
      go (q f) P l [x] (nsl [x]) [] (nsl [])))

def PEqualNP.Outside.L_meta_20924.gen : ℕ → List ℕ → List ℕ
  | 0, _ => []
  | _ + 1, [] => []
  | f + 1, x :: l => bif l.isEmpty then [x] else
    (splits l).flatMap fun s => bif s.2.isEmpty then [] else
      (gen f (x :: s.1)).flatMap fun a => (gen f s.2).flatMap fun b =>
        frc (Nat.land a b) fun x => frc (Nat.lor a b) fun y => [x, y]

def PEqualNP.Outside.L_meta_20924.Sem (P : ℕ) (u : ℕ → Bool) : Prop := ∀ i, P.testBit i = true →
  V i ∧ u (po i) = true ∧ u (zo i) = false

def PEqualNP.Outside.L_meta_20924.Enum (l : List ℕ) (S : ℕ) : Prop := ∀ i, i ∈ l ↔ S.testBit i = true

lemma PEqualNP.Outside.L_meta_20924.beq_zero (x : ℕ) (h : ∀ i, x.testBit i = true → False) : Nat.beq x 0 = true := by
  have : x = 0 := by
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.zero_testBit]
    by_contra hne
    exact h i (by simpa using hne)
  rw [this]; rfl

def PEqualNP.Outside.L_meta_20924.Bad (P : ℕ) (u : ℕ → Bool) (x : ℕ) : Prop := ∀ i, x.testBit i = true → P.testBit i = true ∧
  ¬ (u (po i) = true ∧ u (zo i) = false)

def PEqualNP.Outside.L_meta_20924.Bp (nu : ℕ → ℕ) (S : ℕ) (u : ℕ → Bool) : Prop := ∀ P x, (∀ i, x.testBit i = true →
  P.testBit i = true ∧ ∀ j, S.testBit j = true → (nu j).testBit i = true) → Bad P u x

lemma PEqualNP.Outside.L_meta_20924.or_cond (P : ℕ) (a b : ℕ → Bool) (x y : ℕ) (hP : Sem P (fun p => a p || b p)) (hx : Bad P a x) (hy : Bad P b y) :
    Nat.beq (Nat.land (rowf x) (rowf y)) 0 = true ∧ Sem (Nat.land P (rowf y)) a ∧
      Sem (Nat.land P (rowf x)) b := by
  have c1 : ∀ i, (rowf x).testBit i = true → a (po i) = false := by
    intro i hc
    obtain ⟨j, hj, he⟩ := rowf_bit _ _ hc
    have h1 := hx j hj
    have h2 := (hP j h1.1).2
    simp only [Bool.or_eq_false_iff] at h2
    have e : po i = po j := by unfold po; rw [he]
    rw [e]
    by_contra h3
    exact h1.2 ⟨by simpa using h3, h2.2.1⟩
  have c2 : ∀ i, (rowf y).testBit i = true → b (po i) = false := by
    intro i hc
    obtain ⟨j, hj, he⟩ := rowf_bit _ _ hc
    have h1 := hy j hj
    have h2 := (hP j h1.1).2
    simp only [Bool.or_eq_false_iff] at h2
    have e : po i = po j := by unfold po; rw [he]
    rw [e]
    by_contra h3
    exact h1.2 ⟨by simpa using h3, h2.2.2⟩
  refine ⟨?_, ?_, ?_⟩
  · apply beq_zero
    intro i hi
    have hi := land_bit _ _ _ hi
    have h1 := c1 i hi.1
    have h2 := c2 i hi.2
    obtain ⟨j, hj, he⟩ := rowf_bit _ _ hi.1
    have h3 := (hP j (hx j hj).1).2.1
    have e : po j = po i := by unfold po; rw [he]
    simp only [e, h1, h2] at h3
    exact absurd h3 (by simp)
  · intro i hi
    have hi := land_bit _ _ _ hi
    have h2 := hP i hi.1
    simp only [Bool.or_eq_false_iff, Bool.or_eq_true] at h2
    refine ⟨h2.1, ?_, h2.2.2.1⟩
    have h3 := c2 i hi.2
    simpa [h3] using h2.2.1
  · intro i hi
    have hi := land_bit _ _ _ hi
    have h2 := hP i hi.1
    simp only [Bool.or_eq_false_iff, Bool.or_eq_true] at h2
    refine ⟨h2.1, ?_, h2.2.2.2⟩
    have h3 := c1 i hi.2
    simpa [h3] using h2.2.1

lemma PEqualNP.Outside.L_meta_20924.and_cond (P : ℕ) (a b : ℕ → Bool) (x y : ℕ) (hP : Sem P (fun p => a p && b p)) (hx : Bad P a x) (hy : Bad P b y) :
    Nat.beq (Nat.land (colf x) (colf y)) 0 = true ∧ Sem (Nat.land P (colf y)) a ∧
      Sem (Nat.land P (colf x)) b := by
  have c1 : ∀ i, (colf x).testBit i = true → a (zo i) = true := by
    intro i hc
    obtain ⟨j, hj, he⟩ := colf_bit _ _ hc
    have h1 := hx j hj
    have h2 := (hP j h1.1).2
    simp only [Bool.and_eq_true] at h2
    have e : zo i = zo j := by unfold zo; rw [he]
    rw [e]
    by_contra h3
    exact h1.2 ⟨h2.1.1, by simpa using h3⟩
  have c2 : ∀ i, (colf y).testBit i = true → b (zo i) = true := by
    intro i hc
    obtain ⟨j, hj, he⟩ := colf_bit _ _ hc
    have h1 := hy j hj
    have h2 := (hP j h1.1).2
    simp only [Bool.and_eq_true] at h2
    have e : zo i = zo j := by unfold zo; rw [he]
    rw [e]
    by_contra h3
    exact h1.2 ⟨h2.1.2, by simpa using h3⟩
  refine ⟨?_, ?_, ?_⟩
  · apply beq_zero
    intro i hi
    have hi := land_bit _ _ _ hi
    have h1 := c1 i hi.1
    have h2 := c2 i hi.2
    obtain ⟨j, hj, he⟩ := colf_bit _ _ hi.1
    have h3 := (hP j (hx j hj).1).2.2
    have e : zo j = zo i := by unfold zo; rw [he]
    simp only [e, h1, h2] at h3
    exact absurd h3 (by simp)
  · intro i hi
    have hi := land_bit _ _ _ hi
    have h2 := hP i hi.1
    simp only [Bool.and_eq_true] at h2
    refine ⟨h2.1, h2.2.1.1, ?_⟩
    have h3 := c2 i hi.2
    simpa [h3] using h2.2.2
  · intro i hi
    have hi := land_bit _ _ _ hi
    have h2 := hP i hi.1
    simp only [Bool.and_eq_true] at h2
    refine ⟨h2.1, h2.2.1.2, ?_⟩
    have h3 := c1 i hi.2
    simpa [h3] using h2.2.2

lemma PEqualNP.Outside.L_meta_20924.go_true (nu : ℕ → ℕ) (f P A B : ℕ) (a b : ℕ → Bool)
    (hAB : ∀ i, A.testBit i = true → B.testBit i = false) (hAs : Bp nu A a) (hBs : Bp nu B b)
    (hBne : ∃ z, B.testBit z = true)
    (hP : Sem P (fun p => a p && b p) ∨ Sem P (fun p => a p || b p))
    (qA : ∀ l, Enum l A → l.Nodup → l.length ≤ f → ∀ P', Sem P' a →
      q f (l.map nu) P' = true)
    (qB : ∀ l, Enum l B → l.Nodup → l.length ≤ f → ∀ P', Sem P' b →
      q f (l.map nu) P' = true) :
    ∀ l LA LB : List ℕ, (∀ i ∈ LA, A.testBit i = true) → (∀ i ∈ LB, B.testBit i = true) →
      (∀ i, A.testBit i = true → i ∈ LA ∨ i ∈ l) → (∀ i, B.testBit i = true → i ∈ LB ∨ i ∈ l) →
      (∀ i ∈ l, A.testBit i = true ∨ B.testBit i = true) → LA.Nodup → LB.Nodup → l.Nodup →
      (∀ i ∈ l, i ∉ LA ∧ i ∉ LB) → 1 ≤ LA.length → LA.length + LB.length + l.length ≤ f + 1 →
      go (q f) P (l.map nu) (LA.map nu)
        (nsl (LA.map nu)) (LB.map nu)
        (nsl (LB.map nu)) = true := by
  intro l
  induction l with
  | nil =>
    intro LA LB hA hB hA' hB' _ nA nB _ _ h1 hlen
    have eA : Enum LA A := fun i => ⟨hA i, fun h => (hA' i h).resolve_right (by simp)⟩
    have eB : Enum LB B := fun i => ⟨hB i, fun h => (hB' i h).resolve_right (by simp)⟩
    obtain ⟨z, hz⟩ := hBne
    have hzB := (eB z).mpr hz
    have hl2 : 1 ≤ LB.length := List.length_pos_of_mem hzB
    simp only [List.length_nil] at hlen
    have bA : Bad P a (Nat.land P (nsl (LA.map nu))) :=
      hAs P _ (fun i hi => by
        have hi := land_bit _ _ _ hi
        exact ⟨hi.1, fun j hj => nsl_bit _ _ hi.2 _
          (List.mem_map_of_mem (f := nu) ((eA j).mpr hj))⟩)
    have bB : Bad P b (Nat.land P (nsl (LB.map nu))) :=
      hBs P _ (fun i hi => by
        have hi := land_bit _ _ _ hi
        exact ⟨hi.1, fun j hj => nsl_bit _ _ hi.2 _
          (List.mem_map_of_mem (f := nu) ((eB j).mpr hj))⟩)
    have hne : (LB.map nu).isEmpty = false := by
      cases hc : LB with
      | nil => rw [hc] at hl2; simp at hl2
      | cons => rfl
    simp only [List.map_nil, go, hne, Bool.not_false, Bool.true_and, Bool.or_eq_true,
      Bool.and_eq_true]
    rcases hP with hP | hP
    · right
      obtain ⟨h1', h2, h3⟩ := and_cond P a b _ _ hP bA bB
      exact ⟨h1', qA LA eA nA (by omega) _ h2, qB LB eB nB (by omega) _ h3⟩
    · left
      obtain ⟨h1', h2, h3⟩ := or_cond P a b _ _ hP bA bB
      exact ⟨h1', qA LA eA nA (by omega) _ h2, qB LB eB nB (by omega) _ h3⟩
  | cons x l ih =>
    intro LA LB hA hB hA' hB' hl nA nB nl hdj h1 hlen
    have nl' := List.nodup_cons.mp nl
    simp only [List.length_cons] at hlen
    have bd : ∀ (S : ℕ) (m : ℕ → Bool) (L : List ℕ), Bp nu S m → (∀ i, S.testBit i = true → i ∈ L ∨ i ∈ x :: l) →
        Bad P m (Nat.land P (Nat.land (nsl (L.map nu))
          (nsl ((x :: l).map nu)))) := by
      intro S m L hs hS
      refine hs P _ (fun i hi => ?_)
      have hi := land_bit _ _ _ hi
      have hi2 := land_bit _ _ _ hi.2
      refine ⟨hi.1, fun j hj => ?_⟩
      rcases hS j hj with h | h
      · exact nsl_bit _ _ hi2.1 _ (List.mem_map_of_mem (f := nu) h)
      · exact nsl_bit _ _ hi2.2 _ (List.mem_map_of_mem (f := nu) h)
    have bA := bd A a LA hAs hA'
    have bB := bd B b LB hBs hB'
    simp only [List.map_cons] at bA bB ⊢
    rw [go, Bool.and_eq_true, Bool.or_eq_true, Bool.or_eq_true]
    constructor
    · rcases hP with hP | hP
      · right; exact (and_cond P a b _ _ hP bA bB).1
      · left; exact (or_cond P a b _ _ hP bA bB).1
    · have hxd := hdj x List.mem_cons_self
      rcases hl x List.mem_cons_self with hx | hx
      · left
        have := ih (x :: LA) LB (by
            intro i hi; rcases List.mem_cons.mp hi with rfl | hi
            · exact hx
            · exact hA i hi) hB (by
            intro i hi; rcases hA' i hi with h | h
            · exact Or.inl (List.mem_cons_of_mem _ h)
            · rcases List.mem_cons.mp h with rfl | h
              · exact Or.inl List.mem_cons_self
              · exact Or.inr h) (by
            intro i hi; rcases hB' i hi with h | h
            · exact Or.inl h
            · rcases List.mem_cons.mp h with rfl | h
              · rw [hAB _ hx] at hi; exact absurd hi (by simp)
              · exact Or.inr h) (fun i hi => hl i (List.mem_cons_of_mem _ hi))
          (List.nodup_cons.mpr ⟨hxd.1, nA⟩) nB nl'.2 (by
            intro i hi
            have h2 := hdj i (List.mem_cons_of_mem _ hi)
            refine ⟨fun h => ?_, h2.2⟩
            rcases List.mem_cons.mp h with rfl | h
            · exact nl'.1 hi
            · exact h2.1 h) (by simp) (by simp only [List.length_cons]; omega)
        simp only [List.map_cons] at this
        exact this
      · right
        have := ih LA (x :: LB) hA (by
            intro i hi; rcases List.mem_cons.mp hi with rfl | hi
            · exact hx
            · exact hB i hi) (by
            intro i hi; rcases hA' i hi with h | h
            · exact Or.inl h
            · rcases List.mem_cons.mp h with rfl | h
              · rw [hAB _ hi] at hx; exact absurd hx (by simp)
              · exact Or.inr h) (by
            intro i hi; rcases hB' i hi with h | h
            · exact Or.inl (List.mem_cons_of_mem _ h)
            · rcases List.mem_cons.mp h with rfl | h
              · exact Or.inl List.mem_cons_self
              · exact Or.inr h) (fun i hi => hl i (List.mem_cons_of_mem _ hi))
          nA (List.nodup_cons.mpr ⟨hxd.2, nB⟩) nl'.2 (by
            intro i hi
            have h2 := hdj i (List.mem_cons_of_mem _ hi)
            refine ⟨h2.1, fun h => ?_⟩
            rcases List.mem_cons.mp h with rfl | h
            · exact nl'.1 hi
            · exact h2.2 h) h1 (by simp only [List.length_cons]; omega)
        simp only [List.map_cons] at this
        exact this

def PEqualNP.Outside.L_meta_20924.Gd (nu : ℕ → ℕ) (S : ℕ) (u : ℕ → Bool) : Prop := (∃ i, S.testBit i = true) ∧ Bp nu S u ∧
  ∀ l, Enum l S → l.Nodup → ∀ f, l.length ≤ f → ∀ P, Sem P u → q f (l.map nu) P = true

lemma PEqualNP.Outside.L_meta_20924.enum_one (i : ℕ) (l : List ℕ) (hl : Enum l (2 ^ i)) (hn : l.Nodup) : l = [i] := by
  have hb : ∀ j, (2 ^ i).testBit j = true ↔ j = i := by
    intro j; rw [Nat.testBit_two_pow]; simp [eq_comm]
  have : l.Perm [i] := (List.perm_ext_iff_of_nodup hn (by simp)).mpr
    (fun j => by rw [hl j, hb j]; simp)
  exact List.perm_singleton.mp this

lemma PEqualNP.Outside.L_meta_20924.Gd_leaf (nu : ℕ → ℕ) (i : ℕ) (u : ℕ → Bool)
    (h : ∀ t, (nu i).testBit t = true → ¬ (u (po t) = true ∧ u (zo t) = false)) :
    Gd nu (2 ^ i) u := by
  have hb : ∀ j, (2 ^ i).testBit j = true ↔ j = i := by
    intro j; rw [Nat.testBit_two_pow]; simp [eq_comm]
  refine ⟨⟨i, (hb i).mpr rfl⟩, ?_, ?_⟩
  · intro P x hx t ht
    exact ⟨(hx t ht).1, h t ((hx t ht).2 i ((hb i).mpr rfl))⟩
  · intro l hl hn f hf P hP
    have hl' := enum_one i l hl hn
    rw [hl'] at hf ⊢
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
    have h0 : Nat.beq (Nat.land P (nsl ([i].map nu))) 0 = true := by
      apply beq_zero
      intro j hj
      have hj := land_bit _ _ _ hj
      have h1 := nsl_bit _ _ hj.2 (nu i) (by simp)
      exact h j h1 (hP j hj.1).2
    simp only [List.map_cons, List.map_nil] at h0 ⊢
    rw [q, h0]
    simp

lemma PEqualNP.Outside.L_meta_20924.Gd_half (nu : ℕ → ℕ) (A B : ℕ) (a b : ℕ → Bool)
    (h : ∀ i, A.testBit i = true → B.testBit i = false) (hA : Gd nu A a) (hB : Gd nu B b)
    (x : ℕ) (l : List ℕ) (hl : Enum (x :: l) (A ||| B)) (hn : (x :: l).Nodup)
    (hx : A.testBit x = true) (f : ℕ) (hf : (x :: l).length ≤ f) (P : ℕ)
    (hP : Sem P (fun p => a p && b p) ∨ Sem P (fun p => a p || b p)) :
    q f ((x :: l).map nu) P = true := by
  obtain ⟨_, hAs, hAq⟩ := hA
  obtain ⟨⟨z, hz⟩, hBs, hBq⟩ := hB
  obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
  have hor : ∀ i, (A ||| B).testBit i = true ↔ A.testBit i = true ∨ B.testBit i = true := by
    intro i; rw [Nat.testBit_or, Bool.or_eq_true]
  have hN := List.nodup_cons.mp hn
  have hAl : ∀ i, A.testBit i = true → i ∈ x :: l := fun i hi =>
    (hl i).mpr ((hor i).mpr (Or.inl hi))
  have hBl : ∀ i, B.testBit i = true → i ∈ x :: l := fun i hi =>
    (hl i).mpr ((hor i).mpr (Or.inr hi))
  have h0 : Nat.beq (Nat.land P (nsl ((x :: l).map nu))) 0 = true := by
    apply beq_zero
    intro i hi
    have key : ∀ S u, Bp nu S u → (∀ j, S.testBit j = true → j ∈ x :: l) →
        ¬ (u (po i) = true ∧ u (zo i) = false) := by
      intro S u hs hS
      refine (hs P (Nat.land P (nsl ((x :: l).map nu))) (fun t ht => ?_) i hi).2
      have ht := land_bit _ _ _ ht
      exact ⟨ht.1, fun j hj => nsl_bit _ _ ht.2 _ (List.mem_map_of_mem (f := nu) (hS j hj))⟩
    have kA := key A a hAs hAl
    have kB := key B b hBs hBl
    have hi := land_bit _ _ _ hi
    rcases hP with hP | hP
    · have := (hP i hi.1).2
      simp only [Bool.and_eq_true, Bool.and_eq_false_iff] at this
      rcases this.2 with h3 | h3
      · exact kA ⟨this.1.1, h3⟩
      · exact kB ⟨this.1.2, h3⟩
    · have := (hP i hi.1).2
      simp only [Bool.or_eq_true, Bool.or_eq_false_iff] at this
      rcases this.1 with h3 | h3
      · exact kA ⟨h3, this.2.1⟩
      · exact kB ⟨h3, this.2.2⟩
  by_cases hlne : l = []
  · subst hlne
    simp only [List.map_cons, List.map_nil] at h0 ⊢
    rw [q, h0]
    simp
  · have hgo := go_true nu f P A B a b h hAs hBs ⟨z, hz⟩ hP
      (fun l hl hn hf P' hP' => hAq l hl hn f hf P' hP')
      (fun l hl hn hf P' hP' => hBq l hl hn f hf P' hP') l [x] []
      (by intro i hi; rw [List.mem_singleton] at hi; rw [hi]; exact hx) (by simp)
      (by
        intro i hi
        rcases List.mem_cons.mp (hAl i hi) with h1 | h1
        · exact Or.inl (by rw [h1]; simp)
        · exact Or.inr h1)
      (by
        intro i hi
        rcases List.mem_cons.mp (hBl i hi) with h1 | h1
        · have := h x hx
          rw [h1, this] at hi; exact absurd hi (by simp)
        · exact Or.inr h1)
      (fun i hi => (hor i).mp ((hl i).mp (List.mem_cons_of_mem _ hi)))
      (by simp) (by simp) hN.2
      (fun i hi => ⟨fun h1 => by rw [List.mem_singleton] at h1; exact hN.1 (h1 ▸ hi), by simp⟩)
      (by simp) (by simp at hf ⊢; omega)
    simp only [List.map_cons, List.map_nil] at hgo h0 ⊢
    rw [q, Bool.or_eq_true, Bool.and_eq_true, Bool.or_eq_true]
    exact Or.inr ⟨h0, Or.inr hgo⟩

lemma PEqualNP.Outside.L_meta_20924.Gd_step (nu : ℕ → ℕ) (A B : ℕ) (a b : ℕ → Bool)
    (h : ∀ i, A.testBit i = true → B.testBit i = false) (hA : Gd nu A a) (hB : Gd nu B b) :
    Gd nu (A ||| B) (fun p => a p && b p) ∧ Gd nu (A ||| B) (fun p => a p || b p) := by
  have h' : ∀ i, B.testBit i = true → A.testBit i = false := by
    intro i hi
    by_contra hne
    have := h i (by simpa using hne)
    rw [this] at hi; exact absurd hi (by simp)
  have both : ∀ l, Enum l (A ||| B) → l.Nodup → ∀ f, l.length ≤ f → ∀ P,
      (Sem P (fun p => a p && b p) ∨ Sem P (fun p => a p || b p)) → q f (l.map nu) P = true := by
    intro l hl hn f hf P hP
    match l, hl, hn, hf with
    | [], hl, _, _ =>
      obtain ⟨i, hi⟩ := hA.1
      have := (hl i).mpr (by rw [Nat.testBit_or, hi]; rfl)
      simp at this
    | x :: l, hl, hn, hf =>
      have hx := (hl x).mp List.mem_cons_self
      rw [Nat.testBit_or, Bool.or_eq_true] at hx
      rcases hx with hx | hx
      · exact Gd_half nu A B a b h hA hB x l hl hn hx f hf P hP
      · refine Gd_half nu B A b a h' hB hA x l (by rw [Nat.or_comm]; exact hl) hn hx f hf P ?_
        simpa only [Bool.and_comm, Bool.or_comm] using hP
  obtain ⟨⟨i0, hi0⟩, hAs, _⟩ := hA
  obtain ⟨_, hBs, _⟩ := hB
  have hex : ∃ i, (A ||| B).testBit i = true := ⟨i0, by rw [Nat.testBit_or, hi0]; rfl⟩
  have sA : ∀ P x, (∀ i, x.testBit i = true → P.testBit i = true ∧
      ∀ j, (A ||| B).testBit j = true → (nu j).testBit i = true) → Bad P a x := fun P x hx =>
    hAs P x (fun i hi => ⟨(hx i hi).1, fun j hj => (hx i hi).2 j (by rw [Nat.testBit_or, hj]; rfl)⟩)
  have sB : ∀ P x, (∀ i, x.testBit i = true → P.testBit i = true ∧
      ∀ j, (A ||| B).testBit j = true → (nu j).testBit i = true) → Bad P b x := fun P x hx =>
    hBs P x (fun i hi => ⟨(hx i hi).1, fun j hj => (hx i hi).2 j (by rw [Nat.testBit_or, hj]; simp)⟩)
  refine ⟨⟨hex, ?_, fun l hl hn f hf P hP => both l hl hn f hf P (Or.inl hP)⟩,
    ⟨hex, ?_, fun l hl hn f hf P hP => both l hl hn f hf P (Or.inr hP)⟩⟩
  · intro P x hx i hi
    refine ⟨(hx i hi).1, ?_⟩
    rintro ⟨h1, h2⟩
    simp only [Bool.and_eq_true, Bool.and_eq_false_iff] at h1 h2
    rcases h2 with h2 | h2
    · exact (sA P x hx i hi).2 ⟨h1.1, h2⟩
    · exact (sB P x hx i hi).2 ⟨h1.2, h2⟩
  · intro P x hx i hi
    refine ⟨(hx i hi).1, ?_⟩
    rintro ⟨h1, h2⟩
    simp only [Bool.or_eq_true, Bool.or_eq_false_iff] at h1 h2
    rcases h1 with h1 | h1
    · exact (sA P x hx i hi).2 ⟨h1, h2.1⟩
    · exact (sB P x hx i hi).2 ⟨h1, h2.2⟩

lemma PEqualNP.Outside.L_meta_20924.po_lt (i : ℕ) : po i < 20 := by
  unfold po
  by_cases h : i / 32 < OO.length
  · exact (OO_ok _ h).1
  · rw [List.getD_eq_default _ _ (by omega)]; norm_num

lemma PEqualNP.Outside.L_meta_20924.zo_lt (i : ℕ) : zo i < 20 := by
  unfold zo
  by_cases h : i % 32 < ZZ.length
  · exact (ZZ_ok _ h).1
  · rw [List.getD_eq_default _ _ (by omega)]; norm_num

lemma PEqualNP.Outside.L_meta_20924.po_ok (i : ℕ) (h : V i) : po i < 20 ∧ MM.testBit (po i) = true := OO_ok _ h.1
lemma PEqualNP.Outside.L_meta_20924.zo_ok (i : ℕ) (h : V i) : zo i < 20 ∧ MM.testBit (zo i) = false := ZZ_ok _ h.2

def PEqualNP.Outside.L_meta_20924.labs (K S : ℕ) : List ℕ := (List.range K).filter (Nat.testBit S)

lemma PEqualNP.Outside.L_meta_20924.labs_enum (K S : ℕ) (hS : ∀ i, S.testBit i = true → i < K) : Enum (labs K S) S := by
  intro i
  unfold labs
  rw [List.mem_filter, List.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨hS i h, h⟩⟩

lemma PEqualNP.Outside.L_meta_20924.labs_nodup (K S : ℕ) : (labs K S).Nodup := List.Nodup.filter _ List.nodup_range

lemma PEqualNP.Outside.L_meta_20924.labs_len (K S : ℕ) : (labs K S).length ≤ K := by
  unfold labs
  refine (List.length_filter_le _ _).trans ?_
  simp

def PEqualNP.Outside.L_meta_20924.xt (lv : ℕ → ℕ) (K z i : ℕ) : ℕ := bif Nat.blt i K then lv i else z

lemma PEqualNP.Outside.L_meta_20924.xt_eq (lv : ℕ → ℕ) (K z : ℕ) : xt lv K z = ext lv K z := by
  funext i
  unfold xt ext
  by_cases h : i < K
  · have : Nat.blt i K = true := by rw [Nat.blt_eq]; exact h
    simp [this, h]
  · have : Nat.blt i K = false := by
      rw [Bool.eq_false_iff]; intro h'; rw [Nat.blt_eq] at h'; exact h h'
    simp [this, h]

def PEqualNP.Outside.L_meta_20924.nw (K D Sc : ℕ) : ℕ := Nat.lor (Nat.xor D Sc) (Nat.lor (2 ^ K) (2 ^ (K + 1)))

lemma PEqualNP.Outside.L_meta_20924.nw_bit (K D Sc : ℕ) (hSc : ∀ i, Sc.testBit i = true → D.testBit i = true) (i : ℕ) :
    (nw K D Sc).testBit i = true ↔ (D.testBit i = true ∧ Sc.testBit i = false) ∨ i = K ∨ i = K + 1 := by
  change ((D ^^^ Sc) ||| (2 ^ K ||| 2 ^ (K + 1))).testBit i = true ↔ _
  rw [Nat.testBit_or, Nat.testBit_or, Nat.testBit_xor, Bool.or_eq_true, Bool.or_eq_true,
    Nat.testBit_two_pow, Nat.testBit_two_pow, decide_eq_true_eq, decide_eq_true_eq]
  have e : ((D.testBit i ^^ Sc.testBit i) = true) ↔ (D.testBit i = true ∧ Sc.testBit i = false) := by
    cases hs : Sc.testBit i
    · simp
    · rw [hSc i hs]; simp
  rw [e, eq_comm (a := K), eq_comm (a := K + 1)]

lemma PEqualNP.Outside.L_meta_20924.Fam_one (ng : Bool) (lv : ℕ → ℕ) (K D o : ℕ) (val : ℕ → ℕ → Bool)
    (h : Fam ng lv K (fun i => D.testBit i = true) {o} val) :
    ∃ m, RO ng lv K D m ∧ ∀ p < 20, m.testBit p = val o p := by
  obtain ⟨S, m, hRO, hval, _, hun⟩ := h
  have hS : S o = D := by
    apply Nat.eq_of_testBit_eq; intro i
    rw [Bool.eq_iff_iff]
    have := hun i
    simpa using this
  have hR := hRO o (by simp)
  rw [hS] at hR
  exact ⟨m o, hR, hval o (by simp)⟩

def PEqualNP.Outside.L_meta_20924.Sp (lv : ℕ → ℕ) (S m : ℕ) : Prop := ∀ p r, m.testBit p = true → m.testBit r = false →
  ∃ j, S.testBit j = true ∧ (lv j).testBit p = true ∧ (lv j).testBit r = false

lemma PEqualNP.Outside.L_meta_20924.RO_Sp (lv : ℕ → ℕ) (K S m : ℕ) (h : RO false lv K S m) : Sp lv S m := by
  refine h (Sp lv) ?_ ?_ (by simp)
  · intro i _ p r h1 h2
    exact ⟨i, by rw [Nat.testBit_two_pow]; simp, h1, h2⟩
  · intro A B a b _ hA hB
    constructor
    · intro p r h1 h2
      rw [Nat.testBit_and, Bool.and_eq_true] at h1
      rw [Nat.testBit_and, Bool.and_eq_false_iff] at h2
      rcases h2 with h2 | h2
      · obtain ⟨j, hj, h3⟩ := hA p r h1.1 h2
        exact ⟨j, by rw [Nat.testBit_or, hj]; rfl, h3⟩
      · obtain ⟨j, hj, h3⟩ := hB p r h1.2 h2
        exact ⟨j, by rw [Nat.testBit_or, hj]; simp, h3⟩
    · intro p r h1 h2
      rw [Nat.testBit_or, Bool.or_eq_true] at h1
      rw [Nat.testBit_or, Bool.or_eq_false_iff] at h2
      rcases h1 with h1 | h1
      · obtain ⟨j, hj, h3⟩ := hA p r h1 h2.1
        exact ⟨j, by rw [Nat.testBit_or, hj]; rfl, h3⟩
      · obtain ⟨j, hj, h3⟩ := hB p r h1 h2.2
        exact ⟨j, by rw [Nat.testBit_or, hj]; simp, h3⟩

lemma PEqualNP.Outside.L_meta_20924.RO_Gd (lv : ℕ → ℕ) (K S m : ℕ) (h : RO false lv K S m) :
    Gd (fun i => ns (lv i)) S (fun p => m.testBit p) := by
  refine h (fun S m => Gd (fun i => ns (lv i)) S (fun p => m.testBit p)) ?_ ?_ (by simp)
  · intro i _
    exact Gd_leaf _ i _ (fun t ht => (ns_bit _ _ ht).2)
  · intro A B a b hd hA hB
    have := Gd_step _ A B _ _ hd hA hB
    simp only [Nat.testBit_and, Nat.testBit_or]
    exact this

lemma PEqualNP.Outside.L_meta_20924.split_enum (A B : ℕ) (h : ∀ i, A.testBit i = true → B.testBit i = false) (l : List ℕ)
    (hl : Enum l (A ||| B)) : Enum (l.filter fun i => A.testBit i) A ∧
      Enum (l.filter fun i => !A.testBit i) B := by
  have hor : ∀ i, (A ||| B).testBit i = true ↔ A.testBit i = true ∨ B.testBit i = true := by
    intro i; rw [Nat.testBit_or, Bool.or_eq_true]
  constructor
  · intro i
    rw [List.mem_filter]
    exact ⟨fun h => h.2, fun hi => ⟨(hl i).mpr ((hor i).mpr (Or.inl hi)), hi⟩⟩
  · intro i
    rw [List.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩
      rcases (hor i).mp ((hl i).mp h1) with h3 | h3
      · simp [h3] at h2
      · exact h3
    · intro hi
      have hiA : A.testBit i = false := by
        by_contra hne
        have := h i (by simpa using hne)
        rw [this] at hi; exact absurd hi (by simp)
      exact ⟨(hl i).mpr ((hor i).mpr (Or.inr hi)), by simp [hiA]⟩

lemma PEqualNP.Outside.L_meta_20924.enum_ne (S : ℕ) (l : List ℕ) (hl : Enum l S) (hS : ∃ i, S.testBit i = true) : l ≠ [] := by
  obtain ⟨i, hi⟩ := hS
  exact List.ne_nil_of_mem ((hl i).mpr hi)

lemma PEqualNP.Outside.L_meta_20924.map_ne {l : List ℕ} (v : ℕ → ℕ) (h : l ≠ []) : (l.map v).isEmpty = false := by
  cases l with
  | nil => exact absurd rfl h
  | cons => rfl

def PEqualNP.Outside.L_meta_20924.Gn (lv : ℕ → ℕ) (S m : ℕ) : Prop := (∃ i, S.testBit i = true) ∧
  ∀ l, Enum l S → l.Nodup → ∀ f, l.length ≤ f → m ∈ gen f (l.map lv)

lemma PEqualNP.Outside.L_meta_20924.gen_half (lv : ℕ → ℕ) (A B a b : ℕ) (h : ∀ i, A.testBit i = true → B.testBit i = false)
    (hA : Gn lv A a) (hB : Gn lv B b) (x : ℕ) (l : List ℕ) (hl : Enum (x :: l) (A ||| B))
    (hn : (x :: l).Nodup) (hx : A.testBit x = true) (f : ℕ) (hf : (x :: l).length ≤ f) :
    (a &&& b) ∈ gen f ((x :: l).map lv) ∧ (a ||| b) ∈ gen f ((x :: l).map lv) := by
  obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
  obtain ⟨e1, e2⟩ := split_enum A B h (x :: l) hl
  have hN := List.nodup_cons.mp hn
  have f1 : (x :: l).filter (fun i => A.testBit i) = x :: l.filter (fun i => A.testBit i) := by
    simp [hx]
  have f2 : (x :: l).filter (fun i => !A.testBit i) = l.filter (fun i => !A.testBit i) := by
    simp [hx]
  rw [f1] at e1; rw [f2] at e2
  set l1 := l.filter (fun i => A.testBit i) with hl1
  set l2 := l.filter (fun i => !A.testBit i) with hl2
  have hne2 := enum_ne B l2 e2 hB.1
  have hlen : l1.length + l2.length = l.length := by
    rw [hl1, hl2]; exact (List.length_eq_length_filter_add _).symm
  have hlen2 : 0 < l2.length := List.length_pos_of_ne_nil hne2
  have hlf : l.length ≤ f := by simp at hf; omega
  have hlne : l ≠ [] := by
    intro h0
    rw [h0] at hlen
    have : ([] : List ℕ).length = 0 := rfl
    omega
  have hN1 : (x :: l1).Nodup := List.nodup_cons.mpr
    ⟨fun hm => hN.1 (List.mem_of_mem_filter hm), hN.2.filter _⟩
  have hg1 := hA.2 _ e1 hN1 f (by simp; omega)
  have hg2 := hB.2 _ e2 (hN.2.filter _) f (by omega)
  have hs := mem_splits (fun i => A.testBit i) lv l
  rw [← hl1, ← hl2] at hs
  simp only [List.map_cons, gen, map_ne lv hlne, Bool.cond_false, List.mem_flatMap]
  refine ⟨⟨_, hs, ?_⟩, ⟨_, hs, ?_⟩⟩ <;> simp only [map_ne lv hne2, Bool.cond_false, List.mem_flatMap, frc_eq]
  · exact ⟨a, by simpa using hg1, b, hg2, List.mem_cons_self⟩
  · exact ⟨a, by simpa using hg1, b, hg2, List.mem_cons_of_mem _ List.mem_cons_self⟩

lemma PEqualNP.Outside.L_meta_20924.RO_gen (lv : ℕ → ℕ) (K S m : ℕ) (h : RO false lv K S m) : Gn lv S m := by
  refine h (Gn lv) ?_ ?_ (by simp)
  · intro i _
    refine ⟨⟨i, by rw [Nat.testBit_two_pow]; simp⟩, fun l hl hn f hf => ?_⟩
    rw [enum_one i l hl hn] at hf ⊢
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
    simp [gen]
  · intro A B a b hd hA hB
    have h' : ∀ i, B.testBit i = true → A.testBit i = false := by
      intro i hi
      by_contra hne
      have := hd i (by simpa using hne)
      rw [this] at hi; exact absurd hi (by simp)
    have hex : ∃ i, (A ||| B).testBit i = true := by
      obtain ⟨i, hi⟩ := hA.1
      exact ⟨i, by rw [Nat.testBit_or, hi]; rfl⟩
    have both : ∀ l, Enum l (A ||| B) → l.Nodup → ∀ f, l.length ≤ f →
        (a &&& b) ∈ gen f (l.map lv) ∧ (a ||| b) ∈ gen f (l.map lv) := by
      intro l hl hn f hf
      match l, hl, hn, hf with
      | [], hl, _, _ => exact absurd rfl (enum_ne _ _ hl hex)
      | x :: l, hl, hn, hf =>
        have hx := (hl x).mp List.mem_cons_self
        rw [Nat.testBit_or, Bool.or_eq_true] at hx
        rcases hx with hx | hx
        · exact gen_half lv A B a b hd hA hB x l hl hn hx f hf
        · have := gen_half lv B A b a h' hB hA x l (by rw [Nat.or_comm]; exact hl) hn hx f hf
          rw [Nat.and_comm b a, Nat.or_comm b a] at this
          exact this
    exact ⟨⟨hex, fun l hl hn f hf => (both l hl hn f hf).1⟩,
      ⟨hex, fun l hl hn f hf => (both l hl hn f hf).2⟩⟩

def PEqualNP.Outside.L_meta_20924.cv (x : ℕ) : ℕ := cz (OO ++ ZZ) x

lemma PEqualNP.Outside.L_meta_20924.cz_iff (L : List ℕ) (x t : ℕ) : (cz L x).testBit t = true ↔ t < L.length ∧ x.testBit (L.getD t 0) = true :=
  ⟨cz_bit x L t, fun h => cz_of x L t h.1 h.2⟩

lemma PEqualNP.Outside.L_meta_20924.cv_and (a b : ℕ) : cv (a &&& b) = cv a &&& cv b := by
  apply Nat.eq_of_testBit_eq; intro t
  rw [Bool.eq_iff_iff, Nat.testBit_and, Bool.and_eq_true]
  unfold cv
  rw [cz_iff, cz_iff, cz_iff, Nat.testBit_and, Bool.and_eq_true]
  tauto

lemma PEqualNP.Outside.L_meta_20924.cv_or (a b : ℕ) : cv (a ||| b) = cv a ||| cv b := by
  apply Nat.eq_of_testBit_eq; intro t
  rw [Bool.eq_iff_iff, Nat.testBit_or, Bool.or_eq_true]
  unfold cv
  rw [cz_iff, cz_iff, cz_iff, Nat.testBit_or, Bool.or_eq_true]
  tauto

lemma PEqualNP.Outside.L_meta_20924.RO_cv (lv : ℕ → ℕ) (K S m : ℕ) (h : RO false lv K S m) :
    RO false (fun i => cv (lv i)) K S (cv m) := by
  intro Q h1 h2 _
  refine h (fun S m => Q S (cv m)) h1 (fun A B a b hd hA hB => ?_) (by simp)
  have := h2 A B (cv a) (cv b) hd hA hB
  rw [cv_and, cv_or]
  exact this

def PEqualNP.Outside.L_meta_20924.fits (l n z : ℕ) : Bool := Nat.beq (Nat.land l z) l && Nat.beq (Nat.land n z) 0

def PEqualNP.Outside.L_meta_20924.qx : ℕ → List ℕ → ℕ → ℕ → Bool
  | 0, _, _, _ => false
  | f + 1, L, l, n => Nat.beq l 0 || Nat.beq n 0 ||
    (bif Nat.ble L.length 4 then (gen 14 L).any (fits l n) else
      (splits L).any fun s => Nat.ble s.1.length 4 && !s.1.isEmpty && !s.2.isEmpty &&
        (gen 14 s.1).any fun a =>
          (Nat.beq (Nat.land n a) 0 && frc (Nat.xor l (Nat.land l a)) fun l' => qx f s.2 l' n) ||
          (Nat.beq (Nat.land l a) l && frc (Nat.land n a) fun n' => qx f s.2 l n'))

def PEqualNP.Outside.L_meta_20924.In (l n m : ℕ) : Prop := (∀ t, l.testBit t = true → m.testBit t = true) ∧
  (∀ t, n.testBit t = true → m.testBit t = false)

lemma PEqualNP.Outside.L_meta_20924.land_eq (l a : ℕ) (h : ∀ t, l.testBit t = true → a.testBit t = true) :
    Nat.beq (Nat.land l a) l = true := by
  have : Nat.land l a = l := by
    change l &&& a = l
    apply Nat.eq_of_testBit_eq; intro t
    rw [Nat.testBit_and]
    cases hl : l.testBit t
    · rfl
    · rw [h t hl]; rfl
  rw [this]; exact Nat.beq_refl l

lemma PEqualNP.Outside.L_meta_20924.land_zero (n a : ℕ) (h : ∀ t, n.testBit t = true → a.testBit t = false) :
    Nat.beq (Nat.land n a) 0 = true := by
  apply beq_zero
  intro t ht
  have ht := land_bit _ _ _ ht
  rw [h t ht.1] at ht; exact absurd ht.2 (by simp)

def PEqualNP.Outside.L_meta_20924.Qx (lv : ℕ → ℕ) (S m : ℕ) : Prop := RO false lv 100 S m ∧
  ∀ L, Enum L S → L.Nodup → L.length ≤ 8 → ∀ f, L.length ≤ f → ∀ l n,
    In l n m → qx f (L.map lv) l n = true

lemma PEqualNP.Outside.L_meta_20924.qx_small (lv : ℕ → ℕ) (S m : ℕ) (h : RO false lv 100 S m) (L : List ℕ) (hL : Enum L S)
    (hn : L.Nodup) (hlen : L.length ≤ 4) (f : ℕ) (l n : ℕ) (hP : In l n m) :
    qx (f + 1) (L.map lv) l n = true := by
  have hg := (RO_gen lv 100 S m h).2 L hL hn 14 (by omega)
  have hb : Nat.ble (L.map lv).length 4 = true := by
    rw [List.length_map]; exact Nat.ble_eq.mpr hlen
  rw [qx, hb]
  simp only [Bool.cond_true, Bool.or_eq_true, List.any_eq_true]
  right
  refine ⟨m, hg, ?_⟩
  unfold fits
  rw [land_eq l m hP.1, land_zero n m hP.2]; rfl

lemma PEqualNP.Outside.L_meta_20924.qx_half (lv : ℕ → ℕ) (A B a b : ℕ) (hA : Qx lv A a) (hB : Qx lv B b) (L lA lB : List ℕ)
    (eA : Enum lA A) (eB : Enum lB B) (nA : lA.Nodup) (nB : lB.Nodup)
    (hs : (lA.map lv, lB.map lv) ∈ splits (L.map lv)) (h4 : lA.length ≤ 4) (h8 : lB.length ≤ 8)
    (f : ℕ) (hf : lB.length ≤ f) (l n : ℕ) (hlen : ¬ L.length ≤ 4)
    (hP : In l n (a &&& b) ∨ In l n (a ||| b)) :
    qx (f + 1) (L.map lv) l n = true := by
  have hb : Nat.ble (L.map lv).length 4 = false := by
    rw [List.length_map, Bool.eq_false_iff]; intro h; exact hlen (Nat.ble_eq.mp h)
  have hga := (RO_gen lv 100 A a hA.1).2 lA eA nA 14 (by omega)
  have n1 := map_ne lv (enum_ne A lA eA (RO_gen lv 100 A a hA.1).1)
  have n2 := map_ne lv (enum_ne B lB eB (RO_gen lv 100 B b hB.1).1)
  rw [qx, hb]
  simp only [Bool.cond_false, Bool.or_eq_true, List.any_eq_true]
  right
  refine ⟨_, hs, ?_⟩
  have hb4 : Nat.ble (lA.map lv).length 4 = true := by
    rw [List.length_map]; exact Nat.ble_eq.mpr h4
  simp only [hb4, n1, n2, Bool.not_false, Bool.true_and, List.any_eq_true, Bool.or_eq_true,
    Bool.and_eq_true, frc_eq]
  refine ⟨a, hga, ?_⟩
  rcases hP with hP | hP
  · right
    refine ⟨land_eq l a fun t ht => ?_, ?_⟩
    · have := hP.1 t ht
      rw [Nat.testBit_and, Bool.and_eq_true] at this
      exact this.1
    · apply hB.2 lB eB nB h8 f hf
      refine ⟨fun t ht => ?_, fun t ht => ?_⟩
      · have := hP.1 t ht
        rw [Nat.testBit_and, Bool.and_eq_true] at this
        exact this.2
      · have ht := land_bit _ _ _ ht
        have := hP.2 t ht.1
        rw [Nat.testBit_and, ht.2, Bool.true_and] at this
        exact this
  · left
    refine ⟨land_zero n a fun t ht => ?_, ?_⟩
    · have := hP.2 t ht
      rw [Nat.testBit_or, Bool.or_eq_false_iff] at this
      exact this.1
    · apply hB.2 lB eB nB h8 f hf
      refine ⟨fun t ht => ?_, fun t ht => ?_⟩
      · have ht : (l ^^^ (l &&& a)).testBit t = true := ht
        rw [Nat.testBit_xor, Nat.testBit_and] at ht
        cases hl : l.testBit t
        · rw [hl] at ht; simp at ht
        · rw [hl, Bool.true_and] at ht
          have := hP.1 t hl
          rw [Nat.testBit_or, Bool.or_eq_true] at this
          rcases this with h | h
          · rw [h] at ht; simp at ht
          · exact h
      · have := hP.2 t ht
        rw [Nat.testBit_or, Bool.or_eq_false_iff] at this
        exact this.2

lemma PEqualNP.Outside.L_meta_20924.RO_up (lv : ℕ → ℕ) (K S m : ℕ) (hK : K ≤ 100) (h : RO false lv K S m) :
    RO false lv 100 S m := fun Q h1 h2 h3 => h Q (fun i hi => h1 i (by omega)) h2 h3

lemma PEqualNP.Outside.L_meta_20924.RO_qx (lv : ℕ → ℕ) (K S m : ℕ) (hK : K ≤ 100) (h : RO false lv K S m) : Qx lv S m := by
  refine RO_up lv K S m hK h (Qx lv) ?_ ?_ (by simp)
  · intro i hi
    have hR := RO_leaf false lv 100 i hi
    refine ⟨hR, fun L hl hn h8 f hf l n hP => ?_⟩
    have hne := enum_ne _ L hl ⟨i, by rw [Nat.testBit_two_pow]; simp⟩
    have hpos := List.length_pos_of_ne_nil hne
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    refine qx_small lv _ _ hR L hl hn ?_ f l n hP
    rw [enum_one i L hl hn]; simp
  · intro A B a b hd hA hB
    have hRa := RO_and hd hA.1 hB.1
    have hRo := RO_or hd hA.1 hB.1
    have main : ∀ m, RO false lv 100 (A ||| B) m → (m = a &&& b ∨ m = a ||| b) →
        Qx lv (A ||| B) m := by
      intro m hR hm
      refine ⟨hR, fun L hl hn h8 f hf l n hP => ?_⟩
      have hne := enum_ne _ L hl (RO_gen lv 100 _ _ hR).1
      have hpos := List.length_pos_of_ne_nil hne
      obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      by_cases h4 : L.length ≤ 4
      · exact qx_small lv _ _ hR L hl hn h4 f l n hP
      · obtain ⟨e1, e2⟩ := split_enum A B hd L hl
        have hlen : (L.filter fun i => A.testBit i).length + (L.filter fun i => !A.testBit i).length =
            L.length := (List.length_eq_length_filter_add _).symm
        have hne1 := List.length_pos_of_ne_nil (enum_ne A _ e1 (RO_gen lv 100 A a hA.1).1)
        have hne2 := List.length_pos_of_ne_nil (enum_ne B _ e2 (RO_gen lv 100 B b hB.1).1)
        have hP' : In l n (a &&& b) ∨ In l n (a ||| b) := by
          rcases hm with rfl | rfl
          · exact Or.inl hP
          · exact Or.inr hP
        by_cases hA4 : (L.filter fun i => A.testBit i).length ≤ 4
        · exact qx_half lv A B a b hA hB L _ _ e1 e2 (hn.filter _) (hn.filter _)
            (mem_splits (fun i => A.testBit i) lv L) hA4 (by omega) f (by omega) l n h4 hP'
        · have hs := mem_splits (fun i => !A.testBit i) lv L
          simp only [Bool.not_not] at hs
          refine qx_half lv B A b a hB hA L _ _ e2 e1 (hn.filter _) (hn.filter _) hs (by omega)
            (by omega) f (by omega) l n h4 ?_
          rw [Nat.and_comm b a, Nat.or_comm b a]; exact hP'
    exact ⟨main _ hRa (Or.inl rfl), main _ hRo (Or.inr rfl)⟩

def PEqualNP.Outside.L_meta_20924.L0 : ℕ := 2 ^ OO.length - 1
def PEqualNP.Outside.L_meta_20924.N0 : ℕ := Nat.xor (2 ^ (OO ++ ZZ).length - 1) (2 ^ OO.length - 1)

def PEqualNP.Outside.L_meta_20924.qe (lv : ℕ → ℕ) (K D : ℕ) : Bool := frcl ((labs K D).map fun i => cv (lv i)) fun L =>
  qx 14 L L0 N0

lemma PEqualNP.Outside.L_meta_20924.qe_of (lv : ℕ → ℕ) (K D m : ℕ) (hK : K ≤ 14) (hDK : ∀ i, D.testBit i = true → i < K)
    (h8 : (labs K D).length ≤ 8) (hR : RO false lv K D m)
    (hm : ∀ p < 20, m.testBit p = MM.testBit p) : qe lv K D = true := by
  unfold qe
  rw [frcl_eq]
  have hR' := RO_cv lv K D m hR
  refine (RO_qx _ K _ _ (by omega) hR').2 (labs K D) (labs_enum K D hDK) (labs_nodup K D) h8 14
    (by omega) L0 N0 ⟨fun t ht => ?_, fun t ht => ?_⟩
  · have ht : t < OO.length := by
      unfold L0 at ht; rw [Nat.testBit_two_pow_sub_one] at ht; simpa using ht
    unfold cv
    rw [cz_iff]
    have h1 := OO_ok t ht
    refine ⟨by simp; omega, ?_⟩
    have e : (OO ++ ZZ).getD t 0 = OO.getD t 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left ht, List.getD_eq_getElem?_getD]
    rw [e, hm _ h1.1]; exact h1.2
  · have ht : ((2 ^ (OO ++ ZZ).length - 1) ^^^ (2 ^ OO.length - 1)).testBit t = true := ht
    rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow_sub_one] at ht
    have h2 : t < (OO ++ ZZ).length ∧ ¬ t < OO.length := by
      by_cases a1 : t < (OO ++ ZZ).length <;> by_cases a2 : t < OO.length
      · rw [decide_eq_true a1, decide_eq_true a2] at ht; exact absurd ht (by decide)
      · exact ⟨a1, a2⟩
      · exfalso; rw [List.length_append] at a1; omega
      · rw [decide_eq_false a1, decide_eq_false a2] at ht; exact absurd ht (by decide)
    rw [Bool.eq_false_iff]
    intro hc
    unfold cv at hc
    rw [cz_iff] at hc
    have hz : t - OO.length < ZZ.length := by
      have := h2.1; rw [List.length_append] at this; omega
    have h1 := ZZ_ok _ hz
    have e : (OO ++ ZZ).getD t 0 = ZZ.getD (t - OO.length) 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
        List.getD_eq_getElem?_getD]
    rw [e, hm _ h1.1, h1.2] at hc
    exact absurd hc.2 (by simp)

def PEqualNP.Outside.L_meta_20924.dd : List ℕ → List ℕ
  | [] => []
  | x :: l => bif (dd l).any (Nat.beq x) then dd l else x :: dd l

lemma PEqualNP.Outside.L_meta_20924.mem_dd (l : List ℕ) (x : ℕ) (h : x ∈ l) : x ∈ dd l := by
  induction l with
  | nil => simp at h
  | cons y l ih =>
    unfold dd
    cases hb : (dd l).any (Nat.beq y)
    · rw [Bool.cond_false]
      rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h)
    · rw [Bool.cond_true]
      rcases List.mem_cons.mp h with rfl | h
      · rw [List.any_eq_true] at hb
        obtain ⟨t, ht, hxt⟩ := hb
        rw [Nat.eq_of_beq_eq_true hxt]; exact ht
      · exact ih h

def PEqualNP.Outside.L_meta_20924.bd (rec : (ℕ → ℕ) → ℕ → ℕ → Bool) (lv : ℕ → ℕ) (K D Sc : ℕ) : Bool :=
  Nat.beq Sc 0 || !(Nat.beq (Nat.land Sc D) Sc) ||
  (fun U : ℕ => !(q 14 ((labs K Sc).map fun i => ns (lv i)) (Nat.land (rowf U) (colf U))) ||
    (dd ((gen 14 ((labs K Sc).map lv)).filter fun z => Nat.beq (Nat.land U (ns z)) 0)).all fun z =>
      rec (xt lv K z) (K + 2) (nw K D Sc))
    (Nat.land P0 (nsl ((labs K (Nat.xor D Sc)).map fun i => ns (lv i))))

def PEqualNP.Outside.L_meta_20924.top (lv : ℕ → ℕ) (K D : ℕ) : Bool := !(q 14 ((labs K D).map fun i => ns (lv i)) P0) ||
  (Nat.ble (labs K D).length 8 && !(qe lv K D))

def PEqualNP.Outside.L_meta_20924.chkM : ℕ → (ℕ → ℕ) → ℕ → ℕ → Bool
  | 0, lv, K, D => top lv K D
  | j + 1, lv, K, D => top lv K D && (List.range (2 ^ K)).all (bd (chkM j) lv K D)

lemma PEqualNP.Outside.L_meta_20924.chk_split (j : ℕ) (lv : ℕ → ℕ) (K D : ℕ) (hv lt : List ℕ) (h0 : top lv K D = true)
    (hcov : ∀ Sc < 2 ^ K, Sc ∈ hv ∨ Sc ∈ lt) (h1 : ∀ Sc ∈ hv, bd (chkM j) lv K D Sc = true)
    (h2 : lt.all (bd (chkM j) lv K D) = true) : chkM (j + 1) lv K D = true := by
  rw [chkM, h0, Bool.true_and, List.all_eq_true]
  intro Sc hS
  rcases hcov Sc (List.mem_range.mp hS) with h | h
  · exact h1 Sc h
  · exact List.all_eq_true.mp h2 Sc h

lemma PEqualNP.Outside.L_meta_20924.Sh_sep (o : ℕ) (val : ℕ → ℕ → Bool) : ∀ j lv K (D : ℕ → Prop), (∀ i, D i → i < K) →
    Sh false j lv K D {o} val → ∀ p < 20, ∀ r < 20, val o p = true → val o r = false →
    ∃ i, D i ∧ (lv i).testBit p = true ∧ (lv i).testBit r = false := by
  intro j
  induction j with
  | zero =>
    rintro lv K D _ ⟨S, m, hRO, hval, _, hun⟩ p hp r hr h1 h2
    have hm := RO_Sp lv K _ _ (hRO o (by simp)) p r
      (by rw [hval o (by simp) p hp]; exact h1) (by rw [hval o (by simp) r hr]; exact h2)
    obtain ⟨i, hi, h3⟩ := hm
    exact ⟨i, (hun i).mp ⟨o, by simp, hi⟩, h3⟩
  | succ j ih =>
    rintro lv K D hDK ⟨Sc, mc, hR, hSc, hS⟩ p hp r hr h1 h2
    obtain ⟨i, hi, h3, h4⟩ := ih (ext lv K mc) (K + 2) _ (by
      rintro i (⟨h, _⟩ | h | h)
      · have := hDK i h; omega
      · omega
      · omega) hS p hp r hr h1 h2
    rcases hi with ⟨hiD, _⟩ | hi
    · have hlt := hDK i hiD
      simp only [ext, hlt, ↓reduceIte] at h3 h4
      exact ⟨i, hiD, h3, h4⟩
    · have hge : ¬ i < K := by omega
      simp only [ext, hge, ↓reduceIte] at h3 h4
      obtain ⟨t, ht, h5⟩ := RO_Sp lv K _ _ hR p r h3 h4
      exact ⟨t, hSc t ht, h5⟩

lemma PEqualNP.Outside.L_meta_20924.chkM_sound (o : ℕ) (val : ℕ → ℕ → Bool) (hv : ∀ p < 20, val o p = MM.testBit p) :
    ∀ j' j lv K D, j' ≤ j → K + 2 * j' ≤ 14 → (∀ i, D.testBit i = true → i < K) →
      Sh false j' lv K (fun i => D.testBit i = true) {o} val → chkM j lv K D = true → False := by
  intro j'
  induction j' with
  | zero =>
    rintro j lv K D _ hK hDK hF hc
    obtain ⟨m, hR, hm⟩ := Fam_one false lv K D o val hF
    have hsem : Sem P0 (fun p => m.testBit p) := fun i hi => by
      have hV := P0_bit i hi
      have h1 := po_ok i hV
      have h2 := zo_ok i hV
      exact ⟨hV, (hm _ h1.1).trans ((hv _ h1.1).trans h1.2), (hm _ h2.1).trans ((hv _ h2.1).trans h2.2)⟩
    have hlen := labs_len K D
    have hq := (RO_Gd lv K _ _ hR).2.2 (labs K D) (labs_enum K D hDK) (labs_nodup K D) 14
      (by omega) P0 hsem
    have ht : top lv K D = true := by
      cases j with
      | zero => exact hc
      | succ j => rw [chkM, Bool.and_eq_true] at hc; exact hc.1
    unfold top at ht
    rw [hq] at ht
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true] at ht
    have h8 := Nat.ble_eq.mp ht.1
    have hqx := qe_of lv K D m (by omega) hDK h8 hR (fun p hp => (hm p hp).trans (hv p hp))
    rw [hqx] at ht
    exact absurd ht.2 (by simp)
  | succ j' ih =>
    rintro j lv K D hj hK hDK ⟨Sc, mc, hR, hSc, hS⟩ hc
    obtain ⟨j, rfl⟩ : ∃ t, j = t + 1 := ⟨j - 1, by omega⟩
    rw [chkM, Bool.and_eq_true, List.all_eq_true] at hc
    have hScK : ∀ i, Sc.testBit i = true → i < K := fun i hi => hDK i (hSc i hi)
    have hSclt : Sc < 2 ^ K := by
      apply Nat.lt_pow_two_of_testBit
      intro i hi
      by_contra hne
      have := hScK i (by simpa using hne)
      omega
    have h := hc.2 Sc (List.mem_range.mpr hSclt)
    have hGc := RO_Gd lv K _ _ hR
    have e0 : Nat.beq Sc 0 = false := by
      obtain ⟨i, hi⟩ := hGc.1
      cases hb : Nat.beq Sc 0
      · rfl
      · have := Nat.eq_of_beq_eq_true hb
        rw [this] at hi; simp at hi
    have e1 : Nat.beq (Nat.land Sc D) Sc = true := by
      have : Nat.land Sc D = Sc := by
        change Sc &&& D = Sc
        apply Nat.eq_of_testBit_eq; intro i
        rw [Nat.testBit_and]
        cases hs : Sc.testBit i
        · rfl
        · rw [hSc i hs]; rfl
      rw [this]; exact Nat.beq_refl Sc
    unfold bd at h
    rw [e0, e1] at h
    simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true] at h
    set U := Nat.land P0 (nsl ((labs K (Nat.xor D Sc)).map fun i => ns (lv i))) with hU
    have hDK' : ∀ i, ((D.testBit i = true ∧ Sc.testBit i = false) ∨ i = K ∨ i = K + 1) → i < K + 2 := by
      rintro i (⟨h, _⟩ | h | h)
      · have := hDK i h; omega
      · omega
      · omega

    have hUs : ∀ i, U.testBit i = true → V i ∧ mc.testBit (po i) = true ∧ mc.testBit (zo i) = false := by
      intro i hi
      have hi := land_bit _ _ _ hi
      have hV := P0_bit i hi.1
      have h1 := po_ok i hV
      have h2 := zo_ok i hV
      obtain ⟨t, ht, h3, h4⟩ := Sh_sep o val j' (ext lv K mc) (K + 2) _ hDK' hS (po i) h1.1 (zo i) h2.1
        (by rw [hv _ h1.1]; exact h1.2) (by rw [hv _ h2.1]; exact h2.2)
      refine ⟨hV, ?_⟩
      rcases ht with ⟨htD, htS⟩ | ht
      · exfalso
        have hlt := hDK t htD
        simp only [ext, hlt, ↓reduceIte] at h3 h4
        have hx : (Nat.xor D Sc).testBit t = true := by
          change (D ^^^ Sc).testBit t = true
          rw [Nat.testBit_xor, htD, htS]; rfl
        have hmem : t ∈ labs K (Nat.xor D Sc) := by
          unfold labs; rw [List.mem_filter, List.mem_range]; exact ⟨hlt, hx⟩
        have := nsl_bit _ _ hi.2 _ (List.mem_map_of_mem (f := fun i => ns (lv i)) hmem)
        exact (ns_bit _ _ this).2 ⟨h3, h4⟩
      · have hge : ¬ t < K := by omega
        simp only [ext, hge, ↓reduceIte] at h3 h4
        exact ⟨h3, h4⟩
    have hE := labs_enum K Sc hScK
    have hlen : (labs K Sc).length ≤ 14 := by have := labs_len K Sc; omega
    rcases h with h | h
    · have := hGc.2.2 (labs K Sc) hE (labs_nodup K Sc) 14 hlen (Nat.land (rowf U) (colf U))
        (fun i hi => by
          have hi := land_bit _ _ _ hi
          obtain ⟨a, ha, ea⟩ := rowf_bit _ _ hi.1
          obtain ⟨b, hb, eb⟩ := colf_bit _ _ hi.2
          have h1 := hUs a ha
          have h2 := hUs b hb
          have e2 : po i = po a := by unfold po; rw [ea]
          have e3 : zo i = zo b := by unfold zo; rw [eb]
          exact ⟨⟨by rw [← ea]; exact h1.1.1, by rw [← eb]; exact h2.1.2⟩,
            by rw [e2]; exact h1.2.1, by rw [e3]; exact h2.2.2⟩)
      rw [this] at h; exact absurd h (by simp)
    · have hg := (RO_gen lv K _ _ hR).2 (labs K Sc) hE (labs_nodup K Sc) 14 hlen
      have hfit : Nat.beq (Nat.land U (ns mc)) 0 = true := by
        apply beq_zero
        intro i hi
        have hi := land_bit _ _ _ hi
        exact (ns_bit _ _ hi.2).2 (hUs i hi.1).2
      have hmem := mem_dd _ _ ((List.mem_filter
        (p := fun z => Nat.beq (Nat.land U (ns z)) 0)).mpr ⟨hg, hfit⟩)
      have h := List.all_eq_true.mp h mc hmem
      rw [xt_eq] at h
      refine ih j (ext lv K mc) (K + 2) (nw K D Sc) (by omega) (by omega) ?_ ?_ h
      · intro i hi
        exact hDK' i ((nw_bit K D Sc hSc i).mp hi)
      · have e : (fun i => (nw K D Sc).testBit i = true) =
            (fun i => (D.testBit i = true ∧ Sc.testBit i = false) ∨ i = K ∨ i = K + 1) := by
          funext i; exact propext (nw_bit K D Sc hSc i)
        rw [e]; exact hS

lemma PEqualNP.Outside.L_meta_20924.lower (s c : ℕ) (R : Finset ℕ) (DL : List ℕ)
    (hrow : ∀ u : Fin 4, (u : ℕ) ∈ R → ∃ (u' : Fin 4) (v : Fin 5),
      MM.testBit (5 * u + v) = true ∧ MM.testBit (5 * u' + v) = false)
    (hcol : ∀ v : Fin 5, 4 + (v : ℕ) ∈ R → ∃ (v' : Fin 5) (u : Fin 4),
      MM.testBit (5 * u + v) = true ∧ MM.testBit (5 * u + v') = false)
    (hR8 : ∀ i ∈ R, i < 9) (hR0 : 1 ≤ R.card)
    (hcode : ∀ i < 9, c.testBit i = decide (i ∈ R)) (hcbig : ∀ i, 9 ≤ i → c.testBit i = false) (hs : s + 1 ≤ R.card + 2)
    (hnt : ∃ p < 20, MM.testBit p = false)
    (hDL : ∀ D < 512, Nat.land c D = c → D ∈ DL)
    (hchk : ∀ D ∈ DL, chkM (s + 1 - (labs 9 D).length) lf 9 D = true) :
    ¬ RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => MM.testBit (5 * u.val + v.val)) s := by
  intro hrs
  obtain ⟨C, hgood, hsize, hrep, hirr⟩ := min_circ _ s hrs
  have hRD : ∀ D : Finset ℕ, D ⊆ Finset.range 9 →
      (∀ x y : List Bool, x.length = 9 → y.length = 9 →
        (∀ i ∈ D, x.getD i false = y.getD i false) → C.eval x = C.eval y) → R ⊆ D := by
    intro D hD8 hD i hi
    by_contra hiD
    have hi8 := hR8 i hi
    by_cases h4 : i < 4
    · obtain ⟨u', v, h1, h2⟩ := hrow ⟨i, h4⟩ hi
      have := row_in C hgood _ hrep D hD8 hD ⟨i, h4⟩ hiD u' v h1
      rw [h2] at this; exact absurd this (by simp)
    · have e : 4 + (i - 4) = i := by omega
      obtain ⟨v', u, h1, h2⟩ := hcol ⟨i - 4, by omega⟩ (by simpa [e] using hi)
      have := col_in C hgood _ hrep D hD8 hD ⟨i - 4, by omega⟩ (by simpa [e] using hiD) v' u h1
      rw [h2] at this; exact absurd this (by simp)
  have hev : ∀ x, C.eval x = (W C.gates x).getD C.output false := fun x => rfl
  have hv : ∀ p < 20, vl C.gates C.output p = MM.testBit p := by
    intro p hp
    unfold vl
    rw [← hev]
    have h := hrep ⟨p / 5 % 4, by omega⟩ ⟨p % 5, by omega⟩
    have e : 5 * (p / 5 % 4) + p % 5 = p := by omega
    simp only [e] at h
    exact h
  by_cases ho : C.output < 9 + C.gates.length
  swap
  · have := Finset.card_le_card (hRD ∅ (by simp) (fun x y hx hy _ => by
      rw [hev, hev, getD_big _ _ (by rw [W_len]; omega), getD_big _ _ (by rw [W_len]; omega)]))
    rw [Finset.card_empty] at this; omega
  · obtain ⟨D, d1, d2, j, d3, d4⟩ := main C.gates hgood hirr {C.output} (by simpa using ho) (by
      intro w hw
      rw [Finset.mem_singleton] at hw
      obtain ⟨p, hp, h⟩ := hnt
      exact ⟨p, hp, by rw [hw, hv p hp]; exact h⟩)
    rw [Finset.card_singleton] at d3
    have hsub := hRD D d1 (fun x y hx hy hxy => d2 x y hx hy hxy C.output (by simp))
    have hle := Finset.card_le_card hsub

    obtain ⟨dm, hdm⟩ : ∃ dm : ℕ, ∀ i, dm.testBit i = true ↔ i ∈ D := by
      refine ⟨Nat.ofBits (fun i : Fin 9 => decide ((i : ℕ) ∈ D)), fun i => ?_⟩
      by_cases h8 : i < 9
      · rw [Nat.testBit_ofBits_lt _ _ h8]; simp
      · rw [Nat.testBit_ofBits_ge _ _ (by omega)]
        constructor
        · intro h; exact absurd h (by simp)
        · intro h; have := d1 h; simp at this; omega
    have hdK : ∀ i, dm.testBit i = true → i < 9 := fun i hi => by
      have := d1 ((hdm i).mp hi); simpa using this
    have hdlt : dm < 512 := by
      have : dm < 2 ^ 9 := by
        apply Nat.lt_pow_two_of_testBit
        intro i hi
        by_contra hne
        have := hdK i (by simpa using hne)
        omega
      simpa using this
    have hlen : (labs 9 dm).length = D.card := by
      rw [← List.toFinset_card_of_nodup (labs_nodup 9 dm)]
      congr 1
      ext i
      rw [List.mem_toFinset, labs_enum 9 dm hdK i, hdm i]
    have hcd : Nat.land c dm = c := by
      change c &&& dm = c
      apply Nat.eq_of_testBit_eq; intro i
      rw [Nat.testBit_and]
      cases hc : c.testBit i
      · rfl
      · by_cases h8 : i < 9
        · rw [hcode i h8, decide_eq_true_eq] at hc
          rw [(hdm i).mpr (hsub hc)]; rfl
        · exact absurd hc (by
            have := hcbig i (by omega)
            simp [this])
    have hc := hchk dm (hDL dm hdlt hcd)
    rw [hlen] at hc
    refine chkM_sound C.output (vl C.gates) hv j _ lf 9 dm (by omega) (by omega) hdK ?_ hc
    have e : (fun i => dm.testBit i = true) = (· ∈ D) := by
      funext i; exact propext (hdm i)
    rw [e]; exact d4

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
lemma PEqualNP.Outside.L_meta_20924.certificate : chkM 0 lf 9 511 = true := by decide +kernel

theorem PEqualNP.Outside.L_meta_20924 : ¬ PEqualNP.Represents.RepSizeAtMost
    (fun (u : Fin 4) (v : Fin 5) => (39902 : ℕ).testBit (5 * u.val + v.val)) 8 := by
  refine PEqualNP.Outside.L_meta_20924.lower 8 511 {0, 1, 2, 3, 4, 5, 6, 7, 8} [511]
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide +kernel)
    (fun i hi => ?_) (by decide) (by decide +kernel) (by decide +kernel) ?_
  · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (by norm_num : 511 < 2 ^ 9)
      (Nat.pow_le_pow_right (by norm_num) hi))
  · intro D hD
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hD
    rcases hD with rfl
    exact PEqualNP.Outside.L_meta_20924.certificate
