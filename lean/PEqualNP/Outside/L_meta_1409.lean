import Mathlib
import PEqualNP.Defs

-- The live-wire signature search is adapted from L-meta-163 and Vivek Rajkumar's proof in pull request 1413.
-- The enumeration below records the gate signatures and verifies the five-cycle substitutions.
namespace PEqualNP.Outside.L_meta_1409_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev B := BitVec 31
abbrev Sig := B × B
def targetFun (x : Fin 5 → Bool) := decide (∃ i : Fin 5, x i = true ∧ x (i+1) = true)
def pairs : List (ℕ × ℕ) := [(3, 1), (3, 2), (6, 2), (6, 4), (7, 5), (11, 9), (11, 10), (12, 4), (12, 8), (13, 5), (13, 9), (14, 10), (17, 1), (17, 16), (19, 18), (21, 5), (21, 20), (22, 18), (22, 20), (24, 8), (24, 16), (25, 9), (26, 10), (26, 18), (28, 20), (15, 0), (23, 0), (27, 0), (29, 0), (30, 0), (31, 0)]
def maskFun (m : ℕ) : Fin 5 → Bool := fun i => m.testBit i.val

def pairA (r : Fin 31) : Fin 5 → Bool := maskFun (pairs.getD r.val (0, 0)).1
def pairB (r : Fin 31) : Fin 5 → Bool := maskFun (pairs.getD r.val (0, 0)).2

def mkBVLoop : ℕ → (ℕ → Bool) → ℕ
  | 0, _ => 0
  | n + 1, p => 2 * mkBVLoop n (fun k => p (k + 1)) + if p 0 then 1 else 0

def mkBV (p : Fin 31 → Bool) : B :=
  BitVec.ofNat 31 (mkBVLoop 31 (fun i => if h : i < 31 then p ⟨i, h⟩ else false))

lemma testBit_mkBVLoop (n : ℕ) : ∀ (p : ℕ → Bool) (i : ℕ), i < n →
    (mkBVLoop n p).testBit i = p i := by
  induction n with
  | zero => intro p i hi; omega
  | succ n ih =>
    intro p i hi
    cases i with
    | zero =>
      simp only [mkBVLoop]
      cases p 0 <;> simp
    | succ i =>
      simp only [mkBVLoop]
      have hbit : (2 * mkBVLoop n (fun k => p (k + 1)) + if p 0 then 1 else 0).testBit (i + 1) =
          (mkBVLoop n (fun k => p (k + 1))).testBit i := by
        cases p 0 <;> simp [Nat.testBit_succ, Nat.mul_add_div]
      rw [hbit, ih (fun k => p (k + 1)) i (by omega)]

lemma getElem_mkBV (p : Fin 31 → Bool) (i : ℕ) (hi : i < 31) :
    (mkBV p)[i] = p ⟨i, hi⟩ := by
  unfold mkBV
  rw [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat, Nat.testBit_mod_two_pow]
  simp only [decide_eq_true hi, Bool.true_and]
  rw [testBit_mkBVLoop 31 _ i hi]
  simp [hi]

lemma zero_bit (i : ℕ) (hi : i < 31) : (0 : B)[i] = false := by simp

def top : B := BitVec.allOnes 31
def zero : Sig := (0, 0)
def one : Sig := (top, top)
def target : Sig := (top, 0)

def neg (a : Sig) : Sig := (~~~ a.1, ~~~ a.2)

def bin (isOr : Bool) (a b : Sig) : Sig :=
  if isOr then (a.1 ||| b.1, a.2 ||| b.2) else (a.1 &&& b.1, a.2 &&& b.2)

def sep (d : Bool) (a : Sig) : B :=
  if d then a.1 ^^^ a.2 else a.1 &&& ~~~ a.2

def unionSep (d : Bool) : List Sig → B
  | [] => 0
  | a :: l => sep d a ||| unionSep d l

def before (a b : Sig) : Bool :=
  if a.1 == b.1 then decide (a.2.toNat < b.2.toNat) else decide (a.1.toNat < b.1.toNat)

def dropped (del v : List Sig) : List Sig :=
  v.filter (fun x => !del.contains x)

def initList : List Sig := [(1579284083, 2135601), (1858488447, 12732486), (1996984220, 17138328), (2079854560, 6819168), (2113925120, 26697728)]
def tryGate (allow : Sig → Bool) (k t : ℕ) (r : List Sig → Bool) (v rest : List Sig) (g : Sig)
    (keep : List (List Sig)) : Bool :=
  allow g && g != zero && g != one && !v.contains g &&
    (let d := decide (0 < t)
     let base := sep d g ||| unionSep d rest
     keep.any (fun h => decide (rest.length + h.length + 1 ≤ k - t + 1) &&
       (base ||| unionSep d h == top) && r (g :: (h ++ rest))))

def search (allow : Sig → Bool) : ℕ → ℕ → List Sig → Bool
  | 0, _, v => v.contains target
  | k + 1, t, v =>
    v.contains target ||
    (decide (0 < t) &&
      v.any (fun a => tryGate allow k (t - 1) (search allow k (t - 1)) v (dropped [a] v) (neg a) [[], [a]])) ||
    (decide (t ≤ k) &&
      v.any (fun a => v.any (fun b =>
        before a b &&
        (let rest := dropped [a, b] v
         let keep := [[], [a], [b], [a, b]]
         tryGate allow k t (search allow k t) v rest (bin false a b) keep ||
         tryGate allow k t (search allow k t) v rest (bin true a b) keep))))

def wiresToSigs (wa wb : Fin 31 → List Bool) (len : ℕ) : List Sig :=
  (List.range len).map (fun idx =>
    (mkBV (fun r => (wa r).getD idx false),
     mkBV (fun r => (wb r).getD idx false)))

def evalGateSig (g : Gate) (W : List Sig) : Sig :=
  match g.op, g.inputs with
  | GateOp.and, [] => one
  | GateOp.and, [p] => W.getD p zero
  | GateOp.and, [p, q] => bin false (W.getD p zero) (W.getD q zero)
  | GateOp.or, [] => zero
  | GateOp.or, [p] => W.getD p zero
  | GateOp.or, [p, q] => bin true (W.getD p zero) (W.getD q zero)
  | GateOp.not, [] => one
  | GateOp.not, p :: _ => neg (W.getD p zero)
  | _, _ => zero

def evalGates (gs : List Gate) (W : List Sig) : List Sig :=
  gs.foldl (fun W g => W ++ [evalGateSig g W]) W

def evalWires (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma evalGates_cons (g : Gate) (rest : List Gate) (W : List Sig) :
    evalGates (g :: rest) W = evalGates rest (W ++ [evalGateSig g W]) := rfl

lemma evalWires_cons (g : Gate) (rest : List Gate) (w : List Bool) :
    evalWires (g :: rest) w =
      evalWires rest (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma initList_eq :
    wiresToSigs (fun r => List.ofFn (pairA r)) (fun r => List.ofFn (pairB r)) 5 = initList := by
  decide

lemma pairA_true : ∀ r : Fin 31, targetFun (pairA r) = true := by decide
lemma pairB_false : ∀ r : Fin 31, targetFun (pairB r) = false := by decide
lemma initList_nodup : initList.Nodup := by decide
lemma initList_len : initList.length = 5 := by decide
lemma target_ne_zero : target ≠ zero := by decide
lemma target_ne_one : target ≠ one := by decide

lemma all_init_needed_bool :
    initList.all (fun s => unionSep true (initList.erase s) != top) = true := by decide

lemma all_init_needed : ∀ s ∈ initList, unionSep true (initList.erase s) ≠ top := by
  intro s hs
  have h := List.all_eq_true.1 all_init_needed_bool s hs
  exact bne_iff_ne.1 h

lemma bin_comm (isOr : Bool) (a b : Sig) : bin isOr a b = bin isOr b a := by
  cases isOr <;> simp only [bin, BitVec.or_comm, BitVec.and_comm]

lemma bin_self (isOr : Bool) (a : Sig) : bin isOr a a = a := by
  rcases a with ⟨a1, a2⟩
  cases isOr
  · simp only [bin, Bool.false_eq_true, ↓reduceIte, BitVec.and_self]
  · simp only [bin, ↓reduceIte, BitVec.or_self]

lemma bin_zero_left (isOr : Bool) (a : Sig) : bin isOr zero a = if isOr then a else zero := by
  rcases a with ⟨a1, a2⟩
  cases isOr
  · simp only [bin, zero, Bool.false_eq_true, ↓reduceIte]
    apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro r hr <;> simp
  · simp only [bin, zero, ↓reduceIte]
    apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro r hr <;> simp

lemma bin_zero_right (isOr : Bool) (a : Sig) : bin isOr a zero = if isOr then a else zero := by
  rw [bin_comm, bin_zero_left]

lemma bin_one_left (isOr : Bool) (a : Sig) : bin isOr one a = if isOr then one else a := by
  rcases a with ⟨a1, a2⟩
  cases isOr
  · simp only [bin, one, top, Bool.false_eq_true, ↓reduceIte, BitVec.allOnes_and]
  · simp only [bin, one, top, ↓reduceIte, BitVec.allOnes_or]

lemma bin_one_right (isOr : Bool) (a : Sig) : bin isOr a one = if isOr then one else a := by
  rw [bin_comm, bin_one_left]

lemma neg_zero : neg zero = one := by decide
lemma neg_one : neg one = zero := by decide

lemma before_trichotomy {a b : Sig} (hne : a ≠ b) : before a b = true ∨ before b a = true := by
  unfold before
  by_cases h1 : a.1 = b.1
  · have h2 : a.2 ≠ b.2 := fun h => hne (Prod.ext h1 h)
    have h2n : a.2.toNat ≠ b.2.toNat := fun h => h2 (BitVec.eq_of_toNat_eq h)
    have hb1 : (a.1 == b.1) = true := by rw [beq_iff_eq]; exact h1
    have hb2 : (b.1 == a.1) = true := by rw [beq_iff_eq]; exact h1.symm
    rw [hb1, hb2]
    simp only [↓reduceIte, decide_eq_true_eq]
    omega
  · have h1n : a.1.toNat ≠ b.1.toNat := fun h => h1 (BitVec.eq_of_toNat_eq h)
    have hb1 : (a.1 == b.1) = false := beq_false_of_ne h1
    have hb2 : (b.1 == a.1) = false := beq_false_of_ne (Ne.symm h1)
    rw [hb1, hb2]
    simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq]
    omega

lemma unionSep_perm {d : Bool} {v₁ v₂ : List Sig} (hp : v₁.Perm v₂) :
    unionSep d v₁ = unionSep d v₂ := by
  induction hp with
  | nil => rfl
  | cons a _ ih => simp only [unionSep, ih]
  | swap a b l =>
    simp only [unionSep]
    rw [← BitVec.or_assoc, ← BitVec.or_assoc, BitVec.or_comm (sep d a) (sep d b)]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

lemma unionSep_append (d : Bool) (l₁ l₂ : List Sig) :
    unionSep d (l₁ ++ l₂) = unionSep d l₁ ||| unionSep d l₂ := by
  induction l₁ with
  | nil => simp [unionSep]
  | cons a t ih => simp only [List.cons_append, unionSep, ih, BitVec.or_assoc]

lemma unionSep_bit_iff (d : Bool) (v : List Sig) (i : ℕ) (hi : i < 31) :
    (unionSep d v)[i] = true ↔ ∃ s ∈ v, (sep d s)[i] = true := by
  induction v with
  | nil => simp [unionSep]
  | cons a t ih =>
    simp only [unionSep, BitVec.getElem_or, Bool.or_eq_true, ih, List.mem_cons]
    constructor
    · rintro (h | ⟨s, hs, h⟩)
      · exact ⟨a, Or.inl rfl, h⟩
      · exact ⟨s, Or.inr hs, h⟩
    · rintro ⟨s, rfl | hs, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨s, hs, h⟩

lemma bv_eq_top_of_bits {x : B} (h : ∀ i (hi : i < 31), x[i] = true) : x = top := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  rw [top, BitVec.getElem_allOnes]
  exact h i hi

lemma top_bit (i : ℕ) (hi : i < 31) : top[i] = true := by
  rw [top, BitVec.getElem_allOnes]

lemma sep_mono_true (d : Bool) (a : Sig) (i : ℕ) (hi : i < 31) :
    (sep d a)[i] = true → (sep true a)[i] = true := by
  cases d
  · simp only [sep, Bool.false_eq_true, ↓reduceIte, BitVec.getElem_and, BitVec.getElem_not,
      BitVec.getElem_xor, Bool.and_eq_true, Bool.not_eq_true']
    intro h
    simp [h.1, h.2]
  · exact id

lemma sep_neg_true (a : Sig) (i : ℕ) (hi : i < 31) :
    (sep true (neg a))[i] = (sep true a)[i] := by
  simp only [sep, neg, ↓reduceIte, BitVec.getElem_xor, BitVec.getElem_not]
  cases a.1[i] <;> cases a.2[i] <;> rfl

lemma sep_bin_bit (d isOr : Bool) (a b : Sig) (i : ℕ) (hi : i < 31) :
    (sep d (bin isOr a b))[i] = true → (sep d a)[i] = true ∨ (sep d b)[i] = true := by
  cases d <;> cases isOr <;>
    simp only [sep, bin, ↓reduceIte, Bool.false_eq_true, BitVec.getElem_and,
      BitVec.getElem_or, BitVec.getElem_xor, BitVec.getElem_not] <;>
    cases a.1[i] <;> cases a.2[i] <;> cases b.1[i] <;> cases b.2[i] <;> decide

lemma unionSep_target_eq_top : unionSep false [target] = top := by decide

lemma dropped_perm {del v₁ v₂ : List Sig} (hp : v₁.Perm v₂) :
    (dropped del v₁).Perm (dropped del v₂) :=
  hp.filter _

lemma contains_perm {v₁ v₂ : List Sig} (hp : v₁.Perm v₂) (x : Sig) :
    v₁.contains x = v₂.contains x := by
  apply Bool.eq_iff_iff.2
  rw [List.contains_iff_mem, List.contains_iff_mem]
  exact hp.mem_iff

lemma list_any_eq_of_eq {α : Type} (l : List α) (f g : α → Bool)
    (h : ∀ a ∈ l, f a = g a) : l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.any_cons]
    rw [h a (by simp), ih (fun b hb => h b (by simp [hb]))]

lemma search_perm (allow : Sig → Bool) : ∀ k t {v₁ v₂ : List Sig}, v₁.Perm v₂ → search allow k t v₁ = search allow k t v₂ := by
  intro k
  induction k with
  | zero =>
    intro t v₁ v₂ hp
    exact contains_perm hp target
  | succ k ih =>
    intro t v₁ v₂ hp
    have htry : ∀ (t' : ℕ) (rest₁ rest₂ : List Sig) (g : Sig) (keep : List (List Sig)),
        rest₁.Perm rest₂ →
        tryGate allow k t' (search allow k t') v₁ rest₁ g keep =
          tryGate allow k t' (search allow k t') v₂ rest₂ g keep := by
      intro t' rest₁ rest₂ g keep hrest
      have hlen : rest₁.length = rest₂.length := hrest.length_eq
      have hcont : v₁.contains g = v₂.contains g := contains_perm hp g
      have husep : unionSep (decide (0 < t')) rest₁ = unionSep (decide (0 < t')) rest₂ :=
        unionSep_perm hrest
      simp only [tryGate, hcont, hlen, husep]
      congr 1
      refine list_any_eq_of_eq keep _ _ (fun h _ => ?_)
      have hp' : (g :: (h ++ rest₁)).Perm (g :: (h ++ rest₂)) :=
        List.Perm.cons g (List.Perm.append_left h hrest)
      rw [ih t' hp']
    have hcontT : v₁.contains target = v₂.contains target := contains_perm hp target
    have hunary : v₁.any (fun a => tryGate allow k (t - 1) (search allow k (t - 1)) v₁ (dropped [a] v₁) (neg a) [[], [a]]) =
        v₂.any (fun a => tryGate allow k (t - 1) (search allow k (t - 1)) v₂ (dropped [a] v₂) (neg a) [[], [a]]) := by
      apply Bool.eq_iff_iff.2
      rw [List.any_eq_true, List.any_eq_true]
      constructor
      · rintro ⟨a, ha, h⟩
        refine ⟨a, hp.mem_iff.1 ha, ?_⟩
        rw [← htry (t - 1) (dropped [a] v₁) (dropped [a] v₂) (neg a) [[], [a]] (dropped_perm hp)]
        exact h
      · rintro ⟨a, ha, h⟩
        refine ⟨a, hp.mem_iff.2 ha, ?_⟩
        rw [htry (t - 1) (dropped [a] v₁) (dropped [a] v₂) (neg a) [[], [a]] (dropped_perm hp)]
        exact h
    have hbinary :
        v₁.any (fun a => v₁.any (fun b => before a b &&
          (let rest := dropped [a, b] v₁
           let keep := [[], [a], [b], [a, b]]
           tryGate allow k t (search allow k t) v₁ rest (bin false a b) keep ||
           tryGate allow k t (search allow k t) v₁ rest (bin true a b) keep))) =
        v₂.any (fun a => v₂.any (fun b => before a b &&
          (let rest := dropped [a, b] v₂
           let keep := [[], [a], [b], [a, b]]
           tryGate allow k t (search allow k t) v₂ rest (bin false a b) keep ||
           tryGate allow k t (search allow k t) v₂ rest (bin true a b) keep))) := by
      apply Bool.eq_iff_iff.2
      simp only [List.any_eq_true]
      constructor
      · rintro ⟨a, ha, b, hb, h⟩
        refine ⟨a, hp.mem_iff.1 ha, b, hp.mem_iff.1 hb, ?_⟩
        have h1 := htry t (dropped [a, b] v₁) (dropped [a, b] v₂) (bin false a b)
          [[], [a], [b], [a, b]] (dropped_perm hp)
        have h2 := htry t (dropped [a, b] v₁) (dropped [a, b] v₂) (bin true a b)
          [[], [a], [b], [a, b]] (dropped_perm hp)
        simpa only [h1, h2] using h
      · rintro ⟨a, ha, b, hb, h⟩
        refine ⟨a, hp.mem_iff.2 ha, b, hp.mem_iff.2 hb, ?_⟩
        have h1 := htry t (dropped [a, b] v₁) (dropped [a, b] v₂) (bin false a b)
          [[], [a], [b], [a, b]] (dropped_perm hp)
        have h2 := htry t (dropped [a, b] v₁) (dropped [a, b] v₂) (bin true a b)
          [[], [a], [b], [a, b]] (dropped_perm hp)
        simpa only [h1, h2] using h
    simp only [search, hcontT, hunary, hbinary]

lemma getD_mem_of_ne {W : List Sig} {p : ℕ} (hne : W.getD p zero ≠ zero) :
    W.getD p zero ∈ W := by
  by_cases hp : p < W.length
  · rw [List.getD_eq_getElem _ _ hp]
    exact List.getElem_mem hp
  · rw [List.getD_eq_default _ _ (by omega)] at hne
    exact absurd rfl hne

lemma perm_of_nodup_same_mem {l₁ l₂ : List Sig} (h1 : l₁.Nodup) (h2 : l₂.Nodup)
    (hmem : ∀ x, x ∈ l₁ ↔ x ∈ l₂) : l₁.Perm l₂ :=
  (List.perm_ext_iff_of_nodup h1 h2).2 hmem

lemma mem_dropped_iff {del v : List Sig} {x : Sig} :
    x ∈ dropped del v ↔ x ∈ v ∧ x ∉ del := by
  simp only [dropped, List.mem_filter, Bool.not_eq_true']
  constructor
  · rintro ⟨hx, hnot⟩
    refine ⟨hx, fun hm => ?_⟩
    have hc : del.contains x = true := List.contains_iff_mem.2 hm
    rw [hc] at hnot
    cases hnot
  · rintro ⟨hx, hnot⟩
    refine ⟨hx, ?_⟩
    cases hc : del.contains x
    · rfl
    · exact absurd (List.contains_iff_mem.1 hc) hnot

lemma tryGate_eq_true (allow : Sig → Bool) {k t : ℕ} {r : List Sig → Bool} {v rest : List Sig} {g : Sig}
    {keep : List (List Sig)} (hag : allow g = true) (h0 : g ≠ zero) (h1 : g ≠ one) (hnot : g ∉ v)
    (h : List Sig) (hh : h ∈ keep)
    (hlen : rest.length + h.length + 1 ≤ k - t + 1)
    (hsep : (sep (decide (0 < t)) g ||| unionSep (decide (0 < t)) rest) |||
      unionSep (decide (0 < t)) h = top)
    (hr : r (g :: (h ++ rest)) = true) :
    tryGate allow k t r v rest g keep = true := by
  unfold tryGate
  have hb0 : (g != zero) = true := bne_iff_ne.2 h0
  have hb1 : (g != one) = true := bne_iff_ne.2 h1
  have hbn : (!v.contains g) = true := by
    cases hc : v.contains g
    · rfl
    · exact absurd (List.contains_iff_mem.1 hc) hnot
  rw [hag, hb0, hb1, hbn]
  simp only [Bool.true_and, List.any_eq_true]
  refine ⟨h, hh, ?_⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact ⟨⟨hlen, hsep⟩, hr⟩

lemma extract_binary_step (allow : Sig → Bool) {k t : ℕ} {isOr : Bool} {W V' U : List Sig} {sg a0 b0 : Sig}
    (hag : allow sg = true) (ht : t ≤ k) (hVnd : V'.Nodup) (hVlen : V'.length ≤ k - t + 1)
    (hVsep : unionSep (decide (0 < t)) V' = top) (hVsearch : search allow k t V' = true)
    (hsgW : sg ∉ W) (hsg0 : sg ≠ zero) (hsg1 : sg ≠ one)
    (hUnd : U.Nodup) (hsgU : sg ∉ U) (hPermV' : V'.Perm (sg :: U))
    (hUsub : ∀ s ∈ U, s ∈ W ∧ s ≠ zero ∧ s ≠ one) (hUlen : U.length + 1 = V'.length)
    (ha0W : a0 ∈ W) (hb0W : b0 ∈ W) (ha0_ne0 : a0 ≠ zero) (ha0_ne1 : a0 ≠ one)
    (hb0_ne0 : b0 ≠ zero) (hb0_ne1 : b0 ≠ one) (hab_ne : a0 ≠ b0)
    (hsgeq : sg = bin isOr a0 b0) :
    ∃ V : List Sig,
      V.Nodup ∧ (∀ s ∈ V, s ∈ W ∧ s ≠ zero ∧ s ≠ one) ∧
      V.length ≤ (k + 1) - t + 1 ∧ unionSep (decide (0 < t)) V = top ∧
      search allow (k + 1) t V = true := by
  obtain ⟨a, b, hab_ord, haW, hbW, ha0, ha1, hb0, hb1, hab, hbin⟩ :
      ∃ a b : Sig, before a b = true ∧ a ∈ W ∧ b ∈ W ∧ a ≠ zero ∧ a ≠ one ∧
        b ≠ zero ∧ b ≠ one ∧ a ≠ b ∧ sg = bin isOr a b := by
    rcases before_trichotomy hab_ne with h | h
    · exact ⟨a0, b0, h, ha0W, hb0W, ha0_ne0, ha0_ne1, hb0_ne0, hb0_ne1, hab_ne, hsgeq⟩
    · exact ⟨b0, a0, h, hb0W, ha0W, hb0_ne0, hb0_ne1, ha0_ne0, ha0_ne1, hab_ne.symm,
        by rw [hsgeq, bin_comm]⟩
  let addA : List Sig := if a ∈ U then [] else [a]
  let addB : List Sig := if b ∈ U then [] else [b]
  let V : List Sig := addA ++ addB ++ U
  have hV_mem : ∀ x, x ∈ V ↔ x = a ∨ x = b ∨ x ∈ U := by
    intro x
    simp only [V, addA, addB, List.mem_append]
    constructor
    · intro hx
      rcases hx with (hx | hx) | hx
      · split_ifs at hx
        · simp at hx
        · simp only [List.mem_singleton] at hx; exact Or.inl hx
      · split_ifs at hx
        · simp at hx
        · simp only [List.mem_singleton] at hx; exact Or.inr (Or.inl hx)
      · exact Or.inr (Or.inr hx)
    · rintro (rfl | rfl | hx)
      · by_cases haU : x ∈ U
        · exact Or.inr haU
        · exact Or.inl (Or.inl (by simp [haU]))
      · by_cases hbU : x ∈ U
        · exact Or.inr hbU
        · exact Or.inl (Or.inr (by simp [hbU]))
      · exact Or.inr hx
  have hV_nd : V.Nodup := by
    simp only [V, addA, addB]
    by_cases haU : a ∈ U <;> by_cases hbU : b ∈ U <;> simp [haU, hbU, hUnd, hab]
  have hV_sub : ∀ s ∈ V, s ∈ W ∧ s ≠ zero ∧ s ≠ one := by
    intro s hs
    rw [hV_mem] at hs
    rcases hs with rfl | rfl | hsU
    · exact ⟨haW, ha0, ha1⟩
    · exact ⟨hbW, hb0, hb1⟩
    · exact hUsub s hsU
  have hV_len : V.length ≤ (k + 1) - t + 1 := by
    have hA : addA.length ≤ 1 := by simp only [addA]; split_ifs <;> simp
    have hB : addB.length ≤ 1 := by simp only [addB]; split_ifs <;> simp
    have hlenV : V.length = addA.length + addB.length + U.length := by
      simp only [V, List.length_append]
    omega
  have hV_sep : unionSep (decide (0 < t)) V = top := by
    apply bv_eq_top_of_bits
    intro i hi
    rw [unionSep_bit_iff _ _ i hi]
    have htop : (unionSep (decide (0 < t)) V')[i] = true := by rw [hVsep]; exact top_bit i hi
    rw [unionSep_bit_iff _ _ i hi] at htop
    obtain ⟨s, hsV', hsi⟩ := htop
    rw [hPermV'.mem_iff, List.mem_cons] at hsV'
    rcases hsV' with rfl | hsU
    · rw [hbin] at hsi
      rcases sep_bin_bit _ _ a b i hi hsi with ha_b | hb_b
      · exact ⟨a, (hV_mem a).2 (Or.inl rfl), ha_b⟩
      · exact ⟨b, (hV_mem b).2 (Or.inr (Or.inl rfl)), hb_b⟩
    · exact ⟨s, (hV_mem s).2 (Or.inr (Or.inr hsU)), hsi⟩
  let hkeep : List Sig :=
    if a ∈ U then (if b ∈ U then [a, b] else [a]) else (if b ∈ U then [b] else [])
  have hhkeep_mem : hkeep ∈ [[], [a], [b], [a, b]] := by
    simp only [hkeep]; split_ifs <;> simp
  have hdrop_nd : (dropped [a, b] V).Nodup := hV_nd.filter _
  have hperm_next : (sg :: (hkeep ++ dropped [a, b] V)).Perm V' := by
    refine perm_of_nodup_same_mem ?_ hVnd ?_
    · have hsgV_not : sg ∉ V := fun h => hsgW (hV_sub sg h).1
      have hkh_nd : hkeep.Nodup := by
        simp only [hkeep]; split_ifs <;> simp [hab]
      rw [List.nodup_cons, List.nodup_append]
      refine ⟨?_, hkh_nd, hdrop_nd, ?_⟩
      · intro hm
        rw [List.mem_append] at hm
        rcases hm with hm | hm
        · apply hsgU
          simp only [hkeep] at hm
          split_ifs at hm <;> simp at hm <;> rcases hm with rfl | rfl <;> assumption
        · exact hsgV_not (mem_dropped_iff.1 hm).1
      · intro x hx y hy hxy
        subst hxy
        have hynot := (mem_dropped_iff.1 hy).2
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hynot
        simp only [hkeep] at hx
        split_ifs at hx <;> simp at hx <;> rcases hx with rfl | rfl
        · exact hynot.1 rfl
        · exact hynot.2 rfl
        · exact hynot.1 rfl
        · exact hynot.2 rfl
    · intro x
      rw [hPermV'.mem_iff, List.mem_cons, List.mem_cons, List.mem_append]
      constructor
      · rintro (rfl | hx | hx)
        · exact Or.inl rfl
        · right
          simp only [hkeep] at hx
          split_ifs at hx <;> simp at hx <;> rcases hx with rfl | rfl <;> assumption
        · right
          have hx' := mem_dropped_iff.1 hx
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx'
          rw [hV_mem] at hx'
          rcases hx'.1 with rfl | rfl | hxU
          · exact absurd rfl hx'.2.1
          · exact absurd rfl hx'.2.2
          · exact hxU
      · rintro (rfl | hxU)
        · exact Or.inl rfl
        · right
          by_cases hxa : x = a
          · subst hxa; left; simp only [hkeep]; split_ifs <;> simp
          · by_cases hxb : x = b
            · subst hxb; left; simp only [hkeep]; split_ifs <;> simp
            · right
              rw [mem_dropped_iff]
              simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
              exact ⟨(hV_mem x).2 (Or.inr (Or.inr hxU)), hxa, hxb⟩
  have htry_ok : tryGate allow k t (search allow k t) V (dropped [a, b] V) (bin isOr a b)
      [[], [a], [b], [a, b]] = true := by
    have hsg_notV : sg ∉ V := fun h => hsgW (hV_sub sg h).1
    rw [← hbin]
    refine tryGate_eq_true allow hag hsg0 hsg1 hsg_notV hkeep hhkeep_mem ?_ ?_ ?_
    · have := hperm_next.length_eq
      simp only [List.length_cons, List.length_append] at this
      omega
    · have husep := unionSep_perm (d := decide (0 < t)) hperm_next
      rw [hVsep] at husep
      simp only [unionSep, unionSep_append] at husep
      rw [BitVec.or_assoc, BitVec.or_comm (unionSep _ (dropped [a, b] V)) (unionSep _ hkeep)]
      exact husep
    · rw [search_perm allow k t hperm_next]
      exact hVsearch
  have hsearch_new : search allow (k + 1) t V = true := by
    simp only [search, Bool.or_eq_true]
    right
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
    refine ⟨ht, a, (hV_mem a).2 (Or.inl rfl), b, (hV_mem b).2 (Or.inr (Or.inl rfl)),
      hab_ord, ?_⟩
    cases isOr
    · simp only [Bool.or_eq_true]; exact Or.inl htry_ok
    · simp only [Bool.or_eq_true]; exact Or.inr htry_ok
  exact ⟨V, hV_nd, hV_sub, hV_len, hV_sep, hsearch_new⟩

lemma prefixMem (gs : List Gate) (W : List Sig) (z : Sig) (hz : z ∈ W) :
    z ∈ evalGates gs W := by
  induction gs generalizing W with
  | nil => exact hz
  | cons g gs ih => exact ih (W ++ [evalGateSig g W]) (List.mem_append_left _ hz)

lemma extract_live (allow : Sig → Bool) (gs : List Gate) (hfan : ∀ g ∈ gs,
    g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ W : List Sig, (∀ z ∈ evalGates gs W, allow z = true) → target ∈ evalGates gs W →
      ∃ k ≤ gs.length, ∃ t ≤ k, ∃ V : List Sig,
        V.Nodup ∧ (∀ s ∈ V, s ∈ W ∧ s ≠ zero ∧ s ≠ one) ∧
        V.length ≤ k - t + 1 ∧ unionSep (decide (0 < t)) V = top ∧
        search allow k t V = true := by
  induction gs with
  | nil =>
    intro W hall hT
    refine ⟨0, le_rfl, 0, le_rfl, [target], by simp, ?_, by simp, unionSep_target_eq_top, ?_⟩
    · intro s hs
      simp only [List.mem_singleton] at hs
      subst hs
      exact ⟨hT, target_ne_zero, target_ne_one⟩
    · exact List.contains_iff_mem.2 (List.mem_singleton_self target)
  | cons g rest ih =>
    intro W hall hT
    have hg := hfan g List.mem_cons_self
    have hrest : ∀ g' ∈ rest,
        g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hfan g' (List.mem_cons_of_mem g hg')
    rw [evalGates_cons] at hT
    set sg := evalGateSig g W
    obtain ⟨k, hk, t, ht, V', hVnd, hVsub, hVlen, hVsep, hVsearch⟩ := ih hrest (W ++ [sg]) hall hT
    have hag : allow sg = true := hall sg (prefixMem rest (W ++ [sg]) sg (by simp))
    by_cases hskip : sg ∉ V' ∨ sg ∈ W
    · refine ⟨k, by simp; omega, t, ht, V', hVnd, ?_, hVlen, hVsep, hVsearch⟩
      intro s hs
      obtain ⟨hsmem, hs0, hs1⟩ := hVsub s hs
      rw [List.mem_append, List.mem_singleton] at hsmem
      rcases hsmem with hsmem | rfl
      · exact ⟨hsmem, hs0, hs1⟩
      · rcases hskip with hnot | hin
        · exact absurd hs hnot
        · exact ⟨hin, hs0, hs1⟩
    · push Not at hskip
      obtain ⟨hsgV, hsgW⟩ := hskip
      have hsg01 := hVsub sg hsgV
      have hsg0 : sg ≠ zero := hsg01.2.1
      have hsg1 : sg ≠ one := hsg01.2.2
      set U := V'.erase sg
      have hUnd : U.Nodup := hVnd.erase sg
      have hsgU : sg ∉ U := List.Nodup.not_mem_erase hVnd
      have hPermV' : V'.Perm (sg :: U) := List.perm_cons_erase hsgV
      have hUsub : ∀ s ∈ U, s ∈ W ∧ s ≠ zero ∧ s ≠ one := by
        intro s hs
        have hsV : s ∈ V' := List.mem_of_mem_erase hs
        have hsne : s ≠ sg := fun h => hsgU (h ▸ hs)
        obtain ⟨hsm, hs0, hs1⟩ := hVsub s hsV
        rw [List.mem_append, List.mem_singleton] at hsm
        exact ⟨hsm.resolve_right hsne, hs0, hs1⟩
      have hUlen : U.length + 1 = V'.length := by
        have := hPermV'.length_eq
        simp at this
        omega
      rcases hg with ⟨hop, hinlen⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      rcases hop with hop | hop | hop
      · rcases hin : g.inputs with _ | ⟨p, _ | ⟨q, _ | _⟩⟩
        · exfalso; apply hsg1; simp [sg, evalGateSig, hop, hin]
        · exfalso
          have hsgeq : sg = W.getD p zero := by simp [sg, evalGateSig, hop, hin]
          rw [hsgeq] at hsg0 hsgW
          exact hsgW (getD_mem_of_ne hsg0)
        · have hsgeq : sg = bin false (W.getD p zero) (W.getD q zero) := by
            simp [sg, evalGateSig, hop, hin]
          set a0 := W.getD p zero
          set b0 := W.getD q zero
          have ha0_ne0 : a0 ≠ zero := by
            intro h; apply hsg0; rw [hsgeq, h, bin_zero_left]; rfl
          have hb0_ne0 : b0 ≠ zero := by
            intro h; apply hsg0; rw [hsgeq, h, bin_zero_right]; rfl
          have ha0W : a0 ∈ W := getD_mem_of_ne ha0_ne0
          have hb0W : b0 ∈ W := getD_mem_of_ne hb0_ne0
          have ha0_ne1 : a0 ≠ one := by
            intro h; apply hsgW; rw [hsgeq, h, bin_one_left]; simpa using hb0W
          have hb0_ne1 : b0 ≠ one := by
            intro h; apply hsgW; rw [hsgeq, h, bin_one_right]; simpa using ha0W
          have hab_ne : a0 ≠ b0 := by
            intro h; apply hsgW; rw [hsgeq, h, bin_self]; exact hb0W
          obtain ⟨V, hV⟩ := extract_binary_step allow hag ht hVnd hVlen hVsep hVsearch hsgW hsg0 hsg1
            hUnd hsgU hPermV' hUsub hUlen ha0W hb0W ha0_ne0 ha0_ne1 hb0_ne0 hb0_ne1 hab_ne hsgeq
          exact ⟨k + 1, by simp; omega, t, by omega, V, hV⟩
        · rw [hin] at hinlen; simp at hinlen
      · rcases hin : g.inputs with _ | ⟨p, _ | ⟨q, _ | _⟩⟩
        · exfalso; apply hsg0; simp [sg, evalGateSig, hop, hin]
        · exfalso
          have hsgeq : sg = W.getD p zero := by simp [sg, evalGateSig, hop, hin]
          rw [hsgeq] at hsg0 hsgW
          exact hsgW (getD_mem_of_ne hsg0)
        · have hsgeq : sg = bin true (W.getD p zero) (W.getD q zero) := by
            simp [sg, evalGateSig, hop, hin]
          set a0 := W.getD p zero
          set b0 := W.getD q zero
          have ha0_ne0 : a0 ≠ zero := by
            intro h
            have hsgeq' : sg = b0 := by rw [hsgeq, h, bin_zero_left]; rfl
            rw [hsgeq'] at hsg0 hsgW
            exact hsgW (getD_mem_of_ne hsg0)
          have hb0_ne0 : b0 ≠ zero := by
            intro h
            have hsgeq' : sg = a0 := by rw [hsgeq, h, bin_zero_right]; rfl
            rw [hsgeq'] at hsg0 hsgW
            exact hsgW (getD_mem_of_ne hsg0)
          have ha0W : a0 ∈ W := getD_mem_of_ne ha0_ne0
          have hb0W : b0 ∈ W := getD_mem_of_ne hb0_ne0
          have ha0_ne1 : a0 ≠ one := by
            intro h; apply hsg1; rw [hsgeq, h, bin_one_left]; rfl
          have hb0_ne1 : b0 ≠ one := by
            intro h; apply hsg1; rw [hsgeq, h, bin_one_right]; rfl
          have hab_ne : a0 ≠ b0 := by
            intro h; apply hsgW; rw [hsgeq, h, bin_self]; exact hb0W
          obtain ⟨V, hV⟩ := extract_binary_step allow hag ht hVnd hVlen hVsep hVsearch hsgW hsg0 hsg1
            hUnd hsgU hPermV' hUsub hUlen ha0W hb0W ha0_ne0 ha0_ne1 hb0_ne0 hb0_ne1 hab_ne hsgeq
          exact ⟨k + 1, by simp; omega, t, by omega, V, hV⟩
        · rw [hin] at hinlen; simp at hinlen
      · rcases hin : g.inputs with _ | ⟨p, _⟩
        · exfalso; apply hsg1; simp [sg, evalGateSig, hop, hin]
        · have hsgeq : sg = neg (W.getD p zero) := by simp [sg, evalGateSig, hop, hin]
          set a := W.getD p zero
          have ha0 : a ≠ zero := by intro h; apply hsg1; rw [hsgeq, h, neg_zero]
          have ha1 : a ≠ one := by intro h; apply hsg0; rw [hsgeq, h, neg_one]
          have haW : a ∈ W := getD_mem_of_ne ha0
          let V : List Sig := if a ∈ U then U else a :: U
          have hV_mem : ∀ x, x ∈ V ↔ x = a ∨ x ∈ U := by
            intro x
            simp only [V]
            by_cases haU : a ∈ U
            · simp only [haU, ↓reduceIte]
              exact ⟨Or.inr, fun h => h.elim (fun hxa => hxa ▸ haU) id⟩
            · simp only [haU, ↓reduceIte, List.mem_cons]
          have hV_nd : V.Nodup := by
            simp only [V]
            by_cases haU : a ∈ U <;> simp [haU, hUnd]
          have hV_sub : ∀ s ∈ V, s ∈ W ∧ s ≠ zero ∧ s ≠ one := by
            intro s hs
            rw [hV_mem] at hs
            rcases hs with rfl | hsU
            · exact ⟨haW, ha0, ha1⟩
            · exact hUsub s hsU
          have hV_len : V.length ≤ (k + 1) - (t + 1) + 1 := by
            have : V.length ≤ U.length + 1 := by simp only [V]; split_ifs <;> simp
            omega
          have hV_sep : unionSep (decide (0 < t + 1)) V = top := by
            apply bv_eq_top_of_bits
            intro i hi
            rw [unionSep_bit_iff _ _ i hi]
            have htop : (unionSep (decide (0 < t)) V')[i] = true := by rw [hVsep]; exact top_bit i hi
            rw [unionSep_bit_iff _ _ i hi] at htop
            obtain ⟨s, hsV', hsi⟩ := htop
            have hsi' : (sep true s)[i] = true := sep_mono_true _ s i hi hsi
            rw [hPermV'.mem_iff, List.mem_cons] at hsV'
            rcases hsV' with rfl | hsU
            · rw [hsgeq, sep_neg_true a i hi] at hsi'
              exact ⟨a, (hV_mem a).2 (Or.inl rfl), by simpa using hsi'⟩
            · exact ⟨s, (hV_mem s).2 (Or.inr hsU), by simpa using hsi'⟩
          let hkeep : List Sig := if a ∈ U then [a] else []
          have hhkeep_mem : hkeep ∈ [[], [a]] := by simp only [hkeep]; split_ifs <;> simp
          have hdrop_nd : (dropped [a] V).Nodup := hV_nd.filter _
          have hperm_next : (sg :: (hkeep ++ dropped [a] V)).Perm V' := by
            refine perm_of_nodup_same_mem ?_ hVnd ?_
            · have hsgV_not : sg ∉ V := fun h => hsgW (hV_sub sg h).1
              have hkh_nd : hkeep.Nodup := by simp only [hkeep]; split_ifs <;> simp
              rw [List.nodup_cons, List.nodup_append]
              refine ⟨?_, hkh_nd, hdrop_nd, ?_⟩
              · intro hm
                rw [List.mem_append] at hm
                rcases hm with hm | hm
                · apply hsgU
                  simp only [hkeep] at hm
                  split_ifs at hm <;> simp at hm
                  rw [hm]; assumption
                · exact hsgV_not (mem_dropped_iff.1 hm).1
              · intro x hx y hy hxy
                subst hxy
                have hynot := (mem_dropped_iff.1 hy).2
                simp only [List.mem_singleton] at hynot
                simp only [hkeep] at hx
                split_ifs at hx <;> simp at hx
                exact hynot hx
            · intro x
              rw [hPermV'.mem_iff, List.mem_cons, List.mem_cons, List.mem_append]
              constructor
              · rintro (rfl | hx | hx)
                · exact Or.inl rfl
                · right
                  simp only [hkeep] at hx
                  split_ifs at hx <;> simp at hx
                  subst hx; assumption
                · right
                  have hx' := mem_dropped_iff.1 hx
                  simp only [List.mem_singleton] at hx'
                  rw [hV_mem] at hx'
                  exact hx'.1.resolve_left hx'.2
              · rintro (rfl | hxU)
                · exact Or.inl rfl
                · right
                  by_cases hxa : x = a
                  · subst hxa; left; simp only [hkeep]; split_ifs; simp
                  · right
                    rw [mem_dropped_iff]
                    simp only [List.mem_singleton]
                    exact ⟨(hV_mem x).2 (Or.inr hxU), hxa⟩
          have hsearch_new : search allow (k + 1) (t + 1) V = true := by
            simp only [search, Bool.or_eq_true]
            left
            right
            simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
            refine ⟨by omega, a, (hV_mem a).2 (Or.inl rfl), ?_⟩
            simp only [Nat.add_sub_cancel]
            have hsg_notV : sg ∉ V := fun h => hsgW (hV_sub sg h).1
            rw [← hsgeq]
            refine tryGate_eq_true allow hag hsg0 hsg1 hsg_notV hkeep hhkeep_mem ?_ ?_ ?_
            · have := hperm_next.length_eq
              simp only [List.length_cons, List.length_append] at this
              omega
            · have husep := unionSep_perm (d := decide (0 < t)) hperm_next
              rw [hVsep] at husep
              simp only [unionSep, unionSep_append] at husep
              rw [BitVec.or_assoc, BitVec.or_comm (unionSep _ (dropped [a] V)) (unionSep _ hkeep)]
              exact husep
            · rw [search_perm allow k t hperm_next]
              exact hVsearch
          exact ⟨k + 1, by simp; omega, t + 1, by omega, V, hV_nd, hV_sub, hV_len, hV_sep, hsearch_new⟩

lemma wiresToSigs_getD (wa wb : Fin 31 → List Bool) (len : ℕ)
    (hwa : ∀ r, (wa r).length = len) (hwb : ∀ r, (wb r).length = len) (i : ℕ) :
    (wiresToSigs wa wb len).getD i zero =
      (mkBV (fun r => (wa r).getD i false),
       mkBV (fun r => (wb r).getD i false)) := by
  by_cases hi : i < len
  · have hlen : (wiresToSigs wa wb len).length = len := by simp [wiresToSigs]
    rw [List.getD_eq_getElem _ _ (by omega)]
    simp [wiresToSigs]
  · have hlen : (wiresToSigs wa wb len).length = len := by simp [wiresToSigs]
    rw [List.getD_eq_default _ _ (by omega)]
    apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro r hr
    · simp only [zero, getElem_mkBV]
      rw [zero_bit r hr, List.getD_eq_default _ _ (by rw [hwa ⟨r, hr⟩]; omega)]
    · simp only [zero, getElem_mkBV]
      rw [zero_bit r hr, List.getD_eq_default _ _ (by rw [hwb ⟨r, hr⟩]; omega)]

lemma wiresToSigs_step (wa wb : Fin 31 → List Bool) (len : ℕ)
    (hwa : ∀ r, (wa r).length = len) (hwb : ∀ r, (wb r).length = len)
    (g : Gate) (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    wiresToSigs
      (fun r => wa r ++ [g.op.eval (g.inputs.map fun i => (wa r).getD i false)])
      (fun r => wb r ++ [g.op.eval (g.inputs.map fun i => (wb r).getD i false)])
      (len + 1) =
    wiresToSigs wa wb len ++ [evalGateSig g (wiresToSigs wa wb len)] := by
  have hprefix :
      (List.range len).map (fun idx =>
        (mkBV (fun r => (wa r ++ [g.op.eval (g.inputs.map fun i => (wa r).getD i false)]).getD idx false),
         mkBV (fun r => (wb r ++ [g.op.eval (g.inputs.map fun i => (wb r).getD i false)]).getD idx false))) =
      wiresToSigs wa wb len := by
    unfold wiresToSigs
    apply List.map_congr_left
    intro idx hidx
    rw [List.mem_range] at hidx
    apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro r hr
    · simp only [getElem_mkBV]
      rw [List.getD_eq_getElem _ _ (by simp [hwa ⟨r, hr⟩]; omega),
        List.getElem_append_left (by rw [hwa ⟨r, hr⟩]; omega),
        List.getD_eq_getElem _ _ (by rw [hwa ⟨r, hr⟩]; omega)]
    · simp only [getElem_mkBV]
      rw [List.getD_eq_getElem _ _ (by simp [hwb ⟨r, hr⟩]; omega),
        List.getElem_append_left (by rw [hwb ⟨r, hr⟩]; omega),
        List.getD_eq_getElem _ _ (by rw [hwb ⟨r, hr⟩]; omega)]
  have hlast :
      (mkBV (fun r => (wa r ++ [g.op.eval (g.inputs.map fun i => (wa r).getD i false)]).getD len false),
       mkBV (fun r => (wb r ++ [g.op.eval (g.inputs.map fun i => (wb r).getD i false)]).getD len false)) =
      evalGateSig g (wiresToSigs wa wb len) := by
    have hgetLast : ∀ (w : List Bool) (v : Bool), w.length = len → (w ++ [v]).getD len false = v := by
      intro w v hw
      rw [List.getD_eq_getElem _ _ (by simp [hw]), List.getElem_append_right (by omega)]
      simp [hw]
    have hA : (fun r => (wa r ++ [g.op.eval (g.inputs.map fun i => (wa r).getD i false)]).getD len false) =
        fun r => g.op.eval (g.inputs.map fun i => (wa r).getD i false) := by
      funext r; exact hgetLast (wa r) _ (hwa r)
    have hB : (fun r => (wb r ++ [g.op.eval (g.inputs.map fun i => (wb r).getD i false)]).getD len false) =
        fun r => g.op.eval (g.inputs.map fun i => (wb r).getD i false) := by
      funext r; exact hgetLast (wb r) _ (hwb r)
    rw [hA, hB]
    rcases hg with ⟨hop, hinlen⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with hop | hop | hop
    · rcases hin : g.inputs with _ | ⟨p, _ | ⟨q, _ | _⟩⟩
      · simp only [evalGateSig, hop, hin, GateOp.eval, List.map_nil, List.all_nil]
        apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro r hr <;>
          simp only [one, top, getElem_mkBV, BitVec.getElem_allOnes]
      · simp only [evalGateSig, hop, hin, GateOp.eval, List.map_cons, List.map_nil,
          List.all_cons, List.all_nil, id_eq, Bool.and_true]
        exact (wiresToSigs_getD wa wb len hwa hwb p).symm
      · simp only [evalGateSig, hop, hin, GateOp.eval, List.map_cons, List.map_nil,
          List.all_cons, List.all_nil, id_eq, Bool.and_true]
        rw [wiresToSigs_getD wa wb len hwa hwb p, wiresToSigs_getD wa wb len hwa hwb q]
        apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro r hr <;>
          simp only [bin, Bool.false_eq_true, ↓reduceIte, BitVec.getElem_and, getElem_mkBV]
      · rw [hin] at hinlen; simp at hinlen
    · rcases hin : g.inputs with _ | ⟨p, _ | ⟨q, _ | _⟩⟩
      · simp only [evalGateSig, hop, hin, GateOp.eval, List.map_nil, List.any_nil]
        apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro r hr <;>
          (simp only [zero, getElem_mkBV]; exact (zero_bit r hr).symm)
      · simp only [evalGateSig, hop, hin, GateOp.eval, List.map_cons, List.map_nil,
          List.any_cons, List.any_nil, id_eq, Bool.or_false]
        exact (wiresToSigs_getD wa wb len hwa hwb p).symm
      · simp only [evalGateSig, hop, hin, GateOp.eval, List.map_cons, List.map_nil,
          List.any_cons, List.any_nil, id_eq, Bool.or_false]
        rw [wiresToSigs_getD wa wb len hwa hwb p, wiresToSigs_getD wa wb len hwa hwb q]
        apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro r hr <;>
          simp only [bin, ↓reduceIte, BitVec.getElem_or, getElem_mkBV]
      · rw [hin] at hinlen; simp at hinlen
    · rcases hin : g.inputs with _ | ⟨p, _⟩
      · simp only [evalGateSig, hop, hin, GateOp.eval, List.map_nil, List.headD_nil, Bool.not_false]
        apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro r hr <;>
          simp only [one, top, getElem_mkBV, BitVec.getElem_allOnes]
      · simp only [evalGateSig, hop, hin, GateOp.eval, List.map_cons, List.headD_cons]
        rw [wiresToSigs_getD wa wb len hwa hwb p]
        apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro r hr <;>
          simp only [neg, BitVec.getElem_not, getElem_mkBV]
  show (List.range (len + 1)).map _ = _
  rw [List.range_succ, List.map_append, List.map_singleton, hprefix, hlast]

lemma evalWires_len (gs : List Gate) (w : List Bool) :
    (evalWires gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [evalWires]
  | cons g rest ih =>
    rw [evalWires_cons, ih]
    simp
    omega

lemma wiresToSigs_evalGates (gs : List Gate)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ (wa wb : Fin 31 → List Bool) (len : ℕ),
      (∀ r, (wa r).length = len) → (∀ r, (wb r).length = len) →
      wiresToSigs (fun r => evalWires gs (wa r)) (fun r => evalWires gs (wb r)) (len + gs.length) =
        evalGates gs (wiresToSigs wa wb len) := by
  induction gs with
  | nil =>
    intro wa wb len _ _
    simp [evalWires, evalGates]
  | cons g rest ih =>
    intro wa wb len hwa hwb
    have hg := hfan g List.mem_cons_self
    have hrest : ∀ g' ∈ rest,
        g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hfan g' (List.mem_cons_of_mem g hg')
    have h1 := ih hrest
      (fun r => wa r ++ [g.op.eval (g.inputs.map fun i => (wa r).getD i false)])
      (fun r => wb r ++ [g.op.eval (g.inputs.map fun i => (wb r).getD i false)])
      (len + 1)
      (fun r => by simp [hwa r])
      (fun r => by simp [hwb r])
    simp only [List.length_cons]
    rw [show len + (rest.length + 1) = len + 1 + rest.length by omega]
    have hwa_eq : (fun r => evalWires (g :: rest) (wa r)) =
        (fun r => evalWires rest (wa r ++ [g.op.eval (g.inputs.map fun i => (wa r).getD i false)])) := rfl
    have hwb_eq : (fun r => evalWires (g :: rest) (wb r)) =
        (fun r => evalWires rest (wb r ++ [g.op.eval (g.inputs.map fun i => (wb r).getD i false)])) := rfl
    rw [hwa_eq, hwb_eq, evalGates_cons, h1, wiresToSigs_step wa wb len hwa hwb g hg]

def enumGate (k t : ℕ) (r : List Sig → List (List Sig)) (v rest : List Sig)
    (g : Sig) (keep : List (List Sig)) : List (List Sig) :=
  if g != zero && g != one && !v.contains g then
    let d := decide (0 < t)
    let base := sep d g ||| unionSep d rest
    keep.flatMap (fun h =>
      if decide (rest.length + h.length + 1 ≤ k - t + 1) && (base ||| unionSep d h == top)
      then (r (g :: (h ++ rest))).map (g :: ·) else [])
  else []

def enumerate : ℕ → ℕ → List Sig → List (List Sig)
  | 0, _, v => if v.contains target then [[]] else []
  | k+1, t, v =>
    (if v.contains target then [[]] else []) ++
    (if 0 < t then v.flatMap (fun a =>
      enumGate k (t-1) (enumerate k (t-1)) v (dropped [a] v) (neg a) [[],[a]]) else []) ++
    (if t ≤ k then v.flatMap (fun a => v.flatMap (fun b =>
      if before a b then
        let rest := dropped [a,b] v
        let keep := [[],[a],[b],[a,b]]
        enumGate k t (enumerate k t) v rest (bin false a b) keep ++
          enumGate k t (enumerate k t) v rest (bin true a b) keep
      else [])) else [])

def signature (f : (Fin 5 → Bool) → Bool) : Sig :=
  (mkBV (fun r => f (pairA r)), mkBV (fun r => f (pairB r)))

def known : List ((Fin 5 → Bool) → Bool) :=
  [fun _ => false, fun _ => true] ++ List.ofFn (fun i : Fin 5 => fun x => x i)

def rawSig (p : Fin 5) : Sig := initList.getD p.val zero

def slice (p : Fin 5) (b : Bool) : Sig :=
  if b then rawSig p else neg (rawSig p)

def masked (a s : Sig) : Sig := (a.1 &&& s.1, a.2 &&& s.2)

def removable (p : Fin 5) (b : Bool) (s : Sig) : Bool :=
  !initList.contains s &&
  (zero :: one :: initList).any (fun a => masked (slice p b) s == masked (slice p b) a)

def counted (p : Fin 5) (b : Bool) (trace : List Sig) : Finset Sig :=
  trace.toFinset.filter (fun s => removable p b s = true)

def need (b : Bool) : ℕ := if b then 4 else 3

def good (trace : List Sig) : Bool :=
  decide (∃ (p : Fin 5) (b : Bool), need b ≤ (counted p b trace).card)

lemma enum_any_flat {α β} (l : List α) (f : α → List β) (p : β → Bool) :
    (l.flatMap f).any p = l.any (fun x => (f x).any p) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

lemma enum_any_if {α} (P : Prop) [Decidable P] (l : List α) (f : α → Bool) :
    (if P then l else []).any f = (decide P && l.any f) := by by_cases h : P <;> simp [h]

lemma enum_bool_if {α} (b : Bool) (l : List α) (f : α → Bool) :
    (if b then l else []).any f = (b && l.any f) := by cases b <;> simp

lemma enum_any_prefix (g : Sig) (l : List (List Sig)) (allow : Sig → Bool) :
    (l.map (g :: ·)).any (List.all · allow) = (allow g && l.any (List.all · allow)) := by
  cases h : allow g <;> induction l with
  | nil => simp
  | cons a l ih => simp [h, ih]

lemma enum_any_and {α} (l : List α) (b : Bool) (f : α → Bool) :
    (l.any fun a => b && f a) = (b && l.any f) := by cases b <;> simp

lemma enumGate_search (allow : Sig → Bool) (k t : ℕ) (r : List Sig → List (List Sig))
    (v rest : List Sig) (g : Sig) (keep : List (List Sig)) :
    (enumGate k t r v rest g keep).any (List.all · allow) =
    tryGate allow k t (fun u => (r u).any (List.all · allow)) v rest g keep := by
  cases h : allow g <;>
    simp only [enumGate, tryGate, enum_bool_if, enum_any_flat, enum_any_prefix, h,
      Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true] <;> simp

lemma enumerate_search (allow : Sig → Bool) (k t : ℕ) (v : List Sig) :
    (enumerate k t v).any (List.all · allow) = search allow k t v := by
  induction k generalizing t v with
  | zero => simp [enumerate, search, enum_any_if]
  | succ k ih =>
    simp only [enumerate, List.any_append, enum_any_if, enum_any_flat, enumGate_search, ih]
    simp [search]

open PEqualNP.CircuitLowerBounds

lemma allInputsCovered : ∀ x : Fin 5 → Bool, (∃ r, x = pairA r) ∨ ∃ r, x = pairB r := by decide

lemma initSignatures : List.ofFn (fun i : Fin 5 => signature (fun x => x i)) = initList := by decide

lemma rawSignature (p : Fin 5) : rawSig p = signature (fun x => x p) := by
  fin_cases p <;> decide

lemma sigFalse : signature (fun _ => false) = zero := by decide
lemma sigTrue : signature (fun _ => true) = one := by decide

lemma masked_eq_on {f h : (Fin 5 → Bool) → Bool} {p : Fin 5} {b : Bool}
    (he : masked (slice p b) (signature f) = masked (slice p b) (signature h))
    (x : Fin 5 → Bool) (hx : x p = b) : f x = h x := by
  rcases allInputsCovered x with ⟨r,rfl⟩ | ⟨r,rfl⟩
  · have e := congrArg (fun s : Sig => s.1[r.val]) he
    cases b <;> simpa [masked, slice, rawSignature, signature, neg, getElem_mkBV, hx] using e
  · have e := congrArg (fun s : Sig => s.2[r.val]) he
    cases b <;> simpa [masked, slice, rawSignature, signature, neg, getElem_mkBV, hx] using e

def wireFn (C : Circuit) (j : ℕ) (x : Fin 5 → Bool) : Bool :=
  (C.wires (List.ofFn x)).getD j false

def gateSig (C : Circuit) (j : Fin 7) : Sig := signature (wireFn C (5+j.val))

lemma sigAt (C : Circuit) (j : ℕ) (hf : ∀ g ∈ C.gates,
    g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (evalGates C.gates initList).getD j zero = signature (wireFn C j) := by
  have h := wiresToSigs_evalGates C.gates hf
    (fun r => List.ofFn (pairA r)) (fun r => List.ofFn (pairB r)) 5 (by simp) (by simp)
  rw [initList_eq] at h
  rw [← h, wiresToSigs_getD]
  · rfl
  · intro r; rw [evalWires_len]; simp
  · intro r; rw [evalWires_len]; simp

lemma lengthSigs (gs : List Gate) (W : List Sig) :
    (evalGates gs W).length = W.length + gs.length := by
  induction gs generalizing W with
  | nil => simp [evalGates]
  | cons g rest ih => rw [evalGates_cons, ih]; simp; omega

lemma wiresPrefix (gs : List Gate) (x : List Bool) : x <+: evalWires gs x := by
  induction gs generalizing x with
  | nil => exact List.prefix_refl _
  | cons g rest ih => exact (List.prefix_append _ _).trans (ih _)

lemma wireRaw (C : Circuit) (x : Fin 5 → Bool) (i : Fin 5) : wireFn C i.val x = x i := by
  obtain ⟨tail, h⟩ := wiresPrefix C.gates (List.ofFn x)
  change (evalWires C.gates (List.ofFn x)).getD i.val false = x i
  rw [← h]
  fin_cases i <;> rfl

lemma applyRemovable (C : Circuit) (j : Fin 7) (p : Fin 5) (b : Bool)
    (hr : removable p b (gateSig C j) = true) :
    (∀ y z : Fin 5 → Bool, y p = b → z p = b →
       wireFn C (5+j.val) y = wireFn C (5+j.val) z) ∨
    ∃ w < 5+j.val, ∀ u : Fin 5 → Bool, u p = b → wireFn C (5+j.val) u = wireFn C w u := by
  simp only [removable, Bool.and_eq_true, List.any_eq_true, beq_iff_eq] at hr
  obtain ⟨a,ha,he⟩ := hr.2
  simp only [List.mem_cons] at ha
  rcases ha with rfl | rfl | ha
  · rw [← sigFalse] at he
    exact Or.inl (fun y z hy hz => (masked_eq_on he y hy).trans (masked_eq_on he z hz).symm)
  · rw [← sigTrue] at he
    exact Or.inl (fun y z hy hz => (masked_eq_on he y hy).trans (masked_eq_on he z hz).symm)
  · rw [← initSignatures, List.mem_ofFn] at ha
    obtain ⟨i,rfl⟩ := ha
    refine Or.inr ⟨i.val, by omega, fun u hu => ?_⟩
    rw [wireRaw]
    exact masked_eq_on he u hu

set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
lemma checked40 : (enumerate 4 0 initList).all good = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
lemma checked50 : (enumerate 5 0 initList).all good = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
lemma checked51 : (enumerate 5 1 initList).all good = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
lemma checked60 : (enumerate 6 0 initList).all good = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
lemma checked61 : (enumerate 6 1 initList).all good = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
lemma checked62 : (enumerate 6 2 initList).all good = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
lemma checked71 : (enumerate 7 1 initList).all good = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
lemma checked72 : (enumerate 7 2 initList).all good = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
lemma checked73 : (enumerate 7 3 initList).all good = true := by decide +kernel

def firstCellAt (v : List Sig) (a b : Sig) : List (List Sig) :=
  if before a b then
    let rest := dropped [a,b] v
    let keep := [[],[a],[b],[a,b]]
    enumGate 6 0 (enumerate 6 0) v rest (bin false a b) keep ++
      enumGate 6 0 (enumerate 6 0) v rest (bin true a b) keep
  else []

def firstCell := firstCellAt initList

lemma aggregateAt (v : List Sig) (hn : v.contains target = false)
    (cells : ∀ a ∈ v, ∀ b ∈ v, (firstCellAt v a b).all good = true) :
    (enumerate 7 0 v).all good = true := by
  change (((if v.contains target then [[]] else []) ++ [] ++
    v.flatMap (fun a => v.flatMap (firstCellAt v a))).all good) = true
  rw [hn]
  simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, List.all_eq_true,
    List.mem_flatMap, forall_exists_index, and_imp]
  intro tr a ha b hb htr
  exact List.all_eq_true.mp (cells a ha b hb) tr htr

lemma aggregateTest (cells : ∀ i j : Fin 5, (firstCell (rawSig i) (rawSig j)).all good = true) :
    (enumerate 7 0 initList).all good = true := by
  apply aggregateAt initList (by decide)
  intro a ha b hb
  have hi : List.ofFn rawSig = initList := by decide
  rw [← hi, List.mem_ofFn] at ha hb
  obtain ⟨i,rfl⟩ := ha
  obtain ⟨j,rfl⟩ := hb
  exact cells i j
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
lemma first00 : (firstCell (rawSig 0) (rawSig 0)).all good = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
lemma first01 : (firstCell (rawSig 0) (rawSig 1)).all good = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
lemma first02 : (firstCell (rawSig 0) (rawSig 2)).all good = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
lemma first03 : (firstCell (rawSig 0) (rawSig 3)).all good = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
lemma first04 : (firstCell (rawSig 0) (rawSig 4)).all good = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
lemma first10 : (firstCell (rawSig 1) (rawSig 0)).all good = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
lemma first11 : (firstCell (rawSig 1) (rawSig 1)).all good = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
lemma first12 : (firstCell (rawSig 1) (rawSig 2)).all good = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
lemma first13 : (firstCell (rawSig 1) (rawSig 3)).all good = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
lemma first14 : (firstCell (rawSig 1) (rawSig 4)).all good = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
lemma first20 : (firstCell (rawSig 2) (rawSig 0)).all good = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
lemma first21 : (firstCell (rawSig 2) (rawSig 1)).all good = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
lemma first22 : (firstCell (rawSig 2) (rawSig 2)).all good = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
lemma first23 : (firstCell (rawSig 2) (rawSig 3)).all good = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
lemma first24 : (firstCell (rawSig 2) (rawSig 4)).all good = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
lemma first30 : (firstCell (rawSig 3) (rawSig 0)).all good = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
lemma first31 : (firstCell (rawSig 3) (rawSig 1)).all good = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
lemma first32 : (firstCell (rawSig 3) (rawSig 2)).all good = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
lemma first33 : (firstCell (rawSig 3) (rawSig 3)).all good = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
lemma first34 : (firstCell (rawSig 3) (rawSig 4)).all good = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
lemma first40 : (firstCell (rawSig 4) (rawSig 0)).all good = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
lemma first41 : (firstCell (rawSig 4) (rawSig 1)).all good = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
lemma first42 : (firstCell (rawSig 4) (rawSig 2)).all good = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
lemma first43 : (firstCell (rawSig 4) (rawSig 3)).all good = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
lemma first44 : (firstCell (rawSig 4) (rawSig 4)).all good = true := by decide +kernel
set_option maxHeartbeats 3000000 in
lemma checked70 : (enumerate 7 0 initList).all good = true := by
  have cells : ∀ i j : Fin 5, (firstCell (rawSig i) (rawSig j)).all good = true := by
    intro i j
    fin_cases i
    · fin_cases j
      · exact first00
      · exact first01
      · exact first02
      · exact first03
      · exact first04
    · fin_cases j
      · exact first10
      · exact first11
      · exact first12
      · exact first13
      · exact first14
    · fin_cases j
      · exact first20
      · exact first21
      · exact first22
      · exact first23
      · exact first24
    · fin_cases j
      · exact first30
      · exact first31
      · exact first32
      · exact first33
      · exact first34
    · fin_cases j
      · exact first40
      · exact first41
      · exact first42
      · exact first43
      · exact first44
  exact aggregateTest cells

open PEqualNP.CircuitLowerBounds
lemma complete (cert : ∀ k t, k ≤ 7 → t ≤ k → 5 ≤ k-t+1 →
    (enumerate k t initList).all good = true) :
∀ C : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → C.size = 7 → (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = true ↔ ∃ i : Fin 5, x i = true ∧ x (i + 1) = true) → ∃ (p : Fin 5) (b : Bool) (S : Finset (Fin 7)), (if b = true then 4 else 3) ≤ S.card ∧ ∀ j ∈ S, (∀ y z : Fin 5 → Bool, y p = b → z p = b → (C.wires (List.ofFn y)).getD (5 + ((j : Fin 7) : ℕ)) false = (C.wires (List.ofFn z)).getD (5 + ((j : Fin 7) : ℕ)) false) ∨ ∃ w < 5 + ((j : Fin 7) : ℕ), ∀ u : Fin 5 → Bool, u p = b → (C.wires (List.ofFn u)).getD (5 + ((j : Fin 7) : ℕ)) false = (C.wires (List.ofFn u)).getD w false := by
  intro C ops size correct
  have hlen : C.gates.length = 7 := size
  have hfan : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2 := fun g hg => ⟨(ops g hg).1, (ops g hg).2⟩
  have accepts (r : Fin 31) : C.eval (List.ofFn (pairA r)) = true :=
    (correct _).mpr (of_decide_eq_true (pairA_true r))
  have rejects (r : Fin 31) : C.eval (List.ofFn (pairB r)) = false := by
    have hn := of_decide_eq_false (pairB_false r)
    cases h : C.eval (List.ofFn (pairB r)) with
    | false => rfl
    | true => exact False.elim (hn ((correct _).mp h))
  let W := evalGates C.gates initList
  let allow : Sig → Bool := W.contains
  have hW := wiresToSigs_evalGates C.gates hfan
    (fun r => List.ofFn (pairA r)) (fun r => List.ofFn (pairB r)) 5
    (fun r => by simp) (fun r => by simp)
  have htarget_eq : (evalGates C.gates initList).getD C.output zero = target := by
    rw [← initList_eq, ← hW]
    rw [wiresToSigs_getD _ _ (5 + C.gates.length)
      (fun r => by rw [evalWires_len]; simp)
      (fun r => by rw [evalWires_len]; simp) C.output]
    apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro r hr
    · simp only [target, top, getElem_mkBV, BitVec.getElem_allOnes]
      exact accepts ⟨r, hr⟩
    · simp only [target, getElem_mkBV]
      rw [zero_bit r hr]
      exact rejects ⟨r, hr⟩
  have hTmem : target ∈ evalGates C.gates initList :=
    htarget_eq ▸ getD_mem_of_ne (by rw [htarget_eq]; exact target_ne_zero)
  obtain ⟨k, hk, t, ht, V, hVnd, hVsub, hVlen, hVsep, hVsearch⟩ :=
    extract_live allow C.gates hfan initList (fun _ h => List.contains_iff_mem.2 h) hTmem
  have hVsep_true : unionSep true V = top := by
    apply bv_eq_top_of_bits
    intro i hi
    rw [unionSep_bit_iff _ _ i hi]
    have htop : (unionSep (decide (0 < t)) V)[i] = true := by rw [hVsep]; exact top_bit i hi
    rw [unionSep_bit_iff _ _ i hi] at htop
    obtain ⟨s, hs, hsi⟩ := htop
    exact ⟨s, hs, sep_mono_true _ s i hi hsi⟩
  have hall_in_V : ∀ s ∈ initList, s ∈ V := by
    intro s hs
    by_contra hnot
    apply all_init_needed s hs
    apply bv_eq_top_of_bits
    intro i hi
    rw [unionSep_bit_iff _ _ i hi]
    have htop : (unionSep true V)[i] = true := by rw [hVsep_true]; exact top_bit i hi
    rw [unionSep_bit_iff _ _ i hi] at htop
    obtain ⟨u, huV, hui⟩ := htop
    have huInit : u ∈ initList := (hVsub u huV).1
    have hune : u ≠ s := fun h => hnot (h ▸ huV)
    exact ⟨u, (List.mem_erase_of_ne hune).2 huInit, hui⟩
  have hPermInit : V.Perm initList :=
    perm_of_nodup_same_mem hVnd initList_nodup (fun x => ⟨fun h => (hVsub x h).1, hall_in_V x⟩)
  have hVlen5 : V.length = 5 := hPermInit.length_eq.trans initList_len
  have hk7 : k ≤ 7 := by omega
  have hsearch_init : search allow k t initList = true := by
    rw [← search_perm allow k t hPermInit]
    exact hVsearch
  rw [← enumerate_search, List.any_eq_true] at hsearch_init
  obtain ⟨path, hpath, hallowed⟩ := hsearch_init
  have cg := List.all_eq_true.mp (cert k t hk7 ht (by omega)) path hpath
  obtain ⟨p,b,hcard⟩ := of_decide_eq_true cg
  let S : Finset (Fin 7) := Finset.univ.filter (fun j => removable p b (gateSig C j) = true)
  have cover : counted p b path ⊆ S.image (gateSig C) := by
    intro s hs
    obtain ⟨hm,hr⟩ := Finset.mem_filter.mp hs
    have ha := List.all_eq_true.mp hallowed s (List.mem_toFinset.mp hm)
    have hw : s ∈ W := List.contains_iff_mem.mp ha
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hw
    have eqi : W.getD i zero = s := by simpa [List.getD_eq_getElem?_getD, hi] using he
    have hnot : s ∉ initList := by
      intro hsinit
      have hc : initList.contains s = true := List.contains_iff_mem.mpr hsinit
      simp only [removable, hc, Bool.not_true, Bool.false_and, Bool.false_eq_true] at hr
    have hil : i < 12 := by simpa [W, lengthSigs, initList_len, hlen] using hi
    have eqsig := (sigAt C i hfan).symm.trans eqi
    have hi5 : 5 ≤ i := by
      by_contra! small
      let q : Fin 5 := ⟨i,small⟩
      have eqf : wireFn C i = fun x => x q := funext (fun x => wireRaw C x q)
      apply hnot
      rw [← eqsig, eqf, ← initSignatures]
      exact List.mem_ofFn.mpr ⟨q,rfl⟩
    let j : Fin 7 := ⟨i-5, by omega⟩
    have ej : gateSig C j = s := by
      unfold gateSig
      rw [show 5+j.val = i by dsimp [j]; omega]
      exact eqsig
    exact Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ej ▸ hr⟩,ej⟩
  refine ⟨p,b,S,hcard.trans ((Finset.card_le_card cover).trans Finset.card_image_le),?_⟩
  intro j hj
  exact applyRemovable C j p b (Finset.mem_filter.mp hj).2

lemma allChecked (k t : ℕ) (hk : k ≤ 7) (ht : t ≤ k) (hlen : 5 ≤ k-t+1) :
    (enumerate k t initList).all good = true := by
  have choices : (k = 4 ∧ t = 0) ∨ (k = 5 ∧ t = 0) ∨ (k = 5 ∧ t = 1) ∨ (k = 6 ∧ t = 0) ∨ (k = 6 ∧ t = 1) ∨ (k = 6 ∧ t = 2) ∨ (k = 7 ∧ t = 0) ∨ (k = 7 ∧ t = 1) ∨ (k = 7 ∧ t = 2) ∨ (k = 7 ∧ t = 3) := by omega
  rcases choices with ⟨rfl,rfl⟩ |
    ⟨rfl,rfl⟩ |
    ⟨rfl,rfl⟩ |
    ⟨rfl,rfl⟩ |
    ⟨rfl,rfl⟩ |
    ⟨rfl,rfl⟩ |
    ⟨rfl,rfl⟩ |
    ⟨rfl,rfl⟩ |
    ⟨rfl,rfl⟩ |
    ⟨rfl,rfl⟩
  · exact checked40
  · exact checked50
  · exact checked51
  · exact checked60
  · exact checked61
  · exact checked62
  · exact checked70
  · exact checked71
  · exact checked72
  · exact checked73

end PEqualNP.Outside.L_meta_1409_aux

theorem PEqualNP.Outside.L_meta_1409 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → C.size = 7 → (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = true ↔ ∃ i : Fin 5, x i = true ∧ x (i + 1) = true) → ∃ (p : Fin 5) (b : Bool) (S : Finset (Fin 7)), (if b = true then 4 else 3) ≤ S.card ∧ ∀ j ∈ S, (∀ y z : Fin 5 → Bool, y p = b → z p = b → (C.wires (List.ofFn y)).getD (5 + ((j : Fin 7) : ℕ)) false = (C.wires (List.ofFn z)).getD (5 + ((j : Fin 7) : ℕ)) false) ∨ ∃ w < 5 + ((j : Fin 7) : ℕ), ∀ u : Fin 5 → Bool, u p = b → (C.wires (List.ofFn u)).getD (5 + ((j : Fin 7) : ℕ)) false = (C.wires (List.ofFn u)).getD w false := by
  exact PEqualNP.Outside.L_meta_1409_aux.complete PEqualNP.Outside.L_meta_1409_aux.allChecked
