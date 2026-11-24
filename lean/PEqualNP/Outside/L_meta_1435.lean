import Mathlib
import PEqualNP.Defs

-- The search adapts Astro's proof of L-meta-163, based on Vivek Rajkumar's signature search.

namespace PEqualNP.Outside.L_meta_1435_aux

open PEqualNP.CircuitLowerBounds

abbrev B := BitVec 256
abbrev Sig := B × B

def mkBVLoop : ℕ → (ℕ → Bool) → ℕ
  | 0, _ => 0
  | n + 1, p => 2 * mkBVLoop n (fun k => p (k + 1)) + if p 0 then 1 else 0

def mkBV (p : Fin 256 → Bool) : B :=
  BitVec.ofNat 256 (mkBVLoop 256 (fun i => if h : i < 256 then p ⟨i, h⟩ else false))

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

lemma getElem_mkBV (p : Fin 256 → Bool) (i : ℕ) (hi : i < 256) :
    (mkBV p)[i] = p ⟨i, hi⟩ := by
  unfold mkBV
  rw [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat, Nat.testBit_mod_two_pow]
  simp only [decide_eq_true hi, Bool.true_and]
  rw [testBit_mkBVLoop 256 _ i hi]
  simp [hi]

lemma zero_bit (i : ℕ) (hi : i < 256) : (0 : B)[i] = false := by simp

def top : B := BitVec.allOnes 256
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

def tryGate (k t : ℕ) (r : List Sig → Bool) (v rest : List Sig) (g : Sig)
    (keep : List (List Sig)) : Bool :=
  g != zero && g != one && !v.contains g &&
    (let d := decide (0 < t)
     let base := sep d g ||| unionSep d rest
     keep.any (fun h => decide (rest.length + h.length + 1 ≤ k - t + 1) &&
       (base ||| unionSep d h == top) && r (g :: (h ++ rest))))

def search : ℕ → ℕ → List Sig → Bool
  | 0, _, v => v.contains target
  | k + 1, t, v =>
    v.contains target ||
    (decide (0 < t) &&
      v.any (fun a => tryGate k (t - 1) (search k (t - 1)) v (dropped [a] v) (neg a) [[], [a]])) ||
    (decide (t ≤ k) &&
      v.any (fun a => v.any (fun b =>
        before a b &&
        (let rest := dropped [a, b] v
         let keep := [[], [a], [b], [a, b]]
         tryGate k t (search k t) v rest (bin false a b) keep ||
         tryGate k t (search k t) v rest (bin true a b) keep))))

def wiresToSigs (wa wb : Fin 256 → List Bool) (len : ℕ) : List Sig :=
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

lemma target_ne_zero : target ≠ zero := by decide
lemma target_ne_one : target ≠ one := by decide

def cellNot (k t : ℕ) (v : List Sig) (a : Sig) : Bool :=
  tryGate k (t - 1) (search k (t - 1)) v (dropped [a] v) (neg a) [[], [a]]

def cell (k t : ℕ) (v : List Sig) (a b : Sig) : Bool :=
  before a b &&
    (let rest := dropped [a, b] v
     let keep := [[], [a], [b], [a, b]]
     tryGate k t (search k t) v rest (bin false a b) keep ||
     tryGate k t (search k t) v rest (bin true a b) keep)

lemma search_succ (k t : ℕ) (v : List Sig) :
    search (k + 1) t v = (v.contains target ||
      (decide (0 < t) && v.any (fun a => cellNot k t v a)) ||
      (decide (t ≤ k) && v.any (fun a => v.any (fun b => cell k t v a b)))) := rfl

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

lemma unionSep_bit_iff (d : Bool) (v : List Sig) (i : ℕ) (hi : i < 256) :
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

lemma bv_eq_top_of_bits {x : B} (h : ∀ i (hi : i < 256), x[i] = true) : x = top := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  rw [top, BitVec.getElem_allOnes]
  exact h i hi

lemma top_bit (i : ℕ) (hi : i < 256) : top[i] = true := by
  rw [top, BitVec.getElem_allOnes]

lemma sep_mono_true (d : Bool) (a : Sig) (i : ℕ) (hi : i < 256) :
    (sep d a)[i] = true → (sep true a)[i] = true := by
  cases d
  · simp only [sep, Bool.false_eq_true, ↓reduceIte, BitVec.getElem_and, BitVec.getElem_not,
      BitVec.getElem_xor, Bool.and_eq_true, Bool.not_eq_true']
    intro h
    simp [h.1, h.2]
  · exact id

lemma sep_neg_true (a : Sig) (i : ℕ) (hi : i < 256) :
    (sep true (neg a))[i] = (sep true a)[i] := by
  simp only [sep, neg, ↓reduceIte, BitVec.getElem_xor, BitVec.getElem_not]
  cases a.1[i] <;> cases a.2[i] <;> rfl

lemma sep_bin_bit (d isOr : Bool) (a b : Sig) (i : ℕ) (hi : i < 256) :
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

lemma search_perm : ∀ k t {v₁ v₂ : List Sig}, v₁.Perm v₂ → search k t v₁ = search k t v₂ := by
  intro k
  induction k with
  | zero =>
    intro t v₁ v₂ hp
    exact contains_perm hp target
  | succ k ih =>
    intro t v₁ v₂ hp
    have htry : ∀ (t' : ℕ) (rest₁ rest₂ : List Sig) (g : Sig) (keep : List (List Sig)),
        rest₁.Perm rest₂ →
        tryGate k t' (search k t') v₁ rest₁ g keep =
          tryGate k t' (search k t') v₂ rest₂ g keep := by
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
    have hunary : v₁.any (fun a => tryGate k (t - 1) (search k (t - 1)) v₁ (dropped [a] v₁) (neg a) [[], [a]]) =
        v₂.any (fun a => tryGate k (t - 1) (search k (t - 1)) v₂ (dropped [a] v₂) (neg a) [[], [a]]) := by
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
           tryGate k t (search k t) v₁ rest (bin false a b) keep ||
           tryGate k t (search k t) v₁ rest (bin true a b) keep))) =
        v₂.any (fun a => v₂.any (fun b => before a b &&
          (let rest := dropped [a, b] v₂
           let keep := [[], [a], [b], [a, b]]
           tryGate k t (search k t) v₂ rest (bin false a b) keep ||
           tryGate k t (search k t) v₂ rest (bin true a b) keep))) := by
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

lemma tryGate_eq_true {k t : ℕ} {r : List Sig → Bool} {v rest : List Sig} {g : Sig}
    {keep : List (List Sig)} (h0 : g ≠ zero) (h1 : g ≠ one) (hnot : g ∉ v)
    (h : List Sig) (hh : h ∈ keep)
    (hlen : rest.length + h.length + 1 ≤ k - t + 1)
    (hsep : (sep (decide (0 < t)) g ||| unionSep (decide (0 < t)) rest) |||
      unionSep (decide (0 < t)) h = top)
    (hr : r (g :: (h ++ rest)) = true) :
    tryGate k t r v rest g keep = true := by
  unfold tryGate
  have hb0 : (g != zero) = true := bne_iff_ne.2 h0
  have hb1 : (g != one) = true := bne_iff_ne.2 h1
  have hbn : (!v.contains g) = true := by
    cases hc : v.contains g
    · rfl
    · exact absurd (List.contains_iff_mem.1 hc) hnot
  rw [hb0, hb1, hbn]
  simp only [Bool.true_and, List.any_eq_true]
  refine ⟨h, hh, ?_⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact ⟨⟨hlen, hsep⟩, hr⟩

lemma extract_binary_step {k t : ℕ} {isOr : Bool} {W V' U : List Sig} {sg a0 b0 : Sig}
    (ht : t ≤ k) (hVnd : V'.Nodup) (hVlen : V'.length ≤ k - t + 1)
    (hVsep : unionSep (decide (0 < t)) V' = top) (hVsearch : search k t V' = true)
    (hsgW : sg ∉ W) (hsg0 : sg ≠ zero) (hsg1 : sg ≠ one)
    (hUnd : U.Nodup) (hsgU : sg ∉ U) (hPermV' : V'.Perm (sg :: U))
    (hUsub : ∀ s ∈ U, s ∈ W ∧ s ≠ zero ∧ s ≠ one) (hUlen : U.length + 1 = V'.length)
    (ha0W : a0 ∈ W) (hb0W : b0 ∈ W) (ha0_ne0 : a0 ≠ zero) (ha0_ne1 : a0 ≠ one)
    (hb0_ne0 : b0 ≠ zero) (hb0_ne1 : b0 ≠ one) (hab_ne : a0 ≠ b0)
    (hsgeq : sg = bin isOr a0 b0) :
    ∃ V : List Sig,
      V.Nodup ∧ (∀ s ∈ V, s ∈ W ∧ s ≠ zero ∧ s ≠ one) ∧
      V.length ≤ (k + 1) - t + 1 ∧ unionSep (decide (0 < t)) V = top ∧
      search (k + 1) t V = true := by
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
  have htry_ok : tryGate k t (search k t) V (dropped [a, b] V) (bin isOr a b)
      [[], [a], [b], [a, b]] = true := by
    have hsg_notV : sg ∉ V := fun h => hsgW (hV_sub sg h).1
    rw [← hbin]
    refine tryGate_eq_true hsg0 hsg1 hsg_notV hkeep hhkeep_mem ?_ ?_ ?_
    · have := hperm_next.length_eq
      simp only [List.length_cons, List.length_append] at this
      omega
    · have husep := unionSep_perm (d := decide (0 < t)) hperm_next
      rw [hVsep] at husep
      simp only [unionSep, unionSep_append] at husep
      rw [BitVec.or_assoc, BitVec.or_comm (unionSep _ (dropped [a, b] V)) (unionSep _ hkeep)]
      exact husep
    · rw [search_perm k t hperm_next]
      exact hVsearch
  have hsearch_new : search (k + 1) t V = true := by
    simp only [search, Bool.or_eq_true]
    right
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
    refine ⟨ht, a, (hV_mem a).2 (Or.inl rfl), b, (hV_mem b).2 (Or.inr (Or.inl rfl)),
      hab_ord, ?_⟩
    cases isOr
    · simp only [Bool.or_eq_true]; exact Or.inl htry_ok
    · simp only [Bool.or_eq_true]; exact Or.inr htry_ok
  exact ⟨V, hV_nd, hV_sub, hV_len, hV_sep, hsearch_new⟩

def isNotGate (g : Gate) : Bool :=
  match g.op with
  | .not => true
  | _ => false

lemma isNotGate_iff (g : Gate) : isNotGate g = true ↔ g.op = GateOp.not := by
  cases g with
  | mk op ins => cases op <;> simp [isNotGate]

lemma notCount_le_one (gs : List Gate)
    (unique : ∀ i j : Fin gs.length, (gs.get i).op = GateOp.not →
      (gs.get j).op = GateOp.not → i = j) : gs.countP isNotGate ≤ 1 := by
  induction gs with
  | nil => simp
  | cons g rest ih =>
    by_cases head : isNotGate g = true
    · have tailZero : rest.countP isNotGate = 0 := by
        apply List.countP_eq_zero.mpr
        intro a ha haNot
        obtain ⟨i, hi⟩ := List.mem_iff_get.mp ha
        have h0 : (⟨0, by simp⟩ : Fin (g :: rest).length) = i.succ :=
          unique _ _ ((isNotGate_iff g).mp head)
            (show (rest.get i).op = GateOp.not from hi ▸ (isNotGate_iff a).mp haNot)
        have hval := congrArg Fin.val h0
        simp at hval
      simp [head, tailZero]
    · rw [List.countP_cons_of_neg head]
      apply ih
      intro i j hi hj
      exact Fin.succ_inj.mp (unique i.succ j.succ hi hj)

lemma extract_live (gs : List Gate) (hfan : ∀ g ∈ gs,
    g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ W : List Sig, target ∈ evalGates gs W →
      ∃ k ≤ gs.length, ∃ t ≤ k, t ≤ gs.countP isNotGate ∧ k + gs.countP isNotGate ≤ gs.length + t ∧ ∃ V : List Sig,
        V.Nodup ∧ (∀ s ∈ V, s ∈ W ∧ s ≠ zero ∧ s ≠ one) ∧
        V.length ≤ k - t + 1 ∧ unionSep (decide (0 < t)) V = top ∧
        search k t V = true := by
  induction gs with
  | nil =>
    intro W hT
    refine ⟨0, le_rfl, 0, le_rfl, by simp, by simp, [target], by simp, ?_, by simp, unionSep_target_eq_top, ?_⟩
    · intro s hs
      simp only [List.mem_singleton] at hs
      subst hs
      exact ⟨hT, target_ne_zero, target_ne_one⟩
    · exact List.contains_iff_mem.2 (List.mem_singleton_self target)
  | cons g rest ih =>
    intro W hT
    have hg := hfan g List.mem_cons_self
    have hrest : ∀ g' ∈ rest,
        g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hfan g' (List.mem_cons_of_mem g hg')
    rw [evalGates_cons] at hT
    set sg := evalGateSig g W
    obtain ⟨k, hk, t, ht, hbudget, hbinary, V', hVnd, hVsub, hVlen, hVsep, hVsearch⟩ := ih hrest (W ++ [sg]) hT
    have hbudget' : t ≤ (g :: rest).countP isNotGate := by
      rw [List.countP_cons]
      split <;> omega
    have hnewBin : k + (g :: rest).countP isNotGate ≤ (g :: rest).length + t := by
      rw [List.countP_cons, List.length_cons]
      split <;> omega
    by_cases hskip : sg ∉ V' ∨ sg ∈ W
    · refine ⟨k, by simp; omega, t, ht, hbudget', hnewBin, V', hVnd, ?_, hVlen, hVsep, hVsearch⟩
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
          obtain ⟨V, hV⟩ := extract_binary_step ht hVnd hVlen hVsep hVsearch hsgW hsg0 hsg1
            hUnd hsgU hPermV' hUsub hUlen ha0W hb0W ha0_ne0 ha0_ne1 hb0_ne0 hb0_ne1 hab_ne hsgeq
          have hpos : ¬isNotGate g = true := by rw [isNotGate_iff, hop]; intro h; cases h
          exact ⟨k + 1, by simp; omega, t, by omega, hbudget',
            by rw [List.countP_cons_of_neg hpos, List.length_cons]; omega, V, hV⟩
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
          obtain ⟨V, hV⟩ := extract_binary_step ht hVnd hVlen hVsep hVsearch hsgW hsg0 hsg1
            hUnd hsgU hPermV' hUsub hUlen ha0W hb0W ha0_ne0 ha0_ne1 hb0_ne0 hb0_ne1 hab_ne hsgeq
          have hpos : ¬isNotGate g = true := by rw [isNotGate_iff, hop]; intro h; cases h
          exact ⟨k + 1, by simp; omega, t, by omega, hbudget',
            by rw [List.countP_cons_of_neg hpos, List.length_cons]; omega, V, hV⟩
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
          have hsearch_new : search (k + 1) (t + 1) V = true := by
            simp only [search, Bool.or_eq_true]
            left
            right
            simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
            refine ⟨by omega, a, (hV_mem a).2 (Or.inl rfl), ?_⟩
            simp only [Nat.add_sub_cancel]
            have hsg_notV : sg ∉ V := fun h => hsgW (hV_sub sg h).1
            rw [← hsgeq]
            refine tryGate_eq_true hsg0 hsg1 hsg_notV hkeep hhkeep_mem ?_ ?_ ?_
            · have := hperm_next.length_eq
              simp only [List.length_cons, List.length_append] at this
              omega
            · have husep := unionSep_perm (d := decide (0 < t)) hperm_next
              rw [hVsep] at husep
              simp only [unionSep, unionSep_append] at husep
              rw [BitVec.or_assoc, BitVec.or_comm (unionSep _ (dropped [a] V)) (unionSep _ hkeep)]
              exact husep
            · rw [search_perm k t hperm_next]
              exact hVsearch
          exact ⟨k + 1, by simp; omega, t + 1, by omega, by simpa [(isNotGate_iff g).mpr hop] using Nat.succ_le_succ hbudget,
            by rw [List.countP_cons_of_pos ((isNotGate_iff g).mpr hop), List.length_cons]; omega,
            V, hV_nd, hV_sub, hV_len, hV_sep, hsearch_new⟩

lemma wiresToSigs_getD (wa wb : Fin 256 → List Bool) (len : ℕ)
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

lemma wiresToSigs_step (wa wb : Fin 256 → List Bool) (len : ℕ)
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
    ∀ (wa wb : Fin 256 → List Bool) (len : ℕ),
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

def wireX (v : List Sig) (side : Bool) (r : Fin 256) (i : Fin 5) : Bool :=
  (if side then (v.getD i zero).1 else (v.getD i zero).2)[r.val]

lemma wiresToSigs_init (v : List Sig) (hv : v.length = 5) :
    wiresToSigs (fun r => List.ofFn (wireX v true r))
      (fun r => List.ofFn (wireX v false r)) 5 = v := by
  apply List.ext_getElem
  · simp [wiresToSigs, hv]
  · intro i hi hj
    have hi5 : i < 5 := by omega
    simp only [wiresToSigs, List.getElem_map, List.getElem_range]
    apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro r hr
    all_goals
      simp only [getElem_mkBV, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi5,
        ↓reduceDIte, Option.getD_some, wireX, List.getElem?_eq_getElem hj, Bool.true_eq,
        ↓reduceIte, Bool.false_eq_true]

def sampleMask (x : Fin 5 → Bool) : ℕ :=
  ∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0

lemma sample_lower (C : Circuit) (v : List Sig) (bound table : ℕ)
    (hfan : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2)
    (hnot : C.gates.countP isNotGate = 1)
    (hcorrect : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit table (sampleMask x))
    (hlenv : v.length = 5) (hnd : v.Nodup)
    (essential : v.all (fun s => unionSep true (v.erase s) != top) = true)
    (positive : ∀ r : Fin 256, Nat.testBit table (sampleMask (wireX v true r)) = true)
    (negative : ∀ r : Fin 256, Nat.testBit table (sampleMask (wireX v false r)) = false)
    (noRun : ∀ k t, k < bound → t ≤ k → t ≤ 1 → k + 1 < bound + t → 5 ≤ k - t + 1 → search k t v = false) :
    bound ≤ C.size := by
  by_contra small
  have hlen : C.gates.length < bound := by
    change ¬ bound ≤ C.gates.length at small
    omega
  let pairA := wireX v true
  let pairB := wireX v false
  have initList_eq := wiresToSigs_init v hlenv
  have all_init_needed : ∀ s ∈ v, unionSep true (v.erase s) ≠ top :=
    fun s hs => bne_iff_ne.1 (List.all_eq_true.1 essential s hs)
  have accepts (r : Fin 256) := (hcorrect (pairA r)).trans (positive r)
  have rejects (r : Fin 256) := (hcorrect (pairB r)).trans (negative r)
  have hW := wiresToSigs_evalGates C.gates hfan
    (fun r => List.ofFn (pairA r)) (fun r => List.ofFn (pairB r)) 5
    (fun r => by simp) (fun r => by simp)
  have htarget_eq : (evalGates C.gates v).getD C.output zero = target := by
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
  have hTmem : target ∈ evalGates C.gates v :=
    htarget_eq ▸ getD_mem_of_ne (by rw [htarget_eq]; exact target_ne_zero)
  obtain ⟨k, hk, t, ht, hbudget, hbinary, V, hVnd, hVsub, hVlen, hVsep, hVsearch⟩ :=
    extract_live C.gates hfan v hTmem
  have hVsep_true : unionSep true V = top := by
    apply bv_eq_top_of_bits
    intro i hi
    rw [unionSep_bit_iff _ _ i hi]
    have htop : (unionSep (decide (0 < t)) V)[i] = true := by rw [hVsep]; exact top_bit i hi
    rw [unionSep_bit_iff _ _ i hi] at htop
    obtain ⟨s, hs, hsi⟩ := htop
    exact ⟨s, hs, sep_mono_true _ s i hi hsi⟩
  have hall_in_V : ∀ s ∈ v, s ∈ V := by
    intro s hs
    by_contra hnot
    apply all_init_needed s hs
    apply bv_eq_top_of_bits
    intro i hi
    rw [unionSep_bit_iff _ _ i hi]
    have htop : (unionSep true V)[i] = true := by rw [hVsep_true]; exact top_bit i hi
    rw [unionSep_bit_iff _ _ i hi] at htop
    obtain ⟨u, huV, hui⟩ := htop
    have huInit : u ∈ v := (hVsub u huV).1
    have hune : u ≠ s := fun h => hnot (h ▸ huV)
    exact ⟨u, (List.mem_erase_of_ne hune).2 huInit, hui⟩
  have hPermInit : V.Perm v :=
    perm_of_nodup_same_mem hVnd hnd (fun x => ⟨fun h => (hVsub x h).1, hall_in_V x⟩)
  have hVlen5 : V.length = 5 := hPermInit.length_eq.trans hlenv
  have hsearch_init : search k t v = true := by
    rw [← search_perm k t hPermInit]
    exact hVsearch
  have hn := noRun k t (lt_of_le_of_lt hk hlen) ht (by omega) (by omega) (hVlen5 ▸ hVlen)
  simp [hn] at hsearch_init

def v_eae8eac8 : List Sig :=
  [(115790322444171310373542681253754569961897231065817539637364944762444921733119, 936457522748154905461174688781465974337490338950613405879581889159733248530),
   (115792089183397947543611745237842025222448760636234904045687841661471141396479, 16403908756969566306229331718202132274998604352485839358841581620677289583684),
   (115792089237314549919015196298186618729390971924278393167557591395193124257792, 90732132548378306698748644233239734430574464897081035859098886019323513292952),
   (115792089237316195423569452513147041964412955546609198646146869040666854293504, 108952415519282030066891348744021766746363522208889951786325769870295530762464),
   (115792089237316195423570985008687907853268655437644779123584680200852849295360, 115341529485805290704905702847104372337315154408220929287572124797090993831680)]

set_option maxRecDepth 10000 in
lemma nodup_eae8eac8 : v_eae8eac8.Nodup := by decide +kernel

set_option maxRecDepth 10000 in
lemma len_eae8eac8 : v_eae8eac8.length = 5 := by decide +kernel

set_option maxRecDepth 10000 in
lemma ess_eae8eac8 : v_eae8eac8.all (fun s => unionSep true (v_eae8eac8.erase s) != top) = true := by decide +kernel

set_option maxRecDepth 10000 in
lemma pos_eae8eac8 : ∀ r : Fin 256, Nat.testBit 0xeae8eac8 (sampleMask (wireX v_eae8eac8 true r)) = true := by decide +kernel

set_option maxRecDepth 10000 in
lemma neg_eae8eac8 : ∀ r : Fin 256, Nat.testBit 0xeae8eac8 (sampleMask (wireX v_eae8eac8 false r)) = false := by decide +kernel

def v_eaeaea88 : List Sig :=
  [(115790322444171310373542681253754569961897231106379883002368646712747861475327, 31804217753710921317549329052955448185046841700209511897797120763915468818),
   (115792089183397947543611745237842025222447431448805176201602006129307482587135, 16573531251656024553256261473151227998652187508220290088963166264751505417380),
   (115792089237314549919015196298186618729389642736847427496765807342296603000832, 91014836706189070443793527158154893969997103489971787075968193759447206349112),
   (115792089237316195423569452513147041964411626359178232937577306116684374867968, 109348201340217099309954184838902990101555216238937003489942800706468701041088),
   (115792089237316195423570985008687907853269984625075744832154243160018627067904, 114889202833308068712833890167240117074238932659595727340581232412893084941824)]

set_option maxRecDepth 10000 in
lemma nodup_eaeaea88 : v_eaeaea88.Nodup := by decide +kernel

set_option maxRecDepth 10000 in
lemma len_eaeaea88 : v_eaeaea88.length = 5 := by decide +kernel

set_option maxRecDepth 10000 in
lemma ess_eaeaea88 : v_eaeaea88.all (fun s => unionSep true (v_eaeaea88.erase s) != top) = true := by decide +kernel

set_option maxRecDepth 10000 in
lemma pos_eaeaea88 : ∀ r : Fin 256, Nat.testBit 0xeaeaea88 (sampleMask (wireX v_eaeaea88 true r)) = true := by decide +kernel

set_option maxRecDepth 10000 in
lemma neg_eaeaea88 : ∀ r : Fin 256, Nat.testBit 0xeaeaea88 (sampleMask (wireX v_eaeaea88 false r)) = false := by decide +kernel

def v_eaeaeac0 : List Sig :=
  [(115790322444171310373542681253754569961897231106379883002368646712747861442560, 74209841425325483074281767790229379098442630633822194428193281782469427242),
   (115792089183397947543611745237842025222447431448805176201602006129307482587135, 16531125627984409991499529034413954067738791719286677406432770103732951458956),
   (115792089237314549919015196298186618729389642736847427496765807342296603033599, 91000701498298532256541283011909135993025971560327249515124728372441021696304),
   (115792089237316195423569452513147041964411626359178232937577306116684374867968, 109348201340217099309954184838902990101555216238937003489942800706468701041088),
   (115792089237316195423570985008687907853269984625075744832154243160018627067904, 114889202833308068712833890167240117074238932659595727340581232412893084941824)]

set_option maxRecDepth 10000 in
lemma nodup_eaeaeac0 : v_eaeaeac0.Nodup := by decide +kernel

set_option maxRecDepth 10000 in
lemma len_eaeaeac0 : v_eaeaeac0.length = 5 := by decide +kernel

set_option maxRecDepth 10000 in
lemma ess_eaeaeac0 : v_eaeaeac0.all (fun s => unionSep true (v_eaeaeac0.erase s) != top) = true := by decide +kernel

set_option maxRecDepth 10000 in
lemma pos_eaeaeac0 : ∀ r : Fin 256, Nat.testBit 0xeaeaeac0 (sampleMask (wireX v_eaeaeac0 true r)) = true := by decide +kernel

set_option maxRecDepth 10000 in
lemma neg_eaeaeac0 : ∀ r : Fin 256, Nat.testBit 0xeaeaeac0 (sampleMask (wireX v_eaeaeac0 false r)) = false := by decide +kernel

def v_eee0eae0 : List Sig :=
  [(115790322444171310323327399912967187682828898455819280016023827335838236180479, 4540935534835392654783431981449750101976132398307691420963255575736819714570),
   (115792089183397947593825494176623219110589001966476445958278958167592892596224, 5562204304926776683758071547705763938140414315125530191903629786933660879948),
   (115792089237314549919013663849413805278676320697653495912734075229266832785407, 94336610560465544448070901525908018558213106956438113874182559705900599758992),
   (115792089237316195423570984961919855458682420511118434308409431150799196520448, 101715189079326478193742345866193682537143974230886720634471491723128988524768),
   (115792089237316195423570985008687907853268655437644779123584680200852849295360, 115341529485805290704905702847104372337315154408220929287572124797090993831680)]

set_option maxRecDepth 10000 in
lemma nodup_eee0eae0 : v_eee0eae0.Nodup := by decide +kernel

set_option maxRecDepth 10000 in
lemma len_eee0eae0 : v_eee0eae0.length = 5 := by decide +kernel

set_option maxRecDepth 10000 in
lemma ess_eee0eae0 : v_eee0eae0.all (fun s => unionSep true (v_eee0eae0.erase s) != top) = true := by decide +kernel

set_option maxRecDepth 10000 in
lemma pos_eee0eae0 : ∀ r : Fin 256, Nat.testBit 0xeee0eae0 (sampleMask (wireX v_eee0eae0 true r)) = true := by decide +kernel

set_option maxRecDepth 10000 in
lemma neg_eee0eae0 : ∀ r : Fin 256, Nat.testBit 0xeee0eae0 (sampleMask (wireX v_eee0eae0 false r)) = false := by decide +kernel

def v_eee8e8a8 : List Sig :=
  [(115790322444171310323327399912967187682828898496381623381027529286141175922687, 1925922075085828013118264925984524362316725414068242664922158979592658945090),
   (115792089183397947593825494176623219110589001966477683822762685629777236230143, 3880114565952732400741018144460564678575714687425560451531248733197687195796),
   (115792089237314549919013663849413805278674991510222530241942291211553609842688, 94576909094604693631359052012085904166722349760395252408521471285005738856728),
   (115792089237316195423570984961919855458681091323687468599839868191633418747904, 102167515731823700185814158546057937800220195979511922581462384107326897414624),
   (115792089237316195423570985008687907853269984625075744832154243160018627067904, 114889202833308068712833890167240117074238932659595727340581232412893084941824)]

set_option maxRecDepth 10000 in
lemma nodup_eee8e8a8 : v_eee8e8a8.Nodup := by decide +kernel

set_option maxRecDepth 10000 in
lemma len_eee8e8a8 : v_eee8e8a8.length = 5 := by decide +kernel

set_option maxRecDepth 10000 in
lemma ess_eee8e8a8 : v_eee8e8a8.all (fun s => unionSep true (v_eee8e8a8.erase s) != top) = true := by decide +kernel

set_option maxRecDepth 10000 in
lemma pos_eee8e8a8 : ∀ r : Fin 256, Nat.testBit 0xeee8e8a8 (sampleMask (wireX v_eee8e8a8 true r)) = true := by decide +kernel

set_option maxRecDepth 10000 in
lemma neg_eee8e8a8 : ∀ r : Fin 256, Nat.testBit 0xeee8e8a8 (sampleMask (wireX v_eee8e8a8 false r)) = false := by decide +kernel

def v_eee8e8e0 : List Sig :=
  [(115790322444171310323327399912967187682828898496381623381027529286140102213631, 1940057282976366200370509072230282339287857343712780225765624366598843597898),
   (115792089183397947593825494176623219110589001966477683822762685629778309906432, 3865979358062194213488773998214806701604582757781022890687783346191502542988),
   (115792089237314549919013663849413805278674991510222530241942291211553609875455, 94562773886714155444106807865840146189751217830750714847678005897999554203920),
   (115792089237316195423570984961919855458681091323687468599839868191633418747904, 102167515731823700185814158546057937800220195979511922581462384107326897414624),
   (115792089237316195423570985008687907853269984625075744832154243160018627067904, 114889202833308068712833890167240117074238932659595727340581232412893084941824)]

set_option maxRecDepth 10000 in
lemma nodup_eee8e8e0 : v_eee8e8e0.Nodup := by decide +kernel

set_option maxRecDepth 10000 in
lemma len_eee8e8e0 : v_eee8e8e0.length = 5 := by decide +kernel

set_option maxRecDepth 10000 in
lemma ess_eee8e8e0 : v_eee8e8e0.all (fun s => unionSep true (v_eee8e8e0.erase s) != top) = true := by decide +kernel

set_option maxRecDepth 10000 in
lemma pos_eee8e8e0 : ∀ r : Fin 256, Nat.testBit 0xeee8e8e0 (sampleMask (wireX v_eee8e8e0 true r)) = true := by decide +kernel

set_option maxRecDepth 10000 in
lemma neg_eee8e8e0 : ∀ r : Fin 256, Nat.testBit 0xeee8e8e0 (sampleMask (wireX v_eee8e8e0 false r)) = false := by decide +kernel

def v_eee8eaa0 : List Sig :=
  [(115790322444171310323327399912967187682828898496381623381027529286141175922687, 1826975619852060702352555902264218523518801906556479739017901270549366375434),
   (115792089183397947593825494176623219110589001966477683822762685594595011559424, 3922520189624346962497750583197838609489110476359173134061644894216241154220),
   (115792089237314549919013663849413805278674991510222530241942291176370311528447, 94619314718276308193115784450823178097635745549328865091051867446024292815152),
   (115792089237316195423570984961919855458681091323687468599839868226816717094912, 102110974900261547436805181961074905892335668260933772338088522559302158803392),
   (115792089237316195423570985008687907853269984625075744832154243160018627067904, 114889202833308068712833890167240117074238932659595727340581232412893084941824)]

set_option maxRecDepth 10000 in
lemma nodup_eee8eaa0 : v_eee8eaa0.Nodup := by decide +kernel

set_option maxRecDepth 10000 in
lemma len_eee8eaa0 : v_eee8eaa0.length = 5 := by decide +kernel

set_option maxRecDepth 10000 in
lemma ess_eee8eaa0 : v_eee8eaa0.all (fun s => unionSep true (v_eee8eaa0.erase s) != top) = true := by decide +kernel

set_option maxRecDepth 10000 in
lemma pos_eee8eaa0 : ∀ r : Fin 256, Nat.testBit 0xeee8eaa0 (sampleMask (wireX v_eee8eaa0 true r)) = true := by decide +kernel

set_option maxRecDepth 10000 in
lemma neg_eee8eaa0 : ∀ r : Fin 256, Nat.testBit 0xeee8eaa0 (sampleMask (wireX v_eee8eaa0 false r)) = false := by decide +kernel

def v_eee8eac0 : List Sig :=
  [(115790322444171310323327399912967187682828898496381623381027529286141175889920, 1883516451414213451361532487247250431403329625134629982391762818574104986666),
   (115792089183397947593825494176623219110589001966477683822762685594595011592191, 3865979358062194213488773998214806701604582757781022890687783346191502542988),
   (115792089237314549919013663849413805278674991510222530241942291176370311528447, 94619314718276308193115784450823178097635745549328865091051867446024292815152),
   (115792089237316195423570984961919855458681091323687468599839868226816717094912, 102110974900261547436805181961074905892335668260933772338088522559302158803392),
   (115792089237316195423570985008687907853269984625075744832154243160018627067904, 114889202833308068712833890167240117074238932659595727340581232412893084941824)]

set_option maxRecDepth 10000 in
lemma nodup_eee8eac0 : v_eee8eac0.Nodup := by decide +kernel

set_option maxRecDepth 10000 in
lemma len_eee8eac0 : v_eee8eac0.length = 5 := by decide +kernel

set_option maxRecDepth 10000 in
lemma ess_eee8eac0 : v_eee8eac0.all (fun s => unionSep true (v_eee8eac0.erase s) != top) = true := by decide +kernel

set_option maxRecDepth 10000 in
lemma pos_eee8eac0 : ∀ r : Fin 256, Nat.testBit 0xeee8eac0 (sampleMask (wireX v_eee8eac0 true r)) = true := by decide +kernel

set_option maxRecDepth 10000 in
lemma neg_eee8eac0 : ∀ r : Fin 256, Nat.testBit 0xeee8eac0 (sampleMask (wireX v_eee8eac0 false r)) = false := by decide +kernel

def v_fee8e888 : List Sig := [(115790322444169664919200641528799672712472897861780751751054430343977037201407, 3876580763980097853927957107899125184332931705014426061320382386446141032594), (115792089183396302139486519255680698643019522093959784453672959622078714085375, 7753161527960195707855914215798250368665863410028852122640764772892282065188), (115792089237316195373354171125595888990276375199296709729344134444534334455808, 15478052640139315041207340139104984783389462960768629123594598771772194824760), (115792089237316195423570985008686480605577278705760743693527419893050572275712, 30645130706686789962865309060803294073414023469357431908632959029408327287744), (115792089237316195423570985008687907853269984665639326099418298627638230515712, 56088504909655527016904772303167652621451496829525041426870655640540702342144)]

set_option maxRecDepth 10000 in
lemma nodup_fee8e888 : v_fee8e888.Nodup := by decide +kernel

set_option maxRecDepth 10000 in
lemma len_fee8e888 : v_fee8e888.length = 5 := by decide +kernel

set_option maxRecDepth 10000 in
lemma ess_fee8e888 : v_fee8e888.all (fun s => unionSep true (v_fee8e888.erase s) != top) = true := by decide +kernel

set_option maxRecDepth 10000 in
lemma pos_fee8e888 : ∀ r : Fin 256, Nat.testBit 0xfee8e888 (sampleMask (wireX v_fee8e888 true r)) = true := by decide +kernel

set_option maxRecDepth 10000 in
lemma neg_fee8e888 : ∀ r : Fin 256, Nat.testBit 0xfee8e888 (sampleMask (wireX v_fee8e888 false r)) = false := by decide +kernel

def v_eaeaeaa8 : List Sig :=
  [(115791647552509947494639228604858154017032806765940211650157421461422429175807, 883477455573736460229895203936152626604330591662398248485149118048534530),
   (115792089210357894160550168636016784500121928109927959279679823682170263715839, 2072638110775985735699334148434214062013759568039986290946159830941862007380),
   (115792089237314549919019793784809215045724290987377094727991070258192885727232, 112693292061891314789314627580881852515455295115384702182895923476357894775960),
   (115792089237316195423564855026524444297836556469828821337550737577522677940224, 114986799536560734640071435530300104734120137331340288035963370586811890415840),
   (115792089237316195423570985008687907853269979473343705504629955477416800419840, 115679445861730544024891673370186048393377932515203608262775727495361941487360)]

set_option maxRecDepth 10000 in
lemma nodup_eaeaeaa8 : v_eaeaeaa8.Nodup := by decide +kernel

set_option maxRecDepth 10000 in
lemma len_eaeaeaa8 : v_eaeaeaa8.length = 5 := by decide +kernel

set_option maxRecDepth 10000 in
lemma ess_eaeaeaa8 : v_eaeaeaa8.all (fun s => unionSep true (v_eaeaeaa8.erase s) != top) = true := by decide +kernel

set_option maxRecDepth 10000 in
lemma pos_eaeaeaa8 : ∀ r : Fin 256, Nat.testBit 0xeaeaeaa8 (sampleMask (wireX v_eaeaeaa8 true r)) = true := by decide +kernel

set_option maxRecDepth 10000 in
lemma neg_eaeaeaa8 : ∀ r : Fin 256, Nat.testBit 0xeaeaeaa8 (sampleMask (wireX v_eaeaeaa8 false r)) = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eae8eac8_4_0 : search 4 0 v_eae8eac8 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eae8eac8_5_1 : search 5 1 v_eae8eac8 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eaeaea88_4_0 : search 4 0 v_eaeaea88 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eaeaea88_5_1 : search 5 1 v_eaeaea88 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eee8e8a8_4_0 : search 4 0 v_eee8e8a8 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eee8e8a8_5_0 : search 5 0 v_eee8e8a8 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eee8e8a8_5_1 : search 5 1 v_eee8e8a8 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eee8e8a8_6_0 : search 6 0 v_eee8e8a8 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eee8e8a8_6_1 : search 6 1 v_eee8e8a8 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eee8e8a8_7_1 : search 7 1 v_eee8e8a8 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eee8e8e0_4_0 : search 4 0 v_eee8e8e0 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eee8e8e0_5_0 : search 5 0 v_eee8e8e0 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eee8e8e0_5_1 : search 5 1 v_eee8e8e0 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eee8e8e0_6_0 : search 6 0 v_eee8e8e0 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eee8e8e0_6_1 : search 6 1 v_eee8e8e0 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eee8e8e0_7_1 : search 7 1 v_eee8e8e0 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eee8eaa0_4_0 : search 4 0 v_eee8eaa0 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eee8eaa0_5_0 : search 5 0 v_eee8eaa0 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eee8eaa0_5_1 : search 5 1 v_eee8eaa0 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eee8eaa0_6_0 : search 6 0 v_eee8eaa0 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eee8eaa0_6_1 : search 6 1 v_eee8eaa0 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eee8eaa0_7_1 : search 7 1 v_eee8eaa0 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eee8eac0_4_0 : search 4 0 v_eee8eac0 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eee8eac0_5_0 : search 5 0 v_eee8eac0 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eee8eac0_5_1 : search 5 1 v_eee8eac0 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eee8eac0_6_0 : search 6 0 v_eee8eac0 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eee8eac0_6_1 : search 6 1 v_eee8eac0 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eee8eac0_7_1 : search 7 1 v_eee8eac0 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eaeaeaa8_4_0 : search 4 0 v_eaeaeaa8 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eaeaeaa8_5_0 : search 5 0 v_eaeaeaa8 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eaeaeaa8_5_1 : search 5 1 v_eaeaeaa8 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eaeaeaa8_6_1 : search 6 1 v_eaeaeaa8 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_fee8e888_4_0 : search 4 0 v_fee8e888 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_fee8e888_5_0 : search 5 0 v_fee8e888 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_fee8e888_5_1 : search 5 1 v_fee8e888 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_fee8e888_6_0 : search 6 0 v_fee8e888 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_fee8e888_6_1 : search 6 1 v_fee8e888 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_fee8e888_7_0 : search 7 0 v_fee8e888 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_fee8e888_7_1 : search 7 1 v_fee8e888 = false := by decide +kernel

def forward (k t : ℕ) (v : List Sig) (r : ℕ → List Sig → Bool) : Bool :=
  v.contains target ||
    (decide (0 < t) &&
      v.any (fun a => tryGate k (t-1) (r (t-1)) v (dropped [a] v) (neg a) [[], [a]])) ||
    (decide (t ≤ k) &&
      v.any (fun a => v.any (fun b => before a b &&
        (let rest := dropped [a,b] v
         let keep := [[], [a], [b], [a,b]]
         tryGate k t (r t) v rest (bin false a b) keep ||
         tryGate k t (r t) v rest (bin true a b) keep))))

def orderWires (v : List Sig) : List Sig :=
  v.insertionSort (fun a b => before a b = true)

lemma orderWires_perm (v : List Sig) : (orderWires v).Perm v :=
  List.perm_insertionSort _ _

def oneRound (k t : Nat) (v : List Sig) (r : Nat → List Sig → Bool) : Bool :=
  v.contains target ||
    (decide (0 < t) && v.any (fun a =>
      tryGate k (t - 1) (r (t - 1)) v (dropped [a] v) (neg a) [[], [a]])) ||
    (decide (t ≤ k) && v.any (fun a => v.any (fun b =>
      before a b &&
        (let rest := dropped [a, b] v
         let keep := [[], [a], [b], [a, b]]
         tryGate k t (r t) v rest (bin false a b) keep ||
         tryGate k t (r t) v rest (bin true a b) keep))))

lemma negRound (k t : Nat) (v : List Sig) (r : Nat → List Sig → Bool)
    (hr : ∀ t' w, search k t' w = true → r t' w = true)
    (h : oneRound k t v r = false) : search (k+1) t v = false := by
  have gate (t' : Nat) (rest : List Sig) (g : Sig) (keep : List (List Sig))
      (hp : tryGate k t' (search k t') v rest g keep = true) :
      tryGate k t' (r t') v rest g keep = true := by
    simp only [tryGate, Bool.and_eq_true, List.any_eq_true] at hp ⊢
    obtain ⟨ha, s, hs, hb, hc⟩ := hp
    exact ⟨ha, s, hs, hb, hr t' _ hc⟩
  apply Bool.eq_false_iff.mpr
  intro hx
  have hy : oneRound k t v r = true := by
    change oneRound k t v (search k) = true at hx
    simp only [oneRound, Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true] at hx ⊢
    rcases hx with (hx | ⟨ht, a, ha, hnot⟩) | ⟨ht, a, ha, b, hb, hab, hop⟩
    · exact Or.inl (Or.inl hx)
    · exact Or.inl (Or.inr ⟨ht, a, ha, gate _ _ _ _ hnot⟩)
    · exact Or.inr ⟨ht, a, ha, b, hb, hab, hop.imp (gate _ _ _ _) (gate _ _ _ _)⟩
  simp [h] at hy

def pathStep (wire : List Sig) (op : Nat) : List Sig :=
  if op = 1023 then wire else
  let a := wire.getD (op % 8) zero
  let b := wire.getD (op / 8 % 8) zero
  let kind := op / 64 % 3
  let keep := op / 192
  let ls := if keep % 2 = 1 then [a] else []
  let rs := if keep ≥ 2 then [b] else []
  if kind = 2 then neg a :: (ls ++ dropped [a] wire)
  else bin (kind = 1) a b :: (ls ++ rs ++ dropped [a,b] wire)

def stateHash (v : List Sig) : Nat :=
  v.foldl (fun acc s =>
    let n := (s.1.toNat ^^^ s.2.toNat ^^^ (s.1.toNat >>> 71) ^^^ (s.2.toNat >>> 113)) % 4294967291
    acc + n*n*n) 0 % 18446744073709551557

def takeField (word width i : Nat) : Nat := (word >>> (width*i)) &&& (2^width-1)

def rowBits (p : Fin 256 → Fin 256) (s : B) : B := mkBV fun i => s[(p i).val]

def rowSig (p : Fin 256 → Fin 256) (s : Sig) : Sig := (rowBits p s.1, rowBits p s.2)

lemma rowBits_bit (p : Fin 256 → Fin 256) (s : B) (i : ℕ) (hi : i < 256) :
    (rowBits p s)[i] = s[(p ⟨i, hi⟩).val] := getElem_mkBV _ i hi

lemma rowBits_invol (p : Fin 256 → Fin 256) (hp : ∀ i, p (p i) = i) (s : B) :
    rowBits p (rowBits p s) = s := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [rowBits_bit, hp]

lemma rowSig_inj (p : Fin 256 → Fin 256) (hp : ∀ i, p (p i) = i) :
    Function.Injective (rowSig p) := by
  intro a b hab
  have h := congrArg (rowSig p) hab
  simpa only [rowSig, rowBits_invol p hp] using h

lemma rowBits_or (p : Fin 256 → Fin 256) (a b : B) :
    rowBits p (a ||| b) = rowBits p a ||| rowBits p b := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [rowBits_bit, BitVec.getElem_or]

lemma rowBits_and (p : Fin 256 → Fin 256) (a b : B) :
    rowBits p (a &&& b) = rowBits p a &&& rowBits p b := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [rowBits_bit, BitVec.getElem_and]

lemma rowBits_top (p : Fin 256 → Fin 256) : rowBits p top = top := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [rowBits_bit, top, BitVec.getElem_allOnes]

lemma rowBits_zero (p : Fin 256 → Fin 256) : rowBits p 0 = 0 := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp [rowBits_bit]

lemma rowSig_target (p : Fin 256 → Fin 256) : rowSig p target = target := by
  exact Prod.ext (rowBits_top p) (rowBits_zero p)

lemma rowSig_zero (p : Fin 256 → Fin 256) : rowSig p zero = zero := by
  exact Prod.ext (rowBits_zero p) (rowBits_zero p)

lemma rowSig_one (p : Fin 256 → Fin 256) : rowSig p one = one := by
  simp [rowSig, one, rowBits_top]

lemma rowSig_neg (p : Fin 256 → Fin 256) (s : Sig) : rowSig p (neg s) = neg (rowSig p s) := by
  apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro i hi <;>
    simp only [rowSig, neg, rowBits_bit, BitVec.getElem_not]

lemma rowSig_bin (p : Fin 256 → Fin 256) (b : Bool) (a c : Sig) :
    rowSig p (bin b a c) = bin b (rowSig p a) (rowSig p c) := by
  cases b <;> simp [rowSig, bin, rowBits_or, rowBits_and]

lemma rowSep (p : Fin 256 → Fin 256) (d : Bool) (a : Sig) :
    sep d (rowSig p a) = rowBits p (sep d a) := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  cases d <;> simp [sep, rowSig, rowBits_bit]

lemma rowUnion (p : Fin 256 → Fin 256) (d : Bool) (l : List Sig) :
    unionSep d (l.map (rowSig p)) = rowBits p (unionSep d l) := by
  induction l with
  | nil => exact (rowBits_zero p).symm
  | cons a l ih => simp [unionSep, ih, rowSep, rowBits_or]

lemma rowDropped (p : Fin 256 → Fin 256) (hp : ∀ i, p (p i) = i) (u v : List Sig) :
    dropped (u.map (rowSig p)) (v.map (rowSig p)) = (dropped u v).map (rowSig p) := by
  have hinj := rowSig_inj p hp
  unfold dropped
  rw [List.filter_map]
  congr 2
  funext a
  change (!(u.map (rowSig p)).contains (rowSig p a)) = (!u.contains a)
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [List.contains_iff_mem, List.mem_map, hinj.eq_iff, exists_eq_right]

lemma tryData {k t : ℕ} {r : List Sig → Bool} {v rest : List Sig} {g : Sig}
    {keep : List (List Sig)} (hg : tryGate k t r v rest g keep = true) :
    g ≠ zero ∧ g ≠ one ∧ g ∉ v ∧ ∃ h ∈ keep,
    rest.length + h.length + 1 ≤ k-t+1 ∧
    (sep (decide (0 < t)) g ||| unionSep (decide (0 < t)) rest) |||
        unionSep (decide (0 < t)) h = top ∧ r (g :: (h ++ rest)) = true := by
  simpa [tryGate, List.any_eq_true, Bool.and_eq_true, and_assoc] using hg

lemma rowTry (p : Fin 256 → Fin 256) (hp : ∀ i, p (p i) = i) {k t : ℕ}
    (ih : ∀ V, search k t V = true → search k t (V.map (rowSig p)) = true)
    {v rest : List Sig} {g : Sig} {keep keep' : List (List Sig)}
    (hkeep : ∀ h ∈ keep, ∃ h' ∈ keep', h'.Perm (h.map (rowSig p)))
    (hs : tryGate k t (search k t) v rest g keep = true) :
    tryGate k t (search k t) (v.map (rowSig p)) (rest.map (rowSig p)) (rowSig p g) keep' = true := by
  obtain ⟨hz,ho,hn,h,hh,hl,hsep,hr⟩ := tryData hs
  obtain ⟨h',hh',perm⟩ := hkeep h hh
  have inj := rowSig_inj p hp
  apply tryGate_eq_true _ _ _ h' hh'
  · simpa only [List.length_map, perm.length_eq] using hl
  · rw [unionSep_perm perm, rowUnion, rowUnion, rowSep, ← rowBits_or, ← rowBits_or,
      hsep, rowBits_top]
  · have mapped := ih _ hr
    have hperm := List.Perm.cons (rowSig p g) (perm.append_right (rest.map (rowSig p)))
    rw [search_perm k t hperm]
    simpa using mapped
  · exact fun h0 => hz (inj (h0.trans (rowSig_zero p).symm))
  · exact fun h1 => ho (inj (h1.trans (rowSig_one p).symm))
  · simpa [List.mem_map, inj.eq_iff] using hn

def edgeRun (k t : ℕ) (v : List Sig) (d : Bool) (a b : Sig) : Bool :=
  tryGate k t (search k t) v (dropped [a,b] v) (bin d a b) [[],[a],[b],[a,b]]

lemma dropped_swap (a b : Sig) (v : List Sig) : dropped [a,b] v = dropped [b,a] v := by
  unfold dropped
  apply List.filter_congr
  intro s _
  simp only [List.contains_cons, List.contains_nil, Bool.false_or, Bool.or_false]
  rw [Bool.or_comm]

lemma rowEdge (p : Fin 256 → Fin 256) (hp : ∀ i, p (p i) = i) {k t : ℕ}
    (ih : ∀ V, search k t V = true → search k t (V.map (rowSig p)) = true)
    {v : List Sig} {a b : Sig} {d : Bool} (h : edgeRun k t v d a b = true) :
    edgeRun k t (v.map (rowSig p)) d (rowSig p a) (rowSig p b) = true ∧
    edgeRun k t (v.map (rowSig p)) d (rowSig p b) (rowSig p a) = true := by
  let f := rowSig p
  have move (K : List (List Sig)) (hk : ∀ u ∈ [[],[a],[b],[a,b]],
      ∃ z ∈ K, z.Perm (u.map f)) :
      tryGate k t (search k t) (v.map f) (dropped [f a,f b] (v.map f)) (bin d (f a) (f b)) K = true := by
    have zz := rowTry p hp ih hk h
    rw [← rowDropped p hp [a,b] v, rowSig_bin] at zz
    exact zz
  constructor
  · apply move
    intro u hu
    refine ⟨u.map f, ?_, .refl _⟩
    simpa only [List.map_cons, List.map_nil] using
      (List.mem_map_of_mem (f := List.map f) hu)
  · unfold edgeRun
    rw [dropped_swap (rowSig p b) (rowSig p a), bin_comm d (rowSig p b) (rowSig p a)]
    apply move
    intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl|rfl|rfl|rfl
    · exact ⟨[], by simp, .refl _⟩
    · exact ⟨[f a], by simp [f], .refl _⟩
    · exact ⟨[f b], by simp [f], .refl _⟩
    · exact ⟨[f b,f a], by simp [f], .swap _ _ _⟩

lemma rowSearch (p : Fin 256 → Fin 256) (hp : ∀ i, p (p i) = i) :
    ∀ k t v, search k t v = true → search k t (v.map (rowSig p)) = true := by
  intro k
  induction k with
  | zero =>
    intro t v hs
    simp only [search, List.contains_iff_mem] at hs ⊢
    exact rowSig_target p ▸ (List.mem_map_of_mem (f := rowSig p) hs)
  | succ k ih =>
    intro t v hs
    simp only [search, Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true,
      List.contains_iff_mem, decide_eq_true_eq] at hs ⊢
    rcases hs with (ha | ⟨ht,a,ha,hnot⟩) | ⟨ht,a,ha,b,hb,hab,habop⟩
    · exact Or.inl (Or.inl (rowSig_target p ▸ (List.mem_map_of_mem (f := rowSig p) ha)))
    · refine Or.inl (Or.inr ⟨ht,rowSig p a,List.mem_map_of_mem ha,?_⟩)
      have hk : ∀ u ∈ [[],[a]], ∃ z ∈ [[], [rowSig p a]], z.Perm (u.map (rowSig p)) := by
        intro u hu
        refine ⟨_, ?_, .refl _⟩
        simpa only [List.map_cons, List.map_nil] using
          (List.mem_map_of_mem (f := List.map (rowSig p)) hu)
      have zz := rowTry p hp (ih (t-1)) hk hnot
      rw [← rowDropped p hp [a] v, rowSig_neg] at zz
      exact zz
    · right
      refine ⟨ht, ?_⟩
      have hne : rowSig p a ≠ rowSig p b := by
        intro he
        obtain rfl := rowSig_inj p hp he
        simp [before] at hab
      have hsort := before_trichotomy hne
      rcases hsort with hlt|hlt
      · refine ⟨rowSig p a, List.mem_map_of_mem ha, rowSig p b, List.mem_map_of_mem hb, hlt, ?_⟩
        rcases habop with hh|hh
        · exact Or.inl (rowEdge p hp (ih t) (d := false) hh).1
        · exact Or.inr (rowEdge p hp (ih t) (d := true) hh).1
      · refine ⟨rowSig p b, List.mem_map_of_mem hb, rowSig p a, List.mem_map_of_mem ha, hlt, ?_⟩
        rcases habop with hh|hh
        · exact Or.inl (rowEdge p hp (ih t) (d := false) hh).2
        · exact Or.inr (rowEdge p hp (ih t) (d := true) hh).2

def packedSwap (code : ℕ) (i : Fin 256) : Fin 256 :=
  ⟨(code >>> (8 * i.val)) % 256, Nat.mod_lt _ (by decide)⟩

def hardFixedInputs : List Sig := v_fee8e888

def hardSwap01 : Fin 256 → Fin 256 := packedSwap 0xfffefdfbfcfaf9f7f8f6f4f5f3f1f2f0e0dfdddedcdbd9dad8d6d7d5d3d4d2efeeecedebeae8e9e7e5e6e4e2e3e1d1d0cecfcdcccacbc9c7c8c6c4c5c3c2c1bfc0bebdbbbcbab8b9b7b5b6b4a4a3a1a2a09f9d9e9c9a9b99979896b3b2b0b1afaeacadaba9aaa8a6a7a59594929391908e8f8d8b8c8a88898777767475737270716f6d6e6c6a6b698685838482817f807e7c7d7b797a786867656664636162605e5f5d5b5c5a5958565755545253514f504e4c4d4b3b3a383937363435333132302e2f2d4a494748464543444240413f3d3e3c2c2b292a28272526242223211f201e1d1c1a1b191816171513141210110f0e0d0b0c0a09070806040503010200

set_option maxRecDepth 3000 in
lemma hardSwap01_inv : ∀ i, hardSwap01 (hardSwap01 i) = i := by decide +kernel

set_option maxRecDepth 3000 in
lemma hardSwap01_inputs : hardFixedInputs.map (rowSig hardSwap01) = [(115792089183396302139486519255680698643019522093959784453672959622078714085375, 7753161527960195707855914215798250368665863410028852122640764772892282065188), (115790322444169664919200641528799672712472897861780751751054430343977037201407, 3876580763980097853927957107899125184332931705014426061320382386446141032594), (115792089237316195373354171125595888990276375199296709729344134444534334455808, 15478052640139315041207340139104984783389462960768629123594598771772194824760), (115792089237316195423570985008686480605577278705760743693527419893050572275712, 30645130706686789962865309060803294073414023469357431908632959029408327287744), (115792089237316195423570985008687907853269984665639326099418298627638230515712, 56088504909655527016904772303167652621451496829525041426870655640540702342144)] := by decide +kernel

def hardSwap23 : Fin 256 → Fin 256 := packedSwap 0xfffdfefcfbfaf9f5f4f3f8f7f6f2f1f0eeefedecebeae6e5e4e9e8e7e3e2e1dfe0dedddcdbd7d6d5dad9d8d4d3d2d0d1cfcecdccc8c7c6cbcac9c5c4c39495939291908c8b8a8f8e8d8988878586848382817d7c7b807f7e7a79787677757473726e6d6c71706f6b6a69c1c2c0bfbebdb9b8b7bcbbbab6b5b4b2b3b1b0afaeaaa9a8adacaba7a6a5a3a4a2a1a09f9b9a999e9d9c9897966768666564635f5e5d6261605c5b5a585957565554504f4e5352514d4c4b494a4847464541403f4443423e3d3c3a3b393837363231303534332f2e2d1c1d1b1a191814131217161511100f2b2c2a292827232221262524201f1e0d0e0c0b0a09050403080706020100

set_option maxRecDepth 3000 in
lemma hardSwap23_inv : ∀ i, hardSwap23 (hardSwap23 i) = i := by decide +kernel

set_option maxRecDepth 3000 in
lemma hardSwap23_inputs : hardFixedInputs.map (rowSig hardSwap23) = [(115790322444169664919200641528799672712472897861780751751054430343977037201407, 3876580763980097853927957107899125184332931705014426061320382386446141032594), (115792089183396302139486519255680698643019522093959784453672959622078714085375, 7753161527960195707855914215798250368665863410028852122640764772892282065188), (115792089237316195423570985008686480605577278705760743693527419893050572275712, 30645130706686789962865309060803294073414023469357431908632959029408327287744), (115792089237316195373354171125595888990276375199296709729344134444534334455808, 15478052640139315041207340139104984783389462960768629123594598771772194824760), (115792089237316195423570985008687907853269984665639326099418298627638230515712, 56088504909655527016904772303167652621451496829525041426870655640540702342144)] := by decide +kernel

def hardSwap34 : Fin 256 → Fin 256 := packedSwap 0xfffef9f8f7f6fdfcfbfaf5f4f3f2f1f0efeae9e8e7eeedecebe6e5e4e3e2e1e0dbdad9d8dfdedddcd7d6d5d4d3d2d1cccbcac9d0cfcecdc8c7c6c5c4c3c2bdbcbbbac1c0bfbeb9b8b7b6b5b4b3aeadacabb2b1b0afaaa9a8a7a6a5a49f9e9d9ca3a2a1a09b9a99989796595453525158575655504f4e4d4c4b4a454443424948474641403f3e3d3c3b363534333a3938373231302f2e2d2c272625242b2a2928232221201f1e95908f8e8d949392918c8b8a8988878681807f7e858483827d7c7b7a7978777271706f767574736e6d6c6b6a696863626160676665645f5e5d5c5b5a1d181716151c1b1a1914131211100f0e090807060d0c0b0a050403020100

set_option maxRecDepth 3000 in
lemma hardSwap34_inv : ∀ i, hardSwap34 (hardSwap34 i) = i := by decide +kernel

set_option maxRecDepth 3000 in
lemma hardSwap34_inputs : hardFixedInputs.map (rowSig hardSwap34) = [(115790322444169664919200641528799672712472897861780751751054430343977037201407, 3876580763980097853927957107899125184332931705014426061320382386446141032594), (115792089183396302139486519255680698643019522093959784453672959622078714085375, 7753161527960195707855914215798250368665863410028852122640764772892282065188), (115792089237316195373354171125595888990276375199296709729344134444534334455808, 15478052640139315041207340139104984783389462960768629123594598771772194824760), (115792089237316195423570985008687907853269984665639326099418298627638230515712, 56088504909655527016904772303167652621451496829525041426870655640540702342144), (115792089237316195423570985008686480605577278705760743693527419893050572275712, 30645130706686789962865309060803294073414023469357431908632959029408327287744)] := by decide +kernel

def hardSwap24 : Fin 256 → Fin 256 := packedSwap 0xfff9fdf5f4f3fef8f7f6fcfbfaf2f1f0eaeee6e5e4efe9e8e7edecebe3e2e1dbdfd7d6d5e0dad9d8dedddcd4d3d2ccd0c8c7c6d1cbcac9cfcecdc5c4c35458504f4e595352515756554d4c4b454941403f4a4443424847463e3d3c363a3231303b3534333938372f2e2d90948c8b8a958f8e8d93929189888781857d7c7b86807f7e8483827a797872766e6d6c7771706f7574736b6a69181c1413121d1716151b1a1911100fbdc1b9b8b7c2bcbbbac0bfbeb6b5b4aeb2aaa9a8b3adacabb1b0afa7a6a59fa39b9a99a49e9d9ca2a1a0989796272b2322212c2625242a2928201f1e63675f5e5d686261606665645c5b5a090d0504030e0807060c0b0a020100

set_option maxRecDepth 3000 in
lemma hardSwap24_inv : ∀ i, hardSwap24 (hardSwap24 i) = i := by decide +kernel

set_option maxRecDepth 3000 in
lemma hardSwap24_inputs : hardFixedInputs.map (rowSig hardSwap24) = [(115790322444169664919200641528799672712472897861780751751054430343977037201407, 3876580763980097853927957107899125184332931705014426061320382386446141032594), (115792089183396302139486519255680698643019522093959784453672959622078714085375, 7753161527960195707855914215798250368665863410028852122640764772892282065188), (115792089237316195423570985008687907853269984665639326099418298627638230515712, 56088504909655527016904772303167652621451496829525041426870655640540702342144), (115792089237316195423570985008686480605577278705760743693527419893050572275712, 30645130706686789962865309060803294073414023469357431908632959029408327287744), (115792089237316195373354171125595888990276375199296709729344134444534334455808, 15478052640139315041207340139104984783389462960768629123594598771772194824760)] := by decide +kernel

def orbitInput : ℕ → List Sig
| 0 => hardFixedInputs
| 1 => [(115790322444169664919200641528799672712472897861780751751054430343977037201407, 3876580763980097853927957107899125184332931705014426061320382386446141032594), (115792089183396302139486519255680698643019522093959784453672959622078714085375, 7753161527960195707855914215798250368665863410028852122640764772892282065188), (115792089237316195373354171125595888990276375199296709729344134444534334455808, 15478052640139315041207340139104984783389462960768629123594598771772194824760), (115792089237316195423570985008687907853269984665639326099418298627638230515712, 56088504909655527016904772303167652621451496829525041426870655640540702342144), (115792089237316195423570985008686480605577278705760743693527419893050572275712, 30645130706686789962865309060803294073414023469357431908632959029408327287744)]
| 2 => [(115790322444169664919200641528799672712472897861780751751054430343977037201407, 3876580763980097853927957107899125184332931705014426061320382386446141032594), (115792089183396302139486519255680698643019522093959784453672959622078714085375, 7753161527960195707855914215798250368665863410028852122640764772892282065188), (115792089237316195423570985008686480605577278705760743693527419893050572275712, 30645130706686789962865309060803294073414023469357431908632959029408327287744), (115792089237316195373354171125595888990276375199296709729344134444534334455808, 15478052640139315041207340139104984783389462960768629123594598771772194824760), (115792089237316195423570985008687907853269984665639326099418298627638230515712, 56088504909655527016904772303167652621451496829525041426870655640540702342144)]
| 3 => [(115790322444169664919200641528799672712472897861780751751054430343977037201407, 3876580763980097853927957107899125184332931705014426061320382386446141032594), (115792089183396302139486519255680698643019522093959784453672959622078714085375, 7753161527960195707855914215798250368665863410028852122640764772892282065188), (115792089237316195423570985008686480605577278705760743693527419893050572275712, 30645130706686789962865309060803294073414023469357431908632959029408327287744), (115792089237316195423570985008687907853269984665639326099418298627638230515712, 56088504909655527016904772303167652621451496829525041426870655640540702342144), (115792089237316195373354171125595888990276375199296709729344134444534334455808, 15478052640139315041207340139104984783389462960768629123594598771772194824760)]
| 4 => [(115790322444169664919200641528799672712472897861780751751054430343977037201407, 3876580763980097853927957107899125184332931705014426061320382386446141032594), (115792089183396302139486519255680698643019522093959784453672959622078714085375, 7753161527960195707855914215798250368665863410028852122640764772892282065188), (115792089237316195423570985008687907853269984665639326099418298627638230515712, 56088504909655527016904772303167652621451496829525041426870655640540702342144), (115792089237316195373354171125595888990276375199296709729344134444534334455808, 15478052640139315041207340139104984783389462960768629123594598771772194824760), (115792089237316195423570985008686480605577278705760743693527419893050572275712, 30645130706686789962865309060803294073414023469357431908632959029408327287744)]
| 5 => [(115790322444169664919200641528799672712472897861780751751054430343977037201407, 3876580763980097853927957107899125184332931705014426061320382386446141032594), (115792089183396302139486519255680698643019522093959784453672959622078714085375, 7753161527960195707855914215798250368665863410028852122640764772892282065188), (115792089237316195423570985008687907853269984665639326099418298627638230515712, 56088504909655527016904772303167652621451496829525041426870655640540702342144), (115792089237316195423570985008686480605577278705760743693527419893050572275712, 30645130706686789962865309060803294073414023469357431908632959029408327287744), (115792089237316195373354171125595888990276375199296709729344134444534334455808, 15478052640139315041207340139104984783389462960768629123594598771772194824760)]
| 6 => [(115792089183396302139486519255680698643019522093959784453672959622078714085375, 7753161527960195707855914215798250368665863410028852122640764772892282065188), (115790322444169664919200641528799672712472897861780751751054430343977037201407, 3876580763980097853927957107899125184332931705014426061320382386446141032594), (115792089237316195373354171125595888990276375199296709729344134444534334455808, 15478052640139315041207340139104984783389462960768629123594598771772194824760), (115792089237316195423570985008686480605577278705760743693527419893050572275712, 30645130706686789962865309060803294073414023469357431908632959029408327287744), (115792089237316195423570985008687907853269984665639326099418298627638230515712, 56088504909655527016904772303167652621451496829525041426870655640540702342144)]
| 7 => [(115792089183396302139486519255680698643019522093959784453672959622078714085375, 7753161527960195707855914215798250368665863410028852122640764772892282065188), (115790322444169664919200641528799672712472897861780751751054430343977037201407, 3876580763980097853927957107899125184332931705014426061320382386446141032594), (115792089237316195373354171125595888990276375199296709729344134444534334455808, 15478052640139315041207340139104984783389462960768629123594598771772194824760), (115792089237316195423570985008687907853269984665639326099418298627638230515712, 56088504909655527016904772303167652621451496829525041426870655640540702342144), (115792089237316195423570985008686480605577278705760743693527419893050572275712, 30645130706686789962865309060803294073414023469357431908632959029408327287744)]
| 8 => [(115792089183396302139486519255680698643019522093959784453672959622078714085375, 7753161527960195707855914215798250368665863410028852122640764772892282065188), (115790322444169664919200641528799672712472897861780751751054430343977037201407, 3876580763980097853927957107899125184332931705014426061320382386446141032594), (115792089237316195423570985008686480605577278705760743693527419893050572275712, 30645130706686789962865309060803294073414023469357431908632959029408327287744), (115792089237316195373354171125595888990276375199296709729344134444534334455808, 15478052640139315041207340139104984783389462960768629123594598771772194824760), (115792089237316195423570985008687907853269984665639326099418298627638230515712, 56088504909655527016904772303167652621451496829525041426870655640540702342144)]
| 9 => [(115792089183396302139486519255680698643019522093959784453672959622078714085375, 7753161527960195707855914215798250368665863410028852122640764772892282065188), (115790322444169664919200641528799672712472897861780751751054430343977037201407, 3876580763980097853927957107899125184332931705014426061320382386446141032594), (115792089237316195423570985008686480605577278705760743693527419893050572275712, 30645130706686789962865309060803294073414023469357431908632959029408327287744), (115792089237316195423570985008687907853269984665639326099418298627638230515712, 56088504909655527016904772303167652621451496829525041426870655640540702342144), (115792089237316195373354171125595888990276375199296709729344134444534334455808, 15478052640139315041207340139104984783389462960768629123594598771772194824760)]
| 10 => [(115792089183396302139486519255680698643019522093959784453672959622078714085375, 7753161527960195707855914215798250368665863410028852122640764772892282065188), (115790322444169664919200641528799672712472897861780751751054430343977037201407, 3876580763980097853927957107899125184332931705014426061320382386446141032594), (115792089237316195423570985008687907853269984665639326099418298627638230515712, 56088504909655527016904772303167652621451496829525041426870655640540702342144), (115792089237316195373354171125595888990276375199296709729344134444534334455808, 15478052640139315041207340139104984783389462960768629123594598771772194824760), (115792089237316195423570985008686480605577278705760743693527419893050572275712, 30645130706686789962865309060803294073414023469357431908632959029408327287744)]
| 11 => [(115792089183396302139486519255680698643019522093959784453672959622078714085375, 7753161527960195707855914215798250368665863410028852122640764772892282065188), (115790322444169664919200641528799672712472897861780751751054430343977037201407, 3876580763980097853927957107899125184332931705014426061320382386446141032594), (115792089237316195423570985008687907853269984665639326099418298627638230515712, 56088504909655527016904772303167652621451496829525041426870655640540702342144), (115792089237316195423570985008686480605577278705760743693527419893050572275712, 30645130706686789962865309060803294073414023469357431908632959029408327287744), (115792089237316195373354171125595888990276375199296709729344134444534334455808, 15478052640139315041207340139104984783389462960768629123594598771772194824760)]
| _ => hardFixedInputs

set_option maxRecDepth 3000 in
lemma oi6 : (orbitInput 0).map (rowSig hardSwap01) = orbitInput 6 := by decide +kernel

set_option maxRecDepth 3000 in
lemma oi2 : (orbitInput 0).map (rowSig hardSwap23) = orbitInput 2 := by decide +kernel

set_option maxRecDepth 3000 in
lemma oi5 : (orbitInput 0).map (rowSig hardSwap24) = orbitInput 5 := by decide +kernel

set_option maxRecDepth 3000 in
lemma oi1 : (orbitInput 0).map (rowSig hardSwap34) = orbitInput 1 := by decide +kernel

set_option maxRecDepth 3000 in
lemma oi8 : (orbitInput 6).map (rowSig hardSwap23) = orbitInput 8 := by decide +kernel

set_option maxRecDepth 3000 in
lemma oi11 : (orbitInput 6).map (rowSig hardSwap24) = orbitInput 11 := by decide +kernel

set_option maxRecDepth 3000 in
lemma oi7 : (orbitInput 6).map (rowSig hardSwap34) = orbitInput 7 := by decide +kernel

set_option maxRecDepth 3000 in
lemma oi3 : (orbitInput 2).map (rowSig hardSwap24) = orbitInput 3 := by decide +kernel

set_option maxRecDepth 3000 in
lemma oi4 : (orbitInput 2).map (rowSig hardSwap34) = orbitInput 4 := by decide +kernel

set_option maxRecDepth 3000 in
lemma oi9 : (orbitInput 8).map (rowSig hardSwap24) = orbitInput 9 := by decide +kernel

set_option maxRecDepth 3000 in
lemma oi10 : (orbitInput 8).map (rowSig hardSwap34) = orbitInput 10 := by decide +kernel

lemma orbitInput_invariant (F : List Sig → Bool)
    (h : ∀ (p : Fin 256 → Fin 256), (∀ i, p (p i) = i) → ∀ v, F (v.map (rowSig p)) = F v)
    (g : ℕ) : F (orbitInput g) = F hardFixedInputs := by
  have c0 : F (orbitInput 0) = F hardFixedInputs := rfl
  have c6 : F (orbitInput 6) = F hardFixedInputs :=
    (congrArg F oi6).symm.trans ((h hardSwap01 hardSwap01_inv (orbitInput 0)).trans c0)
  have c2 : F (orbitInput 2) = F hardFixedInputs :=
    (congrArg F oi2).symm.trans ((h hardSwap23 hardSwap23_inv (orbitInput 0)).trans c0)
  have c5 : F (orbitInput 5) = F hardFixedInputs :=
    (congrArg F oi5).symm.trans ((h hardSwap24 hardSwap24_inv (orbitInput 0)).trans c0)
  have c1 : F (orbitInput 1) = F hardFixedInputs :=
    (congrArg F oi1).symm.trans ((h hardSwap34 hardSwap34_inv (orbitInput 0)).trans c0)
  have c8 : F (orbitInput 8) = F hardFixedInputs :=
    (congrArg F oi8).symm.trans ((h hardSwap23 hardSwap23_inv (orbitInput 6)).trans c6)
  have c11 : F (orbitInput 11) = F hardFixedInputs :=
    (congrArg F oi11).symm.trans ((h hardSwap24 hardSwap24_inv (orbitInput 6)).trans c6)
  have c7 : F (orbitInput 7) = F hardFixedInputs :=
    (congrArg F oi7).symm.trans ((h hardSwap34 hardSwap34_inv (orbitInput 6)).trans c6)
  have c3 : F (orbitInput 3) = F hardFixedInputs :=
    (congrArg F oi3).symm.trans ((h hardSwap24 hardSwap24_inv (orbitInput 2)).trans c2)
  have c4 : F (orbitInput 4) = F hardFixedInputs :=
    (congrArg F oi4).symm.trans ((h hardSwap34 hardSwap34_inv (orbitInput 2)).trans c2)
  have c9 : F (orbitInput 9) = F hardFixedInputs :=
    (congrArg F oi9).symm.trans ((h hardSwap24 hardSwap24_inv (orbitInput 8)).trans c8)
  have c10 : F (orbitInput 10) = F hardFixedInputs :=
    (congrArg F oi10).symm.trans ((h hardSwap34 hardSwap34_inv (orbitInput 8)).trans c8)
  match g with
  | 0 => exact c0
  | 1 => exact c1
  | 2 => exact c2
  | 3 => exact c3
  | 4 => exact c4
  | 5 => exact c5
  | 6 => exact c6
  | 7 => exact c7
  | 8 => exact c8
  | 9 => exact c9
  | 10 => exact c10
  | 11 => exact c11
  | _+12 => rfl

def runPath (root : List Sig) : Nat → Nat → List Sig
  | 0, _ => root
  | n+1, code => pathStep (runPath root n (code / 1024)) (code % 1024)

lemma pathStep_swap (p : Fin 256 → Fin 256) (hp : ∀ i, p (p i) = i)
    (v : List Sig) (op : Nat) : pathStep (v.map (rowSig p)) op = (pathStep v op).map (rowSig p) := by
  have get (n : Nat) : (v.map (rowSig p)).getD n zero = rowSig p (v.getD n zero) := by
    simpa only [rowSig_zero] using (List.getD_map v zero (n := n) (rowSig p))
  have rdrop1 (a : Sig) : dropped [rowSig p a] (v.map (rowSig p)) =
      (dropped [a] v).map (rowSig p) := rowDropped p hp [a] v
  have rdrop2 (a b : Sig) : dropped [rowSig p a, rowSig p b] (v.map (rowSig p)) =
      (dropped [a,b] v).map (rowSig p) := rowDropped p hp [a,b] v
  unfold pathStep
  split
  · rfl
  · simp only [get]
    repeat' split
    all_goals simp only [List.map_cons, List.map_append, List.map_nil, rowSig_neg, rowSig_bin, rdrop1, rdrop2]

lemma runPath_map (p : Fin 256 → Fin 256) (hp : ∀ i, p (p i) = i)
    (root : List Sig) (n c : Nat) :
    runPath (root.map (rowSig p)) n c = (runPath root n c).map (rowSig p) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => simp only [runPath, ih, pathStep_swap p hp]

lemma runPath_swap (p : Fin 256 → Fin 256) (hp : ∀ i, p (p i) = i)
    (v : List Sig) (k t n c : Nat) :
    search k t (runPath (v.map (rowSig p)) n c) = search k t (runPath v n c) := by
  rw [runPath_map p hp]
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    have he := rowSearch p hp k t _ h
    have inv (x : Sig) : rowSig p (rowSig p x) = x := by
      simp only [rowSig, rowBits_invol p hp]
    simpa [List.map_map, Function.comp_def, inv] using he
  · exact rowSearch p hp k t _

lemma runPath_orbit_search (g k t n code : ℕ) :
    search k t (runPath (orbitInput g) n code) = search k t (runPath hardFixedInputs n code) := by
  apply orbitInput_invariant (fun v => search k t (runPath v n code))
  intro p hp v
  exact runPath_swap p hp v k t n code

def w0000ffff : Sig := (1237940039285380274899124223, 59703584327660668406666212705520255231818487836115522612586928367372427297791)

def w00ff00ff : Sig := (1427247692705959879820345930164114862557364223, 85146958530629405460705675947884613779855961196283132130824624978504802352191)

def w0f0f0f0f : Sig := (50216813883092018862993609466343854310113449563378795184127, 100314036597176880382363644869582923069880521704871934915862985236140934815175)

def w33333333 : Sig := (53919893284084465753007209210250462571680779585784624385834415554560, 108038927709355999715715070792889657484604121255611711916816819235020847574747)

def w55555555 : Sig := (1766793146530504370343479888235140797086803859812288403153663936092438528, 111915508473336097569643027900788782668937052960626137978137201621466988607341)

def w88888888 : Sig := (115790322390251417089456683098741172360718677254943623572316595982293694152703, 0)

def wa0a0a0a0 : Sig := (115790322444169664868985360094480467343748753359946133103203542890730584244224, 28270415781076374504488292491515953942263859289075121686930774012369305616)

def waa00aa00 : Sig := (115790322444169664919200641528798245508335005639785269812563312173320530558976, 226163326248610996035906339932127631538110874312600973495446192098954444928)

def waaaa0000 : Sig := (115790322444169664919200641528799672712472897861779513848792923905154692939776, 3618613219977775936574501438914042104609773989001615575927139073583271118848)

def waaaaaaaa : Sig := (115790322444169664919200641528799672712472897861780751751054430343977037201407, 3876580763980097853927957107899125184332931705014426061320382386446141032594)

def wc0c0c0c0 : Sig := (115792089183396302089269705419355304926922100050252786504511117192553377529856, 56540831562152749008976584983031907884527718578150243373861548024738611232)

def wcc00cc00 : Sig := (115792089183396302139486519255679271395328145321510929816312358466381934493696, 452326652497221992071812679864255263076221748625201946990892384197908889856)

def wcccc0000 : Sig := (115792089183396302139486519255680698643019522093958546513634827128124049719296, 7237226439955551873149002877828084209219547978003231151854278147166542237696)

def wcccccccc : Sig := (115792089183396302139486519255680698643019522093959784453672959622078714085375, 7753161527960195707855914215798250368665863410028852122640764772892282065188)

def weeeeeeee : Sig := (115792089237314549969230477685739198994773742700796912632410793983762057134079, 11629742291940293561783871323697375552998795115043278183961147159338423097782)

def wf000f000 : Sig := (115792089237316195373354171125594461742583669279980470650678025797291380572160, 904653304994443984143625359728510526152443497250403893981784768395817779712)

def wf0f00000 : Sig := (115792089237316195373354171125595888990276375199295471789304849099442733711360, 14474452879911103746298005755656168418439095956006462303708556294333084475392)

def wf0f0f0f0 : Sig := (115792089237316195373354171125595888990276375199296709729344134444534334455808, 15478052640139315041207340139104984783389462960768629123594598771772194824760)

def wfafafafa : Sig := (115792089237316195423569452559915094359000519701131328377195021897780787412991, 19326362988338336520630808954512594013780130806493980063228050384205966551738)

def wfcfcfcfc : Sig := (115792089237316195423570984961921282706373797243003707678505976874059671011327, 23174673336537358000054277769920203244170798652219331002861501996639738278716)

def wff000000 : Sig := (115792089237316195423570985008686480605577278705759505753488134512776746893312, 28948905759822207492596011511312336836878191912012924607417112588666168950784)

def wff00ff00 : Sig := (115792089237316195423570985008686480605577278705760743693527419893050572275712, 30645130706686789962865309060803294073414023469357431908632959029408327287744)

def wffaaffaa : Sig := (115792089237316195423570985008687907809715170927756225632018538063707078918143, 34295548144418276820757359828770291626208844300059256996457895223755513875410)

def wffccffcc : Sig := (115792089237316195423570985008687907853268655478209598330888021048747351867391, 37945965582149763678649410596737289179003665130761082084282831418102700463076)

def wfff0fff0 : Sig := (115792089237316195423570985008687907853269984625076982772193528540293526159360, 45218530041831661019929023840179768330651042932875657138245773032784704332792)

def wffff0000 : Sig := (115792089237316195423570985008687907853269984665639326099418298627638230515712, 56088504909655527016904772303167652621451496829525041426870655640540702342144)

def wffffaaaa : Sig := (115792089237316195423570985008687907853269984665640564001679805066460574777343, 56346472453657848934258227972152735701174654545537851912263898953403572255890)

def wffffcccc : Sig := (115792089237316195423570985008687907853269984665640564039456431121592894881791, 56604439997660170851611683641137818780897812261550662397657142266266442169636)

def wfffff0f0 : Sig := (115792089237316195423570985008687907853269984665640564039457583972729831260160, 57092104669883738311814106686616468986401863834287208246756698117979812691512)

def wffffff00 : Sig := (115792089237316195423570985008687907853269984665640564039457584007912055898112, 57784729856520109487174069852658609857987328386869548728086502081282860679104)

def orbitState0 : List Sig := [w0000ffff, waaaaaaaa, wcccccccc, wf0f0f0f0, wff00ff00, wffff0000]

def orbitState1 : List Sig := [w00ff00ff, waaaaaaaa, wcccccccc, wf0f0f0f0, wff00ff00, wffff0000]

def orbitState2 : List Sig := [w0f0f0f0f, waaaaaaaa, wcccccccc, wf0f0f0f0, wff00ff00, wffff0000]

def orbitState3 : List Sig := [w33333333, waaaaaaaa, wcccccccc, wf0f0f0f0, wff00ff00, wffff0000]

def orbitState4 : List Sig := [w55555555, waaaaaaaa, wcccccccc, wf0f0f0f0, wff00ff00, wffff0000]

def orbitState5 : List Sig := [w88888888, waaaaaaaa, wcccccccc, wf0f0f0f0, wff00ff00, wffff0000]

def orbitState6 : List Sig := [wa0a0a0a0, waaaaaaaa, wcccccccc, wf0f0f0f0, wff00ff00, wffff0000]

def orbitState7 : List Sig := [waa00aa00, waaaaaaaa, wcccccccc, wf0f0f0f0, wff00ff00, wffff0000]

def orbitState8 : List Sig := [waaaa0000, waaaaaaaa, wcccccccc, wf0f0f0f0, wff00ff00, wffff0000]

def orbitState9 : List Sig := [waaaaaaaa, wc0c0c0c0, wcccccccc, wf0f0f0f0, wff00ff00, wffff0000]

def orbitState10 : List Sig := [waaaaaaaa, wcc00cc00, wcccccccc, wf0f0f0f0, wff00ff00, wffff0000]

def orbitState11 : List Sig := [waaaaaaaa, wcccc0000, wcccccccc, wf0f0f0f0, wff00ff00, wffff0000]

def orbitState12 : List Sig := [waaaaaaaa, wcccccccc, weeeeeeee, wf0f0f0f0, wff00ff00, wffff0000]

def orbitState13 : List Sig := [waaaaaaaa, wcccccccc, wf000f000, wf0f0f0f0, wff00ff00, wffff0000]

def orbitState14 : List Sig := [waaaaaaaa, wcccccccc, wf0f00000, wf0f0f0f0, wff00ff00, wffff0000]

def orbitState15 : List Sig := [waaaaaaaa, wcccccccc, wf0f0f0f0, wfafafafa, wff00ff00, wffff0000]

def orbitState16 : List Sig := [waaaaaaaa, wcccccccc, wf0f0f0f0, wfcfcfcfc, wff00ff00, wffff0000]

def orbitState17 : List Sig := [waaaaaaaa, wcccccccc, wf0f0f0f0, wff000000, wff00ff00, wffff0000]

def orbitState18 : List Sig := [waaaaaaaa, wcccccccc, wf0f0f0f0, wff00ff00, wffaaffaa, wffff0000]

def orbitState19 : List Sig := [waaaaaaaa, wcccccccc, wf0f0f0f0, wff00ff00, wffccffcc, wffff0000]

def orbitState20 : List Sig := [waaaaaaaa, wcccccccc, wf0f0f0f0, wff00ff00, wfff0fff0, wffff0000]

def orbitState21 : List Sig := [waaaaaaaa, wcccccccc, wf0f0f0f0, wff00ff00, wffff0000, wffffaaaa]

def orbitState22 : List Sig := [waaaaaaaa, wcccccccc, wf0f0f0f0, wff00ff00, wffff0000, wffffcccc]

def orbitState23 : List Sig := [waaaaaaaa, wcccccccc, wf0f0f0f0, wff00ff00, wffff0000, wfffff0f0]

def orbitState24 : List Sig := [waaaaaaaa, wcccccccc, wf0f0f0f0, wff00ff00, wffff0000, wffffff00]

def orbitBounded (states : List (ℕ × List Sig)) (k t : ℕ) (v : List Sig) : Bool :=
  if states.any (fun s => s.1 == t && v.isPerm s.2) then false else search k t v

lemma orbitKnown (states : List (ℕ × List Sig)) (k t : ℕ) (v : List Sig)
    (hs : ∀ st ∈ states, search k st.1 st.2 = false)
    (hp : forward k t v (orbitBounded states k) = false) : search (k+1) t v = false := by
  have heq : orbitBounded states k = search k := by
    funext t' v'
    unfold orbitBounded
    split
    · rename_i hb
      obtain ⟨st, hmem, he, hv⟩ := (show ∃ st ∈ states, st.1 = t' ∧ v'.Perm st.2 by
        simpa only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq, List.isPerm_iff] using hb)
      rw [← he, search_perm k st.1 hv, hs st hmem]
    · rfl
  rw [heq] at hp
  exact hp

lemma orbit_move (p : Fin 256 → Fin 256) (hp : ∀ i, p (p i) = i)
    (k t : ℕ) (a b : List Sig) (h : search k t b = false) (he : (a.map (rowSig p)).Perm b) :
    search k t a = false := by
  cases hs : search k t a with
  | false => rfl
  | true =>
    have h' := rowSearch p hp k t a hs
    rw [search_perm k t he, h] at h'
    contradiction

set_option maxRecDepth 4000 in
lemma rx_hardSwap01_w55555555 : rowSig hardSwap01 w55555555 = w33333333 := by decide +kernel

set_option maxRecDepth 4000 in
lemma rx_hardSwap01_waaaaaaaa : rowSig hardSwap01 waaaaaaaa = wcccccccc := by decide +kernel

set_option maxRecDepth 4000 in
lemma rx_hardSwap01_wc0c0c0c0 : rowSig hardSwap01 wc0c0c0c0 = wa0a0a0a0 := by decide +kernel

set_option maxRecDepth 4000 in
lemma rx_hardSwap01_wcccccccc : rowSig hardSwap01 wcccccccc = waaaaaaaa := by decide +kernel

set_option maxRecDepth 4000 in
lemma rx_hardSwap01_wf0f0f0f0 : rowSig hardSwap01 wf0f0f0f0 = wf0f0f0f0 := by decide +kernel

set_option maxRecDepth 4000 in
lemma rx_hardSwap01_wfcfcfcfc : rowSig hardSwap01 wfcfcfcfc = wfafafafa := by decide +kernel

set_option maxRecDepth 4000 in
lemma rx_hardSwap01_wff00ff00 : rowSig hardSwap01 wff00ff00 = wff00ff00 := by decide +kernel

set_option maxRecDepth 4000 in
lemma rx_hardSwap01_wffff0000 : rowSig hardSwap01 wffff0000 = wffff0000 := by decide +kernel

set_option maxRecDepth 4000 in
lemma rx_hardSwap23_waa00aa00 : rowSig hardSwap23 waa00aa00 = wa0a0a0a0 := by decide +kernel

set_option maxRecDepth 4000 in
lemma rx_hardSwap23_waaaaaaaa : rowSig hardSwap23 waaaaaaaa = waaaaaaaa := by decide +kernel

set_option maxRecDepth 4000 in
lemma rx_hardSwap23_wcc00cc00 : rowSig hardSwap23 wcc00cc00 = wc0c0c0c0 := by decide +kernel

set_option maxRecDepth 4000 in
lemma rx_hardSwap23_wcccccccc : rowSig hardSwap23 wcccccccc = wcccccccc := by decide +kernel

set_option maxRecDepth 4000 in
lemma rx_hardSwap23_wf0f0f0f0 : rowSig hardSwap23 wf0f0f0f0 = wff00ff00 := by decide +kernel

set_option maxRecDepth 4000 in
lemma rx_hardSwap23_wff00ff00 : rowSig hardSwap23 wff00ff00 = wf0f0f0f0 := by decide +kernel

set_option maxRecDepth 4000 in
lemma rx_hardSwap23_wffaaffaa : rowSig hardSwap23 wffaaffaa = wfafafafa := by decide +kernel

set_option maxRecDepth 4000 in
lemma rx_hardSwap23_wffccffcc : rowSig hardSwap23 wffccffcc = wfcfcfcfc := by decide +kernel

set_option maxRecDepth 4000 in
lemma rx_hardSwap23_wffff0000 : rowSig hardSwap23 wffff0000 = wffff0000 := by decide +kernel

set_option maxRecDepth 4000 in
lemma rx_hardSwap24_w0f0f0f0f : rowSig hardSwap24 w0f0f0f0f = w0000ffff := by decide +kernel

set_option maxRecDepth 4000 in
lemma rx_hardSwap24_waaaa0000 : rowSig hardSwap24 waaaa0000 = wa0a0a0a0 := by decide +kernel

set_option maxRecDepth 4000 in
lemma rx_hardSwap24_waaaaaaaa : rowSig hardSwap24 waaaaaaaa = waaaaaaaa := by decide +kernel

set_option maxRecDepth 4000 in
lemma rx_hardSwap24_wcccc0000 : rowSig hardSwap24 wcccc0000 = wc0c0c0c0 := by decide +kernel

set_option maxRecDepth 4000 in
lemma rx_hardSwap24_wcccccccc : rowSig hardSwap24 wcccccccc = wcccccccc := by decide +kernel

set_option maxRecDepth 4000 in
lemma rx_hardSwap24_wf0f0f0f0 : rowSig hardSwap24 wf0f0f0f0 = wffff0000 := by decide +kernel

set_option maxRecDepth 4000 in
lemma rx_hardSwap24_wff000000 : rowSig hardSwap24 wff000000 = wf000f000 := by decide +kernel

set_option maxRecDepth 4000 in
lemma rx_hardSwap24_wff00ff00 : rowSig hardSwap24 wff00ff00 = wff00ff00 := by decide +kernel

set_option maxRecDepth 4000 in
lemma rx_hardSwap24_wffff0000 : rowSig hardSwap24 wffff0000 = wf0f0f0f0 := by decide +kernel

set_option maxRecDepth 4000 in
lemma rx_hardSwap24_wffffaaaa : rowSig hardSwap24 wffffaaaa = wfafafafa := by decide +kernel

set_option maxRecDepth 4000 in
lemma rx_hardSwap24_wffffcccc : rowSig hardSwap24 wffffcccc = wfcfcfcfc := by decide +kernel

set_option maxRecDepth 4000 in
lemma rx_hardSwap24_wffffff00 : rowSig hardSwap24 wffffff00 = wfff0fff0 := by decide +kernel

set_option maxRecDepth 4000 in
lemma rx_hardSwap34_w00ff00ff : rowSig hardSwap34 w00ff00ff = w0000ffff := by decide +kernel

set_option maxRecDepth 4000 in
lemma rx_hardSwap34_waaaaaaaa : rowSig hardSwap34 waaaaaaaa = waaaaaaaa := by decide +kernel

set_option maxRecDepth 4000 in
lemma rx_hardSwap34_wcccccccc : rowSig hardSwap34 wcccccccc = wcccccccc := by decide +kernel

set_option maxRecDepth 4000 in
lemma rx_hardSwap34_wf0f00000 : rowSig hardSwap34 wf0f00000 = wf000f000 := by decide +kernel

set_option maxRecDepth 4000 in
lemma rx_hardSwap34_wf0f0f0f0 : rowSig hardSwap34 wf0f0f0f0 = wf0f0f0f0 := by decide +kernel

set_option maxRecDepth 4000 in
lemma rx_hardSwap34_wff00ff00 : rowSig hardSwap34 wff00ff00 = wffff0000 := by decide +kernel

set_option maxRecDepth 4000 in
lemma rx_hardSwap34_wffff0000 : rowSig hardSwap34 wffff0000 = wff00ff00 := by decide +kernel

set_option maxRecDepth 4000 in
lemma rx_hardSwap34_wfffff0f0 : rowSig hardSwap34 wfffff0f0 = wfff0fff0 := by decide +kernel

set_option maxRecDepth 15000 in
lemma rootCover_9_1
    (h_8_0_0 : search 8 0 orbitState0 = false)
    (h_8_0_3 : search 8 0 orbitState3 = false)
    (h_8_1_5 : search 8 1 orbitState5 = false)
    (h_8_1_6 : search 8 1 orbitState6 = false)
    (h_8_1_12 : search 8 1 orbitState12 = false)
    (h_8_1_13 : search 8 1 orbitState13 = false)
    (h_8_1_15 : search 8 1 orbitState15 = false)
    (h_8_1_20 : search 8 1 orbitState20 = false)
    : search 9 1 hardFixedInputs = false := by
  have h_8_0_1 : search 8 0 orbitState1 = false := by
    apply orbit_move hardSwap34 hardSwap34_inv _ _ _ _ h_8_0_0
    simp only [orbitState1, orbitState0, List.map_cons, List.map_nil, rx_hardSwap34_w00ff00ff, rx_hardSwap34_waaaaaaaa, rx_hardSwap34_wcccccccc, rx_hardSwap34_wf0f0f0f0, rx_hardSwap34_wff00ff00, rx_hardSwap34_wffff0000] <;> first | rfl | decide
  have h_8_0_2 : search 8 0 orbitState2 = false := by
    apply orbit_move hardSwap24 hardSwap24_inv _ _ _ _ h_8_0_0
    simp only [orbitState2, orbitState0, List.map_cons, List.map_nil, rx_hardSwap24_w0f0f0f0f, rx_hardSwap24_waaaaaaaa, rx_hardSwap24_wcccccccc, rx_hardSwap24_wf0f0f0f0, rx_hardSwap24_wff00ff00, rx_hardSwap24_wffff0000] <;> first | rfl | decide
  have h_8_0_4 : search 8 0 orbitState4 = false := by
    apply orbit_move hardSwap01 hardSwap01_inv _ _ _ _ h_8_0_3
    simp only [orbitState4, orbitState3, List.map_cons, List.map_nil, rx_hardSwap01_w55555555, rx_hardSwap01_waaaaaaaa, rx_hardSwap01_wcccccccc, rx_hardSwap01_wf0f0f0f0, rx_hardSwap01_wff00ff00, rx_hardSwap01_wffff0000] <;> first | rfl | decide
  have h_8_1_7 : search 8 1 orbitState7 = false := by
    apply orbit_move hardSwap23 hardSwap23_inv _ _ _ _ h_8_1_6
    simp only [orbitState7, orbitState6, List.map_cons, List.map_nil, rx_hardSwap23_waa00aa00, rx_hardSwap23_waaaaaaaa, rx_hardSwap23_wcccccccc, rx_hardSwap23_wf0f0f0f0, rx_hardSwap23_wff00ff00, rx_hardSwap23_wffff0000] <;> first | rfl | decide
  have h_8_1_8 : search 8 1 orbitState8 = false := by
    apply orbit_move hardSwap24 hardSwap24_inv _ _ _ _ h_8_1_6
    simp only [orbitState8, orbitState6, List.map_cons, List.map_nil, rx_hardSwap24_waaaa0000, rx_hardSwap24_waaaaaaaa, rx_hardSwap24_wcccccccc, rx_hardSwap24_wf0f0f0f0, rx_hardSwap24_wff00ff00, rx_hardSwap24_wffff0000] <;> first | rfl | decide
  have h_8_1_9 : search 8 1 orbitState9 = false := by
    apply orbit_move hardSwap01 hardSwap01_inv _ _ _ _ h_8_1_6
    simp only [orbitState9, orbitState6, List.map_cons, List.map_nil, rx_hardSwap01_waaaaaaaa, rx_hardSwap01_wc0c0c0c0, rx_hardSwap01_wcccccccc, rx_hardSwap01_wf0f0f0f0, rx_hardSwap01_wff00ff00, rx_hardSwap01_wffff0000] <;> first | rfl | decide
  have h_8_1_10 : search 8 1 orbitState10 = false := by
    apply orbit_move hardSwap23 hardSwap23_inv _ _ _ _ h_8_1_9
    simp only [orbitState10, orbitState9, List.map_cons, List.map_nil, rx_hardSwap23_waaaaaaaa, rx_hardSwap23_wcc00cc00, rx_hardSwap23_wcccccccc, rx_hardSwap23_wf0f0f0f0, rx_hardSwap23_wff00ff00, rx_hardSwap23_wffff0000] <;> first | rfl | decide
  have h_8_1_11 : search 8 1 orbitState11 = false := by
    apply orbit_move hardSwap24 hardSwap24_inv _ _ _ _ h_8_1_9
    simp only [orbitState11, orbitState9, List.map_cons, List.map_nil, rx_hardSwap24_waaaaaaaa, rx_hardSwap24_wcccc0000, rx_hardSwap24_wcccccccc, rx_hardSwap24_wf0f0f0f0, rx_hardSwap24_wff00ff00, rx_hardSwap24_wffff0000] <;> first | rfl | decide
  have h_8_1_14 : search 8 1 orbitState14 = false := by
    apply orbit_move hardSwap34 hardSwap34_inv _ _ _ _ h_8_1_13
    simp only [orbitState14, orbitState13, List.map_cons, List.map_nil, rx_hardSwap34_waaaaaaaa, rx_hardSwap34_wcccccccc, rx_hardSwap34_wf0f00000, rx_hardSwap34_wf0f0f0f0, rx_hardSwap34_wff00ff00, rx_hardSwap34_wffff0000] <;> first | rfl | decide
  have h_8_1_16 : search 8 1 orbitState16 = false := by
    apply orbit_move hardSwap01 hardSwap01_inv _ _ _ _ h_8_1_15
    simp only [orbitState16, orbitState15, List.map_cons, List.map_nil, rx_hardSwap01_waaaaaaaa, rx_hardSwap01_wcccccccc, rx_hardSwap01_wf0f0f0f0, rx_hardSwap01_wfcfcfcfc, rx_hardSwap01_wff00ff00, rx_hardSwap01_wffff0000] <;> first | rfl | decide
  have h_8_1_17 : search 8 1 orbitState17 = false := by
    apply orbit_move hardSwap24 hardSwap24_inv _ _ _ _ h_8_1_13
    simp only [orbitState17, orbitState13, List.map_cons, List.map_nil, rx_hardSwap24_waaaaaaaa, rx_hardSwap24_wcccccccc, rx_hardSwap24_wf0f0f0f0, rx_hardSwap24_wff000000, rx_hardSwap24_wff00ff00, rx_hardSwap24_wffff0000] <;> first | rfl | decide
  have h_8_1_18 : search 8 1 orbitState18 = false := by
    apply orbit_move hardSwap23 hardSwap23_inv _ _ _ _ h_8_1_15
    simp only [orbitState18, orbitState15, List.map_cons, List.map_nil, rx_hardSwap23_waaaaaaaa, rx_hardSwap23_wcccccccc, rx_hardSwap23_wf0f0f0f0, rx_hardSwap23_wff00ff00, rx_hardSwap23_wffaaffaa, rx_hardSwap23_wffff0000] <;> first | rfl | decide
  have h_8_1_19 : search 8 1 orbitState19 = false := by
    apply orbit_move hardSwap23 hardSwap23_inv _ _ _ _ h_8_1_16
    simp only [orbitState19, orbitState16, List.map_cons, List.map_nil, rx_hardSwap23_waaaaaaaa, rx_hardSwap23_wcccccccc, rx_hardSwap23_wf0f0f0f0, rx_hardSwap23_wff00ff00, rx_hardSwap23_wffccffcc, rx_hardSwap23_wffff0000] <;> first | rfl | decide
  have h_8_1_21 : search 8 1 orbitState21 = false := by
    apply orbit_move hardSwap24 hardSwap24_inv _ _ _ _ h_8_1_15
    simp only [orbitState21, orbitState15, List.map_cons, List.map_nil, rx_hardSwap24_waaaaaaaa, rx_hardSwap24_wcccccccc, rx_hardSwap24_wf0f0f0f0, rx_hardSwap24_wff00ff00, rx_hardSwap24_wffff0000, rx_hardSwap24_wffffaaaa] <;> first | rfl | decide
  have h_8_1_22 : search 8 1 orbitState22 = false := by
    apply orbit_move hardSwap24 hardSwap24_inv _ _ _ _ h_8_1_16
    simp only [orbitState22, orbitState16, List.map_cons, List.map_nil, rx_hardSwap24_waaaaaaaa, rx_hardSwap24_wcccccccc, rx_hardSwap24_wf0f0f0f0, rx_hardSwap24_wff00ff00, rx_hardSwap24_wffff0000, rx_hardSwap24_wffffcccc] <;> first | rfl | decide
  have h_8_1_23 : search 8 1 orbitState23 = false := by
    apply orbit_move hardSwap34 hardSwap34_inv _ _ _ _ h_8_1_20
    simp only [orbitState23, orbitState20, List.map_cons, List.map_nil, rx_hardSwap34_waaaaaaaa, rx_hardSwap34_wcccccccc, rx_hardSwap34_wf0f0f0f0, rx_hardSwap34_wff00ff00, rx_hardSwap34_wffff0000, rx_hardSwap34_wfffff0f0] <;> first | rfl | decide
  have h_8_1_24 : search 8 1 orbitState24 = false := by
    apply orbit_move hardSwap24 hardSwap24_inv _ _ _ _ h_8_1_20
    simp only [orbitState24, orbitState20, List.map_cons, List.map_nil, rx_hardSwap24_waaaaaaaa, rx_hardSwap24_wcccccccc, rx_hardSwap24_wf0f0f0f0, rx_hardSwap24_wff00ff00, rx_hardSwap24_wffff0000, rx_hardSwap24_wffffff00] <;> first | rfl | decide
  apply orbitKnown [(0, orbitState0), (0, orbitState1), (0, orbitState2), (0, orbitState3), (0, orbitState4), (1, orbitState5), (1, orbitState6), (1, orbitState7), (1, orbitState8), (1, orbitState9), (1, orbitState10), (1, orbitState11), (1, orbitState12), (1, orbitState13), (1, orbitState14), (1, orbitState15), (1, orbitState16), (1, orbitState17), (1, orbitState18), (1, orbitState19), (1, orbitState20), (1, orbitState21), (1, orbitState22), (1, orbitState23), (1, orbitState24)] _ _ _ ?_ (by decide +kernel)
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact h_8_0_0
  · exact h_8_0_1
  · exact h_8_0_2
  · exact h_8_0_3
  · exact h_8_0_4
  · exact h_8_1_5
  · exact h_8_1_6
  · exact h_8_1_7
  · exact h_8_1_8
  · exact h_8_1_9
  · exact h_8_1_10
  · exact h_8_1_11
  · exact h_8_1_12
  · exact h_8_1_13
  · exact h_8_1_14
  · exact h_8_1_15
  · exact h_8_1_16
  · exact h_8_1_17
  · exact h_8_1_18
  · exact h_8_1_19
  · exact h_8_1_20
  · exact h_8_1_21
  · exact h_8_1_22
  · exact h_8_1_23
  · exact h_8_1_24

set_option maxRecDepth 15000 in
lemma rootCover_8_1
    (h_7_0_0 : search 7 0 orbitState0 = false)
    (h_7_0_3 : search 7 0 orbitState3 = false)
    (h_7_1_5 : search 7 1 orbitState5 = false)
    (h_7_1_6 : search 7 1 orbitState6 = false)
    (h_7_1_12 : search 7 1 orbitState12 = false)
    (h_7_1_13 : search 7 1 orbitState13 = false)
    (h_7_1_15 : search 7 1 orbitState15 = false)
    (h_7_1_20 : search 7 1 orbitState20 = false)
    : search 8 1 hardFixedInputs = false := by
  have h_7_0_1 : search 7 0 orbitState1 = false := by
    apply orbit_move hardSwap34 hardSwap34_inv _ _ _ _ h_7_0_0
    simp only [orbitState1, orbitState0, List.map_cons, List.map_nil, rx_hardSwap34_w00ff00ff, rx_hardSwap34_waaaaaaaa, rx_hardSwap34_wcccccccc, rx_hardSwap34_wf0f0f0f0, rx_hardSwap34_wff00ff00, rx_hardSwap34_wffff0000] <;> first | rfl | decide
  have h_7_0_2 : search 7 0 orbitState2 = false := by
    apply orbit_move hardSwap24 hardSwap24_inv _ _ _ _ h_7_0_0
    simp only [orbitState2, orbitState0, List.map_cons, List.map_nil, rx_hardSwap24_w0f0f0f0f, rx_hardSwap24_waaaaaaaa, rx_hardSwap24_wcccccccc, rx_hardSwap24_wf0f0f0f0, rx_hardSwap24_wff00ff00, rx_hardSwap24_wffff0000] <;> first | rfl | decide
  have h_7_0_4 : search 7 0 orbitState4 = false := by
    apply orbit_move hardSwap01 hardSwap01_inv _ _ _ _ h_7_0_3
    simp only [orbitState4, orbitState3, List.map_cons, List.map_nil, rx_hardSwap01_w55555555, rx_hardSwap01_waaaaaaaa, rx_hardSwap01_wcccccccc, rx_hardSwap01_wf0f0f0f0, rx_hardSwap01_wff00ff00, rx_hardSwap01_wffff0000] <;> first | rfl | decide
  have h_7_1_7 : search 7 1 orbitState7 = false := by
    apply orbit_move hardSwap23 hardSwap23_inv _ _ _ _ h_7_1_6
    simp only [orbitState7, orbitState6, List.map_cons, List.map_nil, rx_hardSwap23_waa00aa00, rx_hardSwap23_waaaaaaaa, rx_hardSwap23_wcccccccc, rx_hardSwap23_wf0f0f0f0, rx_hardSwap23_wff00ff00, rx_hardSwap23_wffff0000] <;> first | rfl | decide
  have h_7_1_8 : search 7 1 orbitState8 = false := by
    apply orbit_move hardSwap24 hardSwap24_inv _ _ _ _ h_7_1_6
    simp only [orbitState8, orbitState6, List.map_cons, List.map_nil, rx_hardSwap24_waaaa0000, rx_hardSwap24_waaaaaaaa, rx_hardSwap24_wcccccccc, rx_hardSwap24_wf0f0f0f0, rx_hardSwap24_wff00ff00, rx_hardSwap24_wffff0000] <;> first | rfl | decide
  have h_7_1_9 : search 7 1 orbitState9 = false := by
    apply orbit_move hardSwap01 hardSwap01_inv _ _ _ _ h_7_1_6
    simp only [orbitState9, orbitState6, List.map_cons, List.map_nil, rx_hardSwap01_waaaaaaaa, rx_hardSwap01_wc0c0c0c0, rx_hardSwap01_wcccccccc, rx_hardSwap01_wf0f0f0f0, rx_hardSwap01_wff00ff00, rx_hardSwap01_wffff0000] <;> first | rfl | decide
  have h_7_1_10 : search 7 1 orbitState10 = false := by
    apply orbit_move hardSwap23 hardSwap23_inv _ _ _ _ h_7_1_9
    simp only [orbitState10, orbitState9, List.map_cons, List.map_nil, rx_hardSwap23_waaaaaaaa, rx_hardSwap23_wcc00cc00, rx_hardSwap23_wcccccccc, rx_hardSwap23_wf0f0f0f0, rx_hardSwap23_wff00ff00, rx_hardSwap23_wffff0000] <;> first | rfl | decide
  have h_7_1_11 : search 7 1 orbitState11 = false := by
    apply orbit_move hardSwap24 hardSwap24_inv _ _ _ _ h_7_1_9
    simp only [orbitState11, orbitState9, List.map_cons, List.map_nil, rx_hardSwap24_waaaaaaaa, rx_hardSwap24_wcccc0000, rx_hardSwap24_wcccccccc, rx_hardSwap24_wf0f0f0f0, rx_hardSwap24_wff00ff00, rx_hardSwap24_wffff0000] <;> first | rfl | decide
  have h_7_1_14 : search 7 1 orbitState14 = false := by
    apply orbit_move hardSwap34 hardSwap34_inv _ _ _ _ h_7_1_13
    simp only [orbitState14, orbitState13, List.map_cons, List.map_nil, rx_hardSwap34_waaaaaaaa, rx_hardSwap34_wcccccccc, rx_hardSwap34_wf0f00000, rx_hardSwap34_wf0f0f0f0, rx_hardSwap34_wff00ff00, rx_hardSwap34_wffff0000] <;> first | rfl | decide
  have h_7_1_16 : search 7 1 orbitState16 = false := by
    apply orbit_move hardSwap01 hardSwap01_inv _ _ _ _ h_7_1_15
    simp only [orbitState16, orbitState15, List.map_cons, List.map_nil, rx_hardSwap01_waaaaaaaa, rx_hardSwap01_wcccccccc, rx_hardSwap01_wf0f0f0f0, rx_hardSwap01_wfcfcfcfc, rx_hardSwap01_wff00ff00, rx_hardSwap01_wffff0000] <;> first | rfl | decide
  have h_7_1_17 : search 7 1 orbitState17 = false := by
    apply orbit_move hardSwap24 hardSwap24_inv _ _ _ _ h_7_1_13
    simp only [orbitState17, orbitState13, List.map_cons, List.map_nil, rx_hardSwap24_waaaaaaaa, rx_hardSwap24_wcccccccc, rx_hardSwap24_wf0f0f0f0, rx_hardSwap24_wff000000, rx_hardSwap24_wff00ff00, rx_hardSwap24_wffff0000] <;> first | rfl | decide
  have h_7_1_18 : search 7 1 orbitState18 = false := by
    apply orbit_move hardSwap23 hardSwap23_inv _ _ _ _ h_7_1_15
    simp only [orbitState18, orbitState15, List.map_cons, List.map_nil, rx_hardSwap23_waaaaaaaa, rx_hardSwap23_wcccccccc, rx_hardSwap23_wf0f0f0f0, rx_hardSwap23_wff00ff00, rx_hardSwap23_wffaaffaa, rx_hardSwap23_wffff0000] <;> first | rfl | decide
  have h_7_1_19 : search 7 1 orbitState19 = false := by
    apply orbit_move hardSwap23 hardSwap23_inv _ _ _ _ h_7_1_16
    simp only [orbitState19, orbitState16, List.map_cons, List.map_nil, rx_hardSwap23_waaaaaaaa, rx_hardSwap23_wcccccccc, rx_hardSwap23_wf0f0f0f0, rx_hardSwap23_wff00ff00, rx_hardSwap23_wffccffcc, rx_hardSwap23_wffff0000] <;> first | rfl | decide
  have h_7_1_21 : search 7 1 orbitState21 = false := by
    apply orbit_move hardSwap24 hardSwap24_inv _ _ _ _ h_7_1_15
    simp only [orbitState21, orbitState15, List.map_cons, List.map_nil, rx_hardSwap24_waaaaaaaa, rx_hardSwap24_wcccccccc, rx_hardSwap24_wf0f0f0f0, rx_hardSwap24_wff00ff00, rx_hardSwap24_wffff0000, rx_hardSwap24_wffffaaaa] <;> first | rfl | decide
  have h_7_1_22 : search 7 1 orbitState22 = false := by
    apply orbit_move hardSwap24 hardSwap24_inv _ _ _ _ h_7_1_16
    simp only [orbitState22, orbitState16, List.map_cons, List.map_nil, rx_hardSwap24_waaaaaaaa, rx_hardSwap24_wcccccccc, rx_hardSwap24_wf0f0f0f0, rx_hardSwap24_wff00ff00, rx_hardSwap24_wffff0000, rx_hardSwap24_wffffcccc] <;> first | rfl | decide
  have h_7_1_23 : search 7 1 orbitState23 = false := by
    apply orbit_move hardSwap34 hardSwap34_inv _ _ _ _ h_7_1_20
    simp only [orbitState23, orbitState20, List.map_cons, List.map_nil, rx_hardSwap34_waaaaaaaa, rx_hardSwap34_wcccccccc, rx_hardSwap34_wf0f0f0f0, rx_hardSwap34_wff00ff00, rx_hardSwap34_wffff0000, rx_hardSwap34_wfffff0f0] <;> first | rfl | decide
  have h_7_1_24 : search 7 1 orbitState24 = false := by
    apply orbit_move hardSwap24 hardSwap24_inv _ _ _ _ h_7_1_20
    simp only [orbitState24, orbitState20, List.map_cons, List.map_nil, rx_hardSwap24_waaaaaaaa, rx_hardSwap24_wcccccccc, rx_hardSwap24_wf0f0f0f0, rx_hardSwap24_wff00ff00, rx_hardSwap24_wffff0000, rx_hardSwap24_wffffff00] <;> first | rfl | decide
  apply orbitKnown [(0, orbitState0), (0, orbitState1), (0, orbitState2), (0, orbitState3), (0, orbitState4), (1, orbitState5), (1, orbitState6), (1, orbitState7), (1, orbitState8), (1, orbitState9), (1, orbitState10), (1, orbitState11), (1, orbitState12), (1, orbitState13), (1, orbitState14), (1, orbitState15), (1, orbitState16), (1, orbitState17), (1, orbitState18), (1, orbitState19), (1, orbitState20), (1, orbitState21), (1, orbitState22), (1, orbitState23), (1, orbitState24)] _ _ _ ?_ (by decide +kernel)
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact h_7_0_0
  · exact h_7_0_1
  · exact h_7_0_2
  · exact h_7_0_3
  · exact h_7_0_4
  · exact h_7_1_5
  · exact h_7_1_6
  · exact h_7_1_7
  · exact h_7_1_8
  · exact h_7_1_9
  · exact h_7_1_10
  · exact h_7_1_11
  · exact h_7_1_12
  · exact h_7_1_13
  · exact h_7_1_14
  · exact h_7_1_15
  · exact h_7_1_16
  · exact h_7_1_17
  · exact h_7_1_18
  · exact h_7_1_19
  · exact h_7_1_20
  · exact h_7_1_21
  · exact h_7_1_22
  · exact h_7_1_23
  · exact h_7_1_24

set_option maxRecDepth 15000 in
lemma rootCover_8_0
    (h_7_0_5 : search 7 0 orbitState5 = false)
    (h_7_0_6 : search 7 0 orbitState6 = false)
    (h_7_0_12 : search 7 0 orbitState12 = false)
    (h_7_0_13 : search 7 0 orbitState13 = false)
    (h_7_0_15 : search 7 0 orbitState15 = false)
    (h_7_0_20 : search 7 0 orbitState20 = false)
    : search 8 0 hardFixedInputs = false := by
  have h_7_0_7 : search 7 0 orbitState7 = false := by
    apply orbit_move hardSwap23 hardSwap23_inv _ _ _ _ h_7_0_6
    simp only [orbitState7, orbitState6, List.map_cons, List.map_nil, rx_hardSwap23_waa00aa00, rx_hardSwap23_waaaaaaaa, rx_hardSwap23_wcccccccc, rx_hardSwap23_wf0f0f0f0, rx_hardSwap23_wff00ff00, rx_hardSwap23_wffff0000] <;> first | rfl | decide
  have h_7_0_8 : search 7 0 orbitState8 = false := by
    apply orbit_move hardSwap24 hardSwap24_inv _ _ _ _ h_7_0_6
    simp only [orbitState8, orbitState6, List.map_cons, List.map_nil, rx_hardSwap24_waaaa0000, rx_hardSwap24_waaaaaaaa, rx_hardSwap24_wcccccccc, rx_hardSwap24_wf0f0f0f0, rx_hardSwap24_wff00ff00, rx_hardSwap24_wffff0000] <;> first | rfl | decide
  have h_7_0_9 : search 7 0 orbitState9 = false := by
    apply orbit_move hardSwap01 hardSwap01_inv _ _ _ _ h_7_0_6
    simp only [orbitState9, orbitState6, List.map_cons, List.map_nil, rx_hardSwap01_waaaaaaaa, rx_hardSwap01_wc0c0c0c0, rx_hardSwap01_wcccccccc, rx_hardSwap01_wf0f0f0f0, rx_hardSwap01_wff00ff00, rx_hardSwap01_wffff0000] <;> first | rfl | decide
  have h_7_0_10 : search 7 0 orbitState10 = false := by
    apply orbit_move hardSwap23 hardSwap23_inv _ _ _ _ h_7_0_9
    simp only [orbitState10, orbitState9, List.map_cons, List.map_nil, rx_hardSwap23_waaaaaaaa, rx_hardSwap23_wcc00cc00, rx_hardSwap23_wcccccccc, rx_hardSwap23_wf0f0f0f0, rx_hardSwap23_wff00ff00, rx_hardSwap23_wffff0000] <;> first | rfl | decide
  have h_7_0_11 : search 7 0 orbitState11 = false := by
    apply orbit_move hardSwap24 hardSwap24_inv _ _ _ _ h_7_0_9
    simp only [orbitState11, orbitState9, List.map_cons, List.map_nil, rx_hardSwap24_waaaaaaaa, rx_hardSwap24_wcccc0000, rx_hardSwap24_wcccccccc, rx_hardSwap24_wf0f0f0f0, rx_hardSwap24_wff00ff00, rx_hardSwap24_wffff0000] <;> first | rfl | decide
  have h_7_0_14 : search 7 0 orbitState14 = false := by
    apply orbit_move hardSwap34 hardSwap34_inv _ _ _ _ h_7_0_13
    simp only [orbitState14, orbitState13, List.map_cons, List.map_nil, rx_hardSwap34_waaaaaaaa, rx_hardSwap34_wcccccccc, rx_hardSwap34_wf0f00000, rx_hardSwap34_wf0f0f0f0, rx_hardSwap34_wff00ff00, rx_hardSwap34_wffff0000] <;> first | rfl | decide
  have h_7_0_16 : search 7 0 orbitState16 = false := by
    apply orbit_move hardSwap01 hardSwap01_inv _ _ _ _ h_7_0_15
    simp only [orbitState16, orbitState15, List.map_cons, List.map_nil, rx_hardSwap01_waaaaaaaa, rx_hardSwap01_wcccccccc, rx_hardSwap01_wf0f0f0f0, rx_hardSwap01_wfcfcfcfc, rx_hardSwap01_wff00ff00, rx_hardSwap01_wffff0000] <;> first | rfl | decide
  have h_7_0_17 : search 7 0 orbitState17 = false := by
    apply orbit_move hardSwap24 hardSwap24_inv _ _ _ _ h_7_0_13
    simp only [orbitState17, orbitState13, List.map_cons, List.map_nil, rx_hardSwap24_waaaaaaaa, rx_hardSwap24_wcccccccc, rx_hardSwap24_wf0f0f0f0, rx_hardSwap24_wff000000, rx_hardSwap24_wff00ff00, rx_hardSwap24_wffff0000] <;> first | rfl | decide
  have h_7_0_18 : search 7 0 orbitState18 = false := by
    apply orbit_move hardSwap23 hardSwap23_inv _ _ _ _ h_7_0_15
    simp only [orbitState18, orbitState15, List.map_cons, List.map_nil, rx_hardSwap23_waaaaaaaa, rx_hardSwap23_wcccccccc, rx_hardSwap23_wf0f0f0f0, rx_hardSwap23_wff00ff00, rx_hardSwap23_wffaaffaa, rx_hardSwap23_wffff0000] <;> first | rfl | decide
  have h_7_0_19 : search 7 0 orbitState19 = false := by
    apply orbit_move hardSwap23 hardSwap23_inv _ _ _ _ h_7_0_16
    simp only [orbitState19, orbitState16, List.map_cons, List.map_nil, rx_hardSwap23_waaaaaaaa, rx_hardSwap23_wcccccccc, rx_hardSwap23_wf0f0f0f0, rx_hardSwap23_wff00ff00, rx_hardSwap23_wffccffcc, rx_hardSwap23_wffff0000] <;> first | rfl | decide
  have h_7_0_21 : search 7 0 orbitState21 = false := by
    apply orbit_move hardSwap24 hardSwap24_inv _ _ _ _ h_7_0_15
    simp only [orbitState21, orbitState15, List.map_cons, List.map_nil, rx_hardSwap24_waaaaaaaa, rx_hardSwap24_wcccccccc, rx_hardSwap24_wf0f0f0f0, rx_hardSwap24_wff00ff00, rx_hardSwap24_wffff0000, rx_hardSwap24_wffffaaaa] <;> first | rfl | decide
  have h_7_0_22 : search 7 0 orbitState22 = false := by
    apply orbit_move hardSwap24 hardSwap24_inv _ _ _ _ h_7_0_16
    simp only [orbitState22, orbitState16, List.map_cons, List.map_nil, rx_hardSwap24_waaaaaaaa, rx_hardSwap24_wcccccccc, rx_hardSwap24_wf0f0f0f0, rx_hardSwap24_wff00ff00, rx_hardSwap24_wffff0000, rx_hardSwap24_wffffcccc] <;> first | rfl | decide
  have h_7_0_23 : search 7 0 orbitState23 = false := by
    apply orbit_move hardSwap34 hardSwap34_inv _ _ _ _ h_7_0_20
    simp only [orbitState23, orbitState20, List.map_cons, List.map_nil, rx_hardSwap34_waaaaaaaa, rx_hardSwap34_wcccccccc, rx_hardSwap34_wf0f0f0f0, rx_hardSwap34_wff00ff00, rx_hardSwap34_wffff0000, rx_hardSwap34_wfffff0f0] <;> first | rfl | decide
  have h_7_0_24 : search 7 0 orbitState24 = false := by
    apply orbit_move hardSwap24 hardSwap24_inv _ _ _ _ h_7_0_20
    simp only [orbitState24, orbitState20, List.map_cons, List.map_nil, rx_hardSwap24_waaaaaaaa, rx_hardSwap24_wcccccccc, rx_hardSwap24_wf0f0f0f0, rx_hardSwap24_wff00ff00, rx_hardSwap24_wffff0000, rx_hardSwap24_wffffff00] <;> first | rfl | decide
  apply orbitKnown [(0, orbitState5), (0, orbitState6), (0, orbitState7), (0, orbitState8), (0, orbitState9), (0, orbitState10), (0, orbitState11), (0, orbitState12), (0, orbitState13), (0, orbitState14), (0, orbitState15), (0, orbitState16), (0, orbitState17), (0, orbitState18), (0, orbitState19), (0, orbitState20), (0, orbitState21), (0, orbitState22), (0, orbitState23), (0, orbitState24)] _ _ _ ?_ (by decide +kernel)
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact h_7_0_5
  · exact h_7_0_6
  · exact h_7_0_7
  · exact h_7_0_8
  · exact h_7_0_9
  · exact h_7_0_10
  · exact h_7_0_11
  · exact h_7_0_12
  · exact h_7_0_13
  · exact h_7_0_14
  · exact h_7_0_15
  · exact h_7_0_16
  · exact h_7_0_17
  · exact h_7_0_18
  · exact h_7_0_19
  · exact h_7_0_20
  · exact h_7_0_21
  · exact h_7_0_22
  · exact h_7_0_23
  · exact h_7_0_24

def repPaths : Nat → Nat → Nat
  | 5, 0 => 0xffe9a7a1a0ffe9a9a051ffe9a6a1d1ffe9a6a1e0ffe9a0a298ffe9a0a258ffe9aa6031ffe9aa6030ffe9aa6028ffe9a96031ffe9a661e8ffe9a661e0ffe5a6a4d9ffe5a6a419ffe5aa4430ffe5a445e9ffe5a445a9ffe5a445a8ffe5a444e8ffe5a44428ffe5a146a0ffe5a14660ffe5a145a0ffe5a144e0ffe5a14420ffe5a14690ffe5a14650ffe5aaa063ffe5aaa01affe5aaa018ffe5a7a191ffe5a7a0d1ffe5a7a011ffe5a7a1a0ffe5a7a0d0ffe5a9a063ffe5a9a051ffe5a9a068ffe5a6a1e0ffe5a6a120ffe5a6a060ffe5aa6063ffe5a761a8ffe5a761a0ffe5a96063ffe5a96051ffe5a96070ffe5a96068ffe90ab028ffe90ab018ffe909b051ffe909b068ffe909b060ffe909b058ffe90a8c18ffe90a8830ffe9098851ffe90a8030ffe90a8028ffe90781e8ffe90781a8ffe90780e8ffe9078028ffe90781a0ffe90780e0ffe9078020ffe9098051ffe90681a9ffe90681d9ffe90681d1ffe90681e8ffe90681a8ffe90681e0ffe90a6028ffe9096062ffe9096051ffe90661d9ffe9066119ffe9066059ffe90661e0ffe50ab028ffe50ab018ffe509b051ffe509b058ffe50a8c28ffe50a8c20ffe50a8c18ffe5098c58ffe50a8830ffe5098851ffe5098860ffe50445e1ffe50781e9ffe50781e1ffe5078199ffe5078191ffe50781e8ffe50781a8ffe50781a0ffe5098051ffe5098070ffe5098068ffe50681e8ffe5068128ffe5068068ffe50681a8ffe50681e0ffe5068120ffe5068060ffe507611affe50761e1ffe50761e0ffe50761a0ffe5096068ffe88a8c30ffe88a8c18ffe8898c51ffe8898c60ffe8898c58ffe88a6420ffe88a6028ffe88761e0ffe88761a0ffe88760e0ffe8876020ffe8896051ffe88661a1ffe88661d1ffe88661e0ffe88661a0ffe48a8c30ffe48a8c20ffe48a8c18ffe4898c51ffe4898c58ffe4896451ffe4896460ffe48445d9ffe4844599ffe481469affe481465affe4814690ffe4814650ffe48a6063ffe48761e1ffe48761a1ffe4876191ffe48761e0ffe48761a0ffe484611affe484605affe48461e1ffe4846121ffe4846061ffe48162a3ffe4816263ffe4816299ffe4816259ffe4816291ffe4816298ffe4816258ffe4816288ffe4816248ffe4896063ffe4896069ffe4896051ffe4896068ffe48661e0ffe4866120ffe4866060ffe48661a0ffd449b051ffd4496851ffd4198c51a6aa916080a69e868080a69e8201e0a69e8201a0a69e820108a6a6814480a69a878080a69a874080a69a8201e0a69a8201a0a6828a6080a682896080a6828501e0a6828501a0a6828501d0a6a9820031a6a9820070a6a9820068a6a5820031a69987a080a699878080a6998201e8a6998201a8a6998201e0a6998201a0a69406c450a69400c5c8a69400c448a694078430a694078428a69407c051a69401c1e1a69401c1a1a69401c0c8a69406c011a694078032a694068032a694068011a694068070a694044032a694044071a694044059a6880aa420a6880a4430a68807a1d1a68807a1a0a68801a291a68801a298a68801a258a68801a288a68809a051a68806a1e0a6880a6071a6880761a8a6880761a0a688096071a688096051a688096070a6880661e8a688066128a688066068a6880661e0a6880a207196aa92006096aa92005896a690608096a912005196a912007096a9120058969117a480969110a14096911500319691150070969115005896851a8080968519808096851681409685138140968510814096851a4080968519408096851501a996851500e9968515002996851501e89685150128968515006896851501a896851501d8968515019896851501d09685150110968515005096aa820063969e868080969e864080969e804140969e85001a969e850019969e8201e0969e8201a0969e82019096a682006396a6820028969a878080969a818140969a850069969a850028969a8201e0969a8201a0969a8200e0969a82002096a9820063969d86a080969d868080969d8201e8969d8201a8969d8201e0969d8201a096a582006396a582003096a5820028969406c821969406c8609694046830969404681096940169a896940168e89694016828969401698896940168c89694016808969407c419969407c410969406c46896940684709694068468969407c063969407c051969406c063969406c019969406c011969407806396940780519694068063969403401996880aa42096880aa418968809a451968809a45896880a443096880a44189688094451968807a1a0968809a051968806a191968806a1e096880761a896880761a0968809605196880661e896880661e0a42ac06080a42ac20068a42ac20058a42ac20018a426c16080a426c20028a426c20020a426c20058a426c20018a42a306080a42a220070a426220018a42a116080a42a020070a42a020068a42a020058a41e07a080a41e06a080a41e00a140a41e068080a41e008140a41e050031a41e050029a41e050070a41e050068a41e050058a41e0201e8a41e020128a41e020068a41e0201a8a41e0201e0a41e020120a41e020060a41e0201a0a41e0201d0a41a07a080a41a06a080a41a078080a41a076080a41a066080a41a074080a41a0201e8a41a0201a8a41a0201e0a41a0201a0a429820068a419878080a419876080a419850062a4198201e0a4198201a0a414078c20a41407a430a41407a428a41406a450a414078428a414068461a41407a051a41406a011a414078061a414068011a414044059a4080ab028a4080ab018a40809b051a40809b058a4080a8c18a4080a8830a408098851a408098858a4080781a9a4080781d9a4080781d1a4080781e8a4080781a8a4080781a0a408098051a4080681e8a4080681a8a4080681e0a4080761d9a4080761e0a4080761a0a408096051a4080661e0942ac06080942ac20068942ac20058942ac200189426c160809426c200589426c20018942a306080942a320068942a320060942a320058942a3200189426316080942a220070942a22005894262200589429a20058942a12005894261060809429120058941d1784809411150058941e07a080941e06a080941e068080941e076080941e066080941e064080941e0201e8941e0201a8941e0201e0941e0201a0941e020198941e020190942602003094260200289426020018941a07a080941a01a140941a06a080941a078080941a018140941a050071941a050069941a050030941a050028941a050018941a0201e8941a0201a8941a0200e8941a020028941a0201e0941a0201a0941a0200e0941a020020941a020190941d878080941d868080941d866080941d8201e0941d8201a094258200289414046810941407a410941406a470941406a4689414068468941407a051941406a0119414078051941403401994080ab02894080ab018940809b051940809b05894080a8c189408098c5894080a883094080a8818940809885194080a6818940809685194080a8418940809845894080a441894080781e894080781a894080781a0940809805194080681e994080681e19408068199940806819194080681e894080681a894080681e094080761e094080761a0940809605194080661e1940806619994080661e094080661a0a22a306080a22a320070a22a320058a22a320018a226316080a226320020a226320058a226320018a229916080a225920018a229820068a229820058a21d878080a21d868080a21d808140a21d850029a21d850068a21d850058a21d8201e0a21d820120a21d820060a21d8201a0a21d8201d0a219878080a219868080a219874080a219864080a2198201e0a2198201a0a214078428a214068450a214078051a214068011a214044059a214044010a2080a8c30a2080a8c18a208098c51a208098c58a2080a6418a208096458a2080761a1a2080761d1a2080761e0a2080761a0a208096051a2080661e0a2080661a0922a306080922a320070922a320060922a320058922a3200189226316080922632005892263200189229920058922590608092259200589229120051922912005892111764809211166480921115005892051a6880920519688092051a4080920519408092051501d8920515019892051501d09205150110920515005092298200639229820051921d878480921d868480921d864480921d878080921d868080921d874080921d864080921d8201e0921d8201a0921d820190921181694092118784809211850063921185006a92058a8c809205898c8092058a6480920589648092058a448092058a6080920589608092058a2080920589208092058501e092058501a092058501909225820063922582006992258200519225820028922582001892198780809219818140921986808092198500699219850028921985001892198201e092198201a092198200e09219820020921982019092198200c89214046810921401698892140168c892140168089214078410921404846392140484699214018588921401840892140684689214078063921407806a921407805192140780289214068063921406806a92140680119214038063921403806a9214038029921400811a921400805a92140081e19214008121921400806192140081a1921400810892140340219214034019921403405092080a8c3092080a8c189208098c519208098c5892080a6418920809645892080a44189208094451920809446092080a602892080761e092080761a092080760e09208076020920809605192080661e192080661a1920806619192080661e092080661a092080361e192080361a192080360e1920803602192080062a39208006263920800629992080062599208006291920800625192080062989208006258920800628892080062489208092021512ac6a060512ac36021512ac061e05126c444205126c145985126c144d85126c144185126c145105126c144d05126c7a0205126c4605a5126c161a05126c3605a512a27c030512a27c028512a27c020512a26c060512a26a059512a26a060512a26a058512a2061e8512a2061e0512627c020512626c070512626c068512626c060512627a02051262161a851262161a05129a7a0305129a7a0285129a7a0205129a6a0605129a061e05125a145105125a144d05125a7a0205125a4a05a5125a4a0715125a1a1185125a1a0d85125a6a0705125a6a0685125a6a0605125a4805a5125a480695125a4605a5125a460695125a460615125a161a05125a3605a5125a360695125a36068512a10c0d8512616c858512616c4195126174430512614443051261145a851261144e85126114428512617c019512617c011512616c068512917a030512917a02851291780285129168051512516a070512516a0685125168068512a076830512a07c419512a07c019512a07c020512a06c051512a06c050511e0aac20511e0aac18511e09ac58511e0a8c20511e0a8c18511e098c51511e098c70511e098c68511e098c60511e098c58511e0aa820511e09a851511e09a860511e096851511e096860511e0aa458511e09a451511e06a599511e06a5d8511e0a4430511e0745a8511e0744e8511e074428511e0aa01a511e0aa020511e07a0d1511e07a011511e07a1a0511e07a0d8511e09a051511e09a018511e06a199511e06a1d1511e06a1e0511e06a1d0511e096051511e066199511e0661d1511e0661e8511e0661a8511e0661e0511e0661a0511e0661d0511e09405a511e0641a9511e0641a851260668585126014590512607c011512607c010512606c051512607605a51260760195126076030511a0aac18511a09ac60511a09ac58511a0a8c18511a098c51511a098c70511a098c68511a098c60511a098c58511a0aa820511a09a851511a09a858511a0a6820511a0aa420511a09a451511a09a418511a0645a9511a07a1d9511a07a191511a07a1a0511a07a190511a09a051511a06a199511a06a1e0511a06a1d8511a0761d9511a0761e8511a0761a8511a0761e0511a0761a0511a076190511a0a401a511a0a4030511a0740d1511a074011511a0741e8511a0741a8511a0740e8511a074028512907a418512906a051512906a050512906a01051290680515129068050511d0ab028511d0ab018511d09b051511d09b058511d0a8c20511d0a8c18511d098c58511d0a8830511d0a8818511d098851511d098860511d096860511d0a8458511d0a6458511d096451511d096468511d096460511d0745d9511d0781e8511d0781a8511d0781a0511d098051511d068199511d0681d1511d0681e8511d0681a8511d0681e0511d0681d0511d0761e0511d0761a0511d096051511d066199511d0661d1511d0661e0511d0661a0511d0661d0511d09405a51250668585125066850512506a4585125014590512507a011512507a050512507a01051250780115125078050512507801051250680685125068060512507605a512507601951190ab02851190ab018511909b051511909b060511909b05851190a8c185119098c605119098c5851190a883051190a88205119098851511909885851190a6820511909685151190968585119098451511909841851190964515119096468511909641851190645d051190781a951190781e151190781d9511907819151190781e851190781a851190781a05119078190511909805151190681e851190681a851190681e051190761d9511907619151190761e051190761a0511907619051190960515119096068511909606051190661e05119066120511906606051190661a0511906611851190a401a506a37c020506a36c060506a30c118506a30c0d8506a36a060506a346031506a346030506a336031506a3061e8506a3061e0506636c419506634443050663145a850663144e85066314428506631451050663144d0506637c011506637c020506637c010506636c070506636c068506636c060506637a020506634605a50663161a850663161a0506633605a5069a7a0305069a7a0285069a7a0205069a6a0605069a061e05065a7a0205065a6a0705065a6a0685065a6a0605065a161a05069978818506997a030506997a0285069968059506596a070506596a0685069178028506514805a506514806950651181185065168068506987a030506986a051506986a050505d8ab020505d8ab018505d89b051505d89b058505d8a8c20505d8a8c18505d898c58505d898860505d896851505d896868505d896860505d8a8430505d8a8458505d898451505d8a8030505d8781e8505d8781a8505d8780e8505d878028505d8781a0505d878198505d898051505d8681a9505d8681e1505d868199505d8681d1505d8681e8505d8681a8505d8681e0505d8681d0505d868190505d866199505d8661e0505d8661a0505d8661d0505d8641e0505d8641a050658668585065814590506587a011506587a010506587605a50598ab02050598ab018505989b051505989b060505989b05850598a8c185059898c605059898c5850598a8820505989885850598a682050598968515059896868505989686050598a843050598984515059898418505987659850598645d850598781d9505987819150598781e850598781a850598781a050598781d05059878190505989805150598681e850598681a850598681e050598681d850598a605850598761d9505987619150598761e050598761a05059876190505989605150598741da50598740d150598741e050598741a0506907841850690780115069068051506906805050690680105069066060505d0a8c30505d0a8c20505d0a8c18505d098c51505d098c58505d0a6818505d096860505d0a6458505d096451505d074590505d0744d0505d0761d9505d0761e0505d0761a0505d076198505d096051505d066199505d0661d1505d0661e0505d0661a0505d0661d0505d09405a505d094060505d0641d8505d064118505d064058505d0641985065066858506506685050650684585065014590506507801150650780505065078010506507605a506507601950590a8c3050590a8c185059098c515059098c605059098c5850590a6820505909685850590964185059094460505906451850590645d05059064510505906445050590761d9505907619150590761e050590761a0505907619850590761d05059076190505909605150590661d150590661e050590661a050590661d850590a401a50590740d1505907401150590741d85059074198
  | 5, 1 => 0xffe5a6a419a682896051a682896068a682896058a6a980a029a6a581442096a910c051969116a051968519805196851082909685108250968510828896851a402996851a402896851a4020968519402996aa818c1896aa818c0896aa80601a969e86401a969e83401a969e834019969e834010969e8040d1969e80401196a6818c1896a681445a96a681a06396a681a051969a84806996a9818c28969d86806896a5818c2896a581445a96a581c06396a581c05196a581a06396a581a051a426c14420a426c14410a426c16028a426214428a41e07a028a41e038029a426014428a426014420a41a06a460a41a06a458a41a076428a41a07a011a41a06a068a41a06a058a425814420942ac0a060942ac060689426c144209426c16051942a3060689426214428941e07a420941e078420941e078418941e07a020941e06a051941e06a050941e076011941e076028942601c051942601a051941a06a068941a048069941d878418941d878028942581a051a226314428a226314410a226318020a226316028a21d878028a21d838029a225814420a219868458a219878011a219878028a219878010a219868068a219868058922a30c058922a308060922a306068922631442892263160519225918051922591804892051a682892051a68189205196851920519686092051a40209205194051921d878428921d878011921d878028921d878018921d868051921d868050921187846392118484639211848469921181851a921181845a92058a8c189205898c51920589645192058964609205894451920589446092058a602892058a601892058960519205892051922581a063922581a069922581a051922581a04892198480699219868068
  | 6, 0 => 0x3ffa6aa9ffe9aaa3ffa69e8ffe9a9a3ffa69a8ffe9a3a3ffa6828ffe9aa63ffa6a58ffe9a663ff96aa9ffe5a9a7ff969a9ffe5aa47ff96911ffe5a147ff96aa8ffe5a7a3ff96a68ffe5a6a3ff96a98ffe5a763ff96a58ffe90ab3ffa426cffe90a8fffa42a2ffe9098bffa429affe9076bffa42a1ffe90a83ffa41e0ffe90983ffa41a0ffe90a63ffa4258ffe90663ff942acffe509b3ff942a3ffe5098fff942a2ffe5098bff9429affe5096bff942a1ffe50987ff94291ffe50447ff942a0ffe50783ff94260ffe50683ff94298ffe50763ff94258ffe88a8fffa2263ffe88a67ffa2259ffe88a63ffa21d8ffe88963ffa2198ffe48a8fff92263ffe48a67ff92259ffe48a47ff92111ffe48147ff92298ffe48763ff92118ffe48163ff92258ffe48663ffa6880ffe5a203ffa4080ffe50203ffa2080ffe48203ff512acffd449b3ff512a2ffd4498bff5129affd4496bff506a3ffd4198fff5069affd4196a9aaa080a69e85029a7a080a6a682029a6a140a69a82029a3a140a68285029aa6080a6a582029a66140a69982029a501f1a69406c69a500f1a69400c69a501e1a69406869a501f0a69404c29a50070a69406c29a501e0a69406829a50110a6880aa69a20291a6880aa29a201e8a68804a29a20068a68809a29a201a8a6880a629a201d8a68809629a20198a6880a225aaa48096a912025a44540968515025aaa080969e85025a7a08096a682025a6a140969a82025aa6080969d85025a7608096a582025a501b29694046a5a5005a969407c65a501b1969407865a501a1969407c25a501b0969407825a501a0969403425a202a9968809a65a20291968809465a202a8968807a25a20268968806a25a20298968807625a20258968806625a20248a42ac202909b080a42a22029098880a42a02029078140a41e02029098080a41a05029068080a42982029096080a41985029066080a414078e90501e9a41406a690501e1a414068690501e8a41406a290501e0a41406829050118a414044290202aca40809b290202a3a4080a8a9020262a4080a6a90202a1a4080a4690202a0a40807829020260a40806829020298a40807629020258a40806629020290a4080a2250ab0809426c20250a8c80942a220250988809429a20250a8480942912025044540942a02025078140941e02025098080941a05025068080942982025076140941d820250960809414046a50501e9941406a650501e19414068650501e8941406a250501e09414068250500d89414034250202ac940809b250202a39408098e50202a29408098a502029a9408096a50202a19408098650202919408094650202a09408078250202609408068250202989408076250202589408066250202509408092288a8c80a226320288a6480a225920288a6080a21d85028876080a22582028866140a219820288501e1a214068688501e0a21406828850110a2080a8e8820263a2080a668820259a2080a468820298a20807628820258a20806628820288922a32024898c809229920248964809229120248445409205150248a6080921d8502487608092118502481614092258202486614092198202485011a9214016a48501e19214048648500619214068648501e09214068248500e09214008248500d092080a8e482026392080a66482025992080a46482025192080a6248201d89208096248201989208036248200189208092144ab1a8512ac68144ab0e0512ac08144ab118512ac66144ab0d8512ac061449b1115126c145449b1e85126c781449b1d85126c461449b0585126c36144a89ea512a27c144a89b0512a26a144a89a0512a246144a8998512a236144a88185126244544989f0512626c144989e85126278144989d85126246144988585126236144a69e85129a6a144a69a05129a46144a69985129a36144a68185125a44544968515125a7a144969285125a1a144969a85125a78144969205125a18144969d85125a46144968585125a36144a85f0512a16c144a84f0512a10c144a85a0512a166144a8418512616c944985b15126174544985115126114544985f0512616c144985e05126176144984585129178544a45e8512916a144a45e05129168144a45985129106144945d1512514454494451512517a144945a85125178144945a0512517614494458512a06c944a81da512a07c544a81f0512a06c144a81a0512a066144782ab511e09ad44782a3511e098d44782aa511e09a9447829a511e096944782a9511e09a544781a9511e0a654478259511e0a4544781d1511e0aa144781e8511e09a144781a8511e0a614478258511e06614478250511e0641449819a512607c544981b15126074544981115126014544981f0512606c144981e05126076144682ab511a09ad44682a3511a098d44682aa511a09a9446829a511a096944682a9511a09a54468299511a09654468251511a064544682a8511a07a14468268511a06a14468298511a07614468258511a0a4144681d05129076944a41e9512906a544a41e1512907a144a41a85129078144a41a05129066144742ac511d09b144742a3511d098d44742a2511d0989447429a511d096944742a1511d09854474299511d09654474291511d074544742a0511d07814474260511d06814474298511d07614474258511d066144742505125066944941e9512506a544941e15125068544941d1512504454494051512507a144941a85125078144941a05125076144642ac511909b144642a35119098d44642a251190989446429a5119096944642a15119098544642995119096544642515119064544642a0511907814464260511906814464298511907614464258511906614464290506a37c141a8db0506a33c141a8c30506a36a141a8da0506a346141a8d98506a336141a8c18506636c54198d11506631454198df0506636c14198de8506637814198dd8506634614198c585066336141a69e85069a6a141a69a05069a46141a69985069a36141a68185065a44541969e85065a6a141969e05065a76141969185065a16141968d85069978941a65e8506996a141a65a05069966141a64185065944541965e8506596a141965e05065976141964585069178141a45a05069166141a44185065174541945115065114541945e05065148141944605065168141945d85065116141a61da506987a541a61e8506986a141a61a05069866141762ac505d89b141762a3505d898d41762a2505d8989417629a505d896941762a1505d89854176299505d89654176291505d874541762a0505d87814176260505d86814176298505d89614176198505d8941417619050658789419619a506587a541961a95065874541961115065814541961e8506586a141961e05065876141662ac505989b141662a35059898d41662a250598989416629a5059896941662a150598985416629950598765416625950598945416619150598a8141661e05059898141661a050598a6141661d85059896141662905059874141a41da5069078541a41a15069078141a41a05069066141742a3505d098d417429a505d09694174299505d09654174291505d07454174298505d07614174258505d06614174250505d0641419419a5065078541941a15065074541941115065014541941e05065068141941d850590a8d416426350590a69416425a50590a65416425950590945416419150590a6141641d850590961416419850590a4141641d0
  | 6, 1 => 0x3ff969a9ffe5a447ff96851ffe9076bff941d1ffe50447ff92111ffe481469aaa458a69e86829a9a051a69a87469a6a1e0a69a87429a0a291a6828a629a0a258a6a980c69aa6030a6a980a29a96031a6a581469a661e8a69987825a9a418969a93665a6a41996a910c25a445e9969116a65a445a8969113a25a4442896851a825a14660968516825a144e0968510825a14690968519425aaa06396aa806a5aaa018969e86465a7a0d1969e80465a7a1a0969e86425a7a0d0969e80425a9a06396a681465a9a068969a87825a6a120969a81825aa6063969d86a25a761a096a5818e5a9605196a581c25a96068a42ac0a290ab018a426c146909b068a426c182909b058a42a306290a8830a42a20829098851a42a116290a8030a42a00a290781e8a41e06a290780e8a41e00a290781a0a41e03829078020a426014690681a9a41a076690681d1a41a07a290681a8a41a078290681d8a41a066290681d0a42980a29096062a425814690661d9a41984669066059a419878290661d8a41981629066190942ac0a250ab0189426c146509b058942a30a250a8c20942a30625098c58942a20c25098851942621825098418941d178650745999411178650781e9941e07865078199941e064650781e8941e06a250781a0941e07625078198941e06425098051942601c25098068941a07a25068128941a01a250681a8941a07825068120941a0182507611a941d87865076199941d878250761a0941d866250761d0942581465096068a22a30c288a8c18a22631468898c60a226316288a6420a229916288a6028a21d878288761a0a21d83828876020a225814688661a1a219874688661e0a219868288661d0a219864248a8c30922a308248a8c18922631464898c589225914648964609225906248445d992111666481469a9205196a48146909205194248a6063921d878648761a1921d864648761e0921d868248761d0921d8642484611a9211816a48461e192118486484606192058a8e481626392058a66481625992058a46481625192058a62481625892058a2248162489225818e48960699225814648960689219878248661209219818248661a0
  | 7, 0 => 0xffe9affe5affe90ffe50ffe88ffe48ffd44ffd41a6940a68809694096880a4140a40809414094080a2140a20809214092080512ac5126c512a2512625129a5125a512a1512615129151251512a0511e051260511a051290511d05125051190506a3506635069a5065a5069950659506915065150698505d8506585059850690505d05065050590
  | 7, 1 => 0xffe9affe5affe90ffe50ffe88ffe48a6aa9a6aa8a69e8a6a68a69a8a68e8a6828a6a98a6a58a699896aa996a69969a996a91969119685196aa8969e896a68969a896a98969d896a58a42aca426ca42a3a42a2a4262a429aa41daa42a1a42a0a41e0a4260a41a0a4298a4258a4198942ac9426c942a394263942a2942629429a9425a942a19426194291941d194111942a0941e094260941a094298941d894258a22a3a2263a2299a2259a2298a21d8a2258a2198922a392263922999225992291921119205192298921d892118920589225892198
  | 8, 0 => 166209
  | 8, 1 => 0xa6a5aa4250a2248
  | _, _ => 0

def repWidth : Nat → Nat → Nat
  | 5, 0 => 40
  | 5, 1 => 40
  | 6, 0 => 30
  | 6, 1 => 30
  | 7, 0 => 20
  | 7, 1 => 20
  | 8, 0 => 9
  | 8, 1 => 10
  | _, _ => 0

def repCount : Nat → Nat → Nat
  | 5, 0 => 1189
  | 5, 1 => 127
  | 6, 0 => 717
  | 6, 1 => 211
  | 7, 0 => 54
  | 7, 1 => 85
  | 8, 0 => 2
  | 8, 1 => 6
  | _, _ => 0

def hitSlots : Nat → Nat → Nat
  | 5, 0 => 0xe861990de1946309891b8800089d6485c95b80002d4715dc0000000000062048208000866200023a88c010000c804000000023227bcc00046d1092e8c88000416100005948000000032e2d75e0a99b3167c238054a8ae4185a28a88000346192824e4400000008ee31bc4d78800000000001fa880007dc20055081c1127b82a745a9abf771f2200005e28000858212c51208a2136470705b3397f480c28fc4ac0800000000002170aa62000000000209ae33e4489c95b8bb120ce21221478823728022b8400000cb5aa200000000000017200000003fe214226a495309f0348622a1d9188f27000000008e080000000000000049910000c85dff080000000a8ce4b8c88346c48f95960b8f74b0218862f9a28142e47ec566087775b6672053b88c17836a5d05b5180011a226d04990bd671b429844151819119e2ec05f920a512b666c500003f010000778c00037b225823ac64d880003dc20000d3243b75c62d4ecaa0815714242745269bd2140c228c421b938123687a04210c5d1000106100000d911886f3c4af9c17179c2bd2d08104b58f0f128529982f14ce30d44b9b8d417942c146039887262231244031115178021a44061800000000001300a7b1794496445e095b1476200000000fd100011c54000000000001e0800000004942080632080000000000000047b153430014361800069eafec895380001ba271456b0ad114fa47a4c8b889115cc202d54e084712562d29dfd888219222fe094138c915d230986008800085641e55548800083245884f13979121224cc603a8dc10f42e50c6f891a113631585000acd18902d6042009f5334621504c98c3528da623dc9d147110fa8289df53c29277ee000000000110000689d9a8800533849c4dbe080009446000014993e13c62140446880000000b2c400031d14c6200016b8aab14702808450b883900002e84ed0c2518e36af85ed8aa414522574e071853179481bd5770a2a130e64390440b4fb92028248000338100011a5d37940f762c2bf2e2958da390822e0518095130000d90431891675f624f045b080000000bdc6360c5216ba2e6052a0a88212e6bd84138af5115e200000003f91000082d40001f212c240001b38adb152c204846b3944782648a0a08105920000050cb9097c329c200006ca22d181a4a605b888a3742ea2044cc8b031084e520e358c9337082008576880002e4400020a89d7102cabc8c00045673a623204430a145250e198c5b88eaa1142d98586880000000000000000000000e94400029b16f426f45d108ee705072684cea00008c025f88e30a1f181a6588dec8b9518fe276c584084d741ce0b84c3080000000b64400016a11e22c904538c9e18a6ad5854288ab1046258c4ac994624bc21904b5100008fc2b4c5c53b4a90000e3c58d0a7a106c30d056f3be415ed68548053b2323e8466d09f8a03183468cc400000006fa212ac00000004184fa862308fc1184ee24438880002094e744f810e41414b138614119e42e090354000214102220000000496158449f0815080d184c6ba8519080000000000181121e5000010ce30916a46e42000000045456b82d884ad080009444d6c88020d73408284c5823a1d131a3229c000000029c80002421921a27462b440003ae12fa24120d0102c15582000134080000000e5c4000472b2b2320c513089850c240001ab8c54b000000020098e915e5309080002ad143820000000284290a495c4d1a3c270000fc8800048917d828604159baa14de2cdc4b918000019297c400000008fcf1249a6a9bc10000e9c5580a1323da405c4fb90d815ba23d9c370869384ae8c0926180003be2b0090f087e75422f5dd0b8a7810000000000000000000074400041311f0e74861c8bb913762fe1077891817d62759c7808352000000009a095d14384e54d790a1110000a1dd7939fc10a4ec5c415aaaa18d8ecfc5370b8016be321c5ea8c68176e8bc1ca3206551a020e06178a1150432840400020e54e421b44000000061a701e000000007bc200023a28933796209cc00013f2440200000003f610000cb440000000000123862d8c03100007fc4000000000000001f30aa0100000000e208000000118c59709ce10000a4dc000000000000000000000000007a0c7f0c2410000000000004e10746688900880008342dc8ce60c0657d2f1d0509992a159c27d060b290f13cc4911c5e881515502db44e00a2711e62d2c5129369404c285cd0d88bf101226b047521eb5132af1dc00000005322000000000000000000122880008322295e4dbb32730221b0400043f11f2e000121ac7f7436a924421caac3588214447139e980ea2059c97ba6218e9600014db9f821e8e084e4589fe125a27905820c14313c2ebcc2f48000000000017c084915843085cee0c22100005fc8000000074c270440001f917b08c9c6188c863944227dc63099b33d4a495c00000000000491081a2b2120a28989d088ec101823085ad99ef17ce2031e229953107620000f10c6710000e5943d1000000009b45da8b13100000000000000000009a8549880e200007c04000452500000000f12ae11814a1204cf9afc578c20000ae0c8426f0239c63e094040b22000000036146162000236b80000000a2c40000000476a000000000008a22000000000004166b504771aa515d82f4051789e0181112094e192891000000023c0949155e310c426092713066fd1d62138612502f49cd40be1124a624885f3800081849f4400000006762d385e689a740000180400000001d02000000000000000000201087b157620000359b52b340892c4e5880002bead5049c12e711d4e5a453739be100000001358c82125c2c006040b0f147c206c5440bb030c6666840001231000015859a0800000010285f10a1511a86a4855c080000000d0c40000331632226d5a90af49562207049b88000000000000000000000100dde2884e21b6283c4278922300000000c7885b13d506584c58b3218ec30e048888000138e914898bbe0186e282c8110bb41108284863929204726eb00445894866004828e13880005e023144000000000000001a92c4c331c2354c0001a917e6ef245601a09544a29484a90a4033508fbc5a2887970eaed684af091016f620f05ed0b701816523c54109643206314ecf5098e300000001f9092114883244db98800088e320dd4f9079177032704823800000007b040000bc3296e5444e48800000000001b1135a76442c045230c8268db2e8c63dbb8a129e224953491e4709240001d00ad210000d044948bb213ee3058c50090f381e21354f2890710ee51045c3b800000c293c400045015ed290860f0ab312254a5c521197113da2489c840b60128a86e06400ca1165e2fb455a8a07528425044a511cf17a22185c2c289d32804ee0c22889f21d68da4499bc1f1000000012e0ae510000740505109f192a2a90cb38aeb129020000000000000005dc400019016d627948d08c05200010405700906192429405bf8b121342400000003ab130a42a45b288e741beec305b70a9a235a6b045df0a1131a465c90c48878729c653c8000156107e2000000044c9028f01c800044fb2f66f4dd170c087484a62cd070bb71200215c62f8b8c100000001eea00030000000000000000000c944aa8800000005d840001ab1020ee49e1d886a1144676446a8b71280c6e20608896543388b704870c9e750e291c5ba88c5726a2e75de4090c15f370344baaba817b042f84d90907223a20000000000033ce000000019212364000000012e748666b8400001630001131e4a91b51898305cdc289963000000000001f43942e000243b0000000000000000000448e0000fc0c1d12de260c4000000000009b0603bb40162a286cc512a07768a65214f539e923686bbc5998c2c203c2afc48a184a178a6650c1b880006122fd058e080008cc2b684530c2a16b2232c47308d3320e800021f0bc411e2ef9440000000474200000000e310000a0c5aa880003046108c00025d13d46000000000000000000000032918104000000024d14182a9c6460c9844f223b91d71a46237843dc58d8c01503ee00000000000594200000004085000115481a1328112628ecde1080007322311dc98901151c43f9c00984983c465b5da88a5e726480144da1462154630a44cc098048122a445a9880000000000053380000000000009bbc711242109606090d42a0228c826885813d2e094482b920764c213c800000008a8200016f8a2c19104a0c8810a7c106a2dd04000000060e21d841d280006d0e0f840003b7200000000000000002c31705a80b21124c296c5430b8874f6469853b0afd174831e44f5145712a66eb056f9c9f10c22ec45af0b8710a2e0000000000000000000000000039c40001ff882753c22b2440000000000000011e9adf500000000000000021280844000000005231084f988000000000020a1404293ee000000018543d620000000000000000000000000000000001a68c18210ee1f1cf4ab63181c282c5c8a80002c08500c4a8ca418b0260848f8c7d182aa000000000000000cac55e0c8730000079c3c9800000008615bb080000000000000039e7372302c53a0b8c72f82454d1eabbb11e420405c58b1d21ae267440000000000092040001aa163c6be54d0a00001e0e44c400000002ead280622889915a02000000001417e6308c5a488a47916f1cc41c89a5121ce1c14a3b800030020000f3080313ce200000003b612d82000000000003ea4568e430925211e2198418080001862000000000002ec6000225bb1e289628344cf092142be279d5b490b2185030f45d48c20143240000299390105021f48000000001021744d00b82189d219442410000054a864509a80000ca68354000314150021e05c18800000007fd400000006fc282848b200004de64b5d6438000000065049c189411fe89e95de0c53123ef161c20889551d26670400000001a080000d1228d700000000000207100000000db8a543000113c4cd89d115d021b1444880007e220001e610000000127454f09de10000d848c0919232b0600000000652000000022d0ac3172c24d0da60c071462210c4000000043a60002440c9421dc2480400014f418820002468ca0743423f1c000000012c200000001ef212a6634d04085380f64f604db0910385ee1104e388f6100000001420968461870c845511d61434a6d501c397f11302c7c5062957172826905071b4a10000000000038b775a20000000073737e20000de1c1818f8ed1c400018140ee20002523c0034f464945cf097310562875607abc3117c4ab854f110441fae5984fe8960179e6240c43c06f18266d08440093615f82161de71c2b170225c05b40a4c10cca0000f48a3774ccf2605118a1610ef0df1029bb3011c4200016c08000000077dcfe1b1811d44e385c8980000000000061b8000442233843f29441444200020d8b6439046c0c8a51a66100010d8853b87f133a513e4c88bf8125e20b5c000000029ac00000001a71468e67d0f7ac7d73a0e0000000101411821d0cd4a000000002d46041be813aa2000204aa35139a253550a1821724824e485c881f139c61f44bf0bd61062ee7048f086e530827f15fe10551420a7284290a18332e88e453a89b727f8319440d0a05141220001df898510000ddc4ba8800012468f440a98af27ba4af49b8a07e13ec31bee2c89d021e822b05510be31276294d5fd100c51202af44168a3c17fa45284aa982f236222c04418c81152827c146388e724d844d1000045b2000000012a880b192630485b8380f18e0b049c6cb9c310b060001a6d90b17a82fe855d0b91158e2628c000000015420000000000000001c8400003a765423b44479000059e2b88406901555f42cc447a8800043c70504ca894b102627a148b0a8e12c28620c3418fb135667b8a491a8a13484000000043c13f643b0d7a09ff3174e2704f1bac817a620001798800064440000000000000000904000032164e4d28d9c888517ba22f8c8688cc12f625ac4b4905f16b691c846d9a7158684ce84d8094d147ea499de518000360625c4340800090a23285cd8a5612282028403893d100000001871000000007cdd62887010f100000c3887270000ad062498ec78aa27e88bf23bd190ea67c532896814fe312086b080003f429904988874100009684d19a70100ae590475080000000000237ac00100010c056f0c1b3786e5844fa8bc1169e2bf8400040277dae000054080000000000000000006882f19d788af79000000018f0954383288f0d8508fa13d8b17849a948624a8a8ac96309ba153e2824d288a9920000514400022b110e28d49ef8be918b4e3892284c6a189a27745298be832bc679ce3d098024da42149a729a54090e624c05da89286c251c5480c0023a820d9c520b3614d44000000000000000000085085f700004f590698000052a0000000000000003768a3080000000c084588b5b16de28f14890a3410000000019bb1b338432609c90922106829f85870b8d181ca5e5e1d0aff17ee2d20407098f37ae20002151000000008d84059bdb20bc2fb9c708ac328c226b459e8902390e44c04000000012863484000000000001650c6082e250a481cc000000000009cc40000bc74822ab9c0002691126a00000000b41000000009d08b31016e000000048530000000000027117982bf94f88814576621704a6098a113423e055c888e107a2900611916d18e02a34435890625f22a304668818141e430449a12b6143465290000000050c4000000040f34186000000033c100000001be1404173e2f25e220848991421685cd08311712eda84b709d816d82a0442308285538505d57f59651894641ccfc904d33e2450c48d8c6e100e4700c92a0ee22f42ff4514b87c16f2239458309a218d2200003c48000880200000003db445ee1f8d2013ba10000c40400000000000aecd270873155843fc60d2b61175e25e040000d31000000005d880008422000000007150001014401b8000
  | 5, 1 => 0x1c4460ec6ce82c400331de2003d89e1062148002d140204610ac1225944a0800000d44001020016140000000118600ae200000331f2100000098821d08003588008f6000004111a29075a80054b446c08007c2002abcc1d281c5a0ca17e2b5f18977123b1670b11a0470411e61c6e2d640955602f44002d3c0ef0530841bc2000004f20005c400000d46000005d1000f8943867763345d0800000000698a1542000006c40011c5e91d1fa2108d1ea6d0230d28d911c2dc570800b62000007c1d4214400000e0221f59fb3be2d8558aa3ae3244a8943264088a17a10659cdc8b213439dbc8800f03d8440f416a5b4400ef752354400271a42644888008a3706d0800ce440400541807885c0c057c779f32f51c4fd5c007275e200320a11000000d8e71865a44a9800d87f840058bc02a040000046200000000001404510d592b584001f1d85a0872a21788002188c5166000b0ca20013c623c41000f0bb8800dc3cc4e16c1c220008bf479621869880028a4863a8f1d0d2dcc0800
  | 6, 0 => 0xed10001ae100009c30001fa16c6d881a7464b100000000000a51350558180c40002706b199384000468c8911805bf16c2c3d10000000000000000029b13b845610c8a8978e057510c497f1000000095446f19d4df4140467279e45f550604161a38de81ac5c00061d5b85161c5c348dc0006904000000000000002310000000068c0001d04000000000000000000002ac1050cbb14e88a81000000097c5f330fce8d565cc04182c6721248877552cab016ace4930e493c300000000001dd100019150001677000000000002015144000000000093047050c04000000000023040000000f114dc40b19d65b320002b6172c94c13ecd0e1a26e9075204e5104c5c81a80482217d4f52075d0b321c4d31a4540004e8e88ba0441f19f84d6168c4df19984501558e12298c62379c89c111ecac374951f399404b316c0c961389d6e152c5d513e1e00247cd983324d2b12f44a9163166a12f9c00001dc000acc8000000071100000007ec4000afc614149447e5636c0008c5d5e417068450912a4b65140f59bcc4c19b4400000000003d90783a34d8cb45c881702d584320ddc616e85ab51b944012d8546281485324306a421754af3a1040a5474ead255cd2b3400d7919e84de735c5d32a2c86352e9d29166859e1a8c8e9338446a16c26c248388e3149056030000911b084043008d3e2adc53b42d440004f459113f1c5c265549517c0c0000000000b15c7f38f4645159482bb1385933a645d911894fb78e84e6189058b15c451112804812a20de310a865633686b293245f654f4ebb1180d9b1ac880005212a13284455212881556044011374d16100006f3a19cba300012e49d8c0008444000000054118569014504000000000010c50510002c4136460e100000006d4d2e10d5e7c186c46c100000000000000a30c00013469e30001434931c0007dc5341b00e6112a86b7774052c73d050017e053b105c5861a2254a450921518b44e910ecc00043dc03500c5b05a4d06f74c100000000000064e0697f85cc206843938f84de38e88ef1210435110093910001524aac49b100000000000703000000070840005b040002c0c00000000009bd68c1000130300000005a48000000281300004350001ae590851874786a4977044031c9d48735915e163240000f168f19fcc58100006555284fd340d2b914c853f27ac64b794859750a4400024040003ac40a30001a2100000000002752000000083440000000000a8c40006ac51e3298400045440e71cc53347c16ab20ec40001c1c00000000000001af1a10e1e35a060629d5c5e32fc400000000006d54ac136de88551846d590042345d065716389f4b405c055000032100000004846c31ad2ea5583c5bd155495210384795441c7011c5cd544a840c246c56210cca2f16244e211809e2189c5d027444381a84acc1291d58432040000002a5b0002247088d21317c8c710000000000000098840000000000a79400057cdb75000000005054110000000a88c3d5af8d1918a468e109d56025e1cf6159883610215c9270051f129055a10885473af86805a5440f145d00000000000a5c400000000000486a81a74800000000000000d13361c0000c449d7a1c42652d1d1814e5044100000008884e8100000002e4e482a485a61321d9250cc40000000a771a4a5b1634c4215a440000000fb100020010001d3100000000000000000000000010911ec40008d449d10000093550c00048cc000000000000024f1a7853f148068d12f0e257194e9110e8e7517c9ca7188149f11e84452a649961884427300014027384000000292400000000000b017788811000000042c47c18dc4481184400075c4ab14d50bc16c880005f041914084000000000000000000001b51ac9d4715ac4f2124481054cc5f61978400073443470000241000000039c691940cdfe200000007d2400000000009c49853380c9b7051400012c40009cc95518c04ef7ad9e1f34d5c0003f0e4d10fd582785c54148d5d2526a063a36b4c605000225100000008ac4d437604781a865b831fc4c0123c429538045f112cc00000000000000000844a972a054531580588364846b7209c8b1201d3110909b015386a6559865d757c8000810a762014c773631d8d5ad6d1c183493740000000299e1e19446a6b6b0e1a100013c24f84dd7a28a4110000c3300000a102555b16c4c57700009218b4d594a684ff350841f3a78ac11a7c4be10406361669c00000000007805ca200000000001941b246ac75e058657c85ee1abc4000000000079040009c0cd2300001d16d1c00000022d220047873ddc5519d103914c4cfc187a4000ac49534a4c61211245f915004b772bc587162850f13a9cca7408cd335dc4d3731861c12b8c6450ac68f5a00d48218498e11b846610f8e2e32e8400001c559755086b176c67f175062154a05f370a0c0000000000000288100000008a0602100000000001e22000101310440000001494745c0002b840000000000756549195dd8d11fd68932d4d96346cc0000002c714b5d4a263927316115047514cff14d9d0a1ac4e393654d4320245ac5499e771a4c93028a85831ab86ad15cc47658e45da10f869c13785e513d5104119ca3416305ad11f1dea131064d7a085ed1490db636c545f36c1c5e101840674589a9157c405151102719d84081040dfc1491c0f32b5e30726048d1000155353464710000000000000073cd4c4ab090324d44d9341c52539c143b519448a1691c1e75b4510178498f4a396681b2c51176e44747465ea2907d62c1644c4154bc49a17fca037519226787c4f710894682035283500006f5000188500000006dcc00000000001c85cb19286a6192102159da400000000003d8800069465315d8563167c60c185845d31e15f177c44405a0c40008088ad30f0c8516c85f314b052611d8c7e716cc0006084ec1ae0497139dcdc73f849415904251b08852192066b1a25688700000000001d6100015412e1c0006104000ad147d70000000a146917a85c2636dc58636c44ad113c46226746c617d44623774a96174843a10d04025898655396441e19906bc16c913c400009979744b21000000000017a377c446257058011588ca12e04153195ea079c06ae25e846e3000000063c400069c403359c461300000004e91ac12dc400000024311b4d6e2398c99181047516c64d7715c6aa112c8b977b0593107154b4000000000024630002c519bc697751040000002b8700028a10e88c2716ca461000000000011c36d84f931f8de116cd09e15c88cc1a46d3244b121d18046b238f046e70695c911144dc14e04ea123867814e8690b2c4607145c400000000000001514381e823118689136c60235945fd10fc4d212d0672400017b1000000000000000000000ac468a40001ef100000009104c110001bb18ec61e746866516e065412884ce14e9c3711e9d203084cdf77c052310000bb7ae840c100019c14e4d893070c15100000000000000000000040c4000a8453076804000000000016468999b844251dc40001795cc13604000ad05c318204e973d4400022069821f84f0782440002c50c97af444a124c462125dcc21a0cc00000000003e468b40000000000000071044eb03100004591d424f90f0108ca8015588000b08e2f34c053c1a945b31190400000000001e4eb31544620b540400000018d94c500008c86101269cd110b0655214469033e06a7100016f27d6c0000000000ad4428150107376b540b373c4bb3a89eb553f440005c0400000018d76f84cd1b206a415648000a1848a20000000000000000000000000000000233112d59510000000000000000017170000000000222300017219fd4000000112100000000000257098400092457e1409c0000002a9132c67421f4673455ca94100067173cc45428145ae300029090fc8c315744b9184de20139cd7d19ec4df3961d8550f8a5e71a440009d9c000000020372840008b84d01a2c49d37a4400000021f90f4943110dd5823e8d1d11d9daa765c64a79c453449b040007fc56a16404791479d90706d4000000000000000005248bf400029810000892000067187dc021a3151d779c4000000000000000007c8c111a4880000000000ac840001d853f400000000000dd16f0419500000000b840000001a119c50d5160dc3e5b285923a884e34a4167d138dc1b171c4fe35584c510a15b4103443c12fde5c16614433289d8959805f292cde1917589cf2514913188c4ca3385ec016c5c82166069a23b9cbd78d1c3d3174483199c4b635bc5fd296052218c468f316c54c24d85aa142046d71a04cf1650c1b38604302a094e4177858f2886d4f13e842930000b245644000aa8aa2275481c11ddc47161cd8518284bc70349f6b6d96cc395842d154c527128c486101159917986c47488c7c24f9c21116863f108146d10002c131edd8c33a8e913295e131271c2f171450619d0557118c6061368d0d14e100009a44000308c00000000004b465a164d5965518d2f45844083
  | 6, 1 => 0x951a733930000000001322057418c1892000122153000a8369b0e5002000000143000915155000ca1767000b110009a74b10008b100000090b4c75d365b861a820000e70000000007a17115c11d11b7142000000c611410210000000000000002211e50000000000005211e31910006310000007315b10001f1000000000a918c70000000000000007e21677b1a471879d70655930b14358a73725a10005e70007c10001d30750004214026793c73d17f13013b15810002811610f70000007477d1183000a860e2cd14428917724338e1c51b51774ac1552c912351c1b61063061a921778e5a812f2841c53481073911b52a415452112030e89056c1cf193b8f50f22a1000641291000d014d16374c116381124591bc37554261251000bd1b31000165a13831472ad1452d11c27042bc14619b14010127071c30007810000000004a1791671ba1b212d38014f10006a10a1000727a01b33000c97a53c173e1851271000af16b1d133913a1000000000000000032097a335719c1b235e19413210000006b5b41000ce1000a513c15c23820d16690000000001819e1a630008a10000000003810f1145a71b438d15417851c28812430419c71010110e3867935a612121921711d2087a93214c810000002b7000000b620000008710009e7222000371cb15910c18eb0d38f13426d12e72d11f30f8a11c313025110d5051621783501000b813417c36f14511116e1a31001071317000031000000821c559f12241a2961b945d26137e1362aa10e11150000009d10007170000000c3b91a23395233681000be16d366b0006613523223f10c50006d55316f2ab1b923610000000002010008c3000351062000602a85c11000000000a26c416399917520914679218b32f1931d236e5c71a25491c212e12416e35512d7751a52be7627981c676a5537bb10812c14317010a2c72a15000ab7c01ae16aba720005430000000000003230001052b1721d21c73607cc78c9bf1b01ac75d10f31b12556111a1a359014118976011510f59b7331761633a622319a19715f19775f25610224e1441000cc16911f50b21e1000000000000000000a21000695651000b710004713110000000002531316bb659771121
  | 7, 0 => 0xb1cc5e9104610000000351a04b56c6616cc0049de36906368cc3944535c40000000bc587b867161153389a239d01001914c4e108400002d1788a77ddc2005b421d9730400002312cc00285f22dc4300051585b2a84003dd07001173c5d4711a150c0048594a4465805731cd631540074800000977072134de124481001f9001e70c400905f13447128ec1ac541046113c9513d00000137000000000039341000002944500000c0581315f3884d5c45d1444000007500000
  | 7, 1 => 0x1b2136001f8800a02002a0b32236ac412aa11420863b8008ce00268c514f62c802a69263105f0a050231093abd1086266221251a65080aae14e2688c149124278460b7b68ee45a0ad24420d440cb11c6645b2b4912aec400831246465d0a321aa1c5308910009880000047300581023684f0429af114accca0b110823088a9611e60022ba85288b08000000000000004522240c68d110000018080030e45dcbc11147204004436eab040028b00094918ce18e20ccc0b716c268428a3774e80800242000648000000000019b8e5000310002330eed0c82a2749225c2a8f50000005a151842c8568a510c200100800406001a88ab14eb9e11b520000004980098338d710a91c2000b89f22694c520c61026000002810000000000048e00201d21866e1c9393267244c80ca142290c959293633c5488000003c4002f2702000000033e2cc400000000000e0800862001358b1000745b5800
  | 8, 0 => 1048593
  | 8, 1 => 0x5142440806202080
  | _, _ => 0

def hitWidth : Nat → Nat → Nat
  | 5, 0 => 15
  | 5, 1 => 11
  | 6, 0 => 14
  | 6, 1 => 12
  | 7, 0 => 10
  | 7, 1 => 11
  | 8, 0 => 5
  | 8, 1 => 7
  | _, _ => 0

def hitCount : Nat → Nat → Nat
  | 5, 0 => 2683
  | 5, 1 => 275
  | 6, 0 => 1853
  | 6, 1 => 539
  | 7, 0 => 147
  | 7, 1 => 251
  | 8, 0 => 5
  | 8, 1 => 9
  | _, _ => 0

def jumpSlots : Nat → Nat → Nat
  | 5, 0 => 0x100461000006040100886000620002000000000000000100000184000086000840194000204000040000c000021000a3000c719c610000000000000030048000020180000286101000011000c80000057119c000004480021016100061148400000200000180015005700000000000c0400000b01840008005000004c020800000026004450000045400008020000a0000000840014000040000000000030000020000001000000018001000020080338c01000010140000000001400004020005100010002000001014001980000066088030004000040000000200000001000000000000000300000000000060000001010000003300015180011d2000000000000804304ca5200010000102040008621818000042004c01002000000030060140000400000000000020002000004840000002000221a000280000000500000100001080500040000010200308c000000008d84000000100000000000870000001005100400006100000014a4000000007c080000001378084090200000009000000000080244960000800040018400608000000028020584230804000c0000006000010100400020004200800300c00c80200006000000500000002020000000800002100000224020000020003000000080801403000000004300400000000040010000008000004000800400000840000442000a0108270000000000004000804700800200000004008001000001846100000000000004000003180600000028c00004210002000004004400080218000080220012480000080001802010021000200000000000000022000002800080000002008144000000880000000200010000200001000c000c00184000004000001000c310040014a10000100c020858d28000002200800500001008000802000002200201800118f80000010800008000000e00102000426000211000108000000200800000c06030a0588070884708001000811000008040000800042200025080020002d000000000000001010002800600002300000000000000000c00002400003010000000002c21000053040000800100200004c000001000100820000a00804000000000000804100c000000000020000e0180000000200400000000240000000004000000002809000000800000021000000000000018110e020061080000000000080024a00002000042c88000000000000020000000100006381e51000010c00000000004000404100205842000000000a10100000400000000000108c0008003000024002801400000020000001000000001802002c010404100408000010000018040500027000100000000001800010001004480b420001c0010000008000400048001080210d4300000080460000118462011e30082000000000230180000c2002c002802019000280000000008022004410000000020000e1000ca0804200005004100040900c0208000080002002000002018c000002490000040000c0028003000010000000000000000800008021000000800000460080400002028040101621848200820004e10006300000001e400000580c150000080001a0400004000000010000000b010a30000200000000000002038440008000080000000004320000000c0000000884010804a08002000000000000042000050000000009000000000500000380200000110800000000146300001004000002000c0a5008118041200400000110046080050000228040200000040000420000801814011c000806000801208c1000000006000000
  | 5, 1 => 0x800044000b46020000000000000b0500000000008800800000000008000000010020000a000800088031000100000000a0000000288000020000010040000000001801000308401104010006100c02080c00800010400200611800100000000200880100060014010002100000044010802000c0000804288001000000020
  | 6, 0 => 0x100000108a08000008b1400010000400401c00020000086010400c001d00000000000400000014000000000000404002600f0040430020000010000000810000450010030010020030000402c30400040400000000030000001000000800cd0040000030001410000000002000000000c00000010000070000000400001801c10000000001c004008000000100901d00000034900000104000900008100600004600000e0000000000000000000010400040000010000000c100018200008f0001000010c92800000000000000000c83000400001000800c00c200028000420000408104310100000000a0c00401403804c12820000002800c00400000010010000000000400001c0000000000280dc00000000000020000000000000490020001030400000400071c000000000000004500000d04000000118000000000020208300004000100800100300a00000000400000000000300014010700a00110a0812870000000020000050400000000430060000800010408c00000000000400010401000010002400000004009e40012801800000010020810000450011800000001410000010010010000001c400f000a820000000060c000000000200000018008d0000010423c00000401c00000010000000400000000002010010400000000000801000000000010000000000000800090000010406c00400000000000410000c000000028400010202a0000820000010800010000000000000030002411001001000400000000800010030010000020000000400080810000410c01000c00000801430410000000400010000400030420000000000000000010002801000440010002400000000040000c18c904000004004200208c0010850010400041010000002b10c80400000030000001000400000010c100010c00000008105c08000004004000000018200204300500c0800001022400800001010000001800070010870050070040022c300300008008600300000208000004010200b000040005000002a402850410000400004400010000000400041400000001c30c118100000000000001314100c00004001d0000440000000000000000020000020000431c00000000000000001000000000060040801c200000000800000000430000100000a0000000c00001000410000000000001c01c00400020000000000400000000120051060000000c004200008200100000104001c0000000000425c70420010400000000410400000101000010022011800800020410400800000400001c00011000000000400000430400011430000000000000000020000000080811400450087c30010000000c00c10000000030400000000000000060000000000400000440000020001000000001000000000002c80000000800001c11430010090041400000802000000400000cf0010007800000000000004c00000400800060000400814c11c20800c0000000
  | 6, 1 => 0x1000020800310c0000440000400003000006080001080088040080010802080060000800040000001004000086100000000010808000c0101400080200000008000000000840300220024000102010000000c0080600000000c0000020080ca0002408043000410002100000002a0220000000006800000000002018c20104e3098000800200c0000817003a00a8030002000000000040800000c01c80410006d0b00201003000001800000005010a00014000000018020002000023284080040000063380020040300060000000000008400180000000ba000100420000000000000020100200000008cc0010000000300080100201000030000200001004000000
  | 7, 0 => 0x40000000001200300212100510002002650000800001000002200200000001100210033003020300000010000350100500405001200712
  | 7, 1 => 0x4218004101a0000000070000000400100000000800050020000000018c60000000400000020000021800000000000000003000401406000040440091400000001800000000212c40010000000000002001400032400000000c001e180000004503000000000002240040000001003000017000100000042000000001001010200100000b0290020008200008d000001
  | 8, 0 => 0
  | 8, 1 => 70
  | _, _ => 0

def jumpWidth : Nat → Nat → Nat
  | 5, 0 => 5
  | 5, 1 => 5
  | 6, 0 => 6
  | 6, 1 => 5
  | 7, 0 => 4
  | 7, 1 => 6
  | 8, 0 => 1
  | 8, 1 => 2
  | _, _ => 0

def jumpCount : Nat → Nat → Nat
  | 5, 0 => 2062
  | 5, 1 => 208
  | 6, 0 => 1423
  | 6, 1 => 413
  | 7, 0 => 110
  | 7, 1 => 192
  | 8, 0 => 2
  | 8, 1 => 6
  | _, _ => 0

def repCode (k t i : Nat) : Nat := takeField (repPaths k t) (repWidth k t) i

def orbitHit (k t : Nat) (w : List Sig) : Bool :=
  let h := stateHash w
  let b := h % jumpCount k t
  let idx := (h / jumpCount k t + takeField (jumpSlots k t) (jumpWidth k t) b) % hitCount k t
  let val := takeField (hitSlots k t) (hitWidth k t) idx
  let rid := (val-1)/16
  let g := (val-1)%16
  val != 0 && decide (rid < repCount k t) &&
    w.isPerm (runPath (orbitInput g) (9-k) (repCode k t rid))

def orbitEntry (k t i : Nat) : Bool :=
  let v := runPath hardFixedInputs (9-k) (repCode k t i)
  if k ≤ 5 then !search k t v
  else !oneRound (k-1) t v (fun t' w => !orbitHit (k-1) t' w)

lemma orbitHit_sound (k t : Nat) (hneg : ∀ i < repCount k t,
    search k t (runPath hardFixedInputs (9-k) (repCode k t i)) = false) {w : List Sig}
    (ok : orbitHit k t w = true) : search k t w = false := by
  let h := stateHash w
  let bucket := h % jumpCount k t
  let idx := (h / jumpCount k t + takeField (jumpSlots k t) (jumpWidth k t) bucket) % hitCount k t
  let val := takeField (hitSlots k t) (hitWidth k t) idx
  let rid := (val-1)/16
  let g := (val-1)%16
  change (val != 0 && decide (rid < repCount k t) && w.isPerm (runPath (orbitInput g) (9-k) (repCode k t rid))) = true at ok
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at ok
  rw [search_perm k t ok.2, runPath_orbit_search]
  exact hneg rid ok.1.2

lemma orbitTable_sound (hcheck : ∀ k t i, i < repCount k t → orbitEntry k t i = true)
    (k t i : Nat) (hi : i < repCount k t) :
    search k t (runPath hardFixedInputs (9-k) (repCode k t i)) = false := by
  induction k generalizing t i with
  | zero =>
    have hc := hcheck 0 t i hi
    simpa only [orbitEntry, Nat.zero_le, ite_true, Bool.not_eq_true'] using hc
  | succ k ih =>
    have hc := hcheck (k+1) t i hi
    by_cases hsmall : k+1 ≤ 5
    · simpa only [orbitEntry, ite_eq_left hsmall, Bool.not_eq_true'] using hc
    · simp only [orbitEntry, ite_eq_right hsmall, Nat.add_sub_cancel, Bool.not_eq_true'] at hc
      apply negRound k t _ _ _ hc
      intro t' w hw
      cases hm : orbitHit k t' w with
      | false => rfl
      | true =>
        have he := orbitHit_sound k t' (fun j hj => ih t' j hj) hm
        simp [he] at hw

def spanOK (f : Nat → Bool) (a b : Nat) : Prop := ∀ i, a ≤ i → i < b → f i = true

lemma span_decide (f : Nat → Bool) (a b : Nat)
    (hc : (List.range' a (b-a)).all f = true) : spanOK f a b := by
  intro i h1 h2
  apply List.all_eq_true.mp hc i
  exact List.mem_range'_1.mpr ⟨h1, by omega⟩

lemma span_join (f : Nat → Bool) (a m b : Nat) (hl : spanOK f a m)
    (hr : spanOK f m b) : spanOK f a b := by
  intro i h1 h2
  by_cases hm : i < m
  · exact hl i h1 hm
  · exact hr i (by omega) h2

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_0 : (List.range' 0 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_24 : (List.range' 24 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_48 : (List.range' 48 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_72 : (List.range' 72 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_96 : (List.range' 96 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_120 : (List.range' 120 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_144 : (List.range' 144 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_168 : (List.range' 168 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_192 : (List.range' 192 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_216 : (List.range' 216 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_240 : (List.range' 240 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_264 : (List.range' 264 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_288 : (List.range' 288 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_312 : (List.range' 312 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_336 : (List.range' 336 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_360 : (List.range' 360 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_384 : (List.range' 384 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_408 : (List.range' 408 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_432 : (List.range' 432 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_456 : (List.range' 456 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_480 : (List.range' 480 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_504 : (List.range' 504 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_528 : (List.range' 528 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_552 : (List.range' 552 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_576 : (List.range' 576 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_600 : (List.range' 600 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_624 : (List.range' 624 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_648 : (List.range' 648 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_672 : (List.range' 672 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_696 : (List.range' 696 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_720 : (List.range' 720 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_744 : (List.range' 744 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_768 : (List.range' 768 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_792 : (List.range' 792 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_816 : (List.range' 816 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_840 : (List.range' 840 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_864 : (List.range' 864 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_888 : (List.range' 888 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_912 : (List.range' 912 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_936 : (List.range' 936 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_960 : (List.range' 960 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_984 : (List.range' 984 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_1008 : (List.range' 1008 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_1032 : (List.range' 1032 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_1056 : (List.range' 1056 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_1080 : (List.range' 1080 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_1104 : (List.range' 1104 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_1128 : (List.range' 1128 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_1152 : (List.range' 1152 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_1176 : (List.range' 1176 13).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_1_0 : (List.range' 0 24).all (orbitEntry 5 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_1_24 : (List.range' 24 24).all (orbitEntry 5 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_1_48 : (List.range' 48 24).all (orbitEntry 5 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_1_72 : (List.range' 72 24).all (orbitEntry 5 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_1_96 : (List.range' 96 24).all (orbitEntry 5 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_1_120 : (List.range' 120 7).all (orbitEntry 5 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_0 : (List.range' 0 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_24 : (List.range' 24 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_48 : (List.range' 48 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_72 : (List.range' 72 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_96 : (List.range' 96 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_120 : (List.range' 120 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_144 : (List.range' 144 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_168 : (List.range' 168 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_192 : (List.range' 192 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_216 : (List.range' 216 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_240 : (List.range' 240 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_264 : (List.range' 264 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_288 : (List.range' 288 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_312 : (List.range' 312 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_336 : (List.range' 336 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_360 : (List.range' 360 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_384 : (List.range' 384 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_408 : (List.range' 408 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_432 : (List.range' 432 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_456 : (List.range' 456 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_480 : (List.range' 480 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_504 : (List.range' 504 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_528 : (List.range' 528 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_552 : (List.range' 552 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_576 : (List.range' 576 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_600 : (List.range' 600 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_624 : (List.range' 624 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_648 : (List.range' 648 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_672 : (List.range' 672 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_696 : (List.range' 696 21).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_1_0 : (List.range' 0 24).all (orbitEntry 6 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_1_24 : (List.range' 24 24).all (orbitEntry 6 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_1_48 : (List.range' 48 24).all (orbitEntry 6 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_1_72 : (List.range' 72 24).all (orbitEntry 6 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_1_96 : (List.range' 96 24).all (orbitEntry 6 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_1_120 : (List.range' 120 24).all (orbitEntry 6 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_1_144 : (List.range' 144 24).all (orbitEntry 6 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_1_168 : (List.range' 168 24).all (orbitEntry 6 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_1_192 : (List.range' 192 19).all (orbitEntry 6 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_7_0_0 : (List.range' 0 24).all (orbitEntry 7 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_7_0_24 : (List.range' 24 24).all (orbitEntry 7 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_7_0_48 : (List.range' 48 6).all (orbitEntry 7 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_7_1_0 : (List.range' 0 24).all (orbitEntry 7 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_7_1_24 : (List.range' 24 24).all (orbitEntry 7 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_7_1_48 : (List.range' 48 24).all (orbitEntry 7 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_7_1_72 : (List.range' 72 13).all (orbitEntry 7 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_8_0_0 : (List.range' 0 2).all (orbitEntry 8 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_8_1_0 : (List.range' 0 6).all (orbitEntry 8 1) = true := by decide +kernel

lemma layerOrbit_5_0 : spanOK (orbitEntry 5 0) 0 1189 :=
  (span_join _ 0 768 1189 (span_join _ 0 384 768 (span_join _ 0 192 384 (span_join _ 0 96 192 (span_join _ 0 48 96 (span_join _ 0 24 48 (span_decide _ 0 24 checkedOrbit_5_0_0) (span_decide _ 24 48 checkedOrbit_5_0_24)) (span_join _ 48 72 96 (span_decide _ 48 72 checkedOrbit_5_0_48) (span_decide _ 72 96 checkedOrbit_5_0_72))) (span_join _ 96 144 192 (span_join _ 96 120 144 (span_decide _ 96 120 checkedOrbit_5_0_96) (span_decide _ 120 144 checkedOrbit_5_0_120)) (span_join _ 144 168 192 (span_decide _ 144 168 checkedOrbit_5_0_144) (span_decide _ 168 192 checkedOrbit_5_0_168)))) (span_join _ 192 288 384 (span_join _ 192 240 288 (span_join _ 192 216 240 (span_decide _ 192 216 checkedOrbit_5_0_192) (span_decide _ 216 240 checkedOrbit_5_0_216)) (span_join _ 240 264 288 (span_decide _ 240 264 checkedOrbit_5_0_240) (span_decide _ 264 288 checkedOrbit_5_0_264))) (span_join _ 288 336 384 (span_join _ 288 312 336 (span_decide _ 288 312 checkedOrbit_5_0_288) (span_decide _ 312 336 checkedOrbit_5_0_312)) (span_join _ 336 360 384 (span_decide _ 336 360 checkedOrbit_5_0_336) (span_decide _ 360 384 checkedOrbit_5_0_360))))) (span_join _ 384 576 768 (span_join _ 384 480 576 (span_join _ 384 432 480 (span_join _ 384 408 432 (span_decide _ 384 408 checkedOrbit_5_0_384) (span_decide _ 408 432 checkedOrbit_5_0_408)) (span_join _ 432 456 480 (span_decide _ 432 456 checkedOrbit_5_0_432) (span_decide _ 456 480 checkedOrbit_5_0_456))) (span_join _ 480 528 576 (span_join _ 480 504 528 (span_decide _ 480 504 checkedOrbit_5_0_480) (span_decide _ 504 528 checkedOrbit_5_0_504)) (span_join _ 528 552 576 (span_decide _ 528 552 checkedOrbit_5_0_528) (span_decide _ 552 576 checkedOrbit_5_0_552)))) (span_join _ 576 672 768 (span_join _ 576 624 672 (span_join _ 576 600 624 (span_decide _ 576 600 checkedOrbit_5_0_576) (span_decide _ 600 624 checkedOrbit_5_0_600)) (span_join _ 624 648 672 (span_decide _ 624 648 checkedOrbit_5_0_624) (span_decide _ 648 672 checkedOrbit_5_0_648))) (span_join _ 672 720 768 (span_join _ 672 696 720 (span_decide _ 672 696 checkedOrbit_5_0_672) (span_decide _ 696 720 checkedOrbit_5_0_696)) (span_join _ 720 744 768 (span_decide _ 720 744 checkedOrbit_5_0_720) (span_decide _ 744 768 checkedOrbit_5_0_744)))))) (span_join _ 768 1152 1189 (span_join _ 768 960 1152 (span_join _ 768 864 960 (span_join _ 768 816 864 (span_join _ 768 792 816 (span_decide _ 768 792 checkedOrbit_5_0_768) (span_decide _ 792 816 checkedOrbit_5_0_792)) (span_join _ 816 840 864 (span_decide _ 816 840 checkedOrbit_5_0_816) (span_decide _ 840 864 checkedOrbit_5_0_840))) (span_join _ 864 912 960 (span_join _ 864 888 912 (span_decide _ 864 888 checkedOrbit_5_0_864) (span_decide _ 888 912 checkedOrbit_5_0_888)) (span_join _ 912 936 960 (span_decide _ 912 936 checkedOrbit_5_0_912) (span_decide _ 936 960 checkedOrbit_5_0_936)))) (span_join _ 960 1056 1152 (span_join _ 960 1008 1056 (span_join _ 960 984 1008 (span_decide _ 960 984 checkedOrbit_5_0_960) (span_decide _ 984 1008 checkedOrbit_5_0_984)) (span_join _ 1008 1032 1056 (span_decide _ 1008 1032 checkedOrbit_5_0_1008) (span_decide _ 1032 1056 checkedOrbit_5_0_1032))) (span_join _ 1056 1104 1152 (span_join _ 1056 1080 1104 (span_decide _ 1056 1080 checkedOrbit_5_0_1056) (span_decide _ 1080 1104 checkedOrbit_5_0_1080)) (span_join _ 1104 1128 1152 (span_decide _ 1104 1128 checkedOrbit_5_0_1104) (span_decide _ 1128 1152 checkedOrbit_5_0_1128))))) (span_join _ 1152 1176 1189 (span_decide _ 1152 1176 checkedOrbit_5_0_1152) (span_decide _ 1176 1189 checkedOrbit_5_0_1176))))

lemma layerOrbit_5_1 : spanOK (orbitEntry 5 1) 0 127 :=
  (span_join _ 0 96 127 (span_join _ 0 48 96 (span_join _ 0 24 48 (span_decide _ 0 24 checkedOrbit_5_1_0) (span_decide _ 24 48 checkedOrbit_5_1_24)) (span_join _ 48 72 96 (span_decide _ 48 72 checkedOrbit_5_1_48) (span_decide _ 72 96 checkedOrbit_5_1_72))) (span_join _ 96 120 127 (span_decide _ 96 120 checkedOrbit_5_1_96) (span_decide _ 120 127 checkedOrbit_5_1_120)))

lemma layerOrbit_6_0 : spanOK (orbitEntry 6 0) 0 717 :=
  (span_join _ 0 384 717 (span_join _ 0 192 384 (span_join _ 0 96 192 (span_join _ 0 48 96 (span_join _ 0 24 48 (span_decide _ 0 24 checkedOrbit_6_0_0) (span_decide _ 24 48 checkedOrbit_6_0_24)) (span_join _ 48 72 96 (span_decide _ 48 72 checkedOrbit_6_0_48) (span_decide _ 72 96 checkedOrbit_6_0_72))) (span_join _ 96 144 192 (span_join _ 96 120 144 (span_decide _ 96 120 checkedOrbit_6_0_96) (span_decide _ 120 144 checkedOrbit_6_0_120)) (span_join _ 144 168 192 (span_decide _ 144 168 checkedOrbit_6_0_144) (span_decide _ 168 192 checkedOrbit_6_0_168)))) (span_join _ 192 288 384 (span_join _ 192 240 288 (span_join _ 192 216 240 (span_decide _ 192 216 checkedOrbit_6_0_192) (span_decide _ 216 240 checkedOrbit_6_0_216)) (span_join _ 240 264 288 (span_decide _ 240 264 checkedOrbit_6_0_240) (span_decide _ 264 288 checkedOrbit_6_0_264))) (span_join _ 288 336 384 (span_join _ 288 312 336 (span_decide _ 288 312 checkedOrbit_6_0_288) (span_decide _ 312 336 checkedOrbit_6_0_312)) (span_join _ 336 360 384 (span_decide _ 336 360 checkedOrbit_6_0_336) (span_decide _ 360 384 checkedOrbit_6_0_360))))) (span_join _ 384 576 717 (span_join _ 384 480 576 (span_join _ 384 432 480 (span_join _ 384 408 432 (span_decide _ 384 408 checkedOrbit_6_0_384) (span_decide _ 408 432 checkedOrbit_6_0_408)) (span_join _ 432 456 480 (span_decide _ 432 456 checkedOrbit_6_0_432) (span_decide _ 456 480 checkedOrbit_6_0_456))) (span_join _ 480 528 576 (span_join _ 480 504 528 (span_decide _ 480 504 checkedOrbit_6_0_480) (span_decide _ 504 528 checkedOrbit_6_0_504)) (span_join _ 528 552 576 (span_decide _ 528 552 checkedOrbit_6_0_528) (span_decide _ 552 576 checkedOrbit_6_0_552)))) (span_join _ 576 672 717 (span_join _ 576 624 672 (span_join _ 576 600 624 (span_decide _ 576 600 checkedOrbit_6_0_576) (span_decide _ 600 624 checkedOrbit_6_0_600)) (span_join _ 624 648 672 (span_decide _ 624 648 checkedOrbit_6_0_624) (span_decide _ 648 672 checkedOrbit_6_0_648))) (span_join _ 672 696 717 (span_decide _ 672 696 checkedOrbit_6_0_672) (span_decide _ 696 717 checkedOrbit_6_0_696)))))

lemma layerOrbit_6_1 : spanOK (orbitEntry 6 1) 0 211 :=
  (span_join _ 0 192 211 (span_join _ 0 96 192 (span_join _ 0 48 96 (span_join _ 0 24 48 (span_decide _ 0 24 checkedOrbit_6_1_0) (span_decide _ 24 48 checkedOrbit_6_1_24)) (span_join _ 48 72 96 (span_decide _ 48 72 checkedOrbit_6_1_48) (span_decide _ 72 96 checkedOrbit_6_1_72))) (span_join _ 96 144 192 (span_join _ 96 120 144 (span_decide _ 96 120 checkedOrbit_6_1_96) (span_decide _ 120 144 checkedOrbit_6_1_120)) (span_join _ 144 168 192 (span_decide _ 144 168 checkedOrbit_6_1_144) (span_decide _ 168 192 checkedOrbit_6_1_168)))) (span_decide _ 192 211 checkedOrbit_6_1_192))

lemma layerOrbit_7_0 : spanOK (orbitEntry 7 0) 0 54 :=
  (span_join _ 0 48 54 (span_join _ 0 24 48 (span_decide _ 0 24 checkedOrbit_7_0_0) (span_decide _ 24 48 checkedOrbit_7_0_24)) (span_decide _ 48 54 checkedOrbit_7_0_48))

lemma layerOrbit_7_1 : spanOK (orbitEntry 7 1) 0 85 :=
  (span_join _ 0 48 85 (span_join _ 0 24 48 (span_decide _ 0 24 checkedOrbit_7_1_0) (span_decide _ 24 48 checkedOrbit_7_1_24)) (span_join _ 48 72 85 (span_decide _ 48 72 checkedOrbit_7_1_48) (span_decide _ 72 85 checkedOrbit_7_1_72)))

lemma layerOrbit_8_0 : spanOK (orbitEntry 8 0) 0 2 :=
  (span_decide _ 0 2 checkedOrbit_8_0_0)

lemma layerOrbit_8_1 : spanOK (orbitEntry 8 1) 0 6 :=
  (span_decide _ 0 6 checkedOrbit_8_1_0)

lemma orbitEntries_checked (k t i : Nat) (hi : i < repCount k t) : orbitEntry k t i = true := by
  have hr : 5 ≤ k ∧ k ≤ 8 ∧ t ≤ 1 := by
    unfold repCount at hi
    split at hi <;> omega
  obtain ⟨hk, hk', ht⟩ := hr
  interval_cases k <;> interval_cases t
  · exact layerOrbit_5_0 i (Nat.zero_le _) hi
  · exact layerOrbit_5_1 i (Nat.zero_le _) hi
  · exact layerOrbit_6_0 i (Nat.zero_le _) hi
  · exact layerOrbit_6_1 i (Nat.zero_le _) hi
  · exact layerOrbit_7_0 i (Nat.zero_le _) hi
  · exact layerOrbit_7_1 i (Nat.zero_le _) hi
  · exact layerOrbit_8_0 i (Nat.zero_le _) hi
  · exact layerOrbit_8_1 i (Nat.zero_le _) hi

lemma certifiedOrbit_hit (k t : Nat) {w : List Sig} (hit : orbitHit k t w = true) : search k t w = false :=
  orbitHit_sound k t (fun i hi => orbitTable_sound orbitEntries_checked k t i hi) hit

set_option maxRecDepth 25000 in
lemma orbitClosed_9_1 : search 9 1 hardFixedInputs = false := by
  apply rootCover_9_1 <;> apply certifiedOrbit_hit <;> decide +kernel

set_option maxRecDepth 25000 in
lemma orbitClosed_8_1 : search 8 1 hardFixedInputs = false := by
  apply rootCover_8_1 <;> apply certifiedOrbit_hit <;> decide +kernel

set_option maxRecDepth 25000 in
lemma orbitClosed_8_0 : search 8 0 hardFixedInputs = false := by
  apply rootCover_8_0 <;> apply certifiedOrbit_hit <;> decide +kernel

lemma cert_fee8e888_8_0 : search 8 0 v_fee8e888 = false := orbitClosed_8_0

lemma cert_fee8e888_8_1 : search 8 1 v_fee8e888 = false := orbitClosed_8_1

lemma cert_fee8e888_9_1 : search 9 1 v_fee8e888 = false := orbitClosed_9_1

lemma lower_eae8eac8 (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hnot : C.gates.countP isNotGate = 1)
    (hcorrect : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit 0xeae8eac8 (sampleMask x)) :
    6 ≤ C.size := by
  apply sample_lower C v_eae8eac8 6 0xeae8eac8 hfan hnot hcorrect len_eae8eac8 nodup_eae8eac8 ess_eae8eac8 pos_eae8eac8 neg_eae8eac8
  intro k t hk ht hone hs hlive
  have casesKt : (k = 4 ∧ t = 0) ∨ (k = 5 ∧ t = 1) := by omega
  rcases casesKt with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact cert_eae8eac8_4_0
  · exact cert_eae8eac8_5_1

lemma lower_eaeaea88 (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hnot : C.gates.countP isNotGate = 1)
    (hcorrect : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit 0xeaeaea88 (sampleMask x)) :
    6 ≤ C.size := by
  apply sample_lower C v_eaeaea88 6 0xeaeaea88 hfan hnot hcorrect len_eaeaea88 nodup_eaeaea88 ess_eaeaea88 pos_eaeaea88 neg_eaeaea88
  intro k t hk ht hone hs hlive
  have casesKt : (k = 4 ∧ t = 0) ∨ (k = 5 ∧ t = 1) := by omega
  rcases casesKt with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact cert_eaeaea88_4_0
  · exact cert_eaeaea88_5_1

lemma lower_eaeaeac0 (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hnot : C.gates.countP isNotGate = 1)
    (hcorrect : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit 0xeaeaeac0 (sampleMask x)) :
    4 ≤ C.size := by
  apply sample_lower C v_eaeaeac0 4 0xeaeaeac0 hfan hnot hcorrect len_eaeaeac0 nodup_eaeaeac0 ess_eaeaeac0 pos_eaeaeac0 neg_eaeaeac0
  intro k t hk ht hone hs hlive
  omega

lemma lower_eee0eae0 (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hnot : C.gates.countP isNotGate = 1)
    (hcorrect : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit 0xeee0eae0 (sampleMask x)) :
    5 ≤ C.size := by
  apply sample_lower C v_eee0eae0 5 0xeee0eae0 hfan hnot hcorrect len_eee0eae0 nodup_eee0eae0 ess_eee0eae0 pos_eee0eae0 neg_eee0eae0
  intro k t hk ht hone hs hlive
  omega

lemma lower_eee8e8a8 (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hnot : C.gates.countP isNotGate = 1)
    (hcorrect : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit 0xeee8e8a8 (sampleMask x)) :
    8 ≤ C.size := by
  apply sample_lower C v_eee8e8a8 8 0xeee8e8a8 hfan hnot hcorrect len_eee8e8a8 nodup_eee8e8a8 ess_eee8e8a8 pos_eee8e8a8 neg_eee8e8a8
  intro k t hk ht hone hs hlive
  have casesKt : (k = 4 ∧ t = 0) ∨ (k = 5 ∧ t = 0) ∨ (k = 5 ∧ t = 1) ∨ (k = 6 ∧ t = 0) ∨ (k = 6 ∧ t = 1) ∨ (k = 7 ∧ t = 1) := by omega
  rcases casesKt with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact cert_eee8e8a8_4_0
  · exact cert_eee8e8a8_5_0
  · exact cert_eee8e8a8_5_1
  · exact cert_eee8e8a8_6_0
  · exact cert_eee8e8a8_6_1
  · exact cert_eee8e8a8_7_1

lemma lower_eee8e8e0 (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hnot : C.gates.countP isNotGate = 1)
    (hcorrect : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit 0xeee8e8e0 (sampleMask x)) :
    8 ≤ C.size := by
  apply sample_lower C v_eee8e8e0 8 0xeee8e8e0 hfan hnot hcorrect len_eee8e8e0 nodup_eee8e8e0 ess_eee8e8e0 pos_eee8e8e0 neg_eee8e8e0
  intro k t hk ht hone hs hlive
  have casesKt : (k = 4 ∧ t = 0) ∨ (k = 5 ∧ t = 0) ∨ (k = 5 ∧ t = 1) ∨ (k = 6 ∧ t = 0) ∨ (k = 6 ∧ t = 1) ∨ (k = 7 ∧ t = 1) := by omega
  rcases casesKt with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact cert_eee8e8e0_4_0
  · exact cert_eee8e8e0_5_0
  · exact cert_eee8e8e0_5_1
  · exact cert_eee8e8e0_6_0
  · exact cert_eee8e8e0_6_1
  · exact cert_eee8e8e0_7_1

lemma lower_eee8eaa0 (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hnot : C.gates.countP isNotGate = 1)
    (hcorrect : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit 0xeee8eaa0 (sampleMask x)) :
    8 ≤ C.size := by
  apply sample_lower C v_eee8eaa0 8 0xeee8eaa0 hfan hnot hcorrect len_eee8eaa0 nodup_eee8eaa0 ess_eee8eaa0 pos_eee8eaa0 neg_eee8eaa0
  intro k t hk ht hone hs hlive
  have casesKt : (k = 4 ∧ t = 0) ∨ (k = 5 ∧ t = 0) ∨ (k = 5 ∧ t = 1) ∨ (k = 6 ∧ t = 0) ∨ (k = 6 ∧ t = 1) ∨ (k = 7 ∧ t = 1) := by omega
  rcases casesKt with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact cert_eee8eaa0_4_0
  · exact cert_eee8eaa0_5_0
  · exact cert_eee8eaa0_5_1
  · exact cert_eee8eaa0_6_0
  · exact cert_eee8eaa0_6_1
  · exact cert_eee8eaa0_7_1

lemma lower_eee8eac0 (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hnot : C.gates.countP isNotGate = 1)
    (hcorrect : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit 0xeee8eac0 (sampleMask x)) :
    8 ≤ C.size := by
  apply sample_lower C v_eee8eac0 8 0xeee8eac0 hfan hnot hcorrect len_eee8eac0 nodup_eee8eac0 ess_eee8eac0 pos_eee8eac0 neg_eee8eac0
  intro k t hk ht hone hs hlive
  have casesKt : (k = 4 ∧ t = 0) ∨ (k = 5 ∧ t = 0) ∨ (k = 5 ∧ t = 1) ∨ (k = 6 ∧ t = 0) ∨ (k = 6 ∧ t = 1) ∨ (k = 7 ∧ t = 1) := by omega
  rcases casesKt with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact cert_eee8eac0_4_0
  · exact cert_eee8eac0_5_0
  · exact cert_eee8eac0_5_1
  · exact cert_eee8eac0_6_0
  · exact cert_eee8eac0_6_1
  · exact cert_eee8eac0_7_1

lemma lower_fee8e888 (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hnot : C.gates.countP isNotGate = 1)
    (hcorrect : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit 0xfee8e888 (sampleMask x)) :
    10 ≤ C.size := by
  apply sample_lower C v_fee8e888 10 0xfee8e888 hfan hnot hcorrect len_fee8e888 nodup_fee8e888 ess_fee8e888 pos_fee8e888 neg_fee8e888
  intro k t hk ht hone hs hlive
  have casesKt : (k = 4 ∧ t = 0) ∨ (k = 5 ∧ t = 0) ∨ (k = 5 ∧ t = 1) ∨ (k = 6 ∧ t = 0) ∨ (k = 6 ∧ t = 1) ∨ (k = 7 ∧ t = 0) ∨ (k = 7 ∧ t = 1) ∨ (k = 8 ∧ t = 0) ∨ (k = 8 ∧ t = 1) ∨ (k = 9 ∧ t = 1) := by omega
  rcases casesKt with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact cert_fee8e888_4_0
  · exact cert_fee8e888_5_0
  · exact cert_fee8e888_5_1
  · exact cert_fee8e888_6_0
  · exact cert_fee8e888_6_1
  · exact cert_fee8e888_7_0
  · exact cert_fee8e888_7_1
  · exact cert_fee8e888_8_0
  · exact cert_fee8e888_8_1
  · exact cert_fee8e888_9_1

lemma lower_eaeaeaa8 (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hnot : C.gates.countP isNotGate = 1)
    (hcorrect : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit 0xeaeaeaa8 (sampleMask x)) :
    7 ≤ C.size := by
  apply sample_lower C v_eaeaeaa8 7 0xeaeaeaa8 hfan hnot hcorrect len_eaeaeaa8 nodup_eaeaeaa8 ess_eaeaeaa8 pos_eaeaeaa8 neg_eaeaeaa8
  intro k t hk ht hone hs hlive
  have casesKt : (k = 4 ∧ t = 0) ∨ (k = 5 ∧ t = 0) ∨ (k = 5 ∧ t = 1) ∨ (k = 6 ∧ t = 1) := by omega
  rcases casesKt with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact cert_eaeaeaa8_4_0
  · exact cert_eaeaeaa8_5_0
  · exact cert_eaeaeaa8_5_1
  · exact cert_eaeaeaa8_6_1

open PEqualNP.CircuitLowerBounds

def monotoneWitness (t k : ℕ) : Prop :=
  ∃ (gates : List Gate) (o : ℕ),
    (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
    gates.length ≤ k ∧ ∀ x : Fin 5 → Bool,
      Circuit.eval ⟨gates, o⟩ (List.ofFn x) =
        Nat.testBit t (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

lemma everyRow (P : (Fin 5 → Bool) → Prop)
    (h : ∀ a b c d e : Bool, P ![a, b, c, d, e]) : ∀ x, P x := by
  intro x
  have hx : x = ![x 0, x 1, x 2, x 3, x 4] := by
    funext i
    fin_cases i <;> rfl
  exact hx ▸ h (x 0) (x 1) (x 2) (x 3) (x 4)

lemma upper_eae8eac8 : monotoneWitness 0xeae8eac8 6 := by
  refine ⟨[⟨.or, [0, 2]⟩, ⟨.and, [2, 4]⟩, ⟨.or, [3, 6]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [1, 8]⟩, ⟨.and, [5, 9]⟩], 10, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · apply everyRow
    decide +kernel

lemma upper_eaeaea88 : monotoneWitness 0xeaeaea88 6 := by
  refine ⟨[⟨.and, [0, 1]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [0, 7]⟩, ⟨.and, [6, 8]⟩, ⟨.or, [5, 9]⟩], 10, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · apply everyRow
    decide +kernel

lemma upper_eaeaeac0 : monotoneWitness 0xeaeaeac0 4 := by
  refine ⟨[⟨.and, [1, 2]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [5, 7]⟩], 8, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> simp
  · apply everyRow
    decide +kernel

lemma upper_eee0eae0 : monotoneWitness 0xeee0eae0 5 := by
  refine ⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [3, 6]⟩, ⟨.or, [2, 7]⟩, ⟨.and, [5, 8]⟩], 9, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp
  · apply everyRow
    decide +kernel

lemma upper_eee8e8a8 : monotoneWitness 0xeee8e8a8 8 := by
  refine ⟨[⟨.and, [0, 1]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [0, 9]⟩, ⟨.and, [7, 10]⟩, ⟨.or, [5, 11]⟩], 12, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · apply everyRow
    decide +kernel

lemma upper_eee8e8e0 : monotoneWitness 0xeee8e8e0 8 := by
  refine ⟨[⟨.or, [0, 1]⟩, ⟨.and, [3, 4]⟩, ⟨.and, [0, 1]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [7, 8]⟩, ⟨.or, [6, 9]⟩, ⟨.or, [2, 10]⟩, ⟨.and, [5, 11]⟩], 12, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · apply everyRow
    decide +kernel

lemma upper_eee8eaa0 : monotoneWitness 0xeee8eaa0 8 := by
  refine ⟨[⟨.or, [2, 3]⟩, ⟨.or, [0, 5]⟩, ⟨.and, [0, 5]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [4, 8]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [7, 10]⟩, ⟨.and, [6, 11]⟩], 12, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · apply everyRow
    decide +kernel

lemma upper_eee8eac0 : monotoneWitness 0xeee8eac0 8 := by
  refine ⟨[⟨.and, [2, 4]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [0, 3]⟩, ⟨.and, [4, 8]⟩, ⟨.or, [2, 9]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [7, 11]⟩], 12, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · apply everyRow
    decide +kernel

lemma upper_fee8e888 : monotoneWitness 0xfee8e888 10 := by
  refine ⟨[⟨.or, [3, 4]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [2, 6]⟩, ⟨.and, [5, 7]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [0, 1]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [10, 11]⟩, ⟨.and, [9, 12]⟩, ⟨.or, [8, 13]⟩], 14, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · apply everyRow
    decide +kernel

lemma upper_eaeaeaa8 : monotoneWitness 0xeaeaeaa8 7 := by
  refine ⟨[⟨.and, [1, 2]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [4, 9]⟩, ⟨.and, [6, 10]⟩], 11, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · apply everyRow
    decide +kernel

lemma solveRow {T bound : ℕ} (upper : monotoneWitness T bound)
    (lower : ∀ (C : Circuit), (∀ g ∈ C.gates,
        g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      C.gates.countP isNotGate = 1 →
      (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit T (sampleMask x)) →
      bound ≤ C.size)
    (gates : List Gate) (o : ℕ)
    (hf : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hu : ∀ i j : Fin gates.length, (gates.get i).op = GateOp.not →
      (gates.get j).op = GateOp.not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) =
      Nat.testBit T (sampleMask x)) : monotoneWitness T gates.length := by
  have count := notCount_le_one gates hu
  by_cases hz : gates.countP isNotGate = 0
  · refine ⟨gates, o, ?_, le_rfl, he⟩
    intro g hg
    obtain ⟨hop, hlen⟩ := hf g hg
    refine ⟨?_, hlen⟩
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact False.elim ((List.countP_eq_zero.mp hz g hg) ((isNotGate_iff g).mpr h))
  · have hone : gates.countP isNotGate = 1 := by omega
    have fan : ∀ g ∈ gates,
        g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hf
    have enough : bound ≤ gates.length := lower ⟨gates, o⟩ fan hone he
    obtain ⟨gs, out, hfan, hsz, heval⟩ := upper
    exact ⟨gs, out, hfan, hsz.trans enough, heval⟩

end PEqualNP.Outside.L_meta_1435_aux

open PEqualNP.Outside.L_meta_1435_aux

theorem PEqualNP.Outside.L_meta_1435 : ∀ T ∈ ({0xeae8eac8, 0xeaeaea88, 0xeaeaeac0, 0xeee0eae0, 0xeee8e8a8, 0xeee8e8e0, 0xeee8eaa0, 0xeee8eac0, 0xfee8e888, 0xeaeaeaa8} : Finset ℕ), ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  intro T hT gates o hf hu he
  simp only [Finset.mem_insert, Finset.mem_singleton] at hT
  rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact solveRow upper_eae8eac8 lower_eae8eac8 gates o hf hu he
  · exact solveRow upper_eaeaea88 lower_eaeaea88 gates o hf hu he
  · exact solveRow upper_eaeaeac0 lower_eaeaeac0 gates o hf hu he
  · exact solveRow upper_eee0eae0 lower_eee0eae0 gates o hf hu he
  · exact solveRow upper_eee8e8a8 lower_eee8e8a8 gates o hf hu he
  · exact solveRow upper_eee8e8e0 lower_eee8e8e0 gates o hf hu he
  · exact solveRow upper_eee8eaa0 lower_eee8eaa0 gates o hf hu he
  · exact solveRow upper_eee8eac0 lower_eee8eac0 gates o hf hu he
  · exact solveRow upper_fee8e888 lower_fee8e888 gates o hf hu he
  · exact solveRow upper_eaeaeaa8 lower_eaeaeaa8 gates o hf hu he
