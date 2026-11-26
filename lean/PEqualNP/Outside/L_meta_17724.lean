import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17724_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def opOf (o : ℕ) : GateOp :=
  if o = 0 then GateOp.and else if o = 1 then GateOp.or else GateOp.not

def mkGate (c : ℕ × List ℕ) : Gate := ⟨opOf c.1, c.2⟩

def mkCircuit (code : List (ℕ × List ℕ)) (out : ℕ) : Circuit := ⟨code.map mkGate, out⟩

def gateTab (M : ℕ) (look : ℕ → ℕ) (c : ℕ × List ℕ) : ℕ :=
  if c.1 = 0 then c.2.foldr (fun i a => look i &&& a) M
  else if c.1 = 1 then c.2.foldr (fun i a => look i ||| a) 0
  else M ^^^ (c.2.map look).headD 0

theorem gateTab_bit (M k : ℕ) (hM : M.testBit k = true) (look : ℕ → ℕ) (c : ℕ × List ℕ) :
    (gateTab M look c).testBit k
      = (mkGate c).op.eval ((mkGate c).inputs.map fun i => (look i).testBit k) := by
  obtain ⟨o, ins⟩ := c
  simp only [gateTab, mkGate, opOf]
  split_ifs
  · simp only [GateOp.eval]
    induction ins with
    | nil => simpa using hM
    | cons i ins ih =>
      simp only [List.foldr_cons, List.map_cons, List.all_cons, Nat.testBit_and, ih, id]
  · simp only [GateOp.eval]
    induction ins with
    | nil => simp
    | cons i ins ih =>
      simp only [List.foldr_cons, List.map_cons, List.any_cons, Nat.testBit_or, ih, id]
  · simp only [GateOp.eval]
    cases ins <;> simp [hM]

theorem fanInTwo_mk (code : List (ℕ × List ℕ)) (out : ℕ)
    (h : (code.all fun c => Nat.ble c.2.length 2) = true) : FanInTwo (mkCircuit code out) := by
  intro g hg
  simp only [mkCircuit, List.mem_map] at hg
  obtain ⟨c, hc, rfl⟩ := hg
  rw [List.all_eq_true] at h
  refine ⟨?_, Nat.le_of_ble_eq_true (h c hc)⟩
  simp only [mkGate, opOf]
  split_ifs <;> simp

theorem monotone2_mk (code : List (ℕ × List ℕ)) (out : ℕ)
    (h : (code.all fun c => Nat.ble c.1 1 && Nat.ble c.2.length 2) = true) :
    Monotone2 (mkCircuit code out) := by
  intro g hg
  simp only [mkCircuit, List.mem_map] at hg
  obtain ⟨c, hc, rfl⟩ := hg
  rw [List.all_eq_true] at h
  have h2 := h c hc
  rw [Bool.and_eq_true] at h2
  refine ⟨?_, Nat.le_of_ble_eq_true h2.2⟩
  have h1 := Nat.le_of_ble_eq_true h2.1
  simp only [mkGate, opOf]
  split_ifs with a b
  · simp
  · simp
  · omega

theorem getD_bit (ts : List ℕ) (k i : ℕ) :
    (ts.map fun t => t.testBit k).getD i false = (ts.getD i 0).testBit k := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ts[i]? <;> simp

def slot (B W i : ℕ) : ℕ := (W >>> (i * B)) % 2 ^ B

def push (B len W t : ℕ) : ℕ := W ||| (t % 2 ^ B) <<< (len * B)

def pushAll (B : ℕ) : List ℕ → ℕ → ℕ → ℕ
  | [], _, W => W
  | t :: ts, len, W => pushAll B ts (len + 1) (push B len W t)

def runP (M B : ℕ) : List (ℕ × List ℕ) → ℕ → ℕ → ℕ
  | [], _, W => W
  | c :: cs, len, W =>
    bif Nat.ble (push B len W (gateTab M (slot B W) c)) 0 then runP M B cs (len + 1) 0
    else runP M B cs (len + 1) (push B len W (gateTab M (slot B W) c))

def outT (M B : ℕ) (code : List (ℕ × List ℕ)) (out : ℕ) (ts : List ℕ) : ℕ :=
  slot B (runP M B code ts.length (pushAll B ts 0 0)) out

def Holds (B k len W : ℕ) (w : List Bool) : Prop :=
  w = (List.range len).map (fun i => W.testBit (i * B + k)) ∧
    ∀ j : ℕ, len * B ≤ j → W.testBit j = false

theorem push_bit (B len W t j : ℕ) :
    (push B len W t).testBit j
      = (W.testBit j || (decide (len * B ≤ j) &&
          (decide (j - len * B < B) && t.testBit (j - len * B)))) := by
  simp [push, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_mod_two_pow]

theorem push_holds {B k len W : ℕ} {w : List Bool} (hk : k < B) (h : Holds B k len W w)
    (t : ℕ) : Holds B k (len + 1) (push B len W t) (w ++ [t.testBit k]) := by
  obtain ⟨rfl, hb⟩ := h
  constructor
  · rw [List.range_succ, List.map_append, List.map_singleton]
    congr 1
    · apply List.map_congr_left
      intro i hi
      have h1 : (i + 1) * B ≤ len * B := Nat.mul_le_mul_right B (List.mem_range.mp hi)
      rw [Nat.succ_mul] at h1
      have h2 : ¬ len * B ≤ i * B + k := by omega
      rw [push_bit]
      simp [h2]
    · rw [push_bit, hb _ (Nat.le_add_right _ _)]
      simp [hk]
  · intro j hj
    rw [Nat.succ_mul] at hj
    have h2 : ¬ j - len * B < B := by omega
    rw [push_bit, hb j (by omega)]
    simp [h2]

theorem slot_bit {B k len W : ℕ} {w : List Bool} (hk : k < B) (h : Holds B k len W w)
    (i : ℕ) : (slot B W i).testBit k = w.getD i false := by
  obtain ⟨rfl, hb⟩ := h
  simp only [slot, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, hk, decide_true,
    Bool.true_and]
  by_cases hi : i < len
  · simp [List.getD_eq_getElem?_getD, hi]
  · have h1 : len * B ≤ i * B + k :=
      Nat.le_trans (Nat.mul_le_mul_right B (Nat.le_of_not_lt hi)) (Nat.le_add_right _ _)
    rw [hb _ h1]
    simp [List.getD_eq_getElem?_getD, hi]

theorem runP_holds (M B k : ℕ) (hk : k < B) (hM : M.testBit k = true)
    (code : List (ℕ × List ℕ)) : ∀ (len W : ℕ) (w : List Bool), Holds B k len W w →
      Holds B k (len + code.length) (runP M B code len W)
        ((code.map mkGate).foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w) := by
  induction code with
  | nil => intro len W w h; exact h
  | cons c cs ih =>
    intro len W w h
    have e : runP M B (c :: cs) len W
        = runP M B cs (len + 1) (push B len W (gateTab M (slot B W) c)) := by
      rw [runP]
      cases hz : Nat.ble (push B len W (gateTab M (slot B W) c)) 0
      · rfl
      · rw [Nat.le_zero.mp (Nat.le_of_ble_eq_true hz)]
        rfl
    have hg : (mkGate c).op.eval ((mkGate c).inputs.map fun i => w.getD i false)
        = (gateTab M (slot B W) c).testBit k := by
      rw [gateTab_bit M k hM]
      congr 1
      apply List.map_congr_left
      intro i _
      exact (slot_bit hk h i).symm
    have h1 := ih (len + 1) _ _ (push_holds hk h (gateTab M (slot B W) c))
    rw [e, List.map_cons, List.foldl_cons, List.length_cons, hg]
    rwa [show len + (cs.length + 1) = len + 1 + cs.length by omega]

theorem pushAll_holds {B k : ℕ} (hk : k < B) (ts : List ℕ) :
    ∀ (len W : ℕ) (w : List Bool), Holds B k len W w →
      Holds B k (len + ts.length) (pushAll B ts len W) (w ++ ts.map fun t => t.testBit k) := by
  induction ts with
  | nil => intro len W w h; simpa [pushAll] using h
  | cons t ts ih =>
    intro len W w h
    have h1 := ih (len + 1) _ _ (push_holds hk h t)
    rw [pushAll, List.map_cons, List.length_cons]
    rw [show len + (ts.length + 1) = len + 1 + ts.length by omega]
    simpa using h1

theorem outT_bit (M B k : ℕ) (hk : k < B) (hM : M.testBit k = true)
    (code : List (ℕ × List ℕ)) (out : ℕ) (ts : List ℕ) :
    (mkCircuit code out).eval (ts.map fun t => t.testBit k)
      = (outT M B code out ts).testBit k := by
  have h0 := pushAll_holds hk ts 0 0 []
    ⟨rfl, fun j _ => Nat.zero_testBit j⟩
  simp only [Nat.zero_add, List.nil_append] at h0
  have h1 := runP_holds M B k hk hM code _ _ _ h0
  simp only [Circuit.eval, Circuit.wires, mkCircuit, outT]
  exact (slot_bit hk h1 out).symm

def varTab : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, b =>
    if b = n then (2 ^ 2 ^ n - 1) <<< 2 ^ n else varTab n b ||| varTab n b <<< 2 ^ n

theorem varTab_bit : ∀ n b k : ℕ,
    (varTab n b).testBit k = (decide (k < 2 ^ n) && decide (b < n) && k.testBit b) := by
  intro n
  induction n with
  | zero => intro b k; simp [varTab]
  | succ n ih =>
    intro b k
    have h2 : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by ring
    rw [varTab]
    split_ifs with hb
    · subst hb
      rw [Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
      by_cases h1 : 2 ^ b ≤ k
      · by_cases h3 : k < 2 ^ (b + 1)
        · rw [Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt h1 h3]
          simp [h1, h3]; omega
        · have : ¬ (k - 2 ^ b < 2 ^ b) := by omega
          simp [h3, this]
      · have h4 : k < 2 ^ b := by omega
        rw [Nat.testBit_lt_two_pow h4]
        simp [h1]
    · rw [Nat.testBit_or, Nat.testBit_shiftLeft, ih, ih]
      by_cases hbn : b < n
      · have hbn' : b < n + 1 := by omega
        by_cases h1 : 2 ^ n ≤ k
        · have hk : k = 2 ^ n + (k - 2 ^ n) := by omega
          have h5 : (k - 2 ^ n).testBit b = k.testBit b := by
            conv_rhs => rw [hk]
            exact (Nat.testBit_two_pow_add_gt hbn _).symm
          have h6 : ¬ k < 2 ^ n := by omega
          have h7 : (k - 2 ^ n < 2 ^ n) = (k < 2 ^ (n + 1)) := by
            apply propext; omega
          simp [h1, h5, h6, h7, hbn, hbn']
        · have h6 : k < 2 ^ n := by omega
          have h7 : k < 2 ^ (n + 1) := by omega
          simp [h1, h6, h7, hbn, hbn']
      · have hbn' : ¬ b < n + 1 := by omega
        simp [hbn, hbn']

def idxL : List Bool → ℕ
  | [] => 0
  | b :: bs => Nat.bit b (idxL bs)

theorem idxL_lt : ∀ bs : List Bool, idxL bs < 2 ^ bs.length := by
  intro bs
  induction bs with
  | nil => simp [idxL]
  | cons b bs ih =>
    have h2 : 2 ^ (bs.length + 1) = 2 ^ bs.length + 2 ^ bs.length := by ring
    rw [idxL, List.length_cons, Nat.bit_val]
    cases b <;> simp <;> omega

theorem range_bits : ∀ bs : List Bool,
    (List.range bs.length).map (fun i => (idxL bs).testBit i) = bs := by
  intro bs
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    conv_rhs => rw [← ih]
    simp only [idxL, Function.comp_def, Nat.testBit_bit_zero, Nat.testBit_bit_succ,
      Nat.succ_eq_add_one]

def dnfVal (w : List Bool) (terms : List (List ℕ)) : Bool :=
  terms.foldl (fun acc t => acc || t.foldl (fun a i => a && w.getD i false) true) false

def dnfTab (M : ℕ) (ts : List ℕ) (terms : List (List ℕ)) : ℕ :=
  terms.foldl (fun acc t => acc ||| t.foldl (fun a i => a &&& ts.getD i 0) M) 0

theorem conj_bit (k : ℕ) (ts : List ℕ) (t : List ℕ) : ∀ a : ℕ,
    (t.foldl (fun a i => a &&& ts.getD i 0) a).testBit k
      = t.foldl (fun a i => a && (ts.map fun t => t.testBit k).getD i false) (a.testBit k) := by
  induction t with
  | nil => intro a; rfl
  | cons i t ih =>
    intro a
    rw [List.foldl_cons, List.foldl_cons, ih, Nat.testBit_and, getD_bit]

theorem dnfTab_bit (M k : ℕ) (hM : M.testBit k = true) (ts : List ℕ) (terms : List (List ℕ)) :
    (dnfTab M ts terms).testBit k = dnfVal (ts.map fun t => t.testBit k) terms := by
  have h : ∀ (terms : List (List ℕ)) (acc : ℕ),
      (terms.foldl (fun acc t => acc ||| t.foldl (fun a i => a &&& ts.getD i 0) M) acc).testBit k
        = terms.foldl (fun acc t => acc ||
            t.foldl (fun a i => a && (ts.map fun t => t.testBit k).getD i false) true)
          (acc.testBit k) := by
    intro terms
    induction terms with
    | nil => intro acc; rfl
    | cons t terms ih =>
      intro acc
      rw [List.foldl_cons, List.foldl_cons, ih, Nat.testBit_or, conj_bit, hM]
  have h0 := h terms 0
  rw [Nat.zero_testBit] at h0
  exact h0

def inTabs (n : ℕ) : List ℕ := (List.range n).map (varTab n)

theorem inTabs_bit (bs : List Bool) :
    (inTabs bs.length).map (fun t => t.testBit (idxL bs)) = bs := by
  unfold inTabs
  rw [List.map_map]
  conv_rhs => rw [← range_bits bs]
  apply List.map_congr_left
  intro b hb
  simp [varTab_bit, idxL_lt bs, List.mem_range.mp hb]

def checkDnf (n : ℕ) (code : List (ℕ × List ℕ)) (out : ℕ) (neg : Bool)
    (terms : List (List ℕ)) : Bool :=
  (code.all fun c => Nat.ble c.2.length 2) &&
    Nat.beq (outT (2 ^ 2 ^ n - 1) (2 ^ n) code out (inTabs n))
      (bif neg then (2 ^ 2 ^ n - 1) ^^^ dnfTab (2 ^ 2 ^ n - 1) (inTabs n) terms
        else dnfTab (2 ^ 2 ^ n - 1) (inTabs n) terms)

theorem sound_dnf (n : ℕ) (code : List (ℕ × List ℕ)) (out : ℕ) (neg : Bool)
    (terms : List (List ℕ)) (s : ℕ) (f : (Fin n → Bool) → Bool)
    (hf : ∀ x : Fin n → Bool, f x =
      (bif neg then !dnfVal (List.ofFn x) terms else dnfVal (List.ofFn x) terms))
    (hs : code.length ≤ s) (hc : checkDnf n code out neg terms = true) :
    HasCircuitSize n f s := by
  simp only [checkDnf, Bool.and_eq_true] at hc
  obtain ⟨hfan, hT⟩ := hc
  have hT := Nat.eq_of_beq_eq_true hT
  refine ⟨mkCircuit code out, fanInTwo_mk code out hfan, ?_, ?_⟩
  · simpa [Circuit.size, mkCircuit] using hs
  · intro x
    have hb := inTabs_bit (List.ofFn x)
    have hl := idxL_lt (List.ofFn x)
    rw [List.length_ofFn] at hb hl
    have hM : (2 ^ 2 ^ n - 1).testBit (idxL (List.ofFn x)) = true := by
      rw [Nat.testBit_two_pow_sub_one]
      exact decide_eq_true hl
    have he := outT_bit _ _ _ hl hM code out (inTabs n)
    rw [hb] at he
    rw [he, hT, hf]
    cases neg
    · simp only [Bool.cond_false]
      rw [dnfTab_bit _ _ hM, hb]
    · simp only [Bool.cond_true]
      rw [Nat.testBit_xor, hM, dnfTab_bit _ _ hM, hb]
      simp

end PEqualNP.Outside.L_meta_17724_aux

theorem PEqualNP.Outside.L_meta_17724 : PEqualNP.MetaComplexity.HasCircuitSize 15 (fun x : Fin 15 → Bool => !((x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 7 && x 9 && x 13 && x 14) || (x 0 && x 2 && x 4 && x 6 && x 8 && x 13) || (x 2 && x 3 && x 4 && x 5 && x 6 && x 7 && x 9 && x 11 && x 12 && x 13) || (x 0 && x 3 && x 4 && x 5 && x 7 && x 9 && x 10 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 5 && x 6 && x 7 && x 9 && x 10 && x 11 && x 14) || (x 0 && x 1 && x 2 && x 6 && x 7 && x 9 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 3 && x 7 && x 8 && x 9 && x 10 && x 12 && x 13 && x 14) || (x 1 && x 3 && x 4 && x 5 && x 6 && x 7 && x 9 && x 10 && x 11 && x 13) || (x 0 && x 3 && x 4 && x 6 && x 7 && x 9 && x 10 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 6 && x 9 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 1 && x 4 && x 5 && x 7 && x 9 && x 10 && x 11 && x 12 && x 13) || (x 2 && x 3 && x 4 && x 5 && x 6 && x 8 && x 9 && x 10 && x 12 && x 13) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 6 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 4 && x 6 && x 8 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 2 && x 3 && x 7 && x 8 && x 9 && x 10 && x 11 && x 12 && x 14) || (x 1 && x 2 && x 3 && x 5 && x 7 && x 8 && x 9 && x 10 && x 11 && x 13) || (x 0 && x 1 && x 3 && x 6 && x 7 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 5 && x 7 && x 8 && x 9 && x 10 && x 11 && x 12) || (x 0 && x 1 && x 2 && x 5 && x 8 && x 9 && x 10 && x 11 && x 12 && x 14) || (x 0 && x 2 && x 4 && x 7 && x 8 && x 9 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 5 && x 6 && x 7 && x 8 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 8 && x 9 && x 10 && x 11 && x 12 && x 13) || (x 1 && x 2 && x 4 && x 6 && x 7 && x 8 && x 9 && x 10 && x 12 && x 13) || (x 2 && x 3 && x 4 && x 5 && x 7 && x 8 && x 9 && x 10 && x 12 && x 14) || (x 0 && x 2 && x 3 && x 5 && x 6 && x 9 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 6 && x 7 && x 9 && x 11 && x 14) || (x 0 && x 1 && x 2 && x 5 && x 6 && x 7 && x 8 && x 10 && x 13 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 7 && x 10) || (x 0 && x 3 && x 4 && x 6 && x 8 && x 9 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 6 && x 7 && x 10 && x 11 && x 13) || (x 9 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 2 && x 3 && x 4 && x 5 && x 6 && x 7 && x 10 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 2 && x 5 && x 6 && x 9) || (x 2 && x 3 && x 4 && x 5 && x 7 && x 8 && x 9 && x 11 && x 13 && x 14) || (x 1 && x 2 && x 3 && x 5 && x 7 && x 8 && x 10 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 8 && x 9 && x 12 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 7 && x 8 && x 9 && x 10 && x 13) || (x 0 && x 1 && x 4 && x 5 && x 6 && x 7 && x 8 && x 10 && x 12 && x 13) || (x 0 && x 2 && x 4 && x 6 && x 7 && x 9 && x 10 && x 11 && x 12 && x 13) || (x 1 && x 3 && x 4 && x 5 && x 6 && x 7 && x 10 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 5 && x 7 && x 8 && x 11 && x 12 && x 13 && x 14) || (x 1 && x 3 && x 4 && x 6 && x 7 && x 8 && x 9 && x 11 && x 13 && x 14) || (x 0 && x 2 && x 4 && x 5 && x 8 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 1 && x 3 && x 4 && x 5 && x 6 && x 8 && x 9 && x 10 && x 11 && x 12) || (x 0 && x 3 && x 4 && x 7 && x 8 && x 14) || (x 1 && x 2 && x 3 && x 6 && x 7 && x 8 && x 10 && x 11 && x 12 && x 14) || (x 2 && x 3 && x 4 && x 5 && x 6 && x 8 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 7 && x 8 && x 9 && x 11 && x 12) || (x 0 && x 2 && x 3 && x 6 && x 7 && x 12) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 8 && x 10 && x 12 && x 13) || (x 1 && x 3 && x 4 && x 5 && x 6 && x 8 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 6 && x 7 && x 8 && x 11 && x 12 && x 13) || (x 1 && x 3 && x 4 && x 6 && x 7 && x 8 && x 9 && x 10 && x 12 && x 14) || (x 0 && x 3 && x 4 && x 5 && x 6 && x 7 && x 8 && x 9 && x 10 && x 13) || (x 0 && x 2 && x 4 && x 5 && x 6 && x 7 && x 8 && x 10 && x 11 && x 12) || (x 0 && x 2 && x 4 && x 5 && x 6 && x 7 && x 8 && x 9 && x 10 && x 14) || (x 0 && x 1 && x 2 && x 6 && x 8 && x 9 && x 10 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 4 && x 5 && x 6 && x 9 && x 10 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 7 && x 11 && x 12 && x 13) || (x 1 && x 2 && x 3 && x 5 && x 6 && x 8 && x 9 && x 10 && x 11 && x 14) || (x 0 && x 1 && x 4 && x 5 && x 8 && x 11) || (x 1 && x 2 && x 3 && x 9 && x 10 && x 12) || (x 0 && x 1 && x 4 && x 7 && x 8 && x 9 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 6 && x 8 && x 9 && x 10 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 6 && x 8 && x 10 && x 11 && x 12) || (x 0 && x 2 && x 3 && x 5 && x 6 && x 7 && x 8 && x 10 && x 11 && x 13) || (x 0 && x 1 && x 2 && x 5 && x 7 && x 9 && x 10 && x 11 && x 13 && x 14) || (x 5 && x 7 && x 8 && x 10 && x 11 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 6 && x 7 && x 8 && x 9 && x 13 && x 14) || (x 2 && x 3 && x 4 && x 12 && x 13 && x 14) || (x 6 && x 7 && x 8 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 6 && x 7 && x 8 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 2 && x 3 && x 5 && x 7 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 5 && x 6 && x 8 && x 9 && x 11 && x 13) || (x 0 && x 2 && x 3 && x 5 && x 6 && x 7 && x 8 && x 9 && x 11 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 6 && x 10 && x 13 && x 14) || (x 1 && x 2 && x 3 && x 6 && x 7 && x 8 && x 9 && x 11 && x 12 && x 13) || (x 1 && x 3 && x 4 && x 10 && x 11 && x 14) || (x 0 && x 2 && x 3 && x 6 && x 8 && x 9 && x 10 && x 11 && x 12 && x 13) || (x 1 && x 2 && x 4 && x 9 && x 11 && x 13) || (x 5 && x 6 && x 7 && x 9 && x 10 && x 12) || (x 0 && x 3 && x 4 && x 5 && x 6 && x 7 && x 8 && x 9 && x 11 && x 12) || (x 1 && x 2 && x 3 && x 5 && x 6 && x 8 && x 9 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 4 && x 5 && x 6 && x 7 && x 8 && x 9 && x 12 && x 14) || (x 0 && x 3 && x 4 && x 5 && x 8 && x 9 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 2 && x 4 && x 5 && x 6 && x 9 && x 10 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 5 && x 6 && x 7 && x 9 && x 12 && x 13 && x 14))) 260 := by
  refine PEqualNP.Outside.L_meta_17724_aux.sound_dnf 15 [(0, [1, 2]), (0, [1, 3]), (0, [1, 4]), (0, [2, 3]), (0, [2, 4]), (0, [3, 4]), (0, [5, 6]), (0, [5, 7]), (0, [5, 8]), (0, [6, 7]), (0, [6, 8]), (0, [7, 8]), (0, [9, 14]), (0, [10, 13]), (0, [11, 12]), (1, [28, 29]), (1, [27, 29]), (1, [27, 28]), (0, [15, 20]), (0, [0, 33]), (0, [21, 26]), (0, [0, 35]), (0, [9, 26]), (0, [14, 21]), (1, [37, 38]), (0, [30, 39]), (0, [10, 25]), (0, [13, 22]), (1, [41, 42]), (0, [31, 43]), (0, [11, 24]), (0, [12, 23]), (1, [45, 46]), (0, [32, 47]), (1, [40, 44]), (1, [48, 49]), (0, [34, 50]), (0, [9, 20]), (0, [14, 15]), (1, [52, 53]), (0, [30, 54]), (0, [10, 19]), (0, [13, 16]), (1, [56, 57]), (0, [31, 58]), (0, [11, 18]), (0, [12, 17]), (1, [60, 61]), (0, [32, 62]), (1, [55, 59]), (1, [63, 64]), (0, [36, 65]), (0, [15, 21]), (0, [9, 67]), (0, [16, 22]), (0, [10, 69]), (0, [17, 23]), (0, [11, 71]), (0, [18, 24]), (0, [12, 73]), (0, [19, 25]), (0, [13, 75]), (0, [20, 26]), (0, [14, 77]), (1, [68, 70]), (1, [72, 79]), (1, [74, 80]), (1, [76, 81]), (1, [78, 82]), (0, [0, 83]), (0, [1, 5]), (0, [1, 10]), (0, [1, 11]), (0, [5, 10]), (0, [5, 11]), (0, [10, 11]), (0, [2, 6]), (0, [2, 12]), (0, [2, 13]), (0, [6, 12]), (0, [6, 13]), (0, [12, 13]), (0, [0, 14]), (0, [3, 8]), (0, [4, 7]), (1, [98, 99]), (1, [97, 99]), (1, [97, 98]), (0, [85, 90]), (0, [9, 103]), (0, [91, 96]), (0, [9, 105]), (0, [0, 96]), (0, [14, 91]), (1, [107, 108]), (0, [100, 109]), (0, [3, 95]), (0, [8, 92]), (1, [111, 112]), (0, [101, 113]), (0, [4, 94]), (0, [7, 93]), (1, [115, 116]), (0, [102, 117]), (1, [110, 114]), (1, [118, 119]), (0, [104, 120]), (0, [0, 90]), (0, [14, 85]), (1, [122, 123]), (0, [100, 124]), (0, [3, 89]), (0, [8, 86]), (1, [126, 127]), (0, [101, 128]), (0, [4, 88]), (0, [7, 87]), (1, [130, 131]), (0, [102, 132]), (1, [125, 129]), (1, [133, 134]), (0, [106, 135]), (0, [86, 92]), (0, [3, 137]), (0, [87, 93]), (0, [4, 139]), (0, [88, 94]), (0, [7, 141]), (0, [89, 95]), (0, [8, 143]), (0, [90, 96]), (0, [14, 145]), (1, [138, 140]), (1, [142, 147]), (1, [144, 148]), (1, [146, 149]), (0, [9, 150]), (0, [3, 7]), (0, [3, 10]), (0, [3, 12]), (0, [7, 10]), (0, [7, 12]), (0, [10, 12]), (0, [4, 8]), (0, [4, 11]), (0, [4, 13]), (0, [8, 11]), (0, [8, 13]), (0, [11, 13]), (0, [0, 9]), (0, [1, 6]), (0, [2, 5]), (1, [165, 166]), (1, [164, 166]), (1, [164, 165]), (0, [152, 157]), (0, [14, 170]), (0, [158, 163]), (0, [14, 172]), (0, [0, 163]), (0, [9, 158]), (1, [174, 175]), (0, [167, 176]), (0, [1, 162]), (0, [6, 159]), (1, [178, 179]), (0, [168, 180]), (0, [2, 161]), (0, [5, 160]), (1, [182, 183]), (0, [169, 184]), (1, [177, 181]), (1, [185, 186]), (0, [171, 187]), (0, [0, 157]), (0, [9, 152]), (1, [189, 190]), (0, [167, 191]), (0, [1, 156]), (0, [6, 153]), (1, [193, 194]), (0, [168, 195]), (0, [2, 155]), (0, [5, 154]), (1, [197, 198]), (0, [169, 199]), (1, [192, 196]), (1, [200, 201]), (0, [173, 202]), (0, [153, 159]), (0, [1, 204]), (0, [154, 160]), (0, [2, 206]), (0, [155, 161]), (0, [5, 208]), (0, [156, 162]), (0, [6, 210]), (1, [205, 207]), (1, [209, 212]), (1, [211, 213]), (0, [14, 214]), (1, [51, 66]), (1, [84, 216]), (1, [121, 217]), (1, [136, 218]), (1, [151, 219]), (1, [188, 220]), (1, [203, 221]), (1, [215, 222]), (2, [223])] 224 true [[0, 1, 2, 3, 4, 5, 7, 9, 13, 14], [0, 2, 4, 6, 8, 13], [2, 3, 4, 5, 6, 7, 9, 11, 12, 13], [0, 3, 4, 5, 7, 9, 10, 12, 13, 14], [1, 2, 4, 5, 6, 7, 9, 10, 11, 14], [0, 1, 2, 6, 7, 9, 11, 12, 13, 14], [0, 1, 3, 7, 8, 9, 10, 12, 13, 14], [1, 3, 4, 5, 6, 7, 9, 10, 11, 13], [0, 3, 4, 6, 7, 9, 10, 11, 12, 14], [0, 1, 3, 5, 6, 9, 10, 11, 13, 14], [0, 1, 4, 5, 7, 9, 10, 11, 12, 13], [2, 3, 4, 5, 6, 8, 9, 10, 12, 13], [0, 1, 2, 3, 4, 5, 6, 11, 12, 14], [0, 1, 4, 6, 8, 10, 11, 12, 13, 14], [0, 2, 3, 7, 8, 9, 10, 11, 12, 14], [1, 2, 3, 5, 7, 8, 9, 10, 11, 13], [0, 1, 3, 6, 7, 10, 11, 12, 13, 14], [1, 2, 4, 5, 7, 8, 9, 10, 11, 12], [0, 1, 2, 5, 8, 9, 10, 11, 12, 14], [0, 2, 4, 7, 8, 9, 10, 11, 13, 14], [0, 1, 2, 5, 6, 7, 8, 11, 12, 14], [0, 1, 3, 5, 8, 9, 10, 11, 12, 13], [1, 2, 4, 6, 7, 8, 9, 10, 12, 13], [2, 3, 4, 5, 7, 8, 9, 10, 12, 14], [0, 2, 3, 5, 6, 9, 11, 12, 13, 14], [0, 1, 2, 3, 4, 6, 7, 9, 11, 14], [0, 1, 2, 5, 6, 7, 8, 10, 13, 14], [0, 1, 3, 5, 7, 10], [0, 3, 4, 6, 8, 9, 10, 11, 13, 14], [0, 1, 2, 3, 4, 6, 7, 10, 11, 13], [9, 10, 11, 12, 13, 14], [2, 3, 4, 5, 6, 7, 10, 11, 12, 14], [0, 1, 2, 5, 6, 9], [2, 3, 4, 5, 7, 8, 9, 11, 13, 14], [1, 2, 3, 5, 7, 8, 10, 12, 13, 14], [0, 1, 2, 3, 4, 5, 8, 9, 12, 14], [0, 1, 2, 3, 4, 7, 8, 9, 10, 13], [0, 1, 4, 5, 6, 7, 8, 10, 12, 13], [0, 2, 4, 6, 7, 9, 10, 11, 12, 13], [1, 3, 4, 5, 6, 7, 10, 12, 13, 14], [1, 2, 4, 5, 7, 8, 11, 12, 13, 14], [1, 3, 4, 6, 7, 8, 9, 11, 13, 14], [0, 2, 4, 5, 8, 10, 11, 12, 13, 14], [1, 3, 4, 5, 6, 8, 9, 10, 11, 12], [0, 3, 4, 7, 8, 14], [1, 2, 3, 6, 7, 8, 10, 11, 12, 14], [2, 3, 4, 5, 6, 8, 10, 11, 13, 14], [0, 1, 2, 3, 4, 7, 8, 9, 11, 12], [0, 2, 3, 6, 7, 12], [0, 1, 2, 3, 4, 5, 8, 10, 12, 13], [1, 3, 4, 5, 6, 8, 11, 12, 13, 14], [0, 1, 3, 5, 6, 7, 8, 11, 12, 13], [1, 3, 4, 6, 7, 8, 9, 10, 12, 14], [0, 3, 4, 5, 6, 7, 8, 9, 10, 13], [0, 2, 4, 5, 6, 7, 8, 10, 11, 12], [0, 2, 4, 5, 6, 7, 8, 9, 10, 14], [0, 1, 2, 6, 8, 9, 10, 12, 13, 14], [0, 1, 4, 5, 6, 9, 10, 11, 12, 14], [0, 1, 2, 3, 4, 5, 7, 11, 12, 13], [1, 2, 3, 5, 6, 8, 9, 10, 11, 14], [0, 1, 4, 5, 8, 11], [1, 2, 3, 9, 10, 12], [0, 1, 4, 7, 8, 9, 11, 12, 13, 14], [0, 1, 2, 3, 4, 6, 8, 9, 10, 14], [0, 1, 2, 3, 4, 6, 8, 10, 11, 12], [0, 2, 3, 5, 6, 7, 8, 10, 11, 13], [0, 1, 2, 5, 7, 9, 10, 11, 13, 14], [5, 7, 8, 10, 11, 14], [0, 1, 3, 5, 6, 7, 8, 9, 13, 14], [2, 3, 4, 12, 13, 14], [6, 7, 8, 12, 13, 14], [1, 2, 4, 6, 7, 8, 10, 11, 13, 14], [0, 2, 3, 5, 7, 10, 11, 12, 13, 14], [5, 6, 8, 9, 11, 13], [0, 2, 3, 5, 6, 7, 8, 9, 11, 14], [0, 1, 2, 3, 4, 5, 6, 10, 13, 14], [1, 2, 3, 6, 7, 8, 9, 11, 12, 13], [1, 3, 4, 10, 11, 14], [0, 2, 3, 6, 8, 9, 10, 11, 12, 13], [1, 2, 4, 9, 11, 13], [5, 6, 7, 9, 10, 12], [0, 3, 4, 5, 6, 7, 8, 9, 11, 12], [1, 2, 3, 5, 6, 8, 9, 12, 13, 14], [0, 1, 4, 5, 6, 7, 8, 9, 12, 14], [0, 3, 4, 5, 8, 9, 11, 12, 13, 14], [0, 2, 4, 5, 6, 9, 10, 12, 13, 14], [1, 2, 4, 5, 6, 7, 9, 12, 13, 14]] 260 _ (fun _ => rfl) ?_ ?_
  · decide +kernel
  · decide +kernel
