import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18217

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

end PEqualNP.Outside.L_meta_18217

theorem PEqualNP.Outside.L_meta_18217 : PEqualNP.MetaComplexity.HasCircuitSize 15 (fun x : Fin 15 → Bool => (x 0 && x 1 && x 5) || (x 0 && x 2 && x 6) || (x 0 && x 3 && x 7) || (x 0 && x 4 && x 8) || (x 1 && x 2 && x 9) || (x 1 && x 3 && x 10) || (x 1 && x 4 && x 11) || (x 2 && x 3 && x 12) || (x 2 && x 4 && x 13) || (x 3 && x 4 && x 14) || (x 5 && x 6 && x 9) || (x 5 && x 7 && x 10) || (x 5 && x 8 && x 11) || (x 6 && x 7 && x 12) || (x 6 && x 8 && x 13) || (x 7 && x 8 && x 14) || (x 9 && x 10 && x 12) || (x 9 && x 11 && x 13) || (x 10 && x 11 && x 14) || (x 12 && x 13 && x 14)) 48 := by
  refine PEqualNP.Outside.L_meta_18217.sound_dnf 15 [(0, [1, 5]), (0, [2, 6]), (0, [3, 7]), (0, [4, 8]), (1, [15, 16]), (1, [19, 17]), (1, [20, 18]), (0, [0, 21]), (0, [2, 9]), (0, [3, 10]), (0, [4, 11]), (1, [23, 24]), (1, [26, 25]), (0, [1, 27]), (0, [3, 12]), (0, [4, 13]), (1, [29, 30]), (0, [2, 31]), (0, [4, 14]), (0, [3, 33]), (1, [22, 28]), (1, [35, 32]), (1, [36, 34]), (0, [12, 7]), (0, [7, 8]), (0, [13, 8]), (0, [8, 11]), (0, [7, 10]), (0, [11, 10]), (0, [13, 11]), (0, [10, 12]), (0, [9, 6]), (0, [13, 12]), (1, [46, 41]), (1, [40, 38]), (1, [48, 42]), (1, [44, 45]), (1, [39, 43]), (0, [51, 9]), (1, [52, 47]), (0, [14, 54]), (0, [50, 5]), (0, [49, 6]), (1, [55, 53]), (1, [56, 57]), (1, [59, 58]), (1, [37, 60])] 61 false [[0, 1, 5], [0, 2, 6], [0, 3, 7], [0, 4, 8], [1, 2, 9], [1, 3, 10], [1, 4, 11], [2, 3, 12], [2, 4, 13], [3, 4, 14], [5, 6, 9], [5, 7, 10], [5, 8, 11], [6, 7, 12], [6, 8, 13], [7, 8, 14], [9, 10, 12], [9, 11, 13], [10, 11, 14], [12, 13, 14]] 48 _ (fun _ => rfl) ?_ ?_
  · decide +kernel
  · decide +kernel
