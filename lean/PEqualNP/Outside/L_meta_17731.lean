import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17731_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-!
Bit-parallel evaluation of a circuit on a family of input vectors.

Vector number `k` of the family is read off bit `k`: every wire carries a natural number, its
table, whose bit `k` is the value of the wire on vector `k`. A gate works on whole tables with the
bitwise operations, so one pass over the gate list evaluates the circuit on all vectors at once.
`outT_bit` says that bit `k` of the table of the output wire is the output of the circuit on
vector `k`, with the conventions of the circuit definition: a wire that does not exist reads
`false`, an AND gate reading no wire is `true`, a gate may read any number of wires.
-/

/-- The operation with code `o`: `0` is AND, `1` is OR, any other code is NOT. -/
def opOf (o : ℕ) : GateOp :=
  if o = 0 then GateOp.and else if o = 1 then GateOp.or else GateOp.not

/-- The gate with code `c`: the code of its operation and the wires it reads. -/
def mkGate (c : ℕ × List ℕ) : Gate := ⟨opOf c.1, c.2⟩

/-- The circuit with the gate codes `code` and the output wire `out`. -/
def mkCircuit (code : List (ℕ × List ℕ)) (out : ℕ) : Circuit := ⟨code.map mkGate, out⟩

/-- The table of the gate with code `c`, when `look i` is the table of wire `i`. `M` is the table
of the constant `true`: it has a one at every vector in use. -/
def gateTab (M : ℕ) (look : ℕ → ℕ) (c : ℕ × List ℕ) : ℕ :=
  if c.1 = 0 then c.2.foldr (fun i a => look i &&& a) M
  else if c.1 = 1 then c.2.foldr (fun i a => look i ||| a) 0
  else M ^^^ (c.2.map look).headD 0

/-- Bit `k` of the table of a gate is the value of the gate on the bits `k` of the tables. -/
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

/-- A circuit built from codes whose gates read at most two wires is a fan-in two circuit. -/
theorem fanInTwo_mk (code : List (ℕ × List ℕ)) (out : ℕ)
    (h : (code.all fun c => Nat.ble c.2.length 2) = true) : FanInTwo (mkCircuit code out) := by
  intro g hg
  simp only [mkCircuit, List.mem_map] at hg
  obtain ⟨c, hc, rfl⟩ := hg
  rw [List.all_eq_true] at h
  refine ⟨?_, Nat.le_of_ble_eq_true (h c hc)⟩
  simp only [mkGate, opOf]
  split_ifs <;> simp

/-- A circuit built from codes `0` and `1` whose gates read at most two wires is monotone. -/
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

/-- Reading bit `k` commutes with looking up a wire. -/
theorem getD_bit (ts : List ℕ) (k i : ℕ) :
    (ts.map fun t => t.testBit k).getD i false = (ts.getD i 0).testBit k := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ts[i]? <;> simp

/-- Table number `i` of the memory `W`: the `B` bits from position `i * B` on. All tables are
kept in one natural number, table `i` in the bits `i * B` to `i * B + B - 1`. -/
def slot (B W i : ℕ) : ℕ := (W >>> (i * B)) % 2 ^ B

/-- The memory `W` of `len` tables with the table `t` added as table number `len`. -/
def push (B len W t : ℕ) : ℕ := W ||| (t % 2 ^ B) <<< (len * B)

/-- The memory with the tables `ts` added one after the other. -/
def pushAll (B : ℕ) : List ℕ → ℕ → ℕ → ℕ
  | [], _, W => W
  | t :: ts, len, W => pushAll B ts (len + 1) (push B len W t)

/-- The memory after all gates: each gate adds its table. The test for zero changes nothing; it
makes the new memory a number before the next gate is looked at. -/
def runP (M B : ℕ) : List (ℕ × List ℕ) → ℕ → ℕ → ℕ
  | [], _, W => W
  | c :: cs, len, W =>
    bif Nat.ble (push B len W (gateTab M (slot B W) c)) 0 then runP M B cs (len + 1) 0
    else runP M B cs (len + 1) (push B len W (gateTab M (slot B W) c))

/-- The table of the output wire (`0`, the table of `false`, if the wire does not exist), for
tables of `B` bits. -/
def outT (M B : ℕ) (code : List (ℕ × List ℕ)) (out : ℕ) (ts : List ℕ) : ℕ :=
  slot B (runP M B code ts.length (pushAll B ts 0 0)) out

/-- The memory `W` holds `len` tables whose bits `k` are the wire values `w`, and nothing else. -/
def Holds (B k len W : ℕ) (w : List Bool) : Prop :=
  w = (List.range len).map (fun i => W.testBit (i * B + k)) ∧
    ∀ j : ℕ, len * B ≤ j → W.testBit j = false

/-- The bits of the memory after adding a table. -/
theorem push_bit (B len W t j : ℕ) :
    (push B len W t).testBit j
      = (W.testBit j || (decide (len * B ≤ j) &&
          (decide (j - len * B < B) && t.testBit (j - len * B)))) := by
  simp [push, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_mod_two_pow]

/-- Adding a table adds its bit `k` to the wire values. -/
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

/-- Bit `k` of a table of the memory is the value of that wire; a wire that does not exist
reads `false`. -/
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

/-- The memory after all gates holds the values of all wires on vector `k`. -/
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

/-- The memory after adding the tables `ts` holds their bits `k`. -/
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

/-- Bit `k` of the table of the output wire is the output of the circuit on vector `k`. -/
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

/-- The table, over the vector numbers below `2 ^ n`, of binary digit `b` of the vector number. -/
def varTab : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, b =>
    if b = n then (2 ^ 2 ^ n - 1) <<< 2 ^ n else varTab n b ||| varTab n b <<< 2 ^ n

/-- Bit `k` of `varTab n b` is binary digit `b` of `k`, for `k < 2 ^ n` and `b < n`. -/
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

/-- The number with the binary digits `bs`, least significant digit first. -/
def idxL : List Bool → ℕ
  | [] => 0
  | b :: bs => Nat.bit b (idxL bs)

/-- A number with `bs.length` binary digits is below `2 ^ bs.length`. -/
theorem idxL_lt : ∀ bs : List Bool, idxL bs < 2 ^ bs.length := by
  intro bs
  induction bs with
  | nil => simp [idxL]
  | cons b bs ih =>
    have h2 : 2 ^ (bs.length + 1) = 2 ^ bs.length + 2 ^ bs.length := by ring
    rw [idxL, List.length_cons, Nat.bit_val]
    cases b <;> simp <;> omega

/-- The binary digits of `idxL bs` are `bs`. -/
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

/-- The value of an OR of ANDs of wires, bracketed to the left, on the wire values `w`. -/
def dnfVal (w : List Bool) (terms : List (List ℕ)) : Bool :=
  terms.foldl (fun acc t => acc || t.foldl (fun a i => a && w.getD i false) true) false

/-- The table of an OR of ANDs of wires, from the tables `ts` of the wires. -/
def dnfTab (M : ℕ) (ts : List ℕ) (terms : List (List ℕ)) : ℕ :=
  terms.foldl (fun acc t => acc ||| t.foldl (fun a i => a &&& ts.getD i 0) M) 0

/-- Bit `k` of the table of an AND of wires. -/
theorem conj_bit (k : ℕ) (ts : List ℕ) (t : List ℕ) : ∀ a : ℕ,
    (t.foldl (fun a i => a &&& ts.getD i 0) a).testBit k
      = t.foldl (fun a i => a && (ts.map fun t => t.testBit k).getD i false) (a.testBit k) := by
  induction t with
  | nil => intro a; rfl
  | cons i t ih =>
    intro a
    rw [List.foldl_cons, List.foldl_cons, ih, Nat.testBit_and, getD_bit]

/-- Bit `k` of the table of an OR of ANDs of wires is its value on the bits `k` of the tables. -/
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

/-- The tables of the `n` input wires on all `2 ^ n` inputs: the input with number `k` has the
binary digits of `k`, wire `0` being the least significant digit. -/
def inTabs (n : ℕ) : List ℕ := (List.range n).map (varTab n)

/-- Bit `idxL bs` of the input tables is the input `bs`. -/
theorem inTabs_bit (bs : List Bool) :
    (inTabs bs.length).map (fun t => t.testBit (idxL bs)) = bs := by
  unfold inTabs
  rw [List.map_map]
  conv_rhs => rw [← range_bits bs]
  apply List.map_congr_left
  intro b hb
  simp [varTab_bit, idxL_lt bs, List.mem_range.mp hb]

/-- The computation behind `sound_dnf`: every gate reads at most two wires, and the output table
is the table of the OR of ANDs `terms`, complemented when `neg` is set. -/
def checkDnf (n : ℕ) (code : List (ℕ × List ℕ)) (out : ℕ) (neg : Bool)
    (terms : List (List ℕ)) : Bool :=
  (code.all fun c => Nat.ble c.2.length 2) &&
    Nat.beq (outT (2 ^ 2 ^ n - 1) (2 ^ n) code out (inTabs n))
      (bif neg then (2 ^ 2 ^ n - 1) ^^^ dnfTab (2 ^ 2 ^ n - 1) (inTabs n) terms
        else dnfTab (2 ^ 2 ^ n - 1) (inTabs n) terms)

/-- If the check passes, the circuit with gate codes `code` computes the OR of ANDs `terms`
(its negation when `neg` is set), so that function has a circuit with at most `s` gates. -/
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

end PEqualNP.Outside.L_meta_17731_aux

theorem PEqualNP.Outside.L_meta_17731 : PEqualNP.MetaComplexity.HasCircuitSize 15 (fun x : Fin 15 → Bool => !((x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 7 && x 9 && x 13 && x 14) || (x 0 && x 2 && x 4 && x 6 && x 8 && x 13) || (x 2 && x 3 && x 4 && x 5 && x 6 && x 7 && x 9 && x 11 && x 12 && x 13) || (x 0 && x 3 && x 4 && x 5 && x 7 && x 9 && x 10 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 5 && x 6 && x 7 && x 9 && x 10 && x 11 && x 14) || (x 0 && x 1 && x 2 && x 6 && x 7 && x 9 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 3 && x 7 && x 8 && x 9 && x 10 && x 12 && x 13 && x 14) || (x 1 && x 3 && x 4 && x 5 && x 6 && x 7 && x 9 && x 10 && x 11 && x 13) || (x 0 && x 3 && x 4 && x 6 && x 7 && x 9 && x 10 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 6 && x 9 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 1 && x 4 && x 5 && x 7 && x 9 && x 10 && x 11 && x 12 && x 13) || (x 2 && x 3 && x 4 && x 5 && x 6 && x 8 && x 9 && x 10 && x 12 && x 13) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 6 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 4 && x 6 && x 8 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 2 && x 3 && x 7 && x 8 && x 9 && x 10 && x 11 && x 12 && x 14) || (x 1 && x 2 && x 3 && x 5 && x 7 && x 8 && x 9 && x 10 && x 11 && x 13) || (x 0 && x 1 && x 3 && x 6 && x 7 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 5 && x 7 && x 8 && x 9 && x 10 && x 11 && x 12) || (x 0 && x 1 && x 2 && x 5 && x 8 && x 9 && x 10 && x 11 && x 12 && x 14) || (x 0 && x 2 && x 4 && x 7 && x 8 && x 9 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 5 && x 6 && x 7 && x 8 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 8 && x 9 && x 10 && x 11 && x 12 && x 13) || (x 1 && x 2 && x 4 && x 6 && x 7 && x 8 && x 9 && x 10 && x 12 && x 13) || (x 2 && x 3 && x 4 && x 5 && x 7 && x 8 && x 9 && x 10 && x 12 && x 14) || (x 0 && x 2 && x 3 && x 5 && x 6 && x 9 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 6 && x 7 && x 9 && x 11 && x 14) || (x 0 && x 1 && x 2 && x 5 && x 6 && x 7 && x 8 && x 10 && x 13 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 7 && x 10) || (x 0 && x 3 && x 4 && x 6 && x 8 && x 9 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 6 && x 7 && x 10 && x 11 && x 13) || (x 9 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 2 && x 3 && x 4 && x 5 && x 6 && x 7 && x 10 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 2 && x 5 && x 6 && x 9) || (x 2 && x 3 && x 4 && x 5 && x 7 && x 8 && x 9 && x 11 && x 13 && x 14) || (x 1 && x 2 && x 3 && x 5 && x 7 && x 8 && x 10 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 8 && x 9 && x 12 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 7 && x 8 && x 9 && x 10 && x 13) || (x 0 && x 1 && x 4 && x 5 && x 6 && x 7 && x 8 && x 10 && x 12 && x 13) || (x 0 && x 2 && x 4 && x 6 && x 7 && x 9 && x 10 && x 11 && x 12 && x 13) || (x 1 && x 3 && x 4 && x 5 && x 6 && x 7 && x 10 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 5 && x 7 && x 8 && x 11 && x 12 && x 13 && x 14) || (x 1 && x 3 && x 4 && x 6 && x 7 && x 8 && x 9 && x 11 && x 13 && x 14) || (x 0 && x 2 && x 4 && x 5 && x 8 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 1 && x 3 && x 4 && x 5 && x 6 && x 8 && x 9 && x 10 && x 11 && x 12) || (x 0 && x 3 && x 4 && x 7 && x 8 && x 14) || (x 1 && x 2 && x 3 && x 6 && x 7 && x 8 && x 10 && x 11 && x 12 && x 14) || (x 2 && x 3 && x 4 && x 5 && x 6 && x 8 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 7 && x 8 && x 9 && x 11 && x 12) || (x 0 && x 2 && x 3 && x 6 && x 7 && x 12) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 8 && x 10 && x 12 && x 13) || (x 1 && x 3 && x 4 && x 5 && x 6 && x 8 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 6 && x 7 && x 8 && x 11 && x 12 && x 13) || (x 1 && x 3 && x 4 && x 6 && x 7 && x 8 && x 9 && x 10 && x 12 && x 14) || (x 0 && x 3 && x 4 && x 5 && x 6 && x 7 && x 8 && x 9 && x 10 && x 13) || (x 0 && x 2 && x 4 && x 5 && x 6 && x 7 && x 8 && x 10 && x 11 && x 12) || (x 0 && x 2 && x 4 && x 5 && x 6 && x 7 && x 8 && x 9 && x 10 && x 14) || (x 0 && x 1 && x 2 && x 6 && x 8 && x 9 && x 10 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 4 && x 5 && x 6 && x 9 && x 10 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 7 && x 11 && x 12 && x 13) || (x 1 && x 2 && x 3 && x 5 && x 6 && x 8 && x 9 && x 10 && x 11 && x 14) || (x 0 && x 1 && x 4 && x 5 && x 8 && x 11) || (x 1 && x 2 && x 3 && x 9 && x 10 && x 12) || (x 0 && x 1 && x 4 && x 7 && x 8 && x 9 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 6 && x 8 && x 9 && x 10 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 6 && x 8 && x 10 && x 11 && x 12) || (x 0 && x 2 && x 3 && x 5 && x 6 && x 7 && x 8 && x 10 && x 11 && x 13) || (x 0 && x 1 && x 2 && x 5 && x 7 && x 9 && x 10 && x 11 && x 13 && x 14) || (x 5 && x 7 && x 8 && x 10 && x 11 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 6 && x 7 && x 8 && x 9 && x 13 && x 14) || (x 2 && x 3 && x 4 && x 12 && x 13 && x 14) || (x 6 && x 7 && x 8 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 6 && x 7 && x 8 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 2 && x 3 && x 5 && x 7 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 5 && x 6 && x 8 && x 9 && x 11 && x 13) || (x 0 && x 2 && x 3 && x 5 && x 6 && x 7 && x 8 && x 9 && x 11 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 6 && x 10 && x 13 && x 14) || (x 1 && x 2 && x 3 && x 6 && x 7 && x 8 && x 9 && x 11 && x 12 && x 13) || (x 1 && x 3 && x 4 && x 10 && x 11 && x 14) || (x 0 && x 2 && x 3 && x 6 && x 8 && x 9 && x 10 && x 11 && x 12 && x 13) || (x 1 && x 2 && x 4 && x 9 && x 11 && x 13) || (x 5 && x 6 && x 7 && x 9 && x 10 && x 12) || (x 0 && x 3 && x 4 && x 5 && x 6 && x 7 && x 8 && x 9 && x 11 && x 12) || (x 1 && x 2 && x 3 && x 5 && x 6 && x 8 && x 9 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 4 && x 5 && x 6 && x 7 && x 8 && x 9 && x 12 && x 14) || (x 0 && x 3 && x 4 && x 5 && x 8 && x 9 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 2 && x 4 && x 5 && x 6 && x 9 && x 10 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 5 && x 6 && x 7 && x 9 && x 12 && x 13 && x 14))) 220 := by
  refine PEqualNP.Outside.L_meta_17731_aux.sound_dnf 15 [(1, [0, 2]), (1, [1, 14]), (1, [3, 4]), (1, [10, 12]), (1, [8, 11]), (1, [6, 7]), (1, [5, 13]), (1, [9, 18]), (1, [6, 10]), (1, [2, 7]), (1, [8, 13]), (1, [1, 4]), (1, [6, 9]), (1, [1, 3]), (1, [11, 13]), (1, [0, 7]), (1, [12, 20]), (1, [5, 19]), (1, [14, 17]), (1, [8, 9]), (1, [2, 12]), (1, [0, 12]), (1, [9, 29]), (1, [5, 27]), (1, [2, 10]), (1, [11, 26]), (1, [6, 15]), (1, [0, 10]), (1, [3, 30]), (1, [10, 28]), (1, [3, 35]), (1, [7, 10]), (1, [11, 14]), (1, [3, 6]), (1, [4, 8]), (1, [4, 13]), (1, [4, 5]), (1, [0, 9]), (1, [13, 36]), (1, [2, 5]), (1, [32, 46]), (1, [12, 21]), (1, [8, 24]), (1, [25, 31]), (1, [7, 34]), (1, [22, 29]), (0, [41, 52]), (0, [53, 61]), (0, [54, 62]), (0, [38, 63]), (0, [55, 64]), (0, [56, 65]), (0, [57, 66]), (0, [58, 67]), (0, [59, 68]), (0, [60, 69]), (1, [14, 70]), (1, [15, 38]), (1, [5, 36]), (1, [0, 21]), (1, [9, 24]), (1, [2, 34]), (1, [6, 25]), (1, [7, 13]), (1, [8, 12]), (0, [72, 73]), (0, [74, 80]), (0, [75, 81]), (0, [76, 82]), (0, [31, 83]), (0, [77, 84]), (0, [78, 85]), (0, [79, 86]), (1, [1, 87]), (1, [25, 41]), (1, [0, 34]), (1, [2, 21]), (1, [7, 9]), (0, [89, 90]), (0, [91, 93]), (0, [38, 94]), (0, [31, 95]), (0, [23, 96]), (0, [92, 97]), (0, [22, 98]), (1, [4, 99]), (1, [33, 44]), (0, [41, 43]), (0, [36, 102]), (0, [101, 103]), (0, [45, 104]), (0, [24, 105]), (0, [48, 106]), (0, [31, 107]), (1, [11, 108]), (1, [30, 33]), (1, [7, 16]), (0, [44, 110]), (0, [111, 112]), (0, [45, 113]), (0, [39, 114]), (0, [22, 115]), (1, [8, 116]), (1, [30, 44]), (1, [0, 16]), (1, [10, 24]), (1, [20, 22]), (0, [118, 119]), (0, [45, 122]), (0, [120, 123]), (0, [121, 124]), (0, [33, 125]), (1, [5, 126]), (1, [15, 31]), (0, [38, 128]), (0, [32, 129]), (0, [21, 130]), (0, [34, 131]), (0, [37, 132]), (1, [3, 133]), (1, [12, 16]), (1, [33, 35]), (0, [42, 43]), (0, [44, 137]), (0, [135, 138]), (0, [136, 139]), (1, [13, 140]), (1, [22, 28]), (1, [26, 37]), (1, [9, 16]), (0, [142, 143]), (0, [144, 145]), (0, [32, 146]), (1, [2, 147]), (0, [15, 28]), (0, [25, 149]), (0, [47, 150]), (1, [23, 151]), (0, [40, 51]), (0, [32, 153]), (1, [12, 154]), (0, [16, 40]), (0, [33, 156]), (1, [6, 157]), (1, [26, 32]), (0, [22, 159]), (0, [37, 160]), (1, [0, 161]), (0, [47, 49]), (1, [42, 163]), (0, [47, 50]), (1, [39, 165]), (0, [37, 40]), (1, [7, 167]), (0, [21, 51]), (1, [46, 169]), (0, [33, 43]), (1, [9, 171]), (1, [36, 49]), (1, [19, 21]), (1, [27, 174]), (1, [24, 50]), (1, [25, 48]), (0, [173, 175]), (0, [176, 178]), (0, [177, 179]), (0, [172, 180]), (0, [170, 181]), (0, [168, 182]), (0, [166, 183]), (0, [164, 184]), (0, [162, 185]), (0, [158, 186]), (0, [155, 187]), (0, [152, 188]), (0, [148, 189]), (0, [141, 190]), (0, [134, 191]), (0, [127, 192]), (0, [117, 193]), (0, [109, 194]), (0, [100, 195]), (0, [88, 196]), (0, [71, 197]), (2, [198])] 199 true [[0, 1, 2, 3, 4, 5, 7, 9, 13, 14], [0, 2, 4, 6, 8, 13], [2, 3, 4, 5, 6, 7, 9, 11, 12, 13], [0, 3, 4, 5, 7, 9, 10, 12, 13, 14], [1, 2, 4, 5, 6, 7, 9, 10, 11, 14], [0, 1, 2, 6, 7, 9, 11, 12, 13, 14], [0, 1, 3, 7, 8, 9, 10, 12, 13, 14], [1, 3, 4, 5, 6, 7, 9, 10, 11, 13], [0, 3, 4, 6, 7, 9, 10, 11, 12, 14], [0, 1, 3, 5, 6, 9, 10, 11, 13, 14], [0, 1, 4, 5, 7, 9, 10, 11, 12, 13], [2, 3, 4, 5, 6, 8, 9, 10, 12, 13], [0, 1, 2, 3, 4, 5, 6, 11, 12, 14], [0, 1, 4, 6, 8, 10, 11, 12, 13, 14], [0, 2, 3, 7, 8, 9, 10, 11, 12, 14], [1, 2, 3, 5, 7, 8, 9, 10, 11, 13], [0, 1, 3, 6, 7, 10, 11, 12, 13, 14], [1, 2, 4, 5, 7, 8, 9, 10, 11, 12], [0, 1, 2, 5, 8, 9, 10, 11, 12, 14], [0, 2, 4, 7, 8, 9, 10, 11, 13, 14], [0, 1, 2, 5, 6, 7, 8, 11, 12, 14], [0, 1, 3, 5, 8, 9, 10, 11, 12, 13], [1, 2, 4, 6, 7, 8, 9, 10, 12, 13], [2, 3, 4, 5, 7, 8, 9, 10, 12, 14], [0, 2, 3, 5, 6, 9, 11, 12, 13, 14], [0, 1, 2, 3, 4, 6, 7, 9, 11, 14], [0, 1, 2, 5, 6, 7, 8, 10, 13, 14], [0, 1, 3, 5, 7, 10], [0, 3, 4, 6, 8, 9, 10, 11, 13, 14], [0, 1, 2, 3, 4, 6, 7, 10, 11, 13], [9, 10, 11, 12, 13, 14], [2, 3, 4, 5, 6, 7, 10, 11, 12, 14], [0, 1, 2, 5, 6, 9], [2, 3, 4, 5, 7, 8, 9, 11, 13, 14], [1, 2, 3, 5, 7, 8, 10, 12, 13, 14], [0, 1, 2, 3, 4, 5, 8, 9, 12, 14], [0, 1, 2, 3, 4, 7, 8, 9, 10, 13], [0, 1, 4, 5, 6, 7, 8, 10, 12, 13], [0, 2, 4, 6, 7, 9, 10, 11, 12, 13], [1, 3, 4, 5, 6, 7, 10, 12, 13, 14], [1, 2, 4, 5, 7, 8, 11, 12, 13, 14], [1, 3, 4, 6, 7, 8, 9, 11, 13, 14], [0, 2, 4, 5, 8, 10, 11, 12, 13, 14], [1, 3, 4, 5, 6, 8, 9, 10, 11, 12], [0, 3, 4, 7, 8, 14], [1, 2, 3, 6, 7, 8, 10, 11, 12, 14], [2, 3, 4, 5, 6, 8, 10, 11, 13, 14], [0, 1, 2, 3, 4, 7, 8, 9, 11, 12], [0, 2, 3, 6, 7, 12], [0, 1, 2, 3, 4, 5, 8, 10, 12, 13], [1, 3, 4, 5, 6, 8, 11, 12, 13, 14], [0, 1, 3, 5, 6, 7, 8, 11, 12, 13], [1, 3, 4, 6, 7, 8, 9, 10, 12, 14], [0, 3, 4, 5, 6, 7, 8, 9, 10, 13], [0, 2, 4, 5, 6, 7, 8, 10, 11, 12], [0, 2, 4, 5, 6, 7, 8, 9, 10, 14], [0, 1, 2, 6, 8, 9, 10, 12, 13, 14], [0, 1, 4, 5, 6, 9, 10, 11, 12, 14], [0, 1, 2, 3, 4, 5, 7, 11, 12, 13], [1, 2, 3, 5, 6, 8, 9, 10, 11, 14], [0, 1, 4, 5, 8, 11], [1, 2, 3, 9, 10, 12], [0, 1, 4, 7, 8, 9, 11, 12, 13, 14], [0, 1, 2, 3, 4, 6, 8, 9, 10, 14], [0, 1, 2, 3, 4, 6, 8, 10, 11, 12], [0, 2, 3, 5, 6, 7, 8, 10, 11, 13], [0, 1, 2, 5, 7, 9, 10, 11, 13, 14], [5, 7, 8, 10, 11, 14], [0, 1, 3, 5, 6, 7, 8, 9, 13, 14], [2, 3, 4, 12, 13, 14], [6, 7, 8, 12, 13, 14], [1, 2, 4, 6, 7, 8, 10, 11, 13, 14], [0, 2, 3, 5, 7, 10, 11, 12, 13, 14], [5, 6, 8, 9, 11, 13], [0, 2, 3, 5, 6, 7, 8, 9, 11, 14], [0, 1, 2, 3, 4, 5, 6, 10, 13, 14], [1, 2, 3, 6, 7, 8, 9, 11, 12, 13], [1, 3, 4, 10, 11, 14], [0, 2, 3, 6, 8, 9, 10, 11, 12, 13], [1, 2, 4, 9, 11, 13], [5, 6, 7, 9, 10, 12], [0, 3, 4, 5, 6, 7, 8, 9, 11, 12], [1, 2, 3, 5, 6, 8, 9, 12, 13, 14], [0, 1, 4, 5, 6, 7, 8, 9, 12, 14], [0, 3, 4, 5, 8, 9, 11, 12, 13, 14], [0, 2, 4, 5, 6, 9, 10, 12, 13, 14], [1, 2, 4, 5, 6, 7, 9, 12, 13, 14]] 220 _ (fun _ => rfl) ?_ ?_
  · decide +kernel
  · decide +kernel
