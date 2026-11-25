import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9502

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def rawGate (g : Bool × Nat × Nat) : Gate :=
  ⟨if g.1 then .and else .or, [g.2.1, g.2.2]⟩

def rowStep {n : Nat} (w : List (BitVec n)) (g : Bool × Nat × Nat) : List (BitVec n) :=
  w ++ [if g.1 then w.getD g.2.1 0 &&& w.getD g.2.2 0
    else w.getD g.2.1 0 ||| w.getD g.2.2 0]

def rowBits {n : Nat} (b : Nat) (w : List (BitVec n)) : List Bool :=
  w.map (fun v => v.getLsbD b)

lemma bits_getD {n : Nat} (b i : Nat) (w : List (BitVec n)) :
    (w.map (fun v => v.getLsbD b)).getD i false = (w.getD i 0).getLsbD b := by
  induction w generalizing i with
  | nil => simp
  | cons v w ih =>
    cases i with
    | zero => simp
    | succ i => simpa using ih i

lemma row_step_sound {n : Nat} (b : Nat) (w : List (BitVec n))
    (g : Bool × Nat × Nat) :
    rowBits b (rowStep w g) =
      rowBits b w ++ [(rawGate g).op.eval
        ((rawGate g).inputs.map (fun i => (rowBits b w).getD i false))] := by
  rcases g with ⟨op, a, c⟩
  cases op <;> simp [rowStep, rowBits, rawGate, GateOp.eval] <;>
    cases ha : w[a]? <;> cases hc : w[c]? <;> simp_all

lemma row_run_sound {n : Nat} (b : Nat) (gs : List (Bool × Nat × Nat))
    (w : List (BitVec n)) :
    rowBits b (gs.foldl rowStep w) =
      (gs.map rawGate).foldl
        (fun v g => v ++ [g.op.eval (g.inputs.map (fun i => v.getD i false))])
        (rowBits b w) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons, List.map_cons]
    rw [ih, row_step_sound]

def rowInput (a : Fin 33) : List (BitVec 33) :=
  List.ofFn (fun i : Fin 33 => if i = a then BitVec.allOnes 33 else 0) ++
    List.ofFn (fun i : Fin 33 => BitVec.ofNat 33 (2 ^ i.val))

lemma row_input_sound (a b : Fin 33) :
    rowBits b.val (rowInput a) = oneEach a b := by
  simp only [rowBits, rowInput, oneEach, List.map_append, List.map_ofFn]
  congr 1
  · apply congrArg List.ofFn
    funext i
    simp only [Function.comp_apply]
    by_cases h : i = a
    · simp only [h, ite_true, decide_true]
      rw [BitVec.getLsbD_allOnes]
      simp [b.isLt]
    · simp [h]
  · apply congrArg List.ofFn
    funext i
    simp only [Function.comp_apply]
    rw [BitVec.getLsbD_ofNat]
    simp [b.isLt, Nat.testBit_two_pow, Fin.ext_iff]

lemma row_circuit_sound (gs : List (Bool × Nat × Nat)) (out : Nat) (a b : Fin 33) :
    (Circuit.mk (gs.map rawGate) out).eval (oneEach a b) =
      ((gs.foldl rowStep (rowInput a)).getD out 0).getLsbD b.val := by
  rw [← bits_getD]
  change _ = (rowBits b.val (gs.foldl rowStep (rowInput a))).getD out false
  rw [row_run_sound, row_input_sound]
  rfl


def adjGraph : Fin 33 → Fin 33 → Bool := (fun a b : Fin 33 => decide (∃ i : Fin 11, ((a.val = i.val ∨ a.val = 11 + i.val) ∧ (b.val = (i.val + 1) % 11 ∨ b.val = 22 + i.val)) ∨ ((b.val = i.val ∨ b.val = 11 + i.val) ∧ (a.val = (i.val + 1) % 11 ∨ a.val = 22 + i.val))))

def adjRows : List Nat :=
  [6292482, 8390661, 16781322, 33562644, 67125288, 134250576, 268501152, 537002304, 1074004608, 2148009216, 4296016385, 4194306, 8388612, 16777224, 33554448, 67108896, 134217792, 268435584, 536871168, 1073742336, 2147484672, 4294967297, 2049, 4098, 8196, 16392, 32784, 65568, 131136, 262272, 524544, 1049088, 2098176]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma adjRows_correct : ∀ a b : Fin 33,
    (BitVec.ofNat 33 (adjRows.getD a.val 0)).getLsbD b.val = adjGraph a b := by
  decide +kernel


def rawGates : List (Bool × Nat × Nat) :=
  [
    (false, 0, 33),
    (false, 1, 34),
    (false, 2, 35),
    (false, 3, 36),
    (false, 4, 37),
    (false, 5, 38),
    (false, 6, 39),
    (false, 7, 40),
    (false, 8, 41),
    (false, 9, 42),
    (false, 10, 43),
    (false, 11, 44),
    (false, 12, 45),
    (false, 13, 46),
    (false, 14, 47),
    (false, 15, 48),
    (false, 16, 49),
    (false, 17, 50),
    (false, 18, 51),
    (false, 19, 52),
    (false, 20, 53),
    (false, 21, 54),
    (false, 22, 55),
    (false, 23, 56),
    (false, 24, 57),
    (false, 25, 58),
    (false, 26, 59),
    (false, 27, 60),
    (false, 28, 61),
    (false, 29, 62),
    (false, 30, 63),
    (false, 31, 64),
    (false, 32, 65),
    (false, 66, 77),
    (false, 67, 88),
    (true, 99, 100),
    (false, 67, 78),
    (false, 68, 89),
    (true, 102, 103),
    (false, 68, 79),
    (false, 69, 90),
    (true, 105, 106),
    (false, 69, 80),
    (false, 70, 91),
    (true, 108, 109),
    (false, 70, 81),
    (false, 71, 92),
    (true, 111, 112),
    (false, 71, 82),
    (false, 72, 93),
    (true, 114, 115),
    (false, 72, 83),
    (false, 73, 94),
    (true, 117, 118),
    (false, 73, 84),
    (false, 74, 95),
    (true, 120, 121),
    (false, 74, 85),
    (false, 75, 96),
    (true, 123, 124),
    (false, 75, 86),
    (false, 76, 97),
    (true, 126, 127),
    (false, 76, 87),
    (false, 66, 98),
    (true, 129, 130),
    (false, 101, 104),
    (false, 132, 107),
    (false, 133, 110),
    (false, 134, 113),
    (false, 135, 116),
    (false, 136, 119),
    (false, 137, 122),
    (false, 138, 125),
    (false, 139, 128),
    (false, 140, 131)
  ]

def circ : Circuit := ⟨rawGates.map rawGate, 141⟩

lemma circ_mono : Monotone2 circ := by
  simp [Monotone2, circ, rawGates, rawGate]

lemma circ_size : circ.size ≤ 76 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma row_eval : ∀ a : Fin 33,
    ((rawGates.foldl rowStep (rowInput a)).getD 141 0) =
      BitVec.ofNat 33 (adjRows.getD a.val 0) := by
  decide +kernel

lemma circ_rep : Represents adjGraph circ := by
  intro a b
  change (Circuit.mk (rawGates.map rawGate) 141).eval (oneEach a b) = _
  rw [row_circuit_sound, row_eval, adjRows_correct]

lemma baseline : RepSizeAtMost adjGraph 76 :=
  ⟨circ, circ_mono, circ_size, circ_rep⟩

end PEqualNP.Outside.L_meta_9502
