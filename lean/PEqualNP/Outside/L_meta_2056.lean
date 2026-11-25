import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2056_aux.PackedChunks

open PEqualNP.CircuitLowerBounds

def packedOp {w : Nat} (op : GateOp) (xs : List (BitVec w)) : BitVec w :=
  match op with
  | .and => xs.foldr (fun a b => a &&& b) (BitVec.allOnes w)
  | .or => xs.foldr (fun a b => a ||| b) 0
  | _ => 0

def packedStep {w : Nat} (xs : List (BitVec w)) (g : Gate) : List (BitVec w) :=
  xs ++ [packedOp g.op (g.inputs.map fun k => xs.getD k 0)]

def packedWires {w : Nat} (C : Circuit) (xs : List (BitVec w)) : List (BitVec w) :=
  C.gates.foldl packedStep xs

def packedEval {w : Nat} (C : Circuit) (xs : List (BitVec w)) : BitVec w :=
  (packedWires C xs).getD C.output 0

lemma read_and {w : Nat} (i : Fin w) (xs : List (BitVec w)) :
    (xs.foldr (fun a b => a &&& b) (BitVec.allOnes w)).getLsbD i =
      (xs.map fun x => x.getLsbD i).all id := by
  induction xs with
  | nil => simp [i.isLt]
  | cons x xs ih =>
    simp only [List.foldr_cons, BitVec.getLsbD_and, List.map_cons, List.all_cons, ih, id_eq]

lemma read_or {w : Nat} (i : Fin w) (xs : List (BitVec w)) :
    (xs.foldr (fun a b => a ||| b) 0).getLsbD i =
      (xs.map fun x => x.getLsbD i).any id := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldr_cons, BitVec.getLsbD_or, List.map_cons, List.any_cons, ih, id_eq]

lemma read_op {w : Nat} (i : Fin w) (op : GateOp)
    (h : op = .and ∨ op = .or) (xs : List (BitVec w)) :
    (packedOp op xs).getLsbD i = op.eval (xs.map fun x => x.getLsbD i) := by
  rcases h with rfl | rfl
  · exact read_and i xs
  · exact read_or i xs

lemma read_getD {w : Nat} (i : Fin w) (xs : List (BitVec w)) (k : Nat) :
    (xs.getD k 0).getLsbD i = (xs.map fun x => x.getLsbD i).getD k false := by
  induction xs generalizing k with
  | nil => simp
  | cons x xs ih =>
    cases k with
    | zero => rfl
    | succ k => simpa using ih k

lemma read_step {w : Nat} (i : Fin w) (xs : List (BitVec w)) (g : Gate)
    (h : g.op = .and ∨ g.op = .or) :
    (packedStep xs g).map (fun x => x.getLsbD i) =
      (xs.map fun x => x.getLsbD i) ++
        [g.op.eval (g.inputs.map fun k =>
          (xs.map fun x => x.getLsbD i).getD k false)] := by
  simp only [packedStep, List.map_append, List.map_cons, List.map_nil]
  rw [read_op i g.op h]
  simp only [List.map_map, Function.comp_def, read_getD]

lemma read_fold {w : Nat} (i : Fin w) (gs : List Gate)
    (h : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) (xs : List (BitVec w)) :
    (gs.foldl packedStep xs).map (fun x => x.getLsbD i) =
      gs.foldl (fun acc g => acc ++
        [g.op.eval (g.inputs.map fun k => acc.getD k false)])
        (xs.map fun x => x.getLsbD i) := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, List.foldl_cons,
      ih (fun g hg => h g (List.mem_cons_of_mem _ hg)),
      read_step i xs g (h g List.mem_cons_self)]

lemma packed_sound {w : Nat} (i : Fin w) (C : Circuit)
    (h : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or)
    (xs : List (BitVec w)) :
    (packedEval C xs).getLsbD i = C.eval (xs.map fun x => x.getLsbD i) := by
  unfold packedEval packedWires Circuit.eval Circuit.wires
  rw [read_getD, read_fold i C.gates h]

def tilePow {w : Nat} (x : BitVec w) : (k : Nat) → BitVec (w * 2 ^ k)
  | 0 => x.cast (by simp)
  | k + 1 =>
    let y := tilePow x k
    (y ++ y).cast (by simp [Nat.pow_succ, Nat.mul_two, Nat.mul_add])

lemma tilePow_read {w : Nat} (x : BitVec w) (k r : Nat) :
    (tilePow x k).getLsbD r =
      (decide (r < w * 2 ^ k) && x.getLsbD (r % w)) := by
  induction k generalizing r with
  | zero =>
    simp only [tilePow, BitVec.getLsbD_cast, Nat.pow_zero, Nat.mul_one]
    by_cases h : r < w
    · simp [h, Nat.mod_eq_of_lt h]
    · simp only [h, decide_false, Bool.false_and]
      exact BitVec.getLsbD_of_ge (x := x) (i := r) (ge := Nat.le_of_not_gt h)
  | succ k ih =>
    simp only [tilePow, BitVec.getLsbD_cast, BitVec.getLsbD_append]
    have width : w * 2 ^ (k + 1) = w * 2 ^ k + w * 2 ^ k := by
      simp [Nat.pow_succ, Nat.mul_two, Nat.mul_add]
    rw [width]
    by_cases h : r < w * 2 ^ k
    · rw [if_pos h, ih]
      simp only [h, decide_true, Bool.true_and,
        show r < w * 2 ^ k + w * 2 ^ k by omega]
    · simp only [h, ↓reduceIte, ih]
      have hm : (r - w * 2 ^ k) % w = r % w := by
        have he : r = w * 2 ^ k + (r - w * 2 ^ k) := by omega
        conv_rhs => rw [he]
        simp [Nat.add_mod]
      rw [hm]
      have he : (r - w * 2 ^ k < w * 2 ^ k) ↔
          (r < w * 2 ^ k + w * 2 ^ k) := by omega
      simp [he]

def pointPattern (n : Nat) (i : Fin n) : BitVec (2 ^ n) :=
  (tilePow ((BitVec.allOnes (2 ^ i.val)) ++ (0 : BitVec (2 ^ i.val)))
    (n - (i.val + 1))).cast (by
      have e : i.val + 1 + (n - (i.val + 1)) = n := by omega
      rw [show 2 ^ i.val + 2 ^ i.val = 2 ^ (i.val + 1) by
        simp [Nat.pow_succ]; omega, ← Nat.pow_add, e])

lemma halfPattern_read (i r : Nat) (hr : r < 2 ^ (i + 1)) :
    ((BitVec.allOnes (2 ^ i)) ++ (0 : BitVec (2 ^ i))).getLsbD r =
      r.testBit i := by
  rw [BitVec.getLsbD_append]
  by_cases h : r < 2 ^ i
  · rw [if_pos h, Nat.testBit_lt_two_pow h]
    simp
  · rw [if_neg h, BitVec.getLsbD_allOnes]
    have small : r - 2 ^ i < 2 ^ i := by
      rw [Nat.pow_succ] at hr
      omega
    have er : r = 2 ^ i + (r - 2 ^ i) := by omega
    conv_rhs => rw [er, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow small]
    simp only [small, decide_true, Bool.not_false]

lemma pointPattern_read (n : Nat) (i : Fin n) (r : Fin (2 ^ n)) :
    (pointPattern n i).getLsbD r = r.val.testBit i.val := by
  simp only [pointPattern, BitVec.getLsbD_cast, tilePow_read]
  have e : i.val + 1 + (n - (i.val + 1)) = n := by omega
  have width : (2 ^ i.val + 2 ^ i.val) * 2 ^ (n - (i.val + 1)) = 2 ^ n := by
    rw [show 2 ^ i.val + 2 ^ i.val = 2 ^ (i.val + 1) by
      simp [Nat.pow_succ]; omega, ← Nat.pow_add, e]
  rw [width]
  simp only [r.isLt, decide_true, Bool.true_and]
  have block : 2 ^ i.val + 2 ^ i.val = 2 ^ (i.val + 1) := by
    simp [Nat.pow_succ]; omega
  have modulus : r.val % (2 ^ i.val + 2 ^ i.val) = r.val % 2 ^ (i.val + 1) :=
    congrArg (fun z => r.val % z) block
  rw [modulus, halfPattern_read i.val _ (Nat.mod_lt _ (Nat.two_pow_pos _))]
  simp only [Nat.testBit_mod_two_pow, Nat.lt_succ_self, decide_true, Bool.true_and]

def packRows {w : Nat} (f : Fin w → Bool) : BitVec w :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (by simp)

lemma packRows_read {w : Nat} (f : Fin w → Bool) (r : Fin w) :
    (packRows f).getLsbD r = f r := by
  simp only [packRows, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos r.isLt, Option.getD_some]

def rowPatterns {n w : Nat} (rows : Fin w → Fin n → Bool) : List (BitVec w) :=
  List.ofFn fun p => packRows (fun r => rows r p)

lemma rowPatterns_read {n w : Nat} (rows : Fin w → Fin n → Bool) (r : Fin w) :
    (rowPatterns rows).map (fun x => x.getLsbD r) = List.ofFn (rows r) := by
  simp only [rowPatterns, List.map_ofFn, Function.comp_def, packRows_read]

lemma rows_true_of_allOnes {n w : Nat} (rows : Fin w → Fin n → Bool) (C : Circuit)
    (mono : PEqualNP.MetaComplexity.Monotone2 C)
    (checked : packedEval C (rowPatterns rows) = BitVec.allOnes w) :
    ∀ r, C.eval (List.ofFn (rows r)) = true := by
  intro r
  have h := packed_sound r C (fun g hg => (mono g hg).1) (rowPatterns rows)
  rw [checked, rowPatterns_read] at h
  simpa [r.isLt] using h.symm

def incident (p l : Fin 13) : Prop := (p.val + l.val) % 13 ∈ ([0,1,3,9] : List Nat)

instance : DecidableRel incident := fun p l => inferInstanceAs
  (Decidable ((p.val + l.val) % 13 ∈ ([0,1,3,9] : List Nat)))

def positivePairs : List (Fin 13 × Fin 13) :=
  [(0,0), (0,1), (0,3), (0,9), (1,0), (1,2), (1,8), (1,12), (2,1), (2,7), (2,11), (2,12), (3,0), (3,6), (3,10), (3,11), (4,5), (4,9), (4,10), (4,12), (5,4), (5,8), (5,9), (5,11), (6,3), (6,7), (6,8), (6,10), (7,2), (7,6), (7,7), (7,9), (8,1), (8,5), (8,6), (8,8), (9,0), (9,4), (9,5), (9,7), (10,3), (10,4), (10,6), (10,12), (11,2), (11,3), (11,5), (11,11), (12,1), (12,2), (12,4), (12,10)]

def positiveRows (r : Fin 52) (i : Fin 26) : Bool :=
  let e := positivePairs.getD r.val (0,0)
  decide (i.val = e.1.val ∨ i.val = 13 + e.2.val)

lemma listed_positive : ∀ p l : Fin 13, incident p l →
    ∃ r : Fin 52, positivePairs.getD r.val (0,0) = (p,l) := by
  decide +kernel

lemma represent_subset {n : Nat} (s : Fin n → Bool) :
    ∃ r : Fin (2 ^ n), ∀ p : Fin n, r.val.testBit p.val = s p := by
  let b : BitVec n := (BitVec.ofBoolListLE (List.ofFn s)).cast (by simp)
  refine ⟨b.toFin, ?_⟩
  intro p
  change b.getLsbD p.val = s p
  simp only [b, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos p.isLt, Option.getD_some]

def chunkBits (b : Fin 16) (r : Fin 512) (p : Fin 13) : Bool :=
  if p.val < 9 then r.val.testBit p.val else b.val.testBit (p.val - 9)

def pointChunk (b : Fin 16) (p : Fin 13) : BitVec 512 :=
  if h : p.val < 9 then pointPattern 9 ⟨p.val,h⟩
  else if b.val.testBit (p.val - 9) then BitVec.allOnes 512 else 0

lemma pointChunk_read (b : Fin 16) (p : Fin 13) (r : Fin 512) :
    (pointChunk b p).getLsbD r = chunkBits b r p := by
  by_cases h : p.val < 9
  · simp only [pointChunk, dif_pos h, pointPattern_read, chunkBits, if_pos h]
  · simp only [pointChunk, dif_neg h, chunkBits, if_neg h]
    cases hb : b.val.testBit (p.val - 9) with
    | false => exact BitVec.getLsbD_zero
    | true => exact (BitVec.getLsbD_allOnes).trans (decide_eq_true r.isLt)

lemma represented_chunk (s : Fin 13 → Bool) :
    ∃ b : Fin 16, ∃ r : Fin 512, chunkBits b r = s := by
  obtain ⟨r,hr⟩ := represent_subset
    (fun p : Fin 9 => s ⟨p.val,by have := p.isLt; omega⟩)
  obtain ⟨b,hb⟩ := represent_subset
    (fun p : Fin 4 => s ⟨9 + p.val,by have := p.isLt; omega⟩)
  refine ⟨b,r,?_⟩
  funext p
  by_cases h : p.val < 9
  · have eq := hr ⟨p.val,h⟩
    simpa only [chunkBits,if_pos h] using eq
  · have high : p.val - 9 < 4 := by have := p.isLt; omega
    have eq := hb ⟨p.val - 9,high⟩
    have back : 9 + (p.val - 9) = p.val := by omega
    simpa only [chunkBits,if_neg h,back] using eq

def lineChunk (I : Fin 13 → Fin 13 → Prop) [DecidableRel I]
    (b : Fin 16) (l : Fin 13) : BitVec 512 :=
  ~~~((List.finRange 13).foldr (fun p acc =>
    if I p l then pointChunk b p ||| acc else acc) 0)

lemma lineChunk_read (I : Fin 13 → Fin 13 → Prop) [DecidableRel I]
    (b : Fin 16) (l : Fin 13) (r : Fin 512) :
    (lineChunk I b l).getLsbD r =
      decide (∀ p : Fin 13, I p l → chunkBits b r p = false) := by
  have fold_read : ∀ ps : List (Fin 13),
      (ps.foldr (fun p acc =>
        if I p l then pointChunk b p ||| acc else acc) 0).getLsbD r =
        ps.any (fun p => decide (I p l) && chunkBits b r p) := by
    intro ps
    induction ps with
    | nil => simp
    | cons p ps ih =>
      simp only [List.foldr_cons, List.any_cons]
      split_ifs with h
      · simp only [BitVec.getLsbD_or, pointChunk_read, ih, h, decide_true, Bool.true_and]
      · simp only [ih, h, decide_false, Bool.false_and, Bool.false_or]
  simp only [lineChunk, BitVec.getLsbD_not, r.isLt, decide_true, Bool.true_and, fold_read]
  apply Bool.eq_iff_iff.mpr
  simp

def closureChunk (I : Fin 13 → Fin 13 → Prop) [DecidableRel I]
    (b : Fin 16) : List (BitVec 512) :=
  List.ofFn (pointChunk b) ++ List.ofFn (lineChunk I b)

def reversedChunk (I : Fin 13 → Fin 13 → Prop) [DecidableRel I]
    (b : Fin 16) : List (BitVec 512) :=
  List.ofFn (lineChunk I b) ++ List.ofFn (pointChunk b)

lemma closureChunk_read (I : Fin 13 → Fin 13 → Prop) [DecidableRel I]
    (b : Fin 16) (r : Fin 512) :
    (closureChunk I b).map (fun x => x.getLsbD r) =
      List.ofFn (Fin.append (chunkBits b r)
        (fun l : Fin 13 => decide (∀ p : Fin 13, I p l → chunkBits b r p = false))) := by
  simp only [closureChunk, List.map_append, List.map_ofFn, Function.comp_def,
    pointChunk_read, lineChunk_read, List.ofFn_fin_append]

lemma reversedChunk_read (I : Fin 13 → Fin 13 → Prop) [DecidableRel I]
    (b : Fin 16) (r : Fin 512) :
    (reversedChunk I b).map (fun x => x.getLsbD r) =
      List.ofFn (Fin.append
        (fun l : Fin 13 => decide (∀ p : Fin 13, I p l → chunkBits b r p = false))
        (chunkBits b r)) := by
  simp only [reversedChunk, List.map_append, List.map_ofFn, Function.comp_def,
    pointChunk_read, lineChunk_read, List.ofFn_fin_append]

lemma closures_of_zero_chunks (I : Fin 13 → Fin 13 → Prop) [DecidableRel I]
    (C : Circuit) (mono : PEqualNP.MetaComplexity.Monotone2 C)
    (checked : ∀ b : Fin 16, packedEval C (closureChunk I b) = 0) :
    ∀ s : Fin 13 → Bool, C.eval (List.ofFn
      (Fin.append s (fun l : Fin 13 => decide (∀ p : Fin 13, I p l → s p = false)))) = false := by
  intro s
  obtain ⟨b,r,hr⟩ := represented_chunk s
  have h := packed_sound r C (fun g hg => (mono g hg).1) (closureChunk I b)
  rw [checked b, closureChunk_read, hr] at h
  simpa using h.symm

lemma reversed_of_zero_chunks (I : Fin 13 → Fin 13 → Prop) [DecidableRel I]
    (C : Circuit) (mono : PEqualNP.MetaComplexity.Monotone2 C)
    (checked : ∀ b : Fin 16, packedEval C (reversedChunk I b) = 0) :
    ∀ s : Fin 13 → Bool, C.eval (List.ofFn
      (Fin.append (fun l : Fin 13 => decide (∀ p : Fin 13, I p l → s p = false)) s)) = false := by
  intro s
  obtain ⟨b,r,hr⟩ := represented_chunk s
  have h := packed_sound r C (fun g hg => (mono g hg).1) (reversedChunk I b)
  rw [checked b, reversedChunk_read, hr] at h
  simpa using h.symm

def requestInput (s t : Finset (Fin 13)) (i : Fin 26) : Bool :=
  if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ s)
  else decide (Fin.ofNat 13 i.val ∈ t)

def miss (s : Finset (Fin 13)) : Finset (Fin 13) :=
  Finset.univ.filter fun l => ∀ p ∈ s, ¬ incident p l

lemma requestInput_append (s t : Finset (Fin 13)) :
    requestInput s t = Fin.append (fun p => decide (p ∈ s)) (fun l => decide (l ∈ t)) := by
  funext i
  refine Fin.addCases (m := 13) (n := 13) ?_ ?_ i
  · intro p
    have eq : Fin.ofNat 13 p.val = p := Fin.ext (Nat.mod_eq_of_lt p.isLt)
    simp only [requestInput, Fin.val_castAdd, Fin.append_left, if_pos p.isLt, eq]
  · intro l
    have eq : Fin.ofNat 13 (13 + l.val) = l := by
      apply Fin.ext
      simp [Nat.add_mod, Nat.mod_eq_of_lt l.isLt]
    have no : ¬13 + l.val < 13 := by omega
    simp only [requestInput, Fin.val_natAdd, Fin.append_right, if_neg no, eq]

lemma singleton_input (p l : Fin 13) :
    requestInput {p} {l} =
      (fun i : Fin 26 => decide (i.val = p.val ∨ i.val = 13 + l.val)) := by
  rw [requestInput_append]
  funext i
  refine Fin.addCases (m := 13) (n := 13) ?_ ?_ i
  · intro q
    have no : q.val ≠ 13 + l.val := by have := q.isLt; omega
    simp only [Fin.append_left, Fin.val_castAdd, Finset.mem_singleton,
      no, or_false, Fin.ext_iff]
  · intro q
    have no : 13 + q.val ≠ p.val := by have := p.isLt; omega
    simp only [Fin.append_right, Fin.val_natAdd, Finset.mem_singleton,
      no, false_or, Nat.add_left_cancel_iff, Fin.ext_iff]

lemma miss_input (s : Finset (Fin 13)) :
    (fun l : Fin 13 => decide (l ∈ miss s)) =
      (fun l : Fin 13 => decide (∀ p : Fin 13, incident p l → decide (p ∈ s) = false)) := by
  funext l
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, miss, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · intro h p hp
    by_cases hs : p ∈ s
    · exact (h p hs hp).elim
    · simp [hs]
  · intro h p hs hp
    have no := h p hp
    simp [hs] at no

def PostedTests (C : Circuit) : Prop :=
  (∀ p l : Fin 13, incident p l → C.eval (List.ofFn (requestInput {p} {l})) = true) ∧
  ∀ s : Finset (Fin 13), s.card ≤ 3 →
    C.eval (List.ofFn (requestInput s (miss s))) = false ∧
    C.eval (List.ofFn (requestInput (miss s) s)) = false

set_option maxHeartbeats 4000000 in
lemma posted_of_checks (C : Circuit) (mono : PEqualNP.MetaComplexity.Monotone2 C)
    (positive : packedEval C (rowPatterns positiveRows) = BitVec.allOnes 52)
    (negative : ∀ b : Fin 16, packedEval C (closureChunk incident b) = 0)
    (reverseNegative : ∀ b : Fin 16, packedEval C (reversedChunk incident b) = 0) : PostedTests C := by
  constructor
  · intro p l hp
    obtain ⟨r,hr⟩ := listed_positive p l hp
    have eq : positiveRows r = (fun i : Fin 26 =>
        decide (i.val = p.val ∨ i.val = 13 + l.val)) := by
      funext i
      simp only [positiveRows, hr]
    rw [singleton_input, ← eq]
    exact rows_true_of_allOnes positiveRows C mono positive r
  · intro s _
    constructor
    · rw [requestInput_append, miss_input]
      exact closures_of_zero_chunks incident C mono negative (fun p => decide (p ∈ s))
    · rw [requestInput_append, miss_input]
      exact reversed_of_zero_chunks incident C mono reverseNegative (fun p => decide (p ∈ s))

lemma witness_of_checks (C : Circuit) (mono : PEqualNP.MetaComplexity.Monotone2 C)
    (size : C.size ≤ 63)
    (positive : packedEval C (rowPatterns positiveRows) = BitVec.allOnes 52)
    (negative : ∀ b : Fin 16, packedEval C (closureChunk incident b) = 0)
    (reverseNegative : ∀ b : Fin 16, packedEval C (reversedChunk incident b) = 0) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ D.size ≤ 63 ∧ PostedTests D :=
  ⟨C,mono,size,posted_of_checks C mono positive negative reverseNegative⟩

set_option maxHeartbeats 4000000 in
lemma exact_statement_of_checks (C : Circuit)
    (mono : PEqualNP.MetaComplexity.Monotone2 C) (size : C.size ≤ 63)
    (positive : packedEval C (rowPatterns positiveRows) = BitVec.allOnes 52)
    (negative : ∀ b : Fin 16, packedEval C (closureChunk incident b) = 0)
    (reverseNegative : ∀ b : Fin 16, packedEval C (reversedChunk incident b) = 0) :
∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     x1.size ≤ (63 : ℕ) ∧       let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => (↑x2 + ↑x3) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];       have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x3 x4 : Finset (Fin (13 : ℕ))) (x5 : Fin (26 : ℕ)) => if ↑x5 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x3) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x4);       have x4 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x4 : Finset (Fin (13 : ℕ))) => {x5 : Fin (13 : ℕ) | ∀ x6 ∈ x4, ¬x2 x6 x5};       have x5 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x5 x6 : Finset (Fin (13 : ℕ))) => x1.eval (List.ofFn (x3 x5 x6));       (∀ (x6 x7 : Fin (13 : ℕ)), x2 x6 x7 → x5 {x6} {x7} = Bool.true) ∧ ∀ (x6 : Finset (Fin (13 : ℕ))), x6.card ≤ (3 : ℕ) → x5 x6 (x4 x6) = Bool.false ∧ x5 (x4 x6) x6 = Bool.false := by
  exact witness_of_checks C mono size positive negative reverseNegative

def control : Circuit :=
  ⟨[⟨.or,[13,14]⟩,
    ⟨.or,[26,16]⟩,
    ⟨.or,[27,22]⟩,
    ⟨.and,[0,28]⟩,
    ⟨.or,[13,15]⟩,
    ⟨.or,[30,21]⟩,
    ⟨.or,[31,25]⟩,
    ⟨.and,[1,32]⟩,
    ⟨.or,[14,20]⟩,
    ⟨.or,[34,24]⟩,
    ⟨.or,[35,25]⟩,
    ⟨.and,[2,36]⟩,
    ⟨.or,[13,19]⟩,
    ⟨.or,[38,23]⟩,
    ⟨.or,[39,24]⟩,
    ⟨.and,[3,40]⟩,
    ⟨.or,[18,22]⟩,
    ⟨.or,[42,23]⟩,
    ⟨.or,[43,25]⟩,
    ⟨.and,[4,44]⟩,
    ⟨.or,[17,21]⟩,
    ⟨.or,[46,22]⟩,
    ⟨.or,[47,24]⟩,
    ⟨.and,[5,48]⟩,
    ⟨.or,[16,20]⟩,
    ⟨.or,[50,21]⟩,
    ⟨.or,[51,23]⟩,
    ⟨.and,[6,52]⟩,
    ⟨.or,[15,19]⟩,
    ⟨.or,[54,20]⟩,
    ⟨.or,[55,22]⟩,
    ⟨.and,[7,56]⟩,
    ⟨.or,[14,18]⟩,
    ⟨.or,[58,19]⟩,
    ⟨.or,[59,21]⟩,
    ⟨.and,[8,60]⟩,
    ⟨.or,[13,17]⟩,
    ⟨.or,[62,18]⟩,
    ⟨.or,[63,20]⟩,
    ⟨.and,[9,64]⟩,
    ⟨.or,[16,17]⟩,
    ⟨.or,[66,19]⟩,
    ⟨.or,[67,25]⟩,
    ⟨.and,[10,68]⟩,
    ⟨.or,[15,16]⟩,
    ⟨.or,[70,18]⟩,
    ⟨.or,[71,24]⟩,
    ⟨.and,[11,72]⟩,
    ⟨.or,[14,15]⟩,
    ⟨.or,[74,17]⟩,
    ⟨.or,[75,23]⟩,
    ⟨.and,[12,76]⟩,
    ⟨.or,[29,33]⟩,
    ⟨.or,[78,37]⟩,
    ⟨.or,[79,41]⟩,
    ⟨.or,[80,45]⟩,
    ⟨.or,[81,49]⟩,
    ⟨.or,[82,53]⟩,
    ⟨.or,[83,57]⟩,
    ⟨.or,[84,61]⟩,
    ⟨.or,[85,65]⟩,
    ⟨.or,[86,69]⟩,
    ⟨.or,[87,73]⟩,
    ⟨.or,[88,77]⟩],89⟩

lemma control_size : control.size = 64 := rfl

lemma control_mono : PEqualNP.MetaComplexity.Monotone2 control := by
  have checked : control.gates.all (fun g => match g.op with
      | .and | .or => decide (g.inputs.length ≤ 2)
      | _ => false) = true := by
    decide +kernel
  intro g hg
  have h := List.all_eq_true.mp checked g hg
  cases op : g.op <;> simp_all


set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
lemma control_negative_0 :
    packedEval control (closureChunk incident 0) = 0 := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
lemma control_negative_1 :
    packedEval control (closureChunk incident 1) = 0 := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
lemma control_negative_2 :
    packedEval control (closureChunk incident 2) = 0 := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
lemma control_negative_3 :
    packedEval control (closureChunk incident 3) = 0 := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
lemma control_negative_4 :
    packedEval control (closureChunk incident 4) = 0 := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
lemma control_negative_5 :
    packedEval control (closureChunk incident 5) = 0 := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
lemma control_negative_6 :
    packedEval control (closureChunk incident 6) = 0 := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
lemma control_negative_7 :
    packedEval control (closureChunk incident 7) = 0 := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
lemma control_negative_8 :
    packedEval control (closureChunk incident 8) = 0 := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
lemma control_negative_9 :
    packedEval control (closureChunk incident 9) = 0 := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
lemma control_negative_10 :
    packedEval control (closureChunk incident 10) = 0 := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
lemma control_negative_11 :
    packedEval control (closureChunk incident 11) = 0 := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
lemma control_negative_12 :
    packedEval control (closureChunk incident 12) = 0 := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
lemma control_negative_13 :
    packedEval control (closureChunk incident 13) = 0 := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
lemma control_negative_14 :
    packedEval control (closureChunk incident 14) = 0 := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
lemma control_negative_15 :
    packedEval control (closureChunk incident 15) = 0 := by
  decide +kernel

lemma control_negative_chunks :
    ∀ b : Fin 16, packedEval control (closureChunk incident b) = 0 := by
  intro b
  fin_cases b
  · exact control_negative_0
  · exact control_negative_1
  · exact control_negative_2
  · exact control_negative_3
  · exact control_negative_4
  · exact control_negative_5
  · exact control_negative_6
  · exact control_negative_7
  · exact control_negative_8
  · exact control_negative_9
  · exact control_negative_10
  · exact control_negative_11
  · exact control_negative_12
  · exact control_negative_13
  · exact control_negative_14
  · exact control_negative_15

set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
lemma control_reverse_0 :
    packedEval control (reversedChunk incident 0) = 0 := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
lemma control_reverse_1 :
    packedEval control (reversedChunk incident 1) = 0 := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
lemma control_reverse_2 :
    packedEval control (reversedChunk incident 2) = 0 := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
lemma control_reverse_3 :
    packedEval control (reversedChunk incident 3) = 0 := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
lemma control_reverse_4 :
    packedEval control (reversedChunk incident 4) = 0 := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
lemma control_reverse_5 :
    packedEval control (reversedChunk incident 5) = 0 := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
lemma control_reverse_6 :
    packedEval control (reversedChunk incident 6) = 0 := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
lemma control_reverse_7 :
    packedEval control (reversedChunk incident 7) = 0 := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
lemma control_reverse_8 :
    packedEval control (reversedChunk incident 8) = 0 := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
lemma control_reverse_9 :
    packedEval control (reversedChunk incident 9) = 0 := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
lemma control_reverse_10 :
    packedEval control (reversedChunk incident 10) = 0 := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
lemma control_reverse_11 :
    packedEval control (reversedChunk incident 11) = 0 := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
lemma control_reverse_12 :
    packedEval control (reversedChunk incident 12) = 0 := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
lemma control_reverse_13 :
    packedEval control (reversedChunk incident 13) = 0 := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
lemma control_reverse_14 :
    packedEval control (reversedChunk incident 14) = 0 := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
lemma control_reverse_15 :
    packedEval control (reversedChunk incident 15) = 0 := by
  decide +kernel

lemma control_reverse_chunks :
    ∀ b : Fin 16, packedEval control (reversedChunk incident b) = 0 := by
  intro b
  fin_cases b
  · exact control_reverse_0
  · exact control_reverse_1
  · exact control_reverse_2
  · exact control_reverse_3
  · exact control_reverse_4
  · exact control_reverse_5
  · exact control_reverse_6
  · exact control_reverse_7
  · exact control_reverse_8
  · exact control_reverse_9
  · exact control_reverse_10
  · exact control_reverse_11
  · exact control_reverse_12
  · exact control_reverse_13
  · exact control_reverse_14
  · exact control_reverse_15

set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
lemma control_positive :
    packedEval control (rowPatterns positiveRows) = BitVec.allOnes 52 := by
  decide +kernel

lemma control_posted : PostedTests control :=
  posted_of_checks control control_mono control_positive
    control_negative_chunks control_reverse_chunks

end PEqualNP.Outside.L_meta_2056_aux.PackedChunks
