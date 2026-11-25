import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583_aux.PackedCircuit

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

def linePattern {n : Nat} (I : Fin n → Fin n → Prop) [DecidableRel I]
    (l : Fin n) : BitVec (2 ^ n) :=
  ~~~((List.finRange n).foldr (fun p acc =>
    if I p l then pointPattern n p ||| acc else acc) 0)

lemma linePattern_read {n : Nat} (I : Fin n → Fin n → Prop) [DecidableRel I]
    (l : Fin n) (r : Fin (2 ^ n)) :
    (linePattern I l).getLsbD r =
      decide (∀ p : Fin n, I p l → r.val.testBit p.val = false) := by
  have fold_read : ∀ ps : List (Fin n),
      (ps.foldr (fun p acc =>
        if I p l then pointPattern n p ||| acc else acc) 0).getLsbD r =
        ps.any (fun p => decide (I p l) && r.val.testBit p.val) := by
    intro ps
    induction ps with
    | nil => simp
    | cons p ps ih =>
      simp only [List.foldr_cons, List.any_cons]
      split_ifs with h
      · simp only [BitVec.getLsbD_or, pointPattern_read, ih, h, decide_true, Bool.true_and]
      · simp only [ih, h, decide_false, Bool.false_and, Bool.false_or]
  simp only [linePattern, BitVec.getLsbD_not, r.isLt, decide_true, Bool.true_and, fold_read]
  apply Bool.eq_iff_iff.mpr
  simp

def closurePatterns {n : Nat} (I : Fin n → Fin n → Prop) [DecidableRel I] :
    List (BitVec (2 ^ n)) :=
  List.ofFn (pointPattern n) ++ List.ofFn (linePattern I)

lemma closurePatterns_read {n : Nat} (I : Fin n → Fin n → Prop) [DecidableRel I]
    (r : Fin (2 ^ n)) :
    (closurePatterns I).map (fun x => x.getLsbD r) =
      List.ofFn (Fin.append (fun p : Fin n => r.val.testBit p.val)
        (fun l : Fin n => decide (∀ p : Fin n, I p l → r.val.testBit p.val = false))) := by
  simp only [closurePatterns, List.map_append, List.map_ofFn, Function.comp_def,
    pointPattern_read, linePattern_read, List.ofFn_fin_append]

lemma represent_subset {n : Nat} (s : Fin n → Bool) :
    ∃ r : Fin (2 ^ n), ∀ p : Fin n, r.val.testBit p.val = s p := by
  let b : BitVec n := (BitVec.ofBoolListLE (List.ofFn s)).cast (by simp)
  refine ⟨b.toFin, ?_⟩
  intro p
  change b.getLsbD p.val = s p
  simp only [b, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos p.isLt, Option.getD_some]

lemma closure_correct_of_zero {n : Nat}
    (I : Fin n → Fin n → Prop) [DecidableRel I] (C : Circuit)
    (ao : PEqualNP.TopForm.IsAO2 (n + n) C)
    (checked : packedEval C (closurePatterns I) = 0) :
    ∀ s : Fin n → Bool, C.eval (List.ofFn
      (Fin.append s (fun l : Fin n => decide (∀ p : Fin n, I p l → s p = false)))) = false := by
  intro s
  obtain ⟨r,hr⟩ := represent_subset s
  have h := packed_sound r C (fun g hg => ao.1 g hg) (closurePatterns I)
  rw [checked, closurePatterns_read] at h
  have hs : (fun p : Fin n => r.val.testBit p.val) = s := funext hr
  simpa only [hs, BitVec.getLsbD_zero] using h.symm

end PEqualNP.Outside.L_meta_2583_aux.PackedCircuit
