import PEqualNP.Defs
import Mathlib.Tactic.Tauto

namespace PEqualNP.Outside.L_meta_1342

open PEqualNP.CircuitLowerBounds

def baselineCircuit : Circuit :=
  ⟨[
    ⟨.or, [9, 10]⟩,
    ⟨.and, [0, 11]⟩,
    ⟨.or, [5, 10]⟩,
    ⟨.and, [2, 13]⟩,
    ⟨.or, [1, 8]⟩,
    ⟨.or, [15, 10]⟩,
    ⟨.and, [4, 16]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.and, [5, 18]⟩,
    ⟨.or, [3, 7]⟩,
    ⟨.or, [20, 10]⟩,
    ⟨.and, [6, 21]⟩,
    ⟨.or, [3, 9]⟩,
    ⟨.and, [7, 23]⟩,
    ⟨.or, [1, 9]⟩,
    ⟨.and, [8, 25]⟩,
    ⟨.or, [12, 14]⟩,
    ⟨.or, [27, 17]⟩,
    ⟨.or, [28, 19]⟩,
    ⟨.or, [29, 22]⟩,
    ⟨.or, [30, 24]⟩,
    ⟨.or, [31, 26]⟩], 32⟩

lemma baseline_monotone : PEqualNP.MetaComplexity.Monotone2 baselineCircuit := by
  simp [PEqualNP.MetaComplexity.Monotone2, baselineCircuit]

lemma baseline_size : baselineCircuit.size = 22 := rfl

def evalStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma eval_of_fold (C : Circuit) (xs ys : List Bool)
    (h : C.gates.foldl evalStep xs = ys) : C.eval xs = ys.getD C.output false := by
  change (C.gates.foldl evalStep xs).getD C.output false = _
  rw [h]

def baselineValue (x : Fin 11 → Bool) : Bool :=
  let b11 := GateOp.eval .or [x 9, x 10]
  let b12 := GateOp.eval .and [x 0, b11]
  let b13 := GateOp.eval .or [x 5, x 10]
  let b14 := GateOp.eval .and [x 2, b13]
  let b15 := GateOp.eval .or [x 1, x 8]
  let b16 := GateOp.eval .or [b15, x 10]
  let b17 := GateOp.eval .and [x 4, b16]
  let b18 := GateOp.eval .or [x 8, x 9]
  let b19 := GateOp.eval .and [x 5, b18]
  let b20 := GateOp.eval .or [x 3, x 7]
  let b21 := GateOp.eval .or [b20, x 10]
  let b22 := GateOp.eval .and [x 6, b21]
  let b23 := GateOp.eval .or [x 3, x 9]
  let b24 := GateOp.eval .and [x 7, b23]
  let b25 := GateOp.eval .or [x 1, x 9]
  let b26 := GateOp.eval .and [x 8, b25]
  let b27 := GateOp.eval .or [b12, b14]
  let b28 := GateOp.eval .or [b27, b17]
  let b29 := GateOp.eval .or [b28, b19]
  let b30 := GateOp.eval .or [b29, b22]
  let b31 := GateOp.eval .or [b30, b24]
  let b32 := GateOp.eval .or [b31, b26]
  b32

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8000 in
lemma baseline_eval (x : Fin 11 → Bool) :
    baselineCircuit.eval (List.ofFn x) = baselineValue x := by
  let b11 := GateOp.eval .or [x 9, x 10]
  let b12 := GateOp.eval .and [x 0, b11]
  let b13 := GateOp.eval .or [x 5, x 10]
  let b14 := GateOp.eval .and [x 2, b13]
  let b15 := GateOp.eval .or [x 1, x 8]
  let b16 := GateOp.eval .or [b15, x 10]
  let b17 := GateOp.eval .and [x 4, b16]
  let b18 := GateOp.eval .or [x 8, x 9]
  let b19 := GateOp.eval .and [x 5, b18]
  let b20 := GateOp.eval .or [x 3, x 7]
  let b21 := GateOp.eval .or [b20, x 10]
  let b22 := GateOp.eval .and [x 6, b21]
  let b23 := GateOp.eval .or [x 3, x 9]
  let b24 := GateOp.eval .and [x 7, b23]
  let b25 := GateOp.eval .or [x 1, x 9]
  let b26 := GateOp.eval .and [x 8, b25]
  let b27 := GateOp.eval .or [b12, b14]
  let b28 := GateOp.eval .or [b27, b17]
  let b29 := GateOp.eval .or [b28, b19]
  let b30 := GateOp.eval .or [b29, b22]
  let b31 := GateOp.eval .or [b30, b24]
  let b32 := GateOp.eval .or [b31, b26]
  change baselineCircuit.eval (List.ofFn x) = b32
  have hinput : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10] := by
    simp [List.ofFn_succ]
  have s11 : evalStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10] ⟨.or, [9, 10]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, b11] := by rfl
  have s12 : evalStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, b11] ⟨.and, [0, 11]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, b11, b12] := by rfl
  have s13 : evalStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, b11, b12] ⟨.or, [5, 10]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, b11, b12, b13] := by rfl
  have s14 : evalStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, b11, b12, b13] ⟨.and, [2, 13]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, b11, b12, b13, b14] := by rfl
  have s15 : evalStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, b11, b12, b13, b14] ⟨.or, [1, 8]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, b11, b12, b13, b14, b15] := by rfl
  have s16 : evalStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, b11, b12, b13, b14, b15] ⟨.or, [15, 10]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, b11, b12, b13, b14, b15, b16] := by rfl
  have s17 : evalStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, b11, b12, b13, b14, b15, b16] ⟨.and, [4, 16]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, b11, b12, b13, b14, b15, b16, b17] := by rfl
  have s18 : evalStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, b11, b12, b13, b14, b15, b16, b17] ⟨.or, [8, 9]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, b11, b12, b13, b14, b15, b16, b17, b18] := by rfl
  have s19 : evalStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, b11, b12, b13, b14, b15, b16, b17, b18] ⟨.and, [5, 18]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, b11, b12, b13, b14, b15, b16, b17, b18, b19] := by rfl
  have s20 : evalStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, b11, b12, b13, b14, b15, b16, b17, b18, b19] ⟨.or, [3, 7]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20] := by rfl
  have s21 : evalStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20] ⟨.or, [20, 10]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21] := by rfl
  have s22 : evalStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21] ⟨.and, [6, 21]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22] := by rfl
  have s23 : evalStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22] ⟨.or, [3, 9]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23] := by rfl
  have s24 : evalStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23] ⟨.and, [7, 23]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24] := by rfl
  have s25 : evalStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24] ⟨.or, [1, 9]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25] := by rfl
  have s26 : evalStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25] ⟨.and, [8, 25]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26] := by rfl
  have s27 : evalStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26] ⟨.or, [12, 14]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27] := by rfl
  have s28 : evalStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27] ⟨.or, [27, 17]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28] := by rfl
  have s29 : evalStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28] ⟨.or, [28, 19]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29] := by rfl
  have s30 : evalStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29] ⟨.or, [29, 22]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30] := by rfl
  have s31 : evalStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30] ⟨.or, [30, 24]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31] := by rfl
  have s32 : evalStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31] ⟨.or, [31, 26]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32] := by rfl
  have h : baselineCircuit.gates.foldl evalStep (List.ofFn x) = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32] := by
    simp only [baselineCircuit]
    rw [hinput]
    rw [List.foldl_cons, s11]
    rw [List.foldl_cons, s12]
    rw [List.foldl_cons, s13]
    rw [List.foldl_cons, s14]
    rw [List.foldl_cons, s15]
    rw [List.foldl_cons, s16]
    rw [List.foldl_cons, s17]
    rw [List.foldl_cons, s18]
    rw [List.foldl_cons, s19]
    rw [List.foldl_cons, s20]
    rw [List.foldl_cons, s21]
    rw [List.foldl_cons, s22]
    rw [List.foldl_cons, s23]
    rw [List.foldl_cons, s24]
    rw [List.foldl_cons, s25]
    rw [List.foldl_cons, s26]
    rw [List.foldl_cons, s27]
    rw [List.foldl_cons, s28]
    rw [List.foldl_cons, s29]
    rw [List.foldl_cons, s30]
    rw [List.foldl_cons, s31]
    rw [List.foldl_cons, s32]
    rfl
  exact eval_of_fold baselineCircuit (List.ofFn x) [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32] h

lemma edges_iff (es : List (Fin 11 × Fin 11)) (x : Fin 11 → Bool) :
    (∃ u v : Fin 11, (u.val, v.val) ∈ es.map (fun p => (p.1.val, p.2.val)) ∧
      x u = true ∧ x v = true) ↔ es.any (fun p => x p.1 && x p.2) = true := by
  constructor
  · rintro ⟨u, v, hm, hu, hv⟩
    rcases List.mem_map.mp hm with ⟨⟨a, b⟩, hab, hp⟩
    have ha : a = u := Fin.ext (congrArg Prod.fst hp)
    have hb : b = v := Fin.ext (congrArg Prod.snd hp)
    subst u
    subst v
    exact List.any_eq_true.mpr ⟨(a, b), hab, (by simp [hu, hv])⟩
  · intro h
    rcases List.any_eq_true.mp h with ⟨⟨u, v⟩, hm, hv⟩
    have ht : x u = true ∧ x v = true := by simpa using hv
    exact ⟨u, v, List.mem_map.mpr ⟨(u, v), hm, rfl⟩, ht.1, ht.2⟩

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8000 in
lemma baseline_spec : ∀ x : Fin 11 → Bool, (baselineCircuit.eval (List.ofFn x) = true ↔ ∃ u v : Fin 11, (u.val, v.val) ∈ ([(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true) := by
  intro x
  let es : List (Fin 11 × Fin 11) := [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
  change baselineCircuit.eval (List.ofFn x) = true ↔
    (∃ u v : Fin 11, (u.val, v.val) ∈ es.map (fun p => (p.1.val, p.2.val)) ∧
      x u = true ∧ x v = true)
  rw [baseline_eval, edges_iff]
  simp [baselineValue, es, GateOp.eval,
    and_or_left, and_comm,
    or_assoc, or_left_comm, or_comm]

end PEqualNP.Outside.L_meta_1342
