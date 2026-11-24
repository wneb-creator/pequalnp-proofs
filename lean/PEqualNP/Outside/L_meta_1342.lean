import Mathlib
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

namespace PEqualNP.Outside.L_meta_1342_aux

theorem countUnion {α : Type*} [DecidableEq α] (support : ℕ → Finset α)
    (paid : Finset ℕ) (m : ℕ)
    (step : ∀ w < m, 1 < (support w).card → ∃ cs : Finset ℕ,
      cs ⊆ Finset.range w ∧ support w ⊆ cs.biUnion support ∧
      cs.card ≤ 1 + (if w ∈ paid then 1 else 0))
    (roots : Finset ℕ) (hr : roots ⊆ Finset.range m) :
    (roots.biUnion support).card ≤ roots.card + ((Finset.range m) ∩ paid).card := by
  classical
  induction m generalizing roots with
  | zero =>
    have : roots = ∅ := by simpa using hr
    simp [this]
  | succ m ih =>
    have old := ih (fun w hw => step w (by omega))
    have hpre : roots.erase m ⊆ Finset.range m := by
      intro w hw
      have ⟨hne, hmem⟩ := Finset.mem_erase.mp hw
      have hlt := Finset.mem_range.mp (hr hmem)
      exact Finset.mem_range.mpr (by omega)
    have hcost : ((Finset.range (m + 1)) ∩ paid).card =
        ((Finset.range m) ∩ paid).card + (if m ∈ paid then 1 else 0) := by
      by_cases h : m ∈ paid
      · have he : Finset.range (m + 1) ∩ paid = insert m (Finset.range m ∩ paid) := by
          ext w
          by_cases hw : w = m <;> simp [Finset.range_add_one, hw, h]
        simp [he, h]
      · have he : Finset.range (m + 1) ∩ paid = Finset.range m ∩ paid := by
          ext w
          by_cases hw : w = m <;> simp [Finset.range_add_one, hw, h]
        simp [he, h]
    rw [hcost]
    by_cases hm : m ∈ roots
    · have hrins := Finset.insert_erase hm
      have hroots : (roots.erase m).card + 1 = roots.card :=
        Finset.card_erase_add_one hm
      by_cases hb : 1 < (support m).card
      · obtain ⟨cs, hcpre, hcov, hcard⟩ := step m (by omega) hb
        have hsub : roots.biUnion support ⊆ ((roots.erase m) ∪ cs).biUnion support := by
          intro a ha
          obtain ⟨w, hw, haw⟩ := Finset.mem_biUnion.mp ha
          by_cases heq : w = m
          · subst w
            obtain ⟨v, hv, hav⟩ := Finset.mem_biUnion.mp (hcov haw)
            exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_union_right _ hv, hav⟩
          · exact Finset.mem_biUnion.mpr
              ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨heq, hw⟩), haw⟩
        have hh := old ((roots.erase m) ∪ cs) (Finset.union_subset hpre hcpre)
        have hh' := Finset.card_le_card hsub
        have hu := Finset.card_union_le (roots.erase m) cs
        omega
      · have hh := old (roots.erase m) hpre
        have he : roots.biUnion support = support m ∪ (roots.erase m).biUnion support := by
          conv_lhs => rw [← hrins]
          rw [Finset.biUnion_insert]
        rw [he]
        have hu := Finset.card_union_le (support m) ((roots.erase m).biUnion support)
        omega
    · rw [Finset.erase_eq_of_notMem hm] at hpre
      have hh := old roots hpre
      omega

theorem dag_union_bound {α : Type*} [DecidableEq α] (f : ℕ → Finset α) (R B : Finset ℕ)
    (step : ∀ i, 1 < (f i).card → (∃ a < i, f i ⊆ f a) ∨
      (i ∈ B ∧ ∃ a < i, ∃ b < i, f i ⊆ f a ∪ f b)) :
    (R.biUnion f).card ≤ R.card + B.card := by
  classical
  let m := R.sup id + 1
  have hr : R ⊆ Finset.range m := by
    intro w hw
    have h : w ≤ R.sup id := Finset.le_sup (f := id) hw
    exact Finset.mem_range.mpr (by dsimp [m]; omega)
  have haux : (R.biUnion f).card ≤ R.card + (Finset.range m ∩ B).card := by
    apply countUnion f B m _ R hr
    intro i _ hi
    rcases step i hi with ⟨a, ha, hsub⟩ | ⟨hiB, a, ha, b, hb, hsub⟩
    · refine ⟨{a}, ?_, ?_, ?_⟩
      · simpa using ha
      · simpa using hsub
      · simp
    · refine ⟨{a,b}, ?_, ?_, ?_⟩
      · intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact Finset.mem_range.mpr ha
        · rw [Finset.mem_singleton.mp hw]
          exact Finset.mem_range.mpr hb
      · simpa using hsub
      · simp only [hiB, ite_true]
        exact Finset.card_le_two
  have hl := Finset.card_le_card (Finset.inter_subset_right (s₁ := Finset.range m) (s₂ := B))
  omega

theorem gate_partition_count (n len : ℕ) (A : ℕ → Bool) (S : ℕ → Finset (Fin n)) :
    ((Finset.range (n + 1 + len)).filter (fun w => n + 1 ≤ w ∧ A w = true)).card +
    ((Finset.range (n + 1 + len)).filter (fun w => n + 1 ≤ w ∧ A w = false ∧
      1 < (S w).card)).card +
    ((Finset.range (n + 1 + len)).filter (fun w => n + 1 ≤ w ∧ A w = false ∧
      (S w).card ≤ 1)).card ≤ len := by
  classical
  let gates := Finset.range (n + 1 + len)
  let ands := gates.filter (fun w => n + 1 ≤ w ∧ A w = true)
  let large := gates.filter (fun w => n + 1 ≤ w ∧ A w = false ∧ 1 < (S w).card)
  let small := gates.filter (fun w => n + 1 ≤ w ∧ A w = false ∧ (S w).card ≤ 1)
  change ands.card + large.card + small.card ≤ len
  have hdis : Disjoint ands large := by
    apply Finset.disjoint_left.mpr
    intro w h₁ h₂
    have a := (Finset.mem_filter.mp h₁).2.2
    have b := (Finset.mem_filter.mp h₂).2.2.1
    simp_all
  have hdis' : Disjoint (ands ∪ large) small := by
    apply Finset.disjoint_left.mpr
    intro w h₁ h₂
    have b := (Finset.mem_filter.mp h₂).2.2
    rcases Finset.mem_union.mp h₁ with ha | hl
    · have a := (Finset.mem_filter.mp ha).2.2
      simp_all
    · have a := (Finset.mem_filter.mp hl).2.2.2
      exact (Nat.not_lt_of_ge b.2) a
  have hsub : (ands ∪ large) ∪ small ⊆ Finset.Ico (n+1) (n+1+len) := by
    intro w hw
    rcases Finset.mem_union.mp hw with h | h
    · rcases Finset.mem_union.mp h with h | h <;>
        exact Finset.mem_Ico.mpr ⟨(Finset.mem_filter.mp h).2.1,
          Finset.mem_range.mp (Finset.mem_filter.mp h).1⟩
    · exact Finset.mem_Ico.mpr ⟨(Finset.mem_filter.mp h).2.1,
        Finset.mem_range.mp (Finset.mem_filter.mp h).1⟩
  rw [← Finset.card_union_of_disjoint hdis, ← Finset.card_union_of_disjoint hdis']
  simpa using Finset.card_le_card hsub

def coverCert {n : ℕ} (k N : ℕ) (S : ℕ → Finset (Fin n))
    (a b : ℕ → ℕ) (A : ℕ → Bool)
    (ha : ∀ w, k ≤ w → w < N → a w < w)
    (hb : ∀ w, k ≤ w → w < N → b w < w) (w : ℕ) : Finset (Fin n) :=
  if (S w).card ≤ 1 then
    if _hg : k ≤ w ∧ w < N then
      if A w = true then
        if (S (a w)).card ≤ 1 then coverCert k N S a b A ha hb (a w)
        else coverCert k N S a b A ha hb (b w)
      else
        coverCert k N S a b A ha hb (a w) ∪ coverCert k N S a b A ha hb (b w)
    else S w
  else ∅
termination_by w
decreasing_by all_goals first | exact ha _ _hg.1 _hg.2 | exact hb _ _hg.1 _hg.2

theorem cover_half (n k N r : ℕ) (G : SimpleGraph (Fin n))
    (S : ℕ → Finset (Fin n)) (H : ℕ → Fin n → Fin n → Prop)
    (a b : ℕ → ℕ) (A : ℕ → Bool) (hr : r < N) (hrS : S r = ∅)
    (hrH : ∀ u v, G.Adj u v → H r u v)
    (hinput : ∀ w u v, w < k → H w u v → u ∈ S w ∨ v ∈ S w)
    (ha : ∀ w, k ≤ w → w < N → a w < w)
    (hb : ∀ w, k ≤ w → w < N → b w < w)
    (horS : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (horH : ∀ w u v, k ≤ w → w < N → A w = false → H w u v →
      H (a w) u v ∨ H (b w) u v)
    (handS : ∀ w, k ≤ w → w < N → A w = true →
      (S (a w)).card ≤ 1 ∨ (S (b w)).card ≤ 1)
    (handH : ∀ w u v, k ≤ w → w < N → A w = true → H w u v →
      H (a w) u v ∧ H (b w) u v)
    (hdag : ∀ (f : ℕ → Finset (Fin n)) (R B : Finset ℕ),
      (∀ i, 1 < (f i).card → (∃ a < i, f i ⊆ f a) ∨
        (i ∈ B ∧ ∃ a < i, ∃ b < i, f i ⊆ f a ∪ f b)) →
      (R.biUnion f).card ≤ R.card + B.card) :
    ∃ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
      T.card ≤ 1 + ((Finset.range N).filter fun w =>
        k ≤ w ∧ A w = false ∧ (S w).card ≤ 1).card := by
  let f := coverCert k N S a b A ha hb
  let B := (Finset.range N).filter fun w => k ≤ w ∧ A w = false ∧ (S w).card ≤ 1
  have feq (w : ℕ) : f w =
      if (S w).card ≤ 1 then
        if k ≤ w ∧ w < N then
          if A w = true then
            if (S (a w)).card ≤ 1 then f (a w) else f (b w)
          else f (a w) ∪ f (b w)
        else S w
      else ∅ := by
    exact coverCert.eq_1 ..
  have hit : ∀ w, w < N → (S w).card ≤ 1 →
      ∀ u v, H w u v → u ∈ f w ∨ v ∈ f w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw ht u v hwuv
      rw [feq, ite_eq_left ht]
      by_cases hkw : k ≤ w
      · rw [ite_eq_left ⟨hkw, hw⟩]
        cases hg : A w with
        | false =>
          simp only [Bool.false_eq_true, ite_false]
          have heq := horS w hkw hw hg
          have hta : (S (a w)).card ≤ 1 := by
            apply (Finset.card_le_card _).trans ht
            rw [heq]
            exact Finset.subset_union_left
          have htb : (S (b w)).card ≤ 1 := by
            apply (Finset.card_le_card _).trans ht
            rw [heq]
            exact Finset.subset_union_right
          have hia := ha w hkw hw
          have hib := hb w hkw hw
          rcases horH w u v hkw hw hg hwuv with h | h
          · have hitA := ih _ hia (hia.trans hw) hta u v h
            simp only [Finset.mem_union]
            tauto
          · have hitB := ih _ hib (hib.trans hw) htb u v h
            simp only [Finset.mem_union]
            tauto
        | true =>
          simp only [ite_true]
          have hz := handH w u v hkw hw hg hwuv
          by_cases htA : (S (a w)).card ≤ 1
          · rw [ite_eq_left htA]
            have hl := ha w hkw hw
            exact ih _ hl (hl.trans hw) htA u v hz.1
          · rw [ite_eq_right htA]
            have hl := hb w hkw hw
            exact ih _ hl (hl.trans hw) ((handS w hkw hw hg).resolve_left htA) u v hz.2
      · rw [ite_eq_right (fun h => hkw h.1)]
        exact hinput w u v (Nat.lt_of_not_ge hkw) hwuv
  refine ⟨f r, fun u v huv => hit r hr (by simp [hrS]) u v (hrH u v huv), ?_⟩
  have hstep (w : ℕ) (hw : 1 < (f w).card) :
      (∃ j < w, f w ⊆ f j) ∨
        (w ∈ B ∧ ∃ i < w, ∃ j < w, f w ⊆ f i ∪ f j) := by
    have ht : (S w).card ≤ 1 := by
      by_contra ht
      rw [feq, ite_eq_right ht] at hw
      simp at hw
    have hg : k ≤ w ∧ w < N := by
      by_contra h
      rw [feq, ite_eq_left ht, ite_eq_right h] at hw
      omega
    have hia := ha w hg.1 hg.2
    have hib := hb w hg.1 hg.2
    cases hop : A w with
    | false =>
      right
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hg.2, hg.1, hop, ht⟩,
        a w, hia, b w, hib, ?_⟩
      rw [feq, ite_eq_left ht, ite_eq_left hg, hop]
      simp
    | true =>
      left
      by_cases htA : (S (a w)).card ≤ 1
      · refine ⟨a w, hia, ?_⟩
        rw [feq, ite_eq_left ht, ite_eq_left hg, ite_eq_left hop, ite_eq_left htA]
      · refine ⟨b w, hib, ?_⟩
        rw [feq, ite_eq_left ht, ite_eq_left hg, ite_eq_left hop, ite_eq_right htA]
  simpa [B] using hdag f {r} B hstep

theorem edge_birth (n k N r : ℕ) (S : ℕ → Finset (Fin n))
    (H : ℕ → Fin n → Fin n → Prop) (a b : ℕ → ℕ) (A : ℕ → Bool)
    (x y : Fin n) (hr : r < N) (hxy : H r x y) (hx : x ∉ S r) (hy : y ∉ S r)
    (hinput : ∀ w u v, w < k → H w u v → u ∈ S w ∨ v ∈ S w)
    (ha : ∀ w, k ≤ w → w < N → a w < w)
    (hb : ∀ w, k ≤ w → w < N → b w < w)
    (horS : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (horH : ∀ w u v, k ≤ w → w < N → A w = false → H w u v →
      H (a w) u v ∨ H (b w) u v)
    (handH : ∀ w u v, k ≤ w → w < N → A w = true → H w u v →
      H (a w) u v ∧ H (b w) u v)
    (hdisj : ∀ w, k ≤ w → w < N → A w = true → Disjoint (S (a w)) (S (b w))) :
    ∃ w, k ≤ w ∧ w < N ∧ A w = true ∧
      ((x ∈ S (a w) ∧ y ∈ S (b w)) ∨ (y ∈ S (a w) ∧ x ∈ S (b w))) := by
  induction r using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hkw : k ≤ w
    · have hia := ha w hkw hr
      have hib := hb w hkw hr
      cases hop : A w with
      | false =>
        have hSw := horS w hkw hr hop
        rw [hSw, Finset.mem_union] at hx hy
        rcases horH w x y hkw hr hop hxy with h | h
        · exact ih _ hia (hia.trans hr) h (fun h => hx (.inl h)) (fun h => hy (.inl h))
        · exact ih _ hib (hib.trans hr) h (fun h => hx (.inr h)) (fun h => hy (.inr h))
      | true =>
        have htrue := handH w x y hkw hr hop hxy
        by_cases hsa : x ∈ S (a w) ∨ y ∈ S (a w)
        · by_cases hsb : x ∈ S (b w) ∨ y ∈ S (b w)
          · refine ⟨w, hkw, hr, hop, ?_⟩
            have hd := Finset.disjoint_left.mp (hdisj w hkw hr hop)
            rcases hsa with hax | hay <;> rcases hsb with hbx | hby
            · exact False.elim (hd hax hbx)
            · exact Or.inl ⟨hax, hby⟩
            · exact Or.inr ⟨hay, hbx⟩
            · exact False.elim (hd hay hby)
          · exact ih _ hib (hib.trans hr) htrue.2 (fun h => hsb (.inl h)) (fun h => hsb (.inr h))
        · exact ih _ hia (hia.trans hr) htrue.1 (fun h => hsa (.inl h)) (fun h => hsa (.inr h))
    · rcases hinput w x y (Nat.lt_of_not_ge hkw) hxy with h | h
      · exact False.elim (hx h)
      · exact False.elim (hy h)

theorem edge_finset_gate_bound (n k N : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : ℕ → Finset (Fin n)) (a b : ℕ → ℕ) (A : ℕ → Bool)
    (hc4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hsmall : ∀ w < k, (S w).card ≤ 1)
    (hparents : ∀ w, k ≤ w → w < N → a w < w ∧ b w < w)
    (hzero : ∀ w, k ≤ w → w < N → A w = true → S w = ∅)
    (hunion : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (hjoin : ∀ w, k ≤ w → w < N → A w = true →
      ∀ u ∈ S (a w), ∀ v ∈ S (b w), G.Adj u v)
    (hside : ∀ w, k ≤ w → w < N → A w = true →
      (S (a w)).card ≤ 1 ∨ (S (b w)).card ≤ 1)
    (hcover : ∀ u v, G.Adj u v → ∃ w, k ≤ w ∧ w < N ∧ A w = true ∧
      ((u ∈ S (a w) ∧ v ∈ S (b w)) ∨ (v ∈ S (a w) ∧ u ∈ S (b w)))) :
    G.edgeFinset.card ≤
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = true)).card +
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ 1 < (S w).card)).card := by
  classical
  cases isEmpty_or_nonempty (Fin n) with
  | inl h =>
    have := h
    have he : G.edgeFinset = ∅ := Finset.eq_empty_of_forall_notMem (fun e => isEmptyElim e)
    simp [he]
  | inr hn =>
    let z := Classical.choice hn
    let AS := (Finset.range N).filter (fun w => k ≤ w ∧ A w = true)
    let OS := (Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ 1 < (S w).card)
    let adj (c : Fin n) (w : ℕ) := ∀ x ∈ S w, G.Adj c x
    let F (c : Fin n) (w : ℕ) := if w < N ∧ adj c w then S w else ∅
    have pick : ∀ w, ∃ (c : Fin n) (j : ℕ), w ∈ AS →
        ∀ u ∈ S (a w), ∀ v ∈ S (b w),
          (u = c ∧ v ∈ F c j) ∨ (v = c ∧ u ∈ F c j) := by
      intro w
      by_cases hw : w ∈ AS
      · obtain ⟨hN, hk, hA⟩ : w < N ∧ k ≤ w ∧ A w = true := by simpa [AS] using hw
        obtain ⟨ha,hb⟩ := hparents w hk hN
        have hJ := hjoin w hk hN hA
        rcases hside w hk hN hA with h | h
        · by_cases hne : (S (a w)).Nonempty
          · obtain ⟨c,hc⟩ := hne
            have hf : F c (b w) = S (b w) := ite_eq_left ⟨by omega, hJ c hc⟩
            exact ⟨c, b w, fun _ u hu v hv => Or.inl ⟨Finset.card_le_one.mp h u hu c hc, hf ▸ hv⟩⟩
          · exact ⟨z, 0, fun _ u hu => (hne ⟨u,hu⟩).elim⟩
        · by_cases hne : (S (b w)).Nonempty
          · obtain ⟨c,hc⟩ := hne
            have hf : F c (a w) = S (a w) := ite_eq_left ⟨by omega, fun x hx => (hJ x hx c hc).symm⟩
            exact ⟨c, a w, fun _ u hu v hv => Or.inr ⟨Finset.card_le_one.mp h v hv c hc, hf ▸ hu⟩⟩
          · exact ⟨z, 0, fun _ _ _ v hv => (hne ⟨v,hv⟩).elim⟩
      · exact ⟨z, 0, fun h => (hw h).elim⟩
    choose cOf jOf spec using pick
    let oc (w : ℕ) := if h : ∃ c, adj c w then h.choose else z
    have owner_eq (w : ℕ) (c : Fin n) (hbig : 1 < (S w).card) (h : adj c w) : oc w = c := by
      have hex : ∃ c, adj c w := ⟨c,h⟩
      have h' : adj (oc w) w := by simpa [oc, hex] using hex.choose_spec
      by_contra hne
      obtain ⟨u,hu,v,hv,huv⟩ := Finset.one_lt_card.mp hbig
      exact hc4 (oc w) u c v hne huv ⟨h' u hu, (h u hu).symm, h v hv, (h' v hv).symm⟩
    let R (c : Fin n) := (AS.filter (fun w => cOf w = c)).image jOf
    let B (c : Fin n) := OS.filter (fun w => oc w = c)
    have hlocal (c : Fin n) : ((R c).biUnion (F c)).card ≤ (R c).card + (B c).card := by
      apply dag_union_bound
      intro i hi
      by_cases hgood : i < N ∧ adj c i
      · have hf : F c i = S i := ite_eq_left hgood
        rw [hf] at hi
        have hk : k ≤ i := by by_contra! h; have := hsmall i h; omega
        have hA : A i = false := by
          cases he : A i with
          | false => rfl
          | true => simp [hzero i hk hgood.1 he] at hi
        have ⟨ha,hb⟩ := hparents i hk hgood.1
        have hu := hunion i hk hgood.1 hA
        have hfa : F c (a i) = S (a i) := ite_eq_left ⟨by omega,
          fun x hx => hgood.2 x (hu ▸ Finset.mem_union_left _ hx)⟩
        have hfb : F c (b i) = S (b i) := ite_eq_left ⟨by omega,
          fun x hx => hgood.2 x (hu ▸ Finset.mem_union_right _ hx)⟩
        right
        refine ⟨?_, a i, ha, b i, hb, ?_⟩
        · simp [B, OS, hgood.1, hk, hA, hi, owner_eq i c hi hgood.2]
        · rw [hf,hfa,hfb,hu]
      · simp [F,hgood] at hi
    let E (c : Fin n) := ((R c).biUnion (F c)).image (fun x => s(c,x))
    have subset : G.edgeFinset ⊆ Finset.univ.biUnion E := by
      intro e
      induction e using Sym2.inductionOn with
      | _ u v =>
        intro he
        have huv : G.Adj u v := G.mem_edgeFinset.mp he
        obtain ⟨w,hk,hN,hA,how⟩ := hcover u v huv
        have hw : w ∈ AS := by simp [AS,hN,hk,hA]
        have hj : jOf w ∈ R (cOf w) := Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hw,rfl⟩)
        have member (t : Fin n) (ht : t ∈ F (cOf w) (jOf w)) :
            s(cOf w,t) ∈ Finset.univ.biUnion E :=
          Finset.mem_biUnion.mpr ⟨cOf w, Finset.mem_univ _,
            Finset.mem_image_of_mem _ (Finset.mem_biUnion.mpr ⟨jOf w,hj,ht⟩)⟩
        rcases how with ⟨hu,hv⟩ | ⟨hv,hu⟩
        · rcases spec w hw u hu v hv with ⟨he,ht⟩ | ⟨he,ht⟩
          · simpa only [he] using member v ht
          · simpa only [he, Sym2.eq_swap] using member u ht
        · rcases spec w hw v hv u hu with ⟨he,ht⟩ | ⟨he,ht⟩
          · simpa only [he, Sym2.eq_swap] using member u ht
          · simpa only [he] using member v ht
    have hrs : (∑ c, (AS.filter (fun w => cOf w = c)).card) = AS.card :=
      (Finset.card_eq_sum_card_fiberwise (f := cOf) (t := Finset.univ) (by simp)).symm
    have hbs : (∑ c, (B c).card) = OS.card :=
      (Finset.card_eq_sum_card_fiberwise (f := oc) (t := Finset.univ) (by simp)).symm
    calc
      G.edgeFinset.card ≤ (Finset.univ.biUnion E).card := Finset.card_le_card subset
      _ ≤ ∑ c, (E c).card := Finset.card_biUnion_le
      _ ≤ ∑ c, ((AS.filter (fun w => cOf w = c)).card + (B c).card) := by
        apply Finset.sum_le_sum
        intro c _
        exact Finset.card_image_le.trans ((hlocal c).trans (Nat.add_le_add_right Finset.card_image_le _))
      _ = _ := by rw [Finset.sum_add_distrib, hrs, hbs]


theorem edge_finset_gate_bound_partial (n k N : ℕ)
    (K G : SimpleGraph (Fin n)) [DecidableRel K.Adj] [DecidableRel G.Adj]
    (S : ℕ → Finset (Fin n)) (a b : ℕ → ℕ) (A : ℕ → Bool)
    (hc4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (K.Adj a b ∧ K.Adj b c ∧ K.Adj c d ∧ K.Adj d a))
    (hsmall : ∀ w < k, (S w).card ≤ 1)
    (hparents : ∀ w, k ≤ w → w < N → a w < w ∧ b w < w)
    (hzero : ∀ w, k ≤ w → w < N → A w = true → S w = ∅)
    (hunion : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (hjoin : ∀ w, k ≤ w → w < N → A w = true →
      ∀ u ∈ S (a w), ∀ v ∈ S (b w), K.Adj u v)
    (hside : ∀ w, k ≤ w → w < N → A w = true →
      (S (a w)).card ≤ 1 ∨ (S (b w)).card ≤ 1)
    (hcover : ∀ u v, G.Adj u v → ∃ w, k ≤ w ∧ w < N ∧ A w = true ∧
      ((u ∈ S (a w) ∧ v ∈ S (b w)) ∨ (v ∈ S (a w) ∧ u ∈ S (b w)))) :
    G.edgeFinset.card ≤
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = true)).card +
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ 1 < (S w).card)).card := by
  classical
  let born (u v : Fin n) : Prop := ∃ w, k ≤ w ∧ w < N ∧ A w = true ∧
    ((u ∈ S (a w) ∧ v ∈ S (b w)) ∨ (v ∈ S (a w) ∧ u ∈ S (b w)))
  have born_adj (u v : Fin n) (h : born u v) : K.Adj u v := by
    obtain ⟨w, hk, hN, hA, h⟩ := h
    rcases h with ⟨hu,hv⟩ | ⟨hv,hu⟩
    · exact hjoin w hk hN hA u hu v hv
    · exact (hjoin w hk hN hA v hv u hu).symm
  let B : SimpleGraph (Fin n) := {
    Adj := born
    symm := ⟨by
      intro u v h
      obtain ⟨w,hk,hN,hA,h⟩ := h
      exact ⟨w,hk,hN,hA,h.elim Or.inr Or.inl⟩⟩
    loopless := ⟨by
      intro u h
      exact K.loopless.irrefl u (born_adj u u h)⟩ }
  have hB4 (u v x y : Fin n) (hux : u ≠ x) (hvy : v ≠ y) :
      ¬ (B.Adj u v ∧ B.Adj v x ∧ B.Adj x y ∧ B.Adj y u) := by
    intro h
    exact hc4 u v x y hux hvy
      ⟨born_adj u v h.1, born_adj v x h.2.1,
        born_adj x y h.2.2.1, born_adj y u h.2.2.2⟩
  have hjoinB (w : ℕ) (hk : k ≤ w) (hN : w < N) (hA : A w = true)
      (u : Fin n) (hu : u ∈ S (a w)) (v : Fin n) (hv : v ∈ S (b w)) : B.Adj u v :=
    ⟨w,hk,hN,hA,Or.inl ⟨hu,hv⟩⟩
  have hcount := edge_finset_gate_bound n k N B S a b A hB4 hsmall hparents
    hzero hunion hjoinB hside (fun _ _ h => h)
  have hsub : G.edgeFinset ⊆ B.edgeFinset := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
      exact B.mem_edgeFinset.mpr (hcover u v (G.mem_edgeFinset.mp he))
  exact (Finset.card_le_card hsub).trans hcount

theorem total_from_model_partial (n k N r L : ℕ)
    (K G : SimpleGraph (Fin n)) [DecidableRel K.Adj] [DecidableRel G.Adj]
    (S : ℕ → Finset (Fin n)) (R : ℕ → Fin n → Fin n → Prop)
    (a b : ℕ → ℕ) (A : ℕ → Bool)
    (hc4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (K.Adj a b ∧ K.Adj b c ∧ K.Adj c d ∧ K.Adj d a))
    (hr : r < N) (hrS : S r = ∅) (hrH : ∀ u v, G.Adj u v → R r u v)
    (hsmall : ∀ w < k, (S w).card ≤ 1)
    (hinput : ∀ w u v, w < k → R w u v → u ∈ S w ∨ v ∈ S w)
    (ha : ∀ w, k ≤ w → w < N → a w < w)
    (hb : ∀ w, k ≤ w → w < N → b w < w)
    (horS : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (horH : ∀ w u v, k ≤ w → w < N → A w = false → R w u v →
      R (a w) u v ∨ R (b w) u v)
    (handH : ∀ w u v, k ≤ w → w < N → A w = true → R w u v →
      R (a w) u v ∧ R (b w) u v)
    (hzero : ∀ w, k ≤ w → w < N → A w = true → S w = ∅)
    (hjoin : ∀ w, k ≤ w → w < N → A w = true →
      ∀ u ∈ S (a w), ∀ v ∈ S (b w), K.Adj u v)
    (hpartition :
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = true)).card +
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ 1 < (S w).card)).card +
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ (S w).card ≤ 1)).card ≤ L) :
    ∃ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
      G.edgeFinset.card + T.card ≤ L + 1 := by
  classical
  have hd (w : ℕ) (hk : k ≤ w) (hN : w < N) (hA : A w = true) :
      Disjoint (S (a w)) (S (b w)) := by
    apply Finset.disjoint_left.mpr
    intro t ht ht'
    exact K.loopless.irrefl t (hjoin w hk hN hA t ht t ht')
  have hside (w : ℕ) (hk : k ≤ w) (hN : w < N) (hA : A w = true) :
      (S (a w)).card ≤ 1 ∨ (S (b w)).card ≤ 1 := by
    by_contra! hf
    obtain ⟨u,hu,v,hv,huv⟩ := Finset.one_lt_card.mp hf.1
    obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp hf.2
    have hJ := hjoin w hk hN hA
    exact hc4 u x v y huv hxy
      ⟨hJ u hu x hx, (hJ v hv x hx).symm, hJ v hv y hy, (hJ u hu y hy).symm⟩
  have births (u v : Fin n) (huv : G.Adj u v) :=
    edge_birth n k N r S R a b A u v hr (hrH u v huv)
      (by simp [hrS]) (by simp [hrS]) hinput ha hb horS horH handH hd
  have edgeCount := edge_finset_gate_bound_partial n k N K G S a b A hc4 hsmall
    (fun w hk hN => ⟨ha w hk hN, hb w hk hN⟩) hzero horS hjoin hside births
  obtain ⟨T,hT,hcard⟩ := cover_half n k N r G S R a b A hr hrS hrH hinput ha hb
    horS horH hside handH (fun f Q B step => dag_union_bound f Q B step)
  exact ⟨T,hT,by omega⟩

end PEqualNP.Outside.L_meta_1342_aux
