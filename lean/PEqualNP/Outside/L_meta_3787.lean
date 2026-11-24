import Mathlib.Data.List.GetD
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3787

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def incidenceStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def incidenceSuffix (n : ℕ) : List Gate :=
  [⟨GateOp.or, [13, 14]⟩,
   ⟨GateOp.or, [16, 22]⟩,
   ⟨GateOp.or, [n, n + 1]⟩,
   ⟨GateOp.and, [0, n + 2]⟩,
   ⟨GateOp.or, [13, 15]⟩,
   ⟨GateOp.or, [21, 25]⟩,
   ⟨GateOp.or, [n + 4, n + 5]⟩,
   ⟨GateOp.and, [1, n + 6]⟩,
   ⟨GateOp.or, [13, 19]⟩,
   ⟨GateOp.or, [23, 24]⟩,
   ⟨GateOp.or, [n + 8, n + 9]⟩,
   ⟨GateOp.and, [3, n + 10]⟩,
   ⟨GateOp.or, [13, 17]⟩,
   ⟨GateOp.or, [18, 20]⟩,
   ⟨GateOp.or, [n + 12, n + 13]⟩,
   ⟨GateOp.and, [9, n + 14]⟩,
   ⟨GateOp.or, [n + 3, n + 7]⟩,
   ⟨GateOp.or, [n + 11, n + 15]⟩,
   ⟨GateOp.or, [n + 16, n + 17]⟩]

def incidenceFormula (w : ℕ → Bool) : Bool :=
  ((w 0 && ((w 13 || w 14) || (w 16 || w 22))) ||
   (w 1 && ((w 13 || w 15) || (w 21 || w 25)))) ||
  ((w 3 && ((w 13 || w 19) || (w 23 || w 24))) ||
   (w 9 && ((w 13 || w 17) || (w 18 || w 20))))

lemma incidenceSuffix_length (n : ℕ) : (incidenceSuffix n).length = 19 := rfl

lemma incidenceSuffix_monotone (n : ℕ) :
    ∀ g ∈ incidenceSuffix n,
      g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [incidenceSuffix, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

lemma incidenceGetD_append (w t : List Bool) (i : ℕ) :
    (w ++ t).getD i false =
      if i < w.length then w.getD i false else t.getD (i - w.length) false := by
  by_cases hi : i < w.length
  · rw [if_pos hi, List.getD_append _ _ _ _ hi]
  · rw [if_neg hi, List.getD_append_right _ _ _ _ (by omega)]

set_option maxHeartbeats 800000 in
lemma incidenceSuffix_eval (w : List Bool) (hw : 26 ≤ w.length) :
    ((incidenceSuffix w.length).foldl incidenceStep w).getD (w.length + 18) false =
      incidenceFormula (fun i => w.getD i false) := by
  let v0 := w.getD 13 false || w.getD 14 false
  let v1 := w.getD 16 false || w.getD 22 false
  let v2 := v0 || v1
  let v3 := w.getD 0 false && v2
  let v4 := w.getD 13 false || w.getD 15 false
  let v5 := w.getD 21 false || w.getD 25 false
  let v6 := v4 || v5
  let v7 := w.getD 1 false && v6
  let v8 := w.getD 13 false || w.getD 19 false
  let v9 := w.getD 23 false || w.getD 24 false
  let v10 := v8 || v9
  let v11 := w.getD 3 false && v10
  let v12 := w.getD 13 false || w.getD 17 false
  let v13 := w.getD 18 false || w.getD 20 false
  let v14 := v12 || v13
  let v15 := w.getD 9 false && v14
  let v16 := v3 || v7
  let v17 := v11 || v15
  let v18 := v16 || v17
  unfold incidenceSuffix
  have s0 : incidenceStep w ⟨GateOp.or, [13, 14]⟩ = w ++ [v0] := by
    simp (disch := omega) [incidenceStep, GateOp.eval, -List.getD_eq_getElem?_getD, List.getD_append, List.getD_append_right, List.getD_cons_zero, List.getD_cons_succ, v0,
      List.append_assoc]
  rw [List.foldl_cons, s0]
  have s1 : incidenceStep (w ++ [v0]) ⟨GateOp.or, [16, 22]⟩ = w ++ [v0, v1] := by
    simp (disch := omega) [incidenceStep, GateOp.eval, -List.getD_eq_getElem?_getD, List.getD_append, List.getD_append_right, List.getD_cons_zero, List.getD_cons_succ, v1,
      List.append_assoc]
  rw [List.foldl_cons, s1]
  have s2 : incidenceStep (w ++ [v0, v1]) ⟨GateOp.or, [w.length, w.length + 1]⟩ = w ++ [v0, v1, v2] := by
    simp (disch := omega) [incidenceStep, GateOp.eval, -List.getD_eq_getElem?_getD, List.getD_append, List.getD_append_right, List.getD_cons_zero, List.getD_cons_succ, v2,
      List.append_assoc]
  rw [List.foldl_cons, s2]
  have s3 : incidenceStep (w ++ [v0, v1, v2]) ⟨GateOp.and, [0, w.length + 2]⟩ = w ++ [v0, v1, v2, v3] := by
    simp (disch := omega) [incidenceStep, GateOp.eval, -List.getD_eq_getElem?_getD, List.getD_append, List.getD_append_right, List.getD_cons_zero, List.getD_cons_succ, v3,
      List.append_assoc]
  rw [List.foldl_cons, s3]
  have s4 : incidenceStep (w ++ [v0, v1, v2, v3]) ⟨GateOp.or, [13, 15]⟩ = w ++ [v0, v1, v2, v3, v4] := by
    simp (disch := omega) [incidenceStep, GateOp.eval, -List.getD_eq_getElem?_getD, List.getD_append, List.getD_append_right, List.getD_cons_zero, List.getD_cons_succ, v4,
      List.append_assoc]
  rw [List.foldl_cons, s4]
  have s5 : incidenceStep (w ++ [v0, v1, v2, v3, v4]) ⟨GateOp.or, [21, 25]⟩ = w ++ [v0, v1, v2, v3, v4, v5] := by
    simp (disch := omega) [incidenceStep, GateOp.eval, -List.getD_eq_getElem?_getD, List.getD_append, List.getD_append_right, List.getD_cons_zero, List.getD_cons_succ, v5,
      List.append_assoc]
  rw [List.foldl_cons, s5]
  have s6 : incidenceStep (w ++ [v0, v1, v2, v3, v4, v5]) ⟨GateOp.or, [w.length + 4, w.length + 5]⟩ = w ++ [v0, v1, v2, v3, v4, v5, v6] := by
    simp (disch := omega) [incidenceStep, GateOp.eval, -List.getD_eq_getElem?_getD, List.getD_append, List.getD_append_right, List.getD_cons_zero, List.getD_cons_succ, v6,
      List.append_assoc]
  rw [List.foldl_cons, s6]
  have s7 : incidenceStep (w ++ [v0, v1, v2, v3, v4, v5, v6]) ⟨GateOp.and, [1, w.length + 6]⟩ = w ++ [v0, v1, v2, v3, v4, v5, v6, v7] := by
    simp (disch := omega) [incidenceStep, GateOp.eval, -List.getD_eq_getElem?_getD, List.getD_append, List.getD_append_right, List.getD_cons_zero, List.getD_cons_succ, v7,
      List.append_assoc]
  rw [List.foldl_cons, s7]
  have s8 : incidenceStep (w ++ [v0, v1, v2, v3, v4, v5, v6, v7]) ⟨GateOp.or, [13, 19]⟩ = w ++ [v0, v1, v2, v3, v4, v5, v6, v7, v8] := by
    simp (disch := omega) [incidenceStep, GateOp.eval, -List.getD_eq_getElem?_getD, List.getD_append, List.getD_append_right, List.getD_cons_zero, List.getD_cons_succ, v8,
      List.append_assoc]
  rw [List.foldl_cons, s8]
  have s9 : incidenceStep (w ++ [v0, v1, v2, v3, v4, v5, v6, v7, v8]) ⟨GateOp.or, [23, 24]⟩ = w ++ [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9] := by
    simp (disch := omega) [incidenceStep, GateOp.eval, -List.getD_eq_getElem?_getD, List.getD_append, List.getD_append_right, List.getD_cons_zero, List.getD_cons_succ, v9,
      List.append_assoc]
  rw [List.foldl_cons, s9]
  have s10 : incidenceStep (w ++ [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9]) ⟨GateOp.or, [w.length + 8, w.length + 9]⟩ = w ++ [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10] := by
    simp (disch := omega) [incidenceStep, GateOp.eval, -List.getD_eq_getElem?_getD, List.getD_append, List.getD_append_right, List.getD_cons_zero, List.getD_cons_succ, v10,
      List.append_assoc]
  rw [List.foldl_cons, s10]
  have s11 : incidenceStep (w ++ [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10]) ⟨GateOp.and, [3, w.length + 10]⟩ = w ++ [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11] := by
    simp (disch := omega) [incidenceStep, GateOp.eval, -List.getD_eq_getElem?_getD, List.getD_append, List.getD_append_right, List.getD_cons_zero, List.getD_cons_succ, v11,
      List.append_assoc]
  rw [List.foldl_cons, s11]
  have s12 : incidenceStep (w ++ [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11]) ⟨GateOp.or, [13, 17]⟩ = w ++ [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12] := by
    simp (disch := omega) [incidenceStep, GateOp.eval, -List.getD_eq_getElem?_getD, List.getD_append, List.getD_append_right, List.getD_cons_zero, List.getD_cons_succ, v12,
      List.append_assoc]
  rw [List.foldl_cons, s12]
  have s13 : incidenceStep (w ++ [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12]) ⟨GateOp.or, [18, 20]⟩ = w ++ [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13] := by
    simp (disch := omega) [incidenceStep, GateOp.eval, -List.getD_eq_getElem?_getD, List.getD_append, List.getD_append_right, List.getD_cons_zero, List.getD_cons_succ, v13,
      List.append_assoc]
  rw [List.foldl_cons, s13]
  have s14 : incidenceStep (w ++ [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13]) ⟨GateOp.or, [w.length + 12, w.length + 13]⟩ = w ++ [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14] := by
    simp (disch := omega) [incidenceStep, GateOp.eval, -List.getD_eq_getElem?_getD, List.getD_append, List.getD_append_right, List.getD_cons_zero, List.getD_cons_succ, v14,
      List.append_assoc]
  rw [List.foldl_cons, s14]
  have s15 : incidenceStep (w ++ [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14]) ⟨GateOp.and, [9, w.length + 14]⟩ = w ++ [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] := by
    simp (disch := omega) [incidenceStep, GateOp.eval, -List.getD_eq_getElem?_getD, List.getD_append, List.getD_append_right, List.getD_cons_zero, List.getD_cons_succ, v15,
      List.append_assoc]
  rw [List.foldl_cons, s15]
  have s16 : incidenceStep (w ++ [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15]) ⟨GateOp.or, [w.length + 3, w.length + 7]⟩ = w ++ [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16] := by
    simp (disch := omega) [incidenceStep, GateOp.eval, -List.getD_eq_getElem?_getD, List.getD_append, List.getD_append_right, List.getD_cons_zero, List.getD_cons_succ, v16,
      List.append_assoc]
  rw [List.foldl_cons, s16]
  have s17 : incidenceStep (w ++ [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16]) ⟨GateOp.or, [w.length + 11, w.length + 15]⟩ = w ++ [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17] := by
    simp (disch := omega) [incidenceStep, GateOp.eval, -List.getD_eq_getElem?_getD, List.getD_append, List.getD_append_right, List.getD_cons_zero, List.getD_cons_succ, v17,
      List.append_assoc]
  rw [List.foldl_cons, s17]
  have s18 : incidenceStep (w ++ [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17]) ⟨GateOp.or, [w.length + 16, w.length + 17]⟩ = w ++ [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18] := by
    simp (disch := omega) [incidenceStep, GateOp.eval, -List.getD_eq_getElem?_getD, List.getD_append, List.getD_append_right, List.getD_cons_zero, List.getD_cons_succ, v18,
      List.append_assoc]
  rw [List.foldl_cons, s18]
  rw [List.foldl_nil]
  simp [-List.getD_eq_getElem?_getD, List.getD_append, List.getD_append_right, List.getD_cons_zero, List.getD_cons_succ, incidenceFormula, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18]

lemma incidenceRun_prefix (gs : List Gate) (w : List Bool) :
    ∃ t : List Bool,
      gs.foldl incidenceStep w = w ++ t ∧ t.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    obtain ⟨t, ht, hl⟩ := ih (incidenceStep w g)
    refine ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ t, ?_, ?_⟩
    · simpa [incidenceStep, List.append_assoc] using ht
    · simp [hl]

lemma incidenceRun_length (gs : List Gate) (w : List Bool) :
    (gs.foldl incidenceStep w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := incidenceRun_prefix gs w
  simp [ht, hl]

lemma incidenceGetD_last (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp [List.getD_eq_getElem?_getD]

def incidenceExtension (n acc : ℕ) : List Gate :=
  incidenceSuffix n ++ [⟨GateOp.or, [acc, n + 18]⟩]

lemma incidenceExtension_length (n acc : ℕ) :
    (incidenceExtension n acc).length = 20 := by
  simp [incidenceExtension, incidenceSuffix_length]

lemma incidenceExtension_monotone (n acc : ℕ) :
    ∀ g ∈ incidenceExtension n acc,
      g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  rcases List.mem_append.mp hg with h | h
  · exact incidenceSuffix_monotone n g h
  · simp only [List.mem_singleton] at h
    subst g
    simp

lemma incidenceExtension_eval (w : List Bool) (acc : ℕ)
    (hw : 26 ≤ w.length) (ha : acc < w.length) :
    ((incidenceExtension w.length acc).foldl incidenceStep w).getD (w.length + 19) false =
      (w.getD acc false || incidenceFormula (fun i => w.getD i false)) := by
  obtain ⟨t, ht, _⟩ := incidenceRun_prefix (incidenceSuffix w.length) w
  have hacc : ((incidenceSuffix w.length).foldl incidenceStep w).getD acc false =
      w.getD acc false := by
    rw [ht, List.getD_append _ _ _ _ ha]
  have hlen : ((incidenceSuffix w.length).foldl incidenceStep w).length = w.length + 19 := by
    rw [incidenceRun_length, incidenceSuffix_length]
  simp only [incidenceExtension, List.foldl_append, List.foldl_cons, List.foldl_nil,
    incidenceStep]
  rw [← hlen, incidenceGetD_last]
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
    id_eq, Bool.or_false]
  rw [hacc, incidenceSuffix_eval w hw]

def extendIncidence (c : Circuit) (n : ℕ) : Circuit :=
  ⟨c.gates ++ incidenceExtension (n + c.size) c.output, n + c.size + 19⟩

lemma extendIncidence_size (c : Circuit) (n : ℕ) :
    (extendIncidence c n).size = c.size + 20 := by
  simp [extendIncidence, Circuit.size, incidenceExtension_length]

lemma extendIncidence_monotone (c : Circuit) (n : ℕ) (hc : Monotone2 c) :
    Monotone2 (extendIncidence c n) := by
  intro g hg
  rcases List.mem_append.mp hg with h | h
  · exact hc g h
  · exact incidenceExtension_monotone _ _ g h


lemma extendIncidence_eval (c : Circuit) (x : List Bool)
    (hx : 26 ≤ x.length) (ho : c.output < x.length + c.size) :
    (extendIncidence c x.length).eval x =
      (c.eval x || incidenceFormula (fun i => x.getD i false)) := by
  have hlen : (c.gates.foldl incidenceStep x).length = x.length + c.size :=
    incidenceRun_length c.gates x
  have hw : 26 ≤ (c.gates.foldl incidenceStep x).length := by omega
  have ha : c.output < (c.gates.foldl incidenceStep x).length := by omega
  have he := incidenceExtension_eval (c.gates.foldl incidenceStep x) c.output hw ha
  rw [hlen] at he
  change ((c.gates ++ incidenceExtension (x.length + c.size) c.output).foldl
      incidenceStep x).getD (x.length + c.size + 19) false = _
  rw [List.foldl_append, he]
  apply congrArg (fun b => c.eval x || b)
  obtain ⟨t, ht, _⟩ := incidenceRun_prefix c.gates x
  rw [ht]
  simp (disch := omega) [-List.getD_eq_getElem?_getD, incidenceFormula, List.getD_append]


end PEqualNP.Outside.L_meta_3787
