import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4045_2
    (h1 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : (Fin (26 : ℕ) → Bool) → ℕ → Bool),
      (∀ v : Fin (26 : ℕ), (x1.gates.filter (fun g => v.val ∈ g.inputs)).length ≤ 4) →
      x1.size ≤ 60 →
      (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (26 : ℕ) + x3 ∧ x7 < (26 : ℕ) + x3) →
      (∀ (x5 : Fin (26 : ℕ) → Bool) (x6 : ℕ), x2 x5 x6 = (x1.wires (List.ofFn x5)).getD x6 Bool.false) →
      (∀ (x6 : Fin (26 : ℕ) → Bool), x2 x6 x1.output = Bool.true ↔ ∃ (x7 : Fin (13 : ℕ)) (x8 : Fin (13 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (13 : ℕ)) ∨ x7 = x8 + (3 : Fin (13 : ℕ)) ∨ x7 = x8 + (9 : Fin (13 : ℕ))) ∧ x6 (Fin.castAdd (13 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (13 : ℕ) x8) = Bool.true) →
      ∃ (x7 : Fin (26 : ℕ)) (x8 : Finset ℕ), (5 : ℕ) ≤ x8.card ∧ ∀ x9 ∈ x8, x9 < x1.size ∧ ∃ (x11 : Bool) (x12 : Bool), ∃ x13 < (26 : ℕ) + x9, ∀ (x14 : Fin (26 : ℕ) → Bool), x14 x7 = Bool.false → x2 x14 ((26 : ℕ) + x9) = (x11 && x2 x14 x13 || x12))
    (h2 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : (Fin (26 : ℕ) → Bool) → ℕ → Bool),
      (∀ v : Fin (26 : ℕ), (x1.gates.filter (fun g => v.val ∈ g.inputs)).length ≤ 4) →
      x1.size = 61 →
      (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (26 : ℕ) + x3 ∧ x7 < (26 : ℕ) + x3) →
      (∀ (x5 : Fin (26 : ℕ) → Bool) (x6 : ℕ), x2 x5 x6 = (x1.wires (List.ofFn x5)).getD x6 Bool.false) →
      (∀ (x6 : Fin (26 : ℕ) → Bool), x2 x6 x1.output = Bool.true ↔ ∃ (x7 : Fin (13 : ℕ)) (x8 : Fin (13 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (13 : ℕ)) ∨ x7 = x8 + (3 : Fin (13 : ℕ)) ∨ x7 = x8 + (9 : Fin (13 : ℕ))) ∧ x6 (Fin.castAdd (13 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (13 : ℕ) x8) = Bool.true) →
      ∃ (x7 : Fin (26 : ℕ)) (x8 : Finset ℕ), (5 : ℕ) ≤ x8.card ∧ ∀ x9 ∈ x8, x9 < x1.size ∧ ∃ (x11 : Bool) (x12 : Bool), ∃ x13 < (26 : ℕ) + x9, ∀ (x14 : Fin (26 : ℕ) → Bool), x14 x7 = Bool.false → x2 x14 ((26 : ℕ) + x9) = (x11 && x2 x14 x13 || x12))
    (h3 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : (Fin (26 : ℕ) → Bool) → ℕ → Bool),
      (∀ v : Fin (26 : ℕ), (x1.gates.filter (fun g => v.val ∈ g.inputs)).length ≤ 4) →
      x1.size = 62 →
      (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (26 : ℕ) + x3 ∧ x7 < (26 : ℕ) + x3) →
      (∀ (x5 : Fin (26 : ℕ) → Bool) (x6 : ℕ), x2 x5 x6 = (x1.wires (List.ofFn x5)).getD x6 Bool.false) →
      (∀ (x6 : Fin (26 : ℕ) → Bool), x2 x6 x1.output = Bool.true ↔ ∃ (x7 : Fin (13 : ℕ)) (x8 : Fin (13 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (13 : ℕ)) ∨ x7 = x8 + (3 : Fin (13 : ℕ)) ∨ x7 = x8 + (9 : Fin (13 : ℕ))) ∧ x6 (Fin.castAdd (13 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (13 : ℕ) x8) = Bool.true) →
      ∃ (x7 : Fin (26 : ℕ)) (x8 : Finset ℕ), (5 : ℕ) ≤ x8.card ∧ ∀ x9 ∈ x8, x9 < x1.size ∧ ∃ (x11 : Bool) (x12 : Bool), ∃ x13 < (26 : ℕ) + x9, ∀ (x14 : Fin (26 : ℕ) → Bool), x14 x7 = Bool.false → x2 x14 ((26 : ℕ) + x9) = (x11 && x2 x14 x13 || x12)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : (Fin (26 : ℕ) → Bool) → ℕ → Bool), (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (26 : ℕ) + x3 ∧ x7 < (26 : ℕ) + x3) → x1.size ≤ (62 : ℕ) → (∀ (x5 : Fin (26 : ℕ) → Bool) (x6 : ℕ), x2 x5 x6 = (x1.wires (List.ofFn x5)).getD x6 Bool.false) → (∀ (x6 : Fin (26 : ℕ) → Bool), x2 x6 x1.output = Bool.true ↔ ∃ (x7 : Fin (13 : ℕ)) (x8 : Fin (13 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (13 : ℕ)) ∨ x7 = x8 + (3 : Fin (13 : ℕ)) ∨ x7 = x8 + (9 : Fin (13 : ℕ))) ∧ x6 (Fin.castAdd (13 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (13 : ℕ) x8) = Bool.true) → ∃ (x7 : Fin (26 : ℕ)) (x8 : Finset ℕ), (5 : ℕ) ≤ x8.card ∧ ∀ x9 ∈ x8, x9 < x1.size ∧ ∃ (x11 : Bool) (x12 : Bool), ∃ x13 < (26 : ℕ) + x9, ∀ (x14 : Fin (26 : ℕ) → Bool), x14 x7 = Bool.false → x2 x14 ((26 : ℕ) + x9) = (x11 && x2 x14 x13 || x12) := by
  intro C W hlegal hsz hval hcomp
  by_cases hdeg : ∃ v : Fin 26, 5 ≤ (C.gates.filter (fun g => decide (v.val ∈ g.inputs))).length
  · obtain ⟨v, hv⟩ := hdeg
    let x8 : Finset ℕ := (Finset.range C.size).filter (fun j => v.val ∈ (C.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs)
    have hcard : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate),
        ((Finset.range gs.length).filter (fun j => v.val ∈ (gs.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs)).card =
        (gs.filter (fun g => decide (v.val ∈ g.inputs))).length := by
      intro gs
      induction gs using List.reverseRecOn with
      | nil => simp
      | append_singleton gs g ih =>
        rw [List.length_append, List.length_singleton, Finset.range_add_one, Finset.filter_insert,
          List.filter_append, List.filter_cons, List.filter_nil, List.length_append]
        have hget : ∀ j < gs.length,
            ((gs ++ [g]).getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩) =
              gs.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ := by
          intro j hj
          simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
        have hlast : (gs ++ [g]).getD gs.length ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = g := by
          simp [List.getD_eq_getElem?_getD]
        have hfilt : (Finset.range gs.length).filter (fun j => v.val ∈ ((gs ++ [g]).getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs) =
            (Finset.range gs.length).filter (fun j => v.val ∈ (gs.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_range]
          constructor
          · rintro ⟨hj, hmem⟩; exact ⟨hj, by rwa [hget j hj] at hmem⟩
          · rintro ⟨hj, hmem⟩; exact ⟨hj, by rwa [hget j hj]⟩
        by_cases hmem : v.val ∈ g.inputs
        · rw [ite_eq_left (by simpa [hlast] using hmem), Finset.card_insert_of_notMem (by simp), hfilt, ih]
          simp [hmem]
        · rw [ite_eq_right (by simpa [hlast] using hmem), hfilt, ih]
          simp [hmem]
    have hx8_card : 5 ≤ x8.card := by
      change 5 ≤ ((Finset.range C.gates.length).filter _).card
      rw [hcard C.gates]
      exact hv
    have hwires_append : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (init : List Bool),
        ∃ ext : List Bool, gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) init = init ++ ext ∧ ext.length = gs.length := by
      intro gs
      induction gs with
      | nil => intro init; exact ⟨[], by simp, rfl⟩
      | cons g gs ih =>
        intro init
        simp only [List.foldl_cons]
        obtain ⟨ext, heq, hlen⟩ := ih (init ++ [g.op.eval (g.inputs.map fun i => init.getD i false)])
        exact ⟨[g.op.eval (g.inputs.map fun i => init.getD i false)] ++ ext, by rw [heq, List.append_assoc], by simp [hlen]⟩
    have hval_lt : ∀ (x : Fin 26 → Bool) (w : ℕ) (hw : w < 26), W x w = x ⟨w, hw⟩ := by
      intro x w hw
      rw [hval]
      unfold PEqualNP.CircuitLowerBounds.Circuit.wires
      obtain ⟨ext, heq, _⟩ := hwires_append C.gates (List.ofFn x)
      rw [heq, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hw]), List.getElem?_eq_getElem (by simp [hw])]
      exact List.getElem_ofFn ..
    have hval_gate : ∀ (x : Fin 26 → Bool) (j : ℕ) (hj : j < C.gates.length)
        (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g →
        (∀ i ∈ g.inputs, i < 26 + j) →
        W x (26 + j) = g.op.eval (g.inputs.map (W x)) := by
      intro x j hj g hgj hlt
      rw [hval]
      unfold PEqualNP.CircuitLowerBounds.Circuit.wires
      have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
        have h1 := List.take_append_drop j C.gates
        rw [List.drop_eq_getElem_cons hj] at h1
        exact h1.symm
      set w_j := (C.gates.take j).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x)
      have hfold : C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x) =
          (C.gates.drop (j + 1)).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
            (w_j ++ [C.gates[j].op.eval (C.gates[j].inputs.map fun i => w_j.getD i false)]) := by
        conv_lhs => rw [hsplit]
        rw [List.foldl_append, List.foldl_cons]
      obtain ⟨ext, heq, _⟩ := hwires_append (C.gates.drop (j + 1)) (w_j ++ [C.gates[j].op.eval (C.gates[j].inputs.map fun i => w_j.getD i false)])
      obtain ⟨ext', heq', hlen'⟩ := hwires_append (C.gates.take j) (List.ofFn x)
      have hwj_len : w_j.length = 26 + j := by
        change w_j = List.ofFn x ++ ext' at heq'
        rw [heq', List.length_append, List.length_ofFn, hlen', List.length_take, Nat.min_eq_left hj.le]
      have hge_eq : C.gates[j] = g := by
        rw [List.getElem?_eq_getElem hj] at hgj
        exact Option.some.inj hgj
      rw [hfold, heq, List.getD_eq_getElem?_getD, List.append_assoc, List.getElem?_append_right (by omega)]
      rw [hwj_len, Nat.sub_self]
      simp only [List.cons_append, List.getElem?_cons_zero, Option.getD_some, hge_eq]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hi_lt : i < 26 + j := hlt i (hge_eq ▸ hi)
      rw [hval]
      unfold PEqualNP.CircuitLowerBounds.Circuit.wires
      rw [hfold, heq, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.append_assoc,
        List.getElem?_append_left (by omega)]
    refine ⟨v, x8, hx8_card, fun j hj => ?_⟩
    simp only [x8, Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨hj_lt, hj_mem⟩ := hj
    have hj_some : C.gates[j]? = some (C.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩) := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj_lt]
    set g := C.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩
    obtain ⟨hop, a, b, hinp, hab, ha_lt, hb_lt⟩ := hlegal j g hj_some
    have hlt_all : ∀ i ∈ g.inputs, i < 26 + j := by
      intro i hi
      rw [hinp] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> assumption
    rw [hinp] at hj_mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj_mem
    refine ⟨hj_lt, ?_⟩
    rcases hj_mem with ha_eq | hb_eq
    · rcases hop with hand | hor
      · refine ⟨false, false, b, hb_lt, fun x14 hx14 => ?_⟩
        rw [hval_gate x14 j hj_lt g hj_some hlt_all, hand, hinp]
        have heval : PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (W x14) [a, b]) = (W x14 a && (W x14 b && true)) := rfl
        rw [heval, ← ha_eq, hval_lt x14 v.val v.isLt, hx14]
        simp
      · refine ⟨true, false, b, hb_lt, fun x14 hx14 => ?_⟩
        rw [hval_gate x14 j hj_lt g hj_some hlt_all, hor, hinp]
        have heval : PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (W x14) [a, b]) = (W x14 a || (W x14 b || false)) := rfl
        rw [heval, ← ha_eq, hval_lt x14 v.val v.isLt, hx14]
        simp
    · rcases hop with hand | hor
      · refine ⟨false, false, a, ha_lt, fun x14 hx14 => ?_⟩
        rw [hval_gate x14 j hj_lt g hj_some hlt_all, hand, hinp]
        have heval : PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (W x14) [a, b]) = (W x14 a && (W x14 b && true)) := rfl
        rw [heval, ← hb_eq, hval_lt x14 v.val v.isLt, hx14]
        simp
      · refine ⟨true, false, a, ha_lt, fun x14 hx14 => ?_⟩
        rw [hval_gate x14 j hj_lt g hj_some hlt_all, hor, hinp]
        have heval : PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (W x14) [a, b]) = (W x14 a || (W x14 b || false)) := rfl
        rw [heval, ← hb_eq, hval_lt x14 v.val v.isLt, hx14]
        simp
  · have hdeg_le : ∀ v : Fin 26, (C.gates.filter (fun g => v.val ∈ g.inputs)).length ≤ 4 := by
      intro v
      by_contra hgt
      exact hdeg ⟨v, by simpa using Nat.succ_le_of_lt (Nat.lt_of_not_le hgt)⟩
    by_cases h60 : C.size ≤ 60
    · exact h1 C W hdeg_le h60 hlegal hval hcomp
    · by_cases h61 : C.size = 61
      · exact h2 C W hdeg_le h61 hlegal hval hcomp
      · exact h3 C W hdeg_le (by omega) hlegal hval hcomp
