import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover

namespace PEqualNP.Outside.L_meta_1770_aux

lemma opposite_junk_not_and_paths
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO2 : IsAO2 n C) (a g h : ℕ)
    (ha : a ∈ tops G C) (hg : g ∈ junk G C) (hh : h ∈ junk G C)
    (hrg : OrReaches n C (opnd C a 0) g)
    (hrh : OrReaches n C (opnd C a 1) h) :
    (∃ x : Fin n → Bool, graphFun G ∅ x = false ∧
      gateVal n C g x = true ∧ gateVal n C h x = false) ∧
    (∃ x : Fin n → Bool, graphFun G ∅ x = false ∧
      gateVal n C g x = false ∧ gateVal n C h x = true) ∧
    ¬ OrReaches n C (n + g) h ∧ ¬ OrReaches n C (n + h) g ∧
    n + g ∉ (gateAt C h).inputs ∧ n + h ∉ (gateAt C g).inputs ∧
    ¬ Relation.TransGen (fun i j : ℕ => j < C.gates.length ∧
      (gateAt C j).op = GateOp.and ∧ n + i ∈ (gateAt C j).inputs) g h ∧
    ¬ Relation.TransGen (fun i j : ℕ => j < C.gates.length ∧
      (gateAt C j).op = GateOp.and ∧ n + i ∈ (gateAt C j).inputs) h g := by
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  obtain ⟨hAO, hRB, hlen2⟩ := hAO2
  let step : List Bool → Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have step_len : ∀ (w : List Bool) (g : Gate), (step w g).length = w.length + 1 := by
    intro w g
    change (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length = w.length + 1
    rw [List.length_append, List.length_singleton]
  have step_getD_lt : ∀ (w : List Bool) (g : Gate) (i : ℕ), i < w.length →
      (step w g).getD i false = w.getD i false := by
    intro w g i hi
    change (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).getD i false = w.getD i false
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hi, ← List.getD_eq_getElem?_getD]
  have step_getD_self : ∀ (w : List Bool) (g : Gate),
      (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
    intro w g
    change (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).getD w.length false = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, Nat.sub_self]
    rfl
  have getD_ge : ∀ (w : List Bool) (i : ℕ), w.length ≤ i → w.getD i false = false := by
    intro w i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
    rfl
  have foldl_len : ∀ (gs : List Gate) (w : List Bool),
      (gs.foldl step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil =>
      intro w
      rw [List.foldl_nil, List.length_nil, Nat.add_zero]
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih, step_len, List.length_cons]
      omega
  have foldl_getD_lt : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (gs.foldl step w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      rw [List.foldl_cons, ih (step w g) i (by rw [step_len]; omega)]
      exact step_getD_lt w g i hi
  have foldl_getD_gate : ∀ (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length),
      (gs.foldl step w).getD (w.length + j) false =
        (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
          if i < w.length + j then (gs.foldl step w).getD i false else false) := by
    intro gs
    induction gs with
    | nil =>
      intro w j hj
      rw [List.length_nil] at hj
      exact (Nat.not_lt_zero j hj).elim
    | cons g gs ih =>
      intro w j hj
      rw [List.foldl_cons]
      cases j with
      | zero =>
        rw [Nat.add_zero, foldl_getD_lt gs (step w g) w.length (by rw [step_len]; omega),
          step_getD_self]
        rw [List.getElem_cons_zero]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < w.length
        · rw [ite_eq_left_of_eq_true _ _ (eq_true hi),
            foldl_getD_lt gs (step w g) i (by rw [step_len]; omega), step_getD_lt w g i hi]
        · rw [ite_eq_right_of_eq_false _ _ (eq_false hi), getD_ge w i (Nat.le_of_not_lt hi)]
      | succ j =>
        have hj' : j < gs.length := Nat.lt_of_succ_lt_succ hj
        have key := ih (step w g) j hj'
        rw [step_len] at key
        have e : w.length + (j + 1) = w.length + 1 + j := by omega
        rw [List.getElem_cons_succ]
        change (gs.foldl step (step w g)).getD (w.length + (j + 1)) false = _
        rw [e]
        exact key
  have orStep_len : ∀ (cs : List (List ℕ)) (gt : Gate),
      (orStep n cs gt).length = cs.length + 1 := by
    intro cs gt
    change (cs ++ [cs.length :: (if gt.op = GateOp.or then
      (gt.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => cs.getD (w - n) [])
      else [])]).length = cs.length + 1
    rw [List.length_append, List.length_singleton]
  have orReaches_inv : ∀ (gs : List Gate) (w : List Bool) (cs : List (List ℕ)),
      w.length = n + cs.length →
      (∀ k < cs.length, ∀ g ∈ cs.getD k [], g < cs.length ∧
        (w.getD (n + g) false = true → w.getD (n + k) false = true)) →
      (gs.foldl step w).length = n + (gs.foldl (orStep n) cs).length ∧
      ∀ k < (gs.foldl (orStep n) cs).length,
        ∀ g ∈ (gs.foldl (orStep n) cs).getD k [],
          g < (gs.foldl (orStep n) cs).length ∧
            ((gs.foldl step w).getD (n + g) false = true →
              (gs.foldl step w).getD (n + k) false = true) := by
    intro gs
    induction gs with
    | nil => intro w cs hlen hinv; exact ⟨hlen, hinv⟩
    | cons gt gs ih =>
      intro w cs hlen hinv
      rw [List.foldl_cons, List.foldl_cons]
      refine ih (step w gt) (orStep n cs gt)
        (by rw [step_len, orStep_len, hlen]; omega) ?_
      intro k hk g hg
      rw [orStep_len] at hk
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hklt | hkeq
      · have hcs_eq : (orStep n cs gt).getD k [] = cs.getD k [] := by
          change (cs ++ [_]).getD k [] = cs.getD k []
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hklt,
            ← List.getD_eq_getElem?_getD]
        rw [hcs_eq] at hg
        obtain ⟨hg_lt, hval⟩ := hinv k hklt g hg
        refine ⟨by rw [orStep_len]; omega, fun hgv => ?_⟩
        rw [step_getD_lt w gt (n + g) (by omega)] at hgv
        rw [step_getD_lt w gt (n + k) (by omega)]
        exact hval hgv
      · subst hkeq
        have hcs_self : (orStep n cs gt).getD cs.length [] =
            cs.length :: (if gt.op = GateOp.or then
              (gt.inputs.filter (fun i => decide (n ≤ i ∧ i < n + cs.length))).flatMap
                (fun i => cs.getD (i - n) [])
              else []) := by
          change (cs ++ [_]).getD cs.length [] = _
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, Nat.sub_self]
          rfl
        rw [hcs_self, List.mem_cons] at hg
        rcases hg with rfl | hg
        · exact ⟨by rw [orStep_len]; omega, fun h => h⟩
        · split_ifs at hg with hop
          · rw [List.mem_flatMap] at hg
            obtain ⟨i, hi_filt, hg_mem⟩ := hg
            rw [List.mem_filter, decide_eq_true_eq] at hi_filt
            obtain ⟨hi_in, hni, hilt⟩ := hi_filt
            obtain ⟨hg_lt, hval⟩ := hinv (i - n) (by omega) g hg_mem
            refine ⟨by rw [orStep_len]; omega, fun hgv => ?_⟩
            rw [step_getD_lt w gt (n + g) (by omega)] at hgv
            have hwi : w.getD i false = true := by
              have heq : n + (i - n) = i := by omega
              rw [← heq]
              exact hval hgv
            rw [← hlen, step_getD_self, hop]
            change (gt.inputs.map fun k => w.getD k false).any id = true
            rw [List.any_map, List.any_eq_true]
            exact ⟨i, hi_in, hwi⟩
          · exact (List.not_mem_nil hg).elim
  have orReaches_up : ∀ (w g : ℕ) (x : Fin n → Bool),
      OrReaches n C w g → gateVal n C g x = true → wireVal n C w x = true := by
    intro w g x hor hgx
    obtain ⟨hnw, hmem⟩ := hor
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    rw [show n + k - n = k by omega] at hmem
    have empty_inv : ∀ k < ([] : List (List ℕ)).length,
        ∀ g ∈ ([] : List (List ℕ)).getD k [],
          g < ([] : List (List ℕ)).length ∧
            ((List.ofFn x).getD (n + g) false = true →
              (List.ofFn x).getD (n + k) false = true) := by
      intro k hk
      rw [List.length_nil] at hk
      exact (Nat.not_lt_zero k hk).elim
    have hinv_all := orReaches_inv C.gates (List.ofFn x) []
      (by rw [List.length_ofFn, List.length_nil, Nat.add_zero]) empty_inv
    have hlen_or : (orSets n C).length = C.gates.length := by
      have h1 := hinv_all.1
      have h2 := foldl_len C.gates (List.ofFn x)
      rw [List.length_ofFn] at h2
      change (C.gates.foldl step (List.ofFn x)).length = n + (orSets n C).length at h1
      change (C.gates.foldl (orStep n) []).length = C.gates.length
      omega
    by_cases hk : k < C.gates.length
    · have hk' : k < (orSets n C).length := by omega
      exact (hinv_all.2 k hk' g hmem).2 hgx
    · have hnone : (orSets n C).getD k [] = [] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
        rfl
      rw [hnone] at hmem
      exact (List.not_mem_nil hmem).elim
  have top_and_true : ∀ (a : ℕ) (x : Fin n → Bool),
      a ∈ tops G C →
      wireVal n C (opnd C a 0) x = true →
      wireVal n C (opnd C a 1) x = true →
      graphFun G ∅ x = true := by
    intro a x ha h0 h1
    obtain ⟨halen_m, haop, habel⟩ := Finset.mem_filter.mp
      (ha : a ∈ (Finset.range C.gates.length).filter
        (fun j => (gateAt C j).op = GateOp.and ∧ BelowF G C j))
    have halen : a < C.gates.length := Finset.mem_range.mp halen_m
    apply habel
    show (C.wires (List.ofFn x)).getD (n + a) false = true
    have hcw : C.wires (List.ofFn x) = C.gates.foldl step (List.ofFn x) := rfl
    rw [hcw]
    have hlenx : (List.ofFn x).length = n := List.length_ofFn
    have hgate := foldl_getD_gate C.gates (List.ofFn x) a halen
    rw [hlenx] at hgate
    rw [hgate]
    have hge : gateAt C a = C.gates[a] := by
      change C.gates.getD a ⟨GateOp.or, []⟩ = C.gates[a]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem halen]
      rfl
    have hga : C.gates[a] ∈ C.gates := List.getElem_mem halen
    obtain ⟨p, q, hpq⟩ := List.length_eq_two.mp (hlen2 _ hga)
    have ep : opnd C a 0 = p := by
      change (gateAt C a).inputs.getD 0 0 = p
      rw [hge, hpq]
      rfl
    have eq : opnd C a 1 = q := by
      change (gateAt C a).inputs.getD 1 0 = q
      rw [hge, hpq]
      rfl
    have hp_lt : p < n + a := hRB a halen p (by rw [hge, hpq]; exact List.mem_cons_self)
    have hq_lt : q < n + a := hRB a halen q
      (by rw [hge, hpq]; exact List.mem_cons_of_mem p List.mem_cons_self)
    rw [← hge, haop, hge, hpq]
    change (if p < n + a then (C.gates.foldl step (List.ofFn x)).getD p false else false) &&
      ((if q < n + a then (C.gates.foldl step (List.ofFn x)).getD q false else false) && true) = true
    rw [Bool.and_true, ite_eq_left_of_eq_true _ _ (eq_true hp_lt),
      ite_eq_left_of_eq_true _ _ (eq_true hq_lt), ← ep, ← eq]
    exact Bool.and_eq_true_iff.mpr ⟨h0, h1⟩
  have dirty_witness : ∀ j ∈ junk G C,
      ∃ x : Fin n → Bool, gateVal n C j x = true ∧ graphFun G ∅ x = false := by
    intro j hj
    exact (Finset.mem_filter.mp hj).2.2.2
  obtain ⟨x, hxg, hxF⟩ := dirty_witness g hg
  obtain ⟨y, hyh, hyF⟩ := dirty_witness h hh
  have hxh : gateVal n C h x = false := by
    apply Bool.eq_false_iff.mpr
    intro ht
    have hFx := top_and_true a x ha
      (orReaches_up (opnd C a 0) g x hrg hxg)
      (orReaches_up (opnd C a 1) h x hrh ht)
    rw [hxF] at hFx
    cases hFx
  have hyg : gateVal n C g y = false := by
    apply Bool.eq_false_iff.mpr
    intro ht
    have hFy := top_and_true a y ha
      (orReaches_up (opnd C a 0) g y hrg ht)
      (orReaches_up (opnd C a 1) h y hrh hyh)
    rw [hyF] at hFy
    cases hFy
  have hnotgh : ¬ OrReaches n C (n + g) h := by
    intro hr
    have hygt : gateVal n C g y = true := orReaches_up (n + g) h y hr hyh
    rw [hyg] at hygt
    cases hygt
  have hnothg : ¬ OrReaches n C (n + h) g := by
    intro hr
    have hxht : gateVal n C h x = true := orReaches_up (n + h) g x hr hxg
    rw [hxh] at hxht
    cases hxht
  have and_true_inputs : ∀ (j : ℕ), j < C.gates.length →
      (gateAt C j).op = GateOp.and → ∀ (z : Fin n → Bool),
      gateVal n C j z = true → ∀ i ∈ (gateAt C j).inputs,
      wireVal n C i z = true := by
    intro j hj hop z hz i hi
    have hge : gateAt C j = C.gates[j] := by
      change C.gates.getD j ⟨GateOp.or, []⟩ = C.gates[j]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
      rfl
    have hgate := foldl_getD_gate C.gates (List.ofFn z) j hj
    rw [List.length_ofFn] at hgate
    change (C.gates.foldl step (List.ofFn z)).getD (n + j) false = true at hz
    rw [hgate, ← hge, hop] at hz
    change ((gateAt C j).inputs.map fun t =>
      if t < n + j then (C.gates.foldl step (List.ofFn z)).getD t false else false).all id = true at hz
    rw [List.all_map, List.all_eq_true] at hz
    have hval := hz i hi
    by_cases hilt : i < n + j
    · change (C.gates.foldl step (List.ofFn z)).getD i false = true
      simpa [hilt] using hval
    · simp [hilt] at hval
  have hgm : g < C.gates.length ∧ (gateAt C g).op = GateOp.and := by
    have hmem := Finset.mem_filter.mp hg
    exact ⟨Finset.mem_range.mp hmem.1, hmem.2.1⟩
  have hhm : h < C.gates.length ∧ (gateAt C h).op = GateOp.and := by
    have hmem := Finset.mem_filter.mp hh
    exact ⟨Finset.mem_range.mp hmem.1, hmem.2.1⟩
  have hdgh : n + g ∉ (gateAt C h).inputs := by
    intro hin
    have hygt : gateVal n C g y = true := and_true_inputs h hhm.1 hhm.2 y hyh (n + g) hin
    rw [hyg] at hygt
    cases hygt
  have hdhg : n + h ∉ (gateAt C g).inputs := by
    intro hin
    have hxht : gateVal n C h x = true := and_true_inputs g hgm.1 hgm.2 x hxg (n + h) hin
    rw [hxh] at hxht
    cases hxht
  have and_path_down : ∀ (i j : ℕ),
      Relation.TransGen (fun i j : ℕ => j < C.gates.length ∧
        (gateAt C j).op = GateOp.and ∧ n + i ∈ (gateAt C j).inputs) i j →
      ∀ z : Fin n → Bool, gateVal n C j z = true → gateVal n C i z = true := by
    intro i j hp
    induction hp with
    | single hs =>
      intro z hz
      exact and_true_inputs _ hs.1 hs.2.1 z hz _ hs.2.2
    | tail hp hs ih =>
      intro z hz
      exact ih z (and_true_inputs _ hs.1 hs.2.1 z hz _ hs.2.2)
  have hpathgh : ¬ Relation.TransGen (fun i j : ℕ => j < C.gates.length ∧
      (gateAt C j).op = GateOp.and ∧ n + i ∈ (gateAt C j).inputs) g h := by
    intro hp
    have hygt := and_path_down g h hp y hyh
    rw [hyg] at hygt
    cases hygt
  have hpathhg : ¬ Relation.TransGen (fun i j : ℕ => j < C.gates.length ∧
      (gateAt C j).op = GateOp.and ∧ n + i ∈ (gateAt C j).inputs) h g := by
    intro hp
    have hxht := and_path_down h g hp x hxg
    rw [hxh] at hxht
    cases hxht
  exact ⟨⟨x, hxF, hxg, hxh⟩, ⟨y, hyF, hyg, hyh⟩, hnotgh, hnothg, hdgh, hdhg,
    hpathgh, hpathhg⟩

end PEqualNP.Outside.L_meta_1770_aux
