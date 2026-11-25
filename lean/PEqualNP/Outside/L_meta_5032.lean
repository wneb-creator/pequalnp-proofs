import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5032

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_step_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_step_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step w g) (by simp only [step, List.length_append, List.length_cons, List.length_nil]; omega)]
    exact List.getD_append w [g.op.eval (g.inputs.map fun k => w.getD k false)] false i hi

lemma wire_nine_eq (C : Circuit) (g0 : Gate) (rest : List Gate) (hg : C.gates = g0 :: rest)
    (x : Fin 9 → Bool) :
    (C.wires (List.ofFn x)).getD 9 false =
      g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false) := by
  change (C.gates.foldl step (List.ofFn x)).getD 9 false = _
  rw [hg, List.foldl_cons]
  have hlt : 9 < (step (List.ofFn x) g0).length := by
    simp only [step, List.length_append, List.length_ofFn, List.length_cons, List.length_nil]
    omega
  rw [foldl_step_getD_lt rest (step (List.ofFn x) g0) 9 hlt]
  simp only [step]
  rw [List.getD_append_right (List.ofFn x) _ false 9 (by simp)]
  simp

lemma gate0_ne_not (C : Circuit) (g0 : Gate) (rest : List Gate) (hg : C.gates = g0 :: rest)
    (hw9 : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 2)) :
    g0.op ≠ GateOp.not := by
  intro hnot
  have h1 := hw9 (fun _ => false)
  rw [wire_nine_eq C g0 rest hg (fun _ => false), hnot] at h1
  simp only [GateOp.eval, Bool.or_self] at h1
  cases hgi : g0.inputs with
  | nil =>
    rw [hgi] at h1
    simp at h1
  | cons k ks =>
    rw [hgi] at h1
    simp only [List.map_cons, List.headD_cons] at h1
    by_cases hk : k < 9
    · rw [List.getD_eq_getElem _ _ (by simp [hk]), List.getElem_ofFn] at h1
      simp at h1
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)] at h1
      simp at h1

lemma getD_ge_len (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
  rfl

lemma countP_eq_one_of_unique (l : List Gate) (P : Gate → Bool) (i : ℕ) (hi : i < l.length)
    (hPi : P l[i] = true)
    (huniq : ∀ (j : ℕ) (hj : j < l.length), P l[j] = true → j = i) :
    l.countP P = 1 := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a t ih =>
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero] at hPi
      simp only [List.countP_cons, hPi, ite_true]
      have hrest : t.countP P = 0 := by
        rw [List.countP_eq_zero]
        intro g hg hPg
        obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
        have h0 := huniq (j + 1) (by simp; omega) (by simpa using hPg)
        omega
      omega
    | succ k =>
      have ha : P a = false := by
        cases hPa : P a
        · rfl
        · have h0 := huniq 0 (by simp) (by simpa using hPa)
          omega
      simp only [List.countP_cons, ha, Bool.false_eq_true, ite_false]
      have hkt : k < t.length := by simp at hi; omega
      have hPk : P t[k] = true := by simpa using hPi
      have hih := ih k hkt hPk (fun j hj hPj => by
        have h1 := huniq (j + 1) (by simp; omega) (by simpa using hPj)
        omega)
      omega

lemma op_eq_not_of_eval_false (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (he : g.op.eval [false] = true) : g.op = GateOp.not := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with h | h | h
  · rw [h] at he; cases he
  · rw [h] at he; cases he
  · exact h

lemma main (C : Circuit) (hfan : FanInTwo C) (hsz : C.size ≤ 15)
    (hnots : ∃ (x5 x6 : Fin C.gates.length), x5 < x6 ∧ x5.val ≤ 3 ∧
      (C.gates.get x5).op = GateOp.not ∧ (C.gates.get x6).op = GateOp.not ∧
      ∀ (x7 : Fin C.gates.length), (C.gates.get x7).op = GateOp.not → x7 = x5 ∨ x7 = x6)
    (hw9 : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 2))
    (huses : ∀ w : ℕ, w = 0 ∨ w = 2 →
      ∃ g ∈ C.gates.drop 1,
        (g.op = GateOp.not ∧ g.inputs.head? = some w ∨ g.op ≠ GateOp.not ∧ w ∈ g.inputs)) :
    ∃ (x8 x9 : Circuit) (x10 : Fin 13),
      Monotone2 x8 ∧ FanInTwo x9 ∧ x8.size ≤ 2 ∧ x8.size + x9.size ≤ 13 ∧
      List.countP (fun g => g.op.eval [false]) x9.gates = 1 ∧
      (∀ w : ℕ, w = 0 ∨ w = 2 →
        x10.val = w ∨ ∃ g ∈ x8.gates ++ x9.gates,
          (g.op = GateOp.not ∧ g.inputs.head? = some w ∨ g.op ≠ GateOp.not ∧ w ∈ g.inputs)) ∧
      ∀ x : Fin 9 → Bool,
        have x12 : List Bool := x8.wires (List.ofFn x ++ [x 0 || x 2]);
        x9.eval (x12 ++ [!x12.getD x10.val false]) = C.eval (List.ofFn x) := by
  obtain ⟨x5, x6, h56, h5le3, h5op, h6op, huniq⟩ := hnots
  cases hg : C.gates with
  | nil =>
    have hlt := x5.isLt
    have hlen0 : C.gates.length = 0 := by rw [hg]; rfl
    omega
  | cons g0 rest =>
    have hlen_eq : C.gates.length = rest.length + 1 := by rw [hg]; rfl
    have hg0_ne : g0.op ≠ GateOp.not := gate0_ne_not C g0 rest hg hw9
    have hx5_pos : 1 ≤ x5.val := by
      by_contra h0
      have hz : x5.val = 0 := by omega
      have hget : C.gates.get x5 = g0 := by
        simp only [List.get_eq_getElem, hz]
        simp [hg]
      rw [hget] at h5op
      exact hg0_ne h5op
    let p : ℕ := x5.val - 1
    have hp_eq : x5.val = p + 1 := by omega
    have hp_le2 : p ≤ 2 := by omega
    have hp_lt : p < rest.length := by
      have := x5.isLt
      omega
    let pre : List Gate := rest.take p
    let gnot : Gate := rest[p]
    let post : List Gate := rest.drop (p + 1)
    have hrest_eq : rest = pre ++ gnot :: post := by
      have h1 : rest = rest.take p ++ rest.drop p := (List.take_append_drop p rest).symm
      have h2 : rest.drop p = rest[p] :: rest.drop (p + 1) := List.drop_eq_getElem_cons hp_lt
      rw [h2] at h1
      exact h1
    have hpre_len : pre.length = p := List.length_take_of_le (by omega)
    have hpost_len : post.length = rest.length - (p + 1) := List.length_drop
    have hgnot_op : gnot.op = GateOp.not := by
      have hget : C.gates.get x5 = gnot := by
        simp only [List.get_eq_getElem]
        have : C.gates[x5.val]'(x5.isLt) = (g0 :: rest)[p + 1]'(by rw [← hg, ← hp_eq]; exact x5.isLt) := by
          congr 1
        rw [this]
        rfl
      rw [← hget]
      exact h5op
    let x8 : Circuit := ⟨pre, 0⟩
    let x9 : Circuit := ⟨post, C.output⟩
    let x10 : Fin 13 :=
      match gnot.inputs.head? with
      | some k => if hk : k < 13 then ⟨k, hk⟩ else ⟨12, by omega⟩
      | none => ⟨12, by omega⟩
    have hx8_mono : Monotone2 x8 := by
      intro g hgmem
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hgmem
      change j < pre.length at hj
      have hjp : j < p := by omega
      have hjr : j < rest.length := by omega
      have hmemC : pre[j] ∈ C.gates := by
        rw [hg, hrest_eq]
        exact List.mem_cons_of_mem g0 (List.mem_append_left _ (List.getElem_mem hj))
      obtain ⟨hop, hin⟩ := hfan pre[j] hmemC
      have hne_not : pre[j].op ≠ GateOp.not := by
        intro hnot
        let idx : Fin C.gates.length := ⟨j + 1, by omega⟩
        have hget_idx : C.gates.get idx = pre[j] := by
          simp only [List.get_eq_getElem]
          have hstep1 : C.gates[j + 1]'(idx.isLt) = (g0 :: rest)[j + 1]'(by rw [← hg]; exact idx.isLt) := by
            congr 1
          rw [hstep1, List.getElem_cons_succ]
          exact (List.getElem_take (xs := rest) (i := j) (j := p)).symm
        have hidx_not : (C.gates.get idx).op = GateOp.not := by rw [hget_idx]; exact hnot
        rcases huniq idx hidx_not with heq | heq
        · have hv := congrArg Fin.val heq
          change j + 1 = x5.val at hv
          omega
        · have hv := congrArg Fin.val heq
          change j + 1 = x6.val at hv
          have hlt56 : x5.val < x6.val := h56
          omega
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
      exact ⟨hop.elim Or.inl (fun h => h.elim Or.inr (fun hn => False.elim (hne_not hn))), hin⟩
    have hx9_fan : FanInTwo x9 := by
      intro g hgmem
      apply hfan g
      rw [hg, hrest_eq]
      exact List.mem_cons_of_mem g0 (List.mem_append_right _ (List.mem_cons_of_mem gnot hgmem))
    have hx8_sz : x8.size ≤ 2 := by
      change pre.length ≤ 2
      omega
    have hsum_sz : x8.size + x9.size ≤ 13 := by
      change pre.length + post.length ≤ 13
      have hlenC : C.gates.length ≤ 15 := hsz
      omega
    have hx9_cnt : List.countP (fun g => g.op.eval [false]) x9.gates = 1 := by
      change post.countP (fun g => g.op.eval [false]) = 1
      have hlt56 : x5.val < x6.val := h56
      have hlt6 : x6.val < C.gates.length := x6.isLt
      let idx6 : ℕ := x6.val - (p + 2)
      have hidx6_lt : idx6 < post.length := by omega
      have hpost_eq_C : ∀ (j : ℕ) (hj : j < post.length),
          post[j] = C.gates[p + 2 + j]'(by omega) := by
        intro j hj
        have h1 : post[j] = rest[p + 1 + j]'(by omega) := List.getElem_drop
        rw [h1]
        have h2 : (g0 :: rest)[p + 2 + j]'(by simp; omega) = rest[p + 1 + j]'(by omega) := by
          have : p + 2 + j = (p + 1 + j) + 1 := by omega
          simp [this]
        rw [← h2]
        congr 1
        exact hg.symm
      have hP6 : (post[idx6]).op.eval [false] = true := by
        rw [hpost_eq_C idx6 hidx6_lt]
        have heq : p + 2 + idx6 = x6.val := by omega
        have hget : C.gates[p + 2 + idx6]'(by omega) = C.gates.get x6 := by
          simp only [List.get_eq_getElem]
          congr 1
        rw [hget, h6op]
        rfl
      refine countP_eq_one_of_unique post (fun g => g.op.eval [false]) idx6 hidx6_lt hP6 ?_
      intro j hj hPj
      have hmem : post[j] ∈ post := List.getElem_mem hj
      have hop := (hx9_fan post[j] hmem).1
      have hnotj : post[j].op = GateOp.not := op_eq_not_of_eval_false post[j] hop hPj
      let idx : Fin C.gates.length := ⟨p + 2 + j, by omega⟩
      have hget : C.gates.get idx = post[j] := by
        simp only [List.get_eq_getElem]
        exact (hpost_eq_C j hj).symm
      have hnot : (C.gates.get idx).op = GateOp.not := by rw [hget]; exact hnotj
      rcases huniq idx hnot with heq | heq
      · have hv := congrArg Fin.val heq
        change p + 2 + j = x5.val at hv
        omega
      · have hv := congrArg Fin.val heq
        change p + 2 + j = x6.val at hv
        omega
    have huses' : ∀ w : ℕ, w = 0 ∨ w = 2 →
        x10.val = w ∨ ∃ g ∈ x8.gates ++ x9.gates,
          (g.op = GateOp.not ∧ g.inputs.head? = some w ∨ g.op ≠ GateOp.not ∧ w ∈ g.inputs) := by
      intro w hw
      obtain ⟨g, hgdrop, hgw⟩ := huses w hw
      have hgrest : g ∈ pre ++ gnot :: post := by
        rw [hg, List.drop_succ_cons, List.drop_zero, hrest_eq] at hgdrop
        exact hgdrop
      simp only [List.mem_append, List.mem_cons] at hgrest
      rcases hgrest with hpre | rfl | hpost
      · exact Or.inr ⟨g, List.mem_append_left _ hpre, hgw⟩
      · rcases hgw with ⟨_, hhead⟩ | ⟨hne, _⟩
        · left
          have hw13 : w < 13 := by omega
          simp [x10, hhead, hw13]
        · exact False.elim (hne hgnot_op)
      · exact Or.inr ⟨g, List.mem_append_right _ hpost, hgw⟩
    refine ⟨x8, x9, x10, hx8_mono, hx9_fan, hx8_sz, hsum_sz, hx9_cnt, huses', ?_⟩
    intro x
    let x12 : List Bool := x8.wires (List.ofFn x ++ [x 0 || x 2])
    change x9.eval (x12 ++ [!x12.getD x10.val false]) = C.eval (List.ofFn x)
    have hstep0 : step (List.ofFn x) g0 = List.ofFn x ++ [x 0 || x 2] := by
      have h9 := hw9 x
      rw [wire_nine_eq C g0 rest hg x] at h9
      simp only [step, h9]
    have hx12_len : x12.length ≤ 12 := by
      change (pre.foldl step (List.ofFn x ++ [x 0 || x 2])).length ≤ 12
      rw [foldl_step_len]
      simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil]
      omega
    have hstep_not : step x12 gnot = x12 ++ [!x12.getD x10.val false] := by
      simp only [step, hgnot_op, GateOp.eval]
      congr 1
      congr 1
      cases hgi : gnot.inputs with
      | nil =>
        have hx10v : x10.val = 12 := by simp [x10, hgi]
        rw [hx10v, getD_ge_len x12 12 hx12_len]
        rfl
      | cons k ks =>
        simp only [List.map_cons, List.headD_cons]
        by_cases hk : k < 13
        · have hx10v : x10.val = k := by simp [x10, hgi, hk]
          rw [hx10v]
        · have hx10v : x10.val = 12 := by simp [x10, hgi, hk]
          rw [hx10v, getD_ge_len x12 12 hx12_len, getD_ge_len x12 k (by omega)]
    have hwires : C.wires (List.ofFn x) = x9.wires (x12 ++ [!x12.getD x10.val false]) := by
      change (C.gates.foldl step (List.ofFn x)) = post.foldl step (x12 ++ [!x12.getD x10.val false])
      rw [hg, hrest_eq, List.foldl_cons, hstep0, List.foldl_append]
      change (gnot :: post).foldl step x12 = post.foldl step (x12 ++ [!x12.getD x10.val false])
      rw [List.foldl_cons, hstep_not]
    simp only [Circuit.eval, hwires]
    rfl

end PEqualNP.Outside.L_meta_5032

theorem PEqualNP.Outside.L_meta_5032 : have x1 : PEqualNP.CircuitLowerBounds.Gate → ℕ → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : ℕ) => x1.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x1.inputs.head? = Option.some x2 ∨ x1.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x2 ∈ x1.inputs; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size ≤ (15 : ℕ) →       (∃ (x5 : Fin x2.gates.length) (x6 : Fin x2.gates.length), x5 < x6 ∧ ↑x5 ≤ (3 : ℕ) ∧ (x2.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x2.gates.get x6).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x7 : Fin x2.gates.length), (x2.gates.get x7).op = PEqualNP.CircuitLowerBounds.GateOp.not → x7 = x5 ∨ x7 = x6) →         (∀ (x6 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x6)).getD (9 : ℕ) Bool.false = (x6 (0 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)))) →           (∀ (x7 : ℕ), x7 = (0 : ℕ) ∨ x7 = (2 : ℕ) → ∃ x9 ∈ List.drop (1 : ℕ) x2.gates, x1 x9 x7) →             ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit) (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : Fin (13 : ℕ)),               PEqualNP.MetaComplexity.Monotone2 x8 ∧                 PEqualNP.MetaComplexity.FanInTwo x9 ∧                   x8.size ≤ (2 : ℕ) ∧                     x8.size + x9.size ≤ (13 : ℕ) ∧                       List.countP (fun (x11 : PEqualNP.CircuitLowerBounds.Gate) => x11.op.eval [Bool.false]) x9.gates = (1 : ℕ) ∧                         (∀ (x11 : ℕ), x11 = (0 : ℕ) ∨ x11 = (2 : ℕ) → ↑x10 = x11 ∨ ∃ x13 ∈ x8.gates ++ x9.gates, x1 x13 x11) ∧                           ∀ (x11 : Fin (9 : ℕ) → Bool),                             have x12 : List Bool := x8.wires (List.ofFn x11 ++ [x11 (0 : Fin (9 : ℕ)) || x11 (2 : Fin (9 : ℕ))]);                             x9.eval (x12 ++ [!x12.getD (↑x10) Bool.false]) = x2.eval (List.ofFn x11) := by
  intro x1 x2 hfan hsz hnots hw9 huses
  exact PEqualNP.Outside.L_meta_5032.main x2 hfan hsz hnots hw9 huses
