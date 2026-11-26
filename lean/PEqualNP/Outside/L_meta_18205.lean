import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18205

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem step_lt (w : List Bool) (g : Gate) (i : ℕ) (h : i < w.length) :
    (step w g).getD i false = w.getD i false := List.getD_append _ _ _ _ h

theorem step_eq (w : List Bool) (g : Gate) :
    (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  unfold step
  rw [List.getD_append_right _ _ _ _ le_rfl]
  simp

theorem run_lt (gs : List Gate) : ∀ (w : List Bool) (k : ℕ), k < w.length →
    (gs.foldl step w).getD k false = w.getD k false := by
  induction gs with
  | nil => intro w k _; rfl
  | cons g gs ih =>
    intro w k hk
    simp only [List.foldl_cons]
    rw [ih _ k (by rw [step_len]; omega), step_lt _ _ _ hk]

theorem gate_eq (gs : List Gate) : ∀ (x : List Bool) (j : ℕ), j < gs.length →
    (∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < x.length + j) →
    (gs.foldl step x).getD (x.length + j) false
      = (gs.getD j ⟨GateOp.or, []⟩).op.eval
        ((gs.getD j ⟨GateOp.or, []⟩).inputs.map fun i => (gs.foldl step x).getD i false) := by
  induction gs with
  | nil => intro x j hj; simp at hj
  | cons g gs ih =>
    intro x j hj hin
    cases j with
    | zero =>
      simp only [List.foldl_cons, List.getD_cons_zero, Nat.add_zero] at hin ⊢
      rw [run_lt _ _ _ (by rw [step_len]; omega), step_eq]
      congr 1
      apply List.map_congr_left
      intro i hi
      rw [run_lt _ _ _ (by rw [step_len]; have := hin i hi; omega), step_lt _ _ _ (hin i hi)]
    | succ j =>
      simp only [List.foldl_cons, List.getD_cons_succ] at hin ⊢
      have h := ih (step x g) j (by simpa using hj) (by
        intro i hi
        rw [step_len]
        have := hin i hi
        omega)
      rw [step_len] at h
      have e : x.length + 1 + j = x.length + (j + 1) := by omega
      rw [e] at h
      exact h

theorem main (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) (p q : Fin n) (j0 : ℕ)
    (hand : PEqualNP.ReadTwo.isAnd C j0)
    (h1 : PEqualNP.ReadTwo.wval C (PEqualNP.ReadTwo.indW n {(p : ℕ)}) (n + j0) = true)
    (h2 : ∀ i ∈ (gateAt C j0).inputs,
      PEqualNP.ReadTwo.wval C (PEqualNP.ReadTwo.indW n {(q : ℕ)}) i = false) :
    ∀ i ∈ (gateAt C j0).inputs,
      (PEqualNP.ReadTwo.wval C (PEqualNP.ReadTwo.indW n {(p : ℕ)}) i = true ∧
        PEqualNP.ReadTwo.wval C (PEqualNP.ReadTwo.indW n {(q : ℕ)}) i = false) ∧
      Relation.ReflTransGen (fun a b : ℕ => n ≤ b ∧ a ∈ (gateAt C (b - n)).inputs ∧
        (PEqualNP.ReadTwo.wval C (PEqualNP.ReadTwo.indW n {(p : ℕ)}) a = true ∧
          PEqualNP.ReadTwo.wval C (PEqualNP.ReadTwo.indW n {(q : ℕ)}) a = false) ∧
        (PEqualNP.ReadTwo.wval C (PEqualNP.ReadTwo.indW n {(p : ℕ)}) b = true ∧
          PEqualNP.ReadTwo.wval C (PEqualNP.ReadTwo.indW n {(q : ℕ)}) b = false)) (p : ℕ) i := by
  obtain ⟨hao, hrb, hlen⟩ := hC
  have hgate : ∀ (v : Fin n) (j : ℕ), j < C.gates.length →
      PEqualNP.ReadTwo.wval C (PEqualNP.ReadTwo.indW n {(v : ℕ)}) (n + j)
        = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
          PEqualNP.ReadTwo.wval C (PEqualNP.ReadTwo.indW n {(v : ℕ)}) i) := by
    intro v j hj
    have h := gate_eq C.gates (List.ofFn (PEqualNP.ReadTwo.indW n {(v : ℕ)})) j hj (by
      intro i hi
      have := hrb j hj i hi
      simpa using this)
    simp only [List.length_ofFn] at h
    exact h
  have hpair : ∀ j, j < C.gates.length → ∃ a b, (gateAt C j).inputs = [a, b] ∧ a < n + j ∧ b < n + j := by
    intro j hj
    have hmem : gateAt C j ∈ C.gates := by
      unfold gateAt
      rw [List.getD_eq_getElem _ _ hj]
      exact List.getElem_mem hj
    have hl := hlen _ hmem
    rcases hgi : (gateAt C j).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩
    · rw [hgi] at hl; simp at hl
    · rw [hgi] at hl; simp at hl
    · exact ⟨a, b, rfl, hrb j hj a (by rw [hgi]; simp), hrb j hj b (by rw [hgi]; simp)⟩
    · rw [hgi] at hl; simp at hl
  have hop : ∀ j, j < C.gates.length → (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
    intro j hj
    apply hao
    unfold gateAt
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  have hinp : ∀ w, w < n → PEqualNP.ReadTwo.wval C (PEqualNP.ReadTwo.indW n {(p : ℕ)}) w = true →
      w = (p : ℕ) := by
    intro w hw hv
    unfold PEqualNP.ReadTwo.wval at hv
    have e : (C.wires (List.ofFn (PEqualNP.ReadTwo.indW n {(p : ℕ)}))).getD w false
        = (List.ofFn (PEqualNP.ReadTwo.indW n {(p : ℕ)})).getD w false :=
      run_lt C.gates _ w (by simpa using hw)
    rw [e, List.getD_eq_getElem _ _ (by simpa using hw), List.getElem_ofFn] at hv
    simpa [PEqualNP.ReadTwo.indW] using hv
  have star : ∀ w, w < n + C.gates.length →
      (PEqualNP.ReadTwo.wval C (PEqualNP.ReadTwo.indW n {(p : ℕ)}) w = true ∧
        PEqualNP.ReadTwo.wval C (PEqualNP.ReadTwo.indW n {(q : ℕ)}) w = false) →
      Relation.ReflTransGen (fun a b : ℕ => n ≤ b ∧ a ∈ (gateAt C (b - n)).inputs ∧
        (PEqualNP.ReadTwo.wval C (PEqualNP.ReadTwo.indW n {(p : ℕ)}) a = true ∧
          PEqualNP.ReadTwo.wval C (PEqualNP.ReadTwo.indW n {(q : ℕ)}) a = false) ∧
        (PEqualNP.ReadTwo.wval C (PEqualNP.ReadTwo.indW n {(p : ℕ)}) b = true ∧
          PEqualNP.ReadTwo.wval C (PEqualNP.ReadTwo.indW n {(q : ℕ)}) b = false)) (p : ℕ) w := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw hgood
      by_cases hwn : w < n
      · rw [hinp w hwn hgood.1]
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < C.gates.length := by omega
        obtain ⟨a, b, hab, ha, hb⟩ := hpair j hj
        have ep := hgate p j hj
        have eq := hgate q j hj
        rw [hab] at ep eq
        simp only [List.map_cons, List.map_nil] at ep eq
        have hstep : ∀ c, c ∈ [a, b] → c < n + j →
            (PEqualNP.ReadTwo.wval C (PEqualNP.ReadTwo.indW n {(p : ℕ)}) c = true ∧
              PEqualNP.ReadTwo.wval C (PEqualNP.ReadTwo.indW n {(q : ℕ)}) c = false) →
            Relation.ReflTransGen (fun a b : ℕ => n ≤ b ∧ a ∈ (gateAt C (b - n)).inputs ∧
        (PEqualNP.ReadTwo.wval C (PEqualNP.ReadTwo.indW n {(p : ℕ)}) a = true ∧
          PEqualNP.ReadTwo.wval C (PEqualNP.ReadTwo.indW n {(q : ℕ)}) a = false) ∧
        (PEqualNP.ReadTwo.wval C (PEqualNP.ReadTwo.indW n {(p : ℕ)}) b = true ∧
          PEqualNP.ReadTwo.wval C (PEqualNP.ReadTwo.indW n {(q : ℕ)}) b = false)) (p : ℕ) (n + j) := by
          intro c hc hcl hcg
          refine Relation.ReflTransGen.tail (ih c hcl (by omega) hcg) ⟨by omega, ?_, hcg, hgood⟩
          have e : n + j - n = j := by omega
          rw [e, hab]
          exact hc
        rcases hop j hj with ho | ho
        · rw [ho] at ep eq
          rw [hgood.1] at ep
          rw [hgood.2] at eq
          simp only [GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true] at ep eq
          have ep' := Bool.and_eq_true_iff.mp ep.symm
          rcases Bool.and_eq_false_iff.mp eq.symm with hq | hq
          · exact hstep a (by simp) ha ⟨ep'.1, hq⟩
          · exact hstep b (by simp) hb ⟨ep'.2, hq⟩
        · rw [ho] at ep eq
          rw [hgood.1] at ep
          rw [hgood.2] at eq
          simp only [GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false] at ep eq
          have eq' := Bool.or_eq_false_iff.mp eq.symm
          rcases Bool.or_eq_true_iff.mp ep.symm with hp | hp
          · exact hstep a (by simp) ha ⟨hp, eq'.1⟩
          · exact hstep b (by simp) hb ⟨hp, eq'.2⟩
  intro i hi
  obtain ⟨hj0, hopa⟩ := hand
  obtain ⟨a, b, hab, ha, hb⟩ := hpair j0 hj0
  have ep := hgate p j0 hj0
  rw [h1, hopa, hab] at ep
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id,
    Bool.and_true] at ep
  have ep' := Bool.and_eq_true_iff.mp ep.symm
  have hgi : PEqualNP.ReadTwo.wval C (PEqualNP.ReadTwo.indW n {(p : ℕ)}) i = true := by
    rw [hab] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact ep'.1
    · exact ep'.2
  have hil : i < n + j0 := by
    rw [hab] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact ha
    · exact hb
  exact ⟨⟨hgi, h2 i hi⟩, star i (by omega) ⟨hgi, h2 i hi⟩⟩

end PEqualNP.Outside.L_meta_18205

theorem PEqualNP.Outside.L_meta_18205 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 x1 x2 →     ∀ (x4 x5 : Fin x1) (x6 : ℕ),       PEqualNP.ReadTwo.isAnd x2 x6 →         have x8 : Fin x1 → ℕ → Bool := fun (x8 : Fin x1) => PEqualNP.ReadTwo.wval x2 (PEqualNP.ReadTwo.indW x1 {↑x8});         have x9 : ℕ → Prop := fun (x9 : ℕ) => x8 x4 x9 = Bool.true ∧ x8 x5 x9 = Bool.false;         have x10 : ℕ → ℕ → Prop := fun (x10 x11 : ℕ) => x1 ≤ x11 ∧ x10 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 (x11 - x1)).inputs ∧ x9 x10 ∧ x9 x11;         x8 x4 (x1 + x6) = Bool.true → (∀ x12 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x6).inputs, x8 x5 x12 = Bool.false) → ∀ x13 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x6).inputs, x9 x13 ∧ Relation.ReflTransGen x10 (↑x4) x13 := by
  intro n C hC p q j0 hand x8 x9 x10 h1 h2
  exact PEqualNP.Outside.L_meta_18205.main n C hC p q j0 hand h1 h2
