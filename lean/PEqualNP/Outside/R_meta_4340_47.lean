import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_4340_47
    (h1 : ∀ p ∈ ([(0,1),(0,2),(0,3),(0,4),(4,6)] : List (Fin 9 × Fin 9)), ∀ C : Circuit,
      FanInTwo C → C.size = 14 → C.output = 23 →
      (∀ i : Fin C.size, let g := C.gates.get i
        g.inputs.length = 2 ∧ ∀ j ∈ g.inputs, j < 10 + i.val ∨ j = 24) →
      (∀ g ∈ C.gates, (∀ j ∈ g.inputs, j < 9) → g.op ≠ .and ∧ g.op ≠ .not) →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x p.1 || x p.2]) ≠
        (fun (x8 : Fin (9 : ℕ) → Bool) => x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) x)
    (h2 : ∀ p ∈ ([(0,6)] : List (Fin 9 × Fin 9)), ∀ C : Circuit,
      FanInTwo C → C.size = 14 → C.output = 23 →
      (∀ i : Fin C.size, let g := C.gates.get i
        g.inputs.length = 2 ∧ ∀ j ∈ g.inputs, j < 10 + i.val ∨ j = 24) →
      (∀ g ∈ C.gates, (∀ j ∈ g.inputs, j < 9) → g.op ≠ .and ∧ g.op ≠ .not) →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x p.1 || x p.2]) ≠
        (fun (x8 : Fin (9 : ℕ) → Bool) => x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) x) :
  ∀ x1 ∈ [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)))], ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (14 : ℕ) → (∀ x6 ∈ x3.gates, (∀ x8 ∈ x6.inputs, x8 < (9 : ℕ)) → x6.op ≠ PEqualNP.CircuitLowerBounds.GateOp.and ∧ x6.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) → ∃ (x7 : Fin (9 : ℕ) → Bool), x3.eval (List.ofFn x7 ++ [x7 x1.1 || x7 x1.2]) ≠ (fun (x8 : Fin (9 : ℕ) → Bool) => x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) x7 := by
  intro p hp C hfan hsize hdir
  let f : (Fin 9 → Bool) → Bool := (fun (x8 : Fin (9 : ℕ) → Bool) => x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)))
  have core (C : Circuit) (hfan : FanInTwo C) (hsize : C.size ≤ 14)
      (hdir : ∀ g ∈ C.gates, (∀ j ∈ g.inputs, j < 9) → g.op ≠ .and ∧ g.op ≠ .not)
      (houtput : C.output + 1 = 10 + C.size) (hfixed : C.size = 14) :
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x p.1 || x p.2]) ≠ f x := by
    let cg : ℕ → Gate → Gate := fun n g => ⟨g.op,
      [if g.inputs.getD 0 24 < n then g.inputs.getD 0 24 else 24,
       if g.inputs.getD 1 (g.inputs.getD 0 24) < n then g.inputs.getD 1 (g.inputs.getD 0 24) else 24]⟩
    let D : Circuit := ⟨C.gates.mapIdx (fun i g => cg (10 + i) g), min C.output 24⟩
    have hmin (w : List Bool) (hw : w.length ≤ 24) (j : ℕ) :
        w.getD (min j 24) false = w.getD j false := by
      by_cases hj : j ≤ 24
      · simp only [min_eq_left hj]
      · rw [min_eq_right (by omega), List.getD_eq_default _ _ hw,
          List.getD_eq_default _ _ (by omega)]
    have hget (w : List Bool) (hw : w.length ≤ 24) (j : ℕ) :
        w.getD (if j < w.length then j else 24) false = w.getD j false := by
      by_cases hj : j < w.length
      · simp only [ite_eq_left hj]
      · rw [ite_eq_right hj, List.getD_eq_default _ _ hw,
          List.getD_eq_default _ _ (by omega)]
    have hvalue (g : Gate) (hg : g.op = .and ∨ g.op = .or ∨ g.op = .not)
        (hl : g.inputs.length ≤ 2) (he : g.inputs = [] → g.op = .or)
        (w : List Bool) (hw : w.length ≤ 24) :
        (cg w.length g).op.eval ((cg w.length g).inputs.map (fun j => w.getD j false)) =
        g.op.eval (g.inputs.map (fun j => w.getD j false)) := by
      obtain ⟨op, ins⟩ := g
      rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
      · have hop : op = .or := he rfl
        subst op
        have hd : w.getD 24 false = false := List.getD_eq_default _ _ hw
        simp [cg, GateOp.eval, hd, not_lt.mpr hw, -List.getD_eq_getElem?_getD]
      · rcases hg with rfl | rfl | rfl <;>
          simp [cg, GateOp.eval, hget w hw, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil, -List.getD_eq_getElem?_getD]
      · simp [cg, hget w hw, List.getD_cons_zero, List.getD_cons_succ, -List.getD_eq_getElem?_getD]
      · simp at hl
    have hfold : ∀ gs : List Gate, (∀ g ∈ gs, g ∈ C.gates) →
        ∀ w : List Bool, w.length + gs.length ≤ 24 →
        (gs.mapIdx (fun i g => cg (w.length + i) g)).foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun j => w.getD j false))]) w =
        gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun j => w.getD j false))]) w := by
      intro gs
      induction gs with
      | nil => intros; rfl
      | cons g gs ih =>
        intro hs w hw
        have hm : g ∈ C.gates := hs g List.mem_cons_self
        have hop : g.op = .and ∨ g.op = .or ∨ g.op = .not := by
          simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hfan g hm).1
        have he : g.inputs = [] → g.op = .or := by
          intro he
          have hd := hdir g hm (by simp [he])
          rcases hop with ha | ho | hn
          · exact False.elim (hd.1 ha)
          · exact ho
          · exact False.elim (hd.2 hn)
        have hv := hvalue g hop (hfan g hm).2 he w (by simp only [List.length_cons] at hw; omega)
        simp only [List.mapIdx_cons, Nat.add_zero, List.foldl_cons, hv]
        have hh : (w ++ [g.op.eval (g.inputs.map (fun j => w.getD j false))]).length + gs.length ≤ 24 := by
          simp only [List.length_append, List.length_cons, List.length_nil] at *
          omega
        simpa only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero,
          Nat.add_assoc, Nat.add_comm 1] using
          ih (fun a ha => hs a (List.mem_cons_of_mem g ha)) _ hh
    have hlen : ∀ gs : List Gate, ∀ w : List Bool,
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun j => w.getD j false))]) w).length =
        w.length + gs.length := by
      intro gs
      induction gs with
      | nil => intro w; simp
      | cons g gs ih =>
        intro w
        simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
        omega
    have hDsize : D.size = C.size := by simp [D, Circuit.size]
    have hDfan : FanInTwo D := by
      intro g hg
      obtain ⟨i, hi, rfl⟩ := List.mem_mapIdx.mp hg
      exact ⟨(hfan _ (List.getElem_mem hi)).1, by simp [cg]⟩
    have hDdir : ∀ g ∈ D.gates, (∀ j ∈ g.inputs, j < 9) → g.op ≠ .and ∧ g.op ≠ .not := by
      intro g hg hj
      obtain ⟨i, hi, rfl⟩ := List.mem_mapIdx.mp hg
      let a := C.gates[i]
      have ha : a ∈ C.gates := List.getElem_mem hi
      apply hdir a ha
      have hl := (hfan a ha).2
      have hleft := hj (if a.inputs.getD 0 24 < 10 + i then a.inputs.getD 0 24 else 24) (by simp [cg, a])
      have hright := hj (if a.inputs.getD 1 (a.inputs.getD 0 24) < 10 + i then a.inputs.getD 1 (a.inputs.getD 0 24) else 24) (by simp [cg, a])
      intro j hja
      rcases hins : a.inputs with _ | ⟨u, _ | ⟨v, _ | ⟨z, rest⟩⟩⟩
      · simp [hins] at hja
      · simp only [hins, List.mem_singleton] at hja
        subst j
        simp only [hins, List.getD_cons_zero] at hleft
        split_ifs at hleft <;> omega
      · simp only [hins, List.mem_cons, List.mem_nil_iff, or_false] at hja
        simp only [hins, List.getD_cons_zero, List.getD_cons_succ] at hleft hright
        rcases hja with rfl | rfl <;> split_ifs at hleft hright <;> omega
      · simp [hins] at hl
    have hDbound : ∀ i : Fin D.size, let g := D.gates.get i
        g.inputs.length = 2 ∧ ∀ j ∈ g.inputs, j < 10 + i.val ∨ j = 24 := by
      intro i
      change Fin (C.gates.mapIdx (fun i g => cg (10 + i) g)).length at i
      dsimp only [D]
      rw [List.get_eq_getElem, List.getElem_mapIdx]
      refine ⟨by simp [cg], ?_⟩
      intro j hj
      simp only [cg, List.mem_cons, List.mem_nil_iff, or_false] at hj
      rcases hj with rfl | rfl <;> split_ifs
      · exact Or.inl ‹_›
      · exact Or.inr rfl
      · exact Or.inl ‹_›
      · exact Or.inr rfl
    have hDeval (x : Fin 9 → Bool) :
        D.eval (List.ofFn x ++ [x p.1 || x p.2]) = C.eval (List.ofFn x ++ [x p.1 || x p.2]) := by
      have hw : (List.ofFn x ++ [x p.1 || x p.2]).length + C.gates.length ≤ 24 := by
        simp only [List.length_append, List.length_ofFn, List.length_singleton]
        change C.gates.length ≤ 14 at hsize
        omega
      simp only [Circuit.eval, Circuit.wires, D]
      have hf := hfold C.gates (fun _ h => h) _ hw
      simp only [List.length_append, List.length_ofFn, List.length_singleton] at hf
      rw [hf]
      exact hmin _ (by rw [hlen]; exact hw) C.output
    have hsmall : D.size = 14 := hDsize.trans hfixed
    have hcb : C.output ≤ 24 := by omega
    have hout : D.output = 23 := by
      change min C.output 24 = 23
      have hc : C.output = 23 := by omega
      simp [hc]
    have hp' : p ∈ ([(0,1),(0,2),(0,3),(0,4),(4,6)] : List (Fin 9 × Fin 9)) ∨
        p ∈ ([(0,6)] : List (Fin 9 × Fin 9)) := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp ⊢
      tauto
    rcases hp' with hp' | hp'
    · obtain ⟨x, hx⟩ := h1 p hp' D hDfan hsmall hout hDbound hDdir
      exact ⟨x, by simpa only [hDeval] using hx⟩
    · obtain ⟨x, hx⟩ := h2 p hp' D hDfan hsmall hout hDbound hDdir
      exact ⟨x, by simpa only [hDeval] using hx⟩
  have hlen : ∀ gs : List Gate, ∀ w : List Bool,
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun j => w.getD j false))]) w).length =
      w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
      omega
  have hpres (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun j => w.getD j false))]) w).getD i false =
      w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih _ (by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega)]
      exact List.getD_append _ _ _ _ hi
  have hsingle : ∀ i : Fin 9, f (fun j => decide (j = i)) = false := by decide
  change ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x p.1 || x p.2]) ≠ f x
  by_cases ho : C.output < 10
  · by_cases hi : C.output < 9
    · let i : Fin 9 := ⟨C.output, hi⟩
      let x : Fin 9 → Bool := fun j => decide (j = i)
      have heval : C.eval (List.ofFn x ++ [x p.1 || x p.2]) = true := by
        simp only [Circuit.eval, Circuit.wires]
        rw [hpres _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by simpa using hi)]
        rw [List.getD_eq_getElem (List.ofFn x) false (by simpa using hi), List.getElem_ofFn]
        simp [x, i]
      refine ⟨x, ?_⟩
      rw [heval, hsingle i]
      decide
    · have hout : C.output = 9 := by omega
      let x : Fin 9 → Bool := fun j => decide (j = p.1)
      have heval : C.eval (List.ofFn x ++ [x p.1 || x p.2]) = true := by
        simp only [Circuit.eval, Circuit.wires, hout]
        rw [hpres _ _ _ (by simp), List.getD_append_right _ _ _ _ (by simp)]
        simp [x, List.getD_cons_zero, -List.getD_eq_getElem?_getD]
      refine ⟨x, ?_⟩
      rw [heval, hsingle p.1]
      decide
  by_cases hb : 10 + C.size ≤ C.output
  · let x : Fin 9 → Bool := fun j => decide (j = 0 ∨ j = 1)
    have heval : C.eval (List.ofFn x ++ [x p.1 || x p.2]) = false := by
      simp only [Circuit.eval, Circuit.wires]
      apply List.getD_eq_default
      rw [hlen]
      simpa [Circuit.size] using hb
    refine ⟨x, ?_⟩
    rw [heval]
    decide
  let m := C.output + 1 - 10
  have hm : m ≤ C.gates.length := by
    change ¬ 10 + C.gates.length ≤ C.output at hb
    dsimp [m]
    omega
  have hmeq : 10 + m = C.output + 1 := by dsimp [m]; omega
  let E : Circuit := ⟨C.gates.take m, C.output⟩
  have hEfan : FanInTwo E := by
    intro g hg
    exact hfan g (List.mem_of_mem_take hg)
  have hEsize : E.size ≤ 14 := by
    simpa only [E, Circuit.size, List.length_take, min_eq_left hm] using
      hm.trans hsize
  have hEdir : ∀ g ∈ E.gates, (∀ j ∈ g.inputs, j < 9) → g.op ≠ .and ∧ g.op ≠ .not := by
    intro g hg hj
    exact hdir g (List.mem_of_mem_take hg) hj
  have hElast : E.output + 1 = 10 + E.size := by
    simpa only [E, Circuit.size, List.length_take, min_eq_left hm] using hmeq.symm
  have hEval (x : Fin 9 → Bool) :
      E.eval (List.ofFn x ++ [x p.1 || x p.2]) = C.eval (List.ofFn x ++ [x p.1 || x p.2]) := by
    simp only [Circuit.eval, Circuit.wires, E]
    conv_rhs => rw [← List.take_append_drop m C.gates, List.foldl_append]
    symm
    apply hpres
    rw [hlen]
    simp only [List.length_append, List.length_ofFn, List.length_singleton,
      List.length_take, min_eq_left hm]
    omega
  let pad : Gate := ⟨.or, [E.output, E.output]⟩
  let r := 14 - E.size
  let F : Circuit := ⟨E.gates ++ List.replicate r pad, 23⟩
  have hFsize : F.size = 14 := by
    change (E.gates ++ List.replicate r pad).length = 14
    rw [List.length_append, List.length_replicate]
    change E.size + (14 - E.size) = 14
    omega
  have hFfan : FanInTwo F := by
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hEfan g hg
    · have hg' : g = pad := List.eq_of_mem_replicate hg
      subst g
      simp [pad]
  have hFdir : ∀ g ∈ F.gates, (∀ j ∈ g.inputs, j < 9) → g.op ≠ .and ∧ g.op ≠ .not := by
    intro g hg hj
    rcases List.mem_append.mp hg with hg | hg
    · exact hEdir g hg hj
    · have hg' : g = pad := List.eq_of_mem_replicate hg
      subst g
      simp [pad]
  have hFlast : F.output + 1 = 10 + F.size := by
    change 24 = 10 + F.size
    omega
  have hpad (n : ℕ) (w : List Bool) (hw : E.output < w.length) :
      ((List.replicate n pad).foldl (fun w g =>
        w ++ [g.op.eval (g.inputs.map (fun j => w.getD j false))]) w) =
      w ++ List.replicate n (w.getD E.output false) := by
    induction n generalizing w with
    | zero => simp
    | succ n ih =>
      rw [List.replicate_succ, List.foldl_cons]
      have hv : pad.op.eval (pad.inputs.map (fun j => w.getD j false)) = w.getD E.output false := by
        simp [pad, GateOp.eval]
      rw [hv, ih _ (by simp; omega)]
      rw [List.getD_append _ _ _ _ hw]
      simp [List.replicate_succ, List.append_assoc]
  have hFval (x : Fin 9 → Bool) :
      F.eval (List.ofFn x ++ [x p.1 || x p.2]) = E.eval (List.ofFn x ++ [x p.1 || x p.2]) := by
    have hwl : (E.gates.foldl (fun w g =>
        w ++ [g.op.eval (g.inputs.map (fun j => w.getD j false))])
        (List.ofFn x ++ [x p.1 || x p.2])).length = 10 + E.size := by
      rw [hlen]
      simp [Circuit.size]
    simp only [Circuit.eval, Circuit.wires, F]
    rw [List.foldl_append, hpad _ _ (by rw [hwl]; omega)]
    by_cases hz : E.size = 14
    · have hout : E.output = 23 := by omega
      simp only [r, hz, Nat.sub_self, List.replicate_zero, List.append_nil, hout]
    · rw [List.getD_append_right _ _ _ _ (by rw [hwl]; omega)]
      exact List.getD_replicate _ (by dsimp [r]; rw [hwl]; omega)
  obtain ⟨x, hx⟩ := core F hFfan hFsize.le hFdir hFlast hFsize
  exact ⟨x, by simpa only [hFval, hEval] using hx⟩
