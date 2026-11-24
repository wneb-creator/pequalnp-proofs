import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_4340_47
    (h1 : ∀ p ∈ ([(0,1),(0,2),(0,3),(0,4),(4,6)] : List (Fin 9 × Fin 9)), ∀ C : Circuit,
      FanInTwo C → C.size ≤ 14 → C.output ≤ 24 →
      (∀ g ∈ C.gates, g.inputs.length = 2 ∧ ∀ j ∈ g.inputs, j ≤ 24) →
      (∀ g ∈ C.gates, (∀ j ∈ g.inputs, j < 9) → g.op ≠ .and ∧ g.op ≠ .not) →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x p.1 || x p.2]) ≠
        (fun (x8 : Fin (9 : ℕ) → Bool) => x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) x)
    (h2 : ∀ p ∈ ([(0,6)] : List (Fin 9 × Fin 9)), ∀ C : Circuit,
      FanInTwo C → C.size ≤ 14 → C.output ≤ 24 →
      (∀ g ∈ C.gates, g.inputs.length = 2 ∧ ∀ j ∈ g.inputs, j ≤ 24) →
      (∀ g ∈ C.gates, (∀ j ∈ g.inputs, j < 9) → g.op ≠ .and ∧ g.op ≠ .not) →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x p.1 || x p.2]) ≠
        (fun (x8 : Fin (9 : ℕ) → Bool) => x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) x) :
  ∀ x1 ∈ [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)))], ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (14 : ℕ) → (∀ x6 ∈ x3.gates, (∀ x8 ∈ x6.inputs, x8 < (9 : ℕ)) → x6.op ≠ PEqualNP.CircuitLowerBounds.GateOp.and ∧ x6.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) → ∃ (x7 : Fin (9 : ℕ) → Bool), x3.eval (List.ofFn x7 ++ [x7 x1.1 || x7 x1.2]) ≠ (fun (x8 : Fin (9 : ℕ) → Bool) => x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) x7 := by
  intro p hp C hfan hsize hdir
  let cg : Gate → Gate := fun g => ⟨g.op,
    [min (g.inputs.getD 0 24) 24, min (g.inputs.getD 1 (g.inputs.getD 0 24)) 24]⟩
  let D : Circuit := ⟨C.gates.map cg, min C.output 24⟩
  have hget (w : List Bool) (hw : w.length ≤ 24) (j : ℕ) :
      w.getD (min j 24) false = w.getD j false := by
    by_cases hj : j ≤ 24
    · simp only [min_eq_left hj]
    · rw [min_eq_right (by omega), List.getD_eq_default _ _ hw,
        List.getD_eq_default _ _ (by omega)]
  have hvalue (g : Gate) (hg : g.op = .and ∨ g.op = .or ∨ g.op = .not)
      (hl : g.inputs.length ≤ 2) (he : g.inputs = [] → g.op = .or)
      (w : List Bool) (hw : w.length ≤ 24) :
      (cg g).op.eval ((cg g).inputs.map (fun j => w.getD j false)) =
      g.op.eval (g.inputs.map (fun j => w.getD j false)) := by
    obtain ⟨op, ins⟩ := g
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · have hop : op = .or := he rfl
      subst op
      have hd : w.getD 24 false = false := List.getD_eq_default _ _ hw
      simp [cg, GateOp.eval, hd, -List.getD_eq_getElem?_getD]
    · rcases hg with rfl | rfl | rfl <;>
        simp [cg, GateOp.eval, hget w hw, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil, -List.getD_eq_getElem?_getD]
    · simp [cg, hget w hw, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil, -List.getD_eq_getElem?_getD]
    · simp at hl
  have hfold : ∀ gs : List Gate, (∀ g ∈ gs, g ∈ C.gates) →
      ∀ w : List Bool, w.length + gs.length ≤ 24 →
      (gs.map cg).foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun j => w.getD j false))]) w =
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
      simp only [List.map_cons, List.foldl_cons, hv]
      apply ih (fun a ha => hs a (List.mem_cons_of_mem g ha))
      simp only [List.length_append, List.length_cons, List.length_nil] at *
      omega
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
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
    exact ⟨(hfan a ha).1, by simp [cg]⟩
  have hDdir : ∀ g ∈ D.gates, (∀ j ∈ g.inputs, j < 9) → g.op ≠ .and ∧ g.op ≠ .not := by
    intro g hg hj
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
    apply hdir a ha
    have hl := (hfan a ha).2
    have hleft := hj (min (a.inputs.getD 0 24) 24) (by simp [cg])
    have hright := hj (min (a.inputs.getD 1 (a.inputs.getD 0 24)) 24) (by simp [cg])
    intro j hja
    rcases hins : a.inputs with _ | ⟨u, _ | ⟨v, _ | ⟨z, rest⟩⟩⟩
    · simp [hins] at hja
    · simp only [hins, List.mem_singleton] at hja
      subst j
      simp [hins, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil, -List.getD_eq_getElem?_getD] at hleft
      omega
    · simp only [hins, List.mem_cons, List.mem_nil_iff, or_false] at hja
      simp [hins, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil, -List.getD_eq_getElem?_getD] at hleft hright
      rcases hja with rfl | rfl <;> omega
    · simp [hins] at hl
  have hDbound : ∀ g ∈ D.gates, g.inputs.length = 2 ∧ ∀ j ∈ g.inputs, j ≤ 24 := by
    intro g hg
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
    refine ⟨by simp [cg], ?_⟩
    intro j hj
    simp only [cg, List.mem_cons, List.mem_nil_iff, or_false] at hj
    rcases hj with rfl | rfl <;> exact min_le_right _ _
  have hDeval (x : Fin 9 → Bool) :
      D.eval (List.ofFn x ++ [x p.1 || x p.2]) = C.eval (List.ofFn x ++ [x p.1 || x p.2]) := by
    have hw : (List.ofFn x ++ [x p.1 || x p.2]).length + C.gates.length ≤ 24 := by
      simp only [List.length_append, List.length_ofFn, List.length_singleton]
      change C.gates.length ≤ 14 at hsize
      omega
    simp only [Circuit.eval, Circuit.wires, D]
    rw [hfold C.gates (fun _ h => h) _ hw]
    exact hget _ (by rw [hlen]; exact hw) C.output
  have hsmall : D.size ≤ 14 := by omega
  have hout : D.output ≤ 24 := min_le_right _ _
  have hp' : p ∈ ([(0,1),(0,2),(0,3),(0,4),(4,6)] : List (Fin 9 × Fin 9)) ∨
      p ∈ ([(0,6)] : List (Fin 9 × Fin 9)) := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp ⊢
    tauto
  rcases hp' with hp' | hp'
  · obtain ⟨x, hx⟩ := h1 p hp' D hDfan hsmall hout hDbound hDdir
    exact ⟨x, by simpa only [hDeval] using hx⟩
  · obtain ⟨x, hx⟩ := h2 p hp' D hDfan hsmall hout hDbound hDdir
    exact ⟨x, by simpa only [hDeval] using hx⟩
