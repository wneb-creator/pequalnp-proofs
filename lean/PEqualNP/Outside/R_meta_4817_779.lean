import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_4817_779
    (shorter : ∀ (D : Circuit), FanInTwo D → D.size ≤ 17 → ∃ x : Fin 10 → Bool,
      D.eval (List.ofFn x ++ [x 0 && x 2]) ≠
        (fun x : Fin 10 → Bool =>
          (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
          (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
          (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) ||
          (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) x)
    (negatedPair : ∀ (D : Circuit), FanInTwo D → D.size ≤ 17 → ∃ x : Fin 10 → Bool,
      D.eval (List.ofFn x ++ [x 0 && x 2, !(x 0 && x 2)]) ≠
        (fun x : Fin 10 → Bool =>
          (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
          (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
          (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) ||
          (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) x)
    (negatedNear : ∀ (D : Circuit) (v : Fin 10), (v = 0 ∨ v = 1) → FanInTwo D → D.size ≤ 17 →
      ∃ x : Fin 10 → Bool, D.eval (List.ofFn x ++ [x 0 && x 2, !(x v)]) ≠
        (fun x : Fin 10 → Bool =>
          (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
          (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
          (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) ||
          (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) x)
    (negatedFar : ∀ (D : Circuit) (v : Fin 10), (v = 3 ∨ v = 6 ∨ v = 8) → FanInTwo D →
      D.size ≤ 17 → ∃ x : Fin 10 → Bool, D.eval (List.ofFn x ++ [x 0 && x 2, !(x v)]) ≠
        (fun x : Fin 10 → Bool =>
          (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
          (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
          (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) ||
          (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) x) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (12 : ℕ)),   PEqualNP.MetaComplexity.FanInTwo x1 →     x1.size ≤ (17 : ℕ) →       ∃ (x5 : Fin (10 : ℕ) → Bool),         have x6 : List Bool := List.ofFn x5 ++ [x5 (0 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ))];         x1.eval (x6 ++ [!x6.getD (↑x2) Bool.false]) ≠ (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x5) := by
  let f := (fun x : Fin 10 → Bool =>
          (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
          (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
          (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) ||
          (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))
  let pre (x : Fin 10 → Bool) := List.ofFn x ++ [x 0 && x 2]
  have preLen (x : Fin 10 → Bool) : (pre x).length = 11 := by simp [pre]
  have evAnd : ∀ l, GateOp.and.eval l = l.all id := fun _ => rfl
  have evOr : ∀ l, GateOp.or.eval l = l.any id := fun _ => rfl
  have evNot : ∀ l, GateOp.not.eval l = !(l.headD false) := fun _ => rfl
  let step := fun (w : List Bool) (g : Gate) =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have keep : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (gs.foldl step w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      rw [List.foldl_cons, ih _ _ (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi
  have core : ∀ (r : ℕ → ℕ) (T : Gate → Gate) (Q : List Bool → Prop),
      (∀ i, i < 11 → r i = i) → (∀ i, 11 < i → r i = i - 1) →
      (∀ (u : List Bool) (c : Bool), 12 ≤ u.length → Q u → Q (u ++ [c])) →
      ∀ (gs : List Gate),
      (∀ g ∈ gs, ∀ u w : List Bool, u.length = w.length + 1 → 11 ≤ w.length →
        (∀ i, i ≠ 11 → w.getD (r i) false = u.getD i false) → Q u →
        (T g).op.eval ((T g).inputs.map fun i => w.getD i false) =
          g.op.eval (g.inputs.map fun i => u.getD i false)) →
      ∀ u w : List Bool, u.length = w.length + 1 → 11 ≤ w.length →
        (∀ i, i ≠ 11 → w.getD (r i) false = u.getD i false) → Q u →
        (∀ i, i ≠ 11 → ((gs.map T).foldl step w).getD (r i) false =
          (gs.foldl step u).getD i false) ∧ Q (gs.foldl step u) := by
    intro r T Q hlo hhi hQ gs
    induction gs with
    | nil => intro _ u w _ _ agree q; exact ⟨agree, q⟩
    | cons g gs ih =>
      intro hT u w len lo agree q
      have same := hT g List.mem_cons_self u w len lo agree q
      simp only [List.map_cons, List.foldl_cons]
      apply ih (fun g' hg' => hT g' (List.mem_cons_of_mem _ hg'))
      · simp [step, len]
      · simp [step]; omega
      · intro i hi
        simp only [step]
        rw [same]
        rcases lt_trichotomy i 11 with h | h | h
        · rw [hlo i h, List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
          have := agree i hi
          rwa [hlo i h] at this
        · exact absurd h hi
        · rw [hhi i h]
          rcases lt_trichotomy i u.length with h2 | h2 | h2
          · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ h2]
            have := agree i hi
            rwa [hhi i h] at this
          · rw [List.getD_append_right _ _ _ _ (by omega),
              List.getD_append_right _ _ _ _ (by omega)]
            have e1 : i - 1 - w.length = 0 := by omega
            have e2 : i - u.length = 0 := by omega
            rw [e1, e2]
          · rw [List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp; omega)]
      · exact hQ _ _ (by omega) q
  have reduceTo : ∀ (C : Circuit) (r : ℕ → ℕ) (T : Gate → Gate) (Q : List Bool → Prop)
      (v : (Fin 10 → Bool) → Bool), FanInTwo C → C.size ≤ 17 →
      (∀ i, i < 11 → r i = i) → (∀ i, 11 < i → r i = i - 1) →
      (∀ (u : List Bool) (c : Bool), 12 ≤ u.length → Q u → Q (u ++ [c])) →
      (∀ g ∈ C.gates, ∀ u w : List Bool, u.length = w.length + 1 → 11 ≤ w.length →
        (∀ i, i ≠ 11 → w.getD (r i) false = u.getD i false) → Q u →
        (T g).op.eval ((T g).inputs.map fun i => w.getD i false) =
          g.op.eval (g.inputs.map fun i => u.getD i false)) →
      (∀ g ∈ C.gates, (T g).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        (T g).inputs.length ≤ 2) →
      (∀ x, Q (pre x ++ [v x])) → (∃ x, v x ≠ f x) →
      ∃ x, C.eval (pre x ++ [v x]) ≠ f x := by
    intro C r T Q v hfan hsize hlo hhi hQ hT hTfan hstart hwit
    by_cases hout : C.output = 11
    · obtain ⟨x, hx⟩ := hwit
      refine ⟨x, ?_⟩
      change (C.gates.foldl step (pre x ++ [v x])).getD C.output false ≠ f x
      rw [hout, keep _ _ _ (by simp [preLen])]
      rw [List.getD_append_right _ _ _ _ (by simp [preLen])]
      simpa [preLen] using hx
    · let D : Circuit := ⟨C.gates.map T, r C.output⟩
      have dFan : FanInTwo D := by
        intro g hg
        obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
        exact hTfan g' hg'
      have dSize : D.size ≤ 17 := by
        change (C.gates.map T).length ≤ 17
        rw [List.length_map]
        exact hsize
      obtain ⟨x, hx⟩ := shorter D dFan dSize
      refine ⟨x, ?_⟩
      have start : ∀ i, i ≠ 11 → (pre x).getD (r i) false = (pre x ++ [v x]).getD i false := by
        intro i hi
        rcases lt_trichotomy i 11 with h | h | h
        · rw [hlo i h, List.getD_append (pre x) [v x] false i (by rw [preLen]; exact h)]
        · exact absurd h hi
        · rw [hhi i h, List.getD_eq_default _ _ (by rw [preLen]; omega),
            List.getD_eq_default _ _ (by simp [preLen]; omega)]
      have run := (core r T Q hlo hhi hQ C.gates hT (pre x ++ [v x]) (pre x)
        (by simp [preLen]) (by simp [preLen]) start (hstart x)).1 C.output hout
      change (C.gates.foldl step (pre x ++ [v x])).getD C.output false ≠ f x
      rw [← run]
      exact hx
  have constCase : ∀ (C : Circuit) (b : Bool) (v : (Fin 10 → Bool) → Bool), FanInTwo C →
      C.size ≤ 17 → (∀ x, v x = b) → (∃ x, v x ≠ f x) →
      ∃ x, C.eval (pre x ++ [v x]) ≠ f x := by
    intro C b v hfan hsize hv hwit
    let r : ℕ → ℕ := fun i => if i < 11 then i else i - 1
    have hlo : ∀ i, i < 11 → r i = i := fun i h => by simp [r, h]
    have hhi : ∀ i, 11 < i → r i = i - 1 := fun i h => by simp [r, show ¬ i < 11 by omega]
    let T : Gate → Gate := fun g =>
      if 11 ∈ g.inputs then
        if g.op.eval [] && !(g.op.eval [false, true]) then
          (if b then ⟨GateOp.and, (g.inputs.filter (fun i => i != 11)).map r⟩
          else ⟨GateOp.or, []⟩)
        else if !(g.op.eval []) then
          (if b then ⟨GateOp.and, []⟩
          else ⟨GateOp.or, (g.inputs.filter (fun i => i != 11)).map r⟩)
        else if g.inputs.head? = some 11 then (if b then ⟨GateOp.or, []⟩ else ⟨GateOp.and, []⟩)
        else ⟨g.op, g.inputs.map r⟩
      else ⟨g.op, g.inputs.map r⟩
    apply reduceTo C r T (fun u => u.getD 11 false = b) v hfan hsize hlo hhi
    · intro u c hu q
      rw [List.getD_append _ _ _ _ (by omega)]
      exact q
    · intro g hg u w _ _ agree q
      obtain ⟨hop, hlen⟩ := hfan g hg
      rcases g with ⟨op, ins⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      rcases ins with _ | ⟨p, _ | ⟨p', _ | ⟨p'', rest⟩⟩⟩
      · rcases hop with rfl | rfl | rfl <;> simp [-List.getD_eq_getElem?_getD, T, evAnd, evOr, evNot]
      ·
        by_cases hp : p = 11
        · subst hp
          rcases hop with rfl | rfl | rfl <;> cases b <;> simp [-List.getD_eq_getElem?_getD, T, evAnd, evOr, evNot, q]
        · have ap := agree p hp
          rcases hop with rfl | rfl | rfl <;> cases b <;> simp [-List.getD_eq_getElem?_getD, T, evAnd, evOr, evNot, Ne.symm hp, ap]
      ·
        by_cases hp : p = 11 <;> by_cases hp' : p' = 11
        · subst hp hp'
          rcases hop with rfl | rfl | rfl <;> cases b <;> simp [-List.getD_eq_getElem?_getD, T, evAnd, evOr, evNot, q]
        · subst hp
          have ap' := agree p' hp'
          rcases hop with rfl | rfl | rfl <;> cases b <;> simp [-List.getD_eq_getElem?_getD, T, evAnd, evOr, evNot, q, hp', Ne.symm hp', ap']
        · subst hp'
          have ap := agree p hp
          rcases hop with rfl | rfl | rfl <;> cases b <;> simp [-List.getD_eq_getElem?_getD, T, evAnd, evOr, evNot, q, hp, Ne.symm hp, ap]
        · have ap := agree p hp
          have ap' := agree p' hp'
          rcases hop with rfl | rfl | rfl <;> cases b <;> simp [-List.getD_eq_getElem?_getD, T, evAnd, evOr, evNot, Ne.symm hp, ap, Ne.symm hp', ap']
      · simp at hlen
    · intro g hg
      obtain ⟨hop, hlen⟩ := hfan g hg
      rcases g with ⟨op, ins⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      rcases ins with _ | ⟨p, _ | ⟨p', _ | ⟨p'', rest⟩⟩⟩
      · rcases hop with rfl | rfl | rfl <;> simp [T, evAnd, evOr, evNot]
      ·
        by_cases hp : p = 11
        · subst hp
          rcases hop with rfl | rfl | rfl <;> cases b <;> simp [T, evAnd, evOr, evNot]
        · rcases hop with rfl | rfl | rfl <;> cases b <;> simp [T, evAnd, evOr, evNot, hp, Ne.symm hp]
      ·
        by_cases hp : p = 11 <;> by_cases hp' : p' = 11
        · subst hp hp'
          rcases hop with rfl | rfl | rfl <;> cases b <;> simp [T, evAnd, evOr, evNot]
        · subst hp
          rcases hop with rfl | rfl | rfl <;> cases b <;> simp [T, evAnd, evOr, evNot, hp', Ne.symm hp']
        · subst hp'
          rcases hop with rfl | rfl | rfl <;> cases b <;> simp [T, evAnd, evOr, evNot, hp, Ne.symm hp]
        · rcases hop with rfl | rfl | rfl <;> cases b <;> simp [T, evAnd, evOr, evNot, hp, hp', Ne.symm hp, Ne.symm hp']
      · simp at hlen
    · intro x
      show (pre x ++ [v x]).getD 11 false = b
      rw [List.getD_append_right _ _ _ _ (by rw [preLen]), preLen]
      exact hv x
    · exact hwit
  have read11 : ∀ x, (pre x).getD 11 false = false :=
    fun x => List.getD_eq_default _ _ (by rw [preLen])
  have slot : ∀ (z : Fin 10 → Bool) (a b : Bool) (j : ℕ),
      (List.ofFn z ++ [a, b]).getD j false =
        if h : j < 10 then z ⟨j, h⟩ else if j = 10 then a else if j = 11 then b else false := by
    intro z a b j
    by_cases h : j < 10
    · have h' : j < (List.ofFn z).length := by simpa using h
      rw [dif_pos h, List.getD_append _ _ _ _ h', List.getD_eq_getElem _ _ h', List.getElem_ofFn]
    · rw [dif_neg h, List.getD_append_right _ _ _ _ (by simp; omega), List.length_ofFn]
      obtain ⟨m, rfl⟩ : ∃ m, j = 10 + m := ⟨j - 10, by omega⟩
      rcases m with _ | _ | m
      · simp
      · simp
      · rw [if_neg (by omega), if_neg (by omega)]
        exact List.getD_eq_default _ _ (by simp)
  have permCore : ∀ (ρ : ℕ → ℕ), (∀ i, 10 ≤ i → ρ i = i) → (∀ i, i < 10 → ρ i < 10) →
      ∀ (gs : List Gate) (u w : List Bool), u.length = w.length → 10 ≤ u.length →
        (∀ j, w.getD (ρ j) false = u.getD j false) →
        ∀ j, ((gs.map fun g => (⟨g.op, g.inputs.map ρ⟩ : Gate)).foldl step w).getD (ρ j) false =
          (gs.foldl step u).getD j false := by
    intro ρ hhi hlo gs
    induction gs with
    | nil => intro u w _ _ agree; exact agree
    | cons g gs ih =>
      intro u w len lo agree
      simp only [List.map_cons, List.foldl_cons]
      have same : g.op.eval ((g.inputs.map ρ).map fun i => w.getD i false) =
          g.op.eval (g.inputs.map fun i => u.getD i false) := by
        rw [List.map_map]
        congr 1
        apply List.map_congr_left
        intro i _
        exact agree i
      apply ih
      · simp [step, len]
      · simp [step]; omega
      · intro j
        simp only [step]
        rw [same]
        rcases lt_trichotomy j u.length with h | h | h
        · have hρ : ρ j < w.length := by
            by_cases hj : j < 10
            · have := hlo j hj; omega
            · rw [hhi j (by omega)]; omega
          rw [List.getD_append _ _ _ _ hρ, List.getD_append _ _ _ _ h]
          exact agree j
        · subst h
          rw [hhi _ lo, List.getD_append_right _ _ _ _ (by omega),
            List.getD_append_right _ _ _ _ (by omega)]
          rw [show u.length - w.length = 0 by omega, Nat.sub_self]
        · rw [hhi j (by omega), List.getD_eq_default _ _ (by simp; omega),
            List.getD_eq_default _ _ (by simp; omega)]
  let perms : List (List ℕ) := [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
    [0, 1, 2, 7, 5, 4, 6, 3, 9, 8],
    [2, 1, 0, 4, 3, 7, 6, 5, 9, 8],
    [2, 1, 0, 5, 7, 3, 6, 4, 8, 9]]
  let σ (p : Fin 4) (i : Fin 10) : Fin 10 := Fin.ofNat 10 ((perms.getD p.val []).getD i.val 0)
  have pick : ∀ v : Fin 10, ∃ p : Fin 4,
      (σ p v = 0 ∨ σ p v = 1) ∨ (σ p v = 3 ∨ σ p v = 6 ∨ σ p v = 8) := by
    decide +kernel
  have either : ∀ p : Fin 4, (σ p 0 = 0 ∧ σ p 2 = 2) ∨ (σ p 0 = 2 ∧ σ p 2 = 0) := by
    decide +kernel
  have invariant : ∀ (p : Fin 4) (y : Fin 10 → Bool), f (fun j => y (σ p j)) = f y := by
    decide +kernel
  have symCase : ∀ (C : Circuit) (v : Fin 10), FanInTwo C → C.size ≤ 17 →
      ∃ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [x 0 && x 2, !(x v)]) ≠ f x := by
    intro C v hfan hsize
    obtain ⟨p, hp⟩ := pick v
    let ρ : ℕ → ℕ := fun i => if h : i < 10 then (σ p ⟨i, h⟩).val else i
    have hhi : ∀ i, 10 ≤ i → ρ i = i := fun i h => dif_neg (by omega)
    have hlo : ∀ i, i < 10 → ρ i < 10 := fun i h => by
      simp only [ρ, dif_pos h]
      exact (σ p _).isLt
    let D : Circuit := ⟨C.gates.map fun g => (⟨g.op, g.inputs.map ρ⟩ : Gate), ρ C.output⟩
    have dFan : FanInTwo D := by
      intro g hg
      obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      exact ⟨(hfan g' hg').1, by simpa using (hfan g' hg').2⟩
    have dSize : D.size ≤ 17 := by
      change (C.gates.map _).length ≤ 17
      rw [List.length_map]
      exact hsize
    have hD : ∃ y : Fin 10 → Bool,
        D.eval (List.ofFn y ++ [y 0 && y 2, !(y (σ p v))]) ≠ f y := by
      rcases hp with near | far
      · exact negatedNear D _ near dFan dSize
      · exact negatedFar D _ far dFan dSize
    obtain ⟨y, hy⟩ := hD
    refine ⟨fun j => y (σ p j), ?_⟩
    rw [invariant p y]
    intro heq
    apply hy
    rw [← heq]
    change ((C.gates.map fun g => (⟨g.op, g.inputs.map ρ⟩ : Gate)).foldl step
        (List.ofFn y ++ [y 0 && y 2, !(y (σ p v))])).getD (ρ C.output) false =
      (C.gates.foldl step (List.ofFn (fun j => y (σ p j)) ++
        [y (σ p 0) && y (σ p 2), !(y (σ p v))])).getD C.output false
    apply permCore ρ hhi hlo C.gates _ _ (by simp) (by simp)
    intro j
    rw [slot, slot]
    by_cases hj : j < 10
    · have hρ : ρ j = (σ p ⟨j, hj⟩).val := dif_pos hj
      rw [hρ, dif_pos (σ p _).isLt, dif_pos hj]
    · rw [hhi j (by omega), dif_neg hj, dif_neg hj]
      by_cases h10 : j = 10
      · rw [if_pos h10, if_pos h10]
        rcases either p with ⟨h0, h2⟩ | ⟨h0, h2⟩
        · rw [h0, h2]
        · rw [h0, h2, Bool.and_comm]
      · rw [if_neg h10, if_neg h10]
  intro C k hfan hsize
  show ∃ x, C.eval (pre x ++ [!(pre x).getD k.val false]) ≠ f x
  have reshape : ∀ (x : Fin 10 → Bool) (c : Bool),
      pre x ++ [c] = List.ofFn x ++ [x 0 && x 2, c] := by
    intro x c
    simp [pre]
  by_cases h11 : k.val = 11
  · exact constCase C true (fun x => !(pre x).getD k.val false) hfan hsize
      (fun x => by rw [h11, read11]; rfl) ⟨fun _ => false, by rw [h11, read11]; decide⟩
  by_cases h10 : k.val = 10
  · obtain ⟨x, hx⟩ := negatedPair C hfan hsize
    refine ⟨x, ?_⟩
    rw [reshape, h10]
    have e : (pre x).getD 10 false = (x 0 && x 2) := by
      rw [List.getD_append_right _ _ _ _ (by simp)]
      simp
    rw [e]
    exact hx
  · have hk : k.val < 10 := by omega
    obtain ⟨x, hx⟩ := symCase C ⟨k.val, hk⟩ hfan hsize
    refine ⟨x, ?_⟩
    rw [reshape]
    have e : (pre x).getD k.val false = x ⟨k.val, hk⟩ := by
      rw [List.getD_append _ _ _ _ (by simpa using hk), List.getD_eq_getElem _ _ (by simpa using hk),
        List.getElem_ofFn]
    rw [e]
    exact hx
