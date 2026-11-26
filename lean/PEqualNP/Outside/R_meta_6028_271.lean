import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_6028_271
    (shorter : ∀ (D : Circuit), FanInTwo D → D.size ≤ 17 → ∃ x : Fin 10 → Bool,
      D.eval (List.ofFn x ++ [x 0 && x 2]) ≠
          (fun x : Fin 10 → Bool =>
          (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
          (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
          (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) ||
          (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) x)
    (genuine : ∀ (D : Circuit) (a b : Fin 11), FanInTwo D → D.size ≤ 17 → a < b →
      ¬(a = 0 ∧ b = 10) → ¬(a = 2 ∧ b = 10) → ∃ x : Fin 10 → Bool,
        let pre := List.ofFn x ++ [x 0 && x 2]
        D.eval (pre ++ [pre.getD a false || pre.getD b false]) ≠
          (fun x : Fin 10 → Bool =>
          (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
          (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
          (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) ||
          (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) x) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → (∃ (x5 : PEqualNP.CircuitLowerBounds.Gate) (x6 : List PEqualNP.CircuitLowerBounds.Gate), x1.gates = x5 :: x6 ∧ x5.op = PEqualNP.CircuitLowerBounds.GateOp.or) → ∃ (x6 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x6 ∘ x2) ++ [x6 (0 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ))]) ≠ (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x6) := by
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
  have copyCase : ∀ (C : Circuit) (t : ℕ) (v : (Fin 10 → Bool) → Bool), FanInTwo C →
      C.size ≤ 17 → t < 11 → (∀ x, v x = (pre x).getD t false) → (∃ x, v x ≠ f x) →
      ∃ x, C.eval (pre x ++ [v x]) ≠ f x := by
    intro C t v hfan hsize ht hv hwit
    let r : ℕ → ℕ := fun i => if i < 11 then i else if i = 11 then t else i - 1
    have hlo : ∀ i, i < 11 → r i = i := fun i h => by simp [r, h]
    have hhi : ∀ i, 11 < i → r i = i - 1 := fun i h => by
      simp [r, show ¬ i < 11 by omega, show i ≠ 11 by omega]
    have h11 : r 11 = t := by simp [r]
    apply reduceTo C r (fun g => ⟨g.op, g.inputs.map r⟩)
      (fun u => u.getD 11 false = u.getD t false) v hfan hsize hlo hhi
    · intro u c hu q
      rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      exact q
    · intro g _ u w _ _ agree q
      simp only [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply]
      by_cases hi : i = 11
      · subst hi
        rw [h11, q, ← agree t (by omega), hlo t ht]
      · exact agree i hi
    · intro g hg
      exact ⟨(hfan g hg).1, by simpa using (hfan g hg).2⟩
    · intro x
      rw [List.getD_append (pre x) [v x] false t (by rw [preLen]; exact ht), ← hv x,
        List.getD_append_right _ _ _ _ (by rw [preLen]), preLen]
      rfl
    · exact hwit
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
  have copyWit : ∀ t : Fin 11, ∃ x, (pre x).getD t false ≠ f x := by
    intro t
    refine ⟨fun j => decide (j.val = t.val) ||
      (decide (t.val = 10) && (decide (j.val = 0) || decide (j.val = 2))), ?_⟩
    fin_cases t <;> decide
  have read11 : ∀ x, (pre x).getD 11 false = false :=
    fun x => List.getD_eq_default _ _ (by rw [preLen])
  have big : ∀ (i : ℕ) (x : Fin 10 → Bool), 11 ≤ i → (pre x).getD i false = false :=
    fun i x h => List.getD_eq_default _ _ (by rw [preLen]; exact h)
  have p0 : ∀ x : Fin 10 → Bool, (pre x).getD 0 false = x 0 := fun x => rfl
  have p2 : ∀ x : Fin 10 → Bool, (pre x).getD 2 false = x 2 := fun x => rfl
  have p10 : ∀ x : Fin 10 → Bool, (pre x).getD 10 false = (x 0 && x 2) := fun x => rfl
  have viaCopy : ∀ (C : Circuit) (t : ℕ) (v : (Fin 10 → Bool) → Bool), FanInTwo C →
      C.size ≤ 17 → t < 11 → (∀ x, v x = (pre x).getD t false) →
      ∃ x, C.eval (pre x ++ [v x]) ≠ f x := by
    intro C t v hfan hsize ht hv
    obtain ⟨x, hx⟩ := copyWit ⟨t, ht⟩
    exact copyCase C t v hfan hsize ht hv ⟨x, fun h => hx ((hv x).symm.trans h)⟩
  have viaFalse : ∀ (C : Circuit) (v : (Fin 10 → Bool) → Bool), FanInTwo C →
      C.size ≤ 17 → (∀ x, v x = false) →
      ∃ x, C.eval (pre x ++ [v x]) ≠ f x := by
    intro C v hfan hsize hv
    exact constCase C false v hfan hsize hv ⟨fun _ => true, by rw [hv]; decide⟩
  have orCase : ∀ (C : Circuit) (ins : List ℕ), FanInTwo C → C.size ≤ 17 → ins.length ≤ 2 →
      ∃ x, C.eval (pre x ++ [GateOp.or.eval (ins.map fun i => (pre x).getD i false)]) ≠ f x := by
    intro C ins hfan hsize hlen
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · exact viaFalse C (fun x => GateOp.or.eval (([] : List ℕ).map fun i => (pre x).getD i false))
        hfan hsize (fun x => rfl)
    · have val1 : ∀ x, GateOp.or.eval ([a].map fun i => (pre x).getD i false) =
          (pre x).getD a false := by
        intro x
        simp [evOr]
      by_cases ha : a < 11
      · exact viaCopy C a (fun x => GateOp.or.eval ([a].map fun i => (pre x).getD i false))
          hfan hsize ha val1
      · exact viaFalse C (fun x => GateOp.or.eval ([a].map fun i => (pre x).getD i false))
          hfan hsize (fun x => (val1 x).trans (big a x (by omega)))
    · have val2 : ∀ x, GateOp.or.eval ([a, b].map fun i => (pre x).getD i false) =
          ((pre x).getD a false || (pre x).getD b false) := by
        intro x
        simp [evOr]
      by_cases ha : a < 11
      · by_cases hb : b < 11
        · by_cases hab : a = b
          · exact viaCopy C a (fun x => GateOp.or.eval ([a, b].map fun i => (pre x).getD i false))
              hfan hsize ha (fun x => by rw [val2, ← hab, Bool.or_self])
          · by_cases hz : (a = 0 ∧ b = 10) ∨ (a = 10 ∧ b = 0)
            · exact viaCopy C 0
                (fun x => GateOp.or.eval ([a, b].map fun i => (pre x).getD i false))
                hfan hsize (by omega) (fun x => by
                  rw [val2]
                  rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2, p0, p10] <;>
                    generalize x 0 = p <;> generalize x 2 = q <;> cases p <;> cases q <;> rfl)
            · by_cases ht : (a = 2 ∧ b = 10) ∨ (a = 10 ∧ b = 2)
              · exact viaCopy C 2
                  (fun x => GateOp.or.eval ([a, b].map fun i => (pre x).getD i false))
                  hfan hsize (by omega) (fun x => by
                    rw [val2]
                    rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2, p2, p10] <;>
                      generalize x 0 = p <;> generalize x 2 = q <;> cases p <;> cases q <;> rfl)
              · rcases lt_or_gt_of_ne hab with h | h
                · obtain ⟨x, hx⟩ := genuine C ⟨a, ha⟩ ⟨b, hb⟩ hfan hsize h
                    (by
                      rintro ⟨h1, h2⟩
                      have e1 := congrArg Fin.val h1
                      have e2 := congrArg Fin.val h2
                      change a = 0 at e1
                      change b = 10 at e2
                      exact hz (Or.inl ⟨e1, e2⟩))
                    (by
                      rintro ⟨h1, h2⟩
                      have e1 := congrArg Fin.val h1
                      have e2 := congrArg Fin.val h2
                      change a = 2 at e1
                      change b = 10 at e2
                      exact ht (Or.inl ⟨e1, e2⟩))
                  refine ⟨x, ?_⟩
                  have hx' : C.eval (pre x ++ [((pre x).getD a false || (pre x).getD b false)]) ≠
                    f x := hx
                  rw [← val2 x] at hx'
                  exact hx'
                · obtain ⟨x, hx⟩ := genuine C ⟨b, hb⟩ ⟨a, ha⟩ hfan hsize h
                    (by
                      rintro ⟨h1, h2⟩
                      have e1 := congrArg Fin.val h1
                      have e2 := congrArg Fin.val h2
                      change b = 0 at e1
                      change a = 10 at e2
                      exact hz (Or.inr ⟨e2, e1⟩))
                    (by
                      rintro ⟨h1, h2⟩
                      have e1 := congrArg Fin.val h1
                      have e2 := congrArg Fin.val h2
                      change b = 2 at e1
                      change a = 10 at e2
                      exact ht (Or.inr ⟨e2, e1⟩))
                  refine ⟨x, ?_⟩
                  have hx' : C.eval (pre x ++ [((pre x).getD b false || (pre x).getD a false)]) ≠
                    f x := hx
                  rw [Bool.or_comm, ← val2 x] at hx'
                  exact hx'
        · exact viaCopy C a (fun x => GateOp.or.eval ([a, b].map fun i => (pre x).getD i false))
            hfan hsize ha (fun x => by rw [val2, big b x (by omega), Bool.or_false])
      · by_cases hb : b < 11
        · exact viaCopy C b (fun x => GateOp.or.eval ([a, b].map fun i => (pre x).getD i false))
            hfan hsize hb (fun x => by rw [val2, big a x (by omega), Bool.false_or])
        · exact viaFalse C (fun x => GateOp.or.eval ([a, b].map fun i => (pre x).getD i false))
            hfan hsize (fun x => by rw [val2, big a x (by omega), big b x (by omega)]; rfl)
    · simp at hlen
  have transport : ∀ (n : ℕ) (C : Circuit) (p : Fin n → Fin n), ∃ r : ℕ → ℕ,
      ∀ (x : Fin n → Bool) (rest : List Bool),
        (Circuit.mk (C.gates.map fun g : Gate => (⟨g.op, g.inputs.map r⟩ : Gate))
          (r C.output)).eval (List.ofFn x ++ rest) = C.eval (List.ofFn (x ∘ p) ++ rest) := by
    intro n C p
    let rename (i : ℕ) : ℕ := if hi : i < n then (p ⟨i, hi⟩).val else i
    have early (i : ℕ) (hi : i < n) : rename i < n := by simp [rename, hi]
    have late (i : ℕ) (hi : n ≤ i) : rename i = i := by simp [rename, Nat.not_lt.mpr hi]
    let mapGate (g : Gate) : Gate := ⟨g.op, g.inputs.map rename⟩
    refine ⟨rename, ?_⟩
    have run (gs : List Gate) (x y : List Bool) (len : x.length = y.length)
        (lo : n ≤ x.length) (agree : ∀ i, y.getD (rename i) false = x.getD i false) :
        ∀ i, ((Circuit.mk (gs.map mapGate) 0).wires y).getD (rename i) false =
          ((Circuit.mk gs 0).wires x).getD i false := by
      induction gs generalizing x y with
      | nil => exact agree
      | cons g rest ih =>
        let b := g.op.eval (g.inputs.map fun i => x.getD i false)
        have next : (mapGate g).op.eval ((mapGate g).inputs.map fun i => y.getD i false) = b := by
          simp only [b, mapGate, List.map_map, Function.comp_def, agree]
        change ∀ i, ((Circuit.mk (rest.map mapGate) 0).wires (y ++ [_])).getD (rename i) false =
          ((Circuit.mk rest 0).wires (x ++ [b])).getD i false
        rw [next]
        apply ih _ _ (by simp [len]) (by simp; omega)
        intro i
        by_cases hi : i < x.length
        · have hy : rename i < y.length := by
            by_cases hn : i < n
            · have := early i hn
              omega
            · rw [late i (by omega)]
              omega
          rw [List.getD_append _ _ _ _ hy, List.getD_append _ _ _ _ hi]
          exact agree i
        · rw [late i (by omega), List.getD_append_right _ _ _ _ (by omega),
              List.getD_append_right _ _ _ _ (by omega), len]
    intro x rest
    apply run C.gates _ _ (by simp) (by simp) _ C.output
    intro i
    by_cases hi : i < n
    · have hx : rename i < (List.ofFn x).length := by simpa using early i hi
      have hy : i < (List.ofFn (x ∘ p)).length := by simpa using hi
      rw [List.getD_append _ _ _ _ hx, List.getD_append _ _ _ _ hy,
          List.getD_eq_getElem _ _ hx, List.getD_eq_getElem _ _ hy]
      simp only [List.getElem_ofFn, Function.comp_apply]
      congr 1
      apply Fin.ext
      exact dite_eq_left hi
    · rw [late i (by omega), List.getD_append_right _ _ _ _ (by simpa using Nat.not_lt.mp hi),
          List.getD_append_right _ _ _ _ (by simpa using Nat.not_lt.mp hi)]
      simp
  intro C p hC small hOr
  obtain ⟨g, gs, hg, hop⟩ := hOr
  obtain ⟨gates, out⟩ := C
  change gates = g :: gs at hg
  subst hg
  obtain ⟨op, ins⟩ := g
  change op = GateOp.or at hop
  subst hop
  obtain ⟨r, agree⟩ := transport 10 ⟨⟨GateOp.or, ins⟩ :: gs, out⟩ p
  let D : Circuit := ⟨gs.map fun g : Gate => (⟨g.op, g.inputs.map r⟩ : Gate), r out⟩
  have dFan : FanInTwo D := by
    intro a ha
    obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
    have fan := hC a' (List.mem_cons_of_mem _ ha')
    exact ⟨fan.1, by simpa using fan.2⟩
  have dSize : D.size ≤ 17 := by
    change gs.length + 1 ≤ 18 at small
    change (gs.map fun g : Gate => (⟨g.op, g.inputs.map r⟩ : Gate)).length ≤ 17
    rw [List.length_map]
    omega
  have pinLen : (ins.map r).length ≤ 2 := by
    simpa using (hC ⟨GateOp.or, ins⟩ List.mem_cons_self).2
  obtain ⟨x, hx⟩ := orCase D (ins.map r) dFan dSize pinLen
  refine ⟨x, ?_⟩
  rw [← agree x [x 0 && x 2]]
  exact hx
