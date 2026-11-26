import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_6026_777
    (shorter : ∀ (D : Circuit), FanInTwo D → D.size ≤ 17 → ∃ x : Fin 10 → Bool,
      D.eval (List.ofFn x ++ [x 0 && x 2]) ≠
        (fun x : Fin 10 → Bool =>
          (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
          (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
          (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) ||
          (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) x)
    (genuine : ∀ (D : Circuit) (a b : Fin 11), FanInTwo D → D.size ≤ 17 → a < b →
      ¬(a = 0 ∧ b = 2) → ¬(a = 0 ∧ b = 10) → ¬(a = 2 ∧ b = 10) → ∃ x : Fin 10 → Bool,
        let pre := List.ofFn x ++ [x 0 && x 2]
        D.eval (pre ++ [pre.getD a false && pre.getD b false]) ≠
          (fun x : Fin 10 → Bool =>
          (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
          (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
          (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) ||
          (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) x) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → (∃ (x5 : PEqualNP.CircuitLowerBounds.Gate) (x6 : List PEqualNP.CircuitLowerBounds.Gate), x1.gates = x5 :: x6 ∧ x5.op = PEqualNP.CircuitLowerBounds.GateOp.and) → ∃ (x6 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x6 ∘ x2) ++ [x6 (0 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ))]) ≠ (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x6) := by
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
  have main : ∀ (C : Circuit) (pins : List (Fin 12)), FanInTwo C → C.size ≤ 17 →
      pins.length ≤ 2 → ∃ x, C.eval (pre x ++
        [GateOp.and.eval (pins.map fun j => (pre x).getD j.val false)]) ≠ f x := by
    intro C pins hfan hsize hlen
    show ∃ x, C.eval (pre x ++ [GateOp.and.eval (pins.map fun j => (pre x).getD j.val false)]) ≠ f x
    rcases pins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    ·
      exact constCase C true _ hfan hsize (fun x => rfl) ⟨fun _ => false, by decide⟩
    ·
      by_cases ha : a.val = 11
      · exact constCase C false _ hfan hsize (fun x => by simp [-List.getD_eq_getElem?_getD, evAnd, evOr, evNot, ha, read11])
          ⟨fun _ => true, by simp [-List.getD_eq_getElem?_getD, evAnd, evOr, evNot, ha, read11, f]⟩
      · have ha' : a.val < 11 := by omega
        obtain ⟨x, hx⟩ := copyWit ⟨a.val, ha'⟩
        exact copyCase C a.val _ hfan hsize ha' (fun x => by simp [evAnd, evOr, evNot])
          ⟨x, by simpa [evAnd, evOr, evNot] using hx⟩
    ·
      by_cases ha : a.val = 11
      · exact constCase C false _ hfan hsize (fun x => by simp [-List.getD_eq_getElem?_getD, evAnd, evOr, evNot, ha, read11])
          ⟨fun _ => true, by simp [-List.getD_eq_getElem?_getD, evAnd, evOr, evNot, ha, read11, f]⟩
      by_cases hb : b.val = 11
      · exact constCase C false _ hfan hsize (fun x => by simp [-List.getD_eq_getElem?_getD, evAnd, evOr, evNot, hb, read11])
          ⟨fun _ => true, by simp [-List.getD_eq_getElem?_getD, evAnd, evOr, evNot, hb, read11, f]⟩
      have ha' : a.val < 11 := by omega
      have hb' : b.val < 11 := by omega
      by_cases hab : a = b
      · subst hab
        obtain ⟨x, hx⟩ := copyWit ⟨a.val, ha'⟩
        exact copyCase C a.val _ hfan hsize ha' (fun x => by simp [evAnd, evOr, evNot])
          ⟨x, by simpa [evAnd, evOr, evNot] using hx⟩
      have hne : a.val ≠ b.val := fun h => hab (Fin.ext h)
      by_cases hdeg : (a.val = 0 ∨ a.val = 2 ∨ a.val = 10) ∧ (b.val = 0 ∨ b.val = 2 ∨ b.val = 10)
      · obtain ⟨x, hx⟩ := copyWit 10
        have hv : ∀ x, GateOp.and.eval ([a, b].map fun j => (pre x).getD j.val false) =
            (pre x).getD 10 false := by
          intro x
          rcases hdeg with ⟨h1 | h1 | h1, h2 | h2 | h2⟩ <;> (try omega) <;>
            simp [evAnd, evOr, evNot, pre, h1, h2] <;> cases x 0 <;> cases x 2 <;> simp
        exact copyCase C 10 _ hfan hsize (by omega) hv ⟨x, by rw [hv]; exact hx⟩
      · rcases lt_or_gt_of_ne hne with h | h
        · obtain ⟨x, hx⟩ := genuine C ⟨a.val, ha'⟩ ⟨b.val, hb'⟩ hfan hsize h
            (by rintro ⟨h1, h2⟩; apply hdeg; have e1 := congrArg Fin.val h1; have e2 := congrArg Fin.val h2; change a.val = 0 at e1; change b.val = 2 at e2; omega)
            (by rintro ⟨h1, h2⟩; apply hdeg; have e1 := congrArg Fin.val h1; have e2 := congrArg Fin.val h2; change a.val = 0 at e1; change b.val = 10 at e2; omega)
            (by rintro ⟨h1, h2⟩; apply hdeg; have e1 := congrArg Fin.val h1; have e2 := congrArg Fin.val h2; change a.val = 2 at e1; change b.val = 10 at e2; omega)
          refine ⟨x, ?_⟩
          have hx' : C.eval (pre x ++ [(pre x).getD a.val false && (pre x).getD b.val false]) ≠
            f x := hx
          simpa [evAnd, evOr, evNot] using hx'
        · obtain ⟨x, hx⟩ := genuine C ⟨b.val, hb'⟩ ⟨a.val, ha'⟩ hfan hsize h
            (by rintro ⟨h1, h2⟩; apply hdeg; have e1 := congrArg Fin.val h1; have e2 := congrArg Fin.val h2; change b.val = 0 at e1; change a.val = 2 at e2; omega)
            (by rintro ⟨h1, h2⟩; apply hdeg; have e1 := congrArg Fin.val h1; have e2 := congrArg Fin.val h2; change b.val = 0 at e1; change a.val = 10 at e2; omega)
            (by rintro ⟨h1, h2⟩; apply hdeg; have e1 := congrArg Fin.val h1; have e2 := congrArg Fin.val h2; change b.val = 2 at e1; change a.val = 10 at e2; omega)
          refine ⟨x, ?_⟩
          have hx' : C.eval (pre x ++ [(pre x).getD b.val false && (pre x).getD a.val false]) ≠
            f x := hx
          rw [Bool.and_comm] at hx'
          simpa [evAnd, evOr, evNot] using hx'
    · simp at hlen
  intro C p hfan hsize first
  obtain ⟨g, gs, hg, hop⟩ := first
  let r : ℕ → ℕ := fun i => if h : i < 10 then (p ⟨i, h⟩).val else i
  let pm : ℕ → Fin 12 := fun j =>
    if h : j < 10 then ⟨(p ⟨j, h⟩).val, by omega⟩ else if j = 10 then 10 else 11
  let T : Gate → Gate := fun g => ⟨g.op, g.inputs.map r⟩
  let D : Circuit := ⟨gs.map T, r C.output⟩
  have hgm : g ∈ C.gates := by simp [hg]
  have dFan : FanInTwo D := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    have hb' : b ∈ C.gates := by simp [hg, hb]
    exact ⟨(hfan b hb').1, by simpa [T] using (hfan b hb').2⟩
  have hs : gs.length + 1 = C.size := by
    change gs.length + 1 = C.gates.length
    rw [hg]
    rfl
  have dSize : D.size ≤ 17 := by
    change (gs.map T).length ≤ 17
    rw [List.length_map]
    omega
  have pLen : (g.inputs.map pm).length ≤ 2 := by simpa using (hfan g hgm).2
  obtain ⟨x, hx⟩ := main D (g.inputs.map pm) dFan dSize pLen
  refine ⟨x, ?_⟩
  let u : List Bool := List.ofFn (x ∘ p) ++ [x 0 && x 2]
  have uLen : u.length = 11 := by simp [u]
  have preAt : ∀ k : Fin 10, (pre x).getD k.val false = x k := by
    intro k
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp), List.getElem?_ofFn]
    simp
  have pre10 : (pre x).getD 10 false = (x 0 && x 2) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
    simp
  have uAt : ∀ i (h : i < 10), u.getD i false = x (p ⟨i, h⟩) := by
    intro i h
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega),
      List.getElem?_ofFn]
    simp [h]
  have u10 : u.getD 10 false = (x 0 && x 2) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
    simp
  have readPin : ∀ j, (pre x).getD (pm j).val false = u.getD j false := by
    intro j
    by_cases h : j < 10
    · have e : (pm j).val = (p ⟨j, h⟩).val := by simp [pm, h]
      rw [e, preAt, uAt j h]
    · by_cases h10 : j = 10
      · subst h10
        have e : (pm 10).val = 10 := by simp [pm]
        rw [e, pre10, u10]
      · have e : (pm j).val = 11 := by simp [pm, h, h10]
        rw [e, read11, List.getD_eq_default _ _ (by rw [uLen]; omega)]
  let gv := g.op.eval (g.inputs.map fun i => u.getD i false)
  have gvEq : GateOp.and.eval ((g.inputs.map pm).map fun j => (pre x).getD j.val false) = gv := by
    simp only [gv, hop, List.map_map, Function.comp_def, readPin]
  have run : ∀ (hs : List Gate) (a b : List Bool), a.length = b.length → 10 ≤ a.length →
      (∀ i, b.getD (r i) false = a.getD i false) →
      ∀ i, ((hs.map T).foldl step b).getD (r i) false = (hs.foldl step a).getD i false := by
    intro hs
    induction hs with
    | nil => intro a b _ _ agree; exact agree
    | cons h hs ih =>
      intro a b len lo agree
      simp only [List.map_cons, List.foldl_cons]
      have same : (T h).op.eval ((T h).inputs.map fun i => b.getD i false) =
          h.op.eval (h.inputs.map fun i => a.getD i false) := by
        simp only [T, List.map_map, Function.comp_def, agree]
      apply ih _ _ (by simp [step, len]) (by simp [step]; omega)
      intro i
      simp only [step]
      rw [same]
      by_cases h1 : i < 10
      · have e : r i = (p ⟨i, h1⟩).val := by simp [r, h1]
        have hr : r i < b.length := by rw [e]; have := (p ⟨i, h1⟩).isLt; omega
        rw [List.getD_append _ _ _ _ hr, List.getD_append _ _ _ _ (by omega)]
        exact agree i
      · have e : r i = i := by simp [r, h1]
        rw [e]
        have ai := agree i
        rw [e] at ai
        rcases lt_trichotomy i a.length with h2 | h2 | h2
        · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ h2]
          exact ai
        · rw [List.getD_append_right _ _ _ _ (by omega),
            List.getD_append_right _ _ _ _ (by omega)]
          rw [show i - b.length = 0 by omega, show i - a.length = 0 by omega]
        · rw [List.getD_eq_default _ _ (by simp; omega),
            List.getD_eq_default _ _ (by simp; omega)]
  have startAgree : ∀ i, (pre x ++ [GateOp.and.eval ((g.inputs.map pm).map
      fun j => (pre x).getD j.val false)]).getD (r i) false = (u ++ [gv]).getD i false := by
    intro i
    rw [gvEq]
    by_cases h1 : i < 10
    · have e : r i = (p ⟨i, h1⟩).val := by simp [r, h1]
      rw [e, List.getD_append (pre x) _ _ _ (by rw [preLen]; have := (p ⟨i, h1⟩).isLt; omega),
        List.getD_append u _ _ _ (by rw [uLen]; omega), preAt, uAt i h1]
    · have e : r i = i := by simp [r, h1]
      rw [e]
      by_cases h10 : i = 10
      · subst h10
        rw [List.getD_append (pre x) _ _ _ (by rw [preLen]; omega),
          List.getD_append u _ _ _ (by rw [uLen]; omega), pre10, u10]
      · by_cases h11 : i = 11
        · subst h11
          rw [List.getD_append_right (pre x) _ _ _ (by rw [preLen]),
            List.getD_append_right u _ _ _ (by rw [uLen]), preLen, uLen]
        · rw [List.getD_eq_default _ _ (by simp [preLen]; omega),
            List.getD_eq_default _ _ (by simp [uLen]; omega)]
  have key : C.eval u = D.eval (pre x ++ [GateOp.and.eval ((g.inputs.map pm).map
      fun j => (pre x).getD j.val false)]) := by
    change (C.gates.foldl step u).getD C.output false =
      ((gs.map T).foldl step _).getD (r C.output) false
    rw [hg, List.foldl_cons]
    exact (run gs (u ++ [gv]) _ (by simp [preLen, uLen]) (by simp [uLen]) startAgree C.output).symm
  change C.eval u ≠ f x
  rw [key]
  exact hx
