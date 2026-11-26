import Mathlib.Data.List.GetD
import Mathlib.Tactic.ByContra
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_4077_317
    (h670 : ¬ PEqualNP.MetaComplexity.HasCircuitSize 9
      (fun x : Fin 9 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
        (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
        (x 6 && x 8) || (x 8 && x 5)) 15)
    (h18 : ¬ PEqualNP.MetaComplexity.HasCircuitSize 10
      (fun (x : Fin 10 → Bool) =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
        x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) 18)
    (hLow : ∀ (b : Bool) (D : PEqualNP.CircuitLowerBounds.Circuit) (u : ℕ),
      PEqualNP.MetaComplexity.FanInTwo D → D.size = 17 → 11 ≤ u → u < 27 →
      (D.gates.filter fun g => (g.inputs.take (if g.op.eval [true] = true then 2 else 1)).contains 0).length ≤ 2 →
      (D.gates.filter fun g => (g.inputs.take (if g.op.eval [true] = true then 2 else 1)).contains (if b = true then 1 else 2)).length ≤ 2 →
      let f := fun x : Fin 10 → Bool => [1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85].any fun e : ℕ => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10));
      let w := fun (x : Fin 10 → Bool) (p : ℕ) => (D.wires (List.ofFn x ++ [x 0 || if b = true then x 1 else x 2])).getD p false;
      (∃ x, w x u = true ∧ w x 27 = false) → (∃ x, w x u = false ∧ w x 27 = true) →
      ¬ (∀ x, (w x u && w x 27) = f x)) :
    ∀ (x1 : Bool) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size ≤ (17 : ℕ) →       have x7 : (Fin (10 : ℕ) → Bool) → Bool := fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ));       have x8 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x8 : Fin (10 : ℕ) → Bool) (x9 : ℕ) => (x2.wires (List.ofFn x8 ++ [x8 (0 : Fin (10 : ℕ)) || if x1 = Bool.true then x8 (1 : Fin (10 : ℕ)) else x8 (2 : Fin (10 : ℕ))])).getD x9 Bool.false;       (∃ (x9 : Fin (10 : ℕ) → Bool), x8 x9 x3 = Bool.true ∧ x8 x9 x4 = Bool.false) → (∃ (x10 : Fin (10 : ℕ) → Bool), x8 x10 x3 = Bool.false ∧ x8 x10 x4 = Bool.true) → (∀ (x11 : Fin (10 : ℕ) → Bool), x7 x11 = Bool.true → x8 x11 x3 = Bool.true ∧ x8 x11 x4 = Bool.true) → ∃ (x12 : Fin (10 : ℕ) → Bool), x7 x12 = Bool.false ∧ x8 x12 x3 = Bool.true ∧ x8 x12 x4 = Bool.true := by
  intro x1 x2 x3 x4 hfan hsize x7 x8 H1 H2 H3
  by_contra hneg
  have exactPair (x : Fin 10 → Bool) : (x8 x x3 && x8 x x4) = x7 x := by
    cases hx : x7 x
    · cases hA : x8 x x3 <;> cases hB : x8 x x4 <;> try rfl
      exact (hneg ⟨x, hx, hA, hB⟩).elim
    · obtain ⟨hA, hB⟩ := H3 x hx
      simp [hA, hB]
  let step (ws : List Bool) (g : Gate) := ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
  have lengthRun (gs : List Gate) (ws : List Bool) :
      (gs.foldl step ws).length = ws.length + gs.length := by
    induction gs generalizing ws with
    | nil => simp
    | cons g gs ih =>
      change (gs.foldl step (step ws g)).length = _
      rw [ih]
      simp [step]
      omega
  have retain (gs : List Gate) (ws : List Bool) (i : ℕ) (hi : i < ws.length) :
      (gs.foldl step ws).getD i false = ws.getD i false := by
    induction gs generalizing ws with
    | nil => rfl
    | cons g gs ih =>
      change (gs.foldl step (step ws g)).getD i false = ws.getD i false
      rw [ih _ (by simpa [step] using Nat.lt_succ_of_lt hi)]
      exact List.getD_append _ _ _ _ hi
  have getD_snoc_end : ∀ {α : Type} (l : List α) (a d : α), (l ++ [a]).getD l.length d = a := by
    intro α l a d
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (Nat.le_refl _)]
    simp
  let seed (x : Fin 10 → Bool) : List Bool :=
    List.ofFn x ++ [x 0 || if x1 = true then x 1 else x 2]
  have seed_len (x : Fin 10 → Bool) : (seed x).length = 11 := by simp [seed]
  have bound (i : ℕ) (h : ∀ x, x7 x = true → x8 x i = true) : 11 ≤ i ∧ i < 11 + x2.size := by
    let xa := fun j : Fin 10 => (24 : ℕ).testBit j.val
    let xb := fun j : Fin 10 => (160 : ℕ).testBit j.val
    have hxa : x8 xa i = true := h xa (by decide)
    have hxb : x8 xb i = true := h xb (by decide)
    have hlo : 11 ≤ i := by
      by_contra! hi
      have readA := retain x2.gates (seed xa) i (by rwa [seed_len])
      have readB := retain x2.gates (seed xb) i (by rwa [seed_len])
      change (x2.gates.foldl step (seed xa)).getD i false = true at hxa
      change (x2.gates.foldl step (seed xb)).getD i false = true at hxb
      rw [readA] at hxa
      rw [readB] at hxb
      have incompatible : ∀ (b : Bool) (j : Fin 11),
          ¬ ((List.ofFn xa ++ [xa 0 || if b = true then xa 1 else xa 2]).getD j.val false = true ∧
             (List.ofFn xb ++ [xb 0 || if b = true then xb 1 else xb 2]).getD j.val false = true) := by
        decide
      exact incompatible x1 ⟨i, hi⟩ ⟨hxa, hxb⟩
    refine ⟨hlo, ?_⟩
    by_contra! hi
    change (x2.gates.foldl step (seed xa)).getD i false = true at hxa
    rw [List.getD_eq_default _ _ (by rw [lengthRun, seed_len]; exact hi)] at hxa
    exact Bool.false_ne_true hxa
  have hx3 := bound x3 (fun x hx => (H3 x hx).1)
  have hx4 := bound x4 (fun x hx => (H3 x hx).2)
  have hne34 : x3 ≠ x4 := by
    rintro rfl
    obtain ⟨x, h1, h2⟩ := H1
    rw [h1] at h2
    exact Bool.noConfusion h2
  let u := min x3 x4
  let v := max x3 x4
  have huv : u < v := by
    rcases lt_or_gt_of_ne hne34 with h | h
    · simpa [u, v, min_eq_left h.le, max_eq_right h.le] using h
    · simpa [u, v, min_eq_right h.le, max_eq_left h.le] using h
  have hu : 11 ≤ u := le_min hx3.1 hx4.1
  have hv : v < 11 + x2.size := max_lt hx3.2 hx4.2
  have evalPair (x : Fin 10 → Bool) : (x8 x u && x8 x v) = x7 x := by
    rcases le_total x3 x4 with h | h
    · simpa [u, v, min_eq_left h, max_eq_right h] using exactPair x
    · simpa [u, v, min_eq_right h, max_eq_left h, Bool.and_comm] using exactPair x
  have hu_not_v : ∃ x, x8 x u = true ∧ x8 x v = false := by
    rcases le_total x3 x4 with h | h
    · simpa [u, v, min_eq_left h, max_eq_right h] using H1
    · obtain ⟨x, h1, h2⟩ := H2
      exact ⟨x, by simpa [u, min_eq_right h] using h2, by simpa [v, max_eq_left h] using h1⟩
  have hv_not_u : ∃ x, x8 x u = false ∧ x8 x v = true := by
    rcases le_total x3 x4 with h | h
    · simpa [u, v, min_eq_left h, max_eq_right h] using H2
    · obtain ⟨x, h1, h2⟩ := H1
      exact ⟨x, by simpa [u, min_eq_right h] using h2, by simpa [v, max_eq_left h] using h1⟩
  have hv27 : v = 27 := by
    by_contra hv'
    have hvlt : v < 27 := by omega
    let gs := x2.gates.take (v - 10)
    have hgs : gs.length = v - 10 := by
      have hz : v - 10 ≤ x2.size := by omega
      change v - 10 ≤ x2.gates.length at hz
      simp [gs, List.length_take, Nat.min_eq_left hz]
    let pIdx : ℕ := if x1 = true then 1 else 2
    let front : Gate := ⟨GateOp.or, [0, pIdx]⟩
    let final : Gate := ⟨GateOp.and, [u, v]⟩
    let D : Circuit := ⟨front :: (gs ++ [final]), 11 + gs.length⟩
    have legal : FanInTwo D := by
      intro g hg
      change g ∈ front :: (gs ++ [final]) at hg
      rcases List.mem_cons.mp hg with rfl | hg
      · simp [front]
      rcases List.mem_append.mp hg with hg | hg
      · exact hfan g (List.mem_of_mem_take hg)
      · obtain rfl := List.mem_singleton.mp hg
        simp [final]
    have short : D.size ≤ 18 := by
      change (front :: (gs ++ [final])).length ≤ 18
      simp only [List.length_cons, List.length_append, List.length_nil]
      omega
    refine h18 ⟨D, legal, short, ?_⟩
    intro x
    let ws := gs.foldl step (seed x)
    have plen : ws.length = 11 + gs.length := by simp [ws, seed_len, lengthRun]
    have prep : step (List.ofFn x) front = seed x := by
      have h0 : (List.ofFn x).getD 0 false = x 0 := by simp [List.getD_eq_getElem?_getD]
      have h1 : (List.ofFn x).getD 1 false = x 1 := by simp [List.getD_eq_getElem?_getD]
      have h2 : (List.ofFn x).getD 2 false = x 2 := by simp [List.getD_eq_getElem?_getD]
      dsimp only [step, front, pIdx, seed]
      cases hx1 : x1
      · change List.ofFn x ++ [((List.ofFn x).getD 0 false || ((List.ofFn x).getD 2 false || false))] =
          List.ofFn x ++ [x 0 || x 2]
        rw [h0, h2, Bool.or_false]
      · change List.ofFn x ++ [((List.ofFn x).getD 0 false || ((List.ofFn x).getD 1 false || false))] =
          List.ofFn x ++ [x 0 || x 1]
        rw [h0, h1, Bool.or_false]
    have result (i : ℕ) (h : i ≤ v) : ws.getD i false = x8 x i := by
      have hi : i < ws.length := by omega
      have split : x2.gates = gs ++ x2.gates.drop (v - 10) := (List.take_append_drop _ _).symm
      change ws.getD i false = (x2.gates.foldl step (seed x)).getD i false
      rw [split, List.foldl_append]
      exact (retain _ _ _ hi).symm
    change (((gs ++ [final]).foldl step (step (List.ofFn x) front)).getD (11 + gs.length) false) = x7 x
    rw [prep, List.foldl_append]
    change (step ws final).getD (11 + gs.length) false = x7 x
    rw [← plen]
    have atEnd : (step ws final).getD ws.length false = (ws.getD u false && ws.getD v false) := by
      change (ws ++ [ws.getD u false && (ws.getD v false && true)]).getD ws.length false = _
      rw [getD_snoc_end, Bool.and_true]
    rw [atEnd, result _ huv.le, result _ le_rfl]
    exact evalPair x
  have size17 : x2.size = 17 := by omega
  have hu27 : u < 27 := by omega
  have eval27 (x : Fin 10 → Bool) : (x8 x u && x8 x 27) = x7 x := by simpa [hv27] using evalPair x
  have hu_not_27 : ∃ x, x8 x u = true ∧ x8 x 27 = false := by simpa [hv27] using hu_not_v
  have h27_not_u : ∃ x, x8 x u = false ∧ x8 x 27 = true := by simpa [hv27] using hv_not_u
  let reads (z : ℕ) (g : Gate) : Bool :=
    (g.inputs.take (if g.op.eval [true] = true then 2 else 1)).contains z
  have pc10 : ∀ x : Fin 10 → Bool,
      ([1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85].any fun e : ℕ =>
        x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10))) = x7 x := by
    intro x
    have h : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : Bool,
        (a0 && a1 || (a1 && a2 || (a2 && a3 || (a3 && a4 || (a4 && a0 || (a0 && a5 || (a1 && a6 || (a2 && a7 || (a3 && a8 || (a4 && a9 || (a5 && a7 || (a7 && a9 || (a9 && a6 || (a6 && a8 || (a8 && a5 || false))))))))))))))) =
        (a0 && a1 || a1 && a2 || a2 && a3 || a3 && a4 || a4 && a0 || a0 && a5 || a1 && a6 || a2 && a7 || a3 && a8 || a4 && a9 || a5 && a7 || a7 && a9 || a9 && a6 || a6 && a8 || a8 && a5) := by
      decide
    exact h (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9)
  let p9 : (Fin 9 → Bool) → Bool := fun y =>
    (y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 3 && y 4) || (y 4 && y 0) ||
    (y 0 && y 5) || (y 1 && y 6) || (y 2 && y 7) || (y 3 && y 8) || (y 5 && y 7) ||
    (y 6 && y 8) || (y 8 && y 5)
  let evalSym : Bool ⊕ ℕ → List Bool → Bool :=
    fun s ws => Sum.elim id (fun k => ws.getD k false) s
  let elimGate : List (Bool ⊕ ℕ) → ℕ → Gate → (Bool ⊕ ℕ) × Option Gate := fun st outIdx g =>
    let ins := g.inputs.map (fun i => st.getD i (Sum.inl false))
    GateOp.casesOn g.op
      (List.casesOn ins
        (Sum.inl true, none)
        (fun a rest => List.casesOn rest
          (a, none)
          (fun b _ => Sum.elim
            (fun ba => Bool.casesOn ba (Sum.inl false, none) (b, none))
            (fun ka => Sum.elim
              (fun bb => Bool.casesOn bb (Sum.inl false, none) (Sum.inr ka, none))
              (fun kb => (Sum.inr outIdx, some ⟨.and, [ka, kb]⟩)) b) a)))
      (List.casesOn ins
        (Sum.inl false, none)
        (fun a rest => List.casesOn rest
          (a, none)
          (fun b _ => Sum.elim
            (fun ba => Bool.casesOn ba (b, none) (Sum.inl true, none))
            (fun ka => Sum.elim
              (fun bb => Bool.casesOn bb (Sum.inr ka, none) (Sum.inl true, none))
              (fun kb => (Sum.inr outIdx, some ⟨.or, [ka, kb]⟩)) b) a)))
      (List.casesOn ins
        (Sum.inl true, none)
        (fun a _ => Sum.elim
          (fun ba => (Sum.inl (!ba), none))
          (fun ka => (Sum.inr outIdx, some ⟨.not, [ka]⟩)) a))
      (fun _ => (Sum.inl false, none))
      (Sum.inl false, none)
  have eval_and : ∀ l, GateOp.and.eval l = l.all id := fun _ => rfl
  have eval_or : ∀ l, GateOp.or.eval l = l.any id := fun _ => rfl
  have eval_not : ∀ l, GateOp.not.eval l = !(l.headD false) := fun _ => rfl
  have elimGate_kills : ∀ (st : List (Bool ⊕ ℕ)) (outIdx z : ℕ) (g : Gate),
      (g.op ∈ ({.and, .or, .not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      st.getD z (Sum.inl false) = Sum.inl false →
      reads z g = true →
      (elimGate st outIdx g).2 = none := by
    intro st outIdx z g hok hz hread
    have hop := hok.1
    have hlen := hok.2
    rcases hop with hop | hop | hop
    · have ht : g.op.eval [true] = true := by rw [hop]; rfl
      dsimp only [reads] at hread
      rw [ht] at hread
      simp only [↓reduceIte] at hread
      cases hg : g.inputs with
      | nil => rw [hg] at hread; simp at hread
      | cons i1 t1 =>
        cases t1 with
        | nil => simp [elimGate, hop, hg]
        | cons i2 t2 =>
          cases t2 with
          | nil =>
            rw [hg] at hread
            simp only [List.take, List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_true, beq_iff_eq] at hread
            dsimp only [elimGate]
            rw [hop, hg]
            simp only [List.map_cons, List.map_nil]
            rcases hread with rfl | rfl
            · rw [hz]; rfl
            · rw [hz]
              cases st.getD i1 (Sum.inl false) with
              | inl b1 => cases b1 <;> rfl
              | inr k1 => rfl
          | cons i3 t3 => rw [hg] at hlen; simp at hlen
    · have ht : g.op.eval [true] = true := by rw [hop]; rfl
      dsimp only [reads] at hread
      rw [ht] at hread
      simp only [↓reduceIte] at hread
      cases hg : g.inputs with
      | nil => rw [hg] at hread; simp at hread
      | cons i1 t1 =>
        cases t1 with
        | nil => simp [elimGate, hop, hg]
        | cons i2 t2 =>
          cases t2 with
          | nil =>
            rw [hg] at hread
            simp only [List.take, List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_true, beq_iff_eq] at hread
            dsimp only [elimGate]
            rw [hop, hg]
            simp only [List.map_cons, List.map_nil]
            rcases hread with rfl | rfl
            · rw [hz]; rfl
            · rw [hz]
              cases st.getD i1 (Sum.inl false) with
              | inl b1 => cases b1 <;> rfl
              | inr k1 => rfl
          | cons i3 t3 => rw [hg] at hlen; simp at hlen
    · change g.op = .not at hop
      have ht : g.op.eval [true] = false := by rw [hop]; rfl
      dsimp only [reads] at hread
      rw [ht] at hread
      simp only [Bool.false_eq_true, ↓reduceIte] at hread
      cases hg : g.inputs with
      | nil => rw [hg] at hread; simp at hread
      | cons i1 t1 =>
        rw [hg] at hread
        simp only [List.take, List.contains_cons, List.contains_nil, Bool.or_false, beq_iff_eq] at hread
        subst hread
        dsimp only [elimGate]
        rw [hop, hg]
        simp only [List.map_cons, hz]
        rfl
  have elimGate_ok : ∀ (st : List (Bool ⊕ ℕ)) (outIdx : ℕ) (g : Gate),
      (g.op ∈ ({.and, .or, .not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      (∀ (wsN wsO : List Bool), wsN.length = outIdx →
        (∀ i < st.length, evalSym (st.getD i (Sum.inl false)) wsN = wsO.getD i false) →
        wsO.length = st.length →
        let r := elimGate st outIdx g
        let wsN' := Option.elim r.2 wsN (fun g' => step wsN g')
        (Option.elim r.2 True (fun g' => g'.op ∈ ({.and, .or, .not} : Set GateOp) ∧ g'.inputs.length ≤ 2)) ∧
        evalSym r.1 wsN' = g.op.eval (g.inputs.map (fun i => wsO.getD i false))) := by
    intro st outIdx g hok wsN wsO hlenN hagree hlenO
    have hop := hok.1
    have hlen := hok.2
    have hval : ∀ i, evalSym (st.getD i (Sum.inl false)) wsN = wsO.getD i false := by
      intro i
      by_cases hi : i < st.length
      · exact hagree i hi
      · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi),
            List.getD_eq_default _ _ (by omega : wsO.length ≤ i)]
        rfl
    rcases hop with hop | hop | hop
    · cases hg : g.inputs with
      | nil =>
        simp only [elimGate, hop, hg, List.map_nil, eval_and, List.all_nil, Option.elim_none,
          evalSym, Sum.elim_inl]
        exact ⟨trivial, rfl⟩
      | cons i1 t1 =>
        cases t1 with
        | nil =>
          simp only [elimGate, hop, hg, List.map_cons, List.map_nil, eval_and, List.all_cons,
            List.all_nil, id, Bool.and_true, Option.elim_none]
          exact ⟨trivial, hval i1⟩
        | cons i2 t2 =>
          cases t2 with
          | nil =>
            have h1 := hval i1
            have h2 := hval i2
            dsimp only [elimGate]
            rw [hop, hg]
            simp only [List.map_cons, List.map_nil, eval_and, List.all_cons, List.all_nil, id, Bool.and_true]
            cases hs1 : st.getD i1 (Sum.inl false) with
            | inl b1 =>
              rw [hs1] at h1
              simp only [evalSym, Sum.elim_inl, id] at h1
              cases b1
              · simp only [Sum.elim_inl, Option.elim_none, evalSym, id, ← h1, Bool.false_and, and_self]
              · simp only [Sum.elim_inl, Option.elim_none, ← h1, Bool.true_and, true_and]; exact h2
            | inr k1 =>
              rw [hs1] at h1
              simp only [evalSym, Sum.elim_inr] at h1
              cases hs2 : st.getD i2 (Sum.inl false) with
              | inl b2 =>
                rw [hs2] at h2
                simp only [evalSym, Sum.elim_inl, id] at h2
                cases b2
                · simp only [Sum.elim_inr, Sum.elim_inl, Option.elim_none, evalSym, id, ← h2, Bool.and_false, and_self]
                · simp only [Sum.elim_inr, Sum.elim_inl, Option.elim_none, evalSym, ← h2, Bool.and_true, true_and]; exact h1
              | inr k2 =>
                rw [hs2] at h2
                simp only [evalSym, Sum.elim_inr] at h2
                simp only [Sum.elim_inr, Option.elim_some]
                refine ⟨⟨Or.inl rfl, by simp⟩, ?_⟩
                simp only [evalSym, Sum.elim_inr, step, ← hlenN, getD_snoc_end,
                  List.map_cons, List.map_nil, eval_and, List.all_cons, List.all_nil, id, Bool.and_true]
                rw [h1, h2]
          | cons i3 t3 => rw [hg] at hlen; simp at hlen
    · cases hg : g.inputs with
      | nil =>
        simp only [elimGate, hop, hg, List.map_nil, eval_or, List.any_nil, Option.elim_none,
          evalSym, Sum.elim_inl]
        exact ⟨trivial, rfl⟩
      | cons i1 t1 =>
        cases t1 with
        | nil =>
          simp only [elimGate, hop, hg, List.map_cons, List.map_nil, eval_or, List.any_cons,
            List.any_nil, id, Bool.or_false, Option.elim_none]
          exact ⟨trivial, hval i1⟩
        | cons i2 t2 =>
          cases t2 with
          | nil =>
            have h1 := hval i1
            have h2 := hval i2
            dsimp only [elimGate]
            rw [hop, hg]
            simp only [List.map_cons, List.map_nil, eval_or, List.any_cons, List.any_nil, id, Bool.or_false]
            cases hs1 : st.getD i1 (Sum.inl false) with
            | inl b1 =>
              rw [hs1] at h1
              simp only [evalSym, Sum.elim_inl, id] at h1
              cases b1
              · simp only [Sum.elim_inl, Option.elim_none, ← h1, Bool.false_or, true_and]; exact h2
              · simp only [Sum.elim_inl, Option.elim_none, evalSym, id, ← h1, Bool.true_or, and_self]
            | inr k1 =>
              rw [hs1] at h1
              simp only [evalSym, Sum.elim_inr] at h1
              cases hs2 : st.getD i2 (Sum.inl false) with
              | inl b2 =>
                rw [hs2] at h2
                simp only [evalSym, Sum.elim_inl, id] at h2
                cases b2
                · simp only [Sum.elim_inr, Sum.elim_inl, Option.elim_none, evalSym, ← h2, Bool.or_false, true_and]; exact h1
                · simp only [Sum.elim_inr, Sum.elim_inl, Option.elim_none, evalSym, id, ← h2, Bool.or_true, and_self]
              | inr k2 =>
                rw [hs2] at h2
                simp only [evalSym, Sum.elim_inr] at h2
                simp only [Sum.elim_inr, Option.elim_some]
                refine ⟨⟨Or.inr (Or.inl rfl), by simp⟩, ?_⟩
                simp only [evalSym, Sum.elim_inr, step, ← hlenN, getD_snoc_end,
                  List.map_cons, List.map_nil, eval_or, List.any_cons, List.any_nil, id, Bool.or_false]
                rw [h1, h2]
          | cons i3 t3 => rw [hg] at hlen; simp at hlen
    · change g.op = .not at hop
      cases hg : g.inputs with
      | nil =>
        simp only [elimGate, hop, hg, List.map_nil, eval_not, List.headD_nil, Option.elim_none,
          evalSym, Sum.elim_inl]
        exact ⟨trivial, rfl⟩
      | cons i1 t1 =>
        have h1 := hval i1
        dsimp only [elimGate]
        rw [hop, hg]
        simp only [List.map_cons, eval_not, List.headD_cons]
        cases hs1 : st.getD i1 (Sum.inl false) with
        | inl b1 =>
          rw [hs1] at h1
          simp only [evalSym, Sum.elim_inl, id] at h1
          simp only [Sum.elim_inl, Option.elim_none, evalSym, id, ← h1, and_self]
        | inr k1 =>
          rw [hs1] at h1
          simp only [evalSym, Sum.elim_inr] at h1
          simp only [Sum.elim_inr, Option.elim_some]
          refine ⟨⟨Or.inr (Or.inr rfl), by simp⟩, ?_⟩
          simp only [evalSym, Sum.elim_inr, step, ← hlenN, getD_snoc_end,
            List.map_cons, eval_not, List.headD_cons]
          rw [h1]
  let elimStep : (List (Bool ⊕ ℕ) × List Gate) → Gate → (List (Bool ⊕ ℕ) × List Gate) := fun acc g =>
    let r := elimGate acc.1 (9 + acc.2.length) g
    (acc.1 ++ [r.1], Option.elim r.2 acc.2 (fun g' => acc.2 ++ [g']))
  have elimRun_ok : ∀ (z : ℕ) (gs : List Gate) (st0 : List (Bool ⊕ ℕ)) (acc0 : List Gate),
      z < st0.length → st0.getD z (Sum.inl false) = Sum.inl false →
      (∀ g ∈ gs, g.op ∈ ({.and, .or, .not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      (∀ g ∈ acc0, g.op ∈ ({.and, .or, .not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      (∀ s ∈ st0, Sum.elim (fun _ => True) (fun k => k < 9 + acc0.length) s) →
      let res := gs.foldl elimStep (st0, acc0)
      (∃ sfx, res.1 = st0 ++ sfx ∧ sfx.length = gs.length) ∧
      res.2.length + (gs.filter (reads z)).length ≤ acc0.length + gs.length ∧
      (∀ g ∈ res.2, g.op ∈ ({.and, .or, .not} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
      (∀ (wsN0 wsO0 : List Bool), wsN0.length = 9 → wsO0.length = st0.length →
        (∀ i < st0.length, evalSym (st0.getD i (Sum.inl false)) (acc0.foldl step wsN0) = wsO0.getD i false) →
        ∀ i < res.1.length, evalSym (res.1.getD i (Sum.inl false)) (res.2.foldl step wsN0) =
          (gs.foldl step wsO0).getD i false) := by
    intro z gs
    induction gs with
    | nil =>
      intro st0 acc0 _ _ _ hacc0 _
      refine ⟨⟨[], by simp, rfl⟩, by simp, hacc0, ?_⟩
      intro wsN0 wsO0 _ _ hagree i hi
      exact hagree i hi
    | cons g rest ih =>
      intro st0 acc0 hz_lt hz_eq hgs hacc0 hst0
      have hg_ok := hgs g List.mem_cons_self
      have hrest_ok : ∀ g' ∈ rest, g'.op ∈ ({.and, .or, .not} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
        fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')
      let r := elimGate st0 (9 + acc0.length) g
      let st1 := st0 ++ [r.1]
      let acc1 := Option.elim r.2 acc0 (fun g' => acc0 ++ [g'])
      have hz_lt1 : z < st1.length := by simp only [st1, List.length_append, List.length_singleton]; omega
      have hz_eq1 : st1.getD z (Sum.inl false) = Sum.inl false := by
        dsimp only [st1]
        rw [List.getD_append _ _ _ _ hz_lt]
        exact hz_eq
      have hacc1_len : acc1.length + (if reads z g then 1 else 0) ≤ acc0.length + 1 := by
        cases hr : reads z g with
        | false =>
          dsimp only [acc1]
          cases r.2 <;> simp
        | true =>
          have hnone : r.2 = none := elimGate_kills st0 (9 + acc0.length) z g hg_ok hz_eq hr
          dsimp only [acc1]
          rw [hnone]
          simp
      have hacc1_ok : ∀ g' ∈ acc1, g'.op ∈ ({.and, .or, .not} : Set GateOp) ∧ g'.inputs.length ≤ 2 := by
        dsimp only [acc1]
        cases hr2 : r.2 with
        | none => exact hacc0
        | some g' =>
          have hdummy := elimGate_ok st0 (9 + acc0.length) g hg_ok
            (List.replicate (9 + acc0.length) false)
            (List.ofFn (fun i : Fin st0.length => evalSym (st0.getD i.val (Sum.inl false)) (List.replicate (9 + acc0.length) false)))
            (by simp)
            (fun i hi => by symm; rw [List.getD_eq_getElem _ _ (by simp [hi]), List.getElem_ofFn])
            (by simp)
          have hg'_ok : g'.op ∈ ({.and, .or, .not} : Set GateOp) ∧ g'.inputs.length ≤ 2 := by
            have := hdummy.1
            change Option.elim r.2 True _ at this
            rw [hr2] at this
            exact this
          intro h hh
          simp only [Option.elim_some, List.mem_append, List.mem_singleton] at hh
          rcases hh with hh | rfl
          · exact hacc0 h hh
          · exact hg'_ok
      have hst1_bnd : ∀ s ∈ st1, Sum.elim (fun _ => True) (fun k => k < 9 + acc1.length) s := by
        intro s hs
        simp only [st1, List.mem_append, List.mem_singleton] at hs
        rcases hs with hs | rfl
        · have h := hst0 s hs
          cases s with
          | inl _ => trivial
          | inr k =>
            have hle : acc0.length ≤ acc1.length := by dsimp only [acc1]; cases r.2 <;> simp
            simp only [Sum.elim_inr] at h ⊢; omega
        · have hst_get : ∀ i, Sum.elim (fun _ => True) (fun k => k < 9 + acc0.length) (st0.getD i (Sum.inl false)) := by
            intro i
            by_cases hi : i < st0.length
            · rw [List.getD_eq_getElem _ _ hi]
              exact hst0 _ (List.getElem_mem hi)
            · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi)]; trivial
          have mono : ∀ s : Bool ⊕ ℕ, Sum.elim (fun _ => True) (fun k => k < 9 + acc0.length) s →
              Sum.elim (fun _ => True) (fun k => k < 9 + acc1.length) s := by
            intro s hs; cases s with
            | inl _ => trivial
            | inr k =>
              have hle : acc0.length ≤ acc1.length := by dsimp only [acc1]; cases r.2 <;> simp
              simp only [Sum.elim_inr] at hs ⊢; omega
          rcases hg_ok.1 with hop | hop | hop
          · cases hg : g.inputs with
            | nil => simp only [r, elimGate, hop, hg, List.map_nil, Sum.elim_inl]
            | cons i1 t1 => cases t1 with
              | nil =>
                simp only [r, elimGate, hop, hg, List.map_cons, List.map_nil]
                exact mono _ (hst_get i1)
              | cons i2 t2 =>
                have h1 := hst_get i1
                have h2 := hst_get i2
                dsimp only [r, acc1, elimGate]
                rw [hop, hg]
                simp only [List.map_cons]
                cases hs1 : st0.getD i1 (Sum.inl false) with
                | inl b1 =>
                  cases b1
                  · simp only [Sum.elim_inl]
                  · simp only [Sum.elim_inl, Option.elim_none]; exact h2
                | inr k1 =>
                  cases hs2 : st0.getD i2 (Sum.inl false) with
                  | inl b2 =>
                    cases b2
                    · simp only [Sum.elim_inr, Sum.elim_inl]
                    · simp only [Sum.elim_inr, Sum.elim_inl, Option.elim_none]; rw [hs1] at h1; exact h1
                  | inr k2 =>
                    simp only [Sum.elim_inr, Option.elim_some, List.length_append, List.length_singleton]
                    omega
          · cases hg : g.inputs with
            | nil => simp only [r, elimGate, hop, hg, List.map_nil, Sum.elim_inl]
            | cons i1 t1 => cases t1 with
              | nil =>
                simp only [r, elimGate, hop, hg, List.map_cons, List.map_nil]
                exact mono _ (hst_get i1)
              | cons i2 t2 =>
                have h1 := hst_get i1
                have h2 := hst_get i2
                dsimp only [r, acc1, elimGate]
                rw [hop, hg]
                simp only [List.map_cons]
                cases hs1 : st0.getD i1 (Sum.inl false) with
                | inl b1 =>
                  cases b1
                  · simp only [Sum.elim_inl, Option.elim_none]; exact h2
                  · simp only [Sum.elim_inl]
                | inr k1 =>
                  cases hs2 : st0.getD i2 (Sum.inl false) with
                  | inl b2 =>
                    cases b2
                    · simp only [Sum.elim_inr, Sum.elim_inl, Option.elim_none]; rw [hs1] at h1; exact h1
                    · simp only [Sum.elim_inr, Sum.elim_inl]
                  | inr k2 =>
                    simp only [Sum.elim_inr, Option.elim_some, List.length_append, List.length_singleton]
                    omega
          · change g.op = .not at hop
            cases hg : g.inputs with
            | nil => simp only [r, elimGate, hop, hg, List.map_nil, Sum.elim_inl]
            | cons i1 t1 =>
              dsimp only [r, acc1, elimGate]
              rw [hop, hg]
              simp only [List.map_cons]
              cases hs1 : st0.getD i1 (Sum.inl false) with
              | inl b1 => simp only [Sum.elim_inl]
              | inr k1 =>
                simp only [Sum.elim_inr, Option.elim_some, List.length_append, List.length_singleton]
                omega
      obtain ⟨⟨sfx, hsfx, hsfx_len⟩, hlen2, hok2, hsem2⟩ := ih st1 acc1 hz_lt1 hz_eq1 hrest_ok hacc1_ok hst1_bnd
      refine ⟨⟨r.1 :: sfx, by simpa [elimStep, st1, acc1, r] using hsfx, by simp [hsfx_len]⟩, ?_, hok2, ?_⟩
      · have hlen2' : (rest.foldl elimStep (st1, acc1)).2.length + (rest.filter (reads z)).length ≤ acc1.length + rest.length := hlen2
        change (rest.foldl elimStep (st1, acc1)).2.length + ((g :: rest).filter (reads z)).length ≤ acc0.length + (g :: rest).length
        cases hr : reads z g <;>
          simp only [List.filter_cons, hr, ↓reduceIte, Bool.false_eq_true, List.length_cons] at hacc1_len ⊢ <;>
          omega
      · intro wsN0 wsO0 hlenN0 hlenO0 hagree0 i hi
        have hlen_acc0 : (acc0.foldl step wsN0).length = 9 + acc0.length := by rw [lengthRun, hlenN0]
        have hstep_sem := (elimGate_ok st0 (9 + acc0.length) g hg_ok (acc0.foldl step wsN0) wsO0 hlen_acc0 hagree0 hlenO0).2
        have hfold_acc1 : acc1.foldl step wsN0 = Option.elim r.2 (acc0.foldl step wsN0) (fun g' => step (acc0.foldl step wsN0) g') := by
          dsimp only [acc1]
          cases r.2 with
          | none => rfl
          | some g' => simp only [Option.elim_some, List.foldl_append, List.foldl_cons, List.foldl_nil]
        have hagree1 : ∀ j < st1.length, evalSym (st1.getD j (Sum.inl false)) (acc1.foldl step wsN0) = (step wsO0 g).getD j false := by
          intro j hj
          simp only [st1, List.length_append, List.length_singleton] at hj
          by_cases hj0 : j < st0.length
          · rw [List.getD_append _ _ _ _ hj0, List.getD_append _ _ _ _ (by omega : j < wsO0.length)]
            have hs_bnd := hst0 (st0.getD j (Sum.inl false)) (by rw [List.getD_eq_getElem _ _ hj0]; exact List.getElem_mem hj0)
            rw [hfold_acc1]
            have hpres : evalSym (st0.getD j (Sum.inl false))
                (Option.elim r.2 (acc0.foldl step wsN0) (fun g' => step (acc0.foldl step wsN0) g')) =
                evalSym (st0.getD j (Sum.inl false)) (acc0.foldl step wsN0) := by
              cases r.2 with
              | none => rfl
              | some g' =>
                simp only [Option.elim_some]
                cases hsj : st0.getD j (Sum.inl false) with
                | inl _ => rfl
                | inr k =>
                  rw [hsj] at hs_bnd
                  simp only [evalSym, Sum.elim_inr]
                  exact List.getD_append _ _ _ _ (by rw [hlen_acc0]; exact hs_bnd)
            rw [hpres]
            exact hagree0 j hj0
          · have hjeq : j = st0.length := by omega
            subst hjeq
            rw [getD_snoc_end, hfold_acc1]
            dsimp only [step]
            rw [← hlenO0, getD_snoc_end]
            exact hstep_sem
        exact hsem2 wsN0 (step wsO0 g) hlenN0 (by simp [step, st1, hlenO0]) hagree1 i hi
  have kill_of_three : ∀ (z : ℕ) (st0 : List (Bool ⊕ ℕ)) (lift : (Fin 9 → Bool) → Fin 10 → Bool),
      st0.length = 11 → z < 11 → st0.getD z (Sum.inl false) = Sum.inl false →
      (∀ s ∈ st0, Sum.elim (fun _ => true) (fun k => decide (k < 9)) s = true) →
      (∀ y : Fin 9 → Bool, ∀ i < 11, evalSym (st0.getD i (Sum.inl false)) (List.ofFn y) = (seed (lift y)).getD i false) →
      (∀ y : Fin 9 → Bool, x7 (lift y) = p9 y) →
      3 ≤ (x2.gates.filter (reads z)).length →
      False := by
    intro z st0 lift hst0_len hz_lt hz_eq hst0_bnd hst0_sem hlift_p9 h3
    let gsFull : List Gate := x2.gates ++ [⟨.and, [u, 27]⟩]
    have hgsFull_ok : ∀ g ∈ gsFull, g.op ∈ ({.and, .or, .not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
      intro g hg
      simp only [gsFull, List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | rfl
      · exact hfan g hg
      · exact ⟨Or.inl rfl, by simp⟩
    have hst0_prop : ∀ s ∈ st0, Sum.elim (fun _ => True) (fun k => k < 9 + ([] : List Gate).length) s := by
      intro s hs
      have hb := hst0_bnd s hs
      cases s with
      | inl _ => trivial
      | inr k => simpa using of_decide_eq_true hb
    let res := gsFull.foldl elimStep (st0, [])
    obtain ⟨⟨sfx, hsfx, hsfx_len⟩, hlen_res, hok_res, hsem_res⟩ :=
      elimRun_ok z gsFull st0 [] (by omega) hz_eq hgsFull_ok
        (fun _ h => (List.not_mem_nil h).elim) hst0_prop
    have hfilt_ge : 3 ≤ (gsFull.filter (reads z)).length := by
      simp only [gsFull, List.filter_append, List.length_append]
      omega
    have hgs_len : gsFull.length = 18 := by
      change (x2.gates ++ [_]).length = 18
      change x2.gates.length = 17 at size17
      simp [size17]
    have hres_le15 : res.2.length ≤ 15 := by
      change res.2.length + (gsFull.filter (reads z)).length ≤ ([] : List Gate).length + gsFull.length at hlen_res
      simp only [List.length_nil, zero_add, hgs_len] at hlen_res
      omega
    have hout_lt : 28 < res.1.length := by
      rw [hsfx, List.length_append, hst0_len, hsfx_len, hgs_len]
      omega
    have hval_out : ∀ y : Fin 9 → Bool, evalSym (res.1.getD 28 (Sum.inl false)) (res.2.foldl step (List.ofFn y)) = p9 y := by
      intro y
      have hsem := hsem_res (List.ofFn y) (seed (lift y)) (by simp) (by rw [seed_len, hst0_len])
        (fun i hi => by rw [hst0_len] at hi; exact hst0_sem y i hi) 28 hout_lt
      rw [hsem]
      have hfold_full : gsFull.foldl step (seed (lift y)) = step (x2.gates.foldl step (seed (lift y))) ⟨.and, [u, 27]⟩ := by
        simp [gsFull, List.foldl_append]
      rw [hfold_full]
      have hlen_x2 : (x2.gates.foldl step (seed (lift y))).length = 28 := by
        have hl17 : x2.gates.length = 17 := size17
        rw [lengthRun, seed_len]
        omega
      dsimp only [step]
      rw [← hlen_x2, getD_snoc_end]
      simp only [List.map_cons, List.map_nil, eval_and, List.all_cons, List.all_nil, id, Bool.and_true]
      exact (eval27 (lift y)).trans (hlift_p9 y)
    cases hout_sym : res.1.getD 28 (Sum.inl false) with
    | inl b =>
      have h0 : p9 (fun _ => false) = false := rfl
      have h1 : p9 (fun _ => true) = true := rfl
      have e0 := hval_out (fun _ => false)
      have e1 := hval_out (fun _ => true)
      rw [hout_sym] at e0 e1
      simp only [evalSym, Sum.elim_inl, id] at e0 e1
      rw [← e0] at h0
      rw [← e1] at h1
      exact Bool.noConfusion (h0.symm.trans h1)
    | inr k =>
      apply h670
      refine ⟨⟨res.2, k⟩, hok_res, hres_le15, ?_⟩
      intro y
      have hy := hval_out y
      rw [hout_sym] at hy
      exact hy
  by_cases c0 : (x2.gates.filter (reads 0)).length ≤ 2
  · by_cases cp : (x2.gates.filter (reads (if x1 = true then 1 else 2))).length ≤ 2
    · exact hLow x1 x2 u hfan size17 hu hu27 c0 cp hu_not_27 h27_not_u
        (fun x => (eval27 x).trans (pc10 x).symm)
    · cases hx1 : x1
      · rw [hx1] at cp
        simp only [Bool.false_eq_true, ↓reduceIte] at cp
        let st2 : List (Bool ⊕ ℕ) :=
          [Sum.inr 5, Sum.inr 7, Sum.inl false, Sum.inr 6, Sum.inr 8, Sum.inr 0, Sum.inr 2, Sum.inr 4, Sum.inr 1, Sum.inr 3, Sum.inr 5]
        let lift2 : (Fin 9 → Bool) → Fin 10 → Bool :=
          fun y j => [y 5, y 7, false, y 6, y 8, y 0, y 2, y 4, y 1, y 3].getD j.val false
        refine kill_of_three 2 st2 lift2 rfl (by decide) rfl (by decide) ?_ ?_ (by omega)
        · intro y i hi
          have hfin : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 := by omega
          rcases hfin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            simp [st2, lift2, seed, hx1, evalSym, List.ofFn_succ]
        · intro y
          have h : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 : Bool,
              x7 (fun j : Fin 10 => [a5, a7, false, a6, a8, a0, a2, a4, a1, a3].getD j.val false) =
              ((a0 && a1) || (a1 && a2) || (a2 && a3) || (a3 && a4) || (a4 && a0) ||
               (a0 && a5) || (a1 && a6) || (a2 && a7) || (a3 && a8) || (a5 && a7) ||
               (a6 && a8) || (a8 && a5)) := by decide
          exact h (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8)
      · rw [hx1] at cp
        simp only [↓reduceIte] at cp
        let st1 : List (Bool ⊕ ℕ) :=
          [Sum.inr 7, Sum.inl false, Sum.inr 6, Sum.inr 8, Sum.inr 5, Sum.inr 2, Sum.inr 4, Sum.inr 1, Sum.inr 3, Sum.inr 0, Sum.inr 7]
        let lift1 : (Fin 9 → Bool) → Fin 10 → Bool :=
          fun y j => [y 7, false, y 6, y 8, y 5, y 2, y 4, y 1, y 3, y 0].getD j.val false
        refine kill_of_three 1 st1 lift1 rfl (by decide) rfl (by decide) ?_ ?_ (by omega)
        · intro y i hi
          have hfin : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 := by omega
          rcases hfin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            simp [st1, lift1, seed, hx1, evalSym, List.ofFn_succ]
        · intro y
          have h : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 : Bool,
              x7 (fun j : Fin 10 => [a7, false, a6, a8, a5, a2, a4, a1, a3, a0].getD j.val false) =
              ((a0 && a1) || (a1 && a2) || (a2 && a3) || (a3 && a4) || (a4 && a0) ||
               (a0 && a5) || (a1 && a6) || (a2 && a7) || (a3 && a8) || (a5 && a7) ||
               (a6 && a8) || (a8 && a5)) := by decide
          exact h (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8)
  · let st0 : List (Bool ⊕ ℕ) :=
      [Sum.inl false, Sum.inr 6, Sum.inr 8, Sum.inr 5, Sum.inr 7, Sum.inr 4, Sum.inr 1, Sum.inr 3, Sum.inr 0, Sum.inr 2,
       if x1 = true then Sum.inr 6 else Sum.inr 8]
    let lift0 : (Fin 9 → Bool) → Fin 10 → Bool :=
      fun y j => [false, y 6, y 8, y 5, y 7, y 4, y 1, y 3, y 0, y 2].getD j.val false
    refine kill_of_three 0 st0 lift0 rfl (by decide) rfl (by cases x1 <;> decide) ?_ ?_ (by omega)
    · intro y i hi
      have hfin : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 := by omega
      cases hx1 : x1 <;>
        (rcases hfin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [st0, lift0, seed, hx1, evalSym, List.ofFn_succ])
    · intro y
      have h : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 : Bool,
          x7 (fun j : Fin 10 => [false, a6, a8, a5, a7, a4, a1, a3, a0, a2].getD j.val false) =
          ((a0 && a1) || (a1 && a2) || (a2 && a3) || (a3 && a4) || (a4 && a0) ||
           (a0 && a5) || (a1 && a6) || (a2 && a7) || (a3 && a8) || (a5 && a7) ||
           (a6 && a8) || (a8 && a5)) := by decide
      exact h (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8)
