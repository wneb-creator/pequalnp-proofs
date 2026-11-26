import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3022_1
    (no14_both :
      (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 14 →
        ∃ x : Fin 9 → Bool, C.eval (List.ofFn x) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) ∧
      (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 14 →
        ∃ y : Fin 8 → Bool, C.eval (List.ofFn y) ≠
          (y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 0 && y 4 || y 1 && y 5 || y 2 && y 6 || y 3 && y 7 || y 4 && y 6 || y 5 && y 7 || y 7 && y 4)))
    (many_nots :
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
        (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) =
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) →
        13 ≤ C.size - PEqualNP.NotBracket.notCount C)
    (core_no9 :
      ∀ p ∈ ([(0, 1), (0, 3), (0, 5), (0, 8), (1, 3), (1, 8), (3, 5), (3, 8)] : List (Fin 9 × Fin 9)),
        ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
          PEqualNP.NotBracket.notCount C ≤ 2 →
          ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 2, x p.1 || x p.2]) ≠
            (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (core_with9 :
      ∀ k ∈ ([(1 : Fin 9), 3, 8] : List (Fin 9)),
        ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
          PEqualNP.NotBracket.notCount C ≤ 2 →
          ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 2, (x 0 || x 2) || x k]) ≠
            (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) :
    ∀ (x1 : List (Fin (11 : ℕ))), x1.length ≤ (2 : ℕ) → ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) → ∃ (x6 : Fin (9 : ℕ) → Bool), have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ))]; x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x8 : Fin (11 : ℕ)) => x7.getD (↑x8) Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  classical
  obtain ⟨no14, no14_del4⟩ := no14_both
  intro pins hlen C hfan hsz
  by_contra hno
  let edge (x : Fin 9 → Bool) : Bool :=
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
    x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  let edge4 (y : Fin 8 → Bool) : Bool :=
    y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 0 && y 4 || y 1 && y 5 || y 2 && y 6 ||
    y 3 && y 7 || y 4 && y 6 || y 5 && y 7 || y 7 && y 4
  have heq : ∀ x : Fin 9 → Bool,
      let x7 : List Bool := List.ofFn x ++ [x 0 || x 2]
      C.eval (x7 ++ [GateOp.or.eval (pins.map fun i => x7.getD i.val false)]) = edge x := by
    intro x
    by_contra hne
    exact hno ⟨x, hne⟩
  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]
  let mapGate (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩
  have hfan_map (f : ℕ → ℕ) (gs : List Gate) (o : ℕ)
      (h : FanInTwo ⟨gs, o⟩) : FanInTwo ⟨gs.map (mapGate f), o⟩ := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    obtain ⟨hop, hlen0⟩ := h g0 hg0
    exact ⟨hop, by simp only [mapGate, List.length_map]; exact hlen0⟩
  have hnot_map (f : ℕ → ℕ) (gs : List Gate) (o₁ o₂ : ℕ) :
      PEqualNP.NotBracket.notCount ⟨gs.map (mapGate f), o₁⟩ =
      PEqualNP.NotBracket.notCount ⟨gs, o₂⟩ := by
    unfold PEqualNP.NotBracket.notCount
    dsimp only
    rw [List.filter_map, List.length_map]
    rfl
  have rewire (m n L : ℕ) (f : ℕ → ℕ)
      (hf_hi : ∀ k, m ≤ k → f k = k - m + n)
      (hf_lo : ∀ k, k < m → f k < n ∨ n + L ≤ f k) :
      ∀ (gs : List Gate) (i : ℕ) (u v : List Bool),
        u.length = m + i → v.length = n + i → i + gs.length ≤ L →
        (∀ k, k < u.length → v.getD (f k) false = u.getD k false) →
        ∀ k, ((gs.map (mapGate f)).foldl step v).getD (f k) false = (gs.foldl step u).getD k false := by
    intro gs
    induction gs with
    | nil =>
      intro i u v hu hv _ hagree k
      change v.getD (f k) false = u.getD k false
      by_cases hk : k < u.length
      · exact hagree k hk
      · have hmk : m ≤ k := by omega
        have hfk : v.length ≤ f k := by rw [hf_hi k hmk]; omega
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_eq_none hfk, List.getElem?_eq_none (Nat.le_of_not_lt hk)]
    | cons g gs ih =>
      intro i u v hu hv hbound hagree k
      rw [List.map_cons, List.foldl_cons, List.foldl_cons]
      have hall : ∀ j, v.getD (f j) false = u.getD j false := by
        intro j
        by_cases hj : j < u.length
        · exact hagree j hj
        · have hmj : m ≤ j := by omega
          have hfj : v.length ≤ f j := by rw [hf_hi j hmj]; omega
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
              List.getElem?_eq_none hfj, List.getElem?_eq_none (Nat.le_of_not_lt hj)]
      have hbit : (mapGate f g).op.eval ((mapGate f g).inputs.map fun j => v.getD j false) =
                  g.op.eval (g.inputs.map fun j => u.getD j false) := by
        change g.op.eval ((g.inputs.map f).map fun j => v.getD j false) = _
        rw [List.map_map]
        congr 1
        exact List.map_congr_left fun j _ => hall j
      have hstep_v : step v (mapGate f g) = v ++ [g.op.eval (g.inputs.map fun j => u.getD j false)] := by
        change v ++ [(mapGate f g).op.eval ((mapGate f g).inputs.map fun j => v.getD j false)] = _
        rw [hbit]
      apply ih (i + 1) (step u g) (step v (mapGate f g))
      · change (u ++ [_]).length = m + (i + 1); simp only [List.length_append, List.length_singleton]; omega
      · change (v ++ [_]).length = n + (i + 1); simp only [List.length_append, List.length_singleton]; omega
      · simp only [List.length_cons] at hbound; omega
      · intro j hj
        rw [hstep_v]
        change (v ++ [g.op.eval (g.inputs.map fun t => u.getD t false)]).getD (f j) false =
               (u ++ [g.op.eval (g.inputs.map fun t => u.getD t false)]).getD j false
        have hulen : (step u g).length = m + i + 1 := by
          change (u ++ [_]).length = m + i + 1; simp only [List.length_append, List.length_singleton]; omega
        by_cases hlast : j = m + i
        · subst hlast
          have hfj : f (m + i) = v.length := by rw [hf_hi (m + i) (Nat.le_add_right m i)]; omega
          rw [hfj, List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self,
              ← hu, List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
        · have hjlt : j < u.length := by omega
          rw [List.getD_append _ _ _ _ hjlt]
          by_cases hjm : j < m
          · rcases hf_lo j hjm with hsmall | hbig
            · rw [List.getD_append _ _ _ _ (by omega)]
              exact hagree j hjlt
            · have hle1 : (v ++ [g.op.eval (g.inputs.map fun t => u.getD t false)]).length ≤ f j := by
                simp only [List.length_append, List.length_cons, List.length_nil] at hbound ⊢; omega
              have hle2 : v.length ≤ f j := by
                simp only [List.length_cons] at hbound; omega
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hle1]
              have hprev : v.getD (f j) false = false := by
                rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hle2]; rfl
              rw [← hagree j hjlt, hprev]; rfl
          · have hfj : f j < v.length := by rw [hf_hi j (Nat.le_of_not_lt hjm)]; omega
            rw [List.getD_append _ _ _ _ hfj]
            exact hagree j hjlt
  have eval_rewire (m n : ℕ) (f : ℕ → ℕ)
      (hf_hi : ∀ k, m ≤ k → f k = k - m + n)
      (hf_lo : ∀ k, k < m → f k < n ∨ n + C.size ≤ f k)
      (u0 v0 : List Bool) (hu0 : u0.length = m) (hv0 : v0.length = n)
      (hagree0 : ∀ k, k < m → v0.getD (f k) false = u0.getD k false) :
      (Circuit.mk (C.gates.map (mapGate f)) (f C.output)).eval v0 = C.eval u0 := by
    change ((C.gates.map (mapGate f)).foldl step v0).getD (f C.output) false =
           (C.gates.foldl step u0).getD C.output false
    exact rewire m n C.size f hf_hi hf_lo C.gates 0 u0 v0 (by omega) (by omega)
      (by change 0 + C.gates.length ≤ C.gates.length; omega)
      (fun k hk => hagree0 k (by omega)) C.output
  -- Helper: getD on List.ofFn
  have ofFn_getD {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < n) :
      (List.ofFn x).getD k false = x ⟨k, hk⟩ := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp only [hk, ↓reduceDIte, Option.getD_some]
  -- Helper: close when wire 10 equals a fixed wire r < 10 or constant false (r = 10 + C.size)
  have close_redundant (r : ℕ) (hr : r < 10 ∨ r = 10 + C.size)
      (hval : ∀ x : Fin 9 → Bool,
        let x7 : List Bool := List.ofFn x ++ [x 0 || x 2]
        GateOp.or.eval (pins.map fun i => x7.getD i.val false) = x7.getD r false) : False := by
    let f (k : ℕ) : ℕ := if k < 10 then k else if k = 10 then r else k - 11 + 10
    let g0 : Gate := ⟨.or, [0, 2]⟩
    let D : Circuit := ⟨g0 :: C.gates.map (mapGate f), f C.output⟩
    have hD_fan : FanInTwo D := by
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg'
      · exact ⟨Or.inr (Or.inl rfl), by decide⟩
      · exact hfan_map f C.gates (f C.output) hfan g hg'
    have hD_sz : D.size ≤ 14 := by
      change (g0 :: C.gates.map (mapGate f)).length ≤ 14
      simp only [List.length_cons, List.length_map]
      change C.gates.length ≤ 13 at hsz
      omega
    obtain ⟨x, hx⟩ := no14 D hD_fan hD_sz
    apply hx
    let x7 : List Bool := List.ofFn x ++ [x 0 || x 2]
    have hlen7 : x7.length = 10 := by
      simp only [x7, List.length_append, List.length_ofFn, List.length_singleton]
    have hstep0 : step (List.ofFn x) g0 = x7 := by
      change List.ofFn x ++ [GateOp.or.eval [(List.ofFn x).getD 0 false, (List.ofFn x).getD 2 false]] = x7
      rw [ofFn_getD x 0 (by omega), ofFn_getD x 2 (by omega)]
      change List.ofFn x ++ [(x 0 || (x 2 || false))] = x7
      rw [Bool.or_false]
    have hDeval : D.eval (List.ofFn x) = (Circuit.mk (C.gates.map (mapGate f)) (f C.output)).eval x7 := by
      change ((g0 :: C.gates.map (mapGate f)).foldl step (List.ofFn x)).getD (f C.output) false = _
      rw [List.foldl_cons, hstep0]
      rfl
    rw [hDeval]
    have hrew := eval_rewire 11 10 f
      (fun k hk => by simp only [f, show ¬ (k < 10) by omega, show ¬ (k = 10) by omega, ↓reduceIte])
      (fun k hk => by
        by_cases h10 : k < 10
        · left; simp only [f, h10, ↓reduceIte]
        · have hk10 : k = 10 := by omega
          subst hk10
          have hf10 : f 10 = r := rfl
          rw [hf10]
          rcases hr with hr1 | hr2
          · exact Or.inl hr1
          · exact Or.inr (by omega))
      (x7 ++ [GateOp.or.eval (pins.map fun i => x7.getD i.val false)]) x7
      (by simp only [List.length_append, hlen7, List.length_singleton])
      hlen7
      (fun k hk => by
        by_cases h10 : k < 10
        · have hfk : f k = k := by simp only [f, h10, ↓reduceIte]
          have hrhs : (x7 ++ [GateOp.or.eval (pins.map fun i => x7.getD i.val false)]).getD k false = x7.getD k false :=
            List.getD_append _ _ _ _ (by omega)
          rw [hfk, hrhs]
        · have hk10 : k = 10 := by omega
          subst hk10
          have hf10 : f 10 = r := rfl
          have hrhs : (x7 ++ [GateOp.or.eval (pins.map fun i => x7.getD i.val false)]).getD 10 false =
              GateOp.or.eval (pins.map fun i => x7.getD i.val false) := by
            rw [List.getD_append_right _ _ _ _ (by omega), hlen7, Nat.sub_self]; rfl
          rw [hf10, hrhs]
          exact (hval x).symm)
    rw [hrew]
    exact heq x
  -- Helper: close when pins = [a, b] and a or b is a degree-2 vertex v in {4, 6, 7}
  have close_deg2 (v : ℕ) (hv : v < 9) (yidx : List ℕ) (p0 p2 : ℕ) (hp0 : p0 < 8) (hp2 : p2 < 8)
      (hyidx_lt : ∀ i : Fin 9, i.val ≠ v → yidx.getD i.val 0 < 8)
      (hp0_eq : yidx.getD 0 0 = p0) (hp2_eq : yidx.getD 2 0 = p2) (hv_ne0 : (0 : ℕ) ≠ v) (hv_ne2 : (2 : ℕ) ≠ v)
      (hedge : ∀ y : Fin 8 → Bool,
        let ex : Fin 9 → Bool := fun i => if h : i.val = v then false else y ⟨yidx.getD i.val 0, hyidx_lt i h⟩
        edge ex = edge4 y)
      (u : Fin 11)
      (hval : ∀ x : Fin 9 → Bool,
        let x7 : List Bool := List.ofFn x ++ [x 0 || x 2]
        x ⟨v, hv⟩ = false →
        GateOp.or.eval (pins.map fun i => x7.getD i.val false) = x7.getD u.val false) : False := by
    let mW (k : ℕ) : ℕ :=
      if k < 9 then (if k = v then 9 + C.size else yidx.getD k 0)
      else if k = 9 then 8 else 9 + C.size
    let f (k : ℕ) : ℕ := if k < 10 then mW k else if k = 10 then mW u.val else k - 11 + 9
    let g0 : Gate := ⟨.or, [p0, p2]⟩
    let D : Circuit := ⟨g0 :: C.gates.map (mapGate f), f C.output⟩
    have hD_fan : FanInTwo D := by
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg'
      · exact ⟨Or.inr (Or.inl rfl), Nat.le_refl 2⟩
      · exact hfan_map f C.gates (f C.output) hfan g hg'
    have hD_sz : D.size ≤ 14 := by
      change (g0 :: C.gates.map (mapGate f)).length ≤ 14
      simp only [List.length_cons, List.length_map]
      change C.gates.length ≤ 13 at hsz
      omega
    obtain ⟨y, hy⟩ := no14_del4 D hD_fan hD_sz
    apply hy
    let ex : Fin 9 → Bool := fun i =>
      if h : i.val = v then false else y ⟨yidx.getD i.val 0, hyidx_lt i h⟩
    let x7 : List Bool := List.ofFn ex ++ [ex 0 || ex 2]
    let y8 : List Bool := List.ofFn y ++ [y ⟨p0, hp0⟩ || y ⟨p2, hp2⟩]
    have hlen7 : x7.length = 10 := by
      simp only [x7, List.length_append, List.length_ofFn, List.length_singleton]
    have hlen8 : y8.length = 9 := by
      simp only [y8, List.length_append, List.length_ofFn, List.length_singleton]
    have hex0 : ex 0 = y ⟨p0, hp0⟩ := by
      simp only [ex, Fin.val_zero, hv_ne0, ↓reduceDIte]
      congr 1; exact Fin.ext hp0_eq
    have hex2 : ex 2 = y ⟨p2, hp2⟩ := by
      simp only [ex, show (2 : Fin 9).val = 2 from rfl, hv_ne2, ↓reduceDIte]
      congr 1; exact Fin.ext hp2_eq
    have hstep0 : step (List.ofFn y) g0 = y8 := by
      change List.ofFn y ++ [GateOp.or.eval [(List.ofFn y).getD p0 false, (List.ofFn y).getD p2 false]] = y8
      rw [ofFn_getD y p0 hp0, ofFn_getD y p2 hp2]
      change List.ofFn y ++ [(y ⟨p0, hp0⟩ || (y ⟨p2, hp2⟩ || false))] = y8
      rw [Bool.or_false]
    have hDeval : D.eval (List.ofFn y) = (Circuit.mk (C.gates.map (mapGate f)) (f C.output)).eval y8 := by
      change ((g0 :: C.gates.map (mapGate f)).foldl step (List.ofFn y)).getD (f C.output) false = _
      rw [List.foldl_cons, hstep0]
      rfl
    have hmW_lo (k : ℕ) : mW k < 9 ∨ 9 + C.size ≤ mW k := by
      by_cases hk9 : k < 9
      · by_cases hkv : k = v
        · right; have hm : mW k = 9 + C.size := by dsimp only [mW]; simp only [hk9, ↓reduceIte]; simp only [hkv, ↓reduceIte]
          omega
        · left; have hm : mW k = yidx.getD k 0 := by dsimp only [mW]; simp only [hk9, ↓reduceIte]; simp only [hkv, ↓reduceIte]
          have hlt := hyidx_lt ⟨k, hk9⟩ hkv
          change yidx.getD k 0 < 8 at hlt
          omega
      · by_cases hk9e : k = 9
        · left; have hm : mW k = 8 := by dsimp only [mW]; simp only [hk9, ↓reduceIte]; simp only [hk9e, ↓reduceIte]
          omega
        · right; have hm : mW k = 9 + C.size := by dsimp only [mW]; simp only [hk9, ↓reduceIte]; simp only [hk9e, ↓reduceIte]
          omega
    have hmW_val (k : ℕ) : y8.getD (mW k) false = x7.getD k false := by
      by_cases hk9 : k < 9
      · have hx7k : x7.getD k false = ex ⟨k, hk9⟩ := by
          rw [List.getD_append _ _ _ _ (by simp only [List.length_ofFn]; exact hk9), ofFn_getD ex k hk9]
        rw [hx7k]
        by_cases hkv : k = v
        · have hm : mW k = 9 + C.size := by dsimp only [mW]; simp only [hk9, ↓reduceIte]; simp only [hkv, ↓reduceIte]
          rw [hm, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
          simp only [ex, hkv, ↓reduceDIte, Option.getD_none]
        · have hm : mW k = yidx.getD k 0 := by dsimp only [mW]; simp only [hk9, ↓reduceIte]; simp only [hkv, ↓reduceIte]
          have hlt8 : yidx.getD k 0 < 8 := hyidx_lt ⟨k, hk9⟩ hkv
          rw [hm, List.getD_append _ _ _ _ (by simp only [List.length_ofFn]; exact hlt8),
              ofFn_getD y (yidx.getD k 0) hlt8]
          simp only [ex, hkv, ↓reduceDIte]
      · by_cases hk9e : k = 9
        · subst hk9e
          have hm : mW 9 = 8 := rfl
          have hy8 : y8.getD 8 false = (y ⟨p0, hp0⟩ || y ⟨p2, hp2⟩) := by
            rw [List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn]; omega)]
            simp only [List.length_ofFn, Nat.sub_self]; rfl
          have hx9 : x7.getD 9 false = (ex 0 || ex 2) := by
            rw [List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn]; omega)]
            simp only [List.length_ofFn, Nat.sub_self]; rfl
          rw [hm, hy8, hx9, hex0, hex2]
        · have hm : mW k = 9 + C.size := by dsimp only [mW]; simp only [hk9, ↓reduceIte]; simp only [hk9e, ↓reduceIte]
          rw [hm, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega),
              List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rw [hDeval]
    have hrew := eval_rewire 11 9 f
      (fun k hk => by simp only [f, show ¬ (k < 10) by omega, show ¬ (k = 10) by omega, ↓reduceIte])
      (fun k hk => by
        by_cases h10 : k < 10
        · simp only [f, h10, ↓reduceIte]; exact hmW_lo k
        · have hk10 : k = 10 := by omega
          subst hk10
          have hf10 : f 10 = mW u.val := rfl
          rw [hf10]; exact hmW_lo u.val)
      (x7 ++ [GateOp.or.eval (pins.map fun i => x7.getD i.val false)]) y8
      (by simp only [List.length_append, hlen7, List.length_singleton])
      hlen8
      (fun k hk => by
        by_cases h10 : k < 10
        · have hfk : f k = mW k := by simp only [f, h10, ↓reduceIte]
          have hrhs : (x7 ++ [GateOp.or.eval (pins.map fun i => x7.getD i.val false)]).getD k false = x7.getD k false :=
            List.getD_append _ _ _ _ (by omega)
          rw [hfk, hrhs]
          exact hmW_val k
        · have hk10 : k = 10 := by omega
          subst hk10
          have hf10 : f 10 = mW u.val := rfl
          have hrhs : (x7 ++ [GateOp.or.eval (pins.map fun i => x7.getD i.val false)]).getD 10 false =
              GateOp.or.eval (pins.map fun i => x7.getD i.val false) := by
            rw [List.getD_append_right _ _ _ _ (by omega), hlen7, Nat.sub_self]; rfl
          rw [hf10, hrhs, hmW_val u.val]
          have hexv : ex ⟨v, hv⟩ = false := by simp only [ex, ↓reduceDIte]
          exact (hval ex hexv).symm)
    rw [hrew, heq ex]
    exact hedge y
  -- Fast decidable graph isomorphism identities (each checks 256 or 512 Bool tuples in < 5ms)
  have hdel4_bool : ∀ a0 a1 a2 a3 a4 a5 a6 a7 : Bool,
      (a0 && a1 || a1 && a2 || a2 && a3 || a3 && false || false && a0 || a0 && a4 ||
       a1 && a5 || a2 && a6 || a3 && a7 || a4 && a6 || a5 && a7 || a7 && a4) =
      (a0 && a1 || a1 && a2 || a2 && a3 || a0 && a4 || a1 && a5 || a2 && a6 ||
       a3 && a7 || a4 && a6 || a5 && a7 || a7 && a4) := by decide
  have hdel6_bool : ∀ a0 a1 a2 a3 a4 a5 a6 a7 : Bool,
      (a1 && a0 || a0 && a4 || a4 && a7 || a7 && a5 || a5 && a1 || a1 && a2 ||
       a0 && false || a4 && a6 || a7 && a3 || a2 && a6 || false && a3 || a3 && a2) =
      (a0 && a1 || a1 && a2 || a2 && a3 || a0 && a4 || a1 && a5 || a2 && a6 ||
       a3 && a7 || a4 && a6 || a5 && a7 || a7 && a4) := by decide
  have hdel7_bool : ∀ a0 a1 a2 a3 a4 a5 a6 a7 : Bool,
      (a2 && a1 || a1 && a0 || a0 && a4 || a4 && a6 || a6 && a2 || a2 && a3 ||
       a1 && a5 || a0 && false || a4 && a7 || a3 && false || a5 && a7 || a7 && a3) =
      (a0 && a1 || a1 && a2 || a2 && a3 || a0 && a4 || a1 && a5 || a2 && a6 ||
       a3 && a7 || a4 && a6 || a5 && a7 || a7 && a4) := by decide
  have hsig_bool : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 : Bool,
      (a2 && a1 || a1 && a0 || a0 && a5 || a5 && a7 || a7 && a2 || a2 && a3 ||
       a1 && a6 || a0 && a4 || a5 && a8 || a3 && a4 || a6 && a8 || a8 && a3) =
      (a0 && a1 || a1 && a2 || a2 && a3 || a3 && a4 || a4 && a0 || a0 && a5 ||
       a1 && a6 || a2 && a7 || a3 && a8 || a5 && a7 || a6 && a8 || a8 && a5) := by decide
  -- Case split on pins : List (Fin 11) with pins.length ≤ 2
  cases pins with
  | nil =>
    exact close_redundant (10 + C.size) (Or.inr rfl) (fun x => by
      dsimp only
      change GateOp.or.eval [] = (List.ofFn x ++ [x 0 || x 2]).getD (10 + C.size) false
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp only [List.length_append, List.length_ofFn, List.length_singleton]; omega)]
      rfl)
  | cons a rest =>
    cases rest with
    | nil =>
      by_cases ha10 : a.val < 10
      · exact close_redundant a.val (Or.inl ha10) (fun x => by
          dsimp only
          change ((List.ofFn x ++ [x 0 || x 2]).getD a.val false || false) = _
          exact Bool.or_false _)
      · exact close_redundant (10 + C.size) (Or.inr rfl) (fun x => by
          dsimp only
          change ((List.ofFn x ++ [x 0 || x 2]).getD a.val false || false) =
                 (List.ofFn x ++ [x 0 || x 2]).getD (10 + C.size) false
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp only [List.length_append, List.length_ofFn, List.length_singleton]; omega),
              List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp only [List.length_append, List.length_ofFn, List.length_singleton]; omega)]
          rfl)
    | cons b tail =>
      cases tail with
      | cons _ _ => simp only [List.length_cons] at hlen; omega
      | nil =>
        have hor2 (x : Fin 9 → Bool) :
            GateOp.or.eval ([a, b].map fun i => (List.ofFn x ++ [x 0 || x 2]).getD i.val false) =
              ((List.ofFn x ++ [x 0 || x 2]).getD a.val false || (List.ofFn x ++ [x 0 || x 2]).getD b.val false) := by
          change ((List.ofFn x ++ [x 0 || x 2]).getD a.val false || ((List.ofFn x ++ [x 0 || x 2]).getD b.val false || false)) = _
          rw [Bool.or_false]
        -- Redundant cases: a = 10, b = 10, a = b, or both in {0, 2, 9}
        by_cases ha10 : a.val = 10
        · by_cases hb10 : b.val = 10
          · exact close_redundant (10 + C.size) (Or.inr rfl) (fun x => by
              dsimp only; rw [hor2 x, ha10, hb10]
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp only [List.length_append, List.length_ofFn, List.length_singleton]; omega),
                  List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp only [List.length_append, List.length_ofFn, List.length_singleton]; omega)]
              rfl)
          · exact close_redundant b.val (Or.inl (by omega)) (fun x => by
              dsimp only; rw [hor2 x, ha10]
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp only [List.length_append, List.length_ofFn, List.length_singleton]; omega)]
              exact Bool.false_or _)
        · by_cases hb10 : b.val = 10
          · exact close_redundant a.val (Or.inl (by have := a.isLt; omega)) (fun x => by
              dsimp only; rw [hor2 x, hb10]
              have h10f : (List.ofFn x ++ [x 0 || x 2]).getD 10 false = false := by
                rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp only [List.length_append, List.length_ofFn, List.length_singleton]; omega)]; rfl
              rw [h10f, Bool.or_false])
          · have ha_lt : a.val < 10 := by have := a.isLt; omega
            have hb_lt : b.val < 10 := by have := b.isLt; omega
            by_cases hab : a.val = b.val
            · exact close_redundant a.val (Or.inl ha_lt) (fun x => by
                dsimp only; rw [hor2 x, hab, Bool.or_self])
            · have hget_lt (x : Fin 9 → Bool) (i : Fin 9) :
                  (List.ofFn x ++ [x 0 || x 2]).getD i.val false = x i := by
                rw [List.getD_append _ _ _ _ (by simp only [List.length_ofFn]; exact i.isLt),
                    ofFn_getD x i.val i.isLt]
              have hget9 (x : Fin 9 → Bool) :
                  (List.ofFn x ++ [x 0 || x 2]).getD 9 false = (x 0 || x 2) := by
                rw [List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn]; omega)]
                simp only [List.length_ofFn, Nat.sub_self]; rfl
              by_cases h029 : (a.val = 0 ∨ a.val = 2 ∨ a.val = 9) ∧ (b.val = 0 ∨ b.val = 2 ∨ b.val = 9)
              · exact close_redundant 9 (Or.inl (by omega)) (fun x => by
                  dsimp only; rw [hor2 x]
                  have h0 : (List.ofFn x ++ [x 0 || x 2]).getD 0 false = x 0 := hget_lt x 0
                  have h2 : (List.ofFn x ++ [x 0 || x 2]).getD 2 false = x 2 := hget_lt x 2
                  have h9 := hget9 x
                  rcases h029 with ⟨ha', hb'⟩
                  rcases ha' with ha' | ha' | ha' <;> rcases hb' with hb' | hb' | hb' <;>
                    first | omega | (simp only [ha', hb', h0, h2, h9]; done) | (simp only [ha', hb', h0, h2, h9]; cases x 0 <;> cases x 2 <;> rfl))
              · -- Degree-2 cases: a or b in {4, 6, 7}
                by_cases h4a : a.val = 4
                · exact close_deg2 4 (by omega) [0, 1, 2, 3, 0, 4, 5, 6, 7] 0 2 (by omega) (by omega)
                    (fun i hi => by fin_cases i <;> first | exact absurd rfl hi | decide)
                    rfl rfl (by omega) (by omega)
                    (fun y => hdel4_bool (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7))
                    b (fun x hx4 => by
                      rw [hor2 x, h4a]
                      have h4v : (List.ofFn x ++ [x 0 || x 2]).getD 4 false = false := (hget_lt x 4).trans hx4
                      rw [h4v, Bool.false_or])
                · by_cases h4b : b.val = 4
                  · exact close_deg2 4 (by omega) [0, 1, 2, 3, 0, 4, 5, 6, 7] 0 2 (by omega) (by omega)
                      (fun i hi => by fin_cases i <;> first | exact absurd rfl hi | decide)
                      rfl rfl (by omega) (by omega)
                      (fun y => hdel4_bool (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7))
                      a (fun x hx4 => by
                        rw [hor2 x, h4b]
                        have h4v : (List.ofFn x ++ [x 0 || x 2]).getD 4 false = false := (hget_lt x 4).trans hx4
                        rw [h4v, Bool.or_false])
                  · by_cases h6a : a.val = 6
                    · exact close_deg2 6 (by omega) [1, 0, 4, 7, 5, 2, 0, 6, 3] 1 4 (by omega) (by omega)
                        (fun i hi => by fin_cases i <;> first | exact absurd rfl hi | decide)
                        rfl rfl (by omega) (by omega)
                        (fun y => hdel6_bool (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7))
                        b (fun x hx6 => by
                          rw [hor2 x, h6a]
                          have h6v : (List.ofFn x ++ [x 0 || x 2]).getD 6 false = false := (hget_lt x 6).trans hx6
                          rw [h6v, Bool.false_or])
                    · by_cases h6b : b.val = 6
                      · exact close_deg2 6 (by omega) [1, 0, 4, 7, 5, 2, 0, 6, 3] 1 4 (by omega) (by omega)
                          (fun i hi => by fin_cases i <;> first | exact absurd rfl hi | decide)
                          rfl rfl (by omega) (by omega)
                          (fun y => hdel6_bool (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7))
                          a (fun x hx6 => by
                            rw [hor2 x, h6b]
                            have h6v : (List.ofFn x ++ [x 0 || x 2]).getD 6 false = false := (hget_lt x 6).trans hx6
                            rw [h6v, Bool.or_false])
                      · by_cases h7a : a.val = 7
                        · exact close_deg2 7 (by omega) [2, 1, 0, 4, 6, 3, 5, 0, 7] 2 0 (by omega) (by omega)
                            (fun i hi => by fin_cases i <;> first | exact absurd rfl hi | decide)
                            rfl rfl (by omega) (by omega)
                            (fun y => hdel7_bool (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7))
                            b (fun x hx7 => by
                              rw [hor2 x, h7a]
                              have h7v : (List.ofFn x ++ [x 0 || x 2]).getD 7 false = false := (hget_lt x 7).trans hx7
                              rw [h7v, Bool.false_or])
                        · by_cases h7b : b.val = 7
                          · exact close_deg2 7 (by omega) [2, 1, 0, 4, 6, 3, 5, 0, 7] 2 0 (by omega) (by omega)
                              (fun i hi => by fin_cases i <;> first | exact absurd rfl hi | decide)
                              rfl rfl (by omega) (by omega)
                              (fun y => hdel7_bool (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7))
                              a (fun x hx7 => by
                                rw [hor2 x, h7b]
                                have h7v : (List.ofFn x ++ [x 0 || x 2]).getD 7 false = false := (hget_lt x 7).trans hx7
                                rw [h7v, Bool.or_false])
                          · -- Now a, b ∈ {0, 1, 2, 3, 5, 8, 9}, a ≠ b, not both in {0, 2, 9}.
                            -- First bound notCount C ≤ 2 via many_nots!
                            have hnot_le2 : PEqualNP.NotBracket.notCount C ≤ 2 := by
                              let g0 : Gate := ⟨.or, [0, 2]⟩
                              let g1 : Gate := ⟨.or, [a.val, b.val]⟩
                              let full : Circuit := ⟨g0 :: g1 :: C.gates, C.output⟩
                              have hfull_fan : FanInTwo full := by
                                intro g hg
                                rcases List.mem_cons.mp hg with rfl | hg1
                                · exact ⟨Or.inr (Or.inl rfl), Nat.le_refl 2⟩
                                · rcases List.mem_cons.mp hg1 with rfl | hg2
                                  · exact ⟨Or.inr (Or.inl rfl), Nat.le_refl 2⟩
                                  · exact hfan g hg2
                              have hfull_eval : ∀ x : Fin 9 → Bool, full.eval (List.ofFn x) = edge x := by
                                intro x
                                let x7 := List.ofFn x ++ [x 0 || x 2]
                                have hs0 : step (List.ofFn x) g0 = x7 := by
                                  change List.ofFn x ++ [GateOp.or.eval [(List.ofFn x).getD 0 false, (List.ofFn x).getD 2 false]] = x7
                                  rw [ofFn_getD x 0 (by omega), ofFn_getD x 2 (by omega)]
                                  change List.ofFn x ++ [(x 0 || (x 2 || false))] = x7
                                  rw [Bool.or_false]
                                have hs1 : step x7 g1 = x7 ++ [GateOp.or.eval ([a, b].map fun i => x7.getD i.val false)] := rfl
                                change ((g0 :: g1 :: C.gates).foldl step (List.ofFn x)).getD C.output false = edge x
                                rw [List.foldl_cons, hs0, List.foldl_cons, hs1]
                                exact heq x
                              have h13 := many_nots full hfull_fan hfull_eval
                              have hfsz : full.size = 2 + C.size := by
                                change (g0 :: g1 :: C.gates).length = 2 + C.gates.length
                                simp only [List.length_cons]; omega
                              have hfnot : PEqualNP.NotBracket.notCount full = PEqualNP.NotBracket.notCount C := by
                                unfold PEqualNP.NotBracket.notCount
                                rfl
                              rw [hfsz, hfnot] at h13
                              omega
                            -- Automorphism sigma = (0 2)(3 5)(4 7) fixing x 0 || x 2
                            let sigL : List ℕ := [2, 1, 0, 5, 7, 3, 6, 4, 8]
                            have hsig_lt (i : Fin 9) : sigL.getD i.val 0 < 9 := by
                              fin_cases i <;> decide
                            let sig (i : Fin 9) : Fin 9 := ⟨sigL.getD i.val 0, hsig_lt i⟩
                            let fSig (k : ℕ) : ℕ := if k < 9 then sigL.getD k 0 else k
                            let Csig : Circuit := ⟨C.gates.map (mapGate fSig), fSig C.output⟩
                            have hCsig_fan : FanInTwo Csig := hfan_map fSig C.gates (fSig C.output) hfan
                            have hCsig_sz : Csig.size ≤ 13 := by
                              change (C.gates.map (mapGate fSig)).length ≤ 13
                              rw [List.length_map]; exact hsz
                            have hCsig_not : PEqualNP.NotBracket.notCount Csig ≤ 2 := by
                              rw [hnot_map fSig C.gates (fSig C.output) C.output]; exact hnot_le2
                            have hedge_sig (x : Fin 9 → Bool) : edge (fun i => x (sig i)) = edge x :=
                              hsig_bool (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8)
                            have eval_sig (w2 : (Fin 9 → Bool) → Bool)
                                (hw2 : ∀ x : Fin 9 → Bool,
                                  let xs := fun i => x (sig i)
                                  let x7 := List.ofFn xs ++ [xs 0 || xs 2]
                                  GateOp.or.eval ([a, b].map fun i => x7.getD i.val false) = w2 x)
                                (x : Fin 9 → Bool) :
                                Csig.eval (List.ofFn x ++ [x 0 || x 2, w2 x]) = edge x := by
                              let xs : Fin 9 → Bool := fun i => x (sig i)
                              let x7s : List Bool := List.ofFn xs ++ [xs 0 || xs 2]
                              have hlen7s : x7s.length = 10 := by
                                simp only [x7s, List.length_append, List.length_ofFn, List.length_singleton]
                              have hrew := eval_rewire 11 11 fSig
                                (fun k hk => by simp only [fSig, show ¬ (k < 9) by omega, ↓reduceIte]; omega)
                                (fun k hk => by
                                  left
                                  by_cases hk9 : k < 9
                                  · have hfk : fSig k = sigL.getD k 0 := by simp only [fSig, hk9, ↓reduceIte]
                                    have hlt := hsig_lt ⟨k, hk9⟩
                                    change sigL.getD k 0 < 9 at hlt
                                    omega
                                  · have hfk : fSig k = k := by simp only [fSig, hk9, ↓reduceIte]
                                    omega)
                                (x7s ++ [GateOp.or.eval ([a, b].map fun i => x7s.getD i.val false)])
                                (List.ofFn x ++ [x 0 || x 2, w2 x])
                                (by simp only [List.length_append, hlen7s, List.length_singleton])
                                (by simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil])
                                (fun k hk => by
                                  by_cases hk9 : k < 9
                                  · have hfk : fSig k = sigL.getD k 0 := by simp only [fSig, hk9, ↓reduceIte]
                                    have hlt9 : sigL.getD k 0 < 9 := hsig_lt ⟨k, hk9⟩
                                    have hlhs : (List.ofFn x ++ [x 0 || x 2, w2 x]).getD (fSig k) false = x ⟨sigL.getD k 0, hlt9⟩ := by
                                      rw [hfk, List.getD_append _ _ _ _ (by simp only [List.length_ofFn]; exact hlt9),
                                          ofFn_getD x (sigL.getD k 0) hlt9]
                                    have hrhs : (x7s ++ [GateOp.or.eval ([a, b].map fun i => x7s.getD i.val false)]).getD k false = xs ⟨k, hk9⟩ := by
                                      rw [List.getD_append _ _ _ _ (by omega),
                                          List.getD_append _ _ _ _ (by simp only [List.length_ofFn]; exact hk9),
                                          ofFn_getD xs k hk9]
                                    rw [hlhs, hrhs]
                                  · by_cases hk9e : k = 9
                                    · subst hk9e
                                      have hf9 : fSig 9 = 9 := rfl
                                      have hlhs : (List.ofFn x ++ [x 0 || x 2, w2 x]).getD 9 false = (x 0 || x 2) := by
                                        rw [List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn]; omega)]
                                        simp only [List.length_ofFn, Nat.sub_self]; rfl
                                      have hrhs : (x7s ++ [GateOp.or.eval ([a, b].map fun i => x7s.getD i.val false)]).getD 9 false = (xs 0 || xs 2) := by
                                        rw [List.getD_append _ _ _ _ (by omega), hget9 xs]
                                      rw [hf9, hlhs, hrhs]
                                      change (x 0 || x 2) = (x 2 || x 0)
                                      exact Bool.or_comm (x 0) (x 2)
                                    · have hk10 : k = 10 := by omega
                                      subst hk10
                                      have hf10 : fSig 10 = 10 := rfl
                                      have hlhs : (List.ofFn x ++ [x 0 || x 2, w2 x]).getD 10 false = w2 x := by
                                        rw [List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn]; omega)]
                                        simp only [List.length_ofFn]; rfl
                                      have hrhs : (x7s ++ [GateOp.or.eval ([a, b].map fun i => x7s.getD i.val false)]).getD 10 false =
                                          GateOp.or.eval ([a, b].map fun i => x7s.getD i.val false) := by
                                        rw [List.getD_append_right _ _ _ _ (by omega), hlen7s, Nat.sub_self]; rfl
                                      rw [hf10, hlhs, hrhs]
                                      exact (hw2 x).symm)
                              rw [show Csig.eval (List.ofFn x ++ [x 0 || x 2, w2 x]) =
                                       (Circuit.mk (C.gates.map (mapGate fSig)) (fSig C.output)).eval (List.ofFn x ++ [x 0 || x 2, w2 x]) from rfl,
                                  hrew, heq xs, hedge_sig x]
                            -- Direct evaluation helper (no sigma)
                            have eval_dir (w2 : (Fin 9 → Bool) → Bool)
                                (hw2 : ∀ x : Fin 9 → Bool,
                                  GateOp.or.eval ([a, b].map fun i => (List.ofFn x ++ [x 0 || x 2]).getD i.val false) = w2 x)
                                (x : Fin 9 → Bool) :
                                C.eval (List.ofFn x ++ [x 0 || x 2, w2 x]) = edge x := by
                              have h := heq x
                              dsimp only at h
                              rw [hw2 x, List.append_assoc] at h
                              exact h
                            -- Split on whether 9 ∈ {a, b}
                            by_cases h9 : a.val = 9 ∨ b.val = 9
                            · have hk_val : ∃ k : Fin 9, (k.val = 1 ∨ k.val = 3 ∨ k.val = 5 ∨ k.val = 8) ∧
                                  ∀ x : Fin 9 → Bool,
                                    GateOp.or.eval ([a, b].map fun i => (List.ofFn x ++ [x 0 || x 2]).getD i.val false) = ((x 0 || x 2) || x k) := by
                                rcases h9 with ha9 | hb9
                                · have hb_ne02 : b.val ≠ 0 ∧ b.val ≠ 2 := ⟨fun h => h029 ⟨Or.inr (Or.inr ha9), Or.inl h⟩, fun h => h029 ⟨Or.inr (Or.inr ha9), Or.inr (Or.inl h)⟩⟩
                                  refine ⟨⟨b.val, by omega⟩, by dsimp only; omega, fun x => ?_⟩
                                  rw [hor2 x, ha9, hget9 x, hget_lt x ⟨b.val, by omega⟩]
                                · have ha_ne02 : a.val ≠ 0 ∧ a.val ≠ 2 := ⟨fun h => h029 ⟨Or.inl h, Or.inr (Or.inr hb9)⟩, fun h => h029 ⟨Or.inr (Or.inl h), Or.inr (Or.inr hb9)⟩⟩
                                  refine ⟨⟨a.val, by omega⟩, by dsimp only; omega, fun x => ?_⟩
                                  rw [hor2 x, hb9, hget9 x, hget_lt x ⟨a.val, by omega⟩, Bool.or_comm]
                              obtain ⟨k, hk_cases, hkw⟩ := hk_val
                              rcases hk_cases with h1 | h3 | h5 | h8
                              · obtain ⟨x, hx⟩ := core_with9 1 (by decide) C hfan hsz hnot_le2
                                exact hx (eval_dir (fun z => (z 0 || z 2) || z 1) (fun z => by have hk1 : k = 1 := Fin.ext h1; rw [hkw z, hk1]) x)
                              · obtain ⟨x, hx⟩ := core_with9 3 (by decide) C hfan hsz hnot_le2
                                exact hx (eval_dir (fun z => (z 0 || z 2) || z 3) (fun z => by have hk3 : k = 3 := Fin.ext h3; rw [hkw z, hk3]) x)
                              · obtain ⟨x, hx⟩ := core_with9 3 (by decide) Csig hCsig_fan hCsig_sz hCsig_not
                                exact hx (eval_sig (fun z => (z 0 || z 2) || z 3) (fun z => by
                                  dsimp only
                                  have hk5 : k = 5 := Fin.ext h5
                                  rw [hkw (fun i => z (sig i)), hk5]
                                  change ((z 2 || z 0) || z 3) = ((z 0 || z 2) || z 3)
                                  rw [Bool.or_comm (z 2) (z 0)]) x)
                              · obtain ⟨x, hx⟩ := core_with9 8 (by decide) C hfan hsz hnot_le2
                                exact hx (eval_dir (fun z => (z 0 || z 2) || z 8) (fun z => by have hk8 : k = 8 := Fin.ext h8; rw [hkw z, hk8]) x)
                            · -- Neither a nor b is 9, so a, b ∈ {0, 1, 2, 3, 5, 8}
                              have ha9 : a.val < 9 := by omega
                              have hb9 : b.val < 9 := by omega
                              let af : Fin 9 := ⟨a.val, ha9⟩
                              let bf : Fin 9 := ⟨b.val, hb9⟩
                              have habw (x : Fin 9 → Bool) :
                                  GateOp.or.eval ([a, b].map fun i => (List.ofFn x ++ [x 0 || x 2]).getD i.val false) = (x af || x bf) := by
                                rw [hor2 x, hget_lt x af, hget_lt x bf]
                              have close_pair_dir (p : Fin 9 × Fin 9)
                                  (hp : p ∈ ([(0, 1), (0, 3), (0, 5), (0, 8), (1, 3), (1, 8), (3, 5), (3, 8)] : List (Fin 9 × Fin 9)))
                                  (heqp : (af = p.1 ∧ bf = p.2) ∨ (af = p.2 ∧ bf = p.1)) : False := by
                                obtain ⟨x, hx⟩ := core_no9 p hp C hfan hsz hnot_le2
                                exact hx (eval_dir (fun z => z p.1 || z p.2) (fun z => by
                                  rw [habw z]
                                  rcases heqp with ⟨h1, h2⟩ | ⟨h1, h2⟩
                                  · rw [h1, h2]
                                  · rw [h1, h2, Bool.or_comm]) x)
                              have close_pair_sig (p : Fin 9 × Fin 9)
                                  (hp : p ∈ ([(0, 1), (0, 3), (0, 5), (0, 8), (1, 3), (1, 8), (3, 5), (3, 8)] : List (Fin 9 × Fin 9)))
                                  (heqp : (sig af = p.1 ∧ sig bf = p.2) ∨ (sig af = p.2 ∧ sig bf = p.1)) : False := by
                                obtain ⟨x, hx⟩ := core_no9 p hp Csig hCsig_fan hCsig_sz hCsig_not
                                exact hx (eval_sig (fun z => z p.1 || z p.2) (fun z => by
                                  dsimp only
                                  rw [habw (fun i => z (sig i))]
                                  rcases heqp with ⟨h1, h2⟩ | ⟨h1, h2⟩
                                  · rw [h1, h2]
                                  · rw [h1, h2, Bool.or_comm]) x)
                              have ha_set : af = 0 ∨ af = 1 ∨ af = 2 ∨ af = 3 ∨ af = 5 ∨ af = 8 := by
                                have : a.val = 0 ∨ a.val = 1 ∨ a.val = 2 ∨ a.val = 3 ∨ a.val = 5 ∨ a.val = 8 := by omega
                                rcases this with h | h | h | h | h | h
                                · exact Or.inl (Fin.ext h)
                                · exact Or.inr (Or.inl (Fin.ext h))
                                · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
                                · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h))))
                                · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h)))))
                                · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext h)))))
                              have hb_set : bf = 0 ∨ bf = 1 ∨ bf = 2 ∨ bf = 3 ∨ bf = 5 ∨ bf = 8 := by
                                have : b.val = 0 ∨ b.val = 1 ∨ b.val = 2 ∨ b.val = 3 ∨ b.val = 5 ∨ b.val = 8 := by omega
                                rcases this with h | h | h | h | h | h
                                · exact Or.inl (Fin.ext h)
                                · exact Or.inr (Or.inl (Fin.ext h))
                                · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
                                · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h))))
                                · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h)))))
                                · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext h)))))
                              rcases ha_set with hae | hae | hae | hae | hae | hae <;>
                                rcases hb_set with hbe | hbe | hbe | hbe | hbe | hbe
                              -- af = 0
                              · exact hab (by rw [show a.val = af.val from rfl, show b.val = bf.val from rfl, hae, hbe])
                              · exact close_pair_dir (0, 1) (by decide) (Or.inl ⟨hae, hbe⟩)
                              · exact h029 ⟨Or.inl (congrArg Fin.val hae), Or.inr (Or.inl (congrArg Fin.val hbe))⟩
                              · exact close_pair_dir (0, 3) (by decide) (Or.inl ⟨hae, hbe⟩)
                              · exact close_pair_dir (0, 5) (by decide) (Or.inl ⟨hae, hbe⟩)
                              · exact close_pair_dir (0, 8) (by decide) (Or.inl ⟨hae, hbe⟩)
                              -- af = 1
                              · exact close_pair_dir (0, 1) (by decide) (Or.inr ⟨hae, hbe⟩)
                              · exact hab (by rw [show a.val = af.val from rfl, show b.val = bf.val from rfl, hae, hbe])
                              · exact close_pair_sig (0, 1) (by decide) (Or.inr ⟨by rw [hae]; rfl, by rw [hbe]; rfl⟩)
                              · exact close_pair_dir (1, 3) (by decide) (Or.inl ⟨hae, hbe⟩)
                              · exact close_pair_sig (1, 3) (by decide) (Or.inl ⟨by rw [hae]; rfl, by rw [hbe]; rfl⟩)
                              · exact close_pair_dir (1, 8) (by decide) (Or.inl ⟨hae, hbe⟩)
                              -- af = 2
                              · exact h029 ⟨Or.inr (Or.inl (congrArg Fin.val hae)), Or.inl (congrArg Fin.val hbe)⟩
                              · exact close_pair_sig (0, 1) (by decide) (Or.inl ⟨by rw [hae]; rfl, by rw [hbe]; rfl⟩)
                              · exact hab (by rw [show a.val = af.val from rfl, show b.val = bf.val from rfl, hae, hbe])
                              · exact close_pair_sig (0, 5) (by decide) (Or.inl ⟨by rw [hae]; rfl, by rw [hbe]; rfl⟩)
                              · exact close_pair_sig (0, 3) (by decide) (Or.inl ⟨by rw [hae]; rfl, by rw [hbe]; rfl⟩)
                              · exact close_pair_sig (0, 8) (by decide) (Or.inl ⟨by rw [hae]; rfl, by rw [hbe]; rfl⟩)
                              -- af = 3
                              · exact close_pair_dir (0, 3) (by decide) (Or.inr ⟨hae, hbe⟩)
                              · exact close_pair_dir (1, 3) (by decide) (Or.inr ⟨hae, hbe⟩)
                              · exact close_pair_sig (0, 5) (by decide) (Or.inr ⟨by rw [hae]; rfl, by rw [hbe]; rfl⟩)
                              · exact hab (by rw [show a.val = af.val from rfl, show b.val = bf.val from rfl, hae, hbe])
                              · exact close_pair_dir (3, 5) (by decide) (Or.inl ⟨hae, hbe⟩)
                              · exact close_pair_dir (3, 8) (by decide) (Or.inl ⟨hae, hbe⟩)
                              -- af = 5
                              · exact close_pair_dir (0, 5) (by decide) (Or.inr ⟨hae, hbe⟩)
                              · exact close_pair_sig (1, 3) (by decide) (Or.inr ⟨by rw [hae]; rfl, by rw [hbe]; rfl⟩)
                              · exact close_pair_sig (0, 3) (by decide) (Or.inr ⟨by rw [hae]; rfl, by rw [hbe]; rfl⟩)
                              · exact close_pair_dir (3, 5) (by decide) (Or.inr ⟨hae, hbe⟩)
                              · exact hab (by rw [show a.val = af.val from rfl, show b.val = bf.val from rfl, hae, hbe])
                              · exact close_pair_sig (3, 8) (by decide) (Or.inl ⟨by rw [hae]; rfl, by rw [hbe]; rfl⟩)
                              -- af = 8
                              · exact close_pair_dir (0, 8) (by decide) (Or.inr ⟨hae, hbe⟩)
                              · exact close_pair_dir (1, 8) (by decide) (Or.inr ⟨hae, hbe⟩)
                              · exact close_pair_sig (0, 8) (by decide) (Or.inr ⟨by rw [hae]; rfl, by rw [hbe]; rfl⟩)
                              · exact close_pair_dir (3, 8) (by decide) (Or.inr ⟨hae, hbe⟩)
                              · exact close_pair_sig (3, 8) (by decide) (Or.inr ⟨by rw [hae]; rfl, by rw [hbe]; rfl⟩)
                              · exact hab (by rw [show a.val = af.val from rfl, show b.val = bf.val from rfl, hae, hbe])
