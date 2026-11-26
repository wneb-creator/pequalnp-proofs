import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 50000 in
theorem PEqualNP.Outside.R_meta_7887_149
  (hU2 : let G := edgeGraph 11 (([9, 10, 15, 19, 27, 32, 39, 40, 52, 54, 63, 64, 73, 76, 86, 97] : List ℕ).map fun k => (k / 11, k % 11))
    ∀ C : Circuit, IsLeastAO G C → TopForm G C → C.size ≤ 21 →
      (Ustar G C).card = 2 → centreless G C = ∅ → 2 ≤ (junk G C).card →
      (junk G C).card + (orN G C \ lam G C).card ≤ 3 → False)
  (hAnd : let G := edgeGraph 11 (([9, 10, 15, 19, 27, 32, 39, 40, 52, 54, 63, 64, 73, 76, 86, 97] : List ℕ).map fun k => (k / 11, k % 11))
    ∀ (C : Circuit) (v : Fin 11) (g r : ℕ),
      let ga := gateAt C
      let J := junk G C
      let B := orN G C \ lam G C
      IsLeastAO G C → TopForm G C → 2 ≤ J.card → C.size ≤ 21 → 3 ≤ (Ustar G C).card →
      2 * (centreless G C).card + J.card + B.card < 2 * (Ustar G C).card →
      v.val < 4 → (ga g).op = GateOp.and → (ga r).op = GateOp.or →
      (∀ k < C.size, v.val ∈ (ga k).inputs ↔ k = g) →
      readers 11 C g = {r} →
      (g ∈ J → r ∈ B) →
      ∃ x : Fin 11, x.val < 4 ∧
        let c := fun j => ∃ w < 11 + j, ∀ y : Fin 11 → Bool, y x = false → wval C y (11 + j) = wval C y w
        ∃ i j k, i < j ∧ j < k ∧ k < C.size ∧ c i ∧ c j ∧ c k)
  (hOr : let G := edgeGraph 11 (([9, 10, 15, 19, 27, 32, 39, 40, 52, 54, 63, 64, 73, 76, 86, 97] : List ℕ).map fun k => (k / 11, k % 11))
    ∀ C : Circuit,
      let ga := gateAt C
      IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card → C.size ≤ 21 → 3 ≤ (Ustar G C).card →
      2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card < 2 * (Ustar G C).card →
      (∀ v : Fin 11, v.val < 4 →
        (∃ h < C.size, h ∈ mixing G C ∧ orIn 11 C (11 + h) = {v} ∧
          ∀ k < C.size, v.val ∈ (ga k).inputs ↔ k = h) ∨
        (∃ h₁ h₂, h₁ < h₂ ∧ h₂ < C.size ∧
          (ga h₁).op = GateOp.or ∧ (ga h₂).op = GateOp.or ∧
          ∀ k < C.size, v.val ∈ (ga k).inputs ↔ k = h₁ ∨ k = h₂)) →
      ∃ x : Fin 11, x.val < 4 ∧
        let c := fun j => ∃ w < 11 + j, ∀ y : Fin 11 → Bool, y x = false → wval C y (11 + j) = wval C y w
        ∃ i j k, i < j ∧ j < k ∧ k < C.size ∧ c i ∧ c j ∧ c k) :
  let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsLeastAO x1 x2 →     PEqualNP.TopForm.TopForm x1 x2 →       (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →         x2.size ≤ (21 : ℕ) →           (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card →             (∀ (x8 : Fin (11 : ℕ)),                 ↑x8 < (4 : ℕ) →                   ¬have x10 : ℕ → Prop := fun (x10 : ℕ) => x10 < x2.size ∧ ↑x8 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x10).inputs;                     (∃ (x11 : ℕ) (x12 : ℕ) (x13 : ℕ), x11 < x12 ∧ x12 < x13 ∧ x10 x11 ∧ x10 x12 ∧ x10 x13) ∨ ∃ (x11 : ℕ) (x12 : ℕ), x11 ≠ x12 ∧ x10 x11 ∧ x10 x12 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and) →               ∃ (x9 : Fin (11 : ℕ)),                 ↑x9 < (4 : ℕ) ∧                   have x10 : ℕ → Prop := fun (x10 : ℕ) => ∃ x11 < (11 : ℕ) + x10, ∀ (x12 : Fin (11 : ℕ) → Bool), x12 x9 = Bool.false → PEqualNP.ReadTwo.wval x2 x12 ((11 : ℕ) + x10) = PEqualNP.ReadTwo.wval x2 x12 x11;                   ∃ (x11 : ℕ) (x12 : ℕ) (x13 : ℕ), x11 < x12 ∧ x12 < x13 ∧ x13 < x2.size ∧ x10 x11 ∧ x10 x12 ∧ x10 x13 := by
  classical
  let _ : DecidableEq GateOp := gateOpDecEq
  intro G D hm ht hj hsz hnum hsparse
  have hU2_ge : 2 ≤ (Ustar G D).card := by omega
  by_cases hUeq2 : (Ustar G D).card = 2
  · have hcent0 : centreless G D = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro a ha
      have hpos : 1 ≤ (centreless G D).card := Finset.card_pos.mpr ⟨a, ha⟩
      omega
    have hsum : (junk G D).card + (orN G D \ lam G D).card ≤ 3 := by
      have : (centreless G D).card = 0 := by rw [hcent0]; exact Finset.card_empty
      omega
    exact False.elim (hU2 D hm ht hsz hUeq2 hcent0 hj hsum)
  have hU3 : 3 ≤ (Ustar G D).card := by omega

  let stepWire (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have wires_eq_foldl (C : Circuit) (x : List Bool) :
      C.wires x = C.gates.foldl stepWire x := rfl

  have foldl_length (gs : List Gate) (w : List Bool) :
      (gs.foldl stepWire w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [stepWire]
      omega

  have foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl stepWire w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.foldl_cons]
      have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
      rw [ih (stepWire w g) hlt]
      simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

  have getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

  have foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
      (gs.foldl stepWire w).getD (w.length + j) false =
        (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
          if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
    induction gs generalizing w j with
    | nil => simp at hj
    | cons g gs ih =>
      rw [List.foldl_cons]
      cases j with
      | zero =>
        have h1 : w.length < (stepWire w g).length := by simp [stepWire]
        rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
        simp only [List.getElem_cons_zero]
        have h2 : (stepWire w g).getD w.length false =
            g.op.eval (g.inputs.map fun i => w.getD i false) := by
          simp [stepWire, List.getD_eq_getElem?_getD]
        rw [h2]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < w.length
        · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
          simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
      | succ j =>
        have hj' : j < gs.length := by simpa using hj
        have key := ih (stepWire w g) j hj'
        have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
        rw [hl] at key
        have e : w.length + (j + 1) = w.length + 1 + j := by omega
        simp only [List.getElem_cons_succ]
        rw [e]
        exact key

  let val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

  have eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

  have gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
    change C.gates.getD j ⟨GateOp.or, []⟩ = C.gates[j]
    simp [List.getD_eq_getElem?_getD, hj]

  have gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
    rw [gateAt_eq hj]; exact List.getElem_mem hj

  have val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
      val C x u = x.getD u false := by
    unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

  have val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
      (hu : n + C.gates.length ≤ u) : val C x u = false := by
    unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

  have val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
      (hj : j < C.gates.length) :
      val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
        if i < n + j then val C x i else false) := by
    subst hx
    rw [gateAt_eq hj]
    exact foldl_getD_gate C.gates x j hj

  have val_prefix {n : ℕ} {C E : Circuit} {x : List Bool} (hx : x.length = n) {m : ℕ}
      (hmC : m ≤ C.gates.length) (hmE : m ≤ E.gates.length)
      (hg : ∀ k < m, gateAt E k = gateAt C k) : ∀ u, u < n + m → val E x u = val C x u := by
    intro u
    induction u using Nat.strong_induction_on with
    | ind u ih =>
      intro hu
      by_cases hun : u < n
      · rw [val_input hx hun, val_input hx hun]
      · obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
        have hk : k < m := by omega
        rw [val_gate hx (by omega), val_gate hx (by omega), hg k hk]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < n + k
        · rw [ite_eq_left hi, ite_eq_left hi]; exact ih i hi (by omega)
        · rw [ite_eq_right hi, ite_eq_right hi]

  let aliasWire (w i u : ℕ) : ℕ := if u = w then i else if w < u then u - 1 else u
  let aliasGate (w i : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (aliasWire w i)⟩
  let bypass (n : ℕ) (C : Circuit) (r i : ℕ) : Circuit :=
    ⟨(List.range (C.gates.length - 1)).map (fun k =>
        if k < r then gateAt C k else aliasGate (n + r) i (gateAt C (k + 1))),
      aliasWire (n + r) i C.output⟩

  have bypass_length (n : ℕ) (C : Circuit) (r i : ℕ) :
      (bypass n C r i).gates.length = C.gates.length - 1 := by simp [bypass]

  have gateAt_bypass {n : ℕ} {C : Circuit} {r i k : ℕ} (hk : k < C.gates.length - 1) :
      gateAt (bypass n C r i) k =
        if k < r then gateAt C k else aliasGate (n + r) i (gateAt C (k + 1)) := by
    have hk' : k < (bypass n C r i).gates.length := by rw [bypass_length]; exact hk
    rw [gateAt_eq hk']
    simp [bypass]

  have bypass_val_lt {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r i : ℕ}
      (hr : r < C.gates.length) : ∀ u, u < n + r → val (bypass n C r i) x u = val C x u := by
    apply val_prefix hx (by omega) (by rw [bypass_length]; omega)
    intro k hk
    rw [gateAt_bypass (by omega), ite_eq_left hk]

  have aliasWire_self (w i : ℕ) : aliasWire w i w = i := by simp [aliasWire]
  have aliasWire_lt_self {w i u : ℕ} (hu : u < w) : aliasWire w i u = u := by
    unfold aliasWire; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  have aliasWire_gt_self {w i u : ℕ} (hu : w < u) : aliasWire w i u = u - 1 := by
    unfold aliasWire; rw [ite_eq_right (by omega), ite_eq_left hu]

  have bypass_eq_wire {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
      {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r)
      (hR : (∃ k, r < k ∧ k < C.gates.length ∧ n + r ∈ (gateAt C k).inputs) →
        val C x (n + r) = val C x i) :
      ∀ u, u ≠ n + r → val C x u = val (bypass n C r i) x (aliasWire (n + r) i u) := by
    intro u
    induction u using Nat.strong_induction_on with
    | ind u ih =>
      intro hne
      by_cases hlt : u < n + r
      · rw [aliasWire_lt_self hlt, bypass_val_lt hx hr u hlt]
      · rw [aliasWire_gt_self (by omega)]
        by_cases hge : n + C.gates.length ≤ u
        · rw [val_ge hx hge, val_ge hx (by rw [bypass_length]; omega)]
        · obtain ⟨k, rfl⟩ : ∃ k, u = n + (k + 1) := ⟨u - n - 1, by omega⟩
          have hk1 : k + 1 < C.gates.length := by omega
          have hkr : ¬ k < r := by omega
          have e : n + (k + 1) - 1 = n + k := by omega
          rw [e, val_gate hx hk1, val_gate hx (by rw [bypass_length]; omega),
            gateAt_bypass (by omega), ite_eq_right hkr]
          simp only [aliasGate, List.map_map]
          congr 1
          apply List.map_congr_left
          intro i' hi'
          simp only [Function.comp_apply]
          by_cases h1 : i' = n + r
          · subst h1
            rw [aliasWire_self, ite_eq_left (by omega), ite_eq_left (by omega), bypass_val_lt hx hr i hi]
            exact hR ⟨k + 1, by omega, hk1, hi'⟩
          · by_cases h2 : i' < n + r
            · rw [aliasWire_lt_self h2, ite_eq_left (by omega), ite_eq_left (by omega),
                bypass_val_lt hx hr i' h2]
            · by_cases h3 : i' < n + (k + 1)
              · have key := ih i' h3 h1
                rw [aliasWire_gt_self (by omega)] at key
                rw [aliasWire_gt_self (by omega), ite_eq_left h3, ite_eq_left (by omega)]
                exact key
              · rw [aliasWire_gt_self (by omega), ite_eq_right h3, ite_eq_right (by omega)]

  have bypass_ok {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
      {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r)
      (hR : ((∃ k, r < k ∧ k < C.gates.length ∧ n + r ∈ (gateAt C k).inputs) ∨
        C.output = n + r) → val C x (n + r) = val C x i) :
      (bypass n C r i).eval x = C.eval x := by
    rw [eval_eq_val, eval_eq_val]
    change val (bypass n C r i) x (aliasWire (n + r) i C.output) = val C x C.output
    by_cases h : C.output = n + r
    · rw [h, aliasWire_self, bypass_val_lt hx hr i hi]
      exact (hR (Or.inr h)).symm
    · exact (bypass_eq_wire hx hr hi (fun hk => hR (Or.inl hk)) _ h).symm

  have bypass_mem {n : ℕ} {C : Circuit} {r i : ℕ} :
      ∀ g ∈ (bypass n C r i).gates, ∃ g' ∈ C.gates, g.op = g'.op ∧ g.inputs.length = g'.inputs.length := by
    intro g hg
    simp only [bypass, List.mem_map, List.mem_range] at hg
    obtain ⟨k, hk, rfl⟩ := hg
    split_ifs with h
    · exact ⟨gateAt C k, gateAt_mem (by omega), rfl, rfl⟩
    · exact ⟨gateAt C (k + 1), gateAt_mem (by omega), rfl, by simp [aliasGate]⟩

  have bypass_readsBack {n : ℕ} {C : Circuit} {r i : ℕ} (hi : i < n + r)
      (hRB : ReadsBack n C) : ReadsBack n (bypass n C r i) := by
    intro k hk u hu
    rw [bypass_length] at hk
    rw [gateAt_bypass hk] at hu
    split_ifs at hu with h
    · exact hRB k (by omega) u hu
    · simp only [aliasGate, List.mem_map] at hu
      obtain ⟨u', hu', rfl⟩ := hu
      have := hRB (k + 1) (by omega) u' hu'
      unfold aliasWire; split_ifs <;> omega

  have hAO2 : IsAO2 11 D := hm.1
  have hfun : circuitFun 11 D = graphFun G ∅ := hm.2.1
  have hRB : ReadsBack 11 D := hAO2.2.1
  have hops : ∀ k < D.gates.length, (gateAt D k).op = GateOp.and ∨ (gateAt D k).op = GateOp.or :=
    fun k hk => hAO2.1 _ (gateAt_mem hk)
  have hlen2 : ∀ k < D.gates.length, (gateAt D k).inputs.length = 2 :=
    fun k hk => hAO2.2.2 _ (gateAt_mem hk)

  have noRep : ∀ r w : ℕ, r < D.gates.length → w < 11 + r →
      (((∃ k, r < k ∧ k < D.gates.length ∧ 11 + r ∈ (gateAt D k).inputs) ∨ D.output = 11 + r) →
        ∀ x : Fin 11 → Bool, wval D x (11 + r) = wval D x w) → False := by
    intro r w hr hw heq
    have modelE : IsAO2 11 (bypass 11 D r w) := by
      refine ⟨?_, bypass_readsBack hw hRB, ?_⟩
      · intro g hg
        obtain ⟨g', hmem, hop, _⟩ := bypass_mem g hg
        rw [hop]; exact hAO2.1 g' hmem
      · intro g hg
        obtain ⟨g', hmem, _, hlen⟩ := bypass_mem g hg
        exact hlen.trans (hAO2.2.2 g' hmem)
    have fE : circuitFun 11 (bypass 11 D r w) = circuitFun 11 D := by
      funext x
      exact bypass_ok List.length_ofFn hr hw (fun h => heq h x)
    have hle := hm.2.2 (bypass 11 D r w) modelE (fE.trans hfun)
    have hlenE := bypass_length 11 D r w
    change D.gates.length ≤ (bypass 11 D r w).gates.length at hle
    omega

  have hasReader : ∀ r, r < D.gates.length → D.output ≠ 11 + r →
      ∃ k, r < k ∧ k < D.gates.length ∧ 11 + r ∈ (gateAt D k).inputs := by
    intro r hr hout
    by_contra hno
    refine noRep r 0 hr (by omega) ?_
    rintro (h | h)
    · exact absurd h hno
    · exact absurd h hout

  have andE : ∀ a b : Bool, GateOp.and.eval [a, b] = (a && b) := by
    intro a b; cases a <;> cases b <;> rfl
  have orE : ∀ a b : Bool, GateOp.or.eval [a, b] = (a || b) := by
    intro a b; cases a <;> cases b <;> rfl

  have gsem : ∀ k < D.gates.length, ∃ p q : ℕ, (gateAt D k).inputs = [p, q] ∧ p < 11 + k ∧
      q < 11 + k ∧ (∀ x : Fin 11 → Bool,
        wval D x (11 + k) = (gateAt D k).op.eval [wval D x p, wval D x q]) := by
    intro k hk
    obtain ⟨p, q, hpq⟩ := List.length_eq_two.mp (hlen2 k hk)
    have hp : p < 11 + k := hRB k hk p (by rw [hpq]; simp)
    have hq : q < 11 + k := hRB k hk q (by rw [hpq]; simp)
    refine ⟨p, q, hpq, hp, hq, fun x => ?_⟩
    have hv := val_gate (C := D) (x := List.ofFn x) List.length_ofFn hk
    rw [hpq] at hv
    simp only [List.map_cons, List.map_nil, ite_eq_left hp, ite_eq_left hq] at hv
    exact hv

  have hin : ∀ (v : Fin 11) (x : Fin 11 → Bool), wval D x v.val = x v := by
    intro v x
    have hv := val_input (C := D) (x := List.ofFn x) List.length_ofFn v.isLt
    refine hv.trans ?_
    rw [List.getD_eq_getElem _ _ (by simp)]
    exact List.getElem_ofFn _

  have zv : ∀ (v : Fin 11) (x : Fin 11 → Bool), x v = false → wval D x v.val = false :=
    fun v x hx => (hin v x).trans hx

  have wval_mono : ∀ (x y : Fin 11 → Bool), (∀ i : Fin 11, x i = true → y i = true) →
      ∀ w : ℕ, wval D x w = true → wval D y w = true := by
    intro x y hxy w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hwx
      by_cases hw : w < 11
      · have hx := (hin ⟨w, hw⟩ x).symm.trans hwx
        exact (hin ⟨w, hw⟩ y).trans (hxy ⟨w, hw⟩ hx)
      by_cases hge : 11 + D.gates.length ≤ w
      · have hf : wval D x w = false := val_ge List.length_ofFn hge
        exact absurd (hf.symm.trans hwx) Bool.false_ne_true
      obtain ⟨k, rfl⟩ : ∃ k, w = 11 + k := ⟨w - 11, by omega⟩
      have hk : k < D.gates.length := by omega
      obtain ⟨p, q, _, hp, hq, hs⟩ := gsem k hk
      rw [hs x] at hwx
      rw [hs y]
      rcases hops k hk with hop | hop
      · rw [hop, andE, Bool.and_eq_true] at hwx ⊢
        exact ⟨ih p hp hwx.1, ih q hq hwx.2⟩
      · rw [hop, orE, Bool.or_eq_true] at hwx ⊢
        exact hwx.elim (fun h => Or.inl (ih p hp h)) (fun h => Or.inr (ih q hq h))

  have wval_allFalse : ∀ w : ℕ, wval D (fun _ : Fin 11 => false) w = false := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      by_cases hw : w < 11
      · exact hin ⟨w, hw⟩ _
      by_cases hge : 11 + D.gates.length ≤ w
      · exact val_ge List.length_ofFn hge
      obtain ⟨k, rfl⟩ : ∃ k, w = 11 + k := ⟨w - 11, by omega⟩
      have hk : k < D.gates.length := by omega
      obtain ⟨p, q, _, hp, hq, hs⟩ := gsem k hk
      rw [hs, ih p hp, ih q hq]
      rcases hops k hk with hop | hop <;> simp [hop, andE, orE]

  have wval_ge : ∀ (x : Fin 11 → Bool) (u : ℕ), 11 + D.gates.length ≤ u → wval D x u = false :=
    fun _ _ hu => val_ge List.length_ofFn hu

  have piDef : ∀ a b i : Fin 11, pairInput a b i = decide (i = a ∨ i = b) := fun _ _ _ => rfl

  have gfDef : ∀ x : Fin 11 → Bool, graphFun G ∅ x =
      (decide (∃ u : Fin 11, u ∈ (∅ : Finset (Fin 11)) ∧ x u = true) ||
       decide (∃ u v : Fin 11, G.Adj u v ∧ x u = true ∧ x v = true)) := fun _ => rfl

  have outNeIn : ∀ v : Fin 11, D.output ≠ v.val := by
    intro v hout
    have h1 : wval D (pairInput v v) D.output = graphFun G ∅ (pairInput v v) := congrFun hfun (pairInput v v)
    have h2 : wval D (pairInput v v) v.val = true := by rw [hin, piDef]; simp
    have h3 : graphFun G ∅ (pairInput v v) = false := by
      rw [gfDef]
      simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
        decide_eq_false_iff_not, not_exists, not_and]
      intro a b hab ha hb
      simp only [piDef, decide_eq_true_eq, or_self] at ha hb
      subst ha; subst hb
      exact G.ne_of_adj hab rfl
    rw [hout, h2, h3] at h1
    cases h1

  have deg2_adj : ∀ v : Fin 11, v.val < 4 → ∃ w₁ w₂ : Fin 11, w₁ ≠ w₂ ∧ G.Adj v w₁ ∧ G.Adj v w₂ := by
    intro v hv
    fin_cases v
    · exact ⟨9, 10, by decide, by decide, by decide⟩
    · exact ⟨4, 8, by decide, by decide, by decide⟩
    · exact ⟨5, 10, by decide, by decide, by decide⟩
    · exact ⟨6, 7, by decide, by decide, by decide⟩
    all_goals exact False.elim (by simp at hv)

  have no_common_nb : ∀ v : Fin 11, v.val < 4 → ∀ u : Fin 11, u ≠ v →
      ¬ ∀ w : Fin 11, G.Adj v w → G.Adj u w := by
    intro v hv u huv hall
    fin_cases v
    · exact (by decide : ∀ x : Fin 11, x ≠ 0 → ¬ (G.Adj x 9 ∧ G.Adj x 10)) u huv
        ⟨hall 9 (by decide), hall 10 (by decide)⟩
    · exact (by decide : ∀ x : Fin 11, x ≠ 1 → ¬ (G.Adj x 4 ∧ G.Adj x 8)) u huv
        ⟨hall 4 (by decide), hall 8 (by decide)⟩
    · exact (by decide : ∀ x : Fin 11, x ≠ 2 → ¬ (G.Adj x 5 ∧ G.Adj x 10)) u huv
        ⟨hall 5 (by decide), hall 10 (by decide)⟩
    · exact (by decide : ∀ x : Fin 11, x ≠ 3 → ¬ (G.Adj x 6 ∧ G.Adj x 7)) u huv
        ⟨hall 6 (by decide), hall 7 (by decide)⟩
    all_goals exact False.elim (by simp at hv)

  have graphFun_single : ∀ w : Fin 11, graphFun G ∅ (pairInput w w) = false := by
    intro w
    rw [gfDef]
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
      decide_eq_false_iff_not, not_exists, not_and]
    intro a b hab ha hb
    simp only [piDef, decide_eq_true_eq, or_self] at ha hb
    subst ha; subst hb
    exact G.ne_of_adj hab rfl

  have graphFun_pair_iff : ∀ u w : Fin 11, graphFun G ∅ (pairInput u w) = true ↔ G.Adj u w := by
    intro u w
    rw [gfDef]
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
      decide_eq_true_eq]
    constructor
    · rintro ⟨a, b, hab, ha, hb⟩
      simp only [piDef, decide_eq_true_eq] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact False.elim (G.ne_of_adj hab rfl)
      · exact hab
      · exact hab.symm
      · exact False.elim (G.ne_of_adj hab rfl)
    · intro h
      exact ⟨u, w, h, by simp [piDef], by simp [piDef]⟩

  have hasInputReader : ∀ v : Fin 11, v.val < 4 → ∃ k < D.size, v.val ∈ (gateAt D k).inputs := by
    intro v hv
    by_contra hnone
    have hno : ∀ k < D.gates.length, v.val ∉ (gateAt D k).inputs := fun k hk hm => hnone ⟨k, hk, hm⟩
    obtain ⟨w, _, _, hvw, _⟩ := deg2_adj v hv
    have hsame : ∀ q : ℕ, q ≠ v.val → wval D (pairInput v w) q = wval D (pairInput w w) q := by
      intro q
      induction q using Nat.strong_induction_on with
      | ind q ih =>
        intro hqv
        by_cases hq : q < 11
        · rw [hin ⟨q, hq⟩, hin ⟨q, hq⟩]
          have hne : (⟨q, hq⟩ : Fin 11) ≠ v := fun e => hqv (congrArg Fin.val e)
          simp [piDef, hne]
        by_cases hge : 11 + D.gates.length ≤ q
        · rw [wval_ge _ _ hge, wval_ge _ _ hge]
        obtain ⟨k, rfl⟩ : ∃ k, q = 11 + k := ⟨q - 11, by omega⟩
        have hk : k < D.gates.length := by omega
        obtain ⟨p, q', hpq, hp, hq', hs⟩ := gsem k hk
        have hpv : p ≠ v.val := fun e => hno k hk (by rw [hpq, e]; simp)
        have hqv' : q' ≠ v.val := fun e => hno k hk (by rw [hpq, e]; simp)
        rw [hs, hs, ih p hp hpv, ih q' hq' hqv']
    have h1 := hsame D.output (outNeIn v)
    change circuitFun 11 D (pairInput v w) = circuitFun 11 D (pairInput w w) at h1
    rw [hfun, (graphFun_pair_iff v w).mpr hvw, graphFun_single w] at h1
    cases h1

  have zand : ∀ (v : Fin 11) (k u : ℕ), k < D.gates.length → (gateAt D k).op = GateOp.and →
      u ∈ (gateAt D k).inputs → (∀ x : Fin 11 → Bool, x v = false → wval D x u = false) →
      ∀ x : Fin 11 → Bool, x v = false → wval D x (11 + k) = false := by
    intro v k u hk hop hu hz x hx
    obtain ⟨p, q, hpq, _, _, hs⟩ := gsem k hk
    rw [hpq, List.mem_pair] at hu
    rw [hs x, hop, andE]
    have hzz := hz x hx
    rcases hu with rfl | rfl <;> simp [hzz]

  have rep1 : ∀ (v : Fin 11) (k u : ℕ), k < D.gates.length → u ∈ (gateAt D k).inputs →
      (∀ x : Fin 11 → Bool, x v = false → wval D x u = false) →
      ∃ w < 11 + k, ∀ x : Fin 11 → Bool, x v = false → wval D x (11 + k) = wval D x w := by
    intro v k u hk hu hz
    obtain ⟨p, q, hpq, hp, hq, hs⟩ := gsem k hk
    have hu' := hu
    rw [hpq, List.mem_pair] at hu'
    rcases hops k hk with hop | hop
    · refine ⟨u, hRB k hk u hu, fun x hx => ?_⟩
      rw [zand v k u hk hop hu hz x hx, hz x hx]
    · rcases hu' with rfl | rfl
      · refine ⟨q, hq, fun x hx => ?_⟩
        rw [hs x, hop, orE, hz x hx]; simp
      · refine ⟨p, hp, fun x hx => ?_⟩
        rw [hs x, hop, orE, hz x hx]; simp

  have outNZ : ∀ (v : Fin 11) (g : ℕ), v.val < 4 →
      (∀ x : Fin 11 → Bool, x v = false → wval D x (11 + g) = false) → D.output ≠ 11 + g := by
    intro v g hv hz hout
    have e1 := hz (fun i : Fin 11 => decide (4 ≤ i.val)) (by simpa using hv)
    have e0 : graphFun G ∅ (fun i : Fin 11 => decide (4 ≤ i.val)) = true := by
      rw [gfDef]
      simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
        decide_eq_true_eq]
      exact ⟨4, 8, by decide, by decide, by decide⟩
    have e2 : wval D (fun i : Fin 11 => decide (4 ≤ i.val)) D.output = true :=
      (congrFun hfun _).trans e0
    rw [hout, e1] at e2
    exact Bool.false_ne_true e2

  have fin3 : ∀ (v : Fin 11), v.val < 4 → ∀ a b c : ℕ, a ≠ b → a ≠ c → b ≠ c →
      a < D.gates.length → b < D.gates.length → c < D.gates.length →
      (∃ w < 11 + a, ∀ x : Fin 11 → Bool, x v = false → wval D x (11 + a) = wval D x w) →
      (∃ w < 11 + b, ∀ x : Fin 11 → Bool, x v = false → wval D x (11 + b) = wval D x w) →
      (∃ w < 11 + c, ∀ x : Fin 11 → Bool, x v = false → wval D x (11 + c) = wval D x w) →
      ∃ x9 : Fin 11, x9.val < 4 ∧
        have x10 : ℕ → Prop := fun j => ∃ w < 11 + j, ∀ x : Fin 11 → Bool, x x9 = false → wval D x (11 + j) = wval D x w
        ∃ i j k, i < j ∧ j < k ∧ k < D.size ∧ x10 i ∧ x10 j ∧ x10 k := by
    intro v hv a b c hab hac hbc ha hb hc ra rb rc
    refine ⟨v, hv, ?_⟩
    rcases lt_or_gt_of_ne hab with o1 | o1 <;> rcases lt_or_gt_of_ne hac with o2 | o2 <;>
      rcases lt_or_gt_of_ne hbc with o3 | o3 <;>
      first
      | exact ⟨a, b, c, by omega, by omega, hc, ra, rb, rc⟩
      | exact ⟨a, c, b, by omega, by omega, hb, ra, rc, rb⟩
      | exact ⟨b, a, c, by omega, by omega, hc, rb, ra, rc⟩
      | exact ⟨b, c, a, by omega, by omega, ha, rb, rc, ra⟩
      | exact ⟨c, a, b, by omega, by omega, hb, rc, ra, rb⟩
      | exact ⟨c, b, a, by omega, by omega, ha, rc, rb, ra⟩

  have orStep_def : ∀ (cs : List (List ℕ)) (g : Gate), orStep 11 cs g =
      cs ++ [cs.length :: if g.op = GateOp.or then
        (g.inputs.filter fun w => decide (11 ≤ w ∧ w < 11 + cs.length)).flatMap
          (fun w => cs.getD (w - 11) [])
      else []] := fun _ _ => rfl

  have orSets_def : orSets 11 D = D.gates.foldl (orStep 11) [] := rfl

  have orStep_len : ∀ (gs : List Gate) (cs : List (List ℕ)),
      (gs.foldl (orStep 11) cs).length = cs.length + gs.length := by
    intro gs; induction gs with
    | nil => intro cs; simp
    | cons g gs ih => intro cs; rw [List.foldl_cons, ih, orStep_def]; simp; omega

  have orStep_getD_lt : ∀ (gs : List Gate) (cs : List (List ℕ)) (m : ℕ),
      m < cs.length → (gs.foldl (orStep 11) cs).getD m [] = cs.getD m [] := by
    intro gs; induction gs with
    | nil => intro cs m _; rfl
    | cons g gs ih =>
      intro cs m hm
      rw [List.foldl_cons, ih _ m (by rw [orStep_def]; simp; omega), orStep_def]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

  have orSets_getD : ∀ k < D.gates.length, ∀ t : ℕ,
      t ∈ (orSets 11 D).getD k [] ↔ t = k ∨ ((gateAt D k).op = GateOp.or ∧
        ∃ w ∈ (gateAt D k).inputs, 11 ≤ w ∧ w < 11 + k ∧ t ∈ (orSets 11 D).getD (w - 11) []) := by
    intro k hk t
    have hsplit : D.gates = D.gates.take k ++ D.gates[k] :: D.gates.drop (k + 1) := by
      rw [List.cons_getElem_drop_succ, List.take_append_drop]
    have hpre_len : (D.gates.take k).length = k := List.length_take_of_le (by omega)
    let cs0 := (D.gates.take k).foldl (orStep 11) []
    have hcs0_len : cs0.length = k := by
      have h1 := orStep_len (D.gates.take k) []
      simpa [cs0, hpre_len] using h1
    have hget_lt : ∀ m < k, (orSets 11 D).getD m [] = cs0.getD m [] := by
      intro m hm
      rw [orSets_def]
      conv_lhs => rw [hsplit]
      rw [List.foldl_append]
      exact orStep_getD_lt _ cs0 m (by omega)
    have hget_k : (orSets 11 D).getD k [] = (orStep 11 cs0 (gateAt D k)).getD k [] := by
      rw [orSets_def]
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_cons, ← gateAt_eq hk]
      have hstep_len : (orStep 11 cs0 (gateAt D k)).length = cs0.length + 1 := by
        rw [orStep_def]; simp
      exact orStep_getD_lt _ (orStep 11 cs0 (gateAt D k)) k (by omega)
    have hstep_k : (orStep 11 cs0 (gateAt D k)).getD k [] =
        if (gateAt D k).op = GateOp.or then
          k :: ((gateAt D k).inputs.filter fun w => decide (11 ≤ w ∧ w < 11 + k)).flatMap
            (fun w => cs0.getD (w - 11) [])
        else [k] := by
      have hlen_eq : cs0.length = k := hcs0_len
      rw [orStep_def, ← hlen_eq]
      simp [List.getD_eq_getElem?_getD]
      split_ifs <;> rfl
    rw [hget_k, hstep_k]
    by_cases hop : (gateAt D k).op = GateOp.or
    · rw [ite_eq_left hop]
      simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
      constructor
      · rintro (rfl | ⟨w, ⟨hw, h11, hlt⟩, hmem⟩)
        · exact Or.inl rfl
        · refine Or.inr ⟨hop, w, hw, h11, hlt, ?_⟩
          rw [hget_lt (w - 11) (by omega)]
          exact hmem
      · rintro (rfl | ⟨_, w, hw, h11, hlt, hmem⟩)
        · exact Or.inl rfl
        · refine Or.inr ⟨w, ⟨hw, h11, hlt⟩, ?_⟩
          rw [hget_lt (w - 11) (by omega)] at hmem
          exact hmem
    · rw [ite_eq_right hop]
      simp [hop]

  have orReaches_val : ∀ (x : Fin 11 → Bool) (w k : ℕ),
      OrReaches 11 D w k → w < 11 + D.gates.length → wval D x (11 + k) = true → wval D x w = true := by
    intro x w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro k hr hw hkx
      obtain ⟨h11, hmem⟩ := hr
      obtain ⟨j, rfl⟩ : ∃ j, w = 11 + j := ⟨w - 11, by omega⟩
      have hj : j < D.gates.length := by omega
      simp only [Nat.add_sub_cancel_left] at hmem
      rw [orSets_getD j hj k] at hmem
      rcases hmem with rfl | ⟨hop, u, hu, h11u, hlt, hmem'⟩
      · exact hkx
      · obtain ⟨p, q, hpq, _, _, hs⟩ := gsem j hj
        rw [hs x, hop, orE, Bool.or_eq_true]
        have huval : wval D x u = true := ih u hlt k ⟨h11u, hmem'⟩ (by omega) hkx
        rw [hpq, List.mem_pair] at hu
        rcases hu with rfl | rfl
        · exact Or.inl huval
        · exact Or.inr huval

  have orIn_mem : ∀ (w : ℕ) (i : Fin 11), i ∈ orIn 11 D w ↔
      (i : ℕ) = w ∨ ∃ k < D.gates.length,
        OrReaches 11 D w k ∧ (gateAt D k).op = GateOp.or ∧ (i : ℕ) ∈ (gateAt D k).inputs := by
    intro w i
    delta orIn
    rw [Finset.mem_filter]
    exact and_iff_right (Finset.mem_univ i)

  have orIn_val : ∀ (u : Fin 11) (w : ℕ), w < 11 + D.gates.length → u ∈ orIn 11 D w →
      wval D (pairInput u u) w = true := by
    intro u w hw hu
    rw [orIn_mem] at hu
    rcases hu with heq | ⟨k, hk, hreach, hop, hmem⟩
    · rw [← heq, hin, piDef]; simp
    · apply orReaches_val (pairInput u u) w k hreach hw
      obtain ⟨p, q, hpq, _, _, hs⟩ := gsem k hk
      rw [hs, hop, orE, Bool.or_eq_true]
      rw [hpq, List.mem_pair] at hmem
      rcases hmem with h | h <;> rw [← h, hin]
      · exact Or.inl (by simp [piDef])
      · exact Or.inr (by simp [piDef])

  have orIn_and_empty : ∀ g < D.gates.length, (gateAt D g).op = GateOp.and → orIn 11 D (11 + g) = ∅ := by
    intro g hg hop
    rw [Finset.eq_empty_iff_forall_notMem]
    intro u hu
    rw [orIn_mem] at hu
    rcases hu with heq | ⟨k, hk, hreach, hopk, _⟩
    · have := u.isLt; omega
    · obtain ⟨_, hmem⟩ := hreach
      simp only [Nat.add_sub_cancel_left] at hmem
      rw [orSets_getD g hg k] at hmem
      rcases hmem with rfl | ⟨hor, _⟩
      · rw [hop] at hopk; cases hopk
      · rw [hop] at hor; cases hor

  by_cases hA : ∃ v : Fin 11, v.val < 4 ∧ ∃ g, g < D.gates.length ∧
      (gateAt D g).op = GateOp.and ∧ v.val ∈ (gateAt D g).inputs
  · obtain ⟨v, hv, g, hg, hgop, hgv⟩ := hA
    have hv11 := v.isLt
    have huniq_v : ∀ k < D.size, v.val ∈ (gateAt D k).inputs ↔ k = g := by
      intro k hk
      constructor
      · intro hkv
        by_contra hne
        exact hsparse v hv (Or.inr ⟨g, k, Ne.symm hne, ⟨hg, hgv⟩, ⟨hk, hkv⟩, hgop⟩)
      · rintro rfl; exact hgv
    have zg := zand v g v.val hg hgop hgv (zv v)
    have rg := rep1 v g v.val hg hgv (zv v)
    obtain ⟨r, hgr, hr, hrg⟩ := hasReader g hg (outNZ v g hv zg)
    have rr := rep1 v r (11 + g) hr hrg zg
    rcases hops r hr with hrop | hrop
    · have zr := zand v r (11 + g) hr hrop hrg zg
      obtain ⟨s, hrs, hs, hsr⟩ := hasReader r hr (outNZ v r hv zr)
      exact fin3 v hv g r s (by omega) (by omega) (by omega) hg hr hs rg rr
        (rep1 v s (11 + r) hs hsr zr)
    · by_cases hB : ∃ k, k < D.gates.length ∧ k ≠ r ∧ 11 + g ∈ (gateAt D k).inputs
      · obtain ⟨k, hk, hkr, hkg_in⟩ := hB
        have hkg : k ≠ g := fun e => by have := hRB k hk _ hkg_in; omega
        exact fin3 v hv g r k (by omega) (Ne.symm hkg) (Ne.symm hkr) hg hr hk rg rr
          (rep1 v k (11 + g) hk hkg_in zg)
      · have hreaders_g : readers 11 D g = {r} := by
          ext k
          delta readers
          rw [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
          constructor
          · rintro ⟨hk, hm⟩
            by_contra hne
            exact hB ⟨k, hk, hne, hm⟩
          · rintro rfl; exact ⟨hr, hrg⟩
        have hjunk_r : g ∈ junk G D → r ∈ orN G D \ lam G D := by
          intro hgj
          change g ∈ (Finset.range D.gates.length).filter _ at hgj
          rw [Finset.mem_filter, Finset.mem_range] at hgj
          obtain ⟨_, _, _, x, hgx, hfx⟩ := hgj
          have hrx : gateVal 11 D r x = true := by
            obtain ⟨pr, qr, hpr, _, _, hrs⟩ := gsem r hr
            change wval D x (11 + r) = true
            rw [hrs x, hrop, orE, Bool.or_eq_true]
            have hrg' := hrg
            rw [hpr, List.mem_pair] at hrg'
            rcases hrg' with rfl | rfl
            · exact Or.inl hgx
            · exact Or.inr hgx
          have hr_orN : r ∈ orN G D := by
            delta orN gatesWhere
            rw [Finset.mem_filter, Finset.mem_range]
            refine ⟨hr, hrop, fun hbf => ?_⟩
            have := hbf x hrx
            rw [hfx] at this; exact Bool.false_ne_true this
          have hr_not_lam : r ∉ lam G D := by
            intro hlam
            delta lam at hlam
            rw [Finset.mem_filter] at hlam
            obtain ⟨_, h0, h1, _⟩ := hlam
            obtain ⟨pr, qr, hpr, _, _, _⟩ := gsem r hr
            have hrg' := hrg
            rw [hpr, List.mem_pair] at hrg'
            have hempty := orIn_and_empty g hg hgop
            rcases hrg' with rfl | rfl
            · have hop0 : opnd D r 0 = 11 + g := by
                change (gateAt D r).inputs.getD 0 0 = 11 + g; rw [hpr]; rfl
              rw [hop0, hempty] at h0; exact Finset.not_nonempty_empty h0
            · have hop1 : opnd D r 1 = 11 + g := by
                change (gateAt D r).inputs.getD 1 0 = 11 + g; rw [hpr]; rfl
              rw [hop1, hempty] at h1; exact Finset.not_nonempty_empty h1
          exact Finset.mem_sdiff.mpr ⟨hr_orN, hr_not_lam⟩
        exact hAnd D v g r hm ht hj hsz hU3 hnum hv hgop hrop huniq_v hreaders_g hjunk_r
  · refine hOr D hm ht hj hsz hU3 hnum ?_
    intro v hv
    have hor_only : ∀ k < D.size, v.val ∈ (gateAt D k).inputs → (gateAt D k).op = GateOp.or := by
      intro k hk hkv
      rcases hops k hk with hand | hor
      · exact False.elim (hA ⟨v, hv, k, hk, hand, hkv⟩)
      · exact hor
    obtain ⟨h₁, hh₁, hhv₁⟩ := hasInputReader v hv
    by_cases htwo : ∃ h₂ < D.size, h₂ ≠ h₁ ∧ v.val ∈ (gateAt D h₂).inputs
    · obtain ⟨h₂, hh₂, hne, hhv₂⟩ := htwo
      have huniq2 : ∀ k < D.size, v.val ∈ (gateAt D k).inputs ↔ k = h₁ ∨ k = h₂ := by
        intro k hk
        constructor
        · intro hkv
          by_contra hneither
          push Not at hneither
          rcases lt_or_gt_of_ne hne.symm with o12 | o12
          · rcases lt_or_gt_of_ne hneither.1 with ok1 | ok1
            · exact hsparse v hv (Or.inl ⟨k, h₁, h₂, ok1, o12, ⟨hk, hkv⟩, ⟨hh₁, hhv₁⟩, ⟨hh₂, hhv₂⟩⟩)
            · rcases lt_or_gt_of_ne hneither.2 with ok2 | ok2
              · exact hsparse v hv (Or.inl ⟨h₁, k, h₂, ok1, ok2, ⟨hh₁, hhv₁⟩, ⟨hk, hkv⟩, ⟨hh₂, hhv₂⟩⟩)
              · exact hsparse v hv (Or.inl ⟨h₁, h₂, k, o12, ok2, ⟨hh₁, hhv₁⟩, ⟨hh₂, hhv₂⟩, ⟨hk, hkv⟩⟩)
          · rcases lt_or_gt_of_ne hneither.2 with ok2 | ok2
            · exact hsparse v hv (Or.inl ⟨k, h₂, h₁, ok2, o12, ⟨hk, hkv⟩, ⟨hh₂, hhv₂⟩, ⟨hh₁, hhv₁⟩⟩)
            · rcases lt_or_gt_of_ne hneither.1 with ok1 | ok1
              · exact hsparse v hv (Or.inl ⟨h₂, k, h₁, ok2, ok1, ⟨hh₂, hhv₂⟩, ⟨hk, hkv⟩, ⟨hh₁, hhv₁⟩⟩)
              · exact hsparse v hv (Or.inl ⟨h₂, h₁, k, o12, ok1, ⟨hh₂, hhv₂⟩, ⟨hh₁, hhv₁⟩, ⟨hk, hkv⟩⟩)
        · rintro (rfl | rfl)
          · exact hhv₁
          · exact hhv₂
      right
      rcases lt_or_gt_of_ne hne with o | o
      · exact ⟨h₂, h₁, o, hh₁, hor_only h₂ hh₂ hhv₂, hor_only h₁ hh₁ hhv₁,
          fun k hk => (huniq2 k hk).trans or_comm⟩
      · exact ⟨h₁, h₂, o, hh₂, hor_only h₁ hh₁ hhv₁, hor_only h₂ hh₂ hhv₂, huniq2⟩
    · left
      have huniq1 : ∀ k < D.size, v.val ∈ (gateAt D k).inputs ↔ k = h₁ := by
        intro k hk
        constructor
        · intro hkv
          by_contra hne
          exact htwo ⟨k, hk, hne, hkv⟩
        · rintro rfl; exact hhv₁
      have hhop : (gateAt D h₁).op = GateOp.or := hor_only h₁ hh₁ hhv₁
      obtain ⟨p, q, hpq, hp, hq, hhs⟩ := gsem h₁ hh₁
      have hhv₁' := hhv₁
      rw [hpq, List.mem_pair] at hhv₁'
      obtain ⟨a, ha_lt, hha_pair⟩ : ∃ a < 11 + h₁,
          (gateAt D h₁).inputs = [v.val, a] ∨ (gateAt D h₁).inputs = [a, v.val] := by
        rcases hhv₁' with rfl | rfl
        · exact ⟨q, hq, Or.inl hpq⟩
        · exact ⟨p, hp, Or.inr hpq⟩
      have hh₁' : h₁ < D.gates.length := hh₁
      have ha_ne_v : a ≠ v.val := by
        intro heq
        refine noRep h₁ v.val hh₁ (by omega) (fun _ x => ?_)
        rw [hhs x, hhop, orE]
        rcases hha_pair with h1 | h1
        · rw [hpq] at h1; injection h1 with e1 e2; injection e2 with e3; rw [e1, e3, heq]; simp
        · rw [hpq] at h1; injection h1 with e1 e2; injection e2 with e3; rw [e1, heq, e3]; simp
      have ha_false_v : wval D (pairInput v v) a = false := by
        have hsame : ∀ q' < 11 + h₁, q' ≠ v.val → wval D (pairInput v v) q' = wval D (fun _ : Fin 11 => false) q' := by
          intro q'
          induction q' using Nat.strong_induction_on with
          | ind q' ih =>
            intro hqlt hqv
            by_cases hq11 : q' < 11
            · rw [hin ⟨q', hq11⟩, hin ⟨q', hq11⟩]
              have hne : (⟨q', hq11⟩ : Fin 11) ≠ v := fun e => hqv (congrArg Fin.val e)
              simp [piDef, hne]
            obtain ⟨k, rfl⟩ : ∃ k, q' = 11 + k := ⟨q' - 11, by omega⟩
            have hk : k < D.gates.length := by omega
            have hkh : k ≠ h₁ := by omega
            obtain ⟨p', q'', hpq', hp', hq'', hks⟩ := gsem k hk
            have hpv : p' ≠ v.val := fun e => hkh ((huniq1 k hk).mp (by rw [hpq', e]; simp))
            have hqv' : q'' ≠ v.val := fun e => hkh ((huniq1 k hk).mp (by rw [hpq', e]; simp))
            rw [hks, hks, ih p' hp' (by omega) hpv, ih q'' hq'' (by omega) hqv']
        exact (hsame a ha_lt ha_ne_v).trans (wval_allFalse a)
      have ha_single_false : ∀ u : Fin 11, wval D (pairInput u u) a = false := by
        intro u
        by_contra hat
        have hat' : wval D (pairInput u u) a = true := Bool.eq_true_of_not_eq_false hat
        have huv : u ≠ v := fun e => by rw [e, ha_false_v] at hat'; cases hat'
        refine no_common_nb v hv u huv (fun w hvw => ?_)
        have hax : wval D (pairInput u w) a = true := by
          apply wval_mono (pairInput u u) (pairInput u w) _ a hat'
          intro z hz; simp [piDef] at hz ⊢; exact Or.inl hz
        have hhx : wval D (pairInput u w) (11 + h₁) = true := by
          rw [hhs, hhop, orE, Bool.or_eq_true]
          rcases hha_pair with h1 | h1
          · rw [hpq] at h1; injection h1 with e1 e2; injection e2 with e3; exact Or.inr (e3 ▸ hax)
          · rw [hpq] at h1; injection h1 with e1 e2; injection e2 with e3; exact Or.inl (e1 ▸ hax)
        have hdom : ∀ q' : ℕ, q' ≠ v.val → wval D (pairInput v w) q' = true → wval D (pairInput u w) q' = true := by
          intro q'
          induction q' using Nat.strong_induction_on with
          | ind q' ih =>
            intro hqv hq1
            by_cases hq11 : q' < 11
            · have hx := (hin ⟨q', hq11⟩ (pairInput v w)).symm.trans hq1
              have hne : (⟨q', hq11⟩ : Fin 11) ≠ v := fun e => hqv (congrArg Fin.val e)
              have hqw : (⟨q', hq11⟩ : Fin 11) = w := by simp [piDef, hne] at hx; exact hx
              rw [hin ⟨q', hq11⟩, hqw, piDef]; simp
            by_cases hge : 11 + D.gates.length ≤ q'
            · exact absurd ((val_ge List.length_ofFn hge).symm.trans hq1) Bool.false_ne_true
            obtain ⟨k, rfl⟩ : ∃ k, q' = 11 + k := ⟨q' - 11, by omega⟩
            have hk : k < D.gates.length := by omega
            by_cases hkh : k = h₁
            · subst hkh; exact hhx
            obtain ⟨p', q'', hpq', hp', hq'', hks⟩ := gsem k hk
            have hpv : p' ≠ v.val := fun e => hkh ((huniq1 k hk).mp (by rw [hpq', e]; simp))
            have hqv' : q'' ≠ v.val := fun e => hkh ((huniq1 k hk).mp (by rw [hpq', e]; simp))
            rw [hks] at hq1 ⊢
            rcases hops k hk with hopk | hopk
            · rw [hopk, andE, Bool.and_eq_true] at hq1 ⊢
              exact ⟨ih p' hp' hpv hq1.1, ih q'' hq'' hqv' hq1.2⟩
            · rw [hopk, orE, Bool.or_eq_true] at hq1 ⊢
              exact hq1.elim (fun h => Or.inl (ih p' hp' hpv h)) (fun h => Or.inr (ih q'' hq'' hqv' h))
        have hout1 : wval D (pairInput v w) D.output = true :=
          (congrFun hfun (pairInput v w)).trans ((graphFun_pair_iff v w).mpr hvw)
        have hout2 : wval D (pairInput u w) D.output = true := hdom D.output (outNeIn v) hout1
        exact (graphFun_pair_iff u w).mp ((congrFun hfun (pairInput u w)).symm.trans hout2)
      have ha_orIn_empty : orIn 11 D a = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro u hu
        have := orIn_val u a (by omega) hu
        rw [ha_single_false u] at this
        exact Bool.false_ne_true this
      have hv_orIn : v ∈ orIn 11 D v.val := (orIn_mem v.val v).mpr (Or.inl rfl)
      have hh_notBelow : ¬ BelowF G D h₁ := by
        intro hbf
        have hhv_true : gateVal 11 D h₁ (pairInput v v) = true := by
          change wval D (pairInput v v) (11 + h₁) = true
          rw [hhs, hhop, orE, Bool.or_eq_true]
          rcases hha_pair with h1 | h1
          · rw [hpq] at h1; injection h1 with e1 e2; rw [e1, hin, piDef]; exact Or.inl (by simp)
          · rw [hpq] at h1; injection h1 with e1 e2; injection e2 with e3; rw [e3, hin, piDef]; exact Or.inr (by simp)
        have := hbf (pairInput v v) hhv_true
        rw [graphFun_single v] at this
        exact Bool.false_ne_true this
      have hh_mix : h₁ ∈ mixing G D := by
        delta mixing
        rw [Finset.mem_filter]
        refine ⟨?_, ?_⟩
        · delta orN gatesWhere
          rw [Finset.mem_filter, Finset.mem_range]
          exact ⟨hh₁, hhop, hh_notBelow⟩
        · rcases hha_pair with h1 | h1
          · have hop0 : opnd D h₁ 0 = v.val := by
              change (gateAt D h₁).inputs.getD 0 0 = v.val; rw [h1]; rfl
            have hop1 : opnd D h₁ 1 = a := by
              change (gateAt D h₁).inputs.getD 1 0 = a; rw [h1]; rfl
            rw [hop0, hop1, ha_orIn_empty]
            intro heq
            have hv0 : orIn 11 D v.val = ∅ := heq.mpr rfl
            rw [hv0] at hv_orIn
            exact Finset.notMem_empty v hv_orIn
          · have hop0 : opnd D h₁ 0 = a := by
              change (gateAt D h₁).inputs.getD 0 0 = a; rw [h1]; rfl
            have hop1 : opnd D h₁ 1 = v.val := by
              change (gateAt D h₁).inputs.getD 1 0 = v.val; rw [h1]; rfl
            rw [hop0, hop1, ha_orIn_empty]
            intro heq
            have hv0 : orIn 11 D v.val = ∅ := heq.mp rfl
            rw [hv0] at hv_orIn
            exact Finset.notMem_empty v hv_orIn
      have hh_orIn : orIn 11 D (11 + h₁) = {v} := by
        ext u
        simp only [Finset.mem_singleton]
        constructor
        · intro hu
          have hval := orIn_val u (11 + h₁) (by omega) hu
          rw [hhs, hhop, orE, Bool.or_eq_true] at hval
          rcases hha_pair with h1 | h1
          · rw [hpq] at h1; injection h1 with e1 e2; injection e2 with e3
            rw [e1, e3, hin, ha_single_false u] at hval
            rcases hval with h | h
            · exact (by simpa [piDef] using h : v = u).symm
            · exact False.elim (Bool.false_ne_true h)
          · rw [hpq] at h1; injection h1 with e1 e2; injection e2 with e3
            rw [e1, e3, hin, ha_single_false u] at hval
            rcases hval with h | h
            · exact False.elim (Bool.false_ne_true h)
            · exact (by simpa [piDef] using h : v = u).symm
        · rintro rfl
          rw [orIn_mem]
          right
          refine ⟨h₁, hh₁, ⟨by omega, ?_⟩, hhop, hhv₁⟩
          simp only [Nat.add_sub_cancel_left]
          exact (orSets_getD h₁ hh₁ h₁).mpr (Or.inl rfl)
      exact ⟨h₁, hh₁, hh_mix, hh_orIn, huniq1⟩
