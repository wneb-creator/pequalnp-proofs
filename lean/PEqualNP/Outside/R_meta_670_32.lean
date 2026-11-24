import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_670_32
    (andBound : ∀ C : Circuit, Monotone2 C → circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) →
      5 ≤ PEqualNP.ReadTwo.nAnd C)
    (orBound : ∀ C : Circuit, Monotone2 C → circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) →
      11 ≤ PEqualNP.ReadTwo.nOr C)
    (oneNot : ∀ C : Circuit, FanInTwo C → PEqualNP.NotBracket.notCount C = 1 →
      circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size)
    (fewNot : ∀ C : Circuit, FanInTwo C → 2 ≤ PEqualNP.NotBracket.notCount C →
      PEqualNP.NotBracket.notCount C ≤ 7 → circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) :
    ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 15 := by
  classical
  have nonNot_lower (n : ℕ) (C : Circuit) (legal : FanInTwo C)
      (hdep : ∀ i : Fin n, ∃ x y : Fin n → Bool,
        (∀ j, j ≠ i → x j = y j) ∧ circuitFun n C x ≠ circuitFun n C y) :
      n ≤ (C.gates.filter (fun g => decide (g.op ≠ GateOp.not))).length + 1 := by
    classical
    let wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

    let effInputs (g : Gate) : List ℕ :=
      if g.op = GateOp.not then g.inputs.take 1 else g.inputs

    let active (g : Gate) : Bool :=
      decide (g.op ≠ GateOp.not)

    have eval_effective (g : Gate) (w : List Bool) :
        g.op.eval (g.inputs.map fun i => w.getD i false) =
          g.op.eval ((effInputs g).map fun i => w.getD i false) := by
      by_cases hop : g.op = GateOp.not
      · have he : effInputs g = g.inputs.take 1 := ite_eq_left hop
        rw [he, hop]
        cases g.inputs <;> rfl
      · simp only [effInputs, ite_eq_right hop]

    have effInputs_length (g : Gate) (h : g.inputs.length ≤ 2) :
        (effInputs g).length ≤ (if active g then 1 else 0) + 1 := by
      by_cases hop : g.op = GateOp.not
      · simp [effInputs, active, hop]
      · simpa [effInputs, active, hop] using h

    have getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
        (L ++ [S]).getD j d = L.getD j d := by
      by_cases hj : j < L.length
      · exact List.getD_append _ _ _ _ hj
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

    have getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
      simp


    let gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
      ((effInputs g).map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

    have mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
        i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
      induction l with
      | nil => simp
      | cons b l ih => simp [ih]

    have mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
        i ∈ gateSupp L g ↔ ∃ a ∈ effInputs g, i ∈ L.getD a ∅ :=
      mem_foldr_union _ _ _


    let suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
      gs.foldl (fun L g => L ++ [gateSupp L g]) L


    let inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}


    let Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
      L.length = w.length ∧ w.length = w'.length ∧
        ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

    have agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
        ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
          Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
      induction gs with
      | nil => intro L w w' h; exact h
      | cons g gs ih =>
        intro L w w' h
        obtain ⟨h1, h2, h3⟩ := h
        apply ih (L ++ [gateSupp L g])
          (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
        refine ⟨by simp [h1], by simp [h2], ?_⟩
        intro j hj
        by_cases hjl : j = L.length
        · subst hjl
          rw [getD_snoc_eq] at hj
          rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
          rw [eval_effective, eval_effective]
          congr 1
          apply List.map_congr_left
          intro a ha
          exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
        · rw [getD_snoc_ne _ _ _ _ hjl] at hj
          rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
          exact h3 j hj

    have agree_inputs (x y : Fin n → Bool) :
        Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
      refine ⟨by simp [inputSupps], by simp, ?_⟩
      intro j hj
      by_cases hjn : j < n
      · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
        simp [hjn, hx]
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]


    let Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
      ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

    have cnt_inputs : Cnt 0 (inputSupps n) := by
      intro W
      refine le_trans Finset.card_biUnion_le ?_
      rw [zero_add, Finset.card_eq_sum_ones]
      apply Finset.sum_le_sum
      intro j _
      by_cases hjn : j < n
      · simp [inputSupps, hjn]
      · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

    have cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate)
        (hg : (effInputs g).length ≤ (if active g then 1 else 0) + 1)
        (h : Cnt t L) : Cnt (t + (if active g then 1 else 0)) (L ++ [gateSupp L g]) := by
      intro W
      by_cases hW : L.length ∈ W
      · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
            ⊆ ((W.erase L.length ∪ (effInputs g).toFinset).biUnion fun j => L.getD j ∅) := by
          intro i hi
          rw [Finset.mem_biUnion] at hi ⊢
          obtain ⟨j, hjW, hij⟩ := hi
          by_cases hjl : j = L.length
          · subst hjl
            rw [getD_snoc_eq] at hij
            obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
            exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
          · rw [getD_snoc_ne _ _ _ _ hjl] at hij
            exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
        have hc1 : (W.erase L.length ∪ (effInputs g).toFinset).card ≤
            (W.card - 1) + ((if active g then 1 else 0) + 1) := by
          refine le_trans (Finset.card_union_le _ _) ?_
          rw [Finset.card_erase_of_mem hW]
          exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
        have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
        have := h (W.erase L.length ∪ (effInputs g).toFinset)
        have := Finset.card_le_card hsub
        omega
      · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
            = (W.biUnion fun j => L.getD j ∅) := by
          apply Finset.biUnion_congr rfl
          intro j hj
          exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
        rw [heq]
        have := h W
        omega

    have cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
        (∀ g ∈ gs, g.inputs.length ≤ 2) → Cnt t L →
          Cnt (t + (gs.filter active).length) (suppsFrom gs L) := by
      induction gs with
      | nil => intro t L _ h; exact h
      | cons g gs ih =>
        intro t L hok h
        have := ih (t + (if active g then 1 else 0)) (L ++ [gateSupp L g])
          (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
          (cnt_step t L g (effInputs_length g (hok g List.mem_cons_self)) h)
        cases ha : active g <;>
          simpa [suppsFrom, List.filter_cons, ha, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
            using this

    set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
    have hall : ∀ i : Fin n, i ∈ S := by
      intro i
      by_contra hi
      obtain ⟨x, y, hxy, hx⟩ := hdep i
      apply hx
      have hag := (agree_wiresFrom x y C.gates _ _ _
        (agree_inputs _ _)).2.2 C.output (by
          intro k hk
          have : k ≠ i := fun e => hi (e ▸ hk)
          exact hxy k this)
      exact hag
    have hcard : S.card = n := by
      rw [Finset.eq_univ_of_forall hall]; simp
    have hc := cnt_suppsFrom C.gates 0 (inputSupps n) (fun g hg => (legal g hg).2)
      cnt_inputs {C.output}
    simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
    rw [← hS, hcard] at hc
    simpa only [active] using hc
  rintro ⟨C, hfan, hsize, hcompute⟩
  have heq : circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) := funext hcompute
  by_cases hz : PEqualNP.NotBracket.notCount C = 0
  · have hmono : Monotone2 C := by
      classical
      intro g hg
      obtain ⟨hop, hlen⟩ := hfan g hg
      refine ⟨?_, hlen⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
      rcases hop with hop | hop | hop
      · exact Or.inl hop
      · exact Or.inr hop
      · have hmem : g ∈ C.gates.filter (fun v => @decide (v.op = GateOp.not) (lineDegreeGateOpDecEq _ _)) := by
          simp [List.mem_filter, hg, hop]
        have hnil : C.gates.filter (fun v => @decide (v.op = GateOp.not) (lineDegreeGateOpDecEq _ _)) = [] :=
          List.eq_nil_of_length_eq_zero hz
        rw [hnil] at hmem
        exact (List.not_mem_nil hmem).elim
    have ha := andBound C hmono heq
    have ho := orBound C hmono heq
    have hcount : PEqualNP.ReadTwo.nAnd C + PEqualNP.ReadTwo.nOr C ≤ C.size := by
      unfold PEqualNP.ReadTwo.nAnd PEqualNP.ReadTwo.nOr Circuit.size
      generalize C.gates = gs
      induction gs with
      | nil => simp
      | cons g gs ih =>
        by_cases ha : g.op = GateOp.and
        · simp [ha]
          omega
        · by_cases ho : g.op = GateOp.or
          · simp [ho]
            omega
          · simp [ha, ho]
            omega
    omega
  · by_cases h1 : PEqualNP.NotBracket.notCount C = 1
    · have := oneNot C hfan h1 heq
      omega
    · by_cases h7 : PEqualNP.NotBracket.notCount C ≤ 7
      · have := fewNot C hfan (by omega) h7 heq
        omega
      · have hdep : ∀ i : Fin 9, ∃ x y : Fin 9 → Bool,
            (∀ j, j ≠ i → x j = y j) ∧ circuitFun 9 C x ≠ circuitFun 9 C y := by
          intro i
          let nb : Fin 9 → Fin 9 := ![1, 0, 1, 2, 3, 0, 1, 2, 3]
          let x : Fin 9 → Bool := fun j => decide (j = nb i)
          let y : Fin 9 → Bool := fun j => decide (j = nb i ∨ j = i)
          refine ⟨x, y, ?_, ?_⟩
          · intro j hj
            simp [x, y, hj]
          · rw [heq]
            have hv : ∀ i : Fin 9,
                (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) (fun j => decide (j = nb i)) = false ∧
                (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) (fun j => decide (j = nb i ∨ j = i)) = true := by
              decide +kernel
            change (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) (fun j => decide (j = nb i)) ≠
              (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) (fun j => decide (j = nb i ∨ j = i))
            rw [(hv i).1, (hv i).2]
            decide
        have lower := nonNot_lower 9 C hfan hdep
        have hsplit : (C.gates.filter (fun g => decide (g.op ≠ GateOp.not))).length +
            PEqualNP.NotBracket.notCount C = C.size := by
          classical
          unfold PEqualNP.NotBracket.notCount Circuit.size
          generalize C.gates = gs
          induction gs with
          | nil => simp
          | cons g gs ih =>
            by_cases h : g.op = GateOp.not
            · simp [h] at *
              omega
            · simp [h] at *
              omega
        omega
