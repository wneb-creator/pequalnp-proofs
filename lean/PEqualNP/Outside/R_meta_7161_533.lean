import PEqualNP.Defs

set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.R_meta_7161_533
    (shell : let E := fun (i j : Fin 13) => (i.val + j.val) % 13 ∈ ([0,1,3,9] : List Nat);
      let I := fun (S T : Finset (Fin 13)) => List.ofFn fun k : Fin 26 =>
        if k.val < 13 then decide (Fin.ofNat 13 k.val ∈ S) else decide (Fin.ofNat 13 k.val ∈ T);
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C →
        C.size ≤ 23 → C.output < 26 + C.size →
        ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (w : Nat), PEqualNP.MetaComplexity.Monotone2 D ∧
          D.size ≤ 62 ∧ C.output < w ∧ ∀ S T,
          (D.wires (I S T)).getD C.output false = C.eval (I S T) ∧
          (D.wires (I S T)).getD w false =
            decide (∃ i ∈ S, i.val ∉ ([0,1,2,3,6] : List Nat) ∧ ∃ j ∈ T, E i j))
    (core : let E := fun (i j : Fin 13) => (i.val + j.val) % 13 ∈ ([0,1,3,9] : List Nat);
      let I := fun (S T : Finset (Fin 13)) => List.ofFn fun k : Fin 26 =>
        if k.val < 13 then decide (Fin.ofNat 13 k.val ∈ S) else decide (Fin.ofNat 13 k.val ∈ T);
      let N := fun (s : Finset (Fin 13)) => Finset.univ.filter fun j => ∀ i ∈ s, ¬ E i j;
      let X : Finset (Fin 13) := {0,1,2,3,6};
      ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧
        C.size ≤ 23 ∧ C.output < 26 + C.size ∧
        (∀ i ∈ X, ∀ j, E i j → C.eval (I {i} {j}) = true) ∧
        ∀ A ⊆ X, (A = X ∨ N A ≠ N X) → C.eval (I (A ∪ Xᶜ) (N A)) = false) :
    let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => (↑x1 + ↑x2) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]; have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x2 : Finset (Fin (13 : ℕ))) => {x3 : Fin (13 : ℕ) | ∀ x4 ∈ x2, ¬x1 x4 x3}; have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool := fun (x3 x4 : Finset (Fin (13 : ℕ))) => List.ofFn fun (x5 : Fin (26 : ℕ)) => if ↑x5 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x3) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x4); ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ) (x6 : ℕ) (x7 : Bool),   PEqualNP.MetaComplexity.Monotone2 x4 ∧     x4.size ≤ (62 : ℕ) ∧       x5 < x6 ∧         have x8 : ℕ → Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x8 : ℕ) (x9 x10 : Finset (Fin (13 : ℕ))) => (x4.wires (x3 x9 x10)).getD x8 Bool.false;         have x9 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x9 x10 : Finset (Fin (13 : ℕ))) => (if x7 = Bool.true then PEqualNP.CircuitLowerBounds.GateOp.and else PEqualNP.CircuitLowerBounds.GateOp.or).eval [x8 x5 x9 x10, x8 x6 x9 x10];         (∀ (x10 x11 : Fin (13 : ℕ)), x1 x10 x11 → x9 {x10} {x11} = Bool.true) ∧ ∀ (x10 : Finset (Fin (13 : ℕ))), x10.card ≤ (3 : ℕ) → x9 x10 (x2 x10) = Bool.false ∧ x9 (x2 x10) x10 = Bool.false := by
  dsimp only at shell core ⊢
  obtain ⟨C, hC, szC, outC, pos, neg⟩ := core
  obtain ⟨D, w, hD, szD, order, values⟩ := shell C hC szC outC
  let X : Finset (Fin 13) := {0,1,2,3,6}
  have inX (i : Fin 13) : i ∈ X ↔ i.val ∈ ([0,1,2,3,6] : List Nat) := by
    revert i
    decide
  let E (i j : Fin 13) := (i.val+j.val)%13 ∈ ([0,1,3,9] : List Nat)
  let N (s : Finset (Fin 13)) := Finset.univ.filter fun j => ∀ i ∈ s, ¬ E i j
  let I (r t : Finset (Fin 13)) := List.ofFn fun k : Fin 26 =>
    if k.val < 13 then decide (Fin.ofNat 13 k.val ∈ r) else decide (Fin.ofNat 13 k.val ∈ t)
  let rel (x y : Bool) := x = true → y = true
  have getMono {x y : List Bool} (h : List.Forall₂ rel x y) (i : Nat) :
      rel (x.getD i false) (y.getD i false) := by
    induction h generalizing i with
    | nil => exact fun hh => hh
    | cons hh ht ih => cases i with
      | zero => exact hh
      | succ i => exact ih i
  have opMono (g : PEqualNP.CircuitLowerBounds.Gate)
      (hop : g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or)
      {x y : List Bool} (h : List.Forall₂ rel x y) :
      rel (g.op.eval (g.inputs.map fun i => x.getD i false))
        (g.op.eval (g.inputs.map fun i => y.getD i false)) := by
    intro hx
    rcases hop with hand | hor
    · rw [hand] at hx ⊢
      change (g.inputs.map fun i => x.getD i false).all id = true at hx
      change (g.inputs.map fun i => y.getD i false).all id = true
      simp at hx ⊢
      exact fun i hi => getMono h i (hx i hi)
    · rw [hor] at hx ⊢
      change (g.inputs.map fun i => x.getD i false).any id = true at hx
      change (g.inputs.map fun i => y.getD i false).any id = true
      simp at hx ⊢
      obtain ⟨i,hi,hx⟩ := hx
      exact ⟨i,hi,getMono h i hx⟩
  have foldMono (gs : List PEqualNP.CircuitLowerBounds.Gate)
      (hg : ∀ g ∈ gs, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or)
      {x y : List Bool} (h : List.Forall₂ rel x y) :
      List.Forall₂ rel
        (gs.foldl (fun v g => v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]) x)
        (gs.foldl (fun v g => v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]) y) := by
    induction gs generalizing x y with
    | nil => exact h
    | cons g tail ih =>
      apply ih (fun a ha => hg a (List.mem_cons_of_mem _ ha))
      exact List.rel_append h (.cons (opMono g (hg g (by simp)) h) .nil)
  have mono {a b c d : Finset (Fin 13)} (h₁ : a ⊆ c) (h₂ : b ⊆ d) :
      rel (C.eval (I a b)) (C.eval (I c d)) := by
    have h : List.Forall₂ rel (I a b) (I c d) := by
      apply List.forall₂_of_length_eq_of_get (by simp [I])
      intro n hn hm
      simp only [I,List.get_eq_getElem,List.getElem_ofFn,rel]
      split
      · simpa using fun hh => h₁ hh
      · simpa using fun hh => h₂ hh
    apply getMono (foldMono C.gates ?_ h) C.output
    intro g hg
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using (hC g hg).1
  have negAll (r t : Finset (Fin 13)) (h : ∀ i ∈ r, ∀ j ∈ t, ¬ E i j) :
      C.eval (I r t) = false := by
    let A := r ∩ X
    have hsmall : A ⊆ X := Finset.inter_subset_right
    have hrows : r ⊆ A ∪ Xᶜ := by
      intro i hi
      by_cases hi' : i ∈ X
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hi,hi'⟩)
      · exact Finset.mem_union_right _ (Finset.mem_compl.mpr hi')
    have hcols : t ⊆ N A := by
      intro j hj
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, fun i hi => h i (Finset.mem_inter.mp hi).1 j hj⟩
    apply Bool.eq_false_iff.mpr
    intro bad
    have contra := mono hrows hcols bad
    have hz : C.eval (I (A ∪ Xᶜ) (N A)) = false := by
      by_cases heq : N A = N X
      · have ha : A ∪ Xᶜ ⊆ X ∪ Xᶜ := Finset.union_subset_union hsmall (Finset.Subset.refl _)
        have hn : N A ⊆ N X := by rw [heq]
        apply Bool.eq_false_iff.mpr
        intro hhit
        have habs := mono ha hn hhit
        have hx : C.eval (I (X ∪ Xᶜ) (N X)) = false := neg X (Finset.Subset.refl _) (Or.inl rfl)
        rw [hx] at habs
        cases habs
      · exact neg A hsmall (Or.inr heq)
    rw [hz] at contra
    cases contra
  refine ⟨D, C.output, w, false, hD, szD, order, ?_, ?_⟩
  · intro i j edge
    obtain ⟨carry, star⟩ := values {i} {j}
    change (_ || _) = true
    rw [carry, star]
    by_cases row : i.val ∈ ([0,1,2,3,6] : List Nat)
    · rw [pos i ((inX i).mpr row) j edge]
      exact Bool.true_or _
    · have hit : ∃ a ∈ ({i} : Finset (Fin 13)), a.val ∉ ([0,1,2,3,6] : List Nat) ∧
            ∃ b ∈ ({j} : Finset (Fin 13)), (a.val+b.val)%13 ∈ ([0,1,3,9] : List Nat) :=
          ⟨i, by simp, row, j, by simp, edge⟩
      rw [decide_eq_true hit]
      exact Bool.or_true _
  · intro S _
    obtain ⟨carryL, starL⟩ := values S (N S)
    obtain ⟨carryR, starR⟩ := values (N S) S
    have hl : ∀ i ∈ S, ∀ j ∈ N S, ¬ E i j :=
      fun i hi j hj => (Finset.mem_filter.mp hj).2 i hi
    have hr : ∀ i ∈ N S, ∀ j ∈ S, ¬ E i j := by
      intro i hi j hj hij
      apply (Finset.mem_filter.mp hi).2 j hj
      simpa only [E,Nat.add_comm i.val j.val] using hij
    have disjointL : ¬ ∃ i ∈ S, i.val ∉ ([0,1,2,3,6] : List Nat) ∧ ∃ j ∈ N S,
        (i.val+j.val)%13 ∈ ([0,1,3,9] : List Nat) := by
      rintro ⟨i,hi,_,j,hj,hij⟩
      exact hl i hi j hj hij
    have disjointR : ¬ ∃ i ∈ N S, i.val ∉ ([0,1,2,3,6] : List Nat) ∧ ∃ j ∈ S,
        (i.val+j.val)%13 ∈ ([0,1,3,9] : List Nat) := by
      rintro ⟨i,hi,_,j,hj,hij⟩
      exact hr i hi j hj hij
    change (_ || _) = false ∧ (_ || _) = false
    rw [carryL, starL, carryR, starR, negAll S (N S) hl, negAll (N S) S hr]
    rw [decide_eq_false disjointL, decide_eq_false disjointR]
    exact ⟨rfl, rfl⟩
