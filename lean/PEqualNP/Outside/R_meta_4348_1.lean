import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16000 in
theorem PEqualNP.Outside.R_meta_4348_1
    (cofactor :
      ¬ PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 ||
        x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4) 12)
    (marked :
      let f : (Fin 8 → Bool) → Bool := fun x =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 ||
        x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4
      ∀ (A B : PEqualNP.CircuitLowerBounds.Circuit) (k : ℕ),
        PEqualNP.MetaComplexity.FanInTwo A →
        PEqualNP.MetaComplexity.FanInTwo B →
        A.size + B.size ≤ 12 →
        (∃ g ∈ A.gates.take 1, g.op = PEqualNP.CircuitLowerBounds.GateOp.and) →
        let w := fun (b : Bool) (z : Fin 8 → Bool) =>
          A.wires (List.ofFn (Function.update z 0 false) ++ [z 0 || b, z 0 || z 3])
        (∀ z : Fin 8 → Bool, B.eval (w false z ++ [(w false z).getD k false]) = f z) →
        ∃ z : Fin 8 → Bool, B.eval (w true z ++ [true]) ≠ (f z || z 0 || z 3)) :
    ∀ (x1 : List ℕ), x1.length ≤ (2 : ℕ) → ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (12 : ℕ) → (∀ (x6 : Fin (9 : ℕ) → Bool), x3.eval (List.ofFn (Function.update x6 (0 : Fin (9 : ℕ)) Bool.false) ++ [x6 (0 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)), x6 (0 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ))] ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x7 : ℕ) => (List.ofFn (Function.update x6 (0 : Fin (9 : ℕ)) Bool.false) ++ [x6 (0 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)), x6 (0 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ))]).getD x7 Bool.false) x1)]) = [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x7 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x6 x7.1 && x6 x7.2) → False := by
  classical
  open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
  intro x1 hx1len C0 hfan0 hsz0 hC0ev
  let f : (Fin 8 → Bool) → Bool := fun x =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 ||
    x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4
  let g : (Fin 8 → Bool) → Bool := fun x => f x || x 0 || x 3
  let p9 : (Fin 9 → Bool) → Bool := fun x =>
    ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)] :
      List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2
  let lift : Bool → (Fin 8 → Bool) → (Fin 9 → Bool) := fun b z i =>
    [z 0, z 1, z 2, z 3, b, z 4, z 5, z 6, z 7].getD i.val false
  let base : Bool → (Fin 8 → Bool) → List Bool := fun b z =>
    [false, z 1, z 2, z 3, b, z 4, z 5, z 6, z 7, z 0 || b, z 0 || z 3]
  have hbaseEq : ∀ b z,
      List.ofFn (Function.update (lift b z) 0 false) ++ [lift b z 0 || lift b z 4, lift b z 0 || lift b z 3] =
        base b z := fun _ _ => rfl
  let w11 : Bool → (Fin 8 → Bool) → Bool := fun b z =>
    GateOp.and.eval (x1.map fun j => (base b z).getD j false)
  let inp : Bool → (Fin 8 → Bool) → List Bool := fun b z => base b z ++ [w11 b z]
  have hFtruth : ∀ b z, p9 (lift b z) = if b then g z else f z := by
    intro b z
    cases b
    · change (z 0 && z 1 || (z 1 && z 2 || (z 2 && z 3 || (z 3 && false || (false && z 0 ||
        (z 0 && z 4 || (z 1 && z 5 || (z 2 && z 6 || (z 3 && z 7 || (z 4 && z 6 ||
        (z 5 && z 7 || (z 7 && z 4 || false)))))))))))) = f z
      simp only [f, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or]
      ac_rfl
    · change (z 0 && z 1 || (z 1 && z 2 || (z 2 && z 3 || (z 3 && true || (true && z 0 ||
        (z 0 && z 4 || (z 1 && z 5 || (z 2 && z 6 || (z 3 && z 7 || (z 4 && z 6 ||
        (z 5 && z 7 || (z 7 && z 4 || false)))))))))))) = g z
      simp only [f, g, Bool.and_true, Bool.true_and, Bool.or_false]
      ac_rfl
  let step : List Bool → Gate → List Bool := fun w gt =>
    w ++ [gt.op.eval (gt.inputs.map fun j => w.getD j false)]
  let mapGate : (ℕ → ℕ) → Gate → Gate := fun r gt => ⟨gt.op, gt.inputs.map r⟩
  have evalAnd0 : GateOp.and.eval [] = true := rfl
  have evalAnd1 : ∀ a, GateOp.and.eval [a] = a := fun a => by cases a <;> rfl
  have evalAnd2 : ∀ a b, GateOp.and.eval [a, b] = (a && b) := fun a b => by cases a <;> cases b <;> rfl
  have evalOr0 : GateOp.or.eval [] = false := rfl
  have evalOr1 : ∀ a, GateOp.or.eval [a] = a := fun a => by cases a <;> rfl
  have evalOr2 : ∀ a b, GateOp.or.eval [a, b] = (a || b) := fun a b => by cases a <;> cases b <;> rfl
  have evalNot0 : GateOp.not.eval [] = true := rfl
  have evalNot1 : ∀ a l, GateOp.not.eval (a :: l) = !a := fun _ _ => rfl
  let trimNot : Gate → Gate := fun gt =>
    GateOp.casesOn gt.op gt gt ⟨GateOp.not, gt.inputs.take 1⟩ (fun _ => gt) gt
  let D : Circuit := ⟨C0.gates.map trimNot, C0.output⟩
  have hfanD : FanInTwo D := by
    intro gt hgt
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hgt
    have h0 := hfan0 g0 hg0
    cases hop : g0.op with
    | and => simpa [trimNot, hop] using h0
    | or => simpa [trimNot, hop] using h0
    | not => exact ⟨by simp [trimNot, hop], by simp [trimNot, hop]⟩
    | mod _ => simpa [trimNot, hop] using h0
    | maj => simpa [trimNot, hop] using h0
  have hnotLen : ∀ gt ∈ D.gates, gt.op = GateOp.not → gt.inputs.length ≤ 1 := by
    intro gt hgt hnot
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hgt
    cases hop : g0.op with
    | and => simp [trimNot, hop] at hnot
    | or => simp [trimNot, hop] at hnot
    | not => simp [trimNot, hop]
    | mod _ => simp [trimNot, hop] at hnot
    | maj => simp [trimNot, hop] at hnot
  have hszD : D.size ≤ 12 := by
    change (C0.gates.map trimNot).length ≤ 12
    rw [List.length_map]; exact hsz0
  have hDeval : ∀ b z, D.eval (inp b z) = if b then g z else f z := by
    intro b z
    have hstepEq : ∀ (gs : List Gate) (w : List Bool),
        (gs.map trimNot).foldl step w = gs.foldl step w := by
      intro gs
      induction gs with
      | nil => intro _; rfl
      | cons g0 gs ihg =>
        intro w
        rw [List.map_cons, List.foldl_cons, List.foldl_cons]
        have hs : step w (trimNot g0) = step w g0 := by
          cases hop : g0.op with
          | and => simp [trimNot, hop]
          | or => simp [trimNot, hop]
          | not =>
            simp only [step, trimNot, hop]
            cases hgi : g0.inputs with
            | nil => rfl
            | cons a l =>
              simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, evalNot1]
          | mod _ => simp [trimNot, hop]
          | maj => simp [trimNot, hop]
        rw [hs]
        exact ihg _
    change ((C0.gates.map trimNot).foldl step (inp b z)).getD C0.output false = _
    rw [hstepEq]
    have h1 := hC0ev (lift b z)
    rw [hbaseEq] at h1
    exact h1.trans (hFtruth b z)
  have foldLen : ∀ (gs : List Gate) (w : List Bool), (gs.foldl step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons gt gs ih => intro w; rw [List.foldl_cons, ih]; simp [step]; omega
  have foldKeep : ∀ (gs : List Gate) (w : List Bool) (j : ℕ), j < w.length →
      (gs.foldl step w).getD j false = w.getD j false := by
    intro gs
    induction gs with
    | nil => intro _ _ _; rfl
    | cons gt gs ih =>
      intro w j hj
      rw [List.foldl_cons, ih (step w gt) j (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hj
  have foldSetComm : ∀ (k : ℕ) (v : Bool) (gs : List Gate) (w : List Bool),
      (∀ gt ∈ gs, k ∉ gt.inputs) → k < w.length →
      gs.foldl step (w.set k v) = (gs.foldl step w).set k v := by
    intro k v gs
    induction gs with
    | nil => intro _ _ _; rfl
    | cons gt gs ih =>
      intro w hno hkw
      have hkg : k ∉ gt.inputs := hno gt List.mem_cons_self
      have hmap : gt.inputs.map (fun j => (w.set k v).getD j false) =
          gt.inputs.map (fun j => w.getD j false) := by
        apply List.map_congr_left
        intro j hj
        have hne : j ≠ k := fun h => hkg (h ▸ hj)
        simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hne)]
      have hst : step (w.set k v) gt = (step w gt).set k v := by
        simp only [step, hmap, List.set_append_left _ _ hkw]
      rw [List.foldl_cons, List.foldl_cons, hst]
      exact ih (step w gt) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')) (by simp [step]; omega)
  have hfFalse : f (fun _ => false) = false := by decide
  have hfTrue : f (fun _ => true) = true := by decide
  have hNonConstF : ∀ c : Bool, ¬ (∀ z : Fin 8 → Bool, f z = c) := by
    intro c hc
    have h0 := hc (fun _ => false)
    have h1 := hc (fun _ => true)
    rw [hfFalse] at h0; rw [hfTrue] at h1
    exact Bool.false_ne_true (h0.trans h1.symm)
  let simpG : GateOp → ℕ → List (Sum Bool ℕ) → Option Gate × Sum Bool ℕ := fun op m ins =>
    GateOp.casesOn op
      (List.casesOn ins (none, Sum.inl true) fun a t1 =>
        List.casesOn t1 (none, a) fun b t2 =>
          List.casesOn t2
            (Sum.casesOn a
              (fun ca => Bool.casesOn ca (none, Sum.inl false) (none, b))
              (fun ia => Sum.casesOn b
                (fun cb => Bool.casesOn cb (none, Sum.inl false) (none, Sum.inr ia))
                (fun ib => (some ⟨GateOp.and, [ia, ib]⟩, Sum.inr m))))
            (fun _ _ => (none, Sum.inl false)))
      (List.casesOn ins (none, Sum.inl false) fun a t1 =>
        List.casesOn t1 (none, a) fun b t2 =>
          List.casesOn t2
            (Sum.casesOn a
              (fun ca => Bool.casesOn ca (none, b) (none, Sum.inl true))
              (fun ia => Sum.casesOn b
                (fun cb => Bool.casesOn cb (none, Sum.inr ia) (none, Sum.inl true))
                (fun ib => (some ⟨GateOp.or, [ia, ib]⟩, Sum.inr m))))
            (fun _ _ => (none, Sum.inl false)))
      (List.casesOn ins (none, Sum.inl true) fun a _ =>
        Sum.casesOn a
          (fun ca => (none, Sum.inl (!ca)))
          (fun ia => (some ⟨GateOp.not, [ia]⟩, Sum.inr m)))
      (fun _ => (none, Sum.inl false))
      (none, Sum.inl false)
  let sVal : List Bool → Sum Bool ℕ → Bool := fun w s =>
    Sum.casesOn s (fun c => c) (fun j => w.getD j false)
  let sValid : ℕ → Sum Bool ℕ → Prop := fun m s =>
    Sum.casesOn s (fun _ => True) (fun j => j < m)
  let elimStep : List (Sum Bool ℕ) × List Gate → Gate → List (Sum Bool ℕ) × List Gate :=
    fun acc gt =>
      let r := simpG gt.op (8 + acc.2.length) (gt.inputs.map fun j => acc.1.getD j (Sum.inl false))
      (acc.1 ++ [r.2], acc.2 ++ r.1.toList)
  have hSimpOk : ∀ op m ins g', g' ∈ (simpG op m ins).1.toList →
      g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2 := by
    intro op m ins g' hg'
    cases op with
    | and =>
      rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
      · simp [simpG] at hg'
      · simp [simpG] at hg'
      · cases a with
        | inl x => cases x <;> (cases b with | inl y => cases y <;> simp [simpG] at hg' | inr j => simp [simpG] at hg')
        | inr i => cases b with | inl y => cases y <;> simp [simpG] at hg' | inr j => simp [simpG] at hg'; subst hg'; simp
      · simp [simpG] at hg'
    | or =>
      rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
      · simp [simpG] at hg'
      · simp [simpG] at hg'
      · cases a with
        | inl x => cases x <;> (cases b with | inl y => cases y <;> simp [simpG] at hg' | inr j => simp [simpG] at hg')
        | inr i => cases b with | inl y => cases y <;> simp [simpG] at hg' | inr j => simp [simpG] at hg'; subst hg'; simp
      · simp [simpG] at hg'
    | not =>
      rcases ins with _ | ⟨a, l⟩
      · simp [simpG] at hg'
      · cases a with
        | inl x => simp [simpG] at hg'
        | inr i => simp [simpG] at hg'; subst hg'; simp
    | mod _ => simp [simpG] at hg'
    | maj => simp [simpG] at hg'
  have hSimpSound : ∀ (op : GateOp) (w : List Bool) (ins : List (Sum Bool ℕ)),
      op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) → ins.length ≤ 2 →
      (∀ s ∈ ins, sValid w.length s) →
      sValid (w.length + (simpG op w.length ins).1.toList.length) (simpG op w.length ins).2 ∧
      sVal ((simpG op w.length ins).1.toList.foldl step w) (simpG op w.length ins).2 =
        op.eval (ins.map (sVal w)) := by
    intro op w ins hop hlen hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
      · exact ⟨trivial, rfl⟩
      · have ha := hv a List.mem_cons_self
        cases a with
        | inl c => exact ⟨trivial, (evalAnd1 c).symm⟩
        | inr j => exact ⟨by simpa [simpG, sValid] using ha, (evalAnd1 _).symm⟩
      · have ha := hv a List.mem_cons_self
        have hb := hv b (List.mem_cons_of_mem _ List.mem_cons_self)
        cases a with
        | inl c =>
          cases c with
          | false => exact ⟨trivial, by simp [simpG, sVal, evalAnd2]⟩
          | true =>
            cases b with
            | inl d => cases d <;> exact ⟨trivial, by simp [simpG, sVal, evalAnd2]⟩
            | inr j => exact ⟨by simpa [simpG, sValid] using hb, by simp [simpG, sVal, evalAnd2]⟩
        | inr i =>
          cases b with
          | inl d =>
            cases d with
            | false => exact ⟨trivial, by simp [simpG, sVal, evalAnd2]⟩
            | true => exact ⟨by simpa [simpG, sValid] using ha, by simp [simpG, sVal, evalAnd2]⟩
          | inr j =>
            refine ⟨by simp [simpG, sValid], ?_⟩
            simp only [simpG, Option.toList_some, List.foldl_cons, List.foldl_nil, step, sVal,
              List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero,
              List.map_cons, List.map_nil, evalAnd2]
      · simp at hlen
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
      · exact ⟨trivial, rfl⟩
      · have ha := hv a List.mem_cons_self
        cases a with
        | inl c => exact ⟨trivial, (evalOr1 c).symm⟩
        | inr j => exact ⟨by simpa [simpG, sValid] using ha, (evalOr1 _).symm⟩
      · have ha := hv a List.mem_cons_self
        have hb := hv b (List.mem_cons_of_mem _ List.mem_cons_self)
        cases a with
        | inl c =>
          cases c with
          | false =>
            cases b with
            | inl d => cases d <;> exact ⟨trivial, by simp [simpG, sVal, evalOr2]⟩
            | inr j => exact ⟨by simpa [simpG, sValid] using hb, by simp [simpG, sVal, evalOr2]⟩
          | true => exact ⟨trivial, by simp [simpG, sVal, evalOr2]⟩
        | inr i =>
          cases b with
          | inl d =>
            cases d with
            | false => exact ⟨by simpa [simpG, sValid] using ha, by simp [simpG, sVal, evalOr2]⟩
            | true => exact ⟨trivial, by simp [simpG, sVal, evalOr2]⟩
          | inr j =>
            refine ⟨by simp [simpG, sValid], ?_⟩
            simp only [simpG, Option.toList_some, List.foldl_cons, List.foldl_nil, step, sVal,
              List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero,
              List.map_cons, List.map_nil, evalOr2]
      · simp at hlen
    · rcases ins with _ | ⟨a, l⟩
      · exact ⟨trivial, rfl⟩
      · cases a with
        | inl c => exact ⟨trivial, by simp [simpG, sVal, evalNot1]⟩
        | inr j =>
          refine ⟨by simp [simpG, sValid], ?_⟩
          simp only [simpG, Option.toList_some, List.foldl_cons, List.foldl_nil, step, sVal,
            List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero,
            List.map_cons, List.map_nil, evalNot1]
  have hSimpDropConst : ∀ op m ins c, (op = GateOp.not → ins.length ≤ 1) →
      Sum.inl c ∈ ins → (simpG op m ins).1 = none := by
    intro op m ins c hnot hmem
    cases op with
    | and =>
      rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
      · simp at hmem
      · rfl
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl
        · cases c <;> rfl
        · cases a with
          | inl ca => cases ca <;> cases c <;> rfl
          | inr ia => cases c <;> rfl
      · rfl
    | or =>
      rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
      · simp at hmem
      · rfl
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl
        · cases c <;> rfl
        · cases a with
          | inl ca => cases ca <;> cases c <;> rfl
          | inr ia => cases c <;> rfl
      · rfl
    | not =>
      have h1 := hnot rfl
      rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩
      · simp at hmem
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        subst hmem; rfl
      · simp at h1
    | mod _ => rfl
    | maj => rfl
  let Inv : (Fin 8 → Bool) → List Bool → List (Sum Bool ℕ) × List Gate → Prop :=
    fun z w acc =>
      acc.1.length = w.length ∧
      ∀ j, sValid (8 + acc.2.length) (acc.1.getD j (Sum.inl false)) ∧
        sVal (acc.2.foldl step (List.ofFn z)) (acc.1.getD j (Sum.inl false)) = w.getD j false
  have hElimInv : ∀ (z : Fin 8 → Bool) (gs : List Gate) (w : List Bool)
      (acc : List (Sum Bool ℕ) × List Gate),
      (∀ gt ∈ gs, gt.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ gt.inputs.length ≤ 2) →
      Inv z w acc → Inv z (gs.foldl step w) (gs.foldl elimStep acc) := by
    intro z gs
    induction gs with
    | nil => intro _ _ _ h; exact h
    | cons gt gs ih =>
      intro w acc hfan hinv
      rw [List.foldl_cons, List.foldl_cons]
      apply ih (step w gt) (elimStep acc gt)
        (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg'))
      have hgt := hfan gt List.mem_cons_self
      let w' := acc.2.foldl step (List.ofFn z)
      have hw'len : w'.length = 8 + acc.2.length := by rw [foldLen, List.length_ofFn]
      let ins := gt.inputs.map (fun j => acc.1.getD j (Sum.inl false))
      have hv : ∀ s ∈ ins, sValid w'.length s := by
        intro s hs
        obtain ⟨j, _, rfl⟩ := List.mem_map.mp hs
        rw [hw'len]; exact (hinv.2 j).1
      have hsnd := hSimpSound gt.op w' ins hgt.1 (by simpa [ins] using hgt.2) hv
      have hvalEq : ins.map (sVal w') = gt.inputs.map (fun j => w.getD j false) := by
        simp only [ins, List.map_map]
        exact List.map_congr_left fun j _ => (hinv.2 j).2
      refine ⟨by simp [elimStep, step, hinv.1], ?_⟩
      intro j
      by_cases hj : j < w.length
      · have hja : j < acc.1.length := hinv.1.symm ▸ hj
        rw [List.getD_append _ _ _ _ hja, List.getD_append _ _ _ _ hj]
        have hprev := hinv.2 j
        cases hs : acc.1.getD j (Sum.inl false) with
        | inl c =>
          rw [hs] at hprev
          exact ⟨trivial, hprev.2⟩
        | inr k =>
          rw [hs] at hprev
          have hk : k < 8 + acc.2.length := hprev.1
          refine ⟨by simp [elimStep, sValid]; omega, ?_⟩
          simp only [elimStep, List.foldl_append, sVal]
          rw [foldKeep _ w' k (by omega)]
          exact hprev.2
      · by_cases hje : j = w.length
        · subst j
          have hget1 : (elimStep acc gt).1.getD w.length (Sum.inl false) = (simpG gt.op w'.length ins).2 := by
            simp only [elimStep, hw'len, ins]
            rw [← hinv.1, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
          have hget2 : (step w gt).getD w.length false = gt.op.eval (gt.inputs.map fun j => w.getD j false) := by
            simp only [step]
            rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
          rw [hget1, hget2]
          refine ⟨by simpa [elimStep, hw'len, ins, Nat.add_assoc] using hsnd.1, ?_⟩
          simp only [elimStep, List.foldl_append]
          rw [← hw'len]
          exact hsnd.2.trans (congrArg gt.op.eval hvalEq)
        · rw [List.getD_eq_default (elimStep acc gt).1 _ (by simp [elimStep, hinv.1]; omega),
            List.getD_eq_default (step w gt) _ (by simp [step]; omega)]
          exact ⟨trivial, rfl⟩
  have hElimFan : ∀ (gs : List Gate) (acc : List (Sum Bool ℕ) × List Gate),
      (∀ gt ∈ acc.2, gt.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ gt.inputs.length ≤ 2) →
      ∀ gt ∈ (gs.foldl elimStep acc).2,
        gt.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ gt.inputs.length ≤ 2 := by
    intro gs
    induction gs with
    | nil => intro _ h; exact h
    | cons gt gs ih =>
      intro acc hacc
      rw [List.foldl_cons]
      apply ih (elimStep acc gt)
      intro g' hg'
      simp only [elimStep, List.mem_append] at hg'
      rcases hg' with hg' | hg'
      · exact hacc g' hg'
      · exact hSimpOk _ _ _ g' hg'
  have hElimKeep : ∀ (gs : List Gate) (acc : List (Sum Bool ℕ) × List Gate) (j : ℕ),
      j < acc.1.length → (gs.foldl elimStep acc).1.getD j (Sum.inl false) = acc.1.getD j (Sum.inl false) := by
    intro gs
    induction gs with
    | nil => intro _ _ _; rfl
    | cons gt gs ih =>
      intro acc j hj
      rw [List.foldl_cons, ih (elimStep acc gt) j (by simp [elimStep]; omega)]
      exact List.getD_append _ _ _ _ hj
  have hElimLenLe : ∀ (gs : List Gate) (acc : List (Sum Bool ℕ) × List Gate),
      (gs.foldl elimStep acc).2.length ≤ acc.2.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro acc; simp
    | cons gt gs ih =>
      intro acc
      rw [List.foldl_cons]
      have h1 := ih (elimStep acc gt)
      have hstep : (elimStep acc gt).2.length ≤ acc.2.length + 1 := by
        have h2 : (simpG gt.op (8 + acc.2.length) (gt.inputs.map fun j => acc.1.getD j (Sum.inl false))).1.toList.length ≤ 1 := by
          cases (simpG gt.op (8 + acc.2.length) (gt.inputs.map fun j => acc.1.getD j (Sum.inl false))).1 <;> simp
        simp only [elimStep, List.length_append]
        omega
      simp only [List.length_cons]
      omega
  have hElimDropCount : ∀ (P : Gate → Bool) (gs : List Gate) (acc : List (Sum Bool ℕ) × List Gate),
      (∀ gt ∈ gs, P gt = true →
        ∃ k c, k < acc.1.length ∧ acc.1.getD k (Sum.inl false) = Sum.inl c ∧ k ∈ gt.inputs) →
      (∀ gt ∈ gs, gt.op = GateOp.not → gt.inputs.length ≤ 1) →
      (gs.foldl elimStep acc).2.length + gs.countP P ≤ acc.2.length + gs.length := by
    intro P gs
    induction gs with
    | nil => intro acc _ _; simp
    | cons gt gs ih =>
      intro acc hP hnot
      rw [List.foldl_cons]
      have htail := ih (elimStep acc gt)
        (fun g' hg' hp => by
          obtain ⟨k, c, hk, hkc, hkin⟩ := hP g' (List.mem_cons_of_mem _ hg') hp
          exact ⟨k, c, by simp [elimStep]; omega, by rw [List.getD_append _ _ _ _ hk]; exact hkc, hkin⟩)
        (fun g' hg' => hnot g' (List.mem_cons_of_mem _ hg'))
      simp only [List.countP_cons, List.length_cons]
      by_cases hp : P gt = true
      · obtain ⟨k, c, hk, hkc, hkin⟩ := hP gt List.mem_cons_self hp
        have hin : Sum.inl c ∈ gt.inputs.map (fun j => acc.1.getD j (Sum.inl false)) :=
          List.mem_map.mpr ⟨k, hkin, hkc⟩
        have hnone := hSimpDropConst gt.op (8 + acc.2.length) _ c
          (fun h => by simpa using hnot gt List.mem_cons_self h) hin
        have hstepLen : (elimStep acc gt).2.length = acc.2.length := by
          simp only [elimStep, hnone, Option.toList_none, List.append_nil]
        rw [hstepLen] at htail
        simp only [hp, ite_true]
        omega
      · have hstepLen : (elimStep acc gt).2.length ≤ acc.2.length + 1 := by
          have h2 : (simpG gt.op (8 + acc.2.length) (gt.inputs.map fun j => acc.1.getD j (Sum.inl false))).1.toList.length ≤ 1 := by
            cases (simpG gt.op (8 + acc.2.length) (gt.inputs.map fun j => acc.1.getD j (Sum.inl false))).1 <;> simp
          simp only [elimStep, List.length_append]
          omega
        have hpf : P gt = false := Bool.eq_false_iff.mpr hp
        simp only [hpf, Bool.false_eq_true, ite_false]
        omega
  let M1 : List (Sum Bool ℕ) :=
    [Sum.inl false, Sum.inr 1, Sum.inr 2, Sum.inr 3, Sum.inl false,
     Sum.inr 4, Sum.inr 5, Sum.inr 6, Sum.inr 7, Sum.inr 0, Sum.inr 8]
  let gOr03 : Gate := ⟨GateOp.or, [0, 3]⟩
  let acc1 := elimStep (M1, [gOr03]) ⟨GateOp.and, x1⟩
  have hInvM1 : ∀ z : Fin 8 → Bool, Inv z (base false z) (M1, [gOr03]) := by
    intro z
    refine ⟨rfl, ?_⟩
    intro j
    by_cases hj : j < 11
    · interval_cases j
      · exact ⟨trivial, rfl⟩
      · exact ⟨by simp [M1, sValid], by simp [M1, base, gOr03, step, sVal, List.getD_eq_getElem?_getD]⟩
      · exact ⟨by simp [M1, sValid], by simp [M1, base, gOr03, step, sVal, List.getD_eq_getElem?_getD]⟩
      · exact ⟨by simp [M1, sValid], by simp [M1, base, gOr03, step, sVal, List.getD_eq_getElem?_getD]⟩
      · exact ⟨trivial, rfl⟩
      · exact ⟨by simp [M1, sValid], by simp [M1, base, gOr03, step, sVal, List.getD_eq_getElem?_getD]⟩
      · exact ⟨by simp [M1, sValid], by simp [M1, base, gOr03, step, sVal, List.getD_eq_getElem?_getD]⟩
      · exact ⟨by simp [M1, sValid], by simp [M1, base, gOr03, step, sVal, List.getD_eq_getElem?_getD]⟩
      · exact ⟨by simp [M1, sValid], by simp [M1, base, gOr03, step, sVal, List.getD_eq_getElem?_getD]⟩
      · exact ⟨by simp [M1, sValid], by simp [M1, base, gOr03, step, sVal, List.getD_eq_getElem?_getD]⟩
      · refine ⟨by simp [M1, sValid], ?_⟩
        simp only [M1, base, gOr03, List.foldl_cons, List.foldl_nil, step, sVal,
          List.getD_cons_zero, List.getD_cons_succ, List.map_cons, List.map_nil]
        rw [List.getD_append_right _ _ _ _ (by simp), List.length_ofFn, Nat.sub_self, List.getD_cons_zero,
          evalOr2]
        simp [List.getD_eq_getElem?_getD]
    · rw [List.getD_eq_default M1 _ (by simp [M1]; omega),
        List.getD_eq_default (base false z) _ (by simp [base]; omega)]
      exact ⟨trivial, rfl⟩
  have hInv1 : ∀ z : Fin 8 → Bool, Inv z (inp false z) acc1 := by
    intro z
    have h1 := hElimInv z [⟨GateOp.and, x1⟩] (base false z) (M1, [gOr03])
      (fun gt h => by simp only [List.mem_singleton] at h; subst h; exact ⟨by simp, hx1len⟩)
      (hInvM1 z)
    simpa [acc1, inp, w11, step] using h1
  have hFan1 : ∀ gt ∈ acc1.2, gt.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ gt.inputs.length ≤ 2 := by
    have h1 := hElimFan [⟨GateOp.and, x1⟩] (M1, [gOr03])
      (fun gt h => by simp only [List.mem_singleton] at h; subst h; exact ⟨by simp [gOr03], by simp [gOr03]⟩)
    simpa [acc1] using h1
  have hNoSize12 : ∀ acc, acc = D.gates.foldl elimStep acc1 → acc.2.length ≤ 12 → False := by
    intro acc hacc hlen
    have hinv : ∀ z, Inv z (D.gates.foldl step (inp false z)) acc := by
      intro z; rw [hacc]; exact hElimInv z D.gates (inp false z) acc1 hfanD (hInv1 z)
    have hfanAcc : ∀ gt ∈ acc.2, gt.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ gt.inputs.length ≤ 2 := by
      rw [hacc]; exact hElimFan D.gates acc1 hFan1
    cases hout : acc.1.getD D.output (Sum.inl false) with
    | inl c =>
      apply hNonConstF c
      intro z
      have h1 := (hinv z).2 D.output
      rw [hout] at h1
      have h2 := hDeval false z
      change (D.gates.foldl step (inp false z)).getD D.output false = f z at h2
      rw [← h2]
      exact h1.2.symm
    | inr out' =>
      apply cofactor
      refine ⟨⟨acc.2, out'⟩, hfanAcc, hlen, ?_⟩
      intro z
      have h1 := (hinv z).2 D.output
      rw [hout] at h1
      change (acc.2.foldl step (List.ofFn z)).getD out' false = f z
      have h2 := hDeval false z
      change (D.gates.foldl step (inp false z)).getD D.output false = f z at h2
      rw [← h2]
      exact h1.2
  -- Witness pair u (x3=1, x4=1, x0=0) vs v (x0=1, x3=1, x4=0) agreeing on all base wires except wire 4!
  let zu : Fin 8 → Bool := ![false, false, false, true, false, false, false, false]
  let zv : Fin 8 → Bool := ![true, false, false, true, false, false, false, false]
  have hgu : g zu = true := by decide
  have hfv : f zv = false := by decide
  have hbaseUV : base true zu = (base false zv).set 4 true := by decide
  have houtNe4 : D.output ≠ 4 := by
    intro h4
    have h1 := hDeval false (fun _ => true)
    change (D.gates.foldl step (inp false (fun _ => true))).getD D.output false = f (fun _ => true) at h1
    rw [h4, foldKeep _ _ 4 (by simp [inp, base]), hfTrue] at h1
    exact Bool.false_ne_true h1
  by_cases h4in : 4 ∈ x1
  · have hacc1Len : acc1.2.length = 1 := by
      have hin : Sum.inl false ∈ x1.map (fun j => M1.getD j (Sum.inl false)) :=
        List.mem_map.mpr ⟨4, h4in, rfl⟩
      have hnone := hSimpDropConst GateOp.and (8 + ([gOr03] : List Gate).length) _ false (by simp) hin
      change ([gOr03] ++ (simpG GateOp.and (8 + ([gOr03] : List Gate).length)
        (x1.map fun j => M1.getD j (Sum.inl false))).1.toList).length = 1
      rw [hnone]; rfl
    have hacc1_11 : acc1.1.getD 11 (Sum.inl false) = Sum.inl false := by
      have hlenM1 : M1.length = 11 := rfl
      have hget : acc1.1.getD 11 (Sum.inl false) =
          (simpG GateOp.and (8 + ([gOr03] : List Gate).length) (x1.map fun j => M1.getD j (Sum.inl false))).2 := by
        simp only [acc1, elimStep]
        rw [← hlenM1, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
      rw [hget]
      rcases hx1 : x1 with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
      · rw [hx1] at h4in; simp at h4in
      · rw [hx1] at h4in; simp only [List.mem_singleton] at h4in; subst h4in; rfl
      · rw [hx1] at h4in; simp only [List.mem_cons, List.not_mem_nil, or_false] at h4in
        rw [List.map_cons, List.map_cons, List.map_nil]
        rcases h4in with rfl | rfl
        · rfl
        · cases M1.getD a (Sum.inl false) with
          | inl ca => cases ca <;> rfl
          | inr _ => rfl
      · rw [hx1] at hx1len; simp at hx1len
    have hacc1_4 : acc1.1.getD 4 (Sum.inl false) = Sum.inl false := by
      simp only [acc1, elimStep]
      rw [List.getD_append _ _ _ _ (by simp [M1])]
      rfl
    let uses411 : Gate → Bool := fun gt => gt.inputs.contains 4 || gt.inputs.contains 11
    by_cases hcnt0 : D.gates.countP uses411 = 0
    · have hno4 : ∀ gt ∈ D.gates, 4 ∉ gt.inputs := fun gt hgt hm => by
        have hp : 0 < D.gates.countP uses411 := List.countP_pos_iff.mpr ⟨gt, hgt, by simp [uses411, hm]⟩
        omega
      have hno11 : ∀ gt ∈ D.gates, 11 ∉ gt.inputs := fun gt hgt hm => by
        have hp : 0 < D.gates.countP uses411 := List.countP_pos_iff.mpr ⟨gt, hgt, by simp [uses411, hm]⟩
        omega
      by_cases hout11 : D.output = 11
      · apply hNonConstF false
        intro z
        have h1 := (hInv1 z).2 11
        have hw11f : w11 false z = false := by
          have h2 : (inp false z).getD 11 false = w11 false z := by
            simp only [inp]; rw [show (11 : ℕ) = (base false z).length from rfl,
              List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
          rw [hacc1_11, h2] at h1
          exact h1.2.symm
        have h2 := hDeval false z
        change (D.gates.foldl step (inp false z)).getD D.output false = f z at h2
        rw [hout11, foldKeep _ _ 11 (by simp [inp, base])] at h2
        have h3 : (inp false z).getD 11 false = false := by
          simp only [inp]; rw [show (11 : ℕ) = (base false z).length from rfl,
            List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]; exact hw11f
        rw [h3] at h2
        exact h2.symm
      · have hinpUV : inp true zu = ((inp false zv).set 4 true).set 11 (w11 true zu) := by
          simp only [inp, hbaseUV]
          rw [List.set_append_left _ _ (by simp [base]),
            List.set_append_right _ _ (by simp [base])]
          simp [base]
        have heq : D.gates.foldl step (inp true zu) =
            ((D.gates.foldl step (inp false zv)).set 4 true).set 11 (w11 true zu) := by
          rw [hinpUV, foldSetComm 11 _ D.gates _ hno11 (by simp [inp, base]),
            foldSetComm 4 true D.gates _ hno4 (by simp [inp, base])]
        have hout : D.eval (inp true zu) = D.eval (inp false zv) := by
          change (D.gates.foldl step (inp true zu)).getD D.output false =
            (D.gates.foldl step (inp false zv)).getD D.output false
          rw [heq]
          simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hout11),
            List.getElem?_set_ne (Ne.symm houtNe4)]
        rw [hDeval true zu, hDeval false zv] at hout
        simp only [ite_true, Bool.false_eq_true, ite_false, hgu, hfv] at hout
        exact Bool.false_ne_true hout.symm
    · have hdrop := hElimDropCount uses411 D.gates acc1
        (fun gt _ hp => by
          simp only [uses411, Bool.or_eq_true, List.contains_iff_mem] at hp
          rcases hp with h4 | h11
          · exact ⟨4, false, by simp [acc1, elimStep, M1], hacc1_4, h4⟩
          · exact ⟨11, false, by simp [acc1, elimStep, M1], hacc1_11, h11⟩)
        hnotLen
      have hlen : (D.gates.foldl elimStep acc1).2.length ≤ 12 := by
        change D.gates.length ≤ 12 at hszD
        omega
      exact hNoSize12 _ rfl hlen
  -- Now 4 ∉ x1!
  have hw11UV : w11 true zu = w11 false zv := by
    simp only [w11]
    congr 1
    apply List.map_congr_left
    intro j hj
    have hj4 : j ≠ 4 := fun h => h4in (h ▸ hj)
    rw [hbaseUV]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hj4)]
  have hinpUV : inp true zu = (inp false zv).set 4 true := by
    simp only [inp, hbaseUV, hw11UV]
    rw [List.set_append_left _ _ (by simp [base])]
  have hacc1LenLe : acc1.2.length ≤ 2 := by
    have := hElimLenLe [⟨GateOp.and, x1⟩] (M1, [gOr03])
    simpa [acc1] using this
  have hacc1_4 : acc1.1.getD 4 (Sum.inl false) = Sum.inl false := by
    simp only [acc1, elimStep]
    rw [List.getD_append _ _ _ _ (by simp [M1])]
    rfl
  let uses4 : Gate → Bool := fun gt => gt.inputs.contains 4
  let cnt4 := D.gates.countP uses4
  by_cases hcnt0 : cnt4 = 0
  · have hno4 : ∀ gt ∈ D.gates, 4 ∉ gt.inputs := fun gt hgt hm => by
      have hp : 0 < cnt4 := List.countP_pos_iff.mpr ⟨gt, hgt, List.contains_iff_mem.mpr hm⟩
      omega
    have heq : D.gates.foldl step (inp true zu) = (D.gates.foldl step (inp false zv)).set 4 true := by
      rw [hinpUV, foldSetComm 4 true D.gates _ hno4 (by simp [inp, base])]
    have hout : D.eval (inp true zu) = D.eval (inp false zv) := by
      change (D.gates.foldl step (inp true zu)).getD D.output false =
        (D.gates.foldl step (inp false zv)).getD D.output false
      rw [heq]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm houtNe4)]
    rw [hDeval true zu, hDeval false zv] at hout
    simp only [ite_true, Bool.false_eq_true, ite_false, hgu, hfv] at hout
    exact Bool.false_ne_true hout.symm
  by_cases hcnt2 : 2 ≤ cnt4
  · have hdrop := hElimDropCount uses4 D.gates acc1
      (fun gt _ hp => ⟨4, false, by simp [acc1, elimStep, M1], hacc1_4, List.contains_iff_mem.mp hp⟩)
      hnotLen
    have hlen : (D.gates.foldl elimStep acc1).2.length ≤ 12 := by
      change D.gates.length ≤ 12 at hszD
      omega
    exact hNoSize12 _ rfl hlen
  have hcnt1 : cnt4 = 1 := by omega
  have hsplit1 : ∀ gs : List Gate, gs.countP uses4 = 1 →
      ∃ a b h, gs = a ++ [h] ++ b ∧ (∀ g' ∈ a, 4 ∉ g'.inputs) ∧ 4 ∈ h.inputs ∧ (∀ g' ∈ b, 4 ∉ g'.inputs) := by
    intro gs
    induction gs with
    | nil => intro h; simp at h
    | cons gt gs ih =>
      intro hcnt
      simp only [List.countP_cons] at hcnt
      by_cases h4 : uses4 gt = true
      · simp only [h4, ite_true] at hcnt
        have h0 : gs.countP uses4 = 0 := by omega
        have hall : ∀ g' ∈ gs, 4 ∉ g'.inputs := fun g' hg' hm => by
          have hp : 0 < gs.countP uses4 := List.countP_pos_iff.mpr ⟨g', hg', List.contains_iff_mem.mpr hm⟩
          omega
        exact ⟨[], gs, gt, by simp, by simp, List.contains_iff_mem.mp h4, hall⟩
      · have h4f : uses4 gt = false := Bool.eq_false_iff.mpr h4
        simp only [h4f, Bool.false_eq_true, ite_false] at hcnt
        obtain ⟨a, b, h, rfl, ha, hh, hb⟩ := ih hcnt
        refine ⟨gt :: a, b, h, by simp, ?_, hh, hb⟩
        intro g' hg'
        simp only [List.mem_cons] at hg'
        rcases hg' with rfl | hg'
        · exact fun hm => h4 (List.contains_iff_mem.mpr hm)
        · exact ha g' hg'
  obtain ⟨gsA, gsB, hgate, hDsplit, hnoA, h4inH, hnoB⟩ := hsplit1 D.gates hcnt1
  have hfanA : ∀ g' ∈ gsA, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
    fun g' hg' => hfanD g' (by rw [hDsplit]; simp [hg'])
  have hfanB : ∀ g' ∈ gsB, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
    fun g' hg' => hfanD g' (by rw [hDsplit]; simp [hg'])
  have hfanH := hfanD hgate (by rw [hDsplit]; simp)
  have hnotB : ∀ g' ∈ gsB, g'.op = GateOp.not → g'.inputs.length ≤ 1 :=
    fun g' hg' => hnotLen g' (by rw [hDsplit]; simp [hg'])
  have hnotH : hgate.op = GateOp.not → hgate.inputs.length ≤ 1 :=
    hnotLen hgate (by rw [hDsplit]; simp)
  let accA := gsA.foldl elimStep acc1
  let accH := elimStep accA hgate
  let hwire := 12 + gsA.length
  have hAccAlen : accA.1.length = hwire := by
    have h1 := (hElimInv (fun _ => false) gsA (inp false (fun _ => false)) acc1 hfanA (hInv1 _)).1
    rw [foldLen] at h1
    simpa [hwire, inp, base] using h1
  have h4val : accA.1.getD 4 (Sum.inl false) = Sum.inl false := by
    rw [hElimKeep gsA acc1 4 (by simp [acc1, elimStep, M1]), hacc1_4]
  have hHdrop : accH.2.length = accA.2.length := by
    have hin : Sum.inl false ∈ hgate.inputs.map (fun j => accA.1.getD j (Sum.inl false)) :=
      List.mem_map.mpr ⟨4, h4inH, h4val⟩
    have hnone := hSimpDropConst hgate.op (8 + accA.2.length) _ false (fun h => by simpa using hnotH h) hin
    simp only [accH, elimStep, hnone, Option.toList_none, List.append_nil]
  have hAccALenLe : accA.2.length ≤ acc1.2.length + gsA.length := hElimLenLe gsA acc1
  cases hr : accH.1.getD hwire (Sum.inl false) with
  | inl c =>
    let usesH : Gate → Bool := fun gt => gt.inputs.contains hwire
    by_cases hused : 1 ≤ gsB.countP usesH
    · have hdropB := hElimDropCount usesH gsB accH
        (fun gt _ hp => ⟨hwire, c, by simp [accH, elimStep, hAccAlen], hr, List.contains_iff_mem.mp hp⟩)
        hnotB
      have hFull : (D.gates.foldl elimStep acc1).2.length ≤ 12 := by
        rw [hDsplit, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
        change (gsB.foldl elimStep accH).2.length ≤ 12
        change D.gates.length ≤ 12 at hszD
        rw [hDsplit] at hszD
        simp only [List.length_append, List.length_singleton] at hszD
        omega
      exact hNoSize12 _ rfl hFull
    · have hnoH : ∀ gt ∈ gsB, hwire ∉ gt.inputs := fun gt hgt hm => by
        have hp : 0 < gsB.countP usesH := List.countP_pos_iff.mpr ⟨gt, hgt, List.contains_iff_mem.mpr hm⟩
        omega
      by_cases houtH : D.output = hwire
      · apply hNonConstF c
        intro z
        have hinv := hElimInv z D.gates (inp false z) acc1 hfanD (hInv1 z)
        have hkeepH : (D.gates.foldl elimStep acc1).1.getD hwire (Sum.inl false) = Sum.inl c := by
          rw [hDsplit, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
          rw [hElimKeep gsB accH hwire (by simp [accH, elimStep, hAccAlen]), hr]
        have h1 := (hinv.2 hwire).2
        rw [hkeepH] at h1
        have h2 := hDeval false z
        change (D.gates.foldl step (inp false z)).getD D.output false = f z at h2
        rw [houtH] at h2
        rw [← h2]
        exact h1.symm
      · have hAeq : gsA.foldl step (inp true zu) = (gsA.foldl step (inp false zv)).set 4 true := by
          rw [hinpUV, foldSetComm 4 true gsA _ hnoA (by simp [inp, base])]
        have hAfLen : (gsA.foldl step (inp false zv)).length = hwire := by
          rw [foldLen]; simp [inp, base, hwire]
        let wt := step (gsA.foldl step (inp true zu)) hgate
        let wf := step (gsA.foldl step (inp false zv)) hgate
        have hwfLen : wf.length = hwire + 1 := by
          change ((gsA.foldl step (inp false zv)) ++ [_]).length = hwire + 1
          rw [List.length_append, hAfLen, List.length_singleton]
        have hwtEq : wt = (wf.set 4 true).set hwire (wt.getD hwire false) := by
          have hwtv : wt.getD hwire false = hgate.op.eval (hgate.inputs.map fun j => (gsA.foldl step (inp true zu)).getD j false) := by
            have hAtLen : (gsA.foldl step (inp true zu)).length = hwire := by rw [foldLen]; simp [inp, base, hwire]
            change ((gsA.foldl step (inp true zu)) ++ [_]).getD hwire false = _
            rw [← hAtLen, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
          rw [hwtv]
          change (gsA.foldl step (inp true zu)) ++ [_] =
            (((gsA.foldl step (inp false zv)) ++ [_]).set 4 true).set hwire _
          rw [List.set_append_left _ _ (by rw [hAfLen]; dsimp only [hwire]; omega),
            List.set_append_right _ _ (by rw [List.length_set, hAfLen]),
            List.length_set, hAfLen, Nat.sub_self, List.set_cons_zero, hAeq]
        have hBeq : gsB.foldl step wt = ((gsB.foldl step wf).set 4 true).set hwire (wt.getD hwire false) := by
          conv_lhs => rw [hwtEq]
          rw [foldSetComm hwire _ gsB _ hnoH (by rw [List.length_set, hwfLen]; omega),
            foldSetComm 4 true gsB _ hnoB (by rw [hwfLen]; omega)]
        have hout : D.eval (inp true zu) = D.eval (inp false zv) := by
          change (D.gates.foldl step (inp true zu)).getD D.output false =
            (D.gates.foldl step (inp false zv)).getD D.output false
          rw [hDsplit, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil,
            List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
          change (gsB.foldl step wt).getD D.output false = (gsB.foldl step wf).getD D.output false
          rw [hBeq]
          simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm houtH),
            List.getElem?_set_ne (Ne.symm houtNe4)]
        rw [hDeval true zu, hDeval false zv] at hout
        simp only [ite_true, Bool.false_eq_true, ite_false, hgu, hfv] at hout
        exact Bool.false_ne_true hout.symm
  | inr idx =>
    have hOrPair : hgate.op = GateOp.or ∧ ∃ k, k ≠ 4 ∧ (hgate.inputs = [4, k] ∨ hgate.inputs = [k, 4]) := by
      have hreq : (simpG hgate.op (8 + accA.2.length) (hgate.inputs.map fun j => accA.1.getD j (Sum.inl false))).2 = Sum.inr idx := by
        have hget : accH.1.getD hwire (Sum.inl false) =
            (simpG hgate.op (8 + accA.2.length) (hgate.inputs.map fun j => accA.1.getD j (Sum.inl false))).2 := by
          simp only [accH, elimStep]
          rw [← hAccAlen, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
        rw [← hget, hr]
      have hop := hfanH.1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      rcases hop with hop | hop | hop
      · exfalso
        rcases hgi : hgate.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
        · simp [hgi] at h4inH
        · simp [hgi] at h4inH; subst a
          rw [hop, hgi] at hreq; simp only [List.map_cons, List.map_nil, h4val, simpG] at hreq; cases hreq
        · rw [hgi] at h4inH; simp only [List.mem_cons, List.not_mem_nil, or_false] at h4inH
          rcases h4inH with rfl | rfl
          · rw [hop, hgi, List.map_cons, List.map_cons, List.map_nil, h4val] at hreq; simp [simpG] at hreq
          · rw [hop, hgi, List.map_cons, List.map_cons, List.map_nil, h4val] at hreq
            cases hga : accA.1.getD a (Sum.inl false) with
            | inl b1 => rw [hga] at hreq; cases b1 <;> simp [simpG] at hreq
            | inr i1 => rw [hga] at hreq; simp [simpG] at hreq
        · have hl := hfanH.2; rw [hgi] at hl; simp at hl
      · refine ⟨hop, ?_⟩
        rcases hgi : hgate.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
        · simp [hgi] at h4inH
        · simp [hgi] at h4inH; subst a
          rw [hop, hgi] at hreq; simp only [List.map_cons, List.map_nil, h4val, simpG] at hreq; cases hreq
        · rw [hgi] at h4inH; simp only [List.mem_cons, List.not_mem_nil, or_false] at h4inH
          rcases h4inH with rfl | rfl
          · have hne : b ≠ 4 := by
              rintro rfl
              rw [hop, hgi, List.map_cons, List.map_cons, List.map_nil, h4val] at hreq; simp [simpG] at hreq
            exact ⟨b, hne, Or.inl rfl⟩
          · have hne : a ≠ 4 := by
              rintro rfl
              rw [hop, hgi, List.map_cons, List.map_cons, List.map_nil, h4val] at hreq; simp [simpG] at hreq
            exact ⟨a, hne, Or.inr rfl⟩
        · have hl := hfanH.2; rw [hgi] at hl; simp at hl
      · exfalso
        have h1 := hnotH hop
        rcases hgi : hgate.inputs with _ | ⟨a, _ | ⟨b, l⟩⟩
        · simp [hgi] at h4inH
        · simp [hgi] at h4inH; subst a
          rw [hop, hgi, List.map_cons, List.map_nil, h4val] at hreq; simp [simpG] at hreq
        · simp [hgi] at h1
    obtain ⟨hopOr, k, hk4, hkins⟩ := hOrPair
    let σ : ℕ → ℕ := fun j => if j < 4 then j else j - 1
    let gAnd : Gate := ⟨GateOp.and, x1.map σ⟩
    let A : Circuit := ⟨gAnd :: gsA.map (mapGate σ), 0⟩
    let B : Circuit := ⟨gsB.map (mapGate σ), σ D.output⟩
    have hfanA' : FanInTwo A := by
      intro g' hg'
      simp only [A, List.mem_cons, List.mem_map] at hg'
      rcases hg' with rfl | ⟨g0, hg0, rfl⟩
      · exact ⟨by simp [gAnd], by simpa [gAnd] using hx1len⟩
      · have h0 := hfanA g0 hg0; exact ⟨h0.1, by simpa [mapGate] using h0.2⟩
    have hfanB' : FanInTwo B := by
      intro g' hg'
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg'
      have h0 := hfanB g0 hg0; exact ⟨h0.1, by simpa [mapGate] using h0.2⟩
    have hszAB : A.size + B.size ≤ 12 := by
      change (gAnd :: gsA.map (mapGate σ)).length + (gsB.map (mapGate σ)).length ≤ 12
      simp only [List.length_cons, List.length_map]
      change D.gates.length ≤ 12 at hszD
      rw [hDsplit] at hszD
      simp only [List.length_append, List.length_singleton] at hszD
      omega
    have hAand : ∃ gt ∈ A.gates.take 1, gt.op = GateOp.and := ⟨gAnd, by simp [A], rfl⟩
    have hSigmaRel : ∀ (gs : List Gate) (wa wb : List Bool),
        (∀ gt ∈ gs, 4 ∉ gt.inputs) →
        5 ≤ wa.length → wa.length = wb.length + 1 →
        (∀ j, j ≠ 4 → wb.getD (σ j) false = wa.getD j false) →
        ∀ j, j ≠ 4 → ((gs.map (mapGate σ)).foldl step wb).getD (σ j) false = (gs.foldl step wa).getD j false := by
      intro gs
      induction gs with
      | nil => intro _ _ _ _ _ hr j hj; exact hr j hj
      | cons gt gs ih =>
        intro wa wb hno hwa hlen hr
        have hg4 : 4 ∉ gt.inputs := hno gt List.mem_cons_self
        have hvals : (mapGate σ gt).inputs.map (fun j => wb.getD j false) =
            gt.inputs.map (fun j => wa.getD j false) := by
          rw [List.map_map]
          exact List.map_congr_left fun j hj => hr j (fun he => hg4 (he ▸ hj))
        rw [List.map_cons, List.foldl_cons, List.foldl_cons]
        apply ih (step wa gt) (step wb (mapGate σ gt))
          (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
          (by simp [step]; omega) (by simp [step, hlen])
        intro j hj
        by_cases hjlt : j < wa.length
        · have hsj : σ j < wb.length := by simp only [σ]; split_ifs <;> omega
          unfold step
          rw [List.getD_append _ _ _ _ hsj, List.getD_append _ _ _ _ hjlt]
          exact hr j hj
        · by_cases hje : j = wa.length
          · subst j
            have hsj : σ wa.length = wb.length := by
              simp only [σ, show ¬ wa.length < 4 by omega, ite_false]; omega
            unfold step
            rw [hsj, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero,
              List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
            change gt.op.eval ((mapGate σ gt).inputs.map fun j => wb.getD j false) = _
            rw [hvals]
          · have hsj : wb.length + 1 ≤ σ j := by
              simp only [σ, show ¬ j < 4 by omega, ite_false]; omega
            rw [List.getD_eq_default _ _ (by simp [step]; omega),
              List.getD_eq_default _ _ (by simp [step]; omega)]
    have hBaseMatch : ∀ (b : Bool) (z : Fin 8 → Bool) (j : ℕ), j ≠ 4 →
        (List.ofFn (Function.update z 0 false) ++ [z 0 || b, z 0 || z 3]).getD (σ j) false =
          (base b z).getD j false := by
      intro b z j hj
      by_cases h11 : j < 11
      · interval_cases j
        all_goals first | exact (hj rfl).elim | simp [σ, base, List.getD_eq_getElem?_getD]
      · rw [List.getD_eq_default _ _ (by simp [σ, show ¬ j < 4 by omega]; omega),
          List.getD_eq_default (base b z) _ (by simp [base]; omega)]
    have hABeval : ∀ (b : Bool) (z : Fin 8 → Bool),
        let wb := A.wires (List.ofFn (Function.update z 0 false) ++ [z 0 || b, z 0 || z 3])
        B.eval (wb ++ [if b then true else wb.getD (σ k) false]) = if b then g z else f z := by
      intro b z
      dsimp only
      let b8 := List.ofFn (Function.update z 0 false) ++ [z 0 || b, z 0 || z 3]
      have hb8len : b8.length = 10 := by simp [b8]
      have hStep0Rel : ∀ j, j ≠ 4 → (step b8 gAnd).getD (σ j) false = (inp b z).getD j false := by
        intro j hj
        by_cases hjlt : j < 11
        · have hsj : σ j < 10 := by simp only [σ]; split_ifs <;> omega
          unfold step
          rw [List.getD_append b8 _ _ _ (by rw [hb8len]; exact hsj)]
          change b8.getD (σ j) false = (base b z ++ [w11 b z]).getD j false
          rw [List.getD_append (base b z) _ _ _ (by simp [base]; exact hjlt)]
          exact hBaseMatch b z j hj
        · by_cases hje : j = 11
          · subst j
            have hsj : σ 11 = 10 := rfl
            unfold step
            rw [hsj, ← hb8len, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
            simp only [inp]
            rw [show (11 : ℕ) = (base b z).length from rfl,
              List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
            change GateOp.and.eval ((x1.map σ).map fun j => b8.getD j false) = w11 b z
            simp only [w11, List.map_map]
            congr 1
            exact List.map_congr_left fun i hi => hBaseMatch b z i (fun h => h4in (h ▸ hi))
          · have hsj : 11 ≤ σ j := by simp only [σ, show ¬ j < 4 by omega, ite_false]; omega
            rw [List.getD_eq_default _ _ (by simp [step, hb8len]; omega),
              List.getD_eq_default _ _ (by simp [inp, base]; omega)]
      let wa := gsA.foldl step (inp b z)
      let wb := A.wires b8
      have hwbEq : wb = (gsA.map (mapGate σ)).foldl step (step b8 gAnd) := rfl
      have hwaLen : wa.length = 12 + gsA.length := by simp [wa, foldLen, inp, base]
      have hwbLen : wb.length = 11 + gsA.length := by
        rw [hwbEq, foldLen]; simp [step, hb8len]
      have hArel : ∀ j, j ≠ 4 → wb.getD (σ j) false = wa.getD j false := by
        rw [hwbEq]
        exact hSigmaRel gsA (inp b z) (step b8 gAnd) hnoA (by simp [inp, base])
          (by simp [inp, base, step, hb8len]) hStep0Rel
      have h4wa : wa.getD 4 false = b := by
        rw [foldKeep gsA (inp b z) 4 (by simp [inp, base])]; rfl
      have hgateVal : hgate.op.eval (hgate.inputs.map fun j => wa.getD j false) =
          if b then true else wb.getD (σ k) false := by
        rw [hopOr]
        rcases hkins with hk1 | hk2
        · rw [hk1, List.map_cons, List.map_cons, List.map_nil, evalOr2, h4wa, ← hArel k hk4]
          cases b <;> simp
        · rw [hk2, List.map_cons, List.map_cons, List.map_nil, evalOr2, h4wa, ← hArel k hk4]
          cases b <;> simp
      have hstepRel : ∀ j, j ≠ 4 →
          (wb ++ [if b then true else wb.getD (σ k) false]).getD (σ j) false = (step wa hgate).getD j false := by
        intro j hj
        by_cases hjlt : j < wa.length
        · have hsj : σ j < wb.length := by simp only [σ]; split_ifs <;> omega
          unfold step
          rw [List.getD_append _ _ _ _ hsj, List.getD_append _ _ _ _ hjlt]
          exact hArel j hj
        · by_cases hje : j = wa.length
          · subst j
            have hsj : σ wa.length = wb.length := by
              simp only [σ, show ¬ wa.length < 4 by omega, ite_false]; omega
            unfold step
            rw [hsj, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero,
              List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero, hgateVal]
          · have hsj : wb.length + 1 ≤ σ j := by
              simp only [σ, show ¬ j < 4 by omega, ite_false]; omega
            rw [List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp [step]; omega)]
      have hBrel := hSigmaRel gsB (step wa hgate) (wb ++ [if b then true else wb.getD (σ k) false])
        hnoB (by simp [step, hwaLen]; omega) (by simp [step, hwaLen, hwbLen]; omega) hstepRel D.output houtNe4
      have hDcomb : (gsB.foldl step (step wa hgate)).getD D.output false = D.eval (inp b z) := by
        change _ = (D.gates.foldl step (inp b z)).getD D.output false
        rw [hDsplit, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact hBrel.trans (hDcomb.trans (hDeval b z))
    obtain ⟨zm, hzm⟩ := marked A B (σ k) hfanA' hfanB' hszAB hAand (fun z => by simpa using hABeval false z)
    exact hzm (by simpa using hABeval true zm)
