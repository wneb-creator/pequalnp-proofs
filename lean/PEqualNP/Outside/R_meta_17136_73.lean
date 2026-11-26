import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17136_73
  (h0 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (10 : ℕ) x1 → PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 = PEqualNP.MetaComplexity.NestedCover.graphFun (PEqualNP.EdgeOwnership.edgeGraph (10 : ℕ) [(0, 3), (0, 7), (1, 4), (1, 9), (2, 5), (2, 6), (3, 7), (3, 9), (4, 7), (4, 8), (5, 6), (5, 9), (6, 8), (7, 8)]) ∅ → (13 : ℕ) ≤ List.countP (fun (x2 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.true Bool.false (fun (x3 : ℕ) => Bool.false) Bool.false x2.op) x1.gates)
  (h1 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (10 : ℕ) x1 → PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 = PEqualNP.MetaComplexity.NestedCover.graphFun (PEqualNP.EdgeOwnership.edgeGraph (10 : ℕ) [(0, 8), (0, 9), (1, 4), (1, 9), (2, 5), (2, 6), (3, 7), (3, 9), (4, 7), (4, 8), (5, 6), (5, 9), (6, 8), (7, 8)]) ∅ → (13 : ℕ) ≤ List.countP (fun (x2 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.true Bool.false (fun (x3 : ℕ) => Bool.false) Bool.false x2.op) x1.gates)
  (h2 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (10 : ℕ) x1 → PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 = PEqualNP.MetaComplexity.NestedCover.graphFun (PEqualNP.EdgeOwnership.edgeGraph (10 : ℕ) [(0, 8), (0, 9), (1, 3), (1, 7), (2, 5), (2, 6), (3, 7), (3, 9), (4, 7), (4, 8), (5, 6), (5, 9), (6, 8), (7, 8)]) ∅ → (13 : ℕ) ≤ List.countP (fun (x2 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.true Bool.false (fun (x3 : ℕ) => Bool.false) Bool.false x2.op) x1.gates)
  (h3 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (10 : ℕ) x1 → PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 = PEqualNP.MetaComplexity.NestedCover.graphFun (PEqualNP.EdgeOwnership.edgeGraph (10 : ℕ) [(0, 8), (0, 9), (1, 3), (1, 7), (2, 4), (2, 9), (3, 7), (3, 9), (4, 7), (4, 8), (5, 6), (5, 9), (6, 8), (7, 8)]) ∅ → (13 : ℕ) ≤ List.countP (fun (x2 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.true Bool.false (fun (x3 : ℕ) => Bool.false) Bool.false x2.op) x1.gates) :
  (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : Fin (11 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), ↑x2 < (4 : ℕ) → PEqualNP.TopForm.IsAO2 (11 : ℕ) x3 → (∀ (x6 : Fin (11 : ℕ) → Bool), x6 x2 = Bool.false → PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x3 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x1 ∅ x6) → (13 : ℕ) ≤ List.countP (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.true Bool.false (fun (x8 : ℕ) => Bool.false) Bool.false x7.op) x3.gates) := by
  intro G11 v C hv hAO hagree
  let isOr : PEqualNP.CircuitLowerBounds.Gate → Bool := fun g =>
    PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.true Bool.false (fun _ => Bool.false) Bool.false g.op
  let bstep : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let step : List PEqualNP.CircuitLowerBounds.Gate × List (Option ℕ) → PEqualNP.CircuitLowerBounds.Gate →
      List PEqualNP.CircuitLowerBounds.Gate × List (Option ℕ) := fun st g =>
    let ds := st.1
    let mp := st.2
    let ma := mp.getD (g.inputs.getD 0 0) none
    let mb := mp.getD (g.inputs.getD 1 0) none
    PEqualNP.CircuitLowerBounds.GateOp.rec
      (Option.rec (ds, mp ++ [none])
        (fun ka => Option.rec (ds, mp ++ [none])
          (fun kb => (ds ++ [PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.and [ka, kb]], mp ++ [some (10 + ds.length)]))
          mb)
        ma)
      (Option.rec
        (Option.rec (ds, mp ++ [none]) (fun kb => (ds, mp ++ [some kb])) mb)
        (fun ka => Option.rec (ds, mp ++ [some ka])
          (fun kb => (ds ++ [PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [ka, kb]], mp ++ [some (10 + ds.length)]))
          mb)
        ma)
      (ds, mp ++ [none])
      (fun _ => (ds, mp ++ [none]))
      (ds, mp ++ [none])
      g.op
  have bstep_len : ∀ (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate), (bstep w g).length = w.length + 1 := by
    intro w g; simp [bstep]
  have wires_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      (gs.foldl bstep w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih (bstep w g), bstep_len, List.length_cons, Nat.add_assoc, Nat.add_comm 1 gs.length]
  have step_mp : ∀ (mp0 : List (Option ℕ)) (v0 : Option ℕ) (n0 : ℕ),
      (∀ i k, mp0.getD i none = some k → k < n0) →
      (∀ k, v0 = some k → k < n0) →
      ∀ i k, (mp0 ++ [v0]).getD i none = some k → k < n0 := by
    intro mp0 v0 n0 h0 hv0 i k hi
    rcases Nat.lt_trichotomy i mp0.length with hlt | heq | hgt
    · rw [List.getD_append _ _ _ _ hlt] at hi; exact h0 i k hi
    · subst heq; rw [List.getD_append_right _ _ _ _ (Nat.le_refl _)] at hi
      simp only [Nat.sub_self, List.getD_cons_zero] at hi
      exact hv0 k hi
    · rw [List.getD_eq_default _ _ (by simp; exact Nat.succ_le_of_lt hgt)] at hi
      cases hi
  have step_inv : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate)
      (ds : List PEqualNP.CircuitLowerBounds.Gate) (mp : List (Option ℕ)),
      (∀ g ∈ gs, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) →
      (∀ i k, mp.getD i none = some k → k < 10 + ds.length) →
      PEqualNP.TopForm.IsAO2 10 ⟨ds, 0⟩ →
      let res := gs.foldl step (ds, mp)
      (∀ i k, res.2.getD i none = some k → k < 10 + res.1.length) ∧
      PEqualNP.TopForm.IsAO2 10 ⟨res.1, 0⟩ ∧
      res.1.countP isOr ≤ ds.countP isOr + gs.countP isOr := by
    intro gs
    induction gs with
    | nil =>
      intro ds mp _ hmp hao
      exact ⟨hmp, hao, Nat.le_add_right _ _⟩
    | cons g gs ih =>
      intro ds mp hgs hmp hao
      have hg := hgs g (List.mem_cons_self ..)
      have htail : ∀ g' ∈ gs, (g'.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g'.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g'.inputs.length = 2 :=
        fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')
      rw [List.foldl_cons]
      have hcount_cons : (g :: gs).countP isOr = gs.countP isOr + cond (isOr g) 1 0 := by
        rw [List.countP_cons]; cases isOr g <;> rfl
      have push_ao2 : ∀ (ds0 : List PEqualNP.CircuitLowerBounds.Gate) (op0 : PEqualNP.CircuitLowerBounds.GateOp) (ka kb : ℕ),
          PEqualNP.TopForm.IsAO2 10 ⟨ds0, 0⟩ →
          op0 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ op0 = PEqualNP.CircuitLowerBounds.GateOp.or →
          ka < 10 + ds0.length → kb < 10 + ds0.length →
          PEqualNP.TopForm.IsAO2 10 ⟨ds0 ++ [PEqualNP.CircuitLowerBounds.Gate.mk op0 [ka, kb]], 0⟩ := by
        intro ds0 op0 ka kb hao0 hop hka hkb
        refine ⟨?_, ?_, ?_⟩
        · intro g' hg'
          simp only [List.mem_append, List.mem_singleton] at hg'
          rcases hg' with hg' | rfl
          · exact hao0.1 g' hg'
          · exact hop
        · intro j hj i hi
          simp only [List.length_append, List.length_singleton] at hj
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hlt | heq
          · have hgate : PEqualNP.MetaComplexity.NestedCover.gateAt ⟨ds0 ++ [PEqualNP.CircuitLowerBounds.Gate.mk op0 [ka, kb]], 0⟩ j =
                PEqualNP.MetaComplexity.NestedCover.gateAt ⟨ds0, 0⟩ j := by
              dsimp only [PEqualNP.MetaComplexity.NestedCover.gateAt]
              rw [List.getD_append _ _ _ _ hlt]
            rw [hgate] at hi
            exact hao0.2.1 j hlt i hi
          · subst heq
            have hgate : PEqualNP.MetaComplexity.NestedCover.gateAt ⟨ds0 ++ [PEqualNP.CircuitLowerBounds.Gate.mk op0 [ka, kb]], 0⟩ ds0.length =
                PEqualNP.CircuitLowerBounds.Gate.mk op0 [ka, kb] := by
              dsimp only [PEqualNP.MetaComplexity.NestedCover.gateAt]
              rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self, List.getD_cons_zero]
            rw [hgate] at hi
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
            rcases hi with rfl | rfl <;> assumption
        · intro g' hg'
          simp only [List.mem_append, List.mem_singleton] at hg'
          rcases hg' with hg' | rfl
          · exact hao0.2.2 g' hg'
          · rfl
      rcases hg.1 with hop | hop
      · cases hma : mp.getD (g.inputs.getD 0 0) none with
        | none =>
          have hst : step (ds, mp) g = (ds, mp ++ [none]) := by dsimp only [step]; rw [hop, hma]
          rw [hst]
          have res := ih ds (mp ++ [none]) htail (step_mp mp none (10 + ds.length) hmp (fun _ h => by cases h)) hao
          refine ⟨res.1, res.2.1, Nat.le_trans res.2.2 ?_⟩
          rw [hcount_cons]; exact Nat.add_le_add_left (Nat.le_add_right _ _) _
        | some ka =>
          cases hmb : mp.getD (g.inputs.getD 1 0) none with
          | none =>
            have hst : step (ds, mp) g = (ds, mp ++ [none]) := by dsimp only [step]; rw [hop, hma, hmb]
            rw [hst]
            have res := ih ds (mp ++ [none]) htail (step_mp mp none (10 + ds.length) hmp (fun _ h => by cases h)) hao
            refine ⟨res.1, res.2.1, Nat.le_trans res.2.2 ?_⟩
            rw [hcount_cons]; exact Nat.add_le_add_left (Nat.le_add_right _ _) _
          | some kb =>
            have hst : step (ds, mp) g = (ds ++ [PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.and [ka, kb]], mp ++ [some (10 + ds.length)]) := by
              dsimp only [step]; rw [hop, hma, hmb]
            rw [hst]
            have hka := hmp _ ka hma
            have hkb := hmp _ kb hmb
            have hmp' : ∀ i k, (mp ++ [some (10 + ds.length)]).getD i none = some k →
                k < 10 + (ds ++ [PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.and [ka, kb]]).length := by
              refine step_mp mp (some (10 + ds.length)) _ (fun i k hi => ?_) (fun k hk => ?_)
              · exact Nat.lt_trans (hmp i k hi) (by simp)
              · cases hk; simp
            have hao' := push_ao2 ds PEqualNP.CircuitLowerBounds.GateOp.and ka kb hao (Or.inl rfl) hka hkb
            have res := ih _ _ htail hmp' hao'
            refine ⟨res.1, res.2.1, Nat.le_trans res.2.2 ?_⟩
            have hc1 : (ds ++ [PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.and [ka, kb]]).countP isOr = ds.countP isOr := by
              rw [List.countP_append, List.countP_cons, List.countP_nil]; rfl
            rw [hc1, hcount_cons]
            exact Nat.add_le_add_left (Nat.le_add_right _ _) _
      · cases hma : mp.getD (g.inputs.getD 0 0) none with
        | none =>
          cases hmb : mp.getD (g.inputs.getD 1 0) none with
          | none =>
            have hst : step (ds, mp) g = (ds, mp ++ [none]) := by dsimp only [step]; rw [hop, hma, hmb]
            rw [hst]
            have res := ih ds (mp ++ [none]) htail (step_mp mp none (10 + ds.length) hmp (fun _ h => by cases h)) hao
            refine ⟨res.1, res.2.1, Nat.le_trans res.2.2 ?_⟩
            rw [hcount_cons]; exact Nat.add_le_add_left (Nat.le_add_right _ _) _
          | some kb =>
            have hst : step (ds, mp) g = (ds, mp ++ [some kb]) := by dsimp only [step]; rw [hop, hma, hmb]
            rw [hst]
            have res := ih ds (mp ++ [some kb]) htail (step_mp mp (some kb) (10 + ds.length) hmp (fun k hk => by cases hk; exact hmp _ kb hmb)) hao
            refine ⟨res.1, res.2.1, Nat.le_trans res.2.2 ?_⟩
            rw [hcount_cons]; exact Nat.add_le_add_left (Nat.le_add_right _ _) _
        | some ka =>
          cases hmb : mp.getD (g.inputs.getD 1 0) none with
          | none =>
            have hst : step (ds, mp) g = (ds, mp ++ [some ka]) := by dsimp only [step]; rw [hop, hma, hmb]
            rw [hst]
            have res := ih ds (mp ++ [some ka]) htail (step_mp mp (some ka) (10 + ds.length) hmp (fun k hk => by cases hk; exact hmp _ ka hma)) hao
            refine ⟨res.1, res.2.1, Nat.le_trans res.2.2 ?_⟩
            rw [hcount_cons]; exact Nat.add_le_add_left (Nat.le_add_right _ _) _
          | some kb =>
            have hst : step (ds, mp) g = (ds ++ [PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [ka, kb]], mp ++ [some (10 + ds.length)]) := by
              dsimp only [step]; rw [hop, hma, hmb]
            rw [hst]
            have hka := hmp _ ka hma
            have hkb := hmp _ kb hmb
            have hmp' : ∀ i k, (mp ++ [some (10 + ds.length)]).getD i none = some k →
                k < 10 + (ds ++ [PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [ka, kb]]).length := by
              refine step_mp mp (some (10 + ds.length)) _ (fun i k hi => ?_) (fun k hk => ?_)
              · exact Nat.lt_trans (hmp i k hi) (by simp)
              · cases hk; simp
            have hao' := push_ao2 ds PEqualNP.CircuitLowerBounds.GateOp.or ka kb hao (Or.inr rfl) hka hkb
            have res := ih _ _ htail hmp' hao'
            refine ⟨res.1, res.2.1, Nat.le_trans res.2.2 ?_⟩
            have hc1 : (ds ++ [PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [ka, kb]]).countP isOr = ds.countP isOr + 1 := by
              rw [List.countP_append, List.countP_cons, List.countP_nil]; rfl
            have hc2 : isOr g = true := by dsimp only [isOr]; rw [hop]
            rw [hc1, hcount_cons, hc2]; dsimp only [cond]
            rw [Nat.add_assoc, Nat.add_comm 1 (gs.countP isOr), ← Nat.add_assoc]
  have step_sem : ∀ (x : Fin 10 → Bool) (gs : List PEqualNP.CircuitLowerBounds.Gate)
      (ds : List PEqualNP.CircuitLowerBounds.Gate) (mp : List (Option ℕ)) (wC : List Bool),
      (∀ g ∈ gs, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) →
      (∀ i k, mp.getD i none = some k → k < 10 + ds.length) →
      wC.length = mp.length →
      (∀ i, wC.getD i false = Option.rec false (fun k => (ds.foldl bstep (List.ofFn x)).getD k false) (mp.getD i none)) →
      ∀ i, (gs.foldl bstep wC).getD i false =
        Option.rec false (fun k => ((gs.foldl step (ds, mp)).1.foldl bstep (List.ofFn x)).getD k false) ((gs.foldl step (ds, mp)).2.getD i none) := by
    intro x gs
    induction gs with
    | nil =>
      intro ds mp wC _ _ _ hsem i
      exact hsem i
    | cons g gs ih =>
      intro ds mp wC hgs hmp hlen hsem i
      have hg := hgs g (List.mem_cons_self ..)
      have htail : ∀ g' ∈ gs, (g'.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g'.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g'.inputs.length = 2 :=
        fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')
      rw [List.foldl_cons, List.foldl_cons]
      have g_inputs_eq : g.inputs = [g.inputs.getD 0 0, g.inputs.getD 1 0] := by
        have hlen2 := hg.2
        rcases h : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, cs⟩⟩⟩
        · rw [h] at hlen2; cases hlen2
        · rw [h] at hlen2; cases hlen2
        · simp [List.getD]
        · rw [h] at hlen2; cases hlen2
      have sem_push_same : ∀ (val : Bool) (mval : Option ℕ),
          (val = Option.rec false (fun k => (ds.foldl bstep (List.ofFn x)).getD k false) mval) →
          ∀ j, (wC ++ [val]).getD j false = Option.rec false (fun k => (ds.foldl bstep (List.ofFn x)).getD k false) ((mp ++ [mval]).getD j none) := by
        intro val mval hval j
        rcases Nat.lt_trichotomy j mp.length with hlt | heq | hgt
        · rw [List.getD_append _ _ _ _ (hlen ▸ hlt), List.getD_append _ _ _ _ hlt]
          exact hsem j
        · subst heq
          rw [List.getD_append_right _ _ _ _ (by simp [hlen]), hlen, Nat.sub_self, List.getD_cons_zero]
          rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self, List.getD_cons_zero]
          exact hval
        · rw [List.getD_eq_default _ _ (by simp [hlen]; exact Nat.succ_le_of_lt hgt)]
          rw [List.getD_eq_default _ _ (by simp; exact Nat.succ_le_of_lt hgt)]
      have sem_push_gate : ∀ (op0 : PEqualNP.CircuitLowerBounds.GateOp) (ka kb : ℕ) (val : Bool),
          val = op0.eval [(ds.foldl bstep (List.ofFn x)).getD ka false, (ds.foldl bstep (List.ofFn x)).getD kb false] →
          ∀ j, (wC ++ [val]).getD j false =
            Option.rec false (fun k => ((ds ++ [PEqualNP.CircuitLowerBounds.Gate.mk op0 [ka, kb]]).foldl bstep (List.ofFn x)).getD k false) ((mp ++ [some (10 + ds.length)]).getD j none) := by
        intro op0 ka kb val hval j
        set wD := ds.foldl bstep (List.ofFn x)
        have hwDlen : wD.length = 10 + ds.length :=
          (wires_len ds (List.ofFn x)).trans (by rw [List.length_ofFn])
        have hgrow : (ds ++ [PEqualNP.CircuitLowerBounds.Gate.mk op0 [ka, kb]]).foldl bstep (List.ofFn x) = wD ++ [val] := by
          rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
          change wD ++ [op0.eval ([ka, kb].map fun i => wD.getD i false)] = wD ++ [val]
          simp only [List.map_cons, List.map_nil, hval]
        rw [hgrow]
        rcases Nat.lt_trichotomy j mp.length with hlt | heq | hgt
        · rw [List.getD_append _ _ _ _ (hlen ▸ hlt), List.getD_append _ _ _ _ hlt]
          rw [hsem j]
          cases hm : mp.getD j none with
          | none => rfl
          | some k =>
            dsimp only
            have hk : k < wD.length := hwDlen ▸ hmp j k hm
            change wD.getD k false = (wD ++ [val]).getD k false
            rw [List.getD_append _ _ _ _ hk]
        · subst heq
          rw [List.getD_append_right _ _ _ _ (by simp [hlen]), hlen, Nat.sub_self, List.getD_cons_zero]
          rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self, List.getD_cons_zero]
          dsimp only
          rw [← hwDlen, List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self, List.getD_cons_zero]
        · rw [List.getD_eq_default _ _ (by simp [hlen]; exact Nat.succ_le_of_lt hgt)]
          rw [List.getD_eq_default _ _ (by simp; exact Nat.succ_le_of_lt hgt)]
      have hha : wC.getD (g.inputs.getD 0 0) false = Option.rec false (fun k => (ds.foldl bstep (List.ofFn x)).getD k false) (mp.getD (g.inputs.getD 0 0) none) := hsem _
      have hhb : wC.getD (g.inputs.getD 1 0) false = Option.rec false (fun k => (ds.foldl bstep (List.ofFn x)).getD k false) (mp.getD (g.inputs.getD 1 0) none) := hsem _
      rcases hg.1 with hop | hop
      · have hval : g.op.eval (g.inputs.map fun i => wC.getD i false) =
            (wC.getD (g.inputs.getD 0 0) false && wC.getD (g.inputs.getD 1 0) false) := by
          conv_lhs => rw [g_inputs_eq, hop]
          dsimp only [PEqualNP.CircuitLowerBounds.GateOp.eval]
          rw [List.map_cons, List.map_cons, List.map_nil, List.all_cons, List.all_cons, List.all_nil, Bool.and_true]
          rfl
        have hbstep : bstep wC g = wC ++ [wC.getD (g.inputs.getD 0 0) false && wC.getD (g.inputs.getD 1 0) false] := by
          dsimp only [bstep]; rw [hval]
        rw [hbstep]
        cases hma : mp.getD (g.inputs.getD 0 0) none with
        | none =>
          have hst : step (ds, mp) g = (ds, mp ++ [none]) := by dsimp only [step]; rw [hop, hma]
          rw [hst]
          rw [hma] at hha
          refine ih ds (mp ++ [none]) _ htail (step_mp mp none (10 + ds.length) hmp (fun _ h => by cases h)) (by simp [hlen]) ?_ i
          refine sem_push_same _ none ?_
          simp only [hha, Bool.false_and]
        | some ka =>
          cases hmb : mp.getD (g.inputs.getD 1 0) none with
          | none =>
            have hst : step (ds, mp) g = (ds, mp ++ [none]) := by dsimp only [step]; rw [hop, hma, hmb]
            rw [hst]
            rw [hmb] at hhb
            refine ih ds (mp ++ [none]) _ htail (step_mp mp none (10 + ds.length) hmp (fun _ h => by cases h)) (by simp [hlen]) ?_ i
            refine sem_push_same _ none ?_
            simp only [hhb, Bool.and_false]
          | some kb =>
            have hst : step (ds, mp) g = (ds ++ [PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.and [ka, kb]], mp ++ [some (10 + ds.length)]) := by
              dsimp only [step]; rw [hop, hma, hmb]
            rw [hst]
            rw [hma] at hha; rw [hmb] at hhb
            have hmp' : ∀ i k, (mp ++ [some (10 + ds.length)]).getD i none = some k →
                k < 10 + (ds ++ [PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.and [ka, kb]]).length := by
              refine step_mp mp (some (10 + ds.length)) _ (fun i k hi => ?_) (fun k hk => ?_)
              · exact Nat.lt_trans (hmp i k hi) (by simp)
              · cases hk; simp
            refine ih _ _ _ htail hmp' (by simp [hlen]) ?_ i
            refine sem_push_gate PEqualNP.CircuitLowerBounds.GateOp.and ka kb _ ?_
            dsimp only [PEqualNP.CircuitLowerBounds.GateOp.eval]
            rw [List.all_cons, List.all_cons, List.all_nil, Bool.and_true, hha, hhb]; rfl
      · have hval : g.op.eval (g.inputs.map fun i => wC.getD i false) =
            (wC.getD (g.inputs.getD 0 0) false || wC.getD (g.inputs.getD 1 0) false) := by
          conv_lhs => rw [g_inputs_eq, hop]
          dsimp only [PEqualNP.CircuitLowerBounds.GateOp.eval]
          rw [List.map_cons, List.map_cons, List.map_nil, List.any_cons, List.any_cons, List.any_nil, Bool.or_false]
          rfl
        have hbstep : bstep wC g = wC ++ [wC.getD (g.inputs.getD 0 0) false || wC.getD (g.inputs.getD 1 0) false] := by
          dsimp only [bstep]; rw [hval]
        rw [hbstep]
        cases hma : mp.getD (g.inputs.getD 0 0) none with
        | none =>
          cases hmb : mp.getD (g.inputs.getD 1 0) none with
          | none =>
            have hst : step (ds, mp) g = (ds, mp ++ [none]) := by dsimp only [step]; rw [hop, hma, hmb]
            rw [hst]
            rw [hma] at hha; rw [hmb] at hhb
            refine ih ds (mp ++ [none]) _ htail (step_mp mp none (10 + ds.length) hmp (fun _ h => by cases h)) (by simp [hlen]) ?_ i
            refine sem_push_same _ none ?_
            simp only [hha, hhb, Bool.or_false]
          | some kb =>
            have hst : step (ds, mp) g = (ds, mp ++ [some kb]) := by dsimp only [step]; rw [hop, hma, hmb]
            rw [hst]
            rw [hma] at hha; rw [hmb] at hhb
            refine ih ds (mp ++ [some kb]) _ htail (step_mp mp (some kb) (10 + ds.length) hmp (fun k hk => by cases hk; exact hmp _ kb hmb)) (by simp [hlen]) ?_ i
            refine sem_push_same _ (some kb) ?_
            simp only [hha, hhb, Bool.false_or]
        | some ka =>
          cases hmb : mp.getD (g.inputs.getD 1 0) none with
          | none =>
            have hst : step (ds, mp) g = (ds, mp ++ [some ka]) := by dsimp only [step]; rw [hop, hma, hmb]
            rw [hst]
            rw [hma] at hha; rw [hmb] at hhb
            refine ih ds (mp ++ [some ka]) _ htail (step_mp mp (some ka) (10 + ds.length) hmp (fun k hk => by cases hk; exact hmp _ ka hma)) (by simp [hlen]) ?_ i
            refine sem_push_same _ (some ka) ?_
            simp only [hha, hhb, Bool.or_false]
          | some kb =>
            have hst : step (ds, mp) g = (ds ++ [PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [ka, kb]], mp ++ [some (10 + ds.length)]) := by
              dsimp only [step]; rw [hop, hma, hmb]
            rw [hst]
            rw [hma] at hha; rw [hmb] at hhb
            have hmp' : ∀ i k, (mp ++ [some (10 + ds.length)]).getD i none = some k →
                k < 10 + (ds ++ [PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [ka, kb]]).length := by
              refine step_mp mp (some (10 + ds.length)) _ (fun i k hi => ?_) (fun k hk => ?_)
              · exact Nat.lt_trans (hmp i k hi) (by simp)
              · cases hk; simp
            refine ih _ _ _ htail hmp' (by simp [hlen]) ?_ i
            refine sem_push_gate PEqualNP.CircuitLowerBounds.GateOp.or ka kb _ ?_
            dsimp only [PEqualNP.CircuitLowerBounds.GateOp.eval]
            rw [List.any_cons, List.any_cons, List.any_nil, Bool.or_false, hha, hhb]; rfl
  let mp0 : List (Option ℕ) := List.ofFn fun i : Fin 11 =>
    if i = v then none else if i.val < v.val then some i.val else some (i.val - 1)
  have hmp0 : ∀ i k, mp0.getD i none = some k → k < 10 + ([] : List PEqualNP.CircuitLowerBounds.Gate).length := by
    intro i k hi
    by_cases h11 : i < 11
    · have hget : mp0.getD i none = if (⟨i, h11⟩ : Fin 11) = v then none else if i < v.val then some i else some (i - 1) := by
        dsimp [mp0]
        rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
        simp only [h11, ↓reduceDIte, Option.getD_some]
      rw [hget] at hi
      split_ifs at hi with heq hlt
      · cases hi; exact Nat.lt_trans hlt (Nat.lt_trans hv (by decide))
      · cases hi
        have hvi : v.val < i := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) (fun h => heq (Fin.ext h.symm))
        have hpos : 1 ≤ i := Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le v.val) hvi)
        exact Nat.sub_lt_left_of_lt_add hpos h11
    · have : mp0.getD i none = none := List.getD_eq_default _ _ (by simp [mp0]; exact Nat.le_of_not_lt h11)
      rw [this] at hi; cases hi
  have hsem0 : ∀ (x : Fin 10 → Bool) (i : ℕ),
      (List.ofFn (Fin.insertNth (α := fun _ => Bool) v false x)).getD i false =
      Option.rec false (fun k => (([] : List PEqualNP.CircuitLowerBounds.Gate).foldl bstep (List.ofFn x)).getD k false) (mp0.getD i none) := by
    intro x i
    by_cases h11 : i < 11
    · have hgetC : (List.ofFn (Fin.insertNth (α := fun _ => Bool) v false x)).getD i false =
          Fin.insertNth (α := fun _ => Bool) v false x ⟨i, h11⟩ := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
        simp only [h11, ↓reduceDIte, Option.getD_some]
      have hgetM : mp0.getD i none =
          (fun f : Fin 11 => if f = v then none else if f.val < v.val then some f.val else some (f.val - 1)) ⟨i, h11⟩ := by
        dsimp [mp0]
        rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
        simp only [h11, ↓reduceDIte, Option.getD_some]
      rw [hgetC, hgetM, List.foldl_nil]
      generalize (⟨i, h11⟩ : Fin 11) = fi
      dsimp only
      induction fi using Fin.succAboveCases v with
      | x =>
        simp [Fin.insertNth_apply_same]
      | p j =>
        rw [Fin.insertNth_apply_succAbove]
        have hne : v.succAbove j ≠ v := Fin.succAbove_ne v j
        simp only [hne, ↓reduceIte]
        by_cases hj : j.castSucc < v
        · have hval : (v.succAbove j).val = j.val := by simp [Fin.succAbove_of_castSucc_lt _ _ hj]
          have hlt : j.val < v.val := hj
          rw [hval]
          simp only [hlt, ↓reduceIte]
          rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
          simp only [j.isLt, ↓reduceDIte, Option.getD_some]
        · have hle : v ≤ j.castSucc := Fin.not_lt.mp hj
          have hval : (v.succAbove j).val = j.val + 1 := by simp [Fin.succAbove_of_le_castSucc _ _ hle]
          have hnotlt : ¬ j.val + 1 < v.val := Nat.not_lt_of_le (Nat.le_succ_of_le hle)
          rw [hval, Nat.add_sub_cancel]
          simp only [hnotlt, ↓reduceIte]
          rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
          simp only [j.isLt, ↓reduceDIte, Option.getD_some]
    · have hc : (List.ofFn (Fin.insertNth (α := fun _ => Bool) v false x)).getD i false = false :=
        List.getD_eq_default _ _ (by simp; exact Nat.le_of_not_lt h11)
      have hm : mp0.getD i none = none :=
        List.getD_eq_default _ _ (by simp [mp0]; exact Nat.le_of_not_lt h11)
      rw [hc, hm]
  have hCgs : ∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2 :=
    fun g hg => ⟨hAO.1 g hg, hAO.2.2 g hg⟩
  have hao0 : PEqualNP.TopForm.IsAO2 10 ⟨[], 0⟩ := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg; cases hg
    · intro j hj; cases hj
    · intro g hg; cases hg
  let res := C.gates.foldl step ([], mp0)
  have hres_inv := step_inv C.gates [] mp0 hCgs hmp0 hao0
  cases hout : res.2.getD C.output none with
  | none =>
    exfalso
    let xEdge : Fin 10 → Bool := fun j => decide ((v.succAbove j).val = 8 ∨ (v.succAbove j).val = 9)
    have h8ne : (8 : Fin 11) ≠ v := by
      intro h; have : (8 : ℕ) = v.val := congrArg Fin.val h
      exact absurd (this ▸ hv) (by decide)
    have h9ne : (9 : Fin 11) ≠ v := by
      intro h; have : (9 : ℕ) = v.val := congrArg Fin.val h
      exact absurd (this ▸ hv) (by decide)
    obtain ⟨j8, hj8⟩ := Fin.exists_succAbove_eq h8ne
    obtain ⟨j9, hj9⟩ := Fin.exists_succAbove_eq h9ne
    have htrue8 : Fin.insertNth (α := fun _ => Bool) v false xEdge (8 : Fin 11) = true := by
      rw [← hj8, Fin.insertNth_apply_succAbove]
      simp [xEdge, hj8]
    have htrue9 : Fin.insertNth (α := fun _ => Bool) v false xEdge (9 : Fin 11) = true := by
      rw [← hj9, Fin.insertNth_apply_succAbove]
      simp [xEdge, hj9]
    have hadj89 : G11.Adj (8 : Fin 11) (9 : Fin 11) := by dsimp [G11]; decide
    have hGtrue : PEqualNP.MetaComplexity.NestedCover.graphFun G11 ∅ (Fin.insertNth (α := fun _ => Bool) v false xEdge) = true := by
      dsimp only [PEqualNP.MetaComplexity.NestedCover.graphFun]
      simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or, decide_eq_true_eq]
      exact ⟨8, 9, hadj89, htrue8, htrue9⟩
    have hCfalse : PEqualNP.MetaComplexity.circuitFun 11 C (Fin.insertNth (α := fun _ => Bool) v false xEdge) = false := by
      change (C.gates.foldl bstep (List.ofFn (Fin.insertNth (α := fun _ => Bool) v false xEdge))).getD C.output false = false
      rw [step_sem xEdge C.gates [] mp0 _ hCgs hmp0 (by simp [mp0]) (hsem0 xEdge) C.output]
      change Option.rec false (fun k => (res.1.foldl bstep (List.ofFn xEdge)).getD k false) (res.2.getD C.output none) = false
      rw [hout]
    have heq := hagree (Fin.insertNth (α := fun _ => Bool) v false xEdge) (Fin.insertNth_apply_same (α := fun _ => Bool) v false xEdge)
    rw [hCfalse, hGtrue] at heq
    cases heq
  | some out =>
    let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨res.1, out⟩
    have hDAO : PEqualNP.TopForm.IsAO2 10 D := hres_inv.2.1
    have hDor : List.countP isOr D.gates ≤ List.countP isOr C.gates := by
      have := hres_inv.2.2
      simp only [List.countP_nil, Nat.zero_add] at this
      exact this
    have hDeval : ∀ x : Fin 10 → Bool, PEqualNP.MetaComplexity.circuitFun 10 D x =
        PEqualNP.MetaComplexity.NestedCover.graphFun G11 ∅ (Fin.insertNth (α := fun _ => Bool) v false x) := by
      intro x
      have h1 := step_sem x C.gates [] mp0 (List.ofFn (Fin.insertNth (α := fun _ => Bool) v false x)) hCgs hmp0 (by simp [mp0]) (hsem0 x) C.output
      change (C.gates.foldl bstep (List.ofFn (Fin.insertNth (α := fun _ => Bool) v false x))).getD C.output false =
        Option.rec false (fun k => (res.1.foldl bstep (List.ofFn x)).getD k false) (res.2.getD C.output none) at h1
      rw [hout] at h1
      have h2 := hagree (Fin.insertNth (α := fun _ => Bool) v false x) (Fin.insertNth_apply_same (α := fun _ => Bool) v false x)
      exact h1.symm.trans h2
    have reduce_graph : ∀ (v0 : Fin 11) (H : SimpleGraph (Fin 10)) [DecidableRel H.Adj],
        (∀ i j : Fin 10, G11.Adj (v0.succAbove i) (v0.succAbove j) ↔ H.Adj i j) →
        (∀ x : Fin 10 → Bool, PEqualNP.MetaComplexity.NestedCover.graphFun G11 ∅ (Fin.insertNth (α := fun _ => Bool) v0 false x) =
          PEqualNP.MetaComplexity.NestedCover.graphFun H ∅ x) := by
      intro v0 H instH hadj x
      dsimp only [PEqualNP.MetaComplexity.NestedCover.graphFun]
      simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or]
      apply decide_eq_decide.mpr
      constructor
      · rintro ⟨a, b, hab, ha, hb⟩
        have hav : a ≠ v0 := by intro h; subst h; rw [Fin.insertNth_apply_same] at ha; cases ha
        have hbv : b ≠ v0 := by intro h; subst h; rw [Fin.insertNth_apply_same] at hb; cases hb
        obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hav
        obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hbv
        rw [Fin.insertNth_apply_succAbove] at ha hb
        exact ⟨i, j, (hadj i j).mp hab, ha, hb⟩
      · rintro ⟨i, j, hij, hi, hj⟩
        refine ⟨v0.succAbove i, v0.succAbove j, (hadj i j).mpr hij, ?_, ?_⟩
        · rw [Fin.insertNth_apply_succAbove]; exact hi
        · rw [Fin.insertNth_apply_succAbove]; exact hj
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hv) with hv3 | hv3
    · rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hv3) with hv2 | hv2
      · rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hv2) with hv1 | hv1
        · have hv0 : v = (0 : Fin 11) := Fin.ext (Nat.lt_one_iff.mp hv1)
          have hadj : ∀ i j : Fin 10, G11.Adj ((0 : Fin 11).succAbove i) ((0 : Fin 11).succAbove j) ↔
              (PEqualNP.EdgeOwnership.edgeGraph 10 [(0, 3), (0, 7), (1, 4), (1, 9), (2, 5), (2, 6), (3, 7), (3, 9), (4, 7), (4, 8), (5, 6), (5, 9), (6, 8), (7, 8)]).Adj i j := by
            dsimp [G11]; decide +kernel
          have hfun : PEqualNP.MetaComplexity.circuitFun 10 D =
              PEqualNP.MetaComplexity.NestedCover.graphFun (PEqualNP.EdgeOwnership.edgeGraph 10 [(0, 3), (0, 7), (1, 4), (1, 9), (2, 5), (2, 6), (3, 7), (3, 9), (4, 7), (4, 8), (5, 6), (5, 9), (6, 8), (7, 8)]) ∅ := by
            funext x; exact (hDeval x).trans (by rw [hv0]; exact reduce_graph 0 _ hadj x)
          exact Nat.le_trans (h0 D hDAO hfun) hDor
        · have hv1' : v = (1 : Fin 11) := Fin.ext hv1
          have hadj : ∀ i j : Fin 10, G11.Adj ((1 : Fin 11).succAbove i) ((1 : Fin 11).succAbove j) ↔
              (PEqualNP.EdgeOwnership.edgeGraph 10 [(0, 8), (0, 9), (1, 4), (1, 9), (2, 5), (2, 6), (3, 7), (3, 9), (4, 7), (4, 8), (5, 6), (5, 9), (6, 8), (7, 8)]).Adj i j := by
            dsimp [G11]; decide +kernel
          have hfun : PEqualNP.MetaComplexity.circuitFun 10 D =
              PEqualNP.MetaComplexity.NestedCover.graphFun (PEqualNP.EdgeOwnership.edgeGraph 10 [(0, 8), (0, 9), (1, 4), (1, 9), (2, 5), (2, 6), (3, 7), (3, 9), (4, 7), (4, 8), (5, 6), (5, 9), (6, 8), (7, 8)]) ∅ := by
            funext x; exact (hDeval x).trans (by rw [hv1']; exact reduce_graph 1 _ hadj x)
          exact Nat.le_trans (h1 D hDAO hfun) hDor
      · have hv2' : v = (2 : Fin 11) := Fin.ext hv2
        have hadj : ∀ i j : Fin 10, G11.Adj ((2 : Fin 11).succAbove i) ((2 : Fin 11).succAbove j) ↔
            (PEqualNP.EdgeOwnership.edgeGraph 10 [(0, 8), (0, 9), (1, 3), (1, 7), (2, 5), (2, 6), (3, 7), (3, 9), (4, 7), (4, 8), (5, 6), (5, 9), (6, 8), (7, 8)]).Adj i j := by
          dsimp [G11]; decide +kernel
        have hfun : PEqualNP.MetaComplexity.circuitFun 10 D =
            PEqualNP.MetaComplexity.NestedCover.graphFun (PEqualNP.EdgeOwnership.edgeGraph 10 [(0, 8), (0, 9), (1, 3), (1, 7), (2, 5), (2, 6), (3, 7), (3, 9), (4, 7), (4, 8), (5, 6), (5, 9), (6, 8), (7, 8)]) ∅ := by
          funext x; exact (hDeval x).trans (by rw [hv2']; exact reduce_graph 2 _ hadj x)
        exact Nat.le_trans (h2 D hDAO hfun) hDor
    · have hv3' : v = (3 : Fin 11) := Fin.ext hv3
      have hadj : ∀ i j : Fin 10, G11.Adj ((3 : Fin 11).succAbove i) ((3 : Fin 11).succAbove j) ↔
          (PEqualNP.EdgeOwnership.edgeGraph 10 [(0, 8), (0, 9), (1, 3), (1, 7), (2, 4), (2, 9), (3, 7), (3, 9), (4, 7), (4, 8), (5, 6), (5, 9), (6, 8), (7, 8)]).Adj i j := by
        dsimp [G11]; decide +kernel
      have hfun : PEqualNP.MetaComplexity.circuitFun 10 D =
          PEqualNP.MetaComplexity.NestedCover.graphFun (PEqualNP.EdgeOwnership.edgeGraph 10 [(0, 8), (0, 9), (1, 3), (1, 7), (2, 4), (2, 9), (3, 7), (3, 9), (4, 7), (4, 8), (5, 6), (5, 9), (6, 8), (7, 8)]) ∅ := by
        funext x; exact (hDeval x).trans (by rw [hv3']; exact reduce_graph 3 _ hadj x)
      exact Nat.le_trans (h3 D hDAO hfun) hDor
