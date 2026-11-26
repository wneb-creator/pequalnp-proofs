import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.BicliqueBlockCost
open scoped BigOperators

-- The trace extraction and boundary-row extension are adapted from R_meta_3188_31.
-- L-meta-2656 supplies the clean AND-gate cover theorem.
-- The fifteen-gate output and reader constraints are L-meta-3602.
set_option synthInstance.maxSize 256 in
set_option maxRecDepth 16000 in
set_option maxHeartbeats 22000000 in
theorem PEqualNP.Outside.R_meta_4881_47
    (toBlocks : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit),
      (∃ a b, G.Adj a b) →
      (∀ a b c d, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) →
      Monotone2 C →
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
        ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true) →
      (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = GateOp.and →
        ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n+j) false = true →
          ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true) →
      HasBlockCost G C.size)
    (cardinalShape : ∀ C : Circuit, FanInTwo C → circuitFun 9 C =
        (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
          (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
          (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) →
      C.size ≤ 15 → C.size = 15 ∧ C.output = 23 ∧
        ∀ j < 14, ∃ k : Fin C.gates.length, j < k.val ∧ 9+j ∈ (C.gates.get k).inputs)
    (unclean : ∀ C : Circuit, Monotone2 C → C.size = 15 → C.output = 23 →
      (∀ j < 14, ∃ k : Fin C.gates.length, j < k.val ∧ 9+j ∈ (C.gates.get k).inputs) →
      C.gates[0]? = some ⟨GateOp.or,[0,2]⟩ →
      C.gates[1]? = some ⟨GateOp.and,[1,9]⟩ →
      (∃ (j : ℕ) (g : Gate) (x : Fin 9 → Bool), C.gates[j]? = some g ∧
        g.op = GateOp.and ∧ (C.wires (List.ofFn x)).getD (9+j) false = true ∧
          C.eval (List.ofFn x) = false) →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x) ≠
        ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
          (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
          (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) :
∀ x1 ∈ [(12288 : BitVec (24 : ℕ))],   ∀ (x3 : List (BitVec (24 : ℕ))),     have x4 : List (BitVec (24 : ℕ)) := [(202052 : BitVec (24 : ℕ)), (276515 : BitVec (24 : ℕ)), (549652 : BitVec (24 : ℕ)), (1097833 : BitVec (24 : ℕ)), (101010 : BitVec (24 : ℕ)), (10616859 : BitVec (24 : ℕ)), (4456668 : BitVec (24 : ℕ)), (2624736 : BitVec (24 : ℕ)), (13635328 : BitVec (24 : ℕ)), (751444 : BitVec (24 : ℕ))] ++ [x1];     (16773120 : BitVec (24 : ℕ)) ∈ x4 ++ x3 →       (∀ (x6 : Fin x3.length),           have x7 : List (BitVec (24 : ℕ)) := x4 ++ List.take (↑x6) x3;           ∃ x8 ∈ x7, ∃ x9 ∈ x7, x3.get x6 = x8 &&& x9 ∨ x3.get x6 = x8 ||| x9) →         (14 : ℕ) ≤ x3.length := by
  have clean : ∀ C : Circuit, Monotone2 C →
        (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) =
          ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
            (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
            (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) →
        (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = GateOp.and →
          ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD (9+j) false = true →
            C.eval (List.ofFn x) = true) →
        16 ≤ C.size := by
    intro C mono correct clean
    let L : List (Fin 9 × Fin 9) := [(0,1),(1,2),(2,3),(3,4),(0,4),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(5,8)]
    let E := L.toFinset
    let Adj (u v : Fin 9) := (u,v) ∈ E ∨ (v,u) ∈ E
    have noloop : ∀ v, ¬ Adj v v := by decide +kernel
    let G : SimpleGraph (Fin 9) := ⟨Adj, ⟨fun _ _ h => h.symm⟩, ⟨noloop⟩⟩
    have adj (u v : Fin 9) : G.Adj u v ↔ Adj u v := Iff.rfl
    have noCycle : ∀ a b c d : Fin 9, ¬(a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
        Adj a b ∧ Adj b c ∧ Adj c d ∧ Adj d a) := by decide +kernel
    have nofour (a b c d : Fin 9) (ab : a ≠ b) (ac : a ≠ c) (ad : a ≠ d)
        (bc : b ≠ c) (bd : b ≠ d) (cd : c ≠ d)
        (eab : Adj a b) (ebc : Adj b c) (ecd : Adj c d) : ¬ Adj d a :=
      fun eda => noCycle a b c d ⟨ab,ac,ad,bc,bd,cd,eab,ebc,ecd,eda⟩
    have sorted : ∀ u v : Fin 9, (u,v) ∈ E → u ≤ v := by decide +kernel
    have edgeCount : E.card = 12 := by decide +kernel
    have minCover : ∀ S : Finset (Fin 9),
        (∀ u v : Fin 9, (u,v) ∈ E → u ∈ S ∨ v ∈ S) → 5 ≤ S.card := by
      decide +kernel
    have eval (x : Fin 9 → Bool) : C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin 9, G.Adj u v ∧ x u = true ∧ x v = true := by
      have heq : C.eval (List.ofFn x) = L.any (fun (p : Fin 9 × Fin 9) => x p.1 && x p.2) := by
        rw [correct]
        simp only [L,List.any_cons,List.any_nil,Bool.or_false,Bool.and_comm,Bool.or_assoc]
      rw [heq,List.any_eq_true]
      constructor
      · rintro ⟨⟨u,v⟩, h, hv⟩
        exact ⟨u,v,(adj _ _).mpr (Or.inl (List.mem_toFinset.mpr h)),(Bool.and_eq_true_iff.mp hv).1,
          (Bool.and_eq_true_iff.mp hv).2⟩
      · rintro ⟨u,v,h,hu,hv⟩
        rcases (adj _ _).mp h with h | h
        · exact ⟨(u,v),List.mem_toFinset.mp h,Bool.and_eq_true_iff.mpr ⟨hu,hv⟩⟩
        · exact ⟨(v,u),List.mem_toFinset.mp h,Bool.and_eq_true_iff.mpr ⟨hv,hu⟩⟩
    have edge : ∃ u v, G.Adj u v := ⟨0,1,(adj _ _).mpr (Or.inl (by decide +kernel))⟩
    obtain ⟨F,cover,cost⟩ := toBlocks 9 G C edge nofour mono eval
      (fun j g hg hand x hv => (eval x).mp (clean j g hg hand x hv))
    classical
    have star (p : Block 9) (hp : p ∈ F) : p.1.card = 1 ∨ p.2.card = 1 := by
      obtain ⟨disj,ha,hb,complete⟩ := cover.1 p hp
      have al := Finset.card_pos.mpr ha
      have bl := Finset.card_pos.mpr hb
      by_contra h
      push Not at h
      obtain ⟨a,ha₁,b,hb₁,hab⟩ := Finset.one_lt_card.mp (show 1 < p.1.card by omega)
      obtain ⟨c,hc₂,d,hd₂,hcd⟩ := Finset.one_lt_card.mp (show 1 < p.2.card by omega)
      have cross {x y : Fin 9} (hx : x ∈ p.1) (hy : y ∈ p.2) : x ≠ y := by
        rintro rfl
        exact Finset.disjoint_left.mp disj hx hy
      have ac := complete a ha₁ c hc₂
      have bc := complete b hb₁ c hc₂
      have bd := complete b hb₁ d hd₂
      have ad := complete a ha₁ d hd₂
      exact nofour a c b d (cross ha₁ hc₂) hab (cross ha₁ hd₂) (cross hb₁ hc₂).symm hcd
        (cross hb₁ hd₂) ac (G.symm.symm _ _ bc) bd (G.symm.symm _ _ ad)
    have chooseCentre (p : F) : ∃ v : Fin 9, ∀ a b : Fin 9, BlockCovers p.val a b → a = v ∨ b = v := by
      rcases star p.val p.property with ha | hb
      · obtain ⟨v,hv⟩ := Finset.card_eq_one.mp ha
        refine ⟨v, fun a b h => ?_⟩
        rcases h with h | h
        · exact Or.inl (Finset.mem_singleton.mp (hv ▸ h.1))
        · exact Or.inr (Finset.mem_singleton.mp (hv ▸ h.1))
      · obtain ⟨v,hv⟩ := Finset.card_eq_one.mp hb
        refine ⟨v, fun a b h => ?_⟩
        rcases h with h | h
        · exact Or.inr (Finset.mem_singleton.mp (hv ▸ h.2))
        · exact Or.inl (Finset.mem_singleton.mp (hv ▸ h.2))
    choose centre property using chooseCentre
    let S := F.attach.image centre
    have covered (u v : Fin 9) (h : (u,v) ∈ E) : u ∈ S ∨ v ∈ S := by
      obtain ⟨p,hp,hcov⟩ := cover.2 u v ((adj u v).mpr (Or.inl h))
      have mem : centre ⟨p,hp⟩ ∈ S :=
        Finset.mem_image.mpr ⟨⟨p,hp⟩,Finset.mem_attach _ _,rfl⟩
      rcases property ⟨p,hp⟩ u v hcov with e | e
      · exact Or.inl (e ▸ mem)
      · exact Or.inr (e ▸ mem)
    have countS : S.card ≤ F.card := Finset.card_image_le.trans_eq Finset.card_attach
    have countF := (minCover S covered).trans countS
    let norm (e : Fin 9 × Fin 9) : Fin 9 × Fin 9 := (min e.1 e.2,max e.1 e.2)
    let edges (p : Block 9) := (p.1 ×ˢ p.2).image norm
    have memEdges : E ⊆ F.biUnion edges := by
      rintro ⟨u,v⟩ h
      obtain ⟨p,hp,hcov⟩ := cover.2 u v ((adj u v).mpr (Or.inl h))
      apply Finset.mem_biUnion.mpr
      refine ⟨p,hp, Finset.mem_image.mpr ?_⟩
      have le := sorted u v h
      rcases hcov with h | h
      · exact ⟨(u,v),Finset.mem_product.mpr h,by simp [norm,min_eq_left le,max_eq_right le]⟩
      · exact ⟨(v,u),Finset.mem_product.mpr h,by simp [norm,min_eq_right le,max_eq_left le]⟩
    have countEdges (p : Block 9) (hp : p ∈ F) : (edges p).card ≤ blockCost p := by
      calc
        (edges p).card ≤ (p.1 ×ˢ p.2).card := Finset.card_image_le
        _ = blockCost p := by
          rw [Finset.card_product]
          change p.1.card * p.2.card = p.1.card + p.2.card - 1
          rcases star p hp with h | h <;> simp [h]
    have sumEdges : 12 ≤ ∑ p ∈ F, blockCost p := by
      rw [← edgeCount]
      exact (Finset.card_le_card memEdges).trans
        (Finset.card_biUnion_le.trans (Finset.sum_le_sum fun p hp => countEdges p hp))
    change (∑ p ∈ F, blockCost p) + (F.card - 1) ≤ C.size at cost
    omega

  have evalAnd (s : List Bool) : GateOp.and.eval s = s.all id := rfl
  have evalOr (s : List Bool) : GateOp.or.eval s = s.any id := rfl
  let target : BitVec 24 := 16773120
  let mask (i : Fin 24) : BitVec 9 := ([42, 50, 69, 104, 116, 138, 201, 208, 261, 276, 385, 402, 3, 6, 12, 24, 17, 33, 66, 132, 264, 160, 320, 288] : List (BitVec 9)).getD i.val 0
  let bits (x : BitVec 9) (i : Fin 9) := x.getLsbD i.val
  let edge (x : Fin 9 → Bool) : Bool := x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let val (r : ℕ) (s : (BitVec 24)) := s.getLsbD r
  let shape (g : Gate) : Prop := g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

  -- The extraction induction follows the 24-row circuit construction in project PR 6186.
  have extract (xs ys : List (BitVec 24))
      (h : ∀ j : Fin ys.length, ∃ a ∈ xs ++ ys.take j.val, ∃ b ∈ xs ++ ys.take j.val,
        ys.get j = a &&& b ∨ ys.get j = a ||| b) :
      ∃ gs : List Gate, gs.length = ys.length ∧ (∀ g ∈ gs, shape g) ∧
        ∀ r : ℕ, gs.foldl step (xs.map (val r)) = (xs ++ ys).map (val r) := by
    induction ys generalizing xs with
    | nil => exact ⟨[], rfl, by simp, by simp⟩
    | cons y ys ih =>
      have hhead : ∃ a ∈ xs, ∃ b ∈ xs, y = a &&& b ∨ y = a ||| b := by
        simpa using h ⟨0, by simp⟩
      obtain ⟨a, ha, b, hb, hgate⟩ := hhead
      obtain ⟨i, hi, ea⟩ := List.mem_iff_getElem.mp ha
      obtain ⟨j, hj, eb⟩ := List.mem_iff_getElem.mp hb
      have sub (r k : ℕ) (hk : k < xs.length) :
          (xs.map (val r)).getD k false = val r xs[k] := by
        rw [List.getD_eq_getElem _ _ (by simpa), List.getElem_map]
      have one : ∃ g : Gate, shape g ∧
          ∀ r, step (xs.map (val r)) g = (xs ++ [y]).map (val r) := by
        rcases hgate with eq | eq
        · refine ⟨⟨.and,[i,j]⟩, by simp [shape], fun r => ?_⟩
          simp only [step, evalAnd, List.map_cons, List.map_nil, List.all_cons,
            List.all_nil, id_eq, Bool.and_true, List.map_append]
          rw [sub r i hi, sub r j hj, ea, eb]
          simp [val, eq]
        · refine ⟨⟨.or,[i,j]⟩, by simp [shape], fun r => ?_⟩
          simp only [step, evalOr, List.map_cons, List.map_nil, List.any_cons,
            List.any_nil, id_eq, Bool.or_false, List.map_append]
          rw [sub r i hi, sub r j hj, ea, eb]
          simp [val, eq]
      obtain ⟨g, hg, same⟩ := one
      have tail : ∀ k : Fin ys.length, ∃ a ∈ (xs ++ [y]) ++ ys.take k.val,
          ∃ b ∈ (xs ++ [y]) ++ ys.take k.val,
            ys.get k = a &&& b ∨ ys.get k = a ||| b := by
        intro k
        simpa [List.append_assoc] using h k.succ
      obtain ⟨gs, hs, hgs, run⟩ := ih (xs ++ [y]) tail
      refine ⟨g :: gs, by simp [hs], ?_, fun r => ?_⟩
      · intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact hg
        · exact hgs _ hu
      · rw [List.foldl_cons, same, run]
        simp [List.append_assoc]

  -- Monotonicity follows the fold argument in the project LowMergeWires module.
  let LeL (a b : List Bool) : Prop := ∀ i, a.getD i false = true → b.getD i false = true

  have eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
      (f f' : ℕ → Bool) (h : ∀ i, f i = true → f' i = true) :
      op.eval (l.map f) = true → op.eval (l.map f') = true := by
    rcases hop with rfl | rfl
    · simp only [evalAnd, List.all_eq_true, List.mem_map, id]
      intro H x hx
      obtain ⟨i, hi, rfl⟩ := hx
      exact h i (H (f i) ⟨i, hi, rfl⟩)
    · simp only [evalOr, List.any_eq_true, List.mem_map, id]
      rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
      exact ⟨f' i, ⟨i, hi, rfl⟩, h i hx⟩

  have fold_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
      ∀ a b : List Bool, a.length = b.length → LeL a b →
        LeL (gs.foldl step a) (gs.foldl step b) := by
    induction gs with
    | nil => intro a b _ h; exact h
    | cons g gs ih =>
      intro a b hl h
      rw [List.foldl_cons, List.foldl_cons]
      apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
      · simp [step, hl]
      · intro i hi
        simp only [step] at hi ⊢
        by_cases hia : i < a.length
        · rw [List.getD_append _ _ _ _ hia] at hi
          rw [List.getD_append _ _ _ _ (by omega)]
          exact h i hi
        · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
          rw [List.getD_append_right _ _ _ _ (by omega)]
          rw [← hl]
          by_cases he : i - a.length = 0
          · rw [he] at hi ⊢
            simp only [List.getD_cons_zero] at hi ⊢
            exact eval_mono g.op (hgs g List.mem_cons_self) _ _ _ (fun k => h k) hi
          · obtain ⟨m, hm⟩ : ∃ m, i - a.length = m + 1 := ⟨i - a.length - 1, by omega⟩
            rw [hm] at hi; simp at hi

  -- Every true input contains a positive boundary row, and every false input is
  -- contained in a negative boundary row. This transfers the 24 tests to the full function.
  have extend (C : Circuit) (mono : Monotone2 C)
      (hits : ∀ i, C.eval (List.ofFn (bits (mask i))) = target.getLsbD i.val) :
      circuitFun 9 C = edge := by
    have cover : ∀ r : BitVec 9, ∃ i : Fin 24,
        target.getLsbD i.val = edge (bits r) ∧
        (if edge (bits r) then mask i &&& r = mask i else mask i &&& r = r) := by decide +kernel
    funext y
    let r : BitVec 9 := (BitVec.ofBoolListLE (List.ofFn y)).cast (by simp)
    have packed : bits r = y := by
      funext i
      simp only [bits, r, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
    obtain ⟨i, lab, sub⟩ := cover r
    have gateMono : PEqualNP.CircuitLowerBounds.IsMonotoneCircuit C := by
      intro g hg
      simpa using (mono g hg).1
    have cmp (a b : BitVec 9) (le : ∀ i : Fin 9, bits a i = true → bits b i = true) :
        C.eval (List.ofFn (bits a)) = true → C.eval (List.ofFn (bits b)) = true := by
      apply fold_mono C.gates gateMono _ _ (by simp)
      intro j hj
      by_cases h : j < 9
      · rw [List.getD_eq_getElem _ _ (by simpa), List.getElem_ofFn] at hj ⊢
        exact le ⟨j,h⟩ hj
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using Nat.le_of_not_gt h)] at hj
        contradiction
    change C.eval (List.ofFn y) = edge y
    rw [← packed]
    have hit := (hits i).trans lab
    cases e : edge (bits r)
    · simp only [e, Bool.false_eq_true, ite_false] at sub
      cases h : C.eval (List.ofFn (bits r)) with
      | false => rfl
      | true =>
        have rel (j : Fin 9) : bits r j = true → bits (mask i) j = true := by
          have eq := congrArg (fun v : BitVec 9 => v.getLsbD j.val) sub
          change ((mask i &&& r).getLsbD j.val) = r.getLsbD j.val at eq
          rw [BitVec.getLsbD_and] at eq
          simp only [bits]
          intro hr
          simpa [hr] using eq
        have h' := cmp _ _ rel h
        rw [hit, e] at h'
        contradiction
    · simp only [e, ite_true] at sub
      apply cmp (mask i) r _ (hit.trans e)
      intro j hj
      have eq := congrArg (fun v : BitVec 9 => v.getLsbD j.val) sub
      change ((mask i &&& r).getLsbD j.val) = (mask i).getLsbD j.val at eq
      rw [BitVec.getLsbD_and] at eq
      change (mask i).getLsbD j.val = true at hj
      change r.getLsbD j.val = true
      simpa [hj] using eq
  intro b hb xs seed out ops
  have tag : b = (12288 : BitVec 24) := List.mem_singleton.mp hb
  subst b
  let inputs : List (BitVec 24) :=
    [202052,276515,549652,1097833,101010,10616859,4456668,2624736,13635328,751444,12288]
  let first : List Gate := [⟨.or,[0,2]⟩,⟨.and,[1,9]⟩]
  change target ∈ inputs ++ xs at out
  have indexed : ∀ i : Fin xs.length, ∃ a ∈ inputs ++ xs.take i.val,
      ∃ b ∈ inputs ++ xs.take i.val, xs.get i = a &&& b ∨ xs.get i = a ||| b := ops
  obtain ⟨gs, len, wf, run⟩ := extract inputs xs indexed
  obtain ⟨o, ho, value⟩ := List.mem_iff_getElem.mp out
  let C : Circuit := ⟨first ++ gs, o⟩
  have mono : Monotone2 C := by
    intro g hg
    change g ∈ first ++ gs at hg
    rcases List.mem_append.mp hg with hg | hg
    · simp [first] at hg
      rcases hg with rfl | rfl <;> simp
    · exact wf g hg
  have hits (i : Fin 24) : C.eval (List.ofFn (bits (mask i))) = target.getLsbD i.val := by
    have table : ∀ i : Fin 24, first.foldl step (List.ofFn (bits (mask i))) =
        inputs.map (val i.val) := by decide +kernel
    change (((first ++ gs).foldl step _).getD o false) = _
    rw [List.foldl_append, table, run, List.getD_eq_getElem _ _ (by simpa using ho),
      List.getElem_map, value]
  have eqFun := extend C mono hits
  by_contra hlen
  have small : C.size ≤ 15 := by
    change (first ++ gs).length ≤ 15
    simp only [List.length_append,first,List.length_cons,List.length_nil,len]
    omega
  by_cases good : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = GateOp.and →
      ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD (9+j) false = true →
        C.eval (List.ofFn x) = true
  · have bound := clean C mono (fun x => congrFun eqFun x) good
    omega
  · push Not at good
    obtain ⟨j,g,hj,hg,x,hx,bad⟩ := good
    have wrong : C.eval (List.ofFn x) = false := by
      cases e : C.eval (List.ofFn x)
      · rfl
      · exact False.elim (bad e)
    have fan : FanInTwo C := by
      intro g hg
      obtain ⟨op, arity⟩ := mono g hg
      exact ⟨by simpa using (show g.op = .and ∨ g.op = .or ∨ g.op = .not from
        (show g.op = .and ∨ g.op = .or from by simpa using op).imp_right Or.inl), arity⟩
    obtain ⟨exactSize,last,live⟩ := cardinalShape C fan eqFun small
    obtain ⟨z, hz⟩ := unclean C mono exactSize last live rfl rfl ⟨j,g,x,hj,hg,hx,wrong⟩
    exact hz (congrFun eqFun z)
