import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The insertion simulation is adapted from R_meta_3614_2 and PR 10212.
set_option maxRecDepth 3500 in
set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.R_meta_2806_606
    (pin : ∀ (n : ℕ) (D : Circuit) (w : List (Option (Fin n))) (i : ℕ),
  let X := fun y : Fin n → Bool => w.map fun p => p.elim false y
  let r := fun g : Gate => (if g.op.eval [false] then g.inputs.take 1 else g.inputs).contains i
  FanInTwo D → w[i]? = some none →
  (∃ a b : List Bool, a.length = w.length ∧ b.length = w.length ∧
    (∀ j, j ≠ i → a.getD j false = b.getD j false) ∧ D.eval a ≠ D.eval b) →
  (∃ a b, D.eval (X a) ≠ D.eval (X b)) →
  ∀ k : ℕ, (k ≤ (D.gates.filter r).length ∨ k = 1 ∨
    k = 2 ∧ ∀ g ∈ D.gates, g.op = GateOp.or → i ∉ g.inputs) →
  ∃ E : Circuit, FanInTwo E ∧ E.size+k ≤ D.size ∧
    ∀ y, E.eval (List.ofFn y) = D.eval (X y))
    (minor : ¬PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) (fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ))) (12 : ℕ))
    (paid : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x3 ++ [x3 (0 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ))]) = (x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)))) → (13 : ℕ) ≤ List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => !x4.op.eval [Bool.false]) x1.gates)
    (remaining : let F := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))); let R := fun (g : Gate) => (if g.op.eval [false] then g.inputs.take 1 else g.inputs).contains 6; ∀ (C : Circuit) (v : Fin 9), FanInTwo C → C.size = 14 → C.output = 23 → v ≠ 0 → v ≠ 6 → (C.gates.filter (fun h => h.inputs.contains v.val)).length = 1 → (∃ h : Gate, h.op = GateOp.or ∧ C.gates.filter R = [h]) → C.gates.countP (fun g => g.op.eval [false]) ≤ 1 → ∃ x, C.eval (List.ofFn x ++ [x 0 || x 6]) ≠ F x)
    : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); have x2 : (Fin (9 : ℕ) → Bool) → List Bool := fun (x2 : Fin (9 : ℕ) → Bool) => List.ofFn x2 ++ [x2 (0 : Fin (9 : ℕ)) || x2 (6 : Fin (9 : ℕ))]; ∀ (x3 : Fin (9 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate),   x3 ≠ (0 : Fin (9 : ℕ)) →     x3 ≠ (6 : Fin (9 : ℕ)) →       PEqualNP.MetaComplexity.FanInTwo x4 →         x4.size ≤ (13 : ℕ) →           (10 : ℕ) ≤ x5 →             x5 ≤ (10 : ℕ) + x4.size →               x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.not →                 x6.inputs.length ≤ (2 : ℕ) →                   ↑x3 ∈ x6.inputs →                     (∀ x16 ∈ List.take (x5 - (10 : ℕ)) x4.gates, ↑x3 ∉ x16.inputs) →                       ∃ (x17 : Fin (9 : ℕ) → Bool),                         have x18 : List Bool := x2 x17;                         x4.eval (x18.set (↑x3) (x6.op.eval (List.map (fun (x19 : ℕ) => if x19 < x5 then (x4.wires x18).getD x19 Bool.false else Bool.false) x6.inputs))) ≠ x1 x17 := by
  let emit (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  let redirect (v k i : ℕ) : ℕ := if i = v then k else if i < k then i else i + 1

  let maskRename (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩

  have fold_size (gs : List Gate) (w : List Bool) : (gs.foldl emit w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih => rw [List.foldl_cons,ih]; simp [emit]; omega

  have fold_preserves (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl emit w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons,ih (emit w g) (by simp [emit]; omega)]
      exact List.getD_append _ _ _ _ hi

  have set_emit_avoid (g : Gate) (w : List Bool) (v : ℕ) (val : Bool)
      (hv : v < w.length) (avoid : v ∉ g.inputs) :
      emit (w.set v val) g = (emit w g).set v val := by
    have reads : ∀ i ∈ g.inputs, (w.set v val).getD i false = w.getD i false := by
      intro i hi
      have ne : v ≠ i := by intro eq; apply avoid; exact eq ▸ hi
      by_cases valid : i < w.length
      · rw [List.getD_eq_getElem _ _ (by simpa using valid),List.getD_eq_getElem _ _ valid,
          List.getElem_set_ne ne]
      · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt valid),
          List.getD_eq_default _ _ (Nat.le_of_not_gt valid)]
    unfold emit
    rw [List.map_congr_left reads,List.set_append_left v val hv]

  have fold_set_avoid (gs : List Gate) (w : List Bool) (v : ℕ) (val : Bool)
      (hv : v < w.length) (avoid : ∀ g ∈ gs, v ∉ g.inputs) :
      gs.foldl emit (w.set v val) = (gs.foldl emit w).set v val := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.foldl_cons]
      rw [set_emit_avoid g w v val hv (avoid g (by simp))]
      exact ih (emit w g) (by simp [emit]; omega) (fun a ha => avoid a (by simp [ha]))

  have append_other (w : List Bool) (b : Bool) (i : ℕ) (ne : i ≠ w.length) :
      (w++[b]).getD i false = w.getD i false := by
    by_cases small : i < w.length
    · exact List.getD_append _ _ _ _ small
    · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]

  have suffix_shift (gs : List Gate) (v k : ℕ) (w y : List Bool)
      (hv : v < k) (hk : k ≤ w.length) (len : y.length = w.length + 1)
      (rel : ∀ i, y.getD (redirect v k i) false = w.getD i false) :
      ∀ i, ((gs.map (maskRename (redirect v k))).foldl emit y).getD (redirect v k i) false =
        (gs.foldl emit w).getD i false := by
    induction gs generalizing w y with
    | nil => exact rel
    | cons g gs ih =>
      simp only [List.map_cons,List.foldl_cons]
      let value := g.op.eval (g.inputs.map fun i => w.getD i false)
      have emitY : emit y (maskRename (redirect v k) g) = y ++ [value] := by
        change y ++ [g.op.eval ((g.inputs.map (redirect v k)).map fun i => y.getD i false)] = _
        simp only [List.map_map,Function.comp_def]
        rw [List.map_congr_left (fun i _ => rel i)]
      rw [emitY]
      apply ih (w++[value]) (y++[value])
      · simp; omega
      · simp [len]
      intro i
      have sameWire : redirect v k i = y.length ↔ i = w.length := by
        by_cases eq : i = v
        · simp only [redirect]
          rw [ite_eq_left eq]
          omega
        · simp only [redirect]
          rw [ite_eq_right eq]
          split <;> omega
      by_cases hi : i = w.length
      · rw [sameWire.mpr hi,hi]
        simp
      · rw [append_other _ _ _ (fun a => hi (sameWire.mp a)),append_other _ _ _ hi]
        exact rel i

  have append_with_mask (v : ℕ) (old : List Bool) (hv : v < old.length) (bit : Bool) :
      ∀ i, (old ++ [bit]).getD (redirect v old.length i) false = (old.set v bit).getD i false := by
    intro i
    by_cases piv : i = v
    · subst i
      simp only [redirect, ite_true]
      rw [List.getD_append_right _ _ _ _ le_rfl,Nat.sub_self,List.getD_cons_zero,
        List.getD_eq_getElem _ _ (by simp; exact hv)]
      simp
    simp only [redirect]
    rw [ite_eq_right piv]
    by_cases valid : i < old.length
    · rw [ite_eq_left valid,List.getD_append _ _ _ _ valid,List.getD_eq_getElem _ _ valid,
        List.getD_eq_getElem _ _ (by simpa using valid),List.getElem_set_ne (Ne.symm piv)]
    · rw [ite_eq_right valid,List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp; omega)]

  let replacement (C : Circuit) (xs : List Bool) (cut : ℕ) (g : Gate) : Bool :=
    g.op.eval (g.inputs.map fun i => if i < cut then (C.wires xs).getD i false else false)

  have compile (C : Circuit) (cut v : ℕ) (g : Gate) (hv : v < 10)
      (lo : 10 ≤ cut) (hi : cut ≤ 10 + C.size) (legal : FanInTwo C)
      (op : g.op = .and ∨ g.op = .or ∨ g.op = .not) (arity : g.inputs.length ≤ 2)
      (reads : v ∈ g.inputs)
      (avoids : ∀ h ∈ C.gates.take (cut - 10), v ∉ h.inputs) :
      ∃ D : Circuit, FanInTwo D ∧ D.size = C.size + 1 ∧ (D.gates.filter (fun h => h.inputs.contains v)) = [g] ∧
        ∀ xs : List Bool, xs.length = 10 → D.eval xs = C.eval (xs.set v (replacement C xs cut g)) := by
    let pre := C.gates.take (cut - 10)
    let suf := C.gates.drop (cut - 10)
    let shift := maskRename (redirect v cut)
    let D : Circuit := ⟨pre ++ g :: suf.map shift, redirect v cut C.output⟩
    have split : pre ++ suf = C.gates := List.take_append_drop _ _
    have size : D.size = C.size + 1 := by
      have len := congrArg List.length split
      change (pre ++ g :: suf.map shift).length = C.gates.length + 1
      simp only [List.length_append, List.length_cons, List.length_map] at len ⊢
      omega
    have fan : FanInTwo D := by
      intro a ha
      change a ∈ pre ++ g :: suf.map shift at ha
      rcases List.mem_append.mp ha with hp | hs
      · exact legal a (by rw [← split]; exact List.mem_append_left _ hp)
      rcases List.mem_cons.mp hs with rfl | hm
      · exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using op, arity⟩
      obtain ⟨a, hSource, rfl⟩ := List.mem_map.mp hm
      obtain ⟨hop, hlen⟩ := legal a (by rw [← split]; exact List.mem_append_right _ hSource)
      exact ⟨hop, by simpa [shift,maskRename] using hlen⟩
    have clean : ∀ i, redirect v cut i ≠ v := by
      intro i
      dsimp only [redirect]
      split <;> first | omega | split <;> omega
    have noPre : pre.filter (fun h => h.inputs.contains v) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro h hh
      simpa using avoids h hh
    have noSuf : (suf.map shift).filter (fun h => h.inputs.contains v) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro h hh
      obtain ⟨src,_,rfl⟩ := List.mem_map.mp hh
      have hn : v ∉ (src.inputs.map (redirect v cut)) := by
        intro hvv
        obtain ⟨i,_,eq⟩ := List.mem_map.mp hvv
        exact clean i eq
      simpa [shift,maskRename] using hn
    have once : D.gates.filter (fun h => h.inputs.contains v) = [g] := by
      change (pre ++ g :: suf.map shift).filter _ = [g]
      rw [List.filter_append,noPre,List.filter_cons_of_pos (by simpa using reads),noSuf]
      rfl
    refine ⟨D, fan, size, once, ?_⟩
    intro xs hxs
    let old := pre.foldl emit xs
    have len : old.length = cut := by
      change (pre.foldl emit xs).length = cut
      have hcut : cut - 10 ≤ C.gates.length := by
        change cut ≤ 10 + C.gates.length at hi
        omega
      rw [fold_size]
      simp only [hxs,pre,List.length_take,min_eq_left hcut]
      omega
    have source (i : ℕ) : old.getD i false =
        if i < cut then (C.wires xs).getD i false else false := by
      by_cases earlier : i < cut
      · rw [ite_eq_left earlier]
        change old.getD i false = (C.gates.foldl emit xs).getD i false
        rw [← split, List.foldl_append]
        exact (fold_preserves suf old i (by omega)).symm
      · rw [ite_eq_right earlier, List.getD_eq_default _ _ (by omega)]
    let bit := replacement C xs cut g
    have emitted : emit old g = old ++ [bit] := by
      change old ++ [g.op.eval (g.inputs.map fun i => old.getD i false)] = _
      simp only [bit,replacement,source]
    have stat : pre.foldl emit (xs.set v bit) = old.set v bit :=
      fold_set_avoid pre xs v bit (by omega) avoids
    have read (i : ℕ) : (old ++ [bit]).getD (redirect v cut i) false =
        (old.set v bit).getD i false := by
      rw [← len]
      exact append_with_mask v old (by omega) bit i
    have sim := suffix_shift suf v cut (old.set v bit) (old ++ [bit]) (by omega)
      (by simp [len]) (by simp) read C.output
    change ((pre ++ g :: suf.map shift).foldl emit xs).getD (redirect v cut C.output) false =
      (C.gates.foldl emit (xs.set v bit)).getD C.output false
    rw [List.foldl_append,List.foldl_cons,emitted,← split,List.foldl_append,stat]
    exact sim
  let F := fun x : Fin 9 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  let X := fun x : Fin 9 → Bool => List.ofFn x ++ [x 0 || x 6]
  let H := fun x : Fin 8 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 ||
    x 1 && x 5 || x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4
  let w : List (Option (Fin 8)) := [some 1,some 0,some 4,some 7,some 5,some 2,none,some 6,some 3,some 1]
  let L := fun (b : Bool) (y : Fin 8 → Bool) (i : Fin 9) =>
    [y 1,y 0,y 4,y 7,y 5,y 2,b,y 6,y 3].getD i.val false
  let R := fun g : Gate => (if g.op.eval [false] then g.inputs.take 1 else g.inputs).contains 6
  have bank : ∀ y, w.map (fun p => p.elim false y) = X (L false y) := by
    intro y
    simp [w,X,L,List.ofFn_succ, List.getD_eq_getElem?_getD]
  have low : ∀ y, F (L false y) = H y := by
    intro y
    change (y 1 && y 0 || y 0 && y 4 || y 4 && y 7 || y 7 && y 5 || y 5 && y 1 ||
      y 1 && y 2 || y 0 && false || y 4 && y 6 || y 7 && y 3 || y 2 && y 6 ||
      false && y 3 || y 3 && y 2) = _
    simp only [Bool.and_false,Bool.false_and,Bool.or_false,H]
    ac_rfl
  let p : Fin 8 → Bool := fun i => decide (i = 1 ∨ i = 3)
  have pair : (X (L false p)).length = w.length ∧ (X (L true p)).length = w.length ∧
      (∀ j, j ≠ 6 → (X (L false p)).getD j false = (X (L true p)).getD j false) ∧
      F (L false p) ≠ F (L true p) := by
    refine ⟨by simp [X,w],by simp [X,w],?_,by decide⟩
    intro j ne
    have eq : X (L true p) = (X (L false p)).set 6 true := by
      simp [X,L,p,List.ofFn_succ,List.getD_eq_getElem?_getD]
    simp only [eq,List.getD_eq_getElem?_getD,List.getElem?_set_ne (Ne.symm ne)]
  have lower (T : Circuit) (fan : FanInTwo T) (he : ∀ x, T.eval (X x) = F x)
      (s : ℕ) (budget : s ≤ (T.gates.filter R).length ∨ s = 1 ∨
        s = 2 ∧ ∀ g ∈ T.gates, g.op = GateOp.or → 6 ∉ g.inputs) : 13 + s ≤ T.size := by
    have pinned (y : Fin 8 → Bool) : T.eval (w.map fun q => q.elim false y) = H y := by
      rw [bank,he,low]
    obtain ⟨E,fanE,cost,sim⟩ := pin 8 T w 6 fan rfl
      ⟨_,_,pair.1,pair.2.1,pair.2.2.1,by rw [he,he]; exact pair.2.2.2⟩
      ⟨fun _ => false,fun _ => true,by dsimp only; rw [pinned,pinned]; decide⟩ s budget
    have lb : 13 ≤ E.size := by
      by_contra! h
      apply minor
      exact ⟨E,fanE,by omega,fun y => (sim y).trans (pinned y)⟩
    omega
  dsimp only
  intro v C cut g v0 v6 fan small lo hi op arity read avoid
  by_contra! good
  obtain ⟨D,hD,size,once,sim⟩ := compile C cut v.val g (by have := v.isLt; omega)
    lo hi fan op arity read avoid
  have agrees (x : Fin 9 → Bool) : D.eval (X x) = F x :=
    (sim (X x) (by simp [X])).trans (good x)
  have full : D.size = 14 := by
    have := lower D hD agrees 1 (Or.inr (Or.inl rfl))
    omega
  have output : D.output = 23 := by
    by_contra ne
    have length : D.gates.length = 14 := full
    have hn : D.gates ≠ [] := by intro h; simp [h] at length
    obtain ⟨pre,last,split⟩ : ∃ pre last, D.gates = pre ++ [last] :=
      ⟨_,_,(List.dropLast_concat_getLast hn).symm⟩
    have pLen : pre.length = 13 := by simpa [split] using length
    let E : Circuit := ⟨pre,D.output⟩
    have okE : FanInTwo E := fun h hh => hD h (by rw [split]; exact List.mem_append_left _ hh)
    have simE (x : Fin 9 → Bool) : E.eval (X x) = D.eval (X x) := by
      change (pre.foldl emit (X x)).getD D.output false = (D.gates.foldl emit (X x)).getD D.output false
      rw [split,List.foldl_append]
      have len : (pre.foldl emit (X x)).length = 23 := by rw [fold_size]; simp [X,pLen]
      exact (append_other _ _ _ (by omega)).symm
    have lb := lower E okE (fun x => (simE x).trans (agrees x)) 1 (Or.inr (Or.inl rfl))
    change 13 + 1 ≤ pre.length at lb
    omega
  have budget := lower D hD agrees (D.gates.filter R).length (Or.inl le_rfl)
  have found : ∃ h ∈ D.gates, h.op = GateOp.or ∧ 6 ∈ h.inputs := by
    by_contra! no
    have := lower D hD agrees 2 (Or.inr (Or.inr ⟨rfl,no⟩))
    omega
  obtain ⟨h,mem,tag,hr⟩ := found
  have hin : h ∈ D.gates.filter R := List.mem_filter.mpr ⟨mem,by
    dsimp only [R]
    rw [tag]
    change h.inputs.contains 6 = true
    simpa using hr⟩
  have only : D.gates.filter R = [h] := by
    cases he : D.gates.filter R with
    | nil => simp [he] at hin
    | cons a l =>
      cases l with
      | nil => simpa [he,eq_comm] using hin
      | cons b l => simp [he] at budget; omega
  have binary := paid D hD agrees
  have partition (gs : List Gate) : gs.countP (fun a => !a.op.eval [false]) +
      gs.countP (fun a => a.op.eval [false]) = gs.length := by
    induction gs with
    | nil => rfl
    | cons a gs ih => cases e : a.op.eval [false] <;> simp [e] <;> omega
  have tot := partition D.gates
  have base : D.gates.length = 14 := full
  obtain ⟨x,bad⟩ := remaining D v hD full output v0 v6 (by rw [once]; rfl)
    ⟨h,tag,only⟩ (by omega)
  apply bad
  have same : ∀ z : Fin 9 → Bool, F z =
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any (fun e => z (Fin.ofNat 9 (e / 10)) && z (Fin.ofNat 9 (e % 10))) := by
    intro z
    simp only [List.any_cons,List.any_nil,Bool.or_false,F,Bool.or_assoc]
    rfl
  exact (agrees x).trans (same x)
