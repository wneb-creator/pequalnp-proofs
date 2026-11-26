import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

-- The AND-trace argument is adapted from L_meta_7025 and the reduction R_meta_7027_1.
-- Distinct sets of incident lines give incompatible rejecting inputs.
set_option maxRecDepth 2048 in
theorem PEqualNP.Outside.R_meta_7027_2
    (hCount : ∃ (x1 : Fin (16385 : ℕ) → Finset (Fin (21 : ℕ))), Function.Injective fun (x2 : Fin (16385 : ℕ)) (x3 : Fin (21 : ℕ)) => ∃ x4 ∈ x1 x2, ∃ (x5 : Fin (5 : ℕ)), x4 + ![(20 : Fin (21 : ℕ)), (0 : Fin (21 : ℕ)), (5 : Fin (21 : ℕ)), (7 : Fin (21 : ℕ)), (17 : Fin (21 : ℕ))] x5 = x3)
    (hRest : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (42 : ℕ)) (x5 : Fin (42 : ℕ)), (↑x4, ↑x5) ∈ List.flatMap (fun (x6 : ℕ) => [(x6, (21 : ℕ) + (x6 + (20 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + x6), (x6, (21 : ℕ) + (x6 + (5 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (7 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (17 : ℕ)) % (21 : ℕ))]) (List.range (21 : ℕ)) ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) → (15 : ℕ) ≤ {x4 : Fin x1.gates.length | (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard → {x5 : Fin x1.gates.length | (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard ≤ (20 : ℕ) → (21 : ℕ) ≤ {x6 : Fin x1.gates.length | (x1.gates.get x6).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (42 : ℕ)) (x5 : Fin (42 : ℕ)), (↑x4, ↑x5) ∈ List.flatMap (fun (x6 : ℕ) => [(x6, (21 : ℕ) + (x6 + (20 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + x6), (x6, (21 : ℕ) + (x6 + (5 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (7 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (17 : ℕ)) % (21 : ℕ))]) (List.range (21 : ℕ)) ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) → (11 : ℕ) ≤ {x4 : Fin x1.gates.length | (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard → {x5 : Fin x1.gates.length | (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard ≤ (20 : ℕ) → (21 : ℕ) ≤ {x6 : Fin x1.gates.length | (x1.gates.get x6).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard := by
  classical
  intro x1 hm hc h11 h20
  let isAnd : Gate → Bool := fun g =>
    GateOp.rec (motive := fun _ => Bool) true false false (fun _ => false) false g.op
  have isAnd_iff : ∀ g : Gate, isAnd g = true ↔ g.op = .and := by
    intro g
    cases g with
    | mk op ins => cases op <;> simp [isAnd]
  let gateValue : Gate → List Bool → Bool := fun g w =>
    g.op.eval (g.inputs.map fun i => w.getD i false)
  let step : List Bool → Gate → List Bool := fun w g =>
    w ++ [gateValue g w]
  let trace : List Gate → List Bool → List Bool :=
    List.rec (fun _ => []) (fun g _ ih w =>
      if isAnd g then w.getD (g.inputs.headD w.length) false :: ih (step w g)
      else ih (step w g))
  have traceLength : ∀ (gs : List Gate) (w : List Bool),
      (trace gs w).length = gs.countP isAnd := by
    intro gs
    induction gs with
    | nil => intro w; rfl
    | cons g gs ih =>
      intro w
      change (if isAnd g then w.getD (g.inputs.headD w.length) false :: trace gs (step w g)
        else trace gs (step w g)).length = (g :: gs).countP isAnd
      rw [List.countP_cons]
      split <;> simp [ih]
  have count_eq : x1.gates.countP isAnd =
      {i : Fin x1.gates.length | (x1.gates.get i).op = GateOp.and}.ncard := by
    let S := Finset.univ.filter (fun i : Fin x1.gates.length => isAnd (x1.gates.get i) = true)
    have hs : (S : Set (Fin x1.gates.length)) = {i | (x1.gates.get i).op = .and} := by
      ext i
      simp [S, isAnd_iff]
    rw [← hs, Set.ncard_coe_finset]
    calc
      x1.gates.countP isAnd = (List.ofFn x1.gates.get).countP isAnd :=
        congrArg (List.countP isAnd) (List.ofFn_get x1.gates).symm
      _ = S.card := List.countP_ofFn x1.gates.get isAnd
  let Bounds : List Bool → List Bool → List Bool → Prop := fun a b z =>
    ∀ i, z.getD i false = true → a.getD i false = true ∨ b.getD i false = true
  have bounds_append : ∀ {a b z : List Bool}, a.length = z.length → b.length = z.length →
      Bounds a b z → ∀ {x y t : Bool}, (t = true → x = true ∨ y = true) →
      Bounds (a ++ [x]) (b ++ [y]) (z ++ [t]) := by
    intro a b z ha hb h x y t hbit i
    by_cases hi : i < z.length
    · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (ha ▸ hi),
        List.getD_append _ _ _ _ (hb ▸ hi)]
      exact h i
    · rw [List.getD_append_right _ _ _ _ (by omega : z.length ≤ i),
        List.getD_append_right _ _ _ _ (by omega : a.length ≤ i),
        List.getD_append_right _ _ _ _ (by omega : b.length ≤ i), ha, hb]
      cases i - z.length with
      | zero => simpa using hbit
      | succ n => simp
  have andEval (bs : List Bool) : GateOp.and.eval bs = bs.all id := rfl
  have orEval (bs : List Bool) : GateOp.or.eval bs = bs.any id := rfl
  have and_bounds : ∀ {ins : List Nat}, ins.length ≤ 2 →
      ∀ {a b z : List Bool}, Bounds a b z →
      a.getD (ins.headD a.length) false = b.getD (ins.headD b.length) false →
      gateValue ⟨.and, ins⟩ z = true →
        gateValue ⟨.and, ins⟩ a = true ∨ gateValue ⟨.and, ins⟩ b = true := by
    intro ins hlen a b z h heq
    rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, ks⟩⟩⟩
    · simp [gateValue, andEval]
    · simpa [gateValue, andEval] using h i
    · simp only [List.headD_cons] at heq
      simp only [gateValue, andEval, List.map_cons, List.map_nil, List.all_cons,
        List.all_nil, id_eq, Bool.and_true, Bool.and_eq_true]
      rintro ⟨hi, hj⟩
      have ha : a.getD i false = true := (h i hi).elim id (fun hb => heq.trans hb)
      have hb : b.getD i false = true := heq.symm.trans ha
      exact (h j hj).imp (fun hja => ⟨ha, hja⟩) (fun hjb => ⟨hb, hjb⟩)
    · simp at hlen
  have or_bounds : ∀ {ins : List Nat} {a b z : List Bool}, Bounds a b z →
      gateValue ⟨.or, ins⟩ z = true →
        gateValue ⟨.or, ins⟩ a = true ∨ gateValue ⟨.or, ins⟩ b = true := by
    intro ins a b z h
    simp only [gateValue, orEval, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨_, ⟨i, hi, rfl⟩, hz⟩
    exact (h i hz).imp (fun ha => ⟨_, ⟨i, hi, rfl⟩, ha⟩)
      (fun hb => ⟨_, ⟨i, hi, rfl⟩, hb⟩)
  have runBounds : ∀ (gs : List Gate),
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      ∀ (a b z : List Bool), a.length = z.length → b.length = z.length →
      Bounds a b z → trace gs a = trace gs b →
      Bounds (gs.foldl step a) (gs.foldl step b) (gs.foldl step z) := by
    intro gs
    induction gs with
    | nil =>
      intro _ a b z _ _ h _
      exact h
    | cons g gs ih =>
      intro hmgs a b z ha hb h ht
      obtain ⟨hop, hlen⟩ := hmgs g (by simp)
      have htail : ∀ k ∈ gs,
          k.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ k.inputs.length ≤ 2 :=
        fun k hk => hmgs k (List.mem_cons_of_mem _ hk)
      rcases g with ⟨op, ins⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      rcases hop with rfl | rfl
      · change (if isAnd ⟨.and, ins⟩ then a.getD (ins.headD a.length) false :: trace gs (step a ⟨.and, ins⟩)
          else trace gs (step a ⟨.and, ins⟩)) =
          (if isAnd ⟨.and, ins⟩ then b.getD (ins.headD b.length) false :: trace gs (step b ⟨.and, ins⟩)
          else trace gs (step b ⟨.and, ins⟩)) at ht
        simp only [isAnd, ite_true, List.cons.injEq] at ht
        exact ih htail _ _ _ (by simp [step, ha]) (by simp [step, hb])
          (bounds_append ha hb h (and_bounds hlen h ht.1)) ht.2
      · change (if isAnd ⟨.or, ins⟩ then a.getD (ins.headD a.length) false :: trace gs (step a ⟨.or, ins⟩)
          else trace gs (step a ⟨.or, ins⟩)) =
          (if isAnd ⟨.or, ins⟩ then b.getD (ins.headD b.length) false :: trace gs (step b ⟨.or, ins⟩)
          else trace gs (step b ⟨.or, ins⟩)) at ht
        simp only [isAnd, Bool.false_eq_true, ite_false] at ht
        exact ih htail _ _ _ (by simp [step, ha]) (by simp [step, hb])
          (bounds_append ha hb h (or_bounds h)) ht
  have evalBounds : ∀ (a b : Fin 42 → Bool),
      trace x1.gates (List.ofFn a) = trace x1.gates (List.ofFn b) →
      x1.eval (List.ofFn fun i => a i || b i) = true →
      x1.eval (List.ofFn a) = true ∨ x1.eval (List.ofFn b) = true := by
    intro a b ht hz
    have h : Bounds (List.ofFn a) (List.ofFn b) (List.ofFn fun i => a i || b i) := by
      intro i hi
      by_cases hi' : i < 42
      · rw [List.getD_eq_getElem _ _ (by simpa using hi'), List.getElem_ofFn] at hi
        rw [List.getD_eq_getElem _ _ (by simpa using hi'), List.getElem_ofFn,
          List.getD_eq_getElem _ _ (by simpa using hi'), List.getElem_ofFn]
        simpa using hi
      · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi')] at hi
        cases hi
    exact runBounds x1.gates hm _ _ _ (by simp) (by simp) h ht x1.output hz
  let point : Fin 21 → Fin 42 := Fin.castAdd 21
  let line : Fin 21 → Fin 42 := Fin.natAdd 21
  let offset : Fin 5 → Fin 21 := ![20, 0, 5, 7, 17]
  let Inc : Fin 21 → Fin 21 → Prop := fun p l => ∃ i, p + offset i = l
  let edgesAt : Nat → List (Nat × Nat) := fun p =>
    [(p, 21 + (p + 20) % 21), (p, 21 + p), (p, 21 + (p + 5) % 21),
     (p, 21 + (p + 7) % 21), (p, 21 + (p + 17) % 21)]
  let edges : List (Nat × Nat) := (List.range 21).flatMap edgesAt
  have edgesAt_point : ∀ p : Fin 21,
      edgesAt p.val = List.ofFn (fun i => ((point p).val, (line (p + offset i)).val)) := by
    intro p
    simp [edgesAt, List.ofFn_succ, point, line, offset, Fin.val_add,
      Nat.mod_eq_of_lt p.isLt, Nat.add_comm 21]
  have edge_forward : ∀ {u v : Fin 42}, (u.val, v.val) ∈ edges →
      ∃ p l, u = point p ∧ v = line l ∧ Inc p l := by
    intro u v h
    obtain ⟨n, hn, hm2⟩ := List.mem_flatMap.mp h
    let p : Fin 21 := ⟨n, List.mem_range.mp hn⟩
    change (u.val, v.val) ∈ edgesAt p.val at hm2
    rw [edgesAt_point, List.mem_ofFn] at hm2
    obtain ⟨i, hi⟩ := hm2
    exact ⟨p, p + offset i, Fin.ext (congrArg Prod.fst hi).symm,
      Fin.ext (congrArg Prod.snd hi).symm, i, rfl⟩
  have edge_backward : ∀ {p l : Fin 21}, Inc p l →
      ((point p).val, (line l).val) ∈ edges := by
    intro p l h
    obtain ⟨i, rfl⟩ := h
    refine List.mem_flatMap.mpr ⟨p.val, List.mem_range.mpr p.isLt, ?_⟩
    rw [edgesAt_point, List.mem_ofFn]
    exact ⟨i, rfl⟩
  let input : Finset (Fin 21) → Fin 42 → Bool := fun P v =>
    decide ((∃ p ∈ P, point p = v) ∨ (∃ l, line l = v ∧ ∀ q ∈ P, ¬ Inc q l))
  have point_inj : Function.Injective point :=
    fun _ _ h => Fin.ext (congrArg (fun v : Fin 42 => v.val) h)
  have line_inj : Function.Injective line := by
    intro a b h
    apply Fin.ext
    have hv := congrArg Fin.val h
    change 21 + a.val = 21 + b.val at hv
    omega
  have point_ne_line : ∀ (p l : Fin 21), point p ≠ line l := by
    intro p l h
    have hv := congrArg Fin.val h
    change p.val = 21 + l.val at hv
    omega
  have input_point : ∀ (P : Finset (Fin 21)) (p : Fin 21),
      input P (point p) = true ↔ p ∈ P := by
    intro P p
    simp only [input, decide_eq_true_eq]
    constructor
    · rintro (⟨q, hq, he⟩ | ⟨l, he, _⟩)
      · exact (point_inj he) ▸ hq
      · exact (point_ne_line p l he.symm).elim
    · exact fun h => Or.inl ⟨p, h, rfl⟩
  have input_line : ∀ (P : Finset (Fin 21)) (l : Fin 21),
      input P (line l) = true ↔ ∀ q ∈ P, ¬ Inc q l := by
    intro P l
    simp only [input, decide_eq_true_eq]
    constructor
    · rintro (⟨p, _, he⟩ | ⟨k, he, h⟩)
      · exact (point_ne_line p l he).elim
      · exact (line_inj he) ▸ h
    · exact fun h => Or.inr ⟨l, rfl, h⟩
  have negative : ∀ P : Finset (Fin 21), x1.eval (List.ofFn (input P)) ≠ true := by
    intro P h
    obtain ⟨u, v, he, hu, hv⟩ := (hc _).mp h
    obtain ⟨p, l, rfl, rfl, hi⟩ := edge_forward he
    exact (input_line P l).mp hv p ((input_point P p).mp hu) hi
  obtain ⟨f, hdist⟩ := hCount
  let neigh (P : Finset (Fin 21)) := Finset.univ.filter (fun l : Fin 21 => ∃ p ∈ P, Inc p l)
  have distinct : Function.Injective (fun i => neigh (f i)) := by
    intro i j h
    apply hdist
    funext l
    apply propext
    simpa only [neigh, Finset.mem_filter, Finset.mem_univ, true_and, Inc, offset] using (Finset.ext_iff.mp h l)
  have oneSide : ∀ (P Q : Finset (Fin 21)) (l : Fin 21), l ∈ neigh P → l ∉ neigh Q →
      ∃ p, Inc p l ∧ input P (point p) = true ∧ input Q (line l) = true := by
    intro P Q l hP hQ
    obtain ⟨p, hp, hpl⟩ := (Finset.mem_filter.mp hP).2
    exact ⟨p, hpl, (input_point _ _).mpr hp, (input_line _ _).mpr
      (fun q hq h => hQ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, q, hq, h⟩))⟩
  have union_positive : ∀ {i j : Fin 16385}, i ≠ j →
      x1.eval (List.ofFn fun v => input (f i) v || input (f j) v) = true := by
    intro i j hij
    have hdiff : ∃ l, ¬ (l ∈ neigh (f i) ↔ l ∈ neigh (f j)) := by
      by_contra! he
      exact hij (distinct (Finset.ext he))
    obtain ⟨l, hl⟩ := hdiff
    apply (hc _).mpr
    by_cases hi : l ∈ neigh (f i)
    · have hj : l ∉ neigh (f j) := fun hj => hl ⟨fun _ => hj, fun _ => hi⟩
      obtain ⟨p, hp, ha, hb⟩ := oneSide _ _ l hi hj
      exact ⟨point p, line l, edge_backward hp, by simp [ha], by simp [hb]⟩
    · have hj : l ∈ neigh (f j) := by
        by_contra hn
        exact hl ⟨fun h => (hi h).elim, fun h => (hn h).elim⟩
      obtain ⟨p, hp, ha, hb⟩ := oneSide _ _ l hj hi
      exact ⟨point p, line l, edge_backward hp, by simp [ha], by simp [hb]⟩
  let k := x1.gates.countP isAnd
  let T (i : Fin 16385) (b : Fin k) := (trace x1.gates (List.ofFn (input (f i)))).getD b.val false
  have hinj : Function.Injective T := by
    intro i j he
    by_contra hn
    have plen := traceLength x1.gates (List.ofFn (input (f i)))
    have qlen := traceLength x1.gates (List.ofFn (input (f j)))
    have ht : trace x1.gates (List.ofFn (input (f i))) =
        trace x1.gates (List.ofFn (input (f j))) := by
      apply List.ext_getElem (plen.trans qlen.symm)
      intro b hi hj
      have hz := congrFun he (⟨b, by simpa only [k, ← plen] using hi⟩ : Fin k)
      simpa only [T, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] using hz
    exact (evalBounds _ _ ht (union_positive hn)).elim (negative _) (negative _)
  have hcard := Fintype.card_le_of_injective T hinj
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hcard
  apply hRest x1 hm hc _ h20
  rw [← count_eq]
  change 15 ≤ k
  by_contra! hk
  have hpow : 2 ^ k ≤ 2 ^ 14 := Nat.pow_le_pow_right (by decide) (by omega)
  omega
