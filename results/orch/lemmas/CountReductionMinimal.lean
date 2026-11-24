import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5282_43
    (andBound : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
      (∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) →
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.IsMinimalMonoCircuit n C →
        PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
        ∃ T : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G T ∧
          T.card ≤ C.gates.countP (fun g => match g.op with
            | PEqualNP.CircuitLowerBounds.GateOp.and => true
            | _ => false))
    (orBound : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
      (∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) →
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.IsMinimalMonoCircuit n C →
        PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
        G.edgeFinset.card ≤ C.gates.countP (fun g => match g.op with
          | PEqualNP.CircuitLowerBounds.GateOp.or => true
          | _ => false) + 1)
    : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj],   have x4 : (Fin x1 → Bool) → Bool := fun (x4 : Fin x1 → Bool) => Decidable.decide (∃ (x5 : Fin x1) (x6 : Fin x1), x2.Adj x5 x6 ∧ x4 x5 = Bool.true ∧ x4 x6 = Bool.true);   have x5 : Finset (Fin x1) → Fin x1 → Bool := fun (x5 : Finset (Fin x1)) (x6 : Fin x1) => Decidable.decide (x6 ∈ x5);   have x6 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x7]? = Option.some x8 → x8.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x11 : Finset (Fin x1)), x11.card ≤ (1 : ℕ) → (x6.wires (List.ofFn (x5 x11))).getD (x1 + x7) Bool.false = Bool.false;   (∀ (x7 x8 x9 : Fin x1), x2.Adj x7 x8 → x2.Adj x8 x9 → ¬x2.Adj x9 x7) → (∀ (x8 x9 x10 x11 : Fin x1), x2.Adj x8 x9 → x2.Adj x9 x10 → x2.Adj x10 x11 → x2.Adj x11 x8 → x8 = x10 ∨ x9 = x11) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x9 ∧ (∀ (x10 : Fin x1 → Bool), x9.eval (List.ofFn x10) = x4 x10) ∧ (∀ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 → (∀ (x12 : Fin x1 → Bool), x10.eval (List.ofFn x12) = x4 x12) → x9.size ≤ x10.size) ∧ x6 x9 := by
  classical
  let wiresFrom (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) : List Bool :=
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

  have wires_eq (C : PEqualNP.CircuitLowerBounds.Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

  have wiresFrom_append (gs gs' : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) :
      wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
    simp [wiresFrom, List.foldl_append]

  have wiresFrom_prefix (gs : List PEqualNP.CircuitLowerBounds.Gate) : ∀ w : List Bool,
      ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
    induction gs with
    | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
    | cons g gs ih =>
      intro w
      obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
      have : wiresFrom (g :: gs) w
          = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
      rw [this, ht]; simp

  have length_wiresFrom (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) :
      (wiresFrom gs w).length = w.length + gs.length := by
    obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
    rw [ht]; simp [hl]

  have getD_wiresFrom (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
      (wiresFrom gs w).getD i false = w.getD i false := by
    obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
    rw [ht, List.getD_append _ _ _ _ h]

  have getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
    simp

  have getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
      (List.ofFn x).getD (i : ℕ) false = x i := by simp

  let Ok (g : PEqualNP.CircuitLowerBounds.Gate) : Prop :=
    g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2

  let Safe (n m : ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate) : Prop :=
    ∀ w : List Bool, w.length = m → PEqualNP.InvisibleWire.IsLight n (fun i => w.getD i false) →
      ∀ j g, gs[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (wiresFrom gs w).getD (m + j) false = false

  have safe_append {n m : ℕ} {gs hs : List PEqualNP.CircuitLowerBounds.Gate} (hm : n ≤ m)
      (sg : Safe n m gs) (sh : Safe n (m + gs.length) hs) : Safe n m (gs ++ hs) := by
    intro w hw light j g entry op
    rw [wiresFrom_append]
    by_cases old : j < gs.length
    · have eg : gs[j]? = some g := by
        rwa [List.getElem?_append_left old] at entry
      rw [getD_wiresFrom _ _ _ (by rw [length_wiresFrom, hw]; omega)]
      exact sg w hw light j g eg op
    · have eh : hs[j - gs.length]? = some g := by
        rwa [List.getElem?_append_right (by omega)] at entry
      have agree : (fun i : Fin n => (wiresFrom gs w).getD i false) =
          (fun i : Fin n => w.getD i false) := by
        funext i
        exact getD_wiresFrom _ _ _ (by have := i.isLt; omega)
      have hl : PEqualNP.InvisibleWire.IsLight n (fun i => (wiresFrom gs w).getD i false) := by
        rwa [agree]
      have h := sh (wiresFrom gs w) (by rw [length_wiresFrom, hw]) hl
        (j - gs.length) g eh op
      have eq : m + gs.length + (j - gs.length) = m + j := by omega
      rwa [eq] at h

  let Bld (n : ℕ) (F : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
    ∀ m, n ≤ m → ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ (∀ g ∈ gs, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) ∧ gs.length ≤ s ∧
      out < m + gs.length ∧ (∀ w : List Bool, w.length = m →
        (wiresFrom gs w).getD out false = F (fun i => w.getD i false)) ∧ Safe n m gs

  have bld_mono {n : ℕ} {F : (Fin n → Bool) → Bool} {s s' : ℕ} (h : Bld n F s) (hs : s ≤ s') :
      Bld n F s' := by
    intro m hm
    obtain ⟨gs, out, ok, nn, len, ho, ev, safe⟩ := h m hm
    exact ⟨gs, out, ok, nn, le_trans len hs, ho, ev, safe⟩

  have bld_congr {n : ℕ} {F H : (Fin n → Bool) → Bool} {s : ℕ} (h : Bld n F s)
      (e : ∀ x, F x = H x) : Bld n H s := by
    intro m hm
    obtain ⟨gs, out, ok, nn, len, ho, ev, safe⟩ := h m hm
    exact ⟨gs, out, ok, nn, len, ho, (fun w hw => by rw [ev w hw, e]), safe⟩

  have bld_var {n : ℕ} (i : Fin n) : Bld n (fun x => x i) 0 := by
    intro m hm
    refine ⟨[], i, by simp, by simp, le_rfl, by simp; omega, ?_, ?_⟩
    · intro w _
      simp [wiresFrom]
    · intro w hw hl j g entry
      simp at entry

  have bld_bin {n : ℕ} (op : PEqualNP.CircuitLowerBounds.GateOp) (hop : op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ op = PEqualNP.CircuitLowerBounds.GateOp.or)
      (c : Bool → Bool → Bool) (hc : ∀ a b, op.eval [a, b] = c a b)
      {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1) (h2 : Bld n H s2)
      (newSafe : op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ x : Fin n → Bool, PEqualNP.InvisibleWire.IsLight n x → c (F x) (H x) = false) :
      Bld n (fun x => c (F x) (H x)) (s1 + s2 + 1) := by
    intro m hm
    obtain ⟨gs1, o1, ok1, nn1, len1, ho1, ev1, safe1⟩ := h1 m hm
    obtain ⟨gs2, o2, ok2, nn2, len2, ho2, ev2, safe2⟩ := h2 (m + gs1.length) (by omega)
    have finalEval : ∀ w : List Bool, w.length = m →
        (wiresFrom (gs1 ++ gs2 ++ [⟨op, [o1,o2]⟩]) w).getD
          (m + gs1.length + gs2.length) false = c (F (fun i => w.getD i false)) (H (fun i => w.getD i false)) := by
      intro w hw
      rw [wiresFrom_append, wiresFrom_append]
      set v := wiresFrom gs1 w with hv
      have lv : v.length = m + gs1.length := by rw [hv, length_wiresFrom, hw]
      set u := wiresFrom gs2 v with hu
      have lu : u.length = m + gs1.length + gs2.length := by rw [hu, length_wiresFrom, lv]
      have step : wiresFrom [⟨op, [o1, o2]⟩] u
          = u ++ [op.eval ([o1, o2].map fun i => u.getD i false)] := rfl
      rw [step, ← lu, getD_snoc_eq]
      simp only [List.map_cons, List.map_nil, hc]
      have e1 : u.getD o1 false = F (fun i => w.getD i false) := by
        rw [hu, getD_wiresFrom _ _ _ (by omega), hv, ev1 w hw]
      have e2 : u.getD o2 false = H (fun i => w.getD i false) := by
        rw [hu, ev2 v lv]
        congr 1
        funext i
        rw [hv, getD_wiresFrom _ _ _ (by have := i.2; omega)]
      rw [e1, e2]
    refine ⟨gs1 ++ gs2 ++ [⟨op, [o1, o2]⟩], m + gs1.length + gs2.length, ?_, ?_, ?_, ?_, finalEval, ?_⟩
    · intro g hg
      simp only [List.mem_append, List.mem_singleton] at hg
      rcases hg with (hg | hg) | hg
      · exact ok1 g hg
      · exact ok2 g hg
      · subst hg; rcases hop with h | h <;> simp [Ok, h]
    · intro g hg
      simp only [List.mem_append, List.mem_singleton] at hg
      rcases hg with (hg | hg) | hg
      · exact nn1 g hg
      · exact nn2 g hg
      · subst hg; rcases hop with h | h <;> simp [h]
    · simp; omega
    · simp; omega
    · intro w hw light j g entry hand
      have priorSafe := safe_append hm safe1 safe2
      by_cases old : j < (gs1 ++ gs2).length
      · have eg : (gs1 ++ gs2)[j]? = some g := by
          rwa [List.getElem?_append_left old] at entry
        rw [wiresFrom_append, getD_wiresFrom _ _ _ (by rw [length_wiresFrom, hw]; omega)]
        exact priorSafe w hw light j g eg hand
      · have e : [⟨op, [o1,o2]⟩][j - (gs1 ++ gs2).length]? = some g := by
          rwa [List.getElem?_append_right (by omega)] at entry
        have bounds := List.getElem?_eq_some_iff.mp e
        have eqj : j = (gs1 ++ gs2).length := by
          have := bounds.1
          simp only [List.length_singleton] at this
          omega
        subst j
        simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at e
        subst g
        rw [List.length_append, ← Nat.add_assoc, finalEval w hw]
        exact newSafe hand _ light

  have bld_or {n : ℕ} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1)
      (h2 : Bld n H s2) : Bld n (fun x => F x || H x) (s1 + s2 + 1) :=
    bld_bin PEqualNP.CircuitLowerBounds.GateOp.or (Or.inr rfl) (· || ·) (by intro a b; simp [PEqualNP.CircuitLowerBounds.GateOp.eval]) h1 h2
      (by intro h; cases h)

  have bld_and {n : ℕ} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1)
      (h2 : Bld n H s2) (sep : ∀ x : Fin n → Bool, PEqualNP.InvisibleWire.IsLight n x → (F x && H x) = false) :
      Bld n (fun x => F x && H x) (s1 + s2 + 1) :=
    bld_bin PEqualNP.CircuitLowerBounds.GateOp.and (Or.inl rfl) (· && ·) (by intro a b; simp [PEqualNP.CircuitLowerBounds.GateOp.eval]) h1 h2 (fun _ => sep)

  have bld_circuit {n : ℕ} {F : (Fin n → Bool) → Bool} {s : ℕ} (h : Bld n F s) :
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ (∀ g ∈ D.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) ∧
        PEqualNP.MetaComplexity.circuitFun n D = F ∧ D.size ≤ s ∧
        ∀ j g, D.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.InvisibleWire.IsInvisible D n (n+j) := by
    obtain ⟨gs, out, ok, nn, len, _, ev, safe⟩ := h n le_rfl
    refine ⟨⟨gs, out⟩, ok, nn, ?_, len, ?_⟩
    · funext x
      have e := ev (List.ofFn x) (by simp)
      simp only [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval, wires_eq, e]
      congr 1
      funext i
      exact getD_ofFn x i
    · intro j g entry hand x hx
      exact safe (List.ofFn x) (by simp) (by simpa using hx) j g entry hand

  have bld_anyList {n : ℕ} (vs : List (Fin n)) : ∀ v : Fin n,
      Bld n (fun x => (v :: vs).any fun j => x j) vs.length := by
    induction vs with
    | nil =>
      intro v
      exact bld_congr (n := n) (F := fun x => x v)
        (H := fun x => [v].any fun j => x j) (s := 0) (bld_var v) (by intro x; simp)
    | cons w ws ih =>
      intro v
      have hb := bld_or (n := n) (F := fun x => x v)
        (H := fun x => (w :: ws).any fun j => x j) (s1 := 0) (s2 := ws.length) (bld_var v) (ih w)
      refine bld_congr (n := n) (F := fun x => x v || (w :: ws).any fun j => x j)
        (H := fun x => (v :: w :: ws).any fun j => x j) (s := (w :: ws).length)
        (bld_mono (n := n) (F := fun x => x v || (w :: ws).any fun j => x j)
          (s := 0 + ws.length + 1) (s' := (w :: ws).length) hb (by simp)) ?_
      intro x
      simp

  have bld_anyFinset {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) :
      Bld n (fun x => decide (∃ v ∈ S, x v = true)) (S.card - 1) := by
    obtain ⟨v, vs, hl⟩ : ∃ v vs, S.toList = v :: vs := by
      cases h : S.toList with
      | nil => simp at h; exact absurd h hS.ne_empty
      | cons v vs => exact ⟨v, vs, rfl⟩
    have hc : S.card = vs.length + 1 := by rw [← Finset.length_toList, hl]; rfl
    refine bld_congr (n := n) (F := fun x => (v :: vs).any fun j => x j)
      (H := fun x => decide (∃ v ∈ S, x v = true)) (s := S.card - 1)
      (bld_mono (n := n) (F := fun x => (v :: vs).any fun j => x j)
        (s := vs.length) (s' := S.card - 1) (bld_anyList vs v) (by omega)) ?_
    intro x
    rw [Bool.eq_iff_iff, decide_eq_true_iff, ← hl, List.any_eq_true]
    simp

  have bld_edges (n : ℕ) (T : Finset (Fin n)) : ∀ E : Finset (Sym2 (Fin n)), E.Nonempty →
      (∀ e ∈ E, ∃ t ∈ T, t ∈ e) → (∀ a, s(a,a) ∉ E) →
      Bld n (fun x => decide (∃ e ∈ E, ∀ v ∈ e, x v = true)) (E.card + T.card - 1) := by
    induction T using Finset.induction_on with
    | empty =>
      intro E hE hc hloop
      obtain ⟨e, he⟩ := hE
      obtain ⟨t, ht, _⟩ := hc e he
      simp at ht
    | @insert t T0 htT ih =>
      intro E hE hc hloop
      set E1 := E.filter (fun e => t ∈ e) with hE1
      set E2 := E.filter (fun e => t ∉ e) with hE2
      have hsplit : E1.card + E2.card = E.card := Finset.card_filter_add_card_filter_not _
      have hcard : (insert t T0).card = T0.card + 1 := Finset.card_insert_of_notMem htT
      have c2 : ∀ e ∈ E2, ∃ t' ∈ T0, t' ∈ e := by
        intro e he
        rw [hE2, Finset.mem_filter] at he
        obtain ⟨t', ht', hte⟩ := hc e he.1
        rcases Finset.mem_insert.1 ht' with h | h
        · subst h; exact absurd hte he.2
        · exact ⟨t', h, hte⟩
      have loop2 : ∀ a, s(a,a) ∉ E2 := by
        intro a ha
        exact hloop a (Finset.mem_filter.mp ha).1

      set S := Finset.univ.filter (fun v : Fin n => s(t, v) ∈ E1) with hS
      have hSc : S.card ≤ E1.card := by
        refine Finset.card_le_card_of_injOn (fun v => s(t, v)) ?_ ?_
        · intro v hv
          simp only [hS, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv
          exact hv
        · intro a _ b _ hab
          exact Sym2.congr_right.1 hab
      have star : E1.Nonempty → Bld n (fun x => decide (∃ e ∈ E1, ∀ v ∈ e, x v = true))
          E1.card := by
        intro h1
        have hSne : S.Nonempty := by
          obtain ⟨e, he⟩ := h1
          have he' := he
          rw [hE1, Finset.mem_filter] at he'
          obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 he'.2
          exact ⟨b, by simp [hS, ← hb, he]⟩
        have separated : ∀ x : Fin n → Bool, PEqualNP.InvisibleWire.IsLight n x →
            (x t && decide (∃ v ∈ S, x v = true)) = false := by
          intro x hx
          apply Bool.eq_false_iff.mpr
          intro htrue
          have hh : x t = true ∧ decide (∃ v ∈ S, x v = true) = true := by
            simpa only [Bool.and_eq_true] using htrue
          obtain ⟨ht, hv⟩ := hh
          obtain ⟨v, hv, hxv⟩ := of_decide_eq_true hv
          have tv : t = v := Finset.card_le_one.mp hx t (by simp [ht]) v (by simp [hxv])
          subst v
          exact hloop t (Finset.mem_filter.mp (Finset.mem_filter.mp hv).2).1
        have hb := bld_and (n := n) (F := fun x => x t)
          (H := fun x => decide (∃ v ∈ S, x v = true)) (s1 := 0) (s2 := S.card - 1)
          (bld_var t) (bld_anyFinset S hSne) separated
        have hpos := hSne.card_pos
        refine bld_congr (n := n) (F := fun x => x t && decide (∃ v ∈ S, x v = true))
          (H := fun x => decide (∃ e ∈ E1, ∀ v ∈ e, x v = true)) (s := E1.card)
          (bld_mono (n := n) (F := fun x => x t && decide (∃ v ∈ S, x v = true))
            (s := 0 + (S.card - 1) + 1) (s' := E1.card) hb (by omega)) ?_
        intro x
        rw [Bool.eq_iff_iff, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
        constructor
        · rintro ⟨ht, v, hv, hxv⟩
          refine ⟨s(t, v), (Finset.mem_filter.1 hv).2, ?_⟩
          intro u hu
          rcases Sym2.mem_iff.1 hu with rfl | rfl <;> assumption
        · rintro ⟨e, he, hall⟩
          have he' := he
          rw [hE1, Finset.mem_filter] at he'
          obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 he'.2
          subst hb
          exact ⟨hall t (Sym2.mem_mk_left _ _), b, by simp [hS, he],
            hall b (Sym2.mem_mk_right _ _)⟩
      have key : ∀ x : Fin n → Bool, decide (∃ e ∈ E, ∀ v ∈ e, x v = true)
          = (decide (∃ e ∈ E1, ∀ v ∈ e, x v = true) || decide (∃ e ∈ E2, ∀ v ∈ e, x v = true)) := by
        intro x
        rw [Bool.eq_iff_iff]
        simp only [Bool.or_eq_true, decide_eq_true_iff, hE1, hE2, Finset.mem_filter]
        constructor
        · rintro ⟨e, he, h⟩
          by_cases hte : t ∈ e
          · exact Or.inl ⟨e, ⟨he, hte⟩, h⟩
          · exact Or.inr ⟨e, ⟨he, hte⟩, h⟩
        · rintro (⟨e, ⟨he, _⟩, h⟩ | ⟨e, ⟨he, _⟩, h⟩) <;> exact ⟨e, he, h⟩
      rw [hcard]
      by_cases h1 : E1.Nonempty
      · by_cases h2 : E2.Nonempty
        · have hb := bld_or (n := n)
            (F := fun x => decide (∃ e ∈ E1, ∀ v ∈ e, x v = true))
            (H := fun x => decide (∃ e ∈ E2, ∀ v ∈ e, x v = true))
            (s1 := E1.card) (s2 := E2.card + T0.card - 1) (star h1) (ih E2 h2 c2 loop2)
          have hp := h2.card_pos
          refine bld_congr (n := n)
            (F := fun x => decide (∃ e ∈ E1, ∀ v ∈ e, x v = true) || decide (∃ e ∈ E2, ∀ v ∈ e, x v = true))
            (H := fun x => decide (∃ e ∈ E, ∀ v ∈ e, x v = true)) (s := E.card + (T0.card + 1) - 1)
            (bld_mono (n := n)
              (F := fun x => decide (∃ e ∈ E1, ∀ v ∈ e, x v = true) || decide (∃ e ∈ E2, ∀ v ∈ e, x v = true))
              (s := E1.card + (E2.card + T0.card - 1) + 1) (s' := E.card + (T0.card + 1) - 1)
              hb (by omega)) ?_
          intro x
          rw [key]
        · rw [Finset.not_nonempty_iff_eq_empty] at h2
          refine bld_congr (n := n) (F := fun x => decide (∃ e ∈ E1, ∀ v ∈ e, x v = true))
            (H := fun x => decide (∃ e ∈ E, ∀ v ∈ e, x v = true)) (s := E.card + (T0.card + 1) - 1)
            (bld_mono (n := n) (F := fun x => decide (∃ e ∈ E1, ∀ v ∈ e, x v = true))
              (s := E1.card) (s' := E.card + (T0.card + 1) - 1) (star h1) (by omega)) ?_
          intro x
          rw [key, h2]
          simp
      · rw [Finset.not_nonempty_iff_eq_empty] at h1
        have h2 : E2.Nonempty := by
          by_contra h2
          rw [Finset.not_nonempty_iff_eq_empty] at h2
          have := hE.card_pos
          rw [h1, h2] at hsplit
          simp at hsplit
          omega
        refine bld_congr (n := n) (F := fun x => decide (∃ e ∈ E2, ∀ v ∈ e, x v = true))
          (H := fun x => decide (∃ e ∈ E, ∀ v ∈ e, x v = true)) (s := E.card + (T0.card + 1) - 1)
          (bld_mono (n := n) (F := fun x => decide (∃ e ∈ E2, ∀ v ∈ e, x v = true))
            (s := E2.card + T0.card - 1) (s' := E.card + (T0.card + 1) - 1)
            (ih E2 h2 c2 loop2) (by omega)) ?_
        intro x
        rw [key, h1]
        simp

  have edge_upper_mono : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n)), (∃ i j : Fin n, G.Adj i j) → (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ (∀ g ∈ D.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) ∧ PEqualNP.MetaComplexity.circuitFun n D = (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) ∧ D.size + 1 ≤ G.edgeFinset.card + T.card ∧
      ∀ j g, D.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.InvisibleWire.IsInvisible D n (n+j) := by
    intro n G _ T hE hc
    obtain ⟨i0, j0, h0⟩ := hE
    have hne : G.edgeFinset.Nonempty := ⟨s(i0, j0), by simpa using h0⟩
    have cov : ∀ e ∈ G.edgeFinset, ∃ t ∈ T, t ∈ e := by
      intro e
      refine Sym2.ind (fun a b => ?_) e
      intro he
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      rcases hc a b he with h | h
      · exact ⟨a, h, Sym2.mem_mk_left _ _⟩
      · exact ⟨b, h, Sym2.mem_mk_right _ _⟩
    have hpos := hne.card_pos
    have loop : ∀ a : Fin n, s(a,a) ∉ G.edgeFinset := by simp
    obtain ⟨D, h1, h2, h3, h4, safe⟩ := bld_circuit (n := n)
      (F := fun x => decide (∃ e ∈ G.edgeFinset, ∀ v ∈ e, x v = true))
      (s := G.edgeFinset.card + T.card - 1) (bld_edges n T G.edgeFinset hne cov loop)
    refine ⟨D, h1, h2, ?_, by omega, safe⟩
    rw [h3]
    funext x
    rw [decide_eq_decide]
    constructor
    · rintro ⟨e, he, h⟩
      revert he h
      refine Sym2.ind (fun a b => ?_) e
      intro he h
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      exact ⟨a, b, he, h a (Sym2.mem_mk_left _ _), h b (Sym2.mem_mk_right _ _)⟩
    · rintro ⟨i, j, hij, hi, hj⟩
      refine ⟨s(i, j), by simpa using hij, ?_⟩
      intro v hv
      rcases Sym2.mem_iff.1 hv with rfl | rfl <;> assumption

  have clean_cover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (T : Finset (Fin n)) (hE : ∃ i j, G.Adj i j)
      (hc : ∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T) :
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
        (∀ x : Fin n → Bool, D.eval (List.ofFn x) =
          decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)) ∧
        D.size + 1 ≤ G.edgeFinset.card + T.card ∧
        ∀ j g, D.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
          ∀ S : Finset (Fin n), S.card ≤ 1 →
            (D.wires (List.ofFn (fun i => decide (i ∈ S)))).getD (n+j) false = false := by
    obtain ⟨D, df, dn, de, size, safe⟩ := edge_upper_mono n G T hE hc
    refine ⟨D, ?_, ?_, size, ?_⟩
    · intro g hg
      obtain ⟨op, arity⟩ := df g hg
      refine ⟨?_, arity⟩
      have shape : g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not := by
        simpa using op
      rcases shape with h | h | h
      · simp [h]
      · simp [h]
      · exact False.elim (dn g hg h)
    · intro x
      exact congrFun de x
    · intro j g entry hand S hS
      exact safe j g entry hand _ (by simpa [PEqualNP.InvisibleWire.IsLight] using hS)

  intro n G inst
  dsimp only
  intro htri hsquare
  by_cases hE : ∃ i j : Fin n, G.Adj i j
  · let Covers : ℕ → Prop := fun k => ∃ T : Finset (Fin n),
      PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G T ∧ T.card = k
    have hc : ∃ k, Covers k :=
      ⟨(Finset.univ : Finset (Fin n)).card, Finset.univ,
        (fun a _ _ => Or.inl (Finset.mem_univ a)), rfl⟩
    obtain ⟨T, hT, ht⟩ := Nat.find_spec hc
    have minCover : ∀ U : Finset (Fin n),
        PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G U → T.card ≤ U.card := by
      intro U hU
      rw [ht]
      exact Nat.find_min' hc ⟨U, hU, rfl⟩
    obtain ⟨C, hC, he, hsize, safe⟩ := clean_cover G T hE hT
    let Fits : ℕ → Prop := fun k => ∃ K : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 K ∧
      PEqualNP.MetaComplexity.circuitFun n K = PEqualNP.MetaComplexity.circuitFun n C ∧ K.size = k
    have hex : ∃ k, Fits k := ⟨C.size, C, hC, rfl, rfl⟩
    obtain ⟨K, hK, heq, hk⟩ := Nat.find_spec hex
    have minK : ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 D →
        PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.circuitFun n C →
        K.size ≤ D.size := by
      intro D hD hd
      rw [hk]
      exact Nat.find_min' hex ⟨D, hD, hd, rfl⟩
    have minimalK : PEqualNP.MetaComplexity.IsMinimalMonoCircuit n K := by
      refine ⟨hK, ?_⟩
      intro D hD hd
      exact minK D hD (hd.trans heq)
    have heK : PEqualNP.MetaComplexity.circuitFun n K =
        PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
      rw [heq]
      funext x
      change C.eval (List.ofFn x) =
        (decide (∃ a ∈ (∅ : Finset (Fin n)), x a = true) ||
         decide (∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true))
      simpa using he x
    obtain ⟨U, hU, hand⟩ := andBound n G htri hsquare K minimalK heK
    have htU := minCover U hU
    have hor := orBound n G htri hsquare K minimalK heK
    have partition : ∀ gs : List PEqualNP.CircuitLowerBounds.Gate,
        (∀ g ∈ gs, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          g.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
        gs.countP (fun g => match g.op with
            | PEqualNP.CircuitLowerBounds.GateOp.and => true | _ => false) +
          gs.countP (fun g => match g.op with
            | PEqualNP.CircuitLowerBounds.GateOp.or => true | _ => false) = gs.length := by
      intro gs
      induction gs with
      | nil => intro _; simp
      | cons g gs ih =>
        intro hall
        have tail := ih (fun g hg => hall g (by simp [hg]))
        rcases hall g (by simp) with h | h <;>
          simp [List.countP_cons, h] <;> omega
    have hp := partition K.gates (fun g hg => by simpa using (hK g hg).1)
    have hCK : C.size ≤ K.size := by
      change C.gates.length + 1 ≤ G.edgeFinset.card + T.card at hsize
      change C.gates.length ≤ K.gates.length
      omega
    refine ⟨C, hC, he, ?_, safe⟩
    intro D hD hd
    apply hCK.trans (minK D hD ?_)
    funext x
    exact (hd x).trans (he x).symm
  · have hG : ∀ a b : Fin n, ¬ G.Adj a b := by
      intro a b hab
      exact hE ⟨a, b, hab⟩
    refine ⟨⟨[], n⟩, ?_, ?_, ?_, ?_⟩
    · simp [PEqualNP.MetaComplexity.Monotone2]
    · intro x
      simp [PEqualNP.CircuitLowerBounds.Circuit.eval,
        PEqualNP.CircuitLowerBounds.Circuit.wires, List.getD, hG]
    · intro D _ _
      simp [PEqualNP.CircuitLowerBounds.Circuit.size]
    · intro j g h
      simp at h
