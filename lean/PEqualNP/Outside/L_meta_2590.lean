import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2590_aux

section packScope1

open PEqualNP.CircuitLowerBounds

open PEqualNP.MetaComplexity

def H2.petersenEdges : List (Fin 10 × Fin 10) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]

open PEqualNP.Outside.L_meta_2590_aux.H2

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def H2.gop : Bool → Bool → Bool → Bool
  | true, a, b => a && b
  | false, a, b => a || b

@[local simp] lemma H2.gop_true (a b : Bool) : gop true a b = (a && b) := rfl

@[local simp] lemma H2.gop_false (a b : Bool) : gop false a b = (a || b) := rfl

abbrev H2.Dag := List (Bool × ℕ × ℕ)

def H2.tag (D : Dag) (j : ℕ) : Bool := (D.getD j (false, 0, 0)).1

def H2.opA (D : Dag) (j : ℕ) : ℕ := (D.getD j (false, 0, 0)).2.1

def H2.opB (D : Dag) (j : ℕ) : ℕ := (D.getD j (false, 0, 0)).2.2

def H2.wstep (w : List Bool) (g : Bool × ℕ × ℕ) : List Bool :=
  w ++ [gop g.1 (w.getD g.2.1 false) (w.getD g.2.2 false)]

def H2.wl (D : Dag) (w : List Bool) : List Bool := D.foldl wstep w

def H2.val (D : Dag) {n : ℕ} (x : Fin n → Bool) (w : ℕ) : Bool :=
  (wl D (List.ofFn x)).getD w false

def H2.Strict (n : ℕ) (D : Dag) : Prop :=
  ∀ j, j < D.length → opA D j < n + j ∧ opB D j < n + j ∧ opA D j ≠ opB D j

def H2.readers (D : Dag) (w : ℕ) : Finset ℕ :=
  (Finset.range D.length).filter (fun j => opA D j = w ∨ opB D j = w)

def H2.fanout (D : Dag) (w : ℕ) : ℕ := (readers D w).card

def H2.Live (n : ℕ) (D : Dag) : Prop := ∀ w, w + 1 < n + D.length → 1 ≤ fanout D w

def H2.StrictLive (n : ℕ) (D : Dag) : Prop := Strict n D ∧ Live n D ∧ D ≠ []

def H2.outW (n : ℕ) (D : Dag) : ℕ := n + D.length - 1

def H2.single {n : ℕ} (v : Fin n) : Fin n → Bool := fun i => decide (i = v)

def H2.supp (n : ℕ) (D : Dag) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => val D (single v) w = true)

def H2.surplusOn (D : Dag) (K : Finset ℕ) : ℕ := ∑ w ∈ K, (fanout D w - 1)

def H2.inner (n : ℕ) (D : Dag) : Finset ℕ := Finset.range (n + D.length - 1)

def H2.totalSurplus (n : ℕ) (D : Dag) : ℕ := surplusOn D (inner n D)

def H2.Bplus (n : ℕ) (D : Dag) : ℕ :=
  surplusOn D ((inner n D).filter (fun w => (supp n D w).Nonempty))

def H2.Bzero (n : ℕ) (D : Dag) : ℕ :=
  surplusOn D ((inner n D).filter (fun w => ¬ (supp n D w).Nonempty))

def H2.branchW (n : ℕ) (D : Dag) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => 2 ≤ fanout D w)

def H2.eligSet (n : ℕ) (D : Dag) : Finset (Fin n) := (branchW n D).biUnion (supp n D)

def H2.ineligSet (n : ℕ) (D : Dag) : Finset (Fin n) := Finset.univ \ eligSet n D

def H2.units (n : ℕ) (D : Dag) : Finset (Σ _ : ℕ, ℕ) :=
  (inner n D).sigma (fun w => Finset.range (fanout D w - 1))

def H2.unitsPlus (n : ℕ) (D : Dag) : Finset (Σ _ : ℕ, ℕ) :=
  (units n D).filter (fun u => (supp n D u.1).Nonempty)

def H2.arcs (D : Dag) : Finset (ℕ × Bool) := Finset.range D.length ×ˢ Finset.univ

def H2.src (D : Dag) (e : ℕ × Bool) : ℕ := if e.2 = true then opB D e.1 else opA D e.1

def H2.exitArcs (n : ℕ) (D : Dag) (K : Finset ℕ) : Finset (ℕ × Bool) :=
  (arcs D).filter (fun e => src D e ∈ K ∧ n + e.1 ∉ K)

def H2.merges (n : ℕ) (D : Dag) (K : Finset ℕ) : Finset ℕ :=
  (Finset.range D.length).filter (fun j => n + j ∈ K ∧ opA D j ∈ K ∧ opB D j ∈ K)

def H2.sources (n : ℕ) (K : Finset ℕ) : Finset ℕ := K.filter (fun w => w < n)

def H2.carrierT (n : ℕ) (D : Dag) (T : Finset (Fin n)) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => (supp n D w ∩ T).Nonempty)

def H2.PureBranch (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Prop :=
  ∀ v ∈ eligSet n D, 2 ≤ fanout D (b v) ∧ supp n D (b v) = {v}

def H2.reservedUnits (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (eligSet n D).image (fun v => (⟨b v, 0⟩ : Σ _ : ℕ, ℕ))

def H2.residualUnits (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  unitsPlus n D \ reservedUnits n D b

lemma H2.tag_eq (D : Dag) (j : ℕ) (h : j < D.length) : tag D j = (D[j]).1 := by
  simp [tag, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

lemma H2.opA_eq (D : Dag) (j : ℕ) (h : j < D.length) : opA D j = (D[j]).2.1 := by
  simp [opA, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

lemma H2.opB_eq (D : Dag) (j : ℕ) (h : j < D.length) : opB D j = (D[j]).2.2 := by
  simp [opB, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

lemma H2.wl_cons (g : Bool × ℕ × ℕ) (D : Dag) (w : List Bool) :
    wl (g :: D) w = wl D (wstep w g) := rfl

lemma H2.wl_append (D E : Dag) (w : List Bool) : wl (D ++ E) w = wl E (wl D w) := by
  simp [wl, List.foldl_append]

lemma H2.wstep_length (w : List Bool) (g : Bool × ℕ × ℕ) : (wstep w g).length = w.length + 1 := by
  simp [wstep]

lemma H2.wl_length (D : Dag) : ∀ w : List Bool, (wl D w).length = w.length + D.length := by
  induction D with
  | nil => intro w; simp [wl]
  | cons g D ih => intro w; rw [wl_cons, ih, wstep_length]; simp; omega

lemma H2.wstep_getD_lt (w : List Bool) (g : Bool × ℕ × ℕ) (i : ℕ) (h : i < w.length) :
    (wstep w g).getD i false = w.getD i false := by
  simp [wstep, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma H2.wl_getD_lt (D : Dag) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wl D w).getD i false = w.getD i false := by
  induction D with
  | nil => intro w i _; rfl
  | cons g D ih =>
    intro w i h
    rw [wl_cons, ih _ _ (by rw [wstep_length]; omega), wstep_getD_lt _ _ _ h]

lemma H2.getD_ge (w : List Bool) (i : ℕ) (h : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

lemma H2.wstep_getD_last (w : List Bool) (g : Bool × ℕ × ℕ) :
    (wstep w g).getD w.length false = gop g.1 (w.getD g.2.1 false) (w.getD g.2.2 false) := by
  simp [wstep, List.getD_eq_getElem?_getD]

lemma H2.wl_getD_gate (D : Dag) (w : List Bool) (j : ℕ) (hj : j < D.length) :
    (wl D w).getD (w.length + j) false =
      gop (tag D j) ((wl (D.take j) w).getD (opA D j) false)
        ((wl (D.take j) w).getD (opB D j) false) := by
  have hsplit : D = D.take j ++ D[j] :: D.drop (j + 1) := by simp
  have hlen : (wl (D.take j) w).length = w.length + j := by
    rw [wl_length, List.length_take]; omega
  rw [tag_eq D j hj, opA_eq D j hj, opB_eq D j hj]
  conv_lhs => rw [hsplit, wl_append, wl_cons]
  rw [wl_getD_lt _ _ _ (by rw [wstep_length, hlen]; omega), ← hlen, wstep_getD_last]

lemma H2.wl_take_getD (D : Dag) (w : List Bool) (j i : ℕ) (hi : i < w.length + j)
    (hj : j ≤ D.length) :
    (wl (D.take j) w).getD i false = (wl D w).getD i false := by
  have hsplit : D = D.take j ++ D.drop j := by simp
  have hlen : (wl (D.take j) w).length = w.length + j := by
    rw [wl_length, List.length_take]; omega
  conv_rhs => rw [hsplit, wl_append]
  rw [wl_getD_lt (D.drop j) (wl (D.take j) w) i (by rw [hlen]; exact hi)]

lemma H2.val_input (D : Dag) {n : ℕ} (x : Fin n → Bool) (i : ℕ) (h : i < n) :
    val D x i = x ⟨i, h⟩ := by
  unfold val
  rw [wl_getD_lt _ _ _ (by simpa using h)]
  simp [List.getD_eq_getElem?_getD, h]

lemma H2.val_ge (D : Dag) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (h : n + D.length ≤ w) :
    val D x w = false := by
  unfold val
  exact getD_ge _ _ (by rw [wl_length]; simpa using h)

lemma H2.val_take (D : Dag) {n : ℕ} (x : Fin n → Bool) (k w : ℕ) (hw : w < n + k)
    (hk : k ≤ D.length) : val (D.take k) x w = val D x w := by
  unfold val
  exact wl_take_getD D _ k w (by simpa using hw) hk

lemma H2.val_gate {n : ℕ} {D : Dag} (hS : Strict n D) (x : Fin n → Bool) (j : ℕ)
    (hj : j < D.length) :
    val D x (n + j) = gop (tag D j) (val D x (opA D j)) (val D x (opB D j)) := by
  obtain ⟨ha, hb, -⟩ := hS j hj
  have h := wl_getD_gate D (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  unfold val
  rw [h, wl_take_getD D _ j _ (by simpa using ha) hj.le,
    wl_take_getD D _ j _ (by simpa using hb) hj.le]

lemma H2.val_unique {n : ℕ} {D : Dag} (hS : Strict n D) (x : Fin n → Bool) (f : ℕ → Bool)
    (hin : ∀ i (h : i < n), f i = x ⟨i, h⟩)
    (hg : ∀ j, j < D.length → f (n + j) = gop (tag D j) (f (opA D j)) (f (opB D j))) :
    ∀ w, w < n + D.length → val D x w = f w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hn : w < n
    · rw [val_input D x w hn, hin w hn]
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < D.length := by omega
      obtain ⟨ha, hb, -⟩ := hS j hj
      rw [val_gate hS x j hj, hg j hj, ih _ ha (by omega), ih _ hb (by omega)]

abbrev H2.Ref := Bool ⊕ ℕ

def H2.refVal (W : List Bool) : Ref → Bool
  | Sum.inl b => b
  | Sum.inr k => W.getD k false

def H2.na_look (m : List Ref) (i : ℕ) : Ref := m.getD i (Sum.inl false)

def H2.na_comb (t : Bool) : Ref → Ref → Ref ⊕ (ℕ × ℕ)
  | Sum.inl a, r => Sum.inl (if a = t then r else Sum.inl a)
  | Sum.inr i, Sum.inl b => Sum.inl (if b = t then Sum.inr i else Sum.inl b)
  | Sum.inr i, Sum.inr j => if i = j then Sum.inl (Sum.inr i) else Sum.inr (i, j)

def H2.na_isAnd : GateOp → Bool
  | GateOp.and => true
  | _ => false

def H2.na_step (n : ℕ) (st : List Ref × Dag) (g : Gate) : List Ref × Dag :=
  match g.inputs with
  | [] => (st.1 ++ [Sum.inl (na_isAnd g.op)], st.2)
  | [a] => (st.1 ++ [na_look st.1 a], st.2)
  | a :: b :: _ =>
    match na_comb (na_isAnd g.op) (na_look st.1 a) (na_look st.1 b) with
    | Sum.inl r => (st.1 ++ [r], st.2)
    | Sum.inr p => (st.1 ++ [Sum.inr (n + st.2.length)], st.2 ++ [(na_isAnd g.op, p.1, p.2)])

def H2.na_ok (B : ℕ) : Ref → Prop
  | Sum.inl _ => True
  | Sum.inr k => k < B

def H2.na_Good (n : ℕ) (st : List Ref × Dag) : Prop :=
  Strict n st.2 ∧ ∀ r ∈ st.1, na_ok (n + st.2.length) r

lemma H2.na_ok_mono {B B' : ℕ} (h : B ≤ B') (r : Ref) (hr : na_ok B r) : na_ok B' r := by
  rcases r with b | k
  · trivial
  · exact lt_of_lt_of_le hr h

lemma H2.na_look_val (W : List Bool) (m : List Ref) (i : ℕ) :
    refVal W (na_look m i) = (m.map (refVal W)).getD i false := by
  simp only [na_look, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases m[i]? <;> rfl

lemma H2.na_look_ok (B : ℕ) (m : List Ref) (hm : ∀ r ∈ m, na_ok B r) (i : ℕ) :
    na_ok B (na_look m i) := by
  simp only [na_look, List.getD_eq_getElem?_getD]
  rcases h : m[i]? with _ | r
  · trivial
  · exact hm r (List.mem_of_getElem? h)

lemma H2.na_refVal_wstep (W : List Bool) (g : Bool × ℕ × ℕ) (r : Ref) (hr : na_ok W.length r) :
    refVal (wstep W g) r = refVal W r := by
  rcases r with b | k
  · rfl
  · exact wstep_getD_lt W g k hr

lemma H2.na_comb_inl (t : Bool) (W : List Bool) (a b r : Ref) (h : na_comb t a b = Sum.inl r) :
    refVal W r = gop t (refVal W a) (refVal W b) := by
  rcases a with a | i
  · simp only [na_comb, Sum.inl.injEq] at h
    subst h
    cases t <;> cases a <;> simp [refVal]
  · rcases b with b | j
    · simp only [na_comb, Sum.inl.injEq] at h
      subst h
      cases t <;> cases b <;> simp [refVal]
    · simp only [na_comb] at h
      split_ifs at h with hij
      simp only [Sum.inl.injEq] at h
      subst h; subst hij
      cases t <;> simp [refVal]

lemma H2.na_comb_ok (B : ℕ) (t : Bool) (a b r : Ref) (ha : na_ok B a) (hb : na_ok B b)
    (h : na_comb t a b = Sum.inl r) : na_ok B r := by
  rcases a with a | i
  · simp only [na_comb, Sum.inl.injEq] at h
    subst h; split_ifs
    · exact hb
    · trivial
  · rcases b with b | j
    · simp only [na_comb, Sum.inl.injEq] at h
      subst h; split_ifs
      · exact ha
      · trivial
    · simp only [na_comb] at h
      split_ifs at h
      simp only [Sum.inl.injEq] at h
      subst h; exact ha

lemma H2.na_comb_inr (t : Bool) (a b : Ref) (p : ℕ × ℕ) (h : na_comb t a b = Sum.inr p) :
    a = Sum.inr p.1 ∧ b = Sum.inr p.2 ∧ p.1 ≠ p.2 := by
  rcases a with a | i
  · simp [na_comb] at h
  · rcases b with b | j
    · simp [na_comb] at h
    · simp only [na_comb] at h
      split_ifs at h with hij
      cases h
      exact ⟨rfl, rfl, hij⟩

lemma H2.na_eval0 (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
    op.eval [] = na_isAnd op := by
  rcases hop with rfl | rfl <;> rfl

lemma H2.na_eval1 (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (u : Bool) :
    op.eval [u] = u := by
  rcases hop with rfl | rfl <;> simp [GateOp.eval]

lemma H2.na_eval2 (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (u v : Bool) : op.eval [u, v] = gop (na_isAnd op) u v := by
  rcases hop with rfl | rfl <;> simp [GateOp.eval, na_isAnd]

lemma H2.na_getD_append_lt (D E : Dag) (k : ℕ) (h : k < D.length) :
    (D ++ E).getD k (false, 0, 0) = D.getD k (false, 0, 0) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma H2.na_getD_snoc (D : Dag) (g : Bool × ℕ × ℕ) :
    (D ++ [g]).getD D.length (false, 0, 0) = g := by
  simp [List.getD_eq_getElem?_getD]

lemma H2.na_strict_snoc {n : ℕ} {D : Dag} (hS : Strict n D) (t : Bool) (i j : ℕ)
    (hi : i < n + D.length) (hj : j < n + D.length) (hij : i ≠ j) :
    Strict n (D ++ [(t, i, j)]) := by
  intro k hk
  simp only [List.length_append, List.length_singleton] at hk
  by_cases hk' : k < D.length
  · simp only [opA, opB, na_getD_append_lt D _ k hk']
    exact hS k hk'
  · have hkD : k = D.length := by omega
    subst hkD
    simp only [opA, opB, na_getD_snoc]
    exact ⟨hi, hj, hij⟩

lemma H2.na_strict_take {n : ℕ} {D : Dag} (hS : Strict n D) (k : ℕ) : Strict n (D.take k) := by
  intro j hj
  simp only [List.length_take] at hj
  have hj1 : j < k := by omega
  have hj2 : j < D.length := by omega
  have e : (D.take k).getD j (false, 0, 0) = D.getD j (false, 0, 0) := by
    simp [List.getD_eq_getElem?_getD, hj1]
  simp only [opA, opB, e]
  exact hS j hj2

lemma H2.na_step_spec (n : ℕ) (st : List Ref × Dag) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : na_Good n st) :
    na_Good n (na_step n st g) ∧ (na_step n st g).2.length ≤ st.2.length + 1 ∧
    ∀ (x : Fin n → Bool) (w : List Bool), st.1.map (refVal (wl st.2 (List.ofFn x))) = w →
      (na_step n st g).1.map (refVal (wl (na_step n st g).2 (List.ofFn x))) =
        w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := by
  obtain ⟨m, D⟩ := st
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  obtain ⟨hS, hok⟩ := h
  dsimp only at hS hok hop hlen ⊢
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · refine ⟨⟨hS, ?_⟩, by simp [na_step], fun x w hw => ?_⟩
    · intro r hr
      simp only [na_step, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact hok r hr
      · trivial
    · subst hw
      simp only [na_step, List.map_append, List.map_cons, List.map_nil, refVal, na_eval0 op hop]
  · refine ⟨⟨hS, ?_⟩, by simp [na_step], fun x w hw => ?_⟩
    · intro r hr
      simp only [na_step, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact hok r hr
      · exact na_look_ok _ m hok a
    · subst hw
      simp only [na_step, List.map_append, List.map_cons, List.map_nil, na_eval1 op hop,
        na_look_val]
  · have hla := na_look_ok _ m hok a
    have hlb := na_look_ok _ m hok b
    rcases hc : na_comb (na_isAnd op) (na_look m a) (na_look m b) with r | p
    · refine ⟨⟨by simpa only [na_step, hc] using hS, ?_⟩, by simp [na_step, hc],
        fun x w hw => ?_⟩
      · intro r' hr
        simp only [na_step, hc, List.mem_append, List.mem_singleton] at hr ⊢
        rcases hr with hr | rfl
        · exact hok r' hr
        · exact na_comb_ok _ _ _ _ _ hla hlb hc
      · subst hw
        simp only [na_step, hc, List.map_append, List.map_cons, List.map_nil, na_eval2 op hop,
          na_comb_inl _ (wl D (List.ofFn x)) _ _ _ hc, na_look_val]
    · obtain ⟨ea, eb, hne⟩ := na_comb_inr _ _ _ _ hc
      rw [ea] at hla
      rw [eb] at hlb
      have hS' := na_strict_snoc hS (na_isAnd op) p.1 p.2 hla hlb hne
      refine ⟨⟨by simpa only [na_step, hc] using hS', ?_⟩, by simp [na_step, hc],
        fun x w hw => ?_⟩
      · intro r' hr
        simp only [na_step, hc, List.mem_append, List.mem_singleton, List.length_append,
          List.length_singleton] at hr ⊢
        rcases hr with hr | rfl
        · exact na_ok_mono (by omega) r' (hok r' hr)
        · show n + D.length < n + (D.length + 1)
          omega
      · subst hw
        have hWlen : (wl D (List.ofFn x)).length = n + D.length := by
          rw [wl_length, List.length_ofFn]
        have hW' : wl (D ++ [(na_isAnd op, p.1, p.2)]) (List.ofFn x) =
            wstep (wl D (List.ofFn x)) (na_isAnd op, p.1, p.2) := by
          rw [wl_append]; rfl
        have h1 : m.map (refVal (wstep (wl D (List.ofFn x)) (na_isAnd op, p.1, p.2))) =
            m.map (refVal (wl D (List.ofFn x))) :=
          List.map_congr_left (fun r hr => na_refVal_wstep _ _ r (by rw [hWlen]; exact hok r hr))
        have h2 : (wstep (wl D (List.ofFn x)) (na_isAnd op, p.1, p.2)).getD (n + D.length) false =
            gop (na_isAnd op) ((m.map (refVal (wl D (List.ofFn x)))).getD a false)
              ((m.map (refVal (wl D (List.ofFn x)))).getD b false) := by
          rw [← hWlen, wstep_getD_last, ← na_look_val, ← na_look_val, ea, eb]; rfl
        simp only [na_step, hc, hW', List.map_append, List.map_cons, List.map_nil, h1, refVal,
          h2, na_eval2 op hop]
  · simp at hlen

lemma H2.na_no_reader {D : Dag} {w : ℕ} (h : fanout D w = 0) (j : ℕ) (hj : j < D.length) :
    opA D j ≠ w ∧ opB D j ≠ w := by
  unfold fanout readers at h
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
  have := h (Finset.mem_range.mpr hj)
  tauto

def H2.na_sh (c a : ℕ) : ℕ := if c < a then a - 1 else a

def H2.na_up (c w : ℕ) : ℕ := if w < c then w else w + 1

def H2.na_del (n j : ℕ) (D : Dag) : Dag :=
  (D.eraseIdx j).map (fun g => (g.1, na_sh (n + j) g.2.1, na_sh (n + j) g.2.2))

lemma H2.na_del_length (n j : ℕ) (D : Dag) (hj : j < D.length) :
    (na_del n j D).length = D.length - 1 := by
  simp [na_del, List.length_eraseIdx, hj]

lemma H2.na_del_ops (n j : ℕ) (D : Dag) (k : ℕ) (hk : na_up j k < D.length) :
    tag (na_del n j D) k = tag D (na_up j k) ∧
    opA (na_del n j D) k = na_sh (n + j) (opA D (na_up j k)) ∧
    opB (na_del n j D) k = na_sh (n + j) (opB D (na_up j k)) := by
  have e : (na_del n j D).getD k (false, 0, 0) =
      ((D.getD (na_up j k) (false, 0, 0)).1, na_sh (n + j) (D.getD (na_up j k) (false, 0, 0)).2.1,
        na_sh (n + j) (D.getD (na_up j k) (false, 0, 0)).2.2) := by
    simp only [na_del, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eraseIdx]
    unfold na_up at hk ⊢
    split_ifs at hk ⊢ <;> simp [List.getElem?_eq_getElem hk]
  unfold tag opA opB
  rw [e]
  exact ⟨rfl, rfl, rfl⟩

lemma H2.na_del_strict {n : ℕ} {D : Dag} (hS : Strict n D) (j : ℕ) (hj : j < D.length)
    (hf : fanout D (n + j) = 0) : Strict n (na_del n j D) := by
  intro k hk
  rw [na_del_length n j D hj] at hk
  have hk' : na_up j k < D.length := by unfold na_up; split_ifs <;> omega
  have hk2 : (k < j ∧ na_up j k = k) ∨ (j ≤ k ∧ na_up j k = k + 1) := by
    unfold na_up; split_ifs <;> omega
  obtain ⟨ha, hb, hab⟩ := hS _ hk'
  obtain ⟨ra, rb⟩ := na_no_reader hf _ hk'
  obtain ⟨-, ea, eb⟩ := na_del_ops n j D k hk'
  rw [ea, eb]
  generalize na_up j k = k' at *
  generalize opA D k' = a at *
  generalize opB D k' = b at *
  refine ⟨?_, ?_, ?_⟩ <;> unfold na_sh <;> split_ifs <;> omega

lemma H2.na_del_val {n : ℕ} {D : Dag} (hS : Strict n D) (j : ℕ) (hj : j < D.length)
    (hf : fanout D (n + j) = 0) (x : Fin n → Bool) (w : ℕ) (hw : w < n + (D.length - 1)) :
    val (na_del n j D) x w = val D x (na_up (n + j) w) := by
  refine val_unique (na_del_strict hS j hj hf) x (fun u => val D x (na_up (n + j) u))
    (fun i hi => ?_) (fun k hk => ?_) w (by rw [na_del_length n j D hj]; exact hw)
  · have e : na_up (n + j) i = i := by unfold na_up; split_ifs <;> omega
    show val D x (na_up (n + j) i) = x ⟨i, hi⟩
    rw [e]; exact val_input D x i hi
  · rw [na_del_length n j D hj] at hk
    have hk' : na_up j k < D.length := by unfold na_up; split_ifs <;> omega
    obtain ⟨et, ea, eb⟩ := na_del_ops n j D k hk'
    obtain ⟨ra, rb⟩ := na_no_reader hf _ hk'
    have e1 : na_up (n + j) (n + k) = n + na_up j k := by unfold na_up; split_ifs <;> omega
    have e2 : ∀ a, a ≠ n + j → na_up (n + j) (na_sh (n + j) a) = a := by
      intro a ha; unfold na_up na_sh; split_ifs <;> omega
    show val D x (na_up (n + j) (n + k)) = gop (tag (na_del n j D) k)
      (val D x (na_up (n + j) (opA (na_del n j D) k)))
      (val D x (na_up (n + j) (opB (na_del n j D) k)))
    rw [e1, et, ea, eb, e2 _ ra, e2 _ rb]
    exact val_gate hS x _ hk'

section SurplusFlow

variable {n : ℕ} {D : Dag}

lemma H2.sb_mem_inner {w : ℕ} : w ∈ inner n D ↔ w + 1 < n + D.length := by
  unfold inner; rw [Finset.mem_range]; omega

lemma H2.sb_src_false (j : ℕ) : src D (j, false) = opA D j := by simp [src]

lemma H2.sb_src_true (j : ℕ) : src D (j, true) = opB D j := by simp [src]

lemma H2.fanout_eq_zero_of_ge (hS : Strict n D) (w : ℕ) (h : n + D.length ≤ w + 1) :
    fanout D w = 0 := by
  unfold fanout readers
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro j hj
  have hj2 := Finset.mem_range.mp hj
  have := hS j hj2
  omega

lemma H2.lt_of_fanout_pos (hS : Strict n D) {w : ℕ} (h : 1 ≤ fanout D w) :
    w + 1 < n + D.length := by
  by_contra hc
  have := fanout_eq_zero_of_ge hS w (by omega)
  omega

lemma H2.sb_card_arcs_filter (P : ℕ × Bool → Prop) [DecidablePred P] :
    ((arcs D).filter P).card = ∑ j ∈ Finset.range D.length,
      ((if P (j, false) then 1 else 0) + (if P (j, true) then 1 else 0)) := by
  rw [Finset.card_filter, arcs, Finset.sum_product]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Fintype.sum_bool, add_comm]

lemma H2.sb_card_arcs : (arcs D).card = 2 * D.length := by
  simp [arcs, Finset.card_product, Nat.mul_comm]

lemma H2.sb_src_lt (hS : Strict n D) (e : ℕ × Bool) (he : e ∈ arcs D) :
    src D e + 1 < n + D.length := by
  obtain ⟨j, c⟩ := e
  have hj : j < D.length := by simpa [arcs] using he
  have := hS j hj
  cases c
  · rw [sb_src_false]; omega
  · rw [sb_src_true]; omega

lemma H2.sb_fanout_arcs (hS : Strict n D) (w : ℕ) :
    fanout D w = ((arcs D).filter (fun e => src D e = w)).card := by
  rw [sb_card_arcs_filter, fanout, readers, Finset.card_filter]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have := (hS j (Finset.mem_range.mp hj)).2.2
  rw [sb_src_false, sb_src_true]
  split_ifs <;> omega

lemma H2.sb_sum_fanout_eq (hS : Strict n D) (K : Finset ℕ) :
    ∑ w ∈ K, fanout D w = ((arcs D).filter (fun e => src D e ∈ K)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := src D)
    (s := (arcs D).filter (fun e => src D e ∈ K)) (t := K)
    (fun e he => Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp he)).2)]
  refine Finset.sum_congr rfl (fun w hw => ?_)
  rw [sb_fanout_arcs hS, Finset.filter_filter]
  congr 1
  ext e
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨he, rfl⟩; exact ⟨he, hw, rfl⟩
  · rintro ⟨he, -, h⟩; exact ⟨he, h⟩

lemma H2.sb_surplus_add_card {K : Finset ℕ} (hL : ∀ w ∈ K, 1 ≤ fanout D w) :
    surplusOn D K + K.card = ∑ w ∈ K, fanout D w := by
  rw [surplusOn, Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun w hw => Nat.sub_add_cancel (hL w hw))

lemma H2.surplus_identity (h : StrictLive n D) : totalSurplus n D + n = D.length + 1 := by
  obtain ⟨hS, hL, hne⟩ := h
  have hpos : 0 < D.length := List.length_pos_iff.mpr hne
  have h1 : surplusOn D (inner n D) + (inner n D).card = ∑ w ∈ inner n D, fanout D w :=
    sb_surplus_add_card (fun w hw => hL w (sb_mem_inner.mp hw))
  have h2 : ∑ w ∈ inner n D, fanout D w = 2 * D.length := by
    rw [sb_sum_fanout_eq hS, Finset.filter_true_of_mem, sb_card_arcs]
    intro e he
    exact sb_mem_inner.mpr (sb_src_lt hS e he)
  have h3 : (inner n D).card = n + D.length - 1 := Finset.card_range _
  unfold totalSurplus
  omega

lemma H2.totalSurplus_split (n : ℕ) (D : Dag) : totalSurplus n D = Bplus n D + Bzero n D := by
  unfold totalSurplus Bplus Bzero surplusOn
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

lemma H2.mem_supp {v : Fin n} {w : ℕ} : v ∈ supp n D w ↔ val D (single v) w = true := by
  simp [supp]

lemma H2.val_mono (hS : Strict n D) (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true)
    (w : ℕ) : val D x w = true → val D y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · rw [val_input D x w hn, val_input D y w hn]; exact hxy _
    · by_cases hw : w < n + D.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < D.length := by omega
        obtain ⟨ha, hb, -⟩ := hS j hj
        rw [val_gate hS x j hj, val_gate hS y j hj]
        have h1 := ih _ ha
        have h2 := ih _ hb
        cases tag D j <;>
          simp only [gop_true, gop_false, Bool.and_eq_true, Bool.or_eq_true] <;> tauto
      · rw [val_ge D x w (by omega)]; simp

lemma H2.supp_input (D : Dag) (i : Fin n) : supp n D i.val = {i} := by
  ext v
  rw [mem_supp, val_input D (single v) i.val i.isLt]
  simp [single, eq_comm]

lemma H2.supp_ge (D : Dag) (w : ℕ) (h : n + D.length ≤ w) : supp n D w = ∅ := by
  ext v
  simp [mem_supp, val_ge D (single v) w h]

lemma H2.supp_gate (hS : Strict n D) (j : ℕ) (hj : j < D.length) :
    supp n D (n + j) = if tag D j = true then supp n D (opA D j) ∩ supp n D (opB D j)
      else supp n D (opA D j) ∪ supp n D (opB D j) := by
  ext v
  rw [mem_supp, val_gate hS _ j hj]
  cases tag D j <;> simp [mem_supp]

lemma H2.carrier_flow (h : StrictLive n D) (K : Finset ℕ) (hK : K ⊆ inner n D)
    (hpred : ∀ j, j < D.length → n + j ∈ K → opA D j ∈ K ∨ opB D j ∈ K) :
    (exitArcs n D K).card + (merges n D K).card = (sources n K).card + surplusOn D K := by
  obtain ⟨hS, hL, -⟩ := h
  have hKlt : ∀ w ∈ K, w + 1 < n + D.length := fun w hw => sb_mem_inner.mp (hK hw)
  have h1 : surplusOn D K + K.card = ((arcs D).filter (fun e => src D e ∈ K)).card := by
    rw [← sb_sum_fanout_eq hS, sb_surplus_add_card (fun w hw => hL w (hKlt w hw))]
  have h2 := Finset.card_filter_add_card_filter_not
    (s := (arcs D).filter (fun e => src D e ∈ K)) (fun e : ℕ × Bool => n + e.1 ∈ K)
  rw [Finset.filter_filter, Finset.filter_filter] at h2
  have h3 : ((arcs D).filter (fun e => src D e ∈ K ∧ n + e.1 ∈ K)).card =
      ((Finset.range D.length).filter (fun j => n + j ∈ K)).card + (merges n D K).card := by
    rw [sb_card_arcs_filter, merges, Finset.card_filter, Finset.card_filter,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have := hpred j (Finset.mem_range.mp hj)
    rw [sb_src_false, sb_src_true]
    by_cases hj2 : n + j ∈ K <;> by_cases ha : opA D j ∈ K <;> by_cases hb : opB D j ∈ K <;>
      simp_all
  have h4 : K.card = (sources n K).card +
      ((Finset.range D.length).filter (fun j => n + j ∈ K)).card := by
    rw [← Finset.card_filter_add_card_filter_not (s := K) (fun w => w < n), sources]
    congr 1
    have himg : K.filter (fun w => ¬ w < n) =
        ((Finset.range D.length).filter (fun j => n + j ∈ K)).image (fun j => n + j) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨hw, hn⟩
        have := hKlt w hw
        exact ⟨w - n, ⟨by omega, by rwa [Nat.add_sub_cancel' (by omega)]⟩, by omega⟩
      · rintro ⟨j, ⟨-, hj⟩, rfl⟩
        exact ⟨hj, by omega⟩
    rw [himg, Finset.card_image_of_injective _ (add_right_injective n)]
  unfold exitArcs
  omega

lemma H2.sb_carrierT_sub (T : Finset (Fin n))
    (hout : supp n D (outW n D) ∩ T = ∅) : carrierT n D T ⊆ inner n D := by
  intro w hw
  simp only [carrierT, Finset.mem_filter, Finset.mem_range] at hw
  rw [sb_mem_inner]
  by_contra hc
  have hw2 : w = outW n D := by unfold outW; omega
  rw [hw2, hout] at hw
  exact Finset.not_nonempty_empty hw.2

lemma H2.sb_sources_carrierT (D : Dag) (T : Finset (Fin n)) :
    (sources n (carrierT n D T)).card = T.card := by
  have himg : sources n (carrierT n D T) = T.image (fun v : Fin n => v.val) := by
    ext w
    simp only [sources, carrierT, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨⟨-, v, hv⟩, hw⟩
      have hs : supp n D w = {⟨w, hw⟩} := supp_input D ⟨w, hw⟩
      rw [hs, Finset.mem_inter, Finset.mem_singleton] at hv
      exact ⟨v, hv.2, by rw [hv.1]⟩
    · rintro ⟨v, hv, rfl⟩
      refine ⟨⟨by have := v.isLt; omega, v, ?_⟩, v.isLt⟩
      rw [supp_input]; simp [hv]
  rw [himg, Finset.card_image_of_injective _ Fin.val_injective]

lemma H2.carrier_flow_union (h : StrictLive n D) (T : Finset (Fin n))
    (hout : supp n D (outW n D) ∩ T = ∅) :
    (exitArcs n D (carrierT n D T)).card + (merges n D (carrierT n D T)).card =
      T.card + surplusOn D (carrierT n D T) := by
  rw [← sb_sources_carrierT D T]
  refine carrier_flow h _ (sb_carrierT_sub T hout) (fun j hj hK => ?_)
  obtain ⟨ha, hb, -⟩ := h.1 j hj
  simp only [carrierT, Finset.mem_filter, Finset.mem_range] at hK ⊢
  obtain ⟨v, hv⟩ := hK.2
  rw [Finset.mem_inter, supp_gate h.1 j hj] at hv
  split_ifs at hv with ht
  · rw [Finset.mem_inter] at hv
    exact Or.inl ⟨by omega, v, Finset.mem_inter.mpr ⟨hv.1.1, hv.2⟩⟩
  · rw [Finset.mem_union] at hv
    rcases hv.1 with h1 | h1
    · exact Or.inl ⟨by omega, v, Finset.mem_inter.mpr ⟨h1, hv.2⟩⟩
    · exact Or.inr ⟨by omega, v, Finset.mem_inter.mpr ⟨h1, hv.2⟩⟩

lemma H2.mem_units {u : Σ _ : ℕ, ℕ} :
    u ∈ units n D ↔ u.1 ∈ inner n D ∧ u.2 + 1 < fanout D u.1 := by
  rw [units, Finset.mem_sigma, Finset.mem_range]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩

lemma H2.sb_card_units_filter (n : ℕ) (D : Dag) (p : ℕ → Prop) [DecidablePred p] :
    ((units n D).filter (fun u => p u.1)).card = surplusOn D ((inner n D).filter p) := by
  have hs : (units n D).filter (fun u => p u.1) =
      ((inner n D).filter p).sigma (fun w => Finset.range (fanout D w - 1)) := by
    ext u; simp only [units, Finset.mem_filter, Finset.mem_sigma]; tauto
  rw [hs, Finset.card_sigma, surplusOn]
  simp

lemma H2.card_unitsPlus (n : ℕ) (D : Dag) : (unitsPlus n D).card = Bplus n D := by
  unfold unitsPlus Bplus
  exact sb_card_units_filter n D (fun w => (supp n D w).Nonempty)

lemma H2.mem_eligSet {v : Fin n} :
    v ∈ eligSet n D ↔ ∃ w, 2 ≤ fanout D w ∧ v ∈ supp n D w := by
  simp only [eligSet, branchW, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨w, ⟨-, h2⟩, hv⟩; exact ⟨w, h2, hv⟩
  · rintro ⟨w, h2, hv⟩
    refine ⟨w, ⟨?_, h2⟩, hv⟩
    by_contra hc
    rw [supp_ge D w (by omega)] at hv
    exact Finset.notMem_empty v hv

lemma H2.mem_ineligSet {v : Fin n} :
    v ∈ ineligSet n D ↔ ∀ w, v ∈ supp n D w → fanout D w ≤ 1 := by
  rw [ineligSet, Finset.mem_sdiff, mem_eligSet]
  constructor
  · rintro ⟨-, h⟩ w hw
    by_contra hc
    exact h ⟨w, by omega, hw⟩
  · intro h
    refine ⟨Finset.mem_univ v, ?_⟩
    rintro ⟨w, hw, hv⟩
    have := h w hv
    omega

lemma H2.sb_singleton_inter_nonempty {v : Fin n} {T : Finset (Fin n)} :
    (({v} : Finset (Fin n)) ∩ T).Nonempty ↔ v ∈ T := by
  constructor
  · rintro ⟨u, hu⟩
    rw [Finset.mem_inter, Finset.mem_singleton] at hu
    exact hu.1 ▸ hu.2
  · intro h
    exact ⟨v, Finset.mem_inter.mpr ⟨Finset.mem_singleton_self v, h⟩⟩

lemma H2.sb_reserved_inj (b : Fin n → ℕ) (hb : PureBranch n D b) :
    Set.InjOn (fun v => (⟨b v, 0⟩ : Σ _ : ℕ, ℕ)) (eligSet n D : Set (Fin n)) := by
  intro v hv v2 hv2 he
  have hbv : b v = b v2 := congrArg Sigma.fst he
  have h1 := (hb v hv).2
  rw [hbv, (hb v2 hv2).2] at h1
  exact (Finset.singleton_injective h1).symm

lemma H2.reserved_subset (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b) :
    reservedUnits n D b ⊆ unitsPlus n D := by
  intro u hu
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨h2, hs⟩ := hb v hv
  have h1 : 1 ≤ fanout D (b v) := by omega
  rw [unitsPlus, Finset.mem_filter, mem_units]
  refine ⟨⟨sb_mem_inner.mpr (lt_of_fanout_pos hS h1), ?_⟩, ?_⟩
  · show 0 + 1 < fanout D (b v)
    omega
  · show (supp n D (b v)).Nonempty
    rw [hs]; exact Finset.singleton_nonempty v

lemma H2.card_reserved (b : Fin n → ℕ) (hb : PureBranch n D b) :
    (reservedUnits n D b).card = (eligSet n D).card :=
  Finset.card_image_of_injOn (sb_reserved_inj b hb)

lemma H2.elig_le_Bplus (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b) :
    (eligSet n D).card ≤ Bplus n D := by
  rw [← card_reserved b hb, ← card_unitsPlus]
  exact Finset.card_le_card (reserved_subset hS b hb)

lemma H2.card_residual (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b) :
    (residualUnits n D b).card + (eligSet n D).card = Bplus n D := by
  rw [← card_reserved b hb, ← card_unitsPlus]
  exact Finset.card_sdiff_add_card_eq_card (reserved_subset hS b hb)

lemma H2.surplus_carrierT_eq (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b)
    (T : Finset (Fin n)) :
    surplusOn D (carrierT n D T) = (T ∩ eligSet n D).card +
      ((residualUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty)).card := by
  have h1 : surplusOn D (carrierT n D T) =
      ((units n D).filter (fun u => (supp n D u.1 ∩ T).Nonempty)).card := by
    rw [sb_card_units_filter n D (fun w => (supp n D w ∩ T).Nonempty)]
    symm
    refine Finset.sum_subset (fun w hw => ?_) (fun w hw hnot => ?_)
    · rw [Finset.mem_filter] at hw
      have := sb_mem_inner.mp hw.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hw.2⟩
    · rw [carrierT, Finset.mem_filter] at hw
      have hni : w ∉ inner n D := fun hc => hnot (Finset.mem_filter.mpr ⟨hc, hw.2⟩)
      rw [sb_mem_inner] at hni
      simp [fanout_eq_zero_of_ge hS w (by omega)]
  have h2 : (units n D).filter (fun u => (supp n D u.1 ∩ T).Nonempty) =
      (reservedUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty) ∪
        (residualUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty) := by
    ext u
    have hsub := reserved_subset hS b hb
    simp only [residualUnits, unitsPlus, Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · intro hu
      by_cases hr : u ∈ reservedUnits n D b
      · exact Or.inl ⟨hr, hu.2⟩
      · exact Or.inr ⟨⟨⟨hu.1, hu.2.mono Finset.inter_subset_left⟩, hr⟩, hu.2⟩
    · rintro (hu | hu)
      · exact ⟨(Finset.mem_filter.mp (hsub hu.1)).1, hu.2⟩
      · exact ⟨hu.1.1.1, hu.2⟩
  have h3 : Disjoint ((reservedUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty))
      ((residualUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty)) :=
    Finset.disjoint_filter_filter Finset.disjoint_sdiff
  have h4 : (reservedUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty) =
      (T ∩ eligSet n D).image (fun v => (⟨b v, 0⟩ : Σ _ : ℕ, ℕ)) := by
    rw [reservedUnits, Finset.filter_image]
    congr 1
    ext v
    simp only [Finset.mem_filter, Finset.mem_inter]
    constructor
    · rintro ⟨hv, hne⟩
      rw [(hb v hv).2, sb_singleton_inter_nonempty] at hne
      exact ⟨hne, hv⟩
    · rintro ⟨hT, hv⟩
      refine ⟨hv, ?_⟩
      rw [(hb v hv).2, sb_singleton_inter_nonempty]
      exact hT
  rw [h1, h2, Finset.card_union_of_disjoint h3, h4,
    Finset.card_image_of_injOn ((sb_reserved_inj b hb).mono
      (Finset.coe_subset.mpr Finset.inter_subset_right))]

end SurplusFlow

def H2.liftP {n : ℕ} (σ : Equiv.Perm (Fin n)) (w : ℕ) : ℕ :=
  if h : w < n then (σ ⟨w, h⟩).val else w

def H2.relabel {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) : Dag :=
  D.map (fun g => (g.1, liftP σ g.2.1, liftP σ g.2.2))

lemma H2.tr_liftP_lt {n : ℕ} (σ : Equiv.Perm (Fin n)) {w : ℕ} (h : w < n) :
    liftP σ w = (σ ⟨w, h⟩).val := by
  simp [liftP, h]

lemma H2.tr_liftP_ge {n : ℕ} (σ : Equiv.Perm (Fin n)) {w : ℕ} (h : n ≤ w) : liftP σ w = w := by
  simp [liftP, Nat.not_lt.mpr h]

lemma H2.tr_liftP_lt_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) {m : ℕ} (hm : n ≤ m) (w : ℕ) :
    liftP σ w < m ↔ w < m := by
  by_cases h : w < n
  · rw [tr_liftP_lt σ h]
    have := (σ ⟨w, h⟩).isLt
    constructor <;> intro <;> omega
  · rw [tr_liftP_ge σ (Nat.not_lt.mp h)]

lemma H2.liftP_inv {n : ℕ} (σ : Equiv.Perm (Fin n)) (w : ℕ) : liftP σ⁻¹ (liftP σ w) = w := by
  by_cases h : w < n
  · rw [tr_liftP_lt σ h, tr_liftP_lt σ⁻¹ (σ ⟨w, h⟩).isLt]; simp
  · rw [tr_liftP_ge σ (Nat.not_lt.mp h), tr_liftP_ge σ⁻¹ (Nat.not_lt.mp h)]

lemma H2.tr_liftP_inv' {n : ℕ} (σ : Equiv.Perm (Fin n)) (w : ℕ) : liftP σ (liftP σ⁻¹ w) = w := by
  simpa using liftP_inv σ⁻¹ w

lemma H2.tr_liftP_inj {n : ℕ} (σ : Equiv.Perm (Fin n)) {a b : ℕ} :
    liftP σ a = liftP σ b ↔ a = b := by
  refine ⟨fun h => ?_, congrArg _⟩
  have := congrArg (liftP σ⁻¹) h
  rwa [liftP_inv, liftP_inv] at this

lemma H2.relabel_length {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) :
    (relabel σ D).length = D.length := by
  simp [relabel]

lemma H2.tr_tag {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (j : ℕ) (hj : j < D.length) :
    tag (relabel σ D) j = tag D j := by
  rw [tag_eq _ j (by rw [relabel_length]; exact hj), tag_eq D j hj]; simp [relabel]

lemma H2.tr_opA {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (j : ℕ) (hj : j < D.length) :
    opA (relabel σ D) j = liftP σ (opA D j) := by
  rw [opA_eq _ j (by rw [relabel_length]; exact hj), opA_eq D j hj]; simp [relabel]

lemma H2.tr_opB {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (j : ℕ) (hj : j < D.length) :
    opB (relabel σ D) j = liftP σ (opB D j) := by
  rw [opB_eq _ j (by rw [relabel_length]; exact hj), opB_eq D j hj]; simp [relabel]

lemma H2.relabel_strict {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) :
    Strict n (relabel σ D) := by
  intro j hj
  rw [relabel_length] at hj
  obtain ⟨ha, hb, hab⟩ := hS j hj
  rw [tr_opA σ D j hj, tr_opB σ D j hj]
  exact ⟨(tr_liftP_lt_iff σ (Nat.le_add_right n j) _).mpr ha,
    (tr_liftP_lt_iff σ (Nat.le_add_right n j) _).mpr hb, fun h => hab ((tr_liftP_inj σ).mp h)⟩

lemma H2.relabel_val {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D)
    (x : Fin n → Bool) (w : ℕ) :
    val (relabel σ D) x (liftP σ w) = val D (fun i => x (σ i)) w := by
  by_cases hw : w < n + D.length
  · refine (val_unique (relabel_strict σ hS) x
      (fun w' => val D (fun i => x (σ i)) (liftP σ⁻¹ w')) ?_ ?_ (liftP σ w) ?_).trans ?_
    · intro i hi
      show val D (fun i => x (σ i)) (liftP σ⁻¹ i) = x ⟨i, hi⟩
      rw [tr_liftP_lt σ⁻¹ hi, val_input D _ _ (σ⁻¹ ⟨i, hi⟩).isLt]
      simp
    · intro j hj
      rw [relabel_length] at hj
      show val D (fun i => x (σ i)) (liftP σ⁻¹ (n + j)) =
        gop (tag (relabel σ D) j) (val D (fun i => x (σ i)) (liftP σ⁻¹ (opA (relabel σ D) j)))
          (val D (fun i => x (σ i)) (liftP σ⁻¹ (opB (relabel σ D) j)))
      rw [tr_liftP_ge σ⁻¹ (Nat.le_add_right n j), tr_tag σ D j hj, tr_opA σ D j hj,
        tr_opB σ D j hj, liftP_inv, liftP_inv, val_gate hS _ j hj]
    · rw [relabel_length]; exact (tr_liftP_lt_iff σ (Nat.le_add_right _ _) w).mpr hw
    · show val D (fun i => x (σ i)) (liftP σ⁻¹ (liftP σ w)) = _
      rw [liftP_inv]
  · have hw' := Nat.not_lt.mp hw
    rw [tr_liftP_ge σ (le_trans (Nat.le_add_right _ _) hw'),
      val_ge _ _ _ (by rw [relabel_length]; exact hw'), val_ge _ _ _ hw']

lemma H2.relabel_fanout {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (w : ℕ) :
    fanout (relabel σ D) (liftP σ w) = fanout D w := by
  unfold fanout readers
  rw [relabel_length]
  congr 1
  apply Finset.filter_congr
  intro j hj
  have hj' := Finset.mem_range.mp hj
  rw [tr_opA σ D j hj', tr_opB σ D j hj', tr_liftP_inj, tr_liftP_inj]

lemma H2.relabel_live {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hL : Live n D) :
    Live n (relabel σ D) := by
  rcases eq_or_ne D [] with rfl | hne
  · exact hL
  · intro w' hw'
    rw [relabel_length] at hw'
    have hpos := List.length_pos_iff.mpr hne
    rw [← tr_liftP_inv' σ w', relabel_fanout]
    apply hL
    by_cases h : w' < n
    · have := (tr_liftP_lt_iff σ⁻¹ le_rfl w').mpr h
      omega
    · rw [tr_liftP_ge σ⁻¹ (Nat.not_lt.mp h)]; exact hw'

lemma H2.relabel_strictLive {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (h : StrictLive n D) :
    StrictLive n (relabel σ D) :=
  ⟨relabel_strict σ h.1, relabel_live σ h.2.1, by simpa [relabel] using h.2.2⟩

lemma H2.relabel_out {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) (hne : D ≠ [])
    (x : Fin n → Bool) :
    val (relabel σ D) x (outW n (relabel σ D)) = val D (fun i => x (σ i)) (outW n D) := by
  have hpos := List.length_pos_iff.mpr hne
  have e : outW n (relabel σ D) = liftP σ (outW n D) := by
    rw [tr_liftP_ge σ (by unfold outW; omega)]; simp [outW, relabel_length]
  rw [e, relabel_val σ hS]

lemma H2.tr_single_comp {n : ℕ} (σ : Equiv.Perm (Fin n)) (v : Fin n) :
    (fun i => single v (σ i)) = single (σ⁻¹ v) := by
  funext i
  simp only [single, decide_eq_decide]
  constructor
  · intro h; rw [← h]; simp
  · intro h; rw [h]; simp

lemma H2.relabel_supp {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) (w : ℕ) :
    supp n (relabel σ D) (liftP σ w) = (supp n D w).image σ := by
  ext v
  simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  rw [relabel_val σ hS, tr_single_comp]
  constructor
  · intro h; exact ⟨σ⁻¹ v, h, by simp⟩
  · rintro ⟨a, ha, rfl⟩; simpa using ha

lemma H2.inelig_card_add (n : ℕ) (D : Dag) : (ineligSet n D).card + (eligSet n D).card = n := by
  have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (eligSet n D))
  rw [Finset.card_univ, Fintype.card_fin] at h
  exact h

def H2.sem_Edge {n : ℕ} (G : Fin n → Fin n → Prop) (x : Fin n → Bool) : Prop :=
  ∃ u v : Fin n, G u v ∧ x u = true ∧ x v = true

def H2.sem_Comp (n : ℕ) (G : Fin n → Fin n → Prop) (D : Dag) : Prop :=
  ∀ x : Fin n → Bool, val D x (outW n D) = true ↔ sem_Edge G x

def H2.sem_Gr {n : ℕ} (G : Fin n → Fin n → Prop) : Prop :=
  (∀ u v, G u v → G v u) ∧ (∀ u, ¬ G u u) ∧ (∀ v w, v ≠ w → ∃ z, G v z ∧ ¬ G w z) ∧
    (∀ u v, ∃ a, G u a ∧ a ≠ v)

def H2.sem_step (n : ℕ) (D : Dag) (a b : ℕ) : Prop :=
  b < n + D.length ∧ n ≤ b ∧ (opA D (b - n) = a ∨ opB D (b - n) = a)

def H2.sem_two {n : ℕ} (u z : Fin n) : Fin n → Bool := fun i => decide (i = u) || decide (i = z)

def H2.sem_ins {n : ℕ} (v : Fin n) (x : Fin n → Bool) : Fin n → Bool := fun i => decide (i = v) || x i

def H2.sem_ind {n : ℕ} (A : Finset (Fin n)) : Fin n → Bool := fun i => decide (i ∈ A)

lemma H2.sem_rtg_mono {α : Type} {r p : α → α → Prop} (h : ∀ a b, r a b → p a b) {a b : α}
    (hab : Relation.ReflTransGen r a b) : Relation.ReflTransGen p a b := by
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.tail ih (h _ _ hbc)

section SemCore

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

lemma H2.sem_ins_agree (v : Fin n) (x : Fin n → Bool) : ∀ k, k ≠ v → x k = sem_ins v x k := by
  intro k hk; simp [sem_ins, hk]

lemma H2.sem_ins_self (v : Fin n) (x : Fin n → Bool) : sem_ins v x v = true := by simp [sem_ins]

lemma H2.sem_single_le {x : Fin n → Bool} {u : Fin n} (hu : x u = true) :
    ∀ i, single u i = true → x i = true := by
  intro i hi
  simp only [single, decide_eq_true_eq] at hi
  rw [hi]; exact hu

lemma H2.sem_val_of_supp (hS : Strict n D) {u : Fin n} {w : ℕ} (hu : u ∈ supp n D w)
    {x : Fin n → Bool} (hx : x u = true) : val D x w = true :=
  val_mono hS (single u) x (sem_single_le hx) w (mem_supp.mp hu)

lemma H2.sem_supp_lt {v : Fin n} {w : ℕ} (hv : v ∈ supp n D w) : w < n + D.length := by
  by_contra hc
  rw [supp_ge D w (by omega)] at hv
  exact Finset.notMem_empty v hv

lemma H2.sem_supp_and (hS : Strict n D) {j : ℕ} (hj : j < D.length) (ht : tag D j = true) :
    supp n D (n + j) = supp n D (opA D j) ∩ supp n D (opB D j) := by
  rw [supp_gate hS j hj]; simp [ht]

lemma H2.sem_supp_or (hS : Strict n D) {j : ℕ} (hj : j < D.length) (ht : tag D j = false) :
    supp n D (n + j) = supp n D (opA D j) ∪ supp n D (opB D j) := by
  rw [supp_gate hS j hj]; simp [ht]

lemma H2.sem_supp_and_sub (hS : Strict n D) {j : ℕ} (hj : j < D.length) (ht : tag D j = true)
    (s : Bool) : supp n D (n + j) ⊆ supp n D (src D (j, s)) := by
  rw [sem_supp_and hS hj ht]
  cases s
  · rw [sb_src_false]; exact Finset.inter_subset_left
  · rw [sb_src_true]; exact Finset.inter_subset_right

lemma H2.sem_src_lt (hS : Strict n D) {j : ℕ} (hj : j < D.length) (s : Bool) :
    src D (j, s) < n + j := by
  obtain ⟨ha, hb, -⟩ := hS j hj
  cases s
  · rw [sb_src_false]; exact ha
  · rw [sb_src_true]; exact hb

lemma H2.sem_step_src {j : ℕ} (hj : j < D.length) (s : Bool) :
    sem_step n D (src D (j, s)) (n + j) := by
  refine ⟨by omega, by omega, ?_⟩
  rw [Nat.add_sub_cancel_left]
  cases s
  · exact Or.inl (sb_src_false j).symm
  · exact Or.inr (sb_src_true j).symm

lemma H2.sem_step_reader {a c : ℕ} (h : sem_step n D a c) : c - n ∈ readers D a := by
  unfold readers
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨by have := h.1; have := h.2.1; omega, h.2.2⟩

lemma H2.sem_step_fanout {a c : ℕ} (h : sem_step n D a c) : 1 ≤ fanout D a :=
  Finset.card_pos.mpr ⟨_, sem_step_reader h⟩

lemma H2.sem_step_unique {a c c' : ℕ} (h1 : sem_step n D a c) (h2 : sem_step n D a c')
    (hf : fanout D a = 1) : c = c' := by
  have m1 := sem_step_reader h1
  have m2 := sem_step_reader h2
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp (show (readers D a).card = 1 from hf)
  rw [hr, Finset.mem_singleton] at m1 m2
  have := h1.2.1
  have := h2.2.1
  omega

lemma H2.sem_changed_path (hS : Strict n D) (x y : Fin n → Bool) (v : Fin n)
    (hxy : ∀ k, k ≠ v → x k = y k) (w : ℕ) (hw : val D x w ≠ val D y w) :
    Relation.ReflTransGen (fun a b => sem_step n D a b ∧ val D x b ≠ val D y b) v.val w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · rw [val_input D x w hn, val_input D y w hn] at hw
      have hwv : (⟨w, hn⟩ : Fin n) = v := by
        by_contra hc; exact hw (hxy _ hc)
      rw [← hwv]
    · by_cases hlt : w < n + D.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < D.length := by omega
        obtain ⟨ha, hb, -⟩ := hS j hj
        have hg := hw
        rw [val_gate hS x j hj, val_gate hS y j hj] at hg
        by_cases h1 : val D x (opA D j) = val D y (opA D j)
        · have h2 : val D x (opB D j) ≠ val D y (opB D j) := by
            intro h2; apply hg; rw [h1, h2]
          exact Relation.ReflTransGen.tail (ih _ hb h2)
            ⟨⟨hlt, by omega, Or.inr (by rw [Nat.add_sub_cancel_left])⟩, hw⟩
        · exact Relation.ReflTransGen.tail (ih _ ha h1)
            ⟨⟨hlt, by omega, Or.inl (by rw [Nat.add_sub_cancel_left])⟩, hw⟩
      · exfalso; apply hw; rw [val_ge D x w (by omega), val_ge D y w (by omega)]

def H2.sem_Dom (n : ℕ) (D : Dag) (b v : ℕ) : Prop :=
  b = v ∨ ¬ Relation.ReflTransGen (fun a c => sem_step n D a c ∧ c ≠ b) v (outW n D)

lemma H2.sem_dom_eq (hS : Strict n D) (x y : Fin n → Bool) (v : Fin n)
    (hxy : ∀ k, k ≠ v → x k = y k) (b : ℕ) (hdom : sem_Dom n D b v.val)
    (hb : val D x b = val D y b) : val D x (outW n D) = val D y (outW n D) := by
  by_contra hne
  rcases hdom with rfl | hdom
  · rw [val_input D x _ v.isLt, val_input D y _ v.isLt] at hb
    have hxy2 : x = y := by
      funext k
      by_cases hk : k = v
      · rw [hk]; exact hb
      · exact hxy k hk
    exact hne (by rw [hxy2])
  · exact hdom (sem_rtg_mono
      (fun a c h => ⟨h.1, fun hc => h.2 (by rw [hc]; exact hb)⟩)
      (sem_changed_path hS x y v hxy _ hne))

def H2.sem_Chain (n : ℕ) (D : Dag) (a b : ℕ) : Prop :=
  Relation.ReflTransGen (fun a c => sem_step n D a c ∧ fanout D a = 1) a b

lemma H2.sem_chain_dom (hS : Strict n D) {v b : ℕ} (h : sem_Chain n D v b) :
    sem_Dom n D b v := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Or.inl rfl
  | @head a c hstep _ ih =>
    by_cases hba : b = a
    · exact Or.inl hba
    · right
      intro hp
      rcases Relation.ReflTransGen.cases_head hp with heq | ⟨c', hs, hrest⟩
      · have h0 := fanout_eq_zero_of_ge hS a (by rw [heq]; unfold outW; omega)
        have h1 := hstep.2
        omega
      · have hcc : c = c' := sem_step_unique hstep.1 hs.1 hstep.2
        subst hcc
        rcases ih with rfl | ih
        · exact hs.2 rfl
        · exact ih hrest

lemma H2.sem_carrier_chain (hS : Strict n D) (v : Fin n) : ∀ w, v ∈ supp n D w →
    (∀ u, u < w → v ∈ supp n D u → fanout D u ≤ 1) → sem_Chain n D v.val w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv hlow
    by_cases hn : w < n
    · have hs : supp n D w = {⟨w, hn⟩} := supp_input D ⟨w, hn⟩
      rw [hs, Finset.mem_singleton] at hv
      rw [hv]; exact Relation.ReflTransGen.refl
    · have hlt := sem_supp_lt hv
      obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < D.length := by omega
      have key : ∀ s : Bool, v ∈ supp n D (src D (j, s)) → sem_Chain n D v.val (n + j) := by
        intro s hva
        have hstep : sem_step n D (src D (j, s)) (n + j) := sem_step_src hj s
        have hlt' := sem_src_lt hS hj s
        have h1 := sem_step_fanout hstep
        have h2 := hlow _ hlt' hva
        exact Relation.ReflTransGen.tail (ih _ hlt' hva (fun u hu => hlow u (by omega)))
          ⟨hstep, by omega⟩
      rw [supp_gate hS j hj] at hv
      split_ifs at hv with ht
      · exact key false (by rw [sb_src_false]; exact (Finset.mem_inter.mp hv).1)
      · rcases Finset.mem_union.mp hv with h1 | h1
        · exact key false (by rw [sb_src_false]; exact h1)
        · exact key true (by rw [sb_src_true]; exact h1)

lemma H2.sem_single_no_edge (hG : sem_Gr G) (v : Fin n) : ¬ sem_Edge G (single v) := by
  rintro ⟨a, c, hac, ha, hc⟩
  simp only [single, decide_eq_true_eq] at ha hc
  rw [ha, hc] at hac
  exact hG.2.1 _ hac

lemma H2.sem_two_edge {u v : Fin n} (huv : G u v) : sem_Edge G (sem_two u v) :=
  ⟨u, v, huv, by simp [sem_two], by simp [sem_two]⟩

lemma H2.sem_supp_out (hG : sem_Gr G) (hC : sem_Comp n G D) : supp n D (outW n D) = ∅ :=
  Finset.eq_empty_iff_forall_notMem.2
    (fun v hv => sem_single_no_edge hG v ((hC _).1 (mem_supp.1 hv)))

lemma H2.sem_dom_pure (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) (v : Fin n)
    (b : ℕ) (hdom : sem_Dom n D b v.val) : supp n D b ⊆ {v} := by
  intro u hu
  rw [Finset.mem_singleton]
  by_contra huv
  obtain ⟨hsym, hirr, hsep, -⟩ := hG
  obtain ⟨z, hvz, huz⟩ := hsep v u (Ne.symm huv)
  have hxb : val D (sem_two u z) b = true := sem_val_of_supp hS hu (by simp [sem_two])
  have hyb : val D (sem_ins v (sem_two u z)) b = true :=
    sem_val_of_supp hS hu (by simp [sem_ins, sem_two])
  have hout := sem_dom_eq hS _ _ v (sem_ins_agree v (sem_two u z)) b hdom (by rw [hxb, hyb])
  have h1 : ¬ sem_Edge G (sem_two u z) := by
    rintro ⟨a, c, hac, ha, hc⟩
    simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at ha hc
    rcases ha with ha | ha <;> rcases hc with hc | hc <;> rw [ha, hc] at hac
    · exact hirr _ hac
    · exact huz hac
    · exact huz (hsym _ _ hac)
    · exact hirr _ hac
  have h2 : sem_Edge G (sem_ins v (sem_two u z)) :=
    ⟨v, z, hvz, sem_ins_self v _, by simp [sem_ins, sem_two]⟩
  have h3 := (hC _).mpr h2
  rw [← hout] at h3
  exact h1 ((hC _).mp h3)

lemma H2.sem_first_branch (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) (v : Fin n)
    (hv : v ∈ eligSet n D) :
    ∃ b, 2 ≤ fanout D b ∧ supp n D b = {v} ∧ sem_Chain n D v.val b := by
  classical
  have hex : ∃ w, 2 ≤ fanout D w ∧ v ∈ supp n D w := mem_eligSet.mp hv
  obtain ⟨h1, h2⟩ := Nat.find_spec hex
  have hch : sem_Chain n D v.val (Nat.find hex) :=
    sem_carrier_chain hS v _ h2 (fun u hu huv => by
      have := Nat.find_min hex hu
      by_contra hc
      exact this ⟨by omega, huv⟩)
  exact ⟨Nat.find hex, h1, Finset.Subset.antisymm
    (sem_dom_pure hG hS hC v _ (sem_chain_dom hS hch)) (Finset.singleton_subset_iff.mpr h2), hch⟩

def H2.sem_FirstBranch (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Prop :=
  ∀ v ∈ eligSet n D, 2 ≤ fanout D (b v) ∧ supp n D (b v) = {v} ∧ sem_Chain n D v.val (b v)

lemma H2.sem_exists_firstBranch (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) :
    ∃ b : Fin n → ℕ, sem_FirstBranch n D b := by
  classical
  have h : ∀ v : Fin n, ∃ b, v ∈ eligSet n D →
      2 ≤ fanout D b ∧ supp n D b = {v} ∧ sem_Chain n D v.val b := by
    intro v
    by_cases hv : v ∈ eligSet n D
    · obtain ⟨b, hb⟩ := sem_first_branch hG hS hC v hv
      exact ⟨b, fun _ => hb⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose b hb using h
  exact ⟨b, fun v hv => hb v hv⟩

lemma H2.sem_firstBranch_pure {b : Fin n → ℕ} (hb : sem_FirstBranch n D b) : PureBranch n D b :=
  fun v hv => ⟨(hb v hv).1, (hb v hv).2.1⟩

lemma H2.sem_exists_pureBranch (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) :
    ∃ b : Fin n → ℕ, PureBranch n D b := by
  obtain ⟨b, hb⟩ := sem_exists_firstBranch hG hS hC
  exact ⟨b, sem_firstBranch_pure hb⟩

lemma H2.sem_mem_inelig {v : Fin n} : v ∈ ineligSet n D ↔ v ∉ eligSet n D := by
  simp [ineligSet]

lemma H2.sem_inelig_chain (hS : Strict n D) {v : Fin n} (hv : v ∈ ineligSet n D) {w : ℕ}
    (hw : v ∈ supp n D w) : sem_Chain n D v.val w :=
  sem_carrier_chain hS v w hw (fun u _ hu => mem_ineligSet.mp hv u hu)

lemma H2.sem_inelig_pure (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) {v : Fin n}
    (hv : v ∈ ineligSet n D) {w : ℕ} (hw : v ∈ supp n D w) : supp n D w = {v} :=
  Finset.Subset.antisymm (sem_dom_pure hG hS hC v w (sem_chain_dom hS (sem_inelig_chain hS hv hw)))
    (Finset.singleton_subset_iff.mpr hw)

lemma H2.sem_mem_carrier1 {v : Fin n} {w : ℕ} : w ∈ carrierT n D {v} ↔ v ∈ supp n D w := by
  simp only [carrierT, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨-, u, hu⟩
    rw [Finset.mem_inter, Finset.mem_singleton] at hu
    exact hu.2 ▸ hu.1
  · intro h
    exact ⟨sem_supp_lt h, v, Finset.mem_inter.mpr ⟨h, Finset.mem_singleton_self v⟩⟩

lemma H2.sem_mem_exit1 {v : Fin n} {e : ℕ × Bool} : e ∈ exitArcs n D (carrierT n D {v}) ↔
    e.1 < D.length ∧ v ∈ supp n D (src D e) ∧ v ∉ supp n D (n + e.1) := by
  simp only [exitArcs, arcs, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    Finset.mem_univ, and_true, sem_mem_carrier1]

lemma H2.sem_inelig_surplus {v : Fin n} (hv : v ∈ ineligSet n D) :
    surplusOn D (carrierT n D {v}) = 0 := by
  unfold surplusOn
  refine Finset.sum_eq_zero (fun w hw => ?_)
  have := mem_ineligSet.mp hv w (sem_mem_carrier1.mp hw)
  omega

lemma H2.sem_joint_meeting (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {u v : Fin n} (huv : G u v) :
    ∃ j, j < D.length ∧ tag D j = true ∧ val D (sem_two u v) (n + j) = true ∧
      u ∉ supp n D (n + j) ∧ v ∉ supp n D (n + j) ∧
      ∃ s : Bool, u ∈ supp n D (src D (j, s)) ∧ v ∉ supp n D (src D (j, s)) ∧
        v ∈ supp n D (src D (j, !s)) ∧ u ∉ supp n D (src D (j, !s)) := by
  classical
  have hex : ∃ w, val D (sem_two u v) w = true ∧ u ∉ supp n D w ∧ v ∉ supp n D w :=
    ⟨outW n D, (hC _).2 (sem_two_edge huv), by rw [sem_supp_out hG hC]; simp,
      by rw [sem_supp_out hG hC]; simp⟩
  obtain ⟨hw1, hw2, hw3⟩ := Nat.find_spec hex
  have hmin : ∀ a, a < Nat.find hex → val D (sem_two u v) a = true →
      u ∈ supp n D a ∨ v ∈ supp n D a := by
    intro a ha hva
    by_contra hc
    rw [not_or] at hc
    exact Nat.find_min hex ha ⟨hva, hc.1, hc.2⟩
  generalize Nat.find hex = w at hw1 hw2 hw3 hmin
  have hlt : w < n + D.length := by
    by_contra hc
    rw [val_ge D _ w (by omega)] at hw1
    exact Bool.false_ne_true hw1
  have hn : n ≤ w := by
    by_contra hc
    have hc' : w < n := by omega
    rw [val_input D _ w hc'] at hw1
    have hs : supp n D w = {⟨w, hc'⟩} := supp_input D ⟨w, hc'⟩
    rw [hs, Finset.mem_singleton] at hw2 hw3
    simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at hw1
    rcases hw1 with h | h
    · exact hw2 h.symm
    · exact hw3 h.symm
  obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
  have hj : j < D.length := by omega
  obtain ⟨ha, hb, -⟩ := hS j hj
  have hval := hw1
  rw [val_gate hS _ j hj] at hw1
  rw [supp_gate hS j hj] at hw2 hw3
  cases ht : tag D j
  · exfalso
    rw [ht] at hw1 hw2 hw3
    simp only [gop_false, Bool.or_eq_true] at hw1
    simp only [Bool.false_eq_true, ite_false, Finset.mem_union, not_or] at hw2 hw3
    rcases hw1 with h | h
    · rcases hmin _ ha h with h' | h'
      · exact hw2.1 h'
      · exact hw3.1 h'
    · rcases hmin _ hb h with h' | h'
      · exact hw2.2 h'
      · exact hw3.2 h'
  · rw [ht] at hw1 hw2 hw3
    simp only [gop_true, Bool.and_eq_true] at hw1
    simp only [ite_true, Finset.mem_inter, not_and] at hw2 hw3
    have hsupp : u ∉ supp n D (n + j) ∧ v ∉ supp n D (n + j) := by
      rw [sem_supp_and hS hj ht]
      simp only [Finset.mem_inter, not_and]
      exact ⟨hw2, hw3⟩
    refine ⟨j, hj, ht, hval, hsupp.1, hsupp.2, ?_⟩
    rcases hmin _ ha hw1.1 with hA | hA
    · have hB : u ∉ supp n D (opB D j) := hw2 hA
      have hBv : v ∈ supp n D (opB D j) := (hmin _ hb hw1.2).resolve_left hB
      exact ⟨false, by simpa [src] using hA, by simpa [src] using fun h => hw3 h hBv,
        by simpa [src] using hBv, by simpa [src] using hB⟩
    · have hB : v ∉ supp n D (opB D j) := hw3 hA
      have hBu : u ∈ supp n D (opB D j) := (hmin _ hb hw1.2).resolve_right hB
      exact ⟨true, by simpa [src] using hBu, by simpa [src] using hB,
        by simpa [src] using hA, by simpa [src] using fun h => hw2 h hBu⟩

lemma H2.sem_inelig_consumer (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    {v : Fin n} (hv : v ∈ ineligSet n D) :
    ∃ e : ℕ × Bool, e.1 < D.length ∧ tag D e.1 = true ∧ supp n D (src D e) = {v} ∧
      supp n D (n + e.1) = ∅ ∧ (∀ a, G v a → a ∈ supp n D (src D (e.1, !e.2))) ∧
      exitArcs n D (carrierT n D {v}) = {e} ∧ merges n D (carrierT n D {v}) = ∅ := by
  have hS := h.1
  have hfl := carrier_flow_union h {v} (by rw [sem_supp_out hG hC]; simp)
  rw [sem_inelig_surplus hv, Finset.card_singleton] at hfl
  have hmeet : ∀ a, G v a → ∃ j s, j < D.length ∧ tag D j = true ∧
      (j, s) ∈ exitArcs n D (carrierT n D {v}) ∧ a ∈ supp n D (src D (j, !s)) := by
    intro a hva
    obtain ⟨j, hj, ht, -, hju, -, s, h1, -, h3, -⟩ := sem_joint_meeting hG hS hC hva
    exact ⟨j, s, hj, ht, sem_mem_exit1.mpr ⟨hj, h1, hju⟩, h3⟩
  obtain ⟨a0, ha0, -⟩ := hG.2.2.2 v v
  obtain ⟨j0, s0, hj0, ht0, hm0, -⟩ := hmeet a0 ha0
  have hcard : (exitArcs n D (carrierT n D {v})).card = 1 := by
    have := Finset.card_pos.mpr ⟨_, hm0⟩
    omega
  have hmer : merges n D (carrierT n D {v}) = ∅ := Finset.card_eq_zero.mp (by omega)
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp hcard
  rw [he, Finset.mem_singleton] at hm0
  subst hm0
  have hsrc : supp n D (src D (j0, s0)) = {v} :=
    sem_inelig_pure hG hS hC hv
      (sem_mem_exit1.mp (by rw [he]; exact Finset.mem_singleton_self _)).2.1
  have hnot : v ∉ supp n D (n + j0) :=
    (sem_mem_exit1.mp (by rw [he]; exact Finset.mem_singleton_self _)).2.2
  refine ⟨(j0, s0), hj0, ht0, hsrc, ?_, ?_, he, hmer⟩
  · refine Finset.eq_empty_of_forall_notMem (fun x hx => ?_)
    have hx2 := sem_supp_and_sub hS hj0 ht0 s0 hx
    rw [hsrc, Finset.mem_singleton] at hx2
    exact hnot (hx2 ▸ hx)
  · intro a hva
    obtain ⟨j, s, -, -, hm, ha⟩ := hmeet a hva
    rw [he, Finset.mem_singleton] at hm
    rw [Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact ha

lemma H2.sem_elig_cover (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    {u v : Fin n} (huv : G u v) : u ∈ eligSet n D ∨ v ∈ eligSet n D := by
  by_contra hc
  rw [not_or] at hc
  obtain ⟨eu, -, -, -, -, hnu, hxu, -⟩ := sem_inelig_consumer hG h hC (sem_mem_inelig.mpr hc.1)
  obtain ⟨ev, -, -, hsv, -, -, hxv, -⟩ := sem_inelig_consumer hG h hC (sem_mem_inelig.mpr hc.2)
  obtain ⟨j, hj, -, -, hju, hjv, s, h1, -, h3, -⟩ := sem_joint_meeting hG h.1 hC huv
  have m1 : (j, s) ∈ exitArcs n D (carrierT n D {u}) := sem_mem_exit1.mpr ⟨hj, h1, hju⟩
  have m2 : (j, !s) ∈ exitArcs n D (carrierT n D {v}) := sem_mem_exit1.mpr ⟨hj, h3, hjv⟩
  rw [hxu, Finset.mem_singleton] at m1
  rw [hxv, Finset.mem_singleton] at m2
  subst m1
  subst m2
  obtain ⟨a, hua, hav⟩ := hG.2.2.2 u v
  have h5 : a ∈ supp n D (src D (j, !s)) := hnu a hua
  rw [hsv, Finset.mem_singleton] at h5
  exact hav h5

lemma H2.sem_ind_no_edge {A : Finset (Fin n)} (hA : ∀ a ∈ A, ∀ b ∈ A, ¬ G a b) :
    ¬ sem_Edge G (sem_ind A) := by
  rintro ⟨a, c, hac, ha, hc⟩
  simp only [sem_ind, decide_eq_true_eq] at ha hc
  exact hA a ha c hc hac

lemma H2.sem_exposure (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    (A : Finset (Fin n)) (hA : ∀ a ∈ A, ∀ b ∈ A, ¬ G a b) (x : Fin n)
    (hnb : ∃ a ∈ A, G x a) :
    ∃ j s, j < D.length ∧ tag D j = true ∧ x ∈ supp n D (src D (j, s)) ∧
      x ∉ supp n D (n + j) ∧ Disjoint (supp n D (src D (j, s))) A := by
  by_contra hcon
  have hmask : ∀ j s, j < D.length → tag D j = true → x ∈ supp n D (src D (j, s)) →
      x ∉ supp n D (n + j) → val D (sem_ind A) (src D (j, s)) = true ∧
        val D (sem_ins x (sem_ind A)) (src D (j, s)) = true := by
    intro j s hj ht h1 h2
    have hnd : ¬ Disjoint (supp n D (src D (j, s))) A :=
      fun hd => hcon ⟨j, s, hj, ht, h1, h2, hd⟩
    rw [Finset.not_disjoint_iff] at hnd
    obtain ⟨a, ha1, ha2⟩ := hnd
    exact ⟨sem_val_of_supp hS ha1 (by simp [sem_ind, ha2]),
      sem_val_of_supp hS ha1 (by simp [sem_ins, sem_ind, ha2])⟩
  have key : ∀ w, x ∉ supp n D w → val D (sem_ind A) w = val D (sem_ins x (sem_ind A)) w := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      by_cases hn : w < n
      · rw [val_input D _ w hn, val_input D _ w hn]
        have hs : supp n D w = {⟨w, hn⟩} := supp_input D ⟨w, hn⟩
        rw [hs, Finset.mem_singleton] at hw
        exact sem_ins_agree x _ _ (fun hc => hw hc.symm)
      · by_cases hlt : w < n + D.length
        · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
          have hj : j < D.length := by omega
          obtain ⟨ha, hb, -⟩ := hS j hj
          rw [val_gate hS _ j hj, val_gate hS _ j hj]
          cases ht : tag D j
          · rw [sem_supp_or hS hj ht, Finset.mem_union, not_or] at hw
            rw [ih _ ha hw.1, ih _ hb hw.2]
          · have hw2 := hw
            rw [sem_supp_and hS hj ht, Finset.mem_inter, not_and] at hw2
            by_cases hxa : x ∈ supp n D (opA D j)
            · have h1 := hmask j false hj ht (by rw [sb_src_false]; exact hxa) hw
              rw [sb_src_false] at h1
              rw [ih _ hb (hw2 hxa), h1.1, h1.2]
            · by_cases hxb : x ∈ supp n D (opB D j)
              · have h1 := hmask j true hj ht (by rw [sb_src_true]; exact hxb) hw
                rw [sb_src_true] at h1
                rw [ih _ ha hxa, h1.1, h1.2]
              · rw [ih _ ha hxa, ih _ hb hxb]
        · rw [val_ge D _ w (by omega), val_ge D _ w (by omega)]
  have hout := key (outW n D) (by rw [sem_supp_out hG hC]; exact Finset.notMem_empty x)
  obtain ⟨a, ha, hxa⟩ := hnb
  have h2 : sem_Edge G (sem_ins x (sem_ind A)) :=
    ⟨x, a, hxa, sem_ins_self x _, by simp [sem_ins, sem_ind, ha]⟩
  have h3 := (hC _).mpr h2
  rw [← hout] at h3
  exact sem_ind_no_edge hA ((hC _).mp h3)

lemma H2.sem_first_mask (hS : Strict n D) (T M : Finset (Fin n)) (hM : 2 ≤ M.card) (w : ℕ)
    (hw : supp n D w ∩ T = M) :
    ∃ j, j < D.length ∧ n + j ≤ w ∧ supp n D (n + j) ∩ T = M ∧
      j ∈ merges n D (carrierT n D T) ∧ (∀ u, u < n + j → supp n D u ∩ T ≠ M) ∧
      ((tag D j = true ∧ M ⊂ supp n D (opA D j) ∩ T ∧ M ⊂ supp n D (opB D j) ∩ T) ∨
        (tag D j = false ∧ supp n D (opA D j) ∩ T ⊂ M ∧ supp n D (opB D j) ∩ T ⊂ M ∧
          (supp n D (opA D j) ∩ T) ∪ (supp n D (opB D j) ∩ T) = M ∧
          (supp n D (opA D j) ∩ T).Nonempty ∧ (supp n D (opB D j) ∩ T).Nonempty)) := by
  classical
  have hex : ∃ u, supp n D u ∩ T = M := ⟨w, hw⟩
  have hle : Nat.find hex ≤ w := Nat.find_min' hex hw
  have hmin : ∀ u, u < Nat.find hex → supp n D u ∩ T ≠ M := fun u hu => Nat.find_min hex hu
  have hspec := Nat.find_spec hex
  generalize Nat.find hex = f at hle hmin hspec
  have hMne : M.Nonempty := Finset.card_pos.mp (by omega)
  have hmem : ∀ {u : ℕ}, (supp n D u ∩ T).Nonempty → u ∈ carrierT n D T := by
    intro u hu
    obtain ⟨v, hv⟩ := hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      (sem_supp_lt (Finset.mem_inter.mp hv).1), v, hv⟩
  have hflt : f < n + D.length := by
    obtain ⟨v, hv⟩ := hMne
    rw [← hspec] at hv
    exact sem_supp_lt (Finset.mem_inter.mp hv).1
  have hfn : n ≤ f := by
    by_contra hc
    have hc' : f < n := by omega
    have hs : supp n D f = {⟨f, hc'⟩} := supp_input D ⟨f, hc'⟩
    have h1 : M.card ≤ 1 := by
      rw [← hspec, hs]
      exact (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
    omega
  obtain ⟨j, rfl⟩ : ∃ j, f = n + j := ⟨f - n, by omega⟩
  have hj : j < D.length := by omega
  obtain ⟨ha, hb, -⟩ := hS j hj
  have hna := hmin _ ha
  have hnb := hmin _ hb
  refine ⟨j, hj, hle, hspec, ?_, hmin, ?_⟩
  · have hAB : (supp n D (opA D j) ∩ T).Nonempty ∧ (supp n D (opB D j) ∩ T).Nonempty := by
      cases ht : tag D j
      · rw [sem_supp_or hS hj ht, Finset.union_inter_distrib_right] at hspec
        constructor
        · rw [Finset.nonempty_iff_ne_empty]
          intro he
          rw [he, Finset.empty_union] at hspec
          exact hnb hspec
        · rw [Finset.nonempty_iff_ne_empty]
          intro he
          rw [he, Finset.union_empty] at hspec
          exact hna hspec
      · rw [sem_supp_and hS hj ht] at hspec
        obtain ⟨v, hv⟩ := hMne
        rw [← hspec] at hv
        simp only [Finset.mem_inter] at hv
        exact ⟨⟨v, Finset.mem_inter.mpr ⟨hv.1.1, hv.2⟩⟩, ⟨v, Finset.mem_inter.mpr ⟨hv.1.2, hv.2⟩⟩⟩
    rw [merges, Finset.mem_filter, Finset.mem_range]
    exact ⟨hj, hmem (by rw [hspec]; exact hMne), hmem hAB.1, hmem hAB.2⟩
  · cases ht : tag D j
    · right
      rw [sem_supp_or hS hj ht, Finset.union_inter_distrib_right] at hspec
      have hsa : supp n D (opA D j) ∩ T ⊆ M := by rw [← hspec]; exact Finset.subset_union_left
      have hsb : supp n D (opB D j) ∩ T ⊆ M := by rw [← hspec]; exact Finset.subset_union_right
      refine ⟨rfl, Finset.ssubset_iff_subset_ne.mpr ⟨hsa, hna⟩,
        Finset.ssubset_iff_subset_ne.mpr ⟨hsb, hnb⟩, hspec, ?_, ?_⟩
      · rw [Finset.nonempty_iff_ne_empty]
        intro he
        rw [he, Finset.empty_union] at hspec
        exact hnb hspec
      · rw [Finset.nonempty_iff_ne_empty]
        intro he
        rw [he, Finset.union_empty] at hspec
        exact hna hspec
    · left
      rw [sem_supp_and hS hj ht] at hspec
      have hsa : M ⊆ supp n D (opA D j) ∩ T := by
        rw [← hspec]
        intro v hv
        simp only [Finset.mem_inter] at hv ⊢
        exact ⟨hv.1.1, hv.2⟩
      have hsb : M ⊆ supp n D (opB D j) ∩ T := by
        rw [← hspec]
        intro v hv
        simp only [Finset.mem_inter] at hv ⊢
        exact ⟨hv.1.2, hv.2⟩
      exact ⟨rfl, Finset.ssubset_iff_subset_ne.mpr ⟨hsa, Ne.symm hna⟩,
        Finset.ssubset_iff_subset_ne.mpr ⟨hsb, Ne.symm hnb⟩⟩

end SemCore


variable {n : ℕ} {D : Dag}

lemma H2.carrier_flow_lower (h : StrictLive n D) (K : Finset ℕ) (hK : K ⊆ inner n D)
    : (sources n K).card + surplusOn D K ≤
      (exitArcs n D K).card + (merges n D K).card := by
  obtain ⟨hS, hL, -⟩ := h
  have hKlt : ∀ w ∈ K, w + 1 < n + D.length := fun w hw => sb_mem_inner.mp (hK hw)
  have h1 : surplusOn D K + K.card = ((arcs D).filter (fun e => src D e ∈ K)).card := by
    rw [← sb_sum_fanout_eq hS, sb_surplus_add_card (fun w hw => hL w (hKlt w hw))]
  have h2 := Finset.card_filter_add_card_filter_not
    (s := (arcs D).filter (fun e => src D e ∈ K)) (fun e : ℕ × Bool => n + e.1 ∈ K)
  rw [Finset.filter_filter, Finset.filter_filter] at h2
  have h3 : ((arcs D).filter (fun e => src D e ∈ K ∧ n + e.1 ∈ K)).card ≤
      ((Finset.range D.length).filter (fun j => n + j ∈ K)).card + (merges n D K).card := by
    rw [sb_card_arcs_filter, merges, Finset.card_filter, Finset.card_filter,
      ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun j hj => ?_)
    rw [sb_src_false, sb_src_true]
    by_cases hj2 : n + j ∈ K <;> by_cases ha : opA D j ∈ K <;> by_cases hb : opB D j ∈ K <;>
      simp_all
  have h4 : K.card = (sources n K).card +
      ((Finset.range D.length).filter (fun j => n + j ∈ K)).card := by
    rw [← Finset.card_filter_add_card_filter_not (s := K) (fun w => w < n), sources]
    congr 1
    have himg : K.filter (fun w => ¬ w < n) =
        ((Finset.range D.length).filter (fun j => n + j ∈ K)).image (fun j => n + j) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨hw, hn⟩
        have := hKlt w hw
        exact ⟨w - n, ⟨by omega, by rwa [Nat.add_sub_cancel' (by omega)]⟩, by omega⟩
      · rintro ⟨j, ⟨-, hj⟩, rfl⟩
        exact ⟨hj, by omega⟩
    rw [himg, Finset.card_image_of_injective _ (add_right_injective n)]
  unfold exitArcs
  omega

def H2.copyBoundary (n : ℕ) (D : Dag) (K : Finset ℕ) : Finset ℕ :=
  (Finset.range D.length).filter (fun j =>
    (opA D j ∈ K ∧ opB D j ∈ K) ∨
    ((opA D j ∈ K ∨ opB D j ∈ K) ∧ n + j ∉ K))

lemma H2.source_surplus_le_copyBoundary (h : StrictLive n D) (K : Finset ℕ)
    (hK : K ⊆ inner n D)
    (hclosed : ∀ j < D.length, opA D j ∈ K → opB D j ∈ K → n + j ∈ K) :
    (sources n K).card + surplusOn D K ≤ (copyBoundary n D K).card := by
  have hp (a : ℕ × Bool) (ha : a ∈ exitArcs n D K) :
      a.1 < D.length ∧ src D a ∈ K ∧ n + a.1 ∉ K := by
    obtain ⟨ha, hs, ho⟩ := Finset.mem_filter.mp ha
    exact ⟨Finset.mem_range.mp (Finset.mem_product.mp ha).1, hs, ho⟩
  have hinj : Set.InjOn Prod.fst (↑(exitArcs n D K) : Set (ℕ × Bool)) := by
    rintro ⟨j,s⟩ ha ⟨k,t⟩ hb he
    change j = k at he
    subst k
    obtain ⟨hj, hsa, hoa⟩ := hp _ ha
    obtain ⟨_, hsb, _⟩ := hp _ hb
    cases s <;> cases t
    · rfl
    · exact (hoa (hclosed j hj (by simpa [src] using hsa) (by simpa [src] using hsb))).elim
    · exact (hoa (hclosed j hj (by simpa [src] using hsb) (by simpa [src] using hsa))).elim
    · rfl
  have hdis : Disjoint ((exitArcs n D K).image Prod.fst) (merges n D K) := by
    rw [Finset.disjoint_left]
    intro j he hm
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    exact (hp a ha).2.2 (Finset.mem_filter.mp hm).2.1
  have hsub : (exitArcs n D K).image Prod.fst ∪ merges n D K ⊆ copyBoundary n D K := by
    intro j hj
    rw [copyBoundary, Finset.mem_filter, Finset.mem_range]
    rcases Finset.mem_union.mp hj with he | hm
    · obtain ⟨⟨k,s⟩, hs, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hk, ha, ho⟩ := hp _ hs
      refine ⟨hk, Or.inr ⟨?_, ho⟩⟩
      cases s
      · exact Or.inl (by simpa [src] using ha)
      · exact Or.inr (by simpa [src] using ha)
    · obtain ⟨hj, _, ha, hb⟩ := Finset.mem_filter.mp hm
      exact ⟨Finset.mem_range.mp hj, Or.inl ⟨ha, hb⟩⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis, Finset.card_image_of_injOn hinj] at hc
  have hf := carrier_flow_lower h K hK
  omega

lemma H2.source_le_copyBoundary (h : StrictLive n D) (K : Finset ℕ)
    (hK : K ⊆ inner n D)
    (hclosed : ∀ j < D.length, opA D j ∈ K → opB D j ∈ K → n + j ∈ K) :
    (sources n K).card ≤ (copyBoundary n D K).card := by
  have hh := source_surplus_le_copyBoundary h K hK hclosed
  omega

noncomputable def H2.zeroWires {n : ℕ} {α : Type} (D : Dag)
    (rows : α → Fin n → Bool) : Finset ℕ := by
  classical
  exact (Finset.range (n + D.length)).filter (fun w => ∀ r, val D (rows r) w = false)

lemma H2.mem_zeroWires {n : ℕ} {α : Type} {D : Dag} {rows : α → Fin n → Bool} {w : ℕ} :
    w ∈ zeroWires D rows ↔ w < n + D.length ∧ ∀ r, val D (rows r) w = false := by
  classical
  simp [zeroWires]

lemma H2.true_support_on_rows {n : ℕ} {α : Type} {D : Dag}
    (hS : Strict n D) (rows : α → Fin n → Bool) {v : Fin n}
    (hv : ∀ r, rows r v = true) {w : ℕ} (hw : v ∈ supp n D w) :
    ∀ r, val D (rows r) w = true := by
  intro r
  apply val_mono hS (single v) (rows r) _ w (mem_supp.mp hw)
  intro u hu
  have huv : u = v := by simpa [single] using hu
  simpa only [huv] using hv r

section NeighborhoodPrerequisites

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

def H2.sem_W (n : ℕ) (D : Dag) (x : Fin n) : Finset (ℕ × Bool) := exitArcs n D (carrierT n D {x})

lemma H2.sem_mem_W {x : Fin n} {e : ℕ × Bool} : e ∈ sem_W n D x ↔
    e.1 < D.length ∧ x ∈ supp n D (src D e) ∧ x ∉ supp n D (n + e.1) := sem_mem_exit1

lemma H2.sem_W_and (hS : Strict n D) {x : Fin n} {e : ℕ × Bool} (he : e ∈ sem_W n D x) :
    tag D e.1 = true := by
  obtain ⟨hj, h1, h2⟩ := sem_mem_W.mp he
  by_contra ht
  rw [Bool.not_eq_true] at ht
  apply h2
  rw [sem_supp_or hS hj ht, Finset.mem_union]
  obtain ⟨j, s⟩ := e
  cases s
  · left; simpa [src] using h1
  · right; simpa [src] using h1

def H2.k4_Pos (n : ℕ) (G : Fin n → Fin n → Prop) (D : Dag) (pos : Fin n → ℕ × Bool) : Prop :=
  (∀ i ∈ ineligSet n D, (pos i).1 < D.length ∧ supp n D (n + (pos i).1) = ∅ ∧
    (∀ a, G i a → a ∈ supp n D (src D (pos i))) ∧
    supp n D (src D ((pos i).1, !(pos i).2)) = {i}) ∧
  ∀ i ∈ ineligSet n D, ∀ i' ∈ ineligSet n D, pos i = pos i' → i = i'

lemma H2.k4_assigned (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D) :
    ∃ pos : Fin n → ℕ × Bool, k4_Pos n G D pos := by
  classical
  have hex : ∀ i : Fin n, ∃ e : ℕ × Bool, i ∈ ineligSet n D → (e.1 < D.length ∧
      supp n D (n + e.1) = ∅ ∧ (∀ a, G i a → a ∈ supp n D (src D e)) ∧
      supp n D (src D (e.1, !e.2)) = {i}) := by
    intro i
    by_cases hi : i ∈ ineligSet n D
    · obtain ⟨e, h1, -, h3, h4, h5, -, -⟩ := sem_inelig_consumer hG h hC hi
      exact ⟨(e.1, !e.2), fun _ => ⟨h1, h4, h5, by simpa using h3⟩⟩
    · exact ⟨(0, false), fun hc => absurd hc hi⟩
  choose pos hpos using hex
  refine ⟨pos, hpos, fun i hi i' hi' he => ?_⟩
  have h1 := (hpos i hi).2.2.2
  rw [he, (hpos i' hi').2.2.2] at h1
  exact (Finset.singleton_injective h1).symm

abbrev H2.V := Fin 10

def H2.neighbors (v : V) : Nat :=
  [50, 69, 138, 276, 521, 385, 770, 548, 104, 208].getD v.val 0

abbrev H2.adj (u v : V) : Prop := (neighbors u).testBit v.val = true

lemma H2.graph_ok : sem_Gr adj := by
  unfold sem_Gr
  decide +kernel

end NeighborhoodPrerequisites

noncomputable def H2.centerGates {n : ℕ} (D : Dag) (z : Fin n) : Finset ℕ := by
  classical
  exact (Finset.range D.length).filter (fun j => z ∈ supp n D (n + j))

def H2.neighborhoodResidualRows (x : Fin 6 → Bool) (v : Fin 10) : Bool :=
  match v.val with
  | 0 => true
  | 2 => x 0
  | 8 => x 1
  | 9 => x 2
  | 3 => x 3
  | 7 => x 4
  | 6 => x 5
  | _ => false

def H2.residualC6 (x : Fin 6 → Bool) : Bool :=
  x 0 && x 3 || x 0 && x 4 || x 1 && x 3 || x 1 && x 5 ||
    x 2 && x 4 || x 2 && x 5

def H2.neighborhoodI : Finset (Fin 10) := {1, 4, 5}

lemma H2.neighborhood_rows_false (x : Fin 6 → Bool) :
    ∀ i ∈ neighborhoodI, neighborhoodResidualRows x i = false := by
  intro i hi
  simp only [neighborhoodI, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl <;> rfl

lemma H2.neighborhood_rows_top (v : Fin 10) :
    neighborhoodResidualRows (fun _ => true) v = false ↔ v ∈ neighborhoodI := by
  fin_cases v <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma H2.neighborhood_residual_edges : ∀ x : Fin 6 → Bool,
    sem_Edge adj (neighborhoodResidualRows x) ↔ residualC6 x = true := by
  unfold sem_Edge
  decide +kernel

lemma H2.neighborhood_residual_correct {D : Dag} (hc : sem_Comp 10 adj D)
    (x : Fin 6 → Bool) :
    val D (neighborhoodResidualRows x) (outW 10 D) = residualC6 x := by
  apply Bool.eq_iff_iff.mpr
  exact (hc _).trans (neighborhood_residual_edges x)

lemma H2.zero_wire_support_subset {n : ℕ} {α : Type} {D : Dag}
    (hS : Strict n D) (rows : α → Fin n → Bool)
    (I : Finset (Fin n)) (r : α) (hr : ∀ v, v ∉ I → rows r v = true)
    {w : ℕ} (hw : w ∈ zeroWires D rows) : supp n D w ⊆ I := by
  intro v hv
  by_contra hvi
  have hvtrue := hr v hvi
  have hwtrue : val D (rows r) w = true := by
    apply val_mono hS (single v) (rows r) _ w (mem_supp.mp hv)
    intro u hu
    have huv : u = v := by simpa [single] using hu
    simpa only [huv] using hvtrue
  have hwfalse := (mem_zeroWires.mp hw).2 r
  rw [hwtrue] at hwfalse
  contradiction

lemma H2.earlier_wire_not_first_support {n : ℕ} {D : Dag} {j : ℕ}
    {S : Finset (Fin n)} (hcard : 2 ≤ S.card)
    (hfirst : ∀ k < j, supp n D (n + k) ≠ S) :
    ∀ w < n + j, supp n D w ≠ S := by
  intro w hw heq
  by_cases hn : w < n
  · have hc : S.card = 1 := by
      rw [← heq]
      change (supp n D (⟨w, hn⟩ : Fin n).val).card = 1
      rw [supp_input]
      simp
    omega
  · have hh := hfirst (w - n) (by omega)
    apply hh
    simpa only [Nat.add_sub_of_le (Nat.le_of_not_gt hn)] using heq

lemma H2.first_support_gate_no_zero_input {n : ℕ} {α : Type} {D : Dag}
    (hS : Strict n D) (rows : α → Fin n → Bool)
    (I : Finset (Fin n)) (r : α) (hr : ∀ v, v ∉ I → rows r v = true)
    {j : ℕ} (hj : j < D.length) {S : Finset (Fin n)}
    (hcard : 2 ≤ S.card) (hdis : Disjoint S I)
    (hs : supp n D (n + j) = S)
    (hfirst : ∀ k < j, supp n D (n + k) ≠ S) :
    opA D j ∉ zeroWires D rows ∧ opB D j ∉ zeroWires D rows := by
  have hearly := earlier_wire_not_first_support hcard hfirst
  obtain ⟨ha, hb, _⟩ := hS j hj
  have hnotzero : n + j ∉ zeroWires D rows := by
    intro hz
    have hsub := zero_wire_support_subset hS rows I r hr hz
    rw [hs] at hsub
    have hempty : S = ∅ := by
      ext v
      simp only [Finset.notMem_empty, iff_false]
      intro hv
      exact Finset.disjoint_left.mp hdis hv (hsub hv)
    simp [hempty] at hcard
  have hg := supp_gate hS j hj
  rw [hs] at hg
  have hor_empty : tag D j = false →
      ∀ w, w ∈ zeroWires D rows → supp n D w ⊆ S → supp n D w = ∅ := by
    intro _ w hw hwS
    have hwI := zero_wire_support_subset hS rows I r hr hw
    ext v
    simp only [Finset.notMem_empty, iff_false]
    intro hv
    exact Finset.disjoint_left.mp hdis (hwS hv) (hwI hv)
  cases hop : tag D j with
  | true =>
      constructor <;> intro hz <;> apply hnotzero
      · refine mem_zeroWires.mpr ⟨by omega, ?_⟩
        intro t
        rw [val_gate hS _ j hj, hop, gop_true, (mem_zeroWires.mp hz).2 t]
        rfl
      · refine mem_zeroWires.mpr ⟨by omega, ?_⟩
        intro t
        rw [val_gate hS _ j hj, hop, gop_true, (mem_zeroWires.mp hz).2 t]
        simp
  | false =>
      simp only [hop, Bool.false_eq_true, ↓reduceIte] at hg
      constructor
      · intro hz
        have hsub : supp n D (opA D j) ⊆ S := by rw [hg]; exact Finset.subset_union_left
        have he := hor_empty hop _ hz hsub
        have hbS : supp n D (opB D j) = S := by simpa [he] using hg.symm
        exact hearly _ hb hbS
      · intro hz
        have hsub : supp n D (opB D j) ⊆ S := by rw [hg]; exact Finset.subset_union_right
        have he := hor_empty hop _ hz hsub
        have haS : supp n D (opA D j) = S := by simpa [he] using hg.symm
        exact hearly _ ha haS

lemma H2.first_support_gate_not_copyBoundary {n : ℕ} {α : Type} {D : Dag}
    (hS : Strict n D) (rows : α → Fin n → Bool)
    (I : Finset (Fin n)) (r : α) (hr : ∀ v, v ∉ I → rows r v = true)
    {j : ℕ} (hj : j < D.length) {S : Finset (Fin n)}
    (hcard : 2 ≤ S.card) (hdis : Disjoint S I)
    (hs : supp n D (n + j) = S)
    (hfirst : ∀ k < j, supp n D (n + k) ≠ S) :
    j ∉ copyBoundary n D (zeroWires D rows) := by
  obtain ⟨ha, hb⟩ := first_support_gate_no_zero_input hS rows I r hr hj hcard hdis hs hfirst
  intro hjb
  have hcase := (Finset.mem_filter.mp hjb).2
  rcases hcase with ⟨hza, _⟩ | ⟨hza | hzb, _⟩
  · exact ha hza
  · exact ha hza
  · exact hb hzb


-- Pure OR normalization helpers, adapted from L_meta_4295.
open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves PEqualNP.TopForm
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.CircuitMoves

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
  PEqualNP.CircuitMoves

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
  PEqualNP.CircuitMoves

open PEqualNP.CircuitLowerBounds

lemma H2.val_constant (n : ℕ) (D : Dag) (hS : Strict n D) (b : Bool) :
    ∀ w, w < n + D.length → val D (fun _ : Fin n => b) w = b := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
      intro hw
      by_cases hn : w < n
      · rw [val_input D _ w hn]
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < D.length := by omega
        obtain ⟨ha, hb, _⟩ := hS j hj
        rw [val_gate hS _ j hj, ih _ ha (by omega), ih _ hb (by omega)]
        cases b <;> cases tag D j <;> rfl

lemma H2.ref_eq_false_of_top_false {n : ℕ} {D : Dag} (hS : Strict n D)
    (r : Ref) (hr : na_ok (n + D.length) r)
    (hv : refVal (wl D (List.ofFn (fun _ : Fin n => true))) r = false) :
    r = Sum.inl false := by
  rcases r with b | w
  · change b = false at hv
    exact congrArg Sum.inl hv
  · change val D (fun _ : Fin n => true) w = false at hv
    rw [val_constant n D hS true w hr] at hv
    contradiction

lemma H2.ref_eq_true_of_bottom_true {n : ℕ} {D : Dag} (hS : Strict n D)
    (r : Ref) (hr : na_ok (n + D.length) r)
    (hv : refVal (wl D (List.ofFn (fun _ : Fin n => false))) r = true) :
    r = Sum.inl true := by
  rcases r with b | w
  · change b = true at hv
    exact congrArg Sum.inl hv
  · change val D (fun _ : Fin n => false) w = true at hv
    rw [val_constant n D hS false w hr] at hv
    contradiction

lemma H2.na_step_no_emit_of_constant_operand (n : ℕ) (st : List Ref × Dag)
    (g : Gate) (a b : ℕ) (hinputs : g.inputs = [a, b])
    (hc : (∃ c, na_look st.1 a = Sum.inl c) ∨
      ∃ c, na_look st.1 b = Sum.inl c) :
    (na_step n st g).2 = st.2 := by
  rcases hc with ⟨c, hc⟩ | ⟨c, hc⟩
  · simp [na_step, hinputs, hc, na_comb]
  · cases ha : na_look st.1 a <;> simp [na_step, hinputs, ha, hc, na_comb]

lemma H2.na_step_new_ref_ok (n : ℕ) (st : List Ref × Dag) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hgood : na_Good n st) :
    na_ok (n + (na_step n st g).2.length)
      (na_look (na_step n st g).1 st.1.length) := by
  have hnew := (na_step_spec n st g hg hgood).1
  exact na_look_ok _ _ hnew.2 _

lemma H2.na_step_no_emit_of_constant_new_ref (n : ℕ) (st : List Ref × Dag)
    (g : Gate) (c : Bool)
    (hc : na_look (na_step n st g).1 st.1.length = Sum.inl c) :
    (na_step n st g).2 = st.2 := by
  rcases hi : g.inputs with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · simp [na_step, hi]
  · simp [na_step, hi]
  · cases hcomb : na_comb (na_isAnd g.op) (na_look st.1 a) (na_look st.1 b) with
    | inl r => simp [na_step, hi, hcomb]
    | inr p =>
        simp only [na_step, hi, hcomb] at hc
        simp [na_look, List.getD_eq_getElem?_getD] at hc

lemma H2.na_step_no_emit_of_bottom_true (n : ℕ) (st : List Ref × Dag) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hgood : na_Good n st)
    (hv : refVal (wl (na_step n st g).2 (List.ofFn (fun _ : Fin n => false)))
      (na_look (na_step n st g).1 st.1.length) = true) :
    (na_step n st g).2 = st.2 := by
  apply na_step_no_emit_of_constant_new_ref n st g true
  exact ref_eq_true_of_bottom_true (na_step_spec n st g hg hgood).1.1 _
    (na_step_new_ref_ok n st g hg hgood) hv

open PEqualNP.CircuitLowerBounds

def H2.gateOf (g : Bool × ℕ × ℕ) : Gate :=
  ⟨if g.1 then GateOp.and else GateOp.or, [g.2.1, g.2.2]⟩

lemma H2.gateOf_ok (g : Bool × ℕ × ℕ) :
    (gateOf g).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
      (gateOf g).inputs.length ≤ 2 := by
  cases h : g.1 <;> simp [gateOf, h]

lemma H2.gateOf_eval (g : Bool × ℕ × ℕ) (w : List Bool) :
    (gateOf g).op.eval ((gateOf g).inputs.map fun i => w.getD i false) =
      gop g.1 (w.getD g.2.1 false) (w.getD g.2.2 false) := by
  cases h : g.1 <;> simp [gateOf, h, GateOp.eval, gop]

def H2.stage (n : ℕ) (m : List Ref) (D : Dag) : ℕ → List Ref × Dag
  | 0 => (m, [])
  | k + 1 => na_step n (stage n m D k) (gateOf (D.getD k (false, 0, 0)))

def H2.emitted (n : ℕ) (m : List Ref) (D : Dag) (k : ℕ) : Finset ℕ :=
  (Finset.range k).filter fun j =>
    (stage n m D j).2.length < (stage n m D (j + 1)).2.length

lemma H2.step_shape (n : ℕ) (st : List Ref × Dag) (g : Bool × ℕ × ℕ) :
    (∃ r, na_step n st (gateOf g) = (st.1 ++ [r], st.2)) ∨
    (∃ h, na_step n st (gateOf g) =
      (st.1 ++ [Sum.inr (n + st.2.length)], st.2 ++ [h])) := by
  cases hc : na_comb (na_isAnd (gateOf g).op)
      (na_look st.1 g.2.1) (na_look st.1 g.2.2) with
  | inl r =>
    dsimp only [gateOf] at hc
    exact Or.inl ⟨r, by simp only [na_step, gateOf, hc]⟩
  | inr p =>
    dsimp only [gateOf] at hc
    exact Or.inr ⟨(na_isAnd (gateOf g).op, p.1, p.2),
      by simp only [na_step, gateOf, hc]⟩

lemma H2.stage_good (n : ℕ) (m : List Ref) (D : Dag)
    (hm : ∀ r ∈ m, na_ok n r) (k : ℕ) : na_Good n (stage n m D k) := by
  induction k with
  | zero => exact ⟨by simp [Strict, stage], by simpa [stage] using hm⟩
  | succ k ih => exact (na_step_spec n _ _ (gateOf_ok _) ih).1

lemma H2.stage_map_length (n : ℕ) (m : List Ref) (D : Dag) (k : ℕ) :
    (stage n m D k).1.length = m.length + k := by
  induction k with
  | zero => simp [stage]
  | succ k ih =>
    rcases step_shape n (stage n m D k) (D.getD k (false, 0, 0)) with
      ⟨r, hr⟩ | ⟨g, hg⟩
    · simp only [stage, hr, List.length_append, List.length_singleton, ih, Nat.add_assoc]
    · simp only [stage, hg, List.length_append, List.length_singleton, ih, Nat.add_assoc]

lemma H2.stage_step_length (n : ℕ) (m : List Ref) (D : Dag) (k : ℕ) :
    (stage n m D (k + 1)).2.length = (stage n m D k).2.length ∨
    (stage n m D (k + 1)).2.length = (stage n m D k).2.length + 1 := by
  rcases step_shape n (stage n m D k) (D.getD k (false, 0, 0)) with
    ⟨r, hr⟩ | ⟨g, hg⟩
  · exact Or.inl (by simp only [stage, hr])
  · exact Or.inr (by simp only [stage, hg, List.length_append, List.length_singleton])

lemma H2.emitted_mem (n : ℕ) (m : List Ref) (D : Dag) (k j : ℕ) :
    j ∈ emitted n m D k ↔ j < k ∧
      (stage n m D j).2.length < (stage n m D (j + 1)).2.length := by
  simp [emitted]

lemma H2.emitted_card (n : ℕ) (m : List Ref) (D : Dag) (k : ℕ) :
    (emitted n m D k).card = (stage n m D k).2.length := by
  induction k with
  | zero => simp [emitted, stage]
  | succ k ih =>
    have hn : k ∉ emitted n m D k := by simp [emitted]
    have hh := stage_step_length n m D k
    rcases hh with h | h
    · have he : emitted n m D (k + 1) = emitted n m D k := by
        ext j
        simp only [emitted_mem]
        constructor
        · rintro ⟨hj, hp⟩
          have hne : j ≠ k := by intro e; subst j; omega
          exact ⟨by omega, hp⟩
        · rintro ⟨hj, hp⟩; exact ⟨by omega, hp⟩
      rw [he, ih, h]
    · have he : emitted n m D (k + 1) = insert k (emitted n m D k) := by
        ext j
        simp only [emitted_mem, Finset.mem_insert]
        constructor
        · rintro ⟨hj, hp⟩
          by_cases e : j = k
          · exact Or.inl e
          · exact Or.inr ⟨by omega, hp⟩
        · rintro (rfl | ⟨hj, hp⟩)
          · exact ⟨by omega, by omega⟩
          · exact ⟨by omega, hp⟩
      rw [he, Finset.card_insert_of_notMem hn, ih, h]

lemma H2.stage_prefix (n : ℕ) (m : List Ref) (D : Dag) {j k : ℕ} (h : j ≤ k) :
    (stage n m D j).2 <+: (stage n m D k).2 := by
  induction k, h using Nat.le_induction with
  | base => exact ⟨[], by simp⟩
  | succ k hj ih =>
    apply ih.trans
    rcases step_shape n (stage n m D k) (D.getD k (false, 0, 0)) with
      ⟨r, hr⟩ | ⟨g, hg⟩
    · simp only [stage, hr]; exact ⟨[], by simp⟩
    · simp only [stage, hg]; exact List.prefix_append _ _

lemma H2.stage_ref_prefix (n : ℕ) (m : List Ref) (D : Dag) {j k : ℕ} (h : j ≤ k) :
    (stage n m D j).1 <+: (stage n m D k).1 := by
  induction k, h using Nat.le_induction with
  | base => exact ⟨[], by simp⟩
  | succ k hj ih =>
    apply ih.trans
    rcases step_shape n (stage n m D k) (D.getD k (false, 0, 0)) with
      ⟨r, hr⟩ | ⟨g, hg⟩
    · simp only [stage, hr]; exact List.prefix_append _ _
    · simp only [stage, hg]; exact List.prefix_append _ _

lemma H2.stage_sem (n : ℕ) (m : List Ref) (D : Dag)
    (hm : ∀ r ∈ m, na_ok n r) (x : Fin n → Bool) (w : List Bool)
    (hin : m.map (refVal (List.ofFn x)) = w) (k : ℕ) (hk : k ≤ D.length) :
    (stage n m D k).1.map (refVal (wl (stage n m D k).2 (List.ofFn x))) =
      wl (D.take k) w := by
  induction k with
  | zero => simpa [stage, wl] using hin
  | succ k ih =>
    have hlt : k < D.length := by omega
    have hi := ih (by omega)
    have hs := (na_step_spec n (stage n m D k) (gateOf (D.getD k (false, 0, 0)))
      (gateOf_ok _) (stage_good n m D hm k)).2.2 x _ hi
    change (na_step n (stage n m D k) (gateOf (D.getD k (false, 0, 0)))).1.map
      (refVal (wl (na_step n (stage n m D k) (gateOf (D.getD k (false, 0, 0)))).2
        (List.ofFn x))) = _
    rw [hs, List.take_succ_eq_append_getElem hlt, wl_append]
    rw [gateOf_eval]
    have he : D.getD k (false, 0, 0) = D[k] := by
      simp [List.getD_eq_getElem?_getD, hlt]
    rw [he]
    rfl

lemma H2.stage_wire_sem {n N : ℕ} (m : List Ref) (D : Dag)
    (hm : ∀ r ∈ m, na_ok n r) (x : Fin n → Bool) (y : Fin N → Bool)
    (hin : m.map (refVal (List.ofFn x)) = List.ofFn y)
    (k w : ℕ) (hk : k ≤ D.length) (hw : w < N + k) :
    refVal (wl (stage n m D k).2 (List.ofFn x))
      (na_look (stage n m D k).1 w) = val D y w := by
  rw [na_look_val, stage_sem n m D hm x _ hin k hk]
  exact val_take D y k w hw hk

lemma H2.prefix_look {a b : List Ref} (h : a <+: b) (i : ℕ) (hi : i < a.length) :
    na_look b i = na_look a i := by
  obtain ⟨c, rfl⟩ := h
  exact List.getD_append a c _ i hi

lemma H2.emitted_ref (n : ℕ) (m : List Ref) (D : Dag) {j k : ℕ}
    (hj : j ∈ emitted n m D k) :
    na_look (stage n m D k).1 (m.length + j) =
      Sum.inr (n + (stage n m D j).2.length) := by
  obtain ⟨hjk, hinc⟩ := (emitted_mem n m D k j).mp hj
  rw [prefix_look (stage_ref_prefix n m D (show j + 1 ≤ k by omega))
    (m.length + j) (by rw [stage_map_length]; omega)]
  rcases step_shape n (stage n m D j) (D.getD j (false, 0, 0)) with
    ⟨r, hr⟩ | ⟨g, hg⟩
  · simp only [stage, hr] at hinc
    omega
  · simp only [stage, hg]
    rw [← stage_map_length n m D j]
    simp [na_look, List.getD_eq_getElem?_getD]

lemma H2.emitted_rank_lt (n : ℕ) (m : List Ref) (D : Dag) {j k : ℕ}
    (hj : j ∈ emitted n m D k) :
    (stage n m D j).2.length < (stage n m D k).2.length := by
  obtain ⟨hjk, hinc⟩ := (emitted_mem n m D k j).mp hj
  have hp := (stage_prefix n m D (show j + 1 ≤ k by omega)).length_le
  omega

lemma H2.emitted_rank_strict (n : ℕ) (m : List Ref) (D : Dag) {i j k : ℕ}
    (hi : i ∈ emitted n m D k) (hij : i < j) :
    (stage n m D i).2.length < (stage n m D j).2.length := by
  obtain ⟨_, hinc⟩ := (emitted_mem n m D k i).mp hi
  have hp := (stage_prefix n m D (show i + 1 ≤ j by omega)).length_le
  omega

lemma H2.emitted_rank_inj (n : ℕ) (m : List Ref) (D : Dag) (k : ℕ) :
    Set.InjOn (fun j => (stage n m D j).2.length) (emitted n m D k) := by
  intro i hi j hj he
  dsimp only at he
  rcases lt_trichotomy i j with hij | rfl | hji
  · have hh := emitted_rank_strict n m D hi hij
    omega
  · rfl
  · have hh := emitted_rank_strict n m D hj hji
    omega

lemma H2.emitted_ranks (n : ℕ) (m : List Ref) (D : Dag) (k : ℕ) :
    (emitted n m D k).image (fun j => (stage n m D j).2.length) =
      Finset.range (stage n m D k).2.length := by
  apply Finset.eq_of_subset_of_card_le
  · intro r hr
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hr
    exact Finset.mem_range.mpr (emitted_rank_lt n m D hj)
  · rw [Finset.card_range, Finset.card_image_of_injOn (emitted_rank_inj n m D k),
      emitted_card]

lemma H2.emitted_wire_sem {n N : ℕ} (m : List Ref) (D : Dag)
    (hm : ∀ r ∈ m, na_ok n r) (hmN : m.length = N)
    (x : Fin n → Bool) (y : Fin N → Bool)
    (hin : m.map (refVal (List.ofFn x)) = List.ofFn y)
    {j k : ℕ} (hk : k ≤ D.length) (hj : j ∈ emitted n m D k) :
    val (stage n m D k).2 x (n + (stage n m D j).2.length) = val D y (N + j) := by
  have hsem := stage_wire_sem m D hm x y hin k (N + j) hk
    (by have := ((emitted_mem n m D k j).mp hj).1; omega)
  have href := emitted_ref n m D hj
  rw [hmN] at href
  rw [href] at hsem
  exact hsem

lemma H2.stage_noemit_iff (n : ℕ) (m : List Ref) (D : Dag) {j k : ℕ} (hj : j < k) :
    j ∉ emitted n m D k ↔ (stage n m D (j + 1)).2 = (stage n m D j).2 := by
  rw [emitted_mem]
  rcases step_shape n (stage n m D j) (D.getD j (false, 0, 0)) with
    ⟨r, hr⟩ | ⟨g, hg⟩
  · simp only [stage, hr, lt_self_iff_false, and_false, not_false_eq_true]
  · simp only [stage, hg, List.length_append, List.length_singleton] at *
    constructor
    · intro h
      exact False.elim (h ⟨hj, by omega⟩)
    · intro he h
      have hh := congrArg List.length he
      simp only [List.length_append, List.length_singleton] at hh
      omega

def H2.keptEmitted (n : ℕ) (m : List Ref) (D : Dag) (k q : ℕ) : Finset ℕ :=
  (emitted n m D k).filter fun j => (stage n m D j).2.length < q

lemma H2.keptEmitted_ranks (n : ℕ) (m : List Ref) (D : Dag) (k q : ℕ)
    (hq : q ≤ (stage n m D k).2.length) :
    (keptEmitted n m D k q).image (fun j => (stage n m D j).2.length) =
      Finset.range q := by
  ext r
  constructor
  · intro hr
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hr
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
  · intro hr
    have hrq := Finset.mem_range.mp hr
    have hrR : r ∈ Finset.range (stage n m D k).2.length := Finset.mem_range.mpr (by omega)
    rw [← emitted_ranks n m D k] at hrR
    obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hrR
    exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, by omega⟩, he⟩

lemma H2.keptEmitted_card (n : ℕ) (m : List Ref) (D : Dag) (k q : ℕ)
    (hq : q ≤ (stage n m D k).2.length) : (keptEmitted n m D k q).card = q := by
  have hi : Set.InjOn (fun j => (stage n m D j).2.length) (keptEmitted n m D k q) := by
    intro i hi j hj he
    exact emitted_rank_inj n m D k (Finset.mem_filter.mp hi).1
      (Finset.mem_filter.mp hj).1 he
  have hc := congrArg Finset.card (keptEmitted_ranks n m D k q hq)
  simpa only [Finset.card_image_of_injOn hi, Finset.card_range] using hc

lemma H2.keptEmitted_wire_sem {n N : ℕ} (m : List Ref) (D : Dag)
    (hm : ∀ r ∈ m, na_ok n r) (hmN : m.length = N)
    (x : Fin n → Bool) (y : Fin N → Bool)
    (hin : m.map (refVal (List.ofFn x)) = List.ofFn y)
    {j k q : ℕ} (hk : k ≤ D.length) (hq : q ≤ (stage n m D k).2.length)
    (hj : j ∈ keptEmitted n m D k q) :
    val ((stage n m D k).2.take q) x (n + (stage n m D j).2.length) =
      val D y (N + j) := by
  obtain ⟨hje, hjq⟩ := Finset.mem_filter.mp hj
  rw [val_take _ x q _ (by omega) hq]
  exact emitted_wire_sem m D hm hmN x y hin hk hje

def H2.n0Refs : List Ref :=
  [Sum.inl true, Sum.inl false, Sum.inr 0, Sum.inr 3, Sum.inl false,
    Sum.inl false, Sum.inr 5, Sum.inr 4, Sum.inr 1, Sum.inr 2]

def H2.restrictN0 (x : Fin 6 → Bool) : Fin 10 → Bool :=
  ![true, false, x 0, x 3, false, false, x 5, x 4, x 1, x 2]

lemma H2.n0Refs_good : ∀ r ∈ n0Refs, na_ok 6 r := by
  simp [n0Refs, na_ok]

lemma H2.n0Refs_length : n0Refs.length = 10 := rfl

lemma H2.n0Refs_sem (x : Fin 6 → Bool) :
    n0Refs.map (refVal (List.ofFn x)) = List.ofFn (restrictN0 x) := by
  simp [n0Refs, restrictN0, refVal, List.getD_eq_getElem?_getD, List.ofFn_succ]

lemma H2.stage_noemit_of_output_bottom_true {n N : ℕ} (m : List Ref) (D : Dag)
    (hm : ∀ r ∈ m, na_ok n r) (hmN : m.length = N) (y : Fin N → Bool)
    (hin : m.map (refVal (List.ofFn (fun _ : Fin n => false))) = List.ofFn y)
    (j : ℕ) (hj : j < D.length) (hv : val D y (N + j) = true) :
    (stage n m D (j + 1)).2 = (stage n m D j).2 := by
  apply na_step_no_emit_of_bottom_true n (stage n m D j)
    (gateOf (D.getD j (false, 0, 0))) (gateOf_ok _) (stage_good n m D hm j)
  change refVal (wl (stage n m D (j + 1)).2 (List.ofFn (fun _ : Fin n => false)))
    (na_look (stage n m D (j + 1)).1 (stage n m D j).1.length) = true
  rw [stage_map_length, hmN,
    stage_wire_sem m D hm _ y hin (j + 1) (N + j) (by omega) (by omega), hv]

lemma H2.stage_ref_false_of_top_false {n N : ℕ} (m : List Ref) (D : Dag)
    (hm : ∀ r ∈ m, na_ok n r) (y : Fin N → Bool)
    (hin : m.map (refVal (List.ofFn (fun _ : Fin n => true))) = List.ofFn y)
    (k w : ℕ) (hk : k ≤ D.length) (hw : w < N + k) (hv : val D y w = false) :
    na_look (stage n m D k).1 w = Sum.inl false := by
  have hg := stage_good n m D hm k
  apply ref_eq_false_of_top_false hg.1 _ (na_look_ok _ _ hg.2 _)
  rw [stage_wire_sem m D hm _ y hin k w hk hw, hv]

lemma H2.stage_ref_true_of_bottom_true {n N : ℕ} (m : List Ref) (D : Dag)
    (hm : ∀ r ∈ m, na_ok n r) (y : Fin N → Bool)
    (hin : m.map (refVal (List.ofFn (fun _ : Fin n => false))) = List.ofFn y)
    (k w : ℕ) (hk : k ≤ D.length) (hw : w < N + k) (hv : val D y w = true) :
    na_look (stage n m D k).1 w = Sum.inl true := by
  have hg := stage_good n m D hm k
  apply ref_eq_true_of_bottom_true hg.1 _ (na_look_ok _ _ hg.2 _)
  rw [stage_wire_sem m D hm _ y hin k w hk hw, hv]

lemma H2.stage_noemit_of_constant_operand {n : ℕ} (m : List Ref) (D : Dag) (j : ℕ)
    (hc : (∃ c, na_look (stage n m D j).1 (opA D j) = Sum.inl c) ∨
      ∃ c, na_look (stage n m D j).1 (opB D j) = Sum.inl c) :
    (stage n m D (j + 1)).2 = (stage n m D j).2 := by
  exact na_step_no_emit_of_constant_operand n (stage n m D j)
    (gateOf (D.getD j (false, 0, 0))) (opA D j) (opB D j) rfl hc

lemma H2.n0_noemit_of_output_bottom_true (D : Dag) (j : ℕ) (hj : j < D.length)
    (hv : val D (restrictN0 (fun _ => false)) (10 + j) = true) :
    (stage 6 n0Refs D (j + 1)).2 = (stage 6 n0Refs D j).2 :=
  stage_noemit_of_output_bottom_true n0Refs D n0Refs_good n0Refs_length _ (n0Refs_sem _)
    j hj hv

lemma H2.n0_noemit_of_constant_operand (D : Dag) (hS : Strict 10 D)
    (j : ℕ) (hj : j < D.length)
    (hc : (val D (restrictN0 (fun _ => true)) (opA D j) = false ∨
        val D (restrictN0 (fun _ => false)) (opA D j) = true) ∨
      (val D (restrictN0 (fun _ => true)) (opB D j) = false ∨
        val D (restrictN0 (fun _ => false)) (opB D j) = true)) :
    (stage 6 n0Refs D (j + 1)).2 = (stage 6 n0Refs D j).2 := by
  obtain ⟨ha, hb, _⟩ := hS j hj
  apply stage_noemit_of_constant_operand
  rcases hc with (ha0 | ha1) | (hb0 | hb1)
  · exact Or.inl ⟨false, stage_ref_false_of_top_false n0Refs D n0Refs_good _
      (n0Refs_sem _) j _ hj.le ha ha0⟩
  · exact Or.inl ⟨true, stage_ref_true_of_bottom_true n0Refs D n0Refs_good _
      (n0Refs_sem _) j _ hj.le ha ha1⟩
  · exact Or.inr ⟨false, stage_ref_false_of_top_false n0Refs D n0Refs_good _
      (n0Refs_sem _) j _ hj.le hb hb0⟩
  · exact Or.inr ⟨true, stage_ref_true_of_bottom_true n0Refs D n0Refs_good _
      (n0Refs_sem _) j _ hj.le hb hb1⟩

lemma H2.restricted_output_ref {n N : ℕ} (m : List Ref) (D : Dag)
    (hm : ∀ r ∈ m, na_ok n r)
    (σ : (Fin n → Bool) → (Fin N → Bool))
    (hin : ∀ x, m.map (refVal (List.ofFn x)) = List.ofFn (σ x))
    (o : ℕ) (ho : o < N + D.length) (F : (Fin n → Bool) → Bool)
    (hF : ∀ x, val D (σ x) o = F x)
    (h0 : F (fun _ => false) = false) (h1 : F (fun _ => true) = true)
    (hs : ∀ i : Fin n, F (single i) = false) :
    ∃ r, n ≤ r ∧ r < n + (stage n m D D.length).2.length ∧
      na_look (stage n m D D.length).1 o = Sum.inr r ∧
      ∀ x, val (stage n m D D.length).2 x r = F x := by
  have hg := stage_good n m D hm D.length
  have hv : ∀ x, refVal (wl (stage n m D D.length).2 (List.ofFn x))
      (na_look (stage n m D D.length).1 o) = F x := by
    intro x
    rw [stage_wire_sem m D hm x (σ x) (hin x) D.length o le_rfl ho, hF]
  have hr := na_look_ok _ _ hg.2 o
  cases he : na_look (stage n m D D.length).1 o with
  | inl b =>
    have hb0 := hv (fun _ => false)
    have hb1 := hv (fun _ => true)
    rw [he, h0] at hb0
    rw [he, h1] at hb1
    change b = false at hb0
    change b = true at hb1
    exact False.elim (by cases b <;> simp_all)
  | inr r =>
    have hbound : r < n + (stage n m D D.length).2.length := by
      simpa only [he, na_ok] using hr
    have hsem : ∀ x, val (stage n m D D.length).2 x r = F x := by
      intro x
      simpa only [he, refVal, val] using hv x
    have hn : n ≤ r := by
      by_contra hn
      have hlt : r < n := by omega
      have hx := hsem (single ⟨r, hlt⟩)
      rw [val_input _ _ _ hlt, hs] at hx
      simp [single] at hx
    exact ⟨r, hn, hbound, rfl, hsem⟩

lemma H2.restricted_output_prefix {n N : ℕ} (m : List Ref) (D : Dag)
    (hm : ∀ r ∈ m, na_ok n r) (hmN : m.length = N)
    (σ : (Fin n → Bool) → (Fin N → Bool))
    (hin : ∀ x, m.map (refVal (List.ofFn x)) = List.ofFn (σ x))
    (o : ℕ) (ho : o < N + D.length) (F : (Fin n → Bool) → Bool)
    (hF : ∀ x, val D (σ x) o = F x)
    (h0 : F (fun _ => false) = false) (h1 : F (fun _ => true) = true)
    (hs : ∀ i : Fin n, F (single i) = false) :
    ∃ q, 1 ≤ q ∧ q ≤ (stage n m D D.length).2.length ∧
      Strict n ((stage n m D D.length).2.take q) ∧
      ((stage n m D D.length).2.take q).length = q ∧
      (keptEmitted n m D D.length q).card = q ∧
      (∀ x, val ((stage n m D D.length).2.take q) x
        (outW n ((stage n m D D.length).2.take q)) = F x) ∧
      (∀ j ∈ keptEmitted n m D D.length q, ∀ x,
        val ((stage n m D D.length).2.take q) x (n + (stage n m D j).2.length) =
          val D (σ x) (N + j)) := by
  obtain ⟨r, hrn, hrr, _, hrsem⟩ := restricted_output_ref m D hm σ hin o ho F hF h0 h1 hs
  let q := r - n + 1
  have hq1 : 1 ≤ q := by dsimp [q]; omega
  have hqR : q ≤ (stage n m D D.length).2.length := by dsimp [q]; omega
  have hlen : ((stage n m D D.length).2.take q).length = q := by
    rw [List.length_take, Nat.min_eq_left hqR]
  have hout : outW n ((stage n m D D.length).2.take q) = r := by
    rw [outW, hlen]
    dsimp [q]
    omega
  refine ⟨q, hq1, hqR, na_strict_take (stage_good n m D hm D.length).1 q,
    hlen, keptEmitted_card n m D D.length q hqR, ?_, ?_⟩
  · intro x
    rw [hout, val_take _ x q r (by dsimp [q]; omega) hqR, hrsem]
  · intro j hj x
    exact keptEmitted_wire_sem m D hm hmN x (σ x) (hin x) le_rfl hqR hj

lemma H2.keptEmitted_marked_budget (n : ℕ) (m : List Ref) (D : Dag)
    (k q : ℕ) (hq : q ≤ (stage n m D k).2.length) (Z M : Finset ℕ)
    (hZ : Z ⊆ Finset.range k) (hM : M ⊆ Finset.range k) (hZM : Disjoint M Z)
    (hz : ∀ j ∈ Z, (stage n m D (j + 1)).2 = (stage n m D j).2) :
    q + Z.card + M.card ≤ k + (keptEmitted n m D k q ∩ M).card := by
  let S := keptEmitted n m D k q
  have hSk : S ⊆ Finset.range k := by
    intro j hj
    exact Finset.mem_range.mpr ((emitted_mem n m D k j).mp
      (Finset.mem_filter.mp hj).1).1
  have hSZ : Disjoint S Z := by
    apply Finset.disjoint_left.mpr
    intro j hj hjZ
    exact ((stage_noemit_iff n m D (Finset.mem_range.mp (hZ hjZ))).mpr (hz j hjZ))
      (Finset.mem_filter.mp hj).1
  have hUZ : Disjoint (S ∪ M) Z := Finset.disjoint_union_left.mpr ⟨hSZ, hZM⟩
  have hsub : (S ∪ M) ∪ Z ⊆ Finset.range k := by
    exact Finset.union_subset (Finset.union_subset hSk hM) hZ
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hUZ, Finset.card_range] at hc
  have hu := Finset.card_union_add_card_inter S M
  have hs : S.card = q := keptEmitted_card n m D k q hq
  change q + Z.card + M.card ≤ k + (S ∩ M).card
  omega

lemma H2.n0_output_prefix (D : Dag) (o : ℕ) (ho : o < 10 + D.length)
    (F : (Fin 6 → Bool) → Bool) (hF : ∀ x, val D (restrictN0 x) o = F x)
    (h0 : F (fun _ => false) = false) (h1 : F (fun _ => true) = true)
    (hs : ∀ i : Fin 6, F (single i) = false) :
    ∃ q, 1 ≤ q ∧ q ≤ (stage 6 n0Refs D D.length).2.length ∧
      Strict 6 ((stage 6 n0Refs D D.length).2.take q) ∧
      ((stage 6 n0Refs D D.length).2.take q).length = q ∧
      (keptEmitted 6 n0Refs D D.length q).card = q ∧
      (∀ x, val ((stage 6 n0Refs D D.length).2.take q) x
        (outW 6 ((stage 6 n0Refs D D.length).2.take q)) = F x) ∧
      (∀ j ∈ keptEmitted 6 n0Refs D D.length q, ∀ x,
        val ((stage 6 n0Refs D D.length).2.take q) x (6 + (stage 6 n0Refs D j).2.length) =
          val D (restrictN0 x) (10 + j)) :=
  restricted_output_prefix n0Refs D n0Refs_good n0Refs_length restrictN0 n0Refs_sem
    o ho F hF h0 h1 hs

lemma H2.restrictN0_eq_neighborhood (x : Fin 6 → Bool) :
    restrictN0 x = neighborhoodResidualRows x := by
  funext v
  fin_cases v <;> rfl

lemma H2.n0_noemit_copyBoundary {D : Dag} (hS : Strict 10 D) {j : ℕ}
    (hj : j ∈ copyBoundary 10 D (zeroWires D neighborhoodResidualRows)) :
    (stage 6 n0Refs D (j + 1)).2 = (stage 6 n0Refs D j).2 := by
  obtain ⟨hj, hs⟩ := Finset.mem_filter.mp hj
  apply n0_noemit_of_constant_operand D hS j (Finset.mem_range.mp hj)
  have hz (w : ℕ) (hw : w ∈ zeroWires D neighborhoodResidualRows) :
      val D (restrictN0 (fun _ => true)) w = false := by
    rw [restrictN0_eq_neighborhood]
    exact (mem_zeroWires.mp hw).2 _
  rcases hs with ⟨ha, _⟩ | ⟨ha | hb, _⟩
  · exact Or.inl (Or.inl (hz _ ha))
  · exact Or.inl (Or.inl (hz _ ha))
  · exact Or.inr (Or.inl (hz _ hb))

lemma H2.n0_noemit_center_gate {D : Dag} (hS : Strict 10 D) {j : ℕ}
    (hj : j ∈ centerGates D (0 : Fin 10)) :
    (stage 6 n0Refs D (j + 1)).2 = (stage 6 n0Refs D j).2 := by
  obtain ⟨hj, hz⟩ := Finset.mem_filter.mp hj
  apply n0_noemit_of_output_bottom_true D j (Finset.mem_range.mp hj)
  exact true_support_on_rows hS restrictN0 (v := (0 : Fin 10)) (fun _ => rfl) hz _

lemma H2.n0_six_nonemitted {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hi : neighborhoodI ⊆ ineligSet 10 D) :
    ∃ A : Finset ℕ, A.card = 3 ∧
      (∀ j ∈ A, j < D.length ∧ supp 10 D (10 + j) = ∅) ∧
      Disjoint (copyBoundary 10 D (zeroWires D neighborhoodResidualRows)) A ∧
      3 ≤ (copyBoundary 10 D (zeroWires D neighborhoodResidualRows)).card ∧
      (∀ j ∈ copyBoundary 10 D (zeroWires D neighborhoodResidualRows) ∪ A,
        (stage 6 n0Refs D (j + 1)).2 = (stage 6 n0Refs D j).2) := by
  classical
  let rows := neighborhoodResidualRows
  let K := zeroWires D rows
  let Z := copyBoundary 10 D K
  have hcardI : neighborhoodI.card = 3 := by decide
  have hout : val D (rows (fun _ => true)) (outW 10 D) = true :=
    neighborhood_residual_correct hc _
  have hK : K ⊆ inner 10 D := by
    intro w hw
    obtain ⟨hw, hv⟩ := mem_zeroWires.mp hw
    apply sb_mem_inner.mpr
    by_contra hn
    have heq : w = outW 10 D := by unfold outW; omega
    have hh := hv (fun _ => true)
    rw [heq, hout] at hh
    contradiction
  have hclosed : ∀ j < D.length, opA D j ∈ K → opB D j ∈ K → 10 + j ∈ K := by
    intro j hj ha hb
    refine mem_zeroWires.mpr ⟨by omega, ?_⟩
    intro r
    rw [val_gate h.1 _ j hj, (mem_zeroWires.mp ha).2 r, (mem_zeroWires.mp hb).2 r]
    cases tag D j <;> rfl
  have hsource : neighborhoodI.card ≤ (sources 10 K).card := by
    have hs : neighborhoodI.image Fin.val ⊆ sources 10 K := by
      intro w hw
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
      refine Finset.mem_filter.mpr ⟨mem_zeroWires.mpr ⟨by omega, ?_⟩, i.isLt⟩
      intro r
      rw [val_input D _ i.val i.isLt]
      exact neighborhood_rows_false r i hi
    have hh := Finset.card_le_card hs
    simpa only [Finset.card_image_of_injective _ Fin.val_injective] using hh
  have hIZ : 3 ≤ Z.card := by
    change 3 ≤ (copyBoundary 10 D K).card
    have hh := hsource.trans (source_le_copyBoundary h K hK hclosed)
    omega
  obtain ⟨pos, hpos⟩ := k4_assigned graph_ok h hc
  have hIz : ∀ i ∈ neighborhoodI, adj i 0 := by decide +kernel
  have hinj : Set.InjOn (fun i => (pos i).1) (↑neighborhoodI : Set (Fin 10)) := by
    intro i hiI j hjI heq
    change (pos i).1 = (pos j).1 at heq
    by_cases hs : (pos i).2 = (pos j).2
    · exact hpos.2 i (hi hiI) j (hi hjI) (Prod.ext heq hs)
    · have he : src D (pos i) = src D ((pos j).1, !(pos j).2) := by
        unfold src
        rw [heq]
        cases ha : (pos i).2 <;> cases hb : (pos j).2 <;> simp_all
      have hh := (hpos.1 i (hi hiI)).2.2.1 0 (hIz i hiI)
      rw [he, (hpos.1 j (hi hjI)).2.2.2, Finset.mem_singleton] at hh
      have hjz := hIz j hjI
      rw [hh] at hjz
      exact (graph_ok.2.1 j hjz).elim
  let A := neighborhoodI.image (fun i => (pos i).1)
  have hA : ∀ j ∈ A, j < D.length ∧ supp 10 D (10 + j) = ∅ ∧
      tag D j = true ∧
      ((∀ r, val D (rows r) (opA D j) = true) ∨
       (∀ r, val D (rows r) (opB D j) = true)) := by
    intro j hj
    obtain ⟨i, hiI, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨hlt, hempty, hnb, _⟩ := hpos.1 i (hi hiI)
    have hzi := hnb 0 (hIz i hiI)
    have hzn : (0 : Fin 10) ∉ supp 10 D (10 + (pos i).1) := by
      rw [hempty]; exact Finset.notMem_empty _
    have hop := sem_W_and h.1 (sem_mem_W.mpr ⟨hlt, hzi, hzn⟩)
    have ht := true_support_on_rows h.1 rows (v := (0 : Fin 10)) (fun _ => rfl) hzi
    refine ⟨hlt, hempty, hop, ?_⟩
    cases hs : (pos i).2
    · exact Or.inl (by simpa [src, hs] using ht)
    · exact Or.inr (by simpa [src, hs] using ht)
  have hZA : Disjoint Z A := by
    apply Finset.disjoint_left.mpr
    intro j hj ha
    obtain ⟨hlt, _, hop, ht⟩ := hA j ha
    obtain ⟨_, hcase⟩ := Finset.mem_filter.mp hj
    rcases hcase with ⟨hka, hkb⟩ | ⟨hk, hko⟩
    · rcases ht with ht | ht
      · have hh := (mem_zeroWires.mp hka).2 (fun _ => true)
        rw [ht] at hh; contradiction
      · have hh := (mem_zeroWires.mp hkb).2 (fun _ => true)
        rw [ht] at hh; contradiction
    · apply hko
      refine mem_zeroWires.mpr ⟨by omega, ?_⟩
      intro r
      rw [val_gate h.1 _ j hlt, hop, gop_true]
      rcases hk with hk | hk
      · rw [(mem_zeroWires.mp hk).2 r]; rfl
      · rw [(mem_zeroWires.mp hk).2 r]; simp
  refine ⟨A, ?_, fun j hj => ⟨(hA j hj).1, (hA j hj).2.1⟩, hZA, hIZ, ?_⟩
  · exact (Finset.card_image_of_injOn hinj).trans hcardI
  · intro j hj
    rcases Finset.mem_union.mp hj with hz | ha
    · exact n0_noemit_copyBoundary h.1 hz
    · obtain ⟨hlt, _, _, ht⟩ := hA j ha
      apply n0_noemit_of_constant_operand D h.1 j hlt
      rcases ht with ha | hb
      · exact Or.inl (Or.inr (by rw [restrictN0_eq_neighborhood]; exact ha _))
      · exact Or.inr (Or.inr (by rw [restrictN0_eq_neighborhood]; exact hb _))

lemma H2.n0_c6_output_prefix {D : Dag} (hc : sem_Comp 10 adj D) :
    ∃ q, 1 ≤ q ∧ q ≤ (stage 6 n0Refs D D.length).2.length ∧
      Strict 6 ((stage 6 n0Refs D D.length).2.take q) ∧
      ((stage 6 n0Refs D D.length).2.take q).length = q ∧
      (keptEmitted 6 n0Refs D D.length q).card = q ∧
      (∀ x, val ((stage 6 n0Refs D D.length).2.take q) x
        (outW 6 ((stage 6 n0Refs D D.length).2.take q)) = residualC6 x) ∧
      (∀ j ∈ keptEmitted 6 n0Refs D D.length q, ∀ x,
        val ((stage 6 n0Refs D D.length).2.take q) x (6 + (stage 6 n0Refs D j).2.length) =
          val D (restrictN0 x) (10 + j)) := by
  apply n0_output_prefix D (outW 10 D) (by unfold outW; omega) residualC6
  · intro x
    rw [restrictN0_eq_neighborhood]
    exact neighborhood_residual_correct hc x
  · rfl
  · rfl
  · intro i
    fin_cases i <;> rfl

def H2.n0ResidualVertex : Fin 6 → Fin 10 := ![2, 8, 9, 3, 7, 6]

lemma H2.restrictN0_embed (x : Fin 6 → Bool) (r : Fin 6) :
    restrictN0 x (n0ResidualVertex r) = x r := by
  fin_cases r <;> rfl

lemma H2.n0_singleton_embed_le (r : Fin 6) :
    ∀ v : Fin 10, single (n0ResidualVertex r) v = true → restrictN0 (single r) v = true := by
  intro v hv
  have he : v = n0ResidualVertex r := by simpa [single] using hv
  subst v
  rw [restrictN0_embed]
  simp [single]

lemma H2.n0_kept_support_member {D : Dag} (hS : Strict 10 D) (q : ℕ)
    (hq : q ≤ (stage 6 n0Refs D D.length).2.length) (r : Fin 6) {j : ℕ}
    (hj : j ∈ keptEmitted 6 n0Refs D D.length q)
    (hr : n0ResidualVertex r ∈ supp 10 D (10 + j)) :
    r ∈ supp 6 ((stage 6 n0Refs D D.length).2.take q)
      (6 + (stage 6 n0Refs D j).2.length) := by
  apply mem_supp.mpr
  rw [keptEmitted_wire_sem n0Refs D n0Refs_good n0Refs_length (single r)
    (restrictN0 (single r)) (n0Refs_sem _) le_rfl hq hj]
  exact val_mono hS (single (n0ResidualVertex r)) (restrictN0 (single r))
    (n0_singleton_embed_le r) (10 + j) (mem_supp.mp hr)

lemma H2.n0_kept_no_center_support {D : Dag} (hS : Strict 10 D) (q : ℕ) {j : ℕ}
    (hj : j ∈ keptEmitted 6 n0Refs D D.length q) :
    (0 : Fin 10) ∉ supp 10 D (10 + j) := by
  intro hz
  have he := (Finset.mem_filter.mp hj).1
  have hjlt := ((emitted_mem 6 n0Refs D D.length j).mp he).1
  have hno := n0_noemit_center_gate hS
    (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjlt, hz⟩)
  exact ((stage_noemit_iff 6 n0Refs D hjlt).mpr hno) he

lemma H2.n0_kept_rank_injective (D : Dag) (q : ℕ) :
    Set.InjOn (fun j => (stage 6 n0Refs D j).2.length)
      (keptEmitted 6 n0Refs D D.length q) := by
  intro i hi j hj he
  exact emitted_rank_inj 6 n0Refs D D.length (Finset.mem_filter.mp hi).1
    (Finset.mem_filter.mp hj).1 he

lemma H2.n0_first_marks_nonemit_set {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hi : neighborhoodI ⊆ ineligSet 10 D)
    (M : Finset ℕ) (hM : M ⊆ Finset.range D.length)
    (hcard : ∀ j ∈ M, 2 ≤ (supp 10 D (10 + j)).card)
    (hfirst : ∀ j ∈ M, ∀ k < j, supp 10 D (10 + k) ≠ supp 10 D (10 + j)) :
    ∃ Z : Finset ℕ, Z ⊆ Finset.range D.length ∧ 6 ≤ Z.card ∧ Disjoint Z M ∧
      ∀ j ∈ Z, (stage 6 n0Refs D (j + 1)).2 = (stage 6 n0Refs D j).2 := by
  classical
  obtain ⟨A, hAc, hA, hZA, hZc, hz⟩ := n0_six_nonemitted h hc hi
  let Z := copyBoundary 10 D (zeroWires D neighborhoodResidualRows)
  have hZM : Disjoint Z M := by
    apply Finset.disjoint_left.mpr
    intro j hj hm
    have htop : ∀ v, v ∉ neighborhoodI → neighborhoodResidualRows (fun _ => true) v = true := by
      intro v hv
      cases he : neighborhoodResidualRows (fun _ => true) v
      · exact False.elim (hv ((neighborhood_rows_top v).mp he))
      · rfl
    have hdis : Disjoint (supp 10 D (10 + j)) neighborhoodI := by
      apply Finset.disjoint_left.mpr
      intro v hv hvi
      have hp := sem_inelig_pure graph_ok h.1 hc (hi hvi) hv
      have hh := hcard j hm
      rw [hp, Finset.card_singleton] at hh
      omega
    exact first_support_gate_not_copyBoundary h.1 neighborhoodResidualRows neighborhoodI
      (fun _ => true) htop (Finset.mem_range.mp (hM hm)) (hcard j hm) hdis
      rfl (hfirst j hm) hj
  have hAM : Disjoint A M := by
    apply Finset.disjoint_left.mpr
    intro j ha hm
    have hh := hcard j hm
    rw [(hA j ha).2, Finset.card_empty] at hh
    omega
  refine ⟨Z ∪ A, ?_, ?_, Finset.disjoint_union_left.mpr ⟨hZM, hAM⟩, hz⟩
  · intro j hj
    rcases Finset.mem_union.mp hj with hzj | haj
    · exact (Finset.mem_filter.mp hzj).1
    · exact Finset.mem_range.mpr (hA j haj).1
  · rw [Finset.card_union_of_disjoint hZA, hAc]
    omega

lemma H2.n0_first_marks_budget {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hi : neighborhoodI ⊆ ineligSet 10 D)
    (M : Finset ℕ) (hM : M ⊆ Finset.range D.length)
    (hcard : ∀ j ∈ M, 2 ≤ (supp 10 D (10 + j)).card)
    (hfirst : ∀ j ∈ M, ∀ k < j, supp 10 D (10 + k) ≠ supp 10 D (10 + j))
    (q : ℕ) (hq : q ≤ (stage 6 n0Refs D D.length).2.length) :
    q + 6 + M.card ≤ D.length + (keptEmitted 6 n0Refs D D.length q ∩ M).card := by
  obtain ⟨Z, hZ, hZsix, hdis, hz⟩ := n0_first_marks_nonemit_set h hc hi M hM hcard hfirst
  have hh := keptEmitted_marked_budget 6 n0Refs D D.length q hq Z M hZ hM hdis.symm hz
  omega

lemma H2.n0_first_six_marks_prefix_impossible {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hi : neighborhoodI ⊆ ineligSet 10 D)
    (M : Finset ℕ) (hM : M ⊆ Finset.range D.length) (hsix : 6 ≤ M.card)
    (hcard : ∀ j ∈ M, 2 ≤ (supp 10 D (10 + j)).card)
    (hfirst : ∀ j ∈ M, ∀ k < j, supp 10 D (10 + k) ≠ supp 10 D (10 + j))
    (q : ℕ) (hq : q ≤ (stage 6 n0Refs D D.length).2.length) (hlen : D.length ≤ 19)
    (hlower : 8 + (keptEmitted 6 n0Refs D D.length q ∩ M).card ≤ q) : False := by
  have hh := n0_first_marks_budget h hc hi M hM hcard hfirst q hq
  omega

def H2.n0OriginalPairs : Fin 3 → Finset (Fin 10) := ![{2, 6}, {3, 9}, {7, 8}]

def H2.n0ResidualPairs : Fin 3 → Finset (Fin 6) := ![{0, 5}, {1, 4}, {2, 3}]

def H2.n0PairClass : Fin 3 → Fin 3 := ![0, 2, 1]

lemma H2.n0PairClass_involution (p : Fin 3) : n0PairClass (n0PairClass p) = p := by
  fin_cases p <;> rfl

lemma H2.n0ResidualPairs_embed (p : Fin 3) (r : Fin 6) (hr : r ∈ n0ResidualPairs p) :
    n0ResidualVertex r ∈ n0OriginalPairs (n0PairClass p) := by
  revert hr
  fin_cases p <;> fin_cases r <;> decide +kernel

lemma H2.n0_retained_marks {D : Dag} (hS : Strict 10 D) (q : ℕ)
    (hq : q ≤ (stage 6 n0Refs D D.length).2.length) (M : Finset ℕ)
    (hgood : ∀ j ∈ M, (0 : Fin 10) ∈ supp 10 D (10 + j) ∨
      ∃ p : Fin 3, supp 10 D (10 + j) = n0OriginalPairs p)
    (hunique : ∀ i ∈ M, ∀ j ∈ M, ∀ p : Fin 3,
      supp 10 D (10 + i) = n0OriginalPairs p →
      supp 10 D (10 + j) = n0OriginalPairs p → i = j) :
    ∃ (S : Finset (Fin 3)) (g : Fin 3 → ℕ),
      S.card = (keptEmitted 6 n0Refs D D.length q ∩ M).card ∧
      Set.InjOn g S ∧
      ∀ p ∈ S, 6 ≤ g p ∧ g p < 6 + q ∧
        n0ResidualPairs p ⊆ supp 6 ((stage 6 n0Refs D D.length).2.take q) (g p) := by
  classical
  let K := keptEmitted 6 n0Refs D D.length q ∩ M
  have hex : ∀ j : ℕ, ∃ p : Fin 3,
      j ∈ K → supp 10 D (10 + j) = n0OriginalPairs (n0PairClass p) := by
    intro j
    by_cases hj : j ∈ K
    · obtain ⟨hjk, hjM⟩ := Finset.mem_inter.mp hj
      rcases hgood j hjM with hz | ⟨p, hp⟩
      · exact (n0_kept_no_center_support hS q hjk hz).elim
      · exact ⟨n0PairClass p, fun _ => by rw [n0PairClass_involution]; exact hp⟩
    · exact ⟨0, fun h => (hj h).elim⟩
  choose label hlabel using hex
  have hlabelinj : Set.InjOn label K := by
    intro i hi j hj he
    apply hunique i (Finset.mem_inter.mp hi).2 j (Finset.mem_inter.mp hj).2
      (n0PairClass (label i)) (hlabel i hi)
    rw [he]
    exact hlabel j hj
  let S := K.image label
  have hexrep : ∀ p : Fin 3, ∃ j : ℕ, p ∈ S → j ∈ K ∧ label j = p := by
    intro p
    by_cases hp : p ∈ S
    · obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hp
      exact ⟨j, fun _ => ⟨hj, he⟩⟩
    · exact ⟨0, fun h => (hp h).elim⟩
  choose rep hrep using hexrep
  let g : Fin 3 → ℕ := fun p => 6 + (stage 6 n0Refs D (rep p)).2.length
  refine ⟨S, g, Finset.card_image_of_injOn hlabelinj, ?_, ?_⟩
  · intro p hp t ht he
    have hrp := hrep p hp
    have hrt := hrep t ht
    have hrank : (stage 6 n0Refs D (rep p)).2.length =
        (stage 6 n0Refs D (rep t)).2.length := by dsimp [g] at he; omega
    have hre := n0_kept_rank_injective D q (Finset.mem_inter.mp hrp.1).1
      (Finset.mem_inter.mp hrt.1).1 hrank
    exact hrp.2.symm.trans ((congrArg label hre).trans hrt.2)
  · intro p hp
    obtain ⟨hrK, hrlabel⟩ := hrep p hp
    have hrkept := (Finset.mem_inter.mp hrK).1
    have hrbound := (Finset.mem_filter.mp hrkept).2
    refine ⟨by dsimp [g]; omega, by dsimp [g]; omega, ?_⟩
    intro r hr
    apply n0_kept_support_member hS q hq r hrkept
    rw [hlabel (rep p) hrK, hrlabel]
    exact n0ResidualPairs_embed p r hr

lemma H2.sem_W_gate_injective {n : ℕ} {D : Dag} (hS : Strict n D) (z : Fin n) :
    Set.InjOn Prod.fst (↑(sem_W n D z) : Set (ℕ × Bool)) := by
  rintro ⟨j, s⟩ hs ⟨k, t⟩ ht he
  change j = k at he
  subst k
  by_cases hst : s = t
  · exact Prod.ext rfl hst
  have ha : z ∈ supp n D (opA D j) := by
    cases s <;> cases t <;> simp_all [src, sem_mem_W]
  have hb : z ∈ supp n D (opB D j) := by
    cases s <;> cases t <;> simp_all [src, sem_mem_W]
  have hg := (sem_mem_W.mp hs).1
  have htag := sem_W_and hS hs
  have hout := (sem_mem_W.mp hs).2.2
  apply False.elim
  apply hout
  apply mem_supp.mpr
  rw [val_gate hS (single z) j hg, htag, gop_true, mem_supp.mp ha, mem_supp.mp hb]
  rfl

lemma H2.n0_exit_noemit {D : Dag} (hS : Strict 10 D) {e : ℕ × Bool}
    (he : e ∈ sem_W 10 D (0 : Fin 10)) :
    (stage 6 n0Refs D (e.1 + 1)).2 = (stage 6 n0Refs D e.1).2 := by
  obtain ⟨hj, hs, _⟩ := sem_mem_W.mp he
  have ht := true_support_on_rows hS restrictN0 (v := (0 : Fin 10)) (fun _ => rfl) hs
  apply n0_noemit_of_constant_operand D hS e.1 hj
  cases hb : e.2
  · exact Or.inl (Or.inr (by simpa [src, hb] using ht (fun _ => false)))
  · exact Or.inr (Or.inr (by simpa [src, hb] using ht (fun _ => false)))

lemma H2.n0_exit_not_copyBoundary {D : Dag} (hS : Strict 10 D) {e : ℕ × Bool}
    (he : e ∈ sem_W 10 D (0 : Fin 10)) :
    e.1 ∉ copyBoundary 10 D (zeroWires D neighborhoodResidualRows) := by
  intro hz
  obtain ⟨hj, hs, _⟩ := sem_mem_W.mp he
  have hop := sem_W_and hS he
  have ht := true_support_on_rows hS neighborhoodResidualRows
    (v := (0 : Fin 10)) (fun _ => rfl) hs
  have htt : (∀ r, val D (neighborhoodResidualRows r) (opA D e.1) = true) ∨
      (∀ r, val D (neighborhoodResidualRows r) (opB D e.1) = true) := by
    cases hb : e.2
    · exact Or.inl (by simpa [src, hb] using ht)
    · exact Or.inr (by simpa [src, hb] using ht)
  obtain ⟨_, hcase⟩ := Finset.mem_filter.mp hz
  rcases hcase with ⟨hka, hkb⟩ | ⟨hk, hko⟩
  · rcases htt with hta | htb
    · have hh := (mem_zeroWires.mp hka).2 (fun _ => true)
      rw [hta] at hh
      contradiction
    · have hh := (mem_zeroWires.mp hkb).2 (fun _ => true)
      rw [htb] at hh
      contradiction
  · apply hko
    refine mem_zeroWires.mpr ⟨by omega, ?_⟩
    intro r
    rw [val_gate hS _ e.1 hj, hop, gop_true]
    rcases hk with hk | hk
    · rw [(mem_zeroWires.mp hk).2 r]; rfl
    · rw [(mem_zeroWires.mp hk).2 r]; simp

end packScope1
section packScope2

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

section packScope3

-- Circuit normalization and wire counting, adapted from L_meta_971.
section packScope4



open PEqualNP.Outside.L_meta_2590_aux.H2

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

@[local simp] lemma C6.DagTools.gop_true (a b : Bool) : gop true a b = (a && b) := rfl

@[local simp] lemma C6.DagTools.gop_false (a b : Bool) : gop false a b = (a || b) := rfl

section SurplusFlow

variable {n : ℕ} {D : Dag}

end SurplusFlow

section SemCore

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

end SemCore

def H2.sem_bar (e : ℕ × Bool) : ℕ × Bool := (e.1, !e.2)

section SemCodes

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

lemma H2.sem_bar_bar (e : ℕ × Bool) : sem_bar (sem_bar e) = e := by simp [sem_bar]

lemma H2.sem_bar_ne (e : ℕ × Bool) : sem_bar e ≠ e := by
  intro h
  have h2 := congrArg Prod.snd h
  simp [sem_bar] at h2

lemma H2.sem_same_gate {e f : ℕ × Bool} (h : e.1 = f.1) : f = e ∨ f = sem_bar e := by
  obtain ⟨j, s⟩ := e
  obtain ⟨k, t⟩ := f
  simp only at h
  subst h
  cases s <;> cases t <;> simp [sem_bar]

lemma H2.sem_flow1 (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D) (x : Fin n) :
    (sem_W n D x).card + (merges n D (carrierT n D {x})).card =
      1 + surplusOn D (carrierT n D {x}) := by
  have h1 := carrier_flow_union h {x} (by rw [sem_supp_out hG hC]; simp)
  rwa [Finset.card_singleton] at h1

lemma H2.sem_edge_slots (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) {x y : Fin n}
    (hxy : G x y) : ∃ e, e ∈ sem_W n D x ∧ sem_bar e ∈ sem_W n D y ∧
      y ∉ supp n D (src D e) ∧ x ∉ supp n D (src D (sem_bar e)) ∧
      val D (sem_two x y) (n + e.1) = true := by
  obtain ⟨j, hj, -, hval, hju, hjv, s, h1, h2, h3, h4⟩ := sem_joint_meeting hG hS hC hxy
  exact ⟨(j, s), sem_mem_W.mpr ⟨hj, h1, hju⟩, sem_mem_W.mpr ⟨hj, h3, hjv⟩, h2, h4, hval⟩

end SemCodes

section SemArms

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

lemma H2.sem_zm_gate (hS : Strict n D) {x : Fin n} (hM : merges n D (carrierT n D {x}) = ∅)
    {j : ℕ} (hj : j < D.length) (hx : x ∈ supp n D (n + j)) :
    tag D j = false ∧ ¬ (x ∈ supp n D (opA D j) ∧ x ∈ supp n D (opB D j)) := by
  have hnot : ¬ (x ∈ supp n D (opA D j) ∧ x ∈ supp n D (opB D j)) := by
    intro hc
    have hm : j ∈ merges n D (carrierT n D {x}) := by
      rw [merges, Finset.mem_filter, Finset.mem_range]
      exact ⟨hj, sem_mem_carrier1.mpr hx, sem_mem_carrier1.mpr hc.1, sem_mem_carrier1.mpr hc.2⟩
    rw [hM] at hm
    exact Finset.notMem_empty _ hm
  refine ⟨?_, hnot⟩
  by_contra ht
  rw [Bool.not_eq_false] at ht
  rw [sem_supp_and hS hj ht, Finset.mem_inter] at hx
  exact hnot hx

lemma H2.sem_code_count (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (b : Fin n → ℕ) (hb : PureBranch n D b) (x : Fin n) :
    (sem_W n D x).card + (merges n D (carrierT n D {x})).card =
      1 + (({x} : Finset (Fin n)) ∩ eligSet n D).card +
        ((residualUnits n D b).filter (fun u => x ∈ supp n D u.1)).card := by
  have h1 := sem_flow1 hG h hC x
  have h2 := surplus_carrierT_eq h.1 b hb {x}
  have h3 : (residualUnits n D b).filter (fun u => (supp n D u.1 ∩ {x}).Nonempty) =
      (residualUnits n D b).filter (fun u => x ∈ supp n D u.1) := by
    refine Finset.filter_congr (fun u _ => ?_)
    constructor
    · rintro ⟨y, hy⟩
      rw [Finset.mem_inter, Finset.mem_singleton] at hy
      exact hy.2 ▸ hy.1
    · intro hx
      exact ⟨x, Finset.mem_inter.mpr ⟨hx, Finset.mem_singleton_self x⟩⟩
  rw [h3] at h2
  omega

end SemArms
end packScope4

open PEqualNP.Outside.L_meta_2590_aux.H2

abbrev C6.V := Fin 6

def C6.adj (u v : V) : Prop :=
  (u.val, v.val) ∈ [(0,3),(0,4),(1,3),(1,5),(2,4),(2,5)] ∨
  (v.val, u.val) ∈ [(0,3),(0,4),(1,3),(1,5),(2,4),(2,5)]

def C6.Independent (I : Finset V) : Prop := ∀ u ∈ I, ∀ v ∈ I, ¬ adj u v

set_option synthInstance.maxSize 4096 in
lemma C6.graph_ok : sem_Gr adj := by
  unfold sem_Gr adj
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 10000000 in
set_option synthInstance.maxSize 4096 in
lemma C6.independent_facts : ∀ I : Finset V, Independent I →
    I.card ≤ 3 ∧ (I.card = 3 → ∀ v ∉ I,
      ∃ a ∈ I, ∃ b ∈ I, a ≠ b ∧ adj v a ∧ adj v b) := by
  unfold Independent adj
  decide +kernel

lemma C6.inelig_independent {D : Dag} (h : StrictLive 6 D) (hc : sem_Comp 6 adj D) :
    Independent (ineligSet 6 D) := by
  intro u hu v hv huv
  rcases sem_elig_cover graph_ok h hc huv with he | he
  · exact (sem_mem_inelig.mp hu) he
  · exact (sem_mem_inelig.mp hv) he

lemma C6.consumer_same_gate {D : Dag} {v w : V} {e f : ℕ × Bool}
    (hev : supp 6 D (src D e) = {v})
    (hfw : supp 6 D (src D f) = {w})
    (hne : ∀ a, adj v a → a ∈ supp 6 D (src D (sem_bar e)))
    (hgate : e.1 = f.1) : v = w := by
  rcases sem_same_gate hgate with hf | hf
  · rw [hf, hev] at hfw
    simpa only [Finset.singleton_inj] using hfw
  · obtain ⟨a, hva, haw⟩ := graph_ok.2.2.2 v w
    have hm := hne a hva
    rw [← hf, hfw, Finset.mem_singleton] at hm
    exact (haw hm).elim

def C6.Consumer (D : Dag) (v : V) (e : ℕ × Bool) : Prop :=
  e.1 < D.length ∧ tag D e.1 = true ∧ supp 6 D (src D e) = {v} ∧
    supp 6 D (6 + e.1) = ∅ ∧
    (∀ a, adj v a → a ∈ supp 6 D (src D (sem_bar e))) ∧
    sem_W 6 D v = {e}

lemma C6.consumer_exists {D : Dag} (h : StrictLive 6 D) (hc : sem_Comp 6 adj D)
    {v : V} (hv : v ∈ ineligSet 6 D) : ∃ e, Consumer D v e := by
  obtain ⟨e, he1, he2, he3, he4, he5, he6, _⟩ := sem_inelig_consumer graph_ok h hc hv
  exact ⟨e, he1, he2, he3, he4, he5, he6⟩

lemma C6.consumers_injective {D : Dag} {v w : V} {e f : ℕ × Bool}
    (he : Consumer D v e) (hf : Consumer D w f) (hgate : e.1 = f.1) : v = w :=
  consumer_same_gate he.2.2.1 hf.2.2.1 he.2.2.2.2.1 hgate

end packScope3

section packScope5
open PEqualNP.Outside.L_meta_2590_aux.C6

open PEqualNP.Outside.L_meta_2590_aux.H2

def C6.oppositePair (v w : V) : Prop :=
  (v.val, w.val) ∈ [(0,5),(1,4),(2,3)] ∨ (w.val, v.val) ∈ [(0,5),(1,4),(2,3)]

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 10000000 in
lemma C6.independent_hits_opposite : ∀ I : Finset V, Independent I → I.card = 3 →
    ∀ v w, oppositePair v w → v ∈ I ∨ w ∈ I := by
  unfold Independent adj oppositePair
  decide +kernel

set_option synthInstance.maxSize 4096 in
lemma C6.opposite_distinct : ∀ v w : V, oppositePair v w → v ≠ w := by
  unfold oppositePair
  decide +kernel

def C6.fourEndpoints : Finset V := {0, 1, 4, 5}

end packScope5

section packScope6
open PEqualNP.Outside.L_meta_2590_aux.C6

open PEqualNP.Outside.L_meta_2590_aux.H2

def C6.swapPairs : Equiv.Perm V where
  toFun := ![0, 2, 1, 4, 3, 5]
  invFun := ![0, 2, 1, 4, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def C6.rotatePairs : Equiv.Perm V where
  toFun := ![2, 0, 1, 4, 5, 3]
  invFun := ![1, 2, 0, 5, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

lemma C6.swapPairs_adj : ∀ u v : V, adj (swapPairs u) (swapPairs v) ↔ adj u v := by
  unfold adj
  decide +kernel

lemma C6.rotatePairs_adj : ∀ u v : V, adj (rotatePairs u) (rotatePairs v) ↔ adj u v := by
  unfold adj
  decide +kernel

lemma C6.c6_relabel_computes (σ : Equiv.Perm V)
    (ha : ∀ u v, adj (σ u) (σ v) ↔ adj u v) {D : Dag}
    (h : StrictLive 6 D) (hc : sem_Comp 6 adj D) :
    sem_Comp 6 adj (relabel σ D) := by
  intro x
  rw [relabel_out σ h.1 h.2.2, hc]
  constructor
  · rintro ⟨u, v, huv, hu, hv⟩
    exact ⟨σ u, σ v, (ha u v).mpr huv, hu, hv⟩
  · rintro ⟨u, v, huv, hu, hv⟩
    refine ⟨σ.symm u, σ.symm v, ?_, ?_, ?_⟩
    · apply (ha _ _).mp
      simpa using huv
    · simpa using hu
    · simpa using hv

end packScope6

section packScope7
open PEqualNP.Outside.L_meta_2590_aux.C6

open PEqualNP.Outside.L_meta_2590_aux.H2

def C6.edgeBool (x : V → Bool) : Bool :=
  (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 3) ||
  (x 1 && x 5) || (x 2 && x 4) || (x 2 && x 5)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 4096 in
lemma C6.edgeBool_spec : ∀ x : V → Bool, edgeBool x = true ↔ sem_Edge adj x := by
  unfold edgeBool sem_Edge adj
  decide +kernel

end packScope7

section packScope8

-- Birth roles: C = c*(e+f), D = d*(a+b), K = (a+f)*(b+e).
def C6.ThreeBirth.factors (t : Fin 3) (x : V → Bool) : Bool × Bool :=
  ![(x 2, x 4 || x 5), (x 3, x 0 || x 1), (x 0 || x 5, x 1 || x 4)] t

open PEqualNP.Outside.L_meta_2590_aux.C6.ThreeBirth

def C6.ThreeBirth.order (o : Fin 6) : Fin 3 → Fin 3 :=
  ![![0, 1, 2], ![0, 2, 1], ![1, 0, 2], ![1, 2, 0], ![2, 0, 1], ![2, 1, 0]] o

def C6.ThreeBirth.oneNoise (k : Bool) (a : Bool) : Bool := k && a

def C6.ThreeBirth.twoNoise (k : Fin 5) (a b : Bool) : Bool := ![false, a, b, a && b, a || b] k

def C6.ThreeBirth.births (o : Fin 6) (p q : Bool) (r s : Fin 5) (x : V → Bool) : Fin 3 → Bool :=
  let f₀ := factors (order o 0) x
  let a := f₀.1 && f₀.2
  let f₁ := factors (order o 1) x
  let b := (f₁.1 || oneNoise p a) && (f₁.2 || oneNoise q a)
  let f₂ := factors (order o 2) x
  let c := (f₂.1 || twoNoise r a b) && (f₂.2 || twoNoise s a b)
  ![a, b, c]

def C6.ThreeBirth.rowMask (r : Fin 5) : Nat := ![9, 34, 36, 7, 56] r

def C6.ThreeBirth.rowInput (r : Fin 5) : V → Bool := fun v => (rowMask r).testBit v.val

def C6.ThreeBirth.below {α : Type} (x y : α → Bool) : Prop := ∀ i, x i = true → y i = true

def C6.ThreeBirth.Mono1 (f : Bool → Bool) : Prop :=
  ∀ a b, (a = true → b = true) → f a = true → f b = true

def C6.ThreeBirth.Mono2 (f : Bool → Bool → Bool) : Prop :=
  ∀ a b c d, (a = true → c = true) → (b = true → d = true) →
    f a b = true → f c d = true

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
lemma C6.ThreeBirth.oneNoise_complete : ∀ f : Bool → Bool, Mono1 f → f false = false →
    ∃ k : Bool, ∀ a, f a = oneNoise k a := by
  unfold Mono1 oneNoise
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
lemma C6.ThreeBirth.twoNoise_complete : ∀ f : Bool → Bool → Bool, Mono2 f → f false false = false →
    ∃ k : Fin 5, ∀ a b, f a b = twoNoise k a b := by
  unfold Mono2 twoNoise
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
lemma C6.ThreeBirth.order_complete : ∀ f : Fin 3 → Fin 3, Function.Bijective f →
    ∃ o : Fin 6, f = order o := by
  unfold Function.Bijective Function.Injective Function.Surjective order
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
set_option synthInstance.maxSize 4096 in
lemma C6.ThreeBirth.row_domination : ∀ (o : Fin 6) (p q : Bool) (r s : Fin 5),
    ∃ i : Fin 3, ∃ j : Fin 2,
      below (births o p q r s (rowInput ⟨i.val, by omega⟩))
        (births o p q r s (rowInput ⟨3 + j.val, by omega⟩)) := by
  unfold below births factors order oneNoise twoNoise rowInput rowMask
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
lemma C6.ThreeBirth.positive_rows : ∀ i : Fin 3, edgeBool (rowInput ⟨i.val, by omega⟩) = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
lemma C6.ThreeBirth.negative_rows : ∀ j : Fin 2, edgeBool (rowInput ⟨3 + j.val, by omega⟩) = false := by
  decide +kernel

lemma C6.ThreeBirth.no_monotone_combiner (o : Fin 6) (p q : Bool) (r s : Fin 5)
    (F : (Fin 3 → Bool) → Bool)
    (hF : ∀ u v, below u v → F u = true → F v = true)
    (hc : ∀ x : V → Bool, F (births o p q r s x) = edgeBool x) : False := by
  obtain ⟨i, j, hij⟩ := row_domination o p q r s
  have hp : F (births o p q r s (rowInput ⟨i.val, by omega⟩)) = true := by
    rw [hc]
    exact positive_rows i
  have hn := hF _ _ hij hp
  rw [hc, negative_rows j] at hn
  cases hn

-- The unrestricted model permits any monotone zero-preserving noise function
-- of the previously born empty-support signals at each positive OR factor.
def C6.ThreeBirth.generalBirths (σ : Fin 3 → Fin 3) (p q : Bool → Bool)
    (r s : Bool → Bool → Bool) (x : V → Bool) : Fin 3 → Bool :=
  let f₀ := factors (σ 0) x
  let a := f₀.1 && f₀.2
  let f₁ := factors (σ 1) x
  let b := (f₁.1 || p a) && (f₁.2 || q a)
  let f₂ := factors (σ 2) x
  let c := (f₂.1 || r a b) && (f₂.2 || s a b)
  ![a, b, c]

lemma C6.ThreeBirth.no_general_combiner (σ : Fin 3 → Fin 3) (hσ : Function.Bijective σ)
    (p q : Bool → Bool) (r s : Bool → Bool → Bool)
    (hp : Mono1 p) (hp0 : p false = false)
    (hq : Mono1 q) (hq0 : q false = false)
    (hr : Mono2 r) (hr0 : r false false = false)
    (hs : Mono2 s) (hs0 : s false false = false)
    (F : (Fin 3 → Bool) → Bool)
    (hF : ∀ u v, below u v → F u = true → F v = true)
    (hc : ∀ x : V → Bool, F (generalBirths σ p q r s x) = edgeBool x) : False := by
  obtain ⟨o, rfl⟩ := order_complete σ hσ
  obtain ⟨p', hp'⟩ := oneNoise_complete p hp hp0
  obtain ⟨q', hq'⟩ := oneNoise_complete q hq hq0
  obtain ⟨r', hr'⟩ := twoNoise_complete r hr hr0
  obtain ⟨s', hs'⟩ := twoNoise_complete s hs hs0
  apply no_monotone_combiner o p' q' r' s' F hF
  intro x
  have he : generalBirths (order o) p q r s x = births o p' q' r' s' x := by
    simp only [generalBirths, births, hp', hq', hr', hs']
  rw [← he]
  exact hc x

end packScope8


section packScope9
open PEqualNP.Outside.L_meta_2590_aux.H2

def LinearNoise.linear {n : Nat} (S : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ v ∈ S, x v = true)

open PEqualNP.Outside.L_meta_2590_aux.LinearNoise

lemma LinearNoise.linear_empty {n : Nat} (x : Fin n → Bool) : linear ∅ x = false := by
  simp [linear]

lemma LinearNoise.linear_singleton {n : Nat} (v : Fin n) (x : Fin n → Bool) :
    linear {v} x = x v := by simp [linear]

lemma LinearNoise.linear_union {n : Nat} (S T : Finset (Fin n)) (x : Fin n → Bool) :
    linear (S ∪ T) x = (linear S x || linear T x) := by
  apply Bool.eq_iff_iff.mpr
  simp only [linear, decide_eq_true_eq, Finset.mem_union, Bool.or_eq_true]
  constructor
  · rintro ⟨v, hv | hv, hx⟩
    · exact Or.inl ⟨v, hv, hx⟩
    · exact Or.inr ⟨v, hv, hx⟩
  · rintro (⟨v,hv,hx⟩ | ⟨v,hv,hx⟩)
    · exact ⟨v, Or.inl hv, hx⟩
    · exact ⟨v, Or.inr hv, hx⟩

def LinearNoise.ZeroMono {k : Nat} (f : (Fin k → Bool) → Bool) : Prop :=
  f (fun _ => false) = false ∧
  ∀ a b, (∀ i, a i = true → b i = true) → f a = true → f b = true

def LinearNoise.UsesAtMost {k : Nat} (n : Nat) (birth : Fin k → Nat)
    (w : Nat) (f : (Fin k → Bool) → Bool) : Prop :=
  ∀ a b, (∀ i, n + birth i ≤ w → a i = b i) → f a = f b

lemma LinearNoise.uses_mono {k n : Nat} {birth : Fin k → Nat} {w u : Nat}
    {f : (Fin k → Bool) → Bool} (h : UsesAtMost n birth w f) (hwu : w ≤ u) :
    UsesAtMost n birth u f := by
  intro a b hab
  apply h a b
  intro i hi
  exact hab i (hi.trans hwu)

lemma LinearNoise.zeroMono_or {k : Nat} {f g : (Fin k → Bool) → Bool}
    (hf : ZeroMono f) (hg : ZeroMono g) : ZeroMono (fun z => f z || g z) := by
  refine ⟨by dsimp only; rw [hf.1,hg.1]; rfl, ?_⟩
  intro a b hab hh
  rw [Bool.or_eq_true] at hh ⊢
  exact hh.elim (fun h => Or.inl (hf.2 a b hab h)) (fun h => Or.inr (hg.2 a b hab h))

lemma LinearNoise.zeroMono_and {k : Nat} {f g : (Fin k → Bool) → Bool}
    (hf : ZeroMono f) (hg : ZeroMono g) : ZeroMono (fun z => f z && g z) := by
  refine ⟨by dsimp only; rw [hf.1,hg.1]; rfl, ?_⟩
  intro a b hab hh
  rw [Bool.and_eq_true] at hh ⊢
  exact ⟨hf.2 a b hab hh.1, hg.2 a b hab hh.2⟩

lemma LinearNoise.wire_noise {n k : Nat} {D : Dag} (hS : Strict n D) (birth : Fin k → Nat)
    (hzero : ∀ j, j < D.length → tag D j = true → supp n D (n+j) = ∅)
    (hkind : ∀ j, j < D.length → tag D j = true →
      (∃ i, birth i = j) ∨ (supp n D (opA D j) = ∅ ∧ supp n D (opB D j) = ∅)) :
    ∀ w, w < n + D.length → ∃ f : (Fin k → Bool) → Bool,
      ZeroMono f ∧ UsesAtMost n birth w f ∧
      ∀ x : Fin n → Bool, val D x w =
        (linear (supp n D w) x || f (fun i => val D x (n + birth i))) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hin : w < n
    · refine ⟨fun _ => false, ⟨rfl, ?_⟩, ?_, ?_⟩
      · intro a b hab hh
        exact hh
      · intro a b hab
        rfl
      · intro x
        rw [show supp n D w = {⟨w,hin⟩} from supp_input D ⟨w,hin⟩,
          linear_singleton, val_input D x w hin]
        simp
    · obtain ⟨j,rfl⟩ : ∃ j, w = n+j := ⟨w-n,by omega⟩
      have hj : j < D.length := by omega
      obtain ⟨ha,hb,_⟩ := hS j hj
      by_cases ht : tag D j = true
      · rcases hkind j hj ht with ⟨i,hi⟩ | ⟨hza,hzb⟩
        · refine ⟨fun z => z i, ⟨rfl, fun a b hab hh => hab i hh⟩, ?_, ?_⟩
          · intro a b hab
            exact hab i (by omega)
          · intro x
            rw [hzero j hj ht, linear_empty, Bool.false_or]
            dsimp only
            rw [hi]
        · obtain ⟨f,hf,hu,hvf⟩ := ih _ ha (by omega)
          obtain ⟨g,hg,hv,hvg⟩ := ih _ hb (by omega)
          refine ⟨fun z => f z && g z, zeroMono_and hf hg, ?_, ?_⟩
          · intro a b hab
            dsimp only
            rw [uses_mono hu ha.le a b hab, uses_mono hv hb.le a b hab]
          · intro x
            rw [val_gate hS x j hj, ht, gop_true, hvf x, hvg x,
              hza, hzb, hzero j hj ht, linear_empty]
            simp
      · have ht0 : tag D j = false := Bool.eq_false_of_not_eq_true ht
        obtain ⟨f,hf,hu,hvf⟩ := ih _ ha (by omega)
        obtain ⟨g,hg,hv,hvg⟩ := ih _ hb (by omega)
        refine ⟨fun z => f z || g z, zeroMono_or hf hg, ?_, ?_⟩
        · intro a b hab
          dsimp only
          rw [uses_mono hu ha.le a b hab, uses_mono hv hb.le a b hab]
        · intro x
          rw [val_gate hS x j hj, ht0, gop_false, hvf x, hvg x,
            sem_supp_or hS hj ht0, linear_union]
          dsimp only
          ac_rfl

end packScope9


section packScope10

open PEqualNP.Outside.L_meta_2590_aux.LinearNoise
open PEqualNP.Outside.L_meta_2590_aux.C6.ThreeBirth

lemma BirthNoiseProjection.uses_before {n w : Nat} {birth : Fin 3 → Nat}
    {f : (Fin 3 → Bool) → Bool} (hb : StrictMono birth)
    (hf : UsesAtMost n birth w f) (i : Fin 3) (hw : w < n + birth i)
    (a b : Fin 3 → Bool) (hab : ∀ j, j < i → a j = b j) : f a = f b := by
  apply hf a b
  intro j hj
  apply hab j
  by_contra hji
  have hbirth := hb.monotone (le_of_not_gt hji)
  omega

open PEqualNP.Outside.L_meta_2590_aux.BirthNoiseProjection

lemma BirthNoiseProjection.uses_before_zero {n w : Nat} {birth : Fin 3 → Nat}
    {f : (Fin 3 → Bool) → Bool} (hb : StrictMono birth)
    (hf : UsesAtMost n birth w f) (hw : w < n + birth 0)
    (z : Fin 3 → Bool) : f z = f ![false, false, false] := by
  apply uses_before hb hf 0 hw z ![false, false, false]
  intro j hj
  exact False.elim (by omega)

lemma BirthNoiseProjection.uses_before_one {n w : Nat} {birth : Fin 3 → Nat}
    {f : (Fin 3 → Bool) → Bool} (hb : StrictMono birth)
    (hf : UsesAtMost n birth w f) (hw : w < n + birth 1)
    (z : Fin 3 → Bool) : f z = f ![z 0, false, false] := by
  apply uses_before hb hf 1 hw z ![z 0, false, false]
  intro j hj
  have hj0 : j = 0 := by omega
  subst j
  rfl

lemma BirthNoiseProjection.uses_before_two {n w : Nat} {birth : Fin 3 → Nat}
    {f : (Fin 3 → Bool) → Bool} (hb : StrictMono birth)
    (hf : UsesAtMost n birth w f) (hw : w < n + birth 2)
    (z : Fin 3 → Bool) : f z = f ![z 0, z 1, false] := by
  apply uses_before hb hf 2 hw z ![z 0, z 1, false]
  intro j hj
  have hj01 : j = 0 ∨ j = 1 := by omega
  rcases hj01 with rfl | rfl <;> rfl

lemma BirthNoiseProjection.zeroMono_restrict_one {f : (Fin 3 → Bool) → Bool} (hf : ZeroMono f) :
    Mono1 (fun a => f ![a, false, false]) ∧ f ![false, false, false] = false := by
  refine ⟨?_, ?_⟩
  · intro a b hab ha
    apply hf.2 ![a, false, false] ![b, false, false] _ ha
    intro i hi
    fin_cases i
    · exact hab hi
    · simp at hi
    · simp at hi
  · have he : (![false, false, false] : Fin 3 → Bool) = (fun _ => false) := by
      funext i
      fin_cases i <;> rfl
    rw [he]
    exact hf.1

lemma BirthNoiseProjection.zeroMono_restrict_two {f : (Fin 3 → Bool) → Bool} (hf : ZeroMono f) :
    Mono2 (fun a b => f ![a, b, false]) ∧ f ![false, false, false] = false := by
  refine ⟨?_, (zeroMono_restrict_one hf).2⟩
  intro a b c d hac hbd hab
  apply hf.2 ![a, b, false] ![c, d, false] _ hab
  intro i hi
  fin_cases i
  · exact hac hi
  · exact hbd hi
  · simp at hi

lemma BirthNoiseProjection.zero_before_zero {n w : Nat} {birth : Fin 3 → Nat}
    {f : (Fin 3 → Bool) → Bool} (hb : StrictMono birth)
    (hf : UsesAtMost n birth w f) (hm : ZeroMono f) (hw : w < n + birth 0)
    (z : Fin 3 → Bool) : f z = false := by
  rw [uses_before_zero hb hf hw z]
  exact (zeroMono_restrict_one hm).2

end packScope10


section packScope11

lemma BirthOrder.strictMono_three (f : Fin 3 → Nat) (h01 : f 0 < f 1) (h12 : f 1 < f 2) :
    StrictMono f := by
  have h02 := lt_trans h01 h12
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

open PEqualNP.Outside.L_meta_2590_aux.BirthOrder

lemma BirthOrder.sort_three (G : Fin 3 → Nat) (hG : Function.Injective G) :
    ∃ σ : Fin 3 → Fin 3, Function.Bijective σ ∧ StrictMono (G ∘ σ) := by
  have hne01 : G 0 ≠ G 1 := by
    intro h
    have := hG h
    omega
  have hne02 : G 0 ≠ G 2 := by
    intro h
    have := hG h
    omega
  have hne12 : G 1 ≠ G 2 := by
    intro h
    have := hG h
    omega
  by_cases h01 : G 0 < G 1
  · by_cases h12 : G 1 < G 2
    · refine ⟨![0, 1, 2], by decide, ?_⟩
      exact strictMono_three _ h01 h12
    · by_cases h02 : G 0 < G 2
      · refine ⟨![0, 2, 1], by decide, ?_⟩
        apply strictMono_three
        · exact h02
        · change G 2 < G 1
          omega
      · refine ⟨![2, 0, 1], by decide, ?_⟩
        apply strictMono_three
        · change G 2 < G 0
          omega
        · exact h01
  · by_cases h02 : G 0 < G 2
    · refine ⟨![1, 0, 2], by decide, ?_⟩
      apply strictMono_three
      · change G 1 < G 0
        omega
      · exact h02
    · by_cases h12 : G 1 < G 2
      · refine ⟨![1, 2, 0], by decide, ?_⟩
        apply strictMono_three
        · exact h12
        · change G 2 < G 0
          omega
      · refine ⟨![2, 1, 0], by decide, ?_⟩
        apply strictMono_three
        · change G 2 < G 1
          omega
        · change G 1 < G 0
          omega

end packScope11


section packScope12

open PEqualNP.Outside.L_meta_2590_aux.C6 PEqualNP.Outside.L_meta_2590_aux.H2 PEqualNP.Outside.L_meta_2590_aux.C6.ThreeBirth PEqualNP.Outside.L_meta_2590_aux.LinearNoise PEqualNP.Outside.L_meta_2590_aux.BirthNoiseProjection

lemma BirthNoiseAdapter.no_sorted_three_births {D : Dag} (hD : Strict 6 D)
    (birth L R : Fin 3 → Nat) (hb : StrictMono birth)
    (hbvalid : ∀ i, birth i < D.length)
    (σ : Fin 3 → Fin 3) (hσ : Function.Bijective σ)
    (hL : ∀ i, L i < 6 + birth i) (hR : ∀ i, R i < 6 + birth i)
    (hgate : ∀ i (x : C6.V → Bool), val D x (6 + birth i) =
      (val D x (L i) && val D x (R i)))
    (hlinL : ∀ i (x : C6.V → Bool), linear (supp 6 D (L i)) x = (factors (σ i) x).1)
    (hlinR : ∀ i (x : C6.V → Bool), linear (supp 6 D (R i)) x = (factors (σ i) x).2)
    (hzero : ∀ j, j < D.length → tag D j = true → supp 6 D (6 + j) = ∅)
    (hkind : ∀ j, j < D.length → tag D j = true →
      (∃ i, birth i = j) ∨ (supp 6 D (opA D j) = ∅ ∧ supp 6 D (opB D j) = ∅))
    (out : Nat) (hout : out < 6 + D.length) (hsout : supp 6 D out = ∅)
    (hcorrect : ∀ x : C6.V → Bool, val D x out = edgeBool x) : False := by
  classical
  have hLn : ∀ i, ∃ f : (Fin 3 → Bool) → Bool,
      ZeroMono f ∧ UsesAtMost 6 birth (L i) f ∧
      ∀ x : C6.V → Bool, val D x (L i) =
        (linear (supp 6 D (L i)) x || f (fun j => val D x (6 + birth j))) := by
    intro i
    exact wire_noise hD birth hzero hkind (L i) (by have := hL i; have := hbvalid i; omega)
  have hRn : ∀ i, ∃ f : (Fin 3 → Bool) → Bool,
      ZeroMono f ∧ UsesAtMost 6 birth (R i) f ∧
      ∀ x : C6.V → Bool, val D x (R i) =
        (linear (supp 6 D (R i)) x || f (fun j => val D x (6 + birth j))) := by
    intro i
    exact wire_noise hD birth hzero hkind (R i) (by have := hR i; have := hbvalid i; omega)
  choose lf hlz hlu hle using hLn
  choose rf hrz hru hre using hRn
  let B (x : C6.V → Bool) (i : Fin 3) := val D x (6 + birth i)
  let p (a : Bool) := lf 1 ![a, false, false]
  let q (a : Bool) := rf 1 ![a, false, false]
  let r (a b : Bool) := lf 2 ![a, b, false]
  let s (a b : Bool) := rf 2 ![a, b, false]
  have h0 (x : C6.V → Bool) : B x 0 =
      ((factors (σ 0) x).1 && (factors (σ 0) x).2) := by
    dsimp only [B]
    rw [hgate, hle, hre, hlinL, hlinR,
      zero_before_zero hb (hlu 0) (hlz 0) (hL 0),
      zero_before_zero hb (hru 0) (hrz 0) (hR 0)]
    simp only [Bool.or_false]
  have h1 (x : C6.V → Bool) : B x 1 =
      (((factors (σ 1) x).1 || p (B x 0)) &&
        ((factors (σ 1) x).2 || q (B x 0))) := by
    dsimp only [B, p, q]
    rw [hgate, hle, hre, hlinL, hlinR,
      uses_before_one hb (hlu 1) (hL 1), uses_before_one hb (hru 1) (hR 1)]
  have h2 (x : C6.V → Bool) : B x 2 =
      (((factors (σ 2) x).1 || r (B x 0) (B x 1)) &&
        ((factors (σ 2) x).2 || s (B x 0) (B x 1))) := by
    dsimp only [B, r, s]
    rw [hgate, hle, hre, hlinL, hlinR,
      uses_before_two hb (hlu 2) (hL 2), uses_before_two hb (hru 2) (hR 2)]
  have hB (x : C6.V → Bool) : B x = generalBirths σ p q r s x := by
    funext i
    fin_cases i
    · simpa [generalBirths] using h0 x
    · simpa [generalBirths, h0] using h1 x
    · simpa [generalBirths, h1, h0] using h2 x
  obtain ⟨F, hFz, hFu, hFe⟩ := wire_noise hD birth hzero hkind out hout
  apply no_general_combiner σ hσ p q r s
    (zeroMono_restrict_one (hlz 1)).1 (zeroMono_restrict_one (hlz 1)).2
    (zeroMono_restrict_one (hrz 1)).1 (zeroMono_restrict_one (hrz 1)).2
    (zeroMono_restrict_two (hlz 2)).1 (zeroMono_restrict_two (hlz 2)).2
    (zeroMono_restrict_two (hrz 2)).1 (zeroMono_restrict_two (hrz 2)).2 F hFz.2
  intro x
  rw [← hB x]
  have he := hFe x
  rw [hsout, linear_empty, Bool.false_or] at he
  exact he.symm.trans (hcorrect x)

open PEqualNP.Outside.L_meta_2590_aux.BirthNoiseAdapter

lemma BirthNoiseAdapter.no_three_births {D : Dag} (hD : Strict 6 D)
    (G L R : Fin 3 → Nat) (hG : Function.Injective G)
    (hGvalid : ∀ i, G i < D.length)
    (hL : ∀ i, L i < 6 + G i) (hR : ∀ i, R i < 6 + G i)
    (hgate : ∀ i (x : C6.V → Bool), val D x (6 + G i) =
      (val D x (L i) && val D x (R i)))
    (hlinL : ∀ i (x : C6.V → Bool), linear (supp 6 D (L i)) x = (factors i x).1)
    (hlinR : ∀ i (x : C6.V → Bool), linear (supp 6 D (R i)) x = (factors i x).2)
    (hzero : ∀ j, j < D.length → tag D j = true → supp 6 D (6 + j) = ∅)
    (hother : ∀ j, j < D.length → tag D j = true → (∀ i, j ≠ G i) →
      supp 6 D (opA D j) = ∅ ∧ supp 6 D (opB D j) = ∅)
    (out : Nat) (hout : out < 6 + D.length) (hsout : supp 6 D out = ∅)
    (hcorrect : ∀ x : C6.V → Bool, val D x out = edgeBool x) : False := by
  classical
  obtain ⟨σ, hσ, hs⟩ := BirthOrder.sort_three G hG
  apply no_sorted_three_births hD (G ∘ σ) (L ∘ σ) (R ∘ σ) hs
    (fun i => hGvalid (σ i)) σ hσ (fun i => hL (σ i)) (fun i => hR (σ i))
    (fun i => hgate (σ i)) (fun i => hlinL (σ i)) (fun i => hlinR (σ i))
    hzero ?_ out hout hsout hcorrect
  intro j hj ht
  by_cases he : ∃ i, G i = j
  · obtain ⟨i, hi⟩ := he
    obtain ⟨k, hk⟩ := hσ.2 i
    exact Or.inl ⟨k, by simpa only [Function.comp_apply, hk] using hi⟩
  · apply Or.inr
    apply hother j hj ht
    intro i hi
    exact he ⟨i, hi.symm⟩

end packScope12


section packScope13
open PEqualNP.Outside.L_meta_2590_aux.C6

open PEqualNP.Outside.L_meta_2590_aux.H2 PEqualNP.Outside.L_meta_2590_aux.LinearNoise

lemma C6.linear_pair (a b : V) (x : V → Bool) : linear {a, b} x = (x a || x b) := by
  have hs : ({a, b} : Finset V) = {a} ∪ {b} := by ext v; simp
  rw [hs, linear_union, linear_singleton, linear_singleton]

lemma C6.and_value_on_slots {D : Dag} (hS : Strict 6 D) (e : ℕ × Bool)
    (hj : e.1 < D.length) (ht : tag D e.1 = true) (x : V → Bool) :
    val D x (6 + e.1) =
      (val D x (src D e) && val D x (src D (sem_bar e))) := by
  rw [val_gate hS x e.1 hj, ht, gop_true]
  obtain ⟨j, s⟩ := e
  cases s <;> simp [src, sem_bar, Bool.and_comm]

end packScope13


section packScope14
open PEqualNP.Outside.L_meta_2590_aux.C6

open PEqualNP.Outside.L_meta_2590_aux.H2

lemma C6.c6_Bplus_ge_three {D : Dag} (h : StrictLive 6 D) (hc : sem_Comp 6 adj D) :
    3 ≤ Bplus 6 D := by
  obtain ⟨b, hb⟩ := sem_exists_pureBranch graph_ok h.1 hc
  have hi := (independent_facts _ (inelig_independent h hc)).1
  have he := elig_le_Bplus h.1 b hb
  have hn := inelig_card_add 6 D
  omega

lemma C6.c6_length_ge_eight_add_Bzero {D : Dag} (h : StrictLive 6 D)
    (hc : sem_Comp 6 adj D) : 8 + Bzero 6 D ≤ D.length := by
  have hp := c6_Bplus_ge_three h hc
  have hs := surplus_identity h
  rw [totalSurplus_split] at hs
  omega

end packScope14


section packScope15
open PEqualNP.Outside.L_meta_2590_aux.H2

lemma C6.GenericPair.bf_budget {D : Dag} (h : StrictLive 6 D)
    (hc : sem_Comp 6 adj D) (hE : fourEndpoints ⊆ eligSet 6 D) (hb4 : Bplus 6 D = 4) :
    ∃ b : V → ℕ, PureBranch 6 D b ∧
      eligSet 6 D = fourEndpoints ∧
      residualUnits 6 D b = ∅ := by
  classical
  obtain ⟨b, hb⟩ := sem_exists_pureBranch graph_ok h.1 hc
  have hsub : fourEndpoints ⊆ eligSet 6 D := hE
  have hfour : fourEndpoints.card = 4 := by decide
  have hbound := elig_le_Bplus h.1 b hb
  have heq : eligSet 6 D = fourEndpoints :=
    (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
  have hr := card_residual h.1 b hb
  rw [heq, hfour, hb4] at hr
  exact ⟨b, hb, heq, Finset.card_eq_zero.mp (by omega)⟩

open PEqualNP.Outside.L_meta_2590_aux.C6.GenericPair

lemma C6.GenericPair.bf_inelig {D : Dag} (h : StrictLive 6 D)
    (hc : sem_Comp 6 adj D) (hE : fourEndpoints ⊆ eligSet 6 D) (hb4 : Bplus 6 D = 4) :
    ineligSet 6 D = {2, 3} := by
  classical
  obtain ⟨_, _, heq, _⟩ := bf_budget h hc hE hb4
  ext v
  rw [sem_mem_inelig, heq]
  fin_cases v <;> decide

lemma C6.GenericPair.bf_flow {D : Dag} (h : StrictLive 6 D)
    (hc : sem_Comp 6 adj D) (hE : fourEndpoints ⊆ eligSet 6 D) (hb4 : Bplus 6 D = 4)
    (v : V) :
    (sem_W 6 D v).card +
      (merges 6 D (carrierT 6 D {v})).card =
      1 + if v ∈ fourEndpoints then 1 else 0 := by
  classical
  obtain ⟨b, hb, heq, hr⟩ := bf_budget h hc hE hb4
  have hf := sem_code_count graph_ok h hc b hb v
  rw [hr, heq] at hf
  by_cases hv : v ∈ fourEndpoints <;> simpa [hv] using hf

lemma C6.GenericPair.consumer_two_exits {D : Dag} (h : StrictLive 6 D) (hc : sem_Comp 6 adj D)
    {z v u : V} {e : ℕ × Bool} (he : Consumer D z e)
    (hvz : adj z v) (hvu : adj v u) (huz : u ≠ z) :
    2 ≤ (sem_W 6 D v).card := by
  classical
  have hve : sem_bar e ∈ sem_W 6 D v := by
    apply sem_mem_W.mpr
    refine ⟨he.1, he.2.2.2.2.1 v hvz, ?_⟩
    change v ∉ supp 6 D (6 + e.1)
    rw [he.2.2.2.1]
    exact Finset.notMem_empty _
  obtain ⟨f, hfv, hfu, _⟩ := sem_edge_slots graph_ok h.1 hc hvu
  have hne : f ≠ sem_bar e := by
    intro hf
    have hu := (sem_mem_W.mp hfu).2.1
    rw [hf, sem_bar_bar, he.2.2.1, Finset.mem_singleton] at hu
    exact huz hu
  have hs : {sem_bar e, f} ⊆ sem_W 6 D v := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact hve
    · exact hfv
  have hc2 := Finset.card_le_card hs
  simpa [Ne.symm hne] using hc2

lemma C6.GenericPair.bf_endpoint_exits {D : Dag} (h : StrictLive 6 D)
    (hc : sem_Comp 6 adj D) (hE : fourEndpoints ⊆ eligSet 6 D) (hb4 : Bplus 6 D = 4)
    {v : V} (hv : v ∈ fourEndpoints) : 2 ≤ (sem_W 6 D v).card := by
  have hi := bf_inelig h hc hE hb4
  obtain ⟨ec, hec⟩ := consumer_exists h hc (v := (2 : V)) (by rw [hi]; decide)
  obtain ⟨ed, hed⟩ := consumer_exists h hc (v := (3 : V)) (by rw [hi]; decide)
  simp only [fourEndpoints, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl
  · exact consumer_two_exits h hc hed (v := 0) (u := 4)
      (by unfold adj; decide) (by unfold adj; decide) (by decide)
  · exact consumer_two_exits h hc hed (v := 1) (u := 5)
      (by unfold adj; decide) (by unfold adj; decide) (by decide)
  · exact consumer_two_exits h hc hec (v := 4) (u := 0)
      (by unfold adj; decide) (by unfold adj; decide) (by decide)
  · exact consumer_two_exits h hc hec (v := 5) (u := 1)
      (by unfold adj; decide) (by unfold adj; decide) (by decide)

lemma C6.GenericPair.bf_merges_empty {D : Dag} (h : StrictLive 6 D)
    (hc : sem_Comp 6 adj D) (hE : fourEndpoints ⊆ eligSet 6 D) (hb4 : Bplus 6 D = 4)
    (v : V) : merges 6 D (carrierT 6 D {v}) = ∅ := by
  classical
  by_cases hv : v ∈ fourEndpoints
  · have hf := bf_flow h hc hE hb4 v
    have he := bf_endpoint_exits h hc hE hb4 hv
    simp only [hv, ↓reduceIte] at hf
    exact Finset.card_eq_zero.mp (by omega)
  · obtain ⟨_, _, heq, _⟩ := bf_budget h hc hE hb4
    have hi : v ∈ ineligSet 6 D := sem_mem_inelig.mpr (by rwa [heq])
    obtain ⟨_, _, _, _, _, _, _, hm⟩ := sem_inelig_consumer graph_ok h hc hi
    exact hm

lemma C6.GenericPair.bf_and_empty {D : Dag} (h : StrictLive 6 D)
    (hc : sem_Comp 6 adj D) (hE : fourEndpoints ⊆ eligSet 6 D) (hb4 : Bplus 6 D = 4)
    {j : ℕ} (hj : j < D.length) (ht : tag D j = true) :
    supp 6 D (6 + j) = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro v hv
  have hg := sem_zm_gate h.1 (bf_merges_empty h hc hE hb4 v) hj hv
  rw [ht] at hg
  exact Bool.noConfusion hg.1

lemma C6.GenericPair.bf_exits_le_two {D : Dag} (h : StrictLive 6 D)
    (hc : sem_Comp 6 adj D) (hE : fourEndpoints ⊆ eligSet 6 D) (hb4 : Bplus 6 D = 4)
    (v : V) : (sem_W 6 D v).card ≤ 2 := by
  have hf := bf_flow h hc hE hb4 v
  split_ifs at hf <;> omega

lemma C6.GenericPair.consumer_other_exit {D : Dag} {z v : V} {e : ℕ × Bool}
    (he : Consumer D z e) (hv : v ∈ supp 6 D (src D (sem_bar e))) :
    sem_bar e ∈ sem_W 6 D v := by
  apply sem_mem_W.mpr
  refine ⟨he.1, hv, ?_⟩
  change v ∉ supp 6 D (6 + e.1)
  rw [he.2.2.2.1]
  exact Finset.notMem_empty _

lemma C6.GenericPair.joint_not_consumer {D : Dag} {v u z : V} {f e : ℕ × Bool}
    (hfv : f ∈ sem_W 6 D v) (hfu : sem_bar f ∈ sem_W 6 D u)
    (he : Consumer D z e) (hvz : v ≠ z) (huz : u ≠ z) : f.1 ≠ e.1 := by
  intro hgate
  rcases sem_same_gate hgate.symm with hf | hf
  · have hv := (sem_mem_W.mp hfv).2.1
    rw [hf, he.2.2.1, Finset.mem_singleton] at hv
    exact hvz hv
  · have hu := (sem_mem_W.mp hfu).2.1
    rw [hf, sem_bar_bar, he.2.2.1, Finset.mem_singleton] at hu
    exact huz hu

lemma C6.GenericPair.consumer_extra_impossible {D : Dag} (h : StrictLive 6 D) (hc : sem_Comp 6 adj D)
    {z w v u : V} {ec ed : ℕ × Bool} (hec : Consumer D z ec) (hed : Consumer D w ed)
    (hzw : z ≠ w) (hvz : v ≠ z) (huz : u ≠ z) (hvw' : v ≠ w) (huw : u ≠ w)
    (hvw : adj w v) (hvu : adj v u)
    (hv : v ∈ supp 6 D (src D (sem_bar ec)))
    (hle : (sem_W 6 D v).card ≤ 2) : False := by
  classical
  have hce := consumer_other_exit hec hv
  have hde := consumer_other_exit hed (hed.2.2.2.2.1 v hvw)
  obtain ⟨f, hfv, hfu, _⟩ := sem_edge_slots graph_ok h.1 hc hvu
  have hcf := joint_not_consumer hfv hfu hec hvz huz
  have hdf := joint_not_consumer hfv hfu hed hvw' huw
  have hcd : sem_bar ec ≠ sem_bar ed := by
    intro he
    have hg : ec.1 = ed.1 := by
      simpa only [sem_bar] using congrArg (fun q : ℕ × Bool => q.1) he
    exact hzw (consumers_injective hec hed hg)
  have hcfn : sem_bar ec ≠ f := by
    intro he
    exact hcf (congrArg Prod.fst he).symm
  have hdfn : sem_bar ed ≠ f := by
    intro he
    exact hdf (congrArg Prod.fst he).symm
  have hs : {sem_bar ec, sem_bar ed, f} ⊆ sem_W 6 D v := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl
    · exact hce
    · exact hde
    · exact hfv
  have hcard := Finset.card_le_card hs
  have hthree : ({sem_bar ec, sem_bar ed, f} : Finset (ℕ × Bool)).card = 3 := by
    simp [hcd, hcfn, hdfn]
  rw [hthree] at hcard
  omega

lemma C6.GenericPair.consumer_own_not_other {D : Dag} {z : V} {e : ℕ × Bool}
    (he : Consumer D z e) : z ∉ supp 6 D (src D (sem_bar e)) := by
  intro hz
  have hm := consumer_other_exit he hz
  rw [he.2.2.2.2.2, Finset.mem_singleton] at hm
  exact (sem_bar_ne e) hm

lemma C6.GenericPair.consumer_other_inelig_not {D : Dag} {z w : V} {ec ed : ℕ × Bool}
    (hec : Consumer D z ec) (hed : Consumer D w ed) (hne : z ≠ w) :
    w ∉ supp 6 D (src D (sem_bar ec)) := by
  intro hw
  have hm := consumer_other_exit hec hw
  rw [hed.2.2.2.2.2, Finset.mem_singleton] at hm
  have hg : ec.1 = ed.1 := by
    simpa only [sem_bar] using congrArg (fun q : ℕ × Bool => q.1) hm
  exact hne (consumers_injective hec hed hg)

lemma C6.GenericPair.bf_C_opposite {D : Dag} (h : StrictLive 6 D)
    (hc : sem_Comp 6 adj D) (hE : fourEndpoints ⊆ eligSet 6 D) (hb4 : Bplus 6 D = 4)
    {ec ed : ℕ × Bool} (hec : Consumer D 2 ec)
    (hed : Consumer D 3 ed) :
    supp 6 D (src D (sem_bar ec)) = {4, 5} := by
  classical
  apply Finset.Subset.antisymm
  · intro v hv
    fin_cases v
    · exact (consumer_extra_impossible h hc hec hed (u := 4)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by unfold adj; decide) (by unfold adj; decide) hv
        (bf_exits_le_two h hc hE hb4 0)).elim
    · exact (consumer_extra_impossible h hc hec hed (u := 5)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by unfold adj; decide) (by unfold adj; decide) hv
        (bf_exits_le_two h hc hE hb4 1)).elim
    · exact (consumer_own_not_other hec hv).elim
    · exact (consumer_other_inelig_not hec hed (by decide) hv).elim
    · decide
    · decide
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact hec.2.2.2.2.1 4 (by unfold adj; decide)
    · exact hec.2.2.2.2.1 5 (by unfold adj; decide)

lemma C6.GenericPair.bf_D_opposite {D : Dag} (h : StrictLive 6 D)
    (hc : sem_Comp 6 adj D) (hE : fourEndpoints ⊆ eligSet 6 D) (hb4 : Bplus 6 D = 4)
    {ec ed : ℕ × Bool} (hec : Consumer D 2 ec)
    (hed : Consumer D 3 ed) :
    supp 6 D (src D (sem_bar ed)) = {0, 1} := by
  classical
  apply Finset.Subset.antisymm
  · intro v hv
    fin_cases v
    · decide
    · decide
    · exact (consumer_other_inelig_not hed hec (by decide) hv).elim
    · exact (consumer_own_not_other hed hv).elim
    · exact (consumer_extra_impossible h hc hed hec (u := 0)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by unfold adj; decide) (by unfold adj; decide) hv
        (bf_exits_le_two h hc hE hb4 4)).elim
    · exact (consumer_extra_impossible h hc hed hec (u := 1)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by unfold adj; decide) (by unfold adj; decide) hv
        (bf_exits_le_two h hc hE hb4 5)).elim
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact hed.2.2.2.2.1 0 (by unfold adj; decide)
    · exact hed.2.2.2.2.1 1 (by unfold adj; decide)

lemma C6.GenericPair.joint_support_eligible {D : Dag} (h : StrictLive 6 D) (hc : sem_Comp 6 adj D)
    {u v : V} (hne : u ≠ v) {w : ℕ}
    (hu : u ∈ supp 6 D w) (hv : v ∈ supp 6 D w) :
    u ∈ eligSet 6 D ∧ v ∈ eligSet 6 D := by
  classical
  constructor
  · by_contra hue
    have hi : u ∈ ineligSet 6 D := sem_mem_inelig.mpr hue
    have hs := sem_inelig_pure graph_ok h.1 hc hi hu
    rw [hs, Finset.mem_singleton] at hv
    exact hne hv.symm
  · by_contra hve
    have hi : v ∈ ineligSet 6 D := sem_mem_inelig.mpr hve
    have hs := sem_inelig_pure graph_ok h.1 hc hi hv
    rw [hs, Finset.mem_singleton] at hu
    exact hne hu

end packScope15


section packScope16
open PEqualNP.Outside.L_meta_2590_aux.C6.GenericPair

open PEqualNP.Outside.L_meta_2590_aux.H2

lemma C6.GenericPair.common_exit_of_joint_support {D : Dag} (h : StrictLive 6 D)
    (hc : sem_Comp 6 adj D)
    (ha : ∀ j, j < D.length → tag D j = true → supp 6 D (6 + j) = ∅)
    (u v : V) {w : ℕ} (hu : u ∈ supp 6 D w) (hv : v ∈ supp 6 D w) :
    ∃ e, e ∈ sem_W 6 D u ∧ e ∈ sem_W 6 D v := by
  classical
  let S := (Finset.range (6 + D.length)).filter
    (fun a => u ∈ supp 6 D a ∧ v ∈ supp 6 D a)
  have hS : S.Nonempty := ⟨w, Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (sem_supp_lt hu), hu, hv⟩⟩
  let a := S.max' hS
  have haS : a ∈ S := Finset.max'_mem S hS
  obtain ⟨halt, hau, hav⟩ := Finset.mem_filter.mp haS
  have halt' := Finset.mem_range.mp halt
  have hne : a ≠ outW 6 D := by
    intro he
    rw [he, sem_supp_out graph_ok hc] at hau
    exact Finset.notMem_empty _ hau
  have hinner : a + 1 < 6 + D.length := by unfold outW at hne; omega
  have hf := h.2.1 a hinner
  obtain ⟨j, hj⟩ := Finset.card_pos.mp (show 0 < (readers D a).card by change 0 < fanout D a; omega)
  obtain ⟨hj, hr⟩ := Finset.mem_filter.mp hj
  have hj' := Finset.mem_range.mp hj
  have ht : tag D j = true := by
    by_contra ht
    have ht' : tag D j = false := by cases htag : tag D j <;> simp_all
    have hp : 6 + j ∈ S := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
      rw [sem_supp_or h.1 hj' ht']
      rcases hr with hr | hr
      · rw [hr]
        exact ⟨Finset.mem_union_left _ hau, Finset.mem_union_left _ hav⟩
      · rw [hr]
        exact ⟨Finset.mem_union_right _ hau, Finset.mem_union_right _ hav⟩
    have hle : 6 + j ≤ a := Finset.le_max' S _ hp
    have hs := h.1 j hj'
    rcases hr with hr | hr <;> omega
  have hout := ha j hj' ht
  rcases hr with hr | hr
  · refine ⟨(j, false), sem_mem_W.mpr ?_, sem_mem_W.mpr ?_⟩
    · refine ⟨hj', ?_, ?_⟩
      · simpa [src, hr] using hau
      · rw [hout]; exact Finset.notMem_empty _
    · refine ⟨hj', ?_, ?_⟩
      · simpa [src, hr] using hav
      · rw [hout]; exact Finset.notMem_empty _
  · refine ⟨(j, true), sem_mem_W.mpr ?_, sem_mem_W.mpr ?_⟩
    · refine ⟨hj', ?_, ?_⟩
      · simpa [src, hr] using hau
      · rw [hout]; exact Finset.notMem_empty _
    · refine ⟨hj', ?_, ?_⟩
      · simpa [src, hr] using hav
      · rw [hout]; exact Finset.notMem_empty _

lemma C6.GenericPair.bf_common_AF {D : Dag} (h : StrictLive 6 D)
    (hc : sem_Comp 6 adj D) (hE : fourEndpoints ⊆ eligSet 6 D) (hb4 : Bplus 6 D = 4)
    (hAF : ∃ w, (0 : V) ∈ supp 6 D w ∧ (5 : V) ∈ supp 6 D w) :
    ∃ k, k ∈ sem_W 6 D 0 ∧ k ∈ sem_W 6 D 5 := by
  obtain ⟨w, hwa, hwf⟩ := hAF
  exact common_exit_of_joint_support h hc (fun j hj ht => bf_and_empty h hc hE hb4 hj ht)
    0 5 hwa hwf

lemma C6.GenericPair.two_exits_eq {D : Dag} {v : V} {e f : ℕ × Bool}
    (hle : (sem_W 6 D v).card ≤ 2) (he : e ∈ sem_W 6 D v)
    (hf : f ∈ sem_W 6 D v) (hne : e ≠ f) : sem_W 6 D v = {e, f} := by
  classical
  have hs : {e, f} ⊆ sem_W 6 D v := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl <;> assumption
  exact (Finset.eq_of_subset_of_card_le hs (by simpa [hne] using hle)).symm

lemma C6.GenericPair.slot_not_consumer {D : Dag} {v z : V} {k e : ℕ × Bool}
    (hk : k ∈ sem_W 6 D v) (he : Consumer D z e)
    (hvz : v ≠ z) (hopp : v ∉ supp 6 D (src D (sem_bar e))) : k.1 ≠ e.1 := by
  intro hg
  have hv := (sem_mem_W.mp hk).2.1
  rcases sem_same_gate hg.symm with hf | hf
  · rw [hf, he.2.2.1, Finset.mem_singleton] at hv
    exact hvz hv
  · rw [hf] at hv
    exact hopp hv

lemma C6.GenericPair.bf_AF_distinct {D : Dag} (h : StrictLive 6 D)
    (hc : sem_Comp 6 adj D) (hE : fourEndpoints ⊆ eligSet 6 D) (hb4 : Bplus 6 D = 4)
    {ec ed k : ℕ × Bool} (hec : Consumer D 2 ec)
    (hed : Consumer D 3 ed)
    (hka : k ∈ sem_W 6 D 0) (hkf : k ∈ sem_W 6 D 5) :
    k.1 ≠ ec.1 ∧ k.1 ≠ ed.1 := by
  constructor
  · apply slot_not_consumer hka hec (by decide)
    rw [bf_C_opposite h hc hE hb4 hec hed]
    decide
  · apply slot_not_consumer hkf hed (by decide)
    rw [bf_D_opposite h hc hE hb4 hec hed]
    decide

lemma C6.GenericPair.bf_cross_partners {D : Dag} (h : StrictLive 6 D)
    (hc : sem_Comp 6 adj D) (hE : fourEndpoints ⊆ eligSet 6 D) (hb4 : Bplus 6 D = 4)
    {ec ed k : ℕ × Bool} (hec : Consumer D 2 ec)
    (hed : Consumer D 3 ed)
    (hka : k ∈ sem_W 6 D 0) (hkf : k ∈ sem_W 6 D 5) :
    sem_bar k ∈ sem_W 6 D 1 ∧
      sem_bar k ∈ sem_W 6 D 4 := by
  have hd := bf_AF_distinct h hc hE hb4 hec hed hka hkf
  have heA := consumer_other_exit hed (hed.2.2.2.2.1 0 (by unfold adj; decide))
  have heF := consumer_other_exit hec (hec.2.2.2.2.1 5 (by unfold adj; decide))
  have hWA := two_exits_eq (bf_exits_le_two h hc hE hb4 0) heA hka
    (fun he => hd.2 (congrArg Prod.fst he).symm)
  have hWF := two_exits_eq (bf_exits_le_two h hc hE hb4 5) heF hkf
    (fun he => hd.1 (congrArg Prod.fst he).symm)
  constructor
  · obtain ⟨f, hff, hfb, _⟩ := sem_edge_slots graph_ok h.1 hc
      (x := (5 : V)) (y := (1 : V)) (by unfold adj; decide)
    rw [hWF, Finset.mem_insert, Finset.mem_singleton] at hff
    rcases hff with hf | rfl
    · have hb := (sem_mem_W.mp hfb).2.1
      rw [hf, sem_bar_bar, hec.2.2.1, Finset.mem_singleton] at hb
      exact (by decide : (1 : V) ≠ 2) hb |>.elim
    · exact hfb
  · obtain ⟨f, hfa, hfe, _⟩ := sem_edge_slots graph_ok h.1 hc
      (x := (0 : V)) (y := (4 : V)) (by unfold adj; decide)
    rw [hWA, Finset.mem_insert, Finset.mem_singleton] at hfa
    rcases hfa with hf | rfl
    · have he := (sem_mem_W.mp hfe).2.1
      rw [hf, sem_bar_bar, hed.2.2.1, Finset.mem_singleton] at he
      exact (by decide : (4 : V) ≠ 3) he |>.elim
    · exact hfe

lemma C6.GenericPair.exit_not_opposite {D : Dag} (hS : Strict 6 D) {v : V} {e : ℕ × Bool}
    (he : e ∈ sem_W 6 D v) : v ∉ supp 6 D (src D (sem_bar e)) := by
  have ht := sem_W_and hS he
  obtain ⟨hj, hv, hout⟩ := sem_mem_W.mp he
  intro hb
  apply hout
  rw [sem_supp_and hS hj ht]
  obtain ⟨j, s⟩ := e
  cases s
  · exact Finset.mem_inter.mpr ⟨by simpa [src] using hv, by simpa [src, sem_bar] using hb⟩
  · exact Finset.mem_inter.mpr ⟨by simpa [src, sem_bar] using hb, by simpa [src] using hv⟩

lemma C6.GenericPair.consumer_not_other_gate {D : Dag} {z : V} {e k : ℕ × Bool}
    (he : Consumer D z e) (hj : k.1 < D.length)
    (hempty : supp 6 D (6 + k.1) = ∅) (hne : k.1 ≠ e.1) :
    z ∉ supp 6 D (src D k) := by
  intro hz
  have hk : k ∈ sem_W 6 D z := sem_mem_W.mpr
    ⟨hj, hz, by rw [hempty]; exact Finset.notMem_empty _⟩
  rw [he.2.2.2.2.2, Finset.mem_singleton] at hk
  exact hne (congrArg Prod.fst hk)

lemma C6.GenericPair.bf_cross_supports {D : Dag} (h : StrictLive 6 D)
    (hc : sem_Comp 6 adj D) (hE : fourEndpoints ⊆ eligSet 6 D) (hb4 : Bplus 6 D = 4)
    {ec ed k : ℕ × Bool} (hec : Consumer D 2 ec)
    (hed : Consumer D 3 ed)
    (hka : k ∈ sem_W 6 D 0) (hkf : k ∈ sem_W 6 D 5) :
    supp 6 D (src D k) = {0, 5} ∧
      supp 6 D (src D (sem_bar k)) = {1, 4} := by
  classical
  obtain ⟨hkb, hke⟩ := bf_cross_partners h hc hE hb4 hec hed hka hkf
  obtain ⟨hkc, hkd⟩ := bf_AF_distinct h hc hE hb4 hec hed hka hkf
  have hj := (sem_mem_W.mp hka).1
  have hz := bf_and_empty h hc hE hb4 hj (sem_W_and h.1 hka)
  have hcnot := consumer_not_other_gate hec hj hz hkc
  have hdnot := consumer_not_other_gate hed hj hz hkd
  have hcnot' : (2 : V) ∉ supp 6 D (src D (sem_bar k)) :=
    consumer_not_other_gate hec hj hz hkc
  have hdnot' : (3 : V) ∉ supp 6 D (src D (sem_bar k)) :=
    consumer_not_other_gate hed hj hz hkd
  constructor
  · apply Finset.Subset.antisymm
    · intro v hv
      fin_cases v
      · decide
      · have hn := exit_not_opposite h.1 hkb
        rw [sem_bar_bar] at hn
        exact (hn hv).elim
      · exact (hcnot hv).elim
      · exact (hdnot hv).elim
      · have hn := exit_not_opposite h.1 hke
        rw [sem_bar_bar] at hn
        exact (hn hv).elim
      · decide
    · intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact (sem_mem_W.mp hka).2.1
      · exact (sem_mem_W.mp hkf).2.1
  · apply Finset.Subset.antisymm
    · intro v hv
      fin_cases v
      · exact (exit_not_opposite h.1 hka hv).elim
      · decide
      · exact (hcnot' hv).elim
      · exact (hdnot' hv).elim
      · decide
      · exact (exit_not_opposite h.1 hkf hv).elim
    · intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact (sem_mem_W.mp hkb).2.1
      · exact (sem_mem_W.mp hke).2.1

lemma C6.GenericPair.bf_three_exit_gates {D : Dag} (h : StrictLive 6 D)
    (hc : sem_Comp 6 adj D) (hE : fourEndpoints ⊆ eligSet 6 D) (hb4 : Bplus 6 D = 4)
    {ec ed k : ℕ × Bool} (hec : Consumer D 2 ec)
    (hed : Consumer D 3 ed)
    (hka : k ∈ sem_W 6 D 0) (hkf : k ∈ sem_W 6 D 5) :
    ∀ v : V, ∀ e ∈ sem_W 6 D v,
      e.1 = ec.1 ∨ e.1 = ed.1 ∨ e.1 = k.1 := by
  obtain ⟨hkb, hke⟩ := bf_cross_partners h hc hE hb4 hec hed hka hkf
  obtain ⟨hkc, hkd⟩ := bf_AF_distinct h hc hE hb4 hec hed hka hkf
  have hWA := two_exits_eq (bf_exits_le_two h hc hE hb4 0)
    (consumer_other_exit hed (hed.2.2.2.2.1 0 (by unfold adj; decide))) hka
    (fun he => hkd (congrArg Prod.fst he).symm)
  have hWB := two_exits_eq (bf_exits_le_two h hc hE hb4 1)
    (consumer_other_exit hed (hed.2.2.2.2.1 1 (by unfold adj; decide))) hkb
    (fun he => hkd (congrArg Prod.fst he).symm)
  have hWE := two_exits_eq (bf_exits_le_two h hc hE hb4 4)
    (consumer_other_exit hec (hec.2.2.2.2.1 4 (by unfold adj; decide))) hke
    (fun he => hkc (congrArg Prod.fst he).symm)
  have hWF := two_exits_eq (bf_exits_le_two h hc hE hb4 5)
    (consumer_other_exit hec (hec.2.2.2.2.1 5 (by unfold adj; decide))) hkf
    (fun he => hkc (congrArg Prod.fst he).symm)
  intro v e he
  fin_cases v
  · change e ∈ sem_W 6 D (0 : V) at he
    rw [hWA, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl <;> simp [sem_bar]
  · change e ∈ sem_W 6 D (1 : V) at he
    rw [hWB, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl <;> simp [sem_bar]
  · change e ∈ sem_W 6 D (2 : V) at he
    rw [hec.2.2.2.2.2, Finset.mem_singleton] at he
    subst e
    simp
  · change e ∈ sem_W 6 D (3 : V) at he
    rw [hed.2.2.2.2.2, Finset.mem_singleton] at he
    subst e
    simp
  · change e ∈ sem_W 6 D (4 : V) at he
    rw [hWE, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl <;> simp [sem_bar]
  · change e ∈ sem_W 6 D (5 : V) at he
    rw [hWF, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl <;> simp [sem_bar]

lemma C6.GenericPair.bf_other_and_inputs_empty {D : Dag} (h : StrictLive 6 D)
    (hc : sem_Comp 6 adj D) (hE : fourEndpoints ⊆ eligSet 6 D) (hb4 : Bplus 6 D = 4)
    {ec ed k : ℕ × Bool} (hec : Consumer D 2 ec)
    (hed : Consumer D 3 ed)
    (hka : k ∈ sem_W 6 D 0) (hkf : k ∈ sem_W 6 D 5)
    {j : ℕ} (hj : j < D.length) (ht : tag D j = true)
    (hjc : j ≠ ec.1) (hjd : j ≠ ed.1) (hjk : j ≠ k.1) :
    supp 6 D (opA D j) = ∅ ∧
      supp 6 D (opB D j) = ∅ := by
  have hs : ∀ s : Bool, supp 6 D (src D (j, s)) = ∅ := by
    intro s
    apply Finset.eq_empty_of_forall_notMem
    intro v hv
    have he : (j, s) ∈ sem_W 6 D v := sem_mem_W.mpr
      ⟨hj, hv, by rw [bf_and_empty h hc hE hb4 hj ht]; exact Finset.notMem_empty _⟩
    rcases bf_three_exit_gates h hc hE hb4 hec hed hka hkf v (j, s) he with he | he | he
    · exact hjc he
    · exact hjd he
    · exact hjk he
  exact ⟨by simpa [src] using hs false, by simpa [src] using hs true⟩

lemma C6.GenericPair.bf_three_birth_geometry {D : Dag} (h : StrictLive 6 D)
    (hc : sem_Comp 6 adj D) (hE : fourEndpoints ⊆ eligSet 6 D) (hb4 : Bplus 6 D = 4)
    (hAF : ∃ w, (0 : V) ∈ supp 6 D w ∧ (5 : V) ∈ supp 6 D w) :
    ∃ ec ed k : ℕ × Bool,
      Consumer D 2 ec ∧ Consumer D 3 ed ∧
      k.1 < D.length ∧ tag D k.1 = true ∧
      ec.1 ≠ ed.1 ∧ k.1 ≠ ec.1 ∧ k.1 ≠ ed.1 ∧
      supp 6 D (src D (sem_bar ec)) = {4, 5} ∧
      supp 6 D (src D (sem_bar ed)) = {0, 1} ∧
      supp 6 D (src D k) = {0, 5} ∧
      supp 6 D (src D (sem_bar k)) = {1, 4} ∧
      (∀ j, j < D.length → tag D j = true →
        j ≠ ec.1 → j ≠ ed.1 → j ≠ k.1 →
        supp 6 D (opA D j) = ∅ ∧
          supp 6 D (opB D j) = ∅) := by
  have hi := bf_inelig h hc hE hb4
  obtain ⟨ec, hec⟩ := consumer_exists h hc (v := (2 : V)) (by rw [hi]; decide)
  obtain ⟨ed, hed⟩ := consumer_exists h hc (v := (3 : V)) (by rw [hi]; decide)
  obtain ⟨k, hka, hkf⟩ := bf_common_AF h hc hE hb4 hAF
  obtain ⟨hkc, hkd⟩ := bf_AF_distinct h hc hE hb4 hec hed hka hkf
  obtain ⟨hkA, hkB⟩ := bf_cross_supports h hc hE hb4 hec hed hka hkf
  have hcd : ec.1 ≠ ed.1 := by
    intro hg
    exact (by decide : (2 : V) ≠ 3) (consumers_injective hec hed hg)
  exact ⟨ec, ed, k, hec, hed, (sem_mem_W.mp hka).1, sem_W_and h.1 hka,
    hcd, hkc, hkd, bf_C_opposite h hc hE hb4 hec hed, bf_D_opposite h hc hE hb4 hec hed,
    hkA, hkB, fun _ hj ht hjc hjd hjk =>
      bf_other_and_inputs_empty h hc hE hb4 hec hed hka hkf hj ht hjc hjd hjk⟩

end packScope16


section packScope17
open PEqualNP.Outside.L_meta_2590_aux.C6.GenericPair

open PEqualNP.Outside.L_meta_2590_aux.H2 PEqualNP.Outside.L_meta_2590_aux.LinearNoise

lemma C6.GenericPair.bf_birth_data {D : Dag} (h : StrictLive 6 D)
    (hc : sem_Comp 6 adj D) (hE : fourEndpoints ⊆ eligSet 6 D) (hb4 : Bplus 6 D = 4)
    (hAF : ∃ w, (0 : V) ∈ supp 6 D w ∧ (5 : V) ∈ supp 6 D w) :
    ∃ G L T : Fin 3 → ℕ,
      Function.Injective G ∧
      (∀ i, G i < D.length) ∧
      (∀ i, L i < 6 + G i ∧ T i < 6 + G i) ∧
      (∀ i (x : V → Bool), val D x (6 + G i) =
        (val D x (L i) && val D x (T i))) ∧
      (∀ i (x : V → Bool), linear (supp 6 D (L i)) x = (ThreeBirth.factors i x).1 ∧
        linear (supp 6 D (T i)) x = (ThreeBirth.factors i x).2) ∧
      (∀ j, j < D.length → tag D j = true →
        (∃ i, G i = j) ∨ (supp 6 D (opA D j) = ∅ ∧
          supp 6 D (opB D j) = ∅)) := by
  obtain ⟨ec, ed, k, hec, hed, hkj, hkt, hcd, hkc, hkd, hC, hD, hK, hK', hother⟩ :=
    bf_three_birth_geometry h hc hE hb4 hAF
  let G : Fin 3 → ℕ := ![ec.1, ed.1, k.1]
  let L : Fin 3 → ℕ := ![src D ec, src D ed, src D k]
  let T : Fin 3 → ℕ := ![src D (sem_bar ec),
    src D (sem_bar ed), src D (sem_bar k)]
  refine ⟨G, L, T, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [G]
  · intro i
    fin_cases i
    · exact hec.1
    · exact hed.1
    · exact hkj
  · intro i
    fin_cases i
    · exact ⟨sem_src_lt h.1 hec.1 ec.2, sem_src_lt h.1 hec.1 (!ec.2)⟩
    · exact ⟨sem_src_lt h.1 hed.1 ed.2, sem_src_lt h.1 hed.1 (!ed.2)⟩
    · exact ⟨sem_src_lt h.1 hkj k.2, sem_src_lt h.1 hkj (!k.2)⟩
  · intro i x
    fin_cases i
    · exact and_value_on_slots h.1 ec hec.1 hec.2.1 x
    · exact and_value_on_slots h.1 ed hed.1 hed.2.1 x
    · exact and_value_on_slots h.1 k hkj hkt x
  · intro i x
    fin_cases i
    · constructor
      · change linear (supp 6 D (src D ec)) x = x 2
        rw [hec.2.2.1, linear_singleton]
      · change linear (supp 6 D (src D (sem_bar ec))) x = (x 4 || x 5)
        rw [hC, linear_pair]
    · constructor
      · change linear (supp 6 D (src D ed)) x = x 3
        rw [hed.2.2.1, linear_singleton]
      · change linear (supp 6 D (src D (sem_bar ed))) x = (x 0 || x 1)
        rw [hD, linear_pair]
    · constructor
      · change linear (supp 6 D (src D k)) x = (x 0 || x 5)
        rw [hK, linear_pair]
      · change linear (supp 6 D (src D (sem_bar k))) x = (x 1 || x 4)
        rw [hK', linear_pair]
  · intro j hj ht
    by_cases hjc : j = ec.1
    · left
      exact ⟨0, hjc.symm⟩
    by_cases hjd : j = ed.1
    · left
      exact ⟨1, hjd.symm⟩
    by_cases hjk : j = k.1
    · left
      exact ⟨2, hjk.symm⟩
    exact Or.inr (hother j hj ht hjc hjd hjk)

end packScope17


section packScope18
open PEqualNP.Outside.L_meta_2590_aux.C6.GenericPair

open PEqualNP.Outside.L_meta_2590_aux.H2

lemma C6.GenericPair.no_Bplus_four {D : Dag} (h : StrictLive 6 D) (hc : sem_Comp 6 adj D)
    (hE : fourEndpoints ⊆ eligSet 6 D) (hb4 : Bplus 6 D = 4)
    (hAF : ∃ w, (0 : V) ∈ supp 6 D w ∧ (5 : V) ∈ supp 6 D w) : False := by
  obtain ⟨G, L, T, hG, hvalid, hbound, hgate, hlin, hkind⟩ := bf_birth_data h hc hE hb4 hAF
  apply BirthNoiseAdapter.no_three_births h.1 G L T hG hvalid
    (fun i => (hbound i).1) (fun i => (hbound i).2) hgate
    (fun i x => (hlin i x).1) (fun i x => (hlin i x).2)
    (fun j hj ht => bf_and_empty h hc hE hb4 hj ht) ?_ (outW 6 D) ?_
    (sem_supp_out graph_ok hc) ?_
  · intro j hj ht hnot
    rcases hkind j hj ht with ⟨i, hi⟩ | he
    · exact (hnot i hi.symm).elim
    · exact he
  · unfold outW
    omega
  · intro x
    apply Bool.eq_iff_iff.mpr
    exact (hc x).trans (edgeBool_spec x).symm

lemma C6.GenericPair.two_pair_occurrences_Bplus_ge_five {D : Dag}
    (h : StrictLive 6 D) (hc : sem_Comp 6 adj D)
    (hAF : ∃ w, (0 : V) ∈ supp 6 D w ∧ (5 : V) ∈ supp 6 D w)
    (hBE : ∃ w, (1 : V) ∈ supp 6 D w ∧ (4 : V) ∈ supp 6 D w) :
    5 ≤ Bplus 6 D := by
  classical
  obtain ⟨a, ha0, ha5⟩ := hAF
  obtain ⟨b, hb1, hb4⟩ := hBE
  have heA := joint_support_eligible h hc (by decide : (0 : V) ≠ 5) ha0 ha5
  have heB := joint_support_eligible h hc (by decide : (1 : V) ≠ 4) hb1 hb4
  have hE : fourEndpoints ⊆ eligSet 6 D := by
    intro v hv
    simp only [fourEndpoints, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact heA.1
    · exact heB.1
    · exact heB.2
    · exact heA.2
  obtain ⟨p, hp⟩ := sem_exists_pureBranch graph_ok h.1 hc
  have hcount := (Finset.card_le_card hE).trans (elig_le_Bplus h.1 p hp)
  have hfour : fourEndpoints.card = 4 := by decide
  rw [hfour] at hcount
  by_contra hn
  have heq : Bplus 6 D = 4 := by omega
  exact no_Bplus_four h hc hE heq ⟨a, ha0, ha5⟩

lemma C6.GenericPair.two_pair_occurrences_length_ge_ten_add_Bzero {D : Dag}
    (h : StrictLive 6 D) (hc : sem_Comp 6 adj D)
    (hAF : ∃ w, (0 : V) ∈ supp 6 D w ∧ (5 : V) ∈ supp 6 D w)
    (hBE : ∃ w, (1 : V) ∈ supp 6 D w ∧ (4 : V) ∈ supp 6 D w) :
    10 + Bzero 6 D ≤ D.length := by
  have hb := two_pair_occurrences_Bplus_ge_five h hc hAF hBE
  have hs := surplus_identity h
  rw [totalSurplus_split] at hs
  omega

end packScope18



section packScope19
open PEqualNP.Outside.L_meta_2590_aux.C6.GenericPair

open PEqualNP.Outside.L_meta_2590_aux.H2

lemma C6.GenericPair.opposite_joint_Bplus_ge_four {D : Dag} (h : StrictLive 6 D)
    (hc : sem_Comp 6 adj D) {u v : V} (hop : oppositePair u v)
    (hjoint : ∃ w, u ∈ supp 6 D w ∧ v ∈ supp 6 D w) : 4 ≤ Bplus 6 D := by
  obtain ⟨w, hwu, hwv⟩ := hjoint
  have he := joint_support_eligible h hc (opposite_distinct u v hop) hwu hwv
  by_contra hn
  have hB : Bplus 6 D ≤ 3 := by omega
  obtain ⟨b, hb⟩ := sem_exists_pureBranch graph_ok h.1 hc
  have hi := (independent_facts _ (inelig_independent h hc)).1
  have hel := elig_le_Bplus h.1 b hb
  have hsum := inelig_card_add 6 D
  have hI : (ineligSet 6 D).card = 3 := by omega
  rcases independent_hits_opposite _ (inelig_independent h hc) hI u v hop with hui | hvi
  · exact (sem_mem_inelig.mp hui) he.1
  · exact (sem_mem_inelig.mp hvi) he.2

lemma C6.GenericPair.opposite_joint_length_ge_nine_add_Bzero {D : Dag} (h : StrictLive 6 D)
    (hc : sem_Comp 6 adj D) {u v : V} (hop : oppositePair u v)
    (hjoint : ∃ w, u ∈ supp 6 D w ∧ v ∈ supp 6 D w) :
    9 + Bzero 6 D ≤ D.length := by
  have hb := opposite_joint_Bplus_ge_four h hc hop hjoint
  have hs := surplus_identity h
  rw [totalSurplus_split] at hs
  omega

lemma C6.GenericPair.three_pair_occurrences_Bplus_ge_six {D : Dag}
    (h : StrictLive 6 D) (hc : sem_Comp 6 adj D)
    (hAF : ∃ w, (0 : V) ∈ supp 6 D w ∧ (5 : V) ∈ supp 6 D w)
    (hBE : ∃ w, (1 : V) ∈ supp 6 D w ∧ (4 : V) ∈ supp 6 D w)
    (hCD : ∃ w, (2 : V) ∈ supp 6 D w ∧ (3 : V) ∈ supp 6 D w) :
    6 ≤ Bplus 6 D := by
  classical
  obtain ⟨wa, ha0, ha5⟩ := hAF
  obtain ⟨wb, hb1, hb4⟩ := hBE
  obtain ⟨wc, hc2, hc3⟩ := hCD
  have heAF := joint_support_eligible h hc (by decide : (0 : V) ≠ 5) ha0 ha5
  have heBE := joint_support_eligible h hc (by decide : (1 : V) ≠ 4) hb1 hb4
  have heCD := joint_support_eligible h hc (by decide : (2 : V) ≠ 3) hc2 hc3
  have heq : eligSet 6 D = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro v
    fin_cases v
    · exact heAF.1
    · exact heBE.1
    · exact heCD.1
    · exact heCD.2
    · exact heBE.2
    · exact heAF.2
  obtain ⟨b, hb⟩ := sem_exists_pureBranch graph_ok h.1 hc
  have hB := elig_le_Bplus h.1 b hb
  rw [heq] at hB
  simpa using hB

lemma C6.GenericPair.three_pair_occurrences_length_ge_eleven_add_Bzero {D : Dag}
    (h : StrictLive 6 D) (hc : sem_Comp 6 adj D)
    (hAF : ∃ w, (0 : V) ∈ supp 6 D w ∧ (5 : V) ∈ supp 6 D w)
    (hBE : ∃ w, (1 : V) ∈ supp 6 D w ∧ (4 : V) ∈ supp 6 D w)
    (hCD : ∃ w, (2 : V) ∈ supp 6 D w ∧ (3 : V) ∈ supp 6 D w) :
    11 + Bzero 6 D ≤ D.length := by
  have hb := three_pair_occurrences_Bplus_ge_six h hc hAF hBE hCD
  have hs := surplus_identity h
  rw [totalSurplus_split] at hs
  omega

end packScope19


section packScope20
open PEqualNP.Outside.L_meta_2590_aux.C6.GenericPair

open PEqualNP.Outside.L_meta_2590_aux.H2

lemma C6.GenericPair.joint_relabel {D : Dag} (σ : Equiv.Perm V) (hS : Strict 6 D) {u v : V}
    (hJ : ∃ w, u ∈ supp 6 D w ∧ v ∈ supp 6 D w) :
    ∃ w, σ u ∈ supp 6 (relabel σ D) w ∧ σ v ∈ supp 6 (relabel σ D) w := by
  obtain ⟨w, hu, hv⟩ := hJ
  refine ⟨liftP σ w, ?_, ?_⟩
  · rw [relabel_supp σ hS]
    exact Finset.mem_image.mpr ⟨u, hu, rfl⟩
  · rw [relabel_supp σ hS]
    exact Finset.mem_image.mpr ⟨v, hv, rfl⟩

lemma C6.GenericPair.pair01_length {D : Dag} (h : StrictLive 6 D) (hc : sem_Comp 6 adj D)
    (hAF : ∃ w, (0 : V) ∈ supp 6 D w ∧ (5 : V) ∈ supp 6 D w)
    (hBE : ∃ w, (1 : V) ∈ supp 6 D w ∧ (4 : V) ∈ supp 6 D w) : 10 ≤ D.length := by
  have hb := two_pair_occurrences_length_ge_ten_add_Bzero h hc hAF hBE
  omega

lemma C6.GenericPair.pair02_length {D : Dag} (h : StrictLive 6 D) (hc : sem_Comp 6 adj D)
    (hAF : ∃ w, (0 : V) ∈ supp 6 D w ∧ (5 : V) ∈ supp 6 D w)
    (hCD : ∃ w, (2 : V) ∈ supp 6 D w ∧ (3 : V) ∈ supp 6 D w) : 10 ≤ D.length := by
  have ha : ∃ w, (0 : V) ∈ supp 6 (relabel swapPairs D) w ∧
      (5 : V) ∈ supp 6 (relabel swapPairs D) w := by
    simpa [swapPairs] using joint_relabel swapPairs h.1 hAF
  have hb : ∃ w, (1 : V) ∈ supp 6 (relabel swapPairs D) w ∧
      (4 : V) ∈ supp 6 (relabel swapPairs D) w := by
    simpa [swapPairs] using joint_relabel swapPairs h.1 hCD
  have hs := pair01_length (relabel_strictLive swapPairs h)
    (c6_relabel_computes swapPairs swapPairs_adj h hc) ha hb
  simpa only [relabel_length] using hs

lemma C6.GenericPair.pair12_length {D : Dag} (h : StrictLive 6 D) (hc : sem_Comp 6 adj D)
    (hBE : ∃ w, (1 : V) ∈ supp 6 D w ∧ (4 : V) ∈ supp 6 D w)
    (hCD : ∃ w, (2 : V) ∈ supp 6 D w ∧ (3 : V) ∈ supp 6 D w) : 10 ≤ D.length := by
  have ha : ∃ w, (0 : V) ∈ supp 6 (relabel rotatePairs D) w ∧
      (5 : V) ∈ supp 6 (relabel rotatePairs D) w := by
    simpa [rotatePairs] using joint_relabel rotatePairs h.1 hBE
  have hb : ∃ w, (1 : V) ∈ supp 6 (relabel rotatePairs D) w ∧
      (4 : V) ∈ supp 6 (relabel rotatePairs D) w := by
    simpa [rotatePairs] using joint_relabel rotatePairs h.1 hCD
  have hs := pair01_length (relabel_strictLive rotatePairs h)
    (c6_relabel_computes rotatePairs rotatePairs_adj h hc) ha hb
  simpa only [relabel_length] using hs

def C6.GenericPair.PairOccurs (D : Dag) (p : Fin 3) : Prop :=
  ∃ w, (![0, 1, 2] p : V) ∈ supp 6 D w ∧ (![5, 4, 3] p : V) ∈ supp 6 D w

lemma C6.GenericPair.two_distinct_pair_occurrences_length {D : Dag}
    (h : StrictLive 6 D) (hc : sem_Comp 6 adj D)
    (p q : Fin 3) (hne : p ≠ q) (hp : PairOccurs D p) (hq : PairOccurs D q) :
    10 ≤ D.length := by
  fin_cases p <;> fin_cases q
  · exact (hne rfl).elim
  · exact pair01_length h hc (by simpa [PairOccurs] using hp) (by simpa [PairOccurs] using hq)
  · exact pair02_length h hc (by simpa [PairOccurs] using hp) (by simpa [PairOccurs] using hq)
  · exact pair01_length h hc (by simpa [PairOccurs] using hq) (by simpa [PairOccurs] using hp)
  · exact (hne rfl).elim
  · exact pair12_length h hc (by simpa [PairOccurs] using hp) (by simpa [PairOccurs] using hq)
  · exact pair02_length h hc (by simpa [PairOccurs] using hq) (by simpa [PairOccurs] using hp)
  · exact pair12_length h hc (by simpa [PairOccurs] using hq) (by simpa [PairOccurs] using hp)
  · exact (hne rfl).elim

end packScope20



section packScope21
open PEqualNP.Outside.L_meta_2590_aux.C6.GenericPair

open PEqualNP.Outside.L_meta_2590_aux.H2

lemma C6.GenericPair.one_pair_occurs_length {D : Dag} (h : StrictLive 6 D) (hc : sem_Comp 6 adj D)
    (p : Fin 3) (hp : PairOccurs D p) : 9 ≤ D.length := by
  fin_cases p
  · have hb := opposite_joint_length_ge_nine_add_Bzero h hc
      (u := (0 : V)) (v := (5 : V)) (by unfold oppositePair; decide)
      (by simpa [PairOccurs] using hp)
    omega
  · have hb := opposite_joint_length_ge_nine_add_Bzero h hc
      (u := (1 : V)) (v := (4 : V)) (by unfold oppositePair; decide)
      (by simpa [PairOccurs] using hp)
    omega
  · have hb := opposite_joint_length_ge_nine_add_Bzero h hc
      (u := (2 : V)) (v := (3 : V)) (by unfold oppositePair; decide)
      (by simpa [PairOccurs] using hp)
    omega

lemma C6.GenericPair.all_pair_occurrences_length {D : Dag} (h : StrictLive 6 D) (hc : sem_Comp 6 adj D)
    (hp : ∀ p : Fin 3, PairOccurs D p) : 11 ≤ D.length := by
  have hb := three_pair_occurrences_length_ge_eleven_add_Bzero h hc
    (by simpa [PairOccurs] using hp 0)
    (by simpa [PairOccurs] using hp 1)
    (by simpa [PairOccurs] using hp 2)
  omega

lemma C6.GenericPair.pair_occurrences_length {D : Dag} (h : StrictLive 6 D) (hc : sem_Comp 6 adj D)
    (S : Finset (Fin 3)) (hocc : ∀ p ∈ S, PairOccurs D p) :
    8 + S.card ≤ D.length := by
  classical
  have hmax : S.card ≤ 3 := by simpa using Finset.card_le_univ S
  rcases (by omega : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 ∨ S.card = 3) with h0 | h1 | h2 | h3
  · have hb := c6_length_ge_eight_add_Bzero h hc
    omega
  · obtain ⟨p, hp⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
    have hb := one_pair_occurs_length h hc p (hocc p hp)
    omega
  · obtain ⟨p, hp⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
    have hq : ∃ q ∈ S, q ≠ p := by
      by_contra hn
      push Not at hn
      have hs : S ⊆ {p} := by
        intro q hq
        exact Finset.mem_singleton.mpr (hn q hq)
      have hle := Finset.card_le_card hs
      simp only [Finset.card_singleton] at hle
      omega
    obtain ⟨q, hq, hqp⟩ := hq
    have hb := two_distinct_pair_occurrences_length h hc p q (Ne.symm hqp) (hocc p hp) (hocc q hq)
    omega
  · have heq : S = Finset.univ := Finset.eq_univ_of_card S (by simpa using h3)
    have hb := all_pair_occurrences_length h hc (fun p => hocc p (by rw [heq]; simp))
    omega

end packScope21


end packScope2

section packScope22

open PEqualNP.Outside.L_meta_2590_aux.H2

end packScope22

section packScope23
open PEqualNP.Outside.L_meta_2590_aux.H2

end packScope23

section packScope24
open PEqualNP.Outside.L_meta_2590_aux.H2

def PairPruning.c6Target (x : Fin 6 → Bool) : Bool :=
  (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 3) ||
    (x 1 && x 5) || (x 2 && x 4) || (x 2 && x 5)

open PEqualNP.Outside.L_meta_2590_aux.PairPruning

lemma PairPruning.c6_essential : ∀ i : Fin 6, ∃ x y : Fin 6 → Bool,
    (∀ k, k ≠ i → x k = y k) ∧ c6Target x ≠ c6Target y := by
  have hw : ∀ i : Fin 6, ∃ j : Fin 6,
      c6Target (single j) ≠ c6Target (sem_ins i (single j)) := by decide +kernel
  intro i
  obtain ⟨j, hj⟩ := hw i
  exact ⟨single j, sem_ins i (single j), sem_ins_agree i (single j), hj⟩

lemma PairPruning.c6_nonempty {D : Dag}
    (hD : ∀ x : Fin 6 → Bool, val D x (outW 6 D) = c6Target x) : D ≠ [] := by
  intro he
  have h := hD (single 5)
  rw [he] at h
  have hin : val ([] : Dag) (single (5 : Fin 6)) (outW 6 []) = true := by decide +kernel
  have hout : c6Target (single 5) = false := by decide +kernel
  rw [hin, hout] at h
  exact Bool.false_ne_true h.symm

end packScope24

section packScope25
open PEqualNP.Outside.L_meta_2590_aux.PairPruning

open PEqualNP.Outside.L_meta_2590_aux.H2

end packScope25

section packScope26
open PEqualNP.Outside.L_meta_2590_aux.PairPruning

open PEqualNP.Outside.L_meta_2590_aux.H2

set_option synthInstance.maxSize 4096 in
lemma PairPruning.c6Target_iff_adj (x : Fin 6 → Bool) :
    c6Target x = true ↔ sem_Edge C6.adj x := by
  revert x
  unfold c6Target sem_Edge C6.adj
  decide +kernel

end packScope26

section packScope27
open PEqualNP.Outside.L_meta_2590_aux.H2

def AnnotatedPruning.keep {m : ℕ} (S : Finset (Fin m)) (g : Fin m → ℕ) (q : ℕ) : Finset (Fin m) :=
  S.filter (fun i => g i ≠ q)

open PEqualNP.Outside.L_meta_2590_aux.AnnotatedPruning

def AnnotatedPruning.shift {m : ℕ} (g : Fin m → ℕ) (q : ℕ) (i : Fin m) : ℕ := na_sh q (g i)

lemma AnnotatedPruning.keep_subset {m : ℕ} (S : Finset (Fin m)) (g : Fin m → ℕ) (q : ℕ) :
    keep S g q ⊆ S := Finset.filter_subset _ _

lemma AnnotatedPruning.keep_card_loss {m : ℕ} (S : Finset (Fin m)) (g : Fin m → ℕ) (q : ℕ)
    (hinj : Set.InjOn g S) : S.card ≤ (keep S g q).card + 1 := by
  have heq (i : Fin m) (hi : i ∈ S \ keep S g q) : g i = q := by
    obtain ⟨his, hin⟩ := Finset.mem_sdiff.mp hi
    by_contra hne
    exact hin (Finset.mem_filter.mpr ⟨his, hne⟩)
  have hlost : (S \ keep S g q).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    exact hinj (Finset.mem_sdiff.mp ha).1 (Finset.mem_sdiff.mp hb).1
      ((heq a ha).trans (heq b hb).symm)
  have hsplit := Finset.card_sdiff_add_card_eq_card (keep_subset S g q)
  omega

lemma AnnotatedPruning.shift_inverse {m : ℕ} (g : Fin m → ℕ) (q : ℕ) (i : Fin m)
    (hne : g i ≠ q) : na_up q (shift g q i) = g i := by
  unfold shift na_up na_sh
  split_ifs <;> omega

lemma AnnotatedPruning.delete_support {n : ℕ} {D : Dag} (hS : Strict n D) (j : ℕ)
    (hj : j < D.length) (hf : fanout D (n + j) = 0) (w : ℕ)
    (hw : w < n + (D.length - 1)) :
    supp n (na_del n j D) w = supp n D (na_up (n + j) w) := by
  ext v
  simp only [mem_supp]
  rw [na_del_val hS j hj hf (single v) w hw]

lemma AnnotatedPruning.delete_marks {m n : ℕ} {D : Dag} (hS : Strict n D) (j : ℕ)
    (hj : j < D.length) (hf : fanout D (n + j) = 0)
    (S : Finset (Fin m)) (g : Fin m → ℕ) (P : Fin m → Finset (Fin n))
    (hinj : Set.InjOn g S)
    (hbounds : ∀ i ∈ S, n ≤ g i ∧ g i < n + D.length)
    (hjoint : ∀ i ∈ S, P i ⊆ supp n D (g i)) :
    keep S g (n + j) ⊆ S ∧
    S.card ≤ (keep S g (n + j)).card + 1 ∧
    Set.InjOn (shift g (n + j)) (keep S g (n + j)) ∧
    (∀ i ∈ keep S g (n + j),
      n ≤ shift g (n + j) i ∧ shift g (n + j) i < n + (na_del n j D).length) ∧
    (∀ i ∈ keep S g (n + j), P i ⊆ supp n (na_del n j D) (shift g (n + j) i)) := by
  have hb (i : Fin m) (hi : i ∈ keep S g (n + j)) :
      n ≤ shift g (n + j) i ∧ shift g (n + j) i < n + (na_del n j D).length := by
    obtain ⟨his, hne⟩ := Finset.mem_filter.mp hi
    have hbi := hbounds i his
    rw [na_del_length n j D hj]
    constructor <;> unfold shift na_sh <;> split_ifs <;> omega
  refine ⟨keep_subset S g (n + j), keep_card_loss S g (n + j) hinj, ?_, hb, ?_⟩
  · intro a ha b hb' he
    have hga := shift_inverse g (n + j) a (Finset.mem_filter.mp ha).2
    have hgb := shift_inverse g (n + j) b (Finset.mem_filter.mp hb').2
    apply hinj (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb').1
    exact hga.symm.trans ((congrArg (na_up (n + j)) he).trans hgb)
  · intro i hi
    have hbound := (hb i hi).2
    rw [na_del_length n j D hj] at hbound
    rw [delete_support hS j hj hf _ hbound,
      shift_inverse g (n + j) i (Finset.mem_filter.mp hi).2]
    exact hjoint i (Finset.mem_filter.mp hi).1

end packScope27

section packScope28
open PEqualNP.Outside.L_meta_2590_aux.AnnotatedPruning

open PEqualNP.Outside.L_meta_2590_aux.H2

lemma AnnotatedPruning.prune_aux {m n : ℕ} (F : (Fin n → Bool) → Bool)
    (hess : ∀ i : Fin n, ∃ x y : Fin n → Bool,
      (∀ k, k ≠ i → x k = y k) ∧ F x ≠ F y)
    (P : Fin m → Finset (Fin n)) :
    ∀ (s : ℕ) (D : Dag), D.length = s → Strict n D → D ≠ [] →
      (∀ x : Fin n → Bool, val D x (outW n D) = F x) →
      ∀ (S : Finset (Fin m)) (g : Fin m → ℕ), Set.InjOn g S →
      (∀ i ∈ S, n ≤ g i ∧ g i < n + D.length) →
      (∀ i ∈ S, P i ⊆ supp n D (g i)) →
      ∃ (D' : Dag) (S' : Finset (Fin m)) (g' : Fin m → ℕ),
        StrictLive n D' ∧ S' ⊆ S ∧ Set.InjOn g' S' ∧
        (∀ i ∈ S', n ≤ g' i ∧ g' i < n + D'.length) ∧
        (∀ i ∈ S', P i ⊆ supp n D' (g' i)) ∧
        D'.length ≤ s ∧ D'.length + S.card ≤ s + S'.card ∧
        ∀ x : Fin n → Bool, val D' x (outW n D') = F x := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro D hlen hS hne hD S g hinj hbounds hjoint
    have hpos : 0 < D.length := List.length_pos_iff.mpr hne
    by_cases hL : Live n D
    · exact ⟨D,S,g,⟨hS,hL,hne⟩,Finset.Subset.refl S,hinj,hbounds,hjoint,
        hlen.le,by omega,hD⟩
    · obtain ⟨w, hw, hf0⟩ : ∃ w, w + 1 < n + D.length ∧ fanout D w = 0 := by
        by_contra hcon
        exact hL (fun w hw => by
          by_contra h0
          exact hcon ⟨w, hw, by omega⟩)
      by_cases hwn : w < n
      · exfalso
        obtain ⟨x, y, hxy, hFne⟩ := hess ⟨w, hwn⟩
        apply hFne
        rw [← hD x, ← hD y]
        have hout : outW n D ≠ w := by unfold outW; omega
        have key := val_unique hS y (fun u => if u = w then y ⟨w, hwn⟩ else val D x u)
          (fun i hi => by
            by_cases hiw : i = w
            · subst hiw; simp
            · simp only [hiw, ite_false]
              rw [val_input D x i hi]
              exact hxy ⟨i, hi⟩ (fun h => hiw (congrArg Fin.val h)))
          (fun j hj => by
            obtain ⟨ha, hb⟩ := na_no_reader hf0 j hj
            have hnj : n + j ≠ w := by omega
            simp only [hnj, ha, hb, ite_false]
            exact val_gate hS x j hj)
          (outW n D) (by unfold outW; omega)
        simp only [hout, ite_false] at key
        exact key.symm
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < D.length := by omega
        have hl := na_del_length n j D hj
        have hne' : na_del n j D ≠ [] := by
          intro he
          rw [he] at hl
          simp at hl
          omega
        have hD' : ∀ x : Fin n → Bool,
            val (na_del n j D) x (outW n (na_del n j D)) = F x := by
          intro x
          have ho : outW n (na_del n j D) = n + (D.length - 1) - 1 := by
            unfold outW
            rw [hl]
          have hu : na_up (n + j) (n + (D.length - 1) - 1) = outW n D := by
            unfold na_up outW
            split_ifs <;> omega
          rw [ho, na_del_val hS j hj hf0 x _ (by omega), hu]
          exact hD x
        obtain ⟨hkeep,hdrop,hginj,hgb,hgj⟩ :=
          delete_marks hS j hj hf0 S g P hinj hbounds hjoint
        obtain ⟨D',S',g',h1,hsub,hginj',hgb',hgj',h2,h3,h4⟩ :=
          ih (D.length - 1) (by omega) (na_del n j D) hl
            (na_del_strict hS j hj hf0) hne' hD'
            (keep S g (n+j)) (shift g (n+j)) hginj hgb hgj
        exact ⟨D',S',g',h1,Finset.Subset.trans hsub hkeep,hginj',hgb',hgj',
          by omega,by omega,h4⟩

lemma AnnotatedPruning.exists_live_preserving_marks {m n : ℕ} (F : (Fin n → Bool) → Bool)
    (hess : ∀ i : Fin n, ∃ x y : Fin n → Bool,
      (∀ k, k ≠ i → x k = y k) ∧ F x ≠ F y)
    (P : Fin m → Finset (Fin n)) (D : Dag) (hS : Strict n D) (hne : D ≠ [])
    (hD : ∀ x : Fin n → Bool, val D x (outW n D) = F x)
    (S : Finset (Fin m)) (g : Fin m → ℕ) (hinj : Set.InjOn g S)
    (hbounds : ∀ i ∈ S, n ≤ g i ∧ g i < n + D.length)
    (hjoint : ∀ i ∈ S, P i ⊆ supp n D (g i)) :
    ∃ (D' : Dag) (S' : Finset (Fin m)) (g' : Fin m → ℕ),
      StrictLive n D' ∧ S' ⊆ S ∧ Set.InjOn g' S' ∧
      (∀ i ∈ S', n ≤ g' i ∧ g' i < n + D'.length) ∧
      (∀ i ∈ S', P i ⊆ supp n D' (g' i)) ∧
      D'.length ≤ D.length ∧ D'.length + S.card ≤ D.length + S'.card ∧
      ∀ x : Fin n → Bool, val D' x (outW n D') = F x :=
  prune_aux F hess P D.length D rfl hS hne hD S g hinj hbounds hjoint

lemma AnnotatedPruning.lift_live_bound {m n : ℕ} (F : (Fin n → Bool) → Bool)
    (hess : ∀ i : Fin n, ∃ x y : Fin n → Bool,
      (∀ k, k ≠ i → x k = y k) ∧ F x ≠ F y)
    (P : Fin m → Finset (Fin n)) (b : ℕ)
    (hlive : ∀ (D : Dag) (S : Finset (Fin m)) (g : Fin m → ℕ),
      StrictLive n D → (∀ x : Fin n → Bool, val D x (outW n D) = F x) →
      Set.InjOn g S → (∀ i ∈ S, n ≤ g i ∧ g i < n + D.length) →
      (∀ i ∈ S, P i ⊆ supp n D (g i)) → b + S.card ≤ D.length)
    (D : Dag) (hS : Strict n D) (hne : D ≠ [])
    (hD : ∀ x : Fin n → Bool, val D x (outW n D) = F x)
    (S : Finset (Fin m)) (g : Fin m → ℕ) (hinj : Set.InjOn g S)
    (hbounds : ∀ i ∈ S, n ≤ g i ∧ g i < n + D.length)
    (hjoint : ∀ i ∈ S, P i ⊆ supp n D (g i)) : b + S.card ≤ D.length := by
  obtain ⟨D',S',g',h1,_,h2,h3,h4,_,h5,h6⟩ :=
    exists_live_preserving_marks F hess P D hS hne hD S g hinj hbounds hjoint
  have h7 := hlive D' S' g' h1 h6 h2 h3 h4
  omega

end packScope28

section packScope29
open PEqualNP.Outside.L_meta_2590_aux.AnnotatedPruning

open PEqualNP.Outside.L_meta_2590_aux.H2 PEqualNP.Outside.L_meta_2590_aux.PairPruning

lemma AnnotatedPruning.c6_strict_designated_bound
    (D : Dag) (hS : Strict 6 D)
    (hD : ∀ x : Fin 6 → Bool, val D x (outW 6 D) = c6Target x)
    (S : Finset (Fin 3)) (g : Fin 3 → Nat) (hinj : Set.InjOn g S)
    (hbounds : ∀ p ∈ S, 6 ≤ g p ∧ g p < 6 + D.length)
    (hjoint : ∀ p ∈ S, (![0, 1, 2] p : Fin 6) ∈ supp 6 D (g p) ∧
      (![5, 4, 3] p : Fin 6) ∈ supp 6 D (g p)) :
    8 + S.card ≤ D.length := by
  refine lift_live_bound c6Target c6_essential
    (fun p : Fin 3 => {(![0, 1, 2] p : Fin 6), (![5, 4, 3] p : Fin 6)}) 8
    ?_ D hS (c6_nonempty hD) hD S g hinj hbounds ?_
  · intro D' S' g' hL hF _ _ hP
    have hc : sem_Comp 6 C6.adj D' := by
      intro x
      rw [hF x]
      exact c6Target_iff_adj x
    apply C6.GenericPair.pair_occurrences_length hL hc S'
    intro p hp
    exact ⟨g' p, hP p hp (Finset.mem_insert_self _ _),
      hP p hp (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))⟩
  · intro p hp
    simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using hjoint p hp

end packScope29
section packScope30

open PEqualNP.Outside.L_meta_2590_aux.H2

lemma H2.c6_actual_annotated_bound (D : Dag) (hS : Strict 6 D)
    (hD : ∀ x : Fin 6 → Bool, val D x (outW 6 D) = residualC6 x)
    (S : Finset (Fin 3)) (g : Fin 3 → ℕ) (hinj : Set.InjOn g S)
    (hbounds : ∀ p ∈ S, 6 ≤ g p ∧ g p < 6 + D.length)
    (hjoint : ∀ p ∈ S, n0ResidualPairs p ⊆ supp 6 D (g p)) :
    8 + S.card ≤ D.length := by
  apply PEqualNP.Outside.L_meta_2590_aux.AnnotatedPruning.c6_strict_designated_bound
    D hS hD S g hinj hbounds
  intro p hp
  have hleft : (![0, 1, 2] p : Fin 6) ∈ n0ResidualPairs p := by
    fin_cases p <;> simp [n0ResidualPairs]
  have hright : (![5, 4, 3] p : Fin 6) ∈ n0ResidualPairs p := by
    fin_cases p <;> simp [n0ResidualPairs]
  exact ⟨hjoint p hp hleft, hjoint p hp hright⟩

lemma H2.n0_retained_marks_actual_bound {D : Dag} (hS : Strict 10 D) (q : ℕ)
    (hq : q ≤ (stage 6 n0Refs D D.length).2.length)
    (hF : ∀ x : Fin 6 → Bool,
      val ((stage 6 n0Refs D D.length).2.take q) x
        (outW 6 ((stage 6 n0Refs D D.length).2.take q)) = residualC6 x)
    (M : Finset ℕ)
    (hgood : ∀ j ∈ M, (0 : Fin 10) ∈ supp 10 D (10 + j) ∨
      ∃ p : Fin 3, supp 10 D (10 + j) = n0OriginalPairs p)
    (hunique : ∀ i ∈ M, ∀ j ∈ M, ∀ p : Fin 3,
      supp 10 D (10 + i) = n0OriginalPairs p →
      supp 10 D (10 + j) = n0OriginalPairs p → i = j) :
    8 + (keptEmitted 6 n0Refs D D.length q ∩ M).card ≤ q := by
  obtain ⟨S, g, hcard, hinj, hgp⟩ := n0_retained_marks hS q hq M hgood hunique
  have hlen : ((stage 6 n0Refs D D.length).2.take q).length = q := by
    rw [List.length_take, Nat.min_eq_left hq]
  have hstrict : Strict 6 ((stage 6 n0Refs D D.length).2.take q) :=
    na_strict_take (stage_good 6 n0Refs D n0Refs_good D.length).1 q
  have hb := c6_actual_annotated_bound _ hstrict hF S g hinj
    (fun p hp => ⟨(hgp p hp).1, by rw [hlen]; exact (hgp p hp).2.1⟩)
    (fun p hp => (hgp p hp).2.2)
  rw [hcard, hlen] at hb
  exact hb

lemma H2.n0_first_six_marks_actual_impossible {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hi : neighborhoodI ⊆ ineligSet 10 D)
    (M : Finset ℕ) (hM : M ⊆ Finset.range D.length) (hsix : 6 ≤ M.card)
    (hcard : ∀ j ∈ M, 2 ≤ (supp 10 D (10 + j)).card)
    (hfirst : ∀ j ∈ M, ∀ k < j, supp 10 D (10 + k) ≠ supp 10 D (10 + j))
    (hgood : ∀ j ∈ M, (0 : Fin 10) ∈ supp 10 D (10 + j) ∨
      ∃ p : Fin 3, supp 10 D (10 + j) = n0OriginalPairs p)
    (hlen : D.length ≤ 19) : False := by
  obtain ⟨q, _, hq, _, _, _, hF, _⟩ := n0_c6_output_prefix hc
  have hunique : ∀ i ∈ M, ∀ j ∈ M, ∀ p : Fin 3,
      supp 10 D (10 + i) = n0OriginalPairs p →
      supp 10 D (10 + j) = n0OriginalPairs p → i = j := by
    intro i hi j hj p hip hjp
    by_contra hne
    rcases lt_or_gt_of_ne hne with hij | hji
    · exact hfirst j hj i hij (hip.trans hjp.symm)
    · exact hfirst i hi j hji (hjp.trans hip.symm)
  have hlower := n0_retained_marks_actual_bound h.1 q hq hF M hgood hunique
  exact n0_first_six_marks_prefix_impossible h hc hi M hM hsix hcard hfirst q hq hlen hlower

end packScope30
section packScope31

open PEqualNP.Outside.L_meta_2590_aux.H2

abbrev H2.N0BirthVertex := Fin 10
def H2.n0BirthPair (i : Fin 3) : Finset N0BirthVertex := ![{2, 6}, {3, 9}, {7, 8}] i
def H2.n0BirthTriple (i : Fin 3) : Finset N0BirthVertex := insert 0 (n0BirthPair i)
def H2.n0BirthOccurrence (D : Dag) (S : Finset N0BirthVertex) : Prop := ∃ w, supp 10 D w = S
def H2.n0BirthGood (S : Finset N0BirthVertex) : Prop :=
  2 ≤ S.card ∧ ((0 : N0BirthVertex) ∈ S ∨ ∃ i : Fin 3, S = n0BirthPair i)
def H2.n0BirthAt (D : Dag) (j : ℕ) (S : Finset N0BirthVertex) : Prop :=
  j < D.length ∧ supp 10 D (10 + j) = S ∧
    ∀ w, w < 10 + j → supp 10 D w ≠ S

lemma H2.n0_birth_geometry : (∀ i, (n0BirthTriple i).card = 3 ∧ (0 : N0BirthVertex) ∈ n0BirthTriple i ∧ (n0BirthPair i).card = 2) ∧
    ∀ i j, i ≠ j → n0BirthTriple i ∩ n0BirthTriple j = {0} := by decide +kernel

lemma H2.n0_birth_triple_injective : Function.Injective n0BirthTriple := by decide +kernel

lemma H2.n0_birth_good_subtriple {S : Finset N0BirthVertex} {i : Fin 3}
    (hcard : 2 ≤ S.card) (hsub : S ⊆ n0BirthTriple i) : n0BirthGood S := by
  refine ⟨hcard, ?_⟩
  by_cases hz : (0 : N0BirthVertex) ∈ S
  · exact Or.inl hz
  · right
    refine ⟨i, Finset.eq_of_subset_of_card_le ?_ ?_⟩
    · intro v hv
      have hv' := hsub hv
      rw [n0BirthTriple, Finset.mem_insert] at hv'
      exact hv'.resolve_left (fun he => hz (he ▸ hv))
    · rw [(n0_birth_geometry.1 i).2.2]
      exact hcard

lemma H2.n0_birth_good_supertriple {S : Finset N0BirthVertex} {i : Fin 3}
    (hsub : n0BirthTriple i ⊆ S) : n0BirthGood S := by
  have hc := Finset.card_le_card hsub
  rw [(n0_birth_geometry.1 i).1] at hc
  exact ⟨by omega, Or.inl (hsub (n0_birth_geometry.1 i).2.1)⟩

lemma H2.n0_birth_exists {D : Dag} (hS : Strict 10 D) {S : Finset N0BirthVertex}
    (hcard : 2 ≤ S.card) (hocc : n0BirthOccurrence D S) : ∃ j, n0BirthAt D j S := by
  obtain ⟨w, hw⟩ := hocc
  obtain ⟨j,hj,_,hs,_,hfirst,_⟩ :=
    sem_first_mask hS Finset.univ S hcard w (by simpa using hw)
  simp only [Finset.inter_univ] at hs hfirst
  exact ⟨j,hj,hs,hfirst⟩

lemma H2.n0_birth_support_split {D : Dag} (hS : Strict 10 D) {S : Finset N0BirthVertex}
    (hcard : S.card = 3) (hocc : n0BirthOccurrence D S) :
    (∃ A B : Finset N0BirthVertex, n0BirthOccurrence D A ∧ n0BirthOccurrence D B ∧ S ⊂ A ∧ S ⊂ B ∧ A ∩ B = S) ∨
    (∃ C : Finset N0BirthVertex, n0BirthOccurrence D C ∧ 2 ≤ C.card ∧ C ⊂ S) := by
  obtain ⟨w, hw⟩ := hocc
  obtain ⟨j,hj,_,hs,_,_,hcases⟩ :=
    sem_first_mask hS Finset.univ S (by omega) w (by simpa using hw)
  simp only [Finset.inter_univ] at hs hcases
  rcases hcases with ⟨ht,ha,hb⟩ | ⟨_,ha,hb,hu,_,_⟩
  · exact Or.inl ⟨_,_,⟨opA D j,rfl⟩,⟨opB D j,rfl⟩,ha,hb,
      (sem_supp_and hS hj ht).symm.trans hs⟩
  · have hc := Finset.card_union_le (supp 10 D (opA D j)) (supp 10 D (opB D j))
    rw [hu,hcard] at hc
    by_cases hca : 2 ≤ (supp 10 D (opA D j)).card
    · exact Or.inr ⟨_,⟨opA D j,rfl⟩,hca,ha⟩
    · exact Or.inr ⟨_,⟨opB D j,rfl⟩,by omega,hb⟩

lemma H2.n0_birth_unique {D : Dag} {j k : ℕ} {S : Finset N0BirthVertex}
    (hj : n0BirthAt D j S) (hk : n0BirthAt D k S) : j = k := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hk.2.2 (10+j) (by omega) hj.2.1
  · exact hj.2.2 (10+k) (by omega) hk.2.1

lemma H2.n0_birth_collect_six {D : Dag} (hS : Strict 10 D)
    (hocc : ∀ i, n0BirthOccurrence D (n0BirthTriple i))
    (U : Fin 3 → Finset N0BirthVertex) (hu : ∀ i, n0BirthOccurrence D (U i) ∧ n0BirthGood (U i))
    (hinj : Function.Injective U) (hsep : ∀ i j, n0BirthTriple i ≠ U j) :
    ∃ F : Finset ℕ, F.card = 6 ∧
      (∀ j ∈ F, n0BirthAt D j (supp 10 D (10+j)) ∧ n0BirthGood (supp 10 D (10+j))) ∧
      ∀ j ∈ F, ∀ k ∈ F, ∀ i : Fin 3,
        supp 10 D (10+j) = n0BirthPair i → supp 10 D (10+k) = n0BirthPair i → j = k := by
  classical
  let S : Fin 3 × Bool → Finset N0BirthVertex := fun p => if p.2 then n0BirthTriple p.1 else U p.1
  have hs : ∀ p, n0BirthOccurrence D (S p) ∧ n0BirthGood (S p) := by
    rintro ⟨i,s⟩
    cases s
    · exact hu i
    · exact ⟨hocc i,n0_birth_good_supertriple (Finset.Subset.refl _)⟩
  have hsi : Function.Injective S := by
    rintro ⟨i,s⟩ ⟨j,t⟩ he
    cases s <;> cases t
    · exact Prod.ext (hinj he) rfl
    · exact False.elim (hsep j i he.symm)
    · exact False.elim (hsep i j he)
    · exact Prod.ext (n0_birth_triple_injective he) rfl
  have hbe (p : Fin 3 × Bool) : ∃ j, n0BirthAt D j (S p) :=
    n0_birth_exists hS (hs p).2.1 (hs p).1
  choose gate hb using hbe
  have hgi : Function.Injective gate := by
    intro p q he
    apply hsi
    exact (hb p).2.1.symm.trans ((congrArg (fun j => supp 10 D (10+j)) he).trans (hb q).2.1)
  let F := Finset.univ.image gate
  have hf : ∀ j ∈ F, n0BirthAt D j (supp 10 D (10+j)) ∧ n0BirthGood (supp 10 D (10+j)) := by
    intro j hj
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hj
    simpa only [(hb p).2.1] using And.intro (hb p) (hs p).2
  refine ⟨F,?_,hf,?_⟩
  · rw [Finset.card_image_of_injective _ hgi]
    decide
  · intro j hj k hk i he hf'
    apply n0_birth_unique (S := n0BirthPair i)
    · simpa only [he] using (hf j hj).1
    · simpa only [hf'] using (hf k hk).1

lemma H2.n0_birth_six_of_small_helpers {D : Dag} (hS : Strict 10 D)
    (hocc : ∀ i, n0BirthOccurrence D (n0BirthTriple i))
    (hsmall : ∀ i, ∃ C : Finset N0BirthVertex, n0BirthOccurrence D C ∧ 2 ≤ C.card ∧ C ⊂ n0BirthTriple i) :
    ∃ U : Fin 3 → Finset N0BirthVertex, (∀ i, n0BirthOccurrence D (U i) ∧ n0BirthGood (U i)) ∧
      Function.Injective U ∧ (∀ i j, n0BirthTriple i ≠ U j) := by
  classical
  choose U hu hc hs using hsmall
  have hcard (i : Fin 3) : (U i).card = 2 := by
    have hh := Finset.card_lt_card (hs i)
    rw [(n0_birth_geometry.1 i).1] at hh
    have := hc i
    omega
  refine ⟨U,fun i => ⟨hu i,n0_birth_good_subtriple (hc i) (hs i).le⟩,?_,?_⟩
  · intro i j he
    by_contra hne
    have hsub : U i ⊆ n0BirthTriple i ∩ n0BirthTriple j := by
      intro v hv
      exact Finset.mem_inter.mpr ⟨(hs i).le hv,(hs j).le (he ▸ hv)⟩
    have hh := Finset.card_le_card hsub
    rw [n0_birth_geometry.2 i j hne,Finset.card_singleton,hcard] at hh
    omega
  · intro i j he
    have hh := congrArg Finset.card he
    rw [(n0_birth_geometry.1 i).1,hcard] at hh
    omega

lemma H2.n0_birth_other_parent {i j : Fin 3} (hij : i ≠ j) {A B X Y : Finset N0BirthVertex}
    (hAB : A ∩ B = n0BirthTriple i) (hX : n0BirthTriple j ⊂ X)
    (hXY : X ∩ Y = n0BirthTriple j) :
    (X ≠ A ∧ X ≠ B) ∨ (Y ≠ A ∧ Y ≠ B) := by
  have hne : X ≠ Y := by
    intro he
    have hc := Finset.card_lt_card hX
    have hh : X = n0BirthTriple j := by simpa only [← he,Finset.inter_self] using hXY
    rw [hh] at hc
    omega
  by_cases hx : X ≠ A ∧ X ≠ B
  · exact Or.inl hx
  by_cases hy : Y ≠ A ∧ Y ≠ B
  · exact Or.inr hy
  have hx' : X = A ∨ X = B := by tauto
  have hy' : Y = A ∨ Y = B := by tauto
  exfalso
  rcases hx' with hx' | hx' <;> rcases hy' with hy' | hy'
  · exact hne (hx'.trans hy'.symm)
  · apply hij
    apply n0_birth_triple_injective
    calc n0BirthTriple i = A ∩ B := hAB.symm
         _ = X ∩ Y := by rw [hx',hy']
         _ = n0BirthTriple j := hXY
  · apply hij
    apply n0_birth_triple_injective
    calc n0BirthTriple i = A ∩ B := hAB.symm
         _ = X ∩ Y := by rw [hx',hy',Finset.inter_comm]
         _ = n0BirthTriple j := hXY
  · exact hne (hx'.trans hy'.symm)

lemma H2.n0_birth_helpers_of_and {D : Dag} (hS : Strict 10 D)
    (hocc : ∀ i, n0BirthOccurrence D (n0BirthTriple i)) (i : Fin 3) (A B : Finset N0BirthVertex)
    (hOA : n0BirthOccurrence D A) (hOB : n0BirthOccurrence D B)
    (hA : n0BirthTriple i ⊂ A) (hB : n0BirthTriple i ⊂ B) (hAB : A ∩ B = n0BirthTriple i) :
    ∃ U : Fin 3 → Finset N0BirthVertex, (∀ k, n0BirthOccurrence D (U k) ∧ n0BirthGood (U k)) ∧
      Function.Injective U ∧ (∀ k l, n0BirthTriple k ≠ U l) := by
  classical
  have hAc : 4 ≤ A.card := by
    have hh := Finset.card_lt_card hA
    rw [(n0_birth_geometry.1 i).1] at hh
    omega
  have hBc : 4 ≤ B.card := by
    have hh := Finset.card_lt_card hB
    rw [(n0_birth_geometry.1 i).1] at hh
    omega
  have hABne : A ≠ B := by
    intro he
    have hh : A = n0BirthTriple i := by simpa only [← he,Finset.inter_self] using hAB
    rw [hh,(n0_birth_geometry.1 i).1] at hAc
    omega
  have hje : ∃ j : Fin 3, j ≠ i := by fin_cases i <;> decide +kernel
  obtain ⟨j,hji⟩ := hje
  have hCe : ∃ C : Finset N0BirthVertex, n0BirthOccurrence D C ∧ n0BirthGood C ∧ C ≠ A ∧ C ≠ B ∧
      (∀ k, n0BirthTriple k ≠ C) := by
    rcases n0_birth_support_split hS (n0_birth_geometry.1 j).1 (hocc j) with
      ⟨X,Y,hOX,hOY,hX,hY,hXY⟩ | ⟨C,hOC,hC,hCT⟩
    · have pick := n0_birth_other_parent (Ne.symm hji) hAB hX hXY
      have build (Z : Finset N0BirthVertex) (hOZ : n0BirthOccurrence D Z) (hZ : n0BirthTriple j ⊂ Z)
          (hneA : Z ≠ A) (hneB : Z ≠ B) :
          n0BirthOccurrence D Z ∧ n0BirthGood Z ∧ Z ≠ A ∧ Z ≠ B ∧ (∀ k, n0BirthTriple k ≠ Z) := by
        refine ⟨hOZ,n0_birth_good_supertriple hZ.le,hneA,hneB,?_⟩
        intro k he
        have hc := Finset.card_lt_card hZ
        rw [← he,(n0_birth_geometry.1 j).1,(n0_birth_geometry.1 k).1] at hc
        omega
      rcases pick with hx | hy
      · exact ⟨X,build X hOX hX hx.1 hx.2⟩
      · exact ⟨Y,build Y hOY hY hy.1 hy.2⟩
    · have hCc : C.card = 2 := by
        have hc := Finset.card_lt_card hCT
        rw [(n0_birth_geometry.1 j).1] at hc
        omega
      refine ⟨C,hOC,n0_birth_good_subtriple hC hCT.le,?_,?_,?_⟩
      · intro he
        rw [← he,hCc] at hAc
        omega
      · intro he
        rw [← he,hCc] at hBc
        omega
      · intro k he
        have hc := congrArg Finset.card he
        rw [(n0_birth_geometry.1 k).1,hCc] at hc
        omega
  obtain ⟨C,hOC,hGC,hCA,hCB,hCT⟩ := hCe
  let U : Fin 3 → Finset N0BirthVertex := ![A,B,C]
  refine ⟨U,?_,?_,?_⟩
  · intro k
    fin_cases k
    · exact ⟨hOA,n0_birth_good_supertriple hA.le⟩
    · exact ⟨hOB,n0_birth_good_supertriple hB.le⟩
    · exact ⟨hOC,hGC⟩
  · intro k l he
    fin_cases k <;> fin_cases l <;> simp_all [U]
  · intro k l he
    fin_cases l
    · have hc := congrArg Finset.card he
      change (n0BirthTriple k).card = A.card at hc
      rw [(n0_birth_geometry.1 k).1] at hc
      omega
    · have hc := congrArg Finset.card he
      change (n0BirthTriple k).card = B.card at hc
      rw [(n0_birth_geometry.1 k).1] at hc
      omega
    · exact hCT k he

lemma H2.n0_six_births {D : Dag} (hS : Strict 10 D)
    (hocc : ∀ i, n0BirthOccurrence D (n0BirthTriple i)) :
    ∃ F : Finset ℕ, F.card = 6 ∧
      (∀ j ∈ F, n0BirthAt D j (supp 10 D (10+j)) ∧
        2 ≤ (supp 10 D (10+j)).card ∧
        ((0 : N0BirthVertex) ∈ supp 10 D (10+j) ∨ ∃ i, supp 10 D (10+j) = n0BirthPair i)) ∧
      ∀ j ∈ F, ∀ k ∈ F, ∀ i : Fin 3,
        supp 10 D (10+j) = n0BirthPair i → supp 10 D (10+k) = n0BirthPair i → j = k := by
  classical
  by_cases ha : ∃ i : Fin 3, ∃ A B : Finset N0BirthVertex,
      n0BirthOccurrence D A ∧ n0BirthOccurrence D B ∧ n0BirthTriple i ⊂ A ∧ n0BirthTriple i ⊂ B ∧ A ∩ B = n0BirthTriple i
  · obtain ⟨i,A,B,hOA,hOB,hA,hB,hAB⟩ := ha
    obtain ⟨U,hu,hi,hs⟩ := n0_birth_helpers_of_and hS hocc i A B hOA hOB hA hB hAB
    exact n0_birth_collect_six hS hocc U hu hi hs
  · have hsmall : ∀ i, ∃ C : Finset N0BirthVertex, n0BirthOccurrence D C ∧ 2 ≤ C.card ∧ C ⊂ n0BirthTriple i := by
      intro i
      rcases n0_birth_support_split hS (n0_birth_geometry.1 i).1 (hocc i) with hh | hh
      · exact False.elim (ha ⟨i,hh⟩)
      · exact hh
    obtain ⟨U,hu,hi,hs⟩ := n0_birth_six_of_small_helpers hS hocc hsmall
    exact n0_birth_collect_six hS hocc U hu hi hs

lemma H2.n0_six_first_marks_of_triple_supports {D : Dag} (hS : Strict 10 D)
    (hocc : ∀ i : Fin 3, ∃ w, supp 10 D w = insert 0 (n0OriginalPairs i)) :
    ∃ M : Finset ℕ, M ⊆ Finset.range D.length ∧ M.card = 6 ∧
      (∀ j ∈ M, 2 ≤ (supp 10 D (10 + j)).card) ∧
      (∀ j ∈ M, ∀ k < j, supp 10 D (10 + k) ≠ supp 10 D (10 + j)) ∧
      (∀ j ∈ M, (0 : Fin 10) ∈ supp 10 D (10 + j) ∨
        ∃ i : Fin 3, supp 10 D (10 + j) = n0OriginalPairs i) ∧
      (∀ j ∈ M, ∀ k ∈ M, ∀ i : Fin 3,
        supp 10 D (10 + j) = n0OriginalPairs i →
        supp 10 D (10 + k) = n0OriginalPairs i → j = k) := by
  have hocc' : ∀ i, n0BirthOccurrence D (n0BirthTriple i) := by
    intro i
    exact hocc i
  obtain ⟨M, hcard, hgood, hunique⟩ := n0_six_births hS hocc'
  refine ⟨M, ?_, hcard, ?_, ?_, ?_, ?_⟩
  · intro j hj
    exact Finset.mem_range.mpr (hgood j hj).1.1
  · intro j hj
    exact (hgood j hj).2.1
  · intro j hj k hk
    exact (hgood j hj).1.2.2 (10 + k) (by omega)
  · intro j hj
    exact (hgood j hj).2.2
  · intro j hj k hk i hi hk'
    exact hunique j hj k hk i hi hk'

end packScope31
section packScope32

open PEqualNP.Outside.L_meta_2590_aux.H2

def H2.neighborhoodExtraHitSet (i c : Fin 10) : Finset (Fin 10) :=
  if i = 1 then
    if c = 3 ∨ c = 7 then {1, 3, 7} else {1, 8, 9}
  else if i = 4 then
    if c = 2 ∨ c = 8 then {4, 2, 8} else {4, 6, 7}
  else
    if c = 2 ∨ c = 9 then {5, 2, 9} else {5, 3, 6}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma H2.neighborhoodExtraHitSet_spec :
    ∀ i c : Fin 10, i ∈ neighborhoodI → c ∉ neighborhoodI → ¬ adj i c →
      adj 0 i ∧ i ∈ neighborhoodExtraHitSet i c ∧
      c ∈ neighborhoodExtraHitSet i c ∧ (0 : Fin 10) ∉ neighborhoodExtraHitSet i c ∧
      (neighborhoodExtraHitSet i c).card = 3 ∧
      (∀ a ∈ neighborhoodExtraHitSet i c, ∀ b ∈ neighborhoodExtraHitSet i c, ¬ adj a b) ∧
      ∀ j ∈ neighborhoodI, j ≠ i → ∃ a ∈ neighborhoodExtraHitSet i c, adj j a := by
  decide +kernel

lemma H2.neighborhood_extra_independent_hitting_set (i c : Fin 10)
    (hi : i ∈ neighborhoodI) (hc : c ∉ neighborhoodI) (hic : ¬ adj i c) :
    ∃ A : Finset (Fin 10), i ∈ A ∧ c ∈ A ∧
      (∀ a ∈ A, ∀ b ∈ A, ¬ adj a b) ∧
      (∃ a ∈ A, adj 0 a) ∧
      ∀ j ∈ neighborhoodI, j ≠ i → ∃ a ∈ A, adj j a := by
  obtain ⟨h0i, hiA, hcA, _, _, hA, hhit⟩ := neighborhoodExtraHitSet_spec i c hi hc hic
  exact ⟨neighborhoodExtraHitSet i c, hiA, hcA, hA, ⟨i, hiA, h0i⟩, hhit⟩

end packScope32
section packScope33

open PEqualNP.Outside.L_meta_2590_aux.H2

lemma H2.n0_assigned_exits_exhaust {D : Dag} (hI : neighborhoodI ⊆ ineligSet 10 D)
    (pos : Fin 10 → ℕ × Bool) (hp : k4_Pos 10 adj D pos)
    (hW : (sem_W 10 D (0 : Fin 10)).card ≤ 3) :
    neighborhoodI.image pos = sem_W 10 D (0 : Fin 10) := by
  classical
  have hgeom : ∀ i ∈ neighborhoodI, adj i 0 := by decide +kernel
  have hsub : neighborhoodI.image pos ⊆ sem_W 10 D (0 : Fin 10) := by
    intro e he
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hj, hempty, hnb, _⟩ := hp.1 i (hI hi)
    refine sem_mem_W.mpr ⟨hj, hnb 0 (hgeom i hi), ?_⟩
    rw [hempty]
    exact Finset.notMem_empty _
  have hinj : Set.InjOn pos neighborhoodI := by
    intro i hi j hj he
    exact hp.2 i (hI hi) j (hI hj) he
  apply Finset.eq_of_subset_of_card_le hsub
  rw [Finset.card_image_of_injOn hinj]
  have hcard : neighborhoodI.card = 3 := by decide
  omega

lemma H2.n0_assigned_source_exact_unrestricted {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hI : neighborhoodI ⊆ ineligSet 10 D)
    (pos : Fin 10 → ℕ × Bool) (hp : k4_Pos 10 adj D pos)
    (hW : (sem_W 10 D (0 : Fin 10)).card ≤ 3) :
    ∀ i ∈ neighborhoodI, ∀ a : Fin 10,
      a ∈ supp 10 D (src D (pos i)) ↔ adj i a := by
  have hexits := n0_assigned_exits_exhaust hI pos hp hW
  have hgeom : ∀ i ∈ neighborhoodI, adj i 0 := by decide +kernel
  have hn0 : (0 : Fin 10) ∉ neighborhoodI := by decide
  intro i hi a
  constructor
  · intro ha
    by_contra hna
    have haI : a ∉ neighborhoodI := by
      intro haI
      have hsingle := sem_inelig_pure graph_ok h.1 hc (hI haI) ha
      have h0 := (hp.1 i (hI hi)).2.2.1 0 (hgeom i hi)
      rw [hsingle, Finset.mem_singleton] at h0
      exact hn0 (h0 ▸ haI)
    obtain ⟨A, hiA, haA, hA, h0A, hhit⟩ :=
      neighborhood_extra_independent_hitting_set i a hi haI hna
    obtain ⟨j, s, hj, _, h0s, h0out, hdis⟩ := sem_exposure graph_ok h.1 hc A hA 0 h0A
    have he : (j, s) ∈ sem_W 10 D (0 : Fin 10) := sem_mem_W.mpr ⟨hj, h0s, h0out⟩
    rw [← hexits] at he
    obtain ⟨k, hk, he⟩ := Finset.mem_image.mp he
    rw [← he] at hdis
    by_cases hki : k = i
    · subst k
      exact Finset.disjoint_left.mp hdis ha haA
    · obtain ⟨b, hbA, hkb⟩ := hhit k hk hki
      exact Finset.disjoint_left.mp hdis ((hp.1 k (hI hk)).2.2.1 b hkb) hbA
  · exact (hp.1 i (hI hi)).2.2.1 a

def H2.n0StarVertex : Fin 3 → Fin 10 := ![1, 4, 5]

lemma H2.n0StarVertex_mem (p : Fin 3) : n0StarVertex p ∈ neighborhoodI := by
  fin_cases p <;> decide

lemma H2.n0StarVertex_neighbors (p : Fin 3) (a : Fin 10) :
    adj (n0StarVertex p) a ↔ a ∈ insert 0 (n0OriginalPairs p) := by
  fin_cases p <;> fin_cases a <;> decide +kernel

lemma H2.n0_exact_star_triples {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hI : neighborhoodI ⊆ ineligSet 10 D)
    (hW : (sem_W 10 D (0 : Fin 10)).card ≤ 3) :
    ∀ p : Fin 3, ∃ w, supp 10 D w = insert 0 (n0OriginalPairs p) := by
  obtain ⟨pos, hp⟩ := k4_assigned graph_ok h hc
  intro p
  refine ⟨src D (pos (n0StarVertex p)), ?_⟩
  ext a
  exact (n0_assigned_source_exact_unrestricted h hc hI pos hp hW
    (n0StarVertex p) (n0StarVertex_mem p) a).trans (n0StarVertex_neighbors p a)

end packScope33
section packScope34

open PEqualNP.Outside.L_meta_2590_aux.H2

lemma H2.n0_triple_supports_impossible {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hi : neighborhoodI ⊆ ineligSet 10 D)
    (hocc : ∀ p : Fin 3, ∃ w, supp 10 D w = insert 0 (n0OriginalPairs p))
    (hlen : D.length ≤ 19) : False := by
  obtain ⟨M, hM, h6, hcard, hfirst, hgood, _⟩ :=
    n0_six_first_marks_of_triple_supports h.1 hocc
  exact n0_first_six_marks_actual_impossible h hc hi M hM (by omega) hcard hfirst hgood hlen

lemma H2.n0_three_exit_impossible {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hi : neighborhoodI ⊆ ineligSet 10 D)
    (hW : (sem_W 10 D (0 : Fin 10)).card ≤ 3) (hlen : D.length ≤ 19) : False :=
  n0_triple_supports_impossible h hc hi (n0_exact_star_triples h hc hi hW) hlen

end packScope34
section packScope35

open PEqualNP.Outside.L_meta_2590_aux.H2

lemma H2.n0_selected_empty_exits_first_marks_budget {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hi : neighborhoodI ⊆ ineligSet 10 D)
    (F : Finset (ℕ × Bool)) (hF : F ⊆ sem_W 10 D (0 : Fin 10))
    (hFe : ∀ e ∈ F, supp 10 D (10 + e.1) = ∅)
    (M : Finset ℕ) (hM : M ⊆ Finset.range D.length)
    (hcard : ∀ j ∈ M, 2 ≤ (supp 10 D (10 + j)).card)
    (hfirst : ∀ j ∈ M, ∀ k < j, supp 10 D (10 + k) ≠ supp 10 D (10 + j))
    (q : ℕ) (hq : q ≤ (stage 6 n0Refs D D.length).2.length) :
    q + 3 + F.card + M.card ≤ D.length + (keptEmitted 6 n0Refs D D.length q ∩ M).card := by
  classical
  let Z := copyBoundary 10 D (zeroWires D neighborhoodResidualRows)
  let A := F.image Prod.fst
  have hFi : Set.InjOn Prod.fst (↑F : Set (ℕ × Bool)) := by
    intro e he f hf hsame
    exact sem_W_gate_injective h.1 0 (hF he) (hF hf) hsame
  have hAc : A.card = F.card := Finset.card_image_of_injOn hFi
  obtain ⟨_, _, _, _, hZc, _⟩ := n0_six_nonemitted h hc hi
  have hZA : Disjoint Z A := by
    apply Finset.disjoint_left.mpr
    intro j hz ha
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
    exact n0_exit_not_copyBoundary h.1 (hF he) hz
  have hZM : Disjoint Z M := by
    apply Finset.disjoint_left.mpr
    intro j hz hm
    have htop : ∀ v, v ∉ neighborhoodI → neighborhoodResidualRows (fun _ => true) v = true := by
      intro v hv
      cases he : neighborhoodResidualRows (fun _ => true) v
      · exact False.elim (hv ((neighborhood_rows_top v).mp he))
      · rfl
    have hdis : Disjoint (supp 10 D (10 + j)) neighborhoodI := by
      apply Finset.disjoint_left.mpr
      intro v hv hvi
      have hp := sem_inelig_pure graph_ok h.1 hc (hi hvi) hv
      have hh := hcard j hm
      rw [hp, Finset.card_singleton] at hh
      omega
    exact first_support_gate_not_copyBoundary h.1 neighborhoodResidualRows neighborhoodI
      (fun _ => true) htop (Finset.mem_range.mp (hM hm)) (hcard j hm) hdis
      rfl (hfirst j hm) hz
  have hAM : Disjoint A M := by
    apply Finset.disjoint_left.mpr
    intro j ha hm
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
    have hh := hcard _ hm
    rw [hFe e he, Finset.card_empty] at hh
    omega
  have hsub : Z ∪ A ⊆ Finset.range D.length := by
    intro j hj
    rcases Finset.mem_union.mp hj with hz | ha
    · exact (Finset.mem_filter.mp hz).1
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
      exact Finset.mem_range.mpr (sem_mem_W.mp (hF he)).1
  have hno : ∀ j ∈ Z ∪ A, (stage 6 n0Refs D (j + 1)).2 = (stage 6 n0Refs D j).2 := by
    intro j hj
    rcases Finset.mem_union.mp hj with hz | ha
    · exact n0_noemit_copyBoundary h.1 hz
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
      exact n0_exit_noemit h.1 (hF he)
  have hdis : Disjoint M (Z ∪ A) :=
    (Finset.disjoint_union_left.mpr ⟨hZM, hAM⟩).symm
  have hb := keptEmitted_marked_budget 6 n0Refs D D.length q hq (Z ∪ A) M hsub hM hdis hno
  rw [Finset.card_union_of_disjoint hZA, hAc] at hb
  dsimp only [Z] at hb
  omega

lemma H2.n0_selected_empty_exits_virtual_budget {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hi : neighborhoodI ⊆ ineligSet 10 D)
    (F : Finset (ℕ × Bool)) (hF : F ⊆ sem_W 10 D (0 : Fin 10))
    (hFe : ∀ e ∈ F, supp 10 D (10 + e.1) = ∅)
    (M : Finset ℕ) (hM : M ⊆ Finset.range D.length)
    (hcard : ∀ j ∈ M, 2 ≤ (supp 10 D (10 + j)).card)
    (hfirst : ∀ j ∈ M, ∀ k < j, supp 10 D (10 + k) ≠ supp 10 D (10 + j))
    (t : ℕ) (hcost : t + 3 ≤ F.card) (hmarks : 6 ≤ M.card + t)
    (q : ℕ) (hq : q ≤ (stage 6 n0Refs D D.length).2.length) :
    q + 12 ≤ D.length + (keptEmitted 6 n0Refs D D.length q ∩ M).card := by
  have hb := n0_selected_empty_exits_first_marks_budget h hc hi F hF hFe M hM hcard hfirst q hq
  omega

end packScope35
section packScope36

open PEqualNP.Outside.L_meta_2590_aux.H2

lemma H2.n0_selected_empty_exits_virtual_impossible {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hi : neighborhoodI ⊆ ineligSet 10 D)
    (F : Finset (ℕ × Bool)) (hF : F ⊆ sem_W 10 D (0 : Fin 10))
    (hFe : ∀ e ∈ F, supp 10 D (10 + e.1) = ∅)
    (M : Finset ℕ) (hM : M ⊆ Finset.range D.length)
    (hcard : ∀ j ∈ M, 2 ≤ (supp 10 D (10 + j)).card)
    (hfirst : ∀ j ∈ M, ∀ k < j, supp 10 D (10 + k) ≠ supp 10 D (10 + j))
    (hgood : ∀ j ∈ M, (0 : Fin 10) ∈ supp 10 D (10 + j) ∨
      ∃ p : Fin 3, supp 10 D (10 + j) = n0OriginalPairs p)
    (t : ℕ) (hcost : t + 3 ≤ F.card) (hmarks : 6 ≤ M.card + t)
    (hlen : D.length ≤ 19) : False := by
  obtain ⟨q, _, hq, _, _, _, hcorrect, _⟩ := n0_c6_output_prefix hc
  have hunique : ∀ i ∈ M, ∀ j ∈ M, ∀ p : Fin 3,
      supp 10 D (10 + i) = n0OriginalPairs p →
      supp 10 D (10 + j) = n0OriginalPairs p → i = j := by
    intro i hiM j hjM p hip hjp
    by_contra hne
    rcases lt_or_gt_of_ne hne with hij | hji
    · exact hfirst j hjM i hij (hip.trans hjp.symm)
    · exact hfirst i hiM j hji (hjp.trans hip.symm)
  have hlower := n0_retained_marks_actual_bound h.1 q hq hcorrect M hgood hunique
  have hupper := n0_selected_empty_exits_virtual_budget h hc hi F hF hFe M hM hcard hfirst
    t hcost hmarks q hq
  omega

end packScope36

lemma H2.n0_val_append_prefix (D tail : Dag) (x : Fin 10 → Bool)
    (w : ℕ) (hw : w < 10 + D.length) :
    val (D ++ tail) x w = val D x w := by
  unfold val
  rw [wl_append]
  exact wl_getD_lt tail (wl D (List.ofFn x)) w (by simpa [wl_length] using hw)

lemma H2.n0_supp_append_prefix (D tail : Dag) (w : ℕ)
    (hw : w < 10 + D.length) :
    supp 10 (D ++ tail) w = supp 10 D w := by
  ext x
  simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [n0_val_append_prefix D tail (single x) w hw]

lemma H2.n0_virtual_triples_impossible {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hi : neighborhoodI ⊆ ineligSet 10 D)
    (F : Finset (ℕ × Bool)) (hF : F ⊆ sem_W 10 D (0 : Fin 10))
    (hFe : ∀ e ∈ F, supp 10 D (10 + e.1) = ∅)
    (tail : Dag) (hE : Strict 10 (D ++ tail))
    (hocc : ∀ p : Fin 3, ∃ w, supp 10 (D ++ tail) w = insert 0 (n0OriginalPairs p))
    (hcost : tail.length + 3 ≤ F.card) (hlen : D.length ≤ 19) : False := by
  classical
  obtain ⟨M, hM, h6, hcard, hfirst, hgood, _⟩ :=
    n0_six_first_marks_of_triple_supports hE hocc
  let K := M.filter (fun j => j < D.length)
  have hK : ∀ j ∈ K, j ∈ M ∧ j < D.length := fun j hj => Finset.mem_filter.mp hj
  have hKvalid : K ⊆ Finset.range D.length := fun j hj => Finset.mem_range.mpr (hK j hj).2
  have hcut : 6 ≤ K.card + tail.length := by
    let V := M.filter (fun j => ¬ j < D.length)
    have hV : V ⊆ Finset.Ico D.length (D.length + tail.length) := by
      intro j hj
      obtain ⟨hjM, hjd⟩ := Finset.mem_filter.mp hj
      have hjb := Finset.mem_range.mp (hM hjM)
      simp only [List.length_append] at hjb
      exact Finset.mem_Ico.mpr ⟨by omega, hjb⟩
    have hvcard : V.card ≤ tail.length := by
      have hh := Finset.card_le_card hV
      simpa using hh
    have hsplit := Finset.card_filter_add_card_filter_not (s := M) (fun j => j < D.length)
    change K.card + V.card = M.card at hsplit
    omega
  apply n0_selected_empty_exits_virtual_impossible h hc hi F hF hFe K hKvalid
    (fun j hj => ?_) (fun j hj k hk => ?_) (fun j hj => ?_) tail.length hcost hcut hlen
  · rw [← n0_supp_append_prefix D tail (10+j) (by have := (hK j hj).2; omega)]
    exact hcard j (hK j hj).1
  · intro heq
    apply hfirst j (hK j hj).1 k hk
    rw [n0_supp_append_prefix D tail (10+k) (by have := (hK j hj).2; omega),
      n0_supp_append_prefix D tail (10+j) (by have := (hK j hj).2; omega)]
    exact heq
  · have hg := hgood j (hK j hj).1
    rw [n0_supp_append_prefix D tail (10+j) (by have := (hK j hj).2; omega)] at hg
    exact hg

end PEqualNP.Outside.L_meta_2590_aux

namespace PEqualNP.Outside.L_meta_2590_aux.H2

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

@[local simp] lemma n0_gop_true (a b : Bool) : gop true a b = (a && b) := gop_true a b
@[local simp] lemma n0_gop_false (a b : Bool) : gop false a b = (a || b) := gop_false a b

theorem live_reaches_out (h : StrictLive n D) (w : ℕ) (hw : w < n + D.length) :
    Relation.ReflTransGen (fun a b => b < n + D.length ∧ n ≤ b ∧
      (opA D (b - n) = a ∨ opB D (b - n) = a)) w (outW n D) := by
  obtain ⟨hS, hL, -⟩ := h
  generalize hk : n + D.length - w = k
  induction k using Nat.strong_induction_on generalizing w with
  | _ k ih =>
    by_cases hlast : w + 1 = n + D.length
    · have hw2 : w = outW n D := by unfold outW; omega
      rw [hw2]
    · obtain ⟨j, hj⟩ := Finset.card_pos.mp (hL w (by omega))
      simp only [readers, Finset.mem_filter, Finset.mem_range] at hj
      have hs := hS j hj.1
      refine Relation.ReflTransGen.head (b := n + j) ⟨by omega, by omega, ?_⟩
        (ih (n + D.length - (n + j)) (by omega) (n + j) (by omega) rfl)
      simpa using hj.2

theorem sem_ins_ge (v : Fin n) (x : Fin n → Bool) : ∀ i, x i = true → sem_ins v x i = true := by
  intro i hi; simp [sem_ins, hi]

theorem sem_src_ne (hS : Strict n D) {j : ℕ} (hj : j < D.length) (s : Bool) :
    src D (j, s) ≠ src D (j, !s) := by
  obtain ⟨-, -, hne⟩ := hS j hj
  cases s
  · simpa [src] using hne
  · simpa [src] using hne.symm

theorem sem_step_iff {a b : ℕ} : sem_step n D a b ↔
    ∃ j s, j < D.length ∧ b = n + j ∧ src D (j, s) = a := by
  constructor
  · rintro ⟨h1, h2, h3 | h3⟩
    · exact ⟨b - n, false, by omega, by omega, by rw [sb_src_false]; exact h3⟩
    · exact ⟨b - n, true, by omega, by omega, by rw [sb_src_true]; exact h3⟩
  · rintro ⟨j, s, hj, rfl, rfl⟩
    refine ⟨by omega, by omega, ?_⟩
    rw [Nat.add_sub_cancel_left]
    cases s
    · exact Or.inl (sb_src_false j).symm
    · exact Or.inr (sb_src_true j).symm

theorem sem_step_lt (hS : Strict n D) {a b : ℕ} (h : sem_step n D a b) : a < b := by
  obtain ⟨h1, h2, h3⟩ := h
  have := hS (b - n) (by omega)
  omega

theorem sem_rtg_le (hS : Strict n D) {R : ℕ → ℕ → Prop} (hR : ∀ a b, R a b → sem_step n D a b)
    {a b : ℕ} (h : Relation.ReflTransGen R a b) : a ≤ b := by
  induction h with
  | refl => exact le_refl _
  | tail _ hbc ih => exact le_trans ih (le_of_lt (sem_step_lt hS (hR _ _ hbc)))

theorem sem_ind_single (a : Fin n) : sem_ind ({a} : Finset (Fin n)) = single a := by
  funext k; simp [sem_ind, single]

theorem sem_val_gate_src (hS : Strict n D) (x : Fin n → Bool) {j : ℕ} (hj : j < D.length)
    (s : Bool) : val D x (n + j) =
      gop (tag D j) (val D x (src D (j, s))) (val D x (src D (j, !s))) := by
  rw [val_gate hS x j hj]
  cases s
  · simp [src]
  · cases tag D j <;> simp [src, Bool.and_comm, Bool.or_comm]

theorem sem_ins_ind_edge (hG : sem_Gr G) {i : Fin n} {S : Finset (Fin n)}
    (h : sem_Edge G (sem_ins i (sem_ind S))) :
    (∃ a ∈ S, G i a) ∨ ∃ a ∈ S, ∃ b ∈ S, G a b := by
  obtain ⟨u, v, huv, hu, hv⟩ := h
  simp only [sem_ins, sem_ind, Bool.or_eq_true, decide_eq_true_eq] at hu hv
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · rw [hu, hv] at huv; exact absurd huv (hG.2.1 i)
  · rw [hu] at huv; exact Or.inl ⟨v, hv, huv⟩
  · rw [hv] at huv; exact Or.inl ⟨u, hu, hG.1 _ _ huv⟩
  · exact Or.inr ⟨u, hu, v, hv, huv⟩

theorem sem_chain_dom_at (hS : Strict n D) {v b t : ℕ} (h : sem_Chain n D v b) (hbt : b ≤ t) :
    b = v ∨ ¬ Relation.ReflTransGen (fun a c => sem_step n D a c ∧ c ≠ b) v t := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Or.inl rfl
  | @head a c hstep hrest ih =>
    by_cases hba : b = a
    · exact Or.inl hba
    · right
      intro hp
      rcases Relation.ReflTransGen.cases_head hp with heq | ⟨c', hs, hrest'⟩
      · have h1 := sem_step_lt hS hstep.1
        have h2 := sem_rtg_le hS (fun _ _ hab => hab.1) hrest
        omega
      · have hcc : c = c' := sem_step_unique hstep.1 hs.1 hstep.2
        subst hcc
        rcases ih with rfl | ih
        · exact hs.2 rfl
        · exact ih hrest'

theorem sem_dom_eq_at (hS : Strict n D) (x y : Fin n → Bool) (v : Fin n)
    (hxy : ∀ k, k ≠ v → x k = y k) (b t : ℕ)
    (hdom : b = v.val ∨ ¬ Relation.ReflTransGen (fun a c => sem_step n D a c ∧ c ≠ b) v.val t)
    (hb : val D x b = val D y b) : val D x t = val D y t := by
  by_contra hne
  rcases hdom with rfl | hdom
  · rw [val_input D x _ v.isLt, val_input D y _ v.isLt] at hb
    have hxy2 : x = y := by
      funext k
      by_cases hk : k = v
      · rw [hk]; exact hb
      · exact hxy k hk
    exact hne (by rw [hxy2])
  · exact hdom (sem_rtg_mono
      (fun a c h => ⟨h.1, fun hc => h.2 (by rw [hc]; exact hb)⟩)
      (sem_changed_path hS x y v hxy _ hne))

theorem sem_chain_fork (hS : Strict n D) {a c q : ℕ} (hc : sem_Chain n D a c)
    (hq : Relation.ReflTransGen (sem_step n D) a q) :
    Relation.ReflTransGen (sem_step n D) c q ∨ (sem_Chain n D q c ∧ q ≠ c) := by
  revert hq
  induction hc using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun hq => Or.inl hq
  | @head a a' hstep hrest ih =>
    intro hq
    rcases Relation.ReflTransGen.cases_head hq with heq | ⟨a'', hs, hrest'⟩
    · right
      have h1 := sem_step_lt hS hstep.1
      have h2 := sem_rtg_le hS (fun _ _ hab => hab.1) hrest
      refine ⟨?_, by omega⟩
      rw [← heq]
      exact Relation.ReflTransGen.head hstep hrest
    · have hcc : a' = a'' := sem_step_unique hstep.1 hs hstep.2
      subst hcc
      exact ih hrest'

theorem sem_sibling_indep (hS : Strict n D) (v : Fin n) {j : ℕ} (hj : j < D.length) (s : Bool)
    (hch : sem_Chain n D v.val (src D (j, !s))) (hf : fanout D (src D (j, !s)) = 1)
    (x y : Fin n → Bool) (hxy : ∀ k, k ≠ v → x k = y k) :
    val D x (src D (j, s)) = val D y (src D (j, s)) := by
  by_contra hne
  have hp : Relation.ReflTransGen (sem_step n D) v.val (src D (j, s)) :=
    sem_rtg_mono (fun _ _ h => h.1) (sem_changed_path hS x y v hxy _ hne)
  have hstepc : sem_step n D (src D (j, !s)) (n + j) := sem_step_src hj (!s)
  have hstepq : sem_step n D (src D (j, s)) (n + j) := sem_step_src hj s
  have hlt1 := sem_src_lt hS hj s
  have hlt2 := sem_src_lt hS hj (!s)
  rcases sem_chain_fork hS hch hp with h1 | ⟨h1, h2⟩
  · rcases Relation.ReflTransGen.cases_head h1 with heq | ⟨c', hs, hrest⟩
    · exact sem_src_ne hS hj s heq.symm
    · have hcc : n + j = c' := sem_step_unique hstepc hs hf
      subst hcc
      have := sem_rtg_le hS (fun _ _ h => h) hrest
      omega
  · rcases Relation.ReflTransGen.cases_head h1 with heq | ⟨q', hs, hrest⟩
    · exact h2 heq
    · have hcc : n + j = q' := sem_step_unique hstepq hs.1 hs.2
      subst hcc
      have := sem_rtg_le hS (fun _ _ h => h.1) hrest
      omega

theorem sem_dom_split (hS : Strict n D) (hC : sem_Comp n G D) (x : Fin n → Bool) (v : Fin n)
    (b : ℕ) (hdom : sem_Dom n D b v.val) (h0 : ¬ sem_Edge G x) (h1 : sem_Edge G (sem_ins v x)) :
    val D x b = false ∧ val D (sem_ins v x) b = true := by
  have hne : val D x b ≠ val D (sem_ins v x) b := by
    intro heq
    have h2 := sem_dom_eq hS x _ v (sem_ins_agree v x) b hdom heq
    exact h0 ((hC x).mp (by rw [h2]; exact (hC _).mpr h1))
  have hmono := val_mono hS x (sem_ins v x) (sem_ins_ge v x) b
  cases hx : val D x b
  · refine ⟨rfl, ?_⟩
    cases hy : val D (sem_ins v x) b
    · exact absurd (hx.trans hy.symm) hne
    · rfl
  · exact absurd (hx.trans (hmono hx).symm) hne

theorem sem_factor (hS : Strict n D) (i : Fin n) (w : ℕ) (hch : sem_Chain n D i.val w)
    (Bs N : Finset (Fin n)) (hN : N ⊆ Bs)
    (h0 : val D (sem_ins i (sem_ind (Bs \ N))) w = false)
    (h1 : ∀ a ∈ N, val D (sem_ins i (sem_ind {a})) w = true)
    (hz : ∀ a ∈ N, val D (sem_ind {a}) w = false) :
    ∃ j s, j < D.length ∧ tag D j = true ∧ n + j ≤ w ∧
      sem_Chain n D i.val (src D (j, !s)) ∧ supp n D (src D (j, s)) ∩ Bs = N := by
  have hJ : ∀ c, sem_Chain n D i.val c → (val D (sem_ins i (sem_ind (Bs \ N))) c = true ∨
      ∃ j s, j < D.length ∧ tag D j = true ∧ n + j ≤ c ∧ sem_Chain n D i.val (src D (j, !s)) ∧
        fanout D (src D (j, !s)) = 1 ∧ val D (sem_ind (Bs \ N)) (src D (j, s)) = false) := by
    intro c hc
    induction hc with
    | refl => left; rw [val_input D _ _ i.isLt]; exact sem_ins_self i _
    | tail hab hbc ih =>
      obtain ⟨j, s, hj, rfl, rfl⟩ := sem_step_iff.mp hbc.1
      have hlt := sem_src_lt hS hj s
      rcases ih with hy | ⟨j', s', hj', ht', hle, hc', hf', hv'⟩
      · cases ht : tag D j
        · left
          rw [sem_val_gate_src hS _ hj s, ht, gop_false, hy]
          rfl
        · by_cases hq : val D (sem_ins i (sem_ind (Bs \ N))) (src D (j, !s)) = true
          · left
            rw [sem_val_gate_src hS _ hj s, ht, gop_true, hy, hq]
            rfl
          · right
            refine ⟨j, !s, hj, ht, le_refl _, by rw [Bool.not_not]; exact hab,
              by rw [Bool.not_not]; exact hbc.2, ?_⟩
            by_contra hc2
            rw [Bool.not_eq_false] at hc2
            exact hq (val_mono hS _ _ (sem_ins_ge i _) _ hc2)
      · right
        exact ⟨j', s', hj', ht', by omega, hc', hf', hv'⟩
  rcases hJ w hch with hy | ⟨j, s, hj, ht, hle, hc, hf, hv⟩
  · rw [h0] at hy
    exact absurd hy Bool.false_ne_true
  · refine ⟨j, s, hj, ht, hle, hc, ?_⟩
    have hchg : sem_Chain n D i.val (n + j) :=
      Relation.ReflTransGen.tail hc ⟨sem_step_src hj (!s), hf⟩
    ext a
    rw [Finset.mem_inter]
    constructor
    · rintro ⟨ha1, ha2⟩
      by_contra haN
      have := sem_val_of_supp hS ha1 (x := sem_ind (Bs \ N))
        (by simp [sem_ind, ha2, haN])
      rw [hv] at this
      exact Bool.false_ne_true this
    · intro haN
      refine ⟨?_, hN haN⟩
      have hgne : val D (sem_ind {a}) (n + j) ≠ val D (sem_ins i (sem_ind {a})) (n + j) := by
        intro heq
        have h2 := sem_dom_eq_at hS _ _ i (sem_ins_agree i (sem_ind {a})) (n + j) w
          (sem_chain_dom_at hS hchg hle) heq
        rw [hz a haN, h1 a haN] at h2
        exact Bool.false_ne_true h2
      have hgy : val D (sem_ins i (sem_ind {a})) (n + j) = true := by
        by_contra hc2
        rw [Bool.not_eq_true] at hc2
        apply hgne
        rw [hc2]
        by_contra hc3
        rw [Bool.not_eq_false] at hc3
        rw [val_mono hS _ _ (sem_ins_ge i _) _ hc3] at hc2
        exact Bool.noConfusion hc2
      rw [sem_val_gate_src hS _ hj s, ht, gop_true, Bool.and_eq_true] at hgy
      have hind := sem_sibling_indep hS i hj s hc hf _ _ (sem_ins_agree i (sem_ind {a}))
      rw [hgy.1, sem_ind_single] at hind
      exact mem_supp.mpr hind

theorem sem_exact_at (hS : Strict n D) (i : Fin n) (w : ℕ) (hch : sem_Chain n D i.val w)
    (Bs : Finset (Fin n))
    (h0 : ∀ S : Finset (Fin n), S ⊆ Bs → (∀ a ∈ S, ¬ G i a) →
      val D (sem_ins i (sem_ind S)) w = false)
    (h1 : ∀ a ∈ Bs, G i a →
      val D (sem_ins i (sem_ind {a})) w = true ∧ val D (sem_ind {a}) w = false) :
    ∃ j s, j < D.length ∧ tag D j = true ∧ n + j ≤ w ∧
      sem_Chain n D i.val (src D (j, !s)) ∧
      ∀ a ∈ Bs, (a ∈ supp n D (src D (j, s)) ↔ G i a) := by
  classical
  obtain ⟨j, s, hj, ht, hle, hc, hsupp⟩ := sem_factor hS i w hch Bs (Bs.filter (fun a => G i a))
    (Finset.filter_subset _ _)
    (h0 _ Finset.sdiff_subset (fun a ha hia => by
      rw [Finset.mem_sdiff, Finset.mem_filter] at ha
      exact ha.2 ⟨ha.1, hia⟩))
    (fun a ha => (h1 a (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp ha).2).1)
    (fun a ha => (h1 a (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp ha).2).2)
  refine ⟨j, s, hj, ht, hle, hc, fun a ha => ?_⟩
  constructor
  · intro has
    have : a ∈ supp n D (src D (j, s)) ∩ Bs := Finset.mem_inter.mpr ⟨has, ha⟩
    rw [hsupp, Finset.mem_filter] at this
    exact this.2
  · intro hia
    have : a ∈ Bs.filter (fun a => G i a) := Finset.mem_filter.mpr ⟨ha, hia⟩
    rw [← hsupp] at this
    exact (Finset.mem_inter.mp this).1

theorem sem_branch_empty (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) {i : Fin n}
    (hi : i ∈ ineligSet n D) {b : ℕ} (hch : sem_Chain n D i.val b) (hf : 2 ≤ fanout D b) :
    supp n D b = ∅ := by
  have hsub := sem_dom_pure hG hS hC i b (sem_chain_dom hS hch)
  refine Finset.eq_empty_of_forall_notMem (fun x hx => ?_)
  have h1 := hsub hx
  rw [Finset.mem_singleton] at h1
  have h2 := mem_ineligSet.mp hi b (h1 ▸ hx)
  omega

theorem sem_path_chain {a t : ℕ} (hp : Relation.ReflTransGen (sem_step n D) a t) :
    sem_Chain n D a t ∨ ∃ b, sem_Chain n D a b ∧ 2 ≤ fanout D b := by
  induction hp using Relation.ReflTransGen.head_induction_on with
  | refl => exact Or.inl Relation.ReflTransGen.refl
  | @head a a' hstep _ ih =>
    by_cases hf : fanout D a = 1
    · rcases ih with h1 | ⟨b, h1, h2⟩
      · exact Or.inl (Relation.ReflTransGen.head ⟨hstep, hf⟩ h1)
      · exact Or.inr ⟨b, Relation.ReflTransGen.head ⟨hstep, hf⟩ h1, h2⟩
    · have := sem_step_fanout hstep
      exact Or.inr ⟨a, Relation.ReflTransGen.refl, by omega⟩

theorem sem_bzero_mem (hS : Strict n D) {b : ℕ} (hf : 2 ≤ fanout D b) (he : supp n D b = ∅) :
    b ∈ (inner n D).filter (fun w => ¬ (supp n D w).Nonempty) :=
  Finset.mem_filter.mpr ⟨sb_mem_inner.mpr (lt_of_fanout_pos hS (w := b) (by omega)),
    by rw [he]; exact Finset.not_nonempty_empty⟩

theorem sem_bzero_branch (hS : Strict n D) (hB0 : Bzero n D = 0) {b : ℕ} (hf : 2 ≤ fanout D b) :
    (supp n D b).Nonempty := by
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  have h1 : fanout D b - 1 ≤ ∑ w ∈ (inner n D).filter (fun w => ¬ (supp n D w).Nonempty),
      (fanout D w - 1) :=
    Finset.single_le_sum (f := fun w => fanout D w - 1) (fun _ _ => Nat.zero_le _)
      (sem_bzero_mem hS hf hne)
  unfold Bzero surplusOn at hB0
  omega

theorem sem_noempty_unique (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (hB0 : Bzero n D = 0) {i : Fin n} (hi : i ∈ ineligSet n D) {w : ℕ}
    (hp : Relation.ReflTransGen (sem_step n D) i.val w) : sem_Chain n D i.val w := by
  rcases sem_path_chain hp with h1 | ⟨b, h1, h2⟩
  · exact h1
  · have h3 := sem_bzero_branch h.1 hB0 h2
    rw [sem_branch_empty hG h.1 hC hi h1 h2] at h3
    exact absurd h3 Finset.not_nonempty_empty

theorem sem_noempty_chain_out (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (hB0 : Bzero n D = 0) {i : Fin n} (hi : i ∈ ineligSet n D) :
    sem_Chain n D i.val (outW n D) :=
  sem_noempty_unique hG h hC hB0 hi
    (live_reaches_out h i.val (by have := i.isLt; omega))

theorem sem_exact_nbhd (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    (Bs : Finset (Fin n)) (hBs : ∀ a ∈ Bs, ∀ b ∈ Bs, ¬ G a b) {i : Fin n}
    (hch : sem_Chain n D i.val (outW n D)) :
    ∃ j s, j < D.length ∧ tag D j = true ∧ sem_Chain n D i.val (src D (j, !s)) ∧
      ∀ a ∈ Bs, (a ∈ supp n D (src D (j, s)) ↔ G i a) := by
  obtain ⟨j, s, hj, ht, -, hc, hsupp⟩ := sem_exact_at (G := G) hS i (outW n D) hch Bs
    (fun S hS1 hS2 => by
      by_contra hc
      rw [Bool.not_eq_false] at hc
      rcases sem_ins_ind_edge hG ((hC _).mp hc) with ⟨a, ha, hia⟩ | ⟨a, ha, b, hb, hab⟩
      · exact hS2 a ha hia
      · exact hBs a (hS1 ha) b (hS1 hb) hab)
    (fun a _ hia => by
      constructor
      · exact (hC _).mpr ⟨i, a, hia, sem_ins_self i _, by simp [sem_ins, sem_ind]⟩
      · by_contra hc
        rw [Bool.not_eq_false, sem_ind_single] at hc
        exact sem_single_no_edge hG a ((hC _).mp hc))
  exact ⟨j, s, hj, ht, hc, hsupp⟩

end PEqualNP.Outside.L_meta_2590_aux.H2

namespace PEqualNP.Outside.L_meta_2590_aux.H2.N0Exclusive


abbrev V := Fin 10

def neighbors (v : V) : Nat :=
  [50, 69, 138, 276, 521, 385, 770, 548, 104, 208].getD v.val 0

abbrev Adj (u v : V) : Prop := (neighbors u).testBit v.val = true

def J : Finset V := {1, 4, 5}

def C : Finset V := {2, 3, 6, 7, 8, 9}

def nb (i : V) : Finset V := Finset.univ.filter (Adj i)

def witness (i c : V) : Finset V :=
  if i = 1 then
    if c ∈ ({3, 7} : Finset V) then {1, 3, 7} else {1, 8, 9}
  else if i = 4 then
    if c ∈ ({2, 8} : Finset V) then {4, 2, 8} else {4, 6, 7}
  else if c ∈ ({2, 9} : Finset V) then {5, 2, 9} else {5, 3, 6}

lemma graph_ok : sem_Gr Adj := by
  unfold sem_Gr
  decide +kernel

lemma geometry :
    (∀ i ∈ J, i ≠ 0 ∧ (0 : V) ∈ nb i ∧ (nb i).card = 3) ∧
    (∀ i ∈ J, ∃ c ∈ C, c ∉ nb i) ∧
    (∀ c : V, c = 0 ∨ c ∈ J ∨ c ∈ C) ∧ J.card = 3 := by
  decide +kernel

lemma witness_ok : ∀ i ∈ J, ∀ c ∈ C, c ∉ nb i →
    i ∈ witness i c ∧ c ∈ witness i c ∧
    (∀ a ∈ witness i c, ∀ b ∈ witness i c, ¬ Adj a b) ∧
    (∀ j ∈ J, j ≠ i → ∃ a ∈ witness i c, a ∈ nb j) := by
  decide +kernel

lemma chain_neighbors {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (hz : Bzero 10 D = 0) {i : V} (hi : i ∈ ineligSet 10 D) {g : ℕ} {s : Bool}
    (hg : g < D.length) (ht : tag D g = true)
    (hch : sem_Chain 10 D i.val (src D (g, !s))) :
    nb i ⊆ supp 10 D (src D (g, s)) := by
  have hfpos := sem_step_fanout (sem_step_src (n := 10) (D := D) hg (!s))
  have hf : fanout D (src D (g, !s)) = 1 := by
    by_contra hne
    have htwo : 2 ≤ fanout D (src D (g, !s)) := by omega
    have hnon := sem_bzero_branch h.1 hz htwo
    rw [sem_branch_empty graph_ok h.1 hc hi hch htwo] at hnon
    exact Finset.not_nonempty_empty hnon
  have hgo : sem_Chain 10 D i.val (10 + g) :=
    Relation.ReflTransGen.tail hch ⟨sem_step_src hg (!s), hf⟩
  intro a ha
  have hia : Adj i a := (Finset.mem_filter.mp ha).2
  have htruth := (sem_dom_split h.1 hc (single a) i (10 + g)
    (sem_chain_dom h.1 hgo) (sem_single_no_edge graph_ok a)
    ⟨i, a, hia, sem_ins_self i _, by simp [sem_ins, single]⟩).2
  rw [sem_val_gate_src h.1 _ hg s, ht, gop_true, Bool.and_eq_true] at htruth
  have hind := sem_sibling_indep h.1 i hg s hch hf
    (single a) (sem_ins i (single a)) (sem_ins_agree i (single a))
  exact mem_supp.mpr (hind.trans htruth.1)

noncomputable def family (D : Dag) (i : V) : Finset (ℕ × Bool) := by
  classical
  exact (sem_W 10 D (0 : V)).filter (fun e =>
    sem_Chain 10 D i.val (src D (e.1, !e.2)) ∧
    nb i ⊆ supp 10 D (src D e) ∧
    ∀ j ∈ J, j ≠ i → ¬ nb j ⊆ supp 10 D (src D e))

lemma mem_family {D : Dag} {i : V} {e : ℕ × Bool} :
    e ∈ family D i ↔ e ∈ sem_W 10 D (0 : V) ∧
      sem_Chain 10 D i.val (src D (e.1, !e.2)) ∧
      nb i ⊆ supp 10 D (src D e) ∧
      ∀ j ∈ J, j ≠ i → ¬ nb j ⊆ supp 10 D (src D e) := by
  classical
  simp [family]

lemma family_disjoint (D : Dag) {i j : V} (hi : i ∈ J) (hj : j ∈ J) (hne : i ≠ j) :
    Disjoint (family D i) (family D j) := by
  classical
  apply Finset.disjoint_left.mpr
  intro e hei hej
  exact (mem_family.mp hei).2.2.2 j hj hne.symm (mem_family.mp hej).2.2.1

lemma family_omit_C {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (hz : Bzero 10 D = 0) (hJ : J ⊆ ineligSet 10 D)
    {i c : V} (hi : i ∈ J) (hcC : c ∈ C) (hcN : c ∉ nb i) :
    ∃ e ∈ family D i, c ∉ supp 10 D (src D e) := by
  classical
  obtain ⟨hiA, hcA, hA, hmeet⟩ := witness_ok i hi c hcC hcN
  obtain ⟨g, s, hg, ht, hch, hex⟩ := sem_exact_nbhd graph_ok h.1 hc
    (witness i c) hA (sem_noempty_chain_out graph_ok h hc hz (hJ hi))
  have hn := chain_neighbors h hc hz (hJ hi) hg ht hch
  have hzero : (0 : V) ∈ supp 10 D (src D (g, s)) := hn (geometry.1 i hi).2.1
  have hpure := sem_dom_pure graph_ok h.1 hc i (src D (g, !s))
    (sem_chain_dom h.1 hch)
  have hout : (0 : V) ∉ supp 10 D (10 + g) := by
    intro hh
    have heq := Finset.mem_singleton.mp (hpure (sem_supp_and_sub h.1 hg ht (!s) hh))
    exact (geometry.1 i hi).1 heq.symm
  have havoid : ∀ a ∈ witness i c, a ∉ supp 10 D (src D (g, s)) := by
    intro a ha hmem
    exact hA i hiA a ha ((hex a ha).mp hmem)
  refine ⟨(g, s), mem_family.mpr ⟨sem_mem_W.mpr ⟨hg, hzero, hout⟩, hch, hn, ?_⟩,
    havoid c hcA⟩
  intro j hj hji hsub
  obtain ⟨a, ha, hna⟩ := hmeet j hj hji
  exact havoid a ha (hsub hna)

end PEqualNP.Outside.L_meta_2590_aux.H2.N0Exclusive


namespace PEqualNP.Outside.L_meta_2590_aux.H2.N0Exclusive


lemma family_nonempty {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (hz : Bzero 10 D = 0) (hJ : J ⊆ ineligSet 10 D)
    {i : V} (hi : i ∈ J) : (family D i).Nonempty := by
  obtain ⟨c, hcC, hcN⟩ := geometry.2.1 i hi
  obtain ⟨e, he, _⟩ := family_omit_C h hc hz hJ hi hcC hcN
  exact ⟨e, he⟩

lemma family_source_avoids_J {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (hJ : J ⊆ ineligSet 10 D) {i c : V} {e : ℕ × Bool}
    (he : e ∈ family D i) (hcJ : c ∈ J) : c ∉ supp 10 D (src D e) := by
  intro hmem
  have hsingle := sem_inelig_pure graph_ok h.1 hc (hJ hcJ) hmem
  have hzero := (sem_mem_W.mp (mem_family.mp he).1).2.1
  rw [hsingle, Finset.mem_singleton] at hzero
  exact (geometry.1 c hcJ).1 hzero.symm

lemma family_omit {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (hz : Bzero 10 D = 0) (hJ : J ⊆ ineligSet 10 D)
    {i c : V} (hi : i ∈ J) (hcN : c ∉ nb i) :
    ∃ e ∈ family D i, c ∉ supp 10 D (src D e) := by
  rcases geometry.2.2.1 c with rfl | hcJ | hcC
  · exact False.elim (hcN (geometry.1 i hi).2.1)
  · obtain ⟨e, he⟩ := family_nonempty h hc hz hJ hi
    exact ⟨e, he, family_source_avoids_J h hc hJ he hcJ⟩
  · exact family_omit_C h hc hz hJ hi hcC hcN

lemma family_intersection {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (hz : Bzero 10 D = 0) (hJ : J ⊆ ineligSet 10 D)
    {i : V} (hi : i ∈ J) (c : V) :
    c ∈ nb i ↔ ∀ e ∈ family D i, c ∈ supp 10 D (src D e) := by
  constructor
  · intro hcN e he
    exact (mem_family.mp he).2.2.1 hcN
  · intro hall
    by_contra hcN
    obtain ⟨e, he, hce⟩ := family_omit h hc hz hJ hi hcN
    exact hce (hall e he)

lemma family_output_empty {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (hJ : J ⊆ ineligSet 10 D) {i : V} (hi : i ∈ J) {e : ℕ × Bool}
    (he : e ∈ family D i) : supp 10 D (10 + e.1) = ∅ := by
  have hW := (mem_family.mp he).1
  have hj := (sem_mem_W.mp hW).1
  have ht := sem_W_and h.1 hW
  have hpure := sem_dom_pure graph_ok h.1 hc i (src D (e.1, !e.2))
    (sem_chain_dom h.1 (mem_family.mp he).2.1)
  apply Finset.eq_empty_of_forall_notMem
  intro c hcout
  have hci := Finset.mem_singleton.mp (hpure (sem_supp_and_sub h.1 hj ht (!e.2) hcout))
  subst c
  exact family_source_avoids_J h hc hJ he hi (sem_supp_and_sub h.1 hj ht e.2 hcout)

noncomputable def allArcs (D : Dag) : Finset (ℕ × Bool) := J.biUnion (family D)

lemma allArcs_subset (D : Dag) : allArcs D ⊆ sem_W 10 D (0 : V) := by
  classical
  intro e he
  obtain ⟨i, _, hei⟩ := Finset.mem_biUnion.mp he
  exact (mem_family.mp hei).1

lemma allArcs_card (D : Dag) : (allArcs D).card = ∑ i ∈ J, (family D i).card := by
  classical
  apply Finset.card_biUnion
  intro i hi j hj hne
  exact family_disjoint D hi hj hne

lemma virtual_cost_eq {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (hz : Bzero 10 D = 0) (hJ : J ⊆ ineligSet 10 D) :
    (∑ i ∈ J, ((family D i).card - 1)) + 3 = (allArcs D).card := by
  classical
  have hpos (i : V) (hi : i ∈ J) : 1 ≤ (family D i).card :=
    Finset.card_pos.mpr (family_nonempty h hc hz hJ hi)
  calc
    (∑ i ∈ J, ((family D i).card - 1)) + 3 =
        (∑ i ∈ J, ((family D i).card - 1)) + (∑ _i ∈ J, (1 : Nat)) := by
      simp only [Finset.sum_const, smul_eq_mul, mul_one, geometry.2.2.2]
    _ = ∑ i ∈ J, (((family D i).card - 1) + 1) :=
      (Finset.sum_add_distrib).symm
    _ = ∑ i ∈ J, (family D i).card :=
      Finset.sum_congr rfl (fun i hi => Nat.sub_add_cancel (hpos i hi))
    _ = (allArcs D).card := (allArcs_card D).symm

lemma virtual_cost_le {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (hz : Bzero 10 D = 0) (hJ : J ⊆ ineligSet 10 D) :
    (∑ i ∈ J, ((family D i).card - 1)) ≤ (sem_W 10 D (0 : V)).card - 3 := by
  have heq := virtual_cost_eq h hc hz hJ
  have hle := Finset.card_le_card (allArcs_subset D)
  omega

lemma zero_exit_gate_injective {D : Dag} (hS : Strict 10 D) :
    Set.InjOn Prod.fst (↑(sem_W 10 D (0 : V)) : Set (ℕ × Bool)) := by
  intro e he f hf heq
  rcases sem_same_gate heq with hfe | hfe
  · exact hfe.symm
  · subst f
    obtain ⟨g, s⟩ := e
    have hg := (sem_mem_W.mp he).1
    have ht := sem_W_and hS he
    have ha := (sem_mem_W.mp he).2.1
    have hb := (sem_mem_W.mp hf).2.1
    have hnot := (sem_mem_W.mp he).2.2
    exfalso
    apply hnot
    rw [sem_supp_and hS hg ht]
    cases s
    · exact Finset.mem_inter.mpr ⟨ha, hb⟩
    · exact Finset.mem_inter.mpr ⟨hb, ha⟩

lemma allArcs_gate_card {D : Dag} (hS : Strict 10 D) :
    ((allArcs D).image Prod.fst).card = (allArcs D).card := by
  classical
  apply Finset.card_image_of_injOn
  intro e he f hf heq
  exact zero_exit_gate_injective hS (allArcs_subset D he) (allArcs_subset D hf) heq

end PEqualNP.Outside.L_meta_2590_aux.H2.N0Exclusive

namespace PEqualNP.Outside.L_meta_2590_aux.H2


lemma val_append_prefix (n : ℕ) (D tail : Dag) (x : Fin n → Bool)
    (w : ℕ) (hw : w < n + D.length) :
    val (D ++ tail) x w = val D x w := by
  unfold val
  rw [wl_append]
  exact wl_getD_lt tail (wl D (List.ofFn x)) w (by simpa [wl_length] using hw)

lemma supp_append_prefix (n : ℕ) (D tail : Dag) (w : ℕ)
    (hw : w < n + D.length) :
    supp n (D ++ tail) w = supp n D w := by
  ext x
  simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [val_append_prefix n D tail (single x) w hw]

lemma tag_append_prefix (D tail : Dag) (j : ℕ) (hj : j < D.length) :
    tag (D ++ tail) j = tag D j := by
  simp [tag, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

namespace VirtualAnd


lemma append_and_family {n : ℕ} {D : Dag} (hS : Strict n D) (z : Fin n)
    (F : Finset ℕ) (hne : F.Nonempty)
    (hvalid : ∀ a ∈ F, a < n + D.length)
    (hz : ∀ a ∈ F, z ∈ supp n D a) :
    ∃ tail : Dag, ∃ w : ℕ,
      Strict n (D ++ tail) ∧ tail.length + 1 = F.card ∧
      w < n + (D ++ tail).length ∧ (w ∈ F ∨ n + D.length ≤ w) ∧
      (∀ x : Fin n → Bool, val (D ++ tail) x w = true ↔ ∀ a ∈ F, val D x a = true) ∧
      ∀ j, D.length ≤ j → j < (D ++ tail).length →
        tag (D ++ tail) j = true ∧ z ∈ supp n (D ++ tail) (n + j) := by
  classical
  induction F using Finset.induction_on with
  | empty => exact False.elim (Finset.not_nonempty_empty hne)
  | @insert a F ha ih =>
    by_cases hF : F.Nonempty
    · obtain ⟨tail, w, hE, hcost, hw, horigin, hval, hvirtual⟩ :=
        ih hF (fun u hu => hvalid u (Finset.mem_insert_of_mem hu))
          (fun u hu => hz u (Finset.mem_insert_of_mem hu))
      let E := D ++ tail
      have haD : a < n + D.length := hvalid a (Finset.mem_insert_self _ _)
      have haE : a < n + E.length := by simp only [E, List.length_append]; omega
      have hwE : w < n + E.length := hw
      have hwa : w ≠ a := by
        intro heq
        rcases horigin with hwF | hwnew
        · exact ha (heq ▸ hwF)
        · omega
      have hnext : Strict n (E ++ [(true, w, a)]) := na_strict_snoc hE true w a hwE haE hwa
      have hgate (x : Fin n → Bool) :
          val (E ++ [(true, w, a)]) x (n + E.length) = (val E x w && val D x a) := by
        rw [val_gate hnext x E.length (by simp)]
        simp only [tag, opA, opB, na_getD_snoc, gop_true]
        rw [val_append_prefix n E _ x w hwE, val_append_prefix n E _ x a haE,
          val_append_prefix n D tail x a haD]
      have hznew : z ∈ supp n (E ++ [(true, w, a)]) (n + E.length) := by
        rw [mem_supp, hgate, Bool.and_eq_true]
        exact ⟨(hval (single z)).mpr (fun u hu => mem_supp.mp (hz u (Finset.mem_insert_of_mem hu))),
          mem_supp.mp (hz a (Finset.mem_insert_self _ _))⟩
      refine ⟨tail ++ [(true, w, a)], n + E.length, ?_⟩
      simp only [← List.append_assoc]
      refine ⟨hnext, ?_, ?_, Or.inr ?_, ?_, ?_⟩
      · rw [List.length_append, List.length_singleton, Finset.card_insert_of_notMem ha]
        omega
      · simp only [E, List.length_append, List.length_singleton]
        omega
      · simp only [E, List.length_append]
        omega
      · intro x
        rw [hgate, Bool.and_eq_true, hval]
        constructor
        · rintro ⟨hFx, hax⟩ u hu
          rcases Finset.mem_insert.mp hu with rfl | hu
          · exact hax
          · exact hFx u hu
        · intro hall
          exact ⟨fun u hu => hall u (Finset.mem_insert_of_mem hu), hall a (Finset.mem_insert_self _ _)⟩
      · intro j hjold hjnew
        change j < (E ++ [(true, w, a)]).length at hjnew
        by_cases hjE : j < E.length
        · obtain ⟨ht, hzs⟩ := hvirtual j hjold hjE
          exact ⟨(tag_append_prefix E _ j hjE).trans ht,
            (supp_append_prefix n E _ (n + j) (by omega)).symm ▸ hzs⟩
        · have hj : j = E.length := by
            simp only [List.length_append, List.length_singleton] at hjnew
            omega
          subst j
          refine ⟨?_, hznew⟩
          change tag (E ++ [(true, w, a)]) E.length = true
          simp only [tag, na_getD_snoc]
    · have hFempty : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
      subst F
      refine ⟨[], a, ?_⟩
      simp only [List.append_nil]
      refine ⟨hS, by simp, hvalid a (by simp), Or.inl (by simp), ?_, ?_⟩
      · intro x
        simp
      · intro j hj hj'
        omega

lemma append_and_family_support {n : ℕ} {D : Dag} (hS : Strict n D) (z : Fin n)
    (F : Finset ℕ) (hne : F.Nonempty)
    (hvalid : ∀ a ∈ F, a < n + D.length)
    (hz : ∀ a ∈ F, z ∈ supp n D a) :
    ∃ tail : Dag, ∃ w : ℕ,
      Strict n (D ++ tail) ∧ tail.length + 1 = F.card ∧ w < n + (D ++ tail).length ∧
      (∀ v : Fin n, v ∈ supp n (D ++ tail) w ↔ ∀ a ∈ F, v ∈ supp n D a) ∧
      ∀ j, D.length ≤ j → j < (D ++ tail).length →
        tag (D ++ tail) j = true ∧ z ∈ supp n (D ++ tail) (n + j) := by
  obtain ⟨tail, w, hE, hcost, hw, _, hval, hvirtual⟩ := append_and_family hS z F hne hvalid hz
  refine ⟨tail, w, hE, hcost, hw, ?_, hvirtual⟩
  intro v
  simpa only [mem_supp] using hval (single v)

end VirtualAnd

namespace VirtualAnd


lemma append_three_and_families_support {n : ℕ} {D : Dag} (hS : Strict n D)
    (z : Fin n) (F : Fin 3 → Finset ℕ) (hne : ∀ i, (F i).Nonempty)
    (hvalid : ∀ i, ∀ a ∈ F i, a < n + D.length)
    (hz : ∀ i, ∀ a ∈ F i, z ∈ supp n D a) :
    ∃ tail : Dag, ∃ w : Fin 3 → ℕ,
      Strict n (D ++ tail) ∧ tail.length + 3 = ∑ i, (F i).card ∧
      (∀ i, w i < n + (D ++ tail).length) ∧
      (∀ i v, v ∈ supp n (D ++ tail) (w i) ↔ ∀ a ∈ F i, v ∈ supp n D a) ∧
      ∀ j, D.length ≤ j → j < (D ++ tail).length →
        tag (D ++ tail) j = true ∧ z ∈ supp n (D ++ tail) (n + j) := by
  classical
  obtain ⟨t0, w0, hs0, hc0, hw0, hp0, hv0⟩ :=
    append_and_family_support hS z (F 0) (hne 0) (hvalid 0) (hz 0)
  let E0 := D ++ t0
  change w0 < n + E0.length at hw0
  have hvalid0 : ∀ i, ∀ a ∈ F i, a < n + E0.length := by
    intro i a ha
    have := hvalid i a ha
    simp only [E0, List.length_append]
    omega
  have hz0 : ∀ i, ∀ a ∈ F i, z ∈ supp n E0 a := by
    intro i a ha
    rw [supp_append_prefix n D t0 a (hvalid i a ha)]
    exact hz i a ha
  obtain ⟨t1, w1, hs1, hc1, hw1, hp1, hv1⟩ :=
    append_and_family_support (D := E0) hs0 z (F 1) (hne 1) (hvalid0 1) (hz0 1)
  let E1 := E0 ++ t1
  change w1 < n + E1.length at hw1
  have hvalid1 : ∀ i, ∀ a ∈ F i, a < n + E1.length := by
    intro i a ha
    have := hvalid0 i a ha
    simp only [E1, List.length_append]
    omega
  have hz1 : ∀ i, ∀ a ∈ F i, z ∈ supp n E1 a := by
    intro i a ha
    rw [supp_append_prefix n E0 t1 a (hvalid0 i a ha)]
    exact hz0 i a ha
  obtain ⟨t2, w2, hs2, hc2, hw2, hp2, hv2⟩ :=
    append_and_family_support (D := E1) hs1 z (F 2) (hne 2) (hvalid1 2) (hz1 2)
  let E2 := E1 ++ t2
  have hE0 : E0.length ≤ E1.length := by simp [E1]
  have hE1 : E1.length ≤ E2.length := by simp [E2]
  have hD0 : D.length ≤ E0.length := by simp [E0]
  have hsupp0 (a : ℕ) (ha : a < n + E0.length) :
      supp n E2 a = supp n E0 a := by
    rw [supp_append_prefix n E1 t2 a (by omega), supp_append_prefix n E0 t1 a ha]
  have hsuppD (i : Fin 3) (a : ℕ) (ha : a ∈ F i) :
      supp n E1 a = supp n D a := by
    rw [supp_append_prefix n E0 t1 a (hvalid0 i a ha),
      supp_append_prefix n D t0 a (hvalid i a ha)]
  refine ⟨(t0 ++ t1) ++ t2, ![w0, w1, w2], ?_⟩
  have heq : D ++ ((t0 ++ t1) ++ t2) = E2 := by simp [E2, E1, E0, List.append_assoc]
  rw [heq]
  refine ⟨hs2, ?_, ?_, ?_, ?_⟩
  · have hsum : (∑ i : Fin 3, (F i).card) = (F 0).card + (F 1).card + (F 2).card := by
      simp [Fin.sum_univ_succ, Nat.add_assoc]
    rw [hsum]
    simp only [List.length_append]
    omega
  · intro i
    fin_cases i
    · change w0 < n + E2.length
      omega
    · change w1 < n + E2.length
      omega
    · exact hw2
  · intro i v
    fin_cases i
    · change v ∈ supp n E2 w0 ↔ ∀ a ∈ F 0, v ∈ supp n D a
      rw [hsupp0 w0 hw0]
      exact hp0 v
    · change v ∈ supp n E2 w1 ↔ ∀ a ∈ F 1, v ∈ supp n D a
      rw [supp_append_prefix n E1 t2 w1 hw1, hp1]
      exact forall₂_congr fun a ha => by rw [supp_append_prefix n D t0 a (hvalid 1 a ha)]
    · change v ∈ supp n E2 w2 ↔ ∀ a ∈ F 2, v ∈ supp n D a
      rw [hp2]
      exact forall₂_congr fun a ha => by rw [hsuppD 2 a ha]
  · intro j hjD hjE2
    by_cases hj0 : j < E0.length
    · obtain ⟨ht, hzj⟩ := hv0 j hjD hj0
      refine ⟨?_, ?_⟩
      · rw [tag_append_prefix E1 t2 j (by omega), tag_append_prefix E0 t1 j hj0]
        exact ht
      · rw [hsupp0 (n + j) (by omega)]
        exact hzj
    · by_cases hj1 : j < E1.length
      · obtain ⟨ht, hzj⟩ := hv1 j (by omega) hj1
        refine ⟨?_, ?_⟩
        · rw [tag_append_prefix E1 t2 j hj1]
          exact ht
        · rw [supp_append_prefix n E1 t2 (n + j) (by omega)]
          exact hzj
      · exact hv2 j (by omega) hjE2

end VirtualAnd

namespace VirtualAnd


lemma append_three_source_families {α : Type*} [DecidableEq α] {n : ℕ} {D : Dag}
    (hS : Strict n D) (z : Fin n) (A : Fin 3 → Finset α) (source : α → ℕ)
    (hne : ∀ i, (A i).Nonempty)
    (hvalid : ∀ i, ∀ e ∈ A i, source e < n + D.length)
    (hz : ∀ i, ∀ e ∈ A i, z ∈ supp n D (source e)) :
    ∃ tail : Dag, ∃ w : Fin 3 → ℕ,
      Strict n (D ++ tail) ∧ tail.length + 3 ≤ ∑ i, (A i).card ∧
      (∀ i, w i < n + (D ++ tail).length) ∧
      (∀ i v, v ∈ supp n (D ++ tail) (w i) ↔ ∀ e ∈ A i, v ∈ supp n D (source e)) ∧
      (∀ j, D.length ≤ j → j < (D ++ tail).length →
        tag (D ++ tail) j = true ∧ z ∈ supp n (D ++ tail) (n + j)) ∧
      (∀ x : Fin n → Bool, ∀ a, a < n + D.length → val (D ++ tail) x a = val D x a) ∧
      ∀ a, a < n + D.length → supp n (D ++ tail) a = supp n D a := by
  classical
  let F : Fin 3 → Finset ℕ := fun i => (A i).image source
  have hFn : ∀ i, (F i).Nonempty := by
    intro i
    obtain ⟨e, he⟩ := hne i
    exact ⟨source e, Finset.mem_image.mpr ⟨e, he, rfl⟩⟩
  have hFv : ∀ i, ∀ a ∈ F i, a < n + D.length := by
    intro i a ha
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
    exact hvalid i e he
  have hFz : ∀ i, ∀ a ∈ F i, z ∈ supp n D a := by
    intro i a ha
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
    exact hz i e he
  obtain ⟨tail, w, hE, hcost, hw, hsupport, hvirtual⟩ :=
    append_three_and_families_support hS z F hFn hFv hFz
  refine ⟨tail, w, hE, ?_, hw, ?_, hvirtual,
    fun x a ha => val_append_prefix n D tail x a ha,
    fun a ha => supp_append_prefix n D tail a ha⟩
  · rw [hcost]
    exact Finset.sum_le_sum (fun i _ => Finset.card_image_le)
  · intro i v
    rw [hsupport i v]
    constructor
    · intro hv e he
      exact hv (source e) (Finset.mem_image.mpr ⟨e, he, rfl⟩)
    · intro hv a ha
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
      exact hv e he

end VirtualAnd

end PEqualNP.Outside.L_meta_2590_aux.H2

namespace PEqualNP.Outside.L_meta_2590_aux.H2.N0Exclusive


def familyIndex : Fin 3 → V := ![1, 4, 5]

def targetPairs : Fin 3 → Finset V := ![{2, 6}, {3, 9}, {7, 8}]

lemma familyIndex_mem : ∀ p, familyIndex p ∈ J := by decide +kernel

lemma neighborhood_index : ∀ p, nb (familyIndex p) = insert 0 (targetPairs p) := by
  decide +kernel

lemma indexed_family_card (D : Dag) :
    (∑ p : Fin 3, (family D (familyIndex p)).card) = (allArcs D).card := by
  classical
  rw [allArcs_card]
  simp [J, familyIndex, Fin.sum_univ_succ ]

lemma allArcs_output_empty {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (hi : J ⊆ ineligSet 10 D) :
    ∀ e ∈ allArcs D, supp 10 D (10 + e.1) = ∅ := by
  classical
  intro e he
  obtain ⟨i, hiJ, hei⟩ := Finset.mem_biUnion.mp he
  exact family_output_empty h hc hi hiJ hei

lemma actual_virtual_neighborhoods {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 Adj D) (hz : Bzero 10 D = 0) (hi : J ⊆ ineligSet 10 D) :
    ∃ tail : Dag, Strict 10 (D ++ tail) ∧ tail.length + 3 ≤ (allArcs D).card ∧
      ∀ p : Fin 3, ∃ w, supp 10 (D ++ tail) w = insert 0 (targetPairs p) := by
  classical
  have hne : ∀ p : Fin 3, (family D (familyIndex p)).Nonempty :=
    fun p => family_nonempty h hc hz hi (familyIndex_mem p)
  have hvalid : ∀ p : Fin 3, ∀ e ∈ family D (familyIndex p), src D e < 10 + D.length := by
    intro p e he
    have hej := (sem_mem_W.mp (mem_family.mp he).1).1
    have hlt := sem_src_lt h.1 hej e.2
    change src D e < 10 + e.1 at hlt
    omega
  have hzero : ∀ p : Fin 3, ∀ e ∈ family D (familyIndex p), (0 : V) ∈ supp 10 D (src D e) :=
    fun _ _ he => (sem_mem_W.mp (mem_family.mp he).1).2.1
  obtain ⟨tail, w, hE, hcost, _, hsupport, _, _, _⟩ :=
    VirtualAnd.append_three_source_families h.1 (0 : V)
      (fun p => family D (familyIndex p)) (src D) hne hvalid hzero
  refine ⟨tail, hE, ?_, ?_⟩
  · rwa [indexed_family_card D] at hcost
  · intro p
    refine ⟨w p, ?_⟩
    rw [← neighborhood_index p]
    ext v
    exact (hsupport p v).trans (family_intersection h hc hz hi (familyIndex_mem p) v).symm

end PEqualNP.Outside.L_meta_2590_aux.H2.N0Exclusive

namespace PEqualNP.Outside.L_meta_2590_aux.H2


lemma n0_bzero_zero_impossible {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hz : Bzero 10 D = 0)
    (hi : neighborhoodI ⊆ ineligSet 10 D) (hlen : D.length ≤ 19) : False := by
  obtain ⟨tail, hE, hcost, hocc⟩ := N0Exclusive.actual_virtual_neighborhoods h hc hz hi
  exact PEqualNP.Outside.L_meta_2590_aux.H2.n0_virtual_triples_impossible h hc hi
    (N0Exclusive.allArcs D) (N0Exclusive.allArcs_subset D)
    (N0Exclusive.allArcs_output_empty h hc hi) tail hE hocc hcost hlen

end PEqualNP.Outside.L_meta_2590_aux.H2

namespace PEqualNP.Outside.L_meta_2590_aux

namespace H2

def carrierDiff (n : ℕ) (D : Dag) (x y : Fin n) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => x ∈ supp n D w ∧ y ∉ supp n D w)

variable {n : Nat} {D : Dag} {G : Fin n → Fin n → Prop}

lemma carrier_flow_diff (h : StrictLive n D) (x y : Fin n) (hxy : x ≠ y)
    (hout : x ∉ supp n D (outW n D)) :
    (exitArcs n D (carrierDiff n D x y)).card + (merges n D (carrierDiff n D x y)).card =
      1 + surplusOn D (carrierDiff n D x y) := by
  have hsub : carrierDiff n D x y ⊆ inner n D := by
    intro w hw
    simp only [carrierDiff, Finset.mem_filter, Finset.mem_range] at hw
    rw [sb_mem_inner]
    by_contra hc
    have hw2 : w = outW n D := by unfold outW; omega
    rw [hw2] at hw
    exact hout hw.2.1
  have hsrc : sources n (carrierDiff n D x y) = {x.val} := by
    ext w
    simp only [sources, carrierDiff, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨-, hx, -⟩, hw⟩
      have hs : supp n D w = {⟨w, hw⟩} := supp_input D ⟨w, hw⟩
      rw [hs, Finset.mem_singleton] at hx
      rw [hx]
    · rintro rfl
      refine ⟨⟨by have := x.isLt; omega, ?_, ?_⟩, x.isLt⟩
      · rw [supp_input]; exact Finset.mem_singleton_self x
      · rw [supp_input, Finset.mem_singleton]; exact fun hc => hxy hc.symm
  have hfl := carrier_flow h _ hsub (fun j hj hK => ?_)
  · rw [hsrc, Finset.card_singleton] at hfl; exact hfl
  · obtain ⟨ha, hb, -⟩ := h.1 j hj
    simp only [carrierDiff, Finset.mem_filter, Finset.mem_range] at hK ⊢
    obtain ⟨-, hx, hy⟩ := hK
    rw [supp_gate h.1 j hj] at hx hy
    split_ifs at hx hy with ht
    · rw [Finset.mem_inter] at hx hy
      by_cases hya : y ∈ supp n D (opA D j)
      · exact Or.inr ⟨by omega, hx.2, fun hc => hy ⟨hya, hc⟩⟩
      · exact Or.inl ⟨by omega, hx.1, hya⟩
    · rw [Finset.mem_union] at hx hy
      rcases hx with h1 | h1
      · exact Or.inl ⟨by omega, h1, fun hc => hy (Or.inl hc)⟩
      · exact Or.inr ⟨by omega, h1, fun hc => hy (Or.inr hc)⟩

lemma sem_cover_free (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {x a b y : Fin n} (hab : ¬ G a b) (hxy : G x y) (hya : ¬ G y a) (hyb : ¬ G y b) :
    ∃ e, e ∈ sem_W n D x ∧ a ∉ supp n D (src D e) ∧ b ∉ supp n D (src D e) := by
  have hsym := hG.1
  have hirr := hG.2.1
  have hA : ∀ u ∈ ({a, b, y} : Finset (Fin n)), ∀ v ∈ ({a, b, y} : Finset (Fin n)),
      ¬ G u v := by
    intro u hu v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with hu | hu | hu <;> rcases hv with hv | hv | hv <;> rw [hu, hv]
    · exact hirr a
    · exact hab
    · exact fun h => hya (hsym _ _ h)
    · exact fun h => hab (hsym _ _ h)
    · exact hirr b
    · exact fun h => hyb (hsym _ _ h)
    · exact hya
    · exact hyb
    · exact hirr y
  obtain ⟨j, s, hj, -, h1, h2, hd⟩ := sem_exposure hG hS hC {a, b, y} hA x ⟨y, by simp, hxy⟩
  exact ⟨(j, s), sem_mem_W.mpr ⟨hj, h1, h2⟩, fun h => Finset.disjoint_left.mp hd h (by simp),
    fun h => Finset.disjoint_left.mp hd h (by simp)⟩

end H2

namespace H2

section SemDiff

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

lemma sem_mem_diff {x y : Fin n} {w : ℕ} :
    w ∈ carrierDiff n D x y ↔ x ∈ supp n D w ∧ y ∉ supp n D w := by
  simp only [carrierDiff, Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨sem_supp_lt h.1, h⟩⟩

lemma sem_mem_exit_diff {x y : Fin n} {e : ℕ × Bool} :
    e ∈ exitArcs n D (carrierDiff n D x y) ↔ e.1 < D.length ∧
      (x ∈ supp n D (src D e) ∧ y ∉ supp n D (src D e)) ∧
      ¬ (x ∈ supp n D (n + e.1) ∧ y ∉ supp n D (n + e.1)) := by
  simp only [exitArcs, arcs, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    Finset.mem_univ, and_true, sem_mem_diff]

lemma sem_surplus_diff (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b)
    {x y : Fin n} (hxy : x ≠ y) (hx : x ∈ eligSet n D) :
    surplusOn D (carrierDiff n D x y) = 1 + ((residualUnits n D b).filter
      (fun u => x ∈ supp n D u.1 ∧ y ∉ supp n D u.1)).card := by
  have h1 : surplusOn D (carrierDiff n D x y) =
      ((units n D).filter (fun u => x ∈ supp n D u.1 ∧ y ∉ supp n D u.1)).card := by
    rw [sb_card_units_filter n D (fun w => x ∈ supp n D w ∧ y ∉ supp n D w)]
    symm
    refine Finset.sum_subset (fun w hw => ?_) (fun w hw hnot => ?_)
    · rw [Finset.mem_filter] at hw
      exact sem_mem_diff.mpr hw.2
    · have hni : w ∉ inner n D := fun hc => hnot (Finset.mem_filter.mpr ⟨hc, sem_mem_diff.mp hw⟩)
      rw [sb_mem_inner] at hni
      simp [fanout_eq_zero_of_ge hS w (by omega)]
  have h2 : (units n D).filter (fun u => x ∈ supp n D u.1 ∧ y ∉ supp n D u.1) =
      {(⟨b x, 0⟩ : Σ _ : ℕ, ℕ)} ∪ (residualUnits n D b).filter
        (fun u => x ∈ supp n D u.1 ∧ y ∉ supp n D u.1) := by
    ext u
    have hsub := reserved_subset hS b hb
    simp only [residualUnits, unitsPlus, Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff,
      Finset.mem_singleton]
    constructor
    · intro hu
      by_cases hr : u ∈ reservedUnits n D b
      · left
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hr
        have hxv := hu.2.1
        rw [(hb v hv).2, Finset.mem_singleton] at hxv
        rw [hxv]
      · exact Or.inr ⟨⟨⟨hu.1, ⟨x, hu.2.1⟩⟩, hr⟩, hu.2⟩
    · rintro (rfl | hu)
      · have hbx := hb x hx
        refine ⟨(Finset.mem_filter.mp (hsub (Finset.mem_image.mpr ⟨x, hx, rfl⟩))).1, ?_, ?_⟩
        · rw [hbx.2]; exact Finset.mem_singleton_self x
        · rw [hbx.2, Finset.mem_singleton]; exact fun hc => hxy hc.symm
      · exact ⟨hu.1.1.1, hu.2⟩
  have h3 : (⟨b x, 0⟩ : Σ _ : ℕ, ℕ) ∉ (residualUnits n D b).filter
      (fun u => x ∈ supp n D u.1 ∧ y ∉ supp n D u.1) := by
    intro hc
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hc).1).2 (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  rw [h1, h2, Finset.singleton_union, Finset.card_insert_of_notMem h3]
  omega

lemma sem_first_joint (hS : Strict n D) {x y : Fin n} (hxy : x ≠ y) {w : ℕ}
    (hw : x ∈ supp n D w ∧ y ∈ supp n D w) :
    ∃ j s, j < D.length ∧ tag D j = false ∧ x ∈ supp n D (n + j) ∧ y ∈ supp n D (n + j) ∧
      x ∈ supp n D (src D (j, s)) ∧ y ∉ supp n D (src D (j, s)) ∧
      y ∈ supp n D (src D (j, !s)) ∧ x ∉ supp n D (src D (j, !s)) := by
  classical
  have hex : ∃ u, x ∈ supp n D u ∧ y ∈ supp n D u := ⟨w, hw⟩
  obtain ⟨h1, h2⟩ := Nat.find_spec hex
  have hmin : ∀ u, u < Nat.find hex → ¬ (x ∈ supp n D u ∧ y ∈ supp n D u) :=
    fun u hu => Nat.find_min hex hu
  generalize Nat.find hex = f at h1 h2 hmin
  have hlt := sem_supp_lt h1
  have hn : n ≤ f := by
    by_contra hc
    have hs : supp n D f = {⟨f, by omega⟩} := supp_input D ⟨f, by omega⟩
    rw [hs, Finset.mem_singleton] at h1 h2
    exact hxy (h1.trans h2.symm)
  obtain ⟨j, rfl⟩ : ∃ j, f = n + j := ⟨f - n, by omega⟩
  have hj : j < D.length := by omega
  obtain ⟨ha, hb, -⟩ := hS j hj
  have hna := hmin _ ha
  have hnb := hmin _ hb
  cases ht : tag D j
  · have h1' := h1
    have h2' := h2
    rw [sem_supp_or hS hj ht, Finset.mem_union] at h1' h2'
    refine ⟨j, ?_⟩
    rcases h1' with hxa | hxb
    · have hya : y ∉ supp n D (opA D j) := fun hc => hna ⟨hxa, hc⟩
      have hyb : y ∈ supp n D (opB D j) := h2'.resolve_left hya
      exact ⟨false, hj, ht, h1, h2, by simpa [src] using hxa, by simpa [src] using hya,
        by simpa [src] using hyb, by simpa [src] using fun hc => hnb ⟨hc, hyb⟩⟩
    · have hyb : y ∉ supp n D (opB D j) := fun hc => hnb ⟨hxb, hc⟩
      have hya : y ∈ supp n D (opA D j) := h2'.resolve_right hyb
      exact ⟨true, hj, ht, h1, h2, by simpa [src] using hxb, by simpa [src] using hyb,
        by simpa [src] using hya, by simpa [src] using fun hc => hna ⟨hc, hya⟩⟩
  · exfalso
    rw [sem_supp_and hS hj ht, Finset.mem_inter] at h1 h2
    exact hna ⟨h1.1, h2.1⟩

lemma sem_diff_two_exits (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (b : Fin n → ℕ) (hb : PureBranch n D b) {x c z : Fin n} (hxc : x ≠ c)
    (hx : x ∈ eligSet n D)
    (hres : ∀ u ∈ residualUnits n D b, x ∈ supp n D u.1 → c ∈ supp n D u.1)
    {w : ℕ} (hw : x ∈ supp n D w ∧ c ∈ supp n D w) (hxz : G x z) (hcz : ¬ G c z) :
    surplusOn D (carrierDiff n D x c) = 1 ∧ merges n D (carrierDiff n D x c) = ∅ ∧
      (exitArcs n D (carrierDiff n D x c)).card = 2 ∧
      ∃ e ∈ exitArcs n D (carrierDiff n D x c), tag D e.1 = false ∧ c ∈ supp n D (n + e.1) := by
  have hS := h.1
  have hsur : surplusOn D (carrierDiff n D x c) = 1 := by
    rw [sem_surplus_diff hS b hb hxc hx, Finset.filter_eq_empty_iff.mpr
      (fun u hu hc => hc.2 (hres u hu hc.1)), Finset.card_empty]
  have hfl := carrier_flow_diff h x c hxc
    (by rw [sem_supp_out hG hC]; exact Finset.notMem_empty x)
  rw [hsur] at hfl
  obtain ⟨j1, s1, hj1, ht1, hx1, hc1, hxs1, hcs1, -, -⟩ := sem_first_joint hS hxc hw
  have he1 : (j1, s1) ∈ exitArcs n D (carrierDiff n D x c) :=
    sem_mem_exit_diff.mpr ⟨hj1, ⟨hxs1, hcs1⟩, fun hc => hc.2 hc1⟩
  have hA : ∀ u ∈ ({c, z} : Finset (Fin n)), ∀ v ∈ ({c, z} : Finset (Fin n)), ¬ G u v := by
    intro u hu v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with hu | hu <;> rcases hv with hv | hv <;> rw [hu, hv]
    · exact hG.2.1 c
    · exact hcz
    · exact fun hc => hcz (hG.1 _ _ hc)
    · exact hG.2.1 z
  obtain ⟨j2, s2, hj2, -, hx2, hn2, hd2⟩ := sem_exposure hG hS hC {c, z} hA x ⟨z, by simp, hxz⟩
  have he2 : (j2, s2) ∈ exitArcs n D (carrierDiff n D x c) :=
    sem_mem_exit_diff.mpr ⟨hj2, ⟨hx2, fun hc => Finset.disjoint_left.mp hd2 hc (by simp)⟩,
      fun hc => hn2 hc.1⟩
  have hne : (j1, s1) ≠ (j2, s2) := by
    intro heq
    rw [Prod.mk.injEq] at heq
    exact hn2 (heq.1 ▸ hx1)
  have h2 : 2 ≤ (exitArcs n D (carrierDiff n D x c)).card :=
    Finset.one_lt_card.mpr ⟨_, he1, _, he2, hne⟩
  exact ⟨hsur, Finset.card_eq_zero.mp (by omega), by omega, (j1, s1), he1, ht1, hc1⟩

end SemDiff

section L3bGen

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

lemma ri_gen (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D) (b : Fin n → ℕ)
    (hb : PureBranch n D b) {x c : Fin n} (hxc : x ≠ c) (hx : x ∈ eligSet n D)
    (hres : ∀ u ∈ residualUnits n D b, x ∈ supp n D u.1 → c ∈ supp n D u.1) {w : ℕ}
    (hw : x ∈ supp n D w ∧ c ∈ supp n D w) :
    ∃ e0, ∀ e ∈ sem_W n D x, e ≠ e0 → c ∈ supp n D (src D e) := by
  classical
  obtain ⟨z, hxz, hcz⟩ := hG.2.2.1 x c hxc
  obtain ⟨-, -, h2, e1, he1, ht1, -⟩ := sem_diff_two_exits hG h hC b hb hxc hx hres hw hxz hcz
  have hc1 : ((exitArcs n D (carrierDiff n D x c)).erase e1).card = 1 := by
    rw [Finset.card_erase_of_mem he1, h2]
  obtain ⟨e0, he0⟩ := Finset.card_eq_one.1 hc1
  refine ⟨e0, fun e he hne => ?_⟩
  by_contra hce
  obtain ⟨h1, h4, h5⟩ := sem_mem_W.1 he
  have hm : e ∈ (exitArcs n D (carrierDiff n D x c)).erase e1 :=
    Finset.mem_erase.2 ⟨fun heq => by
      have := sem_W_and h.1 he
      rw [heq, ht1] at this
      exact Bool.false_ne_true this, sem_mem_exit_diff.2 ⟨h1, ⟨h4, hce⟩, fun hc => h5 hc.1⟩⟩
  rw [he0, Finset.mem_singleton] at hm
  exact hne hm

end L3bGen

end H2


namespace N0Exposure

open H2

def Adj (u v : Fin 10) : Prop :=
  (u.val, v.val) ∈ [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),
    (3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)] ∨
  (v.val, u.val) ∈ [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),
    (3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]

def centers : Finset (Fin 10) := {1,4,5}
def center (i : Fin 3) : Fin 10 := ![1,4,5] i
def nb (i : Fin 3) : Finset (Fin 10) := ![{0,2,6},{0,3,9},{0,7,8}] i
def expose (i : Fin 3) (c : Fin 10) : Finset (Fin 10) :=
  if c ∈ ({2,8,9} : Finset (Fin 10)) then ![{1,8,9},{4,2,8},{5,2,9}] i
  else ![{1,3,7},{4,6,7},{5,3,6}] i

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 8192 in
lemma graph_ok : sem_Gr Adj := by unfold sem_Gr Adj; decide +kernel

lemma zero_in_nb : ∀ i, (0 : Fin 10) ∈ nb i := by decide +kernel
lemma center_neighbor : ∀ i, Adj 0 (center i) := by unfold Adj center; decide +kernel
lemma zero_not_center : (0 : Fin 10) ∉ centers := by decide +kernel
lemma center_mem : ∀ i, center i ∈ centers := by decide +kernel
lemma center_injective : Function.Injective center := by
  unfold Function.Injective center
  decide +kernel
lemma neighbors_exact : ∀ i v, Adj (center i) v ↔ v ∈ nb i := by
  unfold Adj center nb
  decide +kernel


end N0Exposure

namespace N0PrivateExitBarrier

open H2 N0Exposure

def cycle : Finset (Fin 10) := {2,3,6,7,8,9}

lemma cycle_nonzero : ∀ v ∈ cycle, v ≠ (0 : Fin 10) := by decide +kernel
lemma cycle_not_center : ∀ v ∈ cycle, v ∉ centers := by decide +kernel

set_option maxRecDepth 4096 in
set_option synthInstance.maxSize 8192 in
set_option maxHeartbeats 1000000 in
lemma cycle_two_neighbors : ∀ v ∈ cycle, ∃ a ∈ cycle, ∃ b ∈ cycle,
    a ≠ b ∧ Adj v a ∧ Adj v b := by
  unfold cycle Adj
  decide +kernel

set_option maxRecDepth 4096 in
set_option synthInstance.maxSize 8192 in
set_option maxHeartbeats 1000000 in
lemma cycle_not_dominated : ∀ x ∈ cycle, ∃ v ∈ cycle, v ≠ x ∧ ¬ Adj v x := by
  unfold cycle Adj
  decide +kernel

lemma no_merge_other {D : Dag}
    (hNoMerge0 : ∀ j, j < D.length → tag D j = true →
      ¬ ((0 : Fin 10) ∈ supp 10 D (opA D j) ∧ 0 ∈ supp 10 D (opB D j)))
    {j : Nat} (hj : j < D.length) (ht : tag D j = true) (s : Bool)
    (hz : (0 : Fin 10) ∈ supp 10 D (src D (j,s))) :
    (0 : Fin 10) ∉ supp 10 D (src D (j,!s)) := by
  intro ho
  apply hNoMerge0 j hj ht
  cases s
  · exact ⟨by simpa [src] using hz, by simpa [src] using ho⟩
  · exact ⟨by simpa [src] using ho, by simpa [src] using hz⟩

lemma private_cycle_cover {D : Dag} (hD : Strict 10 D) (hc : sem_Comp 10 Adj D)
    (hNoMerge0 : ∀ j, j < D.length → tag D j = true →
      ¬ ((0 : Fin 10) ∈ supp 10 D (opA D j) ∧ 0 ∈ supp 10 D (opB D j)))
    (hprivate : ∀ x ∈ cycle, ∃ p : Nat × Bool, ∀ e ∈ sem_W 10 D x,
      (0 : Fin 10) ∉ supp 10 D (src D e) →
      e = p ∧ supp 10 D (src D e) = {x}) :
    ∀ v ∈ cycle, ∃ f ∈ sem_W 10 D 0, ∃ x ∈ cycle,
      supp 10 D (src D (sem_bar f)) = {x} ∧ (v = x ∨ Adj v x) := by
  intro v hv
  obtain ⟨a, ha, b, hb, hab, hva, hvb⟩ := cycle_two_neighbors v hv
  obtain ⟨j, hj, ht, _, hvout, haout, s, hvs, _, has, _⟩ :=
    sem_joint_meeting N0Exposure.graph_ok hD hc hva
  obtain ⟨k, hk, hkt, _, hvoutk, hbout, t, hvst, _, hbst, _⟩ :=
    sem_joint_meeting N0Exposure.graph_ok hD hc hvb
  have hve : (j,s) ∈ sem_W 10 D v := sem_mem_W.mpr ⟨hj,hvs,hvout⟩
  have hae : (j,!s) ∈ sem_W 10 D a := sem_mem_W.mpr ⟨hj,has,haout⟩
  have hvek : (k,t) ∈ sem_W 10 D v := sem_mem_W.mpr ⟨hk,hvst,hvoutk⟩
  have hbe : (k,!t) ∈ sem_W 10 D b := sem_mem_W.mpr ⟨hk,hbst,hbout⟩
  obtain ⟨pa, hpa⟩ := hprivate a ha
  obtain ⟨pb, hpb⟩ := hprivate b hb
  by_cases hz : (0 : Fin 10) ∈ supp 10 D (src D (j,s))
  · have hno := no_merge_other hNoMerge0 hj ht s hz
    have hs := (hpa (j,!s) hae hno).2
    have ho : (0 : Fin 10) ∉ supp 10 D (10+j) :=
      fun h => hno (sem_supp_and_sub hD hj ht (!s) h)
    exact ⟨(j,s), sem_mem_W.mpr ⟨hj,hz,ho⟩, a, ha, hs, Or.inr hva⟩
  by_cases hzk : (0 : Fin 10) ∈ supp 10 D (src D (k,t))
  · have hno := no_merge_other hNoMerge0 hk hkt t hzk
    have hs := (hpb (k,!t) hbe hno).2
    have ho : (0 : Fin 10) ∉ supp 10 D (10+k) :=
      fun h => hno (sem_supp_and_sub hD hk hkt (!t) h)
    exact ⟨(k,t), sem_mem_W.mpr ⟨hk,hzk,ho⟩, b, hb, hs, Or.inr hvb⟩
  obtain ⟨pv, hpv⟩ := hprivate v hv
  have hjs := hpv (j,s) hve hz
  have hkt' := hpv (k,t) hvek hzk
  have he : (j,s) = (k,t) := hjs.1.trans hkt'.1.symm
  have hbjs : b ∈ supp 10 D (src D (j,!s)) := by
    have hbar := congrArg sem_bar he
    change (j,!s) = (k,!t) at hbar
    rw [hbar]
    exact hbst
  have hzo : (0 : Fin 10) ∈ supp 10 D (src D (j,!s)) := by
    by_contra hn
    have hs := (hpa (j,!s) hae hn).2
    rw [hs, Finset.mem_singleton] at hbjs
    exact hab hbjs.symm
  have ho : (0 : Fin 10) ∉ supp 10 D (10+j) :=
    fun h => hz (sem_supp_and_sub hD hj ht s h)
  refine ⟨(j,!s), sem_mem_W.mpr ⟨hj,hzo,ho⟩, v,hv, ?_, Or.inl rfl⟩
  simpa only [sem_bar, Bool.not_not] using hjs.2

lemma private_exit_barrier {D : Dag} (hD : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (hI : centers ⊆ ineligSet 10 D)
    (hW : (sem_W 10 D 0).card ≤ 4)
    (hNoMerge0 : ∀ j, j < D.length → tag D j = true →
      ¬ ((0 : Fin 10) ∈ supp 10 D (opA D j) ∧ 0 ∈ supp 10 D (opB D j)))
    (hprivate : ∀ x ∈ cycle, ∃ p : Nat × Bool, ∀ e ∈ sem_W 10 D x,
      (0 : Fin 10) ∉ supp 10 D (src D e) →
      e = p ∧ supp 10 D (src D e) = {x}) : False := by
  classical
  have hex := fun i : Fin 3 => sem_inelig_consumer N0Exposure.graph_ok hD hc (hI (center_mem i))
  choose a hj ht hs ho hn hx hm using hex
  let e : Fin 3 → Nat × Bool := fun i => sem_bar (a i)
  have hinj : Function.Injective e := by
    intro i k he
    have ha : a i = a k := by
      have hb := congrArg sem_bar he
      simpa only [e, sem_bar_bar] using hb
    apply center_injective
    have hsik : ({center i} : Finset (Fin 10)) = {center k} := by
      rw [←hs i, ←hs k, ha]
    exact Finset.singleton_inj.mp hsik
  have heW : ∀ i, e i ∈ sem_W 10 D 0 := by
    intro i
    apply sem_mem_W.mpr
    refine ⟨hj i, ?_, ?_⟩
    · exact hn i 0 ((neighbors_exact i 0).mpr (zero_in_nb i))
    · change (0 : Fin 10) ∉ supp 10 D (10+(a i).1)
      rw [ho i]
      exact Finset.notMem_empty _
  let B : Finset (Nat × Bool) := Finset.univ.image e
  have hBsub : B ⊆ sem_W 10 D 0 := by
    intro f hf
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hf
    exact heW i
  have hBcard : B.card = 3 := by
    rw [Finset.card_image_of_injective _ hinj]
    simp
  have hdiff : ((sem_W 10 D 0) \ B).card ≤ 1 := by
    have hsum := Finset.card_sdiff_add_card_eq_card hBsub
    omega
  obtain ⟨f0,hf0⟩ := Finset.card_le_one_iff_subset_singleton.mp hdiff
  have hcover : ∀ v ∈ cycle, ∃ x ∈ cycle,
      supp 10 D (src D (sem_bar f0)) = {x} ∧ (v=x ∨ Adj v x) := by
    intro v hv
    obtain ⟨f,hf,x,hx,hsx,hvx⟩ := private_cycle_cover hD.1 hc hNoMerge0 hprivate v hv
    have hfB : f ∉ B := by
      intro hfB
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hfB
      have hse : supp 10 D (src D (sem_bar (e i))) = {center i} := by
        simpa only [e, sem_bar_bar] using hs i
      rw [hi,hsx] at hse
      have hxi : x = center i := Finset.singleton_inj.mp hse
      exact cycle_not_center x hx (hxi.symm ▸ center_mem i)
    have hff : f=f0 := Finset.mem_singleton.mp (hf0 (Finset.mem_sdiff.mpr ⟨hf,hfB⟩))
    exact ⟨x,hx,by simpa only [hff] using hsx,hvx⟩
  obtain ⟨x,hx,hsx,_⟩ := hcover 2 (by decide +kernel)
  obtain ⟨v,hv,hvx,hvn⟩ := cycle_not_dominated x hx
  obtain ⟨y,_,hsy,hvy⟩ := hcover v hv
  have hxy : x=y := Finset.singleton_inj.mp (hsx.symm.trans hsy)
  rw [←hxy] at hvy
  exact hvy.elim hvx hvn

lemma private_exit_barrier_of_exits {D : Dag} (hD : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (hI : centers ⊆ ineligSet 10 D)
    (hW : (sem_W 10 D 0).card ≤ 4)
    (hNoMerge0 : ∀ j, j < D.length → tag D j = true →
      ¬ ((0 : Fin 10) ∈ supp 10 D (opA D j) ∧ 0 ∈ supp 10 D (opB D j)))
    (hprivate : ∀ x ∈ cycle, ∃ p ∈ sem_W 10 D x,
      supp 10 D (src D p) = {x} ∧ ∀ e ∈ sem_W 10 D x,
      (0 : Fin 10) ∉ supp 10 D (src D e) → e = p) : False := by
  apply private_exit_barrier hD hc hI hW hNoMerge0
  intro x hx
  obtain ⟨p,_,hps,hp⟩ := hprivate x hx
  refine ⟨p,fun e he hz => ?_⟩
  have hep := hp e he hz
  exact ⟨hep,by simpa only [hep] using hps⟩

end N0PrivateExitBarrier

namespace N0ActualCode

open H2 N0Exposure N0PrivateExitBarrier

abbrev V := Fin 10

def code (D : Dag) (b : V → ℕ) (x : V) : Finset (Σ _ : ℕ, ℕ) :=
  (residualUnits 10 D b).filter (fun u => x ∈ supp 10 D u.1)

def owner (x : V) : V :=
  if x = 2 ∨ x = 6 then 1 else if x = 3 ∨ x = 9 then 4 else 5

set_option synthInstance.maxSize 8192 in
set_option maxRecDepth 4096 in
lemma geometry : ∀ x ∈ cycle,
    owner x ∈ centers ∧ Adj (owner x) x ∧ Adj (owner x) 0 ∧ (0 : V) ≠ x ∧ x ≠ owner x := by
  unfold owner cycle centers Adj
  decide +kernel

set_option synthInstance.maxSize 8192 in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
lemma cycle_center_geometry :
    (∀ x ∈ cycle, x ≠ 0 ∧ x ∉ centers ∧ ¬ Adj 0 x ∧ ¬ Adj x 0 ∧ ∃ z ∈ cycle, Adj x z) ∧
    (∀ x ∈ cycle, ∀ y ∈ cycle, y ≠ x → ∃ z ∈ cycle, Adj x z ∧ ¬ Adj y z) ∧
    (∀ v : V, v = 0 ∨ v ∈ centers ∨ v ∈ cycle) := by
  unfold cycle centers Adj
  decide +kernel

lemma code_subset_center_private_exit {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 Adj D) (hI : ineligSet 10 D = centers)
    (b : V → ℕ) (hb : PureBranch 10 D b) {x : V} (hx : x ∈ cycle)
    (hinc : code D b x ⊆ code D b 0) :
    ∃ e, e ∈ sem_W 10 D x ∧ supp 10 D (src D e) = {x} ∧
      ∀ f ∈ sem_W 10 D x, (0 : V) ∉ supp 10 D (src D f) → f = e := by
  classical
  have hi : centers ⊆ ineligSet 10 D := by rw [hI]
  obtain ⟨hx0, hxJ, _, _, z, hz, hxz⟩ := cycle_center_geometry.1 x hx
  have hxelig : x ∈ eligSet 10 D := by
    by_contra bad
    have hm : x ∈ ineligSet 10 D := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, bad⟩
    rw [hI] at hm
    exact hxJ hm
  obtain ⟨hoi, hox, ho0, _, _⟩ := geometry x hx
  obtain ⟨q, _, _, _, _, hn, _, _⟩ := sem_inelig_consumer N0Exposure.graph_ok h hc (hi hoi)
  have hres : ∀ u ∈ residualUnits 10 D b, x ∈ supp 10 D u.1 → (0 : V) ∈ supp 10 D u.1 := by
    intro u hu hxu
    exact (Finset.mem_filter.mp (hinc (Finset.mem_filter.mpr ⟨hu, hxu⟩))).2
  obtain ⟨exception, hrest⟩ := ri_gen N0Exposure.graph_ok h hc b hb hx0 hxelig hres ⟨hn x hox, hn 0 ho0⟩
  have hz0 := (cycle_center_geometry.1 z hz).2.2.2.1
  obtain ⟨e, he, he0, _⟩ := sem_cover_free N0Exposure.graph_ok h.1 hc
    (x := x) (a := 0) (b := 0) (y := z) (N0Exposure.graph_ok.2.1 0) hxz hz0 hz0
  have hexc : e = exception := by
    by_contra bad
    exact he0 (hrest e he bad)
  have huniq : ∀ f ∈ sem_W 10 D x, (0 : V) ∉ supp 10 D (src D f) → f = e := by
    intro f hf hf0
    have hfe : f = exception := by
      by_contra bad
      exact hf0 (hrest f hf bad)
    exact hfe.trans hexc.symm
  have hxe := (sem_mem_W.mp he).2.1
  refine ⟨e, he, ?_, huniq⟩
  refine Finset.Subset.antisymm ?_ (Finset.singleton_subset_iff.mpr hxe)
  intro c hce
  rw [Finset.mem_singleton]
  by_contra hcx
  rcases cycle_center_geometry.2.2 c with hc0 | hcJ | hcC
  · subst c
    exact he0 hce
  · have hpure := sem_inelig_pure N0Exposure.graph_ok h.1 hc (hi hcJ) hce
    rw [hpure, Finset.mem_singleton] at hxe
    exact hcx hxe.symm
  · obtain ⟨w, hw, hxw, hcw⟩ := cycle_center_geometry.2.1 x hx c hcC hcx
    have h0c := (cycle_center_geometry.1 c hcC).2.2.1
    have hw0 := (cycle_center_geometry.1 w hw).2.2.2.1
    obtain ⟨f, hf, hf0, hfc⟩ := sem_cover_free N0Exposure.graph_ok h.1 hc
      (x := x) (a := 0) (b := c) (y := w) h0c hxw hw0
      (fun h => hcw (N0Exposure.graph_ok.1 _ _ h))
    have hfe := huniq f hf hf0
    exact hfc (hfe ▸ hce)

end N0ActualCode

namespace N0ActualCode

open H2 N0Exposure N0PrivateExitBarrier

lemma actual_code_barrier {D : Dag} (hD : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (hI : ineligSet 10 D = centers) (b : V → Nat) (hb : PureBranch 10 D b)
    (hW : (sem_W 10 D 0).card ≤ 4)
    (hNoMerge0 : ∀ j, j < D.length → tag D j = true →
      ¬ ((0 : Fin 10) ∈ supp 10 D (opA D j) ∧ 0 ∈ supp 10 D (opB D j)))
    (hcode : ∀ x ∈ cycle, code D b x ⊆ code D b 0) : False := by
  apply private_exit_barrier_of_exits hD hc (by rw [hI]) hW hNoMerge0
  intro x hx
  exact code_subset_center_private_exit hD hc hI b hb hx (hcode x hx)

lemma two_residual_high_center_exits_impossible {D : Dag}
    (hD : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (hI : ineligSet 10 D = centers) (b : V → Nat) (hb : PureBranch 10 D b)
    (hR : (residualUnits 10 D b).card ≤ 2)
    (hW : 4 ≤ (sem_W 10 D 0).card) : False := by
  classical
  have hflow := sem_code_count N0Exposure.graph_ok hD hc b hb (0 : V)
  change (sem_W 10 D 0).card + (merges 10 D (carrierT 10 D {0})).card =
    1 + (({0} : Finset V) ∩ eligSet 10 D).card + (code D b 0).card at hflow
  have hsingle : (({0} : Finset V) ∩ eligSet 10 D).card ≤ 1 :=
    (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
  have hcode_sub : code D b 0 ⊆ residualUnits 10 D b := Finset.filter_subset _ _
  have hcode_card := Finset.card_le_card hcode_sub
  have hM : merges 10 D (carrierT 10 D {0}) = ∅ := Finset.card_eq_zero.mp (by omega)
  have hWup : (sem_W 10 D 0).card ≤ 4 := by omega
  have hcode_eq : code D b 0 = residualUnits 10 D b :=
    Finset.eq_of_subset_of_card_le hcode_sub (by omega)
  apply actual_code_barrier hD hc hI b hb hWup
  · intro j hj ht hab
    have hz : (0 : V) ∈ supp 10 D (10+j) := by
      rw [sem_supp_and hD.1 hj ht]
      exact Finset.mem_inter.mpr hab
    have htag := (sem_zm_gate hD.1 hM hj hz).1
    rw [ht] at htag
    exact Bool.false_ne_true htag.symm
  · intro x hx
    rw [hcode_eq]
    exact Finset.filter_subset _ _

lemma two_residual_center_exits_le_three {D : Dag}
    (hD : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (hI : ineligSet 10 D = centers) (b : V → Nat) (hb : PureBranch 10 D b)
    (hR : (residualUnits 10 D b).card ≤ 2) : (sem_W 10 D 0).card ≤ 3 := by
  by_contra hW
  exact two_residual_high_center_exits_impossible hD hc hI b hb hR (by omega)

lemma positive_Bzero_center_exits_le_three {D : Dag}
    (hD : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (hI : ineligSet 10 D = centers) (hlen : D.length ≤ 19)
    (hzero : 1 ≤ Bzero 10 D) : (sem_W 10 D 0).card ≤ 3 := by
  obtain ⟨b,hb⟩ := sem_exists_pureBranch N0Exposure.graph_ok hD.1 hc
  have helig : (eligSet 10 D).card = 7 := by
    have hsum : (ineligSet 10 D).card + (eligSet 10 D).card = 10 := by
      simpa only [ineligSet, Finset.card_univ, Fintype.card_fin] using
        Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (eligSet 10 D))
    have hc3 : centers.card = 3 := by decide +kernel
    rw [hI,hc3] at hsum
    omega
  have hr := card_residual hD.1 b hb
  have hs := surplus_identity hD
  rw [totalSurplus_split] at hs
  rw [helig] at hr
  apply two_residual_center_exits_le_three hD hc hI b hb
  omega

end N0ActualCode



namespace H2

lemma n0_h7_adj_eq : N0Exposure.Adj = adj := by
  funext a b
  apply propext
  have hh : ∀ a b, N0Exposure.Adj a b ↔ adj a b := by
    unfold N0Exposure.Adj adj neighbors
    decide +kernel
  exact hh a b

lemma n0_positive_bzero_impossible {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hi : ineligSet 10 D = neighborhoodI)
    (hlen : D.length ≤ 19) (hz : 1 ≤ Bzero 10 D) : False := by
  have hc' : sem_Comp 10 N0Exposure.Adj D := by
    rw [n0_h7_adj_eq]
    exact hc
  have hW := N0ActualCode.positive_Bzero_center_exits_le_three h hc' hi hlen hz
  exact n0_three_exit_impossible h hc (by rw [hi]) hW hlen

end H2


end PEqualNP.Outside.L_meta_2590_aux

namespace PEqualNP.Outside.L_meta_2590_aux.H2

lemma n0_neighborhood_impossible {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hi : ineligSet 10 D = neighborhoodI)
    (hlen : D.length ≤ 19) : False := by
  by_cases hz : Bzero 10 D = 0
  · apply n0_bzero_zero_impossible h hc hz ?_ hlen
    rw [hi]
  · exact n0_positive_bzero_impossible h hc hi hlen (by omega)

end PEqualNP.Outside.L_meta_2590_aux.H2

namespace PEqualNP.Outside.L_meta_2590_aux

namespace I3Geometry

abbrev V := Fin 10

def neighbors (v : V) : Nat :=
  [50, 69, 138, 276, 521, 385, 770, 548, 104, 208].getD v.val 0

abbrev adj (u v : V) : Prop := (neighbors u).testBit v.val = true

def mask (m : Nat) : Finset V := Finset.univ.filter (fun v => m.testBit v.val)

abbrev Independent (I : Finset V) : Prop :=
  ∀ u ∈ I, ∀ v ∈ I, ¬ adj u v

def rows : List (Nat × Nat × List Nat) :=
  [(69, 50, [1, 0, 4, 3, 2, 6, 5, 9, 8, 7]),
  (261, 769, [0, 4, 9, 6, 1, 5, 3, 7, 8, 2]),
  (517, 769, [0, 4, 9, 7, 5, 1, 3, 6, 2, 8]),
  (73, 769, [0, 4, 3, 8, 5, 1, 9, 2, 6, 7]),
  (137, 769, [0, 1, 6, 8, 5, 4, 2, 9, 3, 7]),
  (521, 50, [1, 2, 3, 4, 0, 6, 7, 8, 9, 5]),
  (193, 769, [0, 4, 3, 2, 1, 5, 9, 8, 7, 6]),
  (385, 50, [1, 2, 3, 8, 6, 0, 7, 4, 5, 9]),
  (769, 769, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]),
  (42, 769, [4, 0, 5, 8, 3, 9, 1, 7, 6, 2]),
  (138, 50, [2, 1, 0, 4, 3, 7, 6, 5, 9, 8]),
  (522, 769, [1, 0, 4, 9, 6, 2, 5, 3, 7, 8]),
  (50, 50, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]),
  (146, 769, [4, 0, 5, 7, 9, 3, 1, 8, 2, 6]),
  (274, 769, [4, 0, 1, 6, 9, 3, 5, 2, 8, 7]),
  (546, 769, [4, 0, 1, 2, 3, 9, 5, 6, 7, 8]),
  (386, 769, [1, 0, 4, 3, 2, 6, 5, 9, 8, 7]),
  (770, 50, [2, 1, 6, 8, 3, 7, 0, 9, 5, 4]),
  (52, 769, [4, 3, 8, 5, 0, 9, 2, 6, 7, 1]),
  (84, 769, [1, 6, 8, 5, 0, 2, 9, 3, 7, 4]),
  (276, 50, [2, 3, 4, 0, 1, 7, 8, 9, 5, 6]),
  (100, 769, [1, 6, 8, 3, 2, 0, 9, 5, 4, 7]),
  (548, 50, [2, 3, 4, 9, 7, 1, 8, 0, 6, 5]),
  (772, 769, [2, 1, 0, 4, 3, 7, 6, 5, 9, 8]),
  (104, 50, [2, 3, 8, 5, 7, 1, 4, 6, 0, 9]),
  (552, 769, [1, 2, 3, 8, 6, 0, 7, 4, 5, 9]),
  (200, 769, [2, 1, 6, 8, 3, 7, 0, 9, 5, 4]),
  (112, 769, [4, 3, 2, 1, 0, 9, 8, 7, 6, 5]),
  (208, 50, [2, 3, 8, 6, 1, 7, 4, 5, 9, 0]),
  (400, 769, [1, 2, 3, 4, 0, 6, 7, 8, 9, 5])]

def mapRow (r : Nat × Nat × List Nat) (v : V) : V :=
  ⟨(r.2.2.getD v.val 0) % 10, Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma rows_valid : ∀ r ∈ rows,
    Function.Bijective (mapRow r) ∧
    (∀ u v : V, adj (mapRow r u) (mapRow r v) ↔ adj u v) ∧
    (mask r.1).image (mapRow r) = mask r.2.1 ∧
    (r.2.1 = 50 ∨ r.2.1 = 769) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma rows_cover : ∀ I : Finset V, I.card = 3 → Independent I →
    ∃ r ∈ rows, mask r.1 = I := by
  decide +kernel

lemma classify (I : Finset V) (hc : I.card = 3) (hi : Independent I) :
    ∃ σ : Equiv.Perm V,
      (∀ u v : V, adj (σ u) (σ v) ↔ adj u v) ∧
      (I.image σ = mask 50 ∨ I.image σ = mask 769) := by
  obtain ⟨r, hr, heq⟩ := rows_cover I hc hi
  obtain ⟨hb, ha, hm, ht⟩ := rows_valid r hr
  let σ : Equiv.Perm V := Equiv.ofBijective (mapRow r) hb
  refine ⟨σ, ha, ?_⟩
  have hs : I.image σ = mask r.2.1 := by
    rw [← heq]
    exact hm
  rcases ht with h | h
  · exact Or.inl (hs.trans (congrArg mask h))
  · exact Or.inr (hs.trans (congrArg mask h))

lemma canonical_masks : mask 50 = ({1, 4, 5} : Finset V) ∧
    mask 769 = ({0, 8, 9} : Finset V) := by
  decide +kernel

end I3Geometry

namespace H2
@[local simp] lemma i3_gop_true (a b : Bool) : gop true a b = (a && b) := gop_true a b
@[local simp] lemma i3_gop_false (a b : Bool) : gop false a b = (a || b) := gop_false a b

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

section SurplusFlow

variable {n : ℕ} {D : Dag}

end SurplusFlow

theorem relabel_eligSet {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) :
    eligSet n (relabel σ D) = (eligSet n D).image σ := by
  ext v
  simp only [eligSet, Finset.mem_biUnion, Finset.mem_image, branchW, Finset.mem_filter,
    Finset.mem_range]
  constructor
  · rintro ⟨w', ⟨hw', hf⟩, hv⟩
    obtain ⟨w, rfl⟩ : ∃ w, w' = liftP σ w := ⟨liftP σ⁻¹ w', (tr_liftP_inv' σ w').symm⟩
    rw [relabel_supp σ hS, Finset.mem_image] at hv
    obtain ⟨a, ha, rfl⟩ := hv
    rw [relabel_fanout] at hf
    rw [relabel_length, tr_liftP_lt_iff σ (Nat.le_add_right _ _)] at hw'
    exact ⟨a, ⟨w, ⟨hw', hf⟩, ha⟩, rfl⟩
  · rintro ⟨a, ⟨w, ⟨hw, hf⟩, ha⟩, rfl⟩
    refine ⟨liftP σ w, ⟨?_, ?_⟩, ?_⟩
    · rw [relabel_length]; exact (tr_liftP_lt_iff σ (Nat.le_add_right _ _) w).mpr hw
    · rw [relabel_fanout]; exact hf
    · rw [relabel_supp σ hS]; exact Finset.mem_image_of_mem _ ha

theorem relabel_ineligSet {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) :
    ineligSet n (relabel σ D) = (ineligSet n D).image σ := by
  ext v
  simp only [ineligSet, relabel_eligSet σ hS, Finset.mem_sdiff, Finset.mem_univ, true_and,
    Finset.mem_image]
  constructor
  · intro h
    exact ⟨σ⁻¹ v, fun hm => h ⟨σ⁻¹ v, hm, by simp⟩, by simp⟩
  · rintro ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    exact ha (σ.injective hab ▸ hb)

section SemCore

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

end SemCore

section SemCodes

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

end SemCodes

section SemArms

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

end SemArms

section SemPaths

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

theorem sem_inelig_reach (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    {i : Fin n} (hi : i ∈ ineligSet n D) :
    sem_Chain n D i.val (outW n D) ∨
      ∃ b, sem_Chain n D i.val b ∧ 2 ≤ fanout D b ∧ supp n D b = ∅ := by
  have hlt : i.val < n + D.length := by have := i.isLt; omega
  have hp : Relation.ReflTransGen (sem_step n D) i.val (outW n D) := live_reaches_out h i.val hlt
  rcases sem_path_chain hp with h1 | ⟨b, h1, h2⟩
  · exact Or.inl h1
  · exact Or.inr ⟨b, h1, h2, sem_branch_empty hG h.1 hC hi h1 h2⟩

theorem sem_bzero_unique (hS : Strict n D) (hB0 : Bzero n D ≤ 1) {b b' : ℕ}
    (hf : 2 ≤ fanout D b) (he : supp n D b = ∅) (hf' : 2 ≤ fanout D b')
    (he' : supp n D b' = ∅) : b = b' := by
  by_contra hne
  have hsub : ({b, b'} : Finset ℕ) ⊆ (inner n D).filter (fun w => ¬ (supp n D w).Nonempty) := by
    intro c hc
    rw [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl
    · exact sem_bzero_mem hS hf he
    · exact sem_bzero_mem hS hf' he'
  have h1 := Finset.sum_le_sum_of_subset (f := fun w => fanout D w - 1) hsub
  rw [Finset.sum_pair hne] at h1
  unfold Bzero surplusOn at hB0
  omega

theorem sem_shared_exact (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    (Bs : Finset (Fin n)) (hBs : ∀ a ∈ Bs, ∀ b ∈ Bs, ¬ G a b) {i j : Fin n} {w : ℕ}
    (hch : sem_Chain n D i.val w) (hdj : sem_Dom n D w j.val)
    (hnsub : ∃ a ∈ Bs, G j a ∧ ¬ G i a) :
    ∃ k s, k < D.length ∧ tag D k = true ∧ n + k ≤ w ∧
      sem_Chain n D i.val (src D (k, !s)) ∧
      ∀ a ∈ Bs, (a ∈ supp n D (src D (k, s)) ↔ G i a) := by
  classical
  have hX0 : ¬ sem_Edge G (sem_ins i (sem_ind (Bs.filter (fun a => ¬ G i a)))) := by
    intro hc
    rcases sem_ins_ind_edge hG hc with ⟨a, ha, hia⟩ | ⟨a, ha, b, hb, hab⟩
    · exact (Finset.mem_filter.mp ha).2 hia
    · exact hBs a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1 hab
  obtain ⟨a0, ha0, hja0, hia0⟩ := hnsub
  have hX1 : sem_Edge G (sem_ins j (sem_ins i (sem_ind (Bs.filter (fun a => ¬ G i a))))) :=
    ⟨j, a0, hja0, sem_ins_self j _, by simp [sem_ins, sem_ind, ha0, hia0]⟩
  have hwX := (sem_dom_split hS hC _ j w hdj hX0 hX1).1
  refine sem_exact_at hS i w hch Bs (fun S hS1 hS2 => ?_) (fun a _ hia => ?_)
  · by_contra hc
    rw [Bool.not_eq_false] at hc
    have hmono := val_mono hS (sem_ins i (sem_ind S))
      (sem_ins i (sem_ind (Bs.filter (fun a => ¬ G i a)))) (fun k hk => by
        simp only [sem_ins, sem_ind, Bool.or_eq_true, decide_eq_true_eq] at hk ⊢
        rcases hk with hk | hk
        · exact Or.inl hk
        · exact Or.inr (Finset.mem_filter.mpr ⟨hS1 hk, hS2 k hk⟩)) w hc
    rw [hwX] at hmono
    exact Bool.false_ne_true hmono
  · have h2 := sem_dom_split hS hC (sem_ind {a}) i w (sem_chain_dom hS hch)
      (by rw [sem_ind_single]; exact sem_single_no_edge hG a)
      ⟨i, a, hia, sem_ins_self i _, by simp [sem_ins, sem_ind]⟩
    exact ⟨h2.2, h2.1⟩

theorem sem_shared_empty (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (hB0 : Bzero n D ≤ 1) (Bs : Finset (Fin n)) (hBs : ∀ a ∈ Bs, ∀ b ∈ Bs, ¬ G a b)
    {i j : Fin n} (hi : i ∈ ineligSet n D) (hj : j ∈ ineligSet n D)
    (hji : ∃ a ∈ Bs, G j a ∧ ¬ G i a) :
    (∃ k s, k < D.length ∧ tag D k = true ∧ sem_Chain n D i.val (src D (k, !s)) ∧
        ∀ a ∈ Bs, (a ∈ supp n D (src D (k, s)) ↔ G i a)) ∨
      (∃ k s, k < D.length ∧ tag D k = true ∧ sem_Chain n D j.val (src D (k, !s)) ∧
        ∀ a ∈ Bs, (a ∈ supp n D (src D (k, s)) ↔ G j a)) := by
  have hS := h.1
  rcases sem_inelig_reach hG h hC hi with h1 | ⟨b, hb1, hb2, hb3⟩
  · exact Or.inl (sem_exact_nbhd hG hS hC Bs hBs h1)
  · rcases sem_inelig_reach hG h hC hj with h1 | ⟨b', hb1', hb2', hb3'⟩
    · exact Or.inr (sem_exact_nbhd hG hS hC Bs hBs h1)
    · have hbb : b' = b := sem_bzero_unique hS hB0 hb2' hb3' hb2 hb3
      rw [hbb] at hb1'
      obtain ⟨k, s, hk, ht, -, hc, hsupp⟩ := sem_shared_exact hG hS hC Bs hBs hb1
        (sem_chain_dom hS hb1') hji
      exact Or.inl ⟨k, s, hk, ht, hc, hsupp⟩

end SemPaths

section SemDiff

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

end SemDiff

def sup_Occ (n : ℕ) (D : Dag) (P M : Finset (Fin n)) : Prop := ∃ w, supp n D w ∩ P = M

def sup_big (n : ℕ) (D : Dag) (P : Finset (Fin n)) : Finset ℕ :=
  (merges n D (carrierT n D P)).filter (fun j => 2 ≤ (supp n D (n + j) ∩ P).card)

section SupMask

variable {n : ℕ} {D : Dag}

theorem sup_mem_carrier {P : Finset (Fin n)} {w : ℕ} :
    w ∈ carrierT n D P ↔ (supp n D w ∩ P).Nonempty := by
  simp only [carrierT, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    obtain ⟨v, hv⟩ := h
    exact ⟨sem_supp_lt (Finset.mem_inter.mp hv).1, v, hv⟩

theorem sup_occ_big (hS : Strict n D) {P M : Finset (Fin n)} (hM : 2 ≤ M.card)
    (h : sup_Occ n D P M) : ∃ j ∈ sup_big n D P, supp n D (n + j) ∩ P = M := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨j, -, -, hj, hmer, -, -⟩ := sem_first_mask hS P M hM w hw
  exact ⟨j, Finset.mem_filter.mpr ⟨hmer, by rw [hj]; exact hM⟩, hj⟩

theorem sup_card_le_big (hS : Strict n D) (P : Finset (Fin n)) (F : Finset (Finset (Fin n)))
    (hF : ∀ M ∈ F, 2 ≤ M.card ∧ sup_Occ n D P M) : F.card ≤ (sup_big n D P).card := by
  have hsub : F ⊆ (sup_big n D P).image (fun j => supp n D (n + j) ∩ P) := by
    intro M hM
    obtain ⟨j, hj, hjM⟩ := sup_occ_big hS (hF M hM).1 (hF M hM).2
    exact Finset.mem_image.mpr ⟨j, hj, hjM⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

end SupMask

section K4Generic

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

theorem k4_mem_carrier {T : Finset (Fin n)} {w : ℕ} :
    w ∈ carrierT n D T ↔ (supp n D w ∩ T).Nonempty := by
  simp only [carrierT, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
  rintro ⟨v, hv⟩
  exact sem_supp_lt (Finset.mem_inter.mp hv).1

theorem k4_mem_exit {T : Finset (Fin n)} {e : ℕ × Bool} : e ∈ exitArcs n D (carrierT n D T) ↔
    e.1 < D.length ∧ (supp n D (src D e) ∩ T).Nonempty ∧
      ¬ (supp n D (n + e.1) ∩ T).Nonempty := by
  simp only [exitArcs, arcs, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    Finset.mem_univ, and_true, k4_mem_carrier]

theorem k4_pos_exit {pos : Fin n → ℕ × Bool} (hpos : k4_Pos n G D pos) {i a : Fin n}
    {T : Finset (Fin n)} (hi : i ∈ ineligSet n D) (hia : G i a) (haT : a ∈ T) :
    pos i ∈ exitArcs n D (carrierT n D T) := by
  obtain ⟨h1, h2, h3, -⟩ := hpos.1 i hi
  rw [k4_mem_exit]
  refine ⟨h1, ⟨a, Finset.mem_inter.mpr ⟨h3 a hia, haT⟩⟩, ?_⟩
  rw [h2, Finset.empty_inter]
  exact Finset.not_nonempty_empty

theorem k4_exits_ge {pos : Fin n → ℕ × Bool} (hpos : k4_Pos n G D pos) (T J : Finset (Fin n))
    (hJ : ∀ i ∈ J, i ∈ ineligSet n D ∧ ∃ a ∈ T, G i a) :
    J.image pos ⊆ exitArcs n D (carrierT n D T) ∧ (J.image pos).card = J.card := by
  constructor
  · intro e he
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hi1, a, haT, hia⟩ := hJ i hi
    exact k4_pos_exit hpos hi1 hia haT
  · exact Finset.card_image_of_injOn
      (fun i hi i' hi' he => hpos.2 i (hJ i hi).1 i' (hJ i' hi').1 he)

theorem k4_mask_gate (hS : Strict n D) (T : Finset (Fin n)) (w : ℕ)
    (h2 : 2 ≤ (supp n D w ∩ T).card) :
    ∃ j ∈ merges n D (carrierT n D T), supp n D (n + j) ∩ T = supp n D w ∩ T := by
  obtain ⟨j, -, -, h3, h4, -, -⟩ := sem_first_mask hS T _ h2 w rfl
  exact ⟨j, h4, h3⟩

theorem k4_pair_merges (hS : Strict n D) {T : Finset (Fin n)} (hT : T.card = 3)
    {a b c : Fin n} (ha : a ∈ T) (hb : b ∈ T) (hc : c ∈ T) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) {w1 w2 : ℕ} (h1a : a ∈ supp n D w1) (h1b : b ∈ supp n D w1)
    (h2a : a ∈ supp n D w2) (h2c : c ∈ supp n D w2) :
    2 ≤ (merges n D (carrierT n D T)).card := by
  have m1a : a ∈ supp n D w1 ∩ T := Finset.mem_inter.mpr ⟨h1a, ha⟩
  have m1b : b ∈ supp n D w1 ∩ T := Finset.mem_inter.mpr ⟨h1b, hb⟩
  have m2a : a ∈ supp n D w2 ∩ T := Finset.mem_inter.mpr ⟨h2a, ha⟩
  have m2c : c ∈ supp n D w2 ∩ T := Finset.mem_inter.mpr ⟨h2c, hc⟩
  have c1 : 2 ≤ (supp n D w1 ∩ T).card := Finset.one_lt_card.mpr ⟨a, m1a, b, m1b, hab⟩
  have c2 : 2 ≤ (supp n D w2 ∩ T).card := Finset.one_lt_card.mpr ⟨a, m2a, c, m2c, hac⟩
  obtain ⟨j1, hj1, e1⟩ := k4_mask_gate hS T w1 c1
  by_cases heq : supp n D w1 ∩ T = supp n D w2 ∩ T
  · have hfull : supp n D w1 ∩ T = T := by
      refine Finset.eq_of_subset_of_card_le Finset.inter_subset_right ?_
      rw [hT]
      exact Finset.two_lt_card.mpr
        ⟨a, m1a, b, m1b, c, by rw [heq]; exact m2c, hab, hac, hbc⟩
    obtain ⟨j, -, -, h3, h4, -, hcase⟩ := sem_first_mask hS T T (by omega) w1 hfull
    rcases hcase with ⟨-, hA, -⟩ | ⟨-, hA, hB, hU, -, -⟩
    · exact absurd rfl (Finset.ssubset_of_ssubset_of_subset hA Finset.inter_subset_right).ne
    · have hcard : 3 ≤ (supp n D (opA D j) ∩ T).card + (supp n D (opB D j) ∩ T).card := by
        have := Finset.card_union_le (supp n D (opA D j) ∩ T) (supp n D (opB D j) ∩ T)
        rw [hU, hT] at this
        exact this
      have key : ∀ w, supp n D w ∩ T ⊂ T → 2 ≤ (supp n D w ∩ T).card →
          2 ≤ (merges n D (carrierT n D T)).card := by
        intro w hss hc2
        obtain ⟨j', hj', e'⟩ := k4_mask_gate hS T w hc2
        refine Finset.one_lt_card.mpr ⟨j, h4, j', hj', fun hjj => ?_⟩
        rw [hjj, e'] at h3
        exact hss.ne h3
      by_cases hc2 : 2 ≤ (supp n D (opA D j) ∩ T).card
      · exact key _ hA hc2
      · exact key _ hB (by omega)
  · obtain ⟨j2, hj2, e2⟩ := k4_mask_gate hS T w2 c2
    exact Finset.one_lt_card.mpr ⟨j1, hj1, j2, hj2, fun hjj => heq (by rw [← e1, ← e2, hjj])⟩

end K4Generic

section L3Gen

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

theorem tri_exits (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {pos : Fin n → ℕ × Bool} (hpos : k4_Pos n G D pos) (T J : Finset (Fin n))
    (A : Fin n → Finset (Fin n))
    (hJ : ∀ i ∈ J, i ∈ ineligSet n D ∧ (∃ a ∈ T, G i a) ∧ ∀ f ∈ T, ∃ a ∈ A f, G i a)
    (hA : ∀ f ∈ T, (∀ a ∈ A f, ∀ b ∈ A f, ¬ G a b) ∧ T.erase f ⊆ A f ∧ ∃ a ∈ A f, G f a) :
    J.card + T.card ≤ (exitArcs n D (carrierT n D T)).card := by
  classical
  obtain ⟨hsub, hcard⟩ := k4_exits_ge hpos T J (fun i hi => ⟨(hJ i hi).1, (hJ i hi).2.1⟩)
  have hex : ∀ f ∈ T, ∃ e : ℕ × Bool, e.1 < D.length ∧ tag D e.1 = true ∧
      f ∈ supp n D (src D e) ∧ f ∉ supp n D (n + e.1) ∧ Disjoint (supp n D (src D e)) (A f) := by
    intro f hf
    obtain ⟨j, s, h1, h2, h4, h5, h6⟩ := sem_exposure hG hS hC (A f) (hA f hf).1 f (hA f hf).2.2
    exact ⟨(j, s), h1, h2, h4, h5, h6⟩
  choose! w hw using hex
  have hinj : Set.InjOn w T := by
    intro f hf g hg hfg
    by_contra hne
    exact Finset.disjoint_left.1 (hw f hf).2.2.2.2 (hfg ▸ (hw g hg).2.2.1)
      ((hA f hf).2.1 (Finset.mem_erase.2 ⟨fun h => hne h.symm, hg⟩))
  have hdis : Disjoint (J.image pos) (T.image w) := by
    rw [Finset.disjoint_left]
    intro e he1 he2
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 he1
    obtain ⟨f, hf, hfe⟩ := Finset.mem_image.1 he2
    obtain ⟨a, ha, hia⟩ := (hJ i hi).2.2 f hf
    exact Finset.disjoint_left.1 (hw f hf).2.2.2.2
      (hfe ▸ (hpos.1 i (hJ i hi).1).2.2.1 a hia) ha
  have hsub2 : T.image w ⊆ exitArcs n D (carrierT n D T) := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨h1, h2, h4, h5, h6⟩ := hw f hf
    refine k4_mem_exit.2 ⟨h1, ⟨f, Finset.mem_inter.2 ⟨h4, hf⟩⟩, ?_⟩
    rintro ⟨g, hg⟩
    rw [Finset.mem_inter] at hg
    have hgs : g ∈ supp n D (src D (w f)) := sem_supp_and_sub hS h1 h2 (w f).2 hg.1
    exact Finset.disjoint_left.1 h6 hgs
      ((hA f hf).2.1 (Finset.mem_erase.2 ⟨fun h => h5 (h ▸ hg.1), hg.2⟩))
  have := Finset.card_le_card (Finset.union_subset hsub hsub2)
  rw [Finset.card_union_of_disjoint hdis, hcard, Finset.card_image_of_injOn hinj] at this
  exact this

end L3Gen

section L3bGen

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

end L3bGen


end H2

namespace I3Branch

open H2

abbrev V := Fin 10

def neighbors (v : V) : Nat :=
  [50, 69, 138, 276, 521, 385, 770, 548, 104, 208].getD v.val 0

abbrev adj (u v : V) : Prop := (neighbors u).testBit v.val = true

def T : Finset V := {4, 5, 6}

def I : Finset V := {0, 8, 9}

def nb (v : V) : Finset V := T.filter (adj v)

def exposure (v : V) : Finset V :=
  if v = 4 then {3, 5, 6} else if v = 5 then {4, 6, 7} else {1, 4, 5}

lemma graph_ok : sem_Gr adj := by
  unfold sem_Gr
  decide +kernel

lemma T_card : T.card = 3 := by decide +kernel

lemma I_card : I.card = 3 := by decide +kernel

lemma T_independent : ∀ u ∈ T, ∀ v ∈ T, ¬ adj u v := by decide +kernel

lemma exposure_ok : ∀ f ∈ T,
    (∀ a ∈ exposure f, ∀ b ∈ exposure f, ¬ adj a b) ∧
      T.erase f ⊆ exposure f ∧ ∃ a ∈ exposure f, adj f a := by decide +kernel

lemma incidence_ok : ∀ i ∈ I,
    (∃ a ∈ T, adj i a) ∧ ∀ f ∈ T, ∃ a ∈ exposure f, adj i a := by decide +kernel

lemma nb_card : ∀ i ∈ I, (nb i).card = 2 := by decide +kernel

lemma nb_nonsub : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ¬ nb i ⊆ nb j := by decide +kernel

lemma directional_difference : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
    ∃ a ∈ T, adj j a ∧ ¬ adj i a := by decide +kernel

lemma third_vertex : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
    ∃ k ∈ I, k ≠ i ∧ k ≠ j := by decide +kernel

lemma exact_mask_of_witness {D : Dag} {i : V}
    (hw : ∃ k s, k < D.length ∧ tag D k = true ∧
      sem_Chain 10 D i.val (src D (k, !s)) ∧
      ∀ a ∈ T, (a ∈ supp 10 D (src D (k, s)) ↔ adj i a)) :
    sup_Occ 10 D T (nb i) := by
  obtain ⟨k, s, _, _, _, hs⟩ := hw
  refine ⟨src D (k, s), ?_⟩
  ext a
  simp only [nb, Finset.mem_inter, Finset.mem_filter]
  constructor
  · rintro ⟨ha, hat⟩
    exact ⟨hat, (hs a hat).mp ha⟩
  · rintro ⟨hat, ha⟩
    exact ⟨(hs a hat).mpr ha, hat⟩

lemma exact_mask_pair {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hz : Bzero 10 D ≤ 1) (hi : I ⊆ ineligSet 10 D)
    {i j : V} (hiI : i ∈ I) (hjI : j ∈ I) (hne : i ≠ j) :
    sup_Occ 10 D T (nb i) ∨ sup_Occ 10 D T (nb j) := by
  rcases sem_shared_empty graph_ok h hc hz T T_independent (hi hiI) (hi hjI)
    (directional_difference i hiI j hjI hne) with hw | hw
  · exact Or.inl (exact_mask_of_witness hw)
  · exact Or.inr (exact_mask_of_witness hw)

lemma two_exact_masks {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hz : Bzero 10 D ≤ 1) (hi : I ⊆ ineligSet 10 D) :
    ∃ i ∈ I, ∃ j ∈ I, i ≠ j ∧ sup_Occ 10 D T (nb i) ∧ sup_Occ 10 D T (nb j) := by
  have h08 := exact_mask_pair h hc hz hi (i := 0) (j := 8) (by decide) (by decide) (by decide)
  have h09 := exact_mask_pair h hc hz hi (i := 0) (j := 9) (by decide) (by decide) (by decide)
  have h89 := exact_mask_pair h hc hz hi (i := 8) (j := 9) (by decide) (by decide) (by decide)
  by_cases h0 : sup_Occ 10 D T (nb 0)
  · rcases h89 with h8 | h9
    · exact ⟨0, by decide, 8, by decide, by decide, h0, h8⟩
    · exact ⟨0, by decide, 9, by decide, by decide, h0, h9⟩
  · exact ⟨8, by decide, 9, by decide, by decide, h08.resolve_left h0, h09.resolve_left h0⟩

lemma three_merges {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hz : Bzero 10 D ≤ 1) (hi : I ⊆ ineligSet 10 D) :
    3 ≤ (merges 10 D (carrierT 10 D T)).card := by
  classical
  obtain ⟨i, hiI, j, hjI, hij, hiocc, hjocc⟩ := two_exact_masks h hc hz hi
  obtain ⟨k, hkI, hki, hkj⟩ := third_vertex i hiI j hjI hij
  obtain ⟨e, _, _, _, _, hneigh, _, _⟩ := sem_inelig_consumer graph_ok h hc (hi hkI)
  let M := supp 10 D (src D (e.1, !e.2)) ∩ T
  have hMocc : sup_Occ 10 D T M := ⟨src D (e.1, !e.2), rfl⟩
  have hkM : nb k ⊆ M := by
    intro a ha
    obtain ⟨hat, hka⟩ := Finset.mem_filter.mp ha
    exact Finset.mem_inter.mpr ⟨hneigh a hka, hat⟩
  have hMcard : 2 ≤ M.card := by
    have := Finset.card_le_card hkM
    rw [nb_card k hkI] at this
    exact this
  have hMi : M ≠ nb i := by
    intro heq
    exact nb_nonsub k hkI i hiI hki (heq ▸ hkM)
  have hMj : M ≠ nb j := by
    intro heq
    exact nb_nonsub k hkI j hjI hkj (heq ▸ hkM)
  have hnij : nb i ≠ nb j := by
    intro heq
    exact nb_nonsub i hiI j hjI hij (heq ▸ Finset.Subset.refl (nb i))
  let F : Finset (Finset V) := {nb i, nb j, M}
  have hFcard : F.card = 3 := by simp [F, hnij, hMi.symm, hMj.symm]
  have hF : ∀ X ∈ F, 2 ≤ X.card ∧ sup_Occ 10 D T X := by
    intro X hX
    simp only [F, Finset.mem_insert, Finset.mem_singleton] at hX
    rcases hX with rfl | rfl | rfl
    · exact ⟨(nb_card i hiI).ge, hiocc⟩
    · exact ⟨(nb_card j hjI).ge, hjocc⟩
    · exact ⟨hMcard, hMocc⟩
  have hbig := sup_card_le_big h.1 T F hF
  have hsub : (sup_big 10 D T).card ≤ (merges 10 D (carrierT 10 D T)).card :=
    Finset.card_filter_le _ _
  omega

lemma six_exits {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hi : I ⊆ ineligSet 10 D) :
    6 ≤ (exitArcs 10 D (carrierT 10 D T)).card := by
  obtain ⟨pos, hpos⟩ := k4_assigned graph_ok h hc
  have hcount := tri_exits graph_ok h.1 hc hpos T I exposure
    (fun i hiI => ⟨hi hiI, incidence_ok i hiI⟩) exposure_ok
  rw [T_card, I_card] at hcount
  exact hcount

lemma exclude_two_residual {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hz : Bzero 10 D ≤ 1) (hi : I ⊆ ineligSet 10 D)
    (b : V → ℕ) (hb : PureBranch 10 D b) (hr : (residualUnits 10 D b).card ≤ 2) : False := by
  have hmerge := three_merges h hc hz hi
  have hexit := six_exits h hc hi
  have hflow := carrier_flow_union h T (by rw [sem_supp_out graph_ok hc]; simp)
  have hsur := surplus_carrierT_eq h.1 b hb T
  have hcar : (T ∩ eligSet 10 D).card ≤ 3 := by
    have := Finset.card_le_card (Finset.inter_subset_left : T ∩ eligSet 10 D ⊆ T)
    rwa [T_card] at this
  have hfilter := Finset.card_filter_le (residualUnits 10 D b)
    (fun u => (supp 10 D u.1 ∩ T).Nonempty)
  rw [T_card] at hflow
  omega

lemma all_exact_masks {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hz : Bzero 10 D = 0) (hi : I ⊆ ineligSet 10 D) :
    ∀ i ∈ I, sup_Occ 10 D T (nb i) := by
  intro i hiI
  exact exact_mask_of_witness (sem_exact_nbhd graph_ok h.1 hc T T_independent
    (sem_noempty_chain_out graph_ok h hc hz (hi hiI)))

lemma tight_counts {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hz : Bzero 10 D = 0) (hi : I ⊆ ineligSet 10 D)
    (b : V → ℕ) (hb : PureBranch 10 D b) (hr : (residualUnits 10 D b).card ≤ 3) :
    (merges 10 D (carrierT 10 D T)).card = 3 ∧
      (exitArcs 10 D (carrierT 10 D T)).card = 6 := by
  have hmerge := three_merges h hc (by omega) hi
  have hexit := six_exits h hc hi
  have hflow := carrier_flow_union h T (by rw [sem_supp_out graph_ok hc]; simp)
  have hsur := surplus_carrierT_eq h.1 b hb T
  have hcar : (T ∩ eligSet 10 D).card ≤ 3 := by
    have := Finset.card_le_card (Finset.inter_subset_left : T ∩ eligSet 10 D ⊆ T)
    rwa [T_card] at this
  have hfilter := Finset.card_filter_le (residualUnits 10 D b)
    (fun u => (supp 10 D u.1 ∩ T).Nonempty)
  rw [T_card] at hflow
  omega

lemma no_full_mask {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hz : Bzero 10 D = 0) (hi : I ⊆ ineligSet 10 D)
    (hm : (merges 10 D (carrierT 10 D T)).card = 3) :
    ∀ w, supp 10 D w ∩ T ≠ T := by
  classical
  intro w hw
  let F : Finset (Finset V) := {nb 0, nb 8, nb 9, T}
  have hFcard : F.card = 4 := by decide +kernel
  have hF : ∀ X ∈ F, 2 ≤ X.card ∧ sup_Occ 10 D T X := by
    intro X hX
    simp only [F, Finset.mem_insert, Finset.mem_singleton] at hX
    rcases hX with rfl | rfl | rfl | rfl
    · exact ⟨by decide, all_exact_masks h hc hz hi 0 (by decide)⟩
    · exact ⟨by decide, all_exact_masks h hc hz hi 8 (by decide)⟩
    · exact ⟨by decide, all_exact_masks h hc hz hi 9 (by decide)⟩
    · exact ⟨by decide, ⟨w, hw⟩⟩
  have hbig := sup_card_le_big h.1 T F hF
  have hsub : (sup_big 10 D T).card ≤ (merges 10 D (carrierT 10 D T)).card :=
    Finset.card_filter_le _ _
  omega

lemma proper_pair_split_disjoint {A B M : Finset V} (hM : M.card = 2)
    (hA : A ⊂ M) (hB : B ⊂ M) (hU : A ∪ B = M) : Disjoint A B := by
  have ha := Finset.card_lt_card hA
  have hb := Finset.card_lt_card hB
  have hcard := Finset.card_union_add_card_inter A B
  rw [hU, hM] at hcard
  apply Finset.disjoint_iff_inter_eq_empty.mpr
  exact Finset.card_eq_zero.mp (by omega)

lemma pair_creation {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hz : Bzero 10 D = 0) (hi : I ⊆ ineligSet 10 D)
    (hm : (merges 10 D (carrierT 10 D T)).card = 3) :
    ∀ i ∈ I, ∃ j ∈ merges 10 D (carrierT 10 D T),
      supp 10 D (10 + j) ∩ T = nb i ∧ tag D j = false ∧
        Disjoint (supp 10 D (opA D j) ∩ T) (supp 10 D (opB D j) ∩ T) := by
  intro i hiI
  obtain ⟨w, hw⟩ := all_exact_masks h hc hz hi i hiI
  have hcard := nb_card i hiI
  obtain ⟨j, _, _, hjM, hjmerge, _, hcase⟩ := sem_first_mask h.1 T (nb i) hcard.ge w hw
  refine ⟨j, hjmerge, hjM, ?_⟩
  rcases hcase with hAnd | hOr
  · have hlt := Finset.card_lt_card hAnd.2.1
    have hfull : supp 10 D (opA D j) ∩ T = T :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [T_card]; omega)
    exact False.elim (no_full_mask h hc hz hi hm _ hfull)
  · exact ⟨hOr.1, proper_pair_split_disjoint hcard hOr.2.1 hOr.2.2.1 hOr.2.2.2.1⟩

lemma all_merges_or_disjoint {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hz : Bzero 10 D = 0) (hi : I ⊆ ineligSet 10 D)
    (hm : (merges 10 D (carrierT 10 D T)).card = 3) :
    ∀ j ∈ merges 10 D (carrierT 10 D T), tag D j = false ∧
      Disjoint (supp 10 D (opA D j) ∩ T) (supp 10 D (opB D j) ∩ T) := by
  classical
  choose! g hg using pair_creation h hc hz hi hm
  have hinj : Set.InjOn g I := by
    intro i hiI j hjI heq
    by_contra hij
    have he : nb i = nb j := (hg i hiI).2.1.symm.trans (heq ▸ (hg j hjI).2.1)
    exact nb_nonsub i hiI j hjI hij (by rw [he])
  have hsub : I.image g ⊆ merges 10 D (carrierT 10 D T) := by
    intro j hj
    obtain ⟨i, hiI, rfl⟩ := Finset.mem_image.mp hj
    exact (hg i hiI).1
  have hcard : (I.image g).card = 3 := by
    rw [Finset.card_image_of_injOn hinj, I_card]
  have heq : I.image g = merges 10 D (carrierT 10 D T) :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  intro j hj
  rw [← heq] at hj
  obtain ⟨i, hiI, rfl⟩ := Finset.mem_image.mp hj
  exact (hg i hiI).2.2

lemma no_and_T_support {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hz : Bzero 10 D = 0) (hi : I ⊆ ineligSet 10 D)
    (hm : (merges 10 D (carrierT 10 D T)).card = 3) :
    ∀ j < D.length, tag D j = true → supp 10 D (10 + j) ∩ T = ∅ := by
  intro j hj hop
  apply Finset.eq_empty_of_forall_notMem
  intro x hx
  obtain ⟨hxo, hxT⟩ := Finset.mem_inter.mp hx
  have hxa := sem_supp_and_sub h.1 hj hop false hxo
  have hxb := sem_supp_and_sub h.1 hj hop true hxo
  rw [sb_src_false] at hxa
  rw [sb_src_true] at hxb
  have hmj : j ∈ merges 10 D (carrierT 10 D T) := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, ?_, ?_, ?_⟩
    · exact sup_mem_carrier.mpr ⟨x, Finset.mem_inter.mpr ⟨hxo, hxT⟩⟩
    · exact sup_mem_carrier.mpr ⟨x, Finset.mem_inter.mpr ⟨hxa, hxT⟩⟩
    · exact sup_mem_carrier.mpr ⟨x, Finset.mem_inter.mpr ⟨hxb, hxT⟩⟩
  have hfalse := (all_merges_or_disjoint h hc hz hi hm j hmj).1
  rw [hop] at hfalse
  contradiction

lemma no_singleton_T_merges {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hz : Bzero 10 D = 0) (hi : I ⊆ ineligSet 10 D)
    (hm : (merges 10 D (carrierT 10 D T)).card = 3) :
    ∀ x ∈ T, merges 10 D (carrierT 10 D {x}) = ∅ := by
  intro x hxT
  apply Finset.eq_empty_of_forall_notMem
  intro j hj
  obtain ⟨hj, hxo, hxa, hxb⟩ := Finset.mem_filter.mp hj
  have hsub : carrierT 10 D {x} ⊆ carrierT 10 D T := by
    intro w hw
    exact sup_mem_carrier.mpr ⟨x, Finset.mem_inter.mpr ⟨sem_mem_carrier1.mp hw, hxT⟩⟩
  have hmj : j ∈ merges 10 D (carrierT 10 D T) :=
    Finset.mem_filter.mpr ⟨hj, hsub hxo, hsub hxa, hsub hxb⟩
  have hd := (all_merges_or_disjoint h hc hz hi hm j hmj).2
  exact Finset.disjoint_left.mp hd
    (Finset.mem_inter.mpr ⟨sem_mem_carrier1.mp hxa, hxT⟩)
    (Finset.mem_inter.mpr ⟨sem_mem_carrier1.mp hxb, hxT⟩)

lemma two_merges_unconditional {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hi : I ⊆ ineligSet 10 D) :
    2 ≤ (merges 10 D (carrierT 10 D T)).card := by
  obtain ⟨e0, _, _, _, _, h0, _, _⟩ := sem_inelig_consumer graph_ok h hc (hi (by decide : (0 : V) ∈ I))
  obtain ⟨e8, _, _, _, _, h8, _, _⟩ := sem_inelig_consumer graph_ok h hc (hi (by decide : (8 : V) ∈ I))
  exact k4_pair_merges h.1 T_card (a := (5 : V)) (b := (4 : V)) (c := (6 : V))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (h0 5 (by decide)) (h0 4 (by decide)) (h8 5 (by decide)) (h8 6 (by decide))

lemma residual_at_least_two {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hi : I ⊆ ineligSet 10 D) (b : V → ℕ) (hb : PureBranch 10 D b) :
    2 ≤ (residualUnits 10 D b).card := by
  have hmerge := two_merges_unconditional h hc hi
  have hexit := six_exits h hc hi
  have hflow := carrier_flow_union h T (by rw [sem_supp_out graph_ok hc]; simp)
  have hsur := surplus_carrierT_eq h.1 b hb T
  have hcar : (T ∩ eligSet 10 D).card ≤ 3 := by
    have := Finset.card_le_card (Finset.inter_subset_left : T ∩ eligSet 10 D ⊆ T)
    rwa [T_card] at this
  have hfilter := Finset.card_filter_le (residualUnits 10 D b)
    (fun u => (supp 10 D u.1 ∩ T).Nonempty)
  rw [T_card] at hflow
  omega

lemma tight_budget {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hlen : D.length ≤ 19) (hi : ineligSet 10 D = I)
    (b : V → ℕ) (hb : PureBranch 10 D b) :
    Bplus 10 D = 10 ∧ Bzero 10 D = 0 ∧ (residualUnits 10 D b).card = 3 ∧ D.length = 19 := by
  have hsub : I ⊆ ineligSet 10 D := by rw [hi]
  have he : (eligSet 10 D).card = 7 := by
    have hsum : (ineligSet 10 D).card + (eligSet 10 D).card = 10 := by
      simpa only [ineligSet, Finset.card_univ, Fintype.card_fin] using
        Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (eligSet 10 D))
    rw [hi, I_card] at hsum
    omega
  have hres := card_residual h.1 b hb
  have hr2 := residual_at_least_two h hc hsub b hb
  have hsur := surplus_identity h
  rw [he] at hres
  rw [totalSurplus_split] at hsur
  have hz : Bzero 10 D ≤ 1 := by omega
  have hr3 : 3 ≤ (residualUnits 10 D b).card := by
    by_contra hlt
    exact exclude_two_residual h hc hz hsub b hb (by omega)
  omega

open H2

lemma tight_exit_cover {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hi : I ⊆ ineligSet 10 D)
    (hcard : (exitArcs 10 D (carrierT 10 D T)).card = 6) :
    ∃ pos wit : V → ℕ × Bool, k4_Pos 10 adj D pos ∧
      (∀ f ∈ T, (wit f).1 < D.length ∧ tag D (wit f).1 = true ∧
        f ∈ supp 10 D (src D (wit f)) ∧ f ∉ supp 10 D (10 + (wit f).1) ∧
        Disjoint (supp 10 D (src D (wit f))) (exposure f)) ∧
      exitArcs 10 D (carrierT 10 D T) = I.image pos ∪ T.image wit ∧
      (∀ e ∈ exitArcs 10 D (carrierT 10 D T),
        (∃ i ∈ I, e = pos i) ∨ ∃ f ∈ T, e = wit f) := by
  classical
  obtain ⟨pos, hpos⟩ := k4_assigned graph_ok h hc
  obtain ⟨hsub, hsize⟩ := k4_exits_ge hpos T I
    (fun i hiI => ⟨hi hiI, (incidence_ok i hiI).1⟩)
  have hex : ∀ f ∈ T, ∃ e : ℕ × Bool, e.1 < D.length ∧ tag D e.1 = true ∧
      f ∈ supp 10 D (src D e) ∧ f ∉ supp 10 D (10 + e.1) ∧
      Disjoint (supp 10 D (src D e)) (exposure f) := by
    intro f hf
    obtain ⟨j, s, h1, h2, h4, h5, h6⟩ :=
      sem_exposure graph_ok h.1 hc (exposure f) (exposure_ok f hf).1 f
        (exposure_ok f hf).2.2
    exact ⟨(j, s), h1, h2, h4, h5, h6⟩
  choose! wit hw using hex
  have hinj : Set.InjOn wit T := by
    intro f hf g hg hfg
    by_contra hne
    exact Finset.disjoint_left.mp (hw f hf).2.2.2.2
      (hfg ▸ (hw g hg).2.2.1)
      ((exposure_ok f hf).2.1 (Finset.mem_erase.mpr ⟨fun h => hne h.symm, hg⟩))
  have hdis : Disjoint (I.image pos) (T.image wit) := by
    rw [Finset.disjoint_left]
    intro e he1 he2
    obtain ⟨i, hiI, rfl⟩ := Finset.mem_image.mp he1
    obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp he2
    obtain ⟨a, ha, hia⟩ := (incidence_ok i hiI).2 f hf
    exact Finset.disjoint_left.mp (hw f hf).2.2.2.2
      (hfe ▸ (hpos.1 i (hi hiI)).2.2.1 a hia) ha
  have hsub2 : T.image wit ⊆ exitArcs 10 D (carrierT 10 D T) := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨h1, h2, h4, h5, h6⟩ := hw f hf
    refine k4_mem_exit.mpr ⟨h1, ⟨f, Finset.mem_inter.mpr ⟨h4, hf⟩⟩, ?_⟩
    rintro ⟨g, hg⟩
    rw [Finset.mem_inter] at hg
    have hgs := sem_supp_and_sub h.1 h1 h2 (wit f).2 hg.1
    exact Finset.disjoint_left.mp h6 hgs
      ((exposure_ok f hf).2.1 (Finset.mem_erase.mpr ⟨fun h => h5 (h ▸ hg.1), hg.2⟩))
  have hall : I.image pos ∪ T.image wit = exitArcs 10 D (carrierT 10 D T) := by
    apply Finset.eq_of_subset_of_card_le (Finset.union_subset hsub hsub2)
    rw [Finset.card_union_of_disjoint hdis, hsize,
      Finset.card_image_of_injOn hinj, I_card, T_card, hcard]
  refine ⟨pos, wit, hpos, hw, hall.symm, ?_⟩
  intro e he
  rw [← hall, Finset.mem_union] at he
  rcases he with he | he
  · obtain ⟨i, hiI, he⟩ := Finset.mem_image.mp he
    exact Or.inl ⟨i, hiI, he.symm⟩
  · obtain ⟨f, hf, he⟩ := Finset.mem_image.mp he
    exact Or.inr ⟨f, hf, he.symm⟩

lemma exposure_T_single {D : Dag} {f : V} (hf : f ∈ T) {w : ℕ}
    (hw : f ∈ supp 10 D w) (hd : Disjoint (supp 10 D w) (exposure f)) :
    supp 10 D w ∩ T = {f} := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_singleton]
  constructor
  · rintro ⟨hx, hxt⟩
    by_contra hne
    exact Finset.disjoint_left.mp hd hx
      ((exposure_ok f hf).2.1 (Finset.mem_erase.mpr ⟨hne, hxt⟩))
  · rintro rfl
    exact ⟨hw, hf⟩

lemma tight_exit_data {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hi : I ⊆ ineligSet 10 D)
    (hcard : (exitArcs 10 D (carrierT 10 D T)).card = 6) :
    ∃ pos wit : V → ℕ × Bool, k4_Pos 10 adj D pos ∧
      (∀ f ∈ T, wit f ∈ sem_W 10 D f ∧
        supp 10 D (src D (wit f)) ∩ T = {f} ∧
        Disjoint (supp 10 D (src D (wit f))) (exposure f)) ∧
      exitArcs 10 D (carrierT 10 D T) = I.image pos ∪ T.image wit := by
  obtain ⟨pos, wit, hpos, hw, heq, _⟩ := tight_exit_cover h hc hi hcard
  refine ⟨pos, wit, hpos, ?_, heq⟩
  intro f hf
  obtain ⟨h1, _, h2, h3, h4⟩ := hw f hf
  exact ⟨sem_mem_W.mpr ⟨h1, h2, h3⟩, exposure_T_single hf h2 h4, h4⟩

lemma chain_and_neighbors {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hz : Bzero 10 D = 0) {i : V} (hi : i ∈ ineligSet 10 D) {g : ℕ} {s : Bool}
    (hg : g < D.length) (ht : tag D g = true)
    (hch : sem_Chain 10 D i.val (src D (g, !s))) :
    ∀ a, adj i a → a ∈ supp 10 D (src D (g, s)) := by
  have hfpos := sem_step_fanout (sem_step_src (n := 10) (D := D) hg (!s))
  have hf : fanout D (src D (g, !s)) = 1 := by
    by_contra hne
    have htwo : 2 ≤ fanout D (src D (g, !s)) := by omega
    have hnon := sem_bzero_branch h.1 hz htwo
    rw [sem_branch_empty graph_ok h.1 hc hi hch htwo] at hnon
    exact Finset.not_nonempty_empty hnon
  have hgo : sem_Chain 10 D i.val (10 + g) :=
    Relation.ReflTransGen.tail hch ⟨sem_step_src hg (!s), hf⟩
  intro a hia
  have htruth := (sem_dom_split h.1 hc (single a) i (10 + g)
    (sem_chain_dom h.1 hgo) (sem_single_no_edge graph_ok a)
    ⟨i, a, hia, sem_ins_self i _, by simp [sem_ins, single]⟩).2
  rw [sem_val_gate_src h.1 _ hg s, ht, gop_true, Bool.and_eq_true] at htruth
  have hind := sem_sibling_indep h.1 i hg s hch hf
    (single a) (sem_ins i (single a)) (sem_ins_agree i (single a))
  exact mem_supp.mpr (hind.trans htruth.1)

lemma chain_and_assigned {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hz : Bzero 10 D = 0) (hi : I ⊆ ineligSet 10 D)
    {pos wit : V → ℕ × Bool} (hp : k4_Pos 10 adj D pos)
    (hw : ∀ f ∈ T, supp 10 D (src D (wit f)) ∩ T = {f})
    (he : exitArcs 10 D (carrierT 10 D T) = I.image pos ∪ T.image wit)
    {i : V} (hiI : i ∈ I) {g : ℕ} {s : Bool}
    (hg : g < D.length) (ht : tag D g = true)
    (hch : sem_Chain 10 D i.val (src D (g, !s))) : (g, s) = pos i := by
  classical
  have hnb := chain_and_neighbors h hc hz (hi hiI) hg ht hch
  have hsub : nb i ⊆ supp 10 D (src D (g, s)) ∩ T := by
    intro a ha
    obtain ⟨haT, hia⟩ := Finset.mem_filter.mp ha
    exact Finset.mem_inter.mpr ⟨hnb a hia, haT⟩
  have htwo : 2 ≤ (supp 10 D (src D (g, s)) ∩ T).card := by
    have := Finset.card_le_card hsub
    rw [nb_card i hiI] at this
    exact this
  have hpure := sem_dom_pure graph_ok h.1 hc i (src D (g, !s)) (sem_chain_dom h.1 hch)
  have himiss : i ∉ T := by
    have hh : ∀ x ∈ I, x ∉ T := by decide +kernel
    exact hh i hiI
  have hexit : (g, s) ∈ exitArcs 10 D (carrierT 10 D T) := by
    refine k4_mem_exit.mpr ⟨hg, Finset.card_pos.mp (by omega), ?_⟩
    rintro ⟨x, hx⟩
    obtain ⟨hxs, hxT⟩ := Finset.mem_inter.mp hx
    have hxi := Finset.mem_singleton.mp (hpure (sem_supp_and_sub h.1 hg ht (!s) hxs))
    exact himiss (hxi ▸ hxT)
  rw [he, Finset.mem_union] at hexit
  rcases hexit with hh | hh
  · obtain ⟨j, hjI, heq⟩ := Finset.mem_image.mp hh
    have hje := (hp.1 j (hi hjI)).2.2.2
    rw [heq] at hje
    have hjm : j ∈ supp 10 D (src D (g, !s)) := by rw [hje]; simp
    have hji := Finset.mem_singleton.mp (hpure hjm)
    simpa only [hji] using heq.symm
  · obtain ⟨f, hf, heq⟩ := Finset.mem_image.mp hh
    have hh := hw f hf
    rw [heq] at hh
    rw [hh, Finset.card_singleton] at htwo
    omega

lemma assigned_source_exact {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hz : Bzero 10 D = 0) (hi : I ⊆ ineligSet 10 D)
    {pos wit : V → ℕ × Bool} (hp : k4_Pos 10 adj D pos)
    (hw : ∀ f ∈ T, supp 10 D (src D (wit f)) ∩ T = {f})
    (he : exitArcs 10 D (carrierT 10 D T) = I.image pos ∪ T.image wit)
    {i : V} (hiI : i ∈ I) :
    ∀ a, a ∈ supp 10 D (src D (pos i)) ↔ adj i a := by
  intro a
  have hchain := sem_noempty_chain_out graph_ok h hc hz (hi hiI)
  obtain ⟨g, s, hg, ht, hch, hmask⟩ := sem_exact_nbhd graph_ok h.1 hc {a}
    (by simpa only [Finset.mem_singleton, forall_eq] using graph_ok.2.1 a) hchain
  have heq := chain_and_assigned h hc hz hi hp hw he hiI hg ht hch
  simpa only [heq] using hmask a (Finset.mem_singleton_self a)

lemma T_neighbors_card : ∀ x ∈ T, (I.filter (fun i => adj i x)).card = 2 := by
  decide +kernel

lemma assigned_T_mask {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hz : Bzero 10 D = 0) (hi : I ⊆ ineligSet 10 D)
    (hm : (merges 10 D (carrierT 10 D T)).card = 3)
    (pos : V → ℕ × Bool) (hpos : k4_Pos 10 adj D pos) :
    ∀ i ∈ I, supp 10 D (src D (pos i)) ∩ T = nb i := by
  intro i hiI
  have hsub : nb i ⊆ supp 10 D (src D (pos i)) ∩ T := by
    intro a ha
    obtain ⟨hat, hia⟩ := Finset.mem_filter.mp ha
    exact Finset.mem_inter.mpr ⟨(hpos.1 i (hi hiI)).2.2.1 a hia, hat⟩
  have hproper : supp 10 D (src D (pos i)) ∩ T ⊂ T :=
    Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.inter_subset_right, no_full_mask h hc hz hi hm _⟩
  have hcard := Finset.card_lt_card hproper
  rw [T_card] at hcard
  have heq : nb i = supp 10 D (src D (pos i)) ∩ T :=
    Finset.eq_of_subset_of_card_le hsub (by rw [nb_card i hiI]; omega)
  exact heq.symm

lemma W_to_T_exit {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hz : Bzero 10 D = 0) (hi : I ⊆ ineligSet 10 D)
    (hm : (merges 10 D (carrierT 10 D T)).card = 3)
    {x : V} (hxT : x ∈ T) {e : ℕ × Bool} (he : e ∈ sem_W 10 D x) :
    e ∈ exitArcs 10 D (carrierT 10 D T) := by
  obtain ⟨hej, hxs, _⟩ := sem_mem_W.mp he
  apply k4_mem_exit.mpr
  refine ⟨hej, ⟨x, Finset.mem_inter.mpr ⟨hxs, hxT⟩⟩, ?_⟩
  rw [no_and_T_support h hc hz hi hm e.1 hej (sem_W_and h.1 he)]
  exact Finset.not_nonempty_empty

lemma T_codes_card_one_of_cover {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hz : Bzero 10 D = 0) (hi : I ⊆ ineligSet 10 D)
    (hm : (merges 10 D (carrierT 10 D T)).card = 3)
    (helig : T ⊆ eligSet 10 D) (b : V → ℕ) (hb : PureBranch 10 D b)
    (pos wit : V → ℕ × Bool) (hpos : k4_Pos 10 adj D pos)
    (hwit : ∀ x ∈ T, wit x ∈ sem_W 10 D x ∧
      supp 10 D (src D (wit x)) ∩ T = {x} ∧
      Disjoint (supp 10 D (src D (wit x))) (exposure x))
    (hcover : exitArcs 10 D (carrierT 10 D T) = I.image pos ∪ T.image wit) :
    ∀ x ∈ T, ((residualUnits 10 D b).filter (fun u => x ∈ supp 10 D u.1)).card = 1 := by
  classical
  intro x hxT
  let N := I.filter (fun i => adj i x)
  have hNcard : N.card = 2 := T_neighbors_card x hxT
  have hposmask := assigned_T_mask h hc hz hi hm pos hpos
  have hNimage : N.image pos ⊆ sem_W 10 D x := by
    intro e he
    obtain ⟨i, hiN, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hiI, hix⟩ := Finset.mem_filter.mp hiN
    obtain ⟨hij, hiempty, hineigh, _⟩ := hpos.1 i (hi hiI)
    apply sem_mem_W.mpr
    refine ⟨hij, hineigh x hix, ?_⟩
    rw [hiempty]
    exact Finset.notMem_empty x
  have hNinj : Set.InjOn pos N := by
    intro i hiN j hjN heq
    exact hpos.2 i (hi (Finset.mem_filter.mp hiN).1) j
      (hi (Finset.mem_filter.mp hjN).1) heq
  have hNimagecard : (N.image pos).card = 2 := by
    rw [Finset.card_image_of_injOn hNinj, hNcard]
  have hwit_not : wit x ∉ N.image pos := by
    intro hmem
    obtain ⟨i, hiN, heq⟩ := Finset.mem_image.mp hmem
    have hiI := (Finset.mem_filter.mp hiN).1
    obtain ⟨a, haA, hia⟩ := (incidence_ok i hiI).2 x hxT
    have has : a ∈ supp 10 D (src D (wit x)) := by
      rw [← heq]
      exact (hpos.1 i (hi hiI)).2.2.1 a hia
    exact Finset.disjoint_left.mp (hwit x hxT).2.2 has haA
  have hlow : 3 ≤ (sem_W 10 D x).card := by
    have hsub : insert (wit x) (N.image pos) ⊆ sem_W 10 D x :=
      Finset.insert_subset (hwit x hxT).1 hNimage
    have hcount := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hwit_not, hNimagecard] at hcount
    exact hcount
  have hupper : (sem_W 10 D x).card ≤ 3 := by
    have hsub : sem_W 10 D x ⊆ insert (wit x) (N.image pos) := by
      intro e he
      have hTe := W_to_T_exit h hc hz hi hm hxT he
      rw [hcover] at hTe
      rcases Finset.mem_union.mp hTe with hiPos | hiWit
      · obtain ⟨i, hiI, rfl⟩ := Finset.mem_image.mp hiPos
        have hxs := (sem_mem_W.mp he).2.1
        have hmask : x ∈ supp 10 D (src D (pos i)) ∩ T :=
          Finset.mem_inter.mpr ⟨hxs, hxT⟩
        rw [hposmask i hiI] at hmask
        have hix := (Finset.mem_filter.mp hmask).2
        exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
          ⟨i, Finset.mem_filter.mpr ⟨hiI, hix⟩, rfl⟩)
      · obtain ⟨f, hfT, rfl⟩ := Finset.mem_image.mp hiWit
        have hxs := (sem_mem_W.mp he).2.1
        have hmask : x ∈ supp 10 D (src D (wit f)) ∩ T :=
          Finset.mem_inter.mpr ⟨hxs, hxT⟩
        rw [(hwit f hfT).2.1, Finset.mem_singleton] at hmask
        subst f
        exact Finset.mem_insert_self _ _
    have hcount := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hwit_not, hNimagecard] at hcount
    exact hcount
  have hWcard : (sem_W 10 D x).card = 3 := by omega
  have hcode := sem_code_count graph_ok h hc b hb x
  have hsingle : ({x} : Finset V) ∩ eligSet 10 D = {x} :=
    Finset.singleton_inter_of_mem (helig hxT)
  rw [hWcard, no_singleton_T_merges h hc hz hi hm x hxT,
    Finset.card_empty, hsingle, Finset.card_singleton] at hcode
  omega

lemma T_eligible_of_exact_I {D : Dag} (hi : ineligSet 10 D = I) : T ⊆ eligSet 10 D := by
  intro x hxT
  by_contra hx
  have hxI : x ∈ I := by
    rw [← hi]
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩
  have hdis : Disjoint I T := by decide +kernel
  exact Finset.disjoint_left.mp hdis hxI hxT

lemma residual_meets_T {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hz : Bzero 10 D = 0) (hi : I ⊆ ineligSet 10 D)
    (b : V → ℕ) (hb : PureBranch 10 D b) (hr : (residualUnits 10 D b).card ≤ 3) :
    ∀ u ∈ residualUnits 10 D b, ∃ t ∈ T, t ∈ supp 10 D u.1 := by
  classical
  obtain ⟨hmerge, hexit⟩ := tight_counts h hc hz hi b hb hr
  have hflow := carrier_flow_union h T (by rw [sem_supp_out graph_ok hc]; simp)
  have hsur := surplus_carrierT_eq h.1 b hb T
  have hcar : (T ∩ eligSet 10 D).card ≤ 3 := by
    have := Finset.card_le_card (Finset.inter_subset_left : T ∩ eligSet 10 D ⊆ T)
    rwa [T_card] at this
  let Q := (residualUnits 10 D b).filter (fun u => (supp 10 D u.1 ∩ T).Nonempty)
  have hfilter : Q.card ≤ (residualUnits 10 D b).card := Finset.card_filter_le _ _
  rw [T_card, hmerge, hexit] at hflow
  have hQ : Q = residualUnits 10 D b :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by dsimp [Q] at *; omega)
  intro u hu
  rw [← hQ] at hu
  obtain ⟨t, ht⟩ := (Finset.mem_filter.mp hu).2
  exact ⟨t, (Finset.mem_inter.mp ht).2, (Finset.mem_inter.mp ht).1⟩

lemma residual_has_singleton_code {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hz : Bzero 10 D = 0) (hi : I ⊆ ineligSet 10 D)
    (b : V → ℕ) (hb : PureBranch 10 D b) (hr : (residualUnits 10 D b).card ≤ 3)
    (hcodes : ∀ t ∈ T,
      ((residualUnits 10 D b).filter (fun u => t ∈ supp 10 D u.1)).card = 1) :
    ∀ u ∈ residualUnits 10 D b, ∃ t ∈ T,
      (residualUnits 10 D b).filter (fun v => t ∈ supp 10 D v.1) = {u} := by
  classical
  intro u hu
  obtain ⟨t, htT, htu⟩ := residual_meets_T h hc hz hi b hb hr u hu
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp (hcodes t htT)
  have hucode : u ∈ (residualUnits 10 D b).filter (fun v => t ∈ supp 10 D v.1) :=
    Finset.mem_filter.mpr ⟨hu, htu⟩
  rw [hv, Finset.mem_singleton] at hucode
  exact ⟨t, htT, hv.trans (congrArg (fun z => ({z} : Finset (Σ _ : ℕ, ℕ))) hucode.symm)⟩

namespace JointExit

open H2

lemma support_or_exit_of_path {n : ℕ} {D : Dag} (hS : Strict n D) (t : Fin n)
    (hAnd : ∀ j, j < D.length → tag D j = true → t ∉ supp n D (n + j))
    {a b : ℕ} (hp : Relation.ReflTransGen (sem_step n D) a b)
    (hta : t ∈ supp n D a) :
    (t ∈ supp n D b ∧ supp n D a ⊆ supp n D b) ∨
      ∃ e ∈ exitArcs n D (carrierT n D {t}), supp n D a ⊆ supp n D (src D e) := by
  induction hp with
  | refl => exact Or.inl ⟨hta, Finset.Subset.refl _⟩
  | @tail u v hp hstep ih =>
    rcases ih with ⟨htu, hsub⟩ | hexit
    · obtain ⟨j, side, hj, rfl, hsrc⟩ := sem_step_iff.mp hstep
      by_cases htout : t ∈ supp n D (n + j)
      · have hor : tag D j = false := Bool.eq_false_iff.mpr (fun hand => hAnd j hj hand htout)
        have hkeep : supp n D u ⊆ supp n D (n + j) := by
          rw [← hsrc, sem_supp_or hS hj hor]
          cases side
          · rw [sb_src_false]
            exact Finset.subset_union_left
          · rw [sb_src_true]
            exact Finset.subset_union_right
        exact Or.inl ⟨htout, hsub.trans hkeep⟩
      · refine Or.inr ⟨(j, side), sem_mem_exit1.mpr ⟨hj, ?_, htout⟩, ?_⟩
        · simpa only [hsrc] using htu
        · simpa only [hsrc] using hsub
    · exact Or.inr hexit

lemma support_subset_exit {n : ℕ} {D : Dag} (h : StrictLive n D) (t : Fin n)
    (hout : t ∉ supp n D (outW n D))
    (hAnd : ∀ j, j < D.length → tag D j = true → t ∉ supp n D (n + j))
    {w : ℕ} (ht : t ∈ supp n D w) :
    ∃ e ∈ exitArcs n D (carrierT n D {t}), supp n D w ⊆ supp n D (src D e) := by
  have hp : Relation.ReflTransGen (sem_step n D) w (outW n D) :=
    live_reaches_out h w (sem_supp_lt ht)
  rcases support_or_exit_of_path h.1 t hAnd hp ht with ⟨htout, _⟩ | hexit
  · exact False.elim (hout htout)
  · exact hexit

lemma joint_support_exit {n : ℕ} {D : Dag} (h : StrictLive n D) (t c : Fin n)
    (hout : t ∉ supp n D (outW n D))
    (hAnd : ∀ j, j < D.length → tag D j = true → t ∉ supp n D (n + j))
    {w : ℕ} (ht : t ∈ supp n D w) (hc : c ∈ supp n D w) :
    ∃ e ∈ exitArcs n D (carrierT n D {t}),
      t ∈ supp n D (src D e) ∧ c ∈ supp n D (src D e) := by
  obtain ⟨e, he, hsub⟩ := support_subset_exit h t hout hAnd ht
  exact ⟨e, he, hsub ht, hsub hc⟩

lemma no_joint_support_of_exit_exclusion {n : ℕ} {D : Dag} (h : StrictLive n D)
    (t c : Fin n) (hout : t ∉ supp n D (outW n D))
    (hAnd : ∀ j, j < D.length → tag D j = true → t ∉ supp n D (n + j))
    (hexit : ∀ e ∈ exitArcs n D (carrierT n D {t}), c ∉ supp n D (src D e)) :
    ∀ w, t ∈ supp n D w → c ∉ supp n D w := by
  intro w ht hc
  obtain ⟨e, he, _, hce⟩ := joint_support_exit h t c hout hAnd ht hc
  exact hexit e he hce


end JointExit
namespace Finish

open H2

section Generic
variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

lemma sem_one_exit_pure (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {x : Fin n} {e : ℕ × Bool}
    (he : exitArcs n D (carrierT n D {x}) = {e}) :
    supp n D (src D e) = {x} := by
  have hex : e ∈ exitArcs n D (carrierT n D {x}) := by rw [he]; simp
  refine Finset.Subset.antisymm ?_ (Finset.singleton_subset_iff.mpr (sem_mem_exit1.mp hex).2.1)
  intro y hy
  rw [Finset.mem_singleton]
  by_contra hyx
  obtain ⟨z, hxz, hyz⟩ := hG.2.2.1 x y (Ne.symm hyx)
  have hA : ∀ a ∈ ({y, z} : Finset (Fin n)), ∀ b ∈ ({y, z} : Finset (Fin n)), ¬ G a b := by
    intro a ha b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact hG.2.1 _
    · exact hyz
    · exact fun h => hyz (hG.1 _ _ h)
    · exact hG.2.1 _
  obtain ⟨j, s, hj, _, hxs, hxn, hd⟩ := sem_exposure hG hS hC {y, z} hA x ⟨z, by simp, hxz⟩
  have hje : (j, s) = e := by
    have hm := sem_mem_exit1.mpr ⟨hj, hxs, hxn⟩
    rwa [he, Finset.mem_singleton] at hm
  exact Finset.disjoint_left.mp hd (by simpa only [hje] using hy) (by simp)


lemma sem_two_exit_other_pure (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {x z : Fin n} (hxz : x ≠ z) (hz : z ∈ ineligSet n D)
    {e f : ℕ × Bool} {S : Finset (Fin n)}
    (hW : exitArcs n D (carrierT n D {x}) ⊆ {e, f})
    (hf : f ∈ exitArcs n D (carrierT n D {x}))
    (hSub : S ⊆ supp n D (src D e))
    (hsep : ∀ y, y ≠ z → y ≠ x → ∃ A : Finset (Fin n),
      (∀ a ∈ A, ∀ b ∈ A, ¬ G a b) ∧ y ∈ A ∧
      (∃ a ∈ A, a ∈ S) ∧ ∃ a ∈ A, G x a) :
    supp n D (src D f) = {x} := by
  have hxf := (sem_mem_exit1.mp hf).2.1
  refine Finset.Subset.antisymm ?_ (Finset.singleton_subset_iff.mpr hxf)
  intro y hy
  rw [Finset.mem_singleton]
  by_contra hyx
  have hyz : y ≠ z := by
    intro hyz
    subst y
    have hp := sem_inelig_pure hG hS hC hz hy
    rw [hp, Finset.mem_singleton] at hxf
    exact hxz hxf
  obtain ⟨A, hA, hyA, ⟨a, haA, haS⟩, hnb⟩ := hsep y hyz hyx
  obtain ⟨j, s, hj, _, hxs, hxn, hd⟩ := sem_exposure hG hS hC A hA x hnb
  have heither := hW (sem_mem_exit1.mpr ⟨hj, hxs, hxn⟩)
  simp only [Finset.mem_insert, Finset.mem_singleton] at heither
  rcases heither with he | he
  · exact Finset.disjoint_left.mp hd (by simpa only [he] using hSub haS) haA
  · exact Finset.disjoint_left.mp hd (by simpa only [he] using hy) hyA

lemma sem_nonpure_exit_card (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {x y : Fin n} {e : ℕ × Bool}
    (he : e ∈ exitArcs n D (carrierT n D {x}))
    (hy : y ∈ supp n D (src D e)) (hyx : y ≠ x) :
    2 ≤ (exitArcs n D (carrierT n D {x})).card := by
  have hpos := Finset.card_pos.mpr ⟨e, he⟩
  by_contra hc
  have hone : (exitArcs n D (carrierT n D {x})).card = 1 := by omega
  obtain ⟨f, hf⟩ := Finset.card_eq_one.mp hone
  have hef : e = f := by rwa [hf, Finset.mem_singleton] at he
  rw [hef, sem_one_exit_pure hG hS hC hf, Finset.mem_singleton] at hy
  exact hyx hy


lemma sem_two_exit_remaining_slot (hG : sem_Gr G) (hS : Strict n D)
    (hC : sem_Comp n G D) {x z : Fin n} {e f : ℕ × Bool}
    (hW : exitArcs n D (carrierT n D {x}) ⊆ {e, f})
    (hbar : supp n D (src D (e.1, !e.2)) = {z}) {y : Fin n}
    (hxy : G x y) (hyz : y ≠ z) :
    (f.1, !f.2) ∈ exitArcs n D (carrierT n D {y}) := by
  obtain ⟨j, hj, _, _, hxn, hyn, s, hxs, _, hys, _⟩ := sem_joint_meeting hG hS hC hxy
  have heither := hW (sem_mem_exit1.mpr ⟨hj, hxs, hxn⟩)
  simp only [Finset.mem_insert, Finset.mem_singleton] at heither
  rcases heither with he | hf
  · have hy : y ∈ supp n D (src D (e.1, !e.2)) := by simpa only [← he] using hys
    rw [hbar, Finset.mem_singleton] at hy
    exact False.elim (hyz hy)
  · apply sem_mem_exit1.mpr
    simpa only [← hf] using And.intro hj (And.intro hys hyn)


end Generic

def M : Finset V := {1, 3, 7}

def center (x : V) : V := if x = 1 then 0 else if x = 3 then 8 else 9

def finishExposureMask (x y : V) : Nat :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 104, 20, 36, 80, 208, 276, 548,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 69, 50, 36, 0, 48, 36, 68, 208, 0, 548,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 69, 50, 20, 104, 20, 48, 68, 0, 276, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD
     (10 * x.val + y.val) 0

def finishExposure (x y : V) : Finset V :=
  Finset.univ.filter (fun a => (finishExposureMask x y).testBit a.val = true)

lemma finish_geometry : ∀ x ∈ M,
    center x ∈ I ∧ adj (center x) x ∧
    (∃ a : V, adj (center x) a ∧ a ≠ x) ∧
    adj x 2 ∧ (2 : V) ≠ center x ∧ x ≠ center x ∧ x ∉ T := by
  decide +kernel

lemma finish_exposure_ok : ∀ x ∈ M, ∀ y : V, y ≠ center x → y ≠ x →
    (∀ a ∈ finishExposure x y, ∀ b ∈ finishExposure x y, ¬ adj a b) ∧
    y ∈ finishExposure x y ∧
    (∃ a ∈ finishExposure x y, adj (center x) a) ∧
    ∃ a ∈ finishExposure x y, adj x a := by
  decide +kernel

lemma residual_outside_exits {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (b : V → ℕ) (hb : PureBranch 10 D b)
    (hr : ∀ u ∈ residualUnits 10 D b, supp 10 D u.1 ⊆ T)
    {x : V} (hx : x ∉ T) : (sem_W 10 D x).card ≤ 2 := by
  classical
  have hempty : (residualUnits 10 D b).filter (fun u => x ∈ supp 10 D u.1) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro u hu
    obtain ⟨hu, hxu⟩ := Finset.mem_filter.mp hu
    exact hx (hr u hu hxu)
  have count := sem_code_count graph_ok h hc b hb x
  rw [hempty, Finset.card_empty] at count
  have hone : (({x} : Finset V) ∩ eligSet 10 D).card ≤ 1 :=
    (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
  omega

lemma two_exit_cover {α : Type*} [DecidableEq α] {S : Finset α} {e : α}
    (hc : S.card = 2) (he : e ∈ S) : ∃ f, f ∈ S ∧ S ⊆ {e, f} := by
  obtain ⟨a, b, hab, hS⟩ := Finset.card_eq_two.mp hc
  rw [hS, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl
  · exact ⟨b, by simp [hS], by simp [hS]⟩
  · exact ⟨a, by simp [hS], by simp [hS, Finset.pair_comm]⟩

lemma middle_second_exit {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hi : I ⊆ ineligSet 10 D) (b : V → ℕ) (hb : PureBranch 10 D b)
    (hr : ∀ u ∈ residualUnits 10 D b, supp 10 D u.1 ⊆ T)
    {x : V} (hx : x ∈ M) :
    ∃ e ∈ sem_W 10 D (2 : V), supp 10 D (src D (sem_bar e)) = {x} := by
  classical
  obtain ⟨hci, hcx, ⟨a, hca, hax⟩, hx2, h2c, hxc, hxT⟩ := finish_geometry x hx
  obtain ⟨q, hq, _, hp, hout, hn, _, _⟩ := sem_inelig_consumer graph_ok h hc (hi hci)
  let e := sem_bar q
  have he : e ∈ sem_W 10 D x := by
    apply sem_mem_W.mpr
    refine ⟨hq, hn x hcx, ?_⟩
    change x ∉ supp 10 D (10 + q.1)
    rw [hout]
    exact Finset.notMem_empty x
  have ha : a ∈ supp 10 D (src D e) := hn a hca
  have hlo := sem_nonpure_exit_card graph_ok h.1 hc he ha hax
  change 2 ≤ (sem_W 10 D x).card at hlo
  have hhi := residual_outside_exits h hc b hb hr hxT
  obtain ⟨f, hf, hcover⟩ := two_exit_cover (by omega : (sem_W 10 D x).card = 2) he
  have hbar : supp 10 D (src D (e.1, !e.2)) = {center x} := by
    change supp 10 D (src D (sem_bar (sem_bar q))) = {center x}
    rwa [sem_bar_bar]
  have hfp : supp 10 D (src D f) = {x} := by
    apply sem_two_exit_other_pure graph_ok h.1 hc hxc (hi hci) hcover hf
      (S := Finset.univ.filter (adj (center x)))
    · intro v hv
      exact hn v (Finset.mem_filter.mp hv).2
    · intro y hyc hyx
      obtain ⟨hA, hyA, ⟨v, hvA, hcv⟩, hnb⟩ := finish_exposure_ok x hx y hyc hyx
      exact ⟨finishExposure x y, hA, hyA, ⟨v, hvA, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcv⟩⟩, hnb⟩
  refine ⟨sem_bar f, sem_two_exit_remaining_slot graph_ok h.1 hc hcover hbar hx2 h2c, ?_⟩
  rwa [sem_bar_bar]

lemma residual_supported_on_T_impossible {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hi : I ⊆ ineligSet 10 D)
    (b : V → ℕ) (hb : PureBranch 10 D b)
    (hr : ∀ u ∈ residualUnits 10 D b, supp 10 D u.1 ⊆ T) : False := by
  classical
  obtain ⟨e1, h1, hp1⟩ := middle_second_exit h hc hi b hb hr (x := 1) (by decide)
  obtain ⟨e3, h3, hp3⟩ := middle_second_exit h hc hi b hb hr (x := 3) (by decide)
  obtain ⟨e7, h7, hp7⟩ := middle_second_exit h hc hi b hb hr (x := 7) (by decide)
  have h13 : e1 ≠ e3 := by
    intro he
    have : ({1} : Finset V) = {3} := hp1.symm.trans (he ▸ hp3)
    exact (by decide : (1 : V) ≠ 3) (Finset.singleton_injective this)
  have h17 : e1 ≠ e7 := by
    intro he
    have : ({1} : Finset V) = {7} := hp1.symm.trans (he ▸ hp7)
    exact (by decide : (1 : V) ≠ 7) (Finset.singleton_injective this)
  have h37 : e3 ≠ e7 := by
    intro he
    have : ({3} : Finset V) = {7} := hp3.symm.trans (he ▸ hp7)
    exact (by decide : (3 : V) ≠ 7) (Finset.singleton_injective this)
  have hlo : 3 ≤ (sem_W 10 D (2 : V)).card :=
    Finset.two_lt_card.mpr ⟨e1, h1, e3, h3, e7, h7, h13, h17, h37⟩
  have hhi := residual_outside_exits h hc b hb hr (x := 2) (by decide)
  omega

end Finish

def privateNeighbor (t : V) : V := if t = 4 then 3 else if t = 5 then 7 else 1

lemma private_geometry : ∀ t ∈ T,
    privateNeighbor t ∈ exposure t ∧
      (∀ c, adj t c → c ∈ I ∨ c = privateNeighbor t) ∧
      ∀ i ∈ I, adj i t → ¬ adj i (privateNeighbor t) := by
  decide +kernel

lemma residual_support_pair_of_separation {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hz : Bzero 10 D = 0) (hi : I ⊆ ineligSet 10 D)
    (b : V → ℕ) (hb : PureBranch 10 D b) (hr : (residualUnits 10 D b).card ≤ 3)
    (hcodes : ∀ t ∈ T,
      ((residualUnits 10 D b).filter (fun u => t ∈ supp 10 D u.1)).card = 1)
    (hsep : ∀ t ∈ T, ∀ c, c ≠ t → ¬ adj t c →
      ¬ (∀ u ∈ residualUnits 10 D b, t ∈ supp 10 D u.1 → c ∈ supp 10 D u.1)) :
    ∀ u ∈ residualUnits 10 D b, ∃ t ∈ T, t ∈ supp 10 D u.1 ∧
      supp 10 D u.1 ⊆ {t, privateNeighbor t} := by
  classical
  intro u hu
  obtain ⟨t, htT, hcode⟩ := residual_has_singleton_code h hc hz hi b hb hr hcodes u hu
  have htu : t ∈ supp 10 D u.1 := by
    have hmem : u ∈ (residualUnits 10 D b).filter (fun v => t ∈ supp 10 D v.1) := by
      rw [hcode]
      exact Finset.mem_singleton_self u
    exact (Finset.mem_filter.mp hmem).2
  refine ⟨t, htT, htu, ?_⟩
  intro c hcU
  by_cases hct : c = t
  · rw [hct]
    simp
  · have hAdj : adj t c := by
      by_contra hnon
      apply hsep t htT c hct hnon
      intro v hv htv
      have hvc : v ∈ (residualUnits 10 D b).filter (fun z => t ∈ supp 10 D z.1) :=
        Finset.mem_filter.mpr ⟨hv, htv⟩
      rw [hcode, Finset.mem_singleton] at hvc
      simpa only [hvc] using hcU
    rcases (private_geometry t htT).2.1 c hAdj with hcI | hcp
    · have hfan : 2 ≤ fanout D u.1 := by
        have huUnits : u ∈ units 10 D :=
          (Finset.mem_filter.mp (Finset.mem_sdiff.mp hu).1).1
        have := (mem_units.mp huUnits).2
        omega
      have hlow := mem_ineligSet.mp (hi hcI) u.1 hcU
      omega
    · rw [hcp]
      simp

lemma private_neighbor_absent_at_exits {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hz : Bzero 10 D = 0) (hi : I ⊆ ineligSet 10 D)
    (hm : (merges 10 D (carrierT 10 D T)).card = 3)
    (pos wit : V → ℕ × Bool) (hpos : k4_Pos 10 adj D pos)
    (hwit : ∀ f ∈ T, wit f ∈ sem_W 10 D f ∧
      supp 10 D (src D (wit f)) ∩ T = {f} ∧
      Disjoint (supp 10 D (src D (wit f))) (exposure f))
    (hcover : exitArcs 10 D (carrierT 10 D T) = I.image pos ∪ T.image wit) :
    ∀ t ∈ T, ∀ e ∈ sem_W 10 D t, privateNeighbor t ∉ supp 10 D (src D e) := by
  intro t htT e he hprivate
  have hEt := W_to_T_exit h hc hz hi hm htT he
  rw [hcover] at hEt
  rcases Finset.mem_union.mp hEt with hposE | hwitE
  · obtain ⟨i, hiI, rfl⟩ := Finset.mem_image.mp hposE
    have hExact := assigned_source_exact h hc hz hi hpos
      (fun f hf => (hwit f hf).2.1) hcover hiI
    have hit := (hExact t).mp (sem_mem_W.mp he).2.1
    have him := (hExact (privateNeighbor t)).mp hprivate
    exact (private_geometry t htT).2.2 i hiI hit him
  · obtain ⟨f, hfT, rfl⟩ := Finset.mem_image.mp hwitE
    have htmask : t ∈ supp 10 D (src D (wit f)) ∩ T :=
      Finset.mem_inter.mpr ⟨(sem_mem_W.mp he).2.1, htT⟩
    rw [(hwit f hfT).2.1, Finset.mem_singleton] at htmask
    subst f
    exact Finset.disjoint_left.mp (hwit t htT).2.2 hprivate (private_geometry t htT).1

lemma private_neighbor_no_joint {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hz : Bzero 10 D = 0) (hi : I ⊆ ineligSet 10 D)
    (hm : (merges 10 D (carrierT 10 D T)).card = 3)
    (pos wit : V → ℕ × Bool) (hpos : k4_Pos 10 adj D pos)
    (hwit : ∀ f ∈ T, wit f ∈ sem_W 10 D f ∧
      supp 10 D (src D (wit f)) ∩ T = {f} ∧
      Disjoint (supp 10 D (src D (wit f))) (exposure f))
    (hcover : exitArcs 10 D (carrierT 10 D T) = I.image pos ∪ T.image wit) :
    ∀ t ∈ T, ∀ w, t ∈ supp 10 D w → privateNeighbor t ∉ supp 10 D w := by
  intro t htT
  apply JointExit.no_joint_support_of_exit_exclusion h t (privateNeighbor t)
  · rw [sem_supp_out graph_ok hc]
    exact Finset.notMem_empty t
  · intro j hj hop htj
    have hmj : t ∈ supp 10 D (10 + j) ∩ T := Finset.mem_inter.mpr ⟨htj, htT⟩
    rw [no_and_T_support h hc hz hi hm j hj hop] at hmj
    exact Finset.notMem_empty t hmj
  · exact private_neighbor_absent_at_exits h hc hz hi hm pos wit hpos hwit hcover t htT

lemma extendable_I_impossible_of_separation {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hlen : D.length ≤ 19) (hi : ineligSet 10 D = I)
    (b : V → ℕ) (hb : PureBranch 10 D b)
    (hsep : ∀ t ∈ T, ∀ c, c ≠ t → ¬ adj t c →
      ¬ (∀ u ∈ residualUnits 10 D b, t ∈ supp 10 D u.1 → c ∈ supp 10 D u.1)) : False := by
  obtain ⟨_, hz, hr, _⟩ := tight_budget h hc hlen hi b hb
  have hsub : I ⊆ ineligSet 10 D := by rw [hi]
  obtain ⟨hm, he⟩ := tight_counts h hc hz hsub b hb hr.le
  obtain ⟨pos, wit, hpos, hwit, hcover⟩ := tight_exit_data h hc hsub he
  have hcodes := T_codes_card_one_of_cover h hc hz hsub hm
    (T_eligible_of_exact_I hi) b hb pos wit hpos hwit hcover
  have hpair := residual_support_pair_of_separation h hc hz hsub b hb hr.le hcodes hsep
  have hprivate := private_neighbor_no_joint h hc hz hsub hm pos wit hpos hwit hcover
  apply Finish.residual_supported_on_T_impossible h hc hsub b hb
  intro u hu c hcU
  obtain ⟨t, htT, htu, hsupport⟩ := hpair u hu
  have hwhich := hsupport hcU
  simp only [Finset.mem_insert, Finset.mem_singleton] at hwhich
  rcases hwhich with hct | hcp
  · exact hct ▸ htT
  · exact False.elim (hprivate t htT u.1 htu (hcp ▸ hcU))

def separationCenter (t c : V) : V :=
  if adj 0 t ∧ ¬ adj 0 c then 0 else if adj 8 t ∧ ¬ adj 8 c then 8 else 9

def separationMask (t c : V) : Nat :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 138, 548, 0, 0, 104, 104, 138, 770, 0, 0, 138, 276, 138, 208, 0, 208, 0, 0, 770, 521, 0, 548, 138, 50, 50, 0, 138, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List Nat).getD (10 * t.val + c.val) 0

def separationExposure (t c : V) : Finset V :=
  Finset.univ.filter (fun a => (separationMask t c).testBit a.val = true)

lemma separation_geometry : ∀ t ∈ T, ∀ c : V, c ≠ t → ¬ adj t c →
    separationCenter t c ∈ I ∧ adj (separationCenter t c) t ∧
      ¬ adj (separationCenter t c) c ∧
      (∀ a ∈ separationExposure t c, ∀ b ∈ separationExposure t c, ¬ adj a b) ∧
      c ∈ separationExposure t c ∧
      (∃ a ∈ separationExposure t c, adj (separationCenter t c) a) ∧
      ∃ a ∈ separationExposure t c, adj t a := by
  decide +kernel

lemma separation_from_exact_stars {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hi : I ⊆ ineligSet 10 D)
    (b : V → ℕ) (hb : PureBranch 10 D b) (helig : T ⊆ eligSet 10 D)
    (hnonempty : ∀ t ∈ T,
      ((residualUnits 10 D b).filter (fun u => t ∈ supp 10 D u.1)).Nonempty)
    (pos : V → ℕ × Bool) (hpos : k4_Pos 10 adj D pos)
    (hexact : ∀ i ∈ I, ∀ a, a ∈ supp 10 D (src D (pos i)) ↔ adj i a) :
    ∀ t ∈ T, ∀ c, c ≠ t → ¬ adj t c →
      ¬ (∀ u ∈ residualUnits 10 D b, t ∈ supp 10 D u.1 → c ∈ supp 10 D u.1) := by
  intro t htT c hct htc hres
  obtain ⟨u, hu⟩ := hnonempty t htT
  obtain ⟨huR, htu⟩ := Finset.mem_filter.mp hu
  have hcu := hres u huR htu
  obtain ⟨exception, hrest⟩ := ri_gen graph_ok h hc b hb hct.symm (helig htT) hres ⟨htu, hcu⟩
  obtain ⟨hiI, hit, hic, hA, hcA, ⟨a, haA, hia⟩, htnb⟩ :=
    separation_geometry t htT c hct htc
  let i := separationCenter t c
  have hstar : pos i ∈ sem_W 10 D t := by
    obtain ⟨hij, hio, hin, _⟩ := hpos.1 i (hi hiI)
    apply sem_mem_W.mpr
    refine ⟨hij, hin t hit, ?_⟩
    rw [hio]
    exact Finset.notMem_empty t
  have hstar_c : c ∉ supp 10 D (src D (pos i)) := fun hcs => hic ((hexact i hiI c).mp hcs)
  obtain ⟨j, side, hj, _, htj, htout, hdis⟩ :=
    sem_exposure graph_ok h.1 hc (separationExposure t c) hA t htnb
  have hexpose : (j, side) ∈ sem_W 10 D t := sem_mem_W.mpr ⟨hj, htj, htout⟩
  have hexpose_c : c ∉ supp 10 D (src D (j, side)) :=
    fun hcs => Finset.disjoint_left.mp hdis hcs hcA
  have hne : pos i ≠ (j, side) := by
    intro heq
    have has : a ∈ supp 10 D (src D (j, side)) := by
      rw [← heq]
      exact (hpos.1 i (hi hiI)).2.2.1 a hia
    exact Finset.disjoint_left.mp hdis has haA
  have hstar_exception : pos i = exception := by
    by_contra hnot
    exact hstar_c (hrest (pos i) hstar hnot)
  have hexpose_exception : (j, side) = exception := by
    by_contra hnot
    exact hexpose_c (hrest (j, side) hexpose hnot)
  exact hne (hstar_exception.trans hexpose_exception.symm)

lemma extendable_I_impossible {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hlen : D.length ≤ 19) (hi : ineligSet 10 D = I) : False := by
  obtain ⟨b, hb⟩ := sem_exists_pureBranch graph_ok h.1 hc
  apply extendable_I_impossible_of_separation h hc hlen hi b hb
  obtain ⟨_, hz, hr, _⟩ := tight_budget h hc hlen hi b hb
  have hsub : I ⊆ ineligSet 10 D := by rw [hi]
  obtain ⟨hm, he⟩ := tight_counts h hc hz hsub b hb hr.le
  obtain ⟨pos, wit, hpos, hwit, hcover⟩ := tight_exit_data h hc hsub he
  have helig := T_eligible_of_exact_I hi
  have hcodes := T_codes_card_one_of_cover h hc hz hsub hm helig b hb pos wit hpos hwit hcover
  apply separation_from_exact_stars h hc hsub b hb helig ?_ pos hpos
    (fun i hiI => assigned_source_exact h hc hz hsub hpos
      (fun f hf => (hwit f hf).2.1) hcover hiI)
  intro t htT
  apply Finset.card_pos.mp
  rw [hcodes t htT]
  decide

lemma relabel_computes {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (σ : Equiv.Perm V) (hσ : ∀ u v, adj (σ u) (σ v) ↔ adj u v) :
    sem_Comp 10 adj (relabel σ D) := by
  intro x
  rw [relabel_out σ h.1 h.2.2]
  constructor
  · intro hx
    obtain ⟨u, v, huv, hu, hv⟩ := (hc _).mp hx
    exact ⟨σ u, σ v, (hσ u v).mpr huv, hu, hv⟩
  · rintro ⟨u, v, huv, hu, hv⟩
    apply (hc _).mpr
    refine ⟨σ.symm u, σ.symm v, ?_, ?_, ?_⟩
    · apply (hσ _ _).mp
      simpa using huv
    · simpa using hu
    · simpa using hv

lemma canonicalize_three_ineligible {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hi : (ineligSet 10 D).card = 3) :
    ∃ D' : Dag, StrictLive 10 D' ∧ sem_Comp 10 adj D' ∧ D'.length = D.length ∧
      (ineligSet 10 D' = ({1, 4, 5} : Finset V) ∨ ineligSet 10 D' = I) := by
  have hind : I3Geometry.Independent (ineligSet 10 D) := by
    intro u hu v hv huv
    rcases sem_elig_cover graph_ok h hc huv with hu' | hv'
    · exact (sem_mem_inelig.mp hu) hu'
    · exact (sem_mem_inelig.mp hv) hv'
  obtain ⟨σ, hσ, heq⟩ := I3Geometry.classify (ineligSet 10 D) hi hind
  refine ⟨relabel σ D, relabel_strictLive σ h, relabel_computes h hc σ hσ,
    relabel_length σ D, ?_⟩
  rw [relabel_ineligSet σ h.1]
  rcases heq with heq | heq
  · exact Or.inl (heq.trans I3Geometry.canonical_masks.1)
  · exact Or.inr (heq.trans I3Geometry.canonical_masks.2)

lemma reduce_three_to_neighborhood {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hlen : D.length ≤ 19)
    (hi : (ineligSet 10 D).card = 3) :
    ∃ D' : Dag, StrictLive 10 D' ∧ sem_Comp 10 adj D' ∧ D'.length = D.length ∧
      ineligSet 10 D' = ({1, 4, 5} : Finset V) := by
  obtain ⟨D', h', hc', hl, hN | hI⟩ := canonicalize_three_ineligible h hc hi
  · exact ⟨D', h', hc', hl, hN⟩
  · exact False.elim (extendable_I_impossible h' hc' (by omega) hI)

namespace NeighborCover

open H2 Finish

section Generic
variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

end Generic

end NeighborCover


end I3Branch

lemma petersen_three_ineligible_exclusion {D : H2.Dag} (h : H2.StrictLive 10 D)
    (hc : H2.sem_Comp 10 H2.adj D) (hlen : D.length ≤ 19)
    (hi : (H2.ineligSet 10 D).card = 3) : False := by
  obtain ⟨D', h', hc', hl, hi'⟩ := I3Branch.reduce_three_to_neighborhood h hc hlen hi
  exact H2.n0_neighborhood_impossible h' hc' hi' (by omega)

end PEqualNP.Outside.L_meta_2590_aux

namespace PEqualNP.Outside.L_meta_2590_aux.S14Ledger
open H2

def mask (m : Nat) : Finset V := Finset.univ.filter (fun x => m.testBit x.val = true)

def target (t : Fin 7) : Finset V := mask (([0,4,64,68,8,512,520] : List Nat).getD t.val 0)

def side (t : Fin 7) (positive : Bool) (i : Fin 12) : Finset V :=
  ([mask 1,mask 50,mask 2,mask 68 \ target t,mask 16,mask 520 \ target t,
    mask 32,mask 384,(if positive then mask 50 else mask 18),
    (if positive then mask 32 ∪ target t else target t),mask 200,mask 772] :
    List (Finset V)).getD i.val ∅

def opposite (i : Fin 12) : Fin 12 :=
  ⟨(([1,0,3,2,5,4,7,6,9,8,11,10] : List Nat).getD i.val 0) % 12,
    Nat.mod_lt _ (by decide)⟩

def exitSide (t : Fin 7) (positive : Bool) (i : Fin 12) : Finset V :=
  side t positive i \ side t positive (opposite i)

def incidence (x : V) : Nat :=
  ([1,3,2,2,3,2,2,2,2,2] : List Nat).getD x.val 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 1000000 in
lemma profile_incidence : ∀ t : Fin 7, ∀ positive : Bool, ∀ x : V,
    (Finset.univ.filter (fun i : Fin 12 => x ∈ exitSide t positive i)).card = incidence x := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 1000000 in
lemma indexed_intersections : ∀ t : Fin 7, ∀ positive : Bool, ∀ i : Fin 12,
    side t positive i ∩ side t positive (opposite i) =
      if positive = true ∧ (i = 8 ∨ i = 9) then {5} else ∅ := by
  decide +kernel

def known (t : Fin 7) (positive : Bool) (r : Fin 12 → Nat × Bool) (x : V) : Finset (Nat × Bool) :=
  (Finset.univ.filter (fun i : Fin 12 => x ∈ exitSide t positive i)).image r

lemma known_card (t : Fin 7) (positive : Bool) (r : Fin 12 → Nat × Bool)
    (inj : Function.Injective r) (x : V) : (known t positive r x).card = incidence x := by
  rw [known,Finset.card_image_of_injective _ inj,profile_incidence]

lemma output_support {D : Dag} (h : Strict 10 D) (t : Fin 7) (positive : Bool)
    (r : Fin 12 → Nat × Bool)
    (valid : ∀ i, (r i).1 < D.length ∧ tag D (r i).1 = true)
    (paired : ∀ i, r (opposite i) = sem_bar (r i))
    (source : ∀ i, supp 10 D (src D (r i)) = side t positive i) (i : Fin 12) :
    supp 10 D (10+(r i).1) = side t positive i ∩ side t positive (opposite i) := by
  have ha := source i
  have hb := source (opposite i)
  rw [paired i] at hb
  rw [sem_supp_and h (valid i).1 (valid i).2]
  cases hs : (r i).2
  · have a : supp 10 D (opA D (r i).1) = side t positive i := by simpa [src,hs] using ha
    have b : supp 10 D (opB D (r i).1) = side t positive (opposite i) := by simpa [src,sem_bar,hs] using hb
    rw [a,b]
  · have a : supp 10 D (opB D (r i).1) = side t positive i := by simpa [src,hs] using ha
    have b : supp 10 D (opA D (r i).1) = side t positive (opposite i) := by simpa [src,sem_bar,hs] using hb
    rw [a,b,Finset.inter_comm]

lemma known_subset {D : Dag} (h : Strict 10 D) (t : Fin 7) (positive : Bool)
    (r : Fin 12 → Nat × Bool)
    (valid : ∀ i, (r i).1 < D.length ∧ tag D (r i).1 = true)
    (paired : ∀ i, r (opposite i) = sem_bar (r i))
    (source : ∀ i, supp 10 D (src D (r i)) = side t positive i) (x : V) :
    known t positive r x ⊆ sem_W 10 D x := by
  intro a ha
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
  have hx := Finset.mem_sdiff.mp ((Finset.mem_filter.mp hi).2 : x ∈ exitSide t positive i)
  apply sem_mem_W.mpr
  refine ⟨(valid i).1,?_,?_⟩
  · rw [source i]
    exact hx.1
  · rw [output_support h t positive r valid paired source i]
    intro hout
    exact hx.2 (Finset.mem_inter.mp hout).2

lemma upper_counts_cover {D : Dag} (h : Strict 10 D) (t : Fin 7) (positive : Bool)
    (r : Fin 12 → Nat × Bool) (inj : Function.Injective r)
    (valid : ∀ i, (r i).1 < D.length ∧ tag D (r i).1 = true)
    (paired : ∀ i, r (opposite i) = sem_bar (r i))
    (source : ∀ i, supp 10 D (src D (r i)) = side t positive i)
    (upper : ∀ x : V, (sem_W 10 D x).card ≤ incidence x) :
    ∀ x : V, sem_W 10 D x = known t positive r x := by
  intro x
  apply (Finset.eq_of_subset_of_card_le (known_subset h t positive r valid paired source x) ?_).symm
  rw [known_card t positive r inj x]
  exact upper x

lemma nonindexed_inputs_empty {D : Dag} (h : Strict 10 D) (t : Fin 7) (positive : Bool)
    (r : Fin 12 → Nat × Bool) (inj : Function.Injective r)
    (valid : ∀ i, (r i).1 < D.length ∧ tag D (r i).1 = true)
    (paired : ∀ i, r (opposite i) = sem_bar (r i))
    (source : ∀ i, supp 10 D (src D (r i)) = side t positive i)
    (upper : ∀ x : V, (sem_W 10 D x).card ≤ incidence x)
    {g : Nat} (hg : g < D.length) (hout : supp 10 D (10+g) = ∅)
    (nonindexed : ∀ i : Fin 12, (r i).1 ≠ g) :
    supp 10 D (opA D g) = ∅ ∧ supp 10 D (opB D g) = ∅ := by
  have allCover := upper_counts_cover h t positive r inj valid paired source upper
  have arcEmpty (s : Bool) : supp 10 D (src D (g,s)) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro x hx
    have he : (g,s) ∈ sem_W 10 D x := sem_mem_W.mpr ⟨hg,hx,by rw [hout]; simp⟩
    rw [allCover x] at he
    obtain ⟨i,_,eq⟩ := Finset.mem_image.mp he
    exact nonindexed i (congrArg Prod.fst eq)
  exact ⟨by simpa only [sb_src_false] using arcEmpty false,
    by simpa only [sb_src_true] using arcEmpty true⟩

lemma conditional_ledger {D : Dag} (h : Strict 10 D) (t : Fin 7) (positive : Bool)
    (r : Fin 12 → Nat × Bool) (inj : Function.Injective r)
    (valid : ∀ i, (r i).1 < D.length ∧ tag D (r i).1 = true)
    (paired : ∀ i, r (opposite i) = sem_bar (r i))
    (source : ∀ i, supp 10 D (src D (r i)) = side t positive i)
    (upper : ∀ x : V, (sem_W 10 D x).card ≤ incidence x)
    (extraEmpty : ∀ g, g < D.length → tag D g = true →
      (∀ i : Fin 12, (r i).1 ≠ g) → supp 10 D (10+g) = ∅) :
    (∀ x : V, sem_W 10 D x = known t positive r x) ∧
    (∀ g, g < D.length → tag D g = true → (∀ i : Fin 12, (r i).1 ≠ g) →
      supp 10 D (opA D g) = ∅ ∧ supp 10 D (opB D g) = ∅) := by
  refine ⟨upper_counts_cover h t positive r inj valid paired source upper,?_⟩
  intro g hg ht hn
  exact nonindexed_inputs_empty h t positive r inj valid paired source upper hg (extraEmpty g hg ht hn) hn

lemma target_injective : Function.Injective target := by decide +kernel

lemma target_choices (T : Finset V)
    (hT : T ∈ ({mask 0,mask 4,mask 64,mask 68,mask 8,mask 512,mask 520} : Finset (Finset V))) :
    ∃ t : Fin 7, T = target t := by
  simp only [Finset.mem_insert,Finset.mem_singleton] at hT
  rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0,rfl⟩
  · exact ⟨1,rfl⟩
  · exact ⟨2,rfl⟩
  · exact ⟨3,rfl⟩
  · exact ⟨4,rfl⟩
  · exact ⟨5,rfl⟩
  · exact ⟨6,rfl⟩

lemma ledger_of_noncommon_outputs_empty {D : Dag} (h : Strict 10 D) (t : Fin 7) (positive : Bool)
    (r : Fin 12 → Nat × Bool) (inj : Function.Injective r)
    (valid : ∀ i, (r i).1 < D.length ∧ tag D (r i).1 = true)
    (paired : ∀ i, r (opposite i) = sem_bar (r i))
    (source : ∀ i, supp 10 D (src D (r i)) = side t positive i)
    (upper : ∀ x : V, (sem_W 10 D x).card ≤ incidence x)
    (otherEmpty : ∀ g, g < D.length → tag D g = true → g ≠ (r 8).1 →
      supp 10 D (10+g) = ∅) :
    (∀ x : V, sem_W 10 D x = known t positive r x) ∧
    (∀ g, g < D.length → tag D g = true → (∀ i : Fin 12, (r i).1 ≠ g) →
      supp 10 D (opA D g) = ∅ ∧ supp 10 D (opB D g) = ∅) := by
  apply conditional_ledger h t positive r inj valid paired source upper
  intro g hg ht hn
  exact otherEmpty g hg ht (Ne.symm (hn 8))

end PEqualNP.Outside.L_meta_2590_aux.S14Ledger


namespace PEqualNP.Outside.L_meta_2590_aux.S14Positive

abbrev State := Nat × List Nat × List Nat

def values (bits : Nat) : List Nat := (List.range 64).filter bits.testBit

def pairMasks (op : Nat → Nat → Nat) (a b : Nat) : Nat :=
  (values a).foldl (fun acc x =>
    (values b).foldl (fun acc y => acc ||| (1 <<< op x y)) acc) 0

def mergePools (a b : Nat) : Nat := pairMasks (· ||| ·) a b

def addCarrier (pool k : Nat) : Nat := pool ||| mergePools pool (1 <<< k)

def rows : List Nat := [68,520,384,12,320,640]

def classes (_T : Nat) : List Nat := [1,2,16,32,68,520,384]

def side (T g : Nat) (right : Bool) : Nat :=
  if g = 0 then if right then 50 else 1
  else if g = 1 then if right then 32 ||| T else 50
  else if g = 2 then if right then 68 - (68 &&& T) else 2
  else if g = 3 then if right then 520 - (520 &&& T) else 16
  else if right then 384 else 32

def rawMask (A : Nat) : Nat :=
  (List.range 6).foldl (fun acc i =>
    if (rows.getD i 0 &&& A) = 0 then acc else acc ||| (1 <<< i)) 0

def positivePool (T : Nat) (ps : List Nat) (g : Nat) (right : Bool) : Nat :=
  let A := side T g right
  let pool := (List.range (classes T).length).foldl (fun acc i =>
    if (classes T).getD i 0 &&& A = 0 then acc
    else mergePools acc (ps.getD i 1)) 1
  pairMasks (· ||| ·) pool (1 <<< rawMask A)

def live (T used loc : Nat) : Bool :=
  (List.range 5).any fun g => !used.testBit g &&
    decide ((classes T).getD loc 0 &&& (side T g false ||| side T g true) ≠ 0)

def sortedInsert (k : Nat) : List Nat → List Nat
  | [] => [k]
  | x :: xs => if k ≤ x then k :: x :: xs else x :: sortedInsert k xs

def zeroSort : List Nat → List Nat
  | [] => []
  | x :: xs => sortedInsert x (zeroSort xs)

def prune (T : Nat) (s : State) : State :=
  (s.1, (List.range (classes T).length).map (fun i =>
    if live T s.1 i then s.2.1.getD i 1 else 1),
    zeroSort (s.2.2.filter fun k => k != 0))

def insertZero (k : Nat) (zs : List Nat) : List Nat := zeroSort (k :: zs)

def fire (T g k : Nat) (s : State) (rest : List Nat) : State :=
  if g = 1 then
    prune T (s.1 ||| (1 <<< g),
      s.2.1.set 3 (addCarrier (s.2.1.getD 3 1) k), rest)
  else prune T (s.1 ||| (1 <<< g), s.2.1, insertZero k rest)

def groupNext (T : Nat) (s : State) : List State :=
  (List.range 5).flatMap fun g =>
    if s.1.testBit g then [] else
    if side T g false ≠ 0 ∧ side T g true ≠ 0 then
      (values (pairMasks (· &&& ·) (positivePool T s.2.1 g false)
        (positivePool T s.2.1 g true))).filterMap fun k =>
          if k = 0 then none else
          some (fire T g k s s.2.2)
    else
      s.2.2.flatMap fun z =>
        (values (positivePool T s.2.1 g (decide (side T g false = 0)))).filterMap fun p =>
          let k := z &&& p
          if k = 0 then none else
          some (fire T g k s (s.2.2.erase z))

def liftNext (T : Nat) (s : State) : List State :=
  s.2.2.flatMap fun k => (List.range (classes T).length).filterMap fun loc =>
    if live T s.1 loc then
      let old := s.2.1.getD loc 1
      let new := addCarrier old k
      some (prune T (s.1, s.2.1.set loc new, s.2.2.erase k))
    else none

def discardNext (T : Nat) (s : State) : List State :=
  s.2.2.map fun k => prune T (s.1, s.2.1, s.2.2.erase k)

def combineNext (T : Nat) (s : State) : List State :=
  s.2.2.flatMap fun a => (s.2.2.erase a).flatMap fun b =>
    [a &&& b, a ||| b].filterMap fun k => if k = 0 then none else
      some (prune T (s.1, s.2.1, insertZero k ((s.2.2.erase a).erase b)))

def successors (T : Nat) (s : State) : List State :=
  groupNext T s ++ liftNext T s ++ discardNext T s ++ combineNext T s

def initial (T : Nat) : State := (0, List.replicate (classes T).length 1, [63])

def listLess : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a = b then listLess as bs else decide (a < b)

def stateLess (a b : State) : Bool :=
  if a.1 ≠ b.1 then decide (a.1 < b.1)
  else if a.2.1 ≠ b.2.1 then listLess a.2.1 b.2.1
  else listLess a.2.2 b.2.2

def safe (s : State) : Bool := !s.2.2.contains 56

end PEqualNP.Outside.L_meta_2590_aux.S14Positive

namespace PEqualNP.Outside.L_meta_2590_aux.S14Positive.Certificate

lemma reachable_mem {α : Type} (states : List α) (next : α → List α)
    (contains : α → Bool)
    (hcontains : ∀ s, contains s = true → s ∈ states)
    (hclosed : states.all (fun s => (next s).all contains) = true)
    {start finish : α} (hstart : contains start = true)
    (hreach : Relation.ReflTransGen (fun a b => b ∈ next a) start finish) :
    finish ∈ states := by
  have step : ∀ a ∈ states, ∀ b ∈ next a, b ∈ states := by
    intro a ha b hb
    exact hcontains b (List.all_eq_true.mp (List.all_eq_true.mp hclosed a ha) b hb)
  induction hreach with
  | refl => exact hcontains start hstart
  | @tail b c hab hbc ih => exact step b ih c hbc

lemma reachable_safe {α : Type} (states : List α) (next : α → List α)
    (contains safe : α → Bool)
    (hcontains : ∀ s, contains s = true → s ∈ states)
    (hclosed : states.all (fun s => (next s).all contains) = true)
    (hsafe : states.all safe = true)
    {start finish : α} (hstart : contains start = true)
    (hreach : Relation.ReflTransGen (fun a b => b ∈ next a) start finish) :
    safe finish = true := by
  exact List.all_eq_true.mp hsafe finish
    (reachable_mem states next contains hcontains hclosed hstart hreach)

def searchIndex {α : Type} [BEq α] (lt : α → α → Bool)
    (get : Nat → α) (bound : Nat) (needle : α) : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, lo, hi =>
      if lo < hi then
        let mid := (lo + hi) / 2
        if mid < bound then
          if get mid == needle then true
          else if lt needle (get mid) then
            searchIndex lt get bound needle fuel lo mid
          else searchIndex lt get bound needle fuel (mid + 1) hi
        else false
      else false

lemma searchIndex_sound {α : Type} [BEq α] [LawfulBEq α]
    (lt : α → α → Bool) (get : Nat → α) (bound : Nat)
    (needle : α) (fuel lo hi : Nat)
    (hsearch : searchIndex lt get bound needle fuel lo hi = true) :
    ∃ i < bound, get i = needle := by
  induction fuel generalizing lo hi with
  | zero => simp [searchIndex] at hsearch
  | succ fuel ih =>
      simp only [searchIndex] at hsearch
      split at hsearch
      next hlt =>
        split at hsearch
        next hmid =>
          split at hsearch
          next heq => exact ⟨(lo + hi) / 2, hmid, eq_of_beq heq⟩
          next hne =>
            split at hsearch
            next => exact ih _ _ hsearch
            next => exact ih _ _ hsearch
        next => cases hsearch
      next => cases hsearch

lemma index_reachable_safe {α : Type} (get : Nat → α) (bound : Nat)
    (next : α → List α) (contains safe : α → Bool)
    (hcontains : ∀ s, contains s = true → ∃ i < bound, get i = s)
    (hclosed : (List.range bound).all
      (fun i => (next (get i)).all contains) = true)
    (hsafe : (List.range bound).all (fun i => safe (get i)) = true)
    {start finish : α} (hstart : contains start = true)
    (hreach : Relation.ReflTransGen (fun a b => b ∈ next a) start finish) :
    safe finish = true := by
  apply reachable_safe ((List.range bound).map get) next contains safe ?_
      ?_ ?_ hstart hreach
  · intro s hs
    obtain ⟨i, hi, heq⟩ := hcontains s hs
    exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, heq⟩
  · simpa only [List.all_map, Function.comp_def] using hclosed
  · simpa only [List.all_map, Function.comp_def] using hsafe

lemma chunked_all (checked : Nat → Bool) (bound width count : Nat)
    (hwidth : 0 < width) (hbound : bound ≤ count * width)
    (hchunks : ∀ k < count, (List.range width).all
      (fun j => if k * width + j < bound then checked (k * width + j) else true) = true) :
    (List.range bound).all checked = true := by
  apply List.all_eq_true.mpr
  intro i hi
  have hibound : i < bound := List.mem_range.mp hi
  have hk : i / width < count :=
    (Nat.div_lt_iff_lt_mul hwidth).mpr (Nat.lt_of_lt_of_le hibound hbound)
  have hj : i % width < width := Nat.mod_lt _ hwidth
  have hsum : i / width * width + i % width = i := by
    rw [Nat.mul_comm, Nat.div_add_mod]
  have h := List.all_eq_true.mp (hchunks (i / width) hk)
    (i % width) (List.mem_range.mpr hj)
  simpa only [hsum, ite_eq_left hibound] using h

lemma all_and_parts {α : Type} (xs : List α) (p q : α → Bool)
    (h : xs.all (fun a => p a && q a) = true) :
    xs.all p = true ∧ xs.all q = true := by
  constructor
  · apply List.all_eq_true.mpr
    intro a ha
    exact (Bool.and_eq_true_iff.mp (List.all_eq_true.mp h a ha)).1
  · apply List.all_eq_true.mpr
    intro a ha
    exact (Bool.and_eq_true_iff.mp (List.all_eq_true.mp h a ha)).2

lemma chunked_index_reachable_safe {α : Type}
    (get : Nat → α) (bound width count : Nat)
    (next : α → List α) (contains safe : α → Bool)
    (hwidth : 0 < width) (hbound : bound ≤ count * width)
    (hcontains : ∀ s, contains s = true → ∃ i < bound, get i = s)
    (hchunks : ∀ k < count, (List.range width).all (fun j =>
      if k * width + j < bound then
        safe (get (k * width + j)) && (next (get (k * width + j))).all contains
      else true) = true)
    {start finish : α} (hstart : contains start = true)
    (hreach : Relation.ReflTransGen (fun a b => b ∈ next a) start finish) :
    safe finish = true := by
  have hall := chunked_all (fun i => safe (get i) && (next (get i)).all contains)
    bound width count hwidth hbound hchunks
  obtain ⟨hsafe, hclosed⟩ := all_and_parts (List.range bound)
    (fun i => safe (get i)) (fun i => (next (get i)).all contains) hall
  exact index_reachable_safe get bound next contains safe hcontains hclosed hsafe hstart hreach

lemma chunked_searchIndex_reachable_safe {α : Type} [BEq α] [LawfulBEq α]
    (lt : α → α → Bool) (get : Nat → α) (bound width count fuel : Nat)
    (next : α → List α) (safe : α → Bool)
    (hwidth : 0 < width) (hbound : bound ≤ count * width)
    (hchunks : ∀ k < count, (List.range width).all (fun j =>
      if k * width + j < bound then
        safe (get (k * width + j)) && (next (get (k * width + j))).all
          (fun s => searchIndex lt get bound s fuel 0 bound)
      else true) = true)
    {start finish : α}
    (hstart : searchIndex lt get bound start fuel 0 bound = true)
    (hreach : Relation.ReflTransGen (fun a b => b ∈ next a) start finish) :
    safe finish = true := by
  exact chunked_index_reachable_safe get bound width count next
    (fun s => searchIndex lt get bound s fuel 0 bound) safe hwidth hbound
    (fun s hs => searchIndex_sound lt get bound s fuel 0 bound hs)
    hchunks hstart hreach

end PEqualNP.Outside.L_meta_2590_aux.S14Positive.Certificate


namespace PEqualNP.Outside.L_meta_2590_aux.S14Positive.T4

def poolData : Nat := 0xa010000000000201a010000000000001a0000000000000018010000100000001801000000001000180100000000000018000040000000001800002010000020180000201000000018000020000000001800000010000000180000000020102018000000002010001800000000200000180000000000200018000000000010001800000000000020180000000000001018000000000000003800000000000000100100001000000010010000000010001001000000000000100000e010000020100000e010000000100000e000000000100000c010000000100000c000000020100000c000000000100000801000000010000080000000001000005010000010100000501000000010000050000000001000004010000000100000400000001010000040000000001000000010000000100000000020302010000000002030001000000000202020100000000020200010000000002010001000000000200000100000000000300030000000000030001000000000002000300000000000200010000000000010001000000000000030100000000000002030000000000000201000000000000010100000000000000030000000000000001

def poolLookup (i : Nat) : Nat := (poolData >>> (64 * i)) &&& 18446744073709551615

def vectorBlock0 : Nat := 0x23880000000ce0000000471800000000c6000000002f800000000ba000000046d800000011b2000000002c8000000119a00000000268000000118e00000000238000000000200000000031c00000000470000000001800000000c1000000000040000000d80000000035000000020d000000000310000000209800000200260000000009800000008230000008008c00000000230000000006c000000001a00000001260000000001300000000048000000000e00000000034000000000b0000000002000000000070000000001400000000040000000120c00000000830000001c00c00000010030000120000c00001c00030000020000c00000400030000000000c00000000020000000000400000008c00000000200000000005000000000120000000004400000000020000000230000000008000000000060000000000400000008c0000000000000000000

def vectorBlock1 : Nat := 0x200000000e34800000028d2000000023480000003012000000080480000018b110000006e344000001a8d10000006634400004988d10000006234400000148d10000004e34400000128d1000000c6044000002c8110000009a04400000238110000120004400000000110000000e3080000003002000000000080000003c000000000b0000000000c000000006ec00000001ab0000001262c000000014b000000004ec000000012b000000000e500000001f8c00000007a300000045d8c000000072300000045b8c00000006e300000045a8c00000006a30000004998c00000146230000004988c00000005e30000000168c00000115630000000148c00000114e30000000138c00000114a30000000128c00000001630000004838c00000020e30004800038c00000000e30000004808c00120000230000000008c0000000c6200000002c8800000009a2000

def vectorBlock2 : Nat := 0x1028000000000a0000000e0270000003409c000000b0270000002409c00000080270000001c09c00000030240000000c78c00000011e30000000078c000000e1a30000003468c000000b1a30000002468c00000081a30000001c68c00000030630000004008c000000f0230001803808c000000e0230001803408c000000d0230000003008c000600b0230000002c08c000000a0230000002408c00060080230000002008c00001870230001801c08c00000070230000001008c00070030230000400c08c01c00030230000000c08c00001c00230001c00008c01c00000230000000008c00000310210000009c08400000260210000008c08400000311a00000009c68000000261a00000008c6800000032020000180c40800000031020000000ac080000002a020000000a408000000270200001809808000000260200000068c08000060230200000008c0800

def vectorBlock3 : Nat := 0x230000260008000008c00200000038c04800000230120000188d14400006e301100001a8c04400126230110000138c04400004a30110000318004400009a00110000238004400000c08c70000000231c00003808c600000d0231800002c08c60000080231800001c08c60000310201800009808060000230201800000e30020000030230400000c0a00

def vectorBlockLookup (k : Nat) : Nat := (if k < 2 then (if k < 1 then vectorBlock0 else vectorBlock1) else (if k < 3 then vectorBlock2 else vectorBlock3))

def vectorLookup (i : Nat) : Nat :=
  (vectorBlockLookup (i / 64) >>> (42 * (i % 64))) &&& 4398046511103

def zeroData : Nat := 0x7fd3560a34244180

def zeroLookup (i : Nat) : Nat := (zeroData >>> (7 * i)) &&& 127

def codeBlock0 : Nat := 0x444321a010d0062703038171c074e038701b380d1c064e02e701438099c044e01e740e38871c038e01870cc3060182fcc16c60b530549829cc14860a0304e9826cc1326498304c182f8a168509d284b94258a12a5494284a1432c817c40b4204e9025c812c4095224a102508130204610130808c41b4009400218008c0016000500008200000000

def codeBlock1 : Nat := 0x726901348096404927239011c8202206710298812c40922e471023886c40202006700298012c00920e470023803dac1e960d2b0225810ac081603eb01e580c2c059602ab01258082d839641cb00e5806ac35d40fca07d5033a819940b0a0565029a81354096a0495023a9919408ca07c4832a412d208a90444b21a410d21ac807c4032a012d008a8

def codeBlock2 : Nat := 0x8bb04558e26c1136088b043d821ac10b6084b1c1d820ec1036380b040582e2a15d50a2a84fd427aa73b509da84854232a10b5082a840d4e02a10150c6a061d02e2815d40a2a04fd027a873b409da04850232810b4082a040d0e028101407f98194c02a6009370098004c36641b120899041c8202407920359019c80b24057202a9014c80a2404f2

def codeBlock3 : Nat := 0x533c019e00bee05b7003b8015cc02e2017000b86558326c19160c7b06358316c18960c3b060d82f6c17960bbb05d582e6c17160b7b059d82cac16360b0b057d82bac15b60acb055d82aac75360a9b05458e9ec14f60a6b052d8e92c14960a3b05158286c74160a0b04f58e76c13b609cb04d58662c1316093b04958246c121608fb04758236c1196

def codeBlock4 : Nat := 0x57d2ab6815b40aba054d2a9e814f40a5a051d0286813f409da54dd026e81334a97a04bd02568123448da046d021681074081a03fd01f680f74a79a03cd01de80eb4073a038d01be80db4a6ba035d01a694cf4067a071c836e417f209f904ccaa5e412f207f9037c81a654cf206790d0c066e01c700db805fc027e01330a97804bc01fe00df00698

def codeBlock5 : Nat := 0x500f8007c357c0f3e076f2ba781d3c0d9b06bd8346c0276a11b008d803ec01b6a01b200d8006c35341a7a0d2d068e8343419fa0ced066e830b40f1a077d03ae81cf40e5a071d038681bf40dda06dd0356819340c7a062d030e818340bfa05ed02ee817340b7a05ad02ce956340b1a

def codeBlockLookup (k : Nat) : Nat := (if k < 3 then (if k < 1 then codeBlock0 else (if k < 2 then codeBlock1 else codeBlock2)) else (if k < 4 then codeBlock3 else (if k < 5 then codeBlock4 else codeBlock5)))

def codeLookup (i : Nat) : Nat :=
  (codeBlockLookup (i / 64) >>> (17 * (i % 64))) &&& 131071

def getState (i : Nat) : State :=
  let c := codeLookup i
  let p := vectorLookup ((c >>> 5) &&& 255)
  let z := zeroLookup ((c >>> 13) &&& 15)
  (c &&& 31, (List.range 7).map (fun j => poolLookup ((p >>> (6 * j)) &&& 63)),
    (List.range (z &&& 1)).map (fun j => (z >>> (1 + 6 * j)) &&& 63))

def contains (s : State) : Bool :=
  Certificate.searchIndex stateLess getState 372 s 11 0 372

def checked (i : Nat) : Bool := safe (getState i) && (successors 4 (getState i)).all contains

def chunkCheck (k : Nat) : Bool :=
  (List.range 8).all (fun j => if k * 8 + j < 372 then checked (k * 8 + j) else true)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk0_closed : chunkCheck 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk1_closed : chunkCheck 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk2_closed : chunkCheck 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk3_closed : chunkCheck 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk4_closed : chunkCheck 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk5_closed : chunkCheck 5 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk6_closed : chunkCheck 6 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk7_closed : chunkCheck 7 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk8_closed : chunkCheck 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk9_closed : chunkCheck 9 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk10_closed : chunkCheck 10 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk11_closed : chunkCheck 11 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk12_closed : chunkCheck 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk13_closed : chunkCheck 13 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk14_closed : chunkCheck 14 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk15_closed : chunkCheck 15 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk16_closed : chunkCheck 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk17_closed : chunkCheck 17 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk18_closed : chunkCheck 18 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk19_closed : chunkCheck 19 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk20_closed : chunkCheck 20 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk21_closed : chunkCheck 21 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk22_closed : chunkCheck 22 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk23_closed : chunkCheck 23 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk24_closed : chunkCheck 24 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk25_closed : chunkCheck 25 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk26_closed : chunkCheck 26 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk27_closed : chunkCheck 27 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk28_closed : chunkCheck 28 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk29_closed : chunkCheck 29 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk30_closed : chunkCheck 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk31_closed : chunkCheck 31 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk32_closed : chunkCheck 32 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk33_closed : chunkCheck 33 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk34_closed : chunkCheck 34 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk35_closed : chunkCheck 35 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk36_closed : chunkCheck 36 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk37_closed : chunkCheck 37 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk38_closed : chunkCheck 38 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk39_closed : chunkCheck 39 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk40_closed : chunkCheck 40 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk41_closed : chunkCheck 41 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk42_closed : chunkCheck 42 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk43_closed : chunkCheck 43 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk44_closed : chunkCheck 44 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk45_closed : chunkCheck 45 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk46_closed : chunkCheck 46 = true := by decide +kernel

lemma all_chunks_checked : (List.range 47).all chunkCheck = true := by
  change ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46] : List Nat).all chunkCheck = true
  simp only [List.all_cons, List.all_nil, chunk0_closed, chunk1_closed, chunk2_closed, chunk3_closed, chunk4_closed, chunk5_closed, chunk6_closed, chunk7_closed, chunk8_closed, chunk9_closed, chunk10_closed, chunk11_closed, chunk12_closed, chunk13_closed, chunk14_closed, chunk15_closed, chunk16_closed, chunk17_closed, chunk18_closed, chunk19_closed, chunk20_closed, chunk21_closed, chunk22_closed, chunk23_closed, chunk24_closed, chunk25_closed, chunk26_closed, chunk27_closed, chunk28_closed, chunk29_closed, chunk30_closed, chunk31_closed, chunk32_closed, chunk33_closed, chunk34_closed, chunk35_closed, chunk36_closed, chunk37_closed, chunk38_closed, chunk39_closed, chunk40_closed, chunk41_closed, chunk42_closed, chunk43_closed, chunk44_closed, chunk45_closed, chunk46_closed, Bool.and_self]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma initial_contains : contains (initial 4) = true := by decide +kernel

lemma reachable_safe {finish : State}
    (hreach : Relation.ReflTransGen (fun a b => b ∈ successors 4 a) (initial 4) finish) :
    safe finish = true := by
  apply Certificate.chunked_searchIndex_reachable_safe stateLess getState
    372 8 47 11 (successors 4) safe (by decide) (by decide) ?_ initial_contains hreach
  intro k hk
  change chunkCheck k = true
  exact List.all_eq_true.mp all_chunks_checked k (List.mem_range.mpr hk)

lemma reachable_no_target {finish : State}
    (hreach : Relation.ReflTransGen (fun a b => b ∈ successors 4 a) (initial 4) finish) :
    56 ∉ finish.2.2 := by
  simpa [safe] using reachable_safe hreach

end PEqualNP.Outside.L_meta_2590_aux.S14Positive.T4

namespace PEqualNP.Outside.L_meta_2590_aux.S14Positive.T68

def poolData : Nat := 0xa010000002000001a010000000000001a0000000000000018400040000010001840000000000000182000001020000018200000100000001820000000000000180100001000000018010000000010001801000000000000180010001000100018001000100000001800100000000000180000400000000018000000100000001800000000201000180000000020000018000000001000001800000000001000180000000000000010e010400020000010c010400000000010c000400020100010c000000020000010a000401020000010a000401000000010a0004000000000108010000000000010800040100000001080004000200000108000400000000010800000000000001040004000001000104000000000000010010000100000001001000000000000100010000000000010000050100000101000005010000000100000500000000010000040100000001000004000000010100000400000000010000000100000001000000000300000100000000020100010000000002000101000000000200000100000000010101010000000001000001000000000001000100000000000001010000000000000001

def poolLookup (i : Nat) : Nat := (poolData >>> (64 * i)) &&& 18446744073709551615

def vectorBlock0 : Nat := 0xe84000000036100000000c8400000002e100000024a8400000002a10000000088400000001e100000200584000a00016100000000584000000a02100000200084000a000021000000000840000000ad2000000026480000000912000000022480000000852000000030440000000bd100000002e440000000b5100000002b440000000a91000000029440000000a11000000026440000000911000000022440000009851000000021440000000011000000024080000000002000000035000000000d00000000033000000000b0000000002b0000000009400000110240000000809000000000240000000118400000110210000000008400000000170000000005800000000150000000002c000000000a000000000180000280005000001000140000000005000000000040000000840000000840000000011000000000080000000840000000000000000000

def vectorBlock1 : Nat := 0x1685000000056140000000001000000016228000000784a00000016128000000184a00000002128000000500a00000004028000000000a0000005e124000001684900000032124000000b8490000002a124000002b4490000009912400000244490000008912400000214490000000002400000000040000001610c0000000003000000167080000017842000000161080000000842000000900080000000002000000140040000000001000000172000000005c400000005e8000000016a000000005680000000079c00000001670000000019c00000000270000000179800000005a600000000c9800000002e600000000a98000000016300000001788000000016200000000088000000082100000001f8400000007a100000001d84000000072100000001b8400000006a10000000198400000006210000000178400000005a10000000158400000003e1000

def vectorBlock2 : Nat := 0x210000058405000001610130000240004400008400110000178404000005a101000001584040000016108a0000058802800001e100a00000584028000002100a0000178402400005a100900000b8402400002a100900002b4402400009110090000224402400008510090000058400c000014084200000584a0800001670020000178400800001610020000240000800001408800000000220000001428400000000a10000001c08400020050210000001408400020000210000000008400000058540000000005000000058530000000004c000002b0110000009004400000220110000008404400000000110000005e1400

def vectorBlockLookup (k : Nat) : Nat := (if k < 1 then vectorBlock0 else (if k < 2 then vectorBlock1 else vectorBlock2))

def vectorLookup (i : Nat) : Nat :=
  (vectorBlockLookup (i / 64) >>> (42 * (i % 64))) &&& 4398046511103

def zeroData : Nat := 0x3f40e903440c102a40810186a4201050220084000

def zeroLookup (i : Nat) : Nat := (zeroData >>> (14 * i)) &&& 16383

def codeBlock0 : Nat := 0xaa80414007e002f00128008c244200210077583b2c181601eb00e5806ac0316016b00a5804ac0216e0eb1075803ac0196146a07a503ca816140aea0435021281054078a03a501b29cd5406aa078482b240e9206890324b98a40c521448078402b200e9006880324398a00c501182035100988040415c008a001880040000a0004000082c0000000

def codeBlock1 : Nat := 0x38a98454c20660c730619826cc0ce66633031980f4c072600730029c804cc02600130ab90554826241292093904948242411d208d91c648232410b20849041c820a40c920629027480e2406f2335901ac809e40452021900fc80764037201a900cc8062402f2016900ac8052522723139009c80465221201090414407e202f10128808c644220211

def codeBlock2 : Nat := 0x435d19ae80d74061a02fd017680b74059a02bd015680a74051a627d013e809b404ba024d011e988b4045a621d010e987f403fa070c835e4147207b903bcb1d640eb20599023c8106587f203f909ec04d601c300d78051c01ee00ef0c75803ac0166008f0041861fc00fe0072e0057300b8005c262c1256090b04758236c719608cb048cc23e61173

def codeBlock3 : Nat := 0x74d039e81cb40e3a070d037e81bb40dba06cd035e81a340cda065d3b26819340bda05dd02e6816f40b5a059d1ac6816340aba054d029e814b40a3a050d027e9d3b409da04cd025e812b4093a048d023e811b408ba044d421e990f4687a043d4216990b4085a841d020e8103407fa03ed01ee98f34079a63ad01d680e74e71a038d51ae9cd74a6ba

def codeBlock4 : Nat := 0x88d8436c1f766ebb075d8356c1a760cfb761d8b0ec18766bfb05fdd006e0036e01b600da806d0036601b200d8806c003615ba0acd054e82a3414fa0a6d052e82934747a0a3d050e8283413fa09ed04ee82734137a09ad04ce825f412da095d3ca682534113a087d040681ff40fda07cd03de8deb40f5a

def codeBlockLookup (k : Nat) : Nat := (if k < 2 then (if k < 1 then codeBlock0 else codeBlock1) else (if k < 3 then codeBlock2 else (if k < 4 then codeBlock3 else codeBlock4)))

def codeLookup (i : Nat) : Nat :=
  (codeBlockLookup (i / 64) >>> (17 * (i % 64))) &&& 131071

def getState (i : Nat) : State :=
  let c := codeLookup i
  let p := vectorLookup ((c >>> 5) &&& 255)
  let z := zeroLookup ((c >>> 13) &&& 15)
  (c &&& 31, (List.range 7).map (fun j => poolLookup ((p >>> (6 * j)) &&& 63)),
    (List.range (z &&& 3)).map (fun j => (z >>> (2 + 6 * j)) &&& 63))

def contains (s : State) : Bool :=
  Certificate.searchIndex stateLess getState 312 s 11 0 312

def checked (i : Nat) : Bool := safe (getState i) && (successors 68 (getState i)).all contains

def chunkCheck (k : Nat) : Bool :=
  (List.range 8).all (fun j => if k * 8 + j < 312 then checked (k * 8 + j) else true)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk0_closed : chunkCheck 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk1_closed : chunkCheck 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk2_closed : chunkCheck 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk3_closed : chunkCheck 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk4_closed : chunkCheck 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk5_closed : chunkCheck 5 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk6_closed : chunkCheck 6 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk7_closed : chunkCheck 7 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk8_closed : chunkCheck 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk9_closed : chunkCheck 9 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk10_closed : chunkCheck 10 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk11_closed : chunkCheck 11 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk12_closed : chunkCheck 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk13_closed : chunkCheck 13 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk14_closed : chunkCheck 14 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk15_closed : chunkCheck 15 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk16_closed : chunkCheck 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk17_closed : chunkCheck 17 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk18_closed : chunkCheck 18 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk19_closed : chunkCheck 19 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk20_closed : chunkCheck 20 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk21_closed : chunkCheck 21 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk22_closed : chunkCheck 22 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk23_closed : chunkCheck 23 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk24_closed : chunkCheck 24 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk25_closed : chunkCheck 25 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk26_closed : chunkCheck 26 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk27_closed : chunkCheck 27 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk28_closed : chunkCheck 28 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk29_closed : chunkCheck 29 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk30_closed : chunkCheck 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk31_closed : chunkCheck 31 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk32_closed : chunkCheck 32 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk33_closed : chunkCheck 33 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk34_closed : chunkCheck 34 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk35_closed : chunkCheck 35 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk36_closed : chunkCheck 36 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk37_closed : chunkCheck 37 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk38_closed : chunkCheck 38 = true := by decide +kernel

lemma all_chunks_checked : (List.range 39).all chunkCheck = true := by
  change ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38] : List Nat).all chunkCheck = true
  simp only [List.all_cons, List.all_nil, chunk0_closed, chunk1_closed, chunk2_closed, chunk3_closed, chunk4_closed, chunk5_closed, chunk6_closed, chunk7_closed, chunk8_closed, chunk9_closed, chunk10_closed, chunk11_closed, chunk12_closed, chunk13_closed, chunk14_closed, chunk15_closed, chunk16_closed, chunk17_closed, chunk18_closed, chunk19_closed, chunk20_closed, chunk21_closed, chunk22_closed, chunk23_closed, chunk24_closed, chunk25_closed, chunk26_closed, chunk27_closed, chunk28_closed, chunk29_closed, chunk30_closed, chunk31_closed, chunk32_closed, chunk33_closed, chunk34_closed, chunk35_closed, chunk36_closed, chunk37_closed, chunk38_closed, Bool.and_self]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma initial_contains : contains (initial 68) = true := by decide +kernel

lemma reachable_safe {finish : State}
    (hreach : Relation.ReflTransGen (fun a b => b ∈ successors 68 a) (initial 68) finish) :
    safe finish = true := by
  apply Certificate.chunked_searchIndex_reachable_safe stateLess getState
    312 8 39 11 (successors 68) safe (by decide) (by decide) ?_ initial_contains hreach
  intro k hk
  change chunkCheck k = true
  exact List.all_eq_true.mp all_chunks_checked k (List.mem_range.mpr hk)

lemma reachable_no_target {finish : State}
    (hreach : Relation.ReflTransGen (fun a b => b ∈ successors 68 a) (initial 68) finish) :
    56 ∉ finish.2.2 := by
  simpa [safe] using reachable_safe hreach

end PEqualNP.Outside.L_meta_2590_aux.S14Positive.T68
