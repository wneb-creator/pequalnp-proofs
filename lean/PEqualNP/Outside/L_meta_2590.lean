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

def H2.branchW (n : ℕ) (D : Dag) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => 2 ≤ fanout D w)

def H2.eligSet (n : ℕ) (D : Dag) : Finset (Fin n) := (branchW n D).biUnion (supp n D)

def H2.ineligSet (n : ℕ) (D : Dag) : Finset (Fin n) := Finset.univ \ eligSet n D

def H2.arcs (D : Dag) : Finset (ℕ × Bool) := Finset.range D.length ×ˢ Finset.univ

def H2.src (D : Dag) (e : ℕ × Bool) : ℕ := if e.2 = true then opB D e.1 else opA D e.1

def H2.exitArcs (n : ℕ) (D : Dag) (K : Finset ℕ) : Finset (ℕ × Bool) :=
  (arcs D).filter (fun e => src D e ∈ K ∧ n + e.1 ∉ K)

def H2.merges (n : ℕ) (D : Dag) (K : Finset ℕ) : Finset ℕ :=
  (Finset.range D.length).filter (fun j => n + j ∈ K ∧ opA D j ∈ K ∧ opB D j ∈ K)

def H2.sources (n : ℕ) (K : Finset ℕ) : Finset ℕ := K.filter (fun w => w < n)

def H2.carrierT (n : ℕ) (D : Dag) (T : Finset (Fin n)) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => (supp n D w ∩ T).Nonempty)

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

lemma H2.sb_card_arcs_filter (P : ℕ × Bool → Prop) [DecidablePred P] :
    ((arcs D).filter P).card = ∑ j ∈ Finset.range D.length,
      ((if P (j, false) then 1 else 0) + (if P (j, true) then 1 else 0)) := by
  rw [Finset.card_filter, arcs, Finset.sum_product]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Fintype.sum_bool, add_comm]

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

end SurplusFlow

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

end packScope1
section packScope2

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

section packScope3

-- Circuit normalization and wire counting, adapted from L_meta_971.
section packScope4

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def C6.DagTools.gop : Bool → Bool → Bool → Bool
  | true, a, b => a && b
  | false, a, b => a || b

open PEqualNP.Outside.L_meta_2590_aux.C6.DagTools

@[local simp] lemma C6.DagTools.gop_true (a b : Bool) : gop true a b = (a && b) := rfl

@[local simp] lemma C6.DagTools.gop_false (a b : Bool) : gop false a b = (a || b) := rfl

abbrev C6.DagTools.Dag := List (Bool × ℕ × ℕ)

def C6.DagTools.tag (D : Dag) (j : ℕ) : Bool := (D.getD j (false, 0, 0)).1

def C6.DagTools.opA (D : Dag) (j : ℕ) : ℕ := (D.getD j (false, 0, 0)).2.1

def C6.DagTools.opB (D : Dag) (j : ℕ) : ℕ := (D.getD j (false, 0, 0)).2.2

def C6.DagTools.wstep (w : List Bool) (g : Bool × ℕ × ℕ) : List Bool :=
  w ++ [gop g.1 (w.getD g.2.1 false) (w.getD g.2.2 false)]

def C6.DagTools.wl (D : Dag) (w : List Bool) : List Bool := D.foldl wstep w

def C6.DagTools.val (D : Dag) {n : ℕ} (x : Fin n → Bool) (w : ℕ) : Bool :=
  (wl D (List.ofFn x)).getD w false

def C6.DagTools.Strict (n : ℕ) (D : Dag) : Prop :=
  ∀ j, j < D.length → opA D j < n + j ∧ opB D j < n + j ∧ opA D j ≠ opB D j

def C6.DagTools.readers (D : Dag) (w : ℕ) : Finset ℕ :=
  (Finset.range D.length).filter (fun j => opA D j = w ∨ opB D j = w)

def C6.DagTools.fanout (D : Dag) (w : ℕ) : ℕ := (readers D w).card

def C6.DagTools.Live (n : ℕ) (D : Dag) : Prop := ∀ w, w + 1 < n + D.length → 1 ≤ fanout D w

def C6.DagTools.StrictLive (n : ℕ) (D : Dag) : Prop := Strict n D ∧ Live n D ∧ D ≠ []

def C6.DagTools.outW (n : ℕ) (D : Dag) : ℕ := n + D.length - 1

def C6.DagTools.single {n : ℕ} (v : Fin n) : Fin n → Bool := fun i => decide (i = v)

def C6.DagTools.supp (n : ℕ) (D : Dag) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => val D (single v) w = true)

def C6.DagTools.surplusOn (D : Dag) (K : Finset ℕ) : ℕ := ∑ w ∈ K, (fanout D w - 1)

def C6.DagTools.inner (n : ℕ) (D : Dag) : Finset ℕ := Finset.range (n + D.length - 1)

def C6.DagTools.totalSurplus (n : ℕ) (D : Dag) : ℕ := surplusOn D (inner n D)

def C6.DagTools.Bplus (n : ℕ) (D : Dag) : ℕ :=
  surplusOn D ((inner n D).filter (fun w => (supp n D w).Nonempty))

def C6.DagTools.Bzero (n : ℕ) (D : Dag) : ℕ :=
  surplusOn D ((inner n D).filter (fun w => ¬ (supp n D w).Nonempty))

def C6.DagTools.branchW (n : ℕ) (D : Dag) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => 2 ≤ fanout D w)

def C6.DagTools.eligSet (n : ℕ) (D : Dag) : Finset (Fin n) := (branchW n D).biUnion (supp n D)

def C6.DagTools.ineligSet (n : ℕ) (D : Dag) : Finset (Fin n) := Finset.univ \ eligSet n D

def C6.DagTools.units (n : ℕ) (D : Dag) : Finset (Σ _ : ℕ, ℕ) :=
  (inner n D).sigma (fun w => Finset.range (fanout D w - 1))

def C6.DagTools.unitsPlus (n : ℕ) (D : Dag) : Finset (Σ _ : ℕ, ℕ) :=
  (units n D).filter (fun u => (supp n D u.1).Nonempty)

def C6.DagTools.arcs (D : Dag) : Finset (ℕ × Bool) := Finset.range D.length ×ˢ Finset.univ

def C6.DagTools.src (D : Dag) (e : ℕ × Bool) : ℕ := if e.2 = true then opB D e.1 else opA D e.1

def C6.DagTools.exitArcs (n : ℕ) (D : Dag) (K : Finset ℕ) : Finset (ℕ × Bool) :=
  (arcs D).filter (fun e => src D e ∈ K ∧ n + e.1 ∉ K)

def C6.DagTools.merges (n : ℕ) (D : Dag) (K : Finset ℕ) : Finset ℕ :=
  (Finset.range D.length).filter (fun j => n + j ∈ K ∧ opA D j ∈ K ∧ opB D j ∈ K)

def C6.DagTools.sources (n : ℕ) (K : Finset ℕ) : Finset ℕ := K.filter (fun w => w < n)

def C6.DagTools.carrierT (n : ℕ) (D : Dag) (T : Finset (Fin n)) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => (supp n D w ∩ T).Nonempty)

def C6.DagTools.PureBranch (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Prop :=
  ∀ v ∈ eligSet n D, 2 ≤ fanout D (b v) ∧ supp n D (b v) = {v}

def C6.DagTools.reservedUnits (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (eligSet n D).image (fun v => (⟨b v, 0⟩ : Σ _ : ℕ, ℕ))

def C6.DagTools.residualUnits (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  unitsPlus n D \ reservedUnits n D b

lemma C6.DagTools.tag_eq (D : Dag) (j : ℕ) (h : j < D.length) : tag D j = (D[j]).1 := by
  simp [tag, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

lemma C6.DagTools.opA_eq (D : Dag) (j : ℕ) (h : j < D.length) : opA D j = (D[j]).2.1 := by
  simp [opA, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

lemma C6.DagTools.opB_eq (D : Dag) (j : ℕ) (h : j < D.length) : opB D j = (D[j]).2.2 := by
  simp [opB, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

lemma C6.DagTools.wl_cons (g : Bool × ℕ × ℕ) (D : Dag) (w : List Bool) :
    wl (g :: D) w = wl D (wstep w g) := rfl

lemma C6.DagTools.wl_append (D E : Dag) (w : List Bool) : wl (D ++ E) w = wl E (wl D w) := by
  simp [wl, List.foldl_append]

lemma C6.DagTools.wstep_length (w : List Bool) (g : Bool × ℕ × ℕ) : (wstep w g).length = w.length + 1 := by
  simp [wstep]

lemma C6.DagTools.wl_length (D : Dag) : ∀ w : List Bool, (wl D w).length = w.length + D.length := by
  induction D with
  | nil => intro w; simp [wl]
  | cons g D ih => intro w; rw [wl_cons, ih, wstep_length]; simp; omega

lemma C6.DagTools.wstep_getD_lt (w : List Bool) (g : Bool × ℕ × ℕ) (i : ℕ) (h : i < w.length) :
    (wstep w g).getD i false = w.getD i false := by
  simp [wstep, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma C6.DagTools.wl_getD_lt (D : Dag) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wl D w).getD i false = w.getD i false := by
  induction D with
  | nil => intro w i _; rfl
  | cons g D ih =>
    intro w i h
    rw [wl_cons, ih _ _ (by rw [wstep_length]; omega), wstep_getD_lt _ _ _ h]

lemma C6.DagTools.getD_ge (w : List Bool) (i : ℕ) (h : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

lemma C6.DagTools.wstep_getD_last (w : List Bool) (g : Bool × ℕ × ℕ) :
    (wstep w g).getD w.length false = gop g.1 (w.getD g.2.1 false) (w.getD g.2.2 false) := by
  simp [wstep, List.getD_eq_getElem?_getD]

lemma C6.DagTools.wl_getD_gate (D : Dag) (w : List Bool) (j : ℕ) (hj : j < D.length) :
    (wl D w).getD (w.length + j) false =
      gop (tag D j) ((wl (D.take j) w).getD (opA D j) false)
        ((wl (D.take j) w).getD (opB D j) false) := by
  have hsplit : D = D.take j ++ D[j] :: D.drop (j + 1) := by simp
  have hlen : (wl (D.take j) w).length = w.length + j := by
    rw [wl_length, List.length_take]; omega
  rw [tag_eq D j hj, opA_eq D j hj, opB_eq D j hj]
  conv_lhs => rw [hsplit, wl_append, wl_cons]
  rw [wl_getD_lt _ _ _ (by rw [wstep_length, hlen]; omega), ← hlen, wstep_getD_last]

lemma C6.DagTools.wl_take_getD (D : Dag) (w : List Bool) (j i : ℕ) (hi : i < w.length + j)
    (hj : j ≤ D.length) :
    (wl (D.take j) w).getD i false = (wl D w).getD i false := by
  have hsplit : D = D.take j ++ D.drop j := by simp
  have hlen : (wl (D.take j) w).length = w.length + j := by
    rw [wl_length, List.length_take]; omega
  conv_rhs => rw [hsplit, wl_append]
  rw [wl_getD_lt (D.drop j) (wl (D.take j) w) i (by rw [hlen]; exact hi)]

lemma C6.DagTools.val_input (D : Dag) {n : ℕ} (x : Fin n → Bool) (i : ℕ) (h : i < n) :
    val D x i = x ⟨i, h⟩ := by
  unfold val
  rw [wl_getD_lt _ _ _ (by simpa using h)]
  simp [List.getD_eq_getElem?_getD, h]

lemma C6.DagTools.val_ge (D : Dag) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (h : n + D.length ≤ w) :
    val D x w = false := by
  unfold val
  exact getD_ge _ _ (by rw [wl_length]; simpa using h)

lemma C6.DagTools.val_gate {n : ℕ} {D : Dag} (hS : Strict n D) (x : Fin n → Bool) (j : ℕ)
    (hj : j < D.length) :
    val D x (n + j) = gop (tag D j) (val D x (opA D j)) (val D x (opB D j)) := by
  obtain ⟨ha, hb, -⟩ := hS j hj
  have h := wl_getD_gate D (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  unfold val
  rw [h, wl_take_getD D _ j _ (by simpa using ha) hj.le,
    wl_take_getD D _ j _ (by simpa using hb) hj.le]

lemma C6.DagTools.val_unique {n : ℕ} {D : Dag} (hS : Strict n D) (x : Fin n → Bool) (f : ℕ → Bool)
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

section SurplusFlow

variable {n : ℕ} {D : Dag}

lemma C6.DagTools.sb_mem_inner {w : ℕ} : w ∈ inner n D ↔ w + 1 < n + D.length := by
  unfold inner; rw [Finset.mem_range]; omega

lemma C6.DagTools.sb_src_false (j : ℕ) : src D (j, false) = opA D j := by simp [src]

lemma C6.DagTools.sb_src_true (j : ℕ) : src D (j, true) = opB D j := by simp [src]

lemma C6.DagTools.fanout_eq_zero_of_ge (hS : Strict n D) (w : ℕ) (h : n + D.length ≤ w + 1) :
    fanout D w = 0 := by
  unfold fanout readers
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro j hj
  have hj2 := Finset.mem_range.mp hj
  have := hS j hj2
  omega

lemma C6.DagTools.lt_of_fanout_pos (hS : Strict n D) {w : ℕ} (h : 1 ≤ fanout D w) :
    w + 1 < n + D.length := by
  by_contra hc
  have := fanout_eq_zero_of_ge hS w (by omega)
  omega

lemma C6.DagTools.sb_card_arcs_filter (P : ℕ × Bool → Prop) [DecidablePred P] :
    ((arcs D).filter P).card = ∑ j ∈ Finset.range D.length,
      ((if P (j, false) then 1 else 0) + (if P (j, true) then 1 else 0)) := by
  rw [Finset.card_filter, arcs, Finset.sum_product]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Fintype.sum_bool, add_comm]

lemma C6.DagTools.sb_card_arcs : (arcs D).card = 2 * D.length := by
  simp [arcs, Finset.card_product, Nat.mul_comm]

lemma C6.DagTools.sb_src_lt (hS : Strict n D) (e : ℕ × Bool) (he : e ∈ arcs D) :
    src D e + 1 < n + D.length := by
  obtain ⟨j, c⟩ := e
  have hj : j < D.length := by simpa [arcs] using he
  have := hS j hj
  cases c
  · rw [sb_src_false]; omega
  · rw [sb_src_true]; omega

lemma C6.DagTools.sb_fanout_arcs (hS : Strict n D) (w : ℕ) :
    fanout D w = ((arcs D).filter (fun e => src D e = w)).card := by
  rw [sb_card_arcs_filter, fanout, readers, Finset.card_filter]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have := (hS j (Finset.mem_range.mp hj)).2.2
  rw [sb_src_false, sb_src_true]
  split_ifs <;> omega

lemma C6.DagTools.sb_sum_fanout_eq (hS : Strict n D) (K : Finset ℕ) :
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

lemma C6.DagTools.sb_surplus_add_card {K : Finset ℕ} (hL : ∀ w ∈ K, 1 ≤ fanout D w) :
    surplusOn D K + K.card = ∑ w ∈ K, fanout D w := by
  rw [surplusOn, Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun w hw => Nat.sub_add_cancel (hL w hw))

lemma C6.DagTools.surplus_identity (h : StrictLive n D) : totalSurplus n D + n = D.length + 1 := by
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

lemma C6.DagTools.totalSurplus_split (n : ℕ) (D : Dag) : totalSurplus n D = Bplus n D + Bzero n D := by
  unfold totalSurplus Bplus Bzero surplusOn
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

lemma C6.DagTools.mem_supp {v : Fin n} {w : ℕ} : v ∈ supp n D w ↔ val D (single v) w = true := by
  simp [supp]

lemma C6.DagTools.val_mono (hS : Strict n D) (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true)
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

lemma C6.DagTools.supp_input (D : Dag) (i : Fin n) : supp n D i.val = {i} := by
  ext v
  rw [mem_supp, val_input D (single v) i.val i.isLt]
  simp [single, eq_comm]

lemma C6.DagTools.supp_ge (D : Dag) (w : ℕ) (h : n + D.length ≤ w) : supp n D w = ∅ := by
  ext v
  simp [mem_supp, val_ge D (single v) w h]

lemma C6.DagTools.supp_gate (hS : Strict n D) (j : ℕ) (hj : j < D.length) :
    supp n D (n + j) = if tag D j = true then supp n D (opA D j) ∩ supp n D (opB D j)
      else supp n D (opA D j) ∪ supp n D (opB D j) := by
  ext v
  rw [mem_supp, val_gate hS _ j hj]
  cases tag D j <;> simp [mem_supp]

lemma C6.DagTools.carrier_flow (h : StrictLive n D) (K : Finset ℕ) (hK : K ⊆ inner n D)
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

lemma C6.DagTools.sb_carrierT_sub (T : Finset (Fin n))
    (hout : supp n D (outW n D) ∩ T = ∅) : carrierT n D T ⊆ inner n D := by
  intro w hw
  simp only [carrierT, Finset.mem_filter, Finset.mem_range] at hw
  rw [sb_mem_inner]
  by_contra hc
  have hw2 : w = outW n D := by unfold outW; omega
  rw [hw2, hout] at hw
  exact Finset.not_nonempty_empty hw.2

lemma C6.DagTools.sb_sources_carrierT (D : Dag) (T : Finset (Fin n)) :
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

lemma C6.DagTools.carrier_flow_union (h : StrictLive n D) (T : Finset (Fin n))
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

lemma C6.DagTools.mem_units {u : Σ _ : ℕ, ℕ} :
    u ∈ units n D ↔ u.1 ∈ inner n D ∧ u.2 + 1 < fanout D u.1 := by
  rw [units, Finset.mem_sigma, Finset.mem_range]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩

lemma C6.DagTools.sb_card_units_filter (n : ℕ) (D : Dag) (p : ℕ → Prop) [DecidablePred p] :
    ((units n D).filter (fun u => p u.1)).card = surplusOn D ((inner n D).filter p) := by
  have hs : (units n D).filter (fun u => p u.1) =
      ((inner n D).filter p).sigma (fun w => Finset.range (fanout D w - 1)) := by
    ext u; simp only [units, Finset.mem_filter, Finset.mem_sigma]; tauto
  rw [hs, Finset.card_sigma, surplusOn]
  simp

lemma C6.DagTools.card_unitsPlus (n : ℕ) (D : Dag) : (unitsPlus n D).card = Bplus n D := by
  unfold unitsPlus Bplus
  exact sb_card_units_filter n D (fun w => (supp n D w).Nonempty)

lemma C6.DagTools.mem_eligSet {v : Fin n} :
    v ∈ eligSet n D ↔ ∃ w, 2 ≤ fanout D w ∧ v ∈ supp n D w := by
  simp only [eligSet, branchW, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨w, ⟨-, h2⟩, hv⟩; exact ⟨w, h2, hv⟩
  · rintro ⟨w, h2, hv⟩
    refine ⟨w, ⟨?_, h2⟩, hv⟩
    by_contra hc
    rw [supp_ge D w (by omega)] at hv
    exact Finset.notMem_empty v hv

lemma C6.DagTools.mem_ineligSet {v : Fin n} :
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

lemma C6.DagTools.sb_singleton_inter_nonempty {v : Fin n} {T : Finset (Fin n)} :
    (({v} : Finset (Fin n)) ∩ T).Nonempty ↔ v ∈ T := by
  constructor
  · rintro ⟨u, hu⟩
    rw [Finset.mem_inter, Finset.mem_singleton] at hu
    exact hu.1 ▸ hu.2
  · intro h
    exact ⟨v, Finset.mem_inter.mpr ⟨Finset.mem_singleton_self v, h⟩⟩

lemma C6.DagTools.sb_reserved_inj (b : Fin n → ℕ) (hb : PureBranch n D b) :
    Set.InjOn (fun v => (⟨b v, 0⟩ : Σ _ : ℕ, ℕ)) (eligSet n D : Set (Fin n)) := by
  intro v hv v2 hv2 he
  have hbv : b v = b v2 := congrArg Sigma.fst he
  have h1 := (hb v hv).2
  rw [hbv, (hb v2 hv2).2] at h1
  exact (Finset.singleton_injective h1).symm

lemma C6.DagTools.reserved_subset (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b) :
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

lemma C6.DagTools.card_reserved (b : Fin n → ℕ) (hb : PureBranch n D b) :
    (reservedUnits n D b).card = (eligSet n D).card :=
  Finset.card_image_of_injOn (sb_reserved_inj b hb)

lemma C6.DagTools.elig_le_Bplus (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b) :
    (eligSet n D).card ≤ Bplus n D := by
  rw [← card_reserved b hb, ← card_unitsPlus]
  exact Finset.card_le_card (reserved_subset hS b hb)

lemma C6.DagTools.card_residual (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b) :
    (residualUnits n D b).card + (eligSet n D).card = Bplus n D := by
  rw [← card_reserved b hb, ← card_unitsPlus]
  exact Finset.card_sdiff_add_card_eq_card (reserved_subset hS b hb)

lemma C6.DagTools.surplus_carrierT_eq (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b)
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

def C6.DagTools.liftP {n : ℕ} (σ : Equiv.Perm (Fin n)) (w : ℕ) : ℕ :=
  if h : w < n then (σ ⟨w, h⟩).val else w

def C6.DagTools.relabel {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) : Dag :=
  D.map (fun g => (g.1, liftP σ g.2.1, liftP σ g.2.2))

lemma C6.DagTools.tr_liftP_lt {n : ℕ} (σ : Equiv.Perm (Fin n)) {w : ℕ} (h : w < n) :
    liftP σ w = (σ ⟨w, h⟩).val := by
  simp [liftP, h]

lemma C6.DagTools.tr_liftP_ge {n : ℕ} (σ : Equiv.Perm (Fin n)) {w : ℕ} (h : n ≤ w) : liftP σ w = w := by
  simp [liftP, Nat.not_lt.mpr h]

lemma C6.DagTools.tr_liftP_lt_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) {m : ℕ} (hm : n ≤ m) (w : ℕ) :
    liftP σ w < m ↔ w < m := by
  by_cases h : w < n
  · rw [tr_liftP_lt σ h]
    have := (σ ⟨w, h⟩).isLt
    constructor <;> intro <;> omega
  · rw [tr_liftP_ge σ (Nat.not_lt.mp h)]

lemma C6.DagTools.liftP_inv {n : ℕ} (σ : Equiv.Perm (Fin n)) (w : ℕ) : liftP σ⁻¹ (liftP σ w) = w := by
  by_cases h : w < n
  · rw [tr_liftP_lt σ h, tr_liftP_lt σ⁻¹ (σ ⟨w, h⟩).isLt]; simp
  · rw [tr_liftP_ge σ (Nat.not_lt.mp h), tr_liftP_ge σ⁻¹ (Nat.not_lt.mp h)]

lemma C6.DagTools.tr_liftP_inv' {n : ℕ} (σ : Equiv.Perm (Fin n)) (w : ℕ) : liftP σ (liftP σ⁻¹ w) = w := by
  simpa using liftP_inv σ⁻¹ w

lemma C6.DagTools.tr_liftP_inj {n : ℕ} (σ : Equiv.Perm (Fin n)) {a b : ℕ} :
    liftP σ a = liftP σ b ↔ a = b := by
  refine ⟨fun h => ?_, congrArg _⟩
  have := congrArg (liftP σ⁻¹) h
  rwa [liftP_inv, liftP_inv] at this

lemma C6.DagTools.relabel_length {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) :
    (relabel σ D).length = D.length := by
  simp [relabel]

lemma C6.DagTools.tr_tag {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (j : ℕ) (hj : j < D.length) :
    tag (relabel σ D) j = tag D j := by
  rw [tag_eq _ j (by rw [relabel_length]; exact hj), tag_eq D j hj]; simp [relabel]

lemma C6.DagTools.tr_opA {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (j : ℕ) (hj : j < D.length) :
    opA (relabel σ D) j = liftP σ (opA D j) := by
  rw [opA_eq _ j (by rw [relabel_length]; exact hj), opA_eq D j hj]; simp [relabel]

lemma C6.DagTools.tr_opB {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (j : ℕ) (hj : j < D.length) :
    opB (relabel σ D) j = liftP σ (opB D j) := by
  rw [opB_eq _ j (by rw [relabel_length]; exact hj), opB_eq D j hj]; simp [relabel]

lemma C6.DagTools.relabel_strict {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) :
    Strict n (relabel σ D) := by
  intro j hj
  rw [relabel_length] at hj
  obtain ⟨ha, hb, hab⟩ := hS j hj
  rw [tr_opA σ D j hj, tr_opB σ D j hj]
  exact ⟨(tr_liftP_lt_iff σ (Nat.le_add_right n j) _).mpr ha,
    (tr_liftP_lt_iff σ (Nat.le_add_right n j) _).mpr hb, fun h => hab ((tr_liftP_inj σ).mp h)⟩

lemma C6.DagTools.relabel_val {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D)
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

lemma C6.DagTools.relabel_fanout {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (w : ℕ) :
    fanout (relabel σ D) (liftP σ w) = fanout D w := by
  unfold fanout readers
  rw [relabel_length]
  congr 1
  apply Finset.filter_congr
  intro j hj
  have hj' := Finset.mem_range.mp hj
  rw [tr_opA σ D j hj', tr_opB σ D j hj', tr_liftP_inj, tr_liftP_inj]

lemma C6.DagTools.relabel_live {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hL : Live n D) :
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

lemma C6.DagTools.relabel_strictLive {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (h : StrictLive n D) :
    StrictLive n (relabel σ D) :=
  ⟨relabel_strict σ h.1, relabel_live σ h.2.1, by simpa [relabel] using h.2.2⟩

lemma C6.DagTools.relabel_out {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) (hne : D ≠ [])
    (x : Fin n → Bool) :
    val (relabel σ D) x (outW n (relabel σ D)) = val D (fun i => x (σ i)) (outW n D) := by
  have hpos := List.length_pos_iff.mpr hne
  have e : outW n (relabel σ D) = liftP σ (outW n D) := by
    rw [tr_liftP_ge σ (by unfold outW; omega)]; simp [outW, relabel_length]
  rw [e, relabel_val σ hS]

lemma C6.DagTools.tr_single_comp {n : ℕ} (σ : Equiv.Perm (Fin n)) (v : Fin n) :
    (fun i => single v (σ i)) = single (σ⁻¹ v) := by
  funext i
  simp only [single, decide_eq_decide]
  constructor
  · intro h; rw [← h]; simp
  · intro h; rw [h]; simp

lemma C6.DagTools.relabel_supp {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) (w : ℕ) :
    supp n (relabel σ D) (liftP σ w) = (supp n D w).image σ := by
  ext v
  simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  rw [relabel_val σ hS, tr_single_comp]
  constructor
  · intro h; exact ⟨σ⁻¹ v, h, by simp⟩
  · rintro ⟨a, ha, rfl⟩; simpa using ha

lemma C6.DagTools.inelig_card_add (n : ℕ) (D : Dag) : (ineligSet n D).card + (eligSet n D).card = n := by
  have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (eligSet n D))
  rw [Finset.card_univ, Fintype.card_fin] at h
  exact h

def C6.DagTools.sem_Edge {n : ℕ} (G : Fin n → Fin n → Prop) (x : Fin n → Bool) : Prop :=
  ∃ u v : Fin n, G u v ∧ x u = true ∧ x v = true

def C6.DagTools.sem_Comp (n : ℕ) (G : Fin n → Fin n → Prop) (D : Dag) : Prop :=
  ∀ x : Fin n → Bool, val D x (outW n D) = true ↔ sem_Edge G x

def C6.DagTools.sem_Gr {n : ℕ} (G : Fin n → Fin n → Prop) : Prop :=
  (∀ u v, G u v → G v u) ∧ (∀ u, ¬ G u u) ∧ (∀ v w, v ≠ w → ∃ z, G v z ∧ ¬ G w z) ∧
    (∀ u v, ∃ a, G u a ∧ a ≠ v)

def C6.DagTools.sem_step (n : ℕ) (D : Dag) (a b : ℕ) : Prop :=
  b < n + D.length ∧ n ≤ b ∧ (opA D (b - n) = a ∨ opB D (b - n) = a)

def C6.DagTools.sem_two {n : ℕ} (u z : Fin n) : Fin n → Bool := fun i => decide (i = u) || decide (i = z)

def C6.DagTools.sem_ins {n : ℕ} (v : Fin n) (x : Fin n → Bool) : Fin n → Bool := fun i => decide (i = v) || x i

lemma C6.DagTools.sem_rtg_mono {α : Type} {r p : α → α → Prop} (h : ∀ a b, r a b → p a b) {a b : α}
    (hab : Relation.ReflTransGen r a b) : Relation.ReflTransGen p a b := by
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.tail ih (h _ _ hbc)

section SemCore

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

lemma C6.DagTools.sem_ins_agree (v : Fin n) (x : Fin n → Bool) : ∀ k, k ≠ v → x k = sem_ins v x k := by
  intro k hk; simp [sem_ins, hk]

lemma C6.DagTools.sem_ins_self (v : Fin n) (x : Fin n → Bool) : sem_ins v x v = true := by simp [sem_ins]

lemma C6.DagTools.sem_single_le {x : Fin n → Bool} {u : Fin n} (hu : x u = true) :
    ∀ i, single u i = true → x i = true := by
  intro i hi
  simp only [single, decide_eq_true_eq] at hi
  rw [hi]; exact hu

lemma C6.DagTools.sem_val_of_supp (hS : Strict n D) {u : Fin n} {w : ℕ} (hu : u ∈ supp n D w)
    {x : Fin n → Bool} (hx : x u = true) : val D x w = true :=
  val_mono hS (single u) x (sem_single_le hx) w (mem_supp.mp hu)

lemma C6.DagTools.sem_supp_lt {v : Fin n} {w : ℕ} (hv : v ∈ supp n D w) : w < n + D.length := by
  by_contra hc
  rw [supp_ge D w (by omega)] at hv
  exact Finset.notMem_empty v hv

lemma C6.DagTools.sem_supp_and (hS : Strict n D) {j : ℕ} (hj : j < D.length) (ht : tag D j = true) :
    supp n D (n + j) = supp n D (opA D j) ∩ supp n D (opB D j) := by
  rw [supp_gate hS j hj]; simp [ht]

lemma C6.DagTools.sem_supp_or (hS : Strict n D) {j : ℕ} (hj : j < D.length) (ht : tag D j = false) :
    supp n D (n + j) = supp n D (opA D j) ∪ supp n D (opB D j) := by
  rw [supp_gate hS j hj]; simp [ht]

lemma C6.DagTools.sem_supp_and_sub (hS : Strict n D) {j : ℕ} (hj : j < D.length) (ht : tag D j = true)
    (s : Bool) : supp n D (n + j) ⊆ supp n D (src D (j, s)) := by
  rw [sem_supp_and hS hj ht]
  cases s
  · rw [sb_src_false]; exact Finset.inter_subset_left
  · rw [sb_src_true]; exact Finset.inter_subset_right

lemma C6.DagTools.sem_src_lt (hS : Strict n D) {j : ℕ} (hj : j < D.length) (s : Bool) :
    src D (j, s) < n + j := by
  obtain ⟨ha, hb, -⟩ := hS j hj
  cases s
  · rw [sb_src_false]; exact ha
  · rw [sb_src_true]; exact hb

lemma C6.DagTools.sem_step_src {j : ℕ} (hj : j < D.length) (s : Bool) :
    sem_step n D (src D (j, s)) (n + j) := by
  refine ⟨by omega, by omega, ?_⟩
  rw [Nat.add_sub_cancel_left]
  cases s
  · exact Or.inl (sb_src_false j).symm
  · exact Or.inr (sb_src_true j).symm

lemma C6.DagTools.sem_step_reader {a c : ℕ} (h : sem_step n D a c) : c - n ∈ readers D a := by
  unfold readers
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨by have := h.1; have := h.2.1; omega, h.2.2⟩

lemma C6.DagTools.sem_step_fanout {a c : ℕ} (h : sem_step n D a c) : 1 ≤ fanout D a :=
  Finset.card_pos.mpr ⟨_, sem_step_reader h⟩

lemma C6.DagTools.sem_step_unique {a c c' : ℕ} (h1 : sem_step n D a c) (h2 : sem_step n D a c')
    (hf : fanout D a = 1) : c = c' := by
  have m1 := sem_step_reader h1
  have m2 := sem_step_reader h2
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp (show (readers D a).card = 1 from hf)
  rw [hr, Finset.mem_singleton] at m1 m2
  have := h1.2.1
  have := h2.2.1
  omega

lemma C6.DagTools.sem_changed_path (hS : Strict n D) (x y : Fin n → Bool) (v : Fin n)
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

def C6.DagTools.sem_Dom (n : ℕ) (D : Dag) (b v : ℕ) : Prop :=
  b = v ∨ ¬ Relation.ReflTransGen (fun a c => sem_step n D a c ∧ c ≠ b) v (outW n D)

lemma C6.DagTools.sem_dom_eq (hS : Strict n D) (x y : Fin n → Bool) (v : Fin n)
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

def C6.DagTools.sem_Chain (n : ℕ) (D : Dag) (a b : ℕ) : Prop :=
  Relation.ReflTransGen (fun a c => sem_step n D a c ∧ fanout D a = 1) a b

lemma C6.DagTools.sem_chain_dom (hS : Strict n D) {v b : ℕ} (h : sem_Chain n D v b) :
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

lemma C6.DagTools.sem_carrier_chain (hS : Strict n D) (v : Fin n) : ∀ w, v ∈ supp n D w →
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

lemma C6.DagTools.sem_single_no_edge (hG : sem_Gr G) (v : Fin n) : ¬ sem_Edge G (single v) := by
  rintro ⟨a, c, hac, ha, hc⟩
  simp only [single, decide_eq_true_eq] at ha hc
  rw [ha, hc] at hac
  exact hG.2.1 _ hac

lemma C6.DagTools.sem_two_edge {u v : Fin n} (huv : G u v) : sem_Edge G (sem_two u v) :=
  ⟨u, v, huv, by simp [sem_two], by simp [sem_two]⟩

lemma C6.DagTools.sem_supp_out (hG : sem_Gr G) (hC : sem_Comp n G D) : supp n D (outW n D) = ∅ :=
  Finset.eq_empty_iff_forall_notMem.2
    (fun v hv => sem_single_no_edge hG v ((hC _).1 (mem_supp.1 hv)))

lemma C6.DagTools.sem_dom_pure (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) (v : Fin n)
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

lemma C6.DagTools.sem_first_branch (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) (v : Fin n)
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

def C6.DagTools.sem_FirstBranch (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Prop :=
  ∀ v ∈ eligSet n D, 2 ≤ fanout D (b v) ∧ supp n D (b v) = {v} ∧ sem_Chain n D v.val (b v)

lemma C6.DagTools.sem_exists_firstBranch (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) :
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

lemma C6.DagTools.sem_firstBranch_pure {b : Fin n → ℕ} (hb : sem_FirstBranch n D b) : PureBranch n D b :=
  fun v hv => ⟨(hb v hv).1, (hb v hv).2.1⟩

lemma C6.DagTools.sem_exists_pureBranch (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) :
    ∃ b : Fin n → ℕ, PureBranch n D b := by
  obtain ⟨b, hb⟩ := sem_exists_firstBranch hG hS hC
  exact ⟨b, sem_firstBranch_pure hb⟩

lemma C6.DagTools.sem_mem_inelig {v : Fin n} : v ∈ ineligSet n D ↔ v ∉ eligSet n D := by
  simp [ineligSet]

lemma C6.DagTools.sem_inelig_chain (hS : Strict n D) {v : Fin n} (hv : v ∈ ineligSet n D) {w : ℕ}
    (hw : v ∈ supp n D w) : sem_Chain n D v.val w :=
  sem_carrier_chain hS v w hw (fun u _ hu => mem_ineligSet.mp hv u hu)

lemma C6.DagTools.sem_inelig_pure (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) {v : Fin n}
    (hv : v ∈ ineligSet n D) {w : ℕ} (hw : v ∈ supp n D w) : supp n D w = {v} :=
  Finset.Subset.antisymm (sem_dom_pure hG hS hC v w (sem_chain_dom hS (sem_inelig_chain hS hv hw)))
    (Finset.singleton_subset_iff.mpr hw)

lemma C6.DagTools.sem_mem_carrier1 {v : Fin n} {w : ℕ} : w ∈ carrierT n D {v} ↔ v ∈ supp n D w := by
  simp only [carrierT, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨-, u, hu⟩
    rw [Finset.mem_inter, Finset.mem_singleton] at hu
    exact hu.2 ▸ hu.1
  · intro h
    exact ⟨sem_supp_lt h, v, Finset.mem_inter.mpr ⟨h, Finset.mem_singleton_self v⟩⟩

lemma C6.DagTools.sem_mem_exit1 {v : Fin n} {e : ℕ × Bool} : e ∈ exitArcs n D (carrierT n D {v}) ↔
    e.1 < D.length ∧ v ∈ supp n D (src D e) ∧ v ∉ supp n D (n + e.1) := by
  simp only [exitArcs, arcs, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    Finset.mem_univ, and_true, sem_mem_carrier1]

lemma C6.DagTools.sem_inelig_surplus {v : Fin n} (hv : v ∈ ineligSet n D) :
    surplusOn D (carrierT n D {v}) = 0 := by
  unfold surplusOn
  refine Finset.sum_eq_zero (fun w hw => ?_)
  have := mem_ineligSet.mp hv w (sem_mem_carrier1.mp hw)
  omega

lemma C6.DagTools.sem_joint_meeting (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
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

lemma C6.DagTools.sem_inelig_consumer (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
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

lemma C6.DagTools.sem_elig_cover (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
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

end SemCore

def C6.DagTools.sem_W (n : ℕ) (D : Dag) (x : Fin n) : Finset (ℕ × Bool) := exitArcs n D (carrierT n D {x})

def C6.DagTools.sem_bar (e : ℕ × Bool) : ℕ × Bool := (e.1, !e.2)

section SemCodes

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

lemma C6.DagTools.sem_mem_W {x : Fin n} {e : ℕ × Bool} : e ∈ sem_W n D x ↔
    e.1 < D.length ∧ x ∈ supp n D (src D e) ∧ x ∉ supp n D (n + e.1) := sem_mem_exit1

lemma C6.DagTools.sem_bar_bar (e : ℕ × Bool) : sem_bar (sem_bar e) = e := by simp [sem_bar]

lemma C6.DagTools.sem_bar_ne (e : ℕ × Bool) : sem_bar e ≠ e := by
  intro h
  have h2 := congrArg Prod.snd h
  simp [sem_bar] at h2

lemma C6.DagTools.sem_same_gate {e f : ℕ × Bool} (h : e.1 = f.1) : f = e ∨ f = sem_bar e := by
  obtain ⟨j, s⟩ := e
  obtain ⟨k, t⟩ := f
  simp only at h
  subst h
  cases s <;> cases t <;> simp [sem_bar]

lemma C6.DagTools.sem_W_and (hS : Strict n D) {x : Fin n} {e : ℕ × Bool} (he : e ∈ sem_W n D x) :
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

lemma C6.DagTools.sem_flow1 (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D) (x : Fin n) :
    (sem_W n D x).card + (merges n D (carrierT n D {x})).card =
      1 + surplusOn D (carrierT n D {x}) := by
  have h1 := carrier_flow_union h {x} (by rw [sem_supp_out hG hC]; simp)
  rwa [Finset.card_singleton] at h1

lemma C6.DagTools.sem_edge_slots (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) {x y : Fin n}
    (hxy : G x y) : ∃ e, e ∈ sem_W n D x ∧ sem_bar e ∈ sem_W n D y ∧
      y ∉ supp n D (src D e) ∧ x ∉ supp n D (src D (sem_bar e)) ∧
      val D (sem_two x y) (n + e.1) = true := by
  obtain ⟨j, hj, -, hval, hju, hjv, s, h1, h2, h3, h4⟩ := sem_joint_meeting hG hS hC hxy
  exact ⟨(j, s), sem_mem_W.mpr ⟨hj, h1, hju⟩, sem_mem_W.mpr ⟨hj, h3, hjv⟩, h2, h4, hval⟩

end SemCodes

section SemArms

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

lemma C6.DagTools.sem_zm_gate (hS : Strict n D) {x : Fin n} (hM : merges n D (carrierT n D {x}) = ∅)
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

lemma C6.DagTools.sem_code_count (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
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

open PEqualNP.Outside.L_meta_2590_aux.C6.DagTools

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

open PEqualNP.Outside.L_meta_2590_aux.C6.DagTools

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

open PEqualNP.Outside.L_meta_2590_aux.C6.DagTools

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

open PEqualNP.Outside.L_meta_2590_aux.C6.DagTools

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
open PEqualNP.Outside.L_meta_2590_aux.C6.DagTools

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

open PEqualNP.Outside.L_meta_2590_aux.C6 PEqualNP.Outside.L_meta_2590_aux.C6.DagTools PEqualNP.Outside.L_meta_2590_aux.C6.ThreeBirth PEqualNP.Outside.L_meta_2590_aux.LinearNoise PEqualNP.Outside.L_meta_2590_aux.BirthNoiseProjection

lemma BirthNoiseAdapter.no_sorted_three_births {D : Dag} (hD : Strict 6 D)
    (birth L R : Fin 3 → Nat) (hb : StrictMono birth)
    (hbvalid : ∀ i, birth i < D.length)
    (σ : Fin 3 → Fin 3) (hσ : Function.Bijective σ)
    (hL : ∀ i, L i < 6 + birth i) (hR : ∀ i, R i < 6 + birth i)
    (hgate : ∀ i (x : V → Bool), val D x (6 + birth i) =
      (val D x (L i) && val D x (R i)))
    (hlinL : ∀ i (x : V → Bool), linear (supp 6 D (L i)) x = (factors (σ i) x).1)
    (hlinR : ∀ i (x : V → Bool), linear (supp 6 D (R i)) x = (factors (σ i) x).2)
    (hzero : ∀ j, j < D.length → tag D j = true → supp 6 D (6 + j) = ∅)
    (hkind : ∀ j, j < D.length → tag D j = true →
      (∃ i, birth i = j) ∨ (supp 6 D (opA D j) = ∅ ∧ supp 6 D (opB D j) = ∅))
    (out : Nat) (hout : out < 6 + D.length) (hsout : supp 6 D out = ∅)
    (hcorrect : ∀ x : V → Bool, val D x out = edgeBool x) : False := by
  classical
  have hLn : ∀ i, ∃ f : (Fin 3 → Bool) → Bool,
      ZeroMono f ∧ UsesAtMost 6 birth (L i) f ∧
      ∀ x : V → Bool, val D x (L i) =
        (linear (supp 6 D (L i)) x || f (fun j => val D x (6 + birth j))) := by
    intro i
    exact wire_noise hD birth hzero hkind (L i) (by have := hL i; have := hbvalid i; omega)
  have hRn : ∀ i, ∃ f : (Fin 3 → Bool) → Bool,
      ZeroMono f ∧ UsesAtMost 6 birth (R i) f ∧
      ∀ x : V → Bool, val D x (R i) =
        (linear (supp 6 D (R i)) x || f (fun j => val D x (6 + birth j))) := by
    intro i
    exact wire_noise hD birth hzero hkind (R i) (by have := hR i; have := hbvalid i; omega)
  choose lf hlz hlu hle using hLn
  choose rf hrz hru hre using hRn
  let B (x : V → Bool) (i : Fin 3) := val D x (6 + birth i)
  let p (a : Bool) := lf 1 ![a, false, false]
  let q (a : Bool) := rf 1 ![a, false, false]
  let r (a b : Bool) := lf 2 ![a, b, false]
  let s (a b : Bool) := rf 2 ![a, b, false]
  have h0 (x : V → Bool) : B x 0 =
      ((factors (σ 0) x).1 && (factors (σ 0) x).2) := by
    dsimp only [B]
    rw [hgate, hle, hre, hlinL, hlinR,
      zero_before_zero hb (hlu 0) (hlz 0) (hL 0),
      zero_before_zero hb (hru 0) (hrz 0) (hR 0)]
    simp only [Bool.or_false]
  have h1 (x : V → Bool) : B x 1 =
      (((factors (σ 1) x).1 || p (B x 0)) &&
        ((factors (σ 1) x).2 || q (B x 0))) := by
    dsimp only [B, p, q]
    rw [hgate, hle, hre, hlinL, hlinR,
      uses_before_one hb (hlu 1) (hL 1), uses_before_one hb (hru 1) (hR 1)]
  have h2 (x : V → Bool) : B x 2 =
      (((factors (σ 2) x).1 || r (B x 0) (B x 1)) &&
        ((factors (σ 2) x).2 || s (B x 0) (B x 1))) := by
    dsimp only [B, r, s]
    rw [hgate, hle, hre, hlinL, hlinR,
      uses_before_two hb (hlu 2) (hL 2), uses_before_two hb (hru 2) (hR 2)]
  have hB (x : V → Bool) : B x = generalBirths σ p q r s x := by
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
    (hgate : ∀ i (x : V → Bool), val D x (6 + G i) =
      (val D x (L i) && val D x (R i)))
    (hlinL : ∀ i (x : V → Bool), linear (supp 6 D (L i)) x = (factors i x).1)
    (hlinR : ∀ i (x : V → Bool), linear (supp 6 D (R i)) x = (factors i x).2)
    (hzero : ∀ j, j < D.length → tag D j = true → supp 6 D (6 + j) = ∅)
    (hother : ∀ j, j < D.length → tag D j = true → (∀ i, j ≠ G i) →
      supp 6 D (opA D j) = ∅ ∧ supp 6 D (opB D j) = ∅)
    (out : Nat) (hout : out < 6 + D.length) (hsout : supp 6 D out = ∅)
    (hcorrect : ∀ x : V → Bool, val D x out = edgeBool x) : False := by
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

open PEqualNP.Outside.L_meta_2590_aux.C6.DagTools PEqualNP.Outside.L_meta_2590_aux.LinearNoise

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

open PEqualNP.Outside.L_meta_2590_aux.C6.DagTools

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
open PEqualNP.Outside.L_meta_2590_aux.C6.DagTools

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

open PEqualNP.Outside.L_meta_2590_aux.C6.DagTools

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

open PEqualNP.Outside.L_meta_2590_aux.C6.DagTools PEqualNP.Outside.L_meta_2590_aux.LinearNoise

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

open PEqualNP.Outside.L_meta_2590_aux.C6.DagTools

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

open PEqualNP.Outside.L_meta_2590_aux.C6.DagTools

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

open PEqualNP.Outside.L_meta_2590_aux.C6.DagTools

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

open PEqualNP.Outside.L_meta_2590_aux.C6.DagTools

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

open PEqualNP.Outside.L_meta_2590_aux.C6.DagTools

lemma C6.DagTools.na_no_reader {D : Dag} {w : ℕ} (h : fanout D w = 0) (j : ℕ) (hj : j < D.length) :
    opA D j ≠ w ∧ opB D j ≠ w := by
  unfold fanout readers at h
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
  have := h (Finset.mem_range.mpr hj)
  tauto

def C6.DagTools.na_sh (c a : ℕ) : ℕ := if c < a then a - 1 else a

def C6.DagTools.na_up (c w : ℕ) : ℕ := if w < c then w else w + 1

def C6.DagTools.na_del (n j : ℕ) (D : Dag) : Dag :=
  (D.eraseIdx j).map (fun g => (g.1, na_sh (n + j) g.2.1, na_sh (n + j) g.2.2))

lemma C6.DagTools.na_del_length (n j : ℕ) (D : Dag) (hj : j < D.length) :
    (na_del n j D).length = D.length - 1 := by
  simp [na_del, List.length_eraseIdx, hj]

lemma C6.DagTools.na_del_ops (n j : ℕ) (D : Dag) (k : ℕ) (hk : na_up j k < D.length) :
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

lemma C6.DagTools.na_del_strict {n : ℕ} {D : Dag} (hS : Strict n D) (j : ℕ) (hj : j < D.length)
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

lemma C6.DagTools.na_del_val {n : ℕ} {D : Dag} (hS : Strict n D) (j : ℕ) (hj : j < D.length)
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


end packScope22

section packScope23
open PEqualNP.Outside.L_meta_2590_aux.C6.DagTools

end packScope23

section packScope24
open PEqualNP.Outside.L_meta_2590_aux.C6.DagTools

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

open PEqualNP.Outside.L_meta_2590_aux.C6.DagTools

end packScope25

section packScope26
open PEqualNP.Outside.L_meta_2590_aux.PairPruning

open PEqualNP.Outside.L_meta_2590_aux.C6.DagTools

set_option synthInstance.maxSize 4096 in
lemma PairPruning.c6Target_iff_adj (x : Fin 6 → Bool) :
    c6Target x = true ↔ sem_Edge C6.adj x := by
  revert x
  unfold c6Target sem_Edge C6.adj
  decide +kernel

end packScope26

section packScope27
open PEqualNP.Outside.L_meta_2590_aux.C6.DagTools

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

open PEqualNP.Outside.L_meta_2590_aux.C6.DagTools

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

open PEqualNP.Outside.L_meta_2590_aux.C6.DagTools PEqualNP.Outside.L_meta_2590_aux.PairPruning

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

end PEqualNP.Outside.L_meta_2590_aux
