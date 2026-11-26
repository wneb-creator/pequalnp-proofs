import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17589_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def gop : Bool → Bool → Bool → Bool
  | true, a, b => a && b
  | false, a, b => a || b

@[simp] theorem gop_true (a b : Bool) : gop true a b = (a && b) := rfl
@[simp] theorem gop_false (a b : Bool) : gop false a b = (a || b) := rfl

abbrev Dag := List (Bool × ℕ × ℕ)

def tag (D : Dag) (j : ℕ) : Bool := (D.getD j (false, 0, 0)).1
def opA (D : Dag) (j : ℕ) : ℕ := (D.getD j (false, 0, 0)).2.1
def opB (D : Dag) (j : ℕ) : ℕ := (D.getD j (false, 0, 0)).2.2

def wstep (w : List Bool) (g : Bool × ℕ × ℕ) : List Bool :=
  w ++ [gop g.1 (w.getD g.2.1 false) (w.getD g.2.2 false)]

def wl (D : Dag) (w : List Bool) : List Bool := D.foldl wstep w

def val (D : Dag) {n : ℕ} (x : Fin n → Bool) (w : ℕ) : Bool :=
  (wl D (List.ofFn x)).getD w false

def Strict (n : ℕ) (D : Dag) : Prop :=
  ∀ j, j < D.length → opA D j < n + j ∧ opB D j < n + j ∧ opA D j ≠ opB D j

def readers (D : Dag) (w : ℕ) : Finset ℕ :=
  (Finset.range D.length).filter (fun j => opA D j = w ∨ opB D j = w)

def fanout (D : Dag) (w : ℕ) : ℕ := (readers D w).card

def Live (n : ℕ) (D : Dag) : Prop := ∀ w, w + 1 < n + D.length → 1 ≤ fanout D w

def StrictLive (n : ℕ) (D : Dag) : Prop := Strict n D ∧ Live n D ∧ D ≠ []

def outW (n : ℕ) (D : Dag) : ℕ := n + D.length - 1

def single {n : ℕ} (v : Fin n) : Fin n → Bool := fun i => decide (i = v)

def supp (n : ℕ) (D : Dag) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => val D (single v) w = true)

def surplusOn (D : Dag) (K : Finset ℕ) : ℕ := ∑ w ∈ K, (fanout D w - 1)

def inner (n : ℕ) (D : Dag) : Finset ℕ := Finset.range (n + D.length - 1)

def totalSurplus (n : ℕ) (D : Dag) : ℕ := surplusOn D (inner n D)

def Bplus (n : ℕ) (D : Dag) : ℕ :=
  surplusOn D ((inner n D).filter (fun w => (supp n D w).Nonempty))

def Bzero (n : ℕ) (D : Dag) : ℕ :=
  surplusOn D ((inner n D).filter (fun w => ¬ (supp n D w).Nonempty))

def branchW (n : ℕ) (D : Dag) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => 2 ≤ fanout D w)

def eligSet (n : ℕ) (D : Dag) : Finset (Fin n) := (branchW n D).biUnion (supp n D)

def ineligSet (n : ℕ) (D : Dag) : Finset (Fin n) := Finset.univ \ eligSet n D

def units (n : ℕ) (D : Dag) : Finset (Σ _ : ℕ, ℕ) :=
  (inner n D).sigma (fun w => Finset.range (fanout D w - 1))

def unitsPlus (n : ℕ) (D : Dag) : Finset (Σ _ : ℕ, ℕ) :=
  (units n D).filter (fun u => (supp n D u.1).Nonempty)

def unitsOn (n : ℕ) (D : Dag) (K : Finset ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (units n D).filter (fun u => u.1 ∈ K)

def arcs (D : Dag) : Finset (ℕ × Bool) := Finset.range D.length ×ˢ Finset.univ

def src (D : Dag) (e : ℕ × Bool) : ℕ := if e.2 = true then opB D e.1 else opA D e.1

def exitArcs (n : ℕ) (D : Dag) (K : Finset ℕ) : Finset (ℕ × Bool) :=
  (arcs D).filter (fun e => src D e ∈ K ∧ n + e.1 ∉ K)

def merges (n : ℕ) (D : Dag) (K : Finset ℕ) : Finset ℕ :=
  (Finset.range D.length).filter (fun j => n + j ∈ K ∧ opA D j ∈ K ∧ opB D j ∈ K)

def sources (n : ℕ) (K : Finset ℕ) : Finset ℕ := K.filter (fun w => w < n)

def carrierT (n : ℕ) (D : Dag) (T : Finset (Fin n)) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => (supp n D w ∩ T).Nonempty)

def carrierDiff (n : ℕ) (D : Dag) (x y : Fin n) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => x ∈ supp n D w ∧ y ∉ supp n D w)

def PureBranch (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Prop :=
  ∀ v ∈ eligSet n D, 2 ≤ fanout D (b v) ∧ supp n D (b v) = {v}

def reservedUnits (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (eligSet n D).image (fun v => (⟨b v, 0⟩ : Σ _ : ℕ, ℕ))

def residualUnits (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  unitsPlus n D \ reservedUnits n D b

theorem tag_eq (D : Dag) (j : ℕ) (h : j < D.length) : tag D j = (D[j]).1 := by
  simp [tag, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem opA_eq (D : Dag) (j : ℕ) (h : j < D.length) : opA D j = (D[j]).2.1 := by
  simp [opA, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem opB_eq (D : Dag) (j : ℕ) (h : j < D.length) : opB D j = (D[j]).2.2 := by
  simp [opB, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem wl_cons (g : Bool × ℕ × ℕ) (D : Dag) (w : List Bool) :
    wl (g :: D) w = wl D (wstep w g) := rfl

theorem wl_append (D E : Dag) (w : List Bool) : wl (D ++ E) w = wl E (wl D w) := by
  simp [wl, List.foldl_append]

theorem wstep_length (w : List Bool) (g : Bool × ℕ × ℕ) : (wstep w g).length = w.length + 1 := by
  simp [wstep]

theorem wl_length (D : Dag) : ∀ w : List Bool, (wl D w).length = w.length + D.length := by
  induction D with
  | nil => intro w; simp [wl]
  | cons g D ih => intro w; rw [wl_cons, ih, wstep_length]; simp; omega

theorem wstep_getD_lt (w : List Bool) (g : Bool × ℕ × ℕ) (i : ℕ) (h : i < w.length) :
    (wstep w g).getD i false = w.getD i false := by
  simp [wstep, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem wl_getD_lt (D : Dag) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wl D w).getD i false = w.getD i false := by
  induction D with
  | nil => intro w i _; rfl
  | cons g D ih =>
    intro w i h
    rw [wl_cons, ih _ _ (by rw [wstep_length]; omega), wstep_getD_lt _ _ _ h]

theorem getD_ge (w : List Bool) (i : ℕ) (h : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem wstep_getD_last (w : List Bool) (g : Bool × ℕ × ℕ) :
    (wstep w g).getD w.length false = gop g.1 (w.getD g.2.1 false) (w.getD g.2.2 false) := by
  simp [wstep, List.getD_eq_getElem?_getD]

theorem wl_getD_gate (D : Dag) (w : List Bool) (j : ℕ) (hj : j < D.length) :
    (wl D w).getD (w.length + j) false =
      gop (tag D j) ((wl (D.take j) w).getD (opA D j) false)
        ((wl (D.take j) w).getD (opB D j) false) := by
  have hsplit : D = D.take j ++ D[j] :: D.drop (j + 1) := by simp
  have hlen : (wl (D.take j) w).length = w.length + j := by
    rw [wl_length, List.length_take]; omega
  rw [tag_eq D j hj, opA_eq D j hj, opB_eq D j hj]
  conv_lhs => rw [hsplit, wl_append, wl_cons]
  rw [wl_getD_lt _ _ _ (by rw [wstep_length, hlen]; omega), ← hlen, wstep_getD_last]

theorem wl_take_getD (D : Dag) (w : List Bool) (j i : ℕ) (hi : i < w.length + j)
    (hj : j ≤ D.length) :
    (wl (D.take j) w).getD i false = (wl D w).getD i false := by
  have hsplit : D = D.take j ++ D.drop j := by simp
  have hlen : (wl (D.take j) w).length = w.length + j := by
    rw [wl_length, List.length_take]; omega
  conv_rhs => rw [hsplit, wl_append]
  rw [wl_getD_lt (D.drop j) (wl (D.take j) w) i (by rw [hlen]; exact hi)]

theorem val_input (D : Dag) {n : ℕ} (x : Fin n → Bool) (i : ℕ) (h : i < n) :
    val D x i = x ⟨i, h⟩ := by
  unfold val
  rw [wl_getD_lt _ _ _ (by simpa using h)]
  simp [List.getD_eq_getElem?_getD, h]

theorem val_ge (D : Dag) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (h : n + D.length ≤ w) :
    val D x w = false := by
  unfold val
  exact getD_ge _ _ (by rw [wl_length]; simpa using h)

theorem val_take (D : Dag) {n : ℕ} (x : Fin n → Bool) (k w : ℕ) (hw : w < n + k)
    (hk : k ≤ D.length) : val (D.take k) x w = val D x w := by
  unfold val
  exact wl_take_getD D _ k w (by simpa using hw) hk

theorem val_gate {n : ℕ} {D : Dag} (hS : Strict n D) (x : Fin n → Bool) (j : ℕ)
    (hj : j < D.length) :
    val D x (n + j) = gop (tag D j) (val D x (opA D j)) (val D x (opB D j)) := by
  obtain ⟨ha, hb, -⟩ := hS j hj
  have h := wl_getD_gate D (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  unfold val
  rw [h, wl_take_getD D _ j _ (by simpa using ha) hj.le,
    wl_take_getD D _ j _ (by simpa using hb) hj.le]

theorem val_unique {n : ℕ} {D : Dag} (hS : Strict n D) (x : Fin n → Bool) (f : ℕ → Bool)
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

abbrev Ref := Bool ⊕ ℕ

def refVal (W : List Bool) : Ref → Bool
  | Sum.inl b => b
  | Sum.inr k => W.getD k false

def na_look (m : List Ref) (i : ℕ) : Ref := m.getD i (Sum.inl false)

def na_comb (t : Bool) : Ref → Ref → Ref ⊕ (ℕ × ℕ)
  | Sum.inl a, r => Sum.inl (if a = t then r else Sum.inl a)
  | Sum.inr i, Sum.inl b => Sum.inl (if b = t then Sum.inr i else Sum.inl b)
  | Sum.inr i, Sum.inr j => if i = j then Sum.inl (Sum.inr i) else Sum.inr (i, j)

def na_isAnd : GateOp → Bool
  | GateOp.and => true
  | _ => false

def na_step (n : ℕ) (st : List Ref × Dag) (g : Gate) : List Ref × Dag :=
  match g.inputs with
  | [] => (st.1 ++ [Sum.inl (na_isAnd g.op)], st.2)
  | [a] => (st.1 ++ [na_look st.1 a], st.2)
  | a :: b :: _ =>
    match na_comb (na_isAnd g.op) (na_look st.1 a) (na_look st.1 b) with
    | Sum.inl r => (st.1 ++ [r], st.2)
    | Sum.inr p => (st.1 ++ [Sum.inr (n + st.2.length)], st.2 ++ [(na_isAnd g.op, p.1, p.2)])

def na_ok (B : ℕ) : Ref → Prop
  | Sum.inl _ => True
  | Sum.inr k => k < B

def na_Good (n : ℕ) (st : List Ref × Dag) : Prop :=
  Strict n st.2 ∧ ∀ r ∈ st.1, na_ok (n + st.2.length) r

theorem na_ok_mono {B B' : ℕ} (h : B ≤ B') (r : Ref) (hr : na_ok B r) : na_ok B' r := by
  rcases r with b | k
  · trivial
  · exact lt_of_lt_of_le hr h

theorem na_look_val (W : List Bool) (m : List Ref) (i : ℕ) :
    refVal W (na_look m i) = (m.map (refVal W)).getD i false := by
  simp only [na_look, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases m[i]? <;> rfl

theorem na_look_ok (B : ℕ) (m : List Ref) (hm : ∀ r ∈ m, na_ok B r) (i : ℕ) :
    na_ok B (na_look m i) := by
  simp only [na_look, List.getD_eq_getElem?_getD]
  rcases h : m[i]? with _ | r
  · trivial
  · exact hm r (List.mem_of_getElem? h)

theorem na_refVal_wstep (W : List Bool) (g : Bool × ℕ × ℕ) (r : Ref) (hr : na_ok W.length r) :
    refVal (wstep W g) r = refVal W r := by
  rcases r with b | k
  · rfl
  · exact wstep_getD_lt W g k hr

theorem na_comb_inl (t : Bool) (W : List Bool) (a b r : Ref) (h : na_comb t a b = Sum.inl r) :
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

theorem na_comb_ok (B : ℕ) (t : Bool) (a b r : Ref) (ha : na_ok B a) (hb : na_ok B b)
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

theorem na_comb_inr (t : Bool) (a b : Ref) (p : ℕ × ℕ) (h : na_comb t a b = Sum.inr p) :
    a = Sum.inr p.1 ∧ b = Sum.inr p.2 ∧ p.1 ≠ p.2 := by
  rcases a with a | i
  · simp [na_comb] at h
  · rcases b with b | j
    · simp [na_comb] at h
    · simp only [na_comb] at h
      split_ifs at h with hij
      cases h
      exact ⟨rfl, rfl, hij⟩

theorem na_eval0 (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
    op.eval [] = na_isAnd op := by
  rcases hop with rfl | rfl <;> rfl

theorem na_eval1 (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (u : Bool) :
    op.eval [u] = u := by
  rcases hop with rfl | rfl <;> simp [GateOp.eval]

theorem na_eval2 (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (u v : Bool) : op.eval [u, v] = gop (na_isAnd op) u v := by
  rcases hop with rfl | rfl <;> simp [GateOp.eval, na_isAnd]

theorem na_getD_append_lt (D E : Dag) (k : ℕ) (h : k < D.length) :
    (D ++ E).getD k (false, 0, 0) = D.getD k (false, 0, 0) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem na_getD_snoc (D : Dag) (g : Bool × ℕ × ℕ) :
    (D ++ [g]).getD D.length (false, 0, 0) = g := by
  simp [List.getD_eq_getElem?_getD]

theorem na_strict_snoc {n : ℕ} {D : Dag} (hS : Strict n D) (t : Bool) (i j : ℕ)
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

theorem na_strict_take {n : ℕ} {D : Dag} (hS : Strict n D) (k : ℕ) : Strict n (D.take k) := by
  intro j hj
  simp only [List.length_take] at hj
  have hj1 : j < k := by omega
  have hj2 : j < D.length := by omega
  have e : (D.take k).getD j (false, 0, 0) = D.getD j (false, 0, 0) := by
    simp [List.getD_eq_getElem?_getD, hj1]
  simp only [opA, opB, e]
  exact hS j hj2

theorem na_step_spec (n : ℕ) (st : List Ref × Dag) (g : Gate)
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

theorem na_fold_spec (n : ℕ) (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ st : List Ref × Dag, na_Good n st →
      na_Good n (gs.foldl (na_step n) st) ∧
      (gs.foldl (na_step n) st).2.length ≤ st.2.length + gs.length ∧
      ∀ (x : Fin n → Bool) (w : List Bool), st.1.map (refVal (wl st.2 (List.ofFn x))) = w →
        (gs.foldl (na_step n) st).1.map
            (refVal (wl (gs.foldl (na_step n) st).2 (List.ofFn x))) =
          gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w := by
  induction gs with
  | nil => intro st h; exact ⟨h, by simp, fun x w hw => hw⟩
  | cons g gs ih =>
    intro st h
    obtain ⟨h1, h2, h3⟩ := na_step_spec n st g (hgs g (by simp)) h
    obtain ⟨i1, i2, i3⟩ := ih (fun g' hg' => hgs g' (by simp [hg'])) _ h1
    refine ⟨i1, ?_, fun x w hw => ?_⟩
    · simp only [List.foldl_cons, List.length_cons]; omega
    · simp only [List.foldl_cons]; exact i3 x _ (h3 x w hw)

theorem na_init (n : ℕ) (x : Fin n → Bool) :
    ((List.range n).map Sum.inr).map (refVal (wl ([] : Dag) (List.ofFn x))) = List.ofFn x := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp [refVal, wl, List.getD_eq_getElem?_getD, h1]

theorem exists_strict_of_monotone2 {n : ℕ} (C : Circuit) (hmono : Monotone2 C) :
    (∃ b : Bool, ∀ x : Fin n → Bool, C.eval (List.ofFn x) = b) ∨
    (∃ i : Fin n, ∀ x : Fin n → Bool, C.eval (List.ofFn x) = x i) ∨
    (∃ D : Dag, Strict n D ∧ D ≠ [] ∧ D.length ≤ C.size ∧
      ∀ x : Fin n → Bool, val D x (outW n D) = C.eval (List.ofFn x)) := by
  have h0 : na_Good n ((List.range n).map Sum.inr, ([] : Dag)) := by
    refine ⟨fun j hj => absurd hj (by simp), fun r hr => ?_⟩
    simp only [List.mem_map, List.mem_range] at hr
    obtain ⟨k, hk, rfl⟩ := hr
    simpa [na_ok] using hk
  obtain ⟨⟨hS, hok⟩, hlen, hsem⟩ := na_fold_spec n C.gates hmono _ h0
  generalize C.gates.foldl (na_step n) ((List.range n).map Sum.inr, ([] : Dag)) = st
    at hS hok hlen hsem
  obtain ⟨m, D⟩ := st
  dsimp only at hS hok hlen hsem
  have hev : ∀ x : Fin n → Bool,
      C.eval (List.ofFn x) = refVal (wl D (List.ofFn x)) (na_look m C.output) := by
    intro x
    rw [na_look_val, hsem x (List.ofFn x) (na_init n x)]
    rfl
  have hk := na_look_ok _ m hok C.output
  rcases hr : na_look m C.output with b | k
  · exact Or.inl ⟨b, fun x => by rw [hev x, hr]; rfl⟩
  · rw [hr] at hk
    have hk' : k < n + D.length := hk
    by_cases hkn : k < n
    · exact Or.inr (Or.inl ⟨⟨k, hkn⟩, fun x => by rw [hev x, hr]; exact val_input D x k hkn⟩)
    · have hl : (D.take (k - n + 1)).length = k - n + 1 := by
        rw [List.length_take]; omega
      refine Or.inr (Or.inr ⟨D.take (k - n + 1), na_strict_take hS _, ?_, ?_, fun x => ?_⟩)
      · intro h
        rw [h] at hl
        simp at hl
      · rw [hl]
        simp only [List.length_nil, Nat.zero_add] at hlen
        unfold Circuit.size
        omega
      · have ho : outW n (D.take (k - n + 1)) = k := by unfold outW; rw [hl]; omega
        rw [ho, val_take D x (k - n + 1) k (by omega) (by omega), hev x, hr]
        rfl

theorem na_no_reader {D : Dag} {w : ℕ} (h : fanout D w = 0) (j : ℕ) (hj : j < D.length) :
    opA D j ≠ w ∧ opB D j ≠ w := by
  unfold fanout readers at h
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
  have := h (Finset.mem_range.mpr hj)
  tauto

def na_sh (c a : ℕ) : ℕ := if c < a then a - 1 else a

def na_up (c w : ℕ) : ℕ := if w < c then w else w + 1

def na_del (n j : ℕ) (D : Dag) : Dag :=
  (D.eraseIdx j).map (fun g => (g.1, na_sh (n + j) g.2.1, na_sh (n + j) g.2.2))

theorem na_del_length (n j : ℕ) (D : Dag) (hj : j < D.length) :
    (na_del n j D).length = D.length - 1 := by
  simp [na_del, List.length_eraseIdx, hj]

theorem na_del_ops (n j : ℕ) (D : Dag) (k : ℕ) (hk : na_up j k < D.length) :
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

theorem na_del_strict {n : ℕ} {D : Dag} (hS : Strict n D) (j : ℕ) (hj : j < D.length)
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

theorem na_del_val {n : ℕ} {D : Dag} (hS : Strict n D) (j : ℕ) (hj : j < D.length)
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

theorem na_live_aux {n : ℕ} (F : (Fin n → Bool) → Bool)
    (hess : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ k, k ≠ i → x k = y k) ∧ F x ≠ F y) :
    ∀ (s : ℕ) (D : Dag), D.length = s → Strict n D → D ≠ [] →
      (∀ x : Fin n → Bool, val D x (outW n D) = F x) →
      ∃ D' : Dag, StrictLive n D' ∧ D'.length ≤ s ∧
        ∀ x : Fin n → Bool, val D' x (outW n D') = F x := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro D hlen hS hne hD
    have hpos : 0 < D.length := List.length_pos_iff.mpr hne
    by_cases hL : Live n D
    · exact ⟨D, ⟨hS, hL, hne⟩, hlen.le, hD⟩
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
        obtain ⟨D', h1, h2, h3⟩ := ih (D.length - 1) (by omega) (na_del n j D) hl
          (na_del_strict hS j hj hf0)
          (fun h => by rw [h] at hl; simp at hl; omega)
          (fun x => by
            have ho : outW n (na_del n j D) = n + (D.length - 1) - 1 := by unfold outW; rw [hl]
            have hu : na_up (n + j) (n + (D.length - 1) - 1) = outW n D := by
              unfold na_up outW; split_ifs <;> omega
            rw [ho, na_del_val hS j hj hf0 x _ (by omega), hu]
            exact hD x)
        exact ⟨D', h1, by omega, h3⟩

theorem exists_strictLive_of_strict {n : ℕ} (F : (Fin n → Bool) → Bool)
    (hess : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ k, k ≠ i → x k = y k) ∧ F x ≠ F y)
    (D : Dag) (hS : Strict n D) (hne : D ≠ [])
    (hD : ∀ x : Fin n → Bool, val D x (outW n D) = F x) :
    ∃ D' : Dag, StrictLive n D' ∧ D'.length ≤ D.length ∧
      ∀ x : Fin n → Bool, val D' x (outW n D') = F x :=
  na_live_aux F hess D.length D rfl hS hne hD

theorem normalize_strictLive {n : ℕ} (C : Circuit) (hmono : Monotone2 C)
    (hnc : ∀ b : Bool, ∃ x : Fin n → Bool, C.eval (List.ofFn x) ≠ b)
    (hnp : ∀ i : Fin n, ∃ x : Fin n → Bool, C.eval (List.ofFn x) ≠ x i)
    (hess : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ k, k ≠ i → x k = y k) ∧
      C.eval (List.ofFn x) ≠ C.eval (List.ofFn y)) :
    ∃ D : Dag, StrictLive n D ∧ D.length ≤ C.size ∧
      ∀ x : Fin n → Bool, val D x (outW n D) = C.eval (List.ofFn x) := by
  rcases exists_strict_of_monotone2 (n := n) C hmono with
    ⟨b, hb⟩ | ⟨i, hi⟩ | ⟨D, hS, hne, hlen, hD⟩
  · obtain ⟨x, hx⟩ := hnc b
    exact absurd (hb x) hx
  · obtain ⟨x, hx⟩ := hnp i
    exact absurd (hi x) hx
  · obtain ⟨D', h1, h2, h3⟩ :=
      exists_strictLive_of_strict (fun x => C.eval (List.ofFn x)) hess D hS hne hD
    exact ⟨D', h1, by omega, h3⟩

section SurplusFlow

variable {n : ℕ} {D : Dag}

theorem sb_mem_inner {w : ℕ} : w ∈ inner n D ↔ w + 1 < n + D.length := by
  unfold inner; rw [Finset.mem_range]; omega

theorem sb_src_false (j : ℕ) : src D (j, false) = opA D j := by simp [src]

theorem sb_src_true (j : ℕ) : src D (j, true) = opB D j := by simp [src]

theorem fanout_eq_zero_of_ge (hS : Strict n D) (w : ℕ) (h : n + D.length ≤ w + 1) :
    fanout D w = 0 := by
  unfold fanout readers
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro j hj
  have hj2 := Finset.mem_range.mp hj
  have := hS j hj2
  omega

theorem lt_of_fanout_pos (hS : Strict n D) {w : ℕ} (h : 1 ≤ fanout D w) :
    w + 1 < n + D.length := by
  by_contra hc
  have := fanout_eq_zero_of_ge hS w (by omega)
  omega

theorem sb_card_arcs_filter (P : ℕ × Bool → Prop) [DecidablePred P] :
    ((arcs D).filter P).card = ∑ j ∈ Finset.range D.length,
      ((if P (j, false) then 1 else 0) + (if P (j, true) then 1 else 0)) := by
  rw [Finset.card_filter, arcs, Finset.sum_product]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Fintype.sum_bool, add_comm]

theorem sb_card_arcs : (arcs D).card = 2 * D.length := by
  simp [arcs, Finset.card_product, Nat.mul_comm]

theorem sb_src_lt (hS : Strict n D) (e : ℕ × Bool) (he : e ∈ arcs D) :
    src D e + 1 < n + D.length := by
  obtain ⟨j, c⟩ := e
  have hj : j < D.length := by simpa [arcs] using he
  have := hS j hj
  cases c
  · rw [sb_src_false]; omega
  · rw [sb_src_true]; omega

theorem sb_fanout_arcs (hS : Strict n D) (w : ℕ) :
    fanout D w = ((arcs D).filter (fun e => src D e = w)).card := by
  rw [sb_card_arcs_filter, fanout, readers, Finset.card_filter]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have := (hS j (Finset.mem_range.mp hj)).2.2
  rw [sb_src_false, sb_src_true]
  split_ifs <;> omega

theorem sb_sum_fanout_eq (hS : Strict n D) (K : Finset ℕ) :
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

theorem sb_surplus_add_card {K : Finset ℕ} (hL : ∀ w ∈ K, 1 ≤ fanout D w) :
    surplusOn D K + K.card = ∑ w ∈ K, fanout D w := by
  rw [surplusOn, Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun w hw => Nat.sub_add_cancel (hL w hw))

theorem sum_fanout (hS : Strict n D) :
    ∑ w ∈ Finset.range (n + D.length), fanout D w = 2 * D.length := by
  rw [sb_sum_fanout_eq hS, Finset.filter_true_of_mem, sb_card_arcs]
  intro e he
  have := sb_src_lt hS e he
  exact Finset.mem_range.mpr (by omega)

theorem surplus_identity (h : StrictLive n D) : totalSurplus n D + n = D.length + 1 := by
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

theorem totalSurplus_split (n : ℕ) (D : Dag) : totalSurplus n D = Bplus n D + Bzero n D := by
  unfold totalSurplus Bplus Bzero surplusOn
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

theorem Bplus_le_total (n : ℕ) (D : Dag) : Bplus n D ≤ totalSurplus n D := by
  rw [totalSurplus_split]; omega

theorem Bplus_le_twelve (h13 : totalSurplus n D ≤ 13) (h0 : 1 ≤ Bzero n D) :
    Bplus n D ≤ 12 := by
  rw [totalSurplus_split] at h13; omega

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

theorem mem_supp {v : Fin n} {w : ℕ} : v ∈ supp n D w ↔ val D (single v) w = true := by
  simp [supp]

theorem val_mono (hS : Strict n D) (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true)
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

theorem val_zero (hS : Strict n D) (w : ℕ) : val D (fun _ : Fin n => false) w = false := by
  by_cases hw : w < n + D.length
  · exact val_unique hS _ (fun _ => false) (fun _ _ => rfl)
      (fun j _ => by cases tag D j <;> rfl) w hw
  · exact val_ge D _ w (by omega)

theorem supp_input (D : Dag) (i : Fin n) : supp n D i.val = {i} := by
  ext v
  rw [mem_supp, val_input D (single v) i.val i.isLt]
  simp [single, eq_comm]

theorem supp_ge (D : Dag) (w : ℕ) (h : n + D.length ≤ w) : supp n D w = ∅ := by
  ext v
  simp [mem_supp, val_ge D (single v) w h]

theorem supp_gate (hS : Strict n D) (j : ℕ) (hj : j < D.length) :
    supp n D (n + j) = if tag D j = true then supp n D (opA D j) ∩ supp n D (opB D j)
      else supp n D (opA D j) ∪ supp n D (opB D j) := by
  ext v
  rw [mem_supp, val_gate hS _ j hj]
  cases tag D j <;> simp [mem_supp]

theorem carrier_flow (h : StrictLive n D) (K : Finset ℕ) (hK : K ⊆ inner n D)
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

theorem sb_carrierT_sub (T : Finset (Fin n))
    (hout : supp n D (outW n D) ∩ T = ∅) : carrierT n D T ⊆ inner n D := by
  intro w hw
  simp only [carrierT, Finset.mem_filter, Finset.mem_range] at hw
  rw [sb_mem_inner]
  by_contra hc
  have hw2 : w = outW n D := by unfold outW; omega
  rw [hw2, hout] at hw
  exact Finset.not_nonempty_empty hw.2

theorem sb_sources_carrierT (D : Dag) (T : Finset (Fin n)) :
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

theorem carrier_flow_union (h : StrictLive n D) (T : Finset (Fin n))
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

theorem carrier_flow_diff (h : StrictLive n D) (x y : Fin n) (hxy : x ≠ y)
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

theorem mem_units {u : Σ _ : ℕ, ℕ} :
    u ∈ units n D ↔ u.1 ∈ inner n D ∧ u.2 + 1 < fanout D u.1 := by
  rw [units, Finset.mem_sigma, Finset.mem_range]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩

theorem sb_card_units_filter (n : ℕ) (D : Dag) (p : ℕ → Prop) [DecidablePred p] :
    ((units n D).filter (fun u => p u.1)).card = surplusOn D ((inner n D).filter p) := by
  have hs : (units n D).filter (fun u => p u.1) =
      ((inner n D).filter p).sigma (fun w => Finset.range (fanout D w - 1)) := by
    ext u; simp only [units, Finset.mem_filter, Finset.mem_sigma]; tauto
  rw [hs, Finset.card_sigma, surplusOn]
  simp

theorem card_units (n : ℕ) (D : Dag) : (units n D).card = totalSurplus n D := by
  rw [units, Finset.card_sigma, totalSurplus, surplusOn]
  simp

theorem card_unitsPlus (n : ℕ) (D : Dag) : (unitsPlus n D).card = Bplus n D := by
  unfold unitsPlus Bplus
  exact sb_card_units_filter n D (fun w => (supp n D w).Nonempty)

theorem card_unitsOn (K : Finset ℕ) (hK : K ⊆ inner n D) :
    (unitsOn n D K).card = surplusOn D K := by
  rw [unitsOn, sb_card_units_filter n D (fun w => w ∈ K), Finset.filter_mem_eq_inter,
    Finset.inter_eq_right.mpr hK]

theorem mem_eligSet {v : Fin n} :
    v ∈ eligSet n D ↔ ∃ w, 2 ≤ fanout D w ∧ v ∈ supp n D w := by
  simp only [eligSet, branchW, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨w, ⟨-, h2⟩, hv⟩; exact ⟨w, h2, hv⟩
  · rintro ⟨w, h2, hv⟩
    refine ⟨w, ⟨?_, h2⟩, hv⟩
    by_contra hc
    rw [supp_ge D w (by omega)] at hv
    exact Finset.notMem_empty v hv

theorem mem_ineligSet {v : Fin n} :
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

theorem sb_singleton_inter_nonempty {v : Fin n} {T : Finset (Fin n)} :
    (({v} : Finset (Fin n)) ∩ T).Nonempty ↔ v ∈ T := by
  constructor
  · rintro ⟨u, hu⟩
    rw [Finset.mem_inter, Finset.mem_singleton] at hu
    exact hu.1 ▸ hu.2
  · intro h
    exact ⟨v, Finset.mem_inter.mpr ⟨Finset.mem_singleton_self v, h⟩⟩

theorem sb_reserved_inj (b : Fin n → ℕ) (hb : PureBranch n D b) :
    Set.InjOn (fun v => (⟨b v, 0⟩ : Σ _ : ℕ, ℕ)) (eligSet n D : Set (Fin n)) := by
  intro v hv v2 hv2 he
  have hbv : b v = b v2 := congrArg Sigma.fst he
  have h1 := (hb v hv).2
  rw [hbv, (hb v2 hv2).2] at h1
  exact (Finset.singleton_injective h1).symm

theorem reserved_subset (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b) :
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

theorem card_reserved (b : Fin n → ℕ) (hb : PureBranch n D b) :
    (reservedUnits n D b).card = (eligSet n D).card :=
  Finset.card_image_of_injOn (sb_reserved_inj b hb)

theorem elig_le_Bplus (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b) :
    (eligSet n D).card ≤ Bplus n D := by
  rw [← card_reserved b hb, ← card_unitsPlus]
  exact Finset.card_le_card (reserved_subset hS b hb)

theorem card_residual (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b) :
    (residualUnits n D b).card + (eligSet n D).card = Bplus n D := by
  rw [← card_reserved b hb, ← card_unitsPlus]
  exact Finset.card_sdiff_add_card_eq_card (reserved_subset hS b hb)

theorem surplus_carrierT_eq (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b)
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

theorem surplus_carrierT_le (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b)
    (T : Finset (Fin n)) :
    surplusOn D (carrierT n D T) + (eligSet n D).card ≤
      (T ∩ eligSet n D).card + Bplus n D := by
  have h1 := surplus_carrierT_eq hS b hb T
  have h2 := card_residual hS b hb
  have h3 := Finset.card_filter_le (residualUnits n D b)
    (fun u => (supp n D u.1 ∩ T).Nonempty)
  omega

end SurplusFlow

def liftP {n : ℕ} (σ : Equiv.Perm (Fin n)) (w : ℕ) : ℕ :=
  if h : w < n then (σ ⟨w, h⟩).val else w

def relabel {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) : Dag :=
  D.map (fun g => (g.1, liftP σ g.2.1, liftP σ g.2.2))

theorem tr_liftP_lt {n : ℕ} (σ : Equiv.Perm (Fin n)) {w : ℕ} (h : w < n) :
    liftP σ w = (σ ⟨w, h⟩).val := by
  simp [liftP, h]

theorem tr_liftP_ge {n : ℕ} (σ : Equiv.Perm (Fin n)) {w : ℕ} (h : n ≤ w) : liftP σ w = w := by
  simp [liftP, Nat.not_lt.mpr h]

theorem tr_liftP_lt_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) {m : ℕ} (hm : n ≤ m) (w : ℕ) :
    liftP σ w < m ↔ w < m := by
  by_cases h : w < n
  · rw [tr_liftP_lt σ h]
    have := (σ ⟨w, h⟩).isLt
    constructor <;> intro <;> omega
  · rw [tr_liftP_ge σ (Nat.not_lt.mp h)]

theorem liftP_inv {n : ℕ} (σ : Equiv.Perm (Fin n)) (w : ℕ) : liftP σ⁻¹ (liftP σ w) = w := by
  by_cases h : w < n
  · rw [tr_liftP_lt σ h, tr_liftP_lt σ⁻¹ (σ ⟨w, h⟩).isLt]; simp
  · rw [tr_liftP_ge σ (Nat.not_lt.mp h), tr_liftP_ge σ⁻¹ (Nat.not_lt.mp h)]

theorem tr_liftP_inv' {n : ℕ} (σ : Equiv.Perm (Fin n)) (w : ℕ) : liftP σ (liftP σ⁻¹ w) = w := by
  simpa using liftP_inv σ⁻¹ w

theorem tr_liftP_inj {n : ℕ} (σ : Equiv.Perm (Fin n)) {a b : ℕ} :
    liftP σ a = liftP σ b ↔ a = b := by
  refine ⟨fun h => ?_, congrArg _⟩
  have := congrArg (liftP σ⁻¹) h
  rwa [liftP_inv, liftP_inv] at this

theorem relabel_length {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) :
    (relabel σ D).length = D.length := by
  simp [relabel]

theorem tr_tag {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (j : ℕ) (hj : j < D.length) :
    tag (relabel σ D) j = tag D j := by
  rw [tag_eq _ j (by rw [relabel_length]; exact hj), tag_eq D j hj]; simp [relabel]

theorem tr_opA {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (j : ℕ) (hj : j < D.length) :
    opA (relabel σ D) j = liftP σ (opA D j) := by
  rw [opA_eq _ j (by rw [relabel_length]; exact hj), opA_eq D j hj]; simp [relabel]

theorem tr_opB {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (j : ℕ) (hj : j < D.length) :
    opB (relabel σ D) j = liftP σ (opB D j) := by
  rw [opB_eq _ j (by rw [relabel_length]; exact hj), opB_eq D j hj]; simp [relabel]

theorem relabel_strict {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) :
    Strict n (relabel σ D) := by
  intro j hj
  rw [relabel_length] at hj
  obtain ⟨ha, hb, hab⟩ := hS j hj
  rw [tr_opA σ D j hj, tr_opB σ D j hj]
  exact ⟨(tr_liftP_lt_iff σ (Nat.le_add_right n j) _).mpr ha,
    (tr_liftP_lt_iff σ (Nat.le_add_right n j) _).mpr hb, fun h => hab ((tr_liftP_inj σ).mp h)⟩

theorem relabel_val {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D)
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

theorem relabel_fanout {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (w : ℕ) :
    fanout (relabel σ D) (liftP σ w) = fanout D w := by
  unfold fanout readers
  rw [relabel_length]
  congr 1
  apply Finset.filter_congr
  intro j hj
  have hj' := Finset.mem_range.mp hj
  rw [tr_opA σ D j hj', tr_opB σ D j hj', tr_liftP_inj, tr_liftP_inj]

theorem relabel_live {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hL : Live n D) :
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

theorem relabel_strictLive {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (h : StrictLive n D) :
    StrictLive n (relabel σ D) :=
  ⟨relabel_strict σ h.1, relabel_live σ h.2.1, by simpa [relabel] using h.2.2⟩

theorem relabel_out {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) (hne : D ≠ [])
    (x : Fin n → Bool) :
    val (relabel σ D) x (outW n (relabel σ D)) = val D (fun i => x (σ i)) (outW n D) := by
  have hpos := List.length_pos_iff.mpr hne
  have e : outW n (relabel σ D) = liftP σ (outW n D) := by
    rw [tr_liftP_ge σ (by unfold outW; omega)]; simp [outW, relabel_length]
  rw [e, relabel_val σ hS]

theorem tr_single_comp {n : ℕ} (σ : Equiv.Perm (Fin n)) (v : Fin n) :
    (fun i => single v (σ i)) = single (σ⁻¹ v) := by
  funext i
  simp only [single, decide_eq_decide]
  constructor
  · intro h; rw [← h]; simp
  · intro h; rw [h]; simp

theorem relabel_supp {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) (w : ℕ) :
    supp n (relabel σ D) (liftP σ w) = (supp n D w).image σ := by
  ext v
  simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  rw [relabel_val σ hS, tr_single_comp]
  constructor
  · intro h; exact ⟨σ⁻¹ v, h, by simp⟩
  · rintro ⟨a, ha, rfl⟩; simpa using ha

theorem tr_sum_liftP {n : ℕ} (σ : Equiv.Perm (Fin n)) {m : ℕ} (hm : n ≤ m) (P : ℕ → Prop)
    [DecidablePred P] (g : ℕ → ℕ) :
    ∑ w ∈ (Finset.range m).filter (fun w => P (liftP σ w)), g (liftP σ w) =
      ∑ w ∈ (Finset.range m).filter P, g w := by
  refine Finset.sum_nbij' (liftP σ) (liftP σ⁻¹) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢
    exact ⟨(tr_liftP_lt_iff σ hm a).mpr ha.1, ha.2⟩
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢
    exact ⟨(tr_liftP_lt_iff σ⁻¹ hm a).mpr ha.1, by rw [tr_liftP_inv']; exact ha.2⟩
  · intro a _; exact liftP_inv σ a
  · intro a _; exact tr_liftP_inv' σ a
  · intro a _; rfl

theorem tr_surplus_filter {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (P Q : ℕ → Prop)
    [DecidablePred P] [DecidablePred Q] (hPQ : ∀ w, Q (liftP σ w) ↔ P w) :
    surplusOn (relabel σ D) ((inner n (relabel σ D)).filter Q) =
      surplusOn D ((inner n D).filter P) := by
  rcases eq_or_ne D [] with rfl | hne
  · simp [surplusOn, relabel, fanout, readers]
  · have hpos := List.length_pos_iff.mpr hne
    have hm : n ≤ n + D.length - 1 := by omega
    unfold surplusOn inner
    rw [relabel_length]
    exact (tr_sum_liftP σ hm Q (fun w => fanout (relabel σ D) w - 1)).symm.trans
      (Finset.sum_congr (Finset.filter_congr fun w _ => hPQ w)
        fun w _ => by rw [relabel_fanout])

theorem relabel_totalSurplus {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) :
    totalSurplus n (relabel σ D) = totalSurplus n D := by
  simpa [totalSurplus] using
    tr_surplus_filter σ D (fun _ => True) (fun _ => True) (fun _ => Iff.rfl)

theorem relabel_Bplus {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) :
    Bplus n (relabel σ D) = Bplus n D :=
  tr_surplus_filter σ D _ _ (fun w => by rw [relabel_supp σ hS]; simp)

theorem relabel_Bzero {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) :
    Bzero n (relabel σ D) = Bzero n D :=
  tr_surplus_filter σ D _ _ (fun w => by rw [relabel_supp σ hS]; simp)

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

theorem relabel_pureBranch {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D)
    (b : Fin n → ℕ) (hb : PureBranch n D b) :
    PureBranch n (relabel σ D) (fun v => liftP σ (b (σ⁻¹ v))) := by
  intro v hv
  rw [relabel_eligSet σ hS, Finset.mem_image] at hv
  obtain ⟨u, hu, rfl⟩ := hv
  obtain ⟨hf, hs⟩ := hb u hu
  have e : σ⁻¹ (σ u) = u := by simp
  show 2 ≤ fanout (relabel σ D) (liftP σ (b (σ⁻¹ (σ u)))) ∧
    supp n (relabel σ D) (liftP σ (b (σ⁻¹ (σ u)))) = {σ u}
  rw [e, relabel_fanout, relabel_supp σ hS, hs, Finset.image_singleton]
  exact ⟨hf, rfl⟩

def edgeList : List (ℕ × ℕ) :=
  [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11),
    (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]

def HeawoodEdge (x : Fin 14 → Bool) : Prop :=
  ∃ u v : Fin 14, (u.val, v.val) ∈ edgeList ∧ x u = true ∧ x v = true

abbrev Adj (u v : Fin 14) : Prop := (u.val, v.val) ∈ edgeList ∨ (v.val, u.val) ∈ edgeList

def inc (p l : Fin 7) : Bool :=
  (([11, 69, 98, 49, 88, 44, 22] : List ℕ).getD l.val 0).testBit p.val

def hc_adjB (u v : Fin 14) : Bool :=
  (([1408, 8832, 12544, 6272, 11264, 5632, 2816, 11, 69, 98, 49, 88, 44, 22] : List ℕ).getD
    u.val 0).testBit v.val

theorem hc_adjB_iff : ∀ u v : Fin 14, hc_adjB u v = true ↔ Adj u v := by decide +kernel

theorem hc_edge_inc : ∀ p l : Fin 7, (p.val, l.val + 7) ∈ edgeList ↔ inc p l = true := by
  decide +kernel

theorem hc_edge_sides : ∀ u v : Fin 14, (u.val, v.val) ∈ edgeList → u.val < 7 ∧ 7 ≤ v.val := by
  decide +kernel

theorem edge_iff_inc (u v : Fin 14) : (u.val, v.val) ∈ edgeList ↔
    ∃ p l : Fin 7, u.val = p.val ∧ v.val = l.val + 7 ∧ inc p l = true := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := hc_edge_sides u v h
    have hv : v.val = v.val - 7 + 7 := by omega
    refine ⟨⟨u.val, h1⟩, ⟨v.val - 7, by omega⟩, rfl, hv, (hc_edge_inc _ _).mp ?_⟩
    rw [← hv]; exact h
  · rintro ⟨p, l, hu, hv, hi⟩
    rw [hu, hv]; exact (hc_edge_inc p l).mpr hi

theorem adj_symm {u v : Fin 14} : Adj u v → Adj v u := Or.symm

theorem adj_irrefl (u : Fin 14) : ¬ Adj u u := by revert u; decide +kernel

theorem heawoodEdge_iff_adj (x : Fin 14 → Bool) :
    HeawoodEdge x ↔ ∃ u v : Fin 14, Adj u v ∧ x u = true ∧ x v = true := by
  constructor
  · rintro ⟨u, v, h, hu, hv⟩; exact ⟨u, v, Or.inl h, hu, hv⟩
  · rintro ⟨u, v, h | h, hu, hv⟩
    · exact ⟨u, v, h, hu, hv⟩
    · exact ⟨v, u, h, hv, hu⟩

theorem degree_three (v : Fin 14) : (Finset.univ.filter (fun u => Adj v u)).card = 3 := by
  rw [Finset.filter_congr (fun u _ => (hc_adjB_iff v u).symm)]
  revert v; decide +kernel

theorem fano_unique_line (p q : Fin 7) (h : p ≠ q) :
    ∃! l : Fin 7, inc p l = true ∧ inc q l = true := by
  revert p q; unfold ExistsUnique; decide +kernel

theorem fano_unique_point (l m : Fin 7) (h : l ≠ m) :
    ∃! p : Fin 7, inc p l = true ∧ inc p m = true := by
  revert l m; unfold ExistsUnique; decide +kernel

theorem common_nbr_le_one (u v : Fin 14) (h : u ≠ v) :
    (Finset.univ.filter (fun z => Adj u z ∧ Adj v z)).card ≤ 1 := by
  rw [Finset.filter_congr (fun z _ => and_congr (hc_adjB_iff u z).symm (hc_adjB_iff v z).symm)]
  revert u v; decide +kernel

theorem hc_nbr_diff : ∀ v w : Fin 14, v ≠ w →
    ∃ z, hc_adjB v z = true ∧ hc_adjB w z = false := by decide +kernel

theorem nbr_diff_exists (v w : Fin 14) (h : v ≠ w) : ∃ z, Adj v z ∧ ¬ Adj w z := by
  obtain ⟨z, h1, h2⟩ := hc_nbr_diff v w h
  refine ⟨z, (hc_adjB_iff v z).mp h1, fun h3 => ?_⟩
  rw [← hc_adjB_iff, h2] at h3
  exact Bool.false_ne_true h3

def IsCover (S : Finset (Fin 14)) : Prop := ∀ u v : Fin 14, Adj u v → u ∈ S ∨ v ∈ S

def IsIndep (I : Finset (Fin 14)) : Prop := ∀ u ∈ I, ∀ v ∈ I, ¬ Adj u v

theorem indep_iff_cover_compl (I : Finset (Fin 14)) : IsIndep I ↔ IsCover (Finset.univ \ I) := by
  constructor
  · intro h u v huv
    by_contra hc
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_or, not_not] at hc
    exact h u hc.1 v hc.2 huv
  · intro h u hu v hv huv
    rcases h u v huv with h1 | h1 <;> simp [hu, hv] at h1

def matching : List (Fin 14 × Fin 14) :=
  [(0, 7), (1, 13), (2, 8), (3, 12), (4, 11), (5, 10), (6, 9)]

def hc_mate (v : Fin 14) : Fin 14 :=
  Fin.ofNat 14 (([7, 13, 8, 12, 11, 10, 9, 0, 2, 6, 5, 4, 3, 1] : List ℕ).getD v.val 0)

theorem hc_match1 : ∀ e ∈ matching, Adj e.1 e.2 := by decide +kernel

theorem hc_match2 : ∀ v : Fin 14, hc_adjB v (hc_mate v) = true ∧ hc_mate (hc_mate v) = v := by
  decide +kernel

theorem hc_match3 : ∀ v : Fin 14, (v, hc_mate v) ∈ matching ∨ (hc_mate v, v) ∈ matching := by
  decide +kernel

theorem matching_adj : (∀ e ∈ matching, Adj e.1 e.2) ∧ ∀ v : Fin 14, Adj v (hc_mate v) ∧
    hc_mate (hc_mate v) = v ∧ ((v, hc_mate v) ∈ matching ∨ (hc_mate v, v) ∈ matching) :=
  ⟨hc_match1, fun v => ⟨(hc_adjB_iff _ _).mp (hc_match2 v).1, (hc_match2 v).2, hc_match3 v⟩⟩

theorem cover_card_ge_seven (S : Finset (Fin 14)) (h : IsCover S) : 7 ≤ S.card := by
  have hsub : (Finset.univ : Finset (Fin 14)) ⊆ S ∪ S.image hc_mate := by
    intro v _
    rcases h v (hc_mate v) (matching_adj.2 v).1 with hv | hv
    · exact Finset.mem_union_left _ hv
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, hv, (matching_adj.2 v).2.1⟩)
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le S (S.image hc_mate)
  have h3 := Finset.card_image_le (s := S) (f := hc_mate)
  simp only [Finset.card_univ, Fintype.card_fin] at h1
  omega

theorem indep_card_le_seven (I : Finset (Fin 14)) (h : IsIndep I) : I.card ≤ 7 := by
  have h1 := cover_card_ge_seven _ ((indep_iff_cover_compl I).mp h)
  rw [Finset.card_univ_sdiff, Fintype.card_fin] at h1
  omega

def IsAut (σ : Equiv.Perm (Fin 14)) : Prop := ∀ u v : Fin 14, Adj (σ u) (σ v) ↔ Adj u v

theorem hc_isAut_of {σ : Equiv.Perm (Fin 14)}
    (h : ∀ u v : Fin 14, hc_adjB (σ u) (σ v) = hc_adjB u v) : IsAut σ := fun u v => by
  rw [← hc_adjB_iff, ← hc_adjB_iff u v, h]

theorem isAut_one : IsAut 1 := fun _ _ => Iff.rfl

theorem isAut_mul {σ τ : Equiv.Perm (Fin 14)} (hσ : IsAut σ) (hτ : IsAut τ) : IsAut (σ * τ) :=
  fun u v => (hσ (τ u) (τ v)).trans (hτ u v)

theorem isAut_inv {σ : Equiv.Perm (Fin 14)} (hσ : IsAut σ) : IsAut σ⁻¹ := fun u v => by
  rw [Equiv.Perm.inv_def]
  have h := hσ (σ.symm u) (σ.symm v)
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
  exact h.symm

theorem heawoodEdge_aut (σ : Equiv.Perm (Fin 14)) (hσ : IsAut σ) (x : Fin 14 → Bool) :
    HeawoodEdge (fun i => x (σ i)) ↔ HeawoodEdge x := by
  rw [heawoodEdge_iff_adj, heawoodEdge_iff_adj]
  constructor
  · rintro ⟨u, v, h, hu, hv⟩; exact ⟨σ u, σ v, (hσ u v).mpr h, hu, hv⟩
  · rintro ⟨u, v, h, hu, hv⟩
    refine ⟨σ.symm u, σ.symm v, ?_, by simpa using hu, by simpa using hv⟩
    rw [← hσ, Equiv.apply_symm_apply, Equiv.apply_symm_apply]; exact h

theorem indep_image_aut {σ : Equiv.Perm (Fin 14)} (hσ : IsAut σ) {I : Finset (Fin 14)}
    (hI : IsIndep I) : IsIndep (I.image σ) := by
  intro u hu v hv
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hv
  rw [hσ a b]; exact hI a ha b hb

def hc_ofList (l : List ℕ) (v : Fin 14) : Fin 14 := Fin.ofNat 14 (l.getD v.val 0)

def dualPerm : Equiv.Perm (Fin 14) :=
  ⟨hc_ofList [13, 8, 7, 12, 10, 11, 9, 2, 1, 6, 4, 5, 3, 0],
    hc_ofList [13, 8, 7, 12, 10, 11, 9, 2, 1, 6, 4, 5, 3, 0],
    by intro x; revert x; decide +kernel, by intro x; revert x; decide +kernel⟩

theorem dualPerm_isAut : IsAut dualPerm := hc_isAut_of (by decide +kernel)

def collPerm : Equiv.Perm (Fin 14) :=
  ⟨hc_ofList [1, 2, 3, 4, 5, 6, 0, 13, 7, 8, 9, 10, 11, 12],
    hc_ofList [6, 0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 13, 7],
    by intro x; revert x; decide +kernel, by intro x; revert x; decide +kernel⟩

theorem collPerm_isAut : IsAut collPerm := hc_isAut_of (by decide +kernel)

def canonI : List (Finset (Fin 14)) :=
  [{0, 1, 2, 3, 4, 5, 6}, {0, 1, 2, 3, 4, 5}, {0, 1, 2, 3, 4}, {0, 1, 2, 5, 11}, {0, 1, 2, 3},
    {0, 1, 2, 5}, {0, 1, 2, 11}, {0, 1, 11, 12}, {0, 1, 2}, {0, 1, 3}, {0, 1, 11}, {0, 1},
    {0, 9}, {0}]

def hc_rep (n : Fin 15) : Finset (Fin 14) := ((∅ : Finset (Fin 14)) :: canonI).getD n.val ∅

theorem hc_rep_of_mem {R : Finset (Fin 14)} (h : R ∈ canonI) :
    ∃ n : Fin 15, n ≠ 0 ∧ hc_rep n = R := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp h
  have hi' : i < 14 := hi
  refine ⟨⟨i + 1, by omega⟩, by simp [Fin.ext_iff], ?_⟩
  show ((∅ : Finset (Fin 14)) :: canonI).getD (i + 1) ∅ = canonI[i]
  rw [List.getD_cons_succ]; exact List.getD_eq_getElem _ _ hi

abbrev hc_ind (I : Finset (Fin 14)) : Prop := ∀ u ∈ I, ∀ v ∈ I, hc_adjB u v = false

theorem hc_ind_iff {I : Finset (Fin 14)} : hc_ind I ↔ IsIndep I := by
  refine forall₂_congr fun u _ => forall₂_congr fun v _ => ?_
  rw [← hc_adjB_iff, Bool.not_eq_true]

theorem hc_rep_ind : ∀ n : Fin 15, hc_ind (hc_rep n) := by decide +kernel

theorem canonI_indep : ∀ R ∈ canonI, IsIndep R := by
  intro R h
  obtain ⟨n, -, rfl⟩ := hc_rep_of_mem h
  exact hc_ind_iff.mp (hc_rep_ind n)

theorem canonI_by_card (R : Finset (Fin 14)) (h : R ∈ canonI) :
    (R.card = 7 ∧ R = {0, 1, 2, 3, 4, 5, 6}) ∨ (R.card = 6 ∧ R = {0, 1, 2, 3, 4, 5}) ∨
    (R.card = 5 ∧ (R = {0, 1, 2, 3, 4} ∨ R = {0, 1, 2, 5, 11})) ∨
    (R.card = 4 ∧ (R = {0, 1, 2, 3} ∨ R = {0, 1, 2, 5} ∨ R = {0, 1, 2, 11} ∨
      R = {0, 1, 11, 12})) ∨
    (R.card = 3 ∧ (R = {0, 1, 2} ∨ R = {0, 1, 3} ∨ R = {0, 1, 11})) ∨
    (R.card = 2 ∧ (R = {0, 1} ∨ R = {0, 9})) ∨ (R.card = 1 ∧ R = {0}) := by
  obtain ⟨n, hn, rfl⟩ := hc_rep_of_mem h
  revert n; decide +kernel

def hc_tab : List (List ℕ) :=
  [[0,1,2,3,4,5,6,7,8,9,10,11,12,13], [1,0,4,3,5,6,2,7,13,8,9,12,11,10],
    [0,3,2,1,5,4,6,7,8,11,10,9,13,12], [0,1,5,3,6,2,4,7,10,13,8,11,12,9],
    [0,2,1,6,4,5,3,8,7,12,10,11,9,13], [0,2,4,6,1,3,5,8,10,12,7,9,11,13],
    [0,2,3,6,5,4,1,8,7,13,10,9,11,12], [1,3,5,0,2,4,6,7,9,11,13,8,10,12],
    [1,2,5,4,3,0,6,13,9,8,7,11,10,12], [1,6,0,5,2,4,3,9,7,11,13,12,10,8],
    [1,6,2,5,0,3,4,9,13,11,7,10,12,8], [11,13,8,10,12,7,9,4,6,1,3,5,0,2],
    [11,13,12,10,8,9,7,4,3,1,6,0,5,2], [11,7,13,12,9,8,10,3,4,0,6,5,2,1],
    [1,2,3,4,5,6,0,13,7,8,9,10,11,12], [2,0,1,6,3,5,4,8,13,10,12,11,9,7],
    [13,8,7,12,10,11,9,2,1,6,4,5,3,0], [8,13,7,12,9,11,10,2,0,4,6,5,3,1],
    [8,13,9,12,7,10,11,2,6,4,0,3,5,1], [8,7,13,10,9,11,12,0,2,3,6,5,4,1]]

def hc_fn (k : Fin 20) : Fin 14 → Fin 14 := hc_ofList (hc_tab.getD k.val [])

theorem hc_fn_inj : ∀ k : Fin 20, ∀ a b : Fin 14, hc_fn k a = hc_fn k b → a = b := by
  decide +kernel

theorem hc_fn_adj : ∀ k : Fin 20, ∀ u v : Fin 14,
    hc_adjB (hc_fn k u) (hc_fn k v) = hc_adjB u v := by decide +kernel

theorem hc_fn_aut (k : Fin 20) : ∃ τ : Equiv.Perm (Fin 14), IsAut τ ∧ ⇑τ = hc_fn k := by
  have hinj : Function.Injective (hc_fn k) := fun a b h => hc_fn_inj k a b h
  exact ⟨Equiv.ofBijective (hc_fn k) ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩,
    hc_isAut_of fun u v => hc_fn_adj k u v, rfl⟩

def hc_witTab : List (List ℕ) :=
  [[0,1,9,7,10,8,14,19,17,13,18,12,11,16], [], [], [0,0,0,0,0,0,1], [], [0,0,0,0,0,2,1],
    [0,0,0,2,5,0,6], [], [], [0,0,0,0,15,0,4], [0,0,0,0,7,3,1], [0,0,0,0,0,3],
    [0,0,0,0,5,3,1,0,0,0,0,0,1], [0,0,9,2,10,0,0,0,0,0,0,12,11,13],
    [0,0,4,2,5,8,6,0,0,0,0,2,4,3]]

def hc_wit (n : Fin 15) (w : Fin 14) : Fin 20 :=
  Fin.ofNat 20 ((hc_witTab.getD n.val []).getD w.val 0)

theorem hc_check : ∀ n : Fin 15, ∀ w : Fin 14, w ∉ hc_rep n →
    hc_ind (insert w (hc_rep n)) →
    (insert w (hc_rep n)).image (hc_fn (hc_wit n w)) ∈ canonI := by decide +kernel

theorem hc_step (R : Finset (Fin 14)) (hR : R = ∅ ∨ R ∈ canonI) (w : Fin 14) (hw : w ∉ R)
    (hI : IsIndep (insert w R)) :
    ∃ τ : Equiv.Perm (Fin 14), IsAut τ ∧ (insert w R).image τ ∈ canonI := by
  obtain ⟨n, rfl⟩ : ∃ n : Fin 15, hc_rep n = R := by
    rcases hR with rfl | hR
    · exact ⟨0, rfl⟩
    · obtain ⟨n, -, h⟩ := hc_rep_of_mem hR; exact ⟨n, h⟩
  obtain ⟨τ, hτ, he⟩ := hc_fn_aut (hc_wit n w)
  exact ⟨τ, hτ, by rw [he]; exact hc_check n w hw (hc_ind_iff.mpr hI)⟩

theorem hc_class (I : Finset (Fin 14)) : IsIndep I →
    I = ∅ ∨ ∃ σ : Equiv.Perm (Fin 14), IsAut σ ∧ I.image σ ∈ canonI := by
  induction I using Finset.induction_on with
  | empty => intro _; exact Or.inl rfl
  | insert v J hv ih =>
    intro hI
    have hJ : IsIndep J := fun u hu w hw =>
      hI u (Finset.mem_insert_of_mem hu) w (Finset.mem_insert_of_mem hw)
    obtain ⟨σ, hσ, R, hR, hJR⟩ : ∃ σ : Equiv.Perm (Fin 14), IsAut σ ∧
        ∃ R, (R = ∅ ∨ R ∈ canonI) ∧ J.image σ = R := by
      rcases ih hJ with h | ⟨σ, hσ, hm⟩
      · exact ⟨1, isAut_one, ∅, Or.inl rfl, by simp [h]⟩
      · exact ⟨σ, hσ, _, Or.inr hm, rfl⟩
    have h1 : (insert v J).image σ = insert (σ v) R := by rw [Finset.image_insert, hJR]
    have h2 : σ v ∉ R := by rw [← hJR]; simpa using hv
    have h3 : IsIndep (insert (σ v) R) := by rw [← h1]; exact indep_image_aut hσ hI
    obtain ⟨τ, hτ, hm⟩ := hc_step R hR (σ v) h2 h3
    refine Or.inr ⟨τ * σ, isAut_mul hτ hσ, ?_⟩
    rw [Equiv.Perm.coe_mul, ← Finset.image_image, h1]; exact hm

theorem indep_classification (I : Finset (Fin 14)) (hI : IsIndep I) (hne : I.Nonempty) :
    ∃ σ : Equiv.Perm (Fin 14), IsAut σ ∧ I.image σ ∈ canonI := by
  rcases hc_class I hI with h | h
  · exact absurd h hne.ne_empty
  · exact h

theorem indep_classification_card (I : Finset (Fin 14)) (hI : IsIndep I) (hne : I.Nonempty) :
    ∃ σ : Equiv.Perm (Fin 14), IsAut σ ∧ I.image σ ∈ canonI ∧ (I.image σ).card = I.card := by
  obtain ⟨σ, hσ, hm⟩ := indep_classification I hI hne
  exact ⟨σ, hσ, hm, Finset.card_image_of_injective _ σ.injective⟩

theorem heawood_not_empty : ¬ HeawoodEdge (fun _ => false) := by
  rintro ⟨u, v, -, h, -⟩; exact Bool.false_ne_true h

theorem heawood_not_single (v : Fin 14) : ¬ HeawoodEdge (fun i => decide (i = v)) := by
  rw [heawoodEdge_iff_adj]
  rintro ⟨a, b, hab, ha, hb⟩
  simp only [decide_eq_true_eq] at ha hb
  subst ha; subst hb; exact adj_irrefl _ hab

theorem heawood_pair_iff (u v : Fin 14) :
    HeawoodEdge (fun i => decide (i = u) || decide (i = v)) ↔ Adj u v := by
  rw [heawoodEdge_iff_adj]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    simp only [Bool.or_eq_true, decide_eq_true_eq] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd hab (adj_irrefl _)
    · exact hab
    · exact adj_symm hab
    · exact absurd hab (adj_irrefl _)
  · intro h; exact ⟨u, v, h, by simp, by simp⟩

theorem heawood_pair {u v : Fin 14} (h : Adj u v) :
    HeawoodEdge (fun i => decide (i = u) || decide (i = v)) := (heawood_pair_iff u v).mpr h

theorem heawood_essential (i : Fin 14) : ∃ x y : Fin 14 → Bool,
    (∀ k, k ≠ i → x k = y k) ∧ ¬ HeawoodEdge x ∧ HeawoodEdge y := by
  refine ⟨fun k => decide (k = hc_mate i), fun k => decide (k = i) || decide (k = hc_mate i),
    ?_, heawood_not_single _, heawood_pair (matching_adj.2 i).1⟩
  intro k hk; simp [hk]

def Correct (D : Dag) : Prop :=
  ∀ x : Fin 14 → Bool, val D x (outW 14 D) = true ↔ HeawoodEdge x

theorem heawood_normalize (C : Circuit) (hmono : Monotone2 C)
    (hC : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ HeawoodEdge x) :
    ∃ D : Dag, StrictLive 14 D ∧ D.length ≤ C.size ∧ Correct D := by
  have h07 : Adj (0 : Fin 14) 7 := by decide
  obtain ⟨D, hD, hlen, hval⟩ := normalize_strictLive (n := 14) C hmono
    (by
      intro b
      cases b
      · exact ⟨_, by rw [Ne, Bool.not_eq_false]; exact (hC _).2 (heawood_pair h07)⟩
      · exact ⟨fun _ => false, fun h => heawood_not_empty ((hC _).1 h)⟩)
    (by
      intro i
      refine ⟨fun k => decide (k = i), fun h => heawood_not_single i ((hC _).1 ?_)⟩
      rw [h]; simp)
    (by
      intro i
      obtain ⟨x, y, hxy, hx, hy⟩ := heawood_essential i
      refine ⟨x, y, hxy, fun h => hx ((hC x).1 ?_)⟩
      rw [h]; exact (hC y).2 hy)
  exact ⟨D, hD, hlen, fun x => by rw [hval x]; exact hC x⟩

theorem heawood_supp_out {D : Dag} (hD : Correct D) : supp 14 D (outW 14 D) = ∅ :=
  Finset.eq_empty_iff_forall_notMem.2
    (fun v hv => heawood_not_single v ((hD _).1 (mem_supp.1 hv)))

theorem heawood_relabel (σ : Equiv.Perm (Fin 14)) (hσ : IsAut σ) {D : Dag}
    (h : StrictLive 14 D) (hD : Correct D) :
    StrictLive 14 (relabel σ D) ∧ Correct (relabel σ D) ∧
      (relabel σ D).length = D.length ∧
      totalSurplus 14 (relabel σ D) = totalSurplus 14 D ∧
      Bplus 14 (relabel σ D) = Bplus 14 D ∧ Bzero 14 (relabel σ D) = Bzero 14 D ∧
      eligSet 14 (relabel σ D) = (eligSet 14 D).image σ ∧
      ineligSet 14 (relabel σ D) = (ineligSet 14 D).image σ := by
  refine ⟨relabel_strictLive σ h, fun x => ?_, relabel_length σ D, relabel_totalSurplus σ D,
    relabel_Bplus σ h.1, relabel_Bzero σ h.1, relabel_eligSet σ h.1, relabel_ineligSet σ h.1⟩
  rw [relabel_out σ h.1 h.2.2 x, hD]
  exact heawoodEdge_aut σ hσ x

theorem inelig_card_add (n : ℕ) (D : Dag) : (ineligSet n D).card + (eligSet n D).card = n := by
  have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (eligSet n D))
  rw [Finset.card_univ, Fintype.card_fin] at h
  exact h

theorem heawood_cover_iff_indep (D : Dag) :
    IsCover (eligSet 14 D) ↔ IsIndep (ineligSet 14 D) := by
  have h : Finset.univ \ ineligSet 14 D = eligSet 14 D := by simp [ineligSet]
  rw [indep_iff_cover_compl, h]

theorem heawood_wlog {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hI : IsIndep (ineligSet 14 D)) (hne : (ineligSet 14 D).Nonempty) :
    ∃ D' : Dag, StrictLive 14 D' ∧ Correct D' ∧ D'.length = D.length ∧
      totalSurplus 14 D' = totalSurplus 14 D ∧ Bplus 14 D' = Bplus 14 D ∧
      Bzero 14 D' = Bzero 14 D ∧ (eligSet 14 D').card = (eligSet 14 D).card ∧
      ineligSet 14 D' ∈ canonI := by
  obtain ⟨σ, hσ, hmem⟩ := indep_classification _ hI hne
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := heawood_relabel σ hσ h hD
  refine ⟨relabel σ D, h1, h2, h3, h4, h5, h6, ?_, ?_⟩
  · rw [h7, Finset.card_image_of_injective _ σ.injective]
  · rw [h8]; exact hmem

theorem heawood_budget {D : Dag} (h : StrictLive 14 D) (hlen : D.length ≤ 26) :
    totalSurplus 14 D + 13 = D.length ∧ totalSurplus 14 D ≤ 13 := by
  have := surplus_identity h
  omega

theorem heawood_p_bounds {D : Dag} (h : StrictLive 14 D) (hlen : D.length ≤ 26)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b) (hcov : IsCover (eligSet 14 D)) :
    7 ≤ (eligSet 14 D).card ∧ (eligSet 14 D).card ≤ Bplus 14 D ∧
      Bplus 14 D ≤ totalSurplus 14 D ∧ totalSurplus 14 D ≤ 13 :=
  ⟨cover_card_ge_seven _ hcov, elig_le_Bplus h.1 b hb, Bplus_le_total 14 D,
    (heawood_budget h hlen).2⟩

theorem heawood_inelig_bounds {D : Dag} (h : StrictLive 14 D) (hlen : D.length ≤ 26)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b) (hcov : IsCover (eligSet 14 D)) :
    (ineligSet 14 D).Nonempty ∧ (ineligSet 14 D).card ≤ 7 := by
  obtain ⟨h7, hp, hB, h13⟩ := heawood_p_bounds h hlen b hb hcov
  have hc := inelig_card_add 14 D
  exact ⟨Finset.card_pos.1 (by omega), by omega⟩

def sem_Edge {n : ℕ} (G : Fin n → Fin n → Prop) (x : Fin n → Bool) : Prop :=
  ∃ u v : Fin n, G u v ∧ x u = true ∧ x v = true

def sem_Comp (n : ℕ) (G : Fin n → Fin n → Prop) (D : Dag) : Prop :=
  ∀ x : Fin n → Bool, val D x (outW n D) = true ↔ sem_Edge G x

def sem_Gr {n : ℕ} (G : Fin n → Fin n → Prop) : Prop :=
  (∀ u v, G u v → G v u) ∧ (∀ u, ¬ G u u) ∧ (∀ v w, v ≠ w → ∃ z, G v z ∧ ¬ G w z) ∧
    (∀ u v, ∃ a, G u a ∧ a ≠ v)

def sem_step (n : ℕ) (D : Dag) (a b : ℕ) : Prop :=
  b < n + D.length ∧ n ≤ b ∧ (opA D (b - n) = a ∨ opB D (b - n) = a)

def sem_two {n : ℕ} (u z : Fin n) : Fin n → Bool := fun i => decide (i = u) || decide (i = z)

def sem_ins {n : ℕ} (v : Fin n) (x : Fin n → Bool) : Fin n → Bool := fun i => decide (i = v) || x i

def sem_ind {n : ℕ} (A : Finset (Fin n)) : Fin n → Bool := fun i => decide (i ∈ A)

theorem sem_rtg_mono {α : Type} {r p : α → α → Prop} (h : ∀ a b, r a b → p a b) {a b : α}
    (hab : Relation.ReflTransGen r a b) : Relation.ReflTransGen p a b := by
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.tail ih (h _ _ hbc)

section SemCore

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

theorem sem_ins_agree (v : Fin n) (x : Fin n → Bool) : ∀ k, k ≠ v → x k = sem_ins v x k := by
  intro k hk; simp [sem_ins, hk]

theorem sem_ins_self (v : Fin n) (x : Fin n → Bool) : sem_ins v x v = true := by simp [sem_ins]

theorem sem_ins_ge (v : Fin n) (x : Fin n → Bool) : ∀ i, x i = true → sem_ins v x i = true := by
  intro i hi; simp [sem_ins, hi]

theorem sem_single_le {x : Fin n → Bool} {u : Fin n} (hu : x u = true) :
    ∀ i, single u i = true → x i = true := by
  intro i hi
  simp only [single, decide_eq_true_eq] at hi
  rw [hi]; exact hu

theorem sem_val_of_supp (hS : Strict n D) {u : Fin n} {w : ℕ} (hu : u ∈ supp n D w)
    {x : Fin n → Bool} (hx : x u = true) : val D x w = true :=
  val_mono hS (single u) x (sem_single_le hx) w (mem_supp.mp hu)

theorem sem_supp_lt {v : Fin n} {w : ℕ} (hv : v ∈ supp n D w) : w < n + D.length := by
  by_contra hc
  rw [supp_ge D w (by omega)] at hv
  exact Finset.notMem_empty v hv

theorem sem_supp_and (hS : Strict n D) {j : ℕ} (hj : j < D.length) (ht : tag D j = true) :
    supp n D (n + j) = supp n D (opA D j) ∩ supp n D (opB D j) := by
  rw [supp_gate hS j hj]; simp [ht]

theorem sem_supp_or (hS : Strict n D) {j : ℕ} (hj : j < D.length) (ht : tag D j = false) :
    supp n D (n + j) = supp n D (opA D j) ∪ supp n D (opB D j) := by
  rw [supp_gate hS j hj]; simp [ht]

theorem sem_supp_and_sub (hS : Strict n D) {j : ℕ} (hj : j < D.length) (ht : tag D j = true)
    (s : Bool) : supp n D (n + j) ⊆ supp n D (src D (j, s)) := by
  rw [sem_supp_and hS hj ht]
  cases s
  · rw [sb_src_false]; exact Finset.inter_subset_left
  · rw [sb_src_true]; exact Finset.inter_subset_right

theorem sem_src_lt (hS : Strict n D) {j : ℕ} (hj : j < D.length) (s : Bool) :
    src D (j, s) < n + j := by
  obtain ⟨ha, hb, -⟩ := hS j hj
  cases s
  · rw [sb_src_false]; exact ha
  · rw [sb_src_true]; exact hb

theorem sem_src_ne (hS : Strict n D) {j : ℕ} (hj : j < D.length) (s : Bool) :
    src D (j, s) ≠ src D (j, !s) := by
  obtain ⟨-, -, hne⟩ := hS j hj
  cases s
  · simpa [src] using hne
  · simpa [src] using hne.symm

theorem sem_step_src {j : ℕ} (hj : j < D.length) (s : Bool) :
    sem_step n D (src D (j, s)) (n + j) := by
  refine ⟨by omega, by omega, ?_⟩
  rw [Nat.add_sub_cancel_left]
  cases s
  · exact Or.inl (sb_src_false j).symm
  · exact Or.inr (sb_src_true j).symm

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

theorem sem_step_reader {a c : ℕ} (h : sem_step n D a c) : c - n ∈ readers D a := by
  unfold readers
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨by have := h.1; have := h.2.1; omega, h.2.2⟩

theorem sem_step_fanout {a c : ℕ} (h : sem_step n D a c) : 1 ≤ fanout D a :=
  Finset.card_pos.mpr ⟨_, sem_step_reader h⟩

theorem sem_step_unique {a c c' : ℕ} (h1 : sem_step n D a c) (h2 : sem_step n D a c')
    (hf : fanout D a = 1) : c = c' := by
  have m1 := sem_step_reader h1
  have m2 := sem_step_reader h2
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp (show (readers D a).card = 1 from hf)
  rw [hr, Finset.mem_singleton] at m1 m2
  have := h1.2.1
  have := h2.2.1
  omega

theorem sem_changed_path (hS : Strict n D) (x y : Fin n → Bool) (v : Fin n)
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

def sem_Dom (n : ℕ) (D : Dag) (b v : ℕ) : Prop :=
  b = v ∨ ¬ Relation.ReflTransGen (fun a c => sem_step n D a c ∧ c ≠ b) v (outW n D)

theorem sem_dom_eq (hS : Strict n D) (x y : Fin n → Bool) (v : Fin n)
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

def sem_Chain (n : ℕ) (D : Dag) (a b : ℕ) : Prop :=
  Relation.ReflTransGen (fun a c => sem_step n D a c ∧ fanout D a = 1) a b

theorem sem_chain_dom (hS : Strict n D) {v b : ℕ} (h : sem_Chain n D v b) :
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

theorem sem_carrier_chain (hS : Strict n D) (v : Fin n) : ∀ w, v ∈ supp n D w →
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

theorem sem_single_no_edge (hG : sem_Gr G) (v : Fin n) : ¬ sem_Edge G (single v) := by
  rintro ⟨a, c, hac, ha, hc⟩
  simp only [single, decide_eq_true_eq] at ha hc
  rw [ha, hc] at hac
  exact hG.2.1 _ hac

theorem sem_two_edge {u v : Fin n} (huv : G u v) : sem_Edge G (sem_two u v) :=
  ⟨u, v, huv, by simp [sem_two], by simp [sem_two]⟩

theorem sem_supp_out (hG : sem_Gr G) (hC : sem_Comp n G D) : supp n D (outW n D) = ∅ :=
  Finset.eq_empty_iff_forall_notMem.2
    (fun v hv => sem_single_no_edge hG v ((hC _).1 (mem_supp.1 hv)))

theorem sem_dom_pure (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) (v : Fin n)
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

theorem sem_first_branch (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) (v : Fin n)
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

def sem_FirstBranch (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Prop :=
  ∀ v ∈ eligSet n D, 2 ≤ fanout D (b v) ∧ supp n D (b v) = {v} ∧ sem_Chain n D v.val (b v)

theorem sem_exists_firstBranch (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) :
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

theorem sem_firstBranch_pure {b : Fin n → ℕ} (hb : sem_FirstBranch n D b) : PureBranch n D b :=
  fun v hv => ⟨(hb v hv).1, (hb v hv).2.1⟩

theorem sem_exists_pureBranch (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) :
    ∃ b : Fin n → ℕ, PureBranch n D b := by
  obtain ⟨b, hb⟩ := sem_exists_firstBranch hG hS hC
  exact ⟨b, sem_firstBranch_pure hb⟩

theorem sem_mem_inelig {v : Fin n} : v ∈ ineligSet n D ↔ v ∉ eligSet n D := by
  simp [ineligSet]

theorem sem_inelig_chain (hS : Strict n D) {v : Fin n} (hv : v ∈ ineligSet n D) {w : ℕ}
    (hw : v ∈ supp n D w) : sem_Chain n D v.val w :=
  sem_carrier_chain hS v w hw (fun u _ hu => mem_ineligSet.mp hv u hu)

theorem sem_inelig_pure (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) {v : Fin n}
    (hv : v ∈ ineligSet n D) {w : ℕ} (hw : v ∈ supp n D w) : supp n D w = {v} :=
  Finset.Subset.antisymm (sem_dom_pure hG hS hC v w (sem_chain_dom hS (sem_inelig_chain hS hv hw)))
    (Finset.singleton_subset_iff.mpr hw)

theorem sem_mem_carrier1 {v : Fin n} {w : ℕ} : w ∈ carrierT n D {v} ↔ v ∈ supp n D w := by
  simp only [carrierT, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨-, u, hu⟩
    rw [Finset.mem_inter, Finset.mem_singleton] at hu
    exact hu.2 ▸ hu.1
  · intro h
    exact ⟨sem_supp_lt h, v, Finset.mem_inter.mpr ⟨h, Finset.mem_singleton_self v⟩⟩

theorem sem_mem_exit1 {v : Fin n} {e : ℕ × Bool} : e ∈ exitArcs n D (carrierT n D {v}) ↔
    e.1 < D.length ∧ v ∈ supp n D (src D e) ∧ v ∉ supp n D (n + e.1) := by
  simp only [exitArcs, arcs, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    Finset.mem_univ, and_true, sem_mem_carrier1]

theorem sem_inelig_surplus {v : Fin n} (hv : v ∈ ineligSet n D) :
    surplusOn D (carrierT n D {v}) = 0 := by
  unfold surplusOn
  refine Finset.sum_eq_zero (fun w hw => ?_)
  have := mem_ineligSet.mp hv w (sem_mem_carrier1.mp hw)
  omega

theorem sem_joint_meeting (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
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

theorem sem_inelig_consumer (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
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

theorem sem_inelig_or (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D) {v : Fin n}
    (hv : v ∈ ineligSet n D) {j : ℕ} (hj : j < D.length) (hc : v ∈ supp n D (n + j)) :
    tag D j = false := by
  obtain ⟨e, -, -, -, -, -, -, hmer⟩ := sem_inelig_consumer hG h hC hv
  by_contra ht
  rw [Bool.not_eq_false] at ht
  have hc2 := hc
  rw [sem_supp_and h.1 hj ht, Finset.mem_inter] at hc2
  have : j ∈ merges n D (carrierT n D {v}) := by
    rw [merges, Finset.mem_filter, Finset.mem_range]
    exact ⟨hj, sem_mem_carrier1.mpr hc, sem_mem_carrier1.mpr hc2.1, sem_mem_carrier1.mpr hc2.2⟩
  rw [hmer] at this
  exact Finset.notMem_empty _ this

theorem sem_elig_cover (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
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

theorem sem_ind_no_edge {A : Finset (Fin n)} (hA : ∀ a ∈ A, ∀ b ∈ A, ¬ G a b) :
    ¬ sem_Edge G (sem_ind A) := by
  rintro ⟨a, c, hac, ha, hc⟩
  simp only [sem_ind, decide_eq_true_eq] at ha hc
  exact hA a ha c hc hac

theorem sem_exposure (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
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

theorem sem_first_mask (hS : Strict n D) (T M : Finset (Fin n)) (hM : 2 ≤ M.card) (w : ℕ)
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

theorem sem_hw_second : ∀ u v : Fin 14, ∃ a, hc_adjB u a = true ∧ a ≠ v := by decide +kernel

theorem sem_heawood_gr : sem_Gr (fun u v : Fin 14 => Adj u v) :=
  ⟨fun _ _ => adj_symm, adj_irrefl, nbr_diff_exists, fun u v => by
    obtain ⟨a, h1, h2⟩ := sem_hw_second u v
    exact ⟨a, (hc_adjB_iff u a).mp h1, h2⟩⟩

theorem sem_heawood_comp {D : Dag} (hD : Correct D) : sem_Comp 14 (fun u v : Fin 14 => Adj u v) D :=
  fun x => (hD x).trans (heawoodEdge_iff_adj x)

theorem exists_pureBranch {D : Dag} (h : StrictLive 14 D) (hD : Correct D) :
    ∃ b : Fin 14 → ℕ, PureBranch 14 D b :=
  sem_exists_pureBranch sem_heawood_gr h.1 (sem_heawood_comp hD)

theorem elig_isCover {D : Dag} (h : StrictLive 14 D) (hD : Correct D) :
    IsCover (eligSet 14 D) :=
  fun _ _ huv => sem_elig_cover sem_heawood_gr h (sem_heawood_comp hD) huv

theorem heawood_wlog_canon (C : Circuit) (hmono : Monotone2 C)
    (hC : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ HeawoodEdge x)
    (hsize : C.size ≤ 26) :
    ∃ D : Dag, StrictLive 14 D ∧ Correct D ∧ D.length ≤ 26 ∧
      totalSurplus 14 D + 13 = D.length ∧ totalSurplus 14 D ≤ 13 ∧
      7 ≤ (eligSet 14 D).card ∧ (eligSet 14 D).card ≤ Bplus 14 D ∧
      Bplus 14 D ≤ totalSurplus 14 D ∧ ineligSet 14 D ∈ canonI := by
  obtain ⟨D0, h0, hlen0, hD0⟩ := heawood_normalize C hmono hC
  have hlen : D0.length ≤ 26 := by omega
  obtain ⟨b, hb⟩ := exists_pureBranch h0 hD0
  have hcov := elig_isCover h0 hD0
  obtain ⟨hne, -⟩ := heawood_inelig_bounds h0 hlen b hb hcov
  obtain ⟨D, h1, h2, h3, h4, h5, -, h7, h8⟩ :=
    heawood_wlog h0 hD0 ((heawood_cover_iff_indep D0).mp hcov) hne
  have hlen' : D.length ≤ 26 := by omega
  obtain ⟨b', hb'⟩ := exists_pureBranch h1 h2
  obtain ⟨p1, p2, p3, p4⟩ := heawood_p_bounds h1 hlen' b' hb' (elig_isCover h1 h2)
  exact ⟨D, h1, h2, hlen', (heawood_budget h1 hlen').1, p4, p1, p2, p3, h8⟩

def sem_W (n : ℕ) (D : Dag) (x : Fin n) : Finset (ℕ × Bool) := exitArcs n D (carrierT n D {x})

def sem_bar (e : ℕ × Bool) : ℕ × Bool := (e.1, !e.2)

section SemCodes

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

theorem sem_mem_W {x : Fin n} {e : ℕ × Bool} : e ∈ sem_W n D x ↔
    e.1 < D.length ∧ x ∈ supp n D (src D e) ∧ x ∉ supp n D (n + e.1) := sem_mem_exit1

theorem sem_bar_bar (e : ℕ × Bool) : sem_bar (sem_bar e) = e := by simp [sem_bar]

theorem sem_bar_ne (e : ℕ × Bool) : sem_bar e ≠ e := by
  intro h
  have h2 := congrArg Prod.snd h
  simp [sem_bar] at h2

theorem sem_same_gate {e f : ℕ × Bool} (h : e.1 = f.1) : f = e ∨ f = sem_bar e := by
  obtain ⟨j, s⟩ := e
  obtain ⟨k, t⟩ := f
  simp only at h
  subst h
  cases s <;> cases t <;> simp [sem_bar]

theorem sem_W_and (hS : Strict n D) {x : Fin n} {e : ℕ × Bool} (he : e ∈ sem_W n D x) :
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

theorem sem_flow1 (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D) (x : Fin n) :
    (sem_W n D x).card + (merges n D (carrierT n D {x})).card =
      1 + surplusOn D (carrierT n D {x}) := by
  have h1 := carrier_flow_union h {x} (by rw [sem_supp_out hG hC]; simp)
  rwa [Finset.card_singleton] at h1

theorem sem_edge_slots (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) {x y : Fin n}
    (hxy : G x y) : ∃ e, e ∈ sem_W n D x ∧ sem_bar e ∈ sem_W n D y ∧
      y ∉ supp n D (src D e) ∧ x ∉ supp n D (src D (sem_bar e)) ∧
      val D (sem_two x y) (n + e.1) = true := by
  obtain ⟨j, hj, -, hval, hju, hjv, s, h1, h2, h3, h4⟩ := sem_joint_meeting hG hS hC hxy
  exact ⟨(j, s), sem_mem_W.mpr ⟨hj, h1, hju⟩, sem_mem_W.mpr ⟨hj, h3, hjv⟩, h2, h4, hval⟩

theorem sem_cover_free (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
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

theorem sem_antichain (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) {x a : Fin n}
    (hxa : x ≠ a) : ∃ e, e ∈ sem_W n D x ∧ a ∉ supp n D (src D e) := by
  obtain ⟨z, hxz, haz⟩ := hG.2.2.1 x a hxa
  obtain ⟨e, he, h1, -⟩ := sem_cover_free hG hS hC (a := a) (b := a) (hG.2.1 a) hxz
    (fun h => haz (hG.1 _ _ h)) (fun h => haz (hG.1 _ _ h))
  exact ⟨e, he, h1⟩

theorem sem_free_empty (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    {u v : Fin n} (huv : G u v) (hu : u ∈ eligSet n D) (hv : v ∈ eligSet n D) :
    ∃ j, j < D.length ∧ tag D j = true ∧ supp n D (n + j) = ∅ ∧
      (supp n D (opA D j)).Nonempty ∧ (supp n D (opB D j)).Nonempty ∧
      val D (sem_two u v) (n + j) = true ∧
      ∀ i ∈ ineligSet n D, i ∉ supp n D (opA D j) ∧ i ∉ supp n D (opB D j) := by
  classical
  have hS := h.1
  have hex : ∃ w, val D (sem_two u v) w = true ∧ supp n D w = ∅ :=
    ⟨outW n D, (hC _).2 (sem_two_edge huv), sem_supp_out hG hC⟩
  obtain ⟨hw1, hw2⟩ := Nat.find_spec hex
  have hmin : ∀ a, a < Nat.find hex → val D (sem_two u v) a = true → (supp n D a).Nonempty := by
    intro a ha hva
    rw [Finset.nonempty_iff_ne_empty]
    exact fun hc => Nat.find_min hex ha ⟨hva, hc⟩
  generalize Nat.find hex = w at hw1 hw2 hmin
  have hlt : w < n + D.length := by
    by_contra hc
    rw [val_ge D _ w (by omega)] at hw1
    exact Bool.false_ne_true hw1
  have hn : n ≤ w := by
    by_contra hc
    have hs : supp n D w = {⟨w, by omega⟩} := supp_input D ⟨w, by omega⟩
    rw [hs] at hw2
    exact Finset.singleton_ne_empty _ hw2
  obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
  have hj : j < D.length := by omega
  obtain ⟨ha, hb, -⟩ := hS j hj
  have hval := hw1
  rw [val_gate hS _ j hj] at hw1
  have hdead : ∀ w', w' < n + j → ∀ i ∈ ineligSet n D, i ∈ supp n D w' →
      val D (sem_two u v) w' = false := by
    intro w'
    induction w' using Nat.strong_induction_on with
    | _ w' ih =>
      intro hlt' i hi hiw
      have hpure := sem_inelig_pure hG hS hC hi hiw
      by_cases hn' : w' < n
      · have hs : supp n D w' = {⟨w', hn'⟩} := supp_input D ⟨w', hn'⟩
        rw [hs, Finset.mem_singleton] at hiw
        rw [val_input D _ w' hn', ← hiw]
        have hiu : i ≠ u := fun hc => (sem_mem_inelig.mp hi) (hc ▸ hu)
        have hiv : i ≠ v := fun hc => (sem_mem_inelig.mp hi) (hc ▸ hv)
        simp [sem_two, hiu, hiv]
      · obtain ⟨j', rfl⟩ : ∃ j', w' = n + j' := ⟨w' - n, by omega⟩
        have hj' : j' < D.length := by omega
        obtain ⟨ha', hb', -⟩ := hS j' hj'
        have ht' := sem_inelig_or hG h hC hi hj' hiw
        have hop : ∀ a, a < n + j' → supp n D a ⊆ {i} → val D (sem_two u v) a = false := by
          intro a hlt2 hsub
          by_cases hia : i ∈ supp n D a
          · exact ih a hlt2 (by omega) i hi hia
          · by_contra hc
            rw [Bool.not_eq_false] at hc
            obtain ⟨q, hq⟩ := hmin a (by omega) hc
            have := hsub hq
            rw [Finset.mem_singleton] at this
            exact hia (this ▸ hq)
        rw [sem_supp_or hS hj' ht'] at hpure
        rw [val_gate hS _ j' hj', ht', gop_false,
          hop _ ha' (by rw [← hpure]; exact Finset.subset_union_left),
          hop _ hb' (by rw [← hpure]; exact Finset.subset_union_right)]
        rfl
  cases ht : tag D j
  · exfalso
    rw [ht] at hw1
    simp only [gop_false, Bool.or_eq_true] at hw1
    rw [sem_supp_or hS hj ht, Finset.union_eq_empty] at hw2
    rcases hw1 with h1 | h1
    · have := hmin _ ha h1
      rw [hw2.1] at this
      exact Finset.not_nonempty_empty this
    · have := hmin _ hb h1
      rw [hw2.2] at this
      exact Finset.not_nonempty_empty this
  · rw [ht] at hw1
    simp only [gop_true, Bool.and_eq_true] at hw1
    refine ⟨j, hj, ht, hw2, hmin _ ha hw1.1, hmin _ hb hw1.2, hval, fun i hi => ⟨?_, ?_⟩⟩
    · intro hc
      have := hdead _ ha i hi hc
      rw [hw1.1] at this
      exact Bool.noConfusion this
    · intro hc
      have := hdead _ hb i hi hc
      rw [hw1.2] at this
      exact Bool.noConfusion this

end SemCodes

theorem sem_hw_third : ∀ x a b : Fin 14, x ≠ a → x ≠ b → hc_adjB a b = false →
    ∃ y, hc_adjB x y = true ∧ hc_adjB y a = false ∧ hc_adjB y b = false := by decide +kernel

theorem sem_hw_two_nbrs : ∀ i x : Fin 14, ∃ r s, r ≠ s ∧ hc_adjB i r = true ∧
    hc_adjB i s = true ∧ r ≠ x ∧ s ≠ x := by decide +kernel

theorem sem_hw_common : ∀ r s t i : Fin 14, r ≠ s → hc_adjB i r = true → hc_adjB i s = true →
    hc_adjB t r = true → hc_adjB t s = true → t = i := by decide +kernel

theorem sem_adjB_false {u v : Fin 14} : hc_adjB u v = false ↔ ¬ Adj u v := by
  rw [← hc_adjB_iff, Bool.not_eq_true]

theorem sem_hw_cover_free {D : Dag} (h : StrictLive 14 D) (hD : Correct D) {x a b : Fin 14}
    (hxa : x ≠ a) (hxb : x ≠ b) (hab : ¬ Adj a b) :
    ∃ e, e ∈ sem_W 14 D x ∧ a ∉ supp 14 D (src D e) ∧ b ∉ supp 14 D (src D e) := by
  obtain ⟨y, h1, h2, h3⟩ := sem_hw_third x a b hxa hxb (sem_adjB_false.mpr hab)
  exact sem_cover_free sem_heawood_gr h.1 (sem_heawood_comp hD) hab ((hc_adjB_iff x y).mp h1)
    (sem_adjB_false.mp h2) (sem_adjB_false.mp h3)

theorem sem_hw_private_slot {D : Dag} (h : StrictLive 14 D) (hD : Correct D) {i x : Fin 14}
    (hi : i ∈ ineligSet 14 D) (hxi : x ≠ i) {e : ℕ × Bool} (he : sem_W 14 D i = {e})
    (hY : sem_bar e ∈ sem_W 14 D x) (hc : (sem_W 14 D x).card ≤ 2) :
    ∃ Z, Z ≠ sem_bar e ∧ sem_W 14 D x = {sem_bar e, Z} ∧ (∀ t, t ≠ x → Z ∉ sem_W 14 D t) ∧
      ∀ i' ∈ ineligSet 14 D, ∀ e', sem_W 14 D i' = {e'} → Z.1 ≠ e'.1 := by
  have hG := sem_heawood_gr
  have hC := sem_heawood_comp hD
  have hS := h.1
  have hcons : ∀ i' ∈ ineligSet 14 D, ∀ e', sem_W 14 D i' = {e'} →
      supp 14 D (src D e') = {i'} ∧ supp 14 D (14 + e'.1) = ∅ ∧
        ∀ q, Adj i' q → q ∈ supp 14 D (src D (sem_bar e')) := by
    intro i' hi' e' he'
    obtain ⟨e0, -, -, hsrc0, hemp0, hnb0, hx0, -⟩ := sem_inelig_consumer hG h hC hi'
    have h1 : ({e'} : Finset (ℕ × Bool)) = {e0} := he'.symm.trans hx0
    have h2 : e' = e0 := Finset.singleton_injective h1
    subst h2
    exact ⟨hsrc0, hemp0, hnb0⟩
  obtain ⟨hsrc, -, hYn⟩ := hcons i hi e he
  obtain ⟨r, s, hrs, hir, his, hrx, hsx⟩ := sem_hw_two_nbrs i x
  rw [hc_adjB_iff] at hir his
  obtain ⟨Z, hZ, hZr⟩ := sem_antichain hG hS hC (x := x) (a := r) (Ne.symm hrx)
  have hZY : Z ≠ sem_bar e := by
    rintro rfl
    exact hZr (hYn r hir)
  have hW : sem_W 14 D x = {sem_bar e, Z} := by
    symm
    refine Finset.eq_of_subset_of_card_le (fun f hf => ?_) ?_
    · rw [Finset.mem_insert, Finset.mem_singleton] at hf
      rcases hf with rfl | rfl
      · exact hY
      · exact hZ
    · rw [Finset.card_pair (Ne.symm hZY)]; exact hc
  have hpriv : ∀ t, t ≠ x → Z ∉ sem_W 14 D t := by
    intro t htx hZt
    have key : ∀ q, q ≠ x → q ∈ supp 14 D (src D (sem_bar e)) → Adj q t := by
      intro q hqx hq
      by_contra hqt
      obtain ⟨f, hf, h1, h2⟩ := sem_hw_cover_free h hD (x := x) (a := q) (b := t)
        (Ne.symm hqx) (Ne.symm htx) hqt
      rw [hW, Finset.mem_insert, Finset.mem_singleton] at hf
      rcases hf with rfl | rfl
      · exact h1 hq
      · exact h2 (sem_mem_W.mp hZt).2.1
    have hrt := adj_symm (key r hrx (hYn r hir))
    have hst := adj_symm (key s hsx (hYn s his))
    have hti : t = i := sem_hw_common r s t i hrs ((hc_adjB_iff _ _).mpr hir)
      ((hc_adjB_iff _ _).mpr his) ((hc_adjB_iff _ _).mpr hrt) ((hc_adjB_iff _ _).mpr hst)
    rw [hti, he, Finset.mem_singleton] at hZt
    have hx2 := (sem_mem_W.mp hZ).2.1
    rw [hZt, hsrc, Finset.mem_singleton] at hx2
    exact hxi hx2
  refine ⟨Z, hZY, hW, hpriv, ?_⟩
  intro i' hi' e' he' hgate
  obtain ⟨-, hemp', hYn'⟩ := hcons i' hi' e' he'
  have hxi' : x ≠ i' := by
    intro hc
    have h1 : (sem_W 14 D x).card = 2 := by rw [hW, Finset.card_pair (Ne.symm hZY)]
    rw [hc, he', Finset.card_singleton] at h1
    omega
  rcases sem_same_gate hgate.symm with h1 | h1
  · exact hpriv i' (Ne.symm hxi') (by rw [he', Finset.mem_singleton]; exact h1)
  · obtain ⟨r', s', hrs', hir', his', hrx', -⟩ := sem_hw_two_nbrs i' x
    rw [hc_adjB_iff] at hir'
    refine hpriv r' hrx' (sem_mem_W.mpr ⟨(sem_mem_W.mp hZ).1, ?_, ?_⟩)
    · rw [h1]; exact hYn' r' hir'
    · rw [hgate, hemp']; exact Finset.notMem_empty _

theorem sem_rtg_comparable {α : Type} {R : α → α → Prop}
    (hfun : ∀ a a' b, R a b → R a' b → a = a') {u v c : α}
    (hu : Relation.ReflTransGen R u c) (hv : Relation.ReflTransGen R v c) :
    Relation.ReflTransGen R u v ∨ Relation.ReflTransGen R v u := by
  induction hu with
  | refl => exact Or.inr hv
  | tail hab hbc ih =>
    rcases Relation.ReflTransGen.cases_tail hv with h | ⟨b', hvb', hb'c⟩
    · left
      rw [← h]
      exact Relation.ReflTransGen.tail hab hbc
    · have hbb : b' = _ := hfun _ _ _ hb'c hbc
      rw [hbb] at hvb'
      exact ih hvb'

def sem_MinBranch (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Prop :=
  ∀ v ∈ eligSet n D, 2 ≤ fanout D (b v) ∧ supp n D (b v) = {v} ∧ sem_Chain n D v.val (b v) ∧
    ∀ w, 2 ≤ fanout D w → v ∈ supp n D w → b v ≤ w

def sem_Arm (n : ℕ) (D : Dag) (X : Finset (Fin n)) (a b : ℕ) : Prop :=
  sem_step n D a b ∧ fanout D a = 1 ∧ ∀ x ∈ X, x ∈ supp n D a ∧ x ∈ supp n D b

section SemArms

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

theorem sem_rtg_le (hS : Strict n D) {R : ℕ → ℕ → Prop} (hR : ∀ a b, R a b → sem_step n D a b)
    {a b : ℕ} (h : Relation.ReflTransGen R a b) : a ≤ b := by
  induction h with
  | refl => exact le_refl _
  | tail _ hbc ih => exact le_trans ih (le_of_lt (sem_step_lt hS (hR _ _ hbc)))

theorem sem_exists_minBranch (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) :
    ∃ b : Fin n → ℕ, sem_MinBranch n D b := by
  classical
  have h : ∀ v : Fin n, ∃ b, v ∈ eligSet n D →
      2 ≤ fanout D b ∧ supp n D b = {v} ∧ sem_Chain n D v.val b ∧
        ∀ w, 2 ≤ fanout D w → v ∈ supp n D w → b ≤ w := by
    intro v
    by_cases hv : v ∈ eligSet n D
    · have hex : ∃ w, 2 ≤ fanout D w ∧ v ∈ supp n D w := mem_eligSet.mp hv
      obtain ⟨h1, h2⟩ := Nat.find_spec hex
      have hch : sem_Chain n D v.val (Nat.find hex) :=
        sem_carrier_chain hS v _ h2 (fun u hu huv => by
          have := Nat.find_min hex hu
          by_contra hc
          exact this ⟨by omega, huv⟩)
      exact ⟨Nat.find hex, fun _ => ⟨h1, Finset.Subset.antisymm
        (sem_dom_pure hG hS hC v _ (sem_chain_dom hS hch)) (Finset.singleton_subset_iff.mpr h2),
        hch, fun w hw1 hw2 => Nat.find_min' hex ⟨hw1, hw2⟩⟩⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose b hb using h
  exact ⟨b, fun v hv => hb v hv⟩

theorem sem_minBranch_first {b : Fin n → ℕ} (hb : sem_MinBranch n D b) : sem_FirstBranch n D b :=
  fun v hv => ⟨(hb v hv).1, (hb v hv).2.1, (hb v hv).2.2.1⟩

theorem sem_minBranch_pure {b : Fin n → ℕ} (hb : sem_MinBranch n D b) : PureBranch n D b :=
  fun v hv => ⟨(hb v hv).1, (hb v hv).2.1⟩

theorem sem_zm_gate (hS : Strict n D) {x : Fin n} (hM : merges n D (carrierT n D {x}) = ∅)
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

theorem sem_code_count (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
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

theorem sem_descent (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (X : Finset (Fin n)) (hX : X.Nonempty)
    (hM : ∀ x ∈ X, merges n D (carrierT n D {x}) = ∅) :
    ∀ c, (∀ x ∈ X, x ∈ supp n D c) →
      (∀ x ∈ X, ∀ w, c ≤ w → x ∈ supp n D w → fanout D w ≤ 1) →
      ∃ e : ℕ × Bool, (∀ x ∈ X, e ∈ sem_W n D x) ∧
        Relation.ReflTransGen (sem_Arm n D X) c (src D e) := by
  classical
  have hS := h.1
  obtain ⟨x0, hx0⟩ := hX
  intro c
  generalize hk : n + D.length - c = k
  induction k using Nat.strong_induction_on generalizing c with
  | _ k ih =>
    intro hc hlow
    have hclt := sem_supp_lt (hc x0 hx0)
    have hcne : c ≠ outW n D := by
      intro he
      have := hc x0 hx0
      rw [he, sem_supp_out hG hC] at this
      exact Finset.notMem_empty _ this
    have hf1 : 1 ≤ fanout D c := h.2.1 c (by unfold outW at hcne; omega)
    have hf : fanout D c = 1 := le_antisymm (hlow x0 hx0 c (le_refl c) (hc x0 hx0)) hf1
    obtain ⟨j, hjr⟩ := Finset.card_pos.mp hf1
    simp only [readers, Finset.mem_filter, Finset.mem_range] at hjr
    obtain ⟨hj, hop⟩ := hjr
    obtain ⟨s, hs⟩ : ∃ s : Bool, src D (j, s) = c := by
      rcases hop with h1 | h1
      · exact ⟨false, by rw [sb_src_false]; exact h1⟩
      · exact ⟨true, by rw [sb_src_true]; exact h1⟩
    have hcj : c < n + j := hs ▸ sem_src_lt hS hj s
    by_cases hcar : ∃ x1 ∈ X, x1 ∈ supp n D (n + j)
    · obtain ⟨x1, hx1, hx1c⟩ := hcar
      have ht := (sem_zm_gate hS (hM x1 hx1) hj hx1c).1
      have hall : ∀ x ∈ X, x ∈ supp n D (n + j) := by
        intro x hx
        rw [sem_supp_or hS hj ht, Finset.mem_union]
        rcases hop with h1 | h1
        · left; rw [h1]; exact hc x hx
        · right; rw [h1]; exact hc x hx
      obtain ⟨e, he1, he2⟩ := ih (n + D.length - (n + j)) (by omega) (n + j) rfl hall
        (fun x hx w hw => hlow x hx w (by omega))
      refine ⟨e, he1, Relation.ReflTransGen.head ⟨?_, hf, fun x hx => ⟨hc x hx, hall x hx⟩⟩ he2⟩
      rw [← hs]
      exact sem_step_src hj s
    · refine ⟨(j, s), fun x hx => sem_mem_W.mpr ⟨hj, ?_, fun hc2 => hcar ⟨x, hx, hc2⟩⟩, ?_⟩
      · rw [hs]; exact hc x hx
      · rw [hs]

theorem sem_two_arms (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (X : Finset (Fin n)) (hX : X.Nonempty)
    (hM : ∀ x ∈ X, merges n D (carrierT n D {x}) = ∅) (r : ℕ)
    (hr : ∀ x ∈ X, x ∈ supp n D r) (hf : 2 ≤ fanout D r)
    (hlow : ∀ x ∈ X, ∀ w, r < w → x ∈ supp n D w → fanout D w ≤ 1) :
    ∃ P Q : ℕ × Bool, P.1 ≠ Q.1 ∧ ∀ x ∈ X, P ∈ sem_W n D x ∧ Q ∈ sem_W n D x := by
  classical
  have hS := h.1
  obtain ⟨x0, hx0⟩ := hX
  obtain ⟨j1, hj1, j2, hj2, hne⟩ := Finset.one_lt_card.mp (show 1 < (readers D r).card from hf)
  have hread : ∀ j ∈ readers D r, j < D.length ∧ r < n + j ∧ (opA D j = r ∨ opB D j = r) := by
    intro j hj
    simp only [readers, Finset.mem_filter, Finset.mem_range] at hj
    have := hS j hj.1
    exact ⟨hj.1, by omega, hj.2⟩
  have hterm : ∀ j ∈ readers D r, ∃ e : ℕ × Bool, (∀ x ∈ X, e ∈ sem_W n D x) ∧
      ((e.1 = j ∧ src D e = r) ∨ Relation.ReflTransGen (sem_Arm n D X) (n + j) (src D e)) := by
    intro j hj
    obtain ⟨hjl, hrj, hop⟩ := hread j hj
    obtain ⟨s, hs⟩ : ∃ s : Bool, src D (j, s) = r := by
      rcases hop with h1 | h1
      · exact ⟨false, by rw [sb_src_false]; exact h1⟩
      · exact ⟨true, by rw [sb_src_true]; exact h1⟩
    by_cases hcar : ∃ x1 ∈ X, x1 ∈ supp n D (n + j)
    · obtain ⟨x1, hx1, hx1c⟩ := hcar
      have ht := (sem_zm_gate hS (hM x1 hx1) hjl hx1c).1
      have hall : ∀ x ∈ X, x ∈ supp n D (n + j) := by
        intro x hx
        rw [sem_supp_or hS hjl ht, Finset.mem_union]
        rcases hop with h1 | h1
        · left; rw [h1]; exact hr x hx
        · right; rw [h1]; exact hr x hx
      obtain ⟨e, he1, he2⟩ := sem_descent hG h hC X ⟨x0, hx0⟩ hM (n + j) hall
        (fun x hx w hw => hlow x hx w (by omega))
      exact ⟨e, he1, Or.inr he2⟩
    · exact ⟨(j, s), fun x hx => sem_mem_W.mpr ⟨hjl, by rw [hs]; exact hr x hx,
        fun hc2 => hcar ⟨x, hx, hc2⟩⟩, Or.inl ⟨rfl, hs⟩⟩
  have hRstep : ∀ a b, sem_Arm n D X a b → sem_step n D a b := fun _ _ hab => hab.1
  have hfun : ∀ a a' b, sem_Arm n D X a b → sem_Arm n D X a' b → a = a' := by
    intro a a' b h1 h2
    by_contra hne2
    obtain ⟨hb1, hb2, hba⟩ := h1.1
    obtain ⟨-, -, hba'⟩ := h2.1
    have hjb : b - n < D.length := by omega
    have hcarb : x0 ∈ supp n D (n + (b - n)) := by
      rw [Nat.add_sub_cancel' hb2]; exact (h1.2.2 x0 hx0).2
    apply (sem_zm_gate hS (hM x0 hx0) hjb hcarb).2
    have ha := (h1.2.2 x0 hx0).1
    have ha' := (h2.2.2 x0 hx0).1
    rcases hba with e1 | e1 <;> rcases hba' with e2 | e2
    · exact absurd (e1.symm.trans e2) hne2
    · rw [e1, e2]; exact ⟨ha, ha'⟩
    · rw [e1, e2]; exact ⟨ha', ha⟩
    · exact absurd (e1.symm.trans e2) hne2
  have hcross : ∀ ja ∈ readers D r, ∀ jb ∈ readers D r, ja ≠ jb →
      ¬ Relation.ReflTransGen (sem_Arm n D X) (n + ja) (n + jb) := by
    intro ja hja jb hjb hab hp
    obtain ⟨hjla, hrja, -⟩ := hread ja hja
    obtain ⟨hjlb, hrjb, hopb⟩ := hread jb hjb
    rcases Relation.ReflTransGen.cases_tail hp with heq | ⟨u, hu1, hu2⟩
    · exact hab (by omega)
    · have hle := sem_rtg_le hS hRstep hu1
      have hur : u = r := by
        by_contra hur
        obtain ⟨-, -, hbu⟩ := hu2.1
        rw [Nat.add_sub_cancel_left] at hbu
        apply (sem_zm_gate hS (hM x0 hx0) hjlb (hu2.2.2 x0 hx0).2).2
        have hu := (hu2.2.2 x0 hx0).1
        have hrr := hr x0 hx0
        rcases hbu with e1 | e1 <;> rcases hopb with e2 | e2
        · exact absurd (e1.symm.trans e2) hur
        · rw [e1, e2]; exact ⟨hu, hrr⟩
        · rw [e1, e2]; exact ⟨hrr, hu⟩
        · exact absurd (e1.symm.trans e2) hur
      omega
  obtain ⟨P, hP1, hP2⟩ := hterm j1 hj1
  obtain ⟨Q, hQ1, hQ2⟩ := hterm j2 hj2
  refine ⟨P, Q, fun hPQ => ?_, fun x hx => ⟨hP1 x hx, hQ1 x hx⟩⟩
  have hsame : Q = P := by
    rcases sem_same_gate hPQ with h1 | h1
    · exact h1
    · exfalso
      obtain ⟨hjP, hxP, hnP⟩ := sem_mem_W.mp (hP1 x0 hx0)
      have hxQ := (sem_mem_W.mp (hQ1 x0 hx0)).2.1
      rw [h1] at hxQ
      apply hnP
      rw [sem_supp_and hS hjP (sem_W_and hS (hP1 x0 hx0)), Finset.mem_inter]
      obtain ⟨j, s⟩ := P
      cases s
      · exact ⟨by simpa [src] using hxP, by simpa [src, sem_bar] using hxQ⟩
      · exact ⟨by simpa [src, sem_bar] using hxQ, by simpa [src] using hxP⟩
  rw [hsame] at hQ2
  obtain ⟨-, hrj1, -⟩ := hread j1 hj1
  obtain ⟨-, hrj2, -⟩ := hread j2 hj2
  rcases hP2 with ⟨hPa, hPb⟩ | hPp <;> rcases hQ2 with ⟨hQa, hQb⟩ | hQp
  · exact hne (hPa.symm.trans hQa)
  · have := sem_rtg_le hS hRstep hQp
    omega
  · have := sem_rtg_le hS hRstep hPp
    omega
  · rcases sem_rtg_comparable hfun hPp hQp with h1 | h1
    · exact hcross j1 hj1 j2 hj2 hne h1
    · exact hcross j2 hj2 j1 hj1 (Ne.symm hne) h1

theorem sem_saturated (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (b : Fin n → ℕ) (hb : PureBranch n D b) {u0 : Σ _ : ℕ, ℕ}
    (hres : residualUnits n D b = {u0}) {x : Fin n} (hsat : 3 ≤ (sem_W n D x).card) :
    (sem_W n D x).card = 3 ∧ merges n D (carrierT n D {x}) = ∅ ∧ x ∈ eligSet n D ∧
      x ∈ supp n D u0.1 := by
  have h1 := sem_code_count hG h hC b hb x
  have h2 : (({x} : Finset (Fin n)) ∩ eligSet n D).card ≤ 1 :=
    (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
  have h3 := Finset.card_filter_le (residualUnits n D b) (fun u => x ∈ supp n D u.1)
  rw [hres, Finset.card_singleton] at h3
  rw [hres] at h1
  refine ⟨by omega, Finset.card_eq_zero.mp (by omega), ?_, ?_⟩
  · by_contra hx
    have h4 : ({x} : Finset (Fin n)) ∩ eligSet n D = ∅ := by
      rw [Finset.singleton_inter_of_notMem hx]
    rw [h4, Finset.card_empty] at h1
    omega
  · have h4 : 0 < (({u0} : Finset (Σ _ : ℕ, ℕ)).filter (fun u => x ∈ supp n D u.1)).card := by
      omega
    obtain ⟨u, hu⟩ := Finset.card_pos.mp h4
    rw [Finset.mem_filter, Finset.mem_singleton] at hu
    exact hu.1 ▸ hu.2

theorem sem_common_terminals (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (b : Fin n → ℕ) (hb : sem_MinBranch n D b) (hone : Bplus n D = (eligSet n D).card + 1)
    (X : Finset (Fin n)) (hX : X.Nonempty) (hsat : ∀ x ∈ X, 3 ≤ (sem_W n D x).card) :
    ∃ P Q : ℕ × Bool, P.1 ≠ Q.1 ∧ ∀ x ∈ X, P ∈ sem_W n D x ∧ Q ∈ sem_W n D x := by
  have hS := h.1
  have hbp := sem_minBranch_pure hb
  have hcard : (residualUnits n D b).card = 1 := by
    have := card_residual hS b hbp
    omega
  obtain ⟨u0, hres⟩ := Finset.card_eq_one.mp hcard
  have hu0 : u0 ∈ residualUnits n D b := by rw [hres]; exact Finset.mem_singleton_self _
  have hu0u : u0 ∈ units n D :=
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp hu0).1).1
  have hfr : 2 ≤ fanout D u0.1 := by
    have := (mem_units.mp hu0u).2
    omega
  refine sem_two_arms hG h hC X hX (fun x hx => (sem_saturated hG h hC b hbp hres (hsat x hx)).2.1)
    u0.1 (fun x hx => (sem_saturated hG h hC b hbp hres (hsat x hx)).2.2.2) hfr ?_
  intro x hx w hrw hxw
  obtain ⟨-, -, hxe, hxr⟩ := sem_saturated hG h hC b hbp hres (hsat x hx)
  by_contra hc
  have hw2 : 2 ≤ fanout D w := by omega
  have hwu : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ unitsPlus n D := by
    rw [unitsPlus, Finset.mem_filter, mem_units]
    exact ⟨⟨sb_mem_inner.mpr (lt_of_fanout_pos hS (w := w) (by omega)), by show 0 + 1 < fanout D w; omega⟩,
      ⟨x, hxw⟩⟩
  by_cases hwr : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ reservedUnits n D b
  · obtain ⟨v, hv, hveq⟩ := Finset.mem_image.mp hwr
    have hbv : b v = w := congrArg Sigma.fst hveq
    have hsv := (hb v hv).2.1
    rw [hbv] at hsv
    rw [hsv, Finset.mem_singleton] at hxw
    have hmin := (hb x hxe).2.2.2 u0.1 hfr hxr
    rw [hxw, hbv] at hmin
    omega
  · have hwres : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ residualUnits n D b :=
      Finset.mem_sdiff.mpr ⟨hwu, hwr⟩
    rw [hres, Finset.mem_singleton] at hwres
    have : w = u0.1 := congrArg Sigma.fst hwres
    omega

end SemArms

theorem sem_all_but_one {α : Type} (J : Finset α) (P : α → Prop)
    (h : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → P i ∨ P j) :
    ∃ J' ⊆ J, J.card ≤ J'.card + 1 ∧ ∀ i ∈ J', P i := by
  classical
  refine ⟨J.filter P, Finset.filter_subset _ _, ?_, fun i hi => (Finset.mem_filter.mp hi).2⟩
  have h1 : (J.filter (fun i => ¬ P i)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    by_contra hab
    rcases h a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1 hab with h1 | h1
    · exact (Finset.mem_filter.mp ha).2 h1
    · exact (Finset.mem_filter.mp hb).2 h1
  have h2 := Finset.card_filter_add_card_filter_not (s := J) P
  omega

section SemPaths

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

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

theorem sem_inelig_reach (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    {i : Fin n} (hi : i ∈ ineligSet n D) :
    sem_Chain n D i.val (outW n D) ∨
      ∃ b, sem_Chain n D i.val b ∧ 2 ≤ fanout D b ∧ supp n D b = ∅ := by
  have hlt : i.val < n + D.length := by have := i.isLt; omega
  have hp : Relation.ReflTransGen (sem_step n D) i.val (outW n D) := live_reaches_out h i.val hlt
  rcases sem_path_chain hp with h1 | ⟨b, h1, h2⟩
  · exact Or.inl h1
  · exact Or.inr ⟨b, h1, h2, sem_branch_empty hG h.1 hC hi h1 h2⟩

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

theorem sem_full_support (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    {i : Fin n} (hi : i ∈ ineligSet n D) {e : ℕ × Bool} (he : sem_W n D i = {e})
    (hor : ∀ j, Relation.ReflTransGen (sem_step n D) (n + e.1) (n + j) → j ≠ e.1 →
      tag D j = false) :
    ∀ t, t ∈ supp n D (src D (sem_bar e)) ↔ G i t := by
  have hS := h.1
  obtain ⟨e0, hj0, ht0, hsrc0, hemp0, hnb0, hx0, -⟩ := sem_inelig_consumer hG h hC hi
  have hee : e = e0 := Finset.singleton_injective (he.symm.trans hx0)
  subst hee
  obtain ⟨g, s⟩ := e
  intro t
  refine ⟨fun ht => ?_, fun ht => hnb0 t ht⟩
  by_contra hnt
  have hgate : val D (sem_two i t) (n + g) = true := by
    rw [sem_val_gate_src hS _ hj0 s, ht0, gop_true, Bool.and_eq_true]
    exact ⟨sem_val_of_supp hS (by rw [hsrc0]; exact Finset.mem_singleton_self i)
      (by simp [sem_two]), sem_val_of_supp hS ht (by simp [sem_two])⟩
  have hall : ∀ c, Relation.ReflTransGen (sem_step n D) (n + g) c →
      val D (sem_two i t) c = true := by
    intro c hc
    induction hc with
    | refl => exact hgate
    | tail hab hbc ih =>
      obtain ⟨j, s', hj, rfl, rfl⟩ := sem_step_iff.mp hbc
      have hne : j ≠ g := by
        have := sem_rtg_le hS (fun _ _ h => h) hab
        have := sem_src_lt hS hj s'
        omega
      rw [sem_val_gate_src hS _ hj s', hor j (Relation.ReflTransGen.tail hab hbc) hne,
        gop_false, ih]
      rfl
  have hout := hall _ (live_reaches_out h (n + g) (by omega))
  obtain ⟨u, v, huv, hu, hv⟩ := (hC _).mp hout
  simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at hu hv
  rcases hu with hu | hu <;> rcases hv with hv | hv <;> rw [hu, hv] at huv
  · exact hG.2.1 _ huv
  · exact hnt huv
  · exact hnt (hG.1 _ _ huv)
  · exact hG.2.1 _ huv

end SemPaths

def sem_hw_opp (i : Fin 14) : Finset (Fin 14) :=
  Finset.univ.filter (fun a => decide (a.val < 7) ≠ decide (i.val < 7))

def sem_hw_nb (i : Fin 14) : Finset (Fin 14) := Finset.univ.filter (fun a => Adj i a)

theorem sem_hw_sides : ∀ a b : Fin 14, hc_adjB a b = true →
    decide (a.val < 7) ≠ decide (b.val < 7) := by decide +kernel

theorem sem_hw_opp_indep (i : Fin 14) : ∀ a ∈ sem_hw_opp i, ∀ b ∈ sem_hw_opp i, ¬ Adj a b := by
  intro a ha b hb hab
  simp only [sem_hw_opp, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  have h1 := sem_hw_sides a b ((hc_adjB_iff a b).mpr hab)
  cases h2 : decide (a.val < 7) <;> cases h3 : decide (b.val < 7) <;>
    cases h4 : decide (i.val < 7) <;> simp_all

theorem sem_hw_nb_opp {i a : Fin 14} (h : Adj i a) : a ∈ sem_hw_opp i := by
  simp only [sem_hw_opp, Finset.mem_filter, Finset.mem_univ, true_and]
  exact (sem_hw_sides i a ((hc_adjB_iff i a).mpr h)).symm

theorem sem_hw_mask {D : Dag} {i : Fin 14} {q : ℕ}
    (h : ∀ a ∈ sem_hw_opp i, (a ∈ supp 14 D q ↔ Adj i a)) :
    supp 14 D q ∩ sem_hw_opp i = sem_hw_nb i := by
  ext a
  simp only [Finset.mem_inter, sem_hw_nb, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩; exact (h a h2).mp h1
  · intro h1; exact ⟨(h a (sem_hw_nb_opp h1)).mpr h1, sem_hw_nb_opp h1⟩

theorem sem_hw_exact_nbhd {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hB0 : Bzero 14 D = 0) {i : Fin 14} (hi : i ∈ ineligSet 14 D) :
    ∃ j s, j < D.length ∧ tag D j = true ∧ sem_Chain 14 D i.val (src D (j, !s)) ∧
      supp 14 D (src D (j, s)) ∩ sem_hw_opp i = sem_hw_nb i := by
  obtain ⟨j, s, hj, ht, hc, hsupp⟩ := sem_exact_nbhd sem_heawood_gr h.1 (sem_heawood_comp hD)
    (sem_hw_opp i) (sem_hw_opp_indep i)
    (sem_noempty_chain_out sem_heawood_gr h (sem_heawood_comp hD) hB0 hi)
  exact ⟨j, s, hj, ht, hc, sem_hw_mask hsupp⟩

theorem sem_hw_shared_empty {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hB0 : Bzero 14 D ≤ 1) {i j : Fin 14} (hi : i ∈ ineligSet 14 D) (hj : j ∈ ineligSet 14 D)
    (hij : i ≠ j) (hside : decide (i.val < 7) = decide (j.val < 7)) :
    (∃ k s, k < D.length ∧ tag D k = true ∧ sem_Chain 14 D i.val (src D (k, !s)) ∧
        supp 14 D (src D (k, s)) ∩ sem_hw_opp i = sem_hw_nb i) ∨
      (∃ k s, k < D.length ∧ tag D k = true ∧ sem_Chain 14 D j.val (src D (k, !s)) ∧
        supp 14 D (src D (k, s)) ∩ sem_hw_opp j = sem_hw_nb j) := by
  have hopp : sem_hw_opp j = sem_hw_opp i := by unfold sem_hw_opp; rw [hside]
  obtain ⟨a, hja, hia⟩ := nbr_diff_exists j i (Ne.symm hij)
  rcases sem_shared_empty sem_heawood_gr h (sem_heawood_comp hD) hB0 (sem_hw_opp i)
    (sem_hw_opp_indep i) hi hj ⟨a, hopp ▸ sem_hw_nb_opp hja, hja, hia⟩ with
    ⟨k, s, hk, ht, hc, hsupp⟩ | ⟨k, s, hk, ht, hc, hsupp⟩
  · exact Or.inl ⟨k, s, hk, ht, hc, sem_hw_mask hsupp⟩
  · exact Or.inr ⟨k, s, hk, ht, hc,
      sem_hw_mask (fun a ha => hsupp a (by rw [← hopp]; exact ha))⟩

section SemDiff

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

theorem sem_mem_diff {x y : Fin n} {w : ℕ} :
    w ∈ carrierDiff n D x y ↔ x ∈ supp n D w ∧ y ∉ supp n D w := by
  simp only [carrierDiff, Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨sem_supp_lt h.1, h⟩⟩

theorem sem_mem_exit_diff {x y : Fin n} {e : ℕ × Bool} :
    e ∈ exitArcs n D (carrierDiff n D x y) ↔ e.1 < D.length ∧
      (x ∈ supp n D (src D e) ∧ y ∉ supp n D (src D e)) ∧
      ¬ (x ∈ supp n D (n + e.1) ∧ y ∉ supp n D (n + e.1)) := by
  simp only [exitArcs, arcs, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    Finset.mem_univ, and_true, sem_mem_diff]

theorem sem_surplus_diff (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b)
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

theorem sem_first_joint (hS : Strict n D) {x y : Fin n} (hxy : x ≠ y) {w : ℕ}
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

theorem sem_diff_two_exits (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
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

theorem sem_and_sibling_nbrs (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {i : Fin n} {j : ℕ} (hj : j < D.length) (s : Bool) (ht : tag D j = true)
    (hch : sem_Chain n D i.val (src D (j, !s))) (hf : fanout D (src D (j, !s)) = 1)
    (hout : n + j ≤ outW n D) {a : Fin n} (hia : G i a) : a ∈ supp n D (src D (j, s)) := by
  have hchg : sem_Chain n D i.val (n + j) :=
    Relation.ReflTransGen.tail hch ⟨sem_step_src hj (!s), hf⟩
  have hx0 : val D (single a) (outW n D) = false := by
    by_contra hc
    rw [Bool.not_eq_false] at hc
    exact sem_single_no_edge hG a ((hC _).mp hc)
  have hy1 : val D (sem_ins i (single a)) (outW n D) = true :=
    (hC _).mpr ⟨i, a, hia, sem_ins_self i _, by simp [sem_ins, single]⟩
  have hgy : val D (sem_ins i (single a)) (n + j) = true := by
    by_contra hc2
    rw [Bool.not_eq_true] at hc2
    have hgx : val D (single a) (n + j) = false := by
      by_contra hc3
      rw [Bool.not_eq_false] at hc3
      rw [val_mono hS _ _ (sem_ins_ge i _) _ hc3] at hc2
      exact Bool.noConfusion hc2
    have h2 := sem_dom_eq_at hS _ _ i (sem_ins_agree i (single a)) (n + j) (outW n D)
      (sem_chain_dom_at hS hchg hout) (hgx.trans hc2.symm)
    rw [hx0, hy1] at h2
    exact Bool.false_ne_true h2
  rw [sem_val_gate_src hS _ hj s, ht, gop_true, Bool.and_eq_true] at hgy
  have hind := sem_sibling_indep hS i hj s hch hf _ _ (sem_ins_agree i (single a))
  rw [hgy.1] at hind
  exact mem_supp.mpr hind

end SemDiff

def sup_Occ (n : ℕ) (D : Dag) (P M : Finset (Fin n)) : Prop := ∃ w, supp n D w ∩ P = M

def sup_big (n : ℕ) (D : Dag) (P : Finset (Fin n)) : Finset ℕ :=
  (merges n D (carrierT n D P)).filter (fun j => 2 ≤ (supp n D (n + j) ∩ P).card)

def sup_Wit (n : ℕ) (D : Dag) (P U : Finset (Fin n)) (f : Fin n) (e : ℕ × Bool) : Prop :=
  e.1 < D.length ∧ tag D e.1 = true ∧ f ∈ P ∧ f ∈ supp n D (src D e) ∧
    f ∉ supp n D (n + e.1) ∧ supp n D (src D e) ∩ P ⊆ U ∧ (supp n D (src D e) ∩ P).card ≤ 2

def sup_cost (n : ℕ) (D : Dag) (P : Finset (Fin n)) (e : ℕ × Bool) : (ℕ × Bool) ⊕ ℕ :=
  if supp n D (n + e.1) ∩ P = ∅ then Sum.inl e else Sum.inr e.1

def sup_CostOK (n : ℕ) (D : Dag) (P : Finset (Fin n)) (c : (ℕ × Bool) ⊕ ℕ) : Prop :=
  Sum.elim (fun e => e ∈ exitArcs n D (carrierT n D P) ∧ (supp n D (src D e) ∩ P).card ≤ 2)
    (fun j => j ∈ merges n D (carrierT n D P) ∧ (supp n D (n + j) ∩ P).card = 1) c

section SupMask

variable {n : ℕ} {D : Dag}

theorem sup_occ_wire (P : Finset (Fin n)) (w : ℕ) : sup_Occ n D P (supp n D w ∩ P) := ⟨w, rfl⟩

theorem sup_occ_sub {P M : Finset (Fin n)} (h : sup_Occ n D P M) : M ⊆ P := by
  obtain ⟨w, rfl⟩ := h
  exact Finset.inter_subset_right

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

theorem sup_triple_parent (hS : Strict n D) {P T : Finset (Fin n)} (hP : P.card ≤ 7)
    (hT : T.card = 3) (h : sup_Occ n D P T) :
    (∃ A, sup_Occ n D P A ∧ A.card = 2 ∧ A ⊆ T) ∨
      (∃ A, sup_Occ n D P A ∧ A.card = 4 ∧ T ⊆ A) ∨
      (∃ A B, A ≠ B ∧ sup_Occ n D P A ∧ sup_Occ n D P B ∧ A.card = 5 ∧ B.card = 5 ∧
        T ⊆ A ∧ T ⊆ B ∧ A ∩ B = T) := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨j, hj, -, hjT, -, -, hpar⟩ := sem_first_mask hS P T (by omega) w hw
  have hoA : sup_Occ n D P (supp n D (opA D j) ∩ P) := sup_occ_wire P _
  have hoB : sup_Occ n D P (supp n D (opB D j) ∩ P) := sup_occ_wire P _
  rcases hpar with ⟨ht, hA, hB⟩ | ⟨-, hA, hB, hun, -, -⟩
  · have hAB : (supp n D (opA D j) ∩ P) ∩ (supp n D (opB D j) ∩ P) = T := by
      rw [← hjT, sem_supp_and hS hj ht]
      ext v
      simp only [Finset.mem_inter]
      tauto
    generalize supp n D (opA D j) ∩ P = A at hoA hA hAB
    generalize supp n D (opB D j) ∩ P = B at hoB hB hAB
    have hcA := Finset.card_lt_card hA
    have hcB := Finset.card_lt_card hB
    have hu : (A ∪ B).card ≤ 7 :=
      (Finset.card_le_card (Finset.union_subset (sup_occ_sub hoA) (sup_occ_sub hoB))).trans hP
    have hie := Finset.card_union_add_card_inter A B
    rw [hAB] at hie
    by_cases h4 : A.card = 4
    · exact Or.inr (Or.inl ⟨A, hoA, h4, hA.subset⟩)
    by_cases h4' : B.card = 4
    · exact Or.inr (Or.inl ⟨B, hoB, h4', hB.subset⟩)
    refine Or.inr (Or.inr ⟨A, B, ?_, hoA, hoB, by omega, by omega, hA.subset, hB.subset, hAB⟩)
    intro hEq
    rw [hEq, Finset.inter_self] at hAB
    rw [hAB] at hcB
    omega
  · generalize supp n D (opA D j) ∩ P = A at hoA hA hun
    generalize supp n D (opB D j) ∩ P = B at hoB hB hun
    have hcA := Finset.card_lt_card hA
    have hcB := Finset.card_lt_card hB
    have hc := Finset.card_union_le A B
    rw [hun] at hc
    by_cases h2 : A.card = 2
    · exact Or.inl ⟨A, hoA, h2, hA.subset⟩
    · exact Or.inl ⟨B, hoB, by omega, hB.subset⟩

theorem sup_triple_parent_six (hS : Strict n D) {P T : Finset (Fin n)} (hP : P.card ≤ 6)
    (hT : T.card = 3) (h : sup_Occ n D P T) :
    (∃ A, sup_Occ n D P A ∧ A.card = 2 ∧ A ⊆ T) ∨
      (∃ A, sup_Occ n D P A ∧ A.card = 4 ∧ T ⊆ A) := by
  rcases sup_triple_parent hS (by omega) hT h with h2 | h4 |
    ⟨A, B, -, hoA, hoB, hcA, hcB, -, -, hAB⟩
  · exact Or.inl h2
  · exact Or.inr h4
  · exfalso
    have hu := (Finset.card_le_card
      (Finset.union_subset (sup_occ_sub hoA) (sup_occ_sub hoB))).trans hP
    have hie := Finset.card_union_add_card_inter A B
    rw [hAB] at hie
    omega

theorem sup_pair_unique {T T' A : Finset (Fin n)} (hA : A.card = 2) (h1 : A ⊆ T)
    (h2 : A ⊆ T') (hint : T ≠ T' → (T ∩ T').card ≤ 1) : T = T' := by
  by_contra hne
  have h3 := Finset.card_le_card (Finset.subset_inter h1 h2)
  have h4 := hint hne
  omega

theorem sup_four_unique {T T' A : Finset (Fin n)} (hT : T.card = 3) (hT' : T'.card = 3)
    (hA : A.card = 4) (h1 : T ⊆ A) (h2 : T' ⊆ A) (hint : T ≠ T' → (T ∩ T').card ≤ 1) :
    T = T' := by
  by_contra hne
  have h3 := Finset.card_le_card (Finset.union_subset h1 h2)
  have h4 := Finset.card_union_add_card_inter T T'
  have h5 := hint hne
  omega

theorem sup_five_cap {T1 T2 T3 A : Finset (Fin n)} (h1 : T1.card = 3) (h2 : T2.card = 3)
    (h3 : T3.card = 3) (hA : A.card ≤ 5) (s1 : T1 ⊆ A) (s2 : T2 ⊆ A) (s3 : T3 ⊆ A)
    (i12 : (T1 ∩ T2).card ≤ 1) (i13 : (T1 ∩ T3).card ≤ 1) (i23 : (T2 ∩ T3).card ≤ 1) :
    False := by
  have hu := Finset.card_le_card (Finset.union_subset (Finset.union_subset s1 s2) s3)
  have e1 := Finset.card_union_add_card_inter T1 T2
  have e2 := Finset.card_union_add_card_inter (T1 ∪ T2) T3
  have e3 : ((T1 ∪ T2) ∩ T3).card ≤ (T1 ∩ T3).card + (T2 ∩ T3).card := by
    rw [Finset.union_inter_distrib_right]
    exact Finset.card_union_le _ _
  omega

theorem sup_aux_exists (hS : Strict n D) {P : Finset (Fin n)} (hP : P.card ≤ 7)
    (L : Finset (Finset (Fin n))) (h3 : ∀ T ∈ L, T.card = 3 ∧ sup_Occ n D P T)
    (hint : ∀ T ∈ L, ∀ T' ∈ L, T ≠ T' → (T ∩ T').card ≤ 1) :
    ∃ Aux : Finset (Finset (Fin n)), L.card ≤ Aux.card ∧ ∀ A ∈ Aux, sup_Occ n D P A ∧
      ((A.card = 2 ∧ ∃ T ∈ L, A ⊆ T) ∨ A.card = 4 ∨ A.card = 5) := by
  classical
  refine ⟨P.powerset.filter (fun A => sup_Occ n D P A ∧
      ((A.card = 2 ∧ ∃ T ∈ L, A ⊆ T) ∨ A.card = 4 ∨ A.card = 5)), ?_,
    fun A hA => (Finset.mem_filter.mp hA).2⟩
  generalize hAux : P.powerset.filter (fun A => sup_Occ n D P A ∧
      ((A.card = 2 ∧ ∃ T ∈ L, A ⊆ T) ∨ A.card = 4 ∨ A.card = 5)) = Aux
  have hmem : ∀ A, sup_Occ n D P A →
      ((A.card = 2 ∧ ∃ T ∈ L, A ⊆ T) ∨ A.card = 4 ∨ A.card = 5) → A ∈ Aux := by
    intro A h1 h2
    rw [← hAux]
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (sup_occ_sub h1), h1, h2⟩
  have hprop : ∀ A ∈ Aux, (A.card = 2 ∧ ∃ T ∈ L, A ⊆ T) ∨ A.card = 4 ∨ A.card = 5 := by
    intro A hA
    rw [← hAux] at hA
    exact (Finset.mem_filter.mp hA).2.2
  have hrow : ∀ T ∈ L, 2 ≤ ∑ A ∈ Aux,
      (if A.card = 5 then (if T ⊆ A then 1 else 0) else (if A ⊆ T ∨ T ⊆ A then 2 else 0)) := by
    intro T hT
    rcases sup_triple_parent hS hP (h3 T hT).1 (h3 T hT).2 with
      ⟨A, ho, hc, hs⟩ | ⟨A, ho, hc, hs⟩ | ⟨A, B, hne, hoA, hoB, hcA, hcB, hsA, hsB, -⟩
    · refine le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (hmem A ho (Or.inl ⟨hc, T, hT, hs⟩)))
      simp [hc, hs]
    · refine le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (hmem A ho (Or.inr (Or.inl hc))))
      simp [hc, hs]
    · have hsub : ({A, B} : Finset (Finset (Fin n))) ⊆ Aux := by
        intro x hx
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hmem _ hoA (Or.inr (Or.inr hcA))
        · exact hmem _ hoB (Or.inr (Or.inr hcB))
      refine le_trans ?_ (Finset.sum_le_sum_of_subset hsub)
      rw [Finset.sum_pair hne]
      simp [hcA, hcB, hsA, hsB]
  have hcol : ∀ A ∈ Aux, ∑ T ∈ L,
      (if A.card = 5 then (if T ⊆ A then 1 else 0) else (if A ⊆ T ∨ T ⊆ A then 2 else 0)) ≤ 2 := by
    intro A hA
    by_cases h5 : A.card = 5
    · have hsum : ∑ T ∈ L, (if A.card = 5 then (if T ⊆ A then 1 else 0)
          else (if A ⊆ T ∨ T ⊆ A then 2 else 0)) = (L.filter (fun T => T ⊆ A)).card := by
        rw [Finset.card_filter]
        exact Finset.sum_congr rfl (fun T _ => by simp [h5])
      rw [hsum]
      by_contra hgt
      obtain ⟨T1, T2, T3, m1, m2, m3, n12, n13, n23⟩ :=
        Finset.two_lt_card_iff.mp (show 2 < (L.filter (fun T => T ⊆ A)).card by omega)
      rw [Finset.mem_filter] at m1 m2 m3
      exact sup_five_cap (h3 _ m1.1).1 (h3 _ m2.1).1 (h3 _ m3.1).1 h5.le m1.2 m2.2 m3.2
        (hint _ m1.1 _ m2.1 n12) (hint _ m1.1 _ m3.1 n13) (hint _ m2.1 _ m3.1 n23)
    · have hsum : ∑ T ∈ L, (if A.card = 5 then (if T ⊆ A then 1 else 0)
          else (if A ⊆ T ∨ T ⊆ A then 2 else 0)) =
          2 * (L.filter (fun T => A ⊆ T ∨ T ⊆ A)).card := by
        rw [Finset.card_filter, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun T _ => by simp [h5])
      rw [hsum]
      have hle : (L.filter (fun T => A ⊆ T ∨ T ⊆ A)).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro T hT T' hT'
        rw [Finset.mem_filter] at hT hT'
        have c3 := (h3 T hT.1).1
        have c3' := (h3 T' hT'.1).1
        rcases hprop A hA with ⟨h2, -⟩ | h4 | h5'
        · have e1 : A ⊆ T := hT.2.resolve_right (fun h => by
            have := Finset.card_le_card h; omega)
          have e2 : A ⊆ T' := hT'.2.resolve_right (fun h => by
            have := Finset.card_le_card h; omega)
          exact sup_pair_unique h2 e1 e2 (hint T hT.1 T' hT'.1)
        · have e1 : T ⊆ A := hT.2.resolve_left (fun h => by
            have := Finset.card_le_card h; omega)
          have e2 : T' ⊆ A := hT'.2.resolve_left (fun h => by
            have := Finset.card_le_card h; omega)
          exact sup_four_unique c3 c3' h4 e1 e2 (hint T hT.1 T' hT'.1)
        · exact absurd h5' h5
      omega
  have h1 := Finset.card_nsmul_le_sum L _ 2 hrow
  have h2 := Finset.sum_le_card_nsmul Aux _ 2 hcol
  rw [Finset.sum_comm] at h1
  simp only [smul_eq_mul] at h1 h2
  omega

theorem sup_charge (hS : Strict n D) {P : Finset (Fin n)} (hP : P.card ≤ 7)
    (L : Finset (Finset (Fin n))) (h3 : ∀ T ∈ L, T.card = 3 ∧ sup_Occ n D P T)
    (hint : ∀ T ∈ L, ∀ T' ∈ L, T ≠ T' → (T ∩ T').card ≤ 1)
    (X : Finset (Finset (Fin n)))
    (hX : ∀ M ∈ X, sup_Occ n D P M ∧ 2 ≤ M.card ∧ M ∉ L ∧ M.card ≠ 4 ∧ M.card ≠ 5 ∧
      (M.card = 2 → ∀ T ∈ L, ¬ M ⊆ T)) :
    2 * L.card + X.card ≤ (sup_big n D P).card := by
  classical
  obtain ⟨Aux, hcard, hAux⟩ := sup_aux_exists hS hP L h3 hint
  have hd1 : Disjoint L Aux := by
    rw [Finset.disjoint_left]
    intro T hT hTA
    have := (h3 T hT).1
    rcases (hAux T hTA).2 with ⟨h, -⟩ | h | h <;> omega
  have hd2 : Disjoint (L ∪ Aux) X := by
    rw [Finset.disjoint_left]
    intro M hM hMX
    obtain ⟨-, -, hnL, hn4, hn5, hno⟩ := hX M hMX
    rcases Finset.mem_union.mp hM with h | h
    · exact hnL h
    · rcases (hAux M h).2 with ⟨h2, T, hT, hs⟩ | h4 | h5
      · exact hno h2 T hT hs
      · exact hn4 h4
      · exact hn5 h5
  have hle := sup_card_le_big hS P ((L ∪ Aux) ∪ X) (by
    intro M hM
    rcases Finset.mem_union.mp hM with h | h
    · rcases Finset.mem_union.mp h with h | h
      · exact ⟨by have := (h3 M h).1; omega, (h3 M h).2⟩
      · refine ⟨?_, (hAux M h).1⟩
        rcases (hAux M h).2 with ⟨h, -⟩ | h | h <;> omega
    · exact ⟨(hX M h).2.1, (hX M h).1⟩)
  rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1] at hle
  omega

theorem sup_wit_exists {G : Fin n → Fin n → Prop} (hG : sem_Gr G) (hS : Strict n D)
    (hC : sem_Comp n G D) {P U X : Finset (Fin n)} (hUP : U ⊆ P)
    (hU : U.card ≤ 2 ∨ (U.card = 3 ∧ ¬ sup_Occ n D P U))
    (hX : ∀ a ∈ X, ∀ b ∈ X, ¬ G a b) (hPX : P \ U ⊆ X) {f : Fin n} (hf : f ∈ U)
    (hnb : ∃ a ∈ X, G f a) : ∃ e, sup_Wit n D P U f e := by
  obtain ⟨j, s, hj, ht, h1, h2, hd⟩ := sem_exposure hG hS hC X hX f hnb
  have hsub : supp n D (src D (j, s)) ∩ P ⊆ U := by
    intro v hv
    rw [Finset.mem_inter] at hv
    by_contra hvU
    exact Finset.disjoint_left.mp hd hv.1 (hPX (Finset.mem_sdiff.mpr ⟨hv.2, hvU⟩))
  refine ⟨(j, s), hj, ht, hUP hf, h1, h2, hsub, ?_⟩
  rcases hU with hU | ⟨hU3, hmiss⟩
  · exact (Finset.card_le_card hsub).trans hU
  · have hne : supp n D (src D (j, s)) ∩ P ≠ U := fun h => hmiss ⟨_, h⟩
    have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
    omega

theorem sup_wit_out (hS : Strict n D) {P U : Finset (Fin n)} {f : Fin n} {e : ℕ × Bool}
    (h : sup_Wit n D P U f e) :
    supp n D (n + e.1) ∩ P ⊆ (supp n D (src D e) ∩ P).erase f := by
  obtain ⟨hj, ht, -, -, h2, -, -⟩ := h
  intro v hv
  rw [Finset.mem_inter] at hv
  rw [Finset.mem_erase, Finset.mem_inter]
  exact ⟨fun hvf => h2 (hvf ▸ hv.1), sem_supp_and_sub hS hj ht e.2 hv.1, hv.2⟩

theorem sup_wit_single {P U : Finset (Fin n)} {f : Fin n} {e : ℕ × Bool}
    (h : sup_Wit n D P U f e)
    (hno : ∀ M, M ⊆ U → M.card = 2 → f ∈ M → ¬ sup_Occ n D P M) :
    supp n D (src D e) ∩ P = {f} := by
  obtain ⟨-, -, hfP, h1, -, hsub, hc⟩ := h
  have hfm : f ∈ supp n D (src D e) ∩ P := Finset.mem_inter.mpr ⟨h1, hfP⟩
  have hc2 : (supp n D (src D e) ∩ P).card ≠ 2 :=
    fun h2 => hno _ hsub h2 hfm (sup_occ_wire P _)
  exact (Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr hfm)
    (by rw [Finset.card_singleton]; omega)).symm

theorem sup_cost_inl {P : Finset (Fin n)} {e e0 : ℕ × Bool}
    (h : sup_cost n D P e = Sum.inl e0) : e = e0 ∧ supp n D (n + e.1) ∩ P = ∅ := by
  unfold sup_cost at h
  split_ifs at h with h0
  exact ⟨Sum.inl.inj h, h0⟩

theorem sup_cost_inr {P : Finset (Fin n)} {e : ℕ × Bool} {j : ℕ}
    (h : sup_cost n D P e = Sum.inr j) : e.1 = j ∧ (supp n D (n + e.1) ∩ P).Nonempty := by
  unfold sup_cost at h
  split_ifs at h with h0
  exact ⟨Sum.inr.inj h, Finset.nonempty_iff_ne_empty.mpr h0⟩

theorem sup_cost_ok (hS : Strict n D) {P U : Finset (Fin n)} {f : Fin n} {e : ℕ × Bool}
    (h : sup_Wit n D P U f e) : sup_CostOK n D P (sup_cost n D P e) := by
  have hout := sup_wit_out hS h
  obtain ⟨hj, ht, hfP, h1, -, -, hc⟩ := h
  have hfm : f ∈ supp n D (src D e) ∩ P := Finset.mem_inter.mpr ⟨h1, hfP⟩
  unfold sup_cost
  split_ifs with h0
  · show e ∈ exitArcs n D (carrierT n D P) ∧ (supp n D (src D e) ∩ P).card ≤ 2
    refine ⟨?_, hc⟩
    rw [exitArcs, Finset.mem_filter]
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hj, Finset.mem_univ _⟩,
      sup_mem_carrier.mpr ⟨f, hfm⟩, ?_⟩
    rw [sup_mem_carrier, h0]
    exact Finset.not_nonempty_empty
  · show e.1 ∈ merges n D (carrierT n D P) ∧ (supp n D (n + e.1) ∩ P).card = 1
    have hne : (supp n D (n + e.1) ∩ P).Nonempty := Finset.nonempty_iff_ne_empty.mpr h0
    have hle := Finset.card_le_card hout
    rw [Finset.card_erase_of_mem hfm] at hle
    have hpos := Finset.card_pos.mpr hne
    refine ⟨?_, by omega⟩
    obtain ⟨v, hv⟩ := hne
    rw [Finset.mem_inter] at hv
    have hA := sem_supp_and_sub hS hj ht false hv.1
    have hB := sem_supp_and_sub hS hj ht true hv.1
    rw [sb_src_false] at hA
    rw [sb_src_true] at hB
    rw [merges, Finset.mem_filter, Finset.mem_range]
    exact ⟨hj, sup_mem_carrier.mpr ⟨v, Finset.mem_inter.mpr hv⟩,
      sup_mem_carrier.mpr ⟨v, Finset.mem_inter.mpr ⟨hA, hv.2⟩⟩,
      sup_mem_carrier.mpr ⟨v, Finset.mem_inter.mpr ⟨hB, hv.2⟩⟩⟩

theorem sup_wit_same_pos (hS : Strict n D) {P U U' : Finset (Fin n)} {f f' : Fin n}
    {e : ℕ × Bool} (h : sup_Wit n D P U f e) (h' : sup_Wit n D P U' f' e)
    (hne : (supp n D (n + e.1) ∩ P).Nonempty) : f = f' := by
  by_contra hff
  obtain ⟨q, hq⟩ := hne
  have h1 := sup_wit_out hS h hq
  have h2 := sup_wit_out hS h' hq
  rw [Finset.mem_erase] at h1 h2
  have hsub : ({q, f, f'} : Finset (Fin n)) ⊆ supp n D (src D e) ∩ P := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx | hx <;> rw [hx]
    · exact h1.2
    · exact Finset.mem_inter.mpr ⟨h.2.2.2.1, h.2.2.1⟩
    · exact Finset.mem_inter.mpr ⟨h'.2.2.2.1, h'.2.2.1⟩
  have hc := Finset.card_le_card hsub
  have h3 : ({q, f, f'} : Finset (Fin n)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hff]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h1.1, h2.1⟩
  have := h.2.2.2.2.2.2
  omega

theorem sup_cost_ne_of_disjoint (hS : Strict n D) {P U U' : Finset (Fin n)} {f f' : Fin n}
    {e e' : ℕ × Bool} (h : sup_Wit n D P U f e) (h' : sup_Wit n D P U' f' e')
    (hd : Disjoint U U') : sup_cost n D P e ≠ sup_cost n D P e' := by
  intro heq
  have hfm : f ∈ supp n D (src D e) ∩ P := Finset.mem_inter.mpr ⟨h.2.2.2.1, h.2.2.1⟩
  by_cases h0 : supp n D (n + e.1) ∩ P = ∅
  · have hc : sup_cost n D P e = Sum.inl e := by simp [sup_cost, h0]
    rw [hc] at heq
    have he := (sup_cost_inl heq.symm).1
    subst he
    exact Finset.disjoint_left.mp hd (h.2.2.2.2.2.1 hfm) (h'.2.2.2.2.2.1 hfm)
  · have hc : sup_cost n D P e = Sum.inr e.1 := by simp [sup_cost, h0]
    rw [hc] at heq
    have he := (sup_cost_inr heq.symm).1
    obtain ⟨q, hq⟩ := Finset.nonempty_iff_ne_empty.mpr h0
    have q1 := Finset.mem_of_mem_erase (sup_wit_out hS h hq)
    rw [← he] at hq
    have q2 := Finset.mem_of_mem_erase (sup_wit_out hS h' hq)
    exact Finset.disjoint_left.mp hd (h.2.2.2.2.2.1 q1) (h'.2.2.2.2.2.1 q2)

theorem sup_cost_ne_of_single (hS : Strict n D) {P U U' : Finset (Fin n)} {f f' : Fin n}
    {e e' : ℕ × Bool} (h : sup_Wit n D P U f e) (h' : sup_Wit n D P U' f' e')
    (hs : supp n D (src D e) ∩ P = {f}) (hff : f ≠ f') :
    sup_cost n D P e ≠ sup_cost n D P e' := by
  intro heq
  have h0 : supp n D (n + e.1) ∩ P = ∅ := by
    have hout := sup_wit_out hS h
    rw [hs, Finset.erase_singleton] at hout
    exact Finset.subset_empty.mp hout
  have hc : sup_cost n D P e = Sum.inl e := by simp [sup_cost, h0]
  rw [hc] at heq
  have he := (sup_cost_inl heq.symm).1
  subst he
  have hm : f' ∈ supp n D (src D e') ∩ P := Finset.mem_inter.mpr ⟨h'.2.2.2.1, h'.2.2.1⟩
  rw [hs, Finset.mem_singleton] at hm
  exact hff hm.symm

theorem sup_fibre_le (hS : Strict n D) {P : Finset (Fin n)} (Lab : Finset (Fin n))
    (U : Fin n → Finset (Fin n)) (wit : Fin n → ℕ × Bool)
    (hwit : ∀ f ∈ Lab, sup_Wit n D P (U f) f (wit f)) (c : (ℕ × Bool) ⊕ ℕ) :
    (Lab.filter (fun f => sup_cost n D P (wit f) = c)).card ≤ 2 := by
  rcases c with e0 | j0
  · by_cases hne : (Lab.filter (fun f => sup_cost n D P (wit f) = Sum.inl e0)).Nonempty
    · obtain ⟨f0, hf0⟩ := hne
      rw [Finset.mem_filter] at hf0
      have hcard := (hwit f0 hf0.1).2.2.2.2.2.2
      rw [(sup_cost_inl hf0.2).1] at hcard
      refine le_trans (Finset.card_le_card ?_) hcard
      intro f hf
      rw [Finset.mem_filter] at hf
      have hw := hwit f hf.1
      rw [(sup_cost_inl hf.2).1] at hw
      exact Finset.mem_inter.mpr ⟨hw.2.2.2.1, hw.2.2.1⟩
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne]
      simp
  · have hinj : Set.InjOn (fun f => (wit f).2)
        (Lab.filter (fun f => sup_cost n D P (wit f) = Sum.inr j0) : Set (Fin n)) := by
      intro f hf f' hf' hs
      rw [Finset.mem_coe, Finset.mem_filter] at hf hf'
      obtain ⟨h1, hn1⟩ := sup_cost_inr hf.2
      obtain ⟨h1', -⟩ := sup_cost_inr hf'.2
      have hee : wit f = wit f' := Prod.ext (h1.trans h1'.symm) hs
      have hw' := hwit f' hf'.1
      rw [← hee] at hw'
      exact sup_wit_same_pos hS (hwit f hf.1) hw' hn1
    have hle := Finset.card_le_card_of_injOn (t := (Finset.univ : Finset Bool))
      (fun f => (wit f).2) (fun _ _ => Finset.mem_univ _) hinj
    simpa using hle

theorem sup_wit_card (hS : Strict n D) {P : Finset (Fin n)} (Lab : Finset (Fin n))
    (U : Fin n → Finset (Fin n)) (wit : Fin n → ℕ × Bool)
    (hwit : ∀ f ∈ Lab, sup_Wit n D P (U f) f (wit f)) :
    Lab.card ≤ 2 * (Lab.image (fun f => sup_cost n D P (wit f))).card :=
  Finset.card_le_mul_card_image Lab 2 (fun c _ => sup_fibre_le hS Lab U wit hwit c)

theorem sup_wit_card_single (hS : Strict n D) {P : Finset (Fin n)} (Lab S : Finset (Fin n))
    (U : Fin n → Finset (Fin n)) (wit : Fin n → ℕ × Bool)
    (hwit : ∀ f ∈ Lab, sup_Wit n D P (U f) f (wit f)) (hSL : S ⊆ Lab)
    (hsing : ∀ f ∈ S, supp n D (src D (wit f)) ∩ P = {f}) :
    2 * S.card + (Lab \ S).card ≤
      2 * (Lab.image (fun f => sup_cost n D P (wit f))).card := by
  have h1 : (S.image (fun f => sup_cost n D P (wit f))).card = S.card :=
    Finset.card_image_of_injOn (fun f hf f' hf' heq => by
      by_contra hne
      exact sup_cost_ne_of_single hS (hwit f (hSL hf)) (hwit f' (hSL hf')) (hsing f hf) hne heq)
  have h2 := sup_wit_card hS (Lab \ S) U wit (fun f hf => hwit f (Finset.mem_sdiff.mp hf).1)
  have hd : Disjoint (S.image (fun f => sup_cost n D P (wit f)))
      ((Lab \ S).image (fun f => sup_cost n D P (wit f))) := by
    rw [Finset.disjoint_left]
    intro c hc1 hc2
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hc1
    obtain ⟨f', hf', heq⟩ := Finset.mem_image.mp hc2
    rw [Finset.mem_sdiff] at hf'
    exact sup_cost_ne_of_single hS (hwit f (hSL hf)) (hwit f' hf'.1) (hsing f hf)
      (fun h => hf'.2 (h ▸ hf)) heq.symm
  have h3 : (S.image (fun f => sup_cost n D P (wit f)) ∪
      (Lab \ S).image (fun f => sup_cost n D P (wit f))).card ≤
      (Lab.image (fun f => sup_cost n D P (wit f))).card :=
    Finset.card_le_card (Finset.union_subset (Finset.image_subset_image hSL)
      (Finset.image_subset_image Finset.sdiff_subset))
  rw [Finset.card_union_of_disjoint hd, h1] at h3
  omega

theorem sup_master (P : Finset (Fin n)) (E : Finset (ℕ × Bool))
    (hE : ∀ e ∈ E, e ∈ exitArcs n D (carrierT n D P) ∧ 3 ≤ (supp n D (src D e) ∩ P).card)
    (C : Finset ((ℕ × Bool) ⊕ ℕ)) (hC : ∀ c ∈ C, sup_CostOK n D P c) :
    (sup_big n D P).card + E.card + C.card ≤
      (exitArcs n D (carrierT n D P)).card + (merges n D (carrierT n D P)).card := by
  have hl : ∀ e ∈ C.toLeft, e ∈ exitArcs n D (carrierT n D P) ∧
      (supp n D (src D e) ∩ P).card ≤ 2 := fun e he => hC _ (Finset.mem_toLeft.mp he)
  have hr : ∀ j ∈ C.toRight, j ∈ merges n D (carrierT n D P) ∧
      (supp n D (n + j) ∩ P).card = 1 := fun j hj => hC _ (Finset.mem_toRight.mp hj)
  have h1 : E.card + C.toLeft.card ≤ (exitArcs n D (carrierT n D P)).card := by
    rw [← Finset.card_union_of_disjoint]
    · refine Finset.card_le_card (fun e he => ?_)
      rcases Finset.mem_union.mp he with h | h
      · exact (hE e h).1
      · exact (hl e h).1
    · rw [Finset.disjoint_left]
      intro e h1 h2
      have a := (hE e h1).2
      have b := (hl e h2).2
      omega
  have h2 : (sup_big n D P).card + C.toRight.card ≤ (merges n D (carrierT n D P)).card := by
    rw [← Finset.card_union_of_disjoint]
    · refine Finset.card_le_card (fun j hj => ?_)
      rcases Finset.mem_union.mp hj with h | h
      · exact (Finset.mem_filter.mp h).1
      · exact (hr j h).1
    · rw [Finset.disjoint_left]
      intro j h1 h2
      have a := (Finset.mem_filter.mp h1).2
      have b := (hr j h2).2
      omega
  have h3 := Finset.card_toLeft_add_card_toRight (u := C)
  omega

theorem sup_count (hS : Strict n D) (P : Finset (Fin n)) (E : Finset (ℕ × Bool))
    (hE : ∀ e ∈ E, e ∈ exitArcs n D (carrierT n D P) ∧ 3 ≤ (supp n D (src D e) ∩ P).card)
    (Lab S : Finset (Fin n)) (U : Fin n → Finset (Fin n)) (wit : Fin n → ℕ × Bool)
    (hwit : ∀ f ∈ Lab, sup_Wit n D P (U f) f (wit f)) (hSL : S ⊆ Lab)
    (hsing : ∀ f ∈ S, supp n D (src D (wit f)) ∩ P = {f}) :
    2 * ((sup_big n D P).card + E.card) + 2 * S.card + (Lab \ S).card ≤
      2 * ((exitArcs n D (carrierT n D P)).card + (merges n D (carrierT n D P)).card) := by
  have h1 := sup_wit_card_single hS Lab S U wit hwit hSL hsing
  have h2 := sup_master P E hE (Lab.image (fun f => sup_cost n D P (wit f))) (by
    intro c hc
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hc
    exact sup_cost_ok hS (hwit f hf))
  omega

theorem sup_assigned_exits {G : Fin n → Fin n → Prop} (hG : sem_Gr G) (h : StrictLive n D)
    (hC : sem_Comp n G D) (P I : Finset (Fin n))
    (hI : ∀ i ∈ I, i ∈ ineligSet n D ∧
      ∃ N : Finset (Fin n), N ⊆ P ∧ 3 ≤ N.card ∧ ∀ a ∈ N, G i a) :
    ∃ E : Finset (ℕ × Bool), E.card = I.card ∧ ∀ e ∈ E,
      e ∈ exitArcs n D (carrierT n D P) ∧ 3 ≤ (supp n D (src D e) ∩ P).card := by
  classical
  have hex : ∀ i : Fin n, ∃ e : ℕ × Bool, i ∈ I → e.1 < D.length ∧
      supp n D (src D e) = {i} ∧ supp n D (n + e.1) = ∅ ∧
      ∀ a, G i a → a ∈ supp n D (src D (e.1, !e.2)) := by
    intro i
    by_cases hi : i ∈ I
    · obtain ⟨e, h1, -, h3, h4, h5, -, -⟩ := sem_inelig_consumer hG h hC (hI i hi).1
      exact ⟨e, fun _ => ⟨h1, h3, h4, h5⟩⟩
    · exact ⟨(0, false), fun hc => absurd hc hi⟩
  choose g hg using hex
  refine ⟨I.image (fun i => ((g i).1, !(g i).2)), ?_, ?_⟩
  · refine Finset.card_image_of_injOn (fun i hi i' hi' heq => ?_)
    rw [Prod.mk.injEq, Bool.not_inj_iff] at heq
    have he : g i = g i' := Prod.ext heq.1 heq.2
    have h1 := (hg i hi).2.1
    rw [he, (hg i' hi').2.1] at h1
    exact (Finset.singleton_injective h1).symm
  · intro e he
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hj, -, hout, hnb⟩ := hg i hi
    obtain ⟨N, hNP, hN3, hNG⟩ := (hI i hi).2
    have hsub : N ⊆ supp n D (src D ((g i).1, !(g i).2)) ∩ P :=
      fun a ha => Finset.mem_inter.mpr ⟨hnb a (hNG a ha), hNP ha⟩
    have hc := Finset.card_le_card hsub
    refine ⟨?_, by omega⟩
    rw [exitArcs, Finset.mem_filter]
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hj, Finset.mem_univ _⟩,
      sup_mem_carrier.mpr (Finset.card_pos.mp (by omega)), ?_⟩
    rw [sup_mem_carrier, hout, Finset.empty_inter]
    exact Finset.not_nonempty_empty

end SupMask

theorem sup_hw_inter (u v : Fin 14) (h : u ≠ v) (P : Finset (Fin 14)) :
    ((Finset.univ.filter (fun z => Adj u z) ∩ P) ∩
      (Finset.univ.filter (fun z => Adj v z) ∩ P)).card ≤ 1 := by
  refine le_trans (Finset.card_le_card (fun z hz => ?_)) (common_nbr_le_one u v h)
  simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hz
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ z, hz.1.1, hz.2.1⟩

def k4_adjB (u v : Fin 10) : Bool :=
  (([112, 400, 672, 832, 3, 5, 9, 6, 10, 12] : List ℕ).getD u.val 0).testBit v.val

abbrev k4_Adj (u v : Fin 10) : Prop := k4_adjB u v = true

theorem k4_gr : sem_Gr k4_Adj :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

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

def k4_Pos (n : ℕ) (G : Fin n → Fin n → Prop) (D : Dag) (pos : Fin n → ℕ × Bool) : Prop :=
  (∀ i ∈ ineligSet n D, (pos i).1 < D.length ∧ supp n D (n + (pos i).1) = ∅ ∧
    (∀ a, G i a → a ∈ supp n D (src D (pos i))) ∧
    supp n D (src D ((pos i).1, !(pos i).2)) = {i}) ∧
  ∀ i ∈ ineligSet n D, ∀ i' ∈ ineligSet n D, pos i = pos i' → i = i'

theorem k4_assigned (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D) :
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

theorem k4_budget (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D) (b : Fin n → ℕ)
    (hb : PureBranch n D b) (T : Finset (Fin n)) :
    (exitArcs n D (carrierT n D T)).card + (merges n D (carrierT n D T)).card +
      (eligSet n D).card ≤ 2 * T.card + Bplus n D := by
  have h1 := carrier_flow_union h T (by rw [sem_supp_out hG hC, Finset.empty_inter])
  have h2 := surplus_carrierT_le h.1 b hb T
  have h3 := Finset.card_le_card (Finset.inter_subset_left : T ∩ eligSet n D ⊆ T)
  omega

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

theorem k4_three_cons (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    {pos : Fin n → ℕ × Bool} (hpos : k4_Pos n G D pos) {u i1 i2 i3 : Fin n}
    (h1 : i1 ∈ ineligSet n D) (h2 : i2 ∈ ineligSet n D) (h12 : i1 ≠ i2) (h13 : i1 ≠ i3)
    (h23 : i2 ≠ i3) (a1 : G u i1) (a2 : G u i2) (a3 : G u i3) :
    3 ≤ (exitArcs n D (carrierT n D {u})).card := by
  have hu := Finset.mem_singleton_self u
  have m1 := k4_pos_exit hpos h1 (hG.1 _ _ a1) hu
  have m2 := k4_pos_exit hpos h2 (hG.1 _ _ a2) hu
  have hne12 : pos i1 ≠ pos i2 := fun he => h12 (hpos.2 i1 h1 i2 h2 he)
  by_cases h3 : i3 ∈ ineligSet n D
  · exact Finset.two_lt_card.mpr ⟨_, m1, _, m2, _, k4_pos_exit hpos h3 (hG.1 _ _ a3) hu, hne12,
      fun he => h13 (hpos.2 i1 h1 i3 h3 he), fun he => h23 (hpos.2 i2 h2 i3 h3 he)⟩
  · obtain ⟨j, hj, -, -, hju, -, s, s1, -, s3, -⟩ := sem_joint_meeting hG h.1 hC a3
    have m3 : (j, s) ∈ exitArcs n D (carrierT n D {u}) := sem_mem_exit1.mpr ⟨hj, s1, hju⟩
    have key : ∀ i ∈ ineligSet n D, i ≠ i3 → pos i ≠ (j, s) := by
      intro i hi hne he
      have h4 : supp n D (src D (j, !s)) = {i} := by
        have := (hpos.1 i hi).2.2.2
        rw [he] at this
        exact this
      rw [h4, Finset.mem_singleton] at s3
      exact hne s3.symm
    exact Finset.two_lt_card.mpr ⟨_, m1, _, m2, _, m3, hne12, key i1 h1 h13, key i2 h2 h23⟩

theorem k4_flow (h : StrictLive n D) (K : Finset ℕ) (hK : K ⊆ inner n D) :
    (exitArcs n D K).card + (merges n D K).card =
      (K.filter (fun w => w < n ∨ (opA D (w - n) ∉ K ∧ opB D (w - n) ∉ K))).card +
        surplusOn D K := by
  obtain ⟨hS, hL, -⟩ := h
  have hKlt : ∀ w ∈ K, w + 1 < n + D.length := fun w hw => sb_mem_inner.mp (hK hw)
  have h1 : surplusOn D K + K.card = ((arcs D).filter (fun e => src D e ∈ K)).card := by
    rw [← sb_sum_fanout_eq hS, sb_surplus_add_card (fun w hw => hL w (hKlt w hw))]
  have h2 := Finset.card_filter_add_card_filter_not
    (s := (arcs D).filter (fun e => src D e ∈ K)) (fun e : ℕ × Bool => n + e.1 ∈ K)
  rw [Finset.filter_filter, Finset.filter_filter] at h2
  have h3 : ((arcs D).filter (fun e => src D e ∈ K ∧ n + e.1 ∈ K)).card =
      ((Finset.range D.length).filter
        (fun j => n + j ∈ K ∧ (opA D j ∈ K ∨ opB D j ∈ K))).card + (merges n D K).card := by
    rw [sb_card_arcs_filter, merges, Finset.card_filter, Finset.card_filter,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [sb_src_false, sb_src_true]
    by_cases hj2 : n + j ∈ K <;> by_cases ha : opA D j ∈ K <;> by_cases hb : opB D j ∈ K <;>
      simp_all
  have h4 : K.card =
      (K.filter (fun w => w < n ∨ (opA D (w - n) ∉ K ∧ opB D (w - n) ∉ K))).card +
      ((Finset.range D.length).filter
        (fun j => n + j ∈ K ∧ (opA D j ∈ K ∨ opB D j ∈ K))).card := by
    rw [← Finset.card_filter_add_card_filter_not (s := K)
      (fun w => w < n ∨ (opA D (w - n) ∉ K ∧ opB D (w - n) ∉ K))]
    congr 1
    have himg : K.filter (fun w => ¬ (w < n ∨ (opA D (w - n) ∉ K ∧ opB D (w - n) ∉ K))) =
        ((Finset.range D.length).filter
          (fun j => n + j ∈ K ∧ (opA D j ∈ K ∨ opB D j ∈ K))).image (fun j => n + j) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨hw, hn⟩
        have := hKlt w hw
        rw [not_or] at hn
        exact ⟨w - n, ⟨by omega, by rwa [Nat.add_sub_cancel' (by omega)], by tauto⟩, by omega⟩
      · rintro ⟨j, ⟨-, hj, hop⟩, rfl⟩
        refine ⟨hj, ?_⟩
        rw [Nat.add_sub_cancel_left]
        intro hc
        rcases hc with hc | hc
        · omega
        · tauto
    rw [himg, Finset.card_image_of_injective _ (add_right_injective n)]
  unfold exitArcs
  omega

def k4_joint (n : ℕ) (D : Dag) (u t : Fin n) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => u ∈ supp n D w ∧ t ∈ supp n D w)

theorem k4_mem_joint {u t : Fin n} {w : ℕ} :
    w ∈ k4_joint n D u t ↔ u ∈ supp n D w ∧ t ∈ supp n D w := by
  simp only [k4_joint, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
  exact fun h => sem_supp_lt h.1

theorem k4_or_sub (hS : Strict n D) {j : ℕ} (hj : j < D.length) (ht : tag D j = false)
    (s : Bool) : supp n D (src D (j, s)) ⊆ supp n D (n + j) := by
  rw [sem_supp_or hS hj ht]
  cases s
  · rw [sb_src_false]; exact Finset.subset_union_left
  · rw [sb_src_true]; exact Finset.subset_union_right

theorem k4_joint_exits (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    {u t : Fin n} (mu : merges n D (carrierT n D {u}) = ∅)
    (mt : merges n D (carrierT n D {t}) = ∅) {r : ℕ} (hru : u ∈ supp n D r)
    (hrt : t ∈ supp n D r) (hfan : 2 ≤ fanout D r) :
    ∃ e1 e2 : ℕ × Bool, e1 ≠ e2 ∧ e1 ∈ exitArcs n D (carrierT n D {u}) ∧
      e1 ∈ exitArcs n D (carrierT n D {t}) ∧ e2 ∈ exitArcs n D (carrierT n D {u}) ∧
      e2 ∈ exitArcs n D (carrierT n D {t}) := by
  have hS := h.1
  have hsub : k4_joint n D u t ⊆ inner n D := by
    intro w hw
    rw [k4_mem_joint] at hw
    rw [sb_mem_inner]
    have hlt := sem_supp_lt hw.1
    by_contra hc
    have hw2 : w = outW n D := by unfold outW; omega
    rw [hw2, sem_supp_out hG hC] at hw
    exact Finset.notMem_empty u hw.1
  have hrJ : r ∈ k4_joint n D u t := k4_mem_joint.mpr ⟨hru, hrt⟩
  have hfl := k4_flow h _ hsub
  have hM : merges n D (k4_joint n D u t) = ∅ := by
    refine Finset.eq_empty_of_forall_notMem (fun j hj => ?_)
    rw [merges, Finset.mem_filter, Finset.mem_range] at hj
    have : j ∈ merges n D (carrierT n D {u}) := by
      rw [merges, Finset.mem_filter, Finset.mem_range]
      exact ⟨hj.1, sem_mem_carrier1.mpr (k4_mem_joint.mp hj.2.1).1,
        sem_mem_carrier1.mpr (k4_mem_joint.mp hj.2.2.1).1,
        sem_mem_carrier1.mpr (k4_mem_joint.mp hj.2.2.2).1⟩
    rw [mu] at this
    exact Finset.notMem_empty _ this
  have hroot : 1 ≤ ((k4_joint n D u t).filter (fun w => w < n ∨
      (opA D (w - n) ∉ k4_joint n D u t ∧ opB D (w - n) ∉ k4_joint n D u t))).card := by
    have hne : (k4_joint n D u t).Nonempty := ⟨r, hrJ⟩
    have hm := Finset.min'_mem _ hne
    refine Finset.card_pos.mpr ⟨_, Finset.mem_filter.mpr ⟨hm, ?_⟩⟩
    by_cases hmn : (k4_joint n D u t).min' hne < n
    · exact Or.inl hmn
    · right
      have hlt := sem_supp_lt (k4_mem_joint.mp hm).1
      have hs := hS ((k4_joint n D u t).min' hne - n) (by omega)
      constructor
      · intro hc
        have := Finset.min'_le _ _ hc
        omega
      · intro hc
        have := Finset.min'_le _ _ hc
        omega
  have hsur : 1 ≤ surplusOn D (k4_joint n D u t) := by
    have := Finset.single_le_sum (f := fun w => fanout D w - 1) (fun _ _ => Nat.zero_le _) hrJ
    unfold surplusOn
    have h2 : 1 ≤ fanout D r - 1 := by omega
    exact h2.trans this
  rw [hM, Finset.card_empty] at hfl
  obtain ⟨e1, he1, e2, he2, hne⟩ := Finset.one_lt_card.mp (by omega :
    1 < (exitArcs n D (k4_joint n D u t)).card)
  have hexit : ∀ e ∈ exitArcs n D (k4_joint n D u t),
      e ∈ exitArcs n D (carrierT n D {u}) ∧ e ∈ exitArcs n D (carrierT n D {t}) := by
    intro e he
    simp only [exitArcs, arcs, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
      Finset.mem_univ, and_true, k4_mem_joint] at he
    obtain ⟨hj, ⟨hsu, hst⟩, hnot⟩ := he
    have aux : ∀ x y : Fin n, merges n D (carrierT n D {x}) = ∅ → y ∈ supp n D (src D e) →
        y ∉ supp n D (n + e.1) → x ∉ supp n D (n + e.1) := by
      intro x y mx hy hyn hx
      cases ht : tag D e.1
      · exact hyn (k4_or_sub hS hj ht e.2 hy)
      · have hx2 := hx
        rw [sem_supp_and hS hj ht, Finset.mem_inter] at hx2
        have : e.1 ∈ merges n D (carrierT n D {x}) := by
          rw [merges, Finset.mem_filter, Finset.mem_range]
          exact ⟨hj, sem_mem_carrier1.mpr hx, sem_mem_carrier1.mpr hx2.1,
            sem_mem_carrier1.mpr hx2.2⟩
        rw [mx] at this
        exact Finset.notMem_empty _ this
    have hu : u ∉ supp n D (n + e.1) := fun hx => aux u t mu hst (fun hy => hnot ⟨hx, hy⟩) hx
    have ht : t ∉ supp n D (n + e.1) := fun hx => aux t u mt hsu (fun hy => hnot ⟨hy, hx⟩) hx
    exact ⟨sem_mem_exit1.mpr ⟨hj, hsu, hu⟩, sem_mem_exit1.mpr ⟨hj, hst, ht⟩⟩
  exact ⟨e1, e2, hne, (hexit e1 he1).1, (hexit e1 he1).2, (hexit e2 he2).1, (hexit e2 he2).2⟩

end K4Generic

theorem k4_indep_facts : ∀ I : Finset (Fin 10), (∀ u ∈ I, ∀ v ∈ I, k4_adjB u v = false) →
    5 ≤ I.card → (∀ q ∈ I, 4 ≤ q.val) ∧
      ((4 ∈ I ∧ 5 ∈ I) ∨ (4 ∈ I ∧ 7 ∈ I) ∨ (5 ∈ I ∧ 7 ∈ I)) := by decide +kernel

theorem k4_cover_five : ∀ S : Finset (Fin 10), (∀ u v : Fin 10, k4_Adj u v → u ∈ S ∨ v ∈ S) →
    S.card ≤ 5 → ∀ q : Fin 10, q.val < 4 → q ∈ S := by decide +kernel

theorem k4_meets012 : ∀ i : Fin 10, 4 ≤ i.val →
    ∃ a ∈ ({0, 1, 2} : Finset (Fin 10)), k4_Adj i a := by decide +kernel

theorem k4_inelig_indep {D : Dag} (h : StrictLive 10 D) (hC : sem_Comp 10 k4_Adj D) :
    ∀ u ∈ ineligSet 10 D, ∀ v ∈ ineligSet 10 D, k4_adjB u v = false := by
  intro u hu v hv
  by_contra hc
  rw [Bool.not_eq_false] at hc
  rcases sem_elig_cover k4_gr h hC (u := u) (v := v) hc with h1 | h1
  · exact sem_mem_inelig.mp hu h1
  · exact sem_mem_inelig.mp hv h1

theorem k4_surplus_six {D : Dag} (h : StrictLive 10 D) (hC : sem_Comp 10 k4_Adj D) :
    6 ≤ Bplus 10 D := by
  by_contra hlt
  obtain ⟨b, hb⟩ := sem_exists_pureBranch k4_gr h.1 hC
  have hp := elig_le_Bplus h.1 b hb
  have hcard := inelig_card_add 10 D
  obtain ⟨hI4, hpairs⟩ := k4_indep_facts _ (k4_inelig_indep h hC) (by omega)
  obtain ⟨pos, hpos⟩ := k4_assigned k4_gr h hC
  have hbud := k4_budget k4_gr h hC b hb ({0, 1, 2} : Finset (Fin 10))
  obtain ⟨hsub, hcd⟩ := k4_exits_ge hpos ({0, 1, 2} : Finset (Fin 10)) (ineligSet 10 D)
    (fun i hi => ⟨hi, k4_meets012 i (hI4 i hi)⟩)
  have hex := Finset.card_le_card hsub
  have hT : ({0, 1, 2} : Finset (Fin 10)).card = 3 := by decide
  have q : ∀ i ∈ ineligSet 10 D, ∀ a, k4_Adj i a → a ∈ supp 10 D (src D (pos i)) :=
    fun i hi => (hpos.1 i hi).2.2.1
  have hmer : 2 ≤ (merges 10 D (carrierT 10 D ({0, 1, 2} : Finset (Fin 10)))).card := by
    rcases hpairs with ⟨i4, i5⟩ | ⟨i4, i7⟩ | ⟨i5, i7⟩
    · exact k4_pair_merges h.1 hT (a := 0) (b := 1) (c := 2) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (q 4 i4 0 (by decide))
        (q 4 i4 1 (by decide)) (q 5 i5 0 (by decide)) (q 5 i5 2 (by decide))
    · exact k4_pair_merges h.1 hT (a := 1) (b := 0) (c := 2) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (q 4 i4 1 (by decide))
        (q 4 i4 0 (by decide)) (q 7 i7 1 (by decide)) (q 7 i7 2 (by decide))
    · exact k4_pair_merges h.1 hT (a := 2) (b := 0) (c := 1) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (q 5 i5 2 (by decide))
        (q 5 i5 0 (by decide)) (q 7 i7 2 (by decide)) (q 7 i7 1 (by decide))
  omega

theorem k4_relabel_comp {G : Fin 10 → Fin 10 → Prop} (σ : Equiv.Perm (Fin 10))
    (hσ : ∀ u v, G u v ↔ k4_Adj (σ u) (σ v)) {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 G D) : sem_Comp 10 k4_Adj (relabel σ D) := by
  intro x
  rw [relabel_out σ h.1 h.2.2 x, hC]
  unfold sem_Edge
  constructor
  · rintro ⟨u, v, huv, hu, hv⟩
    exact ⟨σ u, σ v, (hσ u v).mp huv, hu, hv⟩
  · rintro ⟨u, v, huv, hu, hv⟩
    exact ⟨σ.symm u, σ.symm v, (hσ _ _).mpr (by simpa using huv), by simpa using hu,
      by simpa using hv⟩

theorem k4_surplus_six_iso {G : Fin 10 → Fin 10 → Prop} (σ : Equiv.Perm (Fin 10))
    (hσ : ∀ u v, G u v ↔ k4_Adj (σ u) (σ v)) {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 G D) : 6 ≤ Bplus 10 D := by
  rw [← relabel_Bplus σ h.1]
  exact k4_surplus_six (relabel_strictLive σ h) (k4_relabel_comp σ hσ h hC)

theorem k4_nbr3 : ∀ x : Fin 10, x.val < 4 → ∃ a b c : Fin 10, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    k4_Adj x a ∧ k4_Adj x b ∧ k4_Adj x c ∧
    ∀ i : Fin 10, k4_Adj x i → i = a ∨ i = b ∨ i = c := by decide +kernel

theorem k4_common : ∀ u t i i' : Fin 10, u ≠ t → k4_Adj u i → k4_Adj t i →
    k4_Adj u i' → k4_Adj t i' → i = i' := by decide +kernel

theorem k4_orig_adj : ∀ q : Fin 10, q.val < 4 →
    k4_adjB q 4 = true ∨ k4_adjB q 9 = true := by decide +kernel

theorem k4_share : ∀ i : Fin 10, 4 ≤ i.val → i ≠ 4 → i ≠ 9 → ∃ u i3 : Fin 10,
    k4_Adj u 4 ∧ k4_Adj u i ∧ k4_Adj u i3 ∧ (4 : Fin 10) ≠ i3 ∧ i ≠ i3 := by decide +kernel

theorem k4_opp : ∀ v : Fin 10, 4 ≤ v.val → ∃ u t : Fin 10, u ≠ t ∧ u.val < 4 ∧ t.val < 4 ∧
    (∀ i : Fin 10, k4_Adj u i → 4 ≤ i.val ∧ i ≠ v) ∧
    (∀ i : Fin 10, k4_Adj t i → 4 ≤ i.val ∧ i ≠ v) := by decide +kernel

theorem k4_six : (Finset.univ.filter (fun i : Fin 10 => 4 ≤ i.val)).card = 6 := by decide

theorem k4_sat {D : Dag} (h : StrictLive 10 D) (hC : sem_Comp 10 k4_Adj D) (b : Fin 10 → ℕ)
    (hb : PureBranch 10 D b) {pos : Fin 10 → ℕ × Bool} (hpos : k4_Pos 10 k4_Adj D pos)
    (hres : Bplus 10 D ≤ (eligSet 10 D).card + 1) {x : Fin 10} (hx4 : x.val < 4)
    (hx : ∀ i, k4_Adj x i → i ∈ ineligSet 10 D) :
    merges 10 D (carrierT 10 D {x}) = ∅ ∧
      (∀ e ∈ exitArcs 10 D (carrierT 10 D {x}), ∃ i, k4_Adj x i ∧ e = pos i) ∧
      ∃ ρ ∈ residualUnits 10 D b, x ∈ supp 10 D ρ.1 := by
  obtain ⟨a, b', c, hab, hac, hbc, ha, hb', hc, -⟩ := k4_nbr3 x hx4
  have hJ : ∀ i ∈ ({a, b', c} : Finset (Fin 10)), k4_Adj x i := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact ha
    · exact hb'
    · exact hc
  obtain ⟨hsub, hcd⟩ := k4_exits_ge hpos ({x} : Finset (Fin 10)) ({a, b', c} : Finset (Fin 10))
    (fun i hi => ⟨hx i (hJ i hi), x, Finset.mem_singleton_self x, k4_gr.1 _ _ (hJ i hi)⟩)
  have h3 : ({a, b', c} : Finset (Fin 10)).card = 3 :=
    Finset.card_eq_three.mpr ⟨a, b', c, hab, hac, hbc, rfl⟩
  have hex := Finset.card_le_card hsub
  have hbud := k4_budget k4_gr h hC b hb ({x} : Finset (Fin 10))
  have hfl := carrier_flow_union h ({x} : Finset (Fin 10))
    (by rw [sem_supp_out k4_gr hC, Finset.empty_inter])
  rw [Finset.card_singleton] at hbud hfl
  have heq := surplus_carrierT_eq h.1 b hb ({x} : Finset (Fin 10))
  have hle : (({x} : Finset (Fin 10)) ∩ eligSet 10 D).card ≤ 1 :=
    (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
  refine ⟨Finset.card_eq_zero.mp (by omega), fun e he => ?_, ?_⟩
  · have hEq := Finset.eq_of_subset_of_card_le hsub (by omega)
    rw [← hEq] at he
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
    exact ⟨i, hJ i hi, rfl⟩
  · obtain ⟨ρ, hρ⟩ := Finset.card_pos.mp (by omega :
      0 < ((residualUnits 10 D b).filter (fun u => (supp 10 D u.1 ∩ {x}).Nonempty)).card)
    rw [Finset.mem_filter] at hρ
    obtain ⟨v, hv⟩ := hρ.2
    rw [Finset.mem_inter, Finset.mem_singleton] at hv
    exact ⟨ρ, hρ.1, hv.2 ▸ hv.1⟩

theorem k4_case5 {D : Dag} (h : StrictLive 10 D) (hC : sem_Comp 10 k4_Adj D) (b : Fin 10 → ℕ)
    (hb : PureBranch 10 D b) {pos : Fin 10 → ℕ × Bool} (hpos : k4_Pos 10 k4_Adj D pos)
    (hres : Bplus 10 D ≤ (eligSet 10 D).card + 1) {u t : Fin 10} (hut : u ≠ t)
    (hu4 : u.val < 4) (ht4 : t.val < 4) (hu : ∀ i, k4_Adj u i → i ∈ ineligSet 10 D)
    (ht : ∀ i, k4_Adj t i → i ∈ ineligSet 10 D) : False := by
  obtain ⟨mu, xu, ρu, hρu, cu⟩ := k4_sat h hC b hb hpos hres hu4 hu
  obtain ⟨mt, xt, ρt, hρt, ct⟩ := k4_sat h hC b hb hpos hres ht4 ht
  have hcr := card_residual h.1 b hb
  have hρ : ρu = ρt := Finset.card_le_one.mp (by omega) ρu hρu ρt hρt
  rw [← hρ] at ct
  have hfan : 2 ≤ fanout D ρu.1 := by
    unfold residualUnits unitsPlus at hρu
    have := (mem_units.mp (Finset.mem_filter.mp (Finset.mem_sdiff.mp hρu).1).1).2
    omega
  obtain ⟨e1, e2, hne, a1, a2, b1, b2⟩ := k4_joint_exits k4_gr h hC mu mt cu ct hfan
  obtain ⟨i1, p1, q1⟩ := xu e1 a1
  obtain ⟨i1', p1', q1'⟩ := xt e1 a2
  obtain ⟨i2, p2, q2⟩ := xu e2 b1
  obtain ⟨i2', p2', q2'⟩ := xt e2 b2
  have r1 : i1 = i1' := hpos.2 i1 (hu i1 p1) i1' (ht i1' p1') (q1.symm.trans q1')
  have r2 : i2 = i2' := hpos.2 i2 (hu i2 p2) i2' (ht i2' p2') (q2.symm.trans q2')
  rw [← r1] at p1'
  rw [← r2] at p2'
  have r3 : i1 = i2 := k4_common u t i1 i2 hut p1 p1' p2 p2'
  exact hne (by rw [q1, q2, r3])

theorem k4_tri {D : Dag} (h : StrictLive 10 D) (hC : sem_Comp 10 k4_Adj D) (b : Fin 10 → ℕ)
    (hb : PureBranch 10 D b) {pos : Fin 10 → ℕ × Bool} (hpos : k4_Pos 10 k4_Adj D pos)
    (hres : Bplus 10 D ≤ (eligSet 10 D).card + 2)
    (hall : ∀ i : Fin 10, 4 ≤ i.val → i ∈ ineligSet 10 D)
    (T : Finset (Fin 10)) (a z i1 i2 x y w : Fin 10) (hT : T.card = 3) (haT : a ∈ T)
    (haz : k4_Adj a z)
    (hind : ∀ u ∈ insert z (T.erase a), ∀ v ∈ insert z (T.erase a), ¬ k4_Adj u v)
    (hcov : ∀ i : Fin 10, 4 ≤ i.val → ∃ t ∈ T, k4_Adj i t)
    (huniq : ∀ i : Fin 10, 4 ≤ i.val → (∀ t ∈ T.erase a, ¬ k4_Adj i t) → i = z)
    (hpair : x ∈ T ∧ y ∈ T ∧ w ∈ T ∧ x ≠ y ∧ x ≠ w ∧ y ≠ w ∧ 4 ≤ i1.val ∧ 4 ≤ i2.val ∧
      k4_Adj i1 x ∧ k4_Adj i1 y ∧ k4_Adj i2 x ∧ k4_Adj i2 w) :
    Disjoint (supp 10 D (src D (pos z))) (T.erase a) := by
  have hbud := k4_budget k4_gr h hC b hb T
  obtain ⟨hsub, hcd⟩ := k4_exits_ge hpos T (Finset.univ.filter (fun i : Fin 10 => 4 ≤ i.val))
    (fun i hi => ⟨hall i (Finset.mem_filter.mp hi).2, hcov i (Finset.mem_filter.mp hi).2⟩)
  have h6 := k4_six
  have hmer : 2 ≤ (merges 10 D (carrierT 10 D T)).card := by
    obtain ⟨hx, hy, hw, hxy, hxw, hyw, h1, h2, a1, a2, a3, a4⟩ := hpair
    exact k4_pair_merges h.1 hT hx hy hw hxy hxw hyw
      ((hpos.1 i1 (hall i1 h1)).2.2.1 x a1) ((hpos.1 i1 (hall i1 h1)).2.2.1 y a2)
      ((hpos.1 i2 (hall i2 h2)).2.2.1 x a3) ((hpos.1 i2 (hall i2 h2)).2.2.1 w a4)
  have hEq := Finset.eq_of_subset_of_card_le hsub (by omega)
  obtain ⟨j, s, hj, ht, s1, s2, hd⟩ := sem_exposure k4_gr h.1 hC (insert z (T.erase a)) hind a
    ⟨z, Finset.mem_insert_self _ _, haz⟩
  have hmem : (j, s) ∈ exitArcs 10 D (carrierT 10 D T) := by
    rw [k4_mem_exit]
    refine ⟨hj, ⟨a, Finset.mem_inter.mpr ⟨s1, haT⟩⟩, ?_⟩
    rintro ⟨v, hv⟩
    rw [Finset.mem_inter] at hv
    have hv1 := sem_supp_and_sub h.1 hj ht s hv.1
    by_cases hva : v = a
    · exact s2 (hva ▸ hv.1)
    · exact Finset.disjoint_left.mp hd hv1
        (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hva, hv.2⟩))
  rw [← hEq] at hmem
  obtain ⟨i, hi, hie⟩ := Finset.mem_image.mp hmem
  have hi4 := (Finset.mem_filter.mp hi).2
  have hiz : i = z := huniq i hi4 (fun t ht' hit => by
    have h5 := (hpos.1 i (hall i hi4)).2.2.1 t hit
    rw [hie] at h5
    exact Finset.disjoint_left.mp hd h5 (Finset.mem_insert_of_mem ht'))
  rw [hiz] at hie
  rw [hie]
  exact hd.mono_right (Finset.subset_insert _ _)

theorem k4_case4 {D : Dag} (h : StrictLive 10 D) (hC : sem_Comp 10 k4_Adj D) (b : Fin 10 → ℕ)
    (hb : PureBranch 10 D b) {pos : Fin 10 → ℕ × Bool} (hpos : k4_Pos 10 k4_Adj D pos)
    (hres : Bplus 10 D ≤ (eligSet 10 D).card + 2)
    (hall : ∀ i : Fin 10, 4 ≤ i.val → i ∈ ineligSet 10 D) : False := by
  have F1 := k4_tri h hC b hb hpos hres hall {1, 2, 3} 1 4 7 9 2 1 3 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have F2 := k4_tri h hC b hb hpos hres hall {1, 2, 3} 2 5 7 9 2 1 3 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have F3 := k4_tri h hC b hb hpos hres hall {0, 2, 3} 2 7 5 9 2 0 3 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have q : ∀ i : Fin 10, 4 ≤ i.val → ∀ a, k4_Adj i a → a ∈ supp 10 D (src D (pos i)) :=
    fun i hi => (hpos.1 i (hall i hi)).2.2.1
  have n4 : (2 : Fin 10) ∉ supp 10 D (src D (pos 4)) :=
    fun hc => Finset.disjoint_left.mp F1 hc (by decide)
  have n5 : (1 : Fin 10) ∉ supp 10 D (src D (pos 5)) :=
    fun hc => Finset.disjoint_left.mp F2 hc (by decide)
  have n7 : (0 : Fin 10) ∉ supp 10 D (src D (pos 7)) :=
    fun hc => Finset.disjoint_left.mp F3 hc (by decide)
  have hbud := k4_budget k4_gr h hC b hb ({0, 1, 2} : Finset (Fin 10))
  obtain ⟨hsub, hcd⟩ := k4_exits_ge hpos ({0, 1, 2} : Finset (Fin 10))
    (Finset.univ.filter (fun i : Fin 10 => 4 ≤ i.val))
    (fun i hi => ⟨hall i (Finset.mem_filter.mp hi).2, k4_meets012 i (Finset.mem_filter.mp hi).2⟩)
  have hex := Finset.card_le_card hsub
  have h6 := k4_six
  have hT : ({0, 1, 2} : Finset (Fin 10)).card = 3 := by decide
  have mk : ∀ (i a c : Fin 10), 4 ≤ i.val → k4_Adj i a → k4_Adj i c → a ≠ c →
      a ∈ ({0, 1, 2} : Finset (Fin 10)) → c ∈ ({0, 1, 2} : Finset (Fin 10)) →
      a ∈ supp 10 D (src D (pos i)) ∩ {0, 1, 2} ∧ c ∈ supp 10 D (src D (pos i)) ∩ {0, 1, 2} ∧
        2 ≤ (supp 10 D (src D (pos i)) ∩ ({0, 1, 2} : Finset (Fin 10))).card := by
    intro i a c hi ha hc hac haT hcT
    have m1 := Finset.mem_inter.mpr ⟨q i hi a ha, haT⟩
    have m2 := Finset.mem_inter.mpr ⟨q i hi c hc, hcT⟩
    exact ⟨m1, m2, Finset.one_lt_card.mpr ⟨a, m1, c, m2, hac⟩⟩
  obtain ⟨a40, a41, c4⟩ := mk 4 0 1 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  obtain ⟨a50, a52, c5⟩ := mk 5 0 2 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  obtain ⟨a71, a72, c7⟩ := mk 7 1 2 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  obtain ⟨g4, hg4, e4⟩ := k4_mask_gate h.1 _ _ c4
  obtain ⟨g5, hg5, e5⟩ := k4_mask_gate h.1 _ _ c5
  obtain ⟨g7, hg7, e7⟩ := k4_mask_gate h.1 _ _ c7
  have d45 : g4 ≠ g5 := by
    intro he
    rw [he, e5] at e4
    rw [e4] at a52
    exact n4 (Finset.mem_inter.mp a52).1
  have d47 : g4 ≠ g7 := by
    intro he
    rw [he, e7] at e4
    rw [e4] at a72
    exact n4 (Finset.mem_inter.mp a72).1
  have d57 : g5 ≠ g7 := by
    intro he
    rw [he, e7] at e5
    rw [e5] at a71
    exact n5 (Finset.mem_inter.mp a71).1
  have hmer : 3 ≤ (merges 10 D (carrierT 10 D ({0, 1, 2} : Finset (Fin 10)))).card :=
    Finset.two_lt_card.mpr ⟨g4, hg4, g5, hg5, g7, hg7, d45, d47, d57⟩
  omega

theorem k4_surplus_seven {D : Dag} (h : StrictLive 10 D) (hC : sem_Comp 10 k4_Adj D)
    (h4 : (4 : Fin 10) ∈ ineligSet 10 D) (h9 : (9 : Fin 10) ∈ ineligSet 10 D) :
    7 ≤ totalSurplus 10 D := by
  by_contra hlt
  have hsix := k4_surplus_six h hC
  have hle := Bplus_le_total 10 D
  obtain ⟨b, hb⟩ := sem_exists_pureBranch k4_gr h.1 hC
  have hp := elig_le_Bplus h.1 b hb
  have hcard := inelig_card_add 10 D
  obtain ⟨pos, hpos⟩ := k4_assigned k4_gr h hC
  have hind := k4_inelig_indep h hC
  have hU : ∀ q ∈ ineligSet 10 D, 4 ≤ q.val := by
    intro q hq
    by_contra hc
    rcases k4_orig_adj q (by omega) with h1 | h1
    · rw [hind q hq 4 h4] at h1; exact Bool.false_ne_true h1
    · rw [hind q hq 9 h9] at h1; exact Bool.false_ne_true h1
  have hIsub : ineligSet 10 D ⊆ Finset.univ.filter (fun i : Fin 10 => 4 ≤ i.val) :=
    fun q hq => Finset.mem_filter.mpr ⟨Finset.mem_univ q, hU q hq⟩
  have hI6 := Finset.card_le_card hIsub
  rw [k4_six] at hI6
  have hp5 : (eligSet 10 D).card ≤ 5 := by
    by_cases hex : ∃ i ∈ ineligSet 10 D, i ≠ 4 ∧ i ≠ 9
    · obtain ⟨i, hi, hi4, hi9⟩ := hex
      obtain ⟨u, i3, a1, a2, a3, d1, d2⟩ := k4_share i (hU i hi) hi4 hi9
      have h3 := k4_three_cons k4_gr h hC hpos h4 hi (Ne.symm hi4) d1 d2 a1 a2 a3
      have hbud := k4_budget k4_gr h hC b hb ({u} : Finset (Fin 10))
      rw [Finset.card_singleton] at hbud
      omega
    · have hsub2 : ineligSet 10 D ⊆ ({4, 9} : Finset (Fin 10)) := by
        intro i hi
        by_contra hc
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
        exact hex ⟨i, hi, hc.1, hc.2⟩
      have := Finset.card_le_card hsub2
      have h2 : ({4, 9} : Finset (Fin 10)).card = 2 := by decide
      omega
  have hsd := Finset.card_sdiff_add_card_eq_card hIsub
  rw [k4_six] at hsd
  have hd1 : (Finset.univ.filter (fun i : Fin 10 => 4 ≤ i.val) \ ineligSet 10 D).card ≤ 1 := by
    omega
  have hone : ∀ v v' : Fin 10, 4 ≤ v.val → 4 ≤ v'.val → v ∉ ineligSet 10 D →
      v' ∉ ineligSet 10 D → v = v' := fun v v' hv hv' nv nv' =>
    Finset.card_le_one.mp hd1 v
      (Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩, nv⟩) v'
      (Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ v', hv'⟩, nv'⟩)
  by_cases hall : ∀ i : Fin 10, 4 ≤ i.val → i ∈ ineligSet 10 D
  · exact k4_case4 h hC b hb hpos (by omega) hall
  · rw [not_forall] at hall
    obtain ⟨v, hv⟩ := hall
    rw [Classical.not_imp] at hv
    obtain ⟨hv4, hvn⟩ := hv
    have hlt5 : (ineligSet 10 D).card < 6 := by
      have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hIsub, fun he =>
        hvn (he ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv4⟩)⟩)
      rw [k4_six] at this
      exact this
    have hIv : ∀ i : Fin 10, 4 ≤ i.val ∧ i ≠ v → i ∈ ineligSet 10 D := by
      intro i hi
      by_contra hc
      exact hi.2 (hone i v hi.1 hv4 hc hvn)
    obtain ⟨u, t, hut, hu4, ht4, nu, nt⟩ := k4_opp v hv4
    exact k4_case5 h hC b hb hpos (by omega) hut hu4 ht4 (fun i hi => hIv i (nu i hi))
      (fun i hi => hIv i (nt i hi))

def k4_ofList (l : List ℕ) (v : Fin 10) : Fin 10 := Fin.ofNat 10 (l.getD v.val 0)

def k4_swap12 : Equiv.Perm (Fin 10) :=
  ⟨k4_ofList [0, 2, 1, 3, 5, 4, 6, 7, 9, 8], k4_ofList [0, 2, 1, 3, 5, 4, 6, 7, 9, 8],
    by intro x; revert x; decide +kernel, by intro x; revert x; decide +kernel⟩

def k4_swap13 : Equiv.Perm (Fin 10) :=
  ⟨k4_ofList [0, 3, 2, 1, 6, 5, 4, 9, 8, 7], k4_ofList [0, 3, 2, 1, 6, 5, 4, 9, 8, 7],
    by intro x; revert x; decide +kernel, by intro x; revert x; decide +kernel⟩

theorem k4_swap12_aut : ∀ u v : Fin 10, k4_Adj u v ↔ k4_Adj (k4_swap12 u) (k4_swap12 v) := by
  decide +kernel

theorem k4_swap13_aut : ∀ u v : Fin 10, k4_Adj u v ↔ k4_Adj (k4_swap13 u) (k4_swap13 v) := by
  decide +kernel

theorem k4_surplus_seven_matching {D : Dag} (h : StrictLive 10 D) (hC : sem_Comp 10 k4_Adj D)
    {i1 i2 : Fin 10} (h1 : i1 ∈ ineligSet 10 D) (h2 : i2 ∈ ineligSet 10 D)
    (hm : (i1 = 4 ∧ i2 = 9) ∨ (i1 = 5 ∧ i2 = 8) ∨ (i1 = 6 ∧ i2 = 7)) :
    7 ≤ totalSurplus 10 D := by
  have key : ∀ σ : Equiv.Perm (Fin 10), (∀ u v : Fin 10, k4_Adj u v ↔ k4_Adj (σ u) (σ v)) →
      σ i1 = 4 → σ i2 = 9 → 7 ≤ totalSurplus 10 D := by
    intro σ hσ e1 e2
    rw [← relabel_totalSurplus σ D]
    refine k4_surplus_seven (relabel_strictLive σ h) (k4_relabel_comp σ hσ h hC) ?_ ?_
    · rw [relabel_ineligSet σ h.1, ← e1]; exact Finset.mem_image_of_mem σ h1
    · rw [relabel_ineligSet σ h.1, ← e2]; exact Finset.mem_image_of_mem σ h2
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact k4_surplus_seven h hC h1 h2
  · exact key k4_swap12 k4_swap12_aut (by decide) (by decide)
  · exact key k4_swap13 k4_swap13_aut (by decide) (by decide)

theorem k4_surplus_seven_iso {G : Fin 10 → Fin 10 → Prop} (σ : Equiv.Perm (Fin 10))
    (hσ : ∀ u v, G u v ↔ k4_Adj (σ u) (σ v)) {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 G D) {i1 i2 : Fin 10} (h1 : i1 ∈ ineligSet 10 D)
    (h2 : i2 ∈ ineligSet 10 D)
    (hm : (σ i1 = 4 ∧ σ i2 = 9) ∨ (σ i1 = 5 ∧ σ i2 = 8) ∨ (σ i1 = 6 ∧ σ i2 = 7)) :
    7 ≤ totalSurplus 10 D := by
  rw [← relabel_totalSurplus σ D]
  refine k4_surplus_seven_matching (relabel_strictLive σ h) (k4_relabel_comp σ hσ h hC)
    (i1 := σ i1) (i2 := σ i2) ?_ ?_ hm
  · rw [relabel_ineligSet σ h.1]; exact Finset.mem_image_of_mem σ h1
  · rw [relabel_ineligSet σ h.1]; exact Finset.mem_image_of_mem σ h2

def cof_ext {n m : ℕ} (ρ : Fin n → Option Bool) (ι : Fin m → Fin n) (y : Fin m → Bool) :
    Fin n → Bool :=
  fun v => (ρ v).getD (decide (∃ i : Fin m, ι i = v ∧ y i = true))

def cof_Ok {n m : ℕ} (ρ : Fin n → Option Bool) (ι : Fin m → Fin n) : Prop :=
  Function.Injective ι ∧ ∀ v, ρ v = none ↔ ∃ i, ι i = v

theorem cof_ext_free {n m : ℕ} {ρ : Fin n → Option Bool} {ι : Fin m → Fin n}
    (hok : cof_Ok ρ ι) (y : Fin m → Bool) (i : Fin m) : cof_ext ρ ι y (ι i) = y i := by
  have h : ρ (ι i) = none := (hok.2 _).mpr ⟨i, rfl⟩
  unfold cof_ext
  rw [h, Option.getD_none]
  by_cases hy : y i = true
  · rw [hy, decide_eq_true_eq]; exact ⟨i, rfl, hy⟩
  · rw [Bool.not_eq_true] at hy
    rw [hy, decide_eq_false_iff_not]
    rintro ⟨i', h1, h2⟩
    rw [hok.1 h1, hy] at h2
    exact Bool.false_ne_true h2

theorem cof_ext_fixed {n m : ℕ} {ρ : Fin n → Option Bool} (ι : Fin m → Fin n)
    (y : Fin m → Bool) {v : Fin n} {b : Bool} (h : ρ v = some b) : cof_ext ρ ι y v = b := by
  unfold cof_ext; rw [h, Option.getD_some]

theorem cof_ext_agree {n m : ℕ} {ρ : Fin n → Option Bool} {ι : Fin m → Fin n}
    (hok : cof_Ok ρ ι) {y y' : Fin m → Bool} {i : Fin m} (h : ∀ k, k ≠ i → y k = y' k) :
    ∀ v, v ≠ ι i → cof_ext ρ ι y v = cof_ext ρ ι y' v := by
  intro v hv
  cases hr : ρ v with
  | some b => rw [cof_ext_fixed ι y hr, cof_ext_fixed ι y' hr]
  | none =>
    obtain ⟨k, rfl⟩ := (hok.2 v).mp hr
    rw [cof_ext_free hok, cof_ext_free hok]
    exact h k (fun hc => hv (by rw [hc]))

theorem cof_ext_single {n m : ℕ} {ρ : Fin n → Option Bool} {ι : Fin m → Fin n}
    (hok : cof_Ok ρ ι) (i : Fin m) (v : Fin n) :
    cof_ext ρ ι (single i) v = true ↔ v = ι i ∨ ρ v = some true := by
  cases hr : ρ v with
  | some b =>
    have hne : v ≠ ι i := fun hc => by
      rw [hc, (hok.2 _).mpr ⟨i, rfl⟩] at hr
      cases hr
    rw [cof_ext_fixed ι _ hr]
    simp [hne]
  | none =>
    obtain ⟨k, rfl⟩ := (hok.2 v).mp hr
    rw [cof_ext_free hok]
    simp [single, hok.1.eq_iff]

theorem cof_gate_src {n : ℕ} {D : Dag} (hS : Strict n D) {j : ℕ} (hj : j < D.length) (s : Bool)
    (x : Fin n → Bool) :
    val D x (n + j) = gop (tag D j) (val D x (src D (j, s))) (val D x (src D (j, !s))) := by
  rw [val_gate hS x j hj]
  cases s
  · simp [src]
  · cases tag D j <;> simp [src, Bool.and_comm, Bool.or_comm]

theorem cof_sum_sub_one (f : ℕ → ℕ) (K : Finset ℕ) (h : ∀ w ∈ K, 1 ≤ f w) :
    ∑ w ∈ K, (f w - 1) + K.card = ∑ w ∈ K, f w := by
  rw [Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun w hw => Nat.sub_add_cancel (h w hw))

theorem cof_snoc (E : Dag) (g : Bool × ℕ × ℕ) :
    opA (E ++ [g]) E.length = g.2.1 ∧ opB (E ++ [g]) E.length = g.2.2 ∧
      tag (E ++ [g]) E.length = g.1 ∧
      ∀ i, i < E.length → opA (E ++ [g]) i = opA E i ∧ opB (E ++ [g]) i = opB E i := by
  refine ⟨?_, ?_, ?_, fun i hi => ?_⟩
  · unfold opA; rw [na_getD_snoc]
  · unfold opB; rw [na_getD_snoc]
  · unfold tag; rw [na_getD_snoc]
  · unfold opA opB; rw [na_getD_append_lt E [g] i hi]; exact ⟨rfl, rfl⟩

theorem cof_val_snoc {m : ℕ} {E : Dag} {g : Bool × ℕ × ℕ} (hSE : Strict m (E ++ [g]))
    (y : Fin m → Bool) :
    (∀ w, w < m + E.length → val (E ++ [g]) y w = val E y w) ∧
      val (E ++ [g]) y (m + E.length) = gop g.1 (val E y g.2.1) (val E y g.2.2) := by
  have hpre : ∀ w, w < m + E.length → val (E ++ [g]) y w = val E y w := by
    intro w hw
    have h := val_take (E ++ [g]) y E.length w hw (by simp)
    rw [← h]; simp
  refine ⟨hpre, ?_⟩
  have hlen : E.length < (E ++ [g]).length := by simp
  obtain ⟨ha, hb, -⟩ := hSE E.length hlen
  obtain ⟨e1, e2, e3, -⟩ := cof_snoc E g
  rw [val_gate hSE y E.length hlen, e3]
  rw [e1] at ha
  rw [e2] at hb
  rw [e1, e2, hpre _ ha, hpre _ hb]

noncomputable section CofRestrict

open Classical

variable {n m : ℕ} (D : Dag) (ρ : Fin n → Option Bool) (ι : Fin m → Fin n)

def cof_const (w : ℕ) : Prop :=
  ∀ y y' : Fin m → Bool, val D (cof_ext ρ ι y) w = val D (cof_ext ρ ι y') w

def cof_live (w : ℕ) : Prop :=
  ¬ cof_const D ρ ι w ∧
    Relation.ReflTransGen (fun a b => sem_step n D a b ∧ ¬ cof_const D ρ ι b) w (outW n D)

def cof_deg (w : ℕ) : ℕ := ((readers D w).filter (fun j => cof_live D ρ ι (n + j))).card

def cof_supp (w : ℕ) : Finset (Fin m) :=
  Finset.univ.filter (fun i => val D (cof_ext ρ ι (single i)) w = true)

def cof_sur : ℕ := ∑ w ∈ (inner n D).filter (fun w => cof_live D ρ ι w), (cof_deg D ρ ι w - 1)

def cof_surP : ℕ :=
  ∑ w ∈ (inner n D).filter (fun w => cof_live D ρ ι w ∧ (cof_supp D ρ ι w).Nonempty),
    (cof_deg D ρ ι w - 1)

def cof_fib (t : ℕ → ℕ) (e : ℕ) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => cof_live D ρ ι w ∧ t w = e)

variable {D ρ ι}

theorem cof_mem_supp {w : ℕ} {i : Fin m} :
    i ∈ cof_supp D ρ ι w ↔ val D (cof_ext ρ ι (single i)) w = true := by
  simp [cof_supp]

theorem cof_live_lt {w : ℕ} (h : cof_live D ρ ι w) : w < n + D.length := by
  by_contra hc
  exact h.1 (fun y y' => by rw [val_ge D _ w (by omega), val_ge D _ w (by omega)])

theorem cof_live_of_step {a c : ℕ} (hs : sem_step n D a c) (ha : ¬ cof_const D ρ ι a)
    (hc : cof_live D ρ ι c) : cof_live D ρ ι a :=
  ⟨ha, Relation.ReflTransGen.head ⟨hs, hc.1⟩ hc.2⟩

theorem cof_live_reader {w : ℕ} (h : cof_live D ρ ι w) (hne : w ≠ outW n D) :
    ∃ c, sem_step n D w c ∧ cof_live D ρ ι c := by
  rcases Relation.ReflTransGen.cases_head h.2 with heq | ⟨c, hs, hrest⟩
  · exact absurd heq hne
  · exact ⟨c, hs.1, hs.2, hrest⟩

theorem cof_deg_le (w : ℕ) : cof_deg D ρ ι w ≤ fanout D w := Finset.card_filter_le _ _

theorem cof_deg_pos {w : ℕ} (h : cof_live D ρ ι w) (hne : w ≠ outW n D) :
    1 ≤ cof_deg D ρ ι w := by
  obtain ⟨c, hs, hc⟩ := cof_live_reader h hne
  refine Finset.card_pos.mpr ⟨c - n, Finset.mem_filter.mpr ⟨sem_step_reader hs, ?_⟩⟩
  rw [Nat.add_sub_cancel' hs.2.1]
  exact hc

theorem cof_const_of_true (hS : Strict n D) {c : Fin n} (hc : ρ c = some true) {w : ℕ}
    (hw : c ∈ supp n D w) : cof_const D ρ ι w := by
  intro y y'
  rw [sem_val_of_supp hS hw (cof_ext_fixed ι y hc), sem_val_of_supp hS hw (cof_ext_fixed ι y' hc)]

theorem cof_not_live_of_true (hS : Strict n D) {c : Fin n} (hc : ρ c = some true) {w : ℕ}
    (hw : c ∈ supp n D w) : ¬ cof_live D ρ ι w :=
  fun h => h.1 (cof_const_of_true hS hc hw)

theorem cof_live_input (hok : cof_Ok ρ ι) {w : ℕ} (hw : w < n) (hl : cof_live D ρ ι w) :
    ∃ i : Fin m, (ι i).val = w := by
  cases hr : ρ ⟨w, hw⟩ with
  | some b =>
    exact absurd (fun y y' => by
      rw [val_input D _ w hw, val_input D _ w hw, cof_ext_fixed ι y hr, cof_ext_fixed ι y' hr]) hl.1
  | none =>
    obtain ⟨i, hi⟩ := (hok.2 _).mp hr
    exact ⟨i, by rw [hi]⟩

theorem cof_live_free (hS : Strict n D) (hok : cof_Ok ρ ι) (i : Fin m)
    (hess : ∃ y y' : Fin m → Bool, (∀ k, k ≠ i → y k = y' k) ∧
      val D (cof_ext ρ ι y) (outW n D) ≠ val D (cof_ext ρ ι y') (outW n D)) :
    cof_live D ρ ι (ι i).val := by
  obtain ⟨y, y', hyy, hne⟩ := hess
  have hp := sem_changed_path hS _ _ (ι i) (cof_ext_agree hok hyy) _ hne
  refine ⟨fun hc => hne ?_, sem_rtg_mono (fun a b h => ⟨h.1, fun hc => h.2 (hc y y')⟩) hp⟩
  have h1 := hc y y'
  rw [val_input D _ _ (ι i).isLt, val_input D _ _ (ι i).isLt, Fin.eta, cof_ext_free hok,
    cof_ext_free hok] at h1
  have hyy2 : y = y' := by
    funext k
    by_cases hk : k = i
    · rw [hk]; exact h1
    · exact hyy k hk
  rw [hyy2]

theorem cof_gate_const (hS : Strict n D) {j : ℕ} (hj : j < D.length)
    (ha : cof_const D ρ ι (opA D j)) (hb : cof_const D ρ ι (opB D j)) :
    cof_const D ρ ι (n + j) := by
  intro y y'
  rw [val_gate hS _ j hj, val_gate hS _ j hj, ha y y', hb y y']

theorem cof_live_op (hS : Strict n D) {j : ℕ} (hj : j < D.length)
    (hl : cof_live D ρ ι (n + j)) : ∃ s, cof_live D ρ ι (src D (j, s)) := by
  by_cases ha : cof_const D ρ ι (opA D j)
  · by_cases hb : cof_const D ρ ι (opB D j)
    · exact absurd (cof_gate_const hS hj ha hb) hl.1
    · exact ⟨true, cof_live_of_step (sem_step_src hj true) (by rw [sb_src_true]; exact hb) hl⟩
  · exact ⟨false, cof_live_of_step (sem_step_src hj false) (by rw [sb_src_false]; exact ha) hl⟩

theorem cof_unary (hS : Strict n D) {j : ℕ} (hj : j < D.length) (s : Bool)
    (hc : cof_const D ρ ι (src D (j, !s))) (hn : ¬ cof_const D ρ ι (n + j)) :
    ∀ y, val D (cof_ext ρ ι y) (n + j) = val D (cof_ext ρ ι y) (src D (j, s)) := by
  intro y
  have key : ∀ y', val D (cof_ext ρ ι y') (n + j) = gop (tag D j)
      (val D (cof_ext ρ ι y') (src D (j, s))) (val D (cof_ext ρ ι y) (src D (j, !s))) :=
    fun y' => by rw [cof_gate_src hS hj s, hc y' y]
  rw [key y]
  cases ht : tag D j <;> cases hv : val D (cof_ext ρ ι y) (src D (j, !s))
  · simp
  · exfalso; apply hn; intro y1 y2; rw [key y1, key y2, ht, hv]; simp
  · exfalso; apply hn; intro y1 y2; rw [key y1, key y2, ht, hv]; simp
  · simp

def cof_Inv (D : Dag) (ρ : Fin n → Option Bool) (ι : Fin m → Fin n) (k : ℕ) (E : Dag)
    (t q : ℕ → ℕ) : Prop :=
  Strict m E ∧
  (∀ w, w < n + k → cof_live D ρ ι w →
    t w < m + E.length ∧ ∀ y, val E y (t w) = val D (cof_ext ρ ι y) w) ∧
  (∀ i, i < E.length → q i < k ∧ cof_live D ρ ι (n + q i) ∧ t (n + q i) = m + i ∧
    opA E i = t (opA D (q i)) ∧ opB E i = t (opB D (q i)) ∧
    cof_live D ρ ι (opA D (q i)) ∧ cof_live D ρ ι (opB D (q i))) ∧
  (∀ j, j < k → cof_live D ρ ι (n + j) → (∃ i, i < E.length ∧ q i = j) ∨
    ∀ s, cof_live D ρ ι (src D (j, s)) → t (src D (j, s)) = t (n + j)) ∧
  (∀ i : Fin m, t (ι i).val = i.val)

theorem cof_inv_zero (hok : cof_Ok ρ ι) : ∃ E t q, cof_Inv D ρ ι 0 E t q := by
  have hch : ∀ w : ℕ, ∃ r : ℕ, ∀ i : Fin m, (ι i).val = w → r = i.val := by
    intro w
    by_cases h : ∃ i : Fin m, (ι i).val = w
    · obtain ⟨i, hi⟩ := h
      exact ⟨i.val, fun i' hi' => by rw [hok.1 (Fin.ext (hi.trans hi'.symm))]⟩
    · exact ⟨0, fun i hi => absurd ⟨i, hi⟩ h⟩
  choose t ht using hch
  refine ⟨[], t, fun _ => 0, fun j hj => absurd hj (by simp), ?_,
    fun i hi => absurd hi (by simp), fun j hj => absurd hj (by simp), fun i => ht _ i rfl⟩
  intro w hw hl
  rw [Nat.add_zero] at hw
  obtain ⟨i, hi⟩ := cof_live_input hok hw hl
  have e := ht w i hi
  have hwi : (⟨w, hw⟩ : Fin n) = ι i := Fin.ext hi.symm
  refine ⟨by rw [e]; simp, fun y => ?_⟩
  rw [e, val_input [] y i.val i.isLt, val_input D _ w hw, hwi, cof_ext_free hok]

theorem cof_inv_step (hS : Strict n D) {k : ℕ} (hk : k < D.length) {E : Dag} {t q : ℕ → ℕ}
    (h : cof_Inv D ρ ι k E t q) : ∃ E' t' q', cof_Inv D ρ ι (k + 1) E' t' q' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  obtain ⟨hA, hB, -⟩ := hS k hk
  by_cases hl : cof_live D ρ ι (n + k)
  swap
  · refine ⟨E, t, q, h1, fun w hw hlw => ?_, fun i hi => ?_, fun j hj hlj => ?_, h5⟩
    · have hne : w ≠ n + k := fun hc => hl (hc ▸ hlw)
      exact h2 w (by omega) hlw
    · obtain ⟨a, b⟩ := h3 i hi
      exact ⟨by omega, b⟩
    · have hne : j ≠ k := fun hc => hl (hc ▸ hlj)
      exact h4 j (by omega) hlj
  have hold : ∀ (v : ℕ) (w : ℕ), w < n + k → Function.update t (n + k) v w = t w :=
    fun v w hw => Function.update_of_ne (by omega) _ _
  by_cases hc : cof_live D ρ ι (opA D k) ∧ cof_live D ρ ι (opB D k) ∧
      t (opA D k) ≠ t (opB D k)
  · obtain ⟨la, lb, hne⟩ := hc
    obtain ⟨ta, va⟩ := h2 _ hA la
    obtain ⟨tb, vb⟩ := h2 _ hB lb
    have hSE : Strict m (E ++ [(tag D k, t (opA D k), t (opB D k))]) :=
      na_strict_snoc h1 _ _ _ ta tb hne
    obtain ⟨e1, e2, -, e4⟩ := cof_snoc E (tag D k, t (opA D k), t (opB D k))
    have hlen : (E ++ [(tag D k, t (opA D k), t (opB D k))]).length = E.length + 1 := by simp
    refine ⟨_, Function.update t (n + k) (m + E.length), Function.update q E.length k, hSE,
      fun w hw hlw => ?_, fun i hi => ?_, fun j hj hlj => ?_, fun i => ?_⟩
    · rw [hlen]
      by_cases hwk : w = n + k
      · rw [hwk, Function.update_self]
        refine ⟨by omega, fun y => ?_⟩
        rw [(cof_val_snoc hSE y).2, va y, vb y, val_gate hS _ k hk]
      · obtain ⟨tw, vw⟩ := h2 w (by omega) hlw
        rw [hold _ w (by omega)]
        exact ⟨by omega, fun y => by rw [(cof_val_snoc hSE y).1 _ tw, vw y]⟩
    · rw [hlen] at hi
      by_cases hi' : i < E.length
      · obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h3 i hi'
        obtain ⟨sa, sb, -⟩ := hS (q i) (by omega)
        rw [Function.update_of_ne (by omega : i ≠ E.length), hold _ _ (by omega : n + q i < n + k),
          hold _ _ (by omega : opA D (q i) < n + k), hold _ _ (by omega : opB D (q i) < n + k),
          (e4 i hi').1, (e4 i hi').2]
        exact ⟨by omega, a2, a3, a4, a5, a6, a7⟩
      · have hie : i = E.length := by omega
        rw [hie, Function.update_self, Function.update_self, hold _ _ hA, hold _ _ hB, e1, e2]
        exact ⟨by omega, hl, rfl, rfl, rfl, la, lb⟩
    · by_cases hjk : j = k
      · exact Or.inl ⟨E.length, by omega, by rw [hjk, Function.update_self]⟩
      · rcases h4 j (by omega) hlj with ⟨i, hi, hqi⟩ | hr
        · exact Or.inl ⟨i, by omega, by rw [Function.update_of_ne (by omega : i ≠ E.length)]; exact hqi⟩
        · refine Or.inr (fun s hls => ?_)
          have hlt := sem_src_lt hS (by omega : j < D.length) s
          rw [hold _ _ (by omega), hold _ _ (by omega)]
          exact hr s hls
    · rw [hold _ _ (by have := (ι i).isLt; omega)]
      exact h5 i
  · have hAB : cof_live D ρ ι (opA D k) → cof_live D ρ ι (opB D k) →
        t (opA D k) = t (opB D k) := fun la lb => by
      by_contra hne
      exact hc ⟨la, lb, hne⟩
    obtain ⟨s0, ls0⟩ := cof_live_op hS hk hl
    have hteq : ∀ s, cof_live D ρ ι (src D (k, s)) → t (src D (k, s)) = t (src D (k, s0)) := by
      intro s hls
      cases s <;> cases s0 <;> simp only [sb_src_false, sb_src_true] at hls ls0 ⊢
      · exact hAB hls ls0
      · exact (hAB ls0 hls).symm
    obtain ⟨t0, v0⟩ := h2 _ (sem_src_lt hS hk s0) ls0
    have hval : ∀ y, val D (cof_ext ρ ι y) (n + k) = val D (cof_ext ρ ι y) (src D (k, s0)) := by
      by_cases hother : cof_const D ρ ι (src D (k, !s0))
      · exact cof_unary hS hk s0 hother hl.1
      · have lo := cof_live_of_step (sem_step_src hk (!s0)) hother hl
        obtain ⟨-, v1⟩ := h2 _ (sem_src_lt hS hk (!s0)) lo
        intro y
        rw [cof_gate_src hS hk s0, ← v1 y, hteq _ lo, v0 y]
        cases tag D k <;> simp
    refine ⟨E, Function.update t (n + k) (t (src D (k, s0))), q, h1,
      fun w hw hlw => ?_, fun i hi => ?_, fun j hj hlj => ?_, fun i => ?_⟩
    · by_cases hwk : w = n + k
      · rw [hwk, Function.update_self]
        exact ⟨t0, fun y => by rw [v0 y, hval y]⟩
      · rw [hold _ w (by omega)]
        exact h2 w (by omega) hlw
    · obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h3 i hi
      obtain ⟨sa, sb, -⟩ := hS (q i) (by omega)
      rw [hold _ _ (by omega : n + q i < n + k), hold _ _ (by omega : opA D (q i) < n + k),
        hold _ _ (by omega : opB D (q i) < n + k)]
      exact ⟨by omega, a2, a3, a4, a5, a6, a7⟩
    · by_cases hjk : j = k
      · refine Or.inr (fun s hls => ?_)
        rw [hjk] at hls ⊢
        rw [hold _ _ (sem_src_lt hS hk s), Function.update_self]
        exact hteq s hls
      · rcases h4 j (by omega) hlj with hem | hr
        · exact Or.inl hem
        · refine Or.inr (fun s hls => ?_)
          have hlt := sem_src_lt hS (by omega : j < D.length) s
          rw [hold _ _ (by omega), hold _ _ (by omega)]
          exact hr s hls
    · rw [hold _ _ (by have := (ι i).isLt; omega)]
      exact h5 i

theorem cof_inv_all (hS : Strict n D) (hok : cof_Ok ρ ι) :
    ∃ E t q, cof_Inv D ρ ι D.length E t q := by
  have h : ∀ k, k ≤ D.length → ∃ E t q, cof_Inv D ρ ι k E t q := by
    intro k
    induction k with
    | zero => exact fun _ => cof_inv_zero hok
    | succ k ih =>
      intro hk
      obtain ⟨E, t, q, hI⟩ := ih (by omega)
      exact cof_inv_step hS (by omega) hI
  exact h _ le_rfl

theorem cof_mem_arcs {a : ℕ × Bool} : a ∈ arcs D ↔ a.1 < D.length := by simp [arcs]

theorem cof_tr_mono {E : Dag} {t q : ℕ → ℕ} (hI : cof_Inv D ρ ι D.length E t q) {j : ℕ}
    (hj : j < D.length) (s : Bool) (ha : cof_live D ρ ι (src D (j, s)))
    (hc : cof_live D ρ ι (n + j)) : t (src D (j, s)) ≤ t (n + j) := by
  obtain ⟨h1, -, h3, h4, -⟩ := hI
  rcases h4 j hj hc with ⟨i, hi, hqi⟩ | hr
  · obtain ⟨-, -, e1, e2, e3, -, -⟩ := h3 i hi
    obtain ⟨sa, sb, -⟩ := h1 i hi
    rw [hqi] at e1 e2 e3
    cases s
    · rw [sb_src_false, ← e2, e1]; omega
    · rw [sb_src_true, ← e3, e1]; omega
  · exact (hr s ha).le

theorem cof_tr_le_out {E : Dag} {t q : ℕ → ℕ} (hI : cof_Inv D ρ ι D.length E t q) {w : ℕ}
    (hl : cof_live D ρ ι w) : t w ≤ t (outW n D) := by
  obtain ⟨hnc, hp⟩ := hl
  revert hnc
  induction hp using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun _ => le_rfl
  | @head a c hstep hrest ih =>
    intro hnc
    have hla : cof_live D ρ ι a := ⟨hnc, Relation.ReflTransGen.head hstep hrest⟩
    obtain ⟨j, s, hj, rfl, rfl⟩ := sem_step_iff.mp hstep.1
    exact (cof_tr_mono hI hj s hla ⟨hstep.2, hrest⟩).trans (ih hstep.2)

theorem cof_tr_reader {E : Dag} {t q : ℕ → ℕ} (hI : cof_Inv D ρ ι D.length E t q) {w : ℕ}
    (hl : cof_live D ρ ι w) (hne : t w ≠ t (outW n D)) :
    ∃ i, i < E.length ∧ (opA E i = t w ∨ opB E i = t w) := by
  obtain ⟨hnc, hp⟩ := hl
  revert hnc hne
  induction hp using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun hne _ => absurd rfl hne
  | @head a c hstep hrest ih =>
    intro hne hnc
    have hla : cof_live D ρ ι a := ⟨hnc, Relation.ReflTransGen.head hstep hrest⟩
    obtain ⟨j, s, hj, rfl, rfl⟩ := sem_step_iff.mp hstep.1
    rcases hI.2.2.2.1 j hj ⟨hstep.2, hrest⟩ with ⟨i, hi, hqi⟩ | hr
    · obtain ⟨-, -, -, e2, e3, -, -⟩ := hI.2.2.1 i hi
      rw [hqi] at e2 e3
      refine ⟨i, hi, ?_⟩
      cases s
      · left; rw [sb_src_false]; exact e2
      · right; rw [sb_src_true]; exact e3
    · have e := hr s hla
      rw [e] at hne ⊢
      exact ih hne hstep.2

theorem cof_tr_surj {E : Dag} {t q : ℕ → ℕ} (hI : cof_Inv D ρ ι D.length E t q)
    (hfree : ∀ i : Fin m, cof_live D ρ ι (ι i).val) {e : ℕ} (he : e < m + E.length) :
    ∃ w, cof_live D ρ ι w ∧ t w = e := by
  by_cases hem : e < m
  · exact ⟨_, hfree ⟨e, hem⟩, hI.2.2.2.2 ⟨e, hem⟩⟩
  · obtain ⟨-, h, e1, -⟩ := hI.2.2.1 (e - m) (by omega)
    exact ⟨_, h, by rw [e1]; omega⟩

theorem cof_tr_out {E : Dag} {t q : ℕ → ℕ} (hI : cof_Inv D ρ ι D.length E t q)
    (hfree : ∀ i : Fin m, cof_live D ρ ι (ι i).val) (hm : 0 < m)
    (hlo : cof_live D ρ ι (outW n D)) : t (outW n D) = outW m E := by
  obtain ⟨w, hw, hwe⟩ := cof_tr_surj hI hfree (e := m + E.length - 1) (by omega)
  have h1 := cof_tr_le_out hI hw
  have h2 := (hI.2.1 _ (cof_live_lt hlo) hlo).1
  show t (outW n D) = m + E.length - 1
  omega

theorem cof_tr_live {E : Dag} {t q : ℕ → ℕ} (hI : cof_Inv D ρ ι D.length E t q)
    (hfree : ∀ i : Fin m, cof_live D ρ ι (ι i).val) (hm : 0 < m)
    (hlo : cof_live D ρ ι (outW n D)) : Live m E := by
  intro e he
  obtain ⟨w, hw, hwe⟩ := cof_tr_surj hI hfree (e := e) (by omega)
  have hout : t (outW n D) = m + E.length - 1 := cof_tr_out hI hfree hm hlo
  obtain ⟨i, hi, hop⟩ := cof_tr_reader hI hw (by omega)
  rw [hwe] at hop
  exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, hop⟩⟩

theorem cof_deg_arcs (hS : Strict n D) (w : ℕ) : cof_deg D ρ ι w =
    ((arcs D).filter (fun a => src D a = w ∧ cof_live D ρ ι (n + a.1))).card := by
  rw [sb_card_arcs_filter, cof_deg, readers, Finset.filter_filter, Finset.card_filter]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hne := (hS j (Finset.mem_range.mp hj)).2.2
  rw [sb_src_false, sb_src_true]
  by_cases h1 : opA D j = w <;> by_cases h2 : opB D j = w <;>
    by_cases hl : cof_live D ρ ι (n + j) <;> simp [h1, h2, hl]
  exact hne (h1.trans h2.symm)

theorem cof_fib_bound {E : Dag} {t q : ℕ → ℕ} (hS : Strict n D) (hok : cof_Ok ρ ι)
    (hI : cof_Inv D ρ ι D.length E t q) (e : ℕ) :
    fanout E e + (cof_fib D ρ ι t e).card ≤ ∑ w ∈ cof_fib D ρ ι t e, cof_deg D ρ ι w + 1 := by
  obtain ⟨-, -, h3, h4, h5⟩ := hI
  obtain ⟨F, hF⟩ : ∃ F, F = cof_fib D ρ ι t e := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = (arcs D).filter (fun a => cof_live D ρ ι (n + a.1) ∧
      cof_live D ρ ι (src D a) ∧ t (src D a) = e) := ⟨_, rfl⟩
  rw [← hF]
  have hmemF : ∀ w, w ∈ F ↔ cof_live D ρ ι w ∧ t w = e := by
    intro w
    rw [hF, cof_fib, Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => h.2, fun h => ⟨cof_live_lt h.1, h⟩⟩
  have hmemA : ∀ a, a ∈ A ↔ a.1 < D.length ∧ cof_live D ρ ι (n + a.1) ∧
      cof_live D ρ ι (src D a) ∧ t (src D a) = e := by
    intro a
    rw [hA, Finset.mem_filter, cof_mem_arcs]
  have hcard : A.card = ∑ w ∈ F, cof_deg D ρ ι w := by
    rw [Finset.card_eq_sum_card_fiberwise (f := src D) (s := A) (t := F)
      (fun a ha => Finset.mem_coe.mpr ((hmemF _).mpr ((hmemA a).mp (Finset.mem_coe.mp ha)).2.2))]
    refine Finset.sum_congr rfl (fun w hw => ?_)
    rw [cof_deg_arcs hS w]
    congr 1
    ext a
    rw [Finset.mem_filter, Finset.mem_filter, hmemA, cof_mem_arcs]
    constructor
    · rintro ⟨⟨ha, hl, -, -⟩, rfl⟩; exact ⟨ha, rfl, hl⟩
    · rintro ⟨ha, rfl, hl⟩; exact ⟨⟨ha, hl, (hmemF _).mp hw⟩, rfl⟩
  have hsplit := Finset.card_filter_add_card_filter_not (s := A)
    (fun a : ℕ × Bool => ∃ i, i < E.length ∧ q i = a.1)
  have hem : fanout E e ≤ (A.filter (fun a : ℕ × Bool => ∃ i, i < E.length ∧ q i = a.1)).card := by
    have hex : ∀ i, ∃ a : ℕ × Bool, a.1 = q i ∧ (i ∈ readers E e →
        a ∈ A.filter (fun a : ℕ × Bool => ∃ i, i < E.length ∧ q i = a.1)) := by
      intro i
      by_cases hi : i ∈ readers E e
      · rw [readers, Finset.mem_filter, Finset.mem_range] at hi
        obtain ⟨hi1, hi2⟩ := hi
        obtain ⟨a1, a2, -, a4, a5, a6, a7⟩ := h3 i hi1
        rw [a4, a5] at hi2
        rcases hi2 with h | h
        · exact ⟨(q i, false), rfl, fun _ => Finset.mem_filter.mpr
            ⟨(hmemA _).mpr ⟨a1, a2, by rw [sb_src_false]; exact a6, by rw [sb_src_false]; exact h⟩,
              i, hi1, rfl⟩⟩
        · exact ⟨(q i, true), rfl, fun _ => Finset.mem_filter.mpr
            ⟨(hmemA _).mpr ⟨a1, a2, by rw [sb_src_true]; exact a7, by rw [sb_src_true]; exact h⟩,
              i, hi1, rfl⟩⟩
      · exact ⟨(q i, false), rfl, fun h => absurd h hi⟩
    choose φ hφ1 hφ2 using hex
    refine Finset.card_le_card_of_injOn φ (fun i hi => hφ2 i hi) (fun i hi i' hi' heq => ?_)
    have hq : q i = q i' := by rw [← hφ1 i, ← hφ1 i', heq]
    have hi1 : i ∈ readers E e := hi
    have hi1' : i' ∈ readers E e := hi'
    rw [readers, Finset.mem_filter, Finset.mem_range] at hi1 hi1'
    have e1 := (h3 i hi1.1).2.2.1
    have e2 := (h3 i' hi1'.1).2.2.1
    rw [hq] at e1
    omega
  have hsp := Finset.card_filter_add_card_filter_not (s := F)
    (fun w => w < n ∨ ∃ i, i < E.length ∧ n + q i = w)
  have hprop : (F.filter (fun w => w < n ∨ ∃ i, i < E.length ∧ n + q i = w)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_filter, hmemF] at ha hb
    obtain ⟨⟨la, ta⟩, ca⟩ := ha
    obtain ⟨⟨lb, tb⟩, cb⟩ := hb
    rcases ca with han | ⟨i, hi, rfl⟩ <;> rcases cb with hbn | ⟨i', hi', rfl⟩
    · obtain ⟨i, rfl⟩ := cof_live_input hok han la
      obtain ⟨i', rfl⟩ := cof_live_input hok hbn lb
      have e1 := h5 i
      have e2 := h5 i'
      have hii : i = i' := Fin.ext (by omega)
      rw [hii]
    · obtain ⟨i, rfl⟩ := cof_live_input hok han la
      have e1 := h5 i
      have e2 := (h3 i' hi').2.2.1
      have := i.isLt
      omega
    · obtain ⟨i', rfl⟩ := cof_live_input hok hbn lb
      have e1 := h5 i'
      have e2 := (h3 i hi).2.2.1
      have := i'.isLt
      omega
    · have e1 := (h3 i hi).2.2.1
      have e2 := (h3 i' hi').2.2.1
      have hii : i = i' := by omega
      rw [hii]
  have himp : (F.filter (fun w => ¬ (w < n ∨ ∃ i, i < E.length ∧ n + q i = w))).card ≤
      (A.filter (fun a : ℕ × Bool => ¬ ∃ i, i < E.length ∧ q i = a.1)).card := by
    have hex : ∀ w, ∃ a : ℕ × Bool, a.1 = w - n ∧
        (w ∈ F.filter (fun w => ¬ (w < n ∨ ∃ i, i < E.length ∧ n + q i = w)) →
          a ∈ A.filter (fun a : ℕ × Bool => ¬ ∃ i, i < E.length ∧ q i = a.1)) := by
      intro w
      by_cases hw : w ∈ F.filter (fun w => ¬ (w < n ∨ ∃ i, i < E.length ∧ n + q i = w))
      · have hw' := hw
        rw [Finset.mem_filter, hmemF, not_or] at hw'
        obtain ⟨⟨lw, tw⟩, hwn, hnem⟩ := hw'
        have hwlt := cof_live_lt lw
        have hj : w - n < D.length := by omega
        have hnw : n + (w - n) = w := by omega
        have hnem' : ¬ ∃ i, i < E.length ∧ q i = w - n :=
          fun ⟨i, hi, hq⟩ => hnem ⟨i, hi, by omega⟩
        have lw' : cof_live D ρ ι (n + (w - n)) := by rw [hnw]; exact lw
        have hr := (h4 (w - n) hj lw').resolve_left hnem'
        obtain ⟨s, ls⟩ := cof_live_op hS hj lw'
        exact ⟨(w - n, s), rfl, fun _ => Finset.mem_filter.mpr
          ⟨(hmemA _).mpr ⟨hj, lw', ls, by rw [hr s ls, hnw]; exact tw⟩, hnem'⟩⟩
      · exact ⟨(w - n, false), rfl, fun h => absurd h hw⟩
    choose ψ hψ1 hψ2 using hex
    refine Finset.card_le_card_of_injOn ψ (fun w hw => hψ2 w hw) (fun w hw w' hw' heq => ?_)
    have hq : w - n = w' - n := by rw [← hψ1 w, ← hψ1 w', heq]
    have h1 : w ∈ F.filter (fun w => ¬ (w < n ∨ ∃ i, i < E.length ∧ n + q i = w)) := hw
    have h1' : w' ∈ F.filter (fun w => ¬ (w < n ∨ ∃ i, i < E.length ∧ n + q i = w)) := hw'
    rw [Finset.mem_filter, not_or] at h1 h1'
    omega
  omega

theorem cof_core {E : Dag} {t q : ℕ → ℕ} (hS : Strict n D) (hok : cof_Ok ρ ι)
    (hI : cof_Inv D ρ ι D.length E t q) (hout : t (outW n D) = outW m E) (T : Finset ℕ)
    (hT : T ⊆ inner m E) :
    surplusOn E T ≤ ∑ w ∈ (inner n D).filter (fun w => cof_live D ρ ι w ∧ t w ∈ T),
      (cof_deg D ρ ι w - 1) := by
  have hout' : t (outW n D) = m + E.length - 1 := hout
  have hfib : ∀ e ∈ T, fanout E e - 1 ≤ ∑ w ∈ cof_fib D ρ ι t e, (cof_deg D ρ ι w - 1) := by
    intro e he
    have hb := cof_fib_bound hS hok hI e
    have hpos : ∀ w ∈ cof_fib D ρ ι t e, 1 ≤ cof_deg D ρ ι w := by
      intro w hw
      rw [cof_fib, Finset.mem_filter] at hw
      refine cof_deg_pos hw.2.1 (fun hc => ?_)
      have h1 := sb_mem_inner.mp (hT he)
      have h2 := hw.2.2
      rw [hc] at h2
      omega
    have := cof_sum_sub_one _ _ hpos
    omega
  have hsum := Finset.sum_fiberwise_of_maps_to
    (s := (inner n D).filter (fun w => cof_live D ρ ι w ∧ t w ∈ T)) (t := T) (g := t)
    (fun w hw => (Finset.mem_filter.mp hw).2.2) (fun w => cof_deg D ρ ι w - 1)
  rw [← hsum]
  unfold surplusOn
  refine (Finset.sum_le_sum hfib).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl (fun e he => Finset.sum_congr ?_ (fun _ _ => rfl))
  ext w
  simp only [cof_fib, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hw, lw, rfl⟩
    refine ⟨⟨sb_mem_inner.mpr ?_, lw, he⟩, rfl⟩
    have h1 := sb_mem_inner.mp (hT he)
    by_contra hc
    have hwo : w = outW n D := by unfold outW; omega
    rw [hwo] at h1
    omega
  · rintro ⟨⟨hw, lw, -⟩, rfl⟩
    exact ⟨by have := sb_mem_inner.mp hw; omega, lw, rfl⟩

theorem cof_restrict (hS : Strict n D) (hok : cof_Ok ρ ι) (hm : 2 ≤ m)
    (hess : ∀ i : Fin m, ∃ y y' : Fin m → Bool, (∀ k, k ≠ i → y k = y' k) ∧
      val D (cof_ext ρ ι y) (outW n D) ≠ val D (cof_ext ρ ι y') (outW n D)) :
    ∃ E : Dag, StrictLive m E ∧
      (∀ y, val E y (outW m E) = val D (cof_ext ρ ι y) (outW n D)) ∧
      totalSurplus m E ≤ cof_sur D ρ ι ∧ Bplus m E ≤ cof_surP D ρ ι ∧
      ∀ i : Fin m, (∀ w, Relation.ReflTransGen (sem_step n D) (ι i).val w → fanout D w ≤ 1) →
        i ∈ ineligSet m E := by
  obtain ⟨E, t, q, hI⟩ := cof_inv_all hS hok
  have hfree : ∀ i : Fin m, cof_live D ρ ι (ι i).val :=
    fun i => cof_live_free hS hok i (hess i)
  have hlo : cof_live D ρ ι (outW n D) := by
    obtain ⟨y, y', -, hne⟩ := hess ⟨0, by omega⟩
    exact ⟨fun hc => hne (hc y y'), Relation.ReflTransGen.refl⟩
  have hout := cof_tr_out hI hfree (by omega) hlo
  obtain ⟨-, hvout⟩ := hI.2.1 _ (cof_live_lt hlo) hlo
  rw [hout] at hvout
  have hne : E ≠ [] := by
    rintro rfl
    obtain ⟨y, y', hyy, hne⟩ := hess ⟨0, by omega⟩
    apply hne
    have h1 : outW m ([] : Dag) = m - 1 := by simp [outW]
    rw [← hvout y, ← hvout y', h1, val_input [] y (m - 1) (by omega),
      val_input [] y' (m - 1) (by omega)]
    exact hyy _ (fun hc => by have := congrArg Fin.val hc; simp at this; omega)
  refine ⟨E, ⟨hI.1, cof_tr_live hI hfree (by omega) hlo, hne⟩, hvout, ?_, ?_, ?_⟩
  · unfold totalSurplus cof_sur
    refine (cof_core hS hok hI hout (inner m E) (Finset.Subset.refl _)).trans
      (Finset.sum_le_sum_of_subset (fun w hw => ?_))
    rw [Finset.mem_filter] at hw ⊢
    exact ⟨hw.1, hw.2.1⟩
  · unfold Bplus cof_surP
    refine (cof_core hS hok hI hout _ (Finset.filter_subset _ _)).trans
      (Finset.sum_le_sum_of_subset (fun w hw => ?_))
    rw [Finset.mem_filter] at hw ⊢
    obtain ⟨hw1, lw, htw⟩ := hw
    have hs : supp m E (t w) = cof_supp D ρ ι w := by
      ext i
      rw [mem_supp, cof_mem_supp, (hI.2.1 w (cof_live_lt lw) lw).2]
    exact ⟨hw1, lw, by rw [← hs]; exact (Finset.mem_filter.mp htw).2⟩
  · intro i0 hprot
    rw [mem_ineligSet]
    intro e he
    have hb := cof_fib_bound hS hok hI e
    have hle : ∑ w ∈ cof_fib D ρ ι t e, cof_deg D ρ ι w ≤ (cof_fib D ρ ι t e).card := by
      rw [Finset.card_eq_sum_ones]
      refine Finset.sum_le_sum (fun w hw => ?_)
      rw [cof_fib, Finset.mem_filter] at hw
      obtain ⟨-, lw, hwe⟩ := hw
      refine (cof_deg_le w).trans (hprot w ?_)
      have hv := (hI.2.1 w (cof_live_lt lw) lw).2
      rw [← hwe] at he
      have hne : val D (cof_ext ρ ι (single i0)) w ≠ val D (cof_ext ρ ι (fun _ => false)) w := by
        rw [← hv, ← hv, mem_supp.mp he, val_zero hI.1]
        simp
      exact sem_rtg_mono (fun a b h => h.1) (sem_changed_path hS _ _ (ι i0)
        (cof_ext_agree hok (fun k hk => by simp [single, hk])) w hne)
    omega

def cof_kept (D : Dag) (ρ : Fin n → Option Bool) (ι : Fin m → Fin n) : Finset (Σ _ : ℕ, ℕ) :=
  (units n D).filter (fun u => cof_live D ρ ι u.1 ∧ u.2 + 1 < cof_deg D ρ ι u.1)

def cof_keptP (D : Dag) (ρ : Fin n → Option Bool) (ι : Fin m → Fin n) : Finset (Σ _ : ℕ, ℕ) :=
  (units n D).filter (fun u => (cof_live D ρ ι u.1 ∧ (cof_supp D ρ ι u.1).Nonempty) ∧
    u.2 + 1 < cof_deg D ρ ι u.1)

theorem cof_mem_kept {u : Σ _ : ℕ, ℕ} : u ∈ cof_kept D ρ ι ↔
    u ∈ units n D ∧ cof_live D ρ ι u.1 ∧ u.2 + 1 < cof_deg D ρ ι u.1 := Finset.mem_filter

theorem cof_mem_keptP {u : Σ _ : ℕ, ℕ} : u ∈ cof_keptP D ρ ι ↔
    u ∈ units n D ∧ (cof_live D ρ ι u.1 ∧ (cof_supp D ρ ι u.1).Nonempty) ∧
      u.2 + 1 < cof_deg D ρ ι u.1 := Finset.mem_filter

theorem cof_units_card (P : ℕ → Prop) [DecidablePred P] :
    ((units n D).filter (fun u => P u.1 ∧ u.2 + 1 < cof_deg D ρ ι u.1)).card =
      ∑ w ∈ (inner n D).filter P, (cof_deg D ρ ι w - 1) := by
  have hs : (units n D).filter (fun u => P u.1 ∧ u.2 + 1 < cof_deg D ρ ι u.1) =
      ((inner n D).filter P).sigma (fun w => Finset.range (cof_deg D ρ ι w - 1)) := by
    ext u
    have := cof_deg_le (D := D) (ρ := ρ) (ι := ι) u.1
    simp only [units, Finset.mem_filter, Finset.mem_sigma, Finset.mem_range]
    constructor
    · rintro ⟨⟨h1, -⟩, h2, h3⟩; exact ⟨⟨h1, h2⟩, by omega⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, by omega⟩, h2, by omega⟩
  rw [hs, Finset.card_sigma]
  simp

theorem cof_sur_eq : cof_sur D ρ ι = (cof_kept D ρ ι).card :=
  (cof_units_card (fun w => cof_live D ρ ι w)).symm

theorem cof_surP_eq : cof_surP D ρ ι = (cof_keptP D ρ ι).card :=
  (cof_units_card (fun w => cof_live D ρ ι w ∧ (cof_supp D ρ ι w).Nonempty)).symm

theorem cof_lost_of_true (hS : Strict n D) {c : Fin n} (hc : ρ c = some true)
    {u : Σ _ : ℕ, ℕ} (hu : c ∈ supp n D u.1) : u ∉ cof_kept D ρ ι :=
  fun h => cof_not_live_of_true hS hc hu (cof_mem_kept.mp h).2.1

theorem cof_lost_of_deg {u : Σ _ : ℕ, ℕ} (h : cof_deg D ρ ι u.1 ≤ u.2 + 1) :
    u ∉ cof_kept D ρ ι := fun hk => by
  have := (cof_mem_kept.mp hk).2.2
  omega

theorem cof_keptP_sub : cof_keptP D ρ ι ⊆ cof_kept D ρ ι := fun _ hu =>
  cof_mem_kept.mpr ⟨(cof_mem_keptP.mp hu).1, (cof_mem_keptP.mp hu).2.1.1,
    (cof_mem_keptP.mp hu).2.2⟩

theorem cof_lostP_of_supp {u : Σ _ : ℕ, ℕ} (h : cof_supp D ρ ι u.1 = ∅) :
    u ∉ cof_keptP D ρ ι := fun hk => by
  have := (cof_mem_keptP.mp hk).2.1.2
  rw [h] at this
  exact Finset.not_nonempty_empty this

theorem cof_sur_add_lost (S : Finset (Σ _ : ℕ, ℕ)) (hS1 : S ⊆ units n D)
    (hS2 : ∀ u ∈ S, u ∉ cof_kept D ρ ι) : cof_sur D ρ ι + S.card ≤ totalSurplus n D := by
  rw [cof_sur_eq, ← card_units,
    ← Finset.card_union_of_disjoint (Finset.disjoint_left.mpr (fun u h1 h2 => hS2 u h2 h1))]
  exact Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) hS1)

theorem cof_surP_add_lost (S : Finset (Σ _ : ℕ, ℕ)) (hS1 : S ⊆ units n D)
    (hS2 : ∀ u ∈ S, u ∉ cof_keptP D ρ ι) : cof_surP D ρ ι + S.card ≤ totalSurplus n D := by
  rw [cof_surP_eq, ← card_units,
    ← Finset.card_union_of_disjoint (Finset.disjoint_left.mpr (fun u h1 h2 => hS2 u h2 h1))]
  exact Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) hS1)

theorem cof_arm_dead (hS : Strict n D) (K : Finset ℕ) (x b : ℕ)
    (hreach : ∀ w ∈ K, Relation.ReflTransGen
      (fun a c => sem_step n D a c ∧ a ∈ K ∧ c ∈ K) x w)
    (hb : b ∈ K) (hfan : ∀ w ∈ K, w ≠ b → fanout D w ≤ 1) (e : ℕ × Bool)
    (he : e ∈ exitArcs n D K) (hdead : ¬ cof_live D ρ ι (n + e.1)) :
    ∃ j ∈ readers D b, ¬ cof_live D ρ ι (n + j) := by
  obtain ⟨hea, hsK, htK⟩ := Finset.mem_filter.mp he
  have hej : e.1 < D.length := cof_mem_arcs.mp hea
  have hstep0 : sem_step n D (src D e) (n + e.1) := sem_step_src hej e.2
  have hkey : ∀ a c, a ∈ K → a ≠ b → sem_step n D a c → ¬ cof_live D ρ ι c →
      ¬ cof_live D ρ ι a ∧ ∀ c', sem_step n D a c' → c' = c := by
    intro a c haK hab hs hc
    have h1 : fanout D a = 1 := by
      have := hfan a haK hab
      have := sem_step_fanout hs
      omega
    have huniq : ∀ c', sem_step n D a c' → c' = c := fun c' hs' => sem_step_unique hs' hs h1
    refine ⟨fun hla => ?_, huniq⟩
    have hane : a ≠ outW n D := by
      have := lt_of_fanout_pos hS (sem_step_fanout hs)
      unfold outW
      omega
    obtain ⟨c', hs', hc'⟩ := cof_live_reader hla hane
    rw [huniq c' hs'] at hc'
    exact hc hc'
  have hmot : ∀ a, Relation.ReflTransGen (fun a c => sem_step n D a c ∧ a ∈ K ∧ c ∈ K) a
      (src D e) → (∃ j ∈ readers D b, ¬ cof_live D ρ ι (n + j)) ∨
      (¬ cof_live D ρ ι a ∧
        ¬ Relation.ReflTransGen (fun a c => sem_step n D a c ∧ a ∈ K ∧ c ∈ K) a b) := by
    intro a hp
    induction hp using Relation.ReflTransGen.head_induction_on with
    | refl =>
      by_cases hsb : src D e = b
      · have hr := sem_step_reader hstep0
        rw [Nat.add_sub_cancel_left, hsb] at hr
        exact Or.inl ⟨e.1, hr, hdead⟩
      · obtain ⟨h1, h2⟩ := hkey _ _ hsK hsb hstep0 hdead
        refine Or.inr ⟨h1, fun hp => ?_⟩
        rcases Relation.ReflTransGen.cases_head hp with heq | ⟨c', hs', -⟩
        · exact hsb heq
        · rw [h2 c' hs'.1] at hs'
          exact htK hs'.2.2
    | @head a c hstep hrest ih =>
      rcases ih with hl | ⟨hdc, hnb⟩
      · exact Or.inl hl
      · by_cases hab : a = b
        · refine Or.inl ⟨c - n, ?_, ?_⟩
          · rw [← hab]; exact sem_step_reader hstep.1
          · rw [Nat.add_sub_cancel' hstep.1.2.1]; exact hdc
        · obtain ⟨h1, h2⟩ := hkey _ _ hstep.2.1 hab hstep.1 hdc
          refine Or.inr ⟨h1, fun hp => ?_⟩
          rcases Relation.ReflTransGen.cases_head hp with heq | ⟨c', hs', hrest'⟩
          · exact hab heq
          · rw [h2 c' hs'.1] at hrest'
            exact hnb hrest'
  rcases hmot x (hreach _ hsK) with h | ⟨-, h⟩
  · exact h
  · exact absurd (hreach b hb) h

theorem cof_diff_reach (hS : Strict n D) (x c : Fin n) : ∀ w, w ∈ carrierDiff n D x c →
    Relation.ReflTransGen (fun a d => sem_step n D a d ∧ a ∈ carrierDiff n D x c ∧
      d ∈ carrierDiff n D x c) x.val w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    have hmem : ∀ u, u ∈ carrierDiff n D x c ↔
        u < n + D.length ∧ x ∈ supp n D u ∧ c ∉ supp n D u := by
      intro u; simp only [carrierDiff, Finset.mem_filter, Finset.mem_range]
    obtain ⟨hlt, hx, hc⟩ := (hmem w).mp hw
    by_cases hn : w < n
    · have hs : supp n D w = {⟨w, hn⟩} := supp_input D ⟨w, hn⟩
      rw [hs, Finset.mem_singleton] at hx
      have hxw : x.val = w := by rw [hx]
      rw [hxw]
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < D.length := by omega
      have key : ∀ s : Bool, x ∈ supp n D (src D (j, s)) → c ∉ supp n D (src D (j, s)) →
          Relation.ReflTransGen (fun a d => sem_step n D a d ∧ a ∈ carrierDiff n D x c ∧
            d ∈ carrierDiff n D x c) x.val (n + j) := by
        intro s h1 h2
        have hlt' := sem_src_lt hS hj s
        have hm : src D (j, s) ∈ carrierDiff n D x c := (hmem _).mpr ⟨by omega, h1, h2⟩
        exact Relation.ReflTransGen.tail (ih _ hlt' hm) ⟨sem_step_src hj s, hm, hw⟩
      cases ht : tag D j
      · rw [sem_supp_or hS hj ht, Finset.mem_union] at hx hc
        rcases hx with h1 | h1
        · exact key false (by rw [sb_src_false]; exact h1)
            (by rw [sb_src_false]; exact fun h => hc (Or.inl h))
        · exact key true (by rw [sb_src_true]; exact h1)
            (by rw [sb_src_true]; exact fun h => hc (Or.inr h))
      · rw [sem_supp_and hS hj ht, Finset.mem_inter] at hx hc
        by_cases hca : c ∈ supp n D (opA D j)
        · exact key true (by rw [sb_src_true]; exact hx.2)
            (by rw [sb_src_true]; exact fun h => hc ⟨hca, h⟩)
        · exact key false (by rw [sb_src_false]; exact hx.1) (by rw [sb_src_false]; exact hca)

theorem cof_diff_deplete (hS : Strict n D) {x c : Fin n} (hc : ρ c = some true) {b : ℕ}
    (hb : b ∈ carrierDiff n D x c) (hfb : 2 ≤ fanout D b)
    (hsur : surplusOn D (carrierDiff n D x c) = 1) {e : ℕ × Bool}
    (he : e ∈ exitArcs n D (carrierDiff n D x c)) (hec : c ∈ supp n D (n + e.1)) :
    cof_deg D ρ ι b ≤ 1 := by
  have h1 : fanout D b - 1 + ∑ u ∈ (carrierDiff n D x c).erase b, (fanout D u - 1) =
      ∑ u ∈ carrierDiff n D x c, (fanout D u - 1) :=
    Finset.add_sum_erase _ (fun u => fanout D u - 1) hb
  unfold surplusOn at hsur
  have hfan : ∀ w ∈ carrierDiff n D x c, w ≠ b → fanout D w ≤ 1 := by
    intro w hw hwb
    have h2 : fanout D w - 1 ≤ ∑ u ∈ (carrierDiff n D x c).erase b, (fanout D u - 1) :=
      Finset.single_le_sum (f := fun u => fanout D u - 1) (fun _ _ => Nat.zero_le _)
        (Finset.mem_erase.mpr ⟨hwb, hw⟩)
    omega
  obtain ⟨j, hj, hdj⟩ := cof_arm_dead (ρ := ρ) (ι := ι) hS _ x.val b (cof_diff_reach hS x c) hb
    hfan e he (cof_not_live_of_true hS hc hec)
  have hlt : ((readers D b).filter (fun j => cof_live D ρ ι (n + j))).card <
      (readers D b).card := Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨j, hj, hdj⟩)
  have h2 : (readers D b).card = fanout D b := rfl
  unfold cof_deg
  omega

theorem cof_edge {G : Fin n → Fin n → Prop} (hok : cof_Ok ρ ι) (hsym : ∀ u v, G u v → G v u)
    (hT : ∀ c a, ρ c = some true → G c a → ρ a = some false) (y : Fin m → Bool) :
    sem_Edge G (cof_ext ρ ι y) ↔ sem_Edge (fun u v : Fin m => G (ι u) (ι v)) y := by
  have hfree : ∀ u v, G u v → cof_ext ρ ι y u = true → cof_ext ρ ι y v = true →
      ∃ i, ι i = u ∧ y i = true := by
    intro u v huv hu hv
    cases hr : ρ u with
    | none =>
      obtain ⟨i, rfl⟩ := (hok.2 u).mp hr
      rw [cof_ext_free hok] at hu
      exact ⟨i, rfl, hu⟩
    | some b =>
      rw [cof_ext_fixed ι y hr] at hu
      subst hu
      rw [cof_ext_fixed ι y (hT u v hr huv)] at hv
      exact absurd hv Bool.false_ne_true
  constructor
  · rintro ⟨u, v, huv, hu, hv⟩
    obtain ⟨i, rfl, hi⟩ := hfree u v huv hu hv
    obtain ⟨i', rfl, hi'⟩ := hfree v _ (hsym _ _ huv) hv hu
    exact ⟨i, i', huv, hi, hi'⟩
  · rintro ⟨i, i', huv, hi, hi'⟩
    exact ⟨ι i, ι i', huv, by rw [cof_ext_free hok]; exact hi, by rw [cof_ext_free hok]; exact hi'⟩

theorem cof_restrict_graph {G : Fin n → Fin n → Prop} (hS : Strict n D) (hok : cof_Ok ρ ι)
    (hC : sem_Comp n G D) (hsym : ∀ u v, G u v → G v u)
    (hT : ∀ c a, ρ c = some true → G c a → ρ a = some false)
    (hG' : sem_Gr (fun u v : Fin m => G (ι u) (ι v))) (hm : 0 < m) :
    ∃ E : Dag, StrictLive m E ∧ sem_Comp m (fun u v : Fin m => G (ι u) (ι v)) E ∧
      totalSurplus m E ≤ cof_sur D ρ ι ∧ Bplus m E ≤ cof_surP D ρ ι ∧
      ∀ i : Fin m, (∀ w, Relation.ReflTransGen (sem_step n D) (ι i).val w → fanout D w ≤ 1) →
        i ∈ ineligSet m E := by
  have hval : ∀ y, val D (cof_ext ρ ι y) (outW n D) = true ↔
      sem_Edge (fun u v : Fin m => G (ι u) (ι v)) y :=
    fun y => (hC _).trans (cof_edge hok hsym hT y)
  have hm2 : 2 ≤ m := by
    obtain ⟨a, -, hne⟩ := hG'.2.2.2 ⟨0, hm⟩ ⟨0, hm⟩
    by_contra hc
    exact hne (Fin.ext (by have := a.isLt; show a.val = 0; omega))
  have hess : ∀ i : Fin m, ∃ y y' : Fin m → Bool, (∀ k, k ≠ i → y k = y' k) ∧
      val D (cof_ext ρ ι y) (outW n D) ≠ val D (cof_ext ρ ι y') (outW n D) := by
    intro i
    obtain ⟨a, ha, -⟩ := hG'.2.2.2 i i
    refine ⟨single a, sem_ins i (single a), sem_ins_agree i _, fun heq => ?_⟩
    have h1 : sem_Edge (fun u v : Fin m => G (ι u) (ι v)) (sem_ins i (single a)) :=
      ⟨i, a, ha, sem_ins_self i _, by simp [sem_ins, single]⟩
    have h2 := (hval _).mpr h1
    rw [← heq] at h2
    exact sem_single_no_edge hG' a ((hval _).mp h2)
  obtain ⟨E, h1, h2, h3, h4, h5⟩ := cof_restrict hS hok hm2 hess
  exact ⟨E, h1, fun y => by rw [h2 y]; exact hval y, h3, h4, h5⟩

end CofRestrict

noncomputable section CofCount

open Classical

variable {n m : ℕ} {D : Dag} {ρ : Fin n → Option Bool} {ι : Fin m → Fin n}

def cof_bin (D : Dag) (ρ : Fin n → Option Bool) (ι : Fin m → Fin n) : Finset ℕ :=
  (Finset.range D.length).filter (fun j => cof_live D ρ ι (n + j) ∧
    ¬ cof_const D ρ ι (opA D j) ∧ ¬ cof_const D ρ ι (opB D j))

theorem cof_sur_le_bin (hS : Strict n D) (hok : cof_Ok ρ ι)
    (hfree : ∀ i : Fin m, cof_live D ρ ι (ι i).val) :
    cof_sur D ρ ι + m ≤ (cof_bin D ρ ι).card + 1 := by
  have hSmem : ∀ w, w ∈ (inner n D).filter (fun w => cof_live D ρ ι w) →
      cof_live D ρ ι w ∧ w ≠ outW n D := by
    intro w hw
    rw [Finset.mem_filter, sb_mem_inner] at hw
    exact ⟨hw.2, by unfold outW; omega⟩
  have h1 : cof_sur D ρ ι + ((inner n D).filter (fun w => cof_live D ρ ι w)).card =
      ∑ w ∈ (inner n D).filter (fun w => cof_live D ρ ι w), cof_deg D ρ ι w :=
    cof_sum_sub_one _ _ (fun w hw => cof_deg_pos (hSmem w hw).1 (hSmem w hw).2)
  have h2 : ∑ w ∈ (inner n D).filter (fun w => cof_live D ρ ι w), cof_deg D ρ ι w =
      ((arcs D).filter (fun a => src D a ∈ (inner n D).filter (fun w => cof_live D ρ ι w) ∧
        cof_live D ρ ι (n + a.1))).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := src D)
      (t := (inner n D).filter (fun w => cof_live D ρ ι w))
      (fun a ha => Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2.1)]
    refine Finset.sum_congr rfl (fun w hw => ?_)
    rw [cof_deg_arcs hS, Finset.filter_filter]
    congr 1
    ext a
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨ha, rfl, hl⟩; exact ⟨ha, ⟨Finset.mem_filter.mp hw, hl⟩, rfl⟩
    · rintro ⟨ha, ⟨-, hl⟩, h⟩; exact ⟨ha, h, hl⟩
  have key : ∀ j, ((if (src D (j, false) ∈ (inner n D).filter (fun w => cof_live D ρ ι w) ∧
        cof_live D ρ ι (n + j)) then 1 else 0) +
      (if (src D (j, true) ∈ (inner n D).filter (fun w => cof_live D ρ ι w) ∧
        cof_live D ρ ι (n + j)) then 1 else 0) : ℕ) ≤
      (if cof_live D ρ ι (n + j) then 1 else 0) +
      (if (cof_live D ρ ι (n + j) ∧ ¬ cof_const D ρ ι (opA D j) ∧
        ¬ cof_const D ρ ι (opB D j)) then 1 else 0) := by
    intro j
    have e1 : src D (j, false) ∈ (inner n D).filter (fun w => cof_live D ρ ι w) →
        ¬ cof_const D ρ ι (opA D j) := fun hs => by
      rw [← sb_src_false]; exact (hSmem _ hs).1.1
    have e2 : src D (j, true) ∈ (inner n D).filter (fun w => cof_live D ρ ι w) →
        ¬ cof_const D ρ ι (opB D j) := fun hs => by
      rw [← sb_src_true]; exact (hSmem _ hs).1.1
    split_ifs <;> first | omega | (exfalso; tauto)
  have h3 : ((arcs D).filter (fun a => src D a ∈ (inner n D).filter (fun w => cof_live D ρ ι w) ∧
      cof_live D ρ ι (n + a.1))).card ≤
      ((Finset.range D.length).filter (fun j => cof_live D ρ ι (n + j))).card +
        (cof_bin D ρ ι).card := by
    rw [sb_card_arcs_filter, cof_bin, Finset.card_filter, Finset.card_filter,
      ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun j _ => key j)
  have h4 : m + ((Finset.range D.length).filter (fun j => cof_live D ρ ι (n + j))).card ≤
      ((inner n D).filter (fun w => cof_live D ρ ι w)).card + 1 := by
    have hd : Disjoint (Finset.univ.image (fun i : Fin m => (ι i).val))
        (((Finset.range D.length).filter (fun j => cof_live D ρ ι (n + j))).image
          (fun j => n + j)) := by
      rw [Finset.disjoint_left]
      intro w h5 h6
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp h5
      obtain ⟨j, -, hj⟩ := Finset.mem_image.mp h6
      have := (ι i).isLt
      omega
    have hc := Finset.card_union_of_disjoint hd
    rw [Finset.card_image_of_injective _ (fun a b hab => hok.1 (Fin.ext hab)),
      Finset.card_image_of_injective _ (add_right_injective n), Finset.card_univ,
      Fintype.card_fin] at hc
    have hsub : (Finset.univ.image (fun i : Fin m => (ι i).val) ∪
        ((Finset.range D.length).filter (fun j => cof_live D ρ ι (n + j))).image
          (fun j => n + j)).erase (outW n D) ⊆
        (inner n D).filter (fun w => cof_live D ρ ι w) := by
      intro w hw
      rw [Finset.mem_erase, Finset.mem_union] at hw
      obtain ⟨hne, hw⟩ := hw
      have hl : cof_live D ρ ι w := by
        rcases hw with h5 | h5
        · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp h5
          exact hfree i
        · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h5
          exact (Finset.mem_filter.mp hj).2
      have := cof_live_lt hl
      exact Finset.mem_filter.mpr ⟨sb_mem_inner.mpr (by unfold outW at hne; omega), hl⟩
    have h7 := Finset.card_le_card hsub
    have h8 := Finset.pred_card_le_card_erase (a := outW n D)
      (s := Finset.univ.image (fun i : Fin m => (ι i).val) ∪
        ((Finset.range D.length).filter (fun j => cof_live D ρ ι (n + j))).image
          (fun j => n + j))
    omega
  omega

theorem cof_side_count (hS : Strict n D) (hok : cof_Ok ρ ι)
    (hess : ∀ i : Fin m, ∃ y y' : Fin m → Bool, (∀ k, k ≠ i → y k = y' k) ∧
      val D (cof_ext ρ ι y) (outW n D) ≠ val D (cof_ext ρ ι y') (outW n D))
    (C U : Finset ℕ) (hC : ∀ j ∈ C, j < D.length ∧ cof_const D ρ ι (n + j))
    (hU : ∀ j ∈ U, j < D.length ∧
      (cof_const D ρ ι (opA D j) ∨ cof_const D ρ ι (opB D j)))
    (hCU : Disjoint C U) : C.card + U.card + m ≤ D.length + 1 := by
  have h1 := cof_sur_le_bin hS hok (fun i => cof_live_free hS hok i (hess i))
  have hd1 : Disjoint (cof_bin D ρ ι) C := by
    rw [Finset.disjoint_left]
    intro j h5 h6
    exact (Finset.mem_filter.mp h5).2.1.1 (hC j h6).2
  have hd2 : Disjoint (cof_bin D ρ ι ∪ C) U := by
    rw [Finset.disjoint_union_left]
    refine ⟨?_, hCU⟩
    rw [Finset.disjoint_left]
    intro j h5 h6
    rcases (hU j h6).2 with h7 | h7
    · exact (Finset.mem_filter.mp h5).2.2.1 h7
    · exact (Finset.mem_filter.mp h5).2.2.2 h7
  have hsub : cof_bin D ρ ι ∪ C ∪ U ⊆ Finset.range D.length := by
    intro j hj
    rw [Finset.mem_union, Finset.mem_union] at hj
    rcases hj with (h5 | h5) | h5
    · exact (Finset.mem_filter.mp h5).1
    · exact Finset.mem_range.mpr (hC j h5).1
    · exact Finset.mem_range.mpr (hU j h5).1
  have h2 := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1,
    Finset.card_range] at h2
  omega

theorem cof_supp_count (hS : Strict n D) (hok : cof_Ok ρ ι)
    (hess : ∀ i : Fin m, ∃ y y' : Fin m → Bool, (∀ k, k ≠ i → y k = y' k) ∧
      val D (cof_ext ρ ι y) (outW n D) ≠ val D (cof_ext ρ ι y') (outW n D))
    (P : Finset (Fin n)) (hP : ∀ v ∈ P, ρ v = some true) :
    ((Finset.range D.length).filter (fun j => (supp n D (n + j) ∩ P).Nonempty)).card +
      ((Finset.range D.length).filter (fun j => ¬ (supp n D (n + j) ∩ P).Nonempty ∧
        ((supp n D (opA D j) ∩ P).Nonempty ∨ (supp n D (opB D j) ∩ P).Nonempty))).card + m ≤
      D.length + 1 := by
  have hconst : ∀ w, (supp n D w ∩ P).Nonempty → cof_const D ρ ι w := by
    rintro w ⟨v, hv⟩
    rw [Finset.mem_inter] at hv
    exact cof_const_of_true hS (hP v hv.2) hv.1
  refine cof_side_count hS hok hess _ _ (fun j hj => ?_) (fun j hj => ?_) ?_
  · rw [Finset.mem_filter, Finset.mem_range] at hj
    exact ⟨hj.1, hconst _ hj.2⟩
  · rw [Finset.mem_filter, Finset.mem_range] at hj
    exact ⟨hj.1, hj.2.2.imp (hconst _) (hconst _)⟩
  · rw [Finset.disjoint_left]
    intro j h5 h6
    exact (Finset.mem_filter.mp h6).2.1 (Finset.mem_filter.mp h5).2

end CofCount

def cof_hw_rho (i v : Fin 14) : Option Bool :=
  if decide (v.val < 7) = decide (i.val < 7) then none else some true

def cof_hw_iota (i : Fin 14) (k : Fin 7) : Fin 14 :=
  ⟨if i.val < 7 then k.val else k.val + 7, by have := k.isLt; split_ifs <;> omega⟩

theorem cof_hw_inj : ∀ i : Fin 14, ∀ a b : Fin 7, cof_hw_iota i a = cof_hw_iota i b → a = b := by
  decide +kernel

theorem cof_hw_free : ∀ i v : Fin 14, cof_hw_rho i v = none ↔ ∃ k, cof_hw_iota i k = v := by
  decide +kernel

theorem cof_hw_ok (i : Fin 14) : cof_Ok (cof_hw_rho i) (cof_hw_iota i) :=
  ⟨fun a b hab => cof_hw_inj i a b hab, cof_hw_free i⟩

theorem cof_hw_rho_true {i v : Fin 14} : cof_hw_rho i v = some true ↔ v ∈ sem_hw_opp i := by
  simp only [cof_hw_rho, sem_hw_opp, Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs with h <;> simp [h]

theorem cof_hw_iota_side : ∀ i : Fin 14, ∀ k : Fin 7,
    decide ((cof_hw_iota i k).val < 7) = decide (i.val < 7) := by decide +kernel

theorem cof_hw_ess {D : Dag} (hD : Correct D) (i : Fin 14) (k : Fin 7) :
    ∃ y y' : Fin 7 → Bool, (∀ k', k' ≠ k → y k' = y' k') ∧
      val D (cof_ext (cof_hw_rho i) (cof_hw_iota i) y) (outW 14 D) ≠
        val D (cof_ext (cof_hw_rho i) (cof_hw_iota i) y') (outW 14 D) := by
  have hC := sem_heawood_comp hD
  have hok := cof_hw_ok i
  refine ⟨fun _ => false, single k, fun k' hk' => by simp [single, hk'], ?_⟩
  have h0 : val D (cof_ext (cof_hw_rho i) (cof_hw_iota i) (fun _ => false)) (outW 14 D) =
      false := by
    by_contra hc
    rw [Bool.not_eq_false] at hc
    obtain ⟨u, v, huv, hu, hv⟩ := (hC _).mp hc
    have hside : ∀ w : Fin 14,
        cof_ext (cof_hw_rho i) (cof_hw_iota i) (fun _ => false) w = true → w ∈ sem_hw_opp i := by
      intro w hw
      rw [← cof_hw_rho_true]
      unfold cof_ext at hw
      cases hr : cof_hw_rho i w with
      | none => rw [hr] at hw; simp at hw
      | some b => rw [hr] at hw; simp at hw; rw [hw]
    exact sem_hw_opp_indep i u (hside u hu) v (hside v hv) huv
  have h1 : val D (cof_ext (cof_hw_rho i) (cof_hw_iota i) (single k)) (outW 14 D) = true := by
    obtain ⟨a, ha, -⟩ := sem_heawood_gr.2.2.2 (cof_hw_iota i k) (cof_hw_iota i k)
    refine (hC _).mpr ⟨cof_hw_iota i k, a, ha, ?_, ?_⟩
    · rw [cof_ext_free hok]; simp [single]
    · refine cof_ext_fixed _ _ (cof_hw_rho_true.mpr ?_)
      have h2 := sem_hw_nb_opp ha
      simp only [sem_hw_opp, Finset.mem_filter, Finset.mem_univ, true_and] at h2 ⊢
      rw [← cof_hw_iota_side i k]
      exact h2
  rw [h0, h1]
  exact Bool.false_ne_true

theorem cof_hw_side_count {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (i : Fin 14) :
    ((Finset.range D.length).filter
        (fun j => (supp 14 D (14 + j) ∩ sem_hw_opp i).Nonempty)).card +
      ((Finset.range D.length).filter (fun j => ¬ (supp 14 D (14 + j) ∩ sem_hw_opp i).Nonempty ∧
        ((supp 14 D (opA D j) ∩ sem_hw_opp i).Nonempty ∨
          (supp 14 D (opB D j) ∩ sem_hw_opp i).Nonempty))).card + 6 ≤ D.length := by
  have h1 := cof_supp_count h.1 (cof_hw_ok i) (cof_hw_ess hD i) (sem_hw_opp i)
    (fun v hv => cof_hw_rho_true.mpr hv)
  omega

section L3Gen

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

theorem cnt_main (hS : Strict n D) {P : Finset (Fin n)} (hP : P.card ≤ 7)
    (L : Finset (Finset (Fin n))) (h3 : ∀ T ∈ L, T.card = 3 ∧ sup_Occ n D P T)
    (hint : ∀ T ∈ L, ∀ T' ∈ L, T ≠ T' → (T ∩ T').card ≤ 1) (E : Finset (ℕ × Bool))
    (hE : ∀ e ∈ E, e ∈ exitArcs n D (carrierT n D P) ∧ 3 ≤ (supp n D (src D e) ∩ P).card)
    (Lab : Finset (Fin n)) (U : Fin n → Finset (Fin n))
    (hw : ∀ f ∈ Lab, ∃ e, sup_Wit n D P (U f) f e)
    (hUL : ∀ f ∈ Lab, ∀ T ∈ L, (U f ∩ T).card ≤ 1) :
    2 * L.card + E.card + Lab.card ≤
      (exitArcs n D (carrierT n D P)).card + (merges n D (carrierT n D P)).card := by
  classical
  choose! wit hwit using hw
  let S := Lab.filter (fun f => ∀ M, M ⊆ U f → M.card = 2 → f ∈ M → ¬ sup_Occ n D P M)
  have hSL : S ⊆ Lab := Finset.filter_subset _ _
  have hno : ∀ f ∈ Lab \ S, ∃ M, M ⊆ U f ∧ M.card = 2 ∧ f ∈ M ∧ sup_Occ n D P M := by
    intro f hf
    rw [Finset.mem_sdiff, Finset.mem_filter] at hf
    by_contra hc
    exact hf.2 ⟨hf.1, fun M h1 h2 h4 h5 => hc ⟨M, h1, h2, h4, h5⟩⟩
  choose! pr hpr using hno
  have hX := sup_charge hS hP L h3 hint ((Lab \ S).image pr) (by
    intro M hM
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hM
    obtain ⟨h1, h2, -, h4⟩ := hpr f hf
    refine ⟨h4, by omega, fun hL => by have := (h3 _ hL).1; omega, by omega, by omega,
      fun _ T hT hsub => ?_⟩
    have := Finset.card_le_card (Finset.subset_inter h1 hsub)
    have := hUL f (Finset.mem_sdiff.1 hf).1 T hT
    omega)
  have hcnt := sup_count hS P E hE Lab S U wit hwit hSL (fun f hf =>
    sup_wit_single (hwit f (hSL hf)) (Finset.mem_filter.1 hf).2)
  have hfib : (Lab \ S).card ≤ 2 * ((Lab \ S).image pr).card := by
    refine Finset.card_le_mul_card_image _ 2 (fun M _ => ?_)
    by_cases hne : ((Lab \ S).filter (fun f => pr f = M)).Nonempty
    · obtain ⟨g, hg⟩ := hne
      rw [Finset.mem_filter] at hg
      have hM2 : M.card = 2 := hg.2 ▸ (hpr g hg.1).2.1
      rw [← hM2]
      refine Finset.card_le_card (fun f hf => ?_)
      rw [Finset.mem_filter] at hf
      exact hf.2 ▸ (hpr f hf.1).2.2.1
    · rw [Finset.not_nonempty_iff_eq_empty.1 hne]; simp
  have := Finset.card_sdiff_add_card_eq_card hSL
  omega

theorem bz_card (hS : Strict n D) (Z : Finset ℕ)
    (hZ : ∀ b ∈ Z, 2 ≤ fanout D b ∧ supp n D b = ∅) : Z.card ≤ Bzero n D := by
  have hsub : Z ⊆ (inner n D).filter (fun w => ¬ (supp n D w).Nonempty) :=
    fun b hb => sem_bzero_mem hS (hZ b hb).1 (hZ b hb).2
  calc Z.card = ∑ _w ∈ Z, 1 := by simp
    _ ≤ ∑ w ∈ Z, (fanout D w - 1) :=
        Finset.sum_le_sum (fun w hw => by have := (hZ w hw).1; omega)
    _ ≤ Bzero n D := Finset.sum_le_sum_of_subset hsub

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

theorem tri_bound (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (b : Fin n → ℕ) (hb : PureBranch n D b) {pos : Fin n → ℕ × Bool} (hpos : k4_Pos n G D pos)
    (T J : Finset (Fin n)) (A : Fin n → Finset (Fin n))
    (hJ : ∀ i ∈ J, i ∈ ineligSet n D ∧ (∃ a ∈ T, G i a) ∧ ∀ f ∈ T, ∃ a ∈ A f, G i a)
    (hA : ∀ f ∈ T, (∀ a ∈ A f, ∀ b ∈ A f, ¬ G a b) ∧ T.erase f ⊆ A f ∧ ∃ a ∈ A f, G f a)
    {x y z : Fin n} (hT : T = {x, y, z}) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) {w v : ℕ}
    (hx : x ∈ supp n D w) (hy : y ∈ supp n D w) (hx' : x ∈ supp n D v) (hz : z ∈ supp n D v) :
    J.card + 2 + (eligSet n D).card ≤ 3 + Bplus n D := by
  have hT3 : T.card = 3 := by
    rw [hT, Finset.card_insert_of_notMem (by simp [hxy, hxz]),
      Finset.card_insert_of_notMem (by simp [hyz]), Finset.card_singleton]
  have h1 := tri_exits hG h.1 hC hpos T J A hJ hA
  have h2 := k4_pair_merges h.1 hT3 (a := x) (b := y) (c := z) (by simp [hT]) (by simp [hT])
    (by simp [hT]) hxy hxz hyz hx hy hx' hz
  have h4 := carrier_flow_union h T (by rw [sem_supp_out hG hC]; simp)
  have h5 := surplus_carrierT_le h.1 b hb T
  have h6 := Finset.card_le_card (Finset.inter_subset_left : T ∩ eligSet n D ⊆ T)
  omega

end L3Gen

theorem hw_nb_inj {i j : Fin 14} (h : sem_hw_nb i = sem_hw_nb j) : i = j := by
  by_contra hne
  obtain ⟨z, hz1, hz2⟩ := nbr_diff_exists i j hne
  have : z ∈ sem_hw_nb j := h ▸ (by simp [sem_hw_nb, hz1])
  simp [sem_hw_nb, hz2] at this

theorem hw_mem_nb {i a : Fin 14} : a ∈ sem_hw_nb i ↔ Adj i a := by
  simp [sem_hw_nb]

theorem hw_lost {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (P : Finset (Fin 14))
    (hP : ∀ a ∈ P, ∀ b ∈ P, ¬ Adj a b) (J : Finset (Fin 14))
    (hJ : ∀ i ∈ J, i ∈ ineligSet 14 D ∧ sem_hw_nb i ⊆ P ∧ ¬ sup_Occ 14 D P (sem_hw_nb i)) :
    J.card ≤ Bzero 14 D := by
  classical
  have hG := sem_heawood_gr
  have hC := sem_heawood_comp hD
  have hocc : ∀ i ∈ J, ∀ q, (∀ a ∈ P, (a ∈ supp 14 D q ↔ Adj i a)) → False := by
    intro i hi q hq
    refine (hJ i hi).2.2 ⟨q, ?_⟩
    ext a
    rw [Finset.mem_inter, hw_mem_nb]
    exact ⟨fun h1 => (hq a h1.2).1 h1.1,
      fun h1 => ⟨(hq a ((hJ i hi).2.1 (hw_mem_nb.2 h1))).2 h1, (hJ i hi).2.1 (hw_mem_nb.2 h1)⟩⟩
  have hb : ∀ i ∈ J, ∃ b, sem_Chain 14 D i.val b ∧ 2 ≤ fanout D b ∧ supp 14 D b = ∅ := by
    intro i hi
    rcases sem_inelig_reach hG h hC (hJ i hi).1 with hch | hb
    · obtain ⟨j, s, -, -, -, hq⟩ := sem_exact_nbhd hG h.1 hC P hP hch
      exact (hocc i hi _ hq).elim
    · exact hb
  choose! β hβ using hb
  have hinj : Set.InjOn β J := by
    intro i hi j hj hij
    by_contra hne
    obtain ⟨a, ha1, ha2⟩ := nbr_diff_exists j i (Ne.symm hne)
    obtain ⟨k, s, -, -, -, -, hq⟩ := sem_shared_exact hG h.1 hC P hP (hβ i hi).1
      (sem_chain_dom h.1 (hij ▸ (hβ j hj).1)) ⟨a, (hJ j hj).2.1 (hw_mem_nb.2 ha1), ha1, ha2⟩
    exact hocc i hi _ hq
  rw [← Finset.card_image_of_injOn hinj]
  refine bz_card h.1 _ (fun b hb => ?_)
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hb
  exact (hβ i hi).2

theorem hw_count {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (P : Finset (Fin 14))
    (hPl : P ⊆ sem_hw_opp 0) (hPe : P ⊆ eligSet 14 D) (Oc Ct I : Finset (Fin 14))
    (hOc : ∀ i ∈ Oc, sem_hw_nb i ⊆ P ∧ sup_Occ 14 D P (sem_hw_nb i))
    (hCt : ∀ c ∈ Ct, c ∉ Oc ∧ ((sem_hw_nb c ∩ P).card ≤ 2 ∨
      (sem_hw_nb c ⊆ P ∧ ¬ sup_Occ 14 D P (sem_hw_nb c))))
    (hI : ∀ i ∈ I, i ∈ ineligSet 14 D ∧ sem_hw_nb i ⊆ P) :
    2 * Oc.card + I.card + (Ct.biUnion (fun c => sem_hw_nb c ∩ P)).card +
      (eligSet 14 D).card ≤ 2 * P.card + Bplus 14 D := by
  classical
  have hG := sem_heawood_gr
  have hC := sem_heawood_comp hD
  obtain ⟨b, hb⟩ := exists_pureBranch h hD
  have hPi : ∀ a ∈ P, ∀ b ∈ P, ¬ Adj a b :=
    fun a ha b hb => sem_hw_opp_indep 0 a (hPl ha) b (hPl hb)
  have hP7 : P.card ≤ 7 := (Finset.card_le_card hPl).trans (by decide)
  obtain ⟨E, hEc, hE⟩ := sup_assigned_exits hG h hC P I (fun i hi =>
    ⟨(hI i hi).1, sem_hw_nb i, (hI i hi).2, (degree_three i).ge, fun a ha => hw_mem_nb.1 ha⟩)
  have hlab : ∀ f ∈ Ct.biUnion (fun c => sem_hw_nb c ∩ P), ∃ c ∈ Ct, f ∈ sem_hw_nb c ∩ P :=
    fun f hf => Finset.mem_biUnion.1 hf
  choose! ct hct using hlab
  have hmain := cnt_main h.1 hP7 (Oc.image sem_hw_nb)
    (fun T hT => by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hT
      exact ⟨degree_three i, (hOc i hi).2⟩)
    (fun T hT T' hT' hne => by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hT
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hT'
      have := sup_hw_inter i j (fun hij => hne (hij ▸ rfl)) Finset.univ
      simpa [sem_hw_nb] using this)
    E hE (Ct.biUnion (fun c => sem_hw_nb c ∩ P)) (fun f => sem_hw_nb (ct f) ∩ P)
    (fun f hf => by
      obtain ⟨hc, hfc⟩ := hct f hf
      refine sup_wit_exists hG h.1 hC (X := insert (ct f) (P \ (sem_hw_nb (ct f) ∩ P)))
        Finset.inter_subset_right ?_ ?_ (fun a ha => Finset.mem_insert_of_mem ha) hfc
        ⟨ct f, Finset.mem_insert_self _ _, adj_symm (hw_mem_nb.1 (Finset.mem_inter.1 hfc).1)⟩
      · rcases (hCt _ hc).2 with h2 | ⟨h2, h4⟩
        · exact Or.inl h2
        · rw [Finset.inter_eq_left.2 h2]; exact Or.inr ⟨degree_three _, h4⟩
      · have hno : ∀ a ∈ P \ (sem_hw_nb (ct f) ∩ P), ¬ Adj (ct f) a := by
          intro a ha hadj
          rw [Finset.mem_sdiff, Finset.mem_inter, hw_mem_nb] at ha
          exact ha.2 ⟨hadj, ha.1⟩
        intro a ha b hb
        rcases Finset.mem_insert.1 ha with rfl | ha <;> rcases Finset.mem_insert.1 hb with rfl | hb
        · exact adj_irrefl _
        · exact hno b hb
        · exact fun hab => hno a ha (adj_symm hab)
        · exact hPi a (Finset.mem_sdiff.1 ha).1 b (Finset.mem_sdiff.1 hb).1)
    (fun f hf T hT => by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hT
      have := sup_hw_inter (ct f) i (fun hij => (hCt _ (hct f hf).1).1 (hij ▸ hi)) P
      rwa [show Finset.univ.filter (fun z => Adj i z) ∩ P = sem_hw_nb i from
        Finset.inter_eq_left.2 (hOc i hi).1] at this)
  have h4 := carrier_flow_union h P (by rw [heawood_supp_out hD]; simp)
  have h5 := surplus_carrierT_le h.1 b hb P
  rw [Finset.inter_eq_left.2 hPe] at h5
  rw [Finset.card_image_of_injective _ (fun i j hij => hw_nb_inj hij), hEc] at hmain
  omega

theorem tight_surplus {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hB : Bplus 14 D = (eligSet 14 D).card) (h0 : (0 : Fin 14) ∈ ineligSet 14 D) : False := by
  classical
  have hG := sem_heawood_gr
  have hC := sem_heawood_comp hD
  obtain ⟨b, hb⟩ := exists_pureBranch h hD
  have hres : residualUnits 14 D b = ∅ := by
    have := card_residual h.1 b hb
    exact Finset.card_eq_zero.1 (by omega)
  have hW2 : ∀ x, (sem_W 14 D x).card ≤ 2 := by
    intro x
    have h1 := sem_code_count hG h hC b hb x
    have h2 := Finset.card_le_card
      (Finset.inter_subset_left : ({x} : Finset (Fin 14)) ∩ eligSet 14 D ⊆ {x})
    rw [hres] at h1
    simp only [Finset.filter_empty, Finset.card_empty, Finset.card_singleton] at h1 h2
    omega
  obtain ⟨e, he1, -, hes, heg, henb, heW, -⟩ := sem_inelig_consumer hG h hC h0

  have hline : ∀ u : Fin 14, Adj 0 u → ∃ Z, (∀ t, t ≠ u → Z ∉ sem_W 14 D t) ∧
      ∀ w : Fin 14, Adj w u → w ≠ 0 → sem_bar Z ∈ sem_W 14 D w := by
    intro u hu
    have hY : sem_bar e ∈ sem_W 14 D u :=
      sem_mem_W.2 ⟨he1, henb u hu, by rw [show (sem_bar e).1 = e.1 from rfl, heg]; simp⟩
    obtain ⟨Z, -, hWu, hZ, -⟩ := sem_hw_private_slot h hD h0
      (fun hu0 => adj_irrefl 0 (by rw [hu0] at hu; exact hu)) heW hY (hW2 u)
    refine ⟨Z, hZ, fun w hw hw0 => ?_⟩
    obtain ⟨e', h1, h2, -, -, -⟩ := sem_edge_slots hG h.1 hC hw
    rw [hWu, Finset.mem_insert, Finset.mem_singleton] at h2
    rcases h2 with h2 | h2
    · have h4 : e' = e := by rw [← sem_bar_bar e', h2, sem_bar_bar]
      rw [h4] at h1
      have := (sem_mem_W.1 h1).2.1
      rw [hes, Finset.mem_singleton] at this
      exact (hw0 this).elim
    · rw [← h2, sem_bar_bar]; exact h1

  have key : ∀ w w' u : Fin 14, Adj 0 u → Adj w u → Adj w' u → w ≠ 0 → w' ≠ 0 → w ≠ w' →
      Adj w 9 → u ≠ 9 → ∃ r, sem_bar r ∈ sem_W 14 D 9 ∧ w ∈ supp 14 D (src D r) ∧
        ∀ a, a ≠ w → ¬ Adj a w' → a ∉ supp 14 D (src D r) := by
    intro w w' u hu hwu hw'u hw0 hw'0 hww' hw9 hu9
    obtain ⟨Z, hZ, hZw⟩ := hline u hu
    obtain ⟨r, hr1, hr2, -, -, -⟩ := sem_edge_slots hG h.1 hC hw9
    have hrZ : r ≠ sem_bar Z := by
      intro hrz
      rw [hrz, sem_bar_bar] at hr2
      exact hZ 9 (Ne.symm hu9) hr2
    refine ⟨r, hr2, (sem_mem_W.1 hr1).2.1, fun a ha haw' hmem => ?_⟩
    obtain ⟨e3, h1, h2, h4⟩ := sem_hw_cover_free h hD (x := w) (a := a) (b := w')
      (Ne.symm ha) hww' haw'
    have hsub : ({sem_bar Z, r} : Finset (ℕ × Bool)) ⊆ sem_W 14 D w := by
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact hZw w hwu hw0
      · rw [Finset.mem_singleton.1 hx]; exact hr1
    have heq := Finset.eq_of_subset_of_card_le hsub
      (by rw [Finset.card_pair (Ne.symm hrZ)]; exact hW2 w)
    rw [← heq, Finset.mem_insert, Finset.mem_singleton] at h1
    rcases h1 with rfl | rfl
    · exact h4 (sem_mem_W.1 (hZw w' hw'u hw'0)).2.1
    · exact h2 hmem
  obtain ⟨r1, a1, b1, c1⟩ := key 1 3 7 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  obtain ⟨r5, a5, b5, c5⟩ := key 5 4 10 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  obtain ⟨r6, a6, b6, c6⟩ := key 6 2 8 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have n15 : sem_bar r1 ≠ sem_bar r5 := fun hh =>
    c1 5 (by decide) (by decide) (by rw [← sem_bar_bar r1, hh, sem_bar_bar]; exact b5)
  have n16 : sem_bar r1 ≠ sem_bar r6 := fun hh =>
    c1 6 (by decide) (by decide) (by rw [← sem_bar_bar r1, hh, sem_bar_bar]; exact b6)
  have n56 : sem_bar r5 ≠ sem_bar r6 := fun hh =>
    c5 6 (by decide) (by decide) (by rw [← sem_bar_bar r5, hh, sem_bar_bar]; exact b6)
  have hsub : ({sem_bar r1, sem_bar r5, sem_bar r6} : Finset (ℕ × Bool)) ⊆ sem_W 14 D 9 := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by simp [n15, n16]), Finset.card_pair n56] at this
  have := hW2 9
  omega

theorem tight_le {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hB : Bplus 14 D ≤ (eligSet 14 D).card) (h0 : (0 : Fin 14) ∈ ineligSet 14 D) : False := by
  obtain ⟨b, hb⟩ := exists_pureBranch h hD
  exact tight_surplus h hD (le_antisymm hB (elig_le_Bplus h.1 b hb)) h0

theorem elim_p13 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h13 : totalSurplus 14 D ≤ 13) (hI : ineligSet 14 D = {0}) : False := by
  have h1 := inelig_card_add 14 D
  have h4 := Bplus_le_total 14 D
  rw [hI, Finset.card_singleton] at h1
  exact tight_le h hD (by omega) (by rw [hI]; simp)

def os_pt (k : Fin 7) : Fin 14 := ⟨k.val, by omega⟩

theorem os_pt_inj : Function.Injective os_pt := by decide

theorem os_nb_sub : ∀ k : Fin 7, sem_hw_nb (os_pt k) ⊆ sem_hw_opp 0 := by decide +kernel

theorem os_union : ∀ M : Finset (Fin 7), M.Nonempty →
    min (M.card + 2) 7 ≤ ((M.image os_pt).biUnion
      (fun c => sem_hw_nb c ∩ sem_hw_opp 0)).card := by decide +kernel

theorem elim_onesided {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h13 : totalSurplus 14 D ≤ 13) (q : ℕ) (hq : q = 5 ∨ q = 6 ∨ q = 7)
    (hI : ∀ i : Fin 14, i ∈ ineligSet 14 D ↔ i.val < q) : False := by
  classical
  obtain ⟨b, hb⟩ := exists_pureBranch h hD
  have hPe : sem_hw_opp 0 ⊆ eligSet 14 D := by
    intro a ha
    by_contra hne
    have := (hI a).1 (sem_mem_inelig.2 hne)
    simp only [sem_hw_opp, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    have h7 : ¬ a.val < 7 := by simpa using ha
    omega
  let Oc := Finset.univ.filter (fun k : Fin 7 => sup_Occ 14 D (sem_hw_opp 0) (sem_hw_nb (os_pt k)))
  let Mi := Finset.univ.filter
    (fun k : Fin 7 => ¬ sup_Occ 14 D (sem_hw_opp 0) (sem_hw_nb (os_pt k)))
  let Iq := Finset.univ.filter (fun k : Fin 7 => k.val < q)
  have hIq : ∀ k ∈ Iq, os_pt k ∈ ineligSet 14 D := fun k hk => (hI _).2 (Finset.mem_filter.1 hk).2
  have hcnt := hw_count h hD (sem_hw_opp 0) (Finset.Subset.refl _) hPe (Oc.image os_pt)
    (Mi.image os_pt) (Iq.image os_pt)
    (fun i hi => by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hi
      exact ⟨os_nb_sub k, (Finset.mem_filter.1 hk).2⟩)
    (fun c hc => by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hc
      refine ⟨fun hc' => ?_, Or.inr ⟨os_nb_sub k, (Finset.mem_filter.1 hk).2⟩⟩
      obtain ⟨k', hk', hkk⟩ := Finset.mem_image.1 hc'
      rw [os_pt_inj hkk] at hk'
      exact (Finset.mem_filter.1 hk).2 (Finset.mem_filter.1 hk').2)
    (fun i hi => by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hi
      exact ⟨hIq k hk, os_nb_sub k⟩)
  have hlost := hw_lost h hD (sem_hw_opp 0) (sem_hw_opp_indep 0) ((Mi ∩ Iq).image os_pt)
    (fun i hi => by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hi
      rw [Finset.mem_inter] at hk
      exact ⟨hIq k hk.2, os_nb_sub k, (Finset.mem_filter.1 hk.1).2⟩)
  rw [Finset.card_image_of_injective _ os_pt_inj] at hlost
  rw [Finset.card_image_of_injective _ os_pt_inj, Finset.card_image_of_injective _ os_pt_inj]
    at hcnt
  have hsplit : Oc.card + Mi.card = 7 := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 7)))
      (fun k : Fin 7 => sup_Occ 14 D (sem_hw_opp 0) (sem_hw_nb (os_pt k)))
    simpa using this
  have hIqc : Iq.card = q := by
    rcases hq with rfl | rfl | rfl <;> rfl
  have hMI : Mi.card ≤ (Mi ∩ Iq).card + (7 - q) := by
    have h1 := Finset.card_inter_add_card_sdiff Mi Iq
    have h2 : (Mi \ Iq).card ≤ (Finset.univ \ Iq).card :=
      Finset.card_le_card (Finset.sdiff_subset_sdiff (Finset.subset_univ _) (Finset.Subset.refl _))
    rw [Finset.card_univ_sdiff, hIqc, Fintype.card_fin] at h2
    omega
  have hP7 : (sem_hw_opp 0).card = 7 := by decide
  have hel := inelig_card_add 14 D
  have hin : (ineligSet 14 D).card = q := by
    have : ineligSet 14 D = Iq.image os_pt := by
      ext i
      rw [hI, Finset.mem_image]
      constructor
      · intro hi
        have : i.val < 7 := by omega
        exact ⟨⟨i.val, this⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩, rfl⟩
      · rintro ⟨k, hk, rfl⟩
        exact (Finset.mem_filter.1 hk).2
    rw [this, Finset.card_image_of_injective _ os_pt_inj, hIqc]
  have h2 := elig_le_Bplus h.1 b hb
  have h4 := totalSurplus_split 14 D
  have hgeo : Mi.Nonempty → min (Mi.card + 2) 7 ≤
      ((Mi.image os_pt).biUnion (fun c => sem_hw_nb c ∩ sem_hw_opp 0)).card := os_union Mi
  by_cases hT : Bplus 14 D = (eligSet 14 D).card
  · exact tight_surplus h hD hT ((hI 0).2 (by rcases hq with rfl | rfl | rfl <;> decide))
  · rcases Finset.eq_empty_or_nonempty Mi with hM | hM
    · rw [hM] at hsplit
      simp only [Finset.card_empty] at hsplit
      omega
    · have := hgeo hM
      have := Finset.card_pos.2 hM
      omega

theorem elim_p7 {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (hlen : D.length ≤ 26)
    (hI : ineligSet 14 D = {0, 1, 2, 3, 4, 5, 6}) : False :=
  elim_onesided h hD (heawood_budget h hlen).2 7 (by omega) (by rw [hI]; decide)

theorem elim_p8 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h13 : totalSurplus 14 D ≤ 13) (hI : ineligSet 14 D = {0, 1, 2, 3, 4, 5}) : False :=
  elim_onesided h hD h13 6 (by omega) (by rw [hI]; decide)

theorem elim_p9_onesided {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h13 : totalSurplus 14 D ≤ 13) (hI : ineligSet 14 D = {0, 1, 2, 3, 4}) : False :=
  elim_onesided h hD h13 5 (by omega) (by rw [hI]; decide)

def mx_L : Finset (Fin 14) := {7, 8, 9, 10, 12, 13}

def mx_A (f : Fin 14) : Finset (Fin 14) :=
  if f = 7 then {3, 8, 9, 10, 13} else if f = 8 then {6, 7, 10, 12, 13} else {4, 7, 8, 9, 12}

theorem mx_J : ∀ i ∈ ({0, 1, 2, 5} : Finset (Fin 14)),
    (∃ a ∈ ({7, 8, 10} : Finset (Fin 14)), hc_adjB i a = true) ∧
      ∀ f ∈ ({7, 8, 10} : Finset (Fin 14)), ∃ a ∈ mx_A f, hc_adjB i a = true := by decide +kernel

theorem mx_Aok : ∀ f ∈ ({7, 8, 10} : Finset (Fin 14)),
    (∀ a ∈ mx_A f, ∀ b ∈ mx_A f, hc_adjB a b = false) ∧
      ({7, 8, 10} : Finset (Fin 14)).erase f ⊆ mx_A f ∧ ∃ a ∈ mx_A f, hc_adjB f a = true := by
  decide +kernel

theorem mx_cap : ∀ i ∈ ({0, 1, 2, 5} : Finset (Fin 14)), sem_hw_nb i ⊆ mx_L := by decide +kernel

theorem mx_ctr : ∀ c ∈ ({3, 4, 6} : Finset (Fin 14)), c ∉ ({0, 1, 2, 5} : Finset (Fin 14)) ∧
    (sem_hw_nb c ∩ mx_L).card ≤ 2 := by decide +kernel

theorem mx_el : ∀ a ∈ mx_L, a ∉ ({0, 1, 2, 5, 11} : Finset (Fin 14)) := by decide

theorem mx_lab :
    (({3, 4, 6} : Finset (Fin 14)).biUnion (fun c => sem_hw_nb c ∩ mx_L)).card = 6 := by
  decide +kernel

theorem mx_star {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hcap : ∀ i ∈ ({0, 1, 2, 5} : Finset (Fin 14)), i ∈ ineligSet 14 D) :
    (eligSet 14 D).card + 3 ≤ Bplus 14 D := by
  have hG := sem_heawood_gr
  have hC := sem_heawood_comp hD
  obtain ⟨b, hb⟩ := exists_pureBranch h hD
  obtain ⟨pos, hpos⟩ := k4_assigned hG h hC
  have hQ := (hpos.1 0 (hcap 0 (by decide))).2.2.1
  have hstar := tri_bound hG h hC b hb hpos {7, 8, 10} {0, 1, 2, 5} mx_A
    (fun i hi => ⟨hcap i hi, (mx_J i hi).1.imp (fun a ha => ⟨ha.1, (hc_adjB_iff _ _).1 ha.2⟩),
      fun f hf => ((mx_J i hi).2 f hf).imp (fun a ha => ⟨ha.1, (hc_adjB_iff _ _).1 ha.2⟩)⟩)
    (fun f hf => ⟨fun a ha b hb => sem_adjB_false.1 ((mx_Aok f hf).1 a ha b hb), (mx_Aok f hf).2.1,
      (mx_Aok f hf).2.2.imp (fun a ha => ⟨ha.1, (hc_adjB_iff _ _).1 ha.2⟩)⟩)
    rfl (by decide) (by decide) (by decide)
    (hQ 7 (by decide)) (hQ 8 (by decide)) (hQ 7 (by decide)) (hQ 10 (by decide))
  rw [show ({0, 1, 2, 5} : Finset (Fin 14)).card = 4 from rfl] at hstar
  omega

theorem elim_p9_mixed {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h13 : totalSurplus 14 D ≤ 13) (hI : ineligSet 14 D = {0, 1, 2, 5, 11}) : False := by
  classical
  have hel := inelig_card_add 14 D
  rw [hI, show ({0, 1, 2, 5, 11} : Finset (Fin 14)).card = 5 from rfl] at hel
  have hcap : ∀ i ∈ ({0, 1, 2, 5} : Finset (Fin 14)), i ∈ ineligSet 14 D := by rw [hI]; decide
  have hstar := mx_star h hD hcap
  have hLl : mx_L ⊆ sem_hw_opp 0 := by decide
  have hPe : mx_L ⊆ eligSet 14 D := by
    intro a ha
    by_contra hne
    have h1 := sem_mem_inelig.2 hne
    rw [hI] at h1
    exact mx_el a ha h1
  let Oc := ({0, 1, 2, 5} : Finset (Fin 14)).filter (fun i => sup_Occ 14 D mx_L (sem_hw_nb i))
  let Mc := ({0, 1, 2, 5} : Finset (Fin 14)).filter (fun i => ¬ sup_Occ 14 D mx_L (sem_hw_nb i))
  have hcnt := hw_count h hD mx_L hLl hPe Oc {3, 4, 6} {0, 1, 2, 5}
    (fun i hi => ⟨mx_cap i (Finset.mem_filter.1 hi).1, (Finset.mem_filter.1 hi).2⟩)
    (fun c hc => ⟨fun hc' => (mx_ctr c hc).1 (Finset.mem_filter.1 hc').1, Or.inl (mx_ctr c hc).2⟩)
    (fun i hi => ⟨hcap i hi, mx_cap i hi⟩)
  have hlost := hw_lost h hD mx_L
    (fun a ha b hb => sem_hw_opp_indep 0 a (hLl ha) b (hLl hb)) Mc
    (fun i hi => ⟨hcap i (Finset.mem_filter.1 hi).1, mx_cap i (Finset.mem_filter.1 hi).1,
      (Finset.mem_filter.1 hi).2⟩)
  have hsplit : Oc.card + Mc.card = 4 :=
    Finset.card_filter_add_card_filter_not (s := ({0, 1, 2, 5} : Finset (Fin 14)))
      (fun i => sup_Occ 14 D mx_L (sem_hw_nb i))
  rw [mx_lab, show ({0, 1, 2, 5} : Finset (Fin 14)).card = 4 from rfl,
    show mx_L.card = 6 from rfl] at hcnt
  have h4 := totalSurplus_split 14 D
  omega

section L3bGen

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

theorem ri_gen (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D) (b : Fin n → ℕ)
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

theorem zm_mem (hS : Strict n D) {c : Fin n} (hM : merges n D (carrierT n D {c}) = ∅)
    {e : ℕ × Bool} (he : e.1 < D.length) (ht : tag D e.1 = true)
    (hc : c ∈ supp n D (src D e)) : e ∈ sem_W n D c :=
  sem_mem_W.2 ⟨he, hc, fun hc2 => by
    have := (sem_zm_gate hS hM he hc2).1
    rw [ht] at this
    exact Bool.noConfusion this⟩

theorem gct_gen (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D) (b : Fin n → ℕ)
    (hb : sem_MinBranch n D b) {u0 : Σ _ : ℕ, ℕ} (hu0 : u0 ∈ residualUnits n D b)
    (X : Finset (Fin n)) (hX : X.Nonempty)
    (hsat : ∀ x ∈ X, merges n D (carrierT n D {x}) = ∅ ∧ x ∈ supp n D u0.1 ∧
      ∀ u ∈ residualUnits n D b, x ∈ supp n D u.1 → u = u0) :
    ∃ P Q : ℕ × Bool, P.1 ≠ Q.1 ∧ ∀ x ∈ X, P ∈ sem_W n D x ∧ Q ∈ sem_W n D x := by
  have hS := h.1
  have hu0u : u0 ∈ units n D := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hu0).1).1
  have hfr : 2 ≤ fanout D u0.1 := by
    have := (mem_units.mp hu0u).2
    omega
  refine sem_two_arms hG h hC X hX (fun x hx => (hsat x hx).1) u0.1
    (fun x hx => (hsat x hx).2.1) hfr ?_
  intro x hx w hrw hxw
  obtain ⟨-, hxr, huniq⟩ := hsat x hx
  have hxe : x ∈ eligSet n D := mem_eligSet.2 ⟨u0.1, hfr, hxr⟩
  by_contra hc
  have hwu : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ unitsPlus n D := by
    rw [unitsPlus, Finset.mem_filter, mem_units]
    exact ⟨⟨sb_mem_inner.mpr (lt_of_fanout_pos hS (w := w) (by omega)),
      by show 0 + 1 < fanout D w; omega⟩, ⟨x, hxw⟩⟩
  by_cases hwr : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ reservedUnits n D b
  · obtain ⟨v, hv, hveq⟩ := Finset.mem_image.mp hwr
    have hbv : b v = w := congrArg Sigma.fst hveq
    have hsv := (hb v hv).2.1
    rw [hbv] at hsv
    rw [hsv, Finset.mem_singleton] at hxw
    have hmin := (hb x hxe).2.2.2 u0.1 hfr hxr
    rw [hxw, hbv] at hmin
    omega
  · have h1 := huniq _ (Finset.mem_sdiff.mpr ⟨hwu, hwr⟩) hxw
    have : w = u0.1 := congrArg Sigma.fst h1
    omega

theorem full_gen (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (hB0 : Bzero n D = 0) {i v : Fin n} (hi : i ∈ ineligSet n D) {e : ℕ × Bool}
    (he : sem_W n D i = {e}) (hiv : G i v)
    (hv : ∀ p ∈ sem_W n D v, p.1 ≠ e.1 → ¬ supp n D (src D (sem_bar p)) ⊆ {i}) :
    ∀ t, t ∈ supp n D (src D (sem_bar e)) ↔ G i t := by
  have hS := h.1
  refine sem_full_support hG h hC hi he (fun j hreach hj => ?_)
  by_contra ht
  rw [Bool.not_eq_false] at ht
  rcases Relation.ReflTransGen.cases_tail hreach with heq | ⟨w, hw1, hw2⟩
  · exact hj (by omega)
  · obtain ⟨j', s, hj', hjeq, hsrc⟩ := sem_step_iff.1 hw2
    have hjj : j' = j := by omega
    subst hjj
    have hew : e ∈ sem_W n D i := by rw [he]; exact Finset.mem_singleton_self e
    obtain ⟨he1, he2, -⟩ := sem_mem_W.1 hew
    have hreach2 : Relation.ReflTransGen (sem_step n D) i.val w :=
      ((sem_rtg_mono (fun _ _ hab => hab.1) (sem_inelig_chain hS hi he2)).tail
        (sem_step_src he1 e.2)).trans hw1
    have hch := sem_noempty_unique hG h hC hB0 hi hreach2
    have hf : fanout D w = 1 := by
      have h1 := sem_step_fanout hw2
      by_contra hne
      have h2 := sem_branch_empty hG hS hC hi hch (by omega)
      have h4 := sem_bzero_branch hS hB0 (b := w) (by omega)
      rw [h2] at h4
      exact Finset.not_nonempty_empty h4
    have hsub : supp n D w ⊆ {i} := sem_dom_pure hG hS hC i w (sem_chain_dom hS hch)
    have hvi : v ≠ i := fun hvi => hG.2.1 i (hvi ▸ hiv)
    have hw' : src D (j', !(!s)) = w := by rw [Bool.not_not]; exact hsrc
    have hmem : v ∈ supp n D (src D (j', !s)) :=
      sem_and_sibling_nbrs hG hS hC hj' (!s) ht (hw' ▸ hch) (hw' ▸ hf)
        (by unfold outW; omega) hiv
    have hp : ((j', !s) : ℕ × Bool) ∈ sem_W n D v :=
      sem_mem_W.2 ⟨hj', hmem, fun hc => by
        have := hsub (hsrc ▸ sem_supp_and_sub hS hj' ht s hc)
        exact hvi (Finset.mem_singleton.1 this)⟩
    exact hv _ hp hj (by rw [show sem_bar (j', !s) = (j', !(!s)) from rfl, hw']; exact hsub)

theorem tri_occ (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (b : Fin n → ℕ) (hb : PureBranch n D b) {pos : Fin n → ℕ × Bool} (hpos : k4_Pos n G D pos)
    (T J : Finset (Fin n)) (A : Fin n → Finset (Fin n))
    (hJ : ∀ i ∈ J, i ∈ ineligSet n D ∧ (∃ a ∈ T, G i a) ∧ ∀ f ∈ T, ∃ a ∈ A f, G i a)
    (hA : ∀ f ∈ T, (∀ a ∈ A f, ∀ b ∈ A f, ¬ G a b) ∧ T.erase f ⊆ A f ∧ ∃ a ∈ A f, G f a)
    (F : Finset (Finset (Fin n))) (hF : ∀ M ∈ F, 2 ≤ M.card ∧ sup_Occ n D T M) :
    J.card + F.card + (eligSet n D).card ≤ T.card + Bplus n D := by
  have h1 := tri_exits hG h.1 hC hpos T J A hJ hA
  have h2 := sup_card_le_big h.1 T F hF
  have h3 : (sup_big n D T).card ≤ (merges n D (carrierT n D T)).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have h4 := carrier_flow_union h T (by rw [sem_supp_out hG hC]; simp)
  have h5 := surplus_carrierT_le h.1 b hb T
  have h6 := Finset.card_le_card (Finset.inter_subset_left : T ∩ eligSet n D ⊆ T)
  omega

end L3bGen

section L3bTri

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

theorem tri_sat (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (b : Fin n → ℕ) (hb : PureBranch n D b) {pos : Fin n → ℕ × Bool} (hpos : k4_Pos n G D pos)
    (T J : Finset (Fin n)) (A : Fin n → Finset (Fin n))
    (hJ : ∀ i ∈ J, i ∈ ineligSet n D ∧ (∃ a ∈ T, G i a) ∧ ∀ f ∈ T, ∃ a ∈ A f, G i a)
    (hA : ∀ f ∈ T, (∀ a ∈ A f, ∀ b ∈ A f, ¬ G a b) ∧ T.erase f ⊆ A f ∧ ∃ a ∈ A f, G f a)
    (F : Finset (Finset (Fin n))) (hF : ∀ M ∈ F, M.card = 2 ∧ sup_Occ n D T M)
    (hT3 : T.card = 3)
    (hbud : T.card + Bplus n D ≤ J.card + F.card + (eligSet n D).card) :
    (∀ w, ¬ T ⊆ supp n D w) ∧
    (∀ t ∈ T, merges n D (carrierT n D {t}) = ∅ ∧
      ∃ e1, ∀ e ∈ sem_W n D t, e = e1 ∨ e ∈ J.image pos) ∧
    ∀ u ∈ residualUnits n D b, (supp n D u.1 ∩ T).Nonempty := by
  classical
  have hS := h.1
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
  have hF2 : ∀ M ∈ F, 2 ≤ M.card ∧ sup_Occ n D T M :=
    fun M hM => ⟨by rw [(hF M hM).1], (hF M hM).2⟩
  have h2 := sup_card_le_big hS T F hF2
  have h3 : (sup_big n D T).card ≤ (merges n D (carrierT n D T)).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have h4 := carrier_flow_union h T (by rw [sem_supp_out hG hC]; simp)
  have h5 := surplus_carrierT_le hS b hb T
  have h6 := Finset.card_le_card (Finset.inter_subset_left : T ∩ eligSet n D ⊆ T)
  have hEx := Finset.card_le_card (Finset.union_subset hsub hsub2)
  rw [Finset.card_union_of_disjoint hdis, hcard, Finset.card_image_of_injOn hinj] at hEx
  have hexeq : J.image pos ∪ T.image w = exitArcs n D (carrierT n D T) :=
    Finset.eq_of_subset_of_card_le (Finset.union_subset hsub hsub2) (by
      rw [Finset.card_union_of_disjoint hdis, hcard, Finset.card_image_of_injOn hinj]; omega)
  have hbig : sup_big n D T = merges n D (carrierT n D T) :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
  have hnofull : ∀ w', ¬ T ⊆ supp n D w' := by
    intro w' hTw
    have hnot : T ∉ F := fun hTF => by have := (hF T hTF).1; omega
    have := sup_card_le_big hS T (insert T F) (fun M hM => by
      rcases Finset.mem_insert.1 hM with rfl | hM
      · exact ⟨by omega, ⟨w', Finset.inter_eq_right.2 hTw⟩⟩
      · exact hF2 M hM)
    rw [Finset.card_insert_of_notMem hnot] at this
    omega
  have hunits : ∀ u ∈ residualUnits n D b, (supp n D u.1 ∩ T).Nonempty := by
    have h7 := surplus_carrierT_eq hS b hb T
    have h8 := card_residual hS b hb
    have heq : (residualUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty) =
        residualUnits n D b :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
    intro u hu
    rw [← heq] at hu
    exact (Finset.mem_filter.1 hu).2
  have hmask : Set.InjOn (fun j => supp n D (n + j) ∩ T) (sup_big n D T) := by
    have hsubF : F ⊆ (sup_big n D T).image (fun j => supp n D (n + j) ∩ T) := by
      intro M hM
      obtain ⟨j, hj, hjM⟩ := sup_occ_big hS (hF2 M hM).1 (hF M hM).2
      exact Finset.mem_image.2 ⟨j, hj, hjM⟩
    have := Finset.card_le_card hsubF
    exact Finset.card_image_iff.1 (le_antisymm Finset.card_image_le (by omega))
  have hmemT : ∀ {t : Fin n} {v : ℕ}, t ∈ T → t ∈ supp n D v → v ∈ carrierT n D T :=
    fun ht hv => sup_mem_carrier.2 ⟨_, Finset.mem_inter.2 ⟨hv, ht⟩⟩
  refine ⟨hnofull, fun t ht => ⟨?_, w t, fun e he => ?_⟩, hunits⟩
  · rw [Finset.eq_empty_iff_forall_notMem]
    intro j hj
    rw [merges, Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨hjl, hj1, hj2, hj3⟩ := hj
    rw [sem_mem_carrier1] at hj1 hj2 hj3
    have hjT : j ∈ sup_big n D T := by
      rw [hbig, merges, Finset.mem_filter, Finset.mem_range]
      exact ⟨hjl, hmemT ht hj1, hmemT ht hj2, hmemT ht hj3⟩
    have hM2 : 2 ≤ (supp n D (n + j) ∩ T).card := (Finset.mem_filter.1 hjT).2
    obtain ⟨j0, -, -, hj0M, hj0mer, -, hstr⟩ := sem_first_mask hS T _ hM2 (n + j) rfl
    have hjj : j0 = j :=
      hmask (Finset.mem_filter.2 ⟨hj0mer, by rw [hj0M]; exact hM2⟩) hjT hj0M
    subst hjj
    have hlt : ∀ v, (supp n D v ∩ T).card < 3 := by
      intro v
      by_contra hc
      exact hnofull v (Finset.inter_eq_right.1
        (Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)))
    rcases hstr with ⟨-, hA1, -⟩ | ⟨-, hA1, hB1, hU, -, -⟩
    · have := Finset.card_lt_card hA1
      have := hlt (opA D j0)
      omega
    · have hcA := Finset.card_lt_card hA1
      have hcB := Finset.card_lt_card hB1
      have := hlt (n + j0)
      have hA' : ({t} : Finset (Fin n)) = supp n D (opA D j0) ∩ T :=
        Finset.eq_of_subset_of_card_le
          (Finset.singleton_subset_iff.2 (Finset.mem_inter.2 ⟨hj2, ht⟩))
          (by rw [Finset.card_singleton]; omega)
      have hB' : ({t} : Finset (Fin n)) = supp n D (opB D j0) ∩ T :=
        Finset.eq_of_subset_of_card_le
          (Finset.singleton_subset_iff.2 (Finset.mem_inter.2 ⟨hj3, ht⟩))
          (by rw [Finset.card_singleton]; omega)
      rw [← hU, ← hA', ← hB', Finset.union_self, Finset.card_singleton] at hM2
      omega
  · obtain ⟨he1, he2, he3⟩ := sem_mem_W.1 he
    have htag := sem_W_and hS he
    have hexit : e ∈ exitArcs n D (carrierT n D T) := by
      refine k4_mem_exit.2 ⟨he1, ⟨t, Finset.mem_inter.2 ⟨he2, ht⟩⟩, ?_⟩
      rintro ⟨g, hg⟩
      rw [Finset.mem_inter] at hg
      have hop : ∀ s, g ∈ supp n D (src D (e.1, s)) :=
        fun s => sem_supp_and_sub hS he1 htag s hg.1
      have hjT : e.1 ∈ sup_big n D T := by
        rw [hbig, merges, Finset.mem_filter, Finset.mem_range]
        refine ⟨he1, hmemT hg.2 hg.1, hmemT hg.2 ?_, hmemT hg.2 ?_⟩
        · have := hop false
          rwa [sb_src_false] at this
        · have := hop true
          rwa [sb_src_true] at this
      have hM2 : 2 ≤ (supp n D (n + e.1) ∩ T).card := (Finset.mem_filter.1 hjT).2
      have hsubE : supp n D (n + e.1) ∩ T ⊆ T.erase t := fun a ha =>
        Finset.mem_erase.2 ⟨fun hat => he3 (hat ▸ (Finset.mem_inter.1 ha).1),
          (Finset.mem_inter.1 ha).2⟩
      have heqE := Finset.eq_of_subset_of_card_le hsubE
        (by rw [Finset.card_erase_of_mem ht, hT3]; omega)
      apply hnofull (src D e)
      intro a ha
      by_cases hat : a = t
      · rw [hat]; exact he2
      · have : a ∈ supp n D (n + e.1) ∩ T := by
          rw [heqE]; exact Finset.mem_erase.2 ⟨hat, ha⟩
        exact sem_supp_and_sub hS he1 htag e.2 (Finset.mem_inter.1 this).1
    rw [← hexeq, Finset.mem_union] at hexit
    rcases hexit with h1 | h1
    · exact Or.inr h1
    · obtain ⟨f, hf, hfe⟩ := Finset.mem_image.1 h1
      left
      by_cases hft : f = t
      · rw [← hfe, hft]
      · exfalso
        exact Finset.disjoint_left.1 (hw f hf).2.2.2.2 (hfe ▸ he2)
          ((hA f hf).2.1 (Finset.mem_erase.2 ⟨fun h => hft h.symm, ht⟩))

end L3bTri

abbrev HG : Fin 14 → Fin 14 → Prop := fun u v => Adj u v

def ru (D : Dag) (b : Fin 14 → ℕ) (x : Fin 14) : Finset (Σ _ : ℕ, ℕ) :=
  (residualUnits 14 D b).filter (fun u => x ∈ supp 14 D u.1)

theorem mem_ru {D : Dag} {b : Fin 14 → ℕ} {x : Fin 14} {u : Σ _ : ℕ, ℕ} :
    u ∈ ru D b x ↔ u ∈ residualUnits 14 D b ∧ x ∈ supp 14 D u.1 := Finset.mem_filter

theorem res_fan {n : ℕ} {D : Dag} {b : Fin n → ℕ} {u : Σ _ : ℕ, ℕ}
    (hu : u ∈ residualUnits n D b) : 2 ≤ fanout D u.1 := by
  have := (mem_units.mp (Finset.mem_filter.mp (Finset.mem_sdiff.mp hu).1).1).2
  omega

theorem res_elig {n : ℕ} {D : Dag} {b : Fin n → ℕ} {u : Σ _ : ℕ, ℕ}
    (hu : u ∈ residualUnits n D b) {x : Fin n} (hx : x ∈ supp n D u.1) : x ∈ eligSet n D :=
  mem_eligSet.2 ⟨u.1, res_fan hu, hx⟩

theorem cc_le {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (b : Fin 14 → ℕ)
    (hb : PureBranch 14 D b) (x : Fin 14) :
    (sem_W 14 D x).card + (merges 14 D (carrierT 14 D {x})).card ≤ 2 + (ru D b x).card := by
  have h1 := sem_code_count sem_heawood_gr h (sem_heawood_comp hD) b hb x
  have h2 := Finset.card_le_card
    (Finset.inter_subset_left : ({x} : Finset (Fin 14)) ∩ eligSet 14 D ⊆ {x})
  rw [Finset.card_singleton] at h2
  unfold ru
  omega

theorem cc_el {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (b : Fin 14 → ℕ)
    (hb : PureBranch 14 D b) {x : Fin 14} (hx : x ∈ eligSet 14 D) :
    (sem_W 14 D x).card + (merges 14 D (carrierT 14 D {x})).card = 2 + (ru D b x).card := by
  have h1 := sem_code_count sem_heawood_gr h (sem_heawood_comp hD) b hb x
  rw [Finset.inter_eq_left.2 (Finset.singleton_subset_iff.2 hx), Finset.card_singleton] at h1
  unfold ru
  omega

theorem w_bar {n : ℕ} {D : Dag} (hS : Strict n D) {x : Fin n} {e : ℕ × Bool}
    (he : e ∈ sem_W n D x) : sem_bar e ∉ sem_W n D x := by
  intro hb
  obtain ⟨hj, hx, hn⟩ := sem_mem_W.mp he
  have hx' := (sem_mem_W.mp hb).2.1
  apply hn
  rw [sem_supp_and hS hj (sem_W_and hS he), Finset.mem_inter]
  obtain ⟨j, s⟩ := e
  cases s
  · exact ⟨by simpa [src] using hx, by simpa [src, sem_bar] using hx'⟩
  · exact ⟨by simpa [src, sem_bar] using hx', by simpa [src] using hx⟩

section Assigned

variable {D : Dag} {pos : Fin 14 → ℕ × Bool}

theorem as_mem (hpos : k4_Pos 14 HG D pos) {i a : Fin 14} (hi : i ∈ ineligSet 14 D)
    (hia : Adj i a) : pos i ∈ sem_W 14 D a := by
  obtain ⟨h1, h2, h4, -⟩ := hpos.1 i hi
  exact sem_mem_W.2 ⟨h1, h4 a hia, by rw [h2]; exact Finset.notMem_empty a⟩

theorem as_priv (hpos : k4_Pos 14 HG D pos) {i t : Fin 14} (hi : i ∈ ineligSet 14 D)
    (ht : sem_bar (pos i) ∈ sem_W 14 D t) : t = i := by
  have := (sem_mem_W.1 ht).2.1
  rw [show src D (sem_bar (pos i)) = src D ((pos i).1, !(pos i).2) from rfl,
    (hpos.1 i hi).2.2.2] at this
  exact Finset.mem_singleton.1 this

theorem as_W (h : StrictLive 14 D) (hD : Correct D) (hpos : k4_Pos 14 HG D pos) {i : Fin 14}
    (hi : i ∈ ineligSet 14 D) : sem_W 14 D i = {sem_bar (pos i)} := by
  obtain ⟨e, -, -, h3, -, -, h6, -⟩ :=
    sem_inelig_consumer sem_heawood_gr h (sem_heawood_comp hD) hi
  obtain ⟨h1, h2, -, h5⟩ := hpos.1 i hi
  have hm : sem_bar (pos i) ∈ sem_W 14 D i :=
    sem_mem_W.2 ⟨h1, by
      rw [show src D (sem_bar (pos i)) = src D ((pos i).1, !(pos i).2) from rfl, h5]
      exact Finset.mem_singleton_self i, by
      rw [show (sem_bar (pos i)).1 = (pos i).1 from rfl, h2]; exact Finset.notMem_empty i⟩
  have h7 : sem_W 14 D i = {e} := h6
  rw [h7] at hm ⊢
  rw [Finset.mem_singleton.1 hm]

theorem ps (h : StrictLive 14 D) (hD : Correct D) (hpos : k4_Pos 14 HG D pos) {i x : Fin 14}
    (hi : i ∈ ineligSet 14 D) (hxi : x ≠ i) (hY : pos i ∈ sem_W 14 D x)
    (hc : (sem_W 14 D x).card ≤ 2) :
    ∃ Z, Z ≠ pos i ∧ sem_W 14 D x = {pos i, Z} ∧ ∀ t, t ≠ x → Z ∉ sem_W 14 D t := by
  obtain ⟨Z, h1, h2, h3, -⟩ := sem_hw_private_slot h hD hi hxi (as_W h hD hpos hi)
    (by rw [sem_bar_bar]; exact hY) hc
  rw [sem_bar_bar] at h1 h2
  exact ⟨Z, h1, h2, h3⟩

theorem full (h : StrictLive 14 D) (hD : Correct D) (hB0 : Bzero 14 D = 0)
    (hpos : k4_Pos 14 HG D pos) {i v : Fin 14} (hi : i ∈ ineligSet 14 D) (hiv : Adj i v)
    (hv : ∀ p ∈ sem_W 14 D v, p.1 ≠ (pos i).1 → ¬ supp 14 D (src D (sem_bar p)) ⊆ {i}) :
    ∀ t, t ∈ supp 14 D (src D (pos i)) ↔ Adj i t := by
  have := full_gen sem_heawood_gr h (sem_heawood_comp hD) hB0 hi (as_W h hD hpos hi) hiv hv
  rwa [sem_bar_bar] at this

end Assigned

theorem hw_prot {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (hB0 : Bzero 14 D = 0)
    {i : Fin 14} (hi : i ∈ ineligSet 14 D) :
    ∀ w, Relation.ReflTransGen (sem_step 14 D) i.val w → fanout D w ≤ 1 := by
  intro w hw
  by_contra hc
  have h2 := sem_branch_empty sem_heawood_gr h.1 (sem_heawood_comp hD) hi
    (sem_noempty_unique sem_heawood_gr h (sem_heawood_comp hD) hB0 hi hw) (by omega)
  have h4 := sem_bzero_branch h.1 hB0 (b := w) (by omega)
  rw [h2] at h4
  exact Finset.not_nonempty_empty h4

theorem hw_exact {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (hB0 : Bzero 14 D = 0)
    {i : Fin 14} (hi : i ∈ ineligSet 14 D) {T : Finset (Fin 14)} (hT : T ⊆ sem_hw_opp i) :
    sup_Occ 14 D T (sem_hw_nb i ∩ T) := by
  by_contra hno
  have := hw_lost h hD (sem_hw_opp i) (sem_hw_opp_indep i) {i} (fun j hj => by
    rw [Finset.mem_singleton.1 hj]
    refine ⟨hi, fun a ha => sem_hw_nb_opp (hw_mem_nb.1 ha), ?_⟩
    rintro ⟨w, hw⟩
    exact hno ⟨w, by rw [← hw, Finset.inter_assoc, Finset.inter_eq_right.2 hT]⟩)
  rw [Finset.card_singleton] at this
  omega

def tA (T : Finset (Fin 14)) (f : Fin 14) : Finset (Fin 14) :=
  T.erase f ∪ Finset.univ.filter
    (fun a => hc_adjB f a = true ∧ ∀ g ∈ T.erase f, hc_adjB a g = false)

def tOK (T J : Finset (Fin 14)) : Bool :=
  decide (∀ i ∈ J, (∃ a ∈ T, hc_adjB i a = true) ∧
    ∀ f ∈ T, ∃ a ∈ tA T f, hc_adjB i a = true) &&
  decide (∀ f ∈ T, (∀ a ∈ tA T f, ∀ b ∈ tA T f, hc_adjB a b = false) ∧
    ∃ a ∈ tA T f, hc_adjB f a = true) &&
  decide (T.card = 3 ∧ J.card = 3) &&
  decide (∀ i ∈ J, T ⊆ sem_hw_opp 0 ∧ T ⊆ sem_hw_opp i ∧ sem_hw_nb i ⊆ sem_hw_opp 0 ∧
    (sem_hw_nb i ∩ T).card = 2) &&
  decide (∀ i ∈ J, ∀ j ∈ J, sem_hw_nb j ∩ T ⊆ sem_hw_nb i ∩ T → j = i) &&
  decide (∀ t ∈ T, (J.filter (fun i => hc_adjB i t = true)).card ≤ 2 ∧
    ∀ i ∈ J, hc_adjB i t = false → T.erase t ⊆ sem_hw_nb i)

theorem tOK_iff {T J : Finset (Fin 14)} (h : tOK T J = true) :
    (∀ i ∈ J, (∃ a ∈ T, hc_adjB i a = true) ∧ ∀ f ∈ T, ∃ a ∈ tA T f, hc_adjB i a = true) ∧
    (∀ f ∈ T, (∀ a ∈ tA T f, ∀ b ∈ tA T f, hc_adjB a b = false) ∧
      ∃ a ∈ tA T f, hc_adjB f a = true) ∧
    (T.card = 3 ∧ J.card = 3) ∧
    (∀ i ∈ J, T ⊆ sem_hw_opp 0 ∧ T ⊆ sem_hw_opp i ∧ sem_hw_nb i ⊆ sem_hw_opp 0 ∧
      (sem_hw_nb i ∩ T).card = 2) ∧
    (∀ i ∈ J, ∀ j ∈ J, sem_hw_nb j ∩ T ⊆ sem_hw_nb i ∩ T → j = i) ∧
    ∀ t ∈ T, (J.filter (fun i => hc_adjB i t = true)).card ≤ 2 ∧
      ∀ i ∈ J, hc_adjB i t = false → T.erase t ⊆ sem_hw_nb i := by
  simpa only [tOK, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using h

theorem tri_hyp {D : Dag} {T J : Finset (Fin 14)} (hOK : tOK T J = true)
    (hJ : ∀ i ∈ J, i ∈ ineligSet 14 D) :
    (∀ i ∈ J, i ∈ ineligSet 14 D ∧ (∃ a ∈ T, HG i a) ∧ ∀ f ∈ T, ∃ a ∈ tA T f, HG i a) ∧
    ∀ f ∈ T, (∀ a ∈ tA T f, ∀ b ∈ tA T f, ¬ HG a b) ∧ T.erase f ⊆ tA T f ∧
      ∃ a ∈ tA T f, HG f a := by
  obtain ⟨h1, h2, -⟩ := tOK_iff hOK
  exact ⟨fun i hi => ⟨hJ i hi, (h1 i hi).1.imp (fun _ ha => ⟨ha.1, (hc_adjB_iff _ _).1 ha.2⟩),
    fun f hf => ((h1 i hi).2 f hf).imp (fun _ ha => ⟨ha.1, (hc_adjB_iff _ _).1 ha.2⟩)⟩,
  fun f hf => ⟨fun a ha b hb => sem_adjB_false.1 ((h2 f hf).1 a ha b hb),
    Finset.subset_union_left,
    (h2 f hf).2.imp (fun _ ha => ⟨ha.1, (hc_adjB_iff _ _).1 ha.2⟩)⟩⟩

theorem tri_hw {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (hz : Bzero 14 D ≤ 1)
    {T J : Finset (Fin 14)} (hOK : tOK T J = true) (hJ : ∀ i ∈ J, i ∈ ineligSet 14 D) :
    (eligSet 14 D).card + 3 ≤ Bplus 14 D := by
  classical
  have hG := sem_heawood_gr
  have hC := sem_heawood_comp hD
  obtain ⟨b, hb⟩ := exists_pureBranch h hD
  obtain ⟨pos, hpos⟩ := k4_assigned hG h hC
  obtain ⟨hJ', hA'⟩ := tri_hyp hOK hJ
  obtain ⟨-, -, ⟨hT3, hJ3⟩, hside, hinj, -⟩ := tOK_iff hOK
  have hM : ∀ i ∈ J, ∃ M, sup_Occ 14 D T M ∧ sem_hw_nb i ∩ T ⊆ M ∧
      (sup_Occ 14 D (sem_hw_opp 0) (sem_hw_nb i) → M = sem_hw_nb i ∩ T) := by
    intro i hi
    by_cases hx : sup_Occ 14 D (sem_hw_opp 0) (sem_hw_nb i)
    · obtain ⟨w, hw⟩ := hx
      have : supp 14 D w ∩ T = sem_hw_nb i ∩ T := by
        rw [← hw, Finset.inter_assoc, Finset.inter_eq_right.2 (hside i hi).1]
      exact ⟨_, ⟨w, rfl⟩, this ▸ Finset.Subset.refl _, fun _ => this⟩
    · exact ⟨supp 14 D (src D (pos i)) ∩ T, ⟨_, rfl⟩, fun a ha => by
        rw [Finset.mem_inter, hw_mem_nb] at ha
        exact Finset.mem_inter.2 ⟨(hpos.1 i (hJ i hi)).2.2.1 a ha.1, ha.2⟩,
        fun hc => absurd hc hx⟩
  choose! M hM using hM
  have hlost := hw_lost h hD (sem_hw_opp 0) (sem_hw_opp_indep 0)
    (J.filter (fun i => ¬ sup_Occ 14 D (sem_hw_opp 0) (sem_hw_nb i))) (fun i hi => by
      rw [Finset.mem_filter] at hi
      exact ⟨hJ i hi.1, (hside i hi.1).2.2.1, hi.2⟩)
  have hMinj : Set.InjOn M J := by
    intro i hi j hj hij
    by_contra hne
    have key : ∀ i ∈ J, ∀ j ∈ J, M i = M j → i ≠ j →
        ¬ sup_Occ 14 D (sem_hw_opp 0) (sem_hw_nb i) := by
      intro i hi j hj hij hne hx
      exact hne (hinj i hi j hj (by
        rw [← (hM i hi).2.2 hx, hij]; exact (hM j hj).2.1)).symm
    have h1 : i ∈ J.filter (fun i => ¬ sup_Occ 14 D (sem_hw_opp 0) (sem_hw_nb i)) :=
      Finset.mem_filter.2 ⟨hi, key i hi j hj hij hne⟩
    have h2 : j ∈ J.filter (fun i => ¬ sup_Occ 14 D (sem_hw_opp 0) (sem_hw_nb i)) :=
      Finset.mem_filter.2 ⟨hj, key j hj i hi hij.symm (Ne.symm hne)⟩
    have := Finset.one_lt_card.2 ⟨i, h1, j, h2, hne⟩
    omega
  have := tri_occ hG h hC b hb hpos T J (tA T) hJ' hA' (J.image M) (fun X hX => by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hX
    have := Finset.card_le_card (hM i hi).2.1
    rw [(hside i hi).2.2.2] at this
    exact ⟨this, (hM i hi).1⟩)
  rw [Finset.card_image_of_injOn hMinj] at this
  omega

theorem tri012 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h012 : ∀ i ∈ ({0, 1, 2} : Finset (Fin 14)), i ∈ ineligSet 14 D) :
    (eligSet 14 D).card + 2 ≤ Bplus 14 D := by
  have hG := sem_heawood_gr
  have hC := sem_heawood_comp hD
  obtain ⟨b, hb⟩ := exists_pureBranch h hD
  obtain ⟨pos, hpos⟩ := k4_assigned hG h hC
  have hOK : tOK {7, 8, 13} {0, 1, 2} = true := by decide +kernel
  obtain ⟨hJ', hA'⟩ := tri_hyp hOK h012
  have h0 := (hpos.1 0 (h012 0 (by decide))).2.2.1
  have h1 := (hpos.1 1 (h012 1 (by decide))).2.2.1
  have := tri_bound hG h hC b hb hpos {7, 8, 13} {0, 1, 2} (tA {7, 8, 13}) hJ' hA' rfl
    (by decide) (by decide) (by decide) (h0 7 (by decide)) (h0 8 (by decide))
    (h1 7 (by decide)) (h1 13 (by decide))
  rw [show ({0, 1, 2} : Finset (Fin 14)).card = 3 from rfl] at this
  omega

theorem tri13 {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (h13 : totalSurplus 14 D ≤ 13)
    (h012 : ∀ i ∈ ({0, 1, 2} : Finset (Fin 14)), i ∈ ineligSet 14 D)
    (h10 : 10 ≤ (eligSet 14 D).card) : (eligSet 14 D).card + 3 ≤ Bplus 14 D := by
  have h1 := tri012 h hD h012
  have h2 := totalSurplus_split 14 D
  exact tri_hw h hD (by omega) (by decide +kernel : tOK {7, 8, 13} {0, 1, 2} = true) h012

theorem tri_hw_sat {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (hB0 : Bzero 14 D = 0)
    (hB : Bplus 14 D ≤ (eligSet 14 D).card + 3) (b : Fin 14 → ℕ) (hb : PureBranch 14 D b)
    {T J : Finset (Fin 14)} (hOK : tOK T J = true) (hJ : ∀ i ∈ J, i ∈ ineligSet 14 D) :
    (∀ t ∈ T, (sem_W 14 D t).card ≤ 3 ∧ merges 14 D (carrierT 14 D {t}) = ∅) ∧
    ∀ u ∈ residualUnits 14 D b, (supp 14 D u.1 ∩ T).Nonempty := by
  classical
  have hG := sem_heawood_gr
  have hC := sem_heawood_comp hD
  obtain ⟨pos, hpos⟩ := k4_assigned hG h hC
  obtain ⟨hJ', hA'⟩ := tri_hyp hOK hJ
  obtain ⟨-, -, ⟨hT3, hJ3⟩, hside, hinj, hgeo⟩ := tOK_iff hOK
  have hFinj : Set.InjOn (fun i => sem_hw_nb i ∩ T) J :=
    fun i hi j hj hij => hinj j hj i hi (by rw [show sem_hw_nb i ∩ T = sem_hw_nb j ∩ T from hij])
  obtain ⟨hnofull, hT, hU⟩ := tri_sat hG h hC b hb hpos T J (tA T) hJ' hA'
    (J.image (fun i => sem_hw_nb i ∩ T)) (fun X hX => by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hX
      exact ⟨(hside i hi).2.2.2, hw_exact h hD hB0 (hJ i hi) (hside i hi).2.1⟩) hT3
    (by rw [Finset.card_image_of_injOn hFinj]; omega)
  refine ⟨fun t ht => ⟨?_, (hT t ht).1⟩, hU⟩
  obtain ⟨e1, he1⟩ := (hT t ht).2
  have hsub : sem_W 14 D t ⊆ insert e1 ((J.filter (fun i => hc_adjB i t = true)).image pos) := by
    intro e he
    rcases he1 e he with rfl | h1
    · exact Finset.mem_insert_self _ _
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 h1
      refine Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨i, Finset.mem_filter.2 ⟨hi, ?_⟩, rfl⟩)
      by_contra hadj
      rw [Bool.not_eq_true] at hadj
      refine hnofull (src D (pos i)) (fun a ha => ?_)
      by_cases hat : a = t
      · rw [hat]; exact (sem_mem_W.1 he).2.1
      · exact (hpos.1 i (hJ i hi)).2.2.1 a
          (hw_mem_nb.1 ((hgeo t ht).2 i hi hadj (Finset.mem_erase.2 ⟨hat, ha⟩)))
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_insert_le e1 ((J.filter (fun i => hc_adjB i t = true)).image pos)
  have h4 := Finset.card_image_le (s := J.filter (fun i => hc_adjB i t = true)) (f := pos)
  have h5 := (hgeo t ht).1
  omega

def cf_rho (c v : Fin 14) : Option Bool :=
  if v = c then some true else if hc_adjB c v = true then some false else none

def cf_iota (l : List ℕ) (k : Fin 10) : Fin 14 := Fin.ofNat 14 (l.getD k.val 0)

abbrev cf_good (c : Fin 14) (l : List ℕ) : Prop :=
  (∀ a b : Fin 10, cf_iota l a = cf_iota l b → a = b) ∧
  (∀ v : Fin 14, cf_rho c v = none ↔ ∃ i : Fin 10, cf_iota l i = v) ∧
  ∀ u v : Fin 10, hc_adjB (cf_iota l u) (cf_iota l v) = k4_adjB u v

def cfL7 : List ℕ := [2, 4, 5, 6, 13, 12, 8, 10, 11, 9]

def cfL3 : List ℕ := [8, 9, 10, 13, 6, 0, 2, 5, 1, 4]

theorem cf7_good : cf_good 7 cfL7 := by decide +kernel

theorem cf3_good : cf_good 3 cfL3 := by decide +kernel

theorem cf_main {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (b : Fin 14 → ℕ)
    (hb : PureBranch 14 D b) {c : Fin 14} {l : List ℕ} (hgood : cf_good c l)
    (hc : c ∈ eligSet 14 D) (X : Finset (Fin 14))
    (hX : ∀ x ∈ X, x ∈ eligSet 14 D ∧ x ≠ c ∧
      (∀ u ∈ residualUnits 14 D b, x ∈ supp 14 D u.1 → c ∈ supp 14 D u.1) ∧
      ∃ w, x ∈ supp 14 D w ∧ c ∈ supp 14 D w) :
    ∃ E : Dag, StrictLive 10 E ∧ sem_Comp 10 k4_Adj E ∧
      totalSurplus 10 E + ((ru D b c).card + X.card + 1) ≤ totalSurplus 14 D ∧
      Bplus 10 E + ((ru D b c).card + X.card + 1) ≤ totalSurplus 14 D ∧
      ∀ i : Fin 10, (∀ w, Relation.ReflTransGen (sem_step 14 D) (cf_iota l i).val w →
        fanout D w ≤ 1) → i ∈ ineligSet 10 E := by
  classical
  have hG := sem_heawood_gr
  have hC := sem_heawood_comp hD
  have hS := h.1
  obtain ⟨hinj, hfree, hiso⟩ := hgood
  have hok : cof_Ok (cf_rho c) (cf_iota l) := ⟨fun a b hab => hinj a b hab, hfree⟩
  have hρc : cf_rho c c = some true := by simp [cf_rho]
  have hT : ∀ d a : Fin 14, cf_rho c d = some true → HG d a → cf_rho c a = some false := by
    intro d a h1 h2
    have hd : d = c := by
      by_contra hne
      unfold cf_rho at h1
      simp only [hne, ite_false] at h1
      split at h1 <;> simp at h1
    subst hd
    have hne : a ≠ d := fun hac => adj_irrefl d (hac ▸ h2)
    simp [cf_rho, hne, (hc_adjB_iff d a).2 h2]
  have heq : (fun u v : Fin 10 => HG (cf_iota l u) (cf_iota l v)) = k4_Adj := by
    funext u v
    exact propext (by
      show Adj _ _ ↔ k4_adjB u v = true
      rw [← hiso u v]; exact (hc_adjB_iff _ _).symm)
  obtain ⟨E, hE, hCE, hsur, hsurP, hprot⟩ := cof_restrict_graph hS hok hC
    (fun _ _ huv => adj_symm huv) hT (by rw [heq]; exact k4_gr) (by norm_num)
  have hbel : ∀ x ∈ eligSet 14 D, (⟨b x, 0⟩ : Σ _ : ℕ, ℕ) ∈ units 14 D := fun x hx =>
    mem_units.2 ⟨sb_mem_inner.2 (lt_of_fanout_pos hS (w := b x) (by
      have := (hb x hx).1; omega)), by
      show 0 + 1 < fanout D (b x); have := (hb x hx).1; omega⟩
  have hel : ∀ x ∈ insert c X, x ∈ eligSet 14 D := fun x hx => by
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact hc
    · exact (hX x hx).1
  have hS2inj : Set.InjOn (fun x => (⟨b x, 0⟩ : Σ _ : ℕ, ℕ))
      (insert c X : Finset (Fin 14)) := by
    intro x hx y hy hxy
    have h1 : b x = b y := congrArg Sigma.fst hxy
    have h2 := (hb x (hel x hx)).2
    rw [h1, (hb y (hel y hy)).2] at h2
    exact (Finset.singleton_injective h2).symm
  have hdis : Disjoint (ru D b c)
      ((insert c X).image (fun x => (⟨b x, 0⟩ : Σ _ : ℕ, ℕ))) := by
    rw [Finset.disjoint_left]
    intro u hu1 hu2
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hu2
    exact (Finset.mem_sdiff.1 (mem_ru.1 hu1).1).2 (Finset.mem_image.2 ⟨x, hel x hx, rfl⟩)
  have hsub : ru D b c ∪ (insert c X).image (fun x => (⟨b x, 0⟩ : Σ _ : ℕ, ℕ)) ⊆
      units 14 D := by
    intro u hu
    rcases Finset.mem_union.1 hu with hu | hu
    · exact (Finset.mem_filter.1 (Finset.mem_sdiff.1 (mem_ru.1 hu).1).1).1
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hu
      exact hbel x (hel x hx)
  have hlost : ∀ u ∈ ru D b c ∪ (insert c X).image (fun x => (⟨b x, 0⟩ : Σ _ : ℕ, ℕ)),
      u ∉ cof_kept D (cf_rho c) (cf_iota l) := by
    intro u hu
    rcases Finset.mem_union.1 hu with hu | hu
    · exact cof_lost_of_true hS hρc (mem_ru.1 hu).2
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hu
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact cof_lost_of_true hS hρc (by
          show x ∈ supp 14 D (b x)
          rw [(hb x hc).2]; exact Finset.mem_singleton_self x)
      · obtain ⟨hxe, hxc, hres, w, hw⟩ := hX x hx
        obtain ⟨z, hxz, hcz⟩ := hG.2.2.1 x c hxc
        obtain ⟨hs1, -, -, e, he, -, hec⟩ :=
          sem_diff_two_exits hG h hC b hb hxc hxe hres hw hxz hcz
        have hbx : b x ∈ carrierDiff 14 D x c := sem_mem_diff.2 (by
          rw [(hb x hxe).2]
          exact ⟨Finset.mem_singleton_self x,
            fun hcx => hxc (Finset.mem_singleton.1 hcx).symm⟩)
        exact cof_lost_of_deg (cof_diff_deplete hS hρc hbx (hb x hxe).1 hs1 he hec)
  have hcard : (ru D b c ∪ (insert c X).image (fun x => (⟨b x, 0⟩ : Σ _ : ℕ, ℕ))).card =
      (ru D b c).card + X.card + 1 := by
    rw [Finset.card_union_of_disjoint hdis, Finset.card_image_of_injOn hS2inj,
      Finset.card_insert_of_notMem (fun hcX => (hX c hcX).2.1 rfl)]
    omega
  have h1 := cof_sur_add_lost _ hsub hlost
  have h2 := cof_surP_add_lost _ hsub (fun u hu hk => hlost u hu (cof_keptP_sub hk))
  rw [hcard] at h1 h2
  exact ⟨E, hE, heq ▸ hCE, by omega, by omega, hprot⟩

theorem cf_six {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (b : Fin 14 → ℕ)
    (hb : PureBranch 14 D b) {c : Fin 14} {l : List ℕ} (hgood : cf_good c l)
    (hc : c ∈ eligSet 14 D) (X : Finset (Fin 14))
    (hX : ∀ x ∈ X, x ∈ eligSet 14 D ∧ x ≠ c ∧
      (∀ u ∈ residualUnits 14 D b, x ∈ supp 14 D u.1 → c ∈ supp 14 D u.1) ∧
      ∃ w, x ∈ supp 14 D w ∧ c ∈ supp 14 D w) :
    (ru D b c).card + X.card + 7 ≤ totalSurplus 14 D := by
  obtain ⟨E, hE, hCE, -, h2, -⟩ := cf_main h hD b hb hgood hc X hX
  have := k4_surplus_six hE hCE
  omega

theorem cf_seven {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (hB0 : Bzero 14 D = 0)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b) {c : Fin 14} {l : List ℕ}
    (hgood : cf_good c l) (hc : c ∈ eligSet 14 D) (X : Finset (Fin 14))
    (hX : ∀ x ∈ X, x ∈ eligSet 14 D ∧ x ≠ c ∧
      (∀ u ∈ residualUnits 14 D b, x ∈ supp 14 D u.1 → c ∈ supp 14 D u.1) ∧
      ∃ w, x ∈ supp 14 D w ∧ c ∈ supp 14 D w) {i1 i2 : Fin 10}
    (h1 : cf_iota l i1 ∈ ineligSet 14 D) (h2 : cf_iota l i2 ∈ ineligSet 14 D)
    (hm : (i1 = 4 ∧ i2 = 9) ∨ (i1 = 5 ∧ i2 = 8) ∨ (i1 = 6 ∧ i2 = 7)) :
    (ru D b c).card + X.card + 8 ≤ totalSurplus 14 D := by
  obtain ⟨E, hE, hCE, h4, -, hp⟩ := cf_main h hD b hb hgood hc X hX
  have := k4_surplus_seven_matching hE hCE (hp i1 (hw_prot h hD hB0 h1))
    (hp i2 (hw_prot h hD hB0 h2)) hm
  omega

theorem pa_card3 {α : Type} [DecidableEq α] {s : Finset α} {a b c : α} (ha : a ∈ s)
    (hb : b ∈ s) (hc : c ∈ s) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : 3 ≤ s.card := by
  have hsub : ({a, b, c} : Finset α) ⊆ s := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl <;> assumption
  have := Finset.card_le_card hsub
  rwa [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc] at this

theorem pa_three {α : Type} [DecidableEq α] {s : Finset α} {a b c : α} (ha : a ∈ s)
    (hb : b ∈ s) (hc : c ∈ s) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hs : s.card ≤ 3) :
    ∀ e ∈ s, e = a ∨ e = b ∨ e = c := by
  intro e he
  by_contra hne
  rw [not_or, not_or] at hne
  have := pa_card3 (s := s.erase e) (Finset.mem_erase.2 ⟨Ne.symm hne.1, ha⟩)
    (Finset.mem_erase.2 ⟨Ne.symm hne.2.1, hb⟩) (Finset.mem_erase.2 ⟨Ne.symm hne.2.2, hc⟩)
    hab hac hbc
  rw [Finset.card_erase_of_mem he] at this
  omega

theorem pa_two {α : Type} [DecidableEq α] {s : Finset α} {a b : α} (ha : a ∈ s) (hb : b ∈ s)
    (hab : a ≠ b) (hs : s.card ≤ 2) : ∀ e ∈ s, e = a ∨ e = b := by
  intro e he
  by_contra hne
  rw [not_or] at hne
  have := pa_card3 he ha hb hne.1 hne.2 hab
  omega

theorem pa_q : ∀ i k t : Fin 14, hc_adjB i k = true → t ≠ i →
    ∃ q, hc_adjB i q = true ∧ q ≠ k ∧ q ≠ t ∧ hc_adjB t q = false := by decide +kernel

theorem pa_cf {D : Dag} (h : StrictLive 14 D) (hD : Correct D) {x a b : Fin 14} (hxa : x ≠ a)
    (hxb : x ≠ b) (hab : ¬ Adj a b)
    (hsub : ∀ e ∈ sem_W 14 D x, e ∈ sem_W 14 D a ∨ e ∈ sem_W 14 D b) : False := by
  obtain ⟨e, he, h1, h2⟩ := sem_hw_cover_free h hD hxa hxb hab
  rcases hsub e he with h3 | h3
  exacts [h1 (sem_mem_W.1 h3).2.1, h2 (sem_mem_W.1 h3).2.1]

theorem pa_ed {D : Dag} (h : StrictLive 14 D) (hD : Correct D) {pos : Fin 14 → ℕ × Bool}
    (hpos : k4_Pos 14 HG D pos) {x y : Fin 14} (hxy : Adj x y) :
    ∃ e ∈ sem_W 14 D x, sem_bar e ∈ sem_W 14 D y ∧
      (∀ i ∈ ineligSet 14 D, e = pos i → y = i) ∧
      ∀ i ∈ ineligSet 14 D, sem_bar e = pos i → x = i := by
  obtain ⟨e, he, hb, -⟩ := sem_edge_slots sem_heawood_gr h.1 (sem_heawood_comp hD) hxy
  exact ⟨e, he, hb, fun i hi hei => as_priv hpos hi (hei ▸ hb),
    fun i hi hei => as_priv hpos hi (by rw [← hei, sem_bar_bar]; exact he)⟩

def pa_ctx (D : Dag) (pos : Fin 14 → ℕ × Bool) (P Q : ℕ × Bool) : Prop :=
  k4_Pos 14 HG D pos ∧ (∀ x, (sem_W 14 D x).card ≤ 3) ∧ P ≠ Q ∧
    ∀ x, 3 ≤ (sem_W 14 D x).card → P ∈ sem_W 14 D x ∧ Q ∈ sem_W 14 D x

theorem pa_setup {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h13 : totalSurplus 14 D ≤ 13) (h0 : (0 : Fin 14) ∈ ineligSet 14 D)
    (hp : (eligSet 14 D).card = 12) : ∃ pos P Q, pa_ctx D pos P Q := by
  classical
  have hG := sem_heawood_gr
  have hC := sem_heawood_comp hD
  obtain ⟨b, hb⟩ := sem_exists_minBranch hG h.1 hC
  have hbp := sem_minBranch_pure hb
  obtain ⟨pos, hpos⟩ := k4_assigned hG h hC
  have h1 := card_residual h.1 b hbp
  have h2 := Bplus_le_total 14 D
  have hB : Bplus 14 D = 13 := by
    by_contra hne
    exact tight_le h hD (by omega) h0
  have hc3 : ∀ x, (sem_W 14 D x).card ≤ 3 := fun x => by
    have h3 := cc_le h hD b hbp x
    have h4 : (ru D b x).card ≤ (residualUnits 14 D b).card := Finset.card_filter_le _ _
    omega
  by_cases hX : (Finset.univ.filter (fun x : Fin 14 => 3 ≤ (sem_W 14 D x).card)).Nonempty
  · obtain ⟨P, Q, hPQ, hall⟩ := sem_common_terminals hG h hC b hb (by omega) _ hX
      (fun x hx => (Finset.mem_filter.1 hx).2)
    exact ⟨pos, P, Q, hpos, hc3, fun hpq => hPQ (hpq ▸ rfl),
      fun x hx => hall x (Finset.mem_filter.2 ⟨Finset.mem_univ x, hx⟩)⟩
  · exact ⟨pos, (0, false), (1, false), hpos, hc3, by decide,
      fun x hx => (hX ⟨x, Finset.mem_filter.2 ⟨Finset.mem_univ x, hx⟩⟩).elim⟩

theorem elim_p12_same {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h13 : totalSurplus 14 D ≤ 13) (hI : ineligSet 14 D = {0, 1}) : False := by
  have hel := inelig_card_add 14 D
  rw [hI, show ({0, 1} : Finset (Fin 14)).card = 2 from rfl] at hel
  have hi0 : (0 : Fin 14) ∈ ineligSet 14 D := by rw [hI]; decide
  have hi1 : (1 : Fin 14) ∈ ineligSet 14 D := by rw [hI]; decide
  have hel2 : ∀ x : Fin 14, x ∉ ({0, 1} : Finset (Fin 14)) → x ∉ ineligSet 14 D :=
    fun x hx => hI ▸ hx
  have hadj : ∀ i ∈ ineligSet 14 D, Adj i 7 := by rw [hI]; decide
  obtain ⟨pos, P, Q, hpos, hc3, hPQ, hsat⟩ := pa_setup h hD h13 hi0 (by omega)
  have y7 := fun i hi => as_mem hpos hi (hadj i hi)
  have y01 : pos 0 ≠ pos 1 := fun he => absurd (hpos.2 0 hi0 1 hi1 he) (by decide)
  obtain ⟨H, hH, -, hHf, -⟩ := pa_ed h hD hpos (show Adj 7 3 by decide)
  obtain ⟨hP7, hQ7⟩ := hsat 7 (pa_card3 (y7 0 hi0) (y7 1 hi1) hH y01
    (fun he => absurd (hHf 0 hi0 he.symm) (by decide))
    (fun he => absurd (hHf 1 hi1 he.symm) (by decide)))
  have hS : ∀ t, 3 ≤ (sem_W 14 D t).card → ∀ j ∈ ineligSet 14 D, pos j ∈ sem_W 14 D t := by
    intro t ht j hj
    by_contra hn
    obtain ⟨hP, hQ⟩ := hsat t ht
    obtain ⟨q, hq1, hq7, -, hq2⟩ := pa_q j 7 t ((hc_adjB_iff _ _).2 (hadj j hj)) (fun hti => by
      rw [hti, as_W h hD hpos hj, Finset.card_singleton] at ht
      omega)
    refine pa_cf h hD (fun e : (7 : Fin 14) = t => hn (e ▸ y7 j hj)) hq7.symm
      (sem_adjB_false.1 hq2) (fun e he => ?_)
    rcases pa_three (y7 j hj) hP7 hQ7 (fun e => hn (e ▸ hP)) (fun e => hn (e ▸ hQ)) hPQ
      (hc3 7) e he with rfl | rfl | rfl
    exacts [Or.inr (as_mem hpos hj ((hc_adjB_iff _ _).1 hq1)), Or.inl hP, Or.inl hQ]
  have hline : ∀ l i z : Fin 14, i ∈ ineligSet 14 D → Adj i l → Adj l z →
      z ∉ ineligSet 14 D → ∃ Z ∈ sem_W 14 D l,
        (∀ e ∈ sem_W 14 D l, e = Z ∨ ∃ j ∈ ineligSet 14 D, e = pos j) ∧
        ∀ y, Adj l y → y ∉ ineligSet 14 D → sem_bar Z ∈ sem_W 14 D y := by
    intro l i z hi hil hlz hz
    obtain ⟨Z, hZ, -, hZf, -⟩ := pa_ed h hD hpos hlz
    have hfree : ∀ j ∈ ineligSet 14 D, pos j ≠ Z := fun j hj he => hz (hZf j hj he.symm ▸ hj)
    have hall : ∀ e ∈ sem_W 14 D l, e = Z ∨ ∃ j ∈ ineligSet 14 D, e = pos j := by
      intro e he
      by_cases h3 : 3 ≤ (sem_W 14 D l).card
      · rcases pa_three (hS l h3 0 hi0) (hS l h3 1 hi1) hZ y01 (hfree 0 hi0) (hfree 1 hi1)
          (hc3 l) e he with h1 | h1 | h1
        exacts [Or.inr ⟨0, hi0, h1⟩, Or.inr ⟨1, hi1, h1⟩, Or.inl h1]
      · rcases pa_two (as_mem hpos hi hil) hZ (hfree i hi) (by omega) e he with h1 | h1
        exacts [Or.inr ⟨i, hi, h1⟩, Or.inl h1]
    refine ⟨Z, hZ, hall, fun y hly hy => ?_⟩
    obtain ⟨e, he, hb, hf, -⟩ := pa_ed h hD hpos hly
    rcases hall e he with rfl | ⟨j, hj, rfl⟩
    exacts [hb, (hy (hf j hj rfl ▸ hj)).elim]
  have e2 := hel2 2 (by decide)
  obtain ⟨Z8, hZ8, a8, b8⟩ := hline 8 0 2 hi0 (by decide) (by decide) e2
  obtain ⟨Z13, hZ13, -, b13⟩ := hline 13 1 2 hi1 (by decide) (by decide) e2
  have m8 := b8 2 (by decide) e2
  have m13 := b13 2 (by decide) e2
  have hbne : sem_bar Z8 ≠ sem_bar Z13 := by
    intro he
    have hZ : Z8 = Z13 := by rw [← sem_bar_bar Z8, he, sem_bar_bar]
    refine pa_cf h hD (by decide : (8 : Fin 14) ≠ 7) (by decide : (8 : Fin 14) ≠ 13)
      (by decide) (fun e he => ?_)
    rcases a8 e he with rfl | ⟨j, hj, rfl⟩
    exacts [Or.inr (hZ ▸ hZ13), Or.inl (y7 j hj)]
  have hfr : ∀ (Z : ℕ × Bool) (l i : Fin 14), Z ∈ sem_W 14 D l → i ∈ ineligSet 14 D →
      l ∉ ({0, 1} : Finset (Fin 14)) → pos i ≠ sem_bar Z := fun Z l i hZ hii hl he =>
    hel2 l hl (as_priv hpos hii (by rw [he, sem_bar_bar]; exact hZ) ▸ hii)
  by_cases h3 : 3 ≤ (sem_W 14 D 2).card
  · rcases pa_three (hS 2 h3 0 hi0) (hS 2 h3 1 hi1) m8 y01 (hfr Z8 8 0 hZ8 hi0 (by decide))
      (hfr Z8 8 1 hZ8 hi1 (by decide)) (hc3 2) _ m13 with h1 | h1 | h1
    exacts [hfr Z13 13 0 hZ13 hi0 (by decide) h1.symm,
      hfr Z13 13 1 hZ13 hi1 (by decide) h1.symm, hbne h1.symm]
  · exact pa_cf h hD (by decide : (2 : Fin 14) ≠ 6) (by decide : (2 : Fin 14) ≠ 4)
      (by decide) (fun e he => by
        rcases pa_two m8 m13 hbne (by omega) e he with rfl | rfl
        exacts [Or.inl (b8 6 (by decide) (hel2 6 (by decide))),
          Or.inr (b13 4 (by decide) (hel2 4 (by decide)))])

theorem pa_m1 {D : Dag} (h : StrictLive 14 D) (hD : Correct D) {pos : Fin 14 → ℕ × Bool}
    (hpos : k4_Pos 14 HG D pos) (z k v iz ik : Fin 14)
    (hin : (∀ a ∈ ({iz, ik} : Finset (Fin 14)), a ∈ ineligSet 14 D) ∧
      ∀ a ∈ ({z, k, v} : Finset (Fin 14)), a ∉ ineligSet 14 D)
    (hg : hc_adjB iz z = true ∧ hc_adjB ik k = true ∧ hc_adjB z k = true ∧
      hc_adjB z v = true ∧ v ≠ k)
    (hcz : (sem_W 14 D z).card ≤ 2) (hck : (sem_W 14 D k).card ≤ 2) : False := by
  obtain ⟨g1, g2, g3, g4, g5⟩ := hg
  rw [hc_adjB_iff] at g1 g2 g3 g4
  have hiz := hin.1 iz (by simp)
  have hik := hin.1 ik (by simp)
  have hk := hin.2 k (by simp)
  obtain ⟨Dk, -, hWk, hpk⟩ :=
    ps h hD hpos hik (fun e : k = ik => hk (e ▸ hik)) (as_mem hpos hik g2) hck
  obtain ⟨e, he, hbe, hf, hf'⟩ := pa_ed h hD hpos g3
  obtain ⟨e', he', hbe', hg', -⟩ := pa_ed h hD hpos g4
  rw [hWk, Finset.mem_insert, Finset.mem_singleton] at hbe
  have hb : sem_bar e = Dk :=
    hbe.resolve_left (fun hh => hin.2 z (by simp) (hf' ik hik hh ▸ hik))
  rcases pa_two (as_mem hpos hiz g1) he (fun hh => hk (hf iz hiz hh.symm ▸ hiz)) hcz e' he'
    with h1 | h1
  · exact hin.2 v (by simp) (hg' iz hiz h1 ▸ hiz)
  · exact hpk v g5 (by rw [← hb, ← h1]; exact hbe')

def pa_C (D : Dag) (pos : Fin 14 → ℕ × Bool) (P Q : ℕ × Bool) (y : Fin 14) : Prop :=
  ∃ e, (e = P ∨ e = Q) ∧ (∀ i ∈ ineligSet 14 D, e ≠ pos i) ∧
    (∀ s, s ≠ y → sem_bar e ∉ sem_W 14 D s) ∧ sem_bar e ∈ sem_W 14 D y ∧
    ∃ i ∈ ineligSet 14 D, pos i = P ∨ pos i = Q

theorem pa_edge {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    {pos : Fin 14 → ℕ × Bool} {P Q : ℕ × Bool} (hc : pa_ctx D pos P Q)
    (x y t w ix iy xa xb : Fin 14)
    (hin : (∀ a ∈ ({ix, iy} : Finset (Fin 14)), a ∈ ineligSet 14 D) ∧
      ∀ a ∈ ({x, y, w} : Finset (Fin 14)), a ∉ ineligSet 14 D)
    (hg : hc_adjB ix x = true ∧ hc_adjB iy y = true ∧ hc_adjB x y = true ∧
      hc_adjB w y = true ∧ hc_adjB ix t = true ∧ ix ≠ iy ∧ x ≠ w ∧ x ≠ t ∧ x ≠ xa ∧
      x ≠ xb ∧ hc_adjB w xa = false ∧ hc_adjB w xb = false ∧ hc_adjB t xa = false ∧
      hc_adjB t xb = false)
    (hsx : 3 ≤ (sem_W 14 D x).card)
    (hsu : 3 ≤ (sem_W 14 D xa).card ∨ 3 ≤ (sem_W 14 D xb).card) : pa_C D pos P Q y := by
  obtain ⟨hpos, hc3, hPQ, hsat⟩ := hc
  obtain ⟨g1, g2, g3, g4, g5, g0, g6, g7, g8, g9, g10, g11, g12, g13⟩ := hg
  rw [hc_adjB_iff] at g1 g2 g3 g4 g5
  rw [sem_adjB_false] at g10 g11 g12 g13
  have hix := hin.1 ix (by simp)
  have hiy := hin.1 iy (by simp)
  have hx := hin.2 x (by simp)
  have hy := hin.2 y (by simp)
  obtain ⟨u, hu, gu1, gu2, gu3⟩ :
      ∃ u, 3 ≤ (sem_W 14 D u).card ∧ x ≠ u ∧ ¬ Adj w u ∧ ¬ Adj t u := by
    rcases hsu with hs | hs
    exacts [⟨xa, hs, g8, g10, g12⟩, ⟨xb, hs, g9, g11, g13⟩]
  obtain ⟨hPx, hQx⟩ := hsat x hsx
  obtain ⟨e, he, hbe, hf, hf'⟩ := pa_ed h hD hpos g3
  obtain ⟨e', he', hbe', -, hf2⟩ := pa_ed h hD hpos g4
  have key : ∀ (c : ℕ × Bool) (s : Fin 14), c ∈ sem_W 14 D x → c ∈ sem_W 14 D s → x ≠ s →
      ¬ Adj s u → c = P ∨ c = Q := by
    intro c s hcx hcs hxs hsu'
    by_contra hne
    rw [not_or] at hne
    refine pa_cf h hD hxs gu1 hsu' (fun a ha => ?_)
    rcases pa_three hPx hQx hcx hPQ (Ne.symm hne.1) (Ne.symm hne.2) (hc3 x) a ha with
      rfl | rfl | rfl
    exacts [Or.inr (hsat u hu).1, Or.inr (hsat u hu).2, Or.inl hcs]
  have hx1 := key (pos ix) t (as_mem hpos hix g1) (as_mem hpos hix g5) g7 gu3
  have hB : (∀ c ∈ sem_W 14 D y, c = sem_bar e ∨ ∃ i ∈ ineligSet 14 D, c = pos i) →
      e = P ∨ e = Q := by
    intro hA
    refine key e w he ?_ g6 gu2
    rcases hA _ hbe' with h1 | ⟨i, hi, h1⟩
    · rw [← sem_bar_bar e, ← h1, sem_bar_bar]; exact he'
    · exact (hin.2 w (by simp) (hf2 i hi h1 ▸ hi)).elim
  by_cases hsy : (sem_W 14 D y).card ≤ 2
  · obtain ⟨Dy, -, hWy, hpy⟩ :=
      ps h hD hpos hiy (fun e : y = iy => hy (e ▸ hiy)) (as_mem hpos hiy g2) hsy
    have hDy : Dy ∈ sem_W 14 D y := by rw [hWy]; simp
    have hb : sem_bar e = Dy := by
      rw [hWy, Finset.mem_insert, Finset.mem_singleton] at hbe
      exact hbe.resolve_left (fun hh => hx (hf' iy hiy hh ▸ hiy))
    refine ⟨e, hB (fun c hc' => ?_), fun i hi hei => hy (hf i hi hei ▸ hi),
      fun s hs => hb ▸ hpy s hs, hb ▸ hDy, ix, hix, hx1⟩
    rw [hWy, Finset.mem_insert, Finset.mem_singleton] at hc'
    rcases hc' with h1 | h1
    exacts [Or.inr ⟨iy, hiy, h1⟩, Or.inl (h1.trans hb.symm)]
  · exfalso
    obtain ⟨hPy, hQy⟩ := hsat y (by omega)
    have hWy := pa_three hPy hQy hbe hPQ (fun hh => w_bar h.1 he (hh ▸ hPx))
      (fun hh => w_bar h.1 he (hh ▸ hQx)) (hc3 y)
    have hy1 : pos iy = P ∨ pos iy = Q := by
      rcases hWy _ (as_mem hpos hiy g2) with h1 | h1 | h1
      exacts [Or.inl h1, Or.inr h1, (hx (hf' iy hiy h1.symm ▸ hiy)).elim]
    have hne : pos ix ≠ pos iy := fun hh => g0 (hpos.2 ix hix iy hiy hh)
    have hass : ∀ X, X = P ∨ X = Q → ∃ i ∈ ineligSet 14 D, X = pos i := by
      intro X hX
      rcases hX with rfl | rfl <;> rcases hx1 with h1 | h1 <;> rcases hy1 with h2 | h2 <;>
        first
          | exact ⟨ix, hix, h1.symm⟩
          | exact ⟨iy, hiy, h2.symm⟩
          | exact (hne (h1.trans h2.symm)).elim
    rcases hB (fun c hc' => (hWy c hc').elim (fun h1 => Or.inr (hass c (Or.inl h1)))
      (fun h1 => h1.elim (fun h2 => Or.inr (hass c (Or.inr h2))) Or.inl)) with rfl | rfl
    exacts [w_bar h.1 hPy hbe, w_bar h.1 hQy hbe]

theorem pa_fin {D : Dag} {pos : Fin 14 → ℕ × Bool} {P Q : ℕ × Bool} {y1 y2 : Fin 14}
    (hne : y1 ≠ y2) (c1 : pa_C D pos P Q y1) (c2 : pa_C D pos P Q y2) : False := by
  obtain ⟨e1, he1, hf1, hp1, -, i, hi, hia⟩ := c1
  obtain ⟨e2, he2, hf2, -, hb2, -⟩ := c2
  have h1 := hf1 i hi
  have h2 := hf2 i hi
  have hee : e2 = e1 := by
    rcases he1 with rfl | rfl <;> rcases he2 with rfl | rfl <;> rcases hia with h3 | h3 <;>
      first
        | rfl
        | exact absurd h3.symm h1
        | exact absurd h3.symm h2
  exact hp1 y2 (Ne.symm hne) (hee ▸ hb2)

theorem elim_p12_mixed {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h13 : totalSurplus 14 D ≤ 13) (hI : ineligSet 14 D = {0, 9}) : False := by
  have hel := inelig_card_add 14 D
  rw [hI, show ({0, 9} : Finset (Fin 14)).card = 2 from rfl] at hel
  obtain ⟨pos, P, Q, hc⟩ := pa_setup h hD h13 (by rw [hI]; decide) (by omega)
  have s1 : 3 ≤ (sem_W 14 D 1).card ∨ 3 ≤ (sem_W 14 D 7).card := by
    by_contra hn
    exact pa_m1 h hD hc.1 1 7 13 9 0 (by rw [hI]; decide) (by decide) (by omega) (by omega)
  have s2 : 3 ≤ (sem_W 14 D 6).card ∨ 3 ≤ (sem_W 14 D 8).card := by
    by_contra hn
    exact pa_m1 h hD hc.1 6 8 11 9 0 (by rw [hI]; decide) (by decide) (by omega) (by omega)
  have c1 : pa_C D pos P Q 7 ∨ pa_C D pos P Q 1 := by
    rcases s1 with hs | hs
    · exact Or.inl (pa_edge h hD hc 1 7 5 3 9 0 6 8 (by rw [hI]; decide) (by decide) hs s2)
    · exact Or.inr (pa_edge h hD hc 7 1 10 13 0 9 6 8 (by rw [hI]; decide) (by decide) hs s2)
  have c2 : pa_C D pos P Q 8 ∨ pa_C D pos P Q 6 := by
    rcases s2 with hs | hs
    · exact Or.inl (pa_edge h hD hc 6 8 5 2 9 0 1 7 (by rw [hI]; decide) (by decide) hs s1)
    · exact Or.inr (pa_edge h hD hc 8 6 10 11 0 9 1 7 (by rw [hI]; decide) (by decide) hs s1)
  rcases c1 with a | a <;> rcases c2 with b | b <;> exact pa_fin (by decide) a b

abbrev pb_O : Finset (Fin 14) := {8, 9, 10, 11, 12, 13}

theorem pb_g {I : Finset (Fin 14)} (hI : I = {0, 1, 3}) :
    (∀ i ∈ I, hc_adjB i 7 = true) ∧ (∀ t, t ∉ I → hc_adjB 7 t = false) ∧
    (∀ l ∈ pb_O, l ∉ I ∧ l ≠ 7 ∧ (∃ i ∈ I, hc_adjB i l = true) ∧
      ∃ z, hc_adjB l z = true ∧ z ∉ I) ∧
    (∀ t, t ∉ I → t ≠ 7 → ∀ i ∈ I, ∃ q, hc_adjB i q = true ∧ q ≠ 7 ∧
      hc_adjB q t = false) ∧ I.card = 3 := by
  subst hI
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

abbrev pb_Y (D : Dag) (pos : Fin 14 → ℕ × Bool) : Finset (ℕ × Bool) :=
  (ineligSet 14 D).image pos

def pb_Cx (D : Dag) (b : Fin 14 → ℕ) (u : Σ _ : ℕ, ℕ) : Prop :=
  ∀ x : Fin 14, x ≠ 7 → (sem_W 14 D x).card ≤ 3 ∧ (3 ≤ (sem_W 14 D x).card →
    merges 14 D (carrierT 14 D {x}) = ∅ ∧ x ∈ supp 14 D u.1 ∧
      ∀ v ∈ residualUnits 14 D b, x ∈ supp 14 D v.1 → v = u)

def pb_Sg (D : Dag) (l : Fin 14) : Prop :=
  ∃ Q : ℕ × Bool, sem_bar Q ∈ sem_W 14 D l ∧ (∀ t, sem_bar Q ∈ sem_W 14 D t → t = l) ∧
    ∀ z, Adj l z → z ∈ eligSet 14 D → Q ∈ sem_W 14 D z

def pb_Db (D : Dag) (pos : Fin 14 → ℕ × Bool) (l : Fin 14) : Prop :=
  ∃ F G, F ∈ sem_W 14 D l ∧ G ∈ sem_W 14 D l ∧ F ≠ G ∧ F ∉ pb_Y D pos ∧
    G ∉ pb_Y D pos

theorem pb_free {D : Dag} {pos : Fin 14 → ℕ × Bool} (hpos : k4_Pos 14 HG D pos) {y : Fin 14}
    (hy : y ∈ eligSet 14 D) {e : ℕ × Bool} (he : sem_bar e ∈ sem_W 14 D y) :
    e ∉ pb_Y D pos := by
  intro hc
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hc
  have := as_priv hpos hi he
  subst this
  exact sem_mem_inelig.1 hi hy

theorem pb_single {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hI : ineligSet 14 D = {0, 1, 3}) {pos : Fin 14 → ℕ × Bool}
    (hpos : k4_Pos 14 HG D pos) {l z0 : Fin 14} (hl7 : l ≠ 7) (hz0 : Adj l z0)
    (hz0e : z0 ∈ eligSet 14 D) (hnd : ¬ pb_Db D pos l) : pb_Sg D l := by
  have hg := pb_g hI
  have hG := sem_heawood_gr
  have hC := sem_heawood_comp hD
  obtain ⟨e, he, hbe, -⟩ := sem_edge_slots hG h.1 hC hz0
  have hall : ∀ f ∈ sem_W 14 D l, f = e ∨ f ∈ pb_Y D pos := by
    intro f hf
    by_contra hc
    rw [not_or] at hc
    exact hnd ⟨e, f, he, hf, fun heq => hc.1 heq.symm, pb_free hpos hz0e hbe, hc.2⟩
  refine ⟨sem_bar e, by rw [sem_bar_bar]; exact he, fun t ht => ?_, fun z hz hze => ?_⟩
  · rw [sem_bar_bar] at ht
    have ht := (sem_mem_W.1 ht).2.1
    by_contra htl
    by_cases hti : t ∈ ineligSet 14 D
    · have hl' := (sem_mem_W.1 he).2.1
      rw [sem_inelig_pure hG h.1 hC hti ht, Finset.mem_singleton] at hl'
      exact htl hl'.symm
    · obtain ⟨f, hf, h7, ht'⟩ := sem_hw_cover_free h hD hl7 (Ne.symm htl)
        (sem_adjB_false.1 (hg.2.1 t hti))
      rcases hall f hf with rfl | hc
      · exact ht' ht
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hc
        exact h7 ((hpos.1 i hi).2.2.1 7 ((hc_adjB_iff _ _).1 (hg.1 i hi)))
  · obtain ⟨f, hf, hbf, -⟩ := sem_edge_slots hG h.1 hC hz
    rcases hall f hf with rfl | hc
    · exact hbf
    · exact absurd hc (pb_free hpos hze hbf)

theorem pb_double {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hI : ineligSet 14 D = {0, 1, 3}) (b : Fin 14 → ℕ) (hb : PureBranch 14 D b)
    {pos : Fin 14 → ℕ × Bool} (hpos : k4_Pos 14 HG D pos) {u2 : Σ _ : ℕ, ℕ}
    (hx : pb_Cx D b u2) {l t i j : Fin 14} (hl7 : l ≠ 7) (ht7 : t ≠ 7) (hlt : l ≠ t)
    (ht3 : t ∉ ineligSet 14 D) (hle : l ∈ eligSet 14 D)
    (hi : i ∈ ineligSet 14 D) (hj : j ∈ ineligSet 14 D) (hil : Adj i l) (hjt : Adj j t)
    (hdl : pb_Db D pos l) (hdt : pb_Db D pos t) : i = j := by
  classical
  have hg := pb_g hI
  have key : ∀ {x k : Fin 14}, x ≠ 7 → k ∈ ineligSet 14 D → Adj k x → pb_Db D pos x →
      3 ≤ (sem_W 14 D x).card ∧ ∃ F G, F ∉ pb_Y D pos ∧ G ∉ pb_Y D pos ∧
        sem_W 14 D x = {pos k, F, G} := by
    intro x k hx7 hk hkx ⟨F, G, hF, hG, hFG, hFa, hGa⟩
    have hk' : pos k ∈ pb_Y D pos := Finset.mem_image_of_mem pos hk
    have hn : pos k ∉ ({F, G} : Finset (ℕ × Bool)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun he => hFa (he ▸ hk'), fun he => hGa (he ▸ hk')⟩
    have hsub : ({pos k, F, G} : Finset (ℕ × Bool)) ⊆ sem_W 14 D x := by
      intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl
      · exact as_mem hpos hk hkx
      · exact hF
      · exact hG
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hn, Finset.card_pair hFG] at h1
    exact ⟨h1, F, G, hFa, hGa, (Finset.eq_of_subset_of_card_le hsub (by
      rw [Finset.card_insert_of_notMem hn, Finset.card_pair hFG]; exact (hx x hx7).1)).symm⟩
  obtain ⟨hl3, F, G, hFa, hGa, hWl⟩ := key hl7 hi hil hdl
  obtain ⟨ht3', F', G', hFa', hGa', hWt⟩ := key ht7 hj hjt hdt
  obtain ⟨-, hlu, hluq⟩ := (hx l hl7).2 hl3
  have htu := ((hx t ht7).2 ht3').2.1
  obtain ⟨e0, he0⟩ := ri_gen sem_heawood_gr h (sem_heawood_comp hD) b hb hlt hle
    (fun u hu hlu' => by rw [hluq u hu hlu']; exact htu) ⟨hlu, htu⟩
  have hi' : pos i ∈ pb_Y D pos := Finset.mem_image_of_mem pos hi
  by_cases hp : pos i = e0
  · exfalso
    have h1 := he0 F (by rw [hWl]; simp) (fun he => hFa (by rw [he, ← hp]; exact hi'))
    have h2 := he0 G (by rw [hWl]; simp) (fun he => hGa (by rw [he, ← hp]; exact hi'))
    obtain ⟨e, he, h7, ht'⟩ :=
      sem_hw_cover_free h hD hl7 hlt (sem_adjB_false.1 (hg.2.1 t ht3))
    rw [hWl] at he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact h7 ((hpos.1 i hi).2.2.1 7 ((hc_adjB_iff _ _).1 (hg.1 i hi)))
    · exact ht' h1
    · exact ht' h2
  · have h2 : pos i ∈ sem_W 14 D t := sem_mem_W.2 ⟨(hpos.1 i hi).1,
      he0 (pos i) (by rw [hWl]; simp) hp, by
        rw [(hpos.1 i hi).2.1]; exact Finset.notMem_empty t⟩
    rw [hWt] at h2
    simp only [Finset.mem_insert, Finset.mem_singleton] at h2
    rcases h2 with h2 | h2 | h2
    · exact hpos.2 i hi j hj h2
    · exact absurd (h2 ▸ hi') hFa'
    · exact absurd (h2 ▸ hi') hGa'

def pb_at (l : List (Fin 14)) (k : Fin 4) : Fin 14 := l.getD k.val 0

abbrev pb_cg (zl ll : List (Fin 14)) : Prop :=
  (∀ k : Fin 4, hc_adjB (pb_at ll k) (pb_at zl k) = true ∧
    hc_adjB (pb_at ll k) (pb_at zl (k + 1)) = true ∧ pb_at zl k ≠ 7 ∧
    pb_at zl k ∉ ({0, 1, 3} : Finset (Fin 14))) ∧
  ∀ k m : Fin 4, k ≠ m → pb_at zl k ≠ pb_at zl m ∧
    hc_adjB (pb_at zl k) (pb_at zl m) = false ∧ pb_at ll k ≠ pb_at ll m

theorem pb_cyc {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hI : ineligSet 14 D = {0, 1, 3}) (b : Fin 14 → ℕ) (hbm : sem_MinBranch 14 D b)
    {u2 : Σ _ : ℕ, ℕ} (hu2 : u2 ∈ residualUnits 14 D b) (hx : pb_Cx D b u2)
    (zl ll : List (Fin 14)) (hcg : pb_cg zl ll) (hsg : ∀ k : Fin 4, pb_Sg D (pb_at ll k)) :
    False := by
  classical
  obtain ⟨hg1, hg2⟩ := hcg
  choose Q hQ1 hQ2 hQ3 using hsg
  have hf : ∀ k : Fin 4, k - 1 ≠ k ∧ k + 1 ≠ k ∧ k + 1 ≠ k - 1 ∧ k - 1 + 1 = k := by decide
  have hel : ∀ k, pb_at zl k ∈ eligSet 14 D :=
    fun k => not_not.1 (fun hc => (hg1 k).2.2.2 (hI ▸ sem_mem_inelig.2 hc))
  have hQa : ∀ k, Q k ∈ sem_W 14 D (pb_at zl k) :=
    fun k => hQ3 k _ ((hc_adjB_iff _ _).1 (hg1 k).1) (hel k)
  have hQb : ∀ k, Q k ∈ sem_W 14 D (pb_at zl (k + 1)) :=
    fun k => hQ3 k _ ((hc_adjB_iff _ _).1 (hg1 k).2.1) (hel _)
  have hd : ∀ k m : Fin 4, k ≠ m → Q k ≠ Q m :=
    fun k m hkm he => (hg2 k m hkm).2.2 (hQ2 m _ (by rw [← he]; exact hQ1 k))
  have hne : ∀ k, pb_at zl k ≠ pb_at zl (k + 1) := fun k => (hg2 _ _ (Ne.symm (hf k).2.1)).1
  have h3 : ∀ k, 3 ≤ (sem_W 14 D (pb_at zl k)).card := by
    intro k
    by_contra hc
    have hQp : Q (k - 1) ∈ sem_W 14 D (pb_at zl k) := by
      have := hQb (k - 1)
      rwa [(hf k).2.2.2] at this
    have heq := Finset.eq_of_subset_of_card_le
      (s := ({Q k, Q (k - 1)} : Finset (ℕ × Bool))) (t := sem_W 14 D (pb_at zl k))
      (fun e he => by
        rcases Finset.mem_insert.1 he with rfl | he
        · exact hQa k
        · rw [Finset.mem_singleton.1 he]; exact hQp)
      (by rw [Finset.card_pair (hd _ _ (Ne.symm (hf k).1))]; omega)
    obtain ⟨e, he, ha, hb'⟩ := sem_hw_cover_free h hD (hne k)
      (hg2 k (k - 1) (Ne.symm (hf k).1)).1 (sem_adjB_false.1 (hg2 _ _ (hf k).2.2.1).2.1)
    rw [← heq] at he
    rcases Finset.mem_insert.1 he with rfl | he
    · exact ha (sem_mem_W.1 (hQb k)).2.1
    · rw [Finset.mem_singleton.1 he] at hb'
      exact hb' (sem_mem_W.1 (hQa (k - 1))).2.1
  obtain ⟨P, R, hPR, hcom⟩ := gct_gen sem_heawood_gr h (sem_heawood_comp hD) b hbm hu2
    (Finset.univ.image (pb_at zl)) ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ 0)⟩
    (fun x hx' => by
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hx'
      exact (hx _ (hg1 k).2.2.1).2 (h3 k))
  have hcm : ∀ k, P ∈ sem_W 14 D (pb_at zl k) ∧ R ∈ sem_W 14 D (pb_at zl k) :=
    fun k => hcom _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))
  have hin : ∀ k, Q k = P ∨ Q k = R := by
    intro k
    by_contra hc
    rw [not_or] at hc
    have hn : P ∉ ({R, Q k} : Finset (ℕ × Bool)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun he => hPR (he ▸ rfl), Ne.symm hc.1⟩
    have key : ∀ m, Q k ∈ sem_W 14 D (pb_at zl m) →
        ({P, R, Q k} : Finset (ℕ × Bool)) = sem_W 14 D (pb_at zl m) := fun m hm =>
      Finset.eq_of_subset_of_card_le (fun e he => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl | rfl
        · exact (hcm m).1
        · exact (hcm m).2
        · exact hm) (by
        rw [Finset.card_insert_of_notMem hn, Finset.card_pair (Ne.symm hc.2)]
        exact (hx _ (hg1 m).2.2.1).1)
    obtain ⟨e, he, ha, -⟩ := sem_hw_cover_free h hD (hne k) (hne k) (adj_irrefl _)
    rw [← key k (hQa k), key (k + 1) (hQb k)] at he
    exact ha (sem_mem_W.1 he).2.1
  rcases hin 0 with a | a <;> rcases hin 1 with c | c <;> rcases hin 2 with d | d <;>
    first
    | exact hd 0 1 (by decide) (a.trans c.symm)
    | exact hd 0 2 (by decide) (a.trans d.symm)
    | exact hd 1 2 (by decide) (c.trans d.symm)

theorem elim_p11_conc {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h13 : totalSurplus 14 D ≤ 13) (hI : ineligSet 14 D = {0, 1, 3}) : False := by
  classical
  have hG := sem_heawood_gr
  have hC := sem_heawood_comp hD
  obtain ⟨b, hbm⟩ := sem_exists_minBranch hG h.1 hC
  have hb := sem_minBranch_pure hbm
  obtain ⟨pos, hpos0⟩ := k4_assigned hG h hC
  have hpos : k4_Pos 14 HG D pos := hpos0
  obtain ⟨g1, -, g3, g4, g5⟩ := pb_g hI
  have hel : ∀ x : Fin 14, x ∉ ineligSet 14 D → x ∈ eligSet 14 D :=
    fun x hx => not_not.1 (mt sem_mem_inelig.2 hx)
  have h7e : (7 : Fin 14) ∈ eligSet 14 D := hel 7 (by rw [hI]; decide)
  have hY : ∀ i ∈ ineligSet 14 D, pos i ∈ sem_W 14 D 7 :=
    fun i hi => as_mem hpos hi ((hc_adjB_iff _ _).1 (g1 i hi))
  have hsub7 : pb_Y D pos ⊆ sem_W 14 D 7 := fun e he => by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 he
    exact hY i hi
  have hc7 : (pb_Y D pos).card = 3 :=
    (Finset.card_image_of_injOn (fun _ hi _ hj => hpos.2 _ hi _ hj)).trans g5
  have hW7 := Finset.card_le_card hsub7
  rw [hc7] at hW7
  have hcc7 := cc_el h hD b hb h7e
  have hres := card_residual h.1 b hb
  have hp := inelig_card_add 14 D
  rw [g5] at hp
  have hBt := Bplus_le_total 14 D
  by_cases hall : ∀ u ∈ residualUnits 14 D b, (7 : Fin 14) ∈ supp 14 D u.1
  · have := cf_six h hD b hb cf7_good h7e pb_O (fun x hx => by
      obtain ⟨hx3, hx7, ⟨i, hi, hix⟩, -⟩ := g3 x hx
      exact ⟨hel x hx3, hx7, fun u hu _ => hall u hu, src D (pos i),
        (hpos.1 i hi).2.2.1 x ((hc_adjB_iff _ _).1 hix),
        (hpos.1 i hi).2.2.1 7 ((hc_adjB_iff _ _).1 (g1 i hi))⟩)
    rw [show pb_O.card = 6 from rfl] at this
    omega
  · obtain ⟨u2, hu⟩ := not_forall.1 hall
    obtain ⟨hu2, hu27⟩ := Classical.not_imp.1 hu
    have hsub2 : ru D b 7 ⊆ (residualUnits 14 D b).erase u2 := fun u hu =>
      Finset.mem_erase.2 ⟨fun he => hu27 (he ▸ (mem_ru.1 hu).2), (mem_ru.1 hu).1⟩
    have hle := Finset.card_le_card hsub2
    rw [Finset.card_erase_of_mem hu2] at hle
    obtain ⟨u1, hu1⟩ := Finset.card_eq_one.1 (show (ru D b 7).card = 1 by omega)
    have hu1r : u1 ∈ ru D b 7 := by rw [hu1]; exact Finset.mem_singleton_self _
    obtain ⟨hu1m, hu17⟩ := mem_ru.1 hu1r
    have hres2 : ∀ u ∈ residualUnits 14 D b, u ≠ u2 → u = u1 := fun u hu hne =>
      Finset.card_le_one.1 (by rw [Finset.card_erase_of_mem hu2]; omega) u
        (Finset.mem_erase.2 ⟨hne, hu⟩) u1 (hsub2 hu1r)
    have hW7eq : pb_Y D pos = sem_W 14 D 7 :=
      Finset.eq_of_subset_of_card_le hsub7 (by rw [hc7]; omega)
    have hpure : ∀ t, t ∈ supp 14 D u1.1 → t = 7 := by
      intro t ht
      by_contra ht7
      obtain ⟨e0, he0⟩ := ri_gen hG h hC b hb (Ne.symm ht7) h7e (fun u hu hu7 => by
        rw [hres2 u hu (fun he => hu27 (he ▸ hu7))]; exact ht) ⟨hu17, ht⟩
      have hex : ∃ i3 ∈ ineligSet 14 D, ∀ i ∈ ineligSet 14 D, i ≠ i3 →
          t ∈ supp 14 D (src D (pos i)) := by
        by_cases hc : ∃ i3 ∈ ineligSet 14 D, pos i3 = e0
        · obtain ⟨i3, hi3, he⟩ := hc
          exact ⟨i3, hi3, fun i hi hne => he0 _ (hY i hi) (fun hh =>
            hne (hpos.2 i hi i3 hi3 (hh.trans he.symm)))⟩
        · exact ⟨0, by rw [hI]; decide,
            fun i hi _ => he0 _ (hY i hi) (fun hh => hc ⟨i, hi, hh⟩)⟩
      obtain ⟨i3, hi3, hoth⟩ := hex
      obtain ⟨q, hq1, hq7, hq2⟩ :=
        g4 t (fun hc => sem_mem_inelig.1 hc (res_elig hu1m ht)) ht7 i3 hi3
      obtain ⟨e, he, h1, h2⟩ := sem_hw_cover_free h hD (Ne.symm ht7) (Ne.symm hq7)
        (fun hadj => sem_adjB_false.1 hq2 (adj_symm hadj))
      rw [← hW7eq] at he
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 he
      by_cases hii : i = i3
      · subst hii
        exact h2 ((hpos.1 i hi).2.2.1 q ((hc_adjB_iff _ _).1 hq1))
      · exact h1 (hoth i hi hii)
    have huq : ∀ x : Fin 14, x ≠ 7 → ∀ u ∈ ru D b x, u = u2 := by
      intro x hx u hu
      by_contra hne
      obtain ⟨hur, hxu⟩ := mem_ru.1 hu
      rw [hres2 u hur hne] at hxu
      exact hx (hpure x hxu)
    have hcx : pb_Cx D b u2 := by
      intro x hx
      have h1 := cc_le h hD b hb x
      have h2 : (ru D b x).card ≤ 1 := Finset.card_le_one.2
        (fun u hu v hv => (huq x hx u hu).trans (huq x hx v hv).symm)
      refine ⟨by omega, fun h3 => ?_⟩
      obtain ⟨u, hu⟩ := Finset.card_pos.1 (show 0 < (ru D b x).card by omega)
      exact ⟨Finset.card_eq_zero.1 (by omega), huq x hx u hu ▸ (mem_ru.1 hu).2,
        fun v hv hxv => huq x hx v (mem_ru.2 ⟨hv, hxv⟩)⟩
    have hO : ∀ l ∈ pb_O, ¬ pb_Db D pos l → pb_Sg D l := fun l hl hnd => by
      obtain ⟨-, hl7, -, z, hz, hz3⟩ := g3 l hl
      exact pb_single h hD hI hpos hl7 ((hc_adjB_iff _ _).1 hz) (hel z hz3) hnd
    have hi0 : ∃ i0 ∈ ineligSet 14 D, ∀ l ∈ pb_O, hc_adjB i0 l = false → pb_Sg D l := by
      by_cases hd : ∃ l0 ∈ pb_O, pb_Db D pos l0
      · obtain ⟨l0, hl0, hd0⟩ := hd
        obtain ⟨hl3, hl7, ⟨i0, hi0, hi0l⟩, -⟩ := g3 l0 hl0
        refine ⟨i0, hi0, fun l hl hnl => hO l hl (fun hdl => ?_)⟩
        obtain ⟨ht3, ht7, ⟨j, hj, hjl⟩, -⟩ := g3 l hl
        have hne : l0 ≠ l := fun he => by
          rw [he, hnl] at hi0l
          exact Bool.false_ne_true hi0l
        rw [pb_double h hD hI b hb hpos hcx hl7 ht7 hne ht3 (hel l0 hl3) hi0 hj
          ((hc_adjB_iff _ _).1 hi0l) ((hc_adjB_iff _ _).1 hjl) hd0 hdl, hjl] at hnl
        exact Bool.noConfusion hnl
      · exact ⟨0, by rw [hI]; decide,
          fun l hl _ => hO l hl (fun hdl => hd ⟨l, hl, hdl⟩)⟩
    obtain ⟨i0, hi0, hsg⟩ := hi0
    have fin : ∀ zl ll : List (Fin 14), pb_cg zl ll →
        (∀ k : Fin 4, pb_at ll k ∈ pb_O ∧ hc_adjB i0 (pb_at ll k) = false) → False :=
      fun zl ll hcg hk =>
        pb_cyc h hD hI b hbm hu2 hcx zl ll hcg (fun k => hsg _ (hk k).1 (hk k).2)
    rw [hI] at hi0
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi0
    rcases hi0 with rfl | rfl | rfl
    · exact fin [5, 6, 4, 2] [9, 11, 13, 12] (by decide +kernel) (by decide +kernel)
    · exact fin [2, 6, 4, 5] [8, 11, 10, 12] (by decide +kernel) (by decide +kernel)
    · exact fin [2, 6, 5, 4] [8, 9, 10, 13] (by decide +kernel) (by decide +kernel)

theorem pc_three {α : Type} [DecidableEq α] {S : Finset α} {a b c : α} (ha : a ∈ S)
    (hb : b ∈ S) (hc : c ∈ S) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    3 ≤ S.card ∧ (S.card ≤ 3 → ∀ e ∈ S, e = a ∨ e = b ∨ e = c) := by
  have hsub : ({a, b, c} : Finset α) ⊆ S := by
    simp [Finset.insert_subset_iff, ha, hb, hc]
  have h3 : ({a, b, c} : Finset α).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc]
  refine ⟨h3 ▸ Finset.card_le_card hsub, fun h2 e he => ?_⟩
  rw [← Finset.eq_of_subset_of_card_le hsub (h3 ▸ h2)] at he
  simpa using he

theorem pc_q : ∀ j ∈ ({0, 1} : Finset (Fin 14)), ∀ t : Fin 14, t ≠ j →
    ∃ q, hc_adjB j q = true ∧ q ≠ 7 ∧ hc_adjB t q = false := by decide +kernel

theorem pc_g07 : ∀ t : Fin 14, Adj 0 t → Adj 1 t → t = 7 := by decide +kernel

theorem pc_g17 : ∀ l : Fin 14, Adj 1 l → ¬ Adj 7 l := by decide +kernel

theorem pc_geo (d la lb : Fin 14)
    (hc : (d = 4 ∧ la = 10 ∧ lb = 13) ∨ (d = 6 ∧ la = 8 ∧ lb = 9)) :
    (d ∉ ({0, 1, 11} : Finset (Fin 14)) ∧ la ∉ ({0, 1, 11} : Finset (Fin 14)) ∧
      lb ∉ ({0, 1, 11} : Finset (Fin 14))) ∧
    (Adj 11 d ∧ Adj d la ∧ Adj d lb ∧ Adj 0 la ∧ Adj 1 lb) ∧
    (la ≠ 7 ∧ lb ≠ 7 ∧ d ≠ 7 ∧ la ≠ d ∧ lb ≠ d) ∧ ¬ Adj 0 d ∧ ¬ Adj 1 d := by
  rcases hc with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    exact ⟨by decide, ⟨by decide, by decide, by decide, by decide, by decide⟩, by decide,
      by decide, by decide⟩

theorem elim_p11_mixed {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h13 : totalSurplus 14 D ≤ 13) (hI : ineligSet 14 D = {0, 1, 11}) : False := by
  classical
  have hG := sem_heawood_gr
  have hC := sem_heawood_comp hD
  obtain ⟨b, hbm⟩ := sem_exists_minBranch hG h.1 hC
  have hb := sem_minBranch_pure hbm
  obtain ⟨pos, hpos⟩ := k4_assigned hG h hC
  have hin : ∀ i ∈ ({0, 1, 11} : Finset (Fin 14)), i ∈ ineligSet 14 D := by
    rw [hI]; exact fun _ hi => hi
  have h0 := hin 0 (by decide)
  have h1 := hin 1 (by decide)
  have h11 := hin 11 (by decide)
  have hel : ∀ x : Fin 14, x ∉ ({0, 1, 11} : Finset (Fin 14)) → x ∈ eligSet 14 D := by
    intro x hx
    by_contra hc
    exact hx (hI ▸ sem_mem_inelig.2 hc)
  have hne : ∀ x ∈ eligSet 14 D, ∀ i ∈ ineligSet 14 D, x ≠ i :=
    fun x hx i hi hxi => sem_mem_inelig.1 hi (hxi ▸ hx)
  have edge : ∀ x y : Fin 14, Adj x y → x ∈ eligSet 14 D → y ∈ eligSet 14 D →
      ∃ e ∈ sem_W 14 D x, sem_bar e ∈ sem_W 14 D y ∧
        (∀ i ∈ ineligSet 14 D, e ≠ pos i ∧ sem_bar e ≠ pos i) ∧
        x ∉ supp 14 D (src D (sem_bar e)) := by
    intro x y hxy hx hy
    obtain ⟨e, he, heb, -, hs, -⟩ := sem_edge_slots hG h.1 hC hxy
    exact ⟨e, he, heb, fun i hi => ⟨fun hc => hne y hy i hi (as_priv hpos hi (hc ▸ heb)),
      fun hc => hne x hx i hi (as_priv hpos hi (by rw [← hc, sem_bar_bar]; exact he))⟩, hs⟩
  have k0 := (hpos.1 0 h0).2.2.1
  have k1 := (hpos.1 1 h1).2.2.1
  have e7 := hel 7 (by decide)
  have e3 := hel 3 (by decide)
  obtain ⟨H, hH7, hH3, hHf, -⟩ := edge 7 3 (by decide) e7 e3
  have a07 := as_mem hpos h0 (a := 7) (by decide)
  have a17 := as_mem hpos h1 (a := 7) (by decide)
  have p01 : pos 0 ≠ pos 1 := fun hc => absurd (hpos.2 0 h0 1 h1 hc) (by decide)
  obtain ⟨t71, t72⟩ := pc_three a07 a17 hH7 p01 (hHf 0 h0).1.symm (hHf 1 h1).1.symm
  have c7 := cc_el h hD b hb e7
  have hr := card_residual h.1 b hb
  have hp := inelig_card_add 14 D
  rw [hI, show ({0, 1, 11} : Finset (Fin 14)).card = 3 from rfl] at hp
  have hsplit := totalSurplus_split 14 D
  have hr7 : (ru D b 7).card ≤ (residualUnits 14 D b).card := Finset.card_filter_le _ _
  have lw : ∀ (u : Σ _ : ℕ, ℕ) (x : Fin 14),
      (∀ v ∈ residualUnits 14 D b, x ∈ supp 14 D v.1 → v = u) →
      (sem_W 14 D x).card + (merges 14 D (carrierT 14 D {x})).card ≤ 3 ∧
        (x ∉ supp 14 D u.1 → (sem_W 14 D x).card ≤ 2) := by
    intro u x hu
    have q1 := cc_le h hD b hb x
    have q2 : (ru D b x).card ≤ 1 := Finset.card_le_one.2 (fun a ha c hc =>
      (hu a (mem_ru.1 ha).1 (mem_ru.1 ha).2).trans (hu c (mem_ru.1 hc).1 (mem_ru.1 hc).2).symm)
    refine ⟨by omega, fun hn => ?_⟩
    have : (ru D b x).card = 0 := Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2
      (fun v hv hxv => hn (hu v hv hxv ▸ hxv)))
    omega
  have nB : (ru D b 7).card ≠ 2 := by
    intro hk
    have hall : ∀ u ∈ residualUnits 14 D b, 7 ∈ supp 14 D u.1 := by
      have hE : ru D b 7 = residualUnits 14 D b :=
        Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
      intro u hu
      rw [← hE] at hu
      exact (mem_ru.1 hu).2
    have hy : ∃ y : Fin 14, (y = 3 ∨ y = 12) ∧
        ∃ w, y ∈ supp 14 D w ∧ 7 ∈ supp 14 D w := by
      by_cases h3 : ∃ u ∈ residualUnits 14 D b, 3 ∈ supp 14 D u.1
      · obtain ⟨u, hu, h3u⟩ := h3
        exact ⟨3, Or.inl rfl, u.1, h3u, hall u hu⟩
      · have hr3 : (ru D b 3).card = 0 := Finset.card_eq_zero.2
          (Finset.filter_eq_empty_iff.2 (fun u hu h3u => h3 ⟨u, hu, h3u⟩))
        have := cc_le h hD b hb 3
        obtain ⟨Z, -, hZ, -⟩ := ps h hD hpos h11 (by decide)
          (as_mem hpos h11 (a := 3) (by decide)) (by omega)
        obtain ⟨g, hg, hgb, hgf, -⟩ := edge 3 12 (by decide) e3 (hel 12 (by decide))
        rw [hZ, Finset.mem_insert, Finset.mem_singleton] at hg hH3
        rw [hg.resolve_left (hgf 11 h11).1, ← hH3.resolve_left (hHf 11 h11).2,
          sem_bar_bar] at hgb
        exact ⟨12, Or.inr rfl, _, (sem_mem_W.1 hgb).2.1, (sem_mem_W.1 hH7).2.1⟩
    obtain ⟨y, hy1, w, hyw, h7w⟩ := hy
    have hX : ∀ x ∈ ({8, 10, 9, 13, y} : Finset (Fin 14)), x ∈ eligSet 14 D ∧ x ≠ 7 ∧
        (∀ u ∈ residualUnits 14 D b, x ∈ supp 14 D u.1 → 7 ∈ supp 14 D u.1) ∧
        ∃ w, x ∈ supp 14 D w ∧ 7 ∈ supp 14 D w := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      iterate 2 exact ⟨hel _ (by decide), by decide, fun u hu _ => hall u hu, _,
        k0 _ (by decide), k0 7 (by decide)⟩
      iterate 2 exact ⟨hel _ (by decide), by decide, fun u hu _ => hall u hu, _,
        k1 _ (by decide), k1 7 (by decide)⟩
      rcases hy1 with rfl | rfl <;>
        exact ⟨hel _ (by decide), by decide, fun u hu _ => hall u hu, w, hyw, h7w⟩
    have hc5 : ({8, 10, 9, 13, y} : Finset (Fin 14)).card = 5 := by
      rcases hy1 with rfl | rfl <;> rfl
    have := cf_six h hD b hb cf7_good e7 _ hX
    rw [hc5] at this
    omega
  obtain ⟨u1, hu1⟩ := Finset.card_pos.1 (show 0 < (ru D b 7).card by omega)
  obtain ⟨hu1r, h7u1⟩ := mem_ru.1 hu1
  have huniq : ∀ v ∈ residualUnits 14 D b, 7 ∈ supp 14 D v.1 → v = u1 := fun v hv h7v =>
    Finset.card_le_one.1 (show (ru D b 7).card ≤ 1 by omega) v (mem_ru.2 ⟨hv, h7v⟩) u1 hu1
  have hW7 := t72 (by omega)
  have hW7' := fun e he => or_left_comm.1 (hW7 e he)
  have colab : ∀ t, t ∈ supp 14 D u1.1 → t ≠ 7 →
      t ∈ supp 14 D (src D (pos 0)) ∧ t ∈ supp 14 D (src D (pos 1)) := by
    intro t ht ht7
    have hte := res_elig hu1r ht
    obtain ⟨e0, he0⟩ := ri_gen hG h hC b hb (Ne.symm ht7) e7
      (fun v hv h7v => by rw [huniq v hv h7v]; exact ht) ⟨h7u1, ht⟩
    have mk : ∀ i j : Fin 14, j ∈ ineligSet 14 D → j ∈ ({0, 1} : Finset (Fin 14)) →
        (∀ e ∈ sem_W 14 D 7, e = pos i ∨ e = pos j ∨ e = H) →
        t ∈ supp 14 D (src D (pos i)) → t ∈ supp 14 D (src D H) → False := by
      intro i j hj hj01 hW hti htH
      obtain ⟨q, hq1, hq7, hq2⟩ := pc_q j hj01 t (hne t hte j hj)
      obtain ⟨e, he, n1, n2⟩ := sem_hw_cover_free h hD (x := 7) (Ne.symm ht7)
        (Ne.symm hq7) (sem_adjB_false.1 hq2)
      rcases hW e he with rfl | rfl | rfl
      · exact n1 hti
      · exact n2 ((hpos.1 j hj).2.2.1 q ((hc_adjB_iff _ _).1 hq1))
      · exact n1 htH
    by_cases c0 : pos 0 = e0
    · exact (mk 1 0 h0 (by decide) hW7'
        (he0 _ a17 (fun hc => p01 (c0.trans hc.symm)))
        (he0 _ hH7 (fun hc => (hHf 0 h0).1 (hc.trans c0.symm)))).elim
    · have a0 := he0 _ a07 c0
      by_cases c1 : pos 1 = e0
      · exact (mk 0 1 h1 (by decide) hW7 a0
          (he0 _ hH7 (fun hc => (hHf 1 h1).1 (hc.trans c1.symm)))).elim
      · exact ⟨a0, he0 _ a17 c1⟩
  have nR : (residualUnits 14 D b).card ≠ 1 := by
    intro hR
    have L := fun x => lw u1 x (fun v hv _ => Finset.card_le_one.1 hR.le v hv u1 hu1r)
    have asg : ∀ i ∈ ineligSet 14 D, ∀ t, t ∈ supp 14 D (src D (pos i)) →
        pos i ∈ sem_W 14 D t := fun i hi t ht => sem_mem_W.2 ⟨(hpos.1 i hi).1, ht, by
          rw [(hpos.1 i hi).2.1]; exact Finset.notMem_empty t⟩
    have e4 := hel 4 (by decide)
    have a4 := as_mem hpos h11 (a := 4) (by decide)
    have a10 := as_mem hpos h0 (a := 10) (by decide)
    obtain ⟨e1, he1, hb1, hf1, -⟩ := edge 4 10 (by decide) e4 (hel 10 (by decide))
    obtain ⟨e2, he2, hb2, hf2, -⟩ := edge 4 13 (by decide) e4 (hel 13 (by decide))
    have n4 : 4 ∉ supp 14 D u1.1 := by
      intro h4
      obtain ⟨q0, q1⟩ := colab 4 h4 (by decide)
      rcases (pc_three (asg 0 h0 4 q0) (asg 1 h1 4 q1) he1 p01 (hf1 0 h0).1.symm
        (hf1 1 h1).1.symm).2 (by have := (L 4).1; omega) _ a4 with hc | hc | hc
      · exact absurd (hpos.2 11 h11 0 h0 hc) (by decide)
      · exact absurd (hpos.2 11 h11 1 h1 hc) (by decide)
      · exact (hf1 11 h11).1 hc.symm
    have h12 : e1 = e2 := by
      by_contra hc
      have := (pc_three a4 he1 he2 (hf1 11 h11).1.symm (hf2 11 h11).1.symm hc).1
      have := (L 4).2 n4
      omega
    rw [← h12] at hb2
    obtain ⟨e, he, n7, n13⟩ := sem_hw_cover_free h hD (x := 10) (a := 7) (b := 13)
      (by decide) (by decide) (by decide)
    have d1 : sem_bar e1 ≠ e := fun hc => n13 (hc ▸ (sem_mem_W.1 hb2).2.1)
    have d2 : pos 0 ≠ e := fun hc => n7 (hc ▸ k0 7 (by decide))
    by_cases h10 : 10 ∈ supp 14 D u1.1
    · rcases (pc_three hb1 a10 (asg 1 h1 10 (colab 10 h10 (by decide)).2) (hf1 0 h0).2
        (hf1 1 h1).2 p01).2 (by have := (L 10).1; omega) e he with hc | hc | hc
      · exact d1 hc.symm
      · exact d2 hc.symm
      · exact n7 (hc ▸ k1 7 (by decide))
    · have := (pc_three hb1 a10 he (hf1 0 h0).2 d1 d2).1
      have := (L 10).2 h10
      omega
  have hB0 : Bzero 14 D = 0 := by omega
  have fl : ∀ i j : Fin 14, i ∈ ineligSet 14 D → j ∈ ineligSet 14 D → i ≠ j → i ≠ 3 →
      Adj i 7 → (∀ e ∈ sem_W 14 D 7, e = pos i ∨ e = pos j ∨ e = H) →
      ∀ t, t ∈ supp 14 D (src D (pos i)) → Adj i t := by
    intro i j hi hj hij hi3 hi7 hW t
    refine (full h hD hB0 hpos hi hi7 (fun p hp hp1 hsub => ?_) t).1
    rcases hW p hp with rfl | rfl | rfl
    · exact hp1 rfl
    · exact hij (Finset.singleton_subset_singleton.1
        ((hpos.1 j hj).2.2.2.symm.subset.trans hsub)).symm
    · exact hi3 (Finset.mem_singleton.1 (hsub (sem_mem_W.1 hH3).2.1)).symm
  have f0 := fl 0 1 h0 h1 (by decide) (by decide) (by decide) hW7
  have f1 := fl 1 0 h1 h0 (by decide) (by decide) (by decide) hW7'
  have hpure : ∀ t, t ∈ supp 14 D u1.1 → t = 7 := by
    intro t ht
    by_contra ht7
    obtain ⟨q0, q1⟩ := colab t ht ht7
    exact ht7 (pc_g07 t (f0 t q0) (f1 t q1))
  have hc2 : ((residualUnits 14 D b).erase u1).card = 1 := by
    rw [Finset.card_erase_of_mem hu1r]; omega
  obtain ⟨u2, hu2⟩ := Finset.card_pos.1 (hc2 ▸ Nat.one_pos)
  have hu2r := Finset.mem_of_mem_erase hu2
  have only2 : ∀ x : Fin 14, x ≠ 7 → ∀ u ∈ residualUnits 14 D b, x ∈ supp 14 D u.1 →
      u = u2 := fun x hx u hu hxu => Finset.card_le_one.1 hc2.le u
    (Finset.mem_erase.2 ⟨fun hc => hx (hpure x (hc ▸ hxu)), hu⟩) u2 hu2
  have L := fun x hx => lw u2 x (only2 x hx)
  have ct : ∀ x y : Fin 14, x ≠ 7 → x ≠ y → x ∈ supp 14 D u2.1 → y ∈ supp 14 D u2.1 →
      ∃ e0, ∀ e ∈ sem_W 14 D x, e ≠ e0 → y ∈ supp 14 D (src D e) :=
    fun x y hx hxy hxu hyu => ri_gen hG h hC b hb hxy (res_elig hu2r hxu)
      (fun u hu hxu' => by rw [only2 x hx u hu hxu']; exact hyu) ⟨hxu, hyu⟩
  have low : ∀ i l : Fin 14, i ∈ ineligSet 14 D → Adj i l → l ≠ 7 → l ∉ supp 14 D u2.1 →
      ∀ P ∈ sem_W 14 D l, P ≠ pos i → ∀ t, t ≠ l → P ∉ sem_W 14 D t := by
    intro i l hi hil hl7 hn P hP hPi
    obtain ⟨Z, -, hZ, hZp⟩ := ps h hD hpos hi
      (fun hx => adj_irrefl i (by rw [hx] at hil; exact hil)) (as_mem hpos hi hil)
      ((L l hl7).2 hn)
    rw [hZ, Finset.mem_insert, Finset.mem_singleton] at hP
    rw [hP.resolve_left hPi]
    exact hZp
  have Q : ∀ l1 l2 : Fin 14, Adj 0 l1 → Adj 1 l2 → l1 ≠ 7 → l2 ≠ 7 → ∀ P : ℕ × Bool,
      P ∈ sem_W 14 D l1 → P ∈ sem_W 14 D l2 → P ≠ pos 0 → P ≠ pos 1 → False := by
    intro l1 l2 a1 a2 n1 n2 P hP1 hP2 hP0 hP1'
    have hl : l1 ≠ l2 := fun hc => n1 (pc_g07 l1 a1 (hc ▸ a2))
    obtain ⟨e0, he0⟩ := ct l1 l2 n1 hl
      (by by_contra hn; exact low 0 l1 h0 a1 n1 hn P hP1 hP0 l2 (Ne.symm hl) hP2)
      (by by_contra hn; exact low 1 l2 h1 a2 n2 hn P hP2 hP1' l1 hl hP1)
    have h00 : pos 0 = e0 := by
      by_contra hc
      exact n2 (pc_g07 l2 (f0 l2 (he0 _ (as_mem hpos h0 a1) hc)) a2)
    obtain ⟨e, he, n7, nl⟩ := sem_hw_cover_free h hD (x := l1) (a := 7) (b := l2) n1 hl
      (pc_g17 l2 a2)
    by_cases hc : e = e0
    · exact n7 (by rw [hc, ← h00]; exact k0 7 (by decide))
    · exact nl (he0 e he hc)
  have claim : ∀ d la lb : Fin 14, (d = 4 ∧ la = 10 ∧ lb = 13) ∨ (d = 6 ∧ la = 8 ∧ lb = 9) →
      ∃ e1 e2, (∀ e ∈ sem_W 14 D d, e = pos 11 ∨ e = e1 ∨ e = e2) ∧ e1 ∈ sem_W 14 D d ∧
        e2 ∈ sem_W 14 D d ∧ e1 ≠ pos 11 ∧ e2 ≠ pos 11 ∧ e1 ≠ e2 ∧
        sem_bar e1 ∈ sem_W 14 D la ∧ sem_bar e2 ∈ sem_W 14 D lb ∧
        (∀ t, t ≠ la → sem_bar e1 ∉ sem_W 14 D t) ∧
        (∀ t, t ≠ lb → sem_bar e2 ∉ sem_W 14 D t) ∧
        d ∈ supp 14 D u2.1 ∧ merges 14 D (carrierT 14 D {d}) = ∅ := by
    intro d la lb hcase
    obtain ⟨⟨g1, g2, g3⟩, ⟨g4, g5, g6, g7, g8⟩, ⟨n1, n2, n3, n4, n5⟩, g9, g10⟩ :=
      pc_geo d la lb hcase
    obtain ⟨e1, he1, hb1, hf1, hs1⟩ := edge d la g5 (hel d g1) (hel la g2)
    obtain ⟨e2, he2, hb2, hf2, hs2⟩ := edge d lb g6 (hel d g1) (hel lb g3)
    have h12 : e1 ≠ e2 := fun hc =>
      Q la lb g7 g8 n1 n2 (sem_bar e1) hb1 (hc ▸ hb2) (hf1 0 h0).2 (hf1 1 h1).2
    obtain ⟨t31, t32⟩ := pc_three (as_mem hpos h11 g4) he1 he2 (hf1 11 h11).1.symm
      (hf2 11 h11).1.symm h12
    have q1 := (L d n3).1
    have hdu : d ∈ supp 14 D u2.1 := by
      by_contra hn
      have := (L d n3).2 hn
      omega
    have side : ∀ (i l : Fin 14) (e : ℕ × Bool), i ∈ ineligSet 14 D → Adj i l → l ≠ 7 →
        l ≠ d → sem_bar e ∈ sem_W 14 D l → sem_bar e ≠ pos i →
        d ∉ supp 14 D (src D (sem_bar e)) →
        (∀ t, t ∈ supp 14 D (src D (pos i)) → Adj i t) → ¬ Adj i d →
        ∀ t, t ≠ l → sem_bar e ∉ sem_W 14 D t := by
      intro i l e hi hil hl7 hld hb' hf hs fi hid
      refine low i l hi hil hl7 (fun hl => ?_) _ hb' hf
      obtain ⟨e0, he0⟩ := ct l d hl7 hld hl hdu
      have hx : sem_bar e = e0 := by
        by_contra hc
        exact hs (he0 _ hb' hc)
      exact hid (fi d (he0 _ (as_mem hpos hi hil) (fun hc => hf (hx.trans hc.symm))))
    exact ⟨e1, e2, t32 (by omega), he1, he2, (hf1 11 h11).1, (hf2 11 h11).1, h12, hb1,
      hb2, side 0 la e1 h0 g7 n1 n4 hb1 (hf1 0 h0).2 hs1 f0 g9,
      side 1 lb e2 h1 g8 n2 n5 hb2 (hf2 1 h1).2 hs2 f1 g10, hdu,
      Finset.card_eq_zero.1 (by omega)⟩
  obtain ⟨e1, e2, -, he1, he2, m1, m2, h12, hb1, hb2, -, -, hu4, -⟩ :=
    claim 4 10 13 (Or.inl ⟨rfl, rfl, rfl⟩)
  obtain ⟨g1, g2, hW6, -, -, -, -, -, -, -, hp1, hp2, hu6, hM6⟩ :=
    claim 6 8 9 (Or.inr ⟨rfl, rfl, rfl⟩)
  obtain ⟨e0, he0⟩ := ct 4 6 (by decide) (by decide) hu4 hu6
  have fin : ∀ (e : ℕ × Bool) (l : Fin 14), e ∈ sem_W 14 D 4 → sem_bar e ∈ sem_W 14 D l →
      l ≠ 8 → l ≠ 9 → e ≠ pos 11 → e ≠ e0 → False := by
    intro e l he hbar h8 h9 hne11 hne0
    rcases hW6 e (zm_mem h.1 hM6 (sem_mem_W.1 he).1 (sem_W_and h.1 he) (he0 e he hne0))
      with rfl | rfl | rfl
    · exact hne11 rfl
    · exact hp1 l h8 hbar
    · exact hp2 l h9 hbar
  by_cases c : e1 = e0
  · exact fin e2 13 he2 hb2 (by decide) (by decide) m2 (fun hc => h12 (c.trans hc.symm))
  · exact fin e1 10 he1 hb1 (by decide) (by decide) m1 c

theorem pd_ok1 : tOK {7, 8, 13} {0, 1, 2} = true := by decide +kernel

theorem pd_q : ∀ i t x : Fin 14, hc_adjB i t = true → x ≠ t → x ≠ i →
    ∃ q, hc_adjB i q = true ∧ q ≠ t ∧ q ≠ x ∧ hc_adjB x q = false := by decide +kernel

theorem pd_pre {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (h13 : totalSurplus 14 D ≤ 13)
    {I : Finset (Fin 14)} (hI : ineligSet 14 D = I) (hc : I.card = 4)
    (h012 : ({0, 1, 2} : Finset (Fin 14)) ⊆ I) :
    Bzero 14 D = 0 ∧ Bplus 14 D ≤ (eligSet 14 D).card + 3 := by
  have h1 := inelig_card_add 14 D
  rw [hI, hc] at h1
  have h2 := tri13 h hD h13 (fun i hi => by rw [hI]; exact h012 hi) (by omega)
  have h4 := totalSurplus_split 14 D
  omega

theorem pd_meet {D : Dag} {b : Fin 14 → ℕ} {u : Σ _ : ℕ, ℕ} {x y z : Fin 14}
    (hu : u ∈ residualUnits 14 D b) (hm : (supp 14 D u.1 ∩ {x, y, z}).Nonempty) :
    u ∈ ru D b x ∨ u ∈ ru D b y ∨ u ∈ ru D b z := by
  obtain ⟨a, ha⟩ := hm
  rw [Finset.mem_inter, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha.2 with rfl | rfl | rfl
  · exact Or.inl (mem_ru.2 ⟨hu, ha.1⟩)
  · exact Or.inr (Or.inl (mem_ru.2 ⟨hu, ha.1⟩))
  · exact Or.inr (Or.inr (mem_ru.2 ⟨hu, ha.1⟩))

theorem pd_line {D : Dag} {pos : Fin 14 → ℕ × Bool} (h : StrictLive 14 D) (hD : Correct D)
    (hpos : k4_Pos 14 HG D pos) (hB0 : Bzero 14 D = 0)
    (hB : Bplus 14 D ≤ (eligSet 14 D).card + 3) (b : Fin 14 → ℕ) (hb : PureBranch 14 D b)
    {T J : Finset (Fin 14)} (hOK : tOK T J = true) (hJ : J ⊆ ineligSet 14 D) {t i j z : Fin 14}
    (hg : t ∈ T ∧ i ∈ J ∧ j ∈ J ∧ i ≠ j ∧ hc_adjB i t = true ∧ hc_adjB j t = true ∧
      hc_adjB t z = true ∧ z ≠ i ∧ z ≠ j) :
    ∃ F, sem_bar F ∈ sem_W 14 D z ∧ sem_W 14 D t = {pos i, pos j, F} ∧
      (F ≠ pos i ∧ F ≠ pos j) ∧ merges 14 D (carrierT 14 D {t}) = ∅ ∧
      (ru D b t).card = 1 ∧ ∀ u ∈ residualUnits 14 D b, (supp 14 D u.1 ∩ T).Nonempty := by
  obtain ⟨ht, hiJ, hjJ, hij, hit, hjt, htz, hzi, hzj⟩ := hg
  rw [hc_adjB_iff] at hit hjt htz
  have hi := hJ hiJ
  have hj := hJ hjJ
  obtain ⟨hT, hU⟩ := tri_hw_sat h hD hB0 hB b hb hOK (fun _ ha => hJ ha)
  obtain ⟨hc3, hM⟩ := hT t ht
  obtain ⟨F, hF1, hF2, -⟩ := sem_edge_slots sem_heawood_gr h.1 (sem_heawood_comp hD) htz
  have hFi : F ≠ pos i := fun he => hzi (as_priv hpos hi (by rw [← he]; exact hF2))
  have hFj : F ≠ pos j := fun he => hzj (as_priv hpos hj (by rw [← he]; exact hF2))
  have hpij : pos i ≠ pos j := fun he => hij (hpos.2 i hi j hj he)
  have hsub : ({pos i, pos j, F} : Finset (ℕ × Bool)) ⊆ sem_W 14 D t := by
    intro e he
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact as_mem hpos hi hit
    · exact as_mem hpos hj hjt
    · exact hF1
  have hcard : ({pos i, pos j, F} : Finset (ℕ × Bool)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hpij, Ne.symm hFi]),
      Finset.card_pair (Ne.symm hFj)]
  have heq := Finset.eq_of_subset_of_card_le hsub (by omega)
  have hte : t ∈ eligSet 14 D := by
    rcases sem_elig_cover sem_heawood_gr h (sem_heawood_comp hD) hit with h1 | h1
    · exact absurd h1 (sem_mem_inelig.1 hi)
    · exact h1
  have hcc := cc_el h hD b hb hte
  rw [hM, ← heq, hcard, Finset.card_empty] at hcc
  exact ⟨F, hF2, heq.symm, ⟨hFi, hFj⟩, hM, by omega, hU⟩

theorem pd_full {D : Dag} {pos : Fin 14 → ℕ × Bool} (h : StrictLive 14 D) (hD : Correct D)
    (hB0 : Bzero 14 D = 0) (hpos : k4_Pos 14 HG D pos) {t i j z : Fin 14} {F : ℕ × Bool}
    (hi : i ∈ ineligSet 14 D) (hj : j ∈ ineligSet 14 D) (hg : Adj i t ∧ j ≠ i ∧ z ≠ i)
    (hW : sem_W 14 D t = {pos i, pos j, F}) (hF : sem_bar F ∈ sem_W 14 D z) :
    ∀ a, a ∈ supp 14 D (src D (pos i)) ↔ Adj i a := by
  refine full h hD hB0 hpos hi hg.1 (fun p hp hne hsub => ?_)
  rw [hW, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl
  · exact hne rfl
  · have : j ∈ supp 14 D (src D (sem_bar (pos j))) := by
      rw [show src D (sem_bar (pos j)) = src D ((pos j).1, !(pos j).2) from rfl,
        (hpos.1 j hj).2.2.2]
      exact Finset.mem_singleton_self j
    exact hg.2.1 (Finset.mem_singleton.1 (hsub this))
  · exact hg.2.2 (Finset.mem_singleton.1 (hsub (sem_mem_W.1 hF).2.1))

theorem pd_cov {D : Dag} {pos : Fin 14 → ℕ × Bool} (h : StrictLive 14 D) (hD : Correct D)
    {t i x : Fin 14} {P F : ℕ × Bool}
    (hW : ∀ e ∈ sem_W 14 D t, e = pos i ∨ e = P ∨ e = F)
    (hfi : ∀ a, Adj i a → a ∈ supp 14 D (src D (pos i))) (hit : Adj i t) (hxt : x ≠ t)
    (hxi : x ≠ i) (hP : x ∈ supp 14 D (src D P)) (hF : x ∈ supp 14 D (src D F)) : False := by
  obtain ⟨q, hq1, hq2, -, hq4⟩ := pd_q i t x ((hc_adjB_iff _ _).2 hit) hxt hxi
  obtain ⟨e, he, h1, h2⟩ :=
    sem_hw_cover_free h hD (Ne.symm hxt) (Ne.symm hq2) (sem_adjB_false.1 hq4)
  rcases hW e he with rfl | rfl | rfl
  · exact h2 (hfi q ((hc_adjB_iff _ _).1 hq1))
  · exact h1 hP
  · exact h1 hF

theorem pd_pure {D : Dag} {pos : Fin 14 → ℕ × Bool} (h : StrictLive 14 D) (hD : Correct D)
    (hpos : k4_Pos 14 HG D pos) (b : Fin 14 → ℕ) (hb : PureBranch 14 D b) {t i j : Fin 14}
    {F : ℕ × Bool} (hi : i ∈ ineligSet 14 D) (hj : j ∈ ineligSet 14 D)
    (hg : i ≠ j ∧ Adj i t ∧ Adj j t) (hW : sem_W 14 D t = {pos i, pos j, F})
    (hF : F ≠ pos i ∧ F ≠ pos j) (hfi : ∀ a, a ∈ supp 14 D (src D (pos i)) ↔ Adj i a)
    (hfj : ∀ a, a ∈ supp 14 D (src D (pos j)) ↔ Adj j a) (hc : (ru D b t).card = 1)
    {u : Σ _ : ℕ, ℕ} (hu : u ∈ residualUnits 14 D b) (htu : t ∈ supp 14 D u.1) {x : Fin 14}
    (hx : x ∈ supp 14 D u.1) : x = t := by
  by_contra hxt
  have hxe := res_elig hu hx
  have hxi : x ≠ i := fun e => sem_mem_inelig.1 hi (e ▸ hxe)
  have hxj : x ≠ j := fun e => sem_mem_inelig.1 hj (e ▸ hxe)
  obtain ⟨v, hv⟩ := Finset.card_eq_one.1 hc
  have huv : u = v := by
    have : u ∈ ru D b t := mem_ru.2 ⟨hu, htu⟩
    rwa [hv, Finset.mem_singleton] at this
  obtain ⟨e0, he0⟩ := ri_gen sem_heawood_gr h (sem_heawood_comp hD) b hb (Ne.symm hxt)
    (res_elig hu htu) (fun u' hu' ht' => by
      have : u' ∈ ru D b t := mem_ru.2 ⟨hu', ht'⟩
      rw [hv, Finset.mem_singleton] at this
      rw [this, ← huv]; exact hx) ⟨htu, hx⟩
  have hW' : ∀ e ∈ sem_W 14 D t, e = pos i ∨ e = pos j ∨ e = F := fun e he => by
    rw [hW] at he; simpa using he
  have hmi : pos i ∈ sem_W 14 D t := by rw [hW]; simp
  have hmj : pos j ∈ sem_W 14 D t := by rw [hW]; simp
  have hmF : F ∈ sem_W 14 D t := by rw [hW]; simp
  have hpij : pos i ≠ pos j := fun e => hg.1 (hpos.2 i hi j hj e)
  by_cases h1 : x ∈ supp 14 D (src D (pos i))
  · by_cases h2 : x ∈ supp 14 D (src D (pos j))
    · exact hxt (sem_hw_common i j x t hg.1 ((hc_adjB_iff _ _).2 (adj_symm hg.2.1))
        ((hc_adjB_iff _ _).2 (adj_symm hg.2.2)) ((hc_adjB_iff _ _).2 (adj_symm ((hfi x).1 h1)))
        ((hc_adjB_iff _ _).2 (adj_symm ((hfj x).1 h2))))
    · have hej : pos j = e0 := by
        by_contra hne
        exact h2 (he0 _ hmj hne)
      exact pd_cov h hD (fun e he => or_left_comm.1 (hW' e he)) (fun a ha => (hfj a).2 ha)
        hg.2.2 hxt hxj h1 (he0 F hmF (fun e => hF.2 (e.trans hej.symm)))
  · have hei : pos i = e0 := by
      by_contra hne
      exact h1 (he0 _ hmi hne)
    exact pd_cov h hD hW' (fun a ha => (hfi a).2 ha) hg.2.1 hxt hxi
      (he0 _ hmj (fun e => hpij (hei.trans e.symm)))
      (he0 F hmF (fun e => hF.1 (e.trans hei.symm)))

theorem pd_spoke {D : Dag} {pos : Fin 14 → ℕ × Bool} (h : StrictLive 14 D) (hD : Correct D)
    (hpos : k4_Pos 14 HG D pos) {i s d : Fin 14} (hi : i ∈ ineligSet 14 D)
    (hg : Adj i s ∧ Adj d s ∧ s ≠ i ∧ d ≠ i) (hc : (sem_W 14 D s).card ≤ 2) :
    ∃ Z, (∀ t, t ≠ s → Z ∉ sem_W 14 D t) ∧ Z ∈ sem_W 14 D s ∧ sem_bar Z ∈ sem_W 14 D d := by
  obtain ⟨Z, -, hW, hZp⟩ := ps h hD hpos hi hg.2.2.1 (as_mem hpos hi hg.1) hc
  obtain ⟨e, he1, he2, -⟩ := sem_edge_slots sem_heawood_gr h.1 (sem_heawood_comp hD) hg.2.1
  rw [hW, Finset.mem_insert, Finset.mem_singleton] at he2
  rcases he2 with h1 | h1
  · exact absurd (as_priv hpos hi (by rw [← h1, sem_bar_bar]; exact he1)) hg.2.2.2
  · exact ⟨Z, hZp, by rw [hW]; simp, by rw [← h1, sem_bar_bar]; exact he1⟩

theorem elim_p11_nonconc {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h13 : totalSurplus 14 D ≤ 13) (hI : ineligSet 14 D = {0, 1, 2}) : False := by
  have h1 := inelig_card_add 14 D
  rw [hI, show ({0, 1, 2} : Finset (Fin 14)).card = 3 from rfl] at h1
  have h2 := tri13 h hD h13 (fun i hi => by rw [hI]; exact hi) (by omega)
  have h4 := Bplus_le_total 14 D
  omega

theorem pd_cgeo : ∀ M : Finset (Fin 7), M.card ≤ 3 → 2 * M.card ≤
    ((M.image os_pt).biUnion (fun c => sem_hw_nb c ∩ sem_hw_opp 0)).card := by decide +kernel

theorem pd_cnt {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (h13 : totalSurplus 14 D ≤ 13)
    (Q : Finset (Fin 7)) (hI : ineligSet 14 D = Q.image os_pt) (hQ : Q.card = 4)
    (h012 : ({0, 1, 2} : Finset (Fin 14)) ⊆ Q.image os_pt) : False := by
  classical
  obtain ⟨hB0, hB⟩ := pd_pre h hD h13 hI
    (by rw [Finset.card_image_of_injective _ os_pt_inj, hQ]) h012
  have hQi : ∀ k ∈ Q, os_pt k ∈ ineligSet 14 D := fun k hk => by
    rw [hI]; exact Finset.mem_image_of_mem _ hk
  have hPe : sem_hw_opp 0 ⊆ eligSet 14 D := by
    intro a ha
    by_contra hne
    have h1 := sem_mem_inelig.2 hne
    rw [hI] at h1
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 h1
    exact (by decide : ∀ k : Fin 7, os_pt k ∉ sem_hw_opp 0) k ha
  let Oc := Finset.univ.filter (fun k : Fin 7 => sup_Occ 14 D (sem_hw_opp 0) (sem_hw_nb (os_pt k)))
  let Mi := Finset.univ.filter
    (fun k : Fin 7 => ¬ sup_Occ 14 D (sem_hw_opp 0) (sem_hw_nb (os_pt k)))
  have hcnt := hw_count h hD (sem_hw_opp 0) (Finset.Subset.refl _) hPe (Oc.image os_pt)
    (Mi.image os_pt) (Q.image os_pt)
    (fun i hi => by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hi
      exact ⟨os_nb_sub k, (Finset.mem_filter.1 hk).2⟩)
    (fun c hc => by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hc
      refine ⟨fun hc' => ?_, Or.inr ⟨os_nb_sub k, (Finset.mem_filter.1 hk).2⟩⟩
      obtain ⟨k', hk', hkk⟩ := Finset.mem_image.1 hc'
      rw [os_pt_inj hkk] at hk'
      exact (Finset.mem_filter.1 hk).2 (Finset.mem_filter.1 hk').2)
    (fun i hi => by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hi
      exact ⟨hQi k hk, os_nb_sub k⟩)
  have hlost := hw_lost h hD (sem_hw_opp 0) (sem_hw_opp_indep 0) ((Mi ∩ Q).image os_pt)
    (fun i hi => by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hi
      rw [Finset.mem_inter] at hk
      exact ⟨hQi k hk.2, os_nb_sub k, (Finset.mem_filter.1 hk.1).2⟩)
  rw [Finset.card_image_of_injective _ os_pt_inj] at hlost
  rw [Finset.card_image_of_injective _ os_pt_inj, Finset.card_image_of_injective _ os_pt_inj,
    hQ] at hcnt
  have hsplit : Oc.card + Mi.card = 7 := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 7)))
      (fun k : Fin 7 => sup_Occ 14 D (sem_hw_opp 0) (sem_hw_nb (os_pt k)))
    simpa using this
  have h1 := Finset.card_inter_add_card_sdiff Mi Q
  have h2 : (Mi \ Q).card ≤ (Finset.univ \ Q).card :=
    Finset.card_le_card (Finset.sdiff_subset_sdiff (Finset.subset_univ _) (Finset.Subset.refl _))
  rw [Finset.card_univ_sdiff, hQ, Fintype.card_fin] at h2
  have hgeo := pd_cgeo Mi (by omega)
  have hP7 : (sem_hw_opp 0).card = 7 := by decide
  omega

theorem elim_p10_line {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h13 : totalSurplus 14 D ≤ 13) (hI : ineligSet 14 D = {0, 1, 2, 3}) : False :=
  pd_cnt h hD h13 {0, 1, 2, 3} (by rw [hI]; decide) rfl (by decide)

theorem elim_p10_cap {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h13 : totalSurplus 14 D ≤ 13) (hI : ineligSet 14 D = {0, 1, 2, 5}) : False :=
  pd_cnt h hD h13 {0, 1, 2, 5} (by rw [hI]; decide) rfl (by decide)

theorem elim_p10_mixed31 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h13 : totalSurplus 14 D ≤ 13) (hI : ineligSet 14 D = {0, 1, 2, 11}) : False := by
  obtain ⟨hB0, hB⟩ := pd_pre h hD h13 hI rfl (by decide)
  obtain ⟨b, hb⟩ := exists_pureBranch h hD
  obtain ⟨pos, hpos⟩ := k4_assigned sem_heawood_gr h (sem_heawood_comp hD)
  have hJ1 : ({0, 1, 2} : Finset (Fin 14)) ⊆ ineligSet 14 D := by rw [hI]; decide
  have i0 := hJ1 (show (0 : Fin 14) ∈ ({0, 1, 2} : Finset (Fin 14)) by decide)
  have i1 := hJ1 (show (1 : Fin 14) ∈ ({0, 1, 2} : Finset (Fin 14)) by decide)
  have i2 := hJ1 (show (2 : Fin 14) ∈ ({0, 1, 2} : Finset (Fin 14)) by decide)
  obtain ⟨F7, hF7, hW7, n7, -, c7, m1⟩ := pd_line h hD hpos hB0 hB b hb pd_ok1 hJ1
    (t := 7) (i := 0) (j := 1) (z := 3) (by decide)
  obtain ⟨F13, hF13, hW13, n13, -, c13, -⟩ := pd_line h hD hpos hB0 hB b hb pd_ok1 hJ1
    (t := 13) (i := 1) (j := 2) (z := 4) (by decide)
  obtain ⟨F8, hF8, hW8, n8, -, c8, -⟩ := pd_line h hD hpos hB0 hB b hb pd_ok1 hJ1
    (t := 8) (i := 2) (j := 0) (z := 6) (by decide)
  have f0 := pd_full h hD hB0 hpos i0 i1 (by decide) hW7 hF7
  have f1 := pd_full h hD hB0 hpos i1 i2 (by decide) hW13 hF13
  have f2 := pd_full h hD hB0 hpos i2 i0 (by decide) hW8 hF8
  have hno : ∀ y : Fin 14, y ∉ ({7, 8, 13} : Finset (Fin 14)) → (sem_W 14 D y).card ≤ 2 := by
    intro y hy
    have he : ru D b y = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro u hu
      obtain ⟨huR, hyu⟩ := mem_ru.1 hu
      rcases pd_meet huR (m1 u huR) with h7 | h8 | h13
      · exact hy (by
          rw [pd_pure h hD hpos b hb i0 i1 (by decide) hW7 n7 f0 f1 c7 huR (mem_ru.1 h7).2 hyu]
          decide)
      · exact hy (by
          rw [pd_pure h hD hpos b hb i2 i0 (by decide) hW8 n8 f2 f0 c8 huR (mem_ru.1 h8).2 hyu]
          decide)
      · exact hy (by
          rw [pd_pure h hD hpos b hb i1 i2 (by decide) hW13 n13 f1 f2 c13 huR
            (mem_ru.1 h13).2 hyu]
          decide)
    have := cc_le h hD b hb y
    rw [he, Finset.card_empty] at this
    omega
  obtain ⟨Z1, p1, q1, r1⟩ := pd_spoke h hD hpos i0 (s := 10) (d := 5) (by decide)
    (hno 10 (by decide))
  obtain ⟨Z2, p2, q2, r2⟩ := pd_spoke h hD hpos i1 (s := 9) (d := 5) (by decide)
    (hno 9 (by decide))
  obtain ⟨Z3, -, q3, r3⟩ := pd_spoke h hD hpos i2 (s := 12) (d := 5) (by decide)
    (hno 12 (by decide))
  have n12 : sem_bar Z1 ≠ sem_bar Z2 := fun e =>
    p1 9 (by decide) (by rw [← sem_bar_bar Z1, e, sem_bar_bar]; exact q2)
  have n13' : sem_bar Z1 ≠ sem_bar Z3 := fun e =>
    p1 12 (by decide) (by rw [← sem_bar_bar Z1, e, sem_bar_bar]; exact q3)
  have n23 : sem_bar Z2 ≠ sem_bar Z3 := fun e =>
    p2 12 (by decide) (by rw [← sem_bar_bar Z2, e, sem_bar_bar]; exact q3)
  have hsub : ({sem_bar Z1, sem_bar Z2, sem_bar Z3} : Finset (ℕ × Bool)) ⊆ sem_W 14 D 5 := by
    intro e he
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl <;> assumption
  have := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by simp [n12, n13']), Finset.card_pair n23] at this
  have := hno 5 (by decide)
  omega

section PeMixed

open Finset

def pe_tau : Equiv.Perm (Fin 14) :=
  ⟨hc_ofList [11, 12, 13, 7, 8, 9, 10, 3, 4, 5, 6, 0, 1, 2],
    hc_ofList [11, 12, 13, 7, 8, 9, 10, 3, 4, 5, 6, 0, 1, 2],
    by intro x; revert x; decide +kernel, by intro x; revert x; decide +kernel⟩

def pe_I : Finset (Fin 14) := {0, 1, 11, 12}

def pe_bs (D : Dag) (x : Fin 14) : ℕ :=
  surplusOn D ((inner 14 D).filter (fun w => x ∈ supp 14 D w))

def pe_K (D : Dag) (b : Fin 14 → ℕ) (pos : Fin 14 → ℕ × Bool) : Prop :=
  StrictLive 14 D ∧ Correct D ∧ PureBranch 14 D b ∧ k4_Pos 14 HG D pos ∧ ineligSet 14 D = pe_I

theorem pe_bs_tr (σ : Equiv.Perm (Fin 14)) {D : Dag} (hS : Strict 14 D) (x : Fin 14) :
    pe_bs (relabel σ D) (σ x) = pe_bs D x :=
  tr_surplus_filter σ D _ _ (fun w => by rw [relabel_supp σ hS]; simp)

variable {D : Dag} {pos : Fin 14 → ℕ × Bool} {b : Fin 14 → ℕ}

theorem pe_bs_eq (hK : pe_K D b pos) {x : Fin 14} (hx : x ∈ eligSet 14 D) :
    pe_bs D x = 1 + (ru D b x).card := by
  obtain ⟨h, hD, hb, -⟩ := hK
  have h1 := sem_flow1 sem_heawood_gr h (sem_heawood_comp hD) x
  have h2 := cc_el h hD b hb hx
  have h3 : (inner 14 D).filter (fun w => x ∈ supp 14 D w) = carrierT 14 D {x} := by
    ext w
    rw [mem_filter, sem_mem_carrier1, sb_mem_inner]
    refine ⟨fun hh => hh.2, fun hh => ⟨?_, hh⟩⟩
    have h4 := sem_supp_lt hh
    have h5 : w ≠ outW 14 D := fun e => by
      rw [e, heawood_supp_out hD] at hh
      exact notMem_empty _ hh
    unfold outW at h5
    omega
  unfold pe_bs
  rw [h3]
  omega

theorem pe_in (hK : pe_K D b pos) (i : Fin 14) (hi : i ∈ pe_I) : i ∈ ineligSet 14 D := by
  rw [hK.2.2.2.2]; exact hi

theorem pe_el (hK : pe_K D b pos) (x : Fin 14) (hx : x ∉ pe_I) : x ∈ eligSet 14 D := by
  by_contra hne
  exact hx (hK.2.2.2.2 ▸ sem_mem_inelig.2 hne)

theorem pe_np1 (hpos : k4_Pos 14 HG D pos) {i x : Fin 14} {e : ℕ × Bool}
    (hi : i ∈ ineligSet 14 D) (hx : x ∈ eligSet 14 D) (he : sem_bar e ∈ sem_W 14 D x) :
    e ≠ pos i := fun heq => sem_mem_inelig.1 hi (as_priv hpos hi (heq ▸ he) ▸ hx)

theorem pe_np2 (hpos : k4_Pos 14 HG D pos) {i x : Fin 14} {e : ℕ × Bool}
    (hi : i ∈ ineligSet 14 D) (hx : x ∈ eligSet 14 D) (he : e ∈ sem_W 14 D x) :
    sem_bar e ≠ pos i := pe_np1 hpos hi hx (by rw [sem_bar_bar]; exact he)

theorem pe_asw (hpos : k4_Pos 14 HG D pos) {i t : Fin 14} (hi : i ∈ ineligSet 14 D)
    (ht : t ∈ supp 14 D (src D (pos i))) : pos i ∈ sem_W 14 D t :=
  sem_mem_W.2 ⟨(hpos.1 i hi).1, ht, by rw [(hpos.1 i hi).2.1]; exact notMem_empty t⟩

theorem pe_J (hK : pe_K D b pos) {x : Fin 14} (J : Finset (Fin 14))
    (hJ : ∀ i ∈ J, i ∈ pe_I ∧ hc_adjB i x = true) :
    ∀ i ∈ J, i ∈ ineligSet 14 D ∧ pos i ∈ sem_W 14 D x := fun i hi =>
  ⟨pe_in hK _ (hJ i hi).1,
    as_mem hK.2.2.2.1 (pe_in hK _ (hJ i hi).1) ((hc_adjB_iff _ _).1 (hJ i hi).2)⟩

theorem pe_cnt (hpos : k4_Pos 14 HG D pos) {x : Fin 14} (J : Finset (Fin 14))
    (hJ : ∀ i ∈ J, i ∈ ineligSet 14 D ∧ pos i ∈ sem_W 14 D x) (Fs : Finset (ℕ × Bool))
    (hF : ∀ e ∈ Fs, e ∈ sem_W 14 D x ∧ ∀ i ∈ J, e ≠ pos i) :
    J.card + Fs.card ≤ (sem_W 14 D x).card := by
  classical
  have hinj : Set.InjOn pos J := fun i hi j hj hij => hpos.2 i (hJ i hi).1 j (hJ j hj).1 hij
  have hdis : Disjoint (J.image pos) Fs := by
    rw [disjoint_left]
    intro e he1 he2
    obtain ⟨i, hi, rfl⟩ := mem_image.1 he1
    exact (hF _ he2).2 i hi rfl
  have := card_le_card (union_subset (fun e he => by
    obtain ⟨i, hi, rfl⟩ := mem_image.1 he
    exact (hJ i hi).2) (fun e he => (hF e he).1) : J.image pos ∪ Fs ⊆ sem_W 14 D x)
  rwa [card_union_of_disjoint hdis, card_image_of_injOn hinj] at this

theorem pe_co (hK : pe_K D b pos) {v t j q : Fin 14} (hj : j ∈ ineligSet 14 D)
    (hv : v ∈ eligSet 14 D)
    (hres : ∀ u ∈ residualUnits 14 D b, v ∈ supp 14 D u.1 → t ∈ supp 14 D u.1) {w : ℕ}
    (hw : v ∈ supp 14 D w ∧ t ∈ supp 14 D w)
    (hg : hc_adjB j v = true ∧ hc_adjB j q = true ∧ v ≠ t ∧ v ≠ q ∧ hc_adjB t q = false) :
    t ∈ supp 14 D (src D (pos j)) := by
  obtain ⟨h, hD, hb, hpos, -⟩ := hK
  obtain ⟨hjv, hjq, hvt, hvq, htq⟩ := hg
  rw [hc_adjB_iff] at hjv hjq
  obtain ⟨e0, he0⟩ := ri_gen sem_heawood_gr h (sem_heawood_comp hD) b hb hvt hv hres hw
  by_contra hn
  have h0 : pos j = e0 := by
    by_contra hne
    exact hn (he0 _ (as_mem hpos hj hjv) hne)
  obtain ⟨e, he, h1, h2⟩ := sem_hw_cover_free h hD hvt hvq (sem_adjB_false.1 htq)
  exact h1 (he0 e he (fun hee => h2 (by rw [hee, ← h0]; exact (hpos.1 j hj).2.2.1 q hjq)))

theorem pe_co2 (hK : pe_K D b pos) {v i j t : Fin 14} {u : Σ _ : ℕ, ℕ}
    (hu : u ∈ residualUnits 14 D b) (hvu : v ∈ supp 14 D u.1)
    (huq : ∀ u' ∈ residualUnits 14 D b, v ∈ supp 14 D u'.1 → u' = u)
    (hg : i ∈ pe_I ∧ j ∈ pe_I ∧ v ∉ pe_I ∧ hc_adjB i v = true ∧ hc_adjB j v = true ∧
      ∀ t : Fin 14, t ∉ pe_I → v ≠ t → ∃ q0 q1 : Fin 14,
        (hc_adjB i q0 = true ∧ v ≠ q0 ∧ hc_adjB t q0 = false) ∧
        hc_adjB j q1 = true ∧ v ≠ q1 ∧ hc_adjB t q1 = false)
    (htv : v ≠ t) (ht : t ∈ supp 14 D u.1) :
    ∀ k ∈ ({i, j} : Finset (Fin 14)), pos k ∈ sem_W 14 D t := by
  obtain ⟨hi, hj, hv, hiv, hjv, hq⟩ := hg
  obtain ⟨q0, q1, ⟨a1, a2, a3⟩, a4, a5, a6⟩ := hq t
    (fun hm => sem_mem_inelig.1 (pe_in hK _ hm) (res_elig hu ht)) htv
  have hres : ∀ u' ∈ residualUnits 14 D b, v ∈ supp 14 D u'.1 → t ∈ supp 14 D u'.1 :=
    fun u' hu' hv' => huq u' hu' hv' ▸ ht
  intro k hk
  rcases mem_insert.1 hk with e | e
  · rw [e]
    exact pe_asw hK.2.2.2.1 (pe_in hK _ hi) (pe_co hK (pe_in hK _ hi) (pe_el hK _ hv) hres
      ⟨hvu, ht⟩ ⟨hiv, a1, htv, a2, a3⟩)
  · rw [mem_singleton.1 e]
    exact pe_asw hK.2.2.2.1 (pe_in hK _ hj) (pe_co hK (pe_in hK _ hj) (pe_el hK _ hv) hres
      ⟨hvu, ht⟩ ⟨hjv, a4, htv, a5, a6⟩)

theorem pe_ft (hK : pe_K D b pos) (hB0 : Bzero 14 D = 0) {v t0 : Fin 14}
    (J : Finset (Fin 14)) (hJ : ∀ i ∈ J, i ∈ ineligSet 14 D ∧ pos i ∈ sem_W 14 D v)
    {P : ℕ × Bool} (hP : P ∈ sem_W 14 D v ∧ ∀ i ∈ ineligSet 14 D, P ≠ pos i)
    (ht0 : t0 ∈ supp 14 D (src D (sem_bar P)))
    (hcard : (sem_W 14 D v).card ≤ J.card + 1) (i : Fin 14) (hi : i ∈ J)
    (hg : hc_adjB i v = true ∧ t0 ≠ i) :
    ∀ t, t ∈ supp 14 D (src D (pos i)) ↔ Adj i t := by
  classical
  obtain ⟨h, hD, -, hpos, -⟩ := hK
  refine full h hD hB0 hpos (hJ i hi).1 ((hc_adjB_iff _ _).1 hg.1) (fun p hp hne hsub => ?_)
  by_cases h1 : ∃ j ∈ J, p = pos j
  · obtain ⟨j, hj, rfl⟩ := h1
    have h2 : j ∈ supp 14 D (src D (sem_bar (pos j))) := by
      rw [show src D (sem_bar (pos j)) = src D ((pos j).1, !(pos j).2) from rfl,
        (hpos.1 j (hJ j hj).1).2.2.2]
      exact mem_singleton_self j
    exact hne (by rw [mem_singleton.1 (hsub h2)])
  · by_cases h2 : p = P
    · exact hg.2 (mem_singleton.1 (hsub (h2 ▸ ht0)))
    · have := pe_cnt hpos J hJ {P, p} (fun e he => by
        rcases mem_insert.1 he with he | he
        · rw [he]; exact ⟨hP.1, fun j hj => hP.2 j (hJ j hj).1⟩
        · rw [mem_singleton.1 he]
          exact ⟨hp, fun j hj hpj => h1 ⟨j, hj, hpj⟩⟩)
      rw [card_pair (Ne.symm h2)] at this
      omega

theorem pe_df (hK : pe_K D b pos) {v c : Fin 14} (hv : v ∈ eligSet 14 D) (hvc : v ≠ c)
    {w : ℕ} (hw : v ∈ supp 14 D w ∧ c ∈ supp 14 D w)
    (hcnt : (ru D b v).card ≤ (ru D b v ∩ ru D b c).card + 1) {p q P : ℕ × Bool}
    (hp : p ∈ sem_W 14 D v) (hq : q ∈ sem_W 14 D v) (hP : P ∈ sem_W 14 D v)
    (hd : p ≠ q ∧ p ≠ P ∧ q ≠ P) (hcP : c ∉ supp 14 D (src D P)) :
    c ∈ supp 14 D (src D p) ∨ c ∈ supp 14 D (src D q) := by
  classical
  obtain ⟨h, hD, hb, -⟩ := hK
  by_contra hcon
  rw [not_or] at hcon
  have s1 := sem_surplus_diff h.1 b hb hvc hv
  have s2 := carrier_flow_diff h v c hvc (by rw [heawood_supp_out hD]; exact notMem_empty v)
  obtain ⟨j, s, hj, ht, -, hcj, hvs, hcs, -⟩ := sem_first_joint h.1 hvc hw
  have hm : ∀ e ∈ sem_W 14 D v, c ∉ supp 14 D (src D e) →
      e ∈ (exitArcs 14 D (carrierDiff 14 D v c)).erase (j, s) := fun e he hce =>
    mem_erase.2 ⟨fun heq => by
      have := sem_W_and h.1 he
      rw [heq, ht] at this
      exact Bool.false_ne_true this, sem_mem_exit_diff.2 ⟨(sem_mem_W.1 he).1,
        ⟨(sem_mem_W.1 he).2.1, hce⟩, fun hh => (sem_mem_W.1 he).2.2 hh.1⟩⟩
  have hc4 := two_lt_card.2 ⟨p, hm _ hp hcon.1, q, hm _ hq hcon.2, P, hm _ hP hcP, hd⟩
  rw [card_erase_of_mem (sem_mem_exit_diff.2 ⟨hj, ⟨hvs, hcs⟩, fun hh => hh.2 hcj⟩)] at hc4
  have h5 : ((residualUnits 14 D b).filter
      (fun u => v ∈ supp 14 D u.1 ∧ c ∉ supp 14 D u.1)).card ≤ (ru D b v \ ru D b c).card :=
    card_le_card (fun u hu => by
      rw [mem_filter] at hu
      exact mem_sdiff.2 ⟨mem_ru.2 ⟨hu.1, hu.2.1⟩, fun hm => hu.2.2 (mem_ru.1 hm).2⟩)
  have h6 := card_inter_add_card_sdiff (ru D b v) (ru D b c)
  omega

theorem pe_ll (hK : pe_K D b pos) {x y z i j : Fin 14} (hg : i ∈ pe_I ∧ j ∈ pe_I ∧
      x ∉ pe_I ∧ y ∉ pe_I ∧ z ∉ pe_I ∧ hc_adjB i x = true ∧ hc_adjB j y = true ∧
      hc_adjB x y = true ∧ hc_adjB z x = true ∧ z ≠ y)
    (hx0 : (ru D b x).card = 0) (hy0 : (ru D b y).card = 0) : False := by
  obtain ⟨g1, g2, g3, g4, g5, hix, hjy, hxy, hzx, hzy⟩ := hg
  rw [hc_adjB_iff] at hix hjy hxy hzx
  have hi := pe_in hK _ g1
  have hj := pe_in hK _ g2
  have hx := pe_el hK _ g3
  have hy := pe_el hK _ g4
  have hz := pe_el hK _ g5
  obtain ⟨h, hD, hb, hpos, -⟩ := hK
  have hG := sem_heawood_gr
  have hC := sem_heawood_comp hD
  obtain ⟨Zx, -, hWx, -⟩ := ps h hD hpos hi (fun e => sem_mem_inelig.1 hi (e ▸ hx))
    (as_mem hpos hi hix) (by have := cc_le h hD b hb x; omega)
  obtain ⟨Zy, -, hWy, hZy⟩ := ps h hD hpos hj (fun e => sem_mem_inelig.1 hj (e ▸ hy))
    (as_mem hpos hj hjy) (by have := cc_le h hD b hb y; omega)
  obtain ⟨e, he1, he2, -⟩ := sem_edge_slots hG h.1 hC hxy
  obtain ⟨e', he1', he2', -⟩ := sem_edge_slots hG h.1 hC hzx
  have a1 : e = Zx := mem_singleton.1
    ((mem_insert.1 (hWx ▸ he1)).resolve_left (pe_np1 hpos hi hy he2))
  have a2 : sem_bar e = Zy := mem_singleton.1
    ((mem_insert.1 (hWy ▸ he2)).resolve_left (pe_np2 hpos hj hx he1))
  have a3 : sem_bar e' = Zx := mem_singleton.1
    ((mem_insert.1 (hWx ▸ he2')).resolve_left (pe_np2 hpos hi hz he1'))
  have a4 : e' = Zy := by rw [← a2, a1, ← a3, sem_bar_bar]
  exact hZy z hzy (a4 ▸ he1')

theorem pe_uq {x : Fin 14} {u0 : Σ _ : ℕ, ℕ} (h1 : (ru D b x).card = 1)
    (hu0 : u0 ∈ residualUnits 14 D b) (hx0 : x ∈ supp 14 D u0.1) :
    ∀ u ∈ residualUnits 14 D b, x ∈ supp 14 D u.1 → u = u0 := by
  obtain ⟨a, ha⟩ := card_eq_one.1 h1
  intro u hu hx
  have h2 : u ∈ ru D b x := mem_ru.2 ⟨hu, hx⟩
  have h4 : u0 ∈ ru D b x := mem_ru.2 ⟨hu0, hx0⟩
  rw [ha, mem_singleton] at h2 h4
  rw [h2, h4]

theorem pe_one (hK : pe_K D b pos) {x i : Fin 14} {us uo : Σ _ : ℕ, ℕ}
    (Js Jo : Finset (Fin 14)) {F : ℕ × Bool}
    (hg : Js ⊆ pe_I ∧ Jo ⊆ pe_I ∧ Js.card = 2 ∧ Jo.card = 2 ∧ Disjoint Js Jo ∧ i ∈ Js ∧
      hc_adjB i x = true)
    (hs : x ∈ supp 14 D us.1 → ∀ k ∈ Js, pos k ∈ sem_W 14 D x)
    (ho : x ∈ supp 14 D uo.1 → ∀ k ∈ Jo, pos k ∈ sem_W 14 D x)
    (hρ : (ru D b x).card ≤ (if x ∈ supp 14 D us.1 then 1 else 0) +
      if x ∈ supp 14 D uo.1 then 1 else 0)
    (hF : F ∈ sem_W 14 D x ∧ ∀ k ∈ ineligSet 14 D, F ≠ pos k) :
    ∀ e ∈ sem_W 14 D x, e = F ∨ e ∈ Js.image pos := by
  classical
  obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := hg
  have hin : ∀ {k : Fin 14}, k ∈ pe_I → k ∈ ineligSet 14 D := pe_in hK _
  obtain ⟨h, hD, hb, hpos, -⟩ := hK
  have hcc := cc_le h hD b hb x
  have hxi := as_mem hpos (hin (g1 g6)) ((hc_adjB_iff _ _).1 g7)
  have hF1 : ∀ J : Finset (Fin 14), (∀ k ∈ J, k ∈ ineligSet 14 D ∧ pos k ∈ sem_W 14 D x) →
      J.card + 1 ≤ (sem_W 14 D x).card := fun J hJ => by
    have := pe_cnt hpos J hJ {F} (fun e he => by
      rw [mem_singleton.1 he]; exact ⟨hF.1, fun k hk => hF.2 k (hJ k hk).1⟩)
    rwa [card_singleton] at this
  by_cases ko : x ∈ supp 14 D uo.1
  · exfalso
    by_cases ks : x ∈ supp 14 D us.1
    · have := hF1 (Js ∪ Jo) (fun k hk => by
        rcases mem_union.1 hk with hk | hk
        · exact ⟨hin (g1 hk), hs ks k hk⟩
        · exact ⟨hin (g2 hk), ho ko k hk⟩)
      rw [card_union_of_disjoint g5] at this
      simp only [ko, ks, ite_true] at hρ
      omega
    · have := hF1 (insert i Jo) (fun k hk => by
        rcases mem_insert.1 hk with hk | hk
        · rw [hk]; exact ⟨hin (g1 g6), hxi⟩
        · exact ⟨hin (g2 hk), ho ko k hk⟩)
      rw [card_insert_of_notMem (disjoint_left.1 g5 g6)] at this
      simp only [ko, ks, ite_true, ite_false] at hρ
      omega
  · intro e he
    by_contra hne
    rw [not_or] at hne
    have hF2 : ∀ J : Finset (Fin 14), J ⊆ Js → (∀ k ∈ J, pos k ∈ sem_W 14 D x) →
        J.card + 2 ≤ (sem_W 14 D x).card := fun J hJs hJ => by
      have := pe_cnt hpos J (fun k hk => ⟨hin (g1 (hJs hk)), hJ k hk⟩) {F, e}
        (fun e' he' => by
          rcases mem_insert.1 he' with he' | he'
          · rw [he']; exact ⟨hF.1, fun k hk => hF.2 k (hin (g1 (hJs hk)))⟩
          · rw [mem_singleton.1 he']
            exact ⟨he, fun k hk hek => hne.2 (mem_image.2 ⟨k, hJs hk, hek.symm⟩)⟩)
      rwa [card_pair (Ne.symm hne.1)] at this
    by_cases ks : x ∈ supp 14 D us.1
    · have := hF2 Js (Finset.Subset.refl _) (hs ks)
      simp only [ko, ks, ite_true, ite_false] at hρ
      omega
    · have := hF2 {i} (singleton_subset_iff.2 g6) (fun k hk => by
        rw [mem_singleton.1 hk]; exact hxi)
      rw [card_singleton] at this
      simp only [ko, ks, ite_false] at hρ
      omega

theorem pe_core {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (h13 : totalSurplus 14 D ≤ 13)
    (hI : ineligSet 14 D = pe_I) (hle : pe_bs D 7 ≤ pe_bs D 3) : False := by
  classical
  have hG := sem_heawood_gr
  have hC := sem_heawood_comp hD
  obtain ⟨b, hb⟩ := exists_pureBranch h hD
  obtain ⟨pos, hpos⟩ := k4_assigned hG h hC
  obtain ⟨H, hH3, hH7, hn7, hn3, -⟩ := sem_edge_slots hG h.1 hC (x := 3) (y := 7) (by decide)
  have hK : pe_K D b pos := ⟨h, hD, hb, hpos, hI⟩
  have hin := pe_in hK
  have hel := pe_el hK
  have i0 := hin 0 (by decide)
  have i1 := hin 1 (by decide)
  have l3 := hel 3 (by decide)
  have l7 := hel 7 (by decide)
  have hR : (residualUnits 14 D b).card + Bzero 14 D ≤ 3 := by
    have h1 := card_residual h.1 b hb
    have h2 := inelig_card_add 14 D
    have h3 := totalSurplus_split 14 D
    rw [hI, show pe_I.card = 4 from rfl] at h2
    omega
  have hJ7 := pe_J hK (x := 7) {0, 1} (by decide)
  have hJ3 := pe_J hK (x := 3) {11, 12} (by decide)
  have hK7 : ∀ i ∈ ineligSet 14 D, sem_bar H ≠ pos i := fun i hi => pe_np2 hpos hi l3 hH3
  have hK3 : ∀ i ∈ ineligSet 14 D, H ≠ pos i := fun i hi => pe_np1 hpos hi l7 hH7
  have c7 := pe_cnt hpos _ hJ7 {sem_bar H} (fun e he => by
    rw [mem_singleton.1 he]; exact ⟨hH7, fun i hi => hK7 i (hJ7 i hi).1⟩)
  have c3 := pe_cnt hpos _ hJ3 {H} (fun e he => by
    rw [mem_singleton.1 he]; exact ⟨hH3, fun i hi => hK3 i (hJ3 i hi).1⟩)
  have hc2 : ({0, 1} : Finset (Fin 14)).card = 2 ∧ ({11, 12} : Finset (Fin 14)).card = 2 ∧
      ({4, 6, 2, 5} : Finset (Fin 14)).card = 4 := ⟨rfl, rfl, rfl⟩
  rw [card_singleton, hc2.1] at c7
  rw [card_singleton, hc2.2.1] at c3
  have k7 := cc_el h hD b hb l7
  have k3 := cc_el h hD b hb l3
  have e7 := pe_bs_eq hK l7
  have e3 := pe_bs_eq hK l3
  have hH3s := (sem_mem_W.1 hH3).2.1
  have hX : ∀ x ∈ ({4, 6, 2, 5} : Finset (Fin 14)), x ∈ eligSet 14 D ∧ x ≠ 3 ∧ x ≠ 7 ∧
      ∃ w, x ∈ supp 14 D w ∧ (3 : Fin 14) ∈ supp 14 D w := by
    intro x hx
    obtain ⟨g1, g2, g3, i, hi, g4, g5⟩ := (by decide : ∀ x ∈ ({4, 6, 2, 5} : Finset (Fin 14)),
      x ∉ pe_I ∧ x ≠ 3 ∧ x ≠ 7 ∧ ∃ i ∈ pe_I, hc_adjB i x = true ∧ hc_adjB i 3 = true) x hx
    have hi2 := (hpos.1 i (hin i hi)).2.2.1
    exact ⟨hel x g1, g2, g3, _, hi2 x ((hc_adjB_iff _ _).1 g4), hi2 3 ((hc_adjB_iff _ _).1 g5)⟩

  have hA : ¬ ∀ u ∈ residualUnits 14 D b, (7 : Fin 14) ∈ supp 14 D u.1 →
      (3 : Fin 14) ∈ supp 14 D u.1 := by
    intro hA
    obtain ⟨u, hu⟩ := card_pos.1 (show 0 < (ru D b 7).card by omega)
    rw [mem_ru] at hu
    have hw : (7 : Fin 14) ∈ supp 14 D u.1 ∧ (3 : Fin 14) ∈ supp 14 D u.1 :=
      ⟨hu.2, hA u hu.1 hu.2⟩
    have p0 := pe_asw hpos i0 (pe_co hK i0 l7 hA hw (q := 8) (by decide))
    have p1 := pe_asw hpos i1 (pe_co hK i1 l7 hA hw (q := 9) (by decide))
    have c5 := pe_cnt hpos pe_I (fun i hi => ⟨hin i hi, by
      simp only [pe_I, mem_insert, mem_singleton] at hi
      rcases hi with rfl | rfl | rfl | rfl
      exacts [p0, p1, (hJ3 11 (by decide)).2, (hJ3 12 (by decide)).2]⟩) {H}
      (fun e he => by rw [mem_singleton.1 he]; exact ⟨hH3, fun i hi => hK3 i (hin i hi)⟩)
    rw [show pe_I.card = 4 from rfl, card_singleton] at c5
    have hall : ru D b 3 = residualUnits 14 D b :=
      eq_of_subset_of_card_le (filter_subset _ _) (by omega)
    have := cf_six h hD b hb cf3_good l3 {4, 6, 2, 5} (fun x hx =>
      ⟨(hX x hx).1, (hX x hx).2.1, fun u hu _ => (mem_ru.1 (hall ▸ hu)).2, (hX x hx).2.2.2⟩)
    rw [hc2.2.2] at this
    omega
  obtain ⟨uk, huk, hk7, hk3⟩ : ∃ u ∈ residualUnits 14 D b,
      (7 : Fin 14) ∈ supp 14 D u.1 ∧ (3 : Fin 14) ∉ supp 14 D u.1 := by
    by_contra hcon
    exact hA (fun u hu h7 => by
      by_contra h3
      exact hcon ⟨u, hu, h7, h3⟩)
  have hs3 : ru D b 3 ⊆ (residualUnits 14 D b).erase uk := fun u hu =>
    mem_erase.2 ⟨fun e => hk3 (e ▸ (mem_ru.1 hu).2), (mem_ru.1 hu).1⟩
  have hle3 := card_le_card hs3
  rw [card_erase_of_mem huk] at hle3

  have h71 : (ru D b 7).card = 1 := by
    by_contra h71
    have hui := card_union_add_card_inter (ru D b 3) (ru D b 7)
    have hun : (ru D b 3 ∪ ru D b 7).card ≤ (residualUnits 14 D b).card :=
      card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))
    obtain ⟨uj, huj⟩ := card_pos.1 (show 0 < (ru D b 3 ∩ ru D b 7).card by omega)
    rw [mem_inter, mem_ru, mem_ru] at huj
    have hw : (3 : Fin 14) ∈ supp 14 D uj.1 ∧ (7 : Fin 14) ∈ supp 14 D uj.1 :=
      ⟨huj.1.2, huj.2.2⟩
    have hpn : ∀ i ∈ pe_I, ∀ j ∈ pe_I, i ≠ j → pos i ≠ pos j :=
      fun i hi j hj hij e => hij (hpos.2 i (hin i hi) j (hin j hj) e)
    have a7 := pe_df hK l3 (by decide) hw (by omega) (hJ3 11 (by decide)).2
      (hJ3 12 (by decide)).2 hH3 ⟨hpn 11 (by decide) 12 (by decide) (by decide),
        (hK3 11 (hin 11 (by decide))).symm, (hK3 12 (hin 12 (by decide))).symm⟩ hn7
    have a3 := pe_df hK l7 (by decide) hw.symm (by rw [inter_comm]; omega)
      (hJ7 0 (by decide)).2 (hJ7 1 (by decide)).2 hH7 ⟨hpn 0 (by decide) 1 (by decide)
        (by decide), (hK7 0 i0).symm, (hK7 1 i1).symm⟩ hn3
    have fin : ∀ j ∈ ({11, 12} : Finset (Fin 14)),
        (7 : Fin 14) ∉ supp 14 D (src D (pos j)) := by
      intro j hj h7j
      have hJ : ∀ i ∈ insert j ({0, 1} : Finset (Fin 14)),
          i ∈ ineligSet 14 D ∧ pos i ∈ sem_W 14 D 7 := fun i hi => by
        rcases mem_insert.1 hi with hi | hi
        · rw [hi]; exact ⟨(hJ3 j hj).1, pe_asw hpos (hJ3 j hj).1 h7j⟩
        · exact hJ7 i hi
      have hcard : (insert j ({0, 1} : Finset (Fin 14))).card = 3 := by
        rw [mem_insert, mem_singleton] at hj
        rcases hj with rfl | rfl <;> rfl
      have f := pe_ft hK (by omega) _ hJ ⟨hH7, hK7⟩
        (by rw [sem_bar_bar]; exact hH3s) (by omega)
      rcases a3 with a | a
      · exact absurd ((f 0 (by simp) (by decide) 3).1 a) (by decide)
      · exact absurd ((f 1 (by simp) (by decide) 3).1 a) (by decide)
    rcases a7 with a | a
    · exact fin 11 (by decide) a
    · exact fin 12 (by decide) a
  have hu7 := pe_uq h71 huk hk7
  have co7 : ∀ t : Fin 14, 7 ≠ t → t ∈ supp 14 D uk.1 →
      ∀ k ∈ ({0, 1} : Finset (Fin 14)), pos k ∈ sem_W 14 D t :=
    fun t ht htu => pe_co2 hK huk hk7 hu7 (by decide) ht htu
  have f7 := fun hB0 : Bzero 14 D = 0 => pe_ft hK hB0 {0, 1} hJ7 ⟨hH7, hK7⟩
    (by rw [sem_bar_bar]; exact hH3s) (by rw [hc2.1]; omega)
  have hpk : Bzero 14 D = 0 → ∀ t ∈ supp 14 D uk.1, t = 7 := by
    intro hB0 t ht
    by_contra hne
    have a := co7 t (Ne.symm hne) ht
    exact hne ((by decide : ∀ t : Fin 14, Adj 0 t → Adj 1 t → t = 7) t
      ((f7 hB0 0 (by decide) (by decide) t).1 (sem_mem_W.1 (a 0 (by decide))).2.1)
      ((f7 hB0 1 (by decide) (by decide) t).1 (sem_mem_W.1 (a 1 (by decide))).2.1))
  have h31 : (ru D b 3).card = 1 := by
    by_contra h31
    have hB0 : Bzero 14 D = 0 := by omega
    have heq := eq_of_subset_of_card_le hs3 (by rw [card_erase_of_mem huk]; omega)
    have := cf_seven h hD hB0 b hb cf3_good l3 {4, 6, 2, 5} (fun x hx => by
        obtain ⟨g1, g2, g3, g4⟩ := hX x hx
        refine ⟨g1, g2, fun u hu hxu => ?_, g4⟩
        by_cases huu : u = uk
        · exact absurd (hpk hB0 x (huu ▸ hxu)) g3
        · exact (mem_ru.1 (heq ▸ mem_erase.2 ⟨huu, hu⟩)).2)
      (i1 := 5) (i2 := 8) i0 i1 (Or.inr (Or.inl ⟨rfl, rfl⟩))
    rw [hc2.2.2] at this
    omega
  obtain ⟨uc, huc⟩ := card_pos.1 (show 0 < (ru D b 3).card by omega)
  rw [mem_ru] at huc
  have hu3 := pe_uq h31 huc.1 huc.2
  have hne : uc ≠ uk := fun e => hk3 (e ▸ huc.2)
  have co3 : ∀ t : Fin 14, 3 ≠ t → t ∈ supp 14 D uc.1 →
      ∀ k ∈ ({11, 12} : Finset (Fin 14)), pos k ∈ sem_W 14 D t :=
    fun t ht htu => pe_co2 hK huc.1 huc.2 hu3 (by decide) ht htu

  have hR2 : (residualUnits 14 D b).card = 2 := by
    by_contra hR2
    have hB0 : Bzero 14 D = 0 := by omega
    have f3 := pe_ft hK hB0 {11, 12} hJ3 ⟨hH3, hK3⟩ (sem_mem_W.1 hH7).2.1
      (by rw [hc2.2.1]; omega)
    have hpc : ∀ t ∈ supp 14 D uc.1, t = 3 := by
      intro t ht
      by_contra hne'
      have a := co3 t (Ne.symm hne') ht
      exact hne' ((by decide : ∀ t : Fin 14, Adj 11 t → Adj 12 t → t = 3) t
        ((f3 11 (by decide) (by decide) t).1 (sem_mem_W.1 (a 11 (by decide))).2.1)
        ((f3 12 (by decide) (by decide) t).1 (sem_mem_W.1 (a 12 (by decide))).2.1))
    have hcard : (((residualUnits 14 D b).erase uc).erase uk).card ≤ 1 := by
      rw [card_erase_of_mem (mem_erase.2 ⟨Ne.symm hne, huk⟩), card_erase_of_mem huc.1]
      omega
    have hout : ∀ x : Fin 14, x ≠ 3 → x ≠ 7 → ∀ u ∈ residualUnits 14 D b,
        x ∈ supp 14 D u.1 → u ∈ ((residualUnits 14 D b).erase uc).erase uk :=
      fun x a3 a7 u hu hx => mem_erase.2 ⟨fun e => a7 (hpk hB0 x (e ▸ hx)),
        mem_erase.2 ⟨fun e => a3 (hpc x (e ▸ hx)), hu⟩⟩
    have key : ∀ x1 x2 i a : Fin 14, (i ∈ pe_I ∧ x1 ∉ pe_I ∧ x1 ≠ 3 ∧ x1 ≠ 7 ∧ x2 ≠ 3 ∧
        x2 ≠ 7 ∧ (hc_adjB i x1 = true ∧ hc_adjB i a = true ∧ x1 ≠ x2 ∧ x1 ≠ a ∧
          hc_adjB x2 a = false) ∧ ¬ Adj i x2) →
        (∀ t, t ∈ supp 14 D (src D (pos i)) ↔ Adj i t) →
        (ru D b x1).card ≠ 0 → (ru D b x2).card ≠ 0 → False := by
      intro x1 x2 i a hg hf n1 n2
      obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := hg
      obtain ⟨u1, hu1⟩ := card_pos.1 (Nat.pos_of_ne_zero n1)
      obtain ⟨u2, hu2⟩ := card_pos.1 (Nat.pos_of_ne_zero n2)
      rw [mem_ru] at hu1 hu2
      have h2 := hout x2 g5 g6 u2 hu2.1 hu2.2
      have hall : ∀ u ∈ residualUnits 14 D b, x1 ∈ supp 14 D u.1 → x2 ∈ supp 14 D u.1 :=
        fun u hu hx => card_le_one.1 hcard u (hout x1 g3 g4 u hu hx) u2 h2 ▸ hu2.2
      exact g8 ((hf x2).1 (pe_co hK (hin i g1) (hel x1 g2) hall
        ⟨hu1.2, hall u1 hu1.1 hu1.2⟩ g7))
    have l1 : (ru D b 4).card ≠ 0 ∨ (ru D b 10).card ≠ 0 := by
      by_contra hcon
      rw [not_or, not_not, not_not] at hcon
      exact pe_ll hK (x := 4) (y := 10) (z := 13) (i := 11) (j := 0) (by decide)
        hcon.1 hcon.2
    have l2 : (ru D b 5).card ≠ 0 ∨ (ru D b 9).card ≠ 0 := by
      by_contra hcon
      rw [not_or, not_not, not_not] at hcon
      exact pe_ll hK (x := 5) (y := 9) (z := 10) (i := 12) (j := 1) (by decide)
        hcon.1 hcon.2
    have f11 := f3 11 (by decide) (by decide)
    have f0 := f7 hB0 0 (by decide) (by decide)
    rcases l1 with n1 | n1 <;> rcases l2 with n2 | n2
    · exact key 4 5 11 3 (by decide) f11 n1 n2
    · exact key 4 9 11 3 (by decide) f11 n1 n2
    · exact key 10 5 0 7 (by decide) f0 n1 n2
    · exact key 10 9 0 7 (by decide) f0 n1 n2

  have hres : ({uc, uk} : Finset (Σ _ : ℕ, ℕ)) = residualUnits 14 D b :=
    eq_of_subset_of_card_le (fun u hu => by
      rcases mem_insert.1 hu with hu | hu
      · rw [hu]; exact huc.1
      · rw [mem_singleton.1 hu]; exact huk) (by rw [card_pair hne, hR2])
  have hρ : ∀ x : Fin 14, (ru D b x).card ≤
      (if x ∈ supp 14 D uc.1 then 1 else 0) + if x ∈ supp 14 D uk.1 then 1 else 0 :=
    fun x => by
      have := card_filter (fun u : Σ _ : ℕ, ℕ => x ∈ supp 14 D u.1) {uc, uk}
      rw [sum_pair hne, hres] at this
      exact this.le
  obtain ⟨F, hF1, hF2, -⟩ := sem_edge_slots hG h.1 hC (x := 4) (y := 10) (by decide)
  have P4 := pe_one hK (x := 4) (i := 11) {11, 12} {0, 1} (by decide) (co3 4 (by decide))
    (co7 4 (by decide)) (hρ 4) ⟨hF1, fun k hk => pe_np1 hpos hk (hel 10 (by decide)) hF2⟩
  have P10 := pe_one hK (x := 10) (i := 0) {0, 1} {11, 12} (by decide) (co7 10 (by decide))
    (co3 10 (by decide)) (by rw [Nat.add_comm]; exact hρ 10)
    ⟨hF2, fun k hk => pe_np2 hpos hk (hel 4 (by decide)) hF1⟩
  obtain ⟨e, he1, he2, -⟩ := sem_edge_slots hG h.1 hC (x := 4) (y := 13) (by decide)
  rcases P4 e he1 with h1 | h1
  · rw [h1] at he2
    obtain ⟨e', he', h4, h5⟩ := sem_hw_cover_free h hD (x := 10) (a := 7) (b := 13)
      (by decide) (by decide) (by decide)
    rcases P10 e' he' with h6 | h6
    · exact h5 (h6 ▸ (sem_mem_W.1 he2).2.1)
    · obtain ⟨k, hk, rfl⟩ := mem_image.1 h6
      exact h4 (sem_mem_W.1 (hJ7 k hk).2).2.1
  · obtain ⟨k, hk, rfl⟩ := mem_image.1 h1
    exact pe_np1 hpos (hJ3 k hk).1 (hel 13 (by decide)) he2 rfl

theorem elim_p10_mixed22 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h13 : totalSurplus 14 D ≤ 13) (hI : ineligSet 14 D = {0, 1, 11, 12}) : False := by
  by_cases hle : pe_bs D 7 ≤ pe_bs D 3
  · exact pe_core h hD h13 hI hle
  · obtain ⟨h1, h2, -, h4, -, -, -, h8⟩ :=
      heawood_relabel pe_tau (hc_isAut_of (by decide +kernel)) h hD
    have e1 := pe_bs_tr pe_tau h.1 3
    have e2 := pe_bs_tr pe_tau h.1 7
    rw [show pe_tau 3 = 7 from by decide] at e1
    rw [show pe_tau 7 = 3 from by decide] at e2
    exact pe_core h1 h2 (h4 ▸ h13) (by rw [h8, hI]; decide) (by omega)

end PeMixed

theorem heawood_lb_27 (C : Circuit) (hmono : Monotone2 C)
    (hC : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ HeawoodEdge x) :
    27 ≤ C.size := by
  by_contra hlt
  obtain ⟨D, h, hD, hlen, -, h13, -, -, -, hcanon⟩ :=
    heawood_wlog_canon C hmono hC (by omega)
  rcases canonI_by_card _ hcanon with ⟨-, hI⟩ | ⟨-, hI⟩ | ⟨-, hI | hI⟩ |
    ⟨-, hI | hI | hI | hI⟩ | ⟨-, hI | hI | hI⟩ | ⟨-, hI | hI⟩ | ⟨-, hI⟩
  · exact elim_p7 h hD hlen hI
  · exact elim_p8 h hD h13 hI
  · exact elim_p9_onesided h hD h13 hI
  · exact elim_p9_mixed h hD h13 hI
  · exact elim_p10_line h hD h13 hI
  · exact elim_p10_cap h hD h13 hI
  · exact elim_p10_mixed31 h hD h13 hI
  · exact elim_p10_mixed22 h hD h13 hI
  · exact elim_p11_nonconc h hD h13 hI
  · exact elim_p11_conc h hD h13 hI
  · exact elim_p11_mixed h hD h13 hI
  · exact elim_p12_same h hD h13 hI
  · exact elim_p12_mixed h hD h13 hI
  · exact elim_p13 h hD h13 hI

def pm14 : Fin 14 → Fin 14 := fun i => ([0, 1, 2, 3, 4, 5, 6, 7, 13, 12, 11, 10, 9, 8] : List (Fin 14)).getD i.val 0
def mp14 (i : ℕ) : ℕ := if h : i < 14 then (pm14 ⟨i, h⟩).val else i
def stp14 (w : List Bool) (g : Gate) : List Bool := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
theorem mp14_ge {i : ℕ} (h : 14 ≤ i) : mp14 i = i := by simp [mp14, Nat.not_lt.mpr h]
theorem mp14_lt {i : ℕ} (h : i < 14) : mp14 i < 14 := by rw [mp14, dif_pos h]; exact (pm14 ⟨i, h⟩).isLt
theorem fold14 (gs : List Gate) : ∀ w w' : List Bool, w.length = w'.length → 14 ≤ w.length →
    (∀ i, w'.getD (mp14 i) false = w.getD i false) →
    ∀ i, ((gs.map fun g => (⟨g.op, g.inputs.map mp14⟩ : Gate)).foldl stp14 w').getD (mp14 i) false = (gs.foldl stp14 w).getD i false := by
  induction gs with
  | nil => intro w w' _ _ h i; exact h i
  | cons g gs ih =>
    intro w w' hl h9 h i
    simp only [List.map_cons, List.foldl_cons]
    apply ih
    · simp [stp14, hl]
    · simp [stp14]; omega
    · intro j
      have hv : g.op.eval ((g.inputs.map mp14).map fun i => w'.getD i false) = g.op.eval (g.inputs.map fun i => w.getD i false) := by
        rw [List.map_map]
        congr 1
        apply List.map_congr_left
        intro a _
        exact h a
      simp only [stp14]
      rw [hv]
      rcases Nat.lt_trichotomy j w.length with hj | hj | hj
      · have hj' : mp14 j < w'.length := by
          by_cases h' : j < 14
          · have := mp14_lt h'; omega
          · rw [mp14_ge (by omega)]; omega
        have e := h j
        simp only [List.getD_eq_getElem?_getD] at e ⊢
        rw [List.getElem?_append_left hj', List.getElem?_append_left hj]
        exact e
      · subst hj
        rw [mp14_ge h9]
        simp [List.getD_eq_getElem?_getD, hl]
      · rw [mp14_ge (by omega)]
        rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
def FanoE (x : Fin 14 → Bool) : Prop := ∃ (a : Fin 7) (b : Fin 7), (a = b ∨ a = b + 1 ∨ a = b + 3) ∧ x (Fin.castAdd 7 a) = true ∧ x (Fin.natAdd 7 b) = true
theorem geo1 : ∀ a b : Fin 7, (a = b ∨ a = b + 1 ∨ a = b + 3) → ((pm14 (Fin.castAdd 7 a)).val, (pm14 (Fin.natAdd 7 b)).val) ∈ ([(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ)) := by decide +kernel
theorem geo2 : ∀ u v : Fin 14, (u.val, v.val) ∈ ([(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ)) → ∃ a b : Fin 7, (a = b ∨ a = b + 1 ∨ a = b + 3) ∧ pm14 (Fin.castAdd 7 a) = u ∧ pm14 (Fin.natAdd 7 b) = v := by decide +kernel
theorem fano27 (C : Circuit) (hm : Monotone2 C) (hc : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ FanoE x) : 27 ≤ C.size := by
  have key := heawood_lb_27 ⟨C.gates.map fun g => (⟨g.op, g.inputs.map mp14⟩ : Gate), mp14 C.output⟩ ?_ ?_
  · simpa [Circuit.size] using key
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    obtain ⟨a, b⟩ := hm g' hg'
    exact ⟨a, by simpa using b⟩
  · intro y
    have e : Circuit.eval ⟨C.gates.map fun g => (⟨g.op, g.inputs.map mp14⟩ : Gate), mp14 C.output⟩ (List.ofFn y) = C.eval (List.ofFn fun i => y (pm14 i)) := by
      refine fold14 C.gates (List.ofFn fun i => y (pm14 i)) (List.ofFn y) (by simp) (by simp) ?_ C.output
      intro i
      by_cases hi : i < 14
      · rw [mp14, dif_pos hi]
        interval_cases i <;> rfl
      · rw [mp14_ge (by omega), List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    rw [e, hc]
    constructor
    · rintro ⟨a, b, h, h1, h2⟩
      exact ⟨_, _, geo1 a b h, h1, h2⟩
    · rintro ⟨u, v, h, h1, h2⟩
      obtain ⟨a, b, hab, rfl, rfl⟩ := geo2 u v h
      exact ⟨a, b, hab, h1, h2⟩
theorem ao27 (C : Circuit) (hm : PEqualNP.TopForm.IsAO2 14 C) (hc : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ FanoE x) : 27 ≤ C.size :=
  fano27 C (fun g hg => ⟨by simpa using hm.1 g hg, le_of_eq (hm.2.2 g hg)⟩) hc
theorem op27 (C : Circuit) (hm : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ (a : ℕ) (b : ℕ), g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j) (hc : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ FanoE x) : 27 ≤ C.size := by
  refine fano27 C (fun g hg => ?_) hc
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hg
  obtain ⟨h1, a, b, h2, _⟩ := hm j g hj
  exact ⟨by simpa using h1, by simp [h2]⟩

end PEqualNP.Outside.L_meta_17589_aux

theorem PEqualNP.Outside.L_meta_17589 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)), x4 ∈ PEqualNP.CircuitLowerBounds.fanoLines x5 ∧ x3 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (7 : ℕ) x5) = Bool.true) → (27 : ℕ) ≤ x1.size := by
  intro C hm hc
  refine PEqualNP.Outside.L_meta_17589_aux.fano27 C hm (fun x => ?_)
  have key : ∀ a b : Fin 7, a ∈ PEqualNP.CircuitLowerBounds.fanoLines b ↔
      (a = b ∨ a = b + 1 ∨ a = b + 3) := by decide
  rw [hc x]
  simp only [PEqualNP.Outside.L_meta_17589_aux.FanoE, key]
