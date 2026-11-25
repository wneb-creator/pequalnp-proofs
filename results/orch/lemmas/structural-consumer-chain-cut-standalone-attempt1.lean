import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1479.ConsumerCut

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


/-- Gate operation: `true` is AND, `false` is OR. -/
def gop : Bool → Bool → Bool → Bool
  | true, a, b => a && b
  | false, a, b => a || b

@[local simp] theorem gop_true (a b : Bool) : gop true a b = (a && b) := rfl
@[local simp] theorem gop_false (a b : Bool) : gop false a b = (a || b) := rfl

/-- A binary DAG: gate `j` is `(isAnd, a, b)` and, with `n` inputs, drives wire `n + j`. -/
abbrev Dag := List (Bool × ℕ × ℕ)

def tag (D : Dag) (j : ℕ) : Bool := (D.getD j (false, 0, 0)).1
def opA (D : Dag) (j : ℕ) : ℕ := (D.getD j (false, 0, 0)).2.1
def opB (D : Dag) (j : ℕ) : ℕ := (D.getD j (false, 0, 0)).2.2

/-- One evaluation step: append the value of gate `g` read on the current wire list. -/
def wstep (w : List Bool) (g : Bool × ℕ × ℕ) : List Bool :=
  w ++ [gop g.1 (w.getD g.2.1 false) (w.getD g.2.2 false)]

/-- The wire list of `D` started from the wire list `w`. -/
def wl (D : Dag) (w : List Bool) : List Bool := D.foldl wstep w

/-- Value of wire `w` of `D` on input `x` (`false` beyond the last wire). -/
def val (D : Dag) {n : ℕ} (x : Fin n → Bool) (w : ℕ) : Bool :=
  (wl D (List.ofFn x)).getD w false

/-- Strict binary DAG on `n` inputs: both operands are earlier wires and they differ. -/
def Strict (n : ℕ) (D : Dag) : Prop :=
  ∀ j, j < D.length → opA D j < n + j ∧ opB D j < n + j ∧ opA D j ≠ opB D j

/-- The gates reading wire `w`. -/
def readers (D : Dag) (w : ℕ) : Finset ℕ :=
  (Finset.range D.length).filter (fun j => opA D j = w ∨ opB D j = w)

def fanout (D : Dag) (w : ℕ) : ℕ := (readers D w).card

/-- Every wire except the last one has a reader. -/
def Live (n : ℕ) (D : Dag) : Prop := ∀ w, w + 1 < n + D.length → 1 ≤ fanout D w

/-- Strict, live, nonempty; the output is the last wire `n + D.length - 1`. -/
def StrictLive (n : ℕ) (D : Dag) : Prop := Strict n D ∧ Live n D ∧ D ≠ []

/-- The output wire. -/
def outW (n : ℕ) (D : Dag) : ℕ := n + D.length - 1

/-- Singleton assignment. -/
def single {n : ℕ} (v : Fin n) : Fin n → Bool := fun i => decide (i = v)

/-- Singleton support of a wire. -/
def supp (n : ℕ) (D : Dag) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => val D (single v) w = true)

/-- Surplus carried by a set of wires. -/
def surplusOn (D : Dag) (K : Finset ℕ) : ℕ := ∑ w ∈ K, (fanout D w - 1)

/-- The wires other than the output. -/
def inner (n : ℕ) (D : Dag) : Finset ℕ := Finset.range (n + D.length - 1)

def totalSurplus (n : ℕ) (D : Dag) : ℕ := surplusOn D (inner n D)

def Bplus (n : ℕ) (D : Dag) : ℕ :=
  surplusOn D ((inner n D).filter (fun w => (supp n D w).Nonempty))

def Bzero (n : ℕ) (D : Dag) : ℕ :=
  surplusOn D ((inner n D).filter (fun w => ¬ (supp n D w).Nonempty))

/-- Branching wires. -/
def branchW (n : ℕ) (D : Dag) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => 2 ≤ fanout D w)

/-- Eligible labels: carried by some branching wire. -/
def eligSet (n : ℕ) (D : Dag) : Finset (Fin n) := (branchW n D).biUnion (supp n D)

def ineligSet (n : ℕ) (D : Dag) : Finset (Fin n) := Finset.univ \ eligSet n D

/-- Multiplicity-aware surplus units `⟨w, i⟩` with `i + 1 < fanout w`. -/
def units (n : ℕ) (D : Dag) : Finset (Σ _ : ℕ, ℕ) :=
  (inner n D).sigma (fun w => Finset.range (fanout D w - 1))

def unitsPlus (n : ℕ) (D : Dag) : Finset (Σ _ : ℕ, ℕ) :=
  (units n D).filter (fun u => (supp n D u.1).Nonempty)

def unitsOn (n : ℕ) (D : Dag) (K : Finset ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (units n D).filter (fun u => u.1 ∈ K)

/-- Arcs are operand positions `(gate, side)`; `false` is the first operand. -/
def arcs (D : Dag) : Finset (ℕ × Bool) := Finset.range D.length ×ˢ Finset.univ

def src (D : Dag) (e : ℕ × Bool) : ℕ := if e.2 = true then opB D e.1 else opA D e.1

def exitArcs (n : ℕ) (D : Dag) (K : Finset ℕ) : Finset (ℕ × Bool) :=
  (arcs D).filter (fun e => src D e ∈ K ∧ n + e.1 ∉ K)

def merges (n : ℕ) (D : Dag) (K : Finset ℕ) : Finset ℕ :=
  (Finset.range D.length).filter (fun j => n + j ∈ K ∧ opA D j ∈ K ∧ opB D j ∈ K)

def sources (n : ℕ) (K : Finset ℕ) : Finset ℕ := K.filter (fun w => w < n)

/-- Union carrier of a label set `T`. -/
def carrierT (n : ℕ) (D : Dag) (T : Finset (Fin n)) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => (supp n D w ∩ T).Nonempty)

/-- Difference carrier: wires carrying `x` and not `y`. -/
def carrierDiff (n : ℕ) (D : Dag) (x y : Fin n) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => x ∈ supp n D w ∧ y ∉ supp n D w)

/-- A choice of one pure branching carrier for every eligible label. -/
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

/-- The value of the gate `j` wire in terms of the wire list of the first `j` gates. -/
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

/-- Wires of an initial segment agree with the full wire list below its length. -/
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

/-- Values of an initial segment of a DAG. -/
theorem val_take (D : Dag) {n : ℕ} (x : Fin n → Bool) (k w : ℕ) (hw : w < n + k)
    (hk : k ≤ D.length) : val (D.take k) x w = val D x w := by
  unfold val
  exact wl_take_getD D _ k w (by simpa using hw) hk

/-- The gate equation of a strict DAG. -/
theorem val_gate {n : ℕ} {D : Dag} (hS : Strict n D) (x : Fin n → Bool) (j : ℕ)
    (hj : j < D.length) :
    val D x (n + j) = gop (tag D j) (val D x (opA D j)) (val D x (opB D j)) := by
  obtain ⟨ha, hb, -⟩ := hS j hj
  have h := wl_getD_gate D (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  unfold val
  rw [h, wl_take_getD D _ j _ (by simpa using ha) hj.le,
    wl_take_getD D _ j _ (by simpa using hb) hj.le]

/-- A strict DAG has exactly one solution of its input and gate equations. -/
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


/-- Symbolic reference: a Boolean constant or an emitted wire index. -/
abbrev Ref := Bool ⊕ ℕ

/-- Value of a symbolic reference on a wire list. -/
def refVal (W : List Bool) : Ref → Bool
  | Sum.inl b => b
  | Sum.inr k => W.getD k false

/-- Stage-dependent lookup: an index not yet mapped reads constant false. -/
def na_look (m : List Ref) (i : ℕ) : Ref := m.getD i (Sum.inl false)

/-- Two-operand simplifier: a reference, or two distinct emitted wires needing a gate. -/
def na_comb (t : Bool) : Ref → Ref → Ref ⊕ (ℕ × ℕ)
  | Sum.inl a, r => Sum.inl (if a = t then r else Sum.inl a)
  | Sum.inr i, Sum.inl b => Sum.inl (if b = t then Sum.inr i else Sum.inl b)
  | Sum.inr i, Sum.inr j => if i = j then Sum.inl (Sum.inr i) else Sum.inr (i, j)

def na_isAnd : GateOp → Bool
  | GateOp.and => true
  | _ => false

/-- One translation step for an official gate; the state is (map of old wires, emitted DAG). -/
def na_step (n : ℕ) (st : List Ref × Dag) (g : Gate) : List Ref × Dag :=
  match g.inputs with
  | [] => (st.1 ++ [Sum.inl (na_isAnd g.op)], st.2)
  | [a] => (st.1 ++ [na_look st.1 a], st.2)
  | a :: b :: _ =>
    match na_comb (na_isAnd g.op) (na_look st.1 a) (na_look st.1 b) with
    | Sum.inl r => (st.1 ++ [r], st.2)
    | Sum.inr p => (st.1 ++ [Sum.inr (n + st.2.length)], st.2 ++ [(na_isAnd g.op, p.1, p.2)])

/-- A reference is valid below the bound `B`. -/
def na_ok (B : ℕ) : Ref → Prop
  | Sum.inl _ => True
  | Sum.inr k => k < B

/-- Structural invariant of the translation state. -/
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

/-- One step keeps the invariant, emits at most one gate, and tracks the official fold. -/
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

/-- The whole translation fold keeps the invariant and tracks the official wire list. -/
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

/-- Translation: a constant, an input projection, or a strict DAG no larger than `C`. -/
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

/-- Shift an operand index down past a deleted wire `c`. -/
def na_sh (c a : ℕ) : ℕ := if c < a then a - 1 else a

/-- Inverse shift: the old index of a new wire or gate. -/
def na_up (c w : ℕ) : ℕ := if w < c then w else w + 1

/-- Delete gate `j` and shift larger operand indices down by one. -/
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

/-- Liveness by minimality: a strict DAG for a function with all inputs essential can be
replaced by a strict live one that is no larger. -/
theorem exists_strictLive_of_strict {n : ℕ} (F : (Fin n → Bool) → Bool)
    (hess : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ k, k ≠ i → x k = y k) ∧ F x ≠ F y)
    (D : Dag) (hS : Strict n D) (hne : D ≠ [])
    (hD : ∀ x : Fin n → Bool, val D x (outW n D) = F x) :
    ∃ D' : Dag, StrictLive n D' ∧ D'.length ≤ D.length ∧
      ∀ x : Fin n → Bool, val D' x (outW n D') = F x :=
  na_live_aux F hess D.length D rfl hS hne hD

/-- The bridge from the official model to strict live binary DAGs. -/
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

/-- Fanout counts the operand positions reading the wire. -/
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

/-- The global identity `B = s - n + 1`, in addition form. -/
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

/-- Every wire has a reader path to the output. -/
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


/-- `e_K + M_K = sources_K + B_K` for a wire set missing the output in which every gate
has an operand. -/
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

/-- Flow for the union carrier of a label set. -/
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

/-- Flow for the carrier of `x` without `y`. -/
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

/-- `p ≤ B_+`. -/
theorem elig_le_Bplus (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b) :
    (eligSet n D).card ≤ Bplus n D := by
  rw [← card_reserved b hb, ← card_unitsPlus]
  exact Finset.card_le_card (reserved_subset hS b hb)

theorem card_residual (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b) :
    (residualUnits n D b).card + (eligSet n D).card = Bplus n D := by
  rw [← card_reserved b hb, ← card_unitsPlus]
  exact Finset.card_sdiff_add_card_eq_card (reserved_subset hS b hb)

/-- `B_T = |T ∩ S| +` the number of residual units carrying a label of `T`. -/
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

/-- `B_T ≤ |T ∩ S| + (B_+ - p)`, in addition form. -/
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


/-- The action of `σ` on wires: input wires are permuted, gate wires are fixed. -/
def liftP {n : ℕ} (σ : Equiv.Perm (Fin n)) (w : ℕ) : ℕ :=
  if h : w < n then (σ ⟨w, h⟩).val else w

/-- The DAG with every operand moved by `liftP σ`. -/
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

/-- The relabelled DAG on `x` has the values of the old DAG on `x ∘ σ`. -/
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

/-- Reindexing a filtered sum over an initial range by `liftP σ`. -/
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

/-- Surplus on a filtered set of inner wires is preserved when the filters correspond. -/
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


/-- The official 21 oriented edges (point, line), in the official order. -/
def edgeList : List (ℕ × ℕ) :=
  [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11),
    (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]

/-- The official Heawood edge predicate on an assignment. -/
def HeawoodEdge (x : Fin 14 → Bool) : Prop :=
  ∃ u v : Fin 14, (u.val, v.val) ∈ edgeList ∧ x u = true ∧ x v = true

/-- Undirected Heawood adjacency. -/
abbrev Adj (u v : Fin 14) : Prop := (u.val, v.val) ∈ edgeList ∨ (v.val, u.val) ∈ edgeList

/-- Fano incidence of point `p` and line `l`; line `l` is the official vertex `l + 7`. -/
def inc (p l : Fin 7) : Bool :=
  (([11, 69, 98, 49, 88, 44, 22] : List ℕ).getD l.val 0).testBit p.val

/-- Fast Boolean adjacency through neighbour bit masks. -/
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

/-- The explicit perfect matching. -/
def matching : List (Fin 14 × Fin 14) :=
  [(0, 7), (1, 13), (2, 8), (3, 12), (4, 11), (5, 10), (6, 9)]

/-- The matching partner of a vertex. -/
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

/-- Automorphisms of the Heawood graph. -/
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

/-- A vertex map given by a table of images. -/
def hc_ofList (l : List ℕ) (v : Fin 14) : Fin 14 := Fin.ofNat 14 (l.getD v.val 0)

/-- The duality (a polarity): swaps the point side and the line side. -/
def dualPerm : Equiv.Perm (Fin 14) :=
  ⟨hc_ofList [13, 8, 7, 12, 10, 11, 9, 2, 1, 6, 4, 5, 3, 0],
    hc_ofList [13, 8, 7, 12, 10, 11, 9, 2, 1, 6, 4, 5, 3, 0],
    by intro x; revert x; decide +kernel, by intro x; revert x; decide +kernel⟩

theorem dualPerm_isAut : IsAut dualPerm := hc_isAut_of (by decide +kernel)

/-- A collineation of order seven: the cyclic shift of the points. -/
def collPerm : Equiv.Perm (Fin 14) :=
  ⟨hc_ofList [1, 2, 3, 4, 5, 6, 0, 13, 7, 8, 9, 10, 11, 12],
    hc_ofList [6, 0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 13, 7],
    by intro x; revert x; decide +kernel, by intro x; revert x; decide +kernel⟩

theorem collPerm_isAut : IsAut collPerm := hc_isAut_of (by decide +kernel)

/-- The fourteen canonical independent sets, by decreasing size. -/
def canonI : List (Finset (Fin 14)) :=
  [{0, 1, 2, 3, 4, 5, 6}, {0, 1, 2, 3, 4, 5}, {0, 1, 2, 3, 4}, {0, 1, 2, 5, 11}, {0, 1, 2, 3},
    {0, 1, 2, 5}, {0, 1, 2, 11}, {0, 1, 11, 12}, {0, 1, 2}, {0, 1, 3}, {0, 1, 11}, {0, 1},
    {0, 9}, {0}]

/-- The empty set followed by the canonical sets. -/
def hc_rep (n : Fin 15) : Finset (Fin 14) := ((∅ : Finset (Fin 14)) :: canonI).getD n.val ∅

theorem hc_rep_of_mem {R : Finset (Fin 14)} (h : R ∈ canonI) :
    ∃ n : Fin 15, n ≠ 0 ∧ hc_rep n = R := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp h
  have hi' : i < 14 := hi
  refine ⟨⟨i + 1, by omega⟩, by simp [Fin.ext_iff], ?_⟩
  show ((∅ : Finset (Fin 14)) :: canonI).getD (i + 1) ∅ = canonI[i]
  rw [List.getD_cons_succ]; exact List.getD_eq_getElem _ _ hi

/-- Independence through the fast adjacency. -/
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

/-- Twenty explicit automorphisms covering every one-vertex extension of a canonical set. -/
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

/-- Witness table: row `n`, column `w` is the automorphism index for `insert w (hc_rep n)`. -/
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

/-- Every nonempty independent set is an automorphic image of a canonical one. -/
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


/-- `D` computes the official Heawood edge function at its last wire. -/
def Correct (D : Dag) : Prop :=
  ∀ x : Fin 14 → Bool, val D x (outW 14 D) = true ↔ HeawoodEdge x

/-- The official bridge: every `Monotone2` circuit for the Heawood edge function yields a
strict live constant-free binary DAG with at most as many gates. -/
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

/-- The output of a correct DAG carries no singleton label. -/
theorem heawood_supp_out {D : Dag} (hD : Correct D) : supp 14 D (outW 14 D) = ∅ :=
  Finset.eq_empty_iff_forall_notMem.2
    (fun v hv => heawood_not_single v ((hD _).1 (mem_supp.1 hv)))

/-- Relabelling the inputs by a Heawood automorphism keeps every counted quantity. -/
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

/-- Without loss of generality the ineligible set is one of the fourteen canonical sets. -/
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

/-- Fourteen live inputs: `B = s - 13`, in addition form. -/
theorem heawood_budget {D : Dag} (h : StrictLive 14 D) (hlen : D.length ≤ 26) :
    totalSurplus 14 D + 13 = D.length ∧ totalSurplus 14 D ≤ 13 := by
  have := surplus_identity h
  omega

/-- `7 ≤ p ≤ B_+ ≤ B ≤ 13` for at most 26 gates, given the pure first branches and the
vertex-cover property of the eligible set. -/
theorem heawood_p_bounds {D : Dag} (h : StrictLive 14 D) (hlen : D.length ≤ 26)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b) (hcov : IsCover (eligSet 14 D)) :
    7 ≤ (eligSet 14 D).card ∧ (eligSet 14 D).card ≤ Bplus 14 D ∧
      Bplus 14 D ≤ totalSurplus 14 D ∧ totalSurplus 14 D ≤ 13 :=
  ⟨cover_card_ge_seven _ hcov, elig_le_Bplus h.1 b hb, Bplus_le_total 14 D,
    (heawood_budget h hlen).2⟩

/-- Under the same hypotheses some input is ineligible, and at most seven are. -/
theorem heawood_inelig_bounds {D : Dag} (h : StrictLive 14 D) (hlen : D.length ≤ 26)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b) (hcov : IsCover (eligSet 14 D)) :
    (ineligSet 14 D).Nonempty ∧ (ineligSet 14 D).card ≤ 7 := by
  obtain ⟨h7, hp, hB, h13⟩ := heawood_p_bounds h hlen b hb hcov
  have hc := inelig_card_add 14 D
  exact ⟨Finset.card_pos.1 (by omega), by omega⟩


/-- Edge function of a graph relation on an assignment. -/
def sem_Edge {n : ℕ} (G : Fin n → Fin n → Prop) (x : Fin n → Bool) : Prop :=
  ∃ u v : Fin n, G u v ∧ x u = true ∧ x v = true

/-- `D` computes the edge function of `G` at its last wire. -/
def sem_Comp (n : ℕ) (G : Fin n → Fin n → Prop) (D : Dag) : Prop :=
  ∀ x : Fin n → Bool, val D x (outW n D) = true ↔ sem_Edge G x

/-- Graph hypotheses: symmetric, irreflexive, separated neighbourhoods, and for every
vertex a neighbour different from any given vertex. -/
def sem_Gr {n : ℕ} (G : Fin n → Fin n → Prop) : Prop :=
  (∀ u v, G u v → G v u) ∧ (∀ u, ¬ G u u) ∧ (∀ v w, v ≠ w → ∃ z, G v z ∧ ¬ G w z) ∧
    (∀ u v, ∃ a, G u a ∧ a ≠ v)

/-- Reader step: the gate wire `b` reads the wire `a`. -/
def sem_step (n : ℕ) (D : Dag) (a b : ℕ) : Prop :=
  b < n + D.length ∧ n ≤ b ∧ (opA D (b - n) = a ∨ opB D (b - n) = a)

/-- The assignment with exactly `u` and `z` true. -/
def sem_two {n : ℕ} (u z : Fin n) : Fin n → Bool := fun i => decide (i = u) || decide (i = z)

/-- The assignment `x` with `v` switched on. -/
def sem_ins {n : ℕ} (v : Fin n) (x : Fin n → Bool) : Fin n → Bool := fun i => decide (i = v) || x i

/-- The indicator assignment of a finite set. -/
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

/-- A wire carrying `u` is true on every assignment containing `u`. -/
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


/-- If two assignments differ only at `v` and change the wire `w`, a reader path of changed
wires leads from the input `v` to `w`. -/
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

/-- `b` dominates the wire `v`: it is `v` itself or lies on every reader path from `v` to
the output. -/
def sem_Dom (n : ℕ) (D : Dag) (b v : ℕ) : Prop :=
  b = v ∨ ¬ Relation.ReflTransGen (fun a c => sem_step n D a c ∧ c ≠ b) v (outW n D)

/-- Assignments differing only at `v` and agreeing at a dominating wire agree at the output. -/
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

/-- Reader paths through wires with exactly one reader. -/
def sem_Chain (n : ℕ) (D : Dag) (a b : ℕ) : Prop :=
  Relation.ReflTransGen (fun a c => sem_step n D a c ∧ fanout D a = 1) a b

/-- The end of a single-reader chain dominates its start. -/
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

/-- A carrier of `v` all of whose earlier carriers have at most one reader is reached from
the input `v` through single-reader carriers. -/
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

/-- The output of a circuit for an edge function carries no singleton label. -/
theorem sem_supp_out (hG : sem_Gr G) (hC : sem_Comp n G D) : supp n D (outW n D) = ∅ :=
  Finset.eq_empty_iff_forall_notMem.2
    (fun v hv => sem_single_no_edge hG v ((hC _).1 (mem_supp.1 hv)))

/-- Dominator purity: a wire dominating the input `v` carries no other singleton label. -/
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

/-- The first branching carrier of an eligible label: pure, and reached from the input
through single-reader wires. -/
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

/-- A choice of first branches: pure, branching, and on the single-reader chain. -/
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

/-- Every carrier of an ineligible label is reached through single-reader wires. -/
theorem sem_inelig_chain (hS : Strict n D) {v : Fin n} (hv : v ∈ ineligSet n D) {w : ℕ}
    (hw : v ∈ supp n D w) : sem_Chain n D v.val w :=
  sem_carrier_chain hS v w hw (fun u _ hu => mem_ineligSet.mp hv u hu)

/-- Every carrier of an ineligible label is pure. -/
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


/-- Every edge `uv` has an AND gate true on `{u, v}`, carrying neither endpoint, whose two
operands carry `u` without `v` and `v` without `u`. -/
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


/-- An ineligible label has one consuming position: an AND gate with empty support, a pure
operand on the label side, and every neighbour carried by the opposite operand. Its carrier
has no internal merge. -/
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

/-- Every gate carrying an ineligible label is an OR. -/
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

/-- The eligible labels form a vertex cover. -/
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

/-- Exposure: for an independent set `A` and a label `x` with a neighbour in `A`, some AND
position consuming `x` has an operand whose whole singleton support misses `A`. -/
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

/-- First production of a projected mask `M` with at least two labels: it happens at a
gate that is an internal merge of the union carrier of `T`. An AND has two strictly
larger parent masks; an OR has two nonempty strictly smaller parent masks with union `M`. -/
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

/-- Every correct Heawood DAG has a pure first-branch choice. -/
theorem exists_pureBranch {D : Dag} (h : StrictLive 14 D) (hD : Correct D) :
    ∃ b : Fin 14 → ℕ, PureBranch 14 D b :=
  sem_exists_pureBranch sem_heawood_gr h.1 (sem_heawood_comp hD)

/-- The eligible labels of a correct Heawood DAG form a vertex cover. -/
theorem elig_isCover {D : Dag} (h : StrictLive 14 D) (hD : Correct D) :
    IsCover (eligSet 14 D) :=
  fun _ _ huv => sem_elig_cover sem_heawood_gr h (sem_heawood_comp hD) huv

/-- From an official circuit of size at most 26 to a canonical strict live DAG. -/
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


/-- The consumption code of `x`: the operand positions carrying `x` at gates that do not. -/
def sem_W (n : ℕ) (D : Dag) (x : Fin n) : Finset (ℕ × Bool) := exitArcs n D (carrierT n D {x})

/-- The opposite operand position at the same gate. -/
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

/-- A consuming gate is an AND. -/
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


end SemCodes
end PEqualNP.Outside.L_meta_1479.ConsumerCut


namespace PEqualNP.Outside.L_meta_1479.ConsumerCut

lemma single_reader_path_le {n : ℕ} {D : Dag} (hS : Strict n D) {a b : ℕ}
    (path : Relation.ReflTransGen (sem_step n D) a b) : a ≤ b := by
  induction path with
  | refl => rfl
  | tail path step ih => exact Nat.le_trans ih (Nat.le_of_lt (sem_step_lt hS step))

lemma single_reader_chain_le {n : ℕ} {D : Dag} (hS : Strict n D) {a b : ℕ}
    (path : sem_Chain n D a b) : a ≤ b :=
  single_reader_path_le hS (sem_rtg_mono (fun _ _ h => h.1) path)

lemma single_reader_other_unreachable {n : ℕ} {D : Dag} (hS : Strict n D)
    {v a b c : ℕ} (chain : sem_Chain n D v a)
    (last : sem_step n D a b) (one : fanout D a = 1)
    (other : sem_step n D c b) (different : c ≠ a) :
    ¬ Relation.ReflTransGen (sem_step n D) v c := by
  induction chain using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro reach
    rcases Relation.ReflTransGen.cases_head reach with equal | ⟨z,first,rest⟩
    · exact different equal.symm
    · have same : b = z := sem_step_unique last first one
      have le := single_reader_path_le hS rest
      have lt := sem_step_lt hS other
      omega
  | @head start next first rest ih =>
    intro reach
    rcases Relation.ReflTransGen.cases_head reach with equal | ⟨z,initial,remaining⟩
    · have direct : sem_step n D start b := by simpa [equal] using other
      have same : next = b := sem_step_unique first.1 direct first.2
      have le := single_reader_chain_le hS rest
      have lt := sem_step_lt hS last
      omega
    · have same : next = z := sem_step_unique first.1 initial first.2
      subst z
      exact ih remaining

lemma single_reader_chain_hits {n : ℕ} {D : Dag} (hS : Strict n D)
    {a b : ℕ} (chain : sem_Chain n D a b) (P : ℕ → Prop) :
    ∀ w, Relation.ReflTransGen (fun u v => sem_step n D u v ∧ P v) a w →
      P a → b ≤ w → P b := by
  induction chain using Relation.ReflTransGen.head_induction_on with
  | refl => intro w path start bound; exact start
  | @head a next step rest ih =>
    intro w path start bound
    rcases Relation.ReflTransGen.cases_head path with equal | ⟨z,first,remaining⟩
    · have increasing := sem_step_lt hS step.1
      have restLe := single_reader_chain_le hS rest
      omega
    · have same : next = z := sem_step_unique step.1 first.1 step.2
      subst z
      exact ih w remaining first.2 bound

end PEqualNP.Outside.L_meta_1479.ConsumerCut

namespace PEqualNP.Outside.L_meta_1479.ConsumerCut

lemma consuming_changed_path {n : Nat} {D : Dag} (hS : Strict n D)
    (x y : Fin n → Bool) (i : Fin n)
    (inputs : ∀ k, k ≠ i → x k = y k) (target : Nat)
    (changed : val D x target ≠ val D y target) (absent : i ∉ supp n D target) :
    ∃ e ∈ sem_W n D i, val D x (n+e.1) ≠ val D y (n+e.1) ∧
      Relation.ReflTransGen (fun a b => sem_step n D a b ∧ val D x b ≠ val D y b)
        (n+e.1) target := by
  have first : ∀ {a b : Nat},
      Relation.ReflTransGen (fun a b => sem_step n D a b ∧ val D x b ≠ val D y b) a b →
      i ∈ supp n D a → i ∉ supp n D b →
      ∃ e ∈ sem_W n D i, val D x (n+e.1) ≠ val D y (n+e.1) ∧
        Relation.ReflTransGen (fun a b => sem_step n D a b ∧ val D x b ≠ val D y b)
          (n+e.1) b := by
    intro a b path
    induction path using Relation.ReflTransGen.head_induction_on with
    | refl => intro present absent; exact False.elim (absent present)
    | @head a c step rest ih =>
      intro present absent
      by_cases next : i ∈ supp n D c
      · exact ih next absent
      · obtain ⟨j,s,hj,rfl,source⟩ := sem_step_iff.mp step.1
        refine ⟨(j,s),sem_mem_W.mpr ⟨hj,?_,next⟩,step.2,rest⟩
        rw [source]
        exact present
  apply first (sem_changed_path hS x y i inputs target changed) _ absent
  rw [supp_input D i]
  exact Finset.mem_singleton_self i

end PEqualNP.Outside.L_meta_1479.ConsumerCut

namespace PEqualNP.Outside.L_meta_1479.ConsumerCut

lemma consumer_chain_cut {n : Nat} {D : Dag} (hS : Strict n D)
    (i u : Fin n) (e : Nat × Bool) (he : e ∈ sem_W n D i)
    (empty : supp n D (src D (sem_bar e)) = ∅)
    (g barrier : Nat)
    (two : ∀ f ∈ sem_W n D i, f.1 = g ∨ f.1 = e.1)
    (chain : sem_Chain n D (n+g) barrier)
    (same : val D (single u) barrier = val D (sem_ins i (single u)) barrier) :
    ∀ target, barrier ≤ target → i ∉ supp n D target →
      val D (single u) target = val D (sem_ins i (single u)) target := by
  have inputs := sem_ins_agree i (single u)
  have blocked : ∀ target, barrier ≤ target →
      val D (single u) (n+g) ≠ val D (sem_ins i (single u)) (n+g) →
      Relation.ReflTransGen (fun a b => sem_step n D a b ∧
        val D (single u) b ≠ val D (sem_ins i (single u)) b) (n+g) target → False := by
    intro target bound changed path
    exact (single_reader_chain_hits hS chain
      (fun w => val D (single u) w ≠ val D (sem_ins i (single u)) w)
      target path changed bound) same
  have hj := (sem_mem_W.mp he).1
  have childZero : val D (single u) (src D (sem_bar e)) = false := by
    cases value : val D (single u) (src D (sem_bar e)) with
    | false => rfl
    | true =>
      have member := mem_supp.mpr value
      rw [empty] at member
      exact False.elim (Finset.notMem_empty u member)
  have parentPath : val D (single u) (n+e.1) ≠ val D (sem_ins i (single u)) (n+e.1) →
      (val D (single u) (n+g) ≠ val D (sem_ins i (single u)) (n+g)) ∧
        Relation.ReflTransGen (fun a b => sem_step n D a b ∧
          val D (single u) b ≠ val D (sem_ins i (single u)) b) (n+g) (n+e.1) := by
    intro parentChanged
    have childChanged : val D (single u) (src D (sem_bar e)) ≠
        val D (sem_ins i (single u)) (src D (sem_bar e)) := by
      intro childSame
      have zero : ∀ x : Fin n → Bool, val D x (src D (sem_bar e)) = false →
          val D x (n+e.1) = false := by
        intro x hx
        rw [val_gate hS x e.1 hj,sem_W_and hS he]
        obtain ⟨j,s⟩ := e
        cases s <;> simp only [sem_bar,src,Bool.not_false,Bool.not_true,ite_true,
          Bool.false_eq_true,ite_false] at hx ⊢ <;> simp [gop,hx]
      exact parentChanged ((zero _ childZero).trans
        (zero _ (childSame.symm.trans childZero)).symm)
    obtain ⟨f,hf,changed,path⟩ := consuming_changed_path hS (single u)
      (sem_ins i (single u)) i inputs (src D (sem_bar e)) childChanged
      (by rw [empty]; exact Finset.notMem_empty i)
    rcases two f hf with fromG | fromE
    · have initial : val D (single u) (n+g) ≠ val D (sem_ins i (single u)) (n+g) := by
        simpa only [fromG] using changed
      have toChild : Relation.ReflTransGen (fun a b => sem_step n D a b ∧
          val D (single u) b ≠ val D (sem_ins i (single u)) b)
          (n+g) (src D (sem_bar e)) := by simpa only [fromG] using path
      exact ⟨initial,Relation.ReflTransGen.tail toChild ⟨sem_step_src hj (!e.2),parentChanged⟩⟩
    · have backward := sem_rtg_le hS (fun _ _ step => step.1) path
      have before := sem_src_lt hS hj (!e.2)
      change src D (sem_bar e) < n+e.1 at before
      omega
  intro target bound absent
  by_contra changed
  obtain ⟨f,hf,initial,path⟩ := consuming_changed_path hS (single u)
    (sem_ins i (single u)) i inputs target changed absent
  rcases two f hf with fromG | fromE
  · apply blocked target bound
    · simpa only [fromG] using initial
    · simpa only [fromG] using path
  · have changedE : val D (single u) (n+e.1) ≠ val D (sem_ins i (single u)) (n+e.1) := by
      simpa only [fromE] using initial
    obtain ⟨changedG,toE⟩ := parentPath changedE
    have fromEPath : Relation.ReflTransGen (fun a b => sem_step n D a b ∧
        val D (single u) b ≠ val D (sem_ins i (single u)) b) (n+e.1) target := by
      simpa only [fromE] using path
    exact blocked target bound changedG (toE.trans fromEPath)

lemma consumer_barrier_true {n : Nat} {D : Dag} (hS : Strict n D)
    (i u : Fin n) (e : Nat × Bool) (he : e ∈ sem_W n D i)
    (empty : supp n D (src D (sem_bar e)) = ∅)
    (g barrier : Nat)
    (two : ∀ f ∈ sem_W n D i, f.1 = g ∨ f.1 = e.1)
    (chain : sem_Chain n D (n+g) barrier)
    (target : Nat) (after : barrier ≤ target) (absent : i ∉ supp n D target)
    (baseZero : val D (single u) target = false)
    (positive : val D (sem_ins i (single u)) target = true) :
    val D (sem_ins i (single u)) barrier = true := by
  cases value : val D (sem_ins i (single u)) barrier with
  | true => rfl
  | false =>
    have baseFalse : val D (single u) barrier = false := by
      cases base : val D (single u) barrier with
      | false => rfl
      | true =>
        have raised := val_mono hS (single u) (sem_ins i (single u))
          (sem_ins_ge i (single u)) barrier base
        rw [value] at raised
        exact False.elim (Bool.noConfusion raised)
    have same := consumer_chain_cut hS i u e he empty g barrier two chain
      (baseFalse.trans value.symm) target after absent
    rw [baseZero,positive] at same
    exact False.elim (Bool.noConfusion same)

end PEqualNP.Outside.L_meta_1479.ConsumerCut
