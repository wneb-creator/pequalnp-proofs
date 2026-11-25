import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9777_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-! ## Core: strict binary DAGs, evaluation, and the shared definitions -/

/-- Gate operation: `true` is AND, `false` is OR. -/
def gop : Bool → Bool → Bool → Bool
  | true, a, b => a && b
  | false, a, b => a || b

@[simp] theorem gop_true (a b : Bool) : gop true a b = (a && b) := rfl
@[simp] theorem gop_false (a b : Bool) : gop false a b = (a || b) := rfl

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

/-! ### Evaluation lemmas -/

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

/-! ## Block A: official Monotone2 circuits to strict live binary DAGs -/

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

/-! ## Block B: surplus identity, supports, carrier flow, units -/

section SurplusFlow

variable {n : ℕ} {D : Dag}

theorem sb_mem_inner {w : ℕ} : w ∈ inner n D ↔ w + 1 < n + D.length := by
  unfold inner; rw [Finset.mem_range]; omega

theorem sb_src_false (j : ℕ) : src D (j, false) = opA D j := by simp [src]

theorem sb_src_true (j : ℕ) : src D (j, true) = opB D j := by simp [src]

/-! ### Fanout and the global surplus identity -/

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

/-! ### Semantics of singleton supports -/

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

/-! ### Carrier flow -/

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

/-! ### Multiplicity-aware surplus units -/

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

/-! ### Eligible labels and reserved units -/

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

/-! ## Block T: transport along a permutation of the input labels -/

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



/-! ## Block C: 14-vertex bipartite girth-6 geometry (`L-meta-9774`) and independent sets up to automorphism -/

def edgeList : List (ℕ × ℕ) :=
  [(0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]

def G14Edge (x : Fin 14 → Bool) : Prop :=
  ∃ u v : Fin 14, (u.val, v.val) ∈ edgeList ∧ x u = true ∧ x v = true

abbrev Adj (u v : Fin 14) : Prop :=
  (u.val, v.val) ∈ edgeList ∨ (v.val, u.val) ∈ edgeList

def adjBits (u : Fin 14) : ℕ :=
  match u.val with
  | 0 => 1280 | 1 => 8832 | 2 => 8448 | 3 => 6272 | 4 => 11264 | 5 => 5632 | 6 => 2816 | 7 => 10 | 8 => 69 | 9 => 98 | 10 => 49 | 11 => 88 | 12 => 40 | _ => 22

def hc_adjB (u v : Fin 14) : Bool := (adjBits u).testBit v.val

theorem hc_adjB_iff : ∀ u v : Fin 14, hc_adjB u v = true ↔ Adj u v := by
  decide +kernel

theorem sem_adjB_false {u v : Fin 14} : hc_adjB u v = false ↔ ¬ Adj u v := by
  rw [← hc_adjB_iff]; cases hc_adjB u v <;> decide

theorem adj_symm {u v : Fin 14} (h : Adj u v) : Adj v u := h.symm

theorem adj_irrefl (u : Fin 14) : ¬ Adj u u := by
  revert u; decide +kernel

theorem g14Edge_iff_adj (x : Fin 14 → Bool) :
    G14Edge x ↔ ∃ u v : Fin 14, Adj u v ∧ x u = true ∧ x v = true := by
  constructor
  · rintro ⟨u, v, huv, hx, hy⟩; exact ⟨u, v, Or.inl huv, hx, hy⟩
  · rintro ⟨u, v, huv | hvu, hx, hy⟩
    · exact ⟨u, v, huv, hx, hy⟩
    · exact ⟨v, u, hvu, hy, hx⟩

def g14_nbB (v : Fin 14) : Finset (Fin 14) :=
  Finset.univ.filter (fun u => hc_adjB v u = true)

def sem_g14_nb (v : Fin 14) : Finset (Fin 14) := g14_nbB v

theorem g14_nb_eq (v : Fin 14) : sem_g14_nb v = g14_nbB v := rfl

theorem g14_mem_nb {i a : Fin 14} : a ∈ sem_g14_nb i ↔ Adj i a := by
  simp only [sem_g14_nb, g14_nbB, Finset.mem_filter, Finset.mem_univ, true_and, hc_adjB_iff]

theorem degree_two_or_three : ∀ v : Fin 14, (g14_nbB v).card = 2 ∨ (g14_nbB v).card = 3 := by
  decide +kernel

theorem common_nbr_le_one : ∀ u v : Fin 14, u ≠ v →
    (g14_nbB u ∩ g14_nbB v).card ≤ 1 := by
  decide +kernel

theorem sup_g14_inter (i j : Fin 14) (hij : i ≠ j) (P : Finset (Fin 14)) :
    (sem_g14_nb i ∩ (sem_g14_nb j ∩ P)).card ≤ 1 := by
  have hsub : sem_g14_nb i ∩ (sem_g14_nb j ∩ P) ⊆ g14_nbB i ∩ g14_nbB j := by
    intro x hx
    rw [Finset.mem_inter, Finset.mem_inter] at hx
    exact Finset.mem_inter.2 ⟨hx.1, hx.2.1⟩
  exact (Finset.card_le_card hsub).trans (common_nbr_le_one i j hij)

theorem nbr_diff_exists : ∀ u v : Fin 14, u ≠ v → ∃ z : Fin 14, Adj u z ∧ ¬ Adj v z := by
  have h : ∀ u v : Fin 14, u ≠ v → ∃ z : Fin 14, hc_adjB u z = true ∧ hc_adjB v z = false := by
    decide +kernel
  intro u v huv
  obtain ⟨z, h1, h2⟩ := h u v huv
  exact ⟨z, (hc_adjB_iff u z).1 h1, sem_adjB_false.1 h2⟩

theorem g14_nb_inj {i j : Fin 14} (h : sem_g14_nb i = sem_g14_nb j) : i = j := by
  by_contra hne
  obtain ⟨z, hiz, hjz⟩ := nbr_diff_exists i j hne
  have h1 : z ∈ sem_g14_nb i := g14_mem_nb.2 hiz
  rw [h, g14_mem_nb] at h1
  exact hjz h1

def hc_mate (v : Fin 14) : Fin 14 :=
  match v.val with
  | 0 => 10 | 1 => 9 | 2 => 13 | 3 => 7 | 4 => 11 | 5 => 12 | 6 => 8 | 7 => 3 | 8 => 6 | 9 => 1 | 10 => 0 | 11 => 4 | 12 => 5 | _ => 2

theorem hc_match2 : ∀ v : Fin 14, hc_adjB v (hc_mate v) = true ∧ hc_mate (hc_mate v) = v := by
  decide +kernel

def IsCover (S : Finset (Fin 14)) : Prop :=
  ∀ u v : Fin 14, Adj u v → u ∈ S ∨ v ∈ S

def IsIndep (I : Finset (Fin 14)) : Prop :=
  ∀ u ∈ I, ∀ v ∈ I, ¬ Adj u v

theorem cover_card_ge_seven {S : Finset (Fin 14)} (hcov : IsCover S) : 7 ≤ S.card := by
  have hpair : ∀ v : Fin 14, v ∈ S ∨ hc_mate v ∈ S := fun v =>
    hcov v (hc_mate v) ((hc_adjB_iff v (hc_mate v)).1 (hc_match2 v).1)
  have hsub : (Finset.univ : Finset (Fin 14)) ⊆ S ∪ S.image hc_mate := by
    intro v _
    rcases hpair v with hv | hm
    · exact Finset.mem_union_left _ hv
    · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨hc_mate v, hm, (hc_match2 v).2⟩)
  have h14 : 14 ≤ S.card + (S.image hc_mate).card :=
    (by decide : 14 ≤ (Finset.univ : Finset (Fin 14)).card).trans
      ((Finset.card_le_card hsub).trans (Finset.card_union_le _ _))
  have him : (S.image hc_mate).card ≤ S.card := Finset.card_image_le
  omega

def IsAut (σ : Equiv.Perm (Fin 14)) : Prop :=
  ∀ u v : Fin 14, Adj (σ u) (σ v) ↔ Adj u v

def aut0_fn (v : Fin 14) : Fin 14 :=
  match v.val with
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | 8 => 8 | 9 => 9 | 10 => 10 | 11 => 11 | 12 => 12 | _ => 13

def aut0_inv (v : Fin 14) : Fin 14 :=
  match v.val with
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | 8 => 8 | 9 => 9 | 10 => 10 | 11 => 11 | 12 => 12 | _ => 13

def aut0 : Equiv.Perm (Fin 14) :=
  ⟨aut0_fn, aut0_inv, by decide +kernel, by decide +kernel⟩
def aut1_fn (v : Fin 14) : Fin 14 :=
  match v.val with
  | 0 => 2 | 1 => 5 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 1 | 6 => 6 | 7 => 12 | 8 => 8 | 9 => 9 | 10 => 13 | 11 => 11 | 12 => 7 | _ => 10

def aut1_inv (v : Fin 14) : Fin 14 :=
  match v.val with
  | 0 => 2 | 1 => 5 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 1 | 6 => 6 | 7 => 12 | 8 => 8 | 9 => 9 | 10 => 13 | 11 => 11 | 12 => 7 | _ => 10

def aut1 : Equiv.Perm (Fin 14) :=
  ⟨aut1_fn, aut1_inv, by decide +kernel, by decide +kernel⟩
def aut2_fn (v : Fin 14) : Fin 14 :=
  match v.val with
  | 0 => 7 | 1 => 10 | 2 => 12 | 3 => 8 | 4 => 9 | 5 => 13 | 6 => 11 | 7 => 0 | 8 => 3 | 9 => 4 | 10 => 1 | 11 => 6 | 12 => 2 | _ => 5

def aut2_inv (v : Fin 14) : Fin 14 :=
  match v.val with
  | 0 => 7 | 1 => 10 | 2 => 12 | 3 => 8 | 4 => 9 | 5 => 13 | 6 => 11 | 7 => 0 | 8 => 3 | 9 => 4 | 10 => 1 | 11 => 6 | 12 => 2 | _ => 5

def aut2 : Equiv.Perm (Fin 14) :=
  ⟨aut2_fn, aut2_inv, by decide +kernel, by decide +kernel⟩
def aut3_fn (v : Fin 14) : Fin 14 :=
  match v.val with
  | 0 => 12 | 1 => 13 | 2 => 7 | 3 => 8 | 4 => 9 | 5 => 10 | 6 => 11 | 7 => 2 | 8 => 3 | 9 => 4 | 10 => 5 | 11 => 6 | 12 => 0 | _ => 1

def aut3_inv (v : Fin 14) : Fin 14 :=
  match v.val with
  | 0 => 12 | 1 => 13 | 2 => 7 | 3 => 8 | 4 => 9 | 5 => 10 | 6 => 11 | 7 => 2 | 8 => 3 | 9 => 4 | 10 => 5 | 11 => 6 | 12 => 0 | _ => 1

def aut3 : Equiv.Perm (Fin 14) :=
  ⟨aut3_fn, aut3_inv, by decide +kernel, by decide +kernel⟩

theorem aut0_isAut : IsAut aut0 := by
  intro u v; simp only [← hc_adjB_iff]; revert u v; decide +kernel
theorem aut1_isAut : IsAut aut1 := by
  intro u v; simp only [← hc_adjB_iff]; revert u v; decide +kernel
theorem aut2_isAut : IsAut aut2 := by
  intro u v; simp only [← hc_adjB_iff]; revert u v; decide +kernel
theorem aut3_isAut : IsAut aut3 := by
  intro u v; simp only [← hc_adjB_iff]; revert u v; decide +kernel

def autOf (k : Fin 4) : Equiv.Perm (Fin 14) :=
  match k.val with
  | 0 => aut0
  | 1 => aut1
  | 2 => aut2
  | _ => aut3

theorem autOf_isAut (k : Fin 4) : IsAut (autOf k) := by
  fin_cases k
  · exact aut0_isAut
  · exact aut1_isAut
  · exact aut2_isAut
  · exact aut3_isAut

theorem g14Edge_aut (σ : Equiv.Perm (Fin 14)) (hσ : IsAut σ) (x : Fin 14 → Bool) :
    G14Edge (fun i => x (σ i)) ↔ G14Edge x := by
  simp only [g14Edge_iff_adj]
  constructor
  · rintro ⟨u, v, huv, hx, hy⟩
    exact ⟨σ u, σ v, (hσ u v).2 huv, hx, hy⟩
  · rintro ⟨u, v, huv, hx, hy⟩
    refine ⟨σ⁻¹ u, σ⁻¹ v, (hσ (σ⁻¹ u) (σ⁻¹ v)).1 ?_, by simpa using hx, by simpa using hy⟩
    simpa using huv

def hc_rep (idx : Fin 143) : Finset (Fin 14) :=
  match idx.val with
  | 0 => ({0, 1, 2} : Finset (Fin 14))
  | 1 => ({0, 1, 3} : Finset (Fin 14))
  | 2 => ({0, 2, 3} : Finset (Fin 14))
  | 3 => ({1, 2, 3} : Finset (Fin 14))
  | 4 => ({0, 1, 4} : Finset (Fin 14))
  | 5 => ({0, 2, 4} : Finset (Fin 14))
  | 6 => ({1, 2, 4} : Finset (Fin 14))
  | 7 => ({0, 3, 4} : Finset (Fin 14))
  | 8 => ({1, 3, 4} : Finset (Fin 14))
  | 9 => ({0, 1, 5} : Finset (Fin 14))
  | 10 => ({1, 3, 5} : Finset (Fin 14))
  | 11 => ({1, 4, 5} : Finset (Fin 14))
  | 12 => ({0, 1, 6} : Finset (Fin 14))
  | 13 => ({0, 2, 6} : Finset (Fin 14))
  | 14 => ({1, 2, 6} : Finset (Fin 14))
  | 15 => ({0, 3, 6} : Finset (Fin 14))
  | 16 => ({1, 3, 6} : Finset (Fin 14))
  | 17 => ({0, 4, 6} : Finset (Fin 14))
  | 18 => ({1, 4, 6} : Finset (Fin 14))
  | 19 => ({3, 4, 6} : Finset (Fin 14))
  | 20 => ({1, 5, 6} : Finset (Fin 14))
  | 21 => ({0, 2, 7} : Finset (Fin 14))
  | 22 => ({0, 4, 7} : Finset (Fin 14))
  | 23 => ({2, 4, 7} : Finset (Fin 14))
  | 24 => ({0, 5, 7} : Finset (Fin 14))
  | 25 => ({2, 5, 7} : Finset (Fin 14))
  | 26 => ({4, 5, 7} : Finset (Fin 14))
  | 27 => ({0, 6, 7} : Finset (Fin 14))
  | 28 => ({2, 6, 7} : Finset (Fin 14))
  | 29 => ({4, 6, 7} : Finset (Fin 14))
  | 30 => ({5, 6, 7} : Finset (Fin 14))
  | 31 => ({1, 3, 8} : Finset (Fin 14))
  | 32 => ({1, 4, 8} : Finset (Fin 14))
  | 33 => ({3, 4, 8} : Finset (Fin 14))
  | 34 => ({1, 5, 8} : Finset (Fin 14))
  | 35 => ({4, 7, 8} : Finset (Fin 14))
  | 36 => ({5, 7, 8} : Finset (Fin 14))
  | 37 => ({0, 2, 9} : Finset (Fin 14))
  | 38 => ({0, 4, 9} : Finset (Fin 14))
  | 39 => ({3, 4, 9} : Finset (Fin 14))
  | 40 => ({1, 2, 10} : Finset (Fin 14))
  | 41 => ({1, 3, 10} : Finset (Fin 14))
  | 42 => ({1, 6, 10} : Finset (Fin 14))
  | 43 => ({2, 6, 10} : Finset (Fin 14))
  | 44 => ({3, 6, 10} : Finset (Fin 14))
  | 45 => ({6, 7, 10} : Finset (Fin 14))
  | 46 => ({0, 2, 11} : Finset (Fin 14))
  | 47 => ({1, 2, 11} : Finset (Fin 14))
  | 48 => ({1, 5, 11} : Finset (Fin 14))
  | 49 => ({0, 1, 2, 3} : Finset (Fin 14))
  | 50 => ({0, 1, 2, 4} : Finset (Fin 14))
  | 51 => ({0, 1, 3, 4} : Finset (Fin 14))
  | 52 => ({0, 2, 3, 4} : Finset (Fin 14))
  | 53 => ({1, 2, 3, 4} : Finset (Fin 14))
  | 54 => ({0, 1, 2, 5} : Finset (Fin 14))
  | 55 => ({0, 1, 3, 5} : Finset (Fin 14))
  | 56 => ({0, 1, 4, 5} : Finset (Fin 14))
  | 57 => ({1, 3, 4, 5} : Finset (Fin 14))
  | 58 => ({0, 1, 2, 6} : Finset (Fin 14))
  | 59 => ({0, 1, 3, 6} : Finset (Fin 14))
  | 60 => ({0, 2, 3, 6} : Finset (Fin 14))
  | 61 => ({1, 2, 3, 6} : Finset (Fin 14))
  | 62 => ({0, 1, 4, 6} : Finset (Fin 14))
  | 63 => ({0, 2, 4, 6} : Finset (Fin 14))
  | 64 => ({1, 2, 4, 6} : Finset (Fin 14))
  | 65 => ({0, 3, 4, 6} : Finset (Fin 14))
  | 66 => ({1, 3, 4, 6} : Finset (Fin 14))
  | 67 => ({0, 1, 5, 6} : Finset (Fin 14))
  | 68 => ({1, 3, 5, 6} : Finset (Fin 14))
  | 69 => ({1, 4, 5, 6} : Finset (Fin 14))
  | 70 => ({0, 2, 4, 7} : Finset (Fin 14))
  | 71 => ({0, 2, 5, 7} : Finset (Fin 14))
  | 72 => ({0, 4, 5, 7} : Finset (Fin 14))
  | 73 => ({2, 4, 5, 7} : Finset (Fin 14))
  | 74 => ({0, 2, 6, 7} : Finset (Fin 14))
  | 75 => ({0, 4, 6, 7} : Finset (Fin 14))
  | 76 => ({2, 4, 6, 7} : Finset (Fin 14))
  | 77 => ({0, 5, 6, 7} : Finset (Fin 14))
  | 78 => ({2, 5, 6, 7} : Finset (Fin 14))
  | 79 => ({4, 5, 6, 7} : Finset (Fin 14))
  | 80 => ({1, 3, 4, 8} : Finset (Fin 14))
  | 81 => ({1, 3, 5, 8} : Finset (Fin 14))
  | 82 => ({1, 4, 5, 8} : Finset (Fin 14))
  | 83 => ({4, 5, 7, 8} : Finset (Fin 14))
  | 84 => ({0, 2, 3, 9} : Finset (Fin 14))
  | 85 => ({0, 2, 4, 9} : Finset (Fin 14))
  | 86 => ({0, 3, 4, 9} : Finset (Fin 14))
  | 87 => ({0, 2, 7, 9} : Finset (Fin 14))
  | 88 => ({0, 4, 7, 9} : Finset (Fin 14))
  | 89 => ({2, 4, 7, 9} : Finset (Fin 14))
  | 90 => ({3, 4, 8, 9} : Finset (Fin 14))
  | 91 => ({1, 2, 3, 10} : Finset (Fin 14))
  | 92 => ({1, 2, 6, 10} : Finset (Fin 14))
  | 93 => ({1, 3, 6, 10} : Finset (Fin 14))
  | 94 => ({2, 3, 6, 10} : Finset (Fin 14))
  | 95 => ({2, 6, 7, 10} : Finset (Fin 14))
  | 96 => ({1, 3, 8, 10} : Finset (Fin 14))
  | 97 => ({0, 1, 2, 11} : Finset (Fin 14))
  | 98 => ({0, 1, 5, 11} : Finset (Fin 14))
  | 99 => ({0, 2, 7, 11} : Finset (Fin 14))
  | 100 => ({0, 5, 7, 11} : Finset (Fin 14))
  | 101 => ({1, 5, 8, 11} : Finset (Fin 14))
  | 102 => ({0, 2, 9, 11} : Finset (Fin 14))
  | 103 => ({1, 2, 10, 11} : Finset (Fin 14))
  | 104 => ({0, 2, 7, 12} : Finset (Fin 14))
  | 105 => ({1, 2, 10, 12} : Finset (Fin 14))
  | 106 => ({0, 1, 2, 3, 4} : Finset (Fin 14))
  | 107 => ({0, 1, 2, 3, 5} : Finset (Fin 14))
  | 108 => ({0, 1, 2, 4, 5} : Finset (Fin 14))
  | 109 => ({0, 1, 3, 4, 5} : Finset (Fin 14))
  | 110 => ({0, 1, 2, 3, 6} : Finset (Fin 14))
  | 111 => ({0, 1, 2, 4, 6} : Finset (Fin 14))
  | 112 => ({0, 1, 3, 4, 6} : Finset (Fin 14))
  | 113 => ({0, 2, 3, 4, 6} : Finset (Fin 14))
  | 114 => ({1, 2, 3, 4, 6} : Finset (Fin 14))
  | 115 => ({0, 1, 2, 5, 6} : Finset (Fin 14))
  | 116 => ({0, 1, 3, 5, 6} : Finset (Fin 14))
  | 117 => ({0, 1, 4, 5, 6} : Finset (Fin 14))
  | 118 => ({1, 3, 4, 5, 6} : Finset (Fin 14))
  | 119 => ({0, 2, 4, 5, 7} : Finset (Fin 14))
  | 120 => ({0, 2, 4, 6, 7} : Finset (Fin 14))
  | 121 => ({0, 2, 5, 6, 7} : Finset (Fin 14))
  | 122 => ({0, 4, 5, 6, 7} : Finset (Fin 14))
  | 123 => ({2, 4, 5, 6, 7} : Finset (Fin 14))
  | 124 => ({1, 3, 4, 5, 8} : Finset (Fin 14))
  | 125 => ({0, 2, 3, 4, 9} : Finset (Fin 14))
  | 126 => ({0, 2, 4, 7, 9} : Finset (Fin 14))
  | 127 => ({1, 2, 3, 6, 10} : Finset (Fin 14))
  | 128 => ({0, 1, 2, 5, 11} : Finset (Fin 14))
  | 129 => ({0, 2, 5, 7, 11} : Finset (Fin 14))
  | 130 => ({0, 2, 7, 9, 11} : Finset (Fin 14))
  | 131 => ({0, 2, 4, 7, 12} : Finset (Fin 14))
  | 132 => ({0, 2, 6, 7, 12} : Finset (Fin 14))
  | 133 => ({1, 2, 6, 10, 12} : Finset (Fin 14))
  | 134 => ({0, 1, 2, 3, 4, 5} : Finset (Fin 14))
  | 135 => ({0, 1, 2, 3, 4, 6} : Finset (Fin 14))
  | 136 => ({0, 1, 2, 3, 5, 6} : Finset (Fin 14))
  | 137 => ({0, 1, 2, 4, 5, 6} : Finset (Fin 14))
  | 138 => ({0, 1, 3, 4, 5, 6} : Finset (Fin 14))
  | 139 => ({0, 2, 4, 5, 6, 7} : Finset (Fin 14))
  | 140 => ({0, 2, 4, 6, 7, 12} : Finset (Fin 14))
  | 141 => ({0, 2, 4, 7, 9, 12} : Finset (Fin 14))
  | _ => ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 14))

def repMask (idx : Fin 143) : ℕ :=
  match idx.val with
  | 0 => 7
  | 1 => 11
  | 2 => 13
  | 3 => 14
  | 4 => 19
  | 5 => 21
  | 6 => 22
  | 7 => 25
  | 8 => 26
  | 9 => 35
  | 10 => 42
  | 11 => 50
  | 12 => 67
  | 13 => 69
  | 14 => 70
  | 15 => 73
  | 16 => 74
  | 17 => 81
  | 18 => 82
  | 19 => 88
  | 20 => 98
  | 21 => 133
  | 22 => 145
  | 23 => 148
  | 24 => 161
  | 25 => 164
  | 26 => 176
  | 27 => 193
  | 28 => 196
  | 29 => 208
  | 30 => 224
  | 31 => 266
  | 32 => 274
  | 33 => 280
  | 34 => 290
  | 35 => 400
  | 36 => 416
  | 37 => 517
  | 38 => 529
  | 39 => 536
  | 40 => 1030
  | 41 => 1034
  | 42 => 1090
  | 43 => 1092
  | 44 => 1096
  | 45 => 1216
  | 46 => 2053
  | 47 => 2054
  | 48 => 2082
  | 49 => 15
  | 50 => 23
  | 51 => 27
  | 52 => 29
  | 53 => 30
  | 54 => 39
  | 55 => 43
  | 56 => 51
  | 57 => 58
  | 58 => 71
  | 59 => 75
  | 60 => 77
  | 61 => 78
  | 62 => 83
  | 63 => 85
  | 64 => 86
  | 65 => 89
  | 66 => 90
  | 67 => 99
  | 68 => 106
  | 69 => 114
  | 70 => 149
  | 71 => 165
  | 72 => 177
  | 73 => 180
  | 74 => 197
  | 75 => 209
  | 76 => 212
  | 77 => 225
  | 78 => 228
  | 79 => 240
  | 80 => 282
  | 81 => 298
  | 82 => 306
  | 83 => 432
  | 84 => 525
  | 85 => 533
  | 86 => 537
  | 87 => 645
  | 88 => 657
  | 89 => 660
  | 90 => 792
  | 91 => 1038
  | 92 => 1094
  | 93 => 1098
  | 94 => 1100
  | 95 => 1220
  | 96 => 1290
  | 97 => 2055
  | 98 => 2083
  | 99 => 2181
  | 100 => 2209
  | 101 => 2338
  | 102 => 2565
  | 103 => 3078
  | 104 => 4229
  | 105 => 5126
  | 106 => 31
  | 107 => 47
  | 108 => 55
  | 109 => 59
  | 110 => 79
  | 111 => 87
  | 112 => 91
  | 113 => 93
  | 114 => 94
  | 115 => 103
  | 116 => 107
  | 117 => 115
  | 118 => 122
  | 119 => 181
  | 120 => 213
  | 121 => 229
  | 122 => 241
  | 123 => 244
  | 124 => 314
  | 125 => 541
  | 126 => 661
  | 127 => 1102
  | 128 => 2087
  | 129 => 2213
  | 130 => 2693
  | 131 => 4245
  | 132 => 4293
  | 133 => 5190
  | 134 => 63
  | 135 => 95
  | 136 => 111
  | 137 => 119
  | 138 => 123
  | 139 => 245
  | 140 => 4309
  | 141 => 4757
  | _ => 127

def canonI : Finset (Finset (Fin 14)) := Finset.univ.image hc_rep

theorem hc_rep_of_mem {R : Finset (Fin 14)} (h : R ∈ canonI) :
    ∃ idx : Fin 143, hc_rep idx = R := by
  obtain ⟨idx, -, rfl⟩ := Finset.mem_image.1 h
  exact ⟨idx, rfl⟩

def setMask (S : Finset (Fin 14)) : ℕ :=
  (if (0 : Fin 14) ∈ S then 2 ^ 0 else 0) |||
  (if (1 : Fin 14) ∈ S then 2 ^ 1 else 0) |||
  (if (2 : Fin 14) ∈ S then 2 ^ 2 else 0) |||
  (if (3 : Fin 14) ∈ S then 2 ^ 3 else 0) |||
  (if (4 : Fin 14) ∈ S then 2 ^ 4 else 0) |||
  (if (5 : Fin 14) ∈ S then 2 ^ 5 else 0) |||
  (if (6 : Fin 14) ∈ S then 2 ^ 6 else 0) |||
  (if (7 : Fin 14) ∈ S then 2 ^ 7 else 0) |||
  (if (8 : Fin 14) ∈ S then 2 ^ 8 else 0) |||
  (if (9 : Fin 14) ∈ S then 2 ^ 9 else 0) |||
  (if (10 : Fin 14) ∈ S then 2 ^ 10 else 0) |||
  (if (11 : Fin 14) ∈ S then 2 ^ 11 else 0) |||
  (if (12 : Fin 14) ∈ S then 2 ^ 12 else 0) |||
  (if (13 : Fin 14) ∈ S then 2 ^ 13 else 0)

theorem ite_two_pow_testBit (p : Prop) [Decidable p] (k b : ℕ) :
    (if p then 2 ^ k else 0).testBit b = (decide (k = b) && decide p) := by
  split_ifs with hp <;> simp [Nat.testBit_two_pow, hp]

theorem setMask_testBit (S : Finset (Fin 14)) (i : Fin 14) :
    (setMask S).testBit i.val = decide (i ∈ S) := by
  fin_cases i <;>
    (simp only [setMask, Nat.testBit_or, ite_two_pow_testBit]; simp)

theorem ite_two_pow_lt (p : Prop) [Decidable p] (k : ℕ) (hk : k < 14) :
    (if p then 2 ^ k else 0) < 2 ^ 14 := by
  split_ifs
  · exact Nat.pow_lt_pow_right (by omega) hk
  · omega

theorem setMask_lt (S : Finset (Fin 14)) : setMask S < 16384 := by
  change setMask S < 2 ^ 14
  unfold setMask
  repeat (apply Nat.or_lt_two_pow)
  all_goals exact ite_two_pow_lt _ _ (by omega)

theorem setMask_inj {S T : Finset (Fin 14)} (h : setMask S = setMask T) : S = T := by
  ext i
  have h1 := congrArg (fun m => m.testBit i.val) h
  rw [setMask_testBit, setMask_testBit] at h1
  simpa using h1

theorem repMask_eq : ∀ idx : Fin 143, setMask (hc_rep idx) = repMask idx := by
  decide +kernel

def findCanonIdx (m : ℕ) : Option (Fin 143) :=
  match m with
  | 7 => some ⟨0, by decide⟩
  | 11 => some ⟨1, by decide⟩
  | 13 => some ⟨2, by decide⟩
  | 14 => some ⟨3, by decide⟩
  | 19 => some ⟨4, by decide⟩
  | 21 => some ⟨5, by decide⟩
  | 22 => some ⟨6, by decide⟩
  | 25 => some ⟨7, by decide⟩
  | 26 => some ⟨8, by decide⟩
  | 35 => some ⟨9, by decide⟩
  | 42 => some ⟨10, by decide⟩
  | 50 => some ⟨11, by decide⟩
  | 67 => some ⟨12, by decide⟩
  | 69 => some ⟨13, by decide⟩
  | 70 => some ⟨14, by decide⟩
  | 73 => some ⟨15, by decide⟩
  | 74 => some ⟨16, by decide⟩
  | 81 => some ⟨17, by decide⟩
  | 82 => some ⟨18, by decide⟩
  | 88 => some ⟨19, by decide⟩
  | 98 => some ⟨20, by decide⟩
  | 133 => some ⟨21, by decide⟩
  | 145 => some ⟨22, by decide⟩
  | 148 => some ⟨23, by decide⟩
  | 161 => some ⟨24, by decide⟩
  | 164 => some ⟨25, by decide⟩
  | 176 => some ⟨26, by decide⟩
  | 193 => some ⟨27, by decide⟩
  | 196 => some ⟨28, by decide⟩
  | 208 => some ⟨29, by decide⟩
  | 224 => some ⟨30, by decide⟩
  | 266 => some ⟨31, by decide⟩
  | 274 => some ⟨32, by decide⟩
  | 280 => some ⟨33, by decide⟩
  | 290 => some ⟨34, by decide⟩
  | 400 => some ⟨35, by decide⟩
  | 416 => some ⟨36, by decide⟩
  | 517 => some ⟨37, by decide⟩
  | 529 => some ⟨38, by decide⟩
  | 536 => some ⟨39, by decide⟩
  | 1030 => some ⟨40, by decide⟩
  | 1034 => some ⟨41, by decide⟩
  | 1090 => some ⟨42, by decide⟩
  | 1092 => some ⟨43, by decide⟩
  | 1096 => some ⟨44, by decide⟩
  | 1216 => some ⟨45, by decide⟩
  | 2053 => some ⟨46, by decide⟩
  | 2054 => some ⟨47, by decide⟩
  | 2082 => some ⟨48, by decide⟩
  | 15 => some ⟨49, by decide⟩
  | 23 => some ⟨50, by decide⟩
  | 27 => some ⟨51, by decide⟩
  | 29 => some ⟨52, by decide⟩
  | 30 => some ⟨53, by decide⟩
  | 39 => some ⟨54, by decide⟩
  | 43 => some ⟨55, by decide⟩
  | 51 => some ⟨56, by decide⟩
  | 58 => some ⟨57, by decide⟩
  | 71 => some ⟨58, by decide⟩
  | 75 => some ⟨59, by decide⟩
  | 77 => some ⟨60, by decide⟩
  | 78 => some ⟨61, by decide⟩
  | 83 => some ⟨62, by decide⟩
  | 85 => some ⟨63, by decide⟩
  | 86 => some ⟨64, by decide⟩
  | 89 => some ⟨65, by decide⟩
  | 90 => some ⟨66, by decide⟩
  | 99 => some ⟨67, by decide⟩
  | 106 => some ⟨68, by decide⟩
  | 114 => some ⟨69, by decide⟩
  | 149 => some ⟨70, by decide⟩
  | 165 => some ⟨71, by decide⟩
  | 177 => some ⟨72, by decide⟩
  | 180 => some ⟨73, by decide⟩
  | 197 => some ⟨74, by decide⟩
  | 209 => some ⟨75, by decide⟩
  | 212 => some ⟨76, by decide⟩
  | 225 => some ⟨77, by decide⟩
  | 228 => some ⟨78, by decide⟩
  | 240 => some ⟨79, by decide⟩
  | 282 => some ⟨80, by decide⟩
  | 298 => some ⟨81, by decide⟩
  | 306 => some ⟨82, by decide⟩
  | 432 => some ⟨83, by decide⟩
  | 525 => some ⟨84, by decide⟩
  | 533 => some ⟨85, by decide⟩
  | 537 => some ⟨86, by decide⟩
  | 645 => some ⟨87, by decide⟩
  | 657 => some ⟨88, by decide⟩
  | 660 => some ⟨89, by decide⟩
  | 792 => some ⟨90, by decide⟩
  | 1038 => some ⟨91, by decide⟩
  | 1094 => some ⟨92, by decide⟩
  | 1098 => some ⟨93, by decide⟩
  | 1100 => some ⟨94, by decide⟩
  | 1220 => some ⟨95, by decide⟩
  | 1290 => some ⟨96, by decide⟩
  | 2055 => some ⟨97, by decide⟩
  | 2083 => some ⟨98, by decide⟩
  | 2181 => some ⟨99, by decide⟩
  | 2209 => some ⟨100, by decide⟩
  | 2338 => some ⟨101, by decide⟩
  | 2565 => some ⟨102, by decide⟩
  | 3078 => some ⟨103, by decide⟩
  | 4229 => some ⟨104, by decide⟩
  | 5126 => some ⟨105, by decide⟩
  | 31 => some ⟨106, by decide⟩
  | 47 => some ⟨107, by decide⟩
  | 55 => some ⟨108, by decide⟩
  | 59 => some ⟨109, by decide⟩
  | 79 => some ⟨110, by decide⟩
  | 87 => some ⟨111, by decide⟩
  | 91 => some ⟨112, by decide⟩
  | 93 => some ⟨113, by decide⟩
  | 94 => some ⟨114, by decide⟩
  | 103 => some ⟨115, by decide⟩
  | 107 => some ⟨116, by decide⟩
  | 115 => some ⟨117, by decide⟩
  | 122 => some ⟨118, by decide⟩
  | 181 => some ⟨119, by decide⟩
  | 213 => some ⟨120, by decide⟩
  | 229 => some ⟨121, by decide⟩
  | 241 => some ⟨122, by decide⟩
  | 244 => some ⟨123, by decide⟩
  | 314 => some ⟨124, by decide⟩
  | 541 => some ⟨125, by decide⟩
  | 661 => some ⟨126, by decide⟩
  | 1102 => some ⟨127, by decide⟩
  | 2087 => some ⟨128, by decide⟩
  | 2213 => some ⟨129, by decide⟩
  | 2693 => some ⟨130, by decide⟩
  | 4245 => some ⟨131, by decide⟩
  | 4293 => some ⟨132, by decide⟩
  | 5190 => some ⟨133, by decide⟩
  | 63 => some ⟨134, by decide⟩
  | 95 => some ⟨135, by decide⟩
  | 111 => some ⟨136, by decide⟩
  | 119 => some ⟨137, by decide⟩
  | 123 => some ⟨138, by decide⟩
  | 245 => some ⟨139, by decide⟩
  | 4309 => some ⟨140, by decide⟩
  | 4757 => some ⟨141, by decide⟩
  | 127 => some ⟨142, by decide⟩
  | _ => none

theorem findCanonIdx_some (m : ℕ) (idx : Fin 143) (h : findCanonIdx m = some idx) :
    m = repMask idx := by
  unfold findCanonIdx at h
  split at h <;> cases h <;> rfl

def autMask (k : Fin 4) (m : ℕ) : ℕ :=
  (if m.testBit 0 then 2 ^ (autOf k 0).val else 0) |||
  (if m.testBit 1 then 2 ^ (autOf k 1).val else 0) |||
  (if m.testBit 2 then 2 ^ (autOf k 2).val else 0) |||
  (if m.testBit 3 then 2 ^ (autOf k 3).val else 0) |||
  (if m.testBit 4 then 2 ^ (autOf k 4).val else 0) |||
  (if m.testBit 5 then 2 ^ (autOf k 5).val else 0) |||
  (if m.testBit 6 then 2 ^ (autOf k 6).val else 0) |||
  (if m.testBit 7 then 2 ^ (autOf k 7).val else 0) |||
  (if m.testBit 8 then 2 ^ (autOf k 8).val else 0) |||
  (if m.testBit 9 then 2 ^ (autOf k 9).val else 0) |||
  (if m.testBit 10 then 2 ^ (autOf k 10).val else 0) |||
  (if m.testBit 11 then 2 ^ (autOf k 11).val else 0) |||
  (if m.testBit 12 then 2 ^ (autOf k 12).val else 0) |||
  (if m.testBit 13 then 2 ^ (autOf k 13).val else 0)

theorem autMask_testBit (k : Fin 4) (m : ℕ) (i : Fin 14) :
    (autMask k m).testBit i.val = m.testBit ((autOf k)⁻¹ i).val := by
  have hc : ∀ (j : Fin 14), ((autOf k j).val = i.val) ↔ j = (autOf k)⁻¹ i := by
    intro j
    constructor
    · intro h; exact ((Equiv.eq_symm_apply (autOf k)).2 (Fin.ext h))
    · intro h; exact congrArg Fin.val ((Equiv.eq_symm_apply (autOf k)).1 h)
  have hterm : ∀ (j : Fin 14),
      (if m.testBit j.val = true then 2 ^ (autOf k j).val else 0).testBit i.val =
      (decide (j = (autOf k)⁻¹ i) && m.testBit j.val) := by
    intro j; rw [ite_two_pow_testBit, decide_eq_decide.2 (hc j)]; cases m.testBit j.val <;> rfl
  have hexp : (autMask k m).testBit i.val =
      ((decide ((0 : Fin 14) = (autOf k)⁻¹ i) && m.testBit 0) ||
      (decide ((1 : Fin 14) = (autOf k)⁻¹ i) && m.testBit 1) ||
      (decide ((2 : Fin 14) = (autOf k)⁻¹ i) && m.testBit 2) ||
      (decide ((3 : Fin 14) = (autOf k)⁻¹ i) && m.testBit 3) ||
      (decide ((4 : Fin 14) = (autOf k)⁻¹ i) && m.testBit 4) ||
      (decide ((5 : Fin 14) = (autOf k)⁻¹ i) && m.testBit 5) ||
      (decide ((6 : Fin 14) = (autOf k)⁻¹ i) && m.testBit 6) ||
      (decide ((7 : Fin 14) = (autOf k)⁻¹ i) && m.testBit 7) ||
      (decide ((8 : Fin 14) = (autOf k)⁻¹ i) && m.testBit 8) ||
      (decide ((9 : Fin 14) = (autOf k)⁻¹ i) && m.testBit 9) ||
      (decide ((10 : Fin 14) = (autOf k)⁻¹ i) && m.testBit 10) ||
      (decide ((11 : Fin 14) = (autOf k)⁻¹ i) && m.testBit 11) ||
      (decide ((12 : Fin 14) = (autOf k)⁻¹ i) && m.testBit 12) ||
      (decide ((13 : Fin 14) = (autOf k)⁻¹ i) && m.testBit 13)) := by
    change ((if m.testBit (0 : Fin 14).val = true then 2 ^ (autOf k 0).val else 0) |||
      (if m.testBit (1 : Fin 14).val = true then 2 ^ (autOf k 1).val else 0) |||
      (if m.testBit (2 : Fin 14).val = true then 2 ^ (autOf k 2).val else 0) |||
      (if m.testBit (3 : Fin 14).val = true then 2 ^ (autOf k 3).val else 0) |||
      (if m.testBit (4 : Fin 14).val = true then 2 ^ (autOf k 4).val else 0) |||
      (if m.testBit (5 : Fin 14).val = true then 2 ^ (autOf k 5).val else 0) |||
      (if m.testBit (6 : Fin 14).val = true then 2 ^ (autOf k 6).val else 0) |||
      (if m.testBit (7 : Fin 14).val = true then 2 ^ (autOf k 7).val else 0) |||
      (if m.testBit (8 : Fin 14).val = true then 2 ^ (autOf k 8).val else 0) |||
      (if m.testBit (9 : Fin 14).val = true then 2 ^ (autOf k 9).val else 0) |||
      (if m.testBit (10 : Fin 14).val = true then 2 ^ (autOf k 10).val else 0) |||
      (if m.testBit (11 : Fin 14).val = true then 2 ^ (autOf k 11).val else 0) |||
      (if m.testBit (12 : Fin 14).val = true then 2 ^ (autOf k 12).val else 0) |||
      (if m.testBit (13 : Fin 14).val = true then 2 ^ (autOf k 13).val else 0)).testBit i.val = _
    simp only [Nat.testBit_or, hterm]
    rfl
  rw [hexp]
  generalize (autOf k)⁻¹ i = t
  fin_cases t <;> simp

theorem setMask_image_aut (k : Fin 4) (S : Finset (Fin 14)) :
    setMask (S.image (autOf k)) = autMask k (setMask S) := by
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < 14
  · have hL : (setMask (S.image (autOf k))).testBit b =
        decide ((⟨b, hb⟩ : Fin 14) ∈ S.image (autOf k)) :=
      setMask_testBit (S.image (autOf k)) ⟨b, hb⟩
    rw [hL]
    have him : (⟨b, hb⟩ : Fin 14) ∈ S.image (autOf k) ↔ (autOf k)⁻¹ ⟨b, hb⟩ ∈ S := by
      constructor
      · intro hmem
        obtain ⟨x, hx, hxi⟩ := Finset.mem_image.1 hmem
        have : x = (autOf k)⁻¹ ⟨b, hb⟩ := by rw [← hxi]; simp
        exact this ▸ hx
      · intro hx; exact Finset.mem_image.2 ⟨(autOf k)⁻¹ ⟨b, hb⟩, hx, by simp⟩
    have hR : (autMask k (setMask S)).testBit (⟨b, hb⟩ : Fin 14).val =
        decide ((autOf k)⁻¹ ⟨b, hb⟩ ∈ S) := by
      rw [autMask_testBit, setMask_testBit]
    change _ = (autMask k (setMask S)).testBit (⟨b, hb⟩ : Fin 14).val
    rw [hR, decide_eq_decide]
    exact him
  · have hL : (setMask (S.image (autOf k))).testBit b = false :=
      Nat.testBit_lt_two_pow ((setMask_lt _).trans_le (Nat.pow_le_pow_right (by omega : 0 < 2) (by omega : 14 ≤ b)))
    have hltR : autMask k (setMask S) < 2 ^ 14 := by
      unfold autMask
      repeat (apply Nat.or_lt_two_pow)
      all_goals exact ite_two_pow_lt _ _ (Fin.isLt _)
    have hR : (autMask k (setMask S)).testBit b = false :=
      Nat.testBit_lt_two_pow (hltR.trans_le (Nat.pow_le_pow_right (by omega : 0 < 2) (by omega : 14 ≤ b)))
    rw [hL, hR]

def isIndepMask (m : ℕ) : Bool :=
  edgeList.all (fun e => !(m.testBit e.1 && m.testBit e.2))

def pop14 (m : ℕ) : ℕ :=
  (if m.testBit 0 then 1 else 0) + (if m.testBit 1 then 1 else 0) +
  (if m.testBit 2 then 1 else 0) + (if m.testBit 3 then 1 else 0) +
  (if m.testBit 4 then 1 else 0) + (if m.testBit 5 then 1 else 0) +
  (if m.testBit 6 then 1 else 0) + (if m.testBit 7 then 1 else 0) +
  (if m.testBit 8 then 1 else 0) + (if m.testBit 9 then 1 else 0) +
  (if m.testBit 10 then 1 else 0) + (if m.testBit 11 then 1 else 0) +
  (if m.testBit 12 then 1 else 0) + (if m.testBit 13 then 1 else 0)

theorem isIndepMask_of_indep {I : Finset (Fin 14)} (hI : IsIndep I) :
    isIndepMask (setMask I) = true := by
  have hedge : ∀ u v : Fin 14, Adj u v →
      !((setMask I).testBit u.val && (setMask I).testBit v.val) = true := by
    intro u v huv
    rw [setMask_testBit, setMask_testBit]
    by_cases hu : u ∈ I <;> by_cases hv : v ∈ I
    · exact absurd huv (hI u hu v hv)
    · simp [hu, hv]
    · simp [hu, hv]
    · simp [hu, hv]
  unfold isIndepMask edgeList
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  exact ⟨hedge 0 8 (by decide), hedge 0 10 (by decide), hedge 1 7 (by decide), hedge 1 9 (by decide), hedge 1 13 (by decide), hedge 2 8 (by decide), hedge 2 13 (by decide), hedge 3 7 (by decide), hedge 3 11 (by decide), hedge 3 12 (by decide), hedge 4 10 (by decide), hedge 4 11 (by decide), hedge 4 13 (by decide), hedge 5 9 (by decide), hedge 5 10 (by decide), hedge 5 12 (by decide), hedge 6 8 (by decide), hedge 6 9 (by decide), hedge 6 11 (by decide)⟩

theorem pop14_eq_card (I : Finset (Fin 14)) : pop14 (setMask I) = I.card := by
  have h1 : I.card = ∑ x ∈ (Finset.univ : Finset (Fin 14)), if x ∈ I then 1 else 0 := by
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter, Nat.cast_id]
  have huniv : (Finset.univ : Finset (Fin 14)) = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13} := by
    decide
  rw [h1, huniv]
  simp only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton,
    Fin.reduceEq, or_self, not_false_eq_true]
  dsimp only [pop14]
  rw [show (setMask I).testBit 0 = decide ((0 : Fin 14) ∈ I) from setMask_testBit I 0,
      show (setMask I).testBit 1 = decide ((1 : Fin 14) ∈ I) from setMask_testBit I 1,
      show (setMask I).testBit 2 = decide ((2 : Fin 14) ∈ I) from setMask_testBit I 2,
      show (setMask I).testBit 3 = decide ((3 : Fin 14) ∈ I) from setMask_testBit I 3,
      show (setMask I).testBit 4 = decide ((4 : Fin 14) ∈ I) from setMask_testBit I 4,
      show (setMask I).testBit 5 = decide ((5 : Fin 14) ∈ I) from setMask_testBit I 5,
      show (setMask I).testBit 6 = decide ((6 : Fin 14) ∈ I) from setMask_testBit I 6,
      show (setMask I).testBit 7 = decide ((7 : Fin 14) ∈ I) from setMask_testBit I 7,
      show (setMask I).testBit 8 = decide ((8 : Fin 14) ∈ I) from setMask_testBit I 8,
      show (setMask I).testBit 9 = decide ((9 : Fin 14) ∈ I) from setMask_testBit I 9,
      show (setMask I).testBit 10 = decide ((10 : Fin 14) ∈ I) from setMask_testBit I 10,
      show (setMask I).testBit 11 = decide ((11 : Fin 14) ∈ I) from setMask_testBit I 11,
      show (setMask I).testBit 12 = decide ((12 : Fin 14) ∈ I) from setMask_testBit I 12,
      show (setMask I).testBit 13 = decide ((13 : Fin 14) ∈ I) from setMask_testBit I 13]
  simp only [decide_eq_true_eq]
  omega

theorem g14_canon_all : ∀ mL mR : Fin 128,
    let m := mL.val + 128 * mR.val
    isIndepMask m = true → 3 ≤ pop14 m →
    (findCanonIdx (autMask 0 m)).isSome || (findCanonIdx (autMask 1 m)).isSome ||
    (findCanonIdx (autMask 2 m)).isSome || (findCanonIdx (autMask 3 m)).isSome = true := by
  decide +kernel

theorem exists_aut_canon {I : Finset (Fin 14)} (hI : IsIndep I) (hge : 3 ≤ I.card) :
    ∃ σ : Equiv.Perm (Fin 14), IsAut σ ∧ I.image σ ∈ canonI := by
  set m := setMask I with hm
  have hlt : m < 16384 := setMask_lt I
  have hmL : m % 128 < 128 := Nat.mod_lt _ (by decide)
  have hmR : m / 128 < 128 := by omega
  have hsplit : m % 128 + 128 * (m / 128) = m := by omega
  have hall := g14_canon_all ⟨m % 128, hmL⟩ ⟨m / 128, hmR⟩
  dsimp only at hall
  rw [hsplit] at hall
  have hres := hall (isIndepMask_of_indep hI) (by rw [pop14_eq_card]; exact hge)
  have hex : ∃ k : Fin 4, (findCanonIdx (autMask k m)).isSome = true := by
    simp only [Bool.or_eq_true] at hres
    rcases hres with ((h0 | h1) | h2) | h3
    · exact ⟨0, h0⟩
    · exact ⟨1, h1⟩
    · exact ⟨2, h2⟩
    · exact ⟨3, h3⟩
  obtain ⟨k, hk⟩ := hex
  obtain ⟨idx, hidx⟩ := Option.isSome_iff_exists.1 hk
  refine ⟨autOf k, autOf_isAut k, Finset.mem_image.2 ⟨idx, Finset.mem_univ _, ?_⟩⟩
  apply setMask_inj
  rw [repMask_eq, setMask_image_aut, ← hm]
  exact (findCanonIdx_some _ _ hidx).symm

theorem g14_not_empty : ¬ G14Edge (fun _ => false) := by
  rintro ⟨_, _, _, h, _⟩; exact Bool.noConfusion h

theorem g14_not_single (v : Fin 14) : ¬ G14Edge (fun i => decide (i = v)) := by
  rw [g14Edge_iff_adj]
  rintro ⟨a, b, hab, ha, hb⟩
  simp only [decide_eq_true_eq] at ha hb
  rw [ha, hb] at hab
  exact adj_irrefl v hab

theorem g14_pair {u v : Fin 14} (h : Adj u v) :
    G14Edge (fun i => decide (i = u) || decide (i = v)) :=
  (g14Edge_iff_adj _).2 ⟨u, v, h, by simp, by simp⟩

theorem g14_essential (i : Fin 14) : ∃ x y : Fin 14 → Bool,
    (∀ j, j ≠ i → x j = y j) ∧ G14Edge x ∧ ¬ G14Edge y :=
  ⟨fun j => decide (j = i) || decide (j = hc_mate i), fun j => decide (j = hc_mate i),
   fun j hj => by simp [hj], g14_pair ((hc_adjB_iff i (hc_mate i)).1 (hc_match2 i).1),
   g14_not_single (hc_mate i)⟩

def Correct (D : Dag) : Prop :=
  ∀ x : Fin 14 → Bool, val D x (outW 14 D) = true ↔ G14Edge x

theorem g14_normalize (C : Circuit) (hmono : Monotone2 C)
    (hC : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ G14Edge x) :
    ∃ D : Dag, StrictLive 14 D ∧ D.length ≤ C.size ∧ Correct D := by
  have h08 : Adj (0 : Fin 14) 8 := by decide
  obtain ⟨D, hD, hlen, hval⟩ := normalize_strictLive (n := 14) C hmono
    (by
      intro b
      cases b
      · exact ⟨_, by rw [Ne, Bool.not_eq_false]; exact (hC _).2 (g14_pair h08)⟩
      · exact ⟨fun _ => false, fun h => g14_not_empty ((hC _).1 h)⟩)
    (by
      intro i
      refine ⟨fun k => decide (k = i), fun h => g14_not_single i ((hC _).1 ?_)⟩
      rw [h]; simp)
    (by
      intro i
      obtain ⟨x, y, hxy, hx, hy⟩ := g14_essential i
      refine ⟨x, y, hxy, fun h => hy ((hC y).1 ?_)⟩
      rw [← h]; exact (hC x).2 hx)
  exact ⟨D, hD, hlen, fun x => by rw [hval x]; exact hC x⟩

theorem g14_supp_out {D : Dag} (hD : Correct D) : supp 14 D (outW 14 D) = ∅ :=
  Finset.eq_empty_iff_forall_notMem.mpr fun v hv =>
    g14_not_single v ((hD _).mp (mem_supp.mp hv))

theorem g14_relabel (σ : Equiv.Perm (Fin 14)) (hσ : IsAut σ) {D : Dag}
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
  exact g14Edge_aut σ hσ x

theorem inelig_card_add (n : ℕ) (D : Dag) : (ineligSet n D).card + (eligSet n D).card = n := by
  have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (eligSet n D))
  simpa [ineligSet] using h

theorem g14_cover_iff_indep (D : Dag) :
    IsCover (eligSet 14 D) ↔ IsIndep (ineligSet 14 D) := by
  constructor
  · intro hcov u hu v hv huv
    have h1 := Finset.mem_sdiff.mp hu
    have h2 := Finset.mem_sdiff.mp hv
    exact (hcov u v huv).elim h1.2 h2.2
  · intro hind u v huv
    by_contra hc; push Not at hc
    exact hind u (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hc.1⟩)
      v (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hc.2⟩) huv

theorem g14_wlog {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hind : IsIndep (ineligSet 14 D)) (hge : 3 ≤ (ineligSet 14 D).card) :
    ∃ D' : Dag, StrictLive 14 D' ∧ Correct D' ∧ D'.length = D.length ∧
      totalSurplus 14 D' = totalSurplus 14 D ∧
      Bplus 14 D' = Bplus 14 D ∧ Bzero 14 D' = Bzero 14 D ∧
      (ineligSet 14 D').card = (ineligSet 14 D).card ∧
      ineligSet 14 D' ∈ canonI := by
  obtain ⟨σ, hσ, hmem⟩ := exists_aut_canon hind hge
  obtain ⟨h1, h2, h3, h4, h5, h6, -, h8⟩ := g14_relabel σ hσ h hD
  refine ⟨relabel σ D, h1, h2, h3, h4, h5, h6, ?_, h8 ▸ hmem⟩
  rw [h8, Finset.card_image_of_injective _ σ.injective]

theorem g14_budget {D : Dag} (h : StrictLive 14 D) (hlen : D.length ≤ 24) :
    totalSurplus 14 D = D.length - 13 ∧ totalSurplus 14 D ≤ 11 := by
  have := surplus_identity h
  exact ⟨by omega, by omega⟩

theorem g14_p_bounds {D : Dag} (h : StrictLive 14 D) (hlen : D.length ≤ 24)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b) (hcov : IsCover (eligSet 14 D)) :
    7 ≤ (eligSet 14 D).card ∧ (eligSet 14 D).card ≤ Bplus 14 D ∧
      Bplus 14 D ≤ 11 ∧ totalSurplus 14 D ≤ 11 := by
  have h1 := cover_card_ge_seven hcov
  have h2 := elig_le_Bplus h.1 b hb
  have h3 := Bplus_le_total 14 D
  have h4 := (g14_budget h hlen).2
  exact ⟨h1, h2, by omega, h4⟩

theorem g14_inelig_bounds {D : Dag} (h : StrictLive 14 D) (hlen : D.length ≤ 24)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b) (hcov : IsCover (eligSet 14 D)) :
    (ineligSet 14 D).Nonempty ∧ 3 ≤ (ineligSet 14 D).card ∧ (ineligSet 14 D).card ≤ 7 := by
  obtain ⟨h7, hp, hB, h11⟩ := g14_p_bounds h hlen b hb hcov
  have hc := inelig_card_add 14 D
  exact ⟨Finset.card_pos.1 (by omega), by omega, by omega⟩

/-! ## Block D: semantic core, dominance, purity, consumers -/

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

/-! ### Changed-value paths and dominance -/

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

/-! ### Ineligible labels -/

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

/-! ### Joint meeting of an edge -/

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

/-! ### The unique consumer of an ineligible label -/

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

/-! ### Exposure and first productions of projected masks -/

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


/-! ### G14 forms: the two hypotheses of Layer 1 -/

theorem sem_g14_second : ∀ u v : Fin 14, ∃ a, hc_adjB u a = true ∧ a ≠ v := by decide +kernel

theorem sem_g14_gr : sem_Gr (fun u v : Fin 14 => Adj u v) :=
  ⟨fun _ _ => adj_symm, adj_irrefl, nbr_diff_exists, fun u v => by
    obtain ⟨a, h1, h2⟩ := sem_g14_second u v
    exact ⟨a, (hc_adjB_iff u a).mp h1, h2⟩⟩

theorem sem_g14_comp {D : Dag} (hD : Correct D) : sem_Comp 14 (fun u v : Fin 14 => Adj u v) D :=
  fun x => (hD x).trans (g14Edge_iff_adj x)

theorem exists_pureBranch {D : Dag} (h : StrictLive 14 D) (hD : Correct D) :
    ∃ b : Fin 14 → ℕ, PureBranch 14 D b :=
  sem_exists_pureBranch sem_g14_gr h.1 (sem_g14_comp hD)

theorem elig_isCover {D : Dag} (h : StrictLive 14 D) (hD : Correct D) :
    IsCover (eligSet 14 D) :=
  fun _ _ huv => sem_elig_cover sem_g14_gr h (sem_g14_comp hD) huv

theorem g14_wlog_canon (C : Circuit) (hmono : Monotone2 C)
    (hC : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ G14Edge x)
    (hsize : C.size ≤ 24) :
    ∃ D : Dag, StrictLive 14 D ∧ Correct D ∧ D.length ≤ 24 ∧
      totalSurplus 14 D ≤ 11 ∧ 3 ≤ (ineligSet 14 D).card ∧ ineligSet 14 D ∈ canonI := by
  obtain ⟨D0, h0, hlen0, hD0⟩ := g14_normalize C hmono hC
  have hlen : D0.length ≤ 24 := by omega
  obtain ⟨b, hb⟩ := exists_pureBranch h0 hD0
  have hcov := elig_isCover h0 hD0
  obtain ⟨-, hge3, -⟩ := g14_inelig_bounds h0 hlen b hb hcov
  obtain ⟨D, h1, h2, h3, -, -, -, -, h8⟩ :=
    g14_wlog h0 hD0 ((g14_cover_iff_indep D0).mp hcov) hge3
  have hlen' : D.length ≤ 24 := by omega
  obtain ⟨b', hb'⟩ := exists_pureBranch h1 h2
  obtain ⟨-, hge3', -⟩ := g14_inelig_bounds h1 hlen' b' hb' (elig_isCover h1 h2)
  exact ⟨D, h1, h2, hlen', (g14_budget h1 hlen').2, hge3', h8⟩

/-! ### Signed consumption codes, cover-freeness, private positions -/

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

/-- Single-label flow: `|W_x| + M_x = 1 + B_x`. -/
theorem sem_flow1 (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D) (x : Fin n) :
    (sem_W n D x).card + (merges n D (carrierT n D {x})).card =
      1 + surplusOn D (carrierT n D {x}) := by
  have h1 := carrier_flow_union h {x} (by rw [sem_supp_out hG hC]; simp)
  rwa [Finset.card_singleton] at h1

/-- Every edge is met at opposite consumption positions. -/
theorem sem_edge_slots (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) {x y : Fin n}
    (hxy : G x y) : ∃ e, e ∈ sem_W n D x ∧ sem_bar e ∈ sem_W n D y ∧
      y ∉ supp n D (src D e) ∧ x ∉ supp n D (src D (sem_bar e)) ∧
      val D (sem_two x y) (n + e.1) = true := by
  obtain ⟨j, hj, -, hval, hju, hjv, s, h1, h2, h3, h4⟩ := sem_joint_meeting hG hS hC hxy
  exact ⟨(j, s), sem_mem_W.mpr ⟨hj, h1, hju⟩, sem_mem_W.mpr ⟨hj, h3, hjv⟩, h2, h4, hval⟩

/-- Cover-freeness in operand form: if `a`, `b` are nonadjacent and `x` has a neighbour `y`
adjacent to neither, some position consuming `x` has an operand carrying neither `a` nor
`b`. The case `a = b` is allowed. -/
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

/-- Antichain property in operand form. -/
theorem sem_antichain (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) {x a : Fin n}
    (hxa : x ≠ a) : ∃ e, e ∈ sem_W n D x ∧ a ∉ supp n D (src D e) := by
  obtain ⟨z, hxz, haz⟩ := hG.2.2.1 x a hxa
  obtain ⟨e, he, h1, -⟩ := sem_cover_free hG hS hC (a := a) (b := a) (hG.2.1 a) hxz
    (fun h => haz (hG.1 _ _ h)) (fun h => haz (hG.1 _ _ h))
  exact ⟨e, he, h1⟩

/-- A necessary free AND: an eligible edge forces an AND gate with empty support, two
supported operands, true on the edge, none of whose operands carries an ineligible label. -/
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
/-! ### Zero-merge carriers: single-reader arms and common terminals -/

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

/-- A first-branch choice that is also the earliest branching carrier. -/
def sem_MinBranch (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Prop :=
  ∀ v ∈ eligSet n D, 2 ≤ fanout D (b v) ∧ supp n D (b v) = {v} ∧ sem_Chain n D v.val (b v) ∧
    ∀ w, 2 ≤ fanout D w → v ∈ supp n D w → b v ≤ w

/-- Arm steps for a label set `X`: out of a single-reader wire, both ends carrying all of `X`. -/
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

/-- With no internal merge in the carrier of `x`, a gate carrying `x` is an OR with exactly
one carrying operand. -/
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

/-- The code count of one label: `|W_x| + M_x = 1 + [x eligible] +` residual units on `x`. -/
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

/-- Descent along single-reader carriers: from a wire `c` carrying all of `X`, when the
carriers of the labels of `X` have no merge and no branching from `c` on, an arm leads to
the source of a position consuming every label of `X`. -/
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

/-- Two arms: a wire with two readers carrying all of `X`, after which no carrier of a label
of `X` branches or merges, leads to two positions at different gates consuming all of `X`. -/
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

/-- With exactly one residual unit, a label with three consumption positions is eligible,
has no carrier merge and no further consumption, and is carried by the residual wire. -/
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

/-- Common terminals: with exactly one residual unit, the labels having three consumption
positions share two positions at different gates. -/
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

/-! ### Unique paths, the factor lemma, exact neighbourhoods -/

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

/-- An edge of `{i} ∪ S` uses `i` or lies inside `S`. -/
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

/-- Dominance relative to a target wire `t` at or after the chain end. -/
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

/-- A reader path out of the start of a single-reader chain passes through its end, or ends
strictly inside the chain. -/
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

/-- The other operand of the reader of a single-reader chain wire does not depend on the
input at the start of the chain. -/
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

/-- A dominating wire separates a non-edge assignment from its edge extension by `v`. -/
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

/-- The unique-path factor lemma: if a single-reader chain leads from the input `i` to `w`,
and on the labels of `Bs` the wire `w` behaves like `i AND (OR N)`, then some AND gate on
the chain has an operand whose support projected to `Bs` is exactly `N`. -/
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

/-- Exact neighbourhood at a wire `w`: the conditions of the factor lemma in graph form. -/
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

/-- The first branching wire reached from an ineligible input has empty support. -/
theorem sem_branch_empty (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) {i : Fin n}
    (hi : i ∈ ineligSet n D) {b : ℕ} (hch : sem_Chain n D i.val b) (hf : 2 ≤ fanout D b) :
    supp n D b = ∅ := by
  have hsub := sem_dom_pure hG hS hC i b (sem_chain_dom hS hch)
  refine Finset.eq_empty_of_forall_notMem (fun x hx => ?_)
  have h1 := hsub hx
  rw [Finset.mem_singleton] at h1
  have h2 := mem_ineligSet.mp hi b (h1 ▸ hx)
  omega

/-- A reader path is a single-reader chain or meets a branching wire reached by one. -/
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

/-- An ineligible input has a unique path to the output, or reaches an empty branch. -/
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

/-- Without empty-support surplus, every branching wire has nonempty support. -/
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

/-- With at most one empty-support surplus unit there is at most one empty branch. -/
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

/-- No empty branch: every wire reached from an ineligible input lies on its single-reader
chain; in particular the path to the output is unique. -/
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

/-- Exact neighbourhood from a unique path to the output: for an independent label set
`Bs`, some AND gate on the path of `i` has an operand whose support meets `Bs` exactly in
the neighbours of `i`. -/
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

/-- Exact neighbourhood before a wire dominating two inputs: if the path from `i` to `w` is
unique, `w` also dominates `j`, and `j` has a neighbour in `Bs` that `i` lacks, then some
AND gate on the path of `i` has an operand meeting `Bs` exactly in the neighbours of `i`. -/
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

/-- One empty branch loses at most one exact neighbourhood: of two ineligible inputs with
incomparable neighbourhoods inside an independent set `Bs`, at least one has an AND gate on
its path with an operand meeting `Bs` exactly in its neighbours. -/
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

/-- Full support of the assigned operand: if every gate reached from the consumer of an
ineligible `i` is an OR, the operand opposite the pure one carries exactly the neighbours. -/
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

/-- `B_K = 1 +` the residual units carrying `x` without `y`, for the carrier of an eligible
`x` without `y`. -/
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

/-- The first joint carrier of two labels is an OR whose operands carry one label each. -/
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

/-- Depletion set-up: if every residual unit carrying the eligible `x` also carries `c`, a
joint carrier of `x` and `c` exists, and `x` has a neighbour `z` not adjacent to `c`, then
the carrier of `x` without `c` has surplus one, no merge, exactly two exits, and one of the
exits enters an OR gate carrying `c`. -/
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

/-- On the unique path of an input, every AND sibling carries every neighbour. -/
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

/-! ## Block F: support-mask charging and witness costs -/

/-- `M` occurs as the exact mask, projected onto `P`, of some wire. -/
def sup_Occ (n : ℕ) (D : Dag) (P M : Finset (Fin n)) : Prop := ∃ w, supp n D w ∩ P = M

/-- Internal merges of the union carrier of `P` whose output mask has at least two labels. -/
def sup_big (n : ℕ) (D : Dag) (P : Finset (Fin n)) : Finset ℕ :=
  (merges n D (carrierT n D P)).filter (fun j => 2 ≤ (supp n D (n + j) ∩ P).card)

/-- Witness position for the loss of `f`: an AND position consuming `f` whose operand mask
lies inside `U` and has at most two labels. -/
def sup_Wit (n : ℕ) (D : Dag) (P U : Finset (Fin n)) (f : Fin n) (e : ℕ × Bool) : Prop :=
  e.1 < D.length ∧ tag D e.1 = true ∧ f ∈ P ∧ f ∈ supp n D (src D e) ∧
    f ∉ supp n D (n + e.1) ∧ supp n D (src D e) ∩ P ⊆ U ∧ (supp n D (src D e) ∩ P).card ≤ 2

/-- The cost unit of a witness position: its boundary arc when the output mask is empty,
its gate otherwise. -/
def sup_cost (n : ℕ) (D : Dag) (P : Finset (Fin n)) (e : ℕ × Bool) : (ℕ × Bool) ⊕ ℕ :=
  if supp n D (n + e.1) ∩ P = ∅ then Sum.inl e else Sum.inr e.1

/-- Admissible witness costs: exits whose operand mask has at most two labels, or merges
with a singleton output mask. -/
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

/-! ### First productions are big merges -/

/-- Every occurring mask with at least two labels is the output mask of a big merge. -/
theorem sup_occ_big (hS : Strict n D) {P M : Finset (Fin n)} (hM : 2 ≤ M.card)
    (h : sup_Occ n D P M) : ∃ j ∈ sup_big n D P, supp n D (n + j) ∩ P = M := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨j, -, -, hj, hmer, -, -⟩ := sem_first_mask hS P M hM w hw
  exact ⟨j, Finset.mem_filter.mpr ⟨hmer, by rw [hj]; exact hM⟩, hj⟩

/-- A finite family of occurring masks with at least two labels needs as many big merges. -/
theorem sup_card_le_big (hS : Strict n D) (P : Finset (Fin n)) (F : Finset (Finset (Fin n)))
    (hF : ∀ M ∈ F, 2 ≤ M.card ∧ sup_Occ n D P M) : F.card ≤ (sup_big n D P).card := by
  have hsub : F ⊆ (sup_big n D P).image (fun j => supp n D (n + j) ∩ P) := by
    intro M hM
    obtain ⟨j, hj, hjM⟩ := sup_occ_big hS (hF M hM).1 (hF M hM).2
    exact Finset.mem_image.mpr ⟨j, hj, hjM⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

/-! ### The charging theorem for triples meeting in at most one label -/

/-- First production of an occurring triple: an occurring pair inside it, an occurring
four-set around it, or two different occurring five-sets around it. -/
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

/-- Six-label form (stars of a K4 on six secant labels): the first production of an
occurring triple has an occurring pair inside it or an occurring four-set around it. -/
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

/-- Auxiliary masks: a family `L` of occurring triples pairwise meeting in at most one label,
on at most seven labels, has at least as many occurring auxiliary masks, each a pair inside
a target or a set of four or five labels. Doubled integer charges: two per pair or four-set,
one per five-set. -/
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

/-- The charging theorem: `m` occurring triples pairwise meeting in at most one label, on at
most seven labels, give `2 * m` big merges; further occurring masks outside the charged
classes (not a target, not of size four or five, and if a pair then inside no target) are
counted on top. -/
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

/-! ### Witness positions for missing masks -/

/-- A witness for the loss of `f ∈ U`, from exposure on an independent set containing
`P \ U`: `U` has at most two labels, or is a triple that occurs on no wire. -/
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

/-- The output mask of a witness gate lies in the operand mask without the lost label. -/
theorem sup_wit_out (hS : Strict n D) {P U : Finset (Fin n)} {f : Fin n} {e : ℕ × Bool}
    (h : sup_Wit n D P U f e) :
    supp n D (n + e.1) ∩ P ⊆ (supp n D (src D e) ∩ P).erase f := by
  obtain ⟨hj, ht, -, -, h2, -, -⟩ := h
  intro v hv
  rw [Finset.mem_inter] at hv
  rw [Finset.mem_erase, Finset.mem_inter]
  exact ⟨fun hvf => h2 (hvf ▸ hv.1), sem_supp_and_sub hS hj ht e.2 hv.1, hv.2⟩

/-- When no pair inside `U` containing `f` occurs, the witness operand mask is `{f}`. -/
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

/-- The cost of a witness is admissible: an exit of the carrier of `P` with operand mask of
at most two labels, or a merge of that carrier with a singleton output mask. -/
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

/-- Two witnesses at the same position with nonempty output mask lose the same label. -/
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

/-- Witnesses confined to disjoint label sets have different costs. -/
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

/-- A witness whose operand mask is the singleton of its label shares its cost with no
witness of another label. -/
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

/-- Fibre bound: one cost unit witnesses at most two labels, also across different sets. -/
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

/-- `k` witnessed labels need at least `k / 2` distinct cost units, in doubled form. -/
theorem sup_wit_card (hS : Strict n D) {P : Finset (Fin n)} (Lab : Finset (Fin n))
    (U : Fin n → Finset (Fin n)) (wit : Fin n → ℕ × Bool)
    (hwit : ∀ f ∈ Lab, sup_Wit n D P (U f) f (wit f)) :
    Lab.card ≤ 2 * (Lab.image (fun f => sup_cost n D P (wit f))).card :=
  Finset.card_le_mul_card_image Lab 2 (fun c _ => sup_fibre_le hS Lab U wit hwit c)

/-- Sharpened form: labels whose witness operand mask is their own singleton need one cost
unit each, shared with no other label. -/
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


/-! ### The three disjoint charge classes (generalized for deg-2 and deg-3 exits) -/

theorem sup_master_disj (P : Finset (Fin n)) (E : Finset (ℕ × Bool))
    (hE : ∀ e ∈ E, e ∈ exitArcs n D (carrierT n D P))
    (C : Finset ((ℕ × Bool) ⊕ ℕ)) (hC : ∀ c ∈ C, sup_CostOK n D P c)
    (hdis : Disjoint E C.toLeft) :
    (sup_big n D P).card + E.card + C.card ≤
      (exitArcs n D (carrierT n D P)).card + (merges n D (carrierT n D P)).card := by
  have hl : ∀ e ∈ C.toLeft, e ∈ exitArcs n D (carrierT n D P) ∧
      (supp n D (src D e) ∩ P).card ≤ 2 := fun e he => hC _ (Finset.mem_toLeft.mp he)
  have hr : ∀ j ∈ C.toRight, j ∈ merges n D (carrierT n D P) ∧
      (supp n D (n + j) ∩ P).card = 1 := fun j hj => hC _ (Finset.mem_toRight.mp hj)
  have h1 : E.card + C.toLeft.card ≤ (exitArcs n D (carrierT n D P)).card := by
    rw [← Finset.card_union_of_disjoint hdis]
    refine Finset.card_le_card (fun e he => ?_)
    rcases Finset.mem_union.mp he with h | h
    · exact hE e h
    · exact (hl e h).1
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

theorem sup_count_disj (hS : Strict n D) (P : Finset (Fin n)) (E : Finset (ℕ × Bool))
    (hE : ∀ e ∈ E, e ∈ exitArcs n D (carrierT n D P))
    (Lab S : Finset (Fin n)) (U : Fin n → Finset (Fin n)) (wit : Fin n → ℕ × Bool)
    (hwit : ∀ f ∈ Lab, sup_Wit n D P (U f) f (wit f)) (hSL : S ⊆ Lab)
    (hsing : ∀ f ∈ S, supp n D (src D (wit f)) ∩ P = {f})
    (hdis : ∀ e ∈ E, ∀ f ∈ Lab, e ≠ wit f) :
    2 * ((sup_big n D P).card + E.card) + 2 * S.card + (Lab \ S).card ≤
      2 * ((exitArcs n D (carrierT n D P)).card + (merges n D (carrierT n D P)).card) := by
  have h1 := sup_wit_card_single hS Lab S U wit hwit hSL hsing
  have hdis' : Disjoint E (Lab.image (fun f => sup_cost n D P (wit f))).toLeft := by
    rw [Finset.disjoint_left]
    intro e he hL
    rw [Finset.mem_toLeft, Finset.mem_image] at hL
    obtain ⟨f, hf, hcf⟩ := hL
    have hwe : wit f = e := by
      unfold sup_cost at hcf
      split at hcf
      · exact Sum.inl.inj hcf
      · exact absurd hcf (by simp)
    exact hdis e he f hf hwe.symm
  have h2 := sup_master_disj P E hE (Lab.image (fun f => sup_cost n D P (wit f))) (by
    intro c hc
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hc
    exact sup_cost_ok hS (hwit f hf)) hdis'
  omega

end SupMask

/-- A system of assigned positions: for every ineligible label `i` an operand position of
a gate with empty support whose operand carries every neighbour of `i` and whose opposite
operand is `i`-pure; distinct ineligible labels get distinct positions. -/
def k4_Pos (n : ℕ) (G : Fin n → Fin n → Prop) (D : Dag) (pos : Fin n → ℕ × Bool) : Prop :=
  (∀ i ∈ ineligSet n D, (pos i).1 < D.length ∧ supp n D (n + (pos i).1) = ∅ ∧
    (∀ a, G i a → a ∈ supp n D (src D (pos i))) ∧
    supp n D (src D ((pos i).1, !(pos i).2)) = {i}) ∧
  ∀ i ∈ ineligSet n D, ∀ i' ∈ ineligSet n D, pos i = pos i' → i = i'

theorem k4_assigned {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag} (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D) :
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


/-! ## Stage 3A: generalized counting and G12 elimination -/

theorem bz_card {n : ℕ} {D : Dag} (hS : Strict n D) (Z : Finset ℕ)
    (hZ : ∀ b ∈ Z, 2 ≤ fanout D b ∧ supp n D b = ∅) : Z.card ≤ Bzero n D := by
  have hsub : Z ⊆ (inner n D).filter (fun w => ¬ (supp n D w).Nonempty) :=
    fun b hb => sem_bzero_mem hS (hZ b hb).1 (hZ b hb).2
  calc Z.card = ∑ _w ∈ Z, 1 := by simp
    _ ≤ ∑ w ∈ Z, (fanout D w - 1) :=
        Finset.sum_le_sum (fun w hw => by have := (hZ w hw).1; omega)
    _ ≤ Bzero n D := Finset.sum_le_sum_of_subset hsub

theorem cnt_main2 {n : ℕ} {D : Dag} (hS : Strict n D) {P : Finset (Fin n)} (hP : P.card ≤ 7)
    (L3 : Finset (Finset (Fin n))) (h3 : ∀ T ∈ L3, T.card = 3 ∧ sup_Occ n D P T)
    (hint : ∀ T ∈ L3, ∀ T' ∈ L3, T ≠ T' → (T ∩ T').card ≤ 1)
    (L2 : Finset (Finset (Fin n)))
    (h2 : ∀ M ∈ L2, M.card = 2 ∧ sup_Occ n D P M ∧ ∀ T ∈ L3, ¬ M ⊆ T)
    (E : Finset (ℕ × Bool)) (hE : ∀ e ∈ E, e ∈ exitArcs n D (carrierT n D P))
    (Lab : Finset (Fin n)) (U : Fin n → Finset (Fin n))
    (hw : ∀ f ∈ Lab, ∃ e, sup_Wit n D P (U f) f e)
    (hUL3 : ∀ f ∈ Lab, ∀ T ∈ L3, (U f ∩ T).card ≤ 1)
    (hUL2 : ∀ f ∈ Lab, ∀ M ∈ L2, (U f ∩ M).card ≤ 1)
    (hEdis : ∀ e ∈ E, ∀ f ∈ Lab, ∀ w, sup_Wit n D P (U f) f w → e ≠ w) :
    2 * L3.card + L2.card + E.card + Lab.card ≤
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
  have hL2dis : Disjoint L2 ((Lab \ S).image pr) := by
    rw [Finset.disjoint_left]
    intro M hM2 hMpr
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hMpr
    have hsub := (hpr f hf).1
    have hcard := (hpr f hf).2.1
    have := Finset.card_le_card (Finset.subset_inter hsub (Finset.Subset.refl _))
    have := hUL2 f (Finset.mem_sdiff.1 hf).1 _ hM2
    omega
  have hX := sup_charge hS hP L3 h3 hint (L2 ∪ (Lab \ S).image pr) (by
    intro M hM
    rcases Finset.mem_union.1 hM with hM2 | hMpr
    · obtain ⟨hc, ho, hnoT⟩ := h2 M hM2
      refine ⟨ho, by omega, fun hL => by have := (h3 _ hL).1; omega, by omega, by omega,
        fun _ T hT => hnoT T hT⟩
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hMpr
      obtain ⟨h1, h2', -, h4⟩ := hpr f hf
      refine ⟨h4, by omega, fun hL => by have := (h3 _ hL).1; omega, by omega, by omega,
        fun _ T hT hsub => ?_⟩
      have := Finset.card_le_card (Finset.subset_inter h1 hsub)
      have := hUL3 f (Finset.mem_sdiff.1 hf).1 T hT
      omega)
  rw [Finset.card_union_of_disjoint hL2dis] at hX
  have hcnt := sup_count_disj hS P E hE Lab S U wit hwit hSL
    (fun f hf => sup_wit_single (hwit f (hSL hf)) (Finset.mem_filter.1 hf).2)
    (fun e he f hf => hEdis e he f hf (wit f) (hwit f hf))
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


section L3bGen

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

/-- Residual inclusion: when every residual unit on `x` also carries `c`, all consumption
operands of `x` but one carry `c`. -/
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

/-- With no merge in the carrier of `c`, an AND operand carrying `c` consumes `c`. -/
theorem zm_mem (hS : Strict n D) {c : Fin n} (hM : merges n D (carrierT n D {c}) = ∅)
    {e : ℕ × Bool} (he : e.1 < D.length) (ht : tag D e.1 = true)
    (hc : c ∈ supp n D (src D e)) : e ∈ sem_W n D c :=
  sem_mem_W.2 ⟨he, hc, fun hc2 => by
    have := (sem_zm_gate hS hM he hc2).1
    rw [ht] at this
    exact Bool.noConfusion this⟩

/-- Common terminals: labels without carrier merge whose only residual unit is `u0` share
two consumption positions at different gates. -/
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

/-- Full support of the assigned operand: with no empty branch, if every other consumption
of a neighbour `v` of the ineligible `i` sits opposite an operand carrying a label other
than `i`, the operand opposite the consumer of `i` carries exactly the neighbours of `i`. -/
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


end L3bGen


/-! ## Stage 3A: generalized counting and G14 (`L-meta-9774`) elimination -/

def sideL : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6}
def sideR : Finset (Fin 14) := {7, 8, 9, 10, 11, 12, 13}

def os_ptL (k : Fin 7) : Fin 14 := ⟨k.val, by omega⟩
def os_ptR (k : Fin 7) : Fin 14 := ⟨7 + k.val, by omega⟩

theorem os_ptL_inj : Function.Injective os_ptL := fun a b h => Fin.ext (by
  have := congrArg Fin.val h; simpa [os_ptL] using this)

theorem os_ptR_inj : Function.Injective os_ptR := fun a b h => Fin.ext (by
  have := congrArg Fin.val h; dsimp [os_ptR] at this; omega)

def maskFin7 (m : Fin 128) : Finset (Fin 7) :=
  Finset.univ.filter (fun k : Fin 7 => m.val.testBit k.val)

theorem exists_maskFin7 (S : Finset (Fin 7)) : ∃ m : Fin 128, maskFin7 m = S := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by ext k; simp [maskFin7]⟩
  | insert a s _ ih =>
    obtain ⟨m, hm⟩ := ih
    have hpow : 2 ^ a.val < 2 ^ 7 := Nat.pow_lt_pow_right (by omega) a.isLt
    refine ⟨⟨m.val ||| 2 ^ a.val, Nat.or_lt_two_pow m.isLt hpow⟩, ?_⟩
    ext k
    simp only [maskFin7, Finset.mem_filter, Finset.mem_univ, true_and, Nat.testBit_or,
      Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq, Finset.mem_insert]
    have hmk : m.val.testBit k.val = true ↔ k ∈ s := by
      have := Finset.ext_iff.1 hm k
      simpa [maskFin7] using this
    rw [hmk, Fin.ext_iff]
    tauto

theorem g14_sides : ∀ a b : Fin 14, hc_adjB a b = true →
    decide (a.val < 7) ≠ decide (b.val < 7) := by decide +kernel

theorem sideL_indep : ∀ a ∈ sideL, ∀ b ∈ sideL, ¬ Adj a b := by
  intro a ha b hb hab
  have h1 := g14_sides a b ((hc_adjB_iff a b).2 hab)
  have h2 : ∀ x ∈ sideL, decide (x.val < 7) = true := by decide +kernel
  rw [h2 a ha, h2 b hb] at h1; exact h1 rfl

theorem sideR_indep : ∀ a ∈ sideR, ∀ b ∈ sideR, ¬ Adj a b := by
  intro a ha b hb hab
  have h1 := g14_sides a b ((hc_adjB_iff a b).2 hab)
  have h2 : ∀ x ∈ sideR, decide (x.val < 7) = false := by decide +kernel
  rw [h2 a ha, h2 b hb] at h1; exact h1 rfl

theorem g14_lost {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (P : Finset (Fin 14))
    (hP : ∀ a ∈ P, ∀ b ∈ P, ¬ Adj a b) (J : Finset (Fin 14))
    (hJ : ∀ i ∈ J, i ∈ ineligSet 14 D ∧ sem_g14_nb i ⊆ P ∧ ¬ sup_Occ 14 D P (sem_g14_nb i)) :
    J.card ≤ Bzero 14 D := by
  classical
  have hG := sem_g14_gr
  have hC := sem_g14_comp hD
  have hocc : ∀ i ∈ J, ∀ q, (∀ a ∈ P, (a ∈ supp 14 D q ↔ Adj i a)) → False := by
    intro i hi q hq
    refine (hJ i hi).2.2 ⟨q, ?_⟩
    ext a
    rw [Finset.mem_inter, g14_mem_nb]
    exact ⟨fun h1 => (hq a h1.2).1 h1.1,
      fun h1 => ⟨(hq a ((hJ i hi).2.1 (g14_mem_nb.2 h1))).2 h1, (hJ i hi).2.1 (g14_mem_nb.2 h1)⟩⟩
  have hb : ∀ i ∈ J, ∃ b, sem_Chain 14 D i.val b ∧ 2 ≤ fanout D b ∧ supp 14 D b = ∅ := by
    intro i hi
    rcases sem_inelig_reach hG h hC (hJ i hi).1 with hch | hb
    · obtain ⟨j, s, -, -, -, hq⟩ := sem_exact_nbhd hG h.1 hC P hP hch
      exact absurd hq (hocc i hi _)
    · exact hb
  choose! br hbr using hb
  have hinj : Set.InjOn br J := by
    intro i hi j hj hij
    by_contra hne
    obtain ⟨a, hja, hia⟩ := nbr_diff_exists j i (Ne.symm hne)
    have h1 := sem_shared_exact hG h.1 hC P hP (hbr i hi).1
      (hij ▸ sem_chain_dom h.1 (hbr j hj).1) ⟨a, (hJ j hj).2.1 (g14_mem_nb.2 hja), hja, hia⟩
    obtain ⟨_, _, -, -, -, -, hq⟩ := h1
    exact hocc i hi _ hq
  calc J.card = (J.image br).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ Bzero 14 D := bz_card h.1 (J.image br) (fun b hb => by
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hb
        exact (hbr i hi).2)

theorem g14_count {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (P : Finset (Fin 14))
    (hPi : ∀ a ∈ P, ∀ b ∈ P, ¬ Adj a b) (hP7 : P.card ≤ 7) (hPe : P ⊆ eligSet 14 D)
    (Oc3 Oc2 Ct Iin : Finset (Fin 14))
    (hOc3 : ∀ i ∈ Oc3, sem_g14_nb i ⊆ P ∧ (sem_g14_nb i).card = 3 ∧ sup_Occ 14 D P (sem_g14_nb i))
    (hOc2 : ∀ i ∈ Oc2, sem_g14_nb i ⊆ P ∧ (sem_g14_nb i).card = 2 ∧ sup_Occ 14 D P (sem_g14_nb i))
    (hCt : ∀ c ∈ Ct, c ∉ Oc3 ∧ c ∉ Oc2 ∧
      (sem_g14_nb c ⊆ P → ¬ sup_Occ 14 D P (sem_g14_nb c)))
    (hIin : ∀ i ∈ Iin, i ∈ ineligSet 14 D ∧ sem_g14_nb i ⊆ P) :
    2 * Oc3.card + Oc2.card + Iin.card + (Ct.biUnion (fun c => sem_g14_nb c ∩ P)).card +
      (eligSet 14 D).card ≤ 2 * P.card + Bplus 14 D := by
  classical
  have hG := sem_g14_gr
  have hC := sem_g14_comp hD
  obtain ⟨b, hb⟩ := exists_pureBranch h hD
  obtain ⟨pos, hpos⟩ := k4_assigned hG h hC
  have hEinj : Set.InjOn pos Iin := fun i hi j hj hij =>
    hpos.2 i (hIin i hi).1 j (hIin j hj).1 hij
  have hE : ∀ e ∈ Iin.image pos, e ∈ exitArcs 14 D (carrierT 14 D P) := by
    intro e he
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨hj, hemp, hnb, -⟩ := hpos.1 i (hIin i hi).1
    have hdeg := degree_two_or_three i
    have hne : (sem_g14_nb i).Nonempty := Finset.card_pos.1 (by dsimp [sem_g14_nb]; omega)
    obtain ⟨a, ha⟩ := hne
    rw [exitArcs, Finset.mem_filter]
    refine ⟨Finset.mem_product.2 ⟨Finset.mem_range.2 hj, Finset.mem_univ _⟩,
      sup_mem_carrier.2 ⟨a, Finset.mem_inter.2 ⟨hnb a (g14_mem_nb.1 ha), (hIin i hi).2 ha⟩⟩, ?_⟩
    rw [sup_mem_carrier, hemp, Finset.empty_inter]
    exact Finset.not_nonempty_empty
  have hlab : ∀ f ∈ Ct.biUnion (fun c => sem_g14_nb c ∩ P), ∃ c ∈ Ct, f ∈ sem_g14_nb c ∩ P :=
    fun f hf => Finset.mem_biUnion.1 hf
  choose! ct hct using hlab
  have hmain := cnt_main2 h.1 hP7 (Oc3.image sem_g14_nb)
    (fun T hT => by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hT
      exact ⟨(hOc3 i hi).2.1, (hOc3 i hi).2.2⟩)
    (fun T hT T' hT' hne => by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hT
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hT'
      have := sup_g14_inter i j (fun hij => hne (hij ▸ rfl)) Finset.univ
      simpa [sem_g14_nb] using this)
    (Oc2.image sem_g14_nb)
    (fun M hM => by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hM
      refine ⟨(hOc2 i hi).2.1, (hOc2 i hi).2.2, fun T hT hsub => ?_⟩
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hT
      have hij : i ≠ j := fun h => by
        have h2 := (hOc2 i hi).2.1; have h3 := (hOc3 j hj).2.1; rw [h] at h2; omega
      have hle := sup_g14_inter i j hij Finset.univ
      have hsub' : sem_g14_nb i ⊆ sem_g14_nb i ∩ sem_g14_nb j :=
        Finset.subset_inter (Finset.Subset.refl _) hsub
      have hc := Finset.card_le_card hsub'
      have h2 := (hOc2 i hi).2.1
      simp only [Finset.inter_univ] at hle
      omega)
    (Iin.image pos) hE (Ct.biUnion (fun c => sem_g14_nb c ∩ P)) (fun f => sem_g14_nb (ct f) ∩ P)
    (fun f hf => by
      obtain ⟨hc, hfc⟩ := hct f hf
      refine sup_wit_exists hG h.1 hC (X := insert (ct f) (P \ (sem_g14_nb (ct f) ∩ P)))
        Finset.inter_subset_right ?_ ?_ (fun a ha => Finset.mem_insert_of_mem ha) hfc
        ⟨ct f, Finset.mem_insert_self _ _, adj_symm (g14_mem_nb.1 (Finset.mem_inter.1 hfc).1)⟩
      · by_cases hsubP : sem_g14_nb (ct f) ⊆ P
        · rcases degree_two_or_three (ct f) with hd2 | hd3
          · exact Or.inl (by rw [Finset.inter_eq_left.2 hsubP]; dsimp [sem_g14_nb]; omega)
          · rw [Finset.inter_eq_left.2 hsubP]
            exact Or.inr ⟨hd3, (hCt _ hc).2.2 hsubP⟩
        · have hlt : (sem_g14_nb (ct f) ∩ P).card < (sem_g14_nb (ct f)).card :=
            Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨Finset.inter_subset_left,
              fun heq => hsubP (heq ▸ Finset.inter_subset_right)⟩)
          rcases degree_two_or_three (ct f) with hd2 | hd3 <;> (rw [g14_nb_eq] at hlt ⊢; exact Or.inl (by omega))
      · have hno : ∀ a ∈ P \ (sem_g14_nb (ct f) ∩ P), ¬ Adj (ct f) a := by
          intro a ha hadj
          rw [Finset.mem_sdiff, Finset.mem_inter, g14_mem_nb] at ha
          exact ha.2 ⟨hadj, ha.1⟩
        intro a ha b hb
        rcases Finset.mem_insert.1 ha with rfl | ha <;> rcases Finset.mem_insert.1 hb with rfl | hb
        · exact adj_irrefl _
        · exact hno b hb
        · exact fun hab => hno a ha (adj_symm hab)
        · exact hPi a (Finset.mem_sdiff.1 ha).1 b (Finset.mem_sdiff.1 hb).1)
    (fun f hf T hT => by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hT
      have h1 := sup_g14_inter i (ct f) (fun hij => (hCt _ (hct f hf).1).1 (hij ▸ hi)) P
      rwa [Finset.inter_comm (sem_g14_nb i)] at h1)
    (fun f hf M hM => by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hM
      have h1 := sup_g14_inter i (ct f) (fun hij => (hCt _ (hct f hf).1).2.1 (hij ▸ hi)) P
      rwa [Finset.inter_comm (sem_g14_nb i)] at h1)
    (fun e he f hf w hw hew => by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 he
      obtain ⟨hc, -⟩ := hct f hf
      have hnbi : sem_g14_nb i ⊆ supp 14 D (src D (pos i)) ∩ P := fun a ha =>
        Finset.mem_inter.2 ⟨(hpos.1 i (hIin i hi).1).2.2.1 a (g14_mem_nb.1 ha), (hIin i hi).2 ha⟩
      have hwsub : supp 14 D (src D (pos i)) ∩ P ⊆ sem_g14_nb (ct f) ∩ P := hew ▸ hw.2.2.2.2.2.1
      by_cases hci : ct f = i
      · rw [hci, Finset.inter_eq_left.2 (hIin i hi).2] at hwsub
        have heq : supp 14 D (src D (pos i)) ∩ P = sem_g14_nb i := Finset.Subset.antisymm hwsub hnbi
        exact (hCt (ct f) hc).2.2 (hci ▸ (hIin i hi).2) ⟨src D (pos i), hci ▸ heq⟩
      · have hle := sup_g14_inter i (ct f) (Ne.symm hci) P
        have hsub' : sem_g14_nb i ⊆ sem_g14_nb i ∩ (sem_g14_nb (ct f) ∩ P) :=
          Finset.subset_inter (Finset.Subset.refl _) (hnbi.trans hwsub)
        have hcard := Finset.card_le_card hsub'
        rcases degree_two_or_three i with hd | hd <;> (rw [g14_nb_eq] at hcard hle; omega))
  have h4 := carrier_flow_union h P (by rw [g14_supp_out hD]; simp)
  have h5 := surplus_carrierT_le h.1 b hb P
  rw [Finset.inter_eq_left.2 hPe] at h5
  rw [Finset.card_image_of_injective _ (fun i j hij => g14_nb_inj hij),
    Finset.card_image_of_injective _ (fun i j hij => g14_nb_inj hij),
    Finset.card_image_of_injOn hEinj] at hmain
  omega

/-- Generic side-R counting + lost-budget step for any orbit `I = ineligSet 14 D`. -/
theorem g14_sideR_step {D : Dag} (h : StrictLive 14 D) (hD : Correct D) :
    ∃ m : Fin 128,
      let I := ineligSet 14 D
      let P := sideR \ I
      let Oc := maskFin7 m
      let Oc3 := Oc.filter (fun k => (g14_nbB (os_ptL k)).card = 3)
      let Oc2 := Oc.filter (fun k => (g14_nbB (os_ptL k)).card = 2)
      let Ct := (Finset.univ : Finset (Fin 7)) \ Oc
      let Iin := Finset.univ.filter (fun k : Fin 7 => os_ptL k ∈ I ∧ g14_nbB (os_ptL k) ⊆ P)
      (∀ k ∈ Oc, g14_nbB (os_ptL k) ⊆ P) ∧
      2 * Oc3.card + Oc2.card + Iin.card + (Ct.biUnion (fun k => g14_nbB (os_ptL k) ∩ P)).card +
        (14 - I.card) ≤ 2 * P.card + Bplus 14 D ∧
      (Iin \ Oc).card ≤ Bzero 14 D := by
  classical
  set I := ineligSet 14 D with hIdef
  set P := sideR \ I
  have hPl : P ⊆ sideR := Finset.sdiff_subset
  have hPi : ∀ a ∈ P, ∀ b ∈ P, ¬ Adj a b := fun a ha b hb => sideR_indep a (hPl ha) b (hPl hb)
  have hP7 : P.card ≤ 7 := (Finset.card_le_card hPl).trans (by decide)
  have hPe : P ⊆ eligSet 14 D := fun a ha => by
    by_contra hne; exact (Finset.mem_sdiff.1 ha).2 (sem_mem_inelig.2 hne)
  let Oc := Finset.univ.filter (fun k : Fin 7 =>
    g14_nbB (os_ptL k) ⊆ P ∧ sup_Occ 14 D P (sem_g14_nb (os_ptL k)))
  obtain ⟨m, hm⟩ := exists_maskFin7 Oc
  refine ⟨m, ?_⟩
  dsimp only
  rw [hm]
  let Oc3 := Oc.filter (fun k => (g14_nbB (os_ptL k)).card = 3)
  let Oc2 := Oc.filter (fun k => (g14_nbB (os_ptL k)).card = 2)
  let Ct := (Finset.univ : Finset (Fin 7)) \ Oc
  let Iin := Finset.univ.filter (fun k : Fin 7 => os_ptL k ∈ I ∧ g14_nbB (os_ptL k) ⊆ P)
  have hcnt := g14_count h hD P hPi hP7 hPe (Oc3.image os_ptL) (Oc2.image os_ptL) (Ct.image os_ptL)
    (Iin.image os_ptL)
    (fun i hi => by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hi
      rw [Finset.mem_filter] at hk
      have hko := Finset.mem_filter.1 hk.1
      rw [g14_nb_eq]; exact ⟨hko.2.1, hk.2, g14_nb_eq _ ▸ hko.2.2⟩)
    (fun i hi => by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hi
      rw [Finset.mem_filter] at hk
      have hko := Finset.mem_filter.1 hk.1
      rw [g14_nb_eq]; exact ⟨hko.2.1, hk.2, g14_nb_eq _ ▸ hko.2.2⟩)
    (fun c hc => by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hc
      have hnk : k ∉ Oc := (Finset.mem_sdiff.1 hk).2
      refine ⟨fun h3 => ?_, fun h2 => ?_, fun hsub hocc => ?_⟩
      · obtain ⟨k', hk', heq⟩ := Finset.mem_image.1 h3
        rw [os_ptL_inj heq] at hk'; exact hnk (Finset.mem_filter.1 hk').1
      · obtain ⟨k', hk', heq⟩ := Finset.mem_image.1 h2
        rw [os_ptL_inj heq] at hk'; exact hnk (Finset.mem_filter.1 hk').1
      · exact hnk (Finset.mem_filter.2 ⟨Finset.mem_univ k, g14_nb_eq _ ▸ hsub, hocc⟩))
    (fun i hi => by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hi
      have hki := (Finset.mem_filter.1 hk).2
      exact ⟨hki.1, g14_nb_eq _ ▸ hki.2⟩)
  have hlost := g14_lost h hD P hPi ((Iin \ Oc).image os_ptL)
    (fun i hi => by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hi
      rw [Finset.mem_sdiff] at hk
      have hki := (Finset.mem_filter.1 hk.1).2
      refine ⟨hki.1, g14_nb_eq _ ▸ hki.2, fun hocc => hk.2 ?_⟩
      exact Finset.mem_filter.2 ⟨Finset.mem_univ k, hki.2, hocc⟩)
  rw [Finset.card_image_of_injective _ os_ptL_inj] at hlost
  rw [Finset.card_image_of_injective _ os_ptL_inj, Finset.card_image_of_injective _ os_ptL_inj,
    Finset.card_image_of_injective _ os_ptL_inj] at hcnt
  have hLabEq : ((Ct.image os_ptL).biUnion (fun c => sem_g14_nb c ∩ P)) =
      Ct.biUnion (fun k => g14_nbB (os_ptL k) ∩ P) := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_inter, g14_nb_eq]
    constructor
    · rintro ⟨c, ⟨k, hk, rfl⟩, hx⟩; exact ⟨k, hk, hx⟩
    · rintro ⟨k, hk, hx⟩; exact ⟨os_ptL k, ⟨k, hk, rfl⟩, hx⟩
  rw [hLabEq] at hcnt
  have hel := inelig_card_add 14 D
  rw [← hIdef] at hel
  refine ⟨fun k hk => (Finset.mem_filter.1 hk).2.1, ?_, hlost⟩
  change 2 * Oc3.card + Oc2.card + Iin.card + (Ct.biUnion (fun k => g14_nbB (os_ptL k) ∩ P)).card +
    (14 - I.card) ≤ 2 * P.card + Bplus 14 D
  omega

/-- Generic side-L counting + lost-budget step (used for `I = (1, 3, 8, 9, 10)`). -/
theorem g14_sideL_step {D : Dag} (h : StrictLive 14 D) (hD : Correct D) :
    ∃ m : Fin 128,
      let I := ineligSet 14 D
      let P := sideL \ I
      let Oc := maskFin7 m
      let Oc3 := Oc.filter (fun k => (g14_nbB (os_ptR k)).card = 3)
      let Oc2 := Oc.filter (fun k => (g14_nbB (os_ptR k)).card = 2)
      let Ct := (Finset.univ : Finset (Fin 7)) \ Oc
      let Iin := Finset.univ.filter (fun k : Fin 7 => os_ptR k ∈ I ∧ g14_nbB (os_ptR k) ⊆ P)
      (∀ k ∈ Oc, g14_nbB (os_ptR k) ⊆ P) ∧
      2 * Oc3.card + Oc2.card + Iin.card + (Ct.biUnion (fun k => g14_nbB (os_ptR k) ∩ P)).card +
        (14 - I.card) ≤ 2 * P.card + Bplus 14 D ∧
      (Iin \ Oc).card ≤ Bzero 14 D := by
  classical
  set I := ineligSet 14 D with hIdef
  set P := sideL \ I
  have hPl : P ⊆ sideL := Finset.sdiff_subset
  have hPi : ∀ a ∈ P, ∀ b ∈ P, ¬ Adj a b := fun a ha b hb => sideL_indep a (hPl ha) b (hPl hb)
  have hP7 : P.card ≤ 7 := (Finset.card_le_card hPl).trans (by decide)
  have hPe : P ⊆ eligSet 14 D := fun a ha => by
    by_contra hne; exact (Finset.mem_sdiff.1 ha).2 (sem_mem_inelig.2 hne)
  let Oc := Finset.univ.filter (fun k : Fin 7 =>
    g14_nbB (os_ptR k) ⊆ P ∧ sup_Occ 14 D P (sem_g14_nb (os_ptR k)))
  obtain ⟨m, hm⟩ := exists_maskFin7 Oc
  refine ⟨m, ?_⟩
  dsimp only
  rw [hm]
  let Oc3 := Oc.filter (fun k => (g14_nbB (os_ptR k)).card = 3)
  let Oc2 := Oc.filter (fun k => (g14_nbB (os_ptR k)).card = 2)
  let Ct := (Finset.univ : Finset (Fin 7)) \ Oc
  let Iin := Finset.univ.filter (fun k : Fin 7 => os_ptR k ∈ I ∧ g14_nbB (os_ptR k) ⊆ P)
  have hcnt := g14_count h hD P hPi hP7 hPe (Oc3.image os_ptR) (Oc2.image os_ptR) (Ct.image os_ptR)
    (Iin.image os_ptR)
    (fun i hi => by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hi
      rw [Finset.mem_filter] at hk
      have hko := Finset.mem_filter.1 hk.1
      rw [g14_nb_eq]; exact ⟨hko.2.1, hk.2, g14_nb_eq _ ▸ hko.2.2⟩)
    (fun i hi => by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hi
      rw [Finset.mem_filter] at hk
      have hko := Finset.mem_filter.1 hk.1
      rw [g14_nb_eq]; exact ⟨hko.2.1, hk.2, g14_nb_eq _ ▸ hko.2.2⟩)
    (fun c hc => by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hc
      have hnk : k ∉ Oc := (Finset.mem_sdiff.1 hk).2
      refine ⟨fun h3 => ?_, fun h2 => ?_, fun hsub hocc => ?_⟩
      · obtain ⟨k', hk', heq⟩ := Finset.mem_image.1 h3
        rw [os_ptR_inj heq] at hk'; exact hnk (Finset.mem_filter.1 hk').1
      · obtain ⟨k', hk', heq⟩ := Finset.mem_image.1 h2
        rw [os_ptR_inj heq] at hk'; exact hnk (Finset.mem_filter.1 hk').1
      · exact hnk (Finset.mem_filter.2 ⟨Finset.mem_univ k, g14_nb_eq _ ▸ hsub, hocc⟩))
    (fun i hi => by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hi
      have hki := (Finset.mem_filter.1 hk).2
      exact ⟨hki.1, g14_nb_eq _ ▸ hki.2⟩)
  have hlost := g14_lost h hD P hPi ((Iin \ Oc).image os_ptR)
    (fun i hi => by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hi
      rw [Finset.mem_sdiff] at hk
      have hki := (Finset.mem_filter.1 hk.1).2
      refine ⟨hki.1, g14_nb_eq _ ▸ hki.2, fun hocc => hk.2 ?_⟩
      exact Finset.mem_filter.2 ⟨Finset.mem_univ k, hki.2, hocc⟩)
  rw [Finset.card_image_of_injective _ os_ptR_inj] at hlost
  rw [Finset.card_image_of_injective _ os_ptR_inj, Finset.card_image_of_injective _ os_ptR_inj,
    Finset.card_image_of_injective _ os_ptR_inj] at hcnt
  have hLabEq : ((Ct.image os_ptR).biUnion (fun c => sem_g14_nb c ∩ P)) =
      Ct.biUnion (fun k => g14_nbB (os_ptR k) ∩ P) := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_inter, g14_nb_eq]
    constructor
    · rintro ⟨c, ⟨k, hk, rfl⟩, hx⟩; exact ⟨k, hk, hx⟩
    · rintro ⟨k, hk, hx⟩; exact ⟨os_ptR k, ⟨k, hk, rfl⟩, hx⟩
  rw [hLabEq] at hcnt
  have hel := inelig_card_add 14 D
  rw [← hIdef] at hel
  refine ⟨fun k hk => (Finset.mem_filter.1 hk).2.1, ?_, hlost⟩
  change 2 * Oc3.card + Oc2.card + Iin.card + (Ct.biUnion (fun k => g14_nbB (os_ptR k) ∩ P)).card +
    (14 - I.card) ≤ 2 * P.card + Bplus 14 D
  omega

/-! ## Stage 3B: code-size bounds, `two_in_deg3`, `pa_m1`, `ps_nonadj`, `pa_setup` -/

abbrev G14 : Fin 14 → Fin 14 → Prop := fun u v => Adj u v

def ru (D : Dag) (b : Fin 14 → ℕ) (x : Fin 14) : Finset (Σ _ : ℕ, ℕ) :=
  (residualUnits 14 D b).filter (fun u => x ∈ supp 14 D u.1)

theorem res_elig {D : Dag} {b : Fin 14 → ℕ} {u : Σ _ : ℕ, ℕ}
    (hu : u ∈ residualUnits 14 D b) {x : Fin 14} (hx : x ∈ supp 14 D u.1) : x ∈ eligSet 14 D :=
  mem_eligSet.2 ⟨u.1, by
    have h1 := (mem_units.mp (Finset.mem_filter.mp (Finset.mem_sdiff.mp hu).1).1).2
    omega, hx⟩

theorem cc_le {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (b : Fin 14 → ℕ)
    (hb : PureBranch 14 D b) (x : Fin 14) :
    (sem_W 14 D x).card + (merges 14 D (carrierT 14 D {x})).card ≤ 2 + (ru D b x).card := by
  have h1 := sem_code_count sem_g14_gr h (sem_g14_comp hD) b hb x
  have h2 := Finset.card_le_card
    (Finset.inter_subset_left : ({x} : Finset (Fin 14)) ∩ eligSet 14 D ⊆ {x})
  rw [Finset.card_singleton] at h2
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

theorem as_mem {D : Dag} {pos : Fin 14 → ℕ × Bool} (hpos : k4_Pos 14 G14 D pos)
    {i a : Fin 14} (hi : i ∈ ineligSet 14 D) (hia : Adj i a) : pos i ∈ sem_W 14 D a := by
  obtain ⟨h1, h2, h4, -⟩ := hpos.1 i hi
  exact sem_mem_W.2 ⟨h1, h4 a hia, by rw [h2]; exact Finset.notMem_empty a⟩

theorem as_priv {D : Dag} {pos : Fin 14 → ℕ × Bool} (hpos : k4_Pos 14 G14 D pos)
    {i t : Fin 14} (hi : i ∈ ineligSet 14 D) (ht : sem_bar (pos i) ∈ sem_W 14 D t) : t = i := by
  have := (sem_mem_W.1 ht).2.1
  rw [show src D (sem_bar (pos i)) = src D ((pos i).1, !(pos i).2) from rfl,
    (hpos.1 i hi).2.2.2] at this
  exact Finset.mem_singleton.1 this

theorem as_W {D : Dag} (h : StrictLive 14 D) (hD : Correct D) {pos : Fin 14 → ℕ × Bool}
    (hpos : k4_Pos 14 G14 D pos) {i : Fin 14} (hi : i ∈ ineligSet 14 D) :
    sem_W 14 D i = {sem_bar (pos i)} := by
  obtain ⟨e, -, -, -, -, -, h6, -⟩ :=
    sem_inelig_consumer sem_g14_gr h (sem_g14_comp hD) hi
  obtain ⟨h1, h2, -, h5⟩ := hpos.1 i hi
  have hm : sem_bar (pos i) ∈ sem_W 14 D i :=
    sem_mem_W.2 ⟨h1, by
      rw [show src D (sem_bar (pos i)) = src D ((pos i).1, !(pos i).2) from rfl, h5]
      exact Finset.mem_singleton_self i, by
      rw [show (sem_bar (pos i)).1 = (pos i).1 from rfl, h2]; exact Finset.notMem_empty i⟩
  have h7 : sem_W 14 D i = {e} := h6
  rw [h7] at hm ⊢
  rw [Finset.mem_singleton.1 hm]

theorem full_g14 {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (hB0 : Bzero 14 D = 0)
    {pos : Fin 14 → ℕ × Bool} (hpos : k4_Pos 14 G14 D pos) {i v : Fin 14}
    (hi : i ∈ ineligSet 14 D) (hiv : Adj i v)
    (hv : ∀ p ∈ sem_W 14 D v, p.1 ≠ (pos i).1 → ¬ supp 14 D (src D (sem_bar p)) ⊆ {i}) :
    ∀ t, t ∈ supp 14 D (src D (pos i)) ↔ Adj i t := by
  have := full_gen sem_g14_gr h (sem_g14_comp hD) hB0 hi (as_W h hD hpos hi) hiv hv
  rwa [sem_bar_bar] at this

theorem pa_card3 {α : Type} [DecidableEq α] {s : Finset α} {a b c : α} (ha : a ∈ s)
    (hb : b ∈ s) (hc : c ∈ s) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : 3 ≤ s.card := by
  have hsub : ({a, b, c} : Finset α) ⊆ s := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl <;> assumption
  have := Finset.card_le_card hsub
  rwa [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc] at this

theorem pa_card4 {α : Type} [DecidableEq α] {s : Finset α} {a b c d : α}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hd : d ∈ s)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    4 ≤ s.card := by
  have hsub : ({a, b, c, d} : Finset α) ⊆ s := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl <;> assumption
  have := Finset.card_le_card hsub
  rwa [Finset.card_insert_of_notMem (by simp [hab, hac, had]),
    Finset.card_insert_of_notMem (by simp [hbc, hbd]), Finset.card_pair hcd] at this

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

theorem pa_ed {D : Dag} (h : StrictLive 14 D) (hD : Correct D) {pos : Fin 14 → ℕ × Bool}
    (hpos : k4_Pos 14 G14 D pos) {x y : Fin 14} (hxy : Adj x y) :
    ∃ e ∈ sem_W 14 D x, sem_bar e ∈ sem_W 14 D y ∧
      (∀ i ∈ ineligSet 14 D, e = pos i → y = i) ∧
      ∀ i ∈ ineligSet 14 D, sem_bar e = pos i → x = i := by
  obtain ⟨e, he, hb, -⟩ := sem_edge_slots sem_g14_gr h.1 (sem_g14_comp hD) hxy
  exact ⟨e, he, hb, fun i hi hei => as_priv hpos hi (hei ▸ hb),
    fun i hi hei => as_priv hpos hi (by rw [← hei, sem_bar_bar]; exact he)⟩

theorem g14_deg3_third : ∀ x a b : Fin 14, (g14_nbB x).card = 3 →
    x ≠ a → x ≠ b → hc_adjB a b = false →
    ∃ y, hc_adjB x y = true ∧ hc_adjB y a = false ∧ hc_adjB y b = false := by decide +kernel

theorem g14_deg3_cover_free {D : Dag} (h : StrictLive 14 D) (hD : Correct D) {x a b : Fin 14}
    (hd : (g14_nbB x).card = 3) (hxa : x ≠ a) (hxb : x ≠ b) (hab : ¬ Adj a b) :
    ∃ e, e ∈ sem_W 14 D x ∧ a ∉ supp 14 D (src D e) ∧ b ∉ supp 14 D (src D e) := by
  obtain ⟨y, h1, h2, h3⟩ := g14_deg3_third x a b hd hxa hxb (sem_adjB_false.mpr hab)
  exact sem_cover_free sem_g14_gr h.1 (sem_g14_comp hD) hab ((hc_adjB_iff x y).mp h1)
    (sem_adjB_false.mp h2) (sem_adjB_false.mp h3)

theorem ps_nonadj {D : Dag} (h : StrictLive 14 D) (hD : Correct D) {pos : Fin 14 → ℕ × Bool}
    (hpos : k4_Pos 14 G14 D pos) {i x r : Fin 14} (hi : i ∈ ineligSet 14 D)
    (hix : Adj i x) (hir : Adj i r) (hrx : r ≠ x) (hdx : (g14_nbB x).card = 3)
    (hc : (sem_W 14 D x).card ≤ 2) :
    ∃ Z, Z ≠ pos i ∧ sem_W 14 D x = {pos i, Z} ∧
      ∀ t, t ≠ x → ¬ Adj r t → Z ∉ sem_W 14 D t := by
  obtain ⟨Z, hZ, hZr⟩ := sem_antichain sem_g14_gr h.1 (sem_g14_comp hD) (x := x) (a := r) (Ne.symm hrx)
  have hY : pos i ∈ sem_W 14 D x := as_mem hpos hi hix
  have hZY : Z ≠ pos i := fun heq => hZr (heq ▸ (hpos.1 i hi).2.2.1 r hir)
  have hW : sem_W 14 D x = {pos i, Z} := by
    symm
    refine Finset.eq_of_subset_of_card_le (fun f hf => ?_) ?_
    · rw [Finset.mem_insert, Finset.mem_singleton] at hf
      rcases hf with rfl | rfl
      · exact hY
      · exact hZ
    · rw [Finset.card_pair (Ne.symm hZY)]; exact hc
  refine ⟨Z, hZY, hW, fun t htx hrt hZt => ?_⟩
  obtain ⟨f, hf, h1, h2⟩ := g14_deg3_cover_free h hD hdx (Ne.symm hrx) (Ne.symm htx) hrt
  rw [hW, Finset.mem_insert, Finset.mem_singleton] at hf
  rcases hf with rfl | rfl
  · exact h1 ((hpos.1 i hi).2.2.1 r hir)
  · exact h2 (sem_mem_W.1 hZt).2.1

theorem ps_side {D : Dag} (h : StrictLive 14 D) (hD : Correct D) {pos : Fin 14 → ℕ × Bool}
    (hpos : k4_Pos 14 G14 D pos) {i x : Fin 14} (hi : i ∈ ineligSet 14 D)
    (hix : Adj i x) (hdx : (g14_nbB x).card = 3) (hc : (sem_W 14 D x).card ≤ 2) :
    ∃ Z, Z ≠ pos i ∧ sem_W 14 D x = {pos i, Z} ∧
      ∀ t, t ≠ x → decide (t.val < 7) = decide (x.val < 7) → Z ∉ sem_W 14 D t := by
  obtain ⟨r, hir, hrx⟩ := sem_g14_gr.2.2.2 i x
  obtain ⟨Z, hZY, hW, hp⟩ := ps_nonadj h hD hpos hi hix hir hrx hdx hc
  refine ⟨Z, hZY, hW, fun t htx hside => hp t htx (fun hadj => ?_)⟩
  have s1 := g14_sides i x ((hc_adjB_iff i x).2 hix)
  have s2 := g14_sides i r ((hc_adjB_iff i r).2 hir)
  have s3 := g14_sides r t ((hc_adjB_iff r t).2 hadj)
  cases h1 : decide (i.val < 7) <;> cases h2 : decide (x.val < 7) <;>
    cases h3 : decide (r.val < 7) <;> cases h4 : decide (t.val < 7) <;> simp_all

theorem two_in_deg3 {D : Dag} (h : StrictLive 14 D) (hD : Correct D) {pos : Fin 14 → ℕ × Bool}
    (hpos : k4_Pos 14 G14 D pos) {i1 i2 u v : Fin 14}
    (hi1 : i1 ∈ ineligSet 14 D) (hi2 : i2 ∈ ineligSet 14 D)
    (hg : i1 ≠ i2 ∧ hc_adjB i1 u = true ∧ hc_adjB i2 u = true ∧ hc_adjB u v = true ∧
      v ≠ i1 ∧ v ≠ i2) : 3 ≤ (sem_W 14 D u).card := by
  obtain ⟨hne, h1, h2, h3, hv1, hv2⟩ := hg
  rw [hc_adjB_iff] at h1 h2 h3
  have p1 := as_mem hpos hi1 h1
  have p2 := as_mem hpos hi2 h2
  have p12 : pos i1 ≠ pos i2 := fun e => hne (hpos.2 i1 hi1 i2 hi2 e)
  by_cases hv : v ∈ ineligSet 14 D
  · exact pa_card3 p1 p2 (as_mem hpos hv (adj_symm h3)) p12
      (fun e => hv1.symm (hpos.2 i1 hi1 v hv e)) (fun e => hv2.symm (hpos.2 i2 hi2 v hv e))
  · obtain ⟨e, he, -, hf, -⟩ := pa_ed h hD hpos h3
    exact pa_card3 p1 p2 he p12 (fun hh => hv (hf i1 hi1 hh.symm ▸ hi1))
      (fun hh => hv (hf i2 hi2 hh.symm ▸ hi2))

/-- Full support of `pos i` at a `two_in_deg3` vertex `u` when `Bzero = 0` and `|W_u| ≤ 3`. -/
theorem full_of_two_in_deg3 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hB0 : Bzero 14 D = 0) {pos : Fin 14 → ℕ × Bool} (hpos : k4_Pos 14 G14 D pos)
    {i1 i2 u v : Fin 14} (hi1 : i1 ∈ ineligSet 14 D) (hi2 : i2 ∈ ineligSet 14 D)
    (hg : i1 ≠ i2 ∧ hc_adjB i1 u = true ∧ hc_adjB i2 u = true ∧ hc_adjB u v = true ∧
      v ≠ i1 ∧ v ≠ i2) (hcu : (sem_W 14 D u).card ≤ 3) :
    (∀ t, t ∈ supp 14 D (src D (pos i1)) → Adj i1 t) ∧
    (∀ t, t ∈ supp 14 D (src D (pos i2)) → Adj i2 t) := by
  obtain ⟨hne, h1, h2, h3, hv1, hv2⟩ := hg
  rw [hc_adjB_iff] at h1 h2 h3
  have hfull : ∀ (ia ib : Fin 14), ia ∈ ineligSet 14 D → ib ∈ ineligSet 14 D → ia ≠ ib →
      Adj ia u → Adj ib u → v ≠ ia → v ≠ ib →
      ∀ t, t ∈ supp 14 D (src D (pos ia)) → Adj ia t := by
    intro ia ib hia hib hab hiau hibu hvia hvib t ht
    have pa := as_mem hpos hia hiau
    have pb := as_mem hpos hib hibu
    have pab : pos ia ≠ pos ib := fun e => hab (hpos.2 ia hia ib hib e)
    have hspec : ∀ t, t ∈ supp 14 D (src D (pos ia)) ↔ Adj ia t := by
      refine full_g14 h hD hB0 hpos hia hiau (fun p hp hne1 hsub => ?_)
      by_cases hv : v ∈ ineligSet 14 D
      · have pv := as_mem hpos hv (adj_symm h3)
        have pav : pos ia ≠ pos v := fun e => hvia.symm (hpos.2 ia hia v hv e)
        have pbv : pos ib ≠ pos v := fun e => hvib.symm (hpos.2 ib hib v hv e)
        rcases pa_three pa pb pv pab pav pbv hcu p hp with rfl | rfl | rfl
        · exact hne1 rfl
        · have hm : ib ∈ supp 14 D (src D (sem_bar (pos ib))) := by
            rw [show src D (sem_bar (pos ib)) = src D ((pos ib).1, !(pos ib).2) from rfl,
              (hpos.1 ib hib).2.2.2]; exact Finset.mem_singleton_self ib
          exact hab.symm (Finset.mem_singleton.1 (hsub hm))
        · have hm : v ∈ supp 14 D (src D (sem_bar (pos v))) := by
            rw [show src D (sem_bar (pos v)) = src D ((pos v).1, !(pos v).2) from rfl,
              (hpos.1 v hv).2.2.2]; exact Finset.mem_singleton_self v
          exact hvia (Finset.mem_singleton.1 (hsub hm))
      · obtain ⟨e, he, hbe, hf, -⟩ := pa_ed h hD hpos h3
        have pae : pos ia ≠ e := fun hh => hv (hf ia hia hh.symm ▸ hia)
        have pbe : pos ib ≠ e := fun hh => hv (hf ib hib hh.symm ▸ hib)
        rcases pa_three pa pb he pab pae pbe hcu p hp with rfl | rfl | rfl
        · exact hne1 rfl
        · have hm : ib ∈ supp 14 D (src D (sem_bar (pos ib))) := by
            rw [show src D (sem_bar (pos ib)) = src D ((pos ib).1, !(pos ib).2) from rfl,
              (hpos.1 ib hib).2.2.2]; exact Finset.mem_singleton_self ib
          exact hab.symm (Finset.mem_singleton.1 (hsub hm))
        · exact hv (Finset.mem_singleton.1 (hsub (sem_mem_W.1 hbe).2.1) ▸ hia)
    exact (hspec t).1 ht
  exact ⟨hfull i1 i2 hi1 hi2 hne h1 h2 hv1 hv2, hfull i2 i1 hi2 hi1 hne.symm h2 h1 hv2 hv1⟩

theorem pa_m1 {D : Dag} (h : StrictLive 14 D) (hD : Correct D) {pos : Fin 14 → ℕ × Bool}
    (hpos : k4_Pos 14 G14 D pos) (z k v iz ik : Fin 14)
    (hiz : iz ∈ ineligSet 14 D) (hik : ik ∈ ineligSet 14 D)
    (hz : z ∉ ineligSet 14 D) (hk : k ∉ ineligSet 14 D) (hv : v ∉ ineligSet 14 D)
    (hg : hc_adjB iz z = true ∧ hc_adjB ik k = true ∧ hc_adjB z k = true ∧
      hc_adjB z v = true ∧ v ≠ k ∧ (g14_nbB k).card = 3 ∧
      decide (v.val < 7) = decide (k.val < 7))
    (hcz : (sem_W 14 D z).card ≤ 2) (hck : (sem_W 14 D k).card ≤ 2) : False := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := hg
  rw [hc_adjB_iff] at g1 g2 g3 g4
  obtain ⟨Dk, -, hWk, hpk⟩ := ps_side h hD hpos hik g2 g6 hck
  obtain ⟨e, he, hbe, hf, hf'⟩ := pa_ed h hD hpos g3
  obtain ⟨e', he', hbe', hg', -⟩ := pa_ed h hD hpos g4
  rw [hWk, Finset.mem_insert, Finset.mem_singleton] at hbe
  have hb : sem_bar e = Dk := hbe.resolve_left (fun hh => hz (hf' ik hik hh ▸ hik))
  rcases pa_two (as_mem hpos hiz g1) he (fun hh => hk (hf iz hiz hh.symm ▸ hiz)) hcz e' he'
    with h1 | h1
  · exact hv (hg' iz hiz h1 ▸ hiz)
  · exact hpk v g5 g7 (by rw [← hb, ← h1]; exact hbe')

theorem ps_side_3star {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    {pos : Fin 14 → ℕ × Bool} (hpos : k4_Pos 14 G14 D pos)
    (u k1 k2 v ik1 ik2 : Fin 14)
    (hik1 : ik1 ∈ ineligSet 14 D) (hik2 : ik2 ∈ ineligSet 14 D)
    (hu : u ∉ ineligSet 14 D)
    (hg : hc_adjB u k1 = true ∧ hc_adjB u k2 = true ∧ hc_adjB u v = true ∧
      hc_adjB ik1 k1 = true ∧ hc_adjB ik2 k2 = true ∧
      k1 ≠ k2 ∧ v ≠ k1 ∧ v ≠ k2 ∧
      (g14_nbB k1).card = 3 ∧ (g14_nbB k2).card = 3 ∧
      decide (k1.val < 7) = decide (k2.val < 7) ∧ decide (v.val < 7) = decide (k1.val < 7))
    (hcu : (sem_W 14 D u).card ≤ 2) (hck1 : (sem_W 14 D k1).card ≤ 2)
    (hck2 : (sem_W 14 D k2).card ≤ 2) : False := by
  obtain ⟨g1, g2, g3, g4, g5, hk12, hvk1, hvk2, hd1, hd2, hs12, hsv1⟩ := hg
  rw [hc_adjB_iff] at g1 g2 g3 g4 g5
  obtain ⟨D1, -, hW1, hp1⟩ := ps_side h hD hpos hik1 g4 hd1 hck1
  obtain ⟨D2, -, hW2, hp2⟩ := ps_side h hD hpos hik2 g5 hd2 hck2
  obtain ⟨e1, he1, hbe1, -, hf1'⟩ := pa_ed h hD hpos g1
  obtain ⟨e2, he2, hbe2, -, hf2'⟩ := pa_ed h hD hpos g2
  obtain ⟨e3, he3, hbe3, -, -⟩ := pa_ed h hD hpos g3
  rw [hW1, Finset.mem_insert, Finset.mem_singleton] at hbe1
  have hb1 : sem_bar e1 = D1 := hbe1.resolve_left (fun hh => hu (hf1' ik1 hik1 hh ▸ hik1))
  rw [hW2, Finset.mem_insert, Finset.mem_singleton] at hbe2
  have hb2 : sem_bar e2 = D2 := hbe2.resolve_left (fun hh => hu (hf2' ik2 hik2 hh ▸ hik2))
  have he12 : e1 ≠ e2 := fun heq => by
    have hD12 : D1 = D2 := by rw [← hb1, ← hb2, heq]
    have hD2in : D2 ∈ sem_W 14 D k2 := by rw [hW2]; simp
    exact hp1 k2 hk12.symm hs12.symm (hD12 ▸ hD2in)
  rcases pa_two he1 he2 he12 hcu e3 he3 with rfl | rfl
  · exact hp1 v hvk1 hsv1 (hb1 ▸ hbe3)
  · exact hp2 v hvk2 (hsv1.trans hs12) (hb2 ▸ hbe3)

/-! ### Tight witness table and `tight_le_all` -/

def tight_wit (idx : Fin 143) : Bool × Fin 14 × Fin 14 × Fin 14 × Fin 14 × Fin 14 :=
  match idx.val with
  | 0 => (true, 8, 0, 2, 6, 0)
  | 1 => (true, 0, 0, 0, 0, 0)
  | 2 => (true, 8, 0, 2, 6, 0)
  | 3 => (true, 13, 1, 2, 4, 0)
  | 4 => (true, 10, 0, 4, 5, 0)
  | 5 => (true, 8, 0, 2, 6, 0)
  | 6 => (true, 13, 1, 2, 4, 0)
  | 7 => (true, 10, 0, 4, 5, 0)
  | 8 => (true, 11, 3, 4, 6, 0)
  | 9 => (true, 9, 1, 5, 6, 0)
  | 10 => (true, 9, 1, 5, 6, 0)
  | 11 => (true, 9, 1, 5, 6, 0)
  | 12 => (true, 8, 0, 6, 2, 0)
  | 13 => (true, 8, 0, 2, 6, 0)
  | 14 => (true, 8, 2, 6, 0, 0)
  | 15 => (true, 8, 0, 6, 2, 0)
  | 16 => (true, 9, 1, 6, 5, 0)
  | 17 => (true, 8, 0, 6, 2, 0)
  | 18 => (true, 9, 1, 6, 5, 0)
  | 19 => (true, 11, 3, 4, 6, 0)
  | 20 => (true, 9, 1, 5, 6, 0)
  | 21 => (true, 8, 0, 2, 6, 0)
  | 22 => (true, 10, 0, 4, 5, 0)
  | 23 => (true, 13, 2, 4, 1, 0)
  | 24 => (true, 10, 0, 5, 4, 0)
  | 25 => (false, 1, 9, 13, 7, 5)
  | 26 => (true, 10, 4, 5, 0, 0)
  | 27 => (true, 8, 0, 6, 2, 0)
  | 28 => (true, 8, 2, 6, 0, 0)
  | 29 => (true, 11, 4, 6, 3, 0)
  | 30 => (true, 9, 5, 6, 1, 0)
  | 31 => (false, 6, 9, 11, 8, 1)
  | 32 => (true, 13, 1, 4, 2, 0)
  | 33 => (true, 11, 3, 4, 6, 0)
  | 34 => (true, 9, 1, 5, 6, 0)
  | 35 => (false, 1, 13, 9, 7, 4)
  | 36 => (false, 1, 9, 13, 7, 5)
  | 37 => (true, 8, 0, 2, 6, 0)
  | 38 => (true, 10, 0, 4, 5, 0)
  | 39 => (true, 11, 3, 4, 6, 0)
  | 40 => (true, 13, 1, 2, 4, 0)
  | 41 => (false, 4, 11, 13, 10, 3)
  | 42 => (true, 9, 1, 6, 5, 0)
  | 43 => (true, 8, 2, 6, 0, 0)
  | 44 => (true, 11, 3, 6, 4, 0)
  | 45 => (false, 1, 9, 13, 7, 6)
  | 46 => (true, 8, 0, 2, 6, 0)
  | 47 => (true, 13, 1, 2, 4, 0)
  | 48 => (true, 9, 1, 5, 6, 0)
  | 49 => (true, 8, 0, 2, 6, 0)
  | 50 => (true, 8, 0, 2, 6, 0)
  | 51 => (true, 10, 0, 4, 5, 0)
  | 52 => (true, 8, 0, 2, 6, 0)
  | 53 => (true, 11, 3, 4, 6, 0)
  | 54 => (true, 8, 0, 2, 6, 0)
  | 55 => (true, 9, 1, 5, 6, 0)
  | 56 => (true, 9, 1, 5, 6, 0)
  | 57 => (true, 9, 1, 5, 6, 0)
  | 58 => (true, 8, 0, 2, 6, 0)
  | 59 => (true, 8, 0, 6, 2, 0)
  | 60 => (true, 8, 0, 2, 6, 0)
  | 61 => (true, 8, 2, 6, 0, 0)
  | 62 => (true, 8, 0, 6, 2, 0)
  | 63 => (true, 8, 0, 2, 6, 0)
  | 64 => (true, 8, 2, 6, 0, 0)
  | 65 => (true, 8, 0, 6, 2, 0)
  | 66 => (true, 9, 1, 6, 5, 0)
  | 67 => (true, 8, 0, 6, 2, 0)
  | 68 => (true, 9, 1, 5, 6, 0)
  | 69 => (true, 9, 1, 5, 6, 0)
  | 70 => (true, 8, 0, 2, 6, 0)
  | 71 => (true, 8, 0, 2, 6, 0)
  | 72 => (true, 10, 0, 4, 5, 0)
  | 73 => (true, 10, 4, 5, 0, 0)
  | 74 => (true, 8, 0, 2, 6, 0)
  | 75 => (true, 8, 0, 6, 2, 0)
  | 76 => (true, 8, 2, 6, 0, 0)
  | 77 => (true, 8, 0, 6, 2, 0)
  | 78 => (true, 8, 2, 6, 0, 0)
  | 79 => (true, 9, 5, 6, 1, 0)
  | 80 => (true, 11, 3, 4, 6, 0)
  | 81 => (true, 9, 1, 5, 6, 0)
  | 82 => (true, 9, 1, 5, 6, 0)
  | 83 => (true, 10, 4, 5, 0, 0)
  | 84 => (true, 8, 0, 2, 6, 0)
  | 85 => (true, 8, 0, 2, 6, 0)
  | 86 => (true, 10, 0, 4, 5, 0)
  | 87 => (true, 1, 7, 9, 13, 0)
  | 88 => (true, 1, 7, 9, 13, 0)
  | 89 => (true, 1, 7, 9, 13, 0)
  | 90 => (true, 6, 8, 9, 11, 0)
  | 91 => (true, 13, 1, 2, 4, 0)
  | 92 => (true, 8, 2, 6, 0, 0)
  | 93 => (true, 9, 1, 6, 5, 0)
  | 94 => (true, 8, 2, 6, 0, 0)
  | 95 => (true, 8, 2, 6, 0, 0)
  | 96 => (false, 4, 11, 13, 10, 3)
  | 97 => (true, 8, 0, 2, 6, 0)
  | 98 => (true, 9, 1, 5, 6, 0)
  | 99 => (true, 3, 7, 11, 12, 0)
  | 100 => (true, 3, 7, 11, 12, 0)
  | 101 => (true, 6, 8, 11, 9, 0)
  | 102 => (true, 6, 9, 11, 8, 0)
  | 103 => (true, 4, 10, 11, 13, 0)
  | 104 => (true, 3, 7, 12, 11, 0)
  | 105 => (true, 5, 10, 12, 9, 0)
  | 106 => (true, 8, 0, 2, 6, 0)
  | 107 => (true, 8, 0, 2, 6, 0)
  | 108 => (true, 8, 0, 2, 6, 0)
  | 109 => (true, 9, 1, 5, 6, 0)
  | 110 => (true, 8, 0, 2, 6, 0)
  | 111 => (true, 8, 0, 2, 6, 0)
  | 112 => (true, 8, 0, 6, 2, 0)
  | 113 => (true, 8, 0, 2, 6, 0)
  | 114 => (true, 8, 2, 6, 0, 0)
  | 115 => (true, 8, 0, 2, 6, 0)
  | 116 => (true, 8, 0, 6, 2, 0)
  | 117 => (true, 8, 0, 6, 2, 0)
  | 118 => (true, 9, 1, 5, 6, 0)
  | 119 => (true, 8, 0, 2, 6, 0)
  | 120 => (true, 8, 0, 2, 6, 0)
  | 121 => (true, 8, 0, 2, 6, 0)
  | 122 => (true, 8, 0, 6, 2, 0)
  | 123 => (true, 8, 2, 6, 0, 0)
  | 124 => (true, 9, 1, 5, 6, 0)
  | 125 => (true, 8, 0, 2, 6, 0)
  | 126 => (true, 1, 7, 9, 13, 0)
  | 127 => (true, 8, 2, 6, 0, 0)
  | 128 => (true, 8, 0, 2, 6, 0)
  | 129 => (true, 3, 7, 11, 12, 0)
  | 130 => (true, 1, 7, 9, 13, 0)
  | 131 => (true, 3, 7, 12, 11, 0)
  | 132 => (true, 3, 7, 12, 11, 0)
  | 133 => (true, 5, 10, 12, 9, 0)
  | 134 => (true, 8, 0, 2, 6, 0)
  | 135 => (true, 8, 0, 2, 6, 0)
  | 136 => (true, 8, 0, 2, 6, 0)
  | 137 => (true, 8, 0, 2, 6, 0)
  | 138 => (true, 8, 0, 6, 2, 0)
  | 139 => (true, 8, 0, 2, 6, 0)
  | 140 => (true, 3, 7, 12, 11, 0)
  | 141 => (true, 1, 7, 9, 13, 0)
  | _ => (true, 8, 0, 2, 6, 0)

theorem tight_wit_ok : ∀ idx : Fin 143, idx.val ≠ 1 →
    let I := hc_rep idx
    let (isW3, a, b, c, d, e) := tight_wit idx
    if isW3 then
      b ∈ I ∧ c ∈ I ∧ b ≠ c ∧ hc_adjB b a = true ∧ hc_adjB c a = true ∧
        hc_adjB a d = true ∧ d ≠ b ∧ d ≠ c
    else
      d ∈ I ∧ e ∈ I ∧ a ∉ I ∧ b ∉ I ∧ c ∉ I ∧
        hc_adjB d a = true ∧ hc_adjB e b = true ∧ hc_adjB a b = true ∧
        hc_adjB a c = true ∧ c ≠ b ∧ (g14_nbB b).card = 3 ∧
        decide (c.val < 7) = decide (b.val < 7) := by
  decide +kernel

theorem tight_le_idx {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hB : Bplus 14 D ≤ (eligSet 14 D).card)
    (idx : Fin 143) (hI : ineligSet 14 D = hc_rep idx) (h1 : idx.val ≠ 1) :
    False := by
  classical
  obtain ⟨b, hb⟩ := exists_pureBranch h hD
  obtain ⟨pos, hpos⟩ := k4_assigned sem_g14_gr h (sem_g14_comp hD)
  have hres : residualUnits 14 D b = ∅ := by
    have h1' := card_residual h.1 b hb
    have h2' := elig_le_Bplus h.1 b hb
    exact Finset.card_eq_zero.1 (by omega)
  have hW2 : ∀ x, (sem_W 14 D x).card ≤ 2 := fun x => by
    have h1' := cc_le h hD b hb x
    unfold ru at h1'
    rw [hres] at h1'
    simp only [Finset.filter_empty, Finset.card_empty] at h1'
    omega
  have hw := tight_wit_ok idx h1
  dsimp only at hw
  rcases htw : tight_wit idx with ⟨isW3, a, b', c, d, e⟩
  rw [htw] at hw
  cases isW3
  · simp only [Bool.false_eq_true, ↓reduceIte] at hw
    obtain ⟨hd, he, ha, hb', hc', hg⟩ := hw
    exact pa_m1 h hD hpos a b' c d e (hI ▸ hd) (hI ▸ he) (hI ▸ ha) (hI ▸ hb') (hI ▸ hc') hg
      (hW2 a) (hW2 b')
  · simp only [↓reduceIte] at hw
    obtain ⟨hi1, hi2, hg⟩ := hw
    have h3 := two_in_deg3 h hD hpos (hI ▸ hi1) (hI ▸ hi2) hg
    have := hW2 a; omega

theorem elim_res0_3star {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hB : Bplus 14 D ≤ (eligSet 14 D).card) (idx : Fin 143) (hI : ineligSet 14 D = hc_rep idx)
    (hidx : idx.val = 1) : False := by
  classical
  obtain ⟨b, hb⟩ := exists_pureBranch h hD
  obtain ⟨pos, hpos⟩ := k4_assigned sem_g14_gr h (sem_g14_comp hD)
  have hres : residualUnits 14 D b = ∅ := by
    have h1' := card_residual h.1 b hb
    have h2' := elig_le_Bplus h.1 b hb
    exact Finset.card_eq_zero.1 (by omega)
  have hW2 : ∀ x, (sem_W 14 D x).card ≤ 2 := fun x => by
    have h1' := cc_le h hD b hb x
    unfold ru at h1'
    rw [hres] at h1'
    simp only [Finset.filter_empty, Finset.card_empty] at h1'
    omega
  have hrep : ∀ i : Fin 143, i.val = 1 → hc_rep i = {0, 1, 3} := by decide +kernel
  have hIeq : ineligSet 14 D = {0, 1, 3} := hI.trans (hrep idx hidx)
  exact ps_side_3star h hD hpos 4 10 11 13 0 3
    (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
    (by decide) (hW2 4) (hW2 10) (hW2 11)

theorem tight_le_all {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hB : Bplus 14 D ≤ (eligSet 14 D).card) (idx : Fin 143) (hI : ineligSet 14 D = hc_rep idx) :
    False := by
  by_cases h1 : idx.val = 1
  · exact elim_res0_3star h hD hB idx hI h1
  · exact tight_le_idx h hD hB idx hI h1

/-! ### One residual unit setup (`pa_setup_one`) and `|I| = 4` elimination -/

def pa_ctx (D : Dag) (pos : Fin 14 → ℕ × Bool) (P Q : ℕ × Bool) : Prop :=
  k4_Pos 14 G14 D pos ∧ (∀ x, (sem_W 14 D x).card ≤ 3) ∧ P ≠ Q ∧
    ∀ x, 3 ≤ (sem_W 14 D x).card → P ∈ sem_W 14 D x ∧ Q ∈ sem_W 14 D x

theorem pa_setup_one {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hB : Bplus 14 D = (eligSet 14 D).card + 1) : ∃ pos P Q, pa_ctx D pos P Q := by
  classical
  have hG := sem_g14_gr
  have hC := sem_g14_comp hD
  obtain ⟨b, hb⟩ := sem_exists_minBranch hG h.1 hC
  have hbp := sem_minBranch_pure hb
  obtain ⟨pos, hpos⟩ := k4_assigned hG h hC
  have h1 := card_residual h.1 b hbp
  have hc3 : ∀ x, (sem_W 14 D x).card ≤ 3 := fun x => by
    have h3 := cc_le h hD b hbp x
    have h4 : (ru D b x).card ≤ (residualUnits 14 D b).card := Finset.card_filter_le _ _
    omega
  by_cases hX : (Finset.univ.filter (fun x : Fin 14 => 3 ≤ (sem_W 14 D x).card)).Nonempty
  · obtain ⟨P, Q, hPQ, hall⟩ := sem_common_terminals hG h hC b hb (by omega) _ hX
      (fun x hx => (Finset.mem_filter.1 hx).2)
    exact ⟨pos, P, Q, hpos, hc3, fun hpq => hPQ (hpq ▸ rfl),
      fun x hx => hall x (Finset.mem_filter.2 ⟨Finset.mem_univ x, hx⟩)⟩
  · refine ⟨pos, (0, false), (0, true), hpos, hc3, by decide, fun x hx => ?_⟩
    exact absurd ⟨x, Finset.mem_filter.2 ⟨Finset.mem_univ x, hx⟩⟩ hX

/-- At `|I| = 4`, `Bplus = 11` and `Bzero = 0` are forced. -/
theorem res1_setup_c4 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h11 : totalSurplus 14 D ≤ 11) (idx : Fin 143) (hI : ineligSet 14 D = hc_rep idx)
    (hc4 : (ineligSet 14 D).card = 4) :
    Bzero 14 D = 0 ∧ ∃ pos P Q, pa_ctx D pos P Q := by
  have hel := inelig_card_add 14 D
  have hts := totalSurplus_split 14 D
  have hBgt : (eligSet 14 D).card + 1 ≤ Bplus 14 D := by
    by_contra hle; exact tight_le_all h hD (by omega) idx hI
  have hB1 : Bplus 14 D = (eligSet 14 D).card + 1 := by omega
  have hB0 : Bzero 14 D = 0 := by omega
  exact ⟨hB0, pa_setup_one h hD hB1⟩

/-- Helper: in `pa_ctx` with `Bzero = 0`, at a `two_in_deg3` vertex `x` with `i1, i2 ∈ N(x) ∩ I`,
at least one of `pos i1, pos i2` lies in `{P, Q}` and only belongs to `W_t` when `Adj i t`. -/
theorem two_in_deg3_pick_PQ {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hB0 : Bzero 14 D = 0) {pos : Fin 14 → ℕ × Bool} {P Q : ℕ × Bool}
    (hctx : pa_ctx D pos P Q) {i1 i2 x v3 : Fin 14}
    (hi1 : i1 ∈ ineligSet 14 D) (hi2 : i2 ∈ ineligSet 14 D)
    (hg : i1 ≠ i2 ∧ hc_adjB i1 x = true ∧ hc_adjB i2 x = true ∧ hc_adjB x v3 = true ∧
      v3 ≠ i1 ∧ v3 ≠ i2) :
    ((∀ t, 3 ≤ (sem_W 14 D t).card → Adj i1 t) ∨
     (∀ t, 3 ≤ (sem_W 14 D t).card → Adj i2 t)) := by
  obtain ⟨hpos, hc3, hPQ, hsat⟩ := hctx
  have h3 := two_in_deg3 h hD hpos hi1 hi2 hg
  obtain ⟨hPx, hQx⟩ := hsat x h3
  obtain ⟨hf1, hf2⟩ := full_of_two_in_deg3 h hD hB0 hpos hi1 hi2 hg (hc3 x)
  obtain ⟨hne, h1, h2, h3e, hv1, hv2⟩ := hg
  rw [hc_adjB_iff] at h1 h2 h3e
  have p1 := as_mem hpos hi1 h1
  have p2 := as_mem hpos hi2 h2
  have p12 : pos i1 ≠ pos i2 := fun e => hne (hpos.2 i1 hi1 i2 hi2 e)
  -- Either P or Q equals pos i1 or pos i2 (since |W_x| ≤ 3 has at most one third element!).
  have hpick : pos i1 = P ∨ pos i1 = Q ∨ pos i2 = P ∨ pos i2 = Q := by
    by_contra hno
    push Not at hno
    have h4 := pa_card4 p1 p2 hPx hQx p12 hno.1 hno.2.1 hno.2.2.1 hno.2.2.2 hPQ
    have := hc3 x; omega
  rcases hpick with e | e | e | e
  · exact Or.inl (fun t ht => hf1 t (sem_mem_W.1 (e ▸ (hsat t ht).1)).2.1)
  · exact Or.inl (fun t ht => hf1 t (sem_mem_W.1 (e ▸ (hsat t ht).2)).2.1)
  · exact Or.inr (fun t ht => hf2 t (sem_mem_W.1 (e ▸ (hsat t ht).1)).2.1)
  · exact Or.inr (fun t ht => hf2 t (sem_mem_W.1 (e ▸ (hsat t ht).2)).2.1)

def no_i0_4_idx (k : Fin 52) : Fin 143 :=
  match k.val with
  | 0 => ⟨50, by decide⟩
  | 1 => ⟨52, by decide⟩
  | 2 => ⟨53, by decide⟩
  | 3 => ⟨54, by decide⟩
  | 4 => ⟨56, by decide⟩
  | 5 => ⟨57, by decide⟩
  | 6 => ⟨58, by decide⟩
  | 7 => ⟨60, by decide⟩
  | 8 => ⟨61, by decide⟩
  | 9 => ⟨62, by decide⟩
  | 10 => ⟨63, by decide⟩
  | 11 => ⟨64, by decide⟩
  | 12 => ⟨65, by decide⟩
  | 13 => ⟨66, by decide⟩
  | 14 => ⟨67, by decide⟩
  | 15 => ⟨68, by decide⟩
  | 16 => ⟨69, by decide⟩
  | 17 => ⟨70, by decide⟩
  | 18 => ⟨71, by decide⟩
  | 19 => ⟨72, by decide⟩
  | 20 => ⟨73, by decide⟩
  | 21 => ⟨74, by decide⟩
  | 22 => ⟨75, by decide⟩
  | 23 => ⟨76, by decide⟩
  | 24 => ⟨77, by decide⟩
  | 25 => ⟨78, by decide⟩
  | 26 => ⟨79, by decide⟩
  | 27 => ⟨80, by decide⟩
  | 28 => ⟨81, by decide⟩
  | 29 => ⟨82, by decide⟩
  | 30 => ⟨83, by decide⟩
  | 31 => ⟨84, by decide⟩
  | 32 => ⟨85, by decide⟩
  | 33 => ⟨86, by decide⟩
  | 34 => ⟨87, by decide⟩
  | 35 => ⟨88, by decide⟩
  | 36 => ⟨89, by decide⟩
  | 37 => ⟨90, by decide⟩
  | 38 => ⟨91, by decide⟩
  | 39 => ⟨92, by decide⟩
  | 40 => ⟨93, by decide⟩
  | 41 => ⟨94, by decide⟩
  | 42 => ⟨95, by decide⟩
  | 43 => ⟨97, by decide⟩
  | 44 => ⟨98, by decide⟩
  | 45 => ⟨99, by decide⟩
  | 46 => ⟨100, by decide⟩
  | 47 => ⟨101, by decide⟩
  | 48 => ⟨102, by decide⟩
  | 49 => ⟨103, by decide⟩
  | 50 => ⟨104, by decide⟩
  | _ => ⟨105, by decide⟩

def no_i0_4_wit (k : Fin 52) :
    Fin 14 × Fin 14 × Fin 14 × Fin 14 ×
    (Bool × Fin 14 × Fin 14 × Fin 14 × Fin 14 × Fin 14) ×
    (Bool × Fin 14 × Fin 14 × Fin 14 × Fin 14 × Fin 14) :=
  match k.val with
  | 0 => (8, 0, 2, 6, (true, 13, 1, 2, 4, 0), (true, 10, 0, 4, 5, 0))
  | 1 => (8, 0, 2, 6, (true, 11, 3, 4, 6, 0), (true, 10, 0, 4, 5, 0))
  | 2 => (13, 1, 2, 4, (true, 11, 3, 4, 6, 0), (true, 11, 3, 4, 6, 0))
  | 3 => (8, 0, 2, 6, (true, 9, 1, 5, 6, 0), (true, 9, 1, 5, 6, 0))
  | 4 => (9, 1, 5, 6, (true, 10, 0, 4, 5, 0), (true, 13, 1, 4, 2, 0))
  | 5 => (9, 1, 5, 6, (true, 10, 4, 5, 0, 0), (true, 11, 3, 4, 6, 0))
  | 6 => (8, 0, 2, 6, (true, 9, 1, 6, 5, 0), (true, 9, 1, 6, 5, 0))
  | 7 => (8, 0, 2, 6, (true, 11, 3, 6, 4, 0), (true, 11, 3, 6, 4, 0))
  | 8 => (8, 2, 6, 0, (true, 9, 1, 6, 5, 0), (true, 13, 1, 2, 4, 0))
  | 9 => (8, 0, 6, 2, (true, 9, 1, 6, 5, 0), (true, 10, 0, 4, 5, 0))
  | 10 => (8, 0, 2, 6, (true, 11, 4, 6, 3, 0), (true, 10, 0, 4, 5, 0))
  | 11 => (8, 2, 6, 0, (true, 9, 1, 6, 5, 0), (true, 13, 1, 2, 4, 0))
  | 12 => (8, 0, 6, 2, (true, 11, 3, 4, 6, 0), (true, 10, 0, 4, 5, 0))
  | 13 => (9, 1, 6, 5, (true, 11, 3, 4, 6, 0), (true, 13, 1, 4, 2, 0))
  | 14 => (8, 0, 6, 2, (true, 9, 1, 5, 6, 0), (true, 10, 0, 5, 4, 0))
  | 15 => (9, 1, 5, 6, (true, 11, 3, 6, 4, 0), (true, 11, 3, 6, 4, 0))
  | 16 => (9, 1, 5, 6, (true, 10, 4, 5, 0, 0), (true, 11, 4, 6, 3, 0))
  | 17 => (8, 0, 2, 6, (true, 13, 2, 4, 1, 0), (true, 10, 0, 4, 5, 0))
  | 18 => (8, 0, 2, 6, (false, 1, 9, 13, 7, 5), (true, 10, 0, 5, 4, 0))
  | 19 => (10, 0, 4, 5, (false, 1, 9, 13, 7, 5), (false, 1, 9, 13, 7, 5))
  | 20 => (10, 4, 5, 0, (false, 1, 9, 13, 7, 5), (true, 13, 2, 4, 1, 0))
  | 21 => (8, 0, 2, 6, (false, 1, 9, 13, 7, 6), (false, 1, 9, 13, 7, 6))
  | 22 => (8, 0, 6, 2, (true, 11, 4, 6, 3, 0), (true, 10, 0, 4, 5, 0))
  | 23 => (8, 2, 6, 0, (true, 11, 4, 6, 3, 0), (true, 13, 2, 4, 1, 0))
  | 24 => (8, 0, 6, 2, (true, 9, 5, 6, 1, 0), (true, 10, 0, 5, 4, 0))
  | 25 => (8, 2, 6, 0, (true, 9, 5, 6, 1, 0), (false, 1, 13, 9, 7, 2))
  | 26 => (9, 5, 6, 1, (true, 11, 4, 6, 3, 0), (true, 10, 4, 5, 0, 0))
  | 27 => (11, 3, 4, 6, (true, 13, 1, 4, 2, 0), (false, 6, 9, 11, 8, 1))
  | 28 => (9, 1, 5, 6, (false, 6, 11, 9, 8, 3), (false, 6, 11, 9, 8, 3))
  | 29 => (9, 1, 5, 6, (true, 10, 4, 5, 0, 0), (true, 13, 1, 4, 2, 0))
  | 30 => (10, 4, 5, 0, (false, 1, 9, 13, 7, 5), (false, 1, 13, 9, 7, 4))
  | 31 => (8, 0, 2, 6, (false, 1, 13, 7, 9, 2), (false, 5, 10, 12, 9, 0))
  | 32 => (8, 0, 2, 6, (true, 13, 2, 4, 1, 0), (true, 10, 0, 4, 5, 0))
  | 33 => (10, 0, 4, 5, (true, 11, 3, 4, 6, 0), (false, 6, 8, 11, 9, 0))
  | 34 => (1, 7, 9, 13, (true, 8, 0, 2, 6, 0), (true, 8, 0, 2, 6, 0))
  | 35 => (1, 7, 9, 13, (true, 10, 0, 4, 5, 0), (true, 10, 0, 4, 5, 0))
  | 36 => (1, 7, 9, 13, (true, 13, 2, 4, 1, 0), (true, 13, 2, 4, 1, 0))
  | 37 => (6, 8, 9, 11, (true, 11, 3, 4, 6, 0), (true, 11, 3, 4, 6, 0))
  | 38 => (13, 1, 2, 4, (false, 4, 11, 13, 10, 3), (false, 4, 11, 13, 10, 3))
  | 39 => (8, 2, 6, 0, (true, 9, 1, 6, 5, 0), (true, 13, 1, 2, 4, 0))
  | 40 => (9, 1, 6, 5, (true, 11, 3, 6, 4, 0), (false, 4, 13, 11, 10, 1))
  | 41 => (8, 2, 6, 0, (true, 11, 3, 6, 4, 0), (false, 4, 13, 11, 10, 2))
  | 42 => (8, 2, 6, 0, (false, 1, 9, 13, 7, 6), (false, 1, 13, 9, 7, 2))
  | 43 => (8, 0, 2, 6, (true, 13, 1, 2, 4, 0), (false, 4, 10, 13, 11, 0))
  | 44 => (9, 1, 5, 6, (true, 10, 0, 5, 4, 0), (false, 4, 13, 10, 11, 1))
  | 45 => (3, 7, 11, 12, (true, 8, 0, 2, 6, 0), (true, 8, 0, 2, 6, 0))
  | 46 => (3, 7, 11, 12, (true, 10, 0, 5, 4, 0), (true, 10, 0, 5, 4, 0))
  | 47 => (6, 8, 11, 9, (true, 9, 1, 5, 6, 0), (true, 9, 1, 5, 6, 0))
  | 48 => (6, 9, 11, 8, (true, 8, 0, 2, 6, 0), (true, 8, 0, 2, 6, 0))
  | 49 => (4, 10, 11, 13, (true, 13, 1, 2, 4, 0), (true, 13, 1, 2, 4, 0))
  | 50 => (3, 7, 12, 11, (true, 8, 0, 2, 6, 0), (true, 8, 0, 2, 6, 0))
  | _ => (5, 10, 12, 9, (true, 13, 1, 2, 4, 0), (true, 13, 1, 2, 4, 0))

abbrev kw_ok (I : Finset (Fin 14)) (i0 : Fin 14)
    (kw : Bool × Fin 14 × Fin 14 × Fin 14 × Fin 14 × Fin 14) : Prop :=
  if kw.1 then
    kw.2.2.1 ∈ I ∧ kw.2.2.2.1 ∈ I ∧ hc_adjB i0 kw.2.1 = false ∧
      (kw.2.2.1 ≠ kw.2.2.2.1 ∧ hc_adjB kw.2.2.1 kw.2.1 = true ∧ hc_adjB kw.2.2.2.1 kw.2.1 = true ∧
       hc_adjB kw.2.1 kw.2.2.2.2.1 = true ∧ kw.2.2.2.2.1 ≠ kw.2.2.1 ∧ kw.2.2.2.2.1 ≠ kw.2.2.2.1)
  else
    kw.2.2.2.2.1 ∈ I ∧ kw.2.2.2.2.2 ∈ I ∧ kw.2.1 ∉ I ∧ kw.2.2.1 ∉ I ∧ kw.2.2.2.1 ∉ I ∧
      hc_adjB i0 kw.2.1 = false ∧ hc_adjB i0 kw.2.2.1 = false ∧
      (hc_adjB kw.2.2.2.2.1 kw.2.1 = true ∧ hc_adjB kw.2.2.2.2.2 kw.2.2.1 = true ∧
       hc_adjB kw.2.1 kw.2.2.1 = true ∧ hc_adjB kw.2.1 kw.2.2.2.1 = true ∧
       kw.2.2.2.1 ≠ kw.2.2.1 ∧ (g14_nbB kw.2.2.1).card = 3 ∧
       decide (kw.2.2.2.1.val < 7) = decide (kw.2.2.1.val < 7))

theorem no_i0_4_ok_base : ∀ k : Fin 52,
    let I := hc_rep (no_i0_4_idx k)
    let w := no_i0_4_wit k
    I.card = 4 ∧ w.2.1 ∈ I ∧ w.2.2.1 ∈ I ∧
      (w.2.1 ≠ w.2.2.1 ∧ hc_adjB w.2.1 w.1 = true ∧ hc_adjB w.2.2.1 w.1 = true ∧
       hc_adjB w.1 w.2.2.2.1 = true ∧ w.2.2.2.1 ≠ w.2.1 ∧ w.2.2.2.1 ≠ w.2.2.1) := by
  decide +kernel

theorem no_i0_4_ok_k1 : ∀ k : Fin 52,
    kw_ok (hc_rep (no_i0_4_idx k)) (no_i0_4_wit k).2.1 (no_i0_4_wit k).2.2.2.2.1 := by
  decide +kernel

theorem no_i0_4_ok_k2 : ∀ k : Fin 52,
    kw_ok (hc_rep (no_i0_4_idx k)) (no_i0_4_wit k).2.2.1 (no_i0_4_wit k).2.2.2.2.2 := by
  decide +kernel

theorem elim_no_i0_4 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h11 : totalSurplus 14 D ≤ 11) (k : Fin 52)
    (hI : ineligSet 14 D = hc_rep (no_i0_4_idx k)) : False := by
  obtain ⟨hc4, hi1, hi2, hgx⟩ := no_i0_4_ok_base k
  have hk1 := no_i0_4_ok_k1 k
  have hk2 := no_i0_4_ok_k2 k
  obtain ⟨hB0, pos, P, Q, hctx⟩ := res1_setup_c4 h hD h11 (no_i0_4_idx k) hI (hI ▸ hc4)
  have hkill : ∀ (i0 : Fin 14) (kw : Bool × Fin 14 × Fin 14 × Fin 14 × Fin 14 × Fin 14),
      (∀ t, 3 ≤ (sem_W 14 D t).card → Adj i0 t) →
      kw_ok (hc_rep (no_i0_4_idx k)) i0 kw → False := by
    intro i0 kw hall hkw
    rcases kw with ⟨isW3, a, b', c, d, e⟩
    unfold kw_ok at hkw
    cases isW3
    · simp only [Bool.false_eq_true, ↓reduceIte] at hkw
      obtain ⟨hd, he, ha, hb, hc, hna, hnb, hga⟩ := hkw
      have hca : (sem_W 14 D a).card ≤ 2 := by
        by_contra hlt; exact sem_adjB_false.1 hna (hall a (by omega))
      have hcb : (sem_W 14 D b').card ≤ 2 := by
        by_contra hlt; exact sem_adjB_false.1 hnb (hall b' (by omega))
      exact pa_m1 h hD hctx.1 a b' c d e (hI ▸ hd) (hI ▸ he) (hI ▸ ha) (hI ▸ hb) (hI ▸ hc)
        hga hca hcb
    · simp only [↓reduceIte] at hkw
      obtain ⟨hb, hc, hna, hga⟩ := hkw
      have h3 := two_in_deg3 h hD hctx.1 (hI ▸ hb) (hI ▸ hc) hga
      exact sem_adjB_false.1 hna (hall a h3)
  rcases two_in_deg3_pick_PQ h hD hB0 hctx (hI ▸ hi1) (hI ▸ hi2) hgx with h1 | h2
  · exact hkill _ _ h1 hk1
  · exact hkill _ _ h2 hk2

/-! ### `|I| ≥ 4` counting eliminations (`cnt_b1_R`, `bplus_p1_R`, `cnt_b2_R`) -/

def cnt_b1_idx (k : Fin 31) : Fin 143 :=
  match k.val with
  | 0 => ⟨49, by decide⟩
  | 1 => ⟨51, by decide⟩
  | 2 => ⟨55, by decide⟩
  | 3 => ⟨59, by decide⟩
  | 4 => ⟨106, by decide⟩
  | 5 => ⟨107, by decide⟩
  | 6 => ⟨108, by decide⟩
  | 7 => ⟨109, by decide⟩
  | 8 => ⟨110, by decide⟩
  | 9 => ⟨111, by decide⟩
  | 10 => ⟨112, by decide⟩
  | 11 => ⟨113, by decide⟩
  | 12 => ⟨114, by decide⟩
  | 13 => ⟨115, by decide⟩
  | 14 => ⟨116, by decide⟩
  | 15 => ⟨117, by decide⟩
  | 16 => ⟨118, by decide⟩
  | 17 => ⟨119, by decide⟩
  | 18 => ⟨122, by decide⟩
  | 19 => ⟨123, by decide⟩
  | 20 => ⟨124, by decide⟩
  | 21 => ⟨125, by decide⟩
  | 22 => ⟨127, by decide⟩
  | 23 => ⟨128, by decide⟩
  | 24 => ⟨134, by decide⟩
  | 25 => ⟨135, by decide⟩
  | 26 => ⟨136, by decide⟩
  | 27 => ⟨137, by decide⟩
  | 28 => ⟨138, by decide⟩
  | 29 => ⟨139, by decide⟩
  | _ => ⟨142, by decide⟩
def bplus_p1_idx (k : Fin 27) : Fin 143 :=
  match k.val with
  | 0 => ⟨106, by decide⟩
  | 1 => ⟨107, by decide⟩
  | 2 => ⟨108, by decide⟩
  | 3 => ⟨109, by decide⟩
  | 4 => ⟨110, by decide⟩
  | 5 => ⟨111, by decide⟩
  | 6 => ⟨112, by decide⟩
  | 7 => ⟨113, by decide⟩
  | 8 => ⟨114, by decide⟩
  | 9 => ⟨115, by decide⟩
  | 10 => ⟨116, by decide⟩
  | 11 => ⟨117, by decide⟩
  | 12 => ⟨118, by decide⟩
  | 13 => ⟨119, by decide⟩
  | 14 => ⟨122, by decide⟩
  | 15 => ⟨123, by decide⟩
  | 16 => ⟨124, by decide⟩
  | 17 => ⟨125, by decide⟩
  | 18 => ⟨127, by decide⟩
  | 19 => ⟨128, by decide⟩
  | 20 => ⟨134, by decide⟩
  | 21 => ⟨135, by decide⟩
  | 22 => ⟨136, by decide⟩
  | 23 => ⟨137, by decide⟩
  | 24 => ⟨138, by decide⟩
  | 25 => ⟨139, by decide⟩
  | _ => ⟨142, by decide⟩
def cnt_b2_idx (k : Fin 3) : Fin 143 :=
  match k.val with
  | 0 => ⟨120, by decide⟩
  | 1 => ⟨121, by decide⟩
  | _ => ⟨133, by decide⟩

theorem cnt_b1_comb : ∀ k : Fin 31, ∀ m : Fin 128,
    let I := hc_rep (cnt_b1_idx k)
    let P := sideR \ I
    let Oc := maskFin7 m
    (∀ j ∈ Oc, g14_nbB (os_ptL j) ⊆ P) →
    let Oc3 := Oc.filter (fun j => (g14_nbB (os_ptL j)).card = 3)
    let Oc2 := Oc.filter (fun j => (g14_nbB (os_ptL j)).card = 2)
    let Ct := (Finset.univ : Finset (Fin 7)) \ Oc
    let Iin := Finset.univ.filter (fun j : Fin 7 => os_ptL j ∈ I ∧ g14_nbB (os_ptL j) ⊆ P)
    let Lab := Ct.biUnion (fun j => g14_nbB (os_ptL j) ∩ P)
    (2 * P.card + 11 < 2 * Oc3.card + Oc2.card + Iin.card + Lab.card + (14 - I.card) + (Iin \ Oc).card) ∨
    (11 < (15 - I.card) + (Iin \ Oc).card) := by
  decide +kernel

theorem elim_cnt_b1 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h11 : totalSurplus 14 D ≤ 11) (k : Fin 31)
    (hI : ineligSet 14 D = hc_rep (cnt_b1_idx k)) : False := by
  have hBgt : (eligSet 14 D).card + 1 ≤ Bplus 14 D := by
    by_contra hle; exact tight_le_all h hD (by omega) (cnt_b1_idx k) hI
  obtain ⟨m, hsub, hcnt, hlost⟩ := g14_sideR_step h hD
  have hcomb := cnt_b1_comb k m
  dsimp only at hcomb hsub hcnt hlost
  rw [← hI] at hcomb
  have hts := totalSurplus_split 14 D
  have hel := inelig_card_add 14 D
  rcases hcomb hsub with h1 | h2 <;> omega

theorem bplus_p1_comb : ∀ k : Fin 27, ∀ m : Fin 128,
    let I := hc_rep (bplus_p1_idx k)
    let P := sideR \ I
    let Oc := maskFin7 m
    (∀ j ∈ Oc, g14_nbB (os_ptL j) ⊆ P) →
    let Oc3 := Oc.filter (fun j => (g14_nbB (os_ptL j)).card = 3)
    let Oc2 := Oc.filter (fun j => (g14_nbB (os_ptL j)).card = 2)
    let Ct := (Finset.univ : Finset (Fin 7)) \ Oc
    let Iin := Finset.univ.filter (fun j : Fin 7 => os_ptL j ∈ I ∧ g14_nbB (os_ptL j) ⊆ P)
    let Lab := Ct.biUnion (fun j => g14_nbB (os_ptL j) ∩ P)
    (2 * P.card + 1 < 2 * Oc3.card + Oc2.card + Iin.card + Lab.card) ∨
    (11 < (15 - I.card) + (Iin \ Oc).card) := by
  decide +kernel

theorem bplus_gt_p1_of_cnt {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h11 : totalSurplus 14 D ≤ 11) (k : Fin 27)
    (hI : ineligSet 14 D = hc_rep (bplus_p1_idx k)) :
    (eligSet 14 D).card + 2 ≤ Bplus 14 D := by
  by_contra hle
  have hBgt : (eligSet 14 D).card + 1 ≤ Bplus 14 D := by
    by_contra hle0; exact tight_le_all h hD (by omega) (bplus_p1_idx k) hI
  have hB1 : Bplus 14 D = (eligSet 14 D).card + 1 := by omega
  obtain ⟨m, hsub, hcnt, hlost⟩ := g14_sideR_step h hD
  have hcomb := bplus_p1_comb k m
  dsimp only at hcomb hsub hcnt hlost
  rw [← hI] at hcomb
  have hts := totalSurplus_split 14 D
  have hel := inelig_card_add 14 D
  rcases hcomb hsub with h1 | h2 <;> omega

/-- `Bzero`-free elimination of `Bplus = p + 1` for two adjacent `two_in_deg3` vertices (`129, 132, 133`). -/
theorem elim_adj_w3_p1 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hB1 : Bplus 14 D = (eligSet 14 D).card + 1)
    (x y ix1 ix2 iy1 iy2 : Fin 14)
    (hix1 : ix1 ∈ ineligSet 14 D) (hix2 : ix2 ∈ ineligSet 14 D)
    (hiy1 : iy1 ∈ ineligSet 14 D) (hiy2 : iy2 ∈ ineligSet 14 D)
    (hx : x ∉ ineligSet 14 D) (hy : y ∉ ineligSet 14 D)
    (hg : ix1 ≠ ix2 ∧ iy1 ≠ iy2 ∧ ix1 ≠ iy1 ∧ ix1 ≠ iy2 ∧ ix2 ≠ iy1 ∧ ix2 ≠ iy2 ∧
      hc_adjB ix1 x = true ∧ hc_adjB ix2 x = true ∧ hc_adjB iy1 y = true ∧ hc_adjB iy2 y = true ∧
      hc_adjB x y = true) : False := by
  obtain ⟨h12, h34, h13, h14, h23, h24, gx1, gx2, gy1, gy2, gxy⟩ := hg
  rw [hc_adjB_iff] at gx1 gx2 gy1 gy2 gxy
  obtain ⟨pos, P, Q, hpos, hc3, hPQ, hsat⟩ := pa_setup_one h hD hB1
  obtain ⟨H, hHx, hHy, hfy, hfx⟩ := pa_ed h hD hpos gxy
  have px1 := as_mem hpos hix1 gx1; have px2 := as_mem hpos hix2 gx2
  have py1 := as_mem hpos hiy1 gy1; have py2 := as_mem hpos hiy2 gy2
  have nx : pos ix1 ≠ pos ix2 := fun e => h12 (hpos.2 _ hix1 _ hix2 e)
  have ny : pos iy1 ≠ pos iy2 := fun e => h34 (hpos.2 _ hiy1 _ hiy2 e)
  have hx1H : pos ix1 ≠ H := fun e => hy (hfy _ hix1 e.symm ▸ hix1)
  have hx2H : pos ix2 ≠ H := fun e => hy (hfy _ hix2 e.symm ▸ hix2)
  have hy1H : pos iy1 ≠ sem_bar H := fun e => hx (hfx _ hiy1 e.symm ▸ hiy1)
  have hy2H : pos iy2 ≠ sem_bar H := fun e => hx (hfx _ hiy2 e.symm ▸ hiy2)
  have hWx := pa_three px1 px2 hHx nx hx1H hx2H (hc3 x)
  have hWy := pa_three py1 py2 hHy ny hy1H hy2H (hc3 y)
  have h3x := pa_card3 px1 px2 hHx nx hx1H hx2H
  have h3y := pa_card3 py1 py2 hHy ny hy1H hy2H
  have hdisj : ∀ e ∈ sem_W 14 D x, e ∉ sem_W 14 D y := by
    intro e hex hey
    rcases hWx e hex with rfl | rfl | rfl <;> rcases hWy _ hey with he | he | he
    · exact h13 (hpos.2 _ hix1 _ hiy1 he)
    · exact h14 (hpos.2 _ hix1 _ hiy2 he)
    · exact hx (hfx _ hix1 he.symm ▸ hix1)
    · exact h23 (hpos.2 _ hix2 _ hiy1 he)
    · exact h24 (hpos.2 _ hix2 _ hiy2 he)
    · exact hx (hfx _ hix2 he.symm ▸ hix2)
    · exact hy (hfy _ hiy1 he ▸ hiy1)
    · exact hy (hfy _ hiy2 he ▸ hiy2)
    · exact w_bar h.1 hHx (he ▸ hHx)
  exact hdisj P (hsat x h3x).1 (hsat y h3y).1

/-- `Bzero`-free elimination of `Bplus = p + 1` for 3 `two_in_deg3` vertices forming a triangle on `I` (`128`). -/
theorem elim_tri_w3_p1 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hB1 : Bplus 14 D = (eligSet 14 D).card + 1)
    (x y z i1 i2 i3 vx vy vz : Fin 14)
    (hi1 : i1 ∈ ineligSet 14 D) (hi2 : i2 ∈ ineligSet 14 D) (hi3 : i3 ∈ ineligSet 14 D)
    (hvx : vx ∉ ineligSet 14 D) (hvy : vy ∉ ineligSet 14 D) (hvz : vz ∉ ineligSet 14 D)
    (hg : i1 ≠ i2 ∧ i1 ≠ i3 ∧ i2 ≠ i3 ∧
      hc_adjB i1 x = true ∧ hc_adjB i2 x = true ∧ hc_adjB x vx = true ∧
      hc_adjB i1 y = true ∧ hc_adjB i3 y = true ∧ hc_adjB y vy = true ∧
      hc_adjB i2 z = true ∧ hc_adjB i3 z = true ∧ hc_adjB z vz = true) : False := by
  obtain ⟨h12, h13, h23, gx1, gx2, gxv, gy1, gy3, gyv, gz2, gz3, gzv⟩ := hg
  rw [hc_adjB_iff] at gx1 gx2 gxv gy1 gy3 gyv gz2 gz3 gzv
  obtain ⟨pos, P, Q, hpos, hc3, hPQ, hsat⟩ := pa_setup_one h hD hB1
  obtain ⟨Hx, hHx, -, hfx, -⟩ := pa_ed h hD hpos gxv
  obtain ⟨Hy, hHy, -, hfy, -⟩ := pa_ed h hD hpos gyv
  obtain ⟨Hz, hHz, -, hfz, -⟩ := pa_ed h hD hpos gzv
  have px1 := as_mem hpos hi1 gx1; have px2 := as_mem hpos hi2 gx2
  have py1 := as_mem hpos hi1 gy1; have py3 := as_mem hpos hi3 gy3
  have pz2 := as_mem hpos hi2 gz2; have pz3 := as_mem hpos hi3 gz3
  have n12 : pos i1 ≠ pos i2 := fun e => h12 (hpos.2 _ hi1 _ hi2 e)
  have n13 : pos i1 ≠ pos i3 := fun e => h13 (hpos.2 _ hi1 _ hi3 e)
  have n23 : pos i2 ≠ pos i3 := fun e => h23 (hpos.2 _ hi2 _ hi3 e)
  have hx1 : pos i1 ≠ Hx := fun e => hvx (hfx _ hi1 e.symm ▸ hi1)
  have hx2 : pos i2 ≠ Hx := fun e => hvx (hfx _ hi2 e.symm ▸ hi2)
  have hy1 : pos i1 ≠ Hy := fun e => hvy (hfy _ hi1 e.symm ▸ hi1)
  have hy3 : pos i3 ≠ Hy := fun e => hvy (hfy _ hi3 e.symm ▸ hi3)
  have hz2 : pos i2 ≠ Hz := fun e => hvz (hfz _ hi2 e.symm ▸ hi2)
  have hz3 : pos i3 ≠ Hz := fun e => hvz (hfz _ hi3 e.symm ▸ hi3)
  have hWx := pa_three px1 px2 hHx n12 hx1 hx2 (hc3 x)
  have hWy := pa_three py1 py3 hHy n13 hy1 hy3 (hc3 y)
  have hWz := pa_three pz2 pz3 hHz n23 hz2 hz3 (hc3 z)
  have h3x := pa_card3 px1 px2 hHx n12 hx1 hx2
  have h3y := pa_card3 py1 py3 hHy n13 hy1 hy3
  have h3z := pa_card3 pz2 pz3 hHz n23 hz2 hz3
  have honly : ∀ e, e ∈ sem_W 14 D x → e ∈ sem_W 14 D y → e ∈ sem_W 14 D z → e = Hx := by
    intro e hex hey hez
    rcases hWx e hex with rfl | rfl | rfl
    · rcases hWz _ hez with h | h | h
      · exact absurd h n12
      · exact absurd h n13
      · exact absurd (hfz _ hi1 h.symm ▸ hi1) hvz
    · rcases hWy _ hey with h | h | h
      · exact absurd h.symm n12
      · exact absurd h n23
      · exact absurd (hfy _ hi2 h.symm ▸ hi2) hvy
    · rfl
  exact hPQ ((honly P (hsat x h3x).1 (hsat y h3y).1 (hsat z h3z).1).trans
    (honly Q (hsat x h3x).2 (hsat y h3y).2 (hsat z h3z).2).symm)

/-- `Bzero`-free elimination of `Bplus = p + 1` for 2 `two_in_deg3` vertices sharing 1 `I`-neighbor
whose 3rd neighbors lie on the same side and satisfy `ps_side` (`124, 130`). -/
theorem elim_share_w3_ps_p1 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hB1 : Bplus 14 D = (eligSet 14 D).card + 1)
    (x y i0 i1 i2 vx vy iv : Fin 14)
    (hi0 : i0 ∈ ineligSet 14 D) (hi1 : i1 ∈ ineligSet 14 D) (hi2 : i2 ∈ ineligSet 14 D)
    (hiv : iv ∈ ineligSet 14 D) (hvx : vx ∉ ineligSet 14 D) (hvy : vy ∉ ineligSet 14 D)
    (hg : i0 ≠ i1 ∧ i0 ≠ i2 ∧ i1 ≠ i2 ∧ vx ≠ vy ∧
      hc_adjB i0 x = true ∧ hc_adjB i1 x = true ∧ hc_adjB x vx = true ∧
      hc_adjB i0 y = true ∧ hc_adjB i2 y = true ∧ hc_adjB y vy = true ∧
      hc_adjB iv vx = true ∧ (g14_nbB vx).card = 3 ∧
      decide (vy.val < 7) = decide (vx.val < 7)) : False := by
  obtain ⟨h01, h02, h12, hvxy, gx0, gx1, gxv, gy0, gy2, gyv, giv, hdvx, hsv⟩ := hg
  rw [hc_adjB_iff] at gx0 gx1 gxv gy0 gy2 gyv giv
  obtain ⟨pos, P, Q, hpos, hc3, hPQ, hsat⟩ := pa_setup_one h hD hB1
  obtain ⟨Hx, hHx, hbx, hfx, hfx'⟩ := pa_ed h hD hpos gxv
  obtain ⟨Hy, hHy, hby, hfy, -⟩ := pa_ed h hD hpos gyv
  have px0 := as_mem hpos hi0 gx0; have px1 := as_mem hpos hi1 gx1
  have py0 := as_mem hpos hi0 gy0; have py2 := as_mem hpos hi2 gy2
  have n01 : pos i0 ≠ pos i1 := fun e => h01 (hpos.2 _ hi0 _ hi1 e)
  have n02 : pos i0 ≠ pos i2 := fun e => h02 (hpos.2 _ hi0 _ hi2 e)
  have n12 : pos i1 ≠ pos i2 := fun e => h12 (hpos.2 _ hi1 _ hi2 e)
  have hx0 : pos i0 ≠ Hx := fun e => hvx (hfx _ hi0 e.symm ▸ hi0)
  have hx1 : pos i1 ≠ Hx := fun e => hvx (hfx _ hi1 e.symm ▸ hi1)
  have hy0 : pos i0 ≠ Hy := fun e => hvy (hfy _ hi0 e.symm ▸ hi0)
  have hy2 : pos i2 ≠ Hy := fun e => hvy (hfy _ hi2 e.symm ▸ hi2)
  have hWx := pa_three px0 px1 hHx n01 hx0 hx1 (hc3 x)
  have hWy := pa_three py0 py2 hHy n02 hy0 hy2 (hc3 y)
  have h3x := pa_card3 px0 px1 hHx n01 hx0 hx1
  have h3y := pa_card3 py0 py2 hHy n02 hy0 hy2
  -- Every e ∈ W_x ∩ W_y is either pos i0 or Hx (with Hx = Hy)!
  have hxy_in : ∀ e, e ∈ sem_W 14 D x → e ∈ sem_W 14 D y → e = pos i0 ∨ (e = Hx ∧ Hx = Hy) := by
    intro e hex hey
    rcases hWx e hex with rfl | rfl | rfl
    · exact Or.inl rfl
    · rcases hWy _ hey with h | h | h
      · exact absurd h.symm n01
      · exact absurd h n12
      · exact absurd (hfy _ hi1 h.symm ▸ hi1) hvy
    · rcases hWy _ hey with h | h | h
      · exact absurd h.symm hx0
      · exact absurd (hfx _ hi2 h ▸ hi2) hvx
      · exact Or.inr ⟨rfl, h⟩
  have hHxEq : (P = Hx ∨ Q = Hx) ∧ Hx = Hy := by
    rcases hxy_in P (hsat x h3x).1 (hsat y h3y).1 with hP0 | ⟨hPH, hxy⟩
    · rcases hxy_in Q (hsat x h3x).2 (hsat y h3y).2 with hQ0 | ⟨hQH, hxy⟩
      · exact absurd (hP0.trans hQ0.symm) hPQ
      · exact ⟨Or.inr hQH, hxy⟩
    · exact ⟨Or.inl hPH, hxy⟩
  have hcvx : (sem_W 14 D vx).card ≤ 2 := by
    by_contra hlt
    have hge : 3 ≤ (sem_W 14 D vx).card := by omega
    have hHin : Hx ∈ sem_W 14 D vx := by
      rcases hHxEq.1 with rfl | rfl
      · exact (hsat vx hge).1
      · exact (hsat vx hge).2
    exact w_bar h.1 hHin hbx
  obtain ⟨Z, -, hWvx, hpvx⟩ := ps_side h hD hpos hiv giv hdvx hcvx
  have hbxZ : sem_bar Hx = Z := by
    rw [hWvx, Finset.mem_insert, Finset.mem_singleton] at hbx
    exact hbx.resolve_left (fun hh => by
      have hxI : x = iv := hfx' iv hiv hh
      have hxnot : x ∉ ineligSet 14 D := fun hxin =>
        (g14_cover_iff_indep D).1 (elig_isCover h hD) _ hxin _ hi0 (adj_symm gx0)
      exact hxnot (hxI ▸ hiv))
  exact hpvx vy hvxy.symm hsv (by rw [← hbxZ, hHxEq.2]; exact hby)

/-- `Bzero`-free elimination of `Bplus = p + 1` when `x` has all 3 neighbors in `I` and `y` has
2 disjoint neighbors in `I` + 3rd neighbor outside `I` (`132`). -/
theorem elim_all3_w3_p1 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hB1 : Bplus 14 D = (eligSet 14 D).card + 1)
    (x y ix1 ix2 ix3 iy1 iy2 vy : Fin 14)
    (hix1 : ix1 ∈ ineligSet 14 D) (hix2 : ix2 ∈ ineligSet 14 D) (hix3 : ix3 ∈ ineligSet 14 D)
    (hiy1 : iy1 ∈ ineligSet 14 D) (hiy2 : iy2 ∈ ineligSet 14 D)
    (hvy : vy ∉ ineligSet 14 D)
    (hg : ix1 ≠ ix2 ∧ ix1 ≠ ix3 ∧ ix2 ≠ ix3 ∧ iy1 ≠ iy2 ∧
      ix1 ≠ iy1 ∧ ix1 ≠ iy2 ∧ ix2 ≠ iy1 ∧ ix2 ≠ iy2 ∧ ix3 ≠ iy1 ∧ ix3 ≠ iy2 ∧
      hc_adjB ix1 x = true ∧ hc_adjB ix2 x = true ∧ hc_adjB ix3 x = true ∧
      hc_adjB iy1 y = true ∧ hc_adjB iy2 y = true ∧ hc_adjB y vy = true) : False := by
  obtain ⟨x12, x13, x23, y12, c11, c12, c21, c22, c31, c32, gx1, gx2, gx3, gy1, gy2, gyv⟩ := hg
  rw [hc_adjB_iff] at gx1 gx2 gx3 gy1 gy2 gyv
  obtain ⟨pos, P, Q, hpos, hc3, -, hsat⟩ := pa_setup_one h hD hB1
  obtain ⟨Hy, hHy, -, hfy, -⟩ := pa_ed h hD hpos gyv
  have px1 := as_mem hpos hix1 gx1; have px2 := as_mem hpos hix2 gx2; have px3 := as_mem hpos hix3 gx3
  have py1 := as_mem hpos hiy1 gy1; have py2 := as_mem hpos hiy2 gy2
  have nx12 : pos ix1 ≠ pos ix2 := fun e => x12 (hpos.2 _ hix1 _ hix2 e)
  have nx13 : pos ix1 ≠ pos ix3 := fun e => x13 (hpos.2 _ hix1 _ hix3 e)
  have nx23 : pos ix2 ≠ pos ix3 := fun e => x23 (hpos.2 _ hix2 _ hix3 e)
  have ny12 : pos iy1 ≠ pos iy2 := fun e => y12 (hpos.2 _ hiy1 _ hiy2 e)
  have hy1H : pos iy1 ≠ Hy := fun e => hvy (hfy _ hiy1 e.symm ▸ hiy1)
  have hy2H : pos iy2 ≠ Hy := fun e => hvy (hfy _ hiy2 e.symm ▸ hiy2)
  have hWx := pa_three px1 px2 px3 nx12 nx13 nx23 (hc3 x)
  have hWy := pa_three py1 py2 hHy ny12 hy1H hy2H (hc3 y)
  have h3x := pa_card3 px1 px2 px3 nx12 nx13 nx23
  have h3y := pa_card3 py1 py2 hHy ny12 hy1H hy2H
  rcases hWx P (hsat x h3x).1 with hP | hP | hP <;> rcases hWy P (hsat y h3y).1 with hQ | hQ | hQ
  · exact c11 (hpos.2 _ hix1 _ hiy1 (hP.symm.trans hQ))
  · exact c12 (hpos.2 _ hix1 _ hiy2 (hP.symm.trans hQ))
  · exact hvy (hfy _ hix1 (hQ.symm.trans hP) ▸ hix1)
  · exact c21 (hpos.2 _ hix2 _ hiy1 (hP.symm.trans hQ))
  · exact c22 (hpos.2 _ hix2 _ hiy2 (hP.symm.trans hQ))
  · exact hvy (hfy _ hix2 (hQ.symm.trans hP) ▸ hix2)
  · exact c31 (hpos.2 _ hix3 _ hiy1 (hP.symm.trans hQ))
  · exact c32 (hpos.2 _ hix3 _ hiy2 (hP.symm.trans hQ))
  · exact hvy (hfy _ hix3 (hQ.symm.trans hP) ▸ hix3)

theorem bplus_gt_p1_ge5 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h11 : totalSurplus 14 D ≤ 11) (idx : Fin 143) (hI : ineligSet 14 D = hc_rep idx)
    (hge5 : 106 ≤ idx.val) : (eligSet 14 D).card + 2 ≤ Bplus 14 D := by
  by_contra hle
  have hBgt : (eligSet 14 D).card + 1 ≤ Bplus 14 D := by
    by_contra hle0; exact tight_le_all h hD (by omega) idx hI
  have hB1 : Bplus 14 D = (eligSet 14 D).card + 1 := by omega
  have hcases_all : ∀ i : Fin 143, 106 ≤ i.val →
      (∃ k : Fin 27, bplus_p1_idx k = i) ∨
      i.val = 120 ∨ i.val = 121 ∨ i.val = 126 ∨ i.val = 129 ∨ i.val = 130 ∨
      i.val = 131 ∨ i.val = 132 ∨ i.val = 133 ∨ i.val = 140 ∨ i.val = 141 := by
    decide +kernel
  rcases hcases_all idx hge5 with
    ⟨k, rfl⟩ | h120 | h121 | h126 | h129 | h130 | h131 | h132 | h133 | h140 | h141
  · have := bplus_gt_p1_of_cnt h hD h11 k hI; omega
  · have hrep : ∀ i : Fin 143, i.val = 120 → hc_rep i = {0, 2, 4, 6, 7} := by decide +kernel
    have hIeq : ineligSet 14 D = {0, 2, 4, 6, 7} := hI.trans (hrep idx h120)
    exact elim_share_w3_ps_p1 h hD hB1 11 10 4 6 0 3 5 7
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide)
  · have hrep : ∀ i : Fin 143, i.val = 121 → hc_rep i = {0, 2, 5, 6, 7} := by decide +kernel
    have hIeq : ineligSet 14 D = {0, 2, 5, 6, 7} := hI.trans (hrep idx h121)
    exact elim_share_w3_ps_p1 h hD hB1 9 10 5 6 0 1 4 7
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide)
  · have hrep : ∀ i : Fin 143, i.val = 126 → hc_rep i = {0, 2, 4, 7, 9} := by decide +kernel
    have hIeq : ineligSet 14 D = {0, 2, 4, 7, 9} := hI.trans (hrep idx h126)
    exact elim_adj_w3_p1 h hD hB1 1 13 7 9 2 4
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide)
  · have hrep : ∀ i : Fin 143, i.val = 129 → hc_rep i = {0, 2, 5, 7, 11} := by decide +kernel
    have hIeq : ineligSet 14 D = {0, 2, 5, 7, 11} := hI.trans (hrep idx h129)
    exact elim_share_w3_ps_p1 h hD hB1 8 10 0 2 5 6 4 11
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide)
  · have hrep : ∀ i : Fin 143, i.val = 130 → hc_rep i = {0, 2, 7, 9, 11} := by decide +kernel
    have hIeq : ineligSet 14 D = {0, 2, 7, 9, 11} := hI.trans (hrep idx h130)
    exact elim_adj_w3_p1 h hD hB1 6 8 9 11 0 2
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide)
  · have hrep : ∀ i : Fin 143, i.val = 131 → hc_rep i = {0, 2, 4, 7, 12} := by decide +kernel
    have hIeq : ineligSet 14 D = {0, 2, 4, 7, 12} := hI.trans (hrep idx h131)
    exact elim_tri_w3_p1 h hD hB1 8 10 13 0 2 4 6 5 1
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide)
  · have hrep : ∀ i : Fin 143, i.val = 132 → hc_rep i = {0, 2, 6, 7, 12} := by decide +kernel
    have hIeq : ineligSet 14 D = {0, 2, 6, 7, 12} := hI.trans (hrep idx h132)
    exact elim_all3_w3_p1 h hD hB1 8 3 0 2 6 7 12 11
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide)
  · have hrep : ∀ i : Fin 143, i.val = 133 → hc_rep i = {1, 2, 6, 10, 12} := by decide +kernel
    have hIeq : ineligSet 14 D = {1, 2, 6, 10, 12} := hI.trans (hrep idx h133)
    exact elim_adj_w3_p1 h hD hB1 5 9 10 12 1 6
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide)
  · have hrep : ∀ i : Fin 143, i.val = 140 → hc_rep i = {0, 2, 4, 6, 7, 12} := by decide +kernel
    have hIeq : ineligSet 14 D = {0, 2, 4, 6, 7, 12} := hI.trans (hrep idx h140)
    exact elim_adj_w3_p1 h hD hB1 3 11 7 12 4 6
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide)
  · have hrep : ∀ i : Fin 143, i.val = 141 → hc_rep i = {0, 2, 4, 7, 9, 12} := by decide +kernel
    have hIeq : ineligSet 14 D = {0, 2, 4, 7, 9, 12} := hI.trans (hrep idx h141)
    exact elim_adj_w3_p1 h hD hB1 1 13 7 9 2 4
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide)

theorem cnt_b2_comb : ∀ k : Fin 3, ∀ m : Fin 128,
    let I := hc_rep (cnt_b2_idx k)
    let P := sideR \ I
    let Oc := maskFin7 m
    (∀ j ∈ Oc, g14_nbB (os_ptL j) ⊆ P) →
    let Oc3 := Oc.filter (fun j => (g14_nbB (os_ptL j)).card = 3)
    let Oc2 := Oc.filter (fun j => (g14_nbB (os_ptL j)).card = 2)
    let Ct := (Finset.univ : Finset (Fin 7)) \ Oc
    let Iin := Finset.univ.filter (fun j : Fin 7 => os_ptL j ∈ I ∧ g14_nbB (os_ptL j) ⊆ P)
    let Lab := Ct.biUnion (fun j => g14_nbB (os_ptL j) ∩ P)
    (2 * P.card + 11 < 2 * Oc3.card + Oc2.card + Iin.card + Lab.card + (14 - I.card) + (Iin \ Oc).card) ∨
    (11 < (16 - I.card) + (Iin \ Oc).card) := by
  decide +kernel

theorem cnt_b2_ge106 : ∀ k : Fin 3, 106 ≤ (cnt_b2_idx k).val := by decide +kernel

theorem elim_cnt_b2 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h11 : totalSurplus 14 D ≤ 11) (k : Fin 3)
    (hI : ineligSet 14 D = hc_rep (cnt_b2_idx k)) : False := by
  have hBgt := bplus_gt_p1_ge5 h hD h11 (cnt_b2_idx k) hI (cnt_b2_ge106 k)
  obtain ⟨m, hsub, hcnt, hlost⟩ := g14_sideR_step h hD
  have hcomb := cnt_b2_comb k m
  dsimp only at hcomb hsub hcnt hlost
  rw [← hI] at hcomb
  have hts := totalSurplus_split 14 D
  have hel := inelig_card_add 14 D
  rcases hcomb hsub with h1 | h2 <;> omega

theorem cnt_b2_130_comb : ∀ m : Fin 128,
    let I := hc_rep ⟨130, by decide⟩
    let P := sideL \ I
    let Oc := maskFin7 m
    (∀ j ∈ Oc, g14_nbB (os_ptR j) ⊆ P) →
    let Oc3 := Oc.filter (fun j => (g14_nbB (os_ptR j)).card = 3)
    let Oc2 := Oc.filter (fun j => (g14_nbB (os_ptR j)).card = 2)
    let Ct := (Finset.univ : Finset (Fin 7)) \ Oc
    let Iin := Finset.univ.filter (fun j : Fin 7 => os_ptR j ∈ I ∧ g14_nbB (os_ptR j) ⊆ P)
    let Lab := Ct.biUnion (fun j => g14_nbB (os_ptR j) ∩ P)
    (2 * P.card + 11 < 2 * Oc3.card + Oc2.card + Iin.card + Lab.card + (14 - I.card) + (Iin \ Oc).card) ∨
    (11 < (16 - I.card) + (Iin \ Oc).card) := by
  decide +kernel

theorem elim_130 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h11 : totalSurplus 14 D ≤ 11) (hI : ineligSet 14 D = hc_rep ⟨130, by decide⟩) : False := by
  have hBgt := bplus_gt_p1_ge5 h hD h11 ⟨130, by decide⟩ hI (by decide)
  obtain ⟨m, hsub, hcnt, hlost⟩ := g14_sideL_step h hD
  have hcomb := cnt_b2_130_comb m
  dsimp only at hcomb hsub hcnt hlost
  rw [← hI] at hcomb
  have hts := totalSurplus_split 14 D
  have hel := inelig_card_add 14 D
  rcases hcomb hsub with h1 | h2 <;> omega

/-! ### The 3 `res = 1` special orbits (`[0, 3, 9, 13]`, `[1, 3, 8, 10]`, `[0, 1, 3, 9]`) -/

/-- Adjacent `x ~ y` outside `I` with distinct `I`-neighbors `ix ~ x`, `iy ~ y` (`¬ Adj ix y`)
cannot both have `|W| ≥ 3` when `Bzero = 0`. -/
theorem hnot33_pair {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hB0 : Bzero 14 D = 0) {pos : Fin 14 → ℕ × Bool} {P Q : ℕ × Bool}
    (hctx : pa_ctx D pos P Q) (x y ix iy : Fin 14)
    (hix : ix ∈ ineligSet 14 D) (hiy : iy ∈ ineligSet 14 D)
    (hx : x ∉ ineligSet 14 D) (hy : y ∉ ineligSet 14 D)
    (hg : ix ≠ iy ∧ hc_adjB ix x = true ∧ hc_adjB iy y = true ∧ hc_adjB x y = true ∧
      hc_adjB ix y = false)
    (hsx : 3 ≤ (sem_W 14 D x).card) (hsy : 3 ≤ (sem_W 14 D y).card) : False := by
  obtain ⟨hpos, hc3, hPQ, hsat⟩ := hctx
  obtain ⟨hxyi, g1, g2, g3, g4⟩ := hg
  rw [hc_adjB_iff] at g1 g2 g3
  obtain ⟨hPx, hQx⟩ := hsat x hsx
  obtain ⟨hPy, hQy⟩ := hsat y hsy
  obtain ⟨e, hex, hey, hfy, hfx⟩ := pa_ed h hD hpos g3
  have heP : e ≠ P := fun hh => w_bar h.1 (hh ▸ hPy) hey
  have heQ : e ≠ Q := fun hh => w_bar h.1 (hh ▸ hQy) hey
  have hbeP : sem_bar e ≠ P := fun hh => w_bar h.1 hPx (by rw [← hh, sem_bar_bar]; exact hex)
  have hbeQ : sem_bar e ≠ Q := fun hh => w_bar h.1 hQx (by rw [← hh, sem_bar_bar]; exact hex)
  have hpx := as_mem hpos hix g1
  have hpy := as_mem hpos hiy g2
  have hpxe : pos ix ≠ e := fun hh => hy (hfy ix hix hh.symm ▸ hix)
  have hpybe : pos iy ≠ sem_bar e := fun hh => hx (hfx iy hiy hh.symm ▸ hiy)
  have hpxy : pos ix ∈ sem_W 14 D y := by
    rcases pa_three hPx hQx hex hPQ heP.symm heQ.symm (hc3 x) (pos ix) hpx with heq | heq | heq
    · exact heq ▸ hPy
    · exact heq ▸ hQy
    · exact absurd heq hpxe
  have hpyx : pos iy ∈ sem_W 14 D x := by
    rcases pa_three hPy hQy hey hPQ hbeP.symm hbeQ.symm (hc3 y) (pos iy) hpy with heq | heq | heq
    · exact heq ▸ hPx
    · exact heq ▸ hQx
    · exact absurd heq hpybe
  have hpxpy : pos ix ≠ pos iy := fun hh => hxyi (hpos.2 ix hix iy hiy hh)
  have hpye : pos iy ≠ e := fun hh => hy (hfy iy hiy hh.symm ▸ hiy)
  have hWx := pa_three hpx hpyx hex hpxpy hpxe hpye (hc3 x)
  have hfull := full_g14 h hD hB0 hpos hix g1 (fun p hp hne1 hsub => by
    rcases hWx p hp with rfl | rfl | rfl
    · exact hne1 rfl
    · have hm : iy ∈ supp 14 D (src D (sem_bar (pos iy))) := by
        rw [show src D (sem_bar (pos iy)) = src D ((pos iy).1, !(pos iy).2) from rfl,
          (hpos.1 iy hiy).2.2.2]; exact Finset.mem_singleton_self iy
      exact hxyi.symm (Finset.mem_singleton.1 (hsub hm))
    · exact hy (Finset.mem_singleton.1 (hsub (sem_mem_W.1 hey).2.1) ▸ hix))
  exact sem_adjB_false.1 g4 ((hfull y).1 (sem_mem_W.1 hpxy).2.1)

/-- Two `|W| ≥ 3` vertices `a1, a2` (with distinct `I`-neighbors `ia1, ia2`) whose other two
neighbors are `(b0, b1)` and `(b1, b2)` where `b0, b1, b2` are distinct deg-3 vertices on the
same side with `|W| ≤ 2` and `I`-neighbors `ib0, ib1, ib2` contradict `P ≠ Q`. -/
theorem elim_alt_pair {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    {pos : Fin 14 → ℕ × Bool} {P Q : ℕ × Bool} (hctx : pa_ctx D pos P Q)
    (a1 a2 b0 b1 b2 ia1 ia2 ib0 ib1 ib2 : Fin 14)
    (hia1 : ia1 ∈ ineligSet 14 D) (hia2 : ia2 ∈ ineligSet 14 D)
    (hib0 : ib0 ∈ ineligSet 14 D) (hib1 : ib1 ∈ ineligSet 14 D) (hib2 : ib2 ∈ ineligSet 14 D)
    (ha1 : a1 ∉ ineligSet 14 D) (ha2 : a2 ∉ ineligSet 14 D)
    (hb0 : b0 ∉ ineligSet 14 D) (hb1 : b1 ∉ ineligSet 14 D) (hb2 : b2 ∉ ineligSet 14 D)
    (hg : ia1 ≠ ia2 ∧ b0 ≠ b1 ∧ b0 ≠ b2 ∧ b1 ≠ b2 ∧
      hc_adjB ia1 a1 = true ∧ hc_adjB ia2 a2 = true ∧
      hc_adjB ib0 b0 = true ∧ hc_adjB ib1 b1 = true ∧ hc_adjB ib2 b2 = true ∧
      hc_adjB a1 b0 = true ∧ hc_adjB a1 b1 = true ∧
      hc_adjB a2 b1 = true ∧ hc_adjB a2 b2 = true ∧
      (g14_nbB b0).card = 3 ∧ (g14_nbB b1).card = 3 ∧ (g14_nbB b2).card = 3 ∧
      decide (b0.val < 7) = decide (b1.val < 7) ∧ decide (b1.val < 7) = decide (b2.val < 7))
    (hsa1 : 3 ≤ (sem_W 14 D a1).card) (hsa2 : 3 ≤ (sem_W 14 D a2).card)
    (hcb0 : (sem_W 14 D b0).card ≤ 2) (hcb1 : (sem_W 14 D b1).card ≤ 2)
    (hcb2 : (sem_W 14 D b2).card ≤ 2) : False := by
  obtain ⟨hpos, hc3, hPQ, hsat⟩ := hctx
  obtain ⟨hi12, h01, h02, h12, ga1, ga2, gb0, gb1, gb2, e10, e11, e21, e22,
    hd0, hd1, hd2, hs01, hs12⟩ := hg
  rw [hc_adjB_iff] at ga1 ga2 gb0 gb1 gb2 e10 e11 e21 e22
  obtain ⟨D0, -, hW0, hp0⟩ := ps_side h hD hpos hib0 gb0 hd0 hcb0
  obtain ⟨D1, -, hW1, hp1⟩ := ps_side h hD hpos hib1 gb1 hd1 hcb1
  obtain ⟨D2, -, hW2, hp2⟩ := ps_side h hD hpos hib2 gb2 hd2 hcb2
  have hD0_in : D0 ∈ sem_W 14 D b0 := by rw [hW0]; simp
  have hD1_in : D1 ∈ sem_W 14 D b1 := by rw [hW1]; simp
  have hD2_in : D2 ∈ sem_W 14 D b2 := by rw [hW2]; simp
  obtain ⟨f10, hf10, hbf10, h10y, h10x⟩ := pa_ed h hD hpos e10
  obtain ⟨f11, hf11, hbf11, h11y, h11x⟩ := pa_ed h hD hpos e11
  obtain ⟨f21, hf21, hbf21, h21y, h21x⟩ := pa_ed h hD hpos e21
  obtain ⟨f22, hf22, hbf22, h22y, h22x⟩ := pa_ed h hD hpos e22
  have hb10 : sem_bar f10 = D0 := by
    rw [hW0, Finset.mem_insert, Finset.mem_singleton] at hbf10
    exact hbf10.resolve_left (fun hh => ha1 (h10x ib0 hib0 hh ▸ hib0))
  have hb11 : sem_bar f11 = D1 := by
    rw [hW1, Finset.mem_insert, Finset.mem_singleton] at hbf11
    exact hbf11.resolve_left (fun hh => ha1 (h11x ib1 hib1 hh ▸ hib1))
  have hb21 : sem_bar f21 = D1 := by
    rw [hW1, Finset.mem_insert, Finset.mem_singleton] at hbf21
    exact hbf21.resolve_left (fun hh => ha2 (h21x ib1 hib1 hh ▸ hib1))
  have hb22 : sem_bar f22 = D2 := by
    rw [hW2, Finset.mem_insert, Finset.mem_singleton] at hbf22
    exact hbf22.resolve_left (fun hh => ha2 (h22x ib2 hib2 hh ▸ hib2))
  have hf11_21 : f11 = f21 := by rw [← sem_bar_bar f11, ← sem_bar_bar f21, hb11, hb21]
  have hD01 : D0 ≠ D1 := fun hh => hp0 b1 h01.symm hs01.symm (hh ▸ hD1_in)
  have hD02 : D0 ≠ D2 := fun hh => hp0 b2 h02.symm (hs01.trans hs12).symm (hh ▸ hD2_in)
  have hD12 : D1 ≠ D2 := fun hh => hp1 b2 h12.symm hs12.symm (hh ▸ hD2_in)
  have h10_11 : f10 ≠ f11 := fun hh => hD01 (by rw [← hb10, ← hb11, hh])
  have h21_22 : f21 ≠ f22 := fun hh => hD12 (by rw [← hb21, ← hb22, hh])
  have hpa1 := as_mem hpos hia1 ga1
  have hpa2 := as_mem hpos hia2 ga2
  have hWa1 := pa_three hpa1 hf10 hf11 (fun hh => hb0 (h10y ia1 hia1 hh.symm ▸ hia1))
    (fun hh => hb1 (h11y ia1 hia1 hh.symm ▸ hia1)) h10_11 (hc3 a1)
  have hWa2 := pa_three hpa2 hf21 hf22 (fun hh => hb1 (h21y ia2 hia2 hh.symm ▸ hia2))
    (fun hh => hb2 (h22y ia2 hia2 hh.symm ▸ hia2)) h21_22 (hc3 a2)
  have honly : ∀ e, e ∈ sem_W 14 D a1 → e ∈ sem_W 14 D a2 → e = f11 := by
    intro e he1 he2
    rcases hWa1 e he1 with rfl | rfl | rfl
    · rcases hWa2 _ he2 with hh | hh | hh
      · exact absurd (hpos.2 ia1 hia1 ia2 hia2 hh) hi12
      · exact absurd (h21y ia1 hia1 hh.symm ▸ hia1) hb1
      · exact absurd (h22y ia1 hia1 hh.symm ▸ hia1) hb2
    · rcases hWa2 _ he2 with hh | hh | hh
      · exact absurd (h10y ia2 hia2 hh ▸ hia2) hb0
      · exact absurd (by rw [← hb10, ← hb21, hh]) hD01
      · exact absurd (by rw [← hb10, ← hb22, hh]) hD02
    · rfl
  exact hPQ ((honly P (hsat a1 hsa1).1 (hsat a2 hsa2).1).trans
    (honly Q (hsat a1 hsa1).2 (hsat a2 hsa2).2).symm)

theorem elim_13810 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h11 : totalSurplus 14 D ≤ 11) (hI : ineligSet 14 D = hc_rep ⟨96, by decide⟩) : False := by
  have hIeq : ineligSet 14 D = {1, 3, 8, 10} := by rw [hI]; decide +kernel
  obtain ⟨hB0, pos, P, Q, hctx⟩ := res1_setup_c4 h hD h11 ⟨96, by decide⟩ hI (by rw [hIeq]; decide)
  by_cases h11' : 3 ≤ (sem_W 14 D 11).card
  · have h4 : (sem_W 14 D 4).card ≤ 2 := by
      by_contra hc; exact hnot33_pair h hD hB0 hctx 11 4 3 10
        (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
        (by decide) h11' (by omega)
    have h6 : (sem_W 14 D 6).card ≤ 2 := by
      by_contra hc; exact hnot33_pair h hD hB0 hctx 11 6 3 8
        (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
        (by decide) h11' (by omega)
    have h9 : 3 ≤ (sem_W 14 D 9).card := by
      by_contra hc; exact pa_m1 h hD hctx.1 6 9 11 8 1
        (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
        (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide) h6 (by omega)
    have h5 : (sem_W 14 D 5).card ≤ 2 := by
      by_contra hc; exact hnot33_pair h hD hB0 hctx 9 5 1 10
        (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
        (by decide) h9 (by omega)
    exact elim_alt_pair h hD hctx 11 9 4 6 5 3 1 10 8 10
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (by decide) h11' h9 h4 h6 h5
  · have h11c : (sem_W 14 D 11).card ≤ 2 := by omega
    have h4 : 3 ≤ (sem_W 14 D 4).card := by
      by_contra hc; exact pa_m1 h hD hctx.1 11 4 6 3 10
        (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
        (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide) h11c (by omega)
    have h6 : 3 ≤ (sem_W 14 D 6).card := by
      by_contra hc; exact pa_m1 h hD hctx.1 11 6 4 3 8
        (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
        (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide) h11c (by omega)
    have h13 : (sem_W 14 D 13).card ≤ 2 := by
      by_contra hc; exact hnot33_pair h hD hB0 hctx 4 13 10 1
        (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
        (by decide) h4 (by omega)
    have h9 : (sem_W 14 D 9).card ≤ 2 := by
      by_contra hc; exact hnot33_pair h hD hB0 hctx 6 9 8 1
        (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
        (by decide) h6 (by omega)
    exact elim_alt_pair h hD hctx 4 6 13 11 9 10 8 1 3 1
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (by decide) h4 h6 h13 h11c h9

/-! ### Special `|I| ≥ 5` orbits (`126`, `129`, `131`, `132`, `140`, `141`) -/

theorem pa_card5 {α : Type} [DecidableEq α] {s : Finset α} {a b c d e : α}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hd : d ∈ s) (he : e ∈ s)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) : 5 ≤ s.card := by
  have hsub : ({a, b, c, d, e} : Finset α) ⊆ s := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
  have := Finset.card_le_card hsub
  rwa [Finset.card_insert_of_notMem (by simp [hab, hac, had, hae]),
    Finset.card_insert_of_notMem (by simp [hbc, hbd, hbe]),
    Finset.card_insert_of_notMem (by simp [hcd, hce]),
    Finset.card_pair hde] at this

theorem pa_four {α : Type} [DecidableEq α] {s : Finset α} {a b c d : α}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hd : d ∈ s)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hs : s.card ≤ 4) : ∀ e ∈ s, e = a ∨ e = b ∨ e = c ∨ e = d := by
  intro e he
  by_contra hne
  rw [not_or, not_or, not_or] at hne
  have := pa_card5 he ha hb hc hd hne.1 hne.2.1 hne.2.2.1 hne.2.2.2 hab hac had hbc hbd hcd
  omega

theorem mem_W_of_pos {D : Dag} {pos : Fin 14 → ℕ × Bool} (hpos : k4_Pos 14 G14 D pos)
    {j t : Fin 14} (hj : j ∈ ineligSet 14 D) (ht : t ∈ supp 14 D (src D (pos j))) :
    pos j ∈ sem_W 14 D t := by
  obtain ⟨h1, h2, -, -⟩ := hpos.1 j hj
  exact sem_mem_W.2 ⟨h1, ht, by rw [h2]; exact Finset.notMem_empty t⟩

theorem pe_co_g14 {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (b : Fin 14 → ℕ)
    (hb : PureBranch 14 D b) {pos : Fin 14 → ℕ × Bool} (hpos : k4_Pos 14 G14 D pos)
    {v t j q : Fin 14} (hj : j ∈ ineligSet 14 D) (hv : v ∈ eligSet 14 D)
    (hres : ∀ u ∈ residualUnits 14 D b, v ∈ supp 14 D u.1 → t ∈ supp 14 D u.1)
    {w : ℕ} (hw : v ∈ supp 14 D w ∧ t ∈ supp 14 D w)
    (hg : (g14_nbB v).card = 3 ∧ hc_adjB j v = true ∧ hc_adjB j q = true ∧
      v ≠ t ∧ v ≠ q ∧ hc_adjB t q = false) :
    t ∈ supp 14 D (src D (pos j)) := by
  obtain ⟨hdv, hjv, hjq, hvt, hvq, htq⟩ := hg
  rw [hc_adjB_iff] at hjv hjq
  obtain ⟨e0, he0⟩ := ri_gen sem_g14_gr h (sem_g14_comp hD) b hb hvt hv hres hw
  by_contra hn
  have h0 : pos j = e0 := by
    by_contra hne
    exact hn (he0 _ (as_mem hpos hj hjv) hne)
  obtain ⟨e, he, h1, h2⟩ := g14_deg3_cover_free h hD hdv hvt hvq (sem_adjB_false.1 htq)
  exact h1 (he0 e he (fun hee => h2 (by rw [hee, ← h0]; exact (hpos.1 j hj).2.2.1 q hjq)))

theorem ru_sub_excl {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (hB0 : Bzero 14 D = 0)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b) {pos : Fin 14 → ℕ × Bool} (hpos : k4_Pos 14 G14 D pos)
    {v i1 i2 v3 t : Fin 14} (hi1 : i1 ∈ ineligSet 14 D) (hi2 : i2 ∈ ineligSet 14 D)
    (hv : v ∈ eligSet 14 D)
    (hg : (g14_nbB v).card = 3 ∧ i1 ≠ i2 ∧ hc_adjB i1 v = true ∧ hc_adjB i2 v = true ∧
      hc_adjB v v3 = true ∧ v3 ≠ i1 ∧ v3 ≠ i2)
    (hru1 : (ru D b v).card = 1) (hsub : ru D b v ⊆ ru D b t) (hvt : v ≠ t)
    (hq : ∃ q : Fin 14,
      (hc_adjB i1 q = true ∧ v ≠ q ∧ hc_adjB t q = false ∧ hc_adjB i1 t = false) ∨
      (hc_adjB i2 q = true ∧ v ≠ q ∧ hc_adjB t q = false ∧ hc_adjB i2 t = false)) : False := by
  obtain ⟨hdv, hne, h1, h2, h3, hv1, hv2⟩ := hg
  have hcv : (sem_W 14 D v).card ≤ 3 := by
    have := cc_le h hD b hb v; omega
  obtain ⟨hf1, hf2⟩ := full_of_two_in_deg3 h hD hB0 hpos hi1 hi2 ⟨hne, h1, h2, h3, hv1, hv2⟩ hcv
  obtain ⟨u, hu⟩ := Finset.card_pos.1 (by omega : 0 < (ru D b v).card)
  have hut := hsub hu
  have hres : ∀ u' ∈ residualUnits 14 D b, v ∈ supp 14 D u'.1 → t ∈ supp 14 D u'.1 :=
    fun u' hu' hv' => (Finset.mem_filter.1 (hsub (Finset.mem_filter.2 ⟨hu', hv'⟩))).2
  have hw : v ∈ supp 14 D u.1 ∧ t ∈ supp 14 D u.1 :=
    ⟨(Finset.mem_filter.1 hu).2, (Finset.mem_filter.1 hut).2⟩
  obtain ⟨q, ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩⟩ := hq
  · exact sem_adjB_false.1 a4 (hf1 t (pe_co_g14 h hD b hb hpos hi1 hv hres hw ⟨hdv, h1, a1, hvt, a2, a3⟩))
  · exact sem_adjB_false.1 a4 (hf2 t (pe_co_g14 h hD b hb hpos hi2 hv hres hw ⟨hdv, h2, a1, hvt, a2, a3⟩))

theorem three_subsets_of_two {α : Type} [DecidableEq α] {R A B C : Finset α}
    (hR : R.card = 2) (hA : A ⊆ R) (hB : B ⊆ R) (hC : C ⊆ R)
    (hAn : 1 ≤ A.card) (hBn : 1 ≤ B.card) (hCn : 1 ≤ C.card) :
    (A.card = 1 ∧ (A ⊆ B ∨ A ⊆ C)) ∨ (B.card = 1 ∧ (B ⊆ A ∨ B ⊆ C)) ∨
    (C.card = 1 ∧ (C ⊆ A ∨ C ⊆ B)) ∨ (A = R ∧ B = R) := by
  have hAle := Finset.card_le_card hA
  have hBle := Finset.card_le_card hB
  by_cases hA2 : A.card = 2
  · by_cases hB2 : B.card = 2
    · exact Or.inr (Or.inr (Or.inr ⟨Finset.eq_of_subset_of_card_le hA (by omega),
        Finset.eq_of_subset_of_card_le hB (by omega)⟩))
    · exact Or.inr (Or.inl ⟨by omega, Or.inl (hB.trans (Finset.eq_of_subset_of_card_le hA (by omega)).symm.subset)⟩)
  · have hA1 : A.card = 1 := by omega
    obtain ⟨u, hu⟩ := Finset.card_eq_one.1 hA1
    by_cases huB : u ∈ B
    · exact Or.inl ⟨hA1, Or.inl (by rw [hu, Finset.singleton_subset_iff]; exact huB)⟩
    · by_cases huC : u ∈ C
      · exact Or.inl ⟨hA1, Or.inr (by rw [hu, Finset.singleton_subset_iff]; exact huC)⟩
      · have huR : u ∈ R := hA (hu ▸ Finset.mem_singleton_self u)
        have hBsub : B ⊆ R.erase u := fun x hx =>
          Finset.mem_erase.2 ⟨fun hxu => huB (hxu ▸ hx), hB hx⟩
        have hCsub : C ⊆ R.erase u := fun x hx =>
          Finset.mem_erase.2 ⟨fun hxu => huC (hxu ▸ hx), hC hx⟩
        have hE1 : (R.erase u).card = 1 := by rw [Finset.card_erase_of_mem huR, hR]
        have hBeq : B = R.erase u := Finset.eq_of_subset_of_card_le hBsub (by omega)
        have hCeq : C = R.erase u := Finset.eq_of_subset_of_card_le hCsub (by omega)
        exact Or.inr (Or.inl ⟨by rw [hBeq, hE1], Or.inr (by rw [hBeq, hCeq])⟩)

theorem elim_res2_3w3 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h11 : totalSurplus 14 D ≤ 11) (idx : Fin 143) (hI : ineligSet 14 D = hc_rep idx)
    (hge5 : 106 ≤ idx.val) (hc5 : (ineligSet 14 D).card = 5)
    (a b c a1 a2 va b1 b2 vb c1 c2 vc qa1 qa2 : Fin 14)
    (ha : a ∈ eligSet 14 D) (hb' : b ∈ eligSet 14 D) (hc' : c ∈ eligSet 14 D)
    (ha1 : a1 ∈ ineligSet 14 D) (ha2 : a2 ∈ ineligSet 14 D)
    (hb1 : b1 ∈ ineligSet 14 D) (hb2 : b2 ∈ ineligSet 14 D)
    (hc1 : c1 ∈ ineligSet 14 D) (hc2 : c2 ∈ ineligSet 14 D)
    (hvb : vb ∉ ineligSet 14 D)
    (hg : a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      a1 ≠ a2 ∧ a1 ≠ b1 ∧ a1 ≠ b2 ∧ a2 ≠ b1 ∧ a2 ≠ b2 ∧ b1 ≠ b2 ∧ c1 ≠ c2 ∧
      (g14_nbB a).card = 3 ∧ hc_adjB a1 a = true ∧ hc_adjB a2 a = true ∧ hc_adjB a va = true ∧ va ≠ a1 ∧ va ≠ a2 ∧
      (g14_nbB b).card = 3 ∧ hc_adjB b1 b = true ∧ hc_adjB b2 b = true ∧ hc_adjB b vb = true ∧ vb ≠ b1 ∧ vb ≠ b2 ∧
      (g14_nbB c).card = 3 ∧ hc_adjB c1 c = true ∧ hc_adjB c2 c = true ∧ hc_adjB c vc = true ∧ vc ≠ c1 ∧ vc ≠ c2 ∧
      hc_adjB a1 qa1 = true ∧ a ≠ qa1 ∧ hc_adjB b qa1 = false ∧
      hc_adjB a2 qa2 = true ∧ a ≠ qa2 ∧ hc_adjB b qa2 = false)
    (hqa : ∀ t, (t = b ∨ t = c) → ∃ q : Fin 14,
      (hc_adjB a1 q = true ∧ a ≠ q ∧ hc_adjB t q = false ∧ hc_adjB a1 t = false) ∨
      (hc_adjB a2 q = true ∧ a ≠ q ∧ hc_adjB t q = false ∧ hc_adjB a2 t = false))
    (hqb : ∀ t, (t = a ∨ t = c) → ∃ q : Fin 14,
      (hc_adjB b1 q = true ∧ b ≠ q ∧ hc_adjB t q = false ∧ hc_adjB b1 t = false) ∨
      (hc_adjB b2 q = true ∧ b ≠ q ∧ hc_adjB t q = false ∧ hc_adjB b2 t = false))
    (hqc : ∀ t, (t = a ∨ t = b) → ∃ q : Fin 14,
      (hc_adjB c1 q = true ∧ c ≠ q ∧ hc_adjB t q = false ∧ hc_adjB c1 t = false) ∨
      (hc_adjB c2 q = true ∧ c ≠ q ∧ hc_adjB t q = false ∧ hc_adjB c2 t = false)) : False := by
  classical
  have hBgt := bplus_gt_p1_ge5 h hD h11 idx hI hge5
  have hel := inelig_card_add 14 D
  have hts := totalSurplus_split 14 D
  have hB0 : Bzero 14 D = 0 := by omega
  obtain ⟨br, hbr⟩ := exists_pureBranch h hD
  obtain ⟨pos, hpos⟩ := k4_assigned sem_g14_gr h (sem_g14_comp hD)
  have hR2 : (residualUnits 14 D br).card = 2 := by
    have := card_residual h.1 br hbr; omega
  obtain ⟨hab, hac, hbc, ha12, ha1b1, ha1b2, ha2b1, ha2b2, hb12, hc12,
    hda, ga1, ga2, gva, hva1, hva2,
    hdb, gb1, gb2, gvb, hvb1, hvb2,
    hdc, gc1, gc2, gvc, hvc1, hvc2,
    gqa1, haqa1, gbqa1, gqa2, haqa2, gbqa2⟩ := hg
  have hAn : 1 ≤ (ru D br a).card := by
    have h3 := two_in_deg3 h hD hpos ha1 ha2 ⟨ha12, ga1, ga2, gva, hva1, hva2⟩
    have hc := cc_le h hD br hbr a; omega
  have hBn : 1 ≤ (ru D br b).card := by
    have h3 := two_in_deg3 h hD hpos hb1 hb2 ⟨hb12, gb1, gb2, gvb, hvb1, hvb2⟩
    have hc := cc_le h hD br hbr b; omega
  have hCn : 1 ≤ (ru D br c).card := by
    have h3 := two_in_deg3 h hD hpos hc1 hc2 ⟨hc12, gc1, gc2, gvc, hvc1, hvc2⟩
    have hc := cc_le h hD br hbr c; omega
  rcases three_subsets_of_two hR2 (A := ru D br a) (B := ru D br b) (C := ru D br c)
      (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      (Finset.filter_subset _ _) hAn hBn hCn with
    ⟨h1, hs | hs⟩ | ⟨h1, hs | hs⟩ | ⟨h1, hs | hs⟩ | ⟨hAR, hBR⟩
  · exact ru_sub_excl h hD hB0 br hbr hpos ha1 ha2 ha ⟨hda, ha12, ga1, ga2, gva, hva1, hva2⟩ h1 hs hab (hqa b (Or.inl rfl))
  · exact ru_sub_excl h hD hB0 br hbr hpos ha1 ha2 ha ⟨hda, ha12, ga1, ga2, gva, hva1, hva2⟩ h1 hs hac (hqa c (Or.inr rfl))
  · exact ru_sub_excl h hD hB0 br hbr hpos hb1 hb2 hb' ⟨hdb, hb12, gb1, gb2, gvb, hvb1, hvb2⟩ h1 hs hab.symm (hqb a (Or.inl rfl))
  · exact ru_sub_excl h hD hB0 br hbr hpos hb1 hb2 hb' ⟨hdb, hb12, gb1, gb2, gvb, hvb1, hvb2⟩ h1 hs hbc (hqb c (Or.inr rfl))
  · exact ru_sub_excl h hD hB0 br hbr hpos hc1 hc2 hc' ⟨hdc, hc12, gc1, gc2, gvc, hvc1, hvc2⟩ h1 hs hac.symm (hqc a (Or.inl rfl))
  · exact ru_sub_excl h hD hB0 br hbr hpos hc1 hc2 hc' ⟨hdc, hc12, gc1, gc2, gvc, hvc1, hvc2⟩ h1 hs hbc.symm (hqc b (Or.inr rfl))
  · obtain ⟨u, hu⟩ := Finset.card_pos.1 (by omega : 0 < (ru D br a).card)
    have hsub : ru D br a ⊆ ru D br b := by rw [hAR, hBR]
    have hres : ∀ u' ∈ residualUnits 14 D br, a ∈ supp 14 D u'.1 → b ∈ supp 14 D u'.1 :=
      fun u' hu' ha' => (Finset.mem_filter.1 (hsub (Finset.mem_filter.2 ⟨hu', ha'⟩))).2
    have hw : a ∈ supp 14 D u.1 ∧ b ∈ supp 14 D u.1 :=
      ⟨(Finset.mem_filter.1 hu).2, (Finset.mem_filter.1 (hsub hu)).2⟩
    have hm1 := mem_W_of_pos hpos ha1 (pe_co_g14 h hD br hbr hpos ha1 ha hres hw ⟨hda, ga1, gqa1, hab, haqa1, gbqa1⟩)
    have hm2 := mem_W_of_pos hpos ha2 (pe_co_g14 h hD br hbr hpos ha2 ha hres hw ⟨hda, ga2, gqa2, hab, haqa2, gbqa2⟩)
    have hb1m := as_mem hpos hb1 ((hc_adjB_iff _ _).1 gb1)
    have hb2m := as_mem hpos hb2 ((hc_adjB_iff _ _).1 gb2)
    obtain ⟨ev, hev, -, hfv, -⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gvb)
    have h5 := pa_card5 hm1 hm2 hb1m hb2m hev
      (fun e => ha12 (hpos.2 _ ha1 _ ha2 e))
      (fun e => ha1b1 (hpos.2 _ ha1 _ hb1 e))
      (fun e => ha1b2 (hpos.2 _ ha1 _ hb2 e))
      (fun e => hvb (hfv _ ha1 e.symm ▸ ha1))
      (fun e => ha2b1 (hpos.2 _ ha2 _ hb1 e))
      (fun e => ha2b2 (hpos.2 _ ha2 _ hb2 e))
      (fun e => hvb (hfv _ ha2 e.symm ▸ ha2))
      (fun e => hb12 (hpos.2 _ hb1 _ hb2 e))
      (fun e => hvb (hfv _ hb1 e.symm ▸ hb1))
      (fun e => hvb (hfv _ hb2 e.symm ▸ hb2))
    have hc4 : (sem_W 14 D b).card ≤ 4 := by
      have := cc_le h hD br hbr b; rw [hBR, hR2] at this; omega
    omega

theorem pa_card6 {α : Type} [DecidableEq α] {s : Finset α} {a b c d e f : α}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hd : d ∈ s) (he : e ∈ s) (hf : f ∈ s)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (haf : a ≠ f)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hbf : b ≠ f)
    (hcd : c ≠ d) (hce : c ≠ e) (hcf : c ≠ f)
    (hde : d ≠ e) (hdf : d ≠ f) (hef : e ≠ f) : 6 ≤ s.card := by
  have hsub : ({a, b, c, d, e, f} : Finset α) ⊆ s := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  have := Finset.card_le_card hsub
  rwa [Finset.card_insert_of_notMem (by simp [hab, hac, had, hae, haf]),
    Finset.card_insert_of_notMem (by simp [hbc, hbd, hbe, hbf]),
    Finset.card_insert_of_notMem (by simp [hcd, hce, hcf]),
    Finset.card_insert_of_notMem (by simp [hde, hdf]),
    Finset.card_pair hef] at this

theorem four_2subsets_of_three {α : Type} [DecidableEq α] {R A B C D : Finset α}
    (hR : R.card = 3) (hA : A ⊆ R) (hB : B ⊆ R) (hC : C ⊆ R) (hD : D ⊆ R)
    (hcA : A.card = 2) (hcB : B.card = 2) (hcC : C.card = 2) (hcD : D.card = 2) :
    A = B ∨ A = C ∨ A = D ∨ B = C ∨ B = D ∨ C = D := by
  have hmiss : ∀ S : Finset α, S ⊆ R → S.card = 2 → ∃ x ∈ R, S = R.erase x := by
    intro S hS hcS
    have hpos : 0 < (R \ S).card := by
      have := Finset.card_sdiff_add_card_eq_card hS; omega
    obtain ⟨x, hx⟩ := Finset.card_pos.1 hpos
    have hxR : x ∈ R := (Finset.mem_sdiff.1 hx).1
    have hxS : x ∉ S := (Finset.mem_sdiff.1 hx).2
    refine ⟨x, hxR, Finset.eq_of_subset_of_card_le (fun y hy => Finset.mem_erase.2 ⟨fun h => hxS (h ▸ hy), hS hy⟩) ?_⟩
    rw [Finset.card_erase_of_mem hxR, hR, hcS]
  obtain ⟨xa, hxa, rfl⟩ := hmiss A hA hcA
  obtain ⟨xb, hxb, rfl⟩ := hmiss B hB hcB
  obtain ⟨xc, hxc, rfl⟩ := hmiss C hC hcC
  obtain ⟨xd, hxd, rfl⟩ := hmiss D hD hcD
  by_contra hne
  push Not at hne
  have h4 := pa_card4 hxa hxb hxc hxd
    (fun h => hne.1 (h ▸ rfl)) (fun h => hne.2.1 (h ▸ rfl)) (fun h => hne.2.2.1 (h ▸ rfl))
    (fun h => hne.2.2.2.1 (h ▸ rfl)) (fun h => hne.2.2.2.2.1 (h ▸ rfl)) (fun h => hne.2.2.2.2.2 (h ▸ rfl))
  omega

/-- Generic `Bzero`-free `pe_co` contradiction: `ru a ⊆ ru b` puts two extra `pos` into `W_b`,
exceeding `2 + |ru b|` when `|ru b| ≤ 2`. -/
theorem pe_co_blow5 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (br : Fin 14 → ℕ) (hbr : PureBranch 14 D br) {pos : Fin 14 → ℕ × Bool}
    (hpos : k4_Pos 14 G14 D pos)
    (a b a1 a2 qa1 qa2 b1 b2 vb : Fin 14)
    (ha : a ∈ eligSet 14 D) (ha1 : a1 ∈ ineligSet 14 D) (ha2 : a2 ∈ ineligSet 14 D)
    (hb1 : b1 ∈ ineligSet 14 D) (hb2 : b2 ∈ ineligSet 14 D)
    (hvb : vb ∉ ineligSet 14 D)
    (hg : a ≠ b ∧ a1 ≠ a2 ∧ a1 ≠ b1 ∧ a1 ≠ b2 ∧ a2 ≠ b1 ∧ a2 ≠ b2 ∧ b1 ≠ b2 ∧
      (g14_nbB a).card = 3 ∧ hc_adjB a1 a = true ∧ hc_adjB a2 a = true ∧
      hc_adjB a1 qa1 = true ∧ a ≠ qa1 ∧ hc_adjB b qa1 = false ∧
      hc_adjB a2 qa2 = true ∧ a ≠ qa2 ∧ hc_adjB b qa2 = false ∧
      hc_adjB b1 b = true ∧ hc_adjB b2 b = true ∧ hc_adjB b vb = true)
    (hAn : 1 ≤ (ru D br a).card) (hsub : ru D br a ⊆ ru D br b) (hBle : (ru D br b).card ≤ 2) :
    False := by
  obtain ⟨hab, ha12, ha1b1, ha1b2, ha2b1, ha2b2, hb12, hda, ga1, ga2,
    gqa1, haqa1, gbqa1, gqa2, haqa2, gbqa2, gb1, gb2, gvb⟩ := hg
  obtain ⟨u, hu⟩ := Finset.card_pos.1 (by omega : 0 < (ru D br a).card)
  have hres : ∀ u' ∈ residualUnits 14 D br, a ∈ supp 14 D u'.1 → b ∈ supp 14 D u'.1 :=
    fun u' hu' ha' => (Finset.mem_filter.1 (hsub (Finset.mem_filter.2 ⟨hu', ha'⟩))).2
  have hw : a ∈ supp 14 D u.1 ∧ b ∈ supp 14 D u.1 :=
    ⟨(Finset.mem_filter.1 hu).2, (Finset.mem_filter.1 (hsub hu)).2⟩
  have hm1 := mem_W_of_pos hpos ha1 (pe_co_g14 h hD br hbr hpos ha1 ha hres hw ⟨hda, ga1, gqa1, hab, haqa1, gbqa1⟩)
  have hm2 := mem_W_of_pos hpos ha2 (pe_co_g14 h hD br hbr hpos ha2 ha hres hw ⟨hda, ga2, gqa2, hab, haqa2, gbqa2⟩)
  have hb1m := as_mem hpos hb1 ((hc_adjB_iff _ _).1 gb1)
  have hb2m := as_mem hpos hb2 ((hc_adjB_iff _ _).1 gb2)
  obtain ⟨ev, hev, -, hfv, -⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gvb)
  have h5 := pa_card5 hm1 hm2 hb1m hb2m hev
    (fun e => ha12 (hpos.2 _ ha1 _ ha2 e))
    (fun e => ha1b1 (hpos.2 _ ha1 _ hb1 e))
    (fun e => ha1b2 (hpos.2 _ ha1 _ hb2 e))
    (fun e => hvb (hfv _ ha1 e.symm ▸ ha1))
    (fun e => ha2b1 (hpos.2 _ ha2 _ hb1 e))
    (fun e => ha2b2 (hpos.2 _ ha2 _ hb2 e))
    (fun e => hvb (hfv _ ha2 e.symm ▸ ha2))
    (fun e => hb12 (hpos.2 _ hb1 _ hb2 e))
    (fun e => hvb (hfv _ hb1 e.symm ▸ hb1))
    (fun e => hvb (hfv _ hb2 e.symm ▸ hb2))
  have hc4 := cc_le h hD br hbr b
  omega

/-- Variant of `pe_co_blow5` when `b` has ALL 3 neighbors `b1, b2, b3 ∈ I`. -/
theorem pe_co_blow5_all3 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (br : Fin 14 → ℕ) (hbr : PureBranch 14 D br) {pos : Fin 14 → ℕ × Bool}
    (hpos : k4_Pos 14 G14 D pos)
    (a b a1 a2 qa1 qa2 b1 b2 b3 : Fin 14)
    (ha : a ∈ eligSet 14 D) (ha1 : a1 ∈ ineligSet 14 D) (ha2 : a2 ∈ ineligSet 14 D)
    (hb1 : b1 ∈ ineligSet 14 D) (hb2 : b2 ∈ ineligSet 14 D) (hb3 : b3 ∈ ineligSet 14 D)
    (hg : a ≠ b ∧ a1 ≠ a2 ∧ a1 ≠ b1 ∧ a1 ≠ b2 ∧ a1 ≠ b3 ∧ a2 ≠ b1 ∧ a2 ≠ b2 ∧ a2 ≠ b3 ∧
      b1 ≠ b2 ∧ b1 ≠ b3 ∧ b2 ≠ b3 ∧
      (g14_nbB a).card = 3 ∧ hc_adjB a1 a = true ∧ hc_adjB a2 a = true ∧
      hc_adjB a1 qa1 = true ∧ a ≠ qa1 ∧ hc_adjB b qa1 = false ∧
      hc_adjB a2 qa2 = true ∧ a ≠ qa2 ∧ hc_adjB b qa2 = false ∧
      hc_adjB b1 b = true ∧ hc_adjB b2 b = true ∧ hc_adjB b3 b = true)
    (hAn : 1 ≤ (ru D br a).card) (hsub : ru D br a ⊆ ru D br b) (hBle : (ru D br b).card ≤ 2) :
    False := by
  obtain ⟨hab, ha12, c11, c12, c13, c21, c22, c23, b12, b13, b23, hda, ga1, ga2,
    gqa1, haqa1, gbqa1, gqa2, haqa2, gbqa2, gb1, gb2, gb3⟩ := hg
  obtain ⟨u, hu⟩ := Finset.card_pos.1 (by omega : 0 < (ru D br a).card)
  have hres : ∀ u' ∈ residualUnits 14 D br, a ∈ supp 14 D u'.1 → b ∈ supp 14 D u'.1 :=
    fun u' hu' ha' => (Finset.mem_filter.1 (hsub (Finset.mem_filter.2 ⟨hu', ha'⟩))).2
  have hw : a ∈ supp 14 D u.1 ∧ b ∈ supp 14 D u.1 :=
    ⟨(Finset.mem_filter.1 hu).2, (Finset.mem_filter.1 (hsub hu)).2⟩
  have hm1 := mem_W_of_pos hpos ha1 (pe_co_g14 h hD br hbr hpos ha1 ha hres hw ⟨hda, ga1, gqa1, hab, haqa1, gbqa1⟩)
  have hm2 := mem_W_of_pos hpos ha2 (pe_co_g14 h hD br hbr hpos ha2 ha hres hw ⟨hda, ga2, gqa2, hab, haqa2, gbqa2⟩)
  have hb1m := as_mem hpos hb1 ((hc_adjB_iff _ _).1 gb1)
  have hb2m := as_mem hpos hb2 ((hc_adjB_iff _ _).1 gb2)
  have hb3m := as_mem hpos hb3 ((hc_adjB_iff _ _).1 gb3)
  have h5 := pa_card5 hm1 hm2 hb1m hb2m hb3m
    (fun e => ha12 (hpos.2 _ ha1 _ ha2 e))
    (fun e => c11 (hpos.2 _ ha1 _ hb1 e))
    (fun e => c12 (hpos.2 _ ha1 _ hb2 e))
    (fun e => c13 (hpos.2 _ ha1 _ hb3 e))
    (fun e => c21 (hpos.2 _ ha2 _ hb1 e))
    (fun e => c22 (hpos.2 _ ha2 _ hb2 e))
    (fun e => c23 (hpos.2 _ ha2 _ hb3 e))
    (fun e => b12 (hpos.2 _ hb1 _ hb2 e))
    (fun e => b13 (hpos.2 _ hb1 _ hb3 e))
    (fun e => b23 (hpos.2 _ hb2 _ hb3 e))
  have hc4 := cc_le h hD br hbr b
  omega

theorem elim_126 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h11 : totalSurplus 14 D ≤ 11) (hI : ineligSet 14 D = hc_rep ⟨126, by decide⟩) : False := by
  have hIeq : ineligSet 14 D = {0, 2, 4, 7, 9} := by rw [hI]; decide +kernel
  have hE : ∀ x : Fin 14, x ∉ ({0, 2, 4, 7, 9} : Finset (Fin 14)) → x ∈ eligSet 14 D := fun x hx => by
    by_contra hc; exact hx (hIeq ▸ sem_mem_inelig.2 hc)
  exact elim_res2_3w3 h hD h11 ⟨126, by decide⟩ hI (by decide) (by rw [hIeq]; decide)
    1 8 10 7 9 13 0 2 6 0 4 5 3 5
    (hE 1 (by decide)) (hE 8 (by decide)) (hE 10 (by decide))
    (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
    (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem elim_129 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h11 : totalSurplus 14 D ≤ 11) (hI : ineligSet 14 D = hc_rep ⟨129, by decide⟩) : False := by
  have hIeq : ineligSet 14 D = {0, 2, 5, 7, 11} := by rw [hI]; decide +kernel
  have hE : ∀ x : Fin 14, x ∉ ({0, 2, 5, 7, 11} : Finset (Fin 14)) → x ∈ eligSet 14 D := fun x hx => by
    by_contra hc; exact hx (hIeq ▸ sem_mem_inelig.2 hc)
  exact elim_res2_3w3 h hD h11 ⟨129, by decide⟩ hI (by decide) (by rw [hIeq]; decide)
    3 8 10 7 11 12 0 2 6 0 5 4 1 4
    (hE 3 (by decide)) (hE 8 (by decide)) (hE 10 (by decide))
    (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
    (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem elim_131 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h11 : totalSurplus 14 D ≤ 11) (hI : ineligSet 14 D = hc_rep ⟨131, by decide⟩) : False := by
  have hIeq : ineligSet 14 D = {0, 2, 4, 7, 12} := by rw [hI]; decide +kernel
  have hE : ∀ x : Fin 14, x ∉ ({0, 2, 4, 7, 12} : Finset (Fin 14)) → x ∈ eligSet 14 D := fun x hx => by
    by_contra hc; exact hx (hIeq ▸ sem_mem_inelig.2 hc)
  exact elim_res2_3w3 h hD h11 ⟨131, by decide⟩ hI (by decide) (by rw [hIeq]; decide)
    3 8 10 7 12 11 0 2 6 0 4 5 1 5
    (hE 3 (by decide)) (hE 8 (by decide)) (hE 10 (by decide))
    (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
    (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem elim_132 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h11 : totalSurplus 14 D ≤ 11) (hI : ineligSet 14 D = hc_rep ⟨132, by decide⟩) : False := by
  classical
  have hIeq : ineligSet 14 D = {0, 2, 6, 7, 12} := by rw [hI]; decide +kernel
  have hE : ∀ x : Fin 14, x ∉ ({0, 2, 6, 7, 12} : Finset (Fin 14)) → x ∈ eligSet 14 D := fun x hx => by
    by_contra hc; exact hx (hIeq ▸ sem_mem_inelig.2 hc)
  have hBgt := bplus_gt_p1_ge5 h hD h11 ⟨132, by decide⟩ hI (by decide)
  have hel := inelig_card_add 14 D
  have hts := totalSurplus_split 14 D
  have hc5 : (ineligSet 14 D).card = 5 := by rw [hIeq]; decide
  have hB0 : Bzero 14 D = 0 := by omega
  obtain ⟨br, hbr⟩ := exists_pureBranch h hD
  obtain ⟨pos, hpos⟩ := k4_assigned sem_g14_gr h (sem_g14_comp hD)
  have hR2 : (residualUnits 14 D br).card = 2 := by
    have := card_residual h.1 br hbr; omega
  have h3n : 1 ≤ (ru D br 3).card := by
    have h3 := two_in_deg3 h hD hpos (by rw [hIeq]; decide : (7 : Fin 14) ∈ _)
      (by rw [hIeq]; decide : (12 : Fin 14) ∈ _) (u := 3) (v := 11) (by decide)
    have hc := cc_le h hD br hbr 3; omega
  have h8n : 1 ≤ (ru D br 8).card := by
    have h3 := two_in_deg3 h hD hpos (by rw [hIeq]; decide : (0 : Fin 14) ∈ _)
      (by rw [hIeq]; decide : (2 : Fin 14) ∈ _) (u := 8) (v := 6) (by decide)
    have hc := cc_le h hD br hbr 8; omega
  have hq3 : ∀ t : Fin 14, (t = 8 ∨ t = 5 ∨ t = 10) →
      ∃ q : Fin 14,
        (hc_adjB 7 q = true ∧ (3 : Fin 14) ≠ q ∧ hc_adjB t q = false ∧ hc_adjB 7 t = false) ∨
        (hc_adjB 12 q = true ∧ (3 : Fin 14) ≠ q ∧ hc_adjB t q = false ∧ hc_adjB 12 t = false) := by
    decide +kernel
  have hq8 : ∀ t : Fin 14, (t = 3 ∨ t = 5 ∨ t = 10) →
      ∃ q : Fin 14,
        (hc_adjB 0 q = true ∧ (8 : Fin 14) ≠ q ∧ hc_adjB t q = false ∧ hc_adjB 0 t = false) ∨
        (hc_adjB 2 q = true ∧ (8 : Fin 14) ≠ q ∧ hc_adjB t q = false ∧ hc_adjB 2 t = false) := by
    decide +kernel
  have h3le : (ru D br 3).card ≤ (residualUnits 14 D br).card := Finset.card_le_card (Finset.filter_subset _ _)
  have h8le : (ru D br 8).card ≤ (residualUnits 14 D br).card := Finset.card_le_card (Finset.filter_subset _ _)
  by_cases h82 : (ru D br 8).card = 2
  · have h8R : ru D br 8 = residualUnits 14 D br :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
    exact pe_co_blow5_all3 h hD br hbr hpos 3 8 7 12 1 5 0 2 6
      (hE 3 (by decide)) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (by decide) h3n ((Finset.filter_subset _ _).trans h8R.symm.subset) (by omega)
  · have h81 : (ru D br 8).card = 1 := by omega
    by_cases h32 : (ru D br 3).card = 2
    · have h3R : ru D br 3 = residualUnits 14 D br :=
        Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
      exact ru_sub_excl h hD hB0 br hbr hpos (by rw [hIeq]; decide) (by rw [hIeq]; decide)
        (hE 8 (by decide)) (v3 := 6) (by decide) h81
        ((Finset.filter_subset _ _).trans h3R.symm.subset) (by decide) (hq8 3 (Or.inl rfl))
    · have h31 : (ru D br 3).card = 1 := by omega
      obtain ⟨u3, hu3⟩ := Finset.card_eq_one.1 h31
      obtain ⟨u8, hu8⟩ := Finset.card_eq_one.1 h81
      have hu38 : u3 ≠ u8 := fun hh =>
        ru_sub_excl h hD hB0 br hbr hpos (by rw [hIeq]; decide) (by rw [hIeq]; decide)
          (hE 3 (by decide)) (v3 := 11) (by decide) h31
          (by rw [hu3, hu8, hh]) (by decide) (hq3 8 (Or.inl rfl))
      have hRu : residualUnits 14 D br = {u3, u8} := by
        symm
        refine Finset.eq_of_subset_of_card_le (fun u hu => ?_) (by rw [Finset.card_pair hu38, hR2])
        rw [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with h1 | h1
        · rw [h1]; exact (Finset.filter_subset _ _) (hu3 ▸ Finset.mem_singleton_self u3)
        · rw [h1]; exact (Finset.filter_subset _ _) (hu8 ▸ Finset.mem_singleton_self u8)
      have hru_emp : ∀ t : Fin 14, (t = 5 ∨ t = 10) → (sem_W 14 D t).card ≤ 2 := by
        intro t ht
        have ht3 : (3 : Fin 14) ≠ t := by rcases ht with rfl | rfl <;> decide
        have ht8 : (8 : Fin 14) ≠ t := by rcases ht with rfl | rfl <;> decide
        have hemp : ru D br t = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.2
          intro u hu
          have huR : u ∈ residualUnits 14 D br := (Finset.filter_subset _ _) hu
          rw [hRu, Finset.mem_insert, Finset.mem_singleton] at huR
          rcases huR with rfl | rfl
          · exact ru_sub_excl h hD hB0 br hbr hpos (by rw [hIeq]; decide) (by rw [hIeq]; decide)
              (hE 3 (by decide)) (v3 := 11) (by decide) h31
              (by rw [hu3, Finset.singleton_subset_iff]; exact hu) ht3 (hq3 t (Or.inr ht))
          · exact ru_sub_excl h hD hB0 br hbr hpos (by rw [hIeq]; decide) (by rw [hIeq]; decide)
              (hE 8 (by decide)) (v3 := 6) (by decide) h81
              (by rw [hu8, Finset.singleton_subset_iff]; exact hu) ht8 (hq8 t (Or.inr ht))
        have hc := cc_le h hD br hbr t
        rw [hemp, Finset.card_empty] at hc
        omega
      exact pa_m1 h hD hpos 5 10 9 12 0
        (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
        (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide)
        (hru_emp 5 (Or.inl rfl)) (hru_emp 10 (Or.inr rfl))

theorem cnt_b3_140_comb : ∀ m : Fin 128,
    let I := hc_rep ⟨140, by decide⟩
    let P := sideR \ I
    let Oc := maskFin7 m
    (∀ j ∈ Oc, g14_nbB (os_ptL j) ⊆ P) →
    let Oc3 := Oc.filter (fun j => (g14_nbB (os_ptL j)).card = 3)
    let Oc2 := Oc.filter (fun j => (g14_nbB (os_ptL j)).card = 2)
    let Ct := (Finset.univ : Finset (Fin 7)) \ Oc
    let Iin := Finset.univ.filter (fun j : Fin 7 => os_ptL j ∈ I ∧ g14_nbB (os_ptL j) ⊆ P)
    let Lab := Ct.biUnion (fun j => g14_nbB (os_ptL j) ∩ P)
    (2 * P.card + 11 < 2 * Oc3.card + Oc2.card + Iin.card + Lab.card + (14 - I.card) + (Iin \ Oc).card) ∨
    (11 < (17 - I.card) + (Iin \ Oc).card) := by
  decide +kernel

theorem elim_140 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h11 : totalSurplus 14 D ≤ 11) (hI : ineligSet 14 D = hc_rep ⟨140, by decide⟩) : False := by
  classical
  have hIeq : ineligSet 14 D = {0, 2, 4, 6, 7, 12} := by rw [hI]; decide +kernel
  have hE : ∀ x : Fin 14, x ∉ ({0, 2, 4, 6, 7, 12} : Finset (Fin 14)) → x ∈ eligSet 14 D := fun x hx => by
    by_contra hc; exact hx (hIeq ▸ sem_mem_inelig.2 hc)
  have hBgt := bplus_gt_p1_ge5 h hD h11 ⟨140, by decide⟩ hI (by decide)
  have hel := inelig_card_add 14 D
  have hts := totalSurplus_split 14 D
  have hc6 : (ineligSet 14 D).card = 6 := by rw [hIeq]; decide
  have hBlt11 : Bplus 14 D ≤ 10 := by
    by_contra hge11
    obtain ⟨m, hsub, hcnt, hlost⟩ := g14_sideR_step h hD
    have hcomb := cnt_b3_140_comb m
    dsimp only at hcomb hsub hcnt hlost
    rw [← hI] at hcomb
    rcases hcomb hsub with h1 | h2 <;> omega
  obtain ⟨br, hbr⟩ := exists_pureBranch h hD
  obtain ⟨pos, hpos⟩ := k4_assigned sem_g14_gr h (sem_g14_comp hD)
  have hR2 : (residualUnits 14 D br).card = 2 := by
    have := card_residual h.1 br hbr; omega
  have h3n : 1 ≤ (ru D br 3).card := by
    have h3 := two_in_deg3 h hD hpos (by rw [hIeq]; decide : (7 : Fin 14) ∈ _)
      (by rw [hIeq]; decide : (12 : Fin 14) ∈ _) (u := 3) (v := 11) (by decide)
    have hc := cc_le h hD br hbr 3; omega
  have h8n : 1 ≤ (ru D br 8).card := by
    have h3 := two_in_deg3 h hD hpos (by rw [hIeq]; decide : (0 : Fin 14) ∈ _)
      (by rw [hIeq]; decide : (2 : Fin 14) ∈ _) (u := 8) (v := 6) (by decide)
    have hc := cc_le h hD br hbr 8; omega
  have h11n : 1 ≤ (ru D br 11).card := by
    have h3 := two_in_deg3 h hD hpos (by rw [hIeq]; decide : (4 : Fin 14) ∈ _)
      (by rw [hIeq]; decide : (6 : Fin 14) ∈ _) (u := 11) (v := 3) (by decide)
    have hc := cc_le h hD br hbr 11; omega
  have h3le : (ru D br 3).card ≤ 2 := (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hR2
  have h8le : (ru D br 8).card ≤ 2 := (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hR2
  have h11le : (ru D br 11).card ≤ 2 := (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hR2
  by_cases h82 : (ru D br 8).card = 2
  · have h8R : ru D br 8 = residualUnits 14 D br :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
    exact pe_co_blow5_all3 h hD br hbr hpos 3 8 7 12 1 5 0 2 6
      (hE 3 (by decide)) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (by decide) h3n ((Finset.filter_subset _ _).trans h8R.symm.subset) h8le
  · have h81 : (ru D br 8).card = 1 := by omega
    obtain ⟨u8, hu8⟩ := Finset.card_eq_one.1 h81
    have hnu3 : u8 ∉ ru D br 3 := fun hin =>
      pe_co_blow5 h hD br hbr hpos 8 3 0 2 10 13 7 12 11
        (hE 8 (by decide)) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
        (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
        (by decide) h8n (by rw [hu8, Finset.singleton_subset_iff]; exact hin) h3le
    have hnu11 : u8 ∉ ru D br 11 := fun hin =>
      pe_co_blow5 h hD br hbr hpos 8 11 0 2 10 13 4 6 3
        (hE 8 (by decide)) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
        (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
        (by decide) h8n (by rw [hu8, Finset.singleton_subset_iff]; exact hin) h11le
    have hu8R : u8 ∈ residualUnits 14 D br := (Finset.filter_subset _ _) (hu8 ▸ Finset.mem_singleton_self u8)
    have hE1 : ((residualUnits 14 D br).erase u8).card = 1 := by rw [Finset.card_erase_of_mem hu8R, hR2]
    have h3eq : ru D br 3 = (residualUnits 14 D br).erase u8 :=
      Finset.eq_of_subset_of_card_le
        (fun x hx => Finset.mem_erase.2 ⟨fun h => hnu3 (h ▸ hx), (Finset.filter_subset _ _) hx⟩) (by omega)
    have h11eq : ru D br 11 = (residualUnits 14 D br).erase u8 :=
      Finset.eq_of_subset_of_card_le
        (fun x hx => Finset.mem_erase.2 ⟨fun h => hnu11 (h ▸ hx), (Finset.filter_subset _ _) hx⟩) (by omega)
    exact pe_co_blow5 h hD br hbr hpos 3 11 7 12 1 5 4 6 3
      (hE 3 (by decide)) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (by decide) h3n (by rw [h3eq, h11eq]) h11le

theorem elim_141 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h11 : totalSurplus 14 D ≤ 11) (hI : ineligSet 14 D = hc_rep ⟨141, by decide⟩) : False := by
  classical
  have hIeq : ineligSet 14 D = {0, 2, 4, 7, 9, 12} := by rw [hI]; decide +kernel
  have hE : ∀ x : Fin 14, x ∉ ({0, 2, 4, 7, 9, 12} : Finset (Fin 14)) → x ∈ eligSet 14 D := fun x hx => by
    by_contra hc; exact hx (hIeq ▸ sem_mem_inelig.2 hc)
  have hBgt := bplus_gt_p1_ge5 h hD h11 ⟨141, by decide⟩ hI (by decide)
  have hel := inelig_card_add 14 D
  have hts := totalSurplus_split 14 D
  have hc6 : (ineligSet 14 D).card = 6 := by rw [hIeq]; decide
  obtain ⟨br, hbr⟩ := exists_pureBranch h hD
  obtain ⟨pos, hpos⟩ := k4_assigned sem_g14_gr h (sem_g14_comp hD)
  have h1n : 1 ≤ (ru D br 1).card := by
    have h3 := two_in_deg3 h hD hpos (by rw [hIeq]; decide : (7 : Fin 14) ∈ _)
      (by rw [hIeq]; decide : (9 : Fin 14) ∈ _) (u := 1) (v := 13) (by decide)
    have hc := cc_le h hD br hbr 1; omega
  have h5n : 1 ≤ (ru D br 5).card := by
    have h3 := two_in_deg3 h hD hpos (by rw [hIeq]; decide : (9 : Fin 14) ∈ _)
      (by rw [hIeq]; decide : (12 : Fin 14) ∈ _) (u := 5) (v := 10) (by decide)
    have hc := cc_le h hD br hbr 5; omega
  have h8n : 1 ≤ (ru D br 8).card := by
    have h3 := two_in_deg3 h hD hpos (by rw [hIeq]; decide : (0 : Fin 14) ∈ _)
      (by rw [hIeq]; decide : (2 : Fin 14) ∈ _) (u := 8) (v := 6) (by decide)
    have hc := cc_le h hD br hbr 8; omega
  have h10n : 1 ≤ (ru D br 10).card := by
    have h3 := two_in_deg3 h hD hpos (by rw [hIeq]; decide : (0 : Fin 14) ∈ _)
      (by rw [hIeq]; decide : (4 : Fin 14) ∈ _) (u := 10) (v := 5) (by decide)
    have hc := cc_le h hD br hbr 10; omega
  have h13n : 1 ≤ (ru D br 13).card := by
    have h3 := two_in_deg3 h hD hpos (by rw [hIeq]; decide : (2 : Fin 14) ∈ _)
      (by rw [hIeq]; decide : (4 : Fin 14) ∈ _) (u := 13) (v := 1) (by decide)
    have hc := cc_le h hD br hbr 13; omega
  by_cases hB10 : Bplus 14 D = 10
  · -- Case `Bplus = 10`, `|R| = 2` (`Bzero`-free!)
    have hR2 : (residualUnits 14 D br).card = 2 := by
      have := card_residual h.1 br hbr; omega
    have h1le : (ru D br 1).card ≤ 2 := (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hR2
    have h8le : (ru D br 8).card ≤ 2 := (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hR2
    have h10le : (ru D br 10).card ≤ 2 := (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hR2
    by_cases h12 : (ru D br 1).card = 2
    · have h1R : ru D br 1 = residualUnits 14 D br :=
        Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
      exact pe_co_blow5 h hD br hbr hpos 10 1 0 4 8 11 7 9 13
        (hE 10 (by decide)) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
        (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
        (by decide) h10n ((Finset.filter_subset _ _).trans h1R.symm.subset) h1le
    · have h11' : (ru D br 1).card = 1 := by omega
      obtain ⟨u1, hu1⟩ := Finset.card_eq_one.1 h11'
      have hnu8 : u1 ∉ ru D br 8 := fun hin =>
        pe_co_blow5 h hD br hbr hpos 1 8 7 9 3 5 0 2 6
          (hE 1 (by decide)) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
          (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
          (by decide) h1n (by rw [hu1, Finset.singleton_subset_iff]; exact hin) h8le
      have hnu10 : u1 ∉ ru D br 10 := fun hin =>
        pe_co_blow5 h hD br hbr hpos 1 10 7 9 3 6 0 4 5
          (hE 1 (by decide)) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
          (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
          (by decide) h1n (by rw [hu1, Finset.singleton_subset_iff]; exact hin) h10le
      have hu1R : u1 ∈ residualUnits 14 D br := (Finset.filter_subset _ _) (hu1 ▸ Finset.mem_singleton_self u1)
      have hE1 : ((residualUnits 14 D br).erase u1).card = 1 := by rw [Finset.card_erase_of_mem hu1R, hR2]
      have h8eq : ru D br 8 = (residualUnits 14 D br).erase u1 :=
        Finset.eq_of_subset_of_card_le
          (fun x hx => Finset.mem_erase.2 ⟨fun h => hnu8 (h ▸ hx), (Finset.filter_subset _ _) hx⟩) (by omega)
      have h10eq : ru D br 10 = (residualUnits 14 D br).erase u1 :=
        Finset.eq_of_subset_of_card_le
          (fun x hx => Finset.mem_erase.2 ⟨fun h => hnu10 (h ▸ hx), (Finset.filter_subset _ _) hx⟩) (by omega)
      -- Now `ru 8 = ru 10` (size 1!), so `|W_10| ≤ 3` AND `pe_co` puts `pos 2 ∈ W_10`, giving `4 ≤ |W_10| ≤ 3`!
      obtain ⟨u, hu⟩ := Finset.card_pos.1 (by omega : 0 < (ru D br 8).card)
      have h8sub10 : ru D br 8 ⊆ ru D br 10 := by rw [h8eq, h10eq]
      have hres : ∀ u' ∈ residualUnits 14 D br, (8 : Fin 14) ∈ supp 14 D u'.1 → (10 : Fin 14) ∈ supp 14 D u'.1 :=
        fun u' hu' h8' => (Finset.mem_filter.1 (h8sub10 (Finset.mem_filter.2 ⟨hu', h8'⟩))).2
      have hw : (8 : Fin 14) ∈ supp 14 D u.1 ∧ (10 : Fin 14) ∈ supp 14 D u.1 :=
        ⟨(Finset.mem_filter.1 hu).2, (Finset.mem_filter.1 (h8sub10 hu)).2⟩
      have hp2 := mem_W_of_pos hpos (by rw [hIeq]; decide : (2 : Fin 14) ∈ _)
        (pe_co_g14 h hD br hbr hpos (by rw [hIeq]; decide) (hE 8 (by decide)) hres hw (q := 13) (by decide))
      have hp0 := as_mem hpos (by rw [hIeq]; decide : (0 : Fin 14) ∈ _) (by decide : Adj 0 10)
      have hp4 := as_mem hpos (by rw [hIeq]; decide : (4 : Fin 14) ∈ _) (by decide : Adj 4 10)
      obtain ⟨e5, he5, -, hf5, -⟩ := pa_ed h hD hpos (by decide : Adj 10 5)
      have h4 := pa_card4 hp2 hp0 hp4 he5
        (fun e => (by decide : (2 : Fin 14) ≠ 0) (hpos.2 _ (by rw [hIeq]; decide) _ (by rw [hIeq]; decide) e))
        (fun e => (by decide : (2 : Fin 14) ≠ 4) (hpos.2 _ (by rw [hIeq]; decide) _ (by rw [hIeq]; decide) e))
        (fun e => (by decide : (5 : Fin 14) ≠ 2) (hf5 2 (by rw [hIeq]; decide) e.symm))
        (fun e => (by decide : (0 : Fin 14) ≠ 4) (hpos.2 _ (by rw [hIeq]; decide) _ (by rw [hIeq]; decide) e))
        (fun e => (by decide : (5 : Fin 14) ≠ 0) (hf5 0 (by rw [hIeq]; decide) e.symm))
        (fun e => (by decide : (5 : Fin 14) ≠ 4) (hf5 4 (by rw [hIeq]; decide) e.symm))
      have hc3 := cc_le h hD br hbr 10
      rw [h10eq, hE1] at hc3
      omega
  · -- Case `Bplus = 11`, `Bzero = 0`, `|R| = 3`!
    have hB0 : Bzero 14 D = 0 := by omega
    have hR3 : (residualUnits 14 D br).card = 3 := by
      have := card_residual h.1 br hbr; omega
    have hq1 : ∀ t : Fin 14, (t = 5 ∨ t = 10 ∨ t = 13) → ∃ q : Fin 14,
        (hc_adjB 7 q = true ∧ (1 : Fin 14) ≠ q ∧ hc_adjB t q = false ∧ hc_adjB 7 t = false) ∨
        (hc_adjB 9 q = true ∧ (1 : Fin 14) ≠ q ∧ hc_adjB t q = false ∧ hc_adjB 9 t = false) := by decide +kernel
    have hq5 : ∀ t : Fin 14, (t = 1 ∨ t = 10 ∨ t = 13) → ∃ q : Fin 14,
        (hc_adjB 9 q = true ∧ (5 : Fin 14) ≠ q ∧ hc_adjB t q = false ∧ hc_adjB 9 t = false) ∨
        (hc_adjB 12 q = true ∧ (5 : Fin 14) ≠ q ∧ hc_adjB t q = false ∧ hc_adjB 12 t = false) := by decide +kernel
    have hq10 : ∀ t : Fin 14, (t = 1 ∨ t = 5 ∨ t = 13) → ∃ q : Fin 14,
        (hc_adjB 0 q = true ∧ (10 : Fin 14) ≠ q ∧ hc_adjB t q = false ∧ hc_adjB 0 t = false) ∨
        (hc_adjB 4 q = true ∧ (10 : Fin 14) ≠ q ∧ hc_adjB t q = false ∧ hc_adjB 4 t = false) := by decide +kernel
    have hq13 : ∀ t : Fin 14, (t = 1 ∨ t = 5 ∨ t = 10) → ∃ q : Fin 14,
        (hc_adjB 2 q = true ∧ (13 : Fin 14) ≠ q ∧ hc_adjB t q = false ∧ hc_adjB 2 t = false) ∨
        (hc_adjB 4 q = true ∧ (13 : Fin 14) ≠ q ∧ hc_adjB t q = false ∧ hc_adjB 4 t = false) := by decide +kernel
    -- Helper: no two of `1, 5, 10, 13` can have `|ru a| = 1` and `ru a ⊆ ru b`
    have hno1 : ∀ (a b : Fin 14), a ≠ b →
        (a = 1 ∨ a = 5 ∨ a = 10 ∨ a = 13) → (b = 1 ∨ b = 5 ∨ b = 10 ∨ b = 13) →
        (ru D br a).card = 1 → ru D br a ⊆ ru D br b → False := by
      intro a b hab ha hb h1 hsub
      rcases ha with rfl | rfl | rfl | rfl
      · rcases hb with rfl | rfl | rfl | rfl
        · exact hab rfl
        · exact ru_sub_excl h hD hB0 br hbr hpos (by rw [hIeq]; decide) (by rw [hIeq]; decide)
            (hE 1 (by decide)) (v3 := 13) (by decide) h1 hsub hab (hq1 5 (Or.inl rfl))
        · exact ru_sub_excl h hD hB0 br hbr hpos (by rw [hIeq]; decide) (by rw [hIeq]; decide)
            (hE 1 (by decide)) (v3 := 13) (by decide) h1 hsub hab (hq1 10 (Or.inr (Or.inl rfl)))
        · exact ru_sub_excl h hD hB0 br hbr hpos (by rw [hIeq]; decide) (by rw [hIeq]; decide)
            (hE 1 (by decide)) (v3 := 13) (by decide) h1 hsub hab (hq1 13 (Or.inr (Or.inr rfl)))
      · rcases hb with rfl | rfl | rfl | rfl
        · exact ru_sub_excl h hD hB0 br hbr hpos (by rw [hIeq]; decide) (by rw [hIeq]; decide)
            (hE 5 (by decide)) (v3 := 10) (by decide) h1 hsub hab (hq5 1 (Or.inl rfl))
        · exact hab rfl
        · exact ru_sub_excl h hD hB0 br hbr hpos (by rw [hIeq]; decide) (by rw [hIeq]; decide)
            (hE 5 (by decide)) (v3 := 10) (by decide) h1 hsub hab (hq5 10 (Or.inr (Or.inl rfl)))
        · exact ru_sub_excl h hD hB0 br hbr hpos (by rw [hIeq]; decide) (by rw [hIeq]; decide)
            (hE 5 (by decide)) (v3 := 10) (by decide) h1 hsub hab (hq5 13 (Or.inr (Or.inr rfl)))
      · rcases hb with rfl | rfl | rfl | rfl
        · exact ru_sub_excl h hD hB0 br hbr hpos (by rw [hIeq]; decide) (by rw [hIeq]; decide)
            (hE 10 (by decide)) (v3 := 5) (by decide) h1 hsub hab (hq10 1 (Or.inl rfl))
        · exact ru_sub_excl h hD hB0 br hbr hpos (by rw [hIeq]; decide) (by rw [hIeq]; decide)
            (hE 10 (by decide)) (v3 := 5) (by decide) h1 hsub hab (hq10 5 (Or.inr (Or.inl rfl)))
        · exact hab rfl
        · exact ru_sub_excl h hD hB0 br hbr hpos (by rw [hIeq]; decide) (by rw [hIeq]; decide)
            (hE 10 (by decide)) (v3 := 5) (by decide) h1 hsub hab (hq10 13 (Or.inr (Or.inr rfl)))
      · rcases hb with rfl | rfl | rfl | rfl
        · exact ru_sub_excl h hD hB0 br hbr hpos (by rw [hIeq]; decide) (by rw [hIeq]; decide)
            (hE 13 (by decide)) (v3 := 1) (by decide) h1 hsub hab (hq13 1 (Or.inl rfl))
        · exact ru_sub_excl h hD hB0 br hbr hpos (by rw [hIeq]; decide) (by rw [hIeq]; decide)
            (hE 13 (by decide)) (v3 := 1) (by decide) h1 hsub hab (hq13 5 (Or.inr (Or.inl rfl)))
        · exact ru_sub_excl h hD hB0 br hbr hpos (by rw [hIeq]; decide) (by rw [hIeq]; decide)
            (hE 13 (by decide)) (v3 := 1) (by decide) h1 hsub hab (hq13 10 (Or.inr (Or.inr rfl)))
        · exact hab rfl
    -- Helper: cross-pair `ru x ⊆ ru y` with `|ru y| ≤ 2` dies by `pe_co_blow5`
    have hcross : ∀ (x y : Fin 14),
        (x = 1 ∨ x = 5) → (y = 10 ∨ y = 13) →
        ru D br x ⊆ ru D br y → (ru D br y).card ≤ 2 → False := by
      intro x y hx hy hsub hyle
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact pe_co_blow5 h hD br hbr hpos 1 10 7 9 3 6 0 4 5 (hE 1 (by decide))
          (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
          (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide) h1n hsub hyle
      · exact pe_co_blow5 h hD br hbr hpos 1 13 7 9 3 6 2 4 1 (hE 1 (by decide))
          (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
          (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide) h1n hsub hyle
      · exact pe_co_blow5 h hD br hbr hpos 5 10 9 12 6 3 0 4 5 (hE 5 (by decide))
          (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
          (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide) h5n hsub hyle
      · exact pe_co_blow5 h hD br hbr hpos 5 13 9 12 6 3 2 4 1 (hE 5 (by decide))
          (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
          (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide) h5n hsub hyle
    -- Step 1: None of `1, 5, 10, 13` can have `|ru| = 1`!
    have hge2 : ∀ a : Fin 14, (a = 1 ∨ a = 5 ∨ a = 10 ∨ a = 13) → 2 ≤ (ru D br a).card := by
      intro a ha
      by_contra hlt
      have h1a : (ru D br a).card = 1 := by
        rcases ha with rfl | rfl | rfl | rfl <;> omega
      obtain ⟨ua, hua⟩ := Finset.card_eq_one.1 h1a
      have huaR : ua ∈ residualUnits 14 D br := (Finset.filter_subset _ _) (hua ▸ Finset.mem_singleton_self ua)
      have hE2 : ((residualUnits 14 D br).erase ua).card = 2 := by rw [Finset.card_erase_of_mem huaR, hR3]
      have hsubE : ∀ b : Fin 14, b ≠ a → (b = 1 ∨ b = 5 ∨ b = 10 ∨ b = 13) →
          ru D br b ⊆ (residualUnits 14 D br).erase ua := fun b hba hb x hx =>
        Finset.mem_erase.2 ⟨fun hxa => hno1 a b hba.symm ha hb h1a
          (by rw [hua, Finset.singleton_subset_iff]; exact hxa ▸ hx), (Finset.filter_subset _ _) hx⟩
      rcases ha with rfl | rfl | rfl | rfl
      · rcases three_subsets_of_two hE2 (A := ru D br 5) (B := ru D br 10) (C := ru D br 13)
            (hsubE 5 (by decide) (by decide)) (hsubE 10 (by decide) (by decide)) (hsubE 13 (by decide) (by decide))
            h5n h10n h13n with
          ⟨h1, hs | hs⟩ | ⟨h1, hs | hs⟩ | ⟨h1, hs | hs⟩ | ⟨hA, hB⟩
        · exact hno1 5 10 (by decide) (by decide) (by decide) h1 hs
        · exact hno1 5 13 (by decide) (by decide) (by decide) h1 hs
        · exact hno1 10 5 (by decide) (by decide) (by decide) h1 hs
        · exact hno1 10 13 (by decide) (by decide) (by decide) h1 hs
        · exact hno1 13 5 (by decide) (by decide) (by decide) h1 hs
        · exact hno1 13 10 (by decide) (by decide) (by decide) h1 hs
        · exact hcross 5 10 (Or.inr rfl) (Or.inl rfl) (by rw [hA, hB]) (by rw [hB, hE2])
      · rcases three_subsets_of_two hE2 (A := ru D br 1) (B := ru D br 10) (C := ru D br 13)
            (hsubE 1 (by decide) (by decide)) (hsubE 10 (by decide) (by decide)) (hsubE 13 (by decide) (by decide))
            h1n h10n h13n with
          ⟨h1, hs | hs⟩ | ⟨h1, hs | hs⟩ | ⟨h1, hs | hs⟩ | ⟨hA, hB⟩
        · exact hno1 1 10 (by decide) (by decide) (by decide) h1 hs
        · exact hno1 1 13 (by decide) (by decide) (by decide) h1 hs
        · exact hno1 10 1 (by decide) (by decide) (by decide) h1 hs
        · exact hno1 10 13 (by decide) (by decide) (by decide) h1 hs
        · exact hno1 13 1 (by decide) (by decide) (by decide) h1 hs
        · exact hno1 13 10 (by decide) (by decide) (by decide) h1 hs
        · exact hcross 1 10 (Or.inl rfl) (Or.inl rfl) (by rw [hA, hB]) (by rw [hB, hE2])
      · rcases three_subsets_of_two hE2 (A := ru D br 1) (B := ru D br 13) (C := ru D br 5)
            (hsubE 1 (by decide) (by decide)) (hsubE 13 (by decide) (by decide)) (hsubE 5 (by decide) (by decide))
            h1n h13n h5n with
          ⟨h1, hs | hs⟩ | ⟨h1, hs | hs⟩ | ⟨h1, hs | hs⟩ | ⟨hA, hB⟩
        · exact hno1 1 13 (by decide) (by decide) (by decide) h1 hs
        · exact hno1 1 5 (by decide) (by decide) (by decide) h1 hs
        · exact hno1 13 1 (by decide) (by decide) (by decide) h1 hs
        · exact hno1 13 5 (by decide) (by decide) (by decide) h1 hs
        · exact hno1 5 1 (by decide) (by decide) (by decide) h1 hs
        · exact hno1 5 13 (by decide) (by decide) (by decide) h1 hs
        · exact hcross 1 13 (Or.inl rfl) (Or.inr rfl) (by rw [hA, hB]) (by rw [hB, hE2])
      · rcases three_subsets_of_two hE2 (A := ru D br 1) (B := ru D br 10) (C := ru D br 5)
            (hsubE 1 (by decide) (by decide)) (hsubE 10 (by decide) (by decide)) (hsubE 5 (by decide) (by decide))
            h1n h10n h5n with
          ⟨h1, hs | hs⟩ | ⟨h1, hs | hs⟩ | ⟨h1, hs | hs⟩ | ⟨hA, hB⟩
        · exact hno1 1 10 (by decide) (by decide) (by decide) h1 hs
        · exact hno1 1 5 (by decide) (by decide) (by decide) h1 hs
        · exact hno1 10 1 (by decide) (by decide) (by decide) h1 hs
        · exact hno1 10 5 (by decide) (by decide) (by decide) h1 hs
        · exact hno1 5 1 (by decide) (by decide) (by decide) h1 hs
        · exact hno1 5 10 (by decide) (by decide) (by decide) h1 hs
        · exact hcross 1 10 (Or.inl rfl) (Or.inl rfl) (by rw [hA, hB]) (by rw [hB, hE2])
    -- Step 2: None of `1, 5, 10, 13` can have `|ru| = 3` (else `6 ≤ |W| ≤ 5`)!
    have hblow6 : ∀ (x y1 y2 x1 x2 vx j1 j2 j3 q1 q2 q3 : Fin 14),
        x ∈ eligSet 14 D → y1 ∈ eligSet 14 D → y2 ∈ eligSet 14 D →
        x1 ∈ ineligSet 14 D → x2 ∈ ineligSet 14 D → vx ∉ ineligSet 14 D →
        j1 ∈ ineligSet 14 D → j2 ∈ ineligSet 14 D → j3 ∈ ineligSet 14 D →
        (y1 ≠ x ∧ y2 ≠ x ∧ (g14_nbB y1).card = 3 ∧ (g14_nbB y2).card = 3 ∧
         hc_adjB j1 y1 = true ∧ hc_adjB j2 y1 = true ∧ hc_adjB j3 y2 = true ∧
         hc_adjB j1 q1 = true ∧ y1 ≠ q1 ∧ hc_adjB x q1 = false ∧
         hc_adjB j2 q2 = true ∧ y1 ≠ q2 ∧ hc_adjB x q2 = false ∧
         hc_adjB j3 q3 = true ∧ y2 ≠ q3 ∧ hc_adjB x q3 = false ∧
         hc_adjB x1 x = true ∧ hc_adjB x2 x = true ∧ hc_adjB x vx = true ∧
         x1 ≠ x2 ∧ x1 ≠ j1 ∧ x1 ≠ j2 ∧ x1 ≠ j3 ∧ x2 ≠ j1 ∧ x2 ≠ j2 ∧ x2 ≠ j3 ∧
         j1 ≠ j2 ∧ j1 ≠ j3 ∧ j2 ≠ j3) →
        1 ≤ (ru D br y1).card → 1 ≤ (ru D br y2).card → (ru D br x).card = 3 → False := by
      intro x y1 y2 x1 x2 vx j1 j2 j3 q1 q2 q3 _ hy1 hy2 hx1 hx2 hvx hj1 hj2 hj3 hg hy1n hy2n hx3
      obtain ⟨hy1x, hy2x, hdy1, hdy2, gj1, gj2, gj3, gq1, hq1, gxq1, gq2, hq2, gxq2, gq3, hq3, gxq3,
        gx1, gx2, gvx, d12, d1j1, d1j2, d1j3, d2j1, d2j2, d2j3, dj12, dj13, dj23⟩ := hg
      have hxR : ru D br x = residualUnits 14 D br :=
        Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
      have hs1 : ru D br y1 ⊆ ru D br x := (Finset.filter_subset _ _).trans hxR.symm.subset
      have hs2 : ru D br y2 ⊆ ru D br x := (Finset.filter_subset _ _).trans hxR.symm.subset
      obtain ⟨u1, hu1⟩ := Finset.card_pos.1 (by omega : 0 < (ru D br y1).card)
      obtain ⟨u2, hu2⟩ := Finset.card_pos.1 (by omega : 0 < (ru D br y2).card)
      have hres1 : ∀ u' ∈ residualUnits 14 D br, y1 ∈ supp 14 D u'.1 → x ∈ supp 14 D u'.1 :=
        fun u' hu' h' => (Finset.mem_filter.1 (hs1 (Finset.mem_filter.2 ⟨hu', h'⟩))).2
      have hres2 : ∀ u' ∈ residualUnits 14 D br, y2 ∈ supp 14 D u'.1 → x ∈ supp 14 D u'.1 :=
        fun u' hu' h' => (Finset.mem_filter.1 (hs2 (Finset.mem_filter.2 ⟨hu', h'⟩))).2
      have hw1 : y1 ∈ supp 14 D u1.1 ∧ x ∈ supp 14 D u1.1 := ⟨(Finset.mem_filter.1 hu1).2, (Finset.mem_filter.1 (hs1 hu1)).2⟩
      have hw2 : y2 ∈ supp 14 D u2.1 ∧ x ∈ supp 14 D u2.1 := ⟨(Finset.mem_filter.1 hu2).2, (Finset.mem_filter.1 (hs2 hu2)).2⟩
      have m1 := mem_W_of_pos hpos hj1 (pe_co_g14 h hD br hbr hpos hj1 hy1 hres1 hw1 ⟨hdy1, gj1, gq1, hy1x, hq1, gxq1⟩)
      have m2 := mem_W_of_pos hpos hj2 (pe_co_g14 h hD br hbr hpos hj2 hy1 hres1 hw1 ⟨hdy1, gj2, gq2, hy1x, hq2, gxq2⟩)
      have m3 := mem_W_of_pos hpos hj3 (pe_co_g14 h hD br hbr hpos hj3 hy2 hres2 hw2 ⟨hdy2, gj3, gq3, hy2x, hq3, gxq3⟩)
      have mx1 := as_mem hpos hx1 ((hc_adjB_iff _ _).1 gx1)
      have mx2 := as_mem hpos hx2 ((hc_adjB_iff _ _).1 gx2)
      obtain ⟨ev, hev, -, hfv, -⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gvx)
      have h6 := pa_card6 mx1 mx2 m1 m2 m3 hev
        (fun e => d12 (hpos.2 _ hx1 _ hx2 e)) (fun e => d1j1 (hpos.2 _ hx1 _ hj1 e))
        (fun e => d1j2 (hpos.2 _ hx1 _ hj2 e)) (fun e => d1j3 (hpos.2 _ hx1 _ hj3 e))
        (fun e => hvx (hfv _ hx1 e.symm ▸ hx1))
        (fun e => d2j1 (hpos.2 _ hx2 _ hj1 e)) (fun e => d2j2 (hpos.2 _ hx2 _ hj2 e))
        (fun e => d2j3 (hpos.2 _ hx2 _ hj3 e)) (fun e => hvx (hfv _ hx2 e.symm ▸ hx2))
        (fun e => dj12 (hpos.2 _ hj1 _ hj2 e)) (fun e => dj13 (hpos.2 _ hj1 _ hj3 e))
        (fun e => hvx (hfv _ hj1 e.symm ▸ hj1))
        (fun e => dj23 (hpos.2 _ hj2 _ hj3 e)) (fun e => hvx (hfv _ hj2 e.symm ▸ hj2))
        (fun e => hvx (hfv _ hj3 e.symm ▸ hj3))
      have hc5 := cc_le h hD br hbr x
      omega
    have hne3_1 : (ru D br 1).card ≠ 3 := hblow6 1 10 13 7 9 13 0 4 2 8 11 8
      (hE 1 (by decide)) (hE 10 (by decide)) (hE 13 (by decide))
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide) h10n h13n
    have hne3_5 : (ru D br 5).card ≠ 3 := hblow6 5 10 13 9 12 10 0 4 2 8 11 8
      (hE 5 (by decide)) (hE 10 (by decide)) (hE 13 (by decide))
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide) h10n h13n
    have hne3_10 : (ru D br 10).card ≠ 3 := hblow6 10 1 5 0 4 5 7 9 12 3 6 3
      (hE 10 (by decide)) (hE 1 (by decide)) (hE 5 (by decide))
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide) h1n h5n
    have hne3_13 : (ru D br 13).card ≠ 3 := hblow6 13 1 5 2 4 1 7 9 12 3 6 3
      (hE 13 (by decide)) (hE 1 (by decide)) (hE 5 (by decide))
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide) h1n h5n
    -- Step 3: All four have `|ru| = 2`, so by `four_2subsets_of_three` two are equal!
    have hc1_2 : (ru D br 1).card = 2 := by
      have := hge2 1 (by decide); have : (ru D br 1).card ≤ 3 := (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hR3; omega
    have hc5_2 : (ru D br 5).card = 2 := by
      have := hge2 5 (by decide); have : (ru D br 5).card ≤ 3 := (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hR3; omega
    have hc10_2 : (ru D br 10).card = 2 := by
      have := hge2 10 (by decide); have : (ru D br 10).card ≤ 3 := (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hR3; omega
    have hc13_2 : (ru D br 13).card = 2 := by
      have := hge2 13 (by decide); have : (ru D br 13).card ≤ 3 := (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hR3; omega
    have hsame_kill : ∀ (a b i0 ia ib vb qab qba : Fin 14),
        a ∈ eligSet 14 D → b ∈ eligSet 14 D →
        i0 ∈ ineligSet 14 D → ia ∈ ineligSet 14 D → ib ∈ ineligSet 14 D → vb ∉ ineligSet 14 D →
        (a ≠ b ∧ (g14_nbB a).card = 3 ∧ (g14_nbB b).card = 3 ∧
         i0 ≠ ia ∧ i0 ≠ ib ∧ ia ≠ ib ∧ vb ≠ i0 ∧ vb ≠ ia ∧ vb ≠ ib ∧
         hc_adjB i0 a = true ∧ hc_adjB ia a = true ∧ hc_adjB i0 b = true ∧ hc_adjB ib b = true ∧
         hc_adjB b vb = true ∧ hc_adjB ia qab = true ∧ a ≠ qab ∧ hc_adjB b qab = false ∧
         hc_adjB ib qba = true ∧ b ≠ qba ∧ hc_adjB a qba = false ∧ hc_adjB ib a = false) →
        (ru D br a).card = 2 → (ru D br b).card = 2 → ru D br a = ru D br b → False := by
      intro a b i0 ia ib vb qab qba ha hb hi0 hia hib hvb hg ha2 hb2 heq
      obtain ⟨hab, hda, hdb, d0a, d0b, dab, v0, va, vb', g0a, gaa, g0b, gbb, gv, gq1, hq1, gnq1, gq2, hq2, gnq2, gnba⟩ := hg
      obtain ⟨u, hu⟩ := Finset.card_pos.1 (by omega : 0 < (ru D br a).card)
      have hres1 : ∀ u' ∈ residualUnits 14 D br, a ∈ supp 14 D u'.1 → b ∈ supp 14 D u'.1 := by
        intro u' hu' ha'; have hm : u' ∈ ru D br a := Finset.mem_filter.2 ⟨hu', ha'⟩; rw [heq] at hm; exact (Finset.mem_filter.1 hm).2
      have hres2 : ∀ u' ∈ residualUnits 14 D br, b ∈ supp 14 D u'.1 → a ∈ supp 14 D u'.1 := by
        intro u' hu' hb'; have hm : u' ∈ ru D br b := Finset.mem_filter.2 ⟨hu', hb'⟩; rw [← heq] at hm; exact (Finset.mem_filter.1 hm).2
      have hw : a ∈ supp 14 D u.1 ∧ b ∈ supp 14 D u.1 :=
        ⟨(Finset.mem_filter.1 hu).2, (Finset.mem_filter.1 (show u ∈ ru D br b from heq ▸ hu)).2⟩
      have hpa_in_b := mem_W_of_pos hpos hia (pe_co_g14 h hD br hbr hpos hia ha hres1 hw ⟨hda, gaa, gq1, hab, hq1, gnq1⟩)
      have ha_in_pb := pe_co_g14 h hD br hbr hpos hib hb hres2 ⟨hw.2, hw.1⟩ ⟨hdb, gbb, gq2, hab.symm, hq2, gnq2⟩
      have hp0_in_b := as_mem hpos hi0 ((hc_adjB_iff _ _).1 g0b)
      have hpb_in_b := as_mem hpos hib ((hc_adjB_iff _ _).1 gbb)
      obtain ⟨ev, hev, hbev, hfv, -⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gv)
      have hWb_le4 : (sem_W 14 D b).card ≤ 4 := by have := cc_le h hD br hbr b; omega
      have hWb := pa_four hpb_in_b hp0_in_b hpa_in_b hev
        (fun e => d0b.symm (hpos.2 _ hib _ hi0 e))
        (fun e => dab.symm (hpos.2 _ hib _ hia e))
        (fun e => hvb (hfv _ hib e.symm ▸ hib))
        (fun e => d0a (hpos.2 _ hi0 _ hia e))
        (fun e => hvb (hfv _ hi0 e.symm ▸ hi0))
        (fun e => hvb (hfv _ hia e.symm ▸ hia))
        hWb_le4
      have hfull := full_g14 h hD hB0 hpos hib ((hc_adjB_iff _ _).1 gbb) (fun p hp hne1 hsub => by
        rcases hWb p hp with rfl | rfl | rfl | rfl
        · exact hne1 rfl
        · have hm : i0 ∈ supp 14 D (src D (sem_bar (pos i0))) := by
            rw [show src D (sem_bar (pos i0)) = src D ((pos i0).1, !(pos i0).2) from rfl,
              (hpos.1 i0 hi0).2.2.2]; exact Finset.mem_singleton_self i0
          exact d0b (Finset.mem_singleton.1 (hsub hm))
        · have hm : ia ∈ supp 14 D (src D (sem_bar (pos ia))) := by
            rw [show src D (sem_bar (pos ia)) = src D ((pos ia).1, !(pos ia).2) from rfl,
              (hpos.1 ia hia).2.2.2]; exact Finset.mem_singleton_self ia
          exact dab (Finset.mem_singleton.1 (hsub hm))
        · exact vb' (Finset.mem_singleton.1 (hsub (sem_mem_W.1 hbev).2.1)))
      exact sem_adjB_false.1 gnba ((hfull a).1 ha_in_pb)
    rcases four_2subsets_of_three hR3 (A := ru D br 1) (B := ru D br 5) (C := ru D br 10) (D := ru D br 13)
        (Finset.filter_subset _ _) (Finset.filter_subset _ _) (Finset.filter_subset _ _) (Finset.filter_subset _ _)
        hc1_2 hc5_2 hc10_2 hc13_2 with
      heq | heq | heq | heq | heq | heq
    · exact hsame_kill 1 5 9 7 12 10 3 3 (hE 1 (by decide)) (hE 5 (by decide))
        (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
        (by decide) hc1_2 hc5_2 heq
    · exact hcross 1 10 (Or.inl rfl) (Or.inl rfl) (by rw [heq]) (by omega)
    · exact hcross 1 13 (Or.inl rfl) (Or.inr rfl) (by rw [heq]) (by omega)
    · exact hcross 5 10 (Or.inr rfl) (Or.inl rfl) (by rw [heq]) (by omega)
    · exact hcross 5 13 (Or.inr rfl) (Or.inr rfl) (by rw [heq]) (by omega)
    · exact hsame_kill 10 13 4 0 2 1 8 8 (hE 10 (by decide)) (hE 13 (by decide))
        (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
        (by decide) hc10_2 hc13_2 heq

/-! ## Final dispatch over all 143 canonical orbits -/

theorem g14_orbit_partition : ∀ idx : Fin 143,
    (hc_rep idx).card = 3 ∨
    (∃ k : Fin 52, no_i0_4_idx k = idx) ∨
    (∃ k : Fin 31, cnt_b1_idx k = idx) ∨
    (∃ k : Fin 3, cnt_b2_idx k = idx) ∨
    idx.val = 96 ∨ idx.val = 126 ∨ idx.val = 129 ∨ idx.val = 130 ∨
    idx.val = 131 ∨ idx.val = 132 ∨ idx.val = 140 ∨ idx.val = 141 := by
  decide +kernel

theorem g14_lb_25 (C : Circuit) (hmono : Monotone2 C)
    (hC : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ G14Edge x) (hsize : C.size ≤ 24) :
    False := by
  obtain ⟨D, h, hD, -, h11, -, hmem⟩ := g14_wlog_canon C hmono hC hsize
  obtain ⟨idx, hI⟩ := hc_rep_of_mem hmem
  have hI' : ineligSet 14 D = hc_rep idx := hI.symm
  have hts := totalSurplus_split 14 D
  have hel := inelig_card_add 14 D
  rcases g14_orbit_partition idx with
    hc3 | ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩ | h96 | h126 | h129 | h130 | h131 | h132 | h140 | h141
  · rw [← hI'] at hc3
    exact tight_le_all h hD (by omega) idx hI'
  · exact elim_no_i0_4 h hD h11 k hI'
  · exact elim_cnt_b1 h hD h11 k hI'
  · exact elim_cnt_b2 h hD h11 k hI'
  · have : idx = ⟨96, by decide⟩ := Fin.ext h96
    exact elim_13810 h hD h11 (this ▸ hI')
  · have : idx = ⟨126, by decide⟩ := Fin.ext h126
    exact elim_126 h hD h11 (this ▸ hI')
  · have : idx = ⟨129, by decide⟩ := Fin.ext h129
    exact elim_129 h hD h11 (this ▸ hI')
  · have : idx = ⟨130, by decide⟩ := Fin.ext h130
    exact elim_130 h hD h11 (this ▸ hI')
  · have : idx = ⟨131, by decide⟩ := Fin.ext h131
    exact elim_131 h hD h11 (this ▸ hI')
  · have : idx = ⟨132, by decide⟩ := Fin.ext h132
    exact elim_132 h hD h11 (this ▸ hI')
  · have : idx = ⟨140, by decide⟩ := Fin.ext h140
    exact elim_140 h hD h11 (this ▸ hI')
  · have : idx = ⟨141, by decide⟩ := Fin.ext h141
    exact elim_141 h hD h11 (this ▸ hI')

end PEqualNP.Outside.L_meta_9777_aux

theorem PEqualNP.Outside.L_meta_9777 :
    ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 24 ∧ (∀ x : Fin 14 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 14, (u.val, v.val) ∈ ([(0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true))) := by
  rintro ⟨C, hmono, hsize, hC⟩
  exact PEqualNP.Outside.L_meta_9777_aux.g14_lb_25 C hmono hC hsize
