import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9774_aux

-- Circuit normalization and wire counting, adapted from L_meta_971.
namespace DagTools

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

theorem card_unitsPlus (n : ℕ) (D : Dag) : (unitsPlus n D).card = Bplus n D := by
  unfold unitsPlus Bplus
  exact sb_card_units_filter n D (fun w => (supp n D w).Nonempty)

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

theorem inelig_card_add (n : ℕ) (D : Dag) : (ineligSet n D).card + (eligSet n D).card = n := by
  have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (eligSet n D))
  rw [Finset.card_univ, Fintype.card_fin] at h
  exact h

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

end SemCodes

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

end K4Generic

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

end L3bGen

end DagTools

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_9774_aux.DagTools

def edges : List (Nat × Nat) := [(0,8),(0,10),(1,7),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]

def hit (x : Fin 14 → Bool) := ∃ u v : Fin 14, (u.val,v.val) ∈ edges ∧ x u = true ∧ x v = true

def computes (C : Circuit) := ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ hit x

theorem input_bit {n} (x : Fin n → Bool) (i : Fin n) : (List.ofFn x).getD i.val false = x i := by
  simp [List.getD_eq_getElem?_getD, i.isLt]

open PEqualNP.Outside.L_meta_9774_aux.DagTools PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

abbrev V := Fin 14

def neigh (v : V) : Nat := [1280, 8320, 12544, 6272, 11264, 5632, 2816, 10, 69, 96, 49, 88, 44, 22].getD v.val 0

def adj (u v : V) : Prop := (neigh u).testBit v.val = true

instance (u v : V) : Decidable (adj u v) := inferInstanceAs (Decidable ((neigh u).testBit v.val = true))

theorem graph_ok : sem_Gr adj := by unfold sem_Gr; decide +kernel

theorem graph_edges : ∀ u v : V, adj u v ↔ (u.val,v.val)∈edges ∨ (v.val,u.val)∈edges := by decide +kernel

theorem agrees (x : V → Bool) : hit x ↔ sem_Edge adj x := by
  constructor
  · rintro ⟨u,v,e,hu,hv⟩
    exact ⟨u,v,(graph_edges u v).2 (Or.inl e),hu,hv⟩
  · rintro ⟨u,v,a,hu,hv⟩
    rcases (graph_edges u v).1 a with e|e
    · exact ⟨u,v,e,hu,hv⟩
    · exact ⟨v,u,e,hv,hu⟩

theorem empty_bad : ¬hit (fun _ => false) := by rintro ⟨_,_,_,h,_⟩; contradiction

theorem single_bad (i : V) : ¬hit (single i) := fun h => sem_single_no_edge graph_ok i ((agrees _).mp h)

theorem normalized (C : Circuit) (hm : Monotone2 C) (hc : computes C) :
    ∃ D : Dag, StrictLive 14 D ∧ D.length ≤ C.size ∧ sem_Comp 14 adj D := by
  obtain ⟨D,hd,le,ev⟩ := normalize_strictLive (n:=14) C hm (by
    intro b
    cases b
    · refine ⟨fun _ => true,?_⟩
      rw [Ne, Bool.not_eq_false]
      exact (hc _).2 ⟨0,8,by decide,rfl,rfl⟩
    · exact ⟨fun _ => false,fun h => empty_bad ((hc _).1 h)⟩) (by
    intro i
    exact ⟨single i,fun h => single_bad i ((hc _).1 (by rw [h]; simp [single]))⟩) (by
    intro i
    obtain ⟨j,ij,ne⟩ := graph_ok.2.2.2 i i
    refine ⟨single j,sem_two i j,?_,?_⟩
    · intro k hki; simp [sem_two,single,hki]
    · intro h
      exact single_bad j ((hc _).1 (h.trans ((hc _).2 ((agrees _).2 (sem_two_edge ij))))))
  exact ⟨D,hd,le,fun x => by rw [ev,hc]; exact agrees x⟩

def mask (m : Nat) : Finset V := Finset.univ.filter (fun v => m.testBit v.val)

def independent (T : Finset V) : Prop := ∀ a ∈ T, ∀ b ∈ T, ¬adj a b

instance (T : Finset V) : Decidable (independent T) := inferInstanceAs (Decidable (∀ a ∈ T, ∀ b ∈ T, ¬adj a b))

def ValidPrivate (T J : Finset V) (A : V → Finset V) : Prop :=
  (∀ i ∈ J, (∃ a ∈ T, adj i a) ∧ ∀ f ∈ T, ∃ a ∈ A f, adj i a) ∧
  (∀ f ∈ T, independent (A f) ∧ T.erase f ⊆ A f ∧ ∃ a ∈ A f, adj f a)

instance (T J : Finset V) (A : V → Finset V) : Decidable (ValidPrivate T J A) := by unfold ValidPrivate; infer_instance

def cost (D : Dag) (T : Finset V) := (merges 14 D (carrierT 14 D T)).card

theorem bound_rule {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (T J : Finset V) (A : V → Finset V) (valid : ValidPrivate T J A)
    (hJ : J⊆ineligSet 14 D) (m k : Nat) (hm : m≤cost D T) (hk : k+T.card ≤ J.card+m) :
    (eligSet 14 D).card+k ≤ Bplus 14 D := by
  obtain ⟨b,hb⟩ := sem_exists_pureBranch graph_ok h.1 hc
  obtain ⟨pos,hpos⟩ := k4_assigned graph_ok h hc
  have ex := tri_exits graph_ok h.1 hc hpos T J A
    (fun i hi => ⟨hJ hi,(valid.1 i hi).1,(valid.1 i hi).2⟩) valid.2
  have cap := k4_budget graph_ok h hc b hb T
  unfold cost at hm
  omega

theorem share {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    {i x y : V} (hi : i∈ineligSet 14 D) (hx : adj i x) (hy : adj i y) :
    ∃ w : Nat, x∈supp 14 D w ∧ y∈supp 14 D w := by
  obtain ⟨e,_,_,_,_,hn,_⟩ := sem_inelig_consumer graph_ok h hc hi
  exact ⟨_,hn x hx,hn y hy⟩

theorem cost_one {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (T : Finset V) (i x y : V) (hi : i∈ineligSet 14 D)
    (geom : adj i x ∧ adj i y ∧ x∈T ∧ y∈T ∧ x≠y) : 1≤cost D T := by
  obtain ⟨w,hx,hy⟩ := share h hc hi geom.1 geom.2.1
  obtain ⟨j,hj,_⟩ := k4_mask_gate h.1 T w (Finset.one_lt_card.mpr
    ⟨x,Finset.mem_inter.mpr ⟨hx,geom.2.2.1⟩,y,Finset.mem_inter.mpr ⟨hy,geom.2.2.2.1⟩,geom.2.2.2.2⟩)
  exact Finset.card_pos.mpr ⟨j,hj⟩

theorem cost_two {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (T : Finset V) (i j x y z : V) (hi : i∈ineligSet 14 D) (hj : j∈ineligSet 14 D)
    (geom : adj i x ∧ adj i y ∧ adj j x ∧ adj j z ∧ T.card=3 ∧ x∈T ∧ y∈T ∧ z∈T ∧ x≠y ∧ x≠z ∧ y≠z) :
    2≤cost D T := by
  rcases geom with ⟨ix,iy,jx,jz,t3,xt,yt,zt,xy,xz,yz⟩
  obtain ⟨w,hx,hy⟩ := share h hc hi ix iy
  obtain ⟨v,hx',hz⟩ := share h hc hj jx jz
  exact k4_pair_merges h.1 t3 xt yt zt xy xz yz hx hy hx' hz

open PEqualNP.Outside.L_meta_9774_aux.DagTools

def projected (P : Finset V) (i : V) := P.filter (adj i)

set_option maxHeartbeats 0 in
theorem occurs {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (hz : Bzero 14 D = 0)
    (P : Finset V) (hind : independent P) (i : V) (hi : i∈ineligSet 14 D) :
    sup_Occ 14 D P (projected P i) := by
  obtain ⟨j,s,_,_,_,ex⟩ := sem_exact_nbhd graph_ok h.1 hc P hind (sem_noempty_chain_out graph_ok h hc hz hi)
  refine ⟨src D (j,s),?_⟩
  ext a
  simp only [Finset.mem_inter,projected,Finset.mem_filter]
  constructor
  · rintro ⟨ha,hin⟩; exact ⟨hin,(ex a hin).1 ha⟩
  · rintro ⟨hin,ha⟩; exact ⟨(ex a hin).2 ha,hin⟩

set_option maxHeartbeats 0 in
theorem full_cost {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (hz : Bzero 14 D=0)
    (P I : Finset V) (hind : independent P) (sub : I ⊆ ineligSet 14 D)
    (L X : Finset (Finset V)) (P7 : P.card≤7)
    (tri : ∀ T∈L, T.card=3)
    (distinct : ∀ T∈L, ∀ U∈L, T≠U → (T∩U).card≤1)
    (cover : ∀ M∈L∪X, ∃ i∈I, projected P i=M)
    (pairs : ∀ M∈X, M.card=2 ∧ M∉L ∧ ∀ T∈L, ¬M⊆T)
    (conn : ∀ i∈I, ∃ a∈P, adj i a) :
    2*L.card + X.card + I.card + (eligSet 14 D).card ≤ 2*P.card+Bplus 14 D := by
  obtain ⟨b,hb⟩ := sem_exists_pureBranch graph_ok h.1 hc
  obtain ⟨pos,hpos⟩ := k4_assigned graph_ok h hc
  have occ (M) (hm : M∈L∪X) : sup_Occ 14 D P M := by
    obtain ⟨i,hi,rfl⟩ := cover _ hm
    exact occurs h hc hz P hind i (sub hi)
  have u := sup_charge h.1 P7 L (fun T ht => ⟨tri T ht,occ T (Finset.mem_union_left _ ht)⟩) distinct X (fun M hm => by
    obtain ⟨c,nl,nt⟩ := pairs M hm
    exact ⟨occ M (Finset.mem_union_right _ hm),by omega,nl,by omega,by omega,fun _ => nt⟩)
  have v : (sup_big 14 D P).card ≤ (merges 14 D (carrierT 14 D P)).card := Finset.card_le_card (Finset.filter_subset _ _ : sup_big 14 D P ⊆ merges 14 D (carrierT 14 D P))
  obtain ⟨ex,eq⟩ := k4_exits_ge hpos P I (fun i hi => ⟨sub hi,conn _ hi⟩)
  have w := Finset.card_le_card ex
  have cap := k4_budget graph_ok h hc b hb P
  omega

set_option maxHeartbeats 0 in
theorem side127 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (hz : Bzero 14 D=0) (sub : mask 127 = ineligSet 14 D) : 12≤Bplus 14 D := by
  let P := mask 16256
  let I := mask 127
  let L : Finset (Finset V) := {mask 12544,mask 6272,mask 11264,mask 5632,mask 2816}
  let X : Finset (Finset V) := {mask 1280,mask 8320}
  have hsub : I ⊆ ineligSet 14 D := sub ▸ Finset.Subset.rfl
  have tri : ∀ T∈L, T.card=3 := by
    intro T ht; simp only [L,Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  have distinct : ∀ T∈L, ∀ U∈L, T≠U → (T∩U).card≤1 := by
    intro T ht U hu
    simp only [L,Finset.mem_insert,Finset.mem_singleton] at ht hu
    rcases ht with rfl | rfl | rfl | rfl | rfl <;> rcases hu with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  have hits : ∀ M∈L∪X, ∃ i∈I, projected P i=M := by
    intro M hm; simp only [L,X,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with (rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)
    · exact ⟨2,by decide +kernel,by decide +kernel⟩
    · exact ⟨3,by decide +kernel,by decide +kernel⟩
    · exact ⟨4,by decide +kernel,by decide +kernel⟩
    · exact ⟨5,by decide +kernel,by decide +kernel⟩
    · exact ⟨6,by decide +kernel,by decide +kernel⟩
    · exact ⟨0,by decide +kernel,by decide +kernel⟩
    · exact ⟨1,by decide +kernel,by decide +kernel⟩
  have sep : ∀ M∈X, M.card=2 ∧ M∉L ∧ ∀ T∈L, ¬M⊆T := by
    intro M hm; simp only [X,Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with rfl | rfl <;> refine ⟨by decide +kernel,by decide +kernel,?_⟩ <;>
      intro T ht <;> simp only [L,Finset.mem_insert,Finset.mem_singleton] at ht <;> rcases ht with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  have u := full_cost h hc hz P I (by decide +kernel) hsub L X (by decide +kernel)
    tri distinct hits sep (by decide +kernel)
  have c : P.card=7 ∧ I.card=7 ∧ L.card=5 ∧ X.card=2 := by decide +kernel
  have ec := inelig_card_add 14 D
  rw [←sub] at ec
  change I.card + _ = _ at ec
  omega

set_option maxHeartbeats 0 in
theorem side16256 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (hz : Bzero 14 D=0) (sub : mask 16256 = ineligSet 14 D) : 12≤Bplus 14 D := by
  let P := mask 127
  let I := mask 16256
  let L : Finset (Finset V) := {mask 69,mask 49,mask 88,mask 44,mask 22}
  let X : Finset (Finset V) := {mask 10,mask 96}
  have hsub : I ⊆ ineligSet 14 D := sub ▸ Finset.Subset.rfl
  have tri : ∀ T∈L, T.card=3 := by
    intro T ht; simp only [L,Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  have distinct : ∀ T∈L, ∀ U∈L, T≠U → (T∩U).card≤1 := by
    intro T ht U hu
    simp only [L,Finset.mem_insert,Finset.mem_singleton] at ht hu
    rcases ht with rfl | rfl | rfl | rfl | rfl <;> rcases hu with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  have hits : ∀ M∈L∪X, ∃ i∈I, projected P i=M := by
    intro M hm; simp only [L,X,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with (rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)
    · exact ⟨8,by decide +kernel,by decide +kernel⟩
    · exact ⟨10,by decide +kernel,by decide +kernel⟩
    · exact ⟨11,by decide +kernel,by decide +kernel⟩
    · exact ⟨12,by decide +kernel,by decide +kernel⟩
    · exact ⟨13,by decide +kernel,by decide +kernel⟩
    · exact ⟨7,by decide +kernel,by decide +kernel⟩
    · exact ⟨9,by decide +kernel,by decide +kernel⟩
  have sep : ∀ M∈X, M.card=2 ∧ M∉L ∧ ∀ T∈L, ¬M⊆T := by
    intro M hm; simp only [X,Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with rfl | rfl <;> refine ⟨by decide +kernel,by decide +kernel,?_⟩ <;>
      intro T ht <;> simp only [L,Finset.mem_insert,Finset.mem_singleton] at ht <;> rcases ht with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  have u := full_cost h hc hz P I (by decide +kernel) hsub L X (by decide +kernel)
    tri distinct hits sep (by decide +kernel)
  have c : P.card=7 ∧ I.card=7 ∧ L.card=5 ∧ X.card=2 := by decide +kernel
  have ec := inelig_card_add 14 D
  rw [←sub] at ec
  change I.card + _ = _ at ec
  omega

open PEqualNP.Outside.L_meta_9774_aux.DagTools

def wide (P : Finset V) := Finset.univ.filter fun i : V => (projected P i).card = 3

def labels (P O : Finset V) := (Finset.univ \ O).biUnion (projected P)

theorem proj_mem (P : Finset V) (i a : V) : a∈projected P i ↔ a∈P ∧ adj i a := Finset.mem_filter

theorem proj_le (P : Finset V) (i : V) : (projected P i).card≤3 := by
  have deg : ∀ j : V, (projected Finset.univ j).card≤3 := by decide +kernel
  exact le_trans (Finset.card_le_card (fun a ha => (proj_mem _ _ a).2 ⟨Finset.mem_univ _,((proj_mem _ _ a).1 ha).2⟩)) (deg i)

theorem proj_meet (P : Finset V) {i j : V} (ne : i≠j) : (projected P i ∩ projected P j).card≤1 := by
  have ff : ∀ i j : V, i≠j → (projected Finset.univ i ∩ projected Finset.univ j).card≤1 := by decide +kernel
  apply le_trans (Finset.card_le_card _) (ff _ _ ne)
  intro a ha
  rcases Finset.mem_inter.mp ha with ⟨ai,aj⟩
  exact Finset.mem_inter.mpr ⟨(proj_mem _ _ _).2 ⟨Finset.mem_univ _,((proj_mem _ _ _).1 ai).2⟩,
    (proj_mem _ _ _).2 ⟨Finset.mem_univ _,((proj_mem _ _ _).1 aj).2⟩⟩

noncomputable def marks (D : Dag) (P : Finset V) : Finset V := by
  classical
  exact (wide P).filter (fun i => sup_Occ 14 D P (projected P i))

theorem mark_iff {D : Dag} {P : Finset V} {i : V} : i∈marks D P ↔ (projected P i).card=3 ∧ sup_Occ 14 D P (projected P i) := by
  classical
  simp [marks,wide]

theorem projected_count {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (P : Finset V)
    (hind : independent P) (p7 : P.card ≤ 7) :
    2*(marks D P).card + (ineligSet 14 D ∩ wide P).card + (labels P (marks D P)).card + (eligSet 14 D).card ≤
    P.card + (P ∩ eligSet 14 D).card + Bplus 14 D := by
  classical
  let O := marks D P
  let W := ineligSet 14 D ∩ wide P
  obtain ⟨b,hb⟩ := sem_exists_pureBranch graph_ok h.1 hc
  obtain ⟨E,ne,he⟩ := sup_assigned_exits graph_ok h hc P W (fun i hi => by
    rcases Finset.mem_inter.mp hi with ⟨hin,wi⟩
    have three : (projected P i).card=3 := by simpa [wide] using wi
    exact ⟨hin,projected P i,Finset.filter_subset _ _,by omega,fun a ha => ((proj_mem _ _ a).1 ha).2⟩)
  have each : ∀ f ∈ labels P O, ∃ c, c∉O ∧ f∈projected P c := by
    intro f hf; obtain ⟨c,hc,hf⟩ := Finset.mem_biUnion.mp hf
    exact ⟨c,(Finset.mem_sdiff.mp hc).2,hf⟩
  choose! c chooseC using each
  have src (f) (hf : f∈labels P O) : ∃ e, sup_Wit 14 D P (projected P (c f)) f e := by
    let v := c f
    let U := projected P v
    have inside : U⊆P := Finset.filter_subset _ _
    have cov : U.card≤2 ∨ U.card=3 ∧ ¬sup_Occ 14 D P U := by
      have small := proj_le P v
      by_cases t : U.card=3
      · exact Or.inr ⟨t,fun occ => (chooseC _ hf).1 (mark_iff.2 ⟨t,occ⟩)⟩
      · change U.card≤3 at small
        exact Or.inl (by omega)
    let X := insert v (P \ U)
    refine sup_wit_exists graph_ok h.1 hc (X:=X) inside cov ?_ (fun a ha => Finset.mem_insert_of_mem ha)
      (chooseC _ hf).2 ⟨v,Finset.mem_insert_self _ _,graph_ok.1 _ _ ((proj_mem _ _ _).1 (chooseC _ hf).2).2⟩
    have no (a) (ha : a ∈ P \ U) : ¬adj v a := fun ev => (Finset.mem_sdiff.mp ha).2 ((proj_mem P v a).2 ⟨(Finset.mem_sdiff.mp ha).1,ev⟩)
    intro i hi j hj
    rcases Finset.mem_insert.mp hi with rfl|hi <;> rcases Finset.mem_insert.mp hj with rfl|hj
    · exact graph_ok.2.1 _
    · exact no _ hj
    · exact fun a => no _ hi (graph_ok.1 _ _ a)
    · exact hind _ (Finset.mem_sdiff.mp hi).1 _ (Finset.mem_sdiff.mp hj).1
  have main := cnt_main h.1 p7 (O.image (projected P)) (fun T ht => by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ht; exact mark_iff.mp hi)
    (fun T ht U hu neq => by
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hu
      exact proj_meet P (fun e => neq (congrArg (projected P) e)))
    E he (labels P O) (fun f => projected P (c f)) src (fun f hf T ht => by
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ht
      exact proj_meet P (fun eq => (chooseC _ hf).1 (eq ▸ hi)))
  have inj : Set.InjOn (projected P) O := by
    intro u hu v hv eq
    by_contra bad
    have small := proj_meet P bad
    rw [eq,Finset.inter_self] at small
    have full := (mark_iff.mp hv).1
    omega
  rw [Finset.card_image_of_injOn inj,ne] at main
  have fl := carrier_flow_union h P (by rw [sem_supp_out graph_ok hc];simp)
  have sup := surplus_carrierT_le h.1 b hb P
  change 2*O.card+W.card+(labels P O).card+(eligSet 14 D).card ≤ P.card+(P ∩ eligSet 14 D).card+Bplus 14 D
  omega

open PEqualNP.Outside.L_meta_9774_aux.DagTools

def weights : List (Nat × Nat) := [(5, 1), (4608, 1), (18, 1), (2176, 1), (97, 2), (1792, 2), (14, 2), (12416, 2), (40, 1), (9216, 1), (21, 2), (65, 1), (6400, 2), (68, 1), (3584, 2), (768, 1), (27, 3), (116, 3), (10624, 3), (4224, 1), (33, 1), (14848, 3), (6, 1), (2688, 2), (4992, 3), (10240, 1), (20, 1), (26, 2), (39, 3), (1536, 1), (5120, 1), (19, 2), (17, 1), (48, 1), (72, 1), (2304, 1), (7424, 3), (8448, 1), (7, 2), (37, 2), (56, 2), (73, 2), (78, 3), (2560, 1), (3200, 2), (3712, 3), (4736, 2), (4864, 2), (9472, 2), (13440, 3), (29, 3), (38, 2), (58, 3), (76, 2), (81, 2), (82, 2), (83, 3), (6144, 1), (6656, 2), (8960, 2), (9728, 2), (10368, 2), (41, 2), (80, 1), (104, 2), (36, 1), (24, 1), (12, 1), (3072, 1), (4352, 1), (4480, 2), (7168, 2), (12288, 1), (13, 2), (15, 3), (25, 2), (28, 2), (50, 2), (52, 2), (53, 3), (70, 2), (84, 2), (85, 3), (100, 2), (112, 2), (786, 2), (792, 2), (1542, 2), (1548, 2), (2181, 2), (2209, 2), (2212, 2), (2432, 2), (2565, 2), (2566, 2), (3078, 2), (3328, 2), (4241, 2), (4289, 2), (4304, 2), (4370, 2), (4625, 2), (4626, 2), (5248, 2), (5376, 2), (6912, 3), (7680, 3), (8488, 2), (9288, 2), (10273, 2), (10496, 2), (10752, 2), (10880, 3), (12353, 2), (12800, 2), (12928, 3), (13312, 2), (14336, 2)]

def clean (m : Nat) : Bool := edges.all (fun e => !(m.testBit e.1 && m.testBit e.2))

def possible (cap m : Nat) : Bool :=
  clean m && (let c := (mask m).card
              decide (14 ≤ c+cap) && weights.all (fun r =>
                (r.1 &&& m != r.1) || decide (14+r.2 ≤ c+cap)))

def sevenMasks : List Nat := [127,523,1290,8416,8713,8833,16256]

def claim (m : Nat) : Bool := !possible 9 m && (!possible 10 m || sevenMasks.contains m)

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem repr (I : Finset V) : ∃ m : Fin 16384, mask m.val = I := by
  let bs := List.ofFn (fun i : V => decide (i∈I))
  let B := BitVec.ofBoolListLE bs
  have hl : bs.length=14 := List.length_ofFn
  have lt : B.toNat < 16384 := by have h := B.isLt; change _ < 2 ^ bs.length at h; simpa [hl] using h
  refine ⟨⟨B.toNat,lt⟩,?_⟩
  ext i
  simp only [mask,Finset.mem_filter,Finset.mem_univ,true_and]
  change B.getLsbD i.val = true ↔ i∈I
  rw [BitVec.getLsbD_ofBoolListLE]
  have g := input_bit (fun i : V => decide (i∈I)) i
  simp only [bs,g,decide_eq_true_eq]

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem mask_sub (k m : Nat) (e : k &&& m = k) : mask k ⊆ mask m := by
  intro v hv
  simp only [mask,Finset.mem_filter,Finset.mem_univ,true_and] at *
  have h := congrArg (fun z : Nat => z.testBit v.val) e
  change (k &&& m).testBit v.val = k.testBit v.val at h
  simpa only [Nat.testBit_and,hv,Bool.true_and] using h

def survivingMasks : List Nat := [11, 63, 95, 98, 107, 109, 111, 119, 121, 123, 125, 126, 127, 177, 197, 224, 229, 241, 245, 266, 290, 298, 400, 416, 432, 515, 521, 522, 523, 534, 535, 542, 543, 641, 644, 645, 656, 657, 660, 661, 778, 794, 912, 1034, 1090, 1098, 1156, 1216, 1220, 1282, 1288, 1290, 1408, 1546, 1550, 1668, 1802, 2051, 2082, 2083, 2213, 2338, 2563, 2567, 2693, 2818, 3590, 3842, 4099, 4162, 4163, 4305, 4611, 4627, 4753, 4882, 5186, 5634, 5890, 6147, 6273, 6659, 6785, 7938, 8064, 8201, 8288, 8297, 8321, 8352, 8353, 8384, 8385, 8416, 8417, 8608, 8705, 8712, 8713, 8832, 8833, 9408, 9992, 10112, 10401, 12032, 12160, 12481, 14080, 14208, 14465, 14977, 15232, 15744, 16000, 16128, 16256]
def survivorTest (m : Nat) := !(possible 11 m) || survivingMasks.contains m
theorem possible_mono (a b m : Nat) (h : a ≤ b) (ok : possible a m = true) :
    possible b m = true := by
  simp only [possible, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at ok ⊢
  obtain ⟨ec, bound, rest⟩ := ok
  refine ⟨ec, by omega, ?_⟩
  intro r hr
  have hrow := rest r hr
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hrow ⊢
  exact hrow.imp_right (by omega)
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem survivorChunk0 : ∀ j : Fin 1024, survivorTest (0+j.val)=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem survivorChunk1 : ∀ j : Fin 1024, survivorTest (1024+j.val)=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem survivorChunk2 : ∀ j : Fin 1024, survivorTest (2048+j.val)=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem survivorChunk3 : ∀ j : Fin 1024, survivorTest (3072+j.val)=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem survivorChunk4 : ∀ j : Fin 1024, survivorTest (4096+j.val)=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem survivorChunk5 : ∀ j : Fin 1024, survivorTest (5120+j.val)=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem survivorChunk6 : ∀ j : Fin 1024, survivorTest (6144+j.val)=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem survivorChunk7 : ∀ j : Fin 1024, survivorTest (7168+j.val)=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem survivorChunk8 : ∀ j : Fin 1024, survivorTest (8192+j.val)=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem survivorChunk9 : ∀ j : Fin 1024, survivorTest (9216+j.val)=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem survivorChunk10 : ∀ j : Fin 1024, survivorTest (10240+j.val)=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem survivorChunk11 : ∀ j : Fin 1024, survivorTest (11264+j.val)=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem survivorChunk12 : ∀ j : Fin 1024, survivorTest (12288+j.val)=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem survivorChunk13 : ∀ j : Fin 1024, survivorTest (13312+j.val)=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem survivorChunk14 : ∀ j : Fin 1024, survivorTest (14336+j.val)=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem survivorChunk15 : ∀ j : Fin 1024, survivorTest (15360+j.val)=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem all_survivors (m : Fin 16384) : survivorTest m.val = true := by
  let j : Fin 1024 := ⟨m.val % 1024, Nat.mod_lt _ (by decide)⟩
  have hj : j.val=m.val % 1024 := rfl
  by_cases q0 : m.val/1024=0
  · have eq : m.val=0+j.val := by omega
    rw [eq]; exact survivorChunk0 j
  by_cases q1 : m.val/1024=1
  · have eq : m.val=1024+j.val := by omega
    rw [eq]; exact survivorChunk1 j
  by_cases q2 : m.val/1024=2
  · have eq : m.val=2048+j.val := by omega
    rw [eq]; exact survivorChunk2 j
  by_cases q3 : m.val/1024=3
  · have eq : m.val=3072+j.val := by omega
    rw [eq]; exact survivorChunk3 j
  by_cases q4 : m.val/1024=4
  · have eq : m.val=4096+j.val := by omega
    rw [eq]; exact survivorChunk4 j
  by_cases q5 : m.val/1024=5
  · have eq : m.val=5120+j.val := by omega
    rw [eq]; exact survivorChunk5 j
  by_cases q6 : m.val/1024=6
  · have eq : m.val=6144+j.val := by omega
    rw [eq]; exact survivorChunk6 j
  by_cases q7 : m.val/1024=7
  · have eq : m.val=7168+j.val := by omega
    rw [eq]; exact survivorChunk7 j
  by_cases q8 : m.val/1024=8
  · have eq : m.val=8192+j.val := by omega
    rw [eq]; exact survivorChunk8 j
  by_cases q9 : m.val/1024=9
  · have eq : m.val=9216+j.val := by omega
    rw [eq]; exact survivorChunk9 j
  by_cases q10 : m.val/1024=10
  · have eq : m.val=10240+j.val := by omega
    rw [eq]; exact survivorChunk10 j
  by_cases q11 : m.val/1024=11
  · have eq : m.val=11264+j.val := by omega
    rw [eq]; exact survivorChunk11 j
  by_cases q12 : m.val/1024=12
  · have eq : m.val=12288+j.val := by omega
    rw [eq]; exact survivorChunk12 j
  by_cases q13 : m.val/1024=13
  · have eq : m.val=13312+j.val := by omega
    rw [eq]; exact survivorChunk13 j
  by_cases q14 : m.val/1024=14
  · have eq : m.val=14336+j.val := by omega
    rw [eq]; exact survivorChunk14 j
  by_cases q15 : m.val/1024=15
  · have eq : m.val=15360+j.val := by omega
    rw [eq]; exact survivorChunk15 j
  omega

-- Independent vertex sets give lower bounds on the number of repeated wire uses.
open PEqualNP.Outside.L_meta_9774_aux.DagTools

abbrev WeightSpec := Nat × Nat × Nat × Nat × Nat × Nat × Nat

def weightSpecs : List WeightSpec := [
(5,256,5,1,0,0x0,0x14420000000000000000000000000000),
(4608,32,4608,1,0,0x0,0x113800000000000000000),
(18,8192,18,1,0,0x0,0x1310000000000000000000000000000000000000000000000),
(2176,8,2176,1,0,0x0,0x414c0000000000),
(97,1280,97,2,1,0xa800,0x31a000060e0000000000000000000000000000),
(1792,96,1792,2,1,0x6509,0x827414c00000000000000000),
(14,12288,14,2,1,0xdc02,0x43460e1000000000000000000000000000000000000000000),
(12416,12,12416,2,1,0x320c,0x209c13a0000000),
(40,4096,40,1,0,0x0,0x295000000000000000000000000000000000000000000),
(9216,16,9216,1,0,0x0,0x82700000000000000),
(21,1280,21,2,1,0xa800,0x92200014420000000000000000000000000000),
(65,256,65,1,0,0x0,0x60e0000000000000000000000000000),
(6400,12,6400,2,1,0x320c,0x3d60690000000),
(68,256,68,1,0,0x0,0x12130000000000000000000000000000),
(3584,48,3584,2,1,0x540a,0x414e06900000000000000),
(768,64,768,1,0,0x0,0x827000000000000000000000),
(27,11264,27,3,2,0xdba44,0x3a10000d3029a000000000000000000000000000000000000),
(116,11264,116,3,2,0xdba44,0x7c080009c23a8100000000000000000000000000000000000),
(10624,88,10624,3,2,0x643bb,0x21f000044e414c0000000000),
(4224,8,4224,1,0,0x0,0x209c0000000000),
(33,1024,33,1,0,0x0,0x31a00000000000000000000000000000000000),
(14848,44,14848,3,2,0x532cc,0x113800003d413a0000000),
(6,8192,6,1,0,0x0,0x6c0000000000000000000000000000000000000000000000),
(2688,72,2688,2,1,0x630b,0x13a0000000414c0000000000),
(4992,44,4992,3,2,0x532cc,0x1138000209e0690000000),
(10240,16,10240,1,0,0x0,0x44e00000000000000),
(20,8192,20,1,0,0x0,0x1c28000000000000000000000000000000000000000000000),
(26,10240,26,2,1,0xdb04,0x2294000838400000000000000000000000000000000000000),
(39,12544,39,3,2,0xdc822,0x4e42708000000000034c00000000000000000000000000000),
(1536,32,1536,1,0,0x0,0x414c00000000000000000),
(5120,32,5120,1,0,0x0,0x87c00000000000000000),
(19,9216,19,2,1,0xda04,0x1310000000212800000000000000000000000000000000000),
(17,1024,17,1,0,0x0,0x92200000000000000000000000000000000000),
(48,1024,48,1,0,0x0,0xa0700000000000000000000000000000000000),
(72,2048,72,1,0,0x0,0x6c000000000000000000000000000000000000000),
(2304,64,2304,1,0,0x0,0x21f000000000000000000000),
(7424,44,7424,3,2,0x532cc,0x87c00003d60690000000),
(8448,4,8448,1,0,0x0,0x10530000000),
(7,8448,7,2,1,0xd802,0x6c0000000000000024480000000000000000000000000000),
(37,1280,37,2,1,0xa800,0x31a00014420000000000000000000000000000),
(56,3072,56,2,1,0xba04,0x1310a0700000000000000000000000000000000000),
(73,2304,73,2,1,0xb806,0x6c00000000e060000000000000000000000000000),
(78,12544,78,3,2,0xdc822,0x4e429a000000000003a810000000000000000000000000000),
(2560,64,2560,1,0,0x0,0x13a000000000000000000000),
(3200,24,3200,2,1,0x430b,0x2069414c0000000000),
(3712,88,3712,3,2,0x643bb,0x13a0002069414c0000000000),
(4736,40,4736,2,1,0x530c,0x1138000209c0000000000),
(4864,36,4864,2,1,0x520c,0x113800000020690000000),
(9472,20,9472,2,1,0x420d,0x82700010530000000),
(13440,44,13440,3,2,0x532cc,0x87c000209c13a0000000),
(29,11264,29,3,2,0xdba44,0x7c08000d3029a000000000000000000000000000000000000),
(38,12288,38,2,1,0xdc02,0x4346209000000000000000000000000000000000000000000),
(58,11264,58,3,2,0xdba44,0x3a10000d303a8100000000000000000000000000000000000),
(76,2304,76,2,1,0xb806,0x6c00000001a030000000000000000000000000000),
(81,1280,81,2,1,0xa800,0x922000060e0000000000000000000000000000),
(82,10240,82,2,1,0xdb04,0x229400084a000000000000000000000000000000000000000),
(83,11264,83,3,2,0xdba44,0x3a100009c229a000000000000000000000000000000000000),
(6144,8,6144,1,0,0x0,0x3d40000000000),
(6656,40,6656,2,1,0x530c,0x113800003d40000000000),
(8960,68,8960,2,1,0x6208,0x827000000000010530000000),
(9728,48,9728,2,1,0x540a,0x414c82700000000000000),
(10368,24,10368,2,1,0x430b,0x44e414c0000000000),
(41,5120,41,2,1,0xca05,0x4c4000131200000000000000000000000000000000000),
(80,2048,80,1,0,0x0,0x183800000000000000000000000000000000000000),
(104,6144,104,2,1,0xcb03,0xa07484c00000000000000000000000000000000000000),
(36,4096,36,1,0,0x0,0x31a000000000000000000000000000000000000000000),
(24,2048,24,1,0,0x0,0x131000000000000000000000000000000000000000),
(12,4096,12,1,0,0x0,0x1b0000000000000000000000000000000000000000000),
(3072,16,3072,1,0,0x0,0x206900000000000000),
(4352,4,4352,1,0,0x0,0x20690000000),
(4480,12,4480,2,1,0x320c,0x209e0690000000),
(7168,24,7168,2,1,0x430b,0x206903d40000000000),
(12288,4,12288,1,0,0x0,0x13a0000000),
(13,4352,13,2,1,0xc802,0x1b0000000000014420000000000000000000000000000),
(15,12544,15,3,2,0xdc822,0x4e429a0000000000034c00000000000000000000000000000),
(25,3072,25,2,1,0xba04,0x131092200000000000000000000000000000000000),
(28,6144,28,2,1,0xcb03,0x922510800000000000000000000000000000000000000),
(50,9216,50,2,1,0xda04,0x1310000000220900000000000000000000000000000000000),
(52,5120,52,2,1,0xca05,0x70a0001a0300000000000000000000000000000000000),
(53,12544,53,3,2,0xdc822,0x7c0a708000000000034c00000000000000000000000000000),
(70,8448,70,2,1,0xd802,0x6c0000000000000022090000000000000000000000000000),
(84,2304,84,2,1,0xb806,0x1c280000001a030000000000000000000000000000),
(85,11264,85,3,2,0xdba44,0x7c080009c229a000000000000000000000000000000000000),
(100,4352,100,2,1,0xc802,0x31a000000000012130000000000000000000000000000),
(112,3072,112,2,1,0xba04,0x1838a0700000000000000000000000000000000000),
(786,8256,786,2,0,0x0,0x13100000000000000000000028a1000000000000000000000),
(792,2112,792,2,0,0x0,0x131000000000000000827000000000000000000000),
(1542,8224,1542,2,0,0x0,0x6c0000000000000000000000000c30400000000000000000),
(1548,4128,1548,2,0,0x0,0x1b0000000000000000000000414c00000000000000000),
(2181,264,2181,2,0,0x0,0x2448000000000000004c480000000000),
(2209,1032,2209,2,0,0x0,0x31a00000000000000000000051080000000000),
(2212,4104,2212,2,0,0x0,0x31a0000000000000000000000000000414c0000000000),
(2432,72,2432,2,1,0x630b,0x21f0000000414c0000000000),
(2565,320,2565,2,0,0x0,0x1442000013a000000000000000000000),
(2566,8256,2566,2,0,0x0,0x4344000000000000000000002128000000000000000000000),
(3078,8208,3078,2,0,0x0,0x6c0000000000000000000000000000206900000000000000),
(3328,80,3328,2,1,0x640b,0x21f000206900000000000000),
(4241,1032,4241,2,0,0x0,0x212800000000000000000000038180000000000),
(4289,264,4289,2,0,0x0,0x60e0000000000000024880000000000),
(4304,2056,4304,2,0,0x0,0x1838000000000000000000000000209c0000000000),
(4370,8196,4370,2,0,0x0,0x1310000000000000000000000000000000000020690000000),
(4625,1056,4625,2,0,0x0,0x92200000000000000113800000000000000000),
(4626,8224,4626,2,0,0x0,0x2294000000000000000000000000912000000000000000000),
(5248,40,5248,2,1,0x530c,0x87c000209c0000000000),
(5376,36,5376,2,1,0x520c,0x87c00000020690000000),
(6912,44,6912,3,2,0x532cc,0x113800003d60690000000),
(7680,88,7680,3,2,0x643bb,0x13a000206903d40000000000),
(8488,4100,8488,2,0,0x0,0x295000000000000000000000000000000010530000000),
(9288,2064,9288,2,0,0x0,0x6c000000000000000000000082700000000000000),
(10273,1040,10273,2,0,0x0,0x31a00000000000000000044e00000000000000),
(10496,20,10496,2,1,0x420d,0x44e00010530000000),
(10752,80,10752,2,1,0x640b,0x13a000044e00000000000000),
(10880,88,10880,3,2,0x643bb,0x13a000044e414c0000000000),
(12353,260,12353,2,0,0x0,0x60e00000000000000000013a0000000),
(12800,36,12800,2,1,0x520c,0x1138000000013a0000000),
(12928,44,12928,3,2,0x532cc,0x1138000209c13a0000000),
(13312,20,13312,2,1,0x420d,0x827000013a0000000),
(14336,12,14336,2,1,0x320c,0x3d413a0000000)]

def weightKey (r : WeightSpec) := (r.1,r.2.2.2.1)

def weightWitness (a : Nat) (v : V) := mask ((a >>> (14*v.val)) &&& 16383)

def point (p j : Nat) : V := Fin.ofNat 14 ((p >>> (4*j)) &&& 15)

def weightGeometry (K T : Finset V) (m p : Nat) : Prop :=
  let i := point p 0
  let j := point p 1
  let x := point p 2
  let y := point p 3
  let z := point p 4
  m=0 ∨ (m=1 ∧ i∈K ∧ adj i x ∧ adj i y ∧ x∈T ∧ y∈T ∧ x≠y) ∨
    (m=2 ∧ i∈K ∧ j∈K ∧ adj i x ∧ adj i y ∧ adj j x ∧ adj j z ∧ T.card=3 ∧ x∈T ∧ y∈T ∧ z∈T ∧ x≠y ∧ x≠z ∧ y≠z)

instance (K T : Finset V) (m p : Nat) : Decidable (weightGeometry K T m p) := by unfold weightGeometry; infer_instance

def weightValid (r : WeightSpec) :=
  let (K,T,J,k,m,p,a) := r
  decide (ValidPrivate (mask T) (mask J) (weightWitness a) ∧ mask J ⊆ mask K ∧ k+(mask T).card ≤ (mask J).card+m ∧ weightGeometry (mask K) (mask T) m p)

theorem geometricCost {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (K T : Finset V)
    (m p : Nat) (geom : weightGeometry K T m p) (sub : K⊆ineligSet 14 D) : m≤cost D T := by
  rcases geom with rfl|⟨rfl,i,rest⟩|⟨rfl,i,j,rest⟩
  · exact Nat.zero_le _
  · exact cost_one h hc T (point p 0) (point p 2) (point p 3) (sub i) rest
  · exact cost_two h hc T (point p 0) (point p 1) (point p 2) (point p 3) (point p 4) (sub i) (sub j) rest

theorem compact_weight {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (r : WeightSpec)
    (ok : weightValid r=true) (sub : mask (weightKey r).1 ⊆ ineligSet 14 D) :
    (eligSet 14 D).card+(weightKey r).2 ≤ Bplus 14 D := by
  rcases r with ⟨K,T,J,k,m,p,a⟩
  obtain ⟨valid,small,size,geom⟩ := of_decide_eq_true ok
  exact bound_rule h hc (mask T) (mask J) (weightWitness a) valid (small.trans sub) m k
    (geometricCost h hc (mask K) (mask T) m p geom sub) size

theorem weightRows : weightSpecs.all weightValid=true := by decide +kernel

theorem weightNames : weightSpecs.map weightKey=weights := by decide +kernel

theorem checked_weights {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) :
    ∀ r∈weights, mask r.1 ⊆ ineligSet 14 D → (eligSet 14 D).card+r.2 ≤ Bplus 14 D := by
  intro r hr sub
  rw [←weightNames] at hr
  obtain ⟨w,mem,rfl⟩ := List.mem_map.mp hr
  exact compact_weight h hc w (List.all_eq_true.mp weightRows _ mem) sub

theorem possible_of {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (cap m : Nat) (enc : mask m = ineligSet 14 D) (lim : Bplus 14 D ≤ cap) : possible cap m = true := by
  have p := inelig_card_add 14 D
  rw [←enc] at p
  obtain ⟨b,hb⟩ := sem_exists_pureBranch graph_ok h.1 hc
  have pc := elig_le_Bplus h.1 b hb
  have cleanM : clean m = true := by
    rw [clean,List.all_eq_true]
    rintro ⟨u,v⟩ e
    have bounds : ∀ q ∈ edges, q.1<14 ∧ q.2<14 := by decide +kernel
    obtain ⟨hu,hv⟩ := bounds (u,v) e
    have a := sem_elig_cover graph_ok h hc ((graph_edges ⟨u,hu⟩ ⟨v,hv⟩).2 (Or.inl e))
    by_contra! fail
    have both : m.testBit u=true ∧ m.testBit v=true := by simpa using fail
    have add (x : V) (hx : m.testBit x.val=true) : x ∉ eligSet 14 D := by
      apply sem_mem_inelig.mp
      rw [←enc]; simpa [mask] using hx
    exact a.elim (add _ both.1) (add _ both.2)
  simp only [possible,cleanM,Bool.true_and,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true]
  refine ⟨by omega,?_⟩
  intro r hr
  by_cases eq : r.1 &&& m = r.1
  · have sub : mask r.1 ⊆ ineligSet 14 D := enc ▸ mask_sub _ _ eq
    have w := checked_weights h hc r hr sub
    have enough : 14+r.2 ≤ (mask m).card+cap := by omega
    simp [eq,enough]
  · simp [eq]

open PEqualNP.Outside.L_meta_9774_aux.DagTools

abbrev EdgeIdx := Fin 19

abbrev Slot := ℕ × Bool

def endpoint (s : Bool) (e : EdgeIdx) : V :=
  let ab := edges.getD e.val (0,0)
  Fin.ofNat 14 (if s then ab.2 else ab.1)

def flip (s : Bool) (e : Slot) := if s then sem_bar e else e

theorem flip_inj (s : Bool) : Function.Injective (flip s) := by
  intro a b
  cases s with
  | false => exact id
  | true =>
    intro eq
    have h := congrArg sem_bar eq
    simpa only [flip,if_true,sem_bar_bar] using h

def AtSlots (D : Dag) (P : EdgeIdx → Slot) :=
  ∀ s e, flip s (P e) ∈ sem_W 14 D (endpoint s e)

theorem get_slots {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) : ∃ P, AtSlots D P := by
  have adjE : ∀ e : EdgeIdx, adj (endpoint false e) (endpoint true e) := by decide +kernel
  have both (e : EdgeIdx) : ∃ p : Slot,
      p∈sem_W 14 D (endpoint false e) ∧ sem_bar p∈sem_W 14 D (endpoint true e) := by
    obtain ⟨p,hl,hr,_⟩ := sem_edge_slots graph_ok h.1 hc (adjE e)
    exact ⟨p,hl,hr⟩
  choose P hp using both
  exact ⟨P,fun s e => by cases s; exact (hp e).1; exact (hp e).2⟩

theorem at_most_two {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (tight : Bplus 14 D ≤ (eligSet 14 D).card) : ∀ x, (sem_W 14 D x).card≤2 := by
  obtain ⟨b,hb⟩ := sem_exists_pureBranch graph_ok h.1 hc
  have zero : residualUnits 14 D b = ∅ := by
    have := card_residual h.1 b hb
    exact Finset.card_eq_zero.mp (by omega)
  intro x
  have count := sem_code_count graph_ok h hc b hb x
  have one := Finset.card_le_card (Finset.inter_subset_left : ({x} : Finset V) ∩ eligSet 14 D ⊆ {x})
  rw [zero] at count
  simp only [Finset.filter_empty,Finset.card_empty,Finset.card_singleton] at count one
  omega

theorem all_equal {D : Dag} {P} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (hp : AtSlots D P)
    (s : Bool) (a b : EdgeIdx) (same : endpoint s a=endpoint s b)
    (hi : endpoint s a ∈ ineligSet 14 D) : P a=P b := by
  obtain ⟨e,_,_,_,_,_,hw,_⟩ := sem_inelig_consumer graph_ok h hc hi
  change sem_W 14 D (endpoint s a)={e} at hw
  have ha := hp s a
  have hb := hp s b
  rw [←same] at hb
  exact flip_inj s ((Finset.mem_singleton.mp (hw ▸ ha)).trans (Finset.mem_singleton.mp (hw ▸ hb)).symm)

theorem pure_slot {D : Dag} {P} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (hp : AtSlots D P)
    (s : Bool) (a b : EdgeIdx) (diff : endpoint s a≠endpoint s b)
    (hi : endpoint s a∈ineligSet 14 D) : P a≠P b := by
  intro eq
  have ha := (sem_mem_W.mp (hp s a)).2.1
  have hb := (sem_mem_W.mp (hp s b)).2.1
  rw [←eq] at hb
  rw [sem_inelig_pure graph_ok h.1 hc hi ha,Finset.mem_singleton] at hb
  exact diff hb.symm

theorem couple {D : Dag} {P} (hp : AtSlots D P) (lim : ∀ x, (sem_W 14 D x).card≤2)
    (s : Bool) (a b c : EdgeIdx) (same : endpoint s a=endpoint s b ∧ endpoint s a=endpoint s c) :
    P a=P b ∨ P b=P c ∨ P a=P c := by
  by_contra! ne
  have hb := hp s b
  have hc := hp s c
  rw [←same.1] at hb
  rw [←same.2] at hc
  have card := Finset.two_lt_card.mpr ⟨_,hp s a,_,hb,_,hc,fun e => ne.1 (flip_inj s e),
    fun e => ne.2.2 (flip_inj s e),fun e => ne.2.1 (flip_inj s e)⟩
  exact (Nat.not_lt_of_ge (lim _)) card

theorem exposure {D : Dag} {P} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (hp : AtSlots D P)
    (lim : ∀ x, (sem_W 14 D x).card≤2) (s : Bool) (a b i j : EdgeIdx) (q : V)
    (geom : endpoint s a=endpoint s b ∧ ¬adj (endpoint s i) (endpoint s j) ∧
      adj (endpoint s a) q ∧ ¬adj q (endpoint s i) ∧ ¬adj q (endpoint s j)) :
    P a=P b ∨ P a≠P i ∨ P b≠P j := by
  by_contra! bad
  obtain ⟨sw,na,hq,ni,nj⟩ := geom
  obtain ⟨e,he,no1,no2⟩ := sem_cover_free graph_ok h.1 hc na hq ni nj
  have mb := hp s b
  rw [←sw] at mb
  have yi := (sem_mem_W.mp (hp s i)).2.1
  have yj := (sem_mem_W.mp (hp s j)).2.1
  rw [←bad.2.1] at yi
  rw [←bad.2.2] at yj
  have ne1 : flip s (P a)≠e := fun eq => no1 (eq ▸ yi)
  have ne2 : flip s (P b)≠e := fun eq => no2 (eq ▸ yj)
  have card := Finset.two_lt_card.mpr ⟨_,hp s a,_,mb,e,he,fun eq => bad.1 (flip_inj s eq),ne1,ne2⟩
  exact (Nat.not_lt_of_ge (lim _)) card

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_9774_aux.DagTools

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem all_masks_list : survivingMasks.all claim = true := by decide +kernel
theorem all_masks (m : Fin 16384) : claim m.val = true := by
  by_cases ok : possible 11 m.val = true
  · have mem := all_survivors m
    simp only [survivorTest, ok, Bool.not_true, Bool.false_or, List.contains_iff_mem] at mem
    exact List.all_eq_true.mp all_masks_list _ mem
  ·
    have a : possible 9 m.val = false := by
      cases q : possible 9 m.val
      · rfl
      · exact False.elim (ok (possible_mono 9 11 m.val (by decide) q))
    have b : possible 10 m.val = false := by
      cases q : possible 10 m.val
      · rfl
      · exact False.elim (ok (possible_mono 10 11 m.val (by decide) q))
    simp [claim,a,b]


open PEqualNP.Outside.L_meta_9774_aux.DagTools

set_option maxHeartbeats 0 in
theorem noTwo1 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (w2 : ∀ x, (sem_W 14 D x).card≤2) (sub : mask 1 ⊆ ineligSet 14 D) : False := by
  obtain ⟨P,hp⟩ := get_slots h hc
  have c3 := all_equal h hc hp false 0 1 (by decide +kernel) (sub (by decide +kernel : endpoint false 0 ∈ mask 1))
  have c4 := pure_slot h hc hp false 0 4 (by decide +kernel) (sub (by decide +kernel : endpoint false 0 ∈ mask 1))
  have c5 := pure_slot h hc hp false 0 10 (by decide +kernel) (sub (by decide +kernel : endpoint false 0 ∈ mask 1))
  have c6 := pure_slot h hc hp false 0 14 (by decide +kernel) (sub (by decide +kernel : endpoint false 0 ∈ mask 1))
  have c7 := pure_slot h hc hp false 0 16 (by decide +kernel) (sub (by decide +kernel : endpoint false 0 ∈ mask 1))
  have c8 := exposure h hc hp w2 false 10 11 14 8 13 (by decide +kernel)
  have c9 := exposure h hc hp w2 false 16 18 4 8 9 (by decide +kernel)
  have c10 := exposure h hc hp w2 false 16 18 4 11 9 (by decide +kernel)
  have c11 := couple hp w2 true 0 4 16 (by decide +kernel)
  have c12 := exposure h hc hp w2 true 0 4 1 18 2 (by decide +kernel)
  have c13 := couple hp w2 true 1 10 14 (by decide +kernel)
  have c14 := exposure h hc hp w2 true 1 10 0 11 5 (by decide +kernel)
  have c15 := couple hp w2 true 8 11 18 (by decide +kernel)
  grind only

set_option maxHeartbeats 0 in
theorem noTwo2 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (w2 : ∀ x, (sem_W 14 D x).card≤2) (sub : mask 2 ⊆ ineligSet 14 D) : False := by
  obtain ⟨P,hp⟩ := get_slots h hc
  have c2 := all_equal h hc hp false 2 3 (by decide +kernel) (sub (by decide +kernel : endpoint false 2 ∈ mask 2))
  have c3 := pure_slot h hc hp false 2 6 (by decide +kernel) (sub (by decide +kernel : endpoint false 2 ∈ mask 2))
  have c4 := pure_slot h hc hp false 2 12 (by decide +kernel) (sub (by decide +kernel : endpoint false 2 ∈ mask 2))
  have c5 := couple hp w2 false 4 5 6 (by decide +kernel)
  have c6 := exposure h hc hp w2 false 4 6 0 12 12 (by decide +kernel)
  have c7 := exposure h hc hp w2 false 4 6 16 12 12 (by decide +kernel)
  have c8 := exposure h hc hp w2 false 5 6 9 12 8 (by decide +kernel)
  have c9 := exposure h hc hp w2 false 5 6 15 12 8 (by decide +kernel)
  have c10 := exposure h hc hp w2 false 8 9 11 15 7 (by decide +kernel)
  have c11 := exposure h hc hp w2 false 8 9 18 15 7 (by decide +kernel)
  have c12 := exposure h hc hp w2 false 16 18 0 11 9 (by decide +kernel)
  have c13 := couple hp w2 true 0 4 16 (by decide +kernel)
  have c14 := exposure h hc hp w2 true 4 16 5 18 0 (by decide +kernel)
  have c15 := couple hp w2 true 8 11 18 (by decide +kernel)
  have c16 := couple hp w2 true 5 9 15 (by decide +kernel)
  have c17 := exposure h hc hp w2 true 5 9 4 8 5 (by decide +kernel)
  have c18 := couple hp w2 true 3 6 12 (by decide +kernel)
  have c19 := exposure h hc hp w2 true 3 6 2 4 4 (by decide +kernel)
  have c20 := exposure h hc hp w2 true 3 6 2 5 4 (by decide +kernel)
  grind only

set_option maxHeartbeats 0 in
theorem noTwo4 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (w2 : ∀ x, (sem_W 14 D x).card≤2) (sub : mask 4 ⊆ ineligSet 14 D) : False := by
  obtain ⟨P,hp⟩ := get_slots h hc
  have c4 := all_equal h hc hp false 4 5 (by decide +kernel) (sub (by decide +kernel : endpoint false 4 ∈ mask 4))
  have c5 := pure_slot h hc hp false 4 0 (by decide +kernel) (sub (by decide +kernel : endpoint false 4 ∈ mask 4))
  have c6 := pure_slot h hc hp false 4 9 (by decide +kernel) (sub (by decide +kernel : endpoint false 4 ∈ mask 4))
  have c7 := pure_slot h hc hp false 4 15 (by decide +kernel) (sub (by decide +kernel : endpoint false 4 ∈ mask 4))
  have c8 := pure_slot h hc hp false 4 16 (by decide +kernel) (sub (by decide +kernel : endpoint false 4 ∈ mask 4))
  have c9 := exposure h hc hp w2 false 8 9 11 15 7 (by decide +kernel)
  have c10 := couple hp w2 false 16 17 18 (by decide +kernel)
  have c11 := exposure h hc hp w2 false 16 18 0 8 9 (by decide +kernel)
  have c12 := exposure h hc hp w2 false 16 18 0 11 9 (by decide +kernel)
  have c13 := couple hp w2 true 0 4 16 (by decide +kernel)
  have c14 := exposure h hc hp w2 true 0 4 17 5 0 (by decide +kernel)
  have c15 := exposure h hc hp w2 true 0 4 18 5 0 (by decide +kernel)
  have c16 := couple hp w2 true 8 11 18 (by decide +kernel)
  have c17 := exposure h hc hp w2 true 8 18 9 17 4 (by decide +kernel)
  have c18 := couple hp w2 true 5 9 15 (by decide +kernel)
  grind only

set_option maxHeartbeats 0 in
theorem noTwo8 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (w2 : ∀ x, (sem_W 14 D x).card≤2) (sub : mask 8 ⊆ ineligSet 14 D) : False := by
  obtain ⟨P,hp⟩ := get_slots h hc
  have c4 := all_equal h hc hp false 7 8 (by decide +kernel) (sub (by decide +kernel : endpoint false 7 ∈ mask 8))
  have c5 := all_equal h hc hp false 7 9 (by decide +kernel) (sub (by decide +kernel : endpoint false 7 ∈ mask 8))
  have c6 := pure_slot h hc hp false 7 5 (by decide +kernel) (sub (by decide +kernel : endpoint false 7 ∈ mask 8))
  have c7 := pure_slot h hc hp false 7 11 (by decide +kernel) (sub (by decide +kernel : endpoint false 7 ∈ mask 8))
  have c8 := pure_slot h hc hp false 7 15 (by decide +kernel) (sub (by decide +kernel : endpoint false 7 ∈ mask 8))
  have c9 := pure_slot h hc hp false 7 18 (by decide +kernel) (sub (by decide +kernel : endpoint false 7 ∈ mask 8))
  have c10 := couple hp w2 false 10 11 12 (by decide +kernel)
  have c11 := exposure h hc hp w2 false 10 11 1 18 13 (by decide +kernel)
  have c12 := exposure h hc hp w2 false 10 11 14 18 13 (by decide +kernel)
  have c13 := exposure h hc hp w2 false 14 15 1 5 9 (by decide +kernel)
  have c14 := couple hp w2 true 1 10 14 (by decide +kernel)
  have c15 := exposure h hc hp w2 true 10 14 12 15 0 (by decide +kernel)
  have c16 := couple hp w2 true 8 11 18 (by decide +kernel)
  have c17 := exposure h hc hp w2 true 8 11 7 10 6 (by decide +kernel)
  have c18 := exposure h hc hp w2 true 8 11 7 12 6 (by decide +kernel)
  have c19 := couple hp w2 true 5 9 15 (by decide +kernel)
  grind only

set_option maxHeartbeats 0 in
theorem noTwo16 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (w2 : ∀ x, (sem_W 14 D x).card≤2) (sub : mask 16 ⊆ ineligSet 14 D) : False := by
  obtain ⟨P,hp⟩ := get_slots h hc
  have c3 := exposure h hc hp w2 false 8 9 18 5 7 (by decide +kernel)
  have c4 := all_equal h hc hp false 10 11 (by decide +kernel) (sub (by decide +kernel : endpoint false 10 ∈ mask 16))
  have c5 := pure_slot h hc hp false 10 1 (by decide +kernel) (sub (by decide +kernel : endpoint false 10 ∈ mask 16))
  have c6 := pure_slot h hc hp false 10 8 (by decide +kernel) (sub (by decide +kernel : endpoint false 10 ∈ mask 16))
  have c7 := pure_slot h hc hp false 10 14 (by decide +kernel) (sub (by decide +kernel : endpoint false 10 ∈ mask 16))
  have c8 := pure_slot h hc hp false 10 18 (by decide +kernel) (sub (by decide +kernel : endpoint false 10 ∈ mask 16))
  have c9 := exposure h hc hp w2 false 14 15 1 5 9 (by decide +kernel)
  have c10 := exposure h hc hp w2 false 14 15 1 9 9 (by decide +kernel)
  have c11 := couple hp w2 true 1 10 14 (by decide +kernel)
  have c12 := exposure h hc hp w2 true 1 10 15 11 0 (by decide +kernel)
  have c13 := couple hp w2 true 8 11 18 (by decide +kernel)
  have c14 := exposure h hc hp w2 true 8 11 9 10 6 (by decide +kernel)
  have c15 := couple hp w2 true 5 9 15 (by decide +kernel)
  grind only

set_option maxHeartbeats 0 in
theorem noTwo32 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (w2 : ∀ x, (sem_W 14 D x).card≤2) (sub : mask 32 ⊆ ineligSet 14 D) : False := by
  obtain ⟨P,hp⟩ := get_slots h hc
  have c6 := exposure h hc hp w2 false 8 9 18 5 7 (by decide +kernel)
  have c7 := couple hp w2 false 10 11 12 (by decide +kernel)
  have c8 := exposure h hc hp w2 false 10 11 1 8 13 (by decide +kernel)
  have c9 := exposure h hc hp w2 false 10 11 1 18 13 (by decide +kernel)
  have c10 := all_equal h hc hp false 13 14 (by decide +kernel) (sub (by decide +kernel : endpoint false 13 ∈ mask 32))
  have c11 := all_equal h hc hp false 13 15 (by decide +kernel) (sub (by decide +kernel : endpoint false 13 ∈ mask 32))
  have c12 := pure_slot h hc hp false 13 1 (by decide +kernel) (sub (by decide +kernel : endpoint false 13 ∈ mask 32))
  have c13 := pure_slot h hc hp false 13 5 (by decide +kernel) (sub (by decide +kernel : endpoint false 13 ∈ mask 32))
  have c14 := pure_slot h hc hp false 13 9 (by decide +kernel) (sub (by decide +kernel : endpoint false 13 ∈ mask 32))
  have c15 := pure_slot h hc hp false 13 10 (by decide +kernel) (sub (by decide +kernel : endpoint false 13 ∈ mask 32))
  have c16 := couple hp w2 true 1 10 14 (by decide +kernel)
  have c17 := exposure h hc hp w2 true 1 14 11 13 0 (by decide +kernel)
  have c18 := exposure h hc hp w2 true 1 14 12 13 0 (by decide +kernel)
  have c19 := couple hp w2 true 8 11 18 (by decide +kernel)
  have c20 := exposure h hc hp w2 true 8 11 9 12 6 (by decide +kernel)
  have c21 := couple hp w2 true 5 9 15 (by decide +kernel)
  grind only

set_option maxHeartbeats 0 in
theorem noTwo64 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (w2 : ∀ x, (sem_W 14 D x).card≤2) (sub : mask 64 ⊆ ineligSet 14 D) : False := by
  obtain ⟨P,hp⟩ := get_slots h hc
  have c3 := exposure h hc hp w2 false 4 5 0 9 13 (by decide +kernel)
  have c4 := exposure h hc hp w2 false 4 5 0 15 13 (by decide +kernel)
  have c5 := exposure h hc hp w2 false 8 9 11 15 7 (by decide +kernel)
  have c6 := all_equal h hc hp false 16 17 (by decide +kernel) (sub (by decide +kernel : endpoint false 16 ∈ mask 64))
  have c7 := all_equal h hc hp false 16 18 (by decide +kernel) (sub (by decide +kernel : endpoint false 16 ∈ mask 64))
  have c8 := pure_slot h hc hp false 16 0 (by decide +kernel) (sub (by decide +kernel : endpoint false 16 ∈ mask 64))
  have c9 := pure_slot h hc hp false 16 4 (by decide +kernel) (sub (by decide +kernel : endpoint false 16 ∈ mask 64))
  have c10 := pure_slot h hc hp false 16 8 (by decide +kernel) (sub (by decide +kernel : endpoint false 16 ∈ mask 64))
  have c11 := pure_slot h hc hp false 16 11 (by decide +kernel) (sub (by decide +kernel : endpoint false 16 ∈ mask 64))
  have c12 := couple hp w2 true 0 4 16 (by decide +kernel)
  have c13 := exposure h hc hp w2 true 0 16 5 17 0 (by decide +kernel)
  have c14 := couple hp w2 true 8 11 18 (by decide +kernel)
  have c15 := exposure h hc hp w2 true 8 18 9 16 4 (by decide +kernel)
  have c16 := couple hp w2 true 5 9 15 (by decide +kernel)
  grind only

set_option maxHeartbeats 0 in
theorem noTwo128 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (w2 : ∀ x, (sem_W 14 D x).card≤2) (sub : mask 128 ⊆ ineligSet 14 D) : False := by
  obtain ⟨P,hp⟩ := get_slots h hc
  have c2 := couple hp w2 false 7 8 9 (by decide +kernel)
  have c3 := exposure h hc hp w2 false 7 8 2 11 12 (by decide +kernel)
  have c4 := exposure h hc hp w2 false 7 8 2 18 12 (by decide +kernel)
  have c5 := exposure h hc hp w2 false 7 9 2 5 11 (by decide +kernel)
  have c6 := exposure h hc hp w2 false 7 9 2 15 11 (by decide +kernel)
  have c7 := couple hp w2 false 10 11 12 (by decide +kernel)
  have c8 := exposure h hc hp w2 false 10 11 1 18 13 (by decide +kernel)
  have c9 := exposure h hc hp w2 false 10 11 14 18 13 (by decide +kernel)
  have c10 := exposure h hc hp w2 false 14 15 1 5 9 (by decide +kernel)
  have c11 := all_equal h hc hp true 2 7 (by decide +kernel) (sub (by decide +kernel : endpoint true 2 ∈ mask 128))
  have c12 := pure_slot h hc hp true 2 8 (by decide +kernel) (sub (by decide +kernel : endpoint true 2 ∈ mask 128))
  have c13 := pure_slot h hc hp true 2 9 (by decide +kernel) (sub (by decide +kernel : endpoint true 2 ∈ mask 128))
  have c14 := couple hp w2 true 1 10 14 (by decide +kernel)
  have c15 := exposure h hc hp w2 true 10 14 12 15 0 (by decide +kernel)
  have c16 := couple hp w2 true 8 11 18 (by decide +kernel)
  have c17 := exposure h hc hp w2 true 8 11 9 10 6 (by decide +kernel)
  have c18 := exposure h hc hp w2 true 8 11 9 12 6 (by decide +kernel)
  have c19 := couple hp w2 true 5 9 15 (by decide +kernel)
  grind only

set_option maxHeartbeats 0 in
theorem noTwo256 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (w2 : ∀ x, (sem_W 14 D x).card≤2) (sub : mask 256 ⊆ ineligSet 14 D) : False := by
  obtain ⟨P,hp⟩ := get_slots h hc
  have c3 := exposure h hc hp w2 false 4 5 0 9 13 (by decide +kernel)
  have c4 := exposure h hc hp w2 false 4 5 0 15 13 (by decide +kernel)
  have c5 := exposure h hc hp w2 false 8 9 11 15 7 (by decide +kernel)
  have c6 := couple hp w2 false 16 17 18 (by decide +kernel)
  have c7 := exposure h hc hp w2 false 16 18 0 8 9 (by decide +kernel)
  have c8 := exposure h hc hp w2 false 16 18 0 11 9 (by decide +kernel)
  have c9 := all_equal h hc hp true 0 4 (by decide +kernel) (sub (by decide +kernel : endpoint true 0 ∈ mask 256))
  have c10 := all_equal h hc hp true 0 16 (by decide +kernel) (sub (by decide +kernel : endpoint true 0 ∈ mask 256))
  have c11 := pure_slot h hc hp true 0 5 (by decide +kernel) (sub (by decide +kernel : endpoint true 0 ∈ mask 256))
  have c12 := pure_slot h hc hp true 0 17 (by decide +kernel) (sub (by decide +kernel : endpoint true 0 ∈ mask 256))
  have c13 := pure_slot h hc hp true 0 18 (by decide +kernel) (sub (by decide +kernel : endpoint true 0 ∈ mask 256))
  have c14 := couple hp w2 true 8 11 18 (by decide +kernel)
  have c15 := exposure h hc hp w2 true 8 18 9 17 4 (by decide +kernel)
  have c16 := couple hp w2 true 5 9 15 (by decide +kernel)
  grind only

set_option maxHeartbeats 0 in
theorem noTwo512 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (w2 : ∀ x, (sem_W 14 D x).card≤2) (sub : mask 512 ⊆ ineligSet 14 D) : False := by
  obtain ⟨P,hp⟩ := get_slots h hc
  have c2 := exposure h hc hp w2 false 4 5 0 9 13 (by decide +kernel)
  have c3 := exposure h hc hp w2 false 13 15 17 5 10 (by decide +kernel)
  have c4 := exposure h hc hp w2 false 13 15 17 9 10 (by decide +kernel)
  have c5 := couple hp w2 false 16 17 18 (by decide +kernel)
  have c6 := exposure h hc hp w2 false 16 17 0 13 11 (by decide +kernel)
  have c7 := exposure h hc hp w2 false 16 17 4 13 11 (by decide +kernel)
  have c8 := couple hp w2 true 0 4 16 (by decide +kernel)
  have c9 := exposure h hc hp w2 true 4 16 5 18 0 (by decide +kernel)
  have c10 := all_equal h hc hp true 13 17 (by decide +kernel) (sub (by decide +kernel : endpoint true 13 ∈ mask 512))
  have c11 := pure_slot h hc hp true 13 15 (by decide +kernel) (sub (by decide +kernel : endpoint true 13 ∈ mask 512))
  have c12 := pure_slot h hc hp true 13 16 (by decide +kernel) (sub (by decide +kernel : endpoint true 13 ∈ mask 512))
  have c13 := pure_slot h hc hp true 13 18 (by decide +kernel) (sub (by decide +kernel : endpoint true 13 ∈ mask 512))
  have c14 := couple hp w2 true 5 9 15 (by decide +kernel)
  grind only

set_option maxHeartbeats 0 in
theorem noTwo1024 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (w2 : ∀ x, (sem_W 14 D x).card≤2) (sub : mask 1024 ⊆ ineligSet 14 D) : False := by
  obtain ⟨P,hp⟩ := get_slots h hc
  have c3 := exposure h hc hp w2 false 8 9 18 5 7 (by decide +kernel)
  have c4 := couple hp w2 false 10 11 12 (by decide +kernel)
  have c5 := exposure h hc hp w2 false 10 11 1 8 13 (by decide +kernel)
  have c6 := exposure h hc hp w2 false 10 11 1 18 13 (by decide +kernel)
  have c7 := exposure h hc hp w2 false 14 15 1 5 9 (by decide +kernel)
  have c8 := exposure h hc hp w2 false 14 15 1 9 9 (by decide +kernel)
  have c9 := all_equal h hc hp true 1 10 (by decide +kernel) (sub (by decide +kernel : endpoint true 1 ∈ mask 1024))
  have c10 := all_equal h hc hp true 1 14 (by decide +kernel) (sub (by decide +kernel : endpoint true 1 ∈ mask 1024))
  have c11 := pure_slot h hc hp true 1 11 (by decide +kernel) (sub (by decide +kernel : endpoint true 1 ∈ mask 1024))
  have c12 := pure_slot h hc hp true 1 12 (by decide +kernel) (sub (by decide +kernel : endpoint true 1 ∈ mask 1024))
  have c13 := pure_slot h hc hp true 1 15 (by decide +kernel) (sub (by decide +kernel : endpoint true 1 ∈ mask 1024))
  have c14 := couple hp w2 true 8 11 18 (by decide +kernel)
  have c15 := exposure h hc hp w2 true 8 11 9 12 6 (by decide +kernel)
  have c16 := couple hp w2 true 5 9 15 (by decide +kernel)
  grind only

set_option maxHeartbeats 0 in
theorem noTwo2048 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (w2 : ∀ x, (sem_W 14 D x).card≤2) (sub : mask 2048 ⊆ ineligSet 14 D) : False := by
  obtain ⟨P,hp⟩ := get_slots h hc
  have c2 := exposure h hc hp w2 false 8 9 11 5 7 (by decide +kernel)
  have c3 := exposure h hc hp w2 false 8 9 11 15 7 (by decide +kernel)
  have c4 := couple hp w2 false 10 11 12 (by decide +kernel)
  have c5 := exposure h hc hp w2 false 10 11 1 8 13 (by decide +kernel)
  have c6 := exposure h hc hp w2 false 10 11 14 8 13 (by decide +kernel)
  have c7 := exposure h hc hp w2 false 14 15 1 5 9 (by decide +kernel)
  have c8 := couple hp w2 true 1 10 14 (by decide +kernel)
  have c9 := exposure h hc hp w2 true 10 14 12 15 0 (by decide +kernel)
  have c10 := all_equal h hc hp true 8 11 (by decide +kernel) (sub (by decide +kernel : endpoint true 8 ∈ mask 2048))
  have c11 := pure_slot h hc hp true 8 9 (by decide +kernel) (sub (by decide +kernel : endpoint true 8 ∈ mask 2048))
  have c12 := pure_slot h hc hp true 8 10 (by decide +kernel) (sub (by decide +kernel : endpoint true 8 ∈ mask 2048))
  have c13 := pure_slot h hc hp true 8 12 (by decide +kernel) (sub (by decide +kernel : endpoint true 8 ∈ mask 2048))
  have c14 := couple hp w2 true 5 9 15 (by decide +kernel)
  grind only

set_option maxHeartbeats 0 in
theorem noTwo4096 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (w2 : ∀ x, (sem_W 14 D x).card≤2) (sub : mask 4096 ⊆ ineligSet 14 D) : False := by
  obtain ⟨P,hp⟩ := get_slots h hc
  have c0 := couple hp w2 false 4 5 6 (by decide +kernel)
  have c1 := exposure h hc hp w2 false 4 5 0 9 13 (by decide +kernel)
  have c2 := exposure h hc hp w2 false 4 5 16 9 13 (by decide +kernel)
  have c3 := exposure h hc hp w2 false 8 9 11 5 7 (by decide +kernel)
  have c4 := couple hp w2 false 16 17 18 (by decide +kernel)
  have c5 := exposure h hc hp w2 false 16 18 0 8 9 (by decide +kernel)
  have c6 := exposure h hc hp w2 false 16 18 0 11 9 (by decide +kernel)
  have c7 := couple hp w2 true 0 4 16 (by decide +kernel)
  have c8 := exposure h hc hp w2 true 4 16 6 17 0 (by decide +kernel)
  have c9 := exposure h hc hp w2 true 4 16 6 18 0 (by decide +kernel)
  have c10 := couple hp w2 true 8 11 18 (by decide +kernel)
  have c11 := exposure h hc hp w2 true 8 18 9 17 4 (by decide +kernel)
  have c12 := all_equal h hc hp true 5 9 (by decide +kernel) (sub (by decide +kernel : endpoint true 5 ∈ mask 4096))
  have c13 := pure_slot h hc hp true 5 4 (by decide +kernel) (sub (by decide +kernel : endpoint true 5 ∈ mask 4096))
  have c14 := pure_slot h hc hp true 5 6 (by decide +kernel) (sub (by decide +kernel : endpoint true 5 ∈ mask 4096))
  grind only

set_option maxHeartbeats 0 in
theorem noTwo8192 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (w2 : ∀ x, (sem_W 14 D x).card≤2) (sub : mask 8192 ⊆ ineligSet 14 D) : False := by
  obtain ⟨P,hp⟩ := get_slots h hc
  have c2 := couple hp w2 false 4 5 6 (by decide +kernel)
  have c3 := exposure h hc hp w2 false 4 6 0 3 12 (by decide +kernel)
  have c4 := exposure h hc hp w2 false 4 6 16 3 12 (by decide +kernel)
  have c5 := exposure h hc hp w2 false 5 6 9 3 8 (by decide +kernel)
  have c6 := exposure h hc hp w2 false 5 6 15 3 8 (by decide +kernel)
  have c7 := exposure h hc hp w2 false 8 9 11 15 7 (by decide +kernel)
  have c8 := exposure h hc hp w2 false 8 9 18 15 7 (by decide +kernel)
  have c9 := exposure h hc hp w2 false 16 18 0 11 9 (by decide +kernel)
  have c10 := couple hp w2 true 0 4 16 (by decide +kernel)
  have c11 := exposure h hc hp w2 true 4 16 5 18 0 (by decide +kernel)
  have c12 := couple hp w2 true 8 11 18 (by decide +kernel)
  have c13 := couple hp w2 true 5 9 15 (by decide +kernel)
  have c14 := exposure h hc hp w2 true 5 9 4 8 5 (by decide +kernel)
  have c15 := all_equal h hc hp true 3 6 (by decide +kernel) (sub (by decide +kernel : endpoint true 3 ∈ mask 8192))
  have c16 := pure_slot h hc hp true 3 4 (by decide +kernel) (sub (by decide +kernel : endpoint true 3 ∈ mask 8192))
  have c17 := pure_slot h hc hp true 3 5 (by decide +kernel) (sub (by decide +kernel : endpoint true 3 ∈ mask 8192))
  grind only

set_option maxHeartbeats 0 in
theorem needs_three {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (nonempty : (ineligSet 14 D).Nonempty) : ∃ x, 3≤(sem_W 14 D x).card := by
  by_contra! none
  have w2 (x) : (sem_W 14 D x).card ≤ 2 := by have := none x; omega
  obtain ⟨x,hx⟩ := nonempty
  fin_cases x
  · apply noTwo1 h hc w2
    have eq : mask 1 = {(0:V)} := by decide +kernel
    rw [eq,Finset.singleton_subset_iff]; exact hx
  · apply noTwo2 h hc w2
    have eq : mask 2 = {(1:V)} := by decide +kernel
    rw [eq,Finset.singleton_subset_iff]; exact hx
  · apply noTwo4 h hc w2
    have eq : mask 4 = {(2:V)} := by decide +kernel
    rw [eq,Finset.singleton_subset_iff]; exact hx
  · apply noTwo8 h hc w2
    have eq : mask 8 = {(3:V)} := by decide +kernel
    rw [eq,Finset.singleton_subset_iff]; exact hx
  · apply noTwo16 h hc w2
    have eq : mask 16 = {(4:V)} := by decide +kernel
    rw [eq,Finset.singleton_subset_iff]; exact hx
  · apply noTwo32 h hc w2
    have eq : mask 32 = {(5:V)} := by decide +kernel
    rw [eq,Finset.singleton_subset_iff]; exact hx
  · apply noTwo64 h hc w2
    have eq : mask 64 = {(6:V)} := by decide +kernel
    rw [eq,Finset.singleton_subset_iff]; exact hx
  · apply noTwo128 h hc w2
    have eq : mask 128 = {(7:V)} := by decide +kernel
    rw [eq,Finset.singleton_subset_iff]; exact hx
  · apply noTwo256 h hc w2
    have eq : mask 256 = {(8:V)} := by decide +kernel
    rw [eq,Finset.singleton_subset_iff]; exact hx
  · apply noTwo512 h hc w2
    have eq : mask 512 = {(9:V)} := by decide +kernel
    rw [eq,Finset.singleton_subset_iff]; exact hx
  · apply noTwo1024 h hc w2
    have eq : mask 1024 = {(10:V)} := by decide +kernel
    rw [eq,Finset.singleton_subset_iff]; exact hx
  · apply noTwo2048 h hc w2
    have eq : mask 2048 = {(11:V)} := by decide +kernel
    rw [eq,Finset.singleton_subset_iff]; exact hx
  · apply noTwo4096 h hc w2
    have eq : mask 4096 = {(12:V)} := by decide +kernel
    rw [eq,Finset.singleton_subset_iff]; exact hx
  · apply noTwo8192 h hc w2
    have eq : mask 8192 = {(13:V)} := by decide +kernel
    rw [eq,Finset.singleton_subset_iff]; exact hx

set_option maxHeartbeats 0 in
theorem surplus_extra {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (nonempty : (ineligSet 14 D).Nonempty) : (eligSet 14 D).card + 1 ≤ Bplus 14 D := by
  by_contra! small
  obtain ⟨x,hx⟩ := needs_three h hc nonempty
  have := at_most_two h hc (by omega) x
  omega

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_9774_aux.DagTools

theorem surviving_designs {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (short : D.length≤24) :
    ∃ m : Fin 16384, mask m.val = ineligSet 14 D ∧
      ((Bplus 14 D=11 ∧ Bzero 14 D=0 ∧ 4 ≤ (ineligSet 14 D).card) ∨
       (Bplus 14 D=10 ∧ Bzero 14 D=1 ∧ (m.val=127 ∨ m.val=16256))) := by
  obtain ⟨m,enc⟩ := repr (ineligSet 14 D)
  refine ⟨m,enc,?_⟩
  have total := surplus_identity h
  have split := totalSurplus_split 14 D
  have card := inelig_card_add 14 D
  obtain ⟨b,hb⟩ := sem_exists_pureBranch graph_ok h.1 hc
  have pc := elig_le_Bplus h.1 b hb
  have ine : (ineligSet 14 D).Nonempty := Finset.card_pos.1 (by omega)
  have extra := surplus_extra h hc ine
  have test := all_masks m
  simp only [claim,Bool.and_eq_true,Bool.not_eq_true',Bool.or_eq_true,List.contains_iff_mem] at test
  have floor : 10≤Bplus 14 D := by
    by_contra! low
    have yes := possible_of h hc 9 m.val enc (by omega)
    grind
  by_cases eq : Bplus 14 D=11
  · left; exact ⟨eq,by omega,by omega⟩
  right
  have b10 : Bplus 14 D=10 := by omega
  have yes := possible_of h hc 10 m.val enc (by omega)
  have choice : m.val∈sevenMasks := test.2.resolve_left (by simp [yes])
  have side : m.val=127 ∨ m.val=16256 := by
    simp only [sevenMasks,List.mem_cons,List.not_mem_nil,or_false] at choice
    rw [←enc] at card
    rcases choice with eq | eq | eq | eq | eq | eq | eq
    · exact Or.inl eq
    all_goals first | exact Or.inr eq | rw [eq] at card
    all_goals first
      | rw [show (mask 523).card=4 by decide +kernel] at card
      | rw [show (mask 1290).card=4 by decide +kernel] at card
      | rw [show (mask 8416).card=4 by decide +kernel] at card
      | rw [show (mask 8713).card=4 by decide +kernel] at card
      | rw [show (mask 8833).card=4 by decide +kernel] at card
    all_goals omega
  refine ⟨b10,?_,side⟩
  by_contra! hn
  have zero : Bzero 14 D=0 := by omega
  rcases side with eq | eq <;> rw [eq] at enc
  · have := side127 h hc zero enc; omega
  · have := side16256 h hc zero enc; omega

open PEqualNP.Outside.L_meta_9774_aux.DagTools

set_option maxHeartbeats 0 in
theorem forced_mark {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (z : Bzero 14 D≤1) (P : Finset V) (ind : independent P)
    {i j : V} (hi : i∈ineligSet 14 D) (hj : j∈ineligSet 14 D) (ne : i≠j)
    (wi : i∈wide P) (wj : j∈wide P) : i∈marks D P ∨ j∈marks D P := by
  have ci : (projected P i).card=3 := by simpa [wide] using wi
  have cj : (projected P j).card=3 := by simpa [wide] using wj
  have miss : ¬projected P j ⊆ projected P i := by
    intro e
    have small := proj_meet P ne.symm
    rw [Finset.inter_eq_left.mpr e,cj] at small
    omega
  obtain ⟨a,aj,ai⟩ := Finset.not_subset.mp miss
  obtain ⟨ap,ja⟩ := (proj_mem _ _ _).mp aj
  have no : ¬adj i a := fun ia => ai ((proj_mem _ _ _).2 ⟨ap,ia⟩)
  have asOcc {k : V} {w : Nat} (ex : ∀ a ∈P, a ∈supp 14 D w ↔ adj k a) : sup_Occ 14 D P (projected P k) := by
    refine ⟨w,?_⟩; ext a
    simp only [Finset.mem_inter,proj_mem]
    constructor
    · rintro ⟨a1,a2⟩; exact ⟨a2,(ex a a2).1 a1⟩
    · rintro ⟨a1,a2⟩; exact ⟨(ex a a1).2 a2,a1⟩
  rcases sem_shared_empty graph_ok h hc z P ind hi hj ⟨a,ap,ja,no⟩ with
    ⟨k,s,_,_,_,ex⟩ | ⟨k,s,_,_,_,ex⟩
  · exact Or.inl (mark_iff.2 ⟨ci,asOcc ex⟩)
  · exact Or.inr (mark_iff.2 ⟨cj,asOcc ex⟩)

set_option maxHeartbeats 0 in
theorem mark_shape {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D≤1)
    (P : Finset V) (ind : independent P) (sub : wide P ⊆ ineligSet 14 D) :
    marks D P=wide P ∨ ∃ k∈wide P, marks D P=(wide P).erase k := by
  classical
  have incl : marks D P ⊆ wide P := Finset.filter_subset _ _
  by_cases all : wide P ⊆ marks D P
  · exact Or.inl (Finset.Subset.antisymm incl all)
  obtain ⟨k,hk,miss⟩ := Finset.not_subset.mp all
  right; refine ⟨k,hk,?_⟩
  ext i
  constructor
  · intro hi; exact Finset.mem_erase.2 ⟨fun e => miss (e ▸ hi),incl hi⟩
  · intro hi
    obtain ⟨ne,wi⟩ := Finset.mem_erase.1 hi
    exact (forced_mark h hc z P ind (sub wi) (sub hk) ne wi hk).resolve_right miss

set_option maxHeartbeats 0 in
theorem side_budget {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D≤1)
    (P I : Finset V) (sizeP : P.card=7) (sizeI : I.card=7) (ind : independent P) (sub : wide P ⊆ I)
    (geo : (I∩wide P).card=5 ∧ 13 ≤ 2*(wide P).card+(labels P (wide P)).card ∧
      ∀ k∈wide P, 13 ≤ 2*((wide P).erase k).card+(labels P ((wide P).erase k)).card)
    (eq : I=ineligSet 14 D) : 11≤Bplus 14 D := by
  have eqI := inelig_card_add 14 D
  rw [←eq,sizeI] at eqI
  have bound := projected_count h hc P ind sizeP.le
  rw [←eq,geo.1] at bound
  have card := Finset.card_le_card (Finset.inter_subset_left : P∩eligSet 14 D ⊆ P)
  rcases mark_shape h hc z P ind (eq ▸ sub) with all | ⟨k,hk,lost⟩
  · rw [all] at bound
    have := geo.2.1
    omega
  · rw [lost] at bound
    have := geo.2.2 k hk
    omega

set_option maxHeartbeats 0 in
theorem no_empty_surplus {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (short : D.length≤24) : Bplus 14 D=11 ∧ Bzero 14 D=0 ∧ 4≤(ineligSet 14 D).card := by
  obtain ⟨m,enc,good|⟨bp,bz,eq|eq⟩⟩ := surviving_designs h hc short
  · exact good
  · rw [eq] at enc
    have u := side_budget h hc (by omega) (mask 16256) (mask 127) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) enc
    omega
  · rw [eq] at enc
    have u := side_budget h hc (by omega) (mask 127) (mask 16256) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) enc
    omega

def rejectedPairs : List Nat := [5, 6, 9, 17, 20, 33, 34, 48, 65, 66, 68, 96, 272, 288, 768, 1028, 1088, 1280, 1536, 2176, 2560, 4608, 6144, 8704]

def pairTest (m : Nat) : Bool :=
  !possible 11 m ||
    ((decide ((mask m).card ≠ 4) || rejectedPairs.any (fun k => (k &&& m)==k)) &&
     (decide ((mask m).card < 7) || m==127 || m==16256))

open PEqualNP.Outside.L_meta_9774_aux.DagTools PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem all_pair_tests_list : survivingMasks.all pairTest = true := by decide +kernel
theorem all_pair_tests (m : Fin 16384) : pairTest m.val = true := by
  by_cases ok : possible 11 m.val = true
  · have mem := all_survivors m
    simp only [survivorTest, ok, Bool.not_true, Bool.false_or, List.contains_iff_mem] at mem
    exact List.all_eq_true.mp all_pair_tests_list _ mem
  ·
    simp [pairTest,Bool.eq_false_iff.mpr ok]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem narrow {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (len : D.length≤24) :
    Bplus 14 D=11 ∧ Bzero 14 D=0 ∧ (4≤(ineligSet 14 D).card ∧ (ineligSet 14 D).card≤6) := by
  obtain ⟨bp,bz,lo⟩ := no_empty_surplus h hc len
  obtain ⟨m,enc⟩ := repr (ineligSet 14 D)
  have ok := possible_of h hc 11 m.val enc bp.le
  have check := all_pair_tests m
  simp only [pairTest,ok,Bool.not_true,Bool.false_or,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq,beq_iff_eq] at check
  have count := inelig_card_add 14 D
  have high : (mask m.val).card<7 := by
    by_contra! hi
    have side : m.val=127 ∨ m.val=16256 := by rcases check.2 with (l|s)|s; omega; exact Or.inl s; exact Or.inr s
    rcases side with e|e <;> rw [e] at enc
    · have := side127 h hc bz enc; omega
    · have := side16256 h hc bz enc; omega
  rw [enc] at high
  exact ⟨bp,bz,lo,by omega⟩

open PEqualNP.Outside.L_meta_9774_aux.DagTools

set_option maxHeartbeats 0 in
theorem partial_exits {n : Nat} {G : Fin n → Fin n → Prop} {D : Dag} (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {pos : Fin n → ℕ × Bool} (hpos : k4_Pos n G D pos) (T J Q : Finset (Fin n)) (qsub : Q ⊆ T)
    (A : Fin n → Finset (Fin n))
    (hJ : ∀ i ∈ J, i ∈ ineligSet n D ∧ (∃ a ∈ T, G i a) ∧ ∀ f ∈ Q, ∃ a ∈ A f, G i a)
    (hA : ∀ f ∈ Q, (∀ a ∈ A f, ∀ b ∈ A f, ¬ G a b) ∧ T.erase f ⊆ A f ∧ ∃ a ∈ A f, G f a) :
    J.card + Q.card ≤ (exitArcs n D (carrierT n D T)).card := by
  classical
  obtain ⟨hsub, hcard⟩ := k4_exits_ge hpos T J (fun i hi => ⟨(hJ i hi).1, (hJ i hi).2.1⟩)
  have hex : ∀ f ∈ Q, ∃ e : ℕ × Bool, e.1 < D.length ∧ tag D e.1 = true ∧
      f ∈ supp n D (src D e) ∧ f ∉ supp n D (n + e.1) ∧ Disjoint (supp n D (src D e)) (A f) := by
    intro f hf
    obtain ⟨j, s, h1, h2, h4, h5, h6⟩ := sem_exposure hG hS hC (A f) (hA f hf).1 f (hA f hf).2.2
    exact ⟨(j, s), h1, h2, h4, h5, h6⟩
  choose! w hw using hex
  have hinj : Set.InjOn w Q := by
    intro f hf g hg hfg
    by_contra hne
    exact Finset.disjoint_left.1 (hw f hf).2.2.2.2 (hfg ▸ (hw g hg).2.2.1)
      ((hA f hf).2.1 (Finset.mem_erase.2 ⟨fun h => hne h.symm, qsub hg⟩))
  have hdis : Disjoint (J.image pos) (Q.image w) := by
    rw [Finset.disjoint_left]
    intro e he1 he2
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 he1
    obtain ⟨f, hf, hfe⟩ := Finset.mem_image.1 he2
    obtain ⟨a, ha, hia⟩ := (hJ i hi).2.2 f hf
    exact Finset.disjoint_left.1 (hw f hf).2.2.2.2
      (hfe ▸ (hpos.1 i (hJ i hi).1).2.2.1 a hia) ha
  have hsub2 : Q.image w ⊆ exitArcs n D (carrierT n D T) := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨h1, h2, h4, h5, h6⟩ := hw f hf
    refine k4_mem_exit.2 ⟨h1, ⟨f, Finset.mem_inter.2 ⟨h4, qsub hf⟩⟩, ?_⟩
    rintro ⟨g, hg⟩
    rw [Finset.mem_inter] at hg
    have hgs : g ∈ supp n D (src D (w f)) := sem_supp_and_sub hS h1 h2 (w f).2 hg.1
    exact Finset.disjoint_left.1 h6 hgs
      ((hA f hf).2.1 (Finset.mem_erase.2 ⟨fun h => h5 (h ▸ hg.1), hg.2⟩))
  have := Finset.card_le_card (Finset.union_subset hsub hsub2)
  rw [Finset.card_union_of_disjoint hdis, hcard, Finset.card_image_of_injOn hinj] at this
  exact this

set_option maxHeartbeats 0 in
theorem local_merge {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (zero : Bzero 14 D = 0) (P I U W : Finset V) (ind : independent P) (p7 : P.card ≤ 7)
    (sub : I ⊆ ineligSet 14 D) (u : ∀ i ∈ U, i ∈ I ∧ (projected P i).card=3)
    (w : ∀ i ∈ W, i ∈ I ∧ (projected P i).card=2) :
    2*U.card+W.card ≤ (merges 14 D (carrierT 14 D P)).card := by
  let f := projected P
  have sep {i j : V} (ne : i≠j) : (f i ∩ f j).card≤1 := proj_meet P ne
  have inj {T : Finset V} (hi : ∀ i∈T, 2≤(f i).card) : Set.InjOn f T := by
    intro i iT j _ eq
    by_contra ne
    have le := sep ne
    rw [←eq,Finset.inter_self] at le
    have := hi i iT
    omega
  have uinj : Set.InjOn f U := inj (fun i hi => by have := (u i hi).2; change 2≤(projected P i).card; omega)
  have winj : Set.InjOn f W := inj (fun i hi => (w i hi).2.ge)
  have m := sup_charge h.1 p7 (U.image f) (fun T ht => by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ht
    exact ⟨(u _ hi).2,occurs h hc zero P ind i (sub (u _ hi).1)⟩) (fun T ht M hm diff => by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hm
    exact sep (fun e => diff (congrArg f e))) (W.image f) (fun M hm => by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hm
    have c : (f i).card=2 := (w i hi).2
    have separate : ∀ j∈U, ¬f i ⊆ f j := by
      intro j hj incl
      have cj : (f j).card=3 := (u j hj).2
      have distinct : i≠j := by rintro rfl; omega
      have v := sep distinct
      rw [Finset.inter_eq_left.mpr incl,c] at v
      omega
    refine ⟨occurs h hc zero P ind i (sub (w _ hi).1),by omega,?_,by omega,by omega,?_⟩
    · intro mem
      obtain ⟨j,hj,eq⟩ := Finset.mem_image.mp mem
      exact separate j hj (by rw [eq])
    · intro _ T ht
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp ht
      exact separate j hj)
  rw [Finset.card_image_of_injOn uinj,Finset.card_image_of_injOn winj] at m
  exact m.trans (Finset.card_le_card (Finset.filter_subset _ _))

set_option maxHeartbeats 0 in
theorem private_bound {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (zero : Bzero 14 D=0) (P I U W J Q : Finset V) (A : V → Finset V)
    (eq : I=ineligSet 14 D) (ind : independent P) (p7 : P.card≤7) (qs : Q⊆P)
    (u : ∀ i∈U, i∈I ∧ (projected P i).card=3) (w : ∀ i∈W, i∈I ∧ (projected P i).card=2)
    (j : ∀ i∈J, i∈I ∧ (∃ a ∈ P, adj i a) ∧ ∀ f ∈ Q, ∃ a ∈ A f, adj i a)
    (free : ∀ f∈Q, independent (A f) ∧ P.erase f ⊆ A f ∧ ∃ a∈A f, adj f a) :
    J.card+Q.card+2*U.card+W.card+(14-I.card) ≤ P.card+(P \ I).card+Bplus 14 D := by
  obtain ⟨b,hb⟩ := sem_exists_pureBranch graph_ok h.1 hc
  obtain ⟨pos,hpos⟩ := k4_assigned graph_ok h hc
  have lo := local_merge h hc zero P I U W ind p7 (eq ▸ Finset.Subset.rfl) u w
  have exits := partial_exits graph_ok h.1 hc hpos P J Q qs A
    (fun i hi => ⟨eq ▸ (j i hi).1,(j i hi).2⟩) free
  have fl := carrier_flow_union h P (by rw [sem_supp_out graph_ok hc];simp)
  have sup := surplus_carrierT_le h.1 b hb P
  have card := inelig_card_add 14 D
  have seteq : P \ I = P ∩ eligSet 14 D := by
    ext x
    simp [eq,sem_mem_inelig]
  rw [seteq,eq]
  omega

open PEqualNP.Outside.L_meta_9774_aux.DagTools

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection63 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0)
    (eq : mask 63=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 13568) (mask 63) (mask 4) (mask 49) (mask 63) (mask 256) (fun f : V => mask ([0,0,0,0,0,0,0,0,13504,0,0,0,0,0] : List Nat)[f.val]!) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 63).card+(mask 256).card+2*(mask 4).card+(mask 49).card+(14-(mask 63).card)=20 := by decide +kernel
  have rhs : (mask 13568).card+(mask 13568 \ mask 63).card=8 := by decide +kernel
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection95 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0)
    (eq : mask 95=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 11520) (mask 95) (mask 16) (mask 69) (mask 95) (mask 1024) (fun f : V => mask ([0,0,0,0,0,0,0,0,0,0,10656,0,0,0] : List Nat)[f.val]!) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 95).card+(mask 1024).card+2*(mask 16).card+(mask 69).card+(14-(mask 95).card)=20 := by decide +kernel
  have rhs : (mask 11520).card+(mask 11520 \ mask 95).card=8 := by decide +kernel
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection109 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0)
    (eq : mask 109=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 5376) (mask 109) (mask 0) (mask 37) (mask 109) (mask 1024) (fun f : V => mask ([0,0,0,0,0,0,0,0,0,0,4882,0,0,0] : List Nat)[f.val]!) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 109).card+(mask 1024).card+2*(mask 0).card+(mask 37).card+(14-(mask 109).card)=18 := by decide +kernel
  have rhs : (mask 5376).card+(mask 5376 \ mask 109).card=6 := by decide +kernel
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection119 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0)
    (eq : mask 119=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 11520) (mask 119) (mask 16) (mask 69) (mask 119) (mask 2048) (fun f : V => mask ([0,0,0,0,0,0,0,0,0,0,0,9992,0,0] : List Nat)[f.val]!) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 119).card+(mask 2048).card+2*(mask 16).card+(mask 69).card+(14-(mask 119).card)=20 := by decide +kernel
  have rhs : (mask 11520).card+(mask 11520 \ mask 119).card=8 := by decide +kernel
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection121 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0)
    (eq : mask 121=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 3328) (mask 121) (mask 0) (mask 81) (mask 121) (mask 256) (fun f : V => mask ([0,0,0,0,0,0,0,0,3590,0,0,0,0,0] : List Nat)[f.val]!) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 121).card+(mask 256).card+2*(mask 0).card+(mask 81).card+(14-(mask 121).card)=18 := by decide +kernel
  have rhs : (mask 3328).card+(mask 3328 \ mask 121).card=6 := by decide +kernel
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection125 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0)
    (eq : mask 125=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 15616) (mask 125) (mask 20) (mask 105) (mask 125) (mask 8192) (fun f : V => mask ([0,0,0,0,0,0,0,0,0,0,0,0,0,7938] : List Nat)[f.val]!) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 125).card+(mask 8192).card+2*(mask 20).card+(mask 105).card+(14-(mask 125).card)=23 := by decide +kernel
  have rhs : (mask 15616).card+(mask 15616 \ mask 125).card=10 := by decide +kernel
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection126 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0)
    (eq : mask 126=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 14592) (mask 126) (mask 4) (mask 88) (mask 126) (mask 256) (fun f : V => mask ([0,0,0,0,0,0,0,0,14977,0,0,0,0,0] : List Nat)[f.val]!) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 126).card+(mask 256).card+2*(mask 4).card+(mask 88).card+(14-(mask 126).card)=20 := by decide +kernel
  have rhs : (mask 14592).card+(mask 14592 \ mask 126).card=8 := by decide +kernel
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection229 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0)
    (eq : mask 229=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 5376) (mask 229) (mask 0) (mask 37) (mask 101) (mask 5120) (fun f : V => mask ([0,0,0,0,0,0,0,0,0,0,4882,0,1802,0] : List Nat)[f.val]!) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 101).card+(mask 5120).card+2*(mask 0).card+(mask 37).card+(14-(mask 229).card)=18 := by decide +kernel
  have rhs : (mask 5376).card+(mask 5376 \ mask 229).card=6 := by decide +kernel
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection241 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0)
    (eq : mask 241=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 3328) (mask 241) (mask 0) (mask 81) (mask 113) (mask 2304) (fun f : V => mask ([0,0,0,0,0,0,0,0,3590,0,0,1802,0,0] : List Nat)[f.val]!) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 113).card+(mask 2304).card+2*(mask 0).card+(mask 81).card+(14-(mask 241).card)=18 := by decide +kernel
  have rhs : (mask 3328).card+(mask 3328 \ mask 241).card=6 := by decide +kernel
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection245 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0)
    (eq : mask 245=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 11520) (mask 245) (mask 16) (mask 69) (mask 117) (mask 10240) (fun f : V => mask ([0,0,0,0,0,0,0,0,0,0,0,9992,0,7938] : List Nat)[f.val]!) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 117).card+(mask 10240).card+2*(mask 16).card+(mask 69).card+(14-(mask 245).card)=20 := by decide +kernel
  have rhs : (mask 11520).card+(mask 11520 \ mask 245).card=8 := by decide +kernel
  omega

open PEqualNP.Outside.L_meta_9774_aux.DagTools

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection535 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0)
    (eq : mask 535=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 9472) (mask 535) (mask 0) (mask 21) (mask 23) (mask 1280) (fun f : V => mask ([0,0,0,0,0,0,0,0,9288,0,8488,0,0,0] : List Nat)[f.val]!) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 23).card+(mask 1280).card+2*(mask 0).card+(mask 21).card+(14-(mask 535).card)=18 := by decide +kernel
  have rhs : (mask 9472).card+(mask 9472 \ mask 535).card=6 := by decide +kernel
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection542 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0)
    (eq : mask 542=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 14336) (mask 542) (mask 0) (mask 28) (mask 30) (mask 6144) (fun f : V => mask ([0,0,0,0,0,0,0,0,0,0,0,12481,10401,0] : List Nat)[f.val]!) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 30).card+(mask 6144).card+2*(mask 0).card+(mask 28).card+(14-(mask 542).card)=18 := by decide +kernel
  have rhs : (mask 14336).card+(mask 14336 \ mask 542).card=6 := by decide +kernel
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection661 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0)
    (eq : mask 661=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 9472) (mask 661) (mask 0) (mask 21) (mask 21) (mask 9472) (fun f : V => mask ([0,0,0,0,0,0,0,0,9288,0,8488,0,0,1802] : List Nat)[f.val]!) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 21).card+(mask 9472).card+2*(mask 0).card+(mask 21).card+(14-(mask 661).card)=18 := by decide +kernel
  have rhs : (mask 9472).card+(mask 9472 \ mask 661).card=6 := by decide +kernel
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection2213 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0)
    (eq : mask 2213=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 5376) (mask 2213) (mask 0) (mask 37) (mask 37) (mask 5376) (fun f : V => mask ([0,0,0,0,0,0,0,0,5186,0,4882,0,1802,0] : List Nat)[f.val]!) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 37).card+(mask 5376).card+2*(mask 0).card+(mask 37).card+(14-(mask 2213).card)=18 := by decide +kernel
  have rhs : (mask 5376).card+(mask 5376 \ mask 2213).card=6 := by decide +kernel
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection3590 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0)
    (eq : mask 3590=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 112) (mask 3590) (mask 0) (mask 3584) (mask 3584) (mask 112) (fun f : V => mask ([0,0,0,0,8297,4179,314,0,0,0,0,0,0,0] : List Nat)[f.val]!) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 3584).card+(mask 112).card+2*(mask 0).card+(mask 3584).card+(14-(mask 3590).card)=18 := by decide +kernel
  have rhs : (mask 112).card+(mask 112 \ mask 3590).card=6 := by decide +kernel
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection3842 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0)
    (eq : mask 3842=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 112) (mask 3842) (mask 0) (mask 3584) (mask 3840) (mask 48) (fun f : V => mask ([0,0,0,0,8297,4179,0,0,0,0,0,0,0,0] : List Nat)[f.val]!) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 3840).card+(mask 48).card+2*(mask 0).card+(mask 3584).card+(14-(mask 3842).card)=18 := by decide +kernel
  have rhs : (mask 112).card+(mask 112 \ mask 3842).card=6 := by decide +kernel
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection4305 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0)
    (eq : mask 4305=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 3328) (mask 4305) (mask 0) (mask 81) (mask 81) (mask 3328) (fun f : V => mask ([0,0,0,0,0,0,0,0,3590,0,2338,1802,0,0] : List Nat)[f.val]!) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 81).card+(mask 3328).card+2*(mask 0).card+(mask 81).card+(14-(mask 4305).card)=18 := by decide +kernel
  have rhs : (mask 3328).card+(mask 3328 \ mask 4305).card=6 := by decide +kernel
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection4882 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0)
    (eq : mask 4882=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 100) (mask 4882) (mask 0) (mask 4864) (mask 4864) (mask 100) (fun f : V => mask ([0,0,8297,0,0,1102,2087,0,0,0,0,0,0,0] : List Nat)[f.val]!) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 4864).card+(mask 100).card+2*(mask 0).card+(mask 4864).card+(14-(mask 4882).card)=18 := by decide +kernel
  have rhs : (mask 100).card+(mask 100 \ mask 4882).card=6 := by decide +kernel
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection5890 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0)
    (eq : mask 5890=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 100) (mask 5890) (mask 0) (mask 4864) (mask 5888) (mask 68) (fun f : V => mask ([0,0,8297,0,0,0,2087,0,0,0,0,0,0,0] : List Nat)[f.val]!) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 5888).card+(mask 68).card+2*(mask 0).card+(mask 4864).card+(14-(mask 5890).card)=18 := by decide +kernel
  have rhs : (mask 100).card+(mask 100 \ mask 5890).card=6 := by decide +kernel
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection6659 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0)
    (eq : mask 6659=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 104) (mask 6659) (mask 0) (mask 6656) (mask 6656) (mask 104) (fun f : V => mask ([0,0,0,245,0,1102,314,0,0,0,0,0,0,0] : List Nat)[f.val]!) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 6656).card+(mask 104).card+2*(mask 0).card+(mask 6656).card+(14-(mask 6659).card)=18 := by decide +kernel
  have rhs : (mask 104).card+(mask 104 \ mask 6659).card=6 := by decide +kernel
  omega

open PEqualNP.Outside.L_meta_9774_aux.DagTools

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection6785 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0)
    (eq : mask 6785=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 104) (mask 6785) (mask 0) (mask 6656) (mask 6784) (mask 96) (fun f : V => mask ([0,0,0,0,0,1102,314,0,0,0,0,0,0,0] : List Nat)[f.val]!) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 6784).card+(mask 96).card+2*(mask 0).card+(mask 6656).card+(14-(mask 6785).card)=18 := by decide +kernel
  have rhs : (mask 104).card+(mask 104 \ mask 6785).card=6 := by decide +kernel
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection7938 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0)
    (eq : mask 7938=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 108) (mask 7938) (mask 4096) (mask 2816) (mask 7936) (mask 12) (fun f : V => mask ([0,0,8297,245,0,0,0,0,0,0,0,0,0,0] : List Nat)[f.val]!) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 7936).card+(mask 12).card+2*(mask 4096).card+(mask 2816).card+(14-(mask 7938).card)=20 := by decide +kernel
  have rhs : (mask 108).card+(mask 108 \ mask 7938).card=8 := by decide +kernel
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection8064 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0)
    (eq : mask 8064=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 108) (mask 8064) (mask 4096) (mask 2816) (mask 8064) (mask 4) (fun f : V => mask ([0,0,8297,0,0,0,0,0,0,0,0,0,0,0] : List Nat)[f.val]!) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 8064).card+(mask 4).card+2*(mask 4096).card+(mask 2816).card+(14-(mask 8064).card)=20 := by decide +kernel
  have rhs : (mask 108).card+(mask 108 \ mask 8064).card=8 := by decide +kernel
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection12032 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0)
    (eq : mask 12032=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 84) (mask 12032) (mask 0) (mask 10496) (mask 12032) (mask 4) (fun f : V => mask ([0,0,4179,0,0,0,0,0,0,0,0,0,0,0] : List Nat)[f.val]!) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 12032).card+(mask 4).card+2*(mask 0).card+(mask 10496).card+(14-(mask 12032).card)=18 := by decide +kernel
  have rhs : (mask 84).card+(mask 84 \ mask 12032).card=6 := by decide +kernel
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection14080 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0)
    (eq : mask 14080=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 52) (mask 14080) (mask 0) (mask 13312) (mask 14080) (mask 16) (fun f : V => mask ([0,0,0,0,2087,0,0,0,0,0,0,0,0,0] : List Nat)[f.val]!) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 14080).card+(mask 16).card+2*(mask 0).card+(mask 13312).card+(14-(mask 14080).card)=18 := by decide +kernel
  have rhs : (mask 52).card+(mask 52 \ mask 14080).card=6 := by decide +kernel
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection14465 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0)
    (eq : mask 14465=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 28) (mask 14465) (mask 0) (mask 14336) (mask 14464) (mask 20) (fun f : V => mask ([0,0,314,0,1102,0,0,0,0,0,0,0,0,0] : List Nat)[f.val]!) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 14464).card+(mask 20).card+2*(mask 0).card+(mask 14336).card+(14-(mask 14465).card)=18 := by decide +kernel
  have rhs : (mask 28).card+(mask 28 \ mask 14465).card=6 := by decide +kernel
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection15232 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0)
    (eq : mask 15232=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 92) (mask 15232) (mask 2048) (mask 12544) (mask 15232) (mask 16) (fun f : V => mask ([0,0,0,0,1102,0,0,0,0,0,0,0,0,0] : List Nat)[f.val]!) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 15232).card+(mask 16).card+2*(mask 2048).card+(mask 12544).card+(14-(mask 15232).card)=20 := by decide +kernel
  have rhs : (mask 92).card+(mask 92 \ mask 15232).card=8 := by decide +kernel
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection15744 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0)
    (eq : mask 15744=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 60) (mask 15744) (mask 4096) (mask 11264) (mask 15744) (mask 32) (fun f : V => mask ([0,0,0,0,0,543,0,0,0,0,0,0,0,0] : List Nat)[f.val]!) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 15744).card+(mask 32).card+2*(mask 4096).card+(mask 11264).card+(14-(mask 15744).card)=20 := by decide +kernel
  have rhs : (mask 60).card+(mask 60 \ mask 15744).card=8 := by decide +kernel
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection16000 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0)
    (eq : mask 16000=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 60) (mask 16000) (mask 4096) (mask 11264) (mask 16000) (mask 4) (fun f : V => mask ([0,0,314,0,0,0,0,0,0,0,0,0,0,0] : List Nat)[f.val]!) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 16000).card+(mask 4).card+2*(mask 4096).card+(mask 11264).card+(14-(mask 16000).card)=20 := by decide +kernel
  have rhs : (mask 60).card+(mask 60 \ mask 16000).card=8 := by decide +kernel
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection16128 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0)
    (eq : mask 16128=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 124) (mask 16128) (mask 6144) (mask 9984) (mask 16128) (mask 8) (fun f : V => mask ([0,0,0,245,0,0,0,0,0,0,0,0,0,0] : List Nat)[f.val]!) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 16128).card+(mask 8).card+2*(mask 6144).card+(mask 9984).card+(14-(mask 16128).card)=23 := by decide +kernel
  have rhs : (mask 124).card+(mask 124 \ mask 16128).card=10 := by decide +kernel
  omega

def finalMasks : List Nat := [107, 111, 123, 543, 794, 1550, 1802, 2567, 2693, 4627, 4753, 8297, 8417, 9992, 10112, 10401, 12160, 12481, 14208, 14977]

def otherMasks : List Nat := [63, 95, 109, 119, 121, 125, 126, 229, 241, 245, 535, 542, 661, 2213, 3590, 3842, 4305, 4882, 5890, 6659, 6785, 7938, 8064, 12032, 14080, 14465, 15232, 15744, 16000, 16128]

def exactTest (m : Nat) : Bool := !possible 11 m || (decide ((mask m).card<5) || decide ((mask m).card>6) || finalMasks.contains m || otherMasks.contains m)

open PEqualNP.Outside.L_meta_9774_aux.DagTools

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem all_exact_tests_list : survivingMasks.all exactTest = true := by decide +kernel
theorem all_exact_tests (m : Fin 16384) : exactTest m.val = true := by
  by_cases ok : possible 11 m.val = true
  · have mem := all_survivors m
    simp only [survivorTest, ok, Bool.not_true, Bool.false_or, List.contains_iff_mem] at mem
    exact List.all_eq_true.mp all_exact_tests_list _ mem
  ·
    simp [exactTest,Bool.eq_false_iff.mpr ok]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem classified {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (len : D.length≤24) :
    (ineligSet 14 D).card=4 ∨ ∃ m∈finalMasks, mask m=ineligSet 14 D := by
  obtain ⟨bp,bz,lo,hi⟩ := narrow h hc len
  by_cases four : (ineligSet 14 D).card=4
  · exact Or.inl four
  right
  obtain ⟨m,enc⟩ := repr (ineligSet 14 D)
  have ok := possible_of h hc 11 m.val enc bp.le
  have t := all_exact_tests m
  simp only [exactTest,ok,Bool.not_true,Bool.false_or,Bool.or_eq_true,decide_eq_true_eq,List.contains_iff_mem] at t
  rw [enc] at t
  rcases t with ((a|b)|yes)|no
  · omega
  · omega
  · exact ⟨_,yes,enc⟩
  simp only [otherMasks,List.mem_cons,List.not_mem_nil,or_false] at no
  rcases no with c | c | c | c | c | c | c | c | c | c | c | c | c | c | c | c | c | c | c | c | c | c | c | c | c | c | c | c | c | c
  · rw [c] at enc; have := projection63 h hc bz enc; omega
  · rw [c] at enc; have := projection95 h hc bz enc; omega
  · rw [c] at enc; have := projection109 h hc bz enc; omega
  · rw [c] at enc; have := projection119 h hc bz enc; omega
  · rw [c] at enc; have := projection121 h hc bz enc; omega
  · rw [c] at enc; have := projection125 h hc bz enc; omega
  · rw [c] at enc; have := projection126 h hc bz enc; omega
  · rw [c] at enc; have := projection229 h hc bz enc; omega
  · rw [c] at enc; have := projection241 h hc bz enc; omega
  · rw [c] at enc; have := projection245 h hc bz enc; omega
  · rw [c] at enc; have := projection535 h hc bz enc; omega
  · rw [c] at enc; have := projection542 h hc bz enc; omega
  · rw [c] at enc; have := projection661 h hc bz enc; omega
  · rw [c] at enc; have := projection2213 h hc bz enc; omega
  · rw [c] at enc; have := projection3590 h hc bz enc; omega
  · rw [c] at enc; have := projection3842 h hc bz enc; omega
  · rw [c] at enc; have := projection4305 h hc bz enc; omega
  · rw [c] at enc; have := projection4882 h hc bz enc; omega
  · rw [c] at enc; have := projection5890 h hc bz enc; omega
  · rw [c] at enc; have := projection6659 h hc bz enc; omega
  · rw [c] at enc; have := projection6785 h hc bz enc; omega
  · rw [c] at enc; have := projection7938 h hc bz enc; omega
  · rw [c] at enc; have := projection8064 h hc bz enc; omega
  · rw [c] at enc; have := projection12032 h hc bz enc; omega
  · rw [c] at enc; have := projection14080 h hc bz enc; omega
  · rw [c] at enc; have := projection14465 h hc bz enc; omega
  · rw [c] at enc; have := projection15232 h hc bz enc; omega
  · rw [c] at enc; have := projection15744 h hc bz enc; omega
  · rw [c] at enc; have := projection16000 h hc bz enc; omega
  · rw [c] at enc; have := projection16128 h hc bz enc; omega

open PEqualNP.Outside.L_meta_9774_aux.DagTools

set_option maxHeartbeats 0 in
theorem exact_position {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0)
    (P : Finset V) (ind : independent P) (i x : V) (hi : i∈ineligSet 14 D) (xin : x∈P) (ix : adj i x) :
    ∃ e ∈ sem_W 14 D x, ∀ a∈P, a∈supp 14 D (src D e) ↔ adj i a := by
  obtain ⟨j,s,hj,ht,ch,ex⟩ := sem_exact_nbhd graph_ok h.1 hc P ind (sem_noempty_chain_out graph_ok h hc z hi)
  refine ⟨(j,s),sem_mem_W.mpr ⟨hj,(ex _ xin).2 ix,?_⟩,ex⟩
  intro hx
  have pure := sem_dom_pure graph_ok h.1 hc i _ (sem_chain_dom h.1 ch)
  have eq := Finset.mem_singleton.mp (pure (sem_supp_and_sub h.1 hj ht (!s) hx))
  exact graph_ok.2.1 i (eq ▸ ix)

def MissingTwo (D : Dag) (x c : V) : Prop :=
  ∃ e∈sem_W 14 D x, ∃ f∈sem_W 14 D x, e≠f ∧ c∉supp 14 D (src D e) ∧ c∉supp 14 D (src D f)

set_option maxHeartbeats 0 in
theorem two_exact {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0)
    (P : Finset V) (ind : independent P) (i j x c y : V) (hi : i∈ineligSet 14 D) (hj : j∈ineligSet 14 D)
    (g : x∈P ∧ c∈P ∧ y∈P ∧ adj i x ∧ adj j x ∧ ¬adj i c ∧ ¬adj j c ∧ adj i y ∧ ¬adj j y) : MissingTwo D x c := by
  rcases g with ⟨xp,cp,yp,ix,jx,ic,jc,iy,jy⟩
  obtain ⟨e,he,E⟩ := exact_position h hc z P ind i x hi xp ix
  obtain ⟨f,hf,F⟩ := exact_position h hc z P ind j x hj xp jx
  refine ⟨e,he,f,hf,?_,fun q => ic ((E _ cp).1 q),fun q => jc ((F _ cp).1 q)⟩
  rintro rfl; exact jy ((F _ yp).1 ((E _ yp).2 iy))

set_option maxHeartbeats 0 in
theorem exposed_exact {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0)
    (P A : Finset V) (ind : independent P) (indA : independent A) (i x c : V) (hi : i∈ineligSet 14 D)
    (g : x∈P ∧ c∈P ∧ c∈A ∧ adj i x ∧ ¬adj i c ∧ (∃ a∈A, adj x a) ∧ ∃ y∈P, y∈A ∧ adj i y) : MissingTwo D x c := by
  rcases g with ⟨xp,cp,ca,ix,ic,xa,y,yp,ya,iy⟩
  obtain ⟨e,he,E⟩ := exact_position h hc z P ind i x hi xp ix
  obtain ⟨j,s,js,_,xs,no,free⟩ := sem_exposure graph_ok h.1 hc A indA x xa
  refine ⟨e,he,(j,s),sem_mem_W.mpr ⟨js,xs,no⟩,?_,fun q => ic ((E _ cp).1 q),fun q => Finset.disjoint_left.mp free q ca⟩
  rintro rfl; exact Finset.disjoint_left.mp free ((E _ yp).2 iy) ya

def code {k : Nat} {D : Dag} {b : V → Nat} (f : Fin k ≃ ↥(residualUnits 14 D b)) (x : V) : Finset (Fin k) :=
  Finset.univ.filter (fun t => x∈supp 14 D (f t).val.1)

set_option maxHeartbeats 0 in
theorem code_diff {k : Nat} {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (b : V → Nat) (hb : PureBranch 14 D b) (f : Fin k ≃ ↥(residualUnits 14 D b)) (x c : V)
    (ne : x≠c) (elig : x∈eligSet 14 D) (miss : MissingTwo D x c)
    (together : ∃ w, x∈supp 14 D w ∧ c∈supp 14 D w) : ¬code f x ⊆ code f c := by
  intro sub
  obtain ⟨w,xw,cw⟩ := together
  have incl (u) (hu : u∈residualUnits 14 D b) (xu : x∈supp 14 D u.1) : c∈supp 14 D u.1 := by
    obtain ⟨t,eq⟩ := f.surjective ⟨u,hu⟩
    have xt : t∈code f x := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa [eq] using xu⟩
    simpa [eq] using (Finset.mem_filter.mp (sub xt)).2
  obtain ⟨e0,other⟩ := ri_gen graph_ok h hc b hb ne elig incl (w:=w) ⟨xw,cw⟩
  obtain ⟨p,hp,q,hq,pq,mp,mq⟩ := miss
  by_cases ep : p=e0
  · exact mq (other q hq (by rintro rfl; exact pq ep))
  · exact mp (other p hp ep)

set_option maxHeartbeats 0 in
theorem code_excludes {k : Nat} {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (b : V → Nat) (hb : PureBranch 14 D b) (f : Fin k ≃ ↥(residualUnits 14 D b)) (x c : V)
    (ne : x≠c) (elig : x∈eligSet 14 D) (miss : MissingTwo D x c) :
    code f x=∅ ∨ ¬code f x⊆code f c := by
  by_cases empty : code f x=∅
  · exact Or.inl empty
  right; intro sub
  obtain ⟨t,xt⟩ := Finset.nonempty_iff_ne_empty.mpr empty
  exact code_diff h hc b hb f x c ne elig miss ⟨_,(Finset.mem_filter.mp xt).2,(Finset.mem_filter.mp (sub xt)).2⟩ sub

open PEqualNP.Outside.L_meta_9774_aux.DagTools

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 200000 in
theorem code107 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11)
    (eq : mask 107=ineligSet 14 D) : False := by
  obtain ⟨b,hb⟩ := sem_exists_pureBranch graph_ok h.1 hc
  have card := card_residual h.1 b hb
  have el := inelig_card_add 14 D
  rw [←eq] at el
  have count : (mask 107).card=5 := by decide +kernel
  have res : Fintype.card ↥(residualUnits 14 D b)=2 := by rw [Fintype.card_coe]; omega
  let f := (Fintype.equivFinOfCardEq res).symm
  have miss0 := exposed_exact h hc z (mask 16256) (mask 4882) (by decide +kernel) (by decide +kernel) 0 10 12 (eq ▸ (by decide +kernel : (0:V)∈mask 107)) (by decide +kernel)
  have h0 := code_diff h hc b hb f 10 12 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (10:V)∉mask 107) hin : (10:V)∈eligSet 14 D) miss0 (share h hc (i:=5) (x:=10) (y:=12) (eq ▸ (by decide +kernel : (5:V)∈mask 107)) (by decide +kernel) (by decide +kernel))
  have miss1 := two_exact h hc z (mask 16256) (by decide +kernel) 3 6 11 10 7 (eq ▸ (by decide +kernel : (3:V)∈mask 107)) (eq ▸ (by decide +kernel : (6:V)∈mask 107)) (by decide +kernel)
  have h1 := code_excludes h hc b hb f 11 10 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (11:V)∉mask 107) hin : (11:V)∈eligSet 14 D) miss1
  have miss2 := exposed_exact h hc z (mask 16256) (mask 4627) (by decide +kernel) (by decide +kernel) 6 11 12 (eq ▸ (by decide +kernel : (6:V)∈mask 107)) (by decide +kernel)
  have h2 := code_diff h hc b hb f 11 12 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (11:V)∉mask 107) hin : (11:V)∈eligSet 14 D) miss2 (share h hc (i:=3) (x:=11) (y:=12) (eq ▸ (by decide +kernel : (3:V)∈mask 107)) (by decide +kernel) (by decide +kernel))
  have miss3 := exposed_exact h hc z (mask 16256) (mask 2567) (by decide +kernel) (by decide +kernel) 5 12 11 (eq ▸ (by decide +kernel : (5:V)∈mask 107)) (by decide +kernel)
  have h3 := code_diff h hc b hb f 12 11 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (12:V)∉mask 107) hin : (12:V)∈eligSet 14 D) miss3 (share h hc (i:=3) (x:=12) (y:=11) (eq ▸ (by decide +kernel : (3:V)∈mask 107)) (by decide +kernel) (by decide +kernel))
  have impossible : ∀ a10 a11 a12 : Finset (Fin 2), (¬ a10 ⊆ a12) → (a11=∅ ∨ ¬a11⊆a10) → (¬ a11 ⊆ a12) → (¬ a12 ⊆ a11) → False := by decide +kernel
  exact impossible (code f 10) (code f 11) (code f 12) h0 h1 h2 h3

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 200000 in
theorem code111 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11)
    (eq : mask 111=ineligSet 14 D) : False := by
  obtain ⟨b,hb⟩ := sem_exists_pureBranch graph_ok h.1 hc
  have card := card_residual h.1 b hb
  have el := inelig_card_add 14 D
  rw [←eq] at el
  have count : (mask 111).card=6 := by decide +kernel
  have res : Fintype.card ↥(residualUnits 14 D b)=3 := by rw [Fintype.card_coe]; omega
  let f := (Fintype.equivFinOfCardEq res).symm
  have miss0 := exposed_exact h hc z (mask 16256) (mask 4882) (by decide +kernel) (by decide +kernel) 0 10 12 (eq ▸ (by decide +kernel : (0:V)∈mask 111)) (by decide +kernel)
  have h0 := code_diff h hc b hb f 10 12 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (10:V)∉mask 111) hin : (10:V)∈eligSet 14 D) miss0 (share h hc (i:=5) (x:=10) (y:=12) (eq ▸ (by decide +kernel : (5:V)∈mask 111)) (by decide +kernel) (by decide +kernel))
  have miss1 := two_exact h hc z (mask 16256) (by decide +kernel) 0 5 10 13 8 (eq ▸ (by decide +kernel : (0:V)∈mask 111)) (eq ▸ (by decide +kernel : (5:V)∈mask 111)) (by decide +kernel)
  have h1 := code_excludes h hc b hb f 10 13 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (10:V)∉mask 111) hin : (10:V)∈eligSet 14 D) miss1
  have miss2 := two_exact h hc z (mask 16256) (by decide +kernel) 3 6 11 10 7 (eq ▸ (by decide +kernel : (3:V)∈mask 111)) (eq ▸ (by decide +kernel : (6:V)∈mask 111)) (by decide +kernel)
  have h2 := code_excludes h hc b hb f 11 10 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (11:V)∉mask 111) hin : (11:V)∈eligSet 14 D) miss2
  have miss3 := exposed_exact h hc z (mask 16256) (mask 4627) (by decide +kernel) (by decide +kernel) 6 11 12 (eq ▸ (by decide +kernel : (6:V)∈mask 111)) (by decide +kernel)
  have h3 := code_diff h hc b hb f 11 12 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (11:V)∉mask 111) hin : (11:V)∈eligSet 14 D) miss3 (share h hc (i:=3) (x:=11) (y:=12) (eq ▸ (by decide +kernel : (3:V)∈mask 111)) (by decide +kernel) (by decide +kernel))
  have miss4 := two_exact h hc z (mask 16256) (by decide +kernel) 2 3 12 10 8 (eq ▸ (by decide +kernel : (2:V)∈mask 111)) (eq ▸ (by decide +kernel : (3:V)∈mask 111)) (by decide +kernel)
  have h4 := code_diff h hc b hb f 12 10 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (12:V)∉mask 111) hin : (12:V)∈eligSet 14 D) miss4 (share h hc (i:=5) (x:=12) (y:=10) (eq ▸ (by decide +kernel : (5:V)∈mask 111)) (by decide +kernel) (by decide +kernel))
  have miss5 := two_exact h hc z (mask 16256) (by decide +kernel) 2 5 12 11 8 (eq ▸ (by decide +kernel : (2:V)∈mask 111)) (eq ▸ (by decide +kernel : (5:V)∈mask 111)) (by decide +kernel)
  have h5 := code_diff h hc b hb f 12 11 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (12:V)∉mask 111) hin : (12:V)∈eligSet 14 D) miss5 (share h hc (i:=3) (x:=12) (y:=11) (eq ▸ (by decide +kernel : (3:V)∈mask 111)) (by decide +kernel) (by decide +kernel))
  have miss6 := two_exact h hc z (mask 16256) (by decide +kernel) 3 5 12 13 7 (eq ▸ (by decide +kernel : (3:V)∈mask 111)) (eq ▸ (by decide +kernel : (5:V)∈mask 111)) (by decide +kernel)
  have h6 := code_diff h hc b hb f 12 13 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (12:V)∉mask 111) hin : (12:V)∈eligSet 14 D) miss6 (share h hc (i:=2) (x:=12) (y:=13) (eq ▸ (by decide +kernel : (2:V)∈mask 111)) (by decide +kernel) (by decide +kernel))
  have miss7 := two_exact h hc z (mask 16256) (by decide +kernel) 1 2 13 11 7 (eq ▸ (by decide +kernel : (1:V)∈mask 111)) (eq ▸ (by decide +kernel : (2:V)∈mask 111)) (by decide +kernel)
  have h7 := code_excludes h hc b hb f 13 11 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (13:V)∉mask 111) hin : (13:V)∈eligSet 14 D) miss7
  have miss8 := exposed_exact h hc z (mask 16256) (mask 4305) (by decide +kernel) (by decide +kernel) 1 13 12 (eq ▸ (by decide +kernel : (1:V)∈mask 111)) (by decide +kernel)
  have h8 := code_diff h hc b hb f 13 12 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (13:V)∉mask 111) hin : (13:V)∈eligSet 14 D) miss8 (share h hc (i:=2) (x:=13) (y:=12) (eq ▸ (by decide +kernel : (2:V)∈mask 111)) (by decide +kernel) (by decide +kernel))
  have impossible : ∀ a10 a11 a12 a13 : Finset (Fin 3), (¬ a10 ⊆ a12) → (a10=∅ ∨ ¬a10⊆a13) → (a11=∅ ∨ ¬a11⊆a10) → (¬ a11 ⊆ a12) → (¬ a12 ⊆ a10) → (¬ a12 ⊆ a11) → (¬ a12 ⊆ a13) → (a13=∅ ∨ ¬a13⊆a11) → (¬ a13 ⊆ a12) → False := by decide +kernel
  exact impossible (code f 10) (code f 11) (code f 12) (code f 13) h0 h1 h2 h3 h4 h5 h6 h7 h8

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 200000 in
theorem code543 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11)
    (eq : mask 543=ineligSet 14 D) : False := by
  obtain ⟨b,hb⟩ := sem_exists_pureBranch graph_ok h.1 hc
  have card := card_residual h.1 b hb
  have el := inelig_card_add 14 D
  rw [←eq] at el
  have count : (mask 543).card=6 := by decide +kernel
  have res : Fintype.card ↥(residualUnits 14 D b)=3 := by rw [Fintype.card_coe]; omega
  let f := (Fintype.equivFinOfCardEq res).symm
  have miss0 := two_exact h hc z (mask 16256) (by decide +kernel) 0 4 10 12 8 (eq ▸ (by decide +kernel : (0:V)∈mask 543)) (eq ▸ (by decide +kernel : (4:V)∈mask 543)) (by decide +kernel)
  have h0 := code_excludes h hc b hb f 10 12 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (10:V)∉mask 543) hin : (10:V)∈eligSet 14 D) miss0
  have miss1 := exposed_exact h hc z (mask 16256) (mask 8488) (by decide +kernel) (by decide +kernel) 0 10 13 (eq ▸ (by decide +kernel : (0:V)∈mask 543)) (by decide +kernel)
  have h1 := code_diff h hc b hb f 10 13 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (10:V)∉mask 543) hin : (10:V)∈eligSet 14 D) miss1 (share h hc (i:=4) (x:=10) (y:=13) (eq ▸ (by decide +kernel : (4:V)∈mask 543)) (by decide +kernel) (by decide +kernel))
  have miss2 := exposed_exact h hc z (mask 16256) (mask 1220) (by decide +kernel) (by decide +kernel) 3 11 10 (eq ▸ (by decide +kernel : (3:V)∈mask 543)) (by decide +kernel)
  have h2 := code_diff h hc b hb f 11 10 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (11:V)∉mask 543) hin : (11:V)∈eligSet 14 D) miss2 (share h hc (i:=4) (x:=11) (y:=10) (eq ▸ (by decide +kernel : (4:V)∈mask 543)) (by decide +kernel) (by decide +kernel))
  have miss3 := exposed_exact h hc z (mask 16256) (mask 8417) (by decide +kernel) (by decide +kernel) 3 11 13 (eq ▸ (by decide +kernel : (3:V)∈mask 543)) (by decide +kernel)
  have h3 := code_diff h hc b hb f 11 13 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (11:V)∉mask 543) hin : (11:V)∈eligSet 14 D) miss3 (share h hc (i:=4) (x:=11) (y:=13) (eq ▸ (by decide +kernel : (4:V)∈mask 543)) (by decide +kernel) (by decide +kernel))
  have miss4 := exposed_exact h hc z (mask 16256) (mask 2338) (by decide +kernel) (by decide +kernel) 2 12 11 (eq ▸ (by decide +kernel : (2:V)∈mask 543)) (by decide +kernel)
  have h4 := code_diff h hc b hb f 12 11 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (12:V)∉mask 543) hin : (12:V)∈eligSet 14 D) miss4 (share h hc (i:=3) (x:=12) (y:=11) (eq ▸ (by decide +kernel : (3:V)∈mask 543)) (by decide +kernel) (by decide +kernel))
  have miss5 := exposed_exact h hc z (mask 16256) (mask 8417) (by decide +kernel) (by decide +kernel) 3 12 13 (eq ▸ (by decide +kernel : (3:V)∈mask 543)) (by decide +kernel)
  have h5 := code_diff h hc b hb f 12 13 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (12:V)∉mask 543) hin : (12:V)∈eligSet 14 D) miss5 (share h hc (i:=2) (x:=12) (y:=13) (eq ▸ (by decide +kernel : (2:V)∈mask 543)) (by decide +kernel) (by decide +kernel))
  have miss6 := two_exact h hc z (mask 16256) (by decide +kernel) 1 2 13 10 7 (eq ▸ (by decide +kernel : (1:V)∈mask 543)) (eq ▸ (by decide +kernel : (2:V)∈mask 543)) (by decide +kernel)
  have h6 := code_diff h hc b hb f 13 10 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (13:V)∉mask 543) hin : (13:V)∈eligSet 14 D) miss6 (share h hc (i:=4) (x:=13) (y:=10) (eq ▸ (by decide +kernel : (4:V)∈mask 543)) (by decide +kernel) (by decide +kernel))
  have miss7 := two_exact h hc z (mask 16256) (by decide +kernel) 1 2 13 11 7 (eq ▸ (by decide +kernel : (1:V)∈mask 543)) (eq ▸ (by decide +kernel : (2:V)∈mask 543)) (by decide +kernel)
  have h7 := code_diff h hc b hb f 13 11 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (13:V)∉mask 543) hin : (13:V)∈eligSet 14 D) miss7 (share h hc (i:=4) (x:=13) (y:=11) (eq ▸ (by decide +kernel : (4:V)∈mask 543)) (by decide +kernel) (by decide +kernel))
  have miss8 := two_exact h hc z (mask 16256) (by decide +kernel) 1 4 13 12 7 (eq ▸ (by decide +kernel : (1:V)∈mask 543)) (eq ▸ (by decide +kernel : (4:V)∈mask 543)) (by decide +kernel)
  have h8 := code_diff h hc b hb f 13 12 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (13:V)∉mask 543) hin : (13:V)∈eligSet 14 D) miss8 (share h hc (i:=2) (x:=13) (y:=12) (eq ▸ (by decide +kernel : (2:V)∈mask 543)) (by decide +kernel) (by decide +kernel))
  have impossible : ∀ a10 a11 a12 a13 : Finset (Fin 3), (a10=∅ ∨ ¬a10⊆a12) → (¬ a10 ⊆ a13) → (¬ a11 ⊆ a10) → (¬ a11 ⊆ a13) → (¬ a12 ⊆ a11) → (¬ a12 ⊆ a13) → (¬ a13 ⊆ a10) → (¬ a13 ⊆ a11) → (¬ a13 ⊆ a12) → False := by decide +kernel
  exact impossible (code f 10) (code f 11) (code f 12) (code f 13) h0 h1 h2 h3 h4 h5 h6 h7 h8

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 200000 in
theorem code8297 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11)
    (eq : mask 8297=ineligSet 14 D) : False := by
  obtain ⟨b,hb⟩ := sem_exists_pureBranch graph_ok h.1 hc
  have card := card_residual h.1 b hb
  have el := inelig_card_add 14 D
  rw [←eq] at el
  have count : (mask 8297).card=5 := by decide +kernel
  have res : Fintype.card ↥(residualUnits 14 D b)=2 := by rw [Fintype.card_coe]; omega
  let f := (Fintype.equivFinOfCardEq res).symm
  have miss0 := exposed_exact h hc z (mask 16256) (mask 4882) (by decide +kernel) (by decide +kernel) 0 10 12 (eq ▸ (by decide +kernel : (0:V)∈mask 8297)) (by decide +kernel)
  have h0 := code_diff h hc b hb f 10 12 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (10:V)∉mask 8297) hin : (10:V)∈eligSet 14 D) miss0 (share h hc (i:=5) (x:=10) (y:=12) (eq ▸ (by decide +kernel : (5:V)∈mask 8297)) (by decide +kernel) (by decide +kernel))
  have miss1 := two_exact h hc z (mask 16256) (by decide +kernel) 3 6 11 10 7 (eq ▸ (by decide +kernel : (3:V)∈mask 8297)) (eq ▸ (by decide +kernel : (6:V)∈mask 8297)) (by decide +kernel)
  have h1 := code_excludes h hc b hb f 11 10 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (11:V)∉mask 8297) hin : (11:V)∈eligSet 14 D) miss1
  have miss2 := exposed_exact h hc z (mask 16256) (mask 4627) (by decide +kernel) (by decide +kernel) 6 11 12 (eq ▸ (by decide +kernel : (6:V)∈mask 8297)) (by decide +kernel)
  have h2 := code_diff h hc b hb f 11 12 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (11:V)∉mask 8297) hin : (11:V)∈eligSet 14 D) miss2 (share h hc (i:=3) (x:=11) (y:=12) (eq ▸ (by decide +kernel : (3:V)∈mask 8297)) (by decide +kernel) (by decide +kernel))
  have miss3 := exposed_exact h hc z (mask 16256) (mask 2567) (by decide +kernel) (by decide +kernel) 5 12 11 (eq ▸ (by decide +kernel : (5:V)∈mask 8297)) (by decide +kernel)
  have h3 := code_diff h hc b hb f 12 11 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (12:V)∉mask 8297) hin : (12:V)∈eligSet 14 D) miss3 (share h hc (i:=3) (x:=12) (y:=11) (eq ▸ (by decide +kernel : (3:V)∈mask 8297)) (by decide +kernel) (by decide +kernel))
  have impossible : ∀ a10 a11 a12 : Finset (Fin 2), (¬ a10 ⊆ a12) → (a11=∅ ∨ ¬a11⊆a10) → (¬ a11 ⊆ a12) → (¬ a12 ⊆ a11) → False := by decide +kernel
  exact impossible (code f 10) (code f 11) (code f 12) h0 h1 h2 h3

namespace Resolution

abbrev Lit := Nat × Bool

abbrev Clause := List Lit

def neg (l : Lit) : Lit := (l.1,!l.2)

def Yes (v : Nat → Bool) (l : Lit) := v l.1 = l.2

def Holds (v : Nat → Bool) (c : Clause) := ∃ l∈c, Yes v l

def Valid (v : Nat → Bool) (F : Array Clause) := ∀ c∈F, Holds v c

theorem neg_iff (v : Nat → Bool) (l : Lit) : Yes v (neg l) ↔ ¬Yes v l := by
  simp only [Yes,neg]
  cases v l.1 <;> cases l.2 <;> decide
end Resolution

namespace Resolution

def key (l : Lit) : Nat := 2*l.1+l.2.toNat

theorem key_injective : Function.Injective key := by
  rintro ⟨n,b⟩ ⟨m,c⟩ eq
  cases b <;> cases c <;> simp [key,Bool.toNat] at eq ⊢ <;> omega

def insertBit (a : Nat) (l : Lit) := a ||| (2 ^ key l)

def initial : Clause → Nat
  | [] => 0
  | l::ls => insertBit (initial ls) (neg l)

theorem get_insert (a : Nat) (p x : Lit) :
    (insertBit a p).testBit (key x)=true ↔ a.testBit (key x)=true ∨ p=x := by
  simp [insertBit,Nat.testBit_two_pow,key_injective.eq_iff]

theorem get_initial {c : Clause} {x : Lit} (h : (initial c).testBit (key x)=true) :
    ∃ l∈c, neg l=x := by
  induction c with
  | nil => simp [initial] at h
  | cons l ls ih =>
    rcases (get_insert _ _ _).mp h with h|e
    · obtain ⟨t,ht,eq⟩ := ih h; exact ⟨t,List.mem_cons_of_mem _ ht,eq⟩
    · exact ⟨l,List.mem_cons_self,e⟩

def allowed (a : Nat) (p : Option Lit) (c : Clause) : Bool :=
  c.all fun l => some l == p || a.testBit (key (neg l))

theorem allowed_ok {v a p c} (sat : Holds v c) (forced : ∀ l, a.testBit (key l)=true → Yes v l)
    (ok : allowed a p c=true) : ∃ l, some l=p ∧ Yes v l := by
  obtain ⟨l,hl,hv⟩ := sat
  have bound := (List.all_eq_true.mp ok) l hl
  simp only [Bool.or_eq_true,beq_iff_eq] at bound
  rcases bound with eq|deny
  · exact ⟨l,eq,hv⟩
  · exact ((neg_iff v l).mp (forced _ deny) hv).elim
end Resolution

open PEqualNP.Outside.L_meta_9774_aux.DagTools PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def auto (σ : Equiv.Perm V) := ∀ i j, adj (σ i) (σ j) ↔ adj i j

set_option maxHeartbeats 0 in
theorem rename {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (σ : Equiv.Perm V) (a : auto σ) :
    sem_Comp 14 adj (relabel σ D) := by
  intro x
  rw [relabel_out σ h.1 h.2.2,hc]
  constructor
  · rintro ⟨u,v,uv,hu,hv⟩; exact ⟨σ u,σ v,(a _ _).2 uv,hu,hv⟩
  · rintro ⟨u,v,uv,hu,hv⟩
    refine ⟨σ.symm u,σ.symm v,(a _ _).1 (by simpa using uv),by simpa using hu,by simpa using hv⟩

def permFn0 (v : V) : V := ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] : List V)[v.val]!

def permFn1 (v : V) : V := ([0, 1, 4, 3, 2, 6, 5, 7, 10, 9, 8, 12, 11, 13] : List V)[v.val]!

def permFn2 (v : V) : V := ([9, 7, 11, 13, 12, 10, 8, 1, 6, 0, 5, 2, 4, 3] : List V)[v.val]!

def permFn3 (v : V) : V := ([9, 7, 12, 13, 11, 8, 10, 1, 5, 0, 6, 4, 2, 3] : List V)[v.val]!

def graphPerm0 : Equiv.Perm V where
  toFun := permFn0
  invFun := permFn0
  left_inv := by decide +kernel
  right_inv := by decide +kernel

set_option maxHeartbeats 0 in
theorem auto0 : auto graphPerm0 := by unfold auto; decide +kernel

def graphPerm1 : Equiv.Perm V where
  toFun := permFn1
  invFun := permFn1
  left_inv := by decide +kernel
  right_inv := by decide +kernel

set_option maxHeartbeats 0 in
theorem auto1 : auto graphPerm1 := by unfold auto; decide +kernel

def graphPerm2 : Equiv.Perm V where
  toFun := permFn2
  invFun := permFn2
  left_inv := by decide +kernel
  right_inv := by decide +kernel

set_option maxHeartbeats 0 in
theorem auto2 : auto graphPerm2 := by unfold auto; decide +kernel

def graphPerm3 : Equiv.Perm V where
  toFun := permFn3
  invFun := permFn3
  left_inv := by decide +kernel
  right_inv := by decide +kernel

set_option maxHeartbeats 0 in
theorem auto3 : auto graphPerm3 := by unfold auto; decide +kernel

set_option maxHeartbeats 0 in
theorem move_case {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (len : D.length≤24)
    (i j : Nat) (eq : mask i=ineligSet 14 D) (σ : Equiv.Perm V) (a : auto σ) (moved : (mask i).image σ=mask j) :
    ∃ E : Dag, StrictLive 14 E ∧ sem_Comp 14 adj E ∧ E.length≤24 ∧ ineligSet 14 E=mask j := by
  refine ⟨relabel σ D,relabel_strictLive σ h,rename h hc σ a,by simpa [relabel_length] using len,?_⟩
  rw [relabel_ineligSet σ h.1,←eq,moved]

open PEqualNP.Outside.L_meta_9774_aux.DagTools PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def fourMasks : List Nat := [177, 197, 298, 432, 523, 534, 645, 657, 660, 778, 912, 1098, 1220, 1290, 1546, 1668, 2083, 2338, 2563, 2818, 4163, 4611, 5186, 5634, 6147, 6273, 8353, 8385, 8416, 8608, 8713, 8833, 9408]

def fourTest (m : Nat) := !possible 11 m || decide ((mask m).card≠4) || fourMasks.contains m

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem all_four_tests_list : survivingMasks.all fourTest = true := by decide +kernel
theorem all_four_tests (m : Fin 16384) : fourTest m.val = true := by
  by_cases ok : possible 11 m.val = true
  · have mem := all_survivors m
    simp only [survivorTest, ok, Bool.not_true, Bool.false_or, List.contains_iff_mem] at mem
    exact List.all_eq_true.mp all_four_tests_list _ mem
  ·
    simp [fourTest,Bool.eq_false_iff.mpr ok]


-- Record where a pair of adjacent inputs first meets at an AND gate.
namespace Compact
open PEqualNP.Outside.L_meta_9774_aux.DagTools

def countAt (D : Dag) (x : V) := (sem_W 14 D x).card

def cap (k I : Nat) (x : V) := if x∈mask I then 1 else 2+k

def Together (D : Dag) (x c : V) := ∃ w, x∈supp 14 D w ∧ c∈supp 14 D w

def SLabel (D : Dag) (p : Slot) (x : V) := x∈supp 14 D (src D p)

structure Layout (D : Dag) (k I : Nat) where
  wire : V → Nat → Slot
  edge : EdgeIdx → Slot
  reader : Bool → EdgeIdx → Nat
  branch : V → Nat
  order : Fin k ≃ ↥(residualUnits 14 D branch)
  pure : PureBranch 14 D branch
  limit : ∀ x, countAt D x ≤ cap k I x
  member : ∀ x j, wire x j ∈ sem_W 14 D x
  inject : ∀ x j k, j<countAt D x → k<countAt D x → wire x j=wire x k → j=k
  covers : ∀ x e, e∈sem_W 14 D x → ∃ j<countAt D x, wire x j=e
  reader_live : ∀ s e, reader s e < countAt D (endpoint s e)
  read : ∀ s e, wire (endpoint s e) (reader s e)=flip s (edge e)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem construct_layout {k I : Nat} {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (bp : Bplus 14 D=11) (eq : mask I=ineligSet 14 D) (sizeI : (mask I).card=k+3) :
    Nonempty (Layout D k I) := by
  classical
  obtain ⟨b,hb⟩ := sem_exists_pureBranch graph_ok h.1 hc
  have el := inelig_card_add 14 D
  have diff := card_residual h.1 b hb
  rw [←eq,sizeI] at el
  have count : Fintype.card ↥(residualUnits 14 D b)=k := by rw [Fintype.card_coe]; omega
  let f := (Fintype.equivFinOfCardEq count).symm
  have lim (x : V) : countAt D x ≤ cap k I x := by
    unfold cap countAt
    split
    · rename_i hx
      obtain ⟨p,_,_,_,_,_,sw,_⟩ := sem_inelig_consumer graph_ok h hc (eq ▸ hx)
      change sem_W 14 D x={p} at sw
      rw [sw,Finset.card_singleton]
    · have one := Finset.card_le_card (Finset.inter_subset_left : ({x}:Finset V)∩eligSet 14 D ⊆ {x})
      have two := Finset.card_filter_le (residualUnits 14 D b) (fun u => x∈supp 14 D u.1)
      have cc := sem_code_count graph_ok h hc b hb x
      simp only [Finset.card_singleton] at one
      omega
  have has (x : V) : 0<countAt D x := by
    obtain ⟨y,xy,_⟩ := graph_ok.2.2.2 x x
    obtain ⟨p,hp,_⟩ := sem_edge_slots graph_ok h.1 hc xy
    exact Finset.card_pos.mpr ⟨p,hp⟩
  let enum (x : V) : Fin (countAt D x) ≃ ↥(sem_W 14 D x) :=
    (Fintype.equivFinOfCardEq (by simp [countAt])).symm
  let atIdx (x : V) (j : Nat) : Fin (countAt D x) := if hj : j<countAt D x then ⟨j,hj⟩ else ⟨0,has x⟩
  let w (x : V) (j : Nat) := ((enum x) (atIdx x j)).val
  have onto (x : V) (e) (he : e∈sem_W 14 D x) : ∃ j<countAt D x, w x j=e := by
    obtain ⟨i,hf⟩ := (enum x).surjective ⟨e,he⟩
    exact ⟨i.val,i.isLt,by simpa [w,atIdx,i.isLt] using congrArg Subtype.val hf⟩
  obtain ⟨P,hp⟩ := get_slots h hc
  choose readAt spec using (fun s e => onto (endpoint s e) _ (hp s e))
  refine ⟨⟨w,P,readAt,b,f,hb,lim,fun x j => ((enum x) (atIdx x j)).property,?_,onto,fun s e => (spec s e).1,fun s e => (spec s e).2⟩⟩
  intro x j k hj hk same
  have e := (enum x).injective (Subtype.ext same)
  simpa [atIdx,hj,hk] using congrArg Fin.val e
namespace Layout
variable {D : Dag} {k I : Nat} (Z : Layout D k I)

def lab (x : V) (j : Nat) (c : V) := SLabel D (Z.wire x j) c

def edgeLabelAt (s : Bool) (e : EdgeIdx) (c : V) := SLabel D (flip s (Z.edge e)) c

def res (s : Fin k) (x : V) := x∈supp 14 D (Z.order s).val.1

def Live (_Z : Layout D k I) (x : V) (j : Nat) := j<countAt D x

def avoid (x : V) (A : Nat) (j : Nat) := Z.Live x j ∧ ∀ c∈mask A, ¬Z.lab x j c

def see (x i : V) (P : Nat) (j : Nat) := Z.Live x j ∧ ∀ c∈mask P, Z.lab x j c ↔ adj i c

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem expose (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (x : V) (A : Nat) (ind : independent (mask A))
    (ne : ∃ a∈mask A, adj x a) : ∃ j<cap k I x, Z.avoid x A j := by
  obtain ⟨g,s,hl,_,xl,no,dis⟩ := sem_exposure graph_ok h.1 hc (mask A) ind x ne
  obtain ⟨j,live,eq⟩ := Z.covers x (g,s) (sem_mem_W.mpr ⟨hl,xl,no⟩)
  exact ⟨j,lt_of_lt_of_le live (Z.limit x),live,fun c cin (hh : SLabel D (Z.wire x j) c) =>
    Finset.disjoint_left.mp dis (eq ▸ hh) cin⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem exact_slot (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (zero : Bzero 14 D=0)
    (eq : mask I=ineligSet 14 D) (x i : V) (P : Nat) (ind : independent (mask P))
    (geom : i∈mask I ∧ x∈mask P ∧ adj i x) : ∃ j<cap k I x, Z.see x i P j := by
  obtain ⟨e,he,hw⟩ := exact_position h hc zero (mask P) ind i x (eq ▸ geom.1) geom.2.1 geom.2.2
  obtain ⟨j,live,same⟩ := Z.covers x e he
  exact ⟨j,lt_of_lt_of_le live (Z.limit x),live,fun c inc => by simpa [lab,SLabel,same] using hw c inc⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ri_slots (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (x c : V) (neq : x≠c) (elig : x∈eligSet 14 D)
    {j l : Nat} (lt : j<l) (live : Z.Live x l) (com : Together D x c) :
    Z.lab x j c ∨ Z.lab x l c ∨ ∃ t : Fin k, Z.res t x ∧ ¬Z.res t c := by
  by_contra! bad
  rcases bad with ⟨mj,ml,rest⟩
  have hj : j<countAt D x := lt_trans lt live
  have miss : MissingTwo D x c := ⟨_,Z.member _ _,_,Z.member _ _,fun e => (Nat.ne_of_lt lt) (Z.inject x j l hj live e),mj,ml⟩
  have no := code_diff h hc Z.branch Z.pure Z.order x c neq elig miss com
  apply no
  intro t ht
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,rest t (Finset.mem_filter.mp ht).2⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem size_code (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (x : V) :
    countAt D x ≤ 2 + (code Z.order x).card := by
  classical
  have image : (code Z.order x).image (fun t => (Z.order t).val) = (residualUnits 14 D Z.branch).filter (fun u => x∈supp 14 D u.1) := by
    ext u
    constructor
    · intro hu; obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hu
      exact Finset.mem_filter.mpr ⟨(Z.order t).property,(Finset.mem_filter.mp ht).2⟩
    · intro hu
      obtain ⟨base,supp⟩ := Finset.mem_filter.mp hu
      obtain ⟨t,e⟩ := Z.order.surjective ⟨u,base⟩
      exact Finset.mem_image.mpr ⟨t,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa [e] using supp⟩,congrArg Subtype.val e⟩
  have cc := sem_code_count graph_ok h hc Z.branch Z.pure x
  have one := Finset.card_le_card (Finset.inter_subset_left : ({x}:Finset V)∩eligSet 14 D ⊆ {x})
  simp only [Finset.card_singleton] at one
  rw [←image,Finset.card_image_of_injective _ (fun _ _ e => Z.order.injective (Subtype.ext e))] at cc
  unfold countAt
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem mem_code (x : V) (s : Fin k) : s∈code Z.order x ↔ Z.res s x := by simp [code,res]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem some_code (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (x : V) (live : Z.Live x 2) :
    ∃ t, Z.res t x := by
  have sz := Z.size_code h hc x
  obtain ⟨t,mem⟩ := Finset.card_pos.mp (show 0<(code Z.order x).card by change 2<countAt D x at live; omega)
  exact ⟨t,(Z.mem_code _ _).mp mem⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem all_code (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (x : V) (live : Z.Live x (1+k)) :
    ∀ t, Z.res t x := by
  have sz := Z.size_code h hc x
  change 1+k<countAt D x at live
  have full : code Z.order x=Finset.univ := Finset.eq_univ_of_card _ (by simp; have := Finset.card_le_univ (code Z.order x); simp at this; omega)
  exact fun t => (Z.mem_code x t).1 (full ▸ Finset.mem_univ t)
end Layout
end Compact

namespace Compact
open PEqualNP.Outside.L_meta_9774_aux.DagTools Resolution

theorem together_comm (D : Dag) (x c : V) : Together D x c ↔ Together D c x := by
  simp only [Together,and_comm]
namespace Layout
variable {D : Dag} {k I : Nat} (Z : Layout D k I)

theorem selfLab (x : V) (j : Nat) : Z.lab x j x := (sem_mem_W.mp (Z.member x j)).2.1

theorem commonLab (x c : V) (j : Nat) (h : Z.lab x j c) : Together D x c :=
  ⟨_,Z.selfLab x j,h⟩

theorem commonRes (s : Fin k) (x c : V) (u : Z.res s x) (v : Z.res s c) : Together D x c := ⟨_,u,v⟩

theorem readerLab (s : Bool) (e : EdgeIdx) (j : Nat) (c : V) (x : V) (ep : endpoint s e=x)
    (q : Z.reader s e=j) : Z.lab x j c ↔ Z.edgeLabelAt s e c := by
  subst x j
  unfold lab edgeLabelAt
  rw [Z.read]

theorem readerEq (s : Bool) (i k : EdgeIdx) (j : Nat) (ep : endpoint s i=endpoint s k)
    (qi : Z.reader s i=j) (qk : Z.reader s k=j) : Z.edge i=Z.edge k := by
  apply flip_inj s
  rw [←Z.read,←Z.read,qi,qk,ep]

theorem boundReader (s : Bool) (e : EdgeIdx) : Z.reader s e<cap k I (endpoint s e) :=
  lt_of_lt_of_le (Z.reader_live s e) (Z.limit _)

theorem eqLab (s : Bool) (i j : EdgeIdx) (c : V) (eq : Z.edge i=Z.edge j) : Z.edgeLabelAt s i c ↔ Z.edgeLabelAt s j c := by
  simp [edgeLabelAt,eq]
end Layout
end Compact

namespace Compact
open PEqualNP.Outside.L_meta_9774_aux.DagTools

inductive Fact where
  | live (x : V) (j : Nat)
  | lab (x : V) (j : Nat) (c : V)
  | res (t : Nat) (x : V)
  | common (x c : V)
  | gate (e f : EdgeIdx)
  | reader (s : Bool) (e : EdgeIdx) (j : Nat)
  | es (s : Bool) (e : EdgeIdx) (c : V)
  | avoid (x : V) (a j : Nat)
  | see (x i : V) (p j : Nat)
  | diff (t : Nat) (x c : V)
  deriving DecidableEq, Inhabited

abbrev FactClause := List (Fact × Bool)

def rAt {D : Dag} {k I : Nat} (Z : Layout D k I) (s : Nat) (x : V) :=
  ∃ t : Fin k, t.val=s ∧ Z.res t x

def evalFact {D : Dag} {k I : Nat} (Z : Layout D k I) : Fact → Prop
  | .live x j => Z.Live x j
  | .lab x j c => Z.lab x j c
  | .res t x => rAt Z t x
  | .common x c => Together D x c
  | .gate i j => Z.edge i=Z.edge j
  | .reader s e j => Z.reader s e=j
  | .es s e c => Z.edgeLabelAt s e c
  | .avoid x a j => Z.avoid x a j
  | .see x i p j => Z.see x i p j
  | .diff t x c => rAt Z t x ∧ ¬rAt Z t c

def EvalClause {D : Dag} {k I : Nat} (Z : Layout D k I) (c : FactClause) : Prop :=
  ∃ e∈c, if e.2 then evalFact Z e.1 else ¬evalFact Z e.1

abbrev pos (a : Fact) : Fact × Bool := (a,true)

abbrev negF (a : Fact) : Fact × Bool := (a,false)

def anyRange (n : Nat) (p : Nat → Fact) : FactClause := (List.range n).map (fun j => pos (p j))

theorem pos_iff {D : Dag} {k I} (Z : Layout D k I) (a : Fact) (c : FactClause) :
    EvalClause Z (pos a::c) ↔ evalFact Z a ∨ EvalClause Z c := by
  simp [EvalClause,List.mem_cons,exists_or,or_and_right]

theorem neg_iff {D : Dag} {k I} (Z : Layout D k I) (a : Fact) (c : FactClause) :
    EvalClause Z (negF a::c) ↔ ¬evalFact Z a ∨ EvalClause Z c := by
  simp [EvalClause,List.mem_cons,exists_or,or_and_right]

theorem none_iff {D : Dag} {k I} (Z : Layout D k I) : ¬EvalClause Z [] := by simp [EvalClause]

theorem range_iff {D : Dag} {k I} (Z : Layout D k I) (n : Nat) (p : Nat → Fact) :
    EvalClause Z (anyRange n p) ↔ ∃ j<n, evalFact Z (p j) := by
  simp [EvalClause,anyRange]

theorem atRes {D : Dag} {k I} (Z : Layout D k I) (t : Fin k) (x : V) : rAt Z t.val x ↔ Z.res t x := by
  constructor
  · rintro ⟨s,e,h⟩; exact (Fin.ext e : s=t) ▸ h
  · exact fun h => ⟨t,rfl,h⟩

inductive Scheme where
  | self (x : V) (j : Nat)
  | earlier (x : V) (j : Nat)
  | labCommon (x c : V) (j : Nat)
  | someRes (x : V)
  | allRes (x : V) (t : Nat)
  | exposure (x : V) (a : Nat)
  | exactAt (x i : V) (p : Nat)
  | avoidLive (x : V) (a j : Nat)
  | seeLive (x i : V) (p j : Nat)
  | avoidNot (x c : V) (a j : Nat)
  | seeLab (x i c : V) (p j : Nat)
  | diffX (t : Nat) (x c : V)
  | diffC (t : Nat) (x c : V)
  | adjacentCommon (x c i : V)
  | resCommon (x c : V) (t : Nat)
  | residual (x c : V) (j l : Nat)
  | readerAny (s : Bool) (e : EdgeIdx)
  | readerLive (s : Bool) (e : EdgeIdx) (j : Nat)
  | readerLab (s : Bool) (e : EdgeIdx) (j : Nat) (c : V) (forward : Bool)
  | eqLab (s : Bool) (e f : EdgeIdx) (c : V) (forward : Bool)
  | gateEq (s : Bool) (e f : EdgeIdx) (j : Nat)
  deriving Inhabited

def commonF (x c : V) := Fact.common (min x c) (max x c)

theorem commonF_iff {D : Dag} {k I} (Z : Layout D k I) (x c : V) : evalFact Z (commonF x c) ↔ Together D x c := by
  rcases le_total x c with le|le
  · simp [commonF,min_eq_left le,max_eq_right le,evalFact]
  · simp [commonF,min_eq_right le,max_eq_left le,evalFact,together_comm D c x]

def enabled (k I : Nat) : Scheme → Bool
  | .allRes _ t => decide (t<k)
  | .exposure x a => decide (independent (mask a) ∧ ∃ v∈mask a, adj x v)
  | .exactAt x i p => decide (independent (mask p) ∧ i∈mask I ∧ x∈mask p ∧ adj i x)
  | .avoidNot _ c a _ => decide (c∈mask a)
  | .seeLab _ _ c p _ => decide (c∈mask p)
  | .adjacentCommon x c i => decide (i∈mask I ∧ adj i x ∧ adj i c)
  | .residual x c j l => decide (x≠c ∧ x∉mask I ∧ j<l)
  | .gateEq s e f _ => decide (endpoint s e=endpoint s f)
  | _ => true

def expand (k I : Nat) : Scheme → FactClause
  | .self x j => [pos (.lab x j x)]
  | .earlier x j => [negF (.live x (j+1)),pos (.live x j)]
  | .labCommon x c j => [negF (.live x j),negF (.lab x j c),pos (commonF x c)]
  | .someRes x => negF (.live x 2)::anyRange k (fun t => .res t x)
  | .allRes x t => [negF (.live x (1+k)),pos (.res t x)]
  | .exposure x a => anyRange (cap k I x) (fun j => .avoid x a j)
  | .exactAt x i p => anyRange (cap k I x) (fun j => .see x i p j)
  | .avoidLive x a j => [negF (.avoid x a j),pos (.live x j)]
  | .seeLive x i p j => [negF (.see x i p j),pos (.live x j)]
  | .avoidNot x c a j => [negF (.avoid x a j),negF (.lab x j c)]
  | .seeLab x i c p j => if adj i c then [negF (.see x i p j),pos (.lab x j c)] else [negF (.see x i p j),negF (.lab x j c)]
  | .diffX t x c => [negF (.diff t x c),pos (.res t x)]
  | .diffC t x c => [negF (.diff t x c),negF (.res t c)]
  | .adjacentCommon x c _ => [pos (commonF x c)]
  | .resCommon x c t => [negF (.res t x),negF (.res t c),pos (commonF x c)]
  | .residual x c j l => negF (commonF x c)::negF (.live x l)::pos (.lab x j c)::pos (.lab x l c)::anyRange k (fun t => .diff t x c)
  | .readerAny s e => anyRange (cap k I (endpoint s e)) (fun j => .reader s e j)
  | .readerLive s e j => [negF (.reader s e j),pos (.live (endpoint s e) j)]
  | .readerLab s e j c dir => [(Fact.reader s e j,false),(.lab (endpoint s e) j c,!dir),(.es s e c,dir)]
  | .eqLab s e f c dir => [(Fact.gate e f,false),(.es s e c,!dir),(.es s f c,dir)]
  | .gateEq s e f j => [negF (.reader s e j),negF (.reader s f j),pos (.gate e f)]

theorem scheme_sound {D : Dag} {k I : Nat} (Z : Layout D k I) (h : StrictLive 14 D)
    (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (eq : mask I=ineligSet 14 D)
    (q : Scheme) (en : enabled k I q=true) : EvalClause Z (expand k I q) := by
  classical
  cases q with
  | self x j =>
    simpa only [expand,pos_iff,none_iff,or_false,evalFact] using Z.selfLab x j
  | earlier x j =>
    simp only [expand,neg_iff,pos_iff,none_iff,or_false,evalFact,Layout.Live]
    omega
  | labCommon x c j =>
    simp only [expand,neg_iff,pos_iff,none_iff,or_false,commonF_iff]
    simp only [evalFact]
    have := Z.commonLab x c j; tauto
  | someRes x =>
    simp only [expand,neg_iff,range_iff,evalFact]
    by_cases active : Z.Live x 2
    · obtain ⟨t,ht⟩ := Z.some_code h hc x active
      exact Or.inr ⟨t.val,t.isLt,(atRes Z t x).2 ht⟩
    · exact Or.inl active
  | allRes x t =>
    simp only [enabled,decide_eq_true_eq] at en
    simp only [expand,neg_iff,pos_iff,none_iff,or_false,evalFact]
    by_cases active : Z.Live x (1+k)
    · let i : Fin k := ⟨t,en⟩
      exact Or.inr ((atRes Z i x).2 (Z.all_code h hc x active i))
    · exact Or.inl active
  | exposure x a =>
    simp only [enabled,decide_eq_true_eq] at en
    exact (range_iff _ _ _).2 (Z.expose h hc x a en.1 en.2)
  | exactAt x i p =>
    simp only [enabled,decide_eq_true_eq] at en
    exact (range_iff _ _ _).2 (Z.exact_slot h hc z eq x i p en.1 en.2)
  | avoidLive x a j =>
    simp only [expand,neg_iff,pos_iff,none_iff,or_false,evalFact]
    by_cases v : Z.avoid x a j; exact Or.inr v.1; exact Or.inl v
  | seeLive x i p j =>
    simp only [expand,neg_iff,pos_iff,none_iff,or_false,evalFact]
    by_cases v : Z.see x i p j; exact Or.inr v.1; exact Or.inl v
  | avoidNot x c a j =>
    simp only [enabled,decide_eq_true_eq] at en
    simp only [expand,neg_iff,none_iff,or_false,evalFact]
    by_cases v : Z.avoid x a j; exact Or.inr (v.2 c en); exact Or.inl v
  | seeLab x i c p j =>
    simp only [enabled,decide_eq_true_eq] at en
    by_cases a : adj i c <;> simp only [expand,a,if_true,if_false,neg_iff,pos_iff,none_iff,or_false,evalFact]
    · by_cases v : Z.see x i p j; exact Or.inr ((v.2 c en).2 a); exact Or.inl v
    · by_cases v : Z.see x i p j; exact Or.inr (fun u => a ((v.2 c en).1 u)); exact Or.inl v
  | diffX t x c => simp only [expand,neg_iff,pos_iff,none_iff,or_false,evalFact]; tauto
  | diffC t x c => simp only [expand,neg_iff,none_iff,or_false,evalFact]; tauto
  | adjacentCommon x c i =>
    simp only [enabled,decide_eq_true_eq] at en
    simp only [expand,pos_iff,none_iff,or_false,commonF_iff]
    exact share h hc (i:=i) (eq ▸ en.1) en.2.1 en.2.2
  | resCommon x c t =>
    simp only [expand,neg_iff,pos_iff,none_iff,or_false,commonF_iff]
    simp only [evalFact]
    by_cases rx : rAt Z t x <;> by_cases rc : rAt Z t c
    · obtain ⟨i,eqi,hx⟩ := rx; obtain ⟨j,eqj,hc⟩ := rc
      have same : i=j := Fin.ext (eqi.trans eqj.symm)
      exact Or.inr (Or.inr (Z.commonRes i x c hx (same ▸ hc)))
    all_goals tauto
  | residual x c j l =>
    simp only [enabled,decide_eq_true_eq] at en
    simp only [expand,neg_iff,pos_iff,commonF_iff,range_iff]
    simp only [evalFact]
    by_cases com : Together D x c
    · right; by_cases active : Z.Live x l
      · right
        have elig : x∈eligSet 14 D := by by_contra no; exact en.2.1 (eq ▸ sem_mem_inelig.mpr no)
        rcases Z.ri_slots h hc x c en.1 elig en.2.2 active com with v|v|⟨t,hx,miss⟩
        · exact Or.inl v
        · exact Or.inr (Or.inl v)
        · exact Or.inr (Or.inr ⟨t.val,t.isLt,(atRes Z t x).2 hx,fun u => miss ((atRes Z t c).1 u)⟩)
      · exact Or.inl active
    · exact Or.inl com
  | readerAny s e => exact (range_iff _ _ _).2 ⟨_,Z.boundReader s e,rfl⟩
  | readerLive s e j =>
    simp only [expand,neg_iff,pos_iff,none_iff,or_false,evalFact]
    by_cases r : Z.reader s e=j; exact Or.inr (r ▸ Z.reader_live s e); exact Or.inl r
  | readerLab s e j c dir =>
    cases dir <;> change EvalClause Z (negF _ :: _)
    all_goals simp only [Bool.not_true,Bool.not_false,neg_iff,pos_iff,none_iff,or_false,evalFact]
    all_goals by_cases r : Z.reader s e=j
    all_goals first | exact Or.inl r | have v := Z.readerLab s e j c _ rfl r; tauto
  | eqLab s e f c dir =>
    cases dir <;> change EvalClause Z (negF _ :: _)
    all_goals simp only [Bool.not_true,Bool.not_false,neg_iff,pos_iff,none_iff,or_false,evalFact]
    all_goals by_cases r : Z.edge e=Z.edge f
    all_goals first | exact Or.inl r | have v := Z.eqLab s e f c r; tauto
  | gateEq s e f j =>
    simp only [enabled,decide_eq_true_eq] at en
    simp only [expand,neg_iff,pos_iff,none_iff,or_false,evalFact]
    have v := Z.readerEq s e f j en
    tauto
end Compact

namespace Resolution

def firstOpen (a : Nat) (c : Clause) : Option Lit :=
  c.find? fun l => !(a.testBit (key (neg l)))

def runHints (F : Array Clause) (last : Nat) : List Nat → Nat → Bool
  | [], a => if h : last<F.size then allowed a none F[last] else false
  | i::rest, a => if h : i<F.size then
      match firstOpen a F[i] with
      | none => allowed a none F[i]
      | some p => allowed a (some p) F[i] && runHints F last rest (insertBit a p)
    else false

theorem runHints_sound {F v} (sat : Valid v F) (last : Nat) (units : List Nat) (a : Nat)
    (forced : ∀ l, a.testBit (key l)=true → Yes v l) (ok : runHints F last units a=true) : False := by
  induction units generalizing a with
  | nil =>
    simp only [runHints] at ok
    split at ok
    · rename_i h
      obtain ⟨_,e,_⟩ := allowed_ok (sat _ (Array.getElem_mem h)) forced ok
      contradiction
    · contradiction
  | cons i is ih =>
    simp only [runHints] at ok
    split at ok
    · rename_i h
      split at ok
      · obtain ⟨_,e,_⟩ := allowed_ok (sat _ (Array.getElem_mem h)) forced ok
        contradiction
      · rename_i p _
        rw [Bool.and_eq_true] at ok
        obtain ⟨l,e,hv⟩ := allowed_ok (sat _ (Array.getElem_mem h)) forced ok.1
        have eq := Option.some.inj e
        subst l
        apply ih (insertBit a p) _ ok.2
        intro t ht
        rcases (get_insert _ _ _).1 ht with old | rfl
        · exact forced t old
        · exact hv
    · contradiction

abbrev SmallLine := Clause × Nat × List Nat

def hintGrow (F : Array Clause) : List SmallLine → Array Clause
  | [] => F
  | l::ls => hintGrow (F.push l.1) ls

def validHints (F : Array Clause) : List SmallLine → Bool
  | [] => true
  | l::ls => runHints F l.2.1 l.2.2 (initial l.1) && validHints (F.push l.1) ls

theorem checkedHints {F v} (sat : Valid v F) (ls : List SmallLine) (ok : validHints F ls=true) :
    Valid v (hintGrow F ls) := by
  induction ls generalizing F with
  | nil => exact sat
  | cons l ls ih =>
    simp only [validHints,Bool.and_eq_true] at ok
    obtain ⟨t,r⟩ := ok
    have holds : Holds v l.1 := by
      by_contra no
      apply runHints_sound sat _ _ _ _ t
      intro x hx
      obtain ⟨y,hy,rfl⟩ := get_initial hx
      exact (neg_iff v y).2 (fun yes => no ⟨y,hy,yes⟩)
    apply ih (F:=F.push l.1) _ r
    intro c hc
    rcases Array.mem_push.mp hc with hc|hc
    · exact sat _ hc
    · exact hc ▸ holds

theorem finalHints {F v} (sat : Valid v F) (last : Nat) (hints : List Nat)
    (h : runHints F last hints 0=true) : False := runHints_sound sat last hints 0 (by simp) h

def digits (width : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | count+1, n => (n % (2^width)) :: digits width count (n >>> width)

def unpackLits (width len bits : Nat) : Clause :=
  (digits width len bits).map (fun n => (n/2,n%2==1))
end Resolution

namespace Compact
open PEqualNP.Outside.L_meta_9774_aux.DagTools
open Resolution

def atLit (a : Array Fact) (l : Lit) : Fact × Bool := (a[l.1]?.getD default,l.2)

def localCheck (k I : Nat) (a : Array Fact) (r : Scheme) (c : Clause) : Bool :=
  enabled k I r && (expand k I r).all (fun p => (c.map (atLit a)).contains p)

def inputsOK (k I : Nat) (a : Array Fact) : List Scheme → List Clause → Bool
  | [],[] => true
  | r::rs,c::cs => localCheck k I a r c && inputsOK k I a rs cs
  | _,_ => false

noncomputable def truth {D : Dag} {k I} (Z : Layout D k I) (a : Array Fact) (n : Nat) :=
  @decide (evalFact Z (a[n]?.getD default)) (Classical.propDecidable _)

theorem localSound {D : Dag} {k I : Nat} (Z : Layout D k I) (h : StrictLive 14 D)
    (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (eq : mask I=ineligSet 14 D)
    (a : Array Fact) (r : Scheme) (c : Clause) (ok : localCheck k I a r c=true) :
    Holds (truth Z a) c := by
  simp only [localCheck,Bool.and_eq_true] at ok
  obtain ⟨p,hm,hval⟩ := scheme_sound Z h hc z eq r ok.1
  have mem := List.contains_iff_mem.mp (List.all_eq_true.mp ok.2 p hm)
  obtain ⟨l,hl,eqp⟩ := List.mem_map.mp mem
  subst p
  refine ⟨l,hl,?_⟩
  rcases l with ⟨i,b⟩
  cases b <;> simp [truth,Yes,atLit] at hval ⊢ <;> exact hval

theorem inputs_sound {D : Dag} {k I : Nat} (Z : Layout D k I) (h : StrictLive 14 D)
    (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (eq : mask I=ineligSet 14 D)
    (a : Array Fact) (R : List Scheme) (F : Array Clause)
    (ok : inputsOK k I a R F.toList=true) : Valid (truth Z a) F := by
  have all (rs : List Scheme) (cs : List Clause) (good : inputsOK k I a rs cs=true) : List.Forall (Holds (truth Z a)) cs := by
    induction rs generalizing cs with
    | nil => cases cs <;> simp_all [inputsOK,List.Forall]
    | cons r rs ih =>
      cases cs with
      | nil => contradiction
      | cons c cs =>
        simp only [inputsOK,Bool.and_eq_true] at good
        apply List.forall_iff_forall_mem.mpr
        intro item mem
        rcases List.mem_cons.mp mem with rfl|rest
        · exact localSound Z h hc z eq a r _ good.1
        · exact List.forall_iff_forall_mem.mp (ih cs good.2) item rest
  intro c cF
  exact List.forall_iff_forall_mem.mp (all R F.toList ok) c (Array.mem_toList_iff.mpr cF)
end Compact

namespace Compact
open PEqualNP.Outside.L_meta_9774_aux.DagTools Resolution

def maskBook : List Nat := [127, 245, 314, 432, 543, 661, 794, 1102, 1220, 1550, 1802, 2087, 2213, 2338, 2567, 2693, 3590, 3716, 4179, 4305, 4627, 4753, 4882, 5008, 5186, 6659, 7938, 8297, 8417, 8488, 8713, 9288, 9992, 10401, 10656, 12481, 13504, 14977, 16256]

def field (n i : Nat) := (n >>> (5+6*i)) &&& 63

def readFact (n : Nat) : Fact :=
  match n%32 with
  | 0 => .live (Fin.ofNat 14 (field n 0)) (field n 1)
  | 1 => .lab (Fin.ofNat 14 (field n 0)) (field n 1) (Fin.ofNat 14 (field n 2))
  | 2 => .res (field n 0) (Fin.ofNat 14 (field n 1))
  | 3 => .common (Fin.ofNat 14 (field n 0)) (Fin.ofNat 14 (field n 1))
  | 4 => .gate (Fin.ofNat 19 (field n 0)) (Fin.ofNat 19 (field n 1))
  | 5 => .reader (field n 0==1) (Fin.ofNat 19 (field n 1)) (field n 2)
  | 6 => .es (field n 0==1) (Fin.ofNat 19 (field n 1)) (Fin.ofNat 14 (field n 2))
  | 7 => .avoid (Fin.ofNat 14 (field n 0)) (maskBook.getD (field n 1) 0) (field n 2)
  | 8 => .see (Fin.ofNat 14 (field n 0)) (Fin.ofNat 14 (field n 1)) (maskBook.getD (field n 2) 0) (field n 3)
  | 9 => .diff (field n 0) (Fin.ofNat 14 (field n 1)) (Fin.ofNat 14 (field n 2))
  | _ => default

def readScheme (n : Nat) : Scheme :=
  match n%32 with
  | 0 => .self (Fin.ofNat 14 (field n 0)) (field n 1)
  | 1 => .earlier (Fin.ofNat 14 (field n 0)) (field n 1)
  | 2 => .labCommon (Fin.ofNat 14 (field n 0)) (Fin.ofNat 14 (field n 1)) (field n 2)
  | 3 => .someRes (Fin.ofNat 14 (field n 0))
  | 4 => .allRes (Fin.ofNat 14 (field n 0)) (field n 1)
  | 5 => .exposure (Fin.ofNat 14 (field n 0)) (maskBook.getD (field n 1) 0)
  | 6 => .exactAt (Fin.ofNat 14 (field n 0)) (Fin.ofNat 14 (field n 1)) (maskBook.getD (field n 2) 0)
  | 7 => .avoidLive (Fin.ofNat 14 (field n 0)) (maskBook.getD (field n 1) 0) (field n 2)
  | 8 => .seeLive (Fin.ofNat 14 (field n 0)) (Fin.ofNat 14 (field n 1)) (maskBook.getD (field n 2) 0) (field n 3)
  | 9 => .avoidNot (Fin.ofNat 14 (field n 0)) (Fin.ofNat 14 (field n 1)) (maskBook.getD (field n 2) 0) (field n 3)
  | 10 => .seeLab (Fin.ofNat 14 (field n 0)) (Fin.ofNat 14 (field n 1)) (Fin.ofNat 14 (field n 2)) (maskBook.getD (field n 3) 0) (field n 4)
  | 11 => .diffX (field n 0) (Fin.ofNat 14 (field n 1)) (Fin.ofNat 14 (field n 2))
  | 12 => .diffC (field n 0) (Fin.ofNat 14 (field n 1)) (Fin.ofNat 14 (field n 2))
  | 13 => .adjacentCommon (Fin.ofNat 14 (field n 0)) (Fin.ofNat 14 (field n 1)) (Fin.ofNat 14 (field n 2))
  | 14 => .resCommon (Fin.ofNat 14 (field n 0)) (Fin.ofNat 14 (field n 1)) (field n 2)
  | 15 => .residual (Fin.ofNat 14 (field n 0)) (Fin.ofNat 14 (field n 1)) (field n 2) (field n 3)
  | 16 => .readerAny (field n 0==1) (Fin.ofNat 19 (field n 1))
  | 17 => .readerLive (field n 0==1) (Fin.ofNat 19 (field n 1)) (field n 2)
  | 18 => .readerLab (field n 0==1) (Fin.ofNat 19 (field n 1)) (field n 2) (Fin.ofNat 14 (field n 3)) (field n 4==1)
  | 19 => .eqLab (field n 0==1) (Fin.ofNat 19 (field n 1)) (Fin.ofNat 19 (field n 2)) (Fin.ofNat 14 (field n 3)) (field n 4==1)
  | 20 => .gateEq (field n 0==1) (Fin.ofNat 19 (field n 1)) (Fin.ofNat 19 (field n 2)) (field n 3)
  | _ => default

def readClause (width n : Nat) : Clause := unpackLits width (n%8) (n>>>3)

def readStep (clauseWidth reasonWidth g u : Nat) : SmallLine :=
  (unpackLits clauseWidth (g%64) (g>>>6), (u>>>9) % (2^reasonWidth), digits reasonWidth (u%512) (u>>>(9+reasonWidth)))
end Compact

namespace Compact
open PEqualNP.Outside.L_meta_9774_aux.DagTools Resolution

def ValidThrough (v : Nat → Bool) (book : Nat → Clause) (n : Nat) :=
  ∀ i, i<n → Holds v (book i)

def checkReasons (book : Nat → Clause) (n last : Nat) : List Nat → Nat → Bool
  | [], a => decide (last<n) && allowed a none (book last)
  | i::rest, a => decide (i<n) &&
      match firstOpen a (book i) with
      | none => allowed a none (book i)
      | some p => allowed a (some p) (book i) && checkReasons book n last rest (insertBit a p)

theorem reasons_sound {v book n} (sat : ValidThrough v book n)
    (last : Nat) (units : List Nat) (a : Nat)
    (forced : ∀ l, a.testBit (key l)=true → Yes v l)
    (ok : checkReasons book n last units a=true) : False := by
  induction units generalizing a with
  | nil =>
    simp only [checkReasons,Bool.and_eq_true,decide_eq_true_eq] at ok
    obtain ⟨_,e,_⟩ := allowed_ok (sat _ ok.1) forced ok.2
    contradiction
  | cons i us ih =>
    simp only [checkReasons,Bool.and_eq_true,decide_eq_true_eq] at ok
    obtain ⟨hi,rest⟩ := ok
    split at rest
    · obtain ⟨_,e,_⟩ := allowed_ok (sat _ hi) forced rest
      contradiction
    · rename_i p _
      rw [Bool.and_eq_true] at rest
      obtain ⟨l,e,hv⟩ := allowed_ok (sat _ hi) forced rest.1
      have eq := Option.some.inj e
      subst l
      apply ih (insertBit a p) _ rest.2
      intro t ht
      rcases (get_insert _ _ _).1 ht with old|rfl
      · exact forced t old
      · exact hv

def checkRows (book : Nat → Clause) (width : Nat) : Nat → List Nat → Bool
  | _, [] => true
  | i, u::us => checkReasons book i ((u>>>9) % (2^width))
      (digits width (u%512) (u>>>(9+width))) (initial (book i)) && checkRows book width (i+1) us

theorem rows_sound {v book width i} (sat : ValidThrough v book i) (rows : List Nat)
    (ok : checkRows book width i rows=true) : ValidThrough v book (i+rows.length) := by
  induction rows generalizing i with
  | nil => simpa using sat
  | cons u us ih =>
    simp only [checkRows,Bool.and_eq_true] at ok
    have holds : Holds v (book i) := by
      by_contra no
      apply reasons_sound sat _ _ _ _ ok.1
      intro x hx
      obtain ⟨y,hy,rfl⟩ := get_initial hx
      exact (Resolution.neg_iff v y).2 (fun yes => no ⟨y,hy,yes⟩)
    have step : ValidThrough v book (i+1) := by
      intro j hj
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with lt | rfl
      · exact sat j lt
      · exact holds
    have next := ih step ok.2
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using next

def baseBook (book : Nat → Clause) (n : Nat) : Array Clause :=
  Array.ofFn fun i : Fin n => book i.val

theorem book_start {D k I} (Z : Layout D k I) (h : StrictLive 14 D)
    (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (eq : mask I=ineligSet 14 D)
    (a : Array Fact) (R : List Scheme) (book : Nat → Clause) (n : Nat)
    (ok : inputsOK k I a R (baseBook book n).toList=true) : ValidThrough (truth Z a) book n := by
  have sat := inputs_sound Z h hc z eq a R (baseBook book n) ok
  intro j hj
  apply sat
  exact Array.mem_ofFn.mpr ⟨⟨j,hj⟩,rfl⟩

theorem book_end {v book n} (sat : ValidThrough v book n) (last : Nat) (units : List Nat)
    (ok : checkReasons book n last units 0=true) : False :=
  reasons_sound sat last units 0 (by simp) ok
end Compact

-- The following finite cases encode clauses and proofs by unit propagation.
namespace Compact
open PEqualNP.Outside.L_meta_9774_aux.DagTools Resolution

def a177 := ([6146,0x5002,0x5802,0x60061,0x20061,0xc0061,0x5063,0x60861,0x20861,0xc0861,4192,0x9067,0x29067,0x49067,0x3868,0x803868,0x1003868,0x60081,0xc0081,0x3887,0xc00c1,0xc08c1,0xc10c1,0x60141,0x100141,0x160141,0x5943,2368,0x60941,0x100941,0x160941,4416,0x61141,0x101141,0x161141,0x140148,0x940148,0x1140148,0x340148,0xb40148,0x1340148,0x142948,0x942948,0x1142948,0x342948,0xb42948,0x1342948,0x65009,0x165009,4448,0x4005,0x24005,0x44005,0x64006,0xc4006,0x4025,0x24025,0x44025,0x5805,0x65806,0xc5806,0x5825,0x25825,0x45825,0x9005,0x29005,0x49005,0xc9006,0x9025,0x29025,0x49025,0x5904,0x9104,0x9164] : List Nat).toArray.map readFact

def r177 := ([96,2144,99,0x240869,0x243069,0xa40869,0xa43069,0x49067,0x9065,0x2386a,0xc386a,0x2002386a,0x200c386a,0x1003868,0x3866,0xe1889,0xe3089,0x3885,192,2240,4288,0x506014a,0x510014a,0x940148,0x2506014a,0x2510014a,0x1140148,0x4506014a,0x4510014a,0x140146,0xd10014a,0xd16014a,0xb40148,0x2d10014a,0x2d16014a,0x1340148,0x4d10014a,0x4d16014a,0x340146,0x506294a,0x510294a,0x942948,0x2506294a,0x2510294a,0x1142948,0x4506294a,0x4510294a,0x142946,0xd10294a,0xd16294a,0xb42948,0x2d10294a,0x2d16294a,0x1342948,0x4d10294a,0x4d16294a,0x342946,6478,0x6500c,0x80194f,0x100194f,0x102194f,0x8594d,0x16500b,0x16500c,0x80594f,0x100594f,0x102594f,355,0x4010,0x21804012,0x3004012,0x21824012,0x3024012,0x44011,0x4030,0x44031,0x5810,0x1805812,0x3005812,0x5830,0x45831,0x9010,0x23009012,0x23029012,0x23049012,0x9030,0x49031,0x21964013,0x164034,0x964034,0x3244013,0x244034,0xa44034,0x3245813,0x245834,0xa45834] : List Nat).map readScheme

def table177_0 : List Nat := [449,961,0x4502,0x20582,0x28582,0x40602,0x48602,0x54682,0x6c645c3,0x24702,0x28702,0x44782,0x48782,0x54802,0x847c743,0x88982]

def table177_1 : List Nat := [0x90982,2497,2625,2753,2881,0xb9182,0xc5182,0xdd202,0xe1202,0xed202,0xfd282,0x101282,0x10d282,0x12d251c3,0xc5302,0xc9302]

def table177_2 : List Nat := [0xdd382,0xed382,0xf1382,0xfd402,0x10d402,0x111402,0x1453d343,0xb9482,0xc1482,0xdd502,0xe1502,0xe9502,0xfd582,0x101582,0x109582,0x15d554c3]

def table177_3 : List Nat := [0xc1602,0xc9602,0xdd682,0xe9682,0xf1682,0xfd702,0x109702,0x111702,0x1756d643,0x3400083,6018,0x17ce4bcd8305,0x17d04bcf8305,0x17d04e4f8305,3393,0xd802]

def table177_4 : List Nat := [0x11802,0x184f4ccd8d05,0x18514ccf8d05,0x18514f4f8d05,0x15882,0x1a59d943,0x1ac19903,0x1b02d903,0x1ac39983,0x1b04d983,0x55a02,0x1cdc5bc3,0x18dc82,7489,0x1d88dd03,0x1e095d03]

def table177_5 : List Nat := [0x1fdf5ec3,0x18df82,0x2160e043,0x21ca2003,0x21caa083,0x21cb2103,0x2362e243,0x18e302,0x1ddaa383,0x23de9b83,0x23df1c03,0x219b6403,0x24621b83,0x24629c03,0x219e6483,0x24e21e83]

def table177_6 : List Nat := [0x24e29f03,8641,0x1151d85604,0x11d64fc3,0x11d15843,0x6c84483,0x1b0542,0x800f9204,0x11c0800f84,0x23e211d804,0x11d84fc3,0x1758545204,0x15d754584d8e86,0x15d458574d85,0x23e211c3,0x23e20dc3]

def table177_7 : List Nat := [0x23e21803,0x164d984f8cc5,0xd98565584,0xd93d8564f85,0x23e202,0xd984fc3,0x184d975444,0xd985143,0xd9842,0x801583,0x317cd95d185,0x23cd82,0x12554fc3,0x23cc42,9153,0xf8082]

def table177_8 : List Nat := [0xf8c02,3969,4545]

def encoded177 (i : Nat) : Nat :=
  if i < 64 then
    if i < 32 then
      if i < 16 then
        table177_0.getD (i%16) 0
      else
        table177_1.getD (i%16) 0
    else
      if i < 48 then
        table177_2.getD (i%16) 0
      else
        table177_3.getD (i%16) 0
  else
    if i < 96 then
      if i < 80 then
        table177_4.getD (i%16) 0
      else
        table177_5.getD (i%16) 0
    else
      if i < 112 then
        table177_6.getD (i%16) 0
      else
        if i < 128 then
          table177_7.getD (i%16) 0
        else
          table177_8.getD (i%16) 0

def book177 (i : Nat) : Clause := let n := encoded177 i; unpackLits 8 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClauses177 : inputsOK 1 177 a177 r177 (baseBook book177 97).toList=true := by decide +kernel

def rows177_0 : List Nat := [0xaa28a826a624a406,0x444c463c602e3a3484627c820b,0x323a34706a6605,0x484c443e84706886c67cc46c0b,0x6100c1c181205,0xa10081c148e8a9492ca0e1a160c,0x5a7a56324e7674302e725e0a,0x5c38547a4e7874363ace725e0b,0x7674302e725e5856323a34d07e04ccb6b89698b4a0a28880bebcc29e20229a4e1f,0x464482622e3a347c3c60c64c0b,0x4482622e7c3c607066324c0a,0x44826270667c3c505e564c0a,0x823e7c70603c4c42d86809,0x3c4c405e52da5c383ad64a6ec8d2500e,0x745a2a7204ccb6b89698b4a0a28880bebcc29e20229a7e846e7064603e4c485c40585e52502cdc7c7828,0x5a585e5476742ade502cd27204ccb6b89698b4a0a28880bebcc29e20229a7e781f,0x6e8468827c7005,0x86447c7066424c485c3ee2586e0c,0x864a7c706c484c3ee26809,0x466ae642565ee450e0602cdcdeda0d,0x58466ada03,0x385cd62c60e4da3a07,0x867ce6602cc8ea4407,0x6e4aeeec03]

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk177_0 : checkRows book177 8 97 rows177_0=true := by decide +kernel

def rows177_1 : List Nat := [0x78745a72d0582a06,0x762a5e502c5405,0x76305e56323a34d0f47274f27e04ccb6ba9698b2a0a2c0bcc29e20229aacae8880f0e84e23,0x2c3a345e585005,0x98bab6cc04d07ef852b2a0a2c0bcc29e20229aacae8880c44a4c403c706c383a2e64f6dc2c9625,0x98bab6cc04f27eb2a0a2c0bcc29e20229aacae8880846e7064603e4c485c5e50fa40f82e52f67ce89628,0x52f47274f2502cd004948a90028cb09c1e229afc005e15,0x485c5e5250403e846e7064f07efe607c4c10,0x4ac82c40f07efe3d004c09,0x74304e5e5856322e3a347204948a90028cb09c1e229afc007ed502761b]

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk177_1 : checkRows book177 8 121 rows177_1=true := by decide +kernel

def lastUnits177 := digits 8 28 0x3a2a1539024a45480146584e0f114d7e003f6d2335292f2c81281682

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflict177 : checkReasons book177 131 59 lastUnits177 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem exclude177 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 177=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=1) h hc bp eq (by decide +kernel)
  let v := truth Z a177
  have hbase : ValidThrough v book177 97 := book_start Z h hc z eq _ _ _ _ initialClauses177
  have h0 : ValidThrough v book177 121 := rows_sound hbase rows177_0 rowsOk177_0
  have h1 : ValidThrough v book177 131 := rows_sound h0 rows177_1 rowsOk177_1
  exact book_end h1 _ _ conflict177
end Compact

namespace Compact
open PEqualNP.Outside.L_meta_9774_aux.DagTools Resolution

def a298 := ([0x3002,0x5802,0x6002,0x60c3,4288,0x120101,0x160101,8455,0x5907,0x120121,0x120921,0x121121,0x160161,0xe0161,0x120161,0x6163,0x160961,0xe0961,0x120961,4448,0x2967,0x22967,0x42967,0x1e1968,0x9e1968,0x11e1968,0xc0181,0xe0181,0x120181,0x160181,2432,0xc0981,0xe0981,0x120981,0x160981,4480,0xc1181,0xe1181,0x121181,0x161181,2439,0x20987,0x40987,0x7987,0x27987,0x47987,0x261988,0xa61988,0x1261988,0x4a2988,0xca2988,0x14a2988,0xc6009,0x166009,0x8005,0x28005,0x48005,0x8025,0x128026,0x168026,0x8805,0x28805,0x48805,0x8825,0x28825,0x48825,0x128826,0x9005,0x29005,0x49005,0x9025,0x29025,0x49025,0x129026,0x169026,0x8a04,0x9204,0x9224] : List Nat).toArray.map readFact

def r298 := ([195,0x84909,8453,0x165909,0x5905,288,2336,4384,352,2400,355,0xa3969,0xa4969,0x8a3969,0x8a4969,0x42967,0x2965,0x78e196a,0x792196a,0x278e196a,0x2792196a,0x11e1968,0x1e1966,0x23189,0x23989,0x823189,0x823989,0x40987,0x1023189,0x1023989,2437,0x1e3989,0x1e4989,0x1e5989,0x27987,0x9e4989,0x9e5989,0x47987,0x11e4989,0x11e5989,0x7985,0x98c198a,0x98e198a,0xa61988,0x298c198a,0x298e198a,0x1261988,0x498c198a,0x498e198a,0x261986,0x128e298a,0x1292298a,0x1296298a,0xca2988,0x3292298a,0x3296298a,0x14a2988,0x5292298a,0x5296298a,0x4a2986,0x318e,0xc600c,0x80318f,0x100318f,0x102318f,0x6598d,0x16600b,0x16600c,0x80598f,0x100598f,0x102598f,0x8010,0x48011,0x8030,0x4808032,0x5808032,0x8810,0x48811,0x8830,0x24808832,0x24828832,0x24848832,0x9010,0x49011,0x9030,0x4809032,0x25809032,0x4829032,0x25829032,0x49031,0x228014,0xa28014,0x4a28033,0x248014,0xa48014,0x5a48033,0x248814,0xa48814,0x24a48833] : List Nat).map readScheme

def table298_0 : List Nat := [0x4202,0x28382,961,0x30402,1089,1217,1345,1473,1601,2113,0xc982,0x68a02,0x70a02,0x88a82,0x90a82,0x9cb02]

def table298_1 : List Nat := [0xb4aca43,0x6cb82,0x70b82,0x8cc02,0x90c02,0x9cc82,0xccc4bc3,0xd1402,0xd9402,0xf9482,0x101482,0x11d502,0x121502,0x129502,0x1554d443,0xd9582]

def table298_2 : List Nat := [0xe1582,0xe9582,0xf5602,0x109602,0x111602,0x11d682,0x131682,0x139682,0x16d655c3,0xd1702,0xdd702,0xf5782,0xf9782,0x105782,0x11d802,0x121802]

def table298_3 : List Nat := [0x12d802,0x1857d743,0xd9882,0xe5882,0xe9882,0xf5902,0x10d902,0x111902,0x11d982,0x135982,0x139982,0x19d958c3,0x1c00103,6658,0x1a4fcd4f0185,0x1a524d518185]

def table298_4 : List Nat := [0x1a524fd18185,1985,0x15a82,0x9a82,0x1ad14ecf0785,0x1ad3ced18785,0x1ad3d1518785,0x1c5bdb43,0x25c02,7361,0x1d02dc83,0x1d835c83,0x1f5ede43,0x25f02,0x20e05fc3,0x21449f83]

def table298_5 : List Nat := [0x21452003,0x2145a083,0x22e261c3,0x26282,0x2463e343,0x24876303,0x25462303,0x24896383,0x25482383,0x9e402,0x25de1b03,0x25de9b83,0x211d6583,0x26619b03,0x26621b83,0x251de603]

def table298_6 : List Nat := [0x26e19e03,0x26e21e83,0x24e12683,8513,0x1ad6d15884,0x19dad6d144,0x1ad1c2,0x1ad882,0x1ad602,0x1ad142,6849,0xf1a5751818fc6,0x11974f0004,9537,0x1c5f66e204,0x22df5c66c4]

def table298_7 : List Nat := [2305,1793,9345,0x118f03,0x1919a57d405,0x19a545804,4482,0x18419a56d485,1]

def encoded298 (i : Nat) : Nat :=
  if i < 64 then
    if i < 32 then
      if i < 16 then
        table298_0.getD (i%16) 0
      else
        table298_1.getD (i%16) 0
    else
      if i < 48 then
        table298_2.getD (i%16) 0
      else
        table298_3.getD (i%16) 0
  else
    if i < 96 then
      if i < 80 then
        table298_4.getD (i%16) 0
      else
        table298_5.getD (i%16) 0
    else
      if i < 112 then
        table298_6.getD (i%16) 0
      else
        table298_7.getD (i%16) 0

def book298 (i : Nat) : Clause := let n := encoded298 i; unpackLits 8 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClauses298 : inputsOK 1 298 a298 r298 (baseBook book298 99).toList=true := by decide +kernel

def rows298_0 : List Nat := [0x2887a01a7859c06,0x114469050335006,0x46d90c46aef2415008,0x40a123b6f95c256608,0x64509e2b4cd050334809,0x8c9334176d91e77408,0x3a4f1b341ca05,0x4ce74218ae9db7d39f341500c,0x3478e177cc57c05a08,0x1d6064bbf5ec566b7af216a3c0d,0x87aacd4b026b081408,0x17afed960c25ab98e50105266618e0f,0x5bb98e501053305dbfb6583092696e8e11,0x5901e38b15150f514220a,0x6901e30b15150f512260a,0x150f554afc2af1b208,0x38fccbe7aa5e42d46156c3c0c,0x3f2ec55185e05,0xeb033017ae3c06,0x3976d5928447d531ebd1e42d4f55f34c11,0x227c6549f54c569a5009,0x585d5b15460f1beeb9ea5ecf216a7c10]

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk298_0 : checkRows book298 7 99 rows298_0=true := by decide +kernel

def lastUnits298 := digits 7 8 0xa736400f18b963

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflict298 : checkReasons book298 121 111 lastUnits298 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem exclude298 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 298=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=1) h hc bp eq (by decide +kernel)
  let v := truth Z a298
  have hbase : ValidThrough v book298 99 := book_start Z h hc z eq _ _ _ _ initialClauses298
  have h0 : ValidThrough v book298 121 := rows_sound hbase rows298_0 rowsOk298_0
  exact book_end h0 _ _ conflict298
end Compact

namespace Compact
open PEqualNP.Outside.L_meta_9774_aux.DagTools Resolution

def a432 := ([6146,0x5002,0x5802,0x60061,0x20061,0xc0061,0x140061,0x5063,2144,0x60861,0x20861,0xc0861,0x140861,4192,0x21061,0x141061,0xc067,0x2c067,0x4c067,0xe3868,0x8e3868,0x10e3868,0x141809,0x60081,0xc0081,0x3887,0xc00c1,0xc08c1,0xc10c1,0x120141,0x160141,0x5943,2368,0x120941,0x160941,4416,0x121141,0x161141,0x7147,0x27147,0x47147,0x202948,0xa02948,0x1202948,0x165009,4448,0x4005,0x24005,0x44005,0x64006,0xc4006,0x4025,0x24025,0x44025,0x5805,0x65806,0xc5806,0x5825,0x25825,0x45825,0x9005,0x29005,0x49005,0xc9006,0x9025,0x29025,0x49025,0x5904,0x9104,0x9164] : List Nat).toArray.map readFact

def r432 := ([96,2144,99,0x300869,0x303069,0x305069,0x2c067,0xb00869,0xb03069,0xb05069,0x4c067,0x1300869,0x1305069,0xc065,0x382386a,0x38c386a,0x394386a,0x8e3868,0x2382386a,0x238c386a,0x2394386a,0x10e3868,0x4382386a,0x4394386a,0xe3866,0x506e,0x14180c,0x80506f,0x100506f,0x102506f,0xe1889,0xe3089,0x3885,192,2240,4288,0x1c4949,0x1c5949,0x27147,0x9c4949,0x9c5949,0x47147,0x11c4949,0x11c5949,0x7145,0x812294a,0x816294a,0xa02948,0x2812294a,0x2816294a,0x1202948,0x4812294a,0x4816294a,0x202946,0x8594d,0x16500b,0x16500c,0x80594f,0x100594f,0x102594f,355,0x4010,0x21804012,0x3004012,0x21824012,0x3024012,0x44011,0x4030,0x44031,0x5810,0x1805812,0x3005812,0x5830,0x45831,0x9010,0x23009012,0x23029012,0x23049012,0x9030,0x49031,0x21964013,0x164034,0x964034,0x3244013,0x244034,0xa44034,0x3245813,0x245834,0xa45834] : List Nat).map readScheme

def table432_0 : List Nat := [449,1217,0x4682,0x20802,0x28802,0x30802,0x44882,0x50882,0x58882,0x60882,0x6c902,0x70902,0x78902,0x948c843,0x24982,0x28982]

def table432_1 : List Nat := [0x30982,0x44a02,0x54a02,0x58a02,0x60a02,0x6ca82,0x74a82,0x78a82,0xaca49c3,0x3c08003,0x8b02,0xb4643440385,0xb47c3468385,0xb47c6468385,0xb8c82,0xc0c82]

def table432_2 : List Nat := [3265,3393,3521,3649,0xe9302,0xf1302,0x105382,0x109382,0x111382,0x11d402,0x121402,0x129402,0x1453d343,0xed482,0xf1482,0x105502]

def table432_3 : List Nat := [0x10d502,0x111502,0x11d582,0x125582,0x129582,0x15d554c3,4033,0xd602,0x11602,0x16514f500f85,0x1652cf518f85,0x1652d1518f85,0x15682,0x1857d743,0x18c19703,0x1902d703]

def table432_4 : List Nat := [0x18c49783,0x1905d783,0x6d802,0x1ada59c3,0x16da82,6977,0x1b8bdb03,0x1c0c5b03,0x1ddd5cc3,0x16dd82,0x1f5ede43,0x1fcd1e03,0x1fcd9e83,0x1fce1f03,0x2160e043,0x16e102]

def table432_5 : List Nat := [0x1bd8a183,0x21dc9983,0x21dd1a03,0x1f996203,0x22601983,0x22609a03,0x1f9c6283,0x22e01c83,0x22e09d03,8129,0x13d65483,0x9d91746c4,0x190b438804,0x190b494384,0x6d90949c4,0x990943]

def table432_6 : List Nat := [0x21e01603,0x165402,0x164f02,0x165582,0x165502,5697,2305,0x38a02,0x9c682,8641]

def encoded432 (i : Nat) : Nat :=
  if i < 48 then
    if i < 16 then
      table432_0.getD (i%16) 0
    else
      if i < 32 then
        table432_1.getD (i%16) 0
      else
        table432_2.getD (i%16) 0
  else
    if i < 80 then
      if i < 64 then
        table432_3.getD (i%16) 0
      else
        table432_4.getD (i%16) 0
    else
      if i < 96 then
        table432_5.getD (i%16) 0
      else
        table432_6.getD (i%16) 0

def book432 (i : Nat) : Clause := let n := encoded432 i; unpackLits 8 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClauses432 : inputsOK 1 432 a432 r432 (baseBook book432 89).toList=true := by decide +kernel

def rows432_0 : List Nat := [0x26a3988a5a19406,0xad72958916b67407,0x133055ec28205,0x508982e702db7e10703360b,0x5ca98241c81b12186dc3a0b,0x1c9182a11fdb1a07,0x417b09f8f1a0c75e0466e9a100d,0x161650e903868619042afb7a7521c4a5224bc715eb598e7d045301d,0x3354c5dae74ad4b66a09,0xd14326ac13acc295736760b,0x74d1936c404,0x72c57b6c404,0x518935a6b8f2367208,0x161650e9038686196f9410a300d,0xd37ca5028dcc1c911360a,0x66127429c345cc6732df2821a0d,0x2449b15a39f41161c4ab4ecdf6f9a74f78e3065a216]

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk432_0 : checkRows book432 7 89 rows432_0=true := by decide +kernel

def lastUnits432 := digits 7 25 0x1a124030dcc0c76832df28284f60017d4231e4117480

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflict432 : checkReasons book432 106 27 lastUnits432 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem exclude432 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 432=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=1) h hc bp eq (by decide +kernel)
  let v := truth Z a432
  have hbase : ValidThrough v book432 89 := book_start Z h hc z eq _ _ _ _ initialClauses432
  have h0 : ValidThrough v book432 106 := rows_sound hbase rows432_0 rowsOk432_0
  exact book_end h0 _ _ conflict432
end Compact

namespace Compact
open PEqualNP.Outside.L_meta_9774_aux.DagTools Resolution

def a523 := ([8194,0x2802,0x3002,0x5002,0x5802,0x6802,0x80061,0xc0061,2151,0x80081,0x3083,0x80881,4224,0x81081,0x58a3,4256,0xc00c1,0x800c1,0xa00c1,0x68c3,2240,0xc08c1,0x808c1,0xa08c1,4288,0x810c1,0xa10c1,4295,0x210c7,0x410c7,0x48c8,0x8048c8,0x10048c8,0x83009,0xe00e1,0xe08e1,0xe10e1,0x120121,0x180121,0x9127,0x140141,0x100141,0x120141,0x5943,0x180141,0x140941,0x100941,0x120941,0x180941,4416,0x141141,0xb147,0x2b147,0x4b147,0x340148,0xb40148,0x1340148,0xa0161,0xe0161,0x140161,0x1a0161,2400,0xa0961,0xe0961,0x140961,0x1a0961,4448,0xa1161,0xe1161,0x141161,0x4167,0x24167,0x44167,0xe167,0x2e167,0x4e167,0x181968,0x981968,0x1181968,0x221968,0xa21968,0x1221968,0xa5809,0x145809,0x180181,0x180981,0x181181,0x1a01a1,0xc01a1,0xe01a1,0x1401a1,2464,0x1a09a1,0xc09a1,0xe09a1,0x1409a1,4512,0xc11a1,0xe11a1,0x41a7,0x241a7,0x441a7,0x4809a8,0xc809a8,0x14809a8,0xc6809,0x3805,0x3825,0x23825,0x43825,0xe3826,0x4005,0x84006,0xc4006,0x4025,0x24025,0x44025,0xe4026,0x5005,0x25005,0x45005,0x5025,0x25025,0x45025,0x145026,0x5805,0x25805,0x45805,0x85806,0x5825,0x25825,0x45825,0x145826,0x1a5826,0x6005,0x26005,0x46005,0x6025,0x26025,0x46025,0x146026,0x1a6026,0x6805,0x26805,0x46805,0x6825,0x126826,0x186826,0x7005,0x27005,0x47005,0x7025,0x27025,0x47025,0x127026,0x187026,0x7805,0x27805,0x47805,0x7825,0x27825,0x47825,0x187826,0x9005,0x29005,0x49005,0x89006,0xc9006,0x9025,0x29025,0x49025,0x40e4,0x5904,0x9104,0x5944,0x6144,0x6164,0x9164,0x71a4,0x79a4,0x79c4] : List Nat).toArray.map readFact

def r523 := ([0x22069,0x23069,2149,128,2176,4224,131,163,192,2240,195,0x420c9,0x428c9,0x210c7,0x8420c9,0x8428c9,0x410c7,0x10420c9,0x10428c9,4293,0x848ca,0xa48ca,0x8048c8,0x200848ca,0x200a48ca,0x10048c8,0x400848ca,0x400a48ca,0x48c6,8398,0x8300c,0x8020cf,0x10020cf,0x10220cf,224,2272,4320,288,0x246129,0x9125,320,2368,4416,323,0x2c4149,0x2c4949,0x2c6149,0xac4149,0xac4949,0xac6149,0x4b147,0xb145,0xd10014a,0xd12014a,0xd18014a,0x2d10014a,0x2d12014a,0x2d18014a,0x1340148,0x340146,355,0x103969,0x105169,0x24167,0x903969,0x905169,0x44167,0x1103969,0x1105169,0x4165,0x382969,0x383969,0x386969,0x2e167,0xb82969,0xb83969,0xb86969,0x4e167,0x1382969,0x1383969,0xe165,0x60a196a,0x60e196a,0x981968,0x260a196a,0x260e196a,0x460a196a,0x460e196a,0x181966,0x88e196a,0x894196a,0xa21968,0x288e196a,0x2894196a,0x488e196a,0x4894196a,0x221966,0x296e,0xa580c,0x80296f,0x100296f,0x102296f,0x516e,0x14580c,0x80516f,0x100516f,0x102516f,384,2432,4480,416,2464,419,0x1031a9,0x1039a9,0x1051a9,0x241a7,0x9031a9,0x9039a9,0x9051a9,0x441a7,0x11031a9,0x11039a9,0x41a5,0x120c09aa,0x120e09aa,0x121409aa,0xc809a8,0x320c09aa,0x320e09aa,0x321409aa,0x14809a8,0x520c09aa,0x520e09aa,0x4809a6,0x31ae,0xc680c,0x8031af,0x10031af,0x10231af,0x3810,0x3830,0x23803832,0x23823832,0x23843832,0x4010,0x2004012,0x3004012,0x4030,0x3804032,0x3824032,0x44031,0x5010,0x45011,0x5030,0x25005032,0x25025032,0x25045032,0x5810,0x22005812,0x22025812,0x45811,0x22045812,0x5830,0x5005832,0x6805832,0x5025832,0x6825832,0x45831,0x6010,0x46011,0x6030,0x5006032,0x26806032,0x5026032,0x26826032,0x46031,0x6810,0x46811,0x6830,0x24806832,0x6006832,0x7010,0x47011,0x7030,0x4807032,0x6007032,0x4827032,0x6027032,0x47031,0x7810,0x47811,0x7830,0x26007832,0x26027832,0x26047832,0x9010,0x2009012,0x23009012,0x2029012,0x23029012,0x49011,0x9030,0x49031,0x103814,0x23903833,0x2164013,0x164034,0x964034,0x3244013,0x244034,0xa44034,0x165014,0x965014,0x25165033,0x185014,0x985014,0x25185033,0x185814,0x985814,0x6985833,0x22245813,0x245834,0xa45834,0x1c6814,0x9c6814,0x249c6833,0x1e6814,0x9e6814,0x61e6833,0x1e7014,0x9e7014,0x61e7033] : List Nat).map readScheme

def table523_0 : List Nat := [0x60402,0x70402,1089,1217,1473,1729,0x8602,0x18782,2113,2753,0x28c02,0x110d82,0x120d82,0x148e02,0x160e02,0x170e02]

def table523_1 : List Nat := [0x188e82,0x190e82,0x1a0e82,0x3b1c8dc3,0x110f02,0x128f02,0x148f82,0x160f82,0x178f82,0x189002,0x191002,0x1a9002,0x411f8f43,0x15000103,4226,0x10c5a23140505]

def table523_2 : List Nat := [0x10c6623180505,0x10c662d180505,4417,4545,4673,4801,0x261382,5057,5185,5825,6465,0x39882,0x291982,0x2a1982,0x2c1982,0x2e1a02]

def table523_3 : List Nat := [0x2f1a02,0x301a02,0x319a82,0x6b3499c3,0x299b02,0x2a1b02,0x2c1b02,0x2e9b82,0x2f1b82,0x301b82,0x319c02,0x71379b43,0x4a102,0x3a2302,0x3b2302,0x3da382]

def table523_4 : List Nat := [0x3f2382,0x402382,0x42a402,0x442402,0x452402,0x9147a343,0x392482,0x3a2482,0x3c2482,0x3da502,0x3e2502,0x3f2502,0x412502,0x42a582,0x432582,0x442582]

def table523_5 : List Nat := [0x974aa4c3,0x392602,0x3aa602,0x3da682,0x3e2682,0x3fa682,0x432702,0x44a702,0x9d4da643,0x3aa782,0x3b2782,0x3da802,0x3fa802,0x402802,0x44a882,0x452882]

def table523_6 : List Nat := [0xa350a7c3,0x1d010203,0x12902,0x294fa733d0705,0x2950e73420705,0x2950e7d420705,0x57030203,0x32982,0x29d02773d1585,0x29d1677421585,0x29d1681421585,0x2a41,0x2ac1,0x2b41,0x2bc1,0x2e41]

def table523_7 : List Nat := [0x5b002,0x583182,0x593182,0x5a3182,0x5bb202,0x5d3202,0x5e3202,0x5f3202,0x60b282,0x613282,0x623282,0xcb64b1c3,0x583302,0x59b302,0x5a3302,0x5bb382]

def table523_8 : List Nat := [0x5d3382,0x5eb382,0x5f3382,0x60b402,0x613402,0x62b402,0xd167b343,0x27020283,0x23482,0x34d76b15b0985,0x34d86b1600985,0x34d86bb600985,0x3541,0xdb6cb5c3,0xdd223583,0xdd233603]

def table523_9 : List Nat := [0xdd243683,0x37c1,0xe006b783,0xe207b783,0xe973b943,0xea3ab903,0xea3fb983,0x42ba02,0xf177bb43,0xcbc02,0xf77abcc3,0xf9283c83,0xf92d3d03,0xf9323d83,0xff7ebec3,0x101093e83]

def table523_10 : List Nat := [0x1010b3f03,0xcbf82,0x1010d3f83,0x10782c0c3,0x1083bc083,0x10a3cc083,0x10840c103,0x10a41c103,0x42c182,0x11187c343,0xcc402,0x1178ac4c3,0x1185ac483,0x11b574483,0x1185fc503,0x11b5c4503]

def table523_11 : List Nat := [0x60c582,0x1218fc743,0xfc802,0x48c1,0x125254883,0x12626c883,0x12d95ca43,0xfcb02,0x13398cbc3,0x1342acb83,0x1362ccb83,0x1342fcc03,0x13630cc03,0x31cc82,0x13d9dce43,0xfcf02]

def table523_12 : List Nat := [0x143a0cfc3,0x145544f83,0x145555003,0x145565083,0x14ba4d1c3,0x14c11d183,0x14f105183,0x14c16d203,0x14f155203,0x18d282,0x155a9d443,0x42d502,0x1576f3503,0xeb6e5583,0x10070d603,0x159813903]

def table523_13 : List Nat := [0x159823983,0x14e71d683,0x15ba83903,0x15ba93983,0x15d7d3b03,0x15d7e3b83,0x1097c5703,0x15f863b03,0x15f873b83,0x1197c5783,0x161863e83,0x161873f03,0x11a85d803,0x14d805883,0x163a84083,0x163a94103]

def table523_14 : List Nat := [0x165944703,0x165954783,0x135925903,0x1679c4703,0x1679d4783,0x14493d983,0x1699c4a03,0x1699d4a83,0x1449bda03,0x5141,0x4041,0x3e41,0x3741,0x180d3133304,0x180d3132ec4,0x23002]

def table523_15 : List Nat := [0x8bc6c2,0xb26199cd84,0x5a67b2db2c785,0x4865b3db4d945,0xb26190cb67a552fccc8,0x6b389783,0x6b389503,0x13a840121c4,0x13a95420084,0x6b389803,0x25b3d9098c4,0x11684508184,0x3187c2,0x8b422503,0x844a8083,0x45a102]

def table523_16 : List Nat := [0x391f8883,0x86300a0b04,0x3b208a43,0x180002,0x1a3178c3204,0x196d18bc604,0x20f4813b8185,0x422502,0x91519ec3,0x20f40648a785,8449,0xaed85e35f88be86,0x2bb61af8644,0xa5d3c2,0x1cc2d11d2c4,0x10bae8c03]

def table523_17 : List Nat := [0x3b208883,8961]

def encoded523 (i : Nat) : Nat :=
  if i < 144 then
    if i < 64 then
      if i < 32 then
        if i < 16 then
          table523_0.getD (i%16) 0
        else
          table523_1.getD (i%16) 0
      else
        if i < 48 then
          table523_2.getD (i%16) 0
        else
          table523_3.getD (i%16) 0
    else
      if i < 96 then
        if i < 80 then
          table523_4.getD (i%16) 0
        else
          table523_5.getD (i%16) 0
      else
        if i < 112 then
          table523_6.getD (i%16) 0
        else
          if i < 128 then
            table523_7.getD (i%16) 0
          else
            table523_8.getD (i%16) 0
  else
    if i < 208 then
      if i < 176 then
        if i < 160 then
          table523_9.getD (i%16) 0
        else
          table523_10.getD (i%16) 0
      else
        if i < 192 then
          table523_11.getD (i%16) 0
        else
          table523_12.getD (i%16) 0
    else
      if i < 240 then
        if i < 224 then
          table523_13.getD (i%16) 0
        else
          table523_14.getD (i%16) 0
      else
        if i < 256 then
          table523_15.getD (i%16) 0
        else
          if i < 272 then
            table523_16.getD (i%16) 0
          else
            table523_17.getD (i%16) 0

def book523 (i : Nat) : Clause := let n := encoded523 i; unpackLits 9 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClauses523 : inputsOK 1 523 a523 r523 (baseBook book523 233).toList=true := by decide +kernel

def rows523_0 : List Nat := [0x619b5846c609ad8006,0x5101540044f80d3c06,0x4e8a938294d8a13406,0x480911e23470891a06,0xea743d9e5147c391f51208,0x3c9d90271449fd0c8445bb4f60a,0x1e90a7538a290886403b9da88439c0f60d,0x15e6f569b95604,0x5e2e97002,0x72ba56a2613acd7ce65b385c80a,0x1ceb67038dcae95a8984eb358bc97c0c,0x5dae5c4b412acde6e874bc5700a,0xb066301d8e06805,0xbc662d1d8d46e05,0x5432944c862308f0b007,0xc4542314cb052239409cf7308f0c60c,0xb066311d8e46805,0x5e33170ec6cf47cbd9ea321d2f46e0c,0x4322904d43e30168d267330f0bc0b,0xb75fac9f403,0xac652a944c66225124c2077e0adf65c258f0b010,0x13cae4632188acf8308f0a009,0x1a8ce661e3ec56fa5bafd64077f3f4ba0d,0x48260b0e0503605]

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk523_0 : checkRows book523 9 233 rows523_0=true := by decide +kernel

def rows523_1 : List Nat := [0x3026110e06841000705c2a09,0x30260d0e0582a05,0x784c161c0a07e04110d086021e0e828300e,0x7e43204ecab571dd5807,0x2090c7d392ad58733dc115c09,0x33998d002,0x158ca552898cc44a3081df82b831248245220f4b25a3017dfa5c258f0b019,0xf48a3f3016cb205,0x413419cb4661e9648a07,0x201707c6833974c10984110beff330adf4b75fac80efe838f08a16,0x152da4c351b004,0x2a5b6986aa79430b4caa9ae09,0x19009630218804,0x31d8add6f32996d368c35260151aa214d0673a92400012458815,0x1b8f06cc14f083583bc14eb0340e180c,0x3c260b0e0503005,0xc09838381787440201964c3d4a482813496966b2907ca3543419cea4900004944bc292acd76331228c1ebac2a27]

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk523_1 : checkRows book523 9 257 rows523_1=true := by decide +kernel

def lastUnits523 := digits 9 53 0xc09838381763b118add6fb2996d268c35929300c40201987a9c98502691d2ad65310546a867b39d4920000928974b335d8cc48a3080452142a22eb

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflict523 : checkReasons book523 274 21 lastUnits523 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem exclude523 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 523=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=1) h hc bp eq (by decide +kernel)
  let v := truth Z a523
  have hbase : ValidThrough v book523 233 := book_start Z h hc z eq _ _ _ _ initialClauses523
  have h0 : ValidThrough v book523 257 := rows_sound hbase rows523_0 rowsOk523_0
  have h1 : ValidThrough v book523 274 := rows_sound h0 rows523_1 rowsOk523_1
  exact book_end h1 _ _ conflict523
end Compact

namespace Compact
open PEqualNP.Outside.L_meta_9774_aux.DagTools Resolution

def a534 := ([0x2802,0x5002,0x6802,1,2049,4097,129,0xa0081,0x5887,0xa00a1,161,0xc00a1,0x68a3,0xa08a1,2209,0xc08a1,4256,0x90a7,0x290a7,0x490a7,0x48a8,0x8048a8,0x10048a8,0x6943,4416,0xa01a1,0x1001a1,0x1401a1,2464,0xa09a1,0x1009a1,0x1409a1,4512,0xa11a1,0x1011a1,0x1411a1,0x51a7,0x251a7,0x451a7,0x4409a8,0xc409a8,0x14409a8,0x3a11a8,0xba11a8,0x13a11a8,0x4011a8,0xc011a8,0x14011a8,0xa6809,0x146809,2053,0x20805,0x40805,2054,2085,0x20825,0x40825,0x5005,0x5006,0xa5006,0x5025,0x25025,0x45025,0x7005,0x27005,0x47005,0x7006,0xa7006,0x7025,0x27025,0x47025,0x5024,0x7024,0x7144] : List Nat).toArray.map readFact

def r534 := ([0,2048,4096,0x160089,0x162889,0x5885,160,2208,163,0x2400a9,0x2430a9,0xa400a9,0xa430a9,0x490a7,0x90a5,0x48aa,0xc48aa,0x200048aa,0x200c48aa,0x10048a8,0x48a6,323,0x1441a9,0x1451a9,0x251a7,0x9441a9,0x9451a9,0x451a7,0x11441a9,0x11451a9,0x51a5,0x110a09aa,0x111009aa,0xc409a8,0x310a09aa,0x311009aa,0x14409a8,0x510a09aa,0x511009aa,0x4409a6,0xe8a11aa,0xe9011aa,0xba11a8,0x2e8a11aa,0x2e9011aa,0x13a11a8,0x4e8a11aa,0x4e9011aa,0x3a11a6,0x101011aa,0x101411aa,0xc011a8,0x301011aa,0x301411aa,0x14011a8,0x501011aa,0x501411aa,0x4011a6,0x29ae,0xa680c,0x8029af,0x10029af,0x10229af,0x851ad,0x14680b,0x14680c,0x8051af,0x10051af,0x10251af,2064,0x20000812,0x20020812,0x20040812,2096,0x40831,0x5010,0x5012,0x2805012,0x5030,0x45031,0x7010,0x7012,0x22807012,0x27012,0x22827012,0x47011,0x7030,0x47031,0x20140813,0x140834,0x940834,0x201c0813,0x1c0834,0x9c0834,0x29c5013,0x1c5034,0x9c5034] : List Nat).map readScheme

def table534_0 : List Nat := [449,577,705,0x30402,0x38402,1089,1217,1729,0x4802,0x50882,0x58882,0x70902,0x78902,0x84982,0x9c948c3,0x50a02]

def table534_1 : List Nat := [0x5ca02,0x70a82,0x7ca82,0x84b02,0xb4aca43,0xcc02,0xd1202,0xd9202,0xe5282,0xf1282,0xf9282,0x105302,0x111302,0x119302,0x1352d243,0xc9382]

def table534_2 : List Nat := [0xd1382,0xe5402,0xe9402,0xf1402,0x105482,0x109482,0x111482,0x14d453c3,0xc9502,0xd5502,0xe5582,0xe9582,0xf5582,0x105602,0x109602,0x115602]

def table534_3 : List Nat := [0x1655d543,0xd5682,0xd9682,0xe5702,0xf5702,0xf9702,0x105782,0x115782,0x119782,0x17d756c3,0x6400103,6146,0x184eccce0605,0x1850ccd00605,0x1850ced00605,3009]

def table534_4 : List Nat := [0x15882,0x9882,0x18cfcdce0b85,0x18d1cdd00b85,0x18d1cfd00b85,0x1a59d943,0x1ac19903,0x1ac21983,0x1ac29a03,0x1c5bdb43,0xc5c02,7361,0x1d035c83,0x1d83dc83,0x1f5ede43,0xc5f02]

def table534_5 : List Nat := [0x20e05fc3,0x21055f83,0x21c49f83,0x21076003,0x21c6a003,0x86082,0x2362e243,0xc6302,0x1d5aa383,0x23de1b03,0x23de9b83,0x215aa403,0x24621b03,0x24629b83,0x219de483,0x24e21e03]

def table534_6 : List Nat := [0x24e29e83,6849,0x18d2d683,0x18ce42,0x18d6d1d284,0x1258d6d1c4,0x18cd82,6337,0x1014d0c004,0x760c56104,0x2464db03,0x2464c2,0x20e1c2,0x9cb4503,2113,0x101582]

def table534_7 : List Nat := [0x1014c2,4097,3201,5505]

def encoded534 (i : Nat) : Nat :=
  if i < 64 then
    if i < 32 then
      if i < 16 then
        table534_0.getD (i%16) 0
      else
        table534_1.getD (i%16) 0
    else
      if i < 48 then
        table534_2.getD (i%16) 0
      else
        table534_3.getD (i%16) 0
  else
    if i < 96 then
      if i < 80 then
        table534_4.getD (i%16) 0
      else
        table534_5.getD (i%16) 0
    else
      if i < 112 then
        table534_6.getD (i%16) 0
      else
        table534_7.getD (i%16) 0

def book534 (i : Nat) : Clause := let n := encoded534 i; unpackLits 8 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClauses534 : inputsOK 1 534 a534 r534 (baseBook book534 97).toList=true := by decide +kernel

def rows534_0 : List Nat := [0x24028e063008a06,0x7591b3c598bf8607,0x71b9786e1b396788c3f3c0b,0x221a7ee5a196c06,0x886dfb96e70f646a08,0x3278eb97194bb26808,0x1c3672d711a859b1bf860a,0x44f8fbd76ea0674e08,0x29d1a002,0x15abdc9d3cac1cf66c4c06165e1c00f,0x2b57bb3a7dab13018597864ca2b073eabe12,0xa81e906a004,0xc1c24a0f2405,0x2870b28474ed1a4ede1d77b6559a102cb2013,0x12be46b0fbc76ad53a11ba0674e0e,0x76894214e814b05da37ba11ba0677810,0x3b4aa182f4dc37ba11ba0677a0d,0x469d21f60b78a85808,0x3c76af92a11ba0677409]

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk534_0 : checkRows book534 7 97 rows534_0=true := by decide +kernel

def lastUnits534 := digits 7 20 0x76893a441c8c1e36594b05bc79ba11ba067

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflict534 : checkReasons book534 116 60 lastUnits534 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem exclude534 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 534=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=1) h hc bp eq (by decide +kernel)
  let v := truth Z a534
  have hbase : ValidThrough v book534 97 := book_start Z h hc z eq _ _ _ _ initialClauses534
  have h0 : ValidThrough v book534 116 := rows_sound hbase rows534_0 rowsOk534_0
  exact book_end h0 _ _ conflict534
end Compact

namespace Compact
open PEqualNP.Outside.L_meta_9774_aux.DagTools Resolution

def a645 := ([0x2802,0x4002,0x5002,0x40a3,4256,0xa0101,0x140101,0x5103,0x1a0101,2304,0xa0901,0x140901,0x1a0901,4352,0xa1101,0x141101,0x1a1101,0xd907,0x2d907,0x4d907,0xf907,0x2f907,0x4f907,0x3a1108,0xba1108,0x13a1108,0x4c1108,0xcc1108,0x14c1108,0xa4009,0x144009,0x140121,0x180121,0x3927,0x9127,0x140141,0x100141,0x180141,0x140941,0x100941,0x180941,4416,0xb147,0x2b147,0x4b147,0x340148,0xb40148,0x1340148,0x180181,0x180981,0x181181,0x6805,0x26805,0x46805,0x6825,0x146826,0x186826,0x7005,0x27005,0x47005,0x7025,0x27025,0x47025,0x147026,0x187026,0x7805,0x27805,0x47805,0x7825,0x27825,0x47825,0x187826,0x71a4,0x79a4,0x79c4] : List Nat).toArray.map readFact

def r645 := ([163,0x362909,0x366909,0x2d907,0xb62909,0xb66909,0x4d907,0x1362909,0x1366909,0xd905,0x3e5109,0x3e6909,0x2f907,0xbe5109,0xbe6909,0x4f907,0x13e5109,0x13e6909,0xf905,0xe8a110a,0xe9a110a,0xba1108,0x2e8a110a,0x2e9a110a,0x13a1108,0x4e8a110a,0x4e9a110a,0x3a1106,0x1314110a,0x131a110a,0xcc1108,0x3314110a,0x331a110a,0x14c1108,0x5314110a,0x531a110a,0x4c1106,0x290e,0xa400c,0x80290f,0x100290f,0x102290f,0x510d,0x14400b,0x14400c,0x80510f,0x100510f,0x102510f,0xe5129,0x3925,0x246129,0x9125,320,2368,323,0x2c4149,0x2c6149,0xac4149,0xac6149,0x4b147,0xb145,0xd10014a,0xd18014a,0x2d10014a,0x2d18014a,0x1340148,0x340146,384,2432,4480,0x6810,0x46811,0x6830,0x5006832,0x6006832,0x7010,0x47011,0x7030,0x25007032,0x6007032,0x25027032,0x6027032,0x47031,0x7810,0x47811,0x7830,0x26007832,0x26027832,0x26047832,0x1c6814,0x9c6814,0x51c6833,0x1e6814,0x9e6814,0x61e6833,0x1e7014,0x9e7014,0x61e7033] : List Nat).map readScheme

def table645_0 : List Nat := [0x4202,0x28882,0x40882,0x4c902,0x50902,0x60902,0x6c982,0x70982,0x80982,0x9c948c3,0x30a02,0x40a02,0x4ca82,0x58a82,0x60a82,0x6cb02]

def table645_1 : List Nat := [0x78b02,0x80b02,0xb4aca43,0x28b82,0x44b82,0x4cc02,0x50c02,0x64c02,0x6cc82,0x70c82,0x84c82,0xccc4bc3,0x30d02,0x44d02,0x4cd82,0x58d82]

def table645_2 : List Nat := [0x64d82,0x6ce02,0x78e02,0x84e02,0xe4dcd43,0x1c00083,3714,0xec542c48185,0xec742c68185,0xec745468185,961,0xcf02,0x10f02,0xf45c3448385,0xf47c3468385,0xf47c5c68385]

def table645_3 : List Nat := [0xf9082,4289,0x101102,4417,4545,4929,0x15482,0x121502,0x129502,0x139582,0x141582,0x14d602,0x1655d543,0x125682,0x129682,0x13d702]

def table645_4 : List Nat := [0x141702,0x14d782,0x17d756c3,6209,6337,6465,0x1ada59c3,0x25a82,6977,0x1b8fdb03,0x1c105b03,0x1ddd5cc3,0x25d82,0x1f5ede43,0x1fd19e03,0x2012de03]

def table645_5 : List Nat := [0x1fd31e83,0x20145e83,0x14df02,0x21e160c3,0x26182,0x2362e243,0x23d82203,0x23d8a283,0x23d92303,0x245c9983,0x245d1a03,0x1f9be403,0x24e09983,0x24e11a03,0x239c6483,0x25609c83]

def table645_6 : List Nat := [0x25611d03,0x23a06503,9153,0x1f5fc2,0x82c5448005,0x245adde56105,0x21dae45de545,0x1657d283,0x9cb644ccd05,0x2446c2,0x6848f4ac345,0x68f448ac4,0x68f4483,0xf4e02,0x68f42,0x1657d403]

def table645_7 : List Nat := [0x12d45f6004,0x244242,0x684800bc2c5,0x6800e4444,0x8c68ec18cc506,0x68ac404,0xec1868bc905,0x6800443,0xec1868c48cbc6,9281,1025]

def encoded645 (i : Nat) : Nat :=
  if i < 64 then
    if i < 32 then
      if i < 16 then
        table645_0.getD (i%16) 0
      else
        table645_1.getD (i%16) 0
    else
      if i < 48 then
        table645_2.getD (i%16) 0
      else
        table645_3.getD (i%16) 0
  else
    if i < 96 then
      if i < 80 then
        table645_4.getD (i%16) 0
      else
        table645_5.getD (i%16) 0
    else
      if i < 112 then
        table645_6.getD (i%16) 0
      else
        table645_7.getD (i%16) 0

def book645 (i : Nat) : Clause := let n := encoded645 i; unpackLits 8 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClauses645 : inputsOK 1 645 a645 r645 (baseBook book645 98).toList=true := by decide +kernel

def rows645_0 : List Nat := [0x2c45af12b43aa06,0xa0d67349a04,0x13254e02,0x2f6294c99c88d665e0ba0a,0xb52efdcbd8a53267229e58c0c,0x3978e213e7e05,0x1bbc750a0519b4a7e1c59aa47980322b266cb85099ddc16cb168d242ce031208eaa7a26,0x6ef1d4281466d29f87166a91e600c8ac09636501090b9ddc16cb169f14487203c910e80c3cc2a7a2c,0xb24412225c7d6aa3a09,0x179054911912428e6a3e0a,0x225e8071c5a375aa4809,0x11463360a5c890aa2409,0x4171c543059d49b4f6c240b,0x3778ea1407a05,0x28cf9a02,0x19f7bb8349b2cdda70e2cd523cce00f,0x509929b2d915ec3208,0x14a60e955ee36684090a800f23c90e942c12,0x389084cd965006,0x1383365c2890ea7a26344490b4aaf7022612,0x29086cb853205,0x65415e40448847cfb264aaf714360f,0x346c4f61004,0x1d4044e4fc262e386754aaf702efa40711213]

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk645_0 : checkRows book645 7 98 rows645_0=true := by decide +kernel

def rows645_1 : List Nat := [0x2d1a4878b06a926d4014486dcb1b52c76e4b06323c823819]

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk645_1 : checkRows book645 7 122 rows645_1=true := by decide +kernel

def lastUnits645 := digits 7 26 0x78e2e2969f49b4e95366372c6d4b1db92c18c8f253d2a

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflict645 : checkReasons book645 123 18 lastUnits645 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem exclude645 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 645=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=1) h hc bp eq (by decide +kernel)
  let v := truth Z a645
  have hbase : ValidThrough v book645 98 := book_start Z h hc z eq _ _ _ _ initialClauses645
  have h0 : ValidThrough v book645 122 := rows_sound hbase rows645_0 rowsOk645_0
  have h1 : ValidThrough v book645 123 := rows_sound h0 rows645_1 rowsOk645_1
  exact book_end h1 _ _ conflict645
end Compact

namespace Compact
open PEqualNP.Outside.L_meta_9774_aux.DagTools Resolution

def a660 := ([0x2802,0x4002,0x5002,0x6002,0x6802,1,2049,4097,0x40041,0x60041,0xa0041,4167,0x60061,0x60861,0x61061,129,0x40081,0xa0081,0x5887,0xa00a1,161,0x600a1,0xc00a1,0x40a3,0x68a3,0xa08a1,2209,0x608a1,0xc08a1,4256,0x90a7,0x290a7,0x490a7,0xf8a7,0x2f8a7,0x4f8a7,0xc00c1,0xc08c1,0xc10c1,0x100101,0xa0101,0x1a0101,2304,0x100901,0xa0901,0x1a0901,4352,0xa1101,0x1a1101,0xd907,0x2d907,0x4d907,0x3a1108,0xba1108,0x13a1108,0xa4009,0x140121,0x180121,0x3927,0x9127,0x140141,0x6143,0x140941,4416,0x141141,0x180181,0x100181,0x140181,2432,0x180981,0x100981,0x140981,4480,0x101181,0x141181,0x5187,0x25187,0x45187,0x341188,0xb41188,0x1341188,0x146009,0xa01a1,0x1001a1,0x1401a1,2464,0xa09a1,0x1009a1,0x1409a1,4512,0xa11a1,0x1011a1,4519,0x211a7,0x411a7,0x51a7,0x251a7,0x451a7,0xa6809,2053,0x20805,0x40805,2054,2085,0x20825,0x40825,8197,8229,0x22025,0x42025,0xa2026,0x102026,0x2805,0x62806,0xa2806,0x2825,0x22825,0x42825,0x3005,0x43006,0x3025,0x23025,0x43025,0xa3026,0x103026,0x4805,0x24805,0x44805,0x64806,0x4825,0x24825,0x44825,0x5005,0x5006,0xa5006,0x5025,0x25025,0x45025,0x145026,0x6005,0x46006,0x6025,0x26025,0x46025,0x146026,0x6805,0x26805,0x46805,0xc6806,0x6825,0x146826,0x186826,0x7005,0x27005,0x47005,0x7006,0xa7006,0x7025,0x27025,0x47025,0x147026,0x7805,0x27805,0x47805,0x67806,0xa7806,0x7825,0x27825,0x47825,0x187826,0x8805,0x28805,0x48805,0xc8806,0x8825,0x5024,0x7024,0x3084,0x48a4,0x78a4,0x60c4,0x7924,0x6144,0x7144,0x71a4,0x79a4,0x89a4] : List Nat).toArray.map readFact

def r660 := ([0,2048,4096,64,0x41849,0x42849,4165,96,2144,4192,0x160089,0x161089,0x162889,0x5885,160,2208,163,0x2400a9,0x2430a9,0xa400a9,0xa430a9,0x490a7,0x90a5,0x3e18a9,0x3e30a9,0xbe18a9,0xbe30a9,0x4f8a7,0xf8a5,192,2240,4288,256,2304,259,0x362909,0x366909,0x2d907,0xb62909,0xb66909,0x4d907,0x1362909,0x1366909,0xd905,0xe8a110a,0xe9a110a,0xba1108,0x2e8a110a,0x2e9a110a,0x13a1108,0x4e8a110a,0x4e9a110a,0x3a1106,0x290e,0xa400c,0x80290f,0x100290f,0x102290f,0xe5129,0x3925,0x246129,0x9125,320,2368,4416,323,384,2432,387,0x144189,0x145189,0x25187,0x944189,0x945189,0x1144189,0x1145189,0x5185,0xd10118a,0xd14118a,0xb41188,0x2d10118a,0x2d14118a,0x4d10118a,0x4d14118a,0x341186,0x518e,0x14600c,0x80518f,0x100518f,0x102518f,419,0x429a9,0x441a9,0x211a7,0x8429a9,0x8441a9,0x10429a9,0x10441a9,4517,0x1441a9,0x1451a9,0x9441a9,0x9451a9,0x451a7,0x51a5,0x29ae,0xa680c,0x8029af,0x10029af,0x10229af,2064,0x20000812,0x20020812,0x20040812,2096,0x40831,8208,8240,0x2802032,0x24002032,0x2822032,0x24022032,0x42031,0x2810,0x1802812,0x2802812,0x2830,0x42831,0x3010,0x21003012,0x3030,0x22803032,0x4003032,0x23031,0x22823032,0x4023032,0x43031,0x22843032,0x4043032,0x4810,0x21804812,0x21824812,0x21844812,0x4830,0x44831,0x5010,0x5012,0x2805012,0x5030,0x25005032,0x25025032,0x45031,0x25045032,0x6010,0x1006012,0x6030,0x5006032,0x5026032,0x46031,0x6810,0x3006812,0x3026812,0x46811,0x6830,0x5006832,0x6006832,0x7010,0x7012,0x22807012,0x27012,0x22827012,0x47011,0x7030,0x25007032,0x25027032,0x47031,0x7810,0x1807812,0x22807812,0x1827812,0x22827812,0x47811,0x7830,0x26007832,0x26027832,0x47831,0x8810,0x23008812,0x23028812,0x23048812,0x8830,0x20140813,0x140834,0x940834,0x201c0813,0x1c0834,0x9c0834,0xc2014,0x28c2033,0x240c2033,0x1922813,0x122834,0x922834,0x29e2813,0x1e2834,0x9e2834,0x21183013,0x183034,0x983034,0x219e4813,0x1e4834,0x9e4834,0x185014,0x25185033,0x29c5013,0x1c5034,0x9c5034,0x1c6814,0x9c6814,0x51c6833,0x1e6814,0x9e6814,0x61e6833,0x3226813,0x226834] : List Nat).map readScheme

def table660_0 : List Nat := [705,833,961,1089,0x90582,0xa0582,1473,1601,1729,1857,0xf0902,0x100902,0x110902,2369,2497,3265]

def table660_1 : List Nat := [0x8e82,0x140f02,0x160f02,0x1a0f82,0x1c0f82,0x1d9002,0x411f8f43,0x151082,0x161082,0x1b1102,0x1c1102,0x1d9182,0x472290c3,4673,4801,4929]

def table660_2 : List Nat := [5057,5569,0x19702,0x281882,0x291882,0x2a9902,0x2c1902,0x2d1902,0x2e9982,0x2f1982,0x301982,0x673298c3,0x281a02,0x299a02,0x2a9a82,0x2c1a82]

def table660_3 : List Nat := [0x2d9a82,0x2e9b02,0x2f1b02,0x309b02,0x6d359a43,0x2f000083,7042,0x1bcb2512a0b85,0x1bcbe512e0b85,0x1bcbe592e0b85,0x381d02,7489,0x391d82,7617,7745,8001]

def table660_4 : List Nat := [8257,0x29f82,8385,8897,0x3a402,0x422582,0x432582,0x44a602,0x462602,0x472602,0x492682,0x4a2682,0x9b4ca5c3,0x42a702,0x432702,0x44a782]

def table660_5 : List Nat := [0x46a782,0x472782,0x49a802,0x4a2802,0xa14fa743,0x7b020183,0x22882,0x28d1e87441e85,0x28d2a87481e85,0x28d2a8f481e85,0x4ac82,0x522e02,0x532e02,0x55ae82,0x562e82,0x572e82]

def table660_6 : List Nat := [0x5a2f02,0x5b2f02,0xbd5dae43,0x532f82,0x542f82,0x573002,0x583002,0x59b082,0xc360afc3,0x31000203,0x3102,0x3155aa5550c05,0x3156aa5590c05,0x3156aad590c05,0xcb64b1c3,0xcd053183]

def table660_7 : List Nat := [0xcd063203,0xcd073283,0xd368b3c3,0x3fb482,0x3541,0xdb6cb5c3,0xdc28b583,0xdf273583,0xdc2cb603,0xdf2b3603,0x2eb682,0x3841,0xe209b803,0xe40ab803,0xeb74b9c3,0x48ba82]

def table660_8 : List Nat := [0x3b41,0xef083b03,0xf579bc43,0xf7523c03,0xf853bc03,0x55bc82,0xf7563c83,0xf857bc83,0x59bd02,0xf75a3d03,0xf85bbd03,0xff7ebec3,0x1010c3e83,0x1010d3f03,0x1010e3f83,0x10782c0c3]

def table660_9 : List Nat := [0x48c182,0x4241,0x10a0fc203,0x10c11c203,0x11388c3c3,0x1153c4383,0x1153e4403,0x3fc482,0x115404483,0x45c1,0x11810c583,0x11f8ec6c3,0x12054c683,0x12058c703,0x59c782,0x12792c8c3]

def table660_10 : List Nat := [0x12816c883,0x1281cc903,0x1dc982,0x4ac1,0x12c38ca83,0x12e39ca83,0x13599cc43,0x13614cc03,0x139134c03,0x1361acc83,0x139194c83,0x1dcd02,0x13f9ecec3,0x1413c4e83,0x1413e4f03,0x3fcf82]

def table660_11 : List Nat := [0x147a2d0c3,0x14815d083,0x14b135083,0x1481bd103,0x14b195103,0x1dd182,0x151a7d343,0x153415303,0x153455383,0x48d402,0x159abd543,0x15b245503,0x15b255583,0x15b265603,0x5741,0x10b665783]

def table660_12 : List Nat := [0x15f873383,0x15f883403,0x137665803,0x1619d3383,0x1619e3403,0x163763503,0xf66ed883,0xf96f5883,0x10071d903,0x165813983,0x165823a03,0x14a72d983,0x167a63983,0x167a73a03,0x119775a03,0x1698d3c03]

def table660_13 : List Nat := [0x1698e3c83,0x149805a83,0x16ba64083,0x16ba74103,0x16d8b4203,0x1218a5b03,0x13886db83,0x16f9d4383,0x16f9e4403,0x171984883,0x171994903,0x14096dc03,0x173a14883,0x173a24903,0x15297dc83,0x15a94dd03]

def table660_14 : List Nat := [0x175ae4a83,0x56c1,0x4541,0x2c9b03,0x6db7c2,0x67369403,0x67001603,0x67369543,0xb2516db704,0x9b50a243,0x120a33d23c4,0x1467a482584,0x22402,0xa55aac84,0x3e14a005dbc05,0x1ee0052bd04]

def table660_15 : List Nat := [0x3dd8aa5183c85,0x3ddf000528c05,0x1f11f61bc04,0x1eef8002944,0xf878acc3,0xf77c31460b25cbc87,0xf77c0003,0x8240245471bd386,0x4782402a347734887,0x15c02a304735086,0xeb9391ea347824007,0x4041,0x9fd042,0x3341,0x91dc626d39e0ec6,0x3700051369645]

def table660_16 : List Nat := [0x289983,0xdc001443,0x500019c3,0x7c0002,0x34e7f13918ec5,6530,1,0x248e8a8d104,0x922442,0x48c1,0x586ded389ce85,8129,0x5301]

def encoded660 (i : Nat) : Nat :=
  if i < 128 then
    if i < 64 then
      if i < 32 then
        if i < 16 then
          table660_0.getD (i%16) 0
        else
          table660_1.getD (i%16) 0
      else
        if i < 48 then
          table660_2.getD (i%16) 0
        else
          table660_3.getD (i%16) 0
    else
      if i < 96 then
        if i < 80 then
          table660_4.getD (i%16) 0
        else
          table660_5.getD (i%16) 0
      else
        if i < 112 then
          table660_6.getD (i%16) 0
        else
          table660_7.getD (i%16) 0
  else
    if i < 192 then
      if i < 160 then
        if i < 144 then
          table660_8.getD (i%16) 0
        else
          table660_9.getD (i%16) 0
      else
        if i < 176 then
          table660_10.getD (i%16) 0
        else
          table660_11.getD (i%16) 0
    else
      if i < 224 then
        if i < 208 then
          table660_12.getD (i%16) 0
        else
          table660_13.getD (i%16) 0
      else
        if i < 240 then
          table660_14.getD (i%16) 0
        else
          if i < 256 then
            table660_15.getD (i%16) 0
          else
            table660_16.getD (i%16) 0

def book660 (i : Nat) : Clause := let n := encoded660 i; unpackLits 9 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClauses660 : inputsOK 1 660 a660 r660 (baseBook book660 225).toList=true := by decide +kernel

def rows660_0 : List Nat := [0x5e87d781e5d8757406,0x4c1012c3f4a8f92806,0xe46c32110c46a05,0xf2213b880ea04,0x9c56231a0b06005,0x70361908c44311a0bc5a24158986a0c,0x9056251a0b85a05,0x3c1d8ea02,0x11498472a13c9a05,0x241308c542715dd24b29964a00a,0x532c118a2ea26914a807,0x160965429128984975945d4562a9109c0d,0x6a34968d803,0x1aae26a244cc683398d369e76980c45c4233d9c9a05835328101a013a18,0x44a21da02,0x43214d602,0x5e2ebb904ef781a8d607,0x6ab89a891331a0c6844db3d9c9a05835328101a013a12,0x4e355c4d448a6da0ce4d02c1a994080d006832a1d04ef79278ce5a34bc4c81a,0x4e355c4d448a6d3cd067268160d4ca0406803419cca8741220c816,0x1b50c622fa1cc005,0x36a24c46145209ea6a34969e8832dbccbc0e,0xb368b4db8de5c10d4a3c1ea8d600b,0x659f40a063db301eb06e3796e425b3dc321c0c281bee1702f94a3c1ea8d681a]

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk660_0 : checkRows book660 9 225 rows660_0=true := by decide +kernel

def rows660_1 : List Nat := [0xcb59038fa05031ed6cd368ac5980b,0x3794a3c1eb7486b66632d680f583e42e1c0d285bee1702f9469f7c1f40a7e65320f804031ed7021,0x470251a084601d1606,0x15c3f568f95804,0x38808e00137800dc06,0x184a7088582a1450b7dc2e05f28ce4c05fa4814fd4a361aca80729956da4fa89260c06a458820,0x70e71b8d86a223d3a05208,0xe06c29110a06a05,0xff73401c603,0x73395c602,0xd8522f1a0cc542c1a888510280b19ecc5401d07211,0xc15fa4814946bb59500e498301a9161b094e110b05428a16fb85c0be532adb49f513f558fe6dbf1483a1da8ce427,0x391b0a46a22140d0662a164005e0b,0x368139dc6e6828d4447a7231e06c5401d06e0f,0x1bca51e0f546dd212d99acb5a03cfa05031ed6e10,0x66b2d640e3e815a4d15885c381a50b7dc2e05f28d61073f325907c02018f68f483e8fea20dae56a10833ed6c26,0x39abd2e41764213ea20841a080a,0x5fa48140d48bf528d73930d820a,0xbf4902928d839311590a612a426160a84940df70b817cfd6b2a81ea6558420cd96dbf15ea41d0ed4709498301a9139a5d802b,0x5986438185037dc2e05f2c1b8de5b9094a3c1ea8e12d247a41f47f5106d72ec20c2d6a10833eda222]

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk660_1 : checkRows book660 9 249 rows660_1=true := by decide +kernel

def lastUnits660 := digits 9 38 0x1680f58371bcb821a94783d51c24fa0566ada187e64b20f804031ed1e907d1fd441b5cbb0830b5a8420cfb

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflict660 : checkReasons book660 269 203 lastUnits660 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem exclude660 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 660=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=1) h hc bp eq (by decide +kernel)
  let v := truth Z a660
  have hbase : ValidThrough v book660 225 := book_start Z h hc z eq _ _ _ _ initialClauses660
  have h0 : ValidThrough v book660 249 := rows_sound hbase rows660_0 rowsOk660_0
  have h1 : ValidThrough v book660 269 := rows_sound h0 rows660_1 rowsOk660_1
  exact book_end h1 _ _ conflict660
end Compact

namespace Compact
open PEqualNP.Outside.L_meta_9774_aux.DagTools Resolution

def a778 := ([2,4098,8194,0x2802,0x3002,0x5002,0x5802,1,0x3003,2049,4096,65,0xc0041,0x3043,0x160041,2113,0xc0841,0x160841,4160,0x9047,0x29047,0x49047,0x164048,0x964048,0x1164048,0x80061,0xc0061,2151,0x80081,129,0xc0081,0x3083,0x80881,2177,0xc0881,4224,0xd887,0x2d887,0x4d887,161,0x800a1,0xc00a1,0x30a3,2209,0x808a1,0xc08a1,4256,0x90a7,0x290a7,0x490a7,0xc00c1,193,0x400c1,0x800c1,0xa00c1,0x1400c1,0x50c3,0x1600c1,0x58c3,2240,0xc08c1,2241,0x408c1,0x808c1,0xa08c1,0x1408c1,0x1608c1,4288,0xc10c1,4289,0x410c1,0x810c1,0xa10c1,0x1410c1,0x1610c1,0x48c7,0x248c7,0x448c7,0x58c7,0x258c7,0x458c7,0x40c8,0x8040c8,0x10040c8,0xe40c8,0x8e40c8,0x10e40c8,0x48c8,0x8048c8,0x10048c8,0x3009,0x43009,0x83009,0xa3009,0x143009,0x163009,0x140121,0x3927,0x140141,0x140941,4416,4448,6,0xc0006,0x160006,37,2053,0x20805,0x40805,2054,2085,0x20825,0x40825,8197,0x22005,0x42005,8198,0xc2006,0x162006,8229,0x4005,0x84006,0xc4006,0x4025,0x24025,0x44025,0x5005,0x25005,0x45005,0x5006,0x85006,0x5025,0x25025,0x45025,0x5805,0x25805,0x45805,0x5806,0x85806,0xc5806,0x5825,0x25825,0x45825,0x6805,0x26805,0x46805,0xc6806,0x6825,0x146826,0x7005,0x27005,0x47005,0x7006,0x87006,0x7025,0x27025,0x47025,0x147026,0x8005,0x28005,0x48005,0x8006,0xc8006,0x168006,0x8025,0x8805,0x28805,0x48805,0xc8806,0x8825,0x9005,0x29005,0x49005,0x9006,0x89006,0xc9006,0x9025,0x29025,0x49025,8196,0x8004,0x5024,0x7024,0x5904,0x9104,0x7144,0x9164,0x71a4,0x89a4] : List Nat).toArray.map readFact

def r778 := ([0,2048,3,67,0x240049,0x243049,0xa40049,0xa43049,0x49047,0x9045,0x580404a,0x596404a,0x2580404a,0x2596404a,0x1164048,0x164046,0x22069,0x23069,2149,128,2176,131,0x360089,0x363089,0xb60089,0xb63089,0x4d887,0xd885,163,0x2400a9,0x2420a9,0x2430a9,0xa400a9,0xa420a9,0xa430a9,0x490a7,0x90a5,192,2240,2241,4288,0x1210c9,0x1250c9,0x9210c9,0x9250c9,0x11210c9,0x11250c9,0x48c5,0x1600c9,0x1610c9,0x1628c9,0x1658c9,0x9600c9,0x9610c9,0x9628c9,0x9658c9,0x458c7,0x11600c9,0x11610c9,0x11628c9,0x11658c9,0x58c5,0x440ca,0x840ca,0xa40ca,0x200440ca,0x200840ca,0x200a40ca,0x10040c8,0x400440ca,0x400840ca,0x400a40ca,0x40c6,0x38440ca,0x39440ca,0x238440ca,0x239440ca,0x438440ca,0x439440ca,0xe40c6,0x48ca,0x448ca,0x848ca,0xa48ca,0x200048ca,0x200448ca,0x200848ca,0x200a48ca,0x10048c8,0x400048ca,0x400448ca,0x400848ca,0x400a48ca,0x48c6,0x1000cd,0x300c,0x8000cf,0x10000cf,0x10200cf,0x1010cd,0x4300b,0x4300c,0x8010cf,0x10010cf,0x10210cf,8398,0x8300c,0x8020cf,0x10020cf,0x10220cf,0x1228cd,0xa300c,0x8028cf,0x10028cf,0x10228cf,0x50ce,0x14300c,0x8050cf,0x10050cf,0x10250cf,0x58ce,0x16300c,0x8058cf,0x10058cf,0x10258cf,0xe5129,0x3925,320,2368,323,355,48,2064,0x20000812,0x20020812,0x40811,2096,0x40831,8208,0x20002012,0x3002012,0x5802012,0x20022012,0x3022012,0x5822012,0x42011,8240,0x4010,0x2004012,0x3004012,0x4030,0x44031,0x5010,0x5012,0x22005012,0x25012,0x22025012,0x45011,0x5030,0x45031,0x5810,0x20005812,0x22005812,0x3005812,0x20025812,0x22025812,0x3025812,0x45811,0x5830,0x45831,0x6810,0x3006812,0x3026812,0x46811,0x6830,0x5006832,0x7010,0x7012,0x2007012,0x27012,0x2027012,0x47011,0x7030,0x25007032,0x25027032,0x47031,0x8010,0x8012,0x23008012,0x25808012,0x28012,0x23028012,0x25828012,0x48012,0x23048012,0x25848012,0x8030,0x8810,0x23008812,0x23028812,0x23048812,0x8830,0x9010,0x9012,0x2009012,0x23009012,0x29012,0x2029012,0x23029012,0x49012,0x2049012,0x23049012,0x9030,0x49031,0x80013,0x23080013,0x25880013,0x80034,0x20200013,0x3200013,0x5a00013,0x200034,0x20140813,0x140834,0x940834,0x201c0813,0x1c0834,0x9c0834,0x2164013,0x164034,0x964034,0x3244013,0x244034,0xa44034,0x221c5013,0x1c5034,0x9c5034,0x20245813,0x22245813,0x3245813,0x245834,0xa45834,0x1c6814,0x9c6814,0x51c6833,0x3226813,0x226834] : List Nat).map readScheme

def table778_0 : List Nat := [961,1217,0x8502,0x18902,0xb0982,0xc0982,0xf0a02,0x100a02,0x128a82,0x2b1489c3,0xb8b02,0xe0b02,0xf8b82,0x110b82,0x128c02,0x31178b43]

def table778_1 : List Nat := [0x190d82,0x1a0d82,3521,3649,4161,0x29182,0x1d1202,0x1e1202,0x211282,0x221282,0x239302,0x4d259243,0x39702,0x271782,0x281782,0x291782]

def table778_2 : List Nat := [0x2b1802,0x2c1802,0x2d1802,0x2e9882,0x633097c3,6465,7745,0x3ba182,8769,0x342582,0x372582,0x3e2602,0x412602,0x462682,0x492682,0x9b4ca5c3]

def table778_3 : List Nat := [0x332702,0x342702,0x362702,0x392702,0x3d2782,0x3e2782,0x402782,0x422782,0x43a802,0x452802,0x462802,0x482802,0x4a2802,0xa14fa743,0x34a882,0x352882]

def table778_4 : List Nat := [0x362882,0x3ea902,0x3f2902,0x402902,0x43a982,0x46a982,0x472982,0x482982,0xa752a8c3,0x34aa02,0x372a02,0x3eaa82,0x412a82,0x46ab02,0x492b02,0xad55aa43]

def table778_5 : List Nat := [0x332b82,0x342b82,0x352b82,0x36ab82,0x3d2c02,0x3e2c02,0x3f2c02,0x40ac02,0x43ac82,0x452c82,0x462c82,0x472c82,0x48ac82,0xb358abc3,1089,0x2d02]

def table778_6 : List Nat := [0x2d4f6673b0405,0x2d51667430405,0x2d5167b430405,1729,0x4ad82,0x12d82,0x2dcfa693b0685,0x2dd1a69430685,0x2dd1a7d430685,0x3f020203,0x22e02,0x2e4fe6b3b0f85,0x2e51e6b430f85,0x2e51e7f430f85,5441,0x32e82]

def table778_7 : List Nat := [0x2ed026d3b1505,0x2ed226d431505,0x2ed2281431505,0x71050203,0x52f02,0x2f5066f3b1c05,0x2f5266f431c05,0x2f52683431c05,0x75060203,0x62f82,0x2fd0a733b1d05,0x2fd2a73431d05,0x2fd2a85431d05,0x603082,0x30c1,0x3141]

def table778_8 : List Nat := [0x31c1,0x5b202,0x6b282,0x34c1,0xd96bb543,0xdb073503,0xdb093583,0xab602,0xe16fb743,0x64b802,0xe772b8c3,0xe90b3883,0xea0cb883,0xec0eb883,0xe90f3903,0xea10b903]

def table778_9 : List Nat := [0xec11b903,0x12b982,0x3bc1,0x3c41,0xf219bc03,0xf41abc03,0xfb7cbdc3,0x65be82,0x1017fbf43,0x1021dbf03,0x1051c3f03,0x10221bf83,0x105203f83,0x23c002,0x10b84c1c3,0x64c282]

def table778_10 : List Nat := [0x11187c343,0x1131d4303,0x1151c4303,0x1161ec303,0x113214383,0x115204383,0x11622c383,0x23c402,0x11d8dc643,0x65c702,0x12390c7c3,0x12429c783,0x1242dc803,0x2ec882,0x49c1,0x12860c983]

def table778_11 : List Nat := [0x12f96cac3,0x13027ca83,0x13228ca83,0x1302bcb03,0x1322ccb03,0x2ecb82,0x1399bcd43,0x13b624d03,0x13b634d83,0x64ce02,0x1419fcf43,0x14233cf03,0x145324f03,0x147394f03,0x1423dcf83,0x1453c4f83]

def table778_12 : List Nat := [0x147424f83,0x14245d003,0x145445003,0x1474a5003,0x5241,0x14fa6d2c3,0x151325283,0x1513c5303,0x151445383,0x54c1,0x159abd543,0x15a33d503,0x15c35d503,0x15f325503,0x15a3dd583,0x15c3fd583]

def table778_13 : List Nat := [0x15f3c5583,0x15a45d603,0x15c47d603,0x15f445603,0x165b1d843,0x65d902,0xe866d983,0xeb675983,0xed685983,0x167773483,0x143665a03,0x14467da03,0x14668da03,0x169a43483,0x1036d5a83,0x16b833703]

def table778_14 : List Nat := [0x16b843783,0x1316d5b03,0x16d9a3703,0x16d9b3783,0x11479db83,0x16f8c3d83,0x16f8d3e03,0x15e7adc03,0x171b03d83,0x171b13e03,0x133825c83,0x1739a4183,0x1739b4203,0x15b895d03,0x15d8a5d03,0x15e8bdd03]

def table778_15 : List Nat := [0x175b04603,0x175b14683,0x177954783,0x177964803,0x13a94dd83,0x15092de03,0x179a94983,0x57c1,0x5441,0x5141,0x212e6f430285,0x210c6b478105,0x88c542,0x1d23115b884,0x14057a783,0xa01a02]

def table778_16 : List Nat := [0x69432dc3,0x6cb6c2,0x80c142,0x5d5f76f8ed805,0x16fbab2c3,0x210c95428305,0x5de5e63994805,0x5adc2639cc12472fb6c189,0x42ed6e131c12472f9cdb49,0x9ccec2,0x5de5e63984785,0x638236a472fb5b247,0x2126864d8285,0x44c9b118b0e85,0xa151aa52a08432b87,0x211e7f430105]

def table778_17 : List Nat := [0x3d479fe2267215d07,0x20e695430305,0x14071a183,0x51a1c2,0x5001,0x204fd2491c4,0x80857a984,0x101086579f85,0x10c04042bc4,0x86020203,0x865bac03,0x432dc2,0x11e6b3fd704,0x7b33d083,0x1ce2b18ba44,0x622b763904]

def table778_18 : List Nat := [0x1ce2b18bb04,0x508ed47479fe280853a789,0x20e676428305,0x106864c8284,0x3fac82,0x142599a83,0x14259a703,0x13a860619c4,0x86479fc3,0x1634252acc4,0x4323c2,0x431ec2,8577]

def encoded778 (i : Nat) : Nat :=
  if i < 144 then
    if i < 64 then
      if i < 32 then
        if i < 16 then
          table778_0.getD (i%16) 0
        else
          table778_1.getD (i%16) 0
      else
        if i < 48 then
          table778_2.getD (i%16) 0
        else
          table778_3.getD (i%16) 0
    else
      if i < 96 then
        if i < 80 then
          table778_4.getD (i%16) 0
        else
          table778_5.getD (i%16) 0
      else
        if i < 112 then
          table778_6.getD (i%16) 0
        else
          if i < 128 then
            table778_7.getD (i%16) 0
          else
            table778_8.getD (i%16) 0
  else
    if i < 224 then
      if i < 176 then
        if i < 160 then
          table778_9.getD (i%16) 0
        else
          table778_10.getD (i%16) 0
      else
        if i < 192 then
          table778_11.getD (i%16) 0
        else
          if i < 208 then
            table778_12.getD (i%16) 0
          else
            table778_13.getD (i%16) 0
    else
      if i < 256 then
        if i < 240 then
          table778_14.getD (i%16) 0
        else
          table778_15.getD (i%16) 0
      else
        if i < 272 then
          table778_16.getD (i%16) 0
        else
          if i < 288 then
            table778_17.getD (i%16) 0
          else
            table778_18.getD (i%16) 0

def book778 (i : Nat) : Clause := let n := encoded778 i; unpackLits 9 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClauses778 : inputsOK 1 778 a778 r778 (baseBook book778 247).toList=true := by decide +kernel

def rows778_0 : List Nat := [0x698a1a026668959406,0x640a18e26630958a06,0x610a17e265e0957406,0x2e3b0b0ea74139cc5e07,0x351a4d802,0x14a145104d4004,0x8c6bb6df2dd62365248304818180f0522c0a0f,0x40481d1ed76db08500f0623914917eb59b4c12cb7588d94920c1c0801994d05a1a960ba571b18c1423,0x40481d1ed76db08500f0623914917eb59b4c11cb7588d94920c1c0801994d03a2a974b83b1c0f5fc511898c1427,0x321e8e86a5d2d19caa661398ca60b,0x10c01428010804,0x138144d04d3004,0x732a1e0e873bdd2a110924d2c0a,0xa878a59d2e77ba54221249b51ab034baa5ca0f,0x3c9e0f802,0xac7abe1ecc9570903cb2583cc440b,0x2d160f21207d56f57c3d992aa833d16e7f579f4fcae753ad6ce34437c4219,0xb4583c8481f55bd5f0f664aaa0cf45c2015e7d3f2b9d4ec5b38910e04f41c421b,0x170805b9fd6c04,0xab7abe1ecc95709040b3583c83e0b,0xb1583cc4822563d5f0f664aaa14f484abcfa7e57386109f44ae43a17,0x161dc54763a1cc5e06,0x643616502854c05,0x146a05206c309b4c265bd0b11c093b0143808be602809cbcad5a870de72238d8dc81861389e4b169161aed670d194d2663b834ef7bc11c8fc53855f6522312082354a0402493414146e3d1914c2e44]

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk778_0 : checkRows book778 9 247 rows778_0=true := by decide +kernel

def rows778_1 : List Nat := [0x351a4da02,0xcb653499eee7e29140a377bddda0b,0x3c9e0f602,0x602f104da6132de8588e049d80a1c045f301504e5e56ad4386f3891c646e40c309c4f258b48b0d76b2c60ca6933ddc1a77bde08e47e29c2b0f2312082552b174b294080492682888cc7afe870e582da6b238183e2499186dc6c2401a0f0702808090401d1ed76db08508a4880ccb007fb6524dd6220c3669,0x29974b0551e8e06a4124110640a,0x30178826d30996f42c47024ec050e022f980a8272f2b56a1c379c48e3237206184e2792c5a4586bb59630653499eee0d3bdef04723f14e158791890412a958ba594a040249341444663d7f43872c16d359fa493230db8d84682c1e0e0601812080199600054635db6c214449b2926eb1107131f3fc3668,0x60361a4c2753605,0xda6a23110d25d2d114ac08,0x1b0d45b2e958d2488b1087e09,0x82488b0fcd6272e96cda6a8b9a4aa0c,0x4636108d66a2909cd23e28c60900b,0xe8d0362b8c4cc551398c7a09,0x3b2e0d4d05a2ec68a26318c007a0b,0xd267b319403,0x1145f2ed7403,0x1d1ed76dbe5bac46ca4906040503c188e453f41211,0x8f6bb6df2dd62365248304810140f06a400e0f,0x18180f05a340a8c6bb6df2dd6236524834547c1211,0x1e46ebd5d4517c343c20a08e44a0402493774707e48208d4f415,0x3c9e0f402,0xb8ee2a3a9d04e733246c5e09,0x178aa6d30996f42c47024ec050e022f984b25e56ad4386f3810c646e40c8c984f269245641240f8630d76b2d94d267bb834ef7bc11c894080492682910cd80ba8a2ec603d1d97242da6b4784edc6c48122080700ccad94937588837e29c2b0f2d99236582296a205b,0xe87a362b8c23a5424104aa5d290fc8a0d,0x474605d298c8a805]

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk778_1 : checkRows book778 9 271 rows778_1=true := by decide +kernel

def rows778_2 : List Nat := [0x1b8d8901f0f23c1e8d23a78322ea28bb6d35a3c910403806658db6524dd6220d801c,0x88af5b8d8902ea28be2a0f46c572e9424e828239128100924ddd1c92bf14e15879924cda6b47922080700ccb1b6ca49bac441c90782e,0x1d0f4691d28498903e289748a0a,0xa44da6146178aa65bd0b11c093b0143808be622c9795ab50e1bce036201b902fa149289e4d258d61aed67329a4cc770fc34ef7bc11c8fc53a50201249a0a44bd6e36240ba8a2f868271b8f4765c188f890452d4a4acda6b47922080700ccad9493758883214a02b193246d405f,0x1489b4c28c2f154cb7a16238127602870117cc45e56ad4386f388ec806e40be8523e24118824a27934744b2ac35dad11cb299e56663ba4a1a77bde08e47e29d28100924d05115eb71b1205d4517c3c1e8d8ae5d284764cda6b47922080700ccad94937588832dca82b193246d4060,0x1489b4c28c2f154cb7a16238127602870117cc25e56ad4386f390ec866e40c8c984f268e8922b20c35dad11c8f468ca6790890461f14598ee29069def782391f8a74a04024934149c645328174b72a2a4ac2b193246d404c]

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk778_2 : checkRows book778 9 295 rows778_2=true := by decide +kernel

def lastUnits778 := digits 9 10 0xae5d2c1447a38188fa272c

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflict778 : checkReasons book778 301 54 lastUnits778 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem exclude778 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 778=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=1) h hc bp eq (by decide +kernel)
  let v := truth Z a778
  have hbase : ValidThrough v book778 247 := book_start Z h hc z eq _ _ _ _ initialClauses778
  have h0 : ValidThrough v book778 271 := rows_sound hbase rows778_0 rowsOk778_0
  have h1 : ValidThrough v book778 295 := rows_sound h0 rows778_1 rowsOk778_1
  have h2 : ValidThrough v book778 301 := rows_sound h1 rows778_2 rowsOk778_2
  exact book_end h2 _ _ conflict778
end Compact

namespace Compact
open PEqualNP.Outside.L_meta_9774_aux.DagTools Resolution

def a794 := ([2,0x3002,0x5802,0x6802,34,0x3022,0x5822,0x6822,1,0x40001,0x3003,0x160001,0x6803,2049,0x40801,0x160801,4096,6144,0x3807,0x23807,0x43807,0x63807,0x164008,0x964008,0x1164008,0x1964008,0x40041,0x40841,0x41041,0x41841,193,0xa00c1,0x1600c1,0x58c3,0x1a00c1,0x68c3,2240,2241,0xa08c1,0x1608c1,0x1a08c1,4288,4289,0xa10c1,0x1610c1,0x1a10c1,6336,6337,0xa18c1,0x1618c1,0x1a18c1,0x108c7,0x308c7,0x508c7,0x708c7,0x3648c8,0xb648c8,0x13648c8,0x1b648c8,0x3009,0x3029,0x163009,0x163029,0x1a3009,0x1a3029,0x58e3,0xe0161,0x1a0161,0x6963,2400,0xe0961,0x1a0961,4448,0xe1161,0x1a1161,6496,0xe1961,0x1a1961,0xe167,0x2e167,0x4e167,0x6e167,0x422168,0xc22168,0x1422168,0x1c22168,0xe5809,0xe5829,417,0xc01a1,0xe01a1,0x1601a1,2464,2465,0xc09a1,0xe09a1,0x1609a1,4512,4513,0xc11a1,0xe11a1,0x1611a1,6560,6561,0xc19a1,0xe19a1,0x1619a1,0x61a7,0x261a7,0x461a7,0x661a7,0x3809a8,0xb809a8,0x13809a8,0x1b809a8,0x4209a8,0xc209a8,0x14209a8,0x1c209a8,0x4821a8,0xc821a8,0x14821a8,0x1c821a8,0x6809,0x6829,0xc6809,0xc6829,0x166809,0x166829,5,0x20005,0x40005,0x60005,6,0x40006,0x160006,37,8197,0x22005,0x42005,0x62005,0x42006,8229,0x8005,0x28005,0x48005,0x68005,0x8006,0x168006,0x8025,8196,0x8004] : List Nat).toArray.map readFact

def r794 := ([3,2052,0xe1009,0x8e1009,0x43807,0x63807,0x3805,0x580400a,0x584400a,0x596400a,0x2580400a,0x2584400a,0x2596400a,0x1164008,0x1964008,0x164006,64,2112,4160,6208,0x4200c9,0x4228c9,0x4258c9,0x4268c9,0x308c7,0xc200c9,0xc228c9,0xc258c9,0xc268c9,0x508c7,0x14200c9,0x14228c9,0x14258c9,0x14268c9,0x708c7,0x1c200c9,0x1c228c9,0x1c258c9,0x1c268c9,0x108c5,0xd8048ca,0xd8a48ca,0xd9a48ca,0xb648c8,0x2d8048ca,0x2d8a48ca,0x2d9a48ca,0x13648c8,0x4d8048ca,0x4d8a48ca,0x4d9a48ca,0x1b648c8,0x6d8048ca,0x6d8a48ca,0x6d9a48ca,0x3648c6,0x1000cd,0x300b,0x300c,0x302b,0x302c,0x8000cf,0x10000cf,0x18000cf,0x10200cf,0x18200cf,0x18400cf,0x58ce,0x258ce,0x16300b,0x16300c,0x16302b,0x16302c,0x8058cf,0x10058cf,0x18058cf,0x10258cf,0x18258cf,0x18458cf,0x68ce,0x268ce,0x1a300c,0x1a302c,0x8068cf,0x10068cf,0x18068cf,0x10268cf,0x18268cf,0x18468cf,0x383969,0x386969,0x2e167,0xb83969,0xb86969,0x4e167,0x1383969,0x1386969,0x6e167,0x1b83969,0x1b86969,0xe165,0x108e216a,0x109a216a,0xc22168,0x308e216a,0x309a216a,0x1422168,0x508e216a,0x509a216a,0x1c22168,0x708e216a,0x709a216a,0x422166,0x6396d,0xe580b,0xe582b,0x80396f,0x100396f,0x180396f,0x102396f,0x182396f,0x184396f,0x1801a9,0x1839a9,0x1859a9,0x261a7,0x9801a9,0x9839a9,0x9859a9,0x461a7,0x11801a9,0x11839a9,0x11859a9,0x661a7,0x19801a9,0x19839a9,0x19859a9,0x61a5,0xe0009aa,0xe0c09aa,0xe0e09aa,0xb809a8,0x2e0009aa,0x2e0c09aa,0x2e0e09aa,0x13809a8,0x4e0009aa,0x4e0c09aa,0x4e0e09aa,0x1b809a8,0x6e0009aa,0x6e0c09aa,0x6e0e09aa,0x3809a6,0x108e09aa,0x109609aa,0xc209a8,0x308e09aa,0x309609aa,0x14209a8,0x508e09aa,0x509609aa,0x1c209a8,0x708e09aa,0x709609aa,0x4209a6,0x120c21aa,0x120e21aa,0xc821a8,0x320c21aa,0x320e21aa,0x14821a8,0x520c21aa,0x520e21aa,0x1c821a8,0x720c21aa,0x720e21aa,0x4821a6,430,0x201ae,0x680b,0x680c,0x682b,0x682c,0x8001af,0x10001af,0x18001af,0x10201af,0x18201af,0x18401af,0xc680b,0xc680c,0xc682b,0xc682c,0x8031af,0x10031af,0x18031af,0x10231af,0x18231af,0x18431af,0x859ad,0x16680b,0x16680c,0x16682b,0x16682c,0x8059af,0x10059af,0x18059af,0x10259af,0x18259af,0x18459af,16,0x20000012,0x1000012,0x5800012,0x20020012,0x1020012,0x5820012,0x40011,0x60011,48,8208,0x21002012,0x21022012,0x21042012,0x21062012,8240,0x8010,0x8012,0x25808012,0x28011,0x28012,0x25828012,0x48011,0x48012,0x25848012,0x68011,0x68012,0x25868012,0x8030,0x1080013,0x80034,0x20200013,0x5a00013,0x200034] : List Nat).map readScheme

def table794_0 : List Nat := [0x9008803,0x48882,0x90902,0xe0982,0x108a02,0x118a82,0x5629138944,0x88b02,0x98b02,0xb0b02,0xd8b82,0xe8b82,0xf0b82,0x108c02,0x118c82,0x6631178b44]

def table794_1 : List Nat := [3393,3521,3649,3777,0x1e1982,0x1f1982,0x201982,0x221982,0x249a02,0x251a02,0x261a02,0x271a02,0x281a02,0x299a82,0x2a1a82,0x2b1a82]

def table794_2 : List Nat := [0x2c1a82,0x2d1a82,0x2e9b02,0x2f1b02,0x301b02,0x311b02,0x321b02,0xda6b3499c4,0x1e1b82,0x1f9b82,0x221b82,0x249c02,0x251c02,0x269c02,0x281c02,0x299c82]

def table794_3 : List Nat := [0x2a1c82,0x2b9c82,0x2d1c82,0x2e9d02,0x2f1d02,0x309d02,0x321d02,0xea73389bc4,1345,0x19d82,7554,0x59e02,0x41e02,0x3c9dc963d240506,0x3c9dcaa3d290506,0x3c9dcbe3d2e0506]

def table794_4 : List Nat := [0x3c9dcaa4b290506,0x3c9dcbe4b2e0506,0x3c9dcbe552e0506,0x43020083,0x43060283,0x19e82,0x21e82,0x59f02,0x61f02,0x3e9ec9e41241086,0x3e9ecb241291086,0x3e9ecc6412e1086,0x3e9ecb24f291086,0x3e9ecc64f2e1086,0x3e9ecc6592e1086,0x47030083]

def table794_5 : List Nat := [0x47070283,0x31f82,0x72002,0x409fca245241186,0x409fcb645291186,0x409fcca452e1186,0x409fcb651291186,0x409fcca512e1186,0x409fcca5b2e1186,0x422702,0x432702,0x45a782,0x462782,0x472782,0x48a802,0x492802]

def table794_6 : List Nat := [0x4a2802,0x4ba882,0x4c2882,0x4d2882,0x146a14fa744,0x422902,0x43a902,0x45a982,0x462982,0x47a982,0x48aa02,0x492a02,0x4aaa02,0x4baa82,0x4c2a82,0x4daa82]

def table794_7 : List Nat := [0x156a953a944,8385,0x2ab02,0x6ab82,0x57ab51a85452086,0x57ab52685482086,0x57ab532854b2086,0x57ab5268d482086,0x57ab5328d4b2086,0x57ab532934b2086,0x583582,0x5a3582,0x5b3582,0x5cb602,0x5d3602,0x5f3602]

def table794_8 : List Nat := [0x603602,0x61b682,0x623682,0x643682,0x653682,0x66b702,0x673702,0x693702,0x6a3702,0x1badb6cb5c4,0x583782,0x593782,0x5ab782,0x5cb802,0x5d3802,0x5e3802]

def table794_9 : List Nat := [0x5fb802,0x61b882,0x623882,0x633882,0x64b882,0x66b902,0x673902,0x683902,0x69b902,0x1cae370b7c4,0x5ab982,0x5b3982,0x5cba02,0x5fba02,0x603a02,0x61ba82]

def table794_10 : List Nat := [0x64ba82,0x653a82,0x66bb02,0x69bb02,0x6a3b02,0x1daeb74b9c4,0x593b82,0x5a3b82,0x5cbc02,0x5e3c02,0x5f3c02,0x61bc82,0x633c82,0x643c82,0x66bd02,0x683d02]

def table794_11 : List Nat := [0x693d02,0x1eaf378bbc4,0x19000183,0x19040383,0x3bd82,0x3d82,0x7be02,0x43e02,0x7cbdd76b15c0606,0x7cbdd8ab1610606,0x7cbdd9eb1660606,0x7cbdd8abb610606,0x7cbdd9ebb660606,0x7cbdd9ec5660606,0x3be82,0x13e82]

def table794_12 : List Nat := [0x7bf02,0x53f02,0x7ebed7ab35c1186,0x7ebed8eb3611186,0x7ebeda2b3661186,0x7ebed8ebd611186,0x7ebeda2bd661186,0x7ebeda2c7661186,8769,0x3bf82,0x23f82,0x7c002,0x64002,0x80bfd82b75c2206,0x80bfd96b7612206,0x80bfdaab7662206]

def table794_13 : List Nat := [0x80bfd96c1612206,0x80bfdaac1662206,0x80bfdaacb662206,0x2130782c0c4,0x10b084083,0x10c09c083,0x10e0bc083,0x10b0d4103,0x10c0ec103,0x10e0fc103,0x10c182,0x11c202,0x4441,0x233178ac4c4,0x11b1a4483,0x11b1b4503]

def table794_14 : List Nat := [0x11b1c4583,0x11b1d4603,0x4741,0x24b2390c7c4,0x1261ec783,0x129204783,0x24c802,0x12625c803,0x129274803,0x29c882,0x1262ac883,0x1292c4883,0x2ec902,0x1262fc903,0x129314903,0x4ac1]

def table794_15 : List Nat := [0x11a86cb03,0x12d8e4403,0x127854b83,0x12887cb83,0x12f954403,0x46c1,0x202ff60b684,0x1017fba03,0x202ff60ba84,0x202ff60bb04,0x1017fb043,0x202ff6ab304,0x1ff0176b584,0x1017fb343,0x80bfc2,0x2e1dcbe713a9e46]

def table794_16 : List Nat := [0x1dce27f071b05,0x204fe45231c85,0x379c5027f229186,0xf2771e9d04,0x359a4fe713b8386,0xac4a2d198845,0x553b9fca45b071b87,0x5a25008244,0x79349fcde71071dc7,0x379c5027f231a86,0x3c818d271378386,0xfd233bd98f17db907,0x38dc2cc7ebbd84f1233ec9,0x522a9a4f26b2e1dc7,0xe2793b9b04,0x349dcf26d2e17c6]

def table794_17 : List Nat := [0x379c4d2793b9706,0xf206389a48c6b2e0388,0xce301309decc7ebc48,0xce3613bd70cc013f48,0x79031c48c69071ac7,0x359a4f271379dc6,0x2d129d8d27103331faef6138cb,0x16895de693881998fd3b308a,0x1e6ef7e919f6cc71bc48,0xb44a6938819decc7e9d89,0x170e15ebf598e3233ec8,0x1a4f2713b9ac5,0xd2713c9dc4,0x5a25779c40c69661e48,0xc3ddaedb7cb906,0xdb6bb3030f77cae87]

def table794_18 : List Nat := [0x6635db6187bbe46,0x16894d2713fbe06,0x3dc30f972b605,0x61f2f75db885,0x72be5ee185db586,0x72bdc30f96eaec6,0xc3e5eee172b686,0x30f97bb344,0x61f2f772b145,0x1f2f70c3944,0x67c8003,0xf90c3dc3,0x1e4d271030385,0x16894e269033906,0x3ec8cfd59b805,0x395fa467dbb85]

def table794_19 : List Nat := [0x3ec8cfd59bc05,0x7abbdfa467dacc6,0x37dcaf577af05,0x2f48cfd7dbc85,0xb4d271128185,0xdf7dbf48cbd71bc07,0x1bebd79bec8cef7eb8c8,0xdf79bbd7afb233f47,0xe7b8203,0x3ec8cfd5eb885,0x3ec8cfd5eb345,0x8cfd7daf44,0x3ec8cfd77b905,0x7dbbdfa466638c6,0x119fafb77b305,0x8cfd7dbbc4]

def table794_20 : List Nat := [0xe26985c084,0x1dc467ebec4,0x349c48c7f3b8386,0x1a4e30b233e85,0xd27185bf04,0xd271859184,0x84c0e1633158846,0xd271238004,0x303858244,0x6938c2c3,0xd271238204,0x15ead42a984,0x152ad57a704,0x15ead42a784,0x27542ad57a145,0x2bd5aa952a885]

def table794_21 : List Nat := [0x142a956abc4,0x108fa7b209b05,0x339a4140c3d9046,0x188ac5233874106,0x23a85531e188a4e26983bf8a,0x104c383,0xa1549c4d31e0091c7,0x467dbf43,0x20918ce69020086,0x2319cd271208106,0x3899cd20c2080c6,0xa15499ce269231047,0x50aa63c69388046,0x1431e549244,0x1942a9049ec151e3483c9,0x2048c7f289a85]

def table794_22 : List Nat := [0xa154824151e231a47,0x1448c7f409d05,0x241c4a27f232046,0x4c7942a9051186,0x1431e549e04,0xf277259c84,0x793b9a03,0x96793b9a84,0x285531e009dc5,0x104c2c3,0x47942a9238045,0x483c9dc3,0x47942a93481c5,0x23ca1549a44,0x8f2442,0x1049e480202c5]

def table794_23 : List Nat := [0x2093c9051388106,0x120ad57aa44,0x9056abc3,0x189051388085,0x90209a03,0x7b20c78120a240307,0x1ec831e3b9205,0x11e2080c3,0x200882690719c6,0x11e20c003,0x8f1042,0x339a4a2463fa046,0x6734944910e230187,0x339a4a30e241186,0x48238003,0x67871c03]

def table794_24 : List Nat := [0x401c2,0x710411c3,0x118f271030085,0x388202,0x389a03,0x4781,0xa3d970c729928307,0x56abc2,0x51ee4c0c949b06,0x7d349ec846d2e18c7,0x1263d9f48529929a87,0x949f4847b20c806,0x24c6d34ca4847b3ec948,0x18d20a231c45,0x24144fe69232046,0x1a4120a031185]

def table794_25 : List Nat := [0x1269050184,0x349e02,0x349dc2,0x129931a4f6423ec907,0x38d27b2111c5,0xb04e92ca44,0x133c383,0x8c6940c2c4,0x8c69408204,0x34c002,6721,0x847b3ec884,0xa3d8303,385,705]

def encoded794 (i : Nat) : Nat :=
  if i < 208 then
    if i < 96 then
      if i < 48 then
        if i < 16 then
          table794_0.getD (i%16) 0
        else
          if i < 32 then
            table794_1.getD (i%16) 0
          else
            table794_2.getD (i%16) 0
      else
        if i < 64 then
          table794_3.getD (i%16) 0
        else
          if i < 80 then
            table794_4.getD (i%16) 0
          else
            table794_5.getD (i%16) 0
    else
      if i < 144 then
        if i < 112 then
          table794_6.getD (i%16) 0
        else
          if i < 128 then
            table794_7.getD (i%16) 0
          else
            table794_8.getD (i%16) 0
      else
        if i < 176 then
          if i < 160 then
            table794_9.getD (i%16) 0
          else
            table794_10.getD (i%16) 0
        else
          if i < 192 then
            table794_11.getD (i%16) 0
          else
            table794_12.getD (i%16) 0
  else
    if i < 304 then
      if i < 256 then
        if i < 224 then
          table794_13.getD (i%16) 0
        else
          if i < 240 then
            table794_14.getD (i%16) 0
          else
            table794_15.getD (i%16) 0
      else
        if i < 272 then
          table794_16.getD (i%16) 0
        else
          if i < 288 then
            table794_17.getD (i%16) 0
          else
            table794_18.getD (i%16) 0
    else
      if i < 352 then
        if i < 320 then
          table794_19.getD (i%16) 0
        else
          if i < 336 then
            table794_20.getD (i%16) 0
          else
            table794_21.getD (i%16) 0
      else
        if i < 384 then
          if i < 368 then
            table794_22.getD (i%16) 0
          else
            table794_23.getD (i%16) 0
        else
          if i < 400 then
            table794_24.getD (i%16) 0
          else
            table794_25.getD (i%16) 0

def book794 (i : Nat) : Clause := let n := encoded794 i; unpackLits 9 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClauses794 : inputsOK 2 794 a794 r794 (baseBook book794 245).toList=true := by decide +kernel

def rows794_0 : List Nat := [0x1c21370049be116f041ba08,0x8440b21a003,0x8842a25ec7f4e9f19a9e4e321a20b,0xa14fb21a003,0xa451321a203,0x4421512f63eb35367b4d295f2f87bb219e0e,0x21d128440344f8a550b49ee9b67b21460d,0x1427c4fa95ee9a3db219c08,0x6721102c852a81068942a01f4fc513dd360e,0x19c8440b214aa041a2510807d3f148fb7ebdd3610,0xc084281f8e06e05,0xc8b02a2a9484c501dbfc44231a8906e0d,0x190bca802,0x6c331bc04aa04,0x34198e07e03,0x30178de063b28408a4170a0a42a27800e07c0f,0xc0c04078341605,0x54290a8763e140e0a007,0xa0e008020a04,0x681e198dc621f820e08408,0x1b08466371887cb006,0x58130886e351209e1217811489e3984144640f,0x31d2eb1582615805,0xaf622b1868b4cc2d6207]

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk794_0 : checkRows book794 9 245 rows794_0=true := by decide +kernel

def rows794_1 : List Nat := [0x8c84141f0e04e05,0x44231a891fe04,0x7884141f8e04e05,0x630d178c06e3487c383e08,0x4c5529144541514c284e08,0x15ec6563151f0c5f93d6208,0x4bb1920aa45b097ea98913d320a,0xa61427114442a05,0xc02827870bc6e33880e07c09,0x113890e55003,0xaf63ab528a962afd2716278e5620b,0x10b47b1916c457ac53207,0x9763241548b612a5511855afd2317278e5320f,0x12ec645b093204,0x531513c382a04,0x880dc621f140f83c1d8d8e0660a,0xa451108aa141d8a302324f1cc70a80c,0x43a60fcbc4b2551206,0x47924bd472297486449f93209,0x24922998f240fe8a5c1f512865e47d760d,0x4183c1d10948a03b8e41075075bada120d,0x2492299481fd14b83f1f57609,0x492457602,0x91a35707a461ed3206]

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk794_1 : checkRows book794 9 269 rows794_1=true := by decide +kernel

def rows794_2 : List Nat := [0x2090289914917605,0x5ca0902994a20d1406,0x248f4914ca30f6899323a4a8591255720d,0x2e4f499461ed1326474950cbd93c89220d,0x2491d24461ee4127414a13209,0x21d30825e9f9787a5d25a53275aac9120d,0x874c2097a7e5e1e9749694c9d120b,0x29144422a85076284f1cc70a80a,0xc0962fd2ea68ea549e398e0f20f2a90945880f,0x47a358402,0x9348a665ca64629d8607,0x54aa18402,0x158ab58cc18604,0x251328f58aa55a05,0x562ad8a02,0x24d2299482a963339922e62ae8ccbe5ac0962fc9e398e0f20f2a909458a19,0x4695099482a92a05,0x11858cd55c03,0x9348cd98a03,0x5bace5602,0x49a458a02,0x98aba6f3397a551606,0x4c55f3699cbd2ec69d4e51609,0x18c9785a555204]

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk794_2 : checkRows book794 9 293 rows794_2=true := by decide +kernel

def rows794_3 : List Nat := [0x4311f1854ced5605,0x18e9358ab5293d54ced5e08,0x98cca78ae9f4ed1606,0x97532565f3f60af8a03b8e0ea0f3865bf992b49a01da8026abc1eaf171371881b,0x12ea64acbd8804,0x108aa12520ec10a806,0x20301408036c3c1eaf1713701e0e06829aed36d805b4001e47254b6a11457c395fd00101f,0x10180a0401b61e0f578b89b80f0703414d769b6c02da004e1692c600ea383b60d00101e,0x13fa250e8203,0x100f06829ae060200db0f07abc5c4dc69b680410,0x254b67f32ca03b8e0e99208,0x36c1c05008028c05,0x270b47f3249e398e0f29147a2d01960c,0x270b47f3249e398e0f19608,0x68339c4e803,0xdc6d3852cb2662d1c4ec08,0x5c2d9c4e803,0x188c264a69c4ec05,0x7831184e2703798cd007,0xdc5c369c0d25d3253ccb4ea61c4f00c,0x128889602,0x100744f51241109406,0x6d8783d5e2e26e008100f063640c0c,0x9aaf07abc5c4096b34db75302bcdcb520a391e5491dc707273a81c9944527b25e8ef6e0380200a551e0a25]

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk794_3 : checkRows book794 9 317 rows794_3=true := by decide +kernel

def rows794_4 : List Nat := [0xd5783d5e2e26e41412d669b6db55306814080e008000413,0x803a27a891c8ce579d5428e479525e8ef6e10ce55039b30731c1d94196feaa03408da005289421,0x4fe8201,0x100744f5123b06aebf2310c940a,0x27ec11dc717c51a10e6b0cb7f32a820c,0x2a4458e0e47604,0x30658c97f33181575fd68e75039564760d,0x42851386055d7e398e0f2aaf372d6c28e479526acf477b716815,0x1456d2a5f55e8ec11dc70755c0c0ae840d,0x4d5783d5e2e203b528cdb79390295239d40e4ca7f32dcaf3aabd1dedc028380200952da0a20,0x10874ac02,0x130884f5f0b94ca42ea1144735e5f1157f5760d74ae12,0x1b0ccae02,0x190bc6f611514cac06,0x241157e1b72bceab2a5b3d1dedc221cea072653f99652b15745a1a0e580a2beabb04921e,0x2406ebc4527b95e755953256cf477b72ba4439d40e4ca7f32ca1631e0ec921a,0x30178e08003,0x34198deca2d0d0a07a190c0e0820b,0x1e0e8e08003,0x462213d9c283d16472cd64ae8e0820c,0xd5783d5e2e26e4140ed4a336c0a0e00800040f,0x803a27a886c924728119caf3aad7428e4795a670cb5a3d1dedc219caa073663f9924f1cda09421,0x118884f670a0f4591cb30e0820a,0x391e569ac395e7559c32d68f477b72d43a39540e6cc7f324736baed902819]

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk794_4 : checkRows book794 9 341 rows794_4=true := by decide +kernel

def rows794_5 : List Nat := [0x4c2213d7c2e5329302aebf288bab83a27db0736baed90ae14,0x11d82460db95e7559c2d1e8ef6e10ce55039b31fcc928d885a1a0e5b4a4c0abda874bf1cdaebb642f1a89225,0x2491c8c39b58ec8606,0x28d88a5572832dfcca60dbd7c0a,0x371b4e0683b994ea5fa81c4f20a,0xc46132180d85c3b964ea6bb89c4f20c,0x29588a35727afd8006,0x492411477661cdcd92fe661cee472b806c301c168688813,0x148a22ea485ca0b695325fcccb4bc9c814a95d2dcf477b70a615,0x130884f5f0b94ca42ea15d0a2beabb04a0cb7f328e572b71ceea3c1ddacae1a,0x50acbf99472b91cea414723ca92f477b70771cba5b857761c9159617,0x803a27a891ca1582310c9409,0x291445c1727ad256b759da47576230ae92f272052f072b91cd9974b73d1dedc65ddca61e,0x261109ebe1729948a22e15cb076c1ba5b981575f93d92febcddcae17,0x4c2213d7cae04,0xbfabb02d63caaca96c52bd944720b,0x1db0475559c302aebe5a5f2d60a,0x254b67f32ca03bb58e99208,0x1385a3f9924f1cdac7955bf5f4342d170ad960f,0x270b47f3259604,0x60073661e5289e05,0x301c96144a4c0abafec408,0x8e0e705811e602cc06,0x2da55620e1457d57608eecc3abf060a40d]

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk794_5 : checkRows book794 9 365 rows794_5=true := by decide +kernel

def rows794_6 : List Nat := [0x1456d2a5f55e8ec11dc73083aaae0efe1679b96f4f477b728415,0x1d64e74135ca4b24111c608,0x5e355caa003,0x44257688f0c04,0x404e0b12c4e04,0x1d41e74131ca4a10075c608,0x743989202,0x1d6e971e2c2c27c56149408,0x3b1dd8cc43ca8af3aaca96d837a3bdb84422920e78739329fccba114472bfabb07121d,0x29dec2e02,0xec7763310f2b4bceab2a5b3d1dedc221157f5760920e78739329fccb29638562ec6947121f,0x3b1dd8cc43cad2f3aaca96cf477b70884527920e78739329fccb2863f1219,0x142aebe60bf993901e0ed9609,0x16b8e6445603,0x1db89763b84604,0x1d64e741344a22c664de755795a475385a13c73927a3bdb84728615c618,0xeb74615c603,0xbfd570602,0x301691d64b1c2b17514a208,0xac5d8328e031c05,0x271344a22c664de59723b06aebf79d547598ca1188672c39cd9839c914996f477b732a1e,0xc0abaff1c2b1760b225127b25fd991ce48a40f,0x490c65b082d0d3cdd64c0de69d2f477b702c0f,0x773ceaa1b7638f364873bcad384c18b434f477b70339ac29109a16]

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk794_6 : checkRows book794 9 389 rows794_6=true := by decide +kernel

def rows794_7 : List Nat := [0xa2502932dfcca3961ce79c1dd987245b9860382d0d66ac414,0x3b9e7550dbb1c79b2311dcef2b4e105a1ac03d1dedc0ce148672c39cd98fe64e7473661de689a21]

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk794_7 : checkRows book794 9 413 rows794_7=true := by decide +kernel

def lastUnits794 := digits 9 8 0x2855d7cc1cf3f9939d

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflict794 : checkReasons book794 415 203 lastUnits794 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem exclude794 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 794=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=2) h hc bp eq (by decide +kernel)
  let v := truth Z a794
  have hbase : ValidThrough v book794 245 := book_start Z h hc z eq _ _ _ _ initialClauses794
  have h0 : ValidThrough v book794 269 := rows_sound hbase rows794_0 rowsOk794_0
  have h1 : ValidThrough v book794 293 := rows_sound h0 rows794_1 rowsOk794_1
  have h2 : ValidThrough v book794 317 := rows_sound h1 rows794_2 rowsOk794_2
  have h3 : ValidThrough v book794 341 := rows_sound h2 rows794_3 rowsOk794_3
  have h4 : ValidThrough v book794 365 := rows_sound h3 rows794_4 rowsOk794_4
  have h5 : ValidThrough v book794 389 := rows_sound h4 rows794_5 rowsOk794_5
  have h6 : ValidThrough v book794 413 := rows_sound h5 rows794_6 rowsOk794_6
  have h7 : ValidThrough v book794 415 := rows_sound h6 rows794_7 rowsOk794_7
  exact book_end h7 _ _ conflict794
end Compact

namespace Compact
open PEqualNP.Outside.L_meta_9774_aux.DagTools Resolution

def a912 := ([0x2802,0x3002,0x5002,0x30a3,4256,193,0xa00c1,0x50c3,2240,2241,0xa08c1,4288,4289,0xa10c1,0x58c7,0x258c7,0x458c7,0x40c8,0x8040c8,0x10040c8,0xa3009,0x120121,0x140121,0x180121,0x3927,0x9127,0x140141,0xc0141,0x120141,0x180141,0x1a0141,2368,0x140941,0xc0941,0x120941,0x180941,0x1a0941,4416,0xc1141,0x1a1141,0xd947,0x2d947,0x4d947,0x12947,0x32947,0x52947,0x482148,0xc82148,0x1482148,0xc5009,0x180181,0x180981,0x181181,0x6805,0x26805,0x46805,0x6825,0x126826,0x146826,0x186826,0x7005,0x27005,0x47005,0x7025,0x27025,0x47025,0x127026,0x147026,0x187026,0x7805,0x27805,0x47805,0x7825,0x27825,0x47825,0x187826,0x71a4,0x79a4,0x79c4] : List Nat).toArray.map readFact

def r912 := ([163,0x1600c9,0x1628c9,0x258c7,0x9600c9,0x9628c9,0x458c7,0x11600c9,0x11628c9,0x58c5,0x40ca,0xa40ca,0x8040c8,0x200040ca,0x200a40ca,0x10040c8,0x400040ca,0x400a40ca,0x40c6,0x1228cd,0xa300b,0xa300c,0x8028cf,0x10028cf,0x10228cf,288,0xe5129,0x3925,0x246129,0x9125,323,0x363149,0x366949,0x2d947,0xb63149,0xb66949,0x1363149,0x1366949,0xd945,0x4a4949,0x4a6149,0x4a6949,0xca4949,0xca6149,0xca6949,0x52947,0x12945,0x120c214a,0x1214214a,0x1218214a,0x121a214a,0xc82148,0x320c214a,0x3214214a,0x3218214a,0x321a214a,0x1482148,0x520c214a,0x521a214a,0x482146,0x314e,0xc500c,0x80314f,0x100314f,0x102314f,384,2432,4480,0x6810,0x46811,0x6830,0x24806832,0x5006832,0x6006832,0x7010,0x47011,0x7030,0x4807032,0x25007032,0x6007032,0x4827032,0x25027032,0x6027032,0x47031,0x7810,0x47811,0x7830,0x26007832,0x26027832,0x26047832,0x1c6814,0x9c6814,0x249c6833,0x51c6833,0x1e6814,0x9e6814,0x61e6833,0x1e7014,0x9e7014,0x61e7033] : List Nat).map readScheme

def table912_0 : List Nat := [0x4202,0x28702,0x30702,0x44782,0x48782,0x50782,0x5c802,0x60802,0x68802,0x847c743,0x2c882,0x30882,0x44902,0x4c902,0x50902,0x5c982]

def table912_1 : List Nat := [0x64982,0x68982,0x9c948c3,449,0xca02,2562,0xa4543440185,0xa46c3458185,0xa46c5458185,2753,0xb0c02,3137,0xb8c82,3265,0x15282,0xd9402]

def table912_2 : List Nat := [0xf1402,0xfd482,0x109482,0x121482,0x131502,0x139502,0x1554d443,0xe1582,0xe9582,0xf1582,0x111602,0x119602,0x121602,0x12d682,0x16d655c3,0xd9702]

def table912_3 : List Nat := [0xd5702,0xe9702,0xf5702,0xfd782,0x109782,0x105782,0x119782,0x125782,0x12d802,0x131802,0x13d802,0x1857d743,0x3c08103,0x9882,0x18d0cdcf8385,0x18d34dd28385]

def table912_4 : List Nat := [0x18d350d28385,6465,6593,6721,0x1bdb5ac3,0x25b82,7233,0x1cca9c03,0x1d0b5c03,0x1d8bdc03,0x1f5ede43,0x25f02,0x20e05fc3,0x210e5f83,0x21cd1f83,0x220edf83]

def table912_5 : List Nat := [0x21116003,0x21d02003,0x2211e003,0x12e082,0x23e362c3,0x26382,0x2564e443,0x25d92403,0x25d9a483,0x25da2503,0x265e1a83,0x265e9b03,0x215ca603,0x219d6603,0x26e29a83,0x26e31b03]

def table912_6 : List Nat := [0x259de683,0x27629e03,0x27631e83,0x25a26703,9665,0xa434783,0x74a4343,0xa48c803,0x74a42,0x95d783,0x9802,0x265f63e75a85,0x1be65f63e745,0xa220d784,0xa212c3,0x1298c39704]

def table912_7 : List Nat := [0x264a02,0x128082,0xa4902,2625,6017]

def encoded912 (i : Nat) : Nat :=
  if i < 64 then
    if i < 32 then
      if i < 16 then
        table912_0.getD (i%16) 0
      else
        table912_1.getD (i%16) 0
    else
      if i < 48 then
        table912_2.getD (i%16) 0
      else
        table912_3.getD (i%16) 0
  else
    if i < 96 then
      if i < 80 then
        table912_4.getD (i%16) 0
      else
        table912_5.getD (i%16) 0
    else
      if i < 112 then
        table912_6.getD (i%16) 0
      else
        table912_7.getD (i%16) 0

def book912 (i : Nat) : Clause := let n := encoded912 i; unpackLits 8 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClauses912 : inputsOK 1 912 a912 r912 (baseBook book912 100).toList=true := by decide +kernel

def rows912_0 : List Nat := [0x2cc3b10abc1ac06,0x141932c03,0x80c272932e05,0x6040626488071c07,0x4428f2434209ce2f313300b,0x1240467df3d68cde1e5ab96374c0e,0x95d22807dfbd72f0f384c0b,0x30649270ec6a98a55abc0a,0xbf832493876361956e26ba80c,0x28d3329369e05,0xa5327b15cb54b276e36d3560c,0x44853247ebd0327c08,0x49011b73ef9a3377ab7bd787b714c79364597540154c18,0x124046dcfbe68cddeadef5e1e4c0e,0x161c309e80405,0x11043c97214074132e09,0x29f1a37641a36d66dc8e663704fa4a739812]

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk912_0 : checkRows book912 7 100 rows912_0=true := by decide +kernel

def lastUnits912 := digits 7 24 0xa172399994e75d9068dc6e0c172de2a593bd4539f4

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflict912 : checkReasons book912 117 42 lastUnits912 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem exclude912 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 912=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=1) h hc bp eq (by decide +kernel)
  let v := truth Z a912
  have hbase : ValidThrough v book912 100 := book_start Z h hc z eq _ _ _ _ initialClauses912
  have h0 : ValidThrough v book912 117 := rows_sound hbase rows912_0 rowsOk912_0
  exact book_end h0 _ _ conflict912
end Compact

namespace Compact
open PEqualNP.Outside.L_meta_9774_aux.DagTools Resolution

def a1290 := ([8194,0x3002,0x3802,0x5802,0x80061,0xc0061,2151,0x80081,129,0xc0081,0x3083,0x3883,0x5883,0x80881,2177,0xc0881,4224,0xd887,0x2d887,0x4d887,0x5088,0x805088,0x1005088,0xc00c1,193,0x800c1,2240,0xc08c1,2241,0x808c1,4288,0xc10c1,4289,0x810c1,8391,0x220c7,0x420c7,0x40c8,0x8040c8,0x10040c8,0x83009,0xe00e1,0x800e1,0x1800e1,2272,0xe08e1,0x808e1,0x1808e1,4320,0x810e1,0x1810e1,0x90e7,0x290e7,0x490e7,0x2618e8,0xa618e8,0x12618e8,0x83809,0x120101,0x160101,8455,0x5907,0x120121,0x120921,0x121121,0x160141,0x1a0141,0x5947,0xd947,352,0x160161,0x80161,0xe0161,0x120161,0x1a0161,0x6963,2400,0x160961,0x80961,0xe0961,0x120961,0x1a0961,4448,0x161161,0x81161,0xe1161,0x1a1161,0x2967,0x22967,0x42967,0x85809,0x1a01a1,0xe01a1,0x1601a1,2464,0x1a09a1,0xe09a1,0x1609a1,4512,0x1a11a1,0xe11a1,0x1611a1,0x61a7,0x261a7,0x461a7,0x4209a8,0xc209a8,0x14209a8,0x166809,0x3805,0x3825,0x23825,0x43825,0x83826,0xe3826,0x4005,0x84006,0xc4006,0x4025,0x24025,0x44025,0x84026,0xe4026,0x5005,0x25005,0x45005,0x5025,0x165026,0x1a5026,0x5805,0x25805,0x45805,0x85806,0xc5806,0x5825,0x25825,0x45825,0x165826,0x1a5826,0x6005,0x26005,0x46005,0x86006,0x6025,0x26025,0x46025,0x1a6026,0x8005,0x28005,0x48005,0x8025,0x128026,0x168026,0x8805,0x28805,0x48805,0x8825,0x28825,0x48825,0x128826,0x9005,0x29005,0x49005,0xc9006,0x9025,0x29025,0x49025,0x129026,0x169026,0x40e4,0x5904,0x9104,0x5944,0x6144,0x6164,0x9164,0x8a04,0x9204,0x9224] : List Nat).toArray.map readFact

def r1290 := ([0x22069,0x23069,2149,128,2176,131,0x360089,0x363089,0xb60089,0xb63089,0x4d887,0xd885,0x508a,0xc508a,0x2000508a,0x200c508a,0x1005088,0x5086,192,2240,2241,4288,195,0x800c9,0x820c9,0x8800c9,0x8820c9,0x10800c9,0x10820c9,8389,0x40ca,0x840ca,0x200040ca,0x200840ca,0x400040ca,0x400840ca,0x40c6,8398,0x8300c,0x8020cf,0x10020cf,0x10220cf,224,2272,227,0x2420e9,0x2460e9,0x290e7,0xa420e9,0xa460e9,0x490e7,0x12420e9,0x12460e9,0x90e5,0x98818ea,0x99818ea,0xa618e8,0x298818ea,0x299818ea,0x12618e8,0x498818ea,0x499818ea,0x2618e6,8430,0x8380c,0x8020ef,0x10020ef,0x10220ef,0x84909,8453,0x165909,0x5905,288,2336,4384,0x165949,0x5945,0x366949,0xd945,352,0x6962,353,2400,0x26962,2401,4448,0x46962,355,0xa2169,0xa3969,0xa4969,0x8a2169,0x8a3969,0x8a4969,0x42967,0x10a2169,0x10a3969,0x2965,8558,0x8580c,0x80216f,0x100216f,0x102216f,416,2464,4512,0x1839a9,0x1859a9,0x261a7,0x9839a9,0x9859a9,0x461a7,0x11839a9,0x11859a9,0x61a5,0x108e09aa,0x109609aa,0xc209a8,0x308e09aa,0x309609aa,0x14209a8,0x508e09aa,0x509609aa,0x4209a6,0x16680c,0x8059af,0x10059af,0x10259af,0x3810,0x3830,0x2003832,0x23803832,0x2023832,0x23823832,0x43831,0x4010,0x2004012,0x3004012,0x4030,0x22004032,0x3804032,0x22024032,0x3824032,0x44031,0x22044032,0x3844032,0x5010,0x45011,0x5030,0x5805032,0x6805032,0x5810,0x3005812,0x3025812,0x45811,0x5830,0x25805832,0x6805832,0x25825832,0x6825832,0x45831,0x25845832,0x6845832,0x6010,0x22006012,0x22026012,0x46011,0x6030,0x26806032,0x26826032,0x26846032,0x8010,0x48011,0x8030,0x4808032,0x5808032,0x8810,0x48811,0x8830,0x24808832,0x24828832,0x24848832,0x9010,0x23009012,0x23029012,0x49011,0x23049012,0x9030,0x4809032,0x25809032,0x4829032,0x25829032,0x49031,0x103814,0x2103833,0x23903833,0x2164013,0x164034,0x964034,0x3244013,0x244034,0xa44034,0x165014,0x965014,0x5965033,0x185014,0x985014,0x6985033,0x185814,0x985814,0x2185813,0x6985833,0x3245813,0x245834,0xa45834,0x228014,0xa28014,0x4a28033,0x248014,0xa48014,0x5a48033,0x248814,0xa48814,0x24a48833] : List Nat).map readScheme

def table1290_0 : List Nat := [0x40302,0x50302,833,961,1729,0x8802,0x80882,0x90882,0xe0902,0xf0902,0x108982,0x271288c3,0x88a02,0x90a02,0xe8a82,0xf0a82]

def table1290_1 : List Nat := [0x108b02,0x2d158a43,3009,3521,0x1a8f02,4033,0x18f02,0x181102,0x191102,0x1c1182,0x1d1182,0x201202,0x211202,0x49239143,0x189282,0x191282]

def table1290_2 : List Nat := [0x1c9302,0x1d1302,0x209382,0x211382,0x4f2692c3,0x15000083,5122,0x14476331a0505,0x14486331e0505,0x144863b1e0505,5313,5825,0x29802,0x2a1982,0x2b1982,0x2c9a02]

def table1290_3 : List Nat := [0x2e1a02,0x2f1a02,0x309a82,0x311a82,0x321a82,0x6b3499c3,0x2a1b02,0x2b9b02,0x2c9b82,0x2e1b82,0x2f9b82,0x309c02,0x311c02,0x329c02,0x71379b43,0x17000103]

def table1290_4 : List Nat := [7298,0x1ccba552c0585,0x1ccc655300585,0x1ccc65d300585,0x3a1e02,7745,0x3b1e82,7873,8001,8129,8257,0x412182,8641,0x422202,8769,9025]

def table1290_5 : List Nat := [0x974a2283,0x45a602,9921,0x97512603,0x4ca902,0x29c1,0x97562903,0x3a902,0x472b82,0x482b82,0x492b82,0x4e2c02,0x4f2c02,0x502c02,0x52ac82,0x542c82]

def table1290_6 : List Nat := [0x552c82,0xb358abc3,0x19000183,0x2d02,0x2d53a8f4c0605,0x2d5528f520605,0x2d5529d520605,0x2dc1,0x2fc1,0x31c1,0x5c3302,0x5d3302,0x5eb382,0x603382,0x613382,0x62b402]

def table1290_7 : List Nat := [0x643402,0x653402,0xd167b343,0x5cb482,0x5d3482,0x5eb502,0x60b502,0x613502,0x62b582,0x64b582,0x653582,0xd76ab4c3,0x33602,0x36586bb5e2585,0x36596bb622585,0x36596c3622585]

def table1290_8 : List Nat := [0x36c1,0xe16fb743,0xe22ab703,0xe5293703,0xe22eb783,0xe52d3783,0x30b802,0x39c1,0xe804b983,0xea05b983,0xf177bb43,0xf3473b03,0xf448bb03,0xf34e3b83,0xf44fbb83,0x52bc02]

def table1290_9 : List Nat := [0xf3543c03,0xf455bc03,0xfb7cbdc3,0x10be82,0x3f41,0xfe41bf03,0x10042bf03,0x10782c0c3,0x10a09c083,0x10a0fc103,0x10c182,0x11187c343,0x113464303,0x1144ac303,0x1134d4383,0x11451c383]

def table1290_10 : List Nat := [0x52c402,0x113534403,0x11456c403,0x11b8cc5c3,0x11d074583,0x11d0d4603,0x10c682,0x12390c7c3,0x1255b4783,0x1255f4803,0x125634883,0x12b94c9c3,0x1eca82,0x4b41,0x12e3acb03,0x1303bcb03]

def table1290_11 : List Nat := [0x1379accc3,0x1ecd82,0x13d9dce43,0x13f3e4e03,0x13f3f4e83,0x13f404f03,0x145a1d043,0x147175003,0x1471b5083,0x1ed102,0x1471f5103,0x14da5d243,0x14e49d203,0x151465203,0x14e50d283,0x1514d5283]

def table1290_12 : List Nat := [0x52d302,0x153733683,0xf271d483,0xf5725483,0x10874d503,0x155863b03,0x155873b83,0x14675d583,0x157a43b03,0x157a53b83,0x159813d83,0x159823e03,0x1127fd603,0x15b8b3d83,0x15b8c3e03,0x12480d683]

def table1290_13 : List Nat := [0x15d8b4083,0x15d8c4103,0x11c84d703,0x1248ad703,0x14685d783,0x15fa44303,0x15fa54383,0x161994983,0x1619a4a03,0x13e97d803,0x163a04983,0x163a14a03,0x15098d883,0x165a04c83,0x165a14d03,0x14f9f5903]

def table1290_14 : List Nat := [0x51c1,0x4fc1,0x4941,0x565f71b84c085,0x41e36fbacc245,0x1b2965db384,0xd94b3483,0x1b2965db504,0xd94b2ec3,0xd94b3583,0x6ca582,0x146ad4ac504,0x3c000ec3,0x47269083,0x1e0002,0x5660f1baebd85]

def table1290_15 : List Nat := [0x46df7074bc405,0x12f1456a604,0x27168483,0x536bef1aac385,0x445e34dafd545,0x8dbee0f1687a906,0x9bee37078b43c6,0x512902,0x3ee370709c585,0x44c1,0x1cc2c60339b85,0x180e6163699c5,0xc0730b1b44,6146,0x70b942,0x58ecb2b9bd005]

def table1290_16 : List Nat := [0x1d8b3a50004,0x88c329af159d7c6,0x848842,0x1e2b3005284,0x535e2b37a0005,0x850842,0x862942,0x10fae8843,0x1c271711a04,0xd6e138b884,0xf479ad4309859bb87,0xb50c291e8f377ab87,0x7a2916a1879acc6,0x87a902,0x43c1,0xf1a68843]

def table1290_17 : List Nat := [0x2941,2113]

def encoded1290 (i : Nat) : Nat :=
  if i < 144 then
    if i < 64 then
      if i < 32 then
        if i < 16 then
          table1290_0.getD (i%16) 0
        else
          table1290_1.getD (i%16) 0
      else
        if i < 48 then
          table1290_2.getD (i%16) 0
        else
          table1290_3.getD (i%16) 0
    else
      if i < 96 then
        if i < 80 then
          table1290_4.getD (i%16) 0
        else
          table1290_5.getD (i%16) 0
      else
        if i < 112 then
          table1290_6.getD (i%16) 0
        else
          if i < 128 then
            table1290_7.getD (i%16) 0
          else
            table1290_8.getD (i%16) 0
  else
    if i < 208 then
      if i < 176 then
        if i < 160 then
          table1290_9.getD (i%16) 0
        else
          table1290_10.getD (i%16) 0
      else
        if i < 192 then
          table1290_11.getD (i%16) 0
        else
          table1290_12.getD (i%16) 0
    else
      if i < 240 then
        if i < 224 then
          table1290_13.getD (i%16) 0
        else
          table1290_14.getD (i%16) 0
      else
        if i < 256 then
          table1290_15.getD (i%16) 0
        else
          if i < 272 then
            table1290_16.getD (i%16) 0
          else
            table1290_17.getD (i%16) 0

def book1290 (i : Nat) : Clause := let n := encoded1290 i; unpackLits 9 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClauses1290 : inputsOK 1 1290 a1290 r1290 (baseBook book1290 224).toList=true := by decide +kernel

def rows1290_0 : List Nat := [0x5d05570135b8496c06,0x5a9296849599216406,0x551a552685419d4e06,0x29006d051b399ee24b1349c9449329a40d,0xa50234546cd67b892c4d2725124cb4bb8da40f,0x371b0fa02,0x71379c9ca74351ccfc07,0x3b9d4fa02,0x1e8f07b73b98fc05,0xe079371fcd67e3d1e0e408,0x713b9bce46d3b1edd2e635ba0fe0b,0xa24fa753603,0x643a1c0c09046290f89c4c1412858400d,0x5c3a1c1208c3c05,0x6c3a181207c50267686842ec12858440d,0x67b892c4d2725146d14bb299a0a,0x51b399e96269392ecb493bd98a12aa54964c4a34dc4a22b281a016,0xeb29944a003,0x201607088341c05,0x63b8112010121d76d645319900a,0x18ee04480404875db5514c54dbcd920c,0x32d989c27a6de0952593124cd67a589a4e4a341a6e278959d47c2b9512e19,0x702612ecb493359ee24b1349cf447b0188e4662709e9b503d52a4b2625110000121da81e,0x1d47c2b950a604]

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk1290_0 : checkRows book1290 9 224 rows1290_0=true := by decide +kernel

def rows1290_1 : List Nat := [0x180d4702611ef74fb4da09765a499acf712589a4e62391989e29254964c4a220000243bd9e620,0x509553c524e13d3606,0xcc8639188e86a05,0x341e8c0863c1f3e86a07,0x391c0f8784216bec8207,0x602f1a8cc8436170ddf8401f8b0820c,0x10a2b418a90204,0x70ab8884556b6160dd55b69b20a,0xd9571108ab06f2adb6b65cbfdb8bf292bc8c4756b7d7c5d3096518c37f219fac143a01c2ac58bb9ae23,0x4d29926058022992c77022402bb6ab31384f4a92c989462220000243bd1c81a,0x3e52a4b26251c89a5324d9809,0x18ee0448040487454019208,0x6cab888455837956db5b2e5fedc5e93d5e4623ab5bebc2d184b88e453218ee04480404875dc0dc2ac58bb9ae26,0xc0b048441e994ba6930f205040180c,0x10cfd61c100b056a38202a06023cbcc143a01fc10,0x33dc4962693946f679028209249bbd98f94a92c98944d2999c15,0x361f0e86281420c10407,0xe47c3717205042d1ac210809,0x1911a612e238b005,0x240ca58461651405,0x240cc8b3216cc30b851511409,0x9130234cc8b3297e18c37f18d85091921876fd60a1d006202c1da6e278959d47c2a15d141f,0xa0834353603,0x6a3820ac481220000243c39e60a]

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk1290_1 : checkRows book1290 9 248 rows1290_1=true := by decide +kernel

def rows1290_2 : List Nat := [0x10cfd61c10bc0587a3d80c143a01fc0c,0x6733d2c4d2728df0937902820ef663e52a4b2625134a669b893ef788439241a]

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk1290_2 : checkRows book1290 9 272 rows1290_2=true := by decide +kernel

def lastUnits1290 := digits 9 25 0x9130234cc8b3297e18c37f18d85091921876fd60a1d006202c44af10

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflict1290 : checkReasons book1290 274 138 lastUnits1290 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem exclude1290 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 1290=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=1) h hc bp eq (by decide +kernel)
  let v := truth Z a1290
  have hbase : ValidThrough v book1290 224 := book_start Z h hc z eq _ _ _ _ initialClauses1290
  have h0 : ValidThrough v book1290 248 := rows_sound hbase rows1290_0 rowsOk1290_0
  have h1 : ValidThrough v book1290 272 := rows_sound h0 rows1290_1 rowsOk1290_1
  have h2 : ValidThrough v book1290 274 := rows_sound h1 rows1290_2 rowsOk1290_2
  exact book_end h2 _ _ conflict1290
end Compact

namespace Compact
open PEqualNP.Outside.L_meta_9774_aux.DagTools Resolution

def a1802 := ([2,8194,0x2802,0x3002,0x5802,34,8226,0x2822,0x3022,0x5822,1,0x40001,0x80001,0xa0001,0x2803,0xc0001,0x3003,0x160001,2049,0xa0801,0x160801,4096,6144,0x6807,0x26807,0x46807,0x66807,0x80061,0xc0061,2151,0x80081,0xa0081,0x2883,0xc0081,0x3083,2176,0x80881,0xa0881,0xc0881,4224,6272,0xd887,0x2d887,0x4d887,0x6d887,0xa2009,0xa2029,0xa00a1,161,0x800a1,0xc00a1,0x30a3,0x58a3,2208,0xa08a1,2209,0x408a1,0x808a1,0xc08a1,4256,0xa10a1,4257,0x810a1,0xc10a1,6304,6305,0xc18a1,0x90a7,0x290a7,0x490a7,0x690a7,0x248a8,0x8248a8,0x10248a8,0x18248a8,0x50a8,0x8050a8,0x10050a8,0x18050a8,0x2809,0x2829,0x82809,0x82829,0xc2809,0xc2829,0xc00c1,193,0x400c1,0x800c1,0xa00c1,0x1600c1,0x58c3,2240,0xc08c1,2241,0x408c1,0x808c1,0xa08c1,0x1608c1,4288,0xc10c1,4289,0x410c1,0x810c1,0xa10c1,0x1610c1,6336,0x60c7,0x260c7,0x460c7,0x660c7,0x40c8,0x8040c8,0x10040c8,0x18040c8,0x3009,0x3029,0x83009,0x83029,0xa3009,0xa3029,0x163009,0x163029,0xa0161,0xe0161,2400,0xa0961,0xe0961,4448,0xa1161,0xe1161,6496,2407,0x20967,0x40967,0x60967,0x181968,0x981968,0x1181968,0x1981968,0xa5809,0xa5829,5,0x20005,0x40005,0x60005,6,0x40006,0x80006,0xa0006,0xc0006,0x160006,37,2053,0x20805,0x40805,0x60805,2054,0x40806,0x80806,0xa0806,0xc0806,2085,0x4005,0x84006,0xc4006,0x4025,0x24025,0x44025,0x64025,0x5805,0x25805,0x45805,0x65805,0x85806,0xa5806,0xc5806,0x5825,0x25825,0x45825,0x65825,0x6805,0x26805,0x46805,0x66805,0x6806,0x86806,0xa6806,0xc6806,0x6825,0x7005,0x27005,0x47005,0x67005,0x7006,0x47006,0x87006,0xa7006,0xc7006,0x7025,0x8005,0x28005,0x48005,0x68005,0x8006,0x48006,0x88006,0xa8006,0xc8006,0x168006,0x8025,0x8805,0x28805,0x48805,0x68805,0x8806,0x88806,0xa8806,0xc8806,0x8825,0x9005,0x29005,0x49005,0x69005,0x89006,0xa9006,0xc9006,0x9025,0x29025,0x49025,0x69025,0x8004,0x7024,0x5904,0x9104,0x9164,0x89a4] : List Nat).toArray.map readFact

def r1802 := ([0,2048,3,2052,0x1a2809,0x1a5809,0x9a2809,0x9a5809,0x46807,0x66807,0x6805,0x22069,0x23069,2149,128,2176,131,2180,0x362889,0x363089,0x2d887,0xb62889,0xb63089,0x4d887,0x6d887,0xd885,0x14288d,0xa200b,0xa202b,0x80288f,164,2212,0x2400a9,0x2420a9,0x2430a9,0x290a7,0xa400a9,0xa420a9,0xa430a9,0x490a7,0x12400a9,0x12420a9,0x12430a9,0x690a7,0x1a400a9,0x1a430a9,0x90a5,0x8048aa,0x8848aa,0x8a48aa,0x8c48aa,0x8248a8,0x208048aa,0x208848aa,0x208a48aa,0x208c48aa,0x408048aa,0x408848aa,0x408a48aa,0x408c48aa,0x18248a8,0x248a6,0x850aa,0xa50aa,0xc50aa,0x8050a8,0x200450aa,0x200850aa,0x200a50aa,0x200c50aa,0x10050a8,0x400050aa,0x400a50aa,0x400c50aa,0x18050a8,0x600050aa,0x600c50aa,0x50a6,0x1400ad,0x280b,0x280c,0x282b,0x282c,0x8000af,0x10000af,0x10200af,0x8280b,0x8280c,0x8282b,0x8282c,0x8020af,0x10020af,0x10220af,0x1230ad,0xc280c,0xc282b,0xc282c,0x8030af,0x10030af,0x18030af,0x10230af,0x18230af,0x18430af,192,2240,2241,4288,196,2244,0x1800c9,0x1828c9,0x1858c9,0x260c7,0x9800c9,0x9828c9,0x9858c9,0x460c7,0x11800c9,0x11828c9,0x11858c9,0x660c7,0x60c5,0x40ca,0x440ca,0x840ca,0xa40ca,0x8040c8,0x200040ca,0x200440ca,0x200840ca,0x200a40ca,0x10040c8,0x400040ca,0x400440ca,0x400840ca,0x400a40ca,0x18040c8,0x40c6,0x1000cd,0x300b,0x300c,0x302b,0x302c,0x8000cf,0x10000cf,0x10200cf,8398,0x220ce,0x8300b,0x8300c,0x8302b,0x8302c,0x8020cf,0x10020cf,0x10220cf,0xa300b,0xa300c,0xa302c,0x8028cf,0x10028cf,0x10228cf,0x58ce,0x258ce,0x16300b,0x16300c,0x16302b,0x16302c,0x8058cf,0x10058cf,0x10258cf,355,356,2404,0x22969,0x23969,0x20967,0x822969,0x823969,0x1022969,0x1023969,0x60967,2405,0x60a196a,0x60e196a,0x981968,0x260a196a,0x260e196a,0x460a196a,0x460e196a,0x1981968,0x181966,0x296e,0x2296e,0xa580b,0xa580c,0xa582b,0xa582c,0x80296f,0x100296f,0x102296f,16,0x20000012,0x1000012,0x22000012,0x3000012,0x5800012,0x20020012,0x22820012,0x5820012,0x40011,0x60011,48,2064,0x20000812,0x21000812,0x2000812,0x2800812,0x23000812,0x20020812,0x2820812,0x40811,0x60811,2096,0x4010,0x2004012,0x3004012,0x4030,0x44031,0x64031,0x5810,0x22005812,0x22805812,0x3005812,0x25811,0x22025812,0x22825812,0x3025812,0x45811,0x65811,0x5830,0x45831,0x65831,0x6810,0x6812,0x2006812,0x22806812,0x3006812,0x26812,0x2026812,0x22826812,0x3026812,0x46811,0x46812,0x2046812,0x22846812,0x3046812,0x66811,0x6830,0x7010,0x7012,0x22007012,0x22807012,0x27012,0x1027012,0x22827012,0x47012,0x22847012,0x3047012,0x67011,0x7030,0x8010,0x8012,0x21008012,0x2008012,0x2808012,0x23008012,0x25808012,0x28012,0x21028012,0x2028012,0x2828012,0x23028012,0x25828012,0x48012,0x21048012,0x2048012,0x2848012,0x23048012,0x25848012,0x68011,0x8030,0x8810,0x20008812,0x22008812,0x2808812,0x23008812,0x20028812,0x22028812,0x2828812,0x23028812,0x48811,0x20048812,0x22048812,0x2848812,0x23048812,0x68811,0x8830,0x9010,0x2009012,0x2809012,0x23009012,0x2029012,0x2829012,0x23029012,0x2049012,0x2849012,0x23049012,0x69011,0x9030,0x49031,0x69031,0x20200013,0x1200013,0x22200013,0x22a00013,0x3200013,0x5a00013,0x200034,0x201c0813,0x211c0813,0x21c0813,0x29c0813,0x231c0813,0x1c0834,0x2164013,0x164034,0x964034,0x3244013,0x244034,0xa44034,0x22245813,0x22a45813,0x3245813,0x245834,0xa45834,0x226813,0x2226813,0x22a26813,0x3226813,0x226834] : List Nat).map readScheme

def table1802_0 : List Nat := [1345,2369,0xb008a83,0x58b02,0xd0b82,0x110b82,0x130c02,0x140c02,0x158c82,0x168d02,0x6a33188bc4,0x1b0e82,0x1c0e82,3777,3905,4673]

def table1802_1 : List Nat := [0xd019383,0x69402,0x1f1482,0x211482,0x239502,0x251502,0x261502,0x279582,0x289602,0xb2572a94c4,4161,0x19682,0x69702,0x2e96c963f231006,0x2a002,0x7a002]

def table1802_2 : List Nat := [0x302182,0x312182,0x322182,0x35a202,0x372202,0x392202,0x3a2202,0x3ba282,0x3d2282,0x3e2282,0x3f2282,0x40a302,0x412302,0x422302,0x11a8b44a1c4,0x302382]

def table1802_3 : List Nat := [0x312382,0x2fa382,0x32a382,0x35a402,0x372402,0x392402,0x36a402,0x3aa402,0x3d2482,0x3e2482,0x3ca482,0x3fa482,0x40a502,0x12a9348a3c4,0x31a582,0x2fa582]

def table1802_4 : List Nat := [0x322582,0x35a602,0x382602,0x39a602,0x36a602,0x3a2602,0x3ba682,0x3da682,0x3ca682,0x3f2682,0x40a702,0x41a702,0x422702,0x13a9b4ca5c4,1857,0x2a782]

def table1802_5 : List Nat := [0x2782,0x7a802,0x52802,0x50a7cde61350706,0x50a7cf6613b0706,0x50a7cf66f3b0706,0x2a882,0x12882,0x7a902,0x62902,0x52a8ce663351006,0x52a8cfa633b1006,0x52a8cfa733b1006,6593,0x32982,0x7aa02]

def table1802_6 : List Nat := [0x82a02,0x54a9cea65351986,0x54a9cfe653b1986,0x54a9d0a65401986,0x54a9cfe753b1986,0x54a9d0a75401986,0x54a9d0a7f401986,0x2ac1,0x2ec1,0x5cb182,0x3241,0x3b502,0x8b502,0x563582,0x593582,0x5a3582]

def table1802_7 : List Nat := [0x5cb602,0x5e3602,0x613602,0x623602,0x63b682,0x653682,0x683682,0x693682,0x6ab702,0x1badb6cb5c4,0x56b782,0x57b782,0x583782,0x593782,0x5cb802,0x5eb802]

def table1802_8 : List Nat := [0x5fb802,0x603802,0x613802,0x63b882,0x65b882,0x66b882,0x673882,0x683882,0x6ab902,0x1cae370b7c4,2113,0x3b982,0x3982,0x8ba02,0x53a02,0x74b9d7aad5c0806]

def table1802_9 : List Nat := [0x74b9d96ad630806,0x74b9d96bd630806,0x45010183,0x45060403,0x3ba82,0x13a82,0x8bb02,0x63b02,0x76bad82b15c1106,0x76bad9eb1631106,0x76bad9ec1631106,0x3bb82,0x23b82,0x73c02,0x78bbd86b35c1986,0x78bbda2b3631986]

def table1802_10 : List Nat := [0x78bbda2c3631986,0xb7040183,0xb7090403,0x3bc82,0x43c82,0x8bd02,0x93d02,0x7abcd8ab55c2d86,0x7abcda6b5632d86,0x7abcda6c5632d86,0x1304c003,0x4c182,0x9c182,0x7b4202,0x7c4202,0x7dc282]

def table1802_11 : List Nat := [0x7e4282,0x7f4282,0x814302,0x824302,0x83c382,0x21f0d85c244,0x7b4402,0x7cc402,0x7dc482,0x7e4482,0x7fc482,0x814502,0x82c502,0x83c582,0x22f1589c444,0x69020203]

def table1802_12 : List Nat := [0x69070483,0x4c602,0x24602,0x9c682,0x74682,0x8dc65faf77d1a06,0x8dc6606f7801a06,0x8dc6606fd801a06,0x247218fc744,0x1250a4703,0x1260bc703,0x1290c4703,0x12c0fc703,0x12e11c703,0x125124783,0x12b134783]

def table1802_13 : List Nat := [0x12e14c783,0x15c802,0x16c882,0x4c41,0x273379accc4,0x13b0a4c83,0x13d0b4c83,0x13e0ccc83,0x1400dcc83,0x1430f4c83,0x13b124d03,0x14013cd03,0x15cd82,0x16ce02,0x5141,0x51c1]

def table1802_14 : List Nat := [0x1481bd183,0x14a1cd183,0x2a751a7d344,0x80d402,0x83d482,0x2b759abd544,0x15d1e5503,0x15f1f5503,0x16021d503,0x23d582,0x15d245583,0x15f255583,0x16026d583,0x27d602,0x28d682,0x2d367b2d8c4]

def table1802_15 : List Nat := [0x80d982,0x83da02,0x2e36fb6dac4,0x17230da83,0x17431da83,0x1772f5a83,0x17832da83,0x17237db03,0x17439db03,0x177365b03,0x1783adb03,0x3bdb82,0x1723ddb83,0x1743edb83,0x1773c5b83,0x1783fdb83]

def table1802_16 : List Nat := [0x40dc02,0x5ec1,0x30781bfdf44,0x18430df03,0x189315f03,0x18b2f5f03,0x18437df83,0x18638df83,0x18b365f83,0x1843de003,0x18b3c6003,0x18c3fe003,0x40e082,0x63c1,0x32f95c9e444,0x19856e403]

def table1802_17 : List Nat := [0x19b576403,0x19c58e403,0x19e59e403,0x1a1556403,0x1a35a6403,0x1985ee483,0x19b5f6483,0x19c60e483,0x19e61e483,0x1a15d6483,0x1a3626483,0x19865e503,0x19b666503,0x19c67e503,0x19e68e503,0x1a1646503]

def table1802_18 : List Nat := [0x1a3696503,0x6ae582,0x6941,0x35babd4e9c4,0x1af566983,0x1b1586983,0x1b259e983,0x1b5556983,0x1af5e6a03,0x1b1606a03,0x1b261ea03,0x1b55d6a03,0x63ea82,0x1af656a83,0x1b1676a83,0x1b268ea83]

def table1802_19 : List Nat := [0x1b5646a83,0x6aeb02,0x6dc1,0x37fbdddee44,0x1c058ee03,0x1c259ee03,0x1c5556e03,0x1c060ee83,0x1c261ee83,0x1c55d6e83,0x1c067ef03,0x1c268ef03,0x1c5646f03,0x6aef82,0x39bcbe4f1c4,0x80f282]

def table1802_20 : List Nat := [0x83f302,0x199927383,0x19a93f383,0x19d947383,0x19f957383,0x1a096f383,0x1a297f383,0x1cfd24c03,0x1859d7403,0x1879e7403,0x1889ff403,0x18aa0f403,0x18da17403,0x1d1c75103,0x15ca4f483,0x1d3b15303]

def table1802_21 : List Nat := [0x1d3b25383,0x1c4a5f503,0x1d5e35303,0x1d5e45383,0x1c1ae7583,0x1c3af7583,0x1c4b0f583,0x1d7e35883,0x1d7e45903,0x1aeb9f603,0x1b0baf603,0x1b3bb7603,0x1b4bcf603,0x1d9db5e83,0x1e2ef59b604,0x54a9d2a8f46a606]

def table1802_22 : List Nat := [0x23d4ea94ba045,0x29d52974ca305,0x9744aa54e8043a647,0x4ba014ea944a1c6,0x152a732a604,0x2014ea94b9945,0x2014ea94c9905,0x152a732a204,0x14ea9401944,0xa754a003,0xa953a203,0xa9539903,0x3501,0x8954a9c3,0x2e41,0x11b8c9a2010f8bc0c7]

def table1802_23 : List Nat := [0x8bc563719344206,0x48004c3,0x6d41,0x1379ccec3,0x6841,0x32dce7bc83bcde76633589,0x6bf64e7093bde7900c1bcec7b17ea8d,0x357afd9061aee7090bde79000b78c,0x6bf64d76fea05,0x31d8f82c4,0x18090bde7b2d5ebf20e76b804b,0x1aeef78b804,0x1def170b684,0x6024ef79ecb5f90739bcec7b17b5cd,0x4f8f61279e4365af73bbcde76a04c8d,0x385def1633585]

def table1802_24 : List Nat := [0x1dee178b184,0xef70bc43,0x1c3b2d3b1c4,0x6cb4faf7384802f363642674095b68d,0x6cb4faf6339c240179e42674095b60d,0x73ec824f399d00f6ef379db21af70acce,0x49e733c81edde6f3b6cb5ee7a0384d,0x6bdb3b2d4b285,0x65b9cf790779bcedb2d4b58a,0x3bf646f3b1edcf90d7b809,0x188bc1279e40f6ef379db64e7d7df0d,0x1bcf783bee105,0x19d82c3,0x70b9dd3afd932c6,0x656cb5ee774ea46,0x8947dacc45e093cdceefc8204b]

def table1802_25 : List Nat := [0x77bc42,0x64596c3134785,0xc3058059791620987,0x64596c10c4705,0x365a973849e66f3de0cc45e61b04039165b590,0x6cb5ee7093ccde7bc1988bc01c8b80d,0x1cee1d900723af8eb2c8,0x35fb2652f04,0xcad939f5e1200b84de7bc1bccbd948f6a4f,0xc897b5ee770ec82401799bcf78365478e,0x644bce1093ccde7bc18075ee7d9474d,0xbd73b87641200bce386f3de0cc45eca358f,0x64764e7d7848026f3d979e662c1b28d,0x8fb5848bc624481c7,0x6bdb3b2d4ab05,0x15a0b00b1197409f4708]

def table1802_26 : List Nat := [0x1eaf35b1bcf78331179d20b56b68c,0xd7ec96cf37aba4de7bc1988bc0b65af0e,0x7abcd8cb66bad46,0x2d196bd14c785,0x27d405a00416cb5ecc88,0x8d96bd5a4705,0x3a75fb2379ef06622f3d5e6b605b2cd,0x195b274ebc16f579adb291ea0360c,0xcad7ba7640b7abcd6d1eca500b,0x32b5ee9d939c5,0x6bdb7abd92b05,0x656bdd3b205bd5e6b6a0478a,8193,0x45af15ae774a386,0x7141,0x1d7a9f379751e9d907]

def table1802_27 : List Nat := [0x2d367e5d46a7cdebf4c8,0x4182eb588305,0x159add743,0x38369b3f2ea353e6d708,0x83059eeb630306,0x286ad0580680cb624708,0x286a149a2dce6f5682c02cba0310c,0x83cd8ad9630486,0x1b3b2d4b1c4,0x160af96cba592bd587,0x1b2d4ec420c67580c081360accb,0xd7a38f07f49a2cde0165ecb6203022b4e,0x38f5fb25637c5,0xeaf60af8345,0x82c59eeb630306,0x8b16780d860dab84c8]

def table1802_28 : List Nat := [0x36183562cfabf587,0x281430580596bd5a4c88,0x143a02f56601d932f5ee705ad0b,0x82d5e6d7630486,0x159b1309bcf07f7580764cbd7b9de60401ea50,0x1ccd48ed89bf65af65a789,0x1af6311362ed75b807,0x671ebf62ed630087,0xd7ecb53b101f581b5758ab0a,0x1af71f00060dabf5b63b2d4ac4b,0xd7f001b57eb38f63b201ea4a,0x1afd931c3,0xc167ebc1a0371ea763b259f58b,0xb4f37a7d7a9c046,0x1435682c02cba03107,0x3a60eeb8244]

def table1802_29 : List Nat := [0x33d58ac66c8206,0x1b2e16a777b1e03447,0x11c88d4b644,0x1ccc66a322b57ac6588309,0x6b3d87d65880c6,0xd7ea4c8bd61b18c688eb2b4a,0x1108ed4f584,0x31a235ec6d48086,0x309bcf07f79ebf64f574ad816bd69328e,0x4418c07d762ec8c2bd61bb8a,0x9d3eb84c4,0x2b57ad29bce46a33a04789,0x8e446a43,0x834d6ac6798486,0x365af309bce6633547e86ad5eacd6ac1a001d0,0x1b60af80c4]

def table1802_30 : List Nat := [0x33199ec1768086,0x6acd9ec101f586,0x61446c8c71f56af566c15ae00b,0xc26fc0e104,0x9decb5e64652786,0x3506344184c9b28fab48,0x32d5eac66b8206,0x8e4447c3,0x1afd96a385c0ddb5c7,0x1820ed7ecb500d0480c8,0x1afd88198cc1768087,0x184de783fbcf5fb27a82dd2bd5b358d,0x73319ab63afd96a23c6137aa0b,0x472202,0x4f19365af73984f6f35aab4e26c09388e,0x56b0c16016232e80be9ec70a]

def table1802_31 : List Nat := [0x4f1916adfd96bdcead309ece26c79848e,0x1cead6febf65b109bac06b30232cc,0x3b18cfa645a984f6add96bdbfb15983ce,0x6fe9cc27bd8bb4e26c0683b5fb274bd56a0b56af52,0x643b18cfbb23debf62616fb58b,0x64309ecec633ecd6811ed8b658c0360ec9a3a9c93993,0xc3319f55acb63190c27b3b501b3b160ec9a3a901c793,0x309ecec64634755acb8f83ca,0x190c27b3b3195acb8ec7c9,0x1af6198cfaad65990f6d9d8b0764d1d4984ec5e8f2a13,0xd797986633eab596643b36762c1d91ef526168c792,0x76319f4c8c6309ed5ac38e2f996d960ecb63a96883d3,0x3625e321d8c67dd7984f7b26fb2cc,0xcc5d7ec9d2f565501993d05820c,0xb106b3d86090700c7,0xc27b3b18cfac5d7ec99540662c586cf9eaa10]

def table1802_32 : List Nat := [0x326bf65a965184f676319f562cf665f8e,0xc27bbfe104,0x5ed898cfa613d9db5fb23237cb,0x35eacd93284,0xb45eb2c6a33575026f399ec70b,0x1d2c6309ece26c5702d66cb5a2f4c,0x35fb2562f04,0x6bf64acd8ac407d606ea49,0x1b2309ed5cb3321d8c67d562c763af05ba4f,0xc60869d63b1758307,0x15c64309ecec633ed0362b3d7ec958b18f02d0,0xc27b3b2f58ccb320288,9089,0x3640358f581bb1566bc8,0x1b1d970373c26bea07,0x1b106ac407d6d93787]

def table1802_33 : List Nat := [0x1b15880fac0d70ec87,0x439e82,0x1774d9fc3,0x9b45a403,0x2ee8bb7a584,0xbba6c2,0x5dc1,0x1afd4b083,0xd47331a275fb1718088,0x1206330ec75fa96cbb88,0x63481875fb1d4b647,0x39d7bafd4ec5d603eb2b49,0x73ec4c203d49fdd601021e0dfaf79ab0e,0x9031ebf6261d481c7,0x198a61379fc17af7aba57a7865020d,0x6a762c5309bcfe0bd7bd5d2bd3c0341c0676b291]

def table1802_34 : List Nat := [0x4818f5e61d8ea46,0x4875d16bda1d0197afe981ca,0x31ec75e610424286cba0018a,0xc661d7ec520cb046008,0xcb632f5208b9d81c7,0x483197a8b65cec6,0x24c7afd4304d473018389,0x3098f6290d7b2c6,0x4832b5e6131acd82b55e83ca,0x2d66330a404,0x30bd762ed749b01a0ed782cf6715eb58e,0x184f67631ebf627d543289,0x76ebf620d05984d8cb749c4f60e7aaf4e,0x27a0105ab596c3a03108,0xec633eebcc27bd8aa08,0x27a010580de6e7d7bac09b1a02f0c]

def table1802_35 : List Nat := [0x1d7b101811e73d05805cfafa032cc,0x105af55b3da03487,0x834de6c66d8486,0x36dceadd7af757b175840080309b5cd,0x184f67136005e6e7d7ec5d6030202cd,8577,0xb92202,0x5c81,7297,0x196895e8284,0xfa76d8b78de0b65aa08,0x44ab02,0x73ab406eb0981385b1e032ca,0x890683c3,0x70ec5be0d01f586,0x19d20b5eab67cf5a00209]

def table1802_36 : List Nat := [0x357b1068241ced67ea48,0x37ba416ad7aec5da0d072f4a,0xd90183583b1d4f587,0x448342,0x73ab5d7b10632c6,8769,0x63282,769,0xcb5eba03,0x65af42,0x65ba42,0x32c1,0x3a01]

def encoded1802 (i : Nat) : Nat :=
  if i < 288 then
    if i < 144 then
      if i < 64 then
        if i < 32 then
          if i < 16 then
            table1802_0.getD (i%16) 0
          else
            table1802_1.getD (i%16) 0
        else
          if i < 48 then
            table1802_2.getD (i%16) 0
          else
            table1802_3.getD (i%16) 0
      else
        if i < 96 then
          if i < 80 then
            table1802_4.getD (i%16) 0
          else
            table1802_5.getD (i%16) 0
        else
          if i < 112 then
            table1802_6.getD (i%16) 0
          else
            if i < 128 then
              table1802_7.getD (i%16) 0
            else
              table1802_8.getD (i%16) 0
    else
      if i < 208 then
        if i < 176 then
          if i < 160 then
            table1802_9.getD (i%16) 0
          else
            table1802_10.getD (i%16) 0
        else
          if i < 192 then
            table1802_11.getD (i%16) 0
          else
            table1802_12.getD (i%16) 0
      else
        if i < 240 then
          if i < 224 then
            table1802_13.getD (i%16) 0
          else
            table1802_14.getD (i%16) 0
        else
          if i < 256 then
            table1802_15.getD (i%16) 0
          else
            if i < 272 then
              table1802_16.getD (i%16) 0
            else
              table1802_17.getD (i%16) 0
  else
    if i < 432 then
      if i < 352 then
        if i < 320 then
          if i < 304 then
            table1802_18.getD (i%16) 0
          else
            table1802_19.getD (i%16) 0
        else
          if i < 336 then
            table1802_20.getD (i%16) 0
          else
            table1802_21.getD (i%16) 0
      else
        if i < 384 then
          if i < 368 then
            table1802_22.getD (i%16) 0
          else
            table1802_23.getD (i%16) 0
        else
          if i < 400 then
            table1802_24.getD (i%16) 0
          else
            if i < 416 then
              table1802_25.getD (i%16) 0
            else
              table1802_26.getD (i%16) 0
    else
      if i < 512 then
        if i < 464 then
          if i < 448 then
            table1802_27.getD (i%16) 0
          else
            table1802_28.getD (i%16) 0
        else
          if i < 480 then
            table1802_29.getD (i%16) 0
          else
            if i < 496 then
              table1802_30.getD (i%16) 0
            else
              table1802_31.getD (i%16) 0
      else
        if i < 544 then
          if i < 528 then
            table1802_32.getD (i%16) 0
          else
            table1802_33.getD (i%16) 0
        else
          if i < 560 then
            table1802_34.getD (i%16) 0
          else
            if i < 576 then
              table1802_35.getD (i%16) 0
            else
              table1802_36.getD (i%16) 0

def book1802 (i : Nat) : Clause := let n := encoded1802 i; unpackLits 9 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClauses1802 : inputsOK 2 1802 a1802 r1802 (baseBook book1802 350).toList=true := by decide +kernel

def rows1802_0 : List Nat := [0x390e02e93c03,0x1505c128443088a208ba1e86a218760b,0x502384c32044310922309a252be1e0562e85c0e,0x3305a158ba268961609207,0xcc150ba2688e1405cb089808,0x541385c168ca22ac42e8c808,0x228822e8c203,0x2488c2689831ac82e8c407,0x922309a260ca132c4110802e8c80a,0x130462e8c203,0x541385c168c6b38421f2ca2e8c40a,0x4ab1880112ccb408606,0x922309a252cc2184a200c2130462e8c80c,0xc81504e2e89a2508e1405c15ad2b50442008a0e,0x541385c15ad41087cb0064b5ad22f0d6300d82e8c410,0x1504e170561087cb0064b5ad22e8c40b,0x368f23c0e838112442d8418d23f0f40b,0x5996a5815a5f1726396c6317809,0x172569705f16e5718a06,0x18a5815e5f1745896a592e05dade5a17a561866117e5516c12,0x2d891a60352563424e33a6208,0x1b4009aa001a804,0x2d88723e352323422633a4208,0xa24e93c41112442d8420f4370d22e8a0011a2641a40191c481146700264a82878daa3a4469800270aa20]

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk1802_0 : checkRows book1802 10 350 rows1802_0=true := by decide +kernel

def rows1802_1 : List Nat := [0xa32285394c399444680e0501204190690066880447122450a02a8a24e93c390fab70ba27196a1a223e112441083f8e23c8f0b60ec97aea96a58a3a44699a031,0x28c8a150530ee5111a0381404810641a4019a20111c488ea940e83c8f03925491a62b62483d11465a86888f8a3a44699a026,0xea3c8f03925444910b60fe941080a,0x1a4019a20119004,0x3a8e83c8f03891e472f2648006728287a8e911a600a4891a62b62f0bbadc4512019,0x3b1043a0f23c2d8388fe2e94009,0x442d8420ea3e93e3b0e82e91209,0x10e39106449103eabc3c8f0b62f8bd93a288aa282f4bb09c2e94014,0x13a4f90e41912440fe3d0ba2a8a0bc9920019ca0a1ea3a44698024711e9424698ad8bb24c370dabe9ae021b0b7114270a226,0x110b610e4f8dc2e8f43691208,0x140390ba449103eabc3c8f0b62f8bf90e0c,0x3c2f8af0fa368f444910b6106c00f20b,0x3c0e83925491a62960da3d112442d8418f20d,0xa32285414c3b94446a8e911a60281404810032f2679b66a1ba019b80111c488ea9424698ad8978ec4519a21,0x28c8a14e530e63494446a8e911a60281404810032f2679b66a1ba019b80111c48a5a91a62b6254390e24519a22,0x11cbc9920019ca0a1e00a5091a6296aea368f23c2d8c1b08c124c280aa2893ac089ca2224a3a4469adc4511e22,0x280aa2893ac089c648006728287a8e911a60091c478e23c8f03aa4891a629690844910b62f0370fac2adc452f223,0xdc3c8f03aa4698ad896a4c08,0x262b6258baa4c3724606,0xa02a8a24eaf6271920019ca0a1ea3a4469802471209224698a5e3b0e83c8f0b6310c38e2940fe452f220,0xbf2948229682a9a869bcc4b0c09,0x2128320402,0x1b8011ba01ae604,0x97a4698a503c8f038922c1248450da3d112442d8420ec11]

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk1802_1 : checkRows book1802 10 374 rows1802_1=true := by decide +kernel

def rows1802_2 : List Nat := [0x98ad896a48478e2c3adc4524609,0x47a50b71143c8f0b60ea39254c731a47318280aa2893ac0b1227290c5a18c505013ab67c86cac9ee1a07a1e076792007fab8b90541705610aba99202a6a1a6f0da33,0x13c412dc2eaf6c08dc06,0x242b6236a099c00a30a219ea3a4469a1c0c,0x90ad88da82648008d28c6680a050120400c641a4019a201322a3a4469a1c17,0x242b6236a09920022ea1996a3a4469a1c0c,0xa31a00381404810021b0872428da8267002641a468b266ba94821a86e8066e0046da9682b16a4318a6a1a6f3244714e530deb71444692036a5891a62b624c37114a3a4469a3437,0xa31a00381404810021b0872428da8267002641a468b266ba94821a86e8066e0046da9682b16a4318a6a1a6f32447152530ee5111a4824891a62978ec3a0f23c2d8ca10440914a3a4469b0e38a503fa343f,0x97a4698a50920f23c0e28aa1c90a36a099c00af24731aa3a44698da3d112442d8420ec1b,0xe29430e02,0x1b06a1ba6e1b6a5a0ac5a90c629a869bc67a888f10e05012018100111c039a0a32405494c39b0e41912440f49224698ad89694446b1ca3a44698082e,0x6e9b86d99ea223c43912440f46c29682b16a4318a6a1a6f00805012018100111c039a0a32405414c37b04930dc5111a478da3c8f03a8e495330b711487242b622aa099c00b2ea3a44699a83b,0x9531c3c8f0b60ea3691e472f2ccb2ecb2dc450e40f,0x1ba6e1b6a5a0a0301404806040040299aa32405414c37b04930dc5111a6ba9482316a43184711eb7114a6a1a6f196a1a3a43112442d83d0daa3a44699a830,0x1b6a5a0a6a1ba6e1aea5208c5a90c629a869bc65a868e90c05012018100111c0299aa32405494c39906449103d24891a629694446b1c950e43c8f03ab3687242b622aa09920032ea3a4469b34ca80c3e,0x25e91a62942483c8f038a2a872428da8264800cd28e911a6368f44491035908ce32aad9f21b2b27b9e4801feae2e4aea6480a18280aa288501a07a1e0761504e170561089cc79464583e4eb204d8ec3e,0xec3c8f036a4698ad89225e08,0x1ba019b8011b6c91046bb2687a8264800a3a446990244910b61083d1a816,0x120400e6828c8d21c90a36021b06a1ba6e1b6c8a1ea099c00a8e911a641112442d8420f4641a4019a20133e548eea5a0aa5208c5a90c6118480ea3a114a6a1a6f01434,0x120400e6828c8d21c90a36021b06a1ba6e1b6c8a1ea099c00a8e911a641112441083d1906900668804cf94e37adca5a0aa5208c5a90c61184825891a62930dc3c8f0b6340cf25038914a6a1a6f0143e,0x3c2d83b9503994e348f207,0x90ad88da2aa099c00a28a31a0a3a4469a1c0d,0x90a368aa826480088a86659ae641a468b46038140480604004021b0a3a44698f844910b61083fa1c1f,0x90ad88da2aa099200228a319aa3a4469a1c0d]

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk1802_2 : checkRows book1802 10 398 rows1802_2=true := by decide +kernel

def rows1802_3 : List Nat := [0x2428da2aa099c00a24a219e641a468b4a0281404810031b66a1ba019b801348a5208a5a0ac5a90c629a869bc4631ad1304920da3d28e911a63e912442d8420fed0a1c34,0x1b06a1ba6e1b667a888f10e050120181001118c700e6828c9015239906449103f8e23d24891a62b625a950e4a3a446980826,0x6c1a86e9b86d99ea223c43912440f4050120181001118478dab7114039a0a3240540dec10fecba4c370f23c2d83ab4ea3a446980829,0x3c2d83a8e49531c3691ecbadc450f20b,0xe43c8f036a4698ad89225408,0x90ad8d422acba1ea099c00a8e911a6d50ea96a1c0f,0x1380f13a0fb2004,0x9324698a58940f23c2d83a120cbab27985ead9ea189e4801fe2489a250861287c181f4ae2e41305c15b5811064aea6480914388dc29,0x2d899a78352723426c33a7a08,0x2a2d71c20601a6fa7cac1c4a82a40a,0x2a2d71c20601a6fa7cab9c4a79ded7aa60c,0x4c12e49adc03,0x1d4079cc071ca04,0x1c00581a6fb60aa29c06,0x12e4993402,0xc910444910b61083d21ea0992001a86e8066e0046c998a2ae8a3a44699b617,0x4810039a0a3234872428d8086c1a86e9b86db2287a8267002a3a446990444910b61083d1906900668804da81423,0x3c2d83b9523794e530d2510f209,0xdc3c8f03a24698ad89624c08,0xe9d6748340c82c7602407,0xa9ce0a032099d072b72ab35caaa6a99a7a9d26ed9b60789e09f9c6b89c8a0158a7364769dc70016069be0d8380c0220b820da25c91a62b624c0d03a2f,0xa9ce0a032099d072b72ab35caaa7699a7a9ba68d9b60789e09f9c6b89c8a0158a7364769dc70016069be0d8380c0220b820d8a4a91a62978ec3c8f0373744a36e46946db298858a2a5a148121883206a43184735a458bcb50be4eb204e05c15b581106417a9a869bcdc0e240a503f912442d8420f40d03a5f,0x442d83f8e2cf2f03691207,0x380d82a738280c8300b826741ca77022768200d03a10]

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk1802_3 : checkRows book1802 10 422 rows1802_3=true := by decide +kernel

def rows1802_4 : List Nat := [0x12e4993202,0x9c2669ead89d268d9b7aab35cd81e27827e71ae2722805629cd91da081dc089c00581a6faaa1d,0xaab7aab35c99a7ab62749a2a8d91da081dc08a700f,0xe0501201810010086c2f26628aba28e911a66cb4610,0xa219e641a468a8e911a6cb0fed280a050120400c6d9a86e8066e004e0a2417,0x14c5134402,0x27099a7a9d268d9b72ab35c0d8380c02edf8e4d81e27827e71ae27228056386e129885a96852048635883206a4318a6a1a6f0fa470daa73647682077022df11ac68f8de1089724698ad8c10fe38b3c921c00581a6faaa44,0x3720d8380c02eab35caaa763b0f23c0e4952669ead89ba68d9b60789e09f9c6b89c8a0158e1b84a6216a5a148121883206a4318a6a1a6f0fa470dac1248a7364768207702270016069bed891ac68fe94252e205e459464a0bcb58be190f8de108dd890248701408e26894d60861f0a02b8b42c13ac81381803427b7a62,0x2d891a5c4d2503fa4a4c10234a620a,0x98a5c4ca524c0f834a483d112442d8e31244aa460f,0xe00e4cf24698ad89225c07,0x24c91a6297380410f23c0ec9daaadeaacd72669ea6e40a68388fe44910b60f4e40dc1a,0x9aaaadeaacd72669ea749726e408f23c0ec97a4698a4a388fe44910b60f8e48dc19,0xdc2503f912442d8418f4d50e8960e20b,0x26a99a7ab62749bb72ab35c0d8380c02ee52a8d91da081dc08aaa14,0x7827e71b6003,0x4810039a0a3234872428d8086c1a86e9b86db2287a8267002a3a446990444910b61083d1906900668804da81423,0x18a5815e5f1745896a592e05dade5a17a6218260154e69e2a01c85596c16,0x3c2d83b9523794e520d2508f209,0x24a91a6297a669ead89da6808,0xe624698a4c370f23c0ece8aaadcaacd70360e0300bb949b90244910b60f4aa39ea736476820e39084b1dc088b22d0ac4e03470016069bee814ae729885a96850908121883206a431846120468c0320bc4db204e8a2230bacf114290a6e2ab47a30eac9e6120462705ea6a1a6f370ad9ea189e4801fe2489a253582184a1f0607d2b8b904caea6480a5c6d,0x37c43112442d83d128479162f2d42f93ac01382b0b42c8343f85c158502389a253582187c110d24511a20,0x2aadcaacd70360e0300bb8099a7ab62749a2a8d91da081dc08a7014,0x300c82f08c4c92a491365013a2c0b42bba8e990c92ab47a1e4801fe2489a253582187c7d2b8b904caea6480a4698a5a4204a1183443912442d83f8f42e92c31]

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk1802_4 : checkRows book1802 10 446 rows1802_4=true := by decide +kernel

def rows1802_5 : List Nat := [0xb22d0ac4e034970f8e392c300c82f1364f13a288a6e2ab47a0481189c3e9124410896a4698ad8923aa190e43f8e2e92dc230bae5ab27985ead9ea189e4801fe2489a253582184a1f0607d2b8b904caea6480ba842,0x98ad896908929324a90ce3ab47a1e4801fe7d2b8b92ba992024b0c0320bc2484c2309a253582187c2e9244db204e8b02d0ae128460d2462b,0xa324087242b622a87a8264800d50ea9680a050120400c6d9a86e9b86ca9885998a2ae8a3a44699906900668804d5a96852048635883206a431846352a6a1a6f19a33,0x28867a8e911a63e912442d8420fec8990691a2d280a050120400c6d9a86e8066e004e0a968529885a048620c81a90c629a869bc46122453b02411a29152e5ab2799e4801fe2489a253582187c7d2b8b904caea648094e528c0b50bc522dc50b9ea736476820770222c8b42b04a0d1c00581a6f8a22989e4e0481189c4da2464,0x78a8072158b8b9a05,0x6c1a86d99ea223c43912440fe3d014039a0a324087242b622a87a8267002a3a44698081b,0xa3240872428aa1ea09920000a0500c6d9a86ca9885998a2ae8a3a4469990691a2ed95253146513b427a9cd91da081dc08ba6193543aa4a91a62b625a70016069be469b86e8120181001296850908121883206a43182811cc738aad1e8298a212046271162f0c82f93ac03b2ebbac398e43f8e2e9396ac9e6ad9ea189e4801fe7d2b8b92ba992022484c2309a253582184a1f0602e85ea6a1a6f19a7b,0x14c5115002,0xdc8360e0300baacd72aa9aa669ea749baa8e69e2a029cd91da080ae2d0b00d1dc089c00581a6f9c8562e227bba9028c6680a050120400c6d9a86e8066e0046c998a2ae8872428aa1ea0992002f2280a62893ac09362711ca3a4469946da11a47916b711443112440d63d128c10fe9337a59,0xdc8360e0300882e0837a07,0x12a4913402,0xaabbeab35c99a7ab62749baa8d91da081dc08a6a0f,0x11a290a62789c5414a52142e7a9cd91da081dc089c00581a6fbc22c8b42b1384f93a2f90e0d3c0c124c4312c300c82f08c2ebbcac9e6792007f9f4ae2e4132ba9920212046a621624a968509026894d60861287ca6a1a6f10844910b60fe3d3b04c,0x3588120c81a1804,0x4591e473182832ed50ea96adc452d62f93ac8138278bc11,0x4691e46318292dc450c82f1364f93a288a6f2290f1bc4cba52ad1e837a9a869bcac9e6792007f9f4ae256342ba99202120462710e370f23c0ea420e441912442d8412543d0921308c26894d60861287c2e8c041,0x14850b4402,0xaabbeab35c99a7a9ba529a2a8e7a9cd91da0838e4212c770222c8b42b1380d1c00581a6fbccd280a050120400c6da96850906a1ba019b8011b2a6216f1a90c629a869bc6628aba28e911a6bc9184891a941142914a300c82f1364f93a288a6e2ab47a0ea12046270ec3c8f0b60e4950fa230bae58f8bc2b2798daf285e192b67a862792007f89226894d60861287c181f4ae2e4132ba99202ee2767b,0x3b0f23c0e4952669ead89a0f8bc2760b,0xf08dc44910b60fe940f436bd0aabbeab35c9baa8e7a9cd91da081dc089c00581a6f90c1b,0x1344a924e390c04,0x3b0540dec124c37112442d83f8f4369080c,0x67a88890fabc21c90a368aa8267002a3a44699a86e8066e004e0a968529885bc6a4318a6a1a6f118489143a8f23c0d839254d13d62409226894d60861f148528a42989e2711a94142f48b22d0ac4e034f53969492c30136c813a2f9b649,0xd91da081dc089c00581a6fb9a78a80f0b684a0dc43112440f4948ae2d0b00d1c8562e227bba46bb6d525a6e1ba048060400447352458a0a5a14243c6a43c81929a869bc378f23c2d83ab8a298a24eb004d8fe9409c39254e59462f0c8f6046ad1e8ac9e6ad9ea189e4801fe7d2b8b92ba99202ee3ce178482484c2309a253582184a1f0602ea9c6b]

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk1802_5 : checkRows book1802 10 470 rows1802_5=true := by decide +kernel

def rows1802_6 : List Nat := [0x6d9a86b29283994a1238428140299aa324087242b622a87a8264800a3a4469990691a2edb2e5414c41944469b86e812018100111cd48a0a5a1081218d621281a90f2108a6a1a6f00c39,0x652848b21c90ad88d9a86e8066e0046db2487a8264800a3a44699ac15,0x4810039a0a3234872428d8086c1a86e9b86db2287a8267002a3a44699906900668804f79045394cb714446a9684100a4a0e81218d621281a90c60a047120cb8fe44910b63dce5914a6a1a6f0143d,0x940fe469204539640912442d8423740b,0xd91da081dc089c00581a6fb60789e09f9c6b89c8a0158f0b6846b52e590c449103fb2e94a4698ad896be2f811621088268940f88e1f1464a0bcb58be278a82889c930ae2d8b00d29c39,0x6d9a86e9b86b29283994a123842814048100299aa32405421c90a2a87a8264800a3a44699906900668804d594850bd2f03044325291a629690844910b6136c08fe4ea96842048635884a06a43184611eb7114a6a1a6f00c45,0x120400e6828c8d21c90a36021b06a1ba6e1b6c8a1ea099c00a8e911a6641a4019a2013de413a0e7a9cd91da081dc089c00581a6fb9840a5c91a62e3a968410044910b6108a4a0e8121884a06a431846120c38e2943e69312c2108826894d608e1f0b22d8ac0d11a528c0b58bc4db96450a42a09e4e3204ebe4378da3709ca6a1a6f01468,0xaabbeab35c9baa8e7a9cd91da081dc088b22d8ac0d1c00581a6fba0528c08d28c6800e05012040086c1a86e8066e004290a827938c813a2fad62f11627118a3a4469ba235,0xaabbeab35c9baa8ed09ea73647682077022d892892a4698a5e70016069bedb9468d28c6800e05012040086c1a86e8066e004470a02a0a24e9404d8bc320c046920fa9141505c1584a218442289a253582387c2e89c6db2287242b623687a8267002a3a4469ba251,0xbc8a02a0a227120458bcb58be4511c0b,0x2f2290a82793827120468c0b58bc4db204ebee4511810,0x84a04862102209a253582387c82a96fb38e4d9084b31846120468c0dc114290a827938c813a2f89ca6a1a6f29023,0x8621284296fb0ae2d8b00d08826894d608e1f206a4318280a82893a501362e89c47120458bcb5bf2dc114a6a1a6f20425,0x2aaefaacd726eaa3b427a9cd91da080ae2d8b00d1dc08b624a24a91a62b625e70016069bedb91a51bdea5a102229283884268942387c812180fa1281a90c60a02a0a22711c481162f2d62f914a6a1a6f3a240,0x2aaefaacd726eaa39ea736476820e392c770222c8b62b03470016069bee814af7a9684088a4a0e212048621281a90c61184811a300c82f1361505c1584a218442289a253582387c450a42a09e4e1404ebf6400ba2729a869bcfc3f44137840af0e58ec3c8f0388fe44910b6108fa3a258,0x1b66a1ba6e1ac652848e01404806040040299aa324054b9687242b622acba1ea0992003543aa5aa3a4469af246352d59485080c28,0xa7364768207702270016069beea39e0b,0x12c4ab96493fc2c8b62b034fe94a290a827938c813a270be45b1c468c09513218,0x6d9a86b194a12380500a66a8c9021c90a2a87a8264800a3a4469990691a2ed95253146513b427a9cd91da081dc089c00581a6fba8df1282b8b62c034469b86e812018100111c47916b7114280a82893a501362f2d6ff8e6a4a0e2110e44910b60fecb8f4d50ea968e4c3b962e89ca5a102209a253582387ca6a1a6f00c63,0x3588121281a1804,0x11a47918c60a4d52dc450c82f1365013a288a8f229100c0092a4698a5abc10c42a9a869bc2710e449103fb2e390f23c2d83abf8fa3961505c1584a218442289a253582387c2e8c038,0xea96b5402,0x2848821c90ad88da2aa09920028e911a66b1a86d80c0500ad299414,0x67a888921c90ad88da2aa099c00a8e911a66a1b00201403b46641a468c0804810a5a106e0046e806a4a0f00a90c611848914a6a1a6f1b62b]

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk1802_6 : checkRows book1802 10 494 rows1802_6=true := by decide +kernel

def rows1802_7 : List Nat := [0xe29433c02,0xea0e4cf24698ad89225c07,0x94c0ee7a9cd91da081dc089c00581a6f8b22d8ac4e3003f93a2f834f340a2108826894d608e1f14a36b8e4212c302d62f11648c0703114e5bd22d,0xb624697132949304b8d249a6209,0xaabbeab35c9baa894c0eed09ea7364768202b8b62c0347702270016069bee1b460381404810021b06a1ba019b8010a02a0a24eb004d8fe271b667a888921c90ad88dc068aa82670030328e911a651c12e5a484a0bcb58c046c1036bd049,0x13ac0138278a82909c3fad62f1164891c450be0e,0xaabbeab35c9baa894c0eed09ea7364768202b8b62c0347702270016069bee1c08048106e1baa4a0e211906900668805052968408900a90c60a02a0a24eb004d8fe2729a869bc51c12921282f0c83011b040f63e8f905c0ce5c062e8da3d404ad1e81484eac9e617ab67a862792007f8547d2b8b908a268942385017056d63da1107c182ba99202193d06d,0x2aaefaacd726eaa364768207702294c0e36bd00e,0xec3c8f03925499a7ab626e94a760a,0x3c0ec978e4ea25c91a62b641c9a2a8d91da081dc08aaaefaacd724c3e8da3d0f219,0x2629790e94a6e99a7a9d268aa3647682077022930dc3c8f03a908393a843112442d907a461c,0x1305c158501e878d60710606e09,0x7e268942186a792007fab8b92ba992027c86c1e878d6077061ea14,0x42170561306e26894d60861a87c0a,0xae2e4aea648084c170561087c79200d61ea1f9f40f,0x1ecae2e4aea64809e4801f22205c1584a2189a254287f0741e878d642615425060441a,0x6c1e8781c41879200d61fc241ecae2e4aea64808450888f0a9f214,0x442d84230e410f4cf0e4adc2caea64809120d,0x12ce3b96adc2caea64808c42f136c813a2c0b42b834248450888e2309a253582187c2e8c01c,0x39891a62930dc3c8f03b3a2aabbeab35c9b90244910b60f4aa39ea736476820e39084b1dc088b22d0ac0d1c00581a6f8a2e814ae729885892a5a142409a250861abc6a431846120468c0b04182f1361f358c3b3c450a42989e4e0681989ca6a1a6f370adc2caea6480a5c54,0x2acd72aae8a6e0d8380c02ee4b66d81e27827e71ae2722805629cd91da081dc08b6270016069be92a4698a5e3b0f23c0dcdd1290c04c1b89edb91a51b6ca62161c050a5a14243c6a4318280a6288681989c47120458bc310be4eb210c892114222388c26894d60861a87c2e914a6a1a6f37040912442d84230e3d33cadc2caea6480b7268,0xdf11a47adc45396adc2caea648090d0ba4a91a629690844910b60fe3d3a817,0x388adc2caea6480c0606,0x28c9021c90a2a87a826480002814031b66a1b2a62166628aba28e911a6641a468bb65494c39944ed29cd91da081dc08b7c92a4698a5a4210c44910358fe3d396adc2caea64809c00581a6fc36469b86e8120181001296853c6a43184711e38c350e1162b8b42c034249282809e298a24eb204d8662709026894d60861a87c1a146b7114a6a1a6f19a6c]

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk1802_7 : checkRows book1802 10 518 rows1802_7=true := by decide +kernel

def rows1802_8 : List Nat := [0xec148e5ab70b2ba992025095209,0x4ab96493fc92a469890c44910b60fe3d3543aa5aadc2caea6480c2f0f13217,0xa219ea3a44698fac8c2e641a468b4a0281404810031b66a1ba019b801382a5a14a6216f1a90c629a869bc46122453cc36b9ea7364768207702270016069bf038f43e112442d8e39090f8e6248a42989e1a09c5291a2409a250864b0c02c8b42b138c00fe38c344e8beb04182f43a1f358e5ab70b2ba992021a8660d22463,0x9ee191ae10fa280a62893ac09361a04017056d604c1b8662711cc6916518dac12b70b2ba99202920f444910359083fbb426,0xc050120400ad2af2f606a6a1ba019b801382290a627938c013a2f8681989c4612246914d114a302c1060bc1f35852396adc2caea6480942368f444910b61083fa51101b636,0x7682077022a71c00581a6fc4306c301984c1bb624692245b96adc2caea6480914949283e0f444910b61083f85023a5110444a621624a968509026894d60861a87ca6a1a6f36437,0xa24eb004d8fe2831847122459141a04017056d604c1b866270a614,0x2931846122468c04509e4e3003f93a2fada2f4481a04017056d604c1b866270a619,0xb2f4ab70b2ba992022b138c813a0d0b40c,0x7682077022a71c00581a6fc4306b6246922459144a0f83d112442d83fa9885a96850902f0c42fc4d11bc61a29112b96adc2caea6480a501429a869bc94c410c0661306e42092114222388c26894d60861a87c2eb6443,0xee946ed09ea7364768207702270016069bef0b6846928e590c44910b60fe3d0ae2d0b00d1b86e81201810013bca621624a9685090268942186af1a90c60a0298a21a0662711c47916d50ea96ab70b2ba99202b7114a6a1a6f0bcb04182f87c0fbb64d,0x90468a42989e271505294850bd22c8b42b13819834f010c4b0c0310bc114222388c4d93e4ec50948de43912440fe940f4d525a370f23c2d83a8e495440e5ab70b0bb13ab47c2b27b868792007fab8b909226894d60861a87caea6480bb04a,0x373e63d2b70a88eaea64808de36a4c0b,0xe63c8f0a5a1042a4a91a630baf11514a4b0882c8b62b03443112440d83fb2e3d3543aa5aa4a0e2109a253581f402a431846352468c0adc2a23aba99202290a827938c813a2f89ca6a1a6f3fe3c,0x29cd91da081dc089c00581a6fc1ae38f83d3cc4db024ec0a3d8fa44910b61083fb96adc2a23aba992031539e22,0x4810039a0a3234872428d8086c1a86e9b86db2287a8267002a3a44699906900668804f790044910b61083d01423,0x39891a62930dc3c8f03b3a2aabbeab35c9b90244910360f4aa39ea736476820e39087702270016069bee813716a9283c2ea5a1100a90c61184833c94114a6a1a6f396adc2aaea64808e31612c2c8b62b034290a827938c813a270891591a2109a253582387c2f94a3025c54,0x2acd72aae8a6e0d8380c02ee4b66d81e27827e71ae2722805629cd91da081dc08b6270016069be92a4698a5e3b0f23c0dcdd36e469204545b0bb7040912442d84230e3d33c38ab70b2ba99202943723e,0xf0c1b086c0080500ed1990691a2a22243eb2d0234453144ed29cd91da081dc089c00581a6fc1b04b96920f846b1aadc2caea6480812040f66e0046e806a3a44698da3d112442d8420ff178f23c,0x6d9a86b194a123842912440fe3d0140299aa324087242b622a87a8264800a3a4469990691a2ed9b86e812018100100c25,0xf0b60e6548de5414c510f208,0x7501edfc2edf24a91a6243112442d83fb9670016069bed81e27827e71ae27228056436bc2b70b2ba992023d29c23,0x364768207702270016069bed81e27827e71ae272280563c2da10c449103f8f494a4698ad8930dd19c6446b5318c5ed525ae5ab70a88eaea64808eb1829283a9684402a42e66e0046e806a6a1a6f29c3e,0x12048b524746821088281464a0ae2d8b00d09e2a0a24eb204d89c458bc30c5c7dab47e872208bae5ab27e1e4801f42289a2508e1c07a1e359148401907c109ecae2e4112b70b2ba992024540c3c]

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk1802_8 : checkRows book1802 10 542 rows1802_8=true := by decide +kernel

def rows1802_9 : List Nat := [0xae2e4aea64808802689423886129e4803587e4231a9ee121ec13,0xae2e4aea648088026894238861a9e4801f9089ee1a07a1e0761505c15b591b46b061ec1b,0x541705612c6a1e878d606b060760a,0x138278aa290681e8781dc182713a2f8c42f116c68fe470542009a2508f088871c04e17056d646a2eb96acc6eadc2caea6480b0028,0x11a8607c1f89a2535823c231a8865294850b9ea7364768207702270016069bf06b8e4212c30396adc2c3e0b22e0ac4e4700d0f4acc6eaea6480936c813a2fb4c32,0x364768207702270016069bed81e27827e71ae2278aa2889c722805633a1f87d068ae2e0b04eb004d8350491a48916e5914920f84a0bc3147414912442d8420fe1a07a1e0770647303406adc2c138baad1f0792007f854170567b2b8b908026894d608f08c6a21c70acc6eaea6480a9c58,0xf03b3a29426e408e23f912442d8420dcf88f4acc6eadc2caea64808f216,0xdcbc10c44910b60fe3d2530db2eadc2d1e116aabbeab35cd9ab31bab47c1e4801fe151291db60789e09f9c6b88ac722805633b061ecae2e4aea64808801f87c2689423c22218bcb68bea7364768202b8b82c0531c04e170560fc6a0d1dc089c00581a6fbc250,0x3c243252bc24698a5aacc6e42112442d892c20adc2caea64808dc14,0x3c0ea39952379509028c6680a050120400c6d9a86e8066e0046b996a1a3a4321c90a2a87a8264800bc91847adc4535642112442d83f8f45228e911a6e5ab31bab70b2ba99202508f239,0x4ab96adc2c493fc92a4698ad90bab31baba992024db204e93213,0x3c0e5ab70b2532025aacc6eaea64809091f936c093aa52081f2968287e26894238871c31708c6a86358a43184611eb7114a6a1a6f10c44910b60fe3d3d230,0x3984230eacc6e91a62930dc3c8f0b60ece8ab70b2ba99202aabbeab35c9baa8d91da081dc08a5c1e,0x50948e7a9cd91da081dc089c00581a6fc84e3b9640912442d8420f48607c1fb0e38ab70b250acc6f2091a290aa279381a07a1e0770609d1d94aad1f0792007f9ecae2e4aea648092c300c42f136c813a150802689423c2221c701385c15b591a8bb1eb424f,0x38c4b912442d8420f446920e5ab31bab70b2ba992024512612,0x98a5a94934929324b90c44910b60fecb8f4e592646b53224764a2b47c1e4801fe7b2b8b92b31bab70b2ba99202458bc310be4eb204e0ac2e0b3218520d0542009a2508f088871c04e17056d646a2ea463f,0x98a5a9493492ab47e9324b92843112442d83d1264691e458bc308be4eb004e0ac2e0b21c87a1e06f061f6792007d1ecae2e40d0fee584c2009a2535823c231a8871c047228bacbc06acc6eadc2caea6480adc4524643,0x104a483e3784212303488459282f0c22f93ac81382b0b82c9f60d0462eab47e8721e8781bc18792007d04d229ecae2e42009a2535823c231a8871c48ce5ab31bab70b2ba992024511a39,0x1b66a1ba6e348a5208a5a0a05012018100100ad2b445314436b2cc507c1fbb427a9cd91da081dc089c00581a6fc1a2b8b82c0343e48ead1fa1c87a1e06f060f444910b610851916c5a18a4318280aa2893ac01362f2d43011a3fb96adc2c121f6792007d04d229ecae2e42009a2535823c231a8871c09c4729a869bcacc6eaea648080c68,0x138c013a2fb962a8a51d2b47e8721e8781bc1844910b6108308bc45b1a3fc90acc6eadc2c118ba121f6792007d04d229ecae2e4aea648088026894d608f08c6a21c702709e36,0x50948e7a9cd91da081dc089c00581a6fc8438b8e4b48e40912442d8420f4ad1fa1c87a1e06f06250528c08607c1f8a42a89e4e3204e8be308bc4592103396acc6eadc2c450462e8487d9e4801f41348a7b2b8b92ba992022009a2535823c231a8871c09d24b4251,0x364768207702270016069bee69e2a0484388ae2e0b00d48e40ab47e8721e8781bc18941c8562e227b2a51a181f07e280aa2893ac809cc4936121f6792007d04c7b2b8b908026894d608e21c7108c6a458bcb50c046c9522912442d8420f5032b31bab70b2ba9920324a9c54,0xc5316a43184729a869bc45bb427a9cd91da081dc089c00581a6fc7cad1fa3d407238ae2e0b01c87a1e06f06034280aa2893ac01363fb2ee5ab31bab70b1f6792007d04c7b2b8b92ba992022009c1207e518bcb50c046c8a1f09a2508f08c6a21c708635925b3851]

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk1802_9 : checkRows book1802 10 566 rows1802_9=true := by decide +kernel

def lastUnits1802 := digits 10 57 0x9c6007f275cb15452906032955a3f4390f43c0de0c2586091c5f1845e22da993023175975663756e1692c243ecf2400fa09a453d95c5c95d4c9011004d129ac11e118d4438e04e

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflict1802 : checkReasons book1802 589 79 lastUnits1802 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem exclude1802 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 1802=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=2) h hc bp eq (by decide +kernel)
  let v := truth Z a1802
  have hbase : ValidThrough v book1802 350 := book_start Z h hc z eq _ _ _ _ initialClauses1802
  have h0 : ValidThrough v book1802 374 := rows_sound hbase rows1802_0 rowsOk1802_0
  have h1 : ValidThrough v book1802 398 := rows_sound h0 rows1802_1 rowsOk1802_1
  have h2 : ValidThrough v book1802 422 := rows_sound h1 rows1802_2 rowsOk1802_2
  have h3 : ValidThrough v book1802 446 := rows_sound h2 rows1802_3 rowsOk1802_3
  have h4 : ValidThrough v book1802 470 := rows_sound h3 rows1802_4 rowsOk1802_4
  have h5 : ValidThrough v book1802 494 := rows_sound h4 rows1802_5 rowsOk1802_5
  have h6 : ValidThrough v book1802 518 := rows_sound h5 rows1802_6 rowsOk1802_6
  have h7 : ValidThrough v book1802 542 := rows_sound h6 rows1802_7 rowsOk1802_7
  have h8 : ValidThrough v book1802 566 := rows_sound h7 rows1802_8 rowsOk1802_8
  have h9 : ValidThrough v book1802 589 := rows_sound h8 rows1802_9 rowsOk1802_9
  exact book_end h9 _ _ conflict1802
end Compact

namespace Compact
open PEqualNP.Outside.L_meta_9774_aux.DagTools Resolution

def a2567 := ([6146,8194,0x2802,0x3002,0x4002,0x6002,6178,8226,0x2822,0x3022,0x4022,0x6022,0x60041,0xa0041,4167,96,0x60061,0x80061,0xa0061,0x2863,0x4063,2144,0x60861,0x80861,0xa0861,4192,0x61061,0xa1061,6240,2151,0x20867,0x40867,0x60867,0x80081,0x60081,0xa0081,0xc0081,0x3083,0x100081,0x4083,0x180081,0x6083,2176,0x80881,0x60881,0xa0881,0xc0881,0x100881,0x180881,4224,0x61081,0xc1081,0x101081,0x181081,6272,0x5087,0x25087,0x45087,0x65087,0xc087,0x2c087,0x4c087,0x6c087,0x45888,0x845888,0x1045888,0x1845888,0x245888,0xa45888,0x1245888,0x1a45888,0x102009,0x102029,0x182009,0x182029,0xa00a1,0x600a1,0xc00a1,0x40a3,2208,0xa08a1,0x608a1,0xc08a1,4256,0xa10a1,0x610a1,0xc10a1,6304,0xa18a1,0x618a1,0xc18a1,0xf8a7,0x2f8a7,0x4f8a7,0x6f8a7,0x3648a8,0xb648a8,0x13648a8,0x1b648a8,0x62809,0x62829,0x800c1,0xa00c1,0x1000c1,0x40c3,0x60c3,2240,0x608c1,0x808c1,0xa08c1,0x1008c1,4288,0x610c1,0x810c1,0xa10c1,0x1010c1,6336,0x618c1,0x818c1,0xa18c1,0x1018c1,4295,0x210c7,0x410c7,0x610c7,0x48c8,0x8048c8,0x10048c8,0x18048c8,0x83009,0x83029,0x103009,0x103029,0x60101,0xa0101,0xc0101,0x140101,0x180101,0x6103,0x1a0101,2304,0x60901,0xa0901,0xc0901,0x140901,0x180901,0x1a0901,4352,0x61101,0xa1101,0xc1101,0x141101,0x181101,0x1a1101,6400,0x61901,0xa1901,0xc1901,0x141901,0x181901,0x1a1901,0xc107,0x2c107,0x4c107,0x6c107,0xd907,0x2d907,0x4d907,0x6d907,0x340108,0xb40108,0x1340108,0x1b40108,0x3a1108,0xba1108,0x13a1108,0x1ba1108,0x64009,0x64029,0xa4009,0xa4029,0xc4009,0xc4029,0x184009,0x184029,0x180181,0xc0181,0x1a0181,2432,0x180981,0xc0981,0x1a0981,4480,0xc1181,0x1a1181,6528,0xd987,0x2d987,0x4d987,0x6d987,0x461188,0xc61188,0x1461188,0x1c61188,0xc6009,0xc6029,8197,8229,0x22025,0x42025,0x62025,0xc2026,0x182026,0x2805,0x62806,0xa2806,0x2825,0x22825,0x42825,0x62825,0xc2826,0x182826,0x4005,0x24005,0x44005,0x64005,0x64006,0x84006,0xa4006,0x104006,0x4025,0x4805,0x24805,0x44805,0x64805,0x64806,0xa4806,0x4825,0x24825,0x44825,0x64825,0x5805,0x25805,0x45805,0x65805,0x65806,0x85806,0xa5806,0x105806,0x5825,0x7805,0x27805,0x47805,0x67805,0x67806,0xa7806,0x7825,0x27825,0x47825,0x67825,0x9005,0x29005,0x49005,0x69005,0x69006,0x89006,0x109006,0x9025,0x2884,0x48a4,0x78a4,0x5904,0x9104,0x7924] : List Nat).toArray.map readFact

def r2567 := ([0x41849,0x42849,4165,96,0x2862,97,2144,0x22862,2145,4192,0x42862,99,100,2148,0x22069,0x22869,0x822069,0x822869,0x40867,0x60867,2149,131,132,2180,0x141889,0x144089,0x25087,0x941889,0x944089,0x45087,0x1141889,0x1144089,0x65087,0x5085,0x303089,0x306089,0x2c087,0xb03089,0xb06089,0x1303089,0x1306089,0x6c087,0xc085,0x106588a,0x108588a,0x10a588a,0x110588a,0x845888,0x2106588a,0x2108588a,0x210a588a,0x2110588a,0x1045888,0x4106588a,0x4110588a,0x1845888,0x45886,0x90c588a,0x918588a,0xa45888,0x290c588a,0x2918588a,0x490c588a,0x4918588a,0x1a45888,0x245886,0x408e,0x2408e,0x10200b,0x10200c,0x10202b,0x10202c,0x80408f,0x100408f,0x102408f,0x608e,0x2608e,0x18200b,0x18200c,0x18202b,0x18202c,0x80608f,0x100608f,0x102608f,160,2208,2209,4256,4257,6304,0x3e18a9,0x3e30a9,0xbe18a9,0xbe30a9,0x4f8a7,0x13e18a9,0x13e30a9,0x6f8a7,0x1be18a9,0x1be30a9,0xf8a5,0xd8648aa,0xd8c48aa,0x2d8648aa,0x2d8c48aa,0x13648a8,0x4d8648aa,0x4d8c48aa,0x1b648a8,0x6d8648aa,0x6d8c48aa,0x3648a6,0x6280b,0x6280c,0x6282b,0x6282c,0x8018af,0x10018af,0x18018af,0x10218af,0x18218af,0x18418af,0x420c9,0x428c9,0x440c9,0x210c7,0x8418c9,0x8420c9,0x8428c9,0x8440c9,0x410c7,0x10418c9,0x10420c9,0x10428c9,0x10440c9,0x610c7,0x18418c9,0x18420c9,0x18428c9,0x18440c9,4293,0x848ca,0xa48ca,0x8048c8,0x200848ca,0x200a48ca,0x10048c8,0x400848ca,0x400a48ca,0x18048c8,0x600848ca,0x600a48ca,0x48c6,0x1620cd,0x8300b,0x8300c,0x8302b,0x8302c,0x8020cf,0x10020cf,0x18020cf,0x10220cf,0x18220cf,0x18420cf,0x40ce,0x240ce,0x10300b,0x10300c,0x10302b,0x10302c,0x8040cf,0x10040cf,0x18040cf,0x10240cf,0x18240cf,0x18440cf,0x303109,0x305109,0x306109,0x2c107,0xb03109,0xb05109,0xb06109,0x4c107,0x1303109,0x1305109,0x1306109,0x6c107,0x1b03109,0x1b05109,0x1b06109,0xc105,0x361909,0x362909,0x366909,0x2d907,0xb61909,0xb62909,0xb66909,0x4d907,0x1361909,0x1362909,0x1366909,0x6d907,0x1b61909,0x1b62909,0x1b66909,0xd905,0xd14010a,0xd18010a,0xb40108,0x2d14010a,0x2d18010a,0x1340108,0x4d14010a,0x4d18010a,0x1b40108,0x6d14010a,0x6d18010a,0x340106,0xe86110a,0xe8a110a,0xe9a110a,0xba1108,0x2e86110a,0x2e8a110a,0x2e9a110a,0x13a1108,0x4e86110a,0x4e8a110a,0x4e9a110a,0x1ba1108,0x6e86110a,0x6e8a110a,0x6e9a110a,0x3a1106,6414,0x2190e,0x6400b,0x6400c,0x6402b,0x6402c,0x80190f,0x100190f,0x180190f,0x102190f,0x182190f,0x184190f,0x290e,0x2290e,0xa400b,0xa400c,0xa402b,0xa402c,0x80290f,0x100290f,0x180290f,0x102290f,0x182290f,0x184290f,0xc400b,0xc400c,0xc402b,0xc402c,0x80310f,0x100310f,0x180310f,0x102310f,0x182310f,0x184310f,0x4610d,0x18400b,0x18400c,0x18402b,0x18402c,0x80610f,0x100610f,0x180610f,0x102610f,0x182610f,0x184610f,384,2432,387,388,2436,0x363189,0x366989,0x2d987,0xb63189,0xb66989,0x4d987,0x1363189,0x1366989,0x6d987,0xd985,0x118c118a,0x119a118a,0xc61188,0x318c118a,0x319a118a,0x1461188,0x518c118a,0x519a118a,0x1c61188,0x461186,0x318e,0x2318e,0xc600b,0xc600c,0xc602b,0xc602c,0x80318f,0x100318f,0x102318f,8208,8240,0x23002032,0x6002032,0x22031,0x23022032,0x6022032,0x42031,0x23042032,0x6042032,0x62031,0x23062032,0x6062032,0x2810,0x1802812,0x2802812,0x2830,0x3002832,0x26002832,0x3022832,0x26022832,0x42831,0x62831,0x4010,0x21804012,0x2004012,0x22804012,0x21824012,0x2024012,0x22824012,0x44011,0x21844012,0x64011,0x4030,0x4810,0x21804812,0x2804812,0x21824812,0x2824812,0x44811,0x21844812,0x2844812,0x64811,0x4830,0x44831,0x64831,0x5810,0x1805812,0x22005812,0x2805812,0x4005812,0x1825812,0x22025812,0x2825812,0x4025812,0x45811,0x65811,0x5830,0x7810,0x1807812,0x22807812,0x1827812,0x22827812,0x47811,0x22847812,0x67811,0x22867812,0x7830,0x47831,0x67831,0x9010,0x2009012,0x24009012,0x29011,0x1829012,0x24029012,0x49011,0x1849012,0x24049012,0x69011,0x1869012,0x24069012,0x9030,0xa2014,0x230a2033,0x60a2033,0x1922813,0x122834,0x922834,0x29e2813,0x1e2834,0x9e2834,0x21964013,0x2164013,0x22964013,0x24164013,0x164034,0x21a44013,0x22244013,0x4244013,0x244034,0x219e4813,0x29e4813,0x1e4834,0x9e4834] : List Nat).map readScheme

def table2567_0 : List Nat := [0x180702,0x1a0702,1857,2113,0x9c240783,0x1f0a82,2881,0x9c300a83,0x2b0c82,3393,0x9c360c83,0x34010c83,0x10e02,0xd0e02,0x220e82,0x240e82]

def table2567_1 : List Nat := [0x2e0f02,0x300f02,0x330f82,0x391002,0x410fc3d0ec4,0x3c031883,0x31b02,0xf1b02,0x441b82,0x4c1b82,0x551c02,0x581c02,0x5e1c02,0x631c82,0x641c82,0x681c82]

def table2567_2 : List Nat := [0x6d1d02,0x751cc711bc4,0x481d82,0x501d82,0x551e02,0x5c1e02,0x601e02,0x661e82,0x6a1e82,0x6d1f02,0x7d1ec791dc4,0x451f82,0x431f82,0x461f82,0x4c1f82,0x552002]

def table2567_3 : List Nat := [0x592002,0x572002,0x5a2002,0x5e2002,0x632082,0x652082,0x682082,0x6d2102,0x8520c811fc4,0x492182,0x502182,0x552202,0x5d2202,0x602202,0x672282,0x6a2282]

def table2567_4 : List Nat := [0x6d2302,0x8d22c8921c4,0x13c080083,0x13c140383,0x32382,0x82382,0xf2402,0x142402,0x9123c5f134541386,0x9123c69134621386,0x9123c6917c621386,0x14c0a0083,0x14c160383,0x32482,0xa2482,0xf2502]

def table2567_5 : List Nat := [0x162502,0x9524c61144541486,0x9524c6b144621486,0x9524c6b184621486,9665,0x2841,0x9f2982,0x2a41,0xa72b82,0x2c41,0x982d82,0x9a2d82,0xa22e02,0xa42e02,0xa72e82,0xaa2e82]

def table2567_6 : List Nat := [0xac2e82,0xaf2f02,0xb22f02,0xb42f02,0xbd2ecb92dc4,0x982f82,0x9b2f82,0xa23002,0xa53002,0xa73082,0xaa3082,0xad3082,0xaf3102,0xb23102,0xb53102,0xc530cc12fc4]

def table2567_7 : List Nat := [0x53182,0x3182,0x113202,0xc3202,0xc931ca32649e0986,0xc931cab264a60986,0xc931cb3264ae0986,0xc931cab28ca60986,0xc931cb328cae0986,0xc931cb32acae0986,0xca3c82,0xcc3c82,0xce3c82,0xd53d02,0xd63d02,0xd83d02]

def table2567_8 : List Nat := [0xda3d02,0xdc3d02,0xdf3d82,0xe03d82,0xe23d82,0xe43d82,0xe63d82,0xe93e02,0xea3e02,0xec3e02,0xee3e02,0xf03e02,0xf93dcf53cc4,0xca3e82,0xcd3e82,0xd53f02]

def table2567_9 : List Nat := [0xd83f02,0xdb3f02,0xdf3f82,0xe23f82,0xe53f82,0xe94002,0xec4002,0xef4002,0x1013fcfd3ec4,4801,0x74082,0x24082,0x134102,0xe4102,0x10540cd932cd41286,0x10540ce332cde1286]

def table2567_10 : List Nat := [0x10540ced32ce81286,0x10540ce3364de1286,0x10540ced364e81286,0x10540ced38ce81286,0x344080183,0x344140483,0x74182,0x84182,0x134202,0x144202,0x10941cdd33cd43406,0x10941ce733cde3406,0x10941cf133ce83406,0x10941ce7374de3406,0x10941cf1374e83406,0x10941cf139ce83406]

def table2567_11 : List Nat := [0x10e5082,0x1105082,0x1125082,0x1195102,0x11e5102,0x1205102,0x1225102,0x1275182,0x12c5182,0x12e5182,0x1305182,0x1355202,0x13a5202,0x13c5202,0x13e5202,0x14951d4550c4]

def table2567_12 : List Nat := [0x10a5282,0x10c5282,0x1165282,0x1195302,0x11a5302,0x11c5302,0x1245302,0x1275382,0x1285382,0x12a5382,0x1325382,0x1355402,0x1365402,0x1385402,0x1405402,0x15153d4d52c4]

def table2567_13 : List Nat := [0x1115482,0x1125482,0x1195502,0x1215502,0x1225502,0x1275582,0x12f5582,0x1305582,0x1355602,0x13d5602,0x13e5602,0x15955d5554c4,0x10a5682,0x10c5682,0x1175682,0x1195702]

def table2567_14 : List Nat := [0x11a5702,0x11c5702,0x1255702,0x1275782,0x1285782,0x12a5782,0x1335782,0x1355802,0x1365802,0x1385802,0x1415802,0x16157d5d56c4,0xa4000203,0xa40c0503,0x95882,0x5882]

def table2567_15 : List Nat := [0x155902,0xc5902,0x16558d1b42d180a06,0x16558d2942d260a06,0x16558d3742d340a06,0x16558d2946d260a06,0x16558d3746d340a06,0x16558d374a5340a06,0x274040203,0x274100503,0x95982,0x45982,0x155a02,0x105a02,0x16959d1d435182706,0x16959d2b435262706]

def table2567_16 : List Nat := [0x16959d39435342706,0x16959d2b475262706,0x16959d39475342706,0x16959d394ad342706,0x95a82,0x65a82,0x155b02,0x125b02,0x16d5ad1f43d183406,0x16d5ad2d43d263406,0x16d5ad3b43d343406,0x16d5ad2d47d263406,0x16d5ad3b47d343406,0x16d5ad3b4b5343406,0x4541,0x95b82]

def table2567_17 : List Nat := [0xa5b82,0x155c02,0x165c02,0x1715bd2344d184506,0x1715bd3144d264506,0x1715bd3f44d344506,0x1715bd3148d264506,0x1715bd3f48d344506,0x1715bd3f4c5344506,0x5cc1,0x5ec1,0x5c0b6003,0xb6182,0x176182,0x1746202,0x1766202]

def table2567_18 : List Nat := [0x1796282,0x17c6282,0x17e6282,0x1816302,0x1826302,0x1846302,0x1876382,0x18f6358b6244,0x1746402,0x1776402,0x1796482,0x17c6482,0x17f6482,0x1816502,0x1826502,0x1856502]

def table2567_19 : List Nat := [0x1876582,0x197655936444,0x34c060283,0x34c120583,0xb6602,0x66602,0x176682,0x126682,0x19b6657d5d5783486,0x19b665835d5803486,0x19b665835f5803486,0x6741,0x1a568da167c4,0x69d0e6783,0x6a1136783,0x1196802]

def table2567_20 : List Nat := [0x69d1e6803,0x6a1236803,0x1276882,0x69d2c6883,0x6a1316883,0x1356902,0x69d3a6903,0x6a13f6903,0x6ac1,0x6b0196a83,0x6b81b6a83,0x1b76d5b36c44,0x6e1756c03,0x6ed726c03,0x6e17d6c83,0x6ed7a6c83]

def table2567_21 : List Nat := [0x1816d02,0x1876d82,0x1c3705bf6f44,0x714206f03,0x718236f03,0x724246f03,0x7142c6f83,0x7182f6f83,0x724306f83,0x337002,0x714347003,0x397082,0x7341,0x1d574dd173c4,0x75c207383,0x760257383]

def table2567_22 : List Nat := [0x75c2c7403,0x760317403,0x337482,0x75c347483,0x760377483,0x397502,0x1e177ddd76c4,0x1817782,0x1877802,0x1e979de578c4,0x7a8457883,0x7b4427883,0x7b8477883,0x7c04d7883,0x7a8597903,0x7b4567903]

def table2567_23 : List Nat := [0x7b85b7903,0x7c05f7903,0x637982,0x6d7a02,0x7cc1,0x1fb7e5f77d44,0x7f0997d03,0x7fc967d03,0x7f0a37d83,0x7fca07d83,0xa77e02,0x7fca87e03,0xaf7e82,0x7fcb07e83,0x207816038044,0x1818102]

def table2567_24 : List Nat := [0x1878182,0x20f8360b8244,0x848cb8203,0x854ce8203,0xd58282,0x840d78283,0x854dc8283,0xdf8302,0x840e18303,0x854e68303,0xe98382,0x840eb8383,0x854f08383,0x85c1,0x865aa6703,0x6e5a68603]

def table2567_25 : List Nat := [0x6e9a98603,0x759ad8683,0x86dda6c03,0x86ddc6c83,0x7f9af8703,0x876006c03,0x876026c83,0x7adc48783,0x7b1c78783,0x7bdc88783,0x7c5ca8783,0x87df27303,0x845c48803,0x84dc68803,0x851cb8803,0x886167303]

def table2567_26 : List Nat := [0x7f5d68883,0x7f9d98883,0x88e007683,0x88e027703,0x7fc1,0x1715bd135184,0x1715bd135104,0x5c56f5483,0x1715bd135584,0x1715bd135504,0x5c56f44c3,0x5c56f5603,0x1715bd3f4d04,0x54d43565494885,0x1715bd235584,0x5c56f5243]

def table2567_27 : List Nat := [0x1715bc2,0x16558d340a1614dc6,0x163594285804,0x16558c285404,0x53d515855f4685,0x16558d1b0a15f5286,0x16558c284a04,0x16558c2846c4,0x16558c285384,0x595630a03,3585,0x7141,0x1e9215ed1d48118c6,0x8d24c6b1887d21c522548,0x75c1,0x40cff414fd3c85]

def table2567_28 : List Nat := [0x1033dcff414f93f46,0x3fd0540cf73e45,0x10540cff3e04,0x415033fc3,0x10540c2,0x852444e23c621d4541348,0x1d46f2147f1785,0x2444e23c621d4851307,0x188140383,0x6ddb56ec3,0x63d8d65d955d05,0x1a55256b3416d499a869d45548a,0x49959525185acd05b5a869da5488b,0x5acd04996d6a1a7695a15089,0x69da85acd05b52650d496889,0x1a869d6d5acd0499184d48]

def table2567_29 : List Nat := [0x4d1185acd05b5a869da35109,0x1345acd05b52650d4547c8,0x5b5345acd06a1a7685a35209,0x461a869d265b56b3414368c9,0xd069da84996d5ad1850c8,0x4996d5acd06a1a74607,0x1266a16d69d6b341345088,0x1a84996d5acd069da34d08,0x6a16d5acd0499a768c7,0xd04996d5ada869c6,0xd04996d5adb763d976048,0x23452254621f4931ac7,0x7d1ec93254522186,0x21888d2547d0286,0x2244621d4850206,0x189260503]

def table2567_30 : List Nat := [0x188080083,0x624982,0x18887234931f4951487,0x63d8d65d955f05,0x5d57d6ddb56e05,0x68d6d5ada8341a75207,0x5b56b524d051d344ec7,0x69d47525a868da54787,0x11f5acd05b5a868da55088,0x14769d6b3416d68da84d08,0x63d976dd475acd068d6d6049,0x624082,6273,0x298066d9763d7d0187,0x42507342153e05,0x20f342158490941e0d3708]

def table2567_31 : List Nat := [0x2123e60f834f73546,0x212425073421583e0d3dc8,0x84a153410941e0f8347,0x3410941e158305,0x857a509341071146,0x75215e93410941c6,0x18f65d7c6084,0x1d4857a4d065d8063d9b5c09,0x66cd26019763d995f07,0x3418063d974105,0x63d8d65d955e45,0x3419763d805c05,0x6181,0x804c2,0x2c126003,6913]

def table2567_32 : List Nat := [0xae314c7098ab3246,0x3d719bf0cc4,0x324c7098a32f05,0xc931ca3098b92986,0x7f0c7098c93005,0x1fc305f729c4,0x7f02631cc928c5,0xc7324262e4b73106,0xc1324c7098b92606,0x2f4b9304c529c5,0xc7324262e4c12bc6,0x1fc31c263244,0x515f461674d14f584104749,0x144614f57d674d1610408,0x27761cf0c84,0x9dd8719bf73c5]

def table2567_33 : List Nat := [0x719d8724276fc5,0x3d761d10cc4,0x1c6725d809c4,0x51630303,0x59d694349c5385,0x434140415f59d184d07,0x10d0501059d5f4606,0x5354f5755f4d45,0x510d59c1057c5,0x1459d0d0404,0x1df816236c84,0x1b577e0588c4,0x1ee2002,0x7b81,0x140202,0x719c1761d30f05]

def table2567_34 : List Nat := [0x719d80cc3,0x52c9c59d695785,0x1675a49c57d5b5406,0x2716752d69545344e47,0x50104d03,0x32099fc0504,0x271675a51d5385,0x271675a51d5855f5307,0x135271675a51d57c6,0x4d56959c9c4745,0x1675a49c5784,0x1355a5672704,0x21650003,0x271675a55d5385,0x14f271675a54d4306,0x9c59d694704]

def table2567_35 : List Nat := [0x1c68882,0x5c066003,0x1800502,0x6001]

def encoded2567 (i : Nat) : Nat :=
  if i < 288 then
    if i < 144 then
      if i < 64 then
        if i < 32 then
          if i < 16 then
            table2567_0.getD (i%16) 0
          else
            table2567_1.getD (i%16) 0
        else
          if i < 48 then
            table2567_2.getD (i%16) 0
          else
            table2567_3.getD (i%16) 0
      else
        if i < 96 then
          if i < 80 then
            table2567_4.getD (i%16) 0
          else
            table2567_5.getD (i%16) 0
        else
          if i < 112 then
            table2567_6.getD (i%16) 0
          else
            if i < 128 then
              table2567_7.getD (i%16) 0
            else
              table2567_8.getD (i%16) 0
    else
      if i < 208 then
        if i < 176 then
          if i < 160 then
            table2567_9.getD (i%16) 0
          else
            table2567_10.getD (i%16) 0
        else
          if i < 192 then
            table2567_11.getD (i%16) 0
          else
            table2567_12.getD (i%16) 0
      else
        if i < 240 then
          if i < 224 then
            table2567_13.getD (i%16) 0
          else
            table2567_14.getD (i%16) 0
        else
          if i < 256 then
            table2567_15.getD (i%16) 0
          else
            if i < 272 then
              table2567_16.getD (i%16) 0
            else
              table2567_17.getD (i%16) 0
  else
    if i < 432 then
      if i < 352 then
        if i < 320 then
          if i < 304 then
            table2567_18.getD (i%16) 0
          else
            table2567_19.getD (i%16) 0
        else
          if i < 336 then
            table2567_20.getD (i%16) 0
          else
            table2567_21.getD (i%16) 0
      else
        if i < 384 then
          if i < 368 then
            table2567_22.getD (i%16) 0
          else
            table2567_23.getD (i%16) 0
        else
          if i < 400 then
            table2567_24.getD (i%16) 0
          else
            if i < 416 then
              table2567_25.getD (i%16) 0
            else
              table2567_26.getD (i%16) 0
    else
      if i < 496 then
        if i < 464 then
          if i < 448 then
            table2567_27.getD (i%16) 0
          else
            table2567_28.getD (i%16) 0
        else
          if i < 480 then
            table2567_29.getD (i%16) 0
          else
            table2567_30.getD (i%16) 0
      else
        if i < 528 then
          if i < 512 then
            table2567_31.getD (i%16) 0
          else
            table2567_32.getD (i%16) 0
        else
          if i < 544 then
            table2567_33.getD (i%16) 0
          else
            if i < 560 then
              table2567_34.getD (i%16) 0
            else
              table2567_35.getD (i%16) 0

def book2567 (i : Nat) : Clause := let n := encoded2567 i; unpackLits 10 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClauses2567 : inputsOK 2 2567 a2567 r2567 (baseBook book2567 420).toList=true := by decide +kernel

def rows2567_0 : List Nat := [0x2fa2caf62baf22aaee2a2ea08,0x5d16e8722803,0x5b1668722603,0x5f1765fb4ad31a2589a08722a09,0x6b9aa8722803,0x6a1a48722603,0x6d1b06db50d4b4e8722a07,0x5e9b25d2305b22e5922a6d1b08717e0b,0xd59ae8c1a88ba1cd39b607,0x5c97e5b1b66a1ac05,0x6b9aa8722c03,0x5d16e5f96a699b6d735ad5b4e593548722c0d,0x5f176d7b5803,0x1c87b9c07b1b87a1d606,0x19c751907b9887b1807a1d07399e0a,0x1967519c6636204,0x6119e621d6701bc05,0x3646f9e4601bc611d606,0x1e4619d67118c67b6ada190d9b64721b80c,0x7918675b647118c67b6663b6a719eadb1b80d,0xd91cc651c07a9b879990639d609,0x36c6019e621c6da370d9b64db9e60a,0x889da879d8dc9e2069de0636009,0x374a92b404aac032a601ab608]

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk2567_0 : checkRows book2567 10 420 rows2567_0=true := by decide +kernel

def rows2567_1 : List Nat := [0x2dccbb76cdae8ae2d2b92d6160420e830158701a03610,0x4e1504c118a42087a2987c08,0x374aeac604ac0032bc01aca08,0x4b0f44a930470f64c94007,0x12c4a9304693c3f8fa4637e4c9440a,0x100488f44f12047b804c91808,0x4b91448144469404490e4c93009,0x12c4a930481424693e42104e0b844c9460c,0x4490e4610a4a0fe508f44f926493864c9460d,0xc0420f8381c06c248662405609,0xf0420e0701986a05,0xd8420f8701b094e30321706009,0xc0420f8341c06c2485ee2b8e23886220401b82c4db884e85613,0x29e8d29a8ca9604,0x9124e8f2629425805,0x2885d280859705f9626827c68a780a,0x28684a80841609f164d6b965b2780a,0xa1a125827c5927805,0x85a865f974a216805,0x5c2125a2109ea78e739aa0b986c176a297e0d,0xa3218a096c9ea105a27807,0x178861708597e04,0xa397c9ea145e27805,0xa321a9ea125c17ee9280e8ba0e7a780b]

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk2567_1 : checkRows book2567 10 444 rows2567_1=true := by decide +kernel

def rows2567_2 : List Nat := [0x5e39ca1ba6e7a1a05,0xa3214e7a8084160ea39a07,0xeab9aa32145827e05,0xa321a9ea125c17ee927e59baaeb2780b,0x5c97ee6a7e6d9b069396a2976eb966ea9ac0d,0x5e1765f974a2166ea96084a86ec21a0b,0x8fa4e90a6295a9ca5a98c7bb2c8392a831ca4276e524696a5213,0xa4de87402,0x4c1d048150441c8a206,0x12878118a21e8762087eee050ed89c258540d,0x301083e0d0701b09217b8ae3884228560c,0x8936087bb452a0e4e3884da08ef08e1006ea8a4c98238ee82a2009e1482ee423619,0x230401b82e4eb884dbbc07,0x4a1e0462887a1d8821fbb8143b6200520b09a280988dbb45220c82934e213aa8a4c982388802af021ed8222ef85424,0x5012878118a21e8762087ede8540a,0x8fa4e90a6295a5205,0x29ca629602,0x280861785dba404,0x168861608517e04,0x5917e5a278a027c05,0x9fa105827c5927805,0xe817ef43cea33ccf296607,0xa096c9ea105997ef43cef2a8af4b1ef2394f1a4696b20e4aa0c72909da7817,0x143b6f1080268520b0a026236f524c982a28e2205ba0a5221ed82224d284f0a0ce402a4dbb81d]

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk2567_2 : checkRows book2567 10 468 rows2567_2=true := by decide +kernel

def rows2567_3 : List Nat := [0xf524c982a28e16e82284f0a0e8da24ee8802785288b6087bbc0a88c1006e0b93a4e388f594a1d,0x23e93a4098a549c3949225c9d26a992520c,0xc5910c0b1257b0c573065611643b76cfb1aae3380f,0x10cc1904463dc408f4c1302c31560a,0x3d1183eb02c230405,0x30ace376cfb1aae302c19183e154f7be0f70fc0e,0x10cf7904f895a04,0x310ce376cfb1aae118f7102568f855b12c39060e,0xf710c57902570f856318c53e4ceb30b7862f9b3ccd2e2198701a056b4ae4f62d4cbb76cdae8cfb1aae11821,0xf710c57902570f856318c53e4ceb30de3e6cf334b685c1c068182d2b92dccbb760d8420ebd80c3e8cdae8cfb1aae11825,0x248973c602,0x24a93a428f26295a509ca6afb3da9914cfa95288a368925e12,0x92a4e90a3c98a5694272fb25e09,0x23e93a4098a549c3949225c9d3f09a2668da20d83ee1006eb982e4ea6e4e25218,0x8fa4e902629525205,0x9926af6a369b2244d388fcbf009,0x2248ea208e36004,0x1006eb982c4d9484d3884e15053bea0b,0xe53f49225c9d3f09ba60932389a2668da700d,0x13a0b9360b38804,0xc0320c43c8b82d0de338ee328ea2c0d60c,0x1c0a026092a4adb74acaa808,0xc4308f002,0x4042f8ee2d0e82b0c806]

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk2567_3 : checkRows book2567 10 492 rows2567_3=true := by decide +kernel

def rows2567_4 : List Nat := [0x2d0c9010bcbaaf82c2f5018ba342f033aec0d,0xca378d834aeabe0b0bd2ec08,0x368d8378d43b8ca3a0ad02c08bc0f00b,0xc6370be3c8da360c806,0x30c00350c0358df038ca2d0c809,0x2d8c82f0de348cc05,0xb6320be378d43ac11048c2360cc0a,0x2d8c8310be378da3b0d43ac102c4142e40d020cc0f,0x18c6799a81182759ba7f1fa7c9c40a,0x66a007e9ba7c98a611bc759c30619e0b,0xb2b74b2014b080e042ba07,0x8c02aeacadd2c5072c207,0xadb74ac81002808aaabf07aa409,0x1e0a026092bab2b74b12be08,0x2bf0700a04422082aeb0ab1080080a,0x1e276b7202,0x192639fe02,0x10a1d2801fa7cc1a05,0x184679970a18a759cf0a9c27f1fa7c9bc0c,0x6119e659d6739bc05,0x6119e669d674a010b9870a1fa7c9bf0b1bc0d,0x7e9ca71c307c9fe05,0xbf300cb328d229400accb43f8c9b22df29200004a434411,0x2fcc032aca348a5002b32d0c9322df29200004a4296a8bf90d34614]

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk2567_4 : checkRows book2567 10 516 rows2567_4=true := by decide +kernel

def rows2567_5 : List Nat := [0x32eddb36ba2b80c0421003a0d860b4ae6ffae4f62e0192d412,0x2dccbb76cdae8ae2d2b9ae4b605a108400e830158701bbfe1a3d90e03616,0x401bae6ff94afe95253bea08,0xaab330eb36ba2b8a92b6ab820aeacadd2c208abe0f,0xac3330eb36ba2b900c230fab2b12c20b,0x66996679947318a809ca71a0609,0x20466996759d4671c206,0x1928198a8119e04,0x6498f061be709d674c4711442609fa6ec327d43c7ca0211,0x1927098e67996631c4759cf124427e9ba60c327d1f23941638817099dd0f20218,0x19263a0202,0x7f186759c4631ba05,0x182679966fc2f139cf131fc08,0x729c71420203,0x1fe729c71098204,0x1926e9d67398f0b98a70c53151fe0a,0x1de7637202,0x81c56759cc651ba7f992639d209,0x4426e99e60c4404,0x1846799a759d28045d1698b15c54709bc0c,0x1be7f45c6f1846799b1344e74a0517c57151f67e1f03841639817161e087b6088c4b10424ccc3acdae8ae342d2340df1d626,0x2649abda8da6c9824c8ebf008,0x13852bf69824cfe13518a24d821f0f3880c,0x220fea1ed8223193fc06]

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk2567_5 : checkRows book2567 10 540 rows2567_5=true := by decide +kernel

def lastUnits2567 := digits 10 27 0x16a65dbb5a5725bc310841d06c306f1730dd988c21b541675fe3366d74570207fdec

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflict2567 : checkReasons book2567 564 24 lastUnits2567 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem exclude2567 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 2567=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=2) h hc bp eq (by decide +kernel)
  let v := truth Z a2567
  have hbase : ValidThrough v book2567 420 := book_start Z h hc z eq _ _ _ _ initialClauses2567
  have h0 : ValidThrough v book2567 444 := rows_sound hbase rows2567_0 rowsOk2567_0
  have h1 : ValidThrough v book2567 468 := rows_sound h0 rows2567_1 rowsOk2567_1
  have h2 : ValidThrough v book2567 492 := rows_sound h1 rows2567_2 rowsOk2567_2
  have h3 : ValidThrough v book2567 516 := rows_sound h2 rows2567_3 rowsOk2567_3
  have h4 : ValidThrough v book2567 540 := rows_sound h3 rows2567_4 rowsOk2567_4
  have h5 : ValidThrough v book2567 564 := rows_sound h4 rows2567_5 rowsOk2567_5
  exact book_end h5 _ _ conflict2567
end Compact

namespace Compact
open PEqualNP.Outside.L_meta_9774_aux.DagTools Resolution

def a8713 := ([0x3002,0x3802,0x5802,0x80061,0xc0061,2151,0x80081,0x20081,0xc0081,0x3083,2176,0x80881,0x20881,0xc0881,4224,0x81081,0x21081,0xc1081,0x3887,0x23887,0x43887,0x6888,0x806888,0x1006888,0xc2009,192,0xc00c1,0x800c1,0xa00c1,0x38c3,0x58c3,2240,0xc08c1,0x808c1,0xa08c1,4288,0xc10c1,0x810c1,6343,0x218c7,0x418c7,0x48c8,0x8048c8,0x10048c8,0xe00e1,0xc00e1,0x1800e1,2272,0xe08e1,0xc08e1,0x1808e1,4320,0xc10e1,0x1810e1,0x90e7,0x290e7,0x490e7,0x2618e8,0xa618e8,0x12618e8,0xc3809,256,0x100101,0x140101,0x160101,0x5903,2304,0x100901,0x140901,0x160901,4352,0x101101,0x141101,0x161101,0x8907,0x28907,0x48907,0x4c0108,0xcc0108,0x14c0108,0x164009,0x100121,0x160121,4391,0x5927,0x160161,0xc0161,0xe0161,2400,0x160961,0xc0961,0xe0961,4448,0x161161,0xc1161,0xe1161,2407,0x20967,0x40967,0xc5809,0x3805,0x3825,0x23825,0x43825,0xc3826,0xe3826,0x4005,0x84006,0xc4006,0x4025,0x24025,0x44025,0xc4026,0xe4026,0x5805,0x25805,0x45805,0x85806,0x5825,0x25825,0x45825,0x8005,0x28005,0x48005,0x8025,0x28025,0x48025,0x108026,0x168026,0x8805,0x28805,0x48805,0x8825,0x108826,0x168826,0x9005,0x29005,0x49005,0x89006,0xc9006,0x9025,0x29025,0x49025,0x169026,0x40e4,0x5904,0x9104,0x9164,0x8a04,0x9204,0x9224] : List Nat).toArray.map readFact

def r8713 := ([0x22069,0x23069,2149,128,2176,4224,0xe0889,0xe3089,0x23887,0x8e0889,0x8e3089,0x43887,0x10e0889,0x10e3089,0x3885,0x2688a,0xc688a,0x806888,0x2002688a,0x200c688a,0x1006888,0x4002688a,0x400c688a,0x6886,0xc200c,0x80308f,0x100308f,0x102308f,192,8386,193,2240,0x220c2,2241,4288,0x420c2,195,0x620c9,0x628c9,0x8620c9,0x8628c9,0x418c7,6341,0x848ca,0xa48ca,0x200848ca,0x200a48ca,0x10048c8,0x48c6,224,2272,227,0x2430e9,0x2460e9,0x290e7,0xa430e9,0xa460e9,0x490e7,0x12430e9,0x12460e9,0x90e5,0x98c18ea,0x99818ea,0xa618e8,0x298c18ea,0x299818ea,0x12618e8,0x498c18ea,0x499818ea,0x2618e6,0x30ee,0xc380c,0x8030ef,0x10030ef,0x10230ef,256,0x5902,2304,0x25902,4352,0x45902,0x225109,0x225909,0x28907,0xa25109,0xa25909,0x48907,0x1225109,0x1225909,0x8905,0x1314010a,0x1316010a,0xcc0108,0x3314010a,0x3316010a,0x14c0108,0x5314010a,0x5316010a,0x4c0106,0x16400c,0x80590f,0x100590f,0x102590f,0x44129,4389,0x165929,0x5925,352,2400,2401,4448,355,0x23169,0x23969,0x823169,0x823969,0x1023169,0x1023969,2405,0x316e,0xc580c,0x80316f,0x100316f,0x102316f,0x3810,0x3830,0x3003832,0x23803832,0x3023832,0x23823832,0x43831,0x4010,0x2004012,0x3004012,0x4030,0x23004032,0x3804032,0x23024032,0x3824032,0x44031,0x23044032,0x3844032,0x5810,0x22005812,0x22025812,0x22045812,0x5830,0x45831,0x8010,0x48011,0x8030,0x8031,0x24008032,0x5808032,0x28031,0x24028032,0x5828032,0x48031,0x24048032,0x5848032,0x8810,0x48811,0x8830,0x4008832,0x5808832,0x9010,0x2009012,0x23009012,0x2029012,0x23029012,0x49011,0x2049012,0x23049012,0x9030,0x25809032,0x25829032,0x49031,0x25849032,0x103814,0x3103833,0x23903833,0x2164013,0x164034,0x964034,0x3244013,0x244034,0xa44034,0x22245813,0x245834,0xa45834,0x228014,0xa28014,0x24228033,0x248014,0xa48014,0x5a48033,0x248814,0xa48814,0x5a48833] : List Nat).map readScheme

def table8713_0 : List Nat := [0x30282,0x40282,705,833,1473,1985,0x70902,0x80902,0xa8982,0xc0982,0xd0982,0xe8a02,0x100a02,0x110a02,0x29138943,0x78a82]

def table8713_1 : List Nat := [0x80a82,0xa8b02,0xc8b02,0xd0b02,0xe8b82,0x108b82,0x110b82,0x2f168ac3,3074,0xc436110a0485,0xc446110e0485,0xc4461b0e0485,3393,0x131b0c83,0x198f82,4161]

def table8713_2 : List Nat := [0x13210f83,0x1f9182,4673,0x13251183,0x9182,0x1b1302,0x1c1302,0x211382,0x221382,0x239402,0x51279343,0x1b1482,0x1c9482,0x211502,0x229502,0x239582]

def table8713_3 : List Nat := [0x572a94c3,5697,6209,0x19982,0x2d1b02,0x2e1b02,0x2f9b82,0x311b82,0x321b82,0x339c02,0x341c02,0x351c02,0x71379b43,0x2d1c82,0x2e9c82,0x2f9d02]

def table8713_4 : List Nat := [0x311d02,0x329d02,0x339d82,0x341d82,0x359d82,0x773a9cc3,0x3b000083,7682,0x1e4c65b2f0e85,0x1e4d25b330e85,0x1e4d263330e85,8001,0x83401e83,8641,0x83452103,9153]

def table8713_5 : List Nat := [0x83492303,0x3f2502,0x402502,0x42a582,0x442582,0x452582,0x46a602,0x482602,0x492602,0x994ba543,0x3fa682,0x402682,0x42a702,0x44a702,0x452702,0x46a782]

def table8713_6 : List Nat := [0x48a782,0x492782,0x9f4ea6c3,0x22802,0x2851681422085,0x2852681462085,0x285268b462085,0x512982,0x29c1,0x522a02,0x2a41,0x2ac1,0x2cc1,0x58ae02,0x2ec1,0x2ae02]

def table8713_7 : List Nat := [0x563002,0x573002,0x5a3082,0x5b3082,0x5e3102,0x5f3102,0xc561b043,0x3d000103,0x3182,0x31d6aad580f05,0x31d7aad5c0f05,0x31d7ab55c0f05,0x3241,0xcf66b2c3,0xd02db283,0xd32c3283]

def table8713_8 : List Nat := [0xd031b303,0xd3303303,0x33b382,0x3541,0xd603b503,0xd804b503,0xdf6eb6c3,0xe1563683,0xe257b683,0xe15a3703,0xe25bb703,0x5cb782,0xe15e3783,0xe25fb783,0xe973b943,0xeb063903]

def table8713_9 : List Nat := [0xeb0b3983,0xeb0f3a03,0xf177bb43,0x5cbc02,0xf77abcc3,0x23bd82,0xfd7dbe43,0x3dbe02,0xff3e3e03,0x10040be03,0x42be82,0xff433e83,0x10045be83,0x46bf02,0xff473f03,0x10049bf03]

def table8713_10 : List Nat := [0x10782c0c3,0x23c182,0x4241,0x10a51c203,0x10c52c203,0x11388c3c3,0x1141bc383,0x1171a4383,0x11421c403,0x117204403,0x23c482,0x11425c483,0x117244483,0x11d8dc643,0x11f554603,0x11f594683]

def table8713_11 : List Nat := [0x5cc702,0x11f5d4703,0x1216a3203,0xe068c803,0xe3694803,0xea6bc883,0x123763683,0x123773703,0x1166cc903,0x1258c3683,0x1258d3703,0x115754983,0x1278c3b03,0x1278d3b83,0x129813c83,0x129823d03]

def table8713_12 : List Nat := [0x10b7f4a03,0x12b873c83,0x12b883d03,0x11e80ca83,0x12d874083,0x12d884103,0x11e86cb03,0x47c1,0x45c1,0x3fc1,0x3ac1,0x3b9c03,0x67b4c2,0x638f170e270b006,0x5c3898e3c70b706,0xc16eac18e3c70af07]

def table8713_13 : List Nat := [0x31c78b8713845,0x17000389c84,0x5c1dc3,7554,0x6212118b04,0x8c62121486c5,0x6212118904,0x2431118a44,0x310908c3,0x31090a83,0x188482,0x1e31d93b684,0x4481,0x138a0f83,0x512b9083,0x9c502]

def table8713_14 : List Nat := [0x93ae42,0x5c0002,0x13aa1412504,0xa1803e83,0x954da283,0x200a1402784,0xa1802003,0x132a1412144,0x50c002,0x257077bc384,0x2e01]

def encoded8713 (i : Nat) : Nat :=
  if i < 112 then
    if i < 48 then
      if i < 16 then
        table8713_0.getD (i%16) 0
      else
        if i < 32 then
          table8713_1.getD (i%16) 0
        else
          table8713_2.getD (i%16) 0
    else
      if i < 80 then
        if i < 64 then
          table8713_3.getD (i%16) 0
        else
          table8713_4.getD (i%16) 0
      else
        if i < 96 then
          table8713_5.getD (i%16) 0
        else
          table8713_6.getD (i%16) 0
  else
    if i < 176 then
      if i < 144 then
        if i < 128 then
          table8713_7.getD (i%16) 0
        else
          table8713_8.getD (i%16) 0
      else
        if i < 160 then
          table8713_9.getD (i%16) 0
        else
          table8713_10.getD (i%16) 0
    else
      if i < 208 then
        if i < 192 then
          table8713_11.getD (i%16) 0
        else
          table8713_12.getD (i%16) 0
      else
        if i < 224 then
          table8713_13.getD (i%16) 0
        else
          table8713_14.getD (i%16) 0

def book8713 (i : Nat) : Clause := let n := encoded8713 i; unpackLits 9 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClauses8713 : inputsOK 1 8713 a8713 r8713 (baseBook book8713 199).toList=true := by decide +kernel

def rows8713_0 : List Nat := [0x162dd5ed95cd75a06,0x15845523f4e394a06,0x13c9f369b30972c06,0x1220b20091e071c06,0x80947a928e748c66728a09,0x10264fe62fa04,0x118f512f2e0db10e30c08,0xf712ece7159ae806,0xf2e4ece90d190e06,0x11b0d0ef4ece4f79f9cdb9aea0b,0x100fd67a0f0eedf699904668c908e6e6c786a7d6506f87afa17,0x100fd67a0f0eedf699904668c908e807f6506f8687870828ba396fa1a,0x76886e9468928e868c6684780b,0x163612240e3226221c08,0x1032200c1e2e2837a81c09,0x28340fa81e0c2e06,0x15abac1c03,0x34162e2a19afa82007,0x1420101c1bb00c1e3208,0x1a12240e3226222e2db1b21c0b,0x15b7371910a03256d6b95080005077a0e,0x15b757158450a03256f6b080005070d17b72761a5a7775647b430495595781d,0x3a3d4bb950414c06,0x4c544e605a5805]

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk8713_0 : checkRows book8713 8 199 rows8713_0=true := by decide +kernel

def rows8713_1 : List Nat := [0x50544a60574d4bb951bc525e43ba5c0e,0x15b7571910a03256f6b95080005070d17b727617813,0x1a5a601,0xc2a4bec4b4a2ca06,0xcab0acc4c0aeb2abc49d34bd38b60d,0xaeb2aac4bcc005,0xcdc8a4b6bf2f2d3ec3c6980a,0x98cdc8ad2d3eb0b2a8bac5cab6a5c72e0f,0xb8b2a7c403,0xbcb2aac9ceb0a13f3b2dc733cdc40d,0x17f8146ced1932983898d8f48d2d545400f,0x18146ced193418b8d48d2d54529854bb9d3878fd0c6df432a49c37c1a]

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk8713_1 : checkRows book8713 8 223 rows8713_1=true := by decide +kernel

def lastUnits8713 := digits 8 20 0x282a25302ba6a5dca8de292f2418dadfbbcae0ea

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflict8713 : checkReasons book8713 235 46 lastUnits8713 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem exclude8713 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 8713=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=1) h hc bp eq (by decide +kernel)
  let v := truth Z a8713
  have hbase : ValidThrough v book8713 199 := book_start Z h hc z eq _ _ _ _ initialClauses8713
  have h0 : ValidThrough v book8713 223 := rows_sound hbase rows8713_0 rowsOk8713_0
  have h1 : ValidThrough v book8713 235 := rows_sound h0 rows8713_1 rowsOk8713_1
  exact book_end h1 _ _ conflict8713
end Compact

open PEqualNP.Outside.L_meta_9774_aux.DagTools PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem candidate {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (len : D.length≤24) :
    ∃ m∈fourMasks++finalMasks, mask m=ineligSet 14 D := by
  rcases classified h hc len with four|⟨m,mem,eq⟩
  · obtain ⟨m,eq⟩ := repr (ineligSet 14 D)
    have bp := (no_empty_surplus h hc len).1
    have ok := possible_of h hc 11 m.val eq bp.le
    have good := all_four_tests m
    have mem : m.val∈fourMasks := by simpa [fourTest,ok,eq,four] using good
    exact ⟨m.val,List.mem_append_left _ mem,eq⟩
  · exact ⟨m,List.mem_append_right _ mem,eq⟩

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem smaller_closed {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (len : D.length≤24) : False := by
  obtain ⟨m,mem,eq⟩ := candidate h hc len
  have shift (i j : Nat) (a : Equiv.Perm V) (perm : auto a) (ei : mask i=ineligSet 14 D)
      (mv : (mask i).image a=mask j)
      (impossible : ∀ {E : Dag}, StrictLive 14 E → sem_Comp 14 adj E → Bzero 14 E=0 → Bplus 14 E=11 → mask j=ineligSet 14 E → False) : False := by
    obtain ⟨E,strict,comp,le,pat⟩ := move_case h hc len i j ei a perm mv
    obtain ⟨bp,bz,_⟩ := no_empty_surplus strict comp le
    exact impossible strict comp bz bp pat.symm
  simp only [fourMasks,finalMasks,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact shift 177 177 graphPerm0 auto0 eq (by decide +kernel) Compact.exclude177
  · exact shift 197 177 graphPerm1 auto1 eq (by decide +kernel) Compact.exclude177
  · exact shift 298 298 graphPerm0 auto0 eq (by decide +kernel) Compact.exclude298
  · exact shift 432 432 graphPerm0 auto0 eq (by decide +kernel) Compact.exclude432
  · exact shift 523 523 graphPerm0 auto0 eq (by decide +kernel) Compact.exclude523
  · exact shift 534 534 graphPerm0 auto0 eq (by decide +kernel) Compact.exclude534
  · exact shift 645 645 graphPerm0 auto0 eq (by decide +kernel) Compact.exclude645
  · exact shift 657 645 graphPerm1 auto1 eq (by decide +kernel) Compact.exclude645
  · exact shift 660 660 graphPerm0 auto0 eq (by decide +kernel) Compact.exclude660
  · exact shift 778 778 graphPerm0 auto0 eq (by decide +kernel) Compact.exclude778
  · exact shift 912 912 graphPerm0 auto0 eq (by decide +kernel) Compact.exclude912
  · exact shift 1098 298 graphPerm1 auto1 eq (by decide +kernel) Compact.exclude298
  · exact shift 1220 432 graphPerm1 auto1 eq (by decide +kernel) Compact.exclude432
  · exact shift 1290 1290 graphPerm0 auto0 eq (by decide +kernel) Compact.exclude1290
  · exact shift 1546 778 graphPerm1 auto1 eq (by decide +kernel) Compact.exclude778
  · exact shift 1668 912 graphPerm1 auto1 eq (by decide +kernel) Compact.exclude912
  · exact shift 2083 912 graphPerm3 auto3 eq (by decide +kernel) Compact.exclude912
  · exact shift 2338 432 graphPerm3 auto3 eq (by decide +kernel) Compact.exclude432
  · exact shift 2563 645 graphPerm2 auto2 eq (by decide +kernel) Compact.exclude645
  · exact shift 2818 177 graphPerm3 auto3 eq (by decide +kernel) Compact.exclude177
  · exact shift 4163 912 graphPerm2 auto2 eq (by decide +kernel) Compact.exclude912
  · exact shift 4611 645 graphPerm3 auto3 eq (by decide +kernel) Compact.exclude645
  · exact shift 5186 432 graphPerm2 auto2 eq (by decide +kernel) Compact.exclude432
  · exact shift 5634 177 graphPerm2 auto2 eq (by decide +kernel) Compact.exclude177
  · exact shift 6147 660 graphPerm2 auto2 eq (by decide +kernel) Compact.exclude660
  · exact shift 6273 534 graphPerm2 auto2 eq (by decide +kernel) Compact.exclude534
  · exact shift 8353 778 graphPerm3 auto3 eq (by decide +kernel) Compact.exclude778
  · exact shift 8385 778 graphPerm2 auto2 eq (by decide +kernel) Compact.exclude778
  · exact shift 8416 1290 graphPerm2 auto2 eq (by decide +kernel) Compact.exclude1290
  · exact shift 8608 298 graphPerm3 auto3 eq (by decide +kernel) Compact.exclude298
  · exact shift 8713 8713 graphPerm0 auto0 eq (by decide +kernel) Compact.exclude8713
  · exact shift 8833 523 graphPerm2 auto2 eq (by decide +kernel) Compact.exclude523
  · exact shift 9408 298 graphPerm2 auto2 eq (by decide +kernel) Compact.exclude298
  · exact shift 107 107 graphPerm0 auto0 eq (by decide +kernel) code107
  · exact shift 111 111 graphPerm0 auto0 eq (by decide +kernel) code111
  · exact shift 123 111 graphPerm1 auto1 eq (by decide +kernel) code111
  · exact shift 543 543 graphPerm0 auto0 eq (by decide +kernel) code543
  · exact shift 794 794 graphPerm0 auto0 eq (by decide +kernel) Compact.exclude794
  · exact shift 1550 794 graphPerm1 auto1 eq (by decide +kernel) Compact.exclude794
  · exact shift 1802 1802 graphPerm0 auto0 eq (by decide +kernel) Compact.exclude1802
  · exact shift 2567 2567 graphPerm0 auto0 eq (by decide +kernel) Compact.exclude2567
  · exact shift 2693 2567 graphPerm2 auto2 eq (by decide +kernel) Compact.exclude2567
  · exact shift 4627 2567 graphPerm1 auto1 eq (by decide +kernel) Compact.exclude2567
  · exact shift 4753 2567 graphPerm3 auto3 eq (by decide +kernel) Compact.exclude2567
  · exact shift 8297 8297 graphPerm0 auto0 eq (by decide +kernel) code8297
  · exact shift 8417 1802 graphPerm2 auto2 eq (by decide +kernel) Compact.exclude1802
  · exact shift 9992 8297 graphPerm2 auto2 eq (by decide +kernel) code8297
  · exact shift 10112 107 graphPerm2 auto2 eq (by decide +kernel) code107
  · exact shift 10401 794 graphPerm3 auto3 eq (by decide +kernel) Compact.exclude794
  · exact shift 12160 111 graphPerm2 auto2 eq (by decide +kernel) code111
  · exact shift 12481 794 graphPerm2 auto2 eq (by decide +kernel) Compact.exclude794
  · exact shift 14208 111 graphPerm3 auto3 eq (by decide +kernel) code111
  · exact shift 14977 543 graphPerm2 auto2 eq (by decide +kernel) code543
end PEqualNP.Outside.L_meta_9774_aux

theorem PEqualNP.Outside.L_meta_9774 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 24 ∧ (∀ x : Fin 14 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 14, (u.val, v.val) ∈ ([(0, 8), (0, 10), (1, 7), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true))) := by
  rintro ⟨C,mono,len,comp⟩
  obtain ⟨D,h,short,hc⟩ := PEqualNP.Outside.L_meta_9774_aux.normalized C mono comp
  exact PEqualNP.Outside.L_meta_9774_aux.smaller_closed h hc (short.trans len)
