import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore

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

end PEqualNP.Outside.L_meta_9775.UpstreamCore

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools

def edges : List (Nat × Nat) := [(0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]

def hit (x : Fin 14 → Bool) := ∃ u v : Fin 14, (u.val,v.val) ∈ edges ∧ x u = true ∧ x v = true

def computes (C : Circuit) := ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ hit x

theorem input_bit {n} (x : Fin n → Bool) (i : Fin n) : (List.ofFn x).getD i.val false = x i := by
  simp [List.getD_eq_getElem?_getD, i.isLt]

open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

abbrev V := Fin 14

def neigh (v : V) : Nat := [1280, 8832, 8448, 6272, 11264, 5632, 2816, 10, 69, 98, 49, 88, 40, 22].getD v.val 0

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

open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools

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
  let L : Finset (Finset V) := {mask 8832,mask 6272,mask 11264,mask 5632,mask 2816}
  let X : Finset (Finset V) := {mask 1280,mask 8448}
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
    · exact ⟨1,by decide +kernel,by decide +kernel⟩
    · exact ⟨3,by decide +kernel,by decide +kernel⟩
    · exact ⟨4,by decide +kernel,by decide +kernel⟩
    · exact ⟨5,by decide +kernel,by decide +kernel⟩
    · exact ⟨6,by decide +kernel,by decide +kernel⟩
    · exact ⟨0,by decide +kernel,by decide +kernel⟩
    · exact ⟨2,by decide +kernel,by decide +kernel⟩
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
  let L : Finset (Finset V) := {mask 69,mask 98,mask 49,mask 88,mask 22}
  let X : Finset (Finset V) := {mask 10,mask 40}
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
    · exact ⟨9,by decide +kernel,by decide +kernel⟩
    · exact ⟨10,by decide +kernel,by decide +kernel⟩
    · exact ⟨11,by decide +kernel,by decide +kernel⟩
    · exact ⟨13,by decide +kernel,by decide +kernel⟩
    · exact ⟨7,by decide +kernel,by decide +kernel⟩
    · exact ⟨12,by decide +kernel,by decide +kernel⟩
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

open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools

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



abbrev WeightSpec := Nat × Nat × Nat × Nat × Nat × Nat × Nat

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

end PEqualNP.Outside.L_meta_9775.UpstreamCore

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore

open DagTools PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def weightSpecs : List WeightSpec := [
(5,256,5,1,0,0x0,0x24480000000000000000000000000000),
(6,8192,6,1,0,0x0,0x6c0000000000000000000000000000000000000000000000),
(17,1024,17,1,0,0x0,0x92200000000000000000000000000000000000),
(18,8192,18,1,0,0x0,0x1830000000000000000000000000000000000000000000000),
(20,8192,20,1,0,0x0,0x1428000000000000000000000000000000000000000000000),
(24,2048,24,1,0,0x0,0x511800000000000000000000000000000000000000),
(33,1024,33,1,0,0x0,0x31800000000000000000000000000000000000),
(34,512,34,1,0,0x0,0x43540000000000000000000000000000000),
(48,1024,48,1,0,0x0,0x180700000000000000000000000000000000000),
(65,256,65,1,0,0x0,0x60c0000000000000000000000000000),
(66,512,66,1,0,0x0,0x6c00000000000000000000000000000000),
(68,256,68,1,0,0x0,0x22090000000000000000000000000000),
(72,2048,72,1,0,0x0,0x6c000000000000000000000000000000000000000),
(80,2048,80,1,0,0x0,0x142800000000000000000000000000000000000000),
(96,512,96,1,0,0x0,0x14280000000000000000000000000000000),
(640,2,640,1,0,0x0,0x81a4000),
(768,64,768,1,0,0x0,0x827000000000000000000000),
(1536,32,1536,1,0,0x0,0x415c00000000000000000),
(2176,8,2176,1,0,0x0,0x415c0000000000),
(2304,64,2304,1,0,0x0,0x21d000000000000000000000),
(2560,64,2560,1,0,0x0,0x13a000000000000000000000),
(3072,16,3072,1,0,0x0,0x206900000000000000),
(4224,8,4224,1,0,0x0,0x209c0000000000),
(4608,32,4608,1,0,0x0,0x113800000000000000000),
(5120,32,5120,1,0,0x0,0x87400000000000000000),
(6144,8,6144,1,0,0x0,0x3d40000000000),
(8320,2,8320,1,0,0x0,0x874000),
(8704,2,8704,1,0,0x0,0x3d4000),
(9216,16,9216,1,0,0x0,0x82700000000000000),
(10240,16,10240,1,0,0x0,0x44e00000000000000),
(7,8448,7,2,1,0xd802,0x6c0000000000000024480000000000000000000000000000),
(19,9216,19,2,1,0xda04,0x1830000000212800000000000000000000000000000000000),
(21,1280,21,2,1,0xa800,0x92200024480000000000000000000000000000),
(25,3072,25,2,1,0xba04,0x511892200000000000000000000000000000000000),
(26,10240,26,2,1,0xdb04,0x2294000838400000000000000000000000000000000000000),
(28,10240,28,2,1,0xdb04,0x2488000838400000000000000000000000000000000000000),
(35,1536,35,2,1,0xa905,0x31853100000000000000000000000000000000),
(37,1280,37,2,1,0xa800,0x31800024480000000000000000000000000000),
(38,8704,38,2,1,0xd901,0xc60000000000091200000000000000000000000000000000),
(50,1536,50,2,1,0xa905,0x1a8553100000000000000000000000000000000),
(52,9216,52,2,1,0xda04,0x1428000000220900000000000000000000000000000000000),
(56,3072,56,2,1,0xba04,0x511980700000000000000000000000000000000000),
(67,768,67,2,1,0x9806,0x6c060c0000000000000000000000000000),
(70,768,70,2,1,0x9806,0x6c22090000000000000000000000000000),
(73,2304,73,2,1,0xb806,0x6c00000001c060000000000000000000000000000),
(74,2560,74,2,1,0xb906,0x4a5400022940000000000000000000000000000000),
(76,2304,76,2,1,0xb806,0x6c000000028a10000000000000000000000000000),
(81,1280,81,2,1,0xa800,0x922000060c0000000000000000000000000000),
(82,2560,82,2,1,0xb906,0x183000022940000000000000000000000000000000),
(84,2304,84,2,1,0xb806,0x142800000028a10000000000000000000000000000),
(97,768,97,2,1,0x9806,0x142860c0000000000000000000000000000),
(100,768,100,2,1,0x9806,0x142a2090000000000000000000000000000),
(104,2560,104,2,1,0xb906,0x4a54000601c0000000000000000000000000000000),
(112,1536,112,2,1,0xa905,0x1a8514280000000000000000000000000000000),
(896,66,896,2,1,0x6109,0x8270000000000000081a4000),
(1664,34,1664,2,1,0x5109,0x415c000000000081a4000),
(1792,96,1792,2,1,0x6509,0x827415c00000000000000000),
(2432,72,2432,2,1,0x630b,0x21d0000000415c0000000000),
(2688,10,2688,2,1,0x3107,0x415c00081a4000),
(3200,24,3200,2,1,0x430b,0x2069415c0000000000),
(3328,80,3328,2,1,0x640b,0x21d000206900000000000000),
(3584,48,3584,2,1,0x540a,0x415e06900000000000000),
(4736,10,4736,2,1,0x3107,0x209c00081a4000),
(4864,96,4864,2,1,0x6509,0x827113800000000000000000),
(5248,40,5248,2,1,0x530c,0x874000209c0000000000),
(6400,72,6400,2,1,0x630b,0x21d000000003d40000000000),
(6656,40,6656,2,1,0x530c,0x113800003d40000000000),
(7168,24,7168,2,1,0x430b,0x206903d40000000000),
(8960,66,8960,2,1,0x6109,0x8270000000000000003d4000),
(9344,18,9344,2,1,0x410d,0x82700000000874000),
(9728,18,9728,2,1,0x410d,0x827000000003d4000),
(10368,10,10368,2,1,0x3107,0x415c0000874000),
(10496,80,10496,2,1,0x640b,0x21d000044e00000000000000),
(10752,18,10752,2,1,0x410d,0x44e000000003d4000),
(12416,10,12416,2,1,0x3107,0x209c0000874000),
(12800,34,12800,2,1,0x5109,0x1138000000000003d4000),
(13312,48,13312,2,1,0x540a,0x87482700000000000000),
(14336,24,14336,2,1,0x430b,0x44e03d40000000000),
(27,11264,27,3,2,0xdba44,0x7a10000d3029a000000000000000000000000000000000000),
(29,11264,29,3,2,0xdba44,0x7408000d3029a000000000000000000000000000000000000),
(58,11264,58,3,2,0xdba44,0x7a10000d303a8100000000000000000000000000000000000),
(60,11264,60,3,2,0xdba44,0x7408000d303a8100000000000000000000000000000000000),
(75,2816,75,3,2,0xb9866,0x4e40000a681e840000000000000000000000000000),
(78,2816,78,3,2,0xb9866,0x4e40000a683a810000000000000000000000000000),
(83,2816,83,3,2,0xb9866,0x9c20000a681e840000000000000000000000000000),
(85,11264,85,3,2,0xdba44,0x74080009c229a000000000000000000000000000000000000),
(86,2816,86,3,2,0xb9866,0x9c20000a683a810000000000000000000000000000),
(105,2816,105,3,2,0xb9866,0x4e400007409e840000000000000000000000000000),
(108,2816,108,3,2,0xb9866,0x4e40000740ba810000000000000000000000000000),
(113,2816,113,3,2,0xb9866,0x9c200007409e840000000000000000000000000000),
(114,11264,114,3,2,0xdba44,0x7a100009c23a8100000000000000000000000000000000000),
(116,2816,116,3,2,0xb9866,0x9c20000740ba810000000000000000000000000000),
(657,1026,657,2,0,0x0,0x92200000000000000000000000000009120000),
(660,8194,660,2,0,0x0,0x14280000000000000000000000000000000000000081a4000),
(792,2112,792,2,0,0x0,0x511800000000000000827000000000000000000000),
(1920,98,1920,3,2,0x65199,0x827415c000000000081a4000),
(2181,264,2181,2,0,0x0,0x24480000000000000044480000000000),
(2209,1032,2209,2,0,0x0,0x31800000000000000000000051180000000000),
(2338,576,2338,2,0,0x0,0x4354000000021d000000000000000000000),
(2565,320,2565,2,0,0x0,0x2448000013a000000000000000000000),
(3078,8208,3078,2,0,0x0,0x6c0000000000000000000000000000206900000000000000),
(3456,88,3456,3,2,0x643bb,0x21d0002069415c0000000000),
(3712,98,3712,3,2,0x65199,0x13a415c000000000081a4000),
(4229,264,4229,2,0,0x0,0x24480000000000000024880000000000),
(4289,264,4289,2,0,0x0,0x60c0000000000000024880000000000),
(4292,264,4292,2,0,0x0,0x22090000000000000024880000000000),
(4304,2056,4304,2,0,0x0,0x1428000000000000000000000000209c0000000000),
(4625,1056,4625,2,0,0x0,0x92200000000000000113800000000000000000),
(4628,8224,4628,2,0,0x0,0x2488000000000000000000000000912000000000000000000),
(4992,98,4992,3,2,0x65199,0x8271138000000000081a4000),
(5126,8224,5126,2,0,0x0,0x6c0000000000000000000000000882400000000000000000),
(5186,544,5186,2,0,0x0,0x6c00000000000087400000000000000000),
(5188,288,5188,2,0,0x0,0x28a100000000c6000000000000000000),
(6149,264,6149,2,0,0x0,0x24480000000000000006c00000000000),
(6150,8200,6150,2,0,0x0,0xc60000000000000000000000000000000083840000000000),
(6784,98,6784,3,2,0x65199,0x13a1138000000000081a4000),
(7424,88,7424,3,2,0x643bb,0x21d000206903d40000000000),
(7680,88,7680,3,2,0x643bb,0x13a000206903d40000000000),
(8353,1026,8353,2,0,0x0,0x111200000000000000000000000000001830000),
(8385,258,8385,2,0,0x0,0x1c060000000000000000000000c60000),
(8416,514,8416,2,0,0x0,0x14280000000000000000000000000874000),
(9288,2064,9288,2,0,0x0,0x6c000000000000000000000082700000000000000),
(9984,98,9984,3,2,0x65199,0x827415c000000000003d4000),
(10273,1040,10273,2,0,0x0,0x31800000000000000000044e00000000000000),
(10624,88,10624,3,2,0x643bb,0x21d000044e415c0000000000),
(10880,88,10880,3,2,0x643bb,0x13a000044e415c0000000000),
(11776,98,11776,3,2,0x65199,0x13a415c000000000003d4000),
(13056,98,13056,3,2,0x65199,0x8271138000000000003d4000),
(14592,88,14592,3,2,0x643bb,0x21d000044e03d40000000000),
(14848,98,14848,3,2,0x65199,0x13a1138000000000003d4000)]

def weights : List (Nat × Nat) := [(5,1),(6,1),(17,1),(18,1),(20,1),(24,1),(33,1),(34,1),(48,1),(65,1),(66,1),(68,1),(72,1),(80,1),(96,1),(640,1),(768,1),(1536,1),(2176,1),(2304,1),(2560,1),(3072,1),(4224,1),(4608,1),(5120,1),(6144,1),(8320,1),(8704,1),(9216,1),(10240,1),(7,2),(19,2),(21,2),(25,2),(26,2),(28,2),(35,2),(37,2),(38,2),(50,2),(52,2),(56,2),(67,2),(70,2),(73,2),(74,2),(76,2),(81,2),(82,2),(84,2),(97,2),(100,2),(104,2),(112,2),(896,2),(1664,2),(1792,2),(2432,2),(2688,2),(3200,2),(3328,2),(3584,2),(4736,2),(4864,2),(5248,2),(6400,2),(6656,2),(7168,2),(8960,2),(9344,2),(9728,2),(10368,2),(10496,2),(10752,2),(12416,2),(12800,2),(13312,2),(14336,2),(27,3),(29,3),(58,3),(60,3),(75,3),(78,3),(83,3),(85,3),(86,3),(105,3),(108,3),(113,3),(114,3),(116,3),(657,2),(660,2),(792,2),(1920,3),(2181,2),(2209,2),(2338,2),(2565,2),(3078,2),(3456,3),(3712,3),(4229,2),(4289,2),(4292,2),(4304,2),(4625,2),(4628,2),(4992,3),(5126,2),(5186,2),(5188,2),(6149,2),(6150,2),(6784,3),(7424,3),(7680,3),(8353,2),(8385,2),(8416,2),(9288,2),(9984,3),(10273,2),(10624,3),(10880,3),(11776,3),(13056,3),(14592,3),(14848,3)]
def clean (m : Nat) : Bool := edges.all (fun e => !(m.testBit e.1 && m.testBit e.2))

def possible (cap m : Nat) : Bool :=
  clean m && (let c := (mask m).card
              decide (14 ≤ c+cap) && weights.all (fun r =>
                (r.1 &&& m != r.1) || decide (14+r.2 ≤ c+cap)))

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

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
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

def tenMasks : List Nat := [127, 1290, 4757, 8488, 16256]

def elevenMasks : List Nat := [11, 44, 47, 55, 63, 95, 103, 111, 119, 123, 125, 126, 127, 164, 177, 181, 197, 229, 245, 266, 296, 298, 400, 416, 432, 521, 524, 525, 645, 661, 1034, 1036, 1038, 1156, 1216, 1220, 1282, 1288, 1290, 1408, 1548, 2051, 2084, 2087, 2212, 2213, 2693, 4099, 4118, 4119, 4165, 4167, 4183, 4241, 4244, 4245, 4293, 4305, 4308, 4309, 4354, 4368, 4370, 4496, 4613, 4629, 4741, 4753, 4756, 4757, 5190, 5316, 5378, 5636, 5764, 6147, 6151, 6273, 6276, 6277, 6661, 6789, 7174, 7300, 7812, 8064, 8201, 8232, 8233, 8417, 8456, 8480, 8488, 8608, 8713, 8833, 9480, 10401, 12160, 12289, 12352, 12353, 12481, 12544, 12929, 13504, 13696, 13952, 14208, 14465, 14977, 15232, 15488, 15744, 16000, 16128, 16256]

def classTest (m : Nat) : Bool :=
  !possible 9 m && (!possible 10 m || tenMasks.contains m) &&
    (!possible 11 m || elevenMasks.contains m)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem classChunk0 : ∀ j : Fin 1024, classTest (0+j.val)=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem classChunk1 : ∀ j : Fin 1024, classTest (1024+j.val)=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem classChunk2 : ∀ j : Fin 1024, classTest (2048+j.val)=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem classChunk3 : ∀ j : Fin 1024, classTest (3072+j.val)=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem classChunk4 : ∀ j : Fin 1024, classTest (4096+j.val)=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem classChunk5 : ∀ j : Fin 1024, classTest (5120+j.val)=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem classChunk6 : ∀ j : Fin 1024, classTest (6144+j.val)=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem classChunk7 : ∀ j : Fin 1024, classTest (7168+j.val)=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem classChunk8 : ∀ j : Fin 1024, classTest (8192+j.val)=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem classChunk9 : ∀ j : Fin 1024, classTest (9216+j.val)=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem classChunk10 : ∀ j : Fin 1024, classTest (10240+j.val)=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem classChunk11 : ∀ j : Fin 1024, classTest (11264+j.val)=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem classChunk12 : ∀ j : Fin 1024, classTest (12288+j.val)=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem classChunk13 : ∀ j : Fin 1024, classTest (13312+j.val)=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem classChunk14 : ∀ j : Fin 1024, classTest (14336+j.val)=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem classChunk15 : ∀ j : Fin 1024, classTest (15360+j.val)=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem all_classes (m : Fin 16384) : classTest m.val=true := by
  let j : Fin 1024 := ⟨m.val % 1024, Nat.mod_lt _ (by decide)⟩
  have hj : j.val=m.val % 1024 := rfl
  by_cases q0 : m.val/1024=0
  · have eq : m.val=0+j.val := by omega
    rw [eq]; exact classChunk0 j
  by_cases q1 : m.val/1024=1
  · have eq : m.val=1024+j.val := by omega
    rw [eq]; exact classChunk1 j
  by_cases q2 : m.val/1024=2
  · have eq : m.val=2048+j.val := by omega
    rw [eq]; exact classChunk2 j
  by_cases q3 : m.val/1024=3
  · have eq : m.val=3072+j.val := by omega
    rw [eq]; exact classChunk3 j
  by_cases q4 : m.val/1024=4
  · have eq : m.val=4096+j.val := by omega
    rw [eq]; exact classChunk4 j
  by_cases q5 : m.val/1024=5
  · have eq : m.val=5120+j.val := by omega
    rw [eq]; exact classChunk5 j
  by_cases q6 : m.val/1024=6
  · have eq : m.val=6144+j.val := by omega
    rw [eq]; exact classChunk6 j
  by_cases q7 : m.val/1024=7
  · have eq : m.val=7168+j.val := by omega
    rw [eq]; exact classChunk7 j
  by_cases q8 : m.val/1024=8
  · have eq : m.val=8192+j.val := by omega
    rw [eq]; exact classChunk8 j
  by_cases q9 : m.val/1024=9
  · have eq : m.val=9216+j.val := by omega
    rw [eq]; exact classChunk9 j
  by_cases q10 : m.val/1024=10
  · have eq : m.val=10240+j.val := by omega
    rw [eq]; exact classChunk10 j
  by_cases q11 : m.val/1024=11
  · have eq : m.val=11264+j.val := by omega
    rw [eq]; exact classChunk11 j
  by_cases q12 : m.val/1024=12
  · have eq : m.val=12288+j.val := by omega
    rw [eq]; exact classChunk12 j
  by_cases q13 : m.val/1024=13
  · have eq : m.val=13312+j.val := by omega
    rw [eq]; exact classChunk13 j
  by_cases q14 : m.val/1024=14
  · have eq : m.val=14336+j.val := by omega
    rw [eq]; exact classChunk14 j
  by_cases q15 : m.val/1024=15
  · have eq : m.val=15360+j.val := by omega
    rw [eq]; exact classChunk15 j
  omega

theorem surplus_ten {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) : 10 ≤ Bplus 14 D := by
  obtain ⟨m, enc⟩ := repr (ineligSet 14 D)
  have cls := all_classes m
  simp only [classTest, Bool.and_eq_true] at cls
  by_contra hn
  have yes := possible_of h hc 9 m.val enc (by omega)
  simpa only [yes, Bool.not_true, Bool.false_eq_true] using cls.1.1

theorem length_twenty_three {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) : 23 ≤ D.length := by
  have lo := surplus_ten h hc
  have total := surplus_identity h
  rw [totalSurplus_split] at total
  omega

theorem monotone_twenty_three (C : Circuit) (hm : Monotone2 C) (hc : computes C) : 23 ≤ C.size := by
  obtain ⟨D, hd, hsize, hcomp⟩ := normalized C hm hc
  exact (length_twenty_three hd hcomp).trans hsize

theorem small_classification {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (hs : D.length ≤ 24) :
    ∃ m ∈ elevenMasks, mask m = ineligSet 14 D ∧
      (Bplus 14 D ≤ 10 → m ∈ tenMasks) := by
  obtain ⟨m, enc⟩ := repr (ineligSet 14 D)
  have total := surplus_identity h
  rw [totalSurplus_split] at total
  have yes := possible_of h hc 11 m.val enc (by omega)
  have cls := all_classes m
  simp only [classTest, Bool.and_eq_true] at cls
  have eleven := cls.2
  simp only [yes, Bool.not_true, Bool.false_or, List.contains_iff_mem] at eleven
  refine ⟨m.val, eleven, enc, ?_⟩
  intro cap
  have ten := cls.1.2
  have yesTen := possible_of h hc 10 m.val enc cap
  simpa only [yesTen, Bool.not_true, Bool.false_or, List.contains_iff_mem] using ten

end PEqualNP.Outside.L_meta_9775.UpstreamCore

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore

open DagTools

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

def graphPerm0 : Equiv.Perm V where
  toFun := permFn0
  invFun := permFn0
  left_inv := by decide +kernel
  right_inv := by decide +kernel

set_option maxHeartbeats 0 in
theorem auto0 : auto graphPerm0 := by unfold auto; decide +kernel

def permFn1 (v : V) : V := ([2, 5, 0, 3, 4, 1, 6, 12, 8, 9, 13, 11, 7, 10] : List V)[v.val]!

def graphPerm1 : Equiv.Perm V where
  toFun := permFn1
  invFun := permFn1
  left_inv := by decide +kernel
  right_inv := by decide +kernel

set_option maxHeartbeats 0 in
theorem auto1 : auto graphPerm1 := by unfold auto; decide +kernel

def permFn2 (v : V) : V := ([7, 10, 12, 8, 9, 13, 11, 0, 3, 4, 1, 6, 2, 5] : List V)[v.val]!

def graphPerm2 : Equiv.Perm V where
  toFun := permFn2
  invFun := permFn2
  left_inv := by decide +kernel
  right_inv := by decide +kernel

set_option maxHeartbeats 0 in
theorem auto2 : auto graphPerm2 := by unfold auto; decide +kernel

def permFn3 (v : V) : V := ([12, 13, 7, 8, 9, 10, 11, 2, 3, 4, 5, 6, 0, 1] : List V)[v.val]!

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

end PEqualNP.Outside.L_meta_9775.UpstreamCore

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools

theorem relabel_support_surplus {n : Nat} (σ : Equiv.Perm (Fin n)) {D : Dag}
    (h : StrictLive n D) (b : Bool) :
    surplusOn (relabel σ D) ((inner n (relabel σ D)).filter
      (fun w => decide ((supp n (relabel σ D) w).Nonempty) = b)) =
    surplusOn D ((inner n D).filter (fun w => decide ((supp n D w).Nonempty) = b)) := by
  have hlen := List.length_pos_iff.mpr h.2.2
  have mem (w : Nat) :
      liftP σ w ∈ (inner n (relabel σ D)).filter
          (fun v => decide ((supp n (relabel σ D) v).Nonempty) = b) ↔
      w ∈ (inner n D).filter (fun v => decide ((supp n D v).Nonempty) = b) := by
    simp only [Finset.mem_filter, inner, Finset.mem_range, relabel_length,
      relabel_supp σ h.1, Finset.image_nonempty]
    rw [tr_liftP_lt_iff σ (by omega)]
  unfold surplusOn
  symm
  refine Finset.sum_bij (fun w _ => liftP σ w) ?_ ?_ ?_ ?_
  · intro w hw
    exact (mem w).mpr hw
  · intro a ha c hc eq
    exact (tr_liftP_inj σ).mp eq
  · intro w hw
    refine ⟨liftP σ⁻¹ w, ?_, tr_liftP_inv' σ w⟩
    apply (mem _).mp
    simpa only [tr_liftP_inv'] using hw
  · intro w hw
    rw [relabel_fanout]

theorem relabel_Bplus {n : Nat} (σ : Equiv.Perm (Fin n)) {D : Dag}
    (h : StrictLive n D) : Bplus n (relabel σ D) = Bplus n D := by
  simpa only [decide_eq_true_eq, Bplus] using relabel_support_surplus σ h true

theorem relabel_Bzero {n : Nat} (σ : Equiv.Perm (Fin n)) {D : Dag}
    (h : StrictLive n D) : Bzero n (relabel σ D) = Bzero n D := by
  simpa only [decide_eq_false_iff_not, Bzero] using relabel_support_surplus σ h false

end PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore

open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools

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

open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools

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

namespace Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools

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
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools Resolution

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
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools

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
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools
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
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools Resolution

def readClause (width n : Nat) : Clause := unpackLits width (n%8) (n>>>3)

def readStep (clauseWidth reasonWidth g u : Nat) : SmallLine :=
  (unpackLits clauseWidth (g%64) (g>>>6), (u>>>9) % (2^reasonWidth), digits reasonWidth (u%512) (u>>>(9+reasonWidth)))
end Compact

namespace Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools Resolution

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

end PEqualNP.Outside.L_meta_9775.UpstreamCore

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore
open DagTools
namespace Compact
open Resolution

theorem construct_layout_budget {k I : Nat} {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (bp : Bplus 14 D + (mask I).card = 14 + k) (eq : mask I=ineligSet 14 D) :
    Nonempty (Layout D k I) := by
  classical
  obtain ⟨b,hb⟩ := sem_exists_pureBranch graph_ok h.1 hc
  have el := inelig_card_add 14 D
  have diff := card_residual h.1 b hb
  rw [←eq] at el
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

def weakScheme : Scheme → Bool
  | .exactAt _ _ _ => false
  | _ => true

theorem scheme_sound_weak {D : Dag} {k I : Nat} (Z : Layout D k I) (h : StrictLive 14 D)
    (hc : sem_Comp 14 adj D) (eq : mask I=ineligSet 14 D)
    (q : Scheme) (no : weakScheme q = true) (en : enabled k I q=true) : EvalClause Z (expand k I q) := by
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
  | exactAt x i p => simp [weakScheme] at no
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

def localCheckWeak (k I : Nat) (a : Array Fact) (r : Scheme) (c : Clause) : Bool :=
  weakScheme r && localCheck k I a r c

def inputsOKWeak (k I : Nat) (a : Array Fact) : List Scheme → List Clause → Bool
  | [], [] => true
  | r::rs, c::cs => localCheckWeak k I a r c && inputsOKWeak k I a rs cs
  | _, _ => false

theorem localSound_weak {D : Dag} {k I : Nat} (Z : Layout D k I) (h : StrictLive 14 D)
    (hc : sem_Comp 14 adj D) (eq : mask I=ineligSet 14 D)
    (a : Array Fact) (r : Scheme) (c : Clause) (ok : localCheckWeak k I a r c=true) :
    Holds (truth Z a) c := by
  simp only [localCheckWeak, localCheck, Bool.and_eq_true] at ok
  obtain ⟨p,hm,hval⟩ := scheme_sound_weak Z h hc eq r ok.1 ok.2.1
  have mem := List.contains_iff_mem.mp (List.all_eq_true.mp ok.2.2 p hm)
  obtain ⟨l,hl,eqp⟩ := List.mem_map.mp mem
  subst p
  refine ⟨l,hl,?_⟩
  rcases l with ⟨i,b⟩
  cases b <;> simp [truth,Yes,atLit] at hval ⊢ <;> exact hval

theorem inputs_sound_weak {D : Dag} {k I : Nat} (Z : Layout D k I) (h : StrictLive 14 D)
    (hc : sem_Comp 14 adj D) (eq : mask I=ineligSet 14 D)
    (a : Array Fact) (R : List Scheme) (F : Array Clause)
    (ok : inputsOKWeak k I a R F.toList=true) : Valid (truth Z a) F := by
  have all (rs : List Scheme) (cs : List Clause) (good : inputsOKWeak k I a rs cs=true) : List.Forall (Holds (truth Z a)) cs := by
    induction rs generalizing cs with
    | nil => cases cs <;> simp_all [inputsOKWeak,List.Forall]
    | cons r rs ih =>
      cases cs with
      | nil => contradiction
      | cons c cs =>
        simp only [inputsOKWeak,Bool.and_eq_true] at good
        apply List.forall_iff_forall_mem.mpr
        intro item mem
        rcases List.mem_cons.mp mem with rfl|rest
        · exact localSound_weak Z h hc eq a r _ good.1
        · exact List.forall_iff_forall_mem.mp (ih cs good.2) item rest
  intro c cF
  exact List.forall_iff_forall_mem.mp (all R F.toList ok) c (Array.mem_toList_iff.mpr cF)

theorem book_start_weak {D k I} (Z : Layout D k I) (h : StrictLive 14 D)
    (hc : sem_Comp 14 adj D) (eq : mask I=ineligSet 14 D)
    (a : Array Fact) (R : List Scheme) (book : Nat → Clause) (n : Nat)
    (ok : inputsOKWeak k I a R (baseBook book n).toList=true) : ValidThrough (truth Z a) book n := by
  have sat := inputs_sound_weak Z h hc eq a R (baseBook book n) ok
  intro j hj
  apply sat
  exact Array.mem_ofFn.mpr ⟨⟨j,hj⟩,rfl⟩


end Compact
end PEqualNP.Outside.L_meta_9775.UpstreamCore

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore
open DagTools
namespace Compact
open Resolution

theorem Layout.exact_from_chain {D : Dag} {k I : Nat} (Z : Layout D k I)
    (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (x i : V) (P : Nat)
    (xp : x ∈ mask P) (ix : adj i x)
    (wit : ∃ q s, q < D.length ∧ tag D q = true ∧
      sem_Chain 14 D i.val (src D (q, !s)) ∧
      ∀ a ∈ mask P, a ∈ supp 14 D (src D (q, s)) ↔ adj i a) :
    ∃ j < cap k I x, Z.see x i P j := by
  obtain ⟨q, s, hq, ht, chain, ex⟩ := wit
  have mem : (q, s) ∈ sem_W 14 D x := by
    refine sem_mem_W.mpr ⟨hq, (ex _ xp).2 ix, ?_⟩
    intro hx
    have pure := sem_dom_pure graph_ok h.1 hc i _ (sem_chain_dom h.1 chain)
    have eq := Finset.mem_singleton.mp (pure (sem_supp_and_sub h.1 hq ht (!s) hx))
    exact graph_ok.2.1 i (eq ▸ ix)
  obtain ⟨j, live, same⟩ := Z.covers x (q, s) mem
  exact ⟨j, lt_of_lt_of_le live (Z.limit x), live,
    fun c cp => by simpa [Layout.lab, SLabel, same] using ex c cp⟩

theorem Layout.paired_exact {D : Dag} {k I : Nat} (Z : Layout D k I)
    (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D ≤ 1)
    (eq : mask I = ineligSet 14 D) (x i y j : V) (P : Nat)
    (geom : independent (mask P) ∧ i ∈ mask I ∧ j ∈ mask I ∧
      x ∈ mask P ∧ y ∈ mask P ∧ adj i x ∧ adj j y ∧
      ∃ a ∈ mask P, adj j a ∧ ¬adj i a) :
    (∃ r < cap k I x, Z.see x i P r) ∨
      ∃ r < cap k I y, Z.see y j P r := by
  obtain ⟨ind, hi, hj, xp, yp, ix, jy, diff⟩ := geom
  rcases sem_shared_empty graph_ok h hc z (mask P) ind (eq ▸ hi) (eq ▸ hj) diff with wi | wj
  · exact Or.inl (Z.exact_from_chain h hc x i P xp ix wi)
  · exact Or.inr (Z.exact_from_chain h hc y j P yp jy wj)

inductive BudgetScheme where
  | plain (q : Scheme)
  | pairedExact (x i y j : V) (p : Nat)

def enabledBudget (k I : Nat) : BudgetScheme → Bool
  | .plain q => weakScheme q && enabled k I q
  | .pairedExact x i y j p => decide (independent (mask p) ∧
      i ∈ mask I ∧ j ∈ mask I ∧ x ∈ mask p ∧ y ∈ mask p ∧
      adj i x ∧ adj j y ∧ ∃ a ∈ mask p, adj j a ∧ ¬adj i a)

def expandBudget (k I : Nat) : BudgetScheme → FactClause
  | .plain q => expand k I q
  | .pairedExact x i y j p =>
      anyRange (cap k I x) (fun r => .see x i p r) ++
      anyRange (cap k I y) (fun r => .see y j p r)

theorem scheme_sound_budget {D : Dag} {k I : Nat} (Z : Layout D k I)
    (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D ≤ 1)
    (eq : mask I = ineligSet 14 D) (q : BudgetScheme)
    (en : enabledBudget k I q = true) : EvalClause Z (expandBudget k I q) := by
  cases q with
  | plain q =>
    simp only [enabledBudget, Bool.and_eq_true] at en
    exact scheme_sound_weak Z h hc eq q en.1 en.2
  | pairedExact x i y j p =>
    have geo := of_decide_eq_true en
    have hh := Z.paired_exact h hc z eq x i y j p geo
    rcases hh with hx | hy
    · obtain ⟨f, hf, yes⟩ := (range_iff Z (cap k I x) (fun r => Fact.see x i p r)).mpr hx
      exact ⟨f, List.mem_append_left _ hf, yes⟩
    · obtain ⟨f, hf, yes⟩ := (range_iff Z (cap k I y) (fun r => Fact.see y j p r)).mpr hy
      exact ⟨f, List.mem_append_right _ hf, yes⟩

def localCheckBudget (k I : Nat) (a : Array Fact) (r : BudgetScheme) (c : Clause) : Bool :=
  enabledBudget k I r && (expandBudget k I r).all (fun p => (c.map (atLit a)).contains p)

def inputsOKBudget (k I : Nat) (a : Array Fact) : List BudgetScheme → List Clause → Bool
  | [], [] => true
  | r::rs, c::cs => localCheckBudget k I a r c && inputsOKBudget k I a rs cs
  | _, _ => false

theorem localSound_budget {D : Dag} {k I : Nat} (Z : Layout D k I)
    (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D ≤ 1)
    (eq : mask I = ineligSet 14 D) (a : Array Fact) (r : BudgetScheme)
    (c : Clause) (ok : localCheckBudget k I a r c = true) : Holds (truth Z a) c := by
  simp only [localCheckBudget, Bool.and_eq_true] at ok
  obtain ⟨p, hm, hval⟩ := scheme_sound_budget Z h hc z eq r ok.1
  have mem := List.contains_iff_mem.mp (List.all_eq_true.mp ok.2 p hm)
  obtain ⟨l, hl, eqp⟩ := List.mem_map.mp mem
  subst p
  refine ⟨l, hl, ?_⟩
  rcases l with ⟨i, b⟩
  cases b <;> simp [truth, Yes, atLit] at hval ⊢ <;> exact hval

theorem inputs_sound_budget {D : Dag} {k I : Nat} (Z : Layout D k I)
    (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D ≤ 1)
    (eq : mask I = ineligSet 14 D) (a : Array Fact) (R : List BudgetScheme)
    (F : Array Clause) (ok : inputsOKBudget k I a R F.toList = true) : Valid (truth Z a) F := by
  have all (rs : List BudgetScheme) (cs : List Clause)
      (good : inputsOKBudget k I a rs cs = true) : List.Forall (Holds (truth Z a)) cs := by
    induction rs generalizing cs with
    | nil => cases cs <;> simp_all [inputsOKBudget, List.Forall]
    | cons r rs ih =>
      cases cs with
      | nil => contradiction
      | cons c cs =>
        simp only [inputsOKBudget, Bool.and_eq_true] at good
        apply List.forall_iff_forall_mem.mpr
        intro item mem
        rcases List.mem_cons.mp mem with rfl | rest
        · exact localSound_budget Z h hc z eq a r _ good.1
        · exact List.forall_iff_forall_mem.mp (ih cs good.2) item rest
  intro c cF
  exact List.forall_iff_forall_mem.mp (all R F.toList ok) c (Array.mem_toList_iff.mpr cF)

theorem book_start_budget {D k I} (Z : Layout D k I) (h : StrictLive 14 D)
    (hc : sem_Comp 14 adj D) (z : Bzero 14 D ≤ 1) (eq : mask I = ineligSet 14 D)
    (a : Array Fact) (R : List BudgetScheme) (book : Nat → Clause) (n : Nat)
    (ok : inputsOKBudget k I a R (baseBook book n).toList = true) :
    ValidThrough (truth Z a) book n := by
  have sat := inputs_sound_budget Z h hc z eq a R (baseBook book n) ok
  intro j hj
  apply sat
  exact Array.mem_ofFn.mpr ⟨⟨j, hj⟩, rfl⟩

end Compact
end PEqualNP.Outside.L_meta_9775.UpstreamCore

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact

def packedMasks : List Nat := [127,245,314,432,541,792,1102,1290,1548,2087,2213,2338,4183,4309,4370,4757,5008,5190,5316,6151,6789,7174,7426,7812,8297,8417,8488,8713,9288,9992,10401,10656,12481,13504,14977,16256]

def field (n i : Nat) := (n >>> (5+6*i)) &&& 63

def readPackedFact (n : Nat) : Fact :=
  match n%32 with
  | 0 => .live (Fin.ofNat 14 (field n 0)) (field n 1)
  | 1 => .lab (Fin.ofNat 14 (field n 0)) (field n 1) (Fin.ofNat 14 (field n 2))
  | 2 => .res (field n 0) (Fin.ofNat 14 (field n 1))
  | 3 => .common (Fin.ofNat 14 (field n 0)) (Fin.ofNat 14 (field n 1))
  | 4 => .gate (Fin.ofNat 19 (field n 0)) (Fin.ofNat 19 (field n 1))
  | 5 => .reader (field n 0==1) (Fin.ofNat 19 (field n 1)) (field n 2)
  | 6 => .es (field n 0==1) (Fin.ofNat 19 (field n 1)) (Fin.ofNat 14 (field n 2))
  | 7 => .avoid (Fin.ofNat 14 (field n 0)) (packedMasks.getD (field n 1) 0) (field n 2)
  | 8 => .see (Fin.ofNat 14 (field n 0)) (Fin.ofNat 14 (field n 1)) (packedMasks.getD (field n 2) 0) (field n 3)
  | 9 => .diff (field n 0) (Fin.ofNat 14 (field n 1)) (Fin.ofNat 14 (field n 2))
  | _ => default

def readPackedScheme (n : Nat) : Scheme :=
  match n%32 with
  | 0 => .self (Fin.ofNat 14 (field n 0)) (field n 1)
  | 1 => .earlier (Fin.ofNat 14 (field n 0)) (field n 1)
  | 2 => .labCommon (Fin.ofNat 14 (field n 0)) (Fin.ofNat 14 (field n 1)) (field n 2)
  | 3 => .someRes (Fin.ofNat 14 (field n 0))
  | 4 => .allRes (Fin.ofNat 14 (field n 0)) (field n 1)
  | 5 => .exposure (Fin.ofNat 14 (field n 0)) (packedMasks.getD (field n 1) 0)
  | 6 => .exactAt (Fin.ofNat 14 (field n 0)) (Fin.ofNat 14 (field n 1)) (packedMasks.getD (field n 2) 0)
  | 7 => .avoidLive (Fin.ofNat 14 (field n 0)) (packedMasks.getD (field n 1) 0) (field n 2)
  | 8 => .seeLive (Fin.ofNat 14 (field n 0)) (Fin.ofNat 14 (field n 1)) (packedMasks.getD (field n 2) 0) (field n 3)
  | 9 => .avoidNot (Fin.ofNat 14 (field n 0)) (Fin.ofNat 14 (field n 1)) (packedMasks.getD (field n 2) 0) (field n 3)
  | 10 => .seeLab (Fin.ofNat 14 (field n 0)) (Fin.ofNat 14 (field n 1)) (Fin.ofNat 14 (field n 2)) (packedMasks.getD (field n 3) 0) (field n 4)
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

def readPackedBudget (n : Nat) : BudgetScheme :=
  if n%32=21 then
    .pairedExact (Fin.ofNat 14 (field n 0)) (Fin.ofNat 14 (field n 1))
      (Fin.ofNat 14 (field n 2)) (Fin.ofNat 14 (field n 3)) (packedMasks.getD (field n 4) 0)
  else .plain (readPackedScheme n)

end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore
open DagTools
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
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection55 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (z : Bzero 14 D=0) (eq : mask 55=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 9472) (mask 55) (mask 0) (mask 21) (mask 55) (mask 256)
    (fun f : V => mask (([0, 0, 0, 0, 0, 0, 0, 0, 9288, 0, 0, 0, 0, 0] : List Nat).getD f.val 0)) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 55).card+(mask 256).card+2*(mask 0).card+(mask 21).card+(14-(mask 55).card)=18 := by decide +kernel
  have rhs : (mask 9472).card+(mask 9472 \ mask 55).card=6 := by decide +kernel
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection95 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (z : Bzero 14 D=0) (eq : mask 95=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 11008) (mask 95) (mask 64) (mask 22) (mask 95) (mask 512)
    (fun f : V => mask (([0, 0, 0, 0, 0, 0, 0, 0, 0, 10656, 0, 0, 0, 0] : List Nat).getD f.val 0)) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 95).card+(mask 512).card+2*(mask 64).card+(mask 22).card+(14-(mask 95).card)=20 := by decide +kernel
  have rhs : (mask 11008).card+(mask 11008 \ mask 95).card=8 := by decide +kernel
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection103 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (z : Bzero 14 D=0) (eq : mask 103=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 1792) (mask 103) (mask 0) (mask 97) (mask 103) (mask 1024)
    (fun f : V => mask (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 792, 0, 0, 0] : List Nat).getD f.val 0)) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 103).card+(mask 1024).card+2*(mask 0).card+(mask 97).card+(14-(mask 103).card)=18 := by decide +kernel
  have rhs : (mask 1792).card+(mask 1792 \ mask 103).card=6 := by decide +kernel
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection119 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (z : Bzero 14 D=0) (eq : mask 119=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 12032) (mask 119) (mask 80) (mask 39) (mask 119) (mask 2048)
    (fun f : V => mask (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9992, 0, 0] : List Nat).getD f.val 0)) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 119).card+(mask 2048).card+2*(mask 80).card+(mask 39).card+(14-(mask 119).card)=23 := by decide +kernel
  have rhs : (mask 12032).card+(mask 12032 \ mask 119).card=10 := by decide +kernel
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection123 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (z : Bzero 14 D=0) (eq : mask 123=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 3840) (mask 123) (mask 64) (mask 49) (mask 123) (mask 256)
    (fun f : V => mask (([0, 0, 0, 0, 0, 0, 0, 0, 7812, 0, 0, 0, 0, 0] : List Nat).getD f.val 0)) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 123).card+(mask 256).card+2*(mask 64).card+(mask 49).card+(14-(mask 123).card)=20 := by decide +kernel
  have rhs : (mask 3840).card+(mask 3840 \ mask 123).card=8 := by decide +kernel
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection181 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (z : Bzero 14 D=0) (eq : mask 181=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 9472) (mask 181) (mask 0) (mask 21) (mask 53) (mask 8448)
    (fun f : V => mask (([0, 0, 0, 0, 0, 0, 0, 0, 9288, 0, 0, 0, 0, 1290] : List Nat).getD f.val 0)) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 53).card+(mask 8448).card+2*(mask 0).card+(mask 21).card+(14-(mask 181).card)=18 := by decide +kernel
  have rhs : (mask 9472).card+(mask 9472 \ mask 181).card=6 := by decide +kernel
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection229 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (z : Bzero 14 D=0) (eq : mask 229=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 1792) (mask 229) (mask 0) (mask 97) (mask 101) (mask 1536)
    (fun f : V => mask (([0, 0, 0, 0, 0, 0, 0, 0, 0, 1290, 792, 0, 0, 0] : List Nat).getD f.val 0)) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 101).card+(mask 1536).card+2*(mask 0).card+(mask 97).card+(14-(mask 229).card)=18 := by decide +kernel
  have rhs : (mask 1792).card+(mask 1792 \ mask 229).card=6 := by decide +kernel
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection245 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (z : Bzero 14 D=0) (eq : mask 245=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 3840) (mask 245) (mask 64) (mask 49) (mask 117) (mask 2560)
    (fun f : V => mask (([0, 0, 0, 0, 0, 0, 0, 0, 0, 7426, 0, 9992, 0, 0] : List Nat).getD f.val 0)) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 117).card+(mask 2560).card+2*(mask 64).card+(mask 49).card+(14-(mask 245).card)=20 := by decide +kernel
  have rhs : (mask 3840).card+(mask 3840 \ mask 245).card=8 := by decide +kernel
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection661 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (z : Bzero 14 D=0) (eq : mask 661=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 9472) (mask 661) (mask 0) (mask 21) (mask 21) (mask 9472)
    (fun f : V => mask (([0, 0, 0, 0, 0, 0, 0, 0, 9288, 0, 8488, 0, 0, 1290] : List Nat).getD f.val 0)) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 21).card+(mask 9472).card+2*(mask 0).card+(mask 21).card+(14-(mask 661).card)=18 := by decide +kernel
  have rhs : (mask 9472).card+(mask 9472 \ mask 661).card=6 := by decide +kernel
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection2693 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (z : Bzero 14 D=0) (eq : mask 2693=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 74) (mask 2693) (mask 0) (mask 2688) (mask 2688) (mask 74)
    (fun f : V => mask (([0, 8297, 0, 4183, 0, 0, 314, 0, 0, 0, 0, 0, 0, 0] : List Nat).getD f.val 0)) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 2688).card+(mask 74).card+2*(mask 0).card+(mask 2688).card+(14-(mask 2693).card)=18 := by decide +kernel
  have rhs : (mask 74).card+(mask 74 \ mask 2693).card=6 := by decide +kernel
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection4245 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (z : Bzero 14 D=0) (eq : mask 4245=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 9472) (mask 4245) (mask 0) (mask 21) (mask 21) (mask 9472)
    (fun f : V => mask (([0, 0, 0, 0, 0, 0, 0, 0, 9288, 0, 8488, 0, 0, 1290] : List Nat).getD f.val 0)) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 21).card+(mask 9472).card+2*(mask 0).card+(mask 21).card+(14-(mask 4245).card)=18 := by decide +kernel
  have rhs : (mask 9472).card+(mask 9472 \ mask 4245).card=6 := by decide +kernel
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection4309 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (z : Bzero 14 D=0) (eq : mask 4309=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 11520) (mask 4309) (mask 16) (mask 69) (mask 85) (mask 11264)
    (fun f : V => mask (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10656, 9992, 0, 7426] : List Nat).getD f.val 0)) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 85).card+(mask 11264).card+2*(mask 16).card+(mask 69).card+(14-(mask 4309).card)=20 := by decide +kernel
  have rhs : (mask 11520).card+(mask 11520 \ mask 4309).card=8 := by decide +kernel
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection5190 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (z : Bzero 14 D=0) (eq : mask 5190=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 8960) (mask 5190) (mask 0) (mask 70) (mask 70) (mask 8960)
    (fun f : V => mask (([0, 0, 0, 0, 0, 0, 0, 0, 8713, 8488, 0, 0, 0, 792] : List Nat).getD f.val 0)) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 70).card+(mask 8960).card+2*(mask 0).card+(mask 70).card+(14-(mask 5190).card)=18 := by decide +kernel
  have rhs : (mask 8960).card+(mask 8960 \ mask 5190).card=6 := by decide +kernel
  omega


end PEqualNP.Outside.L_meta_9775.UpstreamCore

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore
open DagTools

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projected_exclude63 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (z : Bzero 14 D=0) (eq : mask 63=ineligSet 14 D) : 12≤Bplus 14 D := by
  classical
  have sub : wide (mask 16000) ⊆ mask 63 := by decide +kernel
  have marked : marks D (mask 16000) = wide (mask 16000) := by
    apply Finset.Subset.antisymm (Finset.filter_subset _ _)
    intro i hi
    apply mark_iff.mpr
    exact ⟨by simpa [wide] using hi,
      occurs h hc z (mask 16000) (by decide +kernel) i (eq ▸ sub hi)⟩
  have bound := projected_count h hc (mask 16000) (by decide +kernel) (by decide +kernel)
  rw [marked, ←eq] at bound
  have size := inelig_card_add 14 D
  rw [←eq] at size
  have card : (mask 63).card=6 ∧ (mask 16000).card=6 ∧
      (wide (mask 16000)).card=4 ∧ (mask 63 ∩ wide (mask 16000)).card=4 ∧
      (labels (mask 16000) (wide (mask 16000))).card=4 := by decide +kernel
  have inter := Finset.card_le_card (Finset.inter_subset_left :
    mask 16000 ∩ eligSet 14 D ⊆ mask 16000)
  omega

end PEqualNP.Outside.L_meta_9775.UpstreamCore

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore
open DagTools

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 8192 in
theorem residual_exclude111 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 111=ineligSet 14 D) : False := by
  classical
  obtain ⟨b,hb⟩ := sem_exists_pureBranch graph_ok h.1 hc
  have card := card_residual h.1 b hb
  have el := inelig_card_add 14 D
  rw [←eq] at el
  have count : (mask 111).card=6 := by decide +kernel
  have res : Fintype.card ↥(residualUnits 14 D b)=3 := by rw [Fintype.card_coe]; omega
  let f := (Fintype.equivFinOfCardEq res).symm
  have miss0 := two_exact h hc z (mask 6789) (by decide +kernel) 1 5 9 11 7 (eq ▸ (by decide +kernel : (1:V)∈mask 111)) (eq ▸ (by decide +kernel : (5:V)∈mask 111)) (by decide +kernel)
  have h0 := code_diff h hc b hb f 9 11 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (9:V)∉mask 111) hin : (9:V)∈eligSet 14 D) miss0 (share h hc (i:=6) (x:=9) (y:=11) (eq ▸ (by decide +kernel : (6:V)∈mask 111)) (by decide +kernel) (by decide +kernel))
  have miss1 := two_exact h hc z (mask 9992) (by decide +kernel) 5 6 9 13 10 (eq ▸ (by decide +kernel : (5:V)∈mask 111)) (eq ▸ (by decide +kernel : (6:V)∈mask 111)) (by decide +kernel)
  have h1 := code_diff h hc b hb f 9 13 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (9:V)∉mask 111) hin : (9:V)∈eligSet 14 D) miss1 (share h hc (i:=1) (x:=9) (y:=13) (eq ▸ (by decide +kernel : (1:V)∈mask 111)) (by decide +kernel) (by decide +kernel))
  have miss2 := exposed_exact h hc z (mask 9992) (mask 792) (by decide +kernel) (by decide +kernel) 0 10 9 (eq ▸ (by decide +kernel : (0:V)∈mask 111)) (by decide +kernel)
  have h2 := code_diff h hc b hb f 10 9 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (10:V)∉mask 111) hin : (10:V)∈eligSet 14 D) miss2 (share h hc (i:=5) (x:=10) (y:=9) (eq ▸ (by decide +kernel : (5:V)∈mask 111)) (by decide +kernel) (by decide +kernel))
  have miss3 := two_exact h hc z (mask 9992) (by decide +kernel) 0 5 10 13 8 (eq ▸ (by decide +kernel : (0:V)∈mask 111)) (eq ▸ (by decide +kernel : (5:V)∈mask 111)) (by decide +kernel)
  have h3 := code_excludes h hc b hb f 10 13 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (10:V)∉mask 111) hin : (10:V)∈eligSet 14 D) miss3
  have miss4 := exposed_exact h hc z (mask 6789) (mask 4757) (by decide +kernel) (by decide +kernel) 3 11 9 (eq ▸ (by decide +kernel : (3:V)∈mask 111)) (by decide +kernel)
  have h4 := code_diff h hc b hb f 11 9 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (11:V)∉mask 111) hin : (11:V)∈eligSet 14 D) miss4 (share h hc (i:=6) (x:=11) (y:=9) (eq ▸ (by decide +kernel : (6:V)∈mask 111)) (by decide +kernel) (by decide +kernel))
  have miss5 := two_exact h hc z (mask 7174) (by decide +kernel) 3 6 11 10 12 (eq ▸ (by decide +kernel : (3:V)∈mask 111)) (eq ▸ (by decide +kernel : (6:V)∈mask 111)) (by decide +kernel)
  have h5 := code_excludes h hc b hb f 11 10 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (11:V)∉mask 111) hin : (11:V)∈eligSet 14 D) miss5
  have miss6 := two_exact h hc z (mask 10401) (by decide +kernel) 3 6 11 13 7 (eq ▸ (by decide +kernel : (3:V)∈mask 111)) (eq ▸ (by decide +kernel : (6:V)∈mask 111)) (by decide +kernel)
  have h6 := code_excludes h hc b hb f 11 13 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (11:V)∉mask 111) hin : (11:V)∈eligSet 14 D) miss6
  have miss7 := exposed_exact h hc z (mask 9992) (mask 792) (by decide +kernel) (by decide +kernel) 2 13 9 (eq ▸ (by decide +kernel : (2:V)∈mask 111)) (by decide +kernel)
  have h7 := code_diff h hc b hb f 13 9 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (13:V)∉mask 111) hin : (13:V)∈eligSet 14 D) miss7 (share h hc (i:=1) (x:=13) (y:=9) (eq ▸ (by decide +kernel : (1:V)∈mask 111)) (by decide +kernel) (by decide +kernel))
  have miss8 := two_exact h hc z (mask 9992) (by decide +kernel) 1 2 13 10 9 (eq ▸ (by decide +kernel : (1:V)∈mask 111)) (eq ▸ (by decide +kernel : (2:V)∈mask 111)) (by decide +kernel)
  have h8 := code_excludes h hc b hb f 13 10 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (13:V)∉mask 111) hin : (13:V)∈eligSet 14 D) miss8
  have miss9 := two_exact h hc z (mask 10401) (by decide +kernel) 1 2 13 11 7 (eq ▸ (by decide +kernel : (1:V)∈mask 111)) (eq ▸ (by decide +kernel : (2:V)∈mask 111)) (by decide +kernel)
  have h9 := code_excludes h hc b hb f 13 11 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (13:V)∉mask 111) hin : (13:V)∈eligSet 14 D) miss9
  have impossible : ∀ a9 a10 a11 a13 : Finset (Fin 3), (¬ a9⊆a11) → (¬ a9⊆a13) → (¬ a10⊆a9) → (a10=∅ ∨ ¬ a10⊆a13) → (¬ a11⊆a9) → (a11=∅ ∨ ¬ a11⊆a10) → (a11=∅ ∨ ¬ a11⊆a13) → (¬ a13⊆a9) → (a13=∅ ∨ ¬ a13⊆a10) → (a13=∅ ∨ ¬ a13⊆a11) → False := by decide +kernel
  exact impossible (code f 9) (code f 10) (code f 11) (code f 13) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 8192 in
theorem residual_exclude4757 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 4757=ineligSet 14 D) : False := by
  classical
  obtain ⟨b,hb⟩ := sem_exists_pureBranch graph_ok h.1 hc
  have card := card_residual h.1 b hb
  have el := inelig_card_add 14 D
  rw [←eq] at el
  have count : (mask 4757).card=6 := by decide +kernel
  have res : Fintype.card ↥(residualUnits 14 D b)=3 := by rw [Fintype.card_coe]; omega
  let f := (Fintype.equivFinOfCardEq res).symm
  have miss0 := exposed_exact h hc z (mask 127) (mask 2087) (by decide +kernel) (by decide +kernel) 7 3 5 (eq ▸ (by decide +kernel : (7:V)∈mask 4757)) (by decide +kernel)
  have h0 := code_diff h hc b hb f 3 5 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (3:V)∉mask 4757) hin : (3:V)∈eligSet 14 D) miss0 (share h hc (i:=12) (x:=3) (y:=5) (eq ▸ (by decide +kernel : (12:V)∈mask 4757)) (by decide +kernel) (by decide +kernel))
  have miss1 := two_exact h hc z (mask 8297) (by decide +kernel) 12 7 3 13 5 (eq ▸ (by decide +kernel : (12:V)∈mask 4757)) (eq ▸ (by decide +kernel : (7:V)∈mask 4757)) (by decide +kernel)
  have h1 := code_excludes h hc b hb f 3 13 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (3:V)∉mask 4757) hin : (3:V)∈eligSet 14 D) miss1
  have miss2 := exposed_exact h hc z (mask 127) (mask 1102) (by decide +kernel) (by decide +kernel) 9 5 3 (eq ▸ (by decide +kernel : (9:V)∈mask 4757)) (by decide +kernel)
  have h2 := code_diff h hc b hb f 5 3 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (5:V)∉mask 4757) hin : (5:V)∈eligSet 14 D) miss2 (share h hc (i:=12) (x:=5) (y:=3) (eq ▸ (by decide +kernel : (12:V)∈mask 4757)) (by decide +kernel) (by decide +kernel))
  have miss3 := two_exact h hc z (mask 314) (by decide +kernel) 9 12 5 8 1 (eq ▸ (by decide +kernel : (9:V)∈mask 4757)) (eq ▸ (by decide +kernel : (12:V)∈mask 4757)) (by decide +kernel)
  have h3 := code_excludes h hc b hb f 5 8 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (5:V)∉mask 4757) hin : (5:V)∈eligSet 14 D) miss3
  have miss4 := two_exact h hc z (mask 8297) (by decide +kernel) 9 12 5 13 6 (eq ▸ (by decide +kernel : (9:V)∈mask 4757)) (eq ▸ (by decide +kernel : (12:V)∈mask 4757)) (by decide +kernel)
  have h4 := code_excludes h hc b hb f 5 13 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (5:V)∉mask 4757) hin : (5:V)∈eligSet 14 D) miss4
  have miss5 := two_exact h hc z (mask 1290) (by decide +kernel) 0 2 8 3 10 (eq ▸ (by decide +kernel : (0:V)∈mask 4757)) (eq ▸ (by decide +kernel : (2:V)∈mask 4757)) (by decide +kernel)
  have h5 := code_excludes h hc b hb f 8 3 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (8:V)∉mask 4757) hin : (8:V)∈eligSet 14 D) miss5
  have miss6 := exposed_exact h hc z (mask 9992) (mask 9288) (by decide +kernel) (by decide +kernel) 0 8 13 (eq ▸ (by decide +kernel : (0:V)∈mask 4757)) (by decide +kernel)
  have h6 := code_diff h hc b hb f 8 13 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (8:V)∉mask 4757) hin : (8:V)∈eligSet 14 D) miss6 (share h hc (i:=2) (x:=8) (y:=13) (eq ▸ (by decide +kernel : (2:V)∈mask 4757)) (by decide +kernel) (by decide +kernel))
  have miss7 := two_exact h hc z (mask 8488) (by decide +kernel) 2 4 13 3 8 (eq ▸ (by decide +kernel : (2:V)∈mask 4757)) (eq ▸ (by decide +kernel : (4:V)∈mask 4757)) (by decide +kernel)
  have h7 := code_excludes h hc b hb f 13 3 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (13:V)∉mask 4757) hin : (13:V)∈eligSet 14 D) miss7
  have miss8 := two_exact h hc z (mask 8488) (by decide +kernel) 2 4 13 5 8 (eq ▸ (by decide +kernel : (2:V)∈mask 4757)) (eq ▸ (by decide +kernel : (4:V)∈mask 4757)) (by decide +kernel)
  have h8 := code_excludes h hc b hb f 13 5 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (13:V)∉mask 4757) hin : (13:V)∈eligSet 14 D) miss8
  have miss9 := exposed_exact h hc z (mask 9992) (mask 1290) (by decide +kernel) (by decide +kernel) 4 13 8 (eq ▸ (by decide +kernel : (4:V)∈mask 4757)) (by decide +kernel)
  have h9 := code_diff h hc b hb f 13 8 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (13:V)∉mask 4757) hin : (13:V)∈eligSet 14 D) miss9 (share h hc (i:=2) (x:=13) (y:=8) (eq ▸ (by decide +kernel : (2:V)∈mask 4757)) (by decide +kernel) (by decide +kernel))
  have impossible : ∀ a3 a5 a8 a13 : Finset (Fin 3), (¬ a3⊆a5) → (a3=∅ ∨ ¬ a3⊆a13) → (¬ a5⊆a3) → (a5=∅ ∨ ¬ a5⊆a8) → (a5=∅ ∨ ¬ a5⊆a13) → (a8=∅ ∨ ¬ a8⊆a3) → (¬ a8⊆a13) → (a13=∅ ∨ ¬ a13⊆a3) → (a13=∅ ∨ ¬ a13⊆a5) → (¬ a13⊆a8) → False := by decide +kernel
  exact impossible (code f 3) (code f 5) (code f 8) (code f 13) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 8192 in
theorem residual_exclude2213 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 2213=ineligSet 14 D) : False := by
  classical
  obtain ⟨b,hb⟩ := sem_exists_pureBranch graph_ok h.1 hc
  have card := card_residual h.1 b hb
  have el := inelig_card_add 14 D
  rw [←eq] at el
  have count : (mask 2213).card=5 := by decide +kernel
  have res : Fintype.card ↥(residualUnits 14 D b)=2 := by rw [Fintype.card_coe]; omega
  let f := (Fintype.equivFinOfCardEq res).symm
  have miss0 := exposed_exact h hc z (mask 127) (mask 4183) (by decide +kernel) (by decide +kernel) 7 3 6 (eq ▸ (by decide +kernel : (7:V)∈mask 2213)) (by decide +kernel)
  have h0 := code_diff h hc b hb f 3 6 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (3:V)∉mask 2213) hin : (3:V)∈eligSet 14 D) miss0 (share h hc (i:=11) (x:=3) (y:=6) (eq ▸ (by decide +kernel : (11:V)∈mask 2213)) (by decide +kernel) (by decide +kernel))
  have miss1 := two_exact h hc z (mask 1290) (by decide +kernel) 0 2 8 3 10 (eq ▸ (by decide +kernel : (0:V)∈mask 2213)) (eq ▸ (by decide +kernel : (2:V)∈mask 2213)) (by decide +kernel)
  have h1 := code_excludes h hc b hb f 8 3 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (8:V)∉mask 2213) hin : (8:V)∈eligSet 14 D) miss1
  have miss2 := exposed_exact h hc z (mask 9992) (mask 9288) (by decide +kernel) (by decide +kernel) 2 8 10 (eq ▸ (by decide +kernel : (2:V)∈mask 2213)) (by decide +kernel)
  have h2 := code_diff h hc b hb f 8 10 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (8:V)∉mask 2213) hin : (8:V)∈eligSet 14 D) miss2 (share h hc (i:=0) (x:=8) (y:=10) (eq ▸ (by decide +kernel : (0:V)∈mask 2213)) (by decide +kernel) (by decide +kernel))
  have miss3 := two_exact h hc z (mask 1290) (by decide +kernel) 0 5 10 3 8 (eq ▸ (by decide +kernel : (0:V)∈mask 2213)) (eq ▸ (by decide +kernel : (5:V)∈mask 2213)) (by decide +kernel)
  have h3 := code_excludes h hc b hb f 10 3 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (10:V)∉mask 2213) hin : (10:V)∈eligSet 14 D) miss3
  have miss4 := exposed_exact h hc z (mask 7426) (mask 4370) (by decide +kernel) (by decide +kernel) 5 10 8 (eq ▸ (by decide +kernel : (5:V)∈mask 2213)) (by decide +kernel)
  have h4 := code_diff h hc b hb f 10 8 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (10:V)∉mask 2213) hin : (10:V)∈eligSet 14 D) miss4 (share h hc (i:=0) (x:=10) (y:=8) (eq ▸ (by decide +kernel : (0:V)∈mask 2213)) (by decide +kernel) (by decide +kernel))
  have impossible : ∀ a3 a6 a8 a10 : Finset (Fin 2), (¬ a3⊆a6) → (a8=∅ ∨ ¬ a8⊆a3) → (¬ a8⊆a10) → (a10=∅ ∨ ¬ a10⊆a3) → (¬ a10⊆a8) → False := by decide +kernel
  exact impossible (code f 3) (code f 6) (code f 8) (code f 10) h0 h1 h2 h3 h4

end PEqualNP.Outside.L_meta_9775.UpstreamCore

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore
open DagTools

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 8192 in
theorem residual_empty4293 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (z : Bzero 14 D=0) (eq : mask 4293=ineligSet 14 D)
    (b : V → Nat) (hb : PureBranch 14 D b)
    (f : Fin 2 ≃ ↥(residualUnits 14 D b)) : code f 5=∅ ∧ code f 10=∅ := by
  classical
  have miss0 := exposed_exact h hc z (mask 127) (mask 2087) (by decide +kernel) (by decide +kernel) 7 3 5 (eq ▸ (by decide +kernel : (7:V)∈mask 4293)) (by decide +kernel)
  have h0 := code_diff h hc b hb f 3 5 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (3:V)∉mask 4293) hin : (3:V)∈eligSet 14 D) miss0 (share h hc (i:=12) (x:=3) (y:=5) (eq ▸ (by decide +kernel : (12:V)∈mask 4293)) (by decide +kernel) (by decide +kernel))
  have miss1 := two_exact h hc z (mask 314) (by decide +kernel) 7 12 3 8 1 (eq ▸ (by decide +kernel : (7:V)∈mask 4293)) (eq ▸ (by decide +kernel : (12:V)∈mask 4293)) (by decide +kernel)
  have h1 := code_excludes h hc b hb f 3 8 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (3:V)∉mask 4293) hin : (3:V)∈eligSet 14 D) miss1
  have miss2 := two_exact h hc z (mask 1102) (by decide +kernel) 7 12 3 10 1 (eq ▸ (by decide +kernel : (7:V)∈mask 4293)) (eq ▸ (by decide +kernel : (12:V)∈mask 4293)) (by decide +kernel)
  have h2 := code_excludes h hc b hb f 3 10 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (3:V)∉mask 4293) hin : (3:V)∈eligSet 14 D) miss2
  have miss3 := exposed_exact h hc z (mask 314) (mask 792) (by decide +kernel) (by decide +kernel) 12 5 8 (eq ▸ (by decide +kernel : (12:V)∈mask 4293)) (by decide +kernel)
  have h3 := code_excludes h hc b hb f 5 8 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (5:V)∉mask 4293) hin : (5:V)∈eligSet 14 D) miss3
  have miss4 := two_exact h hc z (mask 792) (by decide +kernel) 6 0 8 3 9 (eq ▸ (by decide +kernel : (6:V)∈mask 4293)) (eq ▸ (by decide +kernel : (0:V)∈mask 4293)) (by decide +kernel)
  have h4 := code_excludes h hc b hb f 8 3 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (8:V)∉mask 4293) hin : (8:V)∈eligSet 14 D) miss4
  have miss5 := two_exact h hc z (mask 2338) (by decide +kernel) 6 0 8 5 11 (eq ▸ (by decide +kernel : (6:V)∈mask 4293)) (eq ▸ (by decide +kernel : (0:V)∈mask 4293)) (by decide +kernel)
  have h5 := code_excludes h hc b hb f 8 5 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (8:V)∉mask 4293) hin : (8:V)∈eligSet 14 D) miss5
  have miss6 := two_exact h hc z (mask 7426) (by decide +kernel) 6 2 8 10 11 (eq ▸ (by decide +kernel : (6:V)∈mask 4293)) (eq ▸ (by decide +kernel : (2:V)∈mask 4293)) (by decide +kernel)
  have h6 := code_diff h hc b hb f 8 10 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (8:V)∉mask 4293) hin : (8:V)∈eligSet 14 D) miss6 (share h hc (i:=0) (x:=8) (y:=10) (eq ▸ (by decide +kernel : (0:V)∈mask 4293)) (by decide +kernel) (by decide +kernel))
  have miss7 := exposed_exact h hc z (mask 1290) (mask 314) (by decide +kernel) (by decide +kernel) 0 10 3 (eq ▸ (by decide +kernel : (0:V)∈mask 4293)) (by decide +kernel)
  have h7 := code_excludes h hc b hb f 10 3 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (10:V)∉mask 4293) hin : (10:V)∈eligSet 14 D) miss7
  have finite : ∀ a3 a5 a8 a10 : Finset (Fin 2), (¬ a3⊆a5) → (a3=∅ ∨ ¬ a3⊆a8) → (a3=∅ ∨ ¬ a3⊆a10) → (a5=∅ ∨ ¬ a5⊆a8) → (a8=∅ ∨ ¬ a8⊆a3) → (a8=∅ ∨ ¬ a8⊆a5) → (¬ a8⊆a10) → (a10=∅ ∨ ¬ a10⊆a3) → a5=∅ ∧ a10=∅ := by decide +kernel
  exact finite (code f 3) (code f 5) (code f 8) (code f 10) h0 h1 h2 h3 h4 h5 h6 h7

end PEqualNP.Outside.L_meta_9775.UpstreamCore

/-
The last-case strategy below is adapted from `elim_132` / `pa_m1` in
Thomas Brovelli (GitHub ithurtstom), public PR #18338, exact head
79345c8812d893da9c305e0d1bec931bb198594a:
https://github.com/open-goat/pequalnp-proofs/pull/18338
This specialization uses our existing DagTools and direct slot counting.
-/
namespace PEqualNP.Outside.L_meta_9775.UpstreamCore
open DagTools
namespace Public4293

theorem assigned_mem {D : Dag} {pos : V → Nat × Bool}
    (hp : k4_Pos 14 adj D pos) {i x : V}
    (hi : i ∈ ineligSet 14 D) (hx : adj i x) : pos i ∈ sem_W 14 D x := by
  obtain ⟨h1,h2,h4,_⟩ := hp.1 i hi
  exact sem_mem_W.mpr ⟨h1,h4 x hx,by rw [h2]; exact Finset.notMem_empty x⟩

theorem assigned_private {D : Dag} {pos : V → Nat × Bool}
    (hp : k4_Pos 14 adj D pos) {i x : V}
    (hi : i ∈ ineligSet 14 D) (hx : sem_bar (pos i) ∈ sem_W 14 D x) : x=i := by
  have yes := (sem_mem_W.mp hx).2.1
  rw [show src D (sem_bar (pos i))=src D ((pos i).1, !(pos i).2) from rfl,
    (hp.1 i hi).2.2.2] at yes
  exact Finset.mem_singleton.mp yes

theorem two_slots {α : Type} [DecidableEq α] {S : Finset α} {a b : α}
    (ha : a∈S) (hb : b∈S) (ab : a≠b) (bound : S.card≤2) :
    ∀ e∈S, e=a ∨ e=b := by
  intro e he
  by_contra bad
  rw [not_or] at bad
  have many := Finset.two_lt_card.mpr ⟨e,he,a,ha,b,hb,bad.1,bad.2,ab⟩
  omega

set_option maxHeartbeats 0 in
theorem low_slots_impossible {D : Dag} (h : StrictLive 14 D)
    (hc : sem_Comp 14 adj D) (eq : mask 4293=ineligSet 14 D)
    (h5 : (sem_W 14 D 5).card≤2) (h10 : (sem_W 14 D 10).card≤2) : False := by
  classical
  obtain ⟨pos,hp⟩ := k4_assigned graph_ok h hc
  have i0 : (0:V)∈ineligSet 14 D := eq ▸ (by decide +kernel : (0:V)∈mask 4293)
  have i12 : (12:V)∈ineligSet 14 D := eq ▸ (by decide +kernel : (12:V)∈mask 4293)
  have p0 := assigned_mem hp i0 (by decide +kernel : adj 0 10)
  have p12 := assigned_mem hp i12 (by decide +kernel : adj 12 5)
  obtain ⟨e,he,be,_⟩ := sem_edge_slots graph_ok h.1 hc (by decide +kernel : adj 5 10)
  obtain ⟨f,hf,bf,_⟩ := sem_edge_slots graph_ok h.1 hc (by decide +kernel : adj 5 9)
  have ep : e≠pos 12 := by
    intro same
    have bad : (10:V)=12 := assigned_private hp i12 (same ▸ be)
    exact (by decide : (10:V)≠12) bad
  have fp : f≠pos 12 := by
    intro same
    have bad : (9:V)=12 := assigned_private hp i12 (same ▸ bf)
    exact (by decide : (9:V)≠12) bad
  have fe : f=e := (two_slots p12 he ep.symm h5 f hf).resolve_left fp
  have be0 : sem_bar e≠pos 0 := by
    intro same
    have hei : sem_bar (pos 0)∈sem_W 14 D 5 := by rw [←same,sem_bar_bar]; exact he
    have bad : (5:V)=0 := assigned_private hp i0 hei
    exact (by decide : (5:V)≠0) bad
  obtain ⟨g,hg,no8,no9⟩ := sem_cover_free graph_ok h.1 hc
    (by decide +kernel : ¬adj 8 9) (by decide +kernel : adj 10 4)
    (by decide +kernel : ¬adj 4 8) (by decide +kernel : ¬adj 4 9)
  have gp : g≠pos 0 := by
    intro same
    exact no8 (same ▸ (hp.1 0 i0).2.2.1 8 (by decide +kernel : adj 0 8))
  have ge : g=sem_bar e := (two_slots p0 be be0.symm h10 g hg).resolve_left gp
  exact no9 (by rw [ge,←fe]; exact (sem_mem_W.mp bf).2.1)

end Public4293
end PEqualNP.Outside.L_meta_9775.UpstreamCore

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore
open DagTools

set_option maxHeartbeats 0 in
theorem residual_exclude4293 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 4293=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := Compact.construct_layout (k:=2) h hc bp eq (by decide +kernel)
  obtain ⟨empty5,empty10⟩ := residual_empty4293 h hc z eq Z.branch Z.pure Z.order
  apply Public4293.low_slots_impossible h hc eq
  · simpa only [Compact.countAt,empty5,Finset.card_empty,Nat.add_zero] using Z.size_code h hc 5
  · simpa only [Compact.countAt,empty10,Finset.card_empty,Nat.add_zero] using Z.size_code h hc 10

end PEqualNP.Outside.L_meta_9775.UpstreamCore

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def aP11 := ([0x120101,0x140101,0x160101,0x120901,0x140901,0x160901,0x4107,0x24107,0xa907,0x2a907,0x2c0108,0xac0108,0x3a0108,0xba0108,0x120121,0x120921,0x160161,0x120161,0x180161,0x160961,0x120961,0x180961,0x7967,0x27967,0x281968,0xa81968,0x8005,0x28005,0x8805,0x28805,0x9005,0x29005,0x8025,0x28025,0x128026,0x168026,0x8825,0x28825,0x128826,0x9025,0x29025,0x129026,0x169026,0x8a04,0x9204,0x9224] : List Nat).toArray.map readPackedFact
def rP11 := ([0x4105,0x104909,0x105109,0x904909,0x905109,0xa905,0x2a5109,0x2a5909,0xaa5109,0xaa5909,0x2c0106,0xb14010a,0xb16010a,0x2b14010a,0x2b16010a,0x3a0106,0xe92010a,0xe94010a,0x2e92010a,0x2e94010a,288,0x920,352,0x960,0x7965,0x1e4969,0x1e6169,0x9e4969,0x9e6169,0x281966,0xa12196a,0xa18196a,0x2a12196a,0x2a18196a,0x8010,0x8810,0x9010,0x8030,0x4808032,0x5808032,0x4828032,0x5828032,0x8830,0x24808832,0x24828832,0x9030,0x4809032,0x25809032,0x4829032,0x25829032,0x228014,0xa28014,0x4a28033,0x248014,0xa48014,0x5a48033,0x248814,0xa48814,0x24a48833] : List Nat).map readPackedScheme

def tableP11_0 : List Nat := [0x1e342,770,0x4302,0xc382,0x10382,0x26442,0x4402,0x8402,0x10482,0x14482,0x2e542,0x6502,0x8502,0x12582,0x14582,0x36642,0x602,0x6602,0xc682,0x12682,0x741,0x7c1,0x841,0x9c1,0x5eb42,0x44b02,0x48b02,0x50b82,0x54b82,0x66c42,0x44c02,0x4ac02,0x50c82,0x56c82,0x6ed42,0x76e42,0x7ef42,0x87042,0x4403003,0x460b003,0x440f083,0x4617083,0x97242,0x4d39203,0x4d3d283,0xa33c2,0x5247383,0x5541383,0x5253403,0x554d403,0x5770d03,0x5774d83,0x4c8b583,0x5978d03,0x597cd83,0x548f603,0x5b78e03,0x5b7ce83,0x5399683,0x9b202,0x9b282,0xab382,0xab402,0xa01]
def tableP11_1 : List Nat := [0x881,0x1481,0x1341,0x1681,385,1,0x1101,0x1581,257,641,0x1181,0x1541,0x1601,0xf81,0xf41,0xd01,0xe01,0xdc1,0xec1]

def encodedP11 (i : Nat) : Nat :=
  if i < 64 then
    tableP11_0.getD (i%64) 0
  else
    tableP11_1.getD (i%64) 0
def bookP11 (i : Nat) : Clause := let n := encodedP11 i; unpackLits 7 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClausesP11 : inputsOK 0 11 aP11 rP11 (baseBook bookP11 59).toList=true := by decide +kernel

def rowsP11_0 : List Nat := [0x145601,0x155801,0x165e01,0x176201,0x1a3a6101b3e05,0x1c3a60f194205,0x5cc203f5a04,0x1e3b5402,0x20c27402,0x21e009032205,0x41e008012605,0x4ca22c44a04,0x21466802,0x814146071a05,0x614147091605,0x529e4c84a04,0x1f3d5a02,0x254b6e02,0x8d1396d1e1cc6407,0x4d4801,0x264e6a02,0x21ce7002,0x4f4401,0x504601]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOkP11_0 : checkRows bookP11 7 59 rowsP11_0=true := by decide +kernel

def lastUnitsP11 := digits 7 3 0x11e8d2
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflictP11 : checkReasons bookP11 83 51 lastUnitsP11 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem excludeP11 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 11=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=0) h hc bp eq (by decide +kernel)
  let v := truth Z aP11
  have hbase : ValidThrough v bookP11 59 := book_start Z h hc z eq _ _ _ _ initialClausesP11
  have h0 : ValidThrough v bookP11 83 := rows_sound hbase rowsP11_0 rowsOkP11_0
  exact book_end h0 _ _ conflictP11
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def aP47 := ([1,0xc0001,0x3007,0x4002,0x4022,0x4802,0x4822,0x5002,0x5022,65,0xc0041,0xc047,0xc00c1,0xc08c1,0xc10c1,0xc18c1,0x100101,0x900,0x120101,0x4903,0x140101,0x5103,0x1a0101,0x100901,0x1100,0x120901,0x140901,0x1a0901,0x101101,0x1900,0x121101,0x141101,0x1a1101,0x141901,0x1a1901,0x4107,0x24107,0x44107,0x64107,0xe107,0x2e107,0x4e107,0x6e107,0x3a0108,0xba0108,0x13a0108,0x1ba0108,0x3a1108,0xba1108,0x13a1108,0x1ba1108,0x124009,0x124029,0x144009,0x144029,0xe0121,0x5123,0x180121,0x1120,0xe0921,0x180921,0x1920,0x6927,0x26927,0x46927,0x66927,0x1e0928,0x9e0928,0x11e0928,0x19e0928,0x1e2928,0x9e2928,0x11e2928,0x19e2928,0x940,0x100141,0x120141,0x180141,0x1140,0x100941,0x120941,0x180941,0x141141,0x1940,0x101141,0x121141,0x181141,0x2947,0x22947,0x42947,0x62947,0x7147,0x27147,0x47147,0x67147,0xe0148,0x8e0148,0x10e0148,0x18e0148,0x3a0148,0xba0148,0x13a0148,0x1ba0148,0x2c2948,0xac2948,0x12c2948,0x1ac2948,0x3a2948,0xba2948,0x13a2948,0x1ba2948,0x105009,0x105029,0x125009,0x125029,5,6,0xc0006,0x805,0x2805,0x2806,0xc2806,0x8005,0x28005,0x48005,0x68005,0xc8006,37,0x20025,0x40025,0x60025,0x100026,0x120026,0x140026,0x825,0x20825,0x40825,0x60825,0x100826,0x120826,0x140826,0x2825,0x22825,0x42825,0x62825,0x8025,0x28025,0x48025,0x68025,0x804,0x2804,0x8004,0x80a4] : List Nat).toArray.map readPackedFact
def rP47 := ([0,0x3005,0xc3009,0xc045,0x300049,0x303049,192,0x8c0,0x10c0,0x18c0,256,0x900,0x901,0x1100,0x1101,260,0x904,0x4105,0x104909,0x105109,0x904909,0x905109,0x1104909,0x1105109,0x64107,0xe105,0x385109,0x386909,0xb85109,0xb86909,0x1385109,0x1386909,0x6e107,0x1b85109,0x1b86909,0x3a0106,0xe92010a,0xe94010a,0x2e92010a,0x2e94010a,0x4e92010a,0x4e94010a,0x1ba0108,0x3a1106,0xe94110a,0xe9a110a,0x2e94110a,0x2e9a110a,0x4e94110a,0x4e9a110a,0x1ba1108,0x6e94110a,0x6e9a110a,0x12400b,0x12400c,0x490e,0x12402b,0x12402c,0x2490e,0x80490f,0x100490f,0x102490f,0x14400b,0x14400c,0x14402b,0x14402c,0x510d,0x80510f,0x100510f,0x180510f,0x102510f,0x182510f,0x184510f,291,0x924,0x6925,0x1a3929,0x1a6129,0x9a3929,0x9a6129,0x46927,0x66927,0x1e0926,0x78e092a,0x278e092a,0x11e0928,0x19e0928,0x1e2926,0x78e292a,0x798292a,0x278e292a,0x2798292a,0x11e2928,0x19e2928,0xa512d,0x941,0x1140,324,0x944,0x2945,0xa4149,0xa4949,0x8a4149,0x8a4949,0x42947,0x10a4149,0x10a4949,0x62947,0x7145,0x1c4149,0x1c6149,0x9c4149,0x9c6149,0x11c4149,0x11c6149,0x67147,0xe0146,0x390014a,0x2390014a,0x10e0148,0x18e0148,0x3a0146,0xe90014a,0xe92014a,0x2e90014a,0x2e92014a,0x4e90014a,0x1ba0148,0x2c2946,0xb10294a,0xb18294a,0x2b10294a,0x2b18294a,0x4b10294a,0x4b18294a,0x1ac2948,0x3a2946,0xe92294a,0x2e92294a,0x13a2948,0x1ba2948,0x10500c,0x10502c,0x80414f,0x100414f,0x102414f,0x12500b,0x12500c,0x12502b,0x12502c,0x80494f,0x100494f,0x102494f,16,0x20000012,0x3000012,0x810,0x2810,0x2812,0x3002812,0x8010,0x23008012,0x23028012,0x23048012,0x23068012,48,0x24000032,0x4800032,0x5000032,0x24020032,0x4820032,0x5020032,0x40031,0x24040032,0x4840032,0x5040032,0x60031,0x830,0x4000832,0x4020832,0x24840832,0x25040832,0x60831,0x2830,0x42831,0x62831,0x8030,0x48031,0x68031,0x20014,0x24020033,0x4820033,0x5020033,0x200a0013,0xa0034,0x8a0034,0x3200013,0x200034,0xa00034,0x3202813,0x202834,0xa02834] : List Nat).map readPackedScheme

def tableP47_0 : List Nat := [65,321,0x10102,0x5c1,0x90582,0xa0582,0x641,0x6c1,0x741,0x7c1,0x841,0xbc1,0x118c02,0xe41,0x188e82,0x38e82,0x48e82,0x9a4b2491c4,0x121182,0x141182,0x191202,0x1a1202,0x1e1282,0x1f1282,0x1d9302,0xaa532893c4,0x141382,0x161382,0x1a1402,0x1b1402,0x1f1482,0x201482,0x1d9502,0x211502,0x221502,0xba5b2c95c4,0x121582,0x149582,0x191602,0x1a9602,0x1e1682,0x1f9682,0x1d9702,0xca633097c4,0x141782,0x169782,0x1a1802,0x1b9802,0x1f1882,0x209882,0x1d9902,0x211902,0x229902,0x39982,0x51982,0x27050183,0x49a02,0x61a02,0x27060203,0x3499c6625110986,0x3499c7a25180986,0x3499c7a33180986,0x39a82,0x71a82]
def tableP47_1 : List Nat := [0x49b02,0x81b02,0xac1,0x369ac6a29110a86,0x369ac7e29180a86,0x369ac86291d0a86,0x369ac7e35180a86,0x369ac86351d0a86,0x369ac863f1d0a86,0xd059d03,0x69e82,0x106813f9f44,0x371f02,0x391f02,0x3b1f82,0x3c1f82,0x3aa002,0x3da082,0x1168943a144,0x37a102,0x3ba182,0x3aa202,0x3da282,0x1269147a344,0x372302,0x39a302,0x3b2382,0x3ca382,0x3aa402,0x3da482,0x1c41,0x4aa702,0x2941,0x7a982,0x8a982,0x16ab358abc4,0x4b2b82,0x4c2b82,0x4f2c02,0x502c02,0x4eac82,0x542c82,0x552c82,0x53ad02,0x17abb5cadc4,0x4b2d82,0x4d2d82,0x4f2e02,0x512e02,0x542e82,0x562e82,0x53af02,0x18ac360afc4,0x4baf82,0x4fb002,0x4eb082,0x53b102,0x19acb64b1c4,0x4bb182,0x4c3182,0x4fb202,0x503202,0x54b282,0x53b302]
def tableP47_2 : List Nat := [0x1aad368b3c4,0x4b3382,0x4db382,0x4f3402,0x51b402,0x543482,0x56b482,0x53b502,0x1badb6cb5c4,0x4cb582,0x50b602,0x4eb682,0x53b702,0x33782,0x43802,0x70b7d3e974a0a86,0x70b7d52974e0a86,0x70b7d529f4e0a86,0x7b882,0x53882,0x8b902,0x63902,0x72b8d42994a1c06,0x72b8d56994e1c06,0x72b8d56a14e1c06,0x39c1,0xe9003983,0xea01b983,0x3b41,0x3bc1,0xf009bb83,0xf20abb83,0x1f6f97bbd44,0xfd0c3d03,0xfd0d3d83,0xfd0e3e03,0xfd0f3e83,0x20b0380bfc4,0x107103f83,0x10812bf83,0x10a14bf83,0x107174003,0x10819c003,0x10a1ac003,0x18c082,0x1071c4083,0x1081ec083,0x10a1fc083,0x1dc102,0x2271187c344,0x1144bc303,0x1144fc383,0x117554403,0x119524403,0x53c482,0x2431f8ec6c4,0x18c782,0x1dc802,0x2532792c8c4,0x18c982,0x1dca02,0x12b763983,0x115834a83,0x11684ca83]
def tableP47_3 : List Nat := [0x11885ca83,0xf1744b03,0x12d8d3f83,0x12d8e4003,0xfc75cb83,0x12f913f83,0x12f924003,0xfc79cc03,0x131914683,0x131924703,129,0x481,0x501,0x1b4d635148885,0x1b4d63f148c05,0x1b4d643148e85,0x1b4d63f1a8c05,0x1b4d6431a8e85,0x1b4d6431f8e85,0x385be9f4ba505,0x385bea94ba705,0x385bea94fa705,0x395c6a14ca505,0x395c6ab4ca705,0x395c6ab50a705,0x3a41,0x3a81,0x3c01,0x3c81,0x7ebd02,0x7ebd82,0x7ebe02,0x7ebe82,0x83bf82,0x83c002,0x83c082,0x8cc402,0x4ac1,0x8ac182,0x8b4242,0x8c42c2,0x4b01,0x8d3f82,0x8e4002,0x7e4b82,0x7e4c02,0x3f41,0x4b81,0x4c01,0x7b3aa383,0x3d9d42,0x74a6299904,0x894c63329385,0x894c63329405,0x3a530f83,0x1d2982,0xc0da6b329485,0x181b4d6532a8fc6,0x194a655318d05,0xc0da6b329545,0xa74f2583,0x3a4f2a43,0x1d2782,0x1d25c2]
def tableP47_4 : List Nat := [0x1d2a02,0xe81,0x1301,0x1501,0x1701,0x1901,0x4101,0x4801,0x4a01,0x2063514c284,0x18bf82,0xc41,0x8c1,0x2d5baaf6ba745,0xc692d0284,0x71ad532af4e3946,0xd267131584,0xa94f9a83,0x58342,0xce69131604,0x67348983,0x54a7c2,0x2981,0x2d01,0x2f01,0x3101,0x3301,0x3501,0x3701,0x4481,0xd088c503,0x1a03514c0c4,0x1a0aa1ec084,0xd0551683,0x2a86a2581c405,0x1a0aa1ac0c4,0xd0550d43,0x1a0f82,0xd01fc083,0x81c1c2,0x1a0a02,0x682a82,0x681982,0x681a02,0xd071b943,0x13b902,0x3401,0x54a742,0xa94c81c3,0x54a642,0x548242,0x2a41,0x2c81,0x2e81,0x3481,0x33c1,0x2581,0x26c1,0x2f81,0x2d81,0x2e41,0x2781,0x3001,0x30c1]
def tableP47_5 : List Nat := [0x2741,0x2541,0x3881,0x154ff19c0c4,0xaa7f8d03,0x88c502,0x41c1,0x4541,0x4441,0x4641,0x42c1,0x553fc2,0x2a81,0x3941,0x441,769,0x9c1,0x1b01,705,0x1ac1,0x1981,449,0x1a41,0x3781,577,0x3841]

def encodedP47 (i : Nat) : Nat :=
  if i < 192 then
    if i < 64 then
      tableP47_0.getD (i%64) 0
    else
      if i < 128 then
        tableP47_1.getD (i%64) 0
      else
        tableP47_2.getD (i%64) 0
  else
    if i < 256 then
      tableP47_3.getD (i%64) 0
    else
      if i < 320 then
        tableP47_4.getD (i%64) 0
      else
        tableP47_5.getD (i%64) 0
def bookP47 (i : Nat) : Clause := let n := encodedP47 i; unpackLits 9 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClausesP47 : inputsOK 2 47 aP47 rP47 (baseBook bookP47 202).toList=true := by decide +kernel

def rowsP47_0 : List Nat := [0x40401,0xc0801,0xc0a01,0x1088601,0x1088801,0x1088a01,0x1088c01,0x1088e01,0x1089001,0x1091e01,0x1092001,0x1092201,0x1792c01,0x1792e01,0x1793001,0x2653402,0x652653602,0x65a753c02,0x662753e02,0x194201,0x1d4401,0x214601,0x254801,0x294c01,0x2d5201,0x355a01,0x1816a01,0x4e2657a02,0x3957c01,0x3957e01,0x3958001,0x6db658202,0x3a58401,0x3a58601,0x3698801,0x3718e01,0x1c0df6f3754004,0x3b9d801,0x3b9da01,0x53259489e542d968a25628154980b,0x54259489a532c960aef12e154a0512b1749c0f,0x1c0d089a2cf1a0cc7e6120988320b,0xb85acd0d8687e61209885609,0xb05ecd0e8707e61209885609,0xb858d16788432f57a3cc601e060387e61209885611,0xf8ac322c0d0b8383310b39a0d27b1047e62308386212,0x2c170c59cd00f8785607,0x341c673403204,0x6c5619170705a05,0x1d15864581a66be860f9063e05e0b,0x1c9006c409b4e68737a0d0c09,0x220ca8a319f516683cb50fc8d07a38206b3fa30cc7a7e3dd1215,0x6e401b10a717ea0cde7343bdd040b,0xbe74699d51a0f47040f0f73b3f8ee0c,0x70401b10a7139a1dee6d40bfd080b,0x8833a24c67b459a0f2d53f400c8ff3e3f9187f35bdd1c8d0803d1417,0x4043001,0x4044001,0x4045401,0x4046401,0x4056001,0x4057201,0x4057801,0xab544194a03,0x5d2dd8aea5c2ede10883bbd920a,0x5d2dd8ceb52c2976b8563c2110777c19900e,0x42c1801,0x19d1063459a11405,0x120a0f07a371b0a02e298142c220b,0x19cd4d66b97cc605,0xb050263c1d894490285c30220a,0x2c120a8f476271308e210e1b8d892f2252561e38473561a89321ecf479461fcd69230a347e3e3f1f2050b864102228,0x24929e402,0xb0482a3d1d89c4d0285c30220a,0x4828171e0f4522811c4e210485c08220d,0xe873121aa4d1b0f6ac3512643d9e8f28c3f9ad28624710480fb889f0fd0382c2e281d,0x411f988c30382c2df607,0x458d601,0x458e601,0x458f001,0x458fe01,0x4590e01,0x4591801,0x4596c01,0xb2599b4d8718aa0ce0848ec61620b,0x1c4e173479c8e884c194a08,0x479cee65738d6805,0xe8ac322c0d47e40fa18078522882c0c5e0e,0xa755b9dd0b4724194a07,0xe270b9a3d221208c4f21834114a0b,0x745619180795ee872479cce3918b034251189e430581c105e15,0x601e81c15f404,0x479d0e657b8dc805,0xe270c194a03,0x7c561916068382e82c0c6209,0x265288d50259439dd0b472479cd27934964921824195413]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOkP47_0 : checkRows bookP47 9 202 rowsP47_0=true := by decide +kernel

def rowsP47_1 : List Nat := [0x6732b61ae921fbec808e4ab4e248d1b0d4d25f3b9d0ea6d361c62a70421d907298bc0e0b0b8cc60c623,0x6732b61ae9420bec7c8d49b4e248e1c8e0d25f3b9d0ea6d361c62a70421d907298bc0e0b0b8cc60c623,0xce656c35cd2773a1d4da6c38c54e0843b20e53178cc60c614,0xddf71220a55290382c2c7c09,0x1d3ee243f49a4a592d8a4ae550382c2c800e,0x1951063459a0cc8a3e9e4f4fc8a9fa39178d4591211,0x74398924dac9420901f63e1a9f4f27a7e454fc5f97c0e0b0b8d45a2818,0x114894b52ad6490fdf6401c239a88d981f4f27a7e454fc5f97c0e0b0b8d4586c1b,0x2291296a55b0921fbec80383e9e4f4fc3f4bcd46332cc4cd1581c1617178d4586c1c,0x74398924db09420bec7c3546b511d323518ccb31979f4f27a7e19a2a7e81c1617178d45a2820,0x4ccd201,0x4cce201,0x4cd0a01,0x11b974d90003,0x4dd0201,0x4dd0401,0x4e0ea01,0x4e4dc01,0x1189acecd803,0x4f0de01,0x4f4ec01,0x1199d4f8e803,0x4fcee01,0x500be01,0x46c51a63a4710072fb890fd26929ece2830382c2c6a12,0x162e7592cd54e652c9e3b389ec19680c,0x722c966e8732bdc7431308c4a29944963b389ec116212,0x2c9671d9c4f56205,0x38e4e01,0x519cc01,0x51e8a01,0x521c801,0x525d001,0x3a2b0c8b03425118a0601e572bd4aab13d11ceb482c0e094a835205e18,0xe8ac32300f0a44627124a0581a53aa296e75a4160704a55205e16,0x194ced76c4d22f4ca0508c609,0x5352801,0x5352a01,0x5365a01,0x5388201,0x53e2401,0x2170581d45f604,0x5486c01,0x54c7c01,0xa85522802,0x5551a01,0x5587001,0x283389ed5da604]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOkP47_1 : checkRows bookP47 9 298 rowsP47_1=true := by decide +kernel

def lastUnitsP47 := digits 9 2 0x2b159
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflictP47 : checkReasons bookP47 346 142 lastUnitsP47 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem excludeP47 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 47=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=2) h hc bp eq (by decide +kernel)
  let v := truth Z aP47
  have hbase : ValidThrough v bookP47 202 := book_start Z h hc z eq _ _ _ _ initialClausesP47
  have h0 : ValidThrough v bookP47 298 := rows_sound hbase rowsP47_0 rowsOkP47_0
  have h1 : ValidThrough v bookP47 346 := rows_sound h0 rowsP47_1 rowsOkP47_1
  exact book_end h1 _ _ conflictP47
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def aP164 := ([0xc0041,0xc047,0xc00a1,0x30a7,0xc00c1,0xc08c1,0x100101,0x160101,0x1a0101,0x100901,0x160901,0x1a0901,0xf107,0x2f107,0x920,0x100121,0x140121,0x5123,0x160121,0x180121,0x100921,0x140921,0x160921,0x180921,0x7127,0x27127,0x8927,0x28927,0x9927,0x29927,0xa927,0x2a927,0x202928,0xa02928,0x282928,0xa82928,0x160161,0x160961,0x1a01a1,0x1a09a1,0x2805,0xc2806,0x3005,0x6805,0xc6806,0x8005,0x28005,0xc8006,0x8805,0x28805,0xc8806,0x9005,0x29005,0xc9006,0x2825,0x22825,0x1a2826,0x3025,0x23025,0x1a3026,0x6825,0x26825,0x8025,0x28025,0x108026,0x168026,0x8825,0x28825,0x108826,0x168826,0x9025,0x29025,0x169026,0x30a4,0x80a4,0x89a4,0x8a04,0x9204,0x9224] : List Nat).toArray.map readPackedFact
def rP164 := ([0xc045,0x303049,0x30a5,0xc30a9,192,0x8c0,256,0x900,0xf105,0x3c5909,0x3c6909,0xbc5909,0xbc6909,0x7125,0x1c4129,0x1c6129,0x9c4129,0x9c6129,0x8925,0x225129,0xa26129,0x9925,0x266129,0xa65929,0xa925,0x2a5929,0xaa5129,0x202926,0x810292a,0x818292a,0x2810292a,0x2818292a,0x282926,0xa16292a,0xa18292a,0x2a16292a,0x2a18292a,0xa512d,0x80512f,352,0x960,416,0x9a0,0x2810,0x3002812,0x3010,0x6810,0x3006812,0x8010,0x8810,0x9010,0x23009012,0x23029012,0x2830,0x6802832,0x6822832,0x3030,0x26803032,0x26823032,0x6830,0x26831,0x8030,0x24008032,0x5808032,0x24028032,0x5828032,0x8830,0x4008832,0x5808832,0x4028832,0x5828832,0x9030,0x25809032,0x25829032,0xc2814,0x68c2833,0x3202813,0x202834,0xa02834,0x3226813,0x226834,0x228014,0xa28014,0x24228033,0x248014,0xa48014,0x3248013,0x5a48033,0x248814,0xa48814,0x3248813,0x5a48833] : List Nat).map readPackedScheme

def tableP164_0 : List Nat := [193,130,449,0x10182,577,705,833,0x4c1,0x6c642,0x38602,0x40602,0x50682,0x58682,0xccc42,0x78c02,0x98c02,0xa0c82,0xb8c82,0xdcd42,0x80d02,0xb8d82,0xece42,0x98e02,0xb0e82,0xfcf42,0x90f02,0xa8f82,0x10d042,0x79002,0x9d002,0xa1082,0xbd082,0x11d142,0x91102,0x9d102,0xb1182,0xbd182,0x8c1,0xac8470884,0x1241,0x12c1,0x1341,0x13c1,0x1441,0x14805403,0x1541,0x15c1,0x16015583,0x1756c2,0x18d842,0x1a59c2,0x1ac21983,0x1ac29a03,0x1bdb42,0x1c045b03,0x1c05db83,0x1d5cc2,0x1dd31c83,0x1dd39d03,0x1ede42,0x75e82,0x1fdf42,0x20431f03,0x2083df03]
def tableP164_1 : List Nat := [0x20449f83,0x20855f83,0x21e142,0x2207e103,0x22896103,0x220a6183,0x228b6183,0x23e342,0x24522303,0x2452a383,0x24d51403,0x1d9c6483,0x1794e503,0x255f1b03,0x255f9b83,0x19166583,0x25e11e03,0x26581683,0x26589703,0x22602603,0x26d99683,0x26da1703,0x1a97e683,0x2420e683,0x27599803,0x275a1883,0x1a996703,0x2422e703,1,257,0xac84703,0x1481,0x1601,0x1ad982,0x1ada02,0x1ddc82,0x1ddd02,0x205f02,0x205f82,0x246302,0x246382,0x24c1,0x1d9c42,0x17a502,0x192582,0x1ac1,0xa01,0x781,0x2201,0x2041,0x2601,0x25e2a103,0xb01,0x25e282,0x2441,0x1dc1,0x1c41,0x269f02,0x2681,0x275982,0x2741,0x1941,0x22c1,0x2581]

def encodedP164 (i : Nat) : Nat :=
  if i < 64 then
    tableP164_0.getD (i%64) 0
  else
    tableP164_1.getD (i%64) 0
def bookP164 (i : Nat) : Clause := let n := encodedP164 i; unpackLits 8 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClausesP164 : inputsOK 0 164 aP164 rP164 (baseBook bookP164 92).toList=true := by decide +kernel

def rowsP164_0 : List Nat := [513,0x20601,0x254c01,0x2e2b5802,0x2eae5e02,0x46601,0x56801,0x297201,0x2a7401,0x67c01,0x78001,0x279001,0x289201,0x16ab9402,0x699601,0x5f9801,0x609e01,0x31616402,0xf3634f103a05,0x113634e0e3e05,0x87177ee8404,0x33657a02,0x3871a602,0x13297921a7880c3b4266844240d,0x1640551974405,0x11b9f48403,0x34678e02,0x32637002,0x77d401,0x6e21a899afebebade36f6180c,0x1b086a2e7417be75d7ade3b6d140e,0x18b0b15397aa406,0x62c2cd565ef97aa208,0x36fcb402,0x3b7cb602,0x7dd801]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOkP164_0 : checkRows bookP164 7 92 rowsP164_0=true := by decide +kernel

def lastUnitsP164 := digits 7 2 0x3ffe
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflictP164 : checkReasons bookP164 128 117 lastUnitsP164 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem excludeP164 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 164=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=0) h hc bp eq (by decide +kernel)
  let v := truth Z aP164
  have hbase : ValidThrough v bookP164 92 := book_start Z h hc z eq _ _ _ _ initialClausesP164
  have h0 : ValidThrough v bookP164 128 := rows_sound hbase rowsP164_0 rowsOkP164_0
  exact book_end h0 _ _ conflictP164
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def aP177 := ([0x40001,0xc0001,0x3007,0x3002,0x4002,0x5002,0x5802,0x40041,0x40841,0x41041,0x60061,0x60861,0x61061,0x60081,0xc0081,0x3087,0xc00c1,0x400c1,0x600c1,0x50c3,0xc08c1,0x10c0,0x408c1,0x608c1,0x20c7,0x220c7,0x420c7,0x100101,0x5103,0x100901,0x1100,0x140141,0x940,0xc0141,0x100141,0x120141,0x160141,0x5943,0x180141,0x1a0141,0x140941,0x1140,0xc0941,0x100941,0x120941,0x160941,0x180941,0x1a0941,0x141141,0x101141,0x121141,0x161141,0x181141,0x1a1141,0xd147,0x2d147,0x4d147,0xf947,0x2f947,0x4f947,0x10147,0x30147,0x50147,0xe0148,0x8e0148,0x10e0148,0x2c0148,0xac0148,0x12c0148,0x382148,0xb82148,0x1382148,0x3a2148,0xba2148,0x13a2148,0x462148,0xc62148,0x1462148,0x3a2948,0xba2948,0x13a2948,0x422948,0xc22948,0x1422948,0x462948,0xc62948,0x1462948,0xc5009,0x105009,0x165009,0x100161,0x140161,0x1160,0x100961,0x140961,0x3967,0x23967,0x43967,5,0x40006,0xc0006,0x2805,0x22805,0x42805,0x42806,0x4005,0x24005,0x44005,0x64006,0x5005,0x5805,0x65806,0xc5806,0x8005,0x28005,0x48005,0x48006,0xc8006,0x9005,0x29005,0x49005,0x69006,0xc9006,37,0x20025,0x40025,0x2825,0x22825,0x42825,0x4025,0x24025,0x44025,0x5025,0x25025,0x45025,0x145026,0x5825,0x25825,0x45825,0x145826,0x8025,0x28025,0x48025,0x108026,0x9025,0x29025,0x49025,0x109026,0x2804,0x8004,0x80a4,0x5904,0x9104,0x5944,0x9164,0x9204] : List Nat).toArray.map readPackedFact
def rP177 := ([0x3005,0xc1009,0xc3009,64,0x840,0x1040,96,0x860,0x1060,0x3085,0xc1889,0xc3089,192,0x8c0,195,0x20c5,0x810c9,0x818c9,0x8810c9,0x8818c9,0x420c7,0x50ce,256,0x900,259,0x510d,320,0x940,0x941,0x1140,0xd145,0x346949,0xb46949,0x1344149,0xf945,0x3e5949,0xbe4149,0xbe6949,0x13e4149,0x13e6949,0x10145,0x403149,0x406149,0x406949,0xc03149,0xc06149,0xc06949,0x1406149,0x1406949,0xe0146,0x390014a,0x2390014a,0x10e0148,0x2c0146,0xb10014a,0xb16014a,0x2b10014a,0x2b16014a,0x4b10014a,0x4b16014a,0x382146,0xe0c214a,0xe1a214a,0x2e0c214a,0x2e1a214a,0x4e1a214a,0x3a2146,0xe90214a,0xe92214a,0x2e90214a,0x2e92214a,0x2e9a214a,0x13a2148,0x4e90214a,0x4e92214a,0x4e9a214a,0x462146,0x1198214a,0x3192214a,0x519a214a,0x3a2946,0xe90294a,0xe92294a,0x2e90294a,0x2e92294a,0x13a2948,0x422946,0x108c294a,0x1098294a,0x308c294a,0x3098294a,0x309a294a,0x5098294a,0x509a294a,0x462946,0x1190294a,0x1192294a,0x3190294a,0x3192294a,0x3196294a,0x5190294a,0x5192294a,0x5196294a,0x5198294a,0xc500c,0x80314f,0x10500b,0x10500c,0x80414f,0x100414f,0x102414f,0x16500c,0x8594d,0x80594f,0x100594f,0x102594f,355,0x3965,0xe4169,0xe5169,0x8e4169,0x8e5169,0x43967,16,0x1000012,0x3000012,0x2810,0x21002812,0x21022812,0x21042812,0x4010,0x21804012,0x21824012,0x21844012,0x5010,0x5810,0x1805812,0x3005812,0x8010,0x1008012,0x23008012,0x1028012,0x23028012,0x48011,0x9010,0x1809012,0x23009012,0x1829012,0x23029012,0x49011,48,0x40031,0x2830,0x42831,0x4030,0x44031,0x5030,0x25005032,0x25025032,0x25045032,0x5830,0x5005832,0x5025832,0x45831,0x8030,0x24008032,0x24028032,0x48031,0x9030,0x4009032,0x4029032,0x49031,0x10a0013,0xa0034,0x8a0034,0x3200013,0x200034,0xa00034,0x21202813,0x202834,0xa02834,0x21964013,0x164034,0x964034,0x21a44013,0x244034,0xa44034,0x165014,0x25165033,0x3245813,0x245834,0xa45834,0x248014,0xa48014,0x24248033] : List Nat).map readPackedScheme

def tableP177_0 : List Nat := [321,258,0x10102,961,0x441,0x4c1,0x541,0x5c1,0x641,0x7c1,0xd0782,0xe0782,0x841,0xa41,0x38a82,0x35198c43,0x110c02,0x120c02,0x160c82,0x170c82,0x158d02,0x27050183,0xdc1,0xec1,0x48f02,0xe41,0xfc1,0x1441,0x209482,0x1841,0x71379b43,0x271b02,0x2f1b82,0x311c02,0x773a9cc3,0x241c82,0x2b1d02,0x2f1d02,0x311d82,0x351d82,0x7d3d9e43,0x211e02,0x261e02,0x271e02,0x2a1e82,0x2e1e82,0x2f1e82,0x341f02,0x351f02,0x83409fc3,0x229f82,0x2ba002,0x29a082,0x8943a143,0x22a102,0x242102,0x2ba182,0x2d2182,0x31a202,0x332202,0x8f46a2c3,0x212282,0x27a282,0x2a2302]
def tableP177_1 : List Nat := [0x2fa302,0x35a382,0x9549a443,0x222402,0x232402,0x2b2482,0x2c2482,0x2fa482,0x29a502,0x312502,0x322502,0x35a502,0x9b4ca5c3,0x262582,0x2c2602,0x35a682,0xa14fa743,0x222702,0x23a702,0x2b2782,0x2ca782,0x29a802,0xa752a8c3,0x212882,0x26a882,0x2a2902,0x2ea902,0x2f2902,0x34a982,0x352982,0xad55aa43,0x222a02,0x23aa02,0x2b2a82,0x2caa82,0x2d2a82,0x312b02,0x32ab02,0x332b02,0x34ab02,0x32b82,0x2bcaa43200985,0x5ac02,0x42c02,0x2c4ae45200e05,0x2c4c645290e05,0x2c4c657290e05,0x62c82,0x12c1,0x2ccb649201285,0x2ccce49291285,0x2ccce5b291285,0x6ae02,0xc360afc3,0x5a2f82,0x5b2f82,0x5d3002,0x5e3002,0x5cb082,0x3141,0xc600b103,0xc801b103,0xcf66b2c3,0xd1073283]
def tableP177_2 : List Nat := [0xd1083303,0xd1093383,0xd76ab4c3,0xd90a3483,0xd90b3503,0xd90c3583,0x36c1,0x3741,0xde0db703,0xe00eb703,0xe772b8c3,0xe811b883,0xeb103883,0xe816b903,0xeb143903,0x15b982,0xf177bb43,0xf212bb03,0xf5103b03,0xf217bb83,0xf5143b83,0x15bc02,0xfb7cbdc3,0x1ebe82,0x1017fbf43,0x1ec002,0x10782c0c3,0x5cc182,0x10d85c243,0x10f1f4203,0x10f284283,0x10f304303,0x11589c443,0x1165bc403,0x1165ec483,0x5cc502,0x11d8dc643,0x11f1b4603,0x11f1d4683,0x1ec702,0x12591c843,0x1265ac803,0x1265dc883,0x5cc902,0xd063ca03,0x1297e3d83,0x1297f3e03,0xea64ca83,0x12b8c3d83,0x12b8d3e03,0xe9684b03,0x12d8c3f03,0x12d8d3f83,0xdf6c4b83,0x12f884083,0x12f894103,0xf36c4c03,0x131904083,0x131914103,0x1336e3683,0x117874c83,0xf470cd03,0x135904403,0x135914483]
def tableP177_3 : List Nat := [0x137763883,0x137773903,0x1278f4d83,1,129,0x681,0x701,0x16257229004,0x16263229484,0x162632b9484,0x1665b249004,0x16667249484,0x166672d9484,0x3181,0x3201,0x68b282,0x68b302,0x68b382,0x6cb482,0x6cb502,0x6cb582,0x3781,0x3801,0x75b882,0x75b902,0x7abb02,0x7abb82,0x87c202,0x87c282,0x87c302,0x8fc602,0x8fc682,0x684a02,0x754a82,0x6c4b82,0x4cc1,0x8bc382,0x7a4d02,0x3641,0x4b81,0x3441,0x4a01,0xb131a403,0x58ab02,0x58a482,0xb12b9143,0x5895c2,0x2c41,705,513,0xf01,0x3e81,0x4001,0x4701,0x2ccea85202505,0x16656429484,0x2b14c2,0x599582,0xb3292103,0x599482,0x2cc1,769,0x2e01,0x3081]
def tableP177_4 : List Nat := [0x4181,0x4501,0x4901,0x14c1,0x1041,0x63ea883,0x31a82,0x642a483,0x31e02,0x31e82,0x32902,385,0xa81,0xd01,0x3981,0x3c01,0x3d41,0x4d01,0x3ac1,0x4a81,0x43c1,0x45c1,0x934882,0x934802,0x4981,0x47c1,0x4d81,0xf2743b03,0x793a02,0x96c602,0x4b41,0x3a41,0x3c81,0x4c01,0x4481,0x4441,0x4081,0x4801,0x4141,0x48c1]

def encodedP177 (i : Nat) : Nat :=
  if i < 128 then
    if i < 64 then
      tableP177_0.getD (i%64) 0
    else
      tableP177_1.getD (i%64) 0
  else
    if i < 192 then
      tableP177_2.getD (i%64) 0
    else
      if i < 256 then
        tableP177_3.getD (i%64) 0
      else
        tableP177_4.getD (i%64) 0
def bookP177 (i : Nat) : Clause := let n := encodedP177 i; unpackLits 9 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClausesP177 : inputsOK 1 177 aP177 rP177 (baseBook bookP177 195).toList=true := by decide +kernel

def rowsP177_0 : List Nat := [513,0x401,0x241401,0x241601,0x64d801,0x64da01,0x64dc01,0x1c0e201,0x1c0e401,0x1c0e601,0x619ecf802,0x621ecfa02,0xcfe01,0x110001,0x150201,0x190601,0x1d0801,0x210a01,0x62a1d1002,0x6321d1202,0x311801,0x351c01,0x312401,0x352801,0x693a01,0x6d3c01,0x753e01,0x594a01,0x5d4c01,0x3355801,0x3395e01,0x3556a01,0x43a197602,0x38d7801,0x3597a01,0xd469b490403,0x399c401,0xd16833cfc03,0x3a1c001,0x1c140aa35293206c44218e8a60a,0x36281546a54648e08c45213a8943a32990a20f,0x1c18b1c645f2f188664622bac680b,0x7062c7190cc6805,0x24920844376bb19206,0x492410888602f978c2ee763ad900b,0x3bcd401,0x3bcd601,0x3c43001,0x3c92e01,0x3c93201,0x3c94e01,0x4639110d44e3a259259408,0x1ab30746632178c044213d8382422984720e,0x4428108aa482294ca407,0xbccb2f8dc6cf77c184cc08,0xcc6365b28be371b070bc08,0x44239804a5e1118c46cc6599092261d8e86afa1c3e48413,0x118a0422890c64312a92068fb19be4a80d,0x3f0de01,0x3f4e801,0x3f8f401,0x3f93601,0x3f94601,0x3f95601,0x8c50211448632188cdf055240d0a80c,0x40c3801,0xb054692c15cd015823c05009,0xa45a692d164ad052e8c0d015823c0500d,0x179585057149a47e3c1f07c3c211d0d4b62e100e08e45340548306823c0b81a,0x3f1f1a45629340548306823c0780b,0x3d201a45c2c340548306823c0780b,0x3d201a4b659340548306823c0780b,0x839106c602f978c44e26134b05633c28b82f14426104f25c188416,0x42c1c01,0x4302801,0x4311e01,0x4312a01,0xda6cc3d2003,0x441ca01,0xd86bc391403,0x449c201,0xdd6e36d3803,0x451c801,0x509d540785faaa23017fc54ee0a,0x511d540765f2a623017fc54f20a,0xa88b40a2e03,0xdf6f3d54803,0x8c4658402,0x2341e8a08b01230d874682409,0x1160f4504d82934846e1f1a87434200c,0x1309659ac1d2f479c4d5c08,0x984b2d162a48eba5e8f389bd55a0b,0x744796402,0x47e3801,0x734817002,0x2a134bf5bc86050088b9d7209]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOkP177_0 : checkRows bookP177 9 195 rowsP177_0=true := by decide +kernel

def rowsP177_1 : List Nat := [0x80c894002,0x73c8d6c02,0x88c8d7c02,0x804913402,0x814955002]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOkP177_1 : checkRows bookP177 9 291 rowsP177_1=true := by decide +kernel

def lastUnitsP177 := digits 9 3 0x4864f26
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflictP177 : checkReasons bookP177 296 186 lastUnitsP177 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem excludeP177 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 177=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=1) h hc bp eq (by decide +kernel)
  let v := truth Z aP177
  have hbase : ValidThrough v bookP177 195 := book_start Z h hc z eq _ _ _ _ initialClausesP177
  have h0 : ValidThrough v bookP177 291 := rows_sound hbase rowsP177_0 rowsOkP177_0
  have h1 : ValidThrough v bookP177 296 := rows_sound h0 rowsP177_1 rowsOkP177_1
  exact book_end h1 _ _ conflictP177
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def aP197 := ([1,0xa0001,0x1007,0x2802,0x4002,0x4802,0x5002,0x40041,65,0xc047,0xa00a1,0x40a3,0xa08a1,0x10a0,193,0x400c1,0xa00c1,0x10c7,0x20c7,0x100101,0x900,0xa0101,0x120101,0x4903,0x140101,0x5103,0x1a0101,0x100901,0x1100,0xa0901,0x120901,0x140901,0x160901,0x1a0901,0x101101,0xa1101,0x121101,0x141101,0x1a1101,0x4107,0x24107,0x44107,0xc107,0x2c107,0x4c107,0x3a0108,0xba0108,0x13a0108,0x341108,0xb41108,0x1341108,0x3a1108,0xba1108,0x13a1108,0x461108,0xc61108,0x1461108,0x2c3108,0xac3108,0x12c3108,0x463108,0xc63108,0x1463108,0xa4009,0x124009,0x144009,0x100121,0x140121,0x180121,0x1120,0x100921,0x140921,0x180921,0x3927,0x23927,0x43927,0x7127,0x27127,0x47127,0x140141,0x100141,0x180141,0x140941,0x1140,0x100941,0x180941,0x7147,0x27147,0x47147,0x8147,0x28147,0x48147,0x2c0148,0xac0148,0x12c0148,0x180181,0x180981,0x181181,5,6,0x805,0xa0806,0x2805,0x2806,0x42806,0x6805,0x26805,0x46805,0xa6806,0x7005,0x27005,0x47005,0xa7006,0x7805,0x27805,0x47805,0x8005,0x8006,0x48006,0x8805,0xa8806,37,0x20025,0x40025,0x100026,0x825,0x20825,0x40825,0x100826,0x2825,0x22825,0x42825,0x6825,0x26825,0x46825,0x146826,0x186826,0x7025,0x27025,0x47025,0x147026,0x187026,0x7825,0x27825,0x47825,0x187826,0x8025,0x28025,0x48025,0x108026,0x8825,0x28825,0x48825,0x108826,0x804,0x2804,0x8004,0x7024,0x80a4,0x71a4,0x79a4,0x89a4,0x79c4,0x8a04] : List Nat).toArray.map readPackedFact
def rP197 := ([0,0x1005,0x42809,64,0xc045,0x300049,160,0x8a0,163,0x40ae,0x10c5,0x428c9,0x20c5,0x800c9,0x810c9,256,0x900,0x901,0x1100,259,0x4105,0x104909,0x105109,0x904909,0x905109,0x1104909,0x1105109,0xc105,0x302909,0x306909,0xb02909,0xb06909,0x1302909,0x1306909,0x3a0106,0xe92010a,0xe94010a,0x2e92010a,0x2e94010a,0x4e92010a,0x4e94010a,0x341106,0xd0a110a,0xd1a110a,0x2d0a110a,0x2d1a110a,0x4d0a110a,0x4d1a110a,0x3a1106,0xe94110a,0x2e94110a,0x4e9a110a,0x461106,0x1194110a,0x3196110a,0x5194110a,0x2c3106,0xb14310a,0x2b16310a,0x4b14310a,0x463106,0x1192310a,0x1194310a,0x3194310a,0x5194310a,0x519a310a,0xa400c,0x80290f,0x100290f,0x102290f,0x12400c,0xc490d,0x80490f,0x100490f,0x102490f,0x14400c,0x510d,0x80510f,0x100510f,0x102510f,291,0x3925,0xe4129,0xe5129,0x8e4129,0x8e5129,0x43927,0x7125,0x1c4129,0x1c6129,0x9c4129,0x9c6129,0x47127,320,0x940,323,0x7145,0x1c4149,0x9c6149,0x47147,0x8145,0x206149,0xa04149,0x48147,0x2c0146,0xb10014a,0x2b18014a,0x12c0148,384,0x980,0x1180,16,0x20000012,0x810,0x2800812,0x2810,0x2812,0x21002812,0x6810,0x22806812,0x22826812,0x46811,0x7010,0x22807012,0x22827012,0x47011,0x7810,0x47811,0x8010,0x8012,0x1008012,0x8810,0x2808812,48,0x24000032,0x24020032,0x40031,0x24040032,0x830,0x4020832,0x40831,0x2830,0x42831,0x6830,0x5006832,0x6006832,0x5026832,0x6026832,0x46831,0x7030,0x25007032,0x6007032,0x25027032,0x6027032,0x47031,0x7830,0x26007832,0x26027832,0x26047832,0x8030,0x24008032,0x24028032,0x48031,0x24048032,0x8830,0x4008832,0x4028832,0x48831,0x20014,0x24020033,0x200a0013,0xa0034,0x8a0034,0x20200013,0x200034,0xa00034,0x29c0813,0x1c0834,0x21202813,0x202834,0xa02834,0x1c6814,0x9c6814,0x51c6833,0x1e6814,0x9e6814,0x61e6833,0x22a26813,0x226834,0xa26834,0x1e7014,0x9e7014,0x61e7033,0x228014,0x24228033] : List Nat).map readPackedScheme

def tableP197_0 : List Nat := [65,321,0x10102,961,0x4c1,0x80482,0x541,0x641,0x38682,0x17040183,0x8c1,0x100882,0x941,0xe0902,0xf0902,0x9c1,0xdc1,0x148e02,0x1141,0x48e02,0x532893c3,0x161382,0x181382,0x1e1402,0x1f1402,0x241482,0x251482,0x592b9543,0x151502,0x1a1502,0x1d1582,0x211582,0x231602,0x261602,0x5f2e96c3,0x161682,0x189682,0x1e1702,0x1f9702,0x241782,0x259782,0x65319843,0x151802,0x1a9802,0x1d1882,0x219882,0x231902,0x269902,0x6b3499c3,0x181982,0x1f1a02,0x269a82,0x71379b43,0x181b02,0x201b82,0x251c02,0x773a9cc3,0x181c82,0x209d02,0x251d82,0x7d3d9e43,0x169e02,0x181e02,0x1f1e82]
def tableP197_1 : List Nat := [0x251f02,0x261f02,0x31f82,0x1fc762b140585,0x1fc8e2b1c0585,0x1fc8e3b1c0585,0x52002,0xbc1,0x2047a2d140b85,0x204922d1c0b85,0x204923d1c0b85,0x62082,0xcc1,0x20c7e31140c85,0x20c96311c0c85,0x20c963f1c0c85,0x5a282,0x974aa4c3,0x422482,0x432482,0x462502,0x472502,0x45a582,0x9d4da643,0x422602,0x442602,0x462682,0x482682,0x45a702,0x27c1,0x2941,0x6a982,0xb157ab43,0x502b02,0x552b82,0x53ac02,0xb75aacc3,0x512c82,0x542d02,0x53ad82,0xbd5dae43,0x50ae02,0x552e82,0x53af02,0x2fc1,0x3041,0x30c1,0x3141,0xc7003103,0x3241,0xca01b203,0x3341,0xce08b303,0xd1073303,0xd76ab4c3,0xd90a3483,0xd90c3503,0xdb582,0xdf6eb6c3,0xe10a3683,0xe10c3703,0xdb782,0xe772b8c3,0xdb982]
def tableP197_2 : List Nat := [0x3a41,0xea0eba03,0xec0fba03,0x3bc1,0xf010bb83,0xf77abcc3,0xf9133c83,0xf91b3d03,0x1cbd82,0xf9223d83,0xff7ebec3,0x10054bf03,0x53bf82,0x10782c0c3,0x1cc182,0x10d85c243,0x10e43c203,0x11044c203,0x10e47c283,0x11048c283,0x45c302,0x1178ac4c3,0x1194f4483,0x11a51c483,0x119524503,0x11a55c503,0x53c582,0x1218fc743,0x1235f4703,0x123604783,0x123614803,0x12993c943,0x12b134903,0x12b1b4983,0x1cca02,0x12b224a03,0x13197cb43,0x13242cb03,0x13246cb83,0x45cc02,0x135643103,0x1017c4d03,0xcf634d83,0x137813c83,0x137823d03,0xeb634e03,0x139923c83,0x139933d03,0xe065ce83,0x13b893e83,0xed684f03,0x13d924083,0x13d934103,0x13f6d3483,0x13f6e3503,0x11887cf83,0x141713483,0x141723503,0x12288d003,0xf16c5083,0x143964203,0x143974283,0x145713683,0x145723703]
def tableP197_3 : List Nat := [0x1228dd103,0x147773a03,0x133955183,129,0x401,0x801,0x701,0x781,0x1023d168a04,0x10249168e04,0x102491e8e04,0x1063f188a04,0x1064b188e04,0x1064b1f8e04,0x31c1,0x3281,0x3381,0x3441,0x6cb482,0x6cb502,0x70b682,0x70b702,0x3a81,0x3b01,0x3c01,0x7cbc82,0x7cbd02,0x7cbd82,0x8cc482,0x8cc502,0x91c702,0x91c782,0x91c802,0x95c902,0x95c982,0x95ca02,0x4d41,0x80be02,0x4d81,0x813c82,0x823d02,0x4e01,0x923c82,0x933d02,0x704e82,0x4f01,0x924082,0x934102,0x6c5082,0x51c1,0x99ca82,0x38419f03,0x38418c43,0x1c20c2,0x250c02,0x10238299244,0x811c1283,0x811c1383,0x811c1403,0x408e02,0x1cc982,0xe41,0xa41,577]
def tableP197_4 : List Nat := [0x20c1,0x2041,769,641,0x2981,0x2281,0x2c01,0x2d81,0x2f01,0x3f81,0x4581,0x2581,0x2701,0x4301,0x4c01,0x2a81,0x62c9883,0x62c9803,0x31642,385,0x681,0x3581,0x3781,0x3981,0x3641,0x5081,0x3841,0x4e81,0x4641,0x132874b83,0x994382,0x48c1,0x3e41,0x4041,0x8d4482,0x4681,0x5101,0x13fa0b903,0x9fd042,0x994b02,0x4c81,0x4a81,0x4901,0x4981,0x4a01]

def encodedP197 (i : Nat) : Nat :=
  if i < 128 then
    if i < 64 then
      tableP197_0.getD (i%64) 0
    else
      tableP197_1.getD (i%64) 0
  else
    if i < 192 then
      tableP197_2.getD (i%64) 0
    else
      if i < 256 then
        tableP197_3.getD (i%64) 0
      else
        tableP197_4.getD (i%64) 0
def bookP197 (i : Nat) : Clause := let n := encodedP197 i; unpackLits 9 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClausesP197 : inputsOK 1 197 aP197 rP197 (baseBook bookP197 195).toList=true := by decide +kernel

def rowsP197_0 : List Nat := [0x40401,0x100a01,0x281601,0x301a01,0x301c01,0x11c9001,0x11c9201,0x11c9401,0x1309a01,0x1309c01,0x1309e01,0x1bce002,0x619c4e402,0x621cce802,0x19ccea02,0x18ee01,0x1cf001,0x18f601,0x1cf801,0x632010202,0x63a010402,0x62a0d0802,0x3d0c01,0x410e01,0x491201,0x1752c01,0x1793001,0x1b13801,0x1b53a01,0x1b93c01,0x3d4001,0x414201,0x494601,0x389bd5002,0x3915201,0x683395402,0x3995601,0x3995801,0x6b3395a02,0x3a55c01,0x3a55e01,0x33d6001,0x6bb456402,0x3b56601,0x3b56801,0x3617601,0x41a018202,0x3c58401,0x31190cd98cd209006007,0xa8f0281a1f86198cb08bcc7a0a,0xd870341d8dd9a3f1e0f872357a3cc740d,0x361c0d072351b8ec7407,0x2a1764b282804,0x2a18640984a2213bdc48f60d044280c,0x4a24640582a11143e04408,0x4626640602e11143e04408,0x1189592ca0c851f4f9143e0440a,0x46a15deeb44239ce06,0x2350aee7527df8a247221d009,0x3f42201,0x3f42601,0x3f5ea01,0x3f5f601,0x4009601,0x4048c01,0x408be01,0x40ca001,0x410c601,0x410ce01,0x410d601,0x4111801,0x4113401,0x414ac01,0x414b801,0x4152801,0x4154e01,0x6134180d46284418d207,0x703e43168b084097f3fc3609,0x783a43158a884097f3fc3609,0x381e221145c2988c4084097ebfc360c,0x542c179108a211044812427ebfc520c,0x44c1001,0x450f201,0x450fa01,0x450fe01,0xd369454ec03,0x461e001,0xd56a458f403,0x469d801,0xdd6e4292a03,0x240a28f2a2f54d0b86c64a609,0x124514794978a5524761d1986c2caa0c,0xe06fb793603,0x856db65b403,0x481ca01,0x45991146558a5e370983c84cc0a]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOkP197_0 : checkRows bookP197 9 195 rowsP197_0=true := by decide +kernel

def rowsP197_1 : List Nat := [0x12a998543e4404,0x8fc8d8002,0x7a3b2fd73168ac916a07,0x3d1d97cb83f4962f248ac596c0a,0x932ba3cb0bc52aea4cb78f4321b198fc70b60f,0x4895d1e5a5ea9949275d4996f1e86436330e8fc70b212,0x4a1e401,0x4a5c201,0x4a5c401,0x4a5c601]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOkP197_1 : checkRows bookP197 9 291 rowsP197_1=true := by decide +kernel

def lastUnitsP197 := digits 9 3 0x4ae592a
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflictP197 : checkReasons bookP197 301 159 lastUnitsP197 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem excludeP197 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 197=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=1) h hc bp eq (by decide +kernel)
  let v := truth Z aP197
  have hbase : ValidThrough v bookP197 195 := book_start Z h hc z eq _ _ _ _ initialClausesP197
  have h0 : ValidThrough v bookP197 291 := rows_sound hbase rowsP197_0 rowsOkP197_0
  have h1 : ValidThrough v bookP197 301 := rows_sound h0 rowsP197_1 rowsOkP197_1
  exact book_end h1 _ _ conflictP197
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def aP266 := ([0xa0021,0xc0021,0x827,0xa00a1,0xa08a1,0xc00c1,0x400c1,0xa00c1,0xc08c1,0x408c1,0xa08c1,0x48c7,0x248c7,0x40c8,0x8040c8,0x1805,0xa1806,0xc1806,0x6805,0x26805,0xa6806,0x8805,0x28805,0xa8806,0xc8806,0x1825,0x21825,0x6825,0x26825,0x8825,0x28825,0x6864,0x8864,0x89a4] : List Nat).toArray.map readPackedFact
def rP266 := ([0x825,0x22829,0x23029,160,0x8a0,192,0x8c0,0x48c5,0x1210c9,0x1228c9,0x9210c9,0x9228c9,0x40c6,0x440ca,0xa40ca,0x200440ca,0x200a40ca,0x1810,0x2801812,0x3001812,0x6810,0x22806812,0x22826812,0x8810,0x2808812,0x23008812,0x2828812,0x23028812,0x1830,0x6830,0x8830,0x29a1813,0x1a1834,0x9a1834,0x3221813,0x221834,0xa21834,0x22a26813,0x226834,0xa26834] : List Nat).map readPackedScheme

def tableP266_0 : List Nat := [321,258,0x4102,449,577,705,0x441,0x325c2,0x18582,0x1c582,0x24602,0x28602,0x3a6c2,0x1a682,0x1c682,0x26702,0x28702,0x7c1,0x2002783,0x2206783,0x4e942,0x290c903,0x2910983,0x5aac2,0x2e1ea83,0x3114a83,0x2e2ab03,0x3120b03,0x6acc2,0x72dc2,0x7aec2,0x2842f83,0x3f6cc83,0x3f70d03,0x3047003,0x4174c83,0x4178d03,0x2f51083,0x4374d83,0x4378e03,1,129,0x801,0x881,0x52902,0x52982,0x62a82,0x62b02,0x50f82,0x61002,0xc41,0x1001,0xa41,0xf81,897,0x501,0xb81,0x1081,0xf01,0xec1,0xc81,0xd81,0xd41,0xe41]

def encodedP266 (i : Nat) : Nat :=
  tableP266_0.getD (i%64) 0
def bookP266 (i : Nat) : Clause := let n := encodedP266 i; unpackLits 7 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClausesP266 : inputsOK 0 266 aP266 rP266 (baseBook bookP266 40).toList=true := by decide +kernel

def rowsP266_0 : List Nat := [513,0x401,0x508a402,0x528a602,0x1aa01,0x22c01,0x2b201,0x33601,0x153e01,0x15c401,0x5f72e02,0x196201,0x5b62802,0x1a6001,0x51839c49e05,0x4183a059a05,0x34c6fb2e04,0x69c4a02,0xeb93c9af39c007,0x1d3c01,0x67dc602,0x73dcc02,0x1e3801,0x1eba01]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOkP266_0 : checkRows bookP266 6 40 rowsP266_0=true := by decide +kernel

def lastUnitsP266 := digits 6 3 0x35ffe
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflictP266 : checkReasons bookP266 64 33 lastUnitsP266 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem excludeP266 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 266=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=0) h hc bp eq (by decide +kernel)
  let v := truth Z aP266
  have hbase : ValidThrough v bookP266 40 := book_start Z h hc z eq _ _ _ _ initialClausesP266
  have h0 : ValidThrough v bookP266 64 := rows_sound hbase rowsP266_0 rowsOkP266_0
  exact book_end h0 _ _ conflictP266
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def aP298 := ([0x3002,0x4802,0x5802,0x6802,0x20021,0xc0021,0x827,0x200a1,0xc00a1,0x30a7,0xc00c1,0x48c3,0xc08c1,0x10c0,0xc10c1,0xe00e1,0xe08e1,0xe10e1,0x120101,0x160101,0x2107,0x4907,0x120121,0x920,0xc0121,0xe0121,0x5923,0x180121,0x1a0121,0x6923,0x120921,0x1120,0xc0921,0xe0921,0x180921,0x1a0921,0x121121,0xc1121,0xe1121,0x181121,0x1a1121,0x6927,0x26927,0x46927,0xc127,0x2c127,0x4c127,0x10127,0x30127,0x50127,0x442928,0xc42928,0x1442928,0xc4809,0x1a4809,0x160161,0x960,0xe0161,0x120161,0x160961,0x1160,0xe0961,0x120961,0x180961,0xe1161,0x121161,0x7967,0x27967,0x47967,0x281968,0xa81968,0x1281968,0x461968,0xc61968,0x1461968,0x125809,0xc01a1,0xe01a1,0x11a0,0xc09a1,0xe09a1,0x1209a1,0x9a7,0x209a7,0x409a7,0x79a7,0x279a7,0x479a7,0x3209a8,0xb209a8,0x13209a8,0x1005,0x1805,0x21806,0xc1806,0x2005,0x6805,0x26806,0xc6806,0x8005,0x28005,0x48005,0x8805,0x28805,0x48805,0xc8806,0x9005,0x29005,0x49005,0x1025,0x21025,0x41025,0xe1026,0x1825,0x21825,0x41825,0xc1826,0xe1826,0x121826,0x2025,0x22025,0x42025,0xc2026,0xe2026,0x122026,0x6825,0x26825,0x46825,0x8025,0x128026,0x168026,0x8825,0x28825,0x48825,0x128826,0x9025,0x29025,0x49025,0x129026,0x169026,0x1844,0x2044,0x2064,0x6864,0x8864,0x89a4,0x8a04,0x9204,0x9224] : List Nat).toArray.map readPackedFact
def rP298 := ([32,0x825,0x23029,0x30a5,0xc08a9,0xc30a9,192,0x8c0,0x10c0,195,0x48ce,224,0x8e0,0x10e0,0x2105,0x84909,0x4905,0x125909,288,0x920,0x921,0x1120,291,0x6925,0x1a3129,0x1a3929,0x9a3129,0x9a3929,0x9a6129,0x11a3129,0x11a3929,0x11a6129,0xc125,0x306929,0xb03129,0xb06929,0x1303129,0x10125,0x403929,0x406129,0xc06129,0xc06929,0x1406929,0x442926,0x1118292a,0x111a292a,0x310e292a,0x3118292a,0x311a292a,0x5118292a,0x511a292a,0xc480c,0x80312f,0x100312f,0x102312f,0x592e,0x1a480c,0x2692d,0x80692f,0x100692f,0x102692f,352,0x960,0x961,355,0x7965,0x1e3969,0x1e4969,0x9e3969,0x9e4969,0x9e6169,0x47967,0x11e3969,0x11e4969,0x281966,0xa0e196a,0xa12196a,0x2a12196a,0x2a18196a,0x1281968,0x461966,0x118e196a,0x1192196a,0x318e196a,0x3192196a,0x518e196a,0x5192196a,0x12580c,0x80496f,0x100496f,0x102496f,419,0x9a5,0x239a9,0x8239a9,0x409a7,0x79a5,0x1e39a9,0x9e49a9,0x479a7,0x3209a6,0xc8c09aa,0xc8e09aa,0x2c8c09aa,0x2c8e09aa,0x13209a8,0x1010,0x1810,0x20801812,0x3001812,0x2010,0x6810,0x806812,0x3006812,0x8010,0x48011,0x8810,0x23008812,0x23028812,0x48811,0x23048812,0x9010,0x49011,0x1030,0x23801032,0x23821032,0x23841032,0x1830,0x23001832,0x3801832,0x24801832,0x23021832,0x3821832,0x24821832,0x41831,0x23041832,0x3841832,0x24841832,0x2030,0x3002032,0x3802032,0x3022032,0x4822032,0x42031,0x6830,0x46831,0x8030,0x4808032,0x5808032,0x8830,0x24808832,0x24828832,0x48831,0x24848832,0x9030,0x4809032,0x25809032,0x4829032,0x25829032,0x49031,0x61014,0x23861033,0x81014,0x23881033,0x81814,0x23081833,0x24881833,0x209a1813,0x1a1834,0x9a1834,0x3221813,0x221834,0xa21834,0x3226813,0x226834,0xa26834,0x228014,0xa28014,0x4a28033,0x248014,0xa48014,0x5a48033,0x248814,0xa48814,0x24a48833] : List Nat).map readPackedScheme

def tableP298_0 : List Nat := [577,833,0x50302,0x4c1,0x70482,0x80482,0x541,0x641,0x741,0x8682,0x17010003,0x7c1,0x841,0x8c1,0xa41,0x120a02,0xac1,0x130a82,0xb41,0xf41,0x178f82,0x1241,0x18f82,0x572a94c3,0x181482,0x191482,0x201502,0x211502,0x221502,0x251582,0x261582,0x271582,0x5d2d9643,0x1c1602,0x201682,0x231682,0x251702,0x633097c3,0x191782,0x1b1782,0x221802,0x231802,0x281882,0x69339943,0x1b9902,0x1c1902,0x211982,0x229982,0x231982,0x279a02,0x281a02,0x1a82,0x1ac8231170585,0x1ac96311f0585,0x1ac96411f0585,0x35020083,0x31b02,0xec1,0x1b48e39170e85,0x1b4a2391f0e85,0x1b4a2471f0e85,0x1bc1,0x1dc1,0x389e02]
def tableP298_1 : List Nat := [0x29e02,0x8943a143,0x392102,0x3a2102,0x3d2182,0x3e2182,0x3f2182,0x3ca202,0x402202,0x412202,0x8f46a2c3,0x39a282,0x3a2282,0x3e2302,0x3fa302,0x3ca382,0x9549a443,0x39a402,0x3a2402,0x3da482,0x3e2482,0x40a502,0x412502,0x12582,0x25cfa75380d05,0x25d06753c0d05,0x25d067d3c0d05,0x3a702,0xa953a943,0x4d2902,0x502982,0x4eaa02,0xaf56aac3,0x4d2a82,0x512b02,0x4eab82,0xb559ac43,0x4c2c02,0x4dac02,0x4f2c82,0x50ac82,0x4ead02,0x2dc1,0x2e41,0xbb042e03,0xbc05ae03,0x2fc1,0x3041,0xc207b003,0xc408b003,0xcb64b1c3,0xdb282,0xd167b343,0xd30a3303,0xd30c3383,0xdb402,0xd30e3403,0xd96bb543,0xdb602,0xdf6eb6c3,0xe10f3683,0xe1103703,0xe1113783,0xe772b8c3]
def tableP298_2 : List Nat := [0xe9183883,0xea19b883,0xed163883,0xe9203903,0xea21b903,0xed1e3903,0x1fb982,0xe9253983,0xea26b983,0xed243983,0xf378bbc3,0xf44cbb83,0xf64dbb83,0xf44fbc03,0xf851bc03,0x4ebc82,0xff7ebec3,0x1fbf82,0x4041,0x10212c003,0x10413c003,0x10b84c1c3,0x10d164183,0x10d1e4203,0x1fc282,0x10d244283,0x11388c3c3,0x1143ac383,0x117374383,0x1143ec403,0x1173b4403,0x3cc482,0x1195c2d83,0xeb704603,0x11b5f2d83,0xf7704683,0x11d5f2e03,0xf5744703,0xf9764703,0xc35d4783,0x11f7d3883,0x11f7e3903,0xd25ec803,0x121833883,0x121843903,0xd262c883,0x123833e83,0x123843f03,0x125663183,0x125673203,0x10c81c903,0x1276a3183,0x1276b3203,0x11682c983,0x1296a3303,0x1296b3383,0x115864a03,641,897,0x401,0x901,0x981,0xda471c8b84,0xda511c8f84]
def tableP298_3 : List Nat := [0xda51238f84,0x2ec1,0x2f01,0x3081,0x3101,0x69b302,0x69b382,0x69b402,0x70b682,0x70b702,0x70b782,0x76b882,0x76b902,0x76b982,0x4081,0x4101,0x86c182,0x86c202,0x86c282,0x8bc382,0x8bc402,0x4641,0x75b802,0x46c1,0x7bb802,0x4741,0x7aba02,0x7cbb02,0x4781,0x7d3882,0x7e3902,0x694802,0x694882,0x864902,0x8b4982,0x4341,0x4901,0x34c1,0x4801,0x4881,0x78012503,0x1c12e344aa105,0x1c12e344aa185,0x3c0082,0x1fc182,0x1fc202,0xfc1,0xbc1,193,0x1e01,0x2201,0x2381,0x4481,0x8a2102,0x4501,0x4a01,0x570012c3,0x368e42,0x6d2b8003,0x1270db583,0x9386c2,0x3841,0x3ac1,0x3e15eb57a3c05]
def tableP298_4 : List Nat := [0xf854abd6af37b3d07,0x3dc1,0x3982,0x3e1e8b557a745,0x339b43,0x3902,0xc42,0x2742,1,0x681,0x49c1,0x4581,0x4381,0x4401]

def encodedP298 (i : Nat) : Nat :=
  if i < 128 then
    if i < 64 then
      tableP298_0.getD (i%64) 0
    else
      tableP298_1.getD (i%64) 0
  else
    if i < 192 then
      tableP298_2.getD (i%64) 0
    else
      if i < 256 then
        tableP298_3.getD (i%64) 0
      else
        tableP298_4.getD (i%64) 0
def bookP298 (i : Nat) : Clause := let n := encodedP298 i; unpackLits 9 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClausesP298 : inputsOK 1 298 aP298 rP298 (baseBook bookP298 185).toList=true := by decide +kernel

def rowsP298_0 : List Nat := [0x40401,0xc0801,0xc0a01,0x381e01,0x402201,0xe47401,0xe47601,0xe47801,0x1acd802,0x5c9acda02,0x5d1bce002,0x5d9bce202,0x18ea01,0x1cec01,0x20f001,0x2cf801,0x30fa01,0x34fc01,0x490401,0x4d0a01,0x551201,0x5e2492602,0x5ea492802,0x492c01,0x4d2e01,0x553201,0xf53801,0xf93c01,0x359a94002,0x3554201,0x371a94402,0x35d4601,0x371ad4802,0x3654a01,0x3654c01,0x61b054e02,0x3715001,0x3715201,0x3095401,0x3115a01,0x3396401,0x33d6a01,0xd268b412a03,0x38dc201,0xc763314e803,0x395be01,0x395c001,0x2290cb45924158aa571b900820a,0x140b05121908a805,0x140b05322910a405,0x150a45a2c92482ea74ba06e571f900a00d,0x1207f572ad0c9173b99bc08,0x1207f57ab10c9173b99ba08,0x9876bb12a03,0x3b82801,0x3b82c01,0x3c1d601,0x3c48e01,0x3c49e01,0x3c53e01,0x135344a4d92c86427a3cd3a09,0x1364a4d1393a4622905eaf37a3c8980c,0x71bd97002,0x301a1a8d8660a773c02e08,0x2715894642a180a57ebe77bb8580b,0x382b0b8c830c01a08c4420123e01433108b5f2ee77bc05e14,0xe8725bad0e677723dd6008,0x74392d966797d9e8ee73723dd620b,0xca64b20f603,0x3f5ac01,0x6630190c46747234c207,0x1a0b8642e995188b453fcbc09,0x3f5b001,0x1b48f3498cbe5b438e1f0fa0f221b6cd80bfa0010,0x8f2fc060003,0xac3e2d7d3e46205,0xe8606c3441b6a00694798cbe5b1c4105c1b6da119833053b9df017f3c02e1a,0x1a0e8d06a3305065027f82c09deee7f3c02e0f,0x3498db6cb6d2020c7f82c0a060a,0x4ac0140c05f041c16e0e26409fe0b02773f85410,0x4201201,0x425f801,0x429c401,0x42da601,0x42da801]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOkP298_0 : checkRows bookP298 9 185 rowsP298_0=true := by decide +kernel

def lastUnitsP298 := digits 9 3 0x3d2190d
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflictP298 : checkReasons bookP298 270 154 lastUnitsP298 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem excludeP298 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 298=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=1) h hc bp eq (by decide +kernel)
  let v := truth Z aP298
  have hbase : ValidThrough v bookP298 185 := book_start Z h hc z eq _ _ _ _ initialClausesP298
  have h0 : ValidThrough v bookP298 270 := rows_sound hbase rowsP298_0 rowsOkP298_0
  exact book_end h0 _ _ conflictP298
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def aP400 := ([0x120101,0x160101,0x2107,0x4907,0x120121,0x120921,0x160161,0x120161,0x140161,0x160961,0x120961,0x140961,0x4167,0x24167,0x2e2168,0xae2168,0x8005,0x28005,0x8805,0x28805,0x9005,0x29005,0x8025,0x128026,0x168026,0x8825,0x28825,0x128826,0x9025,0x29025,0x129026,0x169026,0x8a04,0x9204,0x9224] : List Nat).toArray.map readPackedFact
def rP400 := ([0x2105,0x84909,0x4905,0x125909,288,0x920,352,0x960,0x4165,0x104969,0x105169,0x904969,0x905169,0x2e2166,0xb92216a,0xb94216a,0x2b92216a,0x2b94216a,0x8010,0x8810,0x9010,0x8030,0x4808032,0x5808032,0x8830,0x24808832,0x24828832,0x9030,0x4809032,0x25809032,0x4829032,0x25829032,0x228014,0xa28014,0x4a28033,0x248014,0xa48014,0x5a48033,0x248814,0xa48814,0x24a48833] : List Nat).map readPackedScheme

def tableP400_0 : List Nat := [321,258,449,0x4182,577,705,833,0x4c1,0x36642,0x1c602,0x20602,0x28682,0x2c682,0x3e742,0x1c702,0x22702,0x28782,0x2e782,0x46842,0x4e942,0x56a42,0xb41,0x2e02b03,0x3006b03,0x6acc2,0x3710c83,0x3714d03,0x76e42,0x3c1ee03,0x3f18e03,0x3c2ae83,0x3f24e83,0x4148803,0x414c883,0x365f003,0x4350803,0x4354883,0x3e63083,0x4550903,0x4554983,0x3d6d103,1,129,0xb81,0xc01,0x6ec82,0x6ed02,0x7ee02,0x7ee82,0x6d002,0x7d082,0xfc1,0x1081,0xdc1,0x1001,897,0x501,0xf01,0x1101,0xa81,0xa41,0x801,0x901,0x8c1]
def tableP400_1 : List Nat := [0x9c1]

def encodedP400 (i : Nat) : Nat :=
  if i < 64 then
    tableP400_0.getD (i%64) 0
  else
    tableP400_1.getD (i%64) 0
def bookP400 (i : Nat) : Clause := let n := encodedP400 i; unpackLits 7 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClausesP400 : inputsOK 0 400 aP400 rP400 (baseBook bookP400 41).toList=true := by decide +kernel

def rowsP400_0 : List Nat := [513,0x20601,0x14952c02,0x15152e02,0x43201,0x53401,0x63a01,0x73e01,0x2b4401,0x2c4a01,0x182f3602,0x336401,0x172d3002,0x356201,0xc1a207092205,0xa1a2080b1e05,0x3c71c373604,0x1ab95002,0x4c92748d9d344007,0x3b2801,0x1a3c4602,0x1d3c4c02,0x3d2401,0x3e2601]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOkP400_0 : checkRows bookP400 7 41 rowsP400_0=true := by decide +kernel

def lastUnitsP400 := digits 7 3 0xd9fc0
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflictP400 : checkReasons bookP400 65 33 lastUnitsP400 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem excludeP400 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 400=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=0) h hc bp eq (by decide +kernel)
  let v := truth Z aP400
  have hbase : ValidThrough v bookP400 41 := book_start Z h hc z eq _ _ _ _ initialClausesP400
  have h0 : ValidThrough v bookP400 65 := rows_sound hbase rowsP400_0 rowsOkP400_0
  exact book_end h0 _ _ conflictP400
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def aP416 := ([0x120101,0x160101,0x2107,0x4907,0x120121,0x920,0x140121,0x5123,0x160121,0x180121,0x120921,0x140921,0x160921,0x180921,0x8927,0x28927,0x9927,0x29927,0xa927,0x2a927,0x282928,0xa82928,0x160161,0x160961,0x8005,0x28005,0x8805,0x28805,0x9005,0x29005,0x8025,0x128026,0x168026,0x8825,0x28825,0x128826,0x168826,0x9025,0x29025,0x169026,0x8a04,0x9204,0x9224] : List Nat).toArray.map readPackedFact
def rP416 := ([0x2105,0x84909,0x4905,0x125909,288,0x920,0x8925,0x226129,0xa25129,0x9925,0x265929,0xa66129,0xa925,0x2a5129,0xaa5929,0x282926,0xa16292a,0xa18292a,0x2a16292a,0x2a18292a,0xa512d,0x80512f,352,0x960,0x8010,0x8810,0x9010,0x8030,0x4808032,0x5808032,0x8830,0x24808832,0x5808832,0x28831,0x24828832,0x5828832,0x9030,0x25809032,0x25829032,0x228014,0xa28014,0x4a28033,0x248014,0xa48014,0x5a48033,0x248814,0xa48814,0x5a48833] : List Nat).map readPackedScheme

def tableP416_0 : List Nat := [321,258,449,0x4182,577,0x541,0x3e742,0x24702,0x2c782,0x46842,0x20802,0x34882,0x4e942,0x18902,0x30982,0x56a42,0x20a02,0x26a02,0x30a82,0x36a82,961,0xb8d14384,0xb41,0xbc1,0x66c42,0x6ed42,0x76e42,0xf41,0x3e02f03,0x4006f03,0x8b0c2,0x4711083,0x4823083,0x17102,0x4729103,0x4833103,0x9b2c2,0x4f59283,0x4f5d303,0x5168c03,0x516cc83,0x467f403,0x5370c03,0x5374c83,0x4e83483,0x5570d03,0x5574d83,0x4e93503,1,129,0x171a283,0xf81,0x1001,0x8f082,0x8f102,0x9f282,0x9f302,0x8d402,0x9d482,0x13c1,0x1481,0x11c1,0x1401,0x401]
def tableP416_1 : List Nat := [0x1201,0x1501,0xe81,0xe41,0xc01,0xd01,0xcc1,0xdc1]

def encodedP416 (i : Nat) : Nat :=
  if i < 64 then
    tableP416_0.getD (i%64) 0
  else
    tableP416_1.getD (i%64) 0
def bookP416 (i : Nat) : Clause := let n := encodedP416 i; unpackLits 7 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClausesP416 : inputsOK 0 416 aP416 rP416 (baseBook bookP416 48).toList=true := by decide +kernel

def rowsP416_0 : List Nat := [513,0x20601,0x142a01,0x181b3802,0x189b3a02,0x43e01,0x54401,0x164a01,0x174c01,0x335201,0x345801,0x1c374802,0x3b7401,0x1b353c02,0x3d7201,0xb1e2480a2605,0x407644468f1848723427903f0c0e,0x1dc05e02,0x64c2e56fa0bc4e07,0x423401,0x1e435402,0x20c35a02,0x443001,0x453201]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOkP416_0 : checkRows bookP416 7 48 rowsP416_0=true := by decide +kernel

def lastUnitsP416 := digits 7 3 0xfa3c6
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflictP416 : checkReasons bookP416 72 40 lastUnitsP416 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem excludeP416 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 416=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=0) h hc bp eq (by decide +kernel)
  let v := truth Z aP416
  have hbase : ValidThrough v bookP416 48 := book_start Z h hc z eq _ _ _ _ initialClausesP416
  have h0 : ValidThrough v bookP416 72 := rows_sound hbase rowsP416_0 rowsOkP416_0
  exact book_end h0 _ _ conflictP416
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def aP432 := ([1,0x801,0x1001,0x3002,0x5002,0x5802,0x60061,0x60861,0x61061,0x80081,129,0x60081,0xc0081,0x3087,0x4887,161,0x800a1,0x20a7,0xc00c1,0x8c0,193,0x400c1,0x600c1,0x1400c1,0x50c3,0xc08c1,0x10c0,0x408c1,0x608c1,0x1408c1,0x410c1,0x1410c1,0x20c7,0x220c7,0x420c7,0x40c7,0x240c7,0x440c7,0x40c8,0x8040c8,0x10040c8,0x2440c8,0xa440c8,0x12440c8,0x143009,0x940,0x120141,0x160141,0x5943,0x1140,0x160941,0x180941,0x121141,0x161141,0x9947,0x29947,0x49947,0x11147,0x31147,0x51147,0x2a2948,0xaa2948,0x12a2948,0x462948,0xc62948,0x1462948,0x165009,0x1160,0x805,0x20805,0x40805,0x806,0x4005,0x24005,0x44005,0x64006,0x5005,0x5006,0x85006,0x5805,0x65806,0xc5806,0x7005,0x7006,0x87006,0x9005,0x29005,0x49005,0x69006,0xc9006,0x825,0x20825,0x40825,0x4025,0x24025,0x44025,0x5025,0x25025,0x45025,0x5825,0x25825,0x45825,0x7025,0x27025,0x47025,0x9025,0x29025,0x49025,0x5024,0x7024,0x5904,0x9104,0x7144,0x9164] : List Nat).toArray.map readPackedFact
def rP432 := ([0,0x800,0x1000,96,0x860,0x1060,128,0x3085,0xc1889,0xc3089,0x4885,0x120089,0x20a5,0x800a9,0x820a9,192,0x8c0,0x8c1,195,0x20c5,0x800c9,0x818c9,0x8810c9,0x8818c9,0x420c7,0x40c5,0x1010c9,0x1050c9,0x9010c9,0x9050c9,0x11010c9,0x11050c9,0x40c6,0x40ca,0x640ca,0x200440ca,0x200640ca,0x10040c8,0x2440c6,0x90440ca,0x91440ca,0x290440ca,0x291440ca,0x490440ca,0x491440ca,0x14300c,0x50ce,0x8050cf,0x10050cf,0x10250cf,0x941,323,0x9945,0x265949,0xa66149,0x1265949,0x11145,0x444949,0x445949,0xc45949,0x1444949,0x1445949,0x2a2946,0xa96294a,0x2a98294a,0x4a96294a,0x462946,0x1192294a,0x1196294a,0x3196294a,0x5192294a,0x5196294a,0x16500c,0x8594d,0x80594f,0x100594f,0x102594f,355,0x810,0x20000812,0x20020812,0x20040812,0x4010,0x21804012,0x21824012,0x21844012,0x5010,0x5012,0x22005012,0x5810,0x1805812,0x3005812,0x7010,0x7012,0x2007012,0x9010,0x1809012,0x23009012,0x1829012,0x23029012,0x49011,0x830,0x40831,0x4030,0x44031,0x5030,0x45031,0x5830,0x45831,0x7030,0x47031,0x9030,0x49031,0x20140813,0x140834,0x940834,0x201c0813,0x1c0834,0x9c0834,0x21964013,0x164034,0x964034,0x21a44013,0x244034,0xa44034,0x221c5013,0x1c5034,0x9c5034,0x3245813,0x245834,0xa45834] : List Nat).map readPackedScheme

def tableP432_0 : List Nat := [65,193,321,833,961,0x441,0x4c1,0x6c1,0x58682,0x60682,0x741,0x50702,0x8c1,0x78882,0x80882,0x941,0xcc1,0x9cd02,0x1cd02,0x1150d043,0xa1002,0xb1002,0xd9082,0xe1082,0xd5102,0x12d251c3,0xa9182,0xb9182,0xd9202,0xe9202,0xf1282,0xf9282,0x1453d343,0xa5302,0xb1302,0xdd382,0xe1382,0xd5402,0x15d554c3,0xad482,0xb9482,0xdd502,0xe9502,0xf5582,0xf9582,0x21602,0xc420183,0x164ecbc98c05,0x164fcbcd0c05,0x164fcecd0c05,0x16d882,0x25882,0x1c5bdb43,0x179b02,0x199b82,0x1a9c02,0x1ddd5cc3,0x171c82,0x179c82,0x191d02,0x1a1d82,0x1a9d82,0x1f5ede43,0x179e02]
def tableP432_1 : List Nat := [0x19de82,0x1a9f02,0x20e05fc3,0x175f82,0x179f82,0x192002,0x1a6082,0x1aa082,0x2a102,0x1841,0x215957d69805,0x215ad7d89805,0x215ad9589805,0x2e182,0x2362e243,0x23c02203,0x23c0a283,0x23c12303,0x2564e443,0x25c32403,0x25c3a483,0x25c42503,0x2641,0x26856603,0x2744a603,0x27c1,0x2805e783,0x28866783,0x2941,0x2987e903,0x2a086903,0x2beb6ac3,0x2c0b6a83,0x2cc92a83,0x2c0e6b03,0x2cccab03,0xd6b82,0x2e6ded43,0x18ee02,0x2fef6ec3,0x21ef82,0x3170f043,0x18f102,0x32f271c3,0x21f282,0x3473f343,0x18f402,0x35f574c3,0x21f582,0x26e3b603,0x36702d03,0x3670ad83,0x29e3b683,0x36f32d03,0x36f3ad83,0x2865b703,0x3771ae83,0x37722f03,0x2c65b783,0x37f4ae83,0x37f52f03,0x2a673803,0x38733003,0x3873b083]
def tableP432_2 : List Nat := [0x2ca8f883,0x38f4b183,0x38f53203,0x581,0x601,0x501,0x781,0x801,0x215957d684,0x215ad7d884,0x215ad95884,0x23e202,0x23e282,0x23e302,0x25e402,0x25e482,0x25e502,0x2681,0x2741,0x2801,0x2881,0x2981,0x2a01,0x2cea82,0x2ceb02,0x23b602,0x23b682,0x25b702,0x3801,0x333002,0x33b082,0x2cb882,0x25c1,0x3701,0x23c1,0x3601,0x3681,0x2158a083,0x21589c83,0x21589943,0x215882,0x18f382,0x18c1,577,0x2141,0x1601,641,0x2181,0x2f81,0x3281,0x3581,0xd1582,0xd1182,0xd1202,0xd01,0x1101,0x1401,0x2b81,0x2cc1,0x3881,0x132c02,0x37f502,0x37f482,0x37c1]
def tableP432_3 : List Nat := [0x2c41,0x1301,0x13c1,0xdc1,0xe01,0x1081,0x2b01,0x1041,0x2ac1,0xb01]

def encodedP432 (i : Nat) : Nat :=
  if i < 128 then
    if i < 64 then
      tableP432_0.getD (i%64) 0
    else
      tableP432_1.getD (i%64) 0
  else
    if i < 192 then
      tableP432_2.getD (i%64) 0
    else
      tableP432_3.getD (i%64) 0
def bookP432 (i : Nat) : Clause := let n := encodedP432 i; unpackLits 8 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClausesP432 : inputsOK 1 432 aP432 rP432 (baseBook bookP432 131).toList=true := by decide +kernel

def rowsP432_0 : List Nat := [0xe1001,0xe1201,0x141601,0x181a01,0x181c01,0x929401,0x929601,0x929801,0x9e01,0x2a001,0x4a201,0x6a601,0x8a801,0xaaa01,0x10aacae02,0xcacb002,0x106b2b402,0x108b2b602,0x10cb8ba02,0x10eb8bc02,0x1ec201,0x20c601,0x122e201,0x12ae801,0x126ee01,0x12d24fa02,0x138fc01,0x138fe01,0x1290001,0x1211f1ca403,0x1413601,0x11b19169c03,0x1453201,0x1453401,0x76751512788e8c7007,0x8510867472654a8a07,0x6c7c687e6a826f111464800a,0x887a84708a774f4d4b1209,0xd2cb3cecccd54748e408,0xd2cb3aeadb52dcd4cd4748e60b,0x1546601,0x1555001,0x1565a01,0x1589001,0x15c9a01,0x15ed001,0x15ed801,0x15ee001,0x363a60623c58565c255b56320b,0x4c5e4e3634225c25675b56540b,0x4c5e523a38225c25675b56500b,0x505460623e336b69665c255b564c0d,0x16c3001,0x16c4a01,0x16cc801,0x1312f72be03,0x1753e01,0xc0c4442e262843736ebe09,0xd6cf04f977616342f008,0xd6cf02f777616342f208,0xdf7b657c03,0x1417ef402,0x1817801,0x171824002,0x1844601,0x1844801,0x1862c01,0x18188c402,0x16f8a2602,0x1738cbe02,0x18e2a01]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOkP432_0 : checkRows bookP432 8 131 rowsP432_0=true := by decide +kernel

def lastUnitsP432 := digits 8 3 0xc0c9c8
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflictP432 : checkReasons bookP432 202 96 lastUnitsP432 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem excludeP432 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 432=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=1) h hc bp eq (by decide +kernel)
  let v := truth Z aP432
  have hbase : ValidThrough v bookP432 131 := book_start Z h hc z eq _ _ _ _ initialClausesP432
  have h0 : ValidThrough v bookP432 202 := rows_sound hbase rowsP432_0 rowsOkP432_0
  exact book_end h0 _ _ conflictP432
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def aP525 := ([1,0xc0001,0x3007,0x2002,0x3002,0x4002,0x5802,0x6802,65,0xc0041,0xc047,0x80061,0xc0061,0x867,0x80081,0x3083,0x80881,0x1080,0x81081,0xc00c1,0x8c0,0x200c1,0x800c1,0xa00c1,0x1a00c1,0x68c3,0xc08c1,0x10c0,0x808c1,0xa08c1,0x1a08c1,0xc10c1,0x210c1,0x810c1,0xa10c1,0x1a10c1,0x10c7,0x210c7,0x410c7,0x70c7,0x270c7,0x470c7,0xd0c7,0x2d0c7,0x4d0c7,0xf8c7,0x2f8c7,0x4f8c7,0x48c8,0x8048c8,0x10048c8,0x3048c8,0xb048c8,0x13048c8,0x83009,0x1a3009,0x100101,0x5903,0x6903,0x100901,0x1100,0x101101,0x100121,0x160121,0x1127,0x4927,0x140141,0x140941,0x141141,0x160161,0x960,0x100161,0x140161,0x180161,0x160961,0x1160,0x100961,0x140961,0x180961,0x101161,0x181161,0x7167,0x27167,0x47167,0x8967,0x28967,0x48967,0x10967,0x30967,0x50967,0x2c1968,0xac1968,0x12c1968,0x105809,0x180181,0x180981,0x181181,0x9a0,0x1001a1,0x1401a1,0x1601a1,0x11a0,0x1009a1,0x1409a1,0x1609a1,0x39a7,0x239a7,0x439a7,0x59a7,0x259a7,0x459a7,0xb1a7,0x2b1a7,0x4b1a7,0x3a11a8,0xba11a8,0x13a11a8,0x3e11a8,0xbe11a8,0x13e11a8,0x4611a8,0xc611a8,0x14611a8,0x106809,5,6,0xc0006,0x2805,0x2806,0xc2806,0x4005,0x84006,0xc4006,0x4805,0x5005,0x25005,0x45005,0x5805,0x25805,0x45805,0x85806,0x6005,0x26005,0x46005,0x8005,0x28005,0x48005,0xc8006,0x8805,0x28805,0x48805,0x9005,0x29005,0x49005,0xc9006,37,0x20025,0x40025,0x2825,0x22825,0x42825,0x4025,0x24025,0x44025,0x184026,0x4825,0x24825,0x44825,0x184826,0x5025,0x25025,0x45025,0x145026,0x5825,0x25825,0x45825,0x105826,0x145826,0x165826,0x6025,0x26025,0x46025,0x106026,0x146026,0x166026,0x8025,0x28025,0x48025,0x108026,0x8825,0x108826,0x168826,0x9025,0x29025,0x49025,0x109026,0x149026,0x169026,0x2804,0x8004,0x80a4,0x4904,0x5904,0x9104,0x5944,0x6144,0x6164,0x9164,0x8a04,0x9204,0x9224] : List Nat).toArray.map readPackedFact
def rP525 := ([0,0x3005,0xc3009,0xc045,0x300049,0x303049,0x865,0x22069,0x23069,128,0x880,0x1080,131,0x308e,192,0x8c0,0x8c1,0x10c0,195,0x10c5,0x420c9,0x8428c9,0x10420c9,0x70c5,0x1c08c9,0x1c20c9,0x9c20c9,0x11c08c9,0x11c20c9,0xd0c5,0x3468c9,0xb468c9,0x13428c9,0xf8c5,0x3e28c9,0x3e68c9,0xbe28c9,0xbe68c9,0x13e68c9,0x48c6,0x248ca,0x848ca,0x200848ca,0x200a48ca,0x400248ca,0x400848ca,0x3048c6,0xc0a48ca,0xc1a48ca,0x2c0a48ca,0x2c1a48ca,0x4c0a48ca,0x4c1a48ca,0x8300c,0x8020cf,0x10020cf,0x10220cf,0x1a300c,0x68ce,0x8068cf,0x10068cf,0x10268cf,256,0x900,0x1100,259,0x590e,0x4690d,0x1125,0x44129,0x4925,0x125929,320,0x940,0x1140,352,0x960,0x961,355,0x7165,0x1c4169,0x1c6169,0x9c4169,0x9c6169,0x47167,0x11c4169,0x11c6169,0x8965,0x226169,0xa25169,0x48967,0x10965,0x425169,0xc26169,0x50967,0x2c1966,0xb10196a,0xb18196a,0x2b10196a,0x2b18196a,0x4b10196a,0x4b18196a,0x10580c,0x80416f,0x100416f,0x102416f,384,0x980,0x1180,419,0x39a5,0xe41a9,0x8e51a9,0x439a7,0x59a5,0x1659a9,0x9641a9,0x459a7,0xb1a5,0x2c41a9,0x2c51a9,0xac41a9,0xac59a9,0x4b1a7,0x3a11a6,0xe9011aa,0x2e9411aa,0x13a11a8,0x3e11a6,0xf9611aa,0x2f9011aa,0x13e11a8,0x4611a6,0x119411aa,0x319011aa,0x14611a8,0x10680c,0x8041af,16,0x20000012,0x3000012,0x2810,0x2812,0x3002812,0x4010,0x2004012,0x3004012,0x4810,0x5010,0x45011,0x5810,0x22005812,0x22025812,0x45811,0x22045812,0x6010,0x46011,0x8010,0x23008012,0x23028012,0x48011,0x23048012,0x8810,0x48811,0x9010,0x23009012,0x23029012,0x49011,0x23049012,48,0x40031,0x2830,0x42831,0x4030,0x6004032,0x6024032,0x44031,0x4830,0x26004832,0x26024832,0x26044832,0x5030,0x25005032,0x25025032,0x25045032,0x5830,0x4005832,0x5005832,0x25805832,0x4025832,0x25825832,0x45831,0x6030,0x5006032,0x5806032,0x26031,0x24026032,0x5026032,0x5826032,0x46031,0x8030,0x24008032,0x24028032,0x48031,0x24048032,0x8830,0x4008832,0x5808832,0x9030,0x25809032,0x5029032,0x25829032,0x49031,0x200a0013,0xa0034,0x8a0034,0x3200013,0x200034,0xa00034,0x3202813,0x202834,0xa02834,0x124014,0x6124033,0x2164013,0x164034,0x964034,0x3244013,0x244034,0xa44034,0x165014,0x965014,0x25165033,0x185014,0x985014,0x25185033,0x185814,0x985814,0x4185833,0x25985833,0x245834,0xa45834,0x4245833,0x25245833,0x228014,0xa28014,0x24228033,0x248014,0xa48014,0x24248033,0x248814,0xa48814,0x5a48833] : List Nat).map readPackedScheme

def tableP525_0 : List Nat := [65,321,0x10102,0x541,0x80502,0x90502,0x6c1,0xb0682,0xc0682,0x741,0x841,0x941,0x38882,0x1f040183,0x9c1,0xd41,0x148d82,0xfc1,0x48d82,0x4d259243,0x161202,0x1d1282,0x211302,0x532893c3,0x151382,0x161382,0x1c1402,0x201482,0x211482,0x592b9543,0x181502,0x1e1582,0x221602,0x5f2e96c3,0x171682,0x181682,0x1d1702,0x1e1702,0x231782,0x65319843,0x159802,0x161802,0x1c1882,0x1d9882,0x209902,0x211902,0x6b3499c3,0x179982,0x181982,0x1d9a02,0x1e1a02,0x229a82,0x231a82,0x31b02,0x1b4722d140785,0x1b4862d1b0785,0x1b486391b0785,0x71b82,0x33070203,0x1bc7a31140c85,0x1bc8e311b0c85,0x1bc8e3d1b0c85,0x1c41,0x1dc1]
def tableP525_1 : List Nat := [0x1ec1,0x59e02,0x73060283,0x1d41,0x2041,0x3e2002,0x20c1,0x3f2082,0x2141,0x21c1,0x2241,0x22c1,0x2541,0x46a582,0x6a582,0xa752a8c3,0x472882,0x492882,0x4c2902,0x4e2902,0x4ba982,0x4f2982,0x502982,0xad55aa43,0x492a02,0x4d2a82,0x4bab02,0xb358abc3,0x482b82,0x4e2c02,0x4bac82,0xb95bad43,0x472d02,0x49ad02,0x4c2d82,0x4ead82,0x4f2e02,0x50ae02,0x52e82,0x2ed328f461c85,0x2ed3e8f4b1c85,0x2ed3e994b1c85,0x2f41,0x2fc1,0x3041,0x7b282,0xd76ab4c3,0x623482,0x673502,0x65b582,0xdd6db643,0x643602,0x663682,0x65b702,0xe370b7c3,0x623782,0x633782,0x663802,0x683802,0x65b882,0xe973b943,0x62b902,0x673982,0x65ba02]
def tableP525_2 : List Nat := [0xef76bac3,0x643a82,0x66bb02,0x65bb82,0xf579bc43,0x633c02,0x66bc82,0x65bd02,0x53d82,0x3dd9ac5611d05,0x3e41,0xfb003e03,0xfc01be03,0x3fc1,0x10008bf83,0x10209bf83,0x4141,0x1060bc103,0x1080cc103,0x42c1,0x11187c343,0x11c402,0x1178ac4c3,0x1190e4483,0x119104503,0x11c582,0x119124583,0x11f8ec6c3,0x11c782,0x12591c843,0x127134803,0x1271a4883,0x1bc902,0x1271f4903,0x12d95ca43,0x1bcb02,0x13398cbc3,0x135134b83,0x1351a4c03,0x1bcc82,0x1351f4c83,0x13b9ccdc3,0x3cce82,0x1419fcf43,0x3cd002,0x147a2d0c3,0x14849d083,0x1484ed103,0x4bd182,0x14fa6d2c3,0x1515e5283,0x1515f5303,0x151605383,0x157aad4c3,0x159425483,0x159435503,0x159445583,0x15faed6c3,0x16047d683,0x16248d683,0x165455683,0x1604cd703,0x1654a5703,0x4bd782]
def tableP525_3 : List Nat := [0x16bb4d9c3,0x16e63d983,0x17064d983,0x61da02,0x16d665a03,0x16e67da03,0x17068da03,0x65da82,0x177badcc3,0x179385c83,0x1793b5d03,0x3cdd82,0x1793d5d83,0x5ec1,0x17c3ede83,0x17e3fde83,0x185c1e043,0x18b456003,0x1884de083,0x18b4a6083,0x4be102,0x1017d6303,0x18d9e4d83,0x18d9f4e03,0x1267ee383,0x18fb94d83,0x18fba4e03,0x12681e403,0x191b94f03,0x191ba4f83,0x193854103,0x150a4e483,0x11883e503,0x195ad5083,0x195ae5103,0x13484e583,0x197c05083,0x197c15103,0x199894303,0x1998a4383,0x163ac6603,0x19b8d4303,0x19b8e4383,0x16fac6683,0x19d8d4483,0x19d8e4503,0x16cb0e703,0x171b26703,0x19fc05683,0x19fc15703,0x186b0e783,0x189b16783,0x1a1944803,0x1a1954883,0x17dbc6803,0x1a3974803,0x1a3984883,0x187bc6883,0x1a5974a03,0x1a5984a83,0x18abfe903,129,0x401,0x481]
def tableP525_4 : List Nat := [0x581,0x601,0x1f01,0x1f81,0x1eecd62b084,0x3ec1,0x3f01,0x4001,0x4081,0x4181,0x4201,0x8cc482,0x8cc502,0x8cc582,0x93c802,0x93c882,0x93c902,0x9acb82,0x9acc02,0x9acc82,0xa8d282,0xa8d302,0xa8d382,0xacd482,0xacd502,0xacd582,0xb2d682,0xb2d702,0xbcdc82,0xbcdd02,0xbcdd82,0x5f01,0x5f81,0xc5e002,0xc5e082,0x6301,0x9e4d82,0x9f4e02,0x936382,0x936402,0x64c1,0xa85242,0x8c6502,0x9a6582,0xbc6802,0xc56902,0x5e41,0x6801,0x4d41,0x6581,0x4641,0x6501,0x49c1,0x6381,0x6401,0x4c2382,0x12c8f4f8284,0xb91e42,0x96052603,0x4b0282,0x3cdd02,0x1e41,705,0x3d81]
def tableP525_5 : List Nat := [0x2581,0x2981,0x2b01,0x2c81,0x5181,0x5781,0x6101,0x5641,0xde36191a84,0xde36190c44,0x6f1b0c83,0x70d82,0x34ba31bcb84,0x34ba31bcc04,0x1a3d28dc3,0x65b202,0x161ad6703,0xcb66dc03,0x36031903,0xa0da1e329385,0x6c4b030e44,0x36258183,0xd8da51168785,0x8f379dccc705,0x479bcee644,0x5441,0x5241,0xb15682,0x5881,0x6601,0x16e65b343,0xb732c2,0x1bd702,0xdc1,0xa41,577,897,0x3281,0x5a81,0x3201,0x5b81,0x6681,0xce5682,0x6701,0x8c1,449,0x1b01,0x7c1,0x1901,0x12c1,0xe81,0x1881,0x1841,0xb01,0xe41,0x1441]

def encodedP525 (i : Nat) : Nat :=
  if i < 192 then
    if i < 64 then
      tableP525_0.getD (i%64) 0
    else
      if i < 128 then
        tableP525_1.getD (i%64) 0
      else
        tableP525_2.getD (i%64) 0
  else
    if i < 256 then
      tableP525_3.getD (i%64) 0
    else
      if i < 320 then
        tableP525_4.getD (i%64) 0
      else
        tableP525_5.getD (i%64) 0
def bookP525 (i : Nat) : Clause := let n := encodedP525 i; unpackLits 9 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClausesP525 : inputsOK 1 525 aP525 rP525 (baseBook bookP525 253).toList=true := by decide +kernel

def rowsP525_0 : List Nat := [0x40401,0xc0801,0xc0a01,0x180e01,0x181001,0x1108a01,0x1188e01,0x10d1201,0x2291602,0x7ea291802,0x7f2351c02,0x7fa351e02,0x802412202,0x80a412402,0x252e01,0x293001,0x2d3401,0x393c01,0x3d3e01,0x454201,0x394a01,0x3d4c01,0x455001,0x1a96401,0x1ad6601,0x1b16801,0x1216c01,0x1256e01,0x1297001,0x12d7801,0x1317c01,0xf99201,0xfd9401,0x1019801,0x813359c02,0x81b359e02,0x12da201,0x131a601,0x83c15aa02,0x48dac01,0x48dae01,0x419b001,0x421b601,0x49a41bc02,0x4a1be01,0x425c001,0x429c601,0x47dec01,0x481f801,0x11e8ec719003,0x4ba5801,0x113894454803,0x4c25601,0x10d8642d2c03,0x4ca5401,0x11087c393a03,0x4d24c01,0x4d24e01,0x562f93cc05029188ca07,0x4233138d003,0x156a9562a9b2dc9b4d64a08,0x144be4f32156713731148c209,0x2997c9e642a980a06933ce8846626938c60e,0x156a96eb6954ac9b4d64808,0xcb9e4e59003,0x4f48201,0x4f91001,0x4fa7601,0x500a801,0x500b401,0x500bc01,0x5016001,0x5017e01,0x501a801,0x1198c45d6a03,0x1e0f8f07a201a0cc3a07,0x178845c2619094783b08520440a,0x108f44832188b86023a4d204c0a,0x3a090e69403,0xa24ebe9eea051cbdea07,0xa24ebedf0a051cbde807,0xa7a6d314803,0x74401c902733aa0d0407,0xee7a8231988c360309deee8d1ed8f4f36d2e9d2d90be5e4f0683955ae19fcba8d31a24ccec20,0x773d4118cc360308f6c7a7cfcec0b,0xc8686e380d8b45835068482e0a,0x9c6c280c8605405,0x28161b0e02035068482608,0xa438270b8a83554a9d481a35080486e0d,0x5c5a1c1b842a605,0x4b251daea4aa65cc06,0x25928ec74a6eae954ca71ce09,0x1168ac516203,0x5665201,0x2dabcb8ad5db86875aa24ccba0a,0xf32cbc4aed02c3915cad712e6b742a34c6b54499d15a413]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOkP525_0 : checkRows bookP525 9 253 rowsP525_0=true := by decide +kernel

def rowsP525_1 : List Nat := [0xa3d71d002,0x379c208c561b01828542218e28763cfcdc0e,0x1f9807c609f4f0773b1e6bcc73f9ed8a0d,0x3ca9cbd96949e32227b40a2e4572b5c52ea0d1a635aa24cdf215,0x1f2baa71425a4f78484a6d057b955ae15cd825d41a356a634499d15e418,0x5842001,0x5842401,0x5869601,0x590da01,0x5958e01,0x5969e01,0x596be01,0xa3da1d602,0x53282bd74ada8386835aa24cc9e0b,0x527713d8851602baa2c256bbdc51b5cdaa8366ad596cf4499d157a17,0x169aedaeb003,0x5b01801,0x5b46a01,0xb1db41a02,0xb0db6a402,0xb0db6aa02,0x5c42a01,0x5c85601,0xb85cc4e02,0x5d05201,0x2dd62b7dd46c04,0x2c36eb7dd6ac04]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOkP525_1 : checkRows bookP525 9 349 rowsP525_1=true := by decide +kernel

def lastUnitsP525 := digits 9 2 0x2ed77
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflictP525 : checkReasons bookP525 376 26 lastUnitsP525 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem excludeP525 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 525=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=1) h hc bp eq (by decide +kernel)
  let v := truth Z aP525
  have hbase : ValidThrough v bookP525 253 := book_start Z h hc z eq _ _ _ _ initialClausesP525
  have h0 : ValidThrough v bookP525 349 := rows_sound hbase rowsP525_0 rowsOkP525_0
  have h1 : ValidThrough v bookP525 376 := rows_sound h0 rowsP525_1 rowsOkP525_1
  exact book_end h1 _ _ conflictP525
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def aP645 := ([0x80001,0xa0001,0x1007,0x2802,0x4002,0x5002,0x80081,0x80881,0x81081,0xa00a1,0x40a3,0xa08a1,0x10a0,0x100101,0x900,0xa0101,0x140101,0x5103,0x1a0101,0x100901,0x1100,0xa0901,0x140901,0x1a0901,0x101101,0xa1101,0x141101,0x1a1101,0xc107,0x2c107,0x4c107,0xe107,0x2e107,0x4e107,0xe0108,0x8e0108,0x10e0108,0x341108,0xb41108,0x1341108,0x3a1108,0xba1108,0x13a1108,0xa4009,0x144009,0x140121,0x180121,0x3127,0x6127,0x140141,0x100141,0x180141,0x140941,0x1140,0x100941,0x180941,0x7147,0x27147,0x47147,0x8147,0x28147,0x48147,0x180181,0x180981,0x181181,5,0x805,0x80806,0xa0806,0x5005,0x25005,0x45005,0x85006,0x6805,0x26805,0x46805,0x7005,0x27005,0x47005,0xa7006,0x7805,0x27805,0x47805,37,0x20025,0x40025,0x100026,0x825,0x20825,0x40825,0x100826,0x5025,0x25025,0x45025,0x185026,0x6825,0x146826,0x186826,0x7025,0x27025,0x47025,0x147026,0x187026,0x7825,0x27825,0x47825,0x187826,0x804,0x5024,0x7024,0x7144,0x71a4,0x79a4,0x79c4] : List Nat).toArray.map readPackedFact
def rP645 := ([0x1005,0x42009,0x42809,128,0x880,0x1080,160,0x8a0,163,0x40ae,256,0x900,0x901,0x1100,259,0xc105,0x302909,0x306909,0xb02909,0xb06909,0x1302909,0x1306909,0xe105,0x385109,0x386909,0xb85109,0xb86909,0x4e107,0x1385109,0x1386909,0xe0106,0x394010a,0x2394010a,0x10e0108,0x341106,0xd0a110a,0xd1a110a,0x2d0a110a,0x2d1a110a,0x4d0a110a,0x4d1a110a,0x3a1106,0xe94110a,0xe9a110a,0x2e94110a,0x2e9a110a,0x13a1108,0x4e94110a,0x4e9a110a,0xa400c,0x80290f,0x100290f,0x102290f,0x14400c,0x510d,0x80510f,0x100510f,0x102510f,0x3125,0xc5129,0x6125,0x186129,320,0x940,323,0x7145,0x1c4149,0x9c6149,0x47147,0x8145,0x206149,0xa04149,0x48147,384,0x980,0x1180,16,0x810,0x2000812,0x2800812,0x5010,0x22005012,0x22025012,0x22045012,0x6810,0x46811,0x7010,0x22807012,0x22827012,0x47011,0x7810,0x47811,48,0x24000032,0x24020032,0x24040032,0x830,0x4000832,0x4020832,0x40831,0x5030,0x6005032,0x45031,0x6830,0x5006832,0x6006832,0x7030,0x25007032,0x25027032,0x6027032,0x47031,0x7830,0x26007832,0x26027832,0x26047832,0x20014,0x24020033,0x2140813,0x940834,0x29c0813,0x1c0834,0x9c0834,0x1c5034,0x61c5033,0x1c6814,0x9c6814,0x51c6833,0x1e6814,0x9e6814,0x61e6833,0x1e7014,0x9e7014,0x61e7033] : List Nat).map readPackedScheme

def tableP645_0 : List Nat := [321,258,0x8102,833,961,0x441,0x4c1,0x5c1,0x1c602,0x5420183,0x6c1,0x9c1,0x74a02,0xc41,0x24a02,0xf4ece43,0x78e02,0x90e02,0xa8e82,0xb8e82,0xc8f02,0xd8f02,0x10d04fc3,0x80f82,0x90f82,0xb1002,0xb9002,0xa5082,0xd1082,0xd9082,0x1251d143,0x85102,0xb5182,0xa5202,0x13d352c3,0x79282,0x95282,0xa9302,0xbd302,0xc9382,0xdd382,0x1554d443,0x81402,0x95402,0xb1482,0xbd482,0xa5502,0xd1502,0xdd502,0x19582,0x15cac7c70505,0x15ccc7ca0505,0x15cccaca0505,0x29602,0x8c1,0x164b48470885,0x164d484a0885,0x164d4b4a0885,0x17c1,0x169782,0x1841,0x171802,0x18c1,0x1a41]
def tableP645_1 : List Nat := [0x2da82,0x1d5cdc43,0x191c02,0x1b9c82,0x1add02,0x1ede5dc3,0x199d82,0x1b1e02,0x1ade82,0x1f41,0x1fc1,0x2041,0x20c1,0x2141,0x21806103,0x2200e103,0x23e362c3,0x24432283,0x2443a303,0x24442383,0x25e564c3,0x66582,0x2766e643,0x27c4a603,0x27c5a683,0x66702,0x2968e843,0x66902,0x2aea69c3,0x2b46a983,0x2b49aa03,0x2b4c2a83,0x2cec6bc3,0x2d196b83,0x2d1b6c03,0x1aec82,0x2eee6dc3,0x2f19ed83,0x1aee82,0x2fc1,0x3016ef83,0x30976f83,0x3271f143,0x32d8b103,0x32da3183,0x331bf183,0x1af202,0x34f473c3,0x355f3383,0x355fb403,0x35603483,0x35e12083,0x2d6b3583,0x2421f603,0x366e2c03,0x27a27683,0x36f12b83,0x36f1ac03,0x37712d83,0x332f7703,0x37e62483,0x37e6a503,0x32b07783,0x38682483]
def tableP645_2 : List Nat := [0x3868a503,0x3530f803,0x38e82603,0x38e8a683,0x35337883,1,129,0x164b484704,0x164d484a04,0x164d4b4a04,0x1681,0x1701,0x2181,0x2201,0x246282,0x246302,0x246382,0x27e602,0x27e682,0x2b6982,0x2b6a02,0x2b6a82,0x3001,0x3081,0x32f102,0x32f182,0x357382,0x357402,0x357482,0x35c1,0x2d6b02,0x243602,0x27b682,0x32b782,0x353802,0x3541,0x3801,0x2441,0x3601,0x165502,0x164f82,0x165002,0x1641,641,0x1a81,0x1d01,0x1e81,0x2c81,0x2e81,0x3201,0x32c1,0x3781,0xa0e47c184,0x2767c2,0x2b41,0x2d41,0x2f2c02,0x3336eb83,0x3336c2,0x1908e43,0x19082,0x15ca0512c7c5,0x15d54a050945,0x1954a03]
def tableP645_3 : List Nat := [0x15525003,0x19542,0x192c2,385,0x601,0x2581,0x2701,0x2901,0x27c1,0x3681,0x3301,0x3881,0x2601,0x26c1,0x2501,0x2881,0x24c1,0x2841]

def encodedP645 (i : Nat) : Nat :=
  if i < 128 then
    if i < 64 then
      tableP645_0.getD (i%64) 0
    else
      tableP645_1.getD (i%64) 0
  else
    if i < 192 then
      tableP645_2.getD (i%64) 0
    else
      tableP645_3.getD (i%64) 0
def bookP645 (i : Nat) : Clause := let n := encodedP645 i; unpackLits 8 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClausesP645 : inputsOK 1 645 aP645 rP645 (baseBook bookP645 133).toList=true := by decide +kernel

def rowsP645_0 : List Nat := [513,0x401,0x6c6e01,0x6c7001,0x6c7201,0x747601,0x787a01,0x10a9a9c02,0x10c9a9e02,0x6a201,0x8a401,0xaa601,0xcae01,0xeb001,0x14ba01,0x16bc01,0x1abe01,0x114ced002,0x116ced202,0x7cd601,0x7ed801,0x92e001,0x94e201,0x96e401,0x9a98e602,0x13ae801,0x118ea01,0x11aee01,0x12cfc01,0x12f0201,0x1393734de03,0x1474401,0x1211f1ca003,0x14b3e01,0x322e3b1310605e5c2c08,0x183d0e405852563e302f4e420b,0x183d0e3e54525a4034334e420b,0x5459111238362d53514e520a,0x1546a01,0x1568001,0x1588801,0x1589001,0x158c601,0x158cc01,0x158dc01,0x1333162d403,0x1654201,0x282466641262181c1e08,0x12522ac02,0x12b2926b803,0x16d3c01,0x8aca8ec8c4ed5d616f4c8c0a,0xda82d484f0c35b636e8609,0xf6d4c970f2ecc1735f4d6162f40c,0x2826684c4a44476862503a121c361e0e,0x4a486422217612501c183a3662440d,0x4a4e6466184405,0x4a50682a281e217a265a525648440d,0x242a68504e444c34462d6830237c121c63781e12,0x3e523c5a4034325407,0x40523c563e302e2d80437f78580c,0x4e4c6826241e217a622a60121c5d82440f,0x1684847845d822206,0x1861001,0x188aa01,0x188b201,0x188b601,0x18d6a01,0x1914001,0x1937401,0x147950802,0xb4a904f9498f8b97670009,0x18d98ac02,0x1679afa02,0x1979b0602,0x18b9ca802,0x18f9eb402]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOkP645_0 : checkRows bookP645 8 133 rowsP645_0=true := by decide +kernel

def lastUnitsP645 := digits 8 3 0xa4d1d0
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflictP645 : checkReasons bookP645 210 127 lastUnitsP645 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem excludeP645 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 645=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=1) h hc bp eq (by decide +kernel)
  let v := truth Z aP645
  have hbase : ValidThrough v bookP645 133 := book_start Z h hc z eq _ _ _ _ initialClausesP645
  have h0 : ValidThrough v bookP645 210 := rows_sound hbase rowsP645_0 rowsOkP645_0
  exact book_end h0 _ _ conflictP645
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def aP1034 := ([0xc0061,0x867,0xc00c1,0xc08c1,0xe00e1,0xe08e1,0x100101,0x100901,0xe0121,0x100121,0x160121,0xe0921,0x100921,0x160921,0x1927,0x21927,0xf927,0x2f927,0x200928,0xa00928,0x160161,0xe0161,0x100161,0x160961,0xe0961,0x100961,0x1967,0x21967,0x3805,0x4005,0xc4006,0x8005,0x28005,0x8805,0x28805,0x9005,0x29005,0xc9006,0x3825,0x23825,0xe3826,0x4025,0x24025,0xe4026,0x8025,0x28025,0x108026,0x8825,0x28825,0xe8826,0x108826,0x168826,0x9025,0x29025,0xe9026,0x109026,0x169026,0x40e4,0x9104,0x8a04,0x9204,0x9224] : List Nat).toArray.map readPackedFact
def rP1034 := ([0x865,0x23069,192,0x8c0,224,0x8e0,256,0x900,0x1925,0x63929,0x64129,0x863929,0x864129,0xf925,0x3e3929,0x3e5929,0xbe3929,0xbe5929,0x200926,0x80e092a,0x810092a,0x280e092a,0x2810092a,352,0x960,0x1965,0x63969,0x64169,0x863969,0x864169,0x3810,0x4010,0x3004012,0x8010,0x8810,0x9010,0x23009012,0x23029012,0x3830,0x23803832,0x23823832,0x4030,0x3804032,0x3824032,0x8030,0x24008032,0x24028032,0x8830,0x23808832,0x4008832,0x5808832,0x23828832,0x4028832,0x5828832,0x9030,0x3809032,0x4009032,0x25809032,0x3829032,0x4029032,0x25829032,0x103814,0x23903833,0x3244013,0x244034,0xa44034,0x228014,0xa28014,0x24228033,0x248014,0xa48014,0x24248033,0x248814,0xa48814,0x23a48833,0x5a48833] : List Nat).map readPackedScheme

def tableP1034_0 : List Nat := [193,130,321,449,577,705,833,961,0x3e742,0x20702,0x24702,0x2c782,0x30782,0x46842,0x20802,0x28802,0x2c882,0x34882,0x4e942,0x22902,0x24902,0x2e982,0x30982,0xa41,0xbc1,0x6ed42,0x54d02,0x58d02,0x60d82,0x64d82,0xe41,0xec1,0x3c02e83,0x82fc2,0x8b0c2,0x931c2,0x4b09183,0x4b0d203,0x9f342,0x5111303,0x5115383,0xab4c2,0x5657483,0x5663503,0xb7642,0x5d19603,0x5d1d683,0xc37c2,0x6321783,0x6427783,0x662b783,0x632d803,0x6433803,0x6637803,0xd7a42,0x6c57a03,0x6e5ba03,0x7151a03,0x6c63a83,0x6e67a83,0x715da83,0x7374e03,0x57a1c83,0x4a7bd03]
def tableP1034_1 : List Nat := [0x75d1483,0x75d5503,0x7784f83,0x7789003,0x65b9d83,0x798cf83,0x7991003,0x6fb9e03,0x7b8d083,0x7b91103,0x6dc5e83,0x70cfe83,1,0xf01,0x97182,0x97202,0xa3302,0xa3382,0xbb602,0xbb682,0xe3a02,0xe3a82,0x1cc1,0xaf402,0x95d02,0x12c1,0x1d01,0x1441,0x15c1,0xd9a82,0xd9a02,0x1b01,0x1741,0x63cd783,0xc7982,0xe1e82,0x54ef183,0xa9dc2,0x601,0x481,0x1901,0x1d81,0x1501,0x14c1,0x1a01,0xac1,0x1ac1,0xd01,0x1c41,0xdc1,0xc81,0x1b81,0x1e01,0xf7202,0x1ec1]

def encodedP1034 (i : Nat) : Nat :=
  if i < 64 then
    tableP1034_0.getD (i%64) 0
  else
    tableP1034_1.getD (i%64) 0
def bookP1034 (i : Nat) : Clause := let n := encodedP1034 i; unpackLits 7 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClausesP1034 : inputsOK 0 1034 aP1034 rP1034 (baseBook bookP1034 76).toList=true := by decide +kernel

def rowsP1034_0 : List Nat := [513,0x261f4002,0x24801,0x34a01,0x44e01,0x55001,0x65a01,0x75c01,0x177201,0x187801,0xf9e7a02,0x567c01,0x4d7e01,0x27ce4602,0x59b001,0x28d04c02,0x5bae01,0x546549c82ead5c3408,0x566549a80ded5c3808,0x1b5dbc02,0x29d25802,0x546921e4d9302007,0x131a488956acd7e11c09,0x12e55fc403,0x2243222c7706cc9c578ea36836ae608611,0x890c98c8f247706cc9c578ea36836ae608413,0x92420b0c2605,0xb2420a0a2a05,0x62d33e65e04,0x30688802,0x69ca01,0x6a5201,0x2d6b8002,0x2e6b5402,0x6c6c01,0x6d3401,0x6eaa01,0x6f3201,0x713a01,0x37727602,0x30738e02,0x1121931b4f48406,0x448644547d74f48608]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOkP1034_0 : checkRows bookP1034 7 76 rowsP1034_0=true := by decide +kernel

def lastUnitsP1034 := digits 7 2 0x3876
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflictP1034 : checkReasons bookP1034 119 99 lastUnitsP1034 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem excludeP1034 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 1034=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=0) h hc bp eq (by decide +kernel)
  let v := truth Z aP1034
  have hbase : ValidThrough v bookP1034 76 := book_start Z h hc z eq _ _ _ _ initialClausesP1034
  have h0 : ValidThrough v bookP1034 119 := rows_sound hbase rowsP1034_0 rowsOkP1034_0
  exact book_end h0 _ _ conflictP1034
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def aP1038 := ([0x3002,0x4002,0x4802,0x6802,0x20021,0x80021,0x827,0x20041,0x80041,0xc0041,0x1047,0xc047,0x80081,0x80881,0x81081,0xc00c1,0x68c3,0xc08c1,0x10c0,0x100101,0x120101,0x160101,0x1a0101,0x6903,0x100901,0x1100,0x120901,0x160901,0x1a0901,0xd907,0x2d907,0x4d907,0xf107,0x2f107,0x4f107,0x3a1108,0xba1108,0x13a1108,0x120121,0xe0121,0x160121,0x6923,0x120921,0x1120,0xe0921,0x160921,0x5127,0x25127,0x45127,0x280928,0xa80928,0x1280928,0x160161,0x160961,0x161161,0x1a01a1,0x9a0,0xc01a1,0xe01a1,0x1001a1,0x1201a1,0x1a09a1,0x11a0,0xc09a1,0xe09a1,0x1009a1,0x1209a1,0x1a11a1,0xc11a1,0xe11a1,0x1011a1,0x1211a1,0x9a7,0x209a7,0x409a7,0x29a7,0x229a7,0x429a7,0x3209a8,0xb209a8,0x13209a8,0x3a09a8,0xba09a8,0x13a09a8,0x4209a8,0xc209a8,0x14209a8,0xc6809,0x106809,0x126809,0x2005,0x22006,0x82006,0x2805,0xc2806,0x3005,0x23006,0x83006,0x6005,0x26005,0x46005,0x86006,0x8005,0x28005,0x48005,0xc8006,0x8805,0x28805,0x48805,0x9005,0x29005,0x49005,0x2025,0x22025,0x42025,0x2825,0x22825,0x42825,0x102826,0x122826,0x1a2826,0x3025,0x23025,0x43025,0x103026,0x123026,0x1a3026,0x6025,0x26025,0x46025,0x8025,0x28025,0x48025,0x128026,0x168026,0x8825,0x28825,0x48825,0x128826,0x168826,0x9025,0x29025,0x49025,0x169026,0x3084,0x6084,0x30a4,0x80a4,0x60c4,0x8a04,0x9204,0x9224] : List Nat).toArray.map readPackedFact
def rP1038 := ([32,0x825,0x22029,0x1045,0x40849,0x42049,0xc045,0x303049,128,0x880,0x1080,192,0x8c0,195,0x68ce,256,0x900,259,0xd905,0x364909,0x366909,0xb64909,0xb66909,0x4d907,0xf105,0x3c5909,0x3c6909,0xbc5909,0xbc6909,0x4f107,0x3a1106,0xe92110a,0xe9a110a,0x2e92110a,0x2e9a110a,0x13a1108,0x4690d,288,0x920,291,0x5125,0x143929,0x145929,0x943929,0x945929,0x45127,0x280926,0xa0e092a,0xa16092a,0x2a0e092a,0x2a16092a,0x1280928,0x2692d,352,0x960,0x1160,416,0x9a0,0x9a1,0x11a0,419,0x9a5,0x231a9,0x239a9,0x8231a9,0x8239a9,0x10231a9,0x10239a9,0x29a5,0xa41a9,0xa49a9,0x8a41a9,0x8a49a9,0x10a41a9,0x10a49a9,0x3209a6,0xc8c09aa,0xc8e09aa,0x2c8c09aa,0x4c8c09aa,0x4c8e09aa,0x3a09a6,0xe9009aa,0xe9209aa,0x2e9009aa,0x2e9209aa,0x4e9009aa,0x4e9209aa,0x4209a6,0x108c09aa,0x308e09aa,0x508c09aa,0xc680c,0x8031af,0x10031af,0x10231af,0x10680c,0x8041af,0x10041af,0x10241af,0x12680c,0x8049af,0x10049af,0x10249af,0x2010,0x20802012,0x2002012,0x2810,0x3002812,0x3010,0x803012,0x2003012,0x6010,0x22006012,0x22026012,0x22046012,0x8010,0x23008012,0x23028012,0x48011,0x8810,0x48811,0x9010,0x49011,0x2030,0x42031,0x2830,0x24002832,0x4802832,0x6802832,0x24022832,0x4822832,0x6822832,0x42831,0x3030,0x4003032,0x24803032,0x26803032,0x4023032,0x24823032,0x26823032,0x43031,0x4043032,0x24843032,0x26843032,0x6030,0x46031,0x8030,0x4808032,0x5808032,0x4828032,0x5828032,0x48031,0x8830,0x24808832,0x5808832,0x24828832,0x5828832,0x48831,0x9030,0x25809032,0x25829032,0x25849032,0x208c2013,0xc2034,0x8c2034,0x2182013,0x182034,0x982034,0xc2814,0x240c2833,0x48c2833,0x68c2833,0x3202813,0x202834,0xa02834,0x2183013,0x183034,0x983034,0x228014,0xa28014,0x4a28033,0x248014,0xa48014,0x5a48033,0x248814,0xa48814,0x5a48833] : List Nat).map readPackedScheme

def tableP1038_0 : List Nat := [577,833,0x50302,0x541,0x70502,0x80502,0x5c1,0x90582,0x641,0x6c1,0x741,0x7c1,0x8c1,0x8902,0x21030003,0x9c1,0xc41,0x18c82,0x3f1e8ec3,0x140e82,0x160e82,0x1a0f02,0x1c0f02,0x198f82,0x45219043,0x151002,0x161002,0x1b1082,0x1c1082,0x199102,0x4b2491c3,0x141182,0x169182,0x1a1202,0x1c9202,0x199282,0xbc1,0x1341,0x1541,0x29582,0x612f9743,0x271702,0x281702,0x2c1782,0x2d1782,0x2b9802,0x673298c3,0x279882,0x281882,0x2c9902,0x2d1902,0x2b9982,0x14c1,0x1a41,0x1ac1,0x1b41,0x1bc1,0x1ec1,0x389f02,0x21c1,0x39f02,0x9549a443,0x392402,0x3a2402]
def tableP1038_1 : List Nat := [0x3f2482,0x402482,0x442502,0x452502,0x9b4ca5c3,0x3b2582,0x3c2582,0x412602,0x422602,0x462682,0x472682,0xa14fa743,0x392702,0x3aa702,0x3f2782,0x442802,0x45a802,0xa752a8c3,0x3b2882,0x3ca882,0x412902,0x42a902,0x462982,0x47a982,0xad55aa43,0x392a02,0x40aa82,0x442b02,0x2b82,0x2bcfe73380805,0x2bd12733e0805,0x2bd127f3e0805,0x12c02,0x2c50677380b85,0x2c51a773e0b85,0x2c51a833e0b85,0x22c82,0x2cd0a79381485,0x2cd1e793e1485,0x2cd1e853e1485,0x2d41,0xb7042d03,0xb805ad03,0x2ec1,0xbc09ae83,0x2fc1,0xc007af83,0xc208af83,0xc963b143,0xcb0c3103,0xcb0d3183,0xcb0e3203,0xd167b343,0xd30f3303,0xd3113383,0x12b402,0xd96bb543,0x12b602,0xdf6eb6c3,0x12b782,0xe571b843,0x3eb902,0xeb74b9c3,0xed133983]
def tableP1038_2 : List Nat := [0xee14b983,0xf016b983,0xed183a03,0xee1aba03,0xf01cba03,0x19ba82,0xf77abcc3,0xf83bbc83,0xfb3c3c83,0xfd373c83,0xf841bd03,0xfb423d03,0xfd3d3d03,0x3ebd82,0xf846bd83,0xfb473d83,0xfd433d83,0x10380bfc3,0x3ec082,0x10983c143,0x10a14c103,0x10c15c103,0x10a1ac183,0x10c1bc183,0x19c202,0x11388c3c3,0x115264383,0x11628c383,0x1152a4403,0x1162dc403,0x2bc482,0x11d8dc643,0x11f344603,0x11f354683,0x11f364703,0xc15b4803,0x121793803,0x1217a3883,0xca5cc883,0x1237f3803,0x123803883,0x1255f2e83,0xf9764903,0xfa77c903,0xfc78c903,0xd25ec983,0x127823983,0x127833a03,0xca61ca03,0x1297f3c83,0x129803d03,0x12b6a3303,0x12b6b3383,0x11485ca83,0x12d6d3303,0x12d6e3383,0x11e86cb03,0x12f6d3503,0x12f6e3583,0x11e8bcb83,641,897,0x401,0x481]
def tableP1038_3 : List Nat := [0x162833b9c04,0x1628d3b9f04,0x1628d419f04,0x166853c9c04,0x1668f3c9f04,0x1668f429f04,0x2dc1,0x2e01,0x2f01,0x3001,0x3081,0x65b102,0x65b182,0x65b202,0x69b302,0x69b382,0x76b982,0x76ba02,0x7ebc82,0x7ebd02,0x7ebd82,0x8ac382,0x8ac402,0x8fc602,0x8fc682,0x8fc702,0x4801,0x793802,0x7a3882,0x654882,0x4941,0x7cbb02,0x7d3bc2,0x7e3c42,0x694982,0x654a02,0x32c1,0x4881,0x4a01,0xf8af102244,0x2bce0204aa705,0x1f02,0x3ec002,0x1f41,0x1c41,1,0x901,0x3401,0x3601,0x3781,0x34c1,0x4981,0xb14ca883,0x58a082,0x58a0c2,0x2c41,129,0xc81,0xf81,0x1101,0x1281,0x3a81,0x4201,0x3b41]
def tableP1038_4 : List Nat := [0x3e41,0xf0854183,0x784282,0xf0864103,0x784302,0x47c1,0x3f41,0x3c41,0x4281,0x4301,0x4b01,0x1f6b379a684,0x1f6b37aa584,0xfb59a683,0xb34da3c3,0xfb59a583,0x7dacc2,0x89c542,0x2b9402,0x8b15c2,0x773982,0x3b81,0x3e81,0x2cc1,257,0x1581,0x4481,0x4581,0x4541,0x4b81,0x4a81,0x3701,0x36c1,0x3301,0x3501,0x33c1,0x35c1]

def encodedP1038 (i : Nat) : Nat :=
  if i < 128 then
    if i < 64 then
      tableP1038_0.getD (i%64) 0
    else
      tableP1038_1.getD (i%64) 0
  else
    if i < 192 then
      tableP1038_2.getD (i%64) 0
    else
      if i < 256 then
        tableP1038_3.getD (i%64) 0
      else
        tableP1038_4.getD (i%64) 0
def bookP1038 (i : Nat) : Clause := let n := encodedP1038 i; unpackLits 9 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClausesP1038 : inputsOK 1 1038 aP1038 rP1038 (baseBook bookP1038 188).toList=true := by decide +kernel

def rowsP1038_0 : List Nat := [0x40401,0xc0801,0xc0a01,0x180e01,0x90c201,0x90c401,0x90c601,0xd0ca01,0xd0cc01,0xd0ce01,0x1a0d202,0x5e1a0d402,0x5f9acd802,0x5e9b4dc02,0x5f1b4de02,0x20e201,0x24e401,0x28e601,0x2cea01,0x30ec01,0x3cfe01,0x410401,0xe11201,0xe51801,0xed2001,0x953401,0x993801,0xd54001,0xd94201,0xdd4401,0x64b194602,0x3694801,0x3694a01,0x31d4c01,0x369ad5202,0x3795401,0x3795601,0x3795801,0x3215a01,0x3296001,0xcd6632ce003,0x391ba01,0x391c601,0x10c963d260f89c402f17ca009,0x1007e5d269307a05,0x104b03d2c8f8ba4e25ba0b64f2139c1c3c1d170b411,0x10c7c592a0fa8d73395b608,0x863e2c54e91752491a7d73395b80b,0x3ac7401,0x3add201,0x3b41a01,0x3b8ee01,0x3b8f201,0x3b8f601,0xcf673bce803,0x3c9c401,0x249198253293ac8806,0x2292982572b145e85423bac880a,0x4828910a4452b12580c275bb0aa0b,0x3d5ec01,0x3dcc001,0x3e02201,0x3e42e01,0x3e43a01,0x3e44601,0x3e50a01,0x3e53001,0xd1683f4fc03,0x3fdbe01,0x204247e0aabd2cfa7ebcc2809,0x108123f04d5c9449c05fcf37ebe82c0c,0x210307e0cab92afb7ebcc3809,0x102183f06d5e9749c0dfcf37ebec340c,0xd96c35d3e03,0x8669b49a803,0x419c201,0x41e0401,0x41e0801,0x82c257002,0x8662a38944975c011607,0x866221c8c4575c011e07,0x1890b253ad1004,0x11890c462bac8805,0x1870c233b11604,0x10cc3451208e4487a3e1d0d803b1100c,0x6b3553202,0x2b170a0602a168cc6207,0x522e140c8589d4ca6e249e198b45e0c,0xb078241f0a20102fc7d41c440a,0x503c121085906843f451f8fa83bf4400d,0x455c001,0x45a2001,0x45cc801,0x4604e01,0x4653c01,0x4662601]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOkP1038_0 : checkRows bookP1038 9 188 rowsP1038_0=true := by decide +kernel

def rowsP1038_1 : List Nat := [0x46a2201,0x82c6d7602,0x844716a02,0x1e0e8ba5bc79e0ef8ec296609,0x78c7cf402,0x854816c02,0x8ec817202,0x77c84e802,0x78488f002]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOkP1038_1 : checkRows bookP1038 9 284 rowsP1038_1=true := by decide +kernel

def lastUnitsP1038 := digits 9 3 0x47a4724
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflictP1038 : checkReasons bookP1038 293 180 lastUnitsP1038 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem excludeP1038 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 1038=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=1) h hc bp eq (by decide +kernel)
  let v := truth Z aP1038
  have hbase : ValidThrough v bookP1038 188 := book_start Z h hc z eq _ _ _ _ initialClausesP1038
  have h0 : ValidThrough v bookP1038 284 := rows_sound hbase rowsP1038_0 rowsOkP1038_0
  have h1 : ValidThrough v bookP1038 293 := rows_sound h0 rowsP1038_1 rowsOkP1038_1
  exact book_end h1 _ _ conflictP1038
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def aP1216 := ([0x20021,0x20821,0xa00a1,0x200a1,0x800a1,0xa08a1,0x208a1,0x808a1,0x60a7,0x260a7,0x50a8,0x8050a8,0x200c1,0xa00c1,0x10c7,0x1805,0x21805,0x21806,0x6805,0x26805,0x26806,0xa6806,0x8805,0x28806,0xa8806,0x1825,0x21825,0x6825,0x26825,0x8825,0x28825,0x6864,0x8864,0x89a4] : List Nat).toArray.map readPackedFact
def rP1216 := ([32,0x820,160,0x8a0,0x60a5,0x1808a9,0x1820a9,0x9808a9,0x9820a9,0x50a6,0x250aa,0x850aa,0x200250aa,0x200850aa,0x10c5,0x408c9,0x428c9,0x1810,0x20801812,0x20821812,0x6810,0x806812,0x22806812,0x826812,0x22826812,0x8810,0x808812,0x2808812,0x1830,0x6830,0x8830,0x209a1813,0x1a1834,0x9a1834,0x20a21813,0x221834,0xa21834,0x22a26813,0x226834,0xa26834] : List Nat).map readPackedScheme

def tableP1216_0 : List Nat := [65,193,321,705,0x26442,0xc402,0x10402,0x18482,0x1c482,0x2e542,0xc502,0x12502,0x18582,0x1e582,0x741,0x30702,0x34702,0x427c2,0x2300783,0x2304803,0x4e942,0x280e903,0x2b08903,0x281a983,0x2b14983,0xb41,0x2e32b03,0x3036b03,0x6acc2,0x72dc2,0x7aec2,0x2944f83,0x3f6cc83,0x3f70d03,0x2f45003,0x4174c83,0x4178d03,0x3155083,0x4374d83,0x4378e03,0x601,0x681,0x46782,0x46802,0x56902,0x56982,0xb81,0xc01,0x45002,0x55082,0xac1,0x1081,0x8c1,0x1001,385,769,0xa01,0xf81,0xf01,0xec1,0xc81,0xd81,0xd41,0xe41]

def encodedP1216 (i : Nat) : Nat :=
  tableP1216_0.getD (i%64) 0
def bookP1216 (i : Nat) : Clause := let n := encodedP1216 i; unpackLits 7 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClausesP1216 : inputsOK 0 1216 aP1216 rP1216 (baseBook bookP1216 40).toList=true := by decide +kernel

def rowsP1216_0 : List Nat := [0x71e01,0x72001,0x2401,0xa601,0x12c01,0x1b001,0x50cb402,0x52cb602,0x174401,0x17ca01,0x5b62802,0x196201,0x5752202,0x1a6001,0x41221429a05,0x31221839605,0x2eaefb2804,0x69c3e02,0xeb93c9ce7ac007,0x1d3c01,0x6bdc602,0x67dcc02,0x1e3801,0x1eba01]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOkP1216_0 : checkRows bookP1216 6 40 rowsP1216_0=true := by decide +kernel

def lastUnitsP1216 := digits 6 3 0x39ffe
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflictP1216 : checkReasons bookP1216 64 33 lastUnitsP1216 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem excludeP1216 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 1216=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=0) h hc bp eq (by decide +kernel)
  let v := truth Z aP1216
  have hbase : ValidThrough v bookP1216 40 := book_start Z h hc z eq _ _ _ _ initialClausesP1216
  have h0 : ValidThrough v bookP1216 64 := rows_sound hbase rowsP1216_0 rowsOkP1216_0
  exact book_end h0 _ _ conflictP1216
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def aP1220 := ([0x2002,0x4002,0x6802,0x20021,0x20821,0x21021,0x20041,0x80041,0x1047,0x80081,0x880,0x20081,0xa0081,0x100081,0x4083,0x80881,0x1080,0x20881,0xa0881,0x100881,0xa1081,0x101081,0x4887,0x24887,0x44887,0x5887,0x25887,0x45887,0x45088,0x845088,0x1045088,0x102009,0xa00a1,0xa08a1,0xa10a1,0x900,0x120101,0x1a0101,0x6903,0x1100,0x120901,0x1a0901,0x121101,0x1a1101,0xd907,0x2d907,0x4d907,0x341108,0xb41108,0x1341108,0x3a3108,0xba3108,0x13a3108,0x1a4009,0x1a0141,0xc147,0x1a01a1,0x1a09a1,0x11a0,0x2005,0x22005,0x42005,0x22006,0x3005,0x23006,0x83006,0x5005,0x25005,0x45005,0xa5006,0x6005,0x26005,0x46005,0x26006,0x86006,0x7005,0x27005,0x47005,0xa7006,0x2025,0x22025,0x42025,0x3025,0x23025,0x43025,0x5025,0x1a5026,0x6025,0x26025,0x46025,0x1a6026,0x7025,0x3084,0x6084,0x60c4,0x6144,0x7144] : List Nat).toArray.map readPackedFact
def rP1220 := ([32,0x820,0x1020,0x1045,0x40849,0x42049,128,0x880,0x881,131,0x4885,0x120889,0x122889,0x920889,0x922889,0x44887,0x5885,0x162889,0x164089,0x962889,0x964089,0x1162889,0x1164089,0x45086,0x10a508a,0x110508a,0x210a508a,0x2110508a,0x410a508a,0x4110508a,0x10200c,0x408e,0x80408f,0x100408f,0x102408f,160,0x8a0,0x10a0,0x901,0xd905,0x364909,0x366909,0xb64909,0xb66909,0x4d907,0x1364909,0x1366909,0x341106,0xd1a110a,0x2d1a110a,0x1341108,0x3a3106,0xe92310a,0xe9a310a,0x2e92310a,0x2e9a310a,0x13a3108,0x4e92310a,0x4e9a310a,0x1a400b,0x1a400c,0x4690d,0x80690f,0x100690f,0x102690f,0xc145,0x306949,416,0x9a0,419,0x2010,0x20802012,0x20822012,0x20842012,0x3010,0x803012,0x2003012,0x5010,0x2805012,0x2825012,0x45011,0x6010,0x806012,0x22006012,0x826012,0x22026012,0x46011,0x7010,0x22807012,0x22827012,0x22847012,0x2030,0x42031,0x3030,0x43031,0x5030,0x6805032,0x6030,0x26806032,0x26826032,0x46031,0x7030,0x208c2013,0xc2034,0x8c2034,0x20982013,0x182034,0x982034,0x2183013,0x183034,0x983034,0x185014,0x985014,0x6985033,0x29c5013,0x1c5034] : List Nat).map readPackedScheme

def tableP1220_0 : List Nat := [449,577,705,0x441,0x30402,0x38402,0x4c1,0x7c1,0x54802,0x4802,0xc4bcb43,0x58b02,0x60b02,0x88b82,0x90b82,0x84c02,0xdcd4cc3,0x60c82,0x68c82,0x90d02,0x98d02,0xa0d82,0xa8d82,0xf4ece43,0x64e02,0x68e02,0x94e82,0x98e82,0xa4f02,0xa8f02,0x8f82,0x7408003,0xfc9c6c50705,0xfcac6c80705,0xfcac9c80705,0x1041,0x10c1,0x1141,0x11d382,0x1756d643,0x121602,0x129602,0x141682,0x149682,0x13d702,0x151702,0x159702,0x18d857c3,0x12d782,0x14d802,0x13d882,0x1a59d943,0x125902,0x129902,0x145982,0x149982,0x13da02,0x155a02,0x159a02,0xda82,0x11a82,0x1341,0x1ad4d2d19305,0x1ad5d2d39305]
def tableP1220_1 : List Nat := [0x1ad5d4d39305,0x1bc1,0x1b1b82,0x1c41,0x1cc1,0x15d02,0x1ede5dc3,0x1f419d83,0x1f421e03,0x1f429e83,0x1fc1,0x20035f83,0x2083df83,0x2261e143,0x22866103,0x22896183,0x86202,0x2463e343,0x2485e303,0x2544a303,0x2488e383,0x2547a383,0x86402,0x26e665c3,0x27502583,0x2750a603,0x27512683,0x28e867c3,0x1d6882,0x2a69e943,0x1d6a02,0x2ac1,0x2b1b6a83,0x2cec6bc3,0x2d5c2b83,0x2d5cac03,0x1d6c82,0x2dc1,0x205f2e03,0x2e692783,0x2e69a803,0x24df2e83,0x2eeba783,0x2eec2803,0x2520ef03,0x2f6ba903,0x2f6c2983,0x2fe32103,0x2fe3a183,0x2d2b6f83,0x2722f003,0x306daa83,769,897,0x1ad4d2d184,0x1ad5d2d384,0x1ad5d4d384,0x1b01,0x1f5d82,0x1f5e02,0x1f5e82,0x2001,0x2081,0x256302]
def tableP1220_2 : List Nat := [0x256382,0x276582,0x276602,0x276682,0x2b01,0x2d6b82,0x2d6c02,0x1f2e02,0x252f02,0x2d2f82,0x3041,0x1f41,0x2e01,0x1ada02,0x1ad602,0x1ad682,0x1ac1,193,257,0xf81,0x1d01,0x2881,0x2a01,0x2c81,0x2d41,0x2f81,0x80d82,0x80c82,0x801,0xc01,0x2201,0x2401,0x2541,0x2f01,0x2741,0x22c1,0x2eeb82,0x2eec02,0x2ec1,0x24c1,0xb81,0xb41,0x581,0x601,0x2301,0x2101,0x23c1,0x21c1]

def encodedP1220 (i : Nat) : Nat :=
  if i < 64 then
    tableP1220_0.getD (i%64) 0
  else
    if i < 128 then
      tableP1220_1.getD (i%64) 0
    else
      tableP1220_2.getD (i%64) 0
def bookP1220 (i : Nat) : Clause := let n := encodedP1220 i; unpackLits 8 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClausesP1220 : inputsOK 1 1220 aP1220 rP1220 (baseBook bookP1220 116).toList=true := by decide +kernel

def rowsP1220_0 : List Nat := [0x60801,0x60a01,0x7a7c01,0x7a7e01,0x7a8001,0x828401,0x8e01,0x29001,0x49201,0xe8949602,0xea949802,0xca601,0xeaa01,0x46b001,0x48b201,0x4ab401,0xf2bec002,0x86c401,0x88c601,0xfacc01,0xfcd801,0x108e201,0xcabee602,0xf8f6f48c03,0x1170e01,0x56525af0ee7472704e08,0x4c5eec626e66606852511a640b,0x4c5eec606a66626c56551a640b,0x6e6af0ee5c584f1f1d1a660a,0x1207601,0x1207801,0x1223c01,0x1248a01,0x128b801,0x128bc01,0x128c801,0x10d0b2ec203,0x1311201,0x32364244382c2a3e1327222e0b,0x3a364240302422103e1327222e0c,0x323a40443428262137343e121127222e0f,0x1381e01,0x138a001,0x138ac01,0x100ff3ea203,0x1411001,0x1070502ae03,0x11544e402,0xbab6dad5432b2d18d008,0xbab6dcd7432b2d18ce08,0xc3492f4a03,0x1174cd202,0x9aa29ea81c1b333d3f474ede0b,0x13b501402,0x1521601,0x1521801,0x14f54a402,0x147569c02,0x13f58a202,0x13d5a9a02]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOkP1220_0 : checkRows bookP1220 8 116 rowsP1220_0=true := by decide +kernel

def lastUnitsP1220 := digits 8 3 0x99aeaf
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflictP1220 : checkReasons bookP1220 176 112 lastUnitsP1220 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem excludeP1220 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 1220=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=1) h hc bp eq (by decide +kernel)
  let v := truth Z aP1220
  have hbase : ValidThrough v bookP1220 116 := book_start Z h hc z eq _ _ _ _ initialClausesP1220
  have h0 : ValidThrough v bookP1220 176 := rows_sound hbase rowsP1220_0 rowsOkP1220_0
  exact book_end h0 _ _ conflictP1220
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def aP1290 := ([0x2802,0x3002,0x4802,0x6802,0xa0021,0x827,0xa00a1,0x30a3,0xa08a1,0x10a0,0x8c0,193,0xa00c1,0x48c3,0x1a00c1,0x68c3,0x10c0,0x8c1,0xa08c1,0x1a08c1,0x10c1,0xa10c1,0x1a10c1,0x48c7,0x248c7,0x448c7,0xf0c7,0x2f0c7,0x4f0c7,0x110c7,0x310c7,0x510c7,0x40c8,0x8040c8,0x10040c8,0x3040c8,0xb040c8,0x13040c8,0x4040c8,0xc040c8,0x14040c8,0xa3009,0x1a3009,0xe00e1,0xe08e1,0xe10e1,0x120101,0x160101,0x2107,0x4907,0x120121,0x920,288,0xc0121,0xe0121,0x160121,0x5923,0x180121,0x120921,0x1120,0xc0921,0xe0921,0x160921,0x180921,0x121121,0xc1121,0xe1121,0x161121,0x927,0x20927,0x40927,0x5127,0x25127,0x45127,0x6927,0x26927,0x46927,0x280928,0xa80928,0x1280928,0xc4809,0x120141,0x180141,0x2147,0x6147,0x160161,0x960,0xe0161,0x120161,0x160961,0x1160,0xe0961,0x120961,0x161161,0xe1161,0x121161,0x8167,0x28167,0x48167,0x10967,0x30967,0x50967,0x281968,0xa81968,0x1281968,0x125809,0x180181,0x180981,0x181181,0xc01a1,0xe01a1,0x11a0,0xc09a1,0xe09a1,0x9a7,0x209a7,0x409a7,0x3209a8,0xb209a8,0x13209a8,0x1005,0x1805,0xa1806,0x2005,0x3805,0x4005,0x6805,0x26805,0x46805,0xa6806,0x7005,0x27005,0x47005,0x7805,0x27805,0x47805,0x8005,0x28005,0x48005,0x8805,0x28805,0x48805,0x9005,0x29005,0x49005,0x1025,0x21025,0x41025,0xe1026,0x1825,0x21825,0x41825,0xc1826,0xe1826,0x2025,0x22025,0x42025,0xc2026,0xe2026,0x3825,0x23825,0x43825,0xe3826,0x4025,0x24025,0x44025,0xe4026,0x6825,0x26825,0x46825,0x126826,0x186826,0x7025,0x127026,0x187026,0x7825,0x27825,0x47825,0x187826,0x8025,0x128026,0x168026,0x8825,0x28825,0x48825,0x128826,0x168826,0x9025,0x29025,0x49025,0x169026,0x1844,0x2044,0x2064,0x6864,0x40e4,0x71a4,0x79a4,0x79c4,0x8a04,0x9204,0x9224] : List Nat).toArray.map readPackedFact
def rP1290 := ([0x825,0x22829,160,0x8a0,163,0x30ae,0x8c1,195,0x48c5,0x1200c9,0x1228c9,0x9228c9,0x11200c9,0x11228c9,0xf0c5,0x3c28c9,0xbc00c9,0x13c28c9,0x110c5,0x4400c9,0x4468c9,0xc400c9,0xc468c9,0x14400c9,0x14468c9,0x40c6,0x40ca,0xa40ca,0x200040ca,0x200a40ca,0x400040ca,0x400a40ca,0x3040c6,0xc1a40ca,0x2c0040ca,0x4c1a40ca,0x4040c6,0x100040ca,0x101a40ca,0x301a40ca,0x500040ca,0x501a40ca,0xa300c,0x8028cf,0x10028cf,0x10228cf,0x48ce,0x1a300c,0x68ce,0x8068cf,0x10068cf,0x10268cf,224,0x8e0,0x10e0,0x2105,0x84909,0x4905,0x125909,288,289,0x5922,0x920,0x921,0x25922,0x1120,0x45922,291,0x925,0x23129,0x23929,0x823129,0x823929,0x1023129,0x1023929,0x5125,0x143929,0x145929,0x943929,0x945929,0x45127,0x6925,0x1a3929,0x1a6129,0x9a3929,0x9a6129,0x46927,0x280926,0xa0e092a,0xa16092a,0x2a0e092a,0x2a16092a,0x1280928,0xc480c,0x80312f,0x100312f,0x102312f,0x2145,0x84949,0x6145,0x186149,352,0x960,0x961,0x1160,0x8165,0x203969,0x204969,0xa03969,0xa04969,0x48167,0x1203969,0x1204969,0x10965,0x423969,0x30967,0x50967,0x281966,0xa0e196a,0xa12196a,0x2a0e196a,0x2a12196a,0x1281968,0x4a0e196a,0x4a12196a,0x12580c,0x80496f,0x100496f,0x102496f,384,0x980,0x1180,419,0x9a5,0x239a9,0x8239a9,0x409a7,0x3209a6,0xc8c09aa,0xc8e09aa,0x2c8c09aa,0x2c8e09aa,0x13209a8,0x1010,0x1810,0x2801812,0x2010,0x3810,0x4010,0x6810,0x22806812,0x22826812,0x46811,0x7010,0x47011,0x7810,0x47811,0x8010,0x48011,0x8810,0x48811,0x9010,0x49011,0x1030,0x23801032,0x23821032,0x23841032,0x1830,0x23001832,0x3801832,0x23021832,0x3821832,0x41831,0x23041832,0x3841832,0x2030,0x3002032,0x3802032,0x3022032,0x3822032,0x42031,0x3830,0x23803832,0x23823832,0x23843832,0x4030,0x3804032,0x24031,0x44031,0x6830,0x24806832,0x6006832,0x24826832,0x6026832,0x46831,0x7030,0x4807032,0x6007032,0x7830,0x26007832,0x26027832,0x26047832,0x8030,0x4808032,0x5808032,0x8830,0x24808832,0x5808832,0x24828832,0x5828832,0x48831,0x24848832,0x5848832,0x9030,0x25809032,0x25829032,0x25849032,0x61014,0x23861033,0x81014,0x23881033,0x81814,0x23081833,0x29a1813,0x1a1834,0x9a1834,0x103814,0x23903833,0x1c6814,0x9c6814,0x249c6833,0x1e6814,0x9e6814,0x61e6833,0x1e7014,0x9e7014,0x61e7033,0x228014,0xa28014,0x4a28033,0x248014,0xa48014,0x5a48033,0x248814,0xa48814,0x5a48833] : List Nat).map readPackedScheme

def tableP1290_0 : List Nat := [705,0x40282,833,0x441,0x8482,0xf010003,0xa8802,0x18802,0x33188bc3,0xb0b82,0xc0b82,0x120c02,0x140c82,0x150c82,0x391b8d43,0xc0d02,0x110d82,0x150e02,0x3f1e8ec3,0xb0e82,0xe0e82,0x110f02,0x130f02,0x140f82,0x160f82,0x45219043,0xb9002,0xc1002,0x119082,0x121082,0x149102,0x151102,0x4b2491c3,0xe1182,0x119202,0x161282,0x51279343,0xb9302,0xe1302,0x131382,0x149402,0x161402,0x1482,0x14c4a190a0385,0x14c5619100385,0x14c5625100385,0x1b020083,0x31502,0x1f030083,0x1544e1d0a0785,0x1545a1d100785,0x1545a27100785,0x15c1,0x1641,0x16c1,0x1841,0x2e1802,0x18c1,0x2f1882,0x1941,0x349982,0x71371a03,0x1d41,0x339d82]
def tableP1290_1 : List Nat := [0x713e1983,0x2041,0x71431d83,0x29d82,0x8d45a243,0x352202,0x362202,0x3c2282,0x3d2282,0x412302,0x422302,0x9348a3c3,0x362382,0x372382,0x3d2402,0x3e2402,0x3ba482,0x994ba543,0x362502,0x392502,0x3d2582,0x3f2582,0x3ba602,0x9f4ea6c3,0x36a682,0x372682,0x3da702,0x3e2702,0x3ba782,0x12802,0x284f26b330685,0x285066b3b0685,0x28506793b0685,0x29c1,0x512982,0x2a41,0x522a02,0x2ac1,0x2cc1,0x56ad02,0x2ec1,0xc561b043,0x573002,0x583002,0x5b3082,0x5c3082,0x5ab102,0x5e3102,0x5f3102,0xcb64b1c3,0x573182,0x56b202,0x5ab282,0xd167b343,0x57b302,0x583302,0x5bb382,0x5c3382,0x5ab402,0x5eb402,0x5f3402,0x23482,0x34d72b1561c05,0x34d7eb15a1c05]
def tableP1290_2 : List Nat := [0x34d7eb95a1c05,0x3541,0x35c1,0x3641,0x3b782,0xe973b943,0x6e3902,0x713982,0x6fba02,0xef76bac3,0x6d3a82,0x6eba82,0x703b02,0x71bb02,0x6fbb82,0x3c41,0x3cc1,0xf404bc83,0x3dc1,0x3e41,0x3ec1,0x1017fbf43,0x103063f03,0x103083f83,0x9c002,0x10983c143,0x9c202,0x10f86c2c3,0x9c382,0x11589c443,0x10c502,0x11b8cc5c3,0x10c682,0x1218fc743,0x10c802,0x12792c8c3,0x1292b4883,0x1292c4903,0x1292d4983,0x12f96cac3,0x131354a83,0x13236ca83,0x1313c4b03,0x1323dcb03,0x3bcb82,0x131414b83,0x13242cb83,0x1399bcd43,0x13a6dcd03,0x13c6ecd03,0x13a70cd83,0x13c71cd83,0x6fce02,0x143a0cfc3,0x1452b4f83,0x1452c5003,0x1452d5083,0x14ba4d1c3,0x14c57d183,0x56d202,0x5ad282,0x153a8d3c3,0x155325383,0x15639d383]
def tableP1290_3 : List Nat := [0x1553a5403,0x1563fd403,0x3bd482,0x5641,0x15a51d603,0x15c52d603,0x163b0d7c3,0x1656a5783,0x1656b5803,0x1656c5883,0x59c1,0x1682ed983,0x16a2fd983,0x171b7db43,0x173325b03,0x17437db03,0x1733a5b83,0x1743edb83,0x3bdc02,0x173405c03,0x17443dc03,0x17bbcddc3,0x17d555d83,0x17d595e03,0x17d5d5e83,0x17f793c03,0x133945f83,0x1817b3c03,0x13d946003,0x1837b3c83,0x13b986083,0x1027ae103,0x185a74a83,0x185a84b03,0x1877d3e03,0x14da26183,0x189823f03,0x189833f83,0x15baa6203,0x18b853f03,0x18b863f83,0x164abe283,0x18d854103,0x18d864183,0x164aee303,0x18f8b4403,0x18f8c4483,0x172b4e383,0x1918e4403,0x1918f4483,0x17cb5e403,0x1938e4583,0x1938f4603,0x17cbae483,513,0x1701,0x1781,0x2881,0x2901,0x3d01,0x81bf02,0x81bf82,0x94c882,0x94c902]
def tableP1290_4 : List Nat := [0x94c982,0xa2cf82,0xa2d002,0xa2d082,0xaad382,0xaad402,0x5681,0x5701,0xb2d782,0xb2d802,0xb2d882,0x5a01,0x5a81,0xb9db02,0xb9db82,0xb9dc02,0xbedd82,0xbede02,0xbede82,0x5fc1,0x99ca02,0x6041,0x9eca02,0x60c1,0x9dcc02,0x816102,0x61c1,0xa6d102,0xaa6202,0xb26302,0xb96382,0xbe6402,0x5f41,0x6401,0x5cc1,0x6381,0x5941,0x6301,0x34ce0b460b405,0x34ce0ac68b085,0x1a6705a3044,0xd3382d03,0x1a670a63004,0xd3383083,0x5141,0x5341,0x1743b1c43,0x699c02,0xba1d82,0x3b9f02,0x5d01,0x6481,0xaa200f1404,0x154281e288e85,0xaa200f0f04,0x30802,0x10c782,0x841,0x541,193,385,0x2801,0x3781,0x3a01]
def tableP1290_5 : List Nat := [0x3b81,0x4e01,0x178643,0x228603,0x1142,1,0x481,0x4001,0x4201,0x4381,0x40c1,0x6101,0x4a41,0x4cc1,0x4f41,0x9d4d82,0x9d4d02,0x4e81,0x4c01,0x189c5c303,0xc4e2c2,0x3b9e82,0x1dc1,0x19c1,321,0x6c1,0x449ac2,0x96a242,0x4b41,0x1ec1,0x1e01,0x2281,0x20c1,0x1ac1,0x2301,0x2201]

def encodedP1290 (i : Nat) : Nat :=
  if i < 192 then
    if i < 64 then
      tableP1290_0.getD (i%64) 0
    else
      if i < 128 then
        tableP1290_1.getD (i%64) 0
      else
        tableP1290_2.getD (i%64) 0
  else
    if i < 256 then
      tableP1290_3.getD (i%64) 0
    else
      if i < 320 then
        tableP1290_4.getD (i%64) 0
      else
        tableP1290_5.getD (i%64) 0
def bookP1290 (i : Nat) : Clause := let n := encodedP1290 i; unpackLits 9 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClausesP1290 : inputsOK 1 1290 aP1290 rP1290 (baseBook bookP1290 246).toList=true := by decide +kernel

def rowsP1290_0 : List Nat := [513,0xdc7001,0xe47401,0x184c401,0x18cc801,0x7b2412202,0x92c01,0xd2e01,0xd14801,0xd54a01,0xd94c01,0xd16c01,0xd56e01,0xd97001,0xed7c01,0xf98001,0x7cb0d8802,0x7d30d8a02,0x2058e01,0x2099001,0x20d9201,0x7bb299602,0x7c3299802,0xed9c01,0xf9a001,0x105a601,0x195ac01,0x199ae01,0x1a1b001,0x4823db202,0x44db401,0x4923db602,0x455b801,0x49241ba02,0x45dbc01,0x3edbe01,0x4a24dc402,0x469c601,0x419cc01,0x41dd801,0x42dde01,0x431e401,0x11288c41aa03,0x4823e01,0x10f874359a03,0x48a3c01,0x10a84c218c03,0x4923a01,0x1a5006f3e1ecda05,0x1d4fc78369b0ee05,0x1e4ee803f9c0d3279319cea09,0x1f0f27f3f1d8d66a9419cea09,0xbb3cae4eaba3b1acd47a5e4a4fc0b,0x3b1c4ea733c49cd8743d4a4e40a,0x103814056a03,0x4b23601,0x19ed16a0f480421e0fd9a08,0x1ba552b94cb4d205,0x12e3e90e5e03,0x4c2b92cb64f28170b007,0x138ae4b2c9359ecd68cc5a45c284c0b40d,0x904c9ea02,0x140b0c86617148a02407,0x9062250a04c4e05,0x4223188cc44160a8184008,0x984e321986025369acd06007030bc480d,0x27d3af478a79412399c85da09,0x13e9d79bc14338512813d2399c85dc0c,0x4e40c01,0x4e40e01,0x4e66e01,0x4ecba01,0x4f10801,0x4f91001,0x4f91c01,0x4f96801,0x34162c158a80b399d4ec1009,0x1c2d0807438190d83c54059ccec220c,0xc8243b4215d0c54059d4ec340a,0x140b160b4181f0f5100a2a9ccec100c,0x5140801,0x5193001,0x5193401,0x5193801,0xfd7e51d2a03,0x52a3201,0x1007fbf94603,0x5322801,0x5322c01,0x45a151287462cd654ea04fd0c0a,0x46a151286452c5614ea04fd0e0a,0xafa7d06a003,0x5463001,0x994abadd148a3c95c807,0x4ca55d4e74dd4e9325a3d21ca0a,0x3a638bf822f5c2a75494c9851259509c502b2b18524a5d36a815]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOkP1290_0 : checkRows bookP1290 9 246 rowsP1290_0=true := by decide +kernel

def rowsP1290_1 : List Nat := [0xaa3063855829457a52701614e575596aaac256170ad24a5d35d216,0x5587e01,0x5588601,0x9dd605c02,0x8e492f17eaf599ed588808,0x11c9460572b54ea8ad55ab33da6d48880d,0xad5497c8c45add4a9b56accf54e0b,0xa6d715602,0xa95715402,0x5749001,0x27b59ab578c004,0x27b59abd78bc04,0x5809201,0x5848a01]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOkP1290_1 : checkRows bookP1290 9 342 rowsP1290_1=true := by decide +kernel

def lastUnitsP1290 := digits 9 3 0x57ec762
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflictP1290 : checkReasons bookP1290 356 68 lastUnitsP1290 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem excludeP1290 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 1290=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=1) h hc bp eq (by decide +kernel)
  let v := truth Z aP1290
  have hbase : ValidThrough v bookP1290 246 := book_start Z h hc z eq _ _ _ _ initialClausesP1290
  have h0 : ValidThrough v bookP1290 342 := rows_sound hbase rowsP1290_0 rowsOkP1290_0
  have h1 : ValidThrough v bookP1290 356 := rows_sound h0 rowsP1290_1 rowsOkP1290_1
  exact book_end h1 _ _ conflictP1290
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def aP2087 := ([0x4802,0x4822,0x5002,0x5022,0x6802,0x6822,0x20021,0x80021,0x827,0x20041,0x80041,0x1047,0x80081,0x80881,0x81081,0x81881,0x920,0xe0121,0x140121,0x5123,0x1a0121,0x6923,0x1120,0xe0921,0x140921,0x1a0921,0x1920,0xe1121,0x141121,0x1a1121,0xe1921,0x141921,0x9127,0x29127,0x49127,0x69127,0xe127,0x2e127,0x4e127,0x6e127,0x10927,0x30927,0x50927,0x70927,0x2e0928,0xae0928,0x12e0928,0x1ae0928,0x102928,0x902928,0x1102928,0x1902928,0x3a2928,0xba2928,0x13a2928,0x1ba2928,0x144809,0x144829,0x1a4809,0x1a4829,0x940,0x100141,0x120141,0x180141,0x1a0141,0x6943,0x1140,0x100941,0x120941,0x180941,0x1a0941,0x1940,0x101141,0x121141,0x181141,0x1a1141,0x2947,0x22947,0x42947,0x62947,0x7147,0x27147,0x47147,0x67147,0xd147,0x2d147,0x4d147,0x6d147,0xe0148,0x8e0148,0x10e0148,0x18e0148,0x2c0148,0xac0148,0x12c0148,0x1ac0148,0x3a0148,0xba0148,0x13a0148,0x1ba0148,0x2c2948,0xac2948,0x12c2948,0x1ac2948,0x422948,0xc22948,0x1422948,0x1c22948,0x462948,0xc62948,0x1462948,0x1c62948,0x125009,0x125029,0x1a5009,0x1a5029,0x11a0,0x19a0,0x2005,0x22006,0x82006,0x3005,0x23006,0x83006,0x6005,0x26005,0x46005,0x66005,0x86006,0x2025,0x22025,0x42025,0x62025,0x3025,0x23025,0x43025,0x63025,0x6025,0x26025,0x46025,0x66025,0x3084,0x6084,0x60c4] : List Nat).toArray.map readPackedFact
def rP2087 := ([32,0x825,0x22029,0x1045,0x40849,0x42049,128,0x880,0x1080,0x1880,0x921,0x1121,292,0x924,0x9125,0x243929,0x245129,0xa43929,0xa45129,0x49127,0x1243929,0x1245129,0x69127,0x1a45129,0xe125,0x385129,0x386929,0xb85129,0xb86929,0x1385129,0x1386929,0x6e127,0x10925,0x425129,0xc25129,0x1425129,0x1c23929,0x2e0926,0xb8e092a,0xb94092a,0x2b8e092a,0x2b94092a,0x12e0928,0x4b8e092a,0x4b94092a,0x1ae0928,0x6b8e092a,0x6b94092a,0x102926,0x414292a,0x2414292a,0x1102928,0x1902928,0x3a2926,0xe94292a,0xe9a292a,0x2e94292a,0x2e9a292a,0x4e94292a,0x4e9a292a,0x1ba2928,0x14480c,0x14482c,0xa512d,0x80512f,0x100512f,0x180512f,0x102512f,0x182512f,0x184512f,0x1a480b,0x1a480c,0x1a482b,0x1a482c,0x2692d,0x80692f,0x100692f,0x102692f,0x941,324,0x944,0x2945,0xa4149,0xa4949,0x8a4149,0x8a4949,0x10a4149,0x10a4949,0x62947,0x7145,0x1c4149,0x1c6149,0x9c4149,0x9c6149,0x47147,0x11c4149,0x11c6149,0x67147,0xd145,0x346949,0xb44149,0xb46949,0x1344149,0x1346949,0x6d147,0xe0146,0x390014a,0x2390014a,0x10e0148,0x18e0148,0x2c0146,0xb18014a,0x2b10014a,0x4b10014a,0x1ac0148,0x3a0146,0xe90014a,0xe92014a,0xe9a014a,0x2e90014a,0x2e92014a,0x2e9a014a,0x4e90014a,0x4e92014a,0x4e9a014a,0x1ba0148,0x2c2946,0xb10294a,0xb18294a,0x2b10294a,0x2b18294a,0x12c2948,0x4b18294a,0x1ac2948,0x422946,0x1098294a,0x309a294a,0x5098294a,0x1c22948,0x462946,0x1190294a,0x3198294a,0x519a294a,0x1c62948,0x12500b,0x12500c,0x12502b,0x12502c,0x80494f,0x100494f,0x102494f,0x1a500b,0x1a500c,0x694e,0x1a502b,0x1a502c,0x2694e,0x80694f,0x100694f,0x102694f,419,0x9a4,0x2010,0x20802012,0x2002012,0x3010,0x803012,0x2003012,0x6010,0x22006012,0x22026012,0x22046012,0x22066012,0x2030,0x42031,0x62031,0x3030,0x43031,0x63031,0x6030,0x46031,0x66031,0x208c2013,0xc2034,0x8c2034,0x2182013,0x182034,0x982034,0x2183013,0x183034,0x983034] : List Nat).map readPackedScheme

def tableP2087_0 : List Nat := [833,0x441,0x70402,0x5c1,0x90582,0xa0582,0x641,0x6c1,0x741,0x7c1,0x108b02,0x168d02,0x8d02,0x18d02,0x8e45219044,0x111002,0x121002,0x171082,0x181082,0x169102,0x1b1102,0x1c1102,0x1a9182,0x1f1182,0x9e4d259244,0x121202,0x141202,0x181282,0x191282,0x1c1302,0x1d1302,0x1a9382,0xae55299444,0x121402,0x181482,0x1c1502,0x1e1582,0xbe5d2d9644,0x119602,0x121602,0x179682,0x181682,0x169702,0x1b9702,0x1c1702,0x1a9782,0x1e9782,0x1f1782,0xce65319844,0x129802,0x189882,0x169902,0x1a9982,0xde6d359a44,0x129a02,0x141a02,0x189a82,0x191a82,0x1c9b02,0x1d1b02,0x1a9b82,0x21c02,0x31c82,0x9c1]
def tableP2087_1 : List Nat := [0x399c46225100986,0x399c47225160986,0x399c47e251a0986,0x399c47231160986,0x399c47e311a0986,0x399c47e391a0986,0x9d02,0x41d02,0x19d82,0x51d82,0xac1,0x3b9d46629100a86,0x3b9d47629160a86,0x3b9d47633160a86,0x3ca102,0x2a382,0x3a382,0x13e9d4da644,0x3d2602,0x3e2602,0x432682,0x442682,0x482702,0x492702,0x47a782,0x14ea551a844,0x3d2802,0x3f2802,0x432882,0x452882,0x42a902,0x482902,0x4a2902,0x47a982,0x15ead55aa44,0x402a02,0x432a82,0x462a82,0x482b02,0x4b2b02,0x47ab82,0x16eb559ac44,0x3dac02,0x43ac82,0x42ad02,0x47ad82,0x17ebd5dae44,0x3f2e02,0x43ae82,0x48af02,0x47af82,0x18ec561b044,0x3db002,0x3e3002,0x403002,0x43b082,0x443082,0x463082,0x48b102,0x493102,0x4b3102,0x47b182,0x19ecd65b244,0x3d3202]
def tableP2087_2 : List Nat := [0x3fb202,0x433282,0x45b282,0x42b302,0x4ab302,0x47b382,0x1aed569b444,0x3fb402,0x463482,0x4ab502,0x47b582,0x1bedd6db644,0x3d3602,0x45b682,0x4b3702,0x47b782,0x2b802,0x3802,0x3b882,0x13882,0x71b85127d3c0986,0x71b85267d420986,0x71b852689420986,0x2b902,0x43902,0x83040103,0x3b982,0x53982,0x83050183,0x73b951a813c2086,0x73b952e81422086,0x73b952e8d422086,0xb04ba03,0x5ba82,0x3b41,0xef063b03,0xf007bb03,0x3cc1,0xf409bc83,0xf60abc83,0x1fefd7dbe44,0x1010c3e03,0x1010d3e83,0x1010e3f03,0x1010f3f83,0x2130782c0c4,0x74c182,0x75c202,0x2230f86c2c4,0x74c382,0x75c402,0x233178ac4c4,0x74c582,0x75c602,0xf5774683,0x11b854083,0x11b864103,0x10078c703,0x11d894083,0x11d8a4103,0x1007bc783,0x11f894283,0x11f8a4303,897]
def tableP2087_3 : List Nat := [0x481,0x501,0x1cce231128805,0x1cce239128b05,0x1cce23f128d05,0x1cce239188b05,0x1cce23f188d05,0x1cce23f1c8d05,0x1dcea33148805,0x1dcea3b148b05,0x1dcea3b198b05,0x38dc2893e9e05,0x38dc2933ea105,0x38dc29344a105,0x3bc1,0x3c01,0x3d01,0x3d81,0x80be02,0x80be82,0x80bf02,0x80bf82,0x4681,0x854082,0x864102,0x804702,0x804782,0x4041,0x4701,0x4781,0x351c0c03,0xe2e2188944,0x71710e03,0xe2e22c8c44,0x71711643,0x38b882,0x3b92c584f199d46,0x38d3ee1423105,0x38d1ee160a105,0x38d1ee1519ec5,0x1c68f70a8c4,0x1c68f70b004,0xe347b843,0x3b9c44a39258b06,0x1dce2581c8c05,0xee712c0e44,0x1dce258188b05,0xee712c0c44,0x77389603,0x1dce2301a0945,0xb230288e04,0xee71180d04,0x77388c03,0x1dce2491c8b05,0x59208b43,0x16482452e8d45,0x77388903,0xe231128d04,0x3b9c42,0xee2c361d44,0x8f429e83,0x47a142,0x53102,0x53082]
def tableP2087_4 : List Nat := [641,0x3a81,0x4201,0x4401,0x4601,0x8e160c43,0x30120f83,0x8e180903,0x470b02,0x168c02,0xb41,0x841,0x2381,0x2981,0x2f81,0x3381,0x3581,0x3781,0x74c502,0x3a41,577,0x1d01,0x19a02,193,0x3881,0x3841,321,1,0x1c01,0x20c1,0xd01,0x1181,0x1781,0x108c073b944,0x2b81,0x3901,0x120c02,0x398902,0x398942,0x1cc1,0x3181,385,0x3981,0x422582,0x2101]

def encodedP2087 (i : Nat) : Nat :=
  if i < 128 then
    if i < 64 then
      tableP2087_0.getD (i%64) 0
    else
      tableP2087_1.getD (i%64) 0
  else
    if i < 192 then
      tableP2087_2.getD (i%64) 0
    else
      if i < 256 then
        tableP2087_3.getD (i%64) 0
      else
        tableP2087_4.getD (i%64) 0
def bookP2087 (i : Nat) : Clause := let n := encodedP2087 i; unpackLits 9 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClausesP2087 : inputsOK 2 2087 aP2087 rP2087 (baseBook bookP2087 191).toList=true := by decide +kernel

def rowsP2087_0 : List Nat := [0x40401,0xc0801,0xc0a01,0xfc8001,0xfc8201,0xfc8401,0xfc8601,0xfc8801,0xfc8a01,0x1289601,0x1289801,0x1289a01,0xfd2801,0xfd2a01,0xfd2c01,0x2894602,0x5fa894802,0x602954c02,0x60a954e02,0x195201,0x1d5401,0x215601,0x255801,0x683396c02,0x3596e01,0x3597001,0x33d7201,0x3457801,0x1aad469b495004,0x36db201,0x36db401,0x3c4a0e148482c2d0a8b04c09,0x50c184311f248680d498c8660a,0x444a0e13841bede160542c2d06a4c500d,0x2807094202a09b7d8a3e490585a0d49b80220f,0x2014618ac542514849c23e490585a0d49b801c10,0x904dbec30789c4ce2700581a3e49a481c0e,0x683cc8650283005,0x5529b3598563d9e8a207,0xa65765b34a8783b9cdca4e2c1f4a20c,0x802c9f8bc81359a5066c731d0d46136a14b60f,0x2b95598cb3ab989c5e2c968a4e72c184a20e,0xaa5765b309c833f1fca4753a1610a822eba0a210,0x351f8d28336399d28235974b8e836a14fe0e,0x1ab90781f2303122ea280f986e31b0e8720e,0x58260b7586c2427078981c09,0x750f922c50602c78351c3b074e31b09ca00e,0xd07192ca1d8d4781f2303122ea280f9840a718d84e1d768e03016,0x341982ddc321889c6007,0x7cea622442e0c0737824ef0abb41e271338ca010,0x178b188eb7806c520b1f141d4910638c4a0e,0x24128805823110a45c07,0x14128385e1763bc84210788f8a0ea48831c6f0090a45613,0x8051d62b15095bc2d0b3cc521b093c01c0e,0x381e643246e351e07c8c0c48ba8a03e62829c6387a0e83014,0x4a2d088382c2a0982c5008,0x444a0e168585005,0x444a0e1785d8c3e283a9220c7b8b02af57b06420e3783d05015,0x7cea61244140c05b8ca008,0x74180d07192ca23245d4501f308143b198d4603c1a07df23618be070327a38c3a1c,0x1a0e325941f06a4dd490278f5f43b0e8e8300f,0x174fc593f968c2852f20d0409,0x5b3f165025c359a4d4fc419b0bc6136a15000f,0x6531a7d3c663e1e936973427124ea483f49e3d7d124c413,0xc6674ea7cc8793ba6d2e684e249d490273f49e3d7d124c414,0x1bce08740a18fc89421c4c05f2c9751a8b472213c9d461fcb4763a1cdfefe273f538927523d14853e9c8c2974813c7afa4d924dc2d,0x4014201,0x4055e01,0x4056401,0x4056a01,0x88941c2f0bb19ee27080b02ac2628f49e3e280285012,0x504a0e1785c24290809c5609,0x504a0e168598f067909c42101e93c7c50090a45611,0x78941c2f0bb11bc2c0ab0e0e29094147a4f1f1404c12,0x78941c290904c54161682c4c0a,0x9c2031180ca12341982dec09,0x4281401,0x42a1001,0x430c201,0x430e401,0x4310a01,0x4311401,0x4311e01,0x582b57cbb572c607026eb71ae0a,0x582b57aba59c4968b15740e04dd6e411b00e,0x8044d4002,0x4508e01,0x703cc8648646e362407c1b0b8ac28300d,0x36391c0d62cfb1e07c900d85455c80c,0x45d2601,0x86461d402,0x4652001,0x4652201,0x4687a01,0x8a4693202,0x46c1801]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOkP2087_0 : checkRows bookP2087 9 191 rowsP2087_0=true := by decide +kernel

def rowsP2087_1 : List Nat := [0x4782c01,0x4785a01,0x6f3821d02863f22508713017cb25d46a2d1c884f2749c762d1fd1874874421f0d88c74dc1f,0x430d001,0x4513001,0x504a0e1484820279047c5609,0xb02ac59209c211e8e429ee09,0x61b0a170a8e479bc06,0x4964c01,0x430fa01,0x49c7c01,0x4a53401,0x624e990f277399f0ce4e90c8a472a8eca0c60f,0x6639988f26531a7d3d2b90ca2451d91ca8f40f]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOkP2087_1 : checkRows bookP2087 9 287 rowsP2087_1=true := by decide +kernel

def lastUnitsP2087 := digits 9 2 0x2192c
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflictP2087 : checkReasons bookP2087 301 253 lastUnitsP2087 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem excludeP2087 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 2087=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=2) h hc bp eq (by decide +kernel)
  let v := truth Z aP2087
  have hbase : ValidThrough v bookP2087 191 := book_start Z h hc z eq _ _ _ _ initialClausesP2087
  have h0 : ValidThrough v bookP2087 287 := rows_sound hbase rowsP2087_0 rowsOkP2087_0
  have h1 : ValidThrough v bookP2087 301 := rows_sound h0 rowsP2087_1 rowsOkP2087_1
  exact book_end h1 _ _ conflictP2087
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def aW127 := ([1,0x4002,0x4022,0x4042,0x4802,0x4822,0x4842,0x5002,0x5022,0x5042,0x5802,0x5822,0x5842,0x40041,65,0xc047,193,0x400c1,0x20c7,0x900,0x120101,0x4903,0x140101,0x5103,0x160101,0x5903,0x1a0101,0x1100,0x120901,0x140901,0x160901,0x1a0901,0x1900,0x121101,0x141101,0x161101,0x1a1101,0x2100,0x121901,0x141901,0x161901,0x1a1901,0x4107,0x24107,0x44107,0x64107,0x84107,0xa907,0x2a907,0x4a907,0x6a907,0x8a907,0xd907,0x2d907,0x4d907,0x6d907,0x8d907,0xf107,0x2f107,0x4f107,0x6f107,0x8f107,0x460108,0xc60108,0x1460108,0x1c60108,0x2460108,0x461108,0xc61108,0x1461108,0x1c61108,0x2461108,0x124009,0x124029,0x124049,0x164009,0x164029,0x164049,0x920,0xe0121,0x140121,0x5123,0x160121,0x5923,0x180121,0x1120,0xe0921,0x100921,0x140921,0x160921,0x1a0921,0x1920,0xe1121,0x141121,0x161121,0x2120,0xe1921,0x141921,0x161921,0x181921,0x1a1921,0xe2121,0x142121,0x162121,0x5127,0x25127,0x45127,0x65127,0x85127,0x9127,0x29127,0x49127,0x69127,0x89127,0x9927,0x29927,0x49927,0x69927,0x89927,0xb127,0x2b127,0x4b127,0x6b127,0x8b127,0xe127,0x2e127,0x4e127,0x6e127,0x8e127,0xf127,0x2f127,0x4f127,0x6f127,0x8f127,0x2e0928,0xae0928,0x12e0928,0x1ae0928,0x22e0928,0x3a0928,0xba0928,0x13a0928,0x1ba0928,0x23a0928,0x460928,0xc60928,0x1460928,0x1c60928,0x2460928,0x462928,0xc62928,0x1462928,0x1c62928,0x2462928,0x2e3128,0xae3128,0x12e3128,0x1ae3128,0x22e3128,0x3a3128,0xba3128,0x13a3128,0x1ba3128,0x23a3128,0x144809,0x144829,0x144849,0x164809,0x164829,0x164849,0x140141,0x940,0x100141,0x160141,0x5943,0x180141,0x1a0141,0x140941,0x1140,0x100941,0x160941,0x180941,0x1a0941,0x141141,0x1940,0x101141,0x161141,0x181141,0x141941,0x2140,0x101941,0x161941,0x181941,0x142141,0x5947,0x25947,0x45947,0x65947,0x85947,0x7147,0x27147,0x47147,0x67147,0x87147,0x9947,0x29947,0x49947,0x69947,0x89947,0xd147,0x2d147,0x4d147,0x6d147,0x8d147,0x460148,0xc60148,0x1460148,0x1c60148,0x2460148,0x462148,0xc62148,0x1462148,0x1c62148,0x2462148,0x462948,0xc62948,0x1462948,0x1c62948,0x2462948,0x105009,0x105029,0x105049,0x165009,0x165029,0x165049,0x960,0xe0161,0x100161,0x120161,0x140161,0x180161,0x1a0161,0x1160,0xe0961,0x100961,0x120961,0x140961,0x180961,0x1960,0xe1161,0x101161,0x121161,0x141161,0x181161,0x2160,0xe1961,0x101961,0x121961,0x141961,0x181961,0x967,0x20967,0x40967,0x60967,0x80967,0x1967,0x21967,0x41967,0x61967,0x81967,0x3967,0x23967,0x43967,0x63967,0x83967,0x4167,0x24167,0x44167,0x64167,0x84167,0x7967,0x27967,0x47967,0x67967,0x87967,0x8967,0x28967,0x48967,0x68967,0x88967,0xc967,0x2c967,0x4c967,0x6c967,0x8c967,0x2c1968,0xac1968,0x12c1968,0x1ac1968,0x22c1968,0x3e1968,0xbe1968,0x13e1968,0x1be1968,0x23e1968,0x461968,0xc61968,0x1461968,0x1c61968,0x2461968,0x462168,0xc62168,0x1462168,0x1c62168,0x2462168,0x2c3168,0xac3168,0x12c3168,0x1ac3168,0x22c3168,0x3e3168,0xbe3168,0x13e3168,0x1be3168,0x23e3168,0x463168,0xc63168,0x1463168,0x1c63168,0x2463168,0x105809,0x105829,0x105849,0x125809,0x125829,0x125849,0x145809,0x145829,0x145849,5,6,0x2805,0x2806,0x42806,0x6805,0x7005,0x8005,0x8006,0x48006,37,0x20025,0x40025,0x60025,0x80025,0x2825,0x22825,0x42825,0x62825,0x82825,0x6825,0x26825,0x46825,0x66825,0x86825,0x146826,0x7025,0x27025,0x47025,0x67025,0x87025,0x147026,0x8025,0x28025,0x48025,0x68025,0x88025,0x2804,0x8004,0x80a4,0x71a4] : List Nat).toArray.map readPackedFact
def rW127 := ([0,64,0xc045,0x300049,0x20c5,0x800c9,0x810c9,0x901,0x1101,260,0x904,0x1104,0x4105,0x104909,0x105109,0x904909,0x905109,0x1104909,0x1105109,0x64107,0x1904909,0x1905109,0x84107,0xa905,0x2a5109,0x2a5909,0xaa5109,0xaa5909,0x12a5109,0x12a5909,0x6a907,0x1aa5109,0x1aa5909,0x8a907,0xd905,0x364909,0x366909,0xb64909,0xb66909,0x1364909,0x1366909,0x6d907,0x1b64909,0x1b66909,0x8d907,0xf105,0x3c5909,0x3c6909,0xbc5909,0xbc6909,0x13c5909,0x13c6909,0x6f107,0x1bc5909,0x1bc6909,0x8f107,0x1192010a,0x1194010a,0x1196010a,0x3192010a,0x3194010a,0x3196010a,0x5192010a,0x5194010a,0x5196010a,0x1c60108,0x7192010a,0x7194010a,0x7196010a,0x2460108,0x1192110a,0x1196110a,0x119a110a,0x3192110a,0x3196110a,0x319a110a,0x5192110a,0x5196110a,0x519a110a,0x1c61108,0x7192110a,0x7196110a,0x719a110a,0x2461108,0x12400b,0x12400c,0x12402b,0x12402c,0x12404b,0x12404c,0xc490d,0x80490f,0x100490f,0x180490f,0x102490f,0x182490f,0x184490f,0x510d,0x16400b,0x16400c,0x16402b,0x16402c,0x16404b,0x16404c,0xc590d,0x80590f,0x100590f,0x180590f,0x102590f,0x182590f,0x184590f,0x921,0x1121,0x1921,292,0x924,0x1124,0x5125,0x143929,0x145929,0x943929,0x945929,0x1143929,0x1145929,0x65127,0x1945929,0x85127,0x9125,0x243929,0x245129,0xa43929,0xa45129,0x49127,0x1243929,0x1245129,0x69127,0x1a43929,0x1a45129,0x89127,0x2243929,0x2245129,0x9925,0x265929,0x266129,0xa65929,0x1265929,0x69927,0x1a65929,0x1a66129,0x89927,0xb125,0x2c5129,0x2c5929,0xac4129,0xac5129,0xac5929,0x4b127,0x12c5129,0x12c5929,0x6b127,0x1ac5129,0x1ac5929,0x8b127,0x22c5129,0x22c5929,0xe125,0x385129,0xb86929,0x4e127,0x1385129,0x6e127,0x1b85129,0x8e127,0xf125,0x3c5929,0xbc5929,0x13c5929,0x1bc6929,0x8f127,0xb8e092a,0xb94092a,0x2b94092a,0x12e0928,0x4b8e092a,0x4b94092a,0x1ae0928,0x6b8e092a,0x6b94092a,0x22e0928,0x8b8e092a,0x8b94092a,0xe94092a,0x2e9a092a,0x13a0928,0x4e94092a,0x1ba0928,0x6e94092a,0x23a0928,0x118e092a,0x1196092a,0x318e092a,0x3196092a,0x518e092a,0x5196092a,0x1c60928,0x7196092a,0x719a092a,0x2460928,0x9194092a,0x1196292a,0x1198292a,0x3194292a,0x3196292a,0x5194292a,0x5196292a,0x1c62928,0x7196292a,0x7198292a,0x2462928,0x9196292a,0xb94312a,0xb96312a,0x2b94312a,0x12e3128,0x4b94312a,0x4b96312a,0x1ae3128,0x6b94312a,0x6b96312a,0x22e3128,0x8b94312a,0x8b96312a,0xe94312a,0x2e90312a,0x13a3128,0x4e94312a,0x1ba3128,0x6e94312a,0x23a3128,0x14480b,0x14480c,0x14482b,0x14482c,0x14484b,0x14484c,0xa512d,0x80512f,0x100512f,0x180512f,0x200512f,0x102512f,0x182512f,0x202512f,0x184512f,0x204512f,0x206512f,0x16480b,0x16480c,0x16482b,0x16482c,0x16484b,0x16484c,0xc592d,0x80592f,0x100592f,0x180592f,0x102592f,0x182592f,0x202592f,0x184592f,320,0x940,0x941,0x1140,0x1141,0x1940,0x2140,324,0x944,0x1144,0x5945,0x164149,0x165949,0x964149,0x965949,0x1164149,0x1165949,0x65947,0x1964149,0x1965949,0x85947,0x7145,0x1c4149,0x1c6149,0x27147,0x9c4149,0x9c6149,0x47147,0x11c4149,0x11c6149,0x67147,0x19c4149,0x19c6149,0x87147,0x9945,0x265949,0x266149,0xa65949,0xa66149,0x49947,0x1265949,0x1266149,0x69947,0x1a65949,0x1a66149,0x89947,0xd145,0x344149,0x346949,0xb44149,0xb46949,0x4d147,0x1344149,0x6d147,0x1b44149,0x8d147,0x1190014a,0x1196014a,0x3190014a,0x3196014a,0x1460148,0x5190014a,0x5196014a,0x1c60148,0x7190014a,0x7196014a,0x2460148,0x1190214a,0x119a214a,0x3190214a,0x319a214a,0x1462148,0x5190214a,0x5196214a,0x1c62148,0x7190214a,0x7196214a,0x2462148,0x1190294a,0x1196294a,0x1198294a,0xc62948,0x3190294a,0x3196294a,0x3198294a,0x1462948,0x5190294a,0x5196294a,0x5198294a,0x1c62948,0x7190294a,0x7196294a,0x7198294a,0x2462948,0x10500b,0x10500c,0x10502b,0x10502c,0x10504b,0x10504c,0x80414f,0x100414f,0x180414f,0x102414f,0x182414f,0x184414f,0x16500b,0x16500c,0x16502b,0x16502c,0x16504b,0x16504c,0x8594d,0x80594f,0x100594f,0x180594f,0x102594f,0x182594f,0x184594f,0x961,0x1161,356,0x964,0x1164,0x965,0x23969,0x20967,0x40967,0x60967,0x80967,0x1965,0x63969,0x64169,0x863969,0x864169,0x41967,0x1063969,0x1064169,0x61967,0x1863969,0x1864169,0x81967,0x3965,0xe4169,0xe5169,0x8e4169,0x8e5169,0x43967,0x10e4169,0x10e5169,0x63967,0x18e4169,0x18e5169,0x83967,0x4165,0x104969,0x105169,0x904969,0x905169,0x1104969,0x1105169,0x64167,0x1904969,0x1905169,0x84167,0x7965,0x1e3969,0x1e4969,0x9e4969,0x9e6169,0x47967,0x11e4969,0x11e6169,0x67967,0x19e4969,0x19e6169,0x87967,0x8965,0x225169,0x226169,0xa25169,0xa26169,0x48967,0x1225169,0x1226169,0x68967,0x1a25169,0x1a26169,0x88967,0xc965,0x326969,0xb23969,0x4c967,0x6c967,0x8c967,0xb14196a,0x2b18196a,0x4b14196a,0x1ac1968,0x6b14196a,0x22c1968,0xf9a196a,0x2f8e196a,0x13e1968,0x1be1968,0x23e1968,0x118e196a,0x1190196a,0x1192196a,0x1194196a,0x1198196a,0xc61968,0x318e196a,0x3190196a,0x3192196a,0x3194196a,0x3198196a,0x1461968,0x518e196a,0x5190196a,0x5192196a,0x5194196a,0x5198196a,0x1c61968,0x718e196a,0x7190196a,0x7192196a,0x7194196a,0x7198196a,0x2461968,0x1190216a,0x1192216a,0x1194216a,0x119a216a,0x3190216a,0x3192216a,0x3194216a,0x1462168,0x5190216a,0x5192216a,0x5194216a,0x1c62168,0x7190216a,0x7192216a,0x7194216a,0x2462168,0xb14316a,0x2b10316a,0x4b14316a,0x1ac3168,0x6b14316a,0x22c3168,0xf9a316a,0x2f90316a,0x13e3168,0x1be3168,0x23e3168,0x1190316a,0x1194316a,0x3194316a,0x1463168,0x5192316a,0x5194316a,0x1c63168,0x7192316a,0x7194316a,0x2463168,0x10580b,0x10580c,0x10582b,0x10582c,0x10584b,0x10584c,0x80416f,0x100416f,0x180416f,0x102416f,0x182416f,0x184416f,0x12580b,0x12580c,0x12582b,0x12582c,0x12584b,0x12584c,0x80496f,0x100496f,0x180496f,0x102496f,0x182496f,0x184496f,0x14580b,0x14580c,0x14582b,0x14582c,0x14584b,0x14584c,0x80516f,0x100516f,0x180516f,0x102516f,0x182516f,0x184516f,0x2c1963175,0x2e0923135,0x3a0923135,0x3e3161975,0x462940155,0x462920935,0x460101115,0x462161975,0x463161975,0x462142955,16,0x20000012,0x2810,0x2812,0x21002812,0x6810,0x7010,0x8010,0x8012,0x1008012,48,0x40031,0x60031,0x80031,0x2830,0x42831,0x62831,0x82831,0x6830,0x5006832,0x5026832,0x46831,0x66831,0x86831,0x7030,0x25007032,0x25027032,0x25047032,0x25067032,0x25087032,0x8030,0x48031,0x68031,0x88031,0x200a0013,0xa0034,0x8a0034,0x20200013,0x200034,0xa00034,0x21202813,0x202834,0xa02834,0x1c6814,0x51c6833] : List Nat).map readPackedBudget

def tableW127_0 : List Nat := [65,0x6c1,0x7c1,0x1c0782,0x941,0x200902,0x220902,0x270d82,0x371002,0x31282,0x51282,0x71282,0x1745b164571545,0x281502,0x2c1502,0x381582,0x3a1582,0x421602,0x441602,0x411682,0x4c1682,0x4e1682,0x4b1702,0x19c6518c6117c5,0x2c1782,0x301782,0x3a1802,0x3c1802,0x441882,0x461882,0x411902,0x4e1902,0x501902,0x4b1982,0x1c46f1b46b1a45,0x281a02,0x341a02,0x381a82,0x3e1a82,0x421b02,0x481b02,0x411b82,0x4c1b82,0x521b82,0x4b1c02,0x1ec791dc751cc5,0x301c82,0x341c82,0x3c1d02,0x3e1d02,0x461d82,0x481d82,0x411e02,0x501e02,0x521e02,0x4b1e82,0x281f02,0x2d1f02,0x301f02,0x381f82,0x3b1f82,0x3c1f82,0x422002,0x452002]
def tableW127_1 : List Nat := [0x462002,0x412082,0x4c2082,0x4f2082,0x502082,0x4b2102,0x282182,0x302182,0x352182,0x382202,0x3c2202,0x3f2202,0x422282,0x462282,0x492282,0x412302,0x4c2302,0x502302,0x532302,0x4b2382,0x32402,0x82402,0x52482,0xa2482,0x72502,0xc2502,0xac1,0x25493244390a4260a87,0x25493244430a4360a87,0x254932444d0a4400a87,0x25493244430e4360a87,0x254932444d0e4400a87,0x254932444d10c400a87,0xbc1,0x32582,0x142582,0x52602,0x162602,0x72682,0x182682,0xcc1,0x26c9925c3d0c4260c87,0x26c9925c470c4360c87,0x26c9925c510c4400c87,0x26c9925c470f4360c87,0x26c9925c510f4400c87,0x26c9925c5111c400c87,0x9d2a82,0xab2d82,0xb72f82,0x92f82,0xb2f82,0xd2f82,0x364d7354d33445,0x9e3402,0xa43402,0xac3482,0xb23482,0xb83502,0xbc3502,0xb73582,0xc43582,0xbf3602,0x38ce137cdd36c5]
def tableW127_2 : List Nat := [0x9e3682,0xa03682,0xac3702,0xb03702,0xab3782,0xb83782,0xba3782,0xb73802,0xc03802,0xc23802,0xbf3882,0xca3882,0xcc3882,0x3b4eb3a4e73945,0xa43902,0xa83902,0xb23982,0xbc3a02,0xb73a82,0xc43a82,0xc63a82,0xbf3b02,0x3dcf53ccf13bc5,0xa03b82,0xa43b82,0xae3c02,0xb03c02,0xb23c02,0xab3c82,0xba3c82,0xbc3c82,0xb73d02,0xc23d02,0xc43d02,0xbf3d82,0xcc3d82,0xce3d82,0x404ff3f4fb3e45,0xa03e02,0xb43e82,0xab3f02,0xba3f02,0xb73f82,0xc23f82,0xbf4002,0x42d0941d0540c5,0xa44082,0xb24102,0xbc4182,0xc84202,0xbf4282,0x9f4302,0xa04302,0xb04382,0xab4402,0xb94402,0xba4402,0xb74482,0xc14482,0xc24482,0xbf4502,0xcb4502,0xcc4502,0xa04582]
def tableW127_3 : List Nat := [0xb54602,0xab4682,0xba4682,0xb74702,0xc24702,0xbf4782,0x9f4802,0xa44802,0xad4882,0xb24882,0xb94902,0xbc4902,0xb74982,0xc44982,0xc94982,0xbf4a02,0xcc4a02,0xa44a82,0xa94a82,0xb14b02,0xb24b02,0xbb4b82,0xbc4b82,0xb74c02,0xc44c02,0xc74c02,0xbf4c82,0xce4c82,0xa04d02,0xa54d02,0xb04d82,0xab4e02,0xba4e02,0xbd4e02,0xb74e82,0xc24e82,0xc54e82,0xbf4f02,0xcc4f02,0xcf4f02,0xa04f82,0xaf5002,0xab5082,0xba5082,0xb75102,0xc25102,0xbf5182,0x95202,0xe5202,0xb5282,0x105282,0xd5302,0x125302,0x28c1,0x5354b524b12849c2887,0x5354b524bb284aa2887,0x5354b524c3284b62887,0x5354b524cd284be2887,0x5354b524bb2c4aa2887,0x5354b524c32c4b62887,0x5354b524cd2c4be2887,0x5354b524c32ecb62887,0x5354b524cd2ecbe2887,0x5354b524cd30cbe2887]
def tableW127_4 : List Nat := [0x95382,0x145382,0xb5402,0x165402,0xd5482,0x185482,0x29c1,0x54d5153cb32949c2987,0x54d5153cbd294aa2987,0x54d5153cc5294b62987,0x54d5153cbd2ccaa2987,0x54d5153cc52ccb62987,0x54d5153ccf2ccbe2987,0x54d5153cc52f4b62987,0x5541,0x58c1,0x1575902,0x5bc1,0x1655c02,0x5e41,0x60c1,0xf5e82,0x115e82,0x135e82,0x6358b625876145,0x1586102,0x15a6102,0x1666182,0x1686182,0x1726202,0x1746202,0x1716282,0x17c6282,0x17e6282,0x17b6302,0x65d9564d9163c5,0x1586382,0x15e6382,0x1576402,0x1666402,0x16a6402,0x1656482,0x1726482,0x1766482,0x1716502,0x17c6502,0x1806502,0x17b6582,0x6859f6759b6645,0x15a6602,0x15e6602,0x1686682,0x16a6682,0x1656702,0x1746702,0x1766702,0x1716782,0x17e6782,0x1806782,0x17b6802,0x6ada969da568c5,0x1586882,0x1606882,0x1666902]
def tableW127_5 : List Nat := [0x16c6902,0x1656982,0x1726982,0x1716a02,0x17c6a02,0x17b6a82,0x1596b02,0x15a6b02,0x1676b82,0x1686b82,0x1656c02,0x1736c02,0x1746c02,0x1716c82,0x17d6c82,0x17e6c82,0x17b6d02,0x1586d82,0x1616d82,0x1666e02,0x16d6e02,0x1656e82,0x1726e82,0x1756e82,0x1716f02,0x17c6f02,0x17f6f02,0x17b6f82,0x1587002,0x15a7002,0x15f7002,0x1577082,0x1667082,0x1687082,0x16b7082,0x1657102,0x1727102,0x1747102,0x1777102,0x1717182,0x17c7182,0x17e7182,0x1817182,0x17b7202,0xf7282,0x27282,0x117302,0x47302,0x137382,0x67382,0x73dcd72d67565560b87,0x73dcd72d73565640b87,0x73dcd72d7d565700b87,0x73dcd72d7359d640b87,0x73dcd72d7d59d700b87,0x73dcd72d7d5cd700b87,0xf7402,0x147402,0x117482,0x167482,0x137502,0x187502,0x5741,0x755d37456956d565707]
def tableW127_6 : List Nat := [0x755d37457556d645707,0x755d37457f56d705707,0x755d3745755a5645707,0x755d37457f5a5705707,0x755d37457f5d5705707,0x1d77902,0x1e57c02,0x157f02,0x177f02,0x197f02,0x8460f8360b8245,0x1d88202,0x1d78282,0x1e58302,0x1f18382,0x1fd8402,0x86e1985e1584c5,0x1d88482,0x1da8482,0x1e68502,0x1e88502,0x1e58582,0x1f28582,0x1f48582,0x1f18602,0x1fe8602,0x2008602,0x1fd8682,0x896238861f8745,0x1da8702,0x1de8702,0x1e88782,0x1ec8782,0x1e58802,0x1f48802,0x1f88802,0x1f18882,0x2008882,0x2048882,0x1fd8902,0x8be2d8ae2989c5,0x1dc8982,0x1de8982,0x1ea8a02,0x1ec8a02,0x1f68a82,0x1f88a82,0x1f18b02,0x2028b02,0x2048b02,0x1fd8b82,0x8e6378d6338c45,0x1d88c02,0x1dc8c02,0x1ea8c82,0x1ee8c82,0x1e58d02,0x1f68d02,0x1fa8d02,0x1f18d82,0x2028d82,0x2068d82,0x1fd8e02,0x90e418fe3d8ec5]
def tableW127_7 : List Nat := [0x1de8e82,0x1e08e82,0x1ec8f02,0x1ee8f02,0x1e58f82,0x1f88f82,0x1fa8f82,0x1f19002,0x2049002,0x2069002,0x1fd9082,0x9364b926479145,0x1e29102,0x1e69182,0x1e59202,0x1f19282,0x1fd9302,0x1de9382,0x1ef9402,0x1f89482,0x1f19502,0x2049502,0x1fd9582,0x1e29602,0x1e79682,0x1e59702,0x1f19782,0x1fd9802,0x1d99882,0x1da9882,0x1dc9882,0x1de9882,0x1e19882,0x1d79902,0x1e79902,0x1e89902,0x1ea9902,0x1ec9902,0x1ef9902,0x1e59982,0x1f39982,0x1f49982,0x1f69982,0x1f89982,0x1fb9982,0x1f19a02,0x1ff9a02,0x2009a02,0x2029a02,0x2049a02,0x2079a02,0x1fd9a82,0x1da9b02,0x1dc9b02,0x1df9b02,0x1e39b02,0x1e89b82,0x1ea9b82,0x1ed9b82,0x1e59c02,0x1f49c02,0x1f69c02,0x1f99c02,0x1f19c82]
def tableW127_8 : List Nat := [0x2009c82,0x2029c82,0x2059c82,0x1fd9d02,0x1de9d82,0x1e99e02,0x1f89e82,0x1f19f02,0x2049f02,0x1fd9f82,0x1e2a002,0x1e9a082,0x1e5a102,0x1f1a182,0x1fda202,0x1dba282,0x1dea282,0x1eca302,0x1e5a382,0x1f7a382,0x1f8a382,0x1f1a402,0x203a402,0x204a402,0x1fda482,0x15a502,0x2a502,0x17a582,0x4a582,0x19a602,0x6a602,0xa6697a55e976dd60c87,0xa6697a55f576de40c87,0xa6697a560176df00c87,0xa6697a55f57a5e40c87,0xa6697a56017a5f00c87,0xa6697a56017d5f00c87,0x15a682,0x8a682,0x17a702,0xaa702,0x19a782,0xca782,0xa7e9da6deb775d62987,0xa7e9da6df7775e42987,0xa7e9da6e03775f02987,0xa7e9da6df77ade42987,0xa7e9da6e037adf02987,0xa7e9da6e037ddf02987,0x15a802,0xea802,0x17a882,0x10a882,0x19a902,0x12a902,0xa96a3a85ed77dd65707,0xa96a3a85f977de45707,0xa96a3a860577df05707,0xa96a3a85f97b5e45707,0xa96a3a86057b5f05707,0xa96a3a86057e5f05707,0x257956539464f9fe7d9ee799dca,0x11544d1143d0d4f53b4e5374d4a,0x11f4751b4651751d4550d414fca]
def tableW127_9 : List Nat := [0x289a1e85a0e819865f9765b964a,0x1c971dc570dc16d5b36c5af6b4a,0x1334c52f4b52b4a52749523484a,0x8520c811fc7d23c8d22c8921ca,0x2759ce719be6d9ae6999e6598ca,0x293a468fa368b9ae6999e6598ca,0x1bf6f5bb6e5b7725c7715c3704a,0xa9c1,0xaa400a983,0xaac1,0xab01daa83,0xabc1aaa83,0xac41,0xacc1,0xad41,0xad821ad03,0xae023ad03,0xb0ec1afebdaec5,0x37af82,0x41b002,0x4bb082,0xb36cbb26c7b145,0x37b202,0x41b282,0x4bb302,0xb5ed5b4ed1b3c5,0xb60a1b383,0xb60b1b403,0xabb482,0xb7b502,0xbfb582,0xb8ee1b7eddb6c5,0xb9554b683,0xb9562b703,0xb956eb783,0xb9578b803,0xb9582b883,0xbbeedbaee9b9c5,0x37ba82,0x41bb02,0x4bbb82,0xab6a8bc03,0xbc6c4ae83,0xbc6c6af03,0xadea8bc83,0xbcee6ae83,0xbcee8af03,0xae6aebd03,0xbd6e6b103,0xbd6e8b183,0xbdeb2ac03,0xb92d9bd83,0x701,0x801,0x881,0x9524c910e4290986,0x9524c9110c290d86,0x9524c91134291006,0x9524c9110c390d86,0x9524c91134391006,0x9524c91134431006,0x9b264970f4310986,0x9b2649711c310d86,0x9b26497144311006]
def tableW127_10 : List Nat := [0x9b2649711c3d0d86,0x9b264971443d1006,0x9b26497144471006,0x14d52d492c4a12706,0x14d52d492eca12a86,0x14d52d4930ca12d86,0x14d52d49334a12f86,0x14d52d492ecb12a86,0x14d52d4930cb12d86,0x14d52d49334b12f86,0x14d52d4930cbb2d86,0x14d52d49334bb2f86,0x14d52d49334c32f86,0x1535454f2cca52706,0x1535454f2f4a52a86,0x1535454f314a52d86,0x1535454f2f4b32a86,0x1535454f314b32d86,0x1535454f33cb32f86,0x1535454f314bd2d86,0x1cf735cb59d595586,0x1cf735cb5cd595906,0x1cf735cb5f5595c06,0x1cf735cb5cd675906,0x1cf735cb5f5675c06,0x1cf735cb5f5735c06,0x1d574dd15a55b5586,0x1d574dd15d55b5906,0x1d574dd15fd5b5c06,0x1d574dd15d5695906,0x1d574dd15fd695c06,0x1d574dd15fd755c06,0x299a5e957a5db7586,0x299a5e957d5db7906,0x299a5e95805db7c06,0x299a5e957d5e97906,0x299a5e95805e97c06,0x299a5e95805f57c06,0x29fa769b7addd7586,0x29fa769b7dddd7906,0x29fa769b80ddd7c06,0x29fa769b7ddeb7906,0x29fa769b80deb7c06,0x29fa769b80df77c06,0x2a5a8ea17b5df7586,0x2a5a8ea17e5df7906,0x2a5a8ea1815df7c06,0x2a5a8ea17e5ed7906,0x2a5a8ea1815ed7c06,0x2a5a8ea1815f97c06,0xaa41,0xab01,0xabc1,0xad81,0xae01,0x2e5b682,0x2e5b702,0x2e5b782,0x2e5b802,0x2e5b882,0xbc01,0x2c4ae82,0x2c6af02,0xbc81]
def tableW127_11 : List Nat := [0x2e6ae82,0x2e8af02,0xbd01,0x2e6b102,0x2e8b182,0xbdc1,0x2e4b642,0x129977183,0x1ab6fdc971dc15c5725988,0x1297b6397d5c85,0x1297b6397d59c5,0x4a5ed8e5f44,0x1ab6fdc971dc16a5bd599c5594a,0x1297b639667145,0x129597103,0x1297b6383,0x1ab6fdc971dc368db7705c5594a,0x1ab6fdc971dc368db7705c569dbb5c4c,0x4a5ed907144,0x1297b6403,0x18d6fdc971dc5615b7705876e5c35f0c,0x1297b6483,0x4a5ec2,0x5ea2fa403,0x22590e6ba4e917c5f87b08,0x5e9fd77e057e05,0x5e9fd77e057b45,0x17a7f5df8144,0x8966ba4e91811ec99e637949,0x17a7f5df7b26798c6,0x5e9df8f83,0x2f9dd9983,0x5e9fd77e677b05,0x17a2f9fd8984,0x17a7f5ed77c4,0x1fd9be1d98e6775c6,0x7f66f8ee6399e6d7947,0x2f9eb9c83,0x2f9eb9a03,0x5e8be7f6287c05,0x5e8be7f62899c5,0x17a2f9fd8a04,0x5e8be7f62a9985,0x2f9f79a03,0x5e8be7f62a7c05,0x17a7f68f99e6998e657b08,0x4a7f5f9a3e679a6239ce63994a,0x128be7f62a98c5,0x4a2f9fd8a84,0x128be7f43,0x5e8be2c0a030c5,0x17a2f8dd36ce14406,0x17a2f8dd36ce14506,0x17a2f8f13bcf54e06,0x17a2f8b02804,0x5e8be2c03,0x4a2f82,0xbf308ba2804,0x4ab60a12c44,0x4ab60c22e84,0x4ab60c22844,0xbf384f544d3b36cef435352c0a,0x12ad83083,0x2fca02dd412ac5]
def tableW127_12 : List Nat := [0x128a02c4b75045,0x4a30ca02c44,0x2fcdb3bd0d4d4b02dc7,0x128c32803,0xbf384f544d3b374f143d372e8a,0x4ab602,0xb941,0xb641,0x1281,0x1701,0x1981,0x1c01,0x1e81,0x2101,0x2381,0xb081,0xb301,0xbb81,0xa6e398b2358de9fa747,0x17b615996b5c161d9b6bdc35f8a,0x3dd574d755905,0x5ed655683,0x5ed656b5c37045,0x3dd574d655785,0x745d574d5b7085,0xf755d35d44,0x3dd574dc15945,0x745d574d5b6285,0x5ed74705c36bdad5f87,0x3dd574dc156c5,0x5ed7470585665ad5c47,0x3dd574dc16b85,0x3dd574dc170c5,0xf755d37044,0x3dd574c3,0x24493254402305,0x24493254401a05,0x24493254401a85,0x24493254401b05,0x93244951004,0x4121c420e04,0x10437ba03,0x410dc2,0x104420a03,0x9124c951084,0x244932543,0x21ba5df0a56999a06,0x299895f09b297a546,0x25c9926c412005,0x25c9926c411f05,0x25c9926c412285,0x25c9926c412185,0x412047d22c870f06,0x412047d22c8717c731188,0x1048125c9926c5,0xbf4d4ba4e4a02c06,0x2f81,0x3601,0x3881,0x3b01,0x3d81,0x4001,0x4281,0x4501]
def tableW127_13 : List Nat := [0x4781,0x4a01,0x4c81,0x4f01,0x5181,0xb581,0x3dcf735707005,0x3dcf735705645,0x5edc1561725f05,0x5edc1561725985,0xba374f143d373086,0x5354b524aa2845,0x14d524aa2814b2dc6,0x14d524a052cb62e86,0x535492a8a052c5,0x6695a5df09b85,0x6695a5df09905,0x6695a5df09885,0x7357b73dcb705585c87,0x1cd65dcf72d8f5cd957088,0x17b7055871dc35946,0x7357b73dcb705585c47,0x1cd5edcf72dc15606,0x5454f2d9533c85,0x544b653d533145,0xb75454f54caa3c06,0xb75454f54cef2a86,0x2dd5153d533bc5,0x2dcee2ac3,0xb75454f54c4,0x1d3745ad59013705c35c1af5d4a,0x1d3745ad6c56404dc170d706bca,0x74dd16b5b159013705c35c09,0x1d3745ad55813705c35c5665d0a,0x74dd16b56404dc170d715989,0x74dd16b56404dc170d715d49,0x1d3745ad59013705c35c48,0x74dd16b56404dc170c7,0x1d3745ad590137046,0x74dd16b56404c5,0x14b535492a84,0xab2dc2,0x2ac1,0x2741,0x6695a5df09c05,0x19a56739b6977c06,0x14f54d513c04,0x14f54d512d84,0x53d535443,0x1cd65dcf03d647006,0x6fdc95c9716adc15987,0x7357b73c0f5905,0x705715ed665945,0x29786e95a66199986,0x2739b5fd88e6999dda7a08,0x9ce6d7f61988e6999dda7949,0x2979ce6d7f695a661988e69768a,0x7f5f199df47a05,0x1fd7c66776e99a5e957d08,0x1fd7c667a2de575c6,0x7f5f199ddba6697a547,0x22f8b670a7e9ba746,0x9925c9b1044,0x9926c972048722c7d11c8]
def tableW127_14 : List Nat := [0x9926c9718c612086,0x9926c972048722c7d0f08,0x2649b25c8121c8b1f47,0x9926c971f04,0x9926c972284,0x9926c972184,0x2649b25c3,0x967c6679b699a5c6,0x1cb04dcd705715986,0x17b705ad55c4,0x1cb04dcd7044,0x701976456473dcd72c7,0x15a5df199e6da646,0x15a7e9d8b5e49b86,0x8e637a6e9d991e4a7c7,0x90e41a86a3991e4a947,0x1cd65dcb73dc06446,0x7359772dcf7005,0x7f5f105549a76a3256647909,0x7f5f199e6d0554905e639909,0x1fd7c415a5e67a646,0x1fd7c5e59b04,0x7f6237966d7785,0x2554d7283,0x2554d7303,0x7f5f1795ed9881505c7,0x526a105d517c5e57b47,0x149a8417545f17946,0x2a1a7d51a76a38e637791f9988a,0xa869f5469da8e258be3990e6b9d6937c5e49b6677b11,0x1fd7c5de7e04,0x95526a1545fda76a37c5e49b6677b6637e4e,0x25549a869f545fda76a37c5e49b66798cd,0x95526a1a7d517f69da8df17926d99cc,0xa7e9d8e63779266a6c7,0xa869f5469da8e3990e37905e4998b,0xa86a38be439ae938b6419a69179267a2e2798df9a951,0x25549a869f05d517c47,0xa7e9d8be399ae757c2678ddde53a717d8d,0x29fa762f8e66b9d5f099e377794e9c4c,0xa7e9d8be399ae757c2678ddde538b,0x29fa762f8e66b9d5f099e3798df7a6cc,0x7f66798e7180a6d7a87,0x2a1a8e437c2a59906,0xa86a38964395e7f7c21d8ee4f9dea57b4d,0x2a1a8e2f9ae937c26789e63a2ea599629a368f8090,0x2a1a8e437c23ba963d9a08,0x2a1a8e2f9ae937c26789e63a2ea599629a3669a3d0,0xa8e2f9ae937c26789e63a2ea599629a868d9a4f,0x2a1a7d51a76a38962f8e64395e6b9d67fa4df099e377792,0x2a1a8e2590e6ba4df099ddfa94a,0x29fa762f7c29b8ae2d80c8,0xa7e9d8be399ae757c2678de6d0569b98cd,0xa869f5469da8e258be3990e579ae759fe937c2678dd1,0xa7e9d8be6b9d5f099e039a5f6a6cb,0xa86a38962f90e579ae7fa4df099e69a94d,0x29f5469da8e258be3990e579ae759fe937c2a199d0,0x29fa76397c266a6c6,0x77282,0x2a3a86258be4395e6b9fe937c267a94c,0x29f0569d7c2639a06,0xa7e9b8be399ae75a75f077a298dcb,0x29fa6e2f9ae75a75f099e6980ca,0xa7c15a75f07785]
def tableW127_15 : List Nat := [0xa7c15a75f08dc5,0x29f0569d7c04,0xa7e9ba75dd8d05,0xa7dfda6e9d7c6679887,0x15524177c67199e637948,0x256a3a7c155241799c7,0x95a8e9f0554905c6,0xa8dfda86a57945,0x2a3a862590e6ba4ea5791f177ca,0xa8dfda86a57c45,0x77302,0x704c2,0x5edc1599725f05,0xa96a30543,0xa6e9da7e2f9ae757c2678d89,0xa6e9da7e2f8e66b9d5d67c265778b,0xa6e9da7e6b9d5d699e659b6699ce718a0d,0xa6e9da7e3975a379887,0x29b7f69da7dd67c2659a48,0x29b7f69da7de47c06,0xa6e9da7e2f9ae7575a2d9a67399e6598e2b9b4f,0x29da7e2f9ae7575a2d9a67399e65a6e638ace,0xa6dfda769f7905,0x9ae75a4e679c68f9b6699ce9198e8b994d,0x70402,0x1f17f667a7e9da6c6,0x1df17f667a685,0x1df17f667a705,0x77c5fd0604,0x7f5f1a7e9da6c5,0x77c5fd0284,0x1df17f43,0x9b7f02,0x1e955203,0x70582,0x7a842,449,0x7381,0xa601,0xf7342,0x1f003e2588c1987e6d2548,0x1e452d4f7f69f0346,0x791f003e25812670507,0x1f089623a56978046,0x1e47c225812677f695a5c8,0x1e47c00f8960499c6,0x1f003e2588e660546,0x791f003e258105,0x59dcb735595585,0x7355972d645cc5,0x565cb735705f45,0xa5e95759db7a45,0x792957d69776c5,0xa5e957c1db8045,0xa5e957c1e98045,0x7d6957c2978045,0x86e977c2959a05,0x7c225a56979b05,0x52d4d5243,0x72dcd5edc15605,0xa566686e978645,0xa5e737f69588e199a66d7689,0x1fd99df1a569776c6,0x99df125a979b45]
def tableW127_16 : List Nat := [0x1cb65dcd7004,0x7f5f105667a5c5,0x791f003e250505,0x7c00f894159985,0x1f09ce959ae75a5e6d9a667804a,0x1e47c00f8944,0x7f01,0x8681,0x8901,0x8b81,0x9081,0x9581,0x9a81,0x9d01,0x9f81,0xa481,0x791f0a569799c5,0x1f079295a5c4,0x1cb0442,0x791f0a96a39985,0x1e47c014a584,0x1e47c2a3a944,0x745d55edd3705585947,0x1d104dd574dc15606,0x74413755d37045,0x5254f74491a905,0x791f00503,0x1f0524152649300c6,0x1e47c02,0x72c137343,0x7929b54dcc2545,0x7c415a5c3,0x7901572c3,0x1e40542,0x1e47282,0x7909504c3,0x1e42542,0x7901,0x7c01,0x9981,0x9b01,0x8601,0x8881,0x9a01,0x9c81,0x7681,0x1532669b0504,0xd03c2,0xda902,833,0x2501,0x2a50102,0xa941,0x641,0x481,0x2681,0x5481,321,0x7301,0xa581,961,0x72c1,0x541,0x5201]
def tableW127_17 : List Nat := [129,0x5381,0x7401,0x2401]

def encodedW127 (i : Nat) : Nat :=
  if i < 576 then
    if i < 256 then
      if i < 128 then
        if i < 64 then
          tableW127_0.getD (i%64) 0
        else
          tableW127_1.getD (i%64) 0
      else
        if i < 192 then
          tableW127_2.getD (i%64) 0
        else
          tableW127_3.getD (i%64) 0
    else
      if i < 384 then
        if i < 320 then
          tableW127_4.getD (i%64) 0
        else
          tableW127_5.getD (i%64) 0
      else
        if i < 448 then
          tableW127_6.getD (i%64) 0
        else
          if i < 512 then
            tableW127_7.getD (i%64) 0
          else
            tableW127_8.getD (i%64) 0
  else
    if i < 832 then
      if i < 704 then
        if i < 640 then
          tableW127_9.getD (i%64) 0
        else
          tableW127_10.getD (i%64) 0
      else
        if i < 768 then
          tableW127_11.getD (i%64) 0
        else
          tableW127_12.getD (i%64) 0
    else
      if i < 960 then
        if i < 896 then
          tableW127_13.getD (i%64) 0
        else
          tableW127_14.getD (i%64) 0
      else
        if i < 1024 then
          tableW127_15.getD (i%64) 0
        else
          if i < 1088 then
            tableW127_16.getD (i%64) 0
          else
            tableW127_17.getD (i%64) 0
def bookW127 (i : Nat) : Clause := let n := encodedW127 i; unpackLits 10 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClausesW127 : inputsOKBudget 3 127 aW127 rW127 (baseBook bookW127 628).toList=true := by decide +kernel

def rowsW127_0 : List Nat := [0x200601,0x400a01,0x400c01,0x5a0b601,0x5a0b801,0x5a0ba01,0x5a0bc01,0x5a0be01,0x5a0c001,0x680d201,0x680d401,0x680d601,0x680d801,0x680da01,0x680dc01,0xf51ec01,0xf51ee01,0xf51f001,0xf51f201,0xf51f401,0xf51f601,0xf51f801,0xf51fa01,0xf51fc01,0xf51fe01,0x10620e01,0x10621001,0x10621201,0x10621401,0x10621601,0x10621801,0x10621a01,0x612e401,0x612e601,0x612e801,0x612ea01,0x612ec01,0x612ee01,0x17e2fe01,0x17e30001,0x17e30201,0x17e30401,0x17e30601,0x17e30801,0x6843e01,0x6844001,0x6844201,0x6844401,0x6844601,0x6844801,0x10645601,0x10645801,0x10645a01,0x10645c01,0x10645e01,0x10646001,0x17e46e01,0x17e47001,0x17e47201,0x17e47401,0x17e47601,0x17e47801,0x24749002,0x13a24949402,0xa4949602,0x13aa4e49e02,0x13b24e4a002,0x10e4c001,0x10f4c201,0x1114c401,0x1134c601,0x1144c801,0x159ab24d202,0x2bc4d401,0x2bc4d601,0x15aab24d802,0x2bf4da01,0x2bf4dc01,0x15b2b44de02,0x2c24e001,0x2c24e201,0x126a4c4e402,0x2c54e601,0x25449c9212e532a614b16a2d059cb68092de028b880b24610,0x4f92313c2c054c9f9432b0508ab1642a40b,0x14a2be4414a148590590a29502b65ad6392f28c5789294e52c490b68092de028b880b48219,0x120a94290540b5ac725e518af12529c52cb1a95592490b68092de028b880b2be16,0x13e48c4f0b015327eb28b1955282a5564958286a58b68092de028b880b28a56cb5ac725e490af1252a41d,0x27c9189e1552824fca99602a408,0x4f92313c2ac5094aacc2da024b780a2e202ca295b2d6b1c979242bc494a21595964fca99602a41b,0x2c858cb68092de028b880b52a08,0x534a51122be4414a14859ab38af14624a490b68092de028b880b2a05ad6392f48217,0x2809189e158286554a09122a808,0x14048c4f0ac1432a805,0xa0246278564a22985a2558a12975a0514ad96b58e4bcb112827a544ae29424e498b68092de028b880b2a81e,0xb21635a449cb68092de028b880b52e0a]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOkW127_0 : checkRows bookW127 11 628 rowsW127_0=true := by decide +kernel

def rowsW127_1 : List Nat := [0x11e48c460ac9202ae05,0x8f2462305608fa995a8580a991b2b85448c96652ea549592a2525b40496f0145c4059222b65ad6392f2ae1e,0x2429188c1642ac474b0153236570a8919532a614b12d25848d6aad359eb1cb595b25e488b68092de028b880b2b420,0x35c6b0d51b0562ac15721742c855191154684591b11735010,0x1e041e704ce9bf338844f29c2340690e39ed346714f5a1448a11,0x62d2218a3f6634f098c30aab0fd2d83d663cd39ca3e680d0c2d73647d90118e3daab9191154684591b1173b81f,0xc5a44314784c62ac3f463cf9a033ec808c71ed55c7f8c69e755ab65191154684591b1173b81a,0x1e041e704ce9bf338844f29c2340b69091e738868556ad93da71cd22ae4644551a11646c45cd39ca3e68616b9b248a21,0xcea45338848d09a63e2680f2a1141e0a,0x33a914ce214346ab56e23222a8d08b23622e69cf9a185ae6c8d31f15b6680f2a1141e18,0x38a711191154684591b11755a08,0x3d479d130724501cd1507454e08,0x3c06fd6e9c23947216dade38208,0x18b488628ff98e3f6634c31e1318615561fa5c0b7cf8adb3ec6a8d4a3222a8d08b23622e63cf9a033b81d,0xc5a443147fcc71fb3ce634c31e1318614f8aac5b67d9191154684591b11731e7cd019fa3b81a,0x735201cb41475ce620b3ee67d2219c41a7fcf69da39e691061fb3b2738d09863c2614d39d03b67cd01a0e3b01f,0x386910df9ff3da71cfd9c430c728f9a033cc0c,0x4027fd130724501cd1507455408,0x3e07b5130724501cd1507455408,0x1c34887d4df9fd3d6715531c8552abcc2ab030c8c88aa3422c8d88ba260e48a039a2a0e8728f9a033f4700efae2358b95731ab3cc25,0x1c34886fcfe9c5552abd721f554cb8d191154684591b11744c1c9140734541d0e51f34067e8cf1c03beb88d62e55cc6ace3ae73cc25,0xf59e75d06b1191154684591b11755e0a,0x37871cd99bf36c708e01b538c6e954aaf55ab7cf61e74644551a11646c45d130724501cd1507437c728d69ae55620,0x3e07b5130724501cd1507455608,0xfa9f93ca77d00aa7552abd56aab30c8c88aa3422c8d88ba260e48a039a2a0e87cd019fe35cba9759ad4881e,0x915702113e68616b9b242007,0x540671719f4342679222af5c47e976a1a0128700521e0168c88aa3422c8d88bad634e7cd019fe33e1c,0xfa1c03f4aa5502ac3ca790f19e15dc86804a1c01487805a3222a8d08b23622e898392280e68a83a1ae426ba9759ad3487fd762d65c826,0x2e23bebbd752d65c005,0x1bd5da6cd0a1ea372790db1de36aac5582ab554aa0d89b035e6a1782e95c26f8d923222a8d08b23622eb59130724501cd150743e425,0x3905d0a11102583f8e0170274430e617c28c4628a5183c08a8f222c3d08b8711062685a8de10225c5a0dc47c1f,0x1fd458851702dc781151e44587a1171180b,0x1fd4588b17c2f4781151e44587a11710c0b,0x28c4f28b1c2380781151e44587a11712c0b,0x13a291458e71cc8f97aaf45e638c5d8a0112bc86e0b412e204781151e44587a1171062685a8de12c1c,0x6e8b31302004b07f1cc2f85188c1c62ec500891c02e04e88650ca15422f61bc2d44d0831e0454791161e845c3807147c22,0x1a231c6d8d819a35865a8d524a45480c81362084b07f12e204680a31182804489d10ca0d44a8850e34d7b905206404c498830ebc4378700e23c08a8f222c3d08bad648430,0x600e914e264528961d02fc530971442b0628ee1402ac620ed13a2a4610eb47e16,0x4ba9703806f50696c781151e44587a1175ac9797c25a4b210,0xdd166260400960fe3785a89a106be97c8e01702744308a1442f072af81122805d8e347c19,0xdd166260400960fe3785a89a10637c5b09c108be9420f022a3c88b0f422eb58450a21783957c0891402ec71afb47c21,0x708b713c2144b07f1bc2d44d0831142885e0e547c0e,0x1803a45389914a258750c115027143afd1d03705f8b414c25c40afc5f63b4718c41762ac500891e0454791161e845d6b0a2158314772f847e28,0x29d1f8a51d4304540ac18a3b8530bf1d02a8618ec1800f,0xa747e294758c2152a1d7f8f022a3c88b0f422eb58560c51dcbe0530bf1d02a8618ec18019,0x4e89c12c26474b0013ea20781151e44587a1175ac2897c09750e12,0x1c42e44f8875fa04,0xe4174284440960fe3805c09d10ca29810de16a26841b011b82d04b8811e0454791161e845d6b08a1442f072af847c21,0x6e8b31302004b07f1c02e04e8861142885e0e547c0e,0x1ba2cc4c08012c1fc6f8b6138211423041bc2d44d0831c42e44f8875f4a1581afe1e0454791161e845d6b08a1442f072af847c24,0x2bb574ae55c2b74be05,0x30658c01,0x30760a01,0x30802c01,0x30804201,0x30805801,0x30806e01,0x30808a01,0x3080a601,0x3084a801,0x3084b001,0x3084d001,0xdb1b5554aa0d79b036606,0xb314b26e474981182d253c9c9212444eca816b4820e,0x2cc52c9b91d260460b394d27047d4fb132c25249991c2ba51c9891a53aa6cbc122276540b59154821c,0xb1148268b309815d28e4c49d9452a056cb593529458c9c14329a560b391248216,0x241598514a815b2d6528b194329a560b39122900d,0x26649898123264494bc12f2764a49a92c2704498a91553410,0xb095f53402,0x5449e94662cc60af31762a59cb1941224c50ab97828a56cb59155a213,0x15127a5198b3182cec54aa9412245e0a295b2d6454b2b195a211,0x9091f53802,0xb494f2a05aca616548206,0x59ca6a9c6385188c9186365248e29a6305e0911502d64548f14c2cac648831a48217,0xb114826846c981182ce5349c11f2444eca816b23c4d8a616548212,0x4614f11b292520bc12223cc78a3931234c758c9152420f,0x5a8a713a2404c08c133238a798e1782444eca816b23c4d8a616563c51c9891a63ac648ab1f4821b,0x2724d14f1622c2c818f1472624698e9782764549b31926010,0x2724e0981335344418b9322bc575909366325e09d91553810,0x1282304e0ad3da794f81482830b0440a,0x392180c0840502603e0221241d80f0909e53c27704808c03808646c3986b0907217,0x412180c08c0e0068420281301f0110969dd3da7a04c09403808646c3986b0907817,0x92430181181c00d0920ec078420281393c27a4f80a013808646c3986b0907e16,0x154860302483b01e1181c00d0980f808a7b4f29f01502264cc9592323616c2586b0e08619,0x392180c0920ec0781308213c0883e098c3986b090720f,0x12aa51588b0529a574a49598830f57a0a,0x95528ac358099594a664ac94929a574cec4187b1157c0f,0x2583c04c0401100c08c0e01180d0260a42084f02209c1f04c61cc3585b0948616,0x90089940254eecac1382900eca993b0b0480c,0x1381f8280240880604607008c0684907609407a784f4cb19504f0820a409b27612c2d86b0e4861b,0x2a4320648cbaa254a664f79ee32809,0x67cd11a5540a855118530c7d0cf1f63380b,0xc81b4fca000e04007e0799530a02e0a,0x740da7e4fa0601d03903c01d9530a02e0b,0x170300669f94004e09a0d19530c05a0a,0xc81802f4fc9f42404706801d9530c05a0b]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOkW127_1 : checkRows bookW127 11 724 rowsW127_1=true := by decide +kernel

def rowsW127_2 : List Nat := [0x2503d08213d8730d48606,0x960f01881a05a05c1901d03c0d02084f61cc358630a48610,0x19a82e0329f59a333664cc403b2a5000a,0x1c82e85088812c1fc6f0b513420c450a21783944309d1702044b8b447c14,0x2c8570aa1d03987265a06,0x3380fc01,0x33811401,0x33812a01,0x33814401,0x33815801,0x33816401,0x33817801,0x33818a01,0x33819e01,0x3381b401,0x3381ca01,0x3381dc01,0x3384bc01,0x9512d24e4954aa96528578ae16c25e454881122460e,0x5489e2462c8558a11682b2510b015327ea554b2942d8514ad96b22a4408934627c17,0x1542c45009413c2465a0ac94425a4bca295b2d64909e951254508ab16448c15,0x16a2b44b890923230580a99272364889795b2d64649215123a4a8ab16448c15,0xe317628044b3860805,0x710b913e21d42b4a1bc2d44d083506a1037b386080e,0x1803a45389914a258758c215227543b021d830c5509f10225c530b417e37074344680cf59e33847e1c,0x3375f23806e33851005,0xe317628044a8a50ed35a608112e2d06e3385fa0d,0xd11a533a68151aa45407e8fc21d34e624c29863380e,0xcb99a324a8d522a032678cf121d336624c29863200e,0xcb99a328a85512a0322774ee21d336624c29863200e,0x4a1689232ce4b14c349690590ab1422544bca295b2d64909e9512c413,0x129250a5cb116024605,0xb19452b65ac9e9515a006,0x2cc55c9591e246460a9927236a5daa3532ce5609611f2444bcad96b232490a8b5248c18,0x12b5a848cb015324e46cb412d52ea64893556a4544921192444bcad96b2cc15,0x3d2420ea350648791b03343e8d118e1dd4829351c3544f09d0e0d05a133919416,0xd919c2505888d15a350648af120358658b0122344638ae11ca4549a8f67cceda134148419,0x784841d4688c70ee3586587b51aa406989b1341f0660d70ded05a133919015,0xf49083a8d41921e4688c70eea41470d513c2744b3590f827c660d7682d099cb3c19418,0x4b2bfd2d8e91342644b25c138d684fa5d60ed159c33c4b410,0x8047c1fc6f0b510696d2ca5c1be2d8420871723892ea5a12e3744c34367ece983b4516619,0x1a43184787611a1d46a0c91201e46b0cb1221ed46a8e0ded704c35b0f8248660d7682d099db394841c,0x1332384c48d29d536a7c8b97c62609,0x5a8a713a2404c08c1332384c48d29e538c70b293623cd78be122276540b591748217,0x8d12123ca694f29d236524a435f2205f0911172300e,0x5248d2412305948f17c2445408f94d23652d641672d656ca291753413,0x9ba412605249993153aa6db094b590440be13b28a540ad96b22e4e0a69672cc16,0x2cc52c9b91d2604609991c2624694ea9b2f84889d9502d645c8f93829a59ca436248218,0xb294c6c6521b116729a540b59174820a,0x1af29d298d81b217c29206,0xa789831e26c4c48d13453ac60b11616ca5f09d9172720f,0x4e49c1302664d89929a536578aeb662765f08b9105380f,0x34b69c01,0x4b2bfd2d8e91342644b35c4ba27c4e25c60ed159c33c4b410,0x3690e001,0x36a0de01,0x1a533e674d1aa5546a84ff1fc43a69cc49863380d,0x19a32864952aa3542658f49e8488db1a8b5069ecb8c321d3367cd0198932015,0xf09083a8d118e1dc6b0cb0f6a35480d31362683e8cd1b0d61aeb41684ce5b5b6a19018,0xd218c23c3b08d0ea350648900f2358658910f6a354709812cdb86c0cd14224c3eb586aecf1b536b672ceda134148421,0x35d6de01,0x49c9512c528a55a39252bc570b61102460b,0x2c82ce01,0xd1d4a2956acdc48812f28a56cb596c6e40b,0x58ca19582ce514ad96b59807,0x32864951aa132c7a4f41e732008,0x68d2219c3f078ccf9a73e680cce9dd3fc0b,0x3f4788d0193338640fd9a132a66cd39f3406648ce9dd48810,0x3f4788d0193338640fe1a232ea8dbbb763ba674c91a73e680dba99b48814,0x1f63b8678c899c3207e0f199f32866cd39f3406660d21ed3fe65cd11fc48815,0xcf2445c67e908a453b862cc521231a784c6185540de4fe18f3e680d0c18e3da7fd0aa0f3ec1a,0xcf2445c67e908a453b862cc51e131863cf9a03430638f69ff42a634fda123ec16,0xfb1dc33c644ce1903f078ccf994540decfd9a132aa85bd19b34e7cd019983487b4ffa0f4881a,0x3526ad53aa93f67f4d71fe35008,0x33066c01,0x2503d0a211140282010df98730d4860a,0x5d3f81f08810dbf30a03207,0x170364fe14828a437001281e830036df80e8326fec318730d05a12,0x4b0780c40d02d02e0b80c8510880d41027d502e041901d6fe01c0437e61cc358630a48619,0x2003a06d3fa7e4fa0601d03900e021bf30a02e0d,0x5c0c01a8334fca014104e09a021bf30c05a0c,0x350640c017a7f4fc9f42404700e021bf30c05a0d,0x3206c1027e500a080e04007ee09c2b84706021bf30a02e10,0x37c434188c3863330690f69ff6f009,0x6e8dc8a295b2d6d588b97052a08,0xaf91062c02,0x13e48c4f0b21562845a0ac94452aa598b3882c054c9fa94712519ab17028a56cb59172a419,0x25a4b09192a52a5709295e52c08,0xdf0c3a19330690f69ff6f007,0x6a4d69ac54caa4fd1f944a6c8c39853500b,0x3726d554aa63c2790db9e636608,0x380715562af3c2794e19e637e08,0x96129224e2c9295e24606,0x24e499c815c52804,0x7225c11b38f2da15097b2d2dc4582b8f21e2da079a2a71c6f8e51bb38e89518b6a71418,0x7225b42a32d2dc15c790f16d03ccb822a46c4bd532ac5c46d4e01b35c86e1c91b73f4798f29e43c26f8dda2546289d1985843ce310db6a71428]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOkW127_2 : checkRows bookW127 11 820 rowsW127_2=true := by decide +kernel

def rowsW127_3 : List Nat := [0xe31be2193e803,0x3b082ce699f396671051d7398678fb9f634e740eda0e34873ced20d342738eca0c48018,0x1a05c8670ef9c033c69cd09e73f409,0x1e2cb5b40541e05b4b636a0ae08,0x1decb5b40561e45bcb736a0aa08,0x391730e5cb80f30b08d91521e558a99ca23344e86dbda0f6ee7b4cc1ff3ce4bd7139672a690ef1b63666d0ee1b83766f912a3171425,0xe4dcc9016e04151aaac3f48ccf9a033f6e59bda0f6eee54f69a43307fcf398848817,0x705229bf422794e139a41edddcaa123ce710e51f3430620cc1a438e7b4ffa153c017,0x6d8dcaa654e8988037020a8d5569b43be778ee1853660f,0x6b5229a84206a956a3520adc080b8d488e70ff2d8422794d61af3767b4ffa1542617,0xe920538667cdf99c40c74ce29a334e728eb20934871cea20733c700e8a0447a16,0x202415c9235488abcff1f34067b4ff9fa6e00c,0x6fae4913101200dc082a35558e79cf9af3da7fcc29fa73a861019f33946f8d91a748818,0x1b936ca9d53226200dc082a355586d0ef9de3b8e81ce9a73646f8e51f3406860dd98536619,0x6d8daaa954e7a8dd1ec36607,0x1c0384ab557a3520adc080a25744718f61eb37e0d,0x6b5229a84226b1c7aaf42607,0xd59ad54ca9d131006e04151aba473c77cd520f3ec7d4fa3a1746615cda153da71cdd9af44e8ccd91be3947cd0c18835022,0x7d5009f054caa8d59a871ac48dc9ad30a6a8ef90171c8988018648813,0x1f94027c0faaa9556a9dd31df71c898801864880d,0x155b7d3fae9d1310036006,0xdf4fca013e06c0faaa9556a9dc71864880b,0xfc9e43e680cf820148806,0x560e3cf298639004,0x1d240a70ccf9bf338818e99c5346820ea9c834cabd5818647a11,0x10b9ae48a6a0f81b056206,0x1c5392ac4f91f137e05,0x122bad42c02,0xd42b135a85109baf36206,0x3ae422708d63ac7568d482b70750841021df3a2700d519e76011,0xf020f382674df99c42e7c4e41a6428714d1a11384681d5aae55aab0c298648a16,0x3566a5552a835004,0x804f83b371ac48fe9b935aea5c71864880b,0x6d8dcaa654e6d0ef1dc768898809006e04151abb23ecec4c298636613,0x910d89f93c87d4ef3b3554aa0d69fd4040b,0x4226b1d621040877ce89c0354679d93ab7600c,0xaad131006e04151abb73e46f4de3b576c0b,0x556e88c31ea37804,0xe01c2390ab557ab146a415b810144aee4e31ec3d6ee0c33a5430825019f33ac728df1b234e8cd139882041942ba2a70ccb4798620a88c8783972da5b02c06637e2e,0x758eb9021d1380679dbbb238408,0x3ea6f5541f23e06c8f9a03772894df1877680c,0x6a0dc9ad752ee4d51df62407,0x2ab76c01,0x1ab3eaef5da1bc77cef0ef9b23e680ddca2537c61cc298654c11,0x6d8dcaa654e6d0ef1dc7686c8f9a03772894df18730a618fb3bf36613,0xef8de9bc780ee5129b237c7cd019873e40b,0xdc9b854e02,0x30aa98db1b378483cda1de3ba770df1bb6f60c,0x1fa48a91107b936eee55091f3406860c39983487b4ffa1542211,0x3566b4d52a654e7d8faa4471ae48c2bc47867cd019ed3fedf4d7bc144a89cd918735018,0x3cef14ddbc144e894df18774408,0x1c148a6fd089e5384ab1bda0f72cddd0a9ff3da71cd219872a848f39c430c728f9a183c019,0x558ab4c2a155b004,0x1c63847b157ba473c840ef9c0354f210a9ed38e6bcd39b23947cd0c3c737e15,0xe01c239071956aaf5627b0f5bbb792f1d1a9056e040de32184127cceb1ca36469d189872003bc31855454e19968f30c81591a3982de5b82c06637e2a,0x1c892f2e045ddd3ca71406,0x4f92313c2d0564a21452b65ac9f9532c0508ab1642a40f,0x1c0384720e32ad55eac4f61eb776f25e3a184127cceb1ca36469d1898737e15,0xef8de9bc3e403,0xfaa013e07e9532aa3fa6b0d5ba977a77de73b94880e,0x1de3f4a98d61ab48805,0xd9aa67846d0ef1dc36c06,0x6a1533aa7a0df5009b077c7d9e79ad752f45e73b94067ccdf1b235213,0x7c1893d23726b5d4bd171cf39dc9b237c7cd019857660f,0xd49f9350911e837d54c06,0xd59aa54c7d8fabd435006,0x3f27d554aa735af55e8b8e744df4ff9ed3766bde99853646f8f9a0348814,0x7e922a4442203,0x36a6dd531e63c8f5dbda0f6eef0d0a9ff3da6ecd219872a848fd9e7370619eb2184067ccdf22a44e620820656e0e188086379a4082bb2d44c15477b684683c82c0661e88d9e5b6a36634,0x6d4dbaa63cc791ebb7b41edddcaa12370f59e1b7d330690d79bb3da7fd0a9b237c7cd01a183661b,0xfa37c43a5f50d3220a88c996bc90ae8cd0e0f10ca191b43861de18d132250b01987a2367965e9ec1983487b4ffb6a6f022,0x8710e8562facb5910551e03bc31b6870c3c432a2844e160330f47965e9ec36a72817,0x556e0cb4818574663c5e4b684643c19117d20a1607a2367965e9ec36a20015,0x1eb3d93ce02,0x86dc33750c6f6912bdd43415196a280ae1603319833687514bdc0ca13,0x10cb866ea1950e3db44e159eeb2d44c15477b681e2f7914a1d7b866c2c0661e8f2ccc36a0c61a,0xca18cc418770c04,0x67cd119d34ca9152aa2404801b6b2f4388742b17d65ac882a8f01de160bd3d834ef7df00663381b,0x82900452155eb32d45015c78b687c28950d0630c4e18818650b03d1e59867bef803336a6e01a,0x1c0384720e32ad55eac4f61eb7768d9e59a7364728eb1f3412860c33df7c019919be237e19,0x33e688ce9a6548a9551202400db597a1a0a8cb42b8f16d03bd133d6452874beb22464f8d13a1b7c4619ef9a77c05e9ec0f47961982c36a33828,0x3e42e201,0x3e443c01,0xa50a33746ac449c8b732d84bc8abe57120b,0x688ceaa5544801b6a1b2f6c88be21a1e8151cc32d0ac5bdf3be633813,0x22844c40877b706d041079b6a7ac09,0x2443e6a90cfbe865edb1a8b5069e86cbdb222f88687a054730cb42cbe94068a4c486770c404318f22dc1583216f7ce698f8be640025,0x67cd119d548a95513e633807,0xc8a443207e0f19943f865d502a16f0800cd3eb65e614d31f13367cd01be63b816,0x2fa5ed1aa1b79afb10c9877d48d0b73e76440c,0xdd5f5a1b2f6c88bea35336f350c9874685b9f3be63340f,0x1b6beb65e86cbdb222f88687a054730cb42cbe945262433b8620218df73ed34c3c8b70560c85bdf3be64001e,0x3e552801,0x3e552a01,0x3e552c01,0x3e654001]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOkW127_3 : checkRows bookW127 11 916 rowsW127_3=true := by decide +kernel

def rowsW127_4 : List Nat := [0x3e654201,0x3e654401,0x3e654801,0x3e654a01,0x3e665c01,0x3e665e01,0x36a6d001,0x3e56ac01,0x3e66ea01,0x3e66f001,0x3e66f801,0x3e670e01,0x3e572201,0x3e672801,0x1fca1b2f6c88be21a1e8151cc32d0b2fa5149890cee18808631e45b82b0642def9d013ef6da1a,0x3f77dc7a50ca1b2f6c88bea3579a8d0b73e734a0d,0x7e0f19fc3bafd9fbbf548807,0x645221903f078cca1fc32efcdfa3fd34a66a024037f0fe50d97b6445f51aa033e666de6a1930f009013ef30a8d0b73e73b823,0x1f01890ce02,0x40633601,0x40634e01,0x40636401,0x40639401,0x4063ac01,0x4063e601,0x40640601,0x40641201,0x40643001,0x322910c81f83c6650fe1977e6fd1fe9a5335011013ec30afe5fc40d81901e034083b818,0x3f77f87a60840733405,0x798dc9f8b162c0fc1c49467f7000b595b28a4bcb71167e410,0x1c038472156aaf562718f61eb4650160540837e0d,0x8268d20916d0a8cb42ca3520819db83860ac40c32a1c4368ca0286320303a0640b8150260440f7761c,0x1dda3280b03a0640b8150260440f8260a,0x5a259d8a9632aa504891452b65ac9e9516300c,0x2384794d29b63651db391082c464911172300c,0x18ab166ce51a0b91763006,0x12626648c981382584d4949126ce4c8929462bc574ae4182f43c9fd0f30b2cb42b9022764bdb81172fa4151b23553421,0x931332464c09c12c26a4a489367264494a315e2ba5720c17c1e8e5c2c9042764bdb841222c5ec81a344670560c8544350460a1792023c202c085342a,0x3c5e0bfa4523cc3385970ccb4310544500b,0x556e0cb48285946a3ce0abfa4683ca0916d8361588186543886e08a198343c202c0820019,0xe289791780003,0x6e089c803d60aa8a9968f3730158b7c062060c,0x40133086603c067f805,0x3fa0b23c20f32283a5f482a3646af251a0f28248951897b43707e0e4061e615,0x3c5eb3fa4523cc3385970ccb4310541e05b4b64200ac1950e21b83e8960e40645017,0x931332464c09c12c26a4a489367264494a315e2ba5720c17c1e8e5c2c9042764bdb81162f640d1a2337930642a2321e05b4b641c2025e610c065342a,0x7d1ff3fc4365ed912327928d50d0670a8e19968640ac5be0e97c330690f69ff83818e10a3482508a034077fa1f,0x7cefe9cc0f48463ca094221e008,0xb7b867ce19c782297f4fa4798598483ca0942220218e10c060c812,0x42530c01,0x4253ce01,0x101a1342572a03,0x42633001,0x42634801,0x4263da01,0x4263fe01,0x859096034298550ae13c286ee08,0x11422920419db838620218e134067ba0a,0x2fa5ed1aa1b79b07e172261defe8322341e45be093e72d83cc8242664414,0x2f240600a1c0c8e1833a350a8188b6c121e4fe87842f1e709e1340683214,0x22645240033b7070c40c32a337930c03116d8248a0790f17f48c87842f2083ce134067ba19,0x4310b201,0x931332464c09c12c26a4a489367264494a315e2ba5720c17c1e8e5c9d92f824458bda34466f24bca32802f9d0e16f86509a0342753426,0x6448c87a17b792fe90da341e4ffa090ef4345b42a85465a15a19c2680d0b613c322f818,0x43446a01,0x43446c01,0x4350ce01,0x43520a01,0xdc10d9007fe155c332d0c815a1c42784d0a21bc322060f,0x4392de01,0x43943801,0x43a7ce01,0x21b43a83a02,0x80d09a13c3b80204,0x43c1e001,0x43d2da01,0x43e20201,0x43e2f201,0x4400a801]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOkW127_4 : checkRows bookW127 11 1012 rowsW127_4=true := by decide +kernel

def lastUnitsW127 := digits 11 5 0x4348870fe20c42
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflictW127 : checkReasons bookW127 1092 1049 lastUnitsW127 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem excludeW127 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D≤1) (bp : Bplus 14 D=10) (eq : mask 127=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout_budget (k:=3) h hc (by rw [bp]; decide +kernel) eq
  let v := truth Z aW127
  have hbase : ValidThrough v bookW127 628 := book_start_budget Z h hc z eq _ _ _ _ initialClausesW127
  have h0 : ValidThrough v bookW127 724 := rows_sound hbase rowsW127_0 rowsOkW127_0
  have h1 : ValidThrough v bookW127 820 := rows_sound h0 rowsW127_1 rowsOkW127_1
  have h2 : ValidThrough v bookW127 916 := rows_sound h1 rowsW127_2 rowsOkW127_2
  have h3 : ValidThrough v bookW127 1012 := rows_sound h2 rowsW127_3 rowsOkW127_3
  have h4 : ValidThrough v bookW127 1092 := rows_sound h3 rowsW127_4 rowsOkW127_4
  exact book_end h4 _ _ conflictW127
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def aW1290 := ([1,0x801,0xa0021,0xc0021,0x827,0xa00a1,0xa08a1,0xc00c1,193,0xa00c1,0xc08c1,0x8c1,0xa08c1,0x48c7,0x248c7,0x120101,0x160101,0x2107,0x4907,0x120121,0x120921,0x160161,0x160961,5,0x20005,6,0x1805,0xa1806,0xc1806,0x6805,0x26805,0xa6806,0x8005,0x28005,0x8006,0x8805,0x28805,0xa8806,0xc8806,0x9005,0x29005,0xa9006,37,0x1825,0x21825,0x6825,0x26825,0x8025,0x128026,0x168026,0x8825,0x28825,0x128826,0x9025,0x29025,0x169026,0x8004,0x6864,0x8864,0x89a4,0x8a04,0x9204,0x9224] : List Nat).toArray.map readPackedFact
def rW1290 := ([0,0x800,0x825,0x22829,0x23029,160,0x8a0,192,0x8c0,0x48c5,0x1200c9,0x1228c9,0x9200c9,0x9228c9,0x2105,0x84909,0x4905,0x125909,288,0x920,352,0x960,16,0x20000012,0x20020012,0x1810,0x2801812,0x3001812,0x6810,0x22806812,0x22826812,0x8010,0x8012,0x28012,0x8810,0x23008812,0x23028812,0x9010,0x2809012,0x2829012,48,0x1830,0x6830,0x8030,0x4808032,0x5808032,0x8830,0x24808832,0x24828832,0x9030,0x25809032,0x25829032,0x20200013,0x200034,0x29a1813,0x1a1834,0x9a1834,0x3221813,0x221834,0xa21834,0x22a26813,0x226834,0xa26834,0x228014,0xa28014,0x4a28033,0x248014,0xa48014,0x5a48033,0x248814,0xa48814,0x22a48813] : List Nat).map readPackedBudget

def tableW1290_0 : List Nat := [65,193,577,0x8202,0xc202,705,833,961,0x541,0x3a6c2,0x20682,0x24682,0x2c702,0x30702,0x8c1,0x3c882,0x941,0x40902,0x9c1,0xa41,0xac1,0xb41,0x62bc2,0x3300b83,0x3304c03,0xd41,0x360ad03,0x380ed03,0x7aec2,0x3f14e83,0x3f18f03,0x87042,0x4423003,0x442f083,0x931c2,0x4d1d183,0x4d29203,0xa33c2,0x5227383,0x5233403,0x1541,0xb35c2,0xbb6c2,0x17c1,0x603f783,0x6243783,0xcf942,0x694d903,0x6951983,0xdbac2,0x6f55a83,0x6f59b03,0x4565c03,0x71bd503,0x3e6fc83,0x73b5583,0x73b9603,0x4c73d03,0x75c9583,0x75cd603,0x4b7dd83,0x77c9683,0x77cd703,0x798d003]
def tableW1290_1 : List Nat := [0x7991083,0x68c3e03,0x7b9d003,0x7ba1083,0x6ec7e83,0x7d9d183,0x7da1203,0x5395f03,257,385,0x781,0x801,0x66b82,0x66c02,0xd81,0xe01,0x7ee82,0x7ef02,0x9b182,0x9b202,0x1801,0x1881,0xd3902,0xd3982,0xdfa82,0xdfb02,0x1c41,0x7dc82,0x99d02,0xd1e02,0xdde82,0x1bc1,0x1e81,0x1a41,0x1e01,0x1341,0x1d01,0xfc1,0x1c81,0xcc1,0x1141,0xa5402,0xa5382,0x1481,0xef902,0x1dc1,0x12c1,0x1f01,0x1081,0x1041,0x1381,0x1181,0x1441,0x1241]

def encodedW1290 (i : Nat) : Nat :=
  if i < 64 then
    tableW1290_0.getD (i%64) 0
  else
    tableW1290_1.getD (i%64) 0
def bookW1290 (i : Nat) : Clause := let n := encodedW1290 i; unpackLits 7 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClausesW1290 : inputsOKBudget 0 1290 aW1290 rW1290 (baseBook bookW1290 72).toList=true := by decide +kernel

def rowsW1290_0 : List Nat := [0x20601,0x20801,0xe1e01,0x102201,0x2e01,0x13001,0x24193402,0x24993602,0x53a01,0x63c01,0x74601,0x84801,0x252b5802,0x25ab5a02,0x125e01,0x136001,0x146401,0x156601,0x15a86a02,0x4e6c01,0x4f7201,0x548201,0x558801,0x2cd86202,0x5fbc01,0x2bd65c02,0x61ba01,0x29d24402,0x63b801,0x28d03802,0x65b601,0x26cc2c02,0x2d676802,0x4024f8d869f0681408,0x4224f8b849b0681808,0x12e9d402,0x15297aeb3647006,0x54a5f3b5db33646e08,0x32ed7802,0x35ee8e02,0x9514381bf0628a07,0x703e01,0x30718402,0x31717e02,0x724a01,0x734401]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOkW1290_0 : checkRows bookW1290 7 72 rowsW1290_0=true := by decide +kernel

def lastUnitsW1290 := digits 7 3 0x1bfa75
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflictW1290 : checkReasons bookW1290 118 70 lastUnitsW1290 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem excludeW1290 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D≤1) (bp : Bplus 14 D=10) (eq : mask 1290=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout_budget (k:=0) h hc (by rw [bp]; decide +kernel) eq
  let v := truth Z aW1290
  have hbase : ValidThrough v bookW1290 72 := book_start_budget Z h hc z eq _ _ _ _ initialClausesW1290
  have h0 : ValidThrough v bookW1290 118 := rows_sound hbase rowsW1290_0 rowsOkW1290_0
  exact book_end h0 _ _ conflictW1290
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def aW4757 := ([1,0xc0001,0x3007,0x2802,0x2822,0x4002,0x4022,0x6802,0x6822,0x40041,65,0xc0041,0xc047,0x40081,0x3087,0x8a0,0x200a1,0x600a1,0xc00a1,0x1000a1,0x40a3,0x1a00a1,0x68a3,0x10a0,0x208a1,0x608a1,0xc08a1,0x1008a1,0x1a08a1,0x18a0,0x210a1,0x610a1,0xc10a1,0x1010a1,0x1a10a1,0x38a7,0x238a7,0x438a7,0x638a7,0xe0a7,0x2e0a7,0x4e0a7,0x6e0a7,0x448a8,0x8448a8,0x10448a8,0x18448a8,0x3048a8,0xb048a8,0x13048a8,0x1b048a8,0x460a8,0x8460a8,0x10460a8,0x18460a8,0x3060a8,0xb060a8,0x13060a8,0x1b060a8,0x102809,0x102829,0x1a2809,0x1a2829,0xc00c1,0xc08c1,0xc10c1,0xc18c1,0x100101,0x900,0x140101,0x1a0101,0x6903,0x100901,0x1100,0x140901,0x1a0901,0x101101,0x1900,0x141101,0x1a1101,0x101901,0xe107,0x2e107,0x4e107,0x6e107,0x3a0108,0xba0108,0x13a0108,0x1ba0108,0x1a4009,0x1a4029,0x120121,0x140121,0x3127,0x140141,0x140941,0x141141,0x141941,0x120181,0x140181,0x2187,0x3187,0x9a0,0xa01a1,0x1001a1,0x1401a1,0x1601a1,0x11a0,0xa09a1,0x1009a1,0x1409a1,0x1609a1,0x19a0,0xa11a1,0x1011a1,0x1411a1,0x1611a1,0xa19a1,0x1019a1,0x1619a1,0x11a7,0x211a7,0x411a7,0x611a7,0x39a7,0x239a7,0x439a7,0x639a7,0x49a7,0x249a7,0x449a7,0x649a7,0x59a7,0x259a7,0x459a7,0x659a7,0x3e11a8,0xbe11a8,0x13e11a8,0x1be11a8,0x3a21a8,0xba21a8,0x13a21a8,0x1ba21a8,0x3e21a8,0xbe21a8,0x13e21a8,0x1be21a8,0xa6809,0xa6829,0x106809,0x106829,5,6,0xc0006,0x2805,0x2806,0xc2806,0x3005,0x43006,0x5005,0x6005,0x46006,0x6805,0x26805,0x46805,0x66805,0x7005,0x27005,0x47005,0x67005,0x7805,0x27805,0x47805,0x67805,0x8005,0x28005,0x48005,0x68005,0xc8006,37,0x20025,0x40025,0x60025,0x2825,0x22825,0x42825,0x62825,0x102826,0x3025,0x23025,0x43025,0x63025,0x103026,0x5025,0x25025,0x45025,0x65025,0x145026,0x6025,0x26025,0x46025,0x66025,0x146026,0x6825,0x126826,0x146826,0x7025,0x27025,0x47025,0x67025,0x147026,0x7825,0x127826,0x147826,0x8025,0x28025,0x48025,0x68025,0x2804,0x8004,0x30a4,0x80a4,0x60c4,0x6144,0x71a4,0x79a4,0x79c4] : List Nat).toArray.map readPackedFact
def rW4757 := ([0,0x3005,0xc3009,64,0xc045,0x300049,0x303049,0x3085,0xc1089,0x8a1,163,164,0x8a4,0x38a5,0xe08a9,0xe18a9,0xe40a9,0x8e08a9,0x8e18a9,0x8e40a9,0x10e08a9,0x10e18a9,0x10e40a9,0x638a7,0xe0a5,0x3818a9,0x3830a9,0x3868a9,0xb818a9,0xb830a9,0xb868a9,0x13818a9,0x13830a9,0x13868a9,0x6e0a7,0x10248aa,0x11048aa,0x210248aa,0x211048aa,0x410248aa,0x411048aa,0x18448a8,0xc0c48aa,0xc1a48aa,0x2c0c48aa,0x2c1a48aa,0x4c0c48aa,0x4c1a48aa,0x1b048a8,0x10660aa,0x11060aa,0x210660aa,0x211060aa,0x410660aa,0x411060aa,0x18460a8,0xc0660aa,0xc1a60aa,0x2c0660aa,0x2c1a60aa,0x4c0660aa,0x4c1a60aa,0x1b060a8,0x10280b,0x10280c,0x40ae,0x10282b,0x10282c,0x240ae,0x8040af,0x10040af,0x10240af,0x1a280b,0x1a280c,0x68ae,0x1a282c,0x268ae,0x8068af,0x10068af,0x10268af,192,0x8c0,0x10c0,0x18c0,256,0x900,0x901,0x1100,0x1900,259,260,0x904,0xe105,0x385109,0x386909,0xb85109,0xb86909,0x1385109,0x1386909,0x6e107,0xe94010a,0xe9a010a,0x2e94010a,0x2e9a010a,0x4e94010a,0x4e9a010a,0x1ba0108,0x1a400b,0x1a400c,0x1a402b,0x1a402c,0x4690d,0x80690f,0x100690f,0x102690f,288,0x3125,0xc5129,320,0x940,0x1140,0x1940,0x2185,0x84989,0x3185,0xc5189,0x9a1,0x11a1,419,420,0x9a4,0x11a5,0x429a9,0x441a9,0x8429a9,0x8441a9,0x10429a9,0x10441a9,0x611a7,0x18429a9,0x18441a9,0x39a5,0xe41a9,0xe51a9,0x8e41a9,0x8e51a9,0x439a7,0x10e41a9,0x10e51a9,0x639a7,0x49a5,0x1229a9,0x1259a9,0x9229a9,0x11229a9,0x11259a9,0x649a7,0x19229a9,0x19259a9,0x59a5,0x1629a9,0x9659a9,0x11629a9,0x659a7,0x19629a9,0xf8a11aa,0xf9011aa,0x2f8a11aa,0x2f9011aa,0x4f8a11aa,0x4f9011aa,0x1be11a8,0x6f8a11aa,0x6f9011aa,0xe9021aa,0xe9421aa,0x2e9021aa,0x2e9421aa,0x4e9021aa,0x4e9421aa,0x1ba21a8,0xf8a21aa,0xf9621aa,0x2f8a21aa,0x2f9621aa,0x4f8a21aa,0x4f9621aa,0x1be21a8,0x6f8a21aa,0x6f9621aa,0xa680c,0xa682b,0xa682c,0x8029af,0x10029af,0x18029af,0x10229af,0x18229af,0x18429af,0x10680b,0x10680c,0x10682b,0x10682c,0x8041af,0x10041af,0x10241af,0x460a48b5,0x3048a60b5,0x3a01021b5,0x3e11a21b5,16,0x20000012,0x3000012,0x2810,0x2812,0x3002812,0x3010,0x21003012,0x5010,0x6010,0x1006012,0x6810,0x46811,0x66811,0x7010,0x47011,0x67011,0x7810,0x47811,0x67811,0x8010,0x23008012,0x23028012,0x23048012,0x23068012,48,0x40031,0x60031,0x2830,0x24002832,0x24022832,0x42831,0x24042832,0x62831,0x24062832,0x3030,0x4003032,0x4023032,0x43031,0x63031,0x5030,0x25005032,0x25025032,0x25045032,0x25065032,0x6030,0x5006032,0x5026032,0x46031,0x66031,0x6830,0x24806832,0x5006832,0x7030,0x25007032,0x25027032,0x25047032,0x25067032,0x7830,0x4807832,0x5007832,0x8030,0x48031,0x68031,0x200a0013,0xa0034,0x8a0034,0x3200013,0x200034,0xa00034,0xc2814,0x240c2833,0x3202813,0x202834,0xa02834,0x21183013,0x183034,0x983034,0x185014,0x25185033,0x1c6814,0x9c6814,0x51c6833,0x1e6814,0x9e6814,0x249e6833,0x1e7014,0x9e7014,0x251e7033] : List Nat).map readPackedBudget

def tableW4757_0 : List Nat := [65,321,0x10102,0x4c1,0x641,0xa0602,0xb0602,0x741,0xd0702,0xf8b82,0x9038b83,0x38e82,0x48e82,0x9a4b2491c4,0x101182,0x111182,0x131182,0x181202,0x191202,0x1b1202,0x1e1282,0x1f1282,0x211282,0x1d9302,0xaa532893c4,0x111382,0x121382,0x151382,0x191402,0x1a1402,0x1c1402,0x1f1482,0x201482,0x221482,0x1d9502,0x109582,0x131582,0x189602,0x1b1602,0x1e9682,0x211682,0x1d9702,0x129782,0x151782,0x1a9802,0x1c1802,0x209882,0x221882,0x1d9902,0x119982,0x131982,0x199a02,0x1b1a02,0x1f9a82,0x211a82,0x1d9b02,0x119b82,0x151b82,0x199c02,0x1c1c02,0x1f9c82,0x221c82,0x1d9d02,0x39d82]
def tableW4757_1 : List Nat := [0x51d82,0x29050183,0x49e02,0x61e02,0x29060203,0x3c9dc6e270f0a06,0x3c9dc8627170a06,0x3c9dc8637170a06,0x39e82,0x71e82,0x2d070183,0x81f02,0x2d080203,0x3e9ec722b0f0b06,0x3e9ec8a2b170b06,0x3e9ec8a39170b06,0x1fc1,0x2041,0x20c1,0x2141,0x21c1,0x2441,0x44a482,0x2641,0x2841,0xd05a483,0x5a682,0x6a682,0x152a752a8c4,0x452882,0x462882,0x4a2902,0x4b2902,0x4e2982,0x4f2982,0x4daa02,0x45aa82,0x462a82,0x4aab02,0x4b2b02,0x4eab82,0x4f2b82,0x4dac02,0x5ac82,0x72c82,0x6ad02,0x82d02,0x23c1,0x5aacd2e8d442386,0x5aacd3e8d492386,0x5aacd3e97492386,0x2dc1,0x2ec1,0x5c2e82,0x2f41,0x2fc1,0x3041,0x30c1,0x3241,0x623202,0x32c1,0x633282,0x66b582,0x6bb802]
def tableW4757_2 : List Nat := [0x1107b583,0x7b802,0x8b802,0x1eef579bc44,0x673c02,0x683c02,0x6c3c82,0x6d3c82,0x713d02,0x723d02,0x70bd82,0x753d82,0x763d82,0x1fefd7dbe44,0x683e02,0x693e02,0x6d3e82,0x6e3e82,0x6bbf02,0x723f02,0x733f02,0x70bf82,0x20f0581c044,0x674002,0x6a4002,0x6c4082,0x714102,0x744102,0x70c182,0x754182,0x774182,0x21f0d85c244,0x674202,0x6f4282,0x714302,0x70c382,0x754382,0x674402,0x68c402,0x6c4482,0x6dc482,0x714502,0x72c502,0x70c582,0x754582,0x76c582,0x684602,0x69c602,0x6d4682,0x6ec682,0x724702,0x73c702,0x70c782,0x674802,0x6ac802,0x6c4882,0x6fc882,0x714902,0x74c902,0x70c982,0x754982,0x77c982,0x34a02,0x8ca82]
def tableW4757_3 : List Nat := [0x44a82,0x95ca5b2cf660b06,0x95ca5c6cf6b0b06,0x95ca5d6cf700b06,0x95ca5c6d96b0b06,0x95ca5d6d9700b06,0x95ca5d6e3700b06,0x7cb02,0x54b02,0x8cb82,0x64b82,0x97cb5b6d1662386,0x97cb5cad16b2386,0x97cb5cadb6b2386,0xda6b3499cba5b2c95c8,0xca633097cea73389bc8,0x162af56aae3f1d8dc648,0x22f1589c464f2591c848,0x4c41,0x133004c03,0x13401cc03,0x4dc1,0x1380acd83,0x13a0bcd83,0x4f41,0x13f094f03,0x5041,0x50c1,0x1440dd083,0x29b4ba4d1c4,0x17d282,0x1dd302,0x2ab53a8d3c4,0x17d482,0x1dd502,0x2bb5bacd5c4,0x17d682,0x1dd702,0x2cb63b0d7c4,0x1673f5783,0x167405803,0x167415883,0x167425903,0x2df6db5da44,0x49db02,0x4ddb82,0x2ef75b9dc44,0x179435c03,0x179485c83,0x49dd02,0x1794c5d03,0x4ddd82,0x179505d83,0x3037fbedec4,0x18268de83,0x1826ddf03,0x6bdf82,0x70e002,0x31789c3e144,0x18d5e6103,0x18d5f6183,0x18d606203,0x18d616283,0x32b93c8e3c4]
def tableW4757_4 : List Nat := [0x19669e383,0x1966ee403,0x6be482,0x70e502,0x6641,0x19b5b6603,0x19c5ce603,0x34ba3d0e7c4,0x1a75e6783,0x1a75f6803,0x1a7606883,0x1a7616903,0x6a41,0x1aa62ea03,0x1ac63ea03,0x36bb3d8ebc4,0x49ec82,0x4ded02,0x139996d83,0x1b7b85a03,0x1b7b95a83,0x1669aee03,0x1b9d75a03,0x1b9d85a83,0x1bb9e4d83,0x183bc6e83,0x1669def03,0x1bdd75c03,0x1bdd85c83,0x1459f6f83,0x1bfc75e83,0x1bfc85f03,0x1c1a15003,0x197c67003,0x1c3a75183,0x1c3a85203,0x1a6cef083,0x1c5ab5183,0x1c5ac5203,0x1abcd7103,0x1c7ab5383,0x1c7ac5403,0x1add37183,129,0x501,0x581,0x681,0x2d5669746a205,0x2d5669f46a485,0x2d5669f4ba485,0x2e01,0x3101,0x3181,0x4be5adb68b305,0x4be5ae568b585,0x4be5ae56db585,0x4cc1,0x4d01,0x4e01,0x4e81,0x4fc1,0x5101,0xb3d782,0xb3d802]
def tableW4757_5 : List Nat := [0xb3d882,0xb3d902,0xbcdc02,0xbcdc82,0xbcdd02,0xbcdd82,0xc6e102,0xc6e182,0xc6e202,0xc6e282,0x66c1,0x6701,0xd3e782,0xd3e802,0xd3e882,0xd3e902,0x6a81,0x6b01,0x6d81,0xb85a02,0xb95a82,0xb36e02,0x6ec1,0xc1de02,0xb36f02,0x6f81,0xc75e82,0xc85f02,0x7041,0xcbe302,0xd37082,0x7101,0xd37182,0x69c1,0x7081,0x7181,0x59c1,0x6e01,0x6f01,0xe01d4983,0xe01d4003,0xe01d3643,0xd6948b2572780bce071391ba8b,0x700e82,0x3b17d603,0x1d8bc2,0xe0161c83,0xe0161383,0xe0161403,0x700b02,0x3801,0x3d81,0x3f81,0x4181,0x4381,0x4581,0x4781,0x4981,0x6001,0x6501,0xece6631c0a85,0x713602,0x9a039683,0x4d01cd669339186]
def tableW4757_6 : List Nat := [0x4d01cd669339206,0x2680e6b3499c5,0x9a039983,0x9a039a03,0x4d01c2,0x173b8de43,0x32cf9beb5c4,0x360b2c08714406,0x94821b2cf07b586,0x32cfbbdb5c4,0x360b2c08713686,0x30596beb5c4,0x1810d96b33c5,0x1b0596043885,0xc086b0b44,0x4a5c72b6b0b05,0xc0871b584,0x182cb35c3,0xd82cb0204,0x1d95cce5b358d86,0x9a1d9183,0x9a1d9203,0x9a1d9283,0x4d0ec2,0x6341,0x65c1,0xbcdc42,0x5e41,0x60c1,0x35c1,0x3341,0xe81,0x1301,0x1501,0x1701,0x1901,0x1b01,0x1d01,0xbc1,0x2681,0x7c1,0x2a01,0x2c01,0x5b81,0x5d81,0x6d01,0x16ab3492b84,0xb58dc663ab3492887,0xb58dc663ab3492907,0x5ac6e331d59a486,0xb924c2,0x1bce6711c1105,0x6f3d9cce27d160e07,0x3d9cce26f3e8b06,0x25b2f7dc604,0x1240d08b684,0x92068443,0xf67d161c04,0x1f4f66f388b05,0x6f040403,0x92230203,0x129958b03,0x30442,0xfa6f161ec4]
def tableW4757_7 : List Nat := [0x1395cce79030286,0x12446683904,0x1244696b6c4,0x92234b43,0x491182,0xe378183,0x900e0608c4,0x480601c3,0x92244b03,0x1f49e2b161ec5,0x24a5ab505b685,0x1252d5a82c4,0x92240183,0x491202,0x801c2,0x4a030283,0x490402,0x2481,0x5b01,0x5d01,0x6c81,0x5c81,0x5c41,0x5a01,0x6b81,0x5ac1,0x6c41]

def encodedW4757 (i : Nat) : Nat :=
  if i < 256 then
    if i < 128 then
      if i < 64 then
        tableW4757_0.getD (i%64) 0
      else
        tableW4757_1.getD (i%64) 0
    else
      if i < 192 then
        tableW4757_2.getD (i%64) 0
      else
        tableW4757_3.getD (i%64) 0
  else
    if i < 384 then
      if i < 320 then
        tableW4757_4.getD (i%64) 0
      else
        tableW4757_5.getD (i%64) 0
    else
      if i < 448 then
        tableW4757_6.getD (i%64) 0
      else
        tableW4757_7.getD (i%64) 0
def bookW4757 (i : Nat) : Clause := let n := encodedW4757 i; unpackLits 9 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClausesW4757 : inputsOKBudget 2 4757 aW4757 rW4757 (baseBook bookW4757 299).toList=true := by decide +kernel

def rowsW4757_0 : List Nat := [0x40401,0x100a01,0x100c01,0x1c1001,0x1bce001,0x1bce201,0x1bce401,0x1d0ea01,0x1e8f601,0x1f0fa01,0x1bd9601,0x1bd9801,0x1bd9a01,0x349a602,0x95b49a802,0x96355ac02,0x96b55ae02,0x1b61b202,0x9736db802,0x141ce01,0x145d001,0x149d201,0x14dd401,0x151de01,0x155e001,0x15de401,0x161e801,0x1d9f601,0x1ddf801,0x1e1fa01,0x1e5fc01,0x39c120a02,0x994120c02,0x1da1001,0x1de1201,0x1e21401,0x1e61601,0x99c321a02,0x9a4321c02,0x9d4e22402,0x54a2601,0x54a2801,0x4e62a01,0x6c3563002,0x55a3201,0x4ee3401,0x9ecf23a02,0x5663c01,0x5663e01,0x6db6a4002,0x5724201,0x52e4801,0xa852a4e02,0x5465401,0x29f4ea6d320e04,0x586bc01,0x586c001,0x283409fcf9cc04,0x592aa01,0x592b001,0x994ba693cc561b197abc5f1281681600312c0f,0x42b4506ac45ae552885ba9d0cb661b0982984b9f8febe2502d02c00659d4c1a,0x2e150a143a7d06b552a8108ac5222d72a95122182c5621f8febe2502d02c00659da21d,0x44b4506b552a1174c24da692cac4ea2d540e,0x4634506b552a1172a94430d8d6a5ba9d3286b4da2cec0252f8180b3fa055a1a,0xe06eca64cdf71379c362b1d7e440b,0xe06eca24ae3b6391c2de6fb89cb62b1d7e460f,0xd8789c4f0f8f478494092d0422b6dac300e,0x5e3b169389a2a1c06c341924a049682180f8136db5db99e14,0x722b179349e2c1d0783a1c24a049682180f8136db5db99e14,0x1c8ac762d2713c5c2110062e16fb7125024b41088603eb6dad9e16,0x4c255c6db6b412041407,0x5c91401,0x5c92a01,0x5c93801,0x5c94601,0x5c95601,0x5c96801,0x5c97601,0x5c9f201,0x5ca0601,0x1c8ac603e168ed9e06,0x5b29930854b20d6ea74ca19109a54ae6f377badcda212,0x20132311c282813900b4430b910156d0596c1a10,0x3388a2308038805a218a46e092202ada0b2ddf84c11,0x3388a2509844805a218a46e092202ada0b2ddf84811,0x48262311c2c0dc05fc805a2185c52372202ada0b2ddf99c14,0x5826462283c643120168861704910156d0596c1a11,0x58204722848683320168861704910156d0596c1a11,0x10099188e151b0d70383c1110156d0b82c805a2196c1a13,0xa2d11dc02,0x101ad245ea8d813e1257bbd5d1fe0b,0x13094c13f619ee8741a390aa652af98088bedcd0011,0x182803f3009804,0x100ada3dea8d813e1257bbd5d1fe0b,0xc1c41fb12f642a11069043af98088bedcc940f]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOkW4757_0 : checkRows bookW4757 9 299 rowsW4757_0=true := by decide +kernel

def rowsW4757_1 : List Nat := [0x239eb867c5e9ec05,0x30710be601f89405,0x50b453eb55063316f75462b0f7d5caa54579bbdd97012,0x261290002,0x174aa4da252c835ba9d32865aa952e846230ae775bbde5a214,0x18e5f3031e03,0x312ff4856def8b815eeb408,0xc6e472002,0x6826148dd9c04,0x64c6c28230c446100783880432d907085a04db48a11,0xd850321211c8a331284c24112010cb641c2168523704db59c15,0x64241a0988c471a89c2c150a100865b20e10b4291bdb59c14,0x2f96cae501a04,0x29348a3d19f404,0x662ba01,0x6168601,0x50b3401,0x66eae01,0xcce732202,0x674fc01,0x180bcce732404,0x67c2e01,0x67c4401,0x67c5201,0x67c6001,0x67c6e01,0x67c7c01,0x67eda01,0x67f2e01,0x6981201,0x69cc601,0x69cd401,0x69dda01,0x69de601,0x69e2201,0xbc60984c4c269346a4b808,0x3425e642f174adaebc6a8ce09,0x3425e663017cadaebc6a8ca09,0xca67984c4c45cd86bf5d78d56a5a00c,0x87bae20ecaa472cbadd5d9a2c0a,0xd33c302f108785ba5d1e84540a,0x17062f81b276cc3da1cfe98400a,0x1d67860561b178849a4fda69b51a1d1e94580f,0x9347cd95eaeba6751a07,0x239293659acb63b658240dac82cb24d880ba6751a11,0x91d8a355c8e5924e6b37db9b100c936b20b374cf6756213,0xd8849a4f0e0ec75a1d4698300a,0xd8789c4f0f8f479b5d3684300a,0x1b92612c9192ce6677407,0x64c6c282311087b8dd8ff241011838623807ea33fa6cce708a15,0xb8542850e9f41ad54aa042306fab954a89118fcee7ae776bbde5a217,0x12900bf5f6777a05,0x6eb7201,0x6c281a0988c452090349a2d36a19c0c,0x247628d5924cddbe35f001442de0c41e23070411caeba6996215,0x3833565167800a216f0620f11838219dcf69a6e10,0x8e4a4d966b2d8ed96090e11bb7c6b65167800a216f0620f118382174cee991a1b,0x4a24b1f864bdf02b783807e9b7e0b,0x964adf1277e04,0xd8502423914880a1ff1470310989422330910f49a2d36a19c15,0x36140c8484722910143f0989422330910f49a2d36a19c13,0x210f1389a3925f1495bee38678c5924b218fa1d36a03013,0x210f1389ba1d36a03007,0x472526cb3596c76cb0481ad9459ba6751a0e,0x123b146ab91cb249cd66fca65164d774cf6756210,0xd850321211c8a412072cdc42df6482625088cc25c8d268b4da8cce719c19,0x32391c6ec984bdc71c1448e669b920c,0x647238dd930144825e9b9209,0x64241a0988c47209002c270a0d42a42c969345a6ce6659c14,0x392381cf14944963f2f9fce3712c1bcde26803210,0xc84834131188e44050fc87bedc7406a270b054280de6f1349a2d36819c19,0x745d801,0x745e201,0x7462001,0x7476401,0x1aceaf4ddc03,0x75aa601,0xb375a3602,0x1abe975dd603,0x1adea7621e03]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOkW4757_1 : checkRows bookW4757 9 395 rowsW4757_1=true := by decide +kernel

def lastUnitsW4757 := digits 9 3 0x597b5d9
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflictW4757 : checkReasons bookW4757 475 279 lastUnitsW4757 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem excludeW4757 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D≤1) (bp : Bplus 14 D=10) (eq : mask 4757=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout_budget (k:=2) h hc (by rw [bp]; decide +kernel) eq
  let v := truth Z aW4757
  have hbase : ValidThrough v bookW4757 299 := book_start_budget Z h hc z eq _ _ _ _ initialClausesW4757
  have h0 : ValidThrough v bookW4757 395 := rows_sound hbase rowsW4757_0 rowsOkW4757_0
  have h1 : ValidThrough v bookW4757 475 := rows_sound h0 rowsW4757_1 rowsOkW4757_1
  exact book_end h1 _ _ conflictW4757
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore

open DagTools

theorem cap_ten_impossible {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (short : D.length ≤ 24) (small : Bplus 14 D ≤ 10) : False := by
  obtain ⟨m, hm, eq, ht⟩ := small_classification h hc short
  have lo := surplus_ten h hc
  have bp : Bplus 14 D=10 := by omega
  have total := surplus_identity h
  rw [totalSurplus_split] at total
  have bz : Bzero 14 D≤1 := by omega
  have ten := ht small
  simp only [tenMasks,List.mem_cons,List.not_mem_nil,or_false] at ten
  have transfer (i j : Nat) (a : Equiv.Perm V) (perm : auto a)
      (ei : mask i=ineligSet 14 D) (mv : (mask i).image a=mask j)
      (impossible : ∀ {E : Dag}, StrictLive 14 E → sem_Comp 14 adj E →
        Bzero 14 E≤1 → Bplus 14 E=10 → mask j=ineligSet 14 E → False) : False := by
    have strict := relabel_strictLive a h
    have comp := rename h hc a perm
    have zero : Bzero 14 (relabel a D)≤1 := by simpa only [relabel_Bzero a h] using bz
    have plus : Bplus 14 (relabel a D)=10 := by simpa only [relabel_Bplus a h] using bp
    have pat : mask j=ineligSet 14 (relabel a D) := by
      rw [relabel_ineligSet a h.1, ←ei, mv]
    exact impossible strict comp zero plus pat
  rcases ten with rfl | rfl | rfl | rfl | rfl
  · exact Compact.excludeW127 h hc bz bp eq
  · exact Compact.excludeW1290 h hc bz bp eq
  · exact Compact.excludeW4757 h hc bz bp eq
  · exact transfer 8488 1290 graphPerm1 auto1 eq (by decide +kernel) Compact.excludeW1290
  · exact transfer 16256 127 graphPerm2 auto2 eq (by decide +kernel) Compact.excludeW127

theorem no_empty_surplus {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (short : D.length ≤ 24) : Bplus 14 D=11 ∧ Bzero 14 D=0 := by
  have total := surplus_identity h
  rw [totalSurplus_split] at total
  have high : 10 < Bplus 14 D := lt_of_not_ge (cap_ten_impossible h hc short)
  omega

theorem reject55 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (bz : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 55=ineligSet 14 D) : False := by
  have bound := projection55 h hc bz eq
  omega

theorem reject63 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (bz : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 63=ineligSet 14 D) : False := by
  have bound := projected_exclude63 h hc bz eq
  omega

theorem reject95 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (bz : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 95=ineligSet 14 D) : False := by
  have bound := projection95 h hc bz eq
  omega

theorem reject103 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (bz : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 103=ineligSet 14 D) : False := by
  have bound := projection103 h hc bz eq
  omega

theorem reject111 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (bz : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 111=ineligSet 14 D) : False := by
  exact residual_exclude111 h hc bz bp eq

theorem reject119 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (bz : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 119=ineligSet 14 D) : False := by
  have bound := projection119 h hc bz eq
  omega

theorem reject123 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (bz : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 123=ineligSet 14 D) : False := by
  have bound := projection123 h hc bz eq
  omega

theorem reject181 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (bz : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 181=ineligSet 14 D) : False := by
  have bound := projection181 h hc bz eq
  omega

theorem reject229 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (bz : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 229=ineligSet 14 D) : False := by
  have bound := projection229 h hc bz eq
  omega

theorem reject245 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (bz : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 245=ineligSet 14 D) : False := by
  have bound := projection245 h hc bz eq
  omega

theorem reject661 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (bz : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 661=ineligSet 14 D) : False := by
  have bound := projection661 h hc bz eq
  omega

theorem reject2213 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (bz : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 2213=ineligSet 14 D) : False := by
  exact residual_exclude2213 h hc bz bp eq

theorem reject2693 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (bz : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 2693=ineligSet 14 D) : False := by
  have bound := projection2693 h hc bz eq
  omega

theorem reject4245 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (bz : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 4245=ineligSet 14 D) : False := by
  have bound := projection4245 h hc bz eq
  omega

theorem reject4309 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (bz : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 4309=ineligSet 14 D) : False := by
  have bound := projection4309 h hc bz eq
  omega

theorem reject4757 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (bz : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 4757=ineligSet 14 D) : False := by
  exact residual_exclude4757 h hc bz bp eq

theorem reject5190 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (bz : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 5190=ineligSet 14 D) : False := by
  have bound := projection5190 h hc bz eq
  omega

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem smaller_closed {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (short : D.length ≤ 24) : False := by
  obtain ⟨m, mem, eq, _⟩ := small_classification h hc short
  have shift (i j : Nat) (a : Equiv.Perm V) (perm : auto a)
      (ei : mask i=ineligSet 14 D) (mv : (mask i).image a=mask j)
      (impossible : ∀ {E : Dag}, StrictLive 14 E → sem_Comp 14 adj E →
        Bzero 14 E=0 → Bplus 14 E=11 → mask j=ineligSet 14 E → False) : False := by
    obtain ⟨E, strict, comp, len, pat⟩ := move_case h hc short i j ei a perm mv
    obtain ⟨bp,bz⟩ := no_empty_surplus strict comp len
    exact impossible strict comp bz bp pat.symm
  have side {E : Dag} (eh : StrictLive 14 E) (ec : sem_Comp 14 adj E)
      (bz : Bzero 14 E=0) (bp : Bplus 14 E=11)
      (ee : mask 127=ineligSet 14 E) : False := by
    have bound := side127 eh ec bz ee
    omega
  simp only [elevenMasks,List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact shift 11 11 graphPerm0 auto0 eq (by decide +kernel) Compact.excludeP11
  · exact shift 44 11 graphPerm1 auto1 eq (by decide +kernel) Compact.excludeP11
  · exact shift 47 47 graphPerm0 auto0 eq (by decide +kernel) Compact.excludeP47
  · exact shift 55 55 graphPerm0 auto0 eq (by decide +kernel) reject55
  · exact shift 63 63 graphPerm0 auto0 eq (by decide +kernel) reject63
  · exact shift 95 95 graphPerm0 auto0 eq (by decide +kernel) reject95
  · exact shift 103 103 graphPerm0 auto0 eq (by decide +kernel) reject103
  · exact shift 111 111 graphPerm0 auto0 eq (by decide +kernel) reject111
  · exact shift 119 119 graphPerm0 auto0 eq (by decide +kernel) reject119
  · exact shift 123 123 graphPerm0 auto0 eq (by decide +kernel) reject123
  · exact shift 125 95 graphPerm1 auto1 eq (by decide +kernel) reject95
  · exact shift 126 123 graphPerm1 auto1 eq (by decide +kernel) reject123
  · exact shift 127 127 graphPerm0 auto0 eq (by decide +kernel) side
  · exact shift 164 164 graphPerm0 auto0 eq (by decide +kernel) Compact.excludeP164
  · exact shift 177 177 graphPerm0 auto0 eq (by decide +kernel) Compact.excludeP177
  · exact shift 181 181 graphPerm0 auto0 eq (by decide +kernel) reject181
  · exact shift 197 197 graphPerm0 auto0 eq (by decide +kernel) Compact.excludeP197
  · exact shift 229 229 graphPerm0 auto0 eq (by decide +kernel) reject229
  · exact shift 245 245 graphPerm0 auto0 eq (by decide +kernel) reject245
  · exact shift 266 266 graphPerm0 auto0 eq (by decide +kernel) Compact.excludeP266
  · exact shift 296 266 graphPerm1 auto1 eq (by decide +kernel) Compact.excludeP266
  · exact shift 298 298 graphPerm0 auto0 eq (by decide +kernel) Compact.excludeP298
  · exact shift 400 400 graphPerm0 auto0 eq (by decide +kernel) Compact.excludeP400
  · exact shift 416 416 graphPerm0 auto0 eq (by decide +kernel) Compact.excludeP416
  · exact shift 432 432 graphPerm0 auto0 eq (by decide +kernel) Compact.excludeP432
  · exact shift 521 400 graphPerm2 auto2 eq (by decide +kernel) Compact.excludeP400
  · exact shift 524 400 graphPerm3 auto3 eq (by decide +kernel) Compact.excludeP400
  · exact shift 525 525 graphPerm0 auto0 eq (by decide +kernel) Compact.excludeP525
  · exact shift 645 645 graphPerm0 auto0 eq (by decide +kernel) Compact.excludeP645
  · exact shift 661 661 graphPerm0 auto0 eq (by decide +kernel) reject661
  · exact shift 1034 1034 graphPerm0 auto0 eq (by decide +kernel) Compact.excludeP1034
  · exact shift 1036 416 graphPerm3 auto3 eq (by decide +kernel) Compact.excludeP416
  · exact shift 1038 1038 graphPerm0 auto0 eq (by decide +kernel) Compact.excludeP1038
  · exact shift 1156 164 graphPerm3 auto3 eq (by decide +kernel) Compact.excludeP164
  · exact shift 1216 1216 graphPerm0 auto0 eq (by decide +kernel) Compact.excludeP1216
  · exact shift 1220 1220 graphPerm0 auto0 eq (by decide +kernel) Compact.excludeP1220
  · exact shift 1282 1034 graphPerm2 auto2 eq (by decide +kernel) Compact.excludeP1034
  · exact shift 1288 266 graphPerm2 auto2 eq (by decide +kernel) Compact.excludeP266
  · exact shift 1290 1290 graphPerm0 auto0 eq (by decide +kernel) Compact.excludeP1290
  · exact shift 1408 11 graphPerm2 auto2 eq (by decide +kernel) Compact.excludeP11
  · exact shift 1548 432 graphPerm3 auto3 eq (by decide +kernel) Compact.excludeP432
  · exact shift 2051 1216 graphPerm2 auto2 eq (by decide +kernel) Compact.excludeP1216
  · exact shift 2084 1216 graphPerm3 auto3 eq (by decide +kernel) Compact.excludeP1216
  · exact shift 2087 2087 graphPerm0 auto0 eq (by decide +kernel) Compact.excludeP2087
  · exact shift 2212 1220 graphPerm3 auto3 eq (by decide +kernel) Compact.excludeP1220
  · exact shift 2213 2213 graphPerm0 auto0 eq (by decide +kernel) reject2213
  · exact shift 2693 2693 graphPerm0 auto0 eq (by decide +kernel) reject2693
  · exact shift 4099 164 graphPerm1 auto1 eq (by decide +kernel) Compact.excludeP164
  · exact shift 4118 177 graphPerm1 auto1 eq (by decide +kernel) Compact.excludeP177
  · exact shift 4119 181 graphPerm1 auto1 eq (by decide +kernel) reject181
  · exact shift 4165 197 graphPerm1 auto1 eq (by decide +kernel) Compact.excludeP197
  · exact shift 4167 229 graphPerm1 auto1 eq (by decide +kernel) reject229
  · exact shift 4183 245 graphPerm1 auto1 eq (by decide +kernel) reject245
  · exact shift 4241 645 graphPerm2 auto2 eq (by decide +kernel) Compact.excludeP645
  · exact shift 4244 645 graphPerm3 auto3 eq (by decide +kernel) Compact.excludeP645
  · exact shift 4245 4245 graphPerm0 auto0 eq (by decide +kernel) reject4245
  · exact shift 4293 4293 graphPerm0 auto0 eq (by decide +kernel) residual_exclude4293
  · exact shift 4305 2693 graphPerm2 auto2 eq (by decide +kernel) reject2693
  · exact shift 4308 2693 graphPerm3 auto3 eq (by decide +kernel) reject2693
  · exact shift 4309 4309 graphPerm0 auto0 eq (by decide +kernel) reject4309
  · exact shift 4354 416 graphPerm1 auto1 eq (by decide +kernel) Compact.excludeP416
  · exact shift 4368 400 graphPerm1 auto1 eq (by decide +kernel) Compact.excludeP400
  · exact shift 4370 432 graphPerm1 auto1 eq (by decide +kernel) Compact.excludeP432
  · exact shift 4496 525 graphPerm2 auto2 eq (by decide +kernel) Compact.excludeP525
  · exact shift 4613 645 graphPerm1 auto1 eq (by decide +kernel) Compact.excludeP645
  · exact shift 4629 661 graphPerm1 auto1 eq (by decide +kernel) reject661
  · exact shift 4741 4245 graphPerm2 auto2 eq (by decide +kernel) reject4245
  · exact shift 4753 661 graphPerm2 auto2 eq (by decide +kernel) reject661
  · exact shift 4756 661 graphPerm3 auto3 eq (by decide +kernel) reject661
  · exact shift 4757 4757 graphPerm0 auto0 eq (by decide +kernel) reject4757
  · exact shift 5190 5190 graphPerm0 auto0 eq (by decide +kernel) reject5190
  · exact shift 5316 2213 graphPerm3 auto3 eq (by decide +kernel) reject2213
  · exact shift 5378 1038 graphPerm2 auto2 eq (by decide +kernel) Compact.excludeP1038
  · exact shift 5636 177 graphPerm3 auto3 eq (by decide +kernel) Compact.excludeP177
  · exact shift 5764 181 graphPerm3 auto3 eq (by decide +kernel) reject181
  · exact shift 6147 1220 graphPerm2 auto2 eq (by decide +kernel) Compact.excludeP1220
  · exact shift 6151 2213 graphPerm1 auto1 eq (by decide +kernel) reject2213
  · exact shift 6273 197 graphPerm2 auto2 eq (by decide +kernel) Compact.excludeP197
  · exact shift 6276 197 graphPerm3 auto3 eq (by decide +kernel) Compact.excludeP197
  · exact shift 6277 4293 graphPerm2 auto2 eq (by decide +kernel) residual_exclude4293
  · exact shift 6661 2693 graphPerm1 auto1 eq (by decide +kernel) reject2693
  · exact shift 6789 4309 graphPerm2 auto2 eq (by decide +kernel) reject4309
  · exact shift 7174 5190 graphPerm2 auto2 eq (by decide +kernel) reject5190
  · exact shift 7300 229 graphPerm3 auto3 eq (by decide +kernel) reject229
  · exact shift 7812 245 graphPerm3 auto3 eq (by decide +kernel) reject245
  · exact shift 8064 95 graphPerm2 auto2 eq (by decide +kernel) reject95
  · exact shift 8201 416 graphPerm2 auto2 eq (by decide +kernel) Compact.excludeP416
  · exact shift 8232 1034 graphPerm1 auto1 eq (by decide +kernel) Compact.excludeP1034
  · exact shift 8233 1038 graphPerm1 auto1 eq (by decide +kernel) Compact.excludeP1038
  · exact shift 8417 5190 graphPerm1 auto1 eq (by decide +kernel) reject5190
  · exact shift 8456 266 graphPerm3 auto3 eq (by decide +kernel) Compact.excludeP266
  · exact shift 8480 1034 graphPerm3 auto3 eq (by decide +kernel) Compact.excludeP1034
  · exact shift 8488 1290 graphPerm1 auto1 eq (by decide +kernel) Compact.excludeP1290
  · exact shift 8608 1038 graphPerm3 auto3 eq (by decide +kernel) Compact.excludeP1038
  · exact shift 8713 432 graphPerm2 auto2 eq (by decide +kernel) Compact.excludeP432
  · exact shift 8833 177 graphPerm2 auto2 eq (by decide +kernel) Compact.excludeP177
  · exact shift 9480 298 graphPerm2 auto2 eq (by decide +kernel) Compact.excludeP298
  · exact shift 10401 5190 graphPerm3 auto3 eq (by decide +kernel) reject5190
  · exact shift 12160 123 graphPerm2 auto2 eq (by decide +kernel) reject123
  · exact shift 12289 164 graphPerm2 auto2 eq (by decide +kernel) Compact.excludeP164
  · exact shift 12352 1216 graphPerm1 auto1 eq (by decide +kernel) Compact.excludeP1216
  · exact shift 12353 1220 graphPerm1 auto1 eq (by decide +kernel) Compact.excludeP1220
  · exact shift 12481 2213 graphPerm2 auto2 eq (by decide +kernel) reject2213
  · exact shift 12544 11 graphPerm3 auto3 eq (by decide +kernel) Compact.excludeP11
  · exact shift 12929 181 graphPerm2 auto2 eq (by decide +kernel) reject181
  · exact shift 13504 2087 graphPerm2 auto2 eq (by decide +kernel) Compact.excludeP2087
  · exact shift 13696 47 graphPerm2 auto2 eq (by decide +kernel) Compact.excludeP47
  · exact shift 13952 55 graphPerm2 auto2 eq (by decide +kernel) reject55
  · exact shift 14208 63 graphPerm2 auto2 eq (by decide +kernel) reject63
  · exact shift 14465 229 graphPerm2 auto2 eq (by decide +kernel) reject229
  · exact shift 14977 245 graphPerm2 auto2 eq (by decide +kernel) reject245
  · exact shift 15232 95 graphPerm3 auto3 eq (by decide +kernel) reject95
  · exact shift 15488 103 graphPerm2 auto2 eq (by decide +kernel) reject103
  · exact shift 15744 111 graphPerm2 auto2 eq (by decide +kernel) reject111
  · exact shift 16000 119 graphPerm2 auto2 eq (by decide +kernel) reject119
  · exact shift 16128 123 graphPerm3 auto3 eq (by decide +kernel) reject123
  · exact shift 16256 127 graphPerm2 auto2 eq (by decide +kernel) side

end PEqualNP.Outside.L_meta_9775.UpstreamCore

theorem PEqualNP.Outside.L_meta_9775 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 24 ∧ (∀ x : Fin 14 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 14, (u.val, v.val) ∈ ([(0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true))) := by
  rintro ⟨C, hm, hs, hc⟩
  obtain ⟨D, hd, hsize, hcomp⟩ := PEqualNP.Outside.L_meta_9775.UpstreamCore.normalized C hm hc
  exact PEqualNP.Outside.L_meta_9775.UpstreamCore.smaller_closed hd hcomp (hsize.trans hs)
