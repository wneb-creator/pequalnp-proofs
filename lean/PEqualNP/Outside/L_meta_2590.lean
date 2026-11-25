import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2590_aux

-- Circuit normalization and wire counting, adapted from L_meta_971.
namespace DagTools

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def gop : Bool → Bool → Bool → Bool
  | true, a, b => a && b
  | false, a, b => a || b

@[local simp] lemma gop_true (a b : Bool) : gop true a b = (a && b) := rfl

@[local simp] lemma gop_false (a b : Bool) : gop false a b = (a || b) := rfl

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

lemma tag_eq (D : Dag) (j : ℕ) (h : j < D.length) : tag D j = (D[j]).1 := by
  simp [tag, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

lemma opA_eq (D : Dag) (j : ℕ) (h : j < D.length) : opA D j = (D[j]).2.1 := by
  simp [opA, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

lemma opB_eq (D : Dag) (j : ℕ) (h : j < D.length) : opB D j = (D[j]).2.2 := by
  simp [opB, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

lemma wl_cons (g : Bool × ℕ × ℕ) (D : Dag) (w : List Bool) :
    wl (g :: D) w = wl D (wstep w g) := rfl

lemma wl_append (D E : Dag) (w : List Bool) : wl (D ++ E) w = wl E (wl D w) := by
  simp [wl, List.foldl_append]

lemma wstep_length (w : List Bool) (g : Bool × ℕ × ℕ) : (wstep w g).length = w.length + 1 := by
  simp [wstep]

lemma wl_length (D : Dag) : ∀ w : List Bool, (wl D w).length = w.length + D.length := by
  induction D with
  | nil => intro w; simp [wl]
  | cons g D ih => intro w; rw [wl_cons, ih, wstep_length]; simp; omega

lemma wstep_getD_lt (w : List Bool) (g : Bool × ℕ × ℕ) (i : ℕ) (h : i < w.length) :
    (wstep w g).getD i false = w.getD i false := by
  simp [wstep, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma wl_getD_lt (D : Dag) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wl D w).getD i false = w.getD i false := by
  induction D with
  | nil => intro w i _; rfl
  | cons g D ih =>
    intro w i h
    rw [wl_cons, ih _ _ (by rw [wstep_length]; omega), wstep_getD_lt _ _ _ h]

lemma getD_ge (w : List Bool) (i : ℕ) (h : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

lemma wstep_getD_last (w : List Bool) (g : Bool × ℕ × ℕ) :
    (wstep w g).getD w.length false = gop g.1 (w.getD g.2.1 false) (w.getD g.2.2 false) := by
  simp [wstep, List.getD_eq_getElem?_getD]

lemma wl_getD_gate (D : Dag) (w : List Bool) (j : ℕ) (hj : j < D.length) :
    (wl D w).getD (w.length + j) false =
      gop (tag D j) ((wl (D.take j) w).getD (opA D j) false)
        ((wl (D.take j) w).getD (opB D j) false) := by
  have hsplit : D = D.take j ++ D[j] :: D.drop (j + 1) := by simp
  have hlen : (wl (D.take j) w).length = w.length + j := by
    rw [wl_length, List.length_take]; omega
  rw [tag_eq D j hj, opA_eq D j hj, opB_eq D j hj]
  conv_lhs => rw [hsplit, wl_append, wl_cons]
  rw [wl_getD_lt _ _ _ (by rw [wstep_length, hlen]; omega), ← hlen, wstep_getD_last]

lemma wl_take_getD (D : Dag) (w : List Bool) (j i : ℕ) (hi : i < w.length + j)
    (hj : j ≤ D.length) :
    (wl (D.take j) w).getD i false = (wl D w).getD i false := by
  have hsplit : D = D.take j ++ D.drop j := by simp
  have hlen : (wl (D.take j) w).length = w.length + j := by
    rw [wl_length, List.length_take]; omega
  conv_rhs => rw [hsplit, wl_append]
  rw [wl_getD_lt (D.drop j) (wl (D.take j) w) i (by rw [hlen]; exact hi)]

lemma val_input (D : Dag) {n : ℕ} (x : Fin n → Bool) (i : ℕ) (h : i < n) :
    val D x i = x ⟨i, h⟩ := by
  unfold val
  rw [wl_getD_lt _ _ _ (by simpa using h)]
  simp [List.getD_eq_getElem?_getD, h]

lemma val_ge (D : Dag) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (h : n + D.length ≤ w) :
    val D x w = false := by
  unfold val
  exact getD_ge _ _ (by rw [wl_length]; simpa using h)

lemma val_take (D : Dag) {n : ℕ} (x : Fin n → Bool) (k w : ℕ) (hw : w < n + k)
    (hk : k ≤ D.length) : val (D.take k) x w = val D x w := by
  unfold val
  exact wl_take_getD D _ k w (by simpa using hw) hk

lemma val_gate {n : ℕ} {D : Dag} (hS : Strict n D) (x : Fin n → Bool) (j : ℕ)
    (hj : j < D.length) :
    val D x (n + j) = gop (tag D j) (val D x (opA D j)) (val D x (opB D j)) := by
  obtain ⟨ha, hb, -⟩ := hS j hj
  have h := wl_getD_gate D (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  unfold val
  rw [h, wl_take_getD D _ j _ (by simpa using ha) hj.le,
    wl_take_getD D _ j _ (by simpa using hb) hj.le]

lemma val_unique {n : ℕ} {D : Dag} (hS : Strict n D) (x : Fin n → Bool) (f : ℕ → Bool)
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

lemma na_ok_mono {B B' : ℕ} (h : B ≤ B') (r : Ref) (hr : na_ok B r) : na_ok B' r := by
  rcases r with b | k
  · trivial
  · exact lt_of_lt_of_le hr h

lemma na_look_val (W : List Bool) (m : List Ref) (i : ℕ) :
    refVal W (na_look m i) = (m.map (refVal W)).getD i false := by
  simp only [na_look, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases m[i]? <;> rfl

lemma na_look_ok (B : ℕ) (m : List Ref) (hm : ∀ r ∈ m, na_ok B r) (i : ℕ) :
    na_ok B (na_look m i) := by
  simp only [na_look, List.getD_eq_getElem?_getD]
  rcases h : m[i]? with _ | r
  · trivial
  · exact hm r (List.mem_of_getElem? h)

lemma na_refVal_wstep (W : List Bool) (g : Bool × ℕ × ℕ) (r : Ref) (hr : na_ok W.length r) :
    refVal (wstep W g) r = refVal W r := by
  rcases r with b | k
  · rfl
  · exact wstep_getD_lt W g k hr

lemma na_comb_inl (t : Bool) (W : List Bool) (a b r : Ref) (h : na_comb t a b = Sum.inl r) :
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

lemma na_comb_ok (B : ℕ) (t : Bool) (a b r : Ref) (ha : na_ok B a) (hb : na_ok B b)
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

lemma na_comb_inr (t : Bool) (a b : Ref) (p : ℕ × ℕ) (h : na_comb t a b = Sum.inr p) :
    a = Sum.inr p.1 ∧ b = Sum.inr p.2 ∧ p.1 ≠ p.2 := by
  rcases a with a | i
  · simp [na_comb] at h
  · rcases b with b | j
    · simp [na_comb] at h
    · simp only [na_comb] at h
      split_ifs at h with hij
      cases h
      exact ⟨rfl, rfl, hij⟩

lemma na_eval0 (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
    op.eval [] = na_isAnd op := by
  rcases hop with rfl | rfl <;> rfl

lemma na_eval1 (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (u : Bool) :
    op.eval [u] = u := by
  rcases hop with rfl | rfl <;> simp [GateOp.eval]

lemma na_eval2 (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (u v : Bool) : op.eval [u, v] = gop (na_isAnd op) u v := by
  rcases hop with rfl | rfl <;> simp [GateOp.eval, na_isAnd]

lemma na_getD_append_lt (D E : Dag) (k : ℕ) (h : k < D.length) :
    (D ++ E).getD k (false, 0, 0) = D.getD k (false, 0, 0) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma na_getD_snoc (D : Dag) (g : Bool × ℕ × ℕ) :
    (D ++ [g]).getD D.length (false, 0, 0) = g := by
  simp [List.getD_eq_getElem?_getD]

lemma na_strict_snoc {n : ℕ} {D : Dag} (hS : Strict n D) (t : Bool) (i j : ℕ)
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

lemma na_strict_take {n : ℕ} {D : Dag} (hS : Strict n D) (k : ℕ) : Strict n (D.take k) := by
  intro j hj
  simp only [List.length_take] at hj
  have hj1 : j < k := by omega
  have hj2 : j < D.length := by omega
  have e : (D.take k).getD j (false, 0, 0) = D.getD j (false, 0, 0) := by
    simp [List.getD_eq_getElem?_getD, hj1]
  simp only [opA, opB, e]
  exact hS j hj2

lemma na_step_spec (n : ℕ) (st : List Ref × Dag) (g : Gate)
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

lemma na_fold_spec (n : ℕ) (gs : List Gate)
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

lemma na_init (n : ℕ) (x : Fin n → Bool) :
    ((List.range n).map Sum.inr).map (refVal (wl ([] : Dag) (List.ofFn x))) = List.ofFn x := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp [refVal, wl, List.getD_eq_getElem?_getD, h1]

lemma exists_strict_of_monotone2 {n : ℕ} (C : Circuit) (hmono : Monotone2 C) :
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

lemma na_no_reader {D : Dag} {w : ℕ} (h : fanout D w = 0) (j : ℕ) (hj : j < D.length) :
    opA D j ≠ w ∧ opB D j ≠ w := by
  unfold fanout readers at h
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
  have := h (Finset.mem_range.mpr hj)
  tauto

def na_sh (c a : ℕ) : ℕ := if c < a then a - 1 else a

def na_up (c w : ℕ) : ℕ := if w < c then w else w + 1

def na_del (n j : ℕ) (D : Dag) : Dag :=
  (D.eraseIdx j).map (fun g => (g.1, na_sh (n + j) g.2.1, na_sh (n + j) g.2.2))

lemma na_del_length (n j : ℕ) (D : Dag) (hj : j < D.length) :
    (na_del n j D).length = D.length - 1 := by
  simp [na_del, List.length_eraseIdx, hj]

lemma na_del_ops (n j : ℕ) (D : Dag) (k : ℕ) (hk : na_up j k < D.length) :
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

lemma na_del_strict {n : ℕ} {D : Dag} (hS : Strict n D) (j : ℕ) (hj : j < D.length)
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

lemma na_del_val {n : ℕ} {D : Dag} (hS : Strict n D) (j : ℕ) (hj : j < D.length)
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

lemma na_live_aux {n : ℕ} (F : (Fin n → Bool) → Bool)
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

lemma exists_strictLive_of_strict {n : ℕ} (F : (Fin n → Bool) → Bool)
    (hess : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ k, k ≠ i → x k = y k) ∧ F x ≠ F y)
    (D : Dag) (hS : Strict n D) (hne : D ≠ [])
    (hD : ∀ x : Fin n → Bool, val D x (outW n D) = F x) :
    ∃ D' : Dag, StrictLive n D' ∧ D'.length ≤ D.length ∧
      ∀ x : Fin n → Bool, val D' x (outW n D') = F x :=
  na_live_aux F hess D.length D rfl hS hne hD

lemma normalize_strictLive {n : ℕ} (C : Circuit) (hmono : Monotone2 C)
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

lemma sb_mem_inner {w : ℕ} : w ∈ inner n D ↔ w + 1 < n + D.length := by
  unfold inner; rw [Finset.mem_range]; omega

lemma sb_src_false (j : ℕ) : src D (j, false) = opA D j := by simp [src]

lemma sb_src_true (j : ℕ) : src D (j, true) = opB D j := by simp [src]

lemma fanout_eq_zero_of_ge (hS : Strict n D) (w : ℕ) (h : n + D.length ≤ w + 1) :
    fanout D w = 0 := by
  unfold fanout readers
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro j hj
  have hj2 := Finset.mem_range.mp hj
  have := hS j hj2
  omega

lemma lt_of_fanout_pos (hS : Strict n D) {w : ℕ} (h : 1 ≤ fanout D w) :
    w + 1 < n + D.length := by
  by_contra hc
  have := fanout_eq_zero_of_ge hS w (by omega)
  omega

lemma sb_card_arcs_filter (P : ℕ × Bool → Prop) [DecidablePred P] :
    ((arcs D).filter P).card = ∑ j ∈ Finset.range D.length,
      ((if P (j, false) then 1 else 0) + (if P (j, true) then 1 else 0)) := by
  rw [Finset.card_filter, arcs, Finset.sum_product]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Fintype.sum_bool, add_comm]

lemma sb_card_arcs : (arcs D).card = 2 * D.length := by
  simp [arcs, Finset.card_product, Nat.mul_comm]

lemma sb_src_lt (hS : Strict n D) (e : ℕ × Bool) (he : e ∈ arcs D) :
    src D e + 1 < n + D.length := by
  obtain ⟨j, c⟩ := e
  have hj : j < D.length := by simpa [arcs] using he
  have := hS j hj
  cases c
  · rw [sb_src_false]; omega
  · rw [sb_src_true]; omega

lemma sb_fanout_arcs (hS : Strict n D) (w : ℕ) :
    fanout D w = ((arcs D).filter (fun e => src D e = w)).card := by
  rw [sb_card_arcs_filter, fanout, readers, Finset.card_filter]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have := (hS j (Finset.mem_range.mp hj)).2.2
  rw [sb_src_false, sb_src_true]
  split_ifs <;> omega

lemma sb_sum_fanout_eq (hS : Strict n D) (K : Finset ℕ) :
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

lemma sb_surplus_add_card {K : Finset ℕ} (hL : ∀ w ∈ K, 1 ≤ fanout D w) :
    surplusOn D K + K.card = ∑ w ∈ K, fanout D w := by
  rw [surplusOn, Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun w hw => Nat.sub_add_cancel (hL w hw))

lemma surplus_identity (h : StrictLive n D) : totalSurplus n D + n = D.length + 1 := by
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

lemma totalSurplus_split (n : ℕ) (D : Dag) : totalSurplus n D = Bplus n D + Bzero n D := by
  unfold totalSurplus Bplus Bzero surplusOn
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

lemma live_reaches_out (h : StrictLive n D) (w : ℕ) (hw : w < n + D.length) :
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

lemma mem_supp {v : Fin n} {w : ℕ} : v ∈ supp n D w ↔ val D (single v) w = true := by
  simp [supp]

lemma val_mono (hS : Strict n D) (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true)
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

lemma supp_input (D : Dag) (i : Fin n) : supp n D i.val = {i} := by
  ext v
  rw [mem_supp, val_input D (single v) i.val i.isLt]
  simp [single, eq_comm]

lemma supp_ge (D : Dag) (w : ℕ) (h : n + D.length ≤ w) : supp n D w = ∅ := by
  ext v
  simp [mem_supp, val_ge D (single v) w h]

lemma supp_gate (hS : Strict n D) (j : ℕ) (hj : j < D.length) :
    supp n D (n + j) = if tag D j = true then supp n D (opA D j) ∩ supp n D (opB D j)
      else supp n D (opA D j) ∪ supp n D (opB D j) := by
  ext v
  rw [mem_supp, val_gate hS _ j hj]
  cases tag D j <;> simp [mem_supp]

lemma carrier_flow (h : StrictLive n D) (K : Finset ℕ) (hK : K ⊆ inner n D)
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

lemma sb_carrierT_sub (T : Finset (Fin n))
    (hout : supp n D (outW n D) ∩ T = ∅) : carrierT n D T ⊆ inner n D := by
  intro w hw
  simp only [carrierT, Finset.mem_filter, Finset.mem_range] at hw
  rw [sb_mem_inner]
  by_contra hc
  have hw2 : w = outW n D := by unfold outW; omega
  rw [hw2, hout] at hw
  exact Finset.not_nonempty_empty hw.2

lemma sb_sources_carrierT (D : Dag) (T : Finset (Fin n)) :
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

lemma carrier_flow_union (h : StrictLive n D) (T : Finset (Fin n))
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

lemma mem_units {u : Σ _ : ℕ, ℕ} :
    u ∈ units n D ↔ u.1 ∈ inner n D ∧ u.2 + 1 < fanout D u.1 := by
  rw [units, Finset.mem_sigma, Finset.mem_range]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩

lemma sb_card_units_filter (n : ℕ) (D : Dag) (p : ℕ → Prop) [DecidablePred p] :
    ((units n D).filter (fun u => p u.1)).card = surplusOn D ((inner n D).filter p) := by
  have hs : (units n D).filter (fun u => p u.1) =
      ((inner n D).filter p).sigma (fun w => Finset.range (fanout D w - 1)) := by
    ext u; simp only [units, Finset.mem_filter, Finset.mem_sigma]; tauto
  rw [hs, Finset.card_sigma, surplusOn]
  simp

lemma card_unitsPlus (n : ℕ) (D : Dag) : (unitsPlus n D).card = Bplus n D := by
  unfold unitsPlus Bplus
  exact sb_card_units_filter n D (fun w => (supp n D w).Nonempty)

lemma mem_eligSet {v : Fin n} :
    v ∈ eligSet n D ↔ ∃ w, 2 ≤ fanout D w ∧ v ∈ supp n D w := by
  simp only [eligSet, branchW, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨w, ⟨-, h2⟩, hv⟩; exact ⟨w, h2, hv⟩
  · rintro ⟨w, h2, hv⟩
    refine ⟨w, ⟨?_, h2⟩, hv⟩
    by_contra hc
    rw [supp_ge D w (by omega)] at hv
    exact Finset.notMem_empty v hv

lemma mem_ineligSet {v : Fin n} :
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

lemma sb_singleton_inter_nonempty {v : Fin n} {T : Finset (Fin n)} :
    (({v} : Finset (Fin n)) ∩ T).Nonempty ↔ v ∈ T := by
  constructor
  · rintro ⟨u, hu⟩
    rw [Finset.mem_inter, Finset.mem_singleton] at hu
    exact hu.1 ▸ hu.2
  · intro h
    exact ⟨v, Finset.mem_inter.mpr ⟨Finset.mem_singleton_self v, h⟩⟩

lemma sb_reserved_inj (b : Fin n → ℕ) (hb : PureBranch n D b) :
    Set.InjOn (fun v => (⟨b v, 0⟩ : Σ _ : ℕ, ℕ)) (eligSet n D : Set (Fin n)) := by
  intro v hv v2 hv2 he
  have hbv : b v = b v2 := congrArg Sigma.fst he
  have h1 := (hb v hv).2
  rw [hbv, (hb v2 hv2).2] at h1
  exact (Finset.singleton_injective h1).symm

lemma reserved_subset (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b) :
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

lemma card_reserved (b : Fin n → ℕ) (hb : PureBranch n D b) :
    (reservedUnits n D b).card = (eligSet n D).card :=
  Finset.card_image_of_injOn (sb_reserved_inj b hb)

lemma elig_le_Bplus (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b) :
    (eligSet n D).card ≤ Bplus n D := by
  rw [← card_reserved b hb, ← card_unitsPlus]
  exact Finset.card_le_card (reserved_subset hS b hb)

lemma card_residual (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b) :
    (residualUnits n D b).card + (eligSet n D).card = Bplus n D := by
  rw [← card_reserved b hb, ← card_unitsPlus]
  exact Finset.card_sdiff_add_card_eq_card (reserved_subset hS b hb)

lemma surplus_carrierT_eq (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b)
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

lemma surplus_carrierT_le (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b)
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

lemma tr_liftP_lt {n : ℕ} (σ : Equiv.Perm (Fin n)) {w : ℕ} (h : w < n) :
    liftP σ w = (σ ⟨w, h⟩).val := by
  simp [liftP, h]

lemma tr_liftP_ge {n : ℕ} (σ : Equiv.Perm (Fin n)) {w : ℕ} (h : n ≤ w) : liftP σ w = w := by
  simp [liftP, Nat.not_lt.mpr h]

lemma tr_liftP_lt_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) {m : ℕ} (hm : n ≤ m) (w : ℕ) :
    liftP σ w < m ↔ w < m := by
  by_cases h : w < n
  · rw [tr_liftP_lt σ h]
    have := (σ ⟨w, h⟩).isLt
    constructor <;> intro <;> omega
  · rw [tr_liftP_ge σ (Nat.not_lt.mp h)]

lemma liftP_inv {n : ℕ} (σ : Equiv.Perm (Fin n)) (w : ℕ) : liftP σ⁻¹ (liftP σ w) = w := by
  by_cases h : w < n
  · rw [tr_liftP_lt σ h, tr_liftP_lt σ⁻¹ (σ ⟨w, h⟩).isLt]; simp
  · rw [tr_liftP_ge σ (Nat.not_lt.mp h), tr_liftP_ge σ⁻¹ (Nat.not_lt.mp h)]

lemma tr_liftP_inv' {n : ℕ} (σ : Equiv.Perm (Fin n)) (w : ℕ) : liftP σ (liftP σ⁻¹ w) = w := by
  simpa using liftP_inv σ⁻¹ w

lemma tr_liftP_inj {n : ℕ} (σ : Equiv.Perm (Fin n)) {a b : ℕ} :
    liftP σ a = liftP σ b ↔ a = b := by
  refine ⟨fun h => ?_, congrArg _⟩
  have := congrArg (liftP σ⁻¹) h
  rwa [liftP_inv, liftP_inv] at this

lemma relabel_length {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) :
    (relabel σ D).length = D.length := by
  simp [relabel]

lemma tr_tag {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (j : ℕ) (hj : j < D.length) :
    tag (relabel σ D) j = tag D j := by
  rw [tag_eq _ j (by rw [relabel_length]; exact hj), tag_eq D j hj]; simp [relabel]

lemma tr_opA {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (j : ℕ) (hj : j < D.length) :
    opA (relabel σ D) j = liftP σ (opA D j) := by
  rw [opA_eq _ j (by rw [relabel_length]; exact hj), opA_eq D j hj]; simp [relabel]

lemma tr_opB {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (j : ℕ) (hj : j < D.length) :
    opB (relabel σ D) j = liftP σ (opB D j) := by
  rw [opB_eq _ j (by rw [relabel_length]; exact hj), opB_eq D j hj]; simp [relabel]

lemma relabel_strict {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) :
    Strict n (relabel σ D) := by
  intro j hj
  rw [relabel_length] at hj
  obtain ⟨ha, hb, hab⟩ := hS j hj
  rw [tr_opA σ D j hj, tr_opB σ D j hj]
  exact ⟨(tr_liftP_lt_iff σ (Nat.le_add_right n j) _).mpr ha,
    (tr_liftP_lt_iff σ (Nat.le_add_right n j) _).mpr hb, fun h => hab ((tr_liftP_inj σ).mp h)⟩

lemma relabel_val {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D)
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

lemma relabel_fanout {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (w : ℕ) :
    fanout (relabel σ D) (liftP σ w) = fanout D w := by
  unfold fanout readers
  rw [relabel_length]
  congr 1
  apply Finset.filter_congr
  intro j hj
  have hj' := Finset.mem_range.mp hj
  rw [tr_opA σ D j hj', tr_opB σ D j hj', tr_liftP_inj, tr_liftP_inj]

lemma relabel_live {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hL : Live n D) :
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

lemma relabel_strictLive {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (h : StrictLive n D) :
    StrictLive n (relabel σ D) :=
  ⟨relabel_strict σ h.1, relabel_live σ h.2.1, by simpa [relabel] using h.2.2⟩

lemma relabel_out {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) (hne : D ≠ [])
    (x : Fin n → Bool) :
    val (relabel σ D) x (outW n (relabel σ D)) = val D (fun i => x (σ i)) (outW n D) := by
  have hpos := List.length_pos_iff.mpr hne
  have e : outW n (relabel σ D) = liftP σ (outW n D) := by
    rw [tr_liftP_ge σ (by unfold outW; omega)]; simp [outW, relabel_length]
  rw [e, relabel_val σ hS]

lemma tr_single_comp {n : ℕ} (σ : Equiv.Perm (Fin n)) (v : Fin n) :
    (fun i => single v (σ i)) = single (σ⁻¹ v) := by
  funext i
  simp only [single, decide_eq_decide]
  constructor
  · intro h; rw [← h]; simp
  · intro h; rw [h]; simp

lemma relabel_supp {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) (w : ℕ) :
    supp n (relabel σ D) (liftP σ w) = (supp n D w).image σ := by
  ext v
  simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  rw [relabel_val σ hS, tr_single_comp]
  constructor
  · intro h; exact ⟨σ⁻¹ v, h, by simp⟩
  · rintro ⟨a, ha, rfl⟩; simpa using ha

lemma relabel_eligSet {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) :
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

lemma relabel_ineligSet {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) :
    ineligSet n (relabel σ D) = (ineligSet n D).image σ := by
  ext v
  simp only [ineligSet, relabel_eligSet σ hS, Finset.mem_sdiff, Finset.mem_univ, true_and,
    Finset.mem_image]
  constructor
  · intro h
    exact ⟨σ⁻¹ v, fun hm => h ⟨σ⁻¹ v, hm, by simp⟩, by simp⟩
  · rintro ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    exact ha (σ.injective hab ▸ hb)

lemma inelig_card_add (n : ℕ) (D : Dag) : (ineligSet n D).card + (eligSet n D).card = n := by
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

lemma sem_rtg_mono {α : Type} {r p : α → α → Prop} (h : ∀ a b, r a b → p a b) {a b : α}
    (hab : Relation.ReflTransGen r a b) : Relation.ReflTransGen p a b := by
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.tail ih (h _ _ hbc)

section SemCore

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

lemma sem_ins_agree (v : Fin n) (x : Fin n → Bool) : ∀ k, k ≠ v → x k = sem_ins v x k := by
  intro k hk; simp [sem_ins, hk]

lemma sem_ins_self (v : Fin n) (x : Fin n → Bool) : sem_ins v x v = true := by simp [sem_ins]

lemma sem_ins_ge (v : Fin n) (x : Fin n → Bool) : ∀ i, x i = true → sem_ins v x i = true := by
  intro i hi; simp [sem_ins, hi]

lemma sem_single_le {x : Fin n → Bool} {u : Fin n} (hu : x u = true) :
    ∀ i, single u i = true → x i = true := by
  intro i hi
  simp only [single, decide_eq_true_eq] at hi
  rw [hi]; exact hu

lemma sem_val_of_supp (hS : Strict n D) {u : Fin n} {w : ℕ} (hu : u ∈ supp n D w)
    {x : Fin n → Bool} (hx : x u = true) : val D x w = true :=
  val_mono hS (single u) x (sem_single_le hx) w (mem_supp.mp hu)

lemma sem_supp_lt {v : Fin n} {w : ℕ} (hv : v ∈ supp n D w) : w < n + D.length := by
  by_contra hc
  rw [supp_ge D w (by omega)] at hv
  exact Finset.notMem_empty v hv

lemma sem_supp_and (hS : Strict n D) {j : ℕ} (hj : j < D.length) (ht : tag D j = true) :
    supp n D (n + j) = supp n D (opA D j) ∩ supp n D (opB D j) := by
  rw [supp_gate hS j hj]; simp [ht]

lemma sem_supp_or (hS : Strict n D) {j : ℕ} (hj : j < D.length) (ht : tag D j = false) :
    supp n D (n + j) = supp n D (opA D j) ∪ supp n D (opB D j) := by
  rw [supp_gate hS j hj]; simp [ht]

lemma sem_supp_and_sub (hS : Strict n D) {j : ℕ} (hj : j < D.length) (ht : tag D j = true)
    (s : Bool) : supp n D (n + j) ⊆ supp n D (src D (j, s)) := by
  rw [sem_supp_and hS hj ht]
  cases s
  · rw [sb_src_false]; exact Finset.inter_subset_left
  · rw [sb_src_true]; exact Finset.inter_subset_right

lemma sem_src_lt (hS : Strict n D) {j : ℕ} (hj : j < D.length) (s : Bool) :
    src D (j, s) < n + j := by
  obtain ⟨ha, hb, -⟩ := hS j hj
  cases s
  · rw [sb_src_false]; exact ha
  · rw [sb_src_true]; exact hb

lemma sem_src_ne (hS : Strict n D) {j : ℕ} (hj : j < D.length) (s : Bool) :
    src D (j, s) ≠ src D (j, !s) := by
  obtain ⟨-, -, hne⟩ := hS j hj
  cases s
  · simpa [src] using hne
  · simpa [src] using hne.symm

lemma sem_step_src {j : ℕ} (hj : j < D.length) (s : Bool) :
    sem_step n D (src D (j, s)) (n + j) := by
  refine ⟨by omega, by omega, ?_⟩
  rw [Nat.add_sub_cancel_left]
  cases s
  · exact Or.inl (sb_src_false j).symm
  · exact Or.inr (sb_src_true j).symm

lemma sem_step_iff {a b : ℕ} : sem_step n D a b ↔
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

lemma sem_step_lt (hS : Strict n D) {a b : ℕ} (h : sem_step n D a b) : a < b := by
  obtain ⟨h1, h2, h3⟩ := h
  have := hS (b - n) (by omega)
  omega

lemma sem_step_reader {a c : ℕ} (h : sem_step n D a c) : c - n ∈ readers D a := by
  unfold readers
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨by have := h.1; have := h.2.1; omega, h.2.2⟩

lemma sem_step_fanout {a c : ℕ} (h : sem_step n D a c) : 1 ≤ fanout D a :=
  Finset.card_pos.mpr ⟨_, sem_step_reader h⟩

lemma sem_step_unique {a c c' : ℕ} (h1 : sem_step n D a c) (h2 : sem_step n D a c')
    (hf : fanout D a = 1) : c = c' := by
  have m1 := sem_step_reader h1
  have m2 := sem_step_reader h2
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp (show (readers D a).card = 1 from hf)
  rw [hr, Finset.mem_singleton] at m1 m2
  have := h1.2.1
  have := h2.2.1
  omega

lemma sem_changed_path (hS : Strict n D) (x y : Fin n → Bool) (v : Fin n)
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

lemma sem_dom_eq (hS : Strict n D) (x y : Fin n → Bool) (v : Fin n)
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

lemma sem_chain_dom (hS : Strict n D) {v b : ℕ} (h : sem_Chain n D v b) :
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

lemma sem_carrier_chain (hS : Strict n D) (v : Fin n) : ∀ w, v ∈ supp n D w →
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

lemma sem_single_no_edge (hG : sem_Gr G) (v : Fin n) : ¬ sem_Edge G (single v) := by
  rintro ⟨a, c, hac, ha, hc⟩
  simp only [single, decide_eq_true_eq] at ha hc
  rw [ha, hc] at hac
  exact hG.2.1 _ hac

lemma sem_two_edge {u v : Fin n} (huv : G u v) : sem_Edge G (sem_two u v) :=
  ⟨u, v, huv, by simp [sem_two], by simp [sem_two]⟩

lemma sem_supp_out (hG : sem_Gr G) (hC : sem_Comp n G D) : supp n D (outW n D) = ∅ :=
  Finset.eq_empty_iff_forall_notMem.2
    (fun v hv => sem_single_no_edge hG v ((hC _).1 (mem_supp.1 hv)))

lemma sem_dom_pure (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) (v : Fin n)
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

lemma sem_first_branch (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) (v : Fin n)
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

lemma sem_exists_firstBranch (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) :
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

lemma sem_firstBranch_pure {b : Fin n → ℕ} (hb : sem_FirstBranch n D b) : PureBranch n D b :=
  fun v hv => ⟨(hb v hv).1, (hb v hv).2.1⟩

lemma sem_exists_pureBranch (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) :
    ∃ b : Fin n → ℕ, PureBranch n D b := by
  obtain ⟨b, hb⟩ := sem_exists_firstBranch hG hS hC
  exact ⟨b, sem_firstBranch_pure hb⟩

lemma sem_mem_inelig {v : Fin n} : v ∈ ineligSet n D ↔ v ∉ eligSet n D := by
  simp [ineligSet]

lemma sem_inelig_chain (hS : Strict n D) {v : Fin n} (hv : v ∈ ineligSet n D) {w : ℕ}
    (hw : v ∈ supp n D w) : sem_Chain n D v.val w :=
  sem_carrier_chain hS v w hw (fun u _ hu => mem_ineligSet.mp hv u hu)

lemma sem_inelig_pure (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) {v : Fin n}
    (hv : v ∈ ineligSet n D) {w : ℕ} (hw : v ∈ supp n D w) : supp n D w = {v} :=
  Finset.Subset.antisymm (sem_dom_pure hG hS hC v w (sem_chain_dom hS (sem_inelig_chain hS hv hw)))
    (Finset.singleton_subset_iff.mpr hw)

lemma sem_mem_carrier1 {v : Fin n} {w : ℕ} : w ∈ carrierT n D {v} ↔ v ∈ supp n D w := by
  simp only [carrierT, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨-, u, hu⟩
    rw [Finset.mem_inter, Finset.mem_singleton] at hu
    exact hu.2 ▸ hu.1
  · intro h
    exact ⟨sem_supp_lt h, v, Finset.mem_inter.mpr ⟨h, Finset.mem_singleton_self v⟩⟩

lemma sem_mem_exit1 {v : Fin n} {e : ℕ × Bool} : e ∈ exitArcs n D (carrierT n D {v}) ↔
    e.1 < D.length ∧ v ∈ supp n D (src D e) ∧ v ∉ supp n D (n + e.1) := by
  simp only [exitArcs, arcs, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    Finset.mem_univ, and_true, sem_mem_carrier1]

lemma sem_inelig_surplus {v : Fin n} (hv : v ∈ ineligSet n D) :
    surplusOn D (carrierT n D {v}) = 0 := by
  unfold surplusOn
  refine Finset.sum_eq_zero (fun w hw => ?_)
  have := mem_ineligSet.mp hv w (sem_mem_carrier1.mp hw)
  omega

lemma sem_joint_meeting (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
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

lemma sem_inelig_consumer (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
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

lemma sem_elig_cover (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
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

lemma sem_ind_no_edge {A : Finset (Fin n)} (hA : ∀ a ∈ A, ∀ b ∈ A, ¬ G a b) :
    ¬ sem_Edge G (sem_ind A) := by
  rintro ⟨a, c, hac, ha, hc⟩
  simp only [sem_ind, decide_eq_true_eq] at ha hc
  exact hA a ha c hc hac

lemma sem_exposure (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
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

lemma sem_first_mask (hS : Strict n D) (T M : Finset (Fin n)) (hM : 2 ≤ M.card) (w : ℕ)
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

lemma sem_mem_W {x : Fin n} {e : ℕ × Bool} : e ∈ sem_W n D x ↔
    e.1 < D.length ∧ x ∈ supp n D (src D e) ∧ x ∉ supp n D (n + e.1) := sem_mem_exit1

lemma sem_bar_bar (e : ℕ × Bool) : sem_bar (sem_bar e) = e := by simp [sem_bar]

lemma sem_bar_ne (e : ℕ × Bool) : sem_bar e ≠ e := by
  intro h
  have h2 := congrArg Prod.snd h
  simp [sem_bar] at h2

lemma sem_same_gate {e f : ℕ × Bool} (h : e.1 = f.1) : f = e ∨ f = sem_bar e := by
  obtain ⟨j, s⟩ := e
  obtain ⟨k, t⟩ := f
  simp only at h
  subst h
  cases s <;> cases t <;> simp [sem_bar]

lemma sem_W_and (hS : Strict n D) {x : Fin n} {e : ℕ × Bool} (he : e ∈ sem_W n D x) :
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

lemma sem_flow1 (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D) (x : Fin n) :
    (sem_W n D x).card + (merges n D (carrierT n D {x})).card =
      1 + surplusOn D (carrierT n D {x}) := by
  have h1 := carrier_flow_union h {x} (by rw [sem_supp_out hG hC]; simp)
  rwa [Finset.card_singleton] at h1

lemma sem_edge_slots (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) {x y : Fin n}
    (hxy : G x y) : ∃ e, e ∈ sem_W n D x ∧ sem_bar e ∈ sem_W n D y ∧
      y ∉ supp n D (src D e) ∧ x ∉ supp n D (src D (sem_bar e)) ∧
      val D (sem_two x y) (n + e.1) = true := by
  obtain ⟨j, hj, -, hval, hju, hjv, s, h1, h2, h3, h4⟩ := sem_joint_meeting hG hS hC hxy
  exact ⟨(j, s), sem_mem_W.mpr ⟨hj, h1, hju⟩, sem_mem_W.mpr ⟨hj, h3, hjv⟩, h2, h4, hval⟩

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

end SemCodes

lemma sem_rtg_comparable {α : Type} {R : α → α → Prop}
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

lemma sem_rtg_le (hS : Strict n D) {R : ℕ → ℕ → Prop} (hR : ∀ a b, R a b → sem_step n D a b)
    {a b : ℕ} (h : Relation.ReflTransGen R a b) : a ≤ b := by
  induction h with
  | refl => exact le_refl _
  | tail _ hbc ih => exact le_trans ih (le_of_lt (sem_step_lt hS (hR _ _ hbc)))

lemma sem_exists_minBranch (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) :
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

lemma sem_minBranch_pure {b : Fin n → ℕ} (hb : sem_MinBranch n D b) : PureBranch n D b :=
  fun v hv => ⟨(hb v hv).1, (hb v hv).2.1⟩

lemma sem_zm_gate (hS : Strict n D) {x : Fin n} (hM : merges n D (carrierT n D {x}) = ∅)
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

lemma sem_code_count (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
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

lemma sem_descent (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
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

lemma sem_two_arms (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
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

lemma sem_saturated (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
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

lemma sem_common_terminals (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
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

lemma sem_ind_single (a : Fin n) : sem_ind ({a} : Finset (Fin n)) = single a := by
  funext k; simp [sem_ind, single]

lemma sem_val_gate_src (hS : Strict n D) (x : Fin n → Bool) {j : ℕ} (hj : j < D.length)
    (s : Bool) : val D x (n + j) =
      gop (tag D j) (val D x (src D (j, s))) (val D x (src D (j, !s))) := by
  rw [val_gate hS x j hj]
  cases s
  · simp [src]
  · cases tag D j <;> simp [src, Bool.and_comm, Bool.or_comm]

lemma sem_ins_ind_edge (hG : sem_Gr G) {i : Fin n} {S : Finset (Fin n)}
    (h : sem_Edge G (sem_ins i (sem_ind S))) :
    (∃ a ∈ S, G i a) ∨ ∃ a ∈ S, ∃ b ∈ S, G a b := by
  obtain ⟨u, v, huv, hu, hv⟩ := h
  simp only [sem_ins, sem_ind, Bool.or_eq_true, decide_eq_true_eq] at hu hv
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · rw [hu, hv] at huv; exact absurd huv (hG.2.1 i)
  · rw [hu] at huv; exact Or.inl ⟨v, hv, huv⟩
  · rw [hv] at huv; exact Or.inl ⟨u, hu, hG.1 _ _ huv⟩
  · exact Or.inr ⟨u, hu, v, hv, huv⟩

lemma sem_chain_dom_at (hS : Strict n D) {v b t : ℕ} (h : sem_Chain n D v b) (hbt : b ≤ t) :
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

lemma sem_dom_eq_at (hS : Strict n D) (x y : Fin n → Bool) (v : Fin n)
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

lemma sem_chain_fork (hS : Strict n D) {a c q : ℕ} (hc : sem_Chain n D a c)
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

lemma sem_sibling_indep (hS : Strict n D) (v : Fin n) {j : ℕ} (hj : j < D.length) (s : Bool)
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

lemma sem_dom_split (hS : Strict n D) (hC : sem_Comp n G D) (x : Fin n → Bool) (v : Fin n)
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

lemma sem_factor (hS : Strict n D) (i : Fin n) (w : ℕ) (hch : sem_Chain n D i.val w)
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

lemma sem_exact_at (hS : Strict n D) (i : Fin n) (w : ℕ) (hch : sem_Chain n D i.val w)
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

lemma sem_branch_empty (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) {i : Fin n}
    (hi : i ∈ ineligSet n D) {b : ℕ} (hch : sem_Chain n D i.val b) (hf : 2 ≤ fanout D b) :
    supp n D b = ∅ := by
  have hsub := sem_dom_pure hG hS hC i b (sem_chain_dom hS hch)
  refine Finset.eq_empty_of_forall_notMem (fun x hx => ?_)
  have h1 := hsub hx
  rw [Finset.mem_singleton] at h1
  have h2 := mem_ineligSet.mp hi b (h1 ▸ hx)
  omega

lemma sem_path_chain {a t : ℕ} (hp : Relation.ReflTransGen (sem_step n D) a t) :
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

lemma sem_inelig_reach (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    {i : Fin n} (hi : i ∈ ineligSet n D) :
    sem_Chain n D i.val (outW n D) ∨
      ∃ b, sem_Chain n D i.val b ∧ 2 ≤ fanout D b ∧ supp n D b = ∅ := by
  have hlt : i.val < n + D.length := by have := i.isLt; omega
  have hp : Relation.ReflTransGen (sem_step n D) i.val (outW n D) := live_reaches_out h i.val hlt
  rcases sem_path_chain hp with h1 | ⟨b, h1, h2⟩
  · exact Or.inl h1
  · exact Or.inr ⟨b, h1, h2, sem_branch_empty hG h.1 hC hi h1 h2⟩

lemma sem_bzero_mem (hS : Strict n D) {b : ℕ} (hf : 2 ≤ fanout D b) (he : supp n D b = ∅) :
    b ∈ (inner n D).filter (fun w => ¬ (supp n D w).Nonempty) :=
  Finset.mem_filter.mpr ⟨sb_mem_inner.mpr (lt_of_fanout_pos hS (w := b) (by omega)),
    by rw [he]; exact Finset.not_nonempty_empty⟩

lemma sem_bzero_branch (hS : Strict n D) (hB0 : Bzero n D = 0) {b : ℕ} (hf : 2 ≤ fanout D b) :
    (supp n D b).Nonempty := by
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  have h1 : fanout D b - 1 ≤ ∑ w ∈ (inner n D).filter (fun w => ¬ (supp n D w).Nonempty),
      (fanout D w - 1) :=
    Finset.single_le_sum (f := fun w => fanout D w - 1) (fun _ _ => Nat.zero_le _)
      (sem_bzero_mem hS hf hne)
  unfold Bzero surplusOn at hB0
  omega

lemma sem_bzero_unique (hS : Strict n D) (hB0 : Bzero n D ≤ 1) {b b' : ℕ}
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

lemma sem_noempty_unique (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (hB0 : Bzero n D = 0) {i : Fin n} (hi : i ∈ ineligSet n D) {w : ℕ}
    (hp : Relation.ReflTransGen (sem_step n D) i.val w) : sem_Chain n D i.val w := by
  rcases sem_path_chain hp with h1 | ⟨b, h1, h2⟩
  · exact h1
  · have h3 := sem_bzero_branch h.1 hB0 h2
    rw [sem_branch_empty hG h.1 hC hi h1 h2] at h3
    exact absurd h3 Finset.not_nonempty_empty

lemma sem_noempty_chain_out (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (hB0 : Bzero n D = 0) {i : Fin n} (hi : i ∈ ineligSet n D) :
    sem_Chain n D i.val (outW n D) :=
  sem_noempty_unique hG h hC hB0 hi
    (live_reaches_out h i.val (by have := i.isLt; omega))

lemma sem_exact_nbhd (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
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

lemma sem_shared_exact (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
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

lemma sem_shared_empty (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
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

lemma sup_occ_wire (P : Finset (Fin n)) (w : ℕ) : sup_Occ n D P (supp n D w ∩ P) := ⟨w, rfl⟩

lemma sup_occ_sub {P M : Finset (Fin n)} (h : sup_Occ n D P M) : M ⊆ P := by
  obtain ⟨w, rfl⟩ := h
  exact Finset.inter_subset_right

lemma sup_mem_carrier {P : Finset (Fin n)} {w : ℕ} :
    w ∈ carrierT n D P ↔ (supp n D w ∩ P).Nonempty := by
  simp only [carrierT, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    obtain ⟨v, hv⟩ := h
    exact ⟨sem_supp_lt (Finset.mem_inter.mp hv).1, v, hv⟩

lemma sup_occ_big (hS : Strict n D) {P M : Finset (Fin n)} (hM : 2 ≤ M.card)
    (h : sup_Occ n D P M) : ∃ j ∈ sup_big n D P, supp n D (n + j) ∩ P = M := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨j, -, -, hj, hmer, -, -⟩ := sem_first_mask hS P M hM w hw
  exact ⟨j, Finset.mem_filter.mpr ⟨hmer, by rw [hj]; exact hM⟩, hj⟩

lemma sup_card_le_big (hS : Strict n D) (P : Finset (Fin n)) (F : Finset (Finset (Fin n)))
    (hF : ∀ M ∈ F, 2 ≤ M.card ∧ sup_Occ n D P M) : F.card ≤ (sup_big n D P).card := by
  have hsub : F ⊆ (sup_big n D P).image (fun j => supp n D (n + j) ∩ P) := by
    intro M hM
    obtain ⟨j, hj, hjM⟩ := sup_occ_big hS (hF M hM).1 (hF M hM).2
    exact Finset.mem_image.mpr ⟨j, hj, hjM⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

lemma sup_triple_parent (hS : Strict n D) {P T : Finset (Fin n)} (hP : P.card ≤ 7)
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

lemma sup_pair_unique {T T' A : Finset (Fin n)} (hA : A.card = 2) (h1 : A ⊆ T)
    (h2 : A ⊆ T') (hint : T ≠ T' → (T ∩ T').card ≤ 1) : T = T' := by
  by_contra hne
  have h3 := Finset.card_le_card (Finset.subset_inter h1 h2)
  have h4 := hint hne
  omega

lemma sup_four_unique {T T' A : Finset (Fin n)} (hT : T.card = 3) (hT' : T'.card = 3)
    (hA : A.card = 4) (h1 : T ⊆ A) (h2 : T' ⊆ A) (hint : T ≠ T' → (T ∩ T').card ≤ 1) :
    T = T' := by
  by_contra hne
  have h3 := Finset.card_le_card (Finset.union_subset h1 h2)
  have h4 := Finset.card_union_add_card_inter T T'
  have h5 := hint hne
  omega

lemma sup_five_cap {T1 T2 T3 A : Finset (Fin n)} (h1 : T1.card = 3) (h2 : T2.card = 3)
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

lemma sup_aux_exists (hS : Strict n D) {P : Finset (Fin n)} (hP : P.card ≤ 7)
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

lemma sup_charge (hS : Strict n D) {P : Finset (Fin n)} (hP : P.card ≤ 7)
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

lemma sup_wit_exists {G : Fin n → Fin n → Prop} (hG : sem_Gr G) (hS : Strict n D)
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

lemma sup_wit_out (hS : Strict n D) {P U : Finset (Fin n)} {f : Fin n} {e : ℕ × Bool}
    (h : sup_Wit n D P U f e) :
    supp n D (n + e.1) ∩ P ⊆ (supp n D (src D e) ∩ P).erase f := by
  obtain ⟨hj, ht, -, -, h2, -, -⟩ := h
  intro v hv
  rw [Finset.mem_inter] at hv
  rw [Finset.mem_erase, Finset.mem_inter]
  exact ⟨fun hvf => h2 (hvf ▸ hv.1), sem_supp_and_sub hS hj ht e.2 hv.1, hv.2⟩

lemma sup_wit_single {P U : Finset (Fin n)} {f : Fin n} {e : ℕ × Bool}
    (h : sup_Wit n D P U f e)
    (hno : ∀ M, M ⊆ U → M.card = 2 → f ∈ M → ¬ sup_Occ n D P M) :
    supp n D (src D e) ∩ P = {f} := by
  obtain ⟨-, -, hfP, h1, -, hsub, hc⟩ := h
  have hfm : f ∈ supp n D (src D e) ∩ P := Finset.mem_inter.mpr ⟨h1, hfP⟩
  have hc2 : (supp n D (src D e) ∩ P).card ≠ 2 :=
    fun h2 => hno _ hsub h2 hfm (sup_occ_wire P _)
  exact (Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr hfm)
    (by rw [Finset.card_singleton]; omega)).symm

lemma sup_cost_inl {P : Finset (Fin n)} {e e0 : ℕ × Bool}
    (h : sup_cost n D P e = Sum.inl e0) : e = e0 ∧ supp n D (n + e.1) ∩ P = ∅ := by
  unfold sup_cost at h
  split_ifs at h with h0
  exact ⟨Sum.inl.inj h, h0⟩

lemma sup_cost_inr {P : Finset (Fin n)} {e : ℕ × Bool} {j : ℕ}
    (h : sup_cost n D P e = Sum.inr j) : e.1 = j ∧ (supp n D (n + e.1) ∩ P).Nonempty := by
  unfold sup_cost at h
  split_ifs at h with h0
  exact ⟨Sum.inr.inj h, Finset.nonempty_iff_ne_empty.mpr h0⟩

lemma sup_cost_ok (hS : Strict n D) {P U : Finset (Fin n)} {f : Fin n} {e : ℕ × Bool}
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

lemma sup_wit_same_pos (hS : Strict n D) {P U U' : Finset (Fin n)} {f f' : Fin n}
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

lemma sup_cost_ne_of_single (hS : Strict n D) {P U U' : Finset (Fin n)} {f f' : Fin n}
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

lemma sup_fibre_le (hS : Strict n D) {P : Finset (Fin n)} (Lab : Finset (Fin n))
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

lemma sup_wit_card (hS : Strict n D) {P : Finset (Fin n)} (Lab : Finset (Fin n))
    (U : Fin n → Finset (Fin n)) (wit : Fin n → ℕ × Bool)
    (hwit : ∀ f ∈ Lab, sup_Wit n D P (U f) f (wit f)) :
    Lab.card ≤ 2 * (Lab.image (fun f => sup_cost n D P (wit f))).card :=
  Finset.card_le_mul_card_image Lab 2 (fun c _ => sup_fibre_le hS Lab U wit hwit c)

lemma sup_wit_card_single (hS : Strict n D) {P : Finset (Fin n)} (Lab S : Finset (Fin n))
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

lemma sup_master (P : Finset (Fin n)) (E : Finset (ℕ × Bool))
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

lemma sup_count (hS : Strict n D) (P : Finset (Fin n)) (E : Finset (ℕ × Bool))
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

lemma sup_assigned_exits {G : Fin n → Fin n → Prop} (hG : sem_Gr G) (h : StrictLive n D)
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

end DagTools

namespace DagTools

lemma sem_three_exits_of_two_ineligible_neighbors
    {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}
    (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    {x i j y : Fin n} (hi : i ∈ ineligSet n D) (hj : j ∈ ineligSet n D)
    (hxi : G x i) (hxj : G x j) (hxy : G x y)
    (hij : i ≠ j) (hyi : y ≠ i) (hyj : y ≠ j) :
    3 ≤ (sem_W n D x).card := by
  obtain ⟨ei, hei, hbi, _⟩ := sem_edge_slots hG h.1 hC hxi
  obtain ⟨ej, hej, hbj, _⟩ := sem_edge_slots hG h.1 hC hxj
  obtain ⟨ey, hey, hby, _⟩ := sem_edge_slots hG h.1 hC hxy
  have si : supp n D (src D (sem_bar ei)) = {i} :=
    sem_inelig_pure hG h.1 hC hi (sem_mem_W.mp hbi).2.1
  have sj : supp n D (src D (sem_bar ej)) = {j} :=
    sem_inelig_pure hG h.1 hC hj (sem_mem_W.mp hbj).2.1
  have eij : ei ≠ ej := by
    intro he
    have hm := (sem_mem_W.mp hbj).2.1
    rw [← he, si, Finset.mem_singleton] at hm
    exact hij hm.symm
  have eiy : ei ≠ ey := by
    intro he
    have hm := (sem_mem_W.mp hby).2.1
    rw [← he, si, Finset.mem_singleton] at hm
    exact hyi hm
  have ejy : ej ≠ ey := by
    intro he
    have hm := (sem_mem_W.mp hby).2.1
    rw [← he, sj, Finset.mem_singleton] at hm
    exact hyj hm
  have hs : ({ei, ej, ey} : Finset (ℕ × Bool)) ⊆ sem_W n D x := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact hei
    · exact hej
    · exact hey
  have hcard : ({ei, ej, ey} : Finset (ℕ × Bool)).card = 3 := by
    simp [eij, eiy, ejy]
  rw [← hcard]
  exact Finset.card_le_card hs


lemma sem_carrier_surplus_two_of_two_ineligible_neighbors
    {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}
    (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    {x i j y : Fin n} (hi : i ∈ ineligSet n D) (hj : j ∈ ineligSet n D)
    (hxi : G x i) (hxj : G x j) (hxy : G x y)
    (hij : i ≠ j) (hyi : y ≠ i) (hyj : y ≠ j) :
    2 ≤ surplusOn D (carrierT n D {x}) := by
  have hthree := sem_three_exits_of_two_ineligible_neighbors hG h hC hi hj hxi hxj hxy hij hyi hyj
  have hflow := sem_flow1 hG h hC x
  omega

lemma sem_residual_nonempty_of_two_ineligible_neighbors
    {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}
    (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (b : Fin n → ℕ) (hb : PureBranch n D b)
    {x i j y : Fin n} (hi : i ∈ ineligSet n D) (hj : j ∈ ineligSet n D)
    (hxi : G x i) (hxj : G x j) (hxy : G x y)
    (hij : i ≠ j) (hyi : y ≠ i) (hyj : y ≠ j) :
    ∃ u ∈ residualUnits n D b, x ∈ supp n D u.1 := by
  have hthree := sem_three_exits_of_two_ineligible_neighbors hG h hC hi hj hxi hxj hxy hij hyi hyj
  have hcount := sem_code_count hG h hC b hb x
  have hcard : (({x} : Finset (Fin n)) ∩ eligSet n D).card ≤ 1 := by
    exact (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
  have hn : ((residualUnits n D b).filter (fun u => x ∈ supp n D u.1)).Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨u, hu⟩ := hn
  exact ⟨u, (Finset.mem_filter.mp hu).1, (Finset.mem_filter.mp hu).2⟩

end DagTools

namespace DagTools

lemma sem_join_chains_or
    {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}
    (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {i j : Fin n} {g : ℕ} (hg : g < D.length) (s : Bool)
    (hi : sem_Chain n D i.val (src D (g, s)))
    (hj : sem_Chain n D j.val (src D (g, !s)))
    (hf : fanout D (src D (g, s)) = 1) : tag D g = false := by
  obtain ⟨a, hia, haj⟩ := hG.2.2.2 i j
  have hs : supp n D (src D (g, !s)) ⊆ {j} :=
    sem_dom_pure hG hS hC j _ (sem_chain_dom hS hj)
  have hz : val D (single a) (src D (g, !s)) = false := by
    cases hv : val D (single a) (src D (g, !s))
    · rfl
    · exact False.elim (haj (Finset.mem_singleton.mp (hs (mem_supp.mpr hv))))
  have hind : val D (single a) (src D (g, !s)) =
      val D (sem_ins i (single a)) (src D (g, !s)) :=
    sem_sibling_indep hS i hg (!s) (by simpa using hi) (by simpa using hf)
      _ _ (sem_ins_agree i (single a))
  have hc : sem_Chain n D i.val (n + g) :=
    Relation.ReflTransGen.tail hi ⟨sem_step_src hg s, hf⟩
  have he : sem_Edge G (sem_ins i (single a)) :=
    ⟨i, a, hia, sem_ins_self i _, by simp [sem_ins, single]⟩
  have ht := (sem_dom_split hS hC (single a) i (n + g)
    (sem_chain_dom hS hc) (sem_single_no_edge hG a) he).2
  cases hop : tag D g
  · rfl
  · exfalso
    rw [sem_val_gate_src hS _ hg s, hop, gop_true, Bool.and_eq_true] at ht
    rw [← hind, hz] at ht
    exact Bool.false_ne_true ht.2


lemma sem_ineligible_reachable_fanout_le_one
    {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}
    (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (hz : Bzero n D = 0) {i : Fin n} (hi : i ∈ ineligSet n D)
    {w : ℕ} (hw : Relation.ReflTransGen (sem_step n D) i.val w) :
    fanout D w ≤ 1 := by
  by_contra hc
  have hf : 2 ≤ fanout D w := by omega
  have hc := sem_noempty_unique hG h hC hz hi hw
  have hs := sem_bzero_branch h.1 hz hf
  rw [sem_branch_empty hG h.1 hC hi hc hf] at hs
  exact Finset.not_nonempty_empty hs

lemma sem_ineligible_join_or
    {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}
    (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (hz : Bzero n D = 0) {i j : Fin n}
    (hi : i ∈ ineligSet n D) (hj : j ∈ ineligSet n D)
    {g : ℕ} (hg : g < D.length) (s : Bool)
    (hpi : Relation.ReflTransGen (sem_step n D) i.val (src D (g, s)))
    (hpj : Relation.ReflTransGen (sem_step n D) j.val (src D (g, !s))) :
    tag D g = false := by
  apply sem_join_chains_or hG h.1 hC hg s
    (sem_noempty_unique hG h hC hz hi hpi) (sem_noempty_unique hG h hC hz hj hpj)
  have hlo := sem_step_fanout (sem_step_src (n := n) hg s)
  have hhi := sem_ineligible_reachable_fanout_le_one hG h hC hz hi hpi
  omega

end DagTools


namespace Four
open PEqualNP.Outside.L_meta_2590_aux.DagTools

lemma exact_non_neighbors {n : Nat} {G : Fin n → Fin n → Prop} {D : Dag}
    (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    (E : Finset (Fin n)) (i : Fin n)
    (hch : sem_Chain n D i.val (outW n D))
    (hind : ∀ a ∈ E, ∀ b ∈ E, ¬ G i a → ¬ G i b → ¬ G a b) :
    ∃ j s, j < D.length ∧ tag D j = true ∧
      ∀ a ∈ E, (a ∈ supp n D (src D (j, s)) ↔ G i a) := by
  obtain ⟨j, s, hj, ht, _, _, hs⟩ := sem_exact_at (G := G) hS i (outW n D) hch E
    (fun S hSE hSi => by
      by_contra hc
      rw [Bool.not_eq_false] at hc
      rcases sem_ins_ind_edge hG ((hC _).mp hc) with ⟨a, ha, hia⟩ | ⟨a, ha, b, hb, hab⟩
      · exact hSi a ha hia
      · exact hind a (hSE ha) b (hSE hb) (hSi a ha) (hSi b hb) hab)
    (fun a _ hia => by
      constructor
      · exact (hC _).mpr ⟨i, a, hia, sem_ins_self i _, by simp [sem_ins, sem_ind]⟩
      · by_contra hc
        rw [Bool.not_eq_false, sem_ind_single] at hc
        exact sem_single_no_edge hG a ((hC _).mp hc))
  exact ⟨j, s, hj, ht, hs⟩

abbrev V := Fin 10

def edgeList : List (V × V) := [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]

abbrev Adj (u v : V) : Prop := (u,v) ∈ edgeList ∨ (v,u) ∈ edgeList


def I : Finset V := {2,4,5,6}
def E : Finset V := Finset.univ \ I

def neighbors (i : V) : Finset V := E.filter (Adj i)

def triples : Finset (Finset V) := I.image neighbors

set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 200000 in
lemma graph_ok : sem_Gr Adj := by unfold sem_Gr Adj; decide +kernel

set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 200000 in
lemma non_neighbors_independent :
    ∀ i ∈ I, ∀ a ∈ E, ∀ b ∈ E, ¬ Adj i a → ¬ Adj i b → ¬ Adj a b := by
  unfold Adj
  decide +kernel

set_option maxHeartbeats 0 in
lemma triple_geometry :
    E.card ≤ 7 ∧ triples.card = 4 ∧
      (∀ T ∈ triples, T.card = 3) ∧
      (∀ T ∈ triples, ∀ U ∈ triples, T ≠ U → (T ∩ U).card ≤ 1) := by
  decide +kernel

lemma eight_merges {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (zero : Bzero 10 D = 0) (hin : I ⊆ ineligSet 10 D) :
    8 ≤ (merges 10 D (carrierT 10 D E)).card := by
  have occ (T) (ht : T ∈ triples) : sup_Occ 10 D E T := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨j, s, _, _, hs⟩ := exact_non_neighbors graph_ok h.1 hc E i
      (sem_noempty_chain_out graph_ok h hc zero (hin hi)) (non_neighbors_independent i hi)
    refine ⟨src D (j,s), ?_⟩
    ext a
    simp only [neighbors, Finset.mem_inter, Finset.mem_filter]
    exact ⟨fun ⟨ha, he⟩ => ⟨he, (hs a he).1 ha⟩, fun ⟨he, ha⟩ => ⟨(hs a he).2 ha, he⟩⟩
  have lower := sup_charge h.1 triple_geometry.1 triples
    (fun T ht => ⟨triple_geometry.2.2.1 T ht, occ T ht⟩)
    triple_geometry.2.2.2 (∅ : Finset (Finset V)) (by simp)
  have upper := Finset.card_le_card (Finset.filter_subset _ _ :
    sup_big 10 D E ⊆ merges 10 D (carrierT 10 D E))
  change (sup_big 10 D E).card ≤ (merges 10 D (carrierT 10 D E)).card at upper
  rw [triple_geometry.2.1, Finset.card_empty] at lower
  omega

end Four


namespace Four
open PEqualNP.Outside.L_meta_2590_aux.DagTools

def complement (S : Finset V) : Finset V := Finset.univ \ S

def nbrs (S : Finset V) (i : V) : Finset V := (complement S).filter (Adj i)

def nbhdFamily (S : Finset V) : Finset (Finset V) := S.image (nbrs S)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 1000000 in
lemma all_four_geometry : ∀ S : Finset V, S.card = 4 →
    (∀ a ∈ S, ∀ b ∈ S, ¬ Adj a b) →
    (∀ i ∈ S, ∀ a ∈ complement S, ∀ b ∈ complement S,
      ¬ Adj i a → ¬ Adj i b → ¬ Adj a b) ∧
    (complement S).card ≤ 7 ∧ (nbhdFamily S).card = 4 ∧
    (∀ T ∈ nbhdFamily S, T.card = 3) ∧
    (∀ T ∈ nbhdFamily S, ∀ U ∈ nbhdFamily S, T ≠ U → (T ∩ U).card ≤ 1) := by
  unfold Adj
  decide +kernel

lemma eight_merges_general {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (zero : Bzero 10 D = 0) (four : (ineligSet 10 D).card = 4) :
    8 ≤ (merges 10 D (carrierT 10 D (eligSet 10 D))).card := by
  let S := ineligSet 10 D
  have hind : ∀ a ∈ S, ∀ b ∈ S, ¬ Adj a b := by
    intro a ha b hb hab
    rcases sem_elig_cover graph_ok h hc hab with ea | eb
    · exact (sem_mem_inelig.mp ha) ea
    · exact (sem_mem_inelig.mp hb) eb
  have geo := all_four_geometry S four hind
  have compl : complement S = eligSet 10 D := by
    ext v
    simp [complement, S, ineligSet]
  have occ (T) (ht : T ∈ nbhdFamily S) : sup_Occ 10 D (complement S) T := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨j, s, _, _, hs⟩ := exact_non_neighbors graph_ok h.1 hc (complement S) i
      (sem_noempty_chain_out graph_ok h hc zero hi) (geo.1 i hi)
    refine ⟨src D (j,s), ?_⟩
    ext a
    simp only [nbrs, Finset.mem_inter, Finset.mem_filter]
    exact ⟨fun ⟨ha, he⟩ => ⟨he, (hs a he).1 ha⟩, fun ⟨he, ha⟩ => ⟨(hs a he).2 ha, he⟩⟩
  have lower := sup_charge h.1 geo.2.1 (nbhdFamily S)
    (fun T ht => ⟨geo.2.2.2.1 T ht, occ T ht⟩)
    geo.2.2.2.2 (∅ : Finset (Finset V)) (by simp)
  have upper := Finset.card_le_card (Finset.filter_subset _ _ :
    sup_big 10 D (complement S) ⊆ merges 10 D (carrierT 10 D (complement S)))
  change (sup_big 10 D (complement S)).card ≤ (merges 10 D (carrierT 10 D (complement S))).card at upper
  rw [geo.2.2.1, Finset.card_empty] at lower
  rw [compl] at upper lower
  omega

end Four


namespace SevenRows

def base : List Nat := [0, 26, 44, 49, 59, 61, 62, 63, 73, 84, 91, 93, 94, 95, 98, 107, 109, 110, 111, 115, 117, 118, 119, 121, 122, 123, 124, 125, 126, 127]
def first : List Nat := [0, 1, 2, 4, 8, 9, 10, 12, 16, 17, 18, 20, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 36, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 68, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127]
def stage (f : Nat) : List Nat := base ++ base.map (fun a => a ||| f)

set_option maxHeartbeats 0 in
lemma base_closed : ∀ a ∈ base, ∀ b ∈ base, a ||| b ∈ base := by decide +kernel

set_option maxHeartbeats 0 in
lemma first_covers : ∀ a ∈ base, ∀ b ∈ base, a &&& b ∈ first := by decide +kernel

set_option maxHeartbeats 0 in
lemma base_target : ∀ a ∈ base, a ≠ 7 := by decide +kernel

def safe (f : Nat) : Bool := decide (f ≠ 7) &&
  (stage f).all (fun a => (stage f).all (fun b => decide (a &&& b ≠ 7 ∧ f ||| (a &&& b) ≠ 7)))

set_option maxHeartbeats 0 in
lemma checked_0 : safe 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_1 : safe 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_2 : safe 2 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_3 : safe 4 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_4 : safe 8 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_5 : safe 9 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_6 : safe 10 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_7 : safe 12 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_8 : safe 16 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_9 : safe 17 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_10 : safe 18 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_11 : safe 20 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_12 : safe 24 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_13 : safe 25 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_14 : safe 26 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_15 : safe 27 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_16 : safe 28 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_17 : safe 29 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_18 : safe 30 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_19 : safe 31 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_20 : safe 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_21 : safe 33 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_22 : safe 34 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_23 : safe 36 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_24 : safe 40 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_25 : safe 41 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_26 : safe 42 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_27 : safe 43 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_28 : safe 44 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_29 : safe 45 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_30 : safe 46 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_31 : safe 47 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_32 : safe 48 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_33 : safe 49 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_34 : safe 50 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_35 : safe 51 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_36 : safe 52 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_37 : safe 53 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_38 : safe 54 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_39 : safe 55 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_40 : safe 56 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_41 : safe 57 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_42 : safe 58 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_43 : safe 59 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_44 : safe 60 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_45 : safe 61 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_46 : safe 62 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_47 : safe 63 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_48 : safe 64 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_49 : safe 65 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_50 : safe 66 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_51 : safe 68 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_52 : safe 72 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_53 : safe 73 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_54 : safe 74 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_55 : safe 75 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_56 : safe 76 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_57 : safe 77 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_58 : safe 78 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_59 : safe 79 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_60 : safe 80 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_61 : safe 81 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_62 : safe 82 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_63 : safe 83 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_64 : safe 84 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_65 : safe 85 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_66 : safe 86 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_67 : safe 87 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_68 : safe 88 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_69 : safe 89 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_70 : safe 90 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_71 : safe 91 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_72 : safe 92 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_73 : safe 93 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_74 : safe 94 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_75 : safe 95 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_76 : safe 96 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_77 : safe 97 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_78 : safe 98 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_79 : safe 99 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_80 : safe 100 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_81 : safe 101 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_82 : safe 102 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_83 : safe 103 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_84 : safe 104 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_85 : safe 105 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_86 : safe 106 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_87 : safe 107 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_88 : safe 108 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_89 : safe 109 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_90 : safe 110 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_91 : safe 111 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_92 : safe 112 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_93 : safe 113 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_94 : safe 114 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_95 : safe 115 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_96 : safe 116 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_97 : safe 117 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_98 : safe 118 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_99 : safe 119 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_100 : safe 120 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_101 : safe 121 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_102 : safe 122 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_103 : safe 123 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_104 : safe 124 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_105 : safe 125 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_106 : safe 126 = true := by decide +kernel

set_option maxHeartbeats 0 in
lemma checked_107 : safe 127 = true := by decide +kernel

lemma checked : first.all safe = true := by
  simp only [first, List.all_cons, List.all_nil, Bool.and_eq_true]
  exact ⟨checked_0, checked_1, checked_2, checked_3, checked_4, checked_5, checked_6, checked_7, checked_8, checked_9, checked_10, checked_11, checked_12, checked_13, checked_14, checked_15, checked_16, checked_17, checked_18, checked_19, checked_20, checked_21, checked_22, checked_23, checked_24, checked_25, checked_26, checked_27, checked_28, checked_29, checked_30, checked_31, checked_32, checked_33, checked_34, checked_35, checked_36, checked_37, checked_38, checked_39, checked_40, checked_41, checked_42, checked_43, checked_44, checked_45, checked_46, checked_47, checked_48, checked_49, checked_50, checked_51, checked_52, checked_53, checked_54, checked_55, checked_56, checked_57, checked_58, checked_59, checked_60, checked_61, checked_62, checked_63, checked_64, checked_65, checked_66, checked_67, checked_68, checked_69, checked_70, checked_71, checked_72, checked_73, checked_74, checked_75, checked_76, checked_77, checked_78, checked_79, checked_80, checked_81, checked_82, checked_83, checked_84, checked_85, checked_86, checked_87, checked_88, checked_89, checked_90, checked_91, checked_92, checked_93, checked_94, checked_95, checked_96, checked_97, checked_98, checked_99, checked_100, checked_101, checked_102, checked_103, checked_104, checked_105, checked_106, checked_107, True.intro⟩

lemma two_and_excluded (f : Nat) (hf : f ∈ first) (a b : Nat)
    (ha : a ∈ stage f) (hb : b ∈ stage f) :
    f ≠ 7 ∧ a &&& b ≠ 7 ∧ f ||| (a &&& b) ≠ 7 := by
  have h := List.all_eq_true.mp checked f hf
  simp only [safe, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨h.1, h.2 a ha b hb⟩

end SevenRows


namespace SevenRows

def extend (S : List Nat) (f : Nat) : List Nat := S ++ S.map (fun a => a ||| f)

def Closed (S : List Nat) : Prop := 0 ∈ S ∧ ∀ a ∈ S, ∀ b ∈ S, a ||| b ∈ S

lemma extend_mem_left {S : List Nat} {f a : Nat} (h : a ∈ S) : a ∈ extend S f :=
  List.mem_append_left _ h

lemma extend_mem_self {S : List Nat} (h : 0 ∈ S) (f : Nat) : f ∈ extend S f := by
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨0, h, Nat.zero_or f⟩

lemma extend_closed {S : List Nat} (h : Closed S) (f : Nat) : Closed (extend S f) := by
  refine ⟨extend_mem_left h.1, ?_⟩
  intro a ha b hb
  rcases List.mem_append.mp ha with ha | ha <;> rcases List.mem_append.mp hb with hb | hb
  · exact extend_mem_left (h.2 a ha b hb)
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨a ||| c, h.2 a ha c hc, by ac_rfl⟩
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨c ||| b, h.2 c hc b hb, by ac_rfl⟩
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hb
    apply List.mem_append_right
    refine List.mem_map.mpr ⟨c ||| d, h.2 c hc d hd, ?_⟩
    calc
      (c ||| d) ||| f = (c ||| d) ||| (f ||| f) := by rw [Nat.or_self]
      _ = (c ||| f) ||| (d ||| f) := by ac_rfl

lemma base_is_closed : Closed base := ⟨by decide +kernel, base_closed⟩

lemma stage_is_closed (f : Nat) : Closed (stage f) := extend_closed base_is_closed f

lemma stage_mem_self (f : Nat) : f ∈ stage f := extend_mem_self base_is_closed.1 f

lemma first_target (f : Nat) (hf : f ∈ first) : f ≠ 7 := by
  exact (two_and_excluded f hf 0 0 (extend_mem_left base_is_closed.1)
    (extend_mem_left base_is_closed.1)).1

set_option maxHeartbeats 0 in
lemma base_small : ∀ a ∈ base, a ≤ 7 → a = 0 := by decide +kernel

lemma base_or_not_target (a v : Nat) (ha : a ∈ base) (hv : v ≠ 7) : a ||| v ≠ 7 := by
  intro eq
  have le : a ≤ 7 := eq ▸ Nat.left_le_or
  have az := base_small a ha le
  exact hv (by simpa [az] using eq)

lemma stage_target (f : Nat) (hf : f ∈ first) : ∀ a ∈ stage f, a ≠ 7 := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact base_target a ha
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact base_or_not_target b f hb (first_target f hf)

lemma two_stage_target (f : Nat) (hf : f ∈ first) (a b : Nat)
    (ha : a ∈ stage f) (hb : b ∈ stage f) :
    ∀ v ∈ extend (stage f) (a &&& b), v ≠ 7 := by
  intro v hv
  rcases List.mem_append.mp hv with hv | hv
  · exact stage_target f hf v hv
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hv
    have safe := two_and_excluded f hf a b ha hb
    rcases List.mem_append.mp hc with hc | hc
    · exact base_or_not_target c (a &&& b) hc safe.2.1
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
      rw [Nat.or_assoc]
      exact base_or_not_target d (f ||| (a &&& b)) hd safe.2.2

def Holds (S w : List Nat) : Prop := ∀ a ∈ w, a ∈ S

def State (k : Nat) (w : List Nat) : Prop :=
  match k with
  | 0 => Holds base w
  | 1 => ∃ f ∈ first, Holds (stage f) w
  | 2 => ∃ f ∈ first, ∃ a ∈ stage f, ∃ b ∈ stage f, Holds (extend (stage f) (a &&& b)) w
  | _ + 3 => False

lemma read_mem {S w : List Nat} (hz : 0 ∈ S) (hw : Holds S w) (i : Nat) : w.getD i 0 ∈ S := by
  by_cases hi : i < w.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    exact hw _ (List.getElem_mem hi)
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : w.length ≤ i), hz]

lemma holds_append {S w : List Nat} (hw : Holds S w) {v : Nat} (hv : v ∈ S) : Holds S (w ++ [v]) := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hw _ hx
  · simpa using (List.mem_singleton.mp hx) ▸ hv

lemma or_holds {S w : List Nat} (hc : Closed S) (hw : Holds S w) (a b : Nat) :
    Holds S (w ++ [w.getD a 0 ||| w.getD b 0]) :=
  holds_append hw (hc.2 _ (read_mem hc.1 hw a) _ (read_mem hc.1 hw b))

lemma or_state {k : Nat} {w : List Nat} (h : State k w) (a b : Nat) :
    State k (w ++ [w.getD a 0 ||| w.getD b 0]) := by
  cases k with
  | zero => exact or_holds base_is_closed h a b
  | succ k =>
    cases k with
    | zero =>
      obtain ⟨f, hf, hw⟩ := h
      exact ⟨f, hf, or_holds (stage_is_closed f) hw a b⟩
    | succ k =>
      cases k with
      | zero =>
        obtain ⟨f, hf, c, hc, d, hd, hw⟩ := h
        exact ⟨f, hf, c, hc, d, hd, or_holds (extend_closed (stage_is_closed f) _) hw a b⟩
      | succ k => exact False.elim h

lemma and_state {k : Nat} {w : List Nat} (hk : k ≤ 1) (h : State k w) (a b : Nat) :
    State (k+1) (w ++ [w.getD a 0 &&& w.getD b 0]) := by
  cases k with
  | zero =>
    let f := w.getD a 0 &&& w.getD b 0
    have hf : f ∈ first := first_covers _ (read_mem base_is_closed.1 h a) _ (read_mem base_is_closed.1 h b)
    exact ⟨f, hf, holds_append (fun x hx => extend_mem_left (h x hx)) (stage_mem_self f)⟩
  | succ k =>
    have k0 : k = 0 := by omega
    subst k
    obtain ⟨f, hf, hw⟩ := h
    have ha := read_mem (stage_is_closed f).1 hw a
    have hb := read_mem (stage_is_closed f).1 hw b
    exact ⟨f, hf, _, ha, _, hb,
      holds_append (fun x hx => extend_mem_left (hw x hx)) (extend_mem_self (stage_is_closed f).1 _)⟩

def step (w : List Nat) (g : Bool × Nat × Nat) : List Nat :=
  w ++ [if g.1 then w.getD g.2.1 0 &&& w.getD g.2.2 0 else w.getD g.2.1 0 ||| w.getD g.2.2 0]

def run (D : List (Bool × Nat × Nat)) (w : List Nat) : List Nat := D.foldl step w

def ands (D : List (Bool × Nat × Nat)) : Nat := D.countP (fun g => g.1)

lemma run_state (D : List (Bool × Nat × Nat)) {k : Nat} {w : List Nat}
    (h : State k w) (bound : k + ands D ≤ 2) : State (k + ands D) (run D w) := by
  induction D generalizing k w with
  | nil => simpa [run, ands] using h
  | cons g D ih =>
    rcases g with ⟨tag,a,b⟩
    cases tag
    · have hc : ands ((false,a,b)::D) = ands D := by simp [ands]
      rw [hc] at bound ⊢
      exact ih (or_state h a b) bound
    · have hc : ands ((true,a,b)::D) = ands D + 1 := by simp [ands]
      rw [hc] at bound ⊢
      have hk : k ≤ 1 := by omega
      have hnext := ih (and_state hk h a b) (by omega : (k+1) + ands D ≤ 2)
      have arith : k + (ands D + 1) = k + 1 + ands D := by omega
      rw [arith]
      exact hnext

lemma state_target {k : Nat} {w : List Nat} (h : State k w) : ∀ a ∈ w, a ≠ 7 := by
  cases k with
  | zero => exact fun a ha => base_target a (h a ha)
  | succ k =>
    cases k with
    | zero =>
      obtain ⟨f,hf,hw⟩ := h
      exact fun a ha => stage_target f hf a (hw a ha)
    | succ k =>
      cases k with
      | zero =>
        obtain ⟨f,hf,a,ha,b,hb,hw⟩ := h
        exact fun c hc => two_stage_target f hf a b ha hb c (hw c hc)
      | succ k => exact False.elim h

lemma trace_bound (D : List (Bool × Nat × Nat)) (w : List Nat)
    (hw : Holds base w) (bound : ands D ≤ 2) : ∀ a ∈ run D w, a ≠ 7 := by
  exact state_target (run_state D (k := 0) hw (by simpa using bound))

lemma trace_getD_bound (D : List (Bool × Nat × Nat)) (w : List Nat)
    (hw : Holds base w) (bound : ands D ≤ 2) (i : Nat) : (run D w).getD i 0 ≠ 7 := by
  have h := trace_bound D w hw bound
  by_cases hi : i < (run D w).length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    exact h _ (List.getElem_mem hi)
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : (run D w).length ≤ i)]

lemma three_ands (D : List (Bool × Nat × Nat)) (w : List Nat)
    (hw : Holds base w) (i : Nat) (hval : (run D w).getD i 0 = 7) : 3 ≤ ands D := by
  by_contra hn
  exact trace_getD_bound D w hw (by omega) i hval

end SevenRows


namespace SevenRows
open PEqualNP.Outside.L_meta_2590_aux.DagTools

lemma testBit_getD (w : List Nat) (r i : Nat) :
    (w.getD i 0).testBit r = (w.map (fun a => a.testBit r)).getD i false := by
  induction w generalizing i with
  | nil => simp
  | cons a w ih =>
    cases i with
    | zero => rfl
    | succ i => simpa using ih i

lemma step_testBits (w : List Nat) (g : Bool × Nat × Nat) (r : Nat) :
    (step w g).map (fun a => a.testBit r) =
      wstep (w.map (fun a => a.testBit r)) g := by
  rcases g with ⟨b, i, j⟩
  cases b <;> dsimp [step, wstep, gop] <;> rw [List.map_append] <;>
    simp only [List.map_cons, List.map_nil, Nat.testBit_or, Nat.testBit_and, testBit_getD]

lemma run_testBits (D : Dag) (w : List Nat) (r : Nat) :
    (run D w).map (fun a => a.testBit r) = wl D (w.map (fun a => a.testBit r)) := by
  induction D generalizing w with
  | nil => rfl
  | cons g D ih =>
    change (run D (step w g)).map (fun a => a.testBit r) =
      wl D (wstep (w.map (fun a => a.testBit r)) g)
    rw [ih, step_testBits]

lemma run_getD_testBit (D : Dag) (w : List Nat) (r i : Nat) :
    ((run D w).getD i 0).testBit r =
      (wl D (w.map (fun a => a.testBit r))).getD i false := by
  rw [testBit_getD, run_testBits]

lemma run_testBit_val {n : Nat} (D : Dag) (masks : Fin n → Nat) (r i : Nat) :
    ((run D (List.ofFn masks)).getD i 0).testBit r =
      val D (fun v => (masks v).testBit r) i := by
  rw [run_getD_testBit]
  simp only [val, List.map_ofFn, Function.comp_def]

lemma getD_lt_two_pow (w : List Nat) (b i : Nat)
    (hw : ∀ a ∈ w, a < 2 ^ b) : w.getD i 0 < 2 ^ b := by
  by_cases hi : i < w.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    exact hw _ (List.getElem_mem hi)
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : w.length ≤ i)]

lemma step_lt_two_pow (w : List Nat) (g : Bool × Nat × Nat) (b : Nat)
    (hw : ∀ a ∈ w, a < 2 ^ b) : ∀ a ∈ step w g, a < 2 ^ b := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact hw a ha
  · have he := List.mem_singleton.mp ha
    subst a
    split
    · exact Nat.and_lt_two_pow _ (getD_lt_two_pow w b g.2.2 hw)
    · exact Nat.or_lt_two_pow (getD_lt_two_pow w b g.2.1 hw) (getD_lt_two_pow w b g.2.2 hw)

lemma run_lt_two_pow (D : Dag) (w : List Nat) (b : Nat)
    (hw : ∀ a ∈ w, a < 2 ^ b) : ∀ a ∈ run D w, a < 2 ^ b := by
  induction D generalizing w with
  | nil => exact hw
  | cons g D ih => exact ih (step w g) (step_lt_two_pow w g b hw)

lemma nat_eq_of_low_testBits {a c b : Nat} (ha : a < 2 ^ b) (hc : c < 2 ^ b)
    (hbits : ∀ r : Fin b, a.testBit r.val = c.testBit r.val) : a = c := by
  apply Nat.eq_of_testBit_eq
  intro r
  by_cases hr : r < b
  · exact hbits ⟨r, hr⟩
  · have hle : 2 ^ b ≤ 2 ^ r := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
    rw [Nat.testBit_lt_two_pow (ha.trans_le hle), Nat.testBit_lt_two_pow (hc.trans_le hle)]

lemma seven_target_bits : ∀ r : Fin 7, (7 : Nat).testBit r.val = decide (r.val < 3) := by
  decide +kernel

lemma run_eq_seven_of_rows {n : Nat} (D : Dag) (masks : Fin n → Nat) (i : Nat)
    (small : ∀ v, masks v < 128)
    (rows : ∀ r : Fin 7, val D (fun v => (masks v).testBit r.val) i = decide (r.val < 3)) :
    (run D (List.ofFn masks)).getD i 0 = 7 := by
  have init : ∀ a ∈ List.ofFn masks, a < 2 ^ 7 := by
    intro a ha
    obtain ⟨v, rfl⟩ := List.mem_ofFn.mp ha
    exact small v
  have bound := getD_lt_two_pow (run D (List.ofFn masks)) 7 i (run_lt_two_pow D _ 7 init)
  apply nat_eq_of_low_testBits bound (by decide : 7 < 2 ^ 7)
  intro r
  rw [run_testBit_val, rows, seven_target_bits]


lemma run_getD_ne_seven (D : Dag) (w : List Nat)
    (hw : Holds base w) (bound : ands D ≤ 2) (i : Nat) :
    (run D w).getD i 0 ≠ 7 := by
  by_cases hi : i < (run D w).length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    exact trace_bound D w hw bound _ (List.getElem_mem hi)
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : (run D w).length ≤ i)]

lemma three_ands_of_seven_rows {n : Nat} (D : Dag) (masks : Fin n → Nat) (i : Nat)
    (small : ∀ v, masks v < 128) (hw : Holds base (List.ofFn masks))
    (rows : ∀ r : Fin 7, val D (fun v => (masks v).testBit r.val) i = decide (r.val < 3)) :
    3 ≤ ands D := by
  by_contra hc
  have he := run_eq_seven_of_rows D masks i small rows
  exact run_getD_ne_seven D _ hw (by omega) i he


lemma step_eq_copy_of_bit_rows (w : List Nat) (g : Bool × Nat × Nat) (p : Nat)
    (small : ∀ a ∈ w, a < 128)
    (rows : ∀ r : Fin 7,
      gop g.1 ((w.getD g.2.1 0).testBit r.val) ((w.getD g.2.2 0).testBit r.val) =
        (w.getD p 0).testBit r.val) :
    step w g = w ++ [w.getD p 0] := by
  let q := if g.1 then w.getD g.2.1 0 &&& w.getD g.2.2 0 else w.getD g.2.1 0 ||| w.getD g.2.2 0
  have ha : w.getD g.2.1 0 < 2 ^ 7 := getD_lt_two_pow w 7 _ small
  have hb : w.getD g.2.2 0 < 2 ^ 7 := getD_lt_two_pow w 7 _ small
  have hp : w.getD p 0 < 2 ^ 7 := getD_lt_two_pow w 7 _ small
  have hq : q < 2 ^ 7 := by
    dsimp [q]
    split
    · exact Nat.and_lt_two_pow _ hb
    · exact Nat.or_lt_two_pow ha hb
  have eq : q = w.getD p 0 := by
    apply nat_eq_of_low_testBits hq hp
    intro r
    cases ht : g.1 <;> simpa [q, ht, gop] using rows r
  change w ++ [q] = w ++ [w.getD p 0]
  rw [eq]


lemma step_eq_copy_of_val_rows {n : Nat} (D : Dag) (masks : Fin n → Nat)
    (hS : Strict n D) {j : Nat} (hj : j < D.length) (p : Nat) (hp : p < n + j)
    (small : ∀ v, masks v < 128)
    (rows : ∀ r : Fin 7,
      val D (fun v => (masks v).testBit r.val) (n + j) =
        val D (fun v => (masks v).testBit r.val) p) :
    step (run (D.take j) (List.ofFn masks)) (D.getD j (false, 0, 0)) =
      run (D.take j) (List.ofFn masks) ++ [(run (D.take j) (List.ofFn masks)).getD p 0] := by
  apply step_eq_copy_of_bit_rows
  · apply run_lt_two_pow (D.take j) (List.ofFn masks) 7
    intro a ha
    obtain ⟨v, rfl⟩ := List.mem_ofFn.mp ha
    exact small v
  · intro r
    rw [run_testBit_val, run_testBit_val, run_testBit_val]
    change gop (tag D j)
      (val (D.take j) (fun v => (masks v).testBit r.val) (opA D j))
      (val (D.take j) (fun v => (masks v).testBit r.val) (opB D j)) =
      val (D.take j) (fun v => (masks v).testBit r.val) p
    rw [val_take D _ j _ (hS j hj).1 hj.le,
      val_take D _ j _ (hS j hj).2.1 hj.le, val_take D _ j p hp hj.le,
      ← val_gate hS _ j hj]
    exact rows r

end SevenRows


namespace Neutral
open PEqualNP.Outside.L_meta_2590_aux.DagTools

lemma exit_gate_injective {n : Nat} {G : Fin n → Fin n → Prop} {D : Dag}
    (hG : sem_Gr G) {i j : Fin n} (hne : i ≠ j)
    {gi gj : Nat} {si sj : Bool}
    (hi : supp n D (src D (gi,si)) = {i})
    (hj : supp n D (src D (gj,sj)) = {j})
    (hn : ∀ a, G i a → a ∈ supp n D (src D (gi,!si))) : gi ≠ gj := by
  intro heq
  subst gj
  obtain ⟨a, hia, haj⟩ := hG.2.2.2 i j
  have ha := hn a hia
  cases si <;> cases sj
  · exact hne (Finset.singleton_injective (hi.symm.trans hj))
  · simp only [Bool.not_false] at ha
    rw [hj, Finset.mem_singleton] at ha
    exact haj ha
  · simp only [Bool.not_true] at ha
    rw [hj, Finset.mem_singleton] at ha
    exact haj ha
  · exact hne (Finset.singleton_injective (hi.symm.trans hj))

lemma neutral_ineligible_family {n : Nat} {G : Fin n → Fin n → Prop} {D : Dag}
    (hG : sem_Gr G) (h : StrictLive n D) (hc : sem_Comp n G D)
    (I : Finset (Fin n)) (hin : I ⊆ ineligSet n D)
    (R : Finset (Fin n → Bool))
    (hit : ∀ i ∈ I, ∀ x ∈ R, ∃ a, G i a ∧ x a = true) :
    ∃ T : Finset Nat, T.card = I.card ∧ ∀ g ∈ T,
      g < D.length ∧ tag D g = true ∧ ∃ s : Bool,
        ∀ x ∈ R, val D x (n+g) = val D x (src D (g,s)) := by
  classical
  have hex : ∀ i : Fin n, ∃ e : Nat × Bool, i ∈ I →
      e.1 < D.length ∧ tag D e.1 = true ∧ supp n D (src D e) = {i} ∧
        ∀ a, G i a → a ∈ supp n D (src D (e.1,!e.2)) := by
    intro i
    by_cases hi : i ∈ I
    · obtain ⟨e, he, ht, hs, _, hn, _, _⟩ := sem_inelig_consumer hG h hc (hin hi)
      exact ⟨e, fun _ => ⟨he,ht,hs,hn⟩⟩
    · exact ⟨(0,false), fun hh => False.elim (hi hh)⟩
  choose e he using hex
  refine ⟨I.image (fun i => (e i).1), ?_, ?_⟩
  · apply Finset.card_image_of_injOn
    intro i hi j hj eq
    by_contra ne
    exact exit_gate_injective hG ne (he i hi).2.2.1 (he j hj).2.2.1 (he i hi).2.2.2 eq
  · intro g hg
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hg
    obtain ⟨hlt, ht, _, hn⟩ := he i hi
    refine ⟨hlt, ht, (e i).2, ?_⟩
    intro x hx
    obtain ⟨a, hia, hxa⟩ := hit i hi x hx
    have htval : val D x (src D ((e i).1,!(e i).2)) = true :=
      sem_val_of_supp h.1 (hn a hia) hxa
    rw [sem_val_gate_src h.1 x hlt (e i).2, ht, gop_true, htval, Bool.and_true]

end Neutral


namespace Neutral
open PEqualNP.Outside.L_meta_2590_aux.DagTools

lemma chain_and_neighbors {n : Nat} {G : Fin n → Fin n → Prop} {D : Dag}
    (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {i : Fin n} {g : Nat} (hg : g < D.length) (ht : tag D g = true) (s : Bool)
    (hi : sem_Chain n D i.val (src D (g,s)))
    (hf : fanout D (src D (g,s)) = 1) :
    ∀ a, G i a → a ∈ supp n D (src D (g,!s)) := by
  intro a hia
  have hind : val D (single a) (src D (g,!s)) =
      val D (sem_ins i (single a)) (src D (g,!s)) :=
    sem_sibling_indep hS i hg (!s) (by simpa using hi) (by simpa using hf)
      _ _ (sem_ins_agree i (single a))
  have hch : sem_Chain n D i.val (n+g) :=
    Relation.ReflTransGen.tail hi ⟨sem_step_src hg s, hf⟩
  have he : sem_Edge G (sem_ins i (single a)) :=
    ⟨i,a,hia,sem_ins_self i _,by simp [sem_ins,single]⟩
  have hv := (sem_dom_split hS hC (single a) i (n+g)
    (sem_chain_dom hS hch) (sem_single_no_edge hG a) he).2
  rw [sem_val_gate_src hS _ hg s, ht, gop_true, Bool.and_eq_true] at hv
  exact mem_supp.mpr (hind.trans hv.2)

lemma chain_and_neutral {n : Nat} {G : Fin n → Fin n → Prop} {D : Dag}
    (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {i : Fin n} {g : Nat} (hg : g < D.length) (ht : tag D g = true) (s : Bool)
    (hi : sem_Chain n D i.val (src D (g,s)))
    (hf : fanout D (src D (g,s)) = 1)
    (x : Fin n → Bool) (hit : ∃ a, G i a ∧ x a = true) :
    val D x (n+g) = val D x (src D (g,s)) := by
  obtain ⟨a, hia, hxa⟩ := hit
  have hp := chain_and_neighbors hG hS hC hg ht s hi hf a hia
  have hv := sem_val_of_supp hS hp hxa
  rw [sem_val_gate_src hS _ hg s, ht, gop_true, hv, Bool.and_true]

end Neutral


namespace SevenRows

def neutralizeFrom : List (Bool × Nat × Nat) → Nat → Finset Nat → (Nat → Nat) → List (Bool × Nat × Nat)
  | [], _, _, _ => []
  | g :: D, off, T, p => (if off ∈ T then (false,p off,p off) else g) :: neutralizeFrom D (off+1) T p

def NeutralFrom (D : List (Bool × Nat × Nat)) (w : List Nat) (off : Nat)
    (T : Finset Nat) (p : Nat → Nat) : Prop :=
  ∀ j, j < D.length → off+j ∈ T →
    step (run (D.take j) w) (D.getD j (false,0,0)) =
      run (D.take j) w ++ [(run (D.take j) w).getD (p (off+j)) 0]

lemma neutralize_run (D : List (Bool × Nat × Nat)) (w : List Nat) (off : Nat)
    (T : Finset Nat) (p : Nat → Nat) (h : NeutralFrom D w off T p) :
    run (neutralizeFrom D off T p) w = run D w := by
  induction D generalizing w off with
  | nil => rfl
  | cons g D ih =>
    have head : step w (if off ∈ T then (false,p off,p off) else g) = step w g := by
      by_cases ho : off ∈ T
      · have hh := h 0 (by simp) (by simpa using ho)
        simp only [List.take_zero, run, List.foldl_nil, List.getD_cons_zero, Nat.add_zero] at hh
        simpa [ho, step, Nat.or_self] using hh.symm
      · simp [ho]
    have tail : NeutralFrom D (step w g) (off+1) T p := by
      intro j hj ht
      have same : off+(j+1) = off+1+j := by omega
      have hh := h (j+1) (by simpa using hj) (by simpa [same] using ht)
      simpa only [List.take_succ_cons, List.getD_cons_succ, run, List.foldl_cons, same] using hh
    change run (neutralizeFrom D (off+1) T p) (step w (if off ∈ T then (false,p off,p off) else g)) =
      run D (step w g)
    rw [head]
    exact ih (step w g) (off+1) tail

def removed (D : List (Bool × Nat × Nat)) (off : Nat) (T : Finset Nat) : Nat :=
  ∑ j ∈ Finset.range D.length, if off+j ∈ T then 1 else 0

lemma removed_cons (g : Bool × Nat × Nat) (D : List (Bool × Nat × Nat)) (off : Nat) (T : Finset Nat) :
    removed (g::D) off T = removed D (off+1) T + if off ∈ T then 1 else 0 := by
  unfold removed
  rw [List.length_cons, Finset.sum_range_succ']
  simp only [Nat.add_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have eq : off+(j+1)=off+1+j := by omega
  rw [eq]

lemma neutralize_count (D : List (Bool × Nat × Nat)) (off : Nat) (T : Finset Nat) (p : Nat → Nat)
    (h : ∀ j, j < D.length → off+j ∈ T → (D.getD j (false,0,0)).1 = true) :
    ands (neutralizeFrom D off T p) + removed D off T = ands D := by
  induction D generalizing off with
  | nil => simp [ands, neutralizeFrom, removed]
  | cons g D ih =>
    have tail : ∀ j, j<D.length → off+1+j ∈ T → (D.getD j (false,0,0)).1 = true := by
      intro j hj ht
      have same : off+(j+1)=off+1+j := by omega
      simpa only [List.getD_cons_succ] using h (j+1) (by simpa using hj) (by simpa [same] using ht)
    have hit := ih (off+1) tail
    rw [neutralizeFrom, removed_cons]
    by_cases ho : off ∈ T
    · have hg : g.1=true := by simpa using h 0 (by simp) (by simpa using ho)
      simp [ho, ands, hg] at hit ⊢
      omega
    · simp [ho, ands, List.countP_cons] at hit ⊢
      omega

lemma removed_zero (D : List (Bool × Nat × Nat)) (T : Finset Nat)
    (h : ∀ j ∈ T, j < D.length) : removed D 0 T = T.card := by
  unfold removed
  simp only [Nat.zero_add]
  rw [←Finset.card_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨fun hj => hj.2, fun hj => ⟨h j hj,hj⟩⟩

lemma neutralize_count_zero (D : List (Bool × Nat × Nat)) (T : Finset Nat) (p : Nat → Nat)
    (sub : ∀ j ∈ T, j < D.length)
    (h : ∀ j ∈ T, (D.getD j (false,0,0)).1=true) :
    ands (neutralizeFrom D 0 T p) + T.card = ands D := by
  have hc := neutralize_count D 0 T p (fun j _ hj => h j (by simpa using hj))
  rw [removed_zero D T sub] at hc
  exact hc

end SevenRows


namespace SevenGeneral
open PEqualNP.Outside.L_meta_2590_aux.DagTools
open PEqualNP.Outside.L_meta_2590_aux.Four
open PEqualNP.Outside.L_meta_2590_aux.SevenRows
open PEqualNP.Outside.L_meta_2590_aux.Neutral

lemma and_bound_of_rows {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (I : Finset (Fin 10)) (hin : I ⊆ ineligSet 10 D) (masks : Fin 10 → Nat)
    (small : ∀ v, masks v < 128) (inputBase : Holds base (List.ofFn masks))
    (hit : ∀ i ∈ I, ∀ r : Fin 7, ∃ a : Fin 10, Adj i a ∧ (masks a).testBit r.val = true)
    (rows : ∀ r : Fin 7, sem_Edge Adj (fun v => (masks v).testBit r.val) ↔ r.val < 3) :
    I.card + 3 ≤ ands D := by
  classical
  let row (r : Fin 7) (v : Fin 10) : Bool := (masks v).testBit r.val
  let R : Finset (Fin 10 → Bool) := Finset.univ.image row
  have hitR : ∀ i ∈ I, ∀ x ∈ R, ∃ a, Adj i a ∧ x a = true := by
    intro i hi x hx
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hx
    exact hit i hi r
  obtain ⟨T, htcard, hT⟩ := neutral_ineligible_family graph_ok h hc I hin R hitR
  have hex : ∀ g : Nat, ∃ s : Bool, g ∈ T → ∀ r : Fin 7,
      val D (row r) (10+g) = val D (row r) (src D (g,s)) := by
    intro g
    by_cases hg : g ∈ T
    · obtain ⟨_, _, s, hs⟩ := hT g hg
      exact ⟨s, fun _ r => hs _ (Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩)⟩
    · exact ⟨false, fun hh => False.elim (hg hh)⟩
  choose side hs using hex
  let p (g : Nat) := src D (g,side g)
  have neu : NeutralFrom D (List.ofFn masks) 0 T p := by
    intro j hj ht
    simp only [Nat.zero_add] at ht ⊢
    exact step_eq_copy_of_val_rows D masks h.1 hj (p j) (sem_src_lt h.1 hj (side j)) small (hs j ht)
  have same := neutralize_run D (List.ofFn masks) 0 T p neu
  have cnt := neutralize_count_zero D T p (fun g hg => (hT g hg).1)
    (fun g hg => (hT g hg).2.1)
  have target : (run D (List.ofFn masks)).getD (outW 10 D) 0 = 7 := by
    apply run_eq_seven_of_rows D masks _ small
    intro r
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact (hc _).trans (rows r)
  have three : 3 ≤ ands (neutralizeFrom D 0 T p) := by
    apply three_ands _ (List.ofFn masks) inputBase (outW 10 D)
    rw [same]
    exact target
  rw [htcard] at cnt
  omega

def casesI (k : Fin 5) : Finset (Fin 10) :=
  ([{0,2,8,9},{0,3,6,7},{1,3,5,9},{1,4,7,8},{2,4,5,6}] : List (Finset (Fin 10))).getD k.val ∅

def casesMasks (k : Fin 5) (v : Fin 10) : Nat :=
  (([[0,26,0,49,73,44,98,84,0,0],
     [0,44,84,0,26,73,0,0,49,98],
     [44,0,26,0,84,0,73,98,49,0],
     [26,0,44,84,0,98,73,0,0,49],
     [49,73,0,26,0,0,0,44,98,84]] : List (List Nat)).getD k.val []).getD v.val 0

set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 1000000 in
lemma classify_four : ∀ S : Finset (Fin 10), S.card = 4 →
    (∀ a ∈ S, ∀ b ∈ S, ¬ Adj a b) → ∃ k : Fin 5, casesI k = S := by
  unfold Adj
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 1000000 in
lemma cases_geometry : ∀ k : Fin 5,
    (casesI k).card = 4 ∧ (∀ v, casesMasks k v < 128) ∧ Holds base (List.ofFn (casesMasks k)) ∧
    (∀ i ∈ casesI k, ∀ r : Fin 7, ∃ a : Fin 10, Adj i a ∧ (casesMasks k a).testBit r.val = true) ∧
    (∀ r : Fin 7, sem_Edge Adj (fun v => (casesMasks k v).testBit r.val) ↔ r.val < 3) := by
  unfold Holds sem_Edge Adj
  decide +kernel

lemma seven_ands_of_four_ineligible {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (four : (ineligSet 10 D).card = 4) : 7 ≤ ands D := by
  have hind : ∀ a ∈ ineligSet 10 D, ∀ b ∈ ineligSet 10 D, ¬ Adj a b := by
    intro a ha b hb hab
    rcases sem_elig_cover graph_ok h hc hab with ea | eb
    · exact (sem_mem_inelig.mp ha) ea
    · exact (sem_mem_inelig.mp hb) eb
  obtain ⟨k, hk⟩ := classify_four (ineligSet 10 D) four hind
  have geo := cases_geometry k
  have bound := and_bound_of_rows h hc (casesI k) (hk ▸ Finset.Subset.refl _) (casesMasks k)
    geo.2.1 geo.2.2.1 geo.2.2.2.1 geo.2.2.2.2
  rw [geo.1] at bound
  exact bound

end SevenGeneral


namespace Rigidity

variable {α : Type} [DecidableEq α]

def Serves (A T : Finset α) : Prop :=
  (A.card = 2 ∧ A ⊆ T) ∨ (A.card = 4 ∧ T ⊆ A)

lemma serves_unique {A T U : Finset α} (hT : T.card = 3) (hU : U.card = 3)
    (hint : (T ∩ U).card ≤ 1) (ha : Serves A T) (hb : Serves A U) : False := by
  rcases ha with ⟨h2, hat⟩ | ⟨h4, hta⟩ <;>
    rcases hb with ⟨h2', hau⟩ | ⟨h4', hua⟩
  · have hsub : A ⊆ T ∩ U := fun x hx => Finset.mem_inter.mpr ⟨hat hx, hau hx⟩
    have := Finset.card_le_card hsub
    omega
  · omega
  · omega
  · have hsub : T ∪ U ⊆ A := Finset.union_subset hta hua
    have hle := Finset.card_le_card hsub
    have heq := Finset.card_union_add_card_inter T U
    omega

lemma proper_inter_large {T P Q : Finset α} (hT : T.card = 3)
    (hP : P ≠ T) (hQ : Q ≠ T) (hinter : T = P ∩ Q) :
    4 ≤ P.card ∧ 4 ≤ Q.card := by
  have htp : T ⊆ P := by rw [hinter]; exact Finset.inter_subset_left
  have htq : T ⊆ Q := by rw [hinter]; exact Finset.inter_subset_right
  constructor
  · by_contra h
    have hEq : T = P := Finset.eq_of_subset_of_card_le htp (by omega)
    exact hP hEq.symm
  · by_contra h
    have hEq : T = Q := Finset.eq_of_subset_of_card_le htq (by omega)
    exact hQ hEq.symm

lemma inter_serves {S T P Q : Finset α} (hS : S.card ≤ 6) (hT : T.card = 3)
    (hPS : P ⊆ S) (hQS : Q ⊆ S) (hP : P ≠ T) (hQ : Q ≠ T)
    (hinter : T = P ∩ Q) : Serves P T ∨ Serves Q T := by
  have large := proper_inter_large hT hP hQ hinter
  have hsum := Finset.card_union_add_card_inter P Q
  have hu : (P ∪ Q).card ≤ 6 := (Finset.card_le_card (Finset.union_subset hPS hQS)).trans hS
  have hi : (P ∩ Q).card = 3 := by rw [← hinter]; exact hT
  have small : P.card = 4 ∨ Q.card = 4 := by omega
  rcases small with hp | hq
  · exact Or.inl (Or.inr ⟨hp, by rw [hinter]; exact Finset.inter_subset_left⟩)
  · exact Or.inr (Or.inr ⟨hq, by rw [hinter]; exact Finset.inter_subset_right⟩)

lemma union_pair {T P Q : Finset α} (hT : T.card = 3)
    (hP : P ≠ T) (hQ : Q ≠ T) (hunion : T = P ∪ Q) :
    (P.card = 2 ∧ P ⊆ T) ∨ (Q.card = 2 ∧ Q ⊆ T) := by
  have hpt : P ⊆ T := by rw [hunion]; exact Finset.subset_union_left
  have hqt : Q ⊆ T := by rw [hunion]; exact Finset.subset_union_right
  have hp : P.card ≤ 2 := by
    have hle := Finset.card_le_card hpt
    by_contra h
    have hEq : P = T := Finset.eq_of_subset_of_card_le hpt (by omega)
    exact hP hEq
  have hq : Q.card ≤ 2 := by
    have hle := Finset.card_le_card hqt
    by_contra h
    have hEq : Q = T := Finset.eq_of_subset_of_card_le hqt (by omega)
    exact hQ hEq
  have hle := Finset.card_union_le P Q
  have hcard : (P ∪ Q).card = 3 := by rw [← hunion]; exact hT
  have cases : P.card = 2 ∨ Q.card = 2 := by omega
  rcases cases with hp | hq
  · exact Or.inl ⟨hp, hpt⟩
  · exact Or.inr ⟨hq, hqt⟩

lemma parent_cases {L A : Finset (Finset α)}
    (hL : ∀ T ∈ L, T.card = 3) {T : Finset α} (hT : T ∈ L)
    (hpar : ∃ P Q : Finset α,
      (P.card ≤ 1 ∨ P ∈ L ∨ P ∈ A) ∧ (Q.card ≤ 1 ∨ Q ∈ L ∨ Q ∈ A) ∧
      P ≠ T ∧ Q ≠ T ∧ (T = P ∪ Q ∨ T = P ∩ Q)) :
    (∃ M ∈ A, M.card = 2 ∧ M ⊆ T) ∨
      ∃ P ∈ A, ∃ Q ∈ A, P ≠ T ∧ Q ≠ T ∧ T = P ∩ Q := by
  obtain ⟨P,Q,hP,hQ,hPT,hQT,hpq⟩ := hpar
  rcases hpq with hu | hi
  · left
    rcases union_pair (hL T hT) hPT hQT hu with ⟨h2, hsub⟩ | ⟨h2,hsub⟩
    · refine ⟨P, ?_, h2, hsub⟩
      rcases hP with h | h | h
      · omega
      · have := hL P h; omega
      · exact h
    · refine ⟨Q, ?_, h2, hsub⟩
      rcases hQ with h | h | h
      · omega
      · have := hL Q h; omega
      · exact h
  · right
    have large := proper_inter_large (hL T hT) hPT hQT hi
    have pa : P ∈ A := by
      rcases hP with h | h | h
      · omega
      · have := hL P h; omega
      · exact h
    have qa : Q ∈ A := by
      rcases hQ with h | h | h
      · omega
      · have := hL Q h; omega
      · exact h
    exact ⟨P,pa,Q,qa,hPT,hQT,hi⟩

lemma eight_family_rigid {S : Finset α} {L A : Finset (Finset α)}
    (hS : S.card ≤ 6) (hLcard : L.card = 4) (hAcard : A.card ≤ 4)
    (hL : ∀ T ∈ L, T.card = 3)
    (hint : ∀ T ∈ L, ∀ U ∈ L, T ≠ U → (T ∩ U).card ≤ 1)
    (hAS : ∀ M ∈ A, M ⊆ S)
    (hpar : ∀ T ∈ L, ∃ P Q : Finset α,
      (P.card ≤ 1 ∨ P ∈ L ∨ P ∈ A) ∧ (Q.card ≤ 1 ∨ Q ∈ L ∨ Q ∈ A) ∧
      P ≠ T ∧ Q ≠ T ∧ (T = P ∪ Q ∨ T = P ∩ Q)) :
    A.card = 4 ∧ (∀ M ∈ A, M.card = 2 ∧ ∃ T ∈ L, M ⊆ T) ∧
      ∀ T ∈ L, ∃ M ∈ A, M.card = 2 ∧ M ⊆ T := by
  classical
  have cases (T) (hT : T ∈ L) := parent_cases hL hT (hpar T hT)
  have has (T) (hT : T ∈ L) : ∃ M ∈ A, Serves M T := by
    rcases cases T hT with ⟨M,hM,h2,hsub⟩ | ⟨P,hP,Q,hQ,hPT,hQT,hi⟩
    · exact ⟨M,hM,Or.inl ⟨h2,hsub⟩⟩
    · rcases inter_serves hS (hL T hT) (hAS P hP) (hAS Q hQ) hPT hQT hi with hp | hq
      · exact ⟨P,hP,hp⟩
      · exact ⟨Q,hQ,hq⟩
  let f : Finset α → Finset α := fun T => if hT : T ∈ L then Classical.choose (has T hT) else ∅
  have hf (T) (hT : T ∈ L) : f T ∈ A ∧ Serves (f T) T := by
    simp only [f, dite_eq_left hT]
    exact Classical.choose_spec (has T hT)
  have hinj : Set.InjOn f L := by
    intro T hT U hU he
    by_contra ne
    exact serves_unique (hL T hT) (hL U hU) (hint T hT U hU ne)
      (hf T hT).2 (he ▸ (hf U hU).2)
  have himage : L.image f = A := by
    refine Finset.eq_of_subset_of_card_le (by
      intro M hM
      obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hM
      exact (hf T hT).1) ?_
    rw [Finset.card_image_of_injOn hinj, hLcard]
    exact hAcard
  have unique (M) (hM : M ∈ A) (T) (hT : T ∈ L) (hm : Serves M T) : M = f T := by
    have hmem : M ∈ L.image f := by rw [himage]; exact hM
    obtain ⟨U,hU,he⟩ := Finset.mem_image.mp hmem
    have eq : U = T := by
      by_contra ne
      exact serves_unique (hL U hU) (hL T hT) (hint U hU T hT ne)
        (he ▸ (hf U hU).2) hm
    subst U
    exact he.symm
  have pair (T) (hT : T ∈ L) : (f T).card = 2 ∧ f T ⊆ T := by
    rcases cases T hT with ⟨M,hM,h2,hsub⟩ | ⟨P,hP,Q,hQ,hPT,hQT,hi⟩
    · have eq := unique M hM T hT (Or.inl ⟨h2,hsub⟩)
      rw [← eq]
      exact ⟨h2,hsub⟩
    · have large := proper_inter_large (hL T hT) hPT hQT hi
      have sizes (M) (hM : M ∈ A) : M.card = 2 ∨ M.card = 4 := by
        have hm : M ∈ L.image f := by rw [himage]; exact hM
        obtain ⟨U,hU,rfl⟩ := Finset.mem_image.mp hm
        rcases (hf U hU).2 with h | h
        · exact Or.inl h.1
        · exact Or.inr h.1
      have hp4 : P.card = 4 := by have := sizes P hP; omega
      have hq4 : Q.card = 4 := by have := sizes Q hQ; omega
      have ep : P = f T := unique P hP T hT (Or.inr ⟨hp4, by rw [hi]; exact Finset.inter_subset_left⟩)
      have eq : Q = f T := unique Q hQ T hT (Or.inr ⟨hq4, by rw [hi]; exact Finset.inter_subset_right⟩)
      have same : P = Q := ep.trans eq.symm
      rw [← same, Finset.inter_self] at hi
      exact False.elim (hPT hi.symm)
  refine ⟨?_, ?_⟩
  · rw [← himage, Finset.card_image_of_injOn hinj, hLcard]
  constructor
  · intro M hM
    have hm : M ∈ L.image f := by rw [himage]; exact hM
    obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hm
    exact ⟨(pair T hT).1,T,hT,(pair T hT).2⟩
  · intro T hT
    exact ⟨f T,(hf T hT).1,(pair T hT).1,(pair T hT).2⟩

lemma standard_family_no_intersection {L A : Finset (Finset α)}
    (hint : ∀ T ∈ L, ∀ U ∈ L, T ≠ U → (T ∩ U).card ≤ 1)
    (hA : ∀ M ∈ A, M.card = 2) {M P Q : Finset α}
    (hm : 2 ≤ M.card)
    (hP : P.card ≤ 1 ∨ P ∈ L ∨ P ∈ A)
    (hQ : Q.card ≤ 1 ∨ Q ∈ L ∨ Q ∈ A)
    (hPM : P ≠ M) (hQM : Q ≠ M) (heq : M = P ∩ Q) : False := by
  have mp : M ⊆ P := by rw [heq]; exact Finset.inter_subset_left
  have mq : M ⊆ Q := by rw [heq]; exact Finset.inter_subset_right
  have hp3 : 3 ≤ P.card := by
    have le := Finset.card_le_card mp
    by_contra bad
    have same : M = P := Finset.eq_of_subset_of_card_le mp (by omega)
    exact hPM same.symm
  have hq3 : 3 ≤ Q.card := by
    have le := Finset.card_le_card mq
    by_contra bad
    have same : M = Q := Finset.eq_of_subset_of_card_le mq (by omega)
    exact hQM same.symm
  have pl : P ∈ L := by
    rcases hP with h | h | h
    · omega
    · exact h
    · have := hA P h; omega
  have ql : Q ∈ L := by
    rcases hQ with h | h | h
    · omega
    · exact h
    · have := hA Q h; omega
  have ne : P ≠ Q := by
    intro e
    rw [e, Finset.inter_self] at heq
    exact hQM heq.symm
  have le := hint P pl Q ql ne
  rw [← heq] at le
  omega

end Rigidity

namespace DagRigidity
open DagTools Rigidity

variable {n : Nat} {D : Dag}

def bigFamily (n : Nat) (D : Dag) (P : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  (sup_big n D P).image (fun j => supp n D (n+j) ∩ P)

lemma mem_bigFamily (hS : Strict n D) {P M : Finset (Fin n)}
    (hM : 2 ≤ M.card) (hocc : sup_Occ n D P M) : M ∈ bigFamily n D P := by
  obtain ⟨j,hj,heq⟩ := sup_occ_big hS hM hocc
  exact Finset.mem_image.mpr ⟨j,hj,heq⟩

lemma first_parents (hS : Strict n D) {P M : Finset (Fin n)}
    (hM : 2 ≤ M.card) (hocc : sup_Occ n D P M) :
    ∃ A B : Finset (Fin n), sup_Occ n D P A ∧ sup_Occ n D P B ∧
      A ≠ M ∧ B ≠ M ∧ (M = A ∪ B ∨ M = A ∩ B) := by
  obtain ⟨w,hw⟩ := hocc
  obtain ⟨j,hj,_,heq,_,hmin,hcases⟩ := sem_first_mask hS P M hM w hw
  obtain ⟨ha,hb,_⟩ := hS j hj
  refine ⟨supp n D (opA D j) ∩ P, supp n D (opB D j) ∩ P,
    sup_occ_wire P _, sup_occ_wire P _, hmin _ ha, hmin _ hb, ?_⟩
  rcases hcases with ⟨ht,_,_⟩ | ⟨_,_,_,hu,_,_⟩
  · right
    rw [sem_supp_and hS hj ht] at heq
    rw [← heq]
    ext v
    simp only [Finset.mem_inter]
    tauto
  · exact Or.inl hu.symm

lemma family_rigid (hS : Strict n D) (P : Finset (Fin n))
    (hP : P.card ≤ 6) (L : Finset (Finset (Fin n)))
    (hLcard : L.card = 4) (hL : ∀ T ∈ L, T.card = 3 ∧ sup_Occ n D P T)
    (hint : ∀ T ∈ L, ∀ U ∈ L, T ≠ U → (T ∩ U).card ≤ 1)
    (hmerges : (merges n D (carrierT n D P)).card ≤ 8) :
    (bigFamily n D P).card = 8 ∧
    (∀ M ∈ bigFamily n D P \ L, M.card = 2 ∧ ∃ T ∈ L, M ⊆ T) ∧
    ∀ T ∈ L, ∃ M ∈ bigFamily n D P \ L, M.card = 2 ∧ M ⊆ T := by
  classical
  let F := bigFamily n D P
  let A := F \ L
  have hLF : L ⊆ F := by
    intro T hT
    exact mem_bigFamily hS (by have := (hL T hT).1; omega) (hL T hT).2
  have hFcard : F.card ≤ 8 := by
    have hsub : sup_big n D P ⊆ merges n D (carrierT n D P) := Finset.filter_subset _ _
    exact (Finset.card_image_le).trans ((Finset.card_le_card hsub).trans hmerges)
  have hsum : A.card + L.card = F.card := Finset.card_sdiff_add_card_eq_card hLF
  have hAcard : A.card ≤ 4 := by omega
  have hAS : ∀ M ∈ A, M ⊆ P := by
    intro M hM
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp (Finset.mem_sdiff.mp hM).1
    exact Finset.inter_subset_right
  have parent (T) (hT : T ∈ L) : ∃ A' B' : Finset (Fin n),
      (A'.card ≤ 1 ∨ A' ∈ L ∨ A' ∈ A) ∧ (B'.card ≤ 1 ∨ B' ∈ L ∨ B' ∈ A) ∧
      A' ≠ T ∧ B' ≠ T ∧ (T = A' ∪ B' ∨ T = A' ∩ B') := by
    obtain ⟨U,V,hu,hv,hut,hvt,hcases⟩ := first_parents hS
      (by have := (hL T hT).1; omega) (hL T hT).2
    have member (M) (hm : sup_Occ n D P M) : M.card ≤ 1 ∨ M ∈ L ∨ M ∈ A := by
      by_cases small : M.card ≤ 1
      · exact Or.inl small
      · right
        by_cases hmem : M ∈ L
        · exact Or.inl hmem
        · exact Or.inr (Finset.mem_sdiff.mpr ⟨mem_bigFamily hS (by omega) hm,hmem⟩)
    exact ⟨U,V,member U hu,member V hv,hut,hvt,hcases⟩
  have result := eight_family_rigid hP hLcard hAcard (fun T ht => (hL T ht).1) hint hAS parent
  refine ⟨?_,result.2⟩
  change F.card = 8
  omega

lemma all_merges_or (hS : Strict n D) (P : Finset (Fin n))
    (hP : P.card ≤ 6) (L : Finset (Finset (Fin n)))
    (hLcard : L.card = 4) (hL : ∀ T ∈ L, T.card = 3 ∧ sup_Occ n D P T)
    (hint : ∀ T ∈ L, ∀ U ∈ L, T ≠ U → (T ∩ U).card ≤ 1)
    (hmerges : (merges n D (carrierT n D P)).card ≤ 8) :
    ∀ j ∈ merges n D (carrierT n D P), tag D j = false := by
  classical
  obtain ⟨hF, hA, _⟩ := family_rigid hS P hP L hLcard hL hint hmerges
  have hsub : sup_big n D P ⊆ merges n D (carrierT n D P) := Finset.filter_subset _ _
  have hbig : (sup_big n D P).card = 8 := by
    have him : (bigFamily n D P).card ≤ (sup_big n D P).card := Finset.card_image_le
    have hs := Finset.card_le_card hsub
    omega
  have same : sup_big n D P = merges n D (carrierT n D P) :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  have hinj : Set.InjOn (fun j => supp n D (n+j) ∩ P) (sup_big n D P) :=
    Finset.card_image_iff.mp (by change (bigFamily n D P).card = _; omega)
  intro j hj
  have hjbig : j ∈ sup_big n D P := by rw [same]; exact hj
  have hjlt : j < D.length := (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)
  let M := supp n D (n+j) ∩ P
  have hM : 2 ≤ M.card := (Finset.mem_filter.mp hjbig).2
  have proper (w : Nat) (hw : w < n+j) : supp n D w ∩ P ≠ M := by
    intro he
    obtain ⟨k,hk,hkw,hmask,hmerge,_,_⟩ := sem_first_mask hS P M hM w he
    have hkbig : k ∈ sup_big n D P := Finset.mem_filter.mpr ⟨hmerge,by rw [hmask]; exact hM⟩
    have keq : k = j := hinj hkbig hjbig hmask
    omega
  have member (w : Nat) : (supp n D w ∩ P).card ≤ 1 ∨
      supp n D w ∩ P ∈ L ∨ supp n D w ∩ P ∈ bigFamily n D P \ L := by
    by_cases hs : (supp n D w ∩ P).card ≤ 1
    · exact Or.inl hs
    · right
      by_cases ht : supp n D w ∩ P ∈ L
      · exact Or.inl ht
      · exact Or.inr (Finset.mem_sdiff.mpr ⟨mem_bigFamily hS (by omega) (sup_occ_wire P w),ht⟩)
  cases ht : tag D j
  · rfl
  · exfalso
    have heq : M = (supp n D (opA D j) ∩ P) ∩ (supp n D (opB D j) ∩ P) := by
      dsimp [M]
      rw [sem_supp_and hS hjlt ht]
      ext v
      simp only [Finset.mem_inter]
      tauto
    exact standard_family_no_intersection hint (fun A ha => (hA A ha).1) hM
      (member _) (member _) (proper _ (hS j hjlt).1) (proper _ (hS j hjlt).2.1) heq

end DagRigidity


namespace ZeroFlow
open PEqualNP.Outside.L_meta_2590_aux.DagTools

variable {n : Nat} {D : Dag}

def boundaryOrGates (n : Nat) (D : Dag) (K : Finset Nat) : Finset Nat :=
  ((exitArcs n D K).image Prod.fst) ∪ merges n D K

lemma exit_fst_injective (K : Finset Nat)
    (he : ∀ e ∈ exitArcs n D K, tag D e.1 = false)
    (hclosed : ∀ j, j < D.length → tag D j = false →
      opA D j ∈ K → opB D j ∈ K → n+j ∈ K) :
    Set.InjOn (fun e : Nat × Bool => e.1) (exitArcs n D K) := by
  intro a ha b hb hab
  obtain ⟨j,s⟩ := a
  obtain ⟨k,t⟩ := b
  dsimp at hab
  subst k
  have ha' : (j,s) ∈ exitArcs n D K := ha
  have hb' : (j,t) ∈ exitArcs n D K := hb
  have ht := he (j,s) ha'
  have hsa : src D (j,s) ∈ K := (Finset.mem_filter.mp ha').2.1
  have hsb : src D (j,t) ∈ K := (Finset.mem_filter.mp hb').2.1
  have hout : n+j ∉ K := (Finset.mem_filter.mp ha').2.2
  have hjlt : j < D.length :=
    Finset.mem_range.mp (Finset.mem_product.mp (Finset.mem_filter.mp ha').1).1
  by_cases hst : s=t
  · subst t
    rfl
  · exfalso
    have both : opA D j ∈ K ∧ opB D j ∈ K := by
      cases s <;> cases t
      · exact False.elim (hst rfl)
      · simpa [src] using And.intro hsa hsb
      · simpa [src] using And.intro hsb hsa
      · exact False.elim (hst rfl)
    exact hout (hclosed j hjlt ht both.1 both.2)

lemma boundary_disjoint (K : Finset Nat) :
    Disjoint ((exitArcs n D K).image Prod.fst) (merges n D K) := by
  rw [Finset.disjoint_left]
  intro j hj hm
  obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hj
  have hout : n+e.1 ∉ K := (Finset.mem_filter.mp he).2.2
  exact hout (Finset.mem_filter.mp hm).2.1

lemma boundary_or_count (h : StrictLive n D) (K : Finset Nat)
    (hK : K ⊆ inner n D)
    (hpred : ∀ j, j < D.length → n+j ∈ K → opA D j ∈ K ∨ opB D j ∈ K)
    (hz : surplusOn D K=0)
    (he : ∀ e ∈ exitArcs n D K, tag D e.1=false)
    (hm : ∀ j ∈ merges n D K, tag D j=false)
    (hclosed : ∀ j, j < D.length → tag D j=false →
      opA D j ∈ K → opB D j ∈ K → n+j ∈ K) :
    (boundaryOrGates n D K).card = (sources n K).card ∧
      ∀ j ∈ boundaryOrGates n D K,
        j < D.length ∧ tag D j=false ∧ (opA D j ∈ K ∨ opB D j ∈ K) := by
  constructor
  · rw [boundaryOrGates, Finset.card_union_of_disjoint (boundary_disjoint K),
      Finset.card_image_of_injOn (exit_fst_injective K he hclosed), carrier_flow h K hK hpred, hz]
    omega
  · intro j hj
    rcases Finset.mem_union.mp hj with he' | hm'
    · obtain ⟨e,hearc,rfl⟩ := Finset.mem_image.mp he'
      have hjlt : e.1 < D.length :=
        Finset.mem_range.mp (Finset.mem_product.mp (Finset.mem_filter.mp hearc).1).1
      refine ⟨hjlt, he e hearc, ?_⟩
      have hs : src D e ∈ K := (Finset.mem_filter.mp hearc).2.1
      rcases e with ⟨j,s⟩
      cases s <;> simp_all [src]
    · exact ⟨Finset.mem_range.mp (Finset.mem_filter.mp hm').1, hm j hm',
        Or.inl (Finset.mem_filter.mp hm').2.2.1⟩

end ZeroFlow


namespace ZeroForest
open PEqualNP.Outside.L_meta_2590_aux.DagTools

noncomputable def zeroCone {α : Type} (n : Nat) (D : Dag) (I : Finset (Fin n))
    (rows : α → Fin n → Bool) : Finset Nat := by
  classical
  exact (Finset.range (n + D.length)).filter (fun w =>
    (∃ i ∈ I, Relation.ReflTransGen (sem_step n D) i.val w) ∧
      ∀ r, val D (rows r) w = false)

lemma mem_zeroCone {α : Type} {n : Nat} {D : Dag} {I : Finset (Fin n)}
    {rows : α → Fin n → Bool} {w : Nat} :
    w ∈ zeroCone n D I rows ↔ w < n + D.length ∧
      (∃ i ∈ I, Relation.ReflTransGen (sem_step n D) i.val w) ∧
        ∀ r, val D (rows r) w = false := by
  classical
  simp [zeroCone]

section Facts
variable {α : Type} {n : Nat} {G : Fin n → Fin n → Prop} {D : Dag}
  {I : Finset (Fin n)} {rows : α → Fin n → Bool}

lemma zeroCone_inner (positive : ∃ r, val D (rows r) (outW n D) = true) :
    zeroCone n D I rows ⊆ inner n D := by
  intro w hw
  obtain ⟨hlt, _, hz⟩ := mem_zeroCone.mp hw
  have hne : w ≠ outW n D := by
    intro he
    obtain ⟨r, hr⟩ := positive
    rw [← he, hz r] at hr
    exact Bool.false_ne_true hr
  apply sb_mem_inner.mpr
  unfold outW at hne
  omega

lemma zeroCone_sources (inputs : ∀ r i, i ∈ I → rows r i = false) :
    sources n (zeroCone n D I rows) = I.image Fin.val := by
  classical
  ext w
  constructor
  · intro hw
    obtain ⟨hk, hwlt⟩ := Finset.mem_filter.mp hw
    obtain ⟨_, ⟨i, hi, hp⟩, _⟩ := mem_zeroCone.mp hk
    rcases Relation.ReflTransGen.cases_tail hp with he | ⟨a, _, hs⟩
    · exact Finset.mem_image.mpr ⟨i, hi, he.symm⟩
    · have hn := hs.2.1
      omega
  · intro hw
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
    apply Finset.mem_filter.mpr
    refine ⟨mem_zeroCone.mpr ⟨by have := i.isLt; omega,
      ⟨i, hi, Relation.ReflTransGen.refl⟩, ?_⟩, i.isLt⟩
    intro r
    rw [val_input D (rows r) i.val i.isLt]
    exact inputs r i hi

lemma zeroCone_sources_card (inputs : ∀ r i, i ∈ I → rows r i = false) :
    (sources n (zeroCone n D I rows)).card = I.card := by
  rw [zeroCone_sources inputs, Finset.card_image_of_injective _ Fin.val_injective]

lemma zeroCone_surplus (hG : sem_Gr G) (h : StrictLive n D) (hc : sem_Comp n G D)
    (hz : Bzero n D = 0) (hi : I ⊆ ineligSet n D) :
    surplusOn D (zeroCone n D I rows) = 0 := by
  unfold surplusOn
  apply Finset.sum_eq_zero
  intro w hw
  obtain ⟨_, ⟨i, hiI, hp⟩, _⟩ := mem_zeroCone.mp hw
  have hf := sem_ineligible_reachable_fanout_le_one hG h hc hz (hi hiI) hp
  omega

lemma zeroCone_pred (hS : Strict n D)
    (copy : ∀ i ∈ I, ∀ j, j < D.length → ∀ s : Bool, tag D j = true →
      Relation.ReflTransGen (sem_step n D) i.val (src D (j, s)) →
        ∀ r, val D (rows r) (n + j) = val D (rows r) (src D (j, s))) :
    ∀ j, j < D.length → n + j ∈ zeroCone n D I rows →
      opA D j ∈ zeroCone n D I rows ∨ opB D j ∈ zeroCone n D I rows := by
  intro j hj hmem
  obtain ⟨_, ⟨i, hi, hp⟩, hz⟩ := mem_zeroCone.mp hmem
  rcases Relation.ReflTransGen.cases_tail hp with he | ⟨a, hpa, hs⟩
  · have := i.isLt
    omega
  · obtain ⟨j', s, hj', he, hsrc⟩ := sem_step_iff.mp hs
    have heq : j' = j := by omega
    subst j'
    rw [← hsrc] at hpa
    have hzsrc : ∀ r, val D (rows r) (src D (j,s)) = false := by
      intro r
      cases ht : tag D j
      · have hout := hz r
        rw [sem_val_gate_src hS _ hj s, ht, gop_false, Bool.or_eq_false_iff] at hout
        exact hout.1
      · rw [← copy i hi j hj s ht hpa r]
        exact hz r
    have hsMem : src D (j,s) ∈ zeroCone n D I rows :=
      mem_zeroCone.mpr ⟨lt_of_lt_of_le (sem_src_lt hS hj s) (Nat.add_le_add_left hj.le n),
        ⟨i, hi, hpa⟩, hzsrc⟩
    cases s
    · exact Or.inl (by simpa [src] using hsMem)
    · exact Or.inr (by simpa [src] using hsMem)

lemma zeroCone_or_closed (hS : Strict n D) {j : Nat} (hj : j < D.length)
    (ht : tag D j = false) (ha : opA D j ∈ zeroCone n D I rows)
    (hb : opB D j ∈ zeroCone n D I rows) : n + j ∈ zeroCone n D I rows := by
  obtain ⟨_, ⟨i, hi, hpa⟩, hza⟩ := mem_zeroCone.mp ha
  have hzb := (mem_zeroCone.mp hb).2.2
  refine mem_zeroCone.mpr ⟨Nat.add_lt_add_left hj n, ⟨i, hi, ?_⟩, ?_⟩
  · apply Relation.ReflTransGen.tail hpa
    simpa [src] using (sem_step_src (n := n) hj false)
  · intro r
    rw [val_gate hS _ j hj, ht, gop_false, hza r, hzb r]
    rfl

lemma zeroCone_exit_or (_hS : Strict n D)
    (copy : ∀ i ∈ I, ∀ j, j < D.length → ∀ s : Bool, tag D j = true →
      Relation.ReflTransGen (sem_step n D) i.val (src D (j, s)) →
        ∀ r, val D (rows r) (n + j) = val D (rows r) (src D (j, s)))
    {e : Nat × Bool} (he : e ∈ exitArcs n D (zeroCone n D I rows)) : tag D e.1 = false := by
  obtain ⟨ha, hsrc, hout⟩ := Finset.mem_filter.mp he
  have hj := Finset.mem_range.mp (Finset.mem_product.mp ha).1
  obtain ⟨_, ⟨i, hi, hp⟩, hzsrc⟩ := mem_zeroCone.mp hsrc
  cases ht : tag D e.1
  · rfl
  · exfalso
    apply hout
    refine mem_zeroCone.mpr ⟨Nat.add_lt_add_left hj n, ⟨i, hi, ?_⟩, ?_⟩
    · exact Relation.ReflTransGen.tail hp (sem_step_src hj e.2)
    · intro r
      rw [copy i hi e.1 hj e.2 ht hp r]
      exact hzsrc r

lemma zeroCone_merge_or (hG : sem_Gr G) (h : StrictLive n D) (hc : sem_Comp n G D)
    (hz : Bzero n D = 0) (hi : I ⊆ ineligSet n D)
    {j : Nat} (hj : j ∈ merges n D (zeroCone n D I rows)) : tag D j = false := by
  obtain ⟨hjlt, _, ha, hb⟩ := Finset.mem_filter.mp hj
  have hjlt := Finset.mem_range.mp hjlt
  obtain ⟨_, ⟨i, hiI, hpi⟩, _⟩ := mem_zeroCone.mp ha
  obtain ⟨_, ⟨k, hkI, hpk⟩, _⟩ := mem_zeroCone.mp hb
  exact sem_ineligible_join_or hG h hc hz (hi hiI) (hi hkI) hjlt false
    (by simpa [src] using hpi) (by simpa [src] using hpk)


lemma redundant_or_gates (hG : sem_Gr G) (h : StrictLive n D) (hc : sem_Comp n G D)
    (hz : Bzero n D = 0) (hi : I ⊆ ineligSet n D)
    (inputs : ∀ r i, i ∈ I → rows r i = false)
    (positive : ∃ r, val D (rows r) (outW n D) = true)
    (copy : ∀ i ∈ I, ∀ j, j < D.length → ∀ s : Bool, tag D j = true →
      Relation.ReflTransGen (sem_step n D) i.val (src D (j, s)) →
        ∀ r, val D (rows r) (n + j) = val D (rows r) (src D (j, s))) :
    ∃ T : Finset Nat, T.card = I.card ∧ ∀ j ∈ T,
      j < D.length ∧ tag D j = false ∧
        ∃ p, p < n + j ∧ ∀ r, val D (rows r) (n + j) = val D (rows r) p := by
  let K := zeroCone n D I rows
  have hK : K ⊆ inner n D := zeroCone_inner positive
  have hpred := zeroCone_pred h.1 copy
  have hsur := zeroCone_surplus hG h hc hz hi (rows := rows)
  have hexit : ∀ e ∈ exitArcs n D K, tag D e.1 = false :=
    fun e he => zeroCone_exit_or h.1 copy he
  have hmerge : ∀ j ∈ merges n D K, tag D j = false :=
    fun j hj => zeroCone_merge_or hG h hc hz hi hj
  have hclosed : ∀ j, j < D.length → tag D j = false →
      opA D j ∈ K → opB D j ∈ K → n + j ∈ K :=
    fun j hj ht ha hb => zeroCone_or_closed h.1 hj ht ha hb
  obtain ⟨hcard, hvalid⟩ := ZeroFlow.boundary_or_count h K hK hpred hsur hexit hmerge hclosed
  refine ⟨ZeroFlow.boundaryOrGates n D K, hcard.trans (zeroCone_sources_card inputs), ?_⟩
  intro j hj
  obtain ⟨hjlt, ht, ha | hb⟩ := hvalid j hj
  · refine ⟨hjlt, ht, opB D j, (h.1 j hjlt).2.1, ?_⟩
    intro r
    have hzA := (mem_zeroCone.mp ha).2.2 r
    rw [val_gate h.1 _ j hjlt, ht, gop_false, hzA]
    rfl
  · refine ⟨hjlt, ht, opA D j, (h.1 j hjlt).1, ?_⟩
    intro r
    have hzB := (mem_zeroCone.mp hb).2.2 r
    rw [val_gate h.1 _ j hjlt, ht, gop_false, hzB, Bool.or_false]

end Facts
end ZeroForest


namespace Neutral
open PEqualNP.Outside.L_meta_2590_aux.DagTools

lemma and_neutral_single {n : Nat} {D : Dag} (hS : Strict n D)
    {i a : Fin n} {g : Nat} (hg : g < D.length) (ht : tag D g = true)
    (s : Bool) (pure : supp n D (src D (g,s)) ⊆ {i}) (ha : a ≠ i) :
    val D (single a) (n+g) = val D (single a) (src D (g,s)) := by
  have hz : val D (single a) (src D (g,s)) = false := by
    apply Bool.eq_false_iff.mpr
    intro hv
    have hai := pure (mem_supp.mpr hv)
    exact ha (Finset.mem_singleton.mp hai)
  rw [sem_val_gate_src hS _ hg s, ht, gop_true, hz, Bool.false_and]

lemma neutral_ineligible_extended {n : Nat} {G : Fin n → Fin n → Prop} {D : Dag}
    (hG : sem_Gr G) (h : StrictLive n D) (hc : sem_Comp n G D)
    (I : Finset (Fin n)) (hin : I ⊆ ineligSet n D)
    {α : Type} (rows : α → Fin n → Bool)
    (good : ∀ i ∈ I, ∀ r, (∃ a, G i a ∧ rows r a = true) ∨
      ∃ a, a ≠ i ∧ rows r = single a) :
    ∃ T : Finset Nat, T.card = I.card ∧ ∀ g ∈ T,
      g < D.length ∧ tag D g = true ∧ ∃ p, p < n+g ∧
        ∀ r, val D (rows r) (n+g) = val D (rows r) p := by
  classical
  have hex : ∀ i : Fin n, ∃ e : Nat × Bool, i ∈ I →
      e.1 < D.length ∧ tag D e.1 = true ∧ supp n D (src D e) = {i} ∧
        ∀ a, G i a → a ∈ supp n D (src D (e.1,!e.2)) := by
    intro i
    by_cases hi : i ∈ I
    · obtain ⟨e, he, ht, hs, _, hn, _, _⟩ := sem_inelig_consumer hG h hc (hin hi)
      exact ⟨e, fun _ => ⟨he,ht,hs,hn⟩⟩
    · exact ⟨(0,false), fun hh => False.elim (hi hh)⟩
  choose e he using hex
  refine ⟨I.image (fun i => (e i).1), ?_, ?_⟩
  · apply Finset.card_image_of_injOn
    intro i hi j hj eq
    by_contra ne
    exact exit_gate_injective hG ne (he i hi).2.2.1 (he j hj).2.2.1 (he i hi).2.2.2 eq
  · intro g hg
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hg
    obtain ⟨hlt, ht, hpure, hn⟩ := he i hi
    refine ⟨hlt, ht, src D (e i), sem_src_lt h.1 hlt (e i).2, ?_⟩
    intro r
    rcases good i hi r with ⟨a, hia, hxa⟩ | ⟨a, hai, hx⟩
    · have htval : val D (rows r) (src D ((e i).1,!(e i).2)) = true :=
        sem_val_of_supp h.1 (hn a hia) hxa
      rw [sem_val_gate_src h.1 _ hlt (e i).2, ht, gop_true, htval, Bool.and_true]
    · rw [hx]
      exact and_neutral_single h.1 hlt ht (e i).2 (hpure ▸ Finset.Subset.refl _) hai

lemma chain_and_neutral_extended {n : Nat} {G : Fin n → Fin n → Prop} {D : Dag}
    (hG : sem_Gr G) (h : StrictLive n D) (hc : sem_Comp n G D)
    (hz : Bzero n D = 0) {i : Fin n} (hi : i ∈ ineligSet n D)
    {j : Nat} (hj : j < D.length) (s : Bool) (ht : tag D j = true)
    (path : Relation.ReflTransGen (sem_step n D) i.val (src D (j,s)))
    (x : Fin n → Bool) (good : (∃ a, G i a ∧ x a = true) ∨
      ∃ a, a ≠ i ∧ x = single a) :
    val D x (n+j) = val D x (src D (j,s)) := by
  have ch := sem_noempty_unique hG h hc hz hi path
  rcases good with hit | ⟨a, hai, rfl⟩
  · have hf : fanout D (src D (j,s)) = 1 := by
      have hlo := sem_step_fanout (sem_step_src (n := n) hj s)
      have hhi := sem_ineligible_reachable_fanout_le_one hG h hc hz hi path
      omega
    exact chain_and_neutral hG h.1 hc hj ht s ch hf x hit
  · exact and_neutral_single h.1 hj ht s
      (sem_dom_pure hG h.1 hc i _ (sem_chain_dom h.1 ch)) hai

end Neutral

namespace Thirteen
open PEqualNP.Outside.L_meta_2590_aux.DagTools
open PEqualNP.Outside.L_meta_2590_aux.Four
open PEqualNP.Outside.L_meta_2590_aux.Neutral

def masks (v : Fin 10) : Nat :=
  ([177,329,0,538,0,0,0,1068,2146,4180] : List Nat).getD v.val 0

def row (r : Fin 13) (v : Fin 10) : Bool := (masks v).testBit r.val

set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 1000000 in
lemma geometry :
    I.card = 4 ∧ (∀ r i, i ∈ I → row r i = false) ∧
    (sem_Edge Adj (row 0)) ∧
    (∀ i ∈ I, ∀ r, (∃ a, Adj i a ∧ row r a = true) ∨
      ∃ a, a ≠ i ∧ row r = single a) := by
  unfold row masks I sem_Edge Adj single
  decide +kernel

lemma eight_copies {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (hz : Bzero 10 D = 0) (hin : I ⊆ ineligSet 10 D) :
    ∃ A O : Finset Nat, A.card = 4 ∧ O.card = 4 ∧ Disjoint A O ∧
      (∀ j ∈ A, tag D j = true) ∧ (∀ j ∈ O, tag D j = false) ∧
      ∀ j ∈ A ∪ O, j < D.length ∧ ∃ p, p < 10+j ∧
        ∀ r : Fin 13, val D (row r) (10+j) = val D (row r) p := by
  classical
  obtain ⟨A, ha, hA⟩ := neutral_ineligible_extended graph_ok h hc I hin row geometry.2.2.2
  obtain ⟨O, ho, hO⟩ := ZeroForest.redundant_or_gates graph_ok h hc hz hin
    geometry.2.1 ⟨0,(hc _).mpr geometry.2.2.1⟩
    (fun i hi j hj s ht hp r => chain_and_neutral_extended graph_ok h hc hz
      (hin hi) hj s ht hp (row r) (geometry.2.2.2 i hi r))
  refine ⟨A,O,ha.trans geometry.1,ho.trans geometry.1,?_,
    fun j hj => (hA j hj).2.1,fun j hj => (hO j hj).2.1,?_⟩
  · apply Finset.disjoint_left.mpr
    intro j hjA hjO
    exact Bool.noConfusion ((hA j hjA).2.1.symm.trans (hO j hjO).2.1)
  · intro j hj
    rcases Finset.mem_union.mp hj with hj | hj
    · exact ⟨(hA j hj).1,(hA j hj).2.2⟩
    · exact ⟨(hO j hj).1,(hO j hj).2.2⟩


open PEqualNP.Outside.L_meta_2590_aux.SevenGeneral

def liftMask (x : Nat) : Nat :=
  x + if x = 49 then 128 else if x = 73 then 256 else if x = 26 then 512
    else if x = 44 then 1024 else if x = 98 then 2048 else if x = 84 then 4096 else 0

def caseRow (k : Fin 5) (r : Fin 13) (v : Fin 10) : Bool :=
  (liftMask (casesMasks k v)).testBit r.val

set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 1000000 in
lemma cases_geometry13 : ∀ k : Fin 5,
    (casesI k).card = 4 ∧ (∀ r i, i ∈ casesI k → caseRow k r i = false) ∧
    (sem_Edge Adj (caseRow k 0)) ∧
    (∀ i ∈ casesI k, ∀ r, (∃ a, Adj i a ∧ caseRow k r a = true) ∨
      ∃ a, a ≠ i ∧ caseRow k r = single a) := by
  unfold caseRow liftMask casesMasks casesI sem_Edge Adj single
  decide +kernel

lemma eight_copies_general {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (hz : Bzero 10 D = 0) (four : (ineligSet 10 D).card = 4) :
    ∃ k : Fin 5, casesI k = ineligSet 10 D ∧ ∃ A O : Finset Nat,
      A.card = 4 ∧ O.card = 4 ∧ Disjoint A O ∧
      (∀ j ∈ A, tag D j = true) ∧ (∀ j ∈ O, tag D j = false) ∧
      ∀ j ∈ A ∪ O, j < D.length ∧ ∃ p, p < 10+j ∧
        ∀ r : Fin 13, val D (caseRow k r) (10+j) = val D (caseRow k r) p := by
  classical
  have hind : ∀ a ∈ ineligSet 10 D, ∀ b ∈ ineligSet 10 D, ¬ Adj a b := by
    intro a ha b hb hab
    rcases sem_elig_cover graph_ok h hc hab with ea | eb
    · exact (sem_mem_inelig.mp ha) ea
    · exact (sem_mem_inelig.mp hb) eb
  obtain ⟨k, hk⟩ := classify_four (ineligSet 10 D) four hind
  have hin : casesI k ⊆ ineligSet 10 D := hk ▸ Finset.Subset.refl _
  have geo := cases_geometry13 k
  obtain ⟨A, ha, hA⟩ := neutral_ineligible_extended graph_ok h hc (casesI k) hin
    (caseRow k) geo.2.2.2
  obtain ⟨O, ho, hO⟩ := ZeroForest.redundant_or_gates graph_ok h hc hz hin
    geo.2.1 ⟨0,(hc _).mpr geo.2.2.1⟩
    (fun i hi j hj s ht hp r => chain_and_neutral_extended graph_ok h hc hz
      (hin hi) hj s ht hp (caseRow k r) (geo.2.2.2 i hi r))
  refine ⟨k,hk,A,O,ha.trans geo.1,ho.trans geo.1,?_,
    fun j hj => (hA j hj).2.1,fun j hj => (hO j hj).2.1,?_⟩
  · apply Finset.disjoint_left.mpr
    intro j hjA hjO
    exact Bool.noConfusion ((hA j hjA).2.1.symm.trans (hO j hjO).2.1)
  · intro j hj
    rcases Finset.mem_union.mp hj with hj | hj
    · exact ⟨(hA j hj).1,(hA j hj).2.2⟩
    · exact ⟨(hO j hj).1,(hO j hj).2.2⟩

end Thirteen

namespace GeneralFlow

open PEqualNP.Outside.L_meta_2590_aux.DagTools

variable {n : ℕ} {D : Dag}

lemma sources_add_surplus_le_exits_add_merges (h : StrictLive n D)
    (K : Finset ℕ) (hK : K ⊆ inner n D) :
    (sources n K).card + surplusOn D K ≤
      (exitArcs n D K).card + (merges n D K).card := by
  obtain ⟨hS, hL, -⟩ := h
  have hKlt : ∀ w ∈ K, w + 1 < n + D.length :=
    fun w hw => sb_mem_inner.mp (hK hw)
  have h1 : surplusOn D K + K.card =
      ((arcs D).filter (fun e => src D e ∈ K)).card := by
    rw [← sb_sum_fanout_eq hS,
      sb_surplus_add_card (fun w hw => hL w (hKlt w hw))]
  have h2 := Finset.card_filter_add_card_filter_not
    (s := (arcs D).filter (fun e => src D e ∈ K))
    (fun e : ℕ × Bool => n + e.1 ∈ K)
  rw [Finset.filter_filter, Finset.filter_filter] at h2
  have h3 : ((arcs D).filter (fun e => src D e ∈ K ∧ n + e.1 ∈ K)).card ≤
      ((Finset.range D.length).filter (fun j => n + j ∈ K)).card +
        (merges n D K).card := by
    rw [sb_card_arcs_filter, merges, Finset.card_filter, Finset.card_filter,
      ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun j hj => ?_)
    rw [sb_src_false, sb_src_true]
    by_cases hj2 : n + j ∈ K <;>
      by_cases ha : opA D j ∈ K <;>
        by_cases hb : opB D j ∈ K <;> simp_all
  have h4 : K.card = (sources n K).card +
      ((Finset.range D.length).filter (fun j => n + j ∈ K)).card := by
    rw [← Finset.card_filter_add_card_filter_not (s := K) (fun w => w < n), sources]
    congr 1
    have himg : K.filter (fun w => ¬ w < n) =
        ((Finset.range D.length).filter (fun j => n + j ∈ K)).image
          (fun j => n + j) := by
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

lemma sources_le_exits_add_merges (h : StrictLive n D)
    (K : Finset ℕ) (hK : K ⊆ inner n D) :
    (sources n K).card ≤ (exitArcs n D K).card + (merges n D K).card := by
  have := sources_add_surplus_le_exits_add_merges h K hK
  omega

end GeneralFlow

namespace GeneralZero
open PEqualNP.Outside.L_meta_2590_aux.DagTools

noncomputable def zeroWires {α : Type} (n : Nat) (D : Dag)
    (rows : α → Fin n → Bool) : Finset Nat := by
  classical
  exact (Finset.range (n + D.length)).filter (fun w => ∀ r, val D (rows r) w = false)

lemma mem_zeroWires {α : Type} {n : Nat} {D : Dag} {rows : α → Fin n → Bool} {w : Nat} :
    w ∈ zeroWires n D rows ↔ w < n + D.length ∧ ∀ r, val D (rows r) w = false := by
  classical
  simp [zeroWires]

section Facts
variable {α : Type} {n : Nat} {D : Dag} {rows : α → Fin n → Bool}

lemma zeroWires_inner (positive : ∃ r, val D (rows r) (outW n D) = true) :
    zeroWires n D rows ⊆ inner n D := by
  intro w hw
  obtain ⟨hlt, hz⟩ := mem_zeroWires.mp hw
  have hne : w ≠ outW n D := by
    intro he
    obtain ⟨r, hr⟩ := positive
    rw [← he, hz r] at hr
    exact Bool.false_ne_true hr
  apply sb_mem_inner.mpr
  unfold outW at hne
  omega

lemma zeroWires_sources_ge (I : Finset (Fin n))
    (inputs : ∀ r i, i ∈ I → rows r i = false) :
    I.card ≤ (sources n (zeroWires n D rows)).card := by
  have hsub : I.image Fin.val ⊆ sources n (zeroWires n D rows) := by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
    apply Finset.mem_filter.mpr
    refine ⟨mem_zeroWires.mpr ⟨by have := i.isLt; omega, ?_⟩, i.isLt⟩
    intro r
    rw [val_input D (rows r) i.val i.isLt]
    exact inputs r i hi
  have hc := Finset.card_le_card hsub
  rwa [Finset.card_image_of_injective _ Fin.val_injective] at hc

lemma zeroWires_closed (hS : Strict n D) {j : Nat} (hj : j < D.length)
    (ha : opA D j ∈ zeroWires n D rows) (hb : opB D j ∈ zeroWires n D rows) :
    n + j ∈ zeroWires n D rows := by
  refine mem_zeroWires.mpr ⟨Nat.add_lt_add_left hj n, ?_⟩
  intro r
  rw [val_gate hS _ j hj, (mem_zeroWires.mp ha).2 r, (mem_zeroWires.mp hb).2 r]
  cases tag D j <;> rfl

lemma zeroWires_exit_or (hS : Strict n D) {e : Nat × Bool}
    (he : e ∈ exitArcs n D (zeroWires n D rows)) : tag D e.1 = false := by
  obtain ⟨ha, hsrc, hout⟩ := Finset.mem_filter.mp he
  have hj := Finset.mem_range.mp (Finset.mem_product.mp ha).1
  have hzsrc := (mem_zeroWires.mp hsrc).2
  cases ht : tag D e.1
  · rfl
  · exfalso
    apply hout
    refine mem_zeroWires.mpr ⟨Nat.add_lt_add_left hj n, ?_⟩
    intro r
    rw [sem_val_gate_src hS _ hj e.2, ht, gop_true, hzsrc r]
    rfl

lemma zeroWires_boundary_card (hS : Strict n D) :
    (ZeroFlow.boundaryOrGates n D (zeroWires n D rows)).card =
      (exitArcs n D (zeroWires n D rows)).card + (merges n D (zeroWires n D rows)).card := by
  rw [ZeroFlow.boundaryOrGates,
    Finset.card_union_of_disjoint (ZeroFlow.boundary_disjoint _),
    Finset.card_image_of_injOn]
  exact ZeroFlow.exit_fst_injective _ (fun e he => zeroWires_exit_or hS he)
    (fun j hj _ ha hb => zeroWires_closed hS hj ha hb)

lemma zeroWires_boundary_copy (hS : Strict n D) {j : Nat}
    (hj : j ∈ ZeroFlow.boundaryOrGates n D (zeroWires n D rows)) :
    j < D.length ∧
      (tag D j = true → ∀ r, val D (rows r) (opA D j) = false ∧
        val D (rows r) (opB D j) = false) ∧
      ∃ p, p < n + j ∧ ∀ r, val D (rows r) (n + j) = val D (rows r) p := by
  rcases Finset.mem_union.mp hj with hexit | hmerge
  · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hexit
    have ht := zeroWires_exit_or hS he
    obtain ⟨ha, hsrc, _⟩ := Finset.mem_filter.mp he
    have hjlt := Finset.mem_range.mp (Finset.mem_product.mp ha).1
    refine ⟨hjlt, ?_, src D (e.1, !e.2), sem_src_lt hS hjlt (!e.2), ?_⟩
    · intro htrue
      rw [ht] at htrue
      exact False.elim (Bool.false_ne_true htrue)
    · intro r
      rw [sem_val_gate_src hS _ hjlt e.2, ht, gop_false, (mem_zeroWires.mp hsrc).2 r]
      rfl
  · obtain ⟨hjl, hout, ha, hb⟩ := Finset.mem_filter.mp hmerge
    have hjlt := Finset.mem_range.mp hjl
    refine ⟨hjlt, fun _ r => ⟨(mem_zeroWires.mp ha).2 r, (mem_zeroWires.mp hb).2 r⟩,
      opA D j, (hS j hjlt).1, ?_⟩
    intro r
    rw [(mem_zeroWires.mp hout).2 r, (mem_zeroWires.mp ha).2 r]


lemma zero_rows_copy_gates (h : StrictLive n D) (I : Finset (Fin n))
    (inputs : ∀ r i, i ∈ I → rows r i = false)
    (positive : ∃ r, val D (rows r) (outW n D) = true) :
    ∃ T : Finset Nat, I.card + surplusOn D (zeroWires n D rows) ≤ T.card ∧
      ∀ j ∈ T, j < D.length ∧
        (tag D j = true → ∀ r, val D (rows r) (opA D j) = false ∧
          val D (rows r) (opB D j) = false) ∧
        ∃ p, p < n + j ∧ ∀ r, val D (rows r) (n + j) = val D (rows r) p := by
  refine ⟨ZeroFlow.boundaryOrGates n D (zeroWires n D rows), ?_, ?_⟩
  · rw [zeroWires_boundary_card h.1]
    exact (Nat.add_le_add_right (zeroWires_sources_ge I inputs) _).trans
      (GeneralFlow.sources_add_surplus_le_exits_add_merges h _ (zeroWires_inner positive))
  · intro j hj
    exact zeroWires_boundary_copy h.1 hj


lemma zero_rows_exact_copy_gates (h : StrictLive n D) (I : Finset (Fin n))
    (inputs : ∀ r i, i ∈ I → rows r i = false)
    (positive : ∃ r, val D (rows r) (outW n D) = true) :
    ∃ T : Finset Nat, T.card = I.card ∧
      ∀ j ∈ T, j < D.length ∧
        (tag D j = true → ∀ r, val D (rows r) (opA D j) = false ∧
          val D (rows r) (opB D j) = false) ∧
        ∃ p, p < n + j ∧ ∀ r, val D (rows r) (n + j) = val D (rows r) p := by
  obtain ⟨T, hcard, ht⟩ := zero_rows_copy_gates h I inputs positive
  have hbound : I.card ≤ T.card := by omega
  obtain ⟨U, hu, huc⟩ := Finset.exists_subset_card_eq hbound
  exact ⟨U, huc, fun j hj => ht j (hu hj)⟩

lemma zero_boundary_disjoint_active_ands (hS : Strict n D) (A : Finset Nat)
    (ha : ∀ j ∈ A, tag D j = true ∧
      ∃ r, val D (rows r) (opA D j) = true ∨ val D (rows r) (opB D j) = true) :
    Disjoint A (ZeroFlow.boundaryOrGates n D (zeroWires n D rows)) := by
  rw [Finset.disjoint_left]
  intro j hjA hjB
  obtain ⟨htag, r, hr⟩ := ha j hjA
  have hz := (zeroWires_boundary_copy hS hjB).2.1 htag r
  rcases hr with hleft | hright
  · exact Bool.false_ne_true (hz.1.symm.trans hleft)
  · exact Bool.false_ne_true (hz.2.symm.trans hright)

end Facts
end GeneralZero

namespace EightGeneral
open PEqualNP.Outside.L_meta_2590_aux.DagTools
open PEqualNP.Outside.L_meta_2590_aux.Neutral

lemma neutral_ineligible_active {n : Nat} {G : Fin n → Fin n → Prop} {D : Dag}
    (hG : sem_Gr G) (h : StrictLive n D) (hc : sem_Comp n G D)
    (I : Finset (Fin n)) (hin : I ⊆ ineligSet n D)
    {α : Type} (rows : α → Fin n → Bool)
    (good : ∀ i ∈ I, ∀ r, (∃ a, G i a ∧ rows r a = true) ∨
      ∃ a, a ≠ i ∧ rows r = single a)
    (active : ∀ i ∈ I, ∃ r a, G i a ∧ rows r a = true) :
    ∃ T : Finset Nat, T.card = I.card ∧ ∀ g ∈ T,
      g < D.length ∧ tag D g = true ∧
        (∃ r, val D (rows r) (opA D g) = true ∨ val D (rows r) (opB D g) = true) ∧
        ∃ p, p < n + g ∧ ∀ r, val D (rows r) (n + g) = val D (rows r) p := by
  classical
  have hex : ∀ i : Fin n, ∃ e : Nat × Bool, i ∈ I →
      e.1 < D.length ∧ tag D e.1 = true ∧ supp n D (src D e) = {i} ∧
        ∀ a, G i a → a ∈ supp n D (src D (e.1, !e.2)) := by
    intro i
    by_cases hi : i ∈ I
    · obtain ⟨e, he, ht, hs, _, hn, _, _⟩ := sem_inelig_consumer hG h hc (hin hi)
      exact ⟨e, fun _ => ⟨he, ht, hs, hn⟩⟩
    · exact ⟨(0, false), fun hh => False.elim (hi hh)⟩
  choose e he using hex
  refine ⟨I.image (fun i => (e i).1), ?_, ?_⟩
  · apply Finset.card_image_of_injOn
    intro i hi j hj eq
    by_contra ne
    exact exit_gate_injective hG ne (he i hi).2.2.1 (he j hj).2.2.1 (he i hi).2.2.2 eq
  · intro g hg
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hg
    obtain ⟨hlt, ht, hpure, hn⟩ := he i hi
    refine ⟨hlt, ht, ?_, src D (e i), sem_src_lt h.1 hlt (e i).2, ?_⟩
    · obtain ⟨r, a, hia, hxa⟩ := active i hi
      have hval : val D (rows r) (src D ((e i).1, !(e i).2)) = true :=
        sem_val_of_supp h.1 (hn a hia) hxa
      refine ⟨r, ?_⟩
      cases hs : (e i).2
      · right
        simpa [src, hs] using hval
      · left
        simpa [src, hs] using hval
    · intro r
      rcases good i hi r with ⟨a, hia, hxa⟩ | ⟨a, hai, hx⟩
      · have htval : val D (rows r) (src D ((e i).1, !(e i).2)) = true :=
          sem_val_of_supp h.1 (hn a hia) hxa
        rw [sem_val_gate_src h.1 _ hlt (e i).2, ht, gop_true, htval, Bool.and_true]
      · rw [hx]
        exact and_neutral_single h.1 hlt ht (e i).2 (hpure ▸ Finset.Subset.refl _) hai

lemma twice_ineligible_copy_gates {n : Nat} {G : Fin n → Fin n → Prop} {D : Dag}
    (hG : sem_Gr G) (h : StrictLive n D) (hc : sem_Comp n G D)
    (I : Finset (Fin n)) (hin : I ⊆ ineligSet n D)
    {α : Type} (rows : α → Fin n → Bool)
    (good : ∀ i ∈ I, ∀ r, (∃ a, G i a ∧ rows r a = true) ∨
      ∃ a, a ≠ i ∧ rows r = single a)
    (active : ∀ i ∈ I, ∃ r a, G i a ∧ rows r a = true)
    (inputs : ∀ r i, i ∈ I → rows r i = false)
    (positive : ∃ r, val D (rows r) (outW n D) = true) :
    ∃ T : Finset Nat, T.card = 2 * I.card ∧ ∀ j ∈ T,
      j < D.length ∧ ∃ p, p < n + j ∧ ∀ r, val D (rows r) (n + j) = val D (rows r) p := by
  obtain ⟨A, ha, hA⟩ := neutral_ineligible_active hG h hc I hin rows good active
  obtain ⟨Z, hz, hZ⟩ := GeneralZero.zero_rows_exact_copy_gates h I inputs positive
  have hd : Disjoint A Z := by
    rw [Finset.disjoint_left]
    intro j hjA hjZ
    obtain ⟨_, ht, ⟨r, hleft | hright⟩, _⟩ := hA j hjA
    · have hz := (hZ j hjZ).2.1 ht r
      exact Bool.false_ne_true (hz.1.symm.trans hleft)
    · have hz := (hZ j hjZ).2.1 ht r
      exact Bool.false_ne_true (hz.2.symm.trans hright)
  refine ⟨A ∪ Z, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hd, ha, hz]
    omega
  · intro j hj
    rcases Finset.mem_union.mp hj with hj | hj
    · exact ⟨(hA j hj).1, (hA j hj).2.2.2⟩
    · exact ⟨(hZ j hj).1, (hZ j hj).2.2⟩

open PEqualNP.Outside.L_meta_2590_aux.Four
open PEqualNP.Outside.L_meta_2590_aux.SevenGeneral
open PEqualNP.Outside.L_meta_2590_aux.Thirteen

set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 1000000 in
lemma cases_hits_zero : ∀ k : Fin 5, ∀ i ∈ casesI k,
    ∃ a, Adj i a ∧ caseRow k 0 a = true := by
  unfold Adj caseRow liftMask casesMasks casesI
  decide +kernel

lemma eight_copies_without_bzero {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (four : (ineligSet 10 D).card = 4) :
    ∃ k : Fin 5, casesI k = ineligSet 10 D ∧ ∃ T : Finset Nat,
      T.card = 8 ∧ ∀ j ∈ T, j < D.length ∧ ∃ p, p < 10 + j ∧
        ∀ r : Fin 13, val D (caseRow k r) (10 + j) = val D (caseRow k r) p := by
  have hind : ∀ a ∈ ineligSet 10 D, ∀ b ∈ ineligSet 10 D, ¬ Adj a b := by
    intro a ha b hb hab
    rcases sem_elig_cover graph_ok h hc hab with ea | eb
    · exact (sem_mem_inelig.mp ha) ea
    · exact (sem_mem_inelig.mp hb) eb
  obtain ⟨k, hk⟩ := classify_four (ineligSet 10 D) four hind
  have hin : casesI k ⊆ ineligSet 10 D := hk ▸ Finset.Subset.refl _
  have geo := cases_geometry13 k
  obtain ⟨T, ht, hT⟩ := twice_ineligible_copy_gates graph_ok h hc (casesI k) hin
    (caseRow k) geo.2.2.2 (fun i hi => ⟨0, cases_hits_zero k i hi⟩)
    geo.2.1 ⟨0, (hc _).mpr geo.2.2.1⟩
  exact ⟨k, hk, T, by simpa [geo.1] using ht, hT⟩

end EightGeneral


namespace Compression

variable {α : Type}

def meet (a b : α → Bool) : α → Bool := fun x => a x && b x

def join (a b : α → Bool) : α → Bool := fun x => a x || b x

def Step (p : List (α → Bool)) (w : α → Bool) : Prop :=
  ∃ a ∈ p, ∃ b ∈ p, w = meet a b ∨ w = join a b

def Trace (p gs : List (α → Bool)) : Prop :=
  List.rec (motive := fun _ => List (α → Bool) → Prop) (fun _ => True)
    (fun w _ rec q => Step q w ∧ rec (q ++ [w])) gs p

lemma step_mono {p q : List (α → Bool)} {w : α → Bool}
    (hpq : p ⊆ q) (hw : Step p w) : Step q w := by
  obtain ⟨a, ha, b, hb, hab⟩ := hw
  exact ⟨a, hpq ha, b, hpq hb, hab⟩

lemma compress_indexed {p q gs : List (α → Bool)}
    (ht : Trace p gs) (hpq : p ⊆ q) (mark : Fin gs.length → Bool)
    (hd : ∀ j : Fin gs.length, mark j = true → gs.get j ∈ q ++ gs.take j.val) :
    ∃ hs, Trace q hs ∧ p ++ gs ⊆ q ++ hs ∧
      hs.length + (∑ j : Fin gs.length, if mark j then 1 else 0) = gs.length := by
  induction gs generalizing p q with
  | nil =>
      refine ⟨[], trivial, ?_, ?_⟩
      · simpa using hpq
      · simp
  | cons w gs ih =>
      let tailMark : Fin gs.length → Bool := fun j => mark j.succ
      have hsum : (∑ j : Fin (w :: gs).length, if mark j then 1 else 0) =
          (if mark 0 then 1 else 0) + ∑ j : Fin gs.length, if tailMark j then 1 else 0 := by
        exact Fin.sum_univ_succ _
      by_cases hm : mark 0 = true
      · have hwq : w ∈ q := by simpa using hd 0 hm
        have hbase : p ++ [w] ⊆ q := by
          intro a ha
          rcases List.mem_append.mp ha with ha | ha
          · exact hpq ha
          · simpa only [List.mem_singleton.mp ha] using hwq
        have hdelete : ∀ j : Fin gs.length, tailMark j = true →
            gs.get j ∈ q ++ gs.take j.val := by
          intro j hj
          have hjmem : gs.get j ∈ q ++ w :: gs.take j.val := by
            simpa using hd j.succ hj
          rcases List.mem_append.mp hjmem with hq | hg
          · exact List.mem_append_left _ hq
          · rcases List.mem_cons.mp hg with heq | htail
            · exact List.mem_append_left _ (heq ▸ hwq)
            · exact List.mem_append_right _ htail
        obtain ⟨hs, htrace, hcover, hlen⟩ := ih ht.2 hbase tailMark hdelete
        refine ⟨hs, htrace, ?_, ?_⟩
        · simpa [List.append_assoc] using hcover
        · rw [hsum, hm]
          simp only [↓reduceIte, List.length_cons]
          omega
      · have hmfalse : mark 0 = false := Bool.eq_false_iff.mpr hm
        have hbase : p ++ [w] ⊆ q ++ [w] := by
          intro a ha
          rcases List.mem_append.mp ha with ha | ha
          · exact List.mem_append_left _ (hpq ha)
          · exact List.mem_append_right _ ha
        have hdelete : ∀ j : Fin gs.length, tailMark j = true →
            gs.get j ∈ (q ++ [w]) ++ gs.take j.val := by
          intro j hj
          simpa [List.append_assoc] using hd j.succ hj
        obtain ⟨hs, htrace, hcover, hlen⟩ := ih ht.2 hbase tailMark hdelete
        refine ⟨w :: hs, ⟨step_mono hpq ht.1, htrace⟩, ?_, ?_⟩
        · simpa [List.append_assoc] using hcover
        · rw [hsum, hmfalse]
          simp only [Bool.false_eq_true, ↓reduceIte, zero_add, List.length_cons]
          omega

lemma compress_marked {p q gs : List (α → Bool)}
    (ht : Trace p gs) (hpq : p ⊆ q) (marked : Finset (Fin gs.length))
    (hd : ∀ j ∈ marked, gs.get j ∈ q ++ gs.take j.val) :
    ∃ hs, Trace q hs ∧ p ++ gs ⊆ q ++ hs ∧
      hs.length + marked.card = gs.length := by
  classical
  obtain ⟨hs, htrace, hcover, hlen⟩ :=
    compress_indexed ht hpq (fun j => decide (j ∈ marked))
      (fun j hj => hd j (of_decide_eq_true hj))
  refine ⟨hs, htrace, hcover, ?_⟩
  simpa using hlen

lemma compress_free {p freeBase gs : List (α → Bool)}
    (ht : Trace p gs) (marked : Finset (Fin gs.length))
    (hd : ∀ j ∈ marked, gs.get j ∈ (p ++ freeBase) ++ gs.take j.val) :
    ∃ hs, Trace (p ++ freeBase) hs ∧ p ++ gs ⊆ (p ++ freeBase) ++ hs ∧
      hs.length + marked.card = gs.length := by
  exact compress_marked ht (fun _ h => List.mem_append_left _ h) marked hd

lemma compress_free_output {p freeBase gs : List (α → Bool)}
    (ht : Trace p gs) (marked : Finset (Fin gs.length))
    (hd : ∀ j ∈ marked, gs.get j ∈ (p ++ freeBase) ++ gs.take j.val)
    (f : α → Bool) (hf : f ∈ p ++ gs) :
    ∃ hs, Trace (p ++ freeBase) hs ∧ f ∈ (p ++ freeBase) ++ hs ∧
      hs.length + marked.card = gs.length := by
  obtain ⟨hs, htrace, hcover, hlen⟩ := compress_free ht marked hd
  exact ⟨hs, htrace, hcover hf, hlen⟩

lemma compress_two_families {p freeBase gs : List (α → Bool)}
    (ht : Trace p gs) (freeMarks bypassMarks : Finset (Fin gs.length))
    (hdisjoint : Disjoint freeMarks bypassMarks)
    (hfree : ∀ j ∈ freeMarks, gs.get j ∈ p ++ freeBase)
    (hbypass : ∀ j ∈ bypassMarks, gs.get j ∈ p ++ gs.take j.val) :
    ∃ hs, Trace (p ++ freeBase) hs ∧ p ++ gs ⊆ (p ++ freeBase) ++ hs ∧
      hs.length + freeMarks.card + bypassMarks.card = gs.length := by
  classical
  have hd : ∀ j ∈ freeMarks ∪ bypassMarks,
      gs.get j ∈ (p ++ freeBase) ++ gs.take j.val := by
    intro j hj
    rcases Finset.mem_union.mp hj with hj | hj
    · exact List.mem_append_left _ (hfree j hj)
    · rcases List.mem_append.mp (hbypass j hj) with hp | hg
      · exact List.mem_append_left _ (List.mem_append_left _ hp)
      · exact List.mem_append_right _ hg
  obtain ⟨hs, htrace, hcover, hlen⟩ := compress_free ht (freeMarks ∪ bypassMarks) hd
  refine ⟨hs, htrace, hcover, ?_⟩
  simpa [Finset.card_union_of_disjoint hdisjoint, Nat.add_assoc] using hlen

lemma lower_bound_after_compression {p freeBase gs : List (α → Bool)}
    (ht : Trace p gs) (marked : Finset (Fin gs.length))
    (hd : ∀ j ∈ marked, gs.get j ∈ (p ++ freeBase) ++ gs.take j.val)
    (f : α → Bool) (hf : f ∈ p ++ gs) (lower : ℕ)
    (hlower : ∀ hs, Trace (p ++ freeBase) hs → f ∈ (p ++ freeBase) ++ hs →
      lower ≤ hs.length) :
    lower + marked.card ≤ gs.length := by
  obtain ⟨hs, htrace, hout, hlen⟩ := compress_free_output ht marked hd f hf
  have := hlower hs htrace hout
  omega

end Compression


namespace Compression
open PEqualNP.Outside.L_meta_2590_aux.DagTools

lemma trace_of_steps {α : Type} {p gs : List (α → Bool)}
    (steps : ∀ j : Fin gs.length, Step (p ++ gs.take j.val) (gs.get j)) : Trace p gs := by
  induction gs generalizing p with
  | nil => trivial
  | cons w gs ih =>
    refine ⟨?_,ih ?_⟩
    · simpa using steps 0
    · intro j
      simpa [List.append_assoc] using steps j.succ

variable {α : Type}
def wireValue (D : Dag) (rows : α → Fin n → Bool) (w : Nat) : α → Bool :=
  fun r => val D (rows r) w

def inputValues (n : Nat) (D : Dag) (rows : α → Fin n → Bool) : List (α → Bool) :=
  (List.range n).map (wireValue D rows)

def gateValues (n : Nat) (D : Dag) (rows : α → Fin n → Bool) : List (α → Bool) :=
  (List.range D.length).map (fun j => wireValue D rows (n+j))

lemma wire_mem_prefix (n : Nat) (D : Dag) (rows : α → Fin n → Bool)
    {k w : Nat} (hk : k ≤ D.length) (hw : w < n+k) :
    wireValue D rows w ∈ inputValues n D rows ++ (gateValues n D rows).take k := by
  by_cases hinput : w < n
  · apply List.mem_append_left
    exact List.mem_map.mpr ⟨w,List.mem_range.mpr hinput,rfl⟩
  · apply List.mem_append_right
    simp only [gateValues,← List.map_take,List.take_range]
    apply List.mem_map.mpr
    refine ⟨w-n,List.mem_range.mpr ?_,?_⟩
    · omega
    · congr 1
      omega

lemma dag_trace (n : Nat) {D : Dag} (h : Strict n D) (rows : α → Fin n → Bool) :
    Trace (inputValues n D rows) (gateValues n D rows) := by
  apply trace_of_steps
  intro j
  have hj : j.val < D.length := by simpa [gateValues] using j.isLt
  have ha := wire_mem_prefix n D rows (Nat.le_of_lt hj) (h j.val hj).1
  have hb := wire_mem_prefix n D rows (Nat.le_of_lt hj) (h j.val hj).2.1
  refine ⟨wireValue D rows (opA D j.val),ha,wireValue D rows (opB D j.val),hb,?_⟩
  have he : (gateValues n D rows).get j = wireValue D rows (n+j.val) := by
    change ((List.range D.length).map (fun t => wireValue D rows (n+t)))[j.val] = _
    simp only [List.getElem_map,List.getElem_range]
  rw [he]
  cases ht : tag D j.val
  · right
    funext r
    exact (val_gate h (rows r) j.val hj).trans (by simp [ht,gop_false,join,wireValue])
  · left
    funext r
    exact (val_gate h (rows r) j.val hj).trans (by simp [ht,gop_true,meet,wireValue])

lemma compress_dag_copies (n : Nat) {D : Dag} (h : Strict n D) (rows : α → Fin n → Bool)
    (T : Finset Nat) (valid : ∀ j ∈ T, j < D.length)
    (copy : ∀ j ∈ T, ∃ p, p < n+j ∧
      ∀ r, val D (rows r) (n+j) = val D (rows r) p) :
    ∃ gs, Trace (inputValues n D rows) gs ∧
      (∀ w, w < n+D.length → wireValue D rows w ∈ inputValues n D rows ++ gs) ∧
      gs.length + T.card = D.length := by
  classical
  let M : Finset (Fin (gateValues n D rows).length) :=
    T.attach.image (fun j => ⟨j.val,by simpa [gateValues] using valid j.val j.property⟩)
  have hM : M.card = T.card := by
    rw [Finset.card_image_of_injective]
    · exact Finset.card_attach
    · intro a b hab
      exact Subtype.ext (congrArg Fin.val hab)
  have hcopy : ∀ j ∈ M, (gateValues n D rows).get j ∈
      inputValues n D rows ++ (gateValues n D rows).take j.val := by
    intro j hj
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨p,hp,he⟩ := copy a.val a.property
    have hv : wireValue D rows (n+a.val) = wireValue D rows p := funext he
    simp only [gateValues,List.get_eq_getElem,List.getElem_map,List.getElem_range]
    rw [hv]
    exact wire_mem_prefix n D rows (Nat.le_of_lt (valid a.val a.property)) hp
  obtain ⟨gs,htr,hcov,hlen⟩ := compress_marked (dag_trace n h rows)
    (fun _ hh => hh) M hcopy
  refine ⟨gs,htr,?_,?_⟩
  · intro w hw
    apply hcov
    have ht : (gateValues n D rows).take D.length = gateValues n D rows :=
      List.take_of_length_le (by simp [gateValues])
    simpa only [ht] using wire_mem_prefix n D rows (Nat.le_refl _) hw
  · rw [hM] at hlen
    simpa only [gateValues,List.length_map,List.length_range] using hlen

end Compression


namespace Thirteen
open PEqualNP.Outside.L_meta_2590_aux.DagTools
open PEqualNP.Outside.L_meta_2590_aux.Four
open PEqualNP.Outside.L_meta_2590_aux.SevenGeneral
open PEqualNP.Outside.L_meta_2590_aux.Compression

lemma compressed_eleven {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (four : (ineligSet 10 D).card = 4) (size : D.length ≤ 19) :
    ∃ k : Fin 5, casesI k = ineligSet 10 D ∧ ∃ gs,
      Trace (inputValues 10 D (caseRow k)) gs ∧
      (∀ w, w < 10+D.length → wireValue D (caseRow k) w ∈
        inputValues 10 D (caseRow k) ++ gs) ∧ gs.length ≤ 11 := by
  obtain ⟨k,hk,T,hcard,hT⟩ := EightGeneral.eight_copies_without_bzero h hc four
  obtain ⟨gs,htr,hcover,hlen⟩ := compress_dag_copies 10 h.1 (caseRow k) T
    (fun j hj => (hT j hj).1) (fun j hj => (hT j hj).2)
  exact ⟨k,hk,gs,htr,hcover,by omega⟩

end Thirteen

namespace EightSupport
open PEqualNP.Outside.L_meta_2590_aux.DagTools
open PEqualNP.Outside.L_meta_2590_aux.Neutral

lemma neutral_ineligible_active_zero {n : Nat} {G : Fin n → Fin n → Prop} {D : Dag}
    (hG : sem_Gr G) (h : StrictLive n D) (hc : sem_Comp n G D)
    (I : Finset (Fin n)) (hin : I ⊆ ineligSet n D)
    {α : Type} (rows : α → Fin n → Bool)
    (good : ∀ i ∈ I, ∀ r, (∃ a, G i a ∧ rows r a = true) ∨
      ∃ a, a ≠ i ∧ rows r = single a)
    (active : ∀ i ∈ I, ∃ r a, G i a ∧ rows r a = true) :
    ∃ T : Finset Nat, T.card = I.card ∧ ∀ g ∈ T,
      g < D.length ∧ tag D g = true ∧ supp n D (n + g) = ∅ ∧
        (∃ r, val D (rows r) (opA D g) = true ∨ val D (rows r) (opB D g) = true) ∧
        ∃ p, p < n + g ∧ ∀ r, val D (rows r) (n + g) = val D (rows r) p := by
  classical
  have hex : ∀ i : Fin n, ∃ e : Nat × Bool, i ∈ I →
      e.1 < D.length ∧ tag D e.1 = true ∧ supp n D (src D e) = {i} ∧
        supp n D (n + e.1) = ∅ ∧ ∀ a, G i a → a ∈ supp n D (src D (e.1, !e.2)) := by
    intro i
    by_cases hi : i ∈ I
    · obtain ⟨e, he, ht, hs, hzero, hn, _, _⟩ := sem_inelig_consumer hG h hc (hin hi)
      exact ⟨e, fun _ => ⟨he, ht, hs, hzero, hn⟩⟩
    · exact ⟨(0, false), fun hh => False.elim (hi hh)⟩
  choose e he using hex
  refine ⟨I.image (fun i => (e i).1), ?_, ?_⟩
  · apply Finset.card_image_of_injOn
    intro i hi j hj eq
    by_contra ne
    exact exit_gate_injective hG ne (he i hi).2.2.1 (he j hj).2.2.1 (he i hi).2.2.2.2 eq
  · intro g hg
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hg
    obtain ⟨hlt, ht, hpure, hzero, hn⟩ := he i hi
    refine ⟨hlt, ht, hzero, ?_, src D (e i), sem_src_lt h.1 hlt (e i).2, ?_⟩
    · obtain ⟨r, a, hia, hxa⟩ := active i hi
      have hval : val D (rows r) (src D ((e i).1, !(e i).2)) = true :=
        sem_val_of_supp h.1 (hn a hia) hxa
      refine ⟨r, ?_⟩
      cases hs : (e i).2
      · right
        simpa [src, hs] using hval
      · left
        simpa [src, hs] using hval
    · intro r
      rcases good i hi r with ⟨a, hia, hxa⟩ | ⟨a, hai, hx⟩
      · have htval : val D (rows r) (src D ((e i).1, !(e i).2)) = true :=
          sem_val_of_supp h.1 (hn a hia) hxa
        rw [sem_val_gate_src h.1 _ hlt (e i).2, ht, gop_true, htval, Bool.and_true]
      · rw [hx]
        exact and_neutral_single h.1 hlt ht (e i).2 (hpure ▸ Finset.Subset.refl _) hai


lemma twice_ineligible_copy_gates_support {n : Nat} {G : Fin n → Fin n → Prop} {D : Dag}
    (hG : sem_Gr G) (h : StrictLive n D) (hc : sem_Comp n G D)
    (I P : Finset (Fin n)) (hin : I ⊆ ineligSet n D)
    {α : Type} (rows : α → Fin n → Bool)
    (good : ∀ i ∈ I, ∀ r, (∃ a, G i a ∧ rows r a = true) ∨
      ∃ a, a ≠ i ∧ rows r = single a)
    (active : ∀ i ∈ I, ∃ r a, G i a ∧ rows r a = true)
    (inputs : ∀ r i, i ∈ I → rows r i = false)
    (positive : ∃ r, val D (rows r) (outW n D) = true)
    (singletons : ∀ v ∈ P, ∃ r, rows r = single v) :
    ∃ T : Finset Nat, T.card = 2 * I.card ∧ ∀ j ∈ T,
      j < D.length ∧ (tag D j = true → supp n D (n + j) ∩ P = ∅) ∧
        ∃ p, p < n + j ∧ ∀ r, val D (rows r) (n + j) = val D (rows r) p := by
  obtain ⟨A, ha, hA⟩ := neutral_ineligible_active_zero hG h hc I hin rows good active
  obtain ⟨Z, hz, hZ⟩ := GeneralZero.zero_rows_exact_copy_gates h I inputs positive
  have hd : Disjoint A Z := by
    rw [Finset.disjoint_left]
    intro j hjA hjZ
    obtain ⟨_, ht, _, ⟨r, hleft | hright⟩, _⟩ := hA j hjA
    · have hz := (hZ j hjZ).2.1 ht r
      exact Bool.false_ne_true (hz.1.symm.trans hleft)
    · have hz := (hZ j hjZ).2.1 ht r
      exact Bool.false_ne_true (hz.2.symm.trans hright)
  refine ⟨A ∪ Z, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hd, ha, hz]
    omega
  · intro j hj
    rcases Finset.mem_union.mp hj with hj | hj
    · refine ⟨(hA j hj).1, ?_, (hA j hj).2.2.2.2⟩
      intro _
      rw [(hA j hj).2.2.1, Finset.empty_inter]
    · refine ⟨(hZ j hj).1, ?_, (hZ j hj).2.2⟩
      intro ht
      apply Finset.eq_empty_of_forall_notMem
      intro v hv
      obtain ⟨r, hr⟩ := singletons v (Finset.mem_inter.mp hv).2
      have hs := (hZ j hj).2.1 ht r
      have hfalse : val D (rows r) (n + j) = false := by
        rw [val_gate h.1 _ j (hZ j hj).1, ht, gop_true, hs.1]
        rfl
      rw [hr] at hfalse
      exact Bool.false_ne_true (hfalse.symm.trans (mem_supp.mp (Finset.mem_inter.mp hv).1))

open PEqualNP.Outside.L_meta_2590_aux.Four
open PEqualNP.Outside.L_meta_2590_aux.SevenGeneral
open PEqualNP.Outside.L_meta_2590_aux.Thirteen
open PEqualNP.Outside.L_meta_2590_aux.EightGeneral

set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 1000000 in
lemma cases_singletons13 : ∀ k : Fin 5, ∀ v : Fin 10, v ∉ casesI k →
    ∃ r : Fin 13, caseRow k r = single v := by
  unfold caseRow liftMask casesMasks casesI single
  decide +kernel

lemma eight_copies_and_support {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (four : (ineligSet 10 D).card = 4) :
    ∃ k : Fin 5, casesI k = ineligSet 10 D ∧ ∃ T : Finset Nat,
      T.card = 8 ∧ ∀ j ∈ T, j < D.length ∧
        (tag D j = true → supp 10 D (10 + j) ∩ eligSet 10 D = ∅) ∧
        ∃ p, p < 10 + j ∧ ∀ r : Fin 13,
          val D (caseRow k r) (10 + j) = val D (caseRow k r) p := by
  have hind : ∀ a ∈ ineligSet 10 D, ∀ b ∈ ineligSet 10 D, ¬ Adj a b := by
    intro a ha b hb hab
    rcases sem_elig_cover graph_ok h hc hab with ea | eb
    · exact (sem_mem_inelig.mp ha) ea
    · exact (sem_mem_inelig.mp hb) eb
  obtain ⟨k, hk⟩ := classify_four (ineligSet 10 D) four hind
  have hin : casesI k ⊆ ineligSet 10 D := hk ▸ Finset.Subset.refl _
  have geo := cases_geometry13 k
  obtain ⟨T, ht, hT⟩ := twice_ineligible_copy_gates_support graph_ok h hc
    (casesI k) (eligSet 10 D) hin (caseRow k) geo.2.2.2
    (fun i hi => ⟨0, cases_hits_zero k i hi⟩) geo.2.1 ⟨0, (hc _).mpr geo.2.2.1⟩
    (by
      intro v hv
      apply cases_singletons13 k v
      rw [hk]
      intro hvi
      exact (sem_mem_inelig.mp hvi) hv)
  exact ⟨k, hk, T, by simpa [geo.1] using ht, hT⟩

end EightSupport

namespace ThirteenRows
def gateVal (w : List Nat) (g : Bool × Nat × Nat) : Nat :=
  if g.1 then w.getD g.2.1 0 &&& w.getD g.2.2 0 else w.getD g.2.1 0 ||| w.getD g.2.2 0

end ThirteenRows


namespace SevenRows

open ThirteenRows

lemma base_insert_state {k : Nat} {w : List Nat} (h : State k w) {v : Nat} (hv : v ∈ base) :
    State k (w ++ [v]) := by
  cases k with
  | zero => exact holds_append h hv
  | succ k =>
    cases k with
    | zero =>
      obtain ⟨f,hf,hw⟩ := h
      exact ⟨f,hf,holds_append hw (extend_mem_left hv)⟩
    | succ k =>
      cases k with
      | zero =>
        obtain ⟨f,hf,a,ha,b,hb,hw⟩ := h
        exact ⟨f,hf,a,ha,b,hb,holds_append hw (extend_mem_left (extend_mem_left hv))⟩
      | succ k => exact False.elim h

def chargedIndices : List (Bool × Nat × Nat) → List Nat → List Nat
  | [], _ => []
  | g :: D, w =>
      let rest := (chargedIndices D (step w g)).map Nat.succ
      if g.1 = true ∧ gateVal w g ∉ base then 0 :: rest else rest

lemma charged_run_state (D : List (Bool × Nat × Nat)) {k : Nat} {w : List Nat}
    (h : State k w) (bound : k + (chargedIndices D w).length ≤ 2) :
    State (k + (chargedIndices D w).length) (run D w) := by
  induction D generalizing k w with
  | nil => simpa [chargedIndices,run] using h
  | cons g D ih =>
    rcases g with ⟨tag,a,b⟩
    cases tag
    · have hb : (chargedIndices ((false,a,b)::D) w).length =
          (chargedIndices D (step w (false,a,b))).length := by simp [chargedIndices]
      rw [hb] at bound ⊢
      exact ih (or_state h a b) bound
    · by_cases hv : gateVal w (true,a,b) ∈ base
      · have hb : (chargedIndices ((true,a,b)::D) w).length =
            (chargedIndices D (step w (true,a,b))).length := by simp [chargedIndices,hv]
        rw [hb] at bound ⊢
        exact ih (base_insert_state h hv) bound
      · have hb : (chargedIndices ((true,a,b)::D) w).length =
            (chargedIndices D (step w (true,a,b))).length + 1 := by simp [chargedIndices,hv]
        rw [hb] at bound ⊢
        have hk : k ≤ 1 := by omega
        have hn := ih (and_state hk h a b)
          (by omega : k+1+(chargedIndices D (step w (true,a,b))).length ≤ 2)
        have arith : k + ((chargedIndices D (step w (true,a,b))).length + 1) =
            k + 1 + (chargedIndices D (step w (true,a,b))).length := by omega
        rw [arith]
        exact hn

lemma three_charged (D : List (Bool × Nat × Nat)) (w : List Nat) (hw : Holds base w)
    (out : Nat) (ho : (run D w).getD out 0 = 7) : 3 ≤ (chargedIndices D w).length := by
  by_contra hn
  have h := charged_run_state D (k := 0) hw (by omega)
  have no := state_target h
  have hz : 0 ≠ (7 : Nat) := by omega
  by_cases hi : out < (run D w).length
  · have hm : (run D w).getD out 0 ∈ run D w := by
      rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi]
      exact List.getElem_mem hi
    exact no _ hm ho
  · have he : (run D w).getD out 0 = 0 := by
      simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega : (run D w).length ≤ out)]
    omega

lemma charged_mem_spec (D : List (Bool × Nat × Nat)) (w : List Nat) (j : Nat)
    (hj : j ∈ chargedIndices D w) :
    j < D.length ∧ (D.getD j (false,0,0)).1 = true ∧
      gateVal (run (D.take j) w) (D.getD j (false,0,0)) ∉ base := by
  induction D generalizing w j with
  | nil => simp [chargedIndices] at hj
  | cons g D ih =>
    have tail : ∀ j ∈ (chargedIndices D (step w g)).map Nat.succ,
        j < (g::D).length ∧ ((g::D).getD j (false,0,0)).1 = true ∧
        gateVal (run ((g::D).take j) w) ((g::D).getD j (false,0,0)) ∉ base := by
      intro j hm
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
      have hh := ih (step w g) a ha
      simpa only [List.length_cons,Nat.succ_lt_succ_iff,List.getD_cons_succ,
        List.take_succ_cons,run,List.foldl_cons] using hh
    by_cases hs : g.1 = true ∧ gateVal w g ∉ base
    · rw [chargedIndices,ite_eq_left hs] at hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact ⟨by simp,hs⟩
      · exact tail j hj
    · rw [chargedIndices,ite_eq_right hs] at hj
      exact tail j hj

lemma charged_nodup (D : List (Bool × Nat × Nat)) (w : List Nat) :
    (chargedIndices D w).Nodup := by
  induction D generalizing w with
  | nil => simp [chargedIndices]
  | cons g D ih =>
    have hn : ((chargedIndices D (step w g)).map Nat.succ).Nodup :=
      (ih (step w g)).map Nat.succ_injective
    by_cases hs : g.1 = true ∧ gateVal w g ∉ base
    · rw [chargedIndices,ite_eq_left hs]
      exact List.nodup_cons.mpr ⟨by simp,hn⟩
    · simpa only [chargedIndices,ite_eq_right hs] using hn

lemma three_nonbase_ands (D : List (Bool × Nat × Nat)) (w : List Nat) (hw : Holds base w)
    (out : Nat) (ho : (run D w).getD out 0 = 7) :
    ∃ T : Finset Nat, 3 ≤ T.card ∧ ∀ j ∈ T,
      j < D.length ∧ (D.getD j (false,0,0)).1 = true ∧
        gateVal (run (D.take j) w) (D.getD j (false,0,0)) ∉ base := by
  refine ⟨(chargedIndices D w).toFinset,?_,?_⟩
  · simpa only [List.toFinset_card_of_nodup (charged_nodup D w)] using three_charged D w hw out ho
  · intro j hj
    exact charged_mem_spec D w j (List.mem_toFinset.mp hj)

set_option maxHeartbeats 0 in
lemma two_raw_implies_base : ∀ a : Fin 128, ∀ i j : Fin 6, i ≠ j →
    a.val &&& ([49,73,26,44,98,84] : List Nat).getD i.val 0 =
      ([49,73,26,44,98,84] : List Nat).getD i.val 0 →
    a.val &&& ([49,73,26,44,98,84] : List Nat).getD j.val 0 =
      ([49,73,26,44,98,84] : List Nat).getD j.val 0 → a.val ∈ base := by decide +kernel

end SevenRows


namespace SevenRows

open PEqualNP.Outside.L_meta_2590_aux.DagTools
open SevenGeneral

def rawMasks : List Nat := [49,73,26,44,98,84]

lemma mask_contains_input {n : Nat} {D : Dag} (hS : Strict n D)
    (masks : Fin n → Nat) {u : Fin n} {w : Nat} (hu : u ∈ supp n D w) :
    (run D (List.ofFn masks)).getD w 0 &&& masks u = masks u := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [Nat.testBit_and,run_testBit_val]
  by_cases hi : (masks u).testBit r = true
  · rw [sem_val_of_supp hS hu hi,hi]
    rfl
  · have hz : (masks u).testBit r = false := Bool.eq_false_iff.mpr hi
    rw [hz,Bool.and_false]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 1000000 in
lemma cases_raw_codes : ∀ k : Fin 5, ∀ u v : Fin 10,
    u ∉ casesI k → v ∉ casesI k → u ≠ v →
    ∃ i j : Fin 6, i ≠ j ∧ casesMasks k u = rawMasks.getD i.val 0 ∧
      casesMasks k v = rawMasks.getD j.val 0 := by decide +kernel

lemma two_support_mask_base {D : Dag} (hS : Strict 10 D) (k : Fin 5) (w : Nat)
    {u v : Fin 10} (hu : u ∈ supp 10 D w) (hv : v ∈ supp 10 D w)
    (hui : u ∉ casesI k) (hvi : v ∉ casesI k) (hne : u ≠ v) :
    (run D (List.ofFn (casesMasks k))).getD w 0 ∈ base := by
  let a := (run D (List.ofFn (casesMasks k))).getD w 0
  have small : a < 128 := by
    apply getD_lt_two_pow _ 7 w
    apply run_lt_two_pow D _ 7
    intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact (cases_geometry k).2.1 i
  obtain ⟨i,j,hn,hu',hv'⟩ := cases_raw_codes k u v hui hvi hne
  have hau : a &&& rawMasks.getD i.val 0 = rawMasks.getD i.val 0 := by
    rw [← hu']
    exact mask_contains_input hS (casesMasks k) hu
  have hav : a &&& rawMasks.getD j.val 0 = rawMasks.getD j.val 0 := by
    rw [← hv']
    exact mask_contains_input hS (casesMasks k) hv
  exact two_raw_implies_base ⟨a,small⟩ i j hn hau hav

lemma big_support_mask_base {D : Dag} (hS : Strict 10 D) (k : Fin 5) (w : Nat)
    (hbig : 2 ≤ ((supp 10 D w) \ casesI k).card) :
    (run D (List.ofFn (casesMasks k))).getD w 0 ∈ base := by
  obtain ⟨u,hu,v,hv,hne⟩ := Finset.one_lt_card.mp (by omega : 1 < ((supp 10 D w) \ casesI k).card)
  exact two_support_mask_base hS k w (Finset.mem_sdiff.mp hu).1 (Finset.mem_sdiff.mp hv).1
    (Finset.mem_sdiff.mp hu).2 (Finset.mem_sdiff.mp hv).2 hne

end SevenRows


namespace SevenRows

open ThirteenRows

lemma run_nat_length (D : List (Bool × Nat × Nat)) (w : List Nat) :
    (run D w).length = w.length + D.length := by
  induction D generalizing w with
  | nil => rfl
  | cons g D ih =>
    change (run D (step w g)).length = _
    rw [ih]
    simp [step]
    omega

lemma run_nat_getD_lt (D : List (Bool × Nat × Nat)) (w : List Nat) (i : Nat)
    (hi : i < w.length) : (run D w).getD i 0 = w.getD i 0 := by
  induction D generalizing w with
  | nil => rfl
  | cons g D ih =>
    change (run D (step w g)).getD i 0 = _
    rw [ih (step w g) (by simp [step]; omega)]
    simp [step,List.getD_eq_getElem?_getD,List.getElem?_append_left hi]

lemma run_gateVal (D : List (Bool × Nat × Nat)) (w : List Nat) (j : Nat) (hj : j < D.length) :
    (run D w).getD (w.length+j) 0 = gateVal (run (D.take j) w) (D.getD j (false,0,0)) := by
  have hsplit : D = D.take j ++ D[j] :: D.drop (j+1) := by simp
  have hlen : (run (D.take j) w).length = w.length+j := by
    rw [run_nat_length,List.length_take]
    omega
  have hget : D.getD j (false,0,0) = D[j] := by
    simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj]
  rw [hget]
  conv_lhs =>
    rw [hsplit]
    unfold run
    rw [List.foldl_append,List.foldl_cons]
  change (run (D.drop (j+1)) (step (run (D.take j) w) D[j])).getD (w.length+j) 0 = _
  rw [run_nat_getD_lt _ _ _ (by simp [step,hlen])]
  rw [← hlen]
  simp [step,gateVal,List.getD_eq_getElem?_getD]

lemma neutralize_length (D : List (Bool × Nat × Nat)) (off : Nat) (T : Finset Nat) (p : Nat → Nat) :
    (neutralizeFrom D off T p).length = D.length := by
  induction D generalizing off with
  | nil => rfl
  | cons g D ih => simp [neutralizeFrom,ih]

lemma neutralize_getD (D : List (Bool × Nat × Nat)) (off : Nat) (T : Finset Nat) (p : Nat → Nat)
    (j : Nat) (hj : j < D.length) :
    (neutralizeFrom D off T p).getD j (false,0,0) =
      if off+j ∈ T then (false,p (off+j),p (off+j)) else D.getD j (false,0,0) := by
  induction D generalizing off j with
  | nil => simp at hj
  | cons g D ih =>
    cases j with
    | zero => simp [neutralizeFrom]
    | succ j =>
      have hh := ih (off+1) j (by simpa using hj)
      simpa only [neutralizeFrom,List.getD_cons_succ,Nat.add_assoc,Nat.add_comm 1 j] using hh

end SevenRows


namespace SevenRows

open PEqualNP.Outside.L_meta_2590_aux.DagTools
open SevenGeneral Four ThirteenRows

set_option maxHeartbeats 0 in
lemma caseRow_low : ∀ k : Fin 5, ∀ r : Fin 7, ∀ v : Fin 10,
    Thirteen.caseRow k ⟨r.val,by omega⟩ v = (casesMasks k v).testBit r.val := by decide +kernel

lemma charged_package {D : Dag} (hS : Strict 10 D) (hc : sem_Comp 10 Adj D)
    (k : Fin 5) (T : Finset Nat)
    (hT : ∀ j ∈ T, j < D.length ∧ ∃ p, p < 10+j ∧
      ∀ r : Fin 13, val D (Thirteen.caseRow k r) (10+j) = val D (Thirteen.caseRow k r) p) :
    ∃ C : Finset Nat, 3 ≤ C.card ∧ Disjoint C T ∧ ∀ j ∈ C,
      j < D.length ∧ tag D j = true ∧ ((supp 10 D (10+j)) \ casesI k).card ≤ 1 := by
  classical
  have hp : ∀ j : Nat, ∃ p : Nat, j ∈ T → p < 10+j ∧
      ∀ r : Fin 13, val D (Thirteen.caseRow k r) (10+j) = val D (Thirteen.caseRow k r) p := by
    intro j
    by_cases hj : j ∈ T
    · obtain ⟨_,p,hp,hr⟩ := hT j hj
      exact ⟨p,fun _ => ⟨hp,hr⟩⟩
    · exact ⟨0,fun hh => False.elim (hj hh)⟩
  choose p hp using hp
  let w := List.ofFn (casesMasks k)
  let D' := neutralizeFrom D 0 T p
  have neu : NeutralFrom D w 0 T p := by
    intro j hj ht
    simp only [Nat.zero_add] at ht ⊢
    apply step_eq_copy_of_val_rows D (casesMasks k) hS hj (p j) (hp j ht).1 (cases_geometry k).2.1
    intro r
    have eq : Thirteen.caseRow k ⟨r.val,by omega⟩ = fun v => (casesMasks k v).testBit r.val :=
      funext (caseRow_low k r)
    have hh := (hp j ht).2 ⟨r.val,by omega⟩
    rw [eq] at hh
    exact hh
  have same : run D' w = run D w := neutralize_run D w 0 T p neu
  have target : (run D w).getD (outW 10 D) 0 = 7 := by
    apply run_eq_seven_of_rows D (casesMasks k) _ (cases_geometry k).2.1
    intro r
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact (hc _).trans ((cases_geometry k).2.2.2.2 r)
  obtain ⟨C,hcard,hC⟩ := three_nonbase_ands D' w (cases_geometry k).2.2.1 (outW 10 D)
    (by rw [same]; exact target)
  have hgood : ∀ j ∈ C, j < D.length ∧ j ∉ T ∧ tag D j = true ∧
      (run D w).getD (10+j) 0 ∉ base := by
    intro j hj
    obtain ⟨hlt,htag,hnot⟩ := hC j hj
    have hlt' : j < D.length := by simpa only [D',neutralize_length] using hlt
    have fields := neutralize_getD D 0 T p j hlt'
    simp only [Nat.zero_add] at fields
    have hnt : j ∉ T := by
      intro ht
      have hh : (D'.getD j (false,0,0)).1 = false := by
        dsimp [D']
        rw [fields,ite_eq_left ht]
      exact Bool.false_ne_true (hh.symm.trans htag)
    have hfield : D'.getD j (false,0,0) = D.getD j (false,0,0) := by
      simpa only [D',ite_eq_right hnt] using fields
    have ht : tag D j = true := by simpa only [hfield,tag] using htag
    have final : gateVal (run (D'.take j) w) (D'.getD j (false,0,0)) =
        (run D w).getD (10+j) 0 := by
      rw [← run_gateVal D' w j hlt,same]
      simp only [w,List.length_ofFn]
    refine ⟨hlt',hnt,ht,?_⟩
    rw [final] at hnot
    exact hnot
  refine ⟨C,hcard,?_,?_⟩
  · apply Finset.disjoint_left.mpr
    intro j hj ht
    exact (hgood j hj).2.1 ht
  · intro j hj
    have hg := hgood j hj
    refine ⟨hg.1,hg.2.2.1,?_⟩
    by_contra hsmall
    have big : 2 ≤ ((supp 10 D (10+j)) \ casesI k).card := by omega
    exact hg.2.2.2 (big_support_mask_base hS k (10+j) big)

end SevenRows


namespace MaskGeometry

open PEqualNP.Outside.L_meta_2590_aux.DagTools
open SevenRows SevenGeneral Four

def inputs : List Nat := [177,329,538,1068,2146,4180]
def triples : List Nat := [1919,4863,3327,6527]
def pairIndices : List (Nat × Nat) :=
  [(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(1,5),(2,3),(2,5),(3,4),(4,5)]

def vertex (k : Fin 5) (i : Fin 6) : Fin 10 :=
  (([[3,4,1,5,6,7],[8,5,4,1,9,2],[8,6,2,0,7,4],[9,6,0,2,5,3],[0,1,3,7,8,9]] :
    List (List (Fin 10))).getD k.val []).getD i.val 0

def masks (k : Fin 5) (v : Fin 10) : Nat := Thirteen.liftMask (casesMasks k v)
def sig (D : Dag) (k : Fin 5) (w : Nat) : Nat := (run D (List.ofFn (masks k))).getD w 0
def project (D : Dag) (k : Fin 5) (w : Nat) : Finset (Fin 10) :=
  supp 10 D w ∩ complement (casesI k)

set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 1000000 in
lemma geometry : ∀ k : Fin 5,
    (∀ i : Fin 6, vertex k i ∈ complement (casesI k)) ∧
    Function.Injective (vertex k) ∧
    (∀ v ∈ complement (casesI k), ∃ i : Fin 6, vertex k i = v) ∧
    (∀ v : Fin 10, masks k v < 8192 ∧ masks k v ∈ 0 :: inputs) ∧
    (∀ i : Fin 6, masks k (vertex k i) = inputs.getD i.val 0) ∧
    (∀ i : Fin 6, ∀ v : Fin 10, (masks k v).testBit (7+i.val) = single (vertex k i) v) ∧
    (∀ i ∈ casesI k, ∀ a, Adj i a → a ∈ complement (casesI k)) := by
  unfold Function.Injective complement masks Thirteen.liftMask casesMasks casesI vertex inputs single Adj
  decide +kernel

set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 1000000 in
lemma star_geometry : ∀ k : Fin 5, ∀ i ∈ casesI k,
    ∃ t ∈ triples, t < 8192 ∧ (∀ r : Fin 7, t.testBit r.val = true) ∧
      ∀ j : Fin 6, t.testBit (7+j.val) = decide (Adj i (vertex k j)) := by
  unfold triples casesI Adj vertex
  decide +kernel

set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 1000000 in
lemma pair_allowed : ∀ k : Fin 5, ∀ i ∈ casesI k, ∀ a b : Fin 6,
    a ≠ b → Adj i (vertex k a) → Adj i (vertex k b) →
      (a.val,b.val) ∈ pairIndices ∨ (b.val,a.val) ∈ pairIndices := by
  unfold casesI Adj vertex pairIndices
  decide +kernel

lemma sig_bound (D : Dag) (k : Fin 5) (w : Nat) : sig D k w < 8192 := by
  apply getD_lt_two_pow _ 13 w
  apply run_lt_two_pow D _ 13
  intro a ha
  obtain ⟨v,rfl⟩ := List.mem_ofFn.mp ha
  exact ((geometry k).2.2.2.1 v).1

lemma sig_single_bit (D : Dag) (k : Fin 5) (w : Nat) (i : Fin 6) :
    (sig D k w).testBit (7+i.val) = val D (single (vertex k i)) w := by
  unfold sig
  rw [run_testBit_val]
  congr 1
  exact funext ((geometry k).2.2.2.2.2.1 i)

lemma sig_high_bit (D : Dag) (k : Fin 5) (w : Nat) (i : Fin 6) :
    ((sig D k w)/128).testBit i.val = decide (vertex k i ∈ project D k w) := by
  change ((sig D k w)/2^7).testBit i.val = _
  rw [Nat.testBit_div_two_pow,Nat.add_comm,sig_single_bit]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq,project,Finset.mem_inter,(geometry k).1 i,and_true,mem_supp]

lemma sig_high_bound (D : Dag) (k : Fin 5) (w : Nat) : (sig D k w)/128 < 64 := by
  have hb := sig_bound D k w
  omega

lemma sig_high_empty {D : Dag} {k : Fin 5} {w : Nat} (he : project D k w = ∅) :
    (sig D k w)/128 = 0 := by
  apply nat_eq_of_low_testBits (b := 6) (sig_high_bound D k w) (by decide)
  intro r
  rw [sig_high_bit,he]
  simp

set_option maxHeartbeats 0 in
lemma onehot_geometry : ∀ i j : Fin 6,
    (2^i.val : Nat) < 64 ∧ (2^i.val : Nat).testBit j.val = decide (i=j) := by decide +kernel

lemma sig_high_singleton {D : Dag} {k : Fin 5} {w : Nat} {i : Fin 6}
    (he : project D k w = {vertex k i}) : (sig D k w)/128 = 2^i.val := by
  apply nat_eq_of_low_testBits (b := 6) (sig_high_bound D k w) ((onehot_geometry i i).1)
  intro j
  rw [sig_high_bit,he,(onehot_geometry i j).2]
  congr 1
  simp only [Finset.mem_singleton]
  apply propext
  constructor
  · intro eq
    exact ((geometry k).2.1 eq).symm
  · intro eq
    rw [eq]

lemma sig_neighborhood_mem {D : Dag} (hS : Strict 10 D) (k : Fin 5) (w : Nat)
    (i : Fin 10) (hi : i ∈ casesI k) (he : project D k w = nbrs (casesI k) i) :
    sig D k w ∈ triples := by
  obtain ⟨t,ht,tbound,tlo,thi⟩ := star_geometry k i hi
  suffices hs : sig D k w = t by simpa [hs] using ht
  apply nat_eq_of_low_testBits (b := 13) (sig_bound D k w) tbound
  intro r
  by_cases hr : r.val < 7
  · have rt := tlo ⟨r.val,hr⟩
    rw [rt]
    obtain ⟨a,hia,har⟩ := (cases_geometry k).2.2.2.1 i hi ⟨r.val,hr⟩
    have ham : a ∈ project D k w := by
      rw [he]
      exact Finset.mem_filter.mpr ⟨(geometry k).2.2.2.2.2.2 i hi a hia,hia⟩
    have has : a ∈ supp 10 D w := (Finset.mem_inter.mp ham).1
    unfold sig
    rw [run_testBit_val]
    apply sem_val_of_supp hS has
    have eq := caseRow_low k ⟨r.val,hr⟩ a
    exact eq.trans har
  · let j : Fin 6 := ⟨r.val-7,by omega⟩
    have rj : r.val = 7+j.val := by dsimp [j]; omega
    rw [rj,sig_single_bit,thi j]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq,← mem_supp]
    have hv := (geometry k).1 j
    have hm : vertex k j ∈ supp 10 D w ↔ vertex k j ∈ project D k w := by
      simp only [project,Finset.mem_inter,hv,and_true]
    rw [hm,he]
    simp only [nbrs,Finset.mem_filter,hv,true_and]

set_option maxHeartbeats 0 in
lemma low7_bits : ∀ r : Fin 7, (127 : Nat).testBit r.val = true := by decide +kernel

lemma sig_low_eq (D : Dag) (k : Fin 5) (w : Nat) :
    sig D k w &&& 127 = (run D (List.ofFn (casesMasks k))).getD w 0 := by
  have hb : (run D (List.ofFn (casesMasks k))).getD w 0 < 128 := by
    apply getD_lt_two_pow _ 7 w
    apply run_lt_two_pow D _ 7
    intro a ha
    obtain ⟨v,rfl⟩ := List.mem_ofFn.mp ha
    exact (cases_geometry k).2.1 v
  apply nat_eq_of_low_testBits (b := 7) (Nat.and_lt_two_pow _ (by decide : 127 < 2^7)) hb
  intro r
  simp only [sig,Nat.testBit_and,run_testBit_val,low7_bits r,Bool.and_true]
  congr 1
  exact funext (caseRow_low k r)

lemma sig_low_contains {D : Dag} (hS : Strict 10 D) (k : Fin 5) (w : Nat)
    {u : Fin 10} (hu : u ∈ supp 10 D w) :
    (sig D k w &&& 127) &&& casesMasks k u = casesMasks k u := by
  rw [sig_low_eq]
  exact mask_contains_input hS (casesMasks k) hu

set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 1000000 in
lemma rows_target : ∀ k : Fin 5, ∀ r : Fin 13,
    sem_Edge Adj (Thirteen.caseRow k r) ↔ r.val < 3 := by
  unfold sem_Edge Adj Thirteen.caseRow Thirteen.liftMask casesMasks
  decide +kernel

set_option maxHeartbeats 0 in
lemma target13_bits : ∀ r : Fin 13, (7 : Nat).testBit r.val = decide (r.val < 3) := by decide +kernel

lemma sig_output {D : Dag} (hc : sem_Comp 10 Adj D) (k : Fin 5) :
    sig D k (outW 10 D) = 7 := by
  apply nat_eq_of_low_testBits (b := 13) (sig_bound D k _) (by decide)
  intro r
  rw [target13_bits]
  unfold sig
  rw [run_testBit_val]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact (hc _).trans (rows_target k r)

lemma sig_singleton_code {D : Dag} {k : Fin 5} {w : Nat} {u : Fin 10}
    (he : project D k w = {u}) :
    ∃ i : Fin 6, vertex k i = u ∧ (sig D k w)/128 = 2^i.val := by
  have hu : u ∈ complement (casesI k) := by
    have hm : u ∈ project D k w := he ▸ Finset.mem_singleton_self u
    exact (Finset.mem_inter.mp hm).2
  obtain ⟨i,hi⟩ := (geometry k).2.2.1 u hu
  exact ⟨i,hi,sig_high_singleton (he.trans (congrArg Singleton.singleton hi.symm))⟩

set_option maxHeartbeats 0 in
lemma powers_low : ∀ i : Fin 6, (2^i.val : Nat) ∈ [0,1,2,4,8,16,32] := by decide +kernel

lemma sig_high_small {D : Dag} {k : Fin 5} {w : Nat}
    (hs : (project D k w).card ≤ 1) : (sig D k w)/128 ∈ [0,1,2,4,8,16,32] := by
  by_cases he : project D k w = ∅
  · rw [sig_high_empty he]
    simp
  · have hc : (project D k w).card = 1 := by
      have hp := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he)
      omega
    obtain ⟨u,hu⟩ := Finset.card_eq_one.mp hc
    obtain ⟨i,hi,hmask⟩ := sig_singleton_code hu
    rw [hmask]
    exact powers_low i

lemma pair_sources_codes {D : Dag} {k : Fin 5} {a b : Nat} {u v i : Fin 10}
    (hi : i ∈ casesI k) (ha : project D k a = {u}) (hb : project D k b = {v})
    (hne : u ≠ v) (hs : {u,v} ⊆ nbrs (casesI k) i) :
    ∃ x y : Fin 6, (sig D k a)/128 = 2^x.val ∧ (sig D k b)/128 = 2^y.val ∧
      ((x.val,y.val) ∈ pairIndices ∨ (y.val,x.val) ∈ pairIndices) := by
  obtain ⟨x,hx,hhx⟩ := sig_singleton_code ha
  obtain ⟨y,hy,hhy⟩ := sig_singleton_code hb
  have hxy : x ≠ y := by intro he; apply hne; rw [← hx,← hy,he]
  have hu : Adj i (vertex k x) := by
    rw [hx]
    exact (Finset.mem_filter.mp (hs (by simp))).2
  have hv : Adj i (vertex k y) := by
    rw [hy]
    exact (Finset.mem_filter.mp (hs (by simp))).2
  exact ⟨x,y,hhx,hhy,pair_allowed k i hi x y hxy hu hv⟩

end MaskGeometry

namespace LabelRigidity
open PEqualNP.Outside.L_meta_2590_aux.DagTools
open Rigidity DagRigidity

variable {n : Nat} {D : Dag}

lemma family_rigid_of_label_card (hS : Strict n D) (P : Finset (Fin n))
    (hP : P.card ≤ 6) (L : Finset (Finset (Fin n)))
    (hLcard : L.card = 4) (hL : ∀ T ∈ L, T.card = 3 ∧ sup_Occ n D P T)
    (hint : ∀ T ∈ L, ∀ U ∈ L, T ≠ U → (T ∩ U).card ≤ 1)
    (hfamily : (bigFamily n D P).card ≤ 8) :
    (bigFamily n D P).card = 8 ∧
    (∀ M ∈ bigFamily n D P \ L, M.card = 2 ∧ ∃ T ∈ L, M ⊆ T) ∧
    ∀ T ∈ L, ∃ M ∈ bigFamily n D P \ L, M.card = 2 ∧ M ⊆ T := by
  classical
  let F := bigFamily n D P
  let A := F \ L
  have hLF : L ⊆ F := by
    intro T hT
    exact mem_bigFamily hS (by have := (hL T hT).1; omega) (hL T hT).2
  have hFcard : F.card ≤ 8 := hfamily
  have hsum : A.card + L.card = F.card := Finset.card_sdiff_add_card_eq_card hLF
  have hAcard : A.card ≤ 4 := by omega
  have hAS : ∀ M ∈ A, M ⊆ P := by
    intro M hM
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp (Finset.mem_sdiff.mp hM).1
    exact Finset.inter_subset_right
  have parent (T) (hT : T ∈ L) : ∃ A' B' : Finset (Fin n),
      (A'.card ≤ 1 ∨ A' ∈ L ∨ A' ∈ A) ∧ (B'.card ≤ 1 ∨ B' ∈ L ∨ B' ∈ A) ∧
      A' ≠ T ∧ B' ≠ T ∧ (T = A' ∪ B' ∨ T = A' ∩ B') := by
    obtain ⟨U,V,hu,hv,hut,hvt,hcases⟩ := first_parents hS
      (by have := (hL T hT).1; omega) (hL T hT).2
    have member (M) (hm : sup_Occ n D P M) : M.card ≤ 1 ∨ M ∈ L ∨ M ∈ A := by
      by_cases small : M.card ≤ 1
      · exact Or.inl small
      · right
        by_cases hmem : M ∈ L
        · exact Or.inl hmem
        · exact Or.inr (Finset.mem_sdiff.mpr ⟨mem_bigFamily hS (by omega) hm,hmem⟩)
    exact ⟨U,V,member U hu,member V hv,hut,hvt,hcases⟩
  have result := eight_family_rigid hP hLcard hAcard (fun T ht => (hL T ht).1) hint hAS parent
  refine ⟨?_,result.2⟩
  change F.card = 8
  omega


def bigProducers (n : Nat) (D : Dag) (P : Finset (Fin n)) : Finset Nat :=
  (Finset.range D.length).filter (fun j => 2 ≤ (supp n D (n + j) ∩ P).card)

lemma bigFamily_eq_producer_image (hS : Strict n D) (P : Finset (Fin n)) :
    bigFamily n D P = (bigProducers n D P).image (fun j => supp n D (n + j) ∩ P) := by
  ext M
  constructor
  · intro hm
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hm
    have hg := (Finset.mem_filter.mp hj).1
    have hrange := (Finset.mem_filter.mp hg).1
    exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨hrange, (Finset.mem_filter.mp hj).2⟩, rfl⟩
  · intro hm
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hm
    exact mem_bigFamily hS (Finset.mem_filter.mp hj).2 (sup_occ_wire P (n + j))

lemma family_rigid_of_producer_card (hS : Strict n D) (P : Finset (Fin n))
    (hP : P.card ≤ 6) (L : Finset (Finset (Fin n)))
    (hLcard : L.card = 4) (hL : ∀ T ∈ L, T.card = 3 ∧ sup_Occ n D P T)
    (hint : ∀ T ∈ L, ∀ U ∈ L, T ≠ U → (T ∩ U).card ≤ 1)
    (hproducers : (bigProducers n D P).card ≤ 8) :
    (bigFamily n D P).card = 8 ∧
    (∀ M ∈ bigFamily n D P \ L, M.card = 2 ∧ ∃ T ∈ L, M ⊆ T) ∧
    ∀ T ∈ L, ∃ M ∈ bigFamily n D P \ L, M.card = 2 ∧ M ⊆ T := by
  apply family_rigid_of_label_card hS P hP L hLcard hL hint
  rw [bigFamily_eq_producer_image hS P]
  exact Finset.card_image_le.trans hproducers

lemma big_producers_new (hS : Strict n D) (P : Finset (Fin n))
    (hfamily : (bigFamily n D P).card = 8)
    (hproducers : (bigProducers n D P).card ≤ 8) :
    (bigProducers n D P).card = 8 ∧
      ∀ j ∈ bigProducers n D P, ∀ w, w < n + j →
        supp n D w ∩ P ≠ supp n D (n + j) ∩ P := by
  have himage := bigFamily_eq_producer_image hS P
  have hle : (bigFamily n D P).card ≤ (bigProducers n D P).card := by
    rw [himage]
    exact Finset.card_image_le
  have hcard : (bigProducers n D P).card = 8 := by omega
  have hinj : Set.InjOn (fun j => supp n D (n + j) ∩ P) (bigProducers n D P) :=
    Finset.card_image_iff.mp (by rw [← himage, hfamily, hcard])
  refine ⟨hcard, ?_⟩
  intro j hj w hw he
  have hM : 2 ≤ (supp n D (n + j) ∩ P).card := (Finset.mem_filter.mp hj).2
  obtain ⟨k, hk, hkw, hmask, _, _, _⟩ := sem_first_mask hS P _ hM w he
  have hkprod : k ∈ bigProducers n D P := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, by
    rw [hmask]
    exact hM⟩
  have keq : k = j := hinj hkprod hj hmask
  omega

lemma all_big_producers_or (hS : Strict n D) (P : Finset (Fin n))
    (hP : P.card ≤ 6) (L : Finset (Finset (Fin n)))
    (hLcard : L.card = 4) (hL : ∀ T ∈ L, T.card = 3 ∧ sup_Occ n D P T)
    (hint : ∀ T ∈ L, ∀ U ∈ L, T ≠ U → (T ∩ U).card ≤ 1)
    (hproducers : (bigProducers n D P).card ≤ 8) :
    ∀ j ∈ bigProducers n D P, tag D j = false := by
  obtain ⟨hfamily, hpairs, _⟩ := family_rigid_of_producer_card hS P hP L hLcard hL hint hproducers
  have hnew := (big_producers_new hS P hfamily hproducers).2
  have member (w : Nat) : (supp n D w ∩ P).card ≤ 1 ∨
      supp n D w ∩ P ∈ L ∨ supp n D w ∩ P ∈ bigFamily n D P \ L := by
    by_cases hs : (supp n D w ∩ P).card ≤ 1
    · exact Or.inl hs
    · right
      by_cases ht : supp n D w ∩ P ∈ L
      · exact Or.inl ht
      · exact Or.inr (Finset.mem_sdiff.mpr ⟨mem_bigFamily hS (by omega) (sup_occ_wire P w), ht⟩)
  intro j hj
  have hjlt : j < D.length := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
  have hM : 2 ≤ (supp n D (n + j) ∩ P).card := (Finset.mem_filter.mp hj).2
  cases ht : tag D j
  · rfl
  · exfalso
    have heq : supp n D (n + j) ∩ P =
        (supp n D (opA D j) ∩ P) ∩ (supp n D (opB D j) ∩ P) := by
      rw [sem_supp_and hS hjlt ht]
      ext v
      simp only [Finset.mem_inter]
      tauto
    exact standard_family_no_intersection hint (fun A ha => (hpairs A ha).1) hM
      (member _) (member _) (hnew j hj _ (hS j hjlt).1) (hnew j hj _ (hS j hjlt).2.1) heq


lemma abstract_family_rigid {α : Type} [DecidableEq α]
    (S : Finset α) (F L : Finset (Finset α))
    (hS : S.card ≤ 6) (hFcard : F.card ≤ 8) (hLcard : L.card = 4) (hLF : L ⊆ F)
    (hL : ∀ T ∈ L, T.card = 3)
    (hint : ∀ T ∈ L, ∀ U ∈ L, T ≠ U → (T ∩ U).card ≤ 1)
    (hFS : ∀ M ∈ F, M ⊆ S)
    (hpar : ∀ T ∈ L, ∃ P Q : Finset α,
      (P.card ≤ 1 ∨ P ∈ F) ∧ (Q.card ≤ 1 ∨ Q ∈ F) ∧
      P ≠ T ∧ Q ≠ T ∧ (T = P ∪ Q ∨ T = P ∩ Q)) :
    F.card = 8 ∧
      (∀ M ∈ F \ L, M.card = 2 ∧ ∃ T ∈ L, M ⊆ T) ∧
      ∀ T ∈ L, ∃ M ∈ F \ L, M.card = 2 ∧ M ⊆ T := by
  let A := F \ L
  have hsum : A.card + L.card = F.card := Finset.card_sdiff_add_card_eq_card hLF
  have hAcard : A.card ≤ 4 := by omega
  have split (M : Finset α) (hm : M.card ≤ 1 ∨ M ∈ F) :
      M.card ≤ 1 ∨ M ∈ L ∨ M ∈ A := by
    rcases hm with hm | hm
    · exact Or.inl hm
    · by_cases hml : M ∈ L
      · exact Or.inr (Or.inl hml)
      · exact Or.inr (Or.inr (Finset.mem_sdiff.mpr ⟨hm, hml⟩))
  have res := eight_family_rigid hS hLcard hAcard hL hint
    (fun M hM => hFS M (Finset.mem_sdiff.mp hM).1) (by
      intro T hT
      obtain ⟨P,Q,hP,hQ,hPT,hQT,hPQ⟩ := hpar T hT
      exact ⟨P,Q,split P hP,split Q hQ,hPT,hQT,hPQ⟩)
  exact ⟨by omega, res.2⟩

lemma fresh_big_gate_or (hS : Strict n D) (P : Finset (Fin n))
    (hP : P.card ≤ 6) (L : Finset (Finset (Fin n)))
    (hLcard : L.card = 4) (hL : ∀ T ∈ L, T.card = 3 ∧ sup_Occ n D P T)
    (hint : ∀ T ∈ L, ∀ U ∈ L, T ≠ U → (T ∩ U).card ≤ 1)
    (hfamily : (bigFamily n D P).card ≤ 8)
    {j : Nat} (hj : j < D.length) (hM : 2 ≤ (supp n D (n + j) ∩ P).card)
    (fresh : ∀ w, w < n + j → supp n D w ∩ P ≠ supp n D (n + j) ∩ P) :
    tag D j = false := by
  obtain ⟨_, hpairs, _⟩ := family_rigid_of_label_card hS P hP L hLcard hL hint hfamily
  have member (w : Nat) : (supp n D w ∩ P).card ≤ 1 ∨
      supp n D w ∩ P ∈ L ∨ supp n D w ∩ P ∈ bigFamily n D P \ L := by
    by_cases hs : (supp n D w ∩ P).card ≤ 1
    · exact Or.inl hs
    · right
      by_cases ht : supp n D w ∩ P ∈ L
      · exact Or.inl ht
      · exact Or.inr (Finset.mem_sdiff.mpr ⟨mem_bigFamily hS (by omega) (sup_occ_wire P w), ht⟩)
  cases ht : tag D j
  · rfl
  · exfalso
    have heq : supp n D (n + j) ∩ P =
        (supp n D (opA D j) ∩ P) ∩ (supp n D (opB D j) ∩ P) := by
      rw [sem_supp_and hS hj ht]
      ext v
      simp only [Finset.mem_inter]
      tauto
    exact standard_family_no_intersection hint (fun A ha => (hpairs A ha).1) hM
      (member _) (member _) (fresh _ (hS j hj).1) (fresh _ (hS j hj).2.1) heq

end LabelRigidity


namespace LabelBudget
open PEqualNP.Outside.L_meta_2590_aux.DagTools
open PEqualNP.Outside.L_meta_2590_aux.DagRigidity

noncomputable def firstBig (n : Nat) (D : Dag) (P : Finset (Fin n)) : Finset Nat := by
  classical
  exact (Finset.range D.length).filter (fun j => 2 ≤ (supp n D (n+j) ∩ P).card ∧
    ∀ w, w < n+j → supp n D w ∩ P ≠ supp n D (n+j) ∩ P)

lemma mem_firstBig {n : Nat} {D : Dag} {P : Finset (Fin n)} {j : Nat} :
    j ∈ firstBig n D P ↔ j < D.length ∧ 2 ≤ (supp n D (n+j) ∩ P).card ∧
      ∀ w, w < n+j → supp n D w ∩ P ≠ supp n D (n+j) ∩ P := by
  classical
  simp [firstBig]

lemma firstBig_card {n : Nat} {D : Dag} (h : Strict n D) (P : Finset (Fin n)) :
    (firstBig n D P).card = (bigFamily n D P).card := by
  classical
  let lab := fun j => supp n D (n+j) ∩ P
  have heq : (firstBig n D P).image lab = bigFamily n D P := by
    ext M
    constructor
    · rintro hm
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hm
      exact mem_bigFamily h (mem_firstBig.mp hj).2.1 ⟨n+j,rfl⟩
    · intro hm
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hm
      have hb := (Finset.mem_filter.mp hj).2
      obtain ⟨g,hg,_,he,_,hmin,_⟩ := sem_first_mask h P _ hb (n+j) rfl
      exact Finset.mem_image.mpr ⟨g,mem_firstBig.mpr ⟨hg,by simpa [he] using hb,
        by simpa [he] using hmin⟩,he⟩
  have hinj : Set.InjOn lab (firstBig n D P) := by
    intro i hi j hj he
    by_contra hne
    rcases lt_or_gt_of_ne hne with hij | hji
    · exact (mem_firstBig.mp hj).2.2 (n+i) (by omega) he
    · exact (mem_firstBig.mp hi).2.2 (n+j) (by omega) he.symm
  rw [← heq,Finset.card_image_of_injOn hinj]

lemma copy_budget {n : Nat} {D : Dag} (h : Strict n D) (P : Finset (Fin n))
    (T C : Finset Nat) (hT : ∀ j ∈ T, j < D.length)
    (hC : ∀ j ∈ C, j < D.length ∧ (supp n D (n+j) ∩ P).card ≤ 1)
    (hdis : Disjoint T C)
    (copy : ∀ j ∈ T, ∃ p, p < n+j ∧ supp n D (n+j) ∩ P = supp n D p ∩ P) :
    (bigFamily n D P).card + T.card + C.card ≤ D.length := by
  classical
  have hFT : Disjoint (firstBig n D P) T := by
    apply Finset.disjoint_left.mpr
    intro j hj ht
    obtain ⟨p,hp,he⟩ := copy j ht
    exact (mem_firstBig.mp hj).2.2 p hp he.symm
  have hFC : Disjoint (firstBig n D P) C := by
    apply Finset.disjoint_left.mpr
    intro j hj hc
    have hb := (mem_firstBig.mp hj).2.1
    have hs := (hC j hc).2
    omega
  have hsub : (firstBig n D P ∪ T) ∪ C ⊆ Finset.range D.length := by
    intro j hj
    rcases Finset.mem_union.mp hj with hj | hj
    · rcases Finset.mem_union.mp hj with hj | hj
      · exact Finset.mem_range.mpr (mem_firstBig.mp hj).1
      · exact Finset.mem_range.mpr (hT j hj)
    · exact Finset.mem_range.mpr (hC j hj).1
  have hs := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hFC,hdis⟩),
    Finset.card_union_of_disjoint hFT,Finset.card_range,firstBig_card h P] at hs
  exact hs

lemma tight_firstBig {n : Nat} {D : Dag} (h : Strict n D) (P : Finset (Fin n))
    (T C : Finset Nat) (hT : ∀ j ∈ T, j < D.length)
    (hC : ∀ j ∈ C, j < D.length ∧ (supp n D (n+j) ∩ P).card ≤ 1)
    (hdis : Disjoint T C)
    (copy : ∀ j ∈ T, ∃ p, p < n+j ∧ supp n D (n+j) ∩ P = supp n D p ∩ P)
    (tcard : T.card = 8) (ccard : 3 ≤ C.card) (fcard : (bigFamily n D P).card = 8)
    (size : D.length ≤ 19) :
    ∀ j, j < D.length → j ∉ T → 2 ≤ (supp n D (n+j) ∩ P).card →
      j ∈ firstBig n D P := by
  classical
  have bound := copy_budget h P T C hT hC hdis copy
  have hc : C.card = 3 := by omega
  have hf : (firstBig n D P).card = 8 := (firstBig_card h P).trans fcard
  have hFT : Disjoint (firstBig n D P) T := by
    apply Finset.disjoint_left.mpr
    intro j hj ht
    obtain ⟨p,hp,he⟩ := copy j ht
    exact (mem_firstBig.mp hj).2.2 p hp he.symm
  have hFC : Disjoint (firstBig n D P) C := by
    apply Finset.disjoint_left.mpr
    intro j hj hc
    have hb := (mem_firstBig.mp hj).2.1
    have hs := (hC j hc).2
    omega
  have hsub : (firstBig n D P ∪ T) ∪ C ⊆ Finset.range D.length := by
    intro j hj
    rcases Finset.mem_union.mp hj with hj | hj
    · rcases Finset.mem_union.mp hj with hj | hj
      · exact Finset.mem_range.mpr (mem_firstBig.mp hj).1
      · exact Finset.mem_range.mpr (hT j hj)
    · exact Finset.mem_range.mpr (hC j hj).1
  have huc : ((firstBig n D P ∪ T) ∪ C).card = 19 := by
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hFC,hdis⟩),
      Finset.card_union_of_disjoint hFT,hf,tcard,hc]
  have heq : (firstBig n D P ∪ T) ∪ C = Finset.range D.length := by
    apply Finset.eq_of_subset_of_card_le hsub
    simp only [Finset.card_range,huc]
    exact size
  intro j hj ht hb
  have hmem : j ∈ (firstBig n D P ∪ T) ∪ C := heq ▸ Finset.mem_range.mpr hj
  rcases Finset.mem_union.mp hmem with hm | hc
  · exact (Finset.mem_union.mp hm).resolve_right ht
  · have hs := (hC j hc).2
    omega

end LabelBudget


namespace TightFour
open PEqualNP.Outside.L_meta_2590_aux.DagTools
open Four SevenGeneral Thirteen EightSupport LabelBudget LabelRigidity DagRigidity

lemma tight_partition {n : Nat} {D : Dag} (h : Strict n D) (P : Finset (Fin n))
    (T C : Finset Nat) (hT : ∀ j ∈ T, j < D.length)
    (hC : ∀ j ∈ C, j < D.length ∧ (supp n D (n+j) ∩ P).card ≤ 1)
    (hdis : Disjoint T C)
    (copy : ∀ j ∈ T, ∃ p, p < n+j ∧ supp n D (n+j) ∩ P = supp n D p ∩ P)
    (tcard : T.card = 8) (ccard : 3 ≤ C.card) (fcard : (bigFamily n D P).card = 8)
    (size : D.length ≤ 19) :
    C.card = 3 ∧ D.length = 19 ∧
      (firstBig n D P ∪ T) ∪ C = Finset.range D.length := by
  classical
  have bound := copy_budget h P T C hT hC hdis copy
  have hc : C.card = 3 := by omega
  have hn : D.length = 19 := by omega
  have hf : (firstBig n D P).card = 8 := (firstBig_card h P).trans fcard
  have hFT : Disjoint (firstBig n D P) T := by
    apply Finset.disjoint_left.mpr
    intro j hj ht
    obtain ⟨p,hp,he⟩ := copy j ht
    exact (mem_firstBig.mp hj).2.2 p hp he.symm
  have hFC : Disjoint (firstBig n D P) C := by
    apply Finset.disjoint_left.mpr
    intro j hj hc
    have hb := (mem_firstBig.mp hj).2.1
    have hs := (hC j hc).2
    omega
  have hsub : (firstBig n D P ∪ T) ∪ C ⊆ Finset.range D.length := by
    intro j hj
    rcases Finset.mem_union.mp hj with hj | hj
    · rcases Finset.mem_union.mp hj with hj | hj
      · exact Finset.mem_range.mpr (mem_firstBig.mp hj).1
      · exact Finset.mem_range.mpr (hT j hj)
    · exact Finset.mem_range.mpr (hC j hj).1
  have huc : ((firstBig n D P ∪ T) ∪ C).card = 19 := by
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hFC,hdis⟩),
      Finset.card_union_of_disjoint hFT,hf,tcard,hc]
  refine ⟨hc,hn,Finset.eq_of_subset_of_card_le hsub ?_⟩
  simp only [Finset.card_range,huc]
  exact size

lemma four_targets {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (zero : Bzero 10 D = 0) (four : (ineligSet 10 D).card = 4) :
    (eligSet 10 D).card ≤ 6 ∧
    (nbhdFamily (ineligSet 10 D)).card = 4 ∧
    (∀ M ∈ nbhdFamily (ineligSet 10 D), M.card = 3 ∧ sup_Occ 10 D (eligSet 10 D) M) ∧
    (∀ M ∈ nbhdFamily (ineligSet 10 D), ∀ N ∈ nbhdFamily (ineligSet 10 D),
      M ≠ N → (M ∩ N).card ≤ 1) := by
  classical
  let S := ineligSet 10 D
  have hind : ∀ a ∈ S, ∀ b ∈ S, ¬ Adj a b := by
    intro a ha b hb hab
    rcases sem_elig_cover graph_ok h hc hab with ea | eb
    · exact (sem_mem_inelig.mp ha) ea
    · exact (sem_mem_inelig.mp hb) eb
  have geo := all_four_geometry S four hind
  have compl : complement S = eligSet 10 D := by
    ext v
    simp [complement,S,ineligSet]
  have occ (M) (hm : M ∈ nbhdFamily S) : sup_Occ 10 D (complement S) M := by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨j,s,_,_,hs⟩ := exact_non_neighbors graph_ok h.1 hc (complement S) i
      (sem_noempty_chain_out graph_ok h hc zero hi) (geo.1 i hi)
    refine ⟨src D (j,s),?_⟩
    ext a
    simp only [nbrs,Finset.mem_inter,Finset.mem_filter]
    exact ⟨fun ⟨ha,he⟩ => ⟨he,(hs a he).1 ha⟩,
      fun ⟨he,ha⟩ => ⟨(hs a he).2 ha,he⟩⟩
  have hc6 : (eligSet 10 D).card ≤ 6 := by
    have hn := inelig_card_add 10 D
    omega
  refine ⟨hc6,geo.2.2.1,?_,geo.2.2.2.2⟩
  intro M hm
  exact ⟨geo.2.2.2.1 M hm,by simpa only [compl] using occ M hm⟩

lemma rows_copy_support {D : Dag} {k : Fin 5}
    (hk : casesI k = ineligSet 10 D) {u v : Nat}
    (he : ∀ r : Fin 13, val D (caseRow k r) u = val D (caseRow k r) v) :
    supp 10 D u ∩ eligSet 10 D = supp 10 D v ∩ eligSet 10 D := by
  classical
  ext a
  simp only [Finset.mem_inter]
  by_cases ha : a ∈ eligSet 10 D
  · have hai : a ∉ casesI k := by
      rw [hk]
      intro hai
      exact (sem_mem_inelig.mp hai) ha
    obtain ⟨r,hr⟩ := cases_singletons13 k a hai
    have hv := he r
    rw [hr] at hv
    simp only [ha,and_true,mem_supp]
    exact hv ▸ Iff.rfl
  · simp only [ha,and_false]

lemma tight_four {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (zero : Bzero 10 D = 0) (four : (ineligSet 10 D).card = 4)
    (size : D.length ≤ 19) :
    ∃ k : Fin 5, casesI k = ineligSet 10 D ∧ ∃ T C : Finset Nat,
      T.card = 8 ∧ C.card = 3 ∧ D.length = 19 ∧ Disjoint T C ∧
      (∀ j ∈ T, j < D.length ∧
        (tag D j = true → supp 10 D (10+j) ∩ eligSet 10 D = ∅) ∧
        ∃ p, p < 10+j ∧ ∀ r : Fin 13,
          val D (caseRow k r) (10+j) = val D (caseRow k r) p) ∧
      (∀ j ∈ C, j < D.length ∧ tag D j = true ∧
        (supp 10 D (10+j) ∩ eligSet 10 D).card ≤ 1) ∧
      (firstBig 10 D (eligSet 10 D) ∪ T) ∪ C = Finset.range D.length ∧
      (bigFamily 10 D (eligSet 10 D)).card = 8 ∧
      (∀ M ∈ bigFamily 10 D (eligSet 10 D) \ nbhdFamily (ineligSet 10 D),
        M.card = 2 ∧ ∃ N ∈ nbhdFamily (ineligSet 10 D), M ⊆ N) ∧
      (∀ N ∈ nbhdFamily (ineligSet 10 D),
        ∃ M ∈ bigFamily 10 D (eligSet 10 D) \ nbhdFamily (ineligSet 10 D),
          M.card = 2 ∧ M ⊆ N) ∧
      (∀ j, j < D.length → tag D j = true →
        (supp 10 D (10+j) ∩ eligSet 10 D).card ≤ 1) ∧
      (∀ j, j < D.length → j ∉ T → (tag D j = true ↔ j ∈ C)) := by
  classical
  obtain ⟨k,hk,T,ht,hT⟩ := eight_copies_and_support h hc four
  obtain ⟨C,hcc,hCT,hC⟩ := SevenRows.charged_package h.1 hc k T
    (fun j hj => ⟨(hT j hj).1,(hT j hj).2.2⟩)
  have hd : Disjoint T C := hCT.symm
  have hsupp (w : Nat) : supp 10 D w \ casesI k = supp 10 D w ∩ eligSet 10 D := by
    rw [hk]
    ext a
    simp [ineligSet]
  have hCs : ∀ j ∈ C, j < D.length ∧ tag D j = true ∧
      (supp 10 D (10+j) ∩ eligSet 10 D).card ≤ 1 := by
    intro j hj
    obtain ⟨hl,ha,hsmall⟩ := hC j hj
    exact ⟨hl,ha,by simpa only [hsupp] using hsmall⟩
  have hCb : ∀ j ∈ C, j < D.length ∧
      (supp 10 D (10+j) ∩ eligSet 10 D).card ≤ 1 :=
    fun j hj => ⟨(hCs j hj).1,(hCs j hj).2.2⟩
  have hTb : ∀ j ∈ T, j < D.length := fun j hj => (hT j hj).1
  have copy : ∀ j ∈ T, ∃ p, p < 10+j ∧
      supp 10 D (10+j) ∩ eligSet 10 D = supp 10 D p ∩ eligSet 10 D := by
    intro j hj
    obtain ⟨p,hp,hr⟩ := (hT j hj).2.2
    exact ⟨p,hp,rows_copy_support hk hr⟩
  have budget := copy_budget h.1 (eligSet 10 D) T C hTb hCb hd copy
  have fb : (bigFamily 10 D (eligSet 10 D)).card ≤ 8 := by omega
  obtain ⟨hp,hl,hL,hi⟩ := four_targets h hc zero four
  obtain ⟨hf,pairs,hprivate⟩ := family_rigid_of_label_card h.1 (eligSet 10 D) hp
    (nbhdFamily (ineligSet 10 D)) hl hL hi fb
  obtain ⟨cc,sz,partition⟩ := tight_partition h.1 (eligSet 10 D) T C hTb hCb hd copy ht hcc hf size
  have first_or : ∀ j ∈ firstBig 10 D (eligSet 10 D), tag D j = false := by
    intro j hj
    obtain ⟨hlj,hbig,hfresh⟩ := mem_firstBig.mp hj
    exact fresh_big_gate_or h.1 (eligSet 10 D) hp (nbhdFamily (ineligSet 10 D))
      hl hL hi fb hlj hbig hfresh
  have member : ∀ j, j < D.length → j ∈ firstBig 10 D (eligSet 10 D) ∨ j ∈ T ∨ j ∈ C := by
    intro j hj
    have hm : j ∈ (firstBig 10 D (eligSet 10 D) ∪ T) ∪ C :=
      partition ▸ Finset.mem_range.mpr hj
    simpa only [Finset.mem_union,or_assoc] using hm
  refine ⟨k,hk,T,C,ht,cc,sz,hd,hT,hCs,partition,hf,pairs,hprivate,?_,?_⟩
  · intro j hj ha
    rcases member j hj with hf | ht | hc
    · exact False.elim (Bool.false_ne_true ((first_or j hf).symm.trans ha))
    · rw [(hT j ht).2.1 ha,Finset.card_empty]
      omega
    · exact (hCs j hc).2.2
  · intro j hj hn
    constructor
    · intro ha
      rcases member j hj with hf | ht | hc
      · exact False.elim (Bool.false_ne_true ((first_or j hf).symm.trans ha))
      · exact False.elim (hn ht)
      · exact hc
    · intro hc
      exact (hCs j hc).2.1

end TightFour


namespace TightFour
open PEqualNP.Outside.L_meta_2590_aux.DagTools
open Four SevenGeneral Thirteen EightSupport LabelBudget LabelRigidity DagRigidity

lemma fresh_or_inputs {n : Nat} {D : Dag} (h : Strict n D) (P : Finset (Fin n))
    {j : Nat} (hj : j < D.length) (ht : tag D j = false)
    (fresh : ∀ w, w < n+j → supp n D w ∩ P ≠ supp n D (n+j) ∩ P) :
    (supp n D (opA D j) ∩ P).Nonempty ∧
    (supp n D (opB D j) ∩ P).Nonempty ∧
    supp n D (opA D j) ∩ P ⊂ supp n D (n+j) ∩ P ∧
    supp n D (opB D j) ∩ P ⊂ supp n D (n+j) ∩ P ∧
    supp n D (n+j) ∩ P = (supp n D (opA D j) ∩ P) ∪ (supp n D (opB D j) ∩ P) := by
  classical
  have hu : supp n D (n+j) ∩ P =
      (supp n D (opA D j) ∩ P) ∪ (supp n D (opB D j) ∩ P) := by
    rw [sem_supp_or h hj ht,Finset.union_inter_distrib_right]
  obtain ⟨hla,hlb,_⟩ := h j hj
  have hna := fresh (opA D j) hla
  have hnb := fresh (opB D j) hlb
  have ha : supp n D (opA D j) ∩ P ⊆ supp n D (n+j) ∩ P :=
    hu ▸ Finset.subset_union_left
  have hb : supp n D (opB D j) ∩ P ⊆ supp n D (n+j) ∩ P :=
    hu ▸ Finset.subset_union_right
  refine ⟨?_,?_,Finset.ssubset_iff_subset_ne.mpr ⟨ha,hna⟩,
    Finset.ssubset_iff_subset_ne.mpr ⟨hb,hnb⟩,hu⟩
  · by_contra he
    have hz := Finset.not_nonempty_iff_eq_empty.mp he
    rw [hz,Finset.empty_union] at hu
    exact hnb hu.symm
  · by_contra he
    have hz := Finset.not_nonempty_iff_eq_empty.mp he
    rw [hz,Finset.union_empty] at hu
    exact hna hu.symm

lemma fresh_pair_inputs {n : Nat} {D : Dag} (h : Strict n D) (P : Finset (Fin n))
    {j : Nat} (hj : j < D.length) (ht : tag D j = false)
    (pair : (supp n D (n+j) ∩ P).card = 2)
    (fresh : ∀ w, w < n+j → supp n D w ∩ P ≠ supp n D (n+j) ∩ P) :
    (supp n D (opA D j) ∩ P).card = 1 ∧
    (supp n D (opB D j) ∩ P).card = 1 := by
  obtain ⟨ha,hb,hsa,hsb,_⟩ := fresh_or_inputs h P hj ht fresh
  have hap := Finset.card_pos.mpr ha
  have hbp := Finset.card_pos.mpr hb
  have hal := Finset.card_lt_card hsa
  have hbl := Finset.card_lt_card hsb
  constructor <;> omega

lemma tight_four_pool {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (zero : Bzero 10 D = 0) (four : (ineligSet 10 D).card = 4)
    (size : D.length ≤ 19) :
    ∃ k : Fin 5, casesI k = ineligSet 10 D ∧ ∃ T C : Finset Nat,
      T.card = 8 ∧ C.card = 3 ∧ Disjoint T C ∧
      (∀ j ∈ T, j < D.length ∧ ∃ p, p < 10+j ∧ ∀ r : Fin 13,
          val D (caseRow k r) (10+j) = val D (caseRow k r) p) ∧
      (∀ j ∈ C, j < D.length ∧ tag D j = true ∧
        (supp 10 D (10+j) ∩ eligSet 10 D).card ≤ 1) ∧
      (∀ j, j < D.length → j ∉ T → j ∉ C →
        j ∈ firstBig 10 D (eligSet 10 D) ∧ tag D j = false ∧
        ((supp 10 D (10+j) ∩ eligSet 10 D).card = 2 ∧
          ∃ N ∈ nbhdFamily (ineligSet 10 D), supp 10 D (10+j) ∩ eligSet 10 D ⊆ N) ∨
        (j ∈ firstBig 10 D (eligSet 10 D) ∧ tag D j = false ∧
          supp 10 D (10+j) ∩ eligSet 10 D ∈ nbhdFamily (ineligSet 10 D))) := by
  classical
  obtain ⟨k,hk,T,C,ht,hc3,_,hd,hT,hC,hpart,hf,hpairs,_,_,hiff⟩ :=
    tight_four h hc zero four size
  refine ⟨k,hk,T,C,ht,hc3,hd,(fun j hj => ⟨(hT j hj).1,(hT j hj).2.2⟩),hC,?_⟩
  intro j hj hnt hnc
  have hm : j ∈ (firstBig 10 D (eligSet 10 D) ∪ T) ∪ C :=
    hpart ▸ Finset.mem_range.mpr hj
  have hjf : j ∈ firstBig 10 D (eligSet 10 D) :=
    (Finset.mem_union.mp ((Finset.mem_union.mp hm).resolve_right hnc)).resolve_right hnt
  have hor : tag D j = false := by
    cases he : tag D j
    · rfl
    · exact False.elim (hnc ((hiff j hj hnt).mp he))
  have memfam : supp 10 D (10+j) ∩ eligSet 10 D ∈ bigFamily 10 D (eligSet 10 D) :=
    mem_bigFamily h.1 (mem_firstBig.mp hjf).2.1 ⟨10+j,rfl⟩
  by_cases hN : supp 10 D (10+j) ∩ eligSet 10 D ∈ nbhdFamily (ineligSet 10 D)
  · exact Or.inr ⟨hjf,hor,hN⟩
  · exact Or.inl ⟨hjf,hor,hpairs _ (Finset.mem_sdiff.mpr ⟨memfam,hN⟩)⟩

end TightFour


namespace PoolDag
open PEqualNP.Outside.L_meta_2590_aux.DagTools
open PEqualNP.Outside.L_meta_2590_aux.Thirteen
open PEqualNP.Outside.L_meta_2590_aux.SevenRows
open PEqualNP.Outside.L_meta_2590_aux.SevenGeneral
open PEqualNP.Outside.L_meta_2590_aux.Four

def inputs (k : Fin 5) : List Nat := List.ofFn (fun v => liftMask (casesMasks k v))
def mask (D : Dag) (k : Fin 5) (w : Nat) : Nat := (run D (inputs k)).getD w 0

set_option maxHeartbeats 0 in
lemma input_small : ∀ k : Fin 5, ∀ v : Fin 10, liftMask (casesMasks k v) < 2^13 := by
  decide +kernel

lemma mask_small (D : Dag) (k : Fin 5) (w : Nat) : mask D k w < 2^13 := by
  apply getD_lt_two_pow
  apply run_lt_two_pow
  intro v hv
  obtain ⟨a,ha⟩ := List.mem_ofFn.mp hv
  rw [← ha]
  exact input_small k a

lemma mask_bit (D : Dag) (k : Fin 5) (w : Nat) (r : Nat) :
    (mask D k w).testBit r = val D (fun v => (liftMask (casesMasks k v)).testBit r) w :=
  run_testBit_val D (fun v => liftMask (casesMasks k v)) r w

lemma mask_gate {D : Dag} (h : Strict 10 D) (k : Fin 5) {j : Nat} (hj : j < D.length) :
    mask D k (10+j) = if tag D j then
      mask D k (opA D j) &&& mask D k (opB D j)
    else mask D k (opA D j) ||| mask D k (opB D j) := by
  apply Nat.eq_of_testBit_eq
  intro r
  cases ht : tag D j <;>
    simp only [ht,Bool.false_eq_true,↓reduceIte,Nat.testBit_or,Nat.testBit_and,mask_bit]
  · exact (val_gate h _ j hj).trans (by simp [ht,gop_false])
  · exact (val_gate h _ j hj).trans (by simp [ht,gop_true])

lemma mask_copy (D : Dag) (k : Fin 5) {a b : Nat}
    (eqrows : ∀ r : Fin 13, val D (caseRow k r) a = val D (caseRow k r) b) :
    mask D k a = mask D k b := by
  apply nat_eq_of_low_testBits (mask_small D k a) (mask_small D k b)
  intro r
  rw [mask_bit,mask_bit]
  exact eqrows r

lemma mask_input (D : Dag) (k : Fin 5) {v : Nat} (hv : v < 10) :
    mask D k v = liftMask (casesMasks k ⟨v,hv⟩) := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [mask_bit,val_input D _ v hv]

lemma value_mem_prefix (f : Nat → Nat) (n len : Nat) {j w : Nat}
    (hj : j ≤ len) (hw : w < n+j) :
    f w ∈ (List.range n).map f ++ ((List.range len).map (fun t => f (n+t))).take j := by
  by_cases hi : w < n
  · exact List.mem_append_left _ (List.mem_map.mpr ⟨w,List.mem_range.mpr hi,rfl⟩)
  · apply List.mem_append_right
    simp only [← List.map_take,List.take_range]
    exact List.mem_map.mpr ⟨w-n,List.mem_range.mpr (by omega),by congr 1;omega⟩

end PoolDag


namespace PoolProgram
open PEqualNP.Outside.L_meta_2590_aux.MaskGeometry

def FreeValue (previous : List Nat) (v : Nat) : Prop :=
  v ∈ previous ∨ v ∈ triples ∨ ∃ i j : Fin 6,
    (i.val,j.val) ∈ pairIndices ∧ ∃ a ∈ previous, ∃ b ∈ previous,
      a / 128 = 2^i.val ∧ b / 128 = 2^j.val ∧ v = a ||| b

def AndValue (previous : List Nat) (v : Nat) : Prop :=
  [0,1,2,4,8,16,32].contains (v/128) = true ∧
    ∃ a ∈ previous, ∃ b ∈ previous, v = a &&& b

end PoolProgram


namespace PoolClassify

open PEqualNP.Outside.L_meta_2590_aux.DagTools
open Four SevenGeneral PoolDag PoolProgram

abbrev initials (D : Dag) (k : Fin 5) : List Nat := (List.range 10).map (mask D k)
abbrev values (D : Dag) (k : Fin 5) : List Nat :=
  (List.range D.length).map (fun j => mask D k (10+j))

lemma previous_mem (D : Dag) (k : Fin 5) {j w : Nat} (hj : j ≤ D.length) (hw : w < 10+j) :
    mask D k w ∈ initials D k ++ (values D k).take j :=
  value_mem_prefix (mask D k) 10 D.length hj hw

lemma initial_allowed (D : Dag) (k : Fin 5) :
    ∀ v ∈ initials D k, v ∈ 0 :: MaskGeometry.inputs := by
  intro v hv
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hv
  have hw' := List.mem_range.mp hw
  rw [mask_input D k hw']
  exact ((MaskGeometry.geometry k).2.2.2.1 ⟨w,hw'⟩).2

lemma target_mem {D : Dag} (hc : sem_Comp 10 Adj D) (k : Fin 5) :
    7 ∈ initials D k ++ values D k := by
  have hbound : outW 10 D < 10+D.length := by unfold outW; omega
  have hm := previous_mem D k (j := D.length) le_rfl hbound
  have target : mask D k (outW 10 D) = 7 := MaskGeometry.sig_output hc k
  have take : (values D k).take D.length = values D k := by
    simp [values,← List.map_take,List.take_range]
  simpa only [target,take] using hm

lemma classified_nat {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (zero : Bzero 10 D = 0) (four : (ineligSet 10 D).card = 4) (size : D.length ≤ 19) :
    ∃ k : Fin 5, ∃ C : Finset Nat, C.card = 3 ∧ (∀ j ∈ C, j < D.length) ∧
      ∀ j, j < D.length →
        (j ∈ C → AndValue (initials D k ++ (values D k).take j) (mask D k (10+j))) ∧
        (j ∉ C → FreeValue (initials D k ++ (values D k).take j) (mask D k (10+j))) := by
  classical
  obtain ⟨k,hk,T,C,_,hcc,_,hT,hC,hrest⟩ := TightFour.tight_four_pool h hc zero four size
  have compl : complement (casesI k) = eligSet 10 D := by
    rw [hk]
    ext v
    simp [complement,ineligSet]
  have projected (w : Nat) : MaskGeometry.project D k w = supp 10 D w ∩ eligSet 10 D := by
    simp only [MaskGeometry.project,compl]
  refine ⟨k,C,hcc,fun j hj => (hC j hj).1,?_⟩
  intro j hj
  have memA := previous_mem D k hj.le (h.1 j hj).1
  have memB := previous_mem D k hj.le (h.1 j hj).2.1
  constructor
  · intro hinc
    have cg := hC j hinc
    refine ⟨?_,mask D k (opA D j),memA,mask D k (opB D j),memB,?_⟩
    · apply List.contains_iff_mem.mpr
      apply MaskGeometry.sig_high_small
      simpa only [projected] using cg.2.2
    · simpa only [cg.2.1,Bool.true_eq,ite_true] using mask_gate h.1 k hj
  · intro hnc
    by_cases hnt : j ∈ T
    · obtain ⟨_,p,hp,hr⟩ := hT j hnt
      apply Or.inl
      have eq := mask_copy D k hr
      rw [eq]
      exact previous_mem D k hj.le hp
    · rcases hrest j hj hnt hnc with ⟨hf,ht,hpair,N,hN,hsub⟩ | ⟨hf,ht,hN⟩
      · have fresh := (LabelBudget.mem_firstBig.mp hf).2.2
        obtain ⟨ca,cb⟩ := TightFour.fresh_pair_inputs h.1 (eligSet 10 D) hj ht hpair fresh
        obtain ⟨u,hu⟩ := Finset.card_eq_one.mp ca
        obtain ⟨v,hv⟩ := Finset.card_eq_one.mp cb
        have ha : MaskGeometry.project D k (opA D j) = {u} := by rw [projected,hu]
        have hb : MaskGeometry.project D k (opB D j) = {v} := by rw [projected,hv]
        have he : MaskGeometry.project D k (10+j) = {u,v} := by
          rw [projected,sem_supp_or h.1 hj ht,Finset.union_inter_distrib_right,hu,hv]
          simp
        have hne : u ≠ v := by
          intro huv
          have eqc : (MaskGeometry.project D k (10+j)).card = 1 := by simp [he,huv]
          rw [projected,hpair] at eqc
          omega
        obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hN
        have hi' : i ∈ casesI k := hk ▸ hi
        have hs : {u,v} ⊆ nbrs (casesI k) i := by
          rw [← he,projected,hk]
          exact hsub
        obtain ⟨x,y,hx,hy,hxy | hyx⟩ := MaskGeometry.pair_sources_codes hi' ha hb hne hs
        · apply Or.inr
          apply Or.inr
          refine ⟨x,y,hxy,mask D k (opA D j),memA,mask D k (opB D j),memB,hx,hy,?_⟩
          simpa only [ht,Bool.false_eq_true,ite_false] using mask_gate h.1 k hj
        · apply Or.inr
          apply Or.inr
          refine ⟨y,x,hyx,mask D k (opB D j),memB,mask D k (opA D j),memA,hy,hx,?_⟩
          simpa only [ht,Bool.false_eq_true,ite_false,Nat.or_comm] using mask_gate h.1 k hj
      · apply Or.inr
        apply Or.inl
        obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hN
        apply MaskGeometry.sig_neighborhood_mem h.1 k (10+j) i (hk ▸ hi)
        rw [projected,hk]
        exact he.symm

lemma fin_filter_card (n : Nat) (C : Finset Nat) (hc : ∀ j ∈ C, j < n) :
    ((Finset.univ : Finset (Fin n)).filter (fun j => j.val ∈ C)).card = C.card := by
  apply Finset.card_bij (fun j _ => j.val)
  · intro j hj
    exact (Finset.mem_filter.mp hj).2
  · intro i hi j hj eq
    exact Fin.ext eq
  · intro j hj
    exact ⟨⟨j,hc j hj⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩,rfl⟩

lemma values_get (D : Dag) (k : Fin 5) (j : Fin (values D k).length) :
    (values D k).get j = mask D k (10+j.val) := by
  simp [values,List.get_eq_getElem]

lemma classified_program {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (zero : Bzero 10 D = 0) (four : (ineligSet 10 D).card = 4) (size : D.length ≤ 19) :
    ∃ k : Fin 5, ∃ C : Finset (Fin (values D k).length), C.card = 3 ∧
      (∀ v ∈ initials D k, v ∈ 0 :: MaskGeometry.inputs) ∧
      7 ∈ initials D k ++ values D k ∧
      ∀ j : Fin (values D k).length,
        (j ∈ C → AndValue (initials D k ++ (values D k).take j.val) ((values D k).get j)) ∧
        (j ∉ C → FreeValue (initials D k ++ (values D k).take j.val) ((values D k).get j)) := by
  classical
  obtain ⟨k,C,hcard,hvalid,hclass⟩ := classified_nat h hc zero four size
  let S : Finset (Fin (values D k).length) := Finset.univ.filter (fun j => j.val ∈ C)
  refine ⟨k,S,?_,initial_allowed D k,target_mem hc k,?_⟩
  · rw [fin_filter_card _ C (by simpa only [values,List.length_map,List.length_range] using hvalid)]
    exact hcard
  · intro j
    have hj : j.val < D.length := by simpa only [values,List.length_map,List.length_range] using j.isLt
    have hh := hclass j.val hj
    simpa only [S,Finset.mem_filter,Finset.mem_univ,true_and,values_get] using hh

end PoolClassify


namespace RigidClosure

def inputs : List Nat := [177, 329, 538, 1068, 2146, 4180]
def triples : List Nat := [1919, 4863, 3327, 6527]
def pairIndices : List (Nat × Nat) := [(0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (2, 5), (3, 4), (4, 5)]

def low (v : Nat) : Bool := [0, 1, 2, 4, 8, 16, 32].contains (v / 128)

def lowAt (gs : List Nat) (i : Nat) : List Nat :=
  [inputs.getD i 0] ++ gs.filter (fun v => v / 128 == 2 ^ i)

def pool (gs : List Nat) : List Nat :=
  ([0, 8191] ++ inputs ++ triples ++
    pairIndices.flatMap (fun (ij : Nat × Nat) => (lowAt gs ij.1).flatMap
      (fun a => (lowAt gs ij.2).map (fun b => a ||| b))) ++ gs).eraseDups

def ands (xs : List Nat) : List Nat :=
  ((xs.flatMap (fun a => xs.map (fun b => a &&& b))).filter low).eraseDups

def lastOK (gs : List Nat) : Bool :=
  let good := (pool gs).filter (fun v => v &&& 7 == 7)
  good.all (fun a => good.all (fun b => a &&& b != 7))

def caseOK (a : Nat) : Bool :=
  (ands (pool [a])).all (fun b => lastOK [a, b])

def firsts : List Nat := [0, 1, 2, 4, 8, 9, 10, 12, 16, 17, 18, 20, 24, 25, 26, 28, 29, 32, 33, 34, 36, 40, 41, 42, 43, 44, 48, 49, 50, 52, 54, 59, 61, 62, 64, 65, 66, 68, 72, 73, 74, 76, 78, 80, 81, 82, 83, 84, 91, 93, 94, 96, 97, 98, 100, 101, 107, 109, 110, 115, 117, 118, 177, 179, 181, 185, 187, 189, 241, 243, 245, 255, 329, 331, 333, 345, 347, 349, 361, 363, 365, 383, 538, 539, 542, 570, 571, 574, 602, 603, 606, 639, 1068, 1069, 1070, 1084, 1085, 1086, 1132, 1133, 1134, 1151, 2146, 2147, 2150, 2154, 2155, 2158, 2162, 2163, 2166, 2175, 4180, 4181, 4182, 4188, 4189, 4190, 4212, 4213, 4214, 4223]

end RigidClosure


namespace RigidClosure

lemma raw_high (i : Fin 6) : inputs.getD i.val 0 / 128 = 2 ^ i.val := by
  revert i
  decide +kernel

lemma base_singleton : ∀ i : Fin 6, ∀ v ∈ [0, 8191] ++ inputs ++ triples,
    v / 128 = 2 ^ i.val → v = inputs.getD i.val 0 := by decide +kernel

lemma pair_laws : pairIndices.all
    (fun p => decide (p.1 < 6 ∧ p.2 < 6 ∧ p.1 ≠ p.2)) = true := by decide +kernel

lemma pair_not_singleton : ∀ i j k : Fin 6, i ≠ j →
    (2 ^ i.val ||| 2 ^ j.val) ≠ 2 ^ k.val := by decide +kernel

lemma div_or (a b : Nat) : (a ||| b) / 128 = a / 128 ||| b / 128 := by
  simpa [Nat.shiftRight_eq_div_pow] using
    (Nat.shiftRight_or_distrib (a := a) (b := b) (i := 7))

lemma lowAt_label {gs : List Nat} {i v : Nat} (hi : i < 6)
    (hv : v ∈ lowAt gs i) : v / 128 = 2 ^ i := by
  simp only [lowAt, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_filter] at hv
  rcases hv with rfl | ⟨_, hv⟩
  · exact raw_high ⟨i, hi⟩
  · simpa using hv

lemma lowAt_mono {xs ys : List Nat} (h : xs ⊆ ys) (i : Nat) :
    lowAt xs i ⊆ lowAt ys i := by
  intro v hv
  simp only [lowAt, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_filter] at hv ⊢
  rcases hv with hraw | ⟨hv, hlabel⟩
  · exact Or.inl hraw
  · exact Or.inr ⟨h hv, hlabel⟩

lemma pool_mono {xs ys : List Nat} (h : xs ⊆ ys) : pool xs ⊆ pool ys := by
  intro v hv
  simp only [pool, List.mem_eraseDups, List.mem_append, or_assoc] at hv ⊢
  rcases hv with h0 | h1 | h2 | hp | hg
  · exact Or.inl h0
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (Or.inl h2))
  · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    obtain ⟨ij, hij, a, ha, b, hb, rfl⟩ :=
      (show ∃ ij ∈ pairIndices, ∃ a ∈ lowAt xs ij.1,
        ∃ b ∈ lowAt xs ij.2, a ||| b = v from by
        simpa only [List.mem_flatMap, List.mem_map] using hp)
    exact List.mem_flatMap.mpr ⟨ij, hij, List.mem_flatMap.mpr
      ⟨a, lowAt_mono h _ ha, List.mem_map.mpr ⟨b, lowAt_mono h _ hb, rfl⟩⟩⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr (h hg))))

lemma mem_pool_self {gs : List Nat} {v : Nat} (hv : v ∈ gs) : v ∈ pool gs := by
  exact List.mem_eraseDups.mpr (List.mem_append_right _ hv)

lemma mem_pool_inputs (gs : List Nat) {v : Nat} (hv : v ∈ inputs) : v ∈ pool gs := by
  simp only [pool, List.mem_eraseDups, List.mem_append, or_assoc]
  exact Or.inr (Or.inl hv)

lemma mem_pool_triples (gs : List Nat) {v : Nat} (hv : v ∈ triples) : v ∈ pool gs := by
  simp only [pool, List.mem_eraseDups, List.mem_append, or_assoc]
  exact Or.inr (Or.inr (Or.inl hv))

lemma mem_pool_pair {gs : List Nat} {i j a b : Nat}
    (hij : (i, j) ∈ pairIndices) (ha : a ∈ lowAt gs i) (hb : b ∈ lowAt gs j) :
    a ||| b ∈ pool gs := by
  simp only [pool, List.mem_eraseDups, List.mem_append, or_assoc]
  exact Or.inr (Or.inr (Or.inr (Or.inl (List.mem_flatMap.mpr
    ⟨(i, j), hij, List.mem_flatMap.mpr ⟨a, ha, List.mem_map.mpr ⟨b, hb, rfl⟩⟩⟩))))

lemma mem_pool_zero (gs : List Nat) : 0 ∈ pool gs := by
  simp only [pool, List.mem_eraseDups, List.mem_append, or_assoc]
  exact Or.inl (by simp)

lemma lowAt_of_mem_pool {gs : List Nat} {i v : Nat} (hi : i < 6)
    (hv : v ∈ pool gs) (hlabel : v / 128 = 2 ^ i) : v ∈ lowAt gs i := by
  rw [pool, List.mem_eraseDups] at hv
  rcases List.mem_append.mp hv with hv | hv
  · rcases List.mem_append.mp hv with hbase | hpair
    · have hvEq := base_singleton ⟨i, hi⟩ v hbase hlabel
      simp [lowAt, hvEq]
    · obtain ⟨ij, hij, a, ha, b, hb, rfl⟩ :=
        (show ∃ ij ∈ pairIndices, ∃ a ∈ lowAt gs ij.1,
          ∃ b ∈ lowAt gs ij.2, a ||| b = v from by
          simpa only [List.mem_flatMap, List.mem_map] using hpair)
      have hl : ij.1 < 6 ∧ ij.2 < 6 ∧ ij.1 ≠ ij.2 :=
        of_decide_eq_true (List.all_eq_true.mp pair_laws ij hij)
      rw [div_or, lowAt_label hl.1 ha, lowAt_label hl.2.1 hb] at hlabel
      exact False.elim (pair_not_singleton ⟨ij.1, hl.1⟩ ⟨ij.2, hl.2.1⟩ ⟨i, hi⟩
        (fun he => hl.2.2 (congrArg Fin.val he)) hlabel)
  · exact List.mem_append_right _ (List.mem_filter.mpr ⟨hv, by simp [hlabel]⟩)

lemma lowAt_ge {gs : List Nat} {i v : Nat} (hi : i < 6)
    (hv : v ∈ lowAt gs i) : 128 ≤ v := by
  have h := lowAt_label hi hv
  have hp : 0 < 2 ^ i := Nat.pow_pos (by decide)
  omega

lemma target_mem_pool_iff {gs : List Nat} : 7 ∈ pool gs ↔ 7 ∈ gs := by
  constructor
  · intro h
    rw [pool, List.mem_eraseDups] at h
    rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with hb | hp
      · have hn : 7 ∉ [0, 8191] ++ inputs ++ triples := by decide +kernel
        exact False.elim (hn hb)
      · obtain ⟨ij, hij, a, ha, b, hb, he⟩ :=
          (show ∃ ij ∈ pairIndices, ∃ a ∈ lowAt gs ij.1,
            ∃ b ∈ lowAt gs ij.2, a ||| b = 7 from by
            simpa only [List.mem_flatMap, List.mem_map] using hp)
        have hl : ij.1 < 6 ∧ ij.2 < 6 ∧ ij.1 ≠ ij.2 :=
          of_decide_eq_true (List.all_eq_true.mp pair_laws ij hij)
        have hge := lowAt_ge hl.1 ha
        have hor : a ≤ a ||| b := Nat.left_le_or
        omega
    · exact h
  · exact mem_pool_self

lemma and_mem_ands {xs : List Nat} {a b : Nat}
    (ha : a ∈ xs) (hb : b ∈ xs) (hlo : low (a &&& b) = true) :
    a &&& b ∈ ands xs := by
  apply List.mem_eraseDups.mpr
  apply List.mem_filter.mpr
  refine ⟨List.mem_flatMap.mpr ⟨a, ha, ?_⟩, hlo⟩
  exact List.mem_map.mpr ⟨b, hb, rfl⟩

def Certificate : Prop := ∀ {a b p q : Nat},
  a ∈ ands (pool []) → b ∈ ands (pool [a]) →
    p ∈ pool [a, b] → q ∈ pool [a, b] → p &&& q ≠ 7

lemma no_target_first_of_certificate (cert : Certificate) : 7 ∉ ands (pool []) := by
  intro ha
  have hm : 7 ∈ pool [7] := mem_pool_self (by simp)
  have hb : 7 ∈ ands (pool [7]) := by
    simpa using and_mem_ands hm hm (by decide : low (7 &&& 7) = true)
  have hm' : 7 ∈ pool [7, 7] := mem_pool_self (by simp)
  exact cert ha hb hm' hm' (by decide)

lemma no_target_second_of_certificate (cert : Certificate) {a : Nat}
    (ha : a ∈ ands (pool [])) : 7 ∉ ands (pool [a]) := by
  intro hb
  have hm : 7 ∈ pool [a, 7] := mem_pool_self (by simp)
  exact cert ha hb hm hm (by decide)

lemma no_target_third_of_certificate (cert : Certificate) {a b : Nat}
    (ha : a ∈ ands (pool [])) (hb : b ∈ ands (pool [a])) :
    7 ∉ ands (pool [a, b]) := by
  intro hc
  simp only [ands, List.mem_eraseDups, List.mem_filter, List.mem_flatMap,
    List.mem_map] at hc
  obtain ⟨⟨p, hp, q, hq, hpq⟩, _⟩ := hc
  exact cert ha hb hp hq hpq

lemma no_target_history_of_certificate (cert : Certificate) (hist : List Nat)
    (hlen : hist.length ≤ 3)
    (legal : ∀ j : Fin hist.length, hist.get j ∈ ands (pool (hist.take j.val))) :
    7 ∉ pool hist := by
  intro ht
  have hm := target_mem_pool_iff.mp ht
  rcases hist with _ | ⟨a, hist⟩
  · simpa using hm
  have ha := legal ⟨0, by simp⟩
  change a ∈ ands (pool []) at ha
  rcases hist with _ | ⟨b, hist⟩
  · have he : 7 = a := by simpa using hm
    subst a
    exact no_target_first_of_certificate cert ha
  have hb := legal ⟨1, by simp⟩
  change b ∈ ands (pool [a]) at hb
  rcases hist with _ | ⟨c, hist⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with he | he
    · subst a
      exact no_target_first_of_certificate cert ha
    · subst b
      exact no_target_second_of_certificate cert ha hb
  have hc := legal ⟨2, by simp⟩
  change c ∈ ands (pool [a, b]) at hc
  rcases hist with _ | ⟨d, hist⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with he | he | he
    · subst a
      exact no_target_first_of_certificate cert ha
    · subst b
      exact no_target_second_of_certificate cert ha hb
    · subst c
      exact no_target_third_of_certificate cert ha hb hc
  · simp only [List.length_cons] at hlen
    omega


end RigidClosure


namespace RigidClosure

def MaskGood (v : Nat) : Prop := ∀ r : Fin 3, v.testBit r.val = true

def Deficit (v : Nat) : Finset (Fin 4) := Finset.univ.filter (fun r => v.testBit (3+r.val) = false)

def NegLE (u v : Nat) : Prop := ∀ r : Fin 4,
  u.testBit (3+r.val) = true → v.testBit (3+r.val) = true

def MaskValid (v : Nat) : Prop := ∀ i : Fin 6,
  (v/128).testBit i.val = true → NegLE (inputs.getD i.val 0) v

lemma div_and (a b : Nat) : (a &&& b) / 128 = a / 128 &&& b / 128 := by
  simpa [Nat.shiftRight_eq_div_pow] using
    (Nat.shiftRight_and_distrib (a := a) (b := b) (i := 7))

lemma valid_and {a b : Nat} (ha : MaskValid a) (hb : MaskValid b) : MaskValid (a &&& b) := by
  intro i hi r hr
  rw [div_and,Nat.testBit_and,Bool.and_eq_true] at hi
  rw [Nat.testBit_and,ha i hi.1 r hr,hb i hi.2 r hr]
  rfl

lemma valid_or {a b : Nat} (ha : MaskValid a) (hb : MaskValid b) : MaskValid (a ||| b) := by
  intro i hi r hr
  rw [div_or,Nat.testBit_or,Bool.or_eq_true] at hi
  rw [Nat.testBit_or]
  rcases hi with hi | hi
  · rw [ha i hi r hr]
    rfl
  · rw [hb i hi r hr,Bool.or_true]

lemma good_and_left {a b : Nat} (h : MaskGood (a &&& b)) : MaskGood a := by
  intro r
  have hh := h r
  rw [Nat.testBit_and,Bool.and_eq_true] at hh
  exact hh.1

lemma good_and_right {a b : Nat} (h : MaskGood (a &&& b)) : MaskGood b := by
  intro r
  have hh := h r
  rw [Nat.testBit_and,Bool.and_eq_true] at hh
  exact hh.2

lemma deficit_and (a b : Nat) : Deficit (a &&& b) = Deficit a ∪ Deficit b := by
  ext r
  simp only [Deficit,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union,Nat.testBit_and]
  cases ha : a.testBit (3+r.val) <;> cases hb : b.testBit (3+r.val) <;> simp

lemma deficit_and_le (a b : Nat) : (Deficit (a &&& b)).card ≤ (Deficit a).card + (Deficit b).card := by
  rw [deficit_and]
  exact Finset.card_union_le _ _

lemma deficit_mono {u v : Nat} (h : NegLE u v) : Deficit v ⊆ Deficit u := by
  intro r hr
  simp only [Deficit,Finset.mem_filter,Finset.mem_univ,true_and] at hr ⊢
  cases hu : u.testBit (3+r.val)
  · rfl
  · have ht := h r hu
    rw [ht] at hr
    contradiction

lemma negLE_or {a b u v : Nat} (ha : NegLE a u) (hb : NegLE b v) : NegLE (a ||| b) (u ||| v) := by
  intro r hr
  rw [Nat.testBit_or,Bool.or_eq_true] at hr
  rw [Nat.testBit_or]
  rcases hr with hr | hr
  · rw [ha r hr]
    rfl
  · rw [hb r hr,Bool.or_true]

set_option maxHeartbeats 0 in
lemma base_valid : ∀ v ∈ [0,8191] ++ inputs ++ triples, MaskValid v := by
  unfold MaskValid NegLE inputs triples
  decide +kernel

set_option maxHeartbeats 0 in
lemma base_good_deficit : ∀ v ∈ [0,8191] ++ inputs ++ triples,
    MaskGood v → (Deficit v).card = 0 := by
  unfold MaskGood Deficit inputs triples
  decide +kernel

set_option maxHeartbeats 0 in
lemma initial_good_deficit : ∀ v ∈ pool [], MaskGood v → (Deficit v).card = 0 := by
  unfold pool lowAt inputs triples pairIndices MaskGood Deficit
  decide +kernel

set_option maxHeartbeats 0 in
lemma raw_pair_deficit : ∀ ij ∈ pairIndices,
    (Deficit (inputs.getD ij.1 0 ||| inputs.getD ij.2 0)).card ≤ 1 := by
  unfold pairIndices inputs Deficit
  decide +kernel

set_option maxHeartbeats 0 in
lemma raw_valid : ∀ i : Fin 6, MaskValid (inputs.getD i.val 0) := by
  unfold MaskValid NegLE inputs
  decide +kernel

lemma lowAt_valid {hist : List Nat} (hv : ∀ v ∈ hist, MaskValid v) {i v : Nat} (hi : i < 6)
    (hmem : v ∈ lowAt hist i) : MaskValid v := by
  simp only [lowAt,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_filter] at hmem
  rcases hmem with rfl | ⟨hm,_⟩
  · exact raw_valid ⟨i,hi⟩
  · exact hv v hm

set_option maxHeartbeats 0 in
lemma onehot_self : ∀ i : Fin 6, (2^i.val : Nat).testBit i.val = true := by decide +kernel

lemma lowAt_dominates {hist : List Nat} (hv : ∀ v ∈ hist, MaskValid v)
    {i v : Nat} (hi : i < 6) (hmem : v ∈ lowAt hist i) : NegLE (inputs.getD i 0) v := by
  apply lowAt_valid hv hi hmem ⟨i,hi⟩
  rw [lowAt_label hi hmem]
  exact onehot_self ⟨i,hi⟩

lemma pool_valid {hist : List Nat} (hv : ∀ v ∈ hist, MaskValid v) :
    ∀ v ∈ pool hist, MaskValid v := by
  intro v hm
  rw [pool,List.mem_eraseDups] at hm
  rcases List.mem_append.mp hm with hm | hm
  · rcases List.mem_append.mp hm with hb | hp
    · exact base_valid v hb
    · obtain ⟨ij,hij,a,ha,b,hb,rfl⟩ :=
        (show ∃ ij ∈ pairIndices, ∃ a ∈ lowAt hist ij.1,
          ∃ b ∈ lowAt hist ij.2, a ||| b = v from by
          simpa only [List.mem_flatMap,List.mem_map] using hp)
      have hl : ij.1 < 6 ∧ ij.2 < 6 ∧ ij.1 ≠ ij.2 :=
        of_decide_eq_true (List.all_eq_true.mp pair_laws ij hij)
      exact valid_or (lowAt_valid hv hl.1 ha) (lowAt_valid hv hl.2.1 hb)
  · exact hv v hm

lemma pool_good_deficit {hist : List Nat} (hv : ∀ v ∈ hist, MaskValid v)
    {v : Nat} (hm : v ∈ pool hist) (good : MaskGood v) :
    (Deficit v).card ≤ 1 ∨ v ∈ hist := by
  rw [pool,List.mem_eraseDups] at hm
  rcases List.mem_append.mp hm with hm | hm
  · left
    rcases List.mem_append.mp hm with hb | hp
    · have hz := base_good_deficit v hb good
      omega
    · obtain ⟨ij,hij,a,ha,b,hb,rfl⟩ :=
        (show ∃ ij ∈ pairIndices, ∃ a ∈ lowAt hist ij.1,
          ∃ b ∈ lowAt hist ij.2, a ||| b = v from by
          simpa only [List.mem_flatMap,List.mem_map] using hp)
      have hl : ij.1 < 6 ∧ ij.2 < 6 ∧ ij.1 ≠ ij.2 :=
        of_decide_eq_true (List.all_eq_true.mp pair_laws ij hij)
      have dom := negLE_or (lowAt_dominates hv hl.1 ha) (lowAt_dominates hv hl.2.1 hb)
      exact (Finset.card_le_card (deficit_mono dom)).trans (raw_pair_deficit ij hij)
  · exact Or.inr hm


lemma ands_valid {xs : List Nat} (hv : ∀ v ∈ xs, MaskValid v)
    {v : Nat} (hm : v ∈ ands xs) : MaskValid v := by
  simp only [ands,List.mem_eraseDups,List.mem_filter,List.mem_flatMap,List.mem_map] at hm
  obtain ⟨⟨a,ha,b,hb,rfl⟩,_⟩ := hm
  exact valid_and (hv a ha) (hv b hb)

lemma first_valid {a : Nat} (ha : a ∈ ands (pool [])) : MaskValid a :=
  ands_valid (pool_valid (by simp)) ha

lemma first_good_deficit {a : Nat} (ha : a ∈ ands (pool [])) (good : MaskGood a) :
    (Deficit a).card = 0 := by
  simp only [ands,List.mem_eraseDups,List.mem_filter,List.mem_flatMap,List.mem_map] at ha
  obtain ⟨⟨p,hp,q,hq,rfl⟩,_⟩ := ha
  have hpc := initial_good_deficit p hp (good_and_left good)
  have hqc := initial_good_deficit q hq (good_and_right good)
  have hsum := deficit_and_le p q
  omega

lemma first_pool_good_deficit {a v : Nat} (ha : a ∈ ands (pool []))
    (hv : v ∈ pool [a]) (good : MaskGood v) : (Deficit v).card ≤ 1 := by
  have valid : ∀ x ∈ [a], MaskValid x := by
    intro x hx
    have he : x = a := by simpa using hx
    exact he ▸ first_valid ha
  rcases pool_good_deficit valid hv good with hs | hm
  · exact hs
  · have he : v = a := by simpa using hm
    subst v
    have hz := first_good_deficit ha good
    omega

lemma second_valid {a b : Nat} (ha : a ∈ ands (pool []))
    (hb : b ∈ ands (pool [a])) : MaskValid b := by
  apply ands_valid _ hb
  apply pool_valid
  intro x hx
  have he : x = a := by simpa using hx
  exact he ▸ first_valid ha

lemma second_good_deficit {a b : Nat} (ha : a ∈ ands (pool []))
    (hb : b ∈ ands (pool [a])) (good : MaskGood b) : (Deficit b).card ≤ 2 := by
  simp only [ands,List.mem_eraseDups,List.mem_filter,List.mem_flatMap,List.mem_map] at hb
  obtain ⟨⟨p,hp,q,hq,rfl⟩,_⟩ := hb
  have hpc := first_pool_good_deficit ha hp (good_and_left good)
  have hqc := first_pool_good_deficit ha hq (good_and_right good)
  have hsum := deficit_and_le p q
  omega

lemma final_pool_good_deficit {a b v : Nat} (ha : a ∈ ands (pool []))
    (hb : b ∈ ands (pool [a])) (hv : v ∈ pool [a,b]) (good : MaskGood v) :
    (Deficit v).card ≤ 1 ∨ v = b := by
  have valid : ∀ x ∈ [a,b], MaskValid x := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl
    · exact first_valid ha
    · exact second_valid ha hb
  rcases pool_good_deficit valid hv good with hs | hm
  · exact Or.inl hs
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | he
    · left
      have hz := first_good_deficit ha good
      omega
    · exact Or.inr he

lemma target_good : MaskGood 7 := by
  unfold MaskGood
  decide +kernel
lemma target_deficit : (Deficit 7).card = 4 := by decide +kernel

lemma certificate_by_deficit : Certificate := by
  intro a b p q ha hb hp hq he
  have hgood : MaskGood (p &&& q) := he ▸ target_good
  have pg := good_and_left hgood
  have qg := good_and_right hgood
  have hc := deficit_and_le p q
  rw [he,target_deficit] at hc
  rcases final_pool_good_deficit ha hb hp pg with hps | hpb <;>
    rcases final_pool_good_deficit ha hb hq qg with hqs | hqb
  · omega
  · subst q
    have hbs := second_good_deficit ha hb qg
    omega
  · subst p
    have hbs := second_good_deficit ha hb pg
    omega
  · subst p
    subst q
    have hbs := second_good_deficit ha hb pg
    have eq : b = 7 := by simpa using he
    rw [eq,target_deficit] at hbs
    omega

lemma no_target_history_count (hist : List Nat) (hlen : hist.length ≤ 3)
    (legal : ∀ j : Fin hist.length, hist.get j ∈ ands (pool (hist.take j.val))) :
    7 ∉ pool hist := no_target_history_of_certificate certificate_by_deficit hist hlen legal

end RigidClosure


namespace RigidClosure

lemma no_target_of_membership {a b p q : Nat}
    (ha : a ∈ ands (pool [])) (hb : b ∈ ands (pool [a]))
    (hp : p ∈ pool [a, b]) (hq : q ∈ pool [a, b]) : p &&& q ≠ 7 :=
  certificate_by_deficit ha hb hp hq

lemma no_target_three_ands {a b c d e f : Nat}
    (ha : a ∈ pool []) (hb : b ∈ pool [])
    (h1 : low (a &&& b) = true)
    (hc : c ∈ pool [a &&& b]) (hd : d ∈ pool [a &&& b])
    (h2 : low (c &&& d) = true)
    (he : e ∈ pool [a &&& b, c &&& d])
    (hf : f ∈ pool [a &&& b, c &&& d]) : e &&& f ≠ 7 :=
  no_target_of_membership (and_mem_ands ha hb h1) (and_mem_ands hc hd h2) he hf

lemma no_target_history (hist : List Nat) (hlen : hist.length ≤ 3)
    (legal : ∀ j : Fin hist.length, hist.get j ∈ ands (pool (hist.take j.val))) :
    7 ∉ pool hist :=
  no_target_history_of_certificate certificate_by_deficit hist hlen legal

end RigidClosure


namespace PoolNormalize

def Legal (R : List Nat → Nat → Prop) (h gs : List Nat) : Prop :=
  List.rec (motive := fun _ => List Nat → Prop) (fun _ => True)
    (fun w _ rec h => R h w ∧ rec (h ++ [w])) gs h

lemma normalize (P : List Nat → List Nat) (R : List Nat → Nat → Prop)
    (mono : ∀ {h k}, h ⊆ k → P h ⊆ P k)
    (self : ∀ {h v}, v ∈ h → v ∈ P h)
    {p gs h : List Nat} (base : p ⊆ P h) (mark : Fin gs.length → Bool)
    (steps : ∀ j : Fin gs.length, ∀ hist,
      p ++ gs.take j.val ⊆ P hist →
      if mark j then R hist (gs.get j) else gs.get j ∈ P hist) :
    ∃ hs, Legal R h hs ∧ p ++ gs ⊆ P (h ++ hs) ∧
      hs.length = ∑ j : Fin gs.length, if mark j then 1 else 0 := by
  induction gs generalizing p h with
  | nil =>
    refine ⟨[],trivial,?_,?_⟩
    · simpa using base
    · simp
  | cons w gs ih =>
    let tailMark : Fin gs.length → Bool := fun j => mark j.succ
    have hsum : (∑ j : Fin (w :: gs).length, if mark j then 1 else 0) =
        (if mark 0 then 1 else 0) + ∑ j : Fin gs.length, if tailMark j then 1 else 0 := by
      exact Fin.sum_univ_succ _
    have step0 := steps 0 h (by simpa using base)
    have tailSteps : ∀ j : Fin gs.length, ∀ hist,
        (p ++ [w]) ++ gs.take j.val ⊆ P hist →
        if tailMark j then R hist (gs.get j) else gs.get j ∈ P hist := by
      intro j hist hh
      simpa [List.append_assoc] using steps j.succ hist (by simpa [List.append_assoc] using hh)
    by_cases hm : mark 0 = true
    · have hw : R h w := by simpa [hm] using step0
      have hbase : p ++ [w] ⊆ P (h ++ [w]) := by
        intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · exact mono (fun _ hx => List.mem_append_left _ hx) (base ha)
        · exact self (List.mem_append_right _ ha)
      obtain ⟨hs,hlegal,hcover,hlen⟩ := ih hbase tailMark tailSteps
      refine ⟨w :: hs,⟨hw,hlegal⟩,?_,?_⟩
      · simpa [List.append_assoc] using hcover
      · rw [hsum,hm]
        simp only [↓reduceIte,List.length_cons]
        omega
    · have hmfalse : mark 0 = false := Bool.eq_false_iff.mpr hm
      have hw : w ∈ P h := by simpa [hmfalse] using step0
      have hbase : p ++ [w] ⊆ P h := by
        intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · exact base ha
        · exact (List.mem_singleton.mp ha) ▸ hw
      obtain ⟨hs,hlegal,hcover,hlen⟩ := ih hbase tailMark tailSteps
      refine ⟨hs,hlegal,?_,?_⟩
      · simpa [List.append_assoc] using hcover
      · rw [hsum,hmfalse]
        simpa using hlen

lemma normalize_marked (P : List Nat → List Nat) (R : List Nat → Nat → Prop)
    (mono : ∀ {h k}, h ⊆ k → P h ⊆ P k)
    (self : ∀ {h v}, v ∈ h → v ∈ P h)
    {p gs : List Nat} (base : p ⊆ P []) (C : Finset (Fin gs.length))
    (steps : ∀ j : Fin gs.length, ∀ hist, p ++ gs.take j.val ⊆ P hist →
      (j ∈ C → R hist (gs.get j)) ∧ (j ∉ C → gs.get j ∈ P hist)) :
    ∃ hs, Legal R [] hs ∧ p ++ gs ⊆ P hs ∧ hs.length = C.card := by
  classical
  obtain ⟨hs,hl,hc,hn⟩ := normalize P R mono self base (fun j => decide (j ∈ C))
    (fun j hist hh => by
      by_cases hj : j ∈ C
      · simpa [hj] using (steps j hist hh).1 hj
      · simpa [hj] using (steps j hist hh).2 hj)
  exact ⟨hs,hl,by simpa using hc,by simpa using hn⟩


lemma legal_get {R : List Nat → Nat → Prop} {h xs : List Nat} (hl : Legal R h xs)
    (j : Fin xs.length) : R (h ++ xs.take j.val) (xs.get j) := by
  induction xs generalizing h with
  | nil => exact Fin.elim0 j
  | cons w xs ih =>
    refine Fin.cases ?_ (fun i => ?_) j
    · simpa using hl.1
    · simpa [List.append_assoc] using ih hl.2 i

end PoolNormalize


namespace PoolProgram
open PEqualNP.Outside.L_meta_2590_aux.RigidClosure

lemma free_mem_pool {previous hist : List Nat} {v : Nat}
    (hp : previous ⊆ pool hist) (hv : FreeValue previous v) : v ∈ pool hist := by
  rcases hv with hv | hv | ⟨i,j,hij,a,ha,b,hb,hai,hbj,rfl⟩
  · exact hp hv
  · exact mem_pool_triples hist hv
  · apply mem_pool_pair hij
    · exact lowAt_of_mem_pool i.isLt (hp ha) hai
    · exact lowAt_of_mem_pool j.isLt (hp hb) hbj

lemma and_mem_pool_ands {previous hist : List Nat} {v : Nat}
    (hp : previous ⊆ pool hist) (hv : AndValue previous v) : v ∈ ands (pool hist) := by
  obtain ⟨hl,a,ha,b,hb,rfl⟩ := hv
  exact and_mem_ands (hp ha) (hp hb) hl

lemma program_history {p gs : List Nat} (base : p ⊆ pool [])
    (C : Finset (Fin gs.length))
    (step : ∀ j : Fin gs.length,
      (j ∈ C → AndValue (p ++ gs.take j.val) (gs.get j)) ∧
      (j ∉ C → FreeValue (p ++ gs.take j.val) (gs.get j))) :
    ∃ hs, PoolNormalize.Legal (fun hist v => v ∈ ands (pool hist)) [] hs ∧
      p ++ gs ⊆ pool hs ∧ hs.length = C.card := by
  apply PoolNormalize.normalize_marked pool (fun hist v => v ∈ ands (pool hist))
    (fun hh => pool_mono hh) (fun hv => mem_pool_self hv) base C
  intro j hist hh
  exact ⟨fun hj => and_mem_pool_ands hh ((step j).1 hj),
    fun hj => free_mem_pool hh ((step j).2 hj)⟩


lemma program_impossible (cert : Certificate) {p gs : List Nat} (base : p ⊆ pool [])
    (C : Finset (Fin gs.length)) (cc : C.card ≤ 3) (target : 7 ∈ p ++ gs)
    (step : ∀ j : Fin gs.length,
      (j ∈ C → AndValue (p ++ gs.take j.val) (gs.get j)) ∧
      (j ∉ C → FreeValue (p ++ gs.take j.val) (gs.get j))) : False := by
  obtain ⟨hs,hl,hcover,hlen⟩ := program_history base C step
  apply no_target_history_of_certificate cert hs (by omega) ?_ (hcover target)
  intro j
  simpa using PoolNormalize.legal_get hl j

end PoolProgram


namespace FinishFour
open PEqualNP.Outside.L_meta_2590_aux.DagTools
open PEqualNP.Outside.L_meta_2590_aux.Four
open PEqualNP.Outside.L_meta_2590_aux.PoolProgram
open PEqualNP.Outside.L_meta_2590_aux.RigidClosure

lemma four_ineligible_zero_impossible {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 Adj D) (zero : Bzero 10 D = 0)
    (four : (ineligSet 10 D).card = 4) (size : D.length ≤ 19) : False := by
  obtain ⟨k,C,hcard,hbase,htarget,hsteps⟩ :=
    PoolClassify.classified_program h hc zero four size
  apply program_impossible certificate_by_deficit ?_ C (by omega) htarget hsteps
  intro v hv
  rcases List.mem_cons.mp (hbase v hv) with hz | hi
  · rw [hz]
    exact mem_pool_zero []
  · exact mem_pool_inputs [] hi

end FinishFour

end PEqualNP.Outside.L_meta_2590_aux
