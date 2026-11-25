import Mathlib.Logic.Relation
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Tauto
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import PEqualNP.Defs
import Mathlib.Data.Finset.Card

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

namespace DeskDriver

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open DagTools

abbrev V := Fin 10

def target (x : V → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) ||
  (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)

def neighbors (v : V) : Nat :=
  [50, 69, 138, 276, 521, 385, 770, 548, 104, 208].getD v.val 0

abbrev adj (u v : V) : Prop := (neighbors u).testBit v.val = true

lemma graph_ok : sem_Gr adj := by
  unfold sem_Gr
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma target_edge : ∀ x : V → Bool, target x = true ↔ sem_Edge adj x := by
  unfold sem_Edge
  decide +kernel

lemma normalization_witnesses :
    (∀ i : V, target (single i) ≠ single i i) ∧
      (∀ i : V, ∃ j : V, target (single j) ≠ target (sem_ins i (single j))) := by
  decide +kernel

lemma independent_card : ∀ I : Finset V,
    (∀ u ∈ I, ∀ v ∈ I, ¬ adj u v) → I.card ≤ 4 := by
  decide +kernel

lemma ineligible_card {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D) :
    (ineligSet 10 D).card ≤ 4 := by
  apply independent_card
  intro u hu v hv huv
  rcases sem_elig_cover graph_ok h hc huv with h | h
  · exact (sem_mem_inelig.mp hu) h
  · exact (sem_mem_inelig.mp hv) h

lemma normalize {C : Circuit} (hm : Monotone2 C)
    (hf : ∀ x : V → Bool, C.eval (List.ofFn x) = target x) :
    ∃ D : Dag, StrictLive 10 D ∧ D.length ≤ C.size ∧ sem_Comp 10 adj D := by
  have hnc : ∀ b : Bool, ∃ x : V → Bool, C.eval (List.ofFn x) ≠ b := by
    intro b
    cases b
    · exact ⟨fun _ => true, by rw [hf]; decide⟩
    · exact ⟨fun _ => false, by rw [hf]; decide⟩
  have hnp : ∀ i : V, ∃ x : V → Bool, C.eval (List.ofFn x) ≠ x i := by
    intro i
    exact ⟨single i, by rw [hf]; exact normalization_witnesses.1 i⟩
  have hess : ∀ i : V, ∃ x y : V → Bool,
      (∀ k, k ≠ i → x k = y k) ∧ C.eval (List.ofFn x) ≠ C.eval (List.ofFn y) := by
    intro i
    obtain ⟨j, hj⟩ := normalization_witnesses.2 i
    refine ⟨single j, sem_ins i (single j), sem_ins_agree i (single j), ?_⟩
    simpa only [hf] using hj
  obtain ⟨D, hD, hlen, he⟩ := normalize_strictLive C hm hnc hnp hess
  refine ⟨D, hD, hlen, ?_⟩
  intro x
  rw [he, hf]
  exact target_edge x

lemma lift_cases
    (cases : ∀ k ≤ 4, ∀ D : Dag, StrictLive 10 D → sem_Comp 10 adj D →
      D.length ≤ 19 → (ineligSet 10 D).card = k → False)
    (C : Circuit) (hm : Monotone2 C) (hs : C.size ≤ 19) :
    ¬ ∀ x : V → Bool, C.eval (List.ofFn x) = target x := by
  intro hf
  obtain ⟨D, hD, hlen, hc⟩ := normalize hm hf
  exact cases _ (ineligible_card hD hc) D hD hc (by omega) rfl

end DeskDriver

namespace FirstDirty

def Independent {n : ℕ} (G : Fin n → Fin n → Prop) (x : Fin n → Bool) : Prop :=
  ∀ u v, x u = true → x v = true → ¬ G u v

end FirstDirty

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

namespace CircuitPurity

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def Independent {n : ℕ} (G : Fin n → Fin n → Prop) (x : Fin n → Bool) : Prop :=
  ∀ u v, x u = true → x v = true → ¬ G u v

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

end CircuitPurity

namespace ResidualCodes

end ResidualCodes

namespace I3Branch

open PEqualNP.Outside.L_meta_2590_aux.DagTools

namespace DagTools

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

@[local simp] theorem h5_local_gop_true (a b : Bool) : gop true a b = (a && b) := rfl

@[local simp] theorem h5_local_gop_false (a b : Bool) : gop false a b = (a || b) := rfl

section SurplusFlow

variable {n : ℕ} {D : Dag}

end SurplusFlow

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

end SemPaths

section SemDiff

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

end SemDiff

section SupMask

variable {n : ℕ} {D : Dag}

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

open DagTools

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

open DagTools

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

open DagTools

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

open DagTools

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

open DagTools Finish

section Generic

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

end Generic

def J : Finset V := {1, 4, 5}

def C : Finset V := {2, 3, 6, 7, 8, 9}

def owner (x : V) : V :=
  if x = 2 ∨ x = 6 then 1 else if x = 3 ∨ x = 9 then 4 else 5

def exposureMask (x y : V) : Nat :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   9, 0, 0, 9, 208, 104, 72, 129, 385, 521, 5, 770, 5, 0, 0, 548, 69, 385, 257, 516,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   257, 0, 260, 521, 276, 548, 0, 385, 257, 513, 5, 770, 5, 521, 276, 0, 69, 0, 260, 513,
   9, 138, 69, 9, 208, 0, 65, 136, 0, 521, 65, 138, 69, 72, 0, 104, 65, 129, 385, 0].getD
     (10 * x.val + y.val) 0

def exposureSet (x y : V) : Finset V :=
  Finset.univ.filter (fun a => (exposureMask x y).testBit a.val = true)

lemma exposure_ok : ∀ x ∈ C, ∀ y : V, y ≠ owner x → y ≠ x →
    (∀ a ∈ exposureSet x y, ∀ b ∈ exposureSet x y, ¬ adj a b) ∧
    y ∈ exposureSet x y ∧
    (∃ a ∈ exposureSet x y, adj (owner x) a) ∧
    ∃ a ∈ exposureSet x y, adj x a := by
  decide +kernel

end NeighborCover

end I3Branch


namespace Foundation

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open DagTools

lemma graph_agreement : DeskDriver.adj = I3Branch.adj := rfl

lemma extendable_impossible {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 DeskDriver.adj D) (hlen : D.length ≤ 19)
    (hi : ineligSet 10 D = ({0, 8, 9} : Finset (Fin 10))) : False :=
  I3Branch.extendable_I_impossible h hc hlen hi

lemma reduce_three {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 DeskDriver.adj D) (hlen : D.length ≤ 19)
    (hi : (ineligSet 10 D).card = 3) :
    ∃ D' : Dag, StrictLive 10 D' ∧ sem_Comp 10 DeskDriver.adj D' ∧
      D'.length = D.length ∧ ineligSet 10 D' = ({1, 4, 5} : Finset (Fin 10)) :=
  I3Branch.reduce_three_to_neighborhood h hc hlen hi

lemma circuit_three_reduction (C : Circuit) (hm : Monotone2 C) (hs : C.size ≤ 19)
    (hf : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = DeskDriver.target x) :
    ∃ D : Dag, StrictLive 10 D ∧ sem_Comp 10 DeskDriver.adj D ∧ D.length ≤ 19 ∧
      (ineligSet 10 D).card ≤ 4 ∧
      ((ineligSet 10 D).card = 3 →
        ∃ D' : Dag, StrictLive 10 D' ∧ sem_Comp 10 DeskDriver.adj D' ∧
          D'.length = D.length ∧
          ineligSet 10 D' = ({1, 4, 5} : Finset (Fin 10))) := by
  obtain ⟨D, hD, hlen, hc⟩ := DeskDriver.normalize hm hf
  have hsD : D.length ≤ 19 := by omega
  exact ⟨D, hD, hc, hsD, DeskDriver.ineligible_card hD hc,
    fun hi => reduce_three hD hc hsD hi⟩

end Foundation


namespace I4Proof

open PEqualNP.Outside.L_meta_2590_aux.DagTools

namespace DagTools

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

@[local simp] lemma h6_local_gop_true (a b : Bool) : gop true a b = (a && b) := rfl

@[local simp] lemma h6_local_gop_false (a b : Bool) : gop false a b = (a || b) := rfl

section SurplusFlow

variable {n : ℕ} {D : Dag}

end SurplusFlow

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

end SemPaths

section SemDiff

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

end SemDiff

section SupMask

variable {n : ℕ} {D : Dag}

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

end DagTools

namespace Four

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.DagTools

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

end Four

namespace Four

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.DagTools

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

end SevenRows

namespace SevenRows

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.DagTools

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

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.DagTools

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

end Neutral

namespace Neutral

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.DagTools

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

end SevenRows

namespace SevenGeneral

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.DagTools

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.Four

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.SevenRows

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.Neutral

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

end DagRigidity

namespace ZeroFlow

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.DagTools

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

end ZeroFlow

namespace ZeroForest

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.DagTools

section Facts

variable {α : Type} {n : Nat} {G : Fin n → Fin n → Prop} {D : Dag}
  {I : Finset (Fin n)} {rows : α → Fin n → Bool}

end Facts

end ZeroForest

namespace Neutral

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.DagTools

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

end Neutral

namespace Thirteen

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.DagTools

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.Four

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.Neutral

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

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.SevenGeneral

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

end Thirteen

namespace GeneralFlow

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.DagTools

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

end GeneralFlow

namespace GeneralZero

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.DagTools

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

end Facts

end GeneralZero

namespace EightGeneral

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.DagTools

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.Neutral

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

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.Four

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.SevenGeneral

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.Thirteen

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

end Compression

namespace Compression

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.DagTools

variable {α : Type}

end Compression

namespace Thirteen

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.DagTools

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.Four

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.SevenGeneral

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.Compression

end Thirteen

namespace EightSupport

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.DagTools

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.Neutral

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.Four

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.SevenGeneral

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.Thirteen

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.EightGeneral

set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 1000000 in
lemma cases_singletons13 : ∀ k : Fin 5, ∀ v : Fin 10, v ∉ casesI k →
    ∃ r : Fin 13, caseRow k r = single v := by
  unfold caseRow liftMask casesMasks casesI single
  decide +kernel

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

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.DagTools

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

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.DagTools

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

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.DagTools

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

end MaskGeometry

namespace LabelRigidity

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.DagTools

open Rigidity DagRigidity

variable {n : Nat} {D : Dag}

end LabelRigidity

namespace LabelBudget

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.DagTools

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.DagRigidity

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

end LabelBudget

namespace TightFour

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.DagTools

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

end TightFour

namespace TightFour

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.DagTools

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

end TightFour

namespace PoolDag

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.DagTools

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.Thirteen

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.SevenRows

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.SevenGeneral

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.Four

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

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.MaskGeometry

end PoolProgram

namespace PoolClassify

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.DagTools

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

end RigidClosure

namespace RigidClosure

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

end RigidClosure

namespace RigidClosure

def MaskGood (v : Nat) : Prop := ∀ r : Fin 3, v.testBit r.val = true

def Deficit (v : Nat) : Finset (Fin 4) := Finset.univ.filter (fun r => v.testBit (3+r.val) = false)

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

set_option maxHeartbeats 0 in
lemma initial_good_deficit : ∀ v ∈ pool [], MaskGood v → (Deficit v).card = 0 := by
  unfold pool lowAt inputs triples pairIndices MaskGood Deficit
  decide +kernel

lemma first_good_deficit {a : Nat} (ha : a ∈ ands (pool [])) (good : MaskGood a) :
    (Deficit a).card = 0 := by
  simp only [ands,List.mem_eraseDups,List.mem_filter,List.mem_flatMap,List.mem_map] at ha
  obtain ⟨⟨p,hp,q,hq,rfl⟩,_⟩ := ha
  have hpc := initial_good_deficit p hp (good_and_left good)
  have hqc := initial_good_deficit q hq (good_and_right good)
  have hsum := deficit_and_le p q
  omega

lemma target_good : MaskGood 7 := by
  unfold MaskGood
  decide +kernel

lemma target_deficit : (Deficit 7).card = 4 := by decide +kernel

end RigidClosure

namespace RigidClosure

end RigidClosure

namespace PoolNormalize

def Legal (R : List Nat → Nat → Prop) (h gs : List Nat) : Prop :=
  List.rec (motive := fun _ => List Nat → Prop) (fun _ => True)
    (fun w _ rec h => R h w ∧ rec (h ++ [w])) gs h

end PoolNormalize

namespace PoolProgram

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.RigidClosure

end PoolProgram

namespace FinishFour

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.DagTools

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.Four

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.PoolProgram

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.RigidClosure

end FinishFour

namespace SharedDom

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.DagTools

lemma ins_comm {n : Nat} (i j : Fin n) (x : Fin n → Bool) :
    sem_ins i (sem_ins j x) = sem_ins j (sem_ins i x) := by
  funext k
  simp only [sem_ins]
  cases decide (k = i) <;> cases decide (k = j) <;> rfl

lemma shared_dom_reject {n : Nat} {G : Fin n → Fin n → Prop} {D : Dag}
    (hS : Strict n D) (hC : sem_Comp n G D) (i j : Fin n) (b : Nat)
    (di : sem_Dom n D b i.val) (dj : sem_Dom n D b j.val)
    (x : Fin n → Bool) (h0 : ¬ sem_Edge G x)
    (hi : ¬ sem_Edge G (sem_ins i x)) (hj : sem_Edge G (sem_ins j x)) :
    val D (sem_ins i x) b = false := by
  have hb_j := (sem_dom_split hS hC x j b dj h0 hj).2
  apply Bool.eq_false_iff.mpr
  intro hb_i
  have hi_both : val D (sem_ins j (sem_ins i x)) b = true :=
    val_mono hS _ _ (sem_ins_ge j _) b hb_i
  have hj_both : val D (sem_ins i (sem_ins j x)) b = true :=
    val_mono hS _ _ (sem_ins_ge i _) b hb_j
  have ei := sem_dom_eq hS _ _ j (sem_ins_agree j (sem_ins i x)) b dj
    (hb_i.trans hi_both.symm)
  have ej := sem_dom_eq hS _ _ i (sem_ins_agree i (sem_ins j x)) b di
    (hb_j.trans hj_both.symm)
  rw [ins_comm i j x] at ej
  have eq := ei.trans ej.symm
  exact hi ((hC _).mp (eq.symm ▸ (hC _).mpr hj))

lemma exact_support_before_shared_dom
    {n : Nat} {G : Fin n → Fin n → Prop} {D : Dag}
    (hS : Strict n D) (hC : sem_Comp n G D) (i j : Fin n) (b : Nat)
    (ci : sem_Chain n D i.val b) (dj : sem_Dom n D b j.val)
    (Bs N : Finset (Fin n)) (hN : N ⊆ Bs)
    (h0 : ¬ sem_Edge G (sem_ind (Bs \ N)))
    (hi : ¬ sem_Edge G (sem_ins i (sem_ind (Bs \ N))))
    (hj : sem_Edge G (sem_ins j (sem_ind (Bs \ N))))
    (h_single : ∀ a ∈ N, ¬ sem_Edge G (sem_ind {a}))
    (h_incident : ∀ a ∈ N, sem_Edge G (sem_ins i (sem_ind {a}))) :
    ∃ g s, g < D.length ∧ tag D g = true ∧ n + g ≤ b ∧
      sem_Chain n D i.val (src D (g,!s)) ∧
      supp n D (src D (g,s)) ∩ Bs = N := by
  have di := sem_chain_dom hS ci
  apply sem_factor hS i b ci Bs N hN
  · exact shared_dom_reject hS hC i j b di dj _ h0 hi hj
  · intro a ha
    exact (sem_dom_split hS hC _ i b di (h_single a ha) (h_incident a ha)).2
  · intro a ha
    exact (sem_dom_split hS hC _ i b di (h_single a ha) (h_incident a ha)).1

lemma exact_non_neighbors_shared
    {n : Nat} {G : Fin n → Fin n → Prop} {D : Dag}
    [DecidableRel G]
    (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    (E : Finset (Fin n)) (i j : Fin n) (b : Nat)
    (ci : sem_Chain n D i.val b) (dj : sem_Dom n D b j.val)
    (ind : ∀ a ∈ E, ∀ c ∈ E, ¬ G i a → ¬ G i c → ¬ G a c)
    (private_neighbor : ∃ a ∈ E, G j a ∧ ¬ G i a) :
    ∃ g s, g < D.length ∧ tag D g = true ∧ n + g ≤ b ∧
      sem_Chain n D i.val (src D (g,!s)) ∧
      supp n D (src D (g,s)) ∩ E = E.filter (G i) := by
  classical
  let A := E \ E.filter (G i)
  have ain (a : Fin n) (ha : a ∈ A) : a ∈ E ∧ ¬ G i a := by
    simp only [A, Finset.mem_sdiff, Finset.mem_filter] at ha
    exact ⟨ha.1, fun hia => ha.2 ⟨ha.1, hia⟩⟩
  have h0 : ¬ sem_Edge G (sem_ind A) := by
    rintro ⟨a,c,hac,ha,hc⟩
    have ha' : a ∈ A := by simpa only [sem_ind, decide_eq_true_eq] using ha
    have hc' : c ∈ A := by simpa only [sem_ind, decide_eq_true_eq] using hc
    exact ind a (ain a ha').1 c (ain c hc').1 (ain a ha').2 (ain c hc').2 hac
  have hi : ¬ sem_Edge G (sem_ins i (sem_ind A)) := by
    intro he
    rcases sem_ins_ind_edge hG he with ⟨a,ha,hia⟩ | ⟨a,ha,c,hc,hac⟩
    · exact (ain a ha).2 hia
    · exact ind a (ain a ha).1 c (ain c hc).1 (ain a ha).2 (ain c hc).2 hac
  have hj : sem_Edge G (sem_ins j (sem_ind A)) := by
    obtain ⟨a,ha,hja,hia⟩ := private_neighbor
    have haA : a ∈ A := by simp only [A, Finset.mem_sdiff, Finset.mem_filter]; tauto
    exact ⟨j,a,hja,sem_ins_self j _,by simp [sem_ins,sem_ind,haA]⟩
  exact exact_support_before_shared_dom hS hC i j b ci dj E (E.filter (G i))
    (Finset.filter_subset _ _) h0 hi hj
    (fun a _ => by rw [sem_ind_single]; exact sem_single_no_edge hG a)
    (fun a ha => ⟨i,a,(Finset.mem_filter.mp ha).2,sem_ins_self i _,
      by simp [sem_ins,sem_ind]⟩)

lemma unique_empty_branch {n : Nat} {D : Dag}
    (hS : Strict n D) (hz : Bzero n D ≤ 1)
    {a b : Nat} (ha : 2 ≤ fanout D a) (hb : 2 ≤ fanout D b)
    (sa : supp n D a = ∅) (sb : supp n D b = ∅) : a = b := by
  classical
  by_contra ne
  let K := (inner n D).filter (fun w => ¬ (supp n D w).Nonempty)
  have haK : a ∈ K := sem_bzero_mem hS ha sa
  have hbK : b ∈ K := sem_bzero_mem hS hb sb
  have hbErase : b ∈ K.erase a := Finset.mem_erase.mpr ⟨Ne.symm ne,hbK⟩
  have hsum : fanout D b - 1 ≤ ∑ w ∈ K.erase a, (fanout D w - 1) :=
    Finset.single_le_sum (fun w _ => Nat.zero_le (fanout D w - 1)) hbErase
  have heq := Finset.add_sum_erase K (fun w => fanout D w - 1) haK
  have htotal : (∑ w ∈ K, (fanout D w - 1)) = Bzero n D := by rfl
  omega

end SharedDom

namespace SharedDom

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.DagTools

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.Four

lemma exact_petersen_shared {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (four : (ineligSet 10 D).card = 4)
    {i j : Fin 10} (hi : i ∈ ineligSet 10 D) (hj : j ∈ ineligSet 10 D)
    (hne : i ≠ j) {b : Nat} (ci : sem_Chain 10 D i.val b)
    (dj : sem_Dom 10 D b j.val) :
    ∃ g s, g < D.length ∧ tag D g = true ∧ 10 + g ≤ b ∧
      supp 10 D (src D (g,s)) ∩ eligSet 10 D = (eligSet 10 D).filter (Adj i) := by
  have hind : ∀ a ∈ ineligSet 10 D, ∀ b ∈ ineligSet 10 D, ¬ Adj a b := by
    intro a ha b hb hab
    rcases sem_elig_cover graph_ok h hc hab with ea | eb
    · exact (sem_mem_inelig.mp ha) ea
    · exact (sem_mem_inelig.mp hb) eb
  have geo := all_four_geometry (ineligSet 10 D) four hind
  have compl : complement (ineligSet 10 D) = eligSet 10 D := by
    ext v
    simp [complement, ineligSet]
  have ind : ∀ a ∈ eligSet 10 D, ∀ b ∈ eligSet 10 D,
      ¬ Adj i a → ¬ Adj i b → ¬ Adj a b := by
    simpa only [compl] using geo.1 i hi
  have private_neighbor : ∃ a ∈ eligSet 10 D, Adj j a ∧ ¬ Adj i a := by
    obtain ⟨a,hja,hia⟩ := graph_ok.2.2.1 j i (Ne.symm hne)
    have ha : a ∈ eligSet 10 D := by
      rcases sem_elig_cover graph_ok h hc hja with ej | ea
      · exact False.elim ((sem_mem_inelig.mp hj) ej)
      · exact ea
    exact ⟨a,ha,hja,hia⟩
  obtain ⟨g,s,hg,ht,hle,_,hs⟩ :=
    exact_non_neighbors_shared graph_ok h.1 hc (eligSet 10 D) i j b ci dj ind private_neighbor
  exact ⟨g,s,hg,ht,hle,hs⟩

lemma exact_petersen_chain_out {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (four : (ineligSet 10 D).card = 4)
    {i : Fin 10} (hi : i ∈ ineligSet 10 D)
    (ci : sem_Chain 10 D i.val (outW 10 D)) :
    ∃ w, supp 10 D w ∩ eligSet 10 D = (eligSet 10 D).filter (Adj i) := by
  have hind : ∀ a ∈ ineligSet 10 D, ∀ b ∈ ineligSet 10 D, ¬ Adj a b := by
    intro a ha b hb hab
    rcases sem_elig_cover graph_ok h hc hab with ea | eb
    · exact (sem_mem_inelig.mp ha) ea
    · exact (sem_mem_inelig.mp hb) eb
  have geo := all_four_geometry (ineligSet 10 D) four hind
  have compl : complement (ineligSet 10 D) = eligSet 10 D := by
    ext v
    simp [complement, ineligSet]
  have ind : ∀ a ∈ eligSet 10 D, ∀ b ∈ eligSet 10 D,
      ¬ Adj i a → ¬ Adj i b → ¬ Adj a b := by
    simpa only [compl] using geo.1 i hi
  obtain ⟨g,s,_,_,hs⟩ := exact_non_neighbors graph_ok h.1 hc (eligSet 10 D) i ci ind
  refine ⟨src D (g,s), ?_⟩
  ext a
  simp only [Finset.mem_inter, Finset.mem_filter]
  exact ⟨fun ⟨ha,he⟩ => ⟨he,(hs a he).mp ha⟩,
    fun ⟨he,ha⟩ => ⟨(hs a he).mpr ha,he⟩⟩

lemma three_exact_of_bzero_le_one {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (four : (ineligSet 10 D).card = 4) (hz : Bzero 10 D ≤ 1) :
    ∃ i₀ ∈ ineligSet 10 D, ∀ i ∈ ineligSet 10 D, i ≠ i₀ →
      ∃ w, supp 10 D w ∩ eligSet 10 D = (eligSet 10 D).filter (Adj i) := by
  classical
  by_cases hex : ∃ i ∈ ineligSet 10 D, ∃ b,
      sem_Chain 10 D i.val b ∧ 2 ≤ fanout D b ∧ supp 10 D b = ∅
  · obtain ⟨i₀,hi₀,b,ci₀,hfb,hsb⟩ := hex
    refine ⟨i₀,hi₀,fun i hi hne => ?_⟩
    rcases sem_inelig_reach graph_ok h hc hi with ci | ⟨c,ci,hfc,hsc⟩
    · exact exact_petersen_chain_out h hc four hi ci
    · have eq := unique_empty_branch h.1 hz hfc hfb hsc hsb
      subst c
      obtain ⟨g,s,_,_,_,hs⟩ := exact_petersen_shared h hc four hi hi₀ hne ci
        (sem_chain_dom h.1 ci₀)
      exact ⟨src D (g,s),hs⟩
  · have nonempty : (ineligSet 10 D).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨i₀,hi₀⟩ := nonempty
    refine ⟨i₀,hi₀,fun i hi _ => ?_⟩
    rcases sem_inelig_reach graph_ok h hc hi with ci | ⟨b,ci,hfb,hsb⟩
    · exact exact_petersen_chain_out h hc four hi ci
    · exact False.elim (hex ⟨i,hi,b,ci,hfb,hsb⟩)

lemma three_exact_one_superset {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (four : (ineligSet 10 D).card = 4) (hz : Bzero 10 D ≤ 1) :
    ∃ i₀ ∈ ineligSet 10 D, ∀ i ∈ ineligSet 10 D,
      ∃ w, w < 10 + D.length ∧
        (eligSet 10 D).filter (Adj i) ⊆ supp 10 D w ∩ eligSet 10 D ∧
        (i ≠ i₀ → supp 10 D w ∩ eligSet 10 D = (eligSet 10 D).filter (Adj i)) := by
  classical
  obtain ⟨i₀,hi₀,exact_others⟩ := three_exact_of_bzero_le_one h hc four hz
  refine ⟨i₀,hi₀,fun i hi => ?_⟩
  by_cases heq : i = i₀
  · obtain ⟨e,he,_,_,_,hn,_,_⟩ := sem_inelig_consumer graph_ok h hc hi
    refine ⟨src D (e.1,!e.2), (sem_src_lt h.1 he (!e.2)).trans_le (by omega), ?_, ?_⟩
    · intro a ha
      obtain ⟨haE,hia⟩ := Finset.mem_filter.mp ha
      exact Finset.mem_inter.mpr ⟨hn a hia,haE⟩
    · exact fun hne => False.elim (hne heq)
  · obtain ⟨w,hw⟩ := exact_others i hi heq
    have hlo : w < 10 + D.length := by
      obtain ⟨a,hia,_⟩ := graph_ok.2.2.2 i i
      have haE : a ∈ eligSet 10 D := by
        rcases sem_elig_cover graph_ok h hc hia with ei | ea
        · exact False.elim ((sem_mem_inelig.mp hi) ei)
        · exact ea
      have haN : a ∈ (eligSet 10 D).filter (Adj i) := Finset.mem_filter.mpr ⟨haE,hia⟩
      have haw : a ∈ supp 10 D w := (Finset.mem_inter.mp (hw.symm ▸ haN)).1
      by_contra hge
      rw [supp_ge D w (by omega)] at haw
      exact Finset.notMem_empty a haw
    exact ⟨w,hlo,hw.symm ▸ Finset.Subset.refl _,fun _ => hw⟩

end SharedDom

namespace ThreeStars

open Rigidity

variable {α : Type} [DecidableEq α]

lemma cover_not_serves {R M T : Finset α} (hr : R.card = 3) (ht : T.card = 3)
    (hint : (T ∩ R).card ≤ 1) (hRM : R ⊆ M) : ¬ Serves M T := by
  intro hs
  rcases hs with ⟨hm,_⟩ | ⟨hm,hTM⟩
  · have hh := Finset.card_le_card hRM
    omega
  · have hsub : T ∪ R ⊆ M := Finset.union_subset hTM hRM
    have hb := Finset.card_le_card hsub
    have he := Finset.card_union_add_card_inter T R
    omega

lemma cover_not_star {R M T : Finset α} (hr : R.card = 3)
    (hint : (T ∩ R).card ≤ 1) (hRM : R ⊆ M) : M ≠ T := by
  intro he
  rw [he] at hRM
  rw [Finset.inter_eq_right.mpr hRM,hr] at hint
  omega

lemma serving_parent {S : Finset α} {F : Finset (Finset α)} {T : Finset α}
    (hs : S.card ≤ 6) (ht : T.card = 3) (hF : ∀ X ∈ F, X ⊆ S)
    (par : ∃ P Q : Finset α, (P.card ≤ 1 ∨ P ∈ F) ∧ (Q.card ≤ 1 ∨ Q ∈ F) ∧
      P ≠ T ∧ Q ≠ T ∧ (T = P ∪ Q ∨ T = P ∩ Q)) :
    ∃ X ∈ F, Serves X T := by
  obtain ⟨P,Q,hP,hQ,hPT,hQT,he⟩ := par
  rcases he with hu | hi
  · rcases union_pair ht hPT hQT hu with ⟨hp,hsub⟩ | ⟨hq,hsub⟩
    · exact ⟨P,hP.resolve_left (by omega),Or.inl ⟨hp,hsub⟩⟩
    · exact ⟨Q,hQ.resolve_left (by omega),Or.inl ⟨hq,hsub⟩⟩
  · have large := proper_inter_large ht hPT hQT hi
    have hp := hP.resolve_left (by omega)
    have hq := hQ.resolve_left (by omega)
    rcases inter_serves hs ht (hF P hp) (hF Q hq) hPT hQT hi with hp' | hq'
    · exact ⟨P,hp,hp'⟩
    · exact ⟨Q,hq,hq'⟩

lemma serving_selection {L F : Finset (Finset α)}
    (hL : ∀ T ∈ L, T.card = 3)
    (hint : ∀ T ∈ L, ∀ U ∈ L, T ≠ U → (T ∩ U).card ≤ 1)
    (has : ∀ T ∈ L, ∃ X ∈ F, Serves X T) :
    ∃ f : Finset α → Finset α, (∀ T ∈ L, f T ∈ F ∧ Serves (f T) T) ∧ Set.InjOn f L := by
  classical
  let f : Finset α → Finset α := fun T => if ht : T ∈ L then Classical.choose (has T ht) else ∅
  have hf (T) (ht : T ∈ L) : f T ∈ F ∧ Serves (f T) T := by
    simp only [f,dite_eq_left ht]
    exact Classical.choose_spec (has T ht)
  refine ⟨f,hf,?_⟩
  intro T ht U hu he
  by_contra hn
  exact serves_unique (hL T ht) (hL U hu) (hint T ht U hu hn)
    (hf T ht).2 (he ▸ (hf U hu).2)

lemma three_stars_cover_lower {S R M : Finset α} {L F : Finset (Finset α)}
    (hs : S.card ≤ 6) (hr : R.card = 3) (hc : L.card = 3)
    (hL : ∀ T ∈ L, T.card = 3) (hLF : L ⊆ F)
    (hint : ∀ T ∈ L, ∀ U ∈ L, T ≠ U → (T ∩ U).card ≤ 1)
    (hcross : ∀ T ∈ L, (T ∩ R).card ≤ 1)
    (hF : ∀ X ∈ F, X ⊆ S) (hm : M ∈ F) (hRM : R ⊆ M)
    (par : ∀ X ∈ F, ∃ P Q : Finset α,
      (P.card ≤ 1 ∨ P ∈ F) ∧ (Q.card ≤ 1 ∨ Q ∈ F) ∧
      P ≠ X ∧ Q ≠ X ∧ (X = P ∪ Q ∨ X = P ∩ Q)) : 8 ≤ F.card := by
  classical
  by_contra bad
  have cap : F.card ≤ 7 := by omega
  have has : ∀ T ∈ L, ∃ X ∈ F, Serves X T :=
    fun T ht => serving_parent hs (hL T ht) hF (par T (hLF ht))
  obtain ⟨f,hf,hinj⟩ := serving_selection hL hint has
  let A := L.image f
  have ac : A.card = 3 := by rw [Finset.card_image_of_injOn hinj,hc]
  have mne (T) (ht : T ∈ L) : M ≠ T := cover_not_star hr (hcross T ht) hRM
  have mn : M ∉ L := fun hh => mne M hh rfl
  have noM (T) (ht : T ∈ L) : f T ≠ M := by
    intro he
    exact cover_not_serves hr (hL T ht) (hcross T ht) hRM (he ▸ (hf T ht).2)
  have noL (T) (ht : T ∈ L) : f T ∉ L := by
    intro hfL
    have h3 := hL (f T) hfL
    rcases (hf T ht).2 with h2 | h4 <;> omega
  have hLA : Disjoint L A := by
    apply Finset.disjoint_left.mpr
    intro X hx ha
    obtain ⟨T,ht,rfl⟩ := Finset.mem_image.mp ha
    exact noL T ht hx
  have hMA : Disjoint ({M} : Finset (Finset α)) A := by
    apply Finset.disjoint_left.mpr
    intro X hx ha
    have he := Finset.mem_singleton.mp hx
    obtain ⟨T,ht,hTX⟩ := Finset.mem_image.mp ha
    exact noM T ht (hTX.trans he)
  have hLM : Disjoint L ({M} : Finset (Finset α)) := by simpa using mn
  have sub : (L ∪ {M}) ∪ A ⊆ F := by
    intro X hx
    rcases Finset.mem_union.mp hx with hx | hx
    · rcases Finset.mem_union.mp hx with hx | hx
      · exact hLF hx
      · exact (Finset.mem_singleton.mp hx) ▸ hm
    · obtain ⟨T,ht,rfl⟩ := Finset.mem_image.mp hx
      exact (hf T ht).1
  have uc : ((L ∪ {M}) ∪ A).card = 7 := by
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hLA,hMA⟩),
      Finset.card_union_of_disjoint hLM,hc,ac,Finset.card_singleton]
  have eqF : F = (L ∪ {M}) ∪ A := by
    symm
    apply Finset.eq_of_subset_of_card_le sub
    rw [uc]
    exact cap
  have split (X) (hx : X ∈ F) : X ∈ L ∨ X = M ∨ X ∈ A := by
    rw [eqF] at hx
    simpa only [Finset.mem_union,Finset.mem_singleton,or_assoc] using hx
  have unique (X) (hx : X ∈ A) (T) (ht : T ∈ L) (hXT : Serves X T) : X = f T := by
    obtain ⟨U,hu,he⟩ := Finset.mem_image.mp hx
    have hUT : U = T := by
      by_contra hn
      exact serves_unique (hL U hu) (hL T ht) (hint U hu T ht hn)
        (he ▸ (hf U hu).2) hXT
    subst U
    exact he.symm
  have serves_in_A (X T) (hx : X ∈ F) (ht : T ∈ L) (hXT : Serves X T) : X ∈ A := by
    rcases split X hx with hxl | hxm | hxa
    · have h3 := hL X hxl
      rcases hXT with h2 | h4 <;> omega
    · exact False.elim (cover_not_serves hr (hL T ht) (hcross T ht) hRM (hxm ▸ hXT))
    · exact hxa
  have cut_bound {T P : Finset α} (ht : T ∈ L)
      (he : T = M ∩ P ∨ T = P ∩ M) : (P ∩ R).card ≤ 1 := by
    have sub : P ∩ R ⊆ T ∩ R := by
      intro x hx
      obtain ⟨hp,hrx⟩ := Finset.mem_inter.mp hx
      refine Finset.mem_inter.mpr ⟨?_,hrx⟩
      rcases he with he | he
      · rw [he]
        exact Finset.mem_inter.mpr ⟨hRM hrx,hp⟩
      · rw [he]
        exact Finset.mem_inter.mpr ⟨hp,hRM hrx⟩
    exact (Finset.card_le_card sub).trans (hcross T ht)
  have fcross (T) (ht : T ∈ L) : (f T ∩ R).card ≤ 1 := by
    obtain ⟨P,Q,hP,hQ,hPT,hQT,he⟩ := par T (hLF ht)
    rcases he with hu | hi
    · rcases union_pair (hL T ht) hPT hQT hu with ⟨hp,hsub⟩ | ⟨hq,hsub⟩
      · have hpF := hP.resolve_left (by omega)
        have hpA := serves_in_A P T hpF ht (Or.inl ⟨hp,hsub⟩)
        have eq := unique P hpA T ht (Or.inl ⟨hp,hsub⟩)
        rw [← eq]
        exact (Finset.card_le_card (Finset.inter_subset_inter_right hsub)).trans (hcross T ht)
      · have hqF := hQ.resolve_left (by omega)
        have hqA := serves_in_A Q T hqF ht (Or.inl ⟨hq,hsub⟩)
        have eq := unique Q hqA T ht (Or.inl ⟨hq,hsub⟩)
        rw [← eq]
        exact (Finset.card_le_card (Finset.inter_subset_inter_right hsub)).trans (hcross T ht)
    · have large := proper_inter_large (hL T ht) hPT hQT hi
      have classify (X) (hx : X ∈ F) (hlarge : 4 ≤ X.card) (htX : T ⊆ X) : X = M ∨ X = f T := by
        rcases split X hx with hxl | hxm | hxa
        · have h3 := hL X hxl
          omega
        · exact Or.inl hxm
        · obtain ⟨U,hu,he⟩ := Finset.mem_image.mp hxa
          have hx4 : X.card = 4 := by
            have hs := he ▸ (hf U hu).2
            rcases hs with h2 | h4 <;> omega
          exact Or.inr (unique X hxa T ht (Or.inr ⟨hx4,htX⟩))
      have pcase := classify P (hP.resolve_left (by omega)) large.1 (by rw [hi]; exact Finset.inter_subset_left)
      have qcase := classify Q (hQ.resolve_left (by omega)) large.2 (by rw [hi]; exact Finset.inter_subset_right)
      rcases pcase with rfl | hp <;> rcases qcase with rfl | hq
      · rw [Finset.inter_self] at hi
        exact False.elim (hPT hi.symm)
      · exact cut_bound ht (Or.inl (by simpa only [hq] using hi))
      · exact cut_bound ht (Or.inr (by simpa only [hp] using hi))
      · rw [hp,hq,Finset.inter_self] at hi
        exact False.elim (hPT (hp.trans hi.symm))
  have parent_cross (X) (hx : X.card ≤ 1 ∨ X ∈ F) (hne : X ≠ M) : (X ∩ R).card ≤ 1 := by
    rcases hx with hs | hfX
    · exact (Finset.card_le_card Finset.inter_subset_left).trans hs
    · rcases split X hfX with hxl | hxm | hxa
      · exact hcross X hxl
      · exact False.elim (hne hxm)
      · obtain ⟨T,ht,rfl⟩ := Finset.mem_image.mp hxa
        exact fcross T ht
  obtain ⟨P,Q,hP,hQ,hPM,hQM,he⟩ := par M hm
  have pc := parent_cross P hP hPM
  have qc := parent_cross Q hQ hQM
  have mc : (M ∩ R).card = 3 := by rw [Finset.inter_eq_right.mpr hRM,hr]
  rcases he with hu | hi
  · rw [hu,Finset.union_inter_distrib_right] at mc
    have hb := Finset.card_union_le (P ∩ R) (Q ∩ R)
    omega
  · have sub : M ∩ R ⊆ P ∩ R := by
      rw [hi]
      exact Finset.inter_subset_inter_right Finset.inter_subset_left
    have hb := Finset.card_le_card sub
    omega

end ThreeStars

namespace ThreeStars

open Rigidity

variable {α : Type} [DecidableEq α]

lemma three_stars_bad_bound {S R M : Finset α} {L F Bad : Finset (Finset α)}
    (hs : S.card ≤ 6) (hr : R.card = 3) (hc : L.card = 3)
    (hL : ∀ T ∈ L, T.card = 3) (hLF : L ⊆ F)
    (hint : ∀ T ∈ L, ∀ U ∈ L, T ≠ U → (T ∩ U).card ≤ 1)
    (hcross : ∀ T ∈ L, (T ∩ R).card ≤ 1)
    (hF : ∀ X ∈ F, X ⊆ S) (hm : M ∈ F) (hRM : R ⊆ M)
    (par : ∀ X ∈ L, ∃ P Q : Finset α,
      (P.card ≤ 1 ∨ P ∈ F) ∧ (Q.card ≤ 1 ∨ Q ∈ F) ∧
      P ≠ X ∧ Q ≠ X ∧ (X = P ∪ Q ∨ X = P ∩ Q))
    (hbad : ∀ X ∈ Bad, X.card = 3 ∧ X ∉ L ∧ ¬ R ⊆ X)
    (cap : F.card ≤ 8) : (F ∩ Bad).card ≤ 1 := by
  classical
  have has : ∀ T ∈ L, ∃ X ∈ F, Serves X T :=
    fun T ht => serving_parent hs (hL T ht) hF (par T ht)
  obtain ⟨f,hf,hinj⟩ := serving_selection hL hint has
  let A := L.image f
  have ac : A.card = 3 := by rw [Finset.card_image_of_injOn hinj,hc]
  have mn : M ∉ L := by
    intro hmL
    exact cover_not_star hr (hcross M hmL) hRM rfl
  have noM (T) (ht : T ∈ L) : f T ≠ M := by
    intro he
    exact cover_not_serves hr (hL T ht) (hcross T ht) hRM (he ▸ (hf T ht).2)
  have noL (T) (ht : T ∈ L) : f T ∉ L := by
    intro hfL
    have h3 := hL (f T) hfL
    rcases (hf T ht).2 with h2 | h4 <;> omega
  have hLA : Disjoint L A := by
    apply Finset.disjoint_left.mpr
    intro X hx ha
    obtain ⟨T,ht,rfl⟩ := Finset.mem_image.mp ha
    exact noL T ht hx
  have hMA : Disjoint ({M} : Finset (Finset α)) A := by
    apply Finset.disjoint_left.mpr
    intro X hx ha
    have he := Finset.mem_singleton.mp hx
    obtain ⟨T,ht,hTX⟩ := Finset.mem_image.mp ha
    exact noM T ht (hTX.trans he)
  have hLM : Disjoint L ({M} : Finset (Finset α)) := by simpa using mn
  let U := (L ∪ {M}) ∪ A
  have sub : U ⊆ F := by
    intro X hx
    rcases Finset.mem_union.mp hx with hx | hx
    · rcases Finset.mem_union.mp hx with hx | hx
      · exact hLF hx
      · exact (Finset.mem_singleton.mp hx) ▸ hm
    · obtain ⟨T,ht,rfl⟩ := Finset.mem_image.mp hx
      exact (hf T ht).1
  have uc : U.card = 7 := by
    dsimp [U]
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hLA,hMA⟩),
      Finset.card_union_of_disjoint hLM,hc,ac,Finset.card_singleton]
  have hd : Disjoint U (F ∩ Bad) := by
    apply Finset.disjoint_left.mpr
    intro X hu hb
    obtain ⟨h3,hnL,hnR⟩ := hbad X (Finset.mem_inter.mp hb).2
    rcases Finset.mem_union.mp hu with hu | hu
    · rcases Finset.mem_union.mp hu with hu | hu
      · exact hnL hu
      · exact hnR ((Finset.mem_singleton.mp hu) ▸ hRM)
    · obtain ⟨T,ht,rfl⟩ := Finset.mem_image.mp hu
      rcases (hf T ht).2 with h2 | h4 <;> omega
  have sub2 : U ∪ (F ∩ Bad) ⊆ F := Finset.union_subset sub Finset.inter_subset_left
  have cb := Finset.card_le_card sub2
  rw [Finset.card_union_of_disjoint hd,uc] at cb
  omega

end ThreeStars

namespace ThreeStars

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.DagTools

open Rigidity DagRigidity

variable {n : Nat} {D : Dag}

lemma bigFamily_subset (P : Finset (Fin n)) : ∀ X ∈ bigFamily n D P, X ⊆ P := by
  intro X hx
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hx
  exact Finset.inter_subset_right

lemma bigFamily_parents (h : Strict n D) (P : Finset (Fin n)) :
    ∀ X ∈ bigFamily n D P, ∃ U V : Finset (Fin n),
      (U.card ≤ 1 ∨ U ∈ bigFamily n D P) ∧ (V.card ≤ 1 ∨ V ∈ bigFamily n D P) ∧
      U ≠ X ∧ V ≠ X ∧ (X = U ∪ V ∨ X = U ∩ V) := by
  intro X hx
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hx
  have hb := (Finset.mem_filter.mp hj).2
  obtain ⟨U,V,hu,hv,hune,hvne,he⟩ := first_parents h hb ⟨n+j,rfl⟩
  have mem (W) (hw : sup_Occ n D P W) : W.card ≤ 1 ∨ W ∈ bigFamily n D P := by
    by_cases hs : W.card ≤ 1
    · exact Or.inl hs
    · exact Or.inr (mem_bigFamily h (by omega) hw)
  exact ⟨U,V,mem U hu,mem V hv,hune,hvne,he⟩

lemma dag_three_stars_lower (h : Strict n D) (P R M : Finset (Fin n))
    (L : Finset (Finset (Fin n))) (hp : P.card ≤ 6) (hr : R.card = 3) (hc : L.card = 3)
    (hL : ∀ T ∈ L, T.card = 3 ∧ sup_Occ n D P T)
    (hint : ∀ T ∈ L, ∀ U ∈ L, T ≠ U → (T ∩ U).card ≤ 1)
    (hcross : ∀ T ∈ L, (T ∩ R).card ≤ 1)
    (hm : sup_Occ n D P M) (hRM : R ⊆ M) : 8 ≤ (bigFamily n D P).card := by
  have hLF : L ⊆ bigFamily n D P := by
    intro T ht
    exact mem_bigFamily h (by have := (hL T ht).1; omega) (hL T ht).2
  have hMF : M ∈ bigFamily n D P := by
    apply mem_bigFamily h _ hm
    have hc := Finset.card_le_card hRM
    omega
  exact three_stars_cover_lower hp hr hc (fun T ht => (hL T ht).1) hLF
    hint hcross (bigFamily_subset P) hMF hRM (bigFamily_parents h P)

lemma dag_three_stars_bad_bound (h : Strict n D) (P R M : Finset (Fin n))
    (L Bad : Finset (Finset (Fin n))) (hp : P.card ≤ 6) (hr : R.card = 3) (hc : L.card = 3)
    (hL : ∀ T ∈ L, T.card = 3 ∧ sup_Occ n D P T)
    (hint : ∀ T ∈ L, ∀ U ∈ L, T ≠ U → (T ∩ U).card ≤ 1)
    (hcross : ∀ T ∈ L, (T ∩ R).card ≤ 1)
    (hm : sup_Occ n D P M) (hRM : R ⊆ M)
    (hbad : ∀ X ∈ Bad, X.card = 3 ∧ X ∉ L ∧ ¬ R ⊆ X)
    (cap : (bigFamily n D P).card ≤ 8) : (bigFamily n D P ∩ Bad).card ≤ 1 := by
  have hLF : L ⊆ bigFamily n D P := by
    intro T ht
    exact mem_bigFamily h (by have := (hL T ht).1; omega) (hL T ht).2
  have hMF : M ∈ bigFamily n D P := by
    apply mem_bigFamily h _ hm
    have hc := Finset.card_le_card hRM
    omega
  exact three_stars_bad_bound hp hr hc (fun T ht => (hL T ht).1) hLF
    hint hcross (bigFamily_subset P) hMF hRM
    (fun X hx => bigFamily_parents h P X (hLF hx)) hbad cap

end ThreeStars

namespace ThreeCase

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.Four

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.SevenGeneral

def star3 (S : Finset (Fin 10)) (i : Fin 10) : Finset (Finset (Fin 10)) :=
  (S.erase i).image (nbrs S)

def badStars (S : Finset (Fin 10)) : Finset (Finset (Fin 10)) :=
  S.image (fun i => complement S \ nbrs S i)

set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 1000000 in
lemma geometry : ∀ k : Fin 5, ∀ i ∈ casesI k,
    (complement (casesI k)).card ≤ 6 ∧ (nbrs (casesI k) i).card = 3 ∧
    (star3 (casesI k) i).card = 3 ∧
    (∀ T ∈ star3 (casesI k) i, T.card = 3) ∧
    (∀ T ∈ star3 (casesI k) i, ∀ U ∈ star3 (casesI k) i,
      T ≠ U → (T ∩ U).card ≤ 1) ∧
    (∀ T ∈ star3 (casesI k) i, (T ∩ nbrs (casesI k) i).card ≤ 1) ∧
    (∀ X ∈ badStars (casesI k), X.card = 3 ∧ X ∉ star3 (casesI k) i ∧
      ¬ nbrs (casesI k) i ⊆ X) := by
  unfold star3 badStars nbrs Adj
  decide +kernel

end ThreeCase

namespace ThreeCase

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.DagTools

open Four SevenGeneral Thirteen EightGeneral SharedDom ThreeStars LabelBudget DagRigidity

lemma family_bounds {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (four : (ineligSet 10 D).card = 4) (hz : Bzero 10 D ≤ 1)
    (k : Fin 5) (hk : casesI k = ineligSet 10 D) :
    8 ≤ (bigFamily 10 D (eligSet 10 D)).card ∧
    ((bigFamily 10 D (eligSet 10 D)).card ≤ 8 →
      (bigFamily 10 D (eligSet 10 D) ∩ badStars (casesI k)).card ≤ 1) := by
  classical
  obtain ⟨i₀,hi₀,hex⟩ := three_exact_one_superset h hc four hz
  have hi : i₀ ∈ casesI k := by simpa [hk] using hi₀
  have geo := geometry k i₀ hi
  have hp : complement (casesI k) = eligSet 10 D := by
    rw [hk]
    ext v
    simp [complement,ineligSet]
  have hn (i : Fin 10) : nbrs (casesI k) i = (eligSet 10 D).filter (Adj i) := by
    simp only [nbrs,hp]
  obtain ⟨w,_,hcover,_⟩ := hex i₀ hi₀
  let M := supp 10 D w ∩ eligSet 10 D
  have hRM : nbrs (casesI k) i₀ ⊆ M := by simpa only [hn] using hcover
  have hL : ∀ T ∈ star3 (casesI k) i₀, T.card = 3 ∧ sup_Occ 10 D (eligSet 10 D) T := by
    intro T ht
    refine ⟨geo.2.2.2.1 T ht,?_⟩
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ht
    have hie := Finset.mem_erase.mp hi
    have hiI : i ∈ ineligSet 10 D := by simpa [hk] using hie.2
    obtain ⟨v,_,_,he⟩ := hex i hiI
    exact ⟨v,(he hie.1).trans (hn i).symm⟩
  have hpc : (eligSet 10 D).card ≤ 6 := by simpa only [hp] using geo.1
  have hm : sup_Occ 10 D (eligSet 10 D) M := ⟨w,rfl⟩
  constructor
  · exact dag_three_stars_lower h.1 _ _ M _ hpc geo.2.1 geo.2.2.1 hL
      geo.2.2.2.2.1 geo.2.2.2.2.2.1 hm hRM
  · intro cap
    exact dag_three_stars_bad_bound h.1 _ _ M _ _ hpc geo.2.1 geo.2.2.1 hL
      geo.2.2.2.2.1 geo.2.2.2.2.2.1 hm hRM geo.2.2.2.2.2.2 cap

lemma one_structure {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (hz : Bzero 10 D ≤ 1) (four : (ineligSet 10 D).card = 4) (size : D.length ≤ 19) :
    ∃ k : Fin 5, casesI k = ineligSet 10 D ∧ ∃ T C : Finset Nat,
      C.card = 3 ∧ Disjoint T C ∧
      (∀ j ∈ T, j < D.length ∧ ∃ p, p < 10+j ∧ ∀ r : Fin 13,
        val D (caseRow k r) (10+j) = val D (caseRow k r) p) ∧
      (∀ j ∈ C, j < D.length ∧ tag D j = true) ∧
      (∀ j, j < D.length → j ∉ T → j ∉ C → j ∈ firstBig 10 D (eligSet 10 D)) ∧
      (bigFamily 10 D (eligSet 10 D) ∩ badStars (casesI k)).card ≤ 1 := by
  classical
  obtain ⟨k,hk,T,ht,hT⟩ := eight_copies_without_bzero h hc four
  obtain ⟨C,hcc,hCT,hC⟩ := SevenRows.charged_package h.1 hc k T hT
  have hd : Disjoint T C := hCT.symm
  have hsupp (w : Nat) : supp 10 D w \ casesI k = supp 10 D w ∩ eligSet 10 D := by
    rw [hk]
    ext a
    simp [ineligSet]
  have hCb : ∀ j ∈ C, j < D.length ∧ (supp 10 D (10+j) ∩ eligSet 10 D).card ≤ 1 := by
    intro j hj
    exact ⟨(hC j hj).1,by simpa only [hsupp] using (hC j hj).2.2⟩
  have hTb : ∀ j ∈ T, j < D.length := fun j hj => (hT j hj).1
  have copy : ∀ j ∈ T, ∃ p, p < 10+j ∧
      supp 10 D (10+j) ∩ eligSet 10 D = supp 10 D p ∩ eligSet 10 D := by
    intro j hj
    obtain ⟨p,hp,hr⟩ := (hT j hj).2
    exact ⟨p,hp,TightFour.rows_copy_support hk hr⟩
  have bounds := family_bounds h hc four hz k hk
  have budget := copy_budget h.1 (eligSet 10 D) T C hTb hCb hd copy
  have fb : (bigFamily 10 D (eligSet 10 D)).card = 8 := by omega
  obtain ⟨cc,_,partition⟩ := TightFour.tight_partition h.1 (eligSet 10 D) T C
    hTb hCb hd copy ht hcc fb size
  refine ⟨k,hk,T,C,cc,hd,hT,(fun j hj => ⟨(hC j hj).1,(hC j hj).2.1⟩),?_,bounds.2 (by omega)⟩
  intro j hj htj hcj
  have hm : j ∈ (firstBig 10 D (eligSet 10 D) ∪ T) ∪ C :=
    partition ▸ Finset.mem_range.mpr hj
  exact (Finset.mem_union.mp ((Finset.mem_union.mp hm).resolve_right hcj)).resolve_right htj

end ThreeCase

namespace MarkedDeficit

open RigidClosure

def Small (v : Nat) : Prop := MaskGood v → (Deficit v).card ≤ 1

def Pool (free hist : List Nat) : List Nat := free ++ hist

def AndStep (free hist : List Nat) (v : Nat) : Prop :=
  ∃ a ∈ Pool free hist, ∃ b ∈ Pool free hist, a &&& b = v

def Step (free hist : List Nat) (v : Nat) : Prop :=
  AndStep free hist v ∧ (hist = [] → Small v)

lemma pool_mono (free : List Nat) {xs ys : List Nat} (h : xs ⊆ ys) :
    Pool free xs ⊆ Pool free ys := by
  intro v hv
  rcases List.mem_append.mp hv with hf | hx
  · exact List.mem_append_left _ hf
  · exact List.mem_append_right _ (h hx)

lemma first_pool_small {free : List Nat} {a v : Nat}
    (hf : ∀ v ∈ free, Small v) (ha : Small a) (hv : v ∈ Pool free [a]) : Small v := by
  rcases List.mem_append.mp hv with h | h
  · exact hf v h
  · have he : v = a := by simpa using h
    exact he ▸ ha

lemma second_deficit {free : List Nat} {a b : Nat}
    (hf : ∀ v ∈ free, Small v) (ha : Small a) (hb : AndStep free [a] b)
    (good : MaskGood b) : (Deficit b).card ≤ 2 := by
  obtain ⟨p,hp,q,hq,rfl⟩ := hb
  have hpc := first_pool_small hf ha hp (good_and_left good)
  have hqc := first_pool_small hf ha hq (good_and_right good)
  have hsum := deficit_and_le p q
  omega

lemma second_pool_small_or {free : List Nat} {a b v : Nat}
    (hf : ∀ v ∈ free, Small v) (ha : Small a) (hv : v ∈ Pool free [a,b]) :
    Small v ∨ v = b := by
  rcases List.mem_append.mp hv with h | h
  · exact Or.inl (hf v h)
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | h
    · exact Or.inl ha
    · exact Or.inr h

lemma third_deficit {free : List Nat} {a b c : Nat}
    (hf : ∀ v ∈ free, Small v) (ha : Small a) (hb : AndStep free [a] b)
    (hc : AndStep free [a,b] c) (good : MaskGood c) : (Deficit c).card ≤ 3 := by
  obtain ⟨p,hp,q,hq,rfl⟩ := hc
  have pg := good_and_left good
  have qg := good_and_right good
  have hs := deficit_and_le p q
  rcases second_pool_small_or hf ha hp with hps | hpb <;>
    rcases second_pool_small_or hf ha hq with hqs | hqb
  · have hp1 := hps pg
    have hq1 := hqs qg
    omega
  · subst q
    have hp1 := hps pg
    have hb2 := second_deficit hf ha hb qg
    omega
  · subst p
    have hq1 := hqs qg
    have hb2 := second_deficit hf ha hb pg
    omega
  · subst p
    subst q
    have hb2 := second_deficit hf ha hb pg
    simpa only [Nat.and_self] using hb2.trans (by decide : 2 ≤ 3)

lemma small_not_target {v : Nat} (h : Small v) : v ≠ 7 := by
  intro he
  subst v
  have hc := h target_good
  rw [target_deficit] at hc
  omega

lemma history_no_target {free hist : List Nat} (hf : ∀ v ∈ free, Small v)
    (hlen : hist.length ≤ 3) (legal : PoolNormalize.Legal (Step free) [] hist) :
    7 ∉ Pool free hist := by
  intro ht
  rcases List.mem_append.mp ht with ht | ht
  · exact small_not_target (hf 7 ht) rfl
  rcases hist with _ | ⟨a, hist⟩
  · simp at ht
  have ha : Small a := legal.1.2 rfl
  rcases hist with _ | ⟨b,hist⟩
  · have he : 7 = a := by simpa using ht
    exact small_not_target ha he.symm
  have hb : AndStep free [a] b := legal.2.1.1
  rcases hist with _ | ⟨c,hist⟩
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with he | he
    · exact small_not_target ha he.symm
    · subst b
      have hh := second_deficit hf ha hb target_good
      rw [target_deficit] at hh
      omega
  have hc : AndStep free [a,b] c := legal.2.2.1.1
  rcases hist with _ | ⟨d,hist⟩
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with he | he | he
    · exact small_not_target ha he.symm
    · subst b
      have hh := second_deficit hf ha hb target_good
      rw [target_deficit] at hh
      omega
    · subst c
      have hh := third_deficit hf ha hb hc target_good
      rw [target_deficit] at hh
      omega
  · simp only [List.length_cons] at hlen
    omega

end MarkedDeficit

namespace MarkedDeficit

open RigidClosure

lemma normalize_first {free p gs h : List Nat} (base : p ⊆ Pool free h)
    (mark : Fin gs.length → Bool)
    (steps : ∀ j : Fin gs.length,
      if mark j then
        ∃ a ∈ p ++ gs.take j.val, ∃ b ∈ p ++ gs.take j.val, a &&& b = gs.get j
      else gs.get j ∈ p ++ gs.take j.val ∨ gs.get j ∈ free)
    (first : h = [] → ∀ j : Fin gs.length,
      (∀ k : Fin gs.length, k.val < j.val → mark k = false) →
      mark j = true → Small (gs.get j)) :
    ∃ hs, PoolNormalize.Legal (Step free) h hs ∧ p ++ gs ⊆ Pool free (h ++ hs) ∧
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
    have tailSteps : ∀ j : Fin gs.length,
        if tailMark j then
          ∃ a ∈ (p ++ [w]) ++ gs.take j.val,
          ∃ b ∈ (p ++ [w]) ++ gs.take j.val, a &&& b = gs.get j
        else gs.get j ∈ (p ++ [w]) ++ gs.take j.val ∨ gs.get j ∈ free := by
      intro j
      simpa [List.append_assoc] using steps j.succ
    by_cases hm : mark 0 = true
    · have hw : Step free h w := by
        constructor
        · obtain ⟨a,ha,b,hb,he⟩ := (show ∃ a ∈ p, ∃ b ∈ p, a &&& b = w from by
            simpa [hm] using steps 0)
          exact ⟨a,base ha,b,base hb,he⟩
        · intro hnil
          exact first hnil 0 (by intro k hk; simp at hk) hm
      have hbase : p ++ [w] ⊆ Pool free (h ++ [w]) := by
        intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · exact pool_mono free (fun _ hx => List.mem_append_left _ hx) (base ha)
        · exact List.mem_append_right _ (List.mem_append_right _ ha)
      have tailFirst : h ++ [w] = [] → ∀ j : Fin gs.length,
          (∀ k : Fin gs.length, k.val < j.val → tailMark k = false) →
          tailMark j = true → Small (gs.get j) := by
        intro hnil
        simp at hnil
      obtain ⟨hs,hlegal,hcover,hlen⟩ := ih hbase tailMark tailSteps tailFirst
      refine ⟨w :: hs,⟨hw,hlegal⟩,?_,?_⟩
      · simpa [Pool,List.append_assoc] using hcover
      · rw [hsum,hm]
        simp only [↓reduceIte,List.length_cons]
        omega
    · have hmfalse : mark 0 = false := Bool.eq_false_iff.mpr hm
      have hw : w ∈ Pool free h := by
        have hs : w ∈ p ∨ w ∈ free := by simpa [hmfalse] using steps 0
        rcases hs with hp | hf
        · exact base hp
        · exact List.mem_append_left _ hf
      have hbase : p ++ [w] ⊆ Pool free h := by
        intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · exact base ha
        · exact (List.mem_singleton.mp ha) ▸ hw
      have tailFirst : h = [] → ∀ j : Fin gs.length,
          (∀ k : Fin gs.length, k.val < j.val → tailMark k = false) →
          tailMark j = true → Small (gs.get j) := by
        intro hnil j hprev hj
        apply first hnil j.succ _ hj
        intro k hk
        by_cases hz : k.val = 0
        · have he : k = 0 := Fin.ext hz
          simpa [he] using hmfalse
        · let i : Fin gs.length := ⟨k.val-1,by
            have hb := k.isLt
            simp only [List.length_cons] at hb
            omega⟩
          have he : i.succ = k := Fin.ext (by simp [i]; omega)
          have hi : i.val < j.val := by
            have hk' : k.val < j.val + 1 := hk
            dsimp [i]
            omega
          simpa [tailMark,he] using hprev i hi
      obtain ⟨hs,hlegal,hcover,hlen⟩ := ih hbase tailMark tailSteps tailFirst
      refine ⟨hs,hlegal,?_,?_⟩
      · simpa [Pool,List.append_assoc] using hcover
      · rw [hsum,hmfalse]
        simpa using hlen

lemma trace_impossible_free {free p gs : List Nat} (hf : ∀ v ∈ free, Small v)
    (base : p ⊆ free) (C : Finset (Fin gs.length)) (cc : C.card ≤ 3)
    (target : 7 ∈ p ++ gs)
    (steps : ∀ j : Fin gs.length,
      (j ∈ C → ∃ a ∈ p ++ gs.take j.val,
        ∃ b ∈ p ++ gs.take j.val, a &&& b = gs.get j) ∧
      (j ∉ C → gs.get j ∈ p ++ gs.take j.val ∨ gs.get j ∈ free))
    (first : ∀ j : Fin gs.length, j ∈ C →
      (∀ k ∈ C, j.val ≤ k.val) → Small (gs.get j)) : False := by
  classical
  obtain ⟨hs,hl,hcover,hlen⟩ := normalize_first (free := free)
    (h := []) (by simpa [Pool] using base) (fun j => decide (j ∈ C))
    (fun j => by
      by_cases hj : j ∈ C
      · simpa [hj] using (steps j).1 hj
      · simpa [hj] using (steps j).2 hj)
    (by
      intro _ j hprev hj
      apply first j (by simpa using hj)
      intro k hk
      by_contra hn
      have hp := hprev k (by omega)
      simp [hk] at hp)
  have hlen' : hs.length ≤ 3 := by
    have he : hs.length = C.card := by simpa using hlen
    omega
  exact history_no_target hf hlen' hl (by simpa using hcover target)

lemma trace_impossible {p gs : List Nat} (base : ∀ v ∈ p, Small v)
    (C : Finset (Fin gs.length)) (cc : C.card ≤ 3) (target : 7 ∈ p ++ gs)
    (steps : ∀ j : Fin gs.length,
      (j ∈ C → ∃ a ∈ p ++ gs.take j.val,
        ∃ b ∈ p ++ gs.take j.val, a &&& b = gs.get j) ∧
      (j ∉ C → gs.get j ∈ p ++ gs.take j.val ∨ Small (gs.get j)))
    (first : ∀ j : Fin gs.length, j ∈ C →
      (∀ k ∈ C, j.val ≤ k.val) → Small (gs.get j)) : False := by
  classical
  let free := (p ++ gs).filter (fun v => decide (Small v))
  apply trace_impossible_free (free := free) _ _ C cc target _ first
  · intro v hv
    exact of_decide_eq_true (List.mem_filter.mp hv).2
  · intro v hv
    exact List.mem_filter.mpr ⟨List.mem_append_left _ hv,by simpa using base v hv⟩
  · intro j
    constructor
    · exact (steps j).1
    · intro hj
      rcases (steps j).2 hj with hcopy | hsmall
      · exact Or.inl hcopy
      · exact Or.inr (List.mem_filter.mpr
          ⟨List.mem_append_right _ (List.get_mem ..),by simpa using hsmall⟩)

end MarkedDeficit

namespace MarkedDeficit

open RigidClosure

lemma testBit_low (v i : Nat) (hi : i < 7) :
    (v % 128).testBit i = v.testBit i := by
  change (v % 2^7).testBit i = v.testBit i
  rw [Nat.testBit_mod_two_pow]
  simp [hi]

lemma good_low_iff (v : Nat) : MaskGood (v % 128) ↔ MaskGood v := by
  constructor <;> intro h r
  · have hr := h r
    simpa only [testBit_low v r.val (by omega)] using hr
  · rw [testBit_low v r.val (by omega)]
    exact h r

lemma deficit_low (v : Nat) : Deficit (v % 128) = Deficit v := by
  ext r
  simp only [Deficit,Finset.mem_filter,Finset.mem_univ,true_and,
    testBit_low v (3+r.val) (by omega)]

lemma small_low_iff (v : Nat) : Small (v % 128) ↔ Small v := by
  unfold Small
  rw [good_low_iff,deficit_low]

set_option maxHeartbeats 0 in
lemma base_small : ∀ v ∈ SevenRows.base, Small v := by
  unfold SevenRows.base Small MaskGood Deficit
  decide +kernel

lemma base_low_small (v : Nat) (hv : v % 128 ∈ SevenRows.base) : Small v :=
  (small_low_iff v).mp (base_small _ hv)

set_option maxHeartbeats 0 in
lemma inputs_small : ∀ v ∈ 0 :: inputs, Small v := by
  unfold inputs Small MaskGood Deficit
  decide +kernel

end MarkedDeficit

namespace BigProgram

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.DagTools

open Four SevenGeneral PoolDag PoolClassify MarkedDeficit

lemma big_mask_small {D : Dag} (h : Strict 10 D) (k : Fin 5) (w : Nat)
    (hbig : 2 ≤ ((supp 10 D w) \ casesI k).card) : Small (mask D k w) := by
  apply base_low_small
  have he : mask D k w % 128 =
      (SevenRows.run D (List.ofFn (casesMasks k))).getD w 0 := by
    have hm : mask D k w &&& 127 = mask D k w % 128 := by
      simpa using (Nat.and_two_pow_sub_one_eq_mod (mask D k w) 7)
    rw [← hm]
    exact MaskGeometry.sig_low_eq D k w
  rw [he]
  exact SevenRows.big_support_mask_base h k w hbig

lemma big_program_impossible {D : Dag} (h : Strict 10 D) (hc : sem_Comp 10 Adj D)
    (k : Fin 5) (T C : Finset Nat) (cc : C.card ≤ 3)
    (hC : ∀ j ∈ C, j < D.length ∧ tag D j = true)
    (hT : ∀ j ∈ T, j < D.length ∧ ∃ p, p < 10+j ∧
      ∀ r : Fin 13, val D (Thirteen.caseRow k r) (10+j) = val D (Thirteen.caseRow k r) p)
    (rest : ∀ j, j < D.length → j ∉ T → j ∉ C →
      2 ≤ ((supp 10 D (10+j)) \ casesI k).card)
    (first : ∀ j ∈ C, (∀ i ∈ C, j ≤ i) → Small (mask D k (10+j))) : False := by
  classical
  let S : Finset (Fin (values D k).length) := Finset.univ.filter (fun j => j.val ∈ C)
  have s_mem (j : Fin (values D k).length) : j ∈ S ↔ j.val ∈ C := by
    simp [S]
  have s_card : S.card = C.card := by
    apply fin_filter_card
    intro j hj
    simpa only [values,List.length_map,List.length_range] using (hC j hj).1
  refine trace_impossible (p := initials D k) (gs := values D k) ?_ S (by omega)
    (target_mem hc k) ?_ ?_
  · intro v hv
    exact inputs_small v (initial_allowed D k v hv)
  · intro j
    have hj : j.val < D.length := by
      simpa only [values,List.length_map,List.length_range] using j.isLt
    have memA := previous_mem D k hj.le (h j.val hj).1
    have memB := previous_mem D k hj.le (h j.val hj).2.1
    constructor
    · intro hjs
      have htag := (hC j.val ((s_mem j).mp hjs)).2
      refine ⟨mask D k (opA D j.val),memA,mask D k (opB D j.val),memB,?_⟩
      rw [values_get,mask_gate h k hj,htag]
      rfl
    · intro hjn
      have hjc : j.val ∉ C := fun hh => hjn ((s_mem j).mpr hh)
      by_cases hjt : j.val ∈ T
      · left
        obtain ⟨_,p,hp,hr⟩ := hT j.val hjt
        rw [values_get,mask_copy D k hr]
        exact previous_mem D k hj.le hp
      · right
        rw [values_get]
        exact big_mask_small h k (10+j.val) (rest j.val hj hjt hjc)
  · intro j hj hmin
    rw [values_get]
    apply first j.val ((s_mem j).mp hj)
    intro i hi
    let fi : Fin (values D k).length := ⟨i,by
      simpa only [values,List.length_map,List.length_range] using (hC i hi).1⟩
    exact hmin fi ((s_mem fi).mpr hi)

end BigProgram

namespace BeforeFirst

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.DagTools

open Four SevenGeneral PoolDag MaskGeometry RigidClosure

def badLabel (k : Fin 5) (r : Fin 4) : Finset (Fin 10) :=
  (complement (casesI k)).filter (fun v => Thirteen.caseRow k ⟨3+r.val,by omega⟩ v = false)

def badFamily (k : Fin 5) : Finset (Finset (Fin 10)) := Finset.univ.image (badLabel k)

set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 1000000 in
lemma bad_geometry : ∀ k : Fin 5,
    (∀ r : Fin 4, (badLabel k r).card = 3) ∧ Function.Injective (badLabel k) ∧
    badFamily k = (casesI k).image (fun i => complement (casesI k) \ nbrs (casesI k) i) := by
  unfold badLabel badFamily Function.Injective complement casesI nbrs Thirteen.caseRow
    Thirteen.liftMask casesMasks Adj
  decide +kernel

set_option maxHeartbeats 0 in
lemma raw_not_good : ∀ v ∈ 0 :: MaskGeometry.inputs, ¬ MaskGood v := by
  unfold MaskGood MaskGeometry.inputs
  decide +kernel

set_option maxHeartbeats 0 in
lemma raw_pair_not_good : ∀ a ∈ 0 :: MaskGeometry.inputs, ∀ b ∈ 0 :: MaskGeometry.inputs,
    ¬ MaskGood (a ||| b) := by
  unfold MaskGood MaskGeometry.inputs
  decide +kernel

lemma project_eq_of_mask_eq {D : Dag} {k : Fin 5} {a b : Nat}
    (he : mask D k a = mask D k b) : project D k a = project D k b := by
  classical
  ext v
  by_cases hv : v ∈ complement (casesI k)
  · obtain ⟨i,hi⟩ := (geometry k).2.2.1 v hv
    have hb := congrArg (fun x : Nat => (x/128).testBit i.val) he
    change ((sig D k a)/128).testBit i.val = ((sig D k b)/128).testBit i.val at hb
    rw [sig_high_bit,sig_high_bit,hi] at hb
    exact decide_eq_decide.mp hb
  · simp only [project,Finset.mem_inter,hv,and_false]

lemma missing_big_label {D : Dag} (hS : Strict 10 D) (k : Fin 5) (w : Nat) (r : Fin 4)
    (hz : (mask D k w).testBit (3+r.val) = false) (hc : 3 ≤ (project D k w).card) :
    project D k w = badLabel k r := by
  have hzero : val D (Thirteen.caseRow k ⟨3+r.val,by omega⟩) w = false := by
    rw [mask_bit] at hz
    exact hz
  have sub : project D k w ⊆ badLabel k r := by
    intro v hv
    obtain ⟨hs,hv⟩ := Finset.mem_inter.mp hv
    apply Finset.mem_filter.mpr
    refine ⟨hv,Bool.eq_false_iff.mpr ?_⟩
    intro ht
    have ho := sem_val_of_supp hS hs ht
    exact Bool.false_ne_true (hzero.symm.trans ho)
  apply Finset.eq_of_subset_of_card_le sub
  rw [(bad_geometry k).1 r]
  exact hc

lemma unique_bad_row {D : Dag} (hS : Strict 10 D) (k : Fin 5)
    (bound : (DagRigidity.bigFamily 10 D (complement (casesI k)) ∩ badFamily k).card ≤ 1) :
    ∃ r0 : Fin 4, ∀ w r, project D k w = badLabel k r → r = r0 := by
  classical
  have unique : ∀ w r z s, project D k w = badLabel k r →
      project D k z = badLabel k s → r = s := by
    intro w r z s hr hs
    have member (w : Nat) (r : Fin 4) (he : project D k w = badLabel k r) :
        badLabel k r ∈ DagRigidity.bigFamily 10 D (complement (casesI k)) ∩ badFamily k := by
      apply Finset.mem_inter.mpr
      refine ⟨?_,Finset.mem_image.mpr ⟨r,Finset.mem_univ _,rfl⟩⟩
      apply DagRigidity.mem_bigFamily hS
      · rw [(bad_geometry k).1 r]
        omega
      · exact ⟨w,he⟩
    have eq := Finset.card_le_one.mp bound _ (member w r hr) _ (member z s hs)
    exact (bad_geometry k).2.1 eq
  by_cases hex : ∃ w r, project D k w = badLabel k r
  · obtain ⟨w,r,hr⟩ := hex
    exact ⟨r,fun z s hs => unique z s w r hs hr⟩
  · exact ⟨0,fun w r hr => False.elim (hex ⟨w,r,hr⟩)⟩

lemma premarked {D : Dag} (hS : Strict 10 D) (k : Fin 5) (T C : Finset Nat)
    (copy : ∀ j ∈ T, j < D.length → ∃ p, p < 10+j ∧ mask D k (10+j) = mask D k p)
    (partition : ∀ j, j < D.length → j ∉ T → j ∉ C →
      2 ≤ (project D k (10+j)).card ∧
      ∀ w, w < 10+j → project D k w ≠ project D k (10+j))
    (r0 : Fin 4) (unique : ∀ w r, project D k w = badLabel k r → r = r0)
    (j0 : Nat) (hlim : j0 ≤ D.length) (first : ∀ j, j < j0 → j ∉ C) :
    ∀ w, w < 10+j0 →
      ((project D k w).card ≤ 1 → mask D k w ∈ 0 :: MaskGeometry.inputs) ∧
      (MaskGood (mask D k w) → Deficit (mask D k w) ⊆ {r0}) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases input : w < 10
    · have hv : mask D k w ∈ 0 :: MaskGeometry.inputs := by
        rw [mask_input D k input]
        exact ((geometry k).2.2.2.1 ⟨w,input⟩).2
      exact ⟨fun _ => hv,fun hg => False.elim (raw_not_good _ hv hg)⟩
    · let j := w-10
      have eqw : w = 10+j := by dsimp [j]; omega
      have hj0 : j < j0 := by omega
      have hj : j < D.length := by omega
      have earlier (p : Nat) (hp : p < 10+j) := ih p (by omega) (by omega)
      rw [eqw]
      by_cases ht : j ∈ T
      · obtain ⟨p,hp,he⟩ := copy j ht hj
        have hs := project_eq_of_mask_eq he
        have old := earlier p hp
        refine ⟨?_,?_⟩
        · intro small
          rw [he]
          apply old.1
          simpa only [hs] using small
        · intro good
          rw [he] at good ⊢
          exact old.2 good
      · obtain ⟨big,fresh⟩ := partition j hj ht (first j hj0)
        refine ⟨fun small => False.elim (by omega),?_⟩
        intro good
        have oldA := earlier (opA D j) (hS j hj).1
        have oldB := earlier (opB D j) (hS j hj).2.1
        cases hg : tag D j
        · have eq := mask_gate hS k hj
          simp only [hg,Bool.false_eq_true,ite_false] at eq
          by_cases pair : (project D k (10+j)).card = 2
          · have cards := TightFour.fresh_pair_inputs hS (complement (casesI k)) hj hg pair fresh
            have ca : (project D k (opA D j)).card = 1 := cards.1
            have cb : (project D k (opB D j)).card = 1 := cards.2
            have aRaw := oldA.1 ca.le
            have bRaw := oldB.1 cb.le
            rw [eq] at good
            exact False.elim (raw_pair_not_good _ aRaw _ bRaw good)
          · intro r hr
            have hz : (mask D k (10+j)).testBit (3+r.val) = false :=
              (Finset.mem_filter.mp hr).2
            have label := missing_big_label hS k (10+j) r hz (by omega)
            exact Finset.mem_singleton.mpr (unique (10+j) r label)
        · have eq := mask_gate hS k hj
          simp only [hg,ite_true] at eq
          rw [eq] at good ⊢
          rw [deficit_and]
          exact Finset.union_subset (oldA.2 (good_and_left good)) (oldB.2 (good_and_right good))

lemma first_good_deficit {D : Dag} (hS : Strict 10 D) (k : Fin 5) (T C : Finset Nat)
    (copy : ∀ j ∈ T, j < D.length → ∃ p, p < 10+j ∧ mask D k (10+j) = mask D k p)
    (partition : ∀ j, j < D.length → j ∉ T → j ∉ C →
      2 ≤ (project D k (10+j)).card ∧
      ∀ w, w < 10+j → project D k w ≠ project D k (10+j))
    (bound : (DagRigidity.bigFamily 10 D (complement (casesI k)) ∩ badFamily k).card ≤ 1)
    (j0 : Nat) (hj : j0 < D.length) (htag : tag D j0 = true)
    (first : ∀ j, j < j0 → j ∉ C) (good : MaskGood (mask D k (10+j0))) :
    (Deficit (mask D k (10+j0))).card ≤ 1 := by
  obtain ⟨r0,unique⟩ := unique_bad_row hS k bound
  have all := premarked hS k T C copy partition r0 unique j0 hj.le first
  have eq := mask_gate hS k hj
  simp only [htag,ite_true] at eq
  rw [eq] at good ⊢
  have ha := (all (opA D j0) (hS j0 hj).1).2 (good_and_left good)
  have hb := (all (opB D j0) (hS j0 hj).2.1).2 (good_and_right good)
  have sub : Deficit (mask D k (opA D j0) &&& mask D k (opB D j0)) ⊆ {r0} := by
    rw [deficit_and]
    exact Finset.union_subset ha hb
  exact (Finset.card_le_card sub).trans (by simp)

end BeforeFirst

namespace ThreeCase

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.DagTools

open Four SevenGeneral Thirteen LabelBudget DagRigidity PoolDag MaskGeometry

lemma four_ineligible_bzero_le_one_impossible {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 Adj D) (hz : Bzero 10 D ≤ 1)
    (four : (ineligSet 10 D).card = 4) (size : D.length ≤ 19) : False := by
  classical
  obtain ⟨k,hk,T,C,cc,_,hT,hC,rest,bad⟩ := one_structure h hc hz four size
  have hp : complement (casesI k) = eligSet 10 D := by
    rw [hk]
    ext v
    simp [complement,ineligSet]
  have hproj (w : Nat) : project D k w = supp 10 D w ∩ eligSet 10 D := by
    simp only [project,hp]
  have hsupp (w : Nat) : supp 10 D w \ casesI k = supp 10 D w ∩ eligSet 10 D := by
    rw [hk]
    ext v
    simp [ineligSet]
  apply BigProgram.big_program_impossible h.1 hc k T C (by omega) hC hT ?_ ?_
  · intro j hj htj hcj
    rw [hsupp]
    exact (mem_firstBig.mp (rest j hj htj hcj)).2.1
  · intro j hj hfirst good
    apply BeforeFirst.first_good_deficit h.1 k T C ?_ ?_ ?_ j
      (hC j hj).1 (hC j hj).2 ?_ good
    · intro i hi _
      obtain ⟨p,hp,he⟩ := (hT i hi).2
      exact ⟨p,hp,mask_copy D k he⟩
    · intro i hi hti hci
      have hf := (mem_firstBig.mp (rest i hi hti hci)).2
      simpa only [hproj] using hf
    · rw [hp,(BeforeFirst.bad_geometry k).2.2]
      exact bad
    · intro i hij hic
      have hlo := hfirst i hic
      omega

end ThreeCase

namespace SharedDom

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.DagTools

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.Four

end SharedDom

namespace SharedDom

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.DagTools

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.Four

lemma dom_out {n : Nat} {D : Dag} (v : Nat) : sem_Dom n D (outW n D) v := by
  by_cases heq : outW n D = v
  · exact Or.inl heq
  · right
    intro hp
    rcases Relation.ReflTransGen.cases_tail hp with h | ⟨u,_,hu⟩
    · exact heq h
    · exact hu.2 rfl

def ExactSlot (D : Dag) (i : Fin 10) : Prop :=
  ∃ e : Nat × Bool, e.1 < D.length ∧ tag D e.1 = true ∧
    supp 10 D (src D e) ∩ eligSet 10 D = (eligSet 10 D).filter (Adj i) ∧
    ∀ x ∈ (eligSet 10 D).filter (Adj i), e ∈ sem_W 10 D x

lemma exact_slot_shared {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (four : (ineligSet 10 D).card = 4)
    {i j : Fin 10} (hi : i ∈ ineligSet 10 D) (hj : j ∈ ineligSet 10 D)
    (hne : i ≠ j) {b : Nat} (ci : sem_Chain 10 D i.val b)
    (dj : sem_Dom 10 D b j.val) : ExactSlot D i := by
  have hind : ∀ a ∈ ineligSet 10 D, ∀ b ∈ ineligSet 10 D, ¬ Adj a b := by
    intro a ha b hb hab
    rcases sem_elig_cover graph_ok h hc hab with ea | eb
    · exact (sem_mem_inelig.mp ha) ea
    · exact (sem_mem_inelig.mp hb) eb
  have geo := all_four_geometry (ineligSet 10 D) four hind
  have compl : complement (ineligSet 10 D) = eligSet 10 D := by
    ext v
    simp [complement, ineligSet]
  have ind : ∀ a ∈ eligSet 10 D, ∀ b ∈ eligSet 10 D,
      ¬ Adj i a → ¬ Adj i b → ¬ Adj a b := by
    simpa only [compl] using geo.1 i hi
  have private_neighbor : ∃ a ∈ eligSet 10 D, Adj j a ∧ ¬ Adj i a := by
    obtain ⟨a,hja,hia⟩ := graph_ok.2.2.1 j i (Ne.symm hne)
    have ha : a ∈ eligSet 10 D := by
      rcases sem_elig_cover graph_ok h hc hja with ej | ea
      · exact False.elim ((sem_mem_inelig.mp hj) ej)
      · exact ea
    exact ⟨a,ha,hja,hia⟩
  obtain ⟨g,s,hg,ht,_,chain,hs⟩ :=
    exact_non_neighbors_shared graph_ok h.1 hc (eligSet 10 D) i j b ci dj ind private_neighbor
  refine ⟨(g,s),hg,ht,hs,fun x hx => ?_⟩
  have hxE := (Finset.mem_filter.mp hx).1
  have hxsrc : x ∈ supp 10 D (src D (g,s)) := (Finset.mem_inter.mp (hs.symm ▸ hx)).1
  refine sem_mem_W.mpr ⟨hg,hxsrc,fun hxout => ?_⟩
  have hother := sem_supp_and_sub h.1 hg ht (!s) hxout
  have hxi := sem_dom_pure graph_ok h.1 hc i _ (sem_chain_dom h.1 chain) hother
  have eq := Finset.mem_singleton.mp hxi
  exact (sem_mem_inelig.mp hi) (eq ▸ hxE)

lemma exact_slot_chain_out {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (four : (ineligSet 10 D).card = 4)
    {i : Fin 10} (hi : i ∈ ineligSet 10 D)
    (ci : sem_Chain 10 D i.val (outW 10 D)) : ExactSlot D i := by
  have positive : 0 < ((ineligSet 10 D).erase i).card := by
    rw [Finset.card_erase_of_mem hi, four]
    decide
  obtain ⟨j,hj⟩ := Finset.card_pos.mp positive
  have jinfo := Finset.mem_erase.mp hj
  exact exact_slot_shared h hc four hi jinfo.2 (Ne.symm jinfo.1) ci (dom_out j.val)

noncomputable def badSlotCenters (D : Dag) : Finset (Fin 10) := by
  classical
  exact (ineligSet 10 D).filter (fun i => ¬ ExactSlot D i)

lemma mem_badSlotCenters {D : Dag} {i : Fin 10} :
    i ∈ badSlotCenters D ↔ i ∈ ineligSet 10 D ∧ ¬ ExactSlot D i := by
  classical
  simp [badSlotCenters]

lemma bad_slot_centers_le_bzero {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (four : (ineligSet 10 D).card = 4) : (badSlotCenters D).card ≤ Bzero 10 D := by
  classical
  have hex : ∀ i : Fin 10, ∃ b : Nat, i ∈ badSlotCenters D →
      sem_Chain 10 D i.val b ∧ 2 ≤ fanout D b ∧ supp 10 D b = ∅ := by
    intro i
    by_cases hi : i ∈ badSlotCenters D
    · obtain ⟨hin,hbad⟩ := mem_badSlotCenters.mp hi
      rcases sem_inelig_reach graph_ok h hc hin with ci | ⟨b,ci,hfb,hsb⟩
      · exact False.elim (hbad (exact_slot_chain_out h hc four hin ci))
      · exact ⟨b,fun _ => ⟨ci,hfb,hsb⟩⟩
    · exact ⟨0,fun hh => False.elim (hi hh)⟩
  choose branch hb using hex
  have injective : Set.InjOn branch (badSlotCenters D) := by
    intro i hi j hj heq
    by_contra hne
    obtain ⟨ci,_,_⟩ := hb i hi
    obtain ⟨cj,_,_⟩ := hb j hj
    have ci' : sem_Chain 10 D i.val (branch j) := heq ▸ ci
    exact (mem_badSlotCenters.mp hi).2 (exact_slot_shared h hc four
      (mem_badSlotCenters.mp hi).1 (mem_badSlotCenters.mp hj).1 hne ci' (sem_chain_dom h.1 cj))
  let B := (badSlotCenters D).image branch
  let K := (inner 10 D).filter (fun w => ¬ (supp 10 D w).Nonempty)
  have sub : B ⊆ K := by
    intro b hbB
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hbB
    exact sem_bzero_mem h.1 (hb i hi).2.1 (hb i hi).2.2
  have lower : B.card ≤ ∑ b ∈ B, (fanout D b - 1) := by
    calc
      B.card = ∑ _b ∈ B, (1 : Nat) := by simp
      _ ≤ ∑ b ∈ B, (fanout D b - 1) := by
        apply Finset.sum_le_sum
        intro b hbB
        obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hbB
        have hf := (hb i hi).2.1
        omega
  have upper : (∑ b ∈ B, (fanout D b - 1)) ≤ ∑ b ∈ K, (fanout D b - 1) :=
    Finset.sum_le_sum_of_subset_of_nonneg sub (fun b _ _ => Nat.zero_le (fanout D b - 1))
  have card : B.card = (badSlotCenters D).card := Finset.card_image_of_injOn injective
  have total : (∑ b ∈ K, (fanout D b - 1)) = Bzero 10 D := by rfl
  omega

lemma two_exact_slots_of_bzero_le_two {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (four : (ineligSet 10 D).card = 4) (hz : Bzero 10 D ≤ 2) :
    ∃ i ∈ ineligSet 10 D, ∃ j ∈ ineligSet 10 D,
      i ≠ j ∧ ExactSlot D i ∧ ExactSlot D j := by
  classical
  let T := ineligSet 10 D \ badSlotCenters D
  have bound := bad_slot_centers_le_bzero h hc four
  have sub : badSlotCenters D ⊆ ineligSet 10 D := fun _ hi => (mem_badSlotCenters.mp hi).1
  have split := Finset.card_sdiff_add_card_eq_card sub
  have hT : 2 ≤ T.card := by dsimp [T]; omega
  obtain ⟨i,hi⟩ := Finset.card_pos.mp (show 0 < T.card by omega)
  have hp : 0 < (T.erase i).card := by rw [Finset.card_erase_of_mem hi]; omega
  obtain ⟨j,hj⟩ := Finset.card_pos.mp hp
  obtain ⟨hne,hjT⟩ := Finset.mem_erase.mp hj
  have exactT : ∀ a ∈ T, ExactSlot D a := by
    intro a ha
    obtain ⟨hin,hbad⟩ := Finset.mem_sdiff.mp ha
    by_contra he
    exact hbad (mem_badSlotCenters.mpr ⟨hin,he⟩)
  exact ⟨i,(Finset.mem_sdiff.mp hi).1,j,(Finset.mem_sdiff.mp hjT).1,
    Ne.symm hne,exactT i hi,exactT j hjT⟩

lemma exact_slot_of_bzero_le_three {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (four : (ineligSet 10 D).card = 4) (hz : Bzero 10 D ≤ 3) :
    ∃ i ∈ ineligSet 10 D, ExactSlot D i := by
  classical
  let T := ineligSet 10 D \ badSlotCenters D
  have bound := bad_slot_centers_le_bzero h hc four
  have sub : badSlotCenters D ⊆ ineligSet 10 D := fun _ hi => (mem_badSlotCenters.mp hi).1
  have split := Finset.card_sdiff_add_card_eq_card sub
  have hT : 0 < T.card := by dsimp [T]; omega
  obtain ⟨i,hi⟩ := Finset.card_pos.mp hT
  obtain ⟨hin,hbad⟩ := Finset.mem_sdiff.mp hi
  refine ⟨i,hin,?_⟩
  by_contra he
  exact hbad (mem_badSlotCenters.mpr ⟨hin,he⟩)

end SharedDom

namespace SharedDom

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.DagTools

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.Four

lemma omission_unique_of_code_inclusion
    {n : Nat} {G : Fin n → Fin n → Prop} {D : Dag}
    (hG : sem_Gr G) (h : StrictLive n D) (hc : sem_Comp n G D)
    (b : Fin n → Nat) (hb : PureBranch n D b)
    {x c : Fin n} (hne : x ≠ c) (hx : x ∈ eligSet n D)
    (incl : ∀ u ∈ residualUnits n D b, x ∈ supp n D u.1 → c ∈ supp n D u.1)
    {w : Nat} (hw : x ∈ supp n D w ∧ c ∈ supp n D w) :
    ∃ e₀, ∀ e ∈ sem_W n D x, e ≠ e₀ → c ∈ supp n D (src D e) := by
  classical
  obtain ⟨z,hxz,hcz⟩ := hG.2.2.1 x c hne
  obtain ⟨_,_,h2,e₁,he₁,ht₁,_⟩ := sem_diff_two_exits hG h hc b hb hne hx incl hw hxz hcz
  have count : ((exitArcs n D (carrierDiff n D x c)).erase e₁).card = 1 := by
    rw [Finset.card_erase_of_mem he₁,h2]
  obtain ⟨e₀,he₀⟩ := Finset.card_eq_one.mp count
  refine ⟨e₀,fun e he hne₀ => ?_⟩
  by_contra hce
  obtain ⟨helt,hxsrc,hxout⟩ := sem_mem_W.mp he
  have mem : e ∈ (exitArcs n D (carrierDiff n D x c)).erase e₁ :=
    Finset.mem_erase.mpr ⟨fun eq => by
      have ht := sem_W_and h.1 he
      rw [eq,ht₁] at ht
      exact Bool.false_ne_true ht,
      sem_mem_exit_diff.mpr ⟨helt,⟨hxsrc,hce⟩,fun hh => hxout hh.1⟩⟩
  rw [he₀,Finset.mem_singleton] at mem
  exact hne₀ mem

lemma residual_separation_of_two_omissions
    {n : Nat} {G : Fin n → Fin n → Prop} {D : Dag}
    (hG : sem_Gr G) (h : StrictLive n D) (hc : sem_Comp n G D)
    (b : Fin n → Nat) (hb : PureBranch n D b)
    {x c : Fin n} (hne : x ≠ c) (hx : x ∈ eligSet n D)
    (nonempty : ∃ u ∈ residualUnits n D b, x ∈ supp n D u.1)
    {e f : Nat × Bool} (he : e ∈ sem_W n D x) (hf : f ∈ sem_W n D x)
    (hef : e ≠ f) (hec : c ∉ supp n D (src D e)) (hfc : c ∉ supp n D (src D f)) :
    ∃ u ∈ residualUnits n D b, x ∈ supp n D u.1 ∧ c ∉ supp n D u.1 := by
  classical
  by_contra hno
  have incl : ∀ u ∈ residualUnits n D b, x ∈ supp n D u.1 → c ∈ supp n D u.1 := by
    intro u hu hxu
    by_contra hcu
    exact hno ⟨u,hu,hxu,hcu⟩
  obtain ⟨u,hu,hxu⟩ := nonempty
  obtain ⟨e₀,other⟩ := omission_unique_of_code_inclusion hG h hc b hb hne hx incl
    ⟨hxu,incl u hu hxu⟩
  by_cases he₀ : e = e₀
  · exact hfc (other f hf (fun hf₀ => hef (he₀.trans hf₀.symm)))
  · exact hec (other e he he₀)

lemma exact_slot_separates {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (b : Fin 10 → Nat) (hb : PureBranch 10 D b)
    {i x c : Fin 10} (hi : i ∈ ineligSet 10 D) (slot : ExactSlot D i)
    (hx : x ∈ eligSet 10 D) (hxi : Adj i x)
    (hcE : c ∈ eligSet 10 D) (hci : ¬ Adj i c)
    (nonempty : ∃ u ∈ residualUnits 10 D b, x ∈ supp 10 D u.1)
    (A : Finset (Fin 10)) (ind : ∀ a ∈ A, ∀ d ∈ A, ¬ Adj a d)
    (ca : c ∈ A) (hit_i : ∃ a ∈ A, Adj i a) (hit_x : ∃ a ∈ A, Adj x a) :
    ∃ u ∈ residualUnits 10 D b, x ∈ supp 10 D u.1 ∧ c ∉ supp 10 D u.1 := by
  obtain ⟨e,_,_,hs,hW⟩ := slot
  have he : e ∈ sem_W 10 D x := hW x (Finset.mem_filter.mpr ⟨hx,hxi⟩)
  have hec : c ∉ supp 10 D (src D e) := by
    intro hce
    have hn : c ∈ (eligSet 10 D).filter (Adj i) := hs ▸ Finset.mem_inter.mpr ⟨hce,hcE⟩
    exact hci (Finset.mem_filter.mp hn).2
  obtain ⟨g,s,hg,_,hxs,hxo,free⟩ := sem_exposure graph_ok h.1 hc A ind x hit_x
  have hf : (g,s) ∈ sem_W 10 D x := sem_mem_W.mpr ⟨hg,hxs,hxo⟩
  have hfc : c ∉ supp 10 D (src D (g,s)) := fun hcs => Finset.disjoint_left.mp free hcs ca
  have hef : e ≠ (g,s) := by
    intro eq
    obtain ⟨a,ha,hia⟩ := hit_i
    have haE : a ∈ eligSet 10 D := by
      rcases sem_elig_cover graph_ok h hc hia with ei | ea
      · exact False.elim ((sem_mem_inelig.mp hi) ei)
      · exact ea
    have has : a ∈ supp 10 D (src D e) :=
      (Finset.mem_inter.mp (hs.symm ▸ Finset.mem_filter.mpr ⟨haE,hia⟩)).1
    rw [eq] at has
    exact Finset.disjoint_left.mp free has ha
  exact residual_separation_of_two_omissions graph_ok h hc b hb
    (fun eq => hci (eq ▸ hxi)) hx nonempty he hf hef hec hfc

lemma three_of_separations {α : Type} [DecidableEq α] (U : Finset α)
    (P Q Z : α → Prop)
    (pq : ∃ u ∈ U, P u ∧ ¬ Q u) (qp : ∃ u ∈ U, Q u ∧ ¬ P u)
    (pz : ∃ u ∈ U, P u ∧ ¬ Z u) (qz : ∃ u ∈ U, Q u ∧ ¬ Z u)
    (z : ∃ u ∈ U, Z u) : 3 ≤ U.card := by
  classical
  by_contra hlt
  have upper : U.card ≤ 2 := by omega
  obtain ⟨a,ha,pa,nqa⟩ := pq
  obtain ⟨b,hb,qb,npb⟩ := qp
  have ne : a ≠ b := fun eq => npb (eq ▸ pa)
  have sub : ({a,b} : Finset α) ⊆ U := by
    intro u hu
    simp only [Finset.mem_insert,Finset.mem_singleton] at hu
    rcases hu with rfl | rfl <;> assumption
  have eq : ({a,b} : Finset α) = U :=
    Finset.eq_of_subset_of_card_le sub (by simp [ne]; exact upper)
  have cases (u : α) (hu : u ∈ U) : u = a ∨ u = b := by
    rw [← eq] at hu
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hu
  obtain ⟨c,hc,zc⟩ := z
  rcases cases c hc with rfl | rfl
  · obtain ⟨u,hu,pu,nzu⟩ := pz
    rcases cases u hu with rfl | rfl
    · exact nzu zc
    · exact npb pu
  · obtain ⟨u,hu,qu,nzu⟩ := qz
    rcases cases u hu with rfl | rfl
    · exact nqa qu
    · exact nzu zc

end SharedDom

namespace SharedDom

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.DagTools

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.Four

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 1000000 in
lemma exposure_vertices : ∀ S : Finset V, S.card = 4 →
    (∀ a ∈ S, ∀ d ∈ S, ¬ Adj a d) →
    ∀ i ∈ S, ∀ x ∈ nbrs S i, ∀ c ∈ complement S, ¬ Adj i c →
      ∃ m ∈ complement S, ∃ y ∈ complement S,
        Adj x m ∧ Adj i y ∧ ¬ Adj c m ∧ ¬ Adj c y ∧ ¬ Adj m y := by
  unfold Adj
  decide +kernel

lemma exposure_geometry (S : Finset V) (four : S.card = 4)
    (ind : ∀ a ∈ S, ∀ d ∈ S, ¬ Adj a d)
    (i : V) (hi : i ∈ S) (x : V) (hx : x ∈ nbrs S i)
    (c : V) (hc : c ∈ complement S) (hci : ¬ Adj i c) :
    ∃ A : Finset V, (∀ a ∈ A, ∀ d ∈ A, ¬ Adj a d) ∧
      c ∈ A ∧ (∃ a ∈ A, Adj i a) ∧ (∃ a ∈ A, Adj x a) := by
  obtain ⟨m,_,y,_,hxm,hiy,hcm,hcy,hmy⟩ := exposure_vertices S four ind i hi x hx c hc hci
  refine ⟨{c,m,y}, ?_, by simp, ⟨y,by simp,hiy⟩, ⟨m,by simp,hxm⟩⟩
  intro a ha d hd
  simp only [Finset.mem_insert,Finset.mem_singleton] at ha hd
  rcases ha with rfl | rfl | rfl <;> rcases hd with rfl | rfl | rfl
  · exact graph_ok.2.1 _
  · exact hcm
  · exact hcy
  · exact fun hmc => hcm (graph_ok.1 _ _ hmc)
  · exact graph_ok.2.1 _
  · exact hmy
  · exact fun hyc => hcy (graph_ok.1 _ _ hyc)
  · exact fun hym => hmy (graph_ok.1 _ _ hym)
  · exact graph_ok.2.1 _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 1000000 in
lemma two_star_vertices : ∀ S : Finset V, S.card = 4 →
    (∀ a ∈ S, ∀ d ∈ S, ¬ Adj a d) →
    ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      ∃ x ∈ complement S, ∃ y ∈ complement S, ∃ z ∈ complement S,
        Adj i x ∧ ¬ Adj j x ∧ Adj j y ∧ ¬ Adj i y ∧ ¬ Adj i z ∧ ¬ Adj j z := by
  unfold Adj
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 1000000 in
lemma eligible_neighbors : ∀ S : Finset V, S.card = 4 →
    (∀ a ∈ S, ∀ d ∈ S, ¬ Adj a d) →
    ∀ x ∈ complement S, ∃ i ∈ S, ∃ j ∈ S, ∃ y : V,
      Adj x i ∧ Adj x j ∧ Adj x y ∧ i ≠ j ∧ y ≠ i ∧ y ≠ j := by
  unfold Adj
  decide +kernel

end SharedDom

namespace SharedDom

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.DagTools

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.Four

lemma independent_ineligible {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D) :
    ∀ a ∈ ineligSet 10 D, ∀ b ∈ ineligSet 10 D, ¬ Adj a b := by
  intro a ha b hb hab
  rcases sem_elig_cover graph_ok h hc hab with ea | eb
  · exact (sem_mem_inelig.mp ha) ea
  · exact (sem_mem_inelig.mp hb) eb

lemma complement_ineligible (D : Dag) : complement (ineligSet 10 D) = eligSet 10 D := by
  ext v
  simp [complement,ineligSet]

lemma neighbor_eligible {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    {i a : Fin 10} (hi : i ∈ ineligSet 10 D) (hia : Adj i a) : a ∈ eligSet 10 D := by
  rcases sem_elig_cover graph_ok h hc hia with ei | ea
  · exact False.elim ((sem_mem_inelig.mp hi) ei)
  · exact ea

lemma every_eligible_residual {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (four : (ineligSet 10 D).card = 4)
    (b : Fin 10 → Nat) (hb : PureBranch 10 D b)
    {x : Fin 10} (hx : x ∈ eligSet 10 D) :
    ∃ u ∈ residualUnits 10 D b, x ∈ supp 10 D u.1 := by
  have hxE : x ∈ complement (ineligSet 10 D) := by rwa [complement_ineligible]
  obtain ⟨i,hi,j,hj,y,hxi,hxj,hxy,hij,hyi,hyj⟩ :=
    eligible_neighbors (ineligSet 10 D) four (independent_ineligible h hc) x hxE
  exact sem_residual_nonempty_of_two_ineligible_neighbors graph_ok h hc b hb
    hi hj hxi hxj hxy hij hyi hyj

lemma separate_from_slot {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (four : (ineligSet 10 D).card = 4)
    (b : Fin 10 → Nat) (hb : PureBranch 10 D b)
    {i x c : Fin 10} (hi : i ∈ ineligSet 10 D) (slot : ExactSlot D i)
    (hx : x ∈ eligSet 10 D) (hxi : Adj i x)
    (hcE : c ∈ eligSet 10 D) (hci : ¬ Adj i c) :
    ∃ u ∈ residualUnits 10 D b, x ∈ supp 10 D u.1 ∧ c ∉ supp 10 D u.1 := by
  have hxN : x ∈ nbrs (ineligSet 10 D) i := by
    simp only [nbrs,complement_ineligible,Finset.mem_filter]
    exact ⟨hx,hxi⟩
  have hcE' : c ∈ complement (ineligSet 10 D) := by rwa [complement_ineligible]
  obtain ⟨A,ind,ca,hit_i,hit_x⟩ := exposure_geometry (ineligSet 10 D) four
    (independent_ineligible h hc) i hi x hxN c hcE' hci
  exact exact_slot_separates h hc b hb hi slot hx hxi hcE hci
    (every_eligible_residual h hc four b hb hx) A ind ca hit_i hit_x

lemma residual_two_of_exact_slot {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (four : (ineligSet 10 D).card = 4)
    (b : Fin 10 → Nat) (hb : PureBranch 10 D b)
    {i : Fin 10} (hi : i ∈ ineligSet 10 D) (slot : ExactSlot D i) :
    2 ≤ (residualUnits 10 D b).card := by
  classical
  have positive : 0 < ((ineligSet 10 D).erase i).card := by
    rw [Finset.card_erase_of_mem hi,four]
    decide
  obtain ⟨j,hj⟩ := Finset.card_pos.mp positive
  obtain ⟨hji,hjI⟩ := Finset.mem_erase.mp hj
  obtain ⟨c,hjc,hic⟩ := graph_ok.2.2.1 j i hji
  have hcE := neighbor_eligible h hc hjI hjc
  obtain ⟨x,hix,_⟩ := graph_ok.2.2.2 i i
  have hxE := neighbor_eligible h hc hi hix
  obtain ⟨u,hu,_,hcu⟩ := separate_from_slot h hc four b hb hi slot hxE hix hcE hic
  obtain ⟨v,hv,hcv⟩ := every_eligible_residual h hc four b hb hcE
  have hne : u ≠ v := fun eq => hcu (eq.symm ▸ hcv)
  have sub : {u,v} ⊆ residualUnits 10 D b := by
    intro w hw
    simp only [Finset.mem_insert,Finset.mem_singleton] at hw
    rcases hw with rfl | rfl <;> assumption
  have bound := Finset.card_le_card sub
  simpa [hne] using bound

lemma residual_three_of_two_exact_slots {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (four : (ineligSet 10 D).card = 4)
    (b : Fin 10 → Nat) (hb : PureBranch 10 D b)
    {i j : Fin 10} (hi : i ∈ ineligSet 10 D) (hj : j ∈ ineligSet 10 D)
    (hne : i ≠ j) (si : ExactSlot D i) (sj : ExactSlot D j) :
    3 ≤ (residualUnits 10 D b).card := by
  obtain ⟨x,hx,y,hy,z,hz,hix,hjx,hjy,hiy,hiz,hjz⟩ := two_star_vertices
    (ineligSet 10 D) four (independent_ineligible h hc) i hi j hj hne
  rw [complement_ineligible] at hx hy hz
  apply three_of_separations (residualUnits 10 D b)
    (fun u => x ∈ supp 10 D u.1) (fun u => y ∈ supp 10 D u.1) (fun u => z ∈ supp 10 D u.1)
  · exact separate_from_slot h hc four b hb hi si hx hix hy hiy
  · exact separate_from_slot h hc four b hb hj sj hy hjy hx hjx
  · exact separate_from_slot h hc four b hb hi si hx hix hz hiz
  · exact separate_from_slot h hc four b hb hj sj hy hjy hz hjz
  · exact every_eligible_residual h hc four b hb hz

lemma bzero_le_one_of_four_and_nineteen {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (four : (ineligSet 10 D).card = 4) (size : D.length ≤ 19) : Bzero 10 D ≤ 1 := by
  obtain ⟨b,hb⟩ := sem_exists_pureBranch graph_ok h.1 hc
  have el := inelig_card_add 10 D
  have res := card_residual h.1 b hb
  have total := surplus_identity h
  rw [totalSurplus_split] at total
  have budget : (residualUnits 10 D b).card + Bzero 10 D ≤ 4 := by omega
  have epos : 0 < (eligSet 10 D).card := by omega
  obtain ⟨x,hx⟩ := Finset.card_pos.mp epos
  obtain ⟨u,hu,_⟩ := every_eligible_residual h hc four b hb hx
  have rpos : 0 < (residualUnits 10 D b).card := Finset.card_pos.mpr ⟨u,hu⟩
  have zero3 : Bzero 10 D ≤ 3 := by omega
  obtain ⟨i,hi,si⟩ := exact_slot_of_bzero_le_three h hc four zero3
  have rtwo := residual_two_of_exact_slot h hc four b hb hi si
  have zero2 : Bzero 10 D ≤ 2 := by omega
  obtain ⟨i,hi,j,hj,hne,si,sj⟩ := two_exact_slots_of_bzero_le_two h hc four zero2
  have rthree := residual_three_of_two_exact_slots h hc four b hb hi hj hne si sj
  omega

end SharedDom

namespace I4Case

open PEqualNP.Outside.L_meta_2590_aux.I4Proof.DagTools

lemma four_ineligible_impossible {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 Four.Adj D) (four : (ineligSet 10 D).card = 4)
    (size : D.length ≤ 19) : False := by
  exact ThreeCase.four_ineligible_bzero_le_one_impossible h hc
    (SharedDom.bzero_le_one_of_four_and_nineteen h hc four size) four size

end I4Case

end I4Proof

namespace FoundationI4

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open DagTools

lemma graph_iff : ∀ u v, DeskDriver.adj u v ↔ I4Proof.Four.Adj u v := by
  decide +kernel

lemma graph_agreement : DeskDriver.adj = I4Proof.Four.Adj := by
  funext u v
  exact propext (graph_iff u v)

lemma four_ineligible_impossible {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 DeskDriver.adj D) (four : (ineligSet 10 D).card = 4)
    (size : D.length ≤ 19) : False := by
  rw [graph_agreement] at hc
  exact I4Proof.I4Case.four_ineligible_impossible h hc four size

lemma circuit_card_le_three (C : Circuit) (hm : Monotone2 C) (hs : C.size ≤ 19)
    (hf : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = DeskDriver.target x) :
    ∃ D : Dag, StrictLive 10 D ∧ sem_Comp 10 DeskDriver.adj D ∧ D.length ≤ 19 ∧
      (ineligSet 10 D).card ≤ 3 := by
  obtain ⟨D, hD, hlen, hc⟩ := DeskDriver.normalize hm hf
  have hsD : D.length ≤ 19 := by omega
  have hi := DeskDriver.ineligible_card hD hc
  have hn : (ineligSet 10 D).card ≠ 4 :=
    fun four => four_ineligible_impossible hD hc four hsD
  exact ⟨D, hD, hc, hsD, by omega⟩

lemma circuit_remaining_cases (C : Circuit) (hm : Monotone2 C) (hs : C.size ≤ 19)
    (hf : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = DeskDriver.target x) :
    ∃ D : Dag, StrictLive 10 D ∧ sem_Comp 10 DeskDriver.adj D ∧ D.length ≤ 19 ∧
      ((ineligSet 10 D).card ≤ 2 ∨
        ineligSet 10 D = ({1, 4, 5} : Finset (Fin 10))) := by
  obtain ⟨D, hD, hc, hlen, hi⟩ := circuit_card_le_three C hm hs hf
  by_cases hthree : (ineligSet 10 D).card = 3
  · obtain ⟨E, hE, hEC, heq, hI⟩ := Foundation.reduce_three hD hc hlen hthree
    exact ⟨E, hE, hEC, by omega, Or.inr hI⟩
  · exact ⟨D, hD, hc, hlen, Or.inl (by omega)⟩

end FoundationI4


namespace I0Proof

open PEqualNP.Outside.L_meta_2590_aux.DagTools

def combine (t a b : Bool) : Bool := if t then a && b else a || b

def mixed (p a b : ℕ → Bool) (w : ℕ) : Prop :=
  p w = true ∧ a w = false ∧ b w = false

def incoming (n m : ℕ) (left right : ℕ → ℕ) (u v : ℕ) : Prop :=
  ∃ k < m, v = n + k ∧ (u = left k ∨ u = right k)

lemma gate_source_or_predecessor :
    ∀ t pl al bl pr ar br : Bool,
      combine t pl pr = true →
      combine t al ar = false →
      combine t bl br = false →
      (t = true ∧ ((al = true ∧ br = true) ∨ (bl = true ∧ ar = true))) ∨
        (pl = true ∧ al = false ∧ bl = false) ∨
        (pr = true ∧ ar = false ∧ br = false) := by
  decide

lemma guarded_unique_source_reachable
    (n m g : ℕ) (left right : ℕ → ℕ) (tag p a b : ℕ → Bool)
    (hinput : ∀ w < n, p w = (a w || b w))
    (hpast : ∀ k < m, left k < n + k ∧ right k < n + k)
    (hval : ∀ k < m,
      p (n + k) = combine (tag k) (p (left k)) (p (right k)) ∧
      a (n + k) = combine (tag k) (a (left k)) (a (right k)) ∧
      b (n + k) = combine (tag k) (b (left k)) (b (right k)))
    (hsource : ∀ k < m, tag k = true →
      a (n + k) = false → b (n + k) = false →
      ((a (left k) = true ∧ b (right k) = true) ∨
        (b (left k) = true ∧ a (right k) = true)) → k = g) :
    ∀ w < n + m, mixed p a b w →
      Relation.ReflTransGen
        (fun u v => incoming n m left right u v ∧ mixed p a b u ∧ mixed p a b v)
        (n + g) w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hmix
    by_cases hn : w < n
    · obtain ⟨hp, ha, hb⟩ := hmix
      rw [hinput w hn, ha, hb] at hp
      contradiction
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < m := by omega
      obtain ⟨hl, hr⟩ := hpast k hk
      have hmix' := hmix
      obtain ⟨hp, ha, hb⟩ := hmix
      obtain ⟨ep, ea, eb⟩ := hval k hk
      rw [ep] at hp
      rw [ea] at ha
      rw [eb] at hb
      rcases gate_source_or_predecessor (tag k)
          (p (left k)) (a (left k)) (b (left k))
          (p (right k)) (a (right k)) (b (right k)) hp ha hb with hs | hs | hs
      · have hkg : k = g := hsource k hk hs.1 hmix'.2.1 hmix'.2.2 hs.2
        subst k
        exact Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.tail (ih (left k) hl (by omega) hs)
          ⟨⟨k, hk, rfl, Or.inl rfl⟩, hs, hmix'⟩
      · exact Relation.ReflTransGen.tail (ih (right k) hr (by omega) hs)
          ⟨⟨k, hk, rfl, Or.inr rfl⟩, hs, hmix'⟩

lemma le_of_increasing_path
    (R : ℕ → ℕ → Prop) (hlt : ∀ u v, R u v → u < v)
    {u v : ℕ} (hp : Relation.ReflTransGen R u v) : u ≤ v := by
  induction hp with
  | refl => exact Nat.le_refl _
  | tail _ hstep ih => exact Nat.le_trans ih (Nat.le_of_lt (hlt _ _ hstep))

lemma suffix_of_unique_chain
    (R Q : ℕ → ℕ → Prop)
    (hsub : ∀ u v, Q u v → R u v)
    (hlt : ∀ u v, R u v → u < v)
    {s b t : ℕ}
    (hchain : Relation.ReflTransGen
      (fun u v => R u v ∧ ∀ z, R u z → z = v) s b)
    (hbt : b ≤ t)
    (hp : Relation.ReflTransGen Q s t) : Relation.ReflTransGen Q b t := by
  revert hp
  induction hchain using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun hp => hp
  | @head u v hstep htail ih =>
    intro hp
    rcases Relation.ReflTransGen.cases_head hp with heq | ⟨z, huz, hzt⟩
    · have huv : u < v := hlt u v hstep.1
      have hvb : v ≤ b := le_of_increasing_path _ (fun _ _ h => hlt _ _ h.1) htail
      omega
    · have hzv : z = v := hstep.2 z (hsub u z huz)
      subst z
      exact ih hzt

lemma suffix_before_step_of_unique_chain
    (R Q : ℕ → ℕ → Prop)
    (hsub : ∀ u v, Q u v → R u v)
    (hlt : ∀ u v, R u v → u < v)
    {s b w t : ℕ}
    (hchain : Relation.ReflTransGen
      (fun u v => R u v ∧ ∀ z, R u z → z = v) s b)
    (hbt : b < t)
    (hwt : R w t)
    (hp : Relation.ReflTransGen Q s w) : Relation.ReflTransGen Q b w := by
  revert hp
  induction hchain using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun hp => hp
  | @head u v hstep htail ih =>
    intro hp
    rcases Relation.ReflTransGen.cases_head hp with heq | ⟨z, huz, hzw⟩
    · have hut : R u t := by simpa only [heq] using hwt
      have htv : t = v := hstep.2 t hut
      have hvb : v ≤ b := le_of_increasing_path _ (fun _ _ h => hlt _ _ h.1) htail
      omega
    · have hzv : z = v := hstep.2 z (hsub u z huz)
      subst z
      exact ih hzw

lemma closed_of_earlier_escape_on_paths
    (R : ℕ → ℕ → Prop) (S : ℕ → Prop) (b : ℕ)
    (hroot : S b)
    (hlt : ∀ u v, R u v → u < v)
    (hexit : ∀ u v, Relation.ReflTransGen R b u → R u v → S u → ¬ S v →
      ∃ z < v, ¬ S z ∧ Relation.ReflTransGen R b z) :
    ∀ w, Relation.ReflTransGen R b w → S w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hp
    rcases Relation.ReflTransGen.cases_tail hp with heq | ⟨u, hu, huv⟩
    · exact heq ▸ hroot
    · by_contra hw
      have hs : S u := ih u (hlt u w huv) hu
      obtain ⟨z, hz, hnz, hpz⟩ := hexit u w hu huv hs hw
      exact hnz (ih z hz hpz)

lemma falling_left : ∀ t cl cr : Bool,
    cl = true → combine t cl cr = false → t = true ∧ cr = false := by
  decide

lemma falling_right : ∀ t cl cr : Bool,
    cr = true → combine t cl cr = false → t = true ∧ cl = false := by
  decide

lemma guarded_carrier_obstruction
    (n m g cut out : ℕ) (left right : ℕ → ℕ) (tag p a b c : ℕ → Bool)
    (hinput : ∀ w < n, p w = (a w || b w))
    (hpast : ∀ k < m, left k < n + k ∧ right k < n + k)
    (hval : ∀ k < m,
      p (n + k) = combine (tag k) (p (left k)) (p (right k)) ∧
      a (n + k) = combine (tag k) (a (left k)) (a (right k)) ∧
      b (n + k) = combine (tag k) (b (left k)) (b (right k)) ∧
      c (n + k) = combine (tag k) (c (left k)) (c (right k)))
    (hsource : ∀ k < m, tag k = true →
      a (n + k) = false → b (n + k) = false →
      ((a (left k) = true ∧ b (right k) = true) ∨
        (b (left k) = true ∧ a (right k) = true)) → k = g)
    (hchain : Relation.ReflTransGen
      (fun u v => incoming n m left right u v ∧
        ∀ z, incoming n m left right u z → z = v) (n + g) cut)
    (hcut : c cut = true)
    (hexit : ∀ k < m, tag k = true → c (n + k) = false →
      (c (left k) = true → a (right k) = false ∧ b (right k) = false) ∧
      (c (right k) = true → a (left k) = false ∧ b (left k) = false))
    (hcutout : cut ≤ out) (hout : out < n + m)
    (hmixout : mixed p a b out) (hcout : c out = false) : False := by
  let R := incoming n m left right
  let Q := fun u v => R u v ∧ mixed p a b u ∧ mixed p a b v
  have hRlt : ∀ u v, R u v → u < v := by
    rintro u v ⟨k, hk, rfl, rfl | rfl⟩
    · exact (hpast k hk).1
    · exact (hpast k hk).2
  have hQlt : ∀ u v, Q u v → u < v := fun u v h => hRlt u v h.1
  have hreach : ∀ w < n + m, mixed p a b w → Relation.ReflTransGen Q (n + g) w :=
    guarded_unique_source_reachable n m g left right tag p a b hinput hpast
      (fun k hk => ⟨(hval k hk).1, (hval k hk).2.1, (hval k hk).2.2.1⟩) hsource
  have hclosed : ∀ w, Relation.ReflTransGen Q cut w → c w = true := by
    apply closed_of_earlier_escape_on_paths Q (fun w => c w = true) cut hcut hQlt
    intro u v hcu huv hutrue hvnot
    have hvfalse : c v = false := Bool.eq_false_iff.mpr hvnot
    have hcutv : cut < v := lt_of_le_of_lt (le_of_increasing_path Q hQlt hcu) (hQlt u v huv)
    obtain ⟨k, hk, rfl, hu⟩ := huv.1
    have hptrue := huv.2.2.1
    have hcval := (hval k hk).2.2.2
    have hpval := (hval k hk).1
    rw [hcval] at hvfalse
    rcases hu with rfl | rfl
    · obtain ⟨ht, hother⟩ := falling_left (tag k) _ _ hutrue hvfalse
      have hf : c (n + k) = false := by rw [hcval]; exact hvfalse
      obtain ⟨ha, hb⟩ := (hexit k hk ht hf).1 hutrue
      have hp : p (right k) = true := by
        rw [hpval, combine, ht] at hptrue
        cases h : p (right k) <;> simp_all
      have hz : mixed p a b (right k) := ⟨hp, ha, hb⟩
      have hpath := hreach (right k) (by have := (hpast k hk).2; omega) hz
      have hstep : R (right k) (n + k) := ⟨k, hk, rfl, Or.inr rfl⟩
      have hsuffix := suffix_before_step_of_unique_chain R Q (fun _ _ h => h.1) hRlt
        hchain hcutv hstep hpath
      exact ⟨right k, (hpast k hk).2, by simp [hother], hsuffix⟩
    · obtain ⟨ht, hother⟩ := falling_right (tag k) _ _ hutrue hvfalse
      have hf : c (n + k) = false := by rw [hcval]; exact hvfalse
      obtain ⟨ha, hb⟩ := (hexit k hk ht hf).2 hutrue
      have hp : p (left k) = true := by
        rw [hpval, combine, ht] at hptrue
        cases h : p (left k) <;> simp_all
      have hz : mixed p a b (left k) := ⟨hp, ha, hb⟩
      have hpath := hreach (left k) (by have := (hpast k hk).1; omega) hz
      have hstep : R (left k) (n + k) := ⟨k, hk, rfl, Or.inl rfl⟩
      have hsuffix := suffix_before_step_of_unique_chain R Q (fun _ _ h => h.1) hRlt
        hchain hcutv hstep hpath
      exact ⟨left k, (hpast k hk).1, by simp [hother], hsuffix⟩
  have hpout := suffix_of_unique_chain R Q (fun _ _ h => h.1) hRlt hchain hcutout
    (hreach out hout hmixout)
  have := hclosed out hpout
  simp [hcout] at this

lemma guarded_carrier_obstruction_after
    (n m g cut out : ℕ) (left right : ℕ → ℕ) (tag p a b c : ℕ → Bool)
    (hinput : ∀ w < n, p w = (a w || b w))
    (hpast : ∀ k < m, left k < n + k ∧ right k < n + k)
    (hval : ∀ k < m,
      p (n + k) = combine (tag k) (p (left k)) (p (right k)) ∧
      a (n + k) = combine (tag k) (a (left k)) (a (right k)) ∧
      b (n + k) = combine (tag k) (b (left k)) (b (right k)) ∧
      c (n + k) = combine (tag k) (c (left k)) (c (right k)))
    (hsource : ∀ k < m, tag k = true →
      a (n + k) = false → b (n + k) = false →
      ((a (left k) = true ∧ b (right k) = true) ∨
        (b (left k) = true ∧ a (right k) = true)) → k = g)
    (hchain : Relation.ReflTransGen
      (fun u v => incoming n m left right u v ∧
        ∀ z, incoming n m left right u z → z = v) (n + g) cut)
    (hcut : c cut = true)
    (hexit : ∀ k < m, cut < n + k → tag k = true → c (n + k) = false →
      (c (left k) = true → a (right k) = false ∧ b (right k) = false) ∧
      (c (right k) = true → a (left k) = false ∧ b (left k) = false))
    (hcutout : cut ≤ out) (hout : out < n + m)
    (hmixout : mixed p a b out) (hcout : c out = false) : False := by
  let R := incoming n m left right
  let Q := fun u v => R u v ∧ mixed p a b u ∧ mixed p a b v
  have hRlt : ∀ u v, R u v → u < v := by
    rintro u v ⟨k, hk, rfl, rfl | rfl⟩
    · exact (hpast k hk).1
    · exact (hpast k hk).2
  have hQlt : ∀ u v, Q u v → u < v := fun u v h => hRlt u v h.1
  have hreach : ∀ w < n + m, mixed p a b w → Relation.ReflTransGen Q (n + g) w :=
    guarded_unique_source_reachable n m g left right tag p a b hinput hpast
      (fun k hk => ⟨(hval k hk).1, (hval k hk).2.1, (hval k hk).2.2.1⟩) hsource
  have hclosed : ∀ w, Relation.ReflTransGen Q cut w → c w = true := by
    apply closed_of_earlier_escape_on_paths Q (fun w => c w = true) cut hcut hQlt
    intro u v hcu huv hutrue hvnot
    have hvfalse : c v = false := Bool.eq_false_iff.mpr hvnot
    have hcutv : cut < v := lt_of_le_of_lt (le_of_increasing_path Q hQlt hcu) (hQlt u v huv)
    obtain ⟨k, hk, rfl, hu⟩ := huv.1
    have hptrue := huv.2.2.1
    have hcval := (hval k hk).2.2.2
    have hpval := (hval k hk).1
    rw [hcval] at hvfalse
    rcases hu with rfl | rfl
    · obtain ⟨ht, hother⟩ := falling_left (tag k) _ _ hutrue hvfalse
      have hf : c (n + k) = false := by rw [hcval]; exact hvfalse
      obtain ⟨ha, hb⟩ := (hexit k hk hcutv ht hf).1 hutrue
      have hp : p (right k) = true := by
        rw [hpval, combine, ht] at hptrue
        cases h : p (right k) <;> simp_all
      have hz : mixed p a b (right k) := ⟨hp, ha, hb⟩
      have hpath := hreach (right k) (by have := (hpast k hk).2; omega) hz
      have hstep : R (right k) (n + k) := ⟨k, hk, rfl, Or.inr rfl⟩
      have hsuffix := suffix_before_step_of_unique_chain R Q (fun _ _ h => h.1) hRlt
        hchain hcutv hstep hpath
      exact ⟨right k, (hpast k hk).2, by simp [hother], hsuffix⟩
    · obtain ⟨ht, hother⟩ := falling_right (tag k) _ _ hutrue hvfalse
      have hf : c (n + k) = false := by rw [hcval]; exact hvfalse
      obtain ⟨ha, hb⟩ := (hexit k hk hcutv ht hf).2 hutrue
      have hp : p (left k) = true := by
        rw [hpval, combine, ht] at hptrue
        cases h : p (left k) <;> simp_all
      have hz : mixed p a b (left k) := ⟨hp, ha, hb⟩
      have hpath := hreach (left k) (by have := (hpast k hk).1; omega) hz
      have hstep : R (left k) (n + k) := ⟨k, hk, rfl, Or.inl rfl⟩
      have hsuffix := suffix_before_step_of_unique_chain R Q (fun _ _ h => h.1) hRlt
        hchain hcutv hstep hpath
      exact ⟨left k, (hpast k hk).1, by simp [hother], hsuffix⟩
  have hpout := suffix_of_unique_chain R Q (fun _ _ h => h.1) hRlt hchain hcutout
    (hreach out hout hmixout)
  have := hclosed out hpout
  simp [hcout] at this

lemma no_second_path
    (R Q : ℕ → ℕ → Prop)
    (hsub : ∀ u v, Q u v → R u v)
    (hlt : ∀ u v, R u v → u < v)
    {s u v w : ℕ}
    (hchain : Relation.ReflTransGen
      (fun a b => R a b ∧ ∀ z, R a z → z = b) s u)
    (huv : R u v) (hunique : ∀ z, R u z → z = v)
    (hwv : R w v) (hwu : w ≠ u)
    (hp : Relation.ReflTransGen Q s w) : False := by
  have hsuffix := suffix_before_step_of_unique_chain R Q hsub hlt hchain
    (hlt u v huv) hwv hp
  rcases Relation.ReflTransGen.cases_head hsuffix with heq | ⟨z, huz, hzw⟩
  · exact hwu heq.symm
  · have hzv : z = v := hunique z (hsub u z huz)
    have hzwle : z ≤ w := le_of_increasing_path Q (fun a b h => hlt a b (hsub a b h)) hzw
    have hwvlt : w < v := hlt w v hwv
    omega

lemma source_property_of_path
    (R : ℕ → ℕ → Prop) (P : ℕ → Prop)
    (hstep : ∀ u v, R u v → P u)
    {s t : ℕ} (hp : Relation.ReflTransGen R s t) (ht : P t) : P s := by
  rcases Relation.ReflTransGen.cases_head hp with heq | ⟨u, hsu, hut⟩
  · exact heq ▸ ht
  · exact hstep s u hsu

lemma unique_chain_of_all_sources
    {ι : Type} (e₀ : ι) (R : ℕ → ℕ → Prop)
    (Q : ι → ℕ → ℕ → Prop) (P : ι → ℕ → Prop)
    (s out : ℕ)
    (hsub : ∀ e u v, Q e u v → R u v)
    (hlt : ∀ u v, R u v → u < v)
    (hstep : ∀ e u v, Q e u v → P e u)
    (hpaths : ∀ e, Relation.ReflTransGen (Q e) s out)
    (houtput : ∀ e, P e out)
    (hbranch : ∀ u v w, R u v → R u w → v ≠ w → ∃ e, ¬ P e u) :
    Relation.ReflTransGen (fun u v => R u v ∧ ∀ z, R u z → z = v) s out := by
  have hsout : s ≤ out := le_of_increasing_path (Q e₀)
    (fun u v h => hlt u v (hsub e₀ u v h)) (hpaths e₀)
  suffices h : ∀ d w, out - w = d → w ≤ out →
      Relation.ReflTransGen (fun u v => R u v ∧ ∀ z, R u z → z = v) s w →
      Relation.ReflTransGen (fun u v => R u v ∧ ∀ z, R u z → z = v) s out from
    h (out - s) s rfl hsout Relation.ReflTransGen.refl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro w hd hwo hchain
    by_cases hwend : w = out
    · exact hwend ▸ hchain
    have hsuffix (e : ι) : Relation.ReflTransGen (Q e) w out :=
      suffix_of_unique_chain R (Q e) (hsub e) hlt hchain hwo (hpaths e)
    have hwP (e : ι) : P e w :=
      source_property_of_path (Q e) (P e) (hstep e) (hsuffix e) (houtput e)
    rcases Relation.ReflTransGen.cases_head (hsuffix e₀) with heq | ⟨v, hwv, hvout⟩
    · exact (hwend heq).elim
    · have hwvR : R w v := hsub e₀ w v hwv
      have hwvlt : w < v := hlt w v hwvR
      have hvle : v ≤ out := le_of_increasing_path (Q e₀)
        (fun a b h => hlt a b (hsub e₀ a b h)) hvout
      have huniq : ∀ z, R w z → z = v := by
        intro z hwz
        by_contra hz
        obtain ⟨e, he⟩ := hbranch w v z hwvR hwz (Ne.symm hz)
        exact he (hwP e)
      exact ih (out - v) (by omega) v rfl hvle (Relation.ReflTransGen.tail hchain ⟨hwvR, huniq⟩)

lemma source_obstruction
    {ι : Type} (e₀ : ι)
    (n m g out : ℕ) (left right : ℕ → ℕ) (tag q : ℕ → Bool)
    (p a b : ι → ℕ → Bool)
    (hinput : ∀ e w, w < n → p e w = (a e w || b e w))
    (hpast : ∀ k < m, left k < n + k ∧ right k < n + k)
    (hval : ∀ e k, k < m →
      p e (n + k) = combine (tag k) (p e (left k)) (p e (right k)) ∧
      a e (n + k) = combine (tag k) (a e (left k)) (a e (right k)) ∧
      b e (n + k) = combine (tag k) (b e (left k)) (b e (right k)))
    (hqval : ∀ k < m, q (n + k) = combine (tag k) (q (left k)) (q (right k)))
    (hsource : ∀ e k, k < m → tag k = true →
      a e (n + k) = false → b e (n + k) = false →
      ((a e (left k) = true ∧ b e (right k) = true) ∨
        (b e (left k) = true ∧ a e (right k) = true)) → k = g)
    (hbranch : ∀ u v w,
      incoming n m left right u v → incoming n m left right u w → v ≠ w →
      ∃ e, a e u = true ∨ b e u = true)
    (hmiss : ∀ k < m, k ≠ g → tag k = true →
      (∃ e, a e (left k) = false ∧ b e (left k) = false) ∧
      (∃ e, a e (right k) = false ∧ b e (right k) = false))
    (hout : out < n + m)
    (hmixout : ∀ e, mixed (p e) (a e) (b e) out)
    (hqsource : q (n + g) = true) (hqout : q out = false) : False := by
  let R := incoming n m left right
  let Q := fun e u v => R u v ∧ mixed (p e) (a e) (b e) u ∧ mixed (p e) (a e) (b e) v
  have hRlt : ∀ u v, R u v → u < v := by
    rintro u v ⟨k, hk, rfl, rfl | rfl⟩
    · exact (hpast k hk).1
    · exact (hpast k hk).2
  have hreach (e : ι) : ∀ w < n + m, mixed (p e) (a e) (b e) w →
      Relation.ReflTransGen (Q e) (n + g) w :=
    guarded_unique_source_reachable n m g left right tag (p e) (a e) (b e)
      (hinput e) hpast (hval e) (hsource e)
  have hpaths (e : ι) : Relation.ReflTransGen (Q e) (n + g) out :=
    hreach e out hout (hmixout e)
  have hchain : Relation.ReflTransGen
      (fun u v => R u v ∧ ∀ z, R u z → z = v) (n + g) out := by
    apply unique_chain_of_all_sources e₀ R Q (fun e => mixed (p e) (a e) (b e))
      (n + g) out (fun _ _ _ h => h.1) hRlt (fun _ _ _ h => h.2.1) hpaths hmixout
    intro u v w huv huw hvw
    obtain ⟨e, he⟩ := hbranch u v w huv huw hvw
    refine ⟨e, ?_⟩
    rintro ⟨_, ha, hb⟩
    rcases he with he | he
    · rw [ha] at he
      contradiction
    · rw [hb] at he
      contradiction
  have hmixed (e : ι) (w : ℕ)
      (hc : Relation.ReflTransGen
        (fun u v => R u v ∧ ∀ z, R u z → z = v) (n + g) w)
      (hw : w ≤ out) : mixed (p e) (a e) (b e) w :=
    source_property_of_path (Q e) (mixed (p e) (a e) (b e)) (fun _ _ h => h.2.1)
      (suffix_of_unique_chain R (Q e) (fun _ _ h => h.1) hRlt hc hw (hpaths e)) (hmixout e)
  have hpreserve : ∀ w, Relation.ReflTransGen
      (fun u v => R u v ∧ ∀ z, R u z → z = v) (n + g) w → w ≤ out → q w = true := by
    intro w hc
    induction hc with
    | refl => exact fun _ => hqsource
    | @tail u v hprefix hstep ih =>
      intro hvout
      have huv : u < v := hRlt u v hstep.1
      have hqu : q u = true := ih (le_trans (le_of_lt huv) hvout)
      by_contra hqv
      have hqfalse : q v = false := Bool.eq_false_iff.mpr hqv
      have hsu : n + g ≤ u := le_of_increasing_path _ (fun _ _ h => hRlt _ _ h.1) hprefix
      obtain ⟨k, hk, rfl, hu⟩ := hstep.1
      have hkg : k ≠ g := by omega
      rw [hqval k hk] at hqfalse
      rcases hu with rfl | rfl
      · obtain ⟨ht, hother⟩ := falling_left (tag k) _ _ hqu hqfalse
        obtain ⟨e, ha, hb⟩ := (hmiss k hk hkg ht).2
        have hptrue := (hmixed e (n + k) (Relation.ReflTransGen.tail hprefix hstep) hvout).1
        rw [(hval e k hk).1, combine, ht] at hptrue
        have hp : p e (right k) = true := by
          cases h : p e (right k) <;> simp_all
        have hmix : mixed (p e) (a e) (b e) (right k) := ⟨hp, ha, hb⟩
        have hpath := hreach e (right k) (by have := (hpast k hk).2; omega) hmix
        have hmate : R (right k) (n + k) := ⟨k, hk, rfl, Or.inr rfl⟩
        have hne : right k ≠ left k := by
          intro heq
          rw [heq, hqu] at hother
          contradiction
        exact no_second_path R (Q e) (fun _ _ h => h.1) hRlt hprefix
          hstep.1 hstep.2 hmate hne hpath
      · obtain ⟨ht, hother⟩ := falling_right (tag k) _ _ hqu hqfalse
        obtain ⟨e, ha, hb⟩ := (hmiss k hk hkg ht).1
        have hptrue := (hmixed e (n + k) (Relation.ReflTransGen.tail hprefix hstep) hvout).1
        rw [(hval e k hk).1, combine, ht] at hptrue
        have hp : p e (left k) = true := by
          cases h : p e (left k) <;> simp_all
        have hmix : mixed (p e) (a e) (b e) (left k) := ⟨hp, ha, hb⟩
        have hpath := hreach e (left k) (by have := (hpast k hk).1; omega) hmix
        have hmate : R (left k) (n + k) := ⟨k, hk, rfl, Or.inl rfl⟩
        have hne : left k ≠ right k := by
          intro heq
          rw [heq, hqu] at hother
          contradiction
        exact no_second_path R (Q e) (fun _ _ h => h.1) hRlt hprefix
          hstep.1 hstep.2 hmate hne hpath
  have := hpreserve out hchain (le_refl out)
  simp [hqout] at this

lemma unique_chain_or_common_branch
    {ι : Type} (e₀ : ι) (R : ℕ → ℕ → Prop)
    (Q : ι → ℕ → ℕ → Prop) (P : ι → ℕ → Prop)
    (s out : ℕ)
    (hsub : ∀ e u v, Q e u v → R u v)
    (hlt : ∀ u v, R u v → u < v)
    (hstep : ∀ e u v, Q e u v → P e u)
    (hpaths : ∀ e, Relation.ReflTransGen (Q e) s out)
    (houtput : ∀ e, P e out) :
    Relation.ReflTransGen (fun u v => R u v ∧ ∀ z, R u z → z = v) s out ∨
      ∃ cut v w,
        Relation.ReflTransGen (fun u v => R u v ∧ ∀ z, R u z → z = v) s cut ∧
        R cut v ∧ R cut w ∧ v ≠ w ∧ ∀ e, P e cut := by
  have hsout : s ≤ out := le_of_increasing_path (Q e₀)
    (fun u v h => hlt u v (hsub e₀ u v h)) (hpaths e₀)
  suffices h : ∀ d x, out - x = d → x ≤ out →
      Relation.ReflTransGen (fun u v => R u v ∧ ∀ z, R u z → z = v) s x →
      Relation.ReflTransGen (fun u v => R u v ∧ ∀ z, R u z → z = v) s out ∨
        ∃ cut v w,
          Relation.ReflTransGen (fun u v => R u v ∧ ∀ z, R u z → z = v) s cut ∧
          R cut v ∧ R cut w ∧ v ≠ w ∧ ∀ e, P e cut from
    h (out - s) s rfl hsout Relation.ReflTransGen.refl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro x hd hxo hchain
    by_cases hxend : x = out
    · exact Or.inl (hxend ▸ hchain)
    have hsuffix (e : ι) : Relation.ReflTransGen (Q e) x out :=
      suffix_of_unique_chain R (Q e) (hsub e) hlt hchain hxo (hpaths e)
    have hxP (e : ι) : P e x :=
      source_property_of_path (Q e) (P e) (hstep e) (hsuffix e) (houtput e)
    rcases Relation.ReflTransGen.cases_head (hsuffix e₀) with heq | ⟨v, hxv, hvout⟩
    · exact (hxend heq).elim
    · have hxvR : R x v := hsub e₀ x v hxv
      have hxvlt : x < v := hlt x v hxvR
      have hvle : v ≤ out := le_of_increasing_path (Q e₀)
        (fun a b h => hlt a b (hsub e₀ a b h)) hvout
      by_cases hsecond : ∃ w, R x w ∧ v ≠ w
      · obtain ⟨w, hxw, hvw⟩ := hsecond
        exact Or.inr ⟨x, v, w, hchain, hxvR, hxw, hvw, hxP⟩
      · have huniq : ∀ z, R x z → z = v := by
          intro z hxz
          by_contra hz
          exact hsecond ⟨z, hxz, Ne.symm hz⟩
        exact ih (out - v) (by omega) v rfl hvle
          (Relation.ReflTransGen.tail hchain ⟨hxvR, huniq⟩)

lemma chain_source_obstruction
    {ι : Type} (_e₀ : ι)
    (n m g out : ℕ) (left right : ℕ → ℕ) (tag q : ℕ → Bool)
    (p a b : ι → ℕ → Bool)
    (hinput : ∀ e w, w < n → p e w = (a e w || b e w))
    (hpast : ∀ k < m, left k < n + k ∧ right k < n + k)
    (hval : ∀ e k, k < m →
      p e (n + k) = combine (tag k) (p e (left k)) (p e (right k)) ∧
      a e (n + k) = combine (tag k) (a e (left k)) (a e (right k)) ∧
      b e (n + k) = combine (tag k) (b e (left k)) (b e (right k)))
    (hqval : ∀ k < m, q (n + k) = combine (tag k) (q (left k)) (q (right k)))
    (hsource : ∀ e k, k < m → tag k = true →
      a e (n + k) = false → b e (n + k) = false →
      ((a e (left k) = true ∧ b e (right k) = true) ∨
        (b e (left k) = true ∧ a e (right k) = true)) → k = g)
    (hchain : Relation.ReflTransGen
      (fun u v => incoming n m left right u v ∧
        ∀ z, incoming n m left right u z → z = v) (n + g) out)
    (hmiss : ∀ k < m, k ≠ g → tag k = true →
      (∃ e, a e (left k) = false ∧ b e (left k) = false) ∧
      (∃ e, a e (right k) = false ∧ b e (right k) = false))
    (hout : out < n + m)
    (hmixout : ∀ e, mixed (p e) (a e) (b e) out)
    (hqsource : q (n + g) = true) (hqout : q out = false) : False := by
  let R := incoming n m left right
  let Q := fun e u v => R u v ∧ mixed (p e) (a e) (b e) u ∧ mixed (p e) (a e) (b e) v
  have hRlt : ∀ u v, R u v → u < v := by
    rintro u v ⟨k, hk, rfl, rfl | rfl⟩
    · exact (hpast k hk).1
    · exact (hpast k hk).2
  have hreach (e : ι) : ∀ w < n + m, mixed (p e) (a e) (b e) w →
      Relation.ReflTransGen (Q e) (n + g) w :=
    guarded_unique_source_reachable n m g left right tag (p e) (a e) (b e)
      (hinput e) hpast (hval e) (hsource e)
  have hpaths (e : ι) : Relation.ReflTransGen (Q e) (n + g) out :=
    hreach e out hout (hmixout e)
  have hmixed (e : ι) (w : ℕ)
      (hc : Relation.ReflTransGen
        (fun u v => R u v ∧ ∀ z, R u z → z = v) (n + g) w)
      (hw : w ≤ out) : mixed (p e) (a e) (b e) w :=
    source_property_of_path (Q e) (mixed (p e) (a e) (b e)) (fun _ _ h => h.2.1)
      (suffix_of_unique_chain R (Q e) (fun _ _ h => h.1) hRlt hc hw (hpaths e)) (hmixout e)
  have hpreserve : ∀ w, Relation.ReflTransGen
      (fun u v => R u v ∧ ∀ z, R u z → z = v) (n + g) w → w ≤ out → q w = true := by
    intro w hc
    induction hc with
    | refl => exact fun _ => hqsource
    | @tail u v hprefix hstep ih =>
      intro hvout
      have huv : u < v := hRlt u v hstep.1
      have hqu : q u = true := ih (le_trans (le_of_lt huv) hvout)
      by_contra hqv
      have hqfalse : q v = false := Bool.eq_false_iff.mpr hqv
      have hsu : n + g ≤ u := le_of_increasing_path _ (fun _ _ h => hRlt _ _ h.1) hprefix
      obtain ⟨k, hk, rfl, hu⟩ := hstep.1
      have hkg : k ≠ g := by omega
      rw [hqval k hk] at hqfalse
      rcases hu with rfl | rfl
      · obtain ⟨ht, hother⟩ := falling_left (tag k) _ _ hqu hqfalse
        obtain ⟨e, ha, hb⟩ := (hmiss k hk hkg ht).2
        have hptrue := (hmixed e (n + k) (Relation.ReflTransGen.tail hprefix hstep) hvout).1
        rw [(hval e k hk).1, combine, ht] at hptrue
        have hp : p e (right k) = true := by
          cases h : p e (right k) <;> simp_all
        have hmix : mixed (p e) (a e) (b e) (right k) := ⟨hp, ha, hb⟩
        have hpath := hreach e (right k) (by have := (hpast k hk).2; omega) hmix
        have hmate : R (right k) (n + k) := ⟨k, hk, rfl, Or.inr rfl⟩
        have hne : right k ≠ left k := by
          intro heq
          rw [heq, hqu] at hother
          contradiction
        exact no_second_path R (Q e) (fun _ _ h => h.1) hRlt hprefix
          hstep.1 hstep.2 hmate hne hpath
      · obtain ⟨ht, hother⟩ := falling_right (tag k) _ _ hqu hqfalse
        obtain ⟨e, ha, hb⟩ := (hmiss k hk hkg ht).1
        have hptrue := (hmixed e (n + k) (Relation.ReflTransGen.tail hprefix hstep) hvout).1
        rw [(hval e k hk).1, combine, ht] at hptrue
        have hp : p e (left k) = true := by
          cases h : p e (left k) <;> simp_all
        have hmix : mixed (p e) (a e) (b e) (left k) := ⟨hp, ha, hb⟩
        have hpath := hreach e (left k) (by have := (hpast k hk).1; omega) hmix
        have hmate : R (left k) (n + k) := ⟨k, hk, rfl, Or.inl rfl⟩
        have hne : left k ≠ right k := by
          intro heq
          rw [heq, hqu] at hother
          contradiction
        exact no_second_path R (Q e) (fun _ _ h => h.1) hRlt hprefix
          hstep.1 hstep.2 hmate hne hpath
  have := hpreserve out hchain (le_refl out)
  simp [hqout] at this

lemma common_branch_of_separation
    {ι : Type} (e₀ : ι)
    (n m g out : ℕ) (left right : ℕ → ℕ) (tag q : ℕ → Bool)
    (p a b : ι → ℕ → Bool)
    (hinput : ∀ e w, w < n → p e w = (a e w || b e w))
    (hpast : ∀ k < m, left k < n + k ∧ right k < n + k)
    (hval : ∀ e k, k < m →
      p e (n + k) = combine (tag k) (p e (left k)) (p e (right k)) ∧
      a e (n + k) = combine (tag k) (a e (left k)) (a e (right k)) ∧
      b e (n + k) = combine (tag k) (b e (left k)) (b e (right k)))
    (hqval : ∀ k < m, q (n + k) = combine (tag k) (q (left k)) (q (right k)))
    (hsource : ∀ e k, k < m → tag k = true →
      a e (n + k) = false → b e (n + k) = false →
      ((a e (left k) = true ∧ b e (right k) = true) ∨
        (b e (left k) = true ∧ a e (right k) = true)) → k = g)
    (hmiss : ∀ k < m, k ≠ g → tag k = true →
      (∃ e, a e (left k) = false ∧ b e (left k) = false) ∧
      (∃ e, a e (right k) = false ∧ b e (right k) = false))
    (hout : out < n + m)
    (hmixout : ∀ e, mixed (p e) (a e) (b e) out)
    (hqsource : q (n + g) = true) (hqout : q out = false) :
    ∃ cut v w,
      Relation.ReflTransGen
        (fun u v => incoming n m left right u v ∧
          ∀ z, incoming n m left right u z → z = v) (n + g) cut ∧
      incoming n m left right cut v ∧ incoming n m left right cut w ∧
      v ≠ w ∧ ∀ e, mixed (p e) (a e) (b e) cut := by
  let R := incoming n m left right
  let Q := fun e u v => R u v ∧ mixed (p e) (a e) (b e) u ∧ mixed (p e) (a e) (b e) v
  have hRlt : ∀ u v, R u v → u < v := by
    rintro u v ⟨k, hk, rfl, rfl | rfl⟩
    · exact (hpast k hk).1
    · exact (hpast k hk).2
  have hreach (e : ι) : ∀ w < n + m, mixed (p e) (a e) (b e) w →
      Relation.ReflTransGen (Q e) (n + g) w :=
    guarded_unique_source_reachable n m g left right tag (p e) (a e) (b e)
      (hinput e) hpast (hval e) (hsource e)
  have hpaths (e : ι) : Relation.ReflTransGen (Q e) (n + g) out :=
    hreach e out hout (hmixout e)
  rcases unique_chain_or_common_branch e₀ R Q (fun e => mixed (p e) (a e) (b e))
      (n + g) out (fun _ _ _ h => h.1) hRlt (fun _ _ _ h => h.2.1) hpaths hmixout with
      hc | ⟨cut, v, w, hch, hcv, hcw, hvw, hall⟩
  · exact (chain_source_obstruction e₀ n m g out left right tag q p a b
      hinput hpast hval hqval hsource hc hmiss hout hmixout hqsource hqout).elim
  · exact ⟨cut, v, w, hch, hcv, hcw, hvw, hall⟩

namespace DagTools

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

@[local simp] lemma h9_local_gop_true (a b : Bool) : gop true a b = (a && b) := rfl

@[local simp] lemma h9_local_gop_false (a b : Bool) : gop false a b = (a || b) := rfl

section SurplusFlow

variable {n : ℕ} {D : Dag}

end SurplusFlow

section SemCore

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

end SemCore

section SemCodes

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

end SemCodes

end DagTools

namespace DagTools

lemma combine_eq_gop (t a b : Bool) : PEqualNP.Outside.L_meta_2590_aux.I0Proof.combine t a b = gop t a b := by
  cases t <;> rfl

lemma causal_incoming_iff_step {n : ℕ} {D : Dag} {u v : ℕ} :
    PEqualNP.Outside.L_meta_2590_aux.I0Proof.incoming n D.length (opA D) (opB D) u v ↔ sem_step n D u v := by
  constructor
  · rintro ⟨k, hk, rfl, rfl | rfl⟩
    · exact sem_step_src hk false
    · exact sem_step_src hk true
  · intro h
    obtain ⟨k, s, hk, rfl, hs⟩ := sem_step_iff.mp h
    refine ⟨k, hk, rfl, ?_⟩
    cases s
    · exact Or.inl hs.symm
    · exact Or.inr hs.symm

lemma causal_mixed_iff {n : ℕ} {D : Dag} {u v : Fin n} {w : ℕ} :
    PEqualNP.Outside.L_meta_2590_aux.I0Proof.mixed (val D (sem_two u v))
      (val D (single u)) (val D (single v)) w ↔
      val D (sem_two u v) w = true ∧ u ∉ supp n D w ∧ v ∉ supp n D w := by
  unfold PEqualNP.Outside.L_meta_2590_aux.I0Proof.mixed
  simp only [mem_supp, Bool.eq_false_iff]

end DagTools

namespace DagTools

lemma sem_slot_source_of_guards {n : ℕ} {D : Dag} {u v : Fin n} {g : ℕ}
    (hsource : ∀ e ∈ sem_W n D u, sem_bar e ∈ sem_W n D v → e.1 = g)
    (k : ℕ) (hk : k < D.length)
    (hu : u ∉ supp n D (n + k)) (hv : v ∉ supp n D (n + k))
    (hcross : (u ∈ supp n D (opA D k) ∧ v ∈ supp n D (opB D k)) ∨
      (v ∈ supp n D (opA D k) ∧ u ∈ supp n D (opB D k))) : k = g := by
  rcases hcross with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · apply hsource (k, false)
    · exact sem_mem_W.mpr ⟨hk, h1, hu⟩
    · exact sem_mem_W.mpr ⟨hk, h2, hv⟩
  · apply hsource (k, true)
    · exact sem_mem_W.mpr ⟨hk, h2, hu⟩
    · exact sem_mem_W.mpr ⟨hk, h1, hv⟩

lemma sem_slot_carrier_obstruction {n : ℕ} {D : Dag} (hS : Strict n D)
    (g cut out : ℕ) (u v c : Fin n)
    (hsource : ∀ e ∈ sem_W n D u, sem_bar e ∈ sem_W n D v → e.1 = g)
    (hchain : sem_Chain n D (n + g) cut) (hcut : c ∈ supp n D cut)
    (hexit : ∀ e ∈ sem_W n D c,
      u ∉ supp n D (src D (sem_bar e)) ∧ v ∉ supp n D (src D (sem_bar e)))
    (hcutout : cut ≤ out) (hout : out < n + D.length)
    (hp : val D (sem_two u v) out = true)
    (hu : u ∉ supp n D out) (hv : v ∉ supp n D out) (hc : c ∉ supp n D out) : False := by
  have hval (k : ℕ) (hk : k < D.length) := fun x : Fin n → Bool =>
    (val_gate hS x k hk).trans (combine_eq_gop _ _ _).symm
  apply PEqualNP.Outside.L_meta_2590_aux.I0Proof.guarded_carrier_obstruction n D.length g cut out
    (opA D) (opB D) (tag D) (val D (sem_two u v)) (val D (single u))
    (val D (single v)) (val D (single c))
    (by intro i hi; rw [val_input D _ i hi, val_input D _ i hi, val_input D _ i hi]; rfl)
    (fun k hk => ⟨(hS k hk).1, (hS k hk).2.1⟩)
    (fun k hk => ⟨hval k hk _, hval k hk _, hval k hk _, hval k hk _⟩)
    (by
      intro k hk ht hau hbv hh
      apply sem_slot_source_of_guards hsource k hk
      · simpa only [mem_supp, Bool.eq_false_iff] using hau
      · simpa only [mem_supp, Bool.eq_false_iff] using hbv
      · simpa only [mem_supp] using hh)
    (sem_rtg_mono (fun a b h =>
      ⟨causal_incoming_iff_step.mpr h.1, fun z hz =>
        (sem_step_unique h.1 (causal_incoming_iff_step.mp hz) h.2).symm⟩) hchain)
    (mem_supp.mp hcut) ?_ hcutout hout (causal_mixed_iff.mpr ⟨hp, hu, hv⟩)
    (Bool.eq_false_iff.mpr fun hc' => hc (mem_supp.mpr hc'))
  intro k hk ht hcf
  have hcnot : c ∉ supp n D (n + k) := by
    intro hc'
    have := mem_supp.mp hc'
    simp [hcf] at this
  constructor
  · intro hleft
    have he : (k, false) ∈ sem_W n D c :=
      sem_mem_W.mpr ⟨hk, by simpa only [sb_src_false] using (mem_supp.mpr hleft), hcnot⟩
    have hh := hexit (k, false) he
    simpa only [sem_bar, Bool.not_false, sb_src_true, mem_supp, Bool.eq_false_iff] using hh
  · intro hright
    have he : (k, true) ∈ sem_W n D c :=
      sem_mem_W.mpr ⟨hk, by simpa only [sb_src_true] using (mem_supp.mpr hright), hcnot⟩
    have hh := hexit (k, true) he
    simpa only [sem_bar, Bool.not_true, sb_src_false, mem_supp, Bool.eq_false_iff] using hh

lemma sem_slot_carrier_graph {n : ℕ} {D : Dag} {G : Fin n → Fin n → Prop}
    (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (g cut : ℕ) (u v c : Fin n) (huv : G u v)
    (hsource : ∀ e ∈ sem_W n D u, sem_bar e ∈ sem_W n D v → e.1 = g)
    (hchain : sem_Chain n D (n + g) cut) (hcut : c ∈ supp n D cut)
    (hexit : ∀ e ∈ sem_W n D c,
      u ∉ supp n D (src D (sem_bar e)) ∧ v ∉ supp n D (src D (sem_bar e))) : False := by
  have hcutlt := sem_supp_lt hcut
  have hlen : 0 < D.length := List.length_pos_iff.mpr h.2.2
  have hs := sem_supp_out hG hC
  apply sem_slot_carrier_obstruction h.1 g cut (outW n D) u v c hsource hchain hcut hexit
  · unfold outW; omega
  · unfold outW; omega
  · exact (hC _).mpr (sem_two_edge huv)
  · rw [hs]; exact Finset.notMem_empty _
  · rw [hs]; exact Finset.notMem_empty _
  · rw [hs]; exact Finset.notMem_empty _

end DagTools

namespace DagTools

lemma sem_slot_family_obstruction {ι : Type} (e₀ : ι)
    {n : ℕ} {D : Dag} {G : Fin n → Fin n → Prop}
    (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (g : ℕ) (u v : ι → Fin n) (hedge : ∀ e, G (u e) (v e))
    (hsource : ∀ e s, s ∈ sem_W n D (u e) → sem_bar s ∈ sem_W n D (v e) → s.1 = g)
    (hbranch : ∀ w, 2 ≤ fanout D w → ∃ e, u e ∈ supp n D w ∨ v e ∈ supp n D w)
    (hmiss : ∀ k < D.length, k ≠ g → tag D k = true → ∀ s : Bool,
      ∃ e, u e ∉ supp n D (src D (k, s)) ∧ v e ∉ supp n D (src D (k, s)))
    (q : Fin n → Bool) (hq : ¬ sem_Edge G q) (hqg : val D q (n + g) = true) : False := by
  have hval (k : ℕ) (hk : k < D.length) := fun x : Fin n → Bool =>
    (val_gate h.1 x k hk).trans (combine_eq_gop _ _ _).symm
  have hlen : 0 < D.length := List.length_pos_iff.mpr h.2.2
  have hs := sem_supp_out hG hC
  apply PEqualNP.Outside.L_meta_2590_aux.I0Proof.source_obstruction e₀ n D.length g (outW n D)
    (opA D) (opB D) (tag D) (val D q)
    (fun e => val D (sem_two (u e) (v e)))
    (fun e => val D (single (u e))) (fun e => val D (single (v e)))
    (by intro e i hi; rw [val_input D _ i hi, val_input D _ i hi, val_input D _ i hi]; rfl)
    (fun k hk => ⟨(h.1 k hk).1, (h.1 k hk).2.1⟩)
    (fun e k hk => ⟨hval k hk _, hval k hk _, hval k hk _⟩)
    (fun k hk => hval k hk q)
    (by
      intro e k hk ht hau hbv hh
      apply sem_slot_source_of_guards (hsource e) k hk
      · simpa only [mem_supp, Bool.eq_false_iff] using hau
      · simpa only [mem_supp, Bool.eq_false_iff] using hbv
      · simpa only [mem_supp] using hh)
    (by
      intro w w1 w2 h1 h2 hne
      have hs1 := causal_incoming_iff_step.mp h1
      have hs2 := causal_incoming_iff_step.mp h2
      have hfan : 2 ≤ fanout D w := by
        have hpos := sem_step_fanout hs1
        by_contra hn
        have hone : fanout D w = 1 := by omega
        exact hne (sem_step_unique hs1 hs2 hone)
      obtain ⟨e, he⟩ := hbranch w hfan
      exact ⟨e, by simpa only [mem_supp] using he⟩)
    (by
      intro k hk hkg ht
      constructor
      · obtain ⟨e, he⟩ := hmiss k hk hkg ht false
        exact ⟨e, by simpa only [sb_src_false, mem_supp, Bool.eq_false_iff] using he⟩
      · obtain ⟨e, he⟩ := hmiss k hk hkg ht true
        exact ⟨e, by simpa only [sb_src_true, mem_supp, Bool.eq_false_iff] using he⟩)
    (by unfold outW; omega)
    (by
      intro e
      apply causal_mixed_iff.mpr
      refine ⟨(hC _).mpr (sem_two_edge (hedge e)), ?_, ?_⟩
      · rw [hs]; exact Finset.notMem_empty _
      · rw [hs]; exact Finset.notMem_empty _)
    hqg (Bool.eq_false_iff.mpr fun htrue => hq ((hC q).mp htrue))

lemma sem_slot_family_obstruction_cover {ι : Type} (e₀ : ι)
    {n : ℕ} {D : Dag} {G : Fin n → Fin n → Prop}
    (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (g : ℕ) (u v : ι → Fin n) (hedge : ∀ e, G (u e) (v e))
    (hcover : ∀ a : Fin n, ∃ e, u e = a ∨ v e = a)
    (hsource : ∀ e s, s ∈ sem_W n D (u e) → sem_bar s ∈ sem_W n D (v e) → s.1 = g)
    (hbranch : ∀ w, 2 ≤ fanout D w → (supp n D w).Nonempty)
    (hmiss : ∀ k < D.length, k ≠ g → tag D k = true → ∀ s : Bool,
      ∃ e, u e ∉ supp n D (src D (k, s)) ∧ v e ∉ supp n D (src D (k, s)))
    (q : Fin n → Bool) (hq : ¬ sem_Edge G q) (hqg : val D q (n + g) = true) : False := by
  apply sem_slot_family_obstruction e₀ hG h hC g u v hedge hsource ?_ hmiss q hq hqg
  intro w hw
  obtain ⟨a, ha⟩ := hbranch w hw
  obtain ⟨e, he | he⟩ := hcover a
  · exact ⟨e, Or.inl (by simpa only [he] using ha)⟩
  · exact ⟨e, Or.inr (by simpa only [he] using ha)⟩

end DagTools

namespace DagTools

lemma sem_slot_carrier_obstruction_after {n : ℕ} {D : Dag} (hS : Strict n D)
    (g cut out : ℕ) (u v c : Fin n)
    (hsource : ∀ e ∈ sem_W n D u, sem_bar e ∈ sem_W n D v → e.1 = g)
    (hchain : sem_Chain n D (n + g) cut) (hcut : c ∈ supp n D cut)
    (hexit : ∀ e ∈ sem_W n D c, cut < n + e.1 →
      u ∉ supp n D (src D (sem_bar e)) ∧ v ∉ supp n D (src D (sem_bar e)))
    (hcutout : cut ≤ out) (hout : out < n + D.length)
    (hp : val D (sem_two u v) out = true)
    (hu : u ∉ supp n D out) (hv : v ∉ supp n D out) (hc : c ∉ supp n D out) : False := by
  have hval (k : ℕ) (hk : k < D.length) := fun x : Fin n → Bool =>
    (val_gate hS x k hk).trans (combine_eq_gop _ _ _).symm
  apply PEqualNP.Outside.L_meta_2590_aux.I0Proof.guarded_carrier_obstruction_after n D.length g cut out
    (opA D) (opB D) (tag D) (val D (sem_two u v)) (val D (single u))
    (val D (single v)) (val D (single c))
    (by intro i hi; rw [val_input D _ i hi, val_input D _ i hi, val_input D _ i hi]; rfl)
    (fun k hk => ⟨(hS k hk).1, (hS k hk).2.1⟩)
    (fun k hk => ⟨hval k hk _, hval k hk _, hval k hk _, hval k hk _⟩)
    (by
      intro k hk ht hau hbv hh
      apply sem_slot_source_of_guards hsource k hk
      · simpa only [mem_supp, Bool.eq_false_iff] using hau
      · simpa only [mem_supp, Bool.eq_false_iff] using hbv
      · simpa only [mem_supp] using hh)
    (sem_rtg_mono (fun a b h =>
      ⟨causal_incoming_iff_step.mpr h.1, fun z hz =>
        (sem_step_unique h.1 (causal_incoming_iff_step.mp hz) h.2).symm⟩) hchain)
    (mem_supp.mp hcut) ?_ hcutout hout (causal_mixed_iff.mpr ⟨hp, hu, hv⟩)
    (Bool.eq_false_iff.mpr fun hc' => hc (mem_supp.mpr hc'))
  intro k hk hafter ht hcf
  have hcnot : c ∉ supp n D (n + k) := by
    intro hc'
    have := mem_supp.mp hc'
    simp [hcf] at this
  constructor
  · intro hleft
    have he : (k, false) ∈ sem_W n D c :=
      sem_mem_W.mpr ⟨hk, by simpa only [sb_src_false] using (mem_supp.mpr hleft), hcnot⟩
    have hh := hexit (k, false) he hafter
    simpa only [sem_bar, Bool.not_false, sb_src_true, mem_supp, Bool.eq_false_iff] using hh
  · intro hright
    have he : (k, true) ∈ sem_W n D c :=
      sem_mem_W.mpr ⟨hk, by simpa only [sb_src_true] using (mem_supp.mpr hright), hcnot⟩
    have hh := hexit (k, true) he hafter
    simpa only [sem_bar, Bool.not_true, sb_src_false, mem_supp, Bool.eq_false_iff] using hh

lemma sem_slot_carrier_graph_after {n : ℕ} {D : Dag} {G : Fin n → Fin n → Prop}
    (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (g cut : ℕ) (u v c : Fin n) (huv : G u v)
    (hsource : ∀ e ∈ sem_W n D u, sem_bar e ∈ sem_W n D v → e.1 = g)
    (hchain : sem_Chain n D (n + g) cut) (hcut : c ∈ supp n D cut)
    (hexit : ∀ e ∈ sem_W n D c, cut < n + e.1 →
      u ∉ supp n D (src D (sem_bar e)) ∧ v ∉ supp n D (src D (sem_bar e))) : False := by
  have hcutlt := sem_supp_lt hcut
  have hlen : 0 < D.length := List.length_pos_iff.mpr h.2.2
  have hs := sem_supp_out hG hC
  apply sem_slot_carrier_obstruction_after h.1 g cut (outW n D) u v c hsource hchain hcut hexit
  · unfold outW; omega
  · unfold outW; omega
  · exact (hC _).mpr (sem_two_edge huv)
  · rw [hs]; exact Finset.notMem_empty _
  · rw [hs]; exact Finset.notMem_empty _
  · rw [hs]; exact Finset.notMem_empty _

end DagTools

namespace DagTools

lemma sem_step_of_reader {n : ℕ} {D : Dag} {u k : ℕ} (hk : k ∈ readers D u) :
    sem_step n D u (n + k) := by
  obtain ⟨hk, hread⟩ := Finset.mem_filter.mp hk
  have hkl := Finset.mem_range.mp hk
  exact ⟨by omega, by omega, by simpa only [Nat.add_sub_cancel_left] using hread⟩

lemma sem_fanout_one_of_unique_step {n : ℕ} {D : Dag} {u v : ℕ}
    (hstep : sem_step n D u v)
    (hunique : ∀ z, sem_step n D u z → z = v) : fanout D u = 1 := by
  have hle : (readers D u).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro k hk j hj
    have h1 := hunique (n + k) (sem_step_of_reader hk)
    have h2 := hunique (n + j) (sem_step_of_reader hj)
    omega
  have hpos := sem_step_fanout hstep
  change (readers D u).card = 1
  change 1 ≤ (readers D u).card at hpos
  omega

lemma sem_Chain_of_unique_chain {n : ℕ} {D : Dag} {a b : ℕ}
    (hchain : Relation.ReflTransGen
      (fun u v => PEqualNP.Outside.L_meta_2590_aux.I0Proof.incoming n D.length (opA D) (opB D) u v ∧
        ∀ z, PEqualNP.Outside.L_meta_2590_aux.I0Proof.incoming n D.length (opA D) (opB D) u z → z = v) a b) :
    sem_Chain n D a b := by
  apply sem_rtg_mono ?_ hchain
  intro u v h
  have hstep := causal_incoming_iff_step.mp h.1
  exact ⟨hstep, sem_fanout_one_of_unique_step hstep
    (fun z hz => h.2 z (causal_incoming_iff_step.mpr hz))⟩

lemma sem_slot_common_branch {ι : Type} (e₀ : ι)
    {n : ℕ} {D : Dag} {G : Fin n → Fin n → Prop}
    (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (g : ℕ) (u v : ι → Fin n) (hedge : ∀ e, G (u e) (v e))
    (hsource : ∀ e s, s ∈ sem_W n D (u e) → sem_bar s ∈ sem_W n D (v e) → s.1 = g)
    (hmiss : ∀ k < D.length, k ≠ g → tag D k = true → ∀ s : Bool,
      ∃ e, u e ∉ supp n D (src D (k, s)) ∧ v e ∉ supp n D (src D (k, s)))
    (q : Fin n → Bool) (hq : ¬ sem_Edge G q) (hqg : val D q (n + g) = true) :
    ∃ cut, sem_Chain n D (n + g) cut ∧ 2 ≤ fanout D cut ∧
      ∀ e, val D (sem_two (u e) (v e)) cut = true ∧
        u e ∉ supp n D cut ∧ v e ∉ supp n D cut := by
  have hval (k : ℕ) (hk : k < D.length) := fun x : Fin n → Bool =>
    (val_gate h.1 x k hk).trans (combine_eq_gop _ _ _).symm
  have hlen : 0 < D.length := List.length_pos_iff.mpr h.2.2
  have hs := sem_supp_out hG hC
  have hbranch := PEqualNP.Outside.L_meta_2590_aux.I0Proof.common_branch_of_separation e₀ n D.length g (outW n D)
    (opA D) (opB D) (tag D) (val D q)
    (fun e => val D (sem_two (u e) (v e)))
    (fun e => val D (single (u e))) (fun e => val D (single (v e)))
    (by intro e i hi; rw [val_input D _ i hi, val_input D _ i hi, val_input D _ i hi]; rfl)
    (fun k hk => ⟨(h.1 k hk).1, (h.1 k hk).2.1⟩)
    (fun e k hk => ⟨hval k hk _, hval k hk _, hval k hk _⟩)
    (fun k hk => hval k hk q)
    (by
      intro e k hk ht hau hbv hh
      apply sem_slot_source_of_guards (hsource e) k hk
      · simpa only [mem_supp, Bool.eq_false_iff] using hau
      · simpa only [mem_supp, Bool.eq_false_iff] using hbv
      · simpa only [mem_supp] using hh)
    (by
      intro k hk hkg ht
      constructor
      · obtain ⟨e, he⟩ := hmiss k hk hkg ht false
        exact ⟨e, by simpa only [sb_src_false, mem_supp, Bool.eq_false_iff] using he⟩
      · obtain ⟨e, he⟩ := hmiss k hk hkg ht true
        exact ⟨e, by simpa only [sb_src_true, mem_supp, Bool.eq_false_iff] using he⟩)
    (by unfold outW; omega)
    (by
      intro e
      apply causal_mixed_iff.mpr
      refine ⟨(hC _).mpr (sem_two_edge (hedge e)), ?_, ?_⟩
      · rw [hs]; exact Finset.notMem_empty _
      · rw [hs]; exact Finset.notMem_empty _)
    hqg (Bool.eq_false_iff.mpr fun htrue => hq ((hC q).mp htrue))
  obtain ⟨cut, w1, w2, hchain, h1, h2, hne, hall⟩ := hbranch
  refine ⟨cut, sem_Chain_of_unique_chain hchain, ?_, fun e => causal_mixed_iff.mp (hall e)⟩
  have hs1 := causal_incoming_iff_step.mp h1
  have hs2 := causal_incoming_iff_step.mp h2
  have hpos := sem_step_fanout hs1
  by_contra hnot
  have hone : fanout D cut = 1 := by omega
  exact hne (sem_step_unique hs1 hs2 hone)

end DagTools

namespace DagTools

lemma h9_branch_nonempty {n : ℕ} {D : Dag}
    (hS : Strict n D) (hB0 : Bzero n D = 0) {w : ℕ} (hf : 2 ≤ fanout D w) :
    (supp n D w).Nonempty := by
  by_contra hne
  have hmem : w ∈ (inner n D).filter (fun v => ¬ (supp n D v).Nonempty) :=
    Finset.mem_filter.mpr ⟨sb_mem_inner.mpr (lt_of_fanout_pos hS (by omega)), hne⟩
  have hsum : fanout D w - 1 ≤ ∑ v ∈ (inner n D).filter (fun v => ¬ (supp n D v).Nonempty),
      (fanout D v - 1) :=
    Finset.single_le_sum (f := fun v => fanout D v - 1) (fun _ _ => Nat.zero_le _) hmem
  unfold Bzero surplusOn at hB0
  omega

lemma h9_all_branch_pure {n : ℕ} {D : Dag} {G : Fin n → Fin n → Prop}
    (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    (hBp : Bplus n D = (eligSet n D).card) (hB0 : Bzero n D = 0) :
    ∀ w, 2 ≤ fanout D w → ∃ v : Fin n, supp n D w = {v} ∧ fanout D w = 2 := by
  obtain ⟨b, hb⟩ := sem_exists_pureBranch hG hS hC
  have hc := card_residual hS b hb
  have hres : residualUnits n D b = ∅ := Finset.card_eq_zero.mp (by omega)
  have hreserved : ∀ u : Σ _ : ℕ, ℕ, u ∈ unitsPlus n D → u ∈ reservedUnits n D b := by
    intro u hu
    by_contra hn
    have hm : u ∈ residualUnits n D b := Finset.mem_sdiff.mpr ⟨hu, hn⟩
    rw [hres] at hm
    exact Finset.notMem_empty _ hm
  intro w hf
  have hne := h9_branch_nonempty hS hB0 hf
  have hin : w ∈ inner n D := sb_mem_inner.mpr (lt_of_fanout_pos hS (by omega))
  have hzero : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ unitsPlus n D := by
    apply Finset.mem_filter.mpr
    exact ⟨mem_units.mpr ⟨hin, by change 0 + 1 < fanout D w; omega⟩, hne⟩
  obtain ⟨v, hv, hveq⟩ := Finset.mem_image.mp (hreserved _ hzero)
  have hvw : b v = w := congrArg Sigma.fst hveq
  have hs : supp n D w = {v} := by rw [← hvw]; exact (hb v hv).2
  refine ⟨v, hs, ?_⟩
  by_contra htwo
  have hthree : 3 ≤ fanout D w := by omega
  have hone : (⟨w, 1⟩ : Σ _ : ℕ, ℕ) ∈ unitsPlus n D := by
    apply Finset.mem_filter.mpr
    exact ⟨mem_units.mpr ⟨hin, by change 1 + 1 < fanout D w; omega⟩, hne⟩
  obtain ⟨v', hv', hveq'⟩ := Finset.mem_image.mp (hreserved _ hone)
  have hbad : (0 : ℕ) = 1 := congrArg (fun u : Σ _ : ℕ, ℕ => u.2) hveq'
  omega

end DagTools

namespace FourGroupGeometry

abbrev V := Fin 10

def edges : List (Nat × Nat) :=
  [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),
   (5,7),(7,9),(9,6),(6,8),(8,5)]

def adj (u v : V) : Prop := (u.val,v.val) ∈ edges ∨ (v.val,u.val) ∈ edges

def mask (m : Nat) : Finset V := Finset.univ.filter (fun v => m.testBit v.val)

def witnessMasks : List (List Nat) := [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [73, 18, 0, 40, 18, 34, 72, 144, 274, 546], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [5, 42, 5, 40, 0, 40, 65, 193, 261, 516], [5, 146, 5, 73, 144, 0, 65, 144, 260, 517], [261, 18, 260, 42, 18, 34, 0, 146, 260, 516], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

def witness (v w : V) : Finset V := mask ((witnessMasks.getD v.val []).getD w.val 0)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 1000 in
lemma finite_isolation : ∀ v : V, v ∈ mask 116 → ∀ w : V, w ≠ v →
    (∀ a ∈ witness v w, ∀ b ∈ witness v w, ¬ adj a b) ∧
    w ∈ witness v w ∧
    (∃ u ∈ witness v w, u ∈ mask 116) ∧
    (∃ a ∈ witness v w, adj v a) := by
  unfold adj
  decide +kernel

lemma other_of_card_two {α : Type} [DecidableEq α] {W : Finset α}
    (hc : W.card ≤ 2) {a b : α} (ha : a ∈ W) (hb : b ∈ W) (hab : a ≠ b)
    {c : α} (hcw : c ∈ W) : c = a ∨ c = b := by
  by_contra! hn
  have ht : 2 < W.card := Finset.two_lt_card.mpr
    ⟨a,ha,b,hb,c,hcw,hab,Ne.symm hn.1,Ne.symm hn.2⟩
  omega

lemma isolate_extra_slot {α : Type} [DecidableEq α]
    (W : Finset α) (supp : α → Finset V) (big : α) (v : V)
    (hv : v ∈ mask 116) (hc : W.card ≤ 2) (hbig : big ∈ W)
    (hQ : mask 116 ⊆ supp big) (hmem : ∀ e ∈ W, v ∈ supp e)
    (hexpose : ∀ S : Finset V,
      (∀ a ∈ S, ∀ b ∈ S, ¬ adj a b) →
      (∃ a ∈ S, adj v a) → ∃ e ∈ W, Disjoint (supp e) S) :
    ∃ e ∈ W, e ≠ big ∧ supp e = {v} := by
  have zero_ne : (0 : V) ≠ v := by
    intro h
    subst v
    have hh : (0 : V) ∉ mask 116 := by decide +kernel
    exact hh hv
  have big_hits (w : V) (hne : w ≠ v) : ¬ Disjoint (supp big) (witness v w) := by
    obtain ⟨u,hu,hQ'⟩ := (finite_isolation v hv w hne).2.2.1
    intro hd
    exact Finset.disjoint_left.mp hd (hQ hQ') hu
  obtain ⟨e,he,hdis⟩ := hexpose (witness v 0)
    (finite_isolation v hv 0 zero_ne).1 (finite_isolation v hv 0 zero_ne).2.2.2
  have hne : e ≠ big := by
    intro heq
    subst e
    exact big_hits 0 zero_ne hdis
  refine ⟨e,he,hne,?_⟩
  apply Finset.eq_singleton_iff_unique_mem.mpr
  refine ⟨hmem e he,?_⟩
  intro w hw
  by_contra hnv
  obtain ⟨f,hf,hdf⟩ := hexpose (witness v w)
    (finite_isolation v hv w hnv).1 (finite_isolation v hv w hnv).2.2.2
  have hnf : f ≠ big := by
    intro heq
    subst f
    exact big_hits w hnv hdf
  have hfe : f = e := (other_of_card_two hc hbig he (Ne.symm hne) hf).resolve_left hnf
  subst f
  exact Finset.disjoint_left.mp hdf hw (finite_isolation v hv w hnv).2.1

end FourGroupGeometry

namespace DagTools.FourCase

open PEqualNP.Outside.L_meta_2590_aux.I0Proof.FourGroupGeometry

abbrev V := Fin 10

abbrev Slot := ℕ × Bool

def Q : Finset V := mask 116

def R : Finset V := mask 907

set_option synthInstance.maxSize 5000 in
set_option maxRecDepth 100000 in
lemma graph : sem_Gr adj := by
  unfold sem_Gr adj
  decide +kernel

lemma partition : ∀ v : V, v ∈ Q ∨ v ∈ R := by decide +kernel

lemma disjoint : Disjoint Q R := by decide +kernel

lemma required_cover : ∀ z : V, ∃ u : V, ∃ v : V,
    u ∈ Q ∧ v ∈ R ∧ adj u v ∧ (u = z ∨ v = z) := by
  unfold adj
  decide +kernel

lemma required_avoid : ∀ z : V, ∃ u : V, ∃ v : V,
    u ∈ Q ∧ v ∈ R ∧ adj u v ∧ u ≠ z ∧ v ≠ z := by
  unfold adj
  decide +kernel

lemma code_budget {D : Dag} (h : StrictLive 10 D) (hC : sem_Comp 10 adj D)
    (hall : eligSet 10 D = Finset.univ) (hB : Bplus 10 D = 10) (v : V) :
    (sem_W 10 D v).card + (merges 10 D (carrierT 10 D {v})).card ≤ 2 := by
  obtain ⟨b, hb⟩ := sem_exists_pureBranch graph h.1 hC
  have hs := surplus_carrierT_le h.1 b hb {v}
  simp only [hall, Finset.inter_univ, Finset.card_singleton,
    Finset.card_univ, Fintype.card_fin, hB] at hs
  have hf := sem_flow1 graph h hC v
  omega

lemma pure_extra {D : Dag} (h : Strict 10 D) (hC : sem_Comp 10 adj D)
    (hW : ∀ v : V, (sem_W 10 D v).card ≤ 2) (big : Slot)
    (hQ : ∀ v ∈ Q, big ∈ sem_W 10 D v) :
    ∀ v ∈ Q, ∃ e ∈ sem_W 10 D v, e ≠ big ∧ supp 10 D (src D e) = {v} := by
  intro v hv
  apply isolate_extra_slot (sem_W 10 D v) (fun e => supp 10 D (src D e)) big v
    hv (hW v) (hQ v hv)
  · intro u hu
    exact (sem_mem_W.mp (hQ u hu)).2.1
  · intro e he
    exact (sem_mem_W.mp he).2.1
  · intro S hind hnb
    obtain ⟨j, s, hj, _, hx, hn, hd⟩ := sem_exposure graph h hC S hind v hnb
    exact ⟨(j,s), sem_mem_W.mpr ⟨hj,hx,hn⟩,hd⟩

lemma W_two {D : Dag} (big : Slot) (matchSlot : V → Slot)
    (hbudget : ∀ v : V, (sem_W 10 D v).card +
      (merges 10 D (carrierT 10 D {v})).card ≤ 2)
    (hQ : ∀ v ∈ Q, big ∈ sem_W 10 D v)
    (hextra : ∀ v ∈ Q, ∃ e ∈ sem_W 10 D v,
      e ≠ big ∧ supp 10 D (src D e) = {v})
    (hR : ∀ v ∈ R, sem_bar big ∈ sem_W 10 D v ∧ matchSlot v ∈ sem_W 10 D v)
    (hdiff : ∀ v ∈ R, (matchSlot v).1 ≠ big.1) :
    ∀ v : V, (sem_W 10 D v).card = 2 ∧ merges 10 D (carrierT 10 D {v}) = ∅ := by
  intro v
  have hlo : 2 ≤ (sem_W 10 D v).card := by
    rcases partition v with hv | hv
    · obtain ⟨e, he, hne, _⟩ := hextra v hv
      exact Nat.succ_le_of_lt (Finset.one_lt_card.mpr ⟨big, hQ v hv, e, he, Ne.symm hne⟩)
    · have hne : sem_bar big ≠ matchSlot v := by
        intro he
        exact hdiff v hv (congrArg Prod.fst he).symm
      exact Nat.succ_le_of_lt (Finset.one_lt_card.mpr
        ⟨sem_bar big, (hR v hv).1, matchSlot v, (hR v hv).2, hne⟩)
  have hb := hbudget v
  exact ⟨by omega, Finset.card_eq_zero.mp (by omega)⟩

lemma and_supp_empty {D : Dag} (h : Strict 10 D)
    (hmerge : ∀ v : V, merges 10 D (carrierT 10 D {v}) = ∅)
    (k : ℕ) (hk : k < D.length) (ht : tag D k = true) : supp 10 D (10+k) = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro v hv
  have hab := hv
  rw [sem_supp_and h hk ht, Finset.mem_inter] at hab
  have hm : k ∈ merges 10 D (carrierT 10 D {v}) := by
    rw [merges, Finset.mem_filter, Finset.mem_range]
    exact ⟨hk, sem_mem_carrier1.mpr hv,
      sem_mem_carrier1.mpr hab.1, sem_mem_carrier1.mpr hab.2⟩
  rw [hmerge v] at hm
  exact Finset.notMem_empty _ hm

lemma matching_support {D : Dag} (h : Strict 10 D) (big : Slot) (matchSlot : V → Slot)
    (hW : ∀ v : V, (sem_W 10 D v).card ≤ 2)
    (hQ : ∀ v ∈ Q, big ∈ sem_W 10 D v)
    (hextra : ∀ v ∈ Q, ∃ e ∈ sem_W 10 D v,
      e ≠ big ∧ supp 10 D (src D e) = {v})
    (hR : ∀ v ∈ R, sem_bar big ∈ sem_W 10 D v ∧ matchSlot v ∈ sem_W 10 D v)
    (hdiff : ∀ v ∈ R, (matchSlot v).1 ≠ big.1)
    (hinj : ∀ u ∈ R, ∀ v ∈ R, matchSlot u = matchSlot v → u = v)
    (hempty : ∀ k < D.length, tag D k = true → supp 10 D (10+k) = ∅) :
    ∀ v ∈ R, supp 10 D (src D (matchSlot v)) = {v} := by
  intro v hv
  apply Finset.eq_singleton_iff_unique_mem.mpr
  refine ⟨(sem_mem_W.mp (hR v hv).2).2.1, ?_⟩
  intro u hu
  have hslot := (hR v hv).2
  have hk := (sem_mem_W.mp hslot).1
  have ht := sem_W_and h hslot
  have huW : matchSlot v ∈ sem_W 10 D u := by
    apply sem_mem_W.mpr
    refine ⟨hk, hu, ?_⟩
    rw [hempty _ hk ht]
    exact Finset.notMem_empty _
  rcases partition u with huQ | huR
  · obtain ⟨e, he, hne, hpure⟩ := hextra u huQ
    have hchoices := other_of_card_two (hW u) (hQ u huQ) he (Ne.symm hne) huW
    rcases hchoices with hb | heq
    · exact False.elim (hdiff v hv (by simpa only [sem_bar] using congrArg Prod.fst hb))
    · have hvsrc := (sem_mem_W.mp (hR v hv).2).2.1
      rw [heq, hpure, Finset.mem_singleton] at hvsrc
      exact hvsrc.symm
  · have hne : sem_bar big ≠ matchSlot u := by
      intro he
      exact hdiff u huR (congrArg Prod.fst he).symm
    rcases other_of_card_two (hW u) (hR u huR).1 (hR u huR).2 hne huW with hb | hm
    · exact False.elim (hdiff v hv (by simpa only [sem_bar] using congrArg Prod.fst hb))
    · exact (hinj v hv u huR hm).symm

lemma nonbig_side_pure {D : Dag} (big : Slot) (matchSlot : V → Slot)
    (hW : ∀ v : V, (sem_W 10 D v).card ≤ 2)
    (hQ : ∀ v ∈ Q, big ∈ sem_W 10 D v)
    (hextra : ∀ v ∈ Q, ∃ e ∈ sem_W 10 D v,
      e ≠ big ∧ supp 10 D (src D e) = {v})
    (hR : ∀ v ∈ R, sem_bar big ∈ sem_W 10 D v ∧ matchSlot v ∈ sem_W 10 D v)
    (hdiff : ∀ v ∈ R, (matchSlot v).1 ≠ big.1)
    (hpure : ∀ v ∈ R, supp 10 D (src D (matchSlot v)) = {v})
    (hempty : ∀ k < D.length, tag D k = true → supp 10 D (10+k) = ∅)
    (k : ℕ) (hk : k < D.length) (hkg : k ≠ big.1) (ht : tag D k = true)
    (s : Bool) : ∃ v : V, supp 10 D (src D (k,s)) ⊆ {v} := by
  by_cases hn : (supp 10 D (src D (k,s))).Nonempty
  · obtain ⟨v,hv⟩ := hn
    have hvW : (k,s) ∈ sem_W 10 D v := sem_mem_W.mpr
      ⟨hk,hv,by rw [hempty k hk ht]; exact Finset.notMem_empty _⟩
    rcases partition v with hvQ | hvR
    · obtain ⟨e,he,hne,hpure⟩ := hextra v hvQ
      rcases other_of_card_two (hW v) (hQ v hvQ) he (Ne.symm hne) hvW with hb | heq
      · exact False.elim (hkg (by simpa only [sem_bar] using congrArg Prod.fst hb))
      · exact ⟨v, by rw [heq,hpure]⟩
    · have hne : sem_bar big ≠ matchSlot v := by
        intro he
        exact hdiff v hvR (congrArg Prod.fst he).symm
      rcases other_of_card_two (hW v) (hR v hvR).1 (hR v hvR).2 hne hvW with hb | heq
      · exact False.elim (hkg (by simpa only [sem_bar] using congrArg Prod.fst hb))
      · exact ⟨v, by rw [heq,hpure v hvR]⟩
  · exact ⟨0, by rw [Finset.not_nonempty_iff_eq_empty.mp hn]; exact Finset.empty_subset _⟩

lemma opposite_source {D : Dag} (big : Slot) (matchSlot : V → Slot)
    (hW : ∀ v : V, (sem_W 10 D v).card ≤ 2)
    (hR : ∀ v ∈ R, sem_bar big ∈ sem_W 10 D v ∧ matchSlot v ∈ sem_W 10 D v)
    (hdiff : ∀ v ∈ R, (matchSlot v).1 ≠ big.1)
    (hopp : ∀ v ∈ R, ∃ w ∈ R, sem_bar (matchSlot v) = matchSlot w)
    (hpure : ∀ v ∈ R, supp 10 D (src D (matchSlot v)) = {v})
    (u v : V) (hu : u ∈ Q) (hv : v ∈ R) (e : Slot)
    (he : e ∈ sem_W 10 D u) (hbe : sem_bar e ∈ sem_W 10 D v) : e.1 = big.1 := by
  have hne : sem_bar big ≠ matchSlot v := by
    intro h
    exact hdiff v hv (congrArg Prod.fst h).symm
  rcases other_of_card_two (hW v) (hR v hv).1 (hR v hv).2 hne hbe with hb | hm
  · simpa only [sem_bar] using congrArg Prod.fst hb
  · have heq : e = sem_bar (matchSlot v) := by
      simpa only [sem_bar_bar] using congrArg sem_bar hm
    obtain ⟨w,hw,hbw⟩ := hopp v hv
    have hu' := (sem_mem_W.mp he).2.1
    rw [heq,hbw,hpure w hw,Finset.mem_singleton] at hu'
    exact False.elim (Finset.disjoint_left.mp disjoint hu (by simpa only [hu'] using hw))

lemma branch_nonempty {D : Dag} (h : Strict 10 D) (hB : Bzero 10 D = 0)
    (w : ℕ) (hw : 2 ≤ fanout D w) : (supp 10 D w).Nonempty := by
  by_contra hn
  have hm : w ∈ (inner 10 D).filter (fun w => ¬ (supp 10 D w).Nonempty) :=
    Finset.mem_filter.mpr ⟨sb_mem_inner.mpr (lt_of_fanout_pos h (by omega)),hn⟩
  have hs := Finset.single_le_sum (f := fun w => fanout D w - 1)
    (fun _ _ => Nat.zero_le _) hm
  unfold Bzero surplusOn at hB
  omega

abbrev E := {p : V × V // p.1 ∈ Q ∧ p.2 ∈ R ∧ adj p.1 p.2}

lemma abstract_four_impossible {D : Dag} (h : StrictLive 10 D) (hC : sem_Comp 10 adj D)
    (hall : eligSet 10 D = Finset.univ) (hB : Bplus 10 D = 10) (hB0 : Bzero 10 D = 0)
    (big : Slot) (matchSlot : V → Slot)
    (hQ : ∀ v ∈ Q, big ∈ sem_W 10 D v)
    (hR : ∀ v ∈ R, sem_bar big ∈ sem_W 10 D v ∧ matchSlot v ∈ sem_W 10 D v)
    (hdiff : ∀ v ∈ R, (matchSlot v).1 ≠ big.1)
    (hinj : ∀ u ∈ R, ∀ v ∈ R, matchSlot u = matchSlot v → u = v)
    (hopp : ∀ v ∈ R, ∃ w ∈ R, sem_bar (matchSlot v) = matchSlot w) : False := by
  have hb := code_budget h hC hall hB
  have hW (v : V) : (sem_W 10 D v).card ≤ 2 := by have := hb v; omega
  have hextra := pure_extra h.1 hC hW big hQ
  have htwo := W_two big matchSlot hb hQ hextra hR hdiff
  have hempty := and_supp_empty h.1 (fun v => (htwo v).2)
  have hpure := matching_support h.1 big matchSlot hW hQ hextra hR hdiff hinj hempty
  let e₀ : E := ⟨(2,1),by unfold adj; decide +kernel⟩
  have hsource (e : E) (s : Slot) (hs : s ∈ sem_W 10 D e.val.1)
      (hbs : sem_bar s ∈ sem_W 10 D e.val.2) : s.1 = big.1 :=
    opposite_source big matchSlot hW hR hdiff hopp hpure
      e.val.1 e.val.2 e.property.1 e.property.2.1 s hs hbs
  have hcover (v : V) : ∃ e : E, e.val.1 = v ∨ e.val.2 = v := by
    obtain ⟨u,w,hu,hw,he,hv⟩ := required_cover v
    exact ⟨⟨(u,w),hu,hw,he⟩,hv⟩
  have hmiss (k : ℕ) (hk : k < D.length) (hkg : k ≠ big.1) (ht : tag D k = true)
      (s : Bool) : ∃ e : E, e.val.1 ∉ supp 10 D (src D (k,s)) ∧
        e.val.2 ∉ supp 10 D (src D (k,s)) := by
    obtain ⟨z,hz⟩ := nonbig_side_pure big matchSlot hW hQ hextra hR hdiff hpure hempty k hk hkg ht s
    obtain ⟨u,v,hu,hv,he,huz,hvz⟩ := required_avoid z
    exact ⟨⟨(u,v),hu,hv,he⟩,fun h => huz (Finset.mem_singleton.mp (hz h)),
      fun h => hvz (Finset.mem_singleton.mp (hz h))⟩
  have hq : ¬ sem_Edge adj (sem_two (2 : V) 0) := by
    unfold sem_Edge adj
    decide +kernel
  have h2 := hQ (2 : V) (by decide +kernel)
  have h0 := (hR (0 : V) (by decide +kernel)).1
  have hleft : val D (sem_two (2 : V) 0) (src D big) = true :=
    sem_val_of_supp h.1 (sem_mem_W.mp h2).2.1 (by simp [sem_two])
  have hright : val D (sem_two (2 : V) 0) (src D (sem_bar big)) = true :=
    sem_val_of_supp h.1 (sem_mem_W.mp h0).2.1 (by simp [sem_two])
  have hqg : val D (sem_two (2 : V) 0) (10 + big.1) = true := by
    rw [val_gate h.1 _ _ (sem_mem_W.mp h2).1, sem_W_and h.1 h2, gop_true]
    cases hs : big.2
    · simp only [src, sem_bar, hs, Bool.not_false, Bool.false_eq_true, ite_false, ite_true] at hleft hright
      simp [hleft,hright]
    · simp only [src, sem_bar, hs, Bool.not_true, Bool.false_eq_true, ite_false, ite_true] at hleft hright
      simp [hleft,hright]
  exact sem_slot_family_obstruction_cover e₀ graph h hC big.1
    (fun e : E => e.val.1) (fun e : E => e.val.2) (fun e => e.property.2.2)
    hcover hsource (branch_nonempty h.1 hB0) hmiss (sem_two (2 : V) 0) hq hqg

def matching (a b c : Slot) (v : V) : Slot :=
  if v = 0 then a else if v = 1 then sem_bar a else
  if v = 3 then b else if v = 8 then sem_bar b else
  if v = 7 then c else sem_bar c

lemma mem_R : ∀ v : V, v ∈ R ↔
    v = 0 ∨ v = 1 ∨ v = 3 ∨ v = 8 ∨ v = 7 ∨ v = 9 := by decide +kernel

lemma matching_opposite (a b c : Slot) :
    ∀ v ∈ R, ∃ w ∈ R, sem_bar (matching a b c v) = matching a b c w := by
  intro v hv
  rw [mem_R] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1,by decide +kernel,by simp [matching]⟩
  · exact ⟨0,by decide +kernel,by simp [matching,sem_bar_bar]⟩
  · exact ⟨8,by decide +kernel,by simp [matching]⟩
  · exact ⟨3,by decide +kernel,by simp [matching,sem_bar_bar]⟩
  · exact ⟨9,by decide +kernel,by simp [matching]⟩
  · exact ⟨7,by decide +kernel,by simp [matching,sem_bar_bar]⟩

lemma matching_injective (a b c : Slot)
    (hab : a.1 ≠ b.1) (hac : a.1 ≠ c.1) (hbc : b.1 ≠ c.1) :
    ∀ u ∈ R, ∀ v ∈ R, matching a b c u = matching a b c v → u = v := by
  intro u hu v hv he
  rw [mem_R] at hu hv
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [matching] at he
  all_goals try rfl
  all_goals try {
    have hf := congrArg Prod.fst he
    try simp only [sem_bar] at hf
    omega }
  all_goals first
    | exact False.elim (sem_bar_ne a he)
    | exact False.elim (sem_bar_ne a he.symm)
    | exact False.elim (sem_bar_ne b he)
    | exact False.elim (sem_bar_ne b he.symm)
    | exact False.elim (sem_bar_ne c he)
    | exact False.elim (sem_bar_ne c he.symm)

lemma canonical_four_impossible {D : Dag} (h : StrictLive 10 D) (hC : sem_Comp 10 adj D)
    (hall : eligSet 10 D = Finset.univ) (hB : Bplus 10 D = 10) (hB0 : Bzero 10 D = 0)
    (big a b c : Slot)
    (hab : a.1 ≠ b.1) (hac : a.1 ≠ c.1) (hbc : b.1 ≠ c.1)
    (hag : a.1 ≠ big.1) (hbg : b.1 ≠ big.1) (hcg : c.1 ≠ big.1)
    (hQ : ∀ v ∈ Q, big ∈ sem_W 10 D v)
    (hR : ∀ v ∈ R, sem_bar big ∈ sem_W 10 D v)
    (ha0 : a ∈ sem_W 10 D (0 : V)) (ha1 : sem_bar a ∈ sem_W 10 D (1 : V))
    (hb3 : b ∈ sem_W 10 D (3 : V)) (hb8 : sem_bar b ∈ sem_W 10 D (8 : V))
    (hc7 : c ∈ sem_W 10 D (7 : V)) (hc9 : sem_bar c ∈ sem_W 10 D (9 : V)) : False := by
  apply abstract_four_impossible h hC hall hB hB0 big (matching a b c) hQ
  · intro v hv
    refine ⟨hR v hv,?_⟩
    rw [mem_R] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [matching]
  · intro v hv
    rw [mem_R] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [matching,sem_bar]
  · exact matching_injective a b c hab hac hbc
  · exact matching_opposite a b c

end DagTools.FourCase

namespace FiveGroupGeometry

abbrev V := Fin 10

abbrev Slot := ℕ × Bool

def mask (m : ℕ) : Finset V := Finset.univ.filter (fun v => m.testBit v.val)

def inner : Finset V := mask 972

def sides (i : Fin 5) (s : Bool) : Finset V :=
  mask (if s then ([50,68,520,384,772] : List ℕ).getD i.val 0
    else ([1,2,16,32,200] : List ℕ).getD i.val 0)

def bar (e : Slot) : Slot := (e.1, !e.2)

def flip (s : Bool) (e : Slot) : Slot := if s then bar e else e

def known (P : Fin 5 → Slot) (v : V) : Finset Slot :=
  ((Finset.univ ×ˢ Finset.univ).filter (fun p : Fin 5 × Bool => v ∈ sides p.1 p.2)).image
    (fun p => flip p.2 (P p.1))

lemma flip_fst (s : Bool) (e : Slot) : (flip s e).1 = e.1 := by cases s <;> rfl

lemma flip_bar (s : Bool) (e : Slot) : bar (flip s e) = flip (!s) e := by
  rcases e with ⟨k,b⟩
  cases s <;> cases b <;> rfl

lemma flip_injective (e : Slot) : Function.Injective (fun s => flip s e) := by
  rcases e with ⟨k,b⟩
  intro s t h
  cases s <;> cases t <;> cases b <;> simp_all [flip,bar]

lemma flip_exists (p e : Slot) (h : p.1 = e.1) : ∃ s, flip s p = e := by
  rcases p with ⟨k,b⟩
  rcases e with ⟨l,c⟩
  dsimp at h
  subst l
  cases b <;> cases c
  · exact ⟨false,rfl⟩
  · exact ⟨true,rfl⟩
  · exact ⟨true,rfl⟩
  · exact ⟨false,rfl⟩

def leafCover (v : V) : Finset V :=
  mask (if v = 1 then 68 else if v = 4 then 520 else if v = 5 then 384 else 0)

lemma member_known {P : Fin 5 → Slot} {v : V} {e : Slot} :
    e ∈ known P v ↔ ∃ i : Fin 5, ∃ s : Bool, v ∈ sides i s ∧ flip s (P i) = e := by
  simp only [known, Finset.mem_image, Finset.mem_filter, Finset.mem_product,
    Finset.mem_univ, true_and, Prod.exists]

set_option maxHeartbeats 0 in
lemma clean_side_size : ∀ i : Fin 5, i ≠ 4 → ∀ s : Bool,
    (sides i s ∩ inner).card ≤ 2 := by decide +kernel

set_option maxHeartbeats 0 in
lemma leaf_cover_geometry : ∀ v : V, (v = 1 ∨ v = 4 ∨ v = 5) →
    (leafCover v).card ≤ 2 ∧ ∀ i : Fin 5, ∀ s : Bool,
      v ∈ sides i s → sides i (!s) ∩ inner ⊆ leafCover v := by decide +kernel

set_option maxHeartbeats 0 in
lemma center_other_empty : sides 0 true ∩ inner = ∅ := by decide +kernel

lemma support_at_slot (P : Fin 5 → Slot) (hP : Function.Injective (fun i => (P i).1))
    (supp : Slot → Finset V) (e : Slot)
    (htype : ∀ v ∈ inner, v ∈ supp e → e ∈ known P v)
    (i : Fin 5) (s : Bool) (hi : flip s (P i) = e) :
    supp e ∩ inner ⊆ sides i s ∩ inner := by
  intro v hv
  obtain ⟨hs, hn⟩ := Finset.mem_inter.mp hv
  obtain ⟨j,t,hj,he⟩ := member_known.mp (htype v hn hs)
  have hf := congrArg Prod.fst (he.trans hi.symm)
  simp only [flip_fst] at hf
  have hji : j = i := hP hf
  subst j
  have hts : t = s := flip_injective (P i) (he.trans hi.symm)
  exact Finset.mem_inter.mpr ⟨hts ▸ hj, hn⟩

lemma support_size (P : Fin 5 → Slot) (hP : Function.Injective (fun i => (P i).1))
    (supp : Slot → Finset V) (e : Slot)
    (htype : ∀ v ∈ inner, v ∈ supp e → e ∈ known P v)
    (hne : e.1 ≠ (P 4).1) : (supp e ∩ inner).card ≤ 2 := by
  classical
  by_cases hi : ∃ i, (P i).1 = e.1
  · obtain ⟨i,hi⟩ := hi
    obtain ⟨s,hs⟩ := flip_exists (P i) e hi
    have hni : i ≠ 4 := by intro h; subst i; exact hne hi.symm
    exact (Finset.card_le_card (support_at_slot P hP supp e htype i s hs)).trans
      (clean_side_size i hni s)
  · have he : supp e ∩ inner = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      obtain ⟨hs,hn⟩ := Finset.mem_inter.mp hv
      obtain ⟨j,t,_,hj⟩ := member_known.mp (htype v hn hs)
      have hf := congrArg Prod.fst hj
      rw [flip_fst] at hf
      exact hi ⟨j,hf⟩
    simp [he]

lemma leaf_exit_cover (P : Fin 5 → Slot) (hP : Function.Injective (fun i => (P i).1))
    (supp : Slot → Finset V) (v : V) (hv : v = 1 ∨ v = 4 ∨ v = 5)
    (e : Slot) (he : e ∈ known P v)
    (htype : ∀ w ∈ inner, w ∈ supp (bar e) → bar e ∈ known P w) :
    supp (bar e) ∩ inner ⊆ leafCover v := by
  obtain ⟨i,s,hi,hie⟩ := member_known.mp he
  have hbar : flip (!s) (P i) = bar e := by rw [← flip_bar, hie]
  exact (support_at_slot P hP supp (bar e) htype i (!s) hbar).trans
    ((leaf_cover_geometry v hv).2 i s hi)

lemma at_most_two_cover {α : Type} [DecidableEq α] (W : Finset α)
    (a : α) (ha : a ∈ W) (hc : W.card ≤ 2) :
    ∃ b ∈ W, ∀ e ∈ W, e = a ∨ e = b := by
  classical
  by_cases hb : ∃ b ∈ W, b ≠ a
  · obtain ⟨b,hb,hba⟩ := hb
    refine ⟨b,hb,?_⟩
    intro e he
    by_contra! hne
    have ht : 2 < W.card := Finset.two_lt_card.mpr
      ⟨a,ha,b,hb,e,he,Ne.symm hba,Ne.symm hne.1,Ne.symm hne.2⟩
    omega
  · exact ⟨a,ha,fun e he => Or.inl (by by_contra h; exact hb ⟨e,he,h⟩)⟩

lemma center_exit_cover (P : Fin 5 → Slot) (hP : Function.Injective (fun i => (P i).1))
    (supp : Slot → Finset V) (W : Finset Slot) (hW : W.card ≤ 2)
    (hknown : P 0 ∈ W)
    (htype : ∀ e ∈ W, ∀ w ∈ inner, w ∈ supp (bar e) → bar e ∈ known P w)
    (cut : ℕ) (hcut : 10 + (P 4).1 ≤ cut) :
    ∃ T : Finset V, T.card ≤ 2 ∧
      ∀ e ∈ W, cut < 10 + e.1 → supp (bar e) ∩ inner ⊆ T := by
  classical
  have hzero : supp (bar (P 0)) ∩ inner = ∅ := by
    have hh := support_at_slot P hP supp (bar (P 0)) (htype _ hknown) 0 true rfl
    rw [center_other_empty] at hh
    exact Finset.subset_empty.mp hh
  obtain ⟨f,hf,hcover⟩ := at_most_two_cover W (P 0) hknown hW
  by_cases hafter : cut < 10 + f.1
  · refine ⟨supp (bar f) ∩ inner,?_,?_⟩
    · apply support_size P hP supp (bar f) (htype f hf)
      change f.1 ≠ (P 4).1
      omega
    · intro e he hpost
      rcases hcover e he with rfl | rfl
      · rw [hzero]; exact Finset.empty_subset _
      · exact Finset.Subset.refl _
  · refine ⟨∅,by simp,?_⟩
    intro e he hpost
    rcases hcover e he with rfl | rfl
    · rw [hzero]
    · exact (hafter hpost).elim

lemma matching_edge_missed (T : Finset V) (hT : T.card ≤ 2) :
    ((2 : V) ∉ T ∧ (3 : V) ∉ T) ∨
    ((6 : V) ∉ T ∧ (8 : V) ∉ T) ∨
    ((7 : V) ∉ T ∧ (9 : V) ∉ T) := by
  classical
  by_contra! hn
  obtain ⟨h1,h2,h3⟩ := hn
  have h1' : (2 : V) ∈ T ∨ (3 : V) ∈ T := by
    by_cases h : (2 : V) ∈ T
    · exact Or.inl h
    · exact Or.inr (h1 h)
  have h2' : (6 : V) ∈ T ∨ (8 : V) ∈ T := by
    by_cases h : (6 : V) ∈ T
    · exact Or.inl h
    · exact Or.inr (h2 h)
  have h3' : (7 : V) ∈ T ∨ (9 : V) ∈ T := by
    by_cases h : (7 : V) ∈ T
    · exact Or.inl h
    · exact Or.inr (h3 h)
  rcases h1' with h1 | h1 <;> rcases h2' with h2 | h2 <;> rcases h3' with h3 | h3
  all_goals
    have ht : 2 < T.card := Finset.two_lt_card.mpr
      ⟨_,h1,_,h2,_,h3,by decide,by decide,by decide⟩
    omega

end FiveGroupGeometry

namespace DagTools.FiveCase

open PEqualNP.Outside.L_meta_2590_aux.I0Proof.FiveGroupGeometry (sides known flip bar leafCover member_known)

abbrev V := Fin 10

abbrev Slot := ℕ × Bool

abbrev G := PEqualNP.Outside.L_meta_2590_aux.I0Proof.FourGroupGeometry.adj

abbrev I := PEqualNP.Outside.L_meta_2590_aux.I0Proof.FiveGroupGeometry.inner

def U (i : Fin 3) : V := ![2,6,7] i

def Vv (i : Fin 3) : V := ![3,8,9] i

lemma matching_edges : ∀ i : Fin 3, G (U i) (Vv i) := by
  unfold G PEqualNP.Outside.L_meta_2590_aux.I0Proof.FourGroupGeometry.adj
  decide +kernel

lemma matching_inner : ∀ i : Fin 3, U i ∈ I ∧ Vv i ∈ I := by decide +kernel

lemma matching_cover : ∀ v ∈ I, ∃ i : Fin 3, U i = v ∨ Vv i = v := by decide +kernel

lemma inner_nonzero : ∀ v ∈ I, v ≠ (0 : V) := by decide +kernel

lemma outside_inner : ∀ v : V, v ∉ I → v = 0 ∨ v = 1 ∨ v = 4 ∨ v = 5 := by
  decide +kernel

lemma raw_known_card : ∀ v : V, v ≠ 0 →
    (((Finset.univ ×ˢ Finset.univ).filter
      (fun p : Fin 5 × Bool => v ∈ sides p.1 p.2))).card = 2 := by decide +kernel

lemma opposite_inner_only : ∀ u ∈ I, ∀ v ∈ I, ∀ i : Fin 5, ∀ s : Bool,
    u ∈ sides i s → v ∈ sides i (!s) → i = 4 := by decide +kernel

lemma known_card (P : Fin 5 → Slot) (hP : Function.Injective (fun i => (P i).1))
    (v : V) (hv : v ≠ 0) : (known P v).card = 2 := by
  have hinj : Function.Injective (fun p : Fin 5 × Bool => flip p.2 (P p.1)) := by
    rintro ⟨i,s⟩ ⟨j,t⟩ he
    have hf := congrArg Prod.fst he
    simp only [PEqualNP.Outside.L_meta_2590_aux.I0Proof.FiveGroupGeometry.flip_fst] at hf
    have hij := hP hf
    subst j
    have hst : s = t := PEqualNP.Outside.L_meta_2590_aux.I0Proof.FiveGroupGeometry.flip_injective (P i) he
    subst t
    rfl
  rw [known, Finset.card_image_of_injOn (fun _ _ _ _ he => hinj he)]
  exact raw_known_card v hv

lemma known_subset {D : Dag} (P : Fin 5 → Slot)
    (hslots : ∀ i : Fin 5, ∀ s : Bool, ∀ v ∈ sides i s, flip s (P i) ∈ sem_W 10 D v)
    (v : V) : known P v ⊆ sem_W 10 D v := by
  intro e he
  obtain ⟨i,s,hv,rfl⟩ := member_known.mp he
  exact hslots i s v hv

lemma known_eq_W {D : Dag} (P : Fin 5 → Slot)
    (hP : Function.Injective (fun i => (P i).1))
    (hW : ∀ v : V, (sem_W 10 D v).card ≤ 2)
    (hslots : ∀ i : Fin 5, ∀ s : Bool, ∀ v ∈ sides i s, flip s (P i) ∈ sem_W 10 D v)
    (v : V) (hv : v ≠ 0) : sem_W 10 D v = known P v := by
  symm
  apply Finset.eq_of_subset_of_card_le (known_subset P hslots v)
  rw [known_card P hP v hv]
  exact hW v

lemma nonzero_and_absent {D : Dag} (h : Strict 10 D)
    (hM : ∀ v : V, v ≠ 0 → merges 10 D (carrierT 10 D {v}) = ∅)
    (k : ℕ) (hk : k < D.length) (ht : tag D k = true) (v : V) (hv : v ≠ 0) :
    v ∉ supp 10 D (10+k) := by
  intro hm
  have hab := hm
  rw [sem_supp_and h hk ht, Finset.mem_inter] at hab
  have hmer : k ∈ merges 10 D (carrierT 10 D {v}) := by
    rw [merges, Finset.mem_filter, Finset.mem_range]
    exact ⟨hk,sem_mem_carrier1.mpr hm,
      sem_mem_carrier1.mpr hab.1,sem_mem_carrier1.mpr hab.2⟩
  rw [hM v hv] at hmer
  exact Finset.notMem_empty _ hmer

lemma and_input_typed {D : Dag} (h : Strict 10 D) (P : Fin 5 → Slot)
    (hknown : ∀ v : V, v ≠ 0 → sem_W 10 D v = known P v)
    (hM : ∀ v : V, v ≠ 0 → merges 10 D (carrierT 10 D {v}) = ∅)
    (e : Slot) (he : e.1 < D.length) (ht : tag D e.1 = true) :
    ∀ v ∈ I, v ∈ supp 10 D (src D e) → e ∈ known P v := by
  intro v hv hs
  rw [← hknown v (inner_nonzero v hv)]
  exact sem_mem_W.mpr ⟨he,hs,nonzero_and_absent h hM e.1 he ht v (inner_nonzero v hv)⟩

lemma inner_opposite_source {D : Dag} (P : Fin 5 → Slot)
    (hP : Function.Injective (fun i => (P i).1))
    (hknown : ∀ v : V, v ≠ 0 → sem_W 10 D v = known P v)
    (u v : V) (hu : u ∈ I) (hv : v ∈ I) (e : Slot)
    (he : e ∈ sem_W 10 D u) (hbe : sem_bar e ∈ sem_W 10 D v) : e.1 = (P 4).1 := by
  rw [hknown u (inner_nonzero u hu)] at he
  rw [hknown v (inner_nonzero v hv)] at hbe
  obtain ⟨i,s,his,hie⟩ := member_known.mp he
  obtain ⟨j,t,hjt,hje⟩ := member_known.mp hbe
  have hf : (P j).1 = (P i).1 := by
    rw [← PEqualNP.Outside.L_meta_2590_aux.I0Proof.FiveGroupGeometry.flip_fst t, hje]
    change e.1 = (P i).1
    rw [← hie,PEqualNP.Outside.L_meta_2590_aux.I0Proof.FiveGroupGeometry.flip_fst]
  have hji := hP hf
  subst j
  have hts : t = !s := PEqualNP.Outside.L_meta_2590_aux.I0Proof.FiveGroupGeometry.flip_injective (P i) (by
    change flip t (P i) = flip (!s) (P i)
    rw [← PEqualNP.Outside.L_meta_2590_aux.I0Proof.FiveGroupGeometry.flip_bar,hie]
    exact hje)
  have hi : i = 4 := opposite_inner_only u hu v hv i s his (by simpa only [hts] using hjt)
  rw [← hie,PEqualNP.Outside.L_meta_2590_aux.I0Proof.FiveGroupGeometry.flip_fst,hi]

lemma missed_of_small (T : Finset V) (hT : (T ∩ I).card ≤ 2) :
    ∃ i : Fin 3, U i ∉ T ∧ Vv i ∉ T := by
  rcases PEqualNP.Outside.L_meta_2590_aux.I0Proof.FiveGroupGeometry.matching_edge_missed (T ∩ I) hT with h | h | h
  · refine ⟨0,?_,?_⟩
    · intro hm; exact h.1 (Finset.mem_inter.mpr ⟨hm,by decide +kernel⟩)
    · intro hm; exact h.2 (Finset.mem_inter.mpr ⟨hm,by decide +kernel⟩)
  · refine ⟨1,?_,?_⟩
    · intro hm; exact h.1 (Finset.mem_inter.mpr ⟨hm,by decide +kernel⟩)
    · intro hm; exact h.2 (Finset.mem_inter.mpr ⟨hm,by decide +kernel⟩)
  · refine ⟨2,?_,?_⟩
    · intro hm; exact h.1 (Finset.mem_inter.mpr ⟨hm,by decide +kernel⟩)
    · intro hm; exact h.2 (Finset.mem_inter.mpr ⟨hm,by decide +kernel⟩)

lemma exit_cover {D : Dag} (h : Strict 10 D) (P : Fin 5 → Slot)
    (hP : Function.Injective (fun i => (P i).1))
    (hW : ∀ v : V, (sem_W 10 D v).card ≤ 2)
    (hknown : ∀ v : V, v ≠ 0 → sem_W 10 D v = known P v)
    (hM : ∀ v : V, v ≠ 0 → merges 10 D (carrierT 10 D {v}) = ∅)
    (hcenter : P 0 ∈ sem_W 10 D (0 : V))
    (cut : ℕ) (hafter : 10 + (P 4).1 ≤ cut)
    (c : V) (hc : c ∉ I) :
    ∃ T : Finset V, T.card ≤ 2 ∧ ∀ e ∈ sem_W 10 D c,
      cut < 10 + e.1 → supp 10 D (src D (sem_bar e)) ∩ I ⊆ T := by
  have htype (v : V) (e : Slot) (he : e ∈ sem_W 10 D v) :
      ∀ w ∈ I, w ∈ supp 10 D (src D (bar e)) → bar e ∈ known P w := by
    have ht : tag D e.1 = true := sem_W_and h he
    exact and_input_typed h P hknown hM (bar e) (sem_mem_W.mp he).1 ht
  by_cases hc0 : c = 0
  · subst c
    exact PEqualNP.Outside.L_meta_2590_aux.I0Proof.FiveGroupGeometry.center_exit_cover P hP (fun e => supp 10 D (src D e))
      (sem_W 10 D (0 : V)) (hW 0) hcenter (htype 0) cut hafter
  · have hleaf : c = 1 ∨ c = 4 ∨ c = 5 := (outside_inner c hc).resolve_left hc0
    refine ⟨leafCover c,(PEqualNP.Outside.L_meta_2590_aux.I0Proof.FiveGroupGeometry.leaf_cover_geometry c hleaf).1,?_⟩
    intro e he _
    exact PEqualNP.Outside.L_meta_2590_aux.I0Proof.FiveGroupGeometry.leaf_exit_cover P hP (fun e => supp 10 D (src D e)) c hleaf e
      (by rw [← hknown c hc0]; exact he) (htype c e he)

end DagTools.FiveCase

namespace SixCase

open PEqualNP.Outside.L_meta_2590_aux.I0Proof.DagTools

abbrev V := Fin 10

abbrev Slot := ℕ × Bool

def leftSide : Fin 6 → Finset V := ![{0}, {0}, {1}, {2}, {6}, {4, 7, 8}]

def rightSide : Fin 6 → Finset V := ![{1}, {4, 5}, {2, 6}, {3, 7}, {8, 9}, {3, 5, 9}]

def side (i : Fin 6) (s : Bool) : Finset V := if s then rightSide i else leftSide i

def edgeU : Fin 6 → V := ![4, 4, 7, 7, 8, 8]

def edgeV : Fin 6 → V := ![3, 9, 5, 9, 3, 5]

lemma side_nonempty : ∀ i s, (side i s).Nonempty := by decide +kernel

lemma two_positions : ∀ v : V, ∃ (i : Fin 6) (s : Bool) (j : Fin 6) (t : Bool),
    i ≠ j ∧ v ∈ side i s ∧ v ∈ side j t := by decide +kernel

lemma cross_unique : ∀ (e i : Fin 6) (s : Bool),
    edgeU e ∈ side i s → edgeV e ∈ side i (!s) → i = 5 := by decide +kernel

lemma side_misses : ∀ i : Fin 6, i ≠ 5 → ∀ s : Bool,
    ∃ e : Fin 6, edgeU e ∉ side i s ∧ edgeV e ∉ side i s := by decide +kernel

lemma outside_misses : ∀ v : V,
    (∀ e : Fin 6, v ≠ edgeU e ∧ v ≠ edgeV e) →
    ∃ e : Fin 6, ∀ (i : Fin 6) (s : Bool), v ∈ side i s →
      edgeU e ∉ side i (!s) ∧ edgeV e ∉ side i (!s) := by decide +kernel

def slotPos (slots : Fin 6 → Slot) (i : Fin 6) (s : Bool) : Slot :=
  if s then sem_bar (slots i) else slots i

lemma slotPos_fst (slots : Fin 6 → Slot) (i : Fin 6) (s : Bool) :
    (slotPos slots i s).1 = (slots i).1 := by cases s <;> rfl

lemma slotPos_bar (slots : Fin 6 → Slot) (i : Fin 6) (s : Bool) :
    sem_bar (slotPos slots i s) = slotPos slots i (!s) := by
  cases s <;> simp [slotPos, sem_bar_bar]

lemma slotPos_injective (slots : Fin 6 → Slot)
    (hinj : Function.Injective (fun i => (slots i).1)) :
    Function.Injective (fun p : Fin 6 × Bool => slotPos slots p.1 p.2) := by
  rintro ⟨i, s⟩ ⟨j, t⟩ he
  have hij : i = j := hinj (by simpa only [slotPos_fst] using congrArg Prod.fst he)
  subst j
  have hst : s = t := by
    cases s <;> cases t
    · rfl
    · exact False.elim (sem_bar_ne (slots i) he.symm)
    · exact False.elim (sem_bar_ne (slots i) he)
    · rfl
  exact Prod.ext rfl hst

lemma code_budget {D : Dag} {G : V → V → Prop}
    (hG : sem_Gr G) (h : StrictLive 10 D) (hC : sem_Comp 10 G D)
    (hBp : Bplus 10 D = (eligSet 10 D).card) (v : V) :
    (sem_W 10 D v).card + (merges 10 D (carrierT 10 D {v})).card ≤ 2 := by
  obtain ⟨b, hb⟩ := sem_exists_pureBranch hG h.1 hC
  have hs := surplus_carrierT_le h.1 b hb {v}
  have hcard : (({v} : Finset V) ∩ eligSet 10 D).card ≤ 1 :=
    (Finset.card_le_card Finset.inter_subset_left).trans_eq (Finset.card_singleton v)
  have hf := sem_flow1 hG h hC v
  omega

lemma slots_exhaust {D : Dag} (slots : Fin 6 → Slot)
    (hinj : Function.Injective (fun i => (slots i).1))
    (hbudget : ∀ v : V, (sem_W 10 D v).card +
      (merges 10 D (carrierT 10 D {v})).card ≤ 2)
    (hslots : ∀ (i : Fin 6) (s : Bool) (v : V), v ∈ side i s →
      slotPos slots i s ∈ sem_W 10 D v) :
    (∀ v : V, (sem_W 10 D v).card = 2 ∧ merges 10 D (carrierT 10 D {v}) = ∅) ∧
    (∀ v e, e ∈ sem_W 10 D v →
      ∃ i s, v ∈ side i s ∧ e = slotPos slots i s) := by
  have hlocal (v : V) :
      (sem_W 10 D v).card = 2 ∧ merges 10 D (carrierT 10 D {v}) = ∅ ∧
      ∀ e ∈ sem_W 10 D v, ∃ i s, v ∈ side i s ∧ e = slotPos slots i s := by
    obtain ⟨i, s, j, t, hij, hi, hj⟩ := two_positions v
    have hp := hslots i s v hi
    have hq := hslots j t v hj
    have hpq : slotPos slots i s ≠ slotPos slots j t := by
      intro he
      exact hij (hinj (by simpa only [slotPos_fst] using congrArg Prod.fst he))
    have hsub : {slotPos slots i s, slotPos slots j t} ⊆ sem_W 10 D v := by
      intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl <;> assumption
    have hb := hbudget v
    have heq : {slotPos slots i s, slotPos slots j t} = sem_W 10 D v :=
      Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair hpq]; omega)
    have hc : (sem_W 10 D v).card = 2 := by rw [← heq, Finset.card_pair hpq]
    refine ⟨hc, Finset.card_eq_zero.mp (by omega), ?_⟩
    intro e he
    rw [← heq] at he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact ⟨i, s, hi, rfl⟩
    · exact ⟨j, t, hj, rfl⟩
  exact ⟨fun v => ⟨(hlocal v).1, (hlocal v).2.1⟩, fun v e he => (hlocal v).2.2 e he⟩

lemma and_supp_empty {D : Dag} (h : Strict 10 D)
    (hmerge : ∀ v : V, merges 10 D (carrierT 10 D {v}) = ∅)
    (k : ℕ) (hk : k < D.length) (ht : tag D k = true) : supp 10 D (10 + k) = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro v hv
  have hab := hv
  rw [sem_supp_and h hk ht, Finset.mem_inter] at hab
  have hm : k ∈ merges 10 D (carrierT 10 D {v}) := by
    rw [merges, Finset.mem_filter, Finset.mem_range]
    exact ⟨hk, sem_mem_carrier1.mpr hv,
      sem_mem_carrier1.mpr hab.1, sem_mem_carrier1.mpr hab.2⟩
  rw [hmerge v] at hm
  exact Finset.notMem_empty _ hm

lemma slot_valid {D : Dag} (h : Strict 10 D) (slots : Fin 6 → Slot)
    (hslots : ∀ (i : Fin 6) (s : Bool) (v : V), v ∈ side i s →
      slotPos slots i s ∈ sem_W 10 D v) (i : Fin 6) (s : Bool) :
    (slotPos slots i s).1 < D.length ∧ tag D (slotPos slots i s).1 = true := by
  obtain ⟨v, hv⟩ := side_nonempty i s
  have he := hslots i s v hv
  exact ⟨(sem_mem_W.mp he).1, sem_W_and h he⟩

lemma side_exact {D : Dag} (h : Strict 10 D) (slots : Fin 6 → Slot)
    (hinj : Function.Injective (fun i => (slots i).1))
    (hslots : ∀ (i : Fin 6) (s : Bool) (v : V), v ∈ side i s →
      slotPos slots i s ∈ sem_W 10 D v)
    (hcover : ∀ v e, e ∈ sem_W 10 D v → ∃ i s, v ∈ side i s ∧ e = slotPos slots i s)
    (hempty : ∀ k < D.length, tag D k = true → supp 10 D (10 + k) = ∅) :
    ∀ i s, supp 10 D (src D (slotPos slots i s)) = side i s := by
  intro i s
  ext v
  constructor
  · intro hv
    have hk := slot_valid h slots hslots i s
    have hw : slotPos slots i s ∈ sem_W 10 D v := by
      apply sem_mem_W.mpr
      refine ⟨hk.1, hv, ?_⟩
      rw [hempty _ hk.1 hk.2]
      exact Finset.notMem_empty _
    obtain ⟨j, t, hvt, he⟩ := hcover v _ hw
    have hpair : (i, s) = (j, t) := slotPos_injective slots hinj he
    cases hpair
    exact hvt
  · intro hv
    exact (sem_mem_W.mp (hslots i s v hv)).2.1

lemma pair_source {D : Dag} (slots : Fin 6 → Slot)
    (hcover : ∀ v e, e ∈ sem_W 10 D v → ∃ i s, v ∈ side i s ∧ e = slotPos slots i s)
    (hsides : ∀ i s, supp 10 D (src D (slotPos slots i s)) = side i s) :
    ∀ e : Fin 6, ∀ p ∈ sem_W 10 D (edgeU e),
      sem_bar p ∈ sem_W 10 D (edgeV e) → p.1 = (slots 5).1 := by
  intro e p hp hbar
  obtain ⟨i, s, hu, rfl⟩ := hcover _ _ hp
  have hv := (sem_mem_W.mp hbar).2.1
  rw [slotPos_bar, hsides] at hv
  have hi : i = 5 := cross_unique e i s hu hv
  subst i
  exact slotPos_fst slots 5 s

lemma other_operand_misses {D : Dag} (slots : Fin 6 → Slot)
    (hcover : ∀ v e, e ∈ sem_W 10 D v → ∃ i s, v ∈ side i s ∧ e = slotPos slots i s)
    (hsides : ∀ i s, supp 10 D (src D (slotPos slots i s)) = side i s)
    (hempty : ∀ k < D.length, tag D k = true → supp 10 D (10 + k) = ∅) :
    ∀ k < D.length, k ≠ (slots 5).1 → tag D k = true → ∀ s : Bool,
      ∃ e : Fin 6, edgeU e ∉ supp 10 D (src D (k, s)) ∧
        edgeV e ∉ supp 10 D (src D (k, s)) := by
  intro k hk hkg ht s
  by_cases hne : (supp 10 D (src D (k, s))).Nonempty
  · obtain ⟨v, hv⟩ := hne
    have hw : (k, s) ∈ sem_W 10 D v := by
      apply sem_mem_W.mpr
      refine ⟨hk, hv, ?_⟩
      rw [hempty k hk ht]
      exact Finset.notMem_empty _
    obtain ⟨i, t, _, he⟩ := hcover v _ hw
    have hi : i ≠ 5 := by
      intro hi
      subst i
      exact hkg (by simpa only [slotPos_fst] using congrArg Prod.fst he)
    obtain ⟨e, hu, hv⟩ := side_misses i hi t
    refine ⟨e, ?_, ?_⟩ <;> rw [he, hsides] <;> assumption
  · have he : supp 10 D (src D (k, s)) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    exact ⟨0, by rw [he]; exact Finset.notMem_empty _, by rw [he]; exact Finset.notMem_empty _⟩

lemma bad_pair_at_source {D : Dag} (h : Strict 10 D) (slots : Fin 6 → Slot)
    (hslots : ∀ (i : Fin 6) (s : Bool) (v : V), v ∈ side i s →
      slotPos slots i s ∈ sem_W 10 D v)
    (hsides : ∀ i s, supp 10 D (src D (slotPos slots i s)) = side i s) :
    val D (sem_two (4 : V) 5) (10 + (slots 5).1) = true := by
  have hk := slot_valid h slots hslots 5 false
  change (slots 5).1 < D.length ∧ tag D (slots 5).1 = true at hk
  have h4 : (4 : V) ∈ supp 10 D (src D (slotPos slots 5 false)) := by
    rw [hsides]
    decide
  have h5 : (5 : V) ∈ supp 10 D (src D (slotPos slots 5 true)) := by
    rw [hsides]
    decide
  have hleft := sem_val_of_supp h h4 (show sem_two (4 : V) 5 4 = true by simp [sem_two])
  have hright := sem_val_of_supp h h5 (show sem_two (4 : V) 5 5 = true by simp [sem_two])
  change val D (sem_two (4 : V) 5) (src D (slots 5)) = true at hleft
  change val D (sem_two (4 : V) 5) (src D (sem_bar (slots 5))) = true at hright
  rw [val_gate h _ _ hk.1, hk.2, gop_true]
  cases hs : (slots 5).2
  · have ha : val D (sem_two (4 : V) 5) (opA D (slots 5).1) = true := by
      simpa only [src, hs, Bool.false_eq_true, ite_false] using hleft
    have hb : val D (sem_two (4 : V) 5) (opB D (slots 5).1) = true := by
      simpa only [src, sem_bar, hs, Bool.not_false, ite_true] using hright
    simp only [ha, hb, Bool.and_self]
  · have hb : val D (sem_two (4 : V) 5) (opB D (slots 5).1) = true := by
      simpa only [src, hs, ite_true] using hleft
    have ha : val D (sem_two (4 : V) 5) (opA D (slots 5).1) = true := by
      simpa only [src, sem_bar, hs, Bool.not_true, Bool.false_eq_true, ite_false] using hright
    simp only [ha, hb, Bool.and_self]

lemma bad_pair_at_output {D : Dag} {G : V → V → Prop}
    (hG : sem_Gr G) (hC : sem_Comp 10 G D) (hbad : ¬ G 4 5) :
    val D (sem_two (4 : V) 5) (outW 10 D) = false := by
  have hnon : ¬ sem_Edge G (sem_two (4 : V) 5) := by
    rintro ⟨u, v, huv, hu, hv⟩
    simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact hG.2.1 _ huv
    · exact hbad huv
    · exact hbad (hG.1 _ _ huv)
    · exact hG.2.1 _ huv
  exact Bool.eq_false_iff.mpr (fun hp => hnon ((hC _).mp hp))

open PEqualNP.Outside.L_meta_2590_aux.I0Proof.DagTools

lemma canonical_six_impossible {D : Dag} {G : V → V → Prop}
    (hG : sem_Gr G) (h : StrictLive 10 D) (hC : sem_Comp 10 G D)
    (hBp : Bplus 10 D = (eligSet 10 D).card) (hB0 : Bzero 10 D = 0)
    (slots : Fin 6 → Slot) (hinj : Function.Injective (fun i => (slots i).1))
    (hslots : ∀ (i : Fin 6) (s : Bool) (v : V), v ∈ side i s →
      slotPos slots i s ∈ sem_W 10 D v)
    (hedge : ∀ e : Fin 6, G (edgeU e) (edgeV e)) (hbad : ¬ G 4 5) : False := by
  have hbudget := code_budget hG h hC hBp
  obtain ⟨hcounts, hcover⟩ := slots_exhaust slots hinj hbudget hslots
  have hempty := and_supp_empty h.1 (fun v => (hcounts v).2)
  have hsides := side_exact h.1 slots hinj hslots hcover hempty
  have hsources := pair_source slots hcover hsides
  have hmiss := other_operand_misses slots hcover hsides hempty
  have hqg := bad_pair_at_source h.1 slots hslots hsides
  have hq : ¬ sem_Edge G (sem_two (4 : V) 5) := by
    intro hx
    have hp := (hC _).mpr hx
    have hf := bad_pair_at_output hG hC hbad
    rw [hf] at hp
    contradiction
  obtain ⟨cut, hchain, hbranch, hall⟩ := sem_slot_common_branch (0 : Fin 6)
    hG h hC (slots 5).1 edgeU edgeV hedge hsources hmiss
    (sem_two (4 : V) 5) hq hqg
  obtain ⟨v, hsupp, _⟩ := h9_all_branch_pure hG h.1 hC hBp hB0 cut hbranch
  have hv : v ∈ supp 10 D cut := by rw [hsupp]; exact Finset.mem_singleton_self v
  have hout : ∀ e : Fin 6, v ≠ edgeU e ∧ v ≠ edgeV e := by
    intro e
    exact ⟨fun he => (hall e).2.1 (he ▸ hv), fun he => (hall e).2.2 (he ▸ hv)⟩
  obtain ⟨e, he⟩ := outside_misses v hout
  apply sem_slot_carrier_graph hG h hC (slots 5).1 cut (edgeU e) (edgeV e) v
    (hedge e) (hsources e) hchain hv
  intro p hp
  obtain ⟨i, s, hvs, rfl⟩ := hcover v p hp
  simpa only [slotPos_bar, hsides] using he i s hvs

end SixCase

namespace DagTools.FiveCase

open PEqualNP.Outside.L_meta_2590_aux.I0Proof.FiveGroupGeometry (sides known flip bar leafCover member_known)

lemma code_budget_tight {D : Dag} (h : StrictLive 10 D) (hC : sem_Comp 10 G D)
    (hBp : Bplus 10 D = (eligSet 10 D).card) (v : V) :
    (sem_W 10 D v).card + (merges 10 D (carrierT 10 D {v})).card ≤ 2 := by
  obtain ⟨b, hb⟩ := sem_exists_pureBranch FourCase.graph h.1 hC
  have hs := surplus_carrierT_le h.1 b hb {v}
  have hcard : (({v} : Finset V) ∩ eligSet 10 D).card ≤ 1 :=
    (Finset.card_le_card Finset.inter_subset_left).trans_eq (Finset.card_singleton v)
  have hf := sem_flow1 FourCase.graph h hC v
  omega

lemma nonzero_merge_empty_tight {D : Dag} (h : StrictLive 10 D) (hC : sem_Comp 10 G D)
    (hBp : Bplus 10 D = (eligSet 10 D).card)
    (P : Fin 5 → Slot) (hP : Function.Injective (fun i => (P i).1))
    (hslots : ∀ i : Fin 5, ∀ s : Bool, ∀ v ∈ PEqualNP.Outside.L_meta_2590_aux.I0Proof.FiveGroupGeometry.sides i s,
      PEqualNP.Outside.L_meta_2590_aux.I0Proof.FiveGroupGeometry.flip s (P i) ∈ sem_W 10 D v)
    (v : V) (hv : v ≠ 0) : merges 10 D (carrierT 10 D {v}) = ∅ := by
  have hb := code_budget_tight h hC hBp v
  have hlo : 2 ≤ (sem_W 10 D v).card := by
    rw [← known_card P hP v hv]
    exact Finset.card_le_card (known_subset P hslots v)
  exact Finset.card_eq_zero.mp (by omega)

lemma canonical_five_tight_impossible {D : Dag} (h : StrictLive 10 D) (hC : sem_Comp 10 G D)
    (hBp : Bplus 10 D = (eligSet 10 D).card) (hB0 : Bzero 10 D = 0)
    (P : Fin 5 → Slot) (hP : Function.Injective (fun i => (P i).1))
    (hslots : ∀ i : Fin 5, ∀ s : Bool, ∀ v ∈ sides i s, flip s (P i) ∈ sem_W 10 D v) :
    False := by
  have hbudget := code_budget_tight h hC hBp
  have hW (v : V) : (sem_W 10 D v).card ≤ 2 := by have := hbudget v; omega
  have hknown := known_eq_W P hP hW hslots
  have hM := nonzero_merge_empty_tight h hC hBp P hP hslots
  have htype := and_input_typed h.1 P hknown hM
  have hsource (i : Fin 3) (e : Slot) (he : e ∈ sem_W 10 D (U i))
      (hbe : sem_bar e ∈ sem_W 10 D (Vv i)) : e.1 = (P 4).1 :=
    inner_opposite_source P hP hknown (U i) (Vv i)
      (matching_inner i).1 (matching_inner i).2 e he hbe
  have hmiss (k : ℕ) (hk : k < D.length) (hkg : k ≠ (P 4).1)
      (ht : tag D k = true) (s : Bool) :
      ∃ i : Fin 3, U i ∉ supp 10 D (src D (k,s)) ∧ Vv i ∉ supp 10 D (src D (k,s)) :=
    missed_of_small _ (PEqualNP.Outside.L_meta_2590_aux.I0Proof.FiveGroupGeometry.support_size P hP (fun e => supp 10 D (src D e))
      (k,s) (htype (k,s) hk ht) hkg)
  have h6 : P 4 ∈ sem_W 10 D (6 : V) := hslots 4 false 6 (by decide +kernel)
  have h2 : sem_bar (P 4) ∈ sem_W 10 D (2 : V) := hslots 4 true 2 (by decide +kernel)
  have hq : ¬ sem_Edge G (sem_two (2 : V) 6) := by
    unfold sem_Edge G PEqualNP.Outside.L_meta_2590_aux.I0Proof.FourGroupGeometry.adj
    decide +kernel
  have hleft : val D (sem_two (2 : V) 6) (src D (P 4)) = true :=
    sem_val_of_supp h.1 (sem_mem_W.mp h6).2.1 (by simp [sem_two])
  have hright : val D (sem_two (2 : V) 6) (src D (sem_bar (P 4))) = true :=
    sem_val_of_supp h.1 (sem_mem_W.mp h2).2.1 (by simp [sem_two])
  have hqg : val D (sem_two (2 : V) 6) (10 + (P 4).1) = true := by
    rw [val_gate h.1 _ _ (sem_mem_W.mp h6).1, sem_W_and h.1 h6, gop_true]
    cases hs : (P 4).2
    · simp only [src,sem_bar,hs,Bool.not_false,Bool.false_eq_true,ite_false,ite_true] at hleft hright
      simp [hleft,hright]
    · simp only [src,sem_bar,hs,Bool.not_true,Bool.false_eq_true,ite_false,ite_true] at hleft hright
      simp [hleft,hright]
  obtain ⟨cut,hchain,hfan,hmixed⟩ := sem_slot_common_branch (0 : Fin 3)
    FourCase.graph h hC (P 4).1 U Vv matching_edges hsource hmiss (sem_two (2 : V) 6) hq hqg
  obtain ⟨c,hpure,_⟩ := h9_all_branch_pure FourCase.graph h.1 hC hBp hB0 cut hfan
  have hcut : c ∈ supp 10 D cut := by rw [hpure]; exact Finset.mem_singleton_self _
  have hc : c ∉ I := by
    intro hc
    obtain ⟨i,hi | hi⟩ := matching_cover c hc
    · exact (hmixed i).2.1 (by rw [hi]; exact hcut)
    · exact (hmixed i).2.2 (by rw [hi]; exact hcut)
  have hafter : 10 + (P 4).1 ≤ cut :=
    PEqualNP.Outside.L_meta_2590_aux.I0Proof.le_of_increasing_path _ (fun _ _ hh => sem_step_lt h.1 hh.1) hchain
  have hcenter : P 0 ∈ sem_W 10 D (0 : V) := hslots 0 false 0 (by decide +kernel)
  obtain ⟨T,hT,hcover⟩ := exit_cover h.1 P hP hW hknown hM hcenter cut hafter c hc
  obtain ⟨i,hu,hv⟩ := missed_of_small T
    ((Finset.card_le_card Finset.inter_subset_left).trans hT)
  apply sem_slot_carrier_graph_after FourCase.graph h hC (P 4).1 cut (U i) (Vv i) c
    (matching_edges i) (hsource i) hchain hcut
  intro e he heafter
  have hsub := hcover e he heafter
  exact ⟨fun hm => hu (hsub (Finset.mem_inter.mpr ⟨hm,(matching_inner i).1⟩)),
    fun hm => hv (hsub (Finset.mem_inter.mpr ⟨hm,(matching_inner i).2⟩))⟩

end DagTools.FiveCase

namespace DagTools

lemma h9_exit_budget_tight {n : ℕ} {D : Dag} {G : Fin n → Fin n → Prop}
    (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (hBp : Bplus n D = (eligSet n D).card) (v : Fin n) :
    (sem_W n D v).card + (merges n D (carrierT n D {v})).card ≤ 2 := by
  obtain ⟨b, hb⟩ := sem_exists_pureBranch hG h.1 hC
  have hs := surplus_carrierT_le h.1 b hb {v}
  have hcard : (({v} : Finset (Fin n)) ∩ eligSet n D).card ≤ 1 :=
    (Finset.card_le_card Finset.inter_subset_left).trans_eq (Finset.card_singleton v)
  have hf := sem_flow1 hG h hC v
  omega

lemma h9_eligible_of_two_exits {n : ℕ} {D : Dag} {G : Fin n → Fin n → Prop}
    (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (hBp : Bplus n D = (eligSet n D).card) (v : Fin n)
    (hW : 2 ≤ (sem_W n D v).card) : v ∈ eligSet n D := by
  by_contra hv
  obtain ⟨b, hb⟩ := sem_exists_pureBranch hG h.1 hC
  have hs := surplus_carrierT_le h.1 b hb {v}
  have he : ({v} : Finset (Fin n)) ∩ eligSet n D = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro u hu
    obtain ⟨huv, hue⟩ := Finset.mem_inter.mp hu
    have huv' : u = v := Finset.mem_singleton.mp huv
    exact hv (huv' ▸ hue)
  have hcard : (({v} : Finset (Fin n)) ∩ eligSet n D).card = 0 := by rw [he]; rfl
  have hf := sem_flow1 hG h hC v
  omega

end DagTools

namespace DagTools.FourCase

open PEqualNP.Outside.L_meta_2590_aux.I0Proof.FourGroupGeometry

lemma abstract_four_forces_all_eligible {D : Dag}
    (h : StrictLive 10 D) (hC : sem_Comp 10 adj D)
    (hBp : Bplus 10 D = (eligSet 10 D).card)
    (big : Slot) (matchSlot : V → Slot)
    (hQ : ∀ v ∈ Q, big ∈ sem_W 10 D v)
    (hR : ∀ v ∈ R, sem_bar big ∈ sem_W 10 D v ∧ matchSlot v ∈ sem_W 10 D v)
    (hdiff : ∀ v ∈ R, (matchSlot v).1 ≠ big.1) : eligSet 10 D = Finset.univ := by
  have hbudget := h9_exit_budget_tight graph h hC hBp
  have hW (v : V) : (sem_W 10 D v).card ≤ 2 := by have := hbudget v; omega
  have hextra := pure_extra h.1 hC hW big hQ
  have hcounts := W_two big matchSlot hbudget hQ hextra hR hdiff
  ext v
  constructor
  · intro _
    exact Finset.mem_univ v
  · intro _
    apply h9_eligible_of_two_exits graph h hC hBp v
    rw [(hcounts v).1]

lemma canonical_four_tight_impossible {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 adj D)
    (hBp : Bplus 10 D = (eligSet 10 D).card) (hB0 : Bzero 10 D = 0)
    (big a b c : Slot)
    (hab : a.1 ≠ b.1) (hac : a.1 ≠ c.1) (hbc : b.1 ≠ c.1)
    (hag : a.1 ≠ big.1) (hbg : b.1 ≠ big.1) (hcg : c.1 ≠ big.1)
    (hQ : ∀ v ∈ Q, big ∈ sem_W 10 D v)
    (hR : ∀ v ∈ R, sem_bar big ∈ sem_W 10 D v)
    (ha0 : a ∈ sem_W 10 D (0 : V)) (ha1 : sem_bar a ∈ sem_W 10 D (1 : V))
    (hb3 : b ∈ sem_W 10 D (3 : V)) (hb8 : sem_bar b ∈ sem_W 10 D (8 : V))
    (hc7 : c ∈ sem_W 10 D (7 : V)) (hc9 : sem_bar c ∈ sem_W 10 D (9 : V)) : False := by
  have hRR : ∀ v ∈ R, sem_bar big ∈ sem_W 10 D v ∧ matching a b c v ∈ sem_W 10 D v := by
    intro v hv
    refine ⟨hR v hv, ?_⟩
    rw [mem_R] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [matching]
  have hdiff : ∀ v ∈ R, (matching a b c v).1 ≠ big.1 := by
    intro v hv
    rw [mem_R] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [matching, sem_bar]
  have hall := abstract_four_forces_all_eligible h hC hBp big (matching a b c) hQ hRR hdiff
  have hB : Bplus 10 D = 10 := by
    rw [hBp, hall, Finset.card_univ, Fintype.card_fin]
  exact canonical_four_impossible h hC hall hB hB0 big a b c hab hac hbc hag hbg hcg
    hQ hR ha0 ha1 hb3 hb8 hc7 hc9

end DagTools.FourCase

namespace DagTools

end DagTools

namespace DagTools

lemma relabel_mem_image {n : ℕ} (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n)) (v : Fin n) :
    σ v ∈ S.image σ ↔ v ∈ S := by
  constructor
  · intro hv
    obtain ⟨u, hu, huv⟩ := Finset.mem_image.mp hv
    exact σ.injective huv ▸ hu
  · intro hv
    exact Finset.mem_image_of_mem σ hv

lemma relabel_src {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (e : ℕ × Bool)
    (he : e.1 < D.length) : src (relabel σ D) e = liftP σ (src D e) := by
  rcases e with ⟨k,s⟩
  cases s
  · exact tr_opA σ D k he
  · exact tr_opB σ D k he

lemma relabel_port_support {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag}
    (hS : Strict n D) (e : ℕ × Bool) (he : e.1 < D.length) :
    supp n (relabel σ D) (src (relabel σ D) e) = (supp n D (src D e)).image σ := by
  rw [relabel_src σ D e he, relabel_supp σ hS]

lemma relabel_gate_support {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag}
    (hS : Strict n D) (k : ℕ) :
    supp n (relabel σ D) (n + k) = (supp n D (n + k)).image σ := by
  simpa only [tr_liftP_ge σ (Nat.le_add_right n k)] using relabel_supp σ hS (n + k)

lemma relabel_W {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) (v : Fin n) :
    sem_W n (relabel σ D) (σ v) = sem_W n D v := by
  ext e
  rw [sem_mem_W, sem_mem_W, relabel_length]
  by_cases he : e.1 < D.length
  · simp only [he, true_and]
    rw [relabel_port_support σ hS e he, relabel_gate_support σ hS,
      relabel_mem_image, relabel_mem_image]
  · simp only [he, false_and]

lemma relabel_W_preimage {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag}
    (hS : Strict n D) (v : Fin n) :
    sem_W n (relabel σ D) v = sem_W n D (σ.symm v) := by
  simpa only [Equiv.apply_symm_apply] using relabel_W σ hS (σ.symm v)

lemma relabel_comp {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag}
    {G H : Fin n → Fin n → Prop}
    (h : StrictLive n D) (hC : sem_Comp n G D)
    (hσ : ∀ u v, H (σ u) (σ v) ↔ G u v) : sem_Comp n H (relabel σ D) := by
  intro x
  rw [relabel_out σ h.1 h.2.2, hC]
  constructor
  · rintro ⟨u,v,huv,hu,hv⟩
    exact ⟨σ u,σ v,(hσ u v).mpr huv,hu,hv⟩
  · rintro ⟨u,v,huv,hu,hv⟩
    refine ⟨σ.symm u,σ.symm v,(hσ _ _).mp (by simpa using huv),?_,?_⟩
    · simpa using hu
    · simpa using hv

end DagTools

namespace DagTools

lemma relabel_inner {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (hne : D ≠ []) :
    (inner n D).image (liftP σ) = inner n (relabel σ D) := by
  have hlen : 0 < D.length := List.length_pos_iff.mpr hne
  have hcut : n ≤ n + D.length - 1 := by omega
  ext w
  simp only [Finset.mem_image, inner, Finset.mem_range, relabel_length]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (tr_liftP_lt_iff σ hcut v).2 hv
  · intro hw
    refine ⟨liftP σ⁻¹ w, ?_, tr_liftP_inv' σ w⟩
    exact (tr_liftP_lt_iff σ⁻¹ hcut w).2 hw

lemma relabel_Bplus {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag}
    (hS : Strict n D) (hne : D ≠ []) : Bplus n (relabel σ D) = Bplus n D := by
  classical
  unfold Bplus surplusOn
  rw [Finset.sum_filter, Finset.sum_filter, ← relabel_inner σ D hne, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro w hw
    rw [relabel_supp σ hS]
    simp only [Finset.image_nonempty, relabel_fanout]
  · intro a ha b hb he
    exact (tr_liftP_inj σ).mp he

lemma relabel_Bzero {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag}
    (hS : Strict n D) (hne : D ≠ []) : Bzero n (relabel σ D) = Bzero n D := by
  classical
  unfold Bzero surplusOn
  rw [Finset.sum_filter, Finset.sum_filter, ← relabel_inner σ D hne, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro w hw
    rw [relabel_supp σ hS]
    simp only [Finset.image_nonempty, relabel_fanout]
  · intro a ha b hb he
    exact (tr_liftP_inj σ).mp he

end DagTools

namespace DagTools

end DagTools

namespace DagTools

lemma relabel_elig_card {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag}
    (hS : Strict n D) :
    (eligSet n (relabel σ D)).card = (eligSet n D).card := by
  rw [relabel_eligSet σ hS, Finset.card_image_of_injective _ σ.injective]

lemma relabel_tight_budget {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag}
    (hS : Strict n D) (hne : D ≠ [])
    (hb : Bplus n D = (eligSet n D).card) :
    Bplus n (relabel σ D) = (eligSet n (relabel σ D)).card := by
  rw [relabel_Bplus σ hS hne, relabel_elig_card σ hS]
  exact hb

end DagTools

namespace Petersen

abbrev V := Fin 10

def edges : Finset (Sym2 V) := {s(0, 1), s(1, 2), s(2, 3), s(3, 4), s(4, 0), s(0, 5), s(1, 6), s(2, 7), s(3, 8),
      s(4, 9), s(5, 7), s(6, 8), s(7, 9), s(8, 5), s(9, 6)}

def related (v w : V) : Bool := decide (s(v, w) ∈ edges)

def digit (w i : ℕ) (t : List ℕ) : ℕ :=
  (t[i / 16]?.getD 0 >>> (w * (i % 16))) % (2 ^ w)

def Autom (f : V → V) : Prop := ∀ v w, related (f v) (f w) = related v w

def permWord (i : ℕ) : ℕ := digit 40 i ([126226149157589975746341902316111795087821178652033608920161735958946923079870511985886294867129905945234916616031849721433987644004584800004927027771687814726114274588084853161905303621743120, 2660427616327399435269531481718178401646082027935301662405787220980513690381215809495705737399288358085788155882573235272057163748261904316948553213991739791448677035952218303664639833339474945, 1239776632479440460244602490183314676691547349958322777359778274831490461234906931871140444825865134744593906462442277757210676840076939554254334611650596719953180810767997775417393455447621720, 680685397305202844481730047074739049850684476135515465580967989292822686912974557059058932175023691582793193531654587653421625127084123126121360498644757611592746733010595291706279375578552370, 2359441078723314407906557783535630859696363947135212612127674429424469707800345139931796134771291749332960158557197026408827764011363104189937445598002369409681521431006698551114156449727010595, 1791754269936980387159954496114408964656880037637619497637505127712020123491113231000397111323065666707872711214067982177652391611727069481362886028575371653022816591766911860414686323241216320, 1541088152341823624237729883312090527910832664816948779100557851341024978419659269577389250850737176470168489800182385030007969897233769982389941546953591982700802455662121076718277292290230645, 835185793909363909917313300847005245958202268679457184379754624500360860895227543323517272014935] : List ℕ)

def permV (k : Fin 120) (v : V) : V := ⟨((permWord k.val >>> (4*v.val)) % 16) % 10, by omega⟩

lemma permVgood : ∀ k : Fin 120, Autom (permV k) := by
  unfold Autom
  decide +kernel

lemma permVinj : ∀ k : Fin 120, Function.Injective (permV k) := by
  unfold Function.Injective
  decide +kernel

noncomputable def permEquiv (k : Fin 120) : Equiv.Perm V :=
  Equiv.ofBijective (permV k) (Finite.injective_iff_bijective.mp (permVinj k))

end Petersen

namespace SlotGeometry

abbrev V := Fin 10

def mask (m : ℕ) : Finset V := Finset.univ.filter fun i => m.testBit i.val

def edges : List (V × V) := [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]

end SlotGeometry

namespace ExtraGeometry

abbrev V := Fin 10

def mask (m : ℕ) : Finset V := Finset.univ.filter fun i => m.testBit i.val

def edges : List (V × V) := [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]

end ExtraGeometry

namespace FiniteSlots

abbrev V := Fin 10

abbrev H := Fin 15 × Bool

abbrev Slot := ℕ × Bool

def edges : Fin 15 → V × V := ![(0,1),(1,2),(2,3),(3,4),(4,0),
  (0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]

def endpoint (h : H) : V := if h.2 then (edges h.1).2 else (edges h.1).1

def barH (h : H) : H := (h.1, !h.2)

def bar (s : Slot) : Slot := (s.1, !s.2)

def incident (v : V) : Finset H := Finset.univ.filter fun h => endpoint h = v

def selected (t : H → Slot) (v : V) : Finset Slot := (incident v).image t

def lower (t : H → Slot) (h : H) : Finset V :=
  Finset.univ.filter fun v => ∃ k : H, endpoint k = v ∧ t k = t h

def independent (A : Finset V) : Prop :=
  ∀ e : Fin 15, ¬((edges e).1 ∈ A ∧ (edges e).2 ∈ A)

def touches (v : V) (A : Finset V) : Prop :=
  ∃ h : H, endpoint h = v ∧ endpoint (barH h) ∈ A

def Conditions (t : H → Slot) : Prop :=
  (∀ h, t (barH h) = bar (t h)) ∧
  (∀ h, endpoint h ∉ lower t (barH h)) ∧
  (∀ v, (selected t v).card ≤ 2) ∧
  ∀ v A, independent A → touches v A → (selected t v).card = 2 →
    ∃ h : H, endpoint h = v ∧ Disjoint (lower t h) A

lemma mem_selected {t : H → Slot} {v : V} {s : Slot} :
    s ∈ selected t v ↔ ∃ h : H, endpoint h = v ∧ t h = s := by
  simp only [selected, incident, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]

lemma lower_subset (t : H → Slot) (S : Slot → Finset V) (W : V → Finset Slot)
    (hw : ∀ h, t h ∈ W (endpoint h))
    (hs : ∀ v s, s ∈ W v → v ∈ S s) (h : H) : lower t h ⊆ S (t h) := by
  intro v hv
  obtain ⟨k, hk, he⟩ := (Finset.mem_filter.mp hv).2
  have hvS := hs (endpoint k) (t k) (hw k)
  simpa only [hk, he] using hvS

lemma conditions_of_exits (t : H → Slot) (S : Slot → Finset V) (W : V → Finset Slot)
    (hb : ∀ h, t (barH h) = bar (t h))
    (hw : ∀ h, t h ∈ W (endpoint h))
    (hs : ∀ v s, s ∈ W v → v ∈ S s)
    (ho : ∀ h, endpoint h ∉ S (t (barH h)))
    (hc : ∀ v, (W v).card ≤ 2)
    (he : ∀ v A, independent A → touches v A →
      ∃ s ∈ W v, Disjoint (S s) A) : Conditions t := by
  have hsub (v : V) : selected t v ⊆ W v := by
    intro s hs'
    obtain ⟨h, rfl, rfl⟩ := mem_selected.mp hs'
    exact hw h
  refine ⟨hb, ?_, ?_, ?_⟩
  · intro h hh
    exact ho h (lower_subset t S W hw hs (barH h) hh)
  · intro v
    exact (Finset.card_le_card (hsub v)).trans (hc v)
  · intro v A hA hv htwo
    have hEq : selected t v = W v :=
      Finset.eq_of_subset_of_card_le (hsub v) (by rw [htwo]; exact hc v)
    obtain ⟨s, hsW, hsA⟩ := he v A hA hv
    rw [← hEq] at hsW
    obtain ⟨h, hvh, hsh⟩ := mem_selected.mp hsW
    refine ⟨h, hvh, ?_⟩
    apply hsA.mono_left
    simpa only [hsh] using lower_subset t S W hw hs h

def around : V → Fin 3 → H := ![
  ![(0,false),(4,true),(5,false)], ![(0,true),(1,false),(6,false)],
  ![(1,true),(2,false),(7,false)], ![(2,true),(3,false),(8,false)],
  ![(3,true),(4,false),(9,false)], ![(5,true),(10,false),(14,true)],
  ![(6,true),(12,true),(13,false)], ![(7,true),(10,true),(11,false)],
  ![(8,true),(13,true),(14,false)], ![(9,true),(11,true),(12,false)]]

lemma around_endpoint : ∀ v i, endpoint (around v i) = v := by decide +kernel

lemma around_complete : ∀ v h, endpoint h = v → ∃ i, around v i = h := by decide +kernel

def block : Fin 4 → Fin 3 → Fin 2 := ![![0,0,1], ![0,1,0], ![0,1,1], ![0,0,0]]

def localCode (t : H → Slot) (v : V) : Fin 4 :=
  if t (around v 0) = t (around v 1) then
    if t (around v 0) = t (around v 2) then 3 else 0
  else if t (around v 0) = t (around v 2) then 1 else 2

lemma repeated_at_vertex (t : H → Slot) (v : V) (hc : (selected t v).card ≤ 2) :
    t (around v 0) = t (around v 1) ∨ t (around v 0) = t (around v 2) ∨
      t (around v 1) = t (around v 2) := by
  by_contra hn
  simp only [not_or] at hn
  have hmem (i : Fin 3) : t (around v i) ∈ selected t v :=
    mem_selected.mpr ⟨around v i, around_endpoint v i, rfl⟩
  have hsub : {t (around v 0), t (around v 1), t (around v 2)} ⊆ selected t v := by
    intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl
    · exact hmem 0
    · exact hmem 1
    · exact hmem 2
  have hh := (Finset.card_le_card hsub).trans hc
  simp [hn.1, hn.2.1, hn.2.2] at hh

lemma localCode_exact (t : H → Slot) (v : V) (hc : (selected t v).card ≤ 2)
    (i j : Fin 3) :
    t (around v i) = t (around v j) ↔
      block (localCode t v) i = block (localCode t v) j := by
  have hr := repeated_at_vertex t v hc
  by_cases h01 : t (around v 0) = t (around v 1)
  · by_cases h02 : t (around v 0) = t (around v 2)
    · have h12 := h01.symm.trans h02
      fin_cases i <;> fin_cases j <;> simp [localCode, block, h01, h02, h12]
    · have h12 : t (around v 1) ≠ t (around v 2) := fun h => h02 (h01.trans h)
      fin_cases i <;> fin_cases j <;> simp [localCode, block, h01, h02, h12, Ne.symm h02, Ne.symm h12]
  · by_cases h02 : t (around v 0) = t (around v 2)
    · have h12 : t (around v 1) ≠ t (around v 2) := fun h => h01 (h02.trans h.symm)
      fin_cases i <;> fin_cases j <;> simp [localCode, block, h01, h02, h12, Ne.symm h01, Ne.symm h12]
    · have h12 := hr.resolve_left h01 |>.resolve_left h02
      fin_cases i <;> fin_cases j <;> simp [localCode, block, h01, h02, h12, Ne.symm h01, Ne.symm h02]

def seed (q : V → Fin 4) (h k : H) : Prop :=
  ∃ v : V, ∃ i j : Fin 3, block (q v) i = block (q v) j ∧
    ((h = around v i ∧ k = around v j) ∨
      (h = barH (around v i) ∧ k = barH (around v j)))

def closed (q : V → Fin 4) : H → H → Prop := Relation.ReflTransGen (seed q)

lemma seed_sound (t : H → Slot)
    (hb : ∀ h, t (barH h) = bar (t h))
    (hc : ∀ v, (selected t v).card ≤ 2) {h k : H}
    (hr : seed (localCode t) h k) : t h = t k := by
  obtain ⟨v, i, j, hij, hcases⟩ := hr
  have he := (localCode_exact t v (hc v) i j).mpr hij
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact he
  · rw [hb, hb, he]

lemma closed_sound (t : H → Slot)
    (hb : ∀ h, t (barH h) = bar (t h))
    (hc : ∀ v, (selected t v).card ≤ 2) {h k : H}
    (hr : closed (localCode t) h k) : t h = t k := by
  induction hr with
  | refl => rfl
  | tail _ hseed ih => exact ih.trans (seed_sound t hb hc hseed)

lemma closed_local_exact (t : H → Slot)
    (hb : ∀ h, t (barH h) = bar (t h))
    (hc : ∀ v, (selected t v).card ≤ 2) (v : V) (i j : Fin 3) :
    closed (localCode t) (around v i) (around v j) ↔
      block (localCode t v) i = block (localCode t v) j := by
  constructor
  · intro hr
    exact (localCode_exact t v (hc v) i j).mp (closed_sound t hb hc hr)
  · intro hij
    exact Relation.ReflTransGen.single ⟨v, i, j, hij, Or.inl ⟨rfl, rfl⟩⟩

lemma card_two_of_code_ne_three (t : H → Slot) (v : V)
    (hc : (selected t v).card ≤ 2) (hq : localCode t v ≠ 3) :
    (selected t v).card = 2 := by
  have hblocks : ∀ q : Fin 4, q ≠ 3 → ∃ i j : Fin 3, block q i ≠ block q j := by
    decide +kernel
  obtain ⟨i, j, hij⟩ := hblocks (localCode t v) hq
  have hne : t (around v i) ≠ t (around v j) :=
    fun he => hij ((localCode_exact t v hc i j).mp he)
  have hmem (k : Fin 3) : t (around v k) ∈ selected t v :=
    mem_selected.mpr ⟨around v k, around_endpoint v k, rfl⟩
  have hsub : {t (around v i), t (around v j)} ⊆ selected t v := by
    intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · exact hmem i
    · exact hmem j
  have hh := Finset.card_le_card hsub
  simp [hne] at hh
  omega

def CodeConditions (q : V → Fin 4) : Prop :=
  (∀ v i j, closed q (around v i) (around v j) ↔ block (q v) i = block (q v) j) ∧
  (∀ h k, endpoint k = endpoint h → ¬ closed q k (barH h)) ∧
  ∀ v A, independent A → touches v A → q v ≠ 3 →
    ∃ i : Fin 3, ∀ h : H, closed q h (around v i) → endpoint h ∉ A

lemma code_conditions (t : H → Slot) (ht : Conditions t) :
    CodeConditions (localCode t) := by
  obtain ⟨hb, ho, hc, he⟩ := ht
  refine ⟨closed_local_exact t hb hc, ?_, ?_⟩
  · intro h k hv hrel
    apply ho h
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, k, hv, closed_sound t hb hc hrel⟩
  · intro v A hA hv hq
    obtain ⟨h, hhv, hdis⟩ := he v A hA hv (card_two_of_code_ne_three t v (hc v) hq)
    obtain ⟨i, hi⟩ := around_complete v h hhv
    refine ⟨i, ?_⟩
    intro k hrel hkA
    have hlower : endpoint k ∈ lower t h := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, k, rfl, ?_⟩
      rw [hi] at hrel
      exact closed_sound t hb hc hrel
    exact Finset.disjoint_left.mp hdis hlower hkA

end FiniteSlots

namespace FiniteSlots

lemma closed_of_local (q : V → Fin 4) (v : V) (i j : Fin 3)
    (hij : block (q v) i = block (q v) j) :
    closed q (around v i) (around v j) :=
  Relation.ReflTransGen.single ⟨v, i, j, hij, Or.inl ⟨rfl, rfl⟩⟩

lemma closed_of_bar_local (q : V → Fin 4) (v : V) (i j : Fin 3)
    (hij : block (q v) i = block (q v) j) :
    closed q (barH (around v i)) (barH (around v j)) :=
  Relation.ReflTransGen.single ⟨v, i, j, hij, Or.inr ⟨rfl, rfl⟩⟩

lemma reject_local {q : V → Fin 4} (hq : CodeConditions q) (v : V) (i j : Fin 3)
    (hc : closed q (around v i) (around v j))
    (hne : block (q v) i ≠ block (q v) j) : False :=
  hne ((hq.1 v i j).mp hc)

lemma reject_opposite {q : V → Fin 4} (hq : CodeConditions q) (h k : H)
    (hv : endpoint k = endpoint h) (hc : closed q k (barH h)) : False :=
  hq.2.1 h k hv hc

lemma reject_exposure {q : V → Fin 4} (hq : CodeConditions q) (v : V) (A : Finset V)
    (hA : independent A) (hv : touches v A) (htwo : q v ≠ 3)
    (hhit : ∀ i : Fin 3, ∃ h : H, closed q h (around v i) ∧ endpoint h ∈ A) : False := by
  obtain ⟨i, hi⟩ := hq.2.2 v A hA hv htwo
  obtain ⟨h, hc, hm⟩ := hhit i
  exact hi h hc hm

lemma closed_of_code (q : V → Fin 4) (v : V) (c : Fin 4) (i j : Fin 3)
    (hq : q v = c) (hij : block c i = block c j) :
    closed q (around v i) (around v j) :=
  closed_of_local q v i j (by rw [hq]; exact hij)

lemma closed_of_bar_code (q : V → Fin 4) (v : V) (c : Fin 4) (i j : Fin 3)
    (hq : q v = c) (hij : block c i = block c j) :
    closed q (barH (around v i)) (barH (around v j)) :=
  closed_of_bar_local q v i j (by rw [hq]; exact hij)

lemma reject_local_of_code {q : V → Fin 4} (hq : CodeConditions q)
    (v : V) (c : Fin 4) (i j : Fin 3) (hv : q v = c)
    (hc : closed q (around v i) (around v j))
    (hne : block c i ≠ block c j) : False :=
  reject_local hq v i j hc (by rw [hv]; exact hne)

end FiniteSlots

namespace SlotTables

open PEqualNP.Outside.L_meta_2590_aux.I0Proof.FiniteSlots

abbrev Step := V × Fin 3 × Fin 3 × Bool

def stepStart (d : Step) : H :=
  if d.2.2.2 then barH (around d.1 d.2.1) else around d.1 d.2.1

def stepEnd (d : Step) : H :=
  if d.2.2.2 then barH (around d.1 d.2.2.1) else around d.1 d.2.2.1

abbrev stepValid (q : V → Fin 4) (d : Step) : Prop :=
  block (q d.1) d.2.1 = block (q d.1) d.2.2.1

lemma step_seed (q : V → Fin 4) (d : Step) (hv : stepValid q d) :
    seed q (stepStart d) (stepEnd d) := by
  rcases d with ⟨v, i, j, s⟩
  cases s
  · exact ⟨v, i, j, hv, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨v, i, j, hv, Or.inr ⟨rfl, rfl⟩⟩

def checkPath (q : V → Fin 4) (h : H) : List Step → H → Bool
  | [], k => decide (h = k)
  | d :: ds, k => decide (h = stepStart d) && decide (stepValid q d) &&
      checkPath q (stepEnd d) ds k

lemma checkPath_closed (q : V → Fin 4) (ds : List Step) (h k : H)
    (hc : checkPath q h ds k = true) : closed q h k := by
  induction ds generalizing h with
  | nil =>
    have he : h = k := by simpa [checkPath] using hc
    subst h
    exact Relation.ReflTransGen.refl
  | cons d ds ih =>
    simp only [checkPath, Bool.and_eq_true, decide_eq_true_eq] at hc
    rcases hc with ⟨⟨rfl, hv⟩, ht⟩
    exact (Relation.ReflTransGen.single (step_seed q d hv)).trans (ih _ ht)

lemma seed_symm (q : V → Fin 4) {h k : H} (hs : seed q h k) : seed q k h := by
  obtain ⟨v, i, j, hij, hcases⟩ := hs
  refine ⟨v, j, i, hij.symm, ?_⟩
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

lemma closed_symm (q : V → Fin 4) {h k : H} (hc : closed q h k) : closed q k h := by
  induction hc with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact (Relation.ReflTransGen.single (seed_symm q hs)).trans ih

def codeWords : Fin 45 → ℕ := ![
  0x1a9aa,
  0x8696a,
  0x63f3a,
  0x86969,
  0xa1959,
  0xd8dcd,
  0x86968,
  0x44908,
  0x44508,
  0x44108,
  0x44d08,
  0x3db9c,
  0xa1a59,
  0xa1859,
  0xa1b59,
  0x1a9a6,
  0x1a9a2,
  0x1a9ae,
  0x8696b,
  0x6a6a6,
  0x8f0e7,
  0x12022,
  0x10022,
  0x11022,
  0x13022,
  0xf6673,
  0x6a696,
  0x6a686,
  0x6a6b6,
  0xa8295,
  0x49484,
  0x45484,
  0x41484,
  0x4d484,
  0xa8255,
  0xa8215,
  0xa82d5,
  0x24210,
  0x4210,
  0x14210,
  0x34210,
  0x91441,
  0x11441,
  0x51441,
  0xd1441]

def code (p : Fin 45) (v : V) : Fin 4 :=
  ⟨(Nat.shiftRight (codeWords p) (2 * v.val)) % 4, Nat.mod_lt _ (by decide)⟩

def slotWords : Fin 45 → ℕ := ![
  0xba9889baabbaab76543223ab765410,
  0x89baabba9876baab54322367ab5410,
  0x455445765454325445455445544510,
  0x89baabba9876baab54320167ab5432,
  0x8998abba9876549889320167458932,
  0x765467766776673267760167766776,
  0x89baabba9876baab54320167ab5410,
  0x457689ba549876ab89320189988910,
  0x457689ba329876ab89450189988910,
  0x457689ba329876ab89230189988910,
  0x235467983276548967230167766710,
  0x766745766776676776107667327667,
  0x8998abba9876549889107632458910,
  0x8998abba9876329889104554238910,
  0x677689987654327667105445236710,
  0xba9889baabbaab76541001ab763245,
  0xba9889baabbaab76541001ab763223,
  0x987667988998895432100189543223,
  0x679889987654988932100145893210,
  0x899889baab98765432899876541023,
  0x457667766732766767766776671076,
  0x459889ba76ba547632677667761001,
  0x237689ba54ba325489455445541001,
  0x237689ba54ba325467455445541001,
  0x237667985498325467455445541001,
  0x677667765476766710677632677667,
  0x899889baab98765410899876324501,
  0x899889baab98765410899876322301,
  0x677667988976543210677654322301,
  0x8998abbaab765432abba76541023ba,
  0x457689baab98763267456776100176,
  0x457689ba329876ab67456776100176,
  0x237689ba5498765467236776100176,
  0x235467988976548945234554100154,
  0x8998abbaab765410abba76324501ba,
  0x8998abbaab765410abba76322301ba,
  0x677689988954321089985432230198,
  0x899867ba54ba32ab6745ba1001baab,
  0x459867ba32ba98ab6723ba1001baab,
  0x457689ba32ba54ab8923ba1001baab,
  0x677645983298768945239810019889,
  0x6798abba5432765489670110677667,
  0x457689ba32ba543267450110455445,
  0x457689ba3298543267450110455445,
  0x457689983298543267450110455445]

def slotValue (p : Fin 45) (k : ℕ) : Fin 30 :=
  ⟨(Nat.shiftRight (slotWords p) (4 * k)) % 16,
    (Nat.mod_lt _ (by decide)).trans (by decide : 16 < 30)⟩

def slotData (p : Fin 45) (e : Fin 15) : Fin 30 × Fin 30 :=
  (slotValue p (2 * e.val), slotValue p (2 * e.val + 1))

def slot (i : Fin 45) (h : H) : Fin 30 :=
  if h.2 then (slotData i h.1).2 else (slotData i h.1).1

def repWords : Fin 45 → ℕ := ![
  0x31f192906242420,
  0x216b431c6242420,
  0xbd8438c020,
  0x216b431c6208109,
  0xbd84331c8508109,
  0x837a7b909,
  0x216b431c625a820,
  0x73c438c2b45a820,
  0x73c438c14bad020,
  0x73c438c39d52c20,
  0x1cf10e3052c20,
  0x7192916a,
  0xbd8434a08539820,
  0xbd8439c8e621420,
  0x2f610cc721420,
  0x31f192900118909,
  0x31f19291ac00509,
  0xc7c64a400509,
  0x85ad0c718820,
  0xa5528398a400462,
  0x839d9c862,
  0x9cb19292306b001,
  0x9c98dde8a48c001,
  0x9cb19634a48c001,
  0x272634a48c001,
  0x6b4399ac,
  0xa55283984329001,
  0xa5528399ee10c01,
  0x2954a0e610c01,
  0x837a4a0e610ca4,
  0xa56720814b7b843,
  0x73e720814bad043,
  0xbda72081ee52c43,
  0x1cf9c82052c43,
  0x837a4a08539843,
  0x837a4a23021443,
  0x20de92821443,
  0x77a6354b8c085,
  0x6306379d52c85,
  0x58ddea3052c85,
  0x18c18d52c85,
  0xbd98d005ee9c8e6,
  0x9cb19634017b8e6,
  0xbda72634017b8e6,
  0x272634017b8e6]

def representative (p : Fin 45) (c : Fin 30) : H :=
  let z := (Nat.shiftRight (repWords p) (5 * c.val)) % 32
  (⟨(z / 2) % 15, Nat.mod_lt _ (by decide)⟩, z.testBit 0)

def pathWords : Fin 45 → ℕ := ![
  0x6394400b18a200002cc800006640000000000000000490330004919ac628cae63942570000248800002440000b1a000018d00002c4800006240000b0a000018500002c080000604000000000000000000000000000000000000000000000000000000000000000000000000,
  0x32a00005950048c310004718847184b7230c65b0018a4f002c427800000000000000000024880000244000091a000008d00002c4800006240000b0a000018500002c080000604000000000000000000000000000000000000000000000000000000000000000000000000,
  0x451732f220bd97001864d002c226801610b40030c5a00000000000000001220bc001145e8904e4984a2624c000000000000000000244800002240000b0a00001851145c8bc882f45e24138a612898530004a27002241380000892000004900000000000000000000000000000,
  0x32a00005950048c310004718847184b7230c65b0018a4f002c427800000000000000000024880000244000091a000008d00002c4800006240000b0a0000185000024080000204000000000000000000000000000000000000000000000000000000000000000000000000,
  0x451732f220bd97001864d002c22680000b4a00001a500000000000000001220bc001145e000024880000244000091a000008d0000244800002240000b0a0000185000024080000204000000000000000000000000000000000000000000000000000000000000000000000000,
  0x12012c001049600000000000000001210b40010c5a90056cf8822a67c00208ac009005610c5913c842d89e221291e118908f000000000000000000090a0000085000024080000204000000000000008884a278462413c0011894008884a00002228000011400000000000000,
  0x32a00005950048c310004718847184b7230c65b0018a4f002c427800000000000000000024880000244000091a000008d00002c4800006240000b0a0000185000000000000000000008200004410000000000000000000000000000000000000000000000000000000000,
  0x32a000059500000308000118401610b40030c5a000024e80000274000000000000008904e4984a2624c000000000000000000000000000000000b0a0000185000000000000000000008200004410004a27002241380000892000004900000000000000000000000000000,
  0x12a000049500000308000118401610b40030c5a000024e80000274000000000000008904e4984a2624c000000000000000000000000000000000b0a0000185000000000000000000008200004410004a27002241380000892000004900000000000000000000000000000,
  0x308000118401610b40030c5a000024e8000027400008aa00000558904e4984a2624c000000000000000000000000000000000b0a0000185000000000000000000008200004410004a27002241380000892000004900000000000000000000000000000,
  0x12a000049500000308000118401610b40030c5a000024e8000027400008aa00000558904e4984a2624c000000000000000000000000000000000b0a0000185000000000000000000008200004410004a27002241380000892000004900000000000000000000000000000,
  0x24226b4621931a3000864d00242268000000000000008888a4f8464427c23220bf111145f00042c90022064a2044b1e10a218f000464500222228000090a0000085000000000000000000008200004410044089000214480000000000000000002228000011400000000000000,
  0x451732f220bd97001864d002c22680000b4a00001a500000000000000001220bc001145e00002c880000644000091a000008d0000244800002240000b0a0000185000024080000204000000000000000000000000000000000000000000000000000000000000000000000000,
  0x451732f220bd97001864d002c22680000b4a00001a500000000000000001220bc001145e000000000000000000091a000008d0000244800002240000b0a000018500002408000020400008a200000510000000000000000000000000000000000000000000000000000000000,
  0x451732f220bd97001864d002c22680000b4a00001a500000000000000001220bc001145e000024880000244000091a000008d0000244800002240000b0a000018500002408000020400008a200000510000000000000000000000000000000000000000000000000000000000,
  0x6394400b18a200002cc800006640000000000000000490330004919ac628cae63942570000248800002440000b1a000018d00002c480000624000090a000008500002c080000604000000000000000000000000000000000000000000000000000000000000000000000000,
  0x6394400b18a200002cc800006640000000000000000490330004919ac628cae63942570000248800002440000b1a000018d00002c4800006240000000000000000002c080000604000000000000000000000000000000000000000000000002228000011400000000000000,
  0x6394400b18a200002cc800006640000000000000000490330004919ac628cae63942570000248800002440000b1a000018d00002c480000624000090a000008500002c080000604000000000000000000000000000000000000000000000002228000011400000000000000,
  0x32a00005950048c310004718847184b7230c65b0018a4f002c427800000000000000000024880000244000091a000008d00002c4800006240000b0a0000185000024080000204000008200004410000000000000000000000000000000000000000000000000000000000,
  0x16012c0030496b20a6cd9925266c006494c00b20a600002ce800006740000000000000000002c8800006440000b1a000018d00002c480000624000090a000008500002c080000604000000000000000000000000000000000000000000000000000000000000000000000000,
  0x864d0024226801210b40010c5a90056cf8822a67c00208ac00900560000000000000022044b1e10a218f104548fc802b47c000090a000008500002408000020400000820000441004408900021448214421f102250f00000000000000000000000000000,
  0x94200000a100002cc800006640000000000000000000328000119401620bc003145e0000000000000000000000000000000002c4800006240000000000000089852c184e2860c00138a400898520000226800001340000000000000000002228000011400000000000000,
  0x94200000a100000000000000000000b2000045900000328000119401620bc003145e0000000000000000000000000000000002c4800006240000000000000089852c184e2860c00138a400898520000226800001340000000000000000002228000011400000000000000,
  0x94200000a1000024c800002640000000000000000000328000119401620bc003145e0000000000000000000000000000000002c4800006240000000000000089852c184e2860c00138a400898520000226800001340000000000000000002228000011400000000000000,
  0x94200000a1000024c8000026400000b2000045900000328000119401620bc003145e0000000000000000000000000000000002c4800006240000000000000089852c184e2860c00138a400898520000226800001340000000000000000002228000011400000000000000,
  0x12012c00104961049531c804b98e206494e10b20a78888a4f8464427c0000000000000000042c90022064a221291e118908f00046450022222800000000000000000024080000204000008200004410000000000000000011894008884a00002228000011400000000000000,
  0x16012c0030496b20a6cd9925266c006494c00b20a600002ce800006740000000000000000002c8800006440000b1a000018d000024480000224000090a000008500002c080000604000000000000000000000000000000000000000000000000000000000000000000000000,
  0x16012c0030496b20a6cd9925266c006494c00b20a600002ce800006740000000000000000002c8800006440000b1a000018d000000000000000000090a000008500002c080000604000000000000000000000000000000000892000004900000000000000000000000000000,
  0x16012c0030496b20a6cd9925266c006494c00b20a600002ce800006740000000000000000002c8800006440000b1a000018d000024480000224000090a000008500002c080000604000000000000000000000000000000000892000004900000000000000000000000000000,
  0xb4200001a100000000000000001210b40010c5a90056cf8822a67c00208ac009005600002c8800006440000b1a000018d000024480000224000090a0000085000024080000204000000000000000000000000000000000000000000000000000000000000000000000000,
  0x12a0000495000864d00242268000094a00000a500002ce80000674000000000000000000000000000022044b1e10a218f000000000000000000090a0000085000000000000000000008200004410044089000214480000892000004900000000000000000000000000000,
  0x12a0000495000864d00242268000094a00000a5000024e80000274000000000000000000000000000022044b1e10a218f000000000000000000090a0000085000000000000000000008200004410044089000214480000892000004900000000000000000000000000000,
  0x12a0000495000864d00242268000094a00000a500000000000000000000ba000045d0000000000000022044b1e10a218f000000000000000000090a0000085000000000000000000008200004410044089000214480000892000004900000000000000000000000000000,
  0x12a0000495000864d00242268000094a00000a5000024e8000027400000ba000045d0000000000000022044b1e10a218f000000000000000000090a0000085000000000000000000008200004410044089000214480000892000004900000000000000000000000000000,
  0xb4200001a100000000000000001210b40010c5a90056cf8822a67c00208ac009005600002c880000644000091a000008d000024480000224000090a0000085000024080000204000000000000000000000000000000000000000000000000000000000000000000000000,
  0xb4200001a100000000000000001210b40010c5a90056cf8822a67c00208ac009005600002c88000064400000000000000000024480000224000090a0000085000024080000204000000000000000000226800001340000000000000000000000000000000000000000000,
  0xb4200001a100000000000000001210b40010c5a90056cf8822a67c00208ac009005600002c880000644000091a000008d000024480000224000090a0000085000024080000204000000000000000000226800001340000000000000000000000000000000000000000000,
  0xb4200001a100000000000000000000b200004598888a4f8464427c00008aa000005500042c9002206480000000000000000046450022222800000000000000000000000000000000008200004410000226800001340000000000000000002228000011400000000000000,
  0x308000118400000b200004598888a4f8464427c00008aa000005500042c9002206480000000000000000046450022222800000000000000000000000000000000008200004410000226800001340000000000000000002228000011400000000000000,
  0x94200000a100000000000000000000b200004598888a4f8464427c00008aa000005500042c9002206480000000000000000046450022222800000000000000000000000000000000008200004410000226800001340000000000000000002228000011400000000000000,
  0x94200000a100000308000118400000b200004598888a4f8464427c00008aa000005500042c9002206480000000000000000046450022222800000000000000000000000000000000008200004410000226800001340000000000000000002228000011400000000000000,
  0x12012c0010496000024c800002640000b4a00001a500000000000000000000ba000045d000000000000002221291e118908f0000000000000000000000000000000002408000020400008a200000510000000000000000011894008884a00002228000011400000000000000,
  0x12012c0010496000024c800002640000000000000000000328000119400000ba000045d000000000000002221291e118908f0000000000000000000000000000000002408000020400008a200000510000000000000000011894008884a00002228000011400000000000000,
  0x12012c0010496000024c80000264000094a00000a500000000000000000000ba000045d000000000000002221291e118908f0000000000000000000000000000000002408000020400008a200000510000000000000000011894008884a00002228000011400000000000000,
  0x12012c0010496000024c80000264000094a00000a500000328000119400000ba000045d000000000000002221291e118908f0000000000000000000000000000000002408000020400008a200000510000000000000000011894008884a00002228000011400000000000000]

def unpackStep (z : ℕ) : Step :=
  (⟨(z % 16) % 10, Nat.mod_lt _ (by decide)⟩,
   ⟨((z / 16) % 4) % 3, Nat.mod_lt _ (by decide)⟩,
   ⟨((z / 64) % 4) % 3, Nat.mod_lt _ (by decide)⟩, z.testBit 8)

def unpackPath (z : ℕ) : List Step :=
  List.ofFn fun i : Fin (z % 4) => unpackStep (Nat.shiftRight z (2 + 9 * i.val))

def pathAt (p : Fin 45) (k : ℕ) : List Step :=
  unpackPath ((Nat.shiftRight (pathWords p) (29 * k)) % 536870912)

def pathData (p : Fin 45) (e : Fin 15) : List Step × List Step :=
  (pathAt p (2 * e.val), pathAt p (2 * e.val + 1))

def paths (i : Fin 45) (h : H) : List Step :=
  if h.2 then (pathData i h.1).2 else (pathData i h.1).1

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma seed_table_check : ∀ (r : Fin 45) (v : V) (a b : Fin 3),
    block (code r v) a = block (code r v) b →
      slot r (around v a) = slot r (around v b) ∧
      slot r (barH (around v a)) = slot r (barH (around v b)) := by
  decide +kernel

lemma seed_slots (r : Fin 45) {h k : H} (hs : seed (code r) h k) : slot r h = slot r k := by
  obtain ⟨v, i, j, hij, hcases⟩ := hs
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact (seed_table_check r v i j hij).1
  · exact (seed_table_check r v i j hij).2

lemma closed_slots (r : Fin 45) {h k : H} (hc : closed (code r) h k) : slot r h = slot r k := by
  induction hc with
  | refl => rfl
  | tail _ hs ih => exact ih.trans (seed_slots r hs)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_0 : ∀ h : H, checkPath (code 0) h (paths 0 h) (representative 0 (slot 0 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_1 : ∀ h : H, checkPath (code 1) h (paths 1 h) (representative 1 (slot 1 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_2 : ∀ h : H, checkPath (code 2) h (paths 2 h) (representative 2 (slot 2 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_3 : ∀ h : H, checkPath (code 3) h (paths 3 h) (representative 3 (slot 3 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_4 : ∀ h : H, checkPath (code 4) h (paths 4 h) (representative 4 (slot 4 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_5 : ∀ h : H, checkPath (code 5) h (paths 5 h) (representative 5 (slot 5 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_6 : ∀ h : H, checkPath (code 6) h (paths 6 h) (representative 6 (slot 6 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_7 : ∀ h : H, checkPath (code 7) h (paths 7 h) (representative 7 (slot 7 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_8 : ∀ h : H, checkPath (code 8) h (paths 8 h) (representative 8 (slot 8 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_9 : ∀ h : H, checkPath (code 9) h (paths 9 h) (representative 9 (slot 9 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_10 : ∀ h : H, checkPath (code 10) h (paths 10 h) (representative 10 (slot 10 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_11 : ∀ h : H, checkPath (code 11) h (paths 11 h) (representative 11 (slot 11 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_12 : ∀ h : H, checkPath (code 12) h (paths 12 h) (representative 12 (slot 12 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_13 : ∀ h : H, checkPath (code 13) h (paths 13 h) (representative 13 (slot 13 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_14 : ∀ h : H, checkPath (code 14) h (paths 14 h) (representative 14 (slot 14 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_15 : ∀ h : H, checkPath (code 15) h (paths 15 h) (representative 15 (slot 15 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_16 : ∀ h : H, checkPath (code 16) h (paths 16 h) (representative 16 (slot 16 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_17 : ∀ h : H, checkPath (code 17) h (paths 17 h) (representative 17 (slot 17 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_18 : ∀ h : H, checkPath (code 18) h (paths 18 h) (representative 18 (slot 18 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_19 : ∀ h : H, checkPath (code 19) h (paths 19 h) (representative 19 (slot 19 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_20 : ∀ h : H, checkPath (code 20) h (paths 20 h) (representative 20 (slot 20 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_21 : ∀ h : H, checkPath (code 21) h (paths 21 h) (representative 21 (slot 21 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_22 : ∀ h : H, checkPath (code 22) h (paths 22 h) (representative 22 (slot 22 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_23 : ∀ h : H, checkPath (code 23) h (paths 23 h) (representative 23 (slot 23 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_24 : ∀ h : H, checkPath (code 24) h (paths 24 h) (representative 24 (slot 24 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_25 : ∀ h : H, checkPath (code 25) h (paths 25 h) (representative 25 (slot 25 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_26 : ∀ h : H, checkPath (code 26) h (paths 26 h) (representative 26 (slot 26 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_27 : ∀ h : H, checkPath (code 27) h (paths 27 h) (representative 27 (slot 27 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_28 : ∀ h : H, checkPath (code 28) h (paths 28 h) (representative 28 (slot 28 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_29 : ∀ h : H, checkPath (code 29) h (paths 29 h) (representative 29 (slot 29 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_30 : ∀ h : H, checkPath (code 30) h (paths 30 h) (representative 30 (slot 30 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_31 : ∀ h : H, checkPath (code 31) h (paths 31 h) (representative 31 (slot 31 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_32 : ∀ h : H, checkPath (code 32) h (paths 32 h) (representative 32 (slot 32 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_33 : ∀ h : H, checkPath (code 33) h (paths 33 h) (representative 33 (slot 33 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_34 : ∀ h : H, checkPath (code 34) h (paths 34 h) (representative 34 (slot 34 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_35 : ∀ h : H, checkPath (code 35) h (paths 35 h) (representative 35 (slot 35 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_36 : ∀ h : H, checkPath (code 36) h (paths 36 h) (representative 36 (slot 36 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_37 : ∀ h : H, checkPath (code 37) h (paths 37 h) (representative 37 (slot 37 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_38 : ∀ h : H, checkPath (code 38) h (paths 38 h) (representative 38 (slot 38 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_39 : ∀ h : H, checkPath (code 39) h (paths 39 h) (representative 39 (slot 39 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_40 : ∀ h : H, checkPath (code 40) h (paths 40 h) (representative 40 (slot 40 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_41 : ∀ h : H, checkPath (code 41) h (paths 41 h) (representative 41 (slot 41 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_42 : ∀ h : H, checkPath (code 42) h (paths 42 h) (representative 42 (slot 42 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_43 : ∀ h : H, checkPath (code 43) h (paths 43 h) (representative 43 (slot 43 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_44 : ∀ h : H, checkPath (code 44) h (paths 44 h) (representative 44 (slot 44 h)) = true := by
  decide +kernel

lemma paths_checked (i : Fin 45) (h : H) : checkPath (code i) h (paths i h) (representative i (slot i h)) = true := by
  fin_cases i
  · exact paths_0 h
  · exact paths_1 h
  · exact paths_2 h
  · exact paths_3 h
  · exact paths_4 h
  · exact paths_5 h
  · exact paths_6 h
  · exact paths_7 h
  · exact paths_8 h
  · exact paths_9 h
  · exact paths_10 h
  · exact paths_11 h
  · exact paths_12 h
  · exact paths_13 h
  · exact paths_14 h
  · exact paths_15 h
  · exact paths_16 h
  · exact paths_17 h
  · exact paths_18 h
  · exact paths_19 h
  · exact paths_20 h
  · exact paths_21 h
  · exact paths_22 h
  · exact paths_23 h
  · exact paths_24 h
  · exact paths_25 h
  · exact paths_26 h
  · exact paths_27 h
  · exact paths_28 h
  · exact paths_29 h
  · exact paths_30 h
  · exact paths_31 h
  · exact paths_32 h
  · exact paths_33 h
  · exact paths_34 h
  · exact paths_35 h
  · exact paths_36 h
  · exact paths_37 h
  · exact paths_38 h
  · exact paths_39 h
  · exact paths_40 h
  · exact paths_41 h
  · exact paths_42 h
  · exact paths_43 h
  · exact paths_44 h

lemma closed_iff_slot (i : Fin 45) (h k : H) : closed (code i) h k ↔ slot i h = slot i k := by
  constructor
  · exact closed_slots i
  · intro he
    have hh := checkPath_closed (code i) (paths i h) h _ (paths_checked i h)
    have hk := checkPath_closed (code i) (paths i k) k _ (paths_checked i k)
    rw [← he] at hk
    exact hh.trans (closed_symm _ hk)

end SlotTables

namespace SlotTree

open FiniteSlots

abbrev Partial := V → Option (Fin 4)

def Agrees (q : V → Fin 4) (p : Partial) : Prop :=
  ∀ v c, p v = some c → q v = c

lemma agrees_update {q : V → Fin 4} {p : Partial} (ha : Agrees q p)
    (v : V) (c : Fin 4) (hc : q v = c) :
    Agrees q (Function.update p v (some c)) := by
  intro w d hd
  by_cases hw : w = v
  · subst w
    simp only [Function.update_self, Option.some.injEq] at hd
    exact hc.trans hd
  · rw [Function.update_of_ne hw] at hd
    exact ha w d hd

def position (h : H) : Fin 3 :=
  if h.2 then
    (![0,0,0,0,1,0,0,0,0,0,1,1,1,1,2] : Fin 15 → Fin 3) h.1
  else
    (![0,1,1,1,1,2,2,2,2,2,1,2,2,2,2] : Fin 15 → Fin 3) h.1

lemma around_position : ∀ h : H, around (endpoint h) (position h) = h := by
  decide +kernel

lemma barH_barH (h : H) : barH (barH h) = h := by
  rcases h with ⟨e, b⟩
  cases b <;> rfl

def directCheck (p : Partial) (h k : H) : Bool :=
  match p (endpoint h) with
  | none => false
  | some c => decide (endpoint k = endpoint h ∧ block c (position h) = block c (position k))

lemma directCheck_sound {q : V → Fin 4} {p : Partial} (ha : Agrees q p)
    (h k : H) (sw : Bool) (ht : directCheck p h k = true) :
    closed q (if sw then barH h else h) (if sw then barH k else k) := by
  cases hp : p (endpoint h) with
  | none => simp [directCheck, hp] at ht
  | some c =>
    have hh : endpoint k = endpoint h ∧ block c (position h) = block c (position k) := by
      simpa only [directCheck, hp, decide_eq_true_eq] using ht
    have hk : around (endpoint h) (position k) = k := by
      rw [← hh.1]
      exact around_position k
    have hv := ha (endpoint h) c hp
    cases sw
    · simpa only [Bool.false_eq_true, ↓reduceIte, around_position, hk] using
        closed_of_code q (endpoint h) c (position h) (position k) hv hh.2
    · simpa only [↓reduceIte, around_position, hk] using
        closed_of_bar_code q (endpoint h) c (position h) (position k) hv hh.2

def linkCheck (p : Partial) (h k : H) : Bool :=
  decide (h = k) || directCheck p h k || directCheck p (barH h) (barH k)

lemma linkCheck_sound {q : V → Fin 4} {p : Partial} (ha : Agrees q p)
    (h k : H) (ht : linkCheck p h k = true) : closed q h k := by
  simp only [linkCheck, Bool.or_eq_true, decide_eq_true_eq] at ht
  rcases ht with (rfl | hd) | hb
  · exact Relation.ReflTransGen.refl
  · exact directCheck_sound ha h k false hd
  · simpa only [↓reduceIte, barH_barH] using directCheck_sound ha (barH h) (barH k) true hb

def half (n : ℕ) : H := (⟨(n / 2) % 15, by omega⟩, decide (n % 2 = 1))

def vertex (n : ℕ) : V := ⟨n % 10, by omega⟩

def localIndex (n : ℕ) : Fin 3 := ⟨n % 3, by omega⟩

def pathCheck (p : Partial) (h : H) (bits : ℕ) : ℕ → H → Bool
  | 0, k => decide (h = k)
  | n + 1, k => linkCheck p h (half (bits % 32)) &&
      pathCheck p (half (bits % 32)) (bits / 32) n k

lemma pathCheck_sound {q : V → Fin 4} {p : Partial} (ha : Agrees q p)
    (n : ℕ) (h k : H) (bits : ℕ) (ht : pathCheck p h bits n k = true) :
    closed q h k := by
  induction n generalizing h bits with
  | zero =>
    have he : h = k := by simpa only [pathCheck, decide_eq_true_eq] using ht
    subst h
    exact Relation.ReflTransGen.refl
  | succ n ih =>
    simp only [pathCheck, Bool.and_eq_true] at ht
    exact (linkCheck_sound ha _ _ ht.1).trans (ih _ _ ht.2)

def reaches (p : Partial) (h k : H) (bits : ℕ) : Bool := pathCheck p h bits 8 k

lemma reaches_sound {q : V → Fin 4} {p : Partial} (ha : Agrees q p)
    (h k : H) (bits : ℕ) (ht : reaches p h k bits = true) : closed q h k :=
  pathCheck_sound ha 8 h k bits ht

def rowBits : Fin 15 → ℕ := ![50,69,104,116,138,201,208,276,385,402,521,548,554,770,773]

def row (r : Fin 15) : Finset V := Finset.univ.filter fun v => (rowBits r).testBit v.val

lemma row_independent : ∀ r, independent (row r) := by
  unfold independent
  decide +kernel

lemma mem_row (r : Fin 15) (v : V) : v ∈ row r ↔ (rowBits r).testBit v.val = true := by
  simp [row]

def oppositeCheck (p : Partial) (bits : ℕ) : Bool :=
  let h := half (bits % 32)
  let k := half ((bits / 32) % 32)
  decide (endpoint k = endpoint h) && reaches p k (barH h) (bits / 1024)

lemma oppositeCheck_false {q : V → Fin 4} {p : Partial} (ha : Agrees q p)
    (hq : CodeConditions q) (bits : ℕ) (ht : oppositeCheck p bits = true) : False := by
  simp only [oppositeCheck, Bool.and_eq_true, decide_eq_true_eq] at ht
  exact reject_opposite hq _ _ ht.1 (reaches_sound ha _ _ _ ht.2)

def localCheck (p : Partial) (bits : ℕ) : Bool :=
  let v := vertex (bits % 16)
  let i := localIndex ((bits / 16) % 4)
  let j := localIndex ((bits / 64) % 4)
  match p v with
  | none => false
  | some c => decide (block c i ≠ block c j) &&
      reaches p (around v i) (around v j) (bits / 256)

lemma localCheck_false {q : V → Fin 4} {p : Partial} (ha : Agrees q p)
    (hq : CodeConditions q) (bits : ℕ) (ht : localCheck p bits = true) : False := by
  unfold localCheck at ht
  dsimp only at ht
  cases hp : p (vertex (bits % 16)) with
  | none => simp only [hp, Bool.false_eq_true] at ht
  | some c =>
    rw [hp] at ht
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
    exact reject_local_of_code hq _ c _ _ (ha _ _ hp) (reaches_sound ha _ _ _ ht.2) ht.1

def exposureStart (bits : ℕ) (i : Fin 3) : H :=
  half ((bits / (2 ^ (8 + i.val * 45))) % 32)

def exposurePath (bits : ℕ) (i : Fin 3) : ℕ := bits / (2 ^ (13 + i.val * 45))

def exposureCheck (p : Partial) (bits : ℕ) : Bool :=
  let v := vertex (bits % 16)
  let r : Fin 15 := ⟨((bits / 16) % 16) % 15, by omega⟩
  match p v with
  | none => false
  | some c => decide (c ≠ 3) && (decide (∃ h : H, endpoint h = v ∧ (rowBits r).testBit (endpoint (barH h)).val = true) &&
      decide (∀ i : Fin 3,
        (rowBits r).testBit (endpoint (exposureStart bits i)).val = true ∧
        reaches p (exposureStart bits i) (around v i) (exposurePath bits i) = true))

lemma exposureCheck_false {q : V → Fin 4} {p : Partial} (ha : Agrees q p)
    (hq : CodeConditions q) (bits : ℕ) (ht : exposureCheck p bits = true) : False := by
  unfold exposureCheck at ht
  dsimp only at ht
  cases hp : p (vertex (bits % 16)) with
  | none => simp only [hp, Bool.false_eq_true] at ht
  | some c =>
    rw [hp] at ht
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
    have htouch : touches (vertex (bits % 16)) (row ⟨((bits / 16) % 16) % 15, by omega⟩) := by
      obtain ⟨h, hv, hh⟩ := ht.2.1
      exact ⟨h, hv, (mem_row _ _).mpr hh⟩
    apply reject_exposure hq (vertex (bits % 16)) _ (row_independent _) htouch
    · rw [ha _ _ hp]
      exact ht.1
    · intro i
      exact ⟨exposureStart bits i, reaches_sound ha _ _ _ (ht.2.2 i).2,
        (mem_row _ _).mpr (ht.2.2 i).1⟩

def rejects (p : Partial) (n : ℕ) : Bool :=
  if n % 8 = 1 then oppositeCheck p (n / 8)
  else if n % 8 = 2 then localCheck p (n / 8)
  else if n % 8 = 3 then exposureCheck p (n / 8)
  else false

lemma rejects_false {q : V → Fin 4} {p : Partial} (ha : Agrees q p)
    (hq : CodeConditions q) (n : ℕ) (ht : rejects p n = true) : False := by
  unfold rejects at ht
  split at ht
  · exact oppositeCheck_false ha hq _ ht
  · split at ht
    · exact localCheck_false ha hq _ ht
    · split at ht
      · exact exposureCheck_false ha hq _ ht
      · cases ht

def good (codes : Fin 45 → V → Fin 4) (p : Partial) (n : ℕ) : Bool :=
  decide (∀ v, p v = some (codes ⟨n % 45, by omega⟩ v))

lemma good_sound (codes : Fin 45 → V → Fin 4) {q : V → Fin 4} {p : Partial}
    (ha : Agrees q p) (n : ℕ) (ht : good codes p n = true) :
    ∃ i, q = codes i := by
  refine ⟨⟨n % 45, by omega⟩, ?_⟩
  apply funext
  intro v
  exact ha v _ ((decide_eq_true_eq.mp ht) v)

def scanFour (f : Fin 4 → List ℕ → Option (List ℕ)) (ns : List ℕ) : Option (List ℕ) :=
  (f 0 ns).bind fun ns0 => (f 1 ns0).bind fun ns1 => (f 2 ns1).bind fun ns2 => f 3 ns2

lemma bind_some_exists {α β : Type} {a : Option α} {f : α → Option β} {b : β}
    (h : a.bind f = some b) : ∃ x, a = some x ∧ f x = some b := by
  cases a with
  | none => cases h
  | some x => exact ⟨x, rfl, h⟩

lemma scanFour_success (f : Fin 4 → List ℕ → Option (List ℕ))
    (ns rest : List ℕ) (ht : scanFour f ns = some rest) (c : Fin 4) :
    ∃ a b, f c a = some b := by
  obtain ⟨ns0, h0, hrest0⟩ := bind_some_exists ht
  obtain ⟨ns1, h1, hrest1⟩ := bind_some_exists hrest0
  obtain ⟨ns2, h2, h3⟩ := bind_some_exists hrest1
  fin_cases c
  · exact ⟨_, _, h0⟩
  · exact ⟨_, _, h1⟩
  · exact ⟨_, _, h2⟩
  · exact ⟨_, _, h3⟩

def check (codes : Fin 45 → V → Fin 4) :
    List V → Partial → List ℕ → Option (List ℕ)
  | _, _, [] => none
  | todo, p, n :: ns =>
    if n % 8 = 0 then
      match todo with
      | [] => none
      | v :: vs => scanFour (fun c => check codes vs (Function.update p v (some c))) ns
    else if n % 8 = 4 then
      if good codes p (n / 8) then some ns else none
    else if rejects p n then some ns else none

lemma check_sound (codes : Fin 45 → V → Fin 4) (todo : List V) (p : Partial)
    (ns rest : List ℕ) (q : V → Fin 4) (ht : check codes todo p ns = some rest)
    (ha : Agrees q p) (hq : CodeConditions q) : ∃ i, q = codes i := by
  induction todo generalizing p ns rest with
  | nil =>
    cases ns with
    | nil => cases ht
    | cons n ns =>
      by_cases h0 : n % 8 = 0
      · simp only [check, if_pos h0] at ht
        cases ht
      · by_cases h4 : n % 8 = 4
        · simp only [check, if_neg h0, if_pos h4] at ht
          by_cases hg : good codes p (n / 8) = true
          · exact good_sound codes ha _ hg
          · simp only [if_neg hg] at ht
            cases ht
        · simp only [check, if_neg h0, if_neg h4] at ht
          by_cases hr : rejects p n = true
          · exact (rejects_false ha hq _ hr).elim
          · simp only [if_neg hr] at ht
            cases ht
  | cons v vs ih =>
    cases ns with
    | nil => cases ht
    | cons n ns =>
      by_cases h0 : n % 8 = 0
      · simp only [check, if_pos h0] at ht
        obtain ⟨a, b, hab⟩ := scanFour_success _ _ _ ht (q v)
        exact ih _ _ _ hab (agrees_update ha v (q v) rfl)
      · by_cases h4 : n % 8 = 4
        · simp only [check, if_neg h0, if_pos h4] at ht
          by_cases hg : good codes p (n / 8) = true
          · exact good_sound codes ha _ hg
          · simp only [if_neg hg] at ht
            cases ht
        · simp only [check, if_neg h0, if_neg h4] at ht
          by_cases hr : rejects p n = true
          · exact (rejects_false ha hq _ hr).elim
          · simp only [if_neg hr] at ht
            cases ht

end SlotTree

namespace SlotTree

open FiniteSlots

abbrev code : Fin 45 → V → Fin 4 := SlotTables.code

def order : List V := [6,4,0,1,9,3,2,8,5,7]

def c0 : Nat := 40285217132025004452164840870658545442554899
def c1 : Nat := 34530186113891079769029748219665682433997835
def c2 : Nat := 4648876938730377
def c3 : Nat := 4067767319680633
def c4 : Nat := 34530186112958088927261770659588168495487243
def c5 : Nat := 34530186113024006758473638588465997062166795
def c6 : Nat := 4067767312922233
def c7 : Nat := 581109719901209
def c8 : Nat := 1162219249280553
def c9 : Nat := 46040248151837298530002109249233043495906715
def c10 : Nat := 40285217131900774693342474389311868528428051
def c11 : Nat := 46040248151829692626400739152248122896697499
def c12 : Nat := 51795279170797731404486006749425816615176483
def c13 : Nat := 4067767309391225
def c14 : Nat := 4067767322383737
def c15 : Nat := 2905548137307481
def c16 : Nat := 290554824149249
def c17 : Nat := 1743328977971257
def c18 : Nat := 5229986571581593
def c19 : Nat := 28775155094923777046131687776702302567537539
def c20 : Nat := 34530186112950483023660402003755128655528715
def c21 : Nat := 46040248150975296121846912535639344936221723
def c22 : Nat := 74815403246690904981617960455383509931728307
def c23 : Nat := 3486657682757993
def c24 : Nat := 77111817
def c25 : Nat := 28775155094906029937728513533841213760383491
def c26 : Nat := 51795279170790125500884636652440896015960611
def c27 : Nat := 51795279170790125500884636652440896016658979
def c28 : Nat := 51795279170790125500884661224080462949354531
def c29 : Nat := 581109622563865
def c30 : Nat := 28775155094923777046131712636572245652675459
def c31 : Nat := 80570434264713276411932965248756244158691395
def c32 : Nat := 80570434265537249302081314359729101242185795
def c33 : Nat := 83447949775113152913663093301513426284775979
def c34 : Nat := 2905548063726937
def c35 : Nat := 46040248151837298530002105718410935636660251
def c36 : Nat := 51795279169852064056715747615909276023203235
def c37 : Nat := 51795279170797731404486006749425816614492451
def c38 : Nat := 5811096214722217
def c39 : Nat := 1162219347666473
def c40 : Nat := 51795279170790125500884635499519391409081379
def c41 : Nat := 74815403246581887029998329628378249825164211
def c42 : Nat := 83447949775113152913663050715475349869365803
def c43 : Nat := 4648876951673737
def c44 : Nat := 5811096370493097
def c45 : Nat := 46040248150909378290635044606761516369542171
def c46 : Nat := 3486657693014377
def c47 : Nat := 89514505
def c48 : Nat := 51795279170797731404486030816662225282343075
def c49 : Nat := 1162220099579945
def c50 : Nat := 3486657683634793
def c51 : Nat := 2926412297
def c52 : Nat := 46040248151829692626400763435657313678359323
def c53 : Nat := 46040248151000649133851477844245219379582619
def c54 : Nat := 80570434265613308338094984488928058994139331
def c55 : Nat := 40285217131999651440160275562052670999194387
def c56 : Nat := 74815403246657946066012023680698428170023475
def c57 : Nat := 74815403246690904981617957356906966301642803
def c58 : Nat := 34530186113049359770478203897071871505548043
def c59 : Nat := 34530186113891079769029748219665682434677771
def c60 : Nat := 46040248150876419375029111362898542465455771
def c61 : Nat := 83447949775138505925667658610119300728177451
def c62 : Nat := 34530186153188248376130350184069586883795339
def c63 : Nat := 69060372227677230781924475537483532468433483
def c64 : Nat := 1162219252830249
def c65 : Nat := 28775155094906029937728516920548133542324995
def c66 : Nat := 69060372227715260299931310674140605382347851
def c67 : Nat := 74815403245562695947414833477805276599747635
def c68 : Nat := 74815403246592028234800155751820599602512947
def c69 : Nat := 28775155094074451143978795046459376456984835
def c70 : Nat := 28775155094786870781307059970100523658406147
def c71 : Nat := 34530186113891079769029745409419514954728331
def c72 : Nat := 34530186113891079769029772142786903025992587
def c73 : Nat := 40285216283393774828176441731842948339034387
def c74 : Nat := 40285217132843906739912276343449475334027283
def c75 : Nat := 74815403245570301851016202565983880667274163
def c76 : Nat := 1743329644982841
def c77 : Nat := 1743332530202681
def c78 : Nat := 1961020394512962
def c79 : Nat := 5229983705274265
def c80 : Nat := 5229986575653017
def c81 : Nat := 290554826893825
def c82 : Nat := 40285217131933733608948407633174842432514835
def c83 : Nat := 40285217132851512643513642909612288073991443
def c84 : Nat := 46040247301558123125716988830041640087681819
def c85 : Nat := 83447949775138505925667615807908442198983467
def c86 : Nat := 1743328882119225
def c87 : Nat := 290555046750738
def c88 : Nat := 435833132552730
def c89 : Nat := 28775155142161509013036450099584039073686915
def c90 : Nat := 34530186113883473865428378122680761835465995
def c91 : Nat := 3486657690344041
def c92 : Nat := 4648876942212233
def c93 : Nat := 28775155094049098131974231395178164885921155
def c94 : Nat := 28775155094819829696912994871288160434789763
def c95 : Nat := 28775155094906029937728516920548133571244547
def c96 : Nat := 28775155094923777046131709682210890098337411
def c97 : Nat := 34530186113883473865428402550205140692983179
def c98 : Nat := 34530186145559527063931375127856322698228363
def c99 : Nat := 40284279733468293337354821317351610650412179
def c100 : Nat := 40285217131933733608948638505706139953621267
def c101 : Nat := 46040247200384393420301336744261498848763291
def c102 : Nat := 46040248151000649133851477844245219373047195
def c103 : Nat := 46040248185110591484817993744765992120450203
def c104 : Nat := 51795279169950940803533549509226018873222563
def c105 : Nat := 51795279170797731404486003939179649135222947
def c106 : Nat := 69060372227677230781924463575922922172396107
def c107 : Nat := 83447949775138505925645470203417577723994283
def c108 : Nat := 1162219346964521
def c109 : Nat := 1743331745220665
def c110 : Nat := 3486661939222889
def c111 : Nat := 290555205863681
def c112 : Nat := 290556841994753
def c113 : Nat := 290557664323841
def c114 : Nat := 3705266697
def c115 : Nat := 843541513
def c116 : Nat := 69060372227715260299931323500392344133520459
def c117 : Nat := 1162222083900969
def c118 : Nat := 28775155094819829696912994871288160463809923
def c119 : Nat := 28775155094906029937728513533841213760287235
def c120 : Nat := 28775155142161509013040230601255238231943555
def c121 : Nat := 34530185190136340274315788137397102847373963
def c122 : Nat := 34530186113883473865428378122680761836160267
def c123 : Nat := 46040248151829692626400737278750677910518555
def c124 : Nat := 46040248151829692626400739152248122897387675
def c125 : Nat := 51795279169885022972321680859772249927290531
def c126 : Nat := 83447949775113152913663073053329501628237099
def c127 : Nat := 1162222951278121
def c128 : Nat := 1525412012632634
def c129 : Nat := 1525413258727994
def c130 : Nat := 1743328878536761
def c131 : Nat := 1743329730941497
def c132 : Nat := 2905548061004889
def c133 : Nat := 3486654819424617
def c134 : Nat := 91450377
def c135 : Nat := 28775155123828746032535796495138717302730243
def c136 : Nat := 28775155124447359525450449478330764637510019
def c137 : Nat := 40285217131933733608949423212905212988844691
def c138 : Nat := 40285217132025004452164840870658545465013267
def c139 : Nat := 40285217132843906739912300338628289963976979
def c140 : Nat := 83447949775138505925667658610119300721615019
def c141 : Nat := 3486661091768937
def c142 : Nat := 4648879796173961
def c143 : Nat := 145284155335178
def c144 : Nat := 928975881
def c145 : Nat := 28774285300896136944925761770190280016512515
def c146 : Nat := 28775095158152050790232613418359330829265283
def c147 : Nat := 28775155094049098131974026679553503132653955
def c148 : Nat := 28775155094906029937729287504458775150234755
def c149 : Nat := 34530185291700506364602533349037762930629003
def c150 : Nat := 34530186113883473865428376249183316849286539
def c151 : Nat := 34530186113891079769029979092196980030873355
def c152 : Nat := 46040248150909378290635252420862721753709339
def c153 : Nat := 46040248151837298530002133028239076011347995
def c154 : Nat := 51795279170790125500881969656770364220598947
def c155 : Nat := 69060372194654932645980596048549799617835339
def c156 : Nat := 69060372227715260299920788680143999047048139
def c157 : Nat := 74815402097755783464762239598600392232481331
def c158 : Nat := 74815403246592028234800155751820599574999603
def c159 : Nat := 80570434265641196651299789146806090538877635
def c160 : Nat := 83447949775138505925667636992841089351012523
def c161 : Nat := 1162220187111465
def c162 : Nat := 1743328699369529
def c163 : Nat := 1743332523993145
def c164 : Nat := 4648874074938249
def c165 : Nat := 4648880559823753
def c166 : Nat := 290554913122561
def c167 : Nat := 581109623459353
def c168 : Nat := 28775155124447359525447150537560520220744067
def c169 : Nat := 40285217131900774693342728392330852224402067
def c170 : Nat := 46040248151837298530002109249233043495230875
def c171 : Nat := 80570434264705670508331596737038392394589635
def c172 : Nat := 80570434265567672916486792730056150574245315
def c173 : Nat := 80570434265641196651300029170651830905692739
def c174 : Nat := 1452793099586090
def c175 : Nat := 2106521481776170
def c176 : Nat := 2905548140770393
def c177 : Nat := 5229986568066969
def c178 : Nat := 581109719166489
def c179 : Nat := 28775155094049098131974026895726285246437763
def c180 : Nat := 28775155094074451143979565774485206134188419
def c181 : Nat := 28775155094074451143979566206830770361755907
def c182 : Nat := 28775155094786870781307059970100523665629443
def c183 : Nat := 28775155094923777046131478809679592577229955
def c184 : Nat := 28775155143023511421191645155853074760975875
def c185 : Nat := 34530185190136340274315787416821162468094603
def c186 : Nat := 34530186113049359770478203897071871528370827
def c187 : Nat := 34530186113883473865429382821714432762439435
def c188 : Nat := 40285217131933733608948662356769766507768467
def c189 : Nat := 40285217132025004452164840870658545465005203
def c190 : Nat := 40285217132025004452164840870658568515962003
def c191 : Nat := 40285217148146984785867462398893617582916755
def c192 : Nat := 46040248150909378290636046639664207795420187
def c193 : Nat := 51795278255054543703214456484616401292322339
def c194 : Nat := 51795279169925587791528984200620144429862563
def c195 : Nat := 74815403246657946066011994425315248770450739
def c196 : Nat := 74815403246690904981617928605926945167580595
def c197 : Nat := 74815403246690904981617957356906966301730867
def c198 : Nat := 80570433287407904961177683194352062775362883
def c199 : Nat := 80570434171419262837535954192359134717878467
def c200 : Nat := 80570434264705670508331355848501523601498307
def c201 : Nat := 80570434265567672916486792730056150546056515
def c202 : Nat := 1452793813680682
def c203 : Nat := 1743328977302073
def c204 : Nat := 1961243936569922
def c205 : Nat := 2106522195870762
def c206 : Nat := 2899346682420569
def c207 : Nat := 5229986578339737
def c208 : Nat := 290554913982977
def c209 : Nat := 3712000521
def c210 : Nat := 28775155094786870781307059970100523665636867
def c211 : Nat := 28775155123828746032535796495138716587236867
def c212 : Nat := 34530186113883473865429382821714432665372427
def c213 : Nat := 34530186113891079769029772142786903048240907
def c214 : Nat := 46040248151829692626401738374904646844076443
def c215 : Nat := 51795279180880624278701343408930594680149539
def c216 : Nat := 80570434216593259627270421066306217944627651
def c217 : Nat := 83447949775138505925667658610119300722373291
def c218 : Nat := 1598051181466682
def c219 : Nat := 1598051689966650
def c220 : Nat := 2033882434315330
def c221 : Nat := 3486661054437993
def c222 : Nat := 726388258905090
def c223 : Nat := 28775154273212375568589759961623925150615043
def c224 : Nat := 28775155001944140820591334825606041636444547
def c225 : Nat := 28775155094074451144771137900542234751691139
def c226 : Nat := 28775155094786870781307059970100530406737411
def c227 : Nat := 28775155094819829696912994871288160463783427
def c228 : Nat := 28775155094906029937728516920548133548887171
def c229 : Nat := 28775155094906029937729287504458775144344707
def c230 : Nat := 28775155094923777046131712636572245681616003
def c231 : Nat := 28775155094923777046132482716079728989234051
def c232 : Nat := 34530186113024006758473638588465997077983883
def c233 : Nat := 34530186113883473865428402550205140708042123
def c234 : Nat := 34530186145904328027193450714817257703293323
def c235 : Nat := 34530186153188248376104857071990096435173771
def c236 : Nat := 34530186154116168615471922867383128167688843
def c237 : Nat := 40285216182349345483984045266009438311605395
def c238 : Nat := 40285216217290866628674961209440505872094355
def c239 : Nat := 40285216284240565429128923039279154748129939
def c240 : Nat := 40285217132843906739913289833509618791130643
def c241 : Nat := 40285217132851512643513669931210052319505939
def c242 : Nat := 46040247201309778358467943486778151810156315
def c243 : Nat := 46040247329464183439142024012527639923621019
def c244 : Nat := 46040248150975296121846912535639344930413595
def c245 : Nat := 46040248151837298530002316342758308575209883
def c246 : Nat := 46040248177481870172619190041511350122645275
def c247 : Nat := 46040248185896534856934176088070524837973787
def c248 : Nat := 51795279170797731404486030816662225304726179
def c249 : Nat := 63305341208721868509841473512310111948705851
def c250 : Nat := 63305341208721868509841489220865612217488315
def c251 : Nat := 63305341208721868509841490806132681051410491
def c252 : Nat := 63305341208739615618244683135449873379578043
def c253 : Nat := 63305341208739615618244683135449873379674299
def c254 : Nat := 63305341208739615618244686522156793161787707
def c255 : Nat := 69060372194654932645979087666933803672351051
def c256 : Nat := 69060372227263976686250070590867786085648587
def c257 : Nat := 69060372227677230781924473808101275558502475
def c258 : Nat := 69060372227715260299920578776372566557005003
def c259 : Nat := 69060372227715260299931323500392344105352267
def c260 : Nat := 69060372227715260299931323500392344111291339
def c261 : Nat := 74815402105141115861691904091720185112968371
def c262 : Nat := 74815403218990204065430659508248204609913907
def c263 : Nat := 74815403246592028234800155751820599580986419
def c264 : Nat := 74815403246690904981587740725423101572625971
def c265 : Nat := 80570434265641196651300029170651830905776707
def c266 : Nat := 80570434265641196651300032125013186460072771
def c267 : Nat := 1162219071604265
def c268 : Nat := 1525387728892474
def c269 : Nat := 1525414694556218
def c270 : Nat := 1525415203056186
def c271 : Nat := 1525427511407162
def c272 : Nat := 1598041874017338
def c273 : Nat := 1598057272224826
def c274 : Nat := 3486661843245417
def c275 : Nat := 3970842583258745
def c276 : Nat := 3977830113949305
def c277 : Nat := 4648876948937865
def c278 : Nat := 28775155094049098131738584111526908560153475
def c279 : Nat := 34530186113891079769029772142786903048221579
def c280 : Nat := 40285216310975316587943040964173755299621523
def c281 : Nat := 40285217131933733608949422420271678571637395
def c282 : Nat := 40285217132851512643514659209918599010368787
def c283 : Nat := 46040248150876419375030112675225293512053915
def c284 : Nat := 46040248151000649133851477844245219401619227
def c285 : Nat := 46040248151829692626398071436001650722036123
def c286 : Nat := 46040248151837298530003109480695884070543387
def c287 : Nat := 69060372194720850477192465850925073170647755
def c288 : Nat := 74815403246592028234800155751820599580966067
def c289 : Nat := 74815403246657946066012025554195873155319091
def c290 : Nat := 80570434265567672916486792730056150552698307
def c291 : Nat := 80570434265641196651300032125013186439197251
def c292 : Nat := 83447949775138505925667658610119300706630315
def c293 : Nat := 1162240498152474
def c294 : Nat := 1888605581149234
def c295 : Nat := 2815610797383001
def c296 : Nat := 3967117014283897
def c297 : Nat := 3980742130554489
def c298 : Nat := 28774313642026812873498420143046895667719683
def c299 : Nat := 28775058989071023752877985006948543014902147
def c300 : Nat := 28775155094074451144771164489794434747099907
def c301 : Nat := 28775155094786870781307059970100530406795779
def c302 : Nat := 28775155094819829696912994871288190077363843
def c303 : Nat := 28775155094906029915527376633152324956118147
def c304 : Nat := 28775155094906029937728516920548140974136451
def c305 : Nat := 28775155094906029938517506934781067900783747
def c306 : Nat := 28775155094923777046131709682210890098253443
def c307 : Nat := 34529248372612352376515627677710068760130187
def c308 : Nat := 34530185198801999777475964326028565966324363
def c309 : Nat := 34530186112950483023660656439119676579070347
def c310 : Nat := 34530186112950483023660656655292458692854155
def c311 : Nat := 34530186113024006758473638588466012532491531
def c312 : Nat := 34530186113049359770478203897071871521370763
def c313 : Nat := 34530186113049359770478203897071894302765707
def c314 : Nat := 34530186113883473863503173805537697503504139
def c315 : Nat := 34530186113883473865426472055203270580735755
def c316 : Nat := 34530186113883473865428402550205140708069131
def c317 : Nat := 34530186145559527063931374407280381531400459
def c318 : Nat := 34530186145559527063931375127856321910700683
def c319 : Nat := 34530186145919539834396189467635218141757835
def c320 : Nat := 34530227344112763664300793289103049280805259
def c321 : Nat := 40285217131900774693342728608503634338185875
def c322 : Nat := 40285217132843906739913289833509618784509459
def c323 : Nat := 40285217132851512643513876592389753096826387
def c324 : Nat := 40285217149652953698963449646500342537585299
def c325 : Nat := 40285217156587002482212061550207002803923603
def c326 : Nat := 40285217157038286095868262700415553493326995
def c327 : Nat := 40285217157038286095893324043391567896183827
def c328 : Nat := 46039406012733176141646659226458406191987867
def c329 : Nat := 46040247200376787516700968680179269676123035
def c330 : Nat := 46040248150909378290636045558800297226501275
def c331 : Nat := 46040248151837298530002133028239076033481115
def c332 : Nat := 51794341574086949064400080071760223411312163
def c333 : Nat := 51795278295414003513280318036927915516962595
def c334 : Nat := 51795279169885022972321175447807667900746787
def c335 : Nat := 51795279169885022972577834221477225747156003
def c336 : Nat := 51795279169950940803533549509226018895521315
def c337 : Nat := 51795279170790125500884908237512824967049891
def c338 : Nat := 51795279188509345590899705110903408040578851
def c339 : Nat := 51795279189629948721476582017484899054259747
def c340 : Nat := 69060372194720850477190955811984414352820939
def c341 : Nat := 69060372227715260299931323500392344105325771
def c342 : Nat := 74815403141240122151031907341187667213485875
def c343 : Nat := 74815403218990204065432339242822822748030003
def c344 : Nat := 74815403219056121896644209045198096300842803
def c345 : Nat := 74815403245562695947414275103509076696171571
def c346 : Nat := 74815403246657946066012023680698428170076723
def c347 : Nat := 74815403246690904981587950629194534062667827
def c348 : Nat := 74815409928510177700221037643315672874026035
def c349 : Nat := 80570434264705670508330428827554225658601923
def c350 : Nat := 80570434264705670508330429043727007772385731
def c351 : Nat := 83447949765993674495621190738962218761004843
def c352 : Nat := 83447949775113152913663093301513426278986283

set_option maxRecDepth 32000 in
set_option maxHeartbeats 8000000 in
def treeData : List ℕ := [
  0,
  0,
  0,
  0,
  0,
  c26,
  0,
  c29,
  0,
  c8,
  c10,
  c0,
  c8,
  c315,
  c29,
  0,
  c29,
  0,
  c8,
  c10,
  c0,
  c8,
  c315,
  c29,
  c26,
  0,
  c26,
  c76,
  0,
  0,
  c24,
  c20,
  0,
  c11,
  c245,
  c264,
  c11,
  c24,
  0,
  c122,
  c20,
  c152,
  c20,
  0,
  c122,
  c20,
  c84,
  c20,
  0,
  c24,
  c20,
  0,
  c294,
  0,
  c119,
  290556748466689,
  c14,
  290556748466689,
  c264,
  c294,
  c24,
  c76,
  0,
  c26,
  0,
  c233,
  0,
  c242,
  c58,
  c189,
  c58,
  c316,
  c233,
  0,
  c233,
  0,
  c242,
  c6,
  c138,
  c6,
  c316,
  c233,
  c26,
  0,
  c26,
  c76,
  0,
  c29,
  0,
  c8,
  c6,
  c0,
  c8,
  0,
  c8,
  c6,
  c84,
  c8,
  c29,
  c76,
  0,
  c150,
  c69,
  c97,
  c69,
  0,
  0,
  0,
  0,
  c16,
  0,
  c11,
  0,
  0,
  c111,
  c210,
  c131,
  c111,
  c49,
  0,
  c182,
  c210,
  c247,
  c182,
  c49,
  0,
  c107,
  c30,
  c140,
  c30,
  c11,
  0,
  c11,
  0,
  0,
  180,
  c86,
  c131,
  c86,
  c49,
  0,
  c108,
  c86,
  c247,
  c108,
  c49,
  0,
  c107,
  c30,
  c140,
  c30,
  c11,
  c16,
  0,
  c90,
  c10,
  c0,
  c90,
  c40,
  c40,
  c37,
  0,
  0,
  c16,
  0,
  c11,
  0,
  0,
  c111,
  c144,
  c136,
  c111,
  c49,
  0,
  c182,
  c144,
  34530218951327728683122963588519954038815371,
  c144,
  c49,
  0,
  c107,
  c30,
  c140,
  c30,
  c11,
  0,
  c11,
  0,
  0,
  c252,
  c128,
  c128,
  c136,
  c49,
  0,
  c108,
  c299,
  46040283062851163875824760733867151773236379,
  c108,
  c49,
  0,
  c107,
  c30,
  c140,
  c30,
  c11,
  c16,
  0,
  c90,
  c10,
  c0,
  c90,
  0,
  c90,
  0,
  c224,
  c15,
  0,
  c85,
  4648874290158473,
  c61,
  4648874290158473,
  c15,
  c21,
  c90,
  0,
  c16,
  c10,
  c0,
  c16,
  c37,
  c70,
  0,
  0,
  0,
  c154,
  c100,
  c73,
  c154,
  0,
  c242,
  0,
  c124,
  0,
  0,
  c191,
  5229987708377241,
  c131,
  c131,
  c127,
  c137,
  c127,
  c196,
  c124,
  c45,
  c45,
  c40,
  c40,
  c37,
  0,
  0,
  0,
  c11,
  c35,
  c347,
  c35,
  c6,
  c73,
  c6,
  0,
  c242,
  c6,
  c138,
  c6,
  0,
  46040248150975296121846912535639344930408219,
  c6,
  c21,
  c6,
  0,
  0,
  c91,
  c15,
  c347,
  c15,
  c6,
  c73,
  c6,
  c37,
  c70,
  0,
  c150,
  0,
  c26,
  c76,
  0,
  0,
  c24,
  c20,
  0,
  c11,
  c245,
  c264,
  c11,
  c24,
  0,
  c4,
  c20,
  c152,
  c4,
  0,
  c4,
  c20,
  c84,
  c4,
  0,
  c24,
  c20,
  0,
  c294,
  c15,
  c264,
  c15,
  c24,
  c76,
  c97,
  0,
  c26,
  c76,
  0,
  c29,
  0,
  c8,
  c6,
  c0,
  c8,
  0,
  c8,
  c6,
  c84,
  c8,
  c29,
  c76,
  0,
  0,
  0,
  c27,
  0,
  0,
  c130,
  c318,
  34530218580725005103999182333106617655051019,
  c130,
  0,
  c317,
  c318,
  c0,
  c317,
  c125,
  c125,
  c63,
  c27,
  0,
  c27,
  c77,
  c63,
  c77,
  0,
  c27,
  0,
  0,
  0,
  0,
  0,
  c74,
  76,
  c257,
  c74,
  0,
  c74,
  68,
  c257,
  c74,
  0,
  c74,
  60,
  c257,
  c74,
  0,
  c74,
  84,
  c257,
  c74,
  c35,
  c57,
  c35,
  c87,
  c87,
  c58,
  0,
  c88,
  c58,
  c189,
  c88,
  c125,
  c125,
  c63,
  c27,
  0,
  c27,
  c77,
  c63,
  c77,
  0,
  c150,
  0,
  c255,
  0,
  0,
  c143,
  c98,
  0,
  46040248151829692627425924015788847018367387,
  c286,
  c57,
  c286,
  c143,
  0,
  c4,
  c98,
  c330,
  c4,
  0,
  c4,
  c98,
  c243,
  c4,
  0,
  c143,
  c98,
  0,
  c221,
  0,
  3977919630235001,
  0,
  2905553035711577,
  c177,
  c126,
  2905553035711577,
  c14,
  c14,
  c57,
  c221,
  c143,
  c155,
  0,
  0,
  c143,
  c98,
  c3,
  c3,
  0,
  c4,
  c98,
  c330,
  c4,
  0,
  c4,
  c98,
  c243,
  c4,
  0,
  c143,
  c98,
  c3,
  c3,
  c97,
  0,
  c255,
  0,
  0,
  0,
  c285,
  c35,
  c57,
  c35,
  c87,
  c87,
  0,
  c285,
  c35,
  c57,
  c35,
  0,
  c88,
  c10,
  c0,
  c88,
  0,
  c88,
  0,
  c221,
  0,
  c13,
  0,
  c132,
  5229988497184665,
  c126,
  c132,
  3970831009420665,
  c13,
  c57,
  c221,
  c243,
  c88,
  0,
  0,
  c91,
  0,
  c175,
  0,
  c74,
  c83,
  c126,
  c74,
  c174,
  0,
  c167,
  c83,
  1670689995108938,
  c167,
  c57,
  c91,
  c87,
  c87,
  0,
  c91,
  0,
  c13,
  0,
  c132,
  c177,
  c126,
  c132,
  c14,
  c13,
  c57,
  c91,
  c155,
  0,
  0,
  0,
  c285,
  c35,
  c57,
  c35,
  c6,
  c3,
  c3,
  0,
  c88,
  c6,
  c0,
  c6,
  0,
  c88,
  c6,
  c243,
  c6,
  0,
  0,
  c91,
  0,
  c175,
  0,
  c74,
  c178,
  1452774282496554,
  c178,
  c174,
  0,
  c167,
  c178,
  44,
  c167,
  c57,
  c91,
  c6,
  c3,
  c3,
  0,
  0,
  c106,
  c12,
  c63,
  c12,
  0,
  c106,
  c12,
  c63,
  c12,
  0,
  c106,
  c12,
  c63,
  c12,
  0,
  c106,
  c12,
  c63,
  c12,
  0,
  c150,
  0,
  c27,
  c77,
  c155,
  c77,
  c97,
  0,
  c27,
  c77,
  c155,
  c77,
  0,
  0,
  0,
  0,
  0,
  c130,
  0,
  0,
  0,
  c81,
  308,
  c112,
  c81,
  c19,
  0,
  c218,
  c250,
  c269,
  c187,
  c19,
  0,
  0,
  c81,
  316,
  c112,
  c81,
  c19,
  0,
  c218,
  c250,
  c269,
  c187,
  c19,
  0,
  0,
  c81,
  300,
  c112,
  c81,
  c19,
  0,
  c218,
  c250,
  c269,
  c187,
  c19,
  0,
  0,
  c81,
  324,
  c112,
  c81,
  c19,
  0,
  c218,
  c250,
  c269,
  c187,
  c19,
  0,
  c123,
  0,
  0,
  c211,
  c162,
  c112,
  c112,
  c19,
  0,
  c108,
  c162,
  c314,
  c108,
  c19,
  0,
  0,
  c211,
  c162,
  c112,
  c112,
  c19,
  0,
  c324,
  c162,
  c314,
  c162,
  c19,
  c123,
  c130,
  0,
  c90,
  c10,
  c0,
  c90,
  c28,
  c28,
  80677897,
  0,
  0,
  c130,
  0,
  c56,
  0,
  0,
  c81,
  c144,
  c168,
  c81,
  c19,
  0,
  c187,
  c144,
  c319,
  c144,
  c19,
  0,
  0,
  c81,
  c144,
  c168,
  c81,
  c19,
  0,
  c187,
  c144,
  c141,
  c144,
  c19,
  c56,
  0,
  c123,
  0,
  0,
  c211,
  c234,
  c168,
  c168,
  c19,
  0,
  c108,
  c234,
  c319,
  c108,
  c19,
  0,
  0,
  c211,
  c234,
  c168,
  c168,
  c19,
  0,
  c324,
  c234,
  c141,
  c141,
  c19,
  c123,
  c130,
  0,
  c90,
  c10,
  c0,
  c90,
  c194,
  c194,
  80677897,
  c80,
  0,
  0,
  0,
  c232,
  c312,
  c55,
  c232,
  0,
  c232,
  c312,
  0,
  0,
  0,
  c211,
  c305,
  c112,
  c112,
  c306,
  0,
  c92,
  34530186113883473865428402550205156911164683,
  34530186113883473865428402550205156911605515,
  c92,
  c306,
  0,
  0,
  2905551140167001,
  c305,
  c112,
  c112,
  28775155142161509013036450099584038343384451,
  c14,
  c14,
  c196,
  c196,
  c232,
  c28,
  c28,
  2581692937,
  0,
  0,
  51795279169925587791528984200620137732747811,
  c6,
  c55,
  c6,
  0,
  c287,
  c6,
  c138,
  c6,
  c194,
  c194,
  2581692937,
  c80,
  0,
  c93,
  0,
  0,
  0,
  c4,
  0,
  c195,
  0,
  c42,
  c96,
  c33,
  c96,
  0,
  0,
  c47,
  c180,
  c113,
  c113,
  c50,
  0,
  c212,
  c180,
  c181,
  c181,
  c50,
  c195,
  0,
  c123,
  0,
  c42,
  c96,
  c33,
  c96,
  0,
  0,
  c135,
  c162,
  c113,
  c113,
  c50,
  0,
  51795279170790125500884661224080457005388451,
  c162,
  c181,
  c162,
  c50,
  c123,
  c4,
  0,
  c4,
  0,
  c195,
  0,
  c42,
  c89,
  c33,
  c89,
  0,
  0,
  c47,
  c180,
  c113,
  c113,
  c50,
  0,
  c212,
  c180,
  c181,
  c181,
  c50,
  c195,
  0,
  c262,
  0,
  c42,
  c89,
  c14,
  c14,
  0,
  0,
  c135,
  c180,
  c113,
  c113,
  c50,
  0,
  c164,
  c180,
  c181,
  c164,
  c50,
  c262,
  c4,
  c28,
  c28,
  c166,
  0,
  0,
  c4,
  0,
  c56,
  0,
  c42,
  c96,
  c33,
  c96,
  0,
  0,
  c47,
  c114,
  284,
  c47,
  c50,
  0,
  c212,
  c114,
  c141,
  c114,
  c50,
  c56,
  0,
  c123,
  0,
  c42,
  c96,
  c33,
  c96,
  0,
  0,
  c273,
  c268,
  c254,
  c135,
  c50,
  0,
  83447948986429120174466931391070220908694699,
  c298,
  c141,
  c141,
  c50,
  c123,
  c4,
  0,
  c4,
  0,
  c56,
  0,
  c42,
  c89,
  c33,
  c89,
  0,
  0,
  c47,
  c114,
  276,
  c47,
  c50,
  0,
  c212,
  c114,
  c141,
  c114,
  c50,
  c56,
  0,
  c56,
  0,
  c42,
  3980750176597625,
  c14,
  c14,
  0,
  0,
  c273,
  c268,
  c254,
  c135,
  c50,
  0,
  c164,
  c298,
  c141,
  c141,
  c50,
  c56,
  c4,
  0,
  c4,
  0,
  c56,
  0,
  c42,
  c96,
  c33,
  c96,
  0,
  0,
  c47,
  c114,
  236,
  c47,
  c50,
  c266,
  c50,
  c56,
  0,
  c52,
  0,
  c42,
  c96,
  c33,
  c96,
  0,
  0,
  c273,
  c268,
  c254,
  c135,
  c50,
  c266,
  c50,
  c52,
  c4,
  0,
  c4,
  0,
  c56,
  0,
  c42,
  c89,
  c33,
  c89,
  0,
  0,
  c47,
  c114,
  292,
  c47,
  c50,
  c266,
  c50,
  c56,
  0,
  c56,
  0,
  c42,
  3980750176597625,
  c14,
  c14,
  0,
  0,
  c273,
  c268,
  c254,
  c135,
  c50,
  c266,
  c50,
  c56,
  c4,
  c166,
  c97,
  c93,
  0,
  c94,
  0,
  0,
  c104,
  0,
  c122,
  0,
  c195,
  0,
  c38,
  c120,
  c352,
  c38,
  0,
  c38,
  c348,
  c217,
  c38,
  c195,
  0,
  c262,
  0,
  c38,
  c120,
  c14,
  c14,
  0,
  c38,
  c348,
  c217,
  c38,
  c262,
  c122,
  c28,
  c28,
  c166,
  0,
  c104,
  0,
  c122,
  0,
  c56,
  0,
  c95,
  c120,
  0,
  581113285321753,
  c114,
  28775155094819829696912994871318514437793155,
  c114,
  c120,
  0,
  c95,
  c230,
  c61,
  c95,
  c56,
  0,
  c56,
  0,
  c95,
  c120,
  c14,
  c14,
  0,
  c95,
  c230,
  c61,
  c95,
  c56,
  c122,
  0,
  c122,
  0,
  c56,
  0,
  c95,
  c17,
  0,
  c212,
  c114,
  c302,
  c114,
  c17,
  0,
  c95,
  c230,
  c61,
  c95,
  c56,
  0,
  c52,
  0,
  c95,
  c17,
  0,
  c117,
  28775155094819829696912994871288190076923395,
  c302,
  c117,
  c17,
  0,
  c95,
  c230,
  c61,
  c95,
  c52,
  c122,
  c104,
  c166,
  0,
  0,
  c104,
  0,
  c340,
  69060372194746203489195520400014348416928459,
  0,
  0,
  c38,
  c54,
  0,
  c92,
  c325,
  c176,
  c176,
  c38,
  0,
  c38,
  c280,
  c14,
  c14,
  c196,
  c196,
  c340,
  c28,
  c28,
  0,
  c48,
  0,
  0,
  c91,
  c206,
  c57,
  c206,
  c238,
  c189,
  0,
  c91,
  c206,
  c57,
  c206,
  c338,
  c48,
  0,
  c104,
  0,
  c287,
  c6,
  c138,
  c6,
  0,
  c287,
  c6,
  0,
  c52,
  0,
  69060372227677230781924475537483532446902859,
  c17,
  0,
  c117,
  581112503845913,
  46040283062851163901775462530677257418407067,
  581112503845913,
  c17,
  c196,
  c52,
  c6,
  c104,
  0,
  c48,
  0,
  0,
  c91,
  c206,
  c57,
  c206,
  c6,
  c138,
  c6,
  c28,
  c48,
  c94,
  0,
  c150,
  c80,
  c97,
  c80,
  0,
  0,
  0,
  c106,
  80677897,
  c63,
  80677897,
  c80,
  0,
  c106,
  2581692937,
  c63,
  2581692937,
  c80,
  0,
  c93,
  c69,
  c97,
  c69,
  0,
  c94,
  c70,
  0,
  c106,
  0,
  0,
  0,
  c11,
  c35,
  c57,
  c35,
  c87,
  c87,
  0,
  c11,
  c35,
  c57,
  c35,
  0,
  c88,
  c238,
  c189,
  c88,
  0,
  c88,
  0,
  c221,
  c15,
  c57,
  c15,
  c21,
  c88,
  0,
  0,
  c91,
  c15,
  c57,
  c15,
  c87,
  c87,
  0,
  c91,
  c15,
  c57,
  c15,
  c63,
  0,
  0,
  0,
  c11,
  c35,
  c57,
  c35,
  c6,
  c3,
  c3,
  0,
  c88,
  c6,
  c138,
  c6,
  0,
  c88,
  c6,
  c21,
  c6,
  0,
  0,
  c91,
  c15,
  c57,
  c15,
  c6,
  c3,
  c3,
  c70,
  0,
  c150,
  c80,
  c97,
  c80,
  0,
  0,
  0,
  c71,
  0,
  c26,
  0,
  c105,
  0,
  0,
  c209,
  c310,
  46040248150876419375242181200897865020674075,
  c209,
  c20,
  c152,
  c20,
  0,
  0,
  0,
  c119,
  0,
  260,
  252,
  244,
  268,
  c173,
  c119,
  c204,
  c204,
  c153,
  c20,
  c84,
  c20,
  c105,
  c157,
  c26,
  c72,
  0,
  c26,
  c75,
  c157,
  c26,
  0,
  0,
  0,
  0,
  c16,
  c1,
  0,
  c11,
  0,
  c25,
  c183,
  c33,
  c25,
  0,
  c25,
  c134,
  0,
  c278,
  c86,
  34530227344112763638170488659729348634433931,
  c86,
  c134,
  c11,
  c16,
  0,
  0,
  c115,
  0,
  c175,
  0,
  340,
  c83,
  c126,
  c83,
  c174,
  c25,
  0,
  c25,
  c134,
  c236,
  c134,
  c115,
  c1,
  c0,
  c1,
  c40,
  c40,
  0,
  c105,
  0,
  0,
  c115,
  0,
  c175,
  0,
  348,
  c83,
  c126,
  c83,
  c174,
  c25,
  c197,
  c115,
  c1,
  c0,
  c1,
  0,
  0,
  c147,
  c179,
  c197,
  c147,
  c1,
  c21,
  c1,
  c105,
  0,
  0,
  c16,
  c1,
  0,
  c11,
  0,
  c25,
  c183,
  c33,
  c25,
  0,
  c25,
  c134,
  0,
  c278,
  28775155094049098131738586201197135660063107,
  c110,
  c110,
  c134,
  c11,
  c16,
  0,
  0,
  c115,
  0,
  c175,
  0,
  332,
  c83,
  c126,
  c83,
  c174,
  c25,
  0,
  c25,
  c134,
  c236,
  c134,
  c115,
  c1,
  c0,
  c1,
  0,
  0,
  c147,
  c179,
  c32,
  c147,
  c1,
  c21,
  c1,
  0,
  c16,
  c1,
  c0,
  c16,
  0,
  c105,
  0,
  0,
  c115,
  0,
  c175,
  0,
  356,
  c83,
  c126,
  c83,
  c174,
  c25,
  c197,
  c115,
  c1,
  c0,
  c1,
  c40,
  c105,
  c69,
  0,
  0,
  0,
  c5,
  c82,
  c55,
  c5,
  0,
  c2,
  0,
  c7,
  0,
  c25,
  c186,
  c137,
  c25,
  0,
  c25,
  c51,
  0,
  c249,
  c129,
  c129,
  c149,
  c51,
  c7,
  c45,
  c2,
  c40,
  c40,
  c75,
  0,
  0,
  c5,
  c82,
  c55,
  c5,
  0,
  c2,
  0,
  c7,
  0,
  c25,
  c186,
  c137,
  c25,
  0,
  c25,
  c51,
  0,
  108,
  c46,
  c110,
  c46,
  c51,
  c7,
  c45,
  c2,
  0,
  c5,
  0,
  c62,
  c31,
  c32,
  c62,
  c21,
  c5,
  0,
  c2,
  c82,
  c55,
  c2,
  c75,
  c69,
  0,
  0,
  0,
  0,
  c16,
  c1,
  0,
  c11,
  0,
  0,
  188,
  c86,
  c131,
  c86,
  c49,
  c265,
  c49,
  0,
  c107,
  c30,
  c140,
  c30,
  c11,
  c16,
  0,
  0,
  c115,
  0,
  c228,
  c127,
  c301,
  c127,
  0,
  c228,
  c30,
  c236,
  c30,
  c115,
  c1,
  c0,
  c1,
  c40,
  c40,
  c37,
  0,
  0,
  c16,
  c1,
  0,
  c11,
  0,
  0,
  c252,
  c128,
  c128,
  c136,
  c49,
  c265,
  c49,
  0,
  c107,
  c30,
  c140,
  c30,
  c11,
  c16,
  0,
  0,
  c115,
  0,
  c228,
  c127,
  c301,
  c127,
  0,
  c228,
  c30,
  c236,
  c30,
  c115,
  c1,
  c0,
  c1,
  0,
  0,
  c224,
  c15,
  c32,
  c15,
  c1,
  c21,
  c1,
  0,
  c16,
  c1,
  c0,
  c16,
  c37,
  c70,
  0,
  0,
  0,
  c154,
  c100,
  c73,
  c154,
  0,
  c2,
  0,
  c7,
  0,
  0,
  c191,
  40285217132851512643513646440434395933228691,
  c131,
  c131,
  c127,
  c137,
  c127,
  0,
  c85,
  c99,
  c61,
  c99,
  c7,
  c45,
  c2,
  c40,
  c40,
  c37,
  0,
  0,
  c261,
  c100,
  c73,
  c261,
  0,
  c2,
  0,
  c7,
  0,
  0,
  c191,
  c46,
  46040248151837298530239371703854659976358299,
  c46,
  c127,
  c137,
  c127,
  0,
  c85,
  c99,
  c61,
  c99,
  c7,
  c45,
  c2,
  0,
  c244,
  0,
  c346,
  c15,
  c32,
  c15,
  c21,
  c21,
  0,
  c2,
  c100,
  c73,
  c2,
  c37,
  c70,
  0,
  c71,
  0,
  c26,
  c37,
  c157,
  c37,
  c72,
  0,
  c26,
  c37,
  c157,
  c37,
  0,
  0,
  c71,
  0,
  c27,
  0,
  51795279169852064056715241483368753617381155,
  0,
  c60,
  c20,
  0,
  c246,
  c9,
  c197,
  c9,
  c20,
  c334,
  c334,
  c67,
  c27,
  c72,
  0,
  c27,
  c75,
  c67,
  c27,
  0,
  0,
  0,
  0,
  c151,
  c1,
  c3,
  c3,
  0,
  c101,
  c1,
  c0,
  c1,
  0,
  c102,
  c1,
  0,
  c235,
  c31,
  c32,
  c235,
  c1,
  0,
  c151,
  c1,
  c3,
  c3,
  0,
  0,
  c151,
  c1,
  c239,
  c1,
  0,
  c101,
  c1,
  c0,
  c1,
  0,
  c102,
  c1,
  0,
  c274,
  c31,
  c197,
  c274,
  c1,
  0,
  c151,
  c1,
  c239,
  c1,
  0,
  0,
  c151,
  c1,
  0,
  c123,
  c170,
  0,
  40285217131999651440160275562052670993378067,
  c134,
  0,
  34530227343511897253662307923419911315085579,
  c177,
  c110,
  c110,
  c134,
  c123,
  c1,
  0,
  c101,
  c1,
  c0,
  c1,
  0,
  c102,
  c1,
  0,
  c235,
  c31,
  c32,
  c235,
  c1,
  0,
  c151,
  c1,
  c0,
  c1,
  0,
  0,
  c151,
  c1,
  c3,
  c3,
  0,
  c101,
  c1,
  c0,
  c1,
  0,
  c102,
  c1,
  0,
  c274,
  c31,
  c197,
  c274,
  c1,
  0,
  c151,
  c1,
  c3,
  c3,
  0,
  0,
  0,
  c4,
  c59,
  c3,
  c3,
  0,
  c4,
  c59,
  0,
  c246,
  c9,
  c34,
  c34,
  c4,
  0,
  c4,
  c59,
  0,
  c52,
  c31,
  c34,
  c34,
  c4,
  0,
  c4,
  c59,
  c3,
  c3,
  0,
  74815403245562695947414274166760354203109171,
  0,
  c4,
  c59,
  0,
  c246,
  c9,
  c34,
  c34,
  c4,
  c345,
  c345,
  c67,
  c67,
  0,
  0,
  0,
  c5,
  c188,
  c3,
  c3,
  0,
  c2,
  0,
  c7,
  c9,
  0,
  0,
  c47,
  c149,
  c313,
  c47,
  c51,
  0,
  c249,
  c129,
  c129,
  c149,
  c51,
  c7,
  0,
  c7,
  c9,
  0,
  0,
  c279,
  c39,
  c213,
  c39,
  c51,
  0,
  c164,
  c39,
  c320,
  c39,
  c51,
  c7,
  c2,
  0,
  c5,
  0,
  c62,
  c31,
  c32,
  c62,
  0,
  c62,
  c31,
  c32,
  c62,
  c5,
  0,
  c2,
  c188,
  c3,
  c3,
  c75,
  0,
  0,
  c5,
  c82,
  c55,
  c5,
  0,
  c2,
  0,
  c7,
  c9,
  0,
  0,
  c47,
  c46,
  c213,
  c47,
  c51,
  0,
  36,
  c46,
  c110,
  c46,
  c51,
  c7,
  0,
  c7,
  c9,
  0,
  0,
  c279,
  c241,
  c213,
  c279,
  c51,
  0,
  c164,
  c241,
  c110,
  c110,
  c51,
  c7,
  c2,
  0,
  c5,
  0,
  c62,
  c31,
  c32,
  c62,
  0,
  c62,
  c31,
  c32,
  c62,
  c5,
  0,
  c2,
  c82,
  c55,
  c2,
  c75,
  0,
  0,
  0,
  0,
  c64,
  c35,
  c34,
  c64,
  c169,
  c3,
  c3,
  0,
  c2,
  c10,
  c0,
  c2,
  0,
  c102,
  0,
  0,
  c13,
  4648879689653385,
  c173,
  c13,
  c31,
  c34,
  c34,
  0,
  c52,
  c31,
  c34,
  c34,
  c102,
  0,
  c2,
  c169,
  c3,
  c3,
  c75,
  c67,
  c75,
  0,
  0,
  0,
  c36,
  0,
  c60,
  c1,
  c0,
  c1,
  0,
  c53,
  c1,
  0,
  c52,
  c31,
  c32,
  c52,
  c1,
  c36,
  c12,
  0,
  c36,
  0,
  c60,
  c1,
  c0,
  c1,
  0,
  c53,
  c1,
  0,
  c52,
  c31,
  c32,
  c52,
  c1,
  c36,
  c12,
  0,
  0,
  c36,
  0,
  c60,
  c59,
  0,
  c246,
  c9,
  0,
  c65,
  290557992716545,
  c61,
  290557992716545,
  c9,
  c59,
  0,
  c53,
  c59,
  0,
  c52,
  c31,
  c32,
  c52,
  c59,
  c36,
  c12,
  c67,
  c12,
  0,
  0,
  c36,
  0,
  c2,
  0,
  c7,
  c9,
  0,
  c85,
  c99,
  c61,
  c99,
  c7,
  0,
  c7,
  c9,
  0,
  c85,
  c190,
  c61,
  c190,
  c7,
  c2,
  0,
  c53,
  0,
  c193,
  c31,
  c32,
  c193,
  0,
  c52,
  c31,
  c32,
  c52,
  c53,
  c36,
  c12,
  0,
  c36,
  0,
  c2,
  0,
  c7,
  c9,
  0,
  c85,
  c99,
  c61,
  c99,
  c7,
  0,
  c7,
  c9,
  0,
  c85,
  c190,
  c61,
  c190,
  c7,
  c2,
  0,
  c53,
  0,
  c193,
  c31,
  c32,
  c193,
  0,
  c52,
  c31,
  c32,
  c52,
  c53,
  c36,
  c12,
  0,
  0,
  c36,
  0,
  c2,
  c10,
  c0,
  c2,
  0,
  c53,
  0,
  c193,
  c31,
  c32,
  c193,
  0,
  c52,
  c31,
  c32,
  c52,
  c53,
  c36,
  c12,
  c67,
  c12,
  0,
  c71,
  0,
  c27,
  c12,
  c67,
  c12,
  c72,
  0,
  c27,
  c12,
  c67,
  c12,
  0,
  0,
  c71,
  0,
  0,
  c333,
  0,
  c185,
  c121,
  0,
  c297,
  c349,
  80570434138802612893662684670901663300657603,
  c297,
  c185,
  c28,
  c28,
  c23,
  c67,
  c23,
  c72,
  0,
  0,
  c333,
  0,
  c2,
  c10,
  c0,
  c2,
  c28,
  c28,
  c23,
  c67,
  c23,
  0,
  c93,
  0,
  0,
  0,
  c4,
  c59,
  0,
  c223,
  0,
  c42,
  4648880478460809,
  c33,
  4648880478460809,
  c34,
  c34,
  c4,
  0,
  c4,
  c59,
  0,
  c223,
  c350,
  c34,
  c34,
  c4,
  c28,
  c28,
  0,
  c48,
  0,
  c4,
  c59,
  0,
  c223,
  c350,
  c34,
  c34,
  c4,
  0,
  c4,
  c59,
  0,
  c223,
  c31,
  c34,
  c34,
  c4,
  c48,
  c67,
  c67,
  0,
  0,
  0,
  c5,
  c82,
  c55,
  c5,
  0,
  c2,
  0,
  c7,
  0,
  c42,
  c89,
  c137,
  c89,
  0,
  0,
  c47,
  28775155094906029938517504340707021685435139,
  c113,
  c113,
  c51,
  0,
  c249,
  c129,
  c129,
  c149,
  c51,
  c7,
  0,
  c7,
  0,
  c42,
  c89,
  c14,
  c14,
  0,
  0,
  c135,
  28775155094906029938517506934780407050841219,
  c113,
  c113,
  c51,
  0,
  c164,
  c325,
  c320,
  c164,
  c51,
  c7,
  c2,
  c28,
  c28,
  c75,
  0,
  0,
  c5,
  c82,
  c55,
  c5,
  0,
  c2,
  0,
  c7,
  0,
  c42,
  c89,
  c137,
  c89,
  0,
  0,
  c47,
  c46,
  c213,
  c47,
  c51,
  0,
  100,
  c46,
  c110,
  c46,
  c51,
  c7,
  0,
  c7,
  0,
  c42,
  c89,
  c14,
  c14,
  0,
  0,
  c135,
  c241,
  c213,
  c135,
  c51,
  0,
  c164,
  c241,
  c110,
  c110,
  c51,
  c7,
  c2,
  0,
  c5,
  0,
  c62,
  c31,
  c32,
  c62,
  0,
  c62,
  c31,
  c32,
  c62,
  c5,
  0,
  c2,
  c82,
  c55,
  c2,
  c75,
  c93,
  0,
  c94,
  0,
  0,
  c104,
  0,
  0,
  c209,
  0,
  c38,
  c120,
  c352,
  c38,
  c118,
  c209,
  c59,
  0,
  c227,
  0,
  c38,
  c120,
  c14,
  c14,
  c118,
  c118,
  c59,
  c28,
  c28,
  0,
  c48,
  0,
  0,
  c209,
  0,
  c65,
  c120,
  83447949775113152913663093301513426278992555,
  c120,
  c118,
  c209,
  c59,
  0,
  c227,
  0,
  c65,
  c120,
  c14,
  c14,
  c118,
  c118,
  c59,
  0,
  0,
  c227,
  c153,
  c118,
  c118,
  c59,
  0,
  c227,
  c31,
  c118,
  c118,
  c59,
  c48,
  c67,
  c67,
  0,
  0,
  c104,
  0,
  c2,
  0,
  c7,
  0,
  c38,
  c281,
  c137,
  c38,
  0,
  c38,
  c275,
  c217,
  c275,
  c7,
  0,
  c7,
  0,
  c38,
  c280,
  c14,
  c14,
  0,
  c38,
  40285217132025004452164840870682172606034963,
  c217,
  c38,
  c7,
  c2,
  c28,
  c28,
  c75,
  0,
  c104,
  0,
  c2,
  0,
  c7,
  0,
  0,
  c191,
  c46,
  c207,
  c46,
  c281,
  c137,
  c281,
  0,
  c85,
  c99,
  c61,
  c99,
  c7,
  0,
  c7,
  0,
  83447949739413576710035654814928352465077035,
  c280,
  c14,
  c14,
  0,
  c85,
  c190,
  c61,
  c190,
  c7,
  c2,
  0,
  0,
  c267,
  c153,
  c32,
  c267,
  0,
  c336,
  c31,
  c32,
  c336,
  0,
  c52,
  c31,
  c32,
  c52,
  0,
  c267,
  c153,
  c32,
  c267,
  c104,
  c75,
  c94,
  0,
  c71,
  0,
  0,
  c104,
  0,
  c4,
  c121,
  0,
  c297,
  c349,
  c34,
  c34,
  c4,
  c28,
  c28,
  c23,
  c67,
  c23,
  c72,
  0,
  0,
  c104,
  0,
  c2,
  c10,
  c0,
  c2,
  c28,
  c28,
  c23,
  c67,
  c23,
  0,
  0,
  c71,
  0,
  0,
  0,
  c24,
  c121,
  c3,
  c24,
  0,
  c185,
  c121,
  c152,
  c185,
  0,
  c185,
  c121,
  c84,
  c185,
  0,
  c24,
  c121,
  c3,
  c24,
  c23,
  c157,
  c23,
  c72,
  0,
  0,
  c29,
  0,
  c8,
  c10,
  c0,
  c8,
  0,
  c8,
  0,
  0,
  c119,
  c19,
  c173,
  c119,
  c204,
  c204,
  0,
  c119,
  c208,
  0,
  c218,
  c129,
  c129,
  92,
  c208,
  c84,
  c8,
  c29,
  c23,
  c157,
  c23,
  0,
  c93,
  c69,
  0,
  0,
  0,
  c5,
  c188,
  c3,
  c3,
  0,
  c2,
  0,
  c7,
  c9,
  0,
  c25,
  c51,
  0,
  c249,
  c129,
  c129,
  c149,
  c51,
  c7,
  c45,
  c2,
  0,
  c5,
  0,
  c62,
  c31,
  c32,
  c62,
  c21,
  c5,
  0,
  c2,
  c188,
  c3,
  c3,
  c75,
  0,
  0,
  c5,
  c82,
  c55,
  c5,
  0,
  c2,
  0,
  c7,
  c9,
  0,
  c25,
  c51,
  0,
  116,
  c46,
  c110,
  c46,
  c51,
  c7,
  c45,
  c2,
  0,
  c5,
  0,
  c62,
  c31,
  c32,
  c62,
  c21,
  c5,
  0,
  c2,
  c82,
  c55,
  c2,
  c75,
  c69,
  0,
  c94,
  c70,
  0,
  0,
  0,
  0,
  c64,
  c35,
  0,
  c38,
  0,
  c74,
  581110472830489,
  c176,
  581110472830489,
  5891845567436457,
  c38,
  c64,
  c100,
  c3,
  c3,
  0,
  c2,
  0,
  c7,
  c9,
  0,
  c38,
  c275,
  c217,
  c275,
  c7,
  c45,
  c2,
  0,
  c244,
  0,
  0,
  3970839051851129,
  c277,
  c173,
  3970839051851129,
  c15,
  c32,
  c15,
  c21,
  c21,
  0,
  c2,
  c100,
  c3,
  c3,
  c75,
  0,
  0,
  c261,
  c100,
  c73,
  c261,
  0,
  c2,
  0,
  c7,
  c9,
  0,
  c85,
  c99,
  c61,
  c99,
  c7,
  c45,
  c2,
  0,
  c244,
  0,
  c346,
  c15,
  c32,
  c15,
  c21,
  c21,
  0,
  c2,
  c100,
  c73,
  c2,
  c75,
  c70,
  0,
  c71,
  0,
  0,
  0,
  c24,
  c121,
  c3,
  c24,
  0,
  c4,
  c121,
  c152,
  c4,
  0,
  c4,
  c121,
  c84,
  c4,
  0,
  c24,
  c121,
  c3,
  c24,
  c23,
  c157,
  c23,
  c72,
  0,
  0,
  c29,
  0,
  c8,
  c10,
  c0,
  c8,
  0,
  c8,
  0,
  0,
  c13,
  c277,
  c173,
  c13,
  c15,
  c34,
  c15,
  c84,
  c8,
  c29,
  c23,
  c157,
  c23,
  0,
  0,
  0,
  0,
  c26,
  0,
  c29,
  0,
  c8,
  c10,
  c0,
  c8,
  0,
  c8,
  51795279170797731404485476693764073670736547,
  c21,
  c8,
  c29,
  0,
  c29,
  0,
  c8,
  c10,
  c0,
  c8,
  0,
  c8,
  0,
  c296,
  80570433295604533742253414504429745707945539,
  80570434265567672916486792730056150552677955,
  c296,
  c21,
  c8,
  c29,
  c26,
  0,
  c26,
  0,
  c105,
  0,
  0,
  c309,
  c310,
  c339,
  c309,
  c20,
  c152,
  c20,
  0,
  0,
  c203,
  c153,
  c339,
  c203,
  c20,
  c84,
  c20,
  c105,
  c158,
  c26,
  0,
  c26,
  c41,
  0,
  0,
  c24,
  c58,
  c55,
  c24,
  0,
  c263,
  c58,
  c45,
  c58,
  0,
  0,
  c311,
  c153,
  c22,
  c311,
  c58,
  c21,
  c58,
  0,
  c24,
  c58,
  c55,
  c24,
  c26,
  0,
  c26,
  c41,
  c158,
  c26,
  0,
  0,
  0,
  0,
  c16,
  0,
  c11,
  0,
  c13,
  c237,
  c33,
  c13,
  0,
  c13,
  c184,
  c292,
  c13,
  c11,
  0,
  c11,
  0,
  c25,
  c183,
  c33,
  c25,
  0,
  c25,
  c183,
  0,
  c278,
  c86,
  5229987765647513,
  c86,
  c25,
  c11,
  c16,
  0,
  0,
  c145,
  c198,
  c201,
  c145,
  c10,
  c0,
  c45,
  c40,
  c40,
  0,
  c105,
  0,
  0,
  c145,
  c198,
  c201,
  c145,
  c10,
  c0,
  c45,
  0,
  0,
  c203,
  c179,
  0,
  c25,
  c184,
  83447949775138505925667658610119300706609835,
  c25,
  c203,
  0,
  c203,
  c179,
  0,
  c13,
  c184,
  c292,
  c13,
  c203,
  c21,
  c21,
  c105,
  0,
  0,
  c16,
  0,
  c11,
  0,
  c13,
  c237,
  c33,
  c13,
  0,
  c13,
  c184,
  c44,
  c13,
  c11,
  0,
  c11,
  0,
  c25,
  c183,
  c33,
  c25,
  0,
  c25,
  c183,
  c44,
  c44,
  c11,
  c16,
  0,
  0,
  c145,
  c198,
  c201,
  c145,
  c10,
  c0,
  c45,
  0,
  0,
  c147,
  c179,
  0,
  c25,
  c184,
  c44,
  c44,
  c147,
  0,
  c147,
  c179,
  0,
  c13,
  c184,
  c44,
  c13,
  c147,
  c21,
  c21,
  0,
  c16,
  c10,
  c0,
  c16,
  0,
  c105,
  0,
  0,
  c145,
  c198,
  c201,
  c145,
  c10,
  c0,
  c45,
  c40,
  c105,
  c69,
  0,
  0,
  0,
  c5,
  c82,
  c55,
  c5,
  0,
  c5,
  0,
  c124,
  c171,
  c22,
  c124,
  c45,
  c5,
  c40,
  c40,
  c41,
  0,
  0,
  c5,
  c82,
  c55,
  c5,
  0,
  c5,
  0,
  c124,
  c171,
  c22,
  c124,
  c45,
  c5,
  0,
  c5,
  0,
  c344,
  0,
  c25,
  290557737879809,
  c33,
  290557737879809,
  c22,
  c22,
  c21,
  c5,
  0,
  c5,
  c82,
  c55,
  c5,
  c41,
  c69,
  0,
  0,
  0,
  0,
  c16,
  0,
  c11,
  0,
  0,
  c111,
  c210,
  c131,
  c111,
  c49,
  0,
  c182,
  c210,
  c247,
  c182,
  c49,
  0,
  c107,
  c30,
  c140,
  c30,
  c11,
  0,
  c11,
  0,
  0,
  172,
  c86,
  c131,
  c86,
  c49,
  0,
  c108,
  c86,
  c247,
  c108,
  c49,
  0,
  c107,
  c30,
  c140,
  c30,
  c11,
  c16,
  0,
  0,
  c226,
  c198,
  c201,
  c226,
  c10,
  c0,
  c45,
  c40,
  c40,
  c37,
  0,
  0,
  c16,
  0,
  c11,
  0,
  0,
  c111,
  c304,
  c136,
  c111,
  c49,
  0,
  c182,
  c210,
  c165,
  c165,
  c49,
  0,
  c107,
  c30,
  c44,
  c44,
  c11,
  0,
  c11,
  0,
  0,
  c252,
  c128,
  c128,
  c136,
  c49,
  0,
  c108,
  c299,
  c165,
  c108,
  c49,
  0,
  c107,
  c276,
  c44,
  c276,
  c11,
  c16,
  0,
  0,
  c226,
  c198,
  c201,
  c226,
  c10,
  c0,
  c45,
  0,
  0,
  c224,
  c15,
  c290,
  c15,
  0,
  c224,
  c15,
  c290,
  c15,
  c21,
  c21,
  0,
  c16,
  c10,
  c0,
  c16,
  c37,
  c70,
  0,
  0,
  0,
  c154,
  c100,
  c73,
  c154,
  0,
  0,
  3486655034120553,
  c171,
  c22,
  3486655034120553,
  0,
  c124,
  c171,
  c22,
  c124,
  c45,
  c45,
  c40,
  c40,
  c37,
  0,
  0,
  c288,
  c100,
  c73,
  c288,
  0,
  c263,
  0,
  c124,
  c171,
  c22,
  c124,
  c45,
  c45,
  0,
  0,
  46040248178511202460029643914656874506818715,
  c15,
  c22,
  c15,
  0,
  c344,
  c15,
  c22,
  c15,
  c21,
  c21,
  0,
  c263,
  c100,
  c73,
  c263,
  c37,
  c70,
  0,
  0,
  c26,
  c37,
  0,
  c29,
  0,
  c8,
  c10,
  c0,
  c8,
  0,
  c8,
  0,
  c296,
  c15,
  c290,
  c15,
  c21,
  c8,
  c29,
  c37,
  0,
  c26,
  c37,
  c158,
  c37,
  0,
  c26,
  c37,
  0,
  0,
  c24,
  c58,
  c73,
  c24,
  0,
  c5,
  c58,
  c45,
  c5,
  0,
  c5,
  c58,
  c21,
  c5,
  0,
  c24,
  c58,
  c73,
  c24,
  c37,
  0,
  c26,
  c37,
  c158,
  c37,
  0,
  0,
  0,
  c27,
  0,
  0,
  c130,
  c321,
  c239,
  c130,
  0,
  c329,
  c10,
  c0,
  c329,
  c43,
  c43,
  0,
  0,
  c130,
  0,
  0,
  0,
  c81,
  c303,
  c168,
  c81,
  c19,
  0,
  40285217132843906739912276343449475334709267,
  c326,
  c142,
  c142,
  c19,
  c170,
  0,
  0,
  c81,
  c303,
  2905551204212057,
  c81,
  c19,
  c44,
  c44,
  c170,
  c259,
  c130,
  0,
  c60,
  c10,
  c0,
  c60,
  c125,
  c125,
  c27,
  0,
  c27,
  0,
  c342,
  0,
  c283,
  c20,
  c192,
  c20,
  c43,
  c43,
  c68,
  c27,
  0,
  c27,
  c41,
  0,
  0,
  c288,
  c58,
  c55,
  c58,
  0,
  c60,
  c58,
  0,
  0,
  0,
  c219,
  c253,
  c270,
  c139,
  c54,
  0,
  c92,
  52,
  c142,
  c92,
  c54,
  c9,
  c22,
  c9,
  c58,
  c125,
  c125,
  c27,
  0,
  c27,
  c41,
  c68,
  c27,
  0,
  0,
  0,
  0,
  c258,
  c169,
  c3,
  c3,
  0,
  c101,
  c10,
  c0,
  c101,
  0,
  c102,
  0,
  c18,
  0,
  c13,
  3967131513149049,
  c33,
  c13,
  0,
  c13,
  c216,
  c292,
  c13,
  c18,
  0,
  c18,
  0,
  c42,
  c103,
  c33,
  c103,
  0,
  0,
  581109441217561,
  c39,
  c328,
  581109441217561,
  c216,
  c291,
  c216,
  c18,
  c102,
  0,
  c258,
  c169,
  c3,
  c3,
  0,
  0,
  0,
  c161,
  c35,
  c295,
  c161,
  c321,
  c239,
  0,
  c161,
  c35,
  c295,
  c161,
  0,
  c283,
  c10,
  c0,
  c192,
  c43,
  c43,
  0,
  0,
  c341,
  0,
  0,
  c13,
  c237,
  0,
  c132,
  c326,
  c142,
  c132,
  c13,
  c170,
  0,
  c13,
  c237,
  c44,
  c13,
  c170,
  c259,
  c259,
  0,
  c101,
  c10,
  c0,
  c101,
  0,
  c102,
  0,
  c79,
  0,
  c13,
  80570434265613308338095008988510031890371907,
  c33,
  c13,
  0,
  c13,
  c216,
  c44,
  c13,
  c79,
  0,
  c79,
  0,
  c42,
  c103,
  c33,
  c103,
  0,
  83447949767015400879405121298714409793423915,
  c216,
  c44,
  c44,
  c79,
  c102,
  0,
  c341,
  c10,
  c0,
  c259,
  0,
  0,
  0,
  c161,
  c35,
  c295,
  c161,
  c169,
  c3,
  c3,
  0,
  c283,
  c10,
  c0,
  c192,
  c43,
  c43,
  0,
  0,
  0,
  c4,
  0,
  c289,
  c170,
  0,
  0,
  c47,
  581113291007001,
  c307,
  c47,
  c133,
  69060372235813012334189239874728763344499275,
  c133,
  c170,
  c3,
  c3,
  0,
  c4,
  0,
  c289,
  c9,
  c172,
  c9,
  0,
  c343,
  c9,
  c172,
  c9,
  c4,
  0,
  c4,
  0,
  c18,
  0,
  c42,
  c308,
  c33,
  c308,
  0,
  0,
  c47,
  34530186112958088927262776943888908159113611,
  c307,
  c47,
  c133,
  c291,
  c133,
  c18,
  0,
  c18,
  0,
  c42,
  c103,
  c33,
  c103,
  0,
  0,
  c284,
  c39,
  c328,
  c39,
  c133,
  c291,
  c133,
  c18,
  c4,
  0,
  c4,
  0,
  c18,
  c171,
  c172,
  c18,
  c3,
  c3,
  0,
  c342,
  0,
  c4,
  0,
  1162222946641449,
  c9,
  c172,
  1162222946641449,
  c192,
  c4,
  c43,
  c43,
  c68,
  c68,
  0,
  0,
  0,
  c5,
  c188,
  c3,
  c3,
  0,
  c5,
  0,
  0,
  0,
  c47,
  c149,
  c313,
  c47,
  c54,
  0,
  c240,
  c149,
  c214,
  c149,
  c54,
  c9,
  c22,
  c9,
  0,
  0,
  0,
  c139,
  c39,
  c214,
  c39,
  c54,
  0,
  c92,
  c39,
  c214,
  c39,
  c54,
  c9,
  c22,
  c9,
  c5,
  0,
  c5,
  0,
  c18,
  0,
  c42,
  c186,
  c33,
  c186,
  c22,
  c18,
  0,
  c18,
  0,
  c42,
  c103,
  c33,
  c103,
  c22,
  c18,
  c5,
  0,
  c5,
  c188,
  c3,
  c3,
  c41,
  0,
  0,
  c5,
  c82,
  c55,
  c5,
  0,
  c5,
  0,
  0,
  0,
  c47,
  c46,
  34530186113049359770478203897071894303136779,
  c47,
  c54,
  0,
  c240,
  c46,
  c142,
  c46,
  c54,
  c9,
  c22,
  c9,
  0,
  0,
  0,
  c219,
  c253,
  c270,
  c139,
  c54,
  0,
  c92,
  28,
  c142,
  c92,
  c54,
  c9,
  c22,
  c9,
  c5,
  0,
  c5,
  0,
  c79,
  0,
  c42,
  c186,
  c33,
  c186,
  c22,
  c79,
  0,
  c79,
  0,
  c42,
  c103,
  c33,
  c103,
  c22,
  c79,
  c5,
  0,
  c5,
  c82,
  c55,
  c5,
  c41,
  0,
  0,
  0,
  c258,
  c169,
  c3,
  c3,
  0,
  c101,
  c10,
  c0,
  c101,
  0,
  c102,
  0,
  c18,
  0,
  c13,
  3967131513149049,
  c33,
  c13,
  c22,
  c18,
  0,
  c18,
  0,
  c42,
  c103,
  c33,
  c103,
  c22,
  c18,
  c102,
  0,
  c258,
  c169,
  c3,
  c3,
  c41,
  c68,
  c41,
  0,
  0,
  0,
  c36,
  0,
  c60,
  c10,
  c0,
  c60,
  0,
  c53,
  0,
  c18,
  0,
  0,
  c111,
  28775155094906029937728516920548140973765123,
  c163,
  c111,
  c17,
  0,
  c272,
  c271,
  c251,
  c215,
  c17,
  0,
  c85,
  c30,
  c61,
  c30,
  c18,
  0,
  c18,
  0,
  0,
  c284,
  c39,
  c163,
  c39,
  c17,
  0,
  c117,
  c39,
  132,
  c39,
  c17,
  0,
  c85,
  c30,
  c61,
  c30,
  c18,
  c53,
  c36,
  c12,
  0,
  c36,
  0,
  c60,
  c10,
  c0,
  c60,
  0,
  c53,
  0,
  c79,
  0,
  0,
  c111,
  c304,
  c136,
  c111,
  c17,
  0,
  c332,
  63305341208113396221732444880399746894598203,
  c165,
  c165,
  c17,
  0,
  c85,
  c30,
  c44,
  c44,
  c79,
  0,
  c79,
  0,
  0,
  c284,
  c327,
  c136,
  c136,
  c17,
  0,
  c117,
  c327,
  c165,
  c117,
  c17,
  0,
  c85,
  c30,
  c44,
  c44,
  c79,
  c53,
  c36,
  c12,
  0,
  0,
  c36,
  0,
  c60,
  0,
  c289,
  c9,
  c172,
  c9,
  0,
  c343,
  c9,
  c172,
  c9,
  c60,
  0,
  c53,
  0,
  c18,
  0,
  c65,
  c17,
  0,
  c272,
  c271,
  c251,
  c215,
  c17,
  0,
  c65,
  c337,
  c61,
  c65,
  c18,
  0,
  c18,
  0,
  c65,
  c17,
  0,
  c117,
  c39,
  124,
  c39,
  c17,
  0,
  c65,
  c337,
  c61,
  c65,
  c18,
  c53,
  c36,
  c12,
  c68,
  c12,
  0,
  0,
  c36,
  0,
  c60,
  0,
  0,
  0,
  c191,
  c282,
  c163,
  c163,
  c54,
  0,
  c240,
  c282,
  c214,
  c282,
  c54,
  c9,
  c22,
  c9,
  0,
  0,
  0,
  c139,
  c39,
  c163,
  c39,
  c54,
  0,
  c92,
  c39,
  c214,
  c39,
  c54,
  c9,
  c22,
  c9,
  c60,
  0,
  c53,
  0,
  c18,
  0,
  0,
  51795279170790125501140076499849708274102947,
  c215,
  c163,
  c163,
  c17,
  0,
  c272,
  c271,
  c251,
  c215,
  c17,
  c22,
  c18,
  0,
  c18,
  0,
  0,
  c139,
  c39,
  c163,
  c39,
  c17,
  0,
  c117,
  c39,
  4,
  c39,
  c17,
  c22,
  c18,
  c53,
  c36,
  c12,
  0,
  c36,
  0,
  c60,
  0,
  0,
  0,
  c191,
  c46,
  40285217131933733609986487563456523874298131,
  c46,
  c54,
  0,
  c240,
  c46,
  c142,
  c46,
  c54,
  c9,
  c22,
  c9,
  0,
  0,
  0,
  c219,
  c253,
  c270,
  c139,
  c54,
  0,
  c92,
  12,
  c142,
  c92,
  c54,
  c9,
  c22,
  c9,
  c60,
  0,
  c53,
  0,
  c79,
  0,
  0,
  51795279169885022972321930827565967499300643,
  c46,
  c335,
  c46,
  c17,
  0,
  c332,
  c46,
  c165,
  c46,
  c17,
  c22,
  c79,
  0,
  c79,
  0,
  0,
  c139,
  c331,
  c335,
  c139,
  c17,
  0,
  c117,
  c331,
  c165,
  c117,
  c17,
  c22,
  c79,
  c53,
  c36,
  c12,
  0,
  0,
  c36,
  0,
  c60,
  c10,
  c0,
  c60,
  0,
  c53,
  0,
  c18,
  0,
  c65,
  c17,
  0,
  c272,
  c271,
  c251,
  c215,
  c17,
  c22,
  c18,
  0,
  c18,
  0,
  c65,
  c17,
  0,
  c117,
  c39,
  140,
  c39,
  c17,
  c22,
  c18,
  c53,
  c36,
  c12,
  c68,
  c12,
  0,
  0,
  c27,
  c12,
  0,
  c36,
  0,
  c101,
  c10,
  c0,
  c101,
  c125,
  c36,
  c12,
  0,
  c27,
  c12,
  c68,
  c12,
  0,
  c27,
  c12,
  0,
  c36,
  0,
  c5,
  c58,
  0,
  0,
  0,
  c219,
  c253,
  c270,
  c139,
  c54,
  0,
  c92,
  148,
  c142,
  c92,
  c54,
  c9,
  c22,
  c9,
  c5,
  c125,
  c36,
  c12,
  0,
  c27,
  c12,
  c68,
  c12,
  0,
  0,
  0,
  c156,
  0,
  c48,
  0,
  0,
  0,
  c148,
  c19,
  c159,
  c19,
  c78,
  c78,
  0,
  c148,
  c222,
  0,
  581110559313433,
  c83,
  5229988613101465,
  581110559313433,
  c222,
  c10,
  c0,
  0,
  0,
  c148,
  c19,
  c159,
  c19,
  c78,
  c78,
  0,
  c148,
  c222,
  c14,
  c14,
  c194,
  c48,
  c260,
  0,
  c48,
  0,
  0,
  0,
  c148,
  c19,
  c159,
  c19,
  c78,
  c78,
  0,
  c148,
  c222,
  c44,
  c44,
  c10,
  c0,
  0,
  0,
  c148,
  c19,
  c159,
  c19,
  c78,
  c78,
  0,
  c148,
  c222,
  c14,
  c14,
  c28,
  c48,
  0,
  c66,
  c23,
  c68,
  c23,
  0,
  c66,
  c41,
  c116,
  c41,
  0,
  c156,
  c23,
  c68,
  c23,
  0,
  c93,
  0,
  c66,
  0,
  c48,
  0,
  c4,
  0,
  c225,
  c200,
  c199,
  c225,
  0,
  c225,
  c200,
  c199,
  c225,
  c4,
  0,
  c4,
  0,
  c109,
  0,
  c229,
  c231,
  c248,
  c231,
  0,
  c229,
  c133,
  c300,
  c133,
  c109,
  0,
  c109,
  0,
  c229,
  c231,
  c248,
  c231,
  0,
  c229,
  c133,
  c300,
  c133,
  c109,
  c4,
  c48,
  c68,
  c68,
  0,
  c66,
  c41,
  c116,
  c41,
  c93,
  0,
  c94,
  0,
  c66,
  0,
  c48,
  0,
  0,
  c146,
  c200,
  c199,
  c146,
  0,
  c146,
  c200,
  c199,
  c146,
  0,
  c146,
  c200,
  c199,
  c146,
  0,
  c146,
  c200,
  c199,
  c146,
  0,
  0,
  c109,
  c153,
  0,
  c205,
  0,
  c160,
  c256,
  220,
  c160,
  c202,
  c65,
  c109,
  0,
  c109,
  0,
  c65,
  c17,
  c248,
  c17,
  0,
  c205,
  0,
  c160,
  c256,
  212,
  c160,
  c202,
  c65,
  c109,
  0,
  c109,
  0,
  c65,
  c17,
  c248,
  c17,
  0,
  c205,
  0,
  c160,
  c256,
  156,
  c160,
  c202,
  c65,
  c109,
  0,
  c109,
  c153,
  0,
  c205,
  0,
  c160,
  c256,
  228,
  c160,
  c202,
  c65,
  c109,
  c48,
  c68,
  c68,
  0,
  c66,
  c41,
  c116,
  c41,
  c94,
  0,
  0,
  c156,
  0,
  c48,
  0,
  0,
  0,
  0,
  c167,
  c83,
  c207,
  c167,
  c220,
  c159,
  c220,
  c78,
  c78,
  0,
  c175,
  0,
  c322,
  c83,
  c126,
  c83,
  c174,
  0,
  c167,
  c83,
  c207,
  c167,
  c10,
  c0,
  0,
  0,
  c13,
  c220,
  c159,
  c13,
  c78,
  c78,
  0,
  c13,
  0,
  c132,
  1670689536887370,
  c126,
  c132,
  c14,
  c13,
  c194,
  c48,
  c260,
  0,
  c48,
  0,
  0,
  0,
  c38,
  c220,
  c159,
  c38,
  c78,
  c78,
  0,
  c38,
  0,
  c322,
  1016942465451026,
  c176,
  c176,
  c44,
  c38,
  c10,
  c0,
  0,
  0,
  c13,
  c220,
  c159,
  c13,
  c78,
  c78,
  0,
  c13,
  0,
  c132,
  204,
  c176,
  c132,
  c14,
  c13,
  c28,
  c48,
  0,
  c66,
  c23,
  c68,
  c23,
  0,
  c66,
  c41,
  c116,
  c41,
  0,
  c156,
  c23,
  c68,
  c23,
  0,
  0,
  0,
  c156,
  0,
  c29,
  0,
  c8,
  c10,
  c0,
  c8,
  c43,
  c29,
  c260,
  0,
  c29,
  0,
  c8,
  c10,
  c0,
  c8,
  c43,
  c29,
  0,
  c66,
  c23,
  c158,
  c23,
  0,
  c66,
  c41,
  c116,
  c41,
  0,
  c156,
  c23,
  c158,
  c23,
  0,
  c93,
  c69,
  0,
  c66,
  c41,
  c116,
  c41,
  c69,
  0,
  c94,
  c70,
  0,
  c66,
  c41,
  c116,
  c41,
  c70,
  0,
  0,
  c156,
  0,
  c29,
  0,
  c8,
  c10,
  c0,
  c8,
  c43,
  c29,
  c260,
  0,
  c29,
  0,
  c8,
  c10,
  c0,
  c8,
  c43,
  c29,
  0,
  c66,
  c23,
  c158,
  c23,
  0,
  c66,
  c41,
  c116,
  c41,
  0,
  c156,
  c23,
  c158,
  c23,
  0,
  0,
  0,
  c71,
  0,
  c26,
  c76,
  0,
  0,
  c24,
  c20,
  0,
  c293,
  c245,
  0,
  c119,
  c208,
  3977827287274873,
  c208,
  c293,
  c24,
  0,
  c122,
  c20,
  c152,
  c20,
  0,
  c122,
  c20,
  c84,
  c20,
  0,
  c24,
  c20,
  0,
  0,
  c119,
  28775155094923777046131478809679592605463683,
  c173,
  c119,
  c204,
  c204,
  0,
  c119,
  c208,
  c14,
  c208,
  c24,
  c76,
  c72,
  0,
  c26,
  c76,
  0,
  c29,
  0,
  c8,
  c6,
  c0,
  c8,
  0,
  c8,
  c6,
  c84,
  c8,
  c29,
  c76,
  0,
  c150,
  c69,
  c97,
  c69,
  0,
  0,
  0,
  0,
  c16,
  c1,
  0,
  c11,
  0,
  0,
  196,
  c86,
  c131,
  c86,
  c49,
  c265,
  c49,
  0,
  c107,
  c30,
  c140,
  c30,
  c11,
  c16,
  0,
  c90,
  c1,
  c0,
  c1,
  c40,
  c40,
  c37,
  0,
  0,
  c16,
  c1,
  0,
  c11,
  0,
  0,
  c252,
  c128,
  c128,
  c136,
  c49,
  c265,
  c49,
  0,
  c107,
  c276,
  c44,
  c276,
  c11,
  c16,
  0,
  c90,
  c1,
  c0,
  c1,
  0,
  c90,
  c1,
  c21,
  c1,
  0,
  c16,
  c1,
  c0,
  c16,
  c37,
  c70,
  0,
  0,
  0,
  c154,
  c100,
  c73,
  c154,
  0,
  c2,
  0,
  c7,
  c171,
  c172,
  c7,
  c45,
  c2,
  c40,
  c40,
  c37,
  0,
  0,
  0,
  c64,
  c35,
  0,
  5728516812781225,
  0,
  c74,
  c178,
  2905553124914265,
  c178,
  c44,
  c44,
  c64,
  c6,
  c73,
  c6,
  0,
  c2,
  c6,
  c138,
  c6,
  0,
  c244,
  c6,
  c21,
  c6,
  0,
  c2,
  c6,
  c73,
  c6,
  c37,
  c70,
  0,
  c71,
  0,
  c26,
  c76,
  0,
  0,
  c24,
  c20,
  0,
  c293,
  c245,
  c34,
  c34,
  c24,
  0,
  c4,
  c20,
  c152,
  c4,
  0,
  c4,
  c20,
  c84,
  c4,
  0,
  c24,
  c20,
  0,
  0,
  0,
  c219,
  c128,
  c128,
  164,
  c277,
  c173,
  c277,
  c15,
  c34,
  c15,
  c24,
  c76,
  c72,
  0,
  c26,
  c76,
  0,
  c29,
  0,
  c8,
  c6,
  c0,
  c8,
  0,
  c8,
  c6,
  c84,
  c8,
  c29,
  c76,
  0,
  0,
  c71,
  0,
  c27,
  c77,
  c63,
  c77,
  c72,
  0,
  c27,
  c77,
  c63,
  c77,
  0,
  c150,
  0,
  c255,
  0,
  0,
  c143,
  c98,
  0,
  c161,
  c286,
  c34,
  c161,
  c143,
  0,
  c4,
  c98,
  c192,
  c4,
  c43,
  c43,
  c155,
  0,
  0,
  c143,
  c98,
  c3,
  c3,
  0,
  c4,
  c98,
  c192,
  c4,
  c43,
  c43,
  c97,
  0,
  c255,
  0,
  0,
  0,
  c64,
  c35,
  c34,
  c64,
  c87,
  c87,
  0,
  c64,
  c35,
  c34,
  c64,
  0,
  c2,
  c10,
  c0,
  c2,
  c43,
  c43,
  c155,
  0,
  0,
  0,
  c64,
  c35,
  c34,
  c64,
  c6,
  c3,
  c3,
  0,
  c2,
  c6,
  c0,
  c6,
  c43,
  c43,
  0,
  0,
  c106,
  c12,
  c63,
  c12,
  0,
  c106,
  c12,
  c63,
  c12,
  0,
  c106,
  c12,
  c63,
  c12,
  0,
  c106,
  c12,
  c63,
  c12,
  0,
  c71,
  0,
  c27,
  c77,
  c155,
  c77,
  c72,
  0,
  c27,
  c77,
  c155,
  c77,
  0,
  0,
  c71,
  c80,
  c72,
  c80,
  0,
  c93,
  0,
  c66,
  c166,
  c116,
  c166,
  c97,
  c93,
  0,
  c94,
  0,
  c66,
  c166,
  c116,
  c166,
  0,
  c66,
  0,
  c48,
  0,
  c2,
  c238,
  c189,
  c2,
  c338,
  c48,
  c116,
  0,
  c48,
  0,
  c2,
  c6,
  c138,
  c6,
  c28,
  c48,
  c94,
  0,
  c71,
  c80,
  c72,
  c80,
  0,
  0,
  c71,
  c80,
  c72,
  c80,
  0,
  c93,
  c69,
  c97,
  c69,
  0,
  c94,
  c70,
  0,
  c106,
  0,
  0,
  0,
  c64,
  c35,
  0,
  c205,
  0,
  c74,
  c323,
  c351,
  c74,
  c202,
  0,
  1016942286236690,
  c323,
  c207,
  c207,
  c64,
  c87,
  c87,
  0,
  c64,
  c35,
  0,
  c205,
  0,
  1452773636260394,
  c177,
  c351,
  c177,
  c202,
  0,
  20,
  c177,
  c207,
  c177,
  c64,
  0,
  c2,
  c238,
  c189,
  c2,
  c43,
  c43,
  c63,
  0,
  0,
  0,
  c64,
  c35,
  0,
  c38,
  0,
  c74,
  c178,
  c176,
  c178,
  c44,
  c38,
  c64,
  c6,
  c3,
  c3,
  0,
  c2,
  c6,
  c138,
  c6,
  c43,
  c43,
  c70,
  0,
  c71,
  c80,
  c72,
  c80
]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
lemma tree_checked : check code order (fun _ => none) treeData = some [] := by
  decide +kernel

lemma classified (q : V → Fin 4) (hq : CodeConditions q) : ∃ i, q = SlotTables.code i := by
  exact check_sound code order (fun _ => none) treeData [] q tree_checked
    (by intro v c h; cases h) hq

lemma conditions_classified (t : H → Slot) (ht : Conditions t) :
    ∃ i, localCode t = SlotTables.code i :=
  classified (localCode t) (code_conditions t ht)

end SlotTree

namespace FiniteSlots

def joined (f : H → Fin 30) (a b h k : H) : Prop :=
  (f h = f a ∨ f h = f b) ∧ (f k = f a ∨ f k = f b)

def mergeRel (f : H → Fin 30) (a b h k : H) : Prop :=
  f h = f k ∨ joined f a b h k ∨ joined f (barH a) (barH b) h k

lemma joined_sound (t : H → Slot) (f : H → Fin 30)
    (hf : ∀ h k, f h = f k → t h = t k) (a b h k : H)
    (hab : t a = t b) (hr : joined f a b h k) : t h = t k := by
  obtain ⟨hh, hk⟩ := hr
  rcases hh with hh | hh <;> rcases hk with hk | hk
  · exact (hf h a hh).trans (hf k a hk).symm
  · exact (hf h a hh).trans (hab.trans (hf k b hk).symm)
  · exact (hf h b hh).trans (hab.symm.trans (hf k a hk).symm)
  · exact (hf h b hh).trans (hf k b hk).symm

lemma mergeRel_sound (t : H → Slot) (f : H → Fin 30)
    (hf : ∀ h k, f h = f k → t h = t k)
    (hb : ∀ h, t (barH h) = bar (t h)) (a b h k : H)
    (hab : t a = t b) (hr : mergeRel f a b h k) : t h = t k := by
  rcases hr with hr | hr | hr
  · exact hf h k hr
  · exact joined_sound t f hf a b h k hab hr
  · apply joined_sound t f hf (barH a) (barH b) h k ?_ hr
    rw [hb, hb, hab]

def mergeRows : Fin 15 → Finset V := ![{1,4,5}, {0,2,6}, {3,5,6}, {2,4,5,6},
  {1,3,7}, {0,3,6,7}, {4,6,7}, {2,4,8}, {0,7,8}, {1,4,7,8},
  {0,3,9}, {2,5,9}, {1,3,5,9}, {1,8,9}, {0,2,8,9}]

lemma mergeRows_independent : ∀ r, independent (mergeRows r) := by
  unfold independent
  decide +kernel

def mergeHalf (n : ℕ) : H := (⟨(n / 2) % 15, Nat.mod_lt _ (by decide)⟩, n.testBit 0)

def mergeVertex (z : ℕ) : V := ⟨(z / 3) % 10, Nat.mod_lt _ (by decide)⟩

def mergeFirst (z : ℕ) : ℕ := (z / 30) % 30

def mergeSecond (z : ℕ) : ℕ := (z / 900) % 30

def mergeThird (z : ℕ) : ℕ := (z / 27000) % 30

def mergeRow (z : ℕ) : Fin 15 := ⟨(z / 810000) % 15, Nat.mod_lt _ (by decide)⟩

def mergeWitness (z : ℕ) : Fin 3 → H :=
  ![mergeHalf (mergeFirst z), mergeHalf (mergeSecond z), mergeHalf (mergeThird z)]

def MergeCheck (q : V → Fin 4) (f : H → Fin 30) (a b : H) (z : ℕ) : Prop :=
  let v := mergeVertex z
  if z % 3 = 0 then
    let i : Fin 3 := ⟨mergeFirst z % 3, Nat.mod_lt _ (by decide)⟩
    let j : Fin 3 := ⟨mergeSecond z % 3, Nat.mod_lt _ (by decide)⟩
    block (q v) i ≠ block (q v) j ∧ mergeRel f a b (around v i) (around v j)
  else if z % 3 = 1 then
    let h := mergeHalf (mergeFirst z)
    let k := mergeHalf (mergeSecond z)
    endpoint k = endpoint h ∧ mergeRel f a b k (barH h)
  else
    q v ≠ 3 ∧ touches v (mergeRows (mergeRow z)) ∧
      ∀ i : Fin 3, endpoint (mergeWitness z i) ∈ mergeRows (mergeRow z) ∧
        mergeRel f a b (mergeWitness z i) (around v i)

lemma mergeCheck_false (t : H → Slot) (ht : Conditions t) (q : V → Fin 4)
    (hq : localCode t = q) (f : H → Fin 30)
    (hf : ∀ h k, f h = f k → t h = t k) (a b : H) (hab : t a = t b)
    (z : ℕ) (hz : MergeCheck q f a b z) : False := by
  have hs := mergeRel_sound t f hf ht.1 a b
  unfold MergeCheck at hz
  dsimp only at hz
  split_ifs at hz with hzero hone
  · apply hz.1
    rw [← hq]
    exact (localCode_exact t _ (ht.2.2.1 _) _ _).mp (hs _ _ hab hz.2)
  · apply ht.2.1 (mergeHalf (mergeFirst z))
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, mergeHalf (mergeSecond z), hz.1, hs _ _ hab hz.2⟩
  · obtain ⟨hn, htouch, hhits⟩ := hz
    have hc : (selected t (mergeVertex z)).card = 2 :=
      card_two_of_code_ne_three t _ (ht.2.2.1 _) (by rw [hq]; exact hn)
    obtain ⟨h, hv, hdis⟩ := ht.2.2.2 _ _ (mergeRows_independent _) htouch hc
    obtain ⟨i, hi⟩ := around_complete _ h hv
    obtain ⟨hmem, hrel⟩ := hhits i
    have hEq := hs _ _ hab hrel
    rw [hi] at hEq
    have hlower : endpoint (mergeWitness z i) ∈ lower t h := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, mergeWitness z i, rfl, hEq⟩
    exact Finset.disjoint_left.mp hdis hlower hmem

def canonicalLabel (f : H → Fin 30) (h : H) : Finset V :=
  Finset.univ.filter fun v => ∃ k : H, endpoint k = v ∧ f k = f h

lemma lower_eq_canonicalLabel (t : H → Slot) (f : H → Fin 30)
    (he : ∀ h k, t h = t k ↔ f h = f k) (h : H) :
    lower t h = canonicalLabel f h := by
  ext v
  simp only [lower, canonicalLabel, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, hk, heq⟩
    exact ⟨k, hk, (he k h).mp heq⟩
  · rintro ⟨k, hk, heq⟩
    exact ⟨k, hk, (he k h).mpr heq⟩

end FiniteSlots

namespace NonlocalMerge

open PEqualNP.Outside.L_meta_2590_aux.I0Proof.FiniteSlots

open PEqualNP.Outside.L_meta_2590_aux.I0Proof.SlotTables

def repData : Fin 45 → ℕ := ![
  0x31f192906242420,
  0x216b431c6242420,
  0xbd8438c020,
  0x216b431c6208109,
  0xbd84331c8508109,
  0x837a7b909,
  0x216b431c625a820,
  0x73c438c2b45a820,
  0x73c438c14bad020,
  0x73c438c39d52c20,
  0x1cf10e3052c20,
  0x7192916a,
  0xbd8434a08539820,
  0xbd8439c8e621420,
  0x2f610cc721420,
  0x31f192900118909,
  0x31f19291ac00509,
  0xc7c64a400509,
  0x85ad0c718820,
  0xa5528398a400462,
  0x839d9c862,
  0x9cb19292306b001,
  0x9c98dde8a48c001,
  0x9cb19634a48c001,
  0x272634a48c001,
  0x6b4399ac,
  0xa55283984329001,
  0xa5528399ee10c01,
  0x2954a0e610c01,
  0x837a4a0e610ca4,
  0xa56720814b7b843,
  0x73e720814bad043,
  0xbda72081ee52c43,
  0x1cf9c82052c43,
  0x837a4a08539843,
  0x837a4a23021443,
  0x20de92821443,
  0x77a6354b8c085,
  0x6306379d52c85,
  0x58ddea3052c85,
  0x18c18d52c85,
  0xbd98d005ee9c8e6,
  0x9cb19634017b8e6,
  0xbda72634017b8e6,
  0x272634017b8e6]

def certData : Fin 45 → ℕ := ![
  0x15cd00072300039c00039c00072300573100038d000399235e4a2d9ad900039900038d2d9ad9235e4a000e894fb2f970185500596b000396000e6b00038a7018554fb2f900039600596b00038a000e6b0007450003930003906a427046cd9041a2ba1d688246a3603a20a400039000039346cd906a42701d688241a2ba3a20a446a360001d116fab5962e24dad094e4675b83dcddeb51f9f000727000387000384001fa562e24d6fab594675b8ad094eb51f9f3dcdde000387000727001fa5000384000001,
  0xe890007200003990003990007200048a900039f00038d50a2092faa3100038d00039f2faa3150a2090015cd00038a0003966a1fba9e1dc4856400767a2600039600038a9e1dc46a1fba767a268564000007451d688241a2ba00479b000393001cf3000390767a446a1e5241a2ba1d688200039300479b000390001cf36a1e52767a44001d11ad4bb73dcdde9664496faa8d756fe916abc1000727000387000384001fa53dcddead4bb76faa8d96644916abc1756fe9000387000727001fa5000384000001,
  0x4fed00000000000000000000000000039f00071d00000000000000000000000000071d00039f000745000000000000000000000000536f3991b38900039c00071100000000000000000000000091b389536f3900071100039c003a21000000000000000000000000324cce900e180003870003841adaee620504000000000000000000000000900e18324cce0003840003876205041adaee000001,
  0xe890007200003990003990007200048a900039f00038d50a2092faa3100038d00039f2faa3150a2090015cd00038a000396213d1f9e1dc42810631b475700039600038a9e1dc4213d1f1b47572810630007451d68823dcdde00479b0003932f8a8d16abc10007270003873dcdde1d688200039300479b16abc12f8a8d0003870007270000014d91ce41a2ba2f800d72a49f001cf3000390767a44287d5f000384001fa541a2ba4d91ce72a49f2f800d000390001cf3287d5f767a44001fa5000384001d11,
  0x4fed00039600071d00071d00039600074500039f0053171b475728106300531700039f2810631b47570015cd9ce15c1e6caa00039c00038a0015af00038d1e6caa9ce15c00038a00039c00038d0015af000e89b88a2b4431ad000387000393442fcd508bfb620381442faf4431adb88a2b000393000387508bfb442fcd442faf620381000001ae655a085bec287d5f72c50c001cf3000390085be043489a000384001fa5085becae655a72c50c287d5f000390001cf343489a085be0001fa5000384001d11,
  0x100000000000000000000000000071a00039c00000000000000000000000000039c00071a005e7500000000000000000000000000070e000399239d926e003000000000000000000000000000039900070e6e0030239d920032dd0000000000000000000000000003840003901e702858202026822c3a4e4c0000000000000000000000000003900003845820201e70283a4e4c26822c001d11,
  0xe890007200003990003990007200048a900039f00038d50a2092faa3100038d00039f2faa3150a2090015cd00038a0003962d98d5531a01281009767a2600039600038a531a012d98d5767a262810090007451d6882420fb600479b0003932f8a8d16cee99e1cb629c3f9420fb61d688200039300479b16cee92f8a8d29c3f99e1cb60024554d91ce3dcdde2f800d16abcd001cf30003900007270003870007080023293dcdde4d91ce16abcd2f800d000390001cf3000387000727002329000708000001,
  0x32dd00039f00070e00070e00039f0007457656fe1f7ee200071a0007111f7ee27656fe00071100071a003a21004b97000399531a012d98d500072000646f000399004b972d98d5531a0100646f0007200048a904a19e421a4229c3f99df286b16ca1048f7700479b000393421a4204a19e9df28629c3f9048f77b16ca100039300479b0024557dbc433fef03000387000390b521971adaf13fefb71adb690007080023293fef037dbc430003900003871adaf1b521971adb693fefb7002329000708000001,
  0x32dd00039f00070e00070e00039f0007457656fe1f7ee200071a0007111f7ee27656fe00071100071a003a21421a4204a19e6270f529c3f900072000646f04a19e421a4229c3f96270f500646f000720002455004b97000399531a012d98d50844af77eab700039300479b000399004b972d98d5531a0177eab70844af00479b0003930048a97afc3062406e000387000390b52197624b540023290007083fefb77b11fc62406e7afc30000390000387624b54b521970007080023297b11fc3fefb7000001,
  0x32dd00039f00070e00070e00039f0007457656fe1f7ee200071a0007111f7ee27656fe00071100071a003a217adf260c0c0e6270f5316db100072000646f0c0c0e7adf26316db16270f500646f0007200065b9004b97000399531a0129c3f9048f7777eab700071700673f000399004b9729c3f9531a0177eab7048f7700673f0007170024553a4d983fef030003870003903a513a78212cb522e17849220023290007083fef033a4d9800039000038778212c3a513a784922b522e1000708002329000001,
  0x32dd00000000000000039f00070e00000000000000070e00039f0007450000000000007656fe1f7ee200071a0007110000000000001f7ee27656fe00071100071a003a21000000000000004b97000399531a0129c3f900072000646f000000000000000399004b9729c3f9531a0100646f0007200024550000000000003a4d9862406e0003870003903a513a624b5400232900070800000000000062406e3a4d98000390000387624b543a513a000708002329000001,
  0x100000000000000000000000000072300039600000000000000000000000000039600072300573100000000000000000000000000038d00038a1b89907bed0800000000000000000000000000038a00038d7bed081b8990000e89000000000000000000000000000393000708231aa691e2d826c4f81add4600000000000000000000000000070800039391e2d8231aa61add4626c4f8002455,
  0x4fed00039600071d00071d00039600074500039f005317900cb3287d5f00531700039f287d5f900cb3001d119ce15c1e6caa00039c00038a43489a085be01e6caa9ce15c00038a00039c085be043489a000e899ca5a40858682810631b4757001cf300039000038d0015af0858689ca5a41b4757281063000390001cf30015af00038d0015cdb88a2b91b3f8000387000393001fa500038496a37c89ddd6970d12442fcd91b3f8b88a2b000393000387000384001fa589ddd696a37c442fcd970d12000001,
  0x4fed00039600071d00071d00039600074500039f005317900cb32cbf3700531700039f2cbf37900cb30041659ca5a40858682810631b475700401b0007140858689ca5a41b475728106300071400401b0015cd9ce15c1e6caa00039c00038a9cd34c087f0800038d0015af1e6caa9ce15c00038a00039c087f089cd34c0015af00038d000e89231ce09de254000387000393b889b39c3bfc000384001fa51add28442faf9de254231ce00003930003879c3bfcb889b3001fa5000384442faf1add28000001,
  0x4fed00000000000000039600071d00000000000000071d00039600074500000000000000039f0053171b475728106300000000000000531700039f2810631b47570015cd0000000000009ce15c1e6caa00039c00038a0015af00038d0000000000001e6caa9ce15c00038a00039c00038d0015af000e89000000000000231ce091b3f8000387000393001fa50003841add2889ddd600000000000091b3f8231ce0000393000387000384001fa589ddd61add28000001,
  0x15cd00072300039c00039c00072300573100038d000399900e3f2d9ad900039900038d2d9ad9900e3f000e894fb2f96fab5900596b0003962d99710883d96fab594fb2f900039600596b0883d92d9971000001954aa67018552801f0ae4fe8000e6b00038a000387000727701855954aa6ae4fe82801f000038a000e6b000727000387000745000393000390235e4446cd9026c9a81ada94001fa5000384b41670265cac00039000039346cd90235e441ada9426c9a8000384001fa5265cacb41670001d11,
  0x15cd00072300039c00039c00072300573100038d0003994870f46e5f1c00039900038d6e5f1c4870f4000e894fb2f9745a2d00596b0003962d9971435524745a2d4fb2f900039600596b4355242d9971002b9962e24d6fab592801f002e6b8000e6b00038a00070b002a4f6fab5962e24d02e6b82801f000038a000e6b002a4f00070b0000010003930003902fb92862036026c87cb520ad46a3602a9d58001fa50003840003900003936203602fb928b520ad26c87c2a9d5846a360000384001fa5001d11,
  0x15cd00000000000000072300039c00000000000000039c00072300573100000000000000038d000399235e4a6e5f1c00000000000000039900038d6e5f1c235e4a000e890000000000004fb2f96fab5900596b000396000e6b00038a0000000000006fab594fb2f900039600596b00038a000e6b000001000000000000000393000390235e4462036026c87c1ada94001fa5000384000000000000000390000393620360235e441ada9426c87c000384001fa5001d11,
  0xe890000000000000007200003990000000000000003990007200048a900000000000000039f00038d50a2092faa3100000000000000038d00039f2faa3150a2090015cd00000000000000038a000396213d1f531a012810091b475700000000000000039600038a531a01213d1f1b47572810090007450000000000001d68823dcdde00479b000393001cf30003900007270003870000000000003dcdde1d688200039300479b000390001cf3000387000727000001,
  0x48a900039f00039300039300039f001d11531ad948737000039c000390487370531ad900039000039c0015cd004b970003991ada9426c9a80015af00038d000399004b9726c9a81ada9400038d0015af000e89900dbe7abd9c0003840003966203d89c682a7abce862037e7abd9c900dbe0003960003849c682a6203d862037e7abce800000116b653729059265cacae51e070185598ffde000e6b00038a00038700072772905916b653ae51e0265cac98ffde70185500038a000e6b000727000387000745,
  0x10000000000000000000000000007200007170000000000000000000000000007170007200065b900000000000000000000000000039f00071424d2bc6ea77000000000000000000000000000071400039f6ea77024d2bc00416500000000000000000000000000038a0003871da78b588d3d26f9d58557eb00000000000000000000000000038700038a588d3d1da78b8557eb26f9d5000745,
  0x416500072300569b00569b00072300573100071400071d6203602fb92800071d0007142fb928620360000e8951c959b4fd8500039c0060eb000717000711b4fd8551c9590060eb00039c000711000717003a21996a6411c5be00596b0003962a9d584355247464b911d7e511c5be996a6400039600596b4355242a9d5811d7e57464b9002b999673e83393c275a2801adbfc00038400038a75a1541adaee00070b002a4f3393c29673e81adbfc75a28000038a0003841adaee75a154002a4f00070b000001,
  0x416500072300569b00569b000723002b991720d6b8371e00071a005cefb8371e1720d6005cef00071a005e7500071400071d922cac2a9d5862036030262400071d0007142a9d58922cac302624620360000e8951c959b4fd8511d7e57464b900039c0060eb000717000711b4fd8551c9597464b911d7e50060eb00039c000711000717003a219673e83393c2002a4f00070b75a2801adc1a00038400038a75a1541adaee3393c29673e800070b002a4f1adc1a75a28000038a0003841adaee75a154000001,
  0x416500072300569b00569b00072300573111c5be996a6400039600596b996a6411c5be00596b000396002b9900071400071d922cac2fb9286203602a9d5800071d0007142fb928922cac2a9d58620360000e8951c959b4fd8516c985b70cdd00039c0060eb000717000711b4fd8551c959b70cdd16c9850060eb00039c000711000717003a219673e83393c296747e1adbfc002a4f00070b00038400038a75a1541adaee3393c29673e81adbfc96747e00070b002a4f00038a0003841adaee75a154000001,
  0x416500000000000000072300569b00000000000000569b000723002b9900000000000000071400071d6203602a9d5800000000000000071d0007142a9d58620360000e8900000000000051c959b4fd8500039c0060eb000717000711000000000000b4fd8551c9590060eb00039c000711000717003a210000000000009673e83393c2002a4f00070b00038400038a75a1541adaee0000000000003393c29673e800070b002a4f00038a0003841adaee75a154000001,
  0x10000000000000000000000000003930003990000000000000000000000000003990003930048a900000000000000000000000000038d00039000aff14dbeef00000000000000000000000000039000038d4dbeef00aff10015cd00000000000000000000000000070b0003962107af4685571b431f28138d00000000000000000000000000039600070b4685572107af28138d1b431f002b99,
  0x48a900039f00039300039300039f001d111d695a48737000039c0003904873701d695a00039000039c0015cd004b97000399508cac265cac4872bc170114000399004b97265cac508cac1701144872bc000745482d9b16b9d71ada9426c9a80015af00038d00038a000e6b16b9d7482d9b26c9a81ada9400038d0015af000e6b00038a000e89900dbe7abd9c0003840003966203d89c682a0007270003879c680c62037e7abd9c900dbe0003960003849c682a6203d800038700072762037e9c680c000001,
  0x48a900039f00039300039300039f001d11782d830883f700039c0003900883f7782d8300039000039c0015cd004b97000399508cac2b0b804872bc759f9b000399004b972b0b80508cac759f9b4872bc0032dd482d9b16b6531ada94265cac0015af00038d00070e00319316b653482d9b265cac1ada9400038d0015af00319300070e000745900dbe7abd9c0003840003966203d89c682a7abce86204aa0007270003877abd9c900dbe0003960003849c682a6203d86204aa7abce8000387000727000001,
  0x48a900000000000000039f00039300000000000000039300039f001d11000000000000531ad90883f700039c0003900000000000000883f7531ad900039000039c0015cd000000000000004b970003991ada94265cac0015af00038d000000000000000399004b97265cac1ada9400038d0015af000745000000000000900dbe7abd9c0003840003966203d89c682a0007270003870000000000007abd9c900dbe0003960003849c682a6203d8000387000727000001,
  0x100071a00071700071700071a005e7500039f0003847844cc1e702800038400039f1e70287844cc001d11970d12a7f29400039c0060eb001cf3000390a7f294970d120060eb00039c000390001cf30015cd000387000399b6e44b1d9cff3a20982a7b5c29b6431d56af0003990003871d9cffb6e44b2a7b5c3a20981d56af29b64300074589ddd696a37caf025f33834b1e26542a7ee00015af00038d00038a000e6b96a37c89ddd633834baf025f2a7ee01e265400038d0015af000e6b00038a000e89,
  0x48a900039f00531700531700039f0041657b11fcac8980000396000714ac89807b11fc00071400039600000100479b0003939c3a76231aa600072000070800039300479b231aa69c3a76000708000720002455004b97000399b30b4037a1f862406e7afc3037b4162b07fc000399004b9737a1f8b30b407afc3062406e2b07fc37b4160032dd283d9f4d5553b44ea728369700038700038d1add46267fd400070e0031934d5553283d9f283697b44ea700038d000387267fd41add4600319300070e000745,
  0x32dd00039f00531700531700039f0041657afc3062406e00039600071462406e7afc300007140003960000012b07fc37b4169c3a76231aa600072000070837b4162b07fc231aa69c3a76000708000720002455004b970003999c91d03a1ac84687377b11fc00039300479b000399004b973a1ac89c91d07b11fc46873700479b0003930048a900319300070eb44ea728369700038700038d1add46267fd44d5553283d9f00070e003193283697b44ea700038d000387267fd41add46283d9f4d5553000745,
  0x4fed00039f00531700531700039f0041657b159eac8980000396000714ac89807b159e000714000396000001004f1b00071d9c91d037a1f862406e7afc3000071d004f1b37a1f89c91d07afc3062406e0032dd9de0563a965e9c3a76231aa600072000070800039300479b3a965e9de056231aa69c3a7600070800072000479b000393002455b45cb74d58d7b44ea728369700038700038d00070e0031931add46267fd44d58d7b45cb7283697b44ea700038d00038700319300070e267fd41add46000745,
  0x32dd00000000000000039f00531700000000000000531700039f0041650000000000007afc3062406e00039600071400000000000062406e7afc3000071400039600000100000000000000479b0003939c3a76231aa600072000070800000000000000039300479b231aa69c3a7600070800072000245500000000000000319300070eb44ea728369700038700038d1add46267fd400000000000000070e003193283697b44ea700038d000387267fd41add46000745,
  0x100071a00071700071700071a005e7500039f0003847844cc1e702800038400039f1e70287844cc001d1196a37c89ddd600039c0060eb2a7ee01e265489ddd696a37c0060eb00039c1e26542a7ee0000e89970d12407a9533ecc372228b001cf300039000038d0015af407a95970d1272228b33ecc3000390001cf30015af00038d0015cd000387000399b6e44b1d9cff3a20982a7b5c000e6b00038a29b6431d56af0003990003871d9cffb6e44b2a7b5c3a209800038a000e6b1d56af29b643000745,
  0x100071a00071700071700071a005e7500039f0003847844cc1e702800038400039f1e70287844cc001d119b2ceea7f29400039c0060eb7821a41e4d00a7f2949b2cee0060eb00039c1e4d007821a4003a2196a37c89ddd633834b72228b001cf30003900007110038d789ddd696a37c72228b33834b000390001cf30038d7000711000e89000387000399b6e44b1d9cff3a20982a7b5cb6c1231d79d7000e6b00038a0003990003871d9cffb6e44b2a7b5c3a20981d79d7b6c12300038a000e6b000745,
  0x100000000000000071a00071700000000000000071700071a005e7500000000000000039f0003847844cc1e702800000000000000038400039f1e70287844cc001d1100000000000096a37c89ddd600039c0060eb001cf300039000000000000089ddd696a37c0060eb00039c000390001cf3000e89000000000000000387000399b6e44b1d9cff3a20982a7b5c000e6b00038a0000000000000003990003871d9cffb6e44b2a7b5c3a209800038a000e6b000745,
  0x1784580532dae532dae784580005e7500072300070b00071a005cef00070b000723005cef00071a002b9900070800039900071700673f91e2d82a7a3000039900070800673f0007172a7a3091e2d800245578212c3a513a00039c0060eb5da27d449a535d90509b2d483a513a78212c0060eb00039c449a535da27d9b2d485d9050003a2100038a000390633f743e27c026d72540122b26c4f896a5200007110038d700039000038a3e27c0633f7440122b26d72596a52026c4f80038d7000711000e89,
  0x178212c3a513a3a513a78212c003a2100072300070b00071a005cef00070b000723005cef00071a002b99784922b751dd00072000646f622aa53123ddb751dd78492200646f0007203123dd622aa50065b90007080003995d90502fd54891e2d82a7a3000071700673f0003990007082fd5485d90502a7a3091e2d800673f00071700245500038a0003900007110038d726d72540122b6342f89c8cde26c4f896a52000039000038a0038d700071140122b26d7259c8cde6342f896a52026c4f8000e89,
  0x100072300070b00070b000723002b99784580532dae00071a005cef532dae784580005cef00071a005e7578212c3a513a5da27d3123dd00039c0060eb3a513a78212c3123dd5da27d0060eb00039c003a2100070800039991e2d82a7a3061af002fd54800071700673f0003990007082a7a3091e2d82fd54861af0000673f00071700245500038a00039026d72540122b633f743e27c00007110038d726c4f896a52000039000038a40122b26d7253e27c0633f740038d700071196a52026c4f8000e89,
  0x100000000000078212c3a513a0000000000003a513a78212c003a2100000000000000072300070b00071a005cef00000000000000070b000723005cef00071a002b9900000000000000070800039900071700673f91e2d82a7a3000000000000000039900070800673f0007172a7a3091e2d800245500000000000000038a0003900007110038d726d72540122b26c4f896a52000000000000000039000038a0038d700071140122b26d72596a52026c4f8000e89,
  0x4fed00039600596b00596b000396002b999de254231ce000039c00070b231ce09de25400070b00039c000001004f1b00071d440c872107af00039300070e00071d004f1b2107af440c8700070e0003930032dd00039f005317837eb72ca69b9c3bfcb86d9376e4ca836c9000531700039f2ca69b837eb7b86d939c3bfc836c9076e4ca00416526a8d8898250267ea858202000038d00038426822c76744400401b00071489825026a8d8582020267ea800038400038d76744426822c00071400401b0015cd,
  0x416500072300569b00569b000723005731837eb72ca69b00039600596b2ca69b837eb700596b000396002b999c3bfc3a983e9e4bea231ce000039c00070b3a983e9c3bfc231ce09e4bea00070b00039c000001004f1b00071d481910857be8440c872107af00039300070e00071d004f1b857be84819102107af440c8700070e0003930032dd00401b00071426a8d88985d4267ea858202000038d00038426822c76744400071400401b8985d426a8d8582020267ea800038400038d76744426822c0015cd,
  0x4fed00039f00531700531700039f00416585249746eecf00039600596b46eecf85249700596b000396002b999de2543a983e9c3bfc231ce000039c00070b3a983e9de254231ce09c3bfc00070b00039c000001004f1b00071d481910836c90440c872107af00039300070e00071d004f1b836c904819102107af440c8700070e0003930032dd768ce089825000401b000714267ea858202000038d00038426822c767444898250768ce000071400401b582020267ea800038400038d76744426822c0015cd,
  0x416500000000000000039600596b00000000000000596b000396002b990000000000009c3bfc231ce000039c00070b000000000000231ce09c3bfc00070b00039c000001000000000000004f1b00071d440c872107af00039300070e00000000000000071d004f1b2107af440c8700070e0003930032dd00000000000000401b000714267ea858202000038d00038426822c76744400000000000000071400401b582020267ea800038400038d76744426822c0015cd]

def mergeRep (p : Fin 45) (a : Fin 30) : H :=
  mergeHalf ((Nat.shiftRight (repData p) (5 * a.val)) % 32)

def certificate (p : Fin 45) (a b : Fin 30) : ℕ :=
  (Nat.shiftRight (certData p) (24 * (a.val * (23 - a.val) / 2 + b.val - a.val - 1))) % 16777216

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_0 : ∀ h, slot 0 (mergeRep 0 (slot 0 h)) = slot 0 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_1 : ∀ h, slot 1 (mergeRep 1 (slot 1 h)) = slot 1 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_2 : ∀ h, slot 2 (mergeRep 2 (slot 2 h)) = slot 2 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_3 : ∀ h, slot 3 (mergeRep 3 (slot 3 h)) = slot 3 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_4 : ∀ h, slot 4 (mergeRep 4 (slot 4 h)) = slot 4 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_5 : ∀ h, slot 5 (mergeRep 5 (slot 5 h)) = slot 5 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_6 : ∀ h, slot 6 (mergeRep 6 (slot 6 h)) = slot 6 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_7 : ∀ h, slot 7 (mergeRep 7 (slot 7 h)) = slot 7 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_8 : ∀ h, slot 8 (mergeRep 8 (slot 8 h)) = slot 8 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_9 : ∀ h, slot 9 (mergeRep 9 (slot 9 h)) = slot 9 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_10 : ∀ h, slot 10 (mergeRep 10 (slot 10 h)) = slot 10 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_11 : ∀ h, slot 11 (mergeRep 11 (slot 11 h)) = slot 11 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_12 : ∀ h, slot 12 (mergeRep 12 (slot 12 h)) = slot 12 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_13 : ∀ h, slot 13 (mergeRep 13 (slot 13 h)) = slot 13 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_14 : ∀ h, slot 14 (mergeRep 14 (slot 14 h)) = slot 14 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_15 : ∀ h, slot 15 (mergeRep 15 (slot 15 h)) = slot 15 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_16 : ∀ h, slot 16 (mergeRep 16 (slot 16 h)) = slot 16 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_17 : ∀ h, slot 17 (mergeRep 17 (slot 17 h)) = slot 17 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_18 : ∀ h, slot 18 (mergeRep 18 (slot 18 h)) = slot 18 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_19 : ∀ h, slot 19 (mergeRep 19 (slot 19 h)) = slot 19 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_20 : ∀ h, slot 20 (mergeRep 20 (slot 20 h)) = slot 20 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_21 : ∀ h, slot 21 (mergeRep 21 (slot 21 h)) = slot 21 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_22 : ∀ h, slot 22 (mergeRep 22 (slot 22 h)) = slot 22 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_23 : ∀ h, slot 23 (mergeRep 23 (slot 23 h)) = slot 23 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_24 : ∀ h, slot 24 (mergeRep 24 (slot 24 h)) = slot 24 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_25 : ∀ h, slot 25 (mergeRep 25 (slot 25 h)) = slot 25 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_26 : ∀ h, slot 26 (mergeRep 26 (slot 26 h)) = slot 26 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_27 : ∀ h, slot 27 (mergeRep 27 (slot 27 h)) = slot 27 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_28 : ∀ h, slot 28 (mergeRep 28 (slot 28 h)) = slot 28 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_29 : ∀ h, slot 29 (mergeRep 29 (slot 29 h)) = slot 29 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_30 : ∀ h, slot 30 (mergeRep 30 (slot 30 h)) = slot 30 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_31 : ∀ h, slot 31 (mergeRep 31 (slot 31 h)) = slot 31 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_32 : ∀ h, slot 32 (mergeRep 32 (slot 32 h)) = slot 32 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_33 : ∀ h, slot 33 (mergeRep 33 (slot 33 h)) = slot 33 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_34 : ∀ h, slot 34 (mergeRep 34 (slot 34 h)) = slot 34 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_35 : ∀ h, slot 35 (mergeRep 35 (slot 35 h)) = slot 35 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_36 : ∀ h, slot 36 (mergeRep 36 (slot 36 h)) = slot 36 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_37 : ∀ h, slot 37 (mergeRep 37 (slot 37 h)) = slot 37 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_38 : ∀ h, slot 38 (mergeRep 38 (slot 38 h)) = slot 38 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_39 : ∀ h, slot 39 (mergeRep 39 (slot 39 h)) = slot 39 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_40 : ∀ h, slot 40 (mergeRep 40 (slot 40 h)) = slot 40 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_41 : ∀ h, slot 41 (mergeRep 41 (slot 41 h)) = slot 41 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_42 : ∀ h, slot 42 (mergeRep 42 (slot 42 h)) = slot 42 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_43 : ∀ h, slot 43 (mergeRep 43 (slot 43 h)) = slot 43 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_44 : ∀ h, slot 44 (mergeRep 44 (slot 44 h)) = slot 44 h := by
  decide +kernel

lemma rep_slot : ∀ p h, slot p (mergeRep p (slot p h)) = slot p h := by
  intro p
  fin_cases p
  · exact rep_slot_0
  · exact rep_slot_1
  · exact rep_slot_2
  · exact rep_slot_3
  · exact rep_slot_4
  · exact rep_slot_5
  · exact rep_slot_6
  · exact rep_slot_7
  · exact rep_slot_8
  · exact rep_slot_9
  · exact rep_slot_10
  · exact rep_slot_11
  · exact rep_slot_12
  · exact rep_slot_13
  · exact rep_slot_14
  · exact rep_slot_15
  · exact rep_slot_16
  · exact rep_slot_17
  · exact rep_slot_18
  · exact rep_slot_19
  · exact rep_slot_20
  · exact rep_slot_21
  · exact rep_slot_22
  · exact rep_slot_23
  · exact rep_slot_24
  · exact rep_slot_25
  · exact rep_slot_26
  · exact rep_slot_27
  · exact rep_slot_28
  · exact rep_slot_29
  · exact rep_slot_30
  · exact rep_slot_31
  · exact rep_slot_32
  · exact rep_slot_33
  · exact rep_slot_34
  · exact rep_slot_35
  · exact rep_slot_36
  · exact rep_slot_37
  · exact rep_slot_38
  · exact rep_slot_39
  · exact rep_slot_40
  · exact rep_slot_41
  · exact rep_slot_42
  · exact rep_slot_43
  · exact rep_slot_44

def ChecksFor (p : Fin 45) : Prop := ∀ a b : Fin 30, a < b →
  slot p (mergeRep p a) = a → slot p (mergeRep p b) = b →
  MergeCheck (code p) (slot p) (mergeRep p a) (mergeRep p b) (certificate p a b)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_0 : ChecksFor 0 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_1 : ChecksFor 1 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_2 : ChecksFor 2 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_3 : ChecksFor 3 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_4 : ChecksFor 4 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_5 : ChecksFor 5 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_6 : ChecksFor 6 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_7 : ChecksFor 7 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_8 : ChecksFor 8 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_9 : ChecksFor 9 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_10 : ChecksFor 10 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_11 : ChecksFor 11 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_12 : ChecksFor 12 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_13 : ChecksFor 13 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_14 : ChecksFor 14 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_15 : ChecksFor 15 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_16 : ChecksFor 16 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_17 : ChecksFor 17 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_18 : ChecksFor 18 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_19 : ChecksFor 19 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_20 : ChecksFor 20 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_21 : ChecksFor 21 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_22 : ChecksFor 22 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_23 : ChecksFor 23 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_24 : ChecksFor 24 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_25 : ChecksFor 25 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_26 : ChecksFor 26 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_27 : ChecksFor 27 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_28 : ChecksFor 28 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_29 : ChecksFor 29 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_30 : ChecksFor 30 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_31 : ChecksFor 31 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_32 : ChecksFor 32 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_33 : ChecksFor 33 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_34 : ChecksFor 34 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_35 : ChecksFor 35 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_36 : ChecksFor 36 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_37 : ChecksFor 37 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_38 : ChecksFor 38 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_39 : ChecksFor 39 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_40 : ChecksFor 40 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_41 : ChecksFor 41 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_42 : ChecksFor 42 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_43 : ChecksFor 43 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_44 : ChecksFor 44 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

lemma all_checks : ∀ p, ChecksFor p := by
  intro p
  fin_cases p
  · exact checks_0
  · exact checks_1
  · exact checks_2
  · exact checks_3
  · exact checks_4
  · exact checks_5
  · exact checks_6
  · exact checks_7
  · exact checks_8
  · exact checks_9
  · exact checks_10
  · exact checks_11
  · exact checks_12
  · exact checks_13
  · exact checks_14
  · exact checks_15
  · exact checks_16
  · exact checks_17
  · exact checks_18
  · exact checks_19
  · exact checks_20
  · exact checks_21
  · exact checks_22
  · exact checks_23
  · exact checks_24
  · exact checks_25
  · exact checks_26
  · exact checks_27
  · exact checks_28
  · exact checks_29
  · exact checks_30
  · exact checks_31
  · exact checks_32
  · exact checks_33
  · exact checks_34
  · exact checks_35
  · exact checks_36
  · exact checks_37
  · exact checks_38
  · exact checks_39
  · exact checks_40
  · exact checks_41
  · exact checks_42
  · exact checks_43
  · exact checks_44

lemma actual_eq_iff_slot (t : H → Slot) (ht : Conditions t) (p : Fin 45)
    (hclosed : ∀ h k, closed (code p) h k ↔ slot p h = slot p k)
    (hq : localCode t = code p) (h k : H) : t h = t k ↔ slot p h = slot p k := by
  have hf (a b : H) (hab : slot p a = slot p b) : t a = t b := by
    apply closed_sound t ht.1 ht.2.2.1
    rw [hq]
    exact (hclosed a b).mpr hab
  constructor
  · intro heq
    by_contra hne
    have hrep (a : H) : t (mergeRep p (slot p a)) = t a := hf _ _ (rep_slot p a)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact mergeCheck_false t ht (code p) hq (slot p) hf _ _
        ((hrep h).trans (heq.trans (hrep k).symm)) _
        (all_checks p (slot p h) (slot p k) hlt (rep_slot p h) (rep_slot p k))
    · exact mergeCheck_false t ht (code p) hq (slot p) hf _ _
        ((hrep k).trans (heq.symm.trans (hrep h).symm)) _
        (all_checks p (slot p k) (slot p h) hgt (rep_slot p k) (rep_slot p h))
  · exact hf h k

def classLabel (p : Fin 45) (h : H) : Finset V := canonicalLabel (slot p) h

lemma lower_eq_label (t : H → Slot) (ht : Conditions t) (p : Fin 45)
    (hclosed : ∀ h k, closed (code p) h k ↔ slot p h = slot p k)
    (hq : localCode t = code p) (h : H) : lower t h = classLabel p h :=
  lower_eq_canonicalLabel t (slot p) (actual_eq_iff_slot t ht p hclosed hq) h

end NonlocalMerge

namespace SlotLabels

open FiniteSlots

def maskWord : Fin 45 → ℕ := ![717044977533379493273861595016988673, 1002367299225542016166459398851397633, 604611505078938005145601, 1002367299225542016166459383819026433, 664857864774063428997499861655896065, 654588766363988812382209, 1002367299225542016166459381671544833, 669969200334374568157590724444964865, 669969200334374568014601539387672577, 669969200334374568013475640554571777, 638932419142126625212399110145, 733611447441494013673473, 664857864774055164856154820456777729, 664857864774053983989815887280506881, 634057869695725068654175356929, 717044977533379493270483848052916225, 717044977533379493269357949219815425, 683827378781680577540385718273, 955931948876897827307185555457, 706315584149176803395142971679576066, 970678337718248364052482, 664797490394374026405337395353359362, 664797175957744552022702309626614786, 664797173481866834635183194650973186, 634000294561628441787813073922, 912885697341100285558786, 706315584149176803388387511037395970, 706315584149176803386135713371194370, 673595031880547336003680011266, 708993494785160617563682203657838596, 706315265959903517084148165983086596, 669969187950159723684434691707906052, 664776891091624895910667643955193860, 678546488588751167977026496516, 708993494785160617550171282373478404, 708993494785160617545667687041075204, 676148886475716226165948680196, 671289762982573626245841535656546312, 671289762953559406718079587292565512, 671290082332113543151137181845704712, 640191805832142861178167644168, 664857706273911327560303846415679497, 664797173481866834774783650540044297, 664776891091605996218193770084057097, 634077061351313571196295987209]

def mask (i : Fin 45) (s : Fin 30) : ℕ := (maskWord i / (2 ^ (10 * s.val))) % 1024

def maskSet (m : ℕ) : Finset V := Finset.univ.filter fun v => m.testBit v.val

def label (i : Fin 45) (s : Fin 30) : Finset V :=
  Finset.univ.filter fun v => ∃ h : H, endpoint h = v ∧ SlotTables.slot i h = s

abbrev LabelMatches (i : Fin 45) : Prop := ∀ (s : Fin 30) (v : V),
    (∃ h : H, endpoint h = v ∧ SlotTables.slot i h = s) ↔
      (mask i s).testBit v.val = true

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma labels_checked0 : ∀ j : Fin 9, LabelMatches ⟨0 + j.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma labels_checked1 : ∀ j : Fin 9, LabelMatches ⟨9 + j.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma labels_checked2 : ∀ j : Fin 9, LabelMatches ⟨18 + j.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma labels_checked3 : ∀ j : Fin 9, LabelMatches ⟨27 + j.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma labels_checked4 : ∀ j : Fin 9, LabelMatches ⟨36 + j.val, by omega⟩ := by
  decide +kernel

lemma labels_checked (i : Fin 45) : LabelMatches i := by
  fin_cases i
  · exact labels_checked0 0
  · exact labels_checked0 1
  · exact labels_checked0 2
  · exact labels_checked0 3
  · exact labels_checked0 4
  · exact labels_checked0 5
  · exact labels_checked0 6
  · exact labels_checked0 7
  · exact labels_checked0 8
  · exact labels_checked1 0
  · exact labels_checked1 1
  · exact labels_checked1 2
  · exact labels_checked1 3
  · exact labels_checked1 4
  · exact labels_checked1 5
  · exact labels_checked1 6
  · exact labels_checked1 7
  · exact labels_checked1 8
  · exact labels_checked2 0
  · exact labels_checked2 1
  · exact labels_checked2 2
  · exact labels_checked2 3
  · exact labels_checked2 4
  · exact labels_checked2 5
  · exact labels_checked2 6
  · exact labels_checked2 7
  · exact labels_checked2 8
  · exact labels_checked3 0
  · exact labels_checked3 1
  · exact labels_checked3 2
  · exact labels_checked3 3
  · exact labels_checked3 4
  · exact labels_checked3 5
  · exact labels_checked3 6
  · exact labels_checked3 7
  · exact labels_checked3 8
  · exact labels_checked4 0
  · exact labels_checked4 1
  · exact labels_checked4 2
  · exact labels_checked4 3
  · exact labels_checked4 4
  · exact labels_checked4 5
  · exact labels_checked4 6
  · exact labels_checked4 7
  · exact labels_checked4 8

lemma label_eq_mask (i : Fin 45) (s : Fin 30) : label i s = maskSet (mask i s) := by
  ext v
  simp only [label, maskSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact labels_checked i s v

end SlotLabels

namespace SlotLabels

end SlotLabels

namespace SlotOrbits

open FiniteSlots

def word : Fin 45 → ℕ := ![105043959308623874, 104969483439309342, 1016437415936, 105043376338371210, 58393590189269218, 596667025024, 104819952128796798, 85978298829530330, 28557403578642670, 85977711937907906, 186024800087141, 725516043896, 58393586762330342, 20112277620452554, 78272031943793, 105043375186701410, 104819948213824694, 334977050895389, 335267972259841, 85978427682988230, 723247694432, 58170165482775806, 58168577991586042, 19706175202210034, 77108366715049, 593246998148, 85977843561065694, 28557821711281386, 186027585070177, 104936499226878074, 47515898312942722, 47515894890442886, 641515830438946, 35490131143697, 104935623047196814, 104786962864991258, 334555003284485, 104861733572600838, 104861730154540134, 104818782273334450, 334262958842905, 39179399506970226, 38879166909584042, 9160243775196690, 2925682675233]

def canonical (i : Fin 45) : Fin 45 :=
  if word i % 4 = 0 then 2 else if word i % 4 = 1 then 18 else 0

def vertexPerm (i : Fin 45) : Fin 120 := ⟨((word i / 4) % 128) % 120, by omega⟩

def rename (i : Fin 45) (s : Fin 30) : Fin 30 :=
  if s.val < 2 * (4 + word i % 4) then
    ⟨((word i / 512) / (2 ^ (4 * s.val))) % 16, by omega⟩
  else s

def flip (s : Fin 30) : Fin 30 := ⟨2 * (s.val / 2) + (1 - s.val % 2), by omega⟩

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma rename_injective : ∀ i : Fin 45, Function.Injective (rename i) := by
  unfold Function.Injective
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma rename_flip : ∀ (i : Fin 45) (s : Fin 30), rename i (flip s) = flip (rename i s) := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma masks_permuted : ∀ (i : Fin 45) (s : Fin 30) (v : V),
    (SlotLabels.mask i s).testBit v.val =
      (SlotLabels.mask (canonical i) (rename i s)).testBit (Petersen.permV (vertexPerm i) v).val := by
  decide +kernel

lemma maskSet_image (i : Fin 45) (s : Fin 30) :
    (SlotLabels.maskSet (SlotLabels.mask i s)).image (Petersen.permEquiv (vertexPerm i)) =
      SlotLabels.maskSet (SlotLabels.mask (canonical i) (rename i s)) := by
  ext u
  obtain ⟨v, rfl⟩ := (Petersen.permEquiv (vertexPerm i)).surjective u
  have hh : Petersen.permEquiv (vertexPerm i) v ∈
      (SlotLabels.maskSet (SlotLabels.mask i s)).image (Petersen.permEquiv (vertexPerm i)) ↔
      v ∈ SlotLabels.maskSet (SlotLabels.mask i s) := by simp
  rw [hh]
  simpa [SlotLabels.maskSet, Petersen.permEquiv] using
    congrArg (· = true) (masks_permuted i s v)

end SlotOrbits

namespace FiniteSlots

lemma classified_selected (t : H → Slot) (ht : Conditions t) :
    ∃ i : Fin 45, localCode t = SlotTables.code i ∧
      (∀ h k, t h = t k ↔ SlotTables.slot i h = SlotTables.slot i k) ∧
      ∀ h, lower t h = SlotLabels.label i (SlotTables.slot i h) := by
  obtain ⟨i, hi⟩ := SlotTree.conditions_classified t ht
  refine ⟨i, hi, ?_, ?_⟩
  · exact NonlocalMerge.actual_eq_iff_slot t ht i (SlotTables.closed_iff_slot i) hi
  · intro h
    exact NonlocalMerge.lower_eq_label t ht i (SlotTables.closed_iff_slot i) hi h

end FiniteSlots

namespace TopFormFinite

abbrev V := Fin 10

abbrev I := Fin 15

def ends : I → V × V := ![(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]

abbrev independent (X : Finset V) : Prop :=
  ∀ i : I, ¬ ((ends i).1 ∈ X ∧ (ends i).2 ∈ X)

end TopFormFinite

namespace DagTools

lemma h9_all_eligible_budget {n : ℕ} {D : Dag} {G : Fin n → Fin n → Prop}
    (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (hall : eligSet n D = Finset.univ) (hlen : D.length + 1 ≤ 2 * n) :
    Bplus n D = n ∧ Bzero n D = 0 ∧ D.length + 1 = 2 * n := by
  obtain ⟨b, hb⟩ := sem_exists_pureBranch hG h.1 hC
  have hlo := elig_le_Bplus h.1 b hb
  rw [hall, Finset.card_univ, Fintype.card_fin] at hlo
  have hs := surplus_identity h
  have hsplit := totalSurplus_split n D
  omega

end DagTools

namespace DagTools.I0Selected

open FiniteSlots FourGroupGeometry

set_option maxRecDepth 12000 in
lemma edge_adj : ∀ e : Fin 15, adj (FiniteSlots.edges e).1 (FiniteSlots.edges e).2 := by
  unfold adj
  decide +kernel

set_option maxRecDepth 12000 in
lemma adj_edge : ∀ u v : Fin 10, adj u v ↔
    ∃ e : Fin 15, ((FiniteSlots.edges e).1 = u ∧ (FiniteSlots.edges e).2 = v) ∨
      ((FiniteSlots.edges e).1 = v ∧ (FiniteSlots.edges e).2 = u) := by
  unfold adj
  decide +kernel

set_option maxRecDepth 12000 in
lemma port_adj : ∀ h : H, adj (endpoint h) (endpoint (barH h)) := by
  unfold adj
  decide +kernel

lemma selected_exists {D : Dag} (h : StrictLive 10 D) (hC : sem_Comp 10 adj D)
    (hBp : Bplus 10 D = (eligSet 10 D).card) :
    ∃ t : H → Slot, Conditions t ∧
      (∀ p, t (barH p) = bar (t p)) ∧
      (∀ p, t p ∈ sem_W 10 D (endpoint p)) := by
  classical
  have hex : ∀ e : Fin 15, ∃ p : Slot,
      p ∈ sem_W 10 D (FiniteSlots.edges e).1 ∧
      bar p ∈ sem_W 10 D (FiniteSlots.edges e).2 ∧
      (FiniteSlots.edges e).1 ∉ supp 10 D (src D (bar p)) ∧
      (FiniteSlots.edges e).2 ∉ supp 10 D (src D p) := by
    intro e
    obtain ⟨j, hj, _, _, hu, hv, s, hus, hvs, hvs', hus'⟩ :=
      sem_joint_meeting FourCase.graph h.1 hC (edge_adj e)
    exact ⟨(j,s), sem_mem_W.mpr ⟨hj, hus, hu⟩,
      sem_mem_W.mpr ⟨hj, hvs', hv⟩, hus', hvs⟩
  choose p hp using hex
  let t : H → Slot := fun q => if q.2 then bar (p q.1) else p q.1
  have hb : ∀ q, t (barH q) = bar (t q) := by
    rintro ⟨e, b⟩
    cases b <;> simp [t, barH, bar]
  have hw : ∀ q, t q ∈ sem_W 10 D (endpoint q) := by
    rintro ⟨e, b⟩
    cases b
    · exact (hp e).1
    · exact (hp e).2.1
  refine ⟨t, ?_, hb, hw⟩
  apply conditions_of_exits t (fun s => supp 10 D (src D s)) (sem_W 10 D)
    hb hw
  · intro v s hs
    exact (sem_mem_W.mp hs).2.1
  · rintro ⟨e,b⟩
    cases b
    · exact (hp e).2.2.1
    · simpa [t, barH, bar, endpoint] using (hp e).2.2.2
  · intro v
    have hbudget := h9_exit_budget_tight FourCase.graph h hC hBp v
    omega
  · intro v A hA hv
    have hind : ∀ a ∈ A, ∀ b ∈ A, ¬ adj a b := by
      intro a ha b hb' hab
      obtain ⟨e, he | he⟩ := (adj_edge a b).mp hab
      · exact hA e ⟨he.1.symm ▸ ha, he.2.symm ▸ hb'⟩
      · exact hA e ⟨he.1.symm ▸ hb', he.2.symm ▸ ha⟩
    have hnb : ∃ a ∈ A, adj v a := by
      obtain ⟨q, hq, ha⟩ := hv
      exact ⟨endpoint (barH q), ha, hq ▸ port_adj q⟩
    obtain ⟨j, s, hj, _, hs, hg, hd⟩ :=
      sem_exposure FourCase.graph h.1 hC A hind v hnb
    exact ⟨(j,s), sem_mem_W.mpr ⟨hj, hs, hg⟩, hd⟩

lemma classified_exists {D : Dag} (h : StrictLive 10 D) (hC : sem_Comp 10 adj D)
    (hBp : Bplus 10 D = (eligSet 10 D).card) :
    ∃ (t : H → Slot) (i : Fin 45),
      (∀ p, t (barH p) = bar (t p)) ∧
      (∀ p, t p ∈ sem_W 10 D (endpoint p)) ∧
      (∀ p q, t p = t q ↔ SlotTables.slot i p = SlotTables.slot i q) := by
  obtain ⟨t, ht, hb, hw⟩ := selected_exists h hC hBp
  obtain ⟨i, _, heq, _⟩ := classified_selected t ht
  exact ⟨t, i, hb, hw, heq⟩

end DagTools.I0Selected

namespace SlotGateIds

open FiniteSlots

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma slot_bar : ∀ (p : Fin 45) (h : H),
    SlotTables.slot p (barH h) = SlotOrbits.flip (SlotTables.slot p h) := by
  decide +kernel

end SlotGateIds

namespace SlotPackages

open FiniteSlots

def index {m : ℕ} (hm : m ≤ 15) (j : Fin m) (s : Bool) : Fin 30 :=
  ⟨2 * j.val + if s then 1 else 0, by cases s <;> simp only [Bool.false_eq_true,
    if_false, if_true] <;> omega⟩

lemma index_flip {m : ℕ} (hm : m ≤ 15) (j : Fin m) :
    SlotOrbits.flip (index hm j false) = index hm j true := by
  apply Fin.ext
  dsimp [SlotOrbits.flip, index]
  omega

lemma index_inj {m : ℕ} (hm : m ≤ 15) {j k : Fin m}
    (h : index hm j false = index hm k false) : j = k := by
  apply Fin.ext
  have hv := congrArg Fin.val h
  dsimp [index] at hv
  omega

lemma index_even_ne_odd {m : ℕ} (hm : m ≤ 15) (j k : Fin m) :
    index hm j false ≠ index hm k true := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [index] at hv
  omega

lemma canonical_packages {m : ℕ} (hm : m ≤ 15) (i : Fin 45)
    (S : Fin m → Bool → Finset V)
    (hmask : ∀ j s, S j s = SlotLabels.maskSet
      (SlotLabels.mask (SlotOrbits.canonical i) (index hm j s)))
    (hne : ∀ j, (S j false).Nonempty)
    (t : H → Slot) (W : V → Finset Slot)
    (hb : ∀ h, t (barH h) = bar (t h))
    (heq : ∀ h k, t h = t k ↔ SlotTables.slot i h = SlotTables.slot i k)
    (hw : ∀ h, t h ∈ W (endpoint h)) :
    ∃ P : Fin m → Slot, Function.Injective (fun j => (P j).1) ∧
      ∀ j s v, v ∈ S j s → (if s then bar (P j) else P j) ∈
        W ((Petersen.permEquiv (SlotOrbits.vertexPerm i)).symm v) := by
  classical
  let σ := Petersen.permEquiv (SlotOrbits.vertexPerm i)
  let τ : Equiv.Perm (Fin 30) := Equiv.ofBijective (SlotOrbits.rename i)
    (Finite.injective_iff_bijective.mp (SlotOrbits.rename_injective i))
  have horbit (s : Fin 30) : (SlotLabels.label i s).image σ =
      SlotLabels.maskSet (SlotLabels.mask (SlotOrbits.canonical i) (SlotOrbits.rename i s)) := by
    rw [SlotLabels.label_eq_mask]
    exact SlotOrbits.maskSet_image i s
  have hpre (s : Fin 30) (v : V)
      (hv : v ∈ SlotLabels.maskSet (SlotLabels.mask (SlotOrbits.canonical i) s)) :
      ∃ h : H, σ (endpoint h) = v ∧ SlotOrbits.rename i (SlotTables.slot i h) = s := by
    have hτ : SlotOrbits.rename i (τ.symm s) = s := τ.apply_symm_apply s
    have hmemb : v ∈ (SlotLabels.label i (τ.symm s)).image σ := by
      rw [horbit, hτ]
      exact hv
    obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp hmemb
    obtain ⟨h, he, hs⟩ := (Finset.mem_filter.mp hw).2
    refine ⟨h, ?_, ?_⟩
    · simpa only [he] using hwv
    · rw [hs]
      exact hτ
  have hex : ∀ j : Fin m, ∃ h : H,
      SlotOrbits.rename i (SlotTables.slot i h) = index hm j false := by
    intro j
    obtain ⟨v, hv⟩ := hne j
    rw [hmask] at hv
    obtain ⟨h, _, hh⟩ := hpre (index hm j false) v hv
    exact ⟨h, hh⟩
  choose pick hpick using hex
  have hbar (j : Fin m) :
      SlotOrbits.rename i (SlotTables.slot i (barH (pick j))) = index hm j true := by
    rw [SlotGateIds.slot_bar, SlotOrbits.rename_flip, hpick, index_flip]
  refine ⟨fun j => t (pick j), ?_, ?_⟩
  · intro j k hgate
    by_cases hbit : (t (pick j)).2 = (t (pick k)).2
    · have ht : t (pick j) = t (pick k) := Prod.ext hgate hbit
      have hc := congrArg (SlotOrbits.rename i) ((heq _ _).mp ht)
      rw [hpick, hpick] at hc
      exact index_inj hm hc
    · have ht : t (pick j) = bar (t (pick k)) := by
        apply Prod.ext
        · exact hgate
        · cases hj : (t (pick j)).2 <;> cases hk : (t (pick k)).2 <;>
            simp_all [bar]
      have hc := congrArg (SlotOrbits.rename i)
        ((heq (pick j) (barH (pick k))).mp (ht.trans (hb (pick k)).symm))
      rw [hpick, hbar] at hc
      exact False.elim (index_even_ne_odd hm j k hc)
  · intro j s v hv
    rw [hmask] at hv
    obtain ⟨h, hvh, hcode⟩ := hpre (index hm j s) v hv
    have hend : endpoint h = σ.symm v := by
      apply σ.injective
      simpa only [Equiv.apply_symm_apply] using hvh
    have hmem := hw h
    rw [hend] at hmem
    cases s
    · have hs : t h = t (pick j) := (heq _ _).mpr
        (SlotOrbits.rename_injective i (hcode.trans (hpick j).symm))
      simpa only [hs, Bool.false_eq_true, if_false] using hmem
    · have hs : t h = bar (t (pick j)) :=
        ((heq _ _).mpr (SlotOrbits.rename_injective i
          (hcode.trans (hbar j).symm))).trans (hb (pick j))
      simpa only [hs, if_true] using hmem

lemma six_masks : ∀ (j : Fin 6) (s : Bool),
    SixCase.side j s = SlotLabels.maskSet (SlotLabels.mask 0 (index (by decide) j s)) := by
  decide +kernel

lemma five_masks : ∀ (j : Fin 5) (s : Bool),
    FiveGroupGeometry.sides j s =
      SlotLabels.maskSet (SlotLabels.mask 18 (index (by decide) j s)) := by
  decide +kernel

def fourSide (j : Fin 4) (s : Bool) : Finset V :=
  if s then ![{1}, {8}, DagTools.FourCase.R, {9}] j
  else ![{0}, {3}, DagTools.FourCase.Q, {7}] j

lemma four_masks : ∀ (j : Fin 4) (s : Bool),
    fourSide j s = SlotLabels.maskSet (SlotLabels.mask 2 (index (by decide) j s)) := by
  decide +kernel

lemma six_packages (i : Fin 45) (hi : SlotOrbits.canonical i = 0)
    (t : H → Slot) (W : V → Finset Slot)
    (hb : ∀ h, t (barH h) = bar (t h))
    (heq : ∀ h k, t h = t k ↔ SlotTables.slot i h = SlotTables.slot i k)
    (hw : ∀ h, t h ∈ W (endpoint h)) :
    ∃ P : Fin 6 → Slot, Function.Injective (fun j => (P j).1) ∧
      ∀ j s v, v ∈ SixCase.side j s → (if s then bar (P j) else P j) ∈
        W ((Petersen.permEquiv (SlotOrbits.vertexPerm i)).symm v) := by
  apply canonical_packages (by decide) i SixCase.side ?_ ?_ t W hb heq hw
  · intro j s
    rw [hi]
    exact six_masks j s
  · decide +kernel

lemma five_packages (i : Fin 45) (hi : SlotOrbits.canonical i = 18)
    (t : H → Slot) (W : V → Finset Slot)
    (hb : ∀ h, t (barH h) = bar (t h))
    (heq : ∀ h k, t h = t k ↔ SlotTables.slot i h = SlotTables.slot i k)
    (hw : ∀ h, t h ∈ W (endpoint h)) :
    ∃ P : Fin 5 → Slot, Function.Injective (fun j => (P j).1) ∧
      ∀ j s v, v ∈ FiveGroupGeometry.sides j s → (if s then bar (P j) else P j) ∈
        W ((Petersen.permEquiv (SlotOrbits.vertexPerm i)).symm v) := by
  apply canonical_packages (by decide) i FiveGroupGeometry.sides ?_ ?_ t W hb heq hw
  · intro j s
    rw [hi]
    exact five_masks j s
  · decide +kernel

lemma four_packages (i : Fin 45) (hi : SlotOrbits.canonical i = 2)
    (t : H → Slot) (W : V → Finset Slot)
    (hb : ∀ h, t (barH h) = bar (t h))
    (heq : ∀ h k, t h = t k ↔ SlotTables.slot i h = SlotTables.slot i k)
    (hw : ∀ h, t h ∈ W (endpoint h)) :
    ∃ P : Fin 4 → Slot, Function.Injective (fun j => (P j).1) ∧
      ∀ j s v, v ∈ fourSide j s → (if s then bar (P j) else P j) ∈
        W ((Petersen.permEquiv (SlotOrbits.vertexPerm i)).symm v) := by
  apply canonical_packages (by decide) i fourSide ?_ ?_ t W hb heq hw
  · intro j s
    rw [hi]
    exact four_masks j s
  · decide +kernel

end SlotPackages

namespace DagTools.I0Case

open FourGroupGeometry

set_option maxRecDepth 12000 in
lemma related_eq_adj : ∀ u v : Fin 10, Petersen.related u v = true ↔ adj u v := by
  unfold adj
  decide +kernel

lemma permutation_adj (k : Fin 120) (u v : Fin 10) :
    adj (Petersen.permEquiv k u) (Petersen.permEquiv k v) ↔ adj u v := by
  rw [← related_eq_adj, ← related_eq_adj]
  change Petersen.related (Petersen.permV k u) (Petersen.permV k v) = true ↔ _
  rw [Petersen.permVgood k u v]

lemma canonical_cases (i : Fin 45) : SlotOrbits.canonical i = 0 ∨
    SlotOrbits.canonical i = 18 ∨ SlotOrbits.canonical i = 2 := by
  unfold SlotOrbits.canonical
  split
  · exact Or.inr (Or.inr rfl)
  · split
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl

lemma tight_impossible {D : Dag} (h : StrictLive 10 D) (hC : sem_Comp 10 adj D)
    (hBp : Bplus 10 D = (eligSet 10 D).card) (hB0 : Bzero 10 D = 0) : False := by
  classical
  obtain ⟨t, i, hb, hw, heq⟩ := I0Selected.classified_exists h hC hBp
  let σ := Petersen.permEquiv (SlotOrbits.vertexPerm i)
  let E := relabel σ D
  have hE : StrictLive 10 E := relabel_strictLive σ h
  have hEC : sem_Comp 10 adj E := relabel_comp σ h hC
    (permutation_adj (SlotOrbits.vertexPerm i))
  have hEBp : Bplus 10 E = (eligSet 10 E).card := relabel_tight_budget σ h.1 h.2.2 hBp
  have hEB0 : Bzero 10 E = 0 := (relabel_Bzero σ h.1 h.2.2).trans hB0
  have hW (v : Fin 10) : sem_W 10 E v = sem_W 10 D (σ.symm v) :=
    relabel_W_preimage σ h.1 v
  rcases canonical_cases i with hi | hi | hi
  · obtain ⟨P, hP, hs⟩ := SlotPackages.six_packages i hi t (sem_W 10 D) hb heq hw
    apply SixCase.canonical_six_impossible FourCase.graph hE hEC hEBp hEB0 P hP
    · intro j s v hv
      rw [hW]
      exact hs j s v hv
    · unfold adj
      decide +kernel
    · unfold adj
      decide +kernel
  · obtain ⟨P, hP, hs⟩ := SlotPackages.five_packages i hi t (sem_W 10 D) hb heq hw
    apply FiveCase.canonical_five_tight_impossible hE hEC hEBp hEB0 P hP
    intro j s v hv
    rw [hW]
    exact hs j s v hv
  · obtain ⟨P, hP, hs⟩ := SlotPackages.four_packages i hi t (sem_W 10 D) hb heq hw
    have hslots (j : Fin 4) (s : Bool) (v : Fin 10) (hv : v ∈ SlotPackages.fourSide j s) :
        (if s then FiniteSlots.bar (P j) else P j) ∈ sem_W 10 E v := by
      rw [hW]
      exact hs j s v hv
    apply FourCase.canonical_four_tight_impossible hE hEC hEBp hEB0
      (P 2) (P 0) (P 1) (P 3)
    · exact fun he => (by decide : (0 : Fin 4) ≠ 1) (hP he)
    · exact fun he => (by decide : (0 : Fin 4) ≠ 3) (hP he)
    · exact fun he => (by decide : (1 : Fin 4) ≠ 3) (hP he)
    · exact fun he => (by decide : (0 : Fin 4) ≠ 2) (hP he)
    · exact fun he => (by decide : (1 : Fin 4) ≠ 2) (hP he)
    · exact fun he => (by decide : (3 : Fin 4) ≠ 2) (hP he)
    · intro v hv
      exact hslots 2 false v hv
    · intro v hv
      exact hslots 2 true v hv
    · exact hslots 0 false 0 (by decide +kernel)
    · exact hslots 0 true 1 (by decide +kernel)
    · exact hslots 1 false 3 (by decide +kernel)
    · exact hslots 1 true 8 (by decide +kernel)
    · exact hslots 3 false 7 (by decide +kernel)
    · exact hslots 3 true 9 (by decide +kernel)

lemma all_eligible_impossible {D : Dag} (h : StrictLive 10 D) (hC : sem_Comp 10 adj D)
    (hall : eligSet 10 D = Finset.univ) (hlen : D.length ≤ 19) : False := by
  obtain ⟨hBp, hB0, _⟩ := h9_all_eligible_budget FourCase.graph h hC hall (by omega)
  have he : Bplus 10 D = (eligSet 10 D).card := by
    rw [hall, Finset.card_univ, Fintype.card_fin]
    exact hBp
  exact tight_impossible h hC he hB0

lemma zero_ineligible_impossible {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 adj D) (hi : (ineligSet 10 D).card = 0)
    (hlen : D.length ≤ 19) : False := by
  have hnone : ineligSet 10 D = ∅ := Finset.card_eq_zero.mp hi
  have hall : eligSet 10 D = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro v
    by_contra hv
    have hm : v ∈ ineligSet 10 D := sem_mem_inelig.mpr hv
    rw [hnone] at hm
    exact Finset.notMem_empty v hm
  exact all_eligible_impossible h hC hall hlen

end DagTools.I0Case

namespace DagTools.I0Selected

open FiniteSlots FourGroupGeometry

end DagTools.I0Selected

namespace DagTools.ExitCapCanonical

end DagTools.ExitCapCanonical

namespace DagTools.ExitCapCanonical

open FiniteSlots FourGroupGeometry

end DagTools.ExitCapCanonical

namespace DagTools.ExitCapCase

open FiniteSlots FourGroupGeometry

end DagTools.ExitCapCase

namespace DagTools.ExitCapCase

open FiniteSlots FourGroupGeometry

end DagTools.ExitCapCase

end I0Proof

namespace FoundationI0

open DagTools PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 12000 in
lemma graph_iff : ∀ u v, DeskDriver.adj u v ↔ I0Proof.FourGroupGeometry.adj u v := by
  unfold DeskDriver.adj I0Proof.FourGroupGeometry.adj
  decide +kernel

lemma graph_agreement : DeskDriver.adj = I0Proof.FourGroupGeometry.adj := by
  funext u v
  exact propext (graph_iff u v)

lemma zero_ineligible_impossible {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 DeskDriver.adj D) (hi : (ineligSet 10 D).card = 0)
    (hlen : D.length ≤ 19) : False := by
  apply I0Proof.DagTools.I0Case.zero_ineligible_impossible h _ hi hlen
  simpa only [← graph_agreement] using hC

lemma circuit_remaining_cases (C : Circuit) (hm : Monotone2 C) (hs : C.size ≤ 19)
    (hf : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = DeskDriver.target x) :
    ∃ D : Dag, StrictLive 10 D ∧ sem_Comp 10 DeskDriver.adj D ∧ D.length ≤ 19 ∧
      ((ineligSet 10 D).card = 1 ∨ (ineligSet 10 D).card = 2 ∨
        ineligSet 10 D = ({1, 4, 5} : Finset (Fin 10))) := by
  obtain ⟨D, hD, hc, hlen, hcases⟩ := FoundationI4.circuit_remaining_cases C hm hs hf
  refine ⟨D, hD, hc, hlen, ?_⟩
  rcases hcases with hcard | hN
  · have hn : (ineligSet 10 D).card ≠ 0 :=
      fun hz => zero_ineligible_impossible hD hc hz hlen
    have hsmall : (ineligSet 10 D).card = 1 ∨ (ineligSet 10 D).card = 2 := by omega
    exact hsmall.elim Or.inl (Or.inr ∘ Or.inl)
  · exact Or.inr (Or.inr hN)

end FoundationI0

end PEqualNP.Outside.L_meta_2590_aux
