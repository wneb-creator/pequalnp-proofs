import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2590_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def target (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)

def dirtySix : Circuit where
  gates := [
    ⟨.or, [0, 2]⟩,
    ⟨.or, [10, 6]⟩,
    ⟨.or, [1, 4]⟩,
    ⟨.or, [12, 5]⟩,
    ⟨.and, [11, 13]⟩,
    ⟨.or, [0, 1]⟩,
    ⟨.and, [14, 15]⟩,
    ⟨.or, [2, 4]⟩,
    ⟨.or, [17, 8]⟩,
    ⟨.and, [3, 18]⟩,
    ⟨.or, [2, 5]⟩,
    ⟨.or, [20, 9]⟩,
    ⟨.and, [7, 21]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.and, [8, 23]⟩,
    ⟨.or, [4, 6]⟩,
    ⟨.and, [9, 25]⟩,
    ⟨.or, [16, 19]⟩,
    ⟨.or, [22, 24]⟩,
    ⟨.or, [27, 28]⟩,
    ⟨.or, [29, 26]⟩]
  output := 30

def isAnd : GateOp → Bool
  | .and => true
  | _ => false

lemma dirtySix_size : dirtySix.size = 21 := rfl

lemma dirtySix_and_count : (dirtySix.gates.filter (fun g => isAnd g.op)).length = 6 := rfl

lemma dirtySix_monotone : Monotone2 dirtySix := by
  simp [Monotone2, dirtySix]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma dirtySix_eval_bits (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Bool) :
    dirtySix.eval [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9] =
      ((((x0 || x2 || x6) && (x1 || x4 || x5)) && (x0 || x1)) || (x3 && (x2 || x4 || x8)) || (x7 && (x2 || x5 || x9)) || (x8 && (x5 || x6)) || (x9 && (x4 || x6))) := by
  simp [dirtySix, Circuit.eval, Circuit.wires, GateOp.eval, Bool.or_assoc]

lemma doubleStar (a b c d e f : Bool) :
    (((a || b || c) && (d || e || f)) && (a || d)) =
      ((a && d) || (a && e) || (a && f) || (b && d) || (c && d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> rfl

lemma dirtySix_correct_bits (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Bool) :
    dirtySix.eval [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9] =
      ((x0 && x1) || (x1 && x2) || (x2 && x3) || (x3 && x4) || (x4 && x0) || (x0 && x5) || (x1 && x6) || (x2 && x7) || (x3 && x8) || (x4 && x9) || (x5 && x7) || (x7 && x9) || (x9 && x6) || (x6 && x8) || (x8 && x5)) := by
  rw [dirtySix_eval_bits, doubleStar]
  simp only [Bool.and_or_distrib_left, Bool.and_or_distrib_right]
  ac_rfl

lemma dirtySix_correct (x : Fin 10 → Bool) : dirtySix.eval (List.ofFn x) = target x := by
  simpa [target, List.ofFn_succ] using
    dirtySix_correct_bits (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9)

lemma dirtySix_bad_gate :
    (dirtySix.wires (List.ofFn (fun i : Fin 10 => decide (i = 2 ∨ i = 4)))).getD 14 false = true ∧
    target (fun i : Fin 10 => decide (i = 2 ∨ i = 4)) = false := by
  decide +kernel

abbrev BinaryGate := Bool × ℕ × ℕ

def binaryOp (t a b : Bool) : Bool := if t then a && b else a || b

def binaryStep (w : List Bool) (g : BinaryGate) : List Bool :=
  w ++ [binaryOp g.1 (w.getD g.2.1 false) (w.getD g.2.2 false)]

def binaryRun (gs : List BinaryGate) (w : List Bool) : List Bool :=
  gs.foldl binaryStep w

def binaryStrict : ℕ → List BinaryGate → Prop
  | _, [] => True
  | n, g :: gs => g.2.1 < n ∧ g.2.2 < n ∧ binaryStrict (n + 1) gs

def binaryDual (g : BinaryGate) : BinaryGate := (!g.1, g.2.1, g.2.2)

lemma getD_complement (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (w.map Bool.not).getD i false = !(w.getD i false) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

lemma binaryOp_complement (t a b : Bool) :
    binaryOp (!t) (!a) (!b) = !(binaryOp t a b) := by
  cases t <;> cases a <;> cases b <;> rfl

lemma binaryStep_length (w : List Bool) (g : BinaryGate) :
    (binaryStep w g).length = w.length + 1 := by
  simp [binaryStep]

lemma binaryStep_complement (w : List Bool) (g : BinaryGate)
    (ha : g.2.1 < w.length) (hb : g.2.2 < w.length) :
    binaryStep (w.map Bool.not) (binaryDual g) = (binaryStep w g).map Bool.not := by
  simp only [binaryStep, binaryDual, getD_complement w _ ha,
    getD_complement w _ hb, binaryOp_complement, List.map_append,
    List.map_cons, List.map_nil]

lemma binaryRun_complement (gs : List BinaryGate) (w : List Bool)
    (h : binaryStrict w.length gs) :
    binaryRun (gs.map binaryDual) (w.map Bool.not) =
      (binaryRun gs w).map Bool.not := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rcases h with ⟨ha, hb, htail⟩
    simp only [List.map_cons, binaryRun, List.foldl_cons]
    rw [binaryStep_complement w g ha hb]
    exact ih (binaryStep w g) (by simpa only [binaryStep_length] using htail)

lemma binaryRun_length (gs : List BinaryGate) (w : List Bool) :
    (binaryRun gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [binaryRun]
  | cons g gs ih =>
    simpa [binaryRun, List.foldl_cons, binaryStep_length, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using ih (binaryStep w g)

lemma binaryEval_complement (gs : List BinaryGate) (w : List Bool) (o : ℕ)
    (h : binaryStrict w.length gs) (ho : o < w.length + gs.length) :
    (binaryRun (gs.map binaryDual) (w.map Bool.not)).getD o false =
      !((binaryRun gs w).getD o false) := by
  rw [binaryRun_complement gs w h]
  exact getD_complement _ _ (by simpa only [binaryRun_length] using ho)

lemma binaryDual_and_count (gs : List BinaryGate) :
    ((gs.map binaryDual).filter (fun g => g.1)).length =
      (gs.filter (fun g => !g.1)).length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    cases h : g.1 <;> simp [binaryDual, h, ih]

namespace C6

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

end SemArms
end DagTools

open DagTools

abbrev V := Fin 6

def adj (u v : V) : Prop :=
  (u.val, v.val) ∈ [(0,3),(0,4),(1,3),(1,5),(2,4),(2,5)] ∨
  (v.val, u.val) ∈ [(0,3),(0,4),(1,3),(1,5),(2,4),(2,5)]

def Independent (I : Finset V) : Prop := ∀ u ∈ I, ∀ v ∈ I, ¬ adj u v

set_option synthInstance.maxSize 4096 in
lemma graph_ok : sem_Gr adj := by
  unfold sem_Gr adj
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 10000000 in
set_option synthInstance.maxSize 4096 in
lemma independent_facts : ∀ I : Finset V, Independent I →
    I.card ≤ 3 ∧ (I.card = 3 → ∀ v ∉ I,
      ∃ a ∈ I, ∃ b ∈ I, a ≠ b ∧ adj v a ∧ adj v b) := by
  unfold Independent adj
  decide +kernel

lemma inelig_independent {D : Dag} (h : StrictLive 6 D) (hc : sem_Comp 6 adj D) :
    Independent (ineligSet 6 D) := by
  intro u hu v hv huv
  rcases sem_elig_cover graph_ok h hc huv with he | he
  · exact (sem_mem_inelig.mp hu) he
  · exact (sem_mem_inelig.mp hv) he

lemma small_budget {D : Dag} (h : StrictLive 6 D) (hc : sem_Comp 6 adj D)
    (hl : D.length ≤ 8) :
    ∃ b : V → ℕ, PureBranch 6 D b ∧ (ineligSet 6 D).card = 3 ∧
      (eligSet 6 D).card = 3 ∧ Bplus 6 D = 3 ∧ Bzero 6 D = 0 ∧
      residualUnits 6 D b = ∅ := by
  classical
  obtain ⟨b, hb⟩ := sem_exists_pureBranch graph_ok h.1 hc
  have hi := (independent_facts _ (inelig_independent h hc)).1
  have he := elig_le_Bplus h.1 b hb
  have hs := surplus_identity h
  have hz := totalSurplus_split 6 D
  have hn := inelig_card_add 6 D
  have hr := card_residual h.1 b hb
  refine ⟨b, hb, by omega, by omega, by omega, by omega, ?_⟩
  exact Finset.card_eq_zero.mp (by omega)

lemma exits_le_two {D : Dag} (h : StrictLive 6 D) (hc : sem_Comp 6 adj D)
    (hl : D.length ≤ 8) (v : V) : (sem_W 6 D v).card ≤ 2 := by
  classical
  obtain ⟨b, hb, _, _, _, _, hr⟩ := small_budget h hc hl
  have hcount := sem_code_count graph_ok h hc b hb v
  rw [hr] at hcount
  simp only [Finset.filter_empty, Finset.card_empty, add_zero] at hcount
  have hle : (({v} : Finset V) ∩ eligSet 6 D).card ≤ 1 := by
    calc
      _ ≤ ({v} : Finset V).card := Finset.card_le_card Finset.inter_subset_left
      _ = 1 := Finset.card_singleton v
  omega

lemma consumer_same_gate {D : Dag} {v w : V} {e f : ℕ × Bool}
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

def andGates (D : Dag) : Finset ℕ :=
  (Finset.range D.length).filter (fun j => tag D j = true)

def Consumer (D : Dag) (v : V) (e : ℕ × Bool) : Prop :=
  e.1 < D.length ∧ tag D e.1 = true ∧ supp 6 D (src D e) = {v} ∧
    supp 6 D (6 + e.1) = ∅ ∧
    (∀ a, adj v a → a ∈ supp 6 D (src D (sem_bar e))) ∧
    sem_W 6 D v = {e}

lemma consumer_exists {D : Dag} (h : StrictLive 6 D) (hc : sem_Comp 6 adj D)
    {v : V} (hv : v ∈ ineligSet 6 D) : ∃ e, Consumer D v e := by
  obtain ⟨e, he1, he2, he3, he4, he5, he6, _⟩ := sem_inelig_consumer graph_ok h hc hv
  exact ⟨e, he1, he2, he3, he4, he5, he6⟩

lemma consumers_injective {D : Dag} {v w : V} {e f : ℕ × Bool}
    (he : Consumer D v e) (hf : Consumer D w f) (hgate : e.1 = f.1) : v = w :=
  consumer_same_gate he.2.2.1 hf.2.2.1 he.2.2.2.2.1 hgate

lemma all_and_consumers {D : Dag} (h : StrictLive 6 D) (hc : sem_Comp 6 adj D)
    (hl : D.length ≤ 8) (ha : (andGates D).card ≤ 3) {j : ℕ}
    (hj : j < D.length) (ht : tag D j = true) :
    ∃ v ∈ ineligSet 6 D, ∃ e, Consumer D v e ∧ e.1 = j := by
  classical
  obtain ⟨_, _, hI, _, _, _, _⟩ := small_budget h hc hl
  let T := {v : V // v ∈ ineligSet 6 D}
  have hex : ∀ v : T, ∃ e, Consumer D v.val e := fun v => consumer_exists h hc v.property
  choose e he using hex
  have hinj : Function.Injective (fun v : T => (e v).1) := by
    intro v w hvw
    apply Subtype.ext
    exact consumers_injective (he v) (he w) hvw
  let S := (Finset.univ : Finset T).image (fun v => (e v).1)
  have hsub : S ⊆ andGates D := by
    intro k hk
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (he v).1, (he v).2.1⟩
  have hS : S.card = 3 := by
    dsimp only [S]
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
    simpa only [T, Fintype.card_coe] using hI
  have heq : S = andGates D := Finset.eq_of_subset_of_card_le hsub (by omega)
  have hm : j ∈ S := by
    rw [heq]
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, ht⟩
  obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hm
  exact ⟨v.val, v.property, e v, he v, hv⟩

lemma opposite_clean {D : Dag} (h : StrictLive 6 D) (hc : sem_Comp 6 adj D)
    (hl : D.length ≤ 8) {v : V} (_hv : v ∈ ineligSet 6 D) {e : ℕ × Bool}
    (he : Consumer D v e) {w : V} (hw : w ∈ supp 6 D (src D (sem_bar e))) : adj v w := by
  classical
  by_contra hn
  by_cases hwi : w ∈ ineligSet 6 D
  · have hp := sem_inelig_pure graph_ok h.1 hc hwi hw
    obtain ⟨a, hva, haw⟩ := graph_ok.2.2.2 v w
    have hm := he.2.2.2.2.1 a hva
    rw [hp, Finset.mem_singleton] at hm
    exact haw hm
  · obtain ⟨_, _, hI, _, _, _, _⟩ := small_budget h hc hl
    obtain ⟨a, ha, b, hb, hab, hwa, hwb⟩ :=
      (independent_facts _ (inelig_independent h hc)).2 hI w hwi
    obtain ⟨ea, hea⟩ := consumer_exists h hc ha
    obtain ⟨eb, heb⟩ := consumer_exists h hc hb
    have hmem : ∀ {u : V} {f : ℕ × Bool}, Consumer D u f → adj w u →
        sem_bar f ∈ sem_W 6 D w := by
      intro u f hf hwu
      apply sem_mem_W.mpr
      refine ⟨hf.1, hf.2.2.2.2.1 w (graph_ok.1 _ _ hwu), ?_⟩
      change w ∉ supp 6 D (6 + f.1)
      rw [hf.2.2.2.1]
      exact Finset.notMem_empty _
    have hma := hmem hea hwa
    have hmb := hmem heb hwb
    have hne : sem_bar ea ≠ sem_bar eb := by
      intro heq
      have hg := congrArg Prod.fst heq
      exact hab (consumers_injective hea heb hg)
    have hp : ({sem_bar ea, sem_bar eb} : Finset (ℕ × Bool)) ⊆ sem_W 6 D w := by
      intro f hf
      rcases Finset.mem_insert.mp hf with rfl | hf
      · exact hma
      · exact (Finset.mem_singleton.mp hf) ▸ hmb
    have hcard : ({sem_bar ea, sem_bar eb} : Finset (ℕ × Bool)).card = 2 := by simp [hne]
    have heq : ({sem_bar ea, sem_bar eb} : Finset (ℕ × Bool)) = sem_W 6 D w :=
      Finset.eq_of_subset_of_card_le hp (by rw [hcard]; exact exits_le_two h hc hl w)
    have hme : sem_bar e ∈ sem_W 6 D w := by
      apply sem_mem_W.mpr
      refine ⟨he.1, hw, ?_⟩
      change w ∉ supp 6 D (6 + e.1)
      rw [he.2.2.2.1]
      exact Finset.notMem_empty _
    rw [← heq, Finset.mem_insert, Finset.mem_singleton] at hme
    rcases hme with heea | heeb
    · have hva := consumers_injective he hea (by simpa only [sem_bar] using congrArg Prod.fst heea)
      exact hn (hva ▸ graph_ok.1 _ _ hwa)
    · have hvb := consumers_injective he heb (by simpa only [sem_bar] using congrArg Prod.fst heeb)
      exact hn (hvb ▸ graph_ok.1 _ _ hwb)

lemma all_and_cross_clean {D : Dag} (h : StrictLive 6 D) (hc : sem_Comp 6 adj D)
    (hl : D.length ≤ 8) (ha : (andGates D).card ≤ 3) {j : ℕ}
    (hj : j < D.length) (ht : tag D j = true) :
    ∀ a ∈ supp 6 D (opA D j), ∀ b ∈ supp 6 D (opB D j), adj a b := by
  obtain ⟨v, hv, e, he, hej⟩ := all_and_consumers h hc hl ha hj ht
  obtain ⟨k, s⟩ := e
  dsimp only at hej
  subst k
  intro a hA b hB
  cases s
  · have hsv := he.2.2.1
    simp only [src, Bool.false_eq_true, ↓reduceIte] at hsv
    rw [hsv, Finset.mem_singleton] at hA
    subst a
    exact opposite_clean h hc hl hv he hB
  · have hsv := he.2.2.1
    simp only [src, ↓reduceIte] at hsv
    rw [hsv, Finset.mem_singleton] at hB
    subst b
    exact graph_ok.1 _ _ (opposite_clean h hc hl hv he hA)

lemma independent_wire_linear {D : Dag} (hS : Strict 6 D)
    (hcross : ∀ j, j < D.length → tag D j = true →
      ∀ a ∈ supp 6 D (opA D j), ∀ b ∈ supp 6 D (opB D j), adj a b)
    (x : V → Bool) (hx : ¬ sem_Edge adj x) :
    ∀ w, w < 6 + D.length → val D x w = true →
      ∃ v ∈ supp 6 D w, x v = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hv
    by_cases hin : w < 6
    · refine ⟨⟨w, hin⟩, ?_, ?_⟩
      · rw [show supp 6 D w = {⟨w, hin⟩} from supp_input D ⟨w, hin⟩]
        exact Finset.mem_singleton_self _
      · simpa only [val_input D x w hin] using hv
    · obtain ⟨j, rfl⟩ : ∃ j, w = 6 + j := ⟨w - 6, by omega⟩
      have hj : j < D.length := by omega
      obtain ⟨hA, hB, _⟩ := hS j hj
      rw [val_gate hS x j hj] at hv
      by_cases ht : tag D j = true
      · rw [ht, gop_true, Bool.and_eq_true] at hv
        obtain ⟨a, ha, hxa⟩ := ih _ hA (by omega) hv.1
        obtain ⟨b, hb, hxb⟩ := ih _ hB (by omega) hv.2
        exact (hx ⟨a, b, hcross j hj ht a ha b hb, hxa, hxb⟩).elim
      · have ht0 : tag D j = false := Bool.eq_false_of_not_eq_true ht
        rw [ht0, gop_false, Bool.or_eq_true] at hv
        rw [sem_supp_or hS hj ht0]
        rcases hv with hval | hval
        · obtain ⟨a, ha, hxa⟩ := ih _ hA (by omega) hval
          exact ⟨a, Finset.mem_union_left _ ha, hxa⟩
        · obtain ⟨b, hb, hxb⟩ := ih _ hB (by omega) hval
          exact ⟨b, Finset.mem_union_right _ hb, hxb⟩

lemma no_dirty_eight {D : Dag} (h : StrictLive 6 D) (hc : sem_Comp 6 adj D)
    (hl : D.length ≤ 8) (ha : (andGates D).card ≤ 3) {j : ℕ}
    (hj : j < D.length) (ht : tag D j = true) (x : V → Bool)
    (hv : val D x (6 + j) = true) : sem_Edge adj x := by
  classical
  by_contra hx
  obtain ⟨v, _, e, he, hej⟩ := all_and_consumers h hc hl ha hj ht
  have hz : supp 6 D (6 + j) = ∅ := by simpa only [hej] using he.2.2.2.1
  obtain ⟨a, ha, _⟩ := independent_wire_linear h.1
    (fun j hj ht => all_and_cross_clean h hc hl ha hj ht) x hx (6 + j) (by omega) hv
  rw [hz] at ha
  exact Finset.notMem_empty _ ha

lemma opposite_slot_member {D : Dag} {u v : V} {f : ℕ × Bool}
    (hf : Consumer D u f) (hvu : adj v u) : sem_bar f ∈ sem_W 6 D v := by
  apply sem_mem_W.mpr
  refine ⟨hf.1, hf.2.2.2.2.1 v (graph_ok.1 _ _ hvu), ?_⟩
  change v ∉ supp 6 D (6 + f.1)
  rw [hf.2.2.2.1]
  exact Finset.notMem_empty _

lemma eligible_pair {D : Dag} (h : StrictLive 6 D) (hc : sem_Comp 6 adj D)
    (hl : D.length ≤ 8) {v : V} (hv : v ∉ ineligSet 6 D) :
    ∃ a ∈ ineligSet 6 D, ∃ b ∈ ineligSet 6 D, ∃ ea eb,
      Consumer D a ea ∧ Consumer D b eb ∧ sem_bar ea ≠ sem_bar eb ∧
      sem_W 6 D v = {sem_bar ea, sem_bar eb} := by
  classical
  obtain ⟨_, _, hI, _, _, _, _⟩ := small_budget h hc hl
  obtain ⟨a, ha, b, hb, hab, hva, hvb⟩ :=
    (independent_facts _ (inelig_independent h hc)).2 hI v hv
  obtain ⟨ea, hea⟩ := consumer_exists h hc ha
  obtain ⟨eb, heb⟩ := consumer_exists h hc hb
  have hma := opposite_slot_member hea hva
  have hmb := opposite_slot_member heb hvb
  have hne : sem_bar ea ≠ sem_bar eb := by
    intro heq
    have hg : ea.1 = eb.1 := by simpa only [sem_bar] using congrArg Prod.fst heq
    exact hab (consumers_injective hea heb hg)
  have hp : ({sem_bar ea, sem_bar eb} : Finset (ℕ × Bool)) ⊆ sem_W 6 D v := by
    intro f hf
    rcases Finset.mem_insert.mp hf with rfl | hf
    · exact hma
    · exact (Finset.mem_singleton.mp hf) ▸ hmb
  have hcard : ({sem_bar ea, sem_bar eb} : Finset (ℕ × Bool)).card = 2 := by simp [hne]
  have heq : ({sem_bar ea, sem_bar eb} : Finset (ℕ × Bool)) = sem_W 6 D v :=
    Finset.eq_of_subset_of_card_le hp (by rw [hcard]; exact exits_le_two h hc hl v)
  exact ⟨a, ha, b, hb, ea, eb, hea, heb, hne, heq.symm⟩

lemma all_exits_named {D : Dag} (h : StrictLive 6 D) (hc : sem_Comp 6 adj D)
    (hl : D.length ≤ 8) {v : V} {e : ℕ × Bool} (he : e ∈ sem_W 6 D v) :
    ∃ u ∈ ineligSet 6 D, ∃ f, Consumer D u f ∧ e.1 = f.1 := by
  classical
  by_cases hv : v ∈ ineligSet 6 D
  · obtain ⟨f, hf⟩ := consumer_exists h hc hv
    rw [hf.2.2.2.2.2, Finset.mem_singleton] at he
    exact ⟨v, hv, f, hf, congrArg Prod.fst he⟩
  · obtain ⟨a, ha, b, hb, ea, eb, hea, heb, _, hW⟩ := eligible_pair h hc hl hv
    rw [hW, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with he | he
    · exact ⟨a, ha, ea, hea, by simpa only [sem_bar] using congrArg Prod.fst he⟩
    · exact ⟨b, hb, eb, heb, by simpa only [sem_bar] using congrArg Prod.fst he⟩

lemma singleton_merges_empty {D : Dag} (h : StrictLive 6 D) (hc : sem_Comp 6 adj D)
    (hl : D.length ≤ 8) (v : V) : merges 6 D (carrierT 6 D {v}) = ∅ := by
  classical
  obtain ⟨b, hb, _, _, _, _, hr⟩ := small_budget h hc hl
  have hcount := sem_code_count graph_ok h hc b hb v
  rw [hr] at hcount
  simp only [Finset.filter_empty, Finset.card_empty, add_zero] at hcount
  apply Finset.card_eq_zero.mp
  by_cases hv : v ∈ ineligSet 6 D
  · obtain ⟨e, he⟩ := consumer_exists h hc hv
    have hne := sem_mem_inelig.mp hv
    rw [he.2.2.2.2.2] at hcount
    simp [hne] at hcount
    exact Finset.card_eq_zero.mpr hcount
  · obtain ⟨_, _, _, _, ea, eb, _, _, hne, hW⟩ := eligible_pair h hc hl hv
    have hel : v ∈ eligSet 6 D := by simpa [ineligSet] using hv
    rw [hW] at hcount
    simp [hne, hel] at hcount
    exact Finset.card_eq_zero.mpr hcount

lemma and_singletons_empty {D : Dag} (h : StrictLive 6 D) (hc : sem_Comp 6 adj D)
    (hl : D.length ≤ 8) {j : ℕ} (hj : j < D.length) (ht : tag D j = true) :
    supp 6 D (6 + j) = ∅ := by
  classical
  apply Finset.eq_empty_of_forall_notMem
  intro v hv
  have hs := hv
  rw [sem_supp_and h.1 hj ht, Finset.mem_inter] at hs
  have hm : j ∈ merges 6 D (carrierT 6 D {v}) := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr hj, sem_mem_carrier1.mpr hv,
      sem_mem_carrier1.mpr hs.1, sem_mem_carrier1.mpr hs.2⟩
  rw [singleton_merges_empty h hc hl v] at hm
  exact Finset.notMem_empty _ hm

lemma and_cross_clean_unrestricted {D : Dag} (h : StrictLive 6 D) (hc : sem_Comp 6 adj D)
    (hl : D.length ≤ 8) {j : ℕ} (hj : j < D.length) (ht : tag D j = true) :
    ∀ a ∈ supp 6 D (opA D j), ∀ b ∈ supp 6 D (opB D j), adj a b := by
  intro a hA b hB
  have he : (j, false) ∈ sem_W 6 D a := by
    apply sem_mem_W.mpr
    refine ⟨hj, ?_, ?_⟩
    · simpa only [src, Bool.false_eq_true, ↓reduceIte] using hA
    · rw [and_singletons_empty h hc hl hj ht]
      exact Finset.notMem_empty _
  obtain ⟨v, hv, e, hcon, hje⟩ := all_exits_named h hc hl he
  obtain ⟨k, s⟩ := e
  dsimp only at hje
  subst k
  cases s
  · have hsv := hcon.2.2.1
    simp only [src, Bool.false_eq_true, ↓reduceIte] at hsv
    rw [hsv, Finset.mem_singleton] at hA
    subst a
    exact opposite_clean h hc hl hv hcon hB
  · have hsv := hcon.2.2.1
    simp only [src, ↓reduceIte] at hsv
    rw [hsv, Finset.mem_singleton] at hB
    subst b
    exact graph_ok.1 _ _ (opposite_clean h hc hl hv hcon hA)

lemma no_dirty_eight_unrestricted {D : Dag} (h : StrictLive 6 D)
    (hc : sem_Comp 6 adj D) (hl : D.length ≤ 8) {j : ℕ}
    (hj : j < D.length) (ht : tag D j = true) (x : V → Bool)
    (hv : val D x (6 + j) = true) : sem_Edge adj x := by
  classical
  by_contra hx
  obtain ⟨a, ha, _⟩ := independent_wire_linear h.1
    (fun j hj ht => and_cross_clean_unrestricted h hc hl hj ht) x hx (6 + j) (by omega) hv
  rw [and_singletons_empty h hc hl hj ht] at ha
  exact Finset.notMem_empty _ ha

end C6

namespace C6
open DagTools

lemma forward_comparable {α : Type} {R : α → α → Prop}
    (hfun : ∀ a b c, R a b → R a c → b = c) {x a b : α}
    (ha : Relation.ReflTransGen R x a) (hb : Relation.ReflTransGen R x b) :
    Relation.ReflTransGen R a b ∨ Relation.ReflTransGen R b a := by
  revert b
  induction ha using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro b hb
    exact Or.inl hb
  | @head x y hxy hya ih =>
    intro b hb
    rcases Relation.ReflTransGen.cases_head hb with hxb | ⟨z, hxz, hzb⟩
    · right
      rw [← hxb]
      exact Relation.ReflTransGen.head hxy hya
    · have hyz := hfun x y z hxy hxz
      subst z
      exact ih hzb

lemma step_reach_le {n : ℕ} {D : Dag} (hS : Strict n D) {a b : ℕ}
    (h : Relation.ReflTransGen (sem_step n D) a b) : a ≤ b := by
  induction h with
  | refl => exact Nat.le_refl _
  | tail hab hbc ih => exact ih.trans (sem_step_lt hS hbc).le

lemma one_reader_successor {n : ℕ} {D : Dag} (hS : Strict n D)
    (hone : ∀ w, w + 1 < n + D.length → fanout D w = 1)
    {a b c : ℕ} (hab : sem_step n D a b) (hac : sem_step n D a c) : b = c := by
  have hp := sem_step_fanout hab
  exact sem_step_unique hab hac (hone a (lt_of_fanout_pos hS hp))

lemma parents_no_common_ancestor {n : ℕ} {D : Dag} (hS : Strict n D)
    (hone : ∀ w, w + 1 < n + D.length → fanout D w = 1)
    {j : ℕ} (hj : j < D.length) {w : ℕ}
    (ha : Relation.ReflTransGen (sem_step n D) w (opA D j))
    (hb : Relation.ReflTransGen (sem_step n D) w (opB D j)) : False := by
  have hfun : ∀ a b c, sem_step n D a b → sem_step n D a c → b = c :=
    fun _ _ _ hab hac => one_reader_successor hS hone hab hac
  obtain ⟨hA, hB, hne⟩ := hS j hj
  have hstepA : sem_step n D (opA D j) (n + j) := by
    simpa only [src, Bool.false_eq_true, ↓reduceIte] using
      (sem_step_src (n := n) (D := D) hj false)
  have hstepB : sem_step n D (opB D j) (n + j) := by
    simpa only [src, ↓reduceIte] using
      (sem_step_src (n := n) (D := D) hj true)
  rcases forward_comparable hfun ha hb with hpath | hpath
  · rcases Relation.ReflTransGen.cases_head hpath with heq | ⟨z, haz, hzb⟩
    · exact hne heq
    · have hz : z = n + j := hfun _ _ _ haz hstepA
      have hle := step_reach_le hS hzb
      omega
  · rcases Relation.ReflTransGen.cases_head hpath with heq | ⟨z, hbz, hza⟩
    · exact hne heq.symm
    · have hz : z = n + j := hfun _ _ _ hbz hstepB
      have hle := step_reach_le hS hza
      omega

noncomputable def dag_resources (n : ℕ) (D : Dag) (w : ℕ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun v => Relation.ReflTransGen (sem_step n D) v.val w)

lemma mem_resources {n : ℕ} {D : Dag} {w : ℕ} {v : Fin n} :
    v ∈ dag_resources n D w ↔ Relation.ReflTransGen (sem_step n D) v.val w := by
  classical
  simp only [dag_resources, Finset.mem_filter, Finset.mem_univ, true_and]

lemma resources_input {n : ℕ} (D : Dag) (v : Fin n) :
    dag_resources n D v.val = {v} := by
  classical
  ext u
  rw [mem_resources, Finset.mem_singleton]
  constructor
  · intro hp
    rcases Relation.ReflTransGen.cases_tail hp with heq | ⟨z, _, hz⟩
    · exact Fin.ext heq.symm
    · have hn : n ≤ v.val := hz.2.1
      exact (Nat.not_le_of_gt v.isLt hn).elim
  · intro heq
    subst u
    exact Relation.ReflTransGen.refl

lemma resources_gate {n : ℕ} {D : Dag} {j : ℕ} (hj : j < D.length) :
    dag_resources n D (n + j) =
      dag_resources n D (opA D j) ∪ dag_resources n D (opB D j) := by
  classical
  ext v
  rw [Finset.mem_union, mem_resources, mem_resources, mem_resources]
  constructor
  · intro hp
    rcases Relation.ReflTransGen.cases_tail hp with heq | ⟨w, hvw, hw⟩
    · have hv := v.isLt
      omega
    · have hwhich : opA D j = w ∨ opB D j = w := by
        simpa only [Nat.add_sub_cancel_left] using hw.2.2
      rcases hwhich with ha | hb
      · exact Or.inl (ha ▸ hvw)
      · exact Or.inr (hb ▸ hvw)
  · rintro (ha | hb)
    · apply Relation.ReflTransGen.tail ha
      simpa only [src, Bool.false_eq_true, ↓reduceIte] using
        (sem_step_src (n := n) (D := D) hj false)
    · apply Relation.ReflTransGen.tail hb
      simpa only [src, ↓reduceIte] using
        (sem_step_src (n := n) (D := D) hj true)

lemma resources_disjoint {n : ℕ} {D : Dag} (hS : Strict n D)
    (hone : ∀ w, w + 1 < n + D.length → fanout D w = 1)
    {j : ℕ} (hj : j < D.length) :
    Disjoint (dag_resources n D (opA D j)) (dag_resources n D (opB D j)) := by
  apply Finset.disjoint_left.mpr
  intro v ha hb
  exact parents_no_common_ancestor hS hone hj (mem_resources.mp ha) (mem_resources.mp hb)

lemma resources_nonempty {n : ℕ} {D : Dag} (hS : Strict n D) :
    ∀ w, w < n + D.length → (dag_resources n D w).Nonempty := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hi : w < n
    · rw [show dag_resources n D w = {⟨w, hi⟩} from resources_input D ⟨w, hi⟩]
      exact Finset.singleton_nonempty _
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < D.length := by omega
      have hA := (hS j hj).1
      obtain ⟨v, hv⟩ := ih (opA D j) hA (by omega)
      rw [resources_gate hj]
      exact ⟨v, Finset.mem_union_left _ hv⟩

lemma reader_exists {D : Dag} {w : ℕ} (h : 1 ≤ fanout D w) :
    ∃ j, j < D.length ∧ (opA D j = w ∨ opB D j = w) := by
  have hc : (readers D w).Nonempty := Finset.card_pos.mp h
  obtain ⟨j, hj⟩ := hc
  rw [readers, Finset.mem_filter, Finset.mem_range] at hj
  exact ⟨j, hj⟩

lemma wire_reaches_output {n : ℕ} {D : Dag} (h : StrictLive n D) :
    ∀ w, w < n + D.length → Relation.ReflTransGen (sem_step n D) w (outW n D) := by
  have aux : ∀ k w, n + D.length - w = k → w < n + D.length →
      Relation.ReflTransGen (sem_step n D) w (outW n D) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro w hkw hw
      by_cases heq : w = outW n D
      · rw [heq]
      · have hinner : w + 1 < n + D.length := by unfold outW at heq; omega
        obtain ⟨j, hj, hsrc⟩ := reader_exists (h.2.1 w hinner)
        have hstep : sem_step n D w (n + j) := by
          refine ⟨by omega, by omega, ?_⟩
          simpa only [Nat.add_sub_cancel_left] using hsrc
        have hlt := sem_step_lt h.1 hstep
        have hp := ih (n + D.length - (n + j)) (by omega) (n + j) rfl (by omega)
        exact Relation.ReflTransGen.head hstep hp
  intro w hw
  exact aux _ w rfl hw

lemma resources_output {n : ℕ} {D : Dag} (h : StrictLive n D) :
    dag_resources n D (outW n D) = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro v
  apply mem_resources.mpr
  apply wire_reaches_output h v.val
  have hn := v.isLt
  omega

lemma resource_induction {n : ℕ} {D : Dag} {α : Type} (h : StrictLive n D)
    (hone : ∀ w, w + 1 < n + D.length → fanout D w = 1)
    (x : α → Fin n → Bool) (P : Finset (Fin n) → (α → Bool) → Prop)
    (hinput : ∀ v : Fin n, P {v} (fun a => x a v))
    (hand : ∀ S T f g, Disjoint S T → P S f → P T g →
      P (S ∪ T) (fun a => f a && g a))
    (hor : ∀ S T f g, Disjoint S T → P S f → P T g →
      P (S ∪ T) (fun a => f a || g a)) :
    P Finset.univ (fun a => val D (x a) (outW n D)) := by
  have all : ∀ w, w < n + D.length → P (dag_resources n D w) (fun a => val D (x a) w) := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      by_cases hin : w < n
      · rw [show dag_resources n D w = {⟨w, hin⟩} from resources_input D ⟨w, hin⟩]
        have hev : (fun a => val D (x a) w) = (fun a => x a ⟨w, hin⟩) := by
          funext a
          exact val_input D (x a) w hin
        rw [hev]
        exact hinput ⟨w, hin⟩
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < D.length := by omega
        obtain ⟨hA, hB, _⟩ := h.1 j hj
        have pA := ih (opA D j) hA (by omega)
        have pB := ih (opB D j) hB (by omega)
        have hdis := resources_disjoint h.1 hone hj
        rw [resources_gate hj]
        have hev : (fun a => val D (x a) (n + j)) =
            (fun a => gop (tag D j) (val D (x a) (opA D j)) (val D (x a) (opB D j))) := by
          funext a
          exact val_gate h.1 (x a) j hj
        rw [hev]
        cases ht : tag D j
        · exact hor _ _ _ _ hdis pA pB
        · exact hand _ _ _ _ hdis pA pB
  have hout : outW n D < n + D.length := by
    have hp : 0 < D.length := List.length_pos_iff.mpr h.2.2
    unfold outW
    omega
  have hp := all (outW n D) hout
  rw [resources_output h] at hp
  exact hp

lemma resource_induction_nonempty {n : ℕ} {D : Dag} {α : Type} (h : StrictLive n D)
    (hone : ∀ w, w + 1 < n + D.length → fanout D w = 1)
    (x : α → Fin n → Bool) (P : Finset (Fin n) → (α → Bool) → Prop)
    (hinput : ∀ v : Fin n, P {v} (fun a => x a v))
    (hand : ∀ S T f g, S.Nonempty → T.Nonempty → Disjoint S T → P S f → P T g →
      P (S ∪ T) (fun a => f a && g a))
    (hor : ∀ S T f g, S.Nonempty → T.Nonempty → Disjoint S T → P S f → P T g →
      P (S ∪ T) (fun a => f a || g a)) :
    P Finset.univ (fun a => val D (x a) (outW n D)) := by
  have hp := resource_induction h hone x
    (fun S f => S.Nonempty ∧ P S f)
    (fun v => ⟨Finset.singleton_nonempty v, hinput v⟩)
    (fun S T f g hd hS hT =>
      ⟨hS.1.mono Finset.subset_union_left, hand S T f g hS.1 hT.1 hd hS.2 hT.2⟩)
    (fun S T f g hd hS hT =>
      ⟨hS.1.mono Finset.subset_union_left, hor S T f g hS.1 hT.1 hd hS.2 hT.2⟩)
  exact hp.2

end C6

namespace C6
open DagTools

lemma raw_or_branch_left {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}
    (hG : sem_Gr G) (hS : Strict n D) (hc : sem_Comp n G D)
    {j : ℕ} (hj : j < D.length) (ht : tag D j = false)
    {v w : Fin n} (hv : opA D j = v.val) (hw : opB D j = w.val) (hne : v ≠ w) :
    2 ≤ fanout D v.val := by
  have hstep : sem_step n D v.val (n + j) := by
    simpa only [src, Bool.false_eq_true, ↓reduceIte, hv] using
      (sem_step_src (n := n) (D := D) hj false)
  have hpos := sem_step_fanout hstep
  by_contra hlt
  have hfo : fanout D v.val = 1 := by omega
  have hchain : sem_Chain n D v.val (n + j) :=
    Relation.ReflTransGen.single ⟨hstep, hfo⟩
  have hpure := sem_dom_pure hG hS hc v (n + j) (sem_chain_dom hS hchain)
  have hmem : w ∈ supp n D (n + j) := by
    rw [sem_supp_or hS hj ht, hw, supp_input]
    exact Finset.mem_union_right _ (Finset.mem_singleton_self w)
  have heq := hpure hmem
  rw [Finset.mem_singleton] at heq
  exact hne heq.symm

lemma raw_or_branch_right {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}
    (hG : sem_Gr G) (hS : Strict n D) (hc : sem_Comp n G D)
    {j : ℕ} (hj : j < D.length) (ht : tag D j = false)
    {v w : Fin n} (hv : opA D j = v.val) (hw : opB D j = w.val) (hne : v ≠ w) :
    2 ≤ fanout D w.val := by
  have hstep : sem_step n D w.val (n + j) := by
    simpa only [src, ↓reduceIte, hw] using
      (sem_step_src (n := n) (D := D) hj true)
  have hpos := sem_step_fanout hstep
  by_contra hlt
  have hfo : fanout D w.val = 1 := by omega
  have hchain : sem_Chain n D w.val (n + j) :=
    Relation.ReflTransGen.single ⟨hstep, hfo⟩
  have hpure := sem_dom_pure hG hS hc w (n + j) (sem_chain_dom hS hchain)
  have hmem : v ∈ supp n D (n + j) := by
    rw [sem_supp_or hS hj ht, hv, supp_input]
    exact Finset.mem_union_left _ (Finset.mem_singleton_self v)
  have heq := hpure hmem
  rw [Finset.mem_singleton] at heq
  exact hne heq

lemma raw_branch_eligible {n : ℕ} {D : Dag} {v : Fin n}
    (hv : 2 ≤ fanout D v.val) : v ∈ eligSet n D := by
  apply mem_eligSet.mpr
  refine ⟨v.val, hv, ?_⟩
  rw [supp_input]
  exact Finset.mem_singleton_self v

lemma c6_length_at_least_eight {D : Dag} (h : StrictLive 6 D) (hc : sem_Comp 6 adj D) :
    8 ≤ D.length := by
  by_contra hn
  have hl : D.length ≤ 8 := by omega
  obtain ⟨_, _, _, _, hp, hz, _⟩ := small_budget h hc hl
  have hs := surplus_identity h
  rw [totalSurplus_split, hp, hz] at hs
  omega

def oppositePair (v w : V) : Prop :=
  (v.val, w.val) ∈ [(0,5),(1,4),(2,3)] ∨ (w.val, v.val) ∈ [(0,5),(1,4),(2,3)]

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 10000000 in
lemma independent_hits_opposite : ∀ I : Finset V, Independent I → I.card = 3 →
    ∀ v w, oppositePair v w → v ∈ I ∨ w ∈ I := by
  unfold Independent adj oppositePair
  decide +kernel

set_option synthInstance.maxSize 4096 in
lemma opposite_distinct : ∀ v w : V, oppositePair v w → v ≠ w := by
  unfold oppositePair
  decide +kernel

lemma no_opposite_raw_or_eight {D : Dag} (h : StrictLive 6 D) (hc : sem_Comp 6 adj D)
    (hl : D.length ≤ 8) {j : ℕ} (hj : j < D.length) (ht : tag D j = false)
    {v w : V} (hv : opA D j = v.val) (hw : opB D j = w.val)
    (hop : oppositePair v w) : False := by
  have hve := raw_branch_eligible (raw_or_branch_left graph_ok h.1 hc hj ht hv hw
    (opposite_distinct v w hop))
  have hwe := raw_branch_eligible (raw_or_branch_right graph_ok h.1 hc hj ht hv hw
    (opposite_distinct v w hop))
  obtain ⟨_, _, hI, _, _, _, _⟩ := small_budget h hc hl
  rcases independent_hits_opposite _ (inelig_independent h hc) hI v w hop with hi | hi
  · exact (sem_mem_inelig.mp hi) hve
  · exact (sem_mem_inelig.mp hi) hwe

lemma six_raw_branches_length {D : Dag} (h : StrictLive 6 D) (hc : sem_Comp 6 adj D)
    (hraw : ∀ v : V, 2 ≤ fanout D v.val) : 11 ≤ D.length := by
  classical
  obtain ⟨b, hb⟩ := sem_exists_pureBranch graph_ok h.1 hc
  have hfull : eligSet 6 D = Finset.univ := by
    apply Finset.eq_univ_of_forall
    exact fun v => raw_branch_eligible (hraw v)
  have he := elig_le_Bplus h.1 b hb
  rw [hfull] at he
  have he6 : 6 ≤ Bplus 6 D := by simpa using he
  have hs := surplus_identity h
  rw [totalSurplus_split] at hs
  omega

lemma four_raw_branches_budget {D : Dag} (h : StrictLive 6 D) (hl : D.length ≤ 9)
    (S : Finset V) (hS : S.card = 4) (hraw : ∀ v ∈ S, 2 ≤ fanout D v.val) :
    D.length = 9 ∧ ∀ w, 2 ≤ fanout D w →
      ∃ v ∈ S, w = v.val ∧ fanout D w = 2 := by
  classical
  let u : V → Σ _ : ℕ, ℕ := fun v => ⟨v.val, 0⟩
  let U := S.image u
  have hinj : Function.Injective u := by
    intro v w hvw
    apply Fin.ext
    exact congrArg Sigma.fst hvw
  have hU : U.card = 4 := by
    dsimp only [U]
    rw [Finset.card_image_of_injective _ hinj]
    exact hS
  have hsub : U ⊆ units 6 D := by
    intro z hz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    have hbr := hraw v hv
    apply mem_units.mpr
    change v.val ∈ inner 6 D ∧ 0 + 1 < fanout D v.val
    exact ⟨sb_mem_inner.mpr (lt_of_fanout_pos h.1 (w := v.val) (by omega)), by omega⟩
  have hcard : (units 6 D).card = totalSurplus 6 D := by
    simpa only [Finset.filter_true, totalSurplus] using
      (sb_card_units_filter 6 D (fun _ => True))
  have htotal := surplus_identity h
  have huc : (units 6 D).card ≤ 4 := by omega
  have heq : U = units 6 D := Finset.eq_of_subset_of_card_le hsub (by omega)
  have hsize : D.length = 9 := by
    have he : (units 6 D).card = 4 := by rw [← heq]; exact hU
    omega
  refine ⟨hsize, ?_⟩
  intro w hw
  have hzero : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ units 6 D := by
    apply mem_units.mpr
    change w ∈ inner 6 D ∧ _
    exact ⟨sb_mem_inner.mpr (lt_of_fanout_pos h.1 (w := w) (by omega)), by dsimp; omega⟩
  rw [← heq] at hzero
  obtain ⟨v, hv, he0⟩ := Finset.mem_image.mp hzero
  have hew : w = v.val := (congrArg Sigma.fst he0).symm
  refine ⟨v, hv, hew, ?_⟩
  by_contra hne
  have hthree : 3 ≤ fanout D w := by omega
  have hone : (⟨w, 1⟩ : Σ _ : ℕ, ℕ) ∈ units 6 D := by
    apply mem_units.mpr
    change w ∈ inner 6 D ∧ _
    exact ⟨sb_mem_inner.mpr (lt_of_fanout_pos h.1 (w := w) (by omega)), by dsimp; omega⟩
  rw [← heq] at hone
  obtain ⟨v', _, he1⟩ := Finset.mem_image.mp hone
  have : (0 : ℕ) = 1 := congrArg Sigma.snd he1
  omega

lemma fanout_append (P R : Dag) (w : ℕ) : fanout (P ++ R) w = fanout P w + fanout R w := by
  classical
  simp only [fanout, readers, Finset.card_filter, List.length_append]
  rw [Finset.sum_range_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have hg := List.getD_append P R (false, 0, 0) j hj'
    simp only [opA, opB, hg]
    split_ifs with hp <;> simp_all
  · apply Finset.sum_congr rfl
    intro j _
    have hg : (P ++ R).getD (P.length + j) (false, 0, 0) = R.getD j (false, 0, 0) := by
      rw [List.getD_append_right P R (false, 0, 0) (P.length + j) (by omega)]
      congr 1
      omega
    simp only [opA, opB, hg]
    split_ifs with hp <;> simp_all

lemma strict_after_prefix {n : ℕ} {P R : Dag} (h : Strict n (P ++ R)) :
    Strict (n + P.length) R := by
  intro j hj
  have hj' : P.length + j < (P ++ R).length := by simp only [List.length_append]; omega
  have hs := h (P.length + j) hj'
  have hg : (P ++ R).getD (P.length + j) (false, 0, 0) = R.getD j (false, 0, 0) := by
    rw [List.getD_append_right P R (false, 0, 0) (P.length + j) (by omega)]
    congr 1
    omega
  simpa only [opA, opB, hg, Nat.add_assoc] using hs

def prefixTwo : Dag := [(false, 0, 5), (false, 1, 4)]

def fourEndpoints : Finset V := {0, 1, 4, 5}

lemma prefixTwo_fanout (w : ℕ) : fanout prefixTwo w =
    if w = 0 ∨ w = 1 ∨ w = 4 ∨ w = 5 then 1 else 0 := by
  classical
  by_cases hw : w < 6
  · interval_cases w <;> decide
  · have h0 : w ≠ 0 := by omega
    have h1 : w ≠ 1 := by omega
    have h4 : w ≠ 4 := by omega
    have h5 : w ≠ 5 := by omega
    simp [fanout, readers, prefixTwo, opA, opB, Finset.range_add_one, Finset.filter_insert, Finset.filter_singleton, eq_comm, h0, h1, h4, h5]

lemma prefixTwo_branches {R : Dag} (h : StrictLive 6 (prefixTwo ++ R))
    (hc : sem_Comp 6 adj (prefixTwo ++ R)) :
    ∀ v ∈ fourEndpoints, 2 ≤ fanout (prefixTwo ++ R) v.val := by
  have h0 : 0 < (prefixTwo ++ R).length := by simp [prefixTwo]
  have h1 : 1 < (prefixTwo ++ R).length := by simp [prefixTwo]
  have hp0 : opA (prefixTwo ++ R) 0 = (0 : V).val := by simp [opA, prefixTwo]
  have hp5 : opB (prefixTwo ++ R) 0 = (5 : V).val := by simp [opB, prefixTwo]
  have hp1 : opA (prefixTwo ++ R) 1 = (1 : V).val := by simp [opA, prefixTwo]
  have hp4 : opB (prefixTwo ++ R) 1 = (4 : V).val := by simp [opB, prefixTwo]
  have ht0 : tag (prefixTwo ++ R) 0 = false := by simp [tag, prefixTwo]
  have ht1 : tag (prefixTwo ++ R) 1 = false := by simp [tag, prefixTwo]
  have hb0 := raw_or_branch_left graph_ok h.1 hc h0 ht0 hp0 hp5 (by decide)
  have hb5 := raw_or_branch_right graph_ok h.1 hc h0 ht0 hp0 hp5 (by decide)
  have hb1 := raw_or_branch_left graph_ok h.1 hc h1 ht1 hp1 hp4 (by decide)
  have hb4 := raw_or_branch_right graph_ok h.1 hc h1 ht1 hp1 hp4 (by decide)
  intro v hv
  simp only [fourEndpoints, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl
  · exact hb0
  · exact hb1
  · exact hb4
  · exact hb5

lemma prefixTwo_residual_tree {R : Dag} (h : StrictLive 6 (prefixTwo ++ R))
    (hc : sem_Comp 6 adj (prefixTwo ++ R)) (hl : R.length ≤ 7) :
    R.length = 7 ∧ StrictLive 8 R ∧
      ∀ w, w + 1 < 8 + R.length → fanout R w = 1 := by
  classical
  have hlen : (prefixTwo ++ R).length ≤ 9 := by
    simp only [prefixTwo, List.length_append, List.length_cons, List.length_nil]
    omega
  obtain ⟨hsize, hbudget⟩ := four_raw_branches_budget h hlen fourEndpoints (by decide)
    (prefixTwo_branches h hc)
  have hR : R.length = 7 := by simpa [prefixTwo] using hsize
  have hS : Strict 8 R := by simpa [prefixTwo] using strict_after_prefix h.1
  have hfan : ∀ w, w + 1 < 8 + R.length → fanout R w = 1 := by
    intro w hw
    have hd : 1 ≤ fanout (prefixTwo ++ R) w := h.2.1 w (by simp only [prefixTwo, List.length_append, List.length_cons, List.length_nil]; omega)
    have hadd := fanout_append prefixTwo R w
    rw [prefixTwo_fanout] at hadd
    by_cases hp : w = 0 ∨ w = 1 ∨ w = 4 ∨ w = 5
    · have hbr : 2 ≤ fanout (prefixTwo ++ R) w := by
        rcases hp with rfl | rfl | rfl | rfl
        · exact prefixTwo_branches h hc 0 (by decide)
        · exact prefixTwo_branches h hc 1 (by decide)
        · exact prefixTwo_branches h hc 4 (by decide)
        · exact prefixTwo_branches h hc 5 (by decide)
      obtain ⟨_, _, _, hf⟩ := hbudget w hbr
      simp only [hp, ↓reduceIte] at hadd
      omega
    · have hnot : ¬ 2 ≤ fanout (prefixTwo ++ R) w := by
        intro hbr
        obtain ⟨v, hv, hvw, _⟩ := hbudget w hbr
        simp only [fourEndpoints, Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl | rfl | rfl <;> simp_all
      simp only [hp, ↓reduceIte] at hadd
      omega
  refine ⟨hR, ⟨hS, ?_, ?_⟩, hfan⟩
  · intro w hw
    rw [hfan w hw]
  · intro he
    simp [he] at hR

def extendTwo (x : V → Bool) : Fin 8 → Bool :=
  ![x 0, x 1, x 2, x 3, x 4, x 5, x 0 || x 5, x 1 || x 4]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
lemma prefixTwo_inputs : ∀ x : V → Bool,
    wl prefixTwo (List.ofFn x) = List.ofFn (extendTwo x) := by
  decide +kernel

lemma prefixTwo_residual_computes {R : Dag}
    (hc : sem_Comp 6 adj (prefixTwo ++ R)) (x : V → Bool) :
    val R (extendTwo x) (outW 8 R) = true ↔ sem_Edge adj x := by
  have ho : outW 6 (prefixTwo ++ R) = outW 8 R := by
    simp only [outW, List.length_append, prefixTwo, List.length_cons, List.length_nil]
    omega
  have he : val (prefixTwo ++ R) x (outW 6 (prefixTwo ++ R)) =
      val R (extendTwo x) (outW 8 R) := by
    simp only [val, wl_append, prefixTwo_inputs, ho]
  rw [← he]
  exact hc x

end C6

namespace C6

open DagTools

def raw_prefix (n : ℕ) (P : Dag) : Prop :=
  ∀ g ∈ P, g.2.1 < n ∧ g.2.2 < n

lemma raw_prefix_sublist {n : ℕ} {P Q : Dag} (hP : raw_prefix n P)
    (hQP : Q.Sublist P) : raw_prefix n Q := by
  intro g hg
  exact hP g (hQP.subset hg)

lemma raw_prefix_shift {n : ℕ} {P : Dag} (hP : raw_prefix n P) (j : ℕ) :
    P.map (fun g => (g.1, na_sh (n + j) g.2.1, na_sh (n + j) g.2.2)) = P := by
  calc
    _ = P.map id := List.map_congr_left (by
      intro g hg
      obtain ⟨ha, hb⟩ := hP g hg
      have ha' : ¬n + j < g.2.1 := by omega
      have hb' : ¬n + j < g.2.2 := by omega
      simp [na_sh, ha', hb'])
    _ = P := List.map_id P

lemma na_del_raw_prefix {n : ℕ} {P R : Dag} (hP : raw_prefix n P) (j : ℕ) :
    ∃ P' R' : Dag, P'.Sublist P ∧ R'.length ≤ R.length ∧
      na_del n j (P ++ R) = P' ++ R' := by
  by_cases hj : j < P.length
  · refine ⟨P.eraseIdx j,
      R.map (fun g => (g.1, na_sh (n + j) g.2.1, na_sh (n + j) g.2.2)),
      List.eraseIdx_sublist P j, ?_, ?_⟩
    · simp
    · unfold na_del
      rw [List.eraseIdx_append_of_lt_length hj, List.map_append,
        raw_prefix_shift (raw_prefix_sublist hP (List.eraseIdx_sublist P j))]
  · refine ⟨P,
      (R.eraseIdx (j - P.length)).map
        (fun g => (g.1, na_sh (n + j) g.2.1, na_sh (n + j) g.2.2)),
      List.Sublist.refl P, ?_, ?_⟩
    · simp only [List.length_map]
      exact (List.eraseIdx_sublist R _).length_le
    · unfold na_del
      rw [List.eraseIdx_append_of_length_le (by omega), List.map_append,
        raw_prefix_shift hP]

lemma prefix_live_aux {n : ℕ} (F : (Fin n → Bool) → Bool)
    (hess : ∀ i : Fin n, ∃ x y : Fin n → Bool,
      (∀ k, k ≠ i → x k = y k) ∧ F x ≠ F y) :
    ∀ (s : ℕ) (P R : Dag), (P ++ R).length = s → raw_prefix n P →
      Strict n (P ++ R) → P ++ R ≠ [] →
      (∀ x : Fin n → Bool, val (P ++ R) x (outW n (P ++ R)) = F x) →
      ∃ P' R' : Dag, P'.Sublist P ∧ R'.length ≤ R.length ∧
        StrictLive n (P' ++ R') ∧
        ∀ x : Fin n → Bool, val (P' ++ R') x (outW n (P' ++ R')) = F x := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro P R hlen hP hS hne hD
    have hpos : 0 < (P ++ R).length := List.length_pos_iff.mpr hne
    by_cases hL : Live n (P ++ R)
    · exact ⟨P, R, List.Sublist.refl P, le_rfl, ⟨hS, hL, hne⟩, hD⟩
    · obtain ⟨w, hw, hf0⟩ :
          ∃ w, w + 1 < n + (P ++ R).length ∧ fanout (P ++ R) w = 0 := by
        by_contra hcon
        exact hL (fun w hw => by
          by_contra h0
          exact hcon ⟨w, hw, by omega⟩)
      by_cases hwn : w < n
      · exfalso
        obtain ⟨x, y, hxy, hFne⟩ := hess ⟨w, hwn⟩
        apply hFne
        rw [← hD x, ← hD y]
        have hout : outW n (P ++ R) ≠ w := by unfold outW; omega
        have key := val_unique hS y
          (fun u => if u = w then y ⟨w, hwn⟩ else val (P ++ R) x u)
          (fun i hi => by
            by_cases hiw : i = w
            · subst hiw; simp
            · simp only [hiw, ite_false]
              rw [val_input (P ++ R) x i hi]
              exact hxy ⟨i, hi⟩ (fun h => hiw (congrArg Fin.val h)))
          (fun j hj => by
            obtain ⟨ha, hb⟩ := na_no_reader hf0 j hj
            have hnj : n + j ≠ w := by omega
            simp only [hnj, ha, hb, ite_false]
            exact val_gate hS x j hj)
          (outW n (P ++ R)) (by unfold outW; omega)
        simp only [hout, ite_false] at key
        exact key.symm
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < (P ++ R).length := by omega
        have hl := na_del_length n j (P ++ R) hj
        obtain ⟨Q, S, hQP, hSR, hdel⟩ := na_del_raw_prefix hP (R := R) j
        have hlen' : (Q ++ S).length = (P ++ R).length - 1 := by
          rw [← hdel, hl]
        have hS' : Strict n (Q ++ S) := by
          rw [← hdel]
          exact na_del_strict hS j hj hf0
        have hne' : Q ++ S ≠ [] := by
          intro he
          rw [he] at hlen'
          simp only [List.length_nil] at hlen'
          omega
        have hD' : ∀ x : Fin n → Bool,
            val (Q ++ S) x (outW n (Q ++ S)) = F x := by
          intro x
          rw [← hdel]
          have ho : outW n (na_del n j (P ++ R)) = n + ((P ++ R).length - 1) - 1 := by
            unfold outW
            rw [hl]
          have hu : na_up (n + j) (n + ((P ++ R).length - 1) - 1) =
              outW n (P ++ R) := by
            unfold na_up outW
            split_ifs <;> omega
          rw [ho, na_del_val hS j hj hf0 x _ (by omega), hu]
          exact hD x
        obtain ⟨P', R', hP'Q, hR'S, hSL, hF⟩ :=
          ih ((P ++ R).length - 1) (by omega) Q S hlen'
            (raw_prefix_sublist hP hQP) hS' hne' hD'
        exact ⟨P', R', hP'Q.trans hQP, hR'S.trans hSR, hSL, hF⟩

lemma exists_strictLive_raw_prefix {n : ℕ} (F : (Fin n → Bool) → Bool)
    (hess : ∀ i : Fin n, ∃ x y : Fin n → Bool,
      (∀ k, k ≠ i → x k = y k) ∧ F x ≠ F y)
    (P R : Dag) (hP : raw_prefix n P) (hS : Strict n (P ++ R))
    (hne : P ++ R ≠ [])
    (hD : ∀ x : Fin n → Bool, val (P ++ R) x (outW n (P ++ R)) = F x) :
    ∃ P' R' : Dag, P'.Sublist P ∧ R'.length ≤ R.length ∧
      StrictLive n (P' ++ R') ∧
      ∀ x : Fin n → Bool, val (P' ++ R') x (outW n (P' ++ R')) = F x :=
  prefix_live_aux F hess (P ++ R).length P R rfl hP hS hne hD

end C6

namespace C6
open DagTools

def swapPairs : Equiv.Perm V where
  toFun := ![0, 2, 1, 4, 3, 5]
  invFun := ![0, 2, 1, 4, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rotatePairs : Equiv.Perm V where
  toFun := ![2, 0, 1, 4, 5, 3]
  invFun := ![1, 2, 0, 5, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

lemma swapPairs_adj : ∀ u v : V, adj (swapPairs u) (swapPairs v) ↔ adj u v := by
  unfold adj
  decide +kernel

lemma rotatePairs_adj : ∀ u v : V, adj (rotatePairs u) (rotatePairs v) ↔ adj u v := by
  unfold adj
  decide +kernel

lemma c6_relabel_computes (σ : Equiv.Perm V)
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

def prefix02 : Dag := [(false, 0, 5), (false, 2, 3)]
def prefix12 : Dag := [(false, 1, 4), (false, 2, 3)]
def prefixThree : Dag := [(false, 0, 5), (false, 1, 4), (false, 2, 3)]

lemma relabel_prefix02 : relabel swapPairs prefix02 = prefixTwo := by decide +kernel
lemma relabel_prefix12 : relabel rotatePairs prefix12 = prefixTwo := by decide +kernel

lemma canonical_two_pair_reduction {P R : Dag}
    (hP : P = prefixTwo ∨ P = prefix02 ∨ P = prefix12)
    (hl : R.length ≤ 7) (h : StrictLive 6 (P ++ R))
    (hc : sem_Comp 6 adj (P ++ R)) :
    ∃ R', R'.length ≤ 7 ∧ StrictLive 6 (prefixTwo ++ R') ∧
      sem_Comp 6 adj (prefixTwo ++ R') := by
  rcases hP with rfl | rfl | rfl
  · exact ⟨R, hl, h, hc⟩
  · have he : relabel swapPairs (prefix02 ++ R) = prefixTwo ++ relabel swapPairs R := by
      change relabel swapPairs prefix02 ++ relabel swapPairs R = _
      rw [relabel_prefix02]
    exact ⟨relabel swapPairs R, by simpa [relabel_length] using hl,
      he ▸ relabel_strictLive swapPairs h,
      he ▸ c6_relabel_computes swapPairs swapPairs_adj h hc⟩
  · have he : relabel rotatePairs (prefix12 ++ R) = prefixTwo ++ relabel rotatePairs R := by
      change relabel rotatePairs prefix12 ++ relabel rotatePairs R = _
      rw [relabel_prefix12]
    exact ⟨relabel rotatePairs R, by simpa [relabel_length] using hl,
      he ▸ relabel_strictLive rotatePairs h,
      he ▸ c6_relabel_computes rotatePairs rotatePairs_adj h hc⟩

lemma prefixThree_all_branches {R : Dag}
    (h : StrictLive 6 (prefixThree ++ R)) (hc : sem_Comp 6 adj (prefixThree ++ R)) :
    ∀ v : V, 2 ≤ fanout (prefixThree ++ R) v.val := by
  have h0 : 0 < (prefixThree ++ R).length := by simp [prefixThree]
  have h1 : 1 < (prefixThree ++ R).length := by simp [prefixThree]
  have h2 : 2 < (prefixThree ++ R).length := by simp [prefixThree]
  have hb0 := raw_or_branch_left graph_ok h.1 hc h0
    (by simp [tag, prefixThree]) (v := (0 : V)) (w := (5 : V))
    (by simp [opA, prefixThree]) (by simp [opB, prefixThree]) (by decide)
  have hb5 := raw_or_branch_right graph_ok h.1 hc h0
    (by simp [tag, prefixThree]) (v := (0 : V)) (w := (5 : V))
    (by simp [opA, prefixThree]) (by simp [opB, prefixThree]) (by decide)
  have hb1 := raw_or_branch_left graph_ok h.1 hc h1
    (by simp [tag, prefixThree]) (v := (1 : V)) (w := (4 : V))
    (by simp [opA, prefixThree]) (by simp [opB, prefixThree]) (by decide)
  have hb4 := raw_or_branch_right graph_ok h.1 hc h1
    (by simp [tag, prefixThree]) (v := (1 : V)) (w := (4 : V))
    (by simp [opA, prefixThree]) (by simp [opB, prefixThree]) (by decide)
  have hb2 := raw_or_branch_left graph_ok h.1 hc h2
    (by simp [tag, prefixThree]) (v := (2 : V)) (w := (3 : V))
    (by simp [opA, prefixThree]) (by simp [opB, prefixThree]) (by decide)
  have hb3 := raw_or_branch_right graph_ok h.1 hc h2
    (by simp [tag, prefixThree]) (v := (2 : V)) (w := (3 : V))
    (by simp [opA, prefixThree]) (by simp [opB, prefixThree]) (by decide)
  intro v
  fin_cases v <;> assumption

lemma no_three_pairs_seven {R : Dag} (hl : R.length ≤ 7)
    (h : StrictLive 6 (prefixThree ++ R)) (hc : sem_Comp 6 adj (prefixThree ++ R)) : False := by
  have hb := six_raw_branches_length h hc (prefixThree_all_branches h hc)
  simp only [prefixThree, List.length_append, List.length_cons, List.length_nil] at hb
  omega

end C6

namespace C6
open DagTools

def edgeBool (x : V → Bool) : Bool :=
  (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 3) ||
  (x 1 && x 5) || (x 2 && x 4) || (x 2 && x 5)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 4096 in
lemma edgeBool_spec : ∀ x : V → Bool, edgeBool x = true ↔ sem_Edge adj x := by
  unfold edgeBool sem_Edge adj
  decide +kernel

lemma edgeBool_essential : ∀ i : V, ∃ x y : V → Bool,
    (∀ k, k ≠ i → x k = y k) ∧ edgeBool x ≠ edgeBool y := by
  intro i
  let v : V := ![3, 3, 4, 0, 0, 1] i
  refine ⟨single v, sem_two i v, ?_, ?_⟩
  · fin_cases i <;> decide +kernel
  · fin_cases i <;> decide +kernel

lemma prefixThree_classify {P : Dag} (hP : P.Sublist prefixThree) :
    P = [] ∨ P = [(false, 0, 5)] ∨ P = [(false, 1, 4)] ∨ P = [(false, 2, 3)] ∨
      P = prefixTwo ∨ P = prefix02 ∨ P = prefix12 ∨ P = prefixThree := by
  have hm := List.mem_sublists.mpr hP
  have hc : ∀ Q ∈ prefixThree.sublists,
      Q = [] ∨ Q = [(false, 0, 5)] ∨ Q = [(false, 1, 4)] ∨ Q = [(false, 2, 3)] ∨
        Q = prefixTwo ∨ Q = prefix02 ∨ Q = prefix12 ∨ Q = prefixThree := by
    decide +kernel
  exact hc P hm

lemma no_one_pair_seven {v w : V} (hop : oppositePair v w) {R : Dag}
    (hl : R.length ≤ 7) (h : StrictLive 6 ([(false, v.val, w.val)] ++ R))
    (hc : sem_Comp 6 adj ([(false, v.val, w.val)] ++ R)) : False := by
  have hs : ([(false, v.val, w.val)] ++ R).length ≤ 8 := by simp only [List.length_append, List.length_cons, List.length_nil]; omega
  exact no_opposite_raw_or_eight h hc hs
    (j := 0) (by simp) (by simp [tag]) (v := v) (w := w)
    (by simp [opA]) (by simp [opB]) hop

lemma no_free_prefix_seven_of_canonical
    (hcanonical : ∀ R : Dag, R.length ≤ 7 → StrictLive 6 (prefixTwo ++ R) →
      sem_Comp 6 adj (prefixTwo ++ R) → False)
    {R : Dag} (hl : R.length ≤ 7) (h : Strict 6 (prefixThree ++ R))
    (hc : sem_Comp 6 adj (prefixThree ++ R)) : False := by
  have hraw : raw_prefix 6 prefixThree := by
    intro g hg
    simp only [prefixThree, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl <;> decide
  have hne : prefixThree ++ R ≠ [] := by simp [prefixThree]
  have hD : ∀ x : V → Bool, val (prefixThree ++ R) x (outW 6 (prefixThree ++ R)) = edgeBool x := by
    intro x
    have he := (hc x).trans (edgeBool_spec x).symm
    cases ha : val (prefixThree ++ R) x (outW 6 (prefixThree ++ R)) <;>
      cases hb : edgeBool x <;> simp_all
  obtain ⟨P', R', hP', hR', hSL, hcomp⟩ :=
    exists_strictLive_raw_prefix edgeBool edgeBool_essential prefixThree R hraw h hne hD
  have hlen : R'.length ≤ 7 := hR'.trans hl
  have hcomp' : sem_Comp 6 adj (P' ++ R') := by
    intro x
    rw [hcomp x]
    exact edgeBool_spec x
  rcases prefixThree_classify hP' with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst P'
    have hb := c6_length_at_least_eight hSL hcomp'
    simp only [List.nil_append] at hb
    omega
  · subst P'
    exact no_one_pair_seven (v := 0) (w := 5) (by unfold oppositePair; decide +kernel) hlen hSL hcomp'
  · subst P'
    exact no_one_pair_seven (v := 1) (w := 4) (by unfold oppositePair; decide +kernel) hlen hSL hcomp'
  · subst P'
    exact no_one_pair_seven (v := 2) (w := 3) (by unfold oppositePair; decide +kernel) hlen hSL hcomp'
  · obtain ⟨S, hSlen, hSL', hcomp''⟩ := canonical_two_pair_reduction (Or.inl h4) hlen hSL hcomp'
    exact hcanonical S hSlen hSL' hcomp''
  · obtain ⟨S, hSlen, hSL', hcomp''⟩ := canonical_two_pair_reduction (Or.inr (Or.inl h5)) hlen hSL hcomp'
    exact hcanonical S hSlen hSL' hcomp''
  · obtain ⟨S, hSlen, hSL', hcomp''⟩ := canonical_two_pair_reduction (Or.inr (Or.inr h6)) hlen hSL hcomp'
    exact hcanonical S hSlen hSL' hcomp''
  · subst P'
    exact no_three_pairs_seven hlen hSL hcomp'

end C6

namespace ReadOnceCore

def listBits : List Nat → Nat
  | [] => 0
  | x :: xs => (2 ^ x) ||| listBits xs

lemma listBits_mem (xs : List Nat) (x : Nat) :
    (listBits xs).testBit x = true ↔ x ∈ xs := by
  induction xs with
  | nil => simp only [listBits, Nat.zero_testBit, Bool.false_eq_true, List.not_mem_nil]
  | cons y ys ih =>
    simp only [listBits, Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow,
      decide_eq_true_eq, ih, List.mem_cons]
    exact or_congr eq_comm Iff.rfl

def checkTable (choices : Nat → List Nat) (bits : Nat → Nat) (s : Nat) : Bool :=
  listBits (choices s) == bits s

def checkClosed (choices : Nat → List Nat) (bits : Nat → Nat) (a b : Nat) : Bool :=
  if a < b ∧ a &&& b = 0 then
    (choices a).all fun x => (choices b).all fun y =>
      (bits (a ||| b)).testBit (x &&& y) && (bits (a ||| b)).testBit (x ||| y)
  else true

def Allowed (bits : Nat → Nat) (s x : Nat) : Prop :=
  (bits s).testBit x = true

lemma allowed_iff_mem (choices : Nat → List Nat) (bits : Nat → Nat) (s x : Nat)
    (h : checkTable choices bits s = true) : Allowed bits s x ↔ x ∈ choices s := by
  have heq : listBits (choices s) = bits s := by
    simpa only [checkTable, beq_iff_eq] using h
  unfold Allowed
  rw [← heq]
  exact listBits_mem _ _

lemma ordered_closed (choices : Nat → List Nat) (bits : Nat → Nat)
    {a b x y : Nat} (hab : a < b) (hd : a &&& b = 0)
    (ha : checkTable choices bits a = true) (hb : checkTable choices bits b = true)
    (hc : checkClosed choices bits a b = true)
    (hx : Allowed bits a x) (hy : Allowed bits b y) :
    Allowed bits (a ||| b) (x &&& y) ∧ Allowed bits (a ||| b) (x ||| y) := by
  have hxa := (allowed_iff_mem choices bits a x ha).mp hx
  have hyb := (allowed_iff_mem choices bits b y hb).mp hy
  rw [checkClosed, ite_eq_left ⟨hab, hd⟩] at hc
  have hxy := List.all_eq_true.mp (List.all_eq_true.mp hc x hxa) y hyb
  simpa only [Allowed, Bool.and_eq_true] using hxy

lemma union_lt_two_pow {a b n : Nat} (ha : a < 2 ^ n) (hb : b < 2 ^ n) :
    a ||| b < 2 ^ n := Nat.or_lt_two_pow ha hb

lemma union_lt_256 {a b : Nat} (ha : a < 256) (hb : b < 256) :
    a ||| b < 256 := by
  exact union_lt_two_pow (n := 8) ha hb

lemma disjoint_closed (choices : Nat → List Nat) (bits : Nat → Nat)
    (hzero : bits 0 = 0)
    (htable : ∀ s : Fin 256, checkTable choices bits s = true)
    (hclosed : ∀ a b : Fin 256, checkClosed choices bits a b = true)
    {a b x y : Nat} (ha : a < 256) (hb : b < 256) (hd : a &&& b = 0)
    (hx : Allowed bits a x) (hy : Allowed bits b y) :
    Allowed bits (a ||| b) (x &&& y) ∧ Allowed bits (a ||| b) (x ||| y) := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact ordered_closed choices bits hab hd (htable ⟨a, ha⟩) (htable ⟨b, hb⟩)
      (hclosed ⟨a, ha⟩ ⟨b, hb⟩) hx hy
  · subst b
    have hz : a = 0 := by simpa only [Nat.and_self] using hd
    subst a
    simp only [Allowed, hzero, Nat.zero_testBit, Bool.false_eq_true] at hx
  · have hdb : b &&& a = 0 := by simpa only [Nat.and_comm] using hd
    have h := ordered_closed choices bits hab hdb (htable ⟨b, hb⟩) (htable ⟨a, ha⟩)
      (hclosed ⟨b, hb⟩ ⟨a, ha⟩) hy hx
    simpa only [Nat.or_comm, Nat.and_comm] using h

lemma trace_allowed (choices : Nat → List Nat) (bits : Nat → Nat)
    (hzero : bits 0 = 0)
    (htable : ∀ s : Fin 256, checkTable choices bits s = true)
    (hclosed : ∀ a b : Fin 256, checkClosed choices bits a b = true)
    (n k : Nat) (resource value left right : Nat → Nat) (tag : Nat → Bool)
    (hinput : ∀ i, i < n → resource i < 256 ∧ Allowed bits (resource i) (value i))
    (hgate : ∀ i, n ≤ i → i < n + k →
      left i < i ∧ right i < i ∧
      resource i = resource (left i) ||| resource (right i) ∧
      resource (left i) &&& resource (right i) = 0 ∧
      value i = if tag i then value (left i) &&& value (right i)
        else value (left i) ||| value (right i)) :
    ∀ i, i < n + k → resource i < 256 ∧ Allowed bits (resource i) (value i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases hin : i < n
    · exact hinput i hin
    · obtain ⟨hl, hr, hresource, hd, hvalue⟩ := hgate i (by omega) hi
      obtain ⟨hbl, hal⟩ := ih (left i) hl (by omega)
      obtain ⟨hbr, har⟩ := ih (right i) hr (by omega)
      have hc := disjoint_closed choices bits hzero htable hclosed hbl hbr hd hal har
      refine ⟨?_, ?_⟩
      · rw [hresource]
        exact union_lt_256 hbl hbr
      · rw [hresource, hvalue]
        cases ht : tag i
        · exact hc.2
        · exact hc.1

end ReadOnceCore

namespace ReadOnceEncoding

def resourceMask (S : Finset (Fin 8)) : Nat := ∑ i ∈ S, 2 ^ i.val

def truthBits {n : Nat} (f : Fin n → Bool) : Nat := ∑ i : Fin n, if f i then 2 ^ i.val else 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma resourceMask_bound : ∀ S : Finset (Fin 8), resourceMask S < 256 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma resourceMask_testBit : ∀ S : Finset (Fin 8), ∀ i : Fin 8,
    (resourceMask S).testBit i.val = decide (i ∈ S) := by
  decide +kernel

lemma truthBits_zero (f : Fin 0 → Bool) : truthBits f = 0 := by
  simp [truthBits]

lemma truthBits_succ {n : Nat} (f : Fin (n + 1) → Bool) :
    truthBits f = Nat.bit (f 0) (truthBits (fun i => f i.succ)) := by
  rw [truthBits, Fin.sum_univ_succ, Nat.bit_val]
  simp only [Fin.val_zero, pow_zero, Fin.val_succ, pow_succ, truthBits]
  rw [Finset.mul_sum]
  have h (i : Fin n) : (if f i.succ then 2 ^ i.val * 2 else 0) =
      2 * (if f i.succ then 2 ^ i.val else 0) := by
    split <;> simp_all [Nat.mul_comm]
  simp_rw [h]
  cases hf : f 0 <;> simp [Bool.toNat, Nat.add_comm]

lemma truthBits_bound {n : Nat} (f : Fin n → Bool) : truthBits f < 2 ^ n := by
  induction n with
  | zero => simp [truthBits]
  | succ n ih =>
    rw [truthBits_succ, Nat.bit_val, pow_succ]
    have h := ih (fun i => f i.succ)
    cases hf : f 0 <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

lemma truthBits_testBit {n : Nat} (f : Fin n → Bool) (i : Fin n) :
    (truthBits f).testBit i.val = f i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    rw [truthBits_succ]
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Nat.testBit_bit_zero _ _
    · simpa only [Fin.val_succ, Nat.testBit_bit_succ] using ih (fun k => f k.succ) j

lemma testBit_false_of_bound {a n i : Nat} (ha : a < 2 ^ n) (hi : n ≤ i) :
    a.testBit i = false := by
  exact Nat.testBit_lt_two_pow (ha.trans_le (Nat.pow_le_pow_right (by decide) hi))

lemma resourceMask_singleton (i : Fin 8) : resourceMask {i} = 2 ^ i.val := by
  simp [resourceMask]

lemma resourceMask_empty : resourceMask ∅ = 0 := by
  simp [resourceMask]

lemma resourceMask_univ : resourceMask Finset.univ = 255 := by
  decide +kernel

lemma resourceMask_union (S T : Finset (Fin 8)) :
    resourceMask (S ∪ T) = resourceMask S ||| resourceMask T := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or]
  by_cases hi : i < 8
  · have h (U : Finset (Fin 8)) : (resourceMask U).testBit i = decide (⟨i, hi⟩ ∈ U) :=
      resourceMask_testBit U ⟨i, hi⟩
    rw [h, h, h]
    simp only [Finset.mem_union, Bool.decide_or]
  · have h (U : Finset (Fin 8)) : (resourceMask U).testBit i = false :=
      testBit_false_of_bound (n := 8) (resourceMask_bound U) (by omega)
    rw [h, h, h]
    rfl

lemma resourceMask_disjoint {S T : Finset (Fin 8)} (hd : Disjoint S T) :
    resourceMask S &&& resourceMask T = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.zero_testBit]
  by_cases hi : i < 8
  · have h (U : Finset (Fin 8)) : (resourceMask U).testBit i = decide (⟨i, hi⟩ ∈ U) :=
      resourceMask_testBit U ⟨i, hi⟩
    rw [h, h]
    have hnot : ¬ (⟨i, hi⟩ ∈ S ∧ ⟨i, hi⟩ ∈ T) := by
      rintro ⟨hs, ht⟩
      exact Finset.disjoint_left.mp hd hs ht
    simpa only [← Bool.decide_and, decide_eq_false_iff_not] using hnot
  · have h (U : Finset (Fin 8)) : (resourceMask U).testBit i = false :=
      testBit_false_of_bound (n := 8) (resourceMask_bound U) (by omega)
    rw [h, h]
    rfl

lemma truthBits_and {n : Nat} (f g : Fin n → Bool) :
    truthBits (fun i => f i && g i) = truthBits f &&& truthBits g := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < n
  · have h (f : Fin n → Bool) : (truthBits f).testBit i = f ⟨i, hi⟩ :=
      truthBits_testBit f ⟨i, hi⟩
    rw [h, h, h]
  · have h (f : Fin n → Bool) : (truthBits f).testBit i = false :=
      testBit_false_of_bound (n := n) (truthBits_bound f) (by omega)
    rw [h, h, h]
    rfl

lemma truthBits_or {n : Nat} (f g : Fin n → Bool) :
    truthBits (fun i => f i || g i) = truthBits f ||| truthBits g := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or]
  by_cases hi : i < n
  · have h (f : Fin n → Bool) : (truthBits f).testBit i = f ⟨i, hi⟩ :=
      truthBits_testBit f ⟨i, hi⟩
    rw [h, h, h]
  · have h (f : Fin n → Bool) : (truthBits f).testBit i = false :=
      testBit_false_of_bound (n := n) (truthBits_bound f) (by omega)
    rw [h, h, h]
    rfl

end ReadOnceEncoding

namespace ReadOnce

set_option maxRecDepth 100000 in
def choicesData : List (List Nat) := [
  [],
  [81],
  [22],
  [16, 87],
  [24],
  [16, 89],
  [16, 30],
  [16, 22, 24, 81, 95],
  [35],
  [1, 115],
  [2, 55],
  [0, 3, 17, 18, 23, 51, 83, 119],
  [0, 59],
  [0, 1, 16, 17, 25, 51, 81, 123],
  [0, 2, 16, 18, 22, 26, 51, 63],
  [0, 1, 2, 3, 16, 17, 18, 19, 22, 23, 24, 25, 26, 27, 31, 51, 55, 59, 81, 83, 87, 91, 115, 127],
  [32],
  [0, 113],
  [0, 54],
  [0, 16, 22, 48, 81, 119],
  [0, 56],
  [0, 16, 24, 48, 81, 121],
  [0, 16, 22, 24, 48, 62],
  [0, 16, 22, 24, 30, 48, 54, 56, 81, 87, 89, 113, 127],
  [32, 35],
  [0, 1, 32, 33, 35, 113, 115],
  [0, 2, 32, 34, 35, 54, 55],
  [0, 1, 2, 3, 16, 17, 18, 22, 23, 32, 35, 48, 49, 50, 51, 54, 55, 81, 83, 113, 115, 119],
  [0, 32, 35, 56, 59],
  [0, 1, 16, 17, 24, 25, 32, 33, 35, 48, 49, 51, 56, 57, 59, 81, 113, 115, 121, 123],
  [0, 2, 16, 18, 22, 24, 26, 32, 34, 35, 48, 50, 51, 54, 55, 56, 58, 59, 62, 63],
  [0, 1, 2, 3, 16, 17, 18, 19, 22, 23, 24, 25, 26, 27, 30, 31, 32, 33, 34, 35, 48, 49, 50, 51, 54, 55, 56, 57, 58, 59, 62, 63, 81, 83, 87, 89, 91, 113, 115, 119, 121, 123, 127],
  [108],
  [64, 125],
  [4, 126],
  [0, 20, 68, 80, 85, 86, 124, 127],
  [8, 124],
  [0, 24, 72, 80, 88, 89, 124, 125],
  [0, 12, 20, 24, 28, 30, 124, 126],
  [0, 4, 8, 16, 20, 22, 24, 28, 30, 64, 76, 80, 81, 84, 85, 86, 88, 89, 92, 93, 94, 95, 124, 125, 126, 127],
  [32, 111],
  [0, 33, 65, 96, 99, 109, 113, 127],
  [0, 6, 34, 36, 39, 54, 110, 127],
  [0, 1, 2, 4, 5, 16, 22, 32, 35, 48, 53, 55, 64, 66, 71, 81, 87, 100, 103, 108, 111, 114, 115, 117, 118, 119, 125, 126, 127],
  [0, 8, 32, 40, 43, 56, 108, 127],
  [0, 1, 8, 9, 16, 24, 32, 33, 35, 48, 57, 59, 64, 73, 81, 89, 104, 107, 108, 109, 112, 113, 115, 120, 121, 123, 124, 125, 127],
  [0, 2, 4, 8, 10, 14, 16, 22, 24, 30, 32, 34, 35, 44, 47, 48, 52, 54, 55, 58, 59, 60, 62, 63, 108, 110, 124, 126, 127],
  [0, 1, 2, 3, 4, 5, 6, 8, 11, 12, 13, 16, 17, 18, 20, 21, 22, 23, 24, 25, 26, 28, 29, 30, 31, 32, 33, 34, 35, 36, 39, 40, 43, 48, 49, 50, 51, 52, 53, 54, 55, 56, 59, 61, 63, 64, 65, 66, 68, 72, 74, 79, 80, 81, 82, 83, 85, 86, 87, 88, 89, 90, 91, 95, 96, 99, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 122, 123, 124, 125, 126, 127],
  [32, 108],
  [0, 32, 64, 96, 108, 113, 125],
  [0, 4, 32, 36, 54, 108, 126],
  [0, 4, 16, 20, 22, 32, 48, 52, 54, 64, 68, 80, 81, 85, 86, 100, 108, 112, 113, 117, 118, 119, 124, 125, 126, 127],
  [0, 8, 32, 40, 56, 108, 124],
  [0, 8, 16, 24, 32, 48, 56, 64, 72, 80, 81, 88, 89, 104, 108, 112, 113, 120, 121, 124, 125],
  [0, 4, 8, 12, 16, 20, 22, 24, 28, 30, 32, 44, 48, 52, 54, 56, 60, 62, 108, 124, 126],
  [0, 4, 8, 12, 16, 20, 22, 24, 28, 30, 32, 36, 40, 48, 52, 54, 56, 60, 62, 64, 68, 72, 76, 80, 81, 84, 85, 86, 87, 88, 89, 92, 93, 94, 95, 96, 108, 112, 113, 116, 117, 118, 119, 120, 121, 124, 125, 126, 127],
  [32, 35, 108, 111],
  [0, 1, 32, 33, 35, 64, 65, 96, 97, 99, 108, 109, 111, 113, 115, 125, 127],
  [0, 2, 4, 6, 32, 34, 35, 36, 38, 39, 54, 55, 108, 110, 111, 126, 127],
  [0, 1, 2, 3, 4, 5, 6, 16, 17, 18, 20, 22, 23, 32, 33, 34, 35, 36, 37, 39, 48, 49, 50, 51, 52, 53, 54, 55, 64, 65, 66, 68, 71, 80, 81, 83, 85, 86, 87, 96, 98, 99, 100, 103, 108, 109, 110, 111, 112, 113, 114, 115, 117, 118, 119, 124, 125, 126, 127],
  [0, 8, 32, 35, 40, 43, 56, 59, 108, 111, 124, 127],
  [0, 1, 8, 9, 16, 17, 24, 25, 32, 33, 35, 40, 41, 43, 48, 49, 51, 56, 57, 59, 64, 65, 72, 73, 80, 81, 88, 89, 96, 99, 104, 105, 107, 108, 109, 111, 112, 113, 115, 120, 121, 123, 124, 125, 127],
  [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 35, 36, 39, 40, 42, 43, 44, 46, 47, 48, 50, 51, 52, 54, 55, 56, 58, 59, 60, 62, 63, 108, 110, 111, 124, 126, 127],
  [0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 43, 44, 45, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 68, 71, 72, 73, 74, 76, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 103, 104, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127],
  [125],
  [81, 125],
  [20, 127],
  [16, 20, 81, 85, 87, 125, 127],
  [24, 125],
  [16, 24, 81, 89, 125],
  [16, 20, 24, 28, 30, 125, 127],
  [16, 20, 22, 24, 28, 30, 81, 85, 87, 89, 93, 95, 125, 127],
  [33, 127],
  [1, 33, 81, 113, 115, 125, 127],
  [0, 22, 35, 53, 55, 127],
  [0, 1, 3, 16, 17, 18, 20, 21, 22, 23, 33, 35, 49, 51, 53, 55, 81, 83, 87, 115, 117, 119, 125, 127],
  [0, 24, 33, 57, 59, 125, 127],
  [0, 1, 16, 17, 24, 25, 33, 49, 51, 57, 59, 81, 89, 113, 115, 121, 123, 125, 127],
  [0, 2, 16, 18, 20, 22, 24, 26, 30, 33, 35, 49, 51, 53, 55, 59, 61, 63, 125, 127],
  [0, 1, 2, 3, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 33, 35, 49, 51, 53, 55, 57, 59, 61, 63, 81, 83, 85, 87, 89, 91, 95, 113, 115, 117, 119, 123, 125, 127],
  [32, 125],
  [0, 32, 81, 113, 125],
  [0, 20, 32, 52, 54, 125, 127],
  [0, 16, 20, 22, 32, 48, 52, 54, 81, 85, 87, 113, 117, 119, 125, 127],
  [0, 24, 32, 56, 125],
  [0, 16, 24, 32, 48, 56, 81, 89, 113, 121, 125],
  [0, 16, 20, 22, 24, 28, 30, 32, 48, 52, 54, 56, 60, 62, 125, 127],
  [0, 16, 20, 22, 24, 28, 30, 32, 48, 52, 54, 56, 60, 62, 81, 85, 87, 89, 93, 95, 113, 117, 119, 121, 125, 127],
  [32, 33, 35, 125, 127],
  [0, 1, 32, 33, 35, 81, 113, 115, 125, 127],
  [0, 2, 20, 22, 32, 33, 34, 35, 52, 53, 54, 55, 125, 127],
  [0, 1, 2, 3, 16, 17, 18, 20, 21, 22, 23, 32, 33, 34, 35, 48, 49, 50, 51, 52, 53, 54, 55, 81, 83, 85, 87, 113, 115, 117, 119, 125, 127],
  [0, 24, 32, 33, 35, 56, 57, 59, 125, 127],
  [0, 1, 16, 17, 24, 25, 32, 33, 35, 48, 49, 51, 56, 57, 59, 81, 89, 113, 115, 121, 123, 125, 127],
  [0, 2, 16, 18, 20, 22, 24, 26, 28, 30, 32, 33, 34, 35, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 125, 127],
  [0, 1, 2, 3, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 81, 83, 85, 87, 89, 91, 93, 95, 113, 115, 117, 119, 121, 123, 125, 127],
  [108, 125],
  [64, 81, 108, 125],
  [4, 20, 108, 124, 125, 126, 127],
  [0, 4, 16, 20, 64, 68, 80, 81, 84, 85, 86, 87, 108, 124, 125, 126, 127],
  [8, 24, 108, 124, 125],
  [0, 8, 16, 24, 64, 72, 80, 81, 88, 89, 108, 124, 125],
  [0, 4, 8, 12, 16, 20, 24, 28, 30, 108, 124, 125, 126, 127],
  [0, 4, 8, 12, 16, 20, 22, 24, 28, 30, 64, 68, 72, 76, 80, 81, 84, 85, 86, 87, 88, 89, 92, 93, 94, 95, 108, 124, 125, 126, 127],
  [32, 33, 108, 109, 111, 125, 127],
  [0, 1, 32, 33, 64, 65, 81, 96, 97, 99, 108, 109, 111, 113, 115, 125, 127],
  [0, 4, 6, 20, 22, 32, 33, 34, 35, 36, 37, 39, 52, 53, 54, 55, 108, 110, 111, 125, 126, 127],
  [0, 1, 2, 3, 4, 5, 6, 16, 17, 18, 20, 21, 22, 23, 32, 33, 34, 35, 36, 37, 39, 48, 49, 51, 52, 53, 54, 55, 64, 65, 66, 68, 69, 71, 80, 81, 83, 85, 86, 87, 96, 99, 100, 101, 103, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 124, 125, 126, 127],
  [0, 8, 24, 32, 33, 40, 41, 43, 56, 57, 59, 108, 109, 111, 124, 125, 127],
  [0, 1, 8, 9, 16, 17, 24, 25, 32, 33, 35, 40, 41, 43, 48, 49, 51, 56, 57, 59, 64, 65, 72, 73, 80, 81, 88, 89, 96, 97, 99, 104, 105, 107, 108, 109, 111, 112, 113, 115, 120, 121, 123, 124, 125, 127],
  [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32, 33, 34, 35, 36, 37, 39, 40, 43, 44, 45, 47, 48, 49, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 108, 109, 110, 111, 124, 125, 126, 127],
  [0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 39, 40, 41, 43, 44, 45, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 68, 69, 71, 72, 73, 74, 76, 77, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 99, 100, 101, 103, 104, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127],
  [32, 108, 125],
  [0, 32, 64, 81, 96, 108, 113, 125],
  [0, 4, 20, 32, 36, 52, 54, 108, 124, 125, 126, 127],
  [0, 4, 16, 20, 22, 32, 36, 48, 52, 54, 64, 68, 80, 81, 84, 85, 86, 87, 96, 100, 108, 112, 113, 116, 117, 118, 119, 124, 125, 126, 127],
  [0, 8, 24, 32, 40, 56, 108, 124, 125],
  [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80, 81, 88, 89, 96, 104, 108, 112, 113, 120, 121, 124, 125],
  [0, 4, 8, 12, 16, 20, 22, 24, 28, 30, 32, 36, 40, 44, 48, 52, 54, 56, 60, 62, 108, 124, 125, 126, 127],
  [0, 4, 8, 12, 16, 20, 22, 24, 28, 30, 32, 36, 40, 44, 48, 52, 54, 56, 60, 62, 64, 68, 72, 76, 80, 81, 84, 85, 86, 87, 88, 89, 92, 93, 94, 95, 96, 100, 104, 108, 112, 113, 116, 117, 118, 119, 120, 121, 124, 125, 126, 127],
  [32, 33, 35, 108, 109, 111, 125, 127],
  [0, 1, 32, 33, 35, 64, 65, 81, 96, 97, 99, 108, 109, 111, 113, 115, 125, 127],
  [0, 2, 4, 6, 20, 22, 32, 33, 34, 35, 36, 37, 38, 39, 52, 53, 54, 55, 108, 109, 110, 111, 124, 125, 126, 127],
  [0, 1, 2, 3, 4, 5, 6, 16, 17, 18, 20, 21, 22, 23, 32, 33, 34, 35, 36, 37, 38, 39, 48, 49, 50, 51, 52, 53, 54, 55, 64, 65, 66, 68, 69, 71, 80, 81, 83, 84, 85, 86, 87, 96, 97, 98, 99, 100, 101, 103, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 124, 125, 126, 127],
  [0, 8, 24, 32, 33, 35, 40, 41, 43, 56, 57, 59, 108, 109, 111, 124, 125, 127],
  [0, 1, 8, 9, 16, 17, 24, 25, 32, 33, 35, 40, 41, 43, 48, 49, 51, 56, 57, 59, 64, 65, 72, 73, 80, 81, 88, 89, 96, 97, 99, 104, 105, 107, 108, 109, 111, 112, 113, 115, 120, 121, 123, 124, 125, 127],
  [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 108, 109, 110, 111, 124, 125, 126, 127],
  [0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 68, 69, 71, 72, 73, 74, 76, 77, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127],
  [54],
  [16, 119],
  [22, 54],
  [16, 22, 54, 87, 119],
  [16, 62],
  [16, 24, 54, 81, 127],
  [16, 22, 30, 54, 62],
  [16, 22, 24, 30, 54, 62, 81, 87, 95, 119, 127],
  [34, 55],
  [0, 17, 35, 50, 51, 55, 115, 119],
  [2, 22, 34, 54, 55],
  [0, 2, 3, 16, 17, 18, 22, 23, 34, 35, 50, 51, 54, 55, 83, 87, 115, 119],
  [0, 16, 34, 50, 51, 54, 58, 63],
  [0, 1, 16, 17, 24, 25, 34, 35, 50, 51, 54, 55, 58, 59, 63, 81, 115, 119, 123, 127],
  [0, 2, 16, 18, 22, 26, 30, 34, 50, 51, 54, 55, 58, 62, 63],
  [0, 1, 2, 3, 16, 17, 18, 19, 22, 23, 24, 25, 26, 27, 30, 31, 34, 35, 50, 51, 54, 55, 58, 59, 62, 63, 81, 83, 87, 91, 95, 115, 119, 123, 127],
  [32, 54],
  [0, 16, 32, 48, 54, 113, 119],
  [0, 22, 32, 54],
  [0, 16, 22, 32, 48, 54, 81, 87, 113, 119],
  [0, 16, 32, 48, 54, 56, 62],
  [0, 16, 24, 32, 48, 54, 56, 62, 81, 113, 119, 121, 127],
  [0, 16, 22, 24, 30, 32, 48, 54, 56, 62],
  [0, 16, 22, 24, 30, 32, 48, 54, 56, 62, 81, 87, 89, 95, 113, 119, 121, 127],
  [32, 34, 35, 54, 55],
  [0, 1, 16, 17, 32, 33, 34, 35, 48, 49, 50, 51, 54, 55, 113, 115, 119],
  [0, 2, 22, 32, 34, 35, 54, 55],
  [0, 1, 2, 3, 16, 17, 18, 22, 23, 32, 33, 34, 35, 48, 49, 50, 51, 54, 55, 81, 83, 87, 113, 115, 119],
  [0, 16, 32, 34, 35, 48, 50, 51, 54, 55, 56, 58, 59, 62, 63],
  [0, 1, 16, 17, 24, 25, 32, 33, 34, 35, 48, 49, 50, 51, 54, 55, 56, 57, 58, 59, 62, 63, 81, 113, 115, 119, 121, 123, 127],
  [0, 2, 16, 18, 22, 24, 26, 30, 32, 34, 35, 48, 50, 51, 54, 55, 56, 58, 59, 62, 63],
  [0, 1, 2, 3, 16, 17, 18, 19, 22, 23, 24, 25, 26, 27, 30, 31, 32, 33, 34, 35, 48, 49, 50, 51, 54, 55, 56, 57, 58, 59, 62, 63, 81, 83, 87, 89, 91, 95, 113, 115, 119, 121, 123, 127],
  [36, 126],
  [0, 52, 80, 100, 117, 118, 124, 127],
  [4, 22, 36, 54, 126],
  [0, 4, 16, 20, 22, 36, 52, 54, 68, 80, 85, 86, 87, 100, 117, 118, 119, 124, 126, 127],
  [0, 24, 44, 52, 60, 62, 124, 126],
  [0, 8, 16, 24, 36, 52, 54, 60, 62, 64, 80, 81, 88, 89, 108, 116, 117, 118, 124, 125, 126, 127],
  [0, 4, 12, 16, 20, 22, 24, 28, 30, 36, 44, 52, 54, 60, 62, 124, 126],
  [0, 4, 8, 12, 16, 20, 22, 24, 28, 30, 36, 44, 52, 54, 60, 62, 64, 68, 76, 80, 81, 84, 85, 86, 87, 88, 89, 92, 93, 94, 95, 100, 108, 116, 117, 118, 119, 124, 125, 126, 127],
  [32, 34, 36, 38, 39, 54, 110, 127],
  [0, 1, 16, 32, 33, 34, 35, 36, 37, 48, 53, 54, 55, 64, 81, 96, 98, 100, 103, 108, 111, 113, 114, 115, 117, 118, 119, 125, 126, 127],
  [0, 2, 4, 6, 22, 32, 34, 36, 38, 39, 54, 55, 110, 126, 127],
  [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 20, 21, 22, 23, 32, 33, 34, 35, 36, 37, 38, 39, 48, 50, 51, 52, 53, 54, 55, 64, 66, 68, 70, 71, 80, 81, 82, 83, 85, 86, 87, 96, 98, 100, 102, 103, 108, 110, 111, 113, 114, 115, 117, 118, 119, 124, 125, 126, 127],
  [0, 8, 16, 24, 32, 34, 35, 36, 40, 42, 44, 46, 47, 48, 52, 54, 55, 56, 58, 59, 60, 62, 63, 108, 110, 124, 126, 127],
  [0, 1, 8, 16, 17, 24, 25, 32, 33, 34, 35, 36, 37, 38, 39, 40, 43, 44, 45, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 72, 80, 81, 88, 89, 96, 98, 99, 100, 104, 106, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127],
  [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 35, 36, 38, 39, 40, 42, 44, 46, 47, 48, 50, 51, 52, 54, 55, 56, 58, 59, 60, 62, 63, 108, 110, 124, 126, 127],
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 68, 70, 71, 72, 74, 76, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 98, 99, 100, 102, 103, 104, 106, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127],
  [32, 36, 54, 108, 126],
  [0, 16, 32, 36, 48, 52, 54, 64, 80, 96, 100, 108, 112, 113, 117, 118, 119, 124, 125, 126, 127],
  [0, 4, 22, 32, 36, 54, 108, 126],
  [0, 4, 16, 20, 22, 32, 36, 48, 52, 54, 64, 68, 80, 81, 85, 86, 87, 96, 100, 108, 112, 113, 117, 118, 119, 124, 125, 126, 127],
  [0, 8, 16, 24, 32, 36, 40, 44, 48, 52, 54, 56, 60, 62, 108, 124, 126],
  [0, 8, 16, 24, 32, 36, 40, 44, 48, 52, 54, 56, 60, 62, 64, 72, 80, 81, 88, 89, 96, 100, 104, 108, 112, 113, 116, 117, 118, 119, 120, 121, 124, 125, 126, 127],
  [0, 4, 8, 12, 16, 20, 22, 24, 28, 30, 32, 36, 40, 44, 48, 52, 54, 56, 60, 62, 108, 124, 126],
  [0, 4, 8, 12, 16, 20, 22, 24, 28, 30, 32, 36, 40, 44, 48, 52, 54, 56, 60, 62, 64, 68, 72, 76, 80, 81, 84, 85, 86, 87, 88, 89, 92, 93, 94, 95, 96, 100, 104, 108, 112, 113, 116, 117, 118, 119, 120, 121, 124, 125, 126, 127],
  [32, 34, 35, 36, 38, 39, 54, 55, 108, 110, 111, 126, 127],
  [0, 1, 16, 17, 32, 33, 34, 35, 36, 37, 38, 39, 48, 49, 50, 51, 52, 53, 54, 55, 64, 65, 80, 81, 96, 97, 98, 99, 100, 103, 108, 109, 110, 111, 112, 113, 114, 115, 117, 118, 119, 124, 125, 126, 127],
  [0, 2, 4, 6, 22, 32, 34, 35, 36, 38, 39, 54, 55, 108, 110, 111, 126, 127],
  [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 20, 21, 22, 23, 32, 33, 34, 35, 36, 37, 38, 39, 48, 49, 50, 51, 52, 53, 54, 55, 64, 65, 66, 68, 70, 71, 80, 81, 82, 83, 85, 86, 87, 96, 97, 98, 99, 100, 102, 103, 108, 109, 110, 111, 112, 113, 114, 115, 117, 118, 119, 124, 125, 126, 127],
  [0, 8, 16, 24, 32, 34, 35, 36, 38, 39, 40, 42, 43, 44, 46, 47, 48, 50, 51, 52, 54, 55, 56, 58, 59, 60, 62, 63, 108, 110, 111, 124, 126, 127],
  [0, 1, 8, 9, 16, 17, 24, 25, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 72, 73, 80, 81, 88, 89, 96, 97, 98, 99, 100, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127],
  [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 35, 36, 38, 39, 40, 42, 43, 44, 46, 47, 48, 50, 51, 52, 54, 55, 56, 58, 59, 60, 62, 63, 108, 110, 111, 124, 126, 127],
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 68, 70, 71, 72, 73, 74, 76, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127],
  [52, 127],
  [16, 52, 81, 117, 119, 125, 127],
  [20, 22, 52, 54, 127],
  [16, 20, 22, 52, 54, 81, 85, 87, 117, 119, 125, 127],
  [16, 24, 52, 60, 62, 125, 127],
  [16, 24, 52, 54, 60, 62, 81, 89, 117, 119, 125, 127],
  [16, 20, 22, 24, 28, 30, 52, 54, 60, 62, 125, 127],
  [16, 20, 22, 24, 28, 30, 52, 54, 60, 62, 81, 85, 87, 89, 93, 95, 117, 119, 125, 127],
  [32, 35, 53, 54, 55, 127],
  [0, 1, 16, 17, 32, 33, 35, 48, 49, 50, 51, 52, 53, 54, 55, 81, 113, 115, 117, 119, 125, 127],
  [0, 2, 20, 22, 32, 34, 35, 52, 53, 54, 55, 127],
  [0, 1, 2, 3, 16, 17, 18, 20, 21, 22, 23, 32, 33, 34, 35, 48, 49, 50, 51, 52, 53, 54, 55, 81, 83, 85, 87, 113, 115, 117, 119, 125, 127],
  [0, 16, 24, 32, 33, 34, 35, 48, 49, 50, 51, 52, 53, 54, 55, 56, 58, 59, 61, 62, 63, 125, 127],
  [0, 1, 16, 17, 24, 25, 32, 33, 34, 35, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 81, 89, 113, 115, 117, 119, 121, 123, 125, 127],
  [0, 2, 16, 18, 20, 22, 24, 26, 28, 30, 32, 33, 34, 35, 48, 49, 50, 51, 52, 53, 54, 55, 56, 58, 59, 60, 61, 62, 63, 125, 127],
  [0, 1, 2, 3, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 81, 83, 85, 87, 89, 91, 93, 95, 113, 115, 117, 119, 121, 123, 125, 127],
  [32, 52, 54, 125, 127],
  [0, 16, 32, 48, 52, 54, 81, 113, 117, 119, 125, 127],
  [0, 20, 22, 32, 52, 54, 125, 127],
  [0, 16, 20, 22, 32, 48, 52, 54, 81, 85, 87, 113, 117, 119, 125, 127],
  [0, 16, 24, 32, 48, 52, 54, 56, 60, 62, 125, 127],
  [0, 16, 24, 32, 48, 52, 54, 56, 60, 62, 81, 89, 113, 117, 119, 121, 125, 127],
  [0, 16, 20, 22, 24, 28, 30, 32, 48, 52, 54, 56, 60, 62, 125, 127],
  [0, 16, 20, 22, 24, 28, 30, 32, 48, 52, 54, 56, 60, 62, 81, 85, 87, 89, 93, 95, 113, 117, 119, 121, 125, 127],
  [32, 33, 34, 35, 52, 53, 54, 55, 125, 127],
  [0, 1, 16, 17, 32, 33, 34, 35, 48, 49, 50, 51, 52, 53, 54, 55, 81, 113, 115, 117, 119, 125, 127],
  [0, 2, 20, 22, 32, 33, 34, 35, 52, 53, 54, 55, 125, 127],
  [0, 1, 2, 3, 16, 17, 18, 20, 21, 22, 23, 32, 33, 34, 35, 48, 49, 50, 51, 52, 53, 54, 55, 81, 83, 85, 87, 113, 115, 117, 119, 125, 127],
  [0, 16, 24, 32, 33, 34, 35, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 125, 127],
  [0, 1, 16, 17, 24, 25, 32, 33, 34, 35, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 81, 89, 113, 115, 117, 119, 121, 123, 125, 127],
  [0, 2, 16, 18, 20, 22, 24, 26, 28, 30, 32, 33, 34, 35, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 125, 127],
  [0, 1, 2, 3, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 81, 83, 85, 87, 89, 91, 93, 95, 113, 115, 117, 119, 121, 123, 125, 127],
  [36, 52, 108, 124, 125, 126, 127],
  [0, 16, 36, 52, 64, 80, 81, 100, 108, 116, 117, 118, 119, 124, 125, 126, 127],
  [4, 20, 22, 36, 52, 54, 108, 124, 125, 126, 127],
  [0, 4, 16, 20, 22, 36, 52, 54, 64, 68, 80, 81, 84, 85, 86, 87, 100, 108, 116, 117, 118, 119, 124, 125, 126, 127],
  [0, 8, 16, 24, 36, 44, 52, 60, 62, 108, 124, 125, 126, 127],
  [0, 8, 16, 24, 36, 44, 52, 54, 60, 62, 64, 72, 80, 81, 88, 89, 100, 108, 116, 117, 118, 119, 124, 125, 126, 127],
  [0, 4, 8, 12, 16, 20, 22, 24, 28, 30, 36, 44, 52, 54, 60, 62, 108, 124, 125, 126, 127],
  [0, 4, 8, 12, 16, 20, 22, 24, 28, 30, 36, 44, 52, 54, 60, 62, 64, 68, 72, 76, 80, 81, 84, 85, 86, 87, 88, 89, 92, 93, 94, 95, 100, 108, 116, 117, 118, 119, 124, 125, 126, 127],
  [32, 33, 34, 35, 36, 37, 38, 39, 52, 53, 54, 55, 108, 110, 111, 125, 126, 127],
  [0, 1, 16, 17, 32, 33, 34, 35, 36, 37, 38, 39, 48, 49, 50, 51, 52, 53, 54, 55, 64, 65, 80, 81, 96, 98, 99, 100, 101, 103, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 124, 125, 126, 127],
  [0, 2, 4, 6, 20, 22, 32, 33, 34, 35, 36, 37, 38, 39, 52, 53, 54, 55, 108, 110, 111, 124, 125, 126, 127],
  [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 20, 21, 22, 23, 32, 33, 34, 35, 36, 37, 38, 39, 48, 49, 50, 51, 52, 53, 54, 55, 64, 65, 66, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 96, 98, 99, 100, 101, 102, 103, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 124, 125, 126, 127],
  [0, 8, 16, 24, 32, 33, 34, 35, 36, 37, 38, 39, 40, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 108, 109, 110, 111, 124, 125, 126, 127],
  [0, 1, 8, 9, 16, 17, 24, 25, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 72, 73, 80, 81, 88, 89, 96, 97, 98, 99, 100, 101, 103, 104, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127],
  [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32, 33, 34, 35, 36, 37, 38, 39, 40, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 108, 109, 110, 111, 124, 125, 126, 127],
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 68, 69, 70, 71, 72, 73, 74, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127],
  [32, 36, 52, 54, 108, 124, 125, 126, 127],
  [0, 16, 32, 36, 48, 52, 54, 64, 80, 81, 96, 100, 108, 112, 113, 116, 117, 118, 119, 124, 125, 126, 127],
  [0, 4, 20, 22, 32, 36, 52, 54, 108, 124, 125, 126, 127],
  [0, 4, 16, 20, 22, 32, 36, 48, 52, 54, 64, 68, 80, 81, 84, 85, 86, 87, 96, 100, 108, 112, 113, 116, 117, 118, 119, 124, 125, 126, 127],
  [0, 8, 16, 24, 32, 36, 40, 44, 48, 52, 54, 56, 60, 62, 108, 124, 125, 126, 127],
  [0, 8, 16, 24, 32, 36, 40, 44, 48, 52, 54, 56, 60, 62, 64, 72, 80, 81, 88, 89, 96, 100, 104, 108, 112, 113, 116, 117, 118, 119, 120, 121, 124, 125, 126, 127],
  [0, 4, 8, 12, 16, 20, 22, 24, 28, 30, 32, 36, 40, 44, 48, 52, 54, 56, 60, 62, 108, 124, 125, 126, 127],
  [0, 4, 8, 12, 16, 20, 22, 24, 28, 30, 32, 36, 40, 44, 48, 52, 54, 56, 60, 62, 64, 68, 72, 76, 80, 81, 84, 85, 86, 87, 88, 89, 92, 93, 94, 95, 96, 100, 104, 108, 112, 113, 116, 117, 118, 119, 120, 121, 124, 125, 126, 127],
  [32, 33, 34, 35, 36, 37, 38, 39, 52, 53, 54, 55, 108, 109, 110, 111, 124, 125, 126, 127],
  [0, 1, 16, 17, 32, 33, 34, 35, 36, 37, 38, 39, 48, 49, 50, 51, 52, 53, 54, 55, 64, 65, 80, 81, 96, 97, 98, 99, 100, 101, 103, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 124, 125, 126, 127],
  [0, 2, 4, 6, 20, 22, 32, 33, 34, 35, 36, 37, 38, 39, 52, 53, 54, 55, 108, 109, 110, 111, 124, 125, 126, 127],
  [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 20, 21, 22, 23, 32, 33, 34, 35, 36, 37, 38, 39, 48, 49, 50, 51, 52, 53, 54, 55, 64, 65, 66, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 96, 97, 98, 99, 100, 101, 102, 103, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 124, 125, 126, 127],
  [0, 8, 16, 24, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 108, 109, 110, 111, 124, 125, 126, 127],
  [0, 1, 8, 9, 16, 17, 24, 25, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 72, 73, 80, 81, 88, 89, 96, 97, 98, 99, 100, 101, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127],
  [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 108, 109, 110, 111, 124, 125, 126, 127],
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 68, 69, 70, 71, 72, 73, 74, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127]]

set_option maxRecDepth 100000 in
def bitsData : List Nat := [
  0,
  2417851639229258349412352,
  4194304,
  154742504910672534362456064,
  16777216,
  618970019642690137449627648,
  1073807360,
  39616499108771398055142424576,
  34359738368,
  41538374868278621028243970633760770,
  36028797018963972,
  664613997902129343011072363360288777,
  576460752303423489,
  10633823966281744834871937540439605251,
  9225623836740091909,
  170182721837980222195007868413974347791,
  4294967296,
  10384593717069655257060992658440193,
  18014398509481985,
  664613997894875788091414263470555137,
  72057594037927937,
  2658455991572249597447124853903654913,
  4611967493425135617,
  170151568054962431763227310107322810369,
  38654705664,
  51922968585348276285305010536841219,
  54043251363020805,
  716536966489895470991620144026288143,
  648518384996057089,
  13344202926436924857758334630901252099,
  14829509203923894277,
  184150000388057878549757039679418335247,
  324518553658426726783156020576256,
  42535295865117307951368570002680578048,
  85070591730234615865843651857942052880,
  191408831393145151797798740889669992449,
  21267647932558653966460912964485513472,
  63802943798605630577032871598467579905,
  106338239662793269832304564823787573249,
  319014719063723768929066698511892939025,
  2596148429267413814265252459577344,
  170152217804347080905670457518488289281,
  170142481534683865438612451374131052609,
  298975385190430865555403821616998711351,
  170141507979022890158486154365842227457,
  248623906575191956817322407396785586947,
  276481045716030793713537441663494997269,
  336294359172629438232922538089469393279,
  324518553658426726783160315543552,
  42546005056616198547616751749198512129,
  85070916248788274292588449485486555153,
  320193696161591157993305598805511569425,
  21267972451112312393259754818350612737,
  67806549477501662627185403776936771841,
  106338564181346928264890830166479147281,
  324264455785639048130786677396371214609,
  2920666982925840541048442839891968,
  212731972869771918347136995121730420739,
  255215993931901407145033180746809868373,
  320260558154980124793674802542287454335,
  191411752060010811539337793365155512577,
  248626544001804592857832374034778751747,
  276483641864460061127427227486625551701,
  340282318750215161746081671482336837503,
  42535295865117307932921825928971026432,
  42535295865119725784561055187320438784,
  170141183460469231731687303715885154304,
  212676479325782385647386699571158646784,
  42535295865117307932921825928987803648,
  42535295865738695804203745324786843648,
  212676479325586539664609129646215200768,
  212676479375918957238444600705936326656,
  170141183460469231731687303724474040320,
  212728402294174305792533663875086680066,
  170141183460469231731732339746521743361,
  213548785197987222469356922643280232459,
  212676479325586539665329705593841123329,
  226020682252642434541937815305536602115,
  212676479325586539676762656233380708357,
  224192993800731236101667518726518276111,
  42535295865117307932921825933265993728,
  42545680458836795439818116184273846273,
  212676479325586539664631647647288000513,
  213517631416865027723231439453905027073,
  42535295865117307932993883527320698881,
  45204136451025597205340759511315578881,
  212676479325586539670468594240700088321,
  216176087458571431065933619826311364609,
  212676479325586539664609129692099772416,
  212728402294174305792533663913741385731,
  212676479325586539664676683703695441925,
  213559169791742977750865577164024512527,
  212676479325586539665401763226533756929,
  226020682252642434542010154413205946371,
  212676479325586539683055592309444116485,
  226851449802204588167906995933991075855,
  42535620383670966359648609084991602688,
  42535620383673384229734582417050566656,
  319015043506933467923640477623304323088,
  319015043507227237211401481765820366865,
  63803268316229620326109522049493893376,
  63803268317161706873845628086547185921,
  319015043506933467923640477624663347473,
  319015043582432174878218542251273949457,
  212680049029676782358603744373966372864,
  212731972869774336198776224345720094723,
  297751289797018715077968517345819230289,
  320343637123105233025427427561586491519,
  233947696962235436325857302967513776385,
  248626544160260917886361049221866652419,
  319019586766684685916260982737838888277,
  340282239838965449244824692424060141439,
  42535620383670966359648609089286569984,
  42546005056618616399255981007547924481,
  319015043506933467923662995694455619601,
  320276772990729963067650931010200207377,
  63803268316229620326181580747338416385,
  67806549556729825141449742469992349953,
  319015043506933467929499960979565383953,
  324264477335699252010686520432511750417,
  212680049029676782358603744408326111232,
  212731972869774336198776224380079833091,
  319019586766684685897882996897223802965,
  320343637598493550924128413364430241919,
  233947696962235436325857303001873514753,
  248626544160260917886361049221866652419,
  319019586766684685916262185878437582165,
  340282361850335721211904661523412254591,
  18014398509481984,
  664613997892457936451903530140237824,
  18014398513676288,
  664613998047200441380590463016304640,
  4611686018427453440,
  170141183460471649583344547372759842816,
  4629700418014871552,
  170805797498132931286450978253539704832,
  36028814198833152,
  706152372760736557519554031873294337,
  54043212712509444,
  706152372925150469005158015335596045,
  9532994528416432129,
  181481159799511713134182621069399228419,
  14180709345008091141,
  181481159841766088385964826005592801295,
  18014402804449280,
  674998591609527591727260400579837953,
  18014402808643585,
  674998591766687948277162193295835137,
  4702039490246541313,
  173474638043651008925545151107856138241,
  4702039491341254657,
  173474638084038802707230682577518002177,
  54043251363020800,
  716536966477806212795473878036185091,
  54043251367215109,
  716536966644637975902292704158482447,
  14829509203835551745,
  184150000384798614540075999420974563331,
  14829509204997636101,
  184150000427671959806889208476190310415,
  85070591730234615865843651926661529600,
  191907293159099038304540664053480030209,
  85070591730234615865861666325175205904,
  277642498887496911785595816023283531793,
  106338239662793269838073693537291993089,
  319596580756021450449192641969491345665,
  106338239662793269838091708005868441617,
  320261196096131129020715923179421372689,
  170142481534683865438612451653303926784,
  298985770180134002842119694943787220995,
  255213073264918481304492132308269138005,
  320254721257796210758371639383995908351,
  276481045716030793713609575191476764929,
  340282146112981622811741854775413768451,
  276481045716030793713612953717245826389,
  340282161403084702384420844106256711167,
  85070916248788274292588449485486555136,
  320193696240700845482099797629295722497,
  85070916248788274292588449485490749457,
  320193696240974063012480609002137387025,
  106338564181346928264890831333362827521,
  324264477261132631603844561841611145473,
  106338564181346928264890831334710251793,
  324264477335699252010686520432511750417,
  255215993931901407145033180746809868288,
  320260558313155976301934761126693896195,
  255215993931901407145033180746814062677,
  320260563384043687618991163225178308863,
  276483641864460061127427227760088645889,
  340282359236738795627543164851232899843,
  276483641864460061127427227761503458645,
  340282364385637073374386726704171155455,
  170141183460469231731691807315511476224,
  213507246822954529936817741915507195904,
  170141183460469231731709821714026201088,
  213507246823147958067974096981974908928,
  212676479325586539670378240767533580288,
  213507246823573499962243053974517252096,
  212676479325586539670396255167390482432,
  213507246873284529664796605639782629376,
  170141183460469231731750354149321998336,
  213559169791539878213170319445478014979,
  170141183460469231731754857766134480901,
  213559169791742977750865577164024512527,
  212676479325586539681758555615346622465,
  226851449750008006980225766682632847363,
  212676479325586539682911477121368260613,
  226851449802204588167906995933991075855,
  212676479325586539664631647647286951936,
  213517631416671599592093098785946796033,
  212676479325586539664631647647292194817,
  213517631416865027723231439453905027073,
  212676479325586539670468594239352668161,
  216176087408860401363380068161045987329,
  212676479325586539670468594240700088321,
  216176087458571431065933619826311364609,
  212676479325586539664676683703690199040,
  213559169791539878213170319462657884163,
  212676479325586539664676683703695441925,
  213559169791742977750865577164024512527,
  212676479325586539683055592308029325313,
  226851449750008006980225766682632847363,
  212676479325586539683055592309444116485,
  226851449802204588167906995933991075855,
  319015043506933467923644981291650121728,
  320261196020636053578627289868599885825,
  319015043506933467923662995690164846608,
  320261196020926196070500720448396918801,
  319015043506933467929409606406887244033,
  320261196021564513336240447458165981441,
  319015043506933467929427620806744150289,
  320261196096131133743082406049066586385,
  297751289797018715077968517620691894272,
  320343637439737408971921376874279927811,
  319018937729577369044429430585182650453,
  320343642510644463692387423398265291007,
  319019586766684685916262183677999513857,
  340282321207220788780661119950136738563,
  319019586766684685916262183679414326613,
  340282326356119218233527943990427484159,
  319015043506933467923662995694454571008,
  320276772990439820575795514828912656385,
  319015043506933467923662995694459813905,
  320276772990729963067650931010200207377,
  319015043506933467929499960978217959681,
  324264477261132631603844561841611145473,
  319015043506933467929499960979565383953,
  324264477335699252010686520432511750417,
  319019586766684685897882996897218560000,
  320343637598193734000450052061367828483,
  319019586766684685897882996897223802965,
  320343642669100788720916098585353191679,
  319019586766684685916262185877022769409,
  340282361772039996084001967844639310595,
  319019586766684685916262185878437582165,
  340282366920938425536868791884930056191]

def choices (s : Nat) : List Nat := choicesData.getD s []

def bits (s : Nat) : Nat := bitsData.getD s 0

def listBits : List Nat → Nat
  | [] => 0
  | x :: xs => (2^x) ||| listBits xs

def checkTable (s : Nat) : Bool := listBits (choices s) == bits s

def checkClosed (a b : Nat) : Bool :=
  if a < b ∧ a &&& b = 0 then
    (choices a).all fun x => (choices b).all fun y =>
      (bits (a ||| b)).testBit (x &&& y) && (bits (a ||| b)).testBit (x ||| y)
  else true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma all_tables : ∀ s : Fin 256, checkTable s = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma closed_0 : ∀ a : Fin 16, ∀ b : Fin 256, checkClosed (0 + a.val) b.val = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma closed_16 : ∀ a : Fin 16, ∀ b : Fin 256, checkClosed (16 + a.val) b.val = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma closed_32 : ∀ a : Fin 16, ∀ b : Fin 256, checkClosed (32 + a.val) b.val = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma closed_48 : ∀ a : Fin 16, ∀ b : Fin 256, checkClosed (48 + a.val) b.val = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma closed_64 : ∀ a : Fin 16, ∀ b : Fin 256, checkClosed (64 + a.val) b.val = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma closed_80 : ∀ a : Fin 16, ∀ b : Fin 256, checkClosed (80 + a.val) b.val = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma closed_96 : ∀ a : Fin 16, ∀ b : Fin 256, checkClosed (96 + a.val) b.val = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma closed_112 : ∀ a : Fin 16, ∀ b : Fin 256, checkClosed (112 + a.val) b.val = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma closed_128 : ∀ a : Fin 16, ∀ b : Fin 256, checkClosed (128 + a.val) b.val = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma closed_144 : ∀ a : Fin 16, ∀ b : Fin 256, checkClosed (144 + a.val) b.val = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma closed_160 : ∀ a : Fin 16, ∀ b : Fin 256, checkClosed (160 + a.val) b.val = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma closed_176 : ∀ a : Fin 16, ∀ b : Fin 256, checkClosed (176 + a.val) b.val = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma closed_192 : ∀ a : Fin 16, ∀ b : Fin 256, checkClosed (192 + a.val) b.val = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma closed_208 : ∀ a : Fin 16, ∀ b : Fin 256, checkClosed (208 + a.val) b.val = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma closed_224 : ∀ a : Fin 16, ∀ b : Fin 256, checkClosed (224 + a.val) b.val = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma closed_240 : ∀ a : Fin 16, ∀ b : Fin 256, checkClosed (240 + a.val) b.val = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma target_absent : ∀ s : Fin 256, (bits s).testBit 15 = false := by decide +kernel

lemma all_closed (a b : Fin 256) : checkClosed a.val b.val = true := by
  by_cases h16 : a.val < 16
  · have h := closed_0 ⟨a.val - 0, by omega⟩ b
    have heq : 0 + (a.val - 0) = a.val := by omega
    simpa only [heq] using h
  by_cases h32 : a.val < 32
  · have h := closed_16 ⟨a.val - 16, by omega⟩ b
    have heq : 16 + (a.val - 16) = a.val := by omega
    simpa only [heq] using h
  by_cases h48 : a.val < 48
  · have h := closed_32 ⟨a.val - 32, by omega⟩ b
    have heq : 32 + (a.val - 32) = a.val := by omega
    simpa only [heq] using h
  by_cases h64 : a.val < 64
  · have h := closed_48 ⟨a.val - 48, by omega⟩ b
    have heq : 48 + (a.val - 48) = a.val := by omega
    simpa only [heq] using h
  by_cases h80 : a.val < 80
  · have h := closed_64 ⟨a.val - 64, by omega⟩ b
    have heq : 64 + (a.val - 64) = a.val := by omega
    simpa only [heq] using h
  by_cases h96 : a.val < 96
  · have h := closed_80 ⟨a.val - 80, by omega⟩ b
    have heq : 80 + (a.val - 80) = a.val := by omega
    simpa only [heq] using h
  by_cases h112 : a.val < 112
  · have h := closed_96 ⟨a.val - 96, by omega⟩ b
    have heq : 96 + (a.val - 96) = a.val := by omega
    simpa only [heq] using h
  by_cases h128 : a.val < 128
  · have h := closed_112 ⟨a.val - 112, by omega⟩ b
    have heq : 112 + (a.val - 112) = a.val := by omega
    simpa only [heq] using h
  by_cases h144 : a.val < 144
  · have h := closed_128 ⟨a.val - 128, by omega⟩ b
    have heq : 128 + (a.val - 128) = a.val := by omega
    simpa only [heq] using h
  by_cases h160 : a.val < 160
  · have h := closed_144 ⟨a.val - 144, by omega⟩ b
    have heq : 144 + (a.val - 144) = a.val := by omega
    simpa only [heq] using h
  by_cases h176 : a.val < 176
  · have h := closed_160 ⟨a.val - 160, by omega⟩ b
    have heq : 160 + (a.val - 160) = a.val := by omega
    simpa only [heq] using h
  by_cases h192 : a.val < 192
  · have h := closed_176 ⟨a.val - 176, by omega⟩ b
    have heq : 176 + (a.val - 176) = a.val := by omega
    simpa only [heq] using h
  by_cases h208 : a.val < 208
  · have h := closed_192 ⟨a.val - 192, by omega⟩ b
    have heq : 192 + (a.val - 192) = a.val := by omega
    simpa only [heq] using h
  by_cases h224 : a.val < 224
  · have h := closed_208 ⟨a.val - 208, by omega⟩ b
    have heq : 208 + (a.val - 208) = a.val := by omega
    simpa only [heq] using h
  by_cases h240 : a.val < 240
  · have h := closed_224 ⟨a.val - 224, by omega⟩ b
    have heq : 224 + (a.val - 224) = a.val := by omega
    simpa only [heq] using h
  have h := closed_240 ⟨a.val - 240, by omega⟩ b
  have heq : 240 + (a.val - 240) = a.val := by omega
  simpa only [heq] using h

def leafSigs : List Nat := [81, 22, 24, 35, 32, 108, 125, 54]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma input_allowed : ∀ i : Fin 8, (bits (2^i.val)).testBit (leafSigs.getD i.val 0) = true := by decide +kernel

end ReadOnce

namespace ReadOnceEncoding
open ReadOnceCore C6 C6.DagTools

lemma encoded_disjoint_closed {n : Nat} (choices : Nat → List Nat) (bits : Nat → Nat)
    (hzero : bits 0 = 0)
    (htable : ∀ s : Fin 256, checkTable choices bits s = true)
    (hclosed : ∀ a b : Fin 256, checkClosed choices bits a b = true)
    {S T : Finset (Fin 8)} {f g : Fin n → Bool} (hd : Disjoint S T)
    (hf : Allowed bits (resourceMask S) (truthBits f))
    (hg : Allowed bits (resourceMask T) (truthBits g)) :
    Allowed bits (resourceMask (S ∪ T)) (truthBits (fun i => f i && g i)) ∧
    Allowed bits (resourceMask (S ∪ T)) (truthBits (fun i => f i || g i)) := by
  rw [resourceMask_union, truthBits_and, truthBits_or]
  exact disjoint_closed choices bits hzero htable hclosed
    (resourceMask_bound S) (resourceMask_bound T) (resourceMask_disjoint hd) hf hg

lemma encoded_read_once_allowed {n : Nat} {D : Dag}
    (h : StrictLive 8 D)
    (hone : ∀ w, w + 1 < 8 + D.length → fanout D w = 1)
    (x : Fin n → Fin 8 → Bool) (choices : Nat → List Nat) (bits : Nat → Nat)
    (hzero : bits 0 = 0)
    (htable : ∀ s : Fin 256, checkTable choices bits s = true)
    (hclosed : ∀ a b : Fin 256, checkClosed choices bits a b = true)
    (hinput : ∀ v : Fin 8, Allowed bits (2 ^ v.val) (truthBits (fun i => x i v))) :
    Allowed bits 255 (truthBits (fun i => val D (x i) (outW 8 D))) := by
  have hP := resource_induction_nonempty h hone x
    (fun S f => Allowed bits (resourceMask S) (truthBits f))
    (fun v => by simpa only [resourceMask_singleton] using hinput v)
    (fun _ _ _ _ _ _ hd hf hg =>
      (encoded_disjoint_closed choices bits hzero htable hclosed hd hf hg).1)
    (fun _ _ _ _ _ _ hd hf hg =>
      (encoded_disjoint_closed choices bits hzero htable hclosed hd hf hg).2)
  simpa only [resourceMask_univ] using hP

end ReadOnceEncoding

namespace ReadOnce
open C6 C6.DagTools ReadOnceCore ReadOnceEncoding

def rowNumbers : List Nat := [9, 10, 34, 36, 7, 56, 33]

def rowInput (r : Fin 7) (v : Fin 6) : Bool :=
  (rowNumbers.getD r.val 0).testBit v.val

def extendedRowInput (r : Fin 7) : Fin 8 → Bool := extendTwo (rowInput r)

lemma extendedRowInput_signature : ∀ v : Fin 8,
    truthBits (fun r => extendedRowInput r v) = leafSigs.getD v.val 0 := by
  decide +kernel

lemma row_target_signature : truthBits (fun r : Fin 7 =>
    edgeBool (rowInput r)) = 15 := by
  decide +kernel

lemma listBits_core (xs : List Nat) : ReadOnceCore.listBits xs = listBits xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [ReadOnceCore.listBits, listBits, ih]

lemma tables_core (s : Fin 256) : ReadOnceCore.checkTable choices bits s = true := by
  simpa only [ReadOnceCore.checkTable, listBits_core, checkTable] using all_tables s

lemma closed_core (a b : Fin 256) : ReadOnceCore.checkClosed choices bits a b = true :=
  all_closed a b

lemma bits_zero : bits 0 = 0 := by rfl

lemma read_once_output_allowed {D : Dag}
    (h : StrictLive 8 D)
    (hone : ∀ w, w + 1 < 8 + D.length → fanout D w = 1) :
    ReadOnceCore.Allowed bits 255
      (truthBits (fun r => val D (extendedRowInput r) (outW 8 D))) := by
  apply encoded_read_once_allowed h hone extendedRowInput choices bits bits_zero tables_core closed_core
  intro v
  rw [extendedRowInput_signature]
  exact input_allowed v

lemma no_read_once_target {D : Dag}
    (h : StrictLive 8 D)
    (hone : ∀ w, w + 1 < 8 + D.length → fanout D w = 1)
    (hc : ∀ r : Fin 7,
      val D (extendedRowInput r) (outW 8 D) = true ↔ sem_Edge adj (rowInput r)) : False := by
  have hsig : (fun r => val D (extendedRowInput r) (outW 8 D)) =
      (fun r : Fin 7 => edgeBool (rowInput r)) := by
    funext r
    exact Bool.eq_iff_iff.mpr ((hc r).trans (edgeBool_spec (rowInput r)).symm)
  have ha := read_once_output_allowed h hone
  rw [hsig, row_target_signature] at ha
  have hn := target_absent (⟨255, by decide⟩ : Fin 256)
  simp only [ReadOnceCore.Allowed] at ha
  simp only [ha, Bool.true_eq_false] at hn

lemma no_prefixTwo {R : Dag} (h : StrictLive 6 (prefixTwo ++ R))
    (hc : sem_Comp 6 adj (prefixTwo ++ R)) (hl : R.length ≤ 7) : False := by
  obtain ⟨_, hR, hone⟩ := prefixTwo_residual_tree h hc hl
  apply no_read_once_target hR hone
  intro r
  exact prefixTwo_residual_computes hc (rowInput r)

end ReadOnce

namespace C6
open DagTools

def extendThree (x : V → Bool) : Fin 9 → Bool :=
  ![x 0, x 1, x 2, x 3, x 4, x 5, x 0 || x 5, x 1 || x 4, x 2 || x 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
lemma prefixThree_inputs : ∀ x : V → Bool,
    wl prefixThree (List.ofFn x) = List.ofFn (extendThree x) := by
  decide +kernel

lemma prefixThree_strict {R : Dag} (h : Strict 9 R) : Strict 6 (prefixThree ++ R) := by
  intro j hj
  by_cases hj3 : j < 3
  · interval_cases j <;> simp [opA, opB, prefixThree]
  · have hj' : j - 3 < R.length := by
      simp only [prefixThree, List.length_append, List.length_cons, List.length_nil] at hj
      omega
    have hs := h (j - 3) hj'
    have hg : (prefixThree ++ R).getD j (false, 0, 0) = R.getD (j - 3) (false, 0, 0) := by
      simpa [prefixThree] using List.getD_append_right prefixThree R (false, 0, 0) j (by simp [prefixThree]; omega)
    simp only [opA, opB, hg] at hs ⊢
    exact ⟨by omega, by omega, hs.2.2⟩

lemma prefixThree_computes {R : Dag}
    (hc : ∀ x : V → Bool, val R (extendThree x) (outW 9 R) = true ↔ sem_Edge adj x) :
    sem_Comp 6 adj (prefixThree ++ R) := by
  have ho : outW 6 (prefixThree ++ R) = outW 9 R := by
    simp only [outW, List.length_append, prefixThree, List.length_cons, List.length_nil]
    omega
  intro x
  simpa only [val, wl_append, prefixThree_inputs, ho] using hc x

lemma no_seven_with_three_free_pairs_of_canonical
    (hcanonical : ∀ R : Dag, R.length ≤ 7 → StrictLive 6 (prefixTwo ++ R) →
      sem_Comp 6 adj (prefixTwo ++ R) → False)
    {R : Dag} (hl : R.length ≤ 7) (h : Strict 9 R)
    (hc : ∀ x : V → Bool, val R (extendThree x) (outW 9 R) = true ↔ sem_Edge adj x) :
    False :=
  no_free_prefix_seven_of_canonical hcanonical hl (prefixThree_strict h)
    (prefixThree_computes hc)

end C6

namespace C6
open DagTools

lemma no_free_prefix_seven {R : Dag} (hl : R.length ≤ 7)
    (h : Strict 6 (prefixThree ++ R)) (hc : sem_Comp 6 adj (prefixThree ++ R)) : False :=
  no_free_prefix_seven_of_canonical
    (fun _ hl' h' hc' => ReadOnce.no_prefixTwo h' hc' hl') hl h hc

lemma no_seven_with_three_free_pairs {R : Dag} (hl : R.length ≤ 7)
    (h : Strict 9 R)
    (hc : ∀ x : V → Bool, val R (extendThree x) (outW 9 R) = true ↔ sem_Edge adj x) :
    False :=
  no_seven_with_three_free_pairs_of_canonical
    (fun _ hl' h' hc' => ReadOnce.no_prefixTwo h' hc' hl') hl h hc

end C6

namespace C6
open DagTools CircuitLowerBounds MetaComplexity

lemma edgeBool_not_constant : ∀ b : Bool, ∃ x : V → Bool, edgeBool x ≠ b := by
  decide +kernel

lemma extendThree_not_target : ∀ i : Fin 9, ∃ x : V → Bool,
    extendThree x i ≠ edgeBool x := by
  decide +kernel

lemma no_seven_circuit_with_three_free_pairs (C : Circuit) (hm : Monotone2 C)
    (hl : C.size ≤ 7)
    (hc : ∀ x : V → Bool,
      C.eval (List.ofFn (extendThree x)) = true ↔ sem_Edge adj x) : False := by
  have heq (x : V → Bool) : C.eval (List.ofFn (extendThree x)) = edgeBool x :=
    Bool.eq_iff_iff.mpr ((hc x).trans (edgeBool_spec x).symm)
  rcases exists_strict_of_monotone2 (n := 9) C hm with
    ⟨b, hb⟩ | ⟨i, hi⟩ | ⟨D, hS, _, hlen, hD⟩
  · obtain ⟨x, hx⟩ := edgeBool_not_constant b
    exact hx ((heq x).symm.trans (hb (extendThree x)))
  · obtain ⟨x, hx⟩ := extendThree_not_target i
    exact hx ((hi (extendThree x)).symm.trans (heq x))
  · apply no_seven_with_three_free_pairs (hlen.trans hl) hS
    intro x
    rw [hD]
    exact hc x

end C6

namespace C6.CenterNoise
open DagTools

lemma dominated_true_neighbor_completion {n : ℕ} {G : Fin n → Fin n → Prop}
    {D : Dag} (hS : Strict n D) (hc : sem_Comp n G D)
    (v : Fin n) (b : ℕ) (hdom : sem_Dom n D b v.val)
    (x : Fin n → Bool) (hb : val D x b = true)
    (z : Fin n) (hvz : G v z) : sem_Edge G (sem_ins z x) := by
  have hzb : val D (sem_ins z x) b = true :=
    val_mono hS x (sem_ins z x) (sem_ins_ge z x) b hb
  have hvb : val D (sem_ins v (sem_ins z x)) b = true :=
    val_mono hS (sem_ins z x) (sem_ins v (sem_ins z x))
      (sem_ins_ge v (sem_ins z x)) b hzb
  have he := sem_dom_eq hS (sem_ins z x) (sem_ins v (sem_ins z x)) v
    (sem_ins_agree v (sem_ins z x)) b hdom (by rw [hzb, hvb])
  have htarget : sem_Edge G (sem_ins v (sem_ins z x)) :=
    ⟨v, z, hvz, sem_ins_self v _, sem_ins_ge v _ z (sem_ins_self z _)⟩
  apply (hc _).mp
  rw [he]
  exact (hc _).mpr htarget

def pAdj (u v : Fin 10) : Prop :=
  (u.val, v.val) ∈ [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),
    (3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)] ∨
  (v.val, u.val) ∈ [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),
    (3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]

-- Canonical C6 coordinates are Petersen vertices [2,8,9,3,7,6].
def embed (x : V → Bool) : Fin 10 → Bool :=
  ![false, false, x 0, x 3, false, false, x 5, x 4, x 1, x 2]

def alternatingTriple (x : V → Bool) : Prop :=
  (x 0 = true ∧ x 1 = true ∧ x 2 = true) ∨
    (x 3 = true ∧ x 4 = true ∧ x 5 = true)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
set_option synthInstance.maxSize 8192 in
lemma center_completion_classification : ∀ x : V → Bool,
    sem_Edge pAdj (sem_ins 1 (embed x)) →
    sem_Edge pAdj (sem_ins 4 (embed x)) →
    sem_Edge pAdj (sem_ins 5 (embed x)) →
    sem_Edge adj x ∨ alternatingTriple x := by
  unfold sem_Edge pAdj sem_ins embed adj alternatingTriple
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
set_option synthInstance.maxSize 8192 in
lemma center_insertion_restriction : ∀ x : V → Bool,
    sem_Edge pAdj (sem_ins 0 (embed x)) ↔ sem_Edge adj x := by
  unfold sem_Edge pAdj sem_ins embed adj
  decide +kernel

lemma dominated_center_restriction {D : Dag} (hS : Strict 10 D)
    (hc : sem_Comp 10 pAdj D) (b : ℕ) (hdom : sem_Dom 10 D b 0)
    (x : V → Bool) (hb : val D (embed x) b = true) :
    sem_Edge adj x ∨ alternatingTriple x := by
  apply center_completion_classification x
  · exact dominated_true_neighbor_completion hS hc 0 b hdom (embed x) hb 1
      (by unfold pAdj; decide)
  · exact dominated_true_neighbor_completion hS hc 0 b hdom (embed x) hb 4
      (by unfold pAdj; decide)
  · exact dominated_true_neighbor_completion hS hc 0 b hdom (embed x) hb 5
      (by unfold pAdj; decide)

lemma dominated_neighbor_restriction {D : Dag} (hS : Strict 10 D)
    (hc : sem_Comp 10 pAdj D) (v : Fin 10) (hv : v = 1 ∨ v = 4 ∨ v = 5)
    (b : ℕ) (hdom : sem_Dom 10 D b v.val)
    (x : V → Bool) (hb : val D (embed x) b = true) : sem_Edge adj x := by
  apply (center_insertion_restriction x).mp
  apply dominated_true_neighbor_completion hS hc v b hdom (embed x) hb 0
  rcases hv with rfl | rfl | rfl <;> unfold pAdj <;> decide

end C6.CenterNoise



namespace C6
open DagTools

lemma bf_budget {R : Dag} (h : StrictLive 6 (prefixTwo ++ R))
    (hc : sem_Comp 6 adj (prefixTwo ++ R)) (hb4 : Bplus 6 (prefixTwo ++ R) = 4) :
    ∃ b : V → ℕ, PureBranch 6 (prefixTwo ++ R) b ∧
      eligSet 6 (prefixTwo ++ R) = fourEndpoints ∧
      residualUnits 6 (prefixTwo ++ R) b = ∅ := by
  classical
  obtain ⟨b, hb⟩ := sem_exists_pureBranch graph_ok h.1 hc
  have hsub : fourEndpoints ⊆ eligSet 6 (prefixTwo ++ R) := by
    intro v hv
    exact raw_branch_eligible (prefixTwo_branches h hc v hv)
  have hfour : fourEndpoints.card = 4 := by decide
  have hbound := elig_le_Bplus h.1 b hb
  have heq : eligSet 6 (prefixTwo ++ R) = fourEndpoints :=
    (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
  have hr := card_residual h.1 b hb
  rw [heq, hfour, hb4] at hr
  exact ⟨b, hb, heq, Finset.card_eq_zero.mp (by omega)⟩

lemma bf_inelig {R : Dag} (h : StrictLive 6 (prefixTwo ++ R))
    (hc : sem_Comp 6 adj (prefixTwo ++ R)) (hb4 : Bplus 6 (prefixTwo ++ R) = 4) :
    ineligSet 6 (prefixTwo ++ R) = {2, 3} := by
  classical
  obtain ⟨_, _, heq, _⟩ := bf_budget h hc hb4
  ext v
  rw [sem_mem_inelig, heq]
  fin_cases v <;> decide

lemma bf_flow {R : Dag} (h : StrictLive 6 (prefixTwo ++ R))
    (hc : sem_Comp 6 adj (prefixTwo ++ R)) (hb4 : Bplus 6 (prefixTwo ++ R) = 4)
    (v : V) :
    (sem_W 6 (prefixTwo ++ R) v).card +
      (merges 6 (prefixTwo ++ R) (carrierT 6 (prefixTwo ++ R) {v})).card =
      1 + if v ∈ fourEndpoints then 1 else 0 := by
  classical
  obtain ⟨b, hb, heq, hr⟩ := bf_budget h hc hb4
  have hf := sem_code_count graph_ok h hc b hb v
  rw [hr, heq] at hf
  by_cases hv : v ∈ fourEndpoints <;> simpa [hv] using hf

lemma consumer_two_exits {D : Dag} (h : StrictLive 6 D) (hc : sem_Comp 6 adj D)
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

lemma bf_endpoint_exits {R : Dag} (h : StrictLive 6 (prefixTwo ++ R))
    (hc : sem_Comp 6 adj (prefixTwo ++ R)) (hb4 : Bplus 6 (prefixTwo ++ R) = 4)
    {v : V} (hv : v ∈ fourEndpoints) : 2 ≤ (sem_W 6 (prefixTwo ++ R) v).card := by
  have hi := bf_inelig h hc hb4
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

lemma bf_merges_empty {R : Dag} (h : StrictLive 6 (prefixTwo ++ R))
    (hc : sem_Comp 6 adj (prefixTwo ++ R)) (hb4 : Bplus 6 (prefixTwo ++ R) = 4)
    (v : V) : merges 6 (prefixTwo ++ R) (carrierT 6 (prefixTwo ++ R) {v}) = ∅ := by
  classical
  by_cases hv : v ∈ fourEndpoints
  · have hf := bf_flow h hc hb4 v
    have he := bf_endpoint_exits h hc hb4 hv
    simp only [hv, ↓reduceIte] at hf
    exact Finset.card_eq_zero.mp (by omega)
  · obtain ⟨_, _, heq, _⟩ := bf_budget h hc hb4
    have hi : v ∈ ineligSet 6 (prefixTwo ++ R) := sem_mem_inelig.mpr (by rwa [heq])
    obtain ⟨_, _, _, _, _, _, _, hm⟩ := sem_inelig_consumer graph_ok h hc hi
    exact hm

lemma bf_and_empty {R : Dag} (h : StrictLive 6 (prefixTwo ++ R))
    (hc : sem_Comp 6 adj (prefixTwo ++ R)) (hb4 : Bplus 6 (prefixTwo ++ R) = 4)
    {j : ℕ} (hj : j < (prefixTwo ++ R).length) (ht : tag (prefixTwo ++ R) j = true) :
    supp 6 (prefixTwo ++ R) (6 + j) = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro v hv
  have hg := sem_zm_gate h.1 (bf_merges_empty h hc hb4 v) hj hv
  rw [ht] at hg
  exact Bool.noConfusion hg.1

lemma bf_exits_le_two {R : Dag} (h : StrictLive 6 (prefixTwo ++ R))
    (hc : sem_Comp 6 adj (prefixTwo ++ R)) (hb4 : Bplus 6 (prefixTwo ++ R) = 4)
    (v : V) : (sem_W 6 (prefixTwo ++ R) v).card ≤ 2 := by
  have hf := bf_flow h hc hb4 v
  split_ifs at hf <;> omega

lemma consumer_other_exit {D : Dag} {z v : V} {e : ℕ × Bool}
    (he : Consumer D z e) (hv : v ∈ supp 6 D (src D (sem_bar e))) :
    sem_bar e ∈ sem_W 6 D v := by
  apply sem_mem_W.mpr
  refine ⟨he.1, hv, ?_⟩
  change v ∉ supp 6 D (6 + e.1)
  rw [he.2.2.2.1]
  exact Finset.notMem_empty _

lemma joint_not_consumer {D : Dag} {v u z : V} {f e : ℕ × Bool}
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

lemma consumer_extra_impossible {D : Dag} (h : StrictLive 6 D) (hc : sem_Comp 6 adj D)
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

lemma consumer_own_not_other {D : Dag} {z : V} {e : ℕ × Bool}
    (he : Consumer D z e) : z ∉ supp 6 D (src D (sem_bar e)) := by
  intro hz
  have hm := consumer_other_exit he hz
  rw [he.2.2.2.2.2, Finset.mem_singleton] at hm
  exact (sem_bar_ne e) hm

lemma consumer_other_inelig_not {D : Dag} {z w : V} {ec ed : ℕ × Bool}
    (hec : Consumer D z ec) (hed : Consumer D w ed) (hne : z ≠ w) :
    w ∉ supp 6 D (src D (sem_bar ec)) := by
  intro hw
  have hm := consumer_other_exit hec hw
  rw [hed.2.2.2.2.2, Finset.mem_singleton] at hm
  have hg : ec.1 = ed.1 := by
    simpa only [sem_bar] using congrArg (fun q : ℕ × Bool => q.1) hm
  exact hne (consumers_injective hec hed hg)

lemma bf_C_opposite {R : Dag} (h : StrictLive 6 (prefixTwo ++ R))
    (hc : sem_Comp 6 adj (prefixTwo ++ R)) (hb4 : Bplus 6 (prefixTwo ++ R) = 4)
    {ec ed : ℕ × Bool} (hec : Consumer (prefixTwo ++ R) 2 ec)
    (hed : Consumer (prefixTwo ++ R) 3 ed) :
    supp 6 (prefixTwo ++ R) (src (prefixTwo ++ R) (sem_bar ec)) = {4, 5} := by
  classical
  apply Finset.Subset.antisymm
  · intro v hv
    fin_cases v
    · exact (consumer_extra_impossible h hc hec hed (u := 4)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by unfold adj; decide) (by unfold adj; decide) hv
        (bf_exits_le_two h hc hb4 0)).elim
    · exact (consumer_extra_impossible h hc hec hed (u := 5)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by unfold adj; decide) (by unfold adj; decide) hv
        (bf_exits_le_two h hc hb4 1)).elim
    · exact (consumer_own_not_other hec hv).elim
    · exact (consumer_other_inelig_not hec hed (by decide) hv).elim
    · decide
    · decide
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact hec.2.2.2.2.1 4 (by unfold adj; decide)
    · exact hec.2.2.2.2.1 5 (by unfold adj; decide)

lemma bf_D_opposite {R : Dag} (h : StrictLive 6 (prefixTwo ++ R))
    (hc : sem_Comp 6 adj (prefixTwo ++ R)) (hb4 : Bplus 6 (prefixTwo ++ R) = 4)
    {ec ed : ℕ × Bool} (hec : Consumer (prefixTwo ++ R) 2 ec)
    (hed : Consumer (prefixTwo ++ R) 3 ed) :
    supp 6 (prefixTwo ++ R) (src (prefixTwo ++ R) (sem_bar ed)) = {0, 1} := by
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
        (bf_exits_le_two h hc hb4 4)).elim
    · exact (consumer_extra_impossible h hc hed hec (u := 1)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by unfold adj; decide) (by unfold adj; decide) hv
        (bf_exits_le_two h hc hb4 5)).elim
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact hed.2.2.2.2.1 0 (by unfold adj; decide)
    · exact hed.2.2.2.2.1 1 (by unfold adj; decide)

end C6


namespace C6
open DagTools

lemma common_exit_of_joint_support {D : Dag} (h : StrictLive 6 D)
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

lemma bf_common_AF {R : Dag} (h : StrictLive 6 (prefixTwo ++ R))
    (hc : sem_Comp 6 adj (prefixTwo ++ R)) (hb4 : Bplus 6 (prefixTwo ++ R) = 4) :
    ∃ k, k ∈ sem_W 6 (prefixTwo ++ R) 0 ∧ k ∈ sem_W 6 (prefixTwo ++ R) 5 := by
  apply common_exit_of_joint_support h hc (fun j hj ht => bf_and_empty h hc hb4 hj ht)
    (u := 0) (v := 5) (w := 6)
  · have hj : 0 < (prefixTwo ++ R).length := by simp [prefixTwo]
    have hs := sem_supp_or h.1 hj (show tag (prefixTwo ++ R) 0 = false by simp [tag, prefixTwo])
    simp only [Nat.add_zero] at hs
    rw [hs]
    apply Finset.mem_union_left
    change (0 : V) ∈ supp 6 (prefixTwo ++ R) (0 : V).val
    rw [supp_input]
    exact Finset.mem_singleton_self _
  · have hj : 0 < (prefixTwo ++ R).length := by simp [prefixTwo]
    have hs := sem_supp_or h.1 hj (show tag (prefixTwo ++ R) 0 = false by simp [tag, prefixTwo])
    simp only [Nat.add_zero] at hs
    rw [hs]
    apply Finset.mem_union_right
    change (5 : V) ∈ supp 6 (prefixTwo ++ R) (5 : V).val
    rw [supp_input]
    exact Finset.mem_singleton_self _

lemma two_exits_eq {D : Dag} {v : V} {e f : ℕ × Bool}
    (hle : (sem_W 6 D v).card ≤ 2) (he : e ∈ sem_W 6 D v)
    (hf : f ∈ sem_W 6 D v) (hne : e ≠ f) : sem_W 6 D v = {e, f} := by
  classical
  have hs : {e, f} ⊆ sem_W 6 D v := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl <;> assumption
  exact (Finset.eq_of_subset_of_card_le hs (by simpa [hne] using hle)).symm

lemma slot_not_consumer {D : Dag} {v z : V} {k e : ℕ × Bool}
    (hk : k ∈ sem_W 6 D v) (he : Consumer D z e)
    (hvz : v ≠ z) (hopp : v ∉ supp 6 D (src D (sem_bar e))) : k.1 ≠ e.1 := by
  intro hg
  have hv := (sem_mem_W.mp hk).2.1
  rcases sem_same_gate hg.symm with hf | hf
  · rw [hf, he.2.2.1, Finset.mem_singleton] at hv
    exact hvz hv
  · rw [hf] at hv
    exact hopp hv

lemma bf_AF_distinct {R : Dag} (h : StrictLive 6 (prefixTwo ++ R))
    (hc : sem_Comp 6 adj (prefixTwo ++ R)) (hb4 : Bplus 6 (prefixTwo ++ R) = 4)
    {ec ed k : ℕ × Bool} (hec : Consumer (prefixTwo ++ R) 2 ec)
    (hed : Consumer (prefixTwo ++ R) 3 ed)
    (hka : k ∈ sem_W 6 (prefixTwo ++ R) 0) (hkf : k ∈ sem_W 6 (prefixTwo ++ R) 5) :
    k.1 ≠ ec.1 ∧ k.1 ≠ ed.1 := by
  constructor
  · apply slot_not_consumer hka hec (by decide)
    rw [bf_C_opposite h hc hb4 hec hed]
    decide
  · apply slot_not_consumer hkf hed (by decide)
    rw [bf_D_opposite h hc hb4 hec hed]
    decide

lemma bf_cross_partners {R : Dag} (h : StrictLive 6 (prefixTwo ++ R))
    (hc : sem_Comp 6 adj (prefixTwo ++ R)) (hb4 : Bplus 6 (prefixTwo ++ R) = 4)
    {ec ed k : ℕ × Bool} (hec : Consumer (prefixTwo ++ R) 2 ec)
    (hed : Consumer (prefixTwo ++ R) 3 ed)
    (hka : k ∈ sem_W 6 (prefixTwo ++ R) 0) (hkf : k ∈ sem_W 6 (prefixTwo ++ R) 5) :
    sem_bar k ∈ sem_W 6 (prefixTwo ++ R) 1 ∧
      sem_bar k ∈ sem_W 6 (prefixTwo ++ R) 4 := by
  have hd := bf_AF_distinct h hc hb4 hec hed hka hkf
  have heA := consumer_other_exit hed (hed.2.2.2.2.1 0 (by unfold adj; decide))
  have heF := consumer_other_exit hec (hec.2.2.2.2.1 5 (by unfold adj; decide))
  have hWA := two_exits_eq (bf_exits_le_two h hc hb4 0) heA hka
    (fun he => hd.2 (congrArg Prod.fst he).symm)
  have hWF := two_exits_eq (bf_exits_le_two h hc hb4 5) heF hkf
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

lemma exit_not_opposite {D : Dag} (hS : Strict 6 D) {v : V} {e : ℕ × Bool}
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

lemma consumer_not_other_gate {D : Dag} {z : V} {e k : ℕ × Bool}
    (he : Consumer D z e) (hj : k.1 < D.length)
    (hempty : supp 6 D (6 + k.1) = ∅) (hne : k.1 ≠ e.1) :
    z ∉ supp 6 D (src D k) := by
  intro hz
  have hk : k ∈ sem_W 6 D z := sem_mem_W.mpr
    ⟨hj, hz, by rw [hempty]; exact Finset.notMem_empty _⟩
  rw [he.2.2.2.2.2, Finset.mem_singleton] at hk
  exact hne (congrArg Prod.fst hk)

lemma bf_cross_supports {R : Dag} (h : StrictLive 6 (prefixTwo ++ R))
    (hc : sem_Comp 6 adj (prefixTwo ++ R)) (hb4 : Bplus 6 (prefixTwo ++ R) = 4)
    {ec ed k : ℕ × Bool} (hec : Consumer (prefixTwo ++ R) 2 ec)
    (hed : Consumer (prefixTwo ++ R) 3 ed)
    (hka : k ∈ sem_W 6 (prefixTwo ++ R) 0) (hkf : k ∈ sem_W 6 (prefixTwo ++ R) 5) :
    supp 6 (prefixTwo ++ R) (src (prefixTwo ++ R) k) = {0, 5} ∧
      supp 6 (prefixTwo ++ R) (src (prefixTwo ++ R) (sem_bar k)) = {1, 4} := by
  classical
  obtain ⟨hkb, hke⟩ := bf_cross_partners h hc hb4 hec hed hka hkf
  obtain ⟨hkc, hkd⟩ := bf_AF_distinct h hc hb4 hec hed hka hkf
  have hj := (sem_mem_W.mp hka).1
  have hz := bf_and_empty h hc hb4 hj (sem_W_and h.1 hka)
  have hcnot := consumer_not_other_gate hec hj hz hkc
  have hdnot := consumer_not_other_gate hed hj hz hkd
  have hcnot' : (2 : V) ∉ supp 6 (prefixTwo ++ R) (src (prefixTwo ++ R) (sem_bar k)) :=
    consumer_not_other_gate hec hj hz hkc
  have hdnot' : (3 : V) ∉ supp 6 (prefixTwo ++ R) (src (prefixTwo ++ R) (sem_bar k)) :=
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

lemma bf_three_exit_gates {R : Dag} (h : StrictLive 6 (prefixTwo ++ R))
    (hc : sem_Comp 6 adj (prefixTwo ++ R)) (hb4 : Bplus 6 (prefixTwo ++ R) = 4)
    {ec ed k : ℕ × Bool} (hec : Consumer (prefixTwo ++ R) 2 ec)
    (hed : Consumer (prefixTwo ++ R) 3 ed)
    (hka : k ∈ sem_W 6 (prefixTwo ++ R) 0) (hkf : k ∈ sem_W 6 (prefixTwo ++ R) 5) :
    ∀ v : V, ∀ e ∈ sem_W 6 (prefixTwo ++ R) v,
      e.1 = ec.1 ∨ e.1 = ed.1 ∨ e.1 = k.1 := by
  obtain ⟨hkb, hke⟩ := bf_cross_partners h hc hb4 hec hed hka hkf
  obtain ⟨hkc, hkd⟩ := bf_AF_distinct h hc hb4 hec hed hka hkf
  have hWA := two_exits_eq (bf_exits_le_two h hc hb4 0)
    (consumer_other_exit hed (hed.2.2.2.2.1 0 (by unfold adj; decide))) hka
    (fun he => hkd (congrArg Prod.fst he).symm)
  have hWB := two_exits_eq (bf_exits_le_two h hc hb4 1)
    (consumer_other_exit hed (hed.2.2.2.2.1 1 (by unfold adj; decide))) hkb
    (fun he => hkd (congrArg Prod.fst he).symm)
  have hWE := two_exits_eq (bf_exits_le_two h hc hb4 4)
    (consumer_other_exit hec (hec.2.2.2.2.1 4 (by unfold adj; decide))) hke
    (fun he => hkc (congrArg Prod.fst he).symm)
  have hWF := two_exits_eq (bf_exits_le_two h hc hb4 5)
    (consumer_other_exit hec (hec.2.2.2.2.1 5 (by unfold adj; decide))) hkf
    (fun he => hkc (congrArg Prod.fst he).symm)
  intro v e he
  fin_cases v
  · change e ∈ sem_W 6 (prefixTwo ++ R) (0 : V) at he
    rw [hWA, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl <;> simp [sem_bar]
  · change e ∈ sem_W 6 (prefixTwo ++ R) (1 : V) at he
    rw [hWB, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl <;> simp [sem_bar]
  · change e ∈ sem_W 6 (prefixTwo ++ R) (2 : V) at he
    rw [hec.2.2.2.2.2, Finset.mem_singleton] at he
    subst e
    simp
  · change e ∈ sem_W 6 (prefixTwo ++ R) (3 : V) at he
    rw [hed.2.2.2.2.2, Finset.mem_singleton] at he
    subst e
    simp
  · change e ∈ sem_W 6 (prefixTwo ++ R) (4 : V) at he
    rw [hWE, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl <;> simp [sem_bar]
  · change e ∈ sem_W 6 (prefixTwo ++ R) (5 : V) at he
    rw [hWF, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl <;> simp [sem_bar]

lemma bf_other_and_inputs_empty {R : Dag} (h : StrictLive 6 (prefixTwo ++ R))
    (hc : sem_Comp 6 adj (prefixTwo ++ R)) (hb4 : Bplus 6 (prefixTwo ++ R) = 4)
    {ec ed k : ℕ × Bool} (hec : Consumer (prefixTwo ++ R) 2 ec)
    (hed : Consumer (prefixTwo ++ R) 3 ed)
    (hka : k ∈ sem_W 6 (prefixTwo ++ R) 0) (hkf : k ∈ sem_W 6 (prefixTwo ++ R) 5)
    {j : ℕ} (hj : j < (prefixTwo ++ R).length) (ht : tag (prefixTwo ++ R) j = true)
    (hjc : j ≠ ec.1) (hjd : j ≠ ed.1) (hjk : j ≠ k.1) :
    supp 6 (prefixTwo ++ R) (opA (prefixTwo ++ R) j) = ∅ ∧
      supp 6 (prefixTwo ++ R) (opB (prefixTwo ++ R) j) = ∅ := by
  have hs : ∀ s : Bool, supp 6 (prefixTwo ++ R) (src (prefixTwo ++ R) (j, s)) = ∅ := by
    intro s
    apply Finset.eq_empty_of_forall_notMem
    intro v hv
    have he : (j, s) ∈ sem_W 6 (prefixTwo ++ R) v := sem_mem_W.mpr
      ⟨hj, hv, by rw [bf_and_empty h hc hb4 hj ht]; exact Finset.notMem_empty _⟩
    rcases bf_three_exit_gates h hc hb4 hec hed hka hkf v (j, s) he with he | he | he
    · exact hjc he
    · exact hjd he
    · exact hjk he
  exact ⟨by simpa [src] using hs false, by simpa [src] using hs true⟩

lemma bf_three_birth_geometry {R : Dag} (h : StrictLive 6 (prefixTwo ++ R))
    (hc : sem_Comp 6 adj (prefixTwo ++ R)) (hb4 : Bplus 6 (prefixTwo ++ R) = 4) :
    ∃ ec ed k : ℕ × Bool,
      Consumer (prefixTwo ++ R) 2 ec ∧ Consumer (prefixTwo ++ R) 3 ed ∧
      k.1 < (prefixTwo ++ R).length ∧ tag (prefixTwo ++ R) k.1 = true ∧
      ec.1 ≠ ed.1 ∧ k.1 ≠ ec.1 ∧ k.1 ≠ ed.1 ∧
      supp 6 (prefixTwo ++ R) (src (prefixTwo ++ R) (sem_bar ec)) = {4, 5} ∧
      supp 6 (prefixTwo ++ R) (src (prefixTwo ++ R) (sem_bar ed)) = {0, 1} ∧
      supp 6 (prefixTwo ++ R) (src (prefixTwo ++ R) k) = {0, 5} ∧
      supp 6 (prefixTwo ++ R) (src (prefixTwo ++ R) (sem_bar k)) = {1, 4} ∧
      (∀ j, j < (prefixTwo ++ R).length → tag (prefixTwo ++ R) j = true →
        j ≠ ec.1 → j ≠ ed.1 → j ≠ k.1 →
        supp 6 (prefixTwo ++ R) (opA (prefixTwo ++ R) j) = ∅ ∧
          supp 6 (prefixTwo ++ R) (opB (prefixTwo ++ R) j) = ∅) := by
  have hi := bf_inelig h hc hb4
  obtain ⟨ec, hec⟩ := consumer_exists h hc (v := (2 : V)) (by rw [hi]; decide)
  obtain ⟨ed, hed⟩ := consumer_exists h hc (v := (3 : V)) (by rw [hi]; decide)
  obtain ⟨k, hka, hkf⟩ := bf_common_AF h hc hb4
  obtain ⟨hkc, hkd⟩ := bf_AF_distinct h hc hb4 hec hed hka hkf
  obtain ⟨hkA, hkB⟩ := bf_cross_supports h hc hb4 hec hed hka hkf
  have hcd : ec.1 ≠ ed.1 := by
    intro hg
    exact (by decide : (2 : V) ≠ 3) (consumers_injective hec hed hg)
  exact ⟨ec, ed, k, hec, hed, (sem_mem_W.mp hka).1, sem_W_and h.1 hka,
    hcd, hkc, hkd, bf_C_opposite h hc hb4 hec hed, bf_D_opposite h hc hb4 hec hed,
    hkA, hkB, fun _ hj ht hjc hjd hjk =>
      bf_other_and_inputs_empty h hc hb4 hec hed hka hkf hj ht hjc hjd hjk⟩

end C6


namespace C6.ThreeBirth

-- Birth roles: C = c*(e+f), D = d*(a+b), K = (a+f)*(b+e).
def factors (t : Fin 3) (x : V → Bool) : Bool × Bool :=
  ![(x 2, x 4 || x 5), (x 3, x 0 || x 1), (x 0 || x 5, x 1 || x 4)] t

def order (o : Fin 6) : Fin 3 → Fin 3 :=
  ![![0, 1, 2], ![0, 2, 1], ![1, 0, 2], ![1, 2, 0], ![2, 0, 1], ![2, 1, 0]] o

def oneNoise (k : Bool) (a : Bool) : Bool := k && a

def twoNoise (k : Fin 5) (a b : Bool) : Bool := ![false, a, b, a && b, a || b] k

def births (o : Fin 6) (p q : Bool) (r s : Fin 5) (x : V → Bool) : Fin 3 → Bool :=
  let f₀ := factors (order o 0) x
  let a := f₀.1 && f₀.2
  let f₁ := factors (order o 1) x
  let b := (f₁.1 || oneNoise p a) && (f₁.2 || oneNoise q a)
  let f₂ := factors (order o 2) x
  let c := (f₂.1 || twoNoise r a b) && (f₂.2 || twoNoise s a b)
  ![a, b, c]

def rowMask (r : Fin 5) : Nat := ![9, 34, 36, 7, 56] r

def rowInput (r : Fin 5) : V → Bool := fun v => (rowMask r).testBit v.val

def below {α : Type} (x y : α → Bool) : Prop := ∀ i, x i = true → y i = true

def Mono1 (f : Bool → Bool) : Prop :=
  ∀ a b, (a = true → b = true) → f a = true → f b = true

def Mono2 (f : Bool → Bool → Bool) : Prop :=
  ∀ a b c d, (a = true → c = true) → (b = true → d = true) →
    f a b = true → f c d = true

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
lemma oneNoise_complete : ∀ f : Bool → Bool, Mono1 f → f false = false →
    ∃ k : Bool, ∀ a, f a = oneNoise k a := by
  unfold Mono1 oneNoise
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
lemma twoNoise_complete : ∀ f : Bool → Bool → Bool, Mono2 f → f false false = false →
    ∃ k : Fin 5, ∀ a b, f a b = twoNoise k a b := by
  unfold Mono2 twoNoise
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
lemma order_complete : ∀ f : Fin 3 → Fin 3, Function.Bijective f →
    ∃ o : Fin 6, f = order o := by
  unfold Function.Bijective Function.Injective Function.Surjective order
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
set_option synthInstance.maxSize 4096 in
lemma row_domination : ∀ (o : Fin 6) (p q : Bool) (r s : Fin 5),
    ∃ i : Fin 3, ∃ j : Fin 2,
      below (births o p q r s (rowInput ⟨i.val, by omega⟩))
        (births o p q r s (rowInput ⟨3 + j.val, by omega⟩)) := by
  unfold below births factors order oneNoise twoNoise rowInput rowMask
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
lemma positive_rows : ∀ i : Fin 3, edgeBool (rowInput ⟨i.val, by omega⟩) = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
lemma negative_rows : ∀ j : Fin 2, edgeBool (rowInput ⟨3 + j.val, by omega⟩) = false := by
  decide +kernel

lemma no_monotone_combiner (o : Fin 6) (p q : Bool) (r s : Fin 5)
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
def generalBirths (σ : Fin 3 → Fin 3) (p q : Bool → Bool)
    (r s : Bool → Bool → Bool) (x : V → Bool) : Fin 3 → Bool :=
  let f₀ := factors (σ 0) x
  let a := f₀.1 && f₀.2
  let f₁ := factors (σ 1) x
  let b := (f₁.1 || p a) && (f₁.2 || q a)
  let f₂ := factors (σ 2) x
  let c := (f₂.1 || r a b) && (f₂.2 || s a b)
  ![a, b, c]

lemma no_general_combiner (σ : Fin 3 → Fin 3) (hσ : Function.Bijective σ)
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

end C6.ThreeBirth


namespace LinearNoise
open C6.DagTools

def linear {n : Nat} (S : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ v ∈ S, x v = true)

lemma linear_empty {n : Nat} (x : Fin n → Bool) : linear ∅ x = false := by
  simp [linear]

lemma linear_singleton {n : Nat} (v : Fin n) (x : Fin n → Bool) :
    linear {v} x = x v := by simp [linear]

lemma linear_union {n : Nat} (S T : Finset (Fin n)) (x : Fin n → Bool) :
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

def ZeroMono {k : Nat} (f : (Fin k → Bool) → Bool) : Prop :=
  f (fun _ => false) = false ∧
  ∀ a b, (∀ i, a i = true → b i = true) → f a = true → f b = true

def UsesAtMost {k : Nat} (n : Nat) (birth : Fin k → Nat)
    (w : Nat) (f : (Fin k → Bool) → Bool) : Prop :=
  ∀ a b, (∀ i, n + birth i ≤ w → a i = b i) → f a = f b

lemma uses_mono {k n : Nat} {birth : Fin k → Nat} {w u : Nat}
    {f : (Fin k → Bool) → Bool} (h : UsesAtMost n birth w f) (hwu : w ≤ u) :
    UsesAtMost n birth u f := by
  intro a b hab
  apply h a b
  intro i hi
  exact hab i (hi.trans hwu)

lemma zeroMono_or {k : Nat} {f g : (Fin k → Bool) → Bool}
    (hf : ZeroMono f) (hg : ZeroMono g) : ZeroMono (fun z => f z || g z) := by
  refine ⟨by dsimp only; rw [hf.1,hg.1]; rfl, ?_⟩
  intro a b hab hh
  rw [Bool.or_eq_true] at hh ⊢
  exact hh.elim (fun h => Or.inl (hf.2 a b hab h)) (fun h => Or.inr (hg.2 a b hab h))

lemma zeroMono_and {k : Nat} {f g : (Fin k → Bool) → Bool}
    (hf : ZeroMono f) (hg : ZeroMono g) : ZeroMono (fun z => f z && g z) := by
  refine ⟨by dsimp only; rw [hf.1,hg.1]; rfl, ?_⟩
  intro a b hab hh
  rw [Bool.and_eq_true] at hh ⊢
  exact ⟨hf.2 a b hab hh.1, hg.2 a b hab hh.2⟩

lemma wire_noise {n k : Nat} {D : Dag} (hS : Strict n D) (birth : Fin k → Nat)
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

end LinearNoise


namespace BirthNoiseProjection

open LinearNoise
open C6.ThreeBirth

lemma uses_before {n w : Nat} {birth : Fin 3 → Nat}
    {f : (Fin 3 → Bool) → Bool} (hb : StrictMono birth)
    (hf : UsesAtMost n birth w f) (i : Fin 3) (hw : w < n + birth i)
    (a b : Fin 3 → Bool) (hab : ∀ j, j < i → a j = b j) : f a = f b := by
  apply hf a b
  intro j hj
  apply hab j
  by_contra hji
  have hbirth := hb.monotone (le_of_not_gt hji)
  omega

lemma uses_before_zero {n w : Nat} {birth : Fin 3 → Nat}
    {f : (Fin 3 → Bool) → Bool} (hb : StrictMono birth)
    (hf : UsesAtMost n birth w f) (hw : w < n + birth 0)
    (z : Fin 3 → Bool) : f z = f ![false, false, false] := by
  apply uses_before hb hf 0 hw z ![false, false, false]
  intro j hj
  exact False.elim (by omega)

lemma uses_before_one {n w : Nat} {birth : Fin 3 → Nat}
    {f : (Fin 3 → Bool) → Bool} (hb : StrictMono birth)
    (hf : UsesAtMost n birth w f) (hw : w < n + birth 1)
    (z : Fin 3 → Bool) : f z = f ![z 0, false, false] := by
  apply uses_before hb hf 1 hw z ![z 0, false, false]
  intro j hj
  have hj0 : j = 0 := by omega
  subst j
  rfl

lemma uses_before_two {n w : Nat} {birth : Fin 3 → Nat}
    {f : (Fin 3 → Bool) → Bool} (hb : StrictMono birth)
    (hf : UsesAtMost n birth w f) (hw : w < n + birth 2)
    (z : Fin 3 → Bool) : f z = f ![z 0, z 1, false] := by
  apply uses_before hb hf 2 hw z ![z 0, z 1, false]
  intro j hj
  have hj01 : j = 0 ∨ j = 1 := by omega
  rcases hj01 with rfl | rfl <;> rfl

lemma zeroMono_restrict_one {f : (Fin 3 → Bool) → Bool} (hf : ZeroMono f) :
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

lemma zeroMono_restrict_two {f : (Fin 3 → Bool) → Bool} (hf : ZeroMono f) :
    Mono2 (fun a b => f ![a, b, false]) ∧ f ![false, false, false] = false := by
  refine ⟨?_, (zeroMono_restrict_one hf).2⟩
  intro a b c d hac hbd hab
  apply hf.2 ![a, b, false] ![c, d, false] _ hab
  intro i hi
  fin_cases i
  · exact hac hi
  · exact hbd hi
  · simp at hi

lemma zero_before_zero {n w : Nat} {birth : Fin 3 → Nat}
    {f : (Fin 3 → Bool) → Bool} (hb : StrictMono birth)
    (hf : UsesAtMost n birth w f) (hm : ZeroMono f) (hw : w < n + birth 0)
    (z : Fin 3 → Bool) : f z = false := by
  rw [uses_before_zero hb hf hw z]
  exact (zeroMono_restrict_one hm).2

end BirthNoiseProjection


namespace BirthOrder

lemma strictMono_three (f : Fin 3 → Nat) (h01 : f 0 < f 1) (h12 : f 1 < f 2) :
    StrictMono f := by
  have h02 := lt_trans h01 h12
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

lemma sort_three (G : Fin 3 → Nat) (hG : Function.Injective G) :
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

end BirthOrder


namespace BirthNoiseAdapter

open C6 C6.DagTools C6.ThreeBirth LinearNoise BirthNoiseProjection

lemma no_sorted_three_births {D : Dag} (hD : Strict 6 D)
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

lemma no_three_births {D : Dag} (hD : Strict 6 D)
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

end BirthNoiseAdapter


namespace C6
open DagTools LinearNoise

lemma linear_pair (a b : V) (x : V → Bool) : linear {a, b} x = (x a || x b) := by
  have hs : ({a, b} : Finset V) = {a} ∪ {b} := by ext v; simp
  rw [hs, linear_union, linear_singleton, linear_singleton]

lemma and_value_on_slots {D : Dag} (hS : Strict 6 D) (e : ℕ × Bool)
    (hj : e.1 < D.length) (ht : tag D e.1 = true) (x : V → Bool) :
    val D x (6 + e.1) =
      (val D x (src D e) && val D x (src D (sem_bar e))) := by
  rw [val_gate hS x e.1 hj, ht, gop_true]
  obtain ⟨j, s⟩ := e
  cases s <;> simp [src, sem_bar, Bool.and_comm]

lemma bf_birth_data {R : Dag} (h : StrictLive 6 (prefixTwo ++ R))
    (hc : sem_Comp 6 adj (prefixTwo ++ R)) (hb4 : Bplus 6 (prefixTwo ++ R) = 4) :
    ∃ G L T : Fin 3 → ℕ,
      Function.Injective G ∧
      (∀ i, G i < (prefixTwo ++ R).length) ∧
      (∀ i, L i < 6 + G i ∧ T i < 6 + G i) ∧
      (∀ i (x : V → Bool), val (prefixTwo ++ R) x (6 + G i) =
        (val (prefixTwo ++ R) x (L i) && val (prefixTwo ++ R) x (T i))) ∧
      (∀ i (x : V → Bool), linear (supp 6 (prefixTwo ++ R) (L i)) x = (ThreeBirth.factors i x).1 ∧
        linear (supp 6 (prefixTwo ++ R) (T i)) x = (ThreeBirth.factors i x).2) ∧
      (∀ j, j < (prefixTwo ++ R).length → tag (prefixTwo ++ R) j = true →
        (∃ i, G i = j) ∨ (supp 6 (prefixTwo ++ R) (opA (prefixTwo ++ R) j) = ∅ ∧
          supp 6 (prefixTwo ++ R) (opB (prefixTwo ++ R) j) = ∅)) := by
  obtain ⟨ec, ed, k, hec, hed, hkj, hkt, hcd, hkc, hkd, hC, hD, hK, hK', hother⟩ :=
    bf_three_birth_geometry h hc hb4
  let G : Fin 3 → ℕ := ![ec.1, ed.1, k.1]
  let L : Fin 3 → ℕ := ![src (prefixTwo ++ R) ec, src (prefixTwo ++ R) ed, src (prefixTwo ++ R) k]
  let T : Fin 3 → ℕ := ![src (prefixTwo ++ R) (sem_bar ec),
    src (prefixTwo ++ R) (sem_bar ed), src (prefixTwo ++ R) (sem_bar k)]
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
      · change linear (supp 6 (prefixTwo ++ R) (src (prefixTwo ++ R) ec)) x = x 2
        rw [hec.2.2.1, linear_singleton]
      · change linear (supp 6 (prefixTwo ++ R) (src (prefixTwo ++ R) (sem_bar ec))) x = (x 4 || x 5)
        rw [hC, linear_pair]
    · constructor
      · change linear (supp 6 (prefixTwo ++ R) (src (prefixTwo ++ R) ed)) x = x 3
        rw [hed.2.2.1, linear_singleton]
      · change linear (supp 6 (prefixTwo ++ R) (src (prefixTwo ++ R) (sem_bar ed))) x = (x 0 || x 1)
        rw [hD, linear_pair]
    · constructor
      · change linear (supp 6 (prefixTwo ++ R) (src (prefixTwo ++ R) k)) x = (x 0 || x 5)
        rw [hK, linear_pair]
      · change linear (supp 6 (prefixTwo ++ R) (src (prefixTwo ++ R) (sem_bar k))) x = (x 1 || x 4)
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

end C6


namespace C6
open DagTools

lemma c6_Bplus_ge_three {D : Dag} (h : StrictLive 6 D) (hc : sem_Comp 6 adj D) :
    3 ≤ Bplus 6 D := by
  obtain ⟨b, hb⟩ := sem_exists_pureBranch graph_ok h.1 hc
  have hi := (independent_facts _ (inelig_independent h hc)).1
  have he := elig_le_Bplus h.1 b hb
  have hn := inelig_card_add 6 D
  omega

lemma opposite_raw_or_Bplus_ge_four {D : Dag} (h : StrictLive 6 D)
    (hc : sem_Comp 6 adj D) {j : ℕ} (hj : j < D.length)
    (ht : tag D j = false) {v w : V} (hv : opA D j = v.val)
    (hw : opB D j = w.val) (hop : oppositePair v w) : 4 ≤ Bplus 6 D := by
  by_contra hsmall
  have hB : Bplus 6 D ≤ 3 := by omega
  obtain ⟨b, hb⟩ := sem_exists_pureBranch graph_ok h.1 hc
  have hi := (independent_facts _ (inelig_independent h hc)).1
  have he := elig_le_Bplus h.1 b hb
  have hn := inelig_card_add 6 D
  have hI : (ineligSet 6 D).card = 3 := by omega
  have hve := raw_branch_eligible
    (raw_or_branch_left graph_ok h.1 hc hj ht hv hw (opposite_distinct v w hop))
  have hwe := raw_branch_eligible
    (raw_or_branch_right graph_ok h.1 hc hj ht hv hw (opposite_distinct v w hop))
  rcases independent_hits_opposite _ (inelig_independent h hc) hI v w hop with hvi | hwi
  · exact (sem_mem_inelig.mp hvi) hve
  · exact (sem_mem_inelig.mp hwi) hwe

lemma prefixTwo_Bplus_ge_four {R : Dag} (h : StrictLive 6 (prefixTwo ++ R))
    (hc : sem_Comp 6 adj (prefixTwo ++ R)) : 4 ≤ Bplus 6 (prefixTwo ++ R) := by
  obtain ⟨b, hb⟩ := sem_exists_pureBranch graph_ok h.1 hc
  have hs : fourEndpoints ⊆ eligSet 6 (prefixTwo ++ R) := by
    intro v hv
    exact raw_branch_eligible (prefixTwo_branches h hc v hv)
  have hfour : fourEndpoints.card = 4 := by decide
  have he := Finset.card_le_card hs
  have hB := elig_le_Bplus h.1 b hb
  omega

lemma prefixThree_Bplus_ge_six {R : Dag} (h : StrictLive 6 (prefixThree ++ R))
    (hc : sem_Comp 6 adj (prefixThree ++ R)) : 6 ≤ Bplus 6 (prefixThree ++ R) := by
  classical
  obtain ⟨b, hb⟩ := sem_exists_pureBranch graph_ok h.1 hc
  have heq : eligSet 6 (prefixThree ++ R) = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro v
    exact raw_branch_eligible (prefixThree_all_branches h hc v)
  have hB := elig_le_Bplus h.1 b hb
  rw [heq] at hB
  simpa using hB

lemma c6_length_ge_eight_add_Bzero {D : Dag} (h : StrictLive 6 D)
    (hc : sem_Comp 6 adj D) : 8 + Bzero 6 D ≤ D.length := by
  have hp := c6_Bplus_ge_three h hc
  have hs := surplus_identity h
  rw [totalSurplus_split] at hs
  omega

lemma one_pair_length_ge_eight_add_Bzero {v w : V} (hop : oppositePair v w)
    {R : Dag} (h : StrictLive 6 ([(false, v.val, w.val)] ++ R))
    (hc : sem_Comp 6 adj ([(false, v.val, w.val)] ++ R)) :
    8 + Bzero 6 ([(false, v.val, w.val)] ++ R) ≤ R.length := by
  have hp := opposite_raw_or_Bplus_ge_four h hc (j := 0) (by simp)
    (by simp [tag]) (v := v) (w := w) (by simp [opA]) (by simp [opB]) hop
  have hs := surplus_identity h
  rw [totalSurplus_split] at hs
  simp only [List.length_append, List.length_cons, List.length_nil] at hs
  omega

lemma prefixThree_length_ge_eight_add_Bzero {R : Dag}
    (h : StrictLive 6 (prefixThree ++ R)) (hc : sem_Comp 6 adj (prefixThree ++ R)) :
    8 + Bzero 6 (prefixThree ++ R) ≤ R.length := by
  have hp := prefixThree_Bplus_ge_six h hc
  have hs := surplus_identity h
  rw [totalSurplus_split] at hs
  have hlen : (prefixThree ++ R).length = 3 + R.length := by simp [prefixThree]; omega
  rw [hlen] at hs
  omega

end C6


namespace C6
open DagTools

lemma no_prefixTwo_Bplus_four {R : Dag} (h : StrictLive 6 (prefixTwo ++ R))
    (hc : sem_Comp 6 adj (prefixTwo ++ R))
    (hb4 : Bplus 6 (prefixTwo ++ R) = 4) : False := by
  obtain ⟨G, L, T, hG, hvalid, hbound, hgate, hlin, hkind⟩ := bf_birth_data h hc hb4
  apply BirthNoiseAdapter.no_three_births h.1 G L T hG hvalid
    (fun i => (hbound i).1) (fun i => (hbound i).2) hgate
    (fun i x => (hlin i x).1) (fun i x => (hlin i x).2)
    (fun j hj ht => bf_and_empty h hc hb4 hj ht) ?_ (outW 6 (prefixTwo ++ R)) ?_
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

lemma prefixTwo_Bplus_ge_five {R : Dag} (h : StrictLive 6 (prefixTwo ++ R))
    (hc : sem_Comp 6 adj (prefixTwo ++ R)) : 5 ≤ Bplus 6 (prefixTwo ++ R) := by
  have hb := prefixTwo_Bplus_ge_four h hc
  by_contra hn
  have he : Bplus 6 (prefixTwo ++ R) = 4 := by omega
  exact no_prefixTwo_Bplus_four h hc he

lemma prefixTwo_length_ge_eight_add_Bzero {R : Dag} (h : StrictLive 6 (prefixTwo ++ R))
    (hc : sem_Comp 6 adj (prefixTwo ++ R)) :
    8 + Bzero 6 (prefixTwo ++ R) ≤ R.length := by
  have hb := prefixTwo_Bplus_ge_five h hc
  have hs := surplus_identity h
  rw [totalSurplus_split] at hs
  have hlen : (prefixTwo ++ R).length = R.length + 2 := by simp [prefixTwo]
  rw [hlen] at hs
  omega

end C6



namespace FreePairCausalTrace

open C6.DagTools

def SeedsBefore {n : Nat} (D : Dag) (Free : Finset (Fin n) → Prop)
    (P : Finset (Fin n)) (w : Nat) (x : Fin n → Bool) : Prop :=
  (∃ u, u < w ∧ ¬ Free (supp n D u) ∧ supp n D u ⊆ P ∧ val D x u = true) ∨
  (∃ u v, u < w ∧ v < w ∧ u ≠ v ∧ ¬ Free (supp n D u) ∧ ¬ Free (supp n D v) ∧
    supp n D u ∩ supp n D v = P ∧ val D x u = true ∧ val D x v = true)

lemma seeds_mono {n : Nat} {D : Dag} {Free : Finset (Fin n) → Prop}
    {P : Finset (Fin n)} {u w : Nat} {x : Fin n → Bool}
    (h : SeedsBefore D Free P u x) (huw : u ≤ w) : SeedsBefore D Free P w x := by
  rcases h with ⟨v, hv, hf, hs, hx⟩ | ⟨v, z, hv, hz, hvz, hfv, hfz, hs, hxv, hxz⟩
  · exact Or.inl ⟨v, hv.trans_le huw, hf, hs, hx⟩
  · exact Or.inr ⟨v, z, hv.trans_le huw, hz.trans_le huw, hvz, hfv, hfz, hs, hxv, hxz⟩

lemma free_carrier_trace {n : Nat} {D : Dag} (hD : Strict n D)
    (Free : Finset (Fin n) → Prop) (P : Finset (Fin n)) (hP : Free P)
    (hraw : ∀ v : Fin n, ¬ Free {v})
    (hclass : ∀ S, Free S → (S ⊆ P ∨ P ⊆ S) → S = P)
    (x : Fin n → Bool) :
    ∀ w, w < n + D.length → supp n D w = P → val D x w = true →
      SeedsBefore D Free P w x := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hs hx
    by_cases hin : w < n
    · have hsingle : supp n D w = {⟨w, hin⟩} := supp_input D ⟨w, hin⟩
      exact False.elim (hraw ⟨w, hin⟩ (by rwa [← hsingle, hs]))
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < D.length := by omega
      obtain ⟨ha, hb, hab⟩ := hD j hj
      by_cases ht : tag D j = true
      · have hs' : supp n D (opA D j) ∩ supp n D (opB D j) = P := by
          rwa [sem_supp_and hD hj ht] at hs
        have hx' : val D x (opA D j) = true ∧ val D x (opB D j) = true := by
          rwa [val_gate hD x j hj, ht, gop_true, Bool.and_eq_true] at hx
        by_cases hfA : Free (supp n D (opA D j))
        · have hsA : supp n D (opA D j) = P :=
            hclass _ hfA (Or.inr (by rw [← hs']; exact Finset.inter_subset_left))
          exact seeds_mono (ih _ ha (by omega) hsA hx'.1) ha.le
        · by_cases hfB : Free (supp n D (opB D j))
          · have hsB : supp n D (opB D j) = P :=
              hclass _ hfB (Or.inr (by rw [← hs']; exact Finset.inter_subset_right))
            exact seeds_mono (ih _ hb (by omega) hsB hx'.2) hb.le
          · exact Or.inr ⟨opA D j, opB D j, ha, hb, hab, hfA, hfB, hs', hx'.1, hx'.2⟩
      · have ht0 : tag D j = false := Bool.eq_false_of_not_eq_true ht
        have hs' : supp n D (opA D j) ∪ supp n D (opB D j) = P := by
          rwa [sem_supp_or hD hj ht0] at hs
        have hx' : val D x (opA D j) = true ∨ val D x (opB D j) = true := by
          rwa [val_gate hD x j hj, ht0, gop_false, Bool.or_eq_true] at hx
        rcases hx' with hxA | hxB
        · have hsub : supp n D (opA D j) ⊆ P := by rw [← hs']; exact Finset.subset_union_left
          by_cases hfA : Free (supp n D (opA D j))
          · exact seeds_mono (ih _ ha (by omega) (hclass _ hfA (Or.inl hsub)) hxA) ha.le
          · exact Or.inl ⟨opA D j, ha, hfA, hsub, hxA⟩
        · have hsub : supp n D (opB D j) ⊆ P := by rw [← hs']; exact Finset.subset_union_right
          by_cases hfB : Free (supp n D (opB D j))
          · exact seeds_mono (ih _ hb (by omega) (hclass _ hfB (Or.inl hsub)) hxB) hb.le
          · exact Or.inl ⟨opB D j, hb, hfB, hsub, hxB⟩

lemma paid_trace {n : Nat} {D : Dag} {Free : Finset (Fin n) → Prop}
    {P : Finset (Fin n)} {w : Nat} {x : Fin n → Bool}
    (hP : 1 < P.card) (hx : ∀ v ∈ P, x v = false)
    (h : SeedsBefore D Free P w x) :
    (∃ u, n ≤ u ∧ u < w ∧ ¬ Free (supp n D u) ∧ supp n D u ⊆ P ∧ val D x u = true) ∨
    (∃ u v, n ≤ u ∧ n ≤ v ∧ u < w ∧ v < w ∧ u ≠ v ∧
      ¬ Free (supp n D u) ∧ ¬ Free (supp n D v) ∧
      supp n D u ∩ supp n D v = P ∧ val D x u = true ∧ val D x v = true) := by
  have hlarge (u : Nat) (hu : P ⊆ supp n D u) : n ≤ u := by
    by_contra hn
    have hu' : u < n := by omega
    have hc := Finset.card_le_card hu
    rw [show supp n D u = {⟨u, hu'⟩} from supp_input D ⟨u, hu'⟩,
      Finset.card_singleton] at hc
    omega
  rcases h with ⟨u, hu, hf, hs, hval⟩ | ⟨u, v, hu, hv, huv, hfu, hfv, hs, hxu, hxv⟩
  · have hnu : n ≤ u := by
      by_contra hn
      have hu' : u < n := by omega
      have hv : (⟨u, hu'⟩ : Fin n) ∈ P := hs (by
        rw [show supp n D u = {⟨u, hu'⟩} from supp_input D ⟨u, hu'⟩]
        exact Finset.mem_singleton_self _)
      rw [val_input D x u hu', hx _ hv] at hval
      cases hval
    exact Or.inl ⟨u, hnu, hu, hf, hs, hval⟩
  · have hnu := hlarge u (by rw [← hs]; exact Finset.inter_subset_left)
    have hnv := hlarge v (by rw [← hs]; exact Finset.inter_subset_right)
    exact Or.inr ⟨u, v, hnu, hnv, hu, hv, huv, hfu, hfv, hs, hxu, hxv⟩

lemma cardinal_two_trace {n : Nat} {D : Dag} (hD : Strict n D)
    (Free : Finset (Fin n) → Prop) (hsize : ∀ S, Free S → S.card = 2)
    (P : Finset (Fin n)) (hP : Free P) (x : Fin n → Bool)
    (w : Nat) (hw : w < n + D.length) (hs : supp n D w = P)
    (hx : val D x w = true) : SeedsBefore D Free P w x := by
  apply free_carrier_trace hD Free P hP ?_ ?_ x w hw hs hx
  · intro v hv
    have hc := hsize {v} hv
    simp only [Finset.card_singleton] at hc
    omega
  · intro S hS hcomp
    rcases hcomp with hsub | hsub
    · exact Finset.eq_of_subset_of_card_le hsub (by rw [hsize S hS, hsize P hP])
    · exact (Finset.eq_of_subset_of_card_le hsub (by rw [hsize S hS, hsize P hP])).symm

end FreePairCausalTrace


namespace C6.GenericPair
open DagTools

lemma bf_budget {D : Dag} (h : StrictLive 6 D)
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

lemma bf_inelig {D : Dag} (h : StrictLive 6 D)
    (hc : sem_Comp 6 adj D) (hE : fourEndpoints ⊆ eligSet 6 D) (hb4 : Bplus 6 D = 4) :
    ineligSet 6 D = {2, 3} := by
  classical
  obtain ⟨_, _, heq, _⟩ := bf_budget h hc hE hb4
  ext v
  rw [sem_mem_inelig, heq]
  fin_cases v <;> decide

lemma bf_flow {D : Dag} (h : StrictLive 6 D)
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

lemma consumer_two_exits {D : Dag} (h : StrictLive 6 D) (hc : sem_Comp 6 adj D)
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

lemma bf_endpoint_exits {D : Dag} (h : StrictLive 6 D)
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

lemma bf_merges_empty {D : Dag} (h : StrictLive 6 D)
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

lemma bf_and_empty {D : Dag} (h : StrictLive 6 D)
    (hc : sem_Comp 6 adj D) (hE : fourEndpoints ⊆ eligSet 6 D) (hb4 : Bplus 6 D = 4)
    {j : ℕ} (hj : j < D.length) (ht : tag D j = true) :
    supp 6 D (6 + j) = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro v hv
  have hg := sem_zm_gate h.1 (bf_merges_empty h hc hE hb4 v) hj hv
  rw [ht] at hg
  exact Bool.noConfusion hg.1

lemma bf_exits_le_two {D : Dag} (h : StrictLive 6 D)
    (hc : sem_Comp 6 adj D) (hE : fourEndpoints ⊆ eligSet 6 D) (hb4 : Bplus 6 D = 4)
    (v : V) : (sem_W 6 D v).card ≤ 2 := by
  have hf := bf_flow h hc hE hb4 v
  split_ifs at hf <;> omega

lemma consumer_other_exit {D : Dag} {z v : V} {e : ℕ × Bool}
    (he : Consumer D z e) (hv : v ∈ supp 6 D (src D (sem_bar e))) :
    sem_bar e ∈ sem_W 6 D v := by
  apply sem_mem_W.mpr
  refine ⟨he.1, hv, ?_⟩
  change v ∉ supp 6 D (6 + e.1)
  rw [he.2.2.2.1]
  exact Finset.notMem_empty _

lemma joint_not_consumer {D : Dag} {v u z : V} {f e : ℕ × Bool}
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

lemma consumer_extra_impossible {D : Dag} (h : StrictLive 6 D) (hc : sem_Comp 6 adj D)
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

lemma consumer_own_not_other {D : Dag} {z : V} {e : ℕ × Bool}
    (he : Consumer D z e) : z ∉ supp 6 D (src D (sem_bar e)) := by
  intro hz
  have hm := consumer_other_exit he hz
  rw [he.2.2.2.2.2, Finset.mem_singleton] at hm
  exact (sem_bar_ne e) hm

lemma consumer_other_inelig_not {D : Dag} {z w : V} {ec ed : ℕ × Bool}
    (hec : Consumer D z ec) (hed : Consumer D w ed) (hne : z ≠ w) :
    w ∉ supp 6 D (src D (sem_bar ec)) := by
  intro hw
  have hm := consumer_other_exit hec hw
  rw [hed.2.2.2.2.2, Finset.mem_singleton] at hm
  have hg : ec.1 = ed.1 := by
    simpa only [sem_bar] using congrArg (fun q : ℕ × Bool => q.1) hm
  exact hne (consumers_injective hec hed hg)

lemma bf_C_opposite {D : Dag} (h : StrictLive 6 D)
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

lemma bf_D_opposite {D : Dag} (h : StrictLive 6 D)
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

lemma joint_support_eligible {D : Dag} (h : StrictLive 6 D) (hc : sem_Comp 6 adj D)
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

end C6.GenericPair


namespace C6.GenericPair
open DagTools

lemma common_exit_of_joint_support {D : Dag} (h : StrictLive 6 D)
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

lemma bf_common_AF {D : Dag} (h : StrictLive 6 D)
    (hc : sem_Comp 6 adj D) (hE : fourEndpoints ⊆ eligSet 6 D) (hb4 : Bplus 6 D = 4)
    (hAF : ∃ w, (0 : V) ∈ supp 6 D w ∧ (5 : V) ∈ supp 6 D w) :
    ∃ k, k ∈ sem_W 6 D 0 ∧ k ∈ sem_W 6 D 5 := by
  obtain ⟨w, hwa, hwf⟩ := hAF
  exact common_exit_of_joint_support h hc (fun j hj ht => bf_and_empty h hc hE hb4 hj ht)
    0 5 hwa hwf

lemma two_exits_eq {D : Dag} {v : V} {e f : ℕ × Bool}
    (hle : (sem_W 6 D v).card ≤ 2) (he : e ∈ sem_W 6 D v)
    (hf : f ∈ sem_W 6 D v) (hne : e ≠ f) : sem_W 6 D v = {e, f} := by
  classical
  have hs : {e, f} ⊆ sem_W 6 D v := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl <;> assumption
  exact (Finset.eq_of_subset_of_card_le hs (by simpa [hne] using hle)).symm

lemma slot_not_consumer {D : Dag} {v z : V} {k e : ℕ × Bool}
    (hk : k ∈ sem_W 6 D v) (he : Consumer D z e)
    (hvz : v ≠ z) (hopp : v ∉ supp 6 D (src D (sem_bar e))) : k.1 ≠ e.1 := by
  intro hg
  have hv := (sem_mem_W.mp hk).2.1
  rcases sem_same_gate hg.symm with hf | hf
  · rw [hf, he.2.2.1, Finset.mem_singleton] at hv
    exact hvz hv
  · rw [hf] at hv
    exact hopp hv

lemma bf_AF_distinct {D : Dag} (h : StrictLive 6 D)
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

lemma bf_cross_partners {D : Dag} (h : StrictLive 6 D)
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

lemma exit_not_opposite {D : Dag} (hS : Strict 6 D) {v : V} {e : ℕ × Bool}
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

lemma consumer_not_other_gate {D : Dag} {z : V} {e k : ℕ × Bool}
    (he : Consumer D z e) (hj : k.1 < D.length)
    (hempty : supp 6 D (6 + k.1) = ∅) (hne : k.1 ≠ e.1) :
    z ∉ supp 6 D (src D k) := by
  intro hz
  have hk : k ∈ sem_W 6 D z := sem_mem_W.mpr
    ⟨hj, hz, by rw [hempty]; exact Finset.notMem_empty _⟩
  rw [he.2.2.2.2.2, Finset.mem_singleton] at hk
  exact hne (congrArg Prod.fst hk)

lemma bf_cross_supports {D : Dag} (h : StrictLive 6 D)
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

lemma bf_three_exit_gates {D : Dag} (h : StrictLive 6 D)
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

lemma bf_other_and_inputs_empty {D : Dag} (h : StrictLive 6 D)
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

lemma bf_three_birth_geometry {D : Dag} (h : StrictLive 6 D)
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

end C6.GenericPair


namespace C6.GenericPair
open DagTools LinearNoise

lemma bf_birth_data {D : Dag} (h : StrictLive 6 D)
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

end C6.GenericPair


namespace C6.GenericPair
open DagTools

lemma no_Bplus_four {D : Dag} (h : StrictLive 6 D) (hc : sem_Comp 6 adj D)
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

lemma two_pair_occurrences_Bplus_ge_five {D : Dag}
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

lemma two_pair_occurrences_length_ge_ten_add_Bzero {D : Dag}
    (h : StrictLive 6 D) (hc : sem_Comp 6 adj D)
    (hAF : ∃ w, (0 : V) ∈ supp 6 D w ∧ (5 : V) ∈ supp 6 D w)
    (hBE : ∃ w, (1 : V) ∈ supp 6 D w ∧ (4 : V) ∈ supp 6 D w) :
    10 + Bzero 6 D ≤ D.length := by
  have hb := two_pair_occurrences_Bplus_ge_five h hc hAF hBE
  have hs := surplus_identity h
  rw [totalSurplus_split] at hs
  omega

end C6.GenericPair



namespace C6.GenericPair
open DagTools

lemma opposite_joint_Bplus_ge_four {D : Dag} (h : StrictLive 6 D)
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

lemma opposite_joint_length_ge_nine_add_Bzero {D : Dag} (h : StrictLive 6 D)
    (hc : sem_Comp 6 adj D) {u v : V} (hop : oppositePair u v)
    (hjoint : ∃ w, u ∈ supp 6 D w ∧ v ∈ supp 6 D w) :
    9 + Bzero 6 D ≤ D.length := by
  have hb := opposite_joint_Bplus_ge_four h hc hop hjoint
  have hs := surplus_identity h
  rw [totalSurplus_split] at hs
  omega

lemma three_pair_occurrences_Bplus_ge_six {D : Dag}
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

lemma three_pair_occurrences_length_ge_eleven_add_Bzero {D : Dag}
    (h : StrictLive 6 D) (hc : sem_Comp 6 adj D)
    (hAF : ∃ w, (0 : V) ∈ supp 6 D w ∧ (5 : V) ∈ supp 6 D w)
    (hBE : ∃ w, (1 : V) ∈ supp 6 D w ∧ (4 : V) ∈ supp 6 D w)
    (hCD : ∃ w, (2 : V) ∈ supp 6 D w ∧ (3 : V) ∈ supp 6 D w) :
    11 + Bzero 6 D ≤ D.length := by
  have hb := three_pair_occurrences_Bplus_ge_six h hc hAF hBE hCD
  have hs := surplus_identity h
  rw [totalSurplus_split] at hs
  omega

end C6.GenericPair


namespace C6.GenericPair
open DagTools

lemma joint_relabel {D : Dag} (σ : Equiv.Perm V) (hS : Strict 6 D) {u v : V}
    (hJ : ∃ w, u ∈ supp 6 D w ∧ v ∈ supp 6 D w) :
    ∃ w, σ u ∈ supp 6 (relabel σ D) w ∧ σ v ∈ supp 6 (relabel σ D) w := by
  obtain ⟨w, hu, hv⟩ := hJ
  refine ⟨liftP σ w, ?_, ?_⟩
  · rw [relabel_supp σ hS]
    exact Finset.mem_image.mpr ⟨u, hu, rfl⟩
  · rw [relabel_supp σ hS]
    exact Finset.mem_image.mpr ⟨v, hv, rfl⟩

lemma pair01_length {D : Dag} (h : StrictLive 6 D) (hc : sem_Comp 6 adj D)
    (hAF : ∃ w, (0 : V) ∈ supp 6 D w ∧ (5 : V) ∈ supp 6 D w)
    (hBE : ∃ w, (1 : V) ∈ supp 6 D w ∧ (4 : V) ∈ supp 6 D w) : 10 ≤ D.length := by
  have hb := two_pair_occurrences_length_ge_ten_add_Bzero h hc hAF hBE
  omega

lemma pair02_length {D : Dag} (h : StrictLive 6 D) (hc : sem_Comp 6 adj D)
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

lemma pair12_length {D : Dag} (h : StrictLive 6 D) (hc : sem_Comp 6 adj D)
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

def PairOccurs (D : Dag) (p : Fin 3) : Prop :=
  ∃ w, (![0, 1, 2] p : V) ∈ supp 6 D w ∧ (![5, 4, 3] p : V) ∈ supp 6 D w

lemma two_distinct_pair_occurrences_length {D : Dag}
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

end C6.GenericPair


namespace C6.GenericPair
open DagTools

lemma one_pair_occurs_length {D : Dag} (h : StrictLive 6 D) (hc : sem_Comp 6 adj D)
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

lemma all_pair_occurrences_length {D : Dag} (h : StrictLive 6 D) (hc : sem_Comp 6 adj D)
    (hp : ∀ p : Fin 3, PairOccurs D p) : 11 ≤ D.length := by
  have hb := three_pair_occurrences_length_ge_eleven_add_Bzero h hc
    (by simpa [PairOccurs] using hp 0)
    (by simpa [PairOccurs] using hp 1)
    (by simpa [PairOccurs] using hp 2)
  omega

lemma pair_occurrences_length {D : Dag} (h : StrictLive 6 D) (hc : sem_Comp 6 adj D)
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

end C6.GenericPair


namespace RetainedGateCount

lemma retained_unmarked_le_seven {α : Type*} [DecidableEq α]
    (U B M S : Finset α) (hU : U.card ≤ 19)
    (hB : B ⊆ U) (hM : M ⊆ U) (hS : S ⊆ U)
    (hBc : B.card = 6) (hMc : M.card = 6)
    (hBM : Disjoint B M) (hSB : Disjoint S B) : (S \ M).card ≤ 7 := by
  have hBMcard : (B ∪ M).card = 12 := by
    rw [Finset.card_union_of_disjoint hBM, hBc, hMc]
  have hdis : Disjoint (S \ M) (B ∪ M) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨hxS, hxM⟩ := Finset.mem_sdiff.mp hx
    rcases Finset.mem_union.mp hy with hxB | hxM'
    · exact Finset.disjoint_left.mp hSB hxS hxB
    · exact hxM hxM'
  have hsub : (S \ M) ∪ (B ∪ M) ⊆ U := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hS (Finset.mem_sdiff.mp hx).1
    · rcases Finset.mem_union.mp hx with hx | hx
      · exact hB hx
      · exact hM hx
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis, hBMcard] at hc
  omega

lemma retained_le_seven_add_marked {α : Type*} [DecidableEq α]
    (U B M S : Finset α) (hU : U.card ≤ 19)
    (hB : B ⊆ U) (hM : M ⊆ U) (hS : S ⊆ U)
    (hBc : B.card = 6) (hMc : M.card = 6)
    (hBM : Disjoint B M) (hSB : Disjoint S B) :
    S.card ≤ 7 + (S ∩ M).card := by
  have hd := retained_unmarked_le_seven U B M S hU hB hM hS hBc hMc hBM hSB
  have hc := Finset.card_sdiff_add_card_inter S M
  omega

end RetainedGateCount


namespace MarkedC6Contradiction

open C6 C6.DagTools C6.GenericPair

lemma retained_marked_impossible {α : Type*} [DecidableEq α]
    (U B M S : Finset α) (hU : U.card ≤ 19)
    (hB : B ⊆ U) (hM : M ⊆ U) (hS : S ⊆ U)
    (hBc : B.card = 6) (hMc : M.card = 6)
    (hBM : Disjoint B M) (hSB : Disjoint S B)
    (label : α → Fin 3) (hinj : Set.InjOn label ↑(S ∩ M))
    (D : Dag) (hD : StrictLive 6 D) (hc : sem_Comp 6 adj D)
    (hlen : D.length ≤ S.card)
    (hocc : ∀ j ∈ S ∩ M, PairOccurs D (label j)) : False := by
  classical
  have hu := RetainedGateCount.retained_le_seven_add_marked
    U B M S hU hB hM hS hBc hMc hBM hSB
  have hl := pair_occurrences_length hD hc ((S ∩ M).image label) (by
    intro p hp
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp
    exact hocc j hj)
  have he := Finset.card_image_of_injOn hinj
  rw [he] at hl
  omega

end MarkedC6Contradiction


namespace FreePairNoise
open C6.DagTools LinearNoise

lemma linear_mono {n : Nat} {S T : Finset (Fin n)} (h : S ⊆ T) (x : Fin n → Bool) :
    linear S x = true → linear T x = true := by
  intro hs
  obtain ⟨v,hv,hx⟩ := of_decide_eq_true hs
  exact decide_eq_true (Exists.intro v ⟨h hv,hx⟩)

lemma linear_absorb_subset {n : Nat} {S T : Finset (Fin n)}
    (h : S ⊆ T) (x : Fin n → Bool) : (linear T x || linear S x) = linear T x := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true]
  exact ⟨fun hst => hst.elim id (linear_mono h x), Or.inl⟩

lemma linear_absorb_wire {n : Nat} {D : Dag} (hD : Strict n D)
    (P : Finset (Fin n)) (u : Nat) (hP : P ⊆ supp n D u) (x : Fin n → Bool) :
    (linear P x || val D x u) = val D x u := by
  have hh : linear P x = true → val D x u = true := by
    intro hp
    obtain ⟨v,hv,hx⟩ := of_decide_eq_true hp
    apply val_mono hD (single v) x ?_ u (mem_supp.mp (hP hv))
    intro i hi
    have he : i = v := by simpa [single] using hi
    subst i
    exact hx
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true]
  exact ⟨fun hv => hv.elim hh id, Or.inr⟩

lemma join_augmented (l a b f g : Bool) (ha : (l || a) = (l || f))
    (hb : (l || b) = (l || g)) : (l || (a || b)) = (l || (f || g)) := by
  cases l <;> simp_all

lemma paid_coordinate {n k : Nat} {D : Dag} (Free : Finset (Fin n) → Prop)
    (birth : Fin k → Nat)
    (hbirth : ∀ j, j < D.length → ¬ Free (supp n D (n+j)) → ∃ i, birth i = j)
    (u : Nat) (hnu : n ≤ u) (hu : u < n + D.length) (hf : ¬ Free (supp n D u)) :
    ∃ i, n + birth i = u := by
  have he : n + (u-n) = u := by omega
  obtain ⟨i,hi⟩ := hbirth (u-n) (by omega) (by simpa only [he] using hf)
  exact ⟨i,by omega⟩

lemma carrier_noise {n k : Nat} {D : Dag} (hD : Strict n D)
    (Free : Finset (Fin n) → Prop) (hsize : ∀ S, Free S → S.card = 2)
    (birth : Fin k → Nat)
    (hbirth : ∀ j, j < D.length → ¬ Free (supp n D (n+j)) → ∃ i, birth i = j) :
    ∀ w, w < n + D.length → Free (supp n D w) →
      ∃ f : (Fin k → Bool) → Bool, ZeroMono f ∧ UsesAtMost n birth w f ∧
      ∀ x : Fin n → Bool, val D x w =
        (linear (supp n D w) x || f (fun i => val D x (n + birth i))) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hfree
    by_cases hin : w < n
    · have hh := hsize _ hfree
      rw [show supp n D w = {⟨w,hin⟩} from supp_input D ⟨w,hin⟩,
        Finset.card_singleton] at hh
      omega
    · obtain ⟨j,rfl⟩ : ∃ j, w = n+j := ⟨w-n,by omega⟩
      have hj : j < D.length := by omega
      let P := supp n D (n+j)
      have hcard : P.card = 2 := hsize _ hfree
      have hsame (S : Finset (Fin n)) (hS : Free S) (hc : S ⊆ P ∨ P ⊆ S) : S = P := by
        rcases hc with hs | hs
        · exact Finset.eq_of_subset_of_card_le hs (by rw [hsize S hS,hcard])
        · exact (Finset.eq_of_subset_of_card_le hs (by rw [hsize S hS,hcard])).symm
      have down (u : Nat) (hu : u < n+j) (hsub : supp n D u ⊆ P) :
          ∃ f : (Fin k → Bool) → Bool, ZeroMono f ∧ UsesAtMost n birth (n+j) f ∧
            ∀ x, (linear P x || val D x u) =
              (linear P x || f (fun i => val D x (n+birth i))) := by
        by_cases hinput : u < n
        · refine ⟨fun _ => false, ⟨rfl,fun a b hab hh => hh⟩, ?_, ?_⟩
          · intro a b hab
            rfl
          · intro x
            rw [val_input D x u hinput, ← linear_singleton ⟨u,hinput⟩ x, Bool.or_false]
            apply linear_absorb_subset
            simpa only [show supp n D u = {⟨u,hinput⟩} from supp_input D ⟨u,hinput⟩] using hsub
        · by_cases hf : Free (supp n D u)
          · have hs := hsame _ hf (Or.inl hsub)
            obtain ⟨f,hf0,hfu,hfv⟩ := ih u hu (by omega) hf
            refine ⟨f,hf0,uses_mono hfu hu.le,?_⟩
            intro x
            rw [hfv x,hs]
            simp
          · obtain ⟨i,hi⟩ := paid_coordinate Free birth hbirth u (by omega) (by omega) hf
            refine ⟨fun z => z i, ⟨rfl,fun a b hab hh => hab i hh⟩, ?_, ?_⟩
            · intro a b hab
              exact hab i (by omega)
            · intro x
              simp only [hi]
      have up (u : Nat) (hu : u < n+j) (hsub : P ⊆ supp n D u) :
          ∃ f : (Fin k → Bool) → Bool, ZeroMono f ∧ UsesAtMost n birth (n+j) f ∧
            ∀ x, val D x u = (linear P x || f (fun i => val D x (n+birth i))) := by
        have hnu : n ≤ u := by
          by_contra hh
          have hinput : u < n := by omega
          have hle := Finset.card_le_card hsub
          rw [show supp n D u = {⟨u,hinput⟩} from supp_input D ⟨u,hinput⟩,
            Finset.card_singleton,hcard] at hle
          omega
        by_cases hf : Free (supp n D u)
        · have hs := hsame _ hf (Or.inr hsub)
          obtain ⟨f,hf0,hfu,hfv⟩ := ih u hu (by omega) hf
          refine ⟨f,hf0,uses_mono hfu hu.le,?_⟩
          intro x
          simpa only [hs] using hfv x
        · obtain ⟨i,hi⟩ := paid_coordinate Free birth hbirth u hnu (by omega) hf
          refine ⟨fun z => z i, ⟨rfl,fun a b hab hh => hab i hh⟩, ?_, ?_⟩
          · intro a b hab
            exact hab i (by omega)
          · intro x
            simpa only [hi] using (linear_absorb_wire hD P u hsub x).symm
      obtain ⟨ha,hb,_⟩ := hD j hj
      by_cases ht : tag D j = true
      · have hs : supp n D (opA D j) ∩ supp n D (opB D j) = P :=
          (sem_supp_and hD hj ht).symm
        obtain ⟨f,hf,hu,hvf⟩ := up _ ha (by rw [← hs]; exact Finset.inter_subset_left)
        obtain ⟨g,hg,hv,hvg⟩ := up _ hb (by rw [← hs]; exact Finset.inter_subset_right)
        refine ⟨fun z => f z && g z,zeroMono_and hf hg,?_,?_⟩
        · intro a b hab
          dsimp only
          rw [hu a b hab,hv a b hab]
        · intro x
          change val D x (n+j) = (linear P x || _)
          rw [val_gate hD x j hj,ht,gop_true,hvf x,hvg x]
          cases linear P x <;> simp
      · have ht0 := Bool.eq_false_of_not_eq_true ht
        have hs : supp n D (opA D j) ∪ supp n D (opB D j) = P :=
          (sem_supp_or hD hj ht0).symm
        obtain ⟨f,hf,hu,hvf⟩ := down _ ha (by rw [← hs]; exact Finset.subset_union_left)
        obtain ⟨g,hg,hv,hvg⟩ := down _ hb (by rw [← hs]; exact Finset.subset_union_right)
        refine ⟨fun z => f z || g z,zeroMono_or hf hg,?_,?_⟩
        · intro a b hab
          dsimp only
          rw [hu a b hab,hv a b hab]
        · intro x
          change val D x (n+j) = (linear P x || _)
          calc
            val D x (n+j) = (linear P x || val D x (n+j)) :=
              (linear_absorb_wire hD P (n+j) (Finset.Subset.refl _) x).symm
            _ = (linear P x || (val D x (opA D j) || val D x (opB D j))) := by
              rw [val_gate hD x j hj,ht0,gop_false]
            _ = (linear P x || (f (fun i => val D x (n+birth i)) ||
                g (fun i => val D x (n+birth i)))) := join_augmented _ _ _ _ _ (hvf x) (hvg x)

end FreePairNoise


namespace FreePairNoise
open C6.DagTools LinearNoise

lemma paid_carrier_noise {n k : Nat} {D : Dag} (hD : Strict n D)
    (Free : Finset (Fin n) → Prop) (hsize : ∀ S, Free S → S.card = 2)
    (birth : Fin k → Nat)
    (hbirth : ∀ j, j < D.length → ¬ Free (supp n D (n+j)) → ∃ i, birth i = j)
    (hpaid : ∀ i, ¬ Free (supp n D (n + birth i)))
    (w : Nat) (hw : w < n + D.length) (hfree : Free (supp n D w)) :
    ∃ f : (Fin k → Bool) → Bool, ZeroMono f ∧ UsesAtMost n birth (w-1) f ∧
      ∀ x : Fin n → Bool, val D x w =
        (linear (supp n D w) x || f (fun i => val D x (n + birth i))) := by
  obtain ⟨f,hf,hu,hval⟩ := carrier_noise hD Free hsize birth hbirth w hw hfree
  refine ⟨f,hf,?_,hval⟩
  intro a b hab
  apply hu a b
  intro i hi
  have hne : n + birth i ≠ w := by
    intro he
    exact hpaid i (by simpa only [he] using hfree)
  exact hab i (by omega)

end FreePairNoise

end PEqualNP.Outside.L_meta_2590_aux
