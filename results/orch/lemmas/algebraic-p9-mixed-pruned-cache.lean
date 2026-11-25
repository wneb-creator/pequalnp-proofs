import PNPMixed9Finite
import PNPCapSevenBridge

namespace PEqualNP.Outside.L_meta_6659_aux

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

def matching : List (Fin 14 × Fin 14) :=
  [(0, 7), (1, 13), (2, 8), (3, 12), (4, 11), (5, 10), (6, 9)]

/-- The matching partner of a vertex. -/
def IsAut (σ : Equiv.Perm (Fin 14)) : Prop := ∀ u v : Fin 14, Adj (σ u) (σ v) ↔ Adj u v

theorem hc_isAut_of {σ : Equiv.Perm (Fin 14)}
    (h : ∀ u v : Fin 14, hc_adjB (σ u) (σ v) = hc_adjB u v) : IsAut σ := fun u v => by
  rw [← hc_adjB_iff, ← hc_adjB_iff u v, h]

theorem heawoodEdge_aut (σ : Equiv.Perm (Fin 14)) (hσ : IsAut σ) (x : Fin 14 → Bool) :
    HeawoodEdge (fun i => x (σ i)) ↔ HeawoodEdge x := by
  rw [heawoodEdge_iff_adj, heawoodEdge_iff_adj]
  constructor
  · rintro ⟨u, v, h, hu, hv⟩; exact ⟨σ u, σ v, (hσ u v).mpr h, hu, hv⟩
  · rintro ⟨u, v, h, hu, hv⟩
    refine ⟨σ.symm u, σ.symm v, ?_, by simpa using hu, by simpa using hv⟩
    rw [← hσ, Equiv.apply_symm_apply, Equiv.apply_symm_apply]; exact h

def hc_ofList (l : List ℕ) (v : Fin 14) : Fin 14 := Fin.ofNat 14 (l.getD v.val 0)

/-- The duality (a polarity): swaps the point side and the line side. -/
theorem heawood_not_single (v : Fin 14) : ¬ HeawoodEdge (fun i => decide (i = v)) := by
  rw [heawoodEdge_iff_adj]
  rintro ⟨a, b, hab, ha, hb⟩
  simp only [decide_eq_true_eq] at ha hb
  subst ha; subst hb; exact adj_irrefl _ hab

def Correct (D : Dag) : Prop :=
  ∀ x : Fin 14 → Bool, val D x (outW 14 D) = true ↔ HeawoodEdge x

/-- The official bridge: every `Monotone2` circuit for the Heawood edge function yields a
strict live constant-free binary DAG with at most as many gates. -/
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
def sem_W (n : ℕ) (D : Dag) (x : Fin n) : Finset (ℕ × Bool) := exitArcs n D (carrierT n D {x})

/-- The opposite operand position at the same gate. -/
def sem_bar (e : ℕ × Bool) : ℕ × Bool := (e.1, !e.2)

section SemCodes

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

theorem sem_mem_W {x : Fin n} {e : ℕ × Bool} : e ∈ sem_W n D x ↔
    e.1 < D.length ∧ x ∈ supp n D (src D e) ∧ x ∉ supp n D (n + e.1) := sem_mem_exit1

theorem sem_bar_bar (e : ℕ × Bool) : sem_bar (sem_bar e) = e := by simp [sem_bar]

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
end SemCodes


theorem sem_hw_third : ∀ x a b : Fin 14, x ≠ a → x ≠ b → hc_adjB a b = false →
    ∃ y, hc_adjB x y = true ∧ hc_adjB y a = false ∧ hc_adjB y b = false := by decide +kernel

theorem sem_adjB_false {u v : Fin 14} : hc_adjB u v = false ↔ ¬ Adj u v := by
  rw [← hc_adjB_iff, Bool.not_eq_true]

/-- Heawood cover-freeness: for `x` different from nonadjacent `a`, `b` (possibly equal),
some position consuming `x` has an operand carrying neither. -/
theorem sem_hw_cover_free {D : Dag} (h : StrictLive 14 D) (hD : Correct D) {x a b : Fin 14}
    (hxa : x ≠ a) (hxb : x ≠ b) (hab : ¬ Adj a b) :
    ∃ e, e ∈ sem_W 14 D x ∧ a ∉ supp 14 D (src D e) ∧ b ∉ supp 14 D (src D e) := by
  obtain ⟨y, h1, h2, h3⟩ := sem_hw_third x a b hxa hxb (sem_adjB_false.mpr hab)
  exact sem_cover_free sem_heawood_gr h.1 (sem_heawood_comp hD) hab ((hc_adjB_iff x y).mp h1)
    (sem_adjB_false.mp h2) (sem_adjB_false.mp h3)

/-- The private-position lemma: if the code of `x` has at most two positions and contains
the position opposite the pure operand of an ineligible `i`, then it is that position
together with one position `Z` consuming no other label, at a gate assigned to no
ineligible label. -/
section SemArms

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

theorem sem_rtg_le (hS : Strict n D) {R : ℕ → ℕ → Prop} (hR : ∀ a b, R a b → sem_step n D a b)
    {a b : ℕ} (h : Relation.ReflTransGen R a b) : a ≤ b := by
  induction h with
  | refl => exact le_refl _
  | tail _ hbc ih => exact le_trans ih (le_of_lt (sem_step_lt hS (hR _ _ hbc)))

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
theorem sem_noempty_unique (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (hB0 : Bzero n D = 0) {i : Fin n} (hi : i ∈ ineligSet n D) {w : ℕ}
    (hp : Relation.ReflTransGen (sem_step n D) i.val w) : sem_Chain n D i.val w := by
  rcases sem_path_chain hp with h1 | ⟨b, h1, h2⟩
  · exact h1
  · have h3 := sem_bzero_branch h.1 hB0 h2
    rw [sem_branch_empty hG h.1 hC hi h1 h2] at h3
    exact absurd h3 Finset.not_nonempty_empty

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


/-- The side of the bipartition opposite to `i`. -/
def sem_hw_opp (i : Fin 14) : Finset (Fin 14) :=
  Finset.univ.filter (fun a => decide (a.val < 7) ≠ decide (i.val < 7))

/-- The neighbourhood of `i`. -/
def sem_hw_nb (i : Fin 14) : Finset (Fin 14) := Finset.univ.filter (fun a => Adj i a)

theorem sem_hw_sides : ∀ a b : Fin 14, hc_adjB a b = true →
    decide (a.val < 7) ≠ decide (b.val < 7) := by decide +kernel

theorem sem_hw_opp_indep (i : Fin 14) : ∀ a ∈ sem_hw_opp i, ∀ b ∈ sem_hw_opp i, ¬ Adj a b := by
  intro a ha b hb hab
  simp only [sem_hw_opp, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  have h1 := sem_hw_sides a b ((hc_adjB_iff a b).mpr hab)
  cases h2 : decide (a.val < 7) <;> cases h3 : decide (b.val < 7) <;>
    cases h4 : decide (i.val < 7) <;> simp_all

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


/-- Big merges, exits with operand mask of at least three labels, and admissible witness
costs are pairwise disjoint charges against `e_P + M_P`. -/
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

/-- Counting form: big merges and large-mask exits, doubled, plus two for every label of
`S` (singleton witness masks) and one for every other witnessed label, against twice
`e_P + M_P`. Take `S = ∅` when no singleton witness is known. -/
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

/-- Assigned exits: ineligible labels with at least three neighbours in `P` give distinct
boundary arcs of the carrier of `P` whose operand masks have at least three labels. -/
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

/-- Heawood: projected neighbourhoods of two distinct vertices share at most one label. -/
theorem sup_hw_inter (u v : Fin 14) (h : u ≠ v) (P : Finset (Fin 14)) :
    ((Finset.univ.filter (fun z => Adj u z) ∩ P) ∩
      (Finset.univ.filter (fun z => Adj v z) ∩ P)).card ≤ 1 := by
  refine le_trans (Finset.card_le_card (fun z hz => ?_)) (common_nbr_le_one u v h)
  simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hz
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ z, hz.1.1, hz.2.1⟩


/-- Boolean adjacency of the subdivided K4: original vertices 0..3, and the edge-vertices
4..9 for the pairs 01, 02, 03, 12, 13, 23. -/
def k4_adjB (u v : Fin 10) : Bool :=
  (([112, 400, 672, 832, 3, 5, 9, 6, 10, 12] : List ℕ).getD u.val 0).testBit v.val

/-- Adjacency of the subdivided K4. -/
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

/-- A system of assigned positions: for every ineligible label `i` an operand position of
a gate with empty support whose operand carries every neighbour of `i` and whose opposite
operand is `i`-pure; distinct ineligible labels get distinct positions. -/
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

/-- The assigned position of `i` is an exit of every union carrier meeting a neighbour. -/
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

/-- Flow budget of a union carrier: exits plus merges plus `p` is at most `2|T| + B_+`. -/
theorem k4_budget (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D) (b : Fin n → ℕ)
    (hb : PureBranch n D b) (T : Finset (Fin n)) :
    (exitArcs n D (carrierT n D T)).card + (merges n D (carrierT n D T)).card +
      (eligSet n D).card ≤ 2 * T.card + Bplus n D := by
  have h1 := carrier_flow_union h T (by rw [sem_supp_out hG hC, Finset.empty_inter])
  have h2 := surplus_carrierT_le h.1 b hb T
  have h3 := Finset.card_le_card (Finset.inter_subset_left : T ∩ eligSet n D ⊆ T)
  omega

/-- A projected mask with two labels is produced at an internal merge. -/
theorem k4_mask_gate (hS : Strict n D) (T : Finset (Fin n)) (w : ℕ)
    (h2 : 2 ≤ (supp n D w ∩ T).card) :
    ∃ j ∈ merges n D (carrierT n D T), supp n D (n + j) ∩ T = supp n D w ∩ T := by
  obtain ⟨j, -, -, h3, h4, -, -⟩ := sem_first_mask hS T _ h2 w rfl
  exact ⟨j, h4, h3⟩

/-- Two wires carrying two different pairs of a three-label set force two merges. -/
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

/-- A label with two ineligible neighbours and a third neighbour is consumed at three
positions. -/
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

/-- Flow for an arbitrary wire set below the output: exits plus merges equal roots plus
surplus, a root being an input or a gate without an operand in the set. -/
end K4Generic


theorem k4_indep_facts : ∀ I : Finset (Fin 10), (∀ u ∈ I, ∀ v ∈ I, k4_adjB u v = false) →
    5 ≤ I.card → (∀ q ∈ I, 4 ≤ q.val) ∧
      ((4 ∈ I ∧ 5 ∈ I) ∨ (4 ∈ I ∧ 7 ∈ I) ∨ (5 ∈ I ∧ 7 ∈ I)) := by decide +kernel

/-- Every vertex cover of size at most five contains the four original vertices. -/
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

/-- Every strict live circuit for the subdivided K4 has supported surplus at least six. -/
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

/-- Relabelling a circuit for a graph isomorphic to the subdivided K4. -/
def cof_ext {n m : ℕ} (ρ : Fin n → Option Bool) (ι : Fin m → Fin n) (y : Fin m → Bool) :
    Fin n → Bool :=
  fun v => (ρ v).getD (decide (∃ i : Fin m, ι i = v ∧ y i = true))

/-- `ι` lists the free inputs of `ρ` without repetition. -/
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

/-- Assignments of the free inputs differing only at `i` extend to assignments differing
only at `ι i`. -/
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

/-- A cofactor singleton is the assignment of its free input and of the inputs fixed to
true. -/
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

/-- The gate equation written with operand positions. -/
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

/-- Tag and operands of an appended gate. -/
theorem cof_snoc (E : Dag) (g : Bool × ℕ × ℕ) :
    opA (E ++ [g]) E.length = g.2.1 ∧ opB (E ++ [g]) E.length = g.2.2 ∧
      tag (E ++ [g]) E.length = g.1 ∧
      ∀ i, i < E.length → opA (E ++ [g]) i = opA E i ∧ opB (E ++ [g]) i = opB E i := by
  refine ⟨?_, ?_, ?_, fun i hi => ?_⟩
  · unfold opA; rw [na_getD_snoc]
  · unfold opB; rw [na_getD_snoc]
  · unfold tag; rw [na_getD_snoc]
  · unfold opA opB; rw [na_getD_append_lt E [g] i hi]; exact ⟨rfl, rfl⟩

/-- Values of a DAG with one appended gate. -/
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

/-- The wire is constant on the cofactor. -/
def cof_const (w : ℕ) : Prop :=
  ∀ y y' : Fin m → Bool, val D (cof_ext ρ ι y) w = val D (cof_ext ρ ι y') w

/-- Live on the cofactor: not constant, and joined to the output by reader steps into
non-constant wires. -/
def cof_live (w : ℕ) : Prop :=
  ¬ cof_const D ρ ι w ∧
    Relation.ReflTransGen (fun a b => sem_step n D a b ∧ ¬ cof_const D ρ ι b) w (outW n D)

/-- Number of live readers of a wire. -/
def cof_deg (w : ℕ) : ℕ := ((readers D w).filter (fun j => cof_live D ρ ι (n + j))).card

/-- Singleton support of a wire on the cofactor. -/
def cof_supp (w : ℕ) : Finset (Fin m) :=
  Finset.univ.filter (fun i => val D (cof_ext ρ ι (single i)) w = true)

/-- Reader surplus of the live part of the cofactor. -/
def cof_sur : ℕ := ∑ w ∈ (inner n D).filter (fun w => cof_live D ρ ι w), (cof_deg D ρ ι w - 1)

/-- Reader surplus of the live part on wires with nonempty cofactor support. -/
def cof_surP : ℕ :=
  ∑ w ∈ (inner n D).filter (fun w => cof_live D ρ ι w ∧ (cof_supp D ρ ι w).Nonempty),
    (cof_deg D ρ ι w - 1)

/-- The live wires of `D` translated to the wire `e`. -/
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

/-- A wire carrying a label fixed to true is constant on the cofactor. -/
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

/-- A free input on which the cofactor output depends is live. -/
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

/-- A live gate has a live operand. -/
theorem cof_live_op (hS : Strict n D) {j : ℕ} (hj : j < D.length)
    (hl : cof_live D ρ ι (n + j)) : ∃ s, cof_live D ρ ι (src D (j, s)) := by
  by_cases ha : cof_const D ρ ι (opA D j)
  · by_cases hb : cof_const D ρ ι (opB D j)
    · exact absurd (cof_gate_const hS hj ha hb) hl.1
    · exact ⟨true, cof_live_of_step (sem_step_src hj true) (by rw [sb_src_true]; exact hb) hl⟩
  · exact ⟨false, cof_live_of_step (sem_step_src hj false) (by rw [sb_src_false]; exact ha) hl⟩

/-- A non-constant gate with a constant operand equals its other operand on the cofactor. -/
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


/-- Translation invariant after `k` gates of `D`: `E` is a strict DAG on the free inputs,
`t` sends the live wires of `D` to wires of `E` with the same cofactor function, and `q`
sends every gate of `E` back to the live gate of `D` it was emitted for. A live gate that
emitted nothing shares its image with every live operand. -/
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

/-- Images do not decrease along a reader step between live wires. -/
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

/-- A live wire whose image is not the image of the output has its image read in `E`. -/
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

/-- Fibre count: the readers in `E` of a wire and the wires of its fibre are paid for by
the live readers of the fibre. -/
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

/-- Surplus of a set of non-output wires of `E` against the live wires of `D` mapped into
the set. -/
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

/-- Restriction theorem. If every free input is essential for the cofactor output, the
cofactor is computed by a strict live DAG on the free inputs whose total surplus, whose
supported surplus and whose ineligible inputs are controlled by the live part of `D`. -/
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


/-- Surplus units of `D` that survive on the cofactor: the wire is live and the unit index
is below the number of live readers. -/
def cof_kept (D : Dag) (ρ : Fin n → Option Bool) (ι : Fin m → Fin n) : Finset (Σ _ : ℕ, ℕ) :=
  (units n D).filter (fun u => cof_live D ρ ι u.1 ∧ u.2 + 1 < cof_deg D ρ ι u.1)

/-- Surviving units on wires with nonempty cofactor support. -/
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

/-- Units of `D` known not to survive are subtracted from the total surplus. -/
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


/-- Arm lemma. Let every wire of `K` be reached from `x` inside `K`, and let `b` be the only
wire of `K` with more than one reader. If the target of some exit arc of `K` is not live
on the cofactor, then some reader of `b` is not live. -/
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

/-- Every wire of a difference carrier is reached from its input inside the carrier. -/
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

/-- Difference-carrier depletion. Let the carrier of `x` without `c` have surplus one, borne
by a branching wire `b`, and let some exit arc of it enter a gate carrying `c`. If `c` is
fixed to true, at most one reader of `b` stays live, so the unit on `b` is lost. -/
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


/-- If every neighbour of a vertex fixed to true is fixed to false, the cofactor of the
edge function is the edge function of the graph induced on the free vertices. -/
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

/-- Restriction of a circuit for a graph edge function to an induced subgraph: vertices
fixed to false are deleted, and every neighbour of a vertex fixed to true is fixed to
false. -/
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

/-- Gates of `D` that are live on the cofactor and have two non-constant operands. -/
end CofCount


/-- Fix the side opposite to `i` to true and leave the side of `i` free. -/
section L3Gen

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

/-- Master count for a label set `P`: occurring triples cost two merges each, wide exits
one arc each, and every witnessed label one further unit of the flow of `P`. -/
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

/-- Branching wires with empty support are counted by `Bzero`. -/
theorem bz_card (hS : Strict n D) (Z : Finset ℕ)
    (hZ : ∀ b ∈ Z, 2 ≤ fanout D b ∧ supp n D b = ∅) : Z.card ≤ Bzero n D := by
  have hsub : Z ⊆ (inner n D).filter (fun w => ¬ (supp n D w).Nonempty) :=
    fun b hb => sem_bzero_mem hS (hZ b hb).1 (hZ b hb).2
  calc Z.card = ∑ _w ∈ Z, 1 := by simp
    _ ≤ ∑ w ∈ Z, (fanout D w - 1) :=
        Finset.sum_le_sum (fun w hw => by have := (hZ w hw).1; omega)
    _ ≤ Bzero n D := Finset.sum_le_sum_of_subset hsub

/-- Exits of a triple `T`: the assigned positions of `J` and one private exit per label. -/
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

/-- Budget form (easy half of the saturated-triangle lemma): a triple whose pairs `x y`
and `x z` are carried together, with `J` assigned exits and three private exits, needs
`J.card + 2` units beyond the triple. -/
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

/-- An ineligible input whose neighbourhood is not an exact mask on the independent set `P`
has a first empty branch of its own, so such inputs are counted by `Bzero`. -/
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

/-- Heawood count on a set `P` of eligible labels of the far side: `Oc` have occurring
neighbourhoods, the centres `Ct` have a short or missing mask, `I` are assigned exits. -/
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

/-- Tight surplus: no correct circuit has `B_+ = p` with the point `0` ineligible. -/
def mx_L : Finset (Fin 14) := {7, 8, 9, 10, 12, 13}

/-- Independent sets exposing the three lines through the point `0`. -/
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

/-- Ineligible cap points `0, 1, 2, 5`: the three lines through `0` need three units
beyond the reserved ones (seven exits, two merges). -/
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

/-- The mixed case `p = 9`: four cap points and their line. -/
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

/-- Triangle count with occurring masks: `J` assigned exits, one private exit per label of
`T`, and one merge per occurring mask of `F`. -/
end L3bGen

section L3bTri

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

/-- Equality case of the triangle count. When the budget is exhausted by `J` assigned exits,
three private exits and the pair masks `F`: no wire carries all of `T`, the labels of `T`
have no carrier merge, each has at most one consumption outside the assigned positions of
`J`, and every residual unit meets `T`. -/
end L3bTri


/-- The graph relation in the form used by the generic lemmas. -/
abbrev HG : Fin 14 → Fin 14 → Prop := fun u v => Adj u v

/-- Residual units carrying the label `x`. -/
def ru (D : Dag) (b : Fin 14 → ℕ) (x : Fin 14) : Finset (Σ _ : ℕ, ℕ) :=
  (residualUnits 14 D b).filter (fun u => x ∈ supp 14 D u.1)

theorem mem_ru {D : Dag} {b : Fin 14 → ℕ} {x : Fin 14} {u : Σ _ : ℕ, ℕ} :
    u ∈ ru D b x ↔ u ∈ residualUnits 14 D b ∧ x ∈ supp 14 D u.1 := Finset.mem_filter

/-- A residual unit sits on a branching wire, so its labels are eligible. -/
theorem res_fan {n : ℕ} {D : Dag} {b : Fin n → ℕ} {u : Σ _ : ℕ, ℕ}
    (hu : u ∈ residualUnits n D b) : 2 ≤ fanout D u.1 := by
  have := (mem_units.mp (Finset.mem_filter.mp (Finset.mem_sdiff.mp hu).1).1).2
  omega

theorem res_elig {n : ℕ} {D : Dag} {b : Fin n → ℕ} {u : Σ _ : ℕ, ℕ}
    (hu : u ∈ residualUnits n D b) {x : Fin n} (hx : x ∈ supp n D u.1) : x ∈ eligSet n D :=
  mem_eligSet.2 ⟨u.1, res_fan hu, hx⟩

/-- Code count: `|W_x| + M_x = 2 +` residual units on `x` for eligible `x`, with `≤` always. -/
theorem cc_le {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (b : Fin 14 → ℕ)
    (hb : PureBranch 14 D b) (x : Fin 14) :
    (sem_W 14 D x).card + (merges 14 D (carrierT 14 D {x})).card ≤ 2 + (ru D b x).card := by
  have h1 := sem_code_count sem_heawood_gr h (sem_heawood_comp hD) b hb x
  have h2 := Finset.card_le_card
    (Finset.inter_subset_left : ({x} : Finset (Fin 14)) ∩ eligSet 14 D ⊆ {x})
  rw [Finset.card_singleton] at h2
  unfold ru
  omega

section Assigned

variable {D : Dag} {pos : Fin 14 → ℕ × Bool}

/-- The assigned position of an ineligible `i` consumes every neighbour of `i`. -/
theorem as_mem (hpos : k4_Pos 14 HG D pos) {i a : Fin 14} (hi : i ∈ ineligSet 14 D)
    (hia : Adj i a) : pos i ∈ sem_W 14 D a := by
  obtain ⟨h1, h2, h4, -⟩ := hpos.1 i hi
  exact sem_mem_W.2 ⟨h1, h4 a hia, by rw [h2]; exact Finset.notMem_empty a⟩

/-- The position opposite the assigned one is private to `i`. -/
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

/-- Private slot in terms of the assigned position. -/
theorem full (h : StrictLive 14 D) (hD : Correct D) (hB0 : Bzero 14 D = 0)
    (hpos : k4_Pos 14 HG D pos) {i v : Fin 14} (hi : i ∈ ineligSet 14 D) (hiv : Adj i v)
    (hv : ∀ p ∈ sem_W 14 D v, p.1 ≠ (pos i).1 → ¬ supp 14 D (src D (sem_bar p)) ⊆ {i}) :
    ∀ t, t ∈ supp 14 D (src D (pos i)) ↔ Adj i t := by
  have := full_gen sem_heawood_gr h (sem_heawood_comp hD) hB0 hi (as_W h hD hpos hi) hiv hv
  rwa [sem_bar_bar] at this

end Assigned

/-- With no empty branch an ineligible input reaches no branching wire. -/
def cf_rho (c v : Fin 14) : Option Bool :=
  if v = c then some true else if hc_adjB c v = true then some false else none

/-- The ten free labels, listed in the order of the vertices of the subdivided K4. -/
def cf_iota (l : List ℕ) (k : Fin 10) : Fin 14 := Fin.ofNat 14 (l.getD k.val 0)

/-- The list is a bijection onto the free labels carrying the induced graph to `k4_Adj`. -/
abbrev cf_good (c : Fin 14) (l : List ℕ) : Prop :=
  (∀ a b : Fin 10, cf_iota l a = cf_iota l b → a = b) ∧
  (∀ v : Fin 14, cf_rho c v = none ↔ ∃ i : Fin 10, cf_iota l i = v) ∧
  ∀ u v : Fin 10, hc_adjB (cf_iota l u) (cf_iota l v) = k4_adjB u v

/-- Free labels after fixing the line `7`: points `2, 4, 5, 6`, then the six other lines. -/
def cfL3 : List ℕ := [8, 9, 10, 13, 6, 0, 2, 5, 1, 4]

theorem cf3_good : cf_good 3 cfL3 := by decide +kernel

/-- Restriction to the subdivided K4. Fixing `c` to true loses the residual units on `c`,
the reserved unit of `c`, and the reserved unit of every `x` of `X` (all of whose residual
units carry `c`, and which is carried together with `c` somewhere). -/
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

/-- Six-unit form: the cofactor needs supported surplus six. -/
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
end PEqualNP.Outside.L_meta_6659_aux

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace PEqualNP.Outside.L_meta_6659_aux

theorem ke_as_mem {D : Dag} {pos : Fin 10 → ℕ × Bool} (hpos : k4_Pos 10 k4_Adj D pos) {i a : Fin 10} (hi : i ∈ ineligSet 10 D)
    (hia : k4_Adj i a) : pos i ∈ sem_W 10 D a := by
  obtain ⟨h1, h2, h4, -⟩ := hpos.1 i hi
  exact sem_mem_W.2 ⟨h1, h4 a hia, by rw [h2]; exact Finset.notMem_empty a⟩

/-- The position opposite the assigned one is private to `i`. -/
theorem ke_as_priv {D : Dag} {pos : Fin 10 → ℕ × Bool} (hpos : k4_Pos 10 k4_Adj D pos) {i t : Fin 10} (hi : i ∈ ineligSet 10 D)
    (ht : sem_bar (pos i) ∈ sem_W 10 D t) : t = i := by
  have := (sem_mem_W.1 ht).2.1
  rw [show src D (sem_bar (pos i)) = src D ((pos i).1, !(pos i).2) from rfl,
    (hpos.1 i hi).2.2.2] at this
  exact Finset.mem_singleton.1 this

theorem ke_as_W {D : Dag} {pos : Fin 10 → ℕ × Bool} (h : StrictLive 10 D) (hD : sem_Comp 10 k4_Adj D) (hpos : k4_Pos 10 k4_Adj D pos) {i : Fin 10}
    (hi : i ∈ ineligSet 10 D) : sem_W 10 D i = {sem_bar (pos i)} := by
  obtain ⟨e, -, -, h3, -, -, h6, -⟩ :=
    sem_inelig_consumer k4_gr h hD hi
  obtain ⟨h1, h2, -, h5⟩ := hpos.1 i hi
  have hm : sem_bar (pos i) ∈ sem_W 10 D i :=
    sem_mem_W.2 ⟨h1, by
      rw [show src D (sem_bar (pos i)) = src D ((pos i).1, !(pos i).2) from rfl, h5]
      exact Finset.mem_singleton_self i, by
      rw [show (sem_bar (pos i)).1 = (pos i).1 from rfl, h2]; exact Finset.notMem_empty i⟩
  have h7 : sem_W 10 D i = {e} := h6
  rw [h7] at hm ⊢
  rw [Finset.mem_singleton.1 hm]

theorem ke_residual_co_label {D : Dag} (h : StrictLive 10 D) (hD : sem_Comp 10 k4_Adj D)
    (b : Fin 10 → ℕ) (hb : PureBranch 10 D b) (pos : Fin 10 → ℕ × Bool)
    (hpos : k4_Pos 10 k4_Adj D pos) {x t i : Fin 10}
    (hx : x ∈ eligSet 10 D) (ht : t ∈ eligSet 10 D) (hi : i ∈ ineligSet 10 D)
    (hix : k4_Adj i x) (hx4 : x.val < 4) (ht4 : t.val < 4)
    (inclusion : ∀ u ∈ residualUnits 10 D b, x ∈ supp 10 D u.1 → t ∈ supp 10 D u.1)
    (shared : ∃ w, x ∈ supp 10 D w ∧ t ∈ supp 10 D w) :
    t ∈ supp 10 D (src D (pos i)) := by
  by_cases hxt : x = t
  · exact hxt ▸ (hpos.1 i hi).2.2.1 x hix
  obtain ⟨w,hw⟩ := shared
  obtain ⟨e0,he0⟩ := ri_gen k4_gr h hD b hb hxt hx inclusion hw
  have hti : t ≠ i := fun equal => sem_mem_inelig.1 hi (equal ▸ ht)
  have hgeo : ∀ i x t : Fin 10, k4_adjB i x = true → x.val < 4 → t.val < 4 →
      t ≠ x → ∃ q, k4_adjB i q = true ∧ q ≠ x ∧ k4_adjB t q = false := by decide +kernel
  obtain ⟨q,hiq,hqx,htq⟩ := hgeo i x t hix hx4 ht4 (Ne.symm hxt)
  have hiq' : k4_Adj i q := hiq
  have htq' : ¬ k4_Adj t q := by simpa only [k4_Adj,htq] using Bool.false_ne_true
  by_contra hnot
  have heq : pos i = e0 := by
    by_contra hne
    exact hnot (he0 _ (ke_as_mem hpos hi hix) hne)
  have hfree : ∀ x t q : Fin 10, x.val < 4 → t.val < 4 → q.val < 4 → x ≠ t → x ≠ q →
      ∃ y, k4_Adj x y ∧ ¬ k4_Adj y t ∧ ¬ k4_Adj y q := by decide +kernel
  have hq4 : q.val < 4 := by
    have hgeo : ∀ i x q : Fin 10, k4_adjB i x = true → x.val < 4 → k4_adjB i q = true → q.val < 4 := by decide +kernel
    exact hgeo i x q hix hx4 hiq
  obtain ⟨y,hxy,hyt,hyq⟩ := hfree x t q hx4 ht4 hq4 hxt (Ne.symm hqx)
  obtain ⟨e,he,hnt,hnq⟩ := sem_cover_free k4_gr h.1 hD htq' hxy hyt hyq
  exact hnt (he0 e he (fun equal => hnq (by
    rw [equal,← heq]
    exact (hpos.1 i hi).2.2.1 q hiq')))

theorem ke_cc_le {D : Dag} (h : StrictLive 10 D) (hD : sem_Comp 10 k4_Adj D)
    (b : Fin 10 → ℕ) (hb : PureBranch 10 D b) (x : Fin 10) :
    (sem_W 10 D x).card ≤ 2 +
      ((residualUnits 10 D b).filter (fun u => x ∈ supp 10 D u.1)).card := by
  have h1 := sem_code_count k4_gr h hD b hb x
  have h2 := Finset.card_le_card
    (Finset.inter_subset_left : ({x} : Finset (Fin 10)) ∩ eligSet 10 D ⊆ {x})
  rw [Finset.card_singleton] at h2
  omega

abbrev ke_many (I : Finset (Fin 10)) (x : Fin 10) : Prop :=
  2 ≤ (I.filter (fun i => k4_Adj i x)).card

theorem ke_neighbor_pair {I : Finset (Fin 10)} {x i : Fin 10}
    (hm : ke_many I x) (hi : i ∈ I) (hix : k4_Adj i x) :
    ∃ j ∈ I, j ≠ i ∧ k4_Adj j x := by
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp (by exact hm)
  obtain ⟨haI,hax⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbI,hbx⟩ := Finset.mem_filter.mp hb
  by_cases hai : a = i
  · exact ⟨b,hbI,by simpa only [hai] using Ne.symm hab,hbx⟩
  · exact ⟨a,haI,hai,hax⟩

theorem ke_two_neighbors_three {D : Dag} (h : StrictLive 10 D) (hD : sem_Comp 10 k4_Adj D)
    (pos : Fin 10 → ℕ × Bool) (hpos : k4_Pos 10 k4_Adj D pos) {x : Fin 10}
    (hx4 : x.val < 4) (hm : ke_many (ineligSet 10 D) x) :
    3 ≤ (sem_W 10 D x).card := by
  obtain ⟨i,hi,j,hj,hij⟩ := Finset.one_lt_card.mp (by exact hm)
  obtain ⟨hiI,hix⟩ := Finset.mem_filter.mp hi
  obtain ⟨hjI,hjx⟩ := Finset.mem_filter.mp hj
  have hgeo : ∀ x i j : Fin 10, x.val < 4 → k4_Adj i x → k4_Adj j x → i ≠ j →
      ∃ z, k4_Adj x z ∧ z ≠ i ∧ z ≠ j := by decide +kernel
  obtain ⟨z,hxz,hzi,hzj⟩ := hgeo x i j hx4 hix hjx hij
  exact k4_three_cons k4_gr h hD hpos hiI hjI hij (Ne.symm hzi) (Ne.symm hzj)
    (k4_gr.1 _ _ hix) (k4_gr.1 _ _ hjx) hxz

theorem ke_p7_geometry : ∀ I : Finset (Fin 10),
    (∀ u ∈ I, ∀ v ∈ I, k4_adjB u v = false) → I.card = 3 →
    3 ≤ (({0,1,2,3} : Finset (Fin 10)) \ I).card →
    ∃ x : Fin 10, x.val < 4 ∧ ke_many I x := by decide +kernel

end PEqualNP.Outside.L_meta_6659_aux


namespace PEqualNP.Outside.L_meta_6659_aux

theorem ke_p4_mask_certificate : ∀ M : Fin 4 → Finset (Fin 3),
    (∀ x, (M x).Nonempty) →
    ∃ t : Fin 4, 2 + (M t).card <
      (Finset.univ.filter (fun e : Fin 6 =>
        ∃ x : Fin 4,
          k4_Adj (Fin.castLE (by decide : 4 ≤ 10) x) (Fin.natAdd 4 e) ∧
          M x ⊆ M t)).card := by
  decide +kernel

theorem ke_p5_mask_certificate : ∀ omitted : Fin 6,
    ∀ M : Fin 4 → Finset (Fin 3),
    (∀ x, (M x).Nonempty) →
    (Finset.univ.biUnion M).card ≤ 2 →
    ∃ t : Fin 4, 2 + (M t).card <
      (Finset.univ.filter (fun e : Fin 6 =>
        e ≠ omitted ∧ ∃ x : Fin 4,
          k4_Adj (Fin.castLE (by decide : 4 ≤ 10) x) (Fin.natAdd 4 e) ∧
          M x ⊆ M t)).card := by
  decide +kernel

end PEqualNP.Outside.L_meta_6659_aux


namespace PEqualNP.Outside.L_meta_6659_aux

theorem ke_embedding_three (R : Finset (Σ _ : ℕ, ℕ)) (hR : R.card ≤ 3) :
    ∃ f : (Σ _ : ℕ, ℕ) → Fin 3, Set.InjOn f (R : Set _) := by
  classical
  let e : (↑R) ≃ Fin R.card := Fintype.equivFinOfCardEq (by rw [Fintype.card_coe])
  let f : (Σ _ : ℕ, ℕ) → Fin 3 := fun u => if hu : u ∈ R then
    ⟨(e ⟨u,hu⟩).val,lt_of_lt_of_le (e ⟨u,hu⟩).isLt hR⟩ else 0
  refine ⟨f,?_⟩
  intro u hu v hv equal
  change u ∈ R at hu
  change v ∈ R at hv
  have fu : f u = ⟨(e ⟨u,hu⟩).val,lt_of_lt_of_le (e ⟨u,hu⟩).isLt hR⟩ := by simp [f,hu]
  have fv : f v = ⟨(e ⟨v,hv⟩).val,lt_of_lt_of_le (e ⟨v,hv⟩).isLt hR⟩ := by simp [f,hv]
  have val := congrArg Fin.val (fu.symm.trans (equal.trans fv))
  exact congrArg Subtype.val (e.injective (Fin.ext val))

theorem ke_assigned_bound {D : Dag} (h : StrictLive 10 D) (hD : sem_Comp 10 k4_Adj D)
    (b : Fin 10 → ℕ) (hb : PureBranch 10 D b) (pos : Fin 10 → ℕ × Bool)
    (hpos : k4_Pos 10 k4_Adj D pos) (J : Finset (Fin 6)) {t : Fin 10}
    (hJ : ∀ i ∈ J, Fin.natAdd 4 i ∈ ineligSet 10 D ∧
      t ∈ supp 10 D (src D (pos (Fin.natAdd 4 i)))) :
    J.card ≤ 2 + ((residualUnits 10 D b).filter (fun u => t ∈ supp 10 D u.1)).card := by
  classical
  have hinj : Set.InjOn (fun i : Fin 6 => pos (Fin.natAdd 4 i)) (J : Set _) := by
    intro i hi j hj equal
    have he := hpos.2 _ (hJ i hi).1 _ (hJ j hj).1 equal
    apply Fin.ext
    have hv := congrArg Fin.val he
    simpa using hv
  have sub : J.image (fun i => pos (Fin.natAdd 4 i)) ⊆ sem_W 10 D t := by
    intro e he
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp he
    exact sem_mem_W.mpr ⟨(hpos.1 _ (hJ i hi).1).1,(hJ i hi).2,by
      rw [(hpos.1 _ (hJ i hi).1).2.1]
      exact Finset.notMem_empty t⟩
  have lower := Finset.card_le_card sub
  rw [Finset.card_image_of_injOn hinj] at lower
  have upper := ke_cc_le h hD b hb t
  omega

theorem ke_coordinate_budget {D : Dag} (h : StrictLive 10 D) (hD : sem_Comp 10 k4_Adj D)
    (b : Fin 10 → ℕ) (hb : PureBranch 10 D b) (pos : Fin 10 → ℕ × Bool)
    (hpos : k4_Pos 10 k4_Adj D pos) (hR : (residualUnits 10 D b).card ≤ 3)
    (hW : ∀ x : Fin 4, 3 ≤ (sem_W 10 D (Fin.castLE (by decide : 4 ≤ 10) x)).card)
    (J : Finset (Fin 6)) (hJ : ∀ i ∈ J, Fin.natAdd 4 i ∈ ineligSet 10 D) :
    ∃ M : Fin 4 → Finset (Fin 3),
      (∀ x, (M x).Nonempty) ∧ (Finset.univ.biUnion M).card ≤ (residualUnits 10 D b).card ∧
      ∀ t : Fin 4, (J.filter (fun i => ∃ x : Fin 4,
        k4_Adj (Fin.castLE (by decide : 4 ≤ 10) x) (Fin.natAdd 4 i) ∧ M x ⊆ M t)).card ≤
        2 + (M t).card := by
  classical
  let R := residualUnits 10 D b
  obtain ⟨f,hinj⟩ := ke_embedding_three R hR
  let A : Fin 4 → Finset (Σ _ : ℕ, ℕ) := fun x =>
    R.filter (fun u => (Fin.castLE (by decide : 4 ≤ 10) x) ∈ supp 10 D u.1)
  let M : Fin 4 → Finset (Fin 3) := fun x => (A x).image f
  have asub (x) : A x ⊆ R := Finset.filter_subset _ _
  have card (x) : (M x).card = (A x).card := Finset.card_image_of_injOn (hinj.mono (asub x))
  have positive (x) : (A x).Nonempty := by
    apply Finset.card_pos.mp
    have c := ke_cc_le h hD b hb (Fin.castLE (by decide : 4 ≤ 10) x)
    have w := hW x
    have hp : 0 < ((residualUnits 10 D b).filter
        (fun u => (Fin.castLE (by decide : 4 ≤ 10) x) ∈ supp 10 D u.1)).card := by omega
    exact hp
  refine ⟨M,fun x => (positive x).image f,?_,?_⟩
  · have sub : Finset.univ.biUnion M ⊆ R.image f := by
      intro y hy
      obtain ⟨x,_,hy⟩ := Finset.mem_biUnion.mp hy
      exact Finset.image_subset_image (asub x) hy
    have hc := Finset.card_le_card sub
    rw [Finset.card_image_of_injOn hinj] at hc
    exact hc
  · intro t
    rw [card t]
    apply ke_assigned_bound h hD b hb pos hpos
    intro i hi
    obtain ⟨hiJ,x,hxi,hsub⟩ := Finset.mem_filter.mp hi
    have hii := hJ i hiJ
    have inclusion : ∀ u ∈ R, (Fin.castLE (by decide : 4 ≤ 10) x) ∈ supp 10 D u.1 →
        (Fin.castLE (by decide : 4 ≤ 10) t) ∈ supp 10 D u.1 := by
      intro u hu hx
      have hm : f u ∈ M x := Finset.mem_image.mpr ⟨u,Finset.mem_filter.mpr ⟨hu,hx⟩,rfl⟩
      obtain ⟨v,hv,hvu⟩ := Finset.mem_image.mp (hsub hm)
      have vu : v = u := hinj (asub t hv) hu hvu
      exact vu ▸ (Finset.mem_filter.mp hv).2
    obtain ⟨u,hu⟩ := positive x
    obtain ⟨huR,hux⟩ := Finset.mem_filter.mp hu
    have hut := inclusion u huR hux
    refine ⟨hii,?_⟩
    exact ke_residual_co_label h hD b hb pos hpos (res_elig huR hux) (res_elig huR hut)
      hii (k4_gr.1 _ _ hxi) x.isLt t.isLt inclusion ⟨u.1,hux,hut⟩

end PEqualNP.Outside.L_meta_6659_aux


namespace PEqualNP.Outside.L_meta_6659_aux

theorem ke_low_cover_geometry : ∀ S : Finset (Fin 10),
    (∀ u v : Fin 10, k4_Adj u v → u ∈ S ∨ v ∈ S) → S.card ≤ 5 →
    S = {0,1,2,3} ∨ ∃ omitted : Fin 6, S = insert (Fin.natAdd 4 omitted) {0,1,2,3} := by
  decide +kernel

theorem ke_large_edge_family_many {D : Dag} (J : Finset (Fin 6)) (hJ : 5 ≤ J.card)
    (hin : ∀ i ∈ J, Fin.natAdd 4 i ∈ ineligSet 10 D) (x : Fin 4) :
    ke_many (ineligSet 10 D) (Fin.castLE (by decide : 4 ≤ 10) x) := by
  have geo : ∀ J : Finset (Fin 6), 5 ≤ J.card → ∀ x : Fin 4,
      ∃ i ∈ J, ∃ j ∈ J, i ≠ j ∧
        k4_Adj (Fin.natAdd 4 i) (Fin.castLE (by decide : 4 ≤ 10) x) ∧
        k4_Adj (Fin.natAdd 4 j) (Fin.castLE (by decide : 4 ≤ 10) x) := by decide +kernel
  obtain ⟨i,hi,j,hj,hij,hix,hjx⟩ := geo J hJ x
  apply Finset.one_lt_card.mpr
  refine ⟨Fin.natAdd 4 i,Finset.mem_filter.mpr ⟨hin i hi,hix⟩,
    Fin.natAdd 4 j,Finset.mem_filter.mpr ⟨hin j hj,hjx⟩,?_⟩
  intro equal
  apply hij
  apply Fin.ext
  have hv := congrArg Fin.val equal
  simpa using hv

end PEqualNP.Outside.L_meta_6659_aux


namespace PEqualNP.Outside.L_meta_6659_aux

section CofMulti
variable {n m : ℕ} {D : Dag} {ρ : Fin n → Option Bool} {ι : Fin m → Fin n}

theorem equality_cof_slack_set {E : Dag} {t q : ℕ → ℕ}
    (hS : Strict n D) (hok : cof_Ok ρ ι)
    (hI : cof_Inv D ρ ι D.length E t q)
    (hout : t (outW n D) = outW m E)
    (V : Finset ℕ)
    (hV : ∀ w ∈ V, w ∈ inner n D ∧ cof_live D ρ ι w ∧
      2 ≤ cof_deg D ρ ι w ∧ fanout E (t w) ≤ 1) :
    totalSurplus m E + V.card ≤ cof_sur D ρ ι := by
  classical
  let T := (inner m E).filter (fun e => 2 ≤ fanout E e)
  let S := (inner n D).filter (fun w => cof_live D ρ ι w)
  let A := (inner n D).filter (fun w => cof_live D ρ ι w ∧ t w ∈ T)
  have hT : T ⊆ inner m E := Finset.filter_subset _ _
  have htotal : totalSurplus m E = surplusOn E T := by
    symm
    apply Finset.sum_subset hT
    intro e he hnot
    have hf : ¬ 2 ≤ fanout E e := by
      intro hf
      exact hnot (Finset.mem_filter.mpr ⟨he,hf⟩)
    omega
  have hVS : V ⊆ S := by
    intro w hw
    exact Finset.mem_filter.mpr ⟨(hV w hw).1,(hV w hw).2.1⟩
  have hAS : A ⊆ S \ V := by
    intro w hw
    obtain ⟨hwinner,hwlive,hwt⟩ := Finset.mem_filter.mp hw
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨hwinner,hwlive⟩,?_⟩
    intro hwV
    have h1 := (hV w hwV).2.2.2
    have h2 := (Finset.mem_filter.mp hwt).2
    omega
  have hcore := cof_core hS hok hI hout T hT
  have hsum : (∑ w ∈ A, (cof_deg D ρ ι w - 1)) ≤
      ∑ w ∈ S \ V, (cof_deg D ρ ι w - 1) := Finset.sum_le_sum_of_subset hAS
  have hcard : V.card ≤ ∑ w ∈ V, (cof_deg D ρ ι w - 1) := by
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_le_sum
    intro w hw
    have := (hV w hw).2.2.1
    omega
  have hsplit := Finset.sum_sdiff (f := fun w => cof_deg D ρ ι w - 1) hVS
  change surplusOn E T ≤ ∑ w ∈ A, (cof_deg D ρ ι w - 1) at hcore
  change (∑ w ∈ S \ V, (cof_deg D ρ ι w - 1)) +
      (∑ w ∈ V, (cof_deg D ρ ι w - 1)) = cof_sur D ρ ι at hsplit
  omega

theorem equality_cof_slack_units {E : Dag} {t q : ℕ → ℕ}
    (hS : Strict n D) (hok : cof_Ok ρ ι)
    (hI : cof_Inv D ρ ι D.length E t q)
    (hout : t (outW n D) = outW m E)
    (U : Finset (Σ _ : ℕ, ℕ)) (hU : U ⊆ cof_kept D ρ ι)
    (hinj : Set.InjOn (fun u : Σ _ : ℕ, ℕ => u.1) (U : Set _))
    (hbad : ∀ u ∈ U, ∃ i ∈ cof_supp D ρ ι u.1, i ∈ ineligSet m E) :
    totalSurplus m E + U.card ≤ cof_sur D ρ ι := by
  classical
  have hc := Finset.card_image_of_injOn hinj
  rw [← hc]
  apply equality_cof_slack_set hS hok hI hout
  intro w hw
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hw
  obtain ⟨hunit,hlive,hdeg⟩ := cof_mem_kept.mp (hU hu)
  obtain ⟨i,hisupp,hi⟩ := hbad u hu
  refine ⟨(mem_units.mp hunit).1,hlive,by omega,?_⟩
  apply (mem_ineligSet.mp hi) (t u.1)
  rw [mem_supp, (hI.2.1 u.1 (cof_live_lt hlive) hlive).2]
  exact cof_mem_supp.mp hisupp

end CofMulti
end PEqualNP.Outside.L_meta_6659_aux


namespace PEqualNP.Outside.L_meta_6659_aux

theorem ke_reachable_chain {n : ℕ} {D : Dag} {i w : ℕ}
    (hprotected : ∀ u, Relation.ReflTransGen (sem_step n D) i u → fanout D u ≤ 1)
    (path : Relation.ReflTransGen (sem_step n D) i w) : sem_Chain n D i w := by
  induction path with
  | refl => exact Relation.ReflTransGen.refl
  | @tail a c prior step ih =>
    have one : fanout D a = 1 := by
      have := hprotected a prior
      have := sem_step_fanout step
      omega
    exact Relation.ReflTransGen.tail ih ⟨step,one⟩

theorem ke_full_gen_protected {D : Dag} (h : StrictLive 10 D) (hD : sem_Comp 10 k4_Adj D)
    {i v : Fin 10} (hi : i ∈ ineligSet 10 D) {e : ℕ × Bool}
    (he : sem_W 10 D i = {e}) (hiv : k4_Adj i v)
    (hprotected : ∀ w, Relation.ReflTransGen (sem_step 10 D) i.val w → fanout D w ≤ 1)
    (hv : ∀ p ∈ sem_W 10 D v, p.1 ≠ e.1 → ¬ supp 10 D (src D (sem_bar p)) ⊆ {i}) :
    ∀ t, t ∈ supp 10 D (src D (sem_bar e)) ↔ k4_Adj i t := by
  have hG := k4_gr
  have hC := hD
  have hS := h.1
  refine sem_full_support hG h hC hi he (fun j hreach hj => ?_)
  by_contra ht
  rw [Bool.not_eq_false] at ht
  rcases Relation.ReflTransGen.cases_tail hreach with heq | ⟨w, hw1, hw2⟩
  · exact hj (by omega)
  · obtain ⟨j', s, hj', hjeq, hsrc⟩ := sem_step_iff.1 hw2
    have hjj : j' = j := by omega
    subst hjj
    have hew : e ∈ sem_W 10 D i := by rw [he]; exact Finset.mem_singleton_self e
    obtain ⟨he1, he2, -⟩ := sem_mem_W.1 hew
    have hreach2 : Relation.ReflTransGen (sem_step 10 D) i.val w :=
      ((sem_rtg_mono (fun _ _ hab => hab.1) (sem_inelig_chain hS hi he2)).tail
        (sem_step_src he1 e.2)).trans hw1
    have hch := ke_reachable_chain hprotected hreach2
    have hf : fanout D w = 1 := by
      have := hprotected w hreach2
      have := sem_step_fanout hw2
      omega
    have hsub : supp 10 D w ⊆ {i} := sem_dom_pure hG hS hC i w (sem_chain_dom hS hch)
    have hvi : v ≠ i := fun hvi => hG.2.1 i (hvi ▸ hiv)
    have hw' : src D (j', !(!s)) = w := by rw [Bool.not_not]; exact hsrc
    have hmem : v ∈ supp 10 D (src D (j', !s)) :=
      sem_and_sibling_nbrs hG hS hC hj' (!s) ht (hw' ▸ hch) (hw' ▸ hf)
        (by unfold outW; omega) hiv
    have hp : ((j', !s) : ℕ × Bool) ∈ sem_W 10 D v :=
      sem_mem_W.2 ⟨hj', hmem, fun hc => by
        have := hsub (hsrc ▸ sem_supp_and_sub hS hj' ht s hc)
        exact hvi (Finset.mem_singleton.1 this)⟩
    exact hv _ hp hj (by rw [show sem_bar (j', !s) = (j', !(!s)) from rfl, hw']; exact hsub)

theorem ke_three_slot_protected {D : Dag} (h : StrictLive 10 D) (hD : sem_Comp 10 k4_Adj D)
    (pos : Fin 10 → ℕ × Bool)
    (hpos : k4_Pos 10 k4_Adj D pos) {x i j z : Fin 10}
    (hi : i ∈ ineligSet 10 D) (hj : j ∈ ineligSet 10 D)
    (hij : i ≠ j) (hix : k4_Adj i x) (hjx : k4_Adj j x) (hxz : k4_Adj x z)
    (hzi : z ≠ i) (hzj : z ≠ j) (small : (sem_W 10 D x).card ≤ 3)
    (hprotected : ∀ w, Relation.ReflTransGen (sem_step 10 D) i.val w → fanout D w ≤ 1) :
    ∀ t, t ∈ supp 10 D (src D (pos i)) ↔ k4_Adj i t := by
  classical
  obtain ⟨H,hHx,hHz,_,_,_⟩ := sem_edge_slots k4_gr h.1 hD hxz
  have ai := ke_as_mem hpos hi hix
  have aj := ke_as_mem hpos hj hjx
  have ni : H ≠ pos i := fun equal => hzi (ke_as_priv hpos hi (equal ▸ hHz))
  have nj : H ≠ pos j := fun equal => hzj (ke_as_priv hpos hj (equal ▸ hHz))
  have nij : pos i ≠ pos j := fun equal => hij (hpos.2 i hi j hj equal)
  have code : sem_W 10 D x = {pos i,pos j,H} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro e he
      simp only [Finset.mem_insert,Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl <;> assumption
    · rw [Finset.card_insert_of_notMem (by simp [nij,Ne.symm ni]),
        Finset.card_pair (Ne.symm nj)]
      exact small
  have full := ke_full_gen_protected h hD hi (ke_as_W h hD hpos hi) hix hprotected
    (fun p hp hne hsub => by
      rw [code] at hp
      simp only [Finset.mem_insert,Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl
      · exact hne rfl
      · have hjmem : j ∈ supp 10 D (src D (sem_bar (pos j))) := by
          rw [show src D (sem_bar (pos j)) = src D ((pos j).1,!(pos j).2) from rfl,
            (hpos.1 j hj).2.2.2]
          exact Finset.mem_singleton_self j
        exact hij (Finset.mem_singleton.1 (hsub hjmem)).symm
      · exact hzi (Finset.mem_singleton.1 (hsub (sem_mem_W.1 hHz).2.1)))
  simpa only [sem_bar_bar] using full


theorem ke_p6_protected_obstruction {D : Dag} (h : StrictLive 10 D) (hD : sem_Comp 10 k4_Adj D)
    (hB : Bplus 10 D ≤ 7) (hp : (eligSet 10 D).card = 6)
    {x t i : Fin 10} (hx4 : x.val < 4) (ht4 : t.val < 4)
    (hxm : ke_many (ineligSet 10 D) x) (htm : ke_many (ineligSet 10 D) t)
    (hi : i ∈ ineligSet 10 D) (hix : k4_Adj i x) (hit : ¬ k4_Adj i t)
    (hprotected : ∀ w, Relation.ReflTransGen (sem_step 10 D) i.val w → fanout D w ≤ 1) : False := by
  classical
  obtain ⟨b,hb⟩ := sem_exists_pureBranch k4_gr h.1 hD
  obtain ⟨pos,hpos⟩ := k4_assigned k4_gr h hD
  have wx := ke_two_neighbors_three h hD pos hpos hx4 hxm
  have wt := ke_two_neighbors_three h hD pos hpos ht4 htm
  have cx := ke_cc_le h hD b hb x
  have ct := ke_cc_le h hD b hb t
  have cr := card_residual h.1 b hb
  have hsubx : ((residualUnits 10 D b).filter (fun u => x ∈ supp 10 D u.1)).card ≤
      (residualUnits 10 D b).card := Finset.card_le_card (Finset.filter_subset _ _)
  have hsubt : ((residualUnits 10 D b).filter (fun u => t ∈ supp 10 D u.1)).card ≤
      (residualUnits 10 D b).card := Finset.card_le_card (Finset.filter_subset _ _)
  have hR : (residualUnits 10 D b).card = 1 := by omega
  have small : (sem_W 10 D x).card ≤ 3 := by omega
  obtain ⟨rx,hrx⟩ := Finset.card_pos.mp (by omega :
    0 < ((residualUnits 10 D b).filter (fun u => x ∈ supp 10 D u.1)).card)
  obtain ⟨rt,hrt⟩ := Finset.card_pos.mp (by omega :
    0 < ((residualUnits 10 D b).filter (fun u => t ∈ supp 10 D u.1)).card)
  obtain ⟨hrxR,hrxx⟩ := Finset.mem_filter.mp hrx
  obtain ⟨hrtR,hrtt⟩ := Finset.mem_filter.mp hrt
  have huniq : ∀ u ∈ residualUnits 10 D b, u = rt := fun u hu =>
    Finset.card_le_one.mp (by omega) u hu rt hrtR
  have incl : ∀ u ∈ residualUnits 10 D b, x ∈ supp 10 D u.1 → t ∈ supp 10 D u.1 := by
    intro u hu _
    rw [huniq u hu]
    exact hrtt
  have htmem := ke_residual_co_label h hD b hb pos hpos (res_elig hrxR hrxx)
    (res_elig hrtR hrtt) hi hix hx4 ht4 incl ⟨rx.1,hrxx,by rw [huniq rx hrxR];exact hrtt⟩
  obtain ⟨j,hj,hji,hjx⟩ := ke_neighbor_pair hxm hi hix
  have hgeo : ∀ x i j : Fin 10, x.val < 4 → k4_Adj i x → k4_Adj j x → i ≠ j →
      ∃ z, k4_Adj x z ∧ z ≠ i ∧ z ≠ j := by decide +kernel
  obtain ⟨z,hxz,hzi,hzj⟩ := hgeo x i j hx4 hix hjx (Ne.symm hji)
  exact hit ((ke_three_slot_protected h hD pos hpos hi hj (Ne.symm hji) hix hjx hxz hzi hzj small hprotected t).1 htmem)


theorem ke_p7_supported_at_most_two {D : Dag} (h : StrictLive 10 D) (hD : sem_Comp 10 k4_Adj D)
    (hB : Bplus 10 D ≤ 7) (hp : (eligSet 10 D).card = 7) :
    (({0,1,2,3} : Finset (Fin 10)) ∩ eligSet 10 D).card ≤ 2 := by
  classical
  by_contra hnot
  have hcard := inelig_card_add 10 D
  have hIcard : (ineligSet 10 D).card = 3 := by omega
  have heq : ({0,1,2,3} : Finset (Fin 10)) \ ineligSet 10 D =
      ({0,1,2,3} : Finset (Fin 10)) ∩ eligSet 10 D := by
    ext i
    simp only [Finset.mem_sdiff,Finset.mem_inter,sem_mem_inelig,not_not]
  obtain ⟨x,hx4,hxm⟩ := ke_p7_geometry (ineligSet 10 D)
    (k4_inelig_indep h hD) hIcard (by rw [heq]; omega)
  obtain ⟨b,hb⟩ := sem_exists_pureBranch k4_gr h.1 hD
  obtain ⟨pos,hpos⟩ := k4_assigned k4_gr h hD
  have wx := ke_two_neighbors_three h hD pos hpos hx4 hxm
  have cx := ke_cc_le h hD b hb x
  have cr := card_residual h.1 b hb
  have hsubx : ((residualUnits 10 D b).filter (fun u => x ∈ supp 10 D u.1)).card ≤
      (residualUnits 10 D b).card := Finset.card_le_card (Finset.filter_subset _ _)
  omega

theorem ke_low_supported_impossible {D : Dag} (h : StrictLive 10 D) (hD : sem_Comp 10 k4_Adj D)
    (hB : Bplus 10 D ≤ 7) (hp : (eligSet 10 D).card ≤ 5) : False := by
  classical
  obtain ⟨b,hb⟩ := sem_exists_pureBranch k4_gr h.1 hD
  obtain ⟨pos,hpos⟩ := k4_assigned k4_gr h hD
  have cr := card_residual h.1 b hb
  have cover : ∀ u v : Fin 10, k4_Adj u v → u ∈ eligSet 10 D ∨ v ∈ eligSet 10 D :=
    fun u v huv => sem_elig_cover k4_gr h hD huv
  rcases ke_low_cover_geometry (eligSet 10 D) cover hp with heq | ⟨omitted,heq⟩
  · have hp4 : (eligSet 10 D).card = 4 := by rw [heq]; decide
    have hR : (residualUnits 10 D b).card ≤ 3 := by omega
    have hin : ∀ i ∈ (Finset.univ : Finset (Fin 6)), Fin.natAdd 4 i ∈ ineligSet 10 D := by
      intro i _
      rw [sem_mem_inelig,heq]
      have geo : ∀ i : Fin 6, Fin.natAdd 4 i ∉ ({0,1,2,3} : Finset (Fin 10)) := by decide
      exact geo i
    have hw : ∀ x : Fin 4, 3 ≤ (sem_W 10 D (Fin.castLE (by decide : 4 ≤ 10) x)).card := by
      intro x
      exact ke_two_neighbors_three h hD pos hpos x.isLt
        (ke_large_edge_family_many Finset.univ (by decide) hin x)
    obtain ⟨M,hM,_,hbudget⟩ := ke_coordinate_budget h hD b hb pos hpos hR hw Finset.univ hin
    obtain ⟨t,ht⟩ := ke_p4_mask_certificate M hM
    have := hbudget t
    omega
  · have hp5 : (eligSet 10 D).card = 5 := by
      rw [heq]
      have geo : ∀ i : Fin 6, (insert (Fin.natAdd 4 i) ({0,1,2,3} : Finset (Fin 10))).card = 5 := by decide
      exact geo omitted
    have hR : (residualUnits 10 D b).card ≤ 2 := by omega
    let J := (Finset.univ : Finset (Fin 6)).erase omitted
    have hJ : J.card = 5 := by simp [J]
    have hin : ∀ i ∈ J, Fin.natAdd 4 i ∈ ineligSet 10 D := by
      intro i hi
      rw [sem_mem_inelig,heq]
      have ine := (Finset.mem_erase.mp hi).1
      have geo : ∀ o i : Fin 6, i ≠ o → Fin.natAdd 4 i ∉
          insert (Fin.natAdd 4 o) ({0,1,2,3} : Finset (Fin 10)) := by decide
      exact geo omitted i ine
    have hw : ∀ x : Fin 4, 3 ≤ (sem_W 10 D (Fin.castLE (by decide : 4 ≤ 10) x)).card := by
      intro x
      exact ke_two_neighbors_three h hD pos hpos x.isLt
        (ke_large_edge_family_many J (by omega) hin x)
    obtain ⟨M,hM,hunion,hbudget⟩ := ke_coordinate_budget h hD b hb pos hpos (by omega) hw J hin
    obtain ⟨t,ht⟩ := ke_p5_mask_certificate omitted M hM (by omega)
    have same : J.filter (fun i => ∃ x : Fin 4,
        k4_Adj (Fin.castLE (by decide : 4 ≤ 10) x) (Fin.natAdd 4 i) ∧ M x ⊆ M t) =
      Finset.univ.filter (fun i : Fin 6 => i ≠ omitted ∧ ∃ x : Fin 4,
        k4_Adj (Fin.castLE (by decide : 4 ≤ 10) x) (Fin.natAdd 4 i) ∧ M x ⊆ M t) := by
      ext i
      simp only [J,Finset.mem_filter,Finset.mem_erase,Finset.mem_univ,true_and,and_true]
    have bound := hbudget t
    rw [same] at bound
    omega

theorem ke_matching_protected_geometry : ∀ I : Finset (Fin 10),
    (∀ u ∈ I, ∀ v ∈ I, k4_adjB u v = false) → I.card = 4 → 5 ∈ I → 8 ∈ I →
    ∃ x t : Fin 10, x.val < 4 ∧ t.val < 4 ∧ ke_many I x ∧ ke_many I t ∧
      k4_Adj 5 x ∧ ¬ k4_Adj 5 t := by
  have cases : ∀ I : Finset (Fin 10),
      (∀ u ∈ I, ∀ v ∈ I, k4_adjB u v = false) → I.card = 4 → 5 ∈ I → 8 ∈ I →
      I = {4,5,6,8} ∨ I = {4,5,7,8} ∨ I = {4,5,8,9} ∨
      I = {5,6,7,8} ∨ I = {5,6,8,9} ∨ I = {5,7,8,9} := by decide +kernel
  intro I hind hcard h5 h8
  rcases cases I hind hcard h5 h8 with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0,1,by decide⟩
  · exact ⟨0,1,by decide⟩
  · exact ⟨0,1,by decide⟩
  · exact ⟨0,1,by decide⟩
  · exact ⟨0,3,by decide⟩
  · exact ⟨2,1,by decide⟩

theorem ke_protected_matching_supported_lower {D : Dag}
    (h : StrictLive 10 D) (hD : sem_Comp 10 k4_Adj D)
    (h5 : (5 : Fin 10) ∈ ineligSet 10 D) (h8 : (8 : Fin 10) ∈ ineligSet 10 D)
    (hprotected : ∀ w, Relation.ReflTransGen (sem_step 10 D) 5 w → fanout D w ≤ 1) :
    8 ≤ Bplus 10 D := by
  classical
  by_contra hn
  have hB : Bplus 10 D ≤ 7 := by omega
  have cover : ∀ u v : Fin 10, k4_Adj u v → u ∈ eligSet 10 D ∨ v ∈ eligSet 10 D :=
    fun u v huv => sem_elig_cover k4_gr h hD huv
  have geo : ∀ S : Finset (Fin 10),
      (∀ u v : Fin 10, k4_Adj u v → u ∈ S ∨ v ∈ S) → 5 ∉ S → 8 ∉ S →
      ({0,1,2,3} : Finset (Fin 10)) ⊆ S := by decide +kernel
  have sub := geo (eligSet 10 D) cover (sem_mem_inelig.mp h5) (sem_mem_inelig.mp h8)
  have horig : (({0,1,2,3} : Finset (Fin 10)) ∩ eligSet 10 D).card = 4 := by
    rw [Finset.inter_eq_left.mpr sub]
    decide
  obtain ⟨b,hb⟩ := sem_exists_pureBranch k4_gr h.1 hD
  have hp := elig_le_Bplus h.1 b hb
  by_cases small : (eligSet 10 D).card ≤ 5
  · exact ke_low_supported_impossible h hD hB small
  · by_cases six : (eligSet 10 D).card = 6
    · have hcard := inelig_card_add 10 D
      obtain ⟨x,t,hx,ht,hxm,htm,hix,hit⟩ := ke_matching_protected_geometry (ineligSet 10 D)
        (k4_inelig_indep h hD) (by omega) h5 h8
      exact ke_p6_protected_obstruction h hD hB six hx ht hxm htm h5 hix hit hprotected
    · have bound := ke_p7_supported_at_most_two h hD hB (by omega)
      omega

end PEqualNP.Outside.L_meta_6659_aux


namespace PEqualNP.Outside.L_meta_6659_aux

def equality_cof_rep {n m : ℕ} (ι : Fin m → Fin n) (q : ℕ → ℕ) (e : ℕ) : ℕ :=
  if he : e < m then (ι ⟨e,he⟩).val else n + q (e-m)

theorem equality_cof_rep_input {n m : ℕ} (ι : Fin m → Fin n) (q : ℕ → ℕ) (i : Fin m) :
    equality_cof_rep ι q i.val = (ι i).val := by
  simp [equality_cof_rep,i.isLt]

theorem equality_cof_rep_gate {n m : ℕ} (ι : Fin m → Fin n) (q : ℕ → ℕ) (j : ℕ) :
    equality_cof_rep ι q (m+j) = n + q j := by
  simp [equality_cof_rep]

theorem equality_cof_rep_reaches {n m : ℕ} {D E : Dag} {ρ : Fin n → Option Bool}
    {ι : Fin m → Fin n} {t q : ℕ → ℕ} (hS : Strict n D) (hok : cof_Ok ρ ι)
    (hI : cof_Inv D ρ ι D.length E t q) {w : ℕ} (hw : cof_live D ρ ι w) :
    Relation.ReflTransGen (sem_step n D) (equality_cof_rep ι q (t w)) w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases input : w < n
    · obtain ⟨i,rfl⟩ := cof_live_input hok input hw
      rw [hI.2.2.2.2 i,equality_cof_rep_input]
    · let j := w-n
      have wj : w = n+j := by omega
      have hj : j < D.length := by have := cof_live_lt hw; omega
      rw [wj] at hw ⊢
      rcases hI.2.2.2.1 j hj hw with ⟨i,hi,hqi⟩ | collapsed
      · have image := (hI.2.2.1 i hi).2.2.1
        rw [hqi] at image
        rw [image,equality_cof_rep_gate,hqi]
      · obtain ⟨s,hs⟩ := cof_live_op hS hj hw
        have lt : src D (j,s) < w := by
          rw [wj]
          cases s
          · simpa only [sb_src_false] using (hS j hj).1
          · simpa only [sb_src_true] using (hS j hj).2.1
        have path := ih (src D (j,s)) lt hs
        rw [collapsed s hs] at path
        exact path.tail (sem_step_src hj s)

theorem equality_cof_step_lift {n m : ℕ} {D E : Dag} {ρ : Fin n → Option Bool}
    {ι : Fin m → Fin n} {t q : ℕ → ℕ} (hS : Strict n D) (hok : cof_Ok ρ ι)
    (hI : cof_Inv D ρ ι D.length E t q) {a b : ℕ} (hab : sem_step m E a b) :
    Relation.ReflTransGen (sem_step n D) (equality_cof_rep ι q a) (equality_cof_rep ι q b) := by
  obtain ⟨j,s,hj,rfl,rfl⟩ := sem_step_iff.mp hab
  obtain ⟨hq,_,_,ha,hb,hla,hlb⟩ := hI.2.2.1 j hj
  have image : src E (j,s) = t (src D (q j,s)) := by
    cases s <;> simp only [sb_src_false,sb_src_true] <;> assumption
  have live : cof_live D ρ ι (src D (q j,s)) := by
    cases s <;> simp only [sb_src_false,sb_src_true] <;> assumption
  rw [image,equality_cof_rep_gate]
  exact (equality_cof_rep_reaches hS hok hI live).tail (sem_step_src hq s)

theorem equality_cof_path_lift {n m : ℕ} {D E : Dag} {ρ : Fin n → Option Bool}
    {ι : Fin m → Fin n} {t q : ℕ → ℕ} (hS : Strict n D) (hok : cof_Ok ρ ι)
    (hI : cof_Inv D ρ ι D.length E t q) {a b : ℕ}
    (hab : Relation.ReflTransGen (sem_step m E) a b) :
    Relation.ReflTransGen (sem_step n D) (equality_cof_rep ι q a) (equality_cof_rep ι q b) := by
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact ih.trans (equality_cof_step_lift hS hok hI step)

theorem equality_cof_preserves_protection {n m : ℕ} {D E : Dag} {ρ : Fin n → Option Bool}
    {ι : Fin m → Fin n} {t q : ℕ → ℕ} (hS : Strict n D) (hok : cof_Ok ρ ι)
    (hI : cof_Inv D ρ ι D.length E t q) (i : Fin m)
    (hprotected : ∀ w, Relation.ReflTransGen (sem_step n D) (ι i).val w → fanout D w ≤ 1) :
    ∀ e, Relation.ReflTransGen (sem_step m E) i.val e → fanout E e ≤ 1 := by
  classical
  intro e path
  have lifted := equality_cof_path_lift hS hok hI path
  rw [equality_cof_rep_input] at lifted
  have sum : ∑ w ∈ cof_fib D ρ ι t e, cof_deg D ρ ι w ≤ (cof_fib D ρ ι t e).card := by
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_le_sum
    intro w hw
    obtain ⟨_,live,image⟩ := Finset.mem_filter.mp hw
    apply (cof_deg_le w).trans
    apply hprotected
    have tail := equality_cof_rep_reaches hS hok hI live
    rw [image] at tail
    exact lifted.trans tail
  have bound := cof_fib_bound hS hok hI e
  omega

end PEqualNP.Outside.L_meta_6659_aux


namespace PEqualNP.Outside.L_meta_6659_aux
section CofProtectedRestrict
variable {n m : ℕ} {D : Dag} {ρ : Fin n → Option Bool} {ι : Fin m → Fin n}

theorem equality_cof_restrict_protected_many (hS : Strict n D) (hok : cof_Ok ρ ι) (hm : 2 ≤ m)
    (hess : ∀ i : Fin m, ∃ y y' : Fin m → Bool, (∀ k, k ≠ i → y k = y' k) ∧
      val D (cof_ext ρ ι y) (outW n D) ≠ val D (cof_ext ρ ι y') (outW n D)) :
    ∃ E : Dag, StrictLive m E ∧
      (∀ y, val E y (outW m E) = val D (cof_ext ρ ι y) (outW n D)) ∧
      totalSurplus m E ≤ cof_sur D ρ ι ∧ Bplus m E ≤ cof_surP D ρ ι ∧
      (∀ i : Fin m, (∀ w, Relation.ReflTransGen (sem_step n D) (ι i).val w → fanout D w ≤ 1) →
        i ∈ ineligSet m E) ∧
      (∀ i : Fin m, (∀ w, Relation.ReflTransGen (sem_step n D) (ι i).val w → fanout D w ≤ 1) →
        ∀ e, Relation.ReflTransGen (sem_step m E) i.val e → fanout E e ≤ 1) ∧
      ∀ U : Finset (Σ _ : ℕ, ℕ), U ⊆ cof_kept D ρ ι → Set.InjOn (fun u : Σ _ : ℕ, ℕ => u.1) (U : Set _) →
        (∀ u ∈ U, ∃ i ∈ cof_supp D ρ ι u.1, i ∈ ineligSet m E) →
        totalSurplus m E + U.card ≤ cof_sur D ρ ι := by
  classical
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
  refine ⟨E, ⟨hI.1, cof_tr_live hI hfree (by omega) hlo, hne⟩, hvout, ?_, ?_, ?_, ?_, ?_⟩
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

  · exact fun i hprot => equality_cof_preserves_protection hS hok hI i hprot

  · intro U hU hinj hbad
    exact equality_cof_slack_units hS hok hI hout U hU hinj hbad

theorem equality_cof_restrict_graph_protected_many {G : Fin n → Fin n → Prop} (hS : Strict n D) (hok : cof_Ok ρ ι)
    (hC : sem_Comp n G D) (hsym : ∀ u v, G u v → G v u)
    (hT : ∀ c a, ρ c = some true → G c a → ρ a = some false)
    (hG' : sem_Gr (fun u v : Fin m => G (ι u) (ι v))) (hm : 0 < m) :
    ∃ E : Dag, StrictLive m E ∧ sem_Comp m (fun u v : Fin m => G (ι u) (ι v)) E ∧
      totalSurplus m E ≤ cof_sur D ρ ι ∧ Bplus m E ≤ cof_surP D ρ ι ∧
      (∀ i : Fin m, (∀ w, Relation.ReflTransGen (sem_step n D) (ι i).val w → fanout D w ≤ 1) →
        i ∈ ineligSet m E) ∧
      (∀ i : Fin m, (∀ w, Relation.ReflTransGen (sem_step n D) (ι i).val w → fanout D w ≤ 1) →
        ∀ e, Relation.ReflTransGen (sem_step m E) i.val e → fanout E e ≤ 1) ∧
      ∀ U : Finset (Σ _ : ℕ, ℕ), U ⊆ cof_kept D ρ ι → Set.InjOn (fun u : Σ _ : ℕ, ℕ => u.1) (U : Set _) →
        (∀ u ∈ U, ∃ i ∈ cof_supp D ρ ι u.1, i ∈ ineligSet m E) →
        totalSurplus m E + U.card ≤ cof_sur D ρ ι := by
  classical
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
  obtain ⟨E, h1, h2, h3, h4, h5, h6, h7⟩ := equality_cof_restrict_protected_many hS hok hm2 hess
  exact ⟨E, h1, fun y => by rw [h2 y]; exact hval y, h3, h4, h5, h6, h7⟩

end CofProtectedRestrict
end PEqualNP.Outside.L_meta_6659_aux


namespace PEqualNP.Outside.L_meta_6659_aux

theorem equality_cf_supported_eight {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    {c : Fin 14} {l : List ℕ} (hgood : cf_good c l)
    (hp5 : ∀ w, Relation.ReflTransGen (sem_step 14 D) (cf_iota l (5 : Fin 10)).val w →
      fanout D w ≤ 1)
    (hp8 : ∀ w, Relation.ReflTransGen (sem_step 14 D) (cf_iota l (8 : Fin 10)).val w →
      fanout D w ≤ 1) :
    8 ≤ cof_surP D (cf_rho c) (cf_iota l) := by
  classical
  have hC := sem_heawood_comp hD
  have hS := h.1
  obtain ⟨hinj, hfree, hiso⟩ := hgood
  have hok : cof_Ok (cf_rho c) (cf_iota l) := ⟨fun a b hab => hinj a b hab, hfree⟩
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
  obtain ⟨E,hE,hCE,_,hB,hprot,hfull,_⟩ := equality_cof_restrict_graph_protected_many
    hS hok hC (fun _ _ huv => adj_symm huv) hT (by rw [heq]; exact k4_gr) (by norm_num)
  have hK : sem_Comp 10 k4_Adj E := heq ▸ hCE
  have eight := ke_protected_matching_supported_lower hE hK
    (hprot 5 hp5) (hprot 8 hp8) (hfull 5 hp5)
  exact eight.trans hB

end PEqualNP.Outside.L_meta_6659_aux


namespace PEqualNP.Outside.L_meta_6659_aux

def m9_neighbors (i : Fin 4) : Finset (Fin 6) :=
  ![{0,1,2},{0,3,4},{1,3,5},{2,4,5}] i

def m9_protected (i : Fin 2) : Fin 4 := Fin.castLE (by decide) i

def m9_forced (r : Fin 6 → Finset (Fin 3)) (a b : Fin 3) (i : Fin 4) : Finset (Fin 6) :=
  Finset.univ.filter (fun t => (∃ x ∈ m9_neighbors i, r x ⊆ r t) ∨
    (i = 2 ∧ t = m9_extra2 a) ∨ (i = 3 ∧ t = m9_extra5 b))

def m9_consumers (r : Fin 6 → Finset (Fin 3)) (a b : Fin 3) (t : Fin 6) : Finset (Fin 4) :=
  Finset.univ.filter (fun i => t ∈ m9_forced r a b i)

def m9_saturated (r : Fin 6 → Finset (Fin 3)) (a b : Fin 3) (i : Fin 2) : Prop :=
  ∃ x ∈ m9_neighbors (m9_protected i), (m9_consumers r a b x).card = 1 + (r x).card

def m9_unit_support (r : Fin 6 → Finset (Fin 3)) (k : Fin 3) : Finset (Fin 6) :=
  Finset.univ.filter (fun t => k ∈ r t)

abbrev m9_constraints (r : Fin 6 → Finset (Fin 3)) (a b : Fin 3) : Prop :=
  (∀ t, (r t).Nonempty ∧ r t ≠ Finset.univ) ∧
  (∀ k, m9_unit_support r k ≠ m9_neighbors 2 ∧ m9_unit_support r k ≠ m9_neighbors 3) ∧
  (∀ t, (m9_consumers r a b t).card ≤ 1 + (r t).card) ∧
  (∀ i, m9_saturated r a b i → m9_forced r a b (m9_protected i) ⊆ m9_neighbors (m9_protected i))

def m9_point_forced (r : Fin 6 → Finset (Fin 3)) (T : Finset (Fin 3)) : Finset (Fin 4) :=
  Finset.univ.filter (fun i => ∃ x ∈ m9_neighbors i, r x ⊆ T)

abbrev m9_point_constraints (r : Fin 6 → Finset (Fin 3)) (a b : Fin 3)
    (T : Finset (Fin 3)) : Prop :=
  T.Nonempty ∧
  (∀ i, m9_saturated r a b i → m9_protected i ∉ m9_point_forced r T) ∧
  (m9_point_forced r T).card ≤ T.card ∧
  (∀ t, (m9_consumers r a b t).card + (if T ⊆ r t then 1 else 0) ≤ 1 + (r t).card)

theorem m9_sub_correct : ∀ a b : Fin 8, m9_sub a b = true ↔ m9_mask a ⊆ m9_mask b := by
  decide +kernel

theorem m9_card_correct : ∀ a : Fin 8, m9_card a = (m9_mask a).card := by decide +kernel

theorem m9_bit_correct : ∀ a : Fin 8, ∀ k : Fin 3, m9_bit a k = true ↔ k ∈ m9_mask a := by
  decide +kernel

theorem m9_mask_nonempty : ∀ a : Fin 8, a ≠ 0 ↔ (m9_mask a).Nonempty := by decide +kernel

theorem m9_mask_proper : ∀ a : Fin 8, a ≠ 7 ↔ m9_mask a ≠ Finset.univ := by decide +kernel

theorem m9_filter_four : ∀ f : Fin 4 → Bool,
    (Finset.univ.filter (fun i => f i = true)).card =
      (f 0).toNat + (f 1).toNat + (f 2).toNat + (f 3).toNat := by decide +kernel

theorem m9_force_correct (r : Fin 6 → Fin 8) (a b : Fin 3) (i : Fin 4) (t : Fin 6) :
    m9_force r a b i t = true ↔ t ∈ m9_forced (fun x => m9_mask (r x)) a b i := by
  fin_cases i <;> simp [m9_force,m9_forced,m9_neighbors,m9_sub_correct,or_assoc]

theorem m9_count_correct (r : Fin 6 → Fin 8) (a b : Fin 3) (t : Fin 6) :
    m9_count r a b t = (m9_consumers (fun x => m9_mask (r x)) a b t).card := by
  have equal : m9_consumers (fun x => m9_mask (r x)) a b t =
      Finset.univ.filter (fun i => m9_force r a b i t = true) := by
    ext i
    simp [m9_consumers,m9_force_correct]
  rw [equal,m9_filter_four]
  rfl

theorem m9_full_correct (r : Fin 6 → Fin 8) (a b : Fin 3) (i : Fin 2) :
    m9_full r a b i = true ↔ m9_saturated (fun x => m9_mask (r x)) a b i := by
  fin_cases i <;>
    simp [m9_full,m9_saturated,m9_neighbors,m9_protected,m9_count_correct,m9_card_correct,or_assoc]

theorem m9_pointForce_correct (r : Fin 6 → Fin 8) (T : Fin 8) (i : Fin 4) :
    m9_pointForce r T i = true ↔ i ∈ m9_point_forced (fun x => m9_mask (r x)) (m9_mask T) := by
  unfold m9_point_forced
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ,true_and]
  fin_cases i <;> simp [m9_pointForce,m9_neighbors,m9_sub_correct,or_assoc]

theorem m9_pointCount_correct (r : Fin 6 → Fin 8) (T : Fin 8) :
    (m9_pointForce r T 0).toNat + (m9_pointForce r T 1).toNat +
      (m9_pointForce r T 2).toNat + (m9_pointForce r T 3).toNat =
      (m9_point_forced (fun x => m9_mask (r x)) (m9_mask T)).card := by
  have equal : m9_point_forced (fun x => m9_mask (r x)) (m9_mask T) =
      Finset.univ.filter (fun i => m9_pointForce r T i = true) := by
    ext i
    simp [m9_pointForce_correct]
  rw [equal,m9_filter_four]

theorem m9_unit_code_two : ∀ f : Fin 6 → Bool,
    (f 0).toNat + 2*(f 1).toNat + 4*(f 2).toNat + 8*(f 3).toNat +
      16*(f 4).toNat + 32*(f 5).toNat = 42 ↔
      Finset.univ.filter (fun t => f t = true) = m9_neighbors 2 := by decide +kernel

theorem m9_unit_code_five : ∀ f : Fin 6 → Bool,
    (f 0).toNat + 2*(f 1).toNat + 4*(f 2).toNat + 8*(f 3).toNat +
      16*(f 4).toNat + 32*(f 5).toNat = 52 ↔
      Finset.univ.filter (fun t => f t = true) = m9_neighbors 3 := by decide +kernel

theorem m9_unitMask_correct (r : Fin 6 → Fin 8) (k : Fin 3) :
    (m9_unitMask r k = 42 ↔ m9_unit_support (fun x => m9_mask (r x)) k = m9_neighbors 2) ∧
    (m9_unitMask r k = 52 ↔ m9_unit_support (fun x => m9_mask (r x)) k = m9_neighbors 3) := by
  have equal : Finset.univ.filter (fun t => m9_bit (r t) k = true) =
      m9_unit_support (fun x => m9_mask (r x)) k := by
    ext t
    simp [m9_unit_support,m9_bit_correct]
  constructor
  · simpa only [m9_unitMask,equal] using m9_unit_code_two (fun t => m9_bit (r t) k)
  · simpa only [m9_unitMask,equal] using m9_unit_code_five (fun t => m9_bit (r t) k)

theorem m9_bool_imp (a b : Bool) (h : a = true → b = true) : (!a || b) = true := by
  cases a <;> simp_all

theorem m9_not_both (a b : Bool) (h : a = true → b = true → False) : !(a && b) = true := by
  cases a <;> cases b <;> simp_all

theorem m9_normal_of_constraints (r : Fin 6 → Fin 8) (a b : Fin 3)
    (hc : m9_constraints (fun t => m9_mask (r t)) a b) : m9_normal r a b = true := by
  have proper (t : Fin 6) : r t ≠ 0 ∧ r t ≠ 7 :=
    ⟨(m9_mask_nonempty _).2 (hc.1 t).1,(m9_mask_proper _).2 (hc.1 t).2⟩
  have missing (k : Fin 3) : m9_unitMask r k ≠ 42 ∧ m9_unitMask r k ≠ 52 :=
    ⟨fun equal => (hc.2.1 k).1 ((m9_unitMask_correct r k).1.1 equal),
      fun equal => (hc.2.1 k).2 ((m9_unitMask_correct r k).2.1 equal)⟩
  have budget (t : Fin 6) : m9_count r a b t ≤ 1 + m9_card (r t) := by
    rw [m9_count_correct,m9_card_correct]
    exact hc.2.2.1 t
  have outside (i : Fin 2) (full : m9_full r a b i = true) (t : Fin 6)
      (notNeighbor : t ∉ m9_neighbors (m9_protected i)) :
      m9_force r a b (m9_protected i) t = false := by
    cases value : m9_force r a b (m9_protected i) t with
    | false => rfl
    | true =>
      exact False.elim (notNeighbor (hc.2.2.2 i ((m9_full_correct r a b i).1 full)
        ((m9_force_correct r a b _ t).1 value)))
  have full0 : (!m9_full r a b 0 ||
      (!m9_force r a b 0 3 && !m9_force r a b 0 4 && !m9_force r a b 0 5)) = true := by
    apply m9_bool_imp
    intro full
    have h3 := outside 0 full 3 (by decide)
    have h4 := outside 0 full 4 (by decide)
    have h5 := outside 0 full 5 (by decide)
    change m9_force r a b 0 3 = false at h3
    change m9_force r a b 0 4 = false at h4
    change m9_force r a b 0 5 = false at h5
    simp [h3,h4,h5]
  have full1 : (!m9_full r a b 1 ||
      (!m9_force r a b 1 1 && !m9_force r a b 1 2 && !m9_force r a b 1 5)) = true := by
    apply m9_bool_imp
    intro full
    have h1 := outside 1 full 1 (by decide)
    have h2 := outside 1 full 2 (by decide)
    have h5 := outside 1 full 5 (by decide)
    change m9_force r a b 1 1 = false at h1
    change m9_force r a b 1 2 = false at h2
    change m9_force r a b 1 5 = false at h5
    simp [h1,h2,h5]
  have p0 := proper 0
  have p1 := proper 1
  have p2 := proper 2
  have p3 := proper 3
  have p4 := proper 4
  have p5 := proper 5
  have u0 := missing 0
  have u1 := missing 1
  have u2 := missing 2
  have b0 := budget 0
  have b1 := budget 1
  have b2 := budget 2
  have b3 := budget 3
  have b4 := budget 4
  have b5 := budget 5
  simp only [m9_normal,full0,full1,Bool.and_true,Bool.and_eq_true,decide_eq_true_eq]
  tauto

theorem m9_sub_toNat : ∀ a b : Fin 8,
    (m9_sub a b).toNat = if m9_mask a ⊆ m9_mask b then 1 else 0 := by decide +kernel

theorem m9_pointAllowed_of_constraints (r : Fin 6 → Fin 8) (a b : Fin 3) (T : Fin 8)
    (hc : m9_point_constraints (fun t => m9_mask (r t)) a b (m9_mask T)) :
    m9_pointAllowed r a b T = true := by
  have nonempty : T ≠ 0 := (m9_mask_nonempty T).2 hc.1
  have absent (i : Fin 2) : !(m9_full r a b i && m9_pointForce r T (m9_protected i)) = true := by
    apply m9_not_both
    intro full forced
    exact hc.2.1 i ((m9_full_correct r a b i).1 full)
      ((m9_pointForce_correct r T (m9_protected i)).1 forced)
  have count : (m9_pointForce r T 0).toNat + (m9_pointForce r T 1).toNat +
      (m9_pointForce r T 2).toNat + (m9_pointForce r T 3).toNat ≤ m9_card T := by
    rw [m9_pointCount_correct,m9_card_correct]
    exact hc.2.2.1
  have budget (t : Fin 6) : m9_count r a b t + (m9_sub T (r t)).toNat ≤ 1+m9_card (r t) := by
    rw [m9_count_correct,m9_sub_toNat,m9_card_correct]
    exact hc.2.2.2 t
  have a0 := absent 0
  have a1 := absent 1
  change (!(m9_full r a b 0 && m9_pointForce r T 0)) = true at a0
  change (!(m9_full r a b 1 && m9_pointForce r T 1)) = true at a1
  have b0 := budget 0
  have b1 := budget 1
  have b2 := budget 2
  have b3 := budget 3
  have b4 := budget 4
  have b5 := budget 5
  simp only [m9_pointAllowed,Bool.and_eq_true,decide_eq_true_eq]
  tauto


theorem m9_mask_surjective : Function.Surjective m9_mask := by decide +kernel

theorem m9_mask_injective : Function.Injective m9_mask := by decide +kernel

theorem m9_no_point_constraints_of_certificate
    (certificate : ∀ (r : Fin 6 → Fin 8) (a b : Fin 3) (T : Fin 8),
      (r 0 = 1 ∨ r 0 = 3) → m9_normal r a b = true → m9_pointAllowed r a b T = false)
    (r : Fin 6 → Finset (Fin 3)) (a b : Fin 3) (T : Finset (Fin 3))
    (first : r 0 = {0} ∨ r 0 = {0,1}) (normal : m9_constraints r a b)
    (point : m9_point_constraints r a b T) : False := by
  classical
  choose code encoded using (fun t => m9_mask_surjective (r t))
  obtain ⟨pointCode,pointEncoded⟩ := m9_mask_surjective T
  have vector : (fun t => m9_mask (code t)) = r := funext encoded
  have firstCode : code 0 = 1 ∨ code 0 = 3 := by
    rcases first with first | first
    · apply Or.inl
      apply m9_mask_injective
      rw [encoded,first]
      rfl
    · apply Or.inr
      apply m9_mask_injective
      rw [encoded,first]
      rfl
  have normalCode : m9_normal code a b = true :=
    m9_normal_of_constraints code a b (by simpa only [vector] using normal)
  have pointTrue : m9_pointAllowed code a b pointCode = true :=
    m9_pointAllowed_of_constraints code a b pointCode
      (by simpa only [vector,pointEncoded] using point)
  have pointFalse := certificate code a b pointCode firstCode normalCode
  rw [pointFalse] at pointTrue
  exact Bool.false_ne_true pointTrue

theorem equality_lost_saturates_chain {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (P : Finset (Fin 14)) (hP : ∀ a ∈ P, ∀ b ∈ P, ¬ Adj a b)
    (J : Finset (Fin 14))
    (hJ : ∀ i ∈ J, i ∈ ineligSet 14 D ∧ sem_hw_nb i ⊆ P ∧
      ¬ sup_Occ 14 D P (sem_hw_nb i))
    (budget : J.card = Bzero 14 D) {v : Fin 14}
    (hv : v ∈ ineligSet 14 D) (hvJ : v ∉ J) (hvP : sem_hw_nb v ⊆ P) :
    sem_Chain 14 D v.val (outW 14 D) := by
  classical
  have hG := sem_heawood_gr
  have hC := sem_heawood_comp hD
  rcases sem_inelig_reach hG h hC hv with chain | ⟨bv,hbv,hbf,hbs⟩
  · exact chain
  exfalso
  have absent : ∀ i ∈ J, ∀ q,
      (∀ a ∈ P, (a ∈ supp 14 D q ↔ Adj i a)) → False := by
    intro i hi q hq
    refine (hJ i hi).2.2 ⟨q, ?_⟩
    ext a
    rw [Finset.mem_inter, hw_mem_nb]
    exact ⟨fun h1 => (hq a h1.2).1 h1.1,
      fun h1 => ⟨(hq a ((hJ i hi).2.1 (hw_mem_nb.2 h1))).2 h1,
        (hJ i hi).2.1 (hw_mem_nb.2 h1)⟩⟩
  have hb : ∀ i ∈ insert v J,
      ∃ b, sem_Chain 14 D i.val b ∧ 2 ≤ fanout D b ∧ supp 14 D b = ∅ := by
    intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact ⟨bv,hbv,hbf,hbs⟩
    · rcases sem_inelig_reach hG h hC (hJ i hi).1 with chain | branch
      · obtain ⟨j,s,_,_,_,hq⟩ := sem_exact_nbhd hG h.1 hC P hP chain
        exact (absent i hi _ hq).elim
      · exact branch
  choose! β hβ using hb
  have neighbors : ∀ i ∈ insert v J, sem_hw_nb i ⊆ P := by
    intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hvP
    · exact (hJ i hi).2.1
  have distinct : ∀ i ∈ J, ∀ j ∈ insert v J, i ≠ j → β i ≠ β j := by
    intro i hi j hj different equal
    have hi' : i ∈ insert v J := Finset.mem_insert_of_mem hi
    obtain ⟨a,ha1,ha2⟩ := nbr_diff_exists j i (Ne.symm different)
    obtain ⟨k,s,_,_,_,_,hq⟩ := sem_shared_exact hG h.1 hC P hP (hβ i hi').1
      (sem_chain_dom h.1 (equal ▸ (hβ j hj).1))
      ⟨a,neighbors j hj (hw_mem_nb.2 ha1),ha1,ha2⟩
    exact absent i hi _ hq
  have injective : Set.InjOn β ((insert v J : Finset (Fin 14)) : Set (Fin 14)) := by
    intro i hi j hj equal
    by_contra different
    by_cases hiJ : i ∈ J
    · exact distinct i hiJ j hj different equal
    · have hiv : i = v := (Finset.mem_insert.1 hi).resolve_right hiJ
      have hjJ : j ∈ J := (Finset.mem_insert.1 hj).resolve_left (by
        intro hjv
        exact different (hiv.trans hjv.symm))
      exact distinct j hjJ i hi (Ne.symm different) equal.symm
  have bound : ((insert v J).image β).card ≤ Bzero 14 D := by
    apply bz_card h.1
    intro b hb
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.1 hb
    exact (hβ i hi).2
  rw [Finset.card_image_of_injOn injective,Finset.card_insert_of_notMem hvJ,budget] at bound
  omega

theorem equality_chain_protected {D : Dag} (strict : Strict 14 D) {v : ℕ}
    (chain : sem_Chain 14 D v (outW 14 D)) :
    ∀ w, Relation.ReflTransGen (sem_step 14 D) v w → fanout D w ≤ 1 := by
  have last : fanout D (outW 14 D) = 0 :=
    fanout_eq_zero_of_ge strict _ (by unfold outW; omega)
  induction chain using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro w path
    rcases Relation.ReflTransGen.cases_head path with equal | ⟨next,first,rest⟩
    · rw [← equal,last]
      omega
    · have positive := sem_step_fanout first
      omega
  | @head a next first rest ih =>
    intro w path
    rcases Relation.ReflTransGen.cases_head path with equal | ⟨next',initial,remaining⟩
    · rw [← equal,first.2]
    · have same : next = next' := sem_step_unique first.1 initial first.2
      subst next'
      exact ih w remaining



noncomputable def equality_missing_cap (D : Dag) : Finset (Fin 14) := by
  classical
  exact ({0, 1, 2, 5} : Finset (Fin 14)).filter
    (fun i => ¬ sup_Occ 14 D mx_L (sem_hw_nb i))



theorem equality_mixed_cap_saturated {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h14 : totalSurplus 14 D ≤ 14)
    (hI : ineligSet 14 D = {0, 1, 2, 5, 11}) :
    (equality_missing_cap D).card = Bzero 14 D := by
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
  have htotal := totalSurplus_split 14 D
  change Mc.card = Bzero 14 D
  omega

theorem equality_mixed_cap_occ_chain {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h14 : totalSurplus 14 D ≤ 14)
    (hI : ineligSet 14 D = {0, 1, 2, 5, 11}) {v : Fin 14}
    (hv : v ∈ ({0, 1, 2, 5} : Finset (Fin 14)))
    (hmask : sup_Occ 14 D mx_L (sem_hw_nb v)) :
    sem_Chain 14 D v.val (outW 14 D) := by
  classical
  let J := ({0, 1, 2, 5} : Finset (Fin 14)).filter
    (fun i => ¬ sup_Occ 14 D mx_L (sem_hw_nb i))
  have hLl : mx_L ⊆ sem_hw_opp 0 := by decide
  have hin : ∀ i ∈ ({0, 1, 2, 5} : Finset (Fin 14)), i ∈ ineligSet 14 D := by rw [hI]; decide
  apply equality_lost_saturates_chain h hD mx_L
    (fun a ha b hb => sem_hw_opp_indep 0 a (hLl ha) b (hLl hb)) J
  · intro i hi
    exact ⟨hin i (Finset.mem_filter.1 hi).1,mx_cap i (Finset.mem_filter.1 hi).1,
      (Finset.mem_filter.1 hi).2⟩
  · exact equality_mixed_cap_saturated h hD h14 hI
  · exact hin v hv
  · intro hi
    exact (Finset.mem_filter.1 hi).2 hmask
  · exact mx_cap v hv


theorem equality_reachable_chain {n : ℕ} {D : Dag} {i w : ℕ}
    (hprotected : ∀ u, Relation.ReflTransGen (sem_step n D) i u → fanout D u ≤ 1)
    (path : Relation.ReflTransGen (sem_step n D) i w) : sem_Chain n D i w := by
  induction path with
  | refl => exact Relation.ReflTransGen.refl
  | @tail a c prior step ih =>
    have one : fanout D a = 1 := by
      have := hprotected a prior
      have := sem_step_fanout step
      omega
    exact Relation.ReflTransGen.tail ih ⟨step,one⟩

theorem equality_full_gen_protected {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    {i v : Fin 14} (hi : i ∈ ineligSet 14 D) {e : ℕ × Bool}
    (he : sem_W 14 D i = {e}) (hiv : Adj i v)
    (hprotected : ∀ w, Relation.ReflTransGen (sem_step 14 D) i.val w → fanout D w ≤ 1)
    (hv : ∀ p ∈ sem_W 14 D v, p.1 ≠ e.1 → ¬ supp 14 D (src D (sem_bar p)) ⊆ {i}) :
    ∀ t, t ∈ supp 14 D (src D (sem_bar e)) ↔ Adj i t := by
  have hG := sem_heawood_gr
  have hC := sem_heawood_comp hD
  have hS := h.1
  refine sem_full_support hG h hC hi he (fun j hreach hj => ?_)
  by_contra ht
  rw [Bool.not_eq_false] at ht
  rcases Relation.ReflTransGen.cases_tail hreach with heq | ⟨w, hw1, hw2⟩
  · exact hj (by omega)
  · obtain ⟨j', s, hj', hjeq, hsrc⟩ := sem_step_iff.1 hw2
    have hjj : j' = j := by omega
    subst hjj
    have hew : e ∈ sem_W 14 D i := by rw [he]; exact Finset.mem_singleton_self e
    obtain ⟨he1, he2, -⟩ := sem_mem_W.1 hew
    have hreach2 : Relation.ReflTransGen (sem_step 14 D) i.val w :=
      ((sem_rtg_mono (fun _ _ hab => hab.1) (sem_inelig_chain hS hi he2)).tail
        (sem_step_src he1 e.2)).trans hw1
    have hch := equality_reachable_chain hprotected hreach2
    have hf : fanout D w = 1 := by
      have := hprotected w hreach2
      have := sem_step_fanout hw2
      omega
    have hsub : supp 14 D w ⊆ {i} := sem_dom_pure hG hS hC i w (sem_chain_dom hS hch)
    have hvi : v ≠ i := fun hvi => hG.2.1 i (hvi ▸ hiv)
    have hw' : src D (j', !(!s)) = w := by rw [Bool.not_not]; exact hsrc
    have hmem : v ∈ supp 14 D (src D (j', !s)) :=
      sem_and_sibling_nbrs hG hS hC hj' (!s) ht (hw' ▸ hch) (hw' ▸ hf)
        (by unfold outW; omega) hiv
    have hp : ((j', !s) : ℕ × Bool) ∈ sem_W 14 D v :=
      sem_mem_W.2 ⟨hj', hmem, fun hc => by
        have := hsub (hsrc ▸ sem_supp_and_sub hS hj' ht s hc)
        exact hvi (Finset.mem_singleton.1 this)⟩
    exact hv _ hp hj (by rw [show sem_bar (j', !s) = (j', !(!s)) from rfl, hw']; exact hsub)

theorem equality_residual_co_label {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b) (pos : Fin 14 → ℕ × Bool)
    (hpos : k4_Pos 14 HG D pos) {x t i : Fin 14}
    (hx : x ∈ eligSet 14 D) (ht : t ∈ eligSet 14 D) (hi : i ∈ ineligSet 14 D)
    (hix : Adj i x)
    (inclusion : ∀ u ∈ residualUnits 14 D b, x ∈ supp 14 D u.1 → t ∈ supp 14 D u.1)
    (shared : ∃ w, x ∈ supp 14 D w ∧ t ∈ supp 14 D w) :
    t ∈ supp 14 D (src D (pos i)) := by
  by_cases hxt : x = t
  · exact hxt ▸ (hpos.1 i hi).2.2.1 x hix
  obtain ⟨w,hw⟩ := shared
  obtain ⟨e0,he0⟩ := ri_gen sem_heawood_gr h (sem_heawood_comp hD) b hb hxt hx inclusion hw
  have hti : t ≠ i := fun equal => sem_mem_inelig.1 hi (equal ▸ ht)
  have hgeo : ∀ i x t : Fin 14, hc_adjB i x = true → t ≠ x → t ≠ i →
      ∃ q, hc_adjB i q = true ∧ q ≠ x ∧ hc_adjB t q = false := by decide +kernel
  obtain ⟨q,hiq,hqx,htq⟩ := hgeo i x t ((hc_adjB_iff _ _).2 hix) (Ne.symm hxt) hti
  have hiq' := (hc_adjB_iff _ _).1 hiq
  have htq' := sem_adjB_false.1 htq
  by_contra hnot
  have heq : pos i = e0 := by
    by_contra hne
    exact hnot (he0 _ (as_mem hpos hi hix) hne)
  obtain ⟨e,he,hnt,hnq⟩ := sem_hw_cover_free h hD hxt (Ne.symm hqx) htq'
  exact hnt (he0 e he (fun equal => hnq (by
    rw [equal,← heq]
    exact (hpos.1 i hi).2.2.1 q hiq')))

theorem equality_assigned_mem {D : Dag} {pos : Fin 14 → ℕ × Bool}
    (hpos : k4_Pos 14 HG D pos) {i t : Fin 14} (hi : i ∈ ineligSet 14 D)
    (ht : t ∈ supp 14 D (src D (pos i))) : pos i ∈ sem_W 14 D t :=
  sem_mem_W.2 ⟨(hpos.1 i hi).1,ht,by
    rw [(hpos.1 i hi).2.1]
    exact Finset.notMem_empty t⟩

theorem equality_assigned_budget_extra {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b) (pos : Fin 14 → ℕ × Bool)
    (hpos : k4_Pos 14 HG D pos) (J : Finset (Fin 14)) {t z : Fin 14}
    (hJ : ∀ i ∈ J, i ∈ ineligSet 14 D ∧ t ∈ supp 14 D (src D (pos i)))
    (hz : z ∈ eligSet 14 D) (edge : Adj t z) :
    J.card + 1 ≤ 2 + (ru D b t).card := by
  classical
  obtain ⟨H,hHt,hHz,_,_,_⟩ := sem_edge_slots sem_heawood_gr h.1 (sem_heawood_comp hD) edge
  have injective : Set.InjOn pos (J : Set (Fin 14)) :=
    fun i hi j hj equal => hpos.2 i (hJ i hi).1 j (hJ j hj).1 equal
  have fresh : H ∉ J.image pos := by
    intro he
    obtain ⟨i,hi,equal⟩ := Finset.mem_image.1 he
    have same : z = i := as_priv hpos (hJ i hi).1 (equal ▸ hHz)
    exact sem_mem_inelig.1 (hJ i hi).1 (same ▸ hz)
  have subset : insert H (J.image pos) ⊆ sem_W 14 D t := by
    intro e he
    rcases Finset.mem_insert.1 he with rfl | he
    · exact hHt
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.1 he
      exact equality_assigned_mem hpos (hJ i hi).1 (hJ i hi).2
  have lower := Finset.card_le_card subset
  rw [Finset.card_insert_of_notMem fresh,Finset.card_image_of_injOn injective] at lower
  have upper := cc_le h hD b hb t
  omega


theorem equality_three_coordinate_normalize : ∀ M : Finset (Fin 3),
    M.card = 1 ∨ M.card = 2 → ∃ σ : Equiv.Perm (Fin 3),
      M.image σ = {0} ∨ M.image σ = {0,1} := by
  decide +kernel

theorem equality_residual_coordinates {D : Dag} {b : Fin 14 → ℕ}
    (hres : (residualUnits 14 D b).card = 3)
    (h7 : (ru D b 7).card = 1 ∨ (ru D b 7).card = 2) :
    ∃ a : Fin 3 → (Σ _ : ℕ, ℕ), Function.Injective a ∧
      (∀ u, u ∈ residualUnits 14 D b ↔ ∃ k, a k = u) ∧
      ((Finset.univ.filter (fun k => (7 : Fin 14) ∈ supp 14 D (a k).1)) = {0} ∨
        (Finset.univ.filter (fun k => (7 : Fin 14) ∈ supp 14 D (a k).1)) = {0,1}) := by
  classical
  let S := residualUnits 14 D b
  let e : (↑S) ≃ Fin 3 := Fintype.equivFinOfCardEq (by rw [Fintype.card_coe]; exact hres)
  let a0 : Fin 3 → (Σ _ : ℕ, ℕ) := fun k => (e.symm k).val
  have inj0 : Function.Injective a0 :=
    fun i j equal => e.symm.injective (Subtype.ext equal)
  have onto0 : ∀ u, u ∈ S ↔ ∃ k, a0 k = u := by
    intro u
    constructor
    · intro hu
      exact ⟨e ⟨u,hu⟩,by simp [a0]⟩
    · rintro ⟨k,rfl⟩
      exact (e.symm k).property
  let M := Finset.univ.filter (fun k => (7 : Fin 14) ∈ supp 14 D (a0 k).1)
  have image : M.image a0 = ru D b 7 := by
    ext u
    constructor
    · rintro hu
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.1 hu
      exact mem_ru.2 ⟨(onto0 _).2 ⟨k,rfl⟩,(Finset.mem_filter.1 hk).2⟩
    · intro hu
      obtain ⟨hur,hu7⟩ := mem_ru.1 hu
      obtain ⟨k,rfl⟩ := (onto0 u).1 hur
      exact Finset.mem_image.2 ⟨k,Finset.mem_filter.2 ⟨Finset.mem_univ _,hu7⟩,rfl⟩
  have card : M.card = (ru D b 7).card := by
    rw [← image,Finset.card_image_of_injective _ inj0]
  obtain ⟨σ,hσ⟩ := equality_three_coordinate_normalize M (by omega)
  let a : Fin 3 → (Σ _ : ℕ, ℕ) := fun k => a0 (σ.symm k)
  refine ⟨a,inj0.comp σ.symm.injective,?_,?_⟩
  · intro u
    rw [onto0]
    constructor
    · rintro ⟨k,rfl⟩
      exact ⟨σ k,by simp [a]⟩
    · rintro ⟨k,rfl⟩
      exact ⟨σ.symm k,rfl⟩
  · have same : Finset.univ.filter (fun k => (7 : Fin 14) ∈ supp 14 D (a k).1) = M.image σ := by
      ext k
      simp only [M,a,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image]
      constructor
      · intro hk
        exact ⟨σ.symm k,hk,σ.apply_symm_apply k⟩
      · rintro ⟨j,hj,rfl⟩
        simpa using hj
    rw [same]
    exact hσ

noncomputable def equality_coordinate_set {D : Dag}
    (a : Fin 3 → (Σ _ : ℕ, ℕ)) (x : Fin 14) : Finset (Fin 3) := by
  classical
  exact Finset.univ.filter (fun k => x ∈ supp 14 D (a k).1)

theorem equality_coordinate_image {D : Dag} {b : Fin 14 → ℕ}
    (a : Fin 3 → (Σ _ : ℕ, ℕ))
    (onto : ∀ u, u ∈ residualUnits 14 D b ↔ ∃ k, a k = u) (x : Fin 14) :
    (equality_coordinate_set (D := D) a x).image a = ru D b x := by
  classical
  ext u
  constructor
  · intro hu
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.1 hu
    exact mem_ru.2 ⟨(onto _).2 ⟨k,rfl⟩,(Finset.mem_filter.1 hk).2⟩
  · intro hu
    obtain ⟨hur,hux⟩ := mem_ru.1 hu
    obtain ⟨k,rfl⟩ := (onto u).1 hur
    exact Finset.mem_image.2 ⟨k,Finset.mem_filter.2 ⟨Finset.mem_univ _,hux⟩,rfl⟩

theorem equality_coordinate_card {D : Dag} {b : Fin 14 → ℕ}
    (a : Fin 3 → (Σ _ : ℕ, ℕ)) (injective : Function.Injective a)
    (onto : ∀ u, u ∈ residualUnits 14 D b ↔ ∃ k, a k = u) (x : Fin 14) :
    (equality_coordinate_set (D := D) a x).card = (ru D b x).card := by
  rw [← equality_coordinate_image a onto x,Finset.card_image_of_injective _ injective]

theorem equality_coordinate_subset {D : Dag} {b : Fin 14 → ℕ}
    (a : Fin 3 → (Σ _ : ℕ, ℕ))
    (onto : ∀ u, u ∈ residualUnits 14 D b ↔ ∃ k, a k = u) (x y : Fin 14) :
    equality_coordinate_set (D := D) a x ⊆ equality_coordinate_set (D := D) a y ↔
      ∀ u ∈ residualUnits 14 D b, x ∈ supp 14 D u.1 → y ∈ supp 14 D u.1 := by
  classical
  constructor
  · intro sub u hu hx
    obtain ⟨k,rfl⟩ := (onto u).1 hu
    exact (Finset.mem_filter.1 (sub (Finset.mem_filter.2 ⟨Finset.mem_univ _,hx⟩))).2
  · intro inc k hk
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _,inc (a k) ((onto _).2 ⟨k,rfl⟩)
      (Finset.mem_filter.1 hk).2⟩


theorem equality_two_assigned_positive {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b) (pos : Fin 14 → ℕ × Bool)
    (hpos : k4_Pos 14 HG D pos) {x i j z : Fin 14}
    (hi : i ∈ ineligSet 14 D) (hj : j ∈ ineligSet 14 D)
    (hij : i ≠ j) (hix : Adj i x) (hjx : Adj j x) (hxz : Adj x z)
    (hzi : z ≠ i) (hzj : z ≠ j) : 0 < (ru D b x).card := by
  classical
  obtain ⟨H,hHx,hHz,_,_,_⟩ := sem_edge_slots sem_heawood_gr h.1 (sem_heawood_comp hD) hxz
  have ai := as_mem hpos hi hix
  have aj := as_mem hpos hj hjx
  have ni : H ≠ pos i := fun equal => hzi (as_priv hpos hi (equal ▸ hHz))
  have nj : H ≠ pos j := fun equal => hzj (as_priv hpos hj (equal ▸ hHz))
  have nij : pos i ≠ pos j := fun equal => hij (hpos.2 i hi j hj equal)
  have subset : ({pos i,pos j,H} : Finset (ℕ × Bool)) ⊆ sem_W 14 D x := by
    intro e he
    simp only [Finset.mem_insert,Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl <;> assumption
  have lower := Finset.card_le_card subset
  rw [Finset.card_insert_of_notMem (by simp [nij,Ne.symm ni]),
    Finset.card_pair (Ne.symm nj)] at lower
  have upper := cc_le h hD b hb x
  omega



theorem equality_saturated_slot_full {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b) (pos : Fin 14 → ℕ × Bool)
    (hpos : k4_Pos 14 HG D pos) (J : Finset (Fin 14)) {x i z : Fin 14}
    (hJ : ∀ j ∈ J, j ∈ ineligSet 14 D ∧ x ∈ supp 14 D (src D (pos j)))
    (hiJ : i ∈ J) (hix : Adj i x) (hz : z ∈ eligSet 14 D) (hxz : Adj x z)
    (saturated : 2 + (ru D b x).card ≤ J.card + 1)
    (hprotected : ∀ w, Relation.ReflTransGen (sem_step 14 D) i.val w → fanout D w ≤ 1) :
    ∀ t, t ∈ supp 14 D (src D (pos i)) ↔ Adj i t := by
  classical
  have hi := (hJ i hiJ).1
  obtain ⟨H,hHx,hHz,_,_,_⟩ :=
    sem_edge_slots sem_heawood_gr h.1 (sem_heawood_comp hD) hxz
  have injective : Set.InjOn pos (J : Set (Fin 14)) :=
    fun j hj k hk equal => hpos.2 j (hJ j hj).1 k (hJ k hk).1 equal
  have fresh : H ∉ J.image pos := by
    intro member
    obtain ⟨j,hj,equal⟩ := Finset.mem_image.1 member
    have same : z = j := as_priv hpos (hJ j hj).1 (equal ▸ hHz)
    exact sem_mem_inelig.1 (hJ j hj).1 (same ▸ hz)
  have subset : insert H (J.image pos) ⊆ sem_W 14 D x := by
    intro p hp
    rcases Finset.mem_insert.1 hp with rfl | hp
    · exact hHx
    · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.1 hp
      exact equality_assigned_mem hpos (hJ j hj).1 (hJ j hj).2
  have code : sem_W 14 D x = insert H (J.image pos) := by
    symm
    apply Finset.eq_of_subset_of_card_le subset
    rw [Finset.card_insert_of_notMem fresh,Finset.card_image_of_injOn injective]
    have upper := cc_le h hD b hb x
    omega
  have full := equality_full_gen_protected h hD hi (as_W h hD hpos hi) hix hprotected
    (fun p hp hne hsub => by
      rw [code] at hp
      rcases Finset.mem_insert.1 hp with rfl | hp
      · have same : z = i := Finset.mem_singleton.1 (hsub (sem_mem_W.1 hHz).2.1)
        exact sem_mem_inelig.1 hi (same ▸ hz)
      · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.1 hp
        have member : j ∈ supp 14 D (src D (sem_bar (pos j))) := by
          rw [show src D (sem_bar (pos j)) = src D ((pos j).1,!(pos j).2) from rfl,
            (hpos.1 j (hJ j hj).1).2.2.2]
          exact Finset.mem_singleton_self j
        have same : j = i := Finset.mem_singleton.1 (hsub member)
        exact hne (by rw [same]; rfl))
  simpa only [sem_bar_bar] using full


def equality_m9_line : Fin 6 → Fin 14 := ![7,8,10,13,9,12]

def equality_m9_point : Fin 4 → Fin 14 := ![0,1,2,5]

theorem equality_m9_line_injective : Function.Injective equality_m9_line := by decide +kernel

theorem equality_m9_point_injective : Function.Injective equality_m9_point := by decide +kernel

theorem equality_m9_adjacency : ∀ i : Fin 4, ∀ t : Fin 6,
    t ∈ m9_neighbors i ↔ hc_adjB (equality_m9_point i) (equality_m9_line t) = true := by
  decide +kernel

def equality_m9_cofactor : Fin 6 → List ℕ := ![[2,4,5,6,13,12,8,10,11,9],
  [1,3,4,5,7,13,9,11,12,10],
  [1,2,3,6,13,7,9,12,8,11],
  [0,3,5,6,7,10,8,12,11,9],
  [0,2,3,4,8,7,10,12,13,11],
  [0,1,4,6,7,10,8,13,9,11]]

theorem equality_m9_cf_good : ∀ t : Fin 6,
    cf_good (equality_m9_line t) (equality_m9_cofactor t) := by decide +kernel



theorem equality_m9_ineligible {D : Dag} (hI : ineligSet 14 D = {0,1,2,5,11})
    (i : Fin 4) : equality_m9_point i ∈ ineligSet 14 D := by
  rw [hI]
  exact (by decide +kernel : ∀ i : Fin 4, equality_m9_point i ∈ ({0,1,2,5,11} : Finset (Fin 14))) i

theorem equality_m9_eligible {D : Dag} (hI : ineligSet 14 D = {0,1,2,5,11})
    (t : Fin 6) : equality_m9_line t ∈ eligSet 14 D := by
  by_contra hn
  have hm := hI ▸ sem_mem_inelig.2 hn
  exact (by decide +kernel : ∀ t : Fin 6, equality_m9_line t ∉ ({0,1,2,5,11} : Finset (Fin 14))) t hm

theorem equality_m9_positive {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b)
    (pos : Fin 14 → ℕ × Bool) (hpos : k4_Pos 14 HG D pos)
    (hI : ineligSet 14 D = {0,1,2,5,11}) (t : Fin 6) :
    0 < (ru D b (equality_m9_line t)).card := by
  have geometry : ∀ t : Fin 6, ∃ i j : Fin 4, ∃ z : Fin 14,
      i ≠ j ∧ hc_adjB (equality_m9_point i) (equality_m9_line t) = true ∧
      hc_adjB (equality_m9_point j) (equality_m9_line t) = true ∧
      hc_adjB (equality_m9_line t) z = true ∧
      z ≠ equality_m9_point i ∧ z ≠ equality_m9_point j := by decide +kernel
  obtain ⟨i,j,z,hij,hix,hjx,hxz,hzi,hzj⟩ := geometry t
  exact equality_two_assigned_positive h hD b hb pos hpos (equality_m9_ineligible hI i)
    (equality_m9_ineligible hI j) (fun equal => hij (equality_m9_point_injective equal))
    ((hc_adjB_iff _ _).1 hix) ((hc_adjB_iff _ _).1 hjx) ((hc_adjB_iff _ _).1 hxz) hzi hzj

theorem equality_m9_coordinate_proper {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h14 : totalSurplus 14 D ≤ 14) (b : Fin 14 → ℕ) (hb : PureBranch 14 D b)
    (pos : Fin 14 → ℕ × Bool) (hpos : k4_Pos 14 HG D pos)
    (hI : ineligSet 14 D = {0,1,2,5,11})
    (a : Fin 3 → (Σ _ : ℕ, ℕ)) (injective : Function.Injective a)
    (onto : ∀ u, u ∈ residualUnits 14 D b ↔ ∃ k, a k = u) (t : Fin 6) :
    equality_coordinate_set (D := D) a (equality_m9_line t) ≠ Finset.univ := by
  classical
  intro full
  have hall : ∀ u ∈ residualUnits 14 D b, equality_m9_line t ∈ supp 14 D u.1 := by
    intro u hu
    obtain ⟨k,rfl⟩ := (onto u).1 hu
    have member : k ∈ equality_coordinate_set (D := D) a (equality_m9_line t) := by
      rw [full]; exact Finset.mem_univ _
    exact (Finset.mem_filter.1 member).2
  let X := (Finset.univ.erase t).image equality_m9_line
  have hx : ∀ x ∈ X, x ∈ eligSet 14 D ∧ x ≠ equality_m9_line t ∧
      (∀ u ∈ residualUnits 14 D b, x ∈ supp 14 D u.1 → equality_m9_line t ∈ supp 14 D u.1) ∧
      ∃ w, x ∈ supp 14 D w ∧ equality_m9_line t ∈ supp 14 D w := by
    intro x hx
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨u,hu⟩ := Finset.card_pos.1 (equality_m9_positive h hD b hb pos hpos hI s)
    obtain ⟨hur,hux⟩ := mem_ru.1 hu
    exact ⟨equality_m9_eligible hI s,
      fun eq => (Finset.mem_erase.1 hs).1 (equality_m9_line_injective eq),
      fun u hu _ => hall u hu,u.1,hux,hall u hur⟩
  have bound := cf_six h hD b hb (equality_m9_cf_good t) (equality_m9_eligible hI t) X hx
  have Xcard : X.card = 5 := by
    rw [Finset.card_image_of_injective _ equality_m9_line_injective]
    simp
  have card := equality_coordinate_card a injective onto (equality_m9_line t)
  rw [full,Finset.card_univ,Fintype.card_fin] at card
  rw [Xcard] at bound
  omega

theorem equality_m9_forced_mem {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b)
    (pos : Fin 14 → ℕ × Bool) (hpos : k4_Pos 14 HG D pos)
    (hI : ineligSet 14 D = {0,1,2,5,11})
    (a : Fin 3 → (Σ _ : ℕ, ℕ))
    (onto : ∀ u, u ∈ residualUnits 14 D b ↔ ∃ k, a k = u)
    (α β : Fin 3)
    (extra2 : equality_m9_line (m9_extra2 α) ∈ supp 14 D (src D (pos 2)))
    (extra5 : equality_m9_line (m9_extra5 β) ∈ supp 14 D (src D (pos 5)))
    (i : Fin 4) (t : Fin 6)
    (ht : t ∈ m9_forced (fun s => equality_coordinate_set (D := D) a (equality_m9_line s)) α β i) :
    equality_m9_line t ∈ supp 14 D (src D (pos (equality_m9_point i))) := by
  classical
  rcases (Finset.mem_filter.1 ht).2 with ⟨x,hx,subset⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · have inclusion := (equality_coordinate_subset a onto (equality_m9_line x)
      (equality_m9_line t)).1 subset
    obtain ⟨u,hu⟩ := Finset.card_pos.1 (equality_m9_positive h hD b hb pos hpos hI x)
    obtain ⟨hur,hux⟩ := mem_ru.1 hu
    exact equality_residual_co_label h hD b hb pos hpos (equality_m9_eligible hI x)
      (equality_m9_eligible hI t) (equality_m9_ineligible hI i)
      ((hc_adjB_iff _ _).1 ((equality_m9_adjacency i x).1 hx)) inclusion
      ⟨u.1,hux,inclusion u hur hux⟩
  · exact extra2
  · exact extra5



theorem equality_m9_range : Finset.univ.image equality_m9_line = mx_L := by decide +kernel

theorem equality_m9_neighbors_image : ∀ i : Fin 4,
    (m9_neighbors i).image equality_m9_line = sem_hw_nb (equality_m9_point i) := by
  decide +kernel

theorem equality_m9_mask_image {D : Dag} (a : Fin 3 → (Σ _ : ℕ, ℕ)) (k : Fin 3) :
    (m9_unit_support (fun t => equality_coordinate_set (D := D) a (equality_m9_line t)) k).image
      equality_m9_line = supp 14 D (a k).1 ∩ mx_L := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.1 hx
    refine Finset.mem_inter.2 ⟨(Finset.mem_filter.1 ((Finset.mem_filter.1 ht).2)).2,?_⟩
    rw [← equality_m9_range]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  · intro hx
    obtain ⟨hs,hp⟩ := Finset.mem_inter.1 hx
    rw [← equality_m9_range] at hp
    obtain ⟨t,_,rfl⟩ := Finset.mem_image.1 hp
    exact Finset.mem_image.2 ⟨t,Finset.mem_filter.2 ⟨Finset.mem_univ _,
      Finset.mem_filter.2 ⟨Finset.mem_univ _,hs⟩⟩,rfl⟩

theorem equality_m9_unit_missing {D : Dag} (a : Fin 3 → (Σ _ : ℕ, ℕ))
    (missing2 : ¬ sup_Occ 14 D mx_L (sem_hw_nb 2))
    (missing5 : ¬ sup_Occ 14 D mx_L (sem_hw_nb 5)) (k : Fin 3) :
    m9_unit_support (fun t => equality_coordinate_set (D := D) a (equality_m9_line t)) k ≠
      m9_neighbors 2 ∧
    m9_unit_support (fun t => equality_coordinate_set (D := D) a (equality_m9_line t)) k ≠
      m9_neighbors 3 := by
  constructor
  · intro equal
    apply missing2
    refine ⟨(a k).1,?_⟩
    rw [← equality_m9_mask_image a k,equal,equality_m9_neighbors_image]
    rfl
  · intro equal
    apply missing5
    refine ⟨(a k).1,?_⟩
    rw [← equality_m9_mask_image a k,equal,equality_m9_neighbors_image]
    rfl

theorem equality_m9_assigned_extra {D : Dag} (pos : Fin 14 → ℕ × Bool)
    (hpos : k4_Pos 14 HG D pos) (hI : ineligSet 14 D = {0,1,2,5,11})
    (i : Fin 4) (missing : ¬ sup_Occ 14 D mx_L (sem_hw_nb (equality_m9_point i))) :
    ∃ t : Fin 6, t ∉ m9_neighbors i ∧
      equality_m9_line t ∈ supp 14 D (src D (pos (equality_m9_point i))) := by
  classical
  by_contra hn
  apply missing
  refine ⟨src D (pos (equality_m9_point i)),?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨hs,hp⟩ := Finset.mem_inter.1 hx
    rw [← equality_m9_range] at hp
    obtain ⟨t,_,rfl⟩ := Finset.mem_image.1 hp
    have ht : t ∈ m9_neighbors i := by
      by_contra no
      exact hn ⟨t,no,hs⟩
    rw [← equality_m9_neighbors_image i]
    exact Finset.mem_image_of_mem _ ht
  · intro hx
    refine Finset.mem_inter.2 ⟨(hpos.1 _ (equality_m9_ineligible hI i)).2.2.1 x
      (hw_mem_nb.1 hx),?_⟩
    rw [← equality_m9_neighbors_image i] at hx
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.1 hx
    rw [← equality_m9_range]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)

theorem equality_m9_extras {D : Dag} (pos : Fin 14 → ℕ × Bool)
    (hpos : k4_Pos 14 HG D pos) (hI : ineligSet 14 D = {0,1,2,5,11})
    (missing2 : ¬ sup_Occ 14 D mx_L (sem_hw_nb 2))
    (missing5 : ¬ sup_Occ 14 D mx_L (sem_hw_nb 5)) :
    ∃ α β : Fin 3,
      equality_m9_line (m9_extra2 α) ∈ supp 14 D (src D (pos 2)) ∧
      equality_m9_line (m9_extra5 β) ∈ supp 14 D (src D (pos 5)) := by
  obtain ⟨t,ht,hmem⟩ := equality_m9_assigned_extra pos hpos hI 2 missing2
  obtain ⟨s,hs,hmem'⟩ := equality_m9_assigned_extra pos hpos hI 3 missing5
  have g2 : ∀ t : Fin 6, t ∉ m9_neighbors 2 → ∃ α : Fin 3, m9_extra2 α = t := by decide +kernel
  have g5 : ∀ t : Fin 6, t ∉ m9_neighbors 3 → ∃ β : Fin 3, m9_extra5 β = t := by decide +kernel
  obtain ⟨α,rfl⟩ := g2 t ht
  obtain ⟨β,rfl⟩ := g5 s hs
  exact ⟨α,β,hmem,hmem'⟩



theorem equality_m9_extra_neighbor {D : Dag} (hI : ineligSet 14 D = {0,1,2,5,11})
    (t : Fin 6) : ∃ z : Fin 14, z ∈ eligSet 14 D ∧ Adj (equality_m9_line t) z := by
  have geo : ∀ t : Fin 6, ∃ z : Fin 14,
      z ∉ ({0,1,2,5,11} : Finset (Fin 14)) ∧ hc_adjB (equality_m9_line t) z = true := by
    decide +kernel
  obtain ⟨z,hz,edge⟩ := geo t
  refine ⟨z,?_,(hc_adjB_iff _ _).1 edge⟩
  by_contra hn
  exact hz (hI ▸ sem_mem_inelig.2 hn)

theorem equality_m9_consumer_budget {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b)
    (pos : Fin 14 → ℕ × Bool) (hpos : k4_Pos 14 HG D pos)
    (hI : ineligSet 14 D = {0,1,2,5,11})
    (a : Fin 3 → (Σ _ : ℕ, ℕ)) (injective : Function.Injective a)
    (onto : ∀ u, u ∈ residualUnits 14 D b ↔ ∃ k, a k = u)
    (α β : Fin 3)
    (extra2 : equality_m9_line (m9_extra2 α) ∈ supp 14 D (src D (pos 2)))
    (extra5 : equality_m9_line (m9_extra5 β) ∈ supp 14 D (src D (pos 5))) (t : Fin 6) :
    (m9_consumers (fun s => equality_coordinate_set (D := D) a (equality_m9_line s)) α β t).card ≤
      1 + (equality_coordinate_set (D := D) a (equality_m9_line t)).card := by
  classical
  let r := fun s => equality_coordinate_set (D := D) a (equality_m9_line s)
  let J := (m9_consumers r α β t).image equality_m9_point
  have hJ : ∀ i ∈ J, i ∈ ineligSet 14 D ∧
      equality_m9_line t ∈ supp 14 D (src D (pos i)) := by
    intro i hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.1 hi
    exact ⟨equality_m9_ineligible hI j,
      equality_m9_forced_mem h hD b hb pos hpos hI a onto α β extra2 extra5 j t
        (Finset.mem_filter.1 hj).2⟩
  obtain ⟨z,hz,edge⟩ := equality_m9_extra_neighbor hI t
  have budget := equality_assigned_budget_extra h hD b hb pos hpos J hJ hz edge
  have card : J.card = (m9_consumers r α β t).card :=
    Finset.card_image_of_injective _ equality_m9_point_injective
  have rcard := equality_coordinate_card a injective onto (equality_m9_line t)
  rw [card,← rcard] at budget
  dsimp [r] at budget
  omega

theorem equality_m9_saturated_full {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b)
    (pos : Fin 14 → ℕ × Bool) (hpos : k4_Pos 14 HG D pos)
    (hI : ineligSet 14 D = {0,1,2,5,11})
    (hprotected : ∀ i ∈ ({0,1} : Finset (Fin 14)), ∀ w,
      Relation.ReflTransGen (sem_step 14 D) i.val w → fanout D w ≤ 1)
    (a : Fin 3 → (Σ _ : ℕ, ℕ)) (injective : Function.Injective a)
    (onto : ∀ u, u ∈ residualUnits 14 D b ↔ ∃ k, a k = u)
    (α β : Fin 3)
    (extra2 : equality_m9_line (m9_extra2 α) ∈ supp 14 D (src D (pos 2)))
    (extra5 : equality_m9_line (m9_extra5 β) ∈ supp 14 D (src D (pos 5)))
    (i : Fin 2)
    (saturated : m9_saturated (fun s => equality_coordinate_set (D := D) a (equality_m9_line s)) α β i) :
    ∀ v, v ∈ supp 14 D (src D (pos (equality_m9_point (m9_protected i)))) ↔
      Adj (equality_m9_point (m9_protected i)) v := by
  classical
  let r := fun s => equality_coordinate_set (D := D) a (equality_m9_line s)
  obtain ⟨x,hx,sat⟩ := saturated
  let J := (m9_consumers r α β x).image equality_m9_point
  have hJ : ∀ j ∈ J, j ∈ ineligSet 14 D ∧
      equality_m9_line x ∈ supp 14 D (src D (pos j)) := by
    intro j hj
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.1 hj
    exact ⟨equality_m9_ineligible hI k,
      equality_m9_forced_mem h hD b hb pos hpos hI a onto α β extra2 extra5 k x
        (Finset.mem_filter.1 hk).2⟩
  have hiJ : equality_m9_point (m9_protected i) ∈ J := by
    refine Finset.mem_image.2 ⟨m9_protected i,Finset.mem_filter.2 ⟨Finset.mem_univ _,?_⟩,rfl⟩
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _,Or.inl ⟨x,hx,Finset.Subset.refl _⟩⟩
  have card : J.card = (m9_consumers r α β x).card :=
    Finset.card_image_of_injective _ equality_m9_point_injective
  have rcard := equality_coordinate_card a injective onto (equality_m9_line x)
  obtain ⟨z,hz,edge⟩ := equality_m9_extra_neighbor hI x
  apply equality_saturated_slot_full h hD b hb pos hpos J hJ hiJ
    ((hc_adjB_iff _ _).1 ((equality_m9_adjacency (m9_protected i) x).1 hx)) hz edge
  · rw [card]
    change (m9_consumers r α β x).card = 1 + (r x).card at sat
    change (r x).card = (ru D b (equality_m9_line x)).card at rcard
    omega
  · exact hprotected _ ((by decide +kernel : ∀ i : Fin 2,
      equality_m9_point (m9_protected i) ∈ ({0,1} : Finset (Fin 14))) i)

theorem equality_m9_constraints {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h14 : totalSurplus 14 D ≤ 14) (b : Fin 14 → ℕ) (hb : PureBranch 14 D b)
    (pos : Fin 14 → ℕ × Bool) (hpos : k4_Pos 14 HG D pos)
    (hI : ineligSet 14 D = {0,1,2,5,11})
    (missing2 : ¬ sup_Occ 14 D mx_L (sem_hw_nb 2))
    (missing5 : ¬ sup_Occ 14 D mx_L (sem_hw_nb 5))
    (hprotected : ∀ i ∈ ({0,1} : Finset (Fin 14)), ∀ w,
      Relation.ReflTransGen (sem_step 14 D) i.val w → fanout D w ≤ 1)
    (a : Fin 3 → (Σ _ : ℕ, ℕ)) (injective : Function.Injective a)
    (onto : ∀ u, u ∈ residualUnits 14 D b ↔ ∃ k, a k = u)
    (α β : Fin 3)
    (extra2 : equality_m9_line (m9_extra2 α) ∈ supp 14 D (src D (pos 2)))
    (extra5 : equality_m9_line (m9_extra5 β) ∈ supp 14 D (src D (pos 5))) :
    m9_constraints (fun t => equality_coordinate_set (D := D) a (equality_m9_line t)) α β := by
  classical
  refine ⟨?_,?_,?_,?_⟩
  · intro t
    refine ⟨Finset.card_pos.1 ?_,equality_m9_coordinate_proper h hD h14 b hb pos hpos hI a injective onto t⟩
    rw [equality_coordinate_card a injective onto]
    exact equality_m9_positive h hD b hb pos hpos hI t
  · exact equality_m9_unit_missing a missing2 missing5
  · exact equality_m9_consumer_budget h hD b hb pos hpos hI a injective onto α β extra2 extra5
  · intro i saturated t ht
    have full := equality_m9_saturated_full h hD b hb pos hpos hI hprotected a injective onto
      α β extra2 extra5 i saturated
    have mem := equality_m9_forced_mem h hD b hb pos hpos hI a onto α β extra2 extra5
      (m9_protected i) t ht
    exact (equality_m9_adjacency _ _).2 ((hc_adjB_iff _ _).2 ((full _).1 mem))



theorem equality_m9_point_eligible {D : Dag} (hI : ineligSet 14 D = {0,1,2,5,11})
    {z : Fin 14} (hz : z ∈ ({3,4,6} : Finset (Fin 14))) : z ∈ eligSet 14 D := by
  by_contra hn
  exact Finset.disjoint_left.1
    (by decide : Disjoint ({3,4,6} : Finset (Fin 14)) {0,1,2,5,11}) hz
    (hI ▸ sem_mem_inelig.2 hn)

theorem equality_m9_point_forced_mem {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b)
    (pos : Fin 14 → ℕ × Bool) (hpos : k4_Pos 14 HG D pos)
    (hI : ineligSet 14 D = {0,1,2,5,11})
    (a : Fin 3 → (Σ _ : ℕ, ℕ))
    (onto : ∀ u, u ∈ residualUnits 14 D b ↔ ∃ k, a k = u)
    {z : Fin 14} (hz : z ∈ ({3,4,6} : Finset (Fin 14))) (i : Fin 4)
    (hi : i ∈ m9_point_forced (fun s => equality_coordinate_set (D := D) a (equality_m9_line s))
      (equality_coordinate_set (D := D) a z)) :
    z ∈ supp 14 D (src D (pos (equality_m9_point i))) := by
  classical
  obtain ⟨x,hx,subset⟩ := (Finset.mem_filter.1 hi).2
  have inclusion := (equality_coordinate_subset a onto (equality_m9_line x) z).1 subset
  obtain ⟨u,hu⟩ := Finset.card_pos.1 (equality_m9_positive h hD b hb pos hpos hI x)
  obtain ⟨hur,hux⟩ := mem_ru.1 hu
  exact equality_residual_co_label h hD b hb pos hpos (equality_m9_eligible hI x)
    (equality_m9_point_eligible hI hz) (equality_m9_ineligible hI i)
    ((hc_adjB_iff _ _).1 ((equality_m9_adjacency i x).1 hx)) inclusion
    ⟨u.1,hux,inclusion u hur hux⟩

theorem equality_m9_point_constraints {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b)
    (pos : Fin 14 → ℕ × Bool) (hpos : k4_Pos 14 HG D pos)
    (hI : ineligSet 14 D = {0,1,2,5,11})
    (hprotected : ∀ i ∈ ({0,1} : Finset (Fin 14)), ∀ w,
      Relation.ReflTransGen (sem_step 14 D) i.val w → fanout D w ≤ 1)
    (a : Fin 3 → (Σ _ : ℕ, ℕ)) (injective : Function.Injective a)
    (onto : ∀ u, u ∈ residualUnits 14 D b ↔ ∃ k, a k = u)
    (α β : Fin 3)
    (extra2 : equality_m9_line (m9_extra2 α) ∈ supp 14 D (src D (pos 2)))
    (extra5 : equality_m9_line (m9_extra5 β) ∈ supp 14 D (src D (pos 5)))
    {z : Fin 14} (hz : z ∈ ({3,4,6} : Finset (Fin 14)))
    (positive : (equality_coordinate_set (D := D) a z).Nonempty) :
    m9_point_constraints (fun t => equality_coordinate_set (D := D) a (equality_m9_line t))
      α β (equality_coordinate_set (D := D) a z) := by
  classical
  let r := fun t => equality_coordinate_set (D := D) a (equality_m9_line t)
  let T := equality_coordinate_set (D := D) a z
  have hi11 : (11 : Fin 14) ∈ ineligSet 14 D := by rw [hI]; decide
  have edge11 : Adj 11 z := (hc_adjB_iff _ _).1
    ((by decide +kernel : ∀ z ∈ ({3,4,6} : Finset (Fin 14)), hc_adjB 11 z = true) z hz)
  have no11 : ∀ J : Finset (Fin 4), (11 : Fin 14) ∉ J.image equality_m9_point := by
    intro J member
    obtain ⟨i,_,eq⟩ := Finset.mem_image.1 member
    exact (by decide +kernel : ∀ i : Fin 4, equality_m9_point i ≠ (11 : Fin 14)) i eq
  refine ⟨positive,?_,?_,?_⟩
  · intro i saturated forced
    have full := equality_m9_saturated_full h hD b hb pos hpos hI hprotected a injective onto
      α β extra2 extra5 i saturated
    have mem := equality_m9_point_forced_mem h hD b hb pos hpos hI a onto hz (m9_protected i) forced
    have edge := (full z).1 mem
    have no := (by decide +kernel : ∀ i : Fin 2, ∀ z ∈ ({3,4,6} : Finset (Fin 14)),
      hc_adjB (equality_m9_point (m9_protected i)) z = false) i z hz
    have yes := (hc_adjB_iff _ _).2 edge
    rw [no] at yes
    exact Bool.false_ne_true yes
  · let J := (m9_point_forced r T).image equality_m9_point
    have hJ : ∀ i ∈ insert 11 J, i ∈ ineligSet 14 D ∧ z ∈ supp 14 D (src D (pos i)) := by
      intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact ⟨hi11,(hpos.1 11 hi11).2.2.1 z edge11⟩
      · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.1 hi
        exact ⟨equality_m9_ineligible hI j,
          equality_m9_point_forced_mem h hD b hb pos hpos hI a onto hz j hj⟩
    have geo : ∀ z ∈ ({3,4,6} : Finset (Fin 14)), ∃ t : Fin 6,
        hc_adjB z (equality_m9_line t) = true := by decide +kernel
    obtain ⟨t,edge⟩ := geo z hz
    have bound := equality_assigned_budget_extra h hD b hb pos hpos (insert 11 J) hJ
      (equality_m9_eligible hI t) ((hc_adjB_iff _ _).1 edge)
    have card : J.card = (m9_point_forced r T).card :=
      Finset.card_image_of_injective _ equality_m9_point_injective
    rw [Finset.card_insert_of_notMem (no11 _),card] at bound
    have tc := equality_coordinate_card a injective onto z
    change T.card = (ru D b z).card at tc
    change (m9_point_forced r T).card ≤ T.card
    omega
  · intro t
    by_cases inclusion : T ⊆ r t
    · let J := (m9_consumers r α β t).image equality_m9_point
      have inc := (equality_coordinate_subset a onto z (equality_m9_line t)).1 inclusion
      obtain ⟨k,hk⟩ := positive
      have huz : z ∈ supp 14 D (a k).1 := (Finset.mem_filter.1 hk).2
      have hur : a k ∈ residualUnits 14 D b := (onto _).2 ⟨k,rfl⟩
      have line11 := equality_residual_co_label h hD b hb pos hpos
        (equality_m9_point_eligible hI hz) (equality_m9_eligible hI t) hi11 edge11 inc
        ⟨(a k).1,huz,inc (a k) hur huz⟩
      have hJ : ∀ i ∈ insert 11 J, i ∈ ineligSet 14 D ∧
          equality_m9_line t ∈ supp 14 D (src D (pos i)) := by
        intro i hi
        rcases Finset.mem_insert.1 hi with rfl | hi
        · exact ⟨hi11,line11⟩
        · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.1 hi
          exact ⟨equality_m9_ineligible hI j,
            equality_m9_forced_mem h hD b hb pos hpos hI a onto α β extra2 extra5 j t
              (Finset.mem_filter.1 hj).2⟩
      obtain ⟨z',hz',edge⟩ := equality_m9_extra_neighbor hI t
      have bound := equality_assigned_budget_extra h hD b hb pos hpos (insert 11 J) hJ hz' edge
      have card : J.card = (m9_consumers r α β t).card :=
        Finset.card_image_of_injective _ equality_m9_point_injective
      rw [Finset.card_insert_of_notMem (no11 _),card] at bound
      have rc := equality_coordinate_card a injective onto (equality_m9_line t)
      change (r t).card = (ru D b (equality_m9_line t)).card at rc
      change (m9_consumers r α β t).card + (if T ⊆ r t then 1 else 0) ≤ 1 + (r t).card
      rw [ite_eq_left inclusion]
      omega
    · have bound := equality_m9_consumer_budget h hD b hb pos hpos hI a injective onto
        α β extra2 extra5 t
      change (m9_consumers r α β t).card + (if T ⊆ r t then 1 else 0) ≤ 1 + (r t).card
      rw [ite_eq_right inclusion,Nat.add_zero]
      exact bound



theorem equality_m9_all_constraints {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h14 : totalSurplus 14 D ≤ 14) (b : Fin 14 → ℕ) (hb : PureBranch 14 D b)
    (hI : ineligSet 14 D = {0,1,2,5,11})
    (missing2 : ¬ sup_Occ 14 D mx_L (sem_hw_nb 2))
    (missing5 : ¬ sup_Occ 14 D mx_L (sem_hw_nb 5))
    (hprotected : ∀ i ∈ ({0,1} : Finset (Fin 14)), ∀ w,
      Relation.ReflTransGen (sem_step 14 D) i.val w → fanout D w ≤ 1)
    (a : Fin 3 → (Σ _ : ℕ, ℕ)) (injective : Function.Injective a)
    (onto : ∀ u, u ∈ residualUnits 14 D b ↔ ∃ k, a k = u) :
    ∃ α β : Fin 3,
      m9_constraints (fun t => equality_coordinate_set (D := D) a (equality_m9_line t)) α β ∧
      ∀ z ∈ ({3,4,6} : Finset (Fin 14)), (equality_coordinate_set (D := D) a z).Nonempty →
        m9_point_constraints (fun t => equality_coordinate_set (D := D) a (equality_m9_line t))
          α β (equality_coordinate_set (D := D) a z) := by
  obtain ⟨pos,hpos⟩ := k4_assigned sem_heawood_gr h (sem_heawood_comp hD)
  obtain ⟨α,β,e2,e5⟩ := equality_m9_extras pos hpos hI missing2 missing5
  refine ⟨α,β,equality_m9_constraints h hD h14 b hb pos hpos hI missing2 missing5
    hprotected a injective onto α β e2 e5,?_⟩
  intro z hz positive
  exact equality_m9_point_constraints h hD b hb pos hpos hI hprotected a injective onto
    α β e2 e5 hz positive



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

lemma single_reader_chain_agreement {n : ℕ} {D : Dag} (hS : Strict n D)
    (x y : Fin n → Bool) (i : Fin n) (agree : ∀ k, k ≠ i → x k = y k)
    {a w : ℕ} (chain : sem_Chain n D i.val a) (bound : a ≤ w)
    (same : val D x a = val D y a) : val D x w = val D y w := by
  by_contra changed
  have inputChanged : x i ≠ y i := by
    intro hi
    have equal : x = y := by
      funext k
      by_cases hk : k = i
      · simpa only [hk] using hi
      · exact agree k hk
    exact changed (congrArg (fun z => val D z w) equal)
  have firstChanged : val D x i.val ≠ val D y i.val := by
    simpa only [val_input D x i.val i.isLt,val_input D y i.val i.isLt] using inputChanged
  exact (single_reader_chain_hits hS chain (fun z => val D x z ≠ val D y z)
    w (sem_changed_path hS x y i agree w changed) firstChanged bound) same

lemma ineligible_consumption_insert_false {n : ℕ} {D : Dag} (hS : Strict n D)
    (i c : Fin n) (hi : i ∈ ineligSet n D) (e : ℕ × Bool)
    (he : e ∈ sem_W n D i) (absent : c ∉ supp n D (src D (sem_bar e)))
    (w : ℕ) (bound : n + e.1 ≤ w) (absentW : c ∉ supp n D w) :
    val D (sem_ins i (single c)) w = false := by
  obtain ⟨hj,carrier,_⟩ := sem_mem_W.mp he
  have chain : sem_Chain n D i.val (src D e) := sem_inelig_chain hS hi carrier
  have step : sem_step n D (src D e) (n+e.1) := sem_step_src hj e.2
  have one : fanout D (src D e) = 1 := by
    have lower := sem_step_fanout step
    have upper := mem_ineligSet.mp hi (src D e) carrier
    omega
  have otherSame : val D (single c) (src D (sem_bar e)) =
      val D (sem_ins i (single c)) (src D (sem_bar e)) := by
    by_contra changed
    have reach := sem_rtg_mono (fun _ _ h => h.1)
      (sem_changed_path hS (single c) (sem_ins i (single c)) i
        (sem_ins_agree i (single c)) _ changed)
    exact single_reader_other_unreachable hS chain step one
      (sem_step_src hj (!e.2)) (sem_src_ne hS hj e.2).symm reach
  have otherFalse : val D (single c) (src D (sem_bar e)) = false := by
    cases hv : val D (single c) (src D (sem_bar e)) with
    | false => rfl
    | true => exact False.elim (absent (mem_supp.mpr hv))
  have gateFalse (z : Fin n → Bool) (hz : val D z (src D (sem_bar e)) = false) :
      val D z (n+e.1) = false := by
    rw [val_gate hS z e.1 hj,sem_W_and hS he]
    cases hs : e.2 <;> simp [sem_bar,src,hs] at hz <;> simp [gop,hz]
  have sameGate : val D (single c) (n+e.1) = val D (sem_ins i (single c)) (n+e.1) :=
    (gateFalse _ otherFalse).trans (gateFalse _ (otherSame.symm.trans otherFalse)).symm
  have sameW := single_reader_chain_agreement hS (single c) (sem_ins i (single c)) i
    (sem_ins_agree i (single c)) (Relation.ReflTransGen.tail chain ⟨step,one⟩) bound sameGate
  have baseFalse : val D (single c) w = false := by
    cases hv : val D (single c) w with
    | false => rfl
    | true => exact False.elim (absentW (mem_supp.mpr hv))
  exact sameW.symm.trans baseFalse

theorem pilot_nonedge_extension :
    ∀ u v i : Fin 14, hc_adjB u v = false → i ≠ u → i ≠ v →
      ∃ z : Fin 14, hc_adjB i z = true ∧ hc_adjB u z = false ∧ hc_adjB v z = false := by
  decide +kernel

theorem pilot_chain_nonedge_pair_false {D : Dag} (hS : Strict 14 D) (hD : Correct D)
    {i u v : Fin 14} {w : ℕ} (chain : sem_Chain 14 D i.val w)
    (huv : ¬ Adj u v) (hiu : i ≠ u) (hiv : i ≠ v) :
    val D (sem_ind ({u,v} : Finset (Fin 14))) w = false := by
  obtain ⟨z,hiz,huz,hvz⟩ := pilot_nonedge_extension u v i
    (sem_adjB_false.2 huv) hiu hiv
  have hiz' := (hc_adjB_iff _ _).1 hiz
  have huz' := sem_adjB_false.1 huz
  have hvz' := sem_adjB_false.1 hvz
  have independent : ∀ a ∈ ({u,v,z} : Finset (Fin 14)),
      ∀ b ∈ ({u,v,z} : Finset (Fin 14)), ¬ Adj a b := by
    intro a ha b hb
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    · exact adj_irrefl _
    · exact huv
    · exact huz'
    · exact fun h => huv (adj_symm h)
    · exact adj_irrefl _
    · exact hvz'
    · exact fun h => huz' (adj_symm h)
    · exact fun h => hvz' (adj_symm h)
    · exact adj_irrefl _
  have negative := sem_ind_no_edge independent
  have positive : sem_Edge Adj (sem_ins i (sem_ind ({u,v,z} : Finset (Fin 14)))) := by
    refine ⟨i,z,hiz',sem_ins_self _ _,sem_ins_ge _ _ z ?_⟩
    simp [sem_ind]
  have branch_false := (sem_dom_split hS (sem_heawood_comp hD)
    (sem_ind ({u,v,z} : Finset (Fin 14))) i w (sem_chain_dom hS chain)
    negative positive).1
  have monotone : ∀ k : Fin 14, sem_ind ({u,v} : Finset (Fin 14)) k = true →
      sem_ind ({u,v,z} : Finset (Fin 14)) k = true := by
    intro k hk
    simp only [sem_ind,decide_eq_true_eq,Finset.mem_insert,Finset.mem_singleton] at hk ⊢
    rcases hk with rfl | rfl <;> simp
  cases value : val D (sem_ind ({u,v} : Finset (Fin 14))) w with
  | false => rfl
  | true =>
    have bad := val_mono hS _ _ monotone w value
    rw [branch_false] at bad
    exact Bool.noConfusion bad

theorem equality_consumption_before_branch {n : ℕ} {D : Dag} (hS : Strict n D)
    {i : Fin n} (hi : i ∈ ineligSet n D) {e : ℕ × Bool} (he : e ∈ sem_W n D i)
    {b : ℕ} (chain : sem_Chain n D i.val b) (branch : 2 ≤ fanout D b) : n+e.1 ≤ b := by
  obtain ⟨hj,carrier,_⟩ := sem_mem_W.1 he
  have first := sem_inelig_chain hS hi carrier
  have step : sem_step n D (src D e) (n+e.1) := sem_step_src hj e.2
  have one : fanout D (src D e) = 1 := by
    have lower := sem_step_fanout step
    have upper := mem_ineligSet.mp hi _ carrier
    omega
  rcases sem_chain_fork hS first (sem_rtg_mono (fun _ _ h => h.1) chain) with path | ⟨path,ne⟩
  · rcases Relation.ReflTransGen.cases_head path with equal | ⟨w,initial,rest⟩
    · have same := congrArg (fanout D) equal
      omega
    · have equal : n+e.1 = w := sem_step_unique step initial one
      subst w
      exact sem_rtg_le hS (fun _ _ h => h) rest
  · rcases Relation.ReflTransGen.cases_head path with equal | ⟨w,initial,rest⟩
    · exact False.elim (ne equal)
    · have := initial.2
      omega

theorem equality_cf_singleton_pair {c : Fin 14} {l : List ℕ} (hgood : cf_good c l)
    (k : Fin 10) : cof_ext (cf_rho c) (cf_iota l) (single k) =
      sem_ind ({c,cf_iota l k} : Finset (Fin 14)) := by
  have hok : cof_Ok (cf_rho c) (cf_iota l) := ⟨hgood.1,hgood.2.1⟩
  funext u
  have fixed : cf_rho c u = some true ↔ u = c := by
    by_cases equal : u = c <;> simp [cf_rho,equal]
  have support := cof_ext_single hok k u
  rw [fixed] at support
  have other : sem_ind ({c,cf_iota l k} : Finset (Fin 14)) u = true ↔
      u = cf_iota l k ∨ u = c := by simp [sem_ind,or_comm]
  cases first : cof_ext (cf_rho c) (cf_iota l) (single k) u <;>
    cases second : sem_ind ({c,cf_iota l k} : Finset (Fin 14)) u <;> simp_all

theorem equality_cofactor_empty_branch_empty {D : Dag} (hS : Strict 14 D)
    (hD : Correct D) {c i : Fin 14} {l : List ℕ} (hgood : cf_good c l)
    (hi : i ∈ ineligSet 14 D) (hic : i ≠ c) {e : ℕ × Bool} (he : e ∈ sem_W 14 D i)
    (absent : c ∉ supp 14 D (src D (sem_bar e))) {b : ℕ}
    (chain : sem_Chain 14 D i.val b) (branch : 2 ≤ fanout D b) (empty : supp 14 D b = ∅) :
    cof_supp D (cf_rho c) (cf_iota l) b = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.2
  intro k member
  have value := cof_mem_supp.1 member
  rw [equality_cf_singleton_pair hgood k] at value
  by_cases equal : cf_iota l k = i
  · rw [equal] at value
    have assignment : sem_ind ({c,i} : Finset (Fin 14)) = sem_ins i (single c) := by
      funext u
      by_cases hu : u = i <;> simp [sem_ind,sem_ins,single,hu]
    rw [assignment] at value
    have zero := ineligible_consumption_insert_false hS i c hi e he absent b
      (equality_consumption_before_branch hS hi he chain branch) (by rw [empty]; simp)
    rw [zero] at value
    exact Bool.false_ne_true value
  · have free : cf_rho c (cf_iota l k) = none := (hgood.2.1 _).2 ⟨k,rfl⟩
    have distinct : cf_iota l k ≠ c := by
      intro same
      simpa [same,cf_rho] using free
    have nonedge : ¬ Adj c (cf_iota l k) := by
      intro adjacent
      rw [cf_rho,if_neg distinct,if_pos ((hc_adjB_iff _ _).2 adjacent)] at free
      cases free
    have zero := pilot_chain_nonedge_pair_false hS hD chain nonedge hic (Ne.symm equal)
    rw [zero] at value
    exact Bool.false_ne_true value



theorem equality_critical_branch_false {n : ℕ} {D : Dag} (hS : Strict n D)
    (x : Fin n → Bool) (v : Fin n) {b : ℕ}
    (chain : sem_Chain n D v.val b)
    (hfalse : val D x (outW n D) = false)
    (htrue : val D (sem_ins v x) (outW n D) = true) : val D x b = false := by
  cases hb : val D x b with
  | false => rfl
  | true =>
    have hb' : val D (sem_ins v x) b = true :=
      val_mono hS x (sem_ins v x)
        (by intro i hi; by_cases h : i = v <;> simp_all [sem_ins]) b hb
    have same := sem_dom_eq hS x (sem_ins v x) v
      (fun k hk => by simp [sem_ins,hk]) b (sem_chain_dom hS chain) (hb.trans hb'.symm)
    rw [hfalse,htrue] at same
    exact Bool.noConfusion same

theorem equality_cofactor_neighbor_branch_empty {D : Dag} (h : StrictLive 14 D)
    (hD : Correct D) {c z : Fin 14} {l : List ℕ} (hgood : cf_good c l)
    (edge : Adj c z) {b : ℕ} (chain : sem_Chain 14 D z.val b) :
    cof_supp D (cf_rho c) (cf_iota l) b = ∅ := by
  classical
  have hC := sem_heawood_comp hD
  have hok : cof_Ok (cf_rho c) (cf_iota l) := ⟨hgood.1,hgood.2.1⟩
  have truefixed (u : Fin 14) : cf_rho c u = some true ↔ u = c := by
    by_cases equal : u = c
    · simp [cf_rho,equal]
    · simp [cf_rho,equal]
  apply Finset.eq_empty_iff_forall_notMem.2
  intro i member
  let base := cof_ext (cf_rho c) (cf_iota l) (single i)
  have supported (u : Fin 14) : base u = true ↔ u = cf_iota l i ∨ u = c := by
    rw [show base u = cof_ext (cf_rho c) (cf_iota l) (single i) u from rfl,
      cof_ext_single hok,truefixed]
  have free : cf_rho c (cf_iota l i) = none := (hgood.2.1 _).2 ⟨i,rfl⟩
  have distinct : cf_iota l i ≠ c := by
    intro equal
    simpa [equal,cf_rho] using free
  have nonedge : ¬ Adj c (cf_iota l i) := by
    intro adjacent
    rw [cf_rho,if_neg distinct,if_pos ((hc_adjB_iff _ _).2 adjacent)] at free
    cases free
  have zero : val D base (outW 14 D) = false := by
    cases value : val D base (outW 14 D) with
    | false => rfl
    | true =>
      obtain ⟨u,v,adjacent,hu,hv⟩ := (hC base).1 value
      rcases (supported u).1 hu with rfl | rfl <;>
        rcases (supported v).1 hv with rfl | rfl
      · exact (adj_irrefl _ adjacent).elim
      · exact (nonedge (adj_symm adjacent)).elim
      · exact (nonedge adjacent).elim
      · exact (adj_irrefl _ adjacent).elim
  have after : val D (sem_ins z base) (outW 14 D) = true := by
    apply (hC _).2
    refine ⟨c,z,edge,?_,?_⟩
    · have basec : base c = true := (supported c).2 (Or.inr rfl)
      have unequal : c ≠ z := fun equal => adj_irrefl z (equal ▸ edge)
      simpa [sem_ins,unequal] using basec
    · simp [sem_ins]
  have falsebranch := equality_critical_branch_false h.1 base z chain zero after
  have truebranch := cof_mem_supp.1 member
  rw [falsebranch] at truebranch
  exact Bool.false_ne_true truebranch


theorem equality_cofactor_supported_loss {n m : ℕ} {D : Dag} (hS : Strict n D)
    (ρ : Fin n → Option Bool) (ι : Fin m → Fin n)
    (b : Fin n → ℕ) (hb : PureBranch n D b)
    (J : Finset (Fin n)) (Z : Finset ℕ)
    (hJ : ∀ x ∈ J, x ∈ eligSet n D ∧ (⟨b x,0⟩ : Σ _ : ℕ, ℕ) ∉ cof_keptP D ρ ι)
    (hZ : ∀ w ∈ Z, 2 ≤ fanout D w ∧ supp n D w = ∅ ∧ cof_supp D ρ ι w = ∅) :
    cof_surP D ρ ι + J.card + Z.card ≤ totalSurplus n D := by
  classical
  let R := J.image (fun x => (⟨b x,0⟩ : Σ _ : ℕ, ℕ))
  let E := Z.image (fun w => (⟨w,0⟩ : Σ _ : ℕ, ℕ))
  have branch_unit : ∀ w, 2 ≤ fanout D w → (⟨w,0⟩ : Σ _ : ℕ, ℕ) ∈ units n D := by
    intro w hw
    exact mem_units.2 ⟨sb_mem_inner.2 (lt_of_fanout_pos hS (w := w) (by omega)),by change 0+1 < fanout D w; omega⟩
  have injR : Set.InjOn (fun x => (⟨b x,0⟩ : Σ _ : ℕ, ℕ)) (J : Set (Fin n)) := by
    intro x hx y hy eq
    have wires : b x = b y := congrArg Sigma.fst eq
    have same := (hb x (hJ x hx).1).2
    rw [wires,(hb y (hJ y hy).1).2] at same
    exact (Finset.singleton_injective same).symm
  have injE : Function.Injective (fun w => (⟨w,0⟩ : Σ _ : ℕ, ℕ)) :=
    fun _ _ eq => congrArg Sigma.fst eq
  have disjoint : Disjoint R E := by
    apply Finset.disjoint_left.2
    intro u hu hv
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.1 hu
    obtain ⟨w,hw,eq⟩ := Finset.mem_image.1 hv
    have wires : w = b x := congrArg Sigma.fst eq
    have empty := (hZ w hw).2.1
    rw [wires,(hb x (hJ x hx).1).2] at empty
    have : x ∈ (∅ : Finset (Fin n)) := empty ▸ Finset.mem_singleton_self x
    exact Finset.notMem_empty x this
  have sub : R ∪ E ⊆ units n D := by
    intro u hu
    rcases Finset.mem_union.1 hu with hu | hu
    · obtain ⟨x,hx,rfl⟩ := Finset.mem_image.1 hu
      exact branch_unit _ (hb x (hJ x hx).1).1
    · obtain ⟨w,hw,rfl⟩ := Finset.mem_image.1 hu
      exact branch_unit _ (hZ w hw).1
  have lost : ∀ u ∈ R ∪ E, u ∉ cof_keptP D ρ ι := by
    intro u hu
    rcases Finset.mem_union.1 hu with hu | hu
    · obtain ⟨x,hx,rfl⟩ := Finset.mem_image.1 hu
      exact (hJ x hx).2
    · obtain ⟨w,hw,rfl⟩ := Finset.mem_image.1 hu
      exact cof_lostP_of_supp (hZ w hw).2.2
  have bound := cof_surP_add_lost (R ∪ E) sub lost
  have cardR : R.card = J.card := Finset.card_image_of_injOn injR
  have cardE : E.card = Z.card := Finset.card_image_of_injective _ injE
  rw [Finset.card_union_of_disjoint disjoint,cardR,cardE] at bound
  omega

theorem equality_cofactor_reserved_depleted {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b) {c x : Fin 14} {l : List ℕ}
    (hx : x ∈ eligSet 14 D) (hne : x ≠ c)
    (inc : ∀ u ∈ residualUnits 14 D b, x ∈ supp 14 D u.1 → c ∈ supp 14 D u.1)
    (common : ∃ w, x ∈ supp 14 D w ∧ c ∈ supp 14 D w) :
    (⟨b x,0⟩ : Σ _ : ℕ, ℕ) ∉ cof_kept D (cf_rho c) (cf_iota l) := by
  obtain ⟨w,hw⟩ := common
  obtain ⟨z,hxz,hcz⟩ := sem_heawood_gr.2.2.1 x c hne
  obtain ⟨hs1,_,_,e,he,_,hec⟩ :=
    sem_diff_two_exits sem_heawood_gr h (sem_heawood_comp hD) b hb hne hx inc hw hxz hcz
  have hbx : b x ∈ carrierDiff 14 D x c := sem_mem_diff.2 (by
    rw [(hb x hx).2]
    exact ⟨Finset.mem_singleton_self x,fun hcx => hne (Finset.mem_singleton.1 hcx).symm⟩)
  exact cof_lost_of_deg (cof_diff_deplete h.1 (by simp [cf_rho]) hbx (hb x hx).1 hs1 he hec)

theorem equality_missing_branches_distinct {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (P : Finset (Fin 14)) (hP : ∀ a ∈ P, ∀ b ∈ P, ¬ Adj a b)
    {i j : Fin 14} (hne : i ≠ j)
    (hNj : sem_hw_nb j ⊆ P) (missing : ¬ sup_Occ 14 D P (sem_hw_nb i))
    (hNi : sem_hw_nb i ⊆ P) {u v : ℕ}
    (chaini : sem_Chain 14 D i.val u) (chainj : sem_Chain 14 D j.val v) : u ≠ v := by
  intro eq
  obtain ⟨a,ha1,ha2⟩ := nbr_diff_exists j i (Ne.symm hne)
  obtain ⟨k,s,_,_,_,_,hq⟩ := sem_shared_exact sem_heawood_gr h.1 (sem_heawood_comp hD) P hP
    chaini (sem_chain_dom h.1 (eq.symm ▸ chainj)) ⟨a,hNj (hw_mem_nb.2 ha1),ha1,ha2⟩
  apply missing
  refine ⟨src D (k,s),?_⟩
  ext x
  rw [Finset.mem_inter,hw_mem_nb]
  exact ⟨fun hx => (hq x hx.2).1 hx.1,
    fun hx => ⟨(hq x (hNi (hw_mem_nb.2 hx))).2 hx,hNi (hw_mem_nb.2 hx)⟩⟩



theorem equality_missing_empty_branch {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (P : Finset (Fin 14)) (hP : ∀ a ∈ P, ∀ b ∈ P, ¬ Adj a b) {i : Fin 14}
    (hi : i ∈ ineligSet 14 D) (hNi : sem_hw_nb i ⊆ P)
    (missing : ¬ sup_Occ 14 D P (sem_hw_nb i)) :
    ∃ w, sem_Chain 14 D i.val w ∧ 2 ≤ fanout D w ∧ supp 14 D w = ∅ := by
  rcases sem_inelig_reach sem_heawood_gr h (sem_heawood_comp hD) hi with chain | branch
  · obtain ⟨j,s,_,_,_,hq⟩ := sem_exact_nbhd sem_heawood_gr h.1 (sem_heawood_comp hD) P hP chain
    apply False.elim
    apply missing
    refine ⟨src D (j,s),?_⟩
    ext x
    rw [Finset.mem_inter,hw_mem_nb]
    exact ⟨fun hx => (hq x hx.2).1 hx.1,
      fun hx => ⟨(hq x (hNi (hw_mem_nb.2 hx))).2 hx,hNi (hw_mem_nb.2 hx)⟩⟩
  · exact branch

theorem equality_m9_center_absent {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b)
    (pos : Fin 14 → ℕ × Bool) (hpos : k4_Pos 14 HG D pos)
    (hI : ineligSet 14 D = {0,1,2,5,11}) (zero : ru D b 3 = ∅)
    {i : Fin 14} (hi : i ∈ ({0,1,2,5} : Finset (Fin 14))) :
    (3 : Fin 14) ∉ supp 14 D (src D (pos i)) := by
  intro member
  have hi' : i ∈ ineligSet 14 D := by
    rw [hI]
    exact (by decide : ({0,1,2,5} : Finset (Fin 14)) ⊆ {0,1,2,5,11}) hi
  have h11 : (11 : Fin 14) ∈ ineligSet 14 D := by rw [hI]; decide
  have hel7 : (7 : Fin 14) ∈ eligSet 14 D := by
    by_contra hn
    have := hI ▸ sem_mem_inelig.2 hn
    exact (by decide : (7 : Fin 14) ∉ ({0,1,2,5,11} : Finset (Fin 14))) this
  have hj : ∀ j ∈ ({11,i} : Finset (Fin 14)),
      j ∈ ineligSet 14 D ∧ (3 : Fin 14) ∈ supp 14 D (src D (pos j)) := by
    intro j hj
    rcases Finset.mem_insert.1 hj with rfl | hj
    · exact ⟨h11,(hpos.1 11 h11).2.2.1 3 (by decide)⟩
    · have eq := Finset.mem_singleton.1 hj
      subst j
      exact ⟨hi',member⟩
  have bound := equality_assigned_budget_extra h hD b hb pos hpos {11,i} hj hel7 (by decide : Adj 3 7)
  have ne : (11 : Fin 14) ≠ i := by
    intro eq
    rw [← eq] at hi
    exact (by decide : (11 : Fin 14) ∉ ({0,1,2,5} : Finset (Fin 14))) hi
  rw [Finset.card_pair ne,zero,Finset.card_empty] at bound
  omega

theorem equality_m9_cofactor_supported_upper {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h14 : totalSurplus 14 D ≤ 14) (b : Fin 14 → ℕ) (first : sem_FirstBranch 14 D b)
    (hI : ineligSet 14 D = {0,1,2,5,11})
    (zeros : ∀ x ∈ ({3,4,6} : Finset (Fin 14)), ru D b x = ∅)
    (missing2 : ¬ sup_Occ 14 D mx_L (sem_hw_nb 2))
    (missing5 : ¬ sup_Occ 14 D mx_L (sem_hw_nb 5)) :
    cof_surP D (cf_rho 3) (cf_iota cfL3) ≤ 7 := by
  classical
  have hb := sem_firstBranch_pure first
  obtain ⟨pos,hpos⟩ := k4_assigned sem_heawood_gr h (sem_heawood_comp hD)
  have eligible : ∀ x ∈ ({3,4,6,7,12} : Finset (Fin 14)), x ∈ eligSet 14 D := by
    intro x hx
    by_contra hn
    exact Finset.disjoint_left.1
      (by decide : Disjoint ({3,4,6,7,12} : Finset (Fin 14)) {0,1,2,5,11}) hx
      (hI ▸ sem_mem_inelig.2 hn)
  have ineligible : ∀ x ∈ ({2,5,11} : Finset (Fin 14)), x ∈ ineligSet 14 D := by
    intro x hx
    rw [hI]
    exact (by decide : ({2,5,11} : Finset (Fin 14)) ⊆ {0,1,2,5,11}) hx
  have Pind : ∀ a ∈ mx_L, ∀ b ∈ mx_L, ¬ Adj a b := by decide +kernel
  have n2 : sem_hw_nb 2 ⊆ mx_L := by decide
  have n5 : sem_hw_nb 5 ⊆ mx_L := by decide
  obtain ⟨u,cu,bu,eu⟩ := equality_missing_empty_branch h hD mx_L Pind
    (ineligible 2 (by decide)) n2 missing2
  obtain ⟨v,cv,bv,ev⟩ := equality_missing_empty_branch h hD mx_L Pind
    (ineligible 5 (by decide)) n5 missing5
  have different : u ≠ v := equality_missing_branches_distinct h hD mx_L Pind
    (by decide : (2 : Fin 14) ≠ 5) n5 missing2 n2 cu cv
  have empty_transfer : ∀ i ∈ ({2,5} : Finset (Fin 14)), ∀ w,
      sem_Chain 14 D i.val w → 2 ≤ fanout D w → supp 14 D w = ∅ →
        cof_supp D (cf_rho 3) (cf_iota cfL3) w = ∅ := by
    intro i hi w chain branch empty
    have hii : i ∈ ineligSet 14 D := by
      rw [hI]
      exact (by decide : ({2,5} : Finset (Fin 14)) ⊆ {0,1,2,5,11}) hi
    have wi : sem_bar (pos i) ∈ sem_W 14 D i := by
      rw [as_W h hD hpos hii]
      exact Finset.mem_singleton_self _
    apply equality_cofactor_empty_branch_empty h.1 hD cf3_good hii
      ((by decide : ∀ i ∈ ({2,5} : Finset (Fin 14)), i ≠ 3) i hi) wi _ chain branch empty
    rw [sem_bar_bar]
    exact equality_m9_center_absent h hD b hb pos hpos hI (zeros 3 (by decide))
      ((by decide : ({2,5} : Finset (Fin 14)) ⊆ {0,1,2,5}) hi)
  have lost : ∀ x ∈ ({3,4,6,7,12} : Finset (Fin 14)),
      x ∈ eligSet 14 D ∧ (⟨b x,0⟩ : Σ _ : ℕ, ℕ) ∉ cof_keptP D (cf_rho 3) (cf_iota cfL3) := by
    intro x hx
    refine ⟨eligible x hx,?_⟩
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · intro hk
      have member : (3 : Fin 14) ∈ supp 14 D (b 3) := by
        rw [(hb 3 (eligible 3 (by decide))).2]
        exact Finset.mem_singleton_self _
      exact cof_lost_of_true h.1 (by simp [cf_rho]) member (cof_keptP_sub hk)
    · intro hk
      have depleted := equality_cofactor_reserved_depleted (l := cfL3) h hD b hb
        (eligible 4 (by decide)) (by decide : (4 : Fin 14) ≠ 3)
        (by
          intro q hq h4
          have mem := mem_ru.2 ⟨hq,h4⟩
          rw [zeros 4 (by decide)] at mem
          exact (Finset.notMem_empty _ mem).elim)
        ⟨src D (pos 11),(hpos.1 11 (ineligible 11 (by decide))).2.2.1 4 (by decide),
          (hpos.1 11 (ineligible 11 (by decide))).2.2.1 3 (by decide)⟩
      exact depleted (cof_keptP_sub hk)
    · intro hk
      have depleted := equality_cofactor_reserved_depleted (l := cfL3) h hD b hb
        (eligible 6 (by decide)) (by decide : (6 : Fin 14) ≠ 3)
        (by
          intro q hq h6
          have mem := mem_ru.2 ⟨hq,h6⟩
          rw [zeros 6 (by decide)] at mem
          exact (Finset.notMem_empty _ mem).elim)
        ⟨src D (pos 11),(hpos.1 11 (ineligible 11 (by decide))).2.2.1 6 (by decide),
          (hpos.1 11 (ineligible 11 (by decide))).2.2.1 3 (by decide)⟩
      exact depleted (cof_keptP_sub hk)
    · exact cof_lostP_of_supp (equality_cofactor_neighbor_branch_empty h hD cf3_good
        (by decide : Adj 3 7) (first 7 (eligible 7 (by decide))).2.2)
    · exact cof_lostP_of_supp (equality_cofactor_neighbor_branch_empty h hD cf3_good
        (by decide : Adj 3 12) (first 12 (eligible 12 (by decide))).2.2)
  have bound := equality_cofactor_supported_loss h.1 (cf_rho 3) (cf_iota cfL3) b hb
    {3,4,6,7,12} {u,v} lost (by
      intro w hw
      rcases Finset.mem_insert.1 hw with eq | hw
      · subst w
        exact ⟨bu,eu,empty_transfer 2 (by decide) u cu bu eu⟩
      · have eq := Finset.mem_singleton.1 hw
        subst w
        exact ⟨bv,ev,empty_transfer 5 (by decide) v cv bv ev⟩)
  rw [show ({3,4,6,7,12} : Finset (Fin 14)).card = 5 from rfl,
    Finset.card_pair different] at bound
  omega



theorem equality_m9_normal_coordinates {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h14 : totalSurplus 14 D ≤ 14) (b : Fin 14 → ℕ) (hb : PureBranch 14 D b)
    (hI : ineligSet 14 D = {0,1,2,5,11}) (three : (residualUnits 14 D b).card = 3) :
    ∃ a : Fin 3 → (Σ _ : ℕ, ℕ), Function.Injective a ∧
      (∀ u, u ∈ residualUnits 14 D b ↔ ∃ k, a k = u) ∧
      (equality_coordinate_set (D := D) a 7 = {0} ∨
        equality_coordinate_set (D := D) a 7 = {0,1}) := by
  classical
  let S := residualUnits 14 D b
  let e : (↑S) ≃ Fin 3 := Fintype.equivFinOfCardEq (by rw [Fintype.card_coe]; exact three)
  let a : Fin 3 → (Σ _ : ℕ, ℕ) := fun k => (e.symm k).val
  have injective : Function.Injective a := fun i j equal => e.symm.injective (Subtype.ext equal)
  have onto : ∀ u, u ∈ residualUnits 14 D b ↔ ∃ k, a k = u := by
    intro u
    constructor
    · intro member
      exact ⟨e ⟨u,member⟩,by simp [a]⟩
    · rintro ⟨k,rfl⟩
      exact (e.symm k).property
  obtain ⟨pos,hpos⟩ := k4_assigned sem_heawood_gr h (sem_heawood_comp hD)
  have proper := equality_m9_coordinate_proper h hD h14 b hb pos hpos hI a injective onto 0
  change equality_coordinate_set (D := D) a 7 ≠ Finset.univ at proper
  have small := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2
    ⟨Finset.subset_univ (equality_coordinate_set (D := D) a 7),proper⟩)
  have card := equality_coordinate_card a injective onto 7
  have positive := equality_m9_positive h hD b hb pos hpos hI 0
  change 0 < (ru D b 7).card at positive
  simp only [Finset.card_univ,Fintype.card_fin] at small
  obtain ⟨a',inj',onto',first⟩ := equality_residual_coordinates three (by omega)
  exact ⟨a',inj',onto',first⟩


theorem equality_m9_zero_points_of_certificate
    (certificate : ∀ (r : Fin 6 → Fin 8) (a b : Fin 3) (T : Fin 8),
      (r 0 = 1 ∨ r 0 = 3) → m9_normal r a b = true → m9_pointAllowed r a b T = false)
    {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (h14 : totalSurplus 14 D ≤ 14)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b)
    (hI : ineligSet 14 D = {0,1,2,5,11})
    (missing2 : ¬ sup_Occ 14 D mx_L (sem_hw_nb 2))
    (missing5 : ¬ sup_Occ 14 D mx_L (sem_hw_nb 5))
    (protects : ∀ i ∈ ({0,1} : Finset (Fin 14)), ∀ w,
      Relation.ReflTransGen (sem_step 14 D) i.val w → fanout D w ≤ 1)
    (a : Fin 3 → (Σ _ : ℕ, ℕ)) (injective : Function.Injective a)
    (onto : ∀ u, u ∈ residualUnits 14 D b ↔ ∃ k, a k = u)
    (first : equality_coordinate_set (D := D) a 7 = {0} ∨
      equality_coordinate_set (D := D) a 7 = {0,1}) :
    ∀ z ∈ ({3,4,6} : Finset (Fin 14)), ru D b z = ∅ := by
  classical
  obtain ⟨α,β,normal,points⟩ := equality_m9_all_constraints h hD h14 b hb hI
    missing2 missing5 protects a injective onto
  intro z hz
  have zero : equality_coordinate_set (D := D) a z = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.2
    intro k member
    have positive : (equality_coordinate_set (D := D) a z).Nonempty := ⟨k,member⟩
    exact m9_no_point_constraints_of_certificate certificate
      (fun t => equality_coordinate_set (D := D) a (equality_m9_line t)) α β
      (equality_coordinate_set (D := D) a z) first normal (points z hz positive)
  have card := equality_coordinate_card a injective onto z
  rw [zero,Finset.card_empty] at card
  exact Finset.card_eq_zero.1 card.symm


theorem equality_m9_two_missing_impossible_of_certificate
    (certificate : ∀ (r : Fin 6 → Fin 8) (a b : Fin 3) (T : Fin 8),
      (r 0 = 1 ∨ r 0 = 3) → m9_normal r a b = true → m9_pointAllowed r a b T = false)
    {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (h14 : totalSurplus 14 D ≤ 14)
    (hI : ineligSet 14 D = {0,1,2,5,11})
    (hM : equality_missing_cap D = {2,5}) : False := by
  classical
  have missing2 : ¬ sup_Occ 14 D mx_L (sem_hw_nb 2) := by
    have member : (2 : Fin 14) ∈ equality_missing_cap D := by rw [hM]; decide
    exact (Finset.mem_filter.1 member).2
  have missing5 : ¬ sup_Occ 14 D mx_L (sem_hw_nb 5) := by
    have member : (5 : Fin 14) ∈ equality_missing_cap D := by rw [hM]; decide
    exact (Finset.mem_filter.1 member).2
  have protects : ∀ i ∈ ({0,1} : Finset (Fin 14)), ∀ w,
      Relation.ReflTransGen (sem_step 14 D) i.val w → fanout D w ≤ 1 := by
    intro i hi
    apply equality_chain_protected h.1
    apply equality_mixed_cap_occ_chain h hD h14 hI
      ((by decide : ({0,1} : Finset (Fin 14)) ⊆ {0,1,2,5}) hi)
    by_contra missing
    have member : i ∈ equality_missing_cap D := Finset.mem_filter.2
      ⟨((by decide : ({0,1} : Finset (Fin 14)) ⊆ {0,1,2,5}) hi),missing⟩
    rw [hM] at member
    exact Finset.disjoint_left.1 (by decide : Disjoint ({0,1} : Finset (Fin 14)) {2,5}) hi member
  obtain ⟨b,first⟩ := sem_exists_firstBranch sem_heawood_gr h.1 (sem_heawood_comp hD)
  have hb := sem_firstBranch_pure first
  have total := totalSurplus_split 14 D
  have zero := equality_mixed_cap_saturated h hD h14 hI
  rw [hM,show ({2,5} : Finset (Fin 14)).card = 2 from rfl] at zero
  have eligible := inelig_card_add 14 D
  rw [hI,show ({0,1,2,5,11} : Finset (Fin 14)).card = 5 from rfl] at eligible
  have lower := mx_star h hD (by rw [hI]; decide)
  have residual := card_residual h.1 b hb
  have three : (residualUnits 14 D b).card = 3 := by omega
  obtain ⟨a,injective,onto,normalized⟩ := equality_m9_normal_coordinates h hD h14 b hb hI three
  have zeros := equality_m9_zero_points_of_certificate certificate h hD h14 b hb hI missing2 missing5
    protects a injective onto normalized
  have upper := equality_m9_cofactor_supported_upper h hD h14 b first hI zeros missing2 missing5
  have lower := equality_cf_supported_eight h hD cf3_good
    (by change ∀ w, Relation.ReflTransGen (sem_step 14 D) 0 w → fanout D w ≤ 1
        exact protects 0 (by decide))
    (by change ∀ w, Relation.ReflTransGen (sem_step 14 D) 1 w → fanout D w ≤ 1
        exact protects 1 (by decide))
  omega

theorem equality_occurrence_relabel {n : ℕ} (σ : Equiv.Perm (Fin n))
    {D : Dag} (h : Strict n D) (P M : Finset (Fin n)) :
    sup_Occ n (relabel σ D) (P.image σ) (M.image σ) ↔ sup_Occ n D P M := by
  classical
  constructor
  · rintro ⟨w,hw⟩
    let v := liftP σ.symm w
    refine ⟨v,Finset.image_injective σ.injective ?_⟩
    rw [Finset.image_inter _ _ σ.injective,← relabel_supp σ h v]
    have inv : liftP σ v = w := tr_liftP_inv' σ w
    rw [inv]
    exact hw
  · rintro ⟨w,hw⟩
    refine ⟨liftP σ w,?_⟩
    rw [relabel_supp σ h w,← Finset.image_inter _ _ σ.injective,hw]

def equality_m9_pair (k : Fin 6) : Finset (Fin 14) := ![{0,1},{0,2},{0,5},{1,2},{1,5},{2,5}] k

def equality_m9_permutation (k : Fin 6) : Fin 14 → Fin 14 :=
  ![hc_ofList [2,5,0,3,4,1,6,12,8,9,13,11,7,10],
    hc_ofList [5,1,2,6,4,0,3,9,12,7,10,11,8,13],
    hc_ofList [2,1,0,4,3,5,6,13,8,9,12,11,10,7],
    hc_ofList [0,5,2,4,3,1,6,10,8,9,7,11,13,12],
    hc_ofList [0,2,1,6,4,5,3,8,7,12,10,11,9,13],
    hc_ofList [0,1,2,3,4,5,6,7,8,9,10,11,12,13]] k

def equality_m9_automorphism (k : Fin 6) : Equiv.Perm (Fin 14) :=
  ⟨equality_m9_permutation k,equality_m9_permutation k,
    by intro i; revert i k; decide +kernel,
    by intro i; revert i k; decide +kernel⟩

theorem equality_m9_automorphism_aut (k : Fin 6) : IsAut (equality_m9_automorphism k) := by
  apply hc_isAut_of
  revert k
  decide +kernel

theorem equality_m9_automorphism_geometry : ∀ k : Fin 6,
    ({0,1,2,5} : Finset (Fin 14)).image (equality_m9_automorphism k) = {0,1,2,5} ∧
    ({0,1,2,5,11} : Finset (Fin 14)).image (equality_m9_automorphism k) = {0,1,2,5,11} ∧
    mx_L.image (equality_m9_automorphism k) = mx_L ∧
    (equality_m9_pair k).image (equality_m9_automorphism k) = {2,5} ∧
    ∀ i : Fin 14, (sem_hw_nb i).image (equality_m9_automorphism k) =
      sem_hw_nb (equality_m9_automorphism k i) := by
  decide +kernel

theorem equality_m9_missing_relabel {D : Dag} (h : Strict 14 D) (k : Fin 6) :
    equality_missing_cap (relabel (equality_m9_automorphism k) D) =
      (equality_missing_cap D).image (equality_m9_automorphism k) := by
  classical
  let σ := equality_m9_automorphism k
  have geo := equality_m9_automorphism_geometry k
  have member (i : Fin 14) : σ i ∈ ({0,1,2,5} : Finset (Fin 14)) ↔
      i ∈ ({0,1,2,5} : Finset (Fin 14)) := by
    constructor
    · intro hi
      have im : σ i ∈ ({0,1,2,5} : Finset (Fin 14)).image σ := by
        rw [geo.1]
        exact hi
      obtain ⟨j,hj,equal⟩ := Finset.mem_image.1 im
      exact σ.injective equal ▸ hj
    · intro hi
      have im : σ i ∈ ({0,1,2,5} : Finset (Fin 14)).image σ :=
        Finset.mem_image.2 ⟨i,hi,rfl⟩
      rwa [geo.1] at im
  have transfer (i : Fin 14) :
      σ i ∈ equality_missing_cap (relabel σ D) ↔ i ∈ equality_missing_cap D := by
    have occurrence := equality_occurrence_relabel σ h mx_L (sem_hw_nb i)
    rw [geo.2.2.1,geo.2.2.2.2 i] at occurrence
    simp only [equality_missing_cap,Finset.mem_filter]
    exact and_congr (member i) (not_congr occurrence)
  ext j
  constructor
  · intro hj
    refine Finset.mem_image.2 ⟨σ.symm j,?_,σ.apply_symm_apply j⟩
    apply (transfer (σ.symm j)).1
    simpa only [Equiv.apply_symm_apply] using hj
  · intro hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.1 hj
    exact (transfer i).2 hi

theorem equality_m9_any_two_missing_of_canonical
    (canonical : ∀ {D : Dag}, StrictLive 14 D → Correct D → totalSurplus 14 D ≤ 14 →
      ineligSet 14 D = {0,1,2,5,11} → equality_missing_cap D = {2,5} → False)
    {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (h14 : totalSurplus 14 D ≤ 14)
    (hI : ineligSet 14 D = {0,1,2,5,11})
    (two : (equality_missing_cap D).card = 2) : False := by
  classical
  have sub : equality_missing_cap D ⊆ ({0,1,2,5} : Finset (Fin 14)) := Finset.filter_subset _ _
  have shapes : ∀ M : Finset (Fin 14), M ⊆ ({0,1,2,5} : Finset (Fin 14)) →
      M.card = 2 → ∃ k : Fin 6, M = equality_m9_pair k := by
    have enumeration : ({0,1,2,5} : Finset (Fin 14)).powersetCard 2 =
        Finset.univ.image equality_m9_pair := by decide +kernel
    intro M subset card
    have member := Finset.mem_powersetCard.2 ⟨subset,card⟩
    rw [enumeration] at member
    obtain ⟨k,_,equal⟩ := Finset.mem_image.1 member
    exact ⟨k,equal.symm⟩
  obtain ⟨k,hM⟩ := shapes _ sub two
  obtain ⟨h',hD',_,total,_,_,_,ineligible⟩ :=
    heawood_relabel (equality_m9_automorphism k) (equality_m9_automorphism_aut k) h hD
  apply canonical h' hD'
    (by rw [total]; exact h14)
  · rw [ineligible,hI]
    exact (equality_m9_automorphism_geometry k).2.1
  · rw [equality_m9_missing_relabel h.1 k,hM]
    exact (equality_m9_automorphism_geometry k).2.2.2.1

theorem equality_m9_two_missing_impossible {D : Dag}
    (h : StrictLive 14 D) (hD : Correct D) (h14 : totalSurplus 14 D ≤ 14)
    (hI : ineligSet 14 D = {0,1,2,5,11})
    (hM : equality_missing_cap D = {2,5}) : False :=
  equality_m9_two_missing_impossible_of_certificate m9_point_empty h hD h14 hI hM

theorem equality_m9_any_two_missing_impossible {D : Dag}
    (h : StrictLive 14 D) (hD : Correct D) (h14 : totalSurplus 14 D ≤ 14)
    (hI : ineligSet 14 D = {0,1,2,5,11})
    (two : (equality_missing_cap D).card = 2) : False :=
  equality_m9_any_two_missing_of_canonical (fun h hD h14 hI hM =>
    equality_m9_two_missing_impossible h hD h14 hI hM) h hD h14 hI two

end PEqualNP.Outside.L_meta_6659_aux

namespace PEqualNP.Outside.L_meta_6659_aux

noncomputable def equality_mask_pull (f : Fin 7 → Fin 14) (M : Finset (Fin 14)) :
    Finset (Fin 7) := by
  classical
  exact Finset.univ.filter (fun k => f k ∈ M)

theorem equality_mask_pull_image (f : Fin 7 → Fin 14) (P : Finset (Fin 14))
    (range : Finset.univ.image f = P) {M : Finset (Fin 14)} (sub : M ⊆ P) :
    (equality_mask_pull f M).image f = M := by
  classical
  ext a
  constructor
  · intro ha
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.1 ha
    exact (Finset.mem_filter.1 hk).2
  · intro ha
    have hp : a ∈ Finset.univ.image f := by rw [range]; exact sub ha
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.1 hp
    exact Finset.mem_image.2 ⟨k,Finset.mem_filter.2 ⟨Finset.mem_univ _,ha⟩,rfl⟩


def equality_mask_parent (Q : Finset (Fin 7) → Prop) (T : Finset (Fin 7)) : Prop :=
  (∃ A, Q A ∧ A.card = 2 ∧ A ⊆ T) ∨
    (∃ A, Q A ∧ A.card = 4 ∧ T ⊆ A) ∨
    (∃ A B, A ≠ B ∧ Q A ∧ Q B ∧ A.card = 5 ∧ B.card = 5 ∧
      T ⊆ A ∧ T ⊆ B ∧ A ∩ B = T)

theorem equality_occurring_parent_pull_subset {D : Dag} (hS : Strict 14 D)
    (f : Fin 7 → Fin 14) (injective : Function.Injective f) (P R : Finset (Fin 14)) (subrange : P ⊆ R)
    (range : Finset.univ.image f = R) (T : Finset (Fin 7)) (hT : T.card = 3)
    (occur : sup_Occ 14 D P (T.image f)) :
    equality_mask_parent (fun M => sup_Occ 14 D P (M.image f)) T := by
  classical
  have p7 : P.card ≤ 7 := by
    have bound := Finset.card_le_card subrange
    rw [← range,Finset.card_image_of_injective _ injective] at bound
    simpa only [Finset.card_univ,Fintype.card_fin] using bound
  have imageCard : (T.image f).card = 3 := by
    rw [Finset.card_image_of_injective _ injective]
    exact hT
  have back (A : Finset (Fin 14)) (hA : sup_Occ 14 D P A) :
      (equality_mask_pull f A).image f = A :=
    equality_mask_pull_image f R range (fun x hx => subrange (sup_occ_sub hA hx))
  have card (A : Finset (Fin 14)) (hA : sup_Occ 14 D P A) :
      (equality_mask_pull f A).card = A.card := by
    rw [← Finset.card_image_of_injective _ injective,back A hA]
  rcases sup_triple_parent hS p7 imageCard occur with
    ⟨A,hA,ca,sa⟩ | ⟨A,hA,ca,sa⟩ | ⟨A,B,ne,hA,hB,ca,cb,_,_,inter⟩
  · refine Or.inl ⟨equality_mask_pull f A,?_,?_,?_⟩
    · change sup_Occ 14 D P ((equality_mask_pull f A).image f)
      rwa [back A hA]
    · rw [card A hA,ca]
    · apply (Finset.image_subset_image_iff injective).1
      rwa [back A hA]
  · refine Or.inr (Or.inl ⟨equality_mask_pull f A,?_,?_,?_⟩)
    · change sup_Occ 14 D P ((equality_mask_pull f A).image f)
      rwa [back A hA]
    · rw [card A hA,ca]
    · apply (Finset.image_subset_image_iff injective).1
      rwa [back A hA]
  · have eq : equality_mask_pull f A ∩ equality_mask_pull f B = T := by
      apply Finset.image_injective injective
      rw [Finset.image_inter _ _ injective,back A hA,back B hB,inter]
    refine Or.inr (Or.inr ⟨equality_mask_pull f A,equality_mask_pull f B,?_,?_,?_,?_,?_,?_,?_,eq⟩)
    · intro same
      apply ne
      rw [← back A hA,← back B hB,same]
    · change sup_Occ 14 D P ((equality_mask_pull f A).image f)
      rwa [back A hA]
    · change sup_Occ 14 D P ((equality_mask_pull f B).image f)
      rwa [back B hB]
    · rw [card A hA,ca]
    · rw [card B hB,cb]
    · rw [← eq]
      exact Finset.inter_subset_left
    · rw [← eq]
      exact Finset.inter_subset_right


theorem equality_count_mask_family {n : ℕ} {D : Dag} (hS : Strict n D)
    (P : Finset (Fin n)) (L Y : Finset (Finset (Fin n)))
    (hY : ∀ M ∈ Y, 2 ≤ M.card ∧ sup_Occ n D P M)
    (hYpair : ∀ M ∈ Y, M.card = 2 → ∃ T ∈ L, M ⊆ T)
    (E : Finset (ℕ × Bool))
    (hE : ∀ e ∈ E, e ∈ exitArcs n D (carrierT n D P) ∧ 3 ≤ (supp n D (src D e) ∩ P).card)
    (Lab : Finset (Fin n)) (U : Fin n → Finset (Fin n))
    (hw : ∀ f ∈ Lab, ∃ e, sup_Wit n D P (U f) f e)
    (hUL : ∀ f ∈ Lab, ∀ T ∈ L, (U f ∩ T).card ≤ 1) :
    Y.card + E.card + Lab.card ≤
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
  let X := (Lab \ S).image pr
  have hXpair : ∀ M ∈ X, M.card = 2 ∧ sup_Occ n D P M ∧ ∀ T ∈ L, ¬ M ⊆ T := by
    intro M hM
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.1 hM
    obtain ⟨hsub,hcard,_,hocc⟩ := hpr f hf
    refine ⟨hcard,hocc,?_⟩
    intro T hT hMT
    have lower := Finset.card_le_card (Finset.subset_inter hsub hMT)
    have upper := hUL f (Finset.mem_sdiff.1 hf).1 T hT
    omega
  have disjoint : Disjoint Y X := by
    apply Finset.disjoint_left.2
    intro M hMY hMX
    obtain ⟨T,hT,hMT⟩ := hYpair M hMY (hXpair M hMX).1
    exact (hXpair M hMX).2.2 T hT hMT
  have hX : Y.card + X.card ≤ (sup_big n D P).card := by
    have bound := sup_card_le_big hS P (Y ∪ X) (by
      intro M hM
      rcases Finset.mem_union.1 hM with hMY | hMX
      · exact hY M hMY
      · exact ⟨(hXpair M hMX).1.ge,(hXpair M hMX).2.1⟩)
    rwa [Finset.card_union_of_disjoint disjoint] at bound
  have hcnt := sup_count hS P E hE Lab S U wit hwit hSL (fun f hf =>
    sup_wit_single (hwit f (hSL hf)) (Finset.mem_filter.1 hf).2)
  have hfib : (Lab \ S).card ≤ 2 * X.card := by
    refine Finset.card_le_mul_card_image _ 2 (fun M _ => ?_)
    by_cases hne : ((Lab \ S).filter (fun f => pr f = M)).Nonempty
    · obtain ⟨g,hg⟩ := hne
      rw [Finset.mem_filter] at hg
      have hM2 : M.card = 2 := hg.2 ▸ (hpr g hg.1).2.1
      rw [← hM2]
      refine Finset.card_le_card (fun f hf => ?_)
      rw [Finset.mem_filter] at hf
      exact hf.2 ▸ (hpr f hf.1).2.2.1
    · rw [Finset.not_nonempty_iff_eq_empty.1 hne]
      simp
  have split := Finset.card_sdiff_add_card_eq_card hSL
  omega

theorem equality_hw_mask_family {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (P : Finset (Fin 14))
    (hPl : P ⊆ sem_hw_opp 0) (hPe : P ⊆ eligSet 14 D) (Oc Ct I : Finset (Fin 14))
    (hOc : ∀ i ∈ Oc, sem_hw_nb i ⊆ P ∧ sup_Occ 14 D P (sem_hw_nb i))
    (hCt : ∀ c ∈ Ct, c ∉ Oc ∧ ((sem_hw_nb c ∩ P).card ≤ 2 ∨
      (sem_hw_nb c ⊆ P ∧ ¬ sup_Occ 14 D P (sem_hw_nb c))))
    (hI : ∀ i ∈ I, i ∈ ineligSet 14 D ∧ sem_hw_nb i ⊆ P)
    (Y : Finset (Finset (Fin 14)))
    (hY : ∀ M ∈ Y, 2 ≤ M.card ∧ sup_Occ 14 D P M)
    (hYpair : ∀ M ∈ Y, M.card = 2 → ∃ i ∈ Oc, M ⊆ sem_hw_nb i) :
    Y.card + I.card + (Ct.biUnion (fun c => sem_hw_nb c ∩ P)).card +
      (eligSet 14 D).card ≤ 2 * P.card + Bplus 14 D := by
  classical
  have hG := sem_heawood_gr
  have hC := sem_heawood_comp hD
  obtain ⟨b, hb⟩ := exists_pureBranch h hD
  have hPi : ∀ a ∈ P, ∀ b ∈ P, ¬ Adj a b :=
    fun a ha b hb => sem_hw_opp_indep 0 a (hPl ha) b (hPl hb)
  obtain ⟨E, hEc, hE⟩ := sup_assigned_exits hG h hC P I (fun i hi =>
    ⟨(hI i hi).1, sem_hw_nb i, (hI i hi).2, (degree_three i).ge, fun a ha => hw_mem_nb.1 ha⟩)
  have hlab : ∀ f ∈ Ct.biUnion (fun c => sem_hw_nb c ∩ P), ∃ c ∈ Ct, f ∈ sem_hw_nb c ∩ P :=
    fun f hf => Finset.mem_biUnion.1 hf
  choose! ct hct using hlab
  have hmain := equality_count_mask_family h.1 P (Oc.image sem_hw_nb) Y hY
    (fun M hM hM2 => by
      obtain ⟨i,hi,hsub⟩ := hYpair M hM hM2
      exact ⟨sem_hw_nb i,Finset.mem_image.2 ⟨i,hi,rfl⟩,hsub⟩)
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
  rw [hEc] at hmain
  omega


def equality_m9_full_line (i : Fin 7) : Fin 14 := Fin.natAdd 7 i

theorem equality_m9_one_missing_family {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hI : ineligSet 14 D = {0,1,2,5,11}) (hM : equality_missing_cap D = {5}) :
    ∃ Y : Finset (Finset (Fin 14)), 7 ≤ Y.card ∧
      ∀ M ∈ Y, 2 ≤ M.card ∧ sup_Occ 14 D mx_L M ∧
        (M.card = 2 → ∃ i ∈ ({0,1,2} : Finset (Fin 14)), M ⊆ sem_hw_nb i) := by
  classical
  let f := equality_m9_full_line
  let Q := fun M : Finset (Fin 7) => sup_Occ 14 D mx_L (M.image f)
  have inj : Function.Injective f := by
    intro i j equal
    apply Fin.ext
    have eq := congrArg (Fin.val : Fin 14 → ℕ) equal
    change 7+i.val = 7+j.val at eq
    omega
  have range : Finset.univ.image f = sem_hw_opp 0 := by decide +kernel
  have subrange : mx_L ⊆ sem_hw_opp 0 := by decide
  have geometry : (∀ i : Fin 3, (cap7_triple i).image f = sem_hw_nb (![0,1,2] i)) ∧
      cap7_missing.image f = sem_hw_nb 5 := by decide +kernel
  have occurs (i : Fin 14) (hi : i ∈ ({0,1,2} : Finset (Fin 14))) :
      sup_Occ 14 D mx_L (sem_hw_nb i) := by
    by_contra absent
    have member : i ∈ equality_missing_cap D := Finset.mem_filter.2
      ⟨(by decide : ({0,1,2} : Finset (Fin 14)) ⊆ {0,1,2,5}) hi,absent⟩
    rw [hM] at member
    exact Finset.disjoint_left.1 (by decide : Disjoint ({0,1,2} : Finset (Fin 14)) {5}) hi member
  have base (i : Fin 3) : Q (cap7_triple i) := by
    change sup_Occ 14 D mx_L ((cap7_triple i).image f)
    rw [geometry.1 i]
    exact occurs _ ((by decide : ∀ i : Fin 3, (![0,1,2] i : Fin 14) ∈ ({0,1,2} : Finset (Fin 14))) i)
  have parents (i : Fin 3) : cap7_Parent Q (cap7_triple i) := by
    change equality_mask_parent Q (cap7_triple i)
    exact equality_occurring_parent_pull_subset h.1 f inj mx_L (sem_hw_opp 0)
      subrange range (cap7_triple i) (cap7_triple_card i) (base i)
  obtain ⟨pos,hpos⟩ := k4_assigned sem_heawood_gr h (sem_heawood_comp hD)
  have ineligible : (5 : Fin 14) ∈ ineligSet 14 D := by rw [hI]; decide
  let A := supp 14 D (src D (pos 5)) ∩ mx_L
  have hA : sup_Occ 14 D mx_L A := ⟨src D (pos 5),rfl⟩
  have subA : A ⊆ sem_hw_opp 0 := fun x hx => subrange (Finset.mem_inter.1 hx).2
  let S := equality_mask_pull f A
  have back : S.image f = A := equality_mask_pull_image f (sem_hw_opp 0) range subA
  have neighbors : sem_hw_nb 5 ⊆ A := by
    intro x hx
    exact Finset.mem_inter.2 ⟨(hpos.1 _ ineligible).2.2.1 x (hw_mem_nb.1 hx),mx_cap 5 (by decide) hx⟩
  have absent : ¬ sup_Occ 14 D mx_L (sem_hw_nb 5) := by
    have member : (5 : Fin 14) ∈ equality_missing_cap D := by rw [hM]; decide
    exact (Finset.mem_filter.1 member).2
  have strict : cap7_missing ⊂ S := by
    apply Finset.ssubset_iff_subset_ne.2
    constructor
    · apply (Finset.image_subset_image_iff inj).1
      rw [geometry.2,back]
      exact neighbors
    · intro equal
      apply absent
      rw [← geometry.2,equal,back]
      exact hA
  have hS : Q S := by change sup_Occ 14 D mx_L (S.image f); rwa [back]
  obtain ⟨Y,large,good⟩ := cap7_seven_occurring Q base parents S strict hS
  refine ⟨Y.image (fun M => M.image f),?_,?_⟩
  · rw [Finset.card_image_of_injective _ (Finset.image_injective inj)]
    exact large
  · intro M hMY
    obtain ⟨T,hT,rfl⟩ := Finset.mem_image.1 hMY
    refine ⟨?_,(good T hT).1,?_⟩
    · rw [Finset.card_image_of_injective _ inj]
      exact (good T hT).2.1
    · intro pair
      rw [Finset.card_image_of_injective _ inj] at pair
      obtain ⟨i,sub⟩ := (good T hT).2.2 pair
      refine ⟨![0,1,2] i,?_,?_⟩
      · exact (by decide : ∀ i : Fin 3, (![0,1,2] i : Fin 14) ∈ ({0,1,2} : Finset (Fin 14))) i
      · have imageSub := Finset.image_subset_image sub (f := f)
        rwa [geometry.1 i] at imageSub

theorem equality_m9_one_missing_five_impossible {D : Dag}
    (h : StrictLive 14 D) (hD : Correct D) (h14 : totalSurplus 14 D ≤ 14)
    (hI : ineligSet 14 D = {0,1,2,5,11}) (hM : equality_missing_cap D = {5}) : False := by
  classical
  obtain ⟨Y,large,good⟩ := equality_m9_one_missing_family h hD hI hM
  have eligible : mx_L ⊆ eligSet 14 D := by
    intro x hx
    by_contra no
    exact mx_el x hx (hI ▸ sem_mem_inelig.2 no)
  have occurs : ∀ i ∈ ({0,1,2} : Finset (Fin 14)),
      sem_hw_nb i ⊆ mx_L ∧ sup_Occ 14 D mx_L (sem_hw_nb i) := by
    intro i hi
    have cap : i ∈ ({0,1,2,5} : Finset (Fin 14)) := (by decide : ({0,1,2} : Finset (Fin 14)) ⊆ {0,1,2,5}) hi
    refine ⟨mx_cap i cap,?_⟩
    by_contra absent
    have member : i ∈ equality_missing_cap D := Finset.mem_filter.2 ⟨cap,absent⟩
    rw [hM] at member
    exact Finset.disjoint_left.1 (by decide : Disjoint ({0,1,2} : Finset (Fin 14)) {5}) hi member
  have centers : ∀ c ∈ ({3,4,6} : Finset (Fin 14)), c ∉ ({0,1,2} : Finset (Fin 14)) ∧
      ((sem_hw_nb c ∩ mx_L).card ≤ 2 ∨
        (sem_hw_nb c ⊆ mx_L ∧ ¬ sup_Occ 14 D mx_L (sem_hw_nb c))) := by
    intro c hc
    exact ⟨fun hi => (mx_ctr c hc).1 ((by decide : ({0,1,2} : Finset (Fin 14)) ⊆ {0,1,2,5}) hi),
      Or.inl (mx_ctr c hc).2⟩
  have ineligible : ∀ i ∈ ({0,1,2,5} : Finset (Fin 14)),
      i ∈ ineligSet 14 D ∧ sem_hw_nb i ⊆ mx_L := by
    intro i hi
    exact ⟨by rw [hI]; exact (by decide : ({0,1,2,5} : Finset (Fin 14)) ⊆ {0,1,2,5,11}) hi,mx_cap i hi⟩
  have bound := equality_hw_mask_family h hD mx_L (by decide) eligible {0,1,2} {3,4,6}
    {0,1,2,5} occurs centers ineligible Y
    (fun M hMY => ⟨(good M hMY).1,(good M hMY).2.1⟩)
    (fun M hMY pair => (good M hMY).2.2 pair)
  have ec := inelig_card_add 14 D
  rw [hI,show ({0,1,2,5,11} : Finset (Fin 14)).card = 5 from rfl] at ec
  rw [show ({0,1,2,5} : Finset (Fin 14)).card = 4 from rfl,mx_lab,
    show mx_L.card = 6 from rfl] at bound
  have zero := equality_mixed_cap_saturated h hD h14 hI
  rw [hM,Finset.card_singleton] at zero
  have total := totalSurplus_split 14 D
  omega


theorem equality_m9_missing_card_cases {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h14 : totalSurplus 14 D ≤ 14)
    (hI : ineligSet 14 D = {0, 1, 2, 5, 11}) :
    (equality_missing_cap D).card = 1 ∨ (equality_missing_cap D).card = 2 := by
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
  have htotal := totalSurplus_split 14 D
  change Mc.card = 1 ∨ Mc.card = 2
  omega

theorem equality_m9_any_one_missing_impossible {D : Dag}
    (h : StrictLive 14 D) (hD : Correct D) (h14 : totalSurplus 14 D ≤ 14)
    (hI : ineligSet 14 D = {0,1,2,5,11})
    (one : (equality_missing_cap D).card = 1) : False := by
  classical
  obtain ⟨q,hM⟩ := Finset.card_eq_one.1 one
  have cap : q ∈ ({0,1,2,5} : Finset (Fin 14)) := by
    have member : q ∈ equality_missing_cap D := by rw [hM]; simp
    exact (Finset.mem_filter.1 member).1
  have geometry : ∀ q ∈ ({0,1,2,5} : Finset (Fin 14)), ∃ k l : Fin 6,
      equality_m9_automorphism l (equality_m9_automorphism k q) = 5 := by decide +kernel
  obtain ⟨k,l,equal⟩ := geometry q cap
  obtain ⟨h',hD',_,total',_,_,_,ineligible'⟩ :=
    heawood_relabel (equality_m9_automorphism k) (equality_m9_automorphism_aut k) h hD
  have hI' : ineligSet 14 (relabel (equality_m9_automorphism k) D) = {0,1,2,5,11} := by
    rw [ineligible',hI]
    exact (equality_m9_automorphism_geometry k).2.1
  have hM' : equality_missing_cap (relabel (equality_m9_automorphism k) D) =
      {equality_m9_automorphism k q} := by
    rw [equality_m9_missing_relabel h.1 k,hM,Finset.image_singleton]
  obtain ⟨h'',hD'',_,total'',_,_,_,ineligible''⟩ :=
    heawood_relabel (equality_m9_automorphism l) (equality_m9_automorphism_aut l) h' hD'
  apply equality_m9_one_missing_five_impossible h'' hD''
    (by rw [total'',total']; exact h14)
  · rw [ineligible'',hI']
    exact (equality_m9_automorphism_geometry l).2.1
  · rw [equality_m9_missing_relabel h'.1 l,hM',Finset.image_singleton,equal]

theorem equality_p9_mixed_impossible {D : Dag}
    (h : StrictLive 14 D) (hD : Correct D) (h14 : totalSurplus 14 D ≤ 14)
    (hI : ineligSet 14 D = {0,1,2,5,11}) : False := by
  rcases equality_m9_missing_card_cases h hD h14 hI with one | two
  · exact equality_m9_any_one_missing_impossible h hD h14 hI one
  · exact equality_m9_any_two_missing_impossible h hD h14 hI two

end PEqualNP.Outside.L_meta_6659_aux
