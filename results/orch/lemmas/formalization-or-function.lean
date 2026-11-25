import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1479.K4Equality

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


def falseSource {n : ℕ} (D : Dag) (base : Fin n → Bool) (j : ℕ) (s : Bool) : ℕ :=
  if s then opB D j else if val D base (opA D j) = false then opA D j else opB D j

def falseStep {n : ℕ} (D : Dag) (base : Fin n → Bool) (a b : ℕ) : Prop :=
  ∃ j s, j < D.length ∧ b = n + j ∧ val D base b = false ∧
    (s = false ∨ tag D j = false) ∧ a = falseSource D base j s

lemma falseSource_lt {n : ℕ} {D : Dag} (normal : Strict n D)
    (base : Fin n → Bool) {j : ℕ} (hj : j < D.length) (s : Bool) :
    falseSource D base j s < n + j := by
  obtain ⟨ha,hb,_⟩ := normal j hj
  unfold falseSource
  split_ifs <;> assumption

lemma falseStep_lt {n : ℕ} {D : Dag} (normal : Strict n D)
    {base : Fin n → Bool} {a b : ℕ} (step : falseStep D base a b) : a < b := by
  obtain ⟨j,s,hj,rfl,_,_,rfl⟩ := step
  exact falseSource_lt normal base hj s

lemma falseStep_zero {n : ℕ} {D : Dag} (normal : Strict n D)
    {base : Fin n → Bool} {a b : ℕ} (step : falseStep D base a b) :
    val D base a = false := by
  obtain ⟨j,s,hj,rfl,zero,keep,rfl⟩ := step
  rw [val_gate normal base j hj] at zero
  cases hs : s
  · unfold falseSource
    simp only [hs, Bool.false_eq_true, ite_false]
    split_ifs with ha
    · exact ha
    · cases ht : tag D j <;> cases hb : val D base (opB D j) <;>
        cases hc : val D base (opA D j) <;> simp_all [gop]
  · have ht : tag D j = false := by simpa [hs] using keep
    simp only [falseSource, hs, ite_true]
    cases hb : val D base (opB D j) <;>
      cases ha : val D base (opA D j) <;> simp_all [gop]

lemma false_changed_path {n : ℕ} {D : Dag} (normal : Strict n D)
    (base target : Fin n → Bool) (i : Fin n)
    (agree : ∀ k, k ≠ i → base k = target k) (w : ℕ)
    (zero : val D base w = false) (one : val D target w = true) :
    Relation.ReflTransGen (falseStep D base) i.val w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases input : w < n
    · rw [val_input D base w input] at zero
      rw [val_input D target w input] at one
      have equal : (⟨w,input⟩ : Fin n) = i := by
        by_contra ne
        have eq := agree ⟨w,input⟩ ne
        rw [zero,one] at eq
        contradiction
      have eq := congrArg Fin.val equal
      change w = i.val at eq
      rw [← eq]
    · have hw : w < n + D.length := by
        by_contra hn
        rw [val_ge D target w (by omega)] at one
        contradiction
      obtain ⟨j,rfl⟩ : ∃ j, w = n + j := ⟨w-n,by omega⟩
      have hj : j < D.length := by omega
      have join (s : Bool) (hz : val D base (falseSource D base j s) = false)
          (ht : val D target (falseSource D base j s) = true)
          (keep : s = false ∨ tag D j = false) :
          Relation.ReflTransGen (falseStep D base) i.val (n+j) :=
        Relation.ReflTransGen.tail
          (ih _ (falseSource_lt normal base hj s) hz ht)
          ⟨j,s,hj,rfl,zero,keep,rfl⟩
      have gateZero := zero
      have gateOne := one
      rw [val_gate normal base j hj] at gateZero
      rw [val_gate normal target j hj] at gateOne
      cases ht : tag D j
      · have zeros : val D base (opA D j) = false ∧ val D base (opB D j) = false := by
          cases ha : val D base (opA D j) <;> cases hb : val D base (opB D j) <;>
            simp_all [gop]
        have ones : val D target (opA D j) = true ∨ val D target (opB D j) = true := by
          simpa [ht,gop] using gateOne
        rcases ones with ha | hb
        · exact join false (by simpa [falseSource,zeros.1] using zeros.1)
            (by simpa [falseSource,zeros.1] using ha) (Or.inl rfl)
        · exact join true (by simpa [falseSource] using zeros.2)
            (by simpa [falseSource] using hb) (Or.inr ht)
      · have ones : val D target (opA D j) = true ∧ val D target (opB D j) = true := by
          simpa [ht,gop] using gateOne
        by_cases ha : val D base (opA D j) = false
        · exact join false (by simpa [falseSource,ha] using ha)
            (by simpa [falseSource,ha] using ones.1) (Or.inl rfl)
        · have hb : val D base (opB D j) = false := by
            cases hba : val D base (opA D j) <;> cases hbb : val D base (opB D j) <;>
              simp_all [gop]
          exact join false (by simpa [falseSource,ha] using hb)
            (by simpa [falseSource,ha] using ones.2) (Or.inl rfl)

lemma false_path_zero {n : ℕ} {D : Dag} (normal : Strict n D)
    {base : Fin n → Bool} {a b : ℕ}
    (path : Relation.ReflTransGen (falseStep D base) a b)
    (zero : val D base b = false) : val D base a = false := by
  rcases Relation.ReflTransGen.cases_head path with equal | ⟨c,first,_⟩
  · simpa [equal] using zero
  · exact falseStep_zero normal first

open Finset

lemma certificate_input_card_le (n root : Nat) (I J O W : Finset Nat)
    (source : Nat × Bool → Nat)
    (hIrange : I ⊆ range n) (hIW : I ⊆ W)
    (hJW : ∀ j ∈ J, n + j ∈ W)
    (hcover : W ⊆ insert root
      (((J ×ˢ ({false} : Finset Bool)) ∪ (O ×ˢ ({true} : Finset Bool))).image source)) :
    I.card ≤ O.card + 1 := by
  let K := J.image (fun j => n + j)
  have hKcard : K.card = J.card := by
    apply card_image_of_injective
    intro a b hab
    exact Nat.add_left_cancel hab
  have hKW : K ⊆ W := by
    intro w hw
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hw
    exact hJW j hj
  have hdisj : Disjoint I K := by
    apply disjoint_left.mpr
    intro w hwI hwK
    have hwlt := mem_range.mp (hIrange hwI)
    obtain ⟨j, hj, hje⟩ := mem_image.mp hwK
    omega
  have hlower : I.card + J.card ≤ W.card := by
    rw [← hKcard, ← card_union_of_disjoint hdisj]
    exact card_le_card (union_subset hIW hKW)
  have hupper : W.card ≤ J.card + O.card + 1 := by
    calc
      W.card ≤ (insert root
          (((J ×ˢ ({false} : Finset Bool)) ∪
            (O ×ˢ ({true} : Finset Bool))).image source)).card := card_le_card hcover
      _ ≤ (((J ×ˢ ({false} : Finset Bool)) ∪
            (O ×ˢ ({true} : Finset Bool))).image source).card + 1 := card_insert_le _ _
      _ ≤ ((J ×ˢ ({false} : Finset Bool)) ∪
            (O ×ˢ ({true} : Finset Bool))).card + 1 :=
        Nat.add_le_add_right (card_image_le) 1
      _ ≤ (J ×ˢ ({false} : Finset Bool)).card +
            (O ×ˢ ({true} : Finset Bool)).card + 1 :=
        Nat.add_le_add_right (card_union_le _ _) 1
      _ = J.card + O.card + 1 := by simp
  omega

lemma false_or_count {n : ℕ} {D : Dag} (normal : Strict n D)
    (base : Fin n → Bool) (output : ℕ)
    (zero : val D base output = false) (I : Finset (Fin n))
    (critical : ∀ i ∈ I, ∃ target : Fin n → Bool,
      (∀ k, k ≠ i → base k = target k) ∧ val D target output = true) :
    I.card ≤ ((Finset.range D.length).filter
      (fun j => tag D j = false ∧ val D base (n+j) = false)).card + 1 := by
  classical
  let inputs := I.image Fin.val
  let W := (Finset.range (n+D.length)).filter
    (fun w => Relation.ReflTransGen (falseStep D base) w output)
  let J := (Finset.range D.length).filter (fun j => n+j ∈ W)
  let O := J.filter (fun j => tag D j = false)
  let source : ℕ × Bool → ℕ := fun p => falseSource D base p.1 p.2
  have hIrange : inputs ⊆ Finset.range n := by
    intro w hw
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hw
    exact Finset.mem_range.mpr i.isLt
  have hIW : inputs ⊆ W := by
    intro w hw
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨target,agree,one⟩ := critical i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
      false_changed_path normal base target i agree output zero one⟩
  have hJW : ∀ j ∈ J, n+j ∈ W := by
    intro j hj
    exact (Finset.mem_filter.mp hj).2
  have hcover : W ⊆ insert output
      (((J ×ˢ ({false} : Finset Bool)) ∪ (O ×ˢ ({true} : Finset Bool))).image source) := by
    intro w hw
    have path := (Finset.mem_filter.mp hw).2
    rcases Relation.ReflTransGen.cases_head path with equal | ⟨b,step,rest⟩
    · exact Finset.mem_insert.mpr (Or.inl equal)
    · obtain ⟨j,s,hj,rfl,_,keep,eq⟩ := step
      have parent : n+j ∈ W :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),rest⟩
      have jmem : j ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,parent⟩
      have amem : (j,s) ∈ (J ×ˢ ({false} : Finset Bool)) ∪
          (O ×ˢ ({true} : Finset Bool)) := by
        cases hs : s
        · simp [hs,jmem]
        · have hop : tag D j = false := by simpa [hs] using keep
          have jor : j ∈ O := Finset.mem_filter.mpr ⟨jmem,hop⟩
          simp [hs,jor]
      apply Finset.mem_insert.mpr
      right
      exact Finset.mem_image.mpr ⟨(j,s),amem,eq.symm⟩
  have bound := certificate_input_card_le n output inputs J O W source hIrange hIW hJW hcover
  have inputCard : inputs.card = I.card :=
    Finset.card_image_of_injective I (fun _ _ h => Fin.ext h)
  have orBound : O.card ≤ ((Finset.range D.length).filter
      (fun j => tag D j = false ∧ val D base (n+j) = false)).card := by
    apply Finset.card_le_card
    intro j hj
    obtain ⟨jmem,hop⟩ := Finset.mem_filter.mp hj
    obtain ⟨jrange,parent⟩ := Finset.mem_filter.mp jmem
    exact Finset.mem_filter.mpr ⟨jrange,hop,
      false_path_zero normal (Finset.mem_filter.mp parent).2 zero⟩
  omega

lemma or_function_or_count {n : ℕ} {D : Dag} (normal : Strict n D)
    (output : ℕ)
    (correct : ∀ x : Fin n → Bool, val D x output = true ↔ ∃ i, x i = true) :
    n ≤ ((Finset.range D.length).filter (fun j => tag D j = false)).card + 1 := by
  have zero : val D (fun _ : Fin n => false) output = false := by
    cases hv : val D (fun _ : Fin n => false) output
    · rfl
    · exfalso
      obtain ⟨i,hi⟩ := (correct (fun _ => false)).mp hv
      exact Bool.false_ne_true hi
  have critical : ∀ i ∈ (Finset.univ : Finset (Fin n)), ∃ target : Fin n → Bool,
      (∀ k, k ≠ i → false = target k) ∧ val D target output = true := by
    intro i _
    refine ⟨single i, ?_, (correct (single i)).mpr ⟨i, ?_⟩⟩
    · intro k hk
      simp [single,hk]
    · simp [single]
  have raw := false_or_count normal (fun _ : Fin n => false) output zero Finset.univ critical
  simp only [Finset.card_univ, Fintype.card_fin] at raw
  have bound : ((Finset.range D.length).filter
      (fun j => tag D j = false ∧ val D (fun _ : Fin n => false) (n+j) = false)).card ≤
      ((Finset.range D.length).filter (fun j => tag D j = false)).card := by
    apply Finset.card_le_card
    intro j hj
    obtain ⟨hr,ho,_⟩ := Finset.mem_filter.mp hj
    exact Finset.mem_filter.mpr ⟨hr,ho⟩
  omega

lemma minimum_or_function_only_or {n : ℕ} {D : Dag} (normal : Strict n D)
    (output : ℕ)
    (correct : ∀ x : Fin n → Bool, val D x output = true ↔ ∃ i, x i = true)
    (size : D.length ≤ n-1) : ∀ j, j < D.length → tag D j = false := by
  have bound := or_function_or_count normal output correct
  by_cases hn : n = 0
  · intro j hj
    omega
  · have equal : (Finset.range D.length).filter (fun j => tag D j = false) =
        Finset.range D.length := by
      apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
      simp only [Finset.card_range]
      omega
    intro j hj
    have mem : j ∈ (Finset.range D.length).filter (fun j => tag D j = false) := by
      rw [equal]
      exact Finset.mem_range.mpr hj
    exact (Finset.mem_filter.mp mem).2

end PEqualNP.Outside.L_meta_1479.K4Equality
