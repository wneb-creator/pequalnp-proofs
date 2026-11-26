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

end SurplusFlow

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

end SemCodes

section SemArms

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

lemma sem_rtg_le (hS : Strict n D) {R : ℕ → ℕ → Prop} (hR : ∀ a b, R a b → sem_step n D a b)
    {a b : ℕ} (h : Relation.ReflTransGen R a b) : a ≤ b := by
  induction h with
  | refl => exact le_refl _
  | tail _ hbc ih => exact le_trans ih (le_of_lt (sem_step_lt hS (hR _ _ hbc)))

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

section SupMask

variable {n : ℕ} {D : Dag}

lemma sup_occ_wire (P : Finset (Fin n)) (w : ℕ) : sup_Occ n D P (supp n D w ∩ P) := ⟨w, rfl⟩

lemma sup_occ_big (hS : Strict n D) {P M : Finset (Fin n)} (hM : 2 ≤ M.card)
    (h : sup_Occ n D P M) : ∃ j ∈ sup_big n D P, supp n D (n + j) ∩ P = M := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨j, -, -, hj, hmer, -, -⟩ := sem_first_mask hS P M hM w hw
  exact ⟨j, Finset.mem_filter.mpr ⟨hmer, by rw [hj]; exact hM⟩, hj⟩

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

end Neutral


namespace Neutral
open PEqualNP.Outside.L_meta_2590_aux.DagTools

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
open PEqualNP.Outside.L_meta_2590_aux.DagTools
open PEqualNP.Outside.L_meta_2590_aux.Four
open PEqualNP.Outside.L_meta_2590_aux.SevenRows
open PEqualNP.Outside.L_meta_2590_aux.Neutral

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

end ZeroFlow


namespace ZeroForest
open PEqualNP.Outside.L_meta_2590_aux.DagTools

section Facts
variable {α : Type} {n : Nat} {G : Fin n → Fin n → Prop} {D : Dag}
  {I : Finset (Fin n)} {rows : α → Fin n → Bool}

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

end Compression


namespace Compression
open PEqualNP.Outside.L_meta_2590_aux.DagTools

variable {α : Type}
end Compression


namespace Thirteen
open PEqualNP.Outside.L_meta_2590_aux.DagTools
open PEqualNP.Outside.L_meta_2590_aux.Four
open PEqualNP.Outside.L_meta_2590_aux.SevenGeneral
open PEqualNP.Outside.L_meta_2590_aux.Compression

end Thirteen

namespace EightSupport
open PEqualNP.Outside.L_meta_2590_aux.DagTools
open PEqualNP.Outside.L_meta_2590_aux.Neutral

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
open PEqualNP.Outside.L_meta_2590_aux.DagTools
open Rigidity DagRigidity

variable {n : Nat} {D : Dag}

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
open PEqualNP.Outside.L_meta_2590_aux.RigidClosure

end PoolProgram


namespace FinishFour
open PEqualNP.Outside.L_meta_2590_aux.DagTools
open PEqualNP.Outside.L_meta_2590_aux.Four
open PEqualNP.Outside.L_meta_2590_aux.PoolProgram
open PEqualNP.Outside.L_meta_2590_aux.RigidClosure

end FinishFour


namespace SharedDom
open PEqualNP.Outside.L_meta_2590_aux.DagTools

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
open PEqualNP.Outside.L_meta_2590_aux.DagTools
open PEqualNP.Outside.L_meta_2590_aux.Four

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
open PEqualNP.Outside.L_meta_2590_aux.DagTools
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
open PEqualNP.Outside.L_meta_2590_aux.Four
open PEqualNP.Outside.L_meta_2590_aux.SevenGeneral

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
open PEqualNP.Outside.L_meta_2590_aux.DagTools
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
open PEqualNP.Outside.L_meta_2590_aux.DagTools
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

open PEqualNP.Outside.L_meta_2590_aux.DagTools
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
open PEqualNP.Outside.L_meta_2590_aux.DagTools
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
open PEqualNP.Outside.L_meta_2590_aux.DagTools
open PEqualNP.Outside.L_meta_2590_aux.Four

end SharedDom


namespace SharedDom
open PEqualNP.Outside.L_meta_2590_aux.DagTools
open PEqualNP.Outside.L_meta_2590_aux.Four

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
open PEqualNP.Outside.L_meta_2590_aux.DagTools
open PEqualNP.Outside.L_meta_2590_aux.Four

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
open PEqualNP.Outside.L_meta_2590_aux.DagTools
open PEqualNP.Outside.L_meta_2590_aux.Four

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
open PEqualNP.Outside.L_meta_2590_aux.DagTools
open PEqualNP.Outside.L_meta_2590_aux.Four

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
open PEqualNP.Outside.L_meta_2590_aux.DagTools

lemma four_ineligible_impossible {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 Four.Adj D) (four : (ineligSet 10 D).card = 4)
    (size : D.length ≤ 19) : False := by
  exact ThreeCase.four_ineligible_bzero_le_one_impossible h hc
    (SharedDom.bzero_le_one_of_four_and_nineteen h hc four size) four size

end I4Case

end PEqualNP.Outside.L_meta_2590_aux

namespace PEqualNP.Outside.L_meta_2590_aux.SharedDom
open PEqualNP.Outside.L_meta_2590_aux.DagTools

lemma sem_neighbor_exclusion_slot
    {n : Nat} {G : Fin n → Fin n → Prop} {D : Dag}
    (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    (i c : Fin n) (hci : ¬ G i c)
    (chain : sem_Chain n D i.val (outW n D))
    (N : Finset (Fin n)) (hN : ∀ a ∈ N, G i a) :
    ∃ e : Nat × Bool, e.1 < D.length ∧ tag D e.1 = true ∧
      (∀ x ∈ N, e ∈ sem_W n D x) ∧ c ∉ supp n D (src D e) ∧
      N ⊆ supp n D (src D e) := by
  classical
  have hcN : c ∉ N := fun hc => hci (hN c hc)
  have diff : insert c N \ N = ({c} : Finset (Fin n)) := by
    ext a
    simp only [Finset.mem_sdiff,Finset.mem_insert,Finset.mem_singleton]
    constructor
    · rintro ⟨h|h,hno⟩
      · exact h
      · exact False.elim (hno h)
    · rintro rfl
      exact ⟨Or.inl rfl,hcN⟩
  have hzero : val D (sem_ins i (sem_ind (insert c N \ N))) (outW n D) = false := by
    rw [diff]
    apply Bool.eq_false_iff.mpr
    intro hv
    rcases sem_ins_ind_edge hG ((hC _).mp hv) with ⟨a,ha,hia⟩ | ⟨a,ha,b,hb,hab⟩
    · have eq := Finset.mem_singleton.mp ha
      exact hci (eq ▸ hia)
    · have ea := Finset.mem_singleton.mp ha
      have eb := Finset.mem_singleton.mp hb
      subst a
      subst b
      exact hG.2.1 c hab
  have hone (a : Fin n) (ha : a ∈ N) :
      val D (sem_ins i (sem_ind {a})) (outW n D) = true :=
    (hC _).mpr ⟨i,a,hN a ha,sem_ins_self i _,by simp [sem_ins,sem_ind]⟩
  have hz (a : Fin n) (_ : a ∈ N) : val D (sem_ind {a}) (outW n D) = false := by
    apply Bool.eq_false_iff.mpr
    intro hv
    rw [sem_ind_single] at hv
    exact sem_single_no_edge hG a ((hC _).mp hv)
  obtain ⟨g,s,hg,ht,_,other,hs⟩ := sem_factor hS i (outW n D) chain
    (insert c N) N (Finset.subset_insert c N) hzero hone hz
  have has (x : Fin n) (hx : x ∈ N) : x ∈ supp n D (src D (g,s)) :=
    (Finset.mem_inter.mp (hs.symm ▸ hx)).1
  refine ⟨(g,s),hg,ht,fun x hx => ?_,?_,has⟩
  · apply sem_mem_W.mpr
    refine ⟨hg,has x hx,fun hxout => ?_⟩
    have ho := sem_supp_and_sub hS hg ht (!s) hxout
    have hp := sem_dom_pure hG hS hC i _ (sem_chain_dom hS other) ho
    have eq := Finset.mem_singleton.mp hp
    exact hG.2.1 i (eq ▸ hN x hx)
  · intro hcs
    have hc : c ∈ N := hs ▸ Finset.mem_inter.mpr ⟨hcs,Finset.mem_insert_self c N⟩
    exact hcN hc

lemma sem_neighbor_exclusion_slot_of_bzero
    {n : Nat} {G : Fin n → Fin n → Prop} {D : Dag} [DecidableRel G]
    (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (zero : Bzero n D = 0) {i : Fin n} (hi : i ∈ ineligSet n D)
    (c : Fin n) (hci : ¬ G i c) :
    ∃ e : Nat × Bool, (∀ x, G i x → e ∈ sem_W n D x) ∧
      c ∉ supp n D (src D e) ∧ (∀ a, G i a → a ∈ supp n D (src D e)) := by
  classical
  let N := Finset.univ.filter (G i)
  have chain : sem_Chain n D i.val (outW n D) := by
    rcases sem_inelig_reach hG h hC hi with chain | ⟨b,_,hf,hs⟩
    · exact chain
    · have bound : fanout D b - 1 ≤
          ∑ w ∈ (inner n D).filter (fun w => ¬ (supp n D w).Nonempty), (fanout D w - 1) :=
        Finset.single_le_sum (f := fun w => fanout D w - 1)
          (fun _ _ => Nat.zero_le _) (sem_bzero_mem h.1 hf hs)
      unfold Bzero surplusOn at zero
      omega
  obtain ⟨e,_,_,hW,hc,hs⟩ := sem_neighbor_exclusion_slot hG h.1 hC i c hci
    chain N
    (fun a ha => (Finset.mem_filter.mp ha).2)
  exact ⟨e,fun x hx => hW x (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩),
    hc,fun a ha => hs (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩)⟩

end PEqualNP.Outside.L_meta_2590_aux.SharedDom

namespace PEqualNP.Outside.L_meta_2590_aux.I1Exposure
open PEqualNP.Outside.L_meta_2590_aux.DagTools
open PEqualNP.Outside.L_meta_2590_aux.Four
open PEqualNP.Outside.L_meta_2590_aux.SharedDom

set_option maxHeartbeats 0 in
lemma zero_neighbors : ∀ x : V, Adj 0 x ↔ x ∈ ({1,4,5} : Finset V) := by
  unfold Adj
  decide +kernel

set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 65536 in
lemma exposure_vertices : ∀ x c : V, Adj 0 x → c ≠ 0 → ¬ Adj 0 c →
    ∃ m y : V, Adj x m ∧ Adj 0 y ∧ ¬ Adj c m ∧ ¬ Adj c y ∧ ¬ Adj m y := by
  unfold Adj
  decide +kernel

lemma exposure_geometry {x c : V} (hx : Adj 0 x) (hc : c ≠ 0) (hcn : ¬ Adj 0 c) :
    ∃ A : Finset V, (∀ a ∈ A, ∀ d ∈ A, ¬ Adj a d) ∧ c ∈ A ∧
      (∃ a ∈ A, Adj 0 a) ∧ (∃ a ∈ A, Adj x a) := by
  obtain ⟨m,y,hxm,hiy,hcm,hcy,hmy⟩ := exposure_vertices x c hx hc hcn
  refine ⟨{c,m,y},?_,by simp,⟨y,by simp,hiy⟩,⟨m,by simp,hxm⟩⟩
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

lemma residual_support_eligible {n : Nat} {D : Dag} {b : Fin n → Nat}
    {r : Sigma (fun _ : Nat => Nat)} (hr : r ∈ residualUnits n D b) :
    supp n D r.1 ⊆ eligSet n D := by
  have hu : r ∈ unitsPlus n D := (Finset.mem_sdiff.mp hr).1
  have hm : r ∈ units n D := (Finset.mem_filter.mp hu).1
  have hf := (mem_units.mp hm).2
  intro a ha
  exact mem_eligSet.mpr ⟨r.1,by omega,ha⟩

def ZeroOmission (D : Dag) (c : V) : Prop :=
  ∃ e : Nat × Bool, (∀ x : V, Adj 0 x → e ∈ sem_W 10 D x) ∧
    c ∉ supp 10 D (src D e) ∧ ∀ a : V, Adj 0 a → a ∈ supp 10 D (src D e)

lemma outside_not_in_single_residual {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (b : Fin 10 → Nat) (hb : PureBranch 10 D b)
    (hi : (0 : V) ∈ ineligSet 10 D)
    {r : Sigma (fun _ : Nat => Nat)} (hR : residualUnits 10 D b = {r})
    {x c : V} (hx : Adj 0 x) (hxr : x ∈ supp 10 D r.1)
    (hcE : c ∈ eligSet 10 D) (hcn : ¬ Adj 0 c) (localExit : ZeroOmission D c) :
    c ∉ supp 10 D r.1 := by
  have hr : r ∈ residualUnits 10 D b := hR ▸ Finset.mem_singleton_self r
  have hxE := residual_support_eligible hr hxr
  have hc0 : c ≠ 0 := by
    intro he
    exact (sem_mem_inelig.mp hi) (he ▸ hcE)
  obtain ⟨A,ind,ca,hit0,hitx⟩ := exposure_geometry hx hc0 hcn
  obtain ⟨e,he,hec,hall⟩ := localExit
  obtain ⟨g,s,hg,_,hxs,hxo,free⟩ := sem_exposure graph_ok h.1 hc A ind x hitx
  have hf : (g,s) ∈ sem_W 10 D x := sem_mem_W.mpr ⟨hg,hxs,hxo⟩
  have hfc : c ∉ supp 10 D (src D (g,s)) := fun hm => Finset.disjoint_left.mp free hm ca
  have hef : e ≠ (g,s) := by
    intro eq
    obtain ⟨a,ha,hia⟩ := hit0
    have has := hall a hia
    rw [eq] at has
    exact Finset.disjoint_left.mp free has ha
  obtain ⟨u,hu,_,hcu⟩ := residual_separation_of_two_omissions graph_ok h hc b hb
    (show x ≠ c from fun eq => hcn (eq ▸ hx)) hxE ⟨r,hr,hxr⟩ (he x hx) hf hef hec hfc
  have eq : u = r := by simpa only [hR,Finset.mem_singleton] using hu
  exact eq ▸ hcu

lemma single_residual_support_subset {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (b : Fin 10 → Nat) (hb : PureBranch 10 D b)
    (hi : (0 : V) ∈ ineligSet 10 D)
    {r : Sigma (fun _ : Nat => Nat)} (hR : residualUnits 10 D b = {r})
    (coded : ∃ x : V, Adj 0 x ∧ x ∈ supp 10 D r.1)
    (localExits : ∀ c : V, c ∈ eligSet 10 D → ¬ Adj 0 c → ZeroOmission D c) :
    supp 10 D r.1 ⊆ ({1,4,5} : Finset V) := by
  obtain ⟨x,hx,hxr⟩ := coded
  have hr : r ∈ residualUnits 10 D b := hR ▸ Finset.mem_singleton_self r
  intro c hcr
  apply (zero_neighbors c).mp
  by_contra hcn
  have hcE := residual_support_eligible hr hcr
  exact outside_not_in_single_residual h hc b hb hi hR hx hxr hcE hcn
    (localExits c hcE hcn) hcr

lemma exact_slot_local {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (hi : (0 : V) ∈ ineligSet 10 D) (slot : ExactSlot D 0)
    {c : V} (hcE : c ∈ eligSet 10 D) (hcn : ¬ Adj 0 c) : ZeroOmission D c := by
  obtain ⟨e,_,_,hs,hW⟩ := slot
  have neighborE (a : V) (ha : Adj 0 a) : a ∈ eligSet 10 D := by
    rcases sem_elig_cover graph_ok h hc ha with hzero | hEa
    · exact False.elim ((sem_mem_inelig.mp hi) hzero)
    · exact hEa
  refine ⟨e,fun x hx => hW x (Finset.mem_filter.mpr ⟨neighborE x hx,hx⟩),?_,?_⟩
  · intro hm
    have hcN := hs ▸ Finset.mem_inter.mpr ⟨hm,hcE⟩
    exact hcn (Finset.mem_filter.mp hcN).2
  · intro a ha
    exact (Finset.mem_inter.mp (hs.symm ▸ Finset.mem_filter.mpr ⟨neighborE a ha,ha⟩)).1

lemma single_residual_support_subset_of_exact_slot {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (b : Fin 10 → Nat) (hb : PureBranch 10 D b)
    (hi : (0 : V) ∈ ineligSet 10 D) (slot : ExactSlot D 0)
    {r : Sigma (fun _ : Nat => Nat)} (hR : residualUnits 10 D b = {r})
    (coded : ∃ x : V, Adj 0 x ∧ x ∈ supp 10 D r.1) :
    supp 10 D r.1 ⊆ ({1,4,5} : Finset V) :=
  single_residual_support_subset h hc b hb hi hR coded
    (fun _ hcE hcn => exact_slot_local h hc hi slot hcE hcn)


lemma single_residual_support_subset_of_bzero {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (b : Fin 10 → Nat) (hb : PureBranch 10 D b)
    (zero : Bzero 10 D = 0) (hi : (0 : V) ∈ ineligSet 10 D)
    {r : Sigma (fun _ : Nat => Nat)} (hR : residualUnits 10 D b = {r})
    (coded : ∃ x : V, Adj 0 x ∧ x ∈ supp 10 D r.1) :
    supp 10 D r.1 ⊆ ({1,4,5} : Finset V) :=
  single_residual_support_subset h hc b hb hi hR coded
    (fun c _ hcn => sem_neighbor_exclusion_slot_of_bzero graph_ok h hc zero hi c hcn)

end PEqualNP.Outside.L_meta_2590_aux.I1Exposure

namespace PEqualNP.Outside.L_meta_2590_aux.SharedDom
open PEqualNP.Outside.L_meta_2590_aux.DagTools
open PEqualNP.Outside.L_meta_2590_aux.Four
open PEqualNP.Outside.L_meta_2590_aux.I1Exposure

lemma common_exit_unique {n : Nat} {D : Dag} {x : Fin n}
    (small : (sem_W n D x).card ≤ 2)
    {f e g : Nat × Bool} (hf : f ∈ sem_W n D x)
    (he : e ∈ sem_W n D x) (hg : g ∈ sem_W n D x)
    {a : Fin n} (haf : a ∉ supp n D (src D f))
    (hae : a ∈ supp n D (src D e)) (hag : a ∈ supp n D (src D g)) : e = g := by
  classical
  by_contra neg
  have nef : e ≠ f := fun eq => haf (eq ▸ hae)
  have ngf : g ≠ f := fun eq => haf (eq ▸ hag)
  have sub : ({e,g,f} : Finset (Nat × Bool)) ⊆ sem_W n D x := by
    intro q hq
    simp only [Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl <;> assumption
  have bound := Finset.card_le_card sub
  have card : ({e,g,f} : Finset (Nat × Bool)).card = 3 := by simp [neg,nef,ngf]
  omega

def FullZeroSlot (D : Dag) : Prop :=
  ∃ e : Nat × Bool, e.1 < D.length ∧ tag D e.1 = true ∧
    supp 10 D (src D e) = ({1,4,5} : Finset V) ∧
    ∀ x : V, Adj 0 x → e ∈ sem_W 10 D x

lemma empty_neighbor_code_full_slot {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (b : V → Nat) (hb : PureBranch 10 D b)
    (zero : Bzero 10 D = 0) (hi : (0 : V) ∈ ineligSet 10 D)
    {x : V} (hx : Adj 0 x)
    (empty : ∀ u ∈ residualUnits 10 D b, x ∉ supp 10 D u.1) : FullZeroSlot D := by
  classical
  have count := sem_code_count graph_ok h hc b hb x
  have filt : ((residualUnits 10 D b).filter (fun u => x ∈ supp 10 D u.1)) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro u hu
    exact empty u (Finset.mem_filter.mp hu).1 (Finset.mem_filter.mp hu).2
  have single : (({x} : Finset V) ∩ eligSet 10 D).card ≤ 1 :=
    (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
  have small : (sem_W 10 D x).card ≤ 2 := by
    rw [filt,Finset.card_empty] at count
    omega
  obtain ⟨A,ind,_,hit0,hitx⟩ := I1Exposure.exposure_geometry hx
    (show (2 : V) ≠ 0 by decide) (show ¬ Adj 0 2 by decide +kernel)
  obtain ⟨g,s,hg,_,hxs,hxo,free⟩ := sem_exposure graph_ok h.1 hc A ind x hitx
  have hf : (g,s) ∈ sem_W 10 D x := sem_mem_W.mpr ⟨hg,hxs,hxo⟩
  obtain ⟨a,ha,hia⟩ := hit0
  have haf : a ∉ supp 10 D (src D (g,s)) := fun hs => Finset.disjoint_left.mp free hs ha
  obtain ⟨e,he,_,hall⟩ := sem_neighbor_exclusion_slot_of_bzero graph_ok h hc zero hi 0
    (graph_ok.2.1 0)
  have exact_source : supp 10 D (src D e) = ({1,4,5} : Finset V) := by
    apply Finset.Subset.antisymm
    · intro c hcs
      apply (zero_neighbors c).mp
      by_contra hcn
      obtain ⟨ec,hec,hcc,hallc⟩ := sem_neighbor_exclusion_slot_of_bzero graph_ok h hc zero hi c hcn
      have eq := common_exit_unique small hf (he x hx) (hec x hx) haf (hall a hia) (hallc a hia)
      exact hcc (eq ▸ hcs)
    · intro c hcN
      exact hall c ((zero_neighbors c).mpr hcN)
  exact ⟨e,(sem_mem_W.mp (he x hx)).1,sem_W_and h.1 (he x hx),exact_source,he⟩

lemma full_zero_slot_exact {D : Dag} (full : FullZeroSlot D) : ExactSlot D 0 := by
  obtain ⟨e,he,ht,hs,hW⟩ := full
  refine ⟨e,he,ht,?_,fun x hx => hW x (Finset.mem_filter.mp hx).2⟩
  rw [hs]
  ext a
  simp only [Finset.mem_inter,Finset.mem_filter]
  rw [← zero_neighbors a]
  tauto

lemma single_residual_or_full_zero_slot {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (b : V → Nat) (hb : PureBranch 10 D b)
    (zero : Bzero 10 D = 0) (hi : (0 : V) ∈ ineligSet 10 D)
    {r : Sigma (fun _ : Nat => Nat)} (hR : residualUnits 10 D b = {r}) :
    supp 10 D r.1 = ({1,4,5} : Finset V) ∨ FullZeroSlot D := by
  classical
  by_cases all : ∀ x : V, Adj 0 x → x ∈ supp 10 D r.1
  · left
    apply Finset.Subset.antisymm
    · exact single_residual_support_subset_of_bzero h hc b hb zero hi hR
        ⟨1,by decide +kernel,all 1 (by decide +kernel)⟩
    · intro x hx
      exact all x ((zero_neighbors x).mpr hx)
  · push Not at all
    obtain ⟨x,hx,hxr⟩ := all
    right
    apply empty_neighbor_code_full_slot h hc b hb zero hi hx
    intro u hu
    have eq : u = r := by simpa only [hR,Finset.mem_singleton] using hu
    exact eq ▸ hxr

lemma single_residual_or_exact_zero_slot {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (b : V → Nat) (hb : PureBranch 10 D b)
    (zero : Bzero 10 D = 0) (hi : (0 : V) ∈ ineligSet 10 D)
    {r : Sigma (fun _ : Nat => Nat)} (hR : residualUnits 10 D b = {r}) :
    supp 10 D r.1 = ({1,4,5} : Finset V) ∨ ExactSlot D 0 :=
  (single_residual_or_full_zero_slot h hc b hb zero hi hR).imp_right full_zero_slot_exact

end PEqualNP.Outside.L_meta_2590_aux.SharedDom

namespace PEqualNP.Outside.L_meta_2590_aux.SharedDom
open PEqualNP.Outside.L_meta_2590_aux.DagTools
open PEqualNP.Outside.L_meta_2590_aux.Four
open PEqualNP.Outside.L_meta_2590_aux.I1Exposure

def FirstZeroStar (D : Dag) : Prop :=
  ∃ e : Nat × Bool, e.1 < D.length ∧ tag D e.1 = true ∧
    supp 10 D (src D e) = ({0} : Finset V) ∧
    supp 10 D (10 + e.1) = ∅ ∧
    supp 10 D (src D (e.1,!e.2)) = ({1,4,5} : Finset V) ∧
    exitArcs 10 D (carrierT 10 D {0}) = {e} ∧
    merges 10 D (carrierT 10 D {0}) = ∅ ∧ fanout D (src D e) = 1

lemma empty_neighbor_code_first_star {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (b : V → Nat) (hb : PureBranch 10 D b)
    (zero : Bzero 10 D = 0) (hi : (0 : V) ∈ ineligSet 10 D)
    {x : V} (hx : Adj 0 x)
    (empty : ∀ u ∈ residualUnits 10 D b, x ∉ supp 10 D u.1) : FirstZeroStar D := by
  classical
  obtain ⟨e,he,ht,hs,hn,hall,hW,hM⟩ := sem_inelig_consumer graph_ok h hc hi
  have hm : (e.1,!e.2) ∈ sem_W 10 D x :=
    sem_mem_W.mpr ⟨he,hall x hx,by rw [hn]; simp⟩
  obtain ⟨ef,_,_,hsf,hWf⟩ := empty_neighbor_code_full_slot h hc b hb zero hi hx empty
  have count := sem_code_count graph_ok h hc b hb x
  have filt : ((residualUnits 10 D b).filter (fun u => x ∈ supp 10 D u.1)) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro u hu
    exact empty u (Finset.mem_filter.mp hu).1 (Finset.mem_filter.mp hu).2
  have single : (({x} : Finset V) ∩ eligSet 10 D).card ≤ 1 :=
    (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
  have small : (sem_W 10 D x).card ≤ 2 := by
    rw [filt,Finset.card_empty] at count
    omega
  obtain ⟨A,ind,_,hit0,hitx⟩ := I1Exposure.exposure_geometry hx
    (show (2 : V) ≠ 0 by decide) (show ¬ Adj 0 2 by decide +kernel)
  obtain ⟨g,s,hg,_,hxs,hxo,free⟩ := sem_exposure graph_ok h.1 hc A ind x hitx
  have hf : (g,s) ∈ sem_W 10 D x := sem_mem_W.mpr ⟨hg,hxs,hxo⟩
  obtain ⟨a,ha,hia⟩ := hit0
  have haf : a ∉ supp 10 D (src D (g,s)) := fun hs => Finset.disjoint_left.mp free hs ha
  have hafull : a ∈ supp 10 D (src D ef) := hsf.symm ▸ (zero_neighbors a).mp hia
  have eq := common_exit_unique small hf hm (hWf x hx) haf (hall a hia) hafull
  have hmate : supp 10 D (src D (e.1,!e.2)) = ({1,4,5} : Finset V) := by rw [eq,hsf]
  have hzero : (0 : V) ∈ supp 10 D (src D e) := hs.symm ▸ Finset.mem_singleton_self 0
  have upper := (mem_ineligSet.mp hi) _ hzero
  have lower := sem_step_fanout (sem_step_src (n := 10) he e.2)
  change 1 ≤ fanout D (src D e) at lower
  exact ⟨e,he,ht,hs,hn,hmate,hW,hM,by omega⟩

lemma single_residual_or_first_zero_star {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (b : V → Nat) (hb : PureBranch 10 D b)
    (zero : Bzero 10 D = 0) (hi : (0 : V) ∈ ineligSet 10 D)
    {r : Sigma (fun _ : Nat => Nat)} (hR : residualUnits 10 D b = {r}) :
    supp 10 D r.1 = ({1,4,5} : Finset V) ∨ FirstZeroStar D := by
  classical
  by_cases all : ∀ x : V, Adj 0 x → x ∈ supp 10 D r.1
  · left
    apply Finset.Subset.antisymm
    · exact single_residual_support_subset_of_bzero h hc b hb zero hi hR
        ⟨1,by decide +kernel,all 1 (by decide +kernel)⟩
    · intro x hx
      exact all x ((zero_neighbors x).mpr hx)
  · push Not at all
    obtain ⟨x,hx,hxr⟩ := all
    right
    apply empty_neighbor_code_first_star h hc b hb zero hi hx
    intro u hu
    have eq : u = r := by simpa only [hR,Finset.mem_singleton] using hu
    exact eq ▸ hxr

end PEqualNP.Outside.L_meta_2590_aux.SharedDom

namespace PEqualNP.Outside.L_meta_2590_aux.SharedDom
open PEqualNP.Outside.L_meta_2590_aux.DagTools

lemma sem_neighbor_exclusion_slot_with_chain
    {n : Nat} {G : Fin n → Fin n → Prop} {D : Dag}
    (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    (i c : Fin n) (hci : ¬ G i c)
    (chain : sem_Chain n D i.val (outW n D))
    (N : Finset (Fin n)) (hN : ∀ a ∈ N, G i a) :
    ∃ e : Nat × Bool, e.1 < D.length ∧ tag D e.1 = true ∧
      sem_Chain n D i.val (src D (sem_bar e)) ∧
      supp n D (src D (sem_bar e)) ⊆ {i} ∧
      (∀ x ∈ N, e ∈ sem_W n D x) ∧ c ∉ supp n D (src D e) ∧
      N ⊆ supp n D (src D e) := by
  classical
  have hcN : c ∉ N := fun hc => hci (hN c hc)
  have diff : insert c N \ N = ({c} : Finset (Fin n)) := by
    ext a
    simp only [Finset.mem_sdiff,Finset.mem_insert,Finset.mem_singleton]
    constructor
    · rintro ⟨h|h,hno⟩
      · exact h
      · exact False.elim (hno h)
    · rintro rfl
      exact ⟨Or.inl rfl,hcN⟩
  have hzero : val D (sem_ins i (sem_ind (insert c N \ N))) (outW n D) = false := by
    rw [diff]
    apply Bool.eq_false_iff.mpr
    intro hv
    rcases sem_ins_ind_edge hG ((hC _).mp hv) with ⟨a,ha,hia⟩ | ⟨a,ha,b,hb,hab⟩
    · have eq := Finset.mem_singleton.mp ha
      exact hci (eq ▸ hia)
    · have ea := Finset.mem_singleton.mp ha
      have eb := Finset.mem_singleton.mp hb
      subst a
      subst b
      exact hG.2.1 c hab
  have hone (a : Fin n) (ha : a ∈ N) :
      val D (sem_ins i (sem_ind {a})) (outW n D) = true :=
    (hC _).mpr ⟨i,a,hN a ha,sem_ins_self i _,by simp [sem_ins,sem_ind]⟩
  have hz (a : Fin n) (_ : a ∈ N) : val D (sem_ind {a}) (outW n D) = false := by
    apply Bool.eq_false_iff.mpr
    intro hv
    rw [sem_ind_single] at hv
    exact sem_single_no_edge hG a ((hC _).mp hv)
  obtain ⟨g,s,hg,ht,_,other,hs⟩ := sem_factor hS i (outW n D) chain
    (insert c N) N (Finset.subset_insert c N) hzero hone hz
  have has (x : Fin n) (hx : x ∈ N) : x ∈ supp n D (src D (g,s)) :=
    (Finset.mem_inter.mp (hs.symm ▸ hx)).1
  refine ⟨(g,s),hg,ht,other,sem_dom_pure hG hS hC i _ (sem_chain_dom hS other),
    fun x hx => ?_,?_,has⟩
  · apply sem_mem_W.mpr
    refine ⟨hg,has x hx,fun hxout => ?_⟩
    have ho := sem_supp_and_sub hS hg ht (!s) hxout
    have hp := sem_dom_pure hG hS hC i _ (sem_chain_dom hS other) ho
    have eq := Finset.mem_singleton.mp hp
    exact hG.2.1 i (eq ▸ hN x hx)
  · intro hcs
    have hc : c ∈ N := hs ▸ Finset.mem_inter.mpr ⟨hcs,Finset.mem_insert_self c N⟩
    exact hcN hc

lemma sem_neighbor_exclusion_slot_with_chain_of_bzero
    {n : Nat} {G : Fin n → Fin n → Prop} {D : Dag} [DecidableRel G]
    (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (zero : Bzero n D = 0) {i : Fin n} (hi : i ∈ ineligSet n D)
    (c : Fin n) (hci : ¬ G i c) :
    ∃ e : Nat × Bool, e.1 < D.length ∧ tag D e.1 = true ∧
      sem_Chain n D i.val (src D (sem_bar e)) ∧
      supp n D (src D (sem_bar e)) ⊆ {i} ∧
      (∀ x, G i x → e ∈ sem_W n D x) ∧
      c ∉ supp n D (src D e) ∧ (∀ a, G i a → a ∈ supp n D (src D e)) := by
  classical
  let N := Finset.univ.filter (G i)
  have chain : sem_Chain n D i.val (outW n D) := by
    rcases sem_inelig_reach hG h hC hi with chain | ⟨b,_,hf,hs⟩
    · exact chain
    · have bound : fanout D b - 1 ≤
          ∑ w ∈ (inner n D).filter (fun w => ¬ (supp n D w).Nonempty), (fanout D w - 1) :=
        Finset.single_le_sum (f := fun w => fanout D w - 1)
          (fun _ _ => Nat.zero_le _) (sem_bzero_mem h.1 hf hs)
      unfold Bzero surplusOn at zero
      omega
  obtain ⟨e,he,ht,hchain,hpure,hW,hc,hs⟩ := sem_neighbor_exclusion_slot_with_chain hG h.1 hC i c hci
    chain N
    (fun a ha => (Finset.mem_filter.mp ha).2)
  exact ⟨e,he,ht,hchain,hpure,fun x hx => hW x (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩),
    hc,fun a ha => hs (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩)⟩

end PEqualNP.Outside.L_meta_2590_aux.SharedDom

namespace PEqualNP.Outside.L_meta_2590_aux.SharedDom
open PEqualNP.Outside.L_meta_2590_aux.DagTools
open PEqualNP.Outside.L_meta_2590_aux.Four
open PEqualNP.Outside.L_meta_2590_aux.I1Exposure

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 1000000 in
lemma i1_exposure_omit_vertices : ∀ x d : V, x ≠ 0 → d ≠ 0 → d ≠ x →
    ∃ m y : V, Adj x m ∧ Adj 0 y ∧ ¬ Adj d m ∧ ¬ Adj d y ∧ ¬ Adj m y := by
  unfold Adj
  decide +kernel

lemma i1_exposure_omit_geometry (x d : V)
    (hx : x ≠ 0) (hd : d ≠ 0) (hdx : d ≠ x) :
    ∃ A : Finset V, (∀ a ∈ A, ∀ c ∈ A, ¬ Adj a c) ∧
      d ∈ A ∧ (∃ a ∈ A, Adj 0 a) ∧ (∃ a ∈ A, Adj x a) := by
  obtain ⟨m,y,hxm,h0y,hdm,hdy,hmy⟩ := i1_exposure_omit_vertices x d hx hd hdx
  refine ⟨{d,m,y}, ?_, by simp, ⟨y,by simp,h0y⟩, ⟨m,by simp,hxm⟩⟩
  intro a ha c hc
  simp only [Finset.mem_insert,Finset.mem_singleton] at ha hc
  rcases ha with rfl | rfl | rfl <;> rcases hc with rfl | rfl | rfl
  · exact graph_ok.2.1 _
  · exact hdm
  · exact hdy
  · exact fun hmd => hdm (graph_ok.1 _ _ hmd)
  · exact graph_ok.2.1 _
  · exact hmy
  · exact fun hyd => hdy (graph_ok.1 _ _ hyd)
  · exact fun hym => hmy (graph_ok.1 _ _ hym)
  · exact graph_ok.2.1 _

lemma exits_equal_away {n : Nat} {D : Dag} {x : Fin n}
    (small : (sem_W n D x).card ≤ 2)
    {e f g : Nat × Bool} (he : e ∈ sem_W n D x)
    (hf : f ∈ sem_W n D x) (hg : g ∈ sem_W n D x)
    (hfe : f ≠ e) (hge : g ≠ e) : f = g := by
  classical
  by_contra hfg
  have sub : ({f,e,g} : Finset (Nat × Bool)) ⊆ sem_W n D x := by
    intro q hq
    simp only [Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl <;> assumption
  have bound := Finset.card_le_card sub
  have card : ({f,e,g} : Finset (Nat × Bool)).card = 3 := by
    simp [hfe,hfg,Ne.symm hge]
  omega

lemma other_exit_pure {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (hi : (0 : V) ∈ ineligSet 10 D)
    {x : V} (hx : x ≠ 0) (small : (sem_W 10 D x).card ≤ 2)
    {e : Nat × Bool} (he : e ∈ sem_W 10 D x)
    (hall : ∀ a : V, Adj 0 a → a ∈ supp 10 D (src D e))
    {f : Nat × Bool} (hf : f ∈ sem_W 10 D x) (hfe : f ≠ e) :
    supp 10 D (src D f) = {x} := by
  have hxsrc : x ∈ supp 10 D (src D f) := (sem_mem_W.mp hf).2.1
  apply Finset.Subset.antisymm
  · intro d hdsrc
    simp only [Finset.mem_singleton]
    by_contra hdx
    by_cases hd : d = 0
    · have hpure := sem_inelig_pure graph_ok h.1 hc hi (hd ▸ hdsrc)
      rw [hpure,Finset.mem_singleton] at hxsrc
      exact hx hxsrc
    · obtain ⟨A,ind,hdA,hit0,hitx⟩ := i1_exposure_omit_geometry x d hx hd hdx
      obtain ⟨g,s,hg,_,hxg,hxout,free⟩ := sem_exposure graph_ok h.1 hc A ind x hitx
      have hgw : (g,s) ∈ sem_W 10 D x := sem_mem_W.mpr ⟨hg,hxg,hxout⟩
      have hge : (g,s) ≠ e := by
        intro eq
        obtain ⟨a,ha,h0a⟩ := hit0
        have hae := hall a h0a
        rw [← eq] at hae
        exact Finset.disjoint_left.mp free hae ha
      have eq := exits_equal_away small he hf hgw hfe hge
      rw [eq] at hdsrc
      exact Finset.disjoint_left.mp free hdsrc hdA
  · exact Finset.singleton_subset_iff.mpr hxsrc

end PEqualNP.Outside.L_meta_2590_aux.SharedDom

namespace PEqualNP.Outside.L_meta_2590_aux.SharedDom
open PEqualNP.Outside.L_meta_2590_aux.DagTools
open PEqualNP.Outside.L_meta_2590_aux.Four
open PEqualNP.Outside.L_meta_2590_aux.I1Exposure

set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 1000000 in
lemma dirty_neighbor_geometry : ∀ c : V, c ≠ 0 → ¬ Adj 0 c →
    ∃ j d : V, Adj 0 j ∧ Adj j c ∧ Adj j d ∧ d ≠ 0 ∧ d ≠ c := by
  unfold Adj
  decide +kernel

lemma exits_three_of_one_residual {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (b : V → Nat) (hb : PureBranch 10 D b)
    (hR : (residualUnits 10 D b).card ≤ 1) (x : V) : (sem_W 10 D x).card ≤ 3 := by
  have count := sem_code_count graph_ok h hc b hb x
  have single : (({x} : Finset V) ∩ eligSet 10 D).card ≤ 1 :=
    (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
  have filt : ((residualUnits 10 D b).filter (fun u => x ∈ supp 10 D u.1)).card ≤ 1 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans hR
  omega

lemma exits_two_of_empty_code {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (b : V → Nat) (hb : PureBranch 10 D b) (x : V)
    (empty : ∀ u ∈ residualUnits 10 D b, x ∉ supp 10 D u.1) : (sem_W 10 D x).card ≤ 2 := by
  classical
  have count := sem_code_count graph_ok h hc b hb x
  have filt : ((residualUnits 10 D b).filter (fun u => x ∈ supp 10 D u.1)) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro u hu
    exact empty u (Finset.mem_filter.mp hu).1 (Finset.mem_filter.mp hu).2
  have single : (({x} : Finset V) ∩ eligSet 10 D).card ≤ 1 :=
    (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
  rw [filt,Finset.card_empty] at count
  omega

lemma exits_equal_away_two {α : Type} [DecidableEq α] (U : Finset α)
    (small : U.card ≤ 3) {e t u v : α}
    (he : e ∈ U) (ht : t ∈ U) (hu : u ∈ U) (hv : v ∈ U)
    (het : e ≠ t) (hue : u ≠ e) (hut : u ≠ t) (hve : v ≠ e) (hvt : v ≠ t) : u = v := by
  classical
  by_contra huv
  have sub : ({e,t,u,v} : Finset α) ⊆ U := by
    intro q hq
    simp only [Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> assumption
  have bound := Finset.card_le_card sub
  have card : ({e,t,u,v} : Finset α).card = 4 := by
    simp [het,Ne.symm hue,Ne.symm hut,Ne.symm hve,Ne.symm hvt,huv]
  omega

lemma residual_neighborhood_first_star {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (b : V → Nat) (hb : PureBranch 10 D b)
    (zero : Bzero 10 D = 0) (hi : (0 : V) ∈ ineligSet 10 D)
    {r : Sigma (fun _ : Nat => Nat)} (hR : residualUnits 10 D b = {r})
    (hS : supp 10 D r.1 = ({1,4,5} : Finset V)) : FirstZeroStar D := by
  classical
  obtain ⟨e₀,he₀,ht₀,hs₀,hn₀,hall,hW₀,hM₀⟩ := sem_inelig_consumer graph_ok h hc hi
  let e := sem_bar e₀
  have heW (a : V) (ha : Adj 0 a) : e ∈ sem_W 10 D a :=
    sem_mem_W.mpr ⟨he₀,hall a ha,by change a ∉ supp 10 D (10 + e₀.1); rw [hn₀]; simp⟩
  have hallE (a : V) (ha : Adj 0 a) : a ∈ supp 10 D (src D e) := hall a ha
  have control : supp 10 D (src D (sem_bar e)) = ({0} : Finset V) := by
    simpa [e,sem_bar] using hs₀
  have exact_mate : supp 10 D (src D e) = ({1,4,5} : Finset V) := by
    apply Finset.Subset.antisymm
    · intro c hcs
      apply (zero_neighbors c).mp
      by_contra hcn
      have hc0 : c ≠ 0 := by
        intro eq
        have hz : (0 : V) ∈ supp 10 D (src D e) := eq ▸ hcs
        have pure := sem_inelig_pure graph_ok h.1 hc hi hz
        have hone := hallE 1 (by decide +kernel)
        rw [pure,Finset.mem_singleton] at hone
        exact (by decide : (1 : V) ≠ 0) hone
      obtain ⟨j,d,h0j,hjc,hjd,hd0,hdc⟩ := dirty_neighbor_geometry c hc0 hcn
      have hec : e ∈ sem_W 10 D c :=
        sem_mem_W.mpr ⟨he₀,hcs,by change c ∉ supp 10 D (10 + e₀.1); rw [hn₀]; simp⟩
      have empty : ∀ u ∈ residualUnits 10 D b, c ∉ supp 10 D u.1 := by
        intro u hu
        have eq : u = r := by simpa only [hR,Finset.mem_singleton] using hu
        rw [eq,hS]
        exact fun hcN => hcn ((zero_neighbors c).mpr hcN)
      have smallc := exits_two_of_empty_code h hc b hb c empty
      have smallj := exits_three_of_one_residual h hc b hb (by simp [hR]) j
      obtain ⟨t,_,_,_,pureT,hWt,hct,hNt⟩ :=
        sem_neighbor_exclusion_slot_with_chain_of_bzero graph_ok h hc zero hi c hcn
      have het : e ≠ t := fun eq => hct (eq ▸ hcs)
      have avoid {q : Nat × Bool} {y : V} (hy : y ≠ 0)
          (hq : sem_bar q ∈ sem_W 10 D y) : q ≠ e ∧ q ≠ t := by
        have hys := (sem_mem_W.mp hq).2.1
        constructor
        · intro eq
          rw [eq,control,Finset.mem_singleton] at hys
          exact hy hys
        · intro eq
          rw [eq] at hys
          exact hy (Finset.mem_singleton.mp (pureT hys))
      obtain ⟨u,hu,hbu,_,hju,_⟩ := sem_edge_slots graph_ok h.1 hc hjc
      obtain ⟨v,hv,hbv,_,_,_⟩ := sem_edge_slots graph_ok h.1 hc hjd
      have au := avoid hc0 hbu
      have av := avoid hd0 hbv
      have uv := exits_equal_away_two (sem_W 10 D j) smallj (heW j h0j) (hWt j h0j)
        hu hv het au.1 au.2 av.1 av.2
      have hbe : sem_bar u ≠ e := by
        intro eq
        exact hju (eq.symm ▸ hallE j h0j)
      have pure := other_exit_pure h hc hi hc0 smallc hec hallE hbu hbe
      have hdsrc : d ∈ supp 10 D (src D (sem_bar u)) := uv.symm ▸ (sem_mem_W.mp hbv).2.1
      rw [pure,Finset.mem_singleton] at hdsrc
      exact hdc hdsrc
    · intro a ha
      exact hallE a ((zero_neighbors a).mpr ha)
  have hzero : (0 : V) ∈ supp 10 D (src D e₀) := hs₀.symm ▸ Finset.mem_singleton_self 0
  have upper := (mem_ineligSet.mp hi) _ hzero
  have lower := sem_step_fanout (sem_step_src (n := 10) he₀ e₀.2)
  change 1 ≤ fanout D (src D e₀) at lower
  exact ⟨e₀,he₀,ht₀,hs₀,hn₀,exact_mate,hW₀,hM₀,by omega⟩

lemma single_residual_first_zero_star {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (b : V → Nat) (hb : PureBranch 10 D b)
    (zero : Bzero 10 D = 0) (hi : (0 : V) ∈ ineligSet 10 D)
    {r : Sigma (fun _ : Nat => Nat)} (hR : residualUnits 10 D b = {r}) : FirstZeroStar D := by
  rcases single_residual_or_first_zero_star h hc b hb zero hi hR with hS | star
  · exact residual_neighborhood_first_star h hc b hb zero hi hR hS
  · exact star

lemma budget_one_first_zero_star {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (zero : Bzero 10 D = 0) (hi : (0 : V) ∈ ineligSet 10 D)
    (budget : Bplus 10 D = (eligSet 10 D).card + 1) : FirstZeroStar D := by
  obtain ⟨b,hb⟩ := sem_exists_pureBranch graph_ok h.1 hc
  have count := card_residual h.1 b hb
  have one : (residualUnits 10 D b).card = 1 := by omega
  obtain ⟨r,hr⟩ := Finset.card_eq_one.mp one
  exact single_residual_first_zero_star h hc b hb zero hi hr

end PEqualNP.Outside.L_meta_2590_aux.SharedDom

namespace PEqualNP.Outside.L_meta_2590_aux.I1UniqueChain
open PEqualNP.Outside.L_meta_2590_aux.DagTools
open PEqualNP.Outside.L_meta_2590_aux.Four
open PEqualNP.Outside.L_meta_2590_aux.I1Exposure

lemma ineligible_reachable_chain {n : Nat} {G : Fin n → Fin n → Prop} {D : Dag}
    (hG : sem_Gr G) (h : StrictLive n D) (hc : sem_Comp n G D)
    (zero : Bzero n D = 0) {i : Fin n} (hi : i ∈ ineligSet n D) {w : Nat}
    (path : Relation.ReflTransGen (sem_step n D) i.val w) : sem_Chain n D i.val w := by
  rcases sem_path_chain path with chain | ⟨b,chain,hf⟩
  · exact chain
  · have hs := sem_branch_empty hG h.1 hc hi chain hf
    have bound : fanout D b - 1 ≤
        ∑ v ∈ (inner n D).filter (fun v => ¬ (supp n D v).Nonempty), (fanout D v - 1) :=
      Finset.single_le_sum (f := fun v => fanout D v - 1)
        (fun _ _ => Nat.zero_le _) (sem_bzero_mem h.1 hf hs)
    unfold Bzero surplusOn at zero
    omega

lemma chain_gate_input {n : Nat} {D : Dag} {i : Fin n} {g : Nat}
    (chain : sem_Chain n D i.val (n+g)) :
    ∃ s : Bool, sem_Chain n D i.val (src D (g,s)) ∧ fanout D (src D (g,s)) = 1 := by
  rcases Relation.ReflTransGen.cases_tail chain with he | ⟨w,hw,step⟩
  · have hi := i.isLt
    omega
  · obtain ⟨j,s,hj,he,hs⟩ := sem_step_iff.mp step.1
    have hgj : g = j := by omega
    subst j
    exact ⟨s,by simpa only [sem_Chain,hs] using hw,by simpa only [hs] using step.2⟩

lemma chain_and_neighbor_slots {n : Nat} {G : Fin n → Fin n → Prop} {D : Dag}
    (hG : sem_Gr G) (hS : Strict n D) (hc : sem_Comp n G D)
    {i : Fin n} {g : Nat} (hg : g < D.length) (ht : tag D g = true) (s : Bool)
    (hi : sem_Chain n D i.val (src D (g,s))) (hf : fanout D (src D (g,s)) = 1) :
    (∀ a, G i a → a ∈ supp n D (src D (g,!s))) ∧
    (∀ a, G i a → (g,!s) ∈ sem_W n D a) := by
  have all (a) (hia : G i a) : a ∈ supp n D (src D (g,!s)) := by
    have independent : val D (single a) (src D (g,!s)) =
        val D (sem_ins i (single a)) (src D (g,!s)) :=
      sem_sibling_indep hS i hg (!s) (by simpa using hi) (by simpa using hf)
        _ _ (sem_ins_agree i (single a))
    have chain : sem_Chain n D i.val (n+g) :=
      Relation.ReflTransGen.tail hi ⟨sem_step_src hg s,hf⟩
    have he : sem_Edge G (sem_ins i (single a)) :=
      ⟨i,a,hia,sem_ins_self i _,by simp [sem_ins,single]⟩
    have hv := (sem_dom_split hS hc (single a) i (n+g)
      (sem_chain_dom hS chain) (sem_single_no_edge hG a) he).2
    rw [sem_val_gate_src hS _ hg s,ht,gop_true,Bool.and_eq_true] at hv
    exact mem_supp.mpr (independent.trans hv.2)
  refine ⟨all,fun a ha => sem_mem_W.mpr ⟨hg,all a ha,?_⟩⟩
  intro hout
  have hcontrol := sem_supp_and_sub hS hg ht s hout
  have pure := sem_dom_pure hG hS hc i _ (sem_chain_dom hS hi) hcontrol
  have eq := Finset.mem_singleton.mp pure
  exact hG.2.1 i (eq ▸ ha)

lemma reachable_and_neighbor_slots {n : Nat} {G : Fin n → Fin n → Prop} {D : Dag}
    (hG : sem_Gr G) (h : StrictLive n D) (hc : sem_Comp n G D)
    (zero : Bzero n D = 0) {i : Fin n} (hi : i ∈ ineligSet n D)
    {g : Nat} (hg : g < D.length) (ht : tag D g = true)
    (path : Relation.ReflTransGen (sem_step n D) i.val (n+g)) :
    ∃ s : Bool, (∀ a, G i a → a ∈ supp n D (src D (g,s))) ∧
      (∀ a, G i a → (g,s) ∈ sem_W n D a) := by
  obtain ⟨s,chain,fan⟩ := chain_gate_input (ineligible_reachable_chain hG h hc zero hi path)
  exact ⟨!s,chain_and_neighbor_slots hG h.1 hc hg ht s chain fan⟩

lemma reachable_ands_unique_of_empty_neighbor {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (b : V → Nat) (hb : PureBranch 10 D b)
    (zero : Bzero 10 D = 0) (hi : (0 : V) ∈ ineligSet 10 D)
    {x : V} (hx : Adj 0 x)
    (empty : ∀ u ∈ residualUnits 10 D b, x ∉ supp 10 D u.1)
    {g j : Nat} (hg : g < D.length) (htg : tag D g = true)
    (pg : Relation.ReflTransGen (sem_step 10 D) 0 (10+g))
    (hj : j < D.length) (htj : tag D j = true)
    (pj : Relation.ReflTransGen (sem_step 10 D) 0 (10+j)) : g = j := by
  classical
  by_contra ne
  obtain ⟨s,sg,wg⟩ := reachable_and_neighbor_slots graph_ok h hc zero hi hg htg pg
  obtain ⟨t,sj,wj⟩ := reachable_and_neighbor_slots graph_ok h hc zero hi hj htj pj
  have count := sem_code_count graph_ok h hc b hb x
  have filt : ((residualUnits 10 D b).filter (fun u => x ∈ supp 10 D u.1)) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro u hu
    exact empty u (Finset.mem_filter.mp hu).1 (Finset.mem_filter.mp hu).2
  rw [filt,Finset.card_empty] at count
  have singleton : (({x} : Finset V) ∩ eligSet 10 D).card ≤ 1 :=
    (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
  have small : (sem_W 10 D x).card ≤ 2 := by omega
  obtain ⟨A,ind,_,hit0,hitx⟩ := I1Exposure.exposure_geometry hx
    (show (2 : V) ≠ 0 by decide) (show ¬ Adj 0 2 by decide +kernel)
  obtain ⟨f,u,hf,_,hxs,hxo,free⟩ := sem_exposure graph_ok h.1 hc A ind x hitx
  have wf : (f,u) ∈ sem_W 10 D x := sem_mem_W.mpr ⟨hf,hxs,hxo⟩
  obtain ⟨a,ha,hia⟩ := hit0
  have gaf : (g,s) ≠ (f,u) := by
    intro eq
    have has := sg a hia
    rw [eq] at has
    exact Finset.disjoint_left.mp free has ha
  have jaf : (j,t) ≠ (f,u) := by
    intro eq
    have has := sj a hia
    rw [eq] at has
    exact Finset.disjoint_left.mp free has ha
  have gj : (g,s) ≠ (j,t) := fun eq => ne (congrArg Prod.fst eq)
  have large : 2 < (sem_W 10 D x).card :=
    Finset.two_lt_card.mpr ⟨(g,s),wg x hx,(j,t),wj x hx,(f,u),wf,gj,gaf,jaf⟩
  omega

lemma empty_neighbor_of_support_ne {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (b : V → Nat) (hb : PureBranch 10 D b)
    (zero : Bzero 10 D = 0) (hi : (0 : V) ∈ ineligSet 10 D)
    {r : Sigma (fun _ : Nat => Nat)} (hR : residualUnits 10 D b = {r})
    (hne : supp 10 D r.1 ≠ ({1,4,5} : Finset V)) :
    ∃ x : V, Adj 0 x ∧ ∀ u ∈ residualUnits 10 D b, x ∉ supp 10 D u.1 := by
  classical
  have miss : ∃ x : V, Adj 0 x ∧ x ∉ supp 10 D r.1 := by
    by_contra no
    have all (x : V) (hx : Adj 0 x) : x ∈ supp 10 D r.1 := by
      by_contra hn
      exact no ⟨x,hx,hn⟩
    apply hne
    apply Finset.Subset.antisymm
    · exact single_residual_support_subset_of_bzero h hc b hb zero hi hR
        ⟨1,by decide +kernel,all 1 (by decide +kernel)⟩
    · intro x hx
      exact all x ((zero_neighbors x).mpr hx)
  obtain ⟨x,hx,hxr⟩ := miss
  refine ⟨x,hx,fun u hu => ?_⟩
  have eq : u = r := by simpa only [hR,Finset.mem_singleton] using hu
  exact eq ▸ hxr

lemma reachable_ands_unique_of_support_ne {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (b : V → Nat) (hb : PureBranch 10 D b)
    (zero : Bzero 10 D = 0) (hi : (0 : V) ∈ ineligSet 10 D)
    {r : Sigma (fun _ : Nat => Nat)} (hR : residualUnits 10 D b = {r})
    (hne : supp 10 D r.1 ≠ ({1,4,5} : Finset V))
    {g j : Nat} (hg : g < D.length) (htg : tag D g = true)
    (pg : Relation.ReflTransGen (sem_step 10 D) 0 (10+g))
    (hj : j < D.length) (htj : tag D j = true)
    (pj : Relation.ReflTransGen (sem_step 10 D) 0 (10+j)) : g = j := by
  obtain ⟨x,hx,empty⟩ := empty_neighbor_of_support_ne h hc b hb zero hi hR hne
  exact reachable_ands_unique_of_empty_neighbor h hc b hb zero hi hx empty hg htg pg hj htj pj

lemma first_consumer_only_reachable_and {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (b : V → Nat) (hb : PureBranch 10 D b)
    (zero : Bzero 10 D = 0) (hi : (0 : V) ∈ ineligSet 10 D)
    {r : Sigma (fun _ : Nat => Nat)} (hR : residualUnits 10 D b = {r})
    (hne : supp 10 D r.1 ≠ ({1,4,5} : Finset V)) :
    ∃ e : Nat × Bool, e.1 < D.length ∧ tag D e.1 = true ∧
      supp 10 D (src D e) = {0} ∧ supp 10 D (10+e.1) = ∅ ∧
      ∀ g, g < D.length → tag D g = true →
        Relation.ReflTransGen (sem_step 10 D) 0 (10+g) → g = e.1 := by
  obtain ⟨e,he,ht,hs,hout,_,_,_⟩ := sem_inelig_consumer graph_ok h hc hi
  have member : (0 : V) ∈ supp 10 D (src D e) := hs.symm ▸ Finset.mem_singleton_self 0
  have chain := sem_inelig_chain h.1 hi member
  have reach : Relation.ReflTransGen (sem_step 10 D) 0 (10+e.1) :=
    Relation.ReflTransGen.tail (sem_rtg_mono (fun _ _ hh => hh.1) chain) (sem_step_src he e.2)
  refine ⟨e,he,ht,hs,hout,fun g hg htg pg => ?_⟩
  exact reachable_ands_unique_of_support_ne h hc b hb zero hi hR hne hg htg pg he ht reach

end PEqualNP.Outside.L_meta_2590_aux.I1UniqueChain

namespace PEqualNP.Outside.L_meta_2590_aux.I1UniqueChain
open PEqualNP.Outside.L_meta_2590_aux.DagTools
open PEqualNP.Outside.L_meta_2590_aux.Four
open PEqualNP.Outside.L_meta_2590_aux.SharedDom

lemma first_zero_star_only_reachable_and {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (b : V → Nat) (hb : PureBranch 10 D b)
    (zero : Bzero 10 D = 0) (hi : (0 : V) ∈ ineligSet 10 D)
    {r : Sigma (fun _ : Nat => Nat)} (hR : residualUnits 10 D b = {r})
    (hne : supp 10 D r.1 ≠ ({1,4,5} : Finset V)) :
    ∃ e : Nat × Bool, e.1 < D.length ∧ tag D e.1 = true ∧
      supp 10 D (src D e) = ({0} : Finset V) ∧ supp 10 D (10+e.1) = ∅ ∧
      supp 10 D (src D (e.1,!e.2)) = ({1,4,5} : Finset V) ∧
      exitArcs 10 D (carrierT 10 D {0}) = {e} ∧
      merges 10 D (carrierT 10 D {0}) = ∅ ∧ fanout D (src D e) = 1 ∧
      ∀ g, g < D.length → tag D g = true →
        Relation.ReflTransGen (sem_step 10 D) 0 (10+g) → g = e.1 := by
  obtain ⟨e,he,ht,hs,hout,hop,hexits,hmerges,hfan⟩ :=
    single_residual_first_zero_star h hc b hb zero hi hR
  have member : (0 : V) ∈ supp 10 D (src D e) := hs.symm ▸ Finset.mem_singleton_self 0
  have chain := sem_inelig_chain h.1 hi member
  have reach : Relation.ReflTransGen (sem_step 10 D) 0 (10+e.1) :=
    Relation.ReflTransGen.tail (sem_rtg_mono (fun _ _ hh => hh.1) chain) (sem_step_src he e.2)
  refine ⟨e,he,ht,hs,hout,hop,hexits,hmerges,hfan,fun g hg htg pg => ?_⟩
  exact reachable_ands_unique_of_support_ne h hc b hb zero hi hR hne hg htg pg he ht reach

end PEqualNP.Outside.L_meta_2590_aux.I1UniqueChain

namespace PEqualNP.Outside.L_meta_2590_aux.SharedDom
open PEqualNP.Outside.L_meta_2590_aux.DagTools
open PEqualNP.Outside.L_meta_2590_aux.Four
open PEqualNP.Outside.L_meta_2590_aux.I1Exposure

lemma third_exit_pure {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (hi : (0 : V) ∈ ineligSet 10 D)
    {x : V} (hx : x ≠ 0) (small : (sem_W 10 D x).card ≤ 3)
    {e q : Nat × Bool} (he : e ∈ sem_W 10 D x) (hq : q ∈ sem_W 10 D x)
    (heq : e ≠ q)
    (hallE : ∀ a : V, Adj 0 a → a ∈ supp 10 D (src D e))
    (hallQ : ∀ a : V, Adj 0 a → a ∈ supp 10 D (src D q))
    {f : Nat × Bool} (hf : f ∈ sem_W 10 D x) (hfe : f ≠ e) (hfq : f ≠ q) :
    supp 10 D (src D f) = {x} := by
  have hxsrc : x ∈ supp 10 D (src D f) := (sem_mem_W.mp hf).2.1
  apply Finset.Subset.antisymm
  · intro d hdsrc
    simp only [Finset.mem_singleton]
    by_contra hdx
    by_cases hd : d = 0
    · have hpure := sem_inelig_pure graph_ok h.1 hc hi (hd ▸ hdsrc)
      rw [hpure,Finset.mem_singleton] at hxsrc
      exact hx hxsrc
    · obtain ⟨A,ind,hdA,hit0,hitx⟩ := i1_exposure_omit_geometry x d hx hd hdx
      obtain ⟨g,s,hg,_,hxg,hxout,free⟩ := sem_exposure graph_ok h.1 hc A ind x hitx
      have hgw : (g,s) ∈ sem_W 10 D x := sem_mem_W.mpr ⟨hg,hxg,hxout⟩
      have differs (a : Nat × Bool)
          (hallA : ∀ v : V, Adj 0 v → v ∈ supp 10 D (src D a)) : (g,s) ≠ a := by
        intro eq
        obtain ⟨v,hv,h0v⟩ := hit0
        have hva := hallA v h0v
        rw [← eq] at hva
        exact Finset.disjoint_left.mp free hva hv
      have eq := exits_equal_away_two (sem_W 10 D x) small he hq hf hgw heq hfe hfq
        (differs e hallE) (differs q hallQ)
      rw [eq] at hdsrc
      exact Finset.disjoint_left.mp free hdsrc hdA
  · exact Finset.singleton_subset_iff.mpr hxsrc

end PEqualNP.Outside.L_meta_2590_aux.SharedDom

namespace PEqualNP.Outside.L_meta_2590_aux.SharedDom
open PEqualNP.Outside.L_meta_2590_aux.DagTools
open PEqualNP.Outside.L_meta_2590_aux.Four
open PEqualNP.Outside.L_meta_2590_aux.I1Exposure

lemma common_neighbor_exit_exhausted {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (small : (sem_W 10 D 1).card ≤ 3)
    {P Q e : Nat × Bool} (hne : P ≠ Q)
    (hP : ∀ x : V, Adj 0 x → P ∈ sem_W 10 D x)
    (hQ : ∀ x : V, Adj 0 x → Q ∈ sem_W 10 D x)
    (he : ∀ x : V, Adj 0 x → e ∈ sem_W 10 D x) : e = P ∨ e = Q := by
  have n1 : Adj 0 1 := by decide +kernel
  have n4 : Adj 0 4 := by decide +kernel
  obtain ⟨A,ind,ha,_,hit⟩ := i1_exposure_omit_geometry 1 4 (by decide) (by decide) (by decide)
  obtain ⟨g,s,hg,_,hxs,hxo,free⟩ := sem_exposure graph_ok h.1 hc A ind 1 hit
  have hf : (g,s) ∈ sem_W 10 D 1 := sem_mem_W.mpr ⟨hg,hxs,hxo⟩
  have no4 : (4 : V) ∉ supp 10 D (src D (g,s)) := fun hm => Finset.disjoint_left.mp free hm ha
  have fp : (g,s) ≠ P := fun eq => no4 (eq.symm ▸ (sem_mem_W.mp (hP 4 n4)).2.1)
  have fq : (g,s) ≠ Q := fun eq => no4 (eq.symm ▸ (sem_mem_W.mp (hQ 4 n4)).2.1)
  by_contra hn
  push Not at hn
  have eq := exits_equal_away_two (sem_W 10 D 1) small (hP 1 n1) (hQ 1 n1)
    (he 1 n1) hf hne hn.1 hn.2 fp fq
  exact no4 (eq ▸ (sem_mem_W.mp (he 4 n4)).2.1)

lemma three_exit_ports {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (hi : (0 : V) ∈ ineligSet 10 D)
    {e q : Nat × Bool} (heq : e ≠ q)
    (he : ∀ x : V, Adj 0 x → e ∈ sem_W 10 D x)
    (hq : ∀ x : V, Adj 0 x → q ∈ sem_W 10 D x)
    {x : V} (hx : Adj 0 x) (three : (sem_W 10 D x).card = 3) :
    ∃ f : Nat × Bool, sem_W 10 D x = {e,q,f} ∧
      f ≠ e ∧ f ≠ q ∧ supp 10 D (src D f) = {x} := by
  classical
  have sub : ({e,q} : Finset (Nat × Bool)) ⊆ sem_W 10 D x := by
    intro f hf
    simp only [Finset.mem_insert,Finset.mem_singleton] at hf
    rcases hf with rfl | rfl
    · exact he x hx
    · exact hq x hx
  have pair : ({e,q} : Finset (Nat × Bool)).card = 2 := by simp [heq]
  have split := Finset.card_sdiff_add_card_eq_card sub
  have positive : 0 < (sem_W 10 D x \ {e,q}).card := by omega
  obtain ⟨f,hf⟩ := Finset.card_pos.mp positive
  obtain ⟨hfw,hfnot⟩ := Finset.mem_sdiff.mp hf
  have hfe : f ≠ e := fun eq => hfnot (by simp [eq])
  have hfq : f ≠ q := fun eq => hfnot (by simp [eq])
  have sub3 : ({e,q,f} : Finset (Nat × Bool)) ⊆ sem_W 10 D x := by
    intro v hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact he x hx
    · exact hq x hx
    · exact hfw
  have card3 : ({e,q,f} : Finset (Nat × Bool)).card = 3 := by
    simp [heq,Ne.symm hfe,Ne.symm hfq]
  have eq := Finset.eq_of_subset_of_card_le sub3 (by omega)
  refine ⟨f,eq.symm,hfe,hfq,?_⟩
  exact third_exit_pure h hc hi (x := x) (fun eq => graph_ok.2.1 0 (eq ▸ hx))
    (by omega) (he x hx) (hq x hx) heq
    (fun a ha => (sem_mem_W.mp (he a ha)).2.1)
    (fun a ha => (sem_mem_W.mp (hq a ha)).2.1) hfw hfe hfq

lemma case50_ports_of_common {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (hi : (0 : V) ∈ ineligSet 10 D) (star : FirstZeroStar D)
    (sat : ∀ x : V, Adj 0 x → (sem_W 10 D x).card = 3)
    {P Q : Nat × Bool} (hpq : P.1 ≠ Q.1)
    (common : ∀ x : V, Adj 0 x → P ∈ sem_W 10 D x ∧ Q ∈ sem_W 10 D x) :
    ∃ e q : Nat × Bool, e.1 < D.length ∧ tag D e.1 = true ∧
      supp 10 D (src D e) = ({0} : Finset V) ∧
      supp 10 D (src D (sem_bar e)) = ({1,4,5} : Finset V) ∧
      supp 10 D (10 + e.1) = ∅ ∧ e.1 ≠ q.1 ∧
      (∀ x : V, Adj 0 x → q ∈ sem_W 10 D x) ∧
      ∀ x : V, Adj 0 x → ∃ f : Nat × Bool,
        sem_W 10 D x = {sem_bar e,q,f} ∧ f ≠ sem_bar e ∧ f ≠ q ∧
          supp 10 D (src D f) = {x} := by
  obtain ⟨e,he,ht,hs,hn,hm,_,_,_⟩ := star
  have hmate (x : V) (hx : Adj 0 x) : sem_bar e ∈ sem_W 10 D x := by
    apply sem_mem_W.mpr
    refine ⟨he,?_,?_⟩
    · exact hm.symm ▸ (zero_neighbors x).mp hx
    · change x ∉ supp 10 D (10 + e.1)
      rw [hn]
      simp
  have ne : P ≠ Q := fun eq => hpq (congrArg Prod.fst eq)
  have member := common_neighbor_exit_exhausted h hc (by rw [sat 1 (by decide +kernel)]) ne
    (fun x hx => (common x hx).1) (fun x hx => (common x hx).2) hmate
  obtain ⟨q,neq,hq⟩ : ∃ q : Nat × Bool, e.1 ≠ q.1 ∧
      ∀ x : V, Adj 0 x → q ∈ sem_W 10 D x := by
    rcases member with ep | eq
    · refine ⟨Q,?_,fun x hx => (common x hx).2⟩
      have hep := congrArg Prod.fst ep
      change e.1 = P.1 at hep
      exact hep ▸ hpq
    · refine ⟨P,?_,fun x hx => (common x hx).1⟩
      have heq := congrArg Prod.fst eq
      change e.1 = Q.1 at heq
      exact heq ▸ Ne.symm hpq
  refine ⟨e,q,he,ht,hs,hm,hn,neq,hq,?_⟩
  intro x hx
  exact three_exit_ports h hc hi (e := sem_bar e) (q := q) (x := x)
    (by intro eq; have hf := congrArg Prod.fst eq; exact neq hf) hmate hq hx (sat x hx)

lemma case50_budget_ports_of_common {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (zero : Bzero 10 D = 0) (hi : (0 : V) ∈ ineligSet 10 D)
    (budget : Bplus 10 D = (eligSet 10 D).card + 1)
    (sat : ∀ x : V, Adj 0 x → (sem_W 10 D x).card = 3)
    {P Q : Nat × Bool} (hpq : P.1 ≠ Q.1)
    (common : ∀ x : V, Adj 0 x → P ∈ sem_W 10 D x ∧ Q ∈ sem_W 10 D x) :
    ∃ e q : Nat × Bool, e.1 < D.length ∧ tag D e.1 = true ∧
      supp 10 D (src D e) = ({0} : Finset V) ∧
      supp 10 D (src D (sem_bar e)) = ({1,4,5} : Finset V) ∧
      supp 10 D (10 + e.1) = ∅ ∧ e.1 ≠ q.1 ∧
      (∀ x : V, Adj 0 x → q ∈ sem_W 10 D x) ∧
      ∀ x : V, Adj 0 x → ∃ f : Nat × Bool,
        sem_W 10 D x = {sem_bar e,q,f} ∧ f ≠ sem_bar e ∧ f ≠ q ∧
          supp 10 D (src D f) = {x} :=
  case50_ports_of_common h hc hi (budget_one_first_zero_star h hc zero hi budget) sat hpq common

end PEqualNP.Outside.L_meta_2590_aux.SharedDom


namespace PEqualNP.Outside.L_meta_2590_aux.S50Meeting
open DagTools Four

lemma edge_slots_away_one {n : Nat} {D : Dag} {G : Fin n → Fin n → Prop}
    (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {x y i : Fin n} (hxy : G x y) (hyi : y ≠ i)
    {e q f : Nat × Bool} (cover : sem_W n D x ⊆ {e,q,f})
    (epure : supp n D (src D (sem_bar e)) ⊆ {i}) :
    (sem_bar q ∈ sem_W n D y ∧ y ∉ supp n D (src D q) ∧
      x ∉ supp n D (src D (sem_bar q)) ∧
      val D (sem_two x y) (n + q.1) = true) ∨
    (sem_bar f ∈ sem_W n D y ∧ y ∉ supp n D (src D f) ∧
      x ∉ supp n D (src D (sem_bar f)) ∧
      val D (sem_two x y) (n + f.1) = true) := by
  obtain ⟨a,ha,hb,hy,hx,hval⟩ := sem_edge_slots hG hS hC hxy
  have member := cover ha
  simp only [Finset.mem_insert,Finset.mem_singleton] at member
  rcases member with rfl | rfl | rfl
  · exact False.elim (hyi (Finset.mem_singleton.mp (epure (sem_mem_W.mp hb).2.1)))
  · exact Or.inl ⟨hb,hy,hx,hval⟩
  · exact Or.inr ⟨hb,hy,hx,hval⟩

lemma edge_private_of_empty_opposite {n : Nat} {D : Dag} {G : Fin n → Fin n → Prop}
    (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {x y i : Fin n} (hxy : G x y) (hyi : y ≠ i)
    {e q f : Nat × Bool} (cover : sem_W n D x ⊆ {e,q,f})
    (epure : supp n D (src D (sem_bar e)) ⊆ {i})
    (qempty : supp n D (src D (sem_bar q)) = ∅) :
    sem_bar f ∈ sem_W n D y ∧ y ∉ supp n D (src D f) ∧
      x ∉ supp n D (src D (sem_bar f)) ∧
      val D (sem_two x y) (n + f.1) = true := by
  rcases edge_slots_away_one hG hS hC hxy hyi cover epure with hq | hf
  · have hy := (sem_mem_W.mp hq.1).2.1
    rw [qempty] at hy
    exact False.elim (Finset.notMem_empty _ hy)
  · exact hf

lemma case50_edge_coverage {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    {x y : V} (hxy : Adj x y) (hy : y ≠ 0)
    {e q f : Nat × Bool} (cover : sem_W 10 D x = {sem_bar e,q,f})
    (epure : supp 10 D (src D e) = {0}) :
    (sem_bar q ∈ sem_W 10 D y ∧ y ∉ supp 10 D (src D q) ∧
      x ∉ supp 10 D (src D (sem_bar q)) ∧
      val D (sem_two x y) (10 + q.1) = true) ∨
    (sem_bar f ∈ sem_W 10 D y ∧ y ∉ supp 10 D (src D f) ∧
      x ∉ supp 10 D (src D (sem_bar f)) ∧
      val D (sem_two x y) (10 + f.1) = true) := by
  apply edge_slots_away_one graph_ok h.1 hc hxy hy cover.subset
  simp [sem_bar,epure]

lemma case50_private_neighbors {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    {x : V} {e q f : Nat × Bool}
    (cover : sem_W 10 D x = {sem_bar e,q,f})
    (epure : supp 10 D (src D e) = {0})
    (qempty : supp 10 D (src D (sem_bar q)) = ∅) :
    ∀ y : V, Adj x y → y ≠ 0 →
      sem_bar f ∈ sem_W 10 D y ∧ y ∈ supp 10 D (src D (sem_bar f)) := by
  intro y hxy hy
  rcases case50_edge_coverage h hc hxy hy cover epure with hq | hf
  · have mem := (sem_mem_W.mp hq.1).2.1
    rw [qempty] at mem
    exact False.elim (Finset.notMem_empty _ mem)
  · exact ⟨hf.1,(sem_mem_W.mp hf.1).2.1⟩

end PEqualNP.Outside.L_meta_2590_aux.S50Meeting


namespace PEqualNP.Outside.L_meta_2590_aux.S50Private
open DagTools Four S50Meeting

lemma bar_bar (a : Nat × Bool) : sem_bar (sem_bar a) = a := by simp [sem_bar]

lemma exit_opposite_excludes {n : Nat} {D : Dag} (h : Strict n D)
    {x : Fin n} {a : Nat × Bool} (ha : a ∈ sem_W n D x) :
    x ∉ supp n D (src D (sem_bar a)) := by
  obtain ⟨j,s⟩ := a
  obtain ⟨hj,hxs,hxo⟩ := sem_mem_W.mp ha
  have ht := sem_W_and h ha
  intro hbar
  apply hxo
  rw [sem_supp_and h hj ht]
  cases s <;> simpa [sem_bar,src,Finset.mem_inter,and_comm] using And.intro hxs hbar

lemma pure_mate_exit {n : Nat} {D : Dag} (h : Strict n D)
    {x y : Fin n} {a : Nat × Bool} (ha : a ∈ sem_W n D x)
    (hp : supp n D (src D a) = {x}) (hyx : y ≠ x)
    (hy : y ∈ supp n D (src D (sem_bar a))) : sem_bar a ∈ sem_W n D y := by
  obtain ⟨hj,hxs,hxo⟩ := sem_mem_W.mp ha
  apply sem_mem_W.mpr
  refine ⟨hj,hy,?_⟩
  intro hout
  have hsub := sem_supp_and_sub h hj (sem_W_and h ha) a.2
  change y ∈ supp n D (n + a.1) at hout
  have hs := hsub hout
  change y ∈ supp n D (src D a) at hs
  rw [hp,Finset.mem_singleton] at hs
  exact hyx hs

lemma mem_of_card_le_two {α : Type*} [DecidableEq α] (S : Finset α)
    (small : S.card ≤ 2) {a b c : α} (ha : a ∈ S) (hb : b ∈ S)
    (hc : c ∈ S) (hab : a ≠ b) : c = a ∨ c = b := by
  by_contra hn
  push Not at hn
  have sub : ({a,b,c} : Finset α) ⊆ S := by
    intro v hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl <;> assumption
  have card : ({a,b,c} : Finset α).card = 3 := by
    simp [hab,Ne.symm hn.1,Ne.symm hn.2]
  have := Finset.card_le_card sub
  omega

lemma two_exit_neighbor_coverage {n : Nat} {D : Dag} {G : Fin n → Fin n → Prop}
    (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {x y : Fin n} (hxy : G x y) (small : (sem_W n D x).card ≤ 2)
    {a b : Nat × Bool} (ha : a ∈ sem_W n D x) (hb : b ∈ sem_W n D x)
    (hab : a ≠ b) :
    y ∈ supp n D (src D (sem_bar a)) ∨ y ∈ supp n D (src D (sem_bar b)) := by
  obtain ⟨e,he,hbar,_⟩ := sem_edge_slots hG hS hC hxy
  have hs := (sem_mem_W.mp hbar).2.1
  rcases mem_of_card_le_two (sem_W n D x) small ha hb he hab with rfl | rfl
  · exact Or.inl hs
  · exact Or.inr hs

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 1000000 in
lemma outside_neighbor : ∀ x : V, Adj 0 x →
    ∃ c : V, Adj x c ∧ c ≠ 0 ∧ ¬ Adj 0 c := by
  unfold Adj
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 1000000 in
lemma outside_neighbors : ∀ y : V, y ≠ 0 → ¬ Adj 0 y →
    ∃ a z : V, Adj 0 a ∧ Adj a y ∧ Adj y z ∧ z ≠ 0 ∧ ¬ Adj 0 z := by
  unfold Adj
  decide +kernel

lemma private_mates_exact_of_no_opposite_exit {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (hi : (0 : V) ∈ ineligSet 10 D)
    {e q : Nat × Bool} (f : V → Nat × Bool)
    (epure : supp 10 D (src D e) = {0})
    (qno : ∀ y : V, sem_bar q ∉ sem_W 10 D y)
    (cover : ∀ x : V, Adj 0 x → sem_W 10 D x = {sem_bar e,q,f x})
    (pure : ∀ x : V, Adj 0 x → supp 10 D (src D (f x)) = {x})
    (small : ∀ y : V, y ≠ 0 → ¬ Adj 0 y → (sem_W 10 D y).card ≤ 2) :
    ∀ x : V, Adj 0 x →
      supp 10 D (src D (sem_bar (f x))) = Finset.univ.filter (fun y => Adj x y ∧ y ≠ 0) := by
  classical
  have fxmem (x : V) (hx : Adj 0 x) : f x ∈ sem_W 10 D x := by rw [cover x hx]; simp
  have lower (x : V) (hx : Adj 0 x) (y : V) (hxy : Adj x y) (hy0 : y ≠ 0) :
      sem_bar (f x) ∈ sem_W 10 D y ∧ y ∈ supp 10 D (src D (sem_bar (f x))) := by
    rcases case50_edge_coverage h hc hxy hy0 (cover x hx) epure with hq | hf
    · exact False.elim (qno y hq.1)
    · exact ⟨hf.1,(sem_mem_W.mp hf.1).2.1⟩
  intro x hx
  have hx0 : x ≠ 0 := fun eq => graph_ok.2.1 0 (eq ▸ hx)
  obtain ⟨c,hxc,hc0,hcN⟩ := outside_neighbor x hx
  have hcP := (lower x hx c hxc hc0).2
  apply Finset.Subset.antisymm
  · intro y hy
    have hy0 : y ≠ 0 := by
      intro eq
      have zero : (0 : V) ∈ supp 10 D (src D (sem_bar (f x))) := eq ▸ hy
      have hp := sem_inelig_pure graph_ok h.1 hc hi zero
      rw [hp,Finset.mem_singleton] at hcP
      exact hc0 hcP
    have hyx : y ≠ x := fun eq => exit_opposite_excludes h.1 (fxmem x hx) (eq ▸ hy)
    have hymem : sem_bar (f x) ∈ sem_W 10 D y := pure_mate_exit h.1 (fxmem x hx) (pure x hx) hyx hy
    have hyN : ¬ Adj 0 y := by
      intro h0y
      rw [cover y h0y] at hymem
      simp only [Finset.mem_insert,Finset.mem_singleton] at hymem
      rcases hymem with hye | hyq | hyf
      · have eq : f x = e := by simpa only [bar_bar] using congrArg sem_bar hye
        have hs : ({x} : Finset V) = {0} := by rw [← pure x hx,eq,epure]
        exact hx0 (Finset.singleton_inj.mp hs)
      · have eq : f x = sem_bar q := by simpa only [bar_bar] using congrArg sem_bar hyq
        exact qno x (eq ▸ fxmem x hx)
      · have hp : supp 10 D (src D (sem_bar (f x))) = {y} := by rw [hyf,pure y h0y]
        rw [hp,Finset.mem_singleton] at hcP
        exact hcN (hcP ▸ h0y)
    have hxy : Adj x y := by
      by_contra hxy
      obtain ⟨a,z,haN,hay,hyz,hz0,hzN⟩ := outside_neighbors y hy0 hyN
      have hamem := (lower a haN y hay hy0).1
      have hax : a ≠ x := fun eq => hxy (eq ▸ hay)
      have hne : sem_bar (f x) ≠ sem_bar (f a) := by
        intro eq
        have feq : f x = f a := by simpa only [bar_bar] using congrArg sem_bar eq
        have seq : ({x} : Finset V) = {a} := by rw [← pure x hx,feq,pure a haN]
        exact hax (Finset.singleton_inj.mp seq).symm
      have hz := two_exit_neighbor_coverage graph_ok h.1 hc hyz (small y hy0 hyN) hymem hamem hne
      simp only [bar_bar,pure x hx,pure a haN,Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hzN hx
      · exact hzN haN
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ y,hxy,hy0⟩
  · intro y hy
    obtain ⟨_,hxy,hy0⟩ := Finset.mem_filter.mp hy
    exact (lower x hx y hxy hy0).2

lemma opposite_subset_no_exit {n : Nat} {D : Dag} (h : Strict n D)
    {q : Nat × Bool} (sub : supp n D (src D (sem_bar q)) ⊆ supp n D (src D q)) :
    ∀ y : Fin n, sem_bar q ∉ sem_W n D y := by
  intro y hy
  have hn := exit_opposite_excludes h hy
  rw [bar_bar] at hn
  exact hn (sub (sem_mem_W.mp hy).2.1)

lemma private_mates_exact_of_opposite_subset {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (hi : (0 : V) ∈ ineligSet 10 D)
    {e q : Nat × Bool} (f : V → Nat × Bool)
    (epure : supp 10 D (src D e) = {0})
    (qsub : supp 10 D (src D (sem_bar q)) ⊆ supp 10 D (src D q))
    (cover : ∀ x : V, Adj 0 x → sem_W 10 D x = {sem_bar e,q,f x})
    (pure : ∀ x : V, Adj 0 x → supp 10 D (src D (f x)) = {x})
    (small : ∀ y : V, y ≠ 0 → ¬ Adj 0 y → (sem_W 10 D y).card ≤ 2) :
    ∀ x : V, Adj 0 x →
      supp 10 D (src D (sem_bar (f x))) = Finset.univ.filter (fun y => Adj x y ∧ y ≠ 0) :=
  private_mates_exact_of_no_opposite_exit h hc hi f epure
    (opposite_subset_no_exit h.1 qsub) cover pure small

lemma private_mates_exact {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (hi : (0 : V) ∈ ineligSet 10 D)
    {e q : Nat × Bool} (f : V → Nat × Bool)
    (epure : supp 10 D (src D e) = {0})
    (qempty : supp 10 D (src D (sem_bar q)) = ∅)
    (cover : ∀ x : V, Adj 0 x → sem_W 10 D x = {sem_bar e,q,f x})
    (pure : ∀ x : V, Adj 0 x → supp 10 D (src D (f x)) = {x})
    (small : ∀ y : V, y ≠ 0 → ¬ Adj 0 y → (sem_W 10 D y).card ≤ 2) :
    ∀ x : V, Adj 0 x →
      supp 10 D (src D (sem_bar (f x))) = Finset.univ.filter (fun y => Adj x y ∧ y ≠ 0) := by
  apply private_mates_exact_of_opposite_subset h hc hi f epure _ cover pure small
  rw [qempty]
  exact Finset.empty_subset _

end PEqualNP.Outside.L_meta_2590_aux.S50Private


namespace PEqualNP.Outside.L_meta_2590_aux.SharedDom
open PEqualNP.Outside.L_meta_2590_aux.DagTools
open PEqualNP.Outside.L_meta_2590_aux.Four
open PEqualNP.Outside.L_meta_2590_aux.I1Exposure
open PEqualNP.Outside.L_meta_2590_aux.S50Meeting

lemma case50_residual_support {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (b : V → Nat) (hb : PureBranch 10 D b)
    (zero : Bzero 10 D = 0) (hi : (0 : V) ∈ ineligSet 10 D)
    {r : Sigma (fun _ : Nat => Nat)} (hR : residualUnits 10 D b = {r})
    (sat : ∀ x : V, Adj 0 x → 3 ≤ (sem_W 10 D x).card) :
    supp 10 D r.1 = ({1,4,5} : Finset V) := by
  classical
  have coded (x : V) (hx : Adj 0 x) : x ∈ supp 10 D r.1 := by
    have count := sem_code_count graph_ok h hc b hb x
    have single : (({x} : Finset V) ∩ eligSet 10 D).card ≤ 1 :=
      (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
    have three := sat x hx
    have positive : 0 < ((residualUnits 10 D b).filter (fun u => x ∈ supp 10 D u.1)).card := by omega
    obtain ⟨u,hu⟩ := Finset.card_pos.mp positive
    obtain ⟨hu,hxu⟩ := Finset.mem_filter.mp hu
    have eq : u = r := by simpa only [hR,Finset.mem_singleton] using hu
    exact eq ▸ hxu
  apply Finset.Subset.antisymm
  · exact single_residual_support_subset_of_bzero h hc b hb zero hi hR
      ⟨1,by decide +kernel,coded 1 (by decide +kernel)⟩
  · intro x hx
    exact coded x ((zero_neighbors x).mpr hx)

lemma common_gate_output_empty {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (b : V → Nat) (hb : PureBranch 10 D b)
    (hi : (0 : V) ∈ ineligSet 10 D)
    {r : Sigma (fun _ : Nat => Nat)} (hR : residualUnits 10 D b = {r})
    (hS : supp 10 D r.1 = ({1,4,5} : Finset V))
    {e q : Nat × Bool} (epure : supp 10 D (src D e) = {0})
    (hq : ∀ x : V, Adj 0 x → q ∈ sem_W 10 D x)
    (ports : ∀ x : V, Adj 0 x → ∃ f : Nat × Bool,
      sem_W 10 D x = {sem_bar e,q,f} ∧ supp 10 D (src D f) = {x}) :
    supp 10 D (10 + q.1) = ∅ := by
  classical
  have hq1 := hq 1 (by decide +kernel)
  have valid := (sem_mem_W.mp hq1).1
  have tagq := sem_W_and h.1 hq1
  apply Finset.eq_empty_of_forall_notMem
  intro c hcout
  have hcs := sem_supp_and_sub h.1 valid tagq q.2 hcout
  have hcn : ¬ Adj 0 c := fun h0c => (sem_mem_W.mp (hq c h0c)).2.2 hcout
  have hc0 : c ≠ 0 := by
    intro eq
    have hz : (0 : V) ∈ supp 10 D (src D q) := eq ▸ hcs
    have pure := sem_inelig_pure graph_ok h.1 hc hi hz
    have hone := (sem_mem_W.mp hq1).2.1
    rw [pure,Finset.mem_singleton] at hone
    exact (by decide : (1 : V) ≠ 0) hone
  obtain ⟨j,_,h0j,hjc,_,_,_⟩ := dirty_neighbor_geometry c hc0 hcn
  obtain ⟨f,cover,fpure⟩ := ports j h0j
  have hfc : sem_bar f ∈ sem_W 10 D c := by
    rcases case50_edge_coverage h hc hjc hc0 cover epure with hcase | hcase
    · exact False.elim (hcase.2.1 hcs)
    · exact hcase.1
  obtain ⟨d,hcd,hdj⟩ := graph_ok.2.2.2 c j
  obtain ⟨z,hz,hbz,_,_,_⟩ := sem_edge_slots graph_ok h.1 hc hcd
  have hne : z ≠ sem_bar f := by
    intro eq
    have hd : d ∈ supp 10 D (src D f) := by
      simpa [eq,sem_bar] using (sem_mem_W.mp hbz).2.1
    rw [fpure,Finset.mem_singleton] at hd
    exact hdj hd
  have sub : {z,sem_bar f} ⊆ sem_W 10 D c := by
    intro v hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> assumption
  have two : 2 ≤ (sem_W 10 D c).card := by
    have bound := Finset.card_le_card sub
    simpa [hne] using bound
  have count := sem_code_count graph_ok h hc b hb c
  have single : (({c} : Finset V) ∩ eligSet 10 D).card ≤ 1 :=
    (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
  have filt : ((residualUnits 10 D b).filter (fun u => c ∈ supp 10 D u.1)) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro u hu
    obtain ⟨hu,hcu⟩ := Finset.mem_filter.mp hu
    have eq : u = r := by simpa only [hR,Finset.mem_singleton] using hu
    rw [eq,hS] at hcu
    exact hcn ((zero_neighbors c).mpr hcu)
  have hop : c ∈ supp 10 D (opA D q.1) ∧ c ∈ supp 10 D (opB D q.1) := by
    have hh := hcout
    rw [supp_gate h.1 q.1 valid] at hh
    simpa [tagq] using hh
  have hmerge : q.1 ∈ merges 10 D (carrierT 10 D {c}) := by
    simp only [merges,Finset.mem_filter,Finset.mem_range,sem_mem_carrier1]
    exact ⟨valid,hcout,hop.1,hop.2⟩
  have positive : 0 < (merges 10 D (carrierT 10 D {c})).card := Finset.card_pos.mpr ⟨q.1,hmerge⟩
  rw [filt,Finset.card_empty] at count
  omega

end PEqualNP.Outside.L_meta_2590_aux.SharedDom


namespace PEqualNP.Outside.L_meta_2590_aux.SharedDom
open DagTools Four S50Meeting S50Private I1Exposure

lemma two_exits_of_distinct {D : Dag} {c : V} {a b : Nat × Bool}
    (ha : a ∈ sem_W 10 D c) (hb : b ∈ sem_W 10 D c) (hab : a ≠ b) :
    2 ≤ (sem_W 10 D c).card := by
  have sub : ({a,b} : Finset (Nat × Bool)) ⊆ sem_W 10 D c := by
    intro v hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> assumption
  have bound := Finset.card_le_card sub
  simpa [hab] using bound

lemma outside_two_exits_of_large_opposite {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (hi : (0 : V) ∈ ineligSet 10 D)
    {e q : Nat × Bool} (epure : supp 10 D (src D e) = {0})
    (hq : ∀ x : V, Adj 0 x → q ∈ sem_W 10 D x)
    (ports : ∀ x : V, Adj 0 x → ∃ f : Nat × Bool,
      sem_W 10 D x = {sem_bar e,q,f} ∧ supp 10 D (src D f) = {x})
    (emptyout : supp 10 D (10 + q.1) = ∅)
    (large : (∃ u : V, u ≠ 0 ∧ ¬ Adj 0 u ∧ u ∈ supp 10 D (src D q)) →
      2 ≤ (supp 10 D (src D (sem_bar q))).card)
    {c : V} (hc0 : c ≠ 0) (hcN : ¬ Adj 0 c) : 2 ≤ (sem_W 10 D c).card := by
  classical
  have hq1 := hq 1 (by decide +kernel)
  have valid := (sem_mem_W.mp hq1).1
  obtain ⟨j,d,hj,hjc,hcd,hd0,hdN⟩ := outside_neighbors c hc0 hcN
  by_cases hct : c ∈ supp 10 D (src D (sem_bar q))
  · have hqc : sem_bar q ∈ sem_W 10 D c := by
      apply sem_mem_W.mpr
      refine ⟨valid,hct,?_⟩
      change c ∉ supp 10 D (10 + q.1)
      rw [emptyout]
      exact Finset.notMem_empty c
    by_cases extra : ∃ u : V, u ≠ 0 ∧ ¬ Adj 0 u ∧ u ∈ supp 10 D (src D q)
    · have big := large extra
      have another : ∃ a : V, a ∈ supp 10 D (src D (sem_bar q)) ∧ a ≠ c := by
        by_contra hn
        push Not at hn
        have sub : supp 10 D (src D (sem_bar q)) ⊆ {c} := by
          intro a ha
          exact Finset.mem_singleton.mpr (hn a ha)
        have bound := Finset.card_le_card sub
        simp only [Finset.card_singleton] at bound
        omega
      obtain ⟨a,ha,hac⟩ := another
      have ha0 : a ≠ 0 := by
        intro eq
        have hp := sem_inelig_pure graph_ok h.1 hc hi (eq ▸ ha)
        rw [hp,Finset.mem_singleton] at hct
        exact hc0 hct
      obtain ⟨A,hA,haA,_,hitc⟩ := i1_exposure_omit_geometry c a hc0 ha0 hac
      obtain ⟨g,s,hg,_,hcg,hcgo,free⟩ := sem_exposure graph_ok h.1 hc A hA c hitc
      have hgW : (g,s) ∈ sem_W 10 D c := sem_mem_W.mpr ⟨hg,hcg,hcgo⟩
      have hneq : (g,s) ≠ sem_bar q := by
        intro eq
        rw [eq] at free
        exact Finset.disjoint_left.mp free ha haA
      exact two_exits_of_distinct hgW hqc hneq
    · obtain ⟨z,hz,hbz,_,_,_⟩ := sem_edge_slots graph_ok h.1 hc hcd
      have hneq : z ≠ sem_bar q := by
        intro eq
        have hds : d ∈ supp 10 D (src D q) := by
          simpa only [eq,bar_bar] using (sem_mem_W.mp hbz).2.1
        exact extra ⟨d,hd0,hdN,hds⟩
      exact two_exits_of_distinct hz hqc hneq
  · obtain ⟨f,cover,fpure⟩ := ports j hj
    have hf : sem_bar f ∈ sem_W 10 D c := by
      rcases case50_edge_coverage h hc hjc hc0 cover epure with hcase | hcase
      · exact False.elim (hct (sem_mem_W.mp hcase.1).2.1)
      · exact hcase.1
    obtain ⟨z,hz,hbz,_,_,_⟩ := sem_edge_slots graph_ok h.1 hc hcd
    have hneq : z ≠ sem_bar f := by
      intro eq
      have hds : d ∈ supp 10 D (src D f) := by
        simpa only [eq,bar_bar] using (sem_mem_W.mp hbz).2.1
      rw [fpure,Finset.mem_singleton] at hds
      exact hdN (hds ▸ hj)
    exact two_exits_of_distinct hz hf hneq

lemma case50_no_singleton_merges_of_outside_two {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (b : V → Nat) (hb : PureBranch 10 D b)
    (hi : (0 : V) ∈ ineligSet 10 D)
    {r : Sigma (fun _ : Nat => Nat)} (hR : residualUnits 10 D b = {r})
    (hS : supp 10 D r.1 = ({1,4,5} : Finset V))
    (sat : ∀ x : V, Adj 0 x → 3 ≤ (sem_W 10 D x).card)
    (outside : ∀ x : V, x ≠ 0 → ¬ Adj 0 x → 2 ≤ (sem_W 10 D x).card) :
    (∀ x : V, merges 10 D (carrierT 10 D {x}) = ∅) ∧
    (∀ x : V, x ≠ 0 → ¬ Adj 0 x → (sem_W 10 D x).card = 2) := by
  classical
  have getcount (x : V) := sem_code_count graph_ok h hc b hb x
  have single (x : V) : (({x} : Finset V) ∩ eligSet 10 D).card ≤ 1 :=
    (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
  have rcount (x : V) : ((residualUnits 10 D b).filter (fun u => x ∈ supp 10 D u.1)).card ≤ 1 := by
    have sub := Finset.filter_subset (fun u => x ∈ supp 10 D u.1) (residualUnits 10 D b)
    have bound := Finset.card_le_card sub
    simpa [hR] using bound
  have outsidecount (x : V) (hx : ¬ Adj 0 x) :
      (sem_W 10 D x).card + (merges 10 D (carrierT 10 D {x})).card ≤ 2 := by
    have count := getcount x
    have one := single x
    have filt : ((residualUnits 10 D b).filter (fun u => x ∈ supp 10 D u.1)) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro u hu
      obtain ⟨hu,hxu⟩ := Finset.mem_filter.mp hu
      have eq : u = r := by simpa only [hR,Finset.mem_singleton] using hu
      rw [eq,hS] at hxu
      exact hx ((zero_neighbors x).mpr hxu)
    rw [filt,Finset.card_empty] at count
    omega
  constructor
  · intro x
    apply Finset.card_eq_zero.mp
    by_cases hx0 : x = 0
    · subst x
      obtain ⟨e,_,_,_,_,_,_,hm⟩ := sem_inelig_consumer graph_ok h hc hi
      simp [hm]
    · by_cases hxN : Adj 0 x
      · have count := getcount x
        have one := single x
        have residual := rcount x
        have three := sat x hxN
        omega
      · have bound := outsidecount x hxN
        have two := outside x hx0 hxN
        omega
  · intro x hx0 hxN
    have bound := outsidecount x hxN
    have two := outside x hx0 hxN
    omega

lemma and_output_empty_of_no_singleton_merges {D : Dag}
    (h : Strict 10 D)
    (none : ∀ x : V, merges 10 D (carrierT 10 D {x}) = ∅)
    {j : Nat} (hj : j < D.length) (ht : tag D j = true) :
    supp 10 D (10 + j) = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro x hx
  have hop : x ∈ supp 10 D (opA D j) ∧ x ∈ supp 10 D (opB D j) := by
    have hh := hx
    rw [supp_gate h j hj] at hh
    simpa [ht] using hh
  have hm : j ∈ merges 10 D (carrierT 10 D {x}) := by
    simp only [merges,Finset.mem_filter,Finset.mem_range,sem_mem_carrier1]
    exact ⟨hj,hx,hop.1,hop.2⟩
  rw [none x] at hm
  exact Finset.notMem_empty _ hm

end PEqualNP.Outside.L_meta_2590_aux.SharedDom


namespace PEqualNP.Outside.L_meta_2590_aux.S50ExtraSource
open DagTools Four SharedDom S50Meeting S50Private

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 1000000 in
lemma three_opposite_geometry : ∀ u : V, u ≠ 0 → ¬ Adj 0 u →
    ∃ x v w p : V, Adj 0 x ∧ Adj x u ∧ Adj u v ∧ Adj u w ∧ Adj x p ∧
      v ≠ x ∧ w ≠ x ∧ p ≠ 0 ∧ p ≠ u ∧ v ≠ w ∧ v ≠ p ∧ w ≠ p := by
  unfold Adj
  decide +kernel

lemma extra_common_source_forces_three {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (hi : (0 : V) ∈ ineligSet 10 D)
    {e q : Nat × Bool} (epure : supp 10 D (src D e) = {0})
    (hq : ∀ x : V, Adj 0 x → q ∈ sem_W 10 D x)
    (qout : supp 10 D (10 + q.1) = ∅)
    (ports : ∀ x : V, Adj 0 x → ∃ f : Nat × Bool,
      sem_W 10 D x = {sem_bar e,q,f} ∧ supp 10 D (src D f) = {x})
    {u : V} (hu0 : u ≠ 0) (huN : ¬ Adj 0 u)
    (small : (sem_W 10 D u).card ≤ 2) (huq : u ∈ supp 10 D (src D q)) :
    3 ≤ (supp 10 D (src D (sem_bar q))).card := by
  classical
  obtain ⟨x,v,w,p,hxN,hxu,huv,huw,hxp,hvx,hwx,hp0,hpu,hvw,hvp,hwp⟩ :=
    three_opposite_geometry u hu0 huN
  obtain ⟨f,cover,fpure⟩ := ports x hxN
  have fxmem : f ∈ sem_W 10 D x := by rw [cover]; simp
  have qxu := hq x hxN
  have qvalid := (sem_mem_W.mp qxu).1
  have qumem : q ∈ sem_W 10 D u := by
    apply sem_mem_W.mpr
    exact ⟨qvalid,huq,by rw [qout]; simp⟩
  have fumem : sem_bar f ∈ sem_W 10 D u := by
    rcases case50_edge_coverage h hc hxu hu0 cover epure with hh | hh
    · exact False.elim (hh.2.1 huq)
    · exact hh.1
  have fne : sem_bar f ≠ q := by
    intro eq
    have hm := (sem_mem_W.mp qxu).2.1
    rw [← eq] at hm
    exact exit_opposite_excludes h.1 fxmem hm
  have fpureU : supp 10 D (src D (sem_bar f)) = {u} :=
    other_exit_pure h hc hi hu0 small qumem
      (fun a ha => (sem_mem_W.mp (hq a ha)).2.1) fumem fne
  have other (z : V) (huz : Adj u z) (hzx : z ≠ x) :
      z ∈ supp 10 D (src D (sem_bar q)) := by
    obtain ⟨a,ha,hza,_⟩ := sem_edge_slots graph_ok h.1 hc huz
    have hm := (sem_mem_W.mp hza).2.1
    rcases mem_of_card_le_two (sem_W 10 D u) small qumem fumem ha (Ne.symm fne) with he | he
    · exact he ▸ hm
    · rw [he,bar_bar,fpure,Finset.mem_singleton] at hm
      exact False.elim (hzx hm)
  have hv := other v huv hvx
  have hw := other w huw hwx
  have hp : p ∈ supp 10 D (src D (sem_bar q)) := by
    rcases case50_edge_coverage h hc hxp hp0 cover epure with hh | hh
    · exact (sem_mem_W.mp hh.1).2.1
    · have hm := (sem_mem_W.mp hh.1).2.1
      rw [fpureU,Finset.mem_singleton] at hm
      exact False.elim (hpu hm)
  have sub : ({v,w,p} : Finset V) ⊆ supp 10 D (src D (sem_bar q)) := by
    intro z hz
    simp only [Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl <;> assumption
  have card : ({v,w,p} : Finset V).card = 3 := by simp [hvw,hvp,hwp]
  have count := Finset.card_le_card sub
  omega

lemma small_opposite_forces_common_source {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (hi : (0 : V) ∈ ineligSet 10 D)
    {e q : Nat × Bool} (epure : supp 10 D (src D e) = {0})
    (hq : ∀ x : V, Adj 0 x → q ∈ sem_W 10 D x)
    (qout : supp 10 D (10 + q.1) = ∅)
    (ports : ∀ x : V, Adj 0 x → ∃ f : Nat × Bool,
      sem_W 10 D x = {sem_bar e,q,f} ∧ supp 10 D (src D f) = {x})
    (small : ∀ u : V, u ≠ 0 → ¬ Adj 0 u → (sem_W 10 D u).card ≤ 2)
    (bound : (supp 10 D (src D (sem_bar q))).card ≤ 2) :
    supp 10 D (src D q) = ({1,4,5} : Finset V) := by
  apply Finset.Subset.antisymm
  · intro u hu
    apply (I1Exposure.zero_neighbors u).mp
    by_contra hn
    have hu0 : u ≠ 0 := by
      intro eq
      have zero : (0 : V) ∈ supp 10 D (src D q) := eq ▸ hu
      have pure := sem_inelig_pure graph_ok h.1 hc hi zero
      have one := (sem_mem_W.mp (hq 1 (by decide +kernel))).2.1
      rw [pure,Finset.mem_singleton] at one
      exact (by decide : (1 : V) ≠ 0) one
    have three := extra_common_source_forces_three h hc hi epure hq qout ports hu0 hn (small u hu0 hn) hu
    omega
  · intro u hu
    exact (sem_mem_W.mp (hq u ((I1Exposure.zero_neighbors u).mpr hu))).2.1

end PEqualNP.Outside.L_meta_2590_aux.S50ExtraSource


namespace PEqualNP.Outside.L_meta_2590_aux.SharedDom
open DagTools Four S50Meeting S50Private S50ExtraSource I1Exposure

lemma case50_no_singleton_merges_of_common {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (zero : Bzero 10 D = 0) (hi : (0 : V) ∈ ineligSet 10 D)
    (budget : Bplus 10 D = (eligSet 10 D).card + 1)
    (sat : ∀ x : V, Adj 0 x → (sem_W 10 D x).card = 3)
    {P Q : Nat × Bool} (hpq : P.1 ≠ Q.1)
    (common : ∀ x : V, Adj 0 x → P ∈ sem_W 10 D x ∧ Q ∈ sem_W 10 D x) :
    (∀ x : V, merges 10 D (carrierT 10 D {x}) = ∅) ∧
    (∀ x : V, x ≠ 0 → ¬ Adj 0 x → (sem_W 10 D x).card = 2) ∧
    (∀ j : Nat, j < D.length → tag D j = true → supp 10 D (10+j) = ∅) := by
  classical
  obtain ⟨b,hbfirst⟩ := sem_exists_firstBranch graph_ok h.1 hc
  have hb := sem_firstBranch_pure hbfirst
  have rcard : (residualUnits 10 D b).card = 1 := by
    have count := card_residual h.1 b hb
    omega
  obtain ⟨r,hR⟩ := Finset.card_eq_one.mp rcard
  have three (x : V) (hx : Adj 0 x) : 3 ≤ (sem_W 10 D x).card := (sat x hx).ge
  have hS := case50_residual_support h hc b hb zero hi hR three
  obtain ⟨e,q,_,_,epure,_,_,_,hq,portsFull⟩ :=
    case50_budget_ports_of_common h hc zero hi budget sat hpq common
  have ports (x : V) (hx : Adj 0 x) : ∃ f : Nat × Bool,
      sem_W 10 D x = {sem_bar e,q,f} ∧ supp 10 D (src D f) = {x} := by
    obtain ⟨f,cover,_,_,pure⟩ := portsFull x hx
    exact ⟨f,cover,pure⟩
  have emptyout := common_gate_output_empty h hc b hb hi hR hS epure hq ports
  have small (u : V) (huN : ¬ Adj 0 u) : (sem_W 10 D u).card ≤ 2 := by
    have count := sem_code_count graph_ok h hc b hb u
    have one : (({u} : Finset V) ∩ eligSet 10 D).card ≤ 1 :=
      (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
    have filt : ((residualUnits 10 D b).filter (fun a => u ∈ supp 10 D a.1)) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro a ha
      obtain ⟨ha,hua⟩ := Finset.mem_filter.mp ha
      have eq : a = r := by simpa only [hR,Finset.mem_singleton] using ha
      rw [eq,hS] at hua
      exact huN ((zero_neighbors u).mpr hua)
    rw [filt,Finset.card_empty] at count
    omega
  have large : (∃ u : V, u ≠ 0 ∧ ¬ Adj 0 u ∧ u ∈ supp 10 D (src D q)) →
      2 ≤ (supp 10 D (src D (sem_bar q))).card := by
    rintro ⟨u,hu0,huN,huq⟩
    have bound := extra_common_source_forces_three h hc hi epure hq emptyout ports hu0 huN
      (small u huN) huq
    omega
  have outside (u : V) (hu0 : u ≠ 0) (huN : ¬ Adj 0 u) : 2 ≤ (sem_W 10 D u).card :=
    outside_two_exits_of_large_opposite h hc hi epure hq ports emptyout large hu0 huN
  obtain ⟨none,two⟩ := case50_no_singleton_merges_of_outside_two h hc b hb hi hR hS three outside
  exact ⟨none,two,fun j hj ht => and_output_empty_of_no_singleton_merges h.1 none hj ht⟩

lemma case50_no_singleton_merges_of_saturated_common {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (zero : Bzero 10 D = 0) (hi : (0 : V) ∈ ineligSet 10 D)
    (budget : Bplus 10 D = (eligSet 10 D).card + 1)
    (sat : ∀ x : V, Adj 0 x → 3 ≤ (sem_W 10 D x).card)
    {P Q : Nat × Bool} (hpq : P.1 ≠ Q.1)
    (common : ∀ x : V, Adj 0 x → P ∈ sem_W 10 D x ∧ Q ∈ sem_W 10 D x) :
    (∀ x : V, merges 10 D (carrierT 10 D {x}) = ∅) ∧
    (∀ x : V, x ≠ 0 → ¬ Adj 0 x → (sem_W 10 D x).card = 2) ∧
    (∀ j : Nat, j < D.length → tag D j = true → supp 10 D (10+j) = ∅) := by
  classical
  obtain ⟨b,hbfirst⟩ := sem_exists_firstBranch graph_ok h.1 hc
  have hb := sem_firstBranch_pure hbfirst
  have rcard : (residualUnits 10 D b).card = 1 := by
    have count := card_residual h.1 b hb
    omega
  have exactSat (x : V) (hx : Adj 0 x) : (sem_W 10 D x).card = 3 := by
    have count := sem_code_count graph_ok h hc b hb x
    have one : (({x} : Finset V) ∩ eligSet 10 D).card ≤ 1 :=
      (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
    have residual := Finset.card_le_card
      (Finset.filter_subset (fun a => x ∈ supp 10 D a.1) (residualUnits 10 D b))
    have three := sat x hx
    omega
  exact case50_no_singleton_merges_of_common h hc zero hi budget exactSat hpq common

end PEqualNP.Outside.L_meta_2590_aux.SharedDom


namespace PEqualNP.Outside.L_meta_2590_aux.S50SplitPrivate
open DagTools Four S50Meeting S50Private

lemma private_mate_outside_iff {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    {e q : Nat × Bool} (f : V → Nat × Bool)
    (epure : supp 10 D (src D e) = {0})
    (qsrc : supp 10 D (src D q) = ({1,4,5} : Finset V))
    (qout : supp 10 D (10+q.1) = ∅)
    (cover : ∀ x : V, Adj 0 x → sem_W 10 D x = {sem_bar e,q,f x})
    (pure : ∀ x : V, Adj 0 x → supp 10 D (src D (f x)) = {x})
    (small : ∀ y : V, y ≠ 0 → ¬ Adj 0 y → (sem_W 10 D y).card ≤ 2)
    {x y : V} (hx : Adj 0 x) (hy0 : y ≠ 0) (hyN : ¬ Adj 0 y) :
    y ∈ supp 10 D (src D (sem_bar (f x))) ↔
      Adj x y ∧ y ∉ supp 10 D (src D (sem_bar q)) := by
  classical
  have fxmem (a : V) (ha : Adj 0 a) : f a ∈ sem_W 10 D a := by
    rw [cover a ha]
    simp
  have lower (a : V) (ha : Adj 0 a) (hay : Adj a y)
      (hyq : y ∉ supp 10 D (src D (sem_bar q))) : sem_bar (f a) ∈ sem_W 10 D y := by
    rcases case50_edge_coverage h hc hay hy0 (cover a ha) epure with he | he
    · exact False.elim (hyq (sem_mem_W.mp he.1).2.1)
    · exact he.1
  constructor
  · intro hyf
    have hyx : y ≠ x := fun eq => hyN (eq ▸ hx)
    have hfy := pure_mate_exit h.1 (fxmem x hx) (pure x hx) hyx hyf
    obtain ⟨a,z,ha,hay,hyz,hz0,hzN⟩ := outside_neighbors y hy0 hyN
    have hyq : y ∉ supp 10 D (src D (sem_bar q)) := by
      intro hyt
      have hqx : q ∈ sem_W 10 D x := by rw [cover x hx]; simp
      have hqy : sem_bar q ∈ sem_W 10 D y := by
        apply sem_mem_W.mpr
        refine ⟨(sem_mem_W.mp hqx).1,hyt,?_⟩
        change y ∉ supp 10 D (10+q.1)
        rw [qout]
        simp
      have hne : sem_bar (f x) ≠ sem_bar q := by
        intro eq
        have eq' : f x = q := by simpa only [bar_bar] using congrArg sem_bar eq
        have hs : ({x} : Finset V) = {1,4,5} := by rw [← pure x hx,eq',qsrc]
        have hcard := congrArg Finset.card hs
        have hthree : ({1,4,5} : Finset V).card = 3 := by decide
        rw [Finset.card_singleton,hthree] at hcard
        omega
      have hz := two_exit_neighbor_coverage graph_ok h.1 hc hyz (small y hy0 hyN) hfy hqy hne
      simp only [bar_bar,pure x hx,qsrc,Finset.mem_singleton] at hz
      rcases hz with hz | hz
      · exact hzN (hz ▸ hx)
      · exact hzN ((I1Exposure.zero_neighbors z).mpr hz)
    refine ⟨?_,hyq⟩
    by_contra hxy
    have haymem := lower a ha hay hyq
    have hax : a ≠ x := fun eq => hxy (eq ▸ hay)
    have hne : sem_bar (f x) ≠ sem_bar (f a) := by
      intro eq
      have eq' : f x = f a := by simpa only [bar_bar] using congrArg sem_bar eq
      have hs : ({x} : Finset V) = {a} := by rw [← pure x hx,eq',pure a ha]
      exact hax (Finset.singleton_inj.mp hs).symm
    have hz := two_exit_neighbor_coverage graph_ok h.1 hc hyz (small y hy0 hyN) hfy haymem hne
    simp only [bar_bar,pure x hx,pure a ha,Finset.mem_singleton] at hz
    rcases hz with hz | hz
    · exact hzN (hz ▸ hx)
    · exact hzN (hz ▸ ha)
  · rintro ⟨hxy,hyq⟩
    exact (sem_mem_W.mp (lower x hx hxy hyq)).2.1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 1000000 in
lemma two_owner_neighbors : ∀ x y : V, Adj 0 x → Adj 0 y → x ≠ y →
    ∃ a b c : V, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      (a ≠ 0 ∧ ¬ Adj 0 a ∧ (Adj x a ∨ Adj y a)) ∧
      (b ≠ 0 ∧ ¬ Adj 0 b ∧ (Adj x b ∨ Adj y b)) ∧
      (c ≠ 0 ∧ ¬ Adj 0 c ∧ (Adj x c ∨ Adj y c)) := by
  unfold Adj
  decide +kernel

lemma private_mates_exact_of_small_opposite {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    {e q : Nat × Bool} (f : V → Nat × Bool)
    (epure : supp 10 D (src D e) = {0})
    (zero : sem_W 10 D 0 = {e})
    (qsrc : supp 10 D (src D q) = ({1,4,5} : Finset V))
    (qout : supp 10 D (10+q.1) = ∅)
    (cover : ∀ x : V, Adj 0 x → sem_W 10 D x = {sem_bar e,q,f x})
    (pure : ∀ x : V, Adj 0 x → supp 10 D (src D (f x)) = {x})
    (ne : ∀ x : V, Adj 0 x → f x ≠ sem_bar e)
    (small : ∀ y : V, y ≠ 0 → ¬ Adj 0 y → (sem_W 10 D y).card ≤ 2)
    (tcard : (supp 10 D (src D (sem_bar q))).card ≤ 2) :
    ∀ x : V, Adj 0 x → ∀ y : V,
      y ∈ supp 10 D (src D (sem_bar (f x))) ↔
        y ≠ 0 ∧ ¬ Adj 0 y ∧ Adj x y ∧ y ∉ supp 10 D (src D (sem_bar q)) := by
  classical
  have outside {a b : V} (ha : Adj 0 a) (hb0 : b ≠ 0) (hbN : ¬ Adj 0 b) :=
    private_mate_outside_iff h hc f epure qsrc qout cover pure small ha hb0 hbN
  have fxmem (x : V) (hx : Adj 0 x) : f x ∈ sem_W 10 D x := by rw [cover x hx]; simp
  intro x hx
  have hx0 : x ≠ 0 := fun eq => graph_ok.2.1 0 (eq ▸ hx)
  intro y
  constructor
  · intro hy
    have hyx : y ≠ x := fun eq => exit_opposite_excludes h.1 (fxmem x hx) (eq ▸ hy)
    have hymem := pure_mate_exit h.1 (fxmem x hx) (pure x hx) hyx hy
    have hy0 : y ≠ 0 := by
      intro eq
      subst y
      rw [zero,Finset.mem_singleton] at hymem
      have hf : f x = sem_bar e := by simpa only [bar_bar] using congrArg sem_bar hymem
      exact ne x hx hf
    have hyN : ¬ Adj 0 y := by
      intro hyN
      have hm := hymem
      rw [cover y hyN] at hm
      simp only [Finset.mem_insert,Finset.mem_singleton] at hm
      rcases hm with hme | hmq | hmf
      · have hf : f x = e := by simpa only [bar_bar] using congrArg sem_bar hme
        have hs : ({x} : Finset V) = {0} := by rw [← pure x hx,hf,epure]
        exact hx0 (Finset.singleton_inj.mp hs)
      · have hqx : q ∈ sem_W 10 D x := by rw [cover x hx]; simp
        have hf : f x = sem_bar q := by simpa only [bar_bar] using congrArg sem_bar hmq
        have hxs : x ∈ supp 10 D (src D (sem_bar q)) := by rw [← hf,pure x hx]; simp
        exact exit_opposite_excludes h.1 hqx hxs
      · have sx : supp 10 D (src D (sem_bar (f x))) = {y} := by rw [hmf,pure y hyN]
        have sy : supp 10 D (src D (sem_bar (f y))) = {x} := by
          have hf : sem_bar (f y) = f x := by simpa only [bar_bar] using (congrArg sem_bar hmf).symm
          rw [hf,pure x hx]
        have lower (a : V) (ha0 : a ≠ 0) (haN : ¬ Adj 0 a) (hadj : Adj x a ∨ Adj y a) :
            a ∈ supp 10 D (src D (sem_bar q)) := by
          by_contra hat
          rcases hadj with hxa | hya
          · have hh := (outside hx ha0 haN).mpr ⟨hxa,hat⟩
            rw [sx,Finset.mem_singleton] at hh
            exact haN (hh ▸ hyN)
          · have hh := (outside hyN ha0 haN).mpr ⟨hya,hat⟩
            rw [sy,Finset.mem_singleton] at hh
            exact haN (hh ▸ hx)
        obtain ⟨a,b,c,hab,hac,hbc,ha,hb,he⟩ := two_owner_neighbors x y hx hyN (Ne.symm hyx)
        have sub : ({a,b,c} : Finset V) ⊆ supp 10 D (src D (sem_bar q)) := by
          intro v hv
          simp only [Finset.mem_insert,Finset.mem_singleton] at hv
          rcases hv with rfl | rfl | rfl
          · exact lower _ ha.1 ha.2.1 ha.2.2
          · exact lower _ hb.1 hb.2.1 hb.2.2
          · exact lower _ he.1 he.2.1 he.2.2
        have count := Finset.card_le_card sub
        have three : ({a,b,c} : Finset V).card = 3 := by simp [hab,hac,hbc]
        omega
    exact ⟨hy0,hyN,(outside hx hy0 hyN).mp hy⟩
  · rintro ⟨hy0,hyN,hxy,hyq⟩
    exact (outside hx hy0 hyN).mpr ⟨hxy,hyq⟩

end PEqualNP.Outside.L_meta_2590_aux.S50SplitPrivate


namespace PEqualNP.Outside.L_meta_2590_aux.S50SplitCycle
open DagTools Four S50Private

lemma unique_away {α : Type*} [DecidableEq α] (S : Finset α) (hs : S.card ≤ 2)
    {p a b : α} (hp : p ∈ S) (ha : a ∈ S) (hb : b ∈ S)
    (hap : a ≠ p) (hbp : b ≠ p) : a = b := by
  rcases mem_of_card_le_two S hs hp ha hb (Ne.symm hap) with he | he
  · exact False.elim (hbp he)
  · exact he.symm

lemma arc_ne_of_opposite_subset {n : Nat} {D : Dag} {a p : Nat × Bool}
    {z : Fin n} {S : Finset (Fin n)} (hz : sem_bar a ∈ sem_W n D z)
    (hp : supp n D (src D (sem_bar p)) ⊆ S) (hzS : z ∉ S) : a ≠ p := by
  intro eq
  have hm := (sem_mem_W.mp hz).2.1
  rw [eq] at hm
  exact hzS (hp hm)

lemma cycle_propagate_subset {n : Nat} {D : Dag} {G : Fin n → Fin n → Prop}
    (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {x y z : Fin n} {S : Finset (Fin n)} (hxy : G x y) (hyS : y ∉ S) (hzS : z ∉ S)
    (small : (sem_W n D x).card ≤ 2) {p a : Nat × Bool}
    (hp : p ∈ sem_W n D x) (hsub : supp n D (src D (sem_bar p)) ⊆ S)
    (ha : a ∈ sem_W n D x) (hz : sem_bar a ∈ sem_W n D z) :
    sem_bar a ∈ sem_W n D y := by
  obtain ⟨b,hb,hy,_⟩ := sem_edge_slots hG hS hC hxy
  have hap := arc_ne_of_opposite_subset hz hsub hzS
  have hbp := arc_ne_of_opposite_subset hy hsub hyS
  have eq := unique_away (sem_W n D x) small hp ha hb hap hbp
  exact eq ▸ hy

lemma two_exit_eq {α : Type*} [DecidableEq α] (S : Finset α) (hs : S.card ≤ 2)
    {p a : α} (hp : p ∈ S) (ha : a ∈ S) (hpa : p ≠ a) : S = {p,a} := by
  ext b
  simp only [Finset.mem_insert,Finset.mem_singleton]
  constructor
  · intro hb
    exact mem_of_card_le_two S hs hp ha hb hpa
  · rintro (rfl | rfl) <;> assumption

set_option maxHeartbeats 0 in
lemma six_cycle_common {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (p : V → Nat × Bool)
    (first : ∀ y : V, y ≠ 0 → ¬ Adj 0 y → p y ∈ sem_W 10 D y)
    (sub : ∀ y : V, y ≠ 0 → ¬ Adj 0 y →
      supp 10 D (src D (sem_bar (p y))) ⊆ ({1,4,5} : Finset V))
    (small : ∀ y : V, y ≠ 0 → ¬ Adj 0 y → (sem_W 10 D y).card ≤ 2) :
    ∃ a : Nat × Bool,
      a ∈ sem_W 10 D 3 ∧ a ∈ sem_W 10 D 6 ∧ a ∈ sem_W 10 D 7 ∧
      sem_bar a ∈ sem_W 10 D 2 ∧ sem_bar a ∈ sem_W 10 D 8 ∧
      sem_bar a ∈ sem_W 10 D 9 := by
  have small₃ := small 3 (by decide) (by unfold Adj edgeList; decide)
  have small₆ := small 6 (by decide) (by unfold Adj edgeList; decide)
  have small₈ := small 8 (by decide) (by unfold Adj edgeList; decide)
  have small₉ := small 9 (by decide) (by unfold Adj edgeList; decide)
  have p₃ := first 3 (by decide) (by unfold Adj edgeList; decide)
  have p₆ := first 6 (by decide) (by unfold Adj edgeList; decide)
  have p₈ := first 8 (by decide) (by unfold Adj edgeList; decide)
  have p₉ := first 9 (by decide) (by unfold Adj edgeList; decide)
  have s₃ := sub 3 (by decide) (by unfold Adj edgeList; decide)
  have s₆ := sub 6 (by decide) (by unfold Adj edgeList; decide)
  have s₈ := sub 8 (by decide) (by unfold Adj edgeList; decide)
  have s₉ := sub 9 (by decide) (by unfold Adj edgeList; decide)
  obtain ⟨b,h₂,h₃,_⟩ := sem_edge_slots graph_ok h.1 hc (show Adj 2 3 by unfold Adj edgeList; decide)
  have h₈ : b ∈ sem_W 10 D 8 := by
    have hh := cycle_propagate_subset graph_ok h.1 hc (show Adj 3 8 by unfold Adj edgeList; decide)
      (by decide : (8 : V) ∉ ({1,4,5} : Finset V)) (by decide : (2 : V) ∉ ({1,4,5} : Finset V))
      small₃ p₃ s₃ h₃ (by simpa only [bar_bar] using h₂)
    simpa only [bar_bar] using hh
  have h₆ := cycle_propagate_subset graph_ok h.1 hc (show Adj 8 6 by unfold Adj edgeList; decide)
    (by decide : (6 : V) ∉ ({1,4,5} : Finset V)) (by decide : (3 : V) ∉ ({1,4,5} : Finset V))
    small₈ p₈ s₈ h₈ h₃
  have h₉ : b ∈ sem_W 10 D 9 := by
    have hh := cycle_propagate_subset graph_ok h.1 hc (show Adj 6 9 by unfold Adj edgeList; decide)
      (by decide : (9 : V) ∉ ({1,4,5} : Finset V)) (by decide : (8 : V) ∉ ({1,4,5} : Finset V))
      small₆ p₆ s₆ h₆ (by simpa only [bar_bar] using h₈)
    simpa only [bar_bar] using hh
  have h₇ := cycle_propagate_subset graph_ok h.1 hc (show Adj 9 7 by unfold Adj edgeList; decide)
    (by decide : (7 : V) ∉ ({1,4,5} : Finset V)) (by decide : (6 : V) ∉ ({1,4,5} : Finset V))
    small₉ p₉ s₉ h₉ h₆
  refine ⟨sem_bar b,h₃,h₆,h₇,?_,?_,?_⟩ <;> simpa only [bar_bar]

set_option maxHeartbeats 0 in
lemma cycle_ports {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (p : V → Nat × Bool)
    (first : ∀ y : V, y ≠ 0 → ¬ Adj 0 y → p y ∈ sem_W 10 D y)
    (sub : ∀ y : V, y ≠ 0 → ¬ Adj 0 y →
      supp 10 D (src D (sem_bar (p y))) ⊆ ({1,4,5} : Finset V))
    (small : ∀ y : V, y ≠ 0 → ¬ Adj 0 y → (sem_W 10 D y).card ≤ 2) :
    ∃ a : Nat × Bool,
      sem_W 10 D 2 = {p 2,sem_bar a} ∧ sem_W 10 D 3 = {p 3,a} ∧
      sem_W 10 D 6 = {p 6,a} ∧ sem_W 10 D 7 = {p 7,a} ∧
      sem_W 10 D 8 = {p 8,sem_bar a} ∧ sem_W 10 D 9 = {p 9,sem_bar a} := by
  obtain ⟨a,h₃,h₆,h₇,h₂,h₈,h₉⟩ := six_cycle_common h hc p first sub small
  have b₂ : sem_bar (sem_bar a) ∈ sem_W 10 D 3 := by simpa only [bar_bar] using h₃
  refine ⟨a,?_,?_,?_,?_,?_,?_⟩
  · exact two_exit_eq _ (small 2 (by decide) (by unfold Adj edgeList; decide))
      (first 2 (by decide) (by unfold Adj edgeList; decide)) h₂
      (Ne.symm (arc_ne_of_opposite_subset b₂
        (sub 2 (by decide) (by unfold Adj edgeList; decide)) (by decide)))
  · exact two_exit_eq _ (small 3 (by decide) (by unfold Adj edgeList; decide))
      (first 3 (by decide) (by unfold Adj edgeList; decide)) h₃
      (Ne.symm (arc_ne_of_opposite_subset h₂
        (sub 3 (by decide) (by unfold Adj edgeList; decide)) (by decide)))
  · exact two_exit_eq _ (small 6 (by decide) (by unfold Adj edgeList; decide))
      (first 6 (by decide) (by unfold Adj edgeList; decide)) h₆
      (Ne.symm (arc_ne_of_opposite_subset h₂
        (sub 6 (by decide) (by unfold Adj edgeList; decide)) (by decide)))
  · exact two_exit_eq _ (small 7 (by decide) (by unfold Adj edgeList; decide))
      (first 7 (by decide) (by unfold Adj edgeList; decide)) h₇
      (Ne.symm (arc_ne_of_opposite_subset h₂
        (sub 7 (by decide) (by unfold Adj edgeList; decide)) (by decide)))
  · exact two_exit_eq _ (small 8 (by decide) (by unfold Adj edgeList; decide))
      (first 8 (by decide) (by unfold Adj edgeList; decide)) h₈
      (Ne.symm (arc_ne_of_opposite_subset b₂
        (sub 8 (by decide) (by unfold Adj edgeList; decide)) (by decide)))
  · exact two_exit_eq _ (small 9 (by decide) (by unfold Adj edgeList; decide))
      (first 9 (by decide) (by unfold Adj edgeList; decide)) h₉
      (Ne.symm (arc_ne_of_opposite_subset b₂
        (sub 9 (by decide) (by unfold Adj edgeList; decide)) (by decide)))

end PEqualNP.Outside.L_meta_2590_aux.S50SplitCycle


namespace PEqualNP.Outside.L_meta_2590_aux.S50SplitDirty
open DagTools Four S50Private S50SplitCycle

lemma arc_ne_bar (a : Nat × Bool) : a ≠ sem_bar a := by
  intro eq
  have hb := congrArg Prod.snd eq
  cases hs : a.2 <;> simp [sem_bar,hs] at hb

set_option maxHeartbeats 0 in
lemma dirty_sources_exact {D : Dag} (p : V → Nat × Bool) (a : Nat × Bool)
    (sub : ∀ y : V, y ≠ 0 → ¬ Adj 0 y →
      supp 10 D (src D (sem_bar (p y))) ⊆ ({1,4,5} : Finset V))
    (central : ∀ x : V, x = 0 ∨ Adj 0 x → ∀ e ∈ sem_W 10 D x,
      supp 10 D (src D e) ⊆ ({0,1,4,5} : Finset V))
    (emptyout : supp 10 D (10+a.1) = ∅)
    (h₂ : sem_W 10 D 2 = {p 2,sem_bar a})
    (h₃ : sem_W 10 D 3 = {p 3,a})
    (h₆ : sem_W 10 D 6 = {p 6,a})
    (h₇ : sem_W 10 D 7 = {p 7,a})
    (h₈ : sem_W 10 D 8 = {p 8,sem_bar a})
    (h₉ : sem_W 10 D 9 = {p 9,sem_bar a}) :
    supp 10 D (src D a) = ({3,6,7} : Finset V) ∧
    supp 10 D (src D (sem_bar a)) = ({2,8,9} : Finset V) := by
  classical
  have ha₃ : a ∈ sem_W 10 D 3 := by rw [h₃]; simp
  have hb₂ : sem_bar a ∈ sem_W 10 D 2 := by rw [h₂]; simp
  have valid := (sem_mem_W.mp ha₃).1
  have haiff (x : V) : x ∈ supp 10 D (src D a) ↔ a ∈ sem_W 10 D x := by
    constructor
    · intro hx
      exact sem_mem_W.mpr ⟨valid,hx,by rw [emptyout]; simp⟩
    · exact fun hx => (sem_mem_W.mp hx).2.1
  have hbiff (x : V) : x ∈ supp 10 D (src D (sem_bar a)) ↔ sem_bar a ∈ sem_W 10 D x := by
    constructor
    · intro hx
      apply sem_mem_W.mpr
      refine ⟨valid,hx,?_⟩
      change x ∉ supp 10 D (10+a.1)
      rw [emptyout]
      simp
    · exact fun hx => (sem_mem_W.mp hx).2.1
  have aneq (x : V) (hx0 : x ≠ 0) (hxN : ¬ Adj 0 x) : a ≠ p x :=
    arc_ne_of_opposite_subset hb₂ (sub x hx0 hxN) (by decide)
  have bneq (x : V) (hx0 : x ≠ 0) (hxN : ¬ Adj 0 x) : sem_bar a ≠ p x :=
    arc_ne_of_opposite_subset (by simpa only [bar_bar] using ha₃)
      (sub x hx0 hxN) (by decide : (3 : V) ∉ ({1,4,5} : Finset V))
  have acentral (x : V) (hx : x = 0 ∨ Adj 0 x) : a ∉ sem_W 10 D x := by
    intro ha
    have bad := central x hx a ha (sem_mem_W.mp ha₃).2.1
    exact (by decide : (3 : V) ∉ ({0,1,4,5} : Finset V)) bad
  have bcentral (x : V) (hx : x = 0 ∨ Adj 0 x) : sem_bar a ∉ sem_W 10 D x := by
    intro hb
    have bad := central x hx (sem_bar a) hb (sem_mem_W.mp hb₂).2.1
    exact (by decide : (2 : V) ∉ ({0,1,4,5} : Finset V)) bad
  have aneqb := arc_ne_bar a
  constructor
  · ext x
    rw [haiff]
    fin_cases x
    · simp [acentral 0 (Or.inl rfl)]
    · simp [acentral 1 (Or.inr (by unfold Adj edgeList; decide))]
    · simp [h₂,aneq 2 (by decide) (by unfold Adj edgeList; decide),aneqb]
    · simp [h₃]
    · simp [acentral 4 (Or.inr (by unfold Adj edgeList; decide))]
    · simp [acentral 5 (Or.inr (by unfold Adj edgeList; decide))]
    · simp [h₆]
    · simp [h₇]
    · simp [h₈,aneq 8 (by decide) (by unfold Adj edgeList; decide),aneqb]
    · simp [h₉,aneq 9 (by decide) (by unfold Adj edgeList; decide),aneqb]
  · ext x
    rw [hbiff]
    fin_cases x
    · simp [bcentral 0 (Or.inl rfl)]
    · simp [bcentral 1 (Or.inr (by unfold Adj edgeList; decide))]
    · simp [h₂]
    · simp [h₃,bneq 3 (by decide) (by unfold Adj edgeList; decide),Ne.symm aneqb]
    · simp [bcentral 4 (Or.inr (by unfold Adj edgeList; decide))]
    · simp [bcentral 5 (Or.inr (by unfold Adj edgeList; decide))]
    · simp [h₆,bneq 6 (by decide) (by unfold Adj edgeList; decide),Ne.symm aneqb]
    · simp [h₇,bneq 7 (by decide) (by unfold Adj edgeList; decide),Ne.symm aneqb]
    · simp [h₈]
    · simp [h₉]

end PEqualNP.Outside.L_meta_2590_aux.S50SplitDirty


namespace PEqualNP.Outside.L_meta_2590_aux.S50SplitT
open DagTools Four

def cycleSet : Finset V := {2,3,6,7,8,9}

def owner (x : V) : V := if x = 2 ∨ x = 6 then 1 else if x = 3 ∨ x = 9 then 4 else 5

def ownerPair (x : V) : Finset V := Finset.univ.filter (fun y => Adj (owner x) y ∧ y ≠ 0)

def firstSupport (T : Finset V) (x : V) : Finset V := if x ∈ T then T else ownerPair x \ T

def dirtySide (x : V) : Finset V := if x ∈ ({3,6,7} : Finset V) then {3,6,7} else {2,8,9}

def allowed : Finset (Finset V) := {∅,{2},{3},{6},{2,6},{7},{8},{7,8},{9},{3,9}}

def index (T : Finset V) : Nat :=
  (if 2 ∈ T then 1 else 0) + (if 3 ∈ T then 2 else 0) + (if 6 ∈ T then 4 else 0) +
  (if 7 ∈ T then 8 else 0) + (if 8 ∈ T then 16 else 0) + (if 9 ∈ T then 32 else 0)

def witnessCode (T : Finset V) : Nat :=
  ([0, 0, 0, 2568, 0, 0, 3140, 2568, 0, 2432, 3216, 2432, 6274, 2432, 3140, 2432, 0, 2306, 3456, 2306, 6528, 2306, 3140, 2306, 0, 2306, 3216, 2306, 6274, 2306, 3140, 2306, 0, 2562, 0, 2562, 6664, 2562, 3140, 2562, 7688, 2432, 3216, 2432, 6274, 2432, 3140, 2432, 8712, 2306, 3456, 2306, 6528, 2306, 3140, 2306, 7688, 2306, 3216, 2306, 6274, 2306, 3140, 2306] : List Nat).getD (index T) 0

def witnessVertex (T : Finset V) : V := ⟨witnessCode T / 1024 % 10,Nat.mod_lt _ (by decide)⟩

def witnessSet (T : Finset V) : Finset V :=
  Finset.univ.filter (fun x => (witnessCode T % 1024).testBit x.val = true)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 1000000 in
lemma exposure_witness : ∀ T ∈ cycleSet.powerset, T ∈ allowed ∨
    let x := witnessVertex T
    let Z := witnessSet T
    x ∈ cycleSet ∧ (∀ u ∈ Z, ∀ v ∈ Z, ¬ Adj u v) ∧
      (∃ v ∈ Z, Adj x v) ∧ (firstSupport T x ∩ Z).Nonempty ∧ (dirtySide x ∩ Z).Nonempty := by
  unfold Adj edgeList
  decide +kernel

lemma allowed_card : ∀ T ∈ allowed, T.card ≤ 2 := by
  decide +kernel

lemma allowed_of_exposure (T : Finset V) (hT : T ⊆ cycleSet)
    (exposure : ∀ x ∈ cycleSet, ∀ Z : Finset V,
      (∀ u ∈ Z, ∀ v ∈ Z, ¬ Adj u v) → (∃ v ∈ Z, Adj x v) →
      Disjoint (firstSupport T x) Z ∨ Disjoint (dirtySide x) Z) : T ∈ allowed := by
  rcases exposure_witness T (Finset.mem_powerset.mpr hT) with good | bad
  · exact good
  · obtain ⟨hx,hind,hhit,hfirst,hdirty⟩ := bad
    have hdis := exposure (witnessVertex T) hx (witnessSet T) hind hhit
    rcases hdis with hdis | hdis
    · obtain ⟨v,hv⟩ := hfirst
      exact False.elim (Finset.disjoint_left.mp hdis (Finset.mem_inter.mp hv).1 (Finset.mem_inter.mp hv).2)
    · obtain ⟨v,hv⟩ := hdirty
      exact False.elim (Finset.disjoint_left.mp hdis (Finset.mem_inter.mp hv).1 (Finset.mem_inter.mp hv).2)

lemma card_le_two_of_exposure (T : Finset V) (hT : T ⊆ cycleSet)
    (exposure : ∀ x ∈ cycleSet, ∀ Z : Finset V,
      (∀ u ∈ Z, ∀ v ∈ Z, ¬ Adj u v) → (∃ v ∈ Z, Adj x v) →
      Disjoint (firstSupport T x) Z ∨ Disjoint (dirtySide x) Z) : T.card ≤ 2 :=
  allowed_card T (allowed_of_exposure T hT exposure)

lemma allowed_of_exit_cover {D : Dag} (h : Strict 10 D) (hc : sem_Comp 10 Adj D)
    (T : Finset V) (hT : T ⊆ cycleSet) (p d : V → Nat × Bool)
    (cover : ∀ x ∈ cycleSet, sem_W 10 D x ⊆ {p x,d x})
    (first : ∀ x ∈ cycleSet, firstSupport T x ⊆ supp 10 D (src D (p x)))
    (dirty : ∀ x ∈ cycleSet, dirtySide x ⊆ supp 10 D (src D (d x))) :
    T ∈ allowed := by
  apply allowed_of_exposure T hT
  intro x hx Z hind hhit
  obtain ⟨j,s,hj,_,hxs,hxo,free⟩ := sem_exposure graph_ok h hc Z hind x hhit
  have hw : (j,s) ∈ sem_W 10 D x := sem_mem_W.mpr ⟨hj,hxs,hxo⟩
  have hm := cover x hx hw
  simp only [Finset.mem_insert,Finset.mem_singleton] at hm
  rcases hm with hm | hm
  · left
    rw [hm] at free
    apply Finset.disjoint_left.mpr
    intro y hy hyZ
    exact Finset.disjoint_left.mp free (first x hx hy) hyZ
  · right
    rw [hm] at free
    apply Finset.disjoint_left.mpr
    intro y hy hyZ
    exact Finset.disjoint_left.mp free (dirty x hx hy) hyZ

lemma card_le_two_of_exit_cover {D : Dag} (h : Strict 10 D) (hc : sem_Comp 10 Adj D)
    (T : Finset V) (hT : T ⊆ cycleSet) (p d : V → Nat × Bool)
    (cover : ∀ x ∈ cycleSet, sem_W 10 D x ⊆ {p x,d x})
    (first : ∀ x ∈ cycleSet, firstSupport T x ⊆ supp 10 D (src D (p x)))
    (dirty : ∀ x ∈ cycleSet, dirtySide x ⊆ supp 10 D (src D (d x))) :
    T.card ≤ 2 :=
  allowed_card T (allowed_of_exit_cover h hc T hT p d cover first dirty)

end PEqualNP.Outside.L_meta_2590_aux.S50SplitT


namespace PEqualNP.Outside.L_meta_2590_aux.S50SplitPorts
open DagTools Four S50Meeting S50Private S50SplitT

def port (T : Finset V) (q : Nat × Bool) (f : V → Nat × Bool) (x : V) : Nat × Bool :=
  if x ∈ T then sem_bar q else sem_bar (f (owner x))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 1000000 in
lemma owner_geometry : ∀ x ∈ cycleSet,
    x ≠ 0 ∧ ¬ Adj 0 x ∧ Adj 0 (owner x) ∧ Adj (owner x) x := by
  unfold Adj edgeList
  decide +kernel

lemma cycle_mem_iff : ∀ x : V, x ∈ cycleSet ↔ x ≠ 0 ∧ ¬ Adj 0 x := by
  unfold Adj edgeList
  decide +kernel

lemma actual_ports {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    {e q : Nat × Bool} (f : V → Nat × Bool) (T : Finset V)
    (epure : supp 10 D (src D e) = {0})
    (qsrc : supp 10 D (src D q) = ({1,4,5} : Finset V))
    (qout : supp 10 D (10+q.1) = ∅)
    (hT : T = supp 10 D (src D (sem_bar q)))
    (cover : ∀ x : V, Adj 0 x → sem_W 10 D x = {sem_bar e,q,f x})
    (pure : ∀ x : V, Adj 0 x → supp 10 D (src D (f x)) = {x}) :
    (∀ x ∈ cycleSet, port T q f x ∈ sem_W 10 D x) ∧
    (∀ x ∈ cycleSet, supp 10 D (src D (sem_bar (port T q f x))) ⊆ ({1,4,5} : Finset V)) ∧
    (∀ x ∈ cycleSet, firstSupport T x ⊆ supp 10 D (src D (port T q f x))) := by
  classical
  have private_lower (x : V) (hx : x ∈ cycleSet) (y : V)
      (hy : y ∈ ownerPair x) (hyn : y ∉ T) : sem_bar (f (owner x)) ∈ sem_W 10 D y := by
    obtain ⟨_,hxy,hy0⟩ := Finset.mem_filter.mp hy
    have ho := (owner_geometry x hx).2.2.1
    rcases case50_edge_coverage h hc hxy hy0 (cover (owner x) ho) epure with he | he
    · apply False.elim
      apply hyn
      rw [hT]
      exact (sem_mem_W.mp he.1).2.1
    · exact he.1
  refine ⟨?_,?_,?_⟩
  · intro x hx
    by_cases hxt : x ∈ T
    · simp only [port,ite_eq_left hxt]
      have hq1 : q ∈ sem_W 10 D (1 : V) := by
        rw [cover 1 (by decide +kernel)]
        simp
      apply sem_mem_W.mpr
      refine ⟨(sem_mem_W.mp hq1).1,?_,?_⟩
      · rw [← hT]
        exact hxt
      · change x ∉ supp 10 D (10+q.1)
        rw [qout]
        simp
    · simp only [port,ite_eq_right hxt]
      apply private_lower x hx x _ hxt
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ x,(owner_geometry x hx).2.2.2,(owner_geometry x hx).1⟩
  · intro x hx
    by_cases hxt : x ∈ T
    · simp only [port,ite_eq_left hxt,bar_bar,qsrc]
      exact Finset.Subset.refl _
    · simp only [port,ite_eq_right hxt,bar_bar,pure (owner x) (owner_geometry x hx).2.2.1]
      intro y hy
      rw [Finset.mem_singleton] at hy
      subst y
      exact (I1Exposure.zero_neighbors (owner x)).mp (owner_geometry x hx).2.2.1
  · intro x hx
    by_cases hxt : x ∈ T
    · simp only [firstSupport,port,ite_eq_left hxt]
      exact hT.subset
    · simp only [firstSupport,port,ite_eq_right hxt]
      intro y hy
      obtain ⟨hy,hyn⟩ := Finset.mem_sdiff.mp hy
      exact (sem_mem_W.mp (private_lower x hx y hy hyn)).2.1

end PEqualNP.Outside.L_meta_2590_aux.S50SplitPorts


namespace PEqualNP.Outside.L_meta_2590_aux.S50SplitActual
open DagTools Four S50Private S50SplitT S50SplitPorts

lemma split_profile {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    {e q : Nat × Bool} (f : V → Nat × Bool)
    (epure : supp 10 D (src D e) = {0})
    (ebar : supp 10 D (src D (sem_bar e)) = ({1,4,5} : Finset V))
    (zero : sem_W 10 D 0 = {e}) (eqne : e.1 ≠ q.1)
    (qsrc : supp 10 D (src D q) = ({1,4,5} : Finset V))
    (qout : supp 10 D (10+q.1) = ∅)
    (cover : ∀ x : V, Adj 0 x → sem_W 10 D x = {sem_bar e,q,f x})
    (pure : ∀ x : V, Adj 0 x → supp 10 D (src D (f x)) = {x})
    (ne : ∀ x : V, Adj 0 x → f x ≠ sem_bar e)
    (small : ∀ y : V, y ≠ 0 → ¬ Adj 0 y → (sem_W 10 D y).card ≤ 2)
    (empty : ∀ j : Nat, j < D.length → tag D j = true → supp 10 D (10+j) = ∅) :
    let T := supp 10 D (src D (sem_bar q))
    T ∈ allowed ∧ ∃ a : Nat × Bool,
      supp 10 D (src D a) = ({3,6,7} : Finset V) ∧
      supp 10 D (src D (sem_bar a)) = ({2,8,9} : Finset V) ∧
      (∀ x ∈ cycleSet, sem_W 10 D x =
        {port T q f x,if x ∈ ({3,6,7} : Finset V) then a else sem_bar a}) ∧
      ∀ x : V, Adj 0 x → ∀ y : V,
        y ∈ supp 10 D (src D (sem_bar (f x))) ↔
          y ≠ 0 ∧ ¬ Adj 0 y ∧ Adj x y ∧ y ∉ T := by
  classical
  let T := supp 10 D (src D (sem_bar q))
  change T ∈ allowed ∧ _
  have qmem (x : V) (hx : Adj 0 x) : q ∈ sem_W 10 D x := by rw [cover x hx]; simp
  have hT : T ⊆ cycleSet := by
    intro y hy
    apply (cycle_mem_iff y).mpr
    have hqy : sem_bar q ∈ sem_W 10 D y := by
      apply sem_mem_W.mpr
      refine ⟨(sem_mem_W.mp (qmem 1 (by decide +kernel))).1,hy,?_⟩
      change y ∉ supp 10 D (10+q.1)
      rw [qout]
      simp
    constructor
    · intro hy0
      subst y
      rw [zero,Finset.mem_singleton] at hqy
      exact eqne (congrArg Prod.fst hqy).symm
    · intro hyN
      exact exit_opposite_excludes h.1 (qmem y hyN) hy
  obtain ⟨first,opposite,firstLower⟩ := actual_ports h hc f T epure qsrc qout rfl cover pure
  let p := port T q f
  have first' (x : V) (hx0 : x ≠ 0) (hxN : ¬ Adj 0 x) : p x ∈ sem_W 10 D x :=
    first x ((cycle_mem_iff x).mpr ⟨hx0,hxN⟩)
  have opposite' (x : V) (hx0 : x ≠ 0) (hxN : ¬ Adj 0 x) :
      supp 10 D (src D (sem_bar (p x))) ⊆ ({1,4,5} : Finset V) :=
    opposite x ((cycle_mem_iff x).mpr ⟨hx0,hxN⟩)
  obtain ⟨a,h₂,h₃,h₆,h₇,h₈,h₉⟩ := S50SplitCycle.cycle_ports h hc p first' opposite' small
  have central : ∀ x : V, x = 0 ∨ Adj 0 x → ∀ v ∈ sem_W 10 D x,
      supp 10 D (src D v) ⊆ ({0,1,4,5} : Finset V) := by
    intro x hx v hv
    rcases hx with rfl | hx
    · rw [zero,Finset.mem_singleton] at hv
      rw [hv,epure]
      simp
    · rw [cover x hx] at hv
      simp only [Finset.mem_insert,Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl
      · rw [ebar]
        decide
      · rw [qsrc]
        decide
      · rw [pure x hx]
        have hn := (I1Exposure.zero_neighbors x).mp hx
        intro y hy
        have hyx := Finset.mem_singleton.mp hy
        subst y
        exact Finset.mem_insert_of_mem hn
  have ha : a ∈ sem_W 10 D 3 := by rw [h₃]; simp
  have aout := empty a.1 (sem_mem_W.mp ha).1 (sem_W_and h.1 ha)
  obtain ⟨asrc,bsrc⟩ := S50SplitDirty.dirty_sources_exact p a opposite' central aout h₂ h₃ h₆ h₇ h₈ h₉
  let d : V → Nat × Bool := fun x => if x ∈ ({3,6,7} : Finset V) then a else sem_bar a
  have allCover : ∀ x ∈ cycleSet, sem_W 10 D x = {p x,d x} := by
    intro x hx
    fin_cases x <;> simp only [cycleSet,Finset.mem_insert,Finset.mem_singleton] at hx
    · simp at hx
    · simp at hx
    · simpa [d] using h₂
    · simpa [d] using h₃
    · simp at hx
    · simp at hx
    · simpa [d] using h₆
    · simpa [d] using h₇
    · simpa [d] using h₈
    · simpa [d] using h₉
  have dirtyLower (x : V) (_hx : x ∈ cycleSet) : dirtySide x ⊆ supp 10 D (src D (d x)) := by
    simp only [dirtySide,d]
    split_ifs <;> simp [asrc,bsrc]
  have allowedT : T ∈ allowed := allowed_of_exit_cover h.1 hc T hT p d
    (fun x hx => (allCover x hx).subset) firstLower dirtyLower
  refine ⟨allowedT,a,asrc,bsrc,allCover,?_⟩
  exact S50SplitPrivate.private_mates_exact_of_small_opposite h hc f epure zero qsrc qout cover pure ne small
    (allowed_card T allowedT)

end PEqualNP.Outside.L_meta_2590_aux.S50SplitActual


namespace PEqualNP.Outside.L_meta_2590_aux.S50SplitCoverage
open DagTools Four S50Private S50SplitT S50SplitPorts

def canonical (e q a : Nat × Bool) (f : V → Nat × Bool) : Finset Nat :=
  {e.1,q.1,(f 1).1,(f 4).1,(f 5).1,a.1}

lemma exit_gate_covered {D : Dag} (e q a : Nat × Bool) (f : V → Nat × Bool) (T : Finset V)
    (zero : sem_W 10 D 0 = {e})
    (cover : ∀ x : V, Adj 0 x → sem_W 10 D x = {sem_bar e,q,f x})
    (outside : ∀ x ∈ cycleSet, sem_W 10 D x =
      {port T q f x,if x ∈ ({3,6,7} : Finset V) then a else sem_bar a}) :
    ∀ x : V, ∀ b ∈ sem_W 10 D x, b.1 ∈ canonical e q a f := by
  classical
  have fx (x : V) (hx : Adj 0 x) : (f x).1 ∈ canonical e q a f := by
    have hn := (I1Exposure.zero_neighbors x).mp hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl <;> simp [canonical]
  intro x b hb
  by_cases hx0 : x = 0
  · subst x
    rw [zero,Finset.mem_singleton] at hb
    rw [hb]
    simp [canonical]
  · by_cases hxN : Adj 0 x
    · rw [cover x hxN] at hb
      simp only [Finset.mem_insert,Finset.mem_singleton] at hb
      rcases hb with rfl | rfl | rfl
      · simp [canonical,sem_bar]
      · simp [canonical]
      · exact fx x hxN
    · have hxC := (cycle_mem_iff x).mpr ⟨hx0,hxN⟩
      rw [outside x hxC] at hb
      simp only [Finset.mem_insert,Finset.mem_singleton] at hb
      rcases hb with hb | hb
      · rw [hb]
        unfold port
        split_ifs
        · simp [sem_bar,canonical]
        · simpa only [sem_bar] using fx (owner x) (owner_geometry x hxC).2.2.1
      · rw [hb]
        split_ifs <;> simp [sem_bar,canonical]

lemma noncanonical_and_empty {D : Dag} (e q a : Nat × Bool) (f : V → Nat × Bool) (T : Finset V)
    (zero : sem_W 10 D 0 = {e})
    (cover : ∀ x : V, Adj 0 x → sem_W 10 D x = {sem_bar e,q,f x})
    (outside : ∀ x ∈ cycleSet, sem_W 10 D x =
      {port T q f x,if x ∈ ({3,6,7} : Finset V) then a else sem_bar a})
    (empty : ∀ j : Nat, j < D.length → tag D j = true → supp 10 D (10+j) = ∅)
    {j : Nat} (hj : j < D.length) (ht : tag D j = true)
    (hne : j ∉ canonical e q a f) :
    supp 10 D (opA D j) = ∅ ∧ supp 10 D (opB D j) = ∅ := by
  have slots (s : Bool) : supp 10 D (src D (j,s)) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro x hx
    have hm : (j,s) ∈ sem_W 10 D x := by
      apply sem_mem_W.mpr
      exact ⟨hj,hx,by rw [empty j hj ht]; simp⟩
    exact hne (exit_gate_covered e q a f T zero cover outside x (j,s) hm)
  exact ⟨by simpa only [sb_src_false] using slots false,
    by simpa only [sb_src_true] using slots true⟩

end PEqualNP.Outside.L_meta_2590_aux.S50SplitCoverage


namespace PEqualNP.Outside.L_meta_2590_aux.S50SplitDistinct
open DagTools Four S50Private S50SplitT

def sideA (i : Fin 6) : Finset V :=
  ([{0},{1,4,5},{1},{4},{5},{3,6,7}] : List (Finset V)).getD i.val ∅

def sideB (T : Finset V) (i : Fin 6) : Finset V :=
  ([{1,4,5},T,({2,6} : Finset V) \ T,({3,9} : Finset V) \ T,
    ({7,8} : Finset V) \ T,{2,8,9}] : List (Finset V)).getD i.val ∅

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 1000000 in
lemma distinct_profiles : ∀ T : Finset V, T ∈ allowed → ∀ i j : Fin 6, i ≠ j →
    sideA i ≠ sideA j ∧ (sideA i ≠ sideB T j ∨ sideB T i ≠ sideA j) := by
  decide +kernel

lemma same_gate_arc_cases (a b : Nat × Bool) (eq : a.1 = b.1) :
    a = b ∨ a = sem_bar b := by
  rcases a with ⟨i,s⟩
  rcases b with ⟨j,t⟩
  change i = j at eq
  subst j
  cases s <;> cases t <;> simp [sem_bar]

lemma gate_injective {D : Dag} (T : Finset V) (hT : T ∈ allowed)
    (r : Fin 6 → Nat × Bool)
    (left : ∀ i, supp 10 D (src D (r i)) = sideA i)
    (right : ∀ i, supp 10 D (src D (sem_bar (r i))) = sideB T i) :
    Function.Injective (fun i => (r i).1) := by
  intro i j hg
  by_contra hij
  obtain ⟨hnormal,hreverse⟩ := distinct_profiles T hT i j hij
  rcases same_gate_arc_cases (r i) (r j) hg with hs | hs
  · exact hnormal (by rw [← left i,hs,left j])
  · have hA : sideA i = sideB T j := by rw [← left i,hs,right j]
    have hB : sideB T i = sideA j := by rw [← right i,hs,bar_bar,left j]
    rcases hreverse with hn | hn
    · exact hn hA
    · exact hn hB

end PEqualNP.Outside.L_meta_2590_aux.S50SplitDistinct


namespace PEqualNP.Outside.L_meta_2590_aux.S50ExtraSeed
open DagTools Four SharedDom S50Meeting S50Private S50SplitT

def color (x : V) : Finset V := if x ∈ ({3,6,7} : Finset V) then {3,6,7} else {2,8,9}

def oppositeColor (x : V) : Finset V := if x ∈ ({3,6,7} : Finset V) then {2,8,9} else {3,6,7}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 1000000 in
lemma seed_geometry : ∀ u : V, u ≠ 0 → ¬ Adj 0 u →
    ∃ x v w p : V, Adj 0 x ∧ Adj x u ∧ Adj u v ∧ Adj u w ∧ Adj x p ∧
      v ≠ x ∧ w ≠ x ∧ p ≠ 0 ∧ p ≠ u ∧ v ≠ w ∧ v ≠ p ∧ w ≠ p ∧
      ({v,w,p} : Finset V) = oppositeColor u := by
  unfold Adj edgeList
  decide +kernel

lemma color_partition : ∀ u : V,
    color u ∪ oppositeColor u = cycleSet ∧ Disjoint (color u) (oppositeColor u) ∧
      (color u).card = 3 ∧ (oppositeColor u).card = 3 := by
  decide +kernel

set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 1000000 in
lemma color_outside : ∀ u : V, ∀ v ∈ color u ∪ oppositeColor u, v ≠ 0 ∧ ¬ Adj 0 v := by
  unfold Adj edgeList
  decide +kernel

lemma self_color : ∀ u ∈ cycleSet, u ∈ color u := by
  decide +kernel

lemma color_stable : ∀ u : V, ∀ v ∈ color u,
    color v = color u ∧ oppositeColor v = oppositeColor u := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 1000000 in
lemma color_two_neighbors : ∀ u : V, ∀ v ∈ color u,
    ∃ w z : V, w ∈ oppositeColor u ∧ z ∈ oppositeColor u ∧ w ≠ z ∧ Adj v w ∧ Adj v z := by
  unfold Adj edgeList
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 1000000 in
lemma opposite_two_neighbors : ∀ u : V, ∀ v ∈ oppositeColor u,
    ∃ w z : V, w ∈ color u ∧ z ∈ color u ∧ w ≠ z ∧ Adj v w ∧ Adj v z := by
  unfold Adj edgeList
  decide +kernel

lemma extra_common_source_opposite_color {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (hi : (0 : V) ∈ ineligSet 10 D)
    {e q : Nat × Bool} (epure : supp 10 D (src D e) = {0})
    (hq : ∀ x : V, Adj 0 x → q ∈ sem_W 10 D x)
    (qout : supp 10 D (10 + q.1) = ∅)
    (ports : ∀ x : V, Adj 0 x → ∃ f : Nat × Bool,
      sem_W 10 D x = {sem_bar e,q,f} ∧ supp 10 D (src D f) = {x})
    {u : V} (hu0 : u ≠ 0) (huN : ¬ Adj 0 u)
    (small : (sem_W 10 D u).card ≤ 2) (huq : u ∈ supp 10 D (src D q)) :
    oppositeColor u ⊆ supp 10 D (src D (sem_bar q)) := by
  classical
  obtain ⟨x,v,w,p,hxN,hxu,huv,huw,hxp,hvx,hwx,hp0,hpu,hvw,hvp,hwp,heq⟩ :=
    seed_geometry u hu0 huN
  obtain ⟨f,cover,fpure⟩ := ports x hxN
  have fxmem : f ∈ sem_W 10 D x := by rw [cover]; simp
  have qxu := hq x hxN
  have qvalid := (sem_mem_W.mp qxu).1
  have qumem : q ∈ sem_W 10 D u := by
    apply sem_mem_W.mpr
    exact ⟨qvalid,huq,by rw [qout]; simp⟩
  have fumem : sem_bar f ∈ sem_W 10 D u := by
    rcases case50_edge_coverage h hc hxu hu0 cover epure with hh | hh
    · exact False.elim (hh.2.1 huq)
    · exact hh.1
  have fne : sem_bar f ≠ q := by
    intro eq
    have hm := (sem_mem_W.mp qxu).2.1
    rw [← eq] at hm
    exact exit_opposite_excludes h.1 fxmem hm
  have fpureU : supp 10 D (src D (sem_bar f)) = {u} :=
    other_exit_pure h hc hi hu0 small qumem
      (fun a ha => (sem_mem_W.mp (hq a ha)).2.1) fumem fne
  have other (z : V) (huz : Adj u z) (hzx : z ≠ x) :
      z ∈ supp 10 D (src D (sem_bar q)) := by
    obtain ⟨a,ha,hza,_⟩ := sem_edge_slots graph_ok h.1 hc huz
    have hm := (sem_mem_W.mp hza).2.1
    rcases mem_of_card_le_two (sem_W 10 D u) small qumem fumem ha (Ne.symm fne) with he | he
    · exact he ▸ hm
    · rw [he,bar_bar,fpure,Finset.mem_singleton] at hm
      exact False.elim (hzx hm)
  have hv := other v huv hvx
  have hw := other w huw hwx
  have hp : p ∈ supp 10 D (src D (sem_bar q)) := by
    rcases case50_edge_coverage h hc hxp hp0 cover epure with hh | hh
    · exact (sem_mem_W.mp hh.1).2.1
    · have hm := (sem_mem_W.mp hh.1).2.1
      rw [fpureU,Finset.mem_singleton] at hm
      exact False.elim (hpu hm)
  have sub : ({v,w,p} : Finset V) ⊆ supp 10 D (src D (sem_bar q)) := by
    intro z hz
    simp only [Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl <;> assumption
  rw [← heq]
  exact sub

end PEqualNP.Outside.L_meta_2590_aux.S50ExtraSeed


namespace PEqualNP.Outside.L_meta_2590_aux.S50ExtraClosure
open DagTools Four S50Meeting S50Private S50SplitCycle

lemma two_opposite_neighbors_force_source {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    {e q : Nat × Bool} (f : V → Nat × Bool)
    (epure : supp 10 D (src D e) = {0})
    (qout : supp 10 D (10+q.1) = ∅)
    (cover : ∀ x : V, Adj 0 x → sem_W 10 D x = {sem_bar e,q,f x})
    (pure : ∀ x : V, Adj 0 x → supp 10 D (src D (f x)) = {x})
    (small : ∀ y : V, y ≠ 0 → ¬ Adj 0 y → (sem_W 10 D y).card ≤ 2)
    {v b c : V} (hv0 : v ≠ 0) (hvN : ¬ Adj 0 v)
    (hb0 : b ≠ 0) (hbN : ¬ Adj 0 b) (hc0 : c ≠ 0) (hcN : ¬ Adj 0 c)
    (hvb : Adj v b) (hvc : Adj v c) (hbc : b ≠ c)
    (hbT : b ∈ supp 10 D (src D (sem_bar q)))
    (hcT : c ∈ supp 10 D (src D (sem_bar q))) :
    v ∈ supp 10 D (src D q) := by
  classical
  by_contra hvq
  have hq1 : q ∈ sem_W 10 D (1 : V) := by rw [cover 1 (by decide +kernel)]; simp
  have qvalid := (sem_mem_W.mp hq1).1
  have opposite_mem (x : V) (hx : x ∈ supp 10 D (src D (sem_bar q))) :
      sem_bar q ∈ sem_W 10 D x := by
    apply sem_mem_W.mpr
    refine ⟨qvalid,hx,?_⟩
    change x ∉ supp 10 D (10+q.1)
    rw [qout]
    simp
  have hbq := opposite_mem b hbT
  have hcq := opposite_mem c hcT
  have first : ∃ p : Nat × Bool, p ∈ sem_W 10 D v ∧
      b ∉ supp 10 D (src D (sem_bar p)) ∧ c ∉ supp 10 D (src D (sem_bar p)) := by
    by_cases hvT : v ∈ supp 10 D (src D (sem_bar q))
    · refine ⟨sem_bar q,opposite_mem v hvT,?_,?_⟩
      · simpa only [bar_bar] using exit_opposite_excludes h.1 hbq
      · simpa only [bar_bar] using exit_opposite_excludes h.1 hcq
    · obtain ⟨x,_,hx,hxv,_,_,_⟩ := outside_neighbors v hv0 hvN
      have hp : sem_bar (f x) ∈ sem_W 10 D v := by
        rcases case50_edge_coverage h hc hxv hv0 (cover x hx) epure with hh | hh
        · exact False.elim (hvT (sem_mem_W.mp hh.1).2.1)
        · exact hh.1
      refine ⟨sem_bar (f x),hp,?_,?_⟩
      · simp only [bar_bar,pure x hx,Finset.mem_singleton]
        exact fun eq => hbN (eq ▸ hx)
      · simp only [bar_bar,pure x hx,Finset.mem_singleton]
        exact fun eq => hcN (eq ▸ hx)
  obtain ⟨p,hp,hbp,hcp⟩ := first
  obtain ⟨d,hd,hbd,_,_,_⟩ := sem_edge_slots graph_ok h.1 hc hvb
  obtain ⟨d',hd',hcd',_,_,_⟩ := sem_edge_slots graph_ok h.1 hc hvc
  have hdp : d ≠ p := fun eq => hbp (by simpa only [eq] using (sem_mem_W.mp hbd).2.1)
  have hd'p : d' ≠ p := fun eq => hcp (by simpa only [eq] using (sem_mem_W.mp hcd').2.1)
  have heq := unique_away (sem_W 10 D v) (small v hv0 hvN) hp hd hd' hdp hd'p
  have hcd : sem_bar d ∈ sem_W 10 D c := heq ▸ hcd'
  have hne : sem_bar d ≠ sem_bar q := by
    intro eq
    have dq : d = q := by simpa only [bar_bar] using congrArg sem_bar eq
    exact hvq (by simpa only [dq] using (sem_mem_W.mp hd).2.1)
  obtain ⟨Z,hZ,hcZ,_,hitb⟩ := SharedDom.i1_exposure_omit_geometry b c hb0 hc0 (Ne.symm hbc)
  obtain ⟨j,s,hj,_,hbs,hbo,free⟩ := sem_exposure graph_ok h.1 hc Z hZ b hitb
  have hw : (j,s) ∈ sem_W 10 D b := sem_mem_W.mpr ⟨hj,hbs,hbo⟩
  rcases mem_of_card_le_two (sem_W 10 D b) (small b hb0 hbN) hbd hbq hw hne with he | he
  · rw [he] at free
    exact Finset.disjoint_left.mp free (sem_mem_W.mp hcd).2.1 hcZ
  · rw [he] at free
    exact Finset.disjoint_left.mp free hcT hcZ

end PEqualNP.Outside.L_meta_2590_aux.S50ExtraClosure


namespace PEqualNP.Outside.L_meta_2590_aux.S50ExtraActual
open DagTools Four S50Meeting S50Private S50SplitT S50SplitPorts S50ExtraSeed S50ExtraClosure

lemma extra_profile_colors {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (hi : (0 : V) ∈ ineligSet 10 D)
    {e q : Nat × Bool} (f : V → Nat × Bool)
    (epure : supp 10 D (src D e) = {0})
    (zero : sem_W 10 D 0 = {e}) (eqne : e.1 ≠ q.1)
    (qout : supp 10 D (10+q.1) = ∅)
    (cover : ∀ x : V, Adj 0 x → sem_W 10 D x = {sem_bar e,q,f x})
    (pure : ∀ x : V, Adj 0 x → supp 10 D (src D (f x)) = {x})
    (small : ∀ y : V, y ≠ 0 → ¬ Adj 0 y → (sem_W 10 D y).card ≤ 2)
    {u : V} (hu0 : u ≠ 0) (huN : ¬ Adj 0 u) (huq : u ∈ supp 10 D (src D q)) :
    supp 10 D (src D q) = ({1,4,5} : Finset V) ∪ color u ∧
    supp 10 D (src D (sem_bar q)) = oppositeColor u := by
  classical
  have common (x : V) (hx : Adj 0 x) : q ∈ sem_W 10 D x := by rw [cover x hx]; simp
  have ports (x : V) (hx : Adj 0 x) : ∃ a : Nat × Bool,
      sem_W 10 D x = {sem_bar e,q,a} ∧ supp 10 D (src D a) = {x} :=
    ⟨f x,cover x hx,pure x hx⟩
  have seed := extra_common_source_opposite_color h hc hi epure common qout ports hu0 huN
    (small u hu0 huN) huq
  have colorSource : color u ⊆ supp 10 D (src D q) := by
    intro v hv
    have vv := color_outside u v (Finset.mem_union_left _ hv)
    obtain ⟨b,c,hb,hc',hbc,hvb,hvc⟩ := color_two_neighbors u v hv
    have bb := color_outside u b (Finset.mem_union_right _ hb)
    have cc := color_outside u c (Finset.mem_union_right _ hc')
    exact two_opposite_neighbors_force_source h hc f epure qout cover pure small
      vv.1 vv.2 bb.1 bb.2 cc.1 cc.2 hvb hvc hbc (seed hb) (seed hc')
  have nSource : ({1,4,5} : Finset V) ⊆ supp 10 D (src D q) := by
    intro v hv
    exact (sem_mem_W.mp (common v ((I1Exposure.zero_neighbors v).mpr hv))).2.1
  have sourceZero : (0 : V) ∉ supp 10 D (src D q) := by
    intro hz
    have hp := sem_inelig_pure graph_ok h.1 hc hi hz
    have hone := nSource (show (1 : V) ∈ ({1,4,5} : Finset V) by decide)
    rw [hp,Finset.mem_singleton] at hone
    exact (by decide : (1 : V) ≠ 0) hone
  have qvalid := (sem_mem_W.mp (common 1 (by decide +kernel))).1
  have opposite_mem (x : V) (hx : x ∈ supp 10 D (src D (sem_bar q))) : sem_bar q ∈ sem_W 10 D x := by
    apply sem_mem_W.mpr
    refine ⟨qvalid,hx,?_⟩
    change x ∉ supp 10 D (10+q.1)
    rw [qout]
    simp
  have noBoth (x : V) (hx : x ∈ supp 10 D (src D (sem_bar q))) : x ∉ supp 10 D (src D q) := by
    simpa only [bar_bar] using exit_opposite_excludes h.1 (opposite_mem x hx)
  constructor
  · apply Finset.Subset.antisymm
    · intro x hx
      by_cases hxN : Adj 0 x
      · exact Finset.mem_union_left _ ((I1Exposure.zero_neighbors x).mp hxN)
      · have hx0 : x ≠ 0 := fun eq => sourceZero (eq ▸ hx)
        have hcycle := (cycle_mem_iff x).mpr ⟨hx0,hxN⟩
        rw [← (color_partition u).1] at hcycle
        rcases Finset.mem_union.mp hcycle with ha | hb
        · exact Finset.mem_union_right _ ha
        · exact False.elim (noBoth x (seed hb) hx)
    · exact Finset.union_subset nSource colorSource
  · apply Finset.Subset.antisymm
    · intro x hx
      have hx0 : x ≠ 0 := by
        intro eq
        subst x
        have hm := opposite_mem 0 hx
        rw [zero,Finset.mem_singleton] at hm
        exact eqne (congrArg Prod.fst hm).symm
      have hxN : ¬ Adj 0 x := by
        intro hn
        exact noBoth x hx (nSource ((I1Exposure.zero_neighbors x).mp hn))
      have hcycle := (cycle_mem_iff x).mpr ⟨hx0,hxN⟩
      rw [← (color_partition u).1] at hcycle
      rcases Finset.mem_union.mp hcycle with ha | hb
      · exact False.elim (noBoth x hx (colorSource ha))
      · exact hb
    · exact seed

end PEqualNP.Outside.L_meta_2590_aux.S50ExtraActual


namespace PEqualNP.Outside.L_meta_2590_aux.S50ExtraPrivate
open DagTools Four SharedDom S50Meeting S50Private S50SplitT S50ExtraSeed

def mate (u x : V) : V :=
  if x = 1 then if u ∈ ({3,6,7} : Finset V) then 6 else 2
  else if x = 4 then if u ∈ ({3,6,7} : Finset V) then 3 else 9
  else if u ∈ ({3,6,7} : Finset V) then 7 else 8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 1000000 in
lemma mate_geometry : ∀ u x : V, Adj 0 x →
    mate u x ∈ color u ∧ Adj x (mate u x) ∧ mate u x ≠ 0 ∧ ¬ Adj 0 (mate u x) := by
  unfold Adj edgeList
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 1000000 in
lemma owner_geometry : ∀ u : V, ∀ v ∈ color u,
    Adj 0 (owner v) ∧ Adj (owner v) v ∧ mate u (owner v) = v ∧ v ≠ 0 ∧ ¬ Adj 0 v := by
  unfold Adj edgeList
  decide +kernel

lemma private_mates_exact {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (hi : (0 : V) ∈ ineligSet 10 D)
    {e q : Nat × Bool} (f : V → Nat × Bool) (u : V)
    (epure : supp 10 D (src D e) = {0})
    (qsrc : supp 10 D (src D q) = ({1,4,5} : Finset V) ∪ color u)
    (qout : supp 10 D (10+q.1) = ∅)
    (cover : ∀ x : V, Adj 0 x → sem_W 10 D x = {sem_bar e,q,f x})
    (small : ∀ y : V, y ≠ 0 → ¬ Adj 0 y → (sem_W 10 D y).card ≤ 2) :
    ∀ x : V, Adj 0 x → supp 10 D (src D (sem_bar (f x))) = {mate u x} := by
  intro x hx
  obtain ⟨hcolor,hxv,hv0,hvN⟩ := mate_geometry u x hx
  have qx : q ∈ sem_W 10 D x := by rw [cover x hx]; simp
  have fx : f x ∈ sem_W 10 D x := by rw [cover x hx]; simp
  have hvq : mate u x ∈ supp 10 D (src D q) := by
    rw [qsrc]
    exact Finset.mem_union_right _ hcolor
  have qv : q ∈ sem_W 10 D (mate u x) :=
    sem_mem_W.mpr ⟨(sem_mem_W.mp qx).1,hvq,by rw [qout]; simp⟩
  have fv : sem_bar (f x) ∈ sem_W 10 D (mate u x) := by
    rcases case50_edge_coverage h hc hxv hv0 (cover x hx) epure with hh | hh
    · exact False.elim (hh.2.1 hvq)
    · exact hh.1
  have hne : sem_bar (f x) ≠ q := by
    intro eq
    have hxs := (sem_mem_W.mp qx).2.1
    rw [← eq] at hxs
    exact exit_opposite_excludes h.1 fx hxs
  apply other_exit_pure h hc hi hv0 (small _ hv0 hvN) qv _ fv hne
  intro a ha
  rw [qsrc]
  exact Finset.mem_union_left _ ((I1Exposure.zero_neighbors a).mp ha)

lemma source_side_cover {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    {e q : Nat × Bool} (f : V → Nat × Bool) (u : V)
    (epure : supp 10 D (src D e) = {0})
    (qsrc : supp 10 D (src D q) = ({1,4,5} : Finset V) ∪ color u)
    (qout : supp 10 D (10+q.1) = ∅)
    (cover : ∀ x : V, Adj 0 x → sem_W 10 D x = {sem_bar e,q,f x})
    (small : ∀ y : V, y ≠ 0 → ¬ Adj 0 y → (sem_W 10 D y).card ≤ 2) :
    ∀ v ∈ color u, sem_W 10 D v = {q,sem_bar (f (owner v))} := by
  classical
  intro v hv
  obtain ⟨hx,hxv,_,hv0,hvN⟩ := owner_geometry u v hv
  have qx : q ∈ sem_W 10 D (owner v) := by rw [cover _ hx]; simp
  have fx : f (owner v) ∈ sem_W 10 D (owner v) := by rw [cover _ hx]; simp
  have hvq : v ∈ supp 10 D (src D q) := by
    rw [qsrc]
    exact Finset.mem_union_right _ hv
  have qv : q ∈ sem_W 10 D v :=
    sem_mem_W.mpr ⟨(sem_mem_W.mp qx).1,hvq,by rw [qout]; simp⟩
  have fv : sem_bar (f (owner v)) ∈ sem_W 10 D v := by
    rcases case50_edge_coverage h hc hxv hv0 (cover _ hx) epure with hh | hh
    · exact False.elim (hh.2.1 hvq)
    · exact hh.1
  have hne : q ≠ sem_bar (f (owner v)) := by
    intro eq
    have hxs := (sem_mem_W.mp qx).2.1
    rw [eq] at hxs
    exact exit_opposite_excludes h.1 fx hxs
  ext a
  simp only [Finset.mem_insert,Finset.mem_singleton]
  constructor
  · intro ha
    exact mem_of_card_le_two _ (small v hv0 hvN) qv fv ha hne
  · rintro (rfl | rfl) <;> assumption

end PEqualNP.Outside.L_meta_2590_aux.S50ExtraPrivate


namespace PEqualNP.Outside.L_meta_2590_aux.S50ExtraOpposite
open DagTools Four SharedDom S50Meeting S50Private S50SplitT S50ExtraSeed S50ExtraPrivate

lemma source_subset_opposite {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (hi : (0 : V) ∈ ineligSet 10 D)
    {e q : Nat × Bool} (f : V → Nat × Bool) (u : V)
    (epure : supp 10 D (src D e) = {0})
    (ebar : supp 10 D (src D (sem_bar e)) = ({1,4,5} : Finset V))
    (zero : sem_W 10 D 0 = {e})
    (qsrc : supp 10 D (src D q) = ({1,4,5} : Finset V) ∪ color u)
    (qout : supp 10 D (10+q.1) = ∅)
    (cover : ∀ x : V, Adj 0 x → sem_W 10 D x = {sem_bar e,q,f x})
    (pure : ∀ x : V, Adj 0 x → supp 10 D (src D (f x)) = {x})
    (small : ∀ y : V, y ≠ 0 → ¬ Adj 0 y → (sem_W 10 D y).card ≤ 2)
    (empty : ∀ j : Nat, j < D.length → tag D j = true → supp 10 D (10+j) = ∅)
    {b : V} (hb : b ∈ oppositeColor u) {r : Nat × Bool} (hr : r ∈ sem_W 10 D b) :
    supp 10 D (src D r) ⊆ oppositeColor u := by
  classical
  have hbounds := color_outside u b (Finset.mem_union_right _ hb)
  have hb0 := hbounds.1
  have hbN := hbounds.2
  have hbA : b ∉ color u := fun hba => Finset.disjoint_left.mp (color_partition u).2.1 hba hb
  have hbq : b ∉ supp 10 D (src D q) := by
    rw [qsrc]
    intro hmem
    rcases Finset.mem_union.mp hmem with hn | ha
    · exact hbN ((I1Exposure.zero_neighbors b).mpr hn)
    · exact hbA ha
  have privateSides := private_mates_exact h hc hi f u epure qsrc qout cover small
  have ac := source_side_cover h hc f u epure qsrc qout cover small
  intro y hy
  have hry : r ∈ sem_W 10 D y := sem_mem_W.mpr
    ⟨(sem_mem_W.mp hr).1,hy,by rw [empty r.1 (sem_mem_W.mp hr).1 (sem_W_and h.1 hr)]; simp⟩
  have hbr := (sem_mem_W.mp hr).2.1
  by_contra hyB
  by_cases hy0 : y = 0
  · subst y
    rw [zero,Finset.mem_singleton] at hry
    rw [hry,epure,Finset.mem_singleton] at hbr
    exact hb0 hbr
  · by_cases hyN : Adj 0 y
    · rw [cover y hyN] at hry
      simp only [Finset.mem_insert,Finset.mem_singleton] at hry
      rcases hry with hry | hry | hry
      · rw [hry,ebar] at hbr
        exact hbN ((I1Exposure.zero_neighbors b).mpr hbr)
      · exact hbq (hry ▸ hbr)
      · rw [hry,pure y hyN,Finset.mem_singleton] at hbr
        exact hbN (hbr ▸ hyN)
    · have hyC : y ∈ cycleSet := (S50SplitPorts.cycle_mem_iff y).mpr ⟨hy0,hyN⟩
      have hyUnion : y ∈ color u ∪ oppositeColor u := by
        rw [(color_partition u).1]
        exact hyC
      have hyA : y ∈ color u := (Finset.mem_union.mp hyUnion).resolve_right hyB
      rw [ac y hyA] at hry
      simp only [Finset.mem_insert,Finset.mem_singleton] at hry
      rcases hry with hry | hry
      · exact hbq (hry ▸ hbr)
      · obtain ⟨ho,_,hm,_,_⟩ := S50ExtraPrivate.owner_geometry u y hyA
        rw [hry,privateSides (owner y) ho,hm,Finset.mem_singleton] at hbr
        exact hbA (hbr ▸ hyA)

lemma other_pure_of_subset {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (u : V) (q r : Nat × Bool) {b : V} (hb : b ∈ oppositeColor u)
    (qsrc : supp 10 D (src D (sem_bar q)) = oppositeColor u)
    (hq : sem_bar q ∈ sem_W 10 D b) (hr : r ∈ sem_W 10 D b)
    (hne : r ≠ sem_bar q) (small : (sem_W 10 D b).card ≤ 2)
    (sub : supp 10 D (src D r) ⊆ oppositeColor u) :
    supp 10 D (src D r) = {b} := by
  classical
  have hb0 := (color_outside u b (Finset.mem_union_right _ hb)).1
  apply Finset.Subset.antisymm
  · intro c hcsrc
    apply Finset.mem_singleton.mpr
    by_contra hcb
    have hcB := sub hcsrc
    have hc0 := (color_outside u c (Finset.mem_union_right _ hcB)).1
    obtain ⟨Z,hZ,hcZ,_,hitb⟩ := SharedDom.i1_exposure_omit_geometry b c hb0 hc0 hcb
    obtain ⟨j,s,hj,_,hbs,hbo,free⟩ := sem_exposure graph_ok h.1 hc Z hZ b hitb
    have hw : (j,s) ∈ sem_W 10 D b := sem_mem_W.mpr ⟨hj,hbs,hbo⟩
    rcases mem_of_card_le_two _ small hr hq hw hne with he | he
    · rw [he] at free
      exact Finset.disjoint_left.mp free hcsrc hcZ
    · rw [he,qsrc] at free
      exact Finset.disjoint_left.mp free hcB hcZ
  · exact Finset.singleton_subset_iff.mpr (sem_mem_W.mp hr).2.1

lemma opposite_ports_pure {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (hi : (0 : V) ∈ ineligSet 10 D)
    {e q : Nat × Bool} (f : V → Nat × Bool) (u : V)
    (epure : supp 10 D (src D e) = {0})
    (ebar : supp 10 D (src D (sem_bar e)) = ({1,4,5} : Finset V))
    (zero : sem_W 10 D 0 = {e})
    (qsrc : supp 10 D (src D q) = ({1,4,5} : Finset V) ∪ color u)
    (qbar : supp 10 D (src D (sem_bar q)) = oppositeColor u)
    (qout : supp 10 D (10+q.1) = ∅)
    (cover : ∀ x : V, Adj 0 x → sem_W 10 D x = {sem_bar e,q,f x})
    (pure : ∀ x : V, Adj 0 x → supp 10 D (src D (f x)) = {x})
    (two : ∀ y : V, y ≠ 0 → ¬ Adj 0 y → (sem_W 10 D y).card = 2)
    (empty : ∀ j : Nat, j < D.length → tag D j = true → supp 10 D (10+j) = ∅) :
    ∀ b ∈ oppositeColor u, ∃ r : Nat × Bool,
      r ≠ sem_bar q ∧ sem_W 10 D b = {sem_bar q,r} ∧ supp 10 D (src D r) = {b} := by
  classical
  intro b hb
  obtain ⟨hb0,hbN⟩ := color_outside u b (Finset.mem_union_right _ hb)
  have qx : q ∈ sem_W 10 D (1 : V) := by rw [cover 1 (by decide +kernel)]; simp
  have hqb : sem_bar q ∈ sem_W 10 D b := by
    apply sem_mem_W.mpr
    refine ⟨(sem_mem_W.mp qx).1,?_,?_⟩
    · rw [qbar]
      exact hb
    · change b ∉ supp 10 D (10+q.1)
      rw [qout]
      simp
  have small (x : V) (hx0 : x ≠ 0) (hxN : ¬ Adj 0 x) : (sem_W 10 D x).card ≤ 2 :=
    (two x hx0 hxN).le
  have existsOther : ∃ r ∈ sem_W 10 D b, r ≠ sem_bar q := by
    by_contra hn
    push Not at hn
    have sub : sem_W 10 D b ⊆ {sem_bar q} := by
      intro r hr
      exact Finset.mem_singleton.mpr (hn r hr)
    have count := Finset.card_le_card sub
    rw [two b hb0 hbN,Finset.card_singleton] at count
    omega
  obtain ⟨r,hr,hne⟩ := existsOther
  have sub := source_subset_opposite h hc hi f u epure ebar zero qsrc qout cover pure small empty hb hr
  have pureR := other_pure_of_subset h hc u q r hb qbar hqb hr hne (small b hb0 hbN) sub
  refine ⟨r,hne,?_,pureR⟩
  ext a
  simp only [Finset.mem_insert,Finset.mem_singleton]
  constructor
  · intro ha
    exact mem_of_card_le_two _ (small b hb0 hbN) hqb hr ha (Ne.symm hne)
  · rintro (rfl | rfl) <;> assumption

end PEqualNP.Outside.L_meta_2590_aux.S50ExtraOpposite


namespace PEqualNP.Outside.L_meta_2590_aux.S50ExtraCoverage
open DagTools Four S50Private S50SplitT S50SplitPorts S50ExtraSeed

def baseArcs (e q : Nat × Bool) (f : V → Nat × Bool) : Finset (Nat × Bool) :=
  {e,sem_bar e,q,sem_bar q,f 1,sem_bar (f 1),f 4,sem_bar (f 4),f 5,sem_bar (f 5)}

def allArcs (e q : Nat × Bool) (f r : V → Nat × Bool) (u : V) : Finset (Nat × Bool) :=
  baseArcs e q f ∪ (oppositeColor u).image r

def allGates (e q : Nat × Bool) (f r : V → Nat × Bool) (u : V) : Finset Nat :=
  (allArcs e q f r u).image Prod.fst

lemma base_bar_closed (e q : Nat × Bool) (f : V → Nat × Bool)
    {a : Nat × Bool} (ha : a ∈ baseArcs e q f) : sem_bar a ∈ baseArcs e q f := by
  simp only [baseArcs,Finset.mem_insert,Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [baseArcs,bar_bar]

lemma base_bar_iff (e q : Nat × Bool) (f : V → Nat × Bool) (a : Nat × Bool) :
    sem_bar a ∈ baseArcs e q f ↔ a ∈ baseArcs e q f := by
  constructor
  · intro ha
    simpa only [bar_bar] using base_bar_closed e q f ha
  · exact base_bar_closed e q f

lemma exit_arc_covered {D : Dag} (e q : Nat × Bool) (f r : V → Nat × Bool) (u : V)
    (zero : sem_W 10 D 0 = {e})
    (cover : ∀ x : V, Adj 0 x → sem_W 10 D x = {sem_bar e,q,f x})
    (sourceSide : ∀ x ∈ color u, sem_W 10 D x = {q,sem_bar (f (owner x))})
    (oppositeSide : ∀ x ∈ oppositeColor u, sem_W 10 D x = {sem_bar q,r x}) :
    ∀ x : V, ∀ a ∈ sem_W 10 D x, a ∈ allArcs e q f r u := by
  classical
  have fx (x : V) (hx : Adj 0 x) : f x ∈ baseArcs e q f := by
    have hn := (I1Exposure.zero_neighbors x).mp hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl <;> simp [baseArcs]
  intro x a ha
  by_cases hx0 : x = 0
  · subst x
    rw [zero,Finset.mem_singleton] at ha
    rw [ha]
    exact Finset.mem_union_left _ (by simp [baseArcs])
  · by_cases hxN : Adj 0 x
    · rw [cover x hxN] at ha
      simp only [Finset.mem_insert,Finset.mem_singleton] at ha
      apply Finset.mem_union_left
      rcases ha with rfl | rfl | rfl
      · simp [baseArcs]
      · simp [baseArcs]
      · exact fx x hxN
    · have hxC := (cycle_mem_iff x).mpr ⟨hx0,hxN⟩
      have hxAB : x ∈ color u ∪ oppositeColor u := by
        rw [(color_partition u).1]
        exact hxC
      rcases Finset.mem_union.mp hxAB with hxA | hxB
      · rw [sourceSide x hxA] at ha
        simp only [Finset.mem_insert,Finset.mem_singleton] at ha
        apply Finset.mem_union_left
        rcases ha with rfl | rfl
        · simp [baseArcs]
        · exact base_bar_closed e q f (fx (owner x) (owner_geometry x hxC).2.2.1)
      · rw [oppositeSide x hxB] at ha
        simp only [Finset.mem_insert,Finset.mem_singleton] at ha
        rcases ha with rfl | rfl
        · exact Finset.mem_union_left _ (by simp [baseArcs])
        · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x,hxB,rfl⟩)

lemma noncanonical_and_empty {D : Dag} (e q : Nat × Bool) (f r : V → Nat × Bool) (u : V)
    (zero : sem_W 10 D 0 = {e})
    (cover : ∀ x : V, Adj 0 x → sem_W 10 D x = {sem_bar e,q,f x})
    (sourceSide : ∀ x ∈ color u, sem_W 10 D x = {q,sem_bar (f (owner x))})
    (oppositeSide : ∀ x ∈ oppositeColor u, sem_W 10 D x = {sem_bar q,r x})
    (empty : ∀ j : Nat, j < D.length → tag D j = true → supp 10 D (10+j) = ∅)
    {j : Nat} (hj : j < D.length) (ht : tag D j = true)
    (hne : j ∉ allGates e q f r u) :
    supp 10 D (opA D j) = ∅ ∧ supp 10 D (opB D j) = ∅ := by
  have slots (s : Bool) : supp 10 D (src D (j,s)) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro x hx
    have hm : (j,s) ∈ sem_W 10 D x := sem_mem_W.mpr
      ⟨hj,hx,by rw [empty j hj ht]; simp⟩
    have hc := exit_arc_covered e q f r u zero cover sourceSide oppositeSide x (j,s) hm
    exact hne (Finset.mem_image.mpr ⟨(j,s),hc,rfl⟩)
  exact ⟨by simpa only [sb_src_false] using slots false,
    by simpa only [sb_src_true] using slots true⟩

end PEqualNP.Outside.L_meta_2590_aux.S50ExtraCoverage


namespace PEqualNP.Outside.L_meta_2590_aux.S50MateMatching
open DagTools S50Private

lemma pure_arcs_injective {n : Nat} {D : Dag} (B : Finset (Fin n))
    (r : Fin n → Nat × Bool)
    (pure : ∀ b ∈ B, supp n D (src D (r b)) = {b}) :
    Set.InjOn r (↑B : Set (Fin n)) := by
  intro b hb c hc eq
  have hs : ({b} : Finset (Fin n)) = {c} := by rw [← pure b hb,eq,pure c hc]
  exact Finset.singleton_inj.mp hs

lemma mate_empty_or_paired {n : Nat} {D : Dag} (h : Strict n D)
    (B : Finset (Fin n)) (r : Fin n → Nat × Bool) (K : Finset (Nat × Bool))
    (closed : ∀ a ∈ K, sem_bar a ∈ K)
    (nonbase : ∀ b ∈ B, r b ∉ K)
    (member : ∀ b ∈ B, r b ∈ sem_W n D b)
    (cover : ∀ x : Fin n, sem_W n D x ⊆ K ∪ B.image r)
    (empty : ∀ j : Nat, j < D.length → tag D j = true → supp n D (n+j) = ∅) :
    ∀ b ∈ B, supp n D (src D (sem_bar (r b))) = ∅ ∨
      ∃ c ∈ B, c ≠ b ∧ r c = sem_bar (r b) := by
  classical
  intro b hb
  by_cases zero : supp n D (src D (sem_bar (r b))) = ∅
  · exact Or.inl zero
  · right
    obtain ⟨c,hc⟩ := Finset.nonempty_iff_ne_empty.mpr zero
    have hr := member b hb
    have hbar : sem_bar (r b) ∈ sem_W n D c := by
      apply sem_mem_W.mpr
      refine ⟨(sem_mem_W.mp hr).1,hc,?_⟩
      change c ∉ supp n D (n+(r b).1)
      rw [empty (r b).1 (sem_mem_W.mp hr).1 (sem_W_and h hr)]
      simp
    rcases Finset.mem_union.mp (cover c hbar) with hk | hi
    · have bad := closed _ hk
      rw [bar_bar] at bad
      exact False.elim (nonbase b hb bad)
    · obtain ⟨d,hd,heq⟩ := Finset.mem_image.mp hi
      have hdb : d ≠ b := by
        intro eq
        subst d
        have hx : b ∈ supp n D (src D (sem_bar (r b))) := by
          rw [← heq]
          exact (sem_mem_W.mp hr).2.1
        exact exit_opposite_excludes h hr hx
      exact ⟨d,hd,hdb,heq⟩

end PEqualNP.Outside.L_meta_2590_aux.S50MateMatching


namespace PEqualNP.Outside.L_meta_2590_aux.S50ThreeMatching
open DagTools S50Private

lemma three_indices : ∀ i j k : Fin 3, i ≠ j → k ≠ i → k ≠ j →
    ∀ l : Fin 3, l = i ∨ l = j ∨ l = k := by decide

lemma three_pairings (r : Fin 3 → Nat × Bool) (inj : Function.Injective r)
    (E : Fin 3 → Prop)
    (cases : ∀ i : Fin 3, E i ∨ ∃ j : Fin 3, j ≠ i ∧ r j = sem_bar (r i)) :
    (E 0 ∧ E 1 ∧ E 2) ∨ (r 1 = sem_bar (r 0) ∧ E 2) ∨
      (r 2 = sem_bar (r 0) ∧ E 1) ∨ (r 2 = sem_bar (r 1) ∧ E 0) := by
  classical
  have remaining (i j k : Fin 3) (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
      (pair : r j = sem_bar (r i)) : E k := by
    rcases cases k with he | ⟨l,hlk,hl⟩
    · exact he
    rcases three_indices i j k hij hki hkj l with rfl | rfl | rfl
    · have eq : r j = r k := by rw [pair,hl,bar_bar]
      exact False.elim (hkj (inj eq).symm)
    · have eq : r i = r k := by
        have hh := congrArg sem_bar (pair.symm.trans hl)
        simpa only [bar_bar] using hh
      exact False.elim (hki (inj eq).symm)
    · exact False.elim (hlk rfl)
  by_cases p01 : r 1 = sem_bar (r 0)
  · exact Or.inr (Or.inl ⟨p01,remaining 0 1 2 (by decide) (by decide) (by decide) p01⟩)
  by_cases p02 : r 2 = sem_bar (r 0)
  · exact Or.inr (Or.inr (Or.inl ⟨p02,remaining 0 2 1 (by decide) (by decide) (by decide) p02⟩))
  by_cases p12 : r 2 = sem_bar (r 1)
  · exact Or.inr (Or.inr (Or.inr ⟨p12,remaining 1 2 0 (by decide) (by decide) (by decide) p12⟩))
  have flip (i j : Fin 3) (heq : r j = sem_bar (r i)) : r i = sem_bar (r j) := by
    rw [heq,bar_bar]
  have noPair (i j : Fin 3) (hne : j ≠ i) (heq : r j = sem_bar (r i)) : False := by
    fin_cases i <;> fin_cases j
    · exact hne rfl
    · exact p01 heq
    · exact p02 heq
    · exact p01 (flip _ _ heq)
    · exact hne rfl
    · exact p12 heq
    · exact p02 (flip _ _ heq)
    · exact p12 (flip _ _ heq)
    · exact hne rfl
  have all (i : Fin 3) : E i := by
    rcases cases i with he | ⟨j,hji,hj⟩
    · exact he
    · exact False.elim (noPair i j hji hj)
  exact Or.inl ⟨all 0,all 1,all 2⟩

lemma gate_eq_iff {a b : Nat × Bool} : a.1 = b.1 ↔ a = b ∨ a = sem_bar b := by
  rcases a with ⟨i,s⟩
  rcases b with ⟨j,t⟩
  cases s <;> cases t <;> simp [sem_bar]

lemma no_pair_gates_injective (r : Fin 3 → Nat × Bool) (inj : Function.Injective r)
    (noPair : ∀ i j : Fin 3, i ≠ j → r i ≠ sem_bar (r j)) :
    Function.Injective (fun i => (r i).1) := by
  intro i j heq
  rcases gate_eq_iff.mp heq with same | paired
  · exact inj same
  · by_contra hne
    exact noPair i j hne paired

lemma paired_gate_ne_third (r : Fin 3 → Nat × Bool) (inj : Function.Injective r)
    {i j k : Fin 3} (hki : k ≠ i) (hkj : k ≠ j)
    (pair : r j = sem_bar (r i)) : (r k).1 ≠ (r i).1 := by
  intro heq
  rcases gate_eq_iff.mp heq with same | paired
  · exact hki (inj same)
  · exact hkj (inj (paired.trans pair.symm))

end PEqualNP.Outside.L_meta_2590_aux.S50ThreeMatching


namespace PEqualNP.Outside.L_meta_2590_aux.S50ExtraMatching
open DagTools Four S50Private S50SplitT S50ExtraSeed S50ExtraPrivate S50ExtraCoverage

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 1000000 in
lemma pure_side_geometry : ∀ u b : V, b ∈ oppositeColor u →
    ({b} : Finset V) ≠ {0} ∧ ({b} : Finset V) ≠ {1,4,5} ∧
    ({b} : Finset V) ≠ ({1,4,5} : Finset V) ∪ color u ∧
    ({b} : Finset V) ≠ oppositeColor u ∧
    ∀ x : V, Adj 0 x → ({b} : Finset V) ≠ {x} ∧ ({b} : Finset V) ≠ {mate u x} := by
  unfold Adj edgeList
  decide +kernel

lemma pure_not_base {D : Dag} (e q : Nat × Bool) (f : V → Nat × Bool) (u : V)
    (epure : supp 10 D (src D e) = {0})
    (ebar : supp 10 D (src D (sem_bar e)) = ({1,4,5} : Finset V))
    (qsrc : supp 10 D (src D q) = ({1,4,5} : Finset V) ∪ color u)
    (qbar : supp 10 D (src D (sem_bar q)) = oppositeColor u)
    (fpure : ∀ x : V, Adj 0 x → supp 10 D (src D (f x)) = {x})
    (fbar : ∀ x : V, Adj 0 x → supp 10 D (src D (sem_bar (f x))) = {mate u x})
    {b : V} (hb : b ∈ oppositeColor u) {r : Nat × Bool}
    (rpure : supp 10 D (src D r) = {b}) : r ∉ baseArcs e q f := by
  obtain ⟨hn0,hnN,hnq,hnB,hnf⟩ := pure_side_geometry u b hb
  intro hm
  simp only [baseArcs,Finset.mem_insert,Finset.mem_singleton] at hm
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm
  · exact hn0 (by rw [← rpure,hm,epure])
  · exact hnN (by rw [← rpure,hm,ebar])
  · exact hnq (by rw [← rpure,hm,qsrc])
  · exact hnB (by rw [← rpure,hm,qbar])
  · exact (hnf 1 (by decide +kernel)).1 (by rw [← rpure,hm,fpure 1 (by decide +kernel)])
  · exact (hnf 1 (by decide +kernel)).2 (by rw [← rpure,hm,fbar 1 (by decide +kernel)])
  · exact (hnf 4 (by decide +kernel)).1 (by rw [← rpure,hm,fpure 4 (by decide +kernel)])
  · exact (hnf 4 (by decide +kernel)).2 (by rw [← rpure,hm,fbar 4 (by decide +kernel)])
  · exact (hnf 5 (by decide +kernel)).1 (by rw [← rpure,hm,fpure 5 (by decide +kernel)])
  · exact (hnf 5 (by decide +kernel)).2 (by rw [← rpure,hm,fbar 5 (by decide +kernel)])

def vertex (u : V) (i : Fin 3) : V :=
  if u ∈ ({3,6,7} : Finset V) then ([2,8,9] : List V).getD i.val 0
  else ([3,6,7] : List V).getD i.val 0

set_option maxRecDepth 100000 in
lemma vertices_geometry : ∀ u : V,
    Function.Injective (vertex u) ∧
    (∀ i : Fin 3, vertex u i ∈ oppositeColor u) ∧
    ∀ b ∈ oppositeColor u, ∃ i : Fin 3, vertex u i = b := by decide +kernel

lemma four_pairing_layouts {D : Dag} (h : Strict 10 D)
    (e q : Nat × Bool) (f r : V → Nat × Bool) (u : V)
    (epure : supp 10 D (src D e) = {0})
    (ebar : supp 10 D (src D (sem_bar e)) = ({1,4,5} : Finset V))
    (qsrc : supp 10 D (src D q) = ({1,4,5} : Finset V) ∪ color u)
    (qbar : supp 10 D (src D (sem_bar q)) = oppositeColor u)
    (fpure : ∀ x : V, Adj 0 x → supp 10 D (src D (f x)) = {x})
    (fbar : ∀ x : V, Adj 0 x → supp 10 D (src D (sem_bar (f x))) = {mate u x})
    (rpure : ∀ b ∈ oppositeColor u, supp 10 D (src D (r b)) = {b})
    (zero : sem_W 10 D 0 = {e})
    (cover : ∀ x : V, Adj 0 x → sem_W 10 D x = {sem_bar e,q,f x})
    (sourceSide : ∀ x ∈ color u, sem_W 10 D x = {q,sem_bar (f (owner x))})
    (oppositeSide : ∀ x ∈ oppositeColor u, sem_W 10 D x = {sem_bar q,r x})
    (empty : ∀ j : Nat, j < D.length → tag D j = true → supp 10 D (10+j) = ∅) :
    let a := fun i : Fin 3 => r (vertex u i)
    let E := fun i : Fin 3 => supp 10 D (src D (sem_bar (a i))) = ∅
    (E 0 ∧ E 1 ∧ E 2) ∨ (a 1 = sem_bar (a 0) ∧ E 2) ∨
      (a 2 = sem_bar (a 0) ∧ E 1) ∨ (a 2 = sem_bar (a 1) ∧ E 0) := by
  classical
  let B := oppositeColor u
  have membership (b : V) (hb : b ∈ B) : r b ∈ sem_W 10 D b := by
    rw [oppositeSide b hb]
    simp
  have matching := S50MateMatching.mate_empty_or_paired h B r (baseArcs e q f)
    (fun a ha => base_bar_closed e q f ha)
    (fun b hb => pure_not_base e q f u epure ebar qsrc qbar fpure fbar hb (rpure b hb))
    membership (fun x a ha => exit_arc_covered e q f r u zero cover sourceSide oppositeSide x a ha) empty
  obtain ⟨vinj,vmem,vsurj⟩ := vertices_geometry u
  let a := fun i : Fin 3 => r (vertex u i)
  have inj : Function.Injective a := by
    intro i j eq
    apply vinj
    exact S50MateMatching.pure_arcs_injective B r rpure (vmem i) (vmem j) eq
  apply S50ThreeMatching.three_pairings a inj (fun i => supp 10 D (src D (sem_bar (a i))) = ∅)
  intro i
  rcases matching (vertex u i) (vmem i) with he | ⟨b,hb,hne,hpair⟩
  · exact Or.inl he
  · obtain ⟨j,hj⟩ := vsurj b hb
    refine Or.inr ⟨j,?_,?_⟩
    · intro eq
      subst j
      exact hne hj.symm
    · simpa only [a,hj] using hpair

end PEqualNP.Outside.L_meta_2590_aux.S50ExtraMatching


namespace PEqualNP.Outside.L_meta_2590_aux.S50ExtraProfile
open DagTools Four S50Private S50SplitT S50ExtraSeed S50ExtraPrivate S50ExtraCoverage S50ExtraMatching

lemma extra_profile {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (hi : (0 : V) ∈ ineligSet 10 D)
    {e q : Nat × Bool} (f : V → Nat × Bool)
    (epure : supp 10 D (src D e) = {0})
    (ebar : supp 10 D (src D (sem_bar e)) = ({1,4,5} : Finset V))
    (zero : sem_W 10 D 0 = {e}) (eqne : e.1 ≠ q.1)
    (qout : supp 10 D (10+q.1) = ∅)
    (cover : ∀ x : V, Adj 0 x → sem_W 10 D x = {sem_bar e,q,f x})
    (pure : ∀ x : V, Adj 0 x → supp 10 D (src D (f x)) = {x})
    (two : ∀ y : V, y ≠ 0 → ¬ Adj 0 y → (sem_W 10 D y).card = 2)
    (empty : ∀ j : Nat, j < D.length → tag D j = true → supp 10 D (10+j) = ∅)
    {u : V} (hu0 : u ≠ 0) (huN : ¬ Adj 0 u) (huq : u ∈ supp 10 D (src D q)) :
    supp 10 D (src D q) = ({1,4,5} : Finset V) ∪ color u ∧
    supp 10 D (src D (sem_bar q)) = oppositeColor u ∧
    (∀ x : V, Adj 0 x → supp 10 D (src D (sem_bar (f x))) = {mate u x}) ∧
    ∃ r : V → Nat × Bool,
      (∀ b ∈ oppositeColor u, supp 10 D (src D (r b)) = {b}) ∧
      (∀ x ∈ color u, sem_W 10 D x = {q,sem_bar (f (owner x))}) ∧
      (∀ x ∈ oppositeColor u, sem_W 10 D x = {sem_bar q,r x}) ∧
      (∀ j, j < D.length → tag D j = true → j ∉ allGates e q f r u →
        supp 10 D (opA D j) = ∅ ∧ supp 10 D (opB D j) = ∅) ∧
      (let a := fun i : Fin 3 => r (vertex u i)
       let E := fun i : Fin 3 => supp 10 D (src D (sem_bar (a i))) = ∅
       (E 0 ∧ E 1 ∧ E 2) ∨ (a 1 = sem_bar (a 0) ∧ E 2) ∨
         (a 2 = sem_bar (a 0) ∧ E 1) ∨ (a 2 = sem_bar (a 1) ∧ E 0)) := by
  classical
  have small (y : V) (hy0 : y ≠ 0) (hyN : ¬ Adj 0 y) : (sem_W 10 D y).card ≤ 2 :=
    (two y hy0 hyN).le
  obtain ⟨qsrc,qbar⟩ := S50ExtraActual.extra_profile_colors h hc hi f epure zero eqne qout
    cover pure small hu0 huN huq
  have fbar := S50ExtraPrivate.private_mates_exact h hc hi f u epure qsrc qout cover small
  have sourceSide := S50ExtraPrivate.source_side_cover h hc f u epure qsrc qout cover small
  have opposite := S50ExtraOpposite.opposite_ports_pure h hc hi f u epure ebar zero qsrc qbar qout
    cover pure two empty
  let r : V → Nat × Bool := fun b =>
    if hb : b ∈ oppositeColor u then Classical.choose (opposite b hb) else q
  have chosen (b : V) (hb : b ∈ oppositeColor u) :
      r b ≠ sem_bar q ∧ sem_W 10 D b = {sem_bar q,r b} ∧ supp 10 D (src D (r b)) = {b} := by
    simpa only [r,dif_pos hb] using Classical.choose_spec (opposite b hb)
  have rpure (b : V) (hb : b ∈ oppositeColor u) : supp 10 D (src D (r b)) = {b} := (chosen b hb).2.2
  have oppositeSide (b : V) (hb : b ∈ oppositeColor u) : sem_W 10 D b = {sem_bar q,r b} := (chosen b hb).2.1
  refine ⟨qsrc,qbar,fbar,r,rpure,sourceSide,oppositeSide,?_,?_⟩
  · intro j hj ht hn
    exact noncanonical_and_empty e q f r u zero cover sourceSide oppositeSide empty hj ht hn
  · exact four_pairing_layouts h.1 e q f r u epure ebar qsrc qbar pure fbar rpure
      zero cover sourceSide oppositeSide empty

end PEqualNP.Outside.L_meta_2590_aux.S50ExtraProfile


namespace PEqualNP.Outside.L_meta_2590_aux.S50SplitTyped
open DagTools Four S50Private S50SplitT S50SplitPorts S50SplitDistinct

def arcs (e q a : Nat × Bool) (f : V → Nat × Bool) (i : Fin 6) : Nat × Bool :=
  ([e,q,f 1,f 4,f 5,a] : List (Nat × Bool)).getD i.val e

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 1000000 in
lemma private_geometry :
    (∀ y : V, (y ≠ 0 ∧ ¬ Adj 0 y ∧ Adj 1 y) ↔ y ∈ ({2,6} : Finset V)) ∧
    (∀ y : V, (y ≠ 0 ∧ ¬ Adj 0 y ∧ Adj 4 y) ↔ y ∈ ({3,9} : Finset V)) ∧
    (∀ y : V, (y ≠ 0 ∧ ¬ Adj 0 y ∧ Adj 5 y) ↔ y ∈ ({7,8} : Finset V)) := by
  unfold Adj edgeList
  decide +kernel

lemma canonical_iff (e q a : Nat × Bool) (f : V → Nat × Bool) (j : Nat) :
    j ∈ S50SplitCoverage.canonical e q a f ↔ ∃ i : Fin 6, (arcs e q a f i).1 = j := by
  constructor
  · intro hj
    simp only [S50SplitCoverage.canonical,Finset.mem_insert,Finset.mem_singleton] at hj
    rcases hj with hj | hj | hj | hj | hj | hj
    · exact ⟨0,by simpa [arcs] using hj.symm⟩
    · exact ⟨1,by simpa [arcs] using hj.symm⟩
    · exact ⟨2,by simpa [arcs] using hj.symm⟩
    · exact ⟨3,by simpa [arcs] using hj.symm⟩
    · exact ⟨4,by simpa [arcs] using hj.symm⟩
    · exact ⟨5,by simpa [arcs] using hj.symm⟩
  · rintro ⟨i,rfl⟩
    fin_cases i <;> simp [arcs,S50SplitCoverage.canonical]

lemma typed_six_gates {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    {e q : Nat × Bool} (f : V → Nat × Bool)
    (epure : supp 10 D (src D e) = {0})
    (ebar : supp 10 D (src D (sem_bar e)) = ({1,4,5} : Finset V))
    (zero : sem_W 10 D 0 = {e}) (eqne : e.1 ≠ q.1)
    (qsrc : supp 10 D (src D q) = ({1,4,5} : Finset V))
    (qout : supp 10 D (10+q.1) = ∅)
    (cover : ∀ x : V, Adj 0 x → sem_W 10 D x = {sem_bar e,q,f x})
    (pure : ∀ x : V, Adj 0 x → supp 10 D (src D (f x)) = {x})
    (ne : ∀ x : V, Adj 0 x → f x ≠ sem_bar e)
    (small : ∀ y : V, y ≠ 0 → ¬ Adj 0 y → (sem_W 10 D y).card ≤ 2)
    (empty : ∀ j : Nat, j < D.length → tag D j = true → supp 10 D (10+j) = ∅) :
    ∃ T ∈ allowed, ∃ r : Fin 6 → Nat × Bool,
      Function.Injective (fun i => (r i).1) ∧
      (∀ i, (r i).1 < D.length ∧ tag D (r i).1 = true) ∧
      (∀ i, supp 10 D (src D (r i)) = sideA i) ∧
      (∀ i, supp 10 D (src D (sem_bar (r i))) = sideB T i) ∧
      ∀ j : Nat, j < D.length → tag D j = true → (∀ i, (r i).1 ≠ j) →
        supp 10 D (opA D j) = ∅ ∧ supp 10 D (opB D j) = ∅ := by
  classical
  let T := supp 10 D (src D (sem_bar q))
  obtain ⟨allowedT,a,asrc,bsrc,outside,mates⟩ :=
    S50SplitActual.split_profile h hc f epure ebar zero eqne qsrc qout cover pure ne small empty
  change T ∈ allowed at allowedT
  have pair1 : supp 10 D (src D (sem_bar (f 1))) = ({2,6} : Finset V) \ T := by
    ext y
    rw [mates 1 (by decide +kernel)]
    simp only [Finset.mem_sdiff,← private_geometry.1 y]
    tauto
  have pair4 : supp 10 D (src D (sem_bar (f 4))) = ({3,9} : Finset V) \ T := by
    ext y
    rw [mates 4 (by decide +kernel)]
    simp only [Finset.mem_sdiff,← private_geometry.2.1 y]
    tauto
  have pair5 : supp 10 D (src D (sem_bar (f 5))) = ({7,8} : Finset V) \ T := by
    ext y
    rw [mates 5 (by decide +kernel)]
    simp only [Finset.mem_sdiff,← private_geometry.2.2 y]
    tauto
  let r := arcs e q a f
  have left (i : Fin 6) : supp 10 D (src D (r i)) = sideA i := by
    fin_cases i
    · simpa [r,arcs,sideA] using epure
    · simpa [r,arcs,sideA] using qsrc
    · simpa [r,arcs,sideA] using pure 1 (by decide +kernel)
    · simpa [r,arcs,sideA] using pure 4 (by decide +kernel)
    · simpa [r,arcs,sideA] using pure 5 (by decide +kernel)
    · simpa [r,arcs,sideA] using asrc
  have right (i : Fin 6) : supp 10 D (src D (sem_bar (r i))) = sideB T i := by
    fin_cases i
    · simpa [r,arcs,sideB] using ebar
    · rfl
    · simpa [r,arcs,sideB] using pair1
    · simpa [r,arcs,sideB] using pair4
    · simpa [r,arcs,sideB] using pair5
    · simpa [r,arcs,sideB] using bsrc
  have member (i : Fin 6) : ∃ x : V, r i ∈ sem_W 10 D x := by
    have he : e ∈ sem_W 10 D 0 := by rw [zero]; simp
    have hq : q ∈ sem_W 10 D 1 := by rw [cover 1 (by decide +kernel)]; simp
    have hf (x : V) (hx : Adj 0 x) : f x ∈ sem_W 10 D x := by rw [cover x hx]; simp
    have ha : a ∈ sem_W 10 D 3 := by
      rw [outside 3 (by decide +kernel)]
      simp
    fin_cases i
    · exact ⟨0,by simpa [r,arcs] using he⟩
    · exact ⟨1,by simpa [r,arcs] using hq⟩
    · exact ⟨1,by simpa [r,arcs] using hf 1 (by decide +kernel)⟩
    · exact ⟨4,by simpa [r,arcs] using hf 4 (by decide +kernel)⟩
    · exact ⟨5,by simpa [r,arcs] using hf 5 (by decide +kernel)⟩
    · exact ⟨3,by simpa [r,arcs] using ha⟩
  refine ⟨T,allowedT,r,gate_injective T allowedT r left right,?_,left,right,?_⟩
  · intro i
    obtain ⟨x,hx⟩ := member i
    exact ⟨(sem_mem_W.mp hx).1,sem_W_and h.1 hx⟩
  · intro j hj ht hn
    apply S50SplitCoverage.noncanonical_and_empty e q a f T zero cover outside empty hj ht
    intro hm
    obtain ⟨i,hi⟩ := (canonical_iff e q a f j).mp hm
    exact hn i hi

end PEqualNP.Outside.L_meta_2590_aux.S50SplitTyped


namespace PEqualNP.Outside.L_meta_2590_aux.S50Normalize
open DagTools Four SharedDom

lemma normalized_ports_of_common {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (zero : Bzero 10 D = 0) (hi : (0 : V) ∈ ineligSet 10 D)
    (budget : Bplus 10 D = (eligSet 10 D).card + 1)
    (sat : ∀ x : V, Adj 0 x → (sem_W 10 D x).card = 3)
    {P Q : Nat × Bool} (hpq : P.1 ≠ Q.1)
    (common : ∀ x : V, Adj 0 x → P ∈ sem_W 10 D x ∧ Q ∈ sem_W 10 D x) :
    ∃ e q : Nat × Bool, ∃ f : V → Nat × Bool,
      supp 10 D (src D e) = ({0} : Finset V) ∧
      supp 10 D (src D (sem_bar e)) = ({1,4,5} : Finset V) ∧
      sem_W 10 D 0 = {e} ∧ e.1 ≠ q.1 ∧ supp 10 D (10+q.1) = ∅ ∧
      (∀ x : V, Adj 0 x → sem_W 10 D x = {sem_bar e,q,f x}) ∧
      (∀ x : V, Adj 0 x → supp 10 D (src D (f x)) = {x}) ∧
      (∀ x : V, Adj 0 x → f x ≠ sem_bar e) ∧
      (∀ y : V, y ≠ 0 → ¬ Adj 0 y → (sem_W 10 D y).card = 2) ∧
      (∀ j : Nat, j < D.length → tag D j = true → supp 10 D (10+j) = ∅) := by
  classical
  obtain ⟨_,two,empty⟩ := case50_no_singleton_merges_of_common h hc zero hi budget sat hpq common
  obtain ⟨e,q,ev,et,epure,ebar,eout,eqne,qmem,ports⟩ :=
    case50_budget_ports_of_common h hc zero hi budget sat hpq common
  have emem : e ∈ sem_W 10 D (0 : V) := by
    apply sem_mem_W.mpr
    refine ⟨ev,?_,?_⟩
    · rw [epure]
      simp
    · rw [eout]
      simp
  obtain ⟨s,_,_,_,_,_,starW,_,_⟩ := budget_one_first_zero_star h hc zero hi budget
  change sem_W 10 D (0 : V) = {s} at starW
  have es : e = s := by rw [starW,Finset.mem_singleton] at emem; exact emem
  have eW : sem_W 10 D (0 : V) = {e} := by simpa only [es] using starW
  let f : V → Nat × Bool := fun x =>
    if hx : Adj 0 x then Classical.choose (ports x hx) else e
  have choice (x : V) (hx : Adj 0 x) :
      sem_W 10 D x = {sem_bar e,q,f x} ∧ f x ≠ sem_bar e ∧ f x ≠ q ∧
        supp 10 D (src D (f x)) = {x} := by
    simpa only [f,dif_pos hx] using Classical.choose_spec (ports x hx)
  have qx := qmem 1 (by decide +kernel)
  have qout := empty q.1 (sem_mem_W.mp qx).1 (sem_W_and h.1 qx)
  exact ⟨e,q,f,epure,ebar,eW,eqne,qout,
    fun x hx => (choice x hx).1,
    fun x hx => (choice x hx).2.2.2,
    fun x hx => (choice x hx).2.1,two,empty⟩

lemma common_source_cases {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 Adj D)
    (hi : (0 : V) ∈ ineligSet 10 D) (q : Nat × Bool)
    (common : ∀ x : V, Adj 0 x → q ∈ sem_W 10 D x) :
    supp 10 D (src D q) = ({1,4,5} : Finset V) ∨
      ∃ u : V, u ≠ 0 ∧ ¬ Adj 0 u ∧ u ∈ supp 10 D (src D q) := by
  classical
  have lower : ({1,4,5} : Finset V) ⊆ supp 10 D (src D q) := by
    intro x hx
    exact (sem_mem_W.mp (common x ((I1Exposure.zero_neighbors x).mpr hx))).2.1
  by_cases eq : supp 10 D (src D q) = ({1,4,5} : Finset V)
  · exact Or.inl eq
  · right
    have notsub : ¬ supp 10 D (src D q) ⊆ ({1,4,5} : Finset V) :=
      fun sub => eq (Finset.Subset.antisymm sub lower)
    obtain ⟨u,hu,hn⟩ := Finset.not_subset.mp notsub
    have hu0 : u ≠ 0 := by
      intro huEq
      subst u
      have hp := sem_inelig_pure graph_ok h.1 hc hi hu
      have hone := lower (show (1 : V) ∈ ({1,4,5} : Finset V) by decide)
      rw [hp,Finset.mem_singleton] at hone
      exact (by decide : (1 : V) ≠ 0) hone
    exact ⟨u,hu0,fun hx => hn ((I1Exposure.zero_neighbors u).mp hx),hu⟩

end PEqualNP.Outside.L_meta_2590_aux.S50Normalize


namespace PEqualNP.Outside.L_meta_2590_aux.S50ExtraDistinct
open DagTools Four S50Private S50ExtraSeed S50ExtraPrivate S50ExtraCoverage

def baseRep (e q : Nat × Bool) (f : V → Nat × Bool) (i : Fin 5) : Nat × Bool :=
  ([e,q,f 1,f 4,f 5] : List (Nat × Bool)).getD i.val e

def sideA (u : V) (i : Fin 5) : Finset V :=
  ([{0},({1,4,5} : Finset V) ∪ color u,{1},{4},{5}] : List (Finset V)).getD i.val ∅

def sideB (u : V) (i : Fin 5) : Finset V :=
  ([{1,4,5},oppositeColor u,{mate u 1},{mate u 4},{mate u 5}] : List (Finset V)).getD i.val ∅

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 1000000 in
lemma distinct_profiles : ∀ u : V, ∀ i j : Fin 5, i ≠ j →
    sideA u i ≠ sideA u j ∧
      (sideA u i ≠ sideB u j ∨ sideB u i ≠ sideA u j) := by decide +kernel

lemma gate_injective {D : Dag} (u : V) (r : Fin 5 → Nat × Bool)
    (left : ∀ i, supp 10 D (src D (r i)) = sideA u i)
    (right : ∀ i, supp 10 D (src D (sem_bar (r i))) = sideB u i) :
    Function.Injective (fun i => (r i).1) := by
  intro i j eq
  by_contra hij
  obtain ⟨hnormal,hreverse⟩ := distinct_profiles u i j hij
  rcases S50SplitDistinct.same_gate_arc_cases (r i) (r j) eq with hs | hs
  · exact hnormal (by rw [← left i,hs,left j])
  · have hA : sideA u i = sideB u j := by rw [← left i,hs,right j]
    have hB : sideB u i = sideA u j := by rw [← right i,hs,bar_bar,left j]
    rcases hreverse with hn | hn
    · exact hn hA
    · exact hn hB

lemma baseRep_mem (e q : Nat × Bool) (f : V → Nat × Bool) (i : Fin 5) :
    baseRep e q f i ∈ baseArcs e q f := by
  fin_cases i <;> simp [baseRep,baseArcs]

lemma actual_base_injective {D : Dag} (e q : Nat × Bool) (f : V → Nat × Bool) (u : V)
    (epure : supp 10 D (src D e) = {0})
    (ebar : supp 10 D (src D (sem_bar e)) = ({1,4,5} : Finset V))
    (qsrc : supp 10 D (src D q) = ({1,4,5} : Finset V) ∪ color u)
    (qbar : supp 10 D (src D (sem_bar q)) = oppositeColor u)
    (fpure : ∀ x : V, Adj 0 x → supp 10 D (src D (f x)) = {x})
    (fbar : ∀ x : V, Adj 0 x → supp 10 D (src D (sem_bar (f x))) = {mate u x}) :
    Function.Injective (fun i : Fin 5 => (baseRep e q f i).1) := by
  apply gate_injective u (baseRep e q f)
  · intro i
    fin_cases i
    · simpa [baseRep,sideA] using epure
    · simpa [baseRep,sideA] using qsrc
    · simpa [baseRep,sideA] using fpure 1 (by decide +kernel)
    · simpa [baseRep,sideA] using fpure 4 (by decide +kernel)
    · simpa [baseRep,sideA] using fpure 5 (by decide +kernel)
  · intro i
    fin_cases i
    · simpa [baseRep,sideB] using ebar
    · simpa [baseRep,sideB] using qbar
    · simpa [baseRep,sideB] using fbar 1 (by decide +kernel)
    · simpa [baseRep,sideB] using fbar 4 (by decide +kernel)
    · simpa [baseRep,sideB] using fbar 5 (by decide +kernel)

lemma pure_gate_not_base {D : Dag} (e q : Nat × Bool) (f : V → Nat × Bool) (u : V)
    (epure : supp 10 D (src D e) = {0})
    (ebar : supp 10 D (src D (sem_bar e)) = ({1,4,5} : Finset V))
    (qsrc : supp 10 D (src D q) = ({1,4,5} : Finset V) ∪ color u)
    (qbar : supp 10 D (src D (sem_bar q)) = oppositeColor u)
    (fpure : ∀ x : V, Adj 0 x → supp 10 D (src D (f x)) = {x})
    (fbar : ∀ x : V, Adj 0 x → supp 10 D (src D (sem_bar (f x))) = {mate u x})
    {b : V} (hb : b ∈ oppositeColor u) {r : Nat × Bool}
    (rpure : supp 10 D (src D r) = {b}) :
    ∀ i : Fin 5, r.1 ≠ (baseRep e q f i).1 := by
  have hnot := S50ExtraMatching.pure_not_base e q f u epure ebar qsrc qbar fpure fbar hb rpure
  intro i heq
  rcases S50SplitDistinct.same_gate_arc_cases r (baseRep e q f i) heq with he | he
  · apply hnot
    rw [he]
    exact baseRep_mem e q f i
  · apply hnot
    rw [he]
    exact base_bar_closed e q f (baseRep_mem e q f i)

end PEqualNP.Outside.L_meta_2590_aux.S50ExtraDistinct


namespace PEqualNP.Outside.L_meta_2590_aux.S50ExtraTyped7
open DagTools Four S50Private S50SplitT S50ExtraSeed S50ExtraPrivate S50ExtraCoverage
open S50ExtraMatching S50ExtraDistinct S50ThreeMatching

def leafRep (r : V → Nat × Bool) (u : V) (i k : Fin 3) (l : Fin 2) : Nat × Bool :=
  if l = 0 then r (vertex u i) else r (vertex u k)

def reps (e q : Nat × Bool) (f r : V → Nat × Bool) (u : V) (i k : Fin 3) : Fin 7 → Nat × Bool :=
  Fin.append (baseRep e q f) (leafRep r u i k)

def left (u : V) (i k : Fin 3) : Fin 7 → Finset V :=
  Fin.append (sideA u) (fun l : Fin 2 => if l = 0 then {vertex u i} else {vertex u k})

def right (u : V) (j : Fin 3) : Fin 7 → Finset V :=
  Fin.append (sideB u) (fun l : Fin 2 => if l = 0 then {vertex u j} else ∅)

lemma base_gate_represented (e q : Nat × Bool) (f : V → Nat × Bool)
    {a : Nat × Bool} (ha : a ∈ baseArcs e q f) :
    ∃ i : Fin 5, (baseRep e q f i).1 = a.1 := by
  simp only [baseArcs,Finset.mem_insert,Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0,rfl⟩
  · exact ⟨0,rfl⟩
  · exact ⟨1,rfl⟩
  · exact ⟨1,rfl⟩
  · exact ⟨2,rfl⟩
  · exact ⟨2,rfl⟩
  · exact ⟨3,rfl⟩
  · exact ⟨3,rfl⟩
  · exact ⟨4,rfl⟩
  · exact ⟨4,rfl⟩

lemma typed_seven_gates {D : Dag} (h : Strict 10 D)
    (e q : Nat × Bool) (f r : V → Nat × Bool) (u : V)
    (epure : supp 10 D (src D e) = {0})
    (ebar : supp 10 D (src D (sem_bar e)) = ({1,4,5} : Finset V))
    (qsrc : supp 10 D (src D q) = ({1,4,5} : Finset V) ∪ color u)
    (qbar : supp 10 D (src D (sem_bar q)) = oppositeColor u)
    (fpure : ∀ x : V, Adj 0 x → supp 10 D (src D (f x)) = {x})
    (fbar : ∀ x : V, Adj 0 x → supp 10 D (src D (sem_bar (f x))) = {mate u x})
    (rpure : ∀ b ∈ oppositeColor u, supp 10 D (src D (r b)) = {b})
    (zero : sem_W 10 D 0 = {e})
    (cover : ∀ x : V, Adj 0 x → sem_W 10 D x = {sem_bar e,q,f x})
    (sourceSide : ∀ x ∈ color u, sem_W 10 D x = {q,sem_bar (f (owner x))})
    (oppositeSide : ∀ x ∈ oppositeColor u, sem_W 10 D x = {sem_bar q,r x})
    (empty : ∀ j : Nat, j < D.length → tag D j = true → supp 10 D (10+j) = ∅)
    (i j k : Fin 3) (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (pair : r (vertex u j) = sem_bar (r (vertex u i)))
    (third : supp 10 D (src D (sem_bar (r (vertex u k)))) = ∅) :
    Function.Injective (fun l : Fin 7 => (reps e q f r u i k l).1) ∧
    (∀ l : Fin 7, (reps e q f r u i k l).1 < D.length ∧ tag D (reps e q f r u i k l).1 = true) ∧
    (∀ l : Fin 7, supp 10 D (src D (reps e q f r u i k l)) = left u i k l) ∧
    (∀ l : Fin 7, supp 10 D (src D (sem_bar (reps e q f r u i k l))) = right u j l) ∧
    (∀ g : Nat, g < D.length → tag D g = true →
      (∀ l : Fin 7, (reps e q f r u i k l).1 ≠ g) →
      supp 10 D (opA D g) = ∅ ∧ supp 10 D (opB D g) = ∅) := by
  classical
  obtain ⟨vinj,vmem,vsurj⟩ := vertices_geometry u
  have rinj : Function.Injective (fun l : Fin 3 => r (vertex u l)) := by
    intro a b eq
    apply vinj
    exact S50MateMatching.pure_arcs_injective (oppositeColor u) r rpure (vmem a) (vmem b) eq
  have kine : (r (vertex u k)).1 ≠ (r (vertex u i)).1 :=
    paired_gate_ne_third (fun l => r (vertex u l)) rinj hki hkj pair
  have leafinj : Function.Injective (fun l : Fin 2 => (leafRep r u i k l).1) := by
    intro a b eq
    fin_cases a <;> fin_cases b
    · rfl
    · exact False.elim (kine (by simpa [leafRep] using eq.symm))
    · exact False.elim (kine (by simpa [leafRep] using eq))
    · rfl
  have baseinj := actual_base_injective e q f u epure ebar qsrc qbar fpure fbar
  have disjoint (a : Fin 5) (b : Fin 2) : (baseRep e q f a).1 ≠ (leafRep r u i k b).1 := by
    fin_cases b
    · exact Ne.symm (pure_gate_not_base e q f u epure ebar qsrc qbar fpure fbar (vmem i) (rpure _ (vmem i)) a)
    · exact Ne.symm (pure_gate_not_base e q f u epure ebar qsrc qbar fpure fbar (vmem k) (rpure _ (vmem k)) a)
  have funEq : (fun l : Fin 7 => (reps e q f r u i k l).1) =
      Fin.append (fun l => (baseRep e q f l).1) (fun l => (leafRep r u i k l).1) := by
    funext l
    cases l using (Fin.addCases (m := 5) (n := 2)) <;> simp [reps]
  have inj : Function.Injective (fun l : Fin 7 => (reps e q f r u i k l).1) := by
    rw [funEq,Fin.append_injective_iff]
    exact ⟨baseinj,leafinj,disjoint⟩
  have emem : e ∈ sem_W 10 D (0 : V) := by rw [zero]; simp
  have qmem : q ∈ sem_W 10 D (1 : V) := by rw [cover 1 (by decide +kernel)]; simp
  have fmem (x : V) (hx : Adj 0 x) : f x ∈ sem_W 10 D x := by rw [cover x hx]; simp
  have rmem (l : Fin 3) : r (vertex u l) ∈ sem_W 10 D (vertex u l) := by rw [oppositeSide _ (vmem l)]; simp
  have valid {x : V} {a : Nat × Bool} (ha : a ∈ sem_W 10 D x) : a.1 < D.length ∧ tag D a.1 = true :=
    ⟨(sem_mem_W.mp ha).1,sem_W_and h ha⟩
  have baseValid (l : Fin 5) : (baseRep e q f l).1 < D.length ∧ tag D (baseRep e q f l).1 = true := by
    fin_cases l
    · exact valid emem
    · exact valid qmem
    · exact valid (fmem 1 (by decide +kernel))
    · exact valid (fmem 4 (by decide +kernel))
    · exact valid (fmem 5 (by decide +kernel))
  have baseLeft (l : Fin 5) : supp 10 D (src D (baseRep e q f l)) = sideA u l := by
    fin_cases l
    · simpa [baseRep,sideA] using epure
    · simpa [baseRep,sideA] using qsrc
    · simpa [baseRep,sideA] using fpure 1 (by decide +kernel)
    · simpa [baseRep,sideA] using fpure 4 (by decide +kernel)
    · simpa [baseRep,sideA] using fpure 5 (by decide +kernel)
  have baseRight (l : Fin 5) : supp 10 D (src D (sem_bar (baseRep e q f l))) = sideB u l := by
    fin_cases l
    · simpa [baseRep,sideB] using ebar
    · simpa [baseRep,sideB] using qbar
    · simpa [baseRep,sideB] using fbar 1 (by decide +kernel)
    · simpa [baseRep,sideB] using fbar 4 (by decide +kernel)
    · simpa [baseRep,sideB] using fbar 5 (by decide +kernel)
  refine ⟨inj,?_,?_,?_,?_⟩
  · intro l
    cases l using (Fin.addCases (m := 5) (n := 2)) with
    | left a => simpa [reps] using baseValid a
    | right b =>
      fin_cases b
      · change (r (vertex u i)).1 < D.length ∧ tag D (r (vertex u i)).1 = true
        exact valid (rmem i)
      · change (r (vertex u k)).1 < D.length ∧ tag D (r (vertex u k)).1 = true
        exact valid (rmem k)
  · intro l
    cases l using (Fin.addCases (m := 5) (n := 2)) with
    | left a => simpa [reps,left] using baseLeft a
    | right b =>
      fin_cases b
      · change supp 10 D (src D (r (vertex u i))) = {vertex u i}
        exact rpure _ (vmem i)
      · change supp 10 D (src D (r (vertex u k))) = {vertex u k}
        exact rpure _ (vmem k)
  · intro l
    cases l using (Fin.addCases (m := 5) (n := 2)) with
    | left a => simpa [reps,right] using baseRight a
    | right b =>
      fin_cases b
      · change supp 10 D (src D (sem_bar (r (vertex u i)))) = {vertex u j}
        rw [← pair]
        exact rpure _ (vmem j)
      · change supp 10 D (src D (sem_bar (r (vertex u k)))) = ∅
        exact third
  · intro g hg ht hn
    apply noncanonical_and_empty e q f r u zero cover sourceSide oppositeSide empty hg ht
    intro hm
    obtain ⟨a,ha,hag⟩ := Finset.mem_image.mp hm
    rcases Finset.mem_union.mp ha with hbase | hrange
    · obtain ⟨b,hb⟩ := base_gate_represented e q f hbase
      apply hn (Fin.castAdd 2 b)
      simpa [reps] using hb.trans hag
    · obtain ⟨b,hb,hba⟩ := Finset.mem_image.mp hrange
      obtain ⟨l,hl⟩ := vsurj b hb
      have eq : (r (vertex u l)).1 = g := by rw [hl,hba]; exact hag
      rcases three_indices i j k hij hki hkj l with hli | hlj | hlk
      · subst l
        apply hn (Fin.natAdd 5 (0 : Fin 2))
        change (r (vertex u i)).1 = g
        exact eq
      · subst l
        apply hn (Fin.natAdd 5 (0 : Fin 2))
        have he := congrArg Prod.fst pair
        have eq' : (r (vertex u i)).1 = g := he.symm.trans eq
        change (r (vertex u i)).1 = g
        exact eq'
      · subst l
        apply hn (Fin.natAdd 5 (1 : Fin 2))
        change (r (vertex u k)).1 = g
        exact eq

end PEqualNP.Outside.L_meta_2590_aux.S50ExtraTyped7


namespace PEqualNP.Outside.L_meta_2590_aux.S50ExtraTyped8
open DagTools Four S50Private S50SplitT S50ExtraSeed S50ExtraPrivate
open S50ExtraCoverage S50ExtraMatching S50ExtraDistinct

def arcs (e q : Nat × Bool) (f r : V → Nat × Bool) (u : V) : Fin 8 → Nat × Bool :=
  Fin.append (baseRep e q f) (fun i : Fin 3 => r (vertex u i))

def sideA (u : V) : Fin 8 → Finset V :=
  Fin.append (S50ExtraDistinct.sideA u) (fun i : Fin 3 => {vertex u i})

def sideB (u : V) : Fin 8 → Finset V :=
  Fin.append (S50ExtraDistinct.sideB u) (fun _ : Fin 3 => ∅)

lemma all_gates_covered (e q : Nat × Bool) (f r : V → Nat × Bool) (u : V) :
    ∀ j ∈ allGates e q f r u, ∃ i : Fin 8, (arcs e q f r u i).1 = j := by
  have base (i : Fin 5) : ∃ k : Fin 8,
      (arcs e q f r u k).1 = (baseRep e q f i).1 :=
    ⟨Fin.castAdd 3 i,by simp [arcs]⟩
  have leaf (i : Fin 3) : ∃ k : Fin 8,
      (arcs e q f r u k).1 = (r (vertex u i)).1 :=
    ⟨Fin.natAdd 5 i,by simp [arcs]⟩
  intro j hj
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hj
  rcases Finset.mem_union.mp ha with ha | ha
  · simp only [baseArcs,Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [baseRep] using base 0
    · simpa [baseRep,sem_bar] using base 0
    · simpa [baseRep] using base 1
    · simpa [baseRep,sem_bar] using base 1
    · simpa [baseRep] using base 2
    · simpa [baseRep,sem_bar] using base 2
    · simpa [baseRep] using base 3
    · simpa [baseRep,sem_bar] using base 3
    · simpa [baseRep] using base 4
    · simpa [baseRep,sem_bar] using base 4
  · obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨i,hi⟩ := (vertices_geometry u).2.2 b hb
    simpa only [hi] using leaf i

lemma typed_eight_gates {D : Dag} (h : Strict 10 D)
    (e q : Nat × Bool) (f r : V → Nat × Bool) (u : V)
    (epure : supp 10 D (src D e) = {0})
    (ebar : supp 10 D (src D (sem_bar e)) = ({1,4,5} : Finset V))
    (qsrc : supp 10 D (src D q) = ({1,4,5} : Finset V) ∪ color u)
    (qbar : supp 10 D (src D (sem_bar q)) = oppositeColor u)
    (fpure : ∀ x : V, Adj 0 x → supp 10 D (src D (f x)) = {x})
    (fbar : ∀ x : V, Adj 0 x → supp 10 D (src D (sem_bar (f x))) = {mate u x})
    (rpure : ∀ b ∈ oppositeColor u, supp 10 D (src D (r b)) = {b})
    (rempty : ∀ i : Fin 3, supp 10 D (src D (sem_bar (r (vertex u i)))) = ∅)
    (zero : sem_W 10 D 0 = {e})
    (cover : ∀ x : V, Adj 0 x → sem_W 10 D x = {sem_bar e,q,f x})
    (sourceSide : ∀ x ∈ color u, sem_W 10 D x = {q,sem_bar (f (owner x))})
    (oppositeSide : ∀ x ∈ oppositeColor u, sem_W 10 D x = {sem_bar q,r x})
    (empty : ∀ j : Nat, j < D.length → tag D j = true → supp 10 D (10+j) = ∅) :
    let g := arcs e q f r u
    Function.Injective (fun i => (g i).1) ∧
      (∀ i, (g i).1 < D.length ∧ tag D (g i).1 = true) ∧
      (∀ i, supp 10 D (src D (g i)) = sideA u i) ∧
      (∀ i, supp 10 D (src D (sem_bar (g i))) = sideB u i) ∧
      ∀ j : Nat, j < D.length → tag D j = true → (∀ i, (g i).1 ≠ j) →
        supp 10 D (opA D j) = ∅ ∧ supp 10 D (opB D j) = ∅ := by
  classical
  let a := fun i : Fin 3 => r (vertex u i)
  let g := arcs e q f r u
  obtain ⟨vinj,vmem,_⟩ := vertices_geometry u
  have ainj : Function.Injective a := by
    intro i j eq
    apply vinj
    exact S50MateMatching.pure_arcs_injective (oppositeColor u) r rpure (vmem i) (vmem j) eq
  have noPair (i j : Fin 3) (_hne : i ≠ j) : a i ≠ sem_bar (a j) := by
    intro eq
    have hx : vertex u i ∈ supp 10 D (src D (a i)) := by rw [rpure _ (vmem i)]; simp
    rw [eq,rempty j] at hx
    exact Finset.notMem_empty _ hx
  have leafinj := S50ThreeMatching.no_pair_gates_injective a ainj noPair
  have baseinj := actual_base_injective e q f u epure ebar qsrc qbar fpure fbar
  have cross (i : Fin 5) (j : Fin 3) : (baseRep e q f i).1 ≠ (a j).1 :=
    Ne.symm (pure_gate_not_base e q f u epure ebar qsrc qbar fpure fbar
      (vmem j) (rpure _ (vmem j)) i)
  have mapped : (fun i : Fin 8 => (g i).1) =
      Fin.append (fun i : Fin 5 => (baseRep e q f i).1) (fun i : Fin 3 => (a i).1) := by
    funext i
    cases i using (Fin.addCases (m := 5) (n := 3)) <;> simp [g,arcs,a]
  have ginj : Function.Injective (fun i : Fin 8 => (g i).1) := by
    rw [mapped]
    exact Fin.append_injective_iff.mpr ⟨baseinj,leafinj,cross⟩
  have leftBase (i : Fin 5) : supp 10 D (src D (baseRep e q f i)) = S50ExtraDistinct.sideA u i := by
    fin_cases i
    · simpa [baseRep,S50ExtraDistinct.sideA] using epure
    · simpa [baseRep,S50ExtraDistinct.sideA] using qsrc
    · simpa [baseRep,S50ExtraDistinct.sideA] using fpure 1 (by decide +kernel)
    · simpa [baseRep,S50ExtraDistinct.sideA] using fpure 4 (by decide +kernel)
    · simpa [baseRep,S50ExtraDistinct.sideA] using fpure 5 (by decide +kernel)
  have rightBase (i : Fin 5) : supp 10 D (src D (sem_bar (baseRep e q f i))) = S50ExtraDistinct.sideB u i := by
    fin_cases i
    · simpa [baseRep,S50ExtraDistinct.sideB] using ebar
    · simpa [baseRep,S50ExtraDistinct.sideB] using qbar
    · simpa [baseRep,S50ExtraDistinct.sideB] using fbar 1 (by decide +kernel)
    · simpa [baseRep,S50ExtraDistinct.sideB] using fbar 4 (by decide +kernel)
    · simpa [baseRep,S50ExtraDistinct.sideB] using fbar 5 (by decide +kernel)
  have baseMember (i : Fin 5) : ∃ x : V, baseRep e q f i ∈ sem_W 10 D x := by
    have he : e ∈ sem_W 10 D 0 := by rw [zero]; simp
    have hq : q ∈ sem_W 10 D 1 := by rw [cover 1 (by decide +kernel)]; simp
    have hf (x : V) (hx : Adj 0 x) : f x ∈ sem_W 10 D x := by rw [cover x hx]; simp
    fin_cases i
    · exact ⟨0,by simpa [baseRep] using he⟩
    · exact ⟨1,by simpa [baseRep] using hq⟩
    · exact ⟨1,by simpa [baseRep] using hf 1 (by decide +kernel)⟩
    · exact ⟨4,by simpa [baseRep] using hf 4 (by decide +kernel)⟩
    · exact ⟨5,by simpa [baseRep] using hf 5 (by decide +kernel)⟩
  have members (i : Fin 8) : ∃ x : V, g i ∈ sem_W 10 D x := by
    cases i using (Fin.addCases (m := 5) (n := 3)) with
    | left i => simpa [g,arcs] using baseMember i
    | right i =>
        refine ⟨vertex u i,?_⟩
        simp only [g,arcs,Fin.append_right]
        rw [oppositeSide _ (vmem i)]
        simp
  refine ⟨ginj,?_,?_,?_,?_⟩
  · intro i
    obtain ⟨x,hx⟩ := members i
    exact ⟨(sem_mem_W.mp hx).1,sem_W_and h hx⟩
  · intro i
    cases i using (Fin.addCases (m := 5) (n := 3)) with
    | left i => simpa [g,arcs,sideA] using leftBase i
    | right i => simpa [g,arcs,sideA] using rpure _ (vmem i)
  · intro i
    cases i using (Fin.addCases (m := 5) (n := 3)) with
    | left i => simpa [g,arcs,sideB] using rightBase i
    | right i => simpa [g,arcs,sideB] using rempty i
  · intro j hj ht hn
    apply noncanonical_and_empty e q f r u zero cover sourceSide oppositeSide empty hj ht
    intro hm
    obtain ⟨i,hi⟩ := all_gates_covered e q f r u j hm
    exact hn i hi

end PEqualNP.Outside.L_meta_2590_aux.S50ExtraTyped8
