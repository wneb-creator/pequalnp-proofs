import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2590_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

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

lemma sem_step_src {j : ℕ} (hj : j < D.length) (s : Bool) :
    sem_step n D (src D (j, s)) (n + j) := by
  refine ⟨by omega, by omega, ?_⟩
  rw [Nat.add_sub_cancel_left]
  cases s
  · exact Or.inl (sb_src_false j).symm
  · exact Or.inr (sb_src_true j).symm

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

end SemCodes

section SemArms

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

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

end C6

namespace C6
open DagTools

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

def fourEndpoints : Finset V := {0, 1, 4, 5}

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

lemma c6_length_ge_eight_add_Bzero {D : Dag} (h : StrictLive 6 D)
    (hc : sem_Comp 6 adj D) : 8 + Bzero 6 D ≤ D.length := by
  have hp := c6_Bplus_ge_three h hc
  have hs := surplus_identity h
  rw [totalSurplus_split] at hs
  omega

end C6


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


end PEqualNP.Outside.L_meta_2590_aux

namespace PEqualNP.Outside.L_meta_2590_aux.C6.DagTools

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


end PEqualNP.Outside.L_meta_2590_aux.C6.DagTools

namespace PEqualNP.Outside.L_meta_2590_aux.PairPruning
open C6.DagTools

def c6Target (x : Fin 6 → Bool) : Bool :=
  (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 3) ||
    (x 1 && x 5) || (x 2 && x 4) || (x 2 && x 5)

lemma c6_essential : ∀ i : Fin 6, ∃ x y : Fin 6 → Bool,
    (∀ k, k ≠ i → x k = y k) ∧ c6Target x ≠ c6Target y := by
  have hw : ∀ i : Fin 6, ∃ j : Fin 6,
      c6Target (single j) ≠ c6Target (sem_ins i (single j)) := by decide +kernel
  intro i
  obtain ⟨j, hj⟩ := hw i
  exact ⟨single j, sem_ins i (single j), sem_ins_agree i (single j), hj⟩

lemma c6_nonempty {D : Dag}
    (hD : ∀ x : Fin 6 → Bool, val D x (outW 6 D) = c6Target x) : D ≠ [] := by
  intro he
  have h := hD (single 5)
  rw [he] at h
  have hin : val ([] : Dag) (single (5 : Fin 6)) (outW 6 []) = true := by decide +kernel
  have hout : c6Target (single 5) = false := by decide +kernel
  rw [hin, hout] at h
  exact Bool.false_ne_true h.symm

end PEqualNP.Outside.L_meta_2590_aux.PairPruning

namespace PEqualNP.Outside.L_meta_2590_aux.PairPruning
open C6.DagTools

set_option synthInstance.maxSize 4096 in
lemma c6Target_iff_adj (x : Fin 6 → Bool) :
    c6Target x = true ↔ sem_Edge C6.adj x := by
  revert x
  unfold c6Target sem_Edge C6.adj
  decide +kernel

end PEqualNP.Outside.L_meta_2590_aux.PairPruning

namespace PEqualNP.Outside.L_meta_2590_aux.AnnotatedPruning
open C6.DagTools

def keep {m : ℕ} (S : Finset (Fin m)) (g : Fin m → ℕ) (q : ℕ) : Finset (Fin m) :=
  S.filter (fun i => g i ≠ q)

def shift {m : ℕ} (g : Fin m → ℕ) (q : ℕ) (i : Fin m) : ℕ := na_sh q (g i)

lemma keep_subset {m : ℕ} (S : Finset (Fin m)) (g : Fin m → ℕ) (q : ℕ) :
    keep S g q ⊆ S := Finset.filter_subset _ _

lemma keep_card_loss {m : ℕ} (S : Finset (Fin m)) (g : Fin m → ℕ) (q : ℕ)
    (hinj : Set.InjOn g S) : S.card ≤ (keep S g q).card + 1 := by
  have heq (i : Fin m) (hi : i ∈ S \ keep S g q) : g i = q := by
    obtain ⟨his, hin⟩ := Finset.mem_sdiff.mp hi
    by_contra hne
    exact hin (Finset.mem_filter.mpr ⟨his, hne⟩)
  have hlost : (S \ keep S g q).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    exact hinj (Finset.mem_sdiff.mp ha).1 (Finset.mem_sdiff.mp hb).1
      ((heq a ha).trans (heq b hb).symm)
  have hsplit := Finset.card_sdiff_add_card_eq_card (keep_subset S g q)
  omega

lemma shift_inverse {m : ℕ} (g : Fin m → ℕ) (q : ℕ) (i : Fin m)
    (hne : g i ≠ q) : na_up q (shift g q i) = g i := by
  unfold shift na_up na_sh
  split_ifs <;> omega

lemma delete_support {n : ℕ} {D : Dag} (hS : Strict n D) (j : ℕ)
    (hj : j < D.length) (hf : fanout D (n + j) = 0) (w : ℕ)
    (hw : w < n + (D.length - 1)) :
    supp n (na_del n j D) w = supp n D (na_up (n + j) w) := by
  ext v
  simp only [mem_supp]
  rw [na_del_val hS j hj hf (single v) w hw]

lemma delete_annotations {m n : ℕ} {D : Dag} (hS : Strict n D) (j : ℕ)
    (hj : j < D.length) (hf : fanout D (n + j) = 0)
    (S : Finset (Fin m)) (g : Fin m → ℕ) (P : Fin m → Finset (Fin n))
    (hinj : Set.InjOn g S)
    (hbounds : ∀ i ∈ S, n ≤ g i ∧ g i < n + D.length)
    (hjoint : ∀ i ∈ S, P i ⊆ supp n D (g i)) :
    keep S g (n + j) ⊆ S ∧
    S.card ≤ (keep S g (n + j)).card + 1 ∧
    Set.InjOn (shift g (n + j)) (keep S g (n + j)) ∧
    (∀ i ∈ keep S g (n + j),
      n ≤ shift g (n + j) i ∧ shift g (n + j) i < n + (na_del n j D).length) ∧
    (∀ i ∈ keep S g (n + j), P i ⊆ supp n (na_del n j D) (shift g (n + j) i)) := by
  have hb (i : Fin m) (hi : i ∈ keep S g (n + j)) :
      n ≤ shift g (n + j) i ∧ shift g (n + j) i < n + (na_del n j D).length := by
    obtain ⟨his, hne⟩ := Finset.mem_filter.mp hi
    have hbi := hbounds i his
    rw [na_del_length n j D hj]
    constructor <;> unfold shift na_sh <;> split_ifs <;> omega
  refine ⟨keep_subset S g (n + j), keep_card_loss S g (n + j) hinj, ?_, hb, ?_⟩
  · intro a ha b hb' he
    have hga := shift_inverse g (n + j) a (Finset.mem_filter.mp ha).2
    have hgb := shift_inverse g (n + j) b (Finset.mem_filter.mp hb').2
    apply hinj (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb').1
    exact hga.symm.trans ((congrArg (na_up (n + j)) he).trans hgb)
  · intro i hi
    have hbound := (hb i hi).2
    rw [na_del_length n j D hj] at hbound
    rw [delete_support hS j hj hf _ hbound,
      shift_inverse g (n + j) i (Finset.mem_filter.mp hi).2]
    exact hjoint i (Finset.mem_filter.mp hi).1

end PEqualNP.Outside.L_meta_2590_aux.AnnotatedPruning
namespace PEqualNP.Outside.L_meta_2590_aux.AnnotatedPruning
open C6.DagTools

lemma prune_aux {m n : ℕ} (F : (Fin n → Bool) → Bool)
    (hess : ∀ i : Fin n, ∃ x y : Fin n → Bool,
      (∀ k, k ≠ i → x k = y k) ∧ F x ≠ F y)
    (P : Fin m → Finset (Fin n)) :
    ∀ (s : ℕ) (D : Dag), D.length = s → Strict n D → D ≠ [] →
      (∀ x : Fin n → Bool, val D x (outW n D) = F x) →
      ∀ (S : Finset (Fin m)) (g : Fin m → ℕ), Set.InjOn g S →
      (∀ i ∈ S, n ≤ g i ∧ g i < n + D.length) →
      (∀ i ∈ S, P i ⊆ supp n D (g i)) →
      ∃ (D' : Dag) (S' : Finset (Fin m)) (g' : Fin m → ℕ),
        StrictLive n D' ∧ S' ⊆ S ∧ Set.InjOn g' S' ∧
        (∀ i ∈ S', n ≤ g' i ∧ g' i < n + D'.length) ∧
        (∀ i ∈ S', P i ⊆ supp n D' (g' i)) ∧
        D'.length ≤ s ∧ D'.length + S.card ≤ s + S'.card ∧
        ∀ x : Fin n → Bool, val D' x (outW n D') = F x := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro D hlen hS hne hD S g hinj hbounds hjoint
    have hpos : 0 < D.length := List.length_pos_iff.mpr hne
    by_cases hL : Live n D
    · exact ⟨D,S,g,⟨hS,hL,hne⟩,Finset.Subset.refl S,hinj,hbounds,hjoint,
        hlen.le,by omega,hD⟩
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
        have hne' : na_del n j D ≠ [] := by
          intro he
          rw [he] at hl
          simp at hl
          omega
        have hD' : ∀ x : Fin n → Bool,
            val (na_del n j D) x (outW n (na_del n j D)) = F x := by
          intro x
          have ho : outW n (na_del n j D) = n + (D.length - 1) - 1 := by
            unfold outW
            rw [hl]
          have hu : na_up (n + j) (n + (D.length - 1) - 1) = outW n D := by
            unfold na_up outW
            split_ifs <;> omega
          rw [ho, na_del_val hS j hj hf0 x _ (by omega), hu]
          exact hD x
        obtain ⟨hkeep,hdrop,hginj,hgb,hgj⟩ :=
          delete_annotations hS j hj hf0 S g P hinj hbounds hjoint
        obtain ⟨D',S',g',h1,hsub,hginj',hgb',hgj',h2,h3,h4⟩ :=
          ih (D.length - 1) (by omega) (na_del n j D) hl
            (na_del_strict hS j hj hf0) hne' hD'
            (keep S g (n+j)) (shift g (n+j)) hginj hgb hgj
        exact ⟨D',S',g',h1,Finset.Subset.trans hsub hkeep,hginj',hgb',hgj',
          by omega,by omega,h4⟩

lemma exists_live_preserving_annotations {m n : ℕ} (F : (Fin n → Bool) → Bool)
    (hess : ∀ i : Fin n, ∃ x y : Fin n → Bool,
      (∀ k, k ≠ i → x k = y k) ∧ F x ≠ F y)
    (P : Fin m → Finset (Fin n)) (D : Dag) (hS : Strict n D) (hne : D ≠ [])
    (hD : ∀ x : Fin n → Bool, val D x (outW n D) = F x)
    (S : Finset (Fin m)) (g : Fin m → ℕ) (hinj : Set.InjOn g S)
    (hbounds : ∀ i ∈ S, n ≤ g i ∧ g i < n + D.length)
    (hjoint : ∀ i ∈ S, P i ⊆ supp n D (g i)) :
    ∃ (D' : Dag) (S' : Finset (Fin m)) (g' : Fin m → ℕ),
      StrictLive n D' ∧ S' ⊆ S ∧ Set.InjOn g' S' ∧
      (∀ i ∈ S', n ≤ g' i ∧ g' i < n + D'.length) ∧
      (∀ i ∈ S', P i ⊆ supp n D' (g' i)) ∧
      D'.length ≤ D.length ∧ D'.length + S.card ≤ D.length + S'.card ∧
      ∀ x : Fin n → Bool, val D' x (outW n D') = F x :=
  prune_aux F hess P D.length D rfl hS hne hD S g hinj hbounds hjoint

lemma lift_live_bound {m n : ℕ} (F : (Fin n → Bool) → Bool)
    (hess : ∀ i : Fin n, ∃ x y : Fin n → Bool,
      (∀ k, k ≠ i → x k = y k) ∧ F x ≠ F y)
    (P : Fin m → Finset (Fin n)) (b : ℕ)
    (hlive : ∀ (D : Dag) (S : Finset (Fin m)) (g : Fin m → ℕ),
      StrictLive n D → (∀ x : Fin n → Bool, val D x (outW n D) = F x) →
      Set.InjOn g S → (∀ i ∈ S, n ≤ g i ∧ g i < n + D.length) →
      (∀ i ∈ S, P i ⊆ supp n D (g i)) → b + S.card ≤ D.length)
    (D : Dag) (hS : Strict n D) (hne : D ≠ [])
    (hD : ∀ x : Fin n → Bool, val D x (outW n D) = F x)
    (S : Finset (Fin m)) (g : Fin m → ℕ) (hinj : Set.InjOn g S)
    (hbounds : ∀ i ∈ S, n ≤ g i ∧ g i < n + D.length)
    (hjoint : ∀ i ∈ S, P i ⊆ supp n D (g i)) : b + S.card ≤ D.length := by
  obtain ⟨D',S',g',h1,_,h2,h3,h4,_,h5,h6⟩ :=
    exists_live_preserving_annotations F hess P D hS hne hD S g hinj hbounds hjoint
  have h7 := hlive D' S' g' h1 h6 h2 h3 h4
  omega

end PEqualNP.Outside.L_meta_2590_aux.AnnotatedPruning

namespace PEqualNP.Outside.L_meta_2590_aux.AnnotatedPruning
open C6.DagTools PairPruning

lemma c6_strict_designated_bound
    (D : Dag) (hS : Strict 6 D)
    (hD : ∀ x : Fin 6 → Bool, val D x (outW 6 D) = c6Target x)
    (S : Finset (Fin 3)) (g : Fin 3 → Nat) (hinj : Set.InjOn g S)
    (hbounds : ∀ p ∈ S, 6 ≤ g p ∧ g p < 6 + D.length)
    (hjoint : ∀ p ∈ S, (![0, 1, 2] p : Fin 6) ∈ supp 6 D (g p) ∧
      (![5, 4, 3] p : Fin 6) ∈ supp 6 D (g p)) :
    8 + S.card ≤ D.length := by
  refine lift_live_bound c6Target c6_essential
    (fun p : Fin 3 => {(![0, 1, 2] p : Fin 6), (![5, 4, 3] p : Fin 6)}) 8
    ?_ D hS (c6_nonempty hD) hD S g hinj hbounds ?_
  · intro D' S' g' hL hF _ _ hP
    have hc : sem_Comp 6 C6.adj D' := by
      intro x
      rw [hF x]
      exact c6Target_iff_adj x
    apply C6.GenericPair.pair_occurrences_length hL hc S'
    intro p hp
    exact ⟨g' p, hP p hp (Finset.mem_insert_self _ _),
      hP p hp (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))⟩
  · intro p hp
    simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using hjoint p hp

end PEqualNP.Outside.L_meta_2590_aux.AnnotatedPruning
