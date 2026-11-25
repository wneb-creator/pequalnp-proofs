import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2590_aux

-- Circuit normalization and wire counting, adapted from L_meta_971.
namespace DagTools

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def gop : Bool → Bool → Bool → Bool
  | true, a, b => a && b
  | false, a, b => a || b

lemma gop_true (a b : Bool) : gop true a b = (a && b) := rfl

lemma gop_false (a b : Bool) : gop false a b = (a || b) := rfl

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
  cases tag D j <;> simp [gop, mem_supp]

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

lemma sem_val_gate_src (hS : Strict n D) (x : Fin n → Bool) {j : ℕ} (hj : j < D.length)
    (s : Bool) : val D x (n + j) =
      gop (tag D j) (val D x (src D (j, s))) (val D x (src D (j, !s))) := by
  rw [val_gate hS x j hj]
  cases s
  · simp [src]
  · cases tag D j <;> simp [src, gop, Bool.and_comm, Bool.or_comm]

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

lemma sem_noempty_unique (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (hB0 : Bzero n D = 0) {i : Fin n} (hi : i ∈ ineligSet n D) {w : ℕ}
    (hp : Relation.ReflTransGen (sem_step n D) i.val w) : sem_Chain n D i.val w := by
  rcases sem_path_chain hp with h1 | ⟨b, h1, h2⟩
  · exact h1
  · have h3 := sem_bzero_branch h.1 hB0 h2
    rw [sem_branch_empty hG h.1 hC hi h1 h2] at h3
    exact absurd h3 Finset.not_nonempty_empty

end SemPaths

section IneligiblePathFacts

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

lemma val_all_false (hS : Strict n D) (w : ℕ) :
    val D (fun _ : Fin n => false) w = false := by
  by_cases hw : w < n + D.length
  · exact val_unique hS (fun _ => false) (fun _ => false) (fun _ _ => rfl)
      (fun j _ => by cases tag D j <;> rfl) w hw
  · exact val_ge D _ w (by omega)

lemma ineligible_reachable_pure (hG : sem_Gr G) (h : StrictLive n D)
    (hC : sem_Comp n G D) (hz : Bzero n D = 0) {i : Fin n}
    (hi : i ∈ ineligSet n D) {w : ℕ}
    (hp : Relation.ReflTransGen (sem_step n D) i.val w) : supp n D w ⊆ {i} :=
  sem_dom_pure hG h.1 hC i w
    (sem_chain_dom h.1 (sem_noempty_unique hG h hC hz hi hp))

lemma ineligible_reachable_fanout (hG : sem_Gr G) (h : StrictLive n D)
    (hC : sem_Comp n G D) (hz : Bzero n D = 0) {i : Fin n}
    (hi : i ∈ ineligSet n D) {w : ℕ}
    (hp : Relation.ReflTransGen (sem_step n D) i.val w) : fanout D w ≤ 1 := by
  by_contra bad
  have hf : 2 ≤ fanout D w := by omega
  have hn := sem_bzero_branch h.1 hz hf
  rw [sem_branch_empty hG h.1 hC hi (sem_noempty_unique hG h hC hz hi hp) hf] at hn
  exact Finset.not_nonempty_empty hn

lemma ineligible_empty_stays_empty (hG : sem_Gr G) (h : StrictLive n D)
    (hC : sem_Comp n G D) (hz : Bzero n D = 0) {i : Fin n}
    (hi : i ∈ ineligSet n D) {b t : ℕ}
    (hb : Relation.ReflTransGen (sem_step n D) i.val b)
    (hbt : Relation.ReflTransGen (sem_step n D) b t) (empty : supp n D b = ∅) :
    supp n D t = ∅ := by
  have chain := sem_noempty_unique hG h hC hz hi hb
  have sub := ineligible_reachable_pure hG h hC hz hi (hb.trans hbt)
  have le := sem_rtg_le h.1 (fun _ _ h => h) hbt
  have sb : val D (single i) b = false := by
    by_contra bad
    rw [Bool.not_eq_false] at bad
    have mem := mem_supp.mpr bad
    rw [empty] at mem
    exact Finset.notMem_empty _ mem
  have eq := sem_dom_eq_at h.1 (fun _ : Fin n => false) (single i) i
    (by intro k hk; simp [single, hk]) b t (sem_chain_dom_at h.1 chain le)
    (by rw [val_all_false h.1, sb])
  have st : val D (single i) t = false := by rw [←eq]; exact val_all_false h.1 t
  refine Finset.eq_empty_of_forall_notMem (fun u hu => ?_)
  have ui : u = i := Finset.mem_singleton.mp (sub hu)
  subst u
  have truth := mem_supp.mp hu
  rw [st] at truth
  exact Bool.false_ne_true truth

lemma chain_join_is_or (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {i j : Fin n} {g : ℕ} (hg : g < D.length)
    (left : sem_Chain n D i.val (opA D g)) (fan : fanout D (opA D g) = 1)
    (right : sem_Chain n D j.val (opB D g)) : tag D g = false := by
  by_contra bad
  rw [Bool.not_eq_false] at bad
  obtain ⟨a,hia,haj⟩ := hG.2.2.2 i j
  have step : sem_step n D (opA D g) (n + g) := by
    simpa [src] using (sem_step_src (n := n) (D := D) hg false)
  have chain : sem_Chain n D i.val (n + g) := Relation.ReflTransGen.tail left ⟨step, fan⟩
  have split := sem_dom_split hS hC (single a) i (n + g) (sem_chain_dom hS chain)
    (sem_single_no_edge hG a)
    (show sem_Edge G (sem_ins i (single a)) from
      ⟨i,a,hia,sem_ins_self i _,by simp [sem_ins, single]⟩)
  have truth := split.2
  rw [val_gate hS _ g hg, bad, gop_true, Bool.and_eq_true] at truth
  have independent := sem_sibling_indep hS i hg true
    (by simpa [src] using left) (by simpa [src] using fan)
    (single a) (sem_ins i (single a)) (sem_ins_agree i (single a))
  have hAt : val D (single a) (opB D g) = true := by
    change val D (single a) (opB D g) = val D (sem_ins i (single a)) (opB D g) at independent
    exact independent.trans truth.2
  have pure := sem_dom_pure hG hS hC j (opB D g) (sem_chain_dom hS right)
  exact haj (Finset.mem_singleton.mp (pure (mem_supp.mpr hAt)))

lemma ineligible_paths_join_is_or (hG : sem_Gr G) (h : StrictLive n D)
    (hC : sem_Comp n G D) (hz : Bzero n D = 0) {i j : Fin n}
    (hi : i ∈ ineligSet n D) (hj : j ∈ ineligSet n D) {g : ℕ}
    (hg : g < D.length)
    (left : Relation.ReflTransGen (sem_step n D) i.val (opA D g))
    (right : Relation.ReflTransGen (sem_step n D) j.val (opB D g)) : tag D g = false := by
  have le := ineligible_reachable_fanout hG h hC hz hi left
  have pos : 1 ≤ fanout D (opA D g) := sem_step_fanout
    (by simpa [src] using (sem_step_src (n := n) (D := D) hg false))
  exact chain_join_is_or hG h.1 hC hg (sem_noempty_unique hG h hC hz hi left)
    (by omega) (sem_noempty_unique hG h hC hz hj right)

lemma chain_star_influence (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {i a : Fin n} {w : ℕ} (chain : sem_Chain n D i.val w) (hia : G i a) :
    val D (single a) w = false ∧ val D (sem_two i a) w = true := by
  exact sem_dom_split hS hC (single a) i w (sem_chain_dom hS chain)
    (sem_single_no_edge hG a)
    ⟨i,a,hia,sem_ins_self i _,by simp [sem_ins, single]⟩

lemma chain_sibling_not_self (hS : Strict n D) {i : Fin n} {g : ℕ}
    (hg : g < D.length) (left : sem_Chain n D i.val (opA D g))
    (fan : fanout D (opA D g) = 1) : i ∉ supp n D (opB D g) := by
  have independent := sem_sibling_indep hS i hg true
    (by simpa [src] using left) (by simpa [src] using fan)
    (fun _ : Fin n => false) (single i) (by intro k hk; simp [single, hk])
  change val D (fun _ : Fin n => false) (opB D g) = val D (single i) (opB D g) at independent
  rw [val_all_false hS] at independent
  intro mem
  have hv := mem_supp.mp mem
  exact Bool.false_ne_true (independent.trans hv)

lemma chain_and_opposite_neighbors (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {i : Fin n} {g : ℕ} (hg : g < D.length)
    (left : sem_Chain n D i.val (opA D g)) (fan : fanout D (opA D g) = 1)
    (hand : tag D g = true) : ∀ a : Fin n, G i a → a ∈ supp n D (opB D g) := by
  intro a hia
  have step : sem_step n D (opA D g) (n + g) := by
    simpa [src] using (sem_step_src (n := n) (D := D) hg false)
  have chain : sem_Chain n D i.val (n + g) := Relation.ReflTransGen.tail left ⟨step, fan⟩
  have truth := (chain_star_influence hG hS hC chain hia).2
  rw [val_gate hS _ g hg, hand, gop_true, Bool.and_eq_true] at truth
  have independent := sem_sibling_indep hS i hg true
    (by simpa [src] using left) (by simpa [src] using fan)
    (single a) (sem_ins i (single a)) (sem_ins_agree i (single a))
  change val D (single a) (opB D g) = val D (sem_ins i (single a)) (opB D g) at independent
  exact mem_supp.mpr (independent.trans truth.2)

lemma chain_and_output_empty (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {i : Fin n} {g : ℕ} (hg : g < D.length)
    (left : sem_Chain n D i.val (opA D g)) (fan : fanout D (opA D g) = 1)
    (hand : tag D g = true) : supp n D (n + g) = ∅ := by
  have pure := sem_dom_pure hG hS hC i (opA D g) (sem_chain_dom hS left)
  have missing := chain_sibling_not_self hS hg left fan
  refine Finset.eq_empty_of_forall_notMem (fun x hx => ?_)
  rw [sem_supp_and hS hg hand, Finset.mem_inter] at hx
  have xi := Finset.mem_singleton.mp (pure hx.1)
  exact missing (xi ▸ hx.2)

lemma chain_and_neighbor_exits (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {i : Fin n} {g : ℕ} (hg : g < D.length)
    (left : sem_Chain n D i.val (opA D g)) (fan : fanout D (opA D g) = 1)
    (hand : tag D g = true) : ∀ a : Fin n, G i a → (g, true) ∈ sem_W n D a := by
  intro a hia
  refine sem_mem_W.mpr ⟨hg,?_,?_⟩
  · simpa [src] using chain_and_opposite_neighbors hG hS hC hg left fan hand a hia
  · rw [chain_and_output_empty hG hS hC hg left fan hand]
    exact Finset.notMem_empty a

lemma chain_or_sibling_empty (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {i : Fin n} {g : ℕ} (hg : g < D.length)
    (left : sem_Chain n D i.val (opA D g)) (fan : fanout D (opA D g) = 1)
    (hor : tag D g = false) : supp n D (opB D g) = ∅ := by
  have step : sem_step n D (opA D g) (n + g) := by
    simpa [src] using (sem_step_src (n := n) (D := D) hg false)
  have chain : sem_Chain n D i.val (n + g) := Relation.ReflTransGen.tail left ⟨step, fan⟩
  have pure := sem_dom_pure hG hS hC i (n + g) (sem_chain_dom hS chain)
  have missing := chain_sibling_not_self hS hg left fan
  refine Finset.eq_empty_of_forall_notMem (fun x hx => ?_)
  have mem : x ∈ supp n D (n + g) := by
    rw [sem_supp_or hS hg hor]
    exact Finset.mem_union_right _ hx
  have xi := Finset.mem_singleton.mp (pure mem)
  exact missing (xi ▸ hx)

lemma two_chain_support_empty (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {i j : Fin n} (ne : i ≠ j) {w : ℕ}
    (hi : sem_Chain n D i.val w) (hj : sem_Chain n D j.val w) : supp n D w = ∅ := by
  have pi := sem_dom_pure hG hS hC i w (sem_chain_dom hS hi)
  have pj := sem_dom_pure hG hS hC j w (sem_chain_dom hS hj)
  refine Finset.eq_empty_of_forall_notMem (fun x hx => ?_)
  exact ne ((Finset.mem_singleton.mp (pi hx)).symm.trans (Finset.mem_singleton.mp (pj hx)))

lemma or_path_value (hS : Strict n D) (x : Fin n → Bool) {a b : ℕ}
    (hp : Relation.ReflTransGen (fun a b => sem_step n D a b ∧ tag D (b - n) = false) a b)
    (ha : val D x a = true) : val D x b = true := by
  induction hp with
  | refl => exact ha
  | tail hab hbc ih =>
      obtain ⟨j,s,hj,rfl,rfl⟩ := sem_step_iff.mp hbc.1
      have ht : tag D j = false := by simpa using hbc.2
      rw [sem_val_gate_src hS x hj s, ht, gop_false, ih]
      rfl

lemma or_tail_below_target (hS : Strict n D) (hC : sem_Comp n G D) {w : ℕ}
    (hp : Relation.ReflTransGen (fun a b => sem_step n D a b ∧ tag D (b - n) = false)
      w (outW n D)) : ∀ x : Fin n → Bool, val D x w = true → sem_Edge G x := by
  intro x hx
  exact (hC x).mp (or_path_value hS x hp hx)

lemma edge_two_iff (hG : sem_Gr G) (i a : Fin n) : sem_Edge G (sem_two i a) ↔ G i a := by
  constructor
  · rintro ⟨u,v,huv,hu,hv⟩
    simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact False.elim (hG.2.1 _ huv)
    · exact huv
    · exact hG.1 _ _ huv
    · exact False.elim (hG.2.1 _ huv)
  · exact sem_two_edge

lemma chain_star_exact_if_below_target (hG : sem_Gr G) (hS : Strict n D)
    (hC : sem_Comp n G D) {i : Fin n} {g : ℕ} (hg : g < D.length)
    (left : sem_Chain n D i.val (opA D g)) (fan : fanout D (opA D g) = 1)
    (hand : tag D g = true) (hi : i ∈ supp n D (opA D g))
    (below : ∀ x : Fin n → Bool, val D x (n + g) = true → sem_Edge G x) :
    ∀ a : Fin n, a ∈ supp n D (opB D g) ↔ G i a := by
  intro a
  constructor
  · intro ha
    have vi : val D (sem_two i a) (opA D g) = true :=
      sem_val_of_supp hS hi (by simp [sem_two])
    have va : val D (sem_two i a) (opB D g) = true :=
      sem_val_of_supp hS ha (by simp [sem_two])
    apply (edge_two_iff hG i a).mp
    apply below
    rw [val_gate hS _ g hg, hand, gop_true, vi, va]
    rfl
  · exact chain_and_opposite_neighbors hG hS hC hg left fan hand a

end IneligiblePathFacts

end DagTools


open DagTools

abbrev V := Fin 10

def edges : List (V × V) := [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]

abbrev adj (u v : V) : Prop := (u,v) ∈ edges ∨ (v,u) ∈ edges


lemma graph_ok : sem_Gr adj := by
  let instAdj (u v : V) : Decidable (adj u v) :=
    inferInstanceAs (Decidable ((u,v) ∈ edges ∨ (v,u) ∈ edges))
  unfold sem_Gr
  decide

lemma opposite_inelig_mem {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    {i x : V} (hi : i ∈ ineligSet 10 D) (hix : adj i x) :
    ∃ e, e ∈ sem_W 10 D x ∧ supp 10 D (src D (sem_bar e)) = {i} ∧
      ∀ a, adj i a → a ∈ supp 10 D (src D e) := by
  obtain ⟨e,he,_,hp,hz,hn,_,_⟩ := sem_inelig_consumer graph_ok h hc hi
  refine ⟨sem_bar e, sem_mem_W.mpr ⟨he, hn x hix, ?_⟩, ?_, ?_⟩
  · change x ∉ supp 10 D (10 + e.1)
    rw [hz]
    exact Finset.notMem_empty x
  · rw [sem_bar_bar]
    exact hp
  · exact hn

lemma inelig_common_neighbor_three {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    {i j x a b y : V} (hi : i ∈ ineligSet 10 D) (hj : j ∈ ineligSet 10 D)
    (hij : i ≠ j) (hix : adj i x) (hjx : adj j x)
    (hia : adj i a) (hjb : adj j b) (hab : ¬ adj a b)
    (hxy : adj x y) (hya : ¬ adj y a) (hyb : ¬ adj y b) :
    3 ≤ (sem_W 10 D x).card := by
  obtain ⟨ei,hei,hpi,hni⟩ := opposite_inelig_mem h hc hi hix
  obtain ⟨ej,hej,hpj,hnj⟩ := opposite_inelig_mem h hc hj hjx
  have neij : ei ≠ ej := by
    intro eq
    exact hij (Finset.singleton_injective (hpi.symm.trans (eq ▸ hpj)))
  obtain ⟨e,he,ha,hb⟩ := sem_cover_free graph_ok h.1 hc hab hxy hya hyb
  have nei : ei ≠ e := by
    intro eq
    exact ha (eq ▸ hni a hia)
  have nej : ej ≠ e := by
    intro eq
    exact hb (eq ▸ hnj b hjb)
  exact Finset.two_lt_card.mpr ⟨ei,hei,ej,hej,e,he,neij,nei,nej⟩

lemma common_neighbor_geometry : ∀ i j x : V, i ≠ j → adj i x → adj j x →
    ∃ a b y : V, adj i a ∧ adj j b ∧ ¬ adj a b ∧ adj x y ∧ ¬ adj y a ∧ ¬ adj y b := by
  let instAdj (u v : V) : Decidable (adj u v) :=
    inferInstanceAs (Decidable ((u,v) ∈ edges ∨ (v,u) ∈ edges))
  decide

lemma all_common_neighbors_three {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    {i j x : V} (hi : i ∈ ineligSet 10 D) (hj : j ∈ ineligSet 10 D)
    (hij : i ≠ j) (hix : adj i x) (hjx : adj j x) : 3 ≤ (sem_W 10 D x).card := by
  obtain ⟨a,b,y,hia,hjb,hab,hxy,hya,hyb⟩ := common_neighbor_geometry i j x hij hix hjx
  exact inelig_common_neighbor_three h hc hi hj hij hix hjx hia hjb hab hxy hya hyb

lemma common_neighbor_three {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (h0 : (0 : V) ∈ ineligSet 10 D) (h2 : (2 : V) ∈ ineligSet 10 D) :
    3 ≤ (sem_W 10 D (1 : V)).card :=
  all_common_neighbors_three h hc h0 h2 (by decide) (by decide) (by decide)

lemma common_neighbor_residual {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (b : V → ℕ) (hb : PureBranch 10 D b)
    (h0 : (0 : V) ∈ ineligSet 10 D) (h2 : (2 : V) ∈ ineligSet 10 D) :
    ∃ u ∈ residualUnits 10 D b, (1 : V) ∈ supp 10 D u.1 := by
  have three := common_neighbor_three h hc h0 h2
  have count := sem_code_count graph_ok h hc b hb (1 : V)
  have one : (({1} : Finset V) ∩ eligSet 10 D).card ≤ 1 := by
    exact (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
  have pos : 0 < ((residualUnits 10 D b).filter
      (fun u => (1 : V) ∈ supp 10 D u.1)).card := by omega
  obtain ⟨u,hu⟩ := Finset.card_pos.mp pos
  exact ⟨u,(Finset.mem_filter.mp hu).1,(Finset.mem_filter.mp hu).2⟩

lemma common_neighbor_exists : ∀ i j : V, i ≠ j → ¬ adj i j →
    ∃ x : V, adj i x ∧ adj j x := by
  let instAdj (u v : V) : Decidable (adj u v) :=
    inferInstanceAs (Decidable ((u,v) ∈ edges ∨ (v,u) ∈ edges))
  decide

lemma two_ineligible_residual_nonempty {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (b : V → ℕ) (hb : PureBranch 10 D b) (hi : 2 ≤ (ineligSet 10 D).card) :
    (residualUnits 10 D b).Nonempty := by
  obtain ⟨i,hi,j,hj,hij⟩ := Finset.one_lt_card.mp (show 1 < (ineligSet 10 D).card by omega)
  have nonadj : ¬ adj i j := by
    intro ha
    rcases sem_elig_cover graph_ok h hc ha with hmem | hmem
    · exact (sem_mem_inelig.mp hi) hmem
    · exact (sem_mem_inelig.mp hj) hmem
  obtain ⟨x,hix,hjx⟩ := common_neighbor_exists i j hij nonadj
  have three := all_common_neighbors_three h hc hi hj hij hix hjx
  have count := sem_code_count graph_ok h hc b hb x
  have one : (({x} : Finset V) ∩ eligSet 10 D).card ≤ 1 := by
    exact (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
  have pos : 0 < ((residualUnits 10 D b).filter
      (fun u => x ∈ supp 10 D u.1)).card := by omega
  obtain ⟨u,hu⟩ := Finset.card_pos.mp pos
  exact ⟨u, (Finset.mem_filter.mp hu).1⟩

lemma two_ineligible_budget {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (small : D.length ≤ 19) (hi : (ineligSet 10 D).card = 2) :
    9 ≤ Bplus 10 D ∧ Bplus 10 D ≤ 10 ∧ Bzero 10 D ≤ 1 := by
  obtain ⟨b,hb⟩ := sem_exists_pureBranch graph_ok h.1 hc
  have pos := Finset.card_pos.mpr (two_ineligible_residual_nonempty h hc b hb (by omega))
  have residual := card_residual h.1 b hb
  have complement := inelig_card_add 10 D
  have size := surplus_identity h
  rw [totalSurplus_split] at size
  omega

lemma one_residual_exit_cap {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hone : Bplus 10 D = (eligSet 10 D).card + 1) :
    ∀ x : V, (sem_W 10 D x).card ≤ 3 := by
  obtain ⟨b,hb⟩ := sem_exists_pureBranch graph_ok h.1 hc
  have residual : (residualUnits 10 D b).card = 1 := by
    have eq := card_residual h.1 b hb
    omega
  intro x
  have count := sem_code_count graph_ok h hc b hb x
  have single : (({x} : Finset V) ∩ eligSet 10 D).card ≤ 1 :=
    (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
  have rem := Finset.card_filter_le (residualUnits 10 D b) (fun u => x ∈ supp 10 D u.1)
  omega

lemma one_residual_common_interface {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hone : Bplus 10 D = (eligSet 10 D).card + 1)
    (h0 : (0 : V) ∈ ineligSet 10 D) (h2 : (2 : V) ∈ ineligSet 10 D) :
    ∃ P Q : ℕ × Bool, P.1 ≠ Q.1 ∧
      (sem_W 10 D (1 : V)).card = 3 ∧
      (∀ x : V, (sem_W 10 D x).card ≤ 3) ∧
      (∀ x : V, 3 ≤ (sem_W 10 D x).card → P ∈ sem_W 10 D x ∧ Q ∈ sem_W 10 D x) := by
  classical
  obtain ⟨b,hb⟩ := sem_exists_minBranch graph_ok h.1 hc
  let X : Finset V := Finset.univ.filter (fun x => 3 ≤ (sem_W 10 D x).card)
  have three := common_neighbor_three h hc h0 h2
  have ne : X.Nonempty := ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, three⟩⟩
  obtain ⟨P,Q,pq,all⟩ := sem_common_terminals graph_ok h hc b hb hone X ne
    (fun x hx => (Finset.mem_filter.mp hx).2)
  have cap := one_residual_exit_cap h hc hone
  refine ⟨P,Q,pq,le_antisymm (cap 1) three,cap,?_⟩
  intro x hx
  exact all x (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩)

lemma mem_three_of_card_le {α : Type*} [DecidableEq α] {S : Finset α}
    (bound : S.card ≤ 3) {a b c x : α}
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hx : x ∈ S) :
    x = a ∨ x = b ∨ x = c := by
  have sub : ({a,b,c} : Finset α) ⊆ S := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl <;> assumption
  have card : ({a,b,c} : Finset α).card = 3 := by simp [hab,hac,hbc]
  have eq : ({a,b,c} : Finset α) = S := Finset.eq_of_subset_of_card_le sub (by omega)
  rw [←eq] at hx
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hx

lemma one_residual_triple_interface {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hone : Bplus 10 D = (eligSet 10 D).card + 1)
    (h0 : (0 : V) ∈ ineligSet 10 D) (h2 : (2 : V) ∈ ineligSet 10 D) :
    ∃ P Q : ℕ × Bool, P.1 ≠ Q.1 ∧
      (sem_W 10 D (1 : V)).card = 3 ∧
      (∀ x : V, (sem_W 10 D x).card ≤ 3) ∧
      (∀ (x : V) (a b c : ℕ × Bool),
        a ∈ sem_W 10 D x → b ∈ sem_W 10 D x → c ∈ sem_W 10 D x →
        a ≠ b → a ≠ c → b ≠ c →
        (P = a ∨ P = b ∨ P = c) ∧ (Q = a ∨ Q = b ∨ Q = c)) := by
  obtain ⟨P,Q,pq,three,cap,common⟩ := one_residual_common_interface h hc hone h0 h2
  refine ⟨P,Q,pq,three,cap,?_⟩
  intro x a b c ha hb hc hab hac hbc
  have many : 3 ≤ (sem_W 10 D x).card :=
    Finset.two_lt_card.mpr ⟨a,ha,b,hb,c,hc,hab,hac,hbc⟩
  exact ⟨mem_three_of_card_le (cap x) ha hb hc hab hac hbc (common x many).1,
    mem_three_of_card_le (cap x) ha hb hc hab hac hbc (common x many).2⟩

lemma r1_bar_inj {a b : ℕ × Bool} (h : sem_bar a = sem_bar b) : a = b := by
  have h' := congrArg sem_bar h
  simpa only [sem_bar_bar] using h'

lemma r1_pure_ne {D : Dag} {A e : ℕ × Bool} {i y : V}
    (hp : supp 10 D (src D (sem_bar A)) = {i})
    (hy : sem_bar e ∈ sem_W 10 D y) (hne : y ≠ i) : A ≠ e := by
  intro eq
  have hmem := (sem_mem_W.mp hy).2.1
  rw [←eq,hp,Finset.mem_singleton] at hmem
  exact hne hmem

lemma r1_ne_opposite {D : Dag} (h : Strict 10 D) {x : V} {e : ℕ × Bool}
    (he : e ∈ sem_W 10 D x) : x ∉ supp 10 D (src D (sem_bar e)) := by
  obtain ⟨hj,hx,hn⟩ := sem_mem_W.mp he
  have ht := sem_W_and h he
  intro hx'
  apply hn
  rw [sem_supp_and h hj ht]
  rcases e with ⟨j,s⟩
  cases s <;> simpa [src,sem_bar,and_comm] using And.intro hx hx'

lemma r1_no_residual_one {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hone : Bplus 10 D = (eligSet 10 D).card + 1)
    (h0 : (0 : V) ∈ ineligSet 10 D) (h2 : (2 : V) ∈ ineligSet 10 D) : False := by
  classical
  obtain ⟨P,Q,hPQ,hthree,hcap,htrip⟩ := one_residual_triple_interface h hc hone h0 h2
  have hPQ' : P ≠ Q := fun eq => hPQ (congrArg Prod.fst eq)
  obtain ⟨A,hA,hAp,hAn⟩ := opposite_inelig_mem h hc h0 (show adj 0 1 by decide)
  obtain ⟨B,hB,hBp,hBn⟩ := opposite_inelig_mem h hc h2 (show adj 2 1 by decide)
  obtain ⟨C,hC,hC6,hCnot6,hCnot1,-⟩ := sem_edge_slots graph_ok h.1 hc (show adj 1 6 by decide)
  have hAB : A ≠ B := by
    intro eq
    have hp := hAp.symm.trans (eq ▸ hBp)
    have eq02 : (0 : V) = 2 := Finset.singleton_injective hp
    exact (by decide : (0 : V) ≠ 2) eq02
  have hAC : A ≠ C := r1_pure_ne hAp hC6 (by decide)
  have hBC : B ≠ C := r1_pure_ne hBp hC6 (by decide)
  have one_cases (e : ℕ × Bool) (he : e ∈ sem_W 10 D (1 : V)) :
      e = A ∨ e = B ∨ e = C := mem_three_of_card_le (hcap 1) hA hB hC hAB hAC hBC he
  have pqcases := htrip 1 A B C hA hB hC hAB hAC hBC
  have C35 : (3 : V) ∉ supp 10 D (src D C) ∧ (5 : V) ∉ supp 10 D (src D C) := by
    obtain ⟨e,he,he3,he5⟩ := sem_cover_free graph_ok h.1 hc
      (show ¬ adj 3 5 by decide) (show adj 1 6 by decide)
      (show ¬ adj 6 3 by decide) (show ¬ adj 6 5 by decide)
    rcases one_cases e he with rfl | rfl | rfl
    · exact False.elim (he5 (hAn 5 (by decide)))
    · exact False.elim (he3 (hBn 3 (by decide)))
    · exact ⟨he3,he5⟩
  have C47 : (4 : V) ∉ supp 10 D (src D C) ∧ (7 : V) ∉ supp 10 D (src D C) := by
    obtain ⟨e,he,he4,he7⟩ := sem_cover_free graph_ok h.1 hc
      (show ¬ adj 4 7 by decide) (show adj 1 6 by decide)
      (show ¬ adj 6 4 by decide) (show ¬ adj 6 7 by decide)
    rcases one_cases e he with rfl | rfl | rfl
    · exact False.elim (he4 (hAn 4 (by decide)))
    · exact False.elim (he7 (hBn 7 (by decide)))
    · exact ⟨he4,he7⟩
  have notC {x : V} (hx : x ∉ supp 10 D (src D C)) : C ∉ sem_W 10 D x :=
    fun hm => hx (sem_mem_W.mp hm).2.1
  have c3 := notC C35.1
  have c4 := notC C47.1
  have c5 := notC C35.2
  have c7 := notC C47.2
  have hA4 : A ∈ sem_W 10 D (4 : V) := by
    obtain ⟨hj,_,hn⟩ := sem_mem_W.mp hA
    refine sem_mem_W.mpr ⟨hj,hAn 4 (by decide),?_⟩
    intro hm
    have hb := sem_supp_and_sub h.1 hj (sem_W_and h.1 hA) (!A.2) hm
    have hp : supp 10 D (src D (A.1, !A.2)) = {0} := hAp
    rw [hp,Finset.mem_singleton] at hb
    exact (by decide : (4 : V) ≠ 0) hb
  have hA5 : A ∈ sem_W 10 D (5 : V) := by
    obtain ⟨hj,_,hn⟩ := sem_mem_W.mp hA
    refine sem_mem_W.mpr ⟨hj,hAn 5 (by decide),?_⟩
    intro hm
    have hb := sem_supp_and_sub h.1 hj (sem_W_and h.1 hA) (!A.2) hm
    rw [show supp 10 D (src D (A.1, !A.2)) = {0} from hAp,Finset.mem_singleton] at hb
    exact (by decide : (5 : V) ≠ 0) hb
  have hB3 : B ∈ sem_W 10 D (3 : V) := by
    obtain ⟨hj,_,hn⟩ := sem_mem_W.mp hB
    refine sem_mem_W.mpr ⟨hj,hBn 3 (by decide),?_⟩
    intro hm
    have hb := sem_supp_and_sub h.1 hj (sem_W_and h.1 hB) (!B.2) hm
    rw [show supp 10 D (src D (B.1, !B.2)) = {2} from hBp,Finset.mem_singleton] at hb
    exact (by decide : (3 : V) ≠ 2) hb
  have hB7 : B ∈ sem_W 10 D (7 : V) := by
    obtain ⟨hj,_,hn⟩ := sem_mem_W.mp hB
    refine sem_mem_W.mpr ⟨hj,hBn 7 (by decide),?_⟩
    intro hm
    have hb := sem_supp_and_sub h.1 hj (sem_W_and h.1 hB) (!B.2) hm
    rw [show supp 10 D (src D (B.1, !B.2)) = {2} from hBp,Finset.mem_singleton] at hb
    exact (by decide : (7 : V) ≠ 2) hb
  have pair_eq (x : V) (k e f : ℕ × Bool)
      (hk : k = A ∨ k = B) (hkm : k ∈ sem_W 10 D x)
      (he : e ∈ sem_W 10 D x) (hf : f ∈ sem_W 10 D x)
      (hAe : A ≠ e) (hAf : A ≠ f) (hBe : B ≠ e) (hBf : B ≠ f)
      (hCx : C ∉ sem_W 10 D x) : e = f := by
    by_contra hef
    have hke : k ≠ e := by rcases hk with rfl | rfl <;> assumption
    have hkf : k ≠ f := by rcases hk with rfl | rfl <;> assumption
    have trip := htrip x k e f hkm he hf hke hkf hef
    have hCk : C ≠ k := fun eq => hCx (eq ▸ hkm)
    have hCe : C ≠ e := fun eq => hCx (eq ▸ he)
    have hCf : C ≠ f := fun eq => hCx (eq ▸ hf)
    grind
  obtain ⟨a,ha3,ha4,-⟩ := sem_edge_slots graph_ok h.1 hc (show adj 3 4 by decide)
  obtain ⟨a',ha'3,ha'8,-⟩ := sem_edge_slots graph_ok h.1 hc (show adj 3 8 by decide)
  obtain ⟨b,hb4,hb9,-⟩ := sem_edge_slots graph_ok h.1 hc (show adj 4 9 by decide)
  obtain ⟨d,hd5,hd7,-⟩ := sem_edge_slots graph_ok h.1 hc (show adj 5 7 by decide)
  obtain ⟨d',hd'5,hd'8,-⟩ := sem_edge_slots graph_ok h.1 hc (show adj 5 8 by decide)
  obtain ⟨f,hf7,hf9,-⟩ := sem_edge_slots graph_ok h.1 hc (show adj 7 9 by decide)
  obtain ⟨s,hs8,hs6,-⟩ := sem_edge_slots graph_ok h.1 hc (show adj 8 6 by decide)
  obtain ⟨t,ht9,ht6,-⟩ := sem_edge_slots graph_ok h.1 hc (show adj 9 6 by decide)
  have eqaa' : a = a' := pair_eq 3 B a a' (Or.inr rfl) hB3 ha3 ha'3
    (r1_pure_ne hAp ha4 (by decide)) (r1_pure_ne hAp ha'8 (by decide))
    (r1_pure_ne hBp ha4 (by decide)) (r1_pure_ne hBp ha'8 (by decide)) c3
  subst a'
  have eqdd' : d = d' := pair_eq 5 A d d' (Or.inl rfl) hA5 hd5 hd'5
    (r1_pure_ne hAp hd7 (by decide)) (r1_pure_ne hAp hd'8 (by decide))
    (r1_pure_ne hBp hd7 (by decide)) (r1_pure_ne hBp hd'8 (by decide)) c5
  subst d'
  have eqab : sem_bar a = b := pair_eq 4 A (sem_bar a) b (Or.inl rfl) hA4 ha4 hb4
    (r1_pure_ne hAp (by simpa only [sem_bar_bar] using ha3) (by decide))
    (r1_pure_ne hAp hb9 (by decide))
    (r1_pure_ne hBp (by simpa only [sem_bar_bar] using ha3) (by decide))
    (r1_pure_ne hBp hb9 (by decide)) c4
  subst b
  have eqdf : sem_bar d = f := pair_eq 7 B (sem_bar d) f (Or.inr rfl) hB7 hd7 hf7
    (r1_pure_ne hAp (by simpa only [sem_bar_bar] using hd5) (by decide))
    (r1_pure_ne hAp hf9 (by decide))
    (r1_pure_ne hBp (by simpa only [sem_bar_bar] using hd5) (by decide))
    (r1_pure_ne hBp hf9 (by decide)) c7
  subst f
  have ha9 : a ∈ sem_W 10 D (9 : V) := by simpa only [sem_bar_bar] using hb9
  have hd9 : d ∈ sem_W 10 D (9 : V) := by simpa only [sem_bar_bar] using hf9
  have ha8 : sem_bar a ∈ sem_W 10 D (8 : V) := ha'8
  have hd8 : sem_bar d ∈ sem_W 10 D (8 : V) := hd'8
  have hdistinct (x : V) (a b c : ℕ × Bool)
      (ha : a ∈ sem_W 10 D x) (hb : b ∈ sem_W 10 D x) (hc : c ∈ sem_W 10 D x)
      (hAa : A ≠ a) (hAb : A ≠ b) (hAc : A ≠ c)
      (hBa : B ≠ a) (hBb : B ≠ b) (hBc : B ≠ c) : a = b ∨ a = c ∨ b = c := by
    by_contra! hn
    have trip := htrip x a b c ha hb hc hn.1 hn.2.1 hn.2.2
    grind
  have t8 : sem_bar a = sem_bar d ∨ sem_bar a = s ∨ sem_bar d = s :=
    hdistinct 8 _ _ _ ha8 hd8 hs8
      (r1_pure_ne hAp (by simpa only [sem_bar_bar] using ha3) (by decide))
      (r1_pure_ne hAp (by simpa only [sem_bar_bar] using hd5) (by decide))
      (r1_pure_ne hAp hs6 (by decide))
      (r1_pure_ne hBp (by simpa only [sem_bar_bar] using ha3) (by decide))
      (r1_pure_ne hBp (by simpa only [sem_bar_bar] using hd5) (by decide))
      (r1_pure_ne hBp hs6 (by decide))
  have t9 : a = d ∨ a = t ∨ d = t :=
    hdistinct 9 _ _ _ ha9 hd9 ht9
      (r1_pure_ne hAp ha4 (by decide)) (r1_pure_ne hAp hd7 (by decide))
      (r1_pure_ne hAp ht6 (by decide))
      (r1_pure_ne hBp ha4 (by decide)) (r1_pure_ne hBp hd7 (by decide))
      (r1_pure_ne hBp ht6 (by decide))
  have t6 : C = s ∨ C = t ∨ s = t := by
    have ht := hdistinct 6 _ _ _ hC6 hs6 ht6
      (r1_pure_ne hAp (by simpa only [sem_bar_bar] using hC) (by decide))
      (r1_pure_ne hAp (by simpa only [sem_bar_bar] using hs8) (by decide))
      (r1_pure_ne hAp (by simpa only [sem_bar_bar] using ht9) (by decide))
      (r1_pure_ne hBp (by simpa only [sem_bar_bar] using hC) (by decide))
      (r1_pure_ne hBp (by simpa only [sem_bar_bar] using hs8) (by decide))
      (r1_pure_ne hBp (by simpa only [sem_bar_bar] using ht9) (by decide))
    exact ht.elim (fun e => Or.inl (r1_bar_inj e))
      (fun e => e.elim (fun e => Or.inr (Or.inl (r1_bar_inj e))) (fun e => Or.inr (Or.inr (r1_bar_inj e))))
  have hCa : C ≠ a := fun eq => C35.1 (eq ▸ (sem_mem_W.mp ha3).2.1)
  have hCba : C ≠ sem_bar a := fun eq => C47.1 (eq ▸ (sem_mem_W.mp ha4).2.1)
  have hCd : C ≠ d := fun eq => C35.2 (eq ▸ (sem_mem_W.mp hd5).2.1)
  have hCbd : C ≠ sem_bar d := fun eq => C47.2 (eq ▸ (sem_mem_W.mp hd7).2.1)
  have habard : a ≠ sem_bar d := by
    intro eq
    have hm := (sem_mem_W.mp ha9).2.1
    rw [eq] at hm
    exact r1_ne_opposite h.1 hd9 hm
  have eqad : a = d := by
    by_contra ne
    have nb : sem_bar a ≠ sem_bar d := fun eq => ne (r1_bar_inj eq)
    have ha_self := sem_bar_ne a
    have hd_self := sem_bar_ne d
    have invol := sem_bar_bar a
    have invol' := sem_bar_bar d
    grind
  subst d
  have all4 (e : ℕ × Bool) (he : e ∈ sem_W 10 D (4 : V)) : e = A ∨ e = B ∨ e = sem_bar a := by
    by_cases ea : e = A
    · exact Or.inl ea
    by_cases eb : e = sem_bar a
    · exact Or.inr (Or.inr eb)
    have hAba : A ≠ sem_bar a := r1_pure_ne hAp (by simpa only [sem_bar_bar] using ha3) (by decide)
    have trip := htrip 4 A (sem_bar a) e hA4 ha4 he hAba (Ne.symm ea) (Ne.symm eb)
    have hCe : C ≠ e := fun eq => c4 (eq ▸ he)
    have hBba : B ≠ sem_bar a := r1_pure_ne hBp (by simpa only [sem_bar_bar] using ha3) (by decide)
    grind
  obtain ⟨e,he,he1,he8⟩ := sem_cover_free graph_ok h.1 hc
    (show ¬ adj 1 8 by decide) (show adj 4 9 by decide)
    (show ¬ adj 9 1 by decide) (show ¬ adj 9 8 by decide)
  rcases all4 e he with rfl | rfl | rfl
  · exact he1 (hAn 1 (by decide))
  · exact he1 (hBn 1 (by decide))
  · exact he8 (sem_mem_W.mp ha8).2.1

lemma canonical_two_ineligible_tight {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (small : D.length ≤ 19) (hi : (ineligSet 10 D).card = 2)
    (h0 : (0 : V) ∈ ineligSet 10 D) (h2 : (2 : V) ∈ ineligSet 10 D) :
    Bplus 10 D = 10 ∧ Bzero 10 D = 0 := by
  have budget := two_ineligible_budget h hc small hi
  have comp := inelig_card_add 10 D
  have notnine : Bplus 10 D ≠ 9 := by
    intro eq
    exact r1_no_residual_one h hc (by omega) h0 h2
  have size := surplus_identity h
  rw [totalSurplus_split] at size
  omega

def r1_perm_rows : List (List V) := [
  [0,1,2,3,4,5,6,7,8,9],
  [0,1,2,3,4,5,6,7,8,9],
  [0,1,2,3,4,5,6,7,8,9],
  [0,4,3,2,1,5,9,8,7,6],
  [0,1,2,3,4,5,6,7,8,9],
  [0,1,2,3,4,5,6,7,8,9],
  [0,1,6,8,5,4,2,9,3,7],
  [0,4,3,8,5,1,9,2,6,7],
  [0,4,9,7,5,1,3,6,2,8],
  [0,4,9,6,1,5,3,7,8,2],
  [0,1,2,3,4,5,6,7,8,9],
  [0,1,2,3,4,5,6,7,8,9],
  [0,1,2,3,4,5,6,7,8,9],
  [4,0,1,2,3,9,5,6,7,8],
  [1,0,4,3,2,6,5,9,8,7],
  [1,0,4,9,6,2,5,3,7,8],
  [0,1,2,3,4,5,6,7,8,9],
  [4,0,1,6,9,3,5,2,8,7],
  [4,0,5,7,9,3,1,8,2,6],
  [4,0,5,8,3,9,1,7,6,2],
  [2,1,0,4,3,7,6,5,9,8],
  [0,1,2,3,4,5,6,7,8,9],
  [0,1,2,3,4,5,6,7,8,9],
  [0,1,2,3,4,5,6,7,8,9],
  [3,4,0,1,2,8,9,5,6,7],
  [3,4,0,5,8,2,9,1,7,6],
  [6,1,0,4,9,8,2,5,3,7],
  [0,1,2,3,4,5,6,7,8,9],
  [8,5,0,1,6,3,7,4,2,9],
  [8,5,0,4,3,6,7,1,9,2],
  [2,3,4,0,1,7,8,9,5,6],
  [3,2,1,0,4,8,7,6,5,9],
  [0,1,2,3,4,5,6,7,8,9],
  [0,1,2,3,4,5,6,7,8,9],
  [0,1,2,3,4,5,6,7,8,9],
  [3,8,5,0,4,2,6,7,1,9],
  [8,3,4,0,5,6,2,9,1,7],
  [8,6,1,0,5,3,9,2,4,7],
  [0,1,2,3,4,5,6,7,8,9],
  [6,8,5,0,1,9,3,7,4,2],
  [0,1,2,3,4,5,6,7,8,9],
  [1,2,3,4,0,6,7,8,9,5],
  [4,3,2,1,0,9,8,7,6,5],
  [0,1,2,3,4,5,6,7,8,9],
  [0,1,2,3,4,5,6,7,8,9],
  [1,6,8,5,0,2,9,3,7,4],
  [4,3,8,5,0,9,2,6,7,1],
  [4,9,7,5,0,3,6,2,8,1],
  [4,9,6,1,0,3,7,8,2,5],
  [0,1,2,3,4,5,6,7,8,9],
  [0,1,2,3,4,5,6,7,8,9],
  [1,2,3,8,6,0,7,4,5,9],
  [4,3,2,7,9,0,8,1,5,6],
  [4,9,7,2,3,0,6,5,1,8],
  [1,6,8,3,2,0,9,5,4,7],
  [0,1,2,3,4,5,6,7,8,9],
  [4,3,8,6,9,0,2,5,1,7],
  [0,1,2,3,4,5,6,7,8,9],
  [0,1,2,3,4,5,6,7,8,9],
  [4,9,6,8,3,0,7,1,5,2],
  [2,1,6,8,3,7,0,9,5,4],
  [0,1,2,3,4,5,6,7,8,9],
  [6,1,2,3,8,9,0,7,4,5],
  [8,5,7,2,3,6,0,9,1,4],
  [3,4,9,7,2,8,0,6,5,1],
  [3,4,9,6,8,2,0,7,1,5],
  [0,1,2,3,4,5,6,7,8,9],
  [8,5,7,9,6,3,0,2,4,1],
  [0,1,2,3,4,5,6,7,8,9],
  [0,1,2,3,4,5,6,7,8,9],
  [2,3,4,9,7,1,8,0,6,5],
  [3,2,1,6,8,4,7,0,9,5],
  [0,1,2,3,4,5,6,7,8,9],
  [8,6,1,2,3,5,9,0,7,4],
  [3,8,5,7,2,4,6,0,9,1],
  [0,1,2,3,4,5,6,7,8,9],
  [8,3,4,9,6,5,2,0,7,1],
  [0,1,2,3,4,5,6,7,8,9],
  [6,8,5,7,9,1,3,0,2,4],
  [0,1,2,3,4,5,6,7,8,9],
  [2,3,8,5,7,1,4,6,0,9],
  [3,2,7,5,8,4,1,9,0,6],
  [8,3,2,1,6,5,4,7,0,9],
  [0,1,2,3,4,5,6,7,8,9],
  [3,8,6,1,2,4,5,9,0,7],
  [0,1,2,3,4,5,6,7,8,9],
  [0,1,2,3,4,5,6,7,8,9],
  [6,8,3,4,9,1,5,2,0,7],
  [0,1,2,3,4,5,6,7,8,9],
  [8,6,9,4,3,5,1,7,0,2],
  [2,3,8,6,1,7,4,5,9,0],
  [3,2,7,9,4,8,1,5,6,0],
  [8,3,2,7,5,6,4,1,9,0],
  [6,8,3,2,1,9,5,4,7,0],
  [0,1,2,3,4,5,6,7,8,9],
  [3,8,6,9,4,2,5,1,7,0],
  [0,1,2,3,4,5,6,7,8,9],
  [0,1,2,3,4,5,6,7,8,9],
  [8,6,9,7,5,3,1,4,2,0],
  [0,1,2,3,4,5,6,7,8,9]
]

def r1_perm_fn (i j v : V) : V :=
  ((r1_perm_rows.getD (10*i.val+j.val) []).getD v.val 0)

set_option maxHeartbeats 2000000 in
lemma r1_perm_bijective : ∀ i j : V, Function.Bijective (r1_perm_fn i j) := by
  decide +kernel

noncomputable def r1_perm (i j : V) : Equiv.Perm V :=
  Equiv.ofBijective (r1_perm_fn i j) (r1_perm_bijective i j)

set_option maxHeartbeats 2000000 in
lemma r1_perm_adj : ∀ i j u v : V,
    adj (r1_perm_fn i j u) (r1_perm_fn i j v) ↔ adj u v := by
  decide +kernel

set_option maxHeartbeats 2000000 in
lemma r1_perm_maps : ∀ i j : V, i ≠ j → ¬ adj i j →
    r1_perm_fn i j i = 0 ∧ r1_perm_fn i j j = 2 := by
  decide +kernel

lemma r1_relabel_Bplus {n : Nat} {D : Dag} (h : StrictLive n D)
    (σ : Equiv.Perm (Fin n)) : Bplus n (relabel σ D) = Bplus n D := by
  classical
  have lenpos := List.length_pos_iff_ne_nil.mpr h.2.2
  have bound : n ≤ n + D.length - 1 := by omega
  have mem_iff (w : Nat) :
      liftP σ w ∈ (inner n (relabel σ D)).filter (fun u => (supp n (relabel σ D) u).Nonempty) ↔
      w ∈ (inner n D).filter (fun u => (supp n D u).Nonempty) := by
    simp only [Finset.mem_filter, inner, Finset.mem_range, relabel_length,
      tr_liftP_lt_iff σ bound, relabel_supp σ h.1, Finset.image_nonempty]
  unfold Bplus surplusOn
  symm
  refine Finset.sum_bij (fun w _ => liftP σ w) (fun w hw => (mem_iff w).mpr hw)
    (fun a _ b _ hab => (tr_liftP_inj σ).mp hab) ?_ ?_
  · intro b hb
    refine ⟨liftP σ⁻¹ b, ?_, tr_liftP_inv' σ b⟩
    apply (mem_iff _).mp
    simpa only [tr_liftP_inv'] using hb
  · intro a ha
    rw [relabel_fanout]

lemma r1_relabel_comp {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (σ : Equiv.Perm V) (ha : ∀ i j, adj (σ i) (σ j) ↔ adj i j) :
    sem_Comp 10 adj (relabel σ D) := by
  intro x
  rw [relabel_out σ h.1 h.2.2,hc]
  constructor
  · rintro ⟨u,v,uv,hu,hv⟩
    exact ⟨σ u,σ v,(ha _ _).2 uv,hu,hv⟩
  · rintro ⟨u,v,uv,hu,hv⟩
    refine ⟨σ.symm u,σ.symm v,(ha _ _).1 (by simpa using uv),by simpa using hu,by simpa using hv⟩


lemma r1_no_residual_one_pair {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hone : Bplus 10 D = (eligSet 10 D).card + 1)
    {i j : V} (hi : i ∈ ineligSet 10 D) (hj : j ∈ ineligSet 10 D) (hne : i ≠ j) : False := by
  have nonadj : ¬ adj i j := by
    intro ha
    rcases sem_elig_cover graph_ok h hc ha with hm | hm
    · exact sem_mem_inelig.mp hi hm
    · exact sem_mem_inelig.mp hj hm
  let σ := r1_perm i j
  have ha : ∀ u v, adj (σ u) (σ v) ↔ adj u v := r1_perm_adj i j
  have maps : σ i = 0 ∧ σ j = 2 := r1_perm_maps i j hne nonadj
  have hp : Bplus 10 (relabel σ D) = (eligSet 10 (relabel σ D)).card + 1 := by
    rw [r1_relabel_Bplus h σ,relabel_eligSet σ h.1,
      Finset.card_image_of_injective _ σ.injective]
    exact hone
  have h0 : (0 : V) ∈ ineligSet 10 (relabel σ D) := by
    rw [relabel_ineligSet σ h.1]
    exact Finset.mem_image.mpr ⟨i,hi,maps.1⟩
  have h2 : (2 : V) ∈ ineligSet 10 (relabel σ D) := by
    rw [relabel_ineligSet σ h.1]
    exact Finset.mem_image.mpr ⟨j,hj,maps.2⟩
  exact r1_no_residual_one (relabel_strictLive σ h) (r1_relabel_comp h hc σ ha) hp h0 h2

lemma r1_no_residual_one_many {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hone : Bplus 10 D = (eligSet 10 D).card + 1)
    (hi : 2 ≤ (ineligSet 10 D).card) : False := by
  obtain ⟨i,hi,j,hj,hij⟩ := Finset.one_lt_card.mp (show 1 < (ineligSet 10 D).card by omega)
  exact r1_no_residual_one_pair h hc hone hi hj hij

lemma two_ineligible_extra_two {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hi : 2 ≤ (ineligSet 10 D).card) : (eligSet 10 D).card + 2 ≤ Bplus 10 D := by
  obtain ⟨b,hb⟩ := sem_exists_pureBranch graph_ok h.1 hc
  have pos := Finset.card_pos.mpr (two_ineligible_residual_nonempty h hc b hb hi)
  have eq := card_residual h.1 b hb
  by_contra hn
  have hone : Bplus 10 D = (eligSet 10 D).card + 1 := by omega
  exact r1_no_residual_one_many h hc hone hi

lemma two_ineligible_tight {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (small : D.length ≤ 19) (hi : (ineligSet 10 D).card = 2) :
    Bplus 10 D = 10 ∧ Bzero 10 D = 0 ∧ D.length = 19 := by
  have extra := two_ineligible_extra_two h hc (by omega)
  have complement := inelig_card_add 10 D
  have size := surplus_identity h
  rw [totalSurplus_split] at size
  omega

namespace DagTools

section SharedFilterFacts

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

lemma ineligible_opposite_exit (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    {i x : Fin n} (hi : i ∈ ineligSet n D) (hix : G i x) :
    ∃ e, e ∈ sem_W n D x ∧ supp n D (src D (sem_bar e)) = {i} ∧
      ∀ a, G i a → a ∈ supp n D (src D e) := by
  obtain ⟨e,he,_,hp,hz,hn,_,_⟩ := sem_inelig_consumer hG h hC hi
  refine ⟨sem_bar e, sem_mem_W.mpr ⟨he, hn x hix, ?_⟩, ?_, ?_⟩
  · change x ∉ supp n D (n + e.1)
    rw [hz]
    exact Finset.notMem_empty x
  · rw [sem_bar_bar]
    exact hp
  · exact hn

lemma shared_and_opposite_union (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {i j : Fin n} {g : ℕ} (hg : g < D.length)
    (lefti : sem_Chain n D i.val (opA D g))
    (leftj : sem_Chain n D j.val (opA D g))
    (fan : fanout D (opA D g) = 1) (hand : tag D g = true) :
    ∀ a : Fin n, G i a ∨ G j a → a ∈ supp n D (opB D g) := by
  intro a ha
  rcases ha with ha | ha
  · exact chain_and_opposite_neighbors hG hS hC hg lefti fan hand a ha
  · exact chain_and_opposite_neighbors hG hS hC hg leftj fan hand a ha

lemma shared_and_four_exits (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    {i j x y : Fin n} (hi : i ∈ ineligSet n D) (hj : j ∈ ineligSet n D)
    (hij : i ≠ j) (hix : G i x) (hjx : G j x) (hxy : G x y) (hyi : y ≠ i) (hyj : y ≠ j)
    {g : ℕ} (hg : g < D.length) (hand : tag D g = true)
    (lefti : sem_Chain n D i.val (opA D g))
    (leftj : sem_Chain n D j.val (opA D g)) (fan : fanout D (opA D g) = 1) :
    4 ≤ (sem_W n D x).card := by
  obtain ⟨ei,hei,hpi,_⟩ := ineligible_opposite_exit hG h hC hi hix
  obtain ⟨ej,hej,hpj,_⟩ := ineligible_opposite_exit hG h hC hj hjx
  obtain ⟨ey,hey,hybar,_,_,_⟩ := sem_edge_slots hG h.1 hC hxy
  have hy : y ∈ supp n D (src D (sem_bar ey)) := (sem_mem_W.mp hybar).2.1
  let eg : ℕ × Bool := (g,true)
  have heg : eg ∈ sem_W n D x := chain_and_neighbor_exits hG h.1 hC hg lefti fan hand x hix
  have empty : supp n D (src D (sem_bar eg)) = ∅ := by
    change supp n D (opA D g) = ∅
    exact two_chain_support_empty hG h.1 hC hij lefti leftj
  have neij : ei ≠ ej := by
    intro eq
    exact hij (Finset.singleton_injective (hpi.symm.trans (eq ▸ hpj)))
  have neyi : ey ≠ ei := by
    intro eq
    rw [eq, hpi, Finset.mem_singleton] at hy
    exact hyi hy
  have neyj : ey ≠ ej := by
    intro eq
    rw [eq, hpj, Finset.mem_singleton] at hy
    exact hyj hy
  have neyg : ey ≠ eg := by
    intro eq
    rw [eq, empty] at hy
    exact Finset.notMem_empty _ hy
  have neig : ei ≠ eg := by
    intro eq
    have mem : i ∈ supp n D (src D (sem_bar ei)) := by rw [hpi]; simp
    rw [eq, empty] at mem
    exact Finset.notMem_empty _ mem
  have nejg : ej ≠ eg := by
    intro eq
    have mem : j ∈ supp n D (src D (sem_bar ej)) := by rw [hpj]; simp
    rw [eq, empty] at mem
    exact Finset.notMem_empty _ mem
  have sub : ({eg,ei,ej,ey} : Finset (ℕ × Bool)) ⊆ sem_W n D x := by
    intro e he
    simp only [Finset.mem_insert,Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact heg
    · exact hei
    · exact hej
    · exact hey
  have card : ({eg,ei,ej,ey} : Finset (ℕ × Bool)).card = 4 := by
    simp [Ne.symm neig,Ne.symm nejg,Ne.symm neyg,neij,Ne.symm neyi,Ne.symm neyj]
  have le := Finset.card_le_card sub
  omega

lemma four_exits_two_residuals (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (b : Fin n → ℕ) (hb : PureBranch n D b) {x : Fin n}
    (four : 4 ≤ (sem_W n D x).card) (cap : (residualUnits n D b).card ≤ 2) :
    (sem_W n D x).card = 4 ∧ merges n D (carrierT n D {x}) = ∅ ∧
      (residualUnits n D b).card = 2 ∧
      ∀ u ∈ residualUnits n D b, x ∈ supp n D u.1 := by
  have count := sem_code_count hG h hC b hb x
  have single : (({x} : Finset (Fin n)) ∩ eligSet n D).card ≤ 1 :=
    (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
  have rem := Finset.card_filter_le (residualUnits n D b) (fun u => x ∈ supp n D u.1)
  refine ⟨by omega,Finset.card_eq_zero.mp (by omega),by omega,?_⟩
  exact Finset.card_filter_eq_iff.mp (by omega)

end SharedFilterFacts

end DagTools

open DagTools

lemma petersen_shared_and_five_supports {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 adj D) {g : ℕ}
    (hg : g < D.length) (hand : tag D g = true)
    (left0 : sem_Chain 10 D 0 (opA D g)) (left2 : sem_Chain 10 D 2 (opA D g))
    (fan : fanout D (opA D g) = 1) : 5 ≤ (supp 10 D (opB D g)).card := by
  have geom : ∀ a ∈ ({1,3,4,5,7} : Finset V), adj 0 a ∨ adj 2 a := by decide +kernel
  have sub : ({1,3,4,5,7} : Finset V) ⊆ supp 10 D (opB D g) := by
    intro a ha
    exact shared_and_opposite_union graph_ok h.1 hc hg left0 left2 fan hand a (geom a ha)
  have card : ({1,3,4,5,7} : Finset V).card = 5 := by decide
  have le := Finset.card_le_card sub
  omega

lemma petersen_shared_and_residuals {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 adj D) (small : D.length ≤ 19)
    (two : (ineligSet 10 D).card = 2)
    (h0 : (0 : V) ∈ ineligSet 10 D) (h2 : (2 : V) ∈ ineligSet 10 D)
    (b : V → ℕ) (hb : PureBranch 10 D b) {g : ℕ}
    (hg : g < D.length) (hand : tag D g = true)
    (left0 : sem_Chain 10 D 0 (opA D g)) (left2 : sem_Chain 10 D 2 (opA D g))
    (fan : fanout D (opA D g) = 1) :
    (sem_W 10 D (1 : V)).card = 4 ∧ merges 10 D (carrierT 10 D {(1 : V)}) = ∅ ∧
      (residualUnits 10 D b).card = 2 ∧
      ∀ u ∈ residualUnits 10 D b, (1 : V) ∈ supp 10 D u.1 := by
  have four := shared_and_four_exits graph_ok h hc h0 h2
    (by decide : (0 : V) ≠ 2) (by decide : adj 0 1) (by decide : adj 2 1)
    (by decide : adj 1 6) (by decide : (6 : V) ≠ 0) (by decide : (6 : V) ≠ 2)
    hg hand left0 left2 fan
  have cap : (residualUnits 10 D b).card ≤ 2 := by
    have residual := card_residual h.1 b hb
    have complement := inelig_card_add 10 D
    have size := surplus_identity h
    rw [totalSurplus_split] at size
    omega
  exact four_exits_two_residuals graph_ok h hc b hb four cap

namespace DagTools

section IneligibleAndCountFacts

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

lemma chain_and_neighbor_exits_side (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {i : Fin n} {g : ℕ} (hg : g < D.length) (s : Bool)
    (left : sem_Chain n D i.val (src D (g,s))) (fan : fanout D (src D (g,s)) = 1)
    (hand : tag D g = true) : ∀ a : Fin n, G i a → (g,!s) ∈ sem_W n D a := by
  intro a hia
  have chain : sem_Chain n D i.val (n + g) :=
    Relation.ReflTransGen.tail left ⟨sem_step_src hg s,fan⟩
  have truth := (chain_star_influence hG hS hC chain hia).2
  rw [sem_val_gate_src hS _ hg s, hand, gop_true, Bool.and_eq_true] at truth
  have independent := sem_sibling_indep hS i hg (!s)
    (by simpa only [Bool.not_not] using left) (by simpa only [Bool.not_not] using fan)
    (single a) (sem_ins i (single a)) (sem_ins_agree i (single a))
  have mem : a ∈ supp n D (src D (g,!s)) := mem_supp.mpr (independent.trans truth.2)
  refine sem_mem_W.mpr ⟨hg,mem,?_⟩
  intro ha
  have ai := Finset.mem_singleton.mp
    (sem_dom_pure hG hS hC i (n + g) (sem_chain_dom hS chain) ha)
  exact hG.2.1 i (ai ▸ hia)

lemma reachable_and_neighbor_exit (hG : sem_Gr G) (h : StrictLive n D)
    (hC : sem_Comp n G D) (hz : Bzero n D = 0) {i x : Fin n}
    (hi : i ∈ ineligSet n D) (hix : G i x) {g : ℕ}
    (hg : g < D.length) (hand : tag D g = true)
    (path : Relation.ReflTransGen (sem_step n D) i.val (n + g)) :
    ∃ e ∈ sem_W n D x, e.1 = g ∧ supp n D (src D (sem_bar e)) ⊆ {i} := by
  rcases Relation.ReflTransGen.cases_tail path with eq | ⟨u,prev,last⟩
  · have lt := i.isLt
    omega
  · obtain ⟨j,s,hj,eq,hs⟩ := sem_step_iff.mp last
    have jg : j = g := by omega
    subst j
    rw [←hs] at prev
    have chain := sem_noempty_unique hG h hC hz hi prev
    have le := ineligible_reachable_fanout hG h hC hz hi prev
    have pos := sem_step_fanout (sem_step_src (n := n) (D := D) hg s)
    have fan : fanout D (src D (g,s)) = 1 := by omega
    refine ⟨(g,!s),chain_and_neighbor_exits_side hG h.1 hC hg s chain fan hand x hix,rfl,?_⟩
    simpa only [sem_bar, Bool.not_not] using ineligible_reachable_pure hG h hC hz hi prev

lemma W_gate_injective (hS : Strict n D) {x : Fin n} {e f : ℕ × Bool}
    (he : e ∈ sem_W n D x) (hf : f ∈ sem_W n D x) (eq : e.1 = f.1) : e = f := by
  rcases sem_same_gate eq with same | same
  · exact same.symm
  · obtain ⟨hj,hxe,notout⟩ := sem_mem_W.mp he
    have hxf := (sem_mem_W.mp hf).2.1
    rw [same] at hxf
    have hand := sem_W_and hS he
    exfalso
    apply notout
    rw [sem_supp_and hS hj hand, Finset.mem_inter]
    obtain ⟨g,s⟩ := e
    cases s
    · exact ⟨by simpa [src] using hxe,by simpa [src,sem_bar] using hxf⟩
    · exact ⟨by simpa [src,sem_bar] using hxf,by simpa [src] using hxe⟩

lemma ineligible_and_union_bound (hG : sem_Gr G) (h : StrictLive n D)
    (hC : sem_Comp n G D) (hz : Bzero n D = 0) {i j x y : Fin n}
    (hi : i ∈ ineligSet n D) (hj : j ∈ ineligSet n D)
    (hix : G i x) (hjx : G j x) (hxy : G x y) (hyi : y ≠ i) (hyj : y ≠ j)
    (S : Finset ℕ)
    (all : ∀ g ∈ S, g < D.length ∧ tag D g = true ∧
      (Relation.ReflTransGen (sem_step n D) i.val (n + g) ∨
       Relation.ReflTransGen (sem_step n D) j.val (n + g))) :
    S.card + 1 ≤ (sem_W n D x).card := by
  obtain ⟨ey,hey,hybar,_,_,_⟩ := sem_edge_slots hG h.1 hC hxy
  have hy : y ∈ supp n D (src D (sem_bar ey)) := (sem_mem_W.mp hybar).2.1
  have witnesses : ∀ g ∈ S, ∃ e ∈ sem_W n D x, e.1 = g ∧
      (supp n D (src D (sem_bar e)) ⊆ {i} ∨ supp n D (src D (sem_bar e)) ⊆ {j}) := by
    intro g hg
    obtain ⟨lt,hand,path⟩ := all g hg
    rcases path with path | path
    · obtain ⟨e,he,eq,sub⟩ := reachable_and_neighbor_exit hG h hC hz hi hix lt hand path
      exact ⟨e,he,eq,Or.inl sub⟩
    · obtain ⟨e,he,eq,sub⟩ := reachable_and_neighbor_exit hG h hC hz hj hjx lt hand path
      exact ⟨e,he,eq,Or.inr sub⟩
  have notin : ey.1 ∉ S := by
    intro mem
    obtain ⟨e,he,eq,sub⟩ := witnesses ey.1 mem
    have same : e = ey := W_gate_injective h.1 he hey eq
    subst e
    rcases sub with sub | sub
    · exact hyi (Finset.mem_singleton.mp (sub hy))
    · exact hyj (Finset.mem_singleton.mp (sub hy))
  have sub : insert ey.1 S ⊆ (sem_W n D x).image Prod.fst := by
    intro g hg
    rcases Finset.mem_insert.mp hg with rfl | hg
    · exact Finset.mem_image.mpr ⟨ey,hey,rfl⟩
    · obtain ⟨e,he,eq,_⟩ := witnesses g hg
      exact Finset.mem_image.mpr ⟨e,he,eq⟩
  have count := (Finset.card_le_card sub).trans (Finset.card_image_le)
  rw [Finset.card_insert_of_notMem notin] at count
  exact count

end IneligibleAndCountFacts

end DagTools

open DagTools

lemma petersen_ineligible_and_union_three {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 adj D) (hz : Bzero 10 D = 0)
    (small : D.length ≤ 19) (two : (ineligSet 10 D).card = 2)
    (h0 : (0 : V) ∈ ineligSet 10 D) (h2 : (2 : V) ∈ ineligSet 10 D)
    (S : Finset ℕ)
    (all : ∀ g ∈ S, g < D.length ∧ tag D g = true ∧
      (Relation.ReflTransGen (sem_step 10 D) 0 (10 + g) ∨
       Relation.ReflTransGen (sem_step 10 D) 2 (10 + g))) : S.card ≤ 3 := by
  have bound := ineligible_and_union_bound graph_ok h hc hz h0 h2
    (by decide : adj 0 1) (by decide : adj 2 1) (by decide : adj 1 6)
    (by decide : (6 : V) ≠ 0) (by decide : (6 : V) ≠ 2) S all
  obtain ⟨b,hb⟩ := sem_exists_pureBranch graph_ok h.1 hc
  have residual := card_residual h.1 b hb
  have complement := inelig_card_add 10 D
  have size := surplus_identity h
  rw [totalSurplus_split] at size
  have count := sem_code_count graph_ok h hc b hb (1 : V)
  have single : (({1} : Finset V) ∩ eligSet 10 D).card ≤ 1 :=
    (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
  have rem := Finset.card_filter_le (residualUnits 10 D b) (fun u => (1 : V) ∈ supp 10 D u.1)
  omega

end PEqualNP.Outside.L_meta_2590_aux
