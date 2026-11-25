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


namespace PEqualNP.Outside.L_meta_2590_aux.DagTools

section CleanStarTail

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

lemma live_reaches_output (h : StrictLive n D) {w : ℕ}
    (hw : w < n + D.length) :
    Relation.ReflTransGen (sem_step n D) w (outW n D) := by
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
        (ih (n + D.length - (n + j)) (by omega) (w := n + j) (by omega) rfl)
      simpa using hj.2

lemma or_tail_of_no_later_and (h : StrictLive n D) {g : ℕ}
    (hg : g < D.length)
    (hno : ∀ j, g < j → j < D.length → tag D j = true →
      ¬ Relation.ReflTransGen (sem_step n D) (n + g) (n + j)) :
    Relation.ReflTransGen
      (fun a b => sem_step n D a b ∧ tag D (b - n) = false)
      (n + g) (outW n D) := by
  have liftPath : ∀ w, Relation.ReflTransGen (sem_step n D) (n + g) w →
      Relation.ReflTransGen
        (fun a b => sem_step n D a b ∧ tag D (b - n) = false) (n + g) w := by
    intro w hp
    induction hp with
    | refl => exact Relation.ReflTransGen.refl
    | @tail b c hp hs ih =>
      obtain ⟨j, s, hj, rfl, hsrc⟩ := sem_step_iff.mp hs
      have hle := sem_rtg_le h.1 (fun _ _ hstep => hstep) hp
      have hlt := sem_step_lt h.1 hs
      have hgj : g < j := by omega
      have hor : tag D j = false := by
        cases ht : tag D j
        · rfl
        · exact False.elim (hno j hgj hj ht (Relation.ReflTransGen.tail hp hs))
      exact Relation.ReflTransGen.tail ih ⟨hs, by simpa only [Nat.add_sub_cancel_left] using hor⟩
  exact liftPath _ (live_reaches_output h (by omega))

lemma chain_star_exact_side_if_below_target (hG : sem_Gr G) (hS : Strict n D)
    (hC : sem_Comp n G D) {i : Fin n} {g : ℕ} (hg : g < D.length) (s : Bool)
    (left : sem_Chain n D i.val (src D (g, s)))
    (fan : fanout D (src D (g, s)) = 1) (hand : tag D g = true)
    (hi : i ∈ supp n D (src D (g, s)))
    (below : ∀ x : Fin n → Bool, val D x (n + g) = true → sem_Edge G x) :
    ∀ a : Fin n, a ∈ supp n D (src D (g, !s)) ↔ G i a := by
  intro a
  constructor
  · intro ha
    have vi : val D (sem_two i a) (src D (g, s)) = true :=
      sem_val_of_supp hS hi (by simp [sem_two])
    have va : val D (sem_two i a) (src D (g, !s)) = true :=
      sem_val_of_supp hS ha (by simp [sem_two])
    apply (edge_two_iff hG i a).mp
    apply below
    rw [sem_val_gate_src hS _ hg s, hand, gop_true, vi, va]
    rfl
  · intro hia
    exact (sem_mem_W.mp
      (chain_and_neighbor_exits_side hG hS hC hg s left fan hand a hia)).2.1

lemma chain_star_exact_of_no_later_and (hG : sem_Gr G) (h : StrictLive n D)
    (hC : sem_Comp n G D) {i : Fin n} {g : ℕ} (hg : g < D.length) (s : Bool)
    (left : sem_Chain n D i.val (src D (g, s)))
    (fan : fanout D (src D (g, s)) = 1) (hand : tag D g = true)
    (hi : i ∈ supp n D (src D (g, s)))
    (hno : ∀ j, g < j → j < D.length → tag D j = true →
      ¬ Relation.ReflTransGen (sem_step n D) (n + g) (n + j)) :
    ∀ a : Fin n, a ∈ supp n D (src D (g, !s)) ↔ G i a := by
  exact chain_star_exact_side_if_below_target hG h.1 hC hg s left fan hand hi
    (or_tail_below_target h.1 hC (or_tail_of_no_later_and h hg hno))

lemma clean_star_signatures_of_unique_reachable_and
    (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    {i : Fin n} {g : ℕ} (hg : g < D.length) (s : Bool)
    (left : sem_Chain n D i.val (src D (g, s)))
    (fan : fanout D (src D (g, s)) = 1) (hand : tag D g = true)
    (hi : i ∈ supp n D (src D (g, s)))
    (honly : ∀ j, j < D.length → tag D j = true →
      Relation.ReflTransGen (sem_step n D) i.val (n + j) → j = g) :
    supp n D (src D (g, s)) = {i} ∧
      ∀ a : Fin n, a ∈ supp n D (src D (g, !s)) ↔ G i a := by
  have first : Relation.ReflTransGen (sem_step n D) i.val (n + g) :=
    Relation.ReflTransGen.tail
      (sem_rtg_mono (fun _ _ hstep => hstep.1) left) (sem_step_src hg s)
  refine ⟨Finset.Subset.antisymm
    (sem_dom_pure hG h.1 hC i _ (sem_chain_dom h.1 left)) ?_, ?_⟩
  · intro a ha
    have ha' : a = i := Finset.mem_singleton.mp ha
    simpa only [ha'] using hi
  · apply chain_star_exact_of_no_later_and hG h hC hg s left fan hand hi
    intro j hgj hj hjand hp
    have eq := honly j hj hjand (first.trans hp)
    omega

end CleanStarTail

end PEqualNP.Outside.L_meta_2590_aux.DagTools

namespace PEqualNP.Outside.L_meta_2590_aux.DagTools

def carrierDiff (n : ℕ) (D : Dag) (x y : Fin n) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => x ∈ supp n D w ∧ y ∉ supp n D w)

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

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

lemma ri_gen (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D) (b : Fin n → ℕ)
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

end PEqualNP.Outside.L_meta_2590_aux.DagTools

namespace PEqualNP.Outside.L_meta_2590_aux.DagTools

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

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

lemma sem_ind_single (a : Fin n) : sem_ind ({a} : Finset (Fin n)) = single a := by
  funext k; simp [sem_ind, single]

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

end PEqualNP.Outside.L_meta_2590_aux.DagTools

namespace PEqualNP.Outside.L_meta_2590_aux.DagTools

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

lemma ineligible_code_not_subset
    (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (hz : Bzero n D = 0) (b : Fin n → ℕ) (hb : PureBranch n D b)
    {i x c : Fin n} (hi : i ∈ ineligSet n D) (hix : G i x)
    (hic : ¬ G i c) (hxc : ¬ G x c)
    (hcode : ∃ u ∈ residualUnits n D b, x ∈ supp n D u.1)
    (A : Finset (Fin n)) (hA : ∀ a ∈ A, ∀ z ∈ A, ¬ G a z)
    (hcA : c ∈ A) (hiA : ∃ a ∈ A, G i a) (hxA : ∃ a ∈ A, G x a) :
    ¬ (∀ u ∈ residualUnits n D b, x ∈ supp n D u.1 → c ∈ supp n D u.1) := by
  intro hinc
  have hne : x ≠ c := by
    intro he
    exact hic (he ▸ hix)
  have hxe : x ∈ eligSet n D :=
    (sem_elig_cover hG h hC hix).resolve_left (sem_mem_inelig.mp hi)
  have hind : ∀ a ∈ ({x,c} : Finset (Fin n)), ∀ z ∈ ({x,c} : Finset (Fin n)), ¬ G a z := by
    intro a ha z hz'
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hz'
    rcases ha with rfl | rfl <;> rcases hz' with rfl | rfl
    · exact hG.2.1 _
    · exact hxc
    · exact fun hh => hxc (hG.1 _ _ hh)
    · exact hG.2.1 _
  obtain ⟨j,s,hj,ht,hchain,hexact⟩ := sem_exact_nbhd hG h.1 hC {x,c} hind
    (sem_noempty_chain_out hG h hC hz hi)
  have hfan : fanout D (src D (j,!s)) = 1 := by
    have hle := ineligible_reachable_fanout hG h hC hz hi
      (sem_rtg_mono (fun _ _ hh => hh.1) hchain)
    have hpos := sem_step_fanout (sem_step_src (n := n) (D := D) hj (!s))
    omega
  have hall : ∀ a, G i a → (j,s) ∈ sem_W n D a := by
    intro a ha
    simpa only [Bool.not_not] using
      chain_and_neighbor_exits_side hG h.1 hC hj (!s) hchain hfan ht a ha
  have hfree : c ∉ supp n D (src D (j,s)) := by
    intro hc
    exact hic ((hexact c (by simp)).mp hc)
  obtain ⟨k,t,hk,_,hxs,hno,hdis⟩ := sem_exposure hG h.1 hC A hA x hxA
  have hW : (k,t) ∈ sem_W n D x := sem_mem_W.mpr ⟨hk,hxs,hno⟩
  have hfree' : c ∉ supp n D (src D (k,t)) :=
    fun hc => Finset.disjoint_left.mp hdis hc hcA
  have hneq : (j,s) ≠ (k,t) := by
    intro he
    obtain ⟨a,haA,hia⟩ := hiA
    have ham := (sem_mem_W.mp (hall a hia)).2.1
    rw [he] at ham
    exact Finset.disjoint_left.mp hdis ham haA
  obtain ⟨u,hu,hxu⟩ := hcode
  obtain ⟨e0,he0⟩ := ri_gen hG h hC b hb hne hxe hinc ⟨hxu,hinc u hu hxu⟩
  have he : (j,s) = e0 := by
    by_contra hh
    exact hfree (he0 _ (hall x hix) hh)
  have he' : (k,t) = e0 := by
    by_contra hh
    exact hfree' (he0 _ hW hh)
  exact hneq (he.trans he'.symm)

end PEqualNP.Outside.L_meta_2590_aux.DagTools

namespace PEqualNP.Outside.L_meta_2590_aux

open DagTools

lemma petersen_one_code_not_subset {D : Dag}
    (h : StrictLive 10 D) (hC : sem_Comp 10 adj D) (hz : Bzero 10 D = 0)
    (h0 : (0 : V) ∈ ineligSet 10 D) (h2 : (2 : V) ∈ ineligSet 10 D)
    (b : V → ℕ) (hb : PureBranch 10 D b) {c : V}
    (hc : c ∈ ({3,4,5,7,8,9} : Finset V)) :
    ¬ (∀ u ∈ residualUnits 10 D b,
      (1 : V) ∈ supp 10 D u.1 → c ∈ supp 10 D u.1) := by
  have nonempty := common_neighbor_residual h hC b hb h0 h2
  have hc_cases : c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 7 ∨ c = 8 ∨ c = 9 := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hc
  rcases hc_cases with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ineligible_code_not_subset graph_ok h hC hz b hb h0
      (by decide : adj 0 1) (by decide : ¬ adj 0 3) (by decide : ¬ adj 1 3)
      nonempty {3,5,6} (by decide) (by decide) ⟨5, by decide, by decide⟩
      ⟨6, by decide, by decide⟩
  · exact ineligible_code_not_subset graph_ok h hC hz b hb h2
      (by decide : adj 2 1) (by decide : ¬ adj 2 4) (by decide : ¬ adj 1 4)
      nonempty {4,6,7} (by decide) (by decide) ⟨7, by decide, by decide⟩
      ⟨6, by decide, by decide⟩
  · exact ineligible_code_not_subset graph_ok h hC hz b hb h2
      (by decide : adj 2 1) (by decide : ¬ adj 2 5) (by decide : ¬ adj 1 5)
      nonempty {3,5,6} (by decide) (by decide) ⟨3, by decide, by decide⟩
      ⟨6, by decide, by decide⟩
  · exact ineligible_code_not_subset graph_ok h hC hz b hb h0
      (by decide : adj 0 1) (by decide : ¬ adj 0 7) (by decide : ¬ adj 1 7)
      nonempty {4,6,7} (by decide) (by decide) ⟨4, by decide, by decide⟩
      ⟨6, by decide, by decide⟩
  · exact ineligible_code_not_subset graph_ok h hC hz b hb h0
      (by decide : adj 0 1) (by decide : ¬ adj 0 8) (by decide : ¬ adj 1 8)
      nonempty {2,4,8} (by decide) (by decide) ⟨4, by decide, by decide⟩
      ⟨2, by decide, by decide⟩
  · exact ineligible_code_not_subset graph_ok h hC hz b hb h0
      (by decide : adj 0 1) (by decide : ¬ adj 0 9) (by decide : ¬ adj 1 9)
      nonempty {2,5,9} (by decide) (by decide) ⟨5, by decide, by decide⟩
      ⟨2, by decide, by decide⟩

lemma petersen_code_card_le_one {D : Dag}
    (h : StrictLive 10 D) (hC : sem_Comp 10 adj D) (hz : Bzero 10 D = 0)
    (h0 : (0 : V) ∈ ineligSet 10 D) (h2 : (2 : V) ∈ ineligSet 10 D)
    (b : V → ℕ) (hb : PureBranch 10 D b)
    (cap : (residualUnits 10 D b).card ≤ 2) {c : V}
    (hc : c ∈ ({3,4,5,7,8,9} : Finset V)) :
    ((residualUnits 10 D b).filter (fun u => c ∈ supp 10 D u.1)).card ≤ 1 := by
  have notsub := petersen_one_code_not_subset h hC hz h0 h2 b hb hc
  have le := Finset.card_filter_le (residualUnits 10 D b)
    (fun u => c ∈ supp 10 D u.1)
  by_contra bad
  have eq : ((residualUnits 10 D b).filter
      (fun u => c ∈ supp 10 D u.1)).card = (residualUnits 10 D b).card := by omega
  have hall := Finset.card_filter_eq_iff.mp eq
  apply notsub
  intro u hu h1
  exact hall u hu

lemma petersen_exit_card_le_three {D : Dag}
    (h : StrictLive 10 D) (hC : sem_Comp 10 adj D) (hz : Bzero 10 D = 0)
    (h0 : (0 : V) ∈ ineligSet 10 D) (h2 : (2 : V) ∈ ineligSet 10 D)
    (b : V → ℕ) (hb : PureBranch 10 D b)
    (cap : (residualUnits 10 D b).card ≤ 2) {c : V}
    (hc : c ∈ ({3,4,5,7,8,9} : Finset V)) :
    (sem_W 10 D c).card ≤ 3 := by
  have code := petersen_code_card_le_one h hC hz h0 h2 b hb cap hc
  have count := sem_code_count graph_ok h hC b hb c
  have single : (({c} : Finset V) ∩ eligSet 10 D).card ≤ 1 :=
    (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
  omega

lemma petersen_two_ineligible_code_caps {D : Dag}
    (h : StrictLive 10 D) (hC : sem_Comp 10 adj D)
    (small : D.length ≤ 19) (two : (ineligSet 10 D).card = 2)
    (h0 : (0 : V) ∈ ineligSet 10 D) (h2 : (2 : V) ∈ ineligSet 10 D)
    (b : V → ℕ) (hb : PureBranch 10 D b) :
    Bzero 10 D = 0 ∧ (residualUnits 10 D b).card = 2 ∧
      ∀ c ∈ ({3,4,5,7,8,9} : Finset V),
        (¬ (∀ u ∈ residualUnits 10 D b,
          (1 : V) ∈ supp 10 D u.1 → c ∈ supp 10 D u.1)) ∧
        ((residualUnits 10 D b).filter (fun u => c ∈ supp 10 D u.1)).card ≤ 1 ∧
        (sem_W 10 D c).card ≤ 3 := by
  obtain ⟨hp,hz,hlen⟩ := two_ineligible_tight h hC small two
  have residual := card_residual h.1 b hb
  have complement := inelig_card_add 10 D
  have card : (residualUnits 10 D b).card = 2 := by omega
  refine ⟨hz,card,?_⟩
  intro c hc
  exact ⟨petersen_one_code_not_subset h hC hz h0 h2 b hb hc,
    petersen_code_card_le_one h hC hz h0 h2 b hb (by omega) hc,
    petersen_exit_card_le_three h hC hz h0 h2 b hb (by omega) hc⟩

end PEqualNP.Outside.L_meta_2590_aux

namespace PEqualNP.Outside.L_meta_2590_aux

open DagTools

lemma private_filter_no_free_support_reconstructed {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (h0 : (0 : V) ∈ ineligSet 10 D) (h2 : (2 : V) ∈ ineligSet 10 D)
    (cap1 : (sem_W 10 D (1 : V)).card ≤ 4)
    (cap4 : (sem_W 10 D (4 : V)).card ≤ 3)
    (cap5 : (sem_W 10 D (5 : V)).card ≤ 3)
    (free3 : ∀ e ∈ sem_W 10 D (3 : V), ∀ f ∈ sem_W 10 D (3 : V),
      (1 : V) ∉ supp 10 D (src D e) → (1 : V) ∉ supp 10 D (src D f) → e = f)
    (free7 : ∀ e ∈ sem_W 10 D (7 : V), ∀ f ∈ sem_W 10 D (7 : V),
      (1 : V) ∉ supp 10 D (src D e) → (1 : V) ∉ supp 10 D (src D f) → e = f)
    {F : ℕ × Bool} (hF : F.1 < D.length) (tF : tag D F.1 = true)
    (emptyF : supp 10 D (src D (sem_bar F)) = ∅)
    (neighborsF : ∀ x : V, adj 0 x → x ∈ supp 10 D (src D F)) : False := by
  classical
  obtain ⟨A, hA1, pureA, neighborsA⟩ := opposite_inelig_mem h hc h0 (show adj 0 1 by decide)
  obtain ⟨B, hB1, pureB, neighborsB⟩ := opposite_inelig_mem h hc h2 (show adj 2 1 by decide)
  have A_neighbors (x : V) (hx : adj 0 x) (hne : x ≠ 0) : A ∈ sem_W 10 D x := by
    have hj := (sem_mem_W.mp hA1).1
    refine sem_mem_W.mpr ⟨hj, neighborsA x hx, ?_⟩
    intro ho
    have hm := sem_supp_and_sub h.1 hj (sem_W_and h.1 hA1) (!A.2) ho
    change x ∈ supp 10 D (src D (sem_bar A)) at hm
    rw [pureA, Finset.mem_singleton] at hm
    exact hne hm
  have F_neighbors (x : V) (hx : adj 0 x) : F ∈ sem_W 10 D x := by
    refine sem_mem_W.mpr ⟨hF, neighborsF x hx, ?_⟩
    intro ho
    have hm := sem_supp_and_sub h.1 hF tF (!F.2) ho
    change x ∈ supp 10 D (src D (sem_bar F)) at hm
    rw [emptyF] at hm
    exact Finset.notMem_empty x hm
  have hA4 := A_neighbors 4 (by decide) (by decide)
  have hA5 := A_neighbors 5 (by decide) (by decide)
  have hF1 := F_neighbors 1 (by decide)
  have hF4 := F_neighbors 4 (by decide)
  have hF5 := F_neighbors 5 (by decide)
  have neAF : A ≠ F := by
    intro he
    have hm : (0 : V) ∈ supp 10 D (src D (sem_bar A)) := by rw [pureA]; simp
    rw [he, emptyF] at hm
    exact Finset.notMem_empty _ hm
  have neAB : A ≠ B := by
    intro he
    have eq := Finset.singleton_injective (pureA.symm.trans (he ▸ pureB))
    exact (by decide : (0 : V) ≠ 2) eq
  have neBF : B ≠ F := by
    intro he
    have hm : (2 : V) ∈ supp 10 D (src D (sem_bar B)) := by rw [pureB]; simp
    rw [he, emptyF] at hm
    exact Finset.notMem_empty _ hm
  have edge_other {e : ℕ × Bool} {x : V}
      (hx : x ∈ supp 10 D (src D (sem_bar e))) (hx0 : x ≠ 0) : e ≠ A ∧ e ≠ F := by
    constructor
    · intro he
      rw [he, pureA, Finset.mem_singleton] at hx
      exact hx0 hx
    · intro he
      rw [he, emptyF] at hx
      exact Finset.notMem_empty _ hx
  obtain ⟨H4, hH4, hbarH4, _, _, _⟩ := sem_edge_slots graph_ok h.1 hc (show adj 4 3 by decide)
  obtain ⟨J4, hJ4, hbarJ4, _, _, _⟩ := sem_edge_slots graph_ok h.1 hc (show adj 4 9 by decide)
  have h3 : (3 : V) ∈ supp 10 D (src D (sem_bar H4)) := (sem_mem_W.mp hbarH4).2.1
  have h9J : (9 : V) ∈ supp 10 D (src D (sem_bar J4)) := (sem_mem_W.mp hbarJ4).2.1
  have ne4 := edge_other h3 (by decide)
  have neJ4 := edge_other h9J (by decide)
  have cases4 (e) (he : e ∈ sem_W 10 D (4 : V)) : e = A ∨ e = F ∨ e = H4 :=
    mem_three_of_card_le cap4 hA4 hF4 hH4 neAF ne4.1.symm ne4.2.symm he
  have eqJ4 : J4 = H4 := by
    rcases cases4 J4 hJ4 with he | he | he
    · exact False.elim (neJ4.1 he)
    · exact False.elim (neJ4.2 he)
    · exact he
  have h9 : (9 : V) ∈ supp 10 D (src D (sem_bar H4)) := eqJ4 ▸ h9J
  obtain ⟨H5, hH5, hbarH5, _, _, _⟩ := sem_edge_slots graph_ok h.1 hc (show adj 5 7 by decide)
  obtain ⟨J5, hJ5, hbarJ5, _, _, _⟩ := sem_edge_slots graph_ok h.1 hc (show adj 5 8 by decide)
  have h7 : (7 : V) ∈ supp 10 D (src D (sem_bar H5)) := (sem_mem_W.mp hbarH5).2.1
  have h8J : (8 : V) ∈ supp 10 D (src D (sem_bar J5)) := (sem_mem_W.mp hbarJ5).2.1
  have ne5 := edge_other h7 (by decide)
  have neJ5 := edge_other h8J (by decide)
  have cases5 (e) (he : e ∈ sem_W 10 D (5 : V)) : e = A ∨ e = F ∨ e = H5 :=
    mem_three_of_card_le cap5 hA5 hF5 hH5 neAF ne5.1.symm ne5.2.symm he
  have eqJ5 : J5 = H5 := by
    rcases cases5 J5 hJ5 with he | he | he
    · exact False.elim (neJ5.1 he)
    · exact False.elim (neJ5.2 he)
    · exact he
  have h8 : (8 : V) ∈ supp 10 D (src D (sem_bar H5)) := eqJ5 ▸ h8J
  have H4free : (1 : V) ∉ supp 10 D (src D H4) ∧ (5 : V) ∉ supp 10 D (src D H4) := by
    obtain ⟨e, he, he1, he5⟩ := sem_cover_free graph_ok h.1 hc
      (show ¬ adj 1 5 by decide) (show adj 4 3 by decide)
      (show ¬ adj 3 1 by decide) (show ¬ adj 3 5 by decide)
    rcases cases4 e he with rfl | rfl | rfl
    · exact False.elim (he1 (neighborsA 1 (by decide)))
    · exact False.elim (he1 (neighborsF 1 (by decide)))
    · exact ⟨he1, he5⟩
  have H5free : (1 : V) ∉ supp 10 D (src D H5) := by
    obtain ⟨e, he, he1, _⟩ := sem_cover_free graph_ok h.1 hc
      (show ¬ adj 1 4 by decide) (show adj 5 7 by decide)
      (show ¬ adj 7 1 by decide) (show ¬ adj 7 4 by decide)
    rcases cases5 e he with rfl | rfl | rfl
    · exact False.elim (he1 (neighborsA 1 (by decide)))
    · exact False.elim (he1 (neighborsF 1 (by decide)))
    · exact he1
  have barH4one : (1 : V) ∈ supp 10 D (src D (sem_bar H4)) := by
    by_contra hn
    obtain ⟨e, he, he1, he9⟩ := sem_cover_free graph_ok h.1 hc
      (show ¬ adj 1 9 by decide) (show adj 3 8 by decide)
      (show ¬ adj 8 1 by decide) (show ¬ adj 8 9 by decide)
    exact he9 ((free3 _ hbarH4 _ he hn he1) ▸ h9)
  have barH5one : (1 : V) ∈ supp 10 D (src D (sem_bar H5)) := by
    by_contra hn
    obtain ⟨e, he, he1, he8⟩ := sem_cover_free graph_ok h.1 hc
      (show ¬ adj 1 8 by decide) (show adj 7 9 by decide)
      (show ¬ adj 9 1 by decide) (show ¬ adj 9 8 by decide)
    exact he8 ((free7 _ hbarH5 _ he hn he1) ▸ h8)
  have bar_exit {e : ℕ × Bool} {x : V} (he : e ∈ sem_W 10 D x)
      (hno : (1 : V) ∉ supp 10 D (src D e))
      (hyes : (1 : V) ∈ supp 10 D (src D (sem_bar e))) : sem_bar e ∈ sem_W 10 D (1 : V) := by
    have hj := (sem_mem_W.mp he).1
    refine sem_mem_W.mpr ⟨hj, hyes, ?_⟩
    intro ho
    exact hno (sem_supp_and_sub h.1 hj (sem_W_and h.1 he) e.2 ho)
  have hbar41 := bar_exit hH4 H4free.1 barH4one
  have hbar51 := bar_exit hH5 H5free barH5one
  have bar_apart {e : ℕ × Bool} {x : V} (hx : x ∈ supp 10 D (src D e))
      (hx0 : x ≠ 0) (hx2 : x ≠ 2) : sem_bar e ≠ A ∧ sem_bar e ≠ B ∧ sem_bar e ≠ F := by
    have hbar : x ∈ supp 10 D (src D (sem_bar (sem_bar e))) := by simpa only [sem_bar_bar] using hx
    have aa := edge_other hbar hx0
    refine ⟨aa.1, ?_, aa.2⟩
    intro he
    rw [he, pureB, Finset.mem_singleton] at hbar
    exact hx2 hbar
  have nebar4 := bar_apart (sem_mem_W.mp hH4).2.1 (by decide) (by decide)
  have nebar5 := bar_apart (sem_mem_W.mp hH5).2.1 (by decide) (by decide)
  have same : sem_bar H4 = sem_bar H5 := by
    by_contra hn
    have sub : ({A, B, F, sem_bar H4, sem_bar H5} : Finset (ℕ × Bool)) ⊆ sem_W 10 D (1 : V) := by
      intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl | rfl | rfl <;> assumption
    have five : ({A, B, F, sem_bar H4, sem_bar H5} : Finset (ℕ × Bool)).card = 5 := by
      simp [neAB, neAF, neBF, Ne.symm nebar4.1, Ne.symm nebar4.2.1,
        Ne.symm nebar4.2.2, Ne.symm nebar5.1, Ne.symm nebar5.2.1, Ne.symm nebar5.2.2, hn]
    have le := Finset.card_le_card sub
    omega
  have eq : H4 = H5 := r1_bar_inj same
  apply H4free.2
  rw [eq]
  exact (sem_mem_W.mp hH5).2.1

end PEqualNP.Outside.L_meta_2590_aux

namespace PEqualNP.Outside.L_meta_2590_aux

open DagTools

lemma private_filter_four_exits {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (h0 : (0 : V) ∈ ineligSet 10 D) (h2 : (2 : V) ∈ ineligSet 10 D)
    {F : ℕ × Bool} (hF : F.1 < D.length) (tF : tag D F.1 = true)
    (emptyF : supp 10 D (src D (sem_bar F)) = ∅)
    (oneF : (1 : V) ∈ supp 10 D (src D F)) :
    4 ≤ (sem_W 10 D (1 : V)).card := by
  classical
  obtain ⟨A, hA, pureA, _⟩ := opposite_inelig_mem h hc h0 (show adj 0 1 by decide)
  obtain ⟨B, hB, pureB, _⟩ := opposite_inelig_mem h hc h2 (show adj 2 1 by decide)
  obtain ⟨C, hC, hbarC, _, _, _⟩ := sem_edge_slots graph_ok h.1 hc (show adj 1 6 by decide)
  have sixC : (6 : V) ∈ supp 10 D (src D (sem_bar C)) := (sem_mem_W.mp hbarC).2.1
  have exitF : F ∈ sem_W 10 D (1 : V) := by
    refine sem_mem_W.mpr ⟨hF, oneF, ?_⟩
    intro ho
    have hm := sem_supp_and_sub h.1 hF tF (!F.2) ho
    change (1 : V) ∈ supp 10 D (src D (sem_bar F)) at hm
    rw [emptyF] at hm
    exact Finset.notMem_empty _ hm
  have apart {e : ℕ × Bool} {x : V}
      (hx : x ∈ supp 10 D (src D (sem_bar e))) : e ≠ F := by
    intro he
    rw [he, emptyF] at hx
    exact Finset.notMem_empty _ hx
  have neAF : A ≠ F := apart (show (0 : V) ∈ supp 10 D (src D (sem_bar A)) by rw [pureA]; simp)
  have neBF : B ≠ F := apart (show (2 : V) ∈ supp 10 D (src D (sem_bar B)) by rw [pureB]; simp)
  have neCF : C ≠ F := apart sixC
  have neAB : A ≠ B := by
    intro he
    have eq := Finset.singleton_injective (pureA.symm.trans (he ▸ pureB))
    exact (by decide : (0 : V) ≠ 2) eq
  have neCA : C ≠ A := by
    intro he
    rw [he, pureA, Finset.mem_singleton] at sixC
    exact (by decide : (6 : V) ≠ 0) sixC
  have neCB : C ≠ B := by
    intro he
    rw [he, pureB, Finset.mem_singleton] at sixC
    exact (by decide : (6 : V) ≠ 2) sixC
  have sub : ({A, B, C, F} : Finset (ℕ × Bool)) ⊆ sem_W 10 D (1 : V) := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl <;> assumption
  have four : ({A, B, C, F} : Finset (ℕ × Bool)).card = 4 := by
    simp [neAB, Ne.symm neCA, neAF, Ne.symm neCB, neBF, neCF]
  have le := Finset.card_le_card sub
  omega

lemma private_filter_i2_with_caps {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (small : D.length ≤ 19) (hi : (ineligSet 10 D).card = 2)
    (h0 : (0 : V) ∈ ineligSet 10 D) (h2 : (2 : V) ∈ ineligSet 10 D)
    (cap4 : (sem_W 10 D (4 : V)).card ≤ 3)
    (cap5 : (sem_W 10 D (5 : V)).card ≤ 3)
    {F : ℕ × Bool} (hF : F.1 < D.length) (tF : tag D F.1 = true)
    (emptyF : supp 10 D (src D (sem_bar F)) = ∅)
    (neighborsF : ∀ x : V, adj 0 x → x ∈ supp 10 D (src D F)) : False := by
  classical
  obtain ⟨b, hb⟩ := sem_exists_pureBranch graph_ok h.1 hc
  have tight := two_ineligible_tight h hc small hi
  have complement := inelig_card_add 10 D
  have residual := card_residual h.1 b hb
  have cap : (residualUnits 10 D b).card ≤ 2 := by omega
  have four := private_filter_four_exits h hc h0 h2 hF tF emptyF (neighborsF 1 (by decide))
  obtain ⟨size1, _, _, both⟩ := four_exits_two_residuals graph_ok h hc b hb four cap
  obtain ⟨B, _, _, neighborsB⟩ := opposite_inelig_mem h hc h2 (show adj 2 1 by decide)
  have unique_free (x : V) (hx : adj 2 x) (hx1 : x ≠ 1) :
      ∀ e ∈ sem_W 10 D x, ∀ f ∈ sem_W 10 D x,
        (1 : V) ∉ supp 10 D (src D e) → (1 : V) ∉ supp 10 D (src D f) → e = f := by
    have eligible : x ∈ eligSet 10 D := by
      rcases sem_elig_cover graph_ok h hc hx with he | he
      · exact False.elim ((sem_mem_inelig.mp h2) he)
      · exact he
    obtain ⟨e0, he0⟩ := ri_gen graph_ok h hc b hb hx1 eligible
      (fun u hu _ => both u hu)
      (show x ∈ supp 10 D (src D B) ∧ (1 : V) ∈ supp 10 D (src D B) from
        ⟨neighborsB x hx, neighborsB 1 (by decide)⟩)
    intro e he f hf hne hnf
    have ee : e = e0 := by
      by_contra hn
      exact hne (he0 e he hn)
    have fe : f = e0 := by
      by_contra hn
      exact hnf (he0 f hf hn)
    exact ee.trans fe.symm
  exact private_filter_no_free_support_reconstructed h hc h0 h2 (by omega) cap4 cap5
    (unique_free 3 (by decide) (by decide)) (unique_free 7 (by decide) (by decide))
    hF tF emptyF neighborsF

end PEqualNP.Outside.L_meta_2590_aux

namespace PEqualNP.Outside.L_meta_2590_aux

open DagTools

lemma private_filter_i2 {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (small : D.length ≤ 19) (hi : (ineligSet 10 D).card = 2)
    (h0 : (0 : V) ∈ ineligSet 10 D) (h2 : (2 : V) ∈ ineligSet 10 D)
    {F : ℕ × Bool} (hF : F.1 < D.length) (tF : tag D F.1 = true)
    (emptyF : supp 10 D (src D (sem_bar F)) = ∅)
    (neighborsF : ∀ x : V, adj 0 x → x ∈ supp 10 D (src D F)) : False := by
  obtain ⟨b, hb⟩ := sem_exists_pureBranch graph_ok h.1 hc
  have caps := petersen_two_ineligible_code_caps h hc small hi h0 h2 b hb
  exact private_filter_i2_with_caps h hc small hi h0 h2
    (caps.2.2 4 (by decide)).2.2 (caps.2.2 5 (by decide)).2.2
    hF tF emptyF neighborsF

end PEqualNP.Outside.L_meta_2590_aux

namespace PEqualNP.Outside.L_meta_2590_aux

open DagTools

lemma private_filter_two_no_free_support_reconstructed {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (h0 : (2 : V) ∈ ineligSet 10 D) (h2 : (0 : V) ∈ ineligSet 10 D)
    (cap1 : (sem_W 10 D (1 : V)).card ≤ 4)
    (cap4 : (sem_W 10 D (3 : V)).card ≤ 3)
    (cap5 : (sem_W 10 D (7 : V)).card ≤ 3)
    (free3 : ∀ e ∈ sem_W 10 D (4 : V), ∀ f ∈ sem_W 10 D (4 : V),
      (1 : V) ∉ supp 10 D (src D e) → (1 : V) ∉ supp 10 D (src D f) → e = f)
    (free7 : ∀ e ∈ sem_W 10 D (5 : V), ∀ f ∈ sem_W 10 D (5 : V),
      (1 : V) ∉ supp 10 D (src D e) → (1 : V) ∉ supp 10 D (src D f) → e = f)
    {F : ℕ × Bool} (hF : F.1 < D.length) (tF : tag D F.1 = true)
    (emptyF : supp 10 D (src D (sem_bar F)) = ∅)
    (neighborsF : ∀ x : V, adj 2 x → x ∈ supp 10 D (src D F)) : False := by
  classical
  obtain ⟨A, hA1, pureA, neighborsA⟩ := opposite_inelig_mem h hc h0 (show adj 2 1 by decide)
  obtain ⟨B, hB1, pureB, neighborsB⟩ := opposite_inelig_mem h hc h2 (show adj 0 1 by decide)
  have A_neighbors (x : V) (hx : adj 2 x) (hne : x ≠ 2) : A ∈ sem_W 10 D x := by
    have hj := (sem_mem_W.mp hA1).1
    refine sem_mem_W.mpr ⟨hj, neighborsA x hx, ?_⟩
    intro ho
    have hm := sem_supp_and_sub h.1 hj (sem_W_and h.1 hA1) (!A.2) ho
    change x ∈ supp 10 D (src D (sem_bar A)) at hm
    rw [pureA, Finset.mem_singleton] at hm
    exact hne hm
  have F_neighbors (x : V) (hx : adj 2 x) : F ∈ sem_W 10 D x := by
    refine sem_mem_W.mpr ⟨hF, neighborsF x hx, ?_⟩
    intro ho
    have hm := sem_supp_and_sub h.1 hF tF (!F.2) ho
    change x ∈ supp 10 D (src D (sem_bar F)) at hm
    rw [emptyF] at hm
    exact Finset.notMem_empty x hm
  have hA4 := A_neighbors 3 (by decide) (by decide)
  have hA5 := A_neighbors 7 (by decide) (by decide)
  have hF1 := F_neighbors 1 (by decide)
  have hF4 := F_neighbors 3 (by decide)
  have hF5 := F_neighbors 7 (by decide)
  have neAF : A ≠ F := by
    intro he
    have hm : (2 : V) ∈ supp 10 D (src D (sem_bar A)) := by rw [pureA]; simp
    rw [he, emptyF] at hm
    exact Finset.notMem_empty _ hm
  have neAB : A ≠ B := by
    intro he
    have eq := Finset.singleton_injective (pureA.symm.trans (he ▸ pureB))
    exact (by decide : (2 : V) ≠ 0) eq
  have neBF : B ≠ F := by
    intro he
    have hm : (0 : V) ∈ supp 10 D (src D (sem_bar B)) := by rw [pureB]; simp
    rw [he, emptyF] at hm
    exact Finset.notMem_empty _ hm
  have edge_other {e : ℕ × Bool} {x : V}
      (hx : x ∈ supp 10 D (src D (sem_bar e))) (hx0 : x ≠ 2) : e ≠ A ∧ e ≠ F := by
    constructor
    · intro he
      rw [he, pureA, Finset.mem_singleton] at hx
      exact hx0 hx
    · intro he
      rw [he, emptyF] at hx
      exact Finset.notMem_empty _ hx
  obtain ⟨H4, hH4, hbarH4, _, _, _⟩ := sem_edge_slots graph_ok h.1 hc (show adj 3 4 by decide)
  obtain ⟨J4, hJ4, hbarJ4, _, _, _⟩ := sem_edge_slots graph_ok h.1 hc (show adj 3 8 by decide)
  have h3 : (4 : V) ∈ supp 10 D (src D (sem_bar H4)) := (sem_mem_W.mp hbarH4).2.1
  have h9J : (8 : V) ∈ supp 10 D (src D (sem_bar J4)) := (sem_mem_W.mp hbarJ4).2.1
  have ne4 := edge_other h3 (by decide)
  have neJ4 := edge_other h9J (by decide)
  have cases4 (e) (he : e ∈ sem_W 10 D (3 : V)) : e = A ∨ e = F ∨ e = H4 :=
    mem_three_of_card_le cap4 hA4 hF4 hH4 neAF ne4.1.symm ne4.2.symm he
  have eqJ4 : J4 = H4 := by
    rcases cases4 J4 hJ4 with he | he | he
    · exact False.elim (neJ4.1 he)
    · exact False.elim (neJ4.2 he)
    · exact he
  have h9 : (8 : V) ∈ supp 10 D (src D (sem_bar H4)) := eqJ4 ▸ h9J
  obtain ⟨H5, hH5, hbarH5, _, _, _⟩ := sem_edge_slots graph_ok h.1 hc (show adj 7 5 by decide)
  obtain ⟨J5, hJ5, hbarJ5, _, _, _⟩ := sem_edge_slots graph_ok h.1 hc (show adj 7 9 by decide)
  have h7 : (5 : V) ∈ supp 10 D (src D (sem_bar H5)) := (sem_mem_W.mp hbarH5).2.1
  have h8J : (9 : V) ∈ supp 10 D (src D (sem_bar J5)) := (sem_mem_W.mp hbarJ5).2.1
  have ne5 := edge_other h7 (by decide)
  have neJ5 := edge_other h8J (by decide)
  have cases5 (e) (he : e ∈ sem_W 10 D (7 : V)) : e = A ∨ e = F ∨ e = H5 :=
    mem_three_of_card_le cap5 hA5 hF5 hH5 neAF ne5.1.symm ne5.2.symm he
  have eqJ5 : J5 = H5 := by
    rcases cases5 J5 hJ5 with he | he | he
    · exact False.elim (neJ5.1 he)
    · exact False.elim (neJ5.2 he)
    · exact he
  have h8 : (9 : V) ∈ supp 10 D (src D (sem_bar H5)) := eqJ5 ▸ h8J
  have H4free : (1 : V) ∉ supp 10 D (src D H4) ∧ (7 : V) ∉ supp 10 D (src D H4) := by
    obtain ⟨e, he, he1, he5⟩ := sem_cover_free graph_ok h.1 hc
      (show ¬ adj 1 7 by decide) (show adj 3 4 by decide)
      (show ¬ adj 4 1 by decide) (show ¬ adj 4 7 by decide)
    rcases cases4 e he with rfl | rfl | rfl
    · exact False.elim (he1 (neighborsA 1 (by decide)))
    · exact False.elim (he1 (neighborsF 1 (by decide)))
    · exact ⟨he1, he5⟩
  have H5free : (1 : V) ∉ supp 10 D (src D H5) := by
    obtain ⟨e, he, he1, _⟩ := sem_cover_free graph_ok h.1 hc
      (show ¬ adj 1 3 by decide) (show adj 7 5 by decide)
      (show ¬ adj 5 1 by decide) (show ¬ adj 5 3 by decide)
    rcases cases5 e he with rfl | rfl | rfl
    · exact False.elim (he1 (neighborsA 1 (by decide)))
    · exact False.elim (he1 (neighborsF 1 (by decide)))
    · exact he1
  have barH4one : (1 : V) ∈ supp 10 D (src D (sem_bar H4)) := by
    by_contra hn
    obtain ⟨e, he, he1, he9⟩ := sem_cover_free graph_ok h.1 hc
      (show ¬ adj 1 8 by decide) (show adj 4 9 by decide)
      (show ¬ adj 9 1 by decide) (show ¬ adj 9 8 by decide)
    exact he9 ((free3 _ hbarH4 _ he hn he1) ▸ h9)
  have barH5one : (1 : V) ∈ supp 10 D (src D (sem_bar H5)) := by
    by_contra hn
    obtain ⟨e, he, he1, he8⟩ := sem_cover_free graph_ok h.1 hc
      (show ¬ adj 1 9 by decide) (show adj 5 8 by decide)
      (show ¬ adj 8 1 by decide) (show ¬ adj 8 9 by decide)
    exact he8 ((free7 _ hbarH5 _ he hn he1) ▸ h8)
  have bar_exit {e : ℕ × Bool} {x : V} (he : e ∈ sem_W 10 D x)
      (hno : (1 : V) ∉ supp 10 D (src D e))
      (hyes : (1 : V) ∈ supp 10 D (src D (sem_bar e))) : sem_bar e ∈ sem_W 10 D (1 : V) := by
    have hj := (sem_mem_W.mp he).1
    refine sem_mem_W.mpr ⟨hj, hyes, ?_⟩
    intro ho
    exact hno (sem_supp_and_sub h.1 hj (sem_W_and h.1 he) e.2 ho)
  have hbar41 := bar_exit hH4 H4free.1 barH4one
  have hbar51 := bar_exit hH5 H5free barH5one
  have bar_apart {e : ℕ × Bool} {x : V} (hx : x ∈ supp 10 D (src D e))
      (hx0 : x ≠ 2) (hx2 : x ≠ 0) : sem_bar e ≠ A ∧ sem_bar e ≠ B ∧ sem_bar e ≠ F := by
    have hbar : x ∈ supp 10 D (src D (sem_bar (sem_bar e))) := by simpa only [sem_bar_bar] using hx
    have aa := edge_other hbar hx0
    refine ⟨aa.1, ?_, aa.2⟩
    intro he
    rw [he, pureB, Finset.mem_singleton] at hbar
    exact hx2 hbar
  have nebar4 := bar_apart (sem_mem_W.mp hH4).2.1 (by decide) (by decide)
  have nebar5 := bar_apart (sem_mem_W.mp hH5).2.1 (by decide) (by decide)
  have same : sem_bar H4 = sem_bar H5 := by
    by_contra hn
    have sub : ({A, B, F, sem_bar H4, sem_bar H5} : Finset (ℕ × Bool)) ⊆ sem_W 10 D (1 : V) := by
      intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl | rfl | rfl <;> assumption
    have five : ({A, B, F, sem_bar H4, sem_bar H5} : Finset (ℕ × Bool)).card = 5 := by
      simp [neAB, neAF, neBF, Ne.symm nebar4.1, Ne.symm nebar4.2.1,
        Ne.symm nebar4.2.2, Ne.symm nebar5.1, Ne.symm nebar5.2.1, Ne.symm nebar5.2.2, hn]
    have le := Finset.card_le_card sub
    omega
  have eq : H4 = H5 := r1_bar_inj same
  apply H4free.2
  rw [eq]
  exact (sem_mem_W.mp hH5).2.1

end PEqualNP.Outside.L_meta_2590_aux

namespace PEqualNP.Outside.L_meta_2590_aux

open DagTools

lemma private_filter_two_i2_with_caps {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (small : D.length ≤ 19) (hi : (ineligSet 10 D).card = 2)
    (h0 : (2 : V) ∈ ineligSet 10 D) (h2 : (0 : V) ∈ ineligSet 10 D)
    (cap4 : (sem_W 10 D (3 : V)).card ≤ 3)
    (cap5 : (sem_W 10 D (7 : V)).card ≤ 3)
    {F : ℕ × Bool} (hF : F.1 < D.length) (tF : tag D F.1 = true)
    (emptyF : supp 10 D (src D (sem_bar F)) = ∅)
    (neighborsF : ∀ x : V, adj 2 x → x ∈ supp 10 D (src D F)) : False := by
  classical
  obtain ⟨b, hb⟩ := sem_exists_pureBranch graph_ok h.1 hc
  have tight := two_ineligible_tight h hc small hi
  have complement := inelig_card_add 10 D
  have residual := card_residual h.1 b hb
  have cap : (residualUnits 10 D b).card ≤ 2 := by omega
  have four := private_filter_four_exits h hc h2 h0 hF tF emptyF (neighborsF 1 (by decide))
  obtain ⟨size1, _, _, both⟩ := four_exits_two_residuals graph_ok h hc b hb four cap
  obtain ⟨B, _, _, neighborsB⟩ := opposite_inelig_mem h hc h2 (show adj 0 1 by decide)
  have unique_free (x : V) (hx : adj 0 x) (hx1 : x ≠ 1) :
      ∀ e ∈ sem_W 10 D x, ∀ f ∈ sem_W 10 D x,
        (1 : V) ∉ supp 10 D (src D e) → (1 : V) ∉ supp 10 D (src D f) → e = f := by
    have eligible : x ∈ eligSet 10 D := by
      rcases sem_elig_cover graph_ok h hc hx with he | he
      · exact False.elim ((sem_mem_inelig.mp h2) he)
      · exact he
    obtain ⟨e0, he0⟩ := ri_gen graph_ok h hc b hb hx1 eligible
      (fun u hu _ => both u hu)
      (show x ∈ supp 10 D (src D B) ∧ (1 : V) ∈ supp 10 D (src D B) from
        ⟨neighborsB x hx, neighborsB 1 (by decide)⟩)
    intro e he f hf hne hnf
    have ee : e = e0 := by
      by_contra hn
      exact hne (he0 e he hn)
    have fe : f = e0 := by
      by_contra hn
      exact hnf (he0 f hf hn)
    exact ee.trans fe.symm
  exact private_filter_two_no_free_support_reconstructed h hc h0 h2 (by omega) cap4 cap5
    (unique_free 4 (by decide) (by decide)) (unique_free 5 (by decide) (by decide))
    hF tF emptyF neighborsF

end PEqualNP.Outside.L_meta_2590_aux

namespace PEqualNP.Outside.L_meta_2590_aux

open DagTools

lemma private_filter_two_i2 {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (small : D.length ≤ 19) (hi : (ineligSet 10 D).card = 2)
    (h0 : (0 : V) ∈ ineligSet 10 D) (h2 : (2 : V) ∈ ineligSet 10 D)
    {F : ℕ × Bool} (hF : F.1 < D.length) (tF : tag D F.1 = true)
    (emptyF : supp 10 D (src D (sem_bar F)) = ∅)
    (neighborsF : ∀ x : V, adj 2 x → x ∈ supp 10 D (src D F)) : False := by
  obtain ⟨b, hb⟩ := sem_exists_pureBranch graph_ok h.1 hc
  have caps := petersen_two_ineligible_code_caps h hc small hi h0 h2 b hb
  exact private_filter_two_i2_with_caps h hc small hi h2 h0
    (caps.2.2 3 (by decide)).2.2 (caps.2.2 7 (by decide)).2.2
    hF tF emptyF neighborsF

end PEqualNP.Outside.L_meta_2590_aux

namespace PEqualNP.Outside.L_meta_2590_aux.DagTools

section LocalTerminalSupport
variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

lemma sem_arm_step_support_mono (hS : Strict n D)
    {X : Finset (Fin n)} (hX : X.Nonempty)
    (hM : ∀ x ∈ X, merges n D (carrierT n D {x}) = ∅)
    {a c : ℕ} (ha : sem_Arm n D X a c) : supp n D a ⊆ supp n D c := by
  obtain ⟨x, hx⟩ := hX
  obtain ⟨j, s, hj, hceq, hs⟩ := sem_step_iff.mp ha.1
  have hxc : x ∈ supp n D (n + j) := by
    rw [← hceq]
    exact (ha.2.2 x hx).2
  have ht := (sem_zm_gate hS (hM x hx) hj hxc).1
  rw [hceq, sem_supp_or hS hj ht]
  cases s
  · rw [sb_src_false] at hs
    rw [hs]
    exact Finset.subset_union_left
  · rw [sb_src_true] at hs
    rw [hs]
    exact Finset.subset_union_right

lemma sem_arm_support_mono (hS : Strict n D)
    {X : Finset (Fin n)} (hX : X.Nonempty)
    (hM : ∀ x ∈ X, merges n D (carrierT n D {x}) = ∅)
    {a c : ℕ} (ha : Relation.ReflTransGen (sem_Arm n D X) a c) :
    supp n D a ⊆ supp n D c := by
  induction ha with
  | refl => intro v hv; exact hv
  | tail _ hstep ih => exact ih.trans (sem_arm_step_support_mono hS hX hM hstep)

lemma sem_two_arms_support (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (X : Finset (Fin n)) (hX : X.Nonempty)
    (hM : ∀ x ∈ X, merges n D (carrierT n D {x}) = ∅) (r : ℕ)
    (hr : ∀ x ∈ X, x ∈ supp n D r) (hf : 2 ≤ fanout D r)
    (hlow : ∀ x ∈ X, ∀ w, r < w → x ∈ supp n D w → fanout D w ≤ 1) :
    ∃ P Q : ℕ × Bool, P.1 ≠ Q.1 ∧
      (∀ x ∈ X, P ∈ sem_W n D x ∧ Q ∈ sem_W n D x) ∧
      supp n D r ⊆ supp n D (src D P) ∧ supp n D r ⊆ supp n D (src D Q) := by
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
      ((e.1 = j ∧ src D e = r) ∨ Relation.ReflTransGen (sem_Arm n D X) (n + j) (src D e)) ∧
      supp n D r ⊆ supp n D (src D e) := by
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
      have hsub : supp n D r ⊆ supp n D (n + j) := by
        rw [sem_supp_or hS hjl ht]
        rcases hop with ha | hb
        · rw [ha]
          exact Finset.subset_union_left
        · rw [hb]
          exact Finset.subset_union_right
      exact ⟨e, he1, Or.inr he2,
        hsub.trans (sem_arm_support_mono hS ⟨x0, hx0⟩ hM he2)⟩
    · exact ⟨(j, s), fun x hx => sem_mem_W.mpr ⟨hjl, by rw [hs]; exact hr x hx,
        fun hc2 => hcar ⟨x, hx, hc2⟩⟩, Or.inl ⟨rfl, hs⟩, by rw [hs]⟩
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
  obtain ⟨P, hP1, hP2, hPs⟩ := hterm j1 hj1
  obtain ⟨Q, hQ1, hQ2, hQs⟩ := hterm j2 hj2
  refine ⟨P, Q, fun hPQ => ?_, fun x hx => ⟨hP1 x hx, hQ1 x hx⟩, hPs, hQs⟩
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

lemma sem_local_saturated (hG : sem_Gr G) (h : StrictLive n D)
    (hC : sem_Comp n G D) (b : Fin n → ℕ) (hb : PureBranch n D b)
    (u0 : Σ _ : ℕ, ℕ) (x : Fin n)
    (hcode : (residualUnits n D b).filter (fun u => x ∈ supp n D u.1) = {u0})
    (hsat : 3 ≤ (sem_W n D x).card) :
    (sem_W n D x).card = 3 ∧ merges n D (carrierT n D {x}) = ∅ ∧
      x ∈ eligSet n D ∧ x ∈ supp n D u0.1 := by
  have hcount := sem_code_count hG h hC b hb x
  rw [hcode, Finset.card_singleton] at hcount
  have hone : (({x} : Finset (Fin n)) ∩ eligSet n D).card ≤ 1 :=
    (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
  refine ⟨by omega, Finset.card_eq_zero.mp (by omega), ?_, ?_⟩
  · by_contra hx
    have hempty : ({x} : Finset (Fin n)) ∩ eligSet n D = ∅ :=
      Finset.singleton_inter_of_notMem hx
    rw [hempty, Finset.card_empty] at hcount
    omega
  · have hu : u0 ∈ (residualUnits n D b).filter (fun u => x ∈ supp n D u.1) := by
      rw [hcode]
      exact Finset.mem_singleton_self _
    exact (Finset.mem_filter.mp hu).2

lemma sem_local_common_terminals_support (hG : sem_Gr G) (h : StrictLive n D)
    (hC : sem_Comp n G D) (b : Fin n → ℕ) (hb : sem_MinBranch n D b)
    (X : Finset (Fin n)) (hX : X.Nonempty) (u0 : Σ _ : ℕ, ℕ)
    (hcode : ∀ x ∈ X,
      (residualUnits n D b).filter (fun u => x ∈ supp n D u.1) = {u0})
    (hsat : ∀ x ∈ X, 3 ≤ (sem_W n D x).card) :
    ∃ P Q : ℕ × Bool, P.1 ≠ Q.1 ∧
      (∀ x ∈ X, P ∈ sem_W n D x ∧ Q ∈ sem_W n D x) ∧
      supp n D u0.1 ⊆ supp n D (src D P) ∧ supp n D u0.1 ⊆ supp n D (src D Q) := by
  have hS := h.1
  have hbp := sem_minBranch_pure hb
  obtain ⟨x0, hx0⟩ := hX
  have hu0 : u0 ∈ residualUnits n D b := by
    have hh : u0 ∈ (residualUnits n D b).filter (fun u => x0 ∈ supp n D u.1) := by
      rw [hcode x0 hx0]
      exact Finset.mem_singleton_self _
    exact (Finset.mem_filter.mp hh).1
  have hu0u : u0 ∈ units n D :=
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp hu0).1).1
  have hfr : 2 ≤ fanout D u0.1 := by
    have := (mem_units.mp hu0u).2
    omega
  have facts (x : Fin n) (hx : x ∈ X) :=
    sem_local_saturated hG h hC b hbp u0 x (hcode x hx) (hsat x hx)
  refine sem_two_arms_support hG h hC X ⟨x0, hx0⟩
    (fun x hx => (facts x hx).2.1) u0.1 (fun x hx => (facts x hx).2.2.2) hfr ?_
  intro x hx w hrw hxw
  obtain ⟨_, _, hxe, hxr⟩ := facts x hx
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
    have hwcode : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈
        (residualUnits n D b).filter (fun u => x ∈ supp n D u.1) :=
      Finset.mem_filter.mpr ⟨hwres, hxw⟩
    rw [hcode x hx, Finset.mem_singleton] at hwcode
    have heq : w = u0.1 := congrArg Sigma.fst hwcode
    omega

end LocalTerminalSupport

lemma s45_residual_support {G : Fin 10 → Fin 10 → Prop} {D : Dag}
    (hG : sem_Gr G) (h : StrictLive 10 D) (hC : sem_Comp 10 G D)
    (b : Fin 10 → ℕ) (hb : sem_MinBranch 10 D b) (u0 : Σ _ : ℕ, ℕ)
    (hcode : ∀ x ∈ ({4, 5} : Finset (Fin 10)),
      (residualUnits 10 D b).filter (fun u => x ∈ supp 10 D u.1) = {u0})
    (hsat : ∀ x ∈ ({4, 5} : Finset (Fin 10)), 3 ≤ (sem_W 10 D x).card)
    (A Z : ℕ × Bool)
    (hcommon : ∀ e, e ∈ sem_W 10 D (4 : Fin 10) → e ∈ sem_W 10 D (5 : Fin 10) →
      e = A ∨ e = Z)
    (hA : supp 10 D (src D A) = {1, 4, 5})
    (hone : (1 : Fin 10) ∉ supp 10 D u0.1) : supp 10 D u0.1 = {4, 5} := by
  obtain ⟨P, Q, hPQ, hm, hP, hQ⟩ := sem_local_common_terminals_support
    hG h hC b hb {4, 5} (by simp) u0 hcode hsat
  have hPa := hcommon P (hm 4 (by simp)).1 (hm 5 (by simp)).1
  have hQa := hcommon Q (hm 4 (by simp)).2 (hm 5 (by simp)).2
  have hRA : supp 10 D u0.1 ⊆ supp 10 D (src D A) := by
    rcases hPa with rfl | hPZ
    · exact hP
    rcases hQa with rfl | hQZ
    · exact hQ
    exact False.elim (hPQ (by rw [hPZ, hQZ]))
  rw [hA] at hRA
  have hin (x : Fin 10) (hx : x ∈ ({4, 5} : Finset (Fin 10))) : x ∈ supp 10 D u0.1 := by
    have hu : u0 ∈ (residualUnits 10 D b).filter (fun u => x ∈ supp 10 D u.1) := by
      rw [hcode x hx]
      exact Finset.mem_singleton_self _
    exact (Finset.mem_filter.mp hu).2
  apply Finset.Subset.antisymm
  · intro x hx
    have hm := hRA hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm ⊢
    rcases hm with rfl | h4 | h5
    · exact False.elim (hone hx)
    · exact Or.inl h4
    · exact Or.inr h5
  · exact hin

end PEqualNP.Outside.L_meta_2590_aux.DagTools

namespace PEqualNP.Outside.L_meta_2590_aux.DagTools

lemma sem_sat_of_flow {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}
    (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (b : Fin n → ℕ) (hb : PureBranch n D b)
    (E : Finset (ℕ × Bool)) (L : (ℕ × Bool) → Finset (Fin n))
    (hsub : ∀ x : Fin n, E.filter (fun e => x ∈ L e) ⊆ sem_W n D x)
    (hbudget : ∀ x : Fin n,
      1 + (({x} : Finset (Fin n)) ∩ eligSet n D).card +
        ((residualUnits n D b).filter (fun u => x ∈ supp n D u.1)).card ≤
          (E.filter (fun e => x ∈ L e)).card) :
    (∀ x : Fin n, sem_W n D x = E.filter (fun e => x ∈ L e)) ∧
      ∀ x : Fin n, merges n D (carrierT n D {x}) = ∅ := by
  have hpair (x : Fin n) :
      sem_W n D x = E.filter (fun e => x ∈ L e) ∧
        merges n D (carrierT n D {x}) = ∅ := by
    have hflow := sem_code_count hG h hC b hb x
    have hcard := Finset.card_le_card (hsub x)
    have hbound := hbudget x
    have hle : (sem_W n D x).card ≤ (E.filter (fun e => x ∈ L e)).card := by
      omega
    have heq : E.filter (fun e => x ∈ L e) = sem_W n D x :=
      Finset.eq_of_subset_of_card_le (hsub x) hle
    exact ⟨heq.symm, Finset.card_eq_zero.mp (by omega)⟩
  exact ⟨fun x => (hpair x).1, fun x => (hpair x).2⟩

lemma sem_sat_and_supp_empty {n : ℕ} {D : Dag} (hS : Strict n D)
    (hM : ∀ x : Fin n, merges n D (carrierT n D {x}) = ∅)
    {j : ℕ} (hj : j < D.length) (ht : tag D j = true) :
    supp n D (n + j) = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro x hx
  have htag := (sem_zm_gate hS (hM x) hj hx).1
  have hbad : (true : Bool) = false := ht.symm.trans htag
  cases hbad

lemma sem_sat_mem_W_iff_src {n : ℕ} {D : Dag} (hS : Strict n D)
    (hM : ∀ x : Fin n, merges n D (carrierT n D {x}) = ∅)
    {e : ℕ × Bool} (he : e.1 < D.length) (ht : tag D e.1 = true) (x : Fin n) :
    e ∈ sem_W n D x ↔ x ∈ supp n D (src D e) := by
  constructor
  · intro hx
    exact (sem_mem_W.mp hx).2.1
  · intro hx
    apply sem_mem_W.mpr
    refine ⟨he, hx, ?_⟩
    rw [sem_sat_and_supp_empty hS hM he ht]
    exact Finset.notMem_empty x

lemma sem_sat_src_eq_label {n : ℕ} {D : Dag} (hS : Strict n D)
    (hM : ∀ x : Fin n, merges n D (carrierT n D {x}) = ∅)
    (E : Finset (ℕ × Bool)) (L : (ℕ × Bool) → Finset (Fin n))
    (hW : ∀ x : Fin n, sem_W n D x = E.filter (fun e => x ∈ L e))
    {e : ℕ × Bool} (he : e.1 < D.length) (ht : tag D e.1 = true) :
    supp n D (src D e) = if e ∈ E then L e else ∅ := by
  ext x
  calc
    x ∈ supp n D (src D e) ↔ e ∈ sem_W n D x :=
      (sem_sat_mem_W_iff_src hS hM he ht x).symm
    _ ↔ x ∈ (if e ∈ E then L e else ∅) := by
      rw [hW x]
      by_cases h : e ∈ E <;> simp [h]

lemma sem_sat_and_selected_or_empty {n : ℕ} {D : Dag} (hS : Strict n D)
    (hM : ∀ x : Fin n, merges n D (carrierT n D {x}) = ∅)
    (E : Finset (ℕ × Bool))
    (hbar : ∀ e ∈ E, sem_bar e ∈ E)
    (hcover : ∀ x : Fin n, sem_W n D x ⊆ E)
    {j : ℕ} (hj : j < D.length) (ht : tag D j = true) :
    (j, false) ∈ E ∨
      (supp n D (opA D j) = ∅ ∧ supp n D (opB D j) = ∅) := by
  by_cases he : (j, false) ∈ E
  · exact Or.inl he
  · refine Or.inr ⟨?_, ?_⟩
    · apply Finset.eq_empty_of_forall_notMem
      intro x hx
      have hx' : x ∈ supp n D (src D (j, false)) := by simpa [src] using hx
      have hw : (j, false) ∈ sem_W n D x :=
        (sem_sat_mem_W_iff_src hS hM (e := (j, false)) hj ht x).mpr hx'
      exact he (hcover x hw)
    · apply Finset.eq_empty_of_forall_notMem
      intro x hx
      have hx' : x ∈ supp n D (src D (j, true)) := by simpa [src] using hx
      have hw : (j, true) ∈ sem_W n D x :=
        (sem_sat_mem_W_iff_src hS hM (e := (j, true)) hj ht x).mpr hx'
      have hmem := hbar (j, true) (hcover x hw)
      exact he (by simpa [sem_bar] using hmem)

lemma sem_sat_and_signature {n : ℕ} {D : Dag} (hS : Strict n D)
    (hM : ∀ x : Fin n, merges n D (carrierT n D {x}) = ∅)
    (E : Finset (ℕ × Bool)) (L : (ℕ × Bool) → Finset (Fin n))
    (hbar : ∀ e ∈ E, sem_bar e ∈ E)
    (hW : ∀ x : Fin n, sem_W n D x = E.filter (fun e => x ∈ L e))
    {j : ℕ} (hj : j < D.length) (ht : tag D j = true) :
    ((j, false) ∈ E ∧ supp n D (opA D j) = L (j, false) ∧
      supp n D (opB D j) = L (j, true)) ∨
      (supp n D (opA D j) = ∅ ∧ supp n D (opB D j) = ∅) := by
  have hcover (x : Fin n) : sem_W n D x ⊆ E := by
    intro e he
    rw [hW x] at he
    exact (Finset.mem_filter.mp he).1
  rcases sem_sat_and_selected_or_empty hS hM E hbar hcover hj ht with he | hz
  · have he' : (j, true) ∈ E := by simpa [sem_bar] using hbar (j, false) he
    refine Or.inl ⟨he, ?_, ?_⟩
    · simpa [src, he] using
        sem_sat_src_eq_label hS hM E L hW (e := (j, false)) hj ht
    · simpa [src, he'] using
        sem_sat_src_eq_label hS hM E L hW (e := (j, true)) hj ht
  · exact Or.inr hz

end PEqualNP.Outside.L_meta_2590_aux.DagTools

namespace PEqualNP.Outside.L_meta_2590_aux.DagTools

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

lemma unique_reachable_and_of_no_empty_filter
    (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (hz : Bzero n D = 0) {i : Fin n} (hi : i ∈ ineligSet n D)
    (noFilter : ∀ F : ℕ × Bool, F.1 < D.length → tag D F.1 = true →
      supp n D (src D (sem_bar F)) = ∅ →
      (∀ a : Fin n, G i a → a ∈ supp n D (src D F)) → False) :
    ∃ e : ℕ × Bool,
      e.1 < D.length ∧ tag D e.1 = true ∧
      supp n D (src D e) = {i} ∧ supp n D (n + e.1) = ∅ ∧
      sem_Chain n D i.val (src D e) ∧ fanout D (src D e) = 1 ∧
      (∀ a : Fin n, G i a → a ∈ supp n D (src D (sem_bar e))) ∧
      ∀ g, g < D.length → tag D g = true →
        Relation.ReflTransGen (sem_step n D) i.val (n + g) → g = e.1 := by
  classical
  obtain ⟨e, he, ht, hp, hout, hn, hexits, _⟩ := sem_inelig_consumer hG h hC hi
  have himem : i ∈ supp n D (src D e) := by rw [hp]; simp
  have hleft : sem_Chain n D i.val (src D e) := sem_inelig_chain h.1 hi himem
  have hfan : fanout D (src D e) = 1 := by
    have hle := mem_ineligSet.mp hi (src D e) himem
    have hpos := sem_step_fanout (sem_step_src (n := n) (D := D) he e.2)
    change 1 ≤ fanout D (src D e) at hpos
    omega
  refine ⟨e, he, ht, hp, hout, hleft, hfan, hn, ?_⟩
  intro g hg hand path
  rcases Relation.ReflTransGen.cases_tail path with eq | ⟨u, prev, last⟩
  · have hil := i.isLt
    omega
  · obtain ⟨j, s, hj, eq, hs⟩ := sem_step_iff.mp last
    have jg : j = g := by omega
    subst j
    rw [← hs] at prev
    have chain := sem_noempty_unique hG h hC hz hi prev
    have fan : fanout D (src D (g,s)) = 1 := by
      have hle := ineligible_reachable_fanout hG h hC hz hi prev
      have hpos := sem_step_fanout (sem_step_src (n := n) (D := D) hg s)
      omega
    have neighbors : ∀ a : Fin n, G i a → a ∈ supp n D (src D (g,!s)) := by
      intro a ha
      exact (sem_mem_W.mp
        (chain_and_neighbor_exits_side hG h.1 hC hg s chain fan hand a ha)).2.1
    have sub := ineligible_reachable_pure hG h hC hz hi prev
    by_cases hempty : supp n D (src D (g,s)) = ∅
    · exact False.elim (noFilter (g,!s) hg hand
        (by simpa only [sem_bar, Bool.not_not] using hempty) neighbors)
    · obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      have vi : v = i := Finset.mem_singleton.mp (sub hv)
      have hinput : i ∈ supp n D (src D (g,s)) := vi ▸ hv
      have hother : i ∉ supp n D (src D (g,!s)) := by
        intro ho
        have pure := sem_inelig_pure hG h.1 hC hi ho
        obtain ⟨a, ha, hai⟩ := hG.2.2.2 i i
        have ham := neighbors a ha
        rw [pure, Finset.mem_singleton] at ham
        exact hai ham
      have hnotout : i ∉ supp n D (n + g) := by
        intro ho
        exact hother (sem_supp_and_sub h.1 hg hand (!s) ho)
      have hit : (g,s) ∈ exitArcs n D (carrierT n D {i}) :=
        sem_mem_exit1.mpr ⟨hg, hinput, hnotout⟩
      rw [hexits, Finset.mem_singleton] at hit
      exact congrArg Prod.fst hit

end PEqualNP.Outside.L_meta_2590_aux.DagTools

namespace PEqualNP.Outside.L_meta_2590_aux.DagTools

def CleanStarAt (n : ℕ) (G : Fin n → Fin n → Prop) (D : Dag)
    (i : Fin n) (e : ℕ × Bool) : Prop :=
  e.1 < D.length ∧ tag D e.1 = true ∧
  supp n D (src D e) = {i} ∧ supp n D (n + e.1) = ∅ ∧
  sem_Chain n D i.val (src D e) ∧ fanout D (src D e) = 1 ∧
  (∀ a : Fin n, a ∈ supp n D (src D (sem_bar e)) ↔ G i a) ∧
  ∀ g, g < D.length → tag D g = true →
    Relation.ReflTransGen (sem_step n D) i.val (n + g) → g = e.1

lemma clean_star_of_no_empty_filter {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}
    (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (hz : Bzero n D = 0) {i : Fin n} (hi : i ∈ ineligSet n D)
    (noFilter : ∀ F : ℕ × Bool, F.1 < D.length → tag D F.1 = true →
      supp n D (src D (sem_bar F)) = ∅ →
      (∀ a : Fin n, G i a → a ∈ supp n D (src D F)) → False) :
    ∃ e : ℕ × Bool, CleanStarAt n G D i e := by
  obtain ⟨e, he, ht, hp, hout, hleft, hfan, _, honly⟩ :=
    unique_reachable_and_of_no_empty_filter hG h hC hz hi noFilter
  have himem : i ∈ supp n D (src D e) := by rw [hp]; simp
  have exactSides := clean_star_signatures_of_unique_reachable_and
    hG h hC he e.2 hleft hfan ht himem honly
  exact ⟨e, he, ht, hp, hout, hleft, hfan, exactSides.2, honly⟩

end PEqualNP.Outside.L_meta_2590_aux.DagTools

namespace PEqualNP.Outside.L_meta_2590_aux

open DagTools

lemma petersen_two_ineligible_clean_stars {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (small : D.length ≤ 19) (hi : (ineligSet 10 D).card = 2)
    (h0 : (0 : V) ∈ ineligSet 10 D) (h2 : (2 : V) ∈ ineligSet 10 D) :
    (∃ e : ℕ × Bool, CleanStarAt 10 adj D (0 : V) e) ∧
      (∃ e : ℕ × Bool, CleanStarAt 10 adj D (2 : V) e) := by
  have hz := (two_ineligible_tight h hc small hi).2.1
  constructor
  · exact clean_star_of_no_empty_filter graph_ok h hc hz h0
      (fun F hF tF emptyF neighborsF =>
        private_filter_i2 h hc small hi h0 h2 hF tF emptyF neighborsF)
  · exact clean_star_of_no_empty_filter graph_ok h hc hz h2
      (fun F hF tF emptyF neighborsF =>
        private_filter_two_i2 h hc small hi h0 h2 hF tF emptyF neighborsF)

end PEqualNP.Outside.L_meta_2590_aux

namespace PEqualNP.Outside.L_meta_2590_aux.DagTools

lemma zero_merges_exit_support {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}
    (hG : sem_Gr G) (h : StrictLive n D) (hc : sem_Comp n G D)
    {x : Fin n} (hm : merges n D (carrierT n D {x}) = ∅)
    {w : ℕ} (hx : x ∈ supp n D w) :
    ∃ e ∈ sem_W n D x, supp n D w ⊆ supp n D (src D e) := by
  classical
  by_contra bad
  have preserves {u v : ℕ} (step : sem_step n D u v)
      (hu : x ∈ supp n D u) (sub : supp n D w ⊆ supp n D u) :
      x ∈ supp n D v ∧ supp n D w ⊆ supp n D v := by
    obtain ⟨j, s, hj, rfl, hsrc⟩ := sem_step_iff.mp step
    have hxj : x ∈ supp n D (n + j) := by
      by_contra hn
      apply bad
      refine ⟨(j, s), sem_mem_W.mpr ⟨hj, ?_, hn⟩, ?_⟩
      · simpa only [hsrc] using hu
      · simpa only [hsrc] using sub
    have hor := (sem_zm_gate h.1 hm hj hxj).1
    refine ⟨hxj, sub.trans ?_⟩
    intro a ha
    rw [sem_supp_or h.1 hj hor]
    rw [← hsrc] at ha
    cases s
    · exact Finset.mem_union.mpr (Or.inl (by simpa only [sb_src_false] using ha))
    · exact Finset.mem_union.mpr (Or.inr (by simpa only [sb_src_true] using ha))
  have propagate : ∀ u, Relation.ReflTransGen (sem_step n D) w u →
      x ∈ supp n D u ∧ supp n D w ⊆ supp n D u := by
    intro u path
    induction path with
    | refl => exact ⟨hx, Finset.Subset.refl _⟩
    | @tail u v path step ih => exact preserves step ih.1 ih.2
  have hout := (propagate _ (live_reaches_output h (sem_supp_lt hx))).1
  rw [sem_supp_out hG hc] at hout
  exact Finset.notMem_empty _ hout

end PEqualNP.Outside.L_meta_2590_aux.DagTools

namespace PEqualNP.Outside.L_meta_2590_aux

open DagTools

lemma petersen_clean_star_one_exits {D : Dag}
    (h : StrictLive 10 D) (hC : sem_Comp 10 adj D)
    (small : D.length ≤ 19) (two : (ineligSet 10 D).card = 2)
    (h0 : (0 : V) ∈ ineligSet 10 D) (h2 : (2 : V) ∈ ineligSet 10 D) :
    ∃ A B : ℕ × Bool,
      A ∈ sem_W 10 D (1 : V) ∧ B ∈ sem_W 10 D (1 : V) ∧ A ≠ B ∧
      supp 10 D (src D (sem_bar A)) = {(0 : V)} ∧
      supp 10 D (src D (sem_bar B)) = {(2 : V)} ∧
      (6 : V) ∉ supp 10 D (src D A) ∧ (6 : V) ∉ supp 10 D (src D B) := by
  obtain ⟨hs0, hs2⟩ := petersen_two_ineligible_clean_stars h hC small two h0 h2
  obtain ⟨e0, he0, _, hp0, hout0, _, _, hs0, _⟩ := hs0
  obtain ⟨e2, he2, _, hp2, hout2, _, _, hs2, _⟩ := hs2
  have hA : sem_bar e0 ∈ sem_W 10 D (1 : V) := by
    refine sem_mem_W.mpr ⟨he0, (hs0 1).mpr (by decide), ?_⟩
    change (1 : V) ∉ supp 10 D (10 + e0.1)
    rw [hout0]
    exact Finset.notMem_empty _
  have hB : sem_bar e2 ∈ sem_W 10 D (1 : V) := by
    refine sem_mem_W.mpr ⟨he2, (hs2 1).mpr (by decide), ?_⟩
    change (1 : V) ∉ supp 10 D (10 + e2.1)
    rw [hout2]
    exact Finset.notMem_empty _
  have hne : sem_bar e0 ≠ sem_bar e2 := by
    intro hh
    have heq : e0 = e2 := r1_bar_inj hh
    have hz : (0 : V) ∈ supp 10 D (src D e0) := by rw [hp0]; simp
    rw [heq, hp2, Finset.mem_singleton] at hz
    exact (by decide : (0 : V) ≠ 2) hz
  refine ⟨sem_bar e0, sem_bar e2, hA, hB, hne, ?_, ?_, ?_, ?_⟩
  · simpa only [sem_bar_bar] using hp0
  · simpa only [sem_bar_bar] using hp2
  · intro hm
    exact (by decide : ¬ adj 0 6) ((hs0 6).mp hm)
  · intro hm
    exact (by decide : ¬ adj 2 6) ((hs2 6).mp hm)

lemma petersen_one_code_not_subset_six {D : Dag}
    (h : StrictLive 10 D) (hC : sem_Comp 10 adj D)
    (small : D.length ≤ 19) (two : (ineligSet 10 D).card = 2)
    (h0 : (0 : V) ∈ ineligSet 10 D) (h2 : (2 : V) ∈ ineligSet 10 D)
    (b : V → ℕ) (hb : PureBranch 10 D b) :
    ¬ (∀ u ∈ residualUnits 10 D b,
      (1 : V) ∈ supp 10 D u.1 → (6 : V) ∈ supp 10 D u.1) := by
  intro hinc
  obtain ⟨A, B, hA, hB, hne, _, _, hA6, hB6⟩ :=
    petersen_clean_star_one_exits h hC small two h0 h2
  obtain ⟨u, hu, hu1⟩ := common_neighbor_residual h hC b hb h0 h2
  have eligible : (1 : V) ∈ eligSet 10 D :=
    (sem_elig_cover graph_ok h hC (show adj 0 1 by decide)).resolve_left
      (sem_mem_inelig.mp h0)
  obtain ⟨e0, he0⟩ := ri_gen graph_ok h hC b hb
    (by decide : (1 : V) ≠ 6) eligible hinc ⟨hu1, hinc u hu hu1⟩
  have hAe : A = e0 := by
    by_contra hn
    exact hA6 (he0 A hA hn)
  have hBe : B = e0 := by
    by_contra hn
    exact hB6 (he0 B hB hn)
  exact hne (hAe.trans hBe.symm)

lemma petersen_single_one_residual_support {D : Dag}
    (h : StrictLive 10 D) (hC : sem_Comp 10 adj D)
    (small : D.length ≤ 19) (two : (ineligSet 10 D).card = 2)
    (h0 : (0 : V) ∈ ineligSet 10 D) (h2 : (2 : V) ∈ ineligSet 10 D)
    (b : V → ℕ) (hb : PureBranch 10 D b)
    (single : ((residualUnits 10 D b).filter
      (fun u => (1 : V) ∈ supp 10 D u.1)).card = 1)
    {u : Σ _ : ℕ, ℕ} (hu : u ∈ residualUnits 10 D b)
    (hu1 : (1 : V) ∈ supp 10 D u.1) : supp 10 D u.1 = {(1 : V)} := by
  classical
  have hz := (two_ineligible_tight h hC small two).2.1
  have hle : ((residualUnits 10 D b).filter
      (fun v => (1 : V) ∈ supp 10 D v.1)).card ≤ 1 := by omega
  have unique (v : Σ _ : ℕ, ℕ) (hv : v ∈ residualUnits 10 D b)
      (hv1 : (1 : V) ∈ supp 10 D v.1) : v = u :=
    Finset.card_le_one.mp hle v (Finset.mem_filter.mpr ⟨hv, hv1⟩)
      u (Finset.mem_filter.mpr ⟨hu, hu1⟩)
  have inclusion {c : V} (hcu : c ∈ supp 10 D u.1) :
      ∀ v ∈ residualUnits 10 D b, (1 : V) ∈ supp 10 D v.1 → c ∈ supp 10 D v.1 := by
    intro v hv hv1
    rw [unique v hv hv1]
    exact hcu
  have noC6 : ∀ c ∈ ({3,4,5,7,8,9} : Finset V), c ∉ supp 10 D u.1 := by
    intro c hc hcu
    exact petersen_one_code_not_subset h hC hz h0 h2 b hb hc (inclusion hcu)
  have no6 : (6 : V) ∉ supp 10 D u.1 := by
    intro h6
    exact petersen_one_code_not_subset_six h hC small two h0 h2 b hb (inclusion h6)
  have hunit := (mem_units.mp
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp hu).1).1).2
  have hfan : 2 ≤ fanout D u.1 := by omega
  have noIneligible (v : V) (hv : v ∈ ineligSet 10 D) : v ∉ supp 10 D u.1 := by
    intro hvs
    exact (sem_mem_inelig.mp hv) (mem_eligSet.mpr ⟨u.1, hfan, hvs⟩)
  have partition : ∀ c : V, c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 6 ∨
      c ∈ ({3,4,5,7,8,9} : Finset V) := by decide +kernel
  apply Finset.Subset.antisymm
  · intro c hc
    rcases partition c with rfl | rfl | rfl | rfl | hset
    · exact False.elim (noIneligible 0 h0 hc)
    · exact Finset.mem_singleton_self _
    · exact False.elim (noIneligible 2 h2 hc)
    · exact False.elim (no6 hc)
    · exact False.elim (noC6 c hset hc)
  · exact Finset.singleton_subset_iff.mpr hu1

end PEqualNP.Outside.L_meta_2590_aux

namespace PEqualNP.Outside.L_meta_2590_aux

open DagTools

lemma petersen_single_one_flow {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (h0 : (0 : V) ∈ ineligSet 10 D) (h2 : (2 : V) ∈ ineligSet 10 D)
    (b : V → ℕ) (hb : PureBranch 10 D b)
    (single : ((residualUnits 10 D b).filter
      (fun u => (1 : V) ∈ supp 10 D u.1)).card ≤ 1) :
    (sem_W 10 D (1 : V)).card = 3 ∧ merges 10 D (carrierT 10 D {(1 : V)}) = ∅ := by
  have lower := common_neighbor_three h hc h0 h2
  have count := sem_code_count graph_ok h hc b hb (1 : V)
  have cap : (({(1 : V)} : Finset V) ∩ eligSet 10 D).card ≤ 1 :=
    (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
  exact ⟨by omega, Finset.card_eq_zero.mp (by omega)⟩

lemma petersen_single_one_no_joint_six {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (small : D.length ≤ 19) (hi : (ineligSet 10 D).card = 2)
    (h0 : (0 : V) ∈ ineligSet 10 D) (h2 : (2 : V) ∈ ineligSet 10 D)
    (b : V → ℕ) (hb : PureBranch 10 D b)
    (single : ((residualUnits 10 D b).filter
      (fun u => (1 : V) ∈ supp 10 D u.1)).card ≤ 1) :
    ∀ w, ¬ ((1 : V) ∈ supp 10 D w ∧ (6 : V) ∈ supp 10 D w) := by
  obtain ⟨size1, merges1⟩ := petersen_single_one_flow h hc h0 h2 b hb single
  obtain ⟨A, B, hA, hB, neAB, pureA, pureB, freeA, freeB⟩ :=
    petersen_clean_star_one_exits h hc small hi h0 h2
  obtain ⟨C, hC, hbarC, freeC, _, _⟩ :=
    sem_edge_slots graph_ok h.1 hc (show adj 1 6 by decide)
  have sixC : (6 : V) ∈ supp 10 D (src D (sem_bar C)) := (sem_mem_W.mp hbarC).2.1
  have neCA : C ≠ A := by
    intro eq
    rw [eq, pureA, Finset.mem_singleton] at sixC
    exact (by decide : (6 : V) ≠ 0) sixC
  have neCB : C ≠ B := by
    intro eq
    rw [eq, pureB, Finset.mem_singleton] at sixC
    exact (by decide : (6 : V) ≠ 2) sixC
  have all_free (e : ℕ × Bool) (he : e ∈ sem_W 10 D (1 : V)) :
      (6 : V) ∉ supp 10 D (src D e) := by
    rcases mem_three_of_card_le (by omega) hA hB hC neAB neCA.symm neCB.symm he with
      rfl | rfl | rfl
    · exact freeA
    · exact freeB
    · exact freeC
  intro w hw
  obtain ⟨e, he, sub⟩ := zero_merges_exit_support graph_ok h hc merges1 hw.1
  exact all_free e he (sub hw.2)

end PEqualNP.Outside.L_meta_2590_aux

namespace PEqualNP.Outside.L_meta_2590_aux

open DagTools

lemma petersen_six_code_and_exit_caps {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (small : D.length ≤ 19) (hi : (ineligSet 10 D).card = 2)
    (h0 : (0 : V) ∈ ineligSet 10 D) (h2 : (2 : V) ∈ ineligSet 10 D)
    (b : V → ℕ) (hb : PureBranch 10 D b) :
    ((residualUnits 10 D b).filter (fun u => (6 : V) ∈ supp 10 D u.1)).card ≤ 1 ∧
      (sem_W 10 D (6 : V)).card ≤ 3 := by
  classical
  have tight := two_ineligible_tight h hc small hi
  have complement := inelig_card_add 10 D
  have residual := card_residual h.1 b hb
  have cap : (residualUnits 10 D b).card ≤ 2 := by omega
  have code : ((residualUnits 10 D b).filter
      (fun u => (6 : V) ∈ supp 10 D u.1)).card ≤ 1 := by
    have notsub := petersen_one_code_not_subset_six h hc small hi h0 h2 b hb
    have le := Finset.card_filter_le (residualUnits 10 D b)
      (fun u => (6 : V) ∈ supp 10 D u.1)
    by_contra bad
    have eq : ((residualUnits 10 D b).filter
        (fun u => (6 : V) ∈ supp 10 D u.1)).card = (residualUnits 10 D b).card := by omega
    have all := Finset.card_filter_eq_iff.mp eq
    exact notsub (fun u hu _ => all u hu)
  have count := sem_code_count graph_ok h hc b hb (6 : V)
  have single : (({(6 : V)} : Finset V) ∩ eligSet 10 D).card ≤ 1 :=
    (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
  exact ⟨code, by omega⟩

lemma petersen_both_one_flow_cases {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (h0 : (0 : V) ∈ ineligSet 10 D) (h2 : (2 : V) ∈ ineligSet 10 D)
    (b : V → ℕ) (hb : PureBranch 10 D b)
    (both : ((residualUnits 10 D b).filter
      (fun u => (1 : V) ∈ supp 10 D u.1)).card = 2) :
    ((sem_W 10 D (1 : V)).card = 3 ∧
      (merges 10 D (carrierT 10 D {(1 : V)})).card = 1) ∨
    ((sem_W 10 D (1 : V)).card = 4 ∧
      merges 10 D (carrierT 10 D {(1 : V)}) = ∅) := by
  have eligible : (1 : V) ∈ eligSet 10 D :=
    (sem_elig_cover graph_ok h hc (show adj 0 1 by decide)).resolve_left
      (sem_mem_inelig.mp h0)
  have single : (({(1 : V)} : Finset V) ∩ eligSet 10 D).card = 1 := by
    rw [Finset.inter_eq_left.mpr (Finset.singleton_subset_iff.mpr eligible)]
    simp
  have lower := common_neighbor_three h hc h0 h2
  have count := sem_code_count graph_ok h hc b hb (1 : V)
  by_cases three : (sem_W 10 D (1 : V)).card = 3
  · exact Or.inl ⟨three, by omega⟩
  · exact Or.inr ⟨by omega, Finset.card_eq_zero.mp (by omega)⟩

end PEqualNP.Outside.L_meta_2590_aux

namespace PEqualNP.Outside.L_meta_2590_aux.I2ForbiddenPairs

open DagTools

def center : Fin 10 → V := ![2, 2, 2, 0, 0, 0, 0, 0, 2, 2]
def left : Fin 10 → V := ![3, 3, 3, 4, 4, 4, 5, 5, 7, 7]
def right : Fin 10 → V := ![5, 6, 9, 6, 7, 8, 6, 9, 6, 8]
def witness : Fin 10 → Finset V := ![{1, 4, 5}, {4, 6, 7}, {1, 8, 9}, {3, 5, 6}, {1, 3, 7}, {1, 8, 9}, {4, 6, 7}, {1, 8, 9}, {3, 5, 6}, {1, 8, 9}]

set_option synthInstance.maxSize 10000 in
lemma geometry : ∀ k : Fin 10,
    (center k = 0 ∨ center k = 2) ∧ left k ≠ 1 ∧
    adj (center k) (left k) ∧ ¬ adj (center k) (right k) ∧ ¬ adj (left k) (right k) ∧
    (∀ a ∈ witness k, ∀ z ∈ witness k, ¬ adj a z) ∧ right k ∈ witness k ∧
    (∃ a ∈ witness k, adj (center k) a) ∧ (∃ a ∈ witness k, adj (left k) a) := by
  unfold adj
  decide +kernel

lemma code_not_subset {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 adj D) (hz : Bzero 10 D = 0)
    (b : V → ℕ) (hb : PureBranch 10 D b)
    (h0 : (0 : V) ∈ ineligSet 10 D) (h2 : (2 : V) ∈ ineligSet 10 D)
    (k : Fin 10) (hcode : ∃ u ∈ residualUnits 10 D b, left k ∈ supp 10 D u.1) :
    ¬ (∀ u ∈ residualUnits 10 D b, left k ∈ supp 10 D u.1 → right k ∈ supp 10 D u.1) := by
  obtain ⟨hi,_,hix,hic,hxc,hA,hcA,hiA,hxA⟩ := geometry k
  have hin : center k ∈ ineligSet 10 D := by rcases hi with hi | hi <;> simpa [hi]
  exact ineligible_code_not_subset graph_ok h hc hz b hb hin hix hic hxc hcode
    (witness k) hA hcA hiA hxA

lemma other_support_avoids_pairs {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 adj D) (hz : Bzero 10 D = 0)
    (b : V → ℕ) (hb : PureBranch 10 D b)
    (h0 : (0 : V) ∈ ineligSet 10 D) (h2 : (2 : V) ∈ ineligSet 10 D)
    (u v : Σ _ : ℕ, ℕ) (hres : residualUnits 10 D b = {u,v})
    (hu : supp 10 D u.1 = {1}) (S : Finset V) (hv : supp 10 D v.1 = S) :
    ∀ k : Fin 10, ¬ (left k ∈ S ∧ right k ∈ S) := by
  intro k hpair
  have hvm : v ∈ residualUnits 10 D b := by rw [hres]; simp
  apply code_not_subset h hc hz b hb h0 h2 k ⟨v,hvm,by rw [hv]; exact hpair.1⟩
  intro w hw hx
  rw [hres, Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl
  · rw [hu, Finset.mem_singleton] at hx
    exact False.elim ((geometry k).2.1 hx)
  · rw [hv]
    exact hpair.2

def supports : List (Finset V) := [{3}, {4}, {3, 4}, {5}, {4, 5}, {6}, {7}, {3, 7}, {5, 7}, {8}, {3, 8}, {5, 8}, {6, 8}, {9}, {4, 9}, {6, 9}, {7, 9}, {8, 9}, {6, 8, 9}]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
set_option synthInstance.maxSize 10000 in
lemma finite_supports : ∀ S : Finset V, S.Nonempty → S ⊆ {3,4,5,6,7,8,9} →
    (∀ k : Fin 10, ¬ (left k ∈ S ∧ right k ∈ S)) → S ∈ supports := by
  decide +kernel

end PEqualNP.Outside.L_meta_2590_aux.I2ForbiddenPairs

namespace PEqualNP.Outside.L_meta_2590_aux

open DagTools

lemma petersen_single_one_residual_decomposition {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (small : D.length ≤ 19) (two : (ineligSet 10 D).card = 2)
    (h0 : (0 : V) ∈ ineligSet 10 D) (h2 : (2 : V) ∈ ineligSet 10 D)
    (b : V → ℕ) (hb : PureBranch 10 D b)
    (hone : ((residualUnits 10 D b).filter
      (fun u => (1 : V) ∈ supp 10 D u.1)).card ≤ 1) :
    ∃ u v : Σ _ : ℕ, ℕ, u ≠ v ∧ residualUnits 10 D b = {u,v} ∧
      supp 10 D u.1 = {(1 : V)} ∧ supp 10 D v.1 ∈ I2ForbiddenPairs.supports := by
  classical
  obtain ⟨u,hu,hu1⟩ := common_neighbor_residual h hc b hb h0 h2
  have hpos : 0 < ((residualUnits 10 D b).filter
      (fun u => (1 : V) ∈ supp 10 D u.1)).card :=
    Finset.card_pos.mpr ⟨u, Finset.mem_filter.mpr ⟨hu,hu1⟩⟩
  have hone' : ((residualUnits 10 D b).filter
      (fun u => (1 : V) ∈ supp 10 D u.1)).card = 1 := by omega
  obtain ⟨hz,hcard,_⟩ := petersen_two_ineligible_code_caps h hc small two h0 h2 b hb
  have herase : ((residualUnits 10 D b).erase u).card = 1 := by
    rw [Finset.card_erase_of_mem hu, hcard]
  obtain ⟨v,hv⟩ := Finset.card_eq_one.mp herase
  have hvm : v ∈ (residualUnits 10 D b).erase u := by rw [hv]; simp
  have hvne : v ≠ u := (Finset.mem_erase.mp hvm).1
  have hvr : v ∈ residualUnits 10 D b := (Finset.mem_erase.mp hvm).2
  have hres : residualUnits 10 D b = {u,v} := by
    rw [← Finset.insert_erase hu, hv]
  have hus := petersen_single_one_residual_support h hc small two h0 h2 b hb hone' hu hu1
  have hv1 : (1 : V) ∉ supp 10 D v.1 := by
    intro hv1
    exact hvne (Finset.card_le_one.mp hone v (Finset.mem_filter.mpr ⟨hvr,hv1⟩)
      u (Finset.mem_filter.mpr ⟨hu,hu1⟩))
  have hunit := (mem_units.mp
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp hvr).1).1).2
  have hfan : 2 ≤ fanout D v.1 := by omega
  have hnonempty : (supp 10 D v.1).Nonempty :=
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp hvr).1).2
  have hnot (x : V) (hx : x ∈ ineligSet 10 D) : x ∉ supp 10 D v.1 := by
    intro hxs
    exact (sem_mem_inelig.mp hx) (mem_eligSet.mpr ⟨v.1,hfan,hxs⟩)
  have hsub : supp 10 D v.1 ⊆ ({3,4,5,6,7,8,9} : Finset V) := by
    have hpart : ∀ x : V, x = 0 ∨ x = 1 ∨ x = 2 ∨ x ∈ ({3,4,5,6,7,8,9} : Finset V) := by
      decide +kernel
    intro x hx
    rcases hpart x with rfl | rfl | rfl | hxset
    · exact False.elim (hnot 0 h0 hx)
    · exact False.elim (hv1 hx)
    · exact False.elim (hnot 2 h2 hx)
    · exact hxset
  refine ⟨u,v,Ne.symm hvne,hres,hus,?_⟩
  exact I2ForbiddenPairs.finite_supports _ hnonempty hsub
    (I2ForbiddenPairs.other_support_avoids_pairs h hc hz b hb h0 h2 u v hres hus _ rfl)

lemma residual_other_code {D : Dag} (b : V → ℕ) (u v : Σ _ : ℕ, ℕ)
    (hres : residualUnits 10 D b = {u,v}) (hu : supp 10 D u.1 = {(1 : V)})
    {x : V} (hx : x ≠ 1) :
    (residualUnits 10 D b).filter (fun a => x ∈ supp 10 D a.1) =
      if x ∈ supp 10 D v.1 then {v} else ∅ := by
  classical
  rw [hres]
  by_cases hv : x ∈ supp 10 D v.1 <;> simp [Finset.filter_insert, hu, hx, hv]

end PEqualNP.Outside.L_meta_2590_aux

namespace PEqualNP.Outside.L_meta_2590_aux.PortCodes

def bar (e : ℕ × Bool) : ℕ × Bool := (e.1, !e.2)

def flip (s : ℕ) : ℕ := if s % 2 = 0 then s + 1 else s - 1

def decode (r : ℕ → ℕ × Bool) (s : ℕ) : ℕ × Bool :=
  if s % 2 = 0 then r (s / 2) else ((r (s / 2)).1, !(r (s / 2)).2)

lemma bar_ne_self (e : ℕ × Bool) : bar e ≠ e := by
  rcases e with ⟨a, b⟩
  cases b <;> simp [bar]

lemma decode_even (r : ℕ → ℕ × Bool) (a : ℕ) : decode r (2 * a) = r a := by
  have hm : (2 * a) % 2 = 0 := by omega
  have hd : (2 * a) / 2 = a := by omega
  simp [decode, hm, hd]

lemma decode_odd (r : ℕ → ℕ × Bool) (a : ℕ) :
    decode r (2 * a + 1) = ((r a).1, !(r a).2) := by
  have hm : (2 * a + 1) % 2 ≠ 0 := by omega
  have hd : (2 * a + 1) / 2 = a := by omega
  simp [decode, hm, hd]

lemma decode_fst (r : ℕ → ℕ × Bool) (s : ℕ) :
    (decode r s).1 = (r (s / 2)).1 := by
  unfold decode
  split_ifs <;> rfl

lemma flip_div_two (s : ℕ) : flip s / 2 = s / 2 := by
  unfold flip
  split_ifs <;> omega

lemma flip_lt {k s : ℕ} (hs : s < 2 * k) : flip s < 2 * k := by
  unfold flip
  split_ifs <;> omega

lemma decode_flip (r : ℕ → ℕ × Bool) (s : ℕ) :
    decode r (flip s) = bar (decode r s) := by
  by_cases hs : s % 2 = 0
  · have hflip : flip s % 2 ≠ 0 := by
      rw [flip, if_pos hs]
      omega
    simp [decode, hs, hflip, flip_div_two, bar]
  · have hflip : flip s % 2 = 0 := by
      rw [flip, if_neg hs]
      omega
    simp [decode, hs, hflip, flip_div_two, bar]

lemma decode_injective_below (k : ℕ) (r : ℕ → ℕ × Bool)
    (hr : ∀ a < k, ∀ b < k, (r a).1 = (r b).1 → a = b)
    {s t : ℕ} (hs : s < 2 * k) (ht : t < 2 * k)
    (he : decode r s = decode r t) : s = t := by
  have hfst : (r (s / 2)).1 = (r (t / 2)).1 := by
    simpa only [decode_fst] using congrArg Prod.fst he
  have hd : s / 2 = t / 2 := hr (s / 2) (by omega) (t / 2) (by omega) hfst
  by_cases hs0 : s % 2 = 0
  · by_cases ht0 : t % 2 = 0
    · omega
    · have hbad : r (s / 2) = bar (r (s / 2)) := by
        simpa [decode, hs0, ht0, ← hd, bar] using he
      exact False.elim (bar_ne_self _ hbad.symm)
  · by_cases ht0 : t % 2 = 0
    · have hbad : bar (r (s / 2)) = r (s / 2) := by
        simpa [decode, hs0, ht0, ← hd, bar] using he
      exact False.elim (bar_ne_self _ hbad)
    · omega

end PEqualNP.Outside.L_meta_2590_aux.PortCodes

namespace PEqualNP.Outside.L_meta_2590_aux.PortCodes

def groups (a : List ℕ) : ℕ := a.foldl (fun k c => max k (c / 2 + 1)) 0

def Growth (a : List ℕ) : Prop :=
  ∀ (i : ℕ) (hi : i < a.length), a[i] ≤ 2 * groups (a.take i)

lemma groups_snoc (a : List ℕ) (c : ℕ) :
    groups (a ++ [c]) = max (groups a) (c / 2 + 1) := by
  simp [groups, List.foldl_append]

lemma growth_snoc {a : List ℕ} (ha : Growth a) {c : ℕ}
    (hc : c ≤ 2 * groups a) : Growth (a ++ [c]) := by
  intro i hi
  by_cases hia : i < a.length
  · simpa only [List.getElem_append_left hia,
      List.take_append_of_le_length (Nat.le_of_lt hia)] using ha i hia
  · have hieq : i = a.length := by simp only [List.length_append, List.length_singleton] at hi; omega
    subst i
    simpa using hc

lemma extend_reps (r : ℕ → ℕ × Bool) (k : ℕ)
    (hinj : ∀ i j, i < k → j < k → (r i).1 = (r j).1 → i = j)
    (e : ℕ × Bool) :
    ∃ c : ℕ, ∃ r' : ℕ → ℕ × Bool,
      c ≤ 2 * k ∧ (∀ i, i < k → r' i = r i) ∧ decode r' c = e ∧
      ∀ i j, i < max k (c / 2 + 1) → j < max k (c / 2 + 1) →
        (r' i).1 = (r' j).1 → i = j := by
  classical
  by_cases hex : ∃ j, j < k ∧ (r j).1 = e.1
  · obtain ⟨j, hj, he⟩ := hex
    by_cases hs : (r j).2 = e.2
    · refine ⟨2 * j, r, by omega, fun _ _ => rfl, ?_, ?_⟩
      · rw [decode_even]
        exact Prod.ext he hs
      · have hm : max k ((2 * j) / 2 + 1) = k := by omega
        simpa only [hm] using hinj
    · refine ⟨2 * j + 1, r, by omega, fun _ _ => rfl, ?_, ?_⟩
      · rw [decode_odd]
        apply Prod.ext
        · exact he
        · cases h1 : (r j).2 <;> cases h2 : e.2 <;> simp_all
      · have hm : max k ((2 * j + 1) / 2 + 1) = k := by omega
        simpa only [hm] using hinj
  · let r' : ℕ → ℕ × Bool := fun i => if i = k then e else r i
    have old (i : ℕ) (hi : i < k) : r' i = r i := by
      simp only [r', if_neg (show i ≠ k by omega)]
    have new : r' k = e := by simp only [r', if_pos rfl]
    refine ⟨2 * k, r', by omega, old, ?_, ?_⟩
    · rw [decode_even, new]
    · have hm : max k ((2 * k) / 2 + 1) = k + 1 := by omega
      intro i j hi hj he
      rw [hm] at hi hj
      by_cases hik : i = k
      · subst i
        by_cases hjk : j = k
        · exact hjk.symm
        · have hjlt : j < k := by omega
          rw [new, old j hjlt] at he
          exact False.elim (hex ⟨j, hjlt, he.symm⟩)
      · have hilt : i < k := by omega
        by_cases hjk : j = k
        · subst j
          rw [old i hilt, new] at he
          exact False.elim (hex ⟨i, hilt, he⟩)
        · have hjlt : j < k := by omega
          rw [old i hilt, old j hjlt] at he
          exact hinj i j hilt hjlt he

lemma normalize (es : List (ℕ × Bool)) :
    ∃ a : List ℕ, ∃ r : ℕ → ℕ × Bool,
      a.map (decode r) = es ∧ Growth a ∧
      (∀ c ∈ a, c < 2 * groups a) ∧
      (∀ i j, i < groups a → j < groups a → (r i).1 = (r j).1 → i = j) := by
  induction es using List.reverseRecOn with
  | nil =>
    refine ⟨[], fun _ => (0, false), rfl, ?_, by simp, ?_⟩
    · intro i hi
      simp at hi
    · simp [groups]
  | append_singleton es e ih =>
    obtain ⟨a, r, hmap, hgrowth, hbound, hinj⟩ := ih
    obtain ⟨c, r', hc, hold, hnew, hinj'⟩ := extend_reps r (groups a) hinj e
    have hdecode (v : ℕ) (hv : v ∈ a) : decode r' v = decode r v := by
      have hsmall := hbound v hv
      have hvgroup : v / 2 < groups a := by omega
      simp only [decode, hold _ hvgroup]
    refine ⟨a ++ [c], r', ?_, growth_snoc hgrowth hc, ?_, ?_⟩
    · rw [List.map_append, List.map_singleton, hnew]
      have hm : a.map (decode r') = a.map (decode r) := List.map_congr_left hdecode
      rw [hm, hmap]
    · intro v hv
      rw [groups_snoc]
      rcases List.mem_append.mp hv with hv | hv
      · have hb := hbound v hv
        have hm := le_max_left (groups a) (c / 2 + 1)
        omega
      · have hv : v = c := List.mem_singleton.mp hv
        subst v
        have hm := le_max_right (groups a) (c / 2 + 1)
        omega
    · simpa only [groups_snoc] using hinj'

end PEqualNP.Outside.L_meta_2590_aux.PortCodes

namespace PEqualNP.Outside.L_meta_2590_aux.PortCodes

lemma growth_snoc_parts {a : List ℕ} {c : ℕ} (ha : Growth (a ++ [c])) :
    Growth a ∧ c ≤ 2 * groups a := by
  constructor
  · intro i hi
    have hi' : i < (a ++ [c]).length := by
      simp only [List.length_append, List.length_singleton]
      omega
    simpa only [List.getElem_append_left hi,
      List.take_append_of_le_length (Nat.le_of_lt hi)] using ha i hi'
  · have hlast : a.length < (a ++ [c]).length := by simp
    simpa using ha a.length hlast

lemma groups_dense (a : List ℕ) (ha : Growth a) :
    ∀ j, j < groups a → ∃ c ∈ a, c / 2 = j := by
  revert ha
  induction a using List.reverseRecOn with
  | nil =>
    intro _ j hj
    simp [groups] at hj
  | append_singleton a c ih =>
    intro ha j hj
    obtain ⟨hprefix, hc⟩ := growth_snoc_parts ha
    rw [groups_snoc] at hj
    by_cases hold : j < groups a
    · obtain ⟨d, hd, hdj⟩ := ih hprefix j hold
      exact ⟨d, List.mem_append.mpr (Or.inl hd), hdj⟩
    · have hcj : c / 2 = j := by omega
      exact ⟨c, by simp, hcj⟩

lemma groups_le_length (a : List ℕ) (ha : Growth a) : groups a ≤ a.length := by
  revert ha
  induction a using List.reverseRecOn with
  | nil =>
    intro _
    simp [groups]
  | append_singleton a c ih =>
    intro ha
    obtain ⟨hprefix, hc⟩ := growth_snoc_parts ha
    have hlen := ih hprefix
    rw [groups_snoc, List.length_append, List.length_singleton]
    omega

lemma representatives_avoid (a : List ℕ) (r : ℕ → ℕ × Bool)
    (es : List (ℕ × Bool)) (fixedID : ℕ)
    (hmap : a.map (decode r) = es) (ha : Growth a)
    (havoid : ∀ e ∈ es, e.1 ≠ fixedID) :
    ∀ j, j < groups a → (r j).1 ≠ fixedID := by
  intro j hj
  obtain ⟨c, hca, hcj⟩ := groups_dense a ha j hj
  have he : decode r c ∈ es := by
    rw [← hmap]
    exact List.mem_map.mpr ⟨c, hca, rfl⟩
  have hne := havoid (decode r c) he
  simpa only [decode_fst, hcj] using hne

end PEqualNP.Outside.L_meta_2590_aux.PortCodes

namespace PEqualNP.Outside.L_meta_2590_aux.PortCodes

def fixedReps (A B : ℕ × Bool) (r : ℕ → ℕ × Bool) : ℕ → ℕ × Bool
  | 0 => A
  | 1 => B
  | j + 2 => r j

lemma fixedReps_injective (A B : ℕ × Bool) (r : ℕ → ℕ × Bool) (k : ℕ)
    (hAB : A.1 ≠ B.1)
    (hA : ∀ i < k, (r i).1 ≠ A.1) (hB : ∀ i < k, (r i).1 ≠ B.1)
    (hr : ∀ i j, i < k → j < k → (r i).1 = (r j).1 → i = j) :
    ∀ i j, i < k + 2 → j < k + 2 →
      (fixedReps A B r i).1 = (fixedReps A B r j).1 → i = j := by
  intro i j hi hj he
  cases i with
  | zero =>
    cases j with
    | zero => rfl
    | succ j =>
      cases j with
      | zero => exact False.elim (hAB he)
      | succ j => exact False.elim (hA j (by omega) he.symm)
  | succ i =>
    cases i with
    | zero =>
      cases j with
      | zero => exact False.elim (hAB he.symm)
      | succ j =>
        cases j with
        | zero => rfl
        | succ j => exact False.elim (hB j (by omega) he.symm)
    | succ i =>
      cases j with
      | zero => exact False.elim (hA i (by omega) he)
      | succ j =>
        cases j with
        | zero => exact False.elim (hB i (by omega) he)
        | succ j =>
          have hij := hr i j (by omega) (by omega) he
          omega

lemma decode_fixed_zero (A B : ℕ × Bool) (r : ℕ → ℕ × Bool) :
    decode (fixedReps A B r) 0 = A := by
  simpa [fixedReps] using decode_even (fixedReps A B r) 0

lemma decode_fixed_one (A B : ℕ × Bool) (r : ℕ → ℕ × Bool) :
    decode (fixedReps A B r) 1 = bar A := by
  simpa [fixedReps, bar] using decode_odd (fixedReps A B r) 0

lemma decode_fixed_two (A B : ℕ × Bool) (r : ℕ → ℕ × Bool) :
    decode (fixedReps A B r) 2 = B := by
  simpa [fixedReps] using decode_even (fixedReps A B r) 1

lemma decode_fixed_three (A B : ℕ × Bool) (r : ℕ → ℕ × Bool) :
    decode (fixedReps A B r) 3 = bar B := by
  simpa [fixedReps, bar] using decode_odd (fixedReps A B r) 1

lemma decode_fixed_add_four (A B : ℕ × Bool) (r : ℕ → ℕ × Bool) (s : ℕ) :
    decode (fixedReps A B r) (s + 4) = decode r s := by
  have hd : (s + 4) / 2 = s / 2 + 2 := by omega
  have hm : (s + 4) % 2 = s % 2 := by omega
  simp only [decode, hd, hm, fixedReps]

end PEqualNP.Outside.L_meta_2590_aux.PortCodes

namespace PEqualNP.Outside.L_meta_2590_aux.I2Census

abbrev V := Fin 10
abbrev P := Fin 22

def bar (p : P) : P := ⟨2 * (p.val / 2) + (1 - p.val % 2), by omega⟩
def toggle (c : Nat) : Nat := 2 * (c / 2) + (1 - c % 2)
def freeEdges : List (V × V) :=
  [(1,6),(3,4),(3,8),(5,7),(7,9),(4,9),(5,8),(6,8),(6,9)]
def decode (n : Nat) : Finset V := Finset.univ.filter fun v => n / 2 ^ v.val % 2 = 1

def lower (a : List Nat) (p : P) : Finset V :=
  if p.val < 4 then decode (([1,50,4,138] : List Nat).getD p.val 0)
  else ((a.zip freeEdges).flatMap fun z =>
    if z.1 + 4 = p.val then [z.2.1]
    else if toggle z.1 + 4 = p.val then [z.2.2]
    else []).toFinset

def selected (a : List Nat) (v : V) : Finset P :=
  Finset.univ.filter fun p => v ∈ lower a p

def budget (S : Finset V) (v : V) : Nat :=
  if v = 0 ∨ v = 2 then 1 else if v = 1 then 3 else 2 + if v ∈ S then 1 else 0

def row (r : Fin 15) : Finset V :=
  decode ((![50,69,104,116,138,201,208,276,385,402,521,548,554,770,773] : Fin 15 → Nat) r)
def neighbors (v : V) : Finset V :=
  decode ((![50,69,138,276,521,385,770,548,104,208] : Fin 10 → Nat) v)
abbrev touches (v : V) (r : Fin 15) : Prop := ¬ Disjoint (neighbors v) (row r)

abbrev omits (a : List Nat) (p : P) (y : V) : Prop :=
  if p.val < 4 then y ∉ lower a p else y ∈ lower a (bar p)

def triples (a : List Nat) : Finset V :=
  Finset.univ.filter fun v => 3 ≤ v.val ∧ (selected a v).card = 3

def common (a : List Nat) : Finset P :=
  Finset.univ.filter fun p => ∀ v ∈ triples a, p ∈ selected a v

abbrev Conditions (S : Finset V) (a : List Nat) : Prop :=
  (∀ p, Disjoint (lower a p) (lower a (bar p))) ∧
  (∀ v, (selected a v).card ≤ budget S v) ∧
  (∀ v, (selected a v).card = budget S v → ∀ r, touches v r →
    ∃ p ∈ selected a v, Disjoint (lower a p) (row r)) ∧
  (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ∀ p ∈ selected a x, ∀ q ∈ selected a x,
    p ≠ q → ¬ (omits a p y ∧ omits a q y)) ∧
  ((triples a).Nonempty → 2 ≤ (common a).card)

set_option synthInstance.maxSize 100000 in
def valid (S : Finset V) (a : List Nat) : Bool :=
  @decide (Conditions S a) (by unfold Conditions touches omits; infer_instance)

lemma valid_iff (S : Finset V) (a : List Nat) : valid S a = true ↔ Conditions S a := by
  unfold valid
  simp only [decide_eq_true_eq]
def groups (a : List Nat) : Nat := a.foldl (fun k c => max k (c / 2 + 1)) 0

def search (S : Finset V) : Nat → List Nat → List (List Nat)
  | 0, a => if valid S a then [a] else []
  | n + 1, a => if valid S a then
      (List.range (2 * groups a + 1)).flatMap fun c => search S n (a ++ [c])
    else []

def Admissible (S : Finset V) : List Nat → List Nat → Prop
  | p, [] => Conditions S p
  | p, c :: cs => Conditions S p ∧ c < 2 * groups p + 1 ∧ Admissible S (p ++ [c]) cs

lemma admissible_mem_search (S : Finset V) (p a : List Nat) (ha : Admissible S p a) :
    p ++ a ∈ search S a.length p := by
  induction a generalizing p with
  | nil =>
    have hp : valid S p = true := (valid_iff S p).mpr ha
    simp [search, hp]
  | cons c cs ih =>
    rcases ha with ⟨hp, hc, ht⟩
    have hv : valid S p = true := (valid_iff S p).mpr hp
    simp only [List.length_cons, search, hv, ↓reduceIte]
    apply List.mem_flatMap.mpr
    refine ⟨c, List.mem_range.mpr hc, ?_⟩
    simpa only [List.append_assoc, List.singleton_append] using ih (p ++ [c]) ht

def support (i : Fin 19) : Finset V :=
  decode ((![8,16,24,32,48,64,128,136,160,256,264,288,320,512,528,576,640,768,832] : Fin 19 → Nat) i)
def pattern45 : List Nat := [0,2,2,4,5,6,6,6,6]
def pattern37 : List Nat := [0,2,4,6,4,3,6,4,4]

end PEqualNP.Outside.L_meta_2590_aux.I2Census

namespace PEqualNP.Outside.L_meta_2590_aux.I2Census

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma search_0 : search (support 0) 9 [] = [] := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma search_1 : search (support 1) 9 [] = [] := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma search_2 : search (support 2) 9 [] = [] := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma search_3 : search (support 3) 9 [] = [] := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma search_4 : search (support 4) 9 [] = [pattern45] := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma search_5 : search (support 5) 9 [] = [] := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma search_6 : search (support 6) 9 [] = [] := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma search_7 : search (support 7) 9 [] = [pattern37] := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma search_8 : search (support 8) 9 [] = [] := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma search_9 : search (support 9) 9 [] = [] := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma search_10 : search (support 10) 9 [] = [] := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma search_11 : search (support 11) 9 [] = [] := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma search_12 : search (support 12) 9 [] = [] := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma search_13 : search (support 13) 9 [] = [] := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma search_14 : search (support 14) 9 [] = [] := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma search_15 : search (support 15) 9 [] = [] := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma search_16 : search (support 16) 9 [] = [] := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma search_17 : search (support 17) 9 [] = [] := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma search_18 : search (support 18) 9 [] = [] := by decide +kernel

lemma search_result (i : Fin 19) : search (support i) 9 [] =
    if i = 4 then [pattern45] else if i = 7 then [pattern37] else [] := by
  fin_cases i
  · exact search_0
  · exact search_1
  · exact search_2
  · exact search_3
  · exact search_4
  · exact search_5
  · exact search_6
  · exact search_7
  · exact search_8
  · exact search_9
  · exact search_10
  · exact search_11
  · exact search_12
  · exact search_13
  · exact search_14
  · exact search_15
  · exact search_16
  · exact search_17
  · exact search_18

lemma classified (S : Finset V) (a : List Nat) (hS : ∃ i, S = support i)
    (ha : Admissible S [] a) (hlen : a.length = 9) :
    (S = support 4 ∧ a = pattern45) ∨ (S = support 7 ∧ a = pattern37) := by
  obtain ⟨i, rfl⟩ := hS
  have hm := admissible_mem_search (support i) [] a ha
  simp only [List.nil_append, hlen] at hm
  rw [search_result] at hm
  split_ifs at hm with h4 h7
  · subst i
    exact Or.inl ⟨rfl, List.mem_singleton.mp hm⟩
  · subst i
    exact Or.inr ⟨rfl, List.mem_singleton.mp hm⟩
  · simp at hm

lemma admissible_of_prefix_conditions (S : Finset V) (p a : List Nat)
    (hc : ∀ b c, b ++ c = a → Conditions S (p ++ b))
    (hg : ∀ b c d, b ++ c :: d = a → c < 2 * groups (p ++ b) + 1) :
    Admissible S p a := by
  induction a generalizing p with
  | nil =>
    change Conditions S p
    simpa using hc [] [] rfl
  | cons c cs ih =>
    refine ⟨?_, ?_, ?_⟩
    · simpa using hc [] (c :: cs) rfl
    · simpa using hg [] c cs rfl
    · apply ih (p ++ [c])
      · intro b d hbd
        simpa only [List.append_assoc, List.singleton_append] using hc (c :: b) d (by simp [hbd])
      · intro b d es hbd
        simpa only [List.append_assoc, List.singleton_append] using hg (c :: b) d es (by simp [hbd])

end PEqualNP.Outside.L_meta_2590_aux.I2Census

namespace PEqualNP.Outside.L_meta_2590_aux.I2Census

lemma toggle_eq_flip (c : Nat) : toggle c = PortCodes.flip c := by
  unfold toggle PortCodes.flip
  split_ifs <;> omega

lemma groups_eq_portGroups (a : List Nat) : groups a = PortCodes.groups a := rfl

lemma admissible_of_growth (S : Finset V) (a : List Nat) (hg : PortCodes.Growth a)
    (hc : ∀ i, i ≤ a.length → Conditions S (a.take i)) : Admissible S [] a := by
  apply admissible_of_prefix_conditions S [] a
  · intro b c he
    have hb : b.length ≤ a.length := by rw [← he]; simp
    have ht : a.take b.length = b := by rw [← he]; simp
    simpa only [List.nil_append, ht] using hc b.length hb
  · intro b c d he
    have hb : b.length < a.length := by rw [← he]; simp
    have ht : a.take b.length = b := by rw [← he]; simp
    have hi : a[b.length] = c := by simp [← he]
    have hh := hg b.length hb
    rw [hi, ht] at hh
    change c < 2 * PortCodes.groups b + 1
    omega

lemma support_list_eq : List.ofFn support = I2ForbiddenPairs.supports := by decide +kernel

lemma support_exists_of_mem {S : Finset V} (hS : S ∈ I2ForbiddenPairs.supports) :
    ∃ i, S = support i := by
  rw [← support_list_eq] at hS
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hS
  exact ⟨i, hi.symm⟩

end PEqualNP.Outside.L_meta_2590_aux.I2Census

namespace PEqualNP.Outside.L_meta_2590_aux.I2Census

def lower45 : P → Finset V :=
  ![{0},{1,4,5},{2},{1,3,7},{1},{6},{3},{4,8},{5,9},{7},{4,5,6},{8,9},
    ∅,∅,∅,∅,∅,∅,∅,∅,∅,∅]
def lower37 : P → Finset V :=
  ![{0},{1,4,5},{2},{1,3,7},{1},{6},{3,9},{4},{3,6,7},{8,9},{5},{7,8},
    ∅,∅,∅,∅,∅,∅,∅,∅,∅,∅]

set_option synthInstance.maxSize 100000 in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma geometry45 : support 4 = {4,5} ∧ groups pattern45 = 4 ∧
    (∀ p, lower pattern45 p = lower45 p) ∧
    (∀ v, (selected pattern45 v).card = budget (support 4) v) ∧
    (∀ p, (lower pattern45 p).Nonempty ↔ p.val < 12) := by decide +kernel

set_option synthInstance.maxSize 100000 in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma geometry37 : support 7 = {3,7} ∧ groups pattern37 = 4 ∧
    (∀ p, lower pattern37 p = lower37 p) ∧
    (∀ v, (selected pattern37 v).card = budget (support 7) v) ∧
    (∀ p, (lower pattern37 p).Nonempty ↔ p.val < 12) := by decide +kernel

lemma classified_geometry (S : Finset V) (a : List Nat) (hS : ∃ i, S = support i)
    (ha : Admissible S [] a) (hlen : a.length = 9) :
    groups a = 4 ∧ (∀ v, (selected a v).card = budget S v) ∧
    (∀ p, (lower a p).Nonempty ↔ p.val < 12) ∧
    ((S = {4,5} ∧ ∀ p, lower a p = lower45 p) ∨
     (S = {3,7} ∧ ∀ p, lower a p = lower37 p)) := by
  rcases classified S a hS ha hlen with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨geometry45.2.1, geometry45.2.2.2.1, geometry45.2.2.2.2,
      Or.inl ⟨geometry45.1, geometry45.2.2.1⟩⟩
  · exact ⟨geometry37.2.1, geometry37.2.2.2.1, geometry37.2.2.2.2,
      Or.inr ⟨geometry37.1, geometry37.2.2.1⟩⟩

end PEqualNP.Outside.L_meta_2590_aux.I2Census

namespace PEqualNP.Outside.L_meta_2590_aux.DagTools

lemma same_residual_omitting_exits_equal {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}
    (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (b : Fin n → ℕ) (hb : PureBranch n D b)
    {x y : Fin n} (hxy : x ≠ y) (u0 : Σ _ : ℕ, ℕ)
    (hxcode : ((residualUnits n D b).filter (fun u => x ∈ supp n D u.1)) = {u0})
    (hycode : ((residualUnits n D b).filter (fun u => y ∈ supp n D u.1)) = {u0}) :
    ∀ e ∈ sem_W n D x, ∀ f ∈ sem_W n D x,
      y ∉ supp n D (src D e) → y ∉ supp n D (src D f) → e = f := by
  classical
  have hxu0 : u0 ∈ (residualUnits n D b).filter (fun u => x ∈ supp n D u.1) := by
    rw [hxcode]
    exact Finset.mem_singleton_self _
  have hyu0 : u0 ∈ (residualUnits n D b).filter (fun u => y ∈ supp n D u.1) := by
    rw [hycode]
    exact Finset.mem_singleton_self _
  obtain ⟨hu0, hx0⟩ := Finset.mem_filter.mp hxu0
  have hy0 : y ∈ supp n D u0.1 := (Finset.mem_filter.mp hyu0).2
  have hunit := (mem_units.mp
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp hu0).1).1).2
  have fan : 2 ≤ fanout D u0.1 := by omega
  have eligible : x ∈ eligSet n D := mem_eligSet.mpr ⟨u0.1, fan, hx0⟩
  have inclusion : ∀ u ∈ residualUnits n D b, x ∈ supp n D u.1 → y ∈ supp n D u.1 := by
    intro u hu hxu
    have hm : u ∈ (residualUnits n D b).filter (fun v => x ∈ supp n D v.1) :=
      Finset.mem_filter.mpr ⟨hu, hxu⟩
    rw [hxcode, Finset.mem_singleton] at hm
    rw [hm]
    exact hy0
  obtain ⟨e0, he0⟩ := ri_gen hG h hC b hb hxy eligible inclusion ⟨hx0, hy0⟩
  intro e he f hf hey hfy
  have heq : e = e0 := by
    by_contra hn
    exact hey (he0 e he hn)
  have hfq : f = e0 := by
    by_contra hn
    exact hfy (he0 f hf hn)
  exact heq.trans hfq.symm

lemma opposite_exit_omits {n : ℕ} {D : Dag} (hS : Strict n D)
    {e : ℕ × Bool} {y : Fin n} (hbar : sem_bar e ∈ sem_W n D y) :
    y ∉ supp n D (src D e) := by
  intro hy
  have he : e ∈ sem_W n D y :=
    sem_mem_W.mpr ⟨(sem_mem_W.mp hbar).1, hy, (sem_mem_W.mp hbar).2.2⟩
  exact sem_bar_ne e (W_gate_injective hS hbar he rfl)

end PEqualNP.Outside.L_meta_2590_aux.DagTools

namespace PEqualNP.Outside.L_meta_2590_aux.I2Census

open DagTools

lemma budget_and_shared_code {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (h0 : (0 : V) ∈ ineligSet 10 D) (h2 : (2 : V) ∈ ineligSet 10 D)
    (b : V → ℕ) (hb : PureBranch 10 D b)
    (u1 u2 : Σ _ : ℕ, ℕ) (S : Finset V)
    (hR : residualUnits 10 D b = {u1, u2})
    (hs1 : supp 10 D u1.1 = {(1 : V)}) (hs2 : supp 10 D u2.1 = S)
    (h1S : (1 : V) ∉ S) :
    (∀ x ∈ S, (residualUnits 10 D b).filter (fun u => x ∈ supp 10 D u.1) = {u2}) ∧
      ∀ v : V, (sem_W 10 D v).card ≤ budget S v := by
  classical
  have code (v : V) (hv : v ≠ 1) :
      ((residualUnits 10 D b).filter (fun u => v ∈ supp 10 D u.1)).card ≤
        if v ∈ S then 1 else 0 := by
    rw [hR]
    by_cases hs : v ∈ S <;>
      simp [Finset.filter_insert, Finset.filter_singleton, hs1, hs2, hv, hs]
  have code1 : ((residualUnits 10 D b).filter
      (fun u => (1 : V) ∈ supp 10 D u.1)).card ≤ 1 := by
    rw [hR]
    simp [Finset.filter_insert, Finset.filter_singleton, hs1, hs2, h1S]
  refine ⟨?_, ?_⟩
  · intro x hx
    have hx1 : x ≠ 1 := by intro he; subst x; exact h1S hx
    rw [hR]
    simp [Finset.filter_insert, Finset.filter_singleton, hs1, hs2, hx1, hx]
  · intro v
    by_cases hi : v = 0 ∨ v = 2
    · rcases hi with rfl | rfl
      · have flow := sem_flow1 graph_ok h hc (0 : V)
        rw [sem_inelig_surplus h0] at flow
        have cap : (sem_W 10 D (0 : V)).card ≤ 1 := by omega
        simpa [budget] using cap
      · have flow := sem_flow1 graph_ok h hc (2 : V)
        rw [sem_inelig_surplus h2] at flow
        have cap : (sem_W 10 D (2 : V)).card ≤ 1 := by omega
        simpa [budget] using cap
    · have count := sem_code_count graph_ok h hc b hb v
      have single : (({v} : Finset V) ∩ eligSet 10 D).card ≤ 1 :=
        (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
      by_cases hv1 : v = 1
      · subst v
        have cap : (sem_W 10 D (1 : V)).card ≤ 3 := by omega
        simpa [budget] using cap
      · have extra := code v hv1
        have cap : (sem_W 10 D v).card ≤ 2 + if v ∈ S then 1 else 0 := by omega
        simpa [budget, hi, hv1] using cap

end PEqualNP.Outside.L_meta_2590_aux.I2Census

namespace PEqualNP.Outside.L_meta_2590_aux.I2Census

open DagTools

lemma row_independent : ∀ r : Fin 15, ∀ x ∈ row r, ∀ y ∈ row r, ¬ adj x y := by
  decide +kernel

lemma touches_neighbor : ∀ (v : V) (r : Fin 15), touches v r → ∃ x ∈ row r, adj v x := by
  decide +kernel

lemma conditions_of_semantics {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (b : V → ℕ) (hb : sem_MinBranch 10 D b)
    (S : Finset V) (a : List Nat) (u0 : Σ _ : ℕ, ℕ)
    (hcode : ∀ x ∈ S,
      (residualUnits 10 D b).filter (fun u => x ∈ supp 10 D u.1) = {u0})
    (hbudget : ∀ v : V, (sem_W 10 D v).card ≤ budget S v)
    (f : P → ℕ × Bool)
    (hbar : ∀ p : P, f (bar p) = sem_bar (f p))
    (hinj : ∀ p q : P, (lower a p).Nonempty → (lower a q).Nonempty →
      f p = f q → p = q)
    (hselected : ∀ (p : P) (v : V), v ∈ lower a p → f p ∈ sem_W 10 D v)
    (hfixed : ∀ p : P, p.val < 4 → supp 10 D (src D (f p)) = lower a p) :
    Conditions S a := by
  classical
  have selected_mem (v : V) (p : P) : p ∈ selected a v ↔ v ∈ lower a p := by
    simp only [selected, Finset.mem_filter, Finset.mem_univ, true_and]
  have label_sub (p : P) : lower a p ⊆ supp 10 D (src D (f p)) := by
    intro v hv
    exact (sem_mem_W.mp (hselected p v hv)).2.1
  have image_sub (v : V) : (selected a v).image f ⊆ sem_W 10 D v := by
    intro e he
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    exact hselected p v ((selected_mem v p).mp hp)
  have image_card (v : V) : ((selected a v).image f).card = (selected a v).card := by
    apply Finset.card_image_of_injOn
    intro p hp q hq he
    exact hinj p q ⟨v, (selected_mem v p).mp hp⟩ ⟨v, (selected_mem v q).mp hq⟩ he
  have selected_le (v : V) : (selected a v).card ≤ (sem_W 10 D v).card := by
    rw [← image_card v]
    exact Finset.card_le_card (image_sub v)
  have image_eq (v : V) (hsat : (selected a v).card = budget S v) :
      (selected a v).image f = sem_W 10 D v := by
    apply Finset.eq_of_subset_of_card_le (image_sub v)
    rw [image_card v, hsat]
    exact hbudget v
  have pullback (v : V) (hsat : (selected a v).card = budget S v)
      (e : ℕ × Bool) (he : e ∈ sem_W 10 D v) :
      ∃ p ∈ selected a v, f p = e := by
    rw [← image_eq v hsat] at he
    exact Finset.mem_image.mp he
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p
    apply Finset.disjoint_left.mpr
    intro v hv hvbar
    have he := hselected p v hv
    have hother := hselected (bar p) v hvbar
    rw [hbar] at hother
    have eq := W_gate_injective h.1 he hother rfl
    exact sem_bar_ne (f p) eq.symm
  · intro v
    exact (selected_le v).trans (hbudget v)
  · intro v hsat r htouch
    obtain ⟨j, s, hj, _, hvs, hvout, hdis⟩ :=
      sem_exposure graph_ok h.1 hc (row r) (row_independent r) v (touches_neighbor v r htouch)
    have he : (j, s) ∈ sem_W 10 D v := sem_mem_W.mpr ⟨hj, hvs, hvout⟩
    obtain ⟨p, hp, hpe⟩ := pullback v hsat (j, s) he
    refine ⟨p, hp, Finset.disjoint_left.mpr ?_⟩
    intro y hy hyr
    have hys := label_sub p hy
    rw [hpe] at hys
    exact Finset.disjoint_left.mp hdis hys hyr
  · intro x hx y hy hxy p hp q hq hpq homit
    have omission (r : P) (hr : omits a r y) : y ∉ supp 10 D (src D (f r)) := by
      by_cases hsmall : r.val < 4
      · rw [hfixed r hsmall]
        simpa only [omits, hsmall, ite_true] using hr
      · have hyr : y ∈ lower a (bar r) := by
          simpa only [omits, hsmall, ite_false] using hr
        have hother := hselected (bar r) y hyr
        rw [hbar] at hother
        exact opposite_exit_omits h.1 hother
    have eq : f p = f q := same_residual_omitting_exits_equal graph_ok h hc b
      (sem_minBranch_pure hb) hxy u0 (hcode x hx) (hcode y hy)
      (f p) (hselected p x ((selected_mem x p).mp hp))
      (f q) (hselected q x ((selected_mem x q).mp hq))
      (omission p homit.1) (omission q homit.2)
    exact hpq (hinj p q ⟨x, (selected_mem x p).mp hp⟩
      ⟨x, (selected_mem x q).mp hq⟩ eq)
  · intro nonempty
    have triple_facts (v : V) (hv : v ∈ triples a) :
        v ∈ S ∧ (selected a v).card = budget S v ∧ 3 ≤ (sem_W 10 D v).card := by
      have facts := (Finset.mem_filter.mp hv).2
      have ne0 : v ≠ 0 := by intro eq; subst v; simp at facts
      have ne1 : v ≠ 1 := by intro eq; subst v; simp at facts
      have ne2 : v ≠ 2 := by intro eq; subst v; simp at facts
      have inS : v ∈ S := by
        by_contra hn
        have bound := (selected_le v).trans (hbudget v)
        simp only [budget, ne0, ne1, ne2, or_self, ite_false, hn] at bound
        omega
      refine ⟨inS, ?_, ?_⟩
      · simpa only [budget, ne0, ne1, ne2, or_self, ite_false, inS, ite_true] using facts.2
      · have bound := selected_le v
        omega
    obtain ⟨P0, Q0, hPQ, hall, _, _⟩ := sem_local_common_terminals_support
      graph_ok h hc b hb (triples a) nonempty u0
      (fun v hv => hcode v (triple_facts v hv).1)
      (fun v hv => (triple_facts v hv).2.2)
    obtain ⟨v0, hv0⟩ := nonempty
    obtain ⟨p, hp, hpe⟩ := pullback v0 (triple_facts v0 hv0).2.1 P0 (hall v0 hv0).1
    obtain ⟨q, hq, hqe⟩ := pullback v0 (triple_facts v0 hv0).2.1 Q0 (hall v0 hv0).2
    have shared (r : P) (hr : r ∈ selected a v0) (e : ℕ × Bool) (hre : f r = e)
        (he : ∀ v ∈ triples a, e ∈ sem_W 10 D v) : r ∈ common a := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro v hv
      obtain ⟨r', hr', hr'e⟩ := pullback v (triple_facts v hv).2.1 e (he v hv)
      have eq : r' = r := hinj r' r ⟨v, (selected_mem v r').mp hr'⟩
        ⟨v0, (selected_mem v0 r).mp hr⟩ (hr'e.trans hre.symm)
      exact eq ▸ hr'
    have hpcommon := shared p hp P0 hpe (fun v hv => (hall v hv).1)
    have hqcommon := shared q hq Q0 hqe (fun v hv => (hall v hv).2)
    have hpq : p ≠ q := by
      intro eq
      have hsame : P0 = Q0 := hpe.symm.trans ((congrArg f eq).trans hqe)
      exact hPQ (congrArg Prod.fst hsame)
    have card : 1 < (common a).card := Finset.one_lt_card.mpr ⟨p, hpcommon, q, hqcommon, hpq⟩
    omega

end PEqualNP.Outside.L_meta_2590_aux.I2Census

namespace PEqualNP.Outside.L_meta_2590_aux.I2Census

open DagTools

lemma budget_flow_bound {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (h0 : (0 : V) ∈ ineligSet 10 D) (h2 : (2 : V) ∈ ineligSet 10 D)
    (b : V → ℕ) (hb : PureBranch 10 D b)
    (u1 u2 : Σ _ : ℕ, ℕ) (S : Finset V)
    (hR : residualUnits 10 D b = {u1, u2})
    (hs1 : supp 10 D u1.1 = {(1 : V)}) (hs2 : supp 10 D u2.1 = S)
    (h1S : (1 : V) ∉ S) :
    ∀ v : V, 1 + (({v} : Finset V) ∩ eligSet 10 D).card +
      ((residualUnits 10 D b).filter (fun u => v ∈ supp 10 D u.1)).card ≤ budget S v := by
  classical
  have code (v : V) (hv : v ≠ 1) :
      ((residualUnits 10 D b).filter (fun u => v ∈ supp 10 D u.1)).card ≤
        if v ∈ S then 1 else 0 := by
    rw [hR]
    by_cases hs : v ∈ S <;>
      simp [Finset.filter_insert, Finset.filter_singleton, hs1, hs2, hv, hs]
  have code1 : ((residualUnits 10 D b).filter
      (fun u => (1 : V) ∈ supp 10 D u.1)).card ≤ 1 := by
    rw [hR]
    simp [Finset.filter_insert, Finset.filter_singleton, hs1, hs2, h1S]
  intro v
  by_cases hi : v = 0 ∨ v = 2
  · rcases hi with rfl | rfl
    · have flow := sem_flow1 graph_ok h hc (0 : V)
      rw [sem_inelig_surplus h0] at flow
      have count := sem_code_count graph_ok h hc b hb (0 : V)
      rw [show budget S (0 : V) = 1 by simp [budget]]
      omega
    · have flow := sem_flow1 graph_ok h hc (2 : V)
      rw [sem_inelig_surplus h2] at flow
      have count := sem_code_count graph_ok h hc b hb (2 : V)
      rw [show budget S (2 : V) = 1 by simp [budget]]
      omega
  · have single : (({v} : Finset V) ∩ eligSet 10 D).card ≤ 1 :=
      (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
    by_cases hv1 : v = 1
    · subst v
      rw [show budget S (1 : V) = 3 by simp [budget]]
      omega
    · have extra := code v hv1
      rw [show budget S v = 2 + if v ∈ S then 1 else 0 by simp [budget, hi, hv1]]
      omega

end PEqualNP.Outside.L_meta_2590_aux.I2Census

namespace PEqualNP.Outside.L_meta_2590_aux.I2Census

open DagTools

def freePair (i : Fin 9) : V × V := freeEdges.getD i.val (0, 0)

lemma free_pair_geometry : ∀ i : Fin 9,
    adj (freePair i).1 (freePair i).2 ∧
    (freePair i).1 ≠ 0 ∧ (freePair i).2 ≠ 0 ∧
    (freePair i).1 ≠ 2 ∧ (freePair i).2 ≠ 2 := by
  decide +kernel

lemma free_ports_zip {D : Dag} (e : Fin 9 → ℕ × Bool)
    (he : ∀ i : Fin 9, e i ∈ sem_W 10 D (freePair i).1 ∧
      sem_bar (e i) ∈ sem_W 10 D (freePair i).2) :
    ∀ z ∈ (List.ofFn e).zip freeEdges,
      z.1 ∈ sem_W 10 D z.2.1 ∧ sem_bar z.1 ∈ sem_W 10 D z.2.2 := by
  intro z hz
  have zip_eq : (List.ofFn e).zip freeEdges =
      List.ofFn (fun i : Fin 9 => (e i, freePair i)) := by rfl
  rw [zip_eq] at hz
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
  exact he i

lemma edge_exit_avoids_pure_gate {D : Dag}
    {e A : ℕ × Bool} {x y i : V}
    (he : e ∈ sem_W 10 D x) (hbar : sem_bar e ∈ sem_W 10 D y)
    (hpure : supp 10 D (src D A) = {i}) (hxi : x ≠ i) (hyi : y ≠ i) :
    e.1 ≠ A.1 := by
  intro eq
  rcases sem_same_gate eq.symm with heq | heq
  · have hm := (sem_mem_W.mp he).2.1
    rw [heq, hpure, Finset.mem_singleton] at hm
    exact hxi hm
  · have hm := (sem_mem_W.mp hbar).2.1
    rw [heq, sem_bar_bar, hpure, Finset.mem_singleton] at hm
    exact hyi hm

lemma actual_free_port_choice {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (small : D.length ≤ 19) (hi : (ineligSet 10 D).card = 2)
    (h0 : (0 : V) ∈ ineligSet 10 D) (h2 : (2 : V) ∈ ineligSet 10 D) :
    ∃ A B : ℕ × Bool, ∃ e : Fin 9 → ℕ × Bool,
      CleanStarAt 10 adj D (0 : V) A ∧ CleanStarAt 10 adj D (2 : V) B ∧
      A.1 ≠ B.1 ∧
      ∀ i : Fin 9,
        e i ∈ sem_W 10 D (freePair i).1 ∧
        sem_bar (e i) ∈ sem_W 10 D (freePair i).2 ∧
        (e i).1 ≠ A.1 ∧ (e i).1 ≠ B.1 := by
  classical
  obtain ⟨⟨A, hA⟩, ⟨B, hB⟩⟩ := petersen_two_ineligible_clean_stars h hc small hi h0 h2
  have pureA : supp 10 D (src D A) = {(0 : V)} := hA.2.2.1
  have pureB : supp 10 D (src D B) = {(2 : V)} := hB.2.2.1
  have oneA : (1 : V) ∈ supp 10 D (src D (sem_bar A)) :=
    (hA.2.2.2.2.2.2.1 1).mpr (by decide)
  have neAB : A.1 ≠ B.1 := by
    intro eq
    rcases sem_same_gate eq with heq | heq
    · have zeroA : (0 : V) ∈ supp 10 D (src D A) := by rw [pureA]; simp
      rw [← heq, pureB, Finset.mem_singleton] at zeroA
      exact (by decide : (0 : V) ≠ 2) zeroA
    · rw [← heq, pureB, Finset.mem_singleton] at oneA
      exact (by decide : (1 : V) ≠ 2) oneA
  have witnesses : ∀ i : Fin 9, ∃ e : ℕ × Bool,
      e ∈ sem_W 10 D (freePair i).1 ∧ sem_bar e ∈ sem_W 10 D (freePair i).2 := by
    intro i
    obtain ⟨e, he, hbar, _, _, _⟩ := sem_edge_slots graph_ok h.1 hc (free_pair_geometry i).1
    exact ⟨e, he, hbar⟩
  choose e he using witnesses
  refine ⟨A, B, e, hA, hB, neAB, ?_⟩
  intro i
  have geometry := (free_pair_geometry i).2
  exact ⟨(he i).1, (he i).2,
    edge_exit_avoids_pure_gate (he i).1 (he i).2 pureA geometry.1 geometry.2.1,
    edge_exit_avoids_pure_gate (he i).1 (he i).2 pureB geometry.2.2.1 geometry.2.2.2⟩

end PEqualNP.Outside.L_meta_2590_aux.I2Census

namespace PEqualNP.Outside.L_meta_2590_aux.I2Census

lemma zip_fst_mem {α β : Type} (a : List α) :
    ∀ (b : List β) (z : α × β), z ∈ a.zip b → z.1 ∈ a := by
  induction a with
  | nil =>
    intro b z hz
    simp at hz
  | cons x a ih =>
    intro b z hz
    cases b with
    | nil => simp at hz
    | cons y b =>
      change z ∈ (x, y) :: a.zip b at hz
      rcases List.mem_cons.mp hz with he | hz
      · rw [he]
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih b z hz)

lemma lower_free_witness (a : List Nat) (p : P) (hp : 4 ≤ p.val)
    {v : V} (hv : v ∈ lower a p) :
    ∃ z ∈ a.zip freeEdges,
      (z.1 + 4 = p.val ∧ v = z.2.1) ∨
      (toggle z.1 + 4 = p.val ∧ v = z.2.2) := by
  rw [lower, if_neg (by omega : ¬ p.val < 4)] at hv
  have hv' : v ∈ (a.zip freeEdges).flatMap (fun z =>
      if z.1 + 4 = p.val then [z.2.1]
      else if toggle z.1 + 4 = p.val then [z.2.2]
      else []) := by
    simpa only [List.mem_toFinset] using hv
  obtain ⟨z, hz, hvz⟩ := List.mem_flatMap.mp hv'
  refine ⟨z, hz, ?_⟩
  by_cases hfirst : z.1 + 4 = p.val
  · exact Or.inl ⟨hfirst, by simpa [hfirst] using hvz⟩
  · by_cases hsecond : toggle z.1 + 4 = p.val
    · exact Or.inr ⟨hsecond, by simpa [hfirst, hsecond] using hvz⟩
    · simp [hfirst, hsecond] at hvz

lemma lower_nonempty_bound (a : List Nat)
    (hcodes : ∀ c ∈ a, c < 2 * PortCodes.groups a)
    (p : P) (hp : (lower a p).Nonempty) :
    p.val < 4 + 2 * PortCodes.groups a := by
  by_cases hsmall : p.val < 4
  · omega
  obtain ⟨v, hv⟩ := hp
  obtain ⟨z, hz, hcase⟩ := lower_free_witness a p (by omega) hv
  have hc := hcodes z.1 (zip_fst_mem a freeEdges z hz)
  rcases hcase with ⟨he, _⟩ | ⟨he, _⟩
  · omega
  · have ht : toggle z.1 < 2 * PortCodes.groups a := by
      rw [toggle_eq_flip]
      exact PortCodes.flip_lt hc
    omega

lemma zip_take_mem {α β : Type} (i : ℕ) :
    ∀ (a : List α) (b : List β) (z : α × β),
      z ∈ (a.take i).zip b → z ∈ a.zip b := by
  induction i with
  | zero =>
    intro a b z hz
    simp at hz
  | succ i ih =>
    intro a b z hz
    cases a with
    | nil => simp at hz
    | cons x a =>
      cases b with
      | nil => simp at hz
      | cons y b =>
        change z ∈ (x, y) :: (a.take i).zip b at hz
        change z ∈ (x, y) :: a.zip b
        rcases List.mem_cons.mp hz with hz | hz
        · exact List.mem_cons.mpr (Or.inl hz)
        · exact List.mem_cons.mpr (Or.inr (ih a b z hz))

lemma lower_take_subset (a : List Nat) (i : ℕ) (p : P) :
    lower (a.take i) p ⊆ lower a p := by
  intro v hv
  by_cases hp : p.val < 4
  · simpa only [lower, if_pos hp] using hv
  · rw [lower, if_neg hp] at hv ⊢
    obtain ⟨z, hz, hzv⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp hv)
    exact List.mem_toFinset.mpr
      (List.mem_flatMap.mpr ⟨z, zip_take_mem i a freeEdges z hz, hzv⟩)

end PEqualNP.Outside.L_meta_2590_aux.I2Census

namespace PEqualNP.Outside.L_meta_2590_aux.I2Census

open DagTools

def fixedMap (A B : ℕ × Bool) (r : ℕ → ℕ × Bool) (p : P) : ℕ × Bool :=
  PortCodes.decode (PortCodes.fixedReps A B r) p.val

lemma fixedMap_bar (A B : ℕ × Bool) (r : ℕ → ℕ × Bool) (p : P) :
    fixedMap A B r (bar p) = sem_bar (fixedMap A B r p) := by
  have hp : (bar p).val = PortCodes.flip p.val := toggle_eq_flip p.val
  simp only [fixedMap, hp, PortCodes.decode_flip]
  rfl

lemma fixedMap_injective_nonempty (a : List Nat) (A B : ℕ × Bool) (r : ℕ → ℕ × Bool)
    (hcodes : ∀ c ∈ a, c < 2 * PortCodes.groups a)
    (hAB : A.1 ≠ B.1)
    (hA : ∀ i < PortCodes.groups a, (r i).1 ≠ A.1)
    (hB : ∀ i < PortCodes.groups a, (r i).1 ≠ B.1)
    (hr : ∀ i j, i < PortCodes.groups a → j < PortCodes.groups a →
      (r i).1 = (r j).1 → i = j)
    (p q : P) (hp : (lower a p).Nonempty) (hq : (lower a q).Nonempty)
    (he : fixedMap A B r p = fixedMap A B r q) : p = q := by
  have hrep := PortCodes.fixedReps_injective A B r (PortCodes.groups a) hAB hA hB hr
  have hpbound := lower_nonempty_bound a hcodes p hp
  have hqbound := lower_nonempty_bound a hcodes q hq
  apply Fin.ext
  exact PortCodes.decode_injective_below (PortCodes.groups a + 2)
    (PortCodes.fixedReps A B r) (fun i hi j hj => hrep i j hi hj)
    (by omega) (by omega) he

lemma lower_fixed_zero (a : List Nat) : lower a (0 : P) = {0} := by change decode 1 = {0}; decide
lemma lower_fixed_one (a : List Nat) : lower a (1 : P) = {1, 4, 5} := by change decode 50 = {1, 4, 5}; decide
lemma lower_fixed_two (a : List Nat) : lower a (2 : P) = {2} := by change decode 4 = {2}; decide
lemma lower_fixed_three (a : List Nat) : lower a (3 : P) = {1, 3, 7} := by change decode 138 = {1, 3, 7}; decide

lemma fixedMap_fixed_data {D : Dag} (a : List Nat) (A B : ℕ × Bool) (r : ℕ → ℕ × Bool)
    (hA : CleanStarAt 10 adj D (0 : V) A) (hB : CleanStarAt 10 adj D (2 : V) B)
    (p : P) (hp : p.val < 4) :
    (fixedMap A B r p).1 < D.length ∧
      supp 10 D (src D (fixedMap A B r p)) = lower a p ∧
      supp 10 D (10 + (fixedMap A B r p).1) = ∅ := by
  obtain ⟨ha, _, hap, hao, _, _, han, _⟩ := hA
  obtain ⟨hb, _, hbp, hbo, _, _, hbn, _⟩ := hB
  have has : supp 10 D (src D (sem_bar A)) = {1, 4, 5} := by
    ext v
    rw [han v]
    have hn : ∀ v : V, adj 0 v ↔ v ∈ ({1, 4, 5} : Finset V) := by decide
    exact hn v
  have hbs : supp 10 D (src D (sem_bar B)) = {1, 3, 7} := by
    ext v
    rw [hbn v]
    have hn : ∀ v : V, adj 2 v ↔ v ∈ ({1, 3, 7} : Finset V) := by decide
    exact hn v
  by_cases hp0 : p.val = 0
  · have heq : p = 0 := Fin.ext hp0
    subst p
    simpa only [fixedMap, PortCodes.decode_fixed_zero, lower_fixed_zero] using ⟨ha, hap, hao⟩
  by_cases hp1 : p.val = 1
  · have heq : p = 1 := Fin.ext hp1
    subst p
    simpa only [fixedMap, PortCodes.decode_fixed_one, lower_fixed_one, PortCodes.bar, sem_bar] using
      ⟨ha, has, hao⟩
  by_cases hp2 : p.val = 2
  · have heq : p = 2 := Fin.ext hp2
    subst p
    simpa only [fixedMap, PortCodes.decode_fixed_two, lower_fixed_two] using ⟨hb, hbp, hbo⟩
  have hp3 : p.val = 3 := by omega
  have heq : p = 3 := Fin.ext hp3
  subst p
  simpa only [fixedMap, PortCodes.decode_fixed_three, lower_fixed_three, PortCodes.bar, sem_bar] using
    ⟨hb, hbs, hbo⟩

lemma fixedMap_selected {D : Dag} (a : List Nat) (A B : ℕ × Bool) (r : ℕ → ℕ × Bool)
    (hA : CleanStarAt 10 adj D (0 : V) A) (hB : CleanStarAt 10 adj D (2 : V) B)
    (hzip : ∀ z ∈ a.zip freeEdges,
      PortCodes.decode r z.1 ∈ sem_W 10 D z.2.1 ∧
      sem_bar (PortCodes.decode r z.1) ∈ sem_W 10 D z.2.2)
    (p : P) (v : V) (hv : v ∈ lower a p) : fixedMap A B r p ∈ sem_W 10 D v := by
  by_cases hp : p.val < 4
  · obtain ⟨hgate, hsupport, hzero⟩ := fixedMap_fixed_data (D := D) a A B r hA hB p hp
    apply sem_mem_W.mpr
    refine ⟨hgate, hsupport.symm ▸ hv, ?_⟩
    rw [hzero]
    exact Finset.notMem_empty v
  · obtain ⟨z, hz, hcase⟩ := lower_free_witness a p (by omega) hv
    rcases hcase with ⟨he, rfl⟩ | ⟨he, rfl⟩
    · simpa only [fixedMap, ← he, PortCodes.decode_fixed_add_four] using (hzip z hz).1
    · simpa only [fixedMap, ← he, PortCodes.decode_fixed_add_four, toggle_eq_flip,
        PortCodes.decode_flip, PortCodes.bar, sem_bar] using (hzip z hz).2

lemma zip_map_fst_mem {α β γ : Type} (f : α → γ) (a : List α) :
    ∀ (b : List β) (z : α × β), z ∈ a.zip b → (f z.1, z.2) ∈ (a.map f).zip b := by
  induction a with
  | nil => intro b z hz; simp at hz
  | cons x a ih =>
    intro b z hz
    cases b with
    | nil => simp at hz
    | cons y b =>
      change z ∈ (x, y) :: a.zip b at hz
      change (f z.1, z.2) ∈ (f x, y) :: (a.map f).zip b
      rcases List.mem_cons.mp hz with rfl | hz
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih b z hz)

lemma normalize_actual_ports {D : Dag} (A B : ℕ × Bool) (e : Fin 9 → ℕ × Bool)
    (hA : CleanStarAt 10 adj D (0 : V) A) (hB : CleanStarAt 10 adj D (2 : V) B)
    (hAB : A.1 ≠ B.1)
    (he : ∀ i : Fin 9,
      e i ∈ sem_W 10 D (freePair i).1 ∧ sem_bar (e i) ∈ sem_W 10 D (freePair i).2 ∧
      (e i).1 ≠ A.1 ∧ (e i).1 ≠ B.1) :
    ∃ a : List Nat, ∃ f : P → ℕ × Bool,
      a.length = 9 ∧ PortCodes.Growth a ∧
      (∀ p, f (bar p) = sem_bar (f p)) ∧
      (∀ p q, (lower a p).Nonempty → (lower a q).Nonempty → f p = f q → p = q) ∧
      (∀ p v, v ∈ lower a p → f p ∈ sem_W 10 D v) ∧
      (∀ p, p.val < 4 → supp 10 D (src D (f p)) = lower a p) := by
  obtain ⟨a, r, hmap, hgrowth, hcodes, hr⟩ := PortCodes.normalize (List.ofFn e)
  have hlen : a.length = 9 := by simpa using congrArg List.length hmap
  have avoidA := PortCodes.representatives_avoid a r (List.ofFn e) A.1 hmap hgrowth
    (by intro z hz; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz; exact (he i).2.2.1)
  have avoidB := PortCodes.representatives_avoid a r (List.ofFn e) B.1 hmap hgrowth
    (by intro z hz; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz; exact (he i).2.2.2)
  have hzip : ∀ z ∈ a.zip freeEdges,
      PortCodes.decode r z.1 ∈ sem_W 10 D z.2.1 ∧
      sem_bar (PortCodes.decode r z.1) ∈ sem_W 10 D z.2.2 := by
    intro z hz
    have hm := zip_map_fst_mem (PortCodes.decode r) a freeEdges z hz
    rw [hmap] at hm
    exact free_ports_zip (D := D) e (fun i => ⟨(he i).1, (he i).2.1⟩)
      (PortCodes.decode r z.1, z.2) hm
  refine ⟨a, fixedMap A B r, hlen, hgrowth, fixedMap_bar A B r, ?_, ?_, ?_⟩
  · exact fixedMap_injective_nonempty a A B r hcodes hAB avoidA avoidB hr
  · exact fixedMap_selected (D := D) a A B r hA hB hzip
  · intro p hp
    exact (fixedMap_fixed_data (D := D) a A B r hA hB p hp).2.1

lemma map_properties_take {D : Dag} (a : List Nat) (f : P → ℕ × Bool)
    (hinj : ∀ p q, (lower a p).Nonempty → (lower a q).Nonempty → f p = f q → p = q)
    (hselected : ∀ p v, v ∈ lower a p → f p ∈ sem_W 10 D v)
    (hfixed : ∀ p, p.val < 4 → supp 10 D (src D (f p)) = lower a p)
    (i : ℕ) :
    (∀ p q, (lower (a.take i) p).Nonempty → (lower (a.take i) q).Nonempty →
      f p = f q → p = q) ∧
    (∀ p v, v ∈ lower (a.take i) p → f p ∈ sem_W 10 D v) ∧
    (∀ p, p.val < 4 → supp 10 D (src D (f p)) = lower (a.take i) p) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p q hp hq he
    apply hinj p q ?_ ?_ he
    · obtain ⟨v, hv⟩ := hp
      exact ⟨v, lower_take_subset a i p hv⟩
    · obtain ⟨v, hv⟩ := hq
      exact ⟨v, lower_take_subset a i q hv⟩
  · intro p v hv
    exact hselected p v (lower_take_subset a i p hv)
  · intro p hp
    simpa only [lower, if_pos hp] using hfixed p hp

end PEqualNP.Outside.L_meta_2590_aux.I2Census

namespace PEqualNP.Outside.L_meta_2590_aux.I2Census

open DagTools

lemma saturated_actual_sources {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (b : V → ℕ) (hb : PureBranch 10 D b)
    (S : Finset V) (a : List ℕ) (f : P → ℕ × Bool)
    (hinj : ∀ p q, (lower a p).Nonempty → (lower a q).Nonempty → f p = f q → p = q)
    (hselected : ∀ p v, v ∈ lower a p → f p ∈ sem_W 10 D v)
    (hflow : ∀ v, 1 + (({v} : Finset V) ∩ eligSet 10 D).card +
      ((residualUnits 10 D b).filter (fun u => v ∈ supp 10 D u.1)).card ≤ budget S v)
    (hsat : ∀ v, (selected a v).card = budget S v) :
    (∀ v, merges 10 D (carrierT 10 D {v}) = ∅) ∧
    (∀ p, (lower a p).Nonempty → supp 10 D (src D (f p)) = lower a p) ∧
    (∀ v, sem_W 10 D v = (selected a v).image f) := by
  classical
  have selected_mem (v : V) (p : P) : p ∈ selected a v ↔ v ∈ lower a p := by
    simp only [selected, Finset.mem_filter, Finset.mem_univ, true_and]
  have image_sub (v : V) : (selected a v).image f ⊆ sem_W 10 D v := by
    intro e he
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp he
    exact hselected p v ((selected_mem v p).mp hp)
  have image_card (v : V) : ((selected a v).image f).card = budget S v := by
    rw [← hsat v]
    apply Finset.card_image_of_injOn
    intro p hp q hq he
    exact hinj p q ⟨v,(selected_mem v p).mp hp⟩ ⟨v,(selected_mem v q).mp hq⟩ he
  have paired (v : V) : sem_W 10 D v = (selected a v).image f ∧
      merges 10 D (carrierT 10 D {v}) = ∅ := by
    have count := sem_code_count graph_ok h hc b hb v
    have flow := hflow v
    have lowerBound := Finset.card_le_card (image_sub v)
    rw [image_card v] at lowerBound
    have hle : (sem_W 10 D v).card ≤ ((selected a v).image f).card := by
      rw [image_card v]
      omega
    exact ⟨(Finset.eq_of_subset_of_card_le (image_sub v) hle).symm,
      Finset.card_eq_zero.mp (by omega)⟩
  have hm : ∀ v, merges 10 D (carrierT 10 D {v}) = ∅ := fun v => (paired v).2
  refine ⟨hm, ?_, fun v => (paired v).1⟩
  intro p hp
  obtain ⟨x,hx⟩ := hp
  have he := hselected p x hx
  have hj := (sem_mem_W.mp he).1
  have ht := sem_W_and h.1 he
  ext v
  constructor
  · intro hv
    have hw := (sem_sat_mem_W_iff_src h.1 hm hj ht v).mpr hv
    rw [(paired v).1] at hw
    obtain ⟨q,hq,heq⟩ := Finset.mem_image.mp hw
    have hqv := (selected_mem v q).mp hq
    have eq := hinj q p ⟨v,hqv⟩ ⟨x,hx⟩ heq
    exact eq ▸ hqv
  · intro hv
    exact (sem_mem_W.mp (hselected p v hv)).2.1

lemma saturated_actual_and_signature {D : Dag}
    (hS : Strict 10 D) (a : List ℕ) (f : P → ℕ × Bool)
    (hbar : ∀ p, f (bar p) = sem_bar (f p))
    (hnonempty : ∀ p, (lower a p).Nonempty → (lower a (bar p)).Nonempty)
    (hm : ∀ v, merges 10 D (carrierT 10 D {v}) = ∅)
    (hfull : ∀ p, (lower a p).Nonempty → supp 10 D (src D (f p)) = lower a p)
    (hW : ∀ v, sem_W 10 D v = (selected a v).image f)
    {j : ℕ} (hj : j < D.length) (ht : tag D j = true) :
    (∃ p, (lower a p).Nonempty ∧ f p = (j,false) ∧
      supp 10 D (opA D j) = lower a p ∧ supp 10 D (opB D j) = lower a (bar p)) ∨
      (supp 10 D (opA D j) = ∅ ∧ supp 10 D (opB D j) = ∅) := by
  classical
  have recover (e : ℕ × Bool) (he : e.1 < D.length) (ht : tag D e.1 = true)
      (hsrc : (supp 10 D (src D e)).Nonempty) :
      ∃ p, (lower a p).Nonempty ∧ f p = e := by
    obtain ⟨v,hv⟩ := hsrc
    have hw := (sem_sat_mem_W_iff_src hS hm he ht v).mpr hv
    rw [hW v] at hw
    obtain ⟨p,hp,hpe⟩ := Finset.mem_image.mp hw
    exact ⟨p, ⟨v,(Finset.mem_filter.mp hp).2⟩,hpe⟩
  have build (p : P) (hp : (lower a p).Nonempty) (he : f p = (j,false)) :
      ∃ p, (lower a p).Nonempty ∧ f p = (j,false) ∧
      supp 10 D (opA D j) = lower a p ∧ supp 10 D (opB D j) = lower a (bar p) := by
    refine ⟨p,hp,he,?_,?_⟩
    · simpa only [he,src,Bool.false_eq_true,ite_false] using hfull p hp
    · have hbe := hbar p
      rw [he] at hbe
      simpa only [hbe,sem_bar,Bool.not_false,src,ite_true] using hfull (bar p) (hnonempty p hp)
  by_cases ha : (supp 10 D (opA D j)).Nonempty
  · obtain ⟨p,hp,he⟩ := recover (j,false) hj ht (by simpa [src] using ha)
    exact Or.inl (build p hp he)
  · by_cases hb : (supp 10 D (opB D j)).Nonempty
    · obtain ⟨q,hq,he⟩ := recover (j,true) hj ht (by simpa [src] using hb)
      have hbe : f (bar q) = (j,false) := by simpa [he,sem_bar] using hbar q
      exact Or.inl (build (bar q) (hnonempty q hq) hbe)
    · exact Or.inr ⟨Finset.not_nonempty_iff_eq_empty.mp ha,Finset.not_nonempty_iff_eq_empty.mp hb⟩

end PEqualNP.Outside.L_meta_2590_aux.I2Census

namespace PEqualNP.Outside.L_meta_2590_aux

namespace S45.CausalBarrier

abbrev Wire := Finset (Fin 10) × Bool

def Safe (T : Finset (Fin 10)) (w : Wire) : Prop :=
  w.2 = true → (w.1 ∩ T).Nonempty

def Join (a b : Wire) : Wire := (a.1 ∪ b.1, a.2 || b.2)

def Meet (a b : Wire) : Wire := (a.1 ∩ b.1, a.2 && b.2)

def Separates (T A B : Finset (Fin 10)) : Prop :=
  ¬ ((A ∩ T).Nonempty ∧ (B ∩ T).Nonempty)

lemma safe_join {T : Finset (Fin 10)} {a b : Wire}
    (ha : Safe T a) (hb : Safe T b) : Safe T (Join a b) := by
  intro h
  change a.2 || b.2 = true at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · rcases ha h with ⟨v, hv⟩
    refine ⟨v, ?_⟩
    simpa only [Join, Finset.mem_inter, Finset.mem_union] using
      And.intro (Or.inl (Finset.mem_inter.mp hv).1) (Finset.mem_inter.mp hv).2
  · rcases hb h with ⟨v, hv⟩
    refine ⟨v, ?_⟩
    simpa only [Join, Finset.mem_inter, Finset.mem_union] using
      And.intro (Or.inr (Finset.mem_inter.mp hv).1) (Finset.mem_inter.mp hv).2

lemma safe_meet {T : Finset (Fin 10)} {a b : Wire}
    (ha : Safe T a) (hb : Safe T b) (hs : Separates T a.1 b.1) :
    Safe T (Meet a b) := by
  intro h
  change a.2 && b.2 = true at h
  rcases Bool.and_eq_true_iff.mp h with ⟨ha', hb'⟩
  exact False.elim (hs ⟨ha ha', hb hb'⟩)

lemma safe_zero_false {T : Finset (Fin 10)} {w : Wire}
    (h : Safe T w) (hz : w.1 = ∅) : w.2 = false := by
  cases hv : w.2
  · rfl
  · have hn := h hv
    simp [hz] at hn

def OtherSides : List (Finset (Fin 10) × Finset (Fin 10)) :=
  [({0}, {1, 4, 5}), ({1}, {6}), ({2}, {1, 3, 7}), ({3}, {4, 8}), ({7}, {5, 9}), (∅, ∅)]

def DirtyEdges : List (Finset (Fin 10)) :=
  [{4, 9}, {5, 8}, {6, 8}, {6, 9}]

def UniversalEdge (v : Fin 10) : Finset (Fin 10) :=
  match v.val with
  | 0 => {6, 8}
  | 1 => {4, 9}
  | 2 => {4, 9}
  | 3 => {6, 9}
  | 4 => {4, 9}
  | 5 => {5, 8}
  | 6 => {6, 8}
  | 7 => {6, 8}
  | 8 => {5, 8}
  | _ => {4, 9}

def UniversalBarrier (v : Fin 10) : Finset (Fin 10) := insert v (UniversalEdge v)

lemma universal_edge_valid : ∀ v : Fin 10, UniversalEdge v ∈ DirtyEdges := by decide

lemma all_vertices_separation :
    ∀ (v : Fin 10), ∀ AB ∈ OtherSides,
      Separates (UniversalBarrier v) AB.1 AB.2 ∧
      Separates (UniversalBarrier v) AB.2 AB.1 := by
  intro v
  simp [OtherSides, Separates]
  revert v
  decide

end S45.CausalBarrier

namespace S45.ResourceExclusion

open CausalBarrier

abbrev Resource := Finset (Fin 10) × (Finset (Fin 10) → Bool)

def CrossPairs : List (Finset (Fin 10)) :=
  [{4, 8}, {4, 9}, {5, 8}, {5, 9}, {6, 8}, {6, 9}]

def RSafe (E T : Finset (Fin 10)) (w : Resource) : Prop :=
  w.2 E = true → (w.1 ∩ T).Nonempty

def Ordinary (w : Resource) : Prop := ∀ E ∈ CrossPairs, RSafe E E w

def AllOrdinary (p : Multiset Resource) : Prop := ∀ w ∈ p, Ordinary w

def RJoin (a b : Resource) : Resource :=
  (a.1 ∪ b.1, fun E => a.2 E || b.2 E)

def RMeet (a b : Resource) : Resource :=
  (a.1 ∩ b.1, fun E => a.2 E && b.2 E)

def AllowedSides (a b : Resource) : Prop :=
  (a.1, b.1) ∈ OtherSides ∨ (b.1, a.1) ∈ OtherSides

def Keep (w : Resource) : Multiset Resource :=
  if w.1 = ∅ then 0 else {w}

def Next (a b c : Resource) (rest : Multiset Resource) : Multiset Resource :=
  c ::ₘ (Keep a + Keep b + rest)

def ResourceStep (p q : Multiset Resource) : Prop :=
  (∃ a b c rest, p = a ::ₘ b ::ₘ rest ∧ q = Next a b c rest ∧
    (c = RJoin a b ∨ (AllowedSides a b ∧ c = RMeet a b))) ∨
  (∃ w rest, w.1 ≠ ∅ ∧ p = w ::ₘ rest ∧ q = w ::ₘ w ::ₘ rest) ∨
  (∃ w rest, p = w ::ₘ rest ∧ q = rest)

def Blocked (p : Multiset Resource) : Prop :=
  ∃ E ∈ DirtyEdges, ∃ T : Finset (Fin 10),
    (∀ AB ∈ OtherSides, Separates T AB.1 AB.2 ∧ Separates T AB.2 AB.1) ∧
    ∀ w ∈ p, RSafe E T w

def Exceptional (p : Multiset Resource) : Prop :=
  ∃ d rest, p = d ::ₘ rest ∧ d.1 = ∅ ∧
    (∀ E ∈ CrossPairs, d.2 E = true) ∧ AllOrdinary rest

def Invariant (p : Multiset Resource) : Prop := Blocked p ∨ Exceptional p

def Target (w : Resource) : Prop :=
  w.1 = ∅ ∧ (∀ E ∈ DirtyEdges, w.2 E = true) ∧ w.2 {4, 8} = false

lemma rsafe_join {E T : Finset (Fin 10)} {a b : Resource}
    (ha : RSafe E T a) (hb : RSafe E T b) : RSafe E T (RJoin a b) := by
  exact safe_join (a := (a.1, a.2 E)) (b := (b.1, b.2 E)) ha hb

lemma rsafe_meet {E T : Finset (Fin 10)} {a b : Resource}
    (ha : RSafe E T a) (hb : RSafe E T b) (hs : Separates T a.1 b.1) :
    RSafe E T (RMeet a b) := by
  exact safe_meet (a := (a.1, a.2 E)) (b := (b.1, b.2 E)) ha hb hs

lemma rsafe_zero_false {E T : Finset (Fin 10)} {w : Resource}
    (h : RSafe E T w) (hz : w.1 = ∅) : w.2 E = false :=
  safe_zero_false (w := (w.1, w.2 E)) h hz

lemma cross_separation :
    ∀ E ∈ CrossPairs, ∀ AB ∈ OtherSides,
      Separates E AB.1 AB.2 ∧ Separates E AB.2 AB.1 := by
  simp [CrossPairs, OtherSides, Separates]

lemma dirty_mem_cross : ∀ E ∈ DirtyEdges, E ∈ CrossPairs := by
  simp [DirtyEdges, CrossPairs]

lemma ordinary_join {a b : Resource} (ha : Ordinary a) (hb : Ordinary b) :
    Ordinary (RJoin a b) := by
  intro E hE
  exact rsafe_join (ha E hE) (hb E hE)

lemma ordinary_meet {a b : Resource} (ha : Ordinary a) (hb : Ordinary b)
    (hs : AllowedSides a b) : Ordinary (RMeet a b) := by
  intro E hE
  apply rsafe_meet (ha E hE) (hb E hE)
  rcases hs with hs | hs
  · exact (cross_separation E hE _ hs).1
  · exact (cross_separation E hE _ hs).2

lemma keep_mem {a w : Resource} (h : w ∈ Keep a) : w = a := by
  classical
  by_cases hz : a.1 = ∅
  · simp [Keep, hz] at h
  · simpa [Keep, hz] using h

lemma allOrdinary_next {a b c : Resource} {rest : Multiset Resource}
    (ha : Ordinary a) (hb : Ordinary b) (hc : Ordinary c) (hr : AllOrdinary rest) :
    AllOrdinary (Next a b c rest) := by
  intro w hw
  simp only [Next, Multiset.mem_cons, Multiset.mem_add] at hw
  rcases hw with rfl | (hw | hw) | hw
  · exact hc
  · exact (keep_mem hw) ▸ ha
  · exact (keep_mem hw) ▸ hb
  · exact hr w hw

lemma allOrdinary_blocked {p : Multiset Resource} (hp : AllOrdinary p) : Blocked p := by
  refine ⟨{4, 9}, by simp [DirtyEdges], {4, 9}, ?_, ?_⟩
  · exact cross_separation _ (by simp [CrossPairs])
  · intro w hw
    exact hp w hw _ (by simp [CrossPairs])

lemma blocked_no_target {p : Multiset Resource} (hp : Blocked p)
    {w : Resource} (hw : w ∈ p) : ¬ Target w := by
  obtain ⟨E, hE, T, _, hs⟩ := hp
  rintro ⟨hz, ht, _⟩
  have hf := rsafe_zero_false (hs w hw) hz
  rw [ht E hE] at hf
  contradiction

lemma exceptional_no_target {p : Multiset Resource} (hp : Exceptional p)
    {w : Resource} (hw : w ∈ p) : ¬ Target w := by
  obtain ⟨d, rest, rfl, hd, hdt, hr⟩ := hp
  rcases Multiset.mem_cons.mp hw with rfl | hw
  · rintro ⟨_, _, hf⟩
    have ht := hdt {4, 8} (by simp [CrossPairs])
    rw [hf] at ht
    contradiction
  · exact blocked_no_target (allOrdinary_blocked hr) hw

lemma invariant_no_target {p : Multiset Resource} (hp : Invariant p)
    {w : Resource} (hw : w ∈ p) : ¬ Target w := by
  rcases hp with hp | hp
  · exact blocked_no_target hp hw
  · exact exceptional_no_target hp hw


lemma all_safe_next {E T : Finset (Fin 10)} {a b c : Resource}
    {rest : Multiset Resource}
    (ha : RSafe E T a) (hb : RSafe E T b) (hc : RSafe E T c)
    (hr : ∀ w ∈ rest, RSafe E T w) :
    ∀ w ∈ Next a b c rest, RSafe E T w := by
  intro w hw
  simp only [Next, Multiset.mem_cons, Multiset.mem_add] at hw
  rcases hw with rfl | (hw | hw) | hw
  · exact hc
  · exact (keep_mem hw) ▸ ha
  · exact (keep_mem hw) ▸ hb
  · exact hr w hw

lemma blocked_step {p q : Multiset Resource} (hp : Blocked p)
    (hstep : ResourceStep p q) : Blocked q := by
  obtain ⟨E, hE, T, hT, hs⟩ := hp
  refine ⟨E, hE, T, hT, ?_⟩
  rcases hstep with ⟨a, b, c, rest, rfl, rfl, hc⟩ | ⟨w, rest, _, rfl, rfl⟩ | ⟨w, rest, rfl, rfl⟩
  · have ha := hs a (by simp)
    have hb := hs b (by simp)
    have hr : ∀ w ∈ rest, RSafe E T w := fun w hw => hs w (by simp [hw])
    apply all_safe_next ha hb ?_ hr
    rcases hc with rfl | ⟨hside, rfl⟩
    · exact rsafe_join ha hb
    · apply rsafe_meet ha hb
      rcases hside with hside | hside
      · exact (hT _ hside).1
      · exact (hT _ hside).2
  · intro a ha
    simp only [Multiset.mem_cons, or_self_left] at ha
    exact hs a (Multiset.mem_cons.mpr ha)
  · intro a ha
    exact hs a (by simp [ha])

lemma ordinary_carrier_blocked {c : Resource} {rest : Multiset Resource}
    (hc : c.1.Nonempty) (hr : AllOrdinary rest) : Blocked (c ::ₘ rest) := by
  obtain ⟨v, hv⟩ := hc
  refine ⟨UniversalEdge v, universal_edge_valid v, UniversalBarrier v,
    all_vertices_separation v, ?_⟩
  intro w hw
  rcases Multiset.mem_cons.mp hw with rfl | hw
  · intro _
    exact ⟨v, Finset.mem_inter.mpr ⟨hv, Finset.mem_insert_self _ _⟩⟩
  · intro ht
    obtain ⟨u, hu⟩ := hr w hw _ (dirty_mem_cross _ (universal_edge_valid v)) ht
    obtain ⟨hus, huE⟩ := Finset.mem_inter.mp hu
    exact ⟨u, Finset.mem_inter.mpr ⟨hus, Finset.mem_insert_of_mem huE⟩⟩

lemma keep_ordinary {w : Resource} (h : Ordinary w) : AllOrdinary (Keep w) := by
  intro a ha
  exact (keep_mem ha) ▸ h

lemma allOrdinary_add {p q : Multiset Resource}
    (hp : AllOrdinary p) (hq : AllOrdinary q) : AllOrdinary (p + q) := by
  intro w hw
  rcases Multiset.mem_add.mp hw with hw | hw
  · exact hp w hw
  · exact hq w hw

lemma allOrdinary_cons {w : Resource} {p : Multiset Resource}
    (hw : Ordinary w) (hp : AllOrdinary p) : AllOrdinary (w ::ₘ p) := by
  intro a ha
  rcases Multiset.mem_cons.mp ha with rfl | ha
  · exact hw
  · exact hp a ha

lemma zero_side_of_allowed {a b : Resource} (ha : a.1 = ∅) (hs : AllowedSides a b) :
    b.1 = ∅ := by
  have hzero : ∀ AB ∈ OtherSides,
      (AB.1 = ∅ → AB.2 = ∅) ∧ (AB.2 = ∅ → AB.1 = ∅) := by
    simp [OtherSides]
  rcases hs with hs | hs
  · exact (hzero _ hs).1 ha
  · exact (hzero _ hs).2 ha

lemma exceptional_left_step {d b c : Resource} {rest : Multiset Resource}
    (hd : d.1 = ∅) (hdt : ∀ E ∈ CrossPairs, d.2 E = true)
    (hb : Ordinary b) (hr : AllOrdinary rest)
    (hc : c = RJoin d b ∨ (AllowedSides d b ∧ c = RMeet d b)) :
    Invariant (Next d b c rest) := by
  classical
  rcases hc with rfl | ⟨hs, rfl⟩
  · by_cases hbs : b.1 = ∅
    · right
      refine ⟨RJoin d b, rest, ?_, ?_, ?_, hr⟩
      · simp [Next, Keep, hd, hbs]
      · simp [RJoin, hd, hbs]
      · intro E hE
        simp [RJoin, hdt E hE]
    · left
      have hbp : (RJoin d b).1.Nonempty := by
        simpa [RJoin, hd] using Finset.nonempty_iff_ne_empty.mpr hbs
      have hpool : AllOrdinary (Keep d + Keep b + rest) := by
        simpa [Keep, hd, hbs] using allOrdinary_cons hb hr
      exact ordinary_carrier_blocked hbp hpool
  · left
    have hbs := zero_side_of_allowed hd hs
    have hc : Ordinary (RMeet d b) := by
      intro E hE ht
      have hbf := rsafe_zero_false (hb E hE) hbs
      simp [RMeet, hbf] at ht
    apply allOrdinary_blocked
    simpa [Next, Keep, hd, hbs] using allOrdinary_cons hc hr


lemma next_swap (a b c : Resource) (rest : Multiset Resource) :
    Next a b c rest = Next b a c rest := by
  simp only [Next, add_comm (Keep a) (Keep b)]

lemma rjoin_swap (a b : Resource) : RJoin a b = RJoin b a := by
  apply Prod.ext
  · exact Finset.union_comm _ _
  · funext E
    exact Bool.or_comm _ _

lemma rmeet_swap (a b : Resource) : RMeet a b = RMeet b a := by
  apply Prod.ext
  · exact Finset.inter_comm _ _
  · funext E
    exact Bool.and_comm _ _

lemma ordinary_result {a b c : Resource} (ha : Ordinary a) (hb : Ordinary b)
    (hc : c = RJoin a b ∨ (AllowedSides a b ∧ c = RMeet a b)) : Ordinary c := by
  rcases hc with rfl | ⟨hs, rfl⟩
  · exact ordinary_join ha hb
  · exact ordinary_meet ha hb hs

lemma exceptional_step {p q : Multiset Resource} (hp : Exceptional p)
    (hstep : ResourceStep p q) : Invariant q := by
  classical
  obtain ⟨d, r0, hpd, hd, hdt, hr0⟩ := hp
  rcases hstep with ⟨a, b, c, rest, hpab, rfl, hc⟩ |
    ⟨w, rest, hws, hpw, rfl⟩ | ⟨w, rest, hpw, hqr⟩
  · have heq : d ::ₘ r0 = a ::ₘ b ::ₘ rest := hpd.symm.trans hpab
    by_cases had : a = d
    · subst a
      have hrEq := (Multiset.cons_inj_right d).mp heq
      rw [hrEq] at hr0
      exact exceptional_left_step hd hdt (hr0 b (by simp))
        (fun w hw => hr0 w (by simp [hw])) hc
    · by_cases hbd : b = d
      · subst b
        rw [Multiset.cons_swap a d] at heq
        have hrEq := (Multiset.cons_inj_right d).mp heq
        rw [hrEq] at hr0
        rw [next_swap]
        apply exceptional_left_step hd hdt (hr0 a (by simp))
          (fun w hw => hr0 w (by simp [hw]))
        rcases hc with hc | ⟨hs, hc⟩
        · left
          exact hc.trans (rjoin_swap _ _)
        · right
          exact ⟨Or.symm hs, hc.trans (rmeet_swap _ _)⟩
      · have hdm : d ∈ a ::ₘ b ::ₘ rest := heq ▸ (Multiset.mem_cons_self d r0)
        have hdr : d ∈ rest := by
          simpa [Ne.symm had, Ne.symm hbd] using hdm
        obtain ⟨r, rfl⟩ := Multiset.exists_cons_of_mem hdr
        rw [Multiset.cons_swap b d, Multiset.cons_swap a d] at heq
        have hrEq := (Multiset.cons_inj_right d).mp heq
        rw [hrEq] at hr0
        have ha : Ordinary a := hr0 a (by simp)
        have hb : Ordinary b := hr0 b (by simp)
        have hr : AllOrdinary r := fun w hw => hr0 w (by simp [hw])
        right
        refine ⟨d, Next a b c r, ?_, hd, hdt,
          allOrdinary_next ha hb (ordinary_result ha hb hc) hr⟩
        simp only [Next, Multiset.add_cons]
        exact Multiset.cons_swap _ _ _
  · have heq : d ::ₘ r0 = w ::ₘ rest := hpd.symm.trans hpw
    have hdw : d ≠ w := by
      intro h
      subst w
      exact hws hd
    have hdm : d ∈ w ::ₘ rest := heq ▸ (Multiset.mem_cons_self d r0)
    have hdr : d ∈ rest := by simpa [hdw] using hdm
    obtain ⟨r, rfl⟩ := Multiset.exists_cons_of_mem hdr
    rw [Multiset.cons_swap w d] at heq
    have hrEq := (Multiset.cons_inj_right d).mp heq
    rw [hrEq] at hr0
    right
    refine ⟨d, w ::ₘ w ::ₘ r, ?_, hd, hdt, ?_⟩
    · rw [Multiset.cons_swap w d, Multiset.cons_swap w d]
    · exact allOrdinary_cons (hr0 w (by simp)) hr0
  · rw [hqr]
    have heq : d ::ₘ r0 = w ::ₘ rest := hpd.symm.trans hpw
    by_cases hdw : d = w
    · subst w
      have hrEq := (Multiset.cons_inj_right d).mp heq
      rw [hrEq] at hr0
      exact Or.inl (allOrdinary_blocked hr0)
    · have hdm : d ∈ w ::ₘ rest := heq ▸ (Multiset.mem_cons_self d r0)
      have hdr : d ∈ rest := by simpa [hdw] using hdm
      obtain ⟨r, rfl⟩ := Multiset.exists_cons_of_mem hdr
      rw [Multiset.cons_swap w d] at heq
      have hrEq := (Multiset.cons_inj_right d).mp heq
      rw [hrEq] at hr0
      exact Or.inr ⟨d, r, rfl, hd, hdt, fun a ha => hr0 a (by simp [ha])⟩

lemma invariant_step {p q : Multiset Resource} (hp : Invariant p)
    (hstep : ResourceStep p q) : Invariant q := by
  rcases hp with hp | hp
  · exact Or.inl (blocked_step hp hstep)
  · exact exceptional_step hp hstep

end S45.ResourceExclusion

namespace S45.IndexSchedule

open ResourceExclusion

def Pool (W : ℕ → Resource) (ids : Finset ℕ) : Multiset Resource := ids.val.map W

def DropZero (W : ℕ → Resource) (i : ℕ) (ids : Finset ℕ) : Finset ℕ :=
  if (W i).1 = ∅ then ids.erase i else ids

def NextIds (W : ℕ → Resource) (a b out : ℕ) (ids : Finset ℕ) : Finset ℕ :=
  insert out (DropZero W b (DropZero W a ids))

def Available (W : ℕ → Resource) (start : ℕ) (A B : ℕ → ℕ) : ℕ → Finset ℕ
  | 0 => Finset.range start
  | t + 1 => NextIds W (A (start + t)) (B (start + t)) (start + t)
      (Available W start A B t)

lemma drop_subset (W : ℕ → Resource) (i : ℕ) (ids : Finset ℕ) :
    DropZero W i ids ⊆ ids := by
  unfold DropZero
  split
  · exact Finset.erase_subset _ _
  · exact Finset.Subset.refl _

lemma mem_drop {W : ℕ → Resource} {i x : ℕ} {ids : Finset ℕ}
    (hx : x ∈ ids) (hkeep : (W x).1 ≠ ∅ ∨ x ≠ i) : x ∈ DropZero W i ids := by
  unfold DropZero
  split_ifs with hi
  · apply Finset.mem_erase.mpr
    refine ⟨?_, hx⟩
    rcases hkeep with hkeep | hkeep
    · intro hxi
      subst x
      exact hkeep hi
    · exact hkeep
  · exact hx

lemma available_bounded (W : ℕ → Resource) (start : ℕ) (A B : ℕ → ℕ)
    (t : ℕ) : ∀ x ∈ Available W start A B t, x < start + t := by
  induction t with
  | zero => simp [Available]
  | succ t ih =>
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · omega
      · have hx' := drop_subset W _ _ (drop_subset W _ _ hx)
        have hb := ih x hx'
        omega

lemma available_complete (W : ℕ → Resource) (start : ℕ) (A B : ℕ → ℕ)
    (t : ℕ) : ∀ x, x < start + t →
      ((W x).1 ≠ ∅ ∨ ∀ j < t, A (start + j) ≠ x ∧ B (start + j) ≠ x) →
      x ∈ Available W start A B t := by
  induction t with
  | zero => simp [Available]
  | succ t ih =>
      intro x hbound hunused
      by_cases hlast : x = start + t
      · subst x
        exact Finset.mem_insert_self _ _
      · have hold : x < start + t := by omega
        have hprev : (W x).1 ≠ ∅ ∨ ∀ j < t,
            A (start + j) ≠ x ∧ B (start + j) ≠ x := by
          rcases hunused with hp | hu
          · exact Or.inl hp
          · exact Or.inr (fun j hj => hu j (by omega))
        have hmem := ih x hold hprev
        apply Finset.mem_insert_of_mem
        apply mem_drop
        · apply mem_drop hmem
          rcases hunused with hp | hu
          · exact Or.inl hp
          · exact Or.inr (Ne.symm (hu t (by omega)).1)
        · rcases hunused with hp | hu
          · exact Or.inl hp
          · exact Or.inr (Ne.symm (hu t (by omega)).2)

def Reads (A B : ℕ → ℕ) (i x : ℕ) : Prop := A i = x ∨ B i = x

def LinearUpTo (W : ℕ → Resource) (start : ℕ) (A B : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ i < n, ∀ j < n, ∀ x, (W x).1 = ∅ →
    Reads A B (start + i) x → Reads A B (start + j) x → i = j

lemma source_available {W : ℕ → Resource} {start n t x : ℕ} {A B : ℕ → ℕ}
    (hlin : LinearUpTo W start A B n) (ht : t < n)
    (hx : x < start + t) (hr : Reads A B (start + t) x) :
    x ∈ Available W start A B t := by
  apply available_complete W start A B t x hx
  by_cases hp : (W x).1 = ∅
  · right
    intro j hj
    constructor
    · intro hja
      have heq := hlin t ht j (by omega) x hp hr (Or.inl hja)
      omega
    · intro hjb
      have heq := hlin t ht j (by omega) x hp hr (Or.inr hjb)
      omega
  · exact Or.inl hp

lemma pool_insert {W : ℕ → Resource} {ids : Finset ℕ} {i : ℕ} (hi : i ∉ ids) :
    Pool W (insert i ids) = W i ::ₘ Pool W ids := by
  simp only [Pool, Finset.insert_val_of_notMem hi, Multiset.map_cons]

lemma pool_erase_decomp {W : ℕ → Resource} {ids : Finset ℕ} {i : ℕ} (hi : i ∈ ids) :
    Pool W ids = W i ::ₘ Pool W (ids.erase i) := by
  calc
    Pool W ids = Pool W (insert i (ids.erase i)) := by rw [Finset.insert_erase hi]
    _ = W i ::ₘ Pool W (ids.erase i) := pool_insert (Finset.notMem_erase _ _)

lemma pool_two_decomp {W : ℕ → Resource} {ids : Finset ℕ} {a b : ℕ}
    (ha : a ∈ ids) (hb : b ∈ ids) (hab : a ≠ b) :
    Pool W ids = W a ::ₘ W b ::ₘ Pool W ((ids.erase a).erase b) := by
  rw [pool_erase_decomp ha]
  rw [pool_erase_decomp (Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩)]

lemma pool_drop_two {W : ℕ → Resource} {ids : Finset ℕ} {a b : ℕ}
    (ha : a ∈ ids) (hb : b ∈ ids) (hab : a ≠ b) :
    Pool W (DropZero W b (DropZero W a ids)) =
      Keep (W a) + Keep (W b) + Pool W ((ids.erase a).erase b) := by
  classical
  by_cases hza : (W a).1 = ∅ <;> by_cases hzb : (W b).1 = ∅
  · simp [DropZero, Keep, hza, hzb]
  · simp only [DropZero, Keep, hza, hzb, ite_true, ite_false, zero_add]
    exact pool_erase_decomp (Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩)
  · simp only [DropZero, Keep, hza, hzb, ite_true, ite_false, add_zero]
    rw [Finset.erase_right_comm]
    exact pool_erase_decomp (Finset.mem_erase.mpr ⟨hab, ha⟩)
  · simp only [DropZero, Keep, hza, hzb, ite_false]
    simpa using pool_two_decomp ha hb hab

lemma index_resource_step {W : ℕ → Resource} {ids : Finset ℕ} {a b out : ℕ}
    (ha : a ∈ ids) (hb : b ∈ ids) (hab : a ≠ b) (hout : out ∉ ids)
    (hg : W out = RJoin (W a) (W b) ∨
      (AllowedSides (W a) (W b) ∧ W out = RMeet (W a) (W b))) :
    ResourceStep (Pool W ids) (Pool W (NextIds W a b out ids)) := by
  left
  refine ⟨W a, W b, W out, Pool W ((ids.erase a).erase b),
    pool_two_decomp ha hb hab, ?_, hg⟩
  have hfresh : out ∉ DropZero W b (DropZero W a ids) := by
    intro h
    exact hout (drop_subset W _ _ (drop_subset W _ _ h))
  rw [NextIds, pool_insert hfresh, pool_drop_two ha hb hab]
  rfl


def ValidUpTo (start : ℕ) (A B : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ t < n, A (start + t) < start + t ∧ B (start + t) < start + t ∧
    A (start + t) ≠ B (start + t)

def CanonicalUpTo (W : ℕ → Resource) (start : ℕ) (A B : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ t < n,
    W (start + t) = RJoin (W (A (start + t))) (W (B (start + t))) ∨
    (AllowedSides (W (A (start + t))) (W (B (start + t))) ∧
      W (start + t) = RMeet (W (A (start + t))) (W (B (start + t))))

lemma available_step {W : ℕ → Resource} {start n t : ℕ} {A B : ℕ → ℕ}
    (hv : ValidUpTo start A B n) (hl : LinearUpTo W start A B n)
    (hc : CanonicalUpTo W start A B n) (ht : t < n) :
    ResourceStep (Pool W (Available W start A B t))
      (Pool W (Available W start A B (t + 1))) := by
  obtain ⟨ha, hb, hab⟩ := hv t ht
  have haa := source_available hl ht ha (Or.inl rfl)
  have hba := source_available hl ht hb (Or.inr rfl)
  apply index_resource_step haa hba hab ?_ (hc t ht)
  intro h
  have := available_bounded W start A B t _ h
  omega

lemma program_invariant {W : ℕ → Resource} {start n : ℕ} {A B : ℕ → ℕ}
    (hp : Invariant (Pool W (Finset.range start)))
    (hv : ValidUpTo start A B n) (hl : LinearUpTo W start A B n)
    (hc : CanonicalUpTo W start A B n) :
    ∀ t ≤ n, Invariant (Pool W (Available W start A B t)) := by
  intro t
  induction t with
  | zero => intro _; exact hp
  | succ t ih =>
      intro ht
      exact invariant_step (ih (by omega)) (available_step hv hl hc (by omega))

lemma pool_mem {W : ℕ → Resource} {ids : Finset ℕ} {i : ℕ} (hi : i ∈ ids) :
    W i ∈ Pool W ids := by
  exact Multiset.mem_map.mpr ⟨i, hi, rfl⟩

lemma canonical_program_exclusion {W : ℕ → Resource} {start n : ℕ} {A B : ℕ → ℕ}
    (hp : Invariant (Pool W (Finset.range start)))
    (hv : ValidUpTo start A B n) (hl : LinearUpTo W start A B n)
    (hc : CanonicalUpTo W start A B n) :
    ∀ t < n, ¬ Target (W (start + t)) := by
  intro t ht
  have hinv := program_invariant hp hv hl hc (t + 1) (by omega)
  apply invariant_no_target hinv
  apply pool_mem
  exact Finset.mem_insert_self _ _

lemma initial_exceptional {W : ℕ → Resource} {start d : ℕ}
    (hd : d < start) (hz : (W d).1 = ∅)
    (ht : ∀ E ∈ CrossPairs, (W d).2 E = true)
    (ho : ∀ i < start, i ≠ d → Ordinary (W i)) :
    Invariant (Pool W (Finset.range start)) := by
  right
  refine ⟨W d, Pool W ((Finset.range start).erase d),
    pool_erase_decomp (Finset.mem_range.mpr hd), hz, ht, ?_⟩
  intro w hw
  obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hw
  have hi' : i ∈ (Finset.range start).erase d := hi
  obtain ⟨hid, hir⟩ := Finset.mem_erase.mp hi'
  exact ho i (Finset.mem_range.mp hir) hid

lemma program_any_wire_exclusion {W : ℕ → Resource} {start n : ℕ} {A B : ℕ → ℕ}
    (hp : Invariant (Pool W (Finset.range start)))
    (hv : ValidUpTo start A B n) (hl : LinearUpTo W start A B n)
    (hc : CanonicalUpTo W start A B n) :
    ∀ i < start + n, ¬ Target (W i) := by
  intro i hi
  by_cases hold : i < start
  · exact invariant_no_target hp (pool_mem (Finset.mem_range.mpr hold))
  · have ht : i - start < n := by omega
    have heq : start + (i - start) = i := by omega
    simpa only [heq] using canonical_program_exclusion hp hv hl hc (i - start) ht

lemma ordinary_prefix {W : ℕ → Resource} {start n : ℕ} {A B : ℕ → ℕ}
    (hp : ∀ i < start, Ordinary (W i))
    (hv : ValidUpTo start A B n) (hc : CanonicalUpTo W start A B n) :
    ∀ i < start + n, Ordinary (W i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
      intro hi
      by_cases hold : i < start
      · exact hp i hold
      · have ht : i - start < n := by omega
        have heq : start + (i - start) = i := by omega
        obtain ⟨ha, hb, _⟩ := hv (i - start) ht
        rw [heq] at ha hb
        have hca := hc (i - start) ht
        rw [heq] at hca
        exact ordinary_result (ih _ ha (by omega)) (ih _ hb (by omega)) hca

end S45.IndexSchedule


namespace S45.DAGBridge

open PEqualNP.Outside.L_meta_2590_aux.DagTools
open ResourceExclusion IndexSchedule CausalBarrier

def DagResource (D : Dag) (w : ℕ) : Resource :=
  (supp 10 D w, fun E => val D (fun v => decide (v ∈ E)) w)

lemma zero_reader_unique {D : Dag} (hS : Strict 10 D) (hz : Bzero 10 D = 0)
    {j k w : ℕ} (hj : j < D.length) (hk : k < D.length)
    (he : supp 10 D w = ∅)
    (hrj : opA D j = w ∨ opB D j = w)
    (hrk : opA D k = w ∨ opB D k = w) : j = k := by
  have hw : w < 10 + j := by
    obtain ⟨ha, hb, _⟩ := hS j hj
    rcases hrj with h | h <;> omega
  have hinner : w ∈ (inner 10 D).filter (fun u => ¬ (supp 10 D u).Nonempty) := by
    apply Finset.mem_filter.mpr
    constructor
    · simp only [inner, Finset.mem_range]
      omega
    · simp [he]
  have hsum : fanout D w - 1 ≤ Bzero 10 D := by
    unfold Bzero surplusOn
    exact Finset.single_le_sum (f := fun u => fanout D u - 1) (fun _ _ => Nat.zero_le _) hinner
  have hcard : (readers D w).card ≤ 1 := by
    change fanout D w ≤ 1
    omega
  apply Finset.card_le_one.mp hcard j ?_ k ?_
  · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hrj⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hrk⟩

lemma input_ordinary (D : Dag) {i : ℕ} (hi : i < 10) : Ordinary (DagResource D i) := by
  intro E _ ht
  change val D (fun v => decide (v ∈ E)) i = true at ht
  rw [val_input D _ i hi] at ht
  have hm : (⟨i, hi⟩ : Fin 10) ∈ E := of_decide_eq_true ht
  refine ⟨⟨i, hi⟩, Finset.mem_inter.mpr ⟨?_, hm⟩⟩
  change (⟨i, hi⟩ : Fin 10) ∈ supp 10 D i
  rw [supp_input D ⟨i, hi⟩]
  simp

lemma resource_gate {D : Dag} (hS : Strict 10 D) {j : ℕ} (hj : j < D.length) :
    DagResource D (10 + j) =
      if tag D j = true then RMeet (DagResource D (opA D j)) (DagResource D (opB D j))
      else RJoin (DagResource D (opA D j)) (DagResource D (opB D j)) := by
  cases ht : tag D j
  · simp only [Bool.false_eq_true, ite_false]
    apply Prod.ext
    · exact (supp_gate hS j hj).trans (by simp [ht, RJoin, DagResource])
    · funext E
      exact (val_gate hS (fun v => decide (v ∈ E)) j hj).trans (by simp [ht, gop, RJoin, DagResource])
  · simp only [ite_true]
    apply Prod.ext
    · exact (supp_gate hS j hj).trans (by simp [ht, RMeet, DagResource])
    · funext E
      exact (val_gate hS (fun v => decide (v ∈ E)) j hj).trans (by simp [ht, gop, RMeet, DagResource])

lemma support_hit_true {D : Dag} (hS : Strict 10 D) {w : ℕ} {E : Finset (Fin 10)}
    (hh : (supp 10 D w ∩ E).Nonempty) : (DagResource D w).2 E = true := by
  obtain ⟨v, hv⟩ := hh
  obtain ⟨hvs, hvE⟩ := Finset.mem_inter.mp hv
  apply val_mono hS (single v) (fun u => decide (u ∈ E)) ?_ w (mem_supp.mp hvs)
  intro u hu
  have huv : u = v := by simpa [single] using hu
  subst u
  exact decide_eq_true hvE

def DirtyA : Finset (Fin 10) := {4, 5, 6}

def DirtyB : Finset (Fin 10) := {8, 9}

def DirtySides (D : Dag) (g : ℕ) : Prop :=
  (supp 10 D (opA D g) = DirtyA ∧ supp 10 D (opB D g) = DirtyB) ∨
  (supp 10 D (opA D g) = DirtyB ∧ supp 10 D (opB D g) = DirtyA)

lemma cross_hits : ∀ E ∈ CrossPairs,
    (DirtyA ∩ E).Nonempty ∧ (DirtyB ∩ E).Nonempty := by
  simp [CrossPairs, DirtyA, DirtyB]

lemma dirty_seed {D : Dag} (hS : Strict 10 D) {g : ℕ} (hg : g < D.length)
    (ht : tag D g = true) (hs : DirtySides D g) :
    (DagResource D (10 + g)).1 = ∅ ∧
      ∀ E ∈ CrossPairs, (DagResource D (10 + g)).2 E = true := by
  constructor
  · change supp 10 D (10 + g) = ∅
    rw [supp_gate hS g hg, ht]
    simp only [ite_true]
    rcases hs with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [ha, hb]
      decide
    · rw [ha, hb]
      decide
  · intro E hE
    change val D (fun v => decide (v ∈ E)) (10 + g) = true
    rw [val_gate hS _ g hg, ht]
    change (DagResource D (opA D g)).2 E && (DagResource D (opB D g)).2 E = true
    have hcross := cross_hits E hE
    rcases hs with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [support_hit_true hS (by simpa [ha] using hcross.1),
        support_hit_true hS (by simpa [hb] using hcross.2)]
      rfl
    · rw [support_hit_true hS (by simpa [ha] using hcross.2),
        support_hit_true hS (by simpa [hb] using hcross.1)]
      rfl


def Left (D : Dag) (w : ℕ) : ℕ := opA D (w - 10)

def Right (D : Dag) (w : ℕ) : ℕ := opB D (w - 10)

lemma window_valid {D : Dag} (hS : Strict 10 D) {offset count : ℕ}
    (hbound : offset + count ≤ D.length) :
    ValidUpTo (10 + offset) (Left D) (Right D) count := by
  intro t ht
  have hj : offset + t < D.length := by omega
  have hsub : 10 + offset + t - 10 = offset + t := by omega
  obtain ⟨ha, hb, hab⟩ := hS (offset + t) hj
  simp only [Left, Right, hsub]
  exact ⟨by omega, by omega, hab⟩

lemma window_linear {D : Dag} (hS : Strict 10 D) (hB : Bzero 10 D = 0)
    {offset count : ℕ} (hbound : offset + count ≤ D.length) :
    LinearUpTo (DagResource D) (10 + offset) (Left D) (Right D) count := by
  intro i hi j hj w he hri hrj
  have his : 10 + offset + i - 10 = offset + i := by omega
  have hjs : 10 + offset + j - 10 = offset + j := by omega
  change supp 10 D w = ∅ at he
  simp only [Reads, Left, Right, his] at hri
  simp only [Reads, Left, Right, hjs] at hrj
  have heq := zero_reader_unique hS hB (by omega : offset + i < D.length)
    (by omega : offset + j < D.length) he hri hrj
  omega

lemma window_canonical {D : Dag} (hS : Strict 10 D) {offset count : ℕ}
    (hbound : offset + count ≤ D.length)
    (hsides : ∀ j, offset ≤ j → j < offset + count → tag D j = true →
      AllowedSides (DagResource D (opA D j)) (DagResource D (opB D j))) :
    CanonicalUpTo (DagResource D) (10 + offset) (Left D) (Right D) count := by
  intro t ht
  have hj : offset + t < D.length := by omega
  have hsub : 10 + offset + t - 10 = offset + t := by omega
  have hout : 10 + offset + t = 10 + (offset + t) := by omega
  simp only [Left, Right, hsub]
  rw [hout]
  have hgate := resource_gate hS hj
  cases ht : tag D (offset + t)
  · left
    simpa only [ht, Bool.false_eq_true, ite_false] using hgate
  · right
    exact ⟨hsides _ (by omega) (by omega) ht, by simpa only [ht, ite_true] using hgate⟩

def OtherAndSides (D : Dag) (g : ℕ) : Prop :=
  ∀ j < D.length, j ≠ g → tag D j = true →
    AllowedSides (DagResource D (opA D j)) (DagResource D (opB D j))

lemma before_seed_ordinary {D : Dag} (hS : Strict 10 D) {g : ℕ}
    (hg : g < D.length) (hsides : OtherAndSides D g) :
    ∀ i < 10 + g, Ordinary (DagResource D i) := by
  apply ordinary_prefix (start := 10) (n := g) (A := Left D) (B := Right D)
  · exact fun i hi => input_ordinary D hi
  · exact window_valid (offset := 0) hS (by omega)
  · apply window_canonical (offset := 0) hS (by omega)
    intro j _ hj ht
    exact hsides j (by omega) (by omega) ht

lemma canonical_dag_exclusion {D : Dag} (hS : Strict 10 D) (hB : Bzero 10 D = 0)
    {g : ℕ} (hg : g < D.length) (ht : tag D g = true) (hdirty : DirtySides D g)
    (hsides : OtherAndSides D g) :
    ∀ w < 10 + D.length, ¬ Target (DagResource D w) := by
  obtain ⟨hdz, hdt⟩ := dirty_seed hS hg ht hdirty
  have hbefore := before_seed_ordinary hS hg hsides
  have hinit : Invariant (Pool (DagResource D) (Finset.range (10 + (g + 1)))) := by
    apply initial_exceptional (d := 10 + g) (by omega) hdz hdt
    intro i hi hne
    exact hbefore i (by omega)
  have hcount : g + 1 + (D.length - (g + 1)) ≤ D.length := by omega
  have hvalid := window_valid hS hcount
  have hlinear := window_linear hS hB hcount
  have hcanonical : CanonicalUpTo (DagResource D) (10 + (g + 1)) (Left D) (Right D)
      (D.length - (g + 1)) := by
    apply window_canonical hS hcount
    intro j hlo hhi ht
    exact hsides j (by omega) (by omega) ht
  intro w hw
  exact program_any_wire_exclusion hinit hvalid hlinear hcanonical w (by omega)

end S45.DAGBridge

namespace S45.DAGBridge

open DagTools ResourceExclusion CausalBarrier

lemma target_of_sem_comp {D : Dag} (hc : sem_Comp 10 adj D) :
    Target (DagResource D (outW 10 D)) := by
  refine ⟨sem_supp_out graph_ok hc, ?_, ?_⟩
  · intro E hE
    change val D (fun v => decide (v ∈ E)) (outW 10 D) = true
    apply (hc _).mpr
    have hfinite : ∀ E ∈ DirtyEdges,
        sem_Edge adj (fun v => decide (v ∈ E)) := by
      intro E hE
      simp [DirtyEdges] at hE
      rcases hE with rfl | rfl | rfl | rfl <;> unfold sem_Edge <;> decide
    exact hfinite E hE
  · change val D (fun v => decide (v ∈ ({4, 8} : Finset (Fin 10)))) (outW 10 D) = false
    by_contra hn
    have ht : val D (fun v => decide (v ∈ ({4, 8} : Finset (Fin 10)))) (outW 10 D) = true :=
      by simpa only [Bool.not_eq_false] using hn
    have hbad : ¬ sem_Edge adj (fun v => decide (v ∈ ({4, 8} : Finset (Fin 10)))) := by unfold sem_Edge; decide
    exact hbad ((hc _).mp ht)

lemma petersen_dag_exclusion {D : Dag} (hS : Strict 10 D) (hB : Bzero 10 D = 0)
    {g : ℕ} (hg : g < D.length) (ht : tag D g = true) (hdirty : DirtySides D g)
    (hsides : OtherAndSides D g) (hc : sem_Comp 10 adj D) : False := by
  exact canonical_dag_exclusion hS hB hg ht hdirty hsides (outW 10 D)
    (by unfold outW; omega) (target_of_sem_comp hc)

lemma petersen_dag_exclusion_of_supports {D : Dag}
    (hS : Strict 10 D) (hB : Bzero 10 D = 0) (hc : sem_Comp 10 adj D)
    {g : ℕ} (hg : g < D.length) (ht : tag D g = true)
    (hdirty : (supp 10 D (opA D g) = {4, 5, 6} ∧ supp 10 D (opB D g) = {8, 9}) ∨
      (supp 10 D (opA D g) = {8, 9} ∧ supp 10 D (opB D g) = {4, 5, 6}))
    (hsides : ∀ j < D.length, j ≠ g → tag D j = true →
      (supp 10 D (opA D j), supp 10 D (opB D j)) ∈ OtherSides ∨
      (supp 10 D (opB D j), supp 10 D (opA D j)) ∈ OtherSides) : False := by
  exact petersen_dag_exclusion hS hB hg ht hdirty hsides hc

end S45.DAGBridge

end PEqualNP.Outside.L_meta_2590_aux

namespace PEqualNP.Outside.L_meta_2590_aux.I2Census

open DagTools

def swap37Fn : V → V := ![2,1,0,4,3,7,6,5,9,8]

def swap37 : Equiv.Perm V :=
  ⟨swap37Fn,swap37Fn,by decide +kernel,by decide +kernel⟩

lemma swap37_adj : ∀ u v : V, adj (swap37 u) (swap37 v) ↔ adj u v := by
  decide +kernel

lemma relabel_Bzero {n : ℕ} {D : Dag} (h : StrictLive n D)
    (σ : Equiv.Perm (Fin n)) : Bzero n (relabel σ D) = Bzero n D := by
  classical
  have lenpos := List.length_pos_iff_ne_nil.mpr h.2.2
  have bound : n ≤ n + D.length - 1 := by omega
  have mem_iff (w : ℕ) :
      liftP σ w ∈ (inner n (relabel σ D)).filter (fun u => ¬ (supp n (relabel σ D) u).Nonempty) ↔
      w ∈ (inner n D).filter (fun u => ¬ (supp n D u).Nonempty) := by
    simp only [Finset.mem_filter, inner, Finset.mem_range, relabel_length,
      tr_liftP_lt_iff σ bound, relabel_supp σ h.1, Finset.image_nonempty]
  unfold Bzero surplusOn
  symm
  refine Finset.sum_bij (fun w _ => liftP σ w) (fun w hw => (mem_iff w).mpr hw)
    (fun a _ b _ hab => (tr_liftP_inj σ).mp hab) ?_ ?_
  · intro b hb
    refine ⟨liftP σ⁻¹ b, ?_, tr_liftP_inv' σ b⟩
    apply (mem_iff _).mp
    simpa only [tr_liftP_inv'] using hb
  · intro a ha
    rw [relabel_fanout]

def other37Sides : List (Finset V × Finset V) :=
  [({0},{1,4,5}),({1},{6}),({2},{1,3,7}),({4},{3,9}),({5},{7,8}),(∅,∅)]

lemma swap37_other {A B : Finset V} (h : (A,B) ∈ other37Sides) :
    (A.image swap37, B.image swap37) ∈ S45.CausalBarrier.OtherSides := by
  simp only [other37Sides,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at h
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  all_goals decide +kernel

lemma swap37_dirty :
    ({3,6,7} : Finset V).image swap37 = {4,5,6} ∧
    ({8,9} : Finset V).image swap37 = {8,9} := by decide +kernel

lemma s37_exclusion_of_supports {D : Dag}
    (h : StrictLive 10 D) (hB : Bzero 10 D = 0) (hc : sem_Comp 10 adj D)
    {g : ℕ} (hg : g < D.length) (ht : tag D g = true)
    (hdirty : (supp 10 D (opA D g) = {3,6,7} ∧ supp 10 D (opB D g) = {8,9}) ∨
      (supp 10 D (opA D g) = {8,9} ∧ supp 10 D (opB D g) = {3,6,7}))
    (hsides : ∀ j < D.length, j ≠ g → tag D j = true →
      (supp 10 D (opA D j),supp 10 D (opB D j)) ∈ other37Sides ∨
      (supp 10 D (opB D j),supp 10 D (opA D j)) ∈ other37Sides) : False := by
  let E := relabel swap37 D
  have hE := relabel_strictLive swap37 h
  have hEC := r1_relabel_comp h hc swap37 swap37_adj
  have hEB : Bzero 10 E = 0 := by
    change Bzero 10 (relabel swap37 D) = 0
    rw [relabel_Bzero h,hB]
  have left (j : ℕ) (hj : j < D.length) :
      supp 10 E (opA E j) = (supp 10 D (opA D j)).image swap37 := by
    change supp 10 (relabel swap37 D) (opA (relabel swap37 D) j) = _
    rw [tr_opA swap37 D j hj,relabel_supp swap37 h.1]
  have right (j : ℕ) (hj : j < D.length) :
      supp 10 E (opB E j) = (supp 10 D (opB D j)).image swap37 := by
    change supp 10 (relabel swap37 D) (opB (relabel swap37 D) j) = _
    rw [tr_opB swap37 D j hj,relabel_supp swap37 h.1]
  apply S45.DAGBridge.petersen_dag_exclusion_of_supports hE.1 hEB hEC
    (g := g) (by simpa only [E,relabel_length] using hg)
    (by simpa only [E,tr_tag swap37 D g hg] using ht)
  · rw [left g hg,right g hg]
    rcases hdirty with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · exact Or.inl ⟨by rw [ha,swap37_dirty.1],by rw [hb,swap37_dirty.2]⟩
    · exact Or.inr ⟨by rw [ha,swap37_dirty.2],by rw [hb,swap37_dirty.1]⟩
  · intro j hj hne hjt
    have hjD : j < D.length := by simpa only [E,relabel_length] using hj
    have htD : tag D j = true := by simpa only [E,tr_tag swap37 D j hjD] using hjt
    rw [left j hjD,right j hjD]
    rcases hsides j hjD hne htD with hh | hh
    · exact Or.inl (swap37_other hh)
    · exact Or.inr (swap37_other hh)

end PEqualNP.Outside.L_meta_2590_aux.I2Census

namespace PEqualNP.Outside.L_meta_2590_aux.I2Census

open DagTools

lemma dirty_sides_of_full {D : Dag} (f : P → ℕ × Bool) (d : P)
    (hbar : ∀ p, f (bar p) = sem_bar (f p))
    (A B : Finset V)
    (ha : supp 10 D (src D (f d)) = A)
    (hb : supp 10 D (src D (f (bar d))) = B) :
    (supp 10 D (opA D (f d).1) = A ∧ supp 10 D (opB D (f d).1) = B) ∨
    (supp 10 D (opA D (f d).1) = B ∧ supp 10 D (opB D (f d).1) = A) := by
  rw [hbar d] at hb
  cases he : (f d).2
  · left
    simpa only [src, he, sem_bar, Bool.not_false, Bool.false_eq_true, ite_false, ite_true] using And.intro ha hb
  · right
    simpa only [src, he, sem_bar, Bool.not_true, Bool.false_eq_true, ite_false, ite_true] using And.intro hb ha

lemma other_sides_of_selected {D : Dag} (f : P → ℕ × Bool) (d : P)
    (L : P → Finset V) (other : List (Finset V × Finset V))
    (hbar : ∀ p, f (bar p) = sem_bar (f p))
    (hc : ∀ p, p.val < 12 → p ≠ d → p ≠ bar d →
      (L p, L (bar p)) ∈ other ∨ (L (bar p), L p) ∈ other)
    (he : ((∅ : Finset V), ∅) ∈ other)
    (hsig : ∀ j < D.length, tag D j = true →
      (∃ p, p.val < 12 ∧ f p = (j,false) ∧
        supp 10 D (opA D j) = L p ∧ supp 10 D (opB D j) = L (bar p)) ∨
      (supp 10 D (opA D j) = ∅ ∧ supp 10 D (opB D j) = ∅)) :
    ∀ j < D.length, j ≠ (f d).1 → tag D j = true →
      (supp 10 D (opA D j), supp 10 D (opB D j)) ∈ other ∨
      (supp 10 D (opB D j), supp 10 D (opA D j)) ∈ other := by
  intro j hj hne ht
  rcases hsig j hj ht with ⟨p,hp,hfp,hA,hB⟩ | ⟨hA,hB⟩
  · have hpd : p ≠ d := by
      intro hd
      subst p
      exact hne (congrArg Prod.fst hfp).symm
    have hpbd : p ≠ bar d := by
      intro hd
      subst p
      have hb := congrArg Prod.fst (hbar d)
      have hjf := congrArg Prod.fst hfp
      exact hne (hjf.symm.trans hb)
    simpa only [hA,hB] using hc p hp hpd hpbd
  · exact Or.inl (by simpa only [hA,hB] using he)

set_option maxRecDepth 4096 in
lemma catalog45 : ∀ p : P, p.val < 12 → p ≠ 10 → p ≠ bar 10 →
    (lower45 p, lower45 (bar p)) ∈ S45.CausalBarrier.OtherSides ∨
    (lower45 (bar p), lower45 p) ∈ S45.CausalBarrier.OtherSides := by decide +kernel

lemma s45_exclusion_of_selected {D : Dag}
    (hS : Strict 10 D) (hz : Bzero 10 D = 0) (hc : sem_Comp 10 adj D)
    (f : P → ℕ × Bool) (hbar : ∀ p, f (bar p) = sem_bar (f p))
    (hg : (f 10).1 < D.length) (ht : tag D (f 10).1 = true)
    (hfull : ∀ p, p.val < 12 → supp 10 D (src D (f p)) = lower45 p)
    (hsig : ∀ j < D.length, tag D j = true →
      (∃ p, p.val < 12 ∧ f p = (j,false) ∧
        supp 10 D (opA D j) = lower45 p ∧ supp 10 D (opB D j) = lower45 (bar p)) ∨
      (supp 10 D (opA D j) = ∅ ∧ supp 10 D (opB D j) = ∅)) : False := by
  apply S45.DAGBridge.petersen_dag_exclusion_of_supports hS hz hc hg ht
  · exact dirty_sides_of_full f 10 hbar _ _ (hfull 10 (by decide)) (hfull (bar 10) (by decide))
  · exact other_sides_of_selected f 10 lower45 S45.CausalBarrier.OtherSides hbar catalog45 (by decide) hsig

def other37 : List (Finset V × Finset V) :=
  [({0},{1,4,5}),({1},{6}),({2},{1,3,7}),({4},{3,9}),({5},{7,8}),(∅,∅)]

set_option maxRecDepth 4096 in
lemma catalog37 : ∀ p : P, p.val < 12 → p ≠ 8 → p ≠ bar 8 →
    (lower37 p, lower37 (bar p)) ∈ other37 ∨
    (lower37 (bar p), lower37 p) ∈ other37 := by decide +kernel

lemma s37_sides_of_selected {D : Dag}
    (f : P → ℕ × Bool) (hbar : ∀ p, f (bar p) = sem_bar (f p))
    (hfull : ∀ p, p.val < 12 → supp 10 D (src D (f p)) = lower37 p)
    (hsig : ∀ j < D.length, tag D j = true →
      (∃ p, p.val < 12 ∧ f p = (j,false) ∧
        supp 10 D (opA D j) = lower37 p ∧ supp 10 D (opB D j) = lower37 (bar p)) ∨
      (supp 10 D (opA D j) = ∅ ∧ supp 10 D (opB D j) = ∅)) :
    ((supp 10 D (opA D (f 8).1) = {3,6,7} ∧ supp 10 D (opB D (f 8).1) = {8,9}) ∨
      (supp 10 D (opA D (f 8).1) = {8,9} ∧ supp 10 D (opB D (f 8).1) = {3,6,7})) ∧
    (∀ j < D.length, j ≠ (f 8).1 → tag D j = true →
      (supp 10 D (opA D j), supp 10 D (opB D j)) ∈ other37 ∨
      (supp 10 D (opB D j), supp 10 D (opA D j)) ∈ other37) := by
  exact ⟨dirty_sides_of_full f 8 hbar _ _ (hfull 8 (by decide)) (hfull (bar 8) (by decide)),
    other_sides_of_selected f 8 lower37 other37 hbar catalog37 (by decide) hsig⟩

lemma s37_exclusion_of_selected {D : Dag}
    (h : StrictLive 10 D) (hz : Bzero 10 D = 0) (hc : sem_Comp 10 adj D)
    (f : P → ℕ × Bool) (hbar : ∀ p, f (bar p) = sem_bar (f p))
    (hg : (f 8).1 < D.length) (ht : tag D (f 8).1 = true)
    (hfull : ∀ p, p.val < 12 → supp 10 D (src D (f p)) = lower37 p)
    (hsig : ∀ j < D.length, tag D j = true →
      (∃ p, p.val < 12 ∧ f p = (j,false) ∧
        supp 10 D (opA D j) = lower37 p ∧ supp 10 D (opB D j) = lower37 (bar p)) ∨
      (supp 10 D (opA D j) = ∅ ∧ supp 10 D (opB D j) = ∅)) : False := by
  obtain ⟨hd, hs⟩ := s37_sides_of_selected f hbar hfull hsig
  apply s37_exclusion_of_supports h hz hc hg ht hd
  simpa only [other37, other37Sides] using hs

end PEqualNP.Outside.L_meta_2590_aux.I2Census

namespace PEqualNP.Outside.L_meta_2590_aux.I2Census

open DagTools

lemma bar_lt_twelve : ∀ p : P, p.val < 12 → (bar p).val < 12 := by decide +kernel

lemma exclusion_of_normalized_ports {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 adj D) (hz : Bzero 10 D = 0)
    (b : V → ℕ) (hb : PureBranch 10 D b)
    (S : Finset V) (hS : S ∈ I2ForbiddenPairs.supports)
    (a : List ℕ) (hlen : a.length = 9) (hgrowth : PortCodes.Growth a)
    (hconditions : ∀ i, i ≤ a.length → Conditions S (a.take i))
    (f : P → ℕ × Bool) (hbar : ∀ p, f (bar p) = sem_bar (f p))
    (hinj : ∀ p q, (lower a p).Nonempty → (lower a q).Nonempty → f p = f q → p = q)
    (hselected : ∀ p v, v ∈ lower a p → f p ∈ sem_W 10 D v)
    (hflow : ∀ v, 1 + (({v} : Finset V) ∩ eligSet 10 D).card +
      ((residualUnits 10 D b).filter (fun u => v ∈ supp 10 D u.1)).card ≤ budget S v) : False := by
  obtain ⟨_,hsat,hnonempty,hshape⟩ := classified_geometry S a
    (support_exists_of_mem hS) (admissible_of_growth S a hgrowth hconditions) hlen
  obtain ⟨hm,hfull,hW⟩ := saturated_actual_sources h hc b hb S a f hinj hselected hflow hsat
  have hbar_nonempty (p : P) (hp : (lower a p).Nonempty) : (lower a (bar p)).Nonempty :=
    (hnonempty (bar p)).mpr (bar_lt_twelve p ((hnonempty p).mp hp))
  have hsignature (j : ℕ) (hj : j < D.length) (ht : tag D j = true) :=
    saturated_actual_and_signature h.1 a f hbar hbar_nonempty hm hfull hW hj ht
  have valid (p : P) (hp : p.val < 12) : (f p).1 < D.length ∧ tag D (f p).1 = true := by
    obtain ⟨v,hv⟩ := (hnonempty p).mpr hp
    have he := hselected p v hv
    exact ⟨(sem_mem_W.mp he).1,sem_W_and h.1 he⟩
  rcases hshape with ⟨_,h45⟩ | ⟨_,h37⟩
  · apply s45_exclusion_of_selected h.1 hz hc f hbar
      (valid 10 (by decide)).1 (valid 10 (by decide)).2
    · intro p hp
      exact (hfull p ((hnonempty p).mpr hp)).trans (h45 p)
    · intro j hj ht
      rcases hsignature j hj ht with ⟨p,hp,hfp,hA,hB⟩ | hh
      · exact Or.inl ⟨p,(hnonempty p).mp hp,hfp,hA.trans (h45 p),hB.trans (h45 (bar p))⟩
      · exact Or.inr hh
  · apply s37_exclusion_of_selected h hz hc f hbar
      (valid 8 (by decide)).1 (valid 8 (by decide)).2
    · intro p hp
      exact (hfull p ((hnonempty p).mpr hp)).trans (h37 p)
    · intro j hj ht
      rcases hsignature j hj ht with ⟨p,hp,hfp,hA,hB⟩ | hh
      · exact Or.inl ⟨p,(hnonempty p).mp hp,hfp,hA.trans (h37 p),hB.trans (h37 (bar p))⟩
      · exact Or.inr hh

end PEqualNP.Outside.L_meta_2590_aux.I2Census

namespace PEqualNP.Outside.L_meta_2590_aux

open DagTools I2Census

lemma petersen_single_one_exclusion {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (small : D.length ≤ 19) (two : (ineligSet 10 D).card = 2)
    (h0 : (0 : V) ∈ ineligSet 10 D) (h2 : (2 : V) ∈ ineligSet 10 D)
    (b : V → ℕ) (hb : sem_MinBranch 10 D b)
    (hone : ((residualUnits 10 D b).filter
      (fun u => (1 : V) ∈ supp 10 D u.1)).card ≤ 1) : False := by
  have hbp := sem_minBranch_pure hb
  obtain ⟨u,v,_,hR,hu,hS⟩ := petersen_single_one_residual_decomposition h hc small two h0 h2 b hbp hone
  let S := supp 10 D v.1
  have h1S : (1 : V) ∉ S := by
    have finite : ∀ i : Fin 19, (1 : V) ∉ support i := by decide +kernel
    obtain ⟨i,hi⟩ := support_exists_of_mem hS
    change (1 : V) ∉ supp 10 D v.1
    rw [hi]
    exact finite i
  obtain ⟨hcode,hbudget⟩ := budget_and_shared_code h hc h0 h2 b hbp u v S hR hu rfl h1S
  have hflow := budget_flow_bound h hc h0 h2 b hbp u v S hR hu rfl h1S
  obtain ⟨A,B,e,hA,hB,hAB,he⟩ := actual_free_port_choice h hc small two h0 h2
  obtain ⟨a,f,hlen,hgrowth,hbar,hinj,hselected,hfixed⟩ := normalize_actual_ports A B e hA hB hAB he
  have hconditions (i : ℕ) (_ : i ≤ a.length) : Conditions S (a.take i) := by
    obtain ⟨hi,hs,hf⟩ := map_properties_take a f hinj hselected hfixed i
    exact conditions_of_semantics h hc b hb S (a.take i) v hcode hbudget f hbar hi hs hf
  exact exclusion_of_normalized_ports h hc (two_ineligible_tight h hc small two).2.1
    b hbp S hS a hlen hgrowth hconditions f hbar hinj hselected hflow

lemma petersen_two_ineligible_both_one {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (small : D.length ≤ 19) (two : (ineligSet 10 D).card = 2)
    (h0 : (0 : V) ∈ ineligSet 10 D) (h2 : (2 : V) ∈ ineligSet 10 D)
    (b : V → ℕ) (hb : sem_MinBranch 10 D b) :
    ((residualUnits 10 D b).filter (fun u => (1 : V) ∈ supp 10 D u.1)).card = 2 := by
  have hR := (petersen_two_ineligible_code_caps h hc small two h0 h2 b (sem_minBranch_pure hb)).2.1
  have hle := Finset.card_filter_le (residualUnits 10 D b) (fun u => (1 : V) ∈ supp 10 D u.1)
  have hnot : ¬ ((residualUnits 10 D b).filter (fun u => (1 : V) ∈ supp 10 D u.1)).card ≤ 1 :=
    fun hsmall => petersen_single_one_exclusion h hc small two h0 h2 b hb hsmall
  omega

end PEqualNP.Outside.L_meta_2590_aux
