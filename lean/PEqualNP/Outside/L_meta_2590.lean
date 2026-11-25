import Mathlib.Tactic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Relation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Powerset

namespace PEqualNP.Outside.L_meta_2590_aux

-- Checked helper lemmas; the final gap theorem is not declared.

-- Circuit normalization and wire counting, adapted from L_meta_971.
namespace DagTools


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

lemma sem_one_exit_neighbors (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {x : Fin n} {e : ℕ × Bool}
    (he : exitArcs n D (carrierT n D {x}) = {e}) :
    ∀ y, G x y → y ∈ supp n D (src D (e.1, !e.2)) := by
  intro y hxy
  obtain ⟨j, hj, _, _, hxn, _, s, hxs, _, hys, _⟩ := sem_joint_meeting hG hS hC hxy
  have hje : (j, s) = e := by
    have hm := sem_mem_exit1.mpr ⟨hj, hxs, hxn⟩
    rwa [he, Finset.mem_singleton] at hm
  simpa only [← hje] using hys

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

lemma sem_two_exit_remaining_neighbors (hG : sem_Gr G) (hS : Strict n D)
    (hC : sem_Comp n G D) {x z : Fin n} {e f : ℕ × Bool}
    (hW : exitArcs n D (carrierT n D {x}) ⊆ {e, f})
    (hbar : supp n D (src D (e.1, !e.2)) = {z}) :
    ∀ y, G x y → y ≠ z → y ∈ supp n D (src D (f.1, !f.2)) := by
  intro y hxy hyz
  obtain ⟨j, hj, _, _, hxn, _, s, hxs, _, hys, _⟩ := sem_joint_meeting hG hS hC hxy
  have heither := hW (sem_mem_exit1.mpr ⟨hj, hxs, hxn⟩)
  simp only [Finset.mem_insert, Finset.mem_singleton] at heither
  rcases heither with he | hf
  · have hy : y ∈ supp n D (src D (e.1, !e.2)) := by simpa only [← he] using hys
    rw [hbar, Finset.mem_singleton] at hy
    exact False.elim (hyz hy)
  · simpa only [← hf] using hys

lemma sem_tight_exit_le_two (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (hB : Bplus n D = (eligSet n D).card) (x : Fin n) :
    (exitArcs n D (carrierT n D {x})).card ≤ 2 := by
  obtain ⟨b, hb⟩ := sem_exists_pureBranch hG h.1 hC
  have hs := surplus_carrierT_le h.1 b hb {x}
  have hf := carrier_flow_union h {x} (by rw [sem_supp_out hG hC]; simp)
  have hi : (({x} : Finset (Fin n)) ∩ eligSet n D).card ≤ 1 :=
    (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
  rw [Finset.card_singleton] at hf
  omega

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

lemma sem_two_exit_neighbor_card (hG : sem_Gr G) (hS : Strict n D)
    (hC : sem_Comp n G D) {x z y a : Fin n} {e f : ℕ × Bool}
    (hW : exitArcs n D (carrierT n D {x}) ⊆ {e, f})
    (hbar : supp n D (src D (e.1, !e.2)) = {z})
    (hxy : G x y) (hxa : G x a) (hyz : y ≠ z) (haz : a ≠ z) (hay : a ≠ y) :
    2 ≤ (exitArcs n D (carrierT n D {y})).card := by
  exact sem_nonpure_exit_card hG hS hC
    (sem_two_exit_remaining_slot hG hS hC hW hbar hxy hyz)
    (sem_two_exit_remaining_neighbors hG hS hC hW hbar a hxa haz) hay

end SemCore
def petersenAdj (x y : Fin 10) : Prop :=
  (([50, 69, 138, 276, 521, 385, 770, 548, 104, 208] : List Nat).getD x.val 0).testBit y.val = true

def exposureMask (x y : Fin 10) : Nat :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 104, 20, 36, 80, 208, 276, 548, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 548, 10, 0, 40, 104, 138, 770, 514, 0, 130, 276, 138, 144, 0, 208, 130, 258, 770, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List Nat).getD (10 * x.val + y.val) 0

def exposureSet (x y : Fin 10) : Finset (Fin 10) :=
  Finset.univ.filter (fun a => (exposureMask x y).testBit a.val = true)

lemma petersen_exposure_table :
    ∀ x : Fin 10, x ∈ ({1, 4, 5} : Finset (Fin 10)) →
    ∀ y : Fin 10, y ≠ 0 → y ≠ x →
      (∀ a ∈ exposureSet x y, ∀ b ∈ exposureSet x y, ¬ petersenAdj a b) ∧
      y ∈ exposureSet x y ∧
      (∃ a ∈ exposureSet x y, a ∈ ({1, 4, 5} : Finset (Fin 10))) ∧
      ∃ a ∈ exposureSet x y, petersenAdj x a := by
  unfold exposureSet exposureMask petersenAdj
  decide +kernel

lemma petersen_graph_ok : sem_Gr petersenAdj := by
  unfold sem_Gr petersenAdj
  decide +kernel

lemma petersen_other_exit_pure {D : Dag} (hS : Strict 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    {x : Fin 10} (hx : x ∈ ({1, 4, 5} : Finset (Fin 10)))
    {e f : ℕ × Bool}
    (hW : exitArcs 10 D (carrierT 10 D {x}) ⊆ {e, f})
    (hf : f ∈ exitArcs 10 D (carrierT 10 D {x}))
    (hSub : ({1, 4, 5} : Finset (Fin 10)) ⊆ supp 10 D (src D e)) :
    supp 10 D (src D f) = {x} := by
  have hx0 : x ≠ 0 := by
    have h : ∀ a : Fin 10, a ∈ ({1, 4, 5} : Finset (Fin 10)) → a ≠ 0 := by decide
    exact h x hx
  refine sem_two_exit_other_pure petersen_graph_ok hS hC hx0 hz hW hf hSub ?_
  intro y hy0 hyx
  exact ⟨exposureSet x y, petersen_exposure_table x hx y hy0 hyx⟩

lemma petersen_tight_nonzero_exit_card {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hB : Bplus 10 D = (eligSet 10 D).card) :
    ∀ x : Fin 10, x ≠ 0 → (exitArcs 10 D (carrierT 10 D {x})).card = 2 := by
  have hle := sem_tight_exit_le_two petersen_graph_ok h hC hB
  obtain ⟨e0, he0, _, hp0, ho0, hn0, _, _⟩ := sem_inelig_consumer petersen_graph_ok h hC hz
  let e : ℕ × Bool := (e0.1, !e0.2)
  have hbar : supp 10 D (src D (e.1, !e.2)) = {(0 : Fin 10)} := by
    simpa [e] using hp0
  have hSub : ({1, 4, 5} : Finset (Fin 10)) ⊆ supp 10 D (src D e) := by
    intro x hx
    apply hn0
    have hh : ∀ a : Fin 10, a ∈ ({1, 4, 5} : Finset (Fin 10)) → petersenAdj 0 a := by
      unfold petersenAdj
      decide
    exact hh x hx
  have he : ∀ x ∈ ({1, 4, 5} : Finset (Fin 10)), e ∈ exitArcs 10 D (carrierT 10 D {x}) := by
    intro x hx
    apply sem_mem_exit1.mpr
    exact ⟨he0, hSub hx, by rw [show 10 + e.1 = 10 + e0.1 from rfl, ho0]; simp⟩
  have hn : ∀ x ∈ ({1, 4, 5} : Finset (Fin 10)),
      (exitArcs 10 D (carrierT 10 D {x})).card = 2 := by
    intro x hx
    have hh : ∀ a : Fin 10, a ∈ ({1, 4, 5} : Finset (Fin 10)) →
        ∃ b ∈ ({1, 4, 5} : Finset (Fin 10)), b ≠ a := by decide
    obtain ⟨y, hy, hyx⟩ := hh x hx
    have hge := sem_nonpure_exit_card petersen_graph_ok h.1 hC (he x hx) (hSub hy) hyx
    exact Nat.le_antisymm (hle x) hge
  have hrest : ∀ y : Fin 10, y ≠ 0 → y ∉ ({1, 4, 5} : Finset (Fin 10)) →
      2 ≤ (exitArcs 10 D (carrierT 10 D {y})).card := by
    intro y hy0 hyN
    have hh : ∀ b : Fin 10, b ≠ 0 → b ∉ ({1, 4, 5} : Finset (Fin 10)) →
        ∃ a ∈ ({1, 4, 5} : Finset (Fin 10)), ∃ c : Fin 10,
          petersenAdj a b ∧ petersenAdj a c ∧ c ≠ 0 ∧ c ≠ b := by
      unfold petersenAdj
      decide
    obtain ⟨x, hx, a, hxy, hxa, ha0, hay⟩ := hh y hy0 hyN
    have hcard : ((exitArcs 10 D (carrierT 10 D {x})).erase e).card = 1 := by
      rw [Finset.card_erase_of_mem (he x hx), hn x hx]
    obtain ⟨f, hf⟩ := Finset.card_eq_one.mp hcard
    have hEq : exitArcs 10 D (carrierT 10 D {x}) = {e, f} := by
      rw [← Finset.insert_erase (he x hx), hf]
    exact sem_two_exit_neighbor_card petersen_graph_ok h.1 hC
      (by rw [hEq]) hbar hxy hxa hy0 ha0 hay
  intro x hx
  by_cases hxN : x ∈ ({1, 4, 5} : Finset (Fin 10))
  · exact hn x hxN
  · exact Nat.le_antisymm (hle x) (hrest x hx hxN)

lemma petersen_tight_merges_empty {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hB : Bplus 10 D = (eligSet 10 D).card) (x : Fin 10) :
    merges 10 D (carrierT 10 D {x}) = ∅ := by
  by_cases hx : x = 0
  · subst x
    obtain ⟨_, _, _, _, _, _, _, hm⟩ := sem_inelig_consumer petersen_graph_ok h hC hz
    exact hm
  · obtain ⟨b, hb⟩ := sem_exists_pureBranch petersen_graph_ok h.1 hC
    have hw := petersen_tight_nonzero_exit_card h hC hz hB x hx
    have hs := surplus_carrierT_le h.1 b hb {x}
    have hf := carrier_flow_union h {x} (by rw [sem_supp_out petersen_graph_ok hC]; simp)
    have hi : (({x} : Finset (Fin 10)) ∩ eligSet 10 D).card ≤ 1 :=
      (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
    rw [Finset.card_singleton] at hf
    apply Finset.card_eq_zero.mp
    omega

lemma petersen_tight_ineligible_singleton {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hB : Bplus 10 D = (eligSet 10 D).card) :
    ineligSet 10 D = {0} := by
  apply Finset.Subset.antisymm
  · intro x hx
    rw [Finset.mem_singleton]
    by_contra hx0
    have hw := petersen_tight_nonzero_exit_card h hC hz hB x hx0
    have hs := sem_inelig_surplus hx
    have hf := carrier_flow_union h {x} (by rw [sem_supp_out petersen_graph_ok hC]; simp)
    rw [Finset.card_singleton] at hf
    omega
  · exact Finset.singleton_subset_iff.mpr hz

end DagTools

namespace DagTools

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

lemma sem_shared_two_third_avoids (hG : sem_Gr G) (hS : Strict n D)
    (hC : sem_Comp n G D) (S : Finset (Fin n)) (P Q : ℕ × Bool)
    (R : Fin n → ℕ × Bool)
    (hW : ∀ x ∈ S, exitArcs n D (carrierT n D {x}) ⊆ {P, Q, R x})
    (hP : ∀ x ∈ S, x ∈ supp n D (src D P))
    (hQ : ∀ x ∈ S, x ∈ supp n D (src D Q))
    {x y : Fin n} (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) :
    y ∉ supp n D (src D (R x)) := by
  intro hbad
  obtain ⟨z, hxz, hyz⟩ := hG.2.2.1 x y hxy
  have hA : ∀ a ∈ ({y, z} : Finset (Fin n)), ∀ b ∈ ({y, z} : Finset (Fin n)), ¬ G a b := by
    intro a ha b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact hG.2.1 _
    · exact hyz
    · exact fun h => hyz (hG.1 _ _ h)
    · exact hG.2.1 _
  obtain ⟨j, s, hj, _, hxs, hxn, hd⟩ := sem_exposure hG hS hC {y, z} hA x ⟨z, by simp, hxz⟩
  have hslots := hW x hx (sem_mem_exit1.mpr ⟨hj, hxs, hxn⟩)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hslots
  rcases hslots with he | he | he
  · exact Finset.disjoint_left.mp hd (by simpa only [he] using hP y hy) (by simp)
  · exact Finset.disjoint_left.mp hd (by simpa only [he] using hQ y hy) (by simp)
  · exact Finset.disjoint_left.mp hd (by simpa only [he] using hbad) (by simp)

lemma sem_shared_two_edge_pairs (hG : sem_Gr G) (hS : Strict n D)
    (hC : sem_Comp n G D) (S : Finset (Fin n)) (P Q : ℕ × Bool)
    (R : Fin n → ℕ × Bool)
    (hW : ∀ x ∈ S, exitArcs n D (carrierT n D {x}) ⊆ {P, Q, R x})
    (hP : ∀ x ∈ S, x ∈ supp n D (src D P))
    (hQ : ∀ x ∈ S, x ∈ supp n D (src D Q))
    {x y : Fin n} (hx : x ∈ S) (hy : y ∈ S) (hxy : G x y) :
    ((R x).1, !(R x).2) = R y := by
  obtain ⟨j, hj, _, _, hxn, hyn, s, hxs, hysn, hys, hxsn⟩ := sem_joint_meeting hG hS hC hxy
  have hslots := hW x hx (sem_mem_exit1.mpr ⟨hj, hxs, hxn⟩)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hslots
  have he : (j, s) = R x := by
    rcases hslots with he | he | he
    · exact False.elim (hysn (by simpa only [he] using hP y hy))
    · exact False.elim (hysn (by simpa only [he] using hQ y hy))
    · exact he
  have hslots' := hW y hy (sem_mem_exit1.mpr ⟨hj, hys, hyn⟩)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hslots'
  have hf : (j, !s) = R y := by
    rcases hslots' with hf | hf | hf
    · exact False.elim (hxsn (by simpa only [hf] using hP x hx))
    · exact False.elim (hxsn (by simpa only [hf] using hQ x hx))
    · exact hf
  simpa only [← he] using hf

lemma sem_shared_two_matching (hG : sem_Gr G) (hS : Strict n D)
    (hC : sem_Comp n G D) (S : Finset (Fin n)) (P Q : ℕ × Bool)
    (R : Fin n → ℕ × Bool)
    (hW : ∀ x ∈ S, exitArcs n D (carrierT n D {x}) ⊆ {P, Q, R x})
    (hP : ∀ x ∈ S, x ∈ supp n D (src D P))
    (hQ : ∀ x ∈ S, x ∈ supp n D (src D Q))
    (hR : ∀ x ∈ S, x ∈ supp n D (src D (R x))) :
    ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, G x y → G x z → y = z := by
  intro x hx y hy z hz hxy hxz
  by_contra hyz
  have h1 := sem_shared_two_edge_pairs hG hS hC S P Q R hW hP hQ hx hy hxy
  have h2 := sem_shared_two_edge_pairs hG hS hC S P Q R hW hP hQ hx hz hxz
  have h3 : R y = R z := h1.symm.trans h2
  have hnot := sem_shared_two_third_avoids hG hS hC S P Q R hW hP hQ hy hz hyz
  exact hnot (by rw [h3]; exact hR z hz)

lemma sem_three_exits_common_matching (hG : sem_Gr G) (hS : Strict n D)
    (hC : sem_Comp n G D) (S : Finset (Fin n)) (P Q : ℕ × Bool) (hPQ : P ≠ Q)
    (hcard : ∀ x ∈ S, (exitArcs n D (carrierT n D {x})).card = 3)
    (hP : ∀ x ∈ S, P ∈ exitArcs n D (carrierT n D {x}))
    (hQ : ∀ x ∈ S, Q ∈ exitArcs n D (carrierT n D {x})) :
    ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, G x y → G x z → y = z := by
  classical
  have hex : ∀ x ∈ S, ∃ R : ℕ × Bool,
      R ∈ exitArcs n D (carrierT n D {x}) ∧
      exitArcs n D (carrierT n D {x}) ⊆ {P, Q, R} := by
    intro x hx
    have hQ' : Q ∈ (exitArcs n D (carrierT n D {x})).erase P :=
      Finset.mem_erase.mpr ⟨Ne.symm hPQ, hQ x hx⟩
    have hc : (((exitArcs n D (carrierT n D {x})).erase P).erase Q).card = 1 := by
      rw [Finset.card_erase_of_mem hQ', Finset.card_erase_of_mem (hP x hx), hcard x hx]
    obtain ⟨R, hR⟩ := Finset.card_eq_one.mp hc
    have hRmem : R ∈ ((exitArcs n D (carrierT n D {x})).erase P).erase Q := by rw [hR]; simp
    refine ⟨R, (Finset.mem_erase.mp (Finset.mem_erase.mp hRmem).2).2, ?_⟩
    intro t ht
    by_cases htP : t = P
    · simp [htP]
    by_cases htQ : t = Q
    · simp [htQ]
    have htR : t ∈ ((exitArcs n D (carrierT n D {x})).erase P).erase Q :=
      Finset.mem_erase.mpr ⟨htQ, Finset.mem_erase.mpr ⟨htP, ht⟩⟩
    rw [hR, Finset.mem_singleton] at htR
    simp [htR]
  choose! R hR using hex
  exact sem_shared_two_matching hG hS hC S P Q R
    (fun x hx => (hR x hx).2)
    (fun x hx => (sem_mem_exit1.mp (hP x hx)).2.1)
    (fun x hx => (sem_mem_exit1.mp (hQ x hx)).2.1)
    (fun x hx => (sem_mem_exit1.mp (hR x hx).1).2.1)

def h3_opp (e : ℕ × Bool) : ℕ × Bool := (e.1, !e.2)

lemma h3_opp_opp (e : ℕ × Bool) : h3_opp (h3_opp e) = e := by
  simp [h3_opp]

lemma h3_pair_of_card_two {α : Type} [DecidableEq α] {W : Finset α} {e : α}
    (he : e ∈ W) (hcard : W.card = 2) : ∃ f, f ≠ e ∧ W = {e, f} := by
  have hc : (W.erase e).card = 1 := by rw [Finset.card_erase_of_mem he, hcard]
  obtain ⟨f, hf⟩ := Finset.card_eq_one.mp hc
  have hm : f ∈ W.erase e := by rw [hf]; simp
  refine ⟨f, (Finset.mem_erase.mp hm).1, ?_⟩
  rw [← Finset.insert_erase he, hf]

lemma h3_split_edge_pair {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}
    (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {x y cx cy : Fin n} {ax ay rx ry : ℕ × Bool}
    (hWx : exitArcs n D (carrierT n D {x}) ⊆ {ax, rx})
    (hWy : exitArcs n D (carrierT n D {y}) ⊆ {ay, ry})
    (hax : supp n D (src D (h3_opp ax)) = {cx})
    (hay : supp n D (src D (h3_opp ay)) = {cy})
    (hycx : y ≠ cx) (hxcy : x ≠ cy) (hxy : G x y) : h3_opp rx = ry := by
  obtain ⟨j, hj, _, _, hxn, hyn, s, hxs, _, hys, _⟩ := sem_joint_meeting hG hS hC hxy
  have hsx := hWx (sem_mem_exit1.mpr ⟨hj, hxs, hxn⟩)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hsx
  have hx : (j, s) = rx := by
    rcases hsx with he | he
    · have hy : y ∈ supp n D (src D (h3_opp ax)) := by simpa only [← he, h3_opp] using hys
      rw [hax, Finset.mem_singleton] at hy
      exact False.elim (hycx hy)
    · exact he
  have hsy := hWy (sem_mem_exit1.mpr ⟨hj, hys, hyn⟩)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hsy
  have hy : (j, !s) = ry := by
    rcases hsy with he | he
    · have hx : x ∈ supp n D (src D (h3_opp ay)) := by simpa [← he, h3_opp] using hxs
      rw [hay, Finset.mem_singleton] at hx
      exact False.elim (hxcy hx)
    · exact he
  simpa only [← hx, h3_opp] using hy

lemma h3_tight_petersen_five_groups {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hB : Bplus 10 D = (eligSet 10 D).card) :
    ∃ e0 e1 e4 e5 d : ℕ × Bool,
      supp 10 D (src D e0) = {0} ∧ supp 10 D (src D e1) = {1} ∧
      supp 10 D (src D e4) = {4} ∧ supp 10 D (src D e5) = {5} ∧
      exitArcs 10 D (carrierT 10 D {0}) = {e0} ∧
      exitArcs 10 D (carrierT 10 D {1}) = {h3_opp e0, e1} ∧
      exitArcs 10 D (carrierT 10 D {2}) = {h3_opp e1, h3_opp d} ∧
      exitArcs 10 D (carrierT 10 D {3}) = {h3_opp e4, d} ∧
      exitArcs 10 D (carrierT 10 D {4}) = {h3_opp e0, e4} ∧
      exitArcs 10 D (carrierT 10 D {5}) = {h3_opp e0, e5} ∧
      exitArcs 10 D (carrierT 10 D {6}) = {h3_opp e1, d} ∧
      exitArcs 10 D (carrierT 10 D {7}) = {h3_opp e5, d} ∧
      exitArcs 10 D (carrierT 10 D {8}) = {h3_opp e5, h3_opp d} ∧
      exitArcs 10 D (carrierT 10 D {9}) = {h3_opp e4, h3_opp d} := by
  have hc := petersen_tight_nonzero_exit_card h hC hz hB
  obtain ⟨e0, he0, _, hp0, ho0, hn0, hW0, _⟩ := sem_inelig_consumer petersen_graph_ok h hC hz
  let A := h3_opp e0
  have hbarA : supp 10 D (src D (h3_opp A)) = {(0 : Fin 10)} := by
    simpa only [A, h3_opp_opp] using hp0
  have hAN : ({1, 4, 5} : Finset (Fin 10)) ⊆ supp 10 D (src D A) := by
    intro x hx
    apply hn0
    have hh : ∀ a : Fin 10, a ∈ ({1, 4, 5} : Finset (Fin 10)) → petersenAdj 0 a := by
      unfold petersenAdj
      decide
    exact hh x hx
  have hAmem : ∀ x ∈ ({1, 4, 5} : Finset (Fin 10)), A ∈ exitArcs 10 D (carrierT 10 D {x}) := by
    intro x hx
    apply sem_mem_exit1.mpr
    exact ⟨he0, hAN hx, by rw [show 10 + A.1 = 10 + e0.1 from rfl, ho0]; simp⟩
  obtain ⟨e1, _, hW1⟩ := h3_pair_of_card_two (hAmem 1 (by decide)) (hc 1 (by decide))
  obtain ⟨e4, _, hW4⟩ := h3_pair_of_card_two (hAmem 4 (by decide)) (hc 4 (by decide))
  obtain ⟨e5, _, hW5⟩ := h3_pair_of_card_two (hAmem 5 (by decide)) (hc 5 (by decide))
  have hp1 : supp 10 D (src D e1) = {(1 : Fin 10)} :=
    petersen_other_exit_pure h.1 hC hz (by decide) (by rw [hW1]) (by rw [hW1]; simp) hAN
  have hp4 : supp 10 D (src D e4) = {(4 : Fin 10)} :=
    petersen_other_exit_pure h.1 hC hz (by decide) (by rw [hW4]) (by rw [hW4]; simp) hAN
  have hp5 : supp 10 D (src D e5) = {(5 : Fin 10)} :=
    petersen_other_exit_pure h.1 hC hz (by decide) (by rw [hW5]) (by rw [hW5]; simp) hAN
  have ha2 : h3_opp e1 ∈ exitArcs 10 D (carrierT 10 D {2}) :=
    sem_two_exit_remaining_slot petersen_graph_ok h.1 hC (by rw [hW1]) hbarA (by unfold petersenAdj; decide) (by decide)
  have ha6 : h3_opp e1 ∈ exitArcs 10 D (carrierT 10 D {6}) :=
    sem_two_exit_remaining_slot petersen_graph_ok h.1 hC (by rw [hW1]) hbarA (by unfold petersenAdj; decide) (by decide)
  have ha3 : h3_opp e4 ∈ exitArcs 10 D (carrierT 10 D {3}) :=
    sem_two_exit_remaining_slot petersen_graph_ok h.1 hC (by rw [hW4]) hbarA (by unfold petersenAdj; decide) (by decide)
  have ha9 : h3_opp e4 ∈ exitArcs 10 D (carrierT 10 D {9}) :=
    sem_two_exit_remaining_slot petersen_graph_ok h.1 hC (by rw [hW4]) hbarA (by unfold petersenAdj; decide) (by decide)
  have ha7 : h3_opp e5 ∈ exitArcs 10 D (carrierT 10 D {7}) :=
    sem_two_exit_remaining_slot petersen_graph_ok h.1 hC (by rw [hW5]) hbarA (by unfold petersenAdj; decide) (by decide)
  have ha8 : h3_opp e5 ∈ exitArcs 10 D (carrierT 10 D {8}) :=
    sem_two_exit_remaining_slot petersen_graph_ok h.1 hC (by rw [hW5]) hbarA (by unfold petersenAdj; decide) (by decide)
  obtain ⟨g2, _, hW2⟩ := h3_pair_of_card_two ha2 (hc 2 (by decide))
  obtain ⟨g3, _, hW3⟩ := h3_pair_of_card_two ha3 (hc 3 (by decide))
  obtain ⟨g6, _, hW6⟩ := h3_pair_of_card_two ha6 (hc 6 (by decide))
  obtain ⟨g7, _, hW7⟩ := h3_pair_of_card_two ha7 (hc 7 (by decide))
  obtain ⟨g8, _, hW8⟩ := h3_pair_of_card_two ha8 (hc 8 (by decide))
  obtain ⟨g9, _, hW9⟩ := h3_pair_of_card_two ha9 (hc 9 (by decide))
  have hb1 : supp 10 D (src D (h3_opp (h3_opp e1))) = {(1 : Fin 10)} := by rw [h3_opp_opp]; exact hp1
  have hb4 : supp 10 D (src D (h3_opp (h3_opp e4))) = {(4 : Fin 10)} := by rw [h3_opp_opp]; exact hp4
  have hb5 : supp 10 D (src D (h3_opp (h3_opp e5))) = {(5 : Fin 10)} := by rw [h3_opp_opp]; exact hp5
  have h23 : h3_opp g2 = g3 := h3_split_edge_pair petersen_graph_ok h.1 hC
    (by rw [hW2]) (by rw [hW3]) hb1 hb4 (by decide) (by decide) (by unfold petersenAdj; decide)
  have h38 : h3_opp g3 = g8 := h3_split_edge_pair petersen_graph_ok h.1 hC
    (by rw [hW3]) (by rw [hW8]) hb4 hb5 (by decide) (by decide) (by unfold petersenAdj; decide)
  have h86 : h3_opp g8 = g6 := h3_split_edge_pair petersen_graph_ok h.1 hC
    (by rw [hW8]) (by rw [hW6]) hb5 hb1 (by decide) (by decide) (by unfold petersenAdj; decide)
  have h69 : h3_opp g6 = g9 := h3_split_edge_pair petersen_graph_ok h.1 hC
    (by rw [hW6]) (by rw [hW9]) hb1 hb4 (by decide) (by decide) (by unfold petersenAdj; decide)
  have h97 : h3_opp g9 = g7 := h3_split_edge_pair petersen_graph_ok h.1 hC
    (by rw [hW9]) (by rw [hW7]) hb4 hb5 (by decide) (by decide) (by unfold petersenAdj; decide)
  have hg2 : g2 = h3_opp g3 := by rw [← h23, h3_opp_opp]
  have hg6 : g6 = g3 := by rw [← h86, ← h38, h3_opp_opp]
  have hg9 : g9 = h3_opp g3 := by rw [← h69, hg6]
  have hg7 : g7 = g3 := by rw [← h97, hg9, h3_opp_opp]
  refine ⟨e0, e1, e4, e5, g3, hp0, hp1, hp4, hp5, hW0, hW1, ?_, hW3, hW4, hW5, ?_, ?_, ?_, ?_⟩
  · simpa only [hg2] using hW2
  · simpa only [hg6] using hW6
  · simpa only [hg7] using hW7
  · simpa only [← h38] using hW8
  · simpa only [hg9] using hW9

end DagTools

namespace DagTools

lemma h3_tight_branch_pure {n : ℕ} {D : Dag} (hS : Strict n D)
    (b : Fin n → ℕ) (hb : PureBranch n D b)
    (hB : Bplus n D = (eligSet n D).card) {w : ℕ}
    (hf : 2 ≤ fanout D w) (hs : (supp n D w).Nonempty) :
    fanout D w = 2 ∧ ∃ v ∈ eligSet n D, supp n D w = {v} := by
  have hc := card_residual hS b hb
  have hr : residualUnits n D b = ∅ := Finset.card_eq_zero.mp (by omega)
  have hu : ∀ k : ℕ, k + 1 < fanout D w →
      (⟨w, k⟩ : Σ _ : ℕ, ℕ) ∈ reservedUnits n D b := by
    intro k hk
    have huplus : (⟨w, k⟩ : Σ _ : ℕ, ℕ) ∈ unitsPlus n D := by
      rw [unitsPlus, Finset.mem_filter, mem_units]
      exact ⟨⟨sb_mem_inner.mpr (lt_of_fanout_pos hS (w := w) (by omega)), hk⟩, hs⟩
    by_contra hn
    have hm : (⟨w, k⟩ : Σ _ : ℕ, ℕ) ∈ residualUnits n D b :=
      Finset.mem_sdiff.mpr ⟨huplus, hn⟩
    rw [hr] at hm
    exact Finset.notMem_empty _ hm
  obtain ⟨v, hv, he⟩ := Finset.mem_image.mp (hu 0 (by omega))
  have hw : b v = w := congrArg Sigma.fst he
  have hle : fanout D w ≤ 2 := by
    by_contra hn
    obtain ⟨u, _, he'⟩ := Finset.mem_image.mp (hu 1 (by omega))
    have hz := congrArg (fun z : Σ _ : ℕ, ℕ => z.2) he'
    simp at hz
  exact ⟨by omega, v, hv, hw ▸ (hb v hv).2⟩

lemma h3_sem_tight_branch_pure {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}
    (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    (hB : Bplus n D = (eligSet n D).card) {w : ℕ}
    (hf : 2 ≤ fanout D w) (hs : (supp n D w).Nonempty) :
    fanout D w = 2 ∧ ∃ v ∈ eligSet n D, supp n D w = {v} := by
  obtain ⟨b, hb⟩ := sem_exists_pureBranch hG hS hC
  exact h3_tight_branch_pure hS b hb hB hf hs

end DagTools

namespace SideGeometry

def adj (x y : Fin 10) : Prop :=
  (([50, 69, 138, 276, 521, 385, 770, 548, 104, 208] : List Nat).getD x.val 0).testBit y.val = true

def mask (m : Nat) : Finset (Fin 10) :=
  Finset.univ.filter (fun x => m.testBit x.val = true)

def side (i : Fin 10) : Finset (Fin 10) :=
  mask (([1, 50, 2, 68, 16, 520, 32, 384, 200, 772] : List Nat).getD i.val 0)

def allowed (i : Fin 10) : Finset (Fin 10) :=
  mask (([1, 1023, 3, 68, 17, 520, 33, 384, 200, 772] : List Nat).getD i.val 0)

def witnessVertex (i y : Fin 10) : Fin 10 :=
  ⟨(([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6, 0, 6, 6, 6, 0, 6, 6, 6, 0, 4, 4, 4, 0, 4, 4, 4, 4, 4, 9, 9, 9, 0, 9, 9, 9, 9, 9, 0, 0, 5, 5, 5, 5, 0, 5, 5, 5, 5, 8, 8, 8, 8, 8, 8, 8, 0, 0, 8, 7, 7, 7, 0, 7, 6, 0, 0, 7, 7, 9, 9, 0, 9, 8, 9, 9, 9, 0, 0] : List Nat).getD (10 * i.val + y.val) 0) % 10, Nat.mod_lt _ (by decide)⟩

def witnessSet (i y : Fin 10) : Finset (Fin 10) :=
  mask (([0, 2, 20, 10, 16, 32, 80, 130, 258, 514, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 104, 20, 36, 80, 208, 276, 548, 385, 10, 0, 10, 146, 42, 0, 130, 384, 520, 0, 10, 548, 10, 0, 40, 104, 138, 770, 514, 69, 274, 20, 0, 20, 52, 68, 384, 272, 0, 0, 130, 276, 138, 144, 0, 208, 130, 258, 770, 69, 522, 36, 520, 52, 36, 68, 0, 0, 520, 261, 770, 260, 0, 276, 548, 0, 0, 260, 768, 73, 138, 0, 72, 208, 104, 72, 136, 0, 0] : List Nat).getD (10 * i.val + y.val) 0)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma exposure_table : ∀ i y : Fin 10, y ∉ allowed i →
    witnessVertex i y ∈ side i ∧
    (∀ a ∈ witnessSet i y, ∀ b ∈ witnessSet i y, ¬ adj a b) ∧
    y ∈ witnessSet i y ∧
    (∃ a ∈ witnessSet i y, adj (witnessVertex i y) a) ∧
    ∀ j : Fin 10, j ≠ i → witnessVertex i y ∈ side j →
      (side j ∩ witnessSet i y).Nonempty := by
  unfold allowed side witnessVertex witnessSet mask adj
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma side_intersection : ∀ i j : Fin 10, i ≠ j → (side i ∩ side j).card ≤ 1 := by
  unfold side mask
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma incidence_count : ∀ x : Fin 10,
    (Finset.univ.filter (fun i : Fin 10 => x ∈ side i)).card = if x = 0 then 1 else 2 := by
  unfold side mask
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma allowed_bound : ∀ i : Fin 10, i ≠ 1 → allowed i ⊆ insert 0 (side i) := by
  unfold allowed side mask
  decide +kernel

lemma allowed_zero : allowed 0 = ({0} : Finset (Fin 10)) := by decide +kernel

lemma side_zero : side 0 = ({0} : Finset (Fin 10)) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma side_nonempty : ∀ i : Fin 10, (side i).Nonempty := by
  unfold side mask
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma side_zero_absent : ∀ i : Fin 10, i ≠ 0 → (0 : Fin 10) ∉ side i := by
  unfold side mask
  decide +kernel

lemma support_bound (S : Fin 10 → Finset (Fin 10))
    (hsub : ∀ i, side i ⊆ S i)
    (hexposure : ∀ (x : Fin 10) (A : Finset (Fin 10)),
      (∀ a ∈ A, ∀ b ∈ A, ¬ adj a b) → (∃ a ∈ A, adj x a) →
      ∃ j : Fin 10, x ∈ side j ∧ Disjoint (S j) A) :
    ∀ i, S i ⊆ allowed i := by
  intro i y hy
  by_contra hnot
  obtain ⟨hx, hA, hyA, hnb, hhit⟩ := exposure_table i y hnot
  obtain ⟨j, hxj, hd⟩ := hexposure (witnessVertex i y) (witnessSet i y) hA hnb
  by_cases hji : j = i
  · subst j
    exact Finset.disjoint_left.mp hd hy hyA
  · obtain ⟨a, ha⟩ := hhit j hji hxj
    exact Finset.disjoint_left.mp hd (hsub j (Finset.mem_inter.mp ha).1)
      (Finset.mem_inter.mp ha).2

lemma supports_exact (S : Fin 10 → Finset (Fin 10))
    (hsub : ∀ i, side i ⊆ S i)
    (hbound : ∀ i, S i ⊆ allowed i)
    (hzero : ∀ i, (0 : Fin 10) ∈ S i → S i = {0})
    (hdrop : ∀ x, x ∈ S 1 → x ∉ S 0 → x ∈ side 1) :
    ∀ i, S i = side i := by
  have hS0 : S 0 = ({0} : Finset (Fin 10)) := by
    apply Finset.Subset.antisymm
    · simpa only [allowed_zero] using hbound 0
    · simpa only [side_zero] using hsub 0
  have hz : ∀ i : Fin 10, i ≠ 0 → (0 : Fin 10) ∉ S i := by
    intro i hi hmem
    obtain ⟨a, ha⟩ := side_nonempty i
    have hsa : a ∈ S i := hsub i ha
    rw [hzero i hmem, Finset.mem_singleton] at hsa
    exact side_zero_absent i hi (hsa ▸ ha)
  intro i
  apply Finset.Subset.antisymm ?_ (hsub i)
  intro y hy
  by_cases hi : i = 0
  · subst i
    simpa only [hS0, side_zero] using hy
  by_cases hi1 : i = 1
  · subst i
    apply hdrop y hy
    rw [hS0, Finset.mem_singleton]
    intro hy0
    exact hz 1 (by decide) (hy0 ▸ hy)
  have hm := allowed_bound i hi1 (hbound i hy)
  rcases Finset.mem_insert.mp hm with hy0 | hside
  · exact False.elim (hz i hi (hy0 ▸ hy))
  · exact hside

def opposite (i : Fin 10) : Fin 10 :=
  ⟨((([1, 0, 3, 2, 5, 4, 7, 6, 9, 8] : List Nat).getD i.val 0) % 10),
    Nat.mod_lt _ (by decide)⟩

def dirtyVertices : Finset (Fin 10) := side 8 ∪ side 9

def oppositeUnion (x : Fin 10) : Finset (Fin 10) :=
  (Finset.univ.filter (fun i : Fin 10 => x ∈ side i)).biUnion (fun i => side (opposite i))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma opposite_involution : ∀ i : Fin 10, opposite (opposite i) = i := by
  unfold opposite
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma paired_disjoint : ∀ i : Fin 10, Disjoint (side i) (side (opposite i)) := by
  unfold side opposite mask
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma outside_misses_edge : ∀ x : Fin 10, x ∉ dirtyVertices →
    ∃ u ∈ side 8, ∃ v ∈ side 9, adj u v ∧ u ∉ oppositeUnion x ∧ v ∉ oppositeUnion x := by
  unfold dirtyVertices side oppositeUnion opposite mask adj
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma inside_other_opposite_disjoint : ∀ x : Fin 10, x ∈ dirtyVertices →
    ∀ i : Fin 10, i.val < 8 → x ∈ side i → Disjoint (side (opposite i)) dirtyVertices := by
  unfold dirtyVertices side opposite mask
  decide +kernel

lemma intersecting_sides_unique {R : Finset (Fin 10)} (hR : 2 ≤ R.card)
    {i j : Fin 10} (hi : R ⊆ side i) (hj : R ⊆ side j) : i = j := by
  by_contra hne
  have hcard := Finset.card_le_card (Finset.subset_inter hi hj)
  have hbound := side_intersection i j hne
  exact (Nat.not_succ_le_self 1) (hR.trans (hcard.trans hbound))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma side_allowed_unique : ∀ i j : Fin 10, side i ⊆ allowed j → side j ⊆ allowed i → i = j := by
  unfold side allowed mask
  decide +kernel

lemma zero_incidence : (Finset.univ.filter (fun i : Fin 10 => (0 : Fin 10) ∈ side i)) = {0} := by
  unfold side mask
  decide +kernel

lemma opposite_zero : opposite 0 = 1 := by decide +kernel

def incidenceIndices (x : Fin 10) : Finset (Fin 10) :=
  ([{0}, {1, 2}, {3, 9}, {5, 8}, {1, 4}, {1, 6}, {3, 8}, {7, 8}, {7, 9}, {5, 9}] :
    List (Finset (Fin 10))).getD x.val ∅

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma incidence_indices : ∀ x : Fin 10,
    (Finset.univ.filter (fun i : Fin 10 => x ∈ side i)) = incidenceIndices x := by
  unfold side mask incidenceIndices
  decide +kernel

def separator (x : Fin 10) : Finset (Fin 10) :=
  mask (([13, 266, 12, 12, 148, 44, 320, 132, 264, 576] : List Nat).getD x.val 0)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma separator_spec : ∀ x : Fin 10,
    x ∈ separator x ∧
    (∃ u ∈ side 8, ∃ v ∈ side 9, adj u v ∧ u ∈ separator x ∧ v ∈ separator x) ∧
    ∀ i : Fin 10, i.val < 8 →
      Disjoint (side i) (separator x) ∨ Disjoint (side (opposite i)) (separator x) := by
  unfold separator side mask adj opposite
  decide +kernel

end SideGeometry

namespace DagTools

lemma h3_indexed_sources_exact {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (r : Fin 10 → ℕ × Bool)
    (hW : ∀ x : Fin 10, exitArcs 10 D (carrierT 10 D {x}) =
      (Finset.univ.filter (fun i : Fin 10 => x ∈ SideGeometry.side i)).image r)
    (hopp : ∀ i : Fin 10, r (SideGeometry.opposite i) = ((r i).1, !(r i).2)) :
    Function.Injective r ∧ ∀ i, supp 10 D (src D (r i)) = SideGeometry.side i := by
  have hS := h.1
  let S : Fin 10 → Finset (Fin 10) := fun i => supp 10 D (src D (r i))
  have hmem : ∀ (i x : Fin 10), x ∈ SideGeometry.side i →
      r i ∈ exitArcs 10 D (carrierT 10 D {x}) := by
    intro i x hx
    rw [hW]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hx⟩, rfl⟩
  have hsub : ∀ i, SideGeometry.side i ⊆ S i := by
    intro i x hx
    exact (sem_mem_exit1.mp (hmem i x hx)).2.1
  have hb : ∀ i, S i ⊆ SideGeometry.allowed i := by
    apply SideGeometry.support_bound S hsub
    intro x A hA hnb
    obtain ⟨j, s, hj, _, hxs, hxn, hd⟩ :=
      sem_exposure petersen_graph_ok hS hC A hA x hnb
    have hm : (j, s) ∈ exitArcs 10 D (carrierT 10 D {x}) :=
      sem_mem_exit1.mpr ⟨hj, hxs, hxn⟩
    rw [hW] at hm
    obtain ⟨i, hi, hri⟩ := Finset.mem_image.mp hm
    exact ⟨i, (Finset.mem_filter.mp hi).2, by simpa only [S, hri] using hd⟩
  have hinj : Function.Injective r := by
    intro i j heq
    apply SideGeometry.side_allowed_unique i j
    · intro x hx
      apply hb j
      simpa only [S, ← heq] using hsub i hx
    · intro x hx
      apply hb i
      simpa only [S, heq] using hsub j hx
  refine ⟨hinj, ?_⟩
  apply SideGeometry.supports_exact S hsub hb
  · intro i hi
    exact sem_inelig_pure petersen_graph_ok hS hC hz hi
  · intro x hx _
    have hW0 : exitArcs 10 D (carrierT 10 D {0}) = {r 0} := by
      rw [hW, SideGeometry.zero_incidence]
      simp
    obtain ⟨e, he, _, _, ho, _, hWe, _⟩ := sem_inelig_consumer petersen_graph_ok
      h hC hz
    have her : e = r 0 := Finset.singleton_injective (hWe.symm.trans hW0)
    rw [her] at he ho
    have hr : r 1 = ((r 0).1, !(r 0).2) := by
      simpa only [SideGeometry.opposite_zero] using hopp 0
    have hm : r 1 ∈ exitArcs 10 D (carrierT 10 D {x}) := by
      apply sem_mem_exit1.mpr
      refine ⟨?_, hx, ?_⟩
      · simpa only [hr] using he
      · have hout : supp 10 D (10 + (r 1).1) = ∅ := by simpa only [hr] using ho
        rw [hout]
        simp
    rw [hW] at hm
    obtain ⟨i, hi, hri⟩ := Finset.mem_image.mp hm
    have hi1 : i = 1 := hinj hri
    simpa only [hi1] using (Finset.mem_filter.mp hi).2

def h3_sideMap (e0 e1 e4 e5 d : ℕ × Bool) (i : Fin 10) : ℕ × Bool :=
  ([e0, h3_opp e0, e1, h3_opp e1, e4, h3_opp e4, e5, h3_opp e5, d, h3_opp d] :
    List (ℕ × Bool)).getD i.val e0

lemma h3_sideMap_opposite (e0 e1 e4 e5 d : ℕ × Bool) : ∀ i : Fin 10,
    h3_sideMap e0 e1 e4 e5 d (SideGeometry.opposite i) =
      ((h3_sideMap e0 e1 e4 e5 d i).1, !(h3_sideMap e0 e1 e4 e5 d i).2) := by
  intro i
  fin_cases i <;> simp [h3_sideMap, SideGeometry.opposite, h3_opp]

lemma h3_tight_sources_exist {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hB : Bplus 10 D = (eligSet 10 D).card) :
    ∃ r : Fin 10 → ℕ × Bool, Function.Injective r ∧
      (∀ i, r (SideGeometry.opposite i) = ((r i).1, !(r i).2)) ∧
      (∀ i, supp 10 D (src D (r i)) = SideGeometry.side i) ∧
      ∀ x : Fin 10, exitArcs 10 D (carrierT 10 D {x}) =
        (Finset.univ.filter (fun i : Fin 10 => x ∈ SideGeometry.side i)).image r := by
  obtain ⟨e0, e1, e4, e5, d, _, _, _, _, hW0, hW1, hW2, hW3, hW4,
    hW5, hW6, hW7, hW8, hW9⟩ := h3_tight_petersen_five_groups h hC hz hB
  let r := h3_sideMap e0 e1 e4 e5 d
  have hopp : ∀ i : Fin 10, r (SideGeometry.opposite i) = ((r i).1, !(r i).2) :=
    h3_sideMap_opposite e0 e1 e4 e5 d
  have hW : ∀ x : Fin 10, exitArcs 10 D (carrierT 10 D {x}) =
      (Finset.univ.filter (fun i : Fin 10 => x ∈ SideGeometry.side i)).image r := by
    intro x
    rw [SideGeometry.incidence_indices]
    fin_cases x
    · simpa [r, h3_sideMap, SideGeometry.incidenceIndices] using hW0
    · simpa [r, h3_sideMap, SideGeometry.incidenceIndices] using hW1
    · simpa [r, h3_sideMap, SideGeometry.incidenceIndices] using hW2
    · simpa [r, h3_sideMap, SideGeometry.incidenceIndices] using hW3
    · simpa [r, h3_sideMap, SideGeometry.incidenceIndices] using hW4
    · simpa [r, h3_sideMap, SideGeometry.incidenceIndices] using hW5
    · simpa [r, h3_sideMap, SideGeometry.incidenceIndices] using hW6
    · simpa [r, h3_sideMap, SideGeometry.incidenceIndices] using hW7
    · simpa [r, h3_sideMap, SideGeometry.incidenceIndices] using hW8
    · simpa [r, h3_sideMap, SideGeometry.incidenceIndices] using hW9
  obtain ⟨hinj, hsources⟩ := h3_indexed_sources_exact h hC hz r hW hopp
  exact ⟨r, hinj, hopp, hsources, hW⟩

lemma h3_no_merges_inputs_disjoint {n : ℕ} {D : Dag} (hS : Strict n D)
    (hM : ∀ x : Fin n, merges n D (carrierT n D {x}) = ∅)
    {j : ℕ} (hj : j < D.length) :
    Disjoint (supp n D (opA D j)) (supp n D (opB D j)) := by
  apply Finset.disjoint_left.mpr
  intro x hxa hxb
  have hxout : x ∈ supp n D (n + j) := by
    rw [supp_gate hS j hj]
    split_ifs
    · exact Finset.mem_inter.mpr ⟨hxa, hxb⟩
    · exact Finset.mem_union.mpr (Or.inl hxa)
  have hm : j ∈ merges n D (carrierT n D {x}) := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr hj, sem_mem_carrier1.mpr hxout,
      sem_mem_carrier1.mpr hxa, sem_mem_carrier1.mpr hxb⟩
  rw [hM x] at hm
  exact Finset.notMem_empty j hm

lemma h3_tight_inputs_disjoint {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hB : Bplus 10 D = (eligSet 10 D).card) {j : ℕ} (hj : j < D.length) :
    Disjoint (supp 10 D (opA D j)) (supp 10 D (opB D j)) :=
  h3_no_merges_inputs_disjoint h.1 (petersen_tight_merges_empty h hC hz hB) hj

lemma h3_indexed_and_types {D : Dag} (hS : Strict 10 D)
    (r : Fin 10 → ℕ × Bool)
    (hW : ∀ x : Fin 10, exitArcs 10 D (carrierT 10 D {x}) =
      (Finset.univ.filter (fun i : Fin 10 => x ∈ SideGeometry.side i)).image r)
    (hopp : ∀ i : Fin 10, r (SideGeometry.opposite i) = ((r i).1, !(r i).2))
    (hsources : ∀ i, supp 10 D (src D (r i)) = SideGeometry.side i)
    (hM : ∀ x : Fin 10, merges 10 D (carrierT 10 D {x}) = ∅)
    {j : ℕ} (hj : j < D.length) (ht : tag D j = true) :
    (∃ i : Fin 10, r i = (j, false) ∧
      supp 10 D (opA D j) = SideGeometry.side i ∧
      supp 10 D (opB D j) = SideGeometry.side (SideGeometry.opposite i)) ∨
      (supp 10 D (opA D j) = ∅ ∧ supp 10 D (opB D j) = ∅) := by
  have hout : supp 10 D (10 + j) = ∅ := by
    rw [sem_supp_and hS hj ht]
    exact Finset.disjoint_iff_inter_eq_empty.mp (h3_no_merges_inputs_disjoint hS hM hj)
  have hindex : ∀ s : Bool, (supp 10 D (src D (j, s))).Nonempty →
      ∃ i : Fin 10, r i = (j, s) := by
    intro s hs
    obtain ⟨x, hx⟩ := hs
    have hm : (j, s) ∈ exitArcs 10 D (carrierT 10 D {x}) :=
      sem_mem_exit1.mpr ⟨hj, hx, by rw [hout]; simp⟩
    rw [hW] at hm
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hm
    exact ⟨i, hi⟩
  by_cases ha : (supp 10 D (opA D j)).Nonempty
  · obtain ⟨i, hi⟩ := hindex false (by simpa only [sb_src_false] using ha)
    left
    refine ⟨i, hi, ?_, ?_⟩
    · simpa only [hi, sb_src_false] using hsources i
    · have hb := hopp i
      rw [hi] at hb
      simpa only [hb, Bool.not_false, sb_src_true] using hsources (SideGeometry.opposite i)
  · by_cases hb : (supp 10 D (opB D j)).Nonempty
    · obtain ⟨i, hi⟩ := hindex true (by simpa only [sb_src_true] using hb)
      have hf := hopp i
      rw [hi] at hf
      have hm : (supp 10 D (opA D j)).Nonempty := by
        have hs : supp 10 D (opA D j) = SideGeometry.side (SideGeometry.opposite i) := by
          simpa only [hf, Bool.not_true, sb_src_false] using hsources (SideGeometry.opposite i)
        rw [hs]
        exact SideGeometry.side_nonempty (SideGeometry.opposite i)
      exact False.elim (ha hm)
    · exact Or.inr ⟨Finset.not_nonempty_iff_eq_empty.mp ha, Finset.not_nonempty_iff_eq_empty.mp hb⟩

lemma h3_exit_tag_and {n : ℕ} {D : Dag} (hS : Strict n D)
    {x : Fin n} {e : ℕ × Bool} (he : e ∈ exitArcs n D (carrierT n D {x})) :
    tag D e.1 = true := by
  obtain ⟨j, s⟩ := e
  obtain ⟨hj, hx, hn⟩ := sem_mem_exit1.mp he
  by_contra ht
  rw [Bool.not_eq_true] at ht
  apply hn
  rw [sem_supp_or hS hj ht, Finset.mem_union]
  cases s
  · exact Or.inl (by simpa only [sb_src_false] using hx)
  · exact Or.inr (by simpa only [sb_src_true] using hx)

lemma h3_indexed_gate_valid {D : Dag} (hS : Strict 10 D)
    (r : Fin 10 → ℕ × Bool)
    (hW : ∀ x : Fin 10, exitArcs 10 D (carrierT 10 D {x}) =
      (Finset.univ.filter (fun i : Fin 10 => x ∈ SideGeometry.side i)).image r)
    (hM : ∀ x : Fin 10, merges 10 D (carrierT 10 D {x}) = ∅) :
    ∀ i : Fin 10, (r i).1 < D.length ∧ tag D (r i).1 = true ∧
      supp 10 D (10 + (r i).1) = ∅ := by
  intro i
  obtain ⟨x, hx⟩ := SideGeometry.side_nonempty i
  have hm : r i ∈ exitArcs 10 D (carrierT 10 D {x}) := by
    rw [hW]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hx⟩, rfl⟩
  have hj := (sem_mem_exit1.mp hm).1
  have ht := h3_exit_tag_and hS hm
  refine ⟨hj, ht, ?_⟩
  rw [sem_supp_and hS hj ht]
  exact Finset.disjoint_iff_inter_eq_empty.mp (h3_no_merges_inputs_disjoint hS hM hj)

lemma h3_tight_typed_sources_exist {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hB : Bplus 10 D = (eligSet 10 D).card) :
    ∃ r : Fin 10 → ℕ × Bool, Function.Injective r ∧
      (∀ i, r (SideGeometry.opposite i) = ((r i).1, !(r i).2)) ∧
      (∀ i, supp 10 D (src D (r i)) = SideGeometry.side i) ∧
      (∀ x : Fin 10, exitArcs 10 D (carrierT 10 D {x}) =
        (Finset.univ.filter (fun i : Fin 10 => x ∈ SideGeometry.side i)).image r) ∧
      (∀ i : Fin 10, (r i).1 < D.length ∧ tag D (r i).1 = true ∧
        supp 10 D (10 + (r i).1) = ∅) ∧
      (∀ j, j < D.length → Disjoint (supp 10 D (opA D j)) (supp 10 D (opB D j))) ∧
      ∀ j, j < D.length → tag D j = true →
        (∃ i : Fin 10, r i = (j, false) ∧
          supp 10 D (opA D j) = SideGeometry.side i ∧
          supp 10 D (opB D j) = SideGeometry.side (SideGeometry.opposite i)) ∨
        (supp 10 D (opA D j) = ∅ ∧ supp 10 D (opB D j) = ∅) := by
  obtain ⟨r, hinj, hopp, hsources, hW⟩ := h3_tight_sources_exist h hC hz hB
  have hM := petersen_tight_merges_empty h hC hz hB
  refine ⟨r, hinj, hopp, hsources, hW, h3_indexed_gate_valid h.1 r hW hM, ?_, ?_⟩
  · intro j hj
    exact h3_no_merges_inputs_disjoint h.1 hM hj
  · intro j hj ht
    exact h3_indexed_and_types h.1 r hW hopp hsources hM hj ht

end DagTools

def geoAdj (x y : Fin 10) : Bool :=
  (([50, 69, 138, 276, 521, 385, 770, 548, 104, 208] : List Nat).getD x.val 0).testBit y.val

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
lemma petersen_induced_matching_card :
    ∀ S : Finset (Fin 10),
      (∀ x ∈ S, (S.filter (fun y => geoAdj x y = true)).card ≤ 1) → S.card ≤ 6 := by
  decide +kernel

def geoProfile (p : Fin 3) : List Nat :=
  if p = 0 then [0, 8, 0, 64, 0, 128, 1, 54, 2, 4, 16, 512, 32, 256, 200, 822]
  else if p = 1 then [0, 4, 0, 256, 0, 512, 1, 122, 2, 64, 8, 16, 32, 128, 250, 772]
  else [0, 4, 0, 256, 0, 512, 1, 250, 2, 64, 8, 16, 32, 128, 250, 772]

def geoFlip (k : Nat) : Nat := if k % 2 = 0 then k + 1 else k - 1

def geoMergeMask (p : Fin 3) (i j k : Fin 16) : Nat :=
  if k = i ∨ k = j then (geoProfile p).getD i.val 0 ||| (geoProfile p).getD j.val 0
  else if k.val = geoFlip i.val ∨ k.val = geoFlip j.val then
    (geoProfile p).getD (geoFlip i.val) 0 ||| (geoProfile p).getD (geoFlip j.val) 0
  else (geoProfile p).getD k.val 0

def geoWitnessVertex (p : Fin 3) : Fin 10 := if p = 0 then 8 else 3

def geoWitnessSet (p : Fin 3) : Nat := if p = 0 then 520 else 144

lemma geo_witness_independent :
    ∀ p : Fin 3, ∀ a b : Fin 10,
      (geoWitnessSet p).testBit a.val = true →
      (geoWitnessSet p).testBit b.val = true → geoAdj a b = false := by
  decide +kernel

lemma geo_witness_neighbor :
    ∀ p : Fin 3, ∃ a : Fin 10,
      (geoWitnessSet p).testBit a.val = true ∧ geoAdj (geoWitnessVertex p) a = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
lemma geo_exact_neighborhood_obstruction :
    ∀ (p : Fin 3) (i j : Fin 16),
      ((geoProfile p).getD i.val 0).testBit 4 = true →
      ((geoProfile p).getD j.val 0).testBit 5 = true →
      (((geoProfile p).getD i.val 0 ||| (geoProfile p).getD j.val 0).testBit 2 = false) →
      (((geoProfile p).getD i.val 0 ||| (geoProfile p).getD j.val 0).testBit 6 = false) →
      ∀ k : Fin 16,
        ((geoProfile p).getD k.val 0).testBit (geoWitnessVertex p).val = true →
        (geoMergeMask p i j k &&& geoWitnessSet p) ≠ 0 := by
  decide +kernel

end PEqualNP.Outside.L_meta_2590_aux
