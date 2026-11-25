import Mathlib.Data.List.GetD
import Mathlib.Data.Tree.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.AddSub
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


namespace DagTools

lemma h3_tight_size_budget {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hB : Bplus 10 D = (eligSet 10 D).card) (hs : D.length ≤ 19) :
    Bplus 10 D = 9 ∧ Bzero 10 D ≤ 1 ∧ 18 ≤ D.length := by
  have hi := petersen_tight_ineligible_singleton h hC hz hB
  have hc := inelig_card_add 10 D
  rw [hi, Finset.card_singleton] at hc
  have ht := surplus_identity h
  rw [totalSurplus_split] at ht
  omega

lemma h3_zero_branch_mem {n : ℕ} {D : Dag} (hS : Strict n D) {w : ℕ}
    (hf : 2 ≤ fanout D w) (he : supp n D w = ∅) :
    w ∈ (inner n D).filter (fun u => ¬ (supp n D u).Nonempty) :=
  Finset.mem_filter.mpr ⟨sb_mem_inner.mpr (lt_of_fanout_pos hS (w := w) (by omega)),
    by rw [he]; exact Finset.not_nonempty_empty⟩

lemma h3_zero_fanout_le {n : ℕ} {D : Dag} (hS : Strict n D) {w : ℕ}
    (he : supp n D w = ∅) : fanout D w ≤ Bzero n D + 1 := by
  by_cases hf : fanout D w ≤ 1
  · omega
  have hsum := Finset.single_le_sum (f := fun u => fanout D u - 1)
    (fun _ _ => Nat.zero_le _) (h3_zero_branch_mem hS (by omega) he)
  change fanout D w - 1 ≤ Bzero n D at hsum
  omega

lemma h3_zero_branch_unique {n : ℕ} {D : Dag} (hS : Strict n D)
    (hB : Bzero n D ≤ 1) {u v : ℕ}
    (hu : 2 ≤ fanout D u) (hu0 : supp n D u = ∅)
    (hv : 2 ≤ fanout D v) (hv0 : supp n D v = ∅) : u = v := by
  by_contra hne
  have hsub : ({u, v} : Finset ℕ) ⊆
      (inner n D).filter (fun w => ¬ (supp n D w).Nonempty) := by
    intro w hw
    rw [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact h3_zero_branch_mem hS hu hu0
    · exact h3_zero_branch_mem hS hv hv0
  have hsum := Finset.sum_le_sum_of_subset (f := fun w => fanout D w - 1) hsub
  rw [Finset.sum_pair hne] at hsum
  change fanout D u - 1 + (fanout D v - 1) ≤ Bzero n D at hsum
  omega

end DagTools

namespace DagTools

lemma h3_residual_singleton_surplus {n : ℕ} {D : Dag} (hS : Strict n D)
    (b : Fin n → ℕ) (hb : PureBranch n D b) (r : Σ _ : ℕ, ℕ)
    (hr : residualUnits n D b = {r}) (x : Fin n) :
    surplusOn D (carrierT n D {x}) =
      (if x ∈ eligSet n D then 1 else 0) +
      (if x ∈ supp n D r.1 then 1 else 0) := by
  rw [surplus_carrierT_eq hS b hb, hr]
  by_cases he : x ∈ eligSet n D <;> by_cases hx : x ∈ supp n D r.1 <;>
    simp [Finset.filter_singleton, Finset.inter_singleton, he, hx]

lemma h3_residual_singleton_flow {n : ℕ} {D : Dag} {G : Fin n → Fin n → Prop}
    (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (b : Fin n → ℕ) (hb : PureBranch n D b) (r : Σ _ : ℕ, ℕ)
    (hr : residualUnits n D b = {r}) (x : Fin n) :
    (exitArcs n D (carrierT n D {x})).card +
        (merges n D (carrierT n D {x})).card =
      1 + (if x ∈ eligSet n D then 1 else 0) +
        (if x ∈ supp n D r.1 then 1 else 0) := by
  have hf := carrier_flow_union h {x} (by rw [sem_supp_out hG hC]; simp)
  rw [Finset.card_singleton, h3_residual_singleton_surplus h.1 b hb r hr] at hf
  omega

lemma h3_residual_one_branch_unique {n : ℕ} {D : Dag} (hS : Strict n D)
    (b : Fin n → ℕ) (hb : PureBranch n D b)
    (hr : (residualUnits n D b).card ≤ 1) {u v : ℕ}
    (hu : 2 ≤ fanout D u) (hv : 2 ≤ fanout D v)
    (hup : (supp n D u).Nonempty) (hvp : (supp n D v).Nonempty)
    (hru : ∀ x ∈ eligSet n D, b x ≠ u)
    (hrv : ∀ x ∈ eligSet n D, b x ≠ v) : u = v := by
  have hm (w : ℕ) (hw : 2 ≤ fanout D w) (hp : (supp n D w).Nonempty)
      (hbw : ∀ x ∈ eligSet n D, b x ≠ w) :
      (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ residualUnits n D b := by
    apply Finset.mem_sdiff.mpr
    constructor
    · apply Finset.mem_filter.mpr
      exact ⟨mem_units.mpr ⟨sb_mem_inner.mpr (lt_of_fanout_pos hS (w := w) (by omega)), by dsimp; omega⟩, hp⟩
    · intro hc
      obtain ⟨x, hx, he⟩ := Finset.mem_image.mp hc
      exact hbw x hx (congrArg Sigma.fst he)
  exact congrArg Sigma.fst ((Finset.card_le_one.mp hr) _ (hm u hu hup hru) _ (hm v hv hvp hrv))

lemma h3_residual_one_unreserved_fanout {n : ℕ} {D : Dag} (hS : Strict n D)
    (b : Fin n → ℕ) (hb : PureBranch n D b)
    (hr : (residualUnits n D b).card ≤ 1) {w : ℕ}
    (hp : (supp n D w).Nonempty)
    (hw : ∀ x ∈ eligSet n D, b x ≠ w) : fanout D w ≤ 2 := by
  by_contra hc
  have hm (k : ℕ) (hk : k ≤ 1) : (⟨w, k⟩ : Σ _ : ℕ, ℕ) ∈ residualUnits n D b := by
    apply Finset.mem_sdiff.mpr
    constructor
    · apply Finset.mem_filter.mpr
      exact ⟨mem_units.mpr ⟨sb_mem_inner.mpr (lt_of_fanout_pos hS (w := w) (by omega)), by dsimp; omega⟩, hp⟩
    · intro hc
      obtain ⟨x, hx, he⟩ := Finset.mem_image.mp hc
      exact hw x hx (congrArg Sigma.fst he)
  have he := (Finset.card_le_one.mp hr) _ (hm 0 (by omega)) _ (hm 1 (by omega))
  have := congrArg (fun a : Σ _ : ℕ, ℕ => a.2) he
  change 0 = 1 at this
  omega

lemma h3_exact_i1_budget {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hi : ineligSet 10 D = {0})
    (hs : D.length ≤ 19) :
    (eligSet 10 D).card = 9 ∧
      (Bplus 10 D = 9 ∧ Bzero 10 D ≤ 1 ∧ 18 ≤ D.length ∨
       Bplus 10 D = 10 ∧ Bzero 10 D = 0 ∧ D.length = 19) := by
  obtain ⟨b, hb⟩ := sem_exists_pureBranch petersen_graph_ok h.1 hC
  have he := inelig_card_add 10 D
  rw [hi, Finset.card_singleton] at he
  have hp := elig_le_Bplus h.1 b hb
  have ht := surplus_identity h
  rw [totalSurplus_split] at ht
  omega

lemma h3_exact_i1_residual_le_one {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hi : ineligSet 10 D = {0})
    (hs : D.length ≤ 19) (b : Fin 10 → ℕ) (hb : PureBranch 10 D b) :
    (residualUnits 10 D b).card ≤ 1 := by
  have hbgt := h3_exact_i1_budget h hC hi hs
  have hr := card_residual h.1 b hb
  omega

end DagTools

namespace DagTools

def sem_W (n : ℕ) (D : Dag) (x : Fin n) : Finset (ℕ × Bool) := exitArcs n D (carrierT n D {x})

def sem_bar (e : ℕ × Bool) : ℕ × Bool := (e.1, !e.2)


section H3ResidualCodes

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


end H3ResidualCodes

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

def h3_saturatedSet (n : ℕ) (D : Dag) : Finset (Fin n) :=
  Finset.univ.filter (fun x => 3 ≤ (exitArcs n D (carrierT n D {x})).card)

lemma h3_one_residual_common_terminals {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}
    (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (hone : Bplus n D = (eligSet n D).card + 1) :
    ∃ P Q : ℕ × Bool, P.1 ≠ Q.1 ∧
      ∀ x ∈ h3_saturatedSet n D,
        P ∈ exitArcs n D (carrierT n D {x}) ∧
        Q ∈ exitArcs n D (carrierT n D {x}) := by
  classical
  by_cases hX : (h3_saturatedSet n D).Nonempty
  · obtain ⟨b, hb⟩ := sem_exists_minBranch hG h.1 hC
    exact sem_common_terminals hG h hC b hb hone (h3_saturatedSet n D) hX
      (fun x hx => (Finset.mem_filter.mp hx).2)
  · refine ⟨(0, false), (1, false), by decide, ?_⟩
    intro x hx
    exact False.elim (hX ⟨x, hx⟩)

lemma h3_one_residual_saturation {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}
    (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (hone : Bplus n D = (eligSet n D).card + 1) :
    ∀ x ∈ h3_saturatedSet n D,
      (exitArcs n D (carrierT n D {x})).card = 3 ∧
      merges n D (carrierT n D {x}) = ∅ ∧ x ∈ eligSet n D := by
  classical
  obtain ⟨b, hb⟩ := sem_exists_minBranch hG h.1 hC
  have hbp := sem_minBranch_pure hb
  have hcard : (residualUnits n D b).card = 1 := by
    have := card_residual h.1 b hbp
    omega
  obtain ⟨u0, hres⟩ := Finset.card_eq_one.mp hcard
  intro x hx
  have hx3 : 3 ≤ (sem_W n D x).card := (Finset.mem_filter.mp hx).2
  obtain ⟨hc, hm, he, _⟩ := sem_saturated hG h hC b hbp hres hx3
  exact ⟨hc, hm, he⟩

lemma h3_one_residual_matching {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}
    (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (hone : Bplus n D = (eligSet n D).card + 1) :
    ∀ x ∈ h3_saturatedSet n D, ∀ y ∈ h3_saturatedSet n D,
      ∀ z ∈ h3_saturatedSet n D, G x y → G x z → y = z := by
  obtain ⟨P, Q, hPQ, hterm⟩ := h3_one_residual_common_terminals hG h hC hone
  exact sem_three_exits_common_matching hG h.1 hC (h3_saturatedSet n D) P Q
    (fun he => hPQ (congrArg Prod.fst he))
    (fun x hx => (h3_one_residual_saturation hG h hC hone x hx).1)
    (fun x hx => (hterm x hx).1) (fun x hx => (hterm x hx).2)

lemma h3_petersen_one_residual_card {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D)
    (hone : Bplus 10 D = (eligSet 10 D).card + 1) :
    (h3_saturatedSet 10 D).card ≤ 6 := by
  have hmatch := h3_one_residual_matching petersen_graph_ok h hC hone
  apply petersen_induced_matching_card
  intro x hx
  apply Finset.card_le_one.mpr
  intro y hy z hz
  have hy' := Finset.mem_filter.mp hy
  have hz' := Finset.mem_filter.mp hz
  exact hmatch x hx y hy'.1 z hz'.1 hy'.2 hz'.2

end DagTools

namespace DagTools

section H3ForkRouting

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

lemma h3_sem_two_arms_routed (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (X : Finset (Fin n)) (hX : X.Nonempty)
    (hM : ∀ x ∈ X, merges n D (carrierT n D {x}) = ∅) (r : ℕ)
    (hr : ∀ x ∈ X, x ∈ supp n D r) (hf : 2 ≤ fanout D r)
    (hlow : ∀ x ∈ X, ∀ w, r < w → x ∈ supp n D w → fanout D w ≤ 1) :
    ∃ P Q : ℕ × Bool, P.1 ≠ Q.1 ∧
      (∀ x ∈ X, P ∈ sem_W n D x ∧ Q ∈ sem_W n D x) ∧
      ∃ j1 ∈ readers D r, ∃ j2 ∈ readers D r, j1 ≠ j2 ∧
        ((P.1 = j1 ∧ src D P = r) ∨
          Relation.ReflTransGen (sem_Arm n D X) (n + j1) (src D P)) ∧
        ((Q.1 = j2 ∧ src D Q = r) ∨
          Relation.ReflTransGen (sem_Arm n D X) (n + j2) (src D Q)) := by
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
  refine ⟨P, Q, fun hPQ => ?_, (fun x hx => ⟨hP1 x hx, hQ1 x hx⟩),
    j1, hj1, j2, hj2, hne, hP2, hQ2⟩
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

lemma h3_tight_carrier_branch_unique (hS : Strict n D) (b : Fin n → ℕ)
    (hb : PureBranch n D b) (hB : Bplus n D = (eligSet n D).card)
    {x : Fin n} {u v : ℕ} (hu : 2 ≤ fanout D u) (hv : 2 ≤ fanout D v)
    (hxu : x ∈ supp n D u) (hxv : x ∈ supp n D v) : u = v := by
  have hs := surplus_carrierT_le hS b hb {x}
  have hc : (({x} : Finset (Fin n)) ∩ eligSet n D).card ≤ 1 :=
    (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
  have hbound : surplusOn D (carrierT n D {x}) ≤ 1 := by omega
  by_contra hne
  have hsub : ({u, v} : Finset ℕ) ⊆ carrierT n D {x} := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact sem_mem_carrier1.mpr hxu
    · exact sem_mem_carrier1.mpr hxv
  have hsum := Finset.sum_le_sum_of_subset (f := fun w => fanout D w - 1) hsub
  rw [Finset.sum_pair hne] at hsum
  change fanout D u - 1 + (fanout D v - 1) ≤ surplusOn D (carrierT n D {x}) at hsum
  omega

lemma h3_sem_tight_fork_routes (hG : sem_Gr G) (h : StrictLive n D)
    (hC : sem_Comp n G D) (hB : Bplus n D = (eligSet n D).card)
    (hM : ∀ x : Fin n, merges n D (carrierT n D {x}) = ∅)
    {x : Fin n} {r : ℕ} (hf : 2 ≤ fanout D r) (hx : x ∈ supp n D r) :
    ∃ P Q : ℕ × Bool, P.1 ≠ Q.1 ∧ P ∈ sem_W n D x ∧ Q ∈ sem_W n D x ∧
      ∃ j1 ∈ readers D r, ∃ j2 ∈ readers D r, j1 ≠ j2 ∧
        ((P.1 = j1 ∧ src D P = r) ∨
          Relation.ReflTransGen (sem_Arm n D {x}) (n + j1) (src D P)) ∧
        ((Q.1 = j2 ∧ src D Q = r) ∨
          Relation.ReflTransGen (sem_Arm n D {x}) (n + j2) (src D Q)) := by
  obtain ⟨b, hb⟩ := sem_exists_pureBranch hG h.1 hC
  obtain ⟨P, Q, hPQ, hmem, hroutes⟩ := h3_sem_two_arms_routed hG h hC
    {x} (by simp) (fun y hy => hM y) r (by simpa using hx) hf (by
      intro y hy w hrw hyw
      have hyx : y = x := Finset.mem_singleton.mp hy
      subst y
      by_contra hw
      have hw2 : 2 ≤ fanout D w := by omega
      have he := h3_tight_carrier_branch_unique h.1 b hb hB hf hw2 hx hyw
      omega)
  exact ⟨P, Q, hPQ, (hmem x (by simp)).1, (hmem x (by simp)).2, hroutes⟩


lemma h3_sem_arm_or (hS : Strict n D) {x : Fin n}
    (hM : merges n D (carrierT n D {x}) = ∅) {a b : ℕ}
    (hab : sem_Arm n D {x} a b) : tag D (b - n) = false := by
  obtain ⟨hb, hnb, _⟩ := hab.1
  have he : n + (b - n) = b := by omega
  apply (sem_zm_gate hS hM (j := b - n) (by omega) ?_).1
  rw [he]
  exact (hab.2.2 x (by simp)).2

lemma h3_sem_route_before (hS : Strict n D) {x : Fin n} {r j : ℕ}
    (hj : j ∈ readers D r) {e : ℕ × Bool} (he : e ∈ sem_W n D x)
    (hp : (e.1 = j ∧ src D e = r) ∨
      Relation.ReflTransGen (sem_Arm n D {x}) (n + j) (src D e)) :
    r < n + e.1 := by
  have hj' := Finset.mem_filter.mp hj
  have hjl : j < D.length := Finset.mem_range.mp hj'.1
  have hS' := hS j hjl
  have hrj : r < n + j := by rcases hj'.2 with hA | hB <;> omega
  rcases hp with ⟨hgate, _⟩ | hp
  · simpa only [hgate] using hrj
  · have hle := sem_rtg_le hS (fun _ _ hab => hab.1) hp
    have hsrc := sem_src_lt hS (sem_mem_W.mp he).1 e.2
    exact lt_trans hrj (lt_of_le_of_lt hle hsrc)

lemma h3_sem_tight_fork_routes_to (hG : sem_Gr G) (h : StrictLive n D)
    (hC : sem_Comp n G D) (hB : Bplus n D = (eligSet n D).card)
    (hM : ∀ x : Fin n, merges n D (carrierT n D {x}) = ∅)
    {x : Fin n} {r : ℕ} (hf : 2 ≤ fanout D r) (hx : x ∈ supp n D r)
    {P Q : ℕ × Bool} (hW : sem_W n D x = {P, Q}) :
    ∃ j1 ∈ readers D r, ∃ j2 ∈ readers D r, j1 ≠ j2 ∧
      ((P.1 = j1 ∧ src D P = r) ∨
        Relation.ReflTransGen (sem_Arm n D {x}) (n + j1) (src D P)) ∧
      ((Q.1 = j2 ∧ src D Q = r) ∨
        Relation.ReflTransGen (sem_Arm n D {x}) (n + j2) (src D Q)) := by
  obtain ⟨P', Q', hne, hP, hQ, j1, hj1, j2, hj2, hjne, hp, hq⟩ :=
    h3_sem_tight_fork_routes hG h hC hB hM hf hx
  rw [hW] at hP hQ
  simp only [Finset.mem_insert, Finset.mem_singleton] at hP hQ
  rcases hP with rfl | rfl <;> rcases hQ with rfl | rfl
  · exact (hne rfl).elim
  · exact ⟨j1, hj1, j2, hj2, hjne, hp, hq⟩
  · exact ⟨j2, hj2, j1, hj1, Ne.symm hjne, hq, hp⟩
  · exact (hne rfl).elim

lemma h3_sem_tight_fork_before_all_exits (hG : sem_Gr G) (h : StrictLive n D)
    (hC : sem_Comp n G D) (hB : Bplus n D = (eligSet n D).card)
    (hM : ∀ x : Fin n, merges n D (carrierT n D {x}) = ∅)
    {x : Fin n} {r : ℕ} (hf : 2 ≤ fanout D r) (hx : x ∈ supp n D r)
    (hc : (sem_W n D x).card ≤ 2) :
    ∀ e ∈ sem_W n D x, r < n + e.1 := by
  obtain ⟨P, Q, hne, hP, hQ, j1, hj1, j2, hj2, hjne, hp, hq⟩ :=
    h3_sem_tight_fork_routes hG h hC hB hM hf hx
  have hPQ : P ≠ Q := fun he => hne (congrArg Prod.fst he)
  have hsub : ({P, Q} : Finset (ℕ × Bool)) ⊆ sem_W n D x := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl <;> assumption
  have heq : ({P, Q} : Finset (ℕ × Bool)) = sem_W n D x :=
    Finset.eq_of_subset_of_card_le hsub (by simpa [Finset.card_pair hPQ] using hc)
  intro e he
  rw [← heq] at he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl
  · exact h3_sem_route_before h.1 hj1 hP hp
  · exact h3_sem_route_before h.1 hj2 hQ hq


def h3_outsideCenterIndex (x : Fin 10) : Fin 10 :=
  if x = 1 then 2 else if x = 4 then 4 else 6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma h3_outside_exit_indices : ∀ x ∈ ({1, 4, 5} : Finset (Fin 10)),
    Finset.univ.filter (fun i : Fin 10 => x ∈ SideGeometry.side i) =
      {1, h3_outsideCenterIndex x} := by
  unfold h3_outsideCenterIndex SideGeometry.side SideGeometry.mask
  decide +kernel

lemma h3_petersen_outside_fork_routes {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hB : Bplus 10 D = (eligSet 10 D).card)
    (r : Fin 10 → ℕ × Bool)
    (hW : ∀ x : Fin 10, exitArcs 10 D (carrierT 10 D {x}) =
      (Finset.univ.filter (fun i : Fin 10 => x ∈ SideGeometry.side i)).image r)
    {x : Fin 10} (hxout : x ∈ ({1, 4, 5} : Finset (Fin 10)))
    {w : ℕ} (hf : 2 ≤ fanout D w) (hx : x ∈ supp 10 D w) :
    ∃ j1 ∈ readers D w, ∃ j2 ∈ readers D w, j1 ≠ j2 ∧
      (((r 1).1 = j1 ∧ src D (r 1) = w) ∨
        Relation.ReflTransGen (sem_Arm 10 D {x}) (10 + j1) (src D (r 1))) ∧
      (((r (h3_outsideCenterIndex x)).1 = j2 ∧ src D (r (h3_outsideCenterIndex x)) = w) ∨
        Relation.ReflTransGen (sem_Arm 10 D {x}) (10 + j2) (src D (r (h3_outsideCenterIndex x)))) := by
  apply h3_sem_tight_fork_routes_to petersen_graph_ok h hC hB
    (petersen_tight_merges_empty h hC hz hB) hf hx
  change exitArcs 10 D (carrierT 10 D {x}) = _
  rw [hW, h3_outside_exit_indices x hxout]
  simp

end H3ForkRouting

end DagTools

namespace DagTools

def h3_linear {n : ℕ} (D : Dag) (x : Fin n → Bool) (w : ℕ) : Bool :=
  decide (∃ v : Fin n, v ∈ supp n D w ∧ x v = true)

def h3_noise {n : ℕ} (D : Dag) (hS : Strict n D) (x : Fin n → Bool) (w : ℕ) : Bool :=
  if _hn : w < n then false else
  if _hj : w - n < D.length then
    if tag D (w - n) then val D x w
    else h3_noise D hS x (opA D (w - n)) || h3_noise D hS x (opB D (w - n))
  else false
termination_by w
decreasing_by
  all_goals
    obtain ⟨ha, hb, _⟩ := hS (w - n) _hj
    omega

lemma h3_linear_le_val {n : ℕ} {D : Dag} (hS : Strict n D) (x : Fin n → Bool) (w : ℕ)
    (hl : h3_linear D x w = true) : val D x w = true := by
  obtain ⟨v, hv, hx⟩ := of_decide_eq_true hl
  exact sem_val_of_supp hS hv hx

lemma h3_noise_input {n : ℕ} {D : Dag} (hS : Strict n D) (x : Fin n → Bool)
    {w : ℕ} (hw : w < n) : h3_noise D hS x w = false := by
  rw [h3_noise]
  simp only [hw, ↓reduceDIte]

lemma h3_noise_gate {n : ℕ} {D : Dag} (hS : Strict n D) (x : Fin n → Bool)
    {j : ℕ} (hj : j < D.length) :
    h3_noise D hS x (n + j) =
      if tag D j then val D x (n + j)
      else h3_noise D hS x (opA D j) || h3_noise D hS x (opB D j) := by
  rw [h3_noise]
  simp only [show ¬n + j < n by omega, ↓reduceDIte, Nat.add_sub_cancel_left, hj]

lemma h3_linear_input {n : ℕ} (D : Dag) (x : Fin n → Bool) (i : Fin n) :
    h3_linear D x i.val = x i := by
  simp [h3_linear, supp_input D i]

lemma h3_linear_or {n : ℕ} {D : Dag} (hS : Strict n D) (x : Fin n → Bool)
    {j : ℕ} (hj : j < D.length) (ht : tag D j = false) :
    h3_linear D x (n + j) = (h3_linear D x (opA D j) || h3_linear D x (opB D j)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [h3_linear, decide_eq_true_eq, Bool.or_eq_true, sem_supp_or hS hj ht,
    Finset.mem_union, or_and_right, exists_or]

lemma h3_noise_decomposition {n : ℕ} {D : Dag} (hS : Strict n D) (x : Fin n → Bool)
    (w : ℕ) : val D x w = (h3_linear D x w || h3_noise D hS x w) := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · rw [val_input D x w hn, h3_noise_input hS x hn]
      have hl := h3_linear_input D x (⟨w, hn⟩ : Fin n)
      simpa only [Bool.or_false] using hl.symm
    · by_cases hlt : w < n + D.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < D.length := by omega
        obtain ⟨ha, hb, _⟩ := hS j hj
        cases ht : tag D j
        · rw [val_gate hS x j hj, ht, gop_false, h3_noise_gate hS x hj, ht]
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [h3_linear_or hS x hj ht, ih _ ha, ih _ hb]
          ac_rfl
        · rw [h3_noise_gate hS x hj, ht]
          simp only [↓reduceIte]
          have hl := h3_linear_le_val hS x (n + j)
          cases he : h3_linear D x (n + j) <;> cases hv : val D x (n + j) <;>
            simp_all
      · have hs : supp n D w = ∅ := by
          apply Finset.eq_empty_of_forall_notMem
          intro v hv
          have := sem_supp_lt hv
          omega
        have hj : ¬ w - n < D.length := by omega
        rw [val_ge D x w (by omega), h3_noise]
        simp only [hn, ↓reduceDIte, hj, h3_linear, hs, Finset.notMem_empty,
          false_and, exists_false, decide_false, Bool.false_or]

def h3_row_left (k : Fin 6) : Fin 10 :=
  ⟨(([2, 3, 7, 2, 2, 3] : List Nat).getD k.val 0) % 10, Nat.mod_lt _ (by decide)⟩

def h3_row_right (k : Fin 6) : Fin 10 :=
  ⟨(([6, 9, 8, 3, 7, 8] : List Nat).getD k.val 0) % 10, Nat.mod_lt _ (by decide)⟩

def h3_row_input (k : Fin 6) : Fin 10 → Bool := sem_two (h3_row_left k) (h3_row_right k)

def h3_side_mask (i : Fin 10) : Nat := ([0, 0, 0, 25, 0, 42, 0, 52, 63, 63] : List Nat).getD i.val 0

lemma h3_sides_linear_table : ∀ (i : Fin 10) (k : Fin 6),
    decide (∃ v : Fin 10, v ∈ SideGeometry.side i ∧ h3_row_input k v = true) =
      (h3_side_mask i).testBit k.val := by
  unfold SideGeometry.side SideGeometry.mask h3_row_input h3_row_left h3_row_right sem_two h3_side_mask
  decide +kernel

lemma h3_six_target_table : ∀ k : Fin 6,
    sem_Edge petersenAdj (h3_row_input k) ↔ (56 : Nat).testBit k.val = true := by
  unfold sem_Edge petersenAdj h3_row_input h3_row_left h3_row_right sem_two
  decide +kernel

lemma h3_six_target_of_computes {D : Dag} (hC : sem_Comp 10 petersenAdj D) (k : Fin 6) :
    val D (h3_row_input k) (outW 10 D) = (56 : Nat).testBit k.val := by
  have hc := (hC (h3_row_input k)).trans (h3_six_target_table k)
  cases hv : val D (h3_row_input k) (outW 10 D) <;>
    cases hb : (56 : Nat).testBit k.val <;> simp_all

lemma h3_six_noise_output {D : Dag} (hS : Strict 10 D)
    (hC : sem_Comp 10 petersenAdj D) (k : Fin 6) :
    h3_noise D hS (h3_row_input k) (outW 10 D) = (56 : Nat).testBit k.val := by
  have hd := h3_noise_decomposition hS (h3_row_input k) (outW 10 D)
  have hl : h3_linear D (h3_row_input k) (outW 10 D) = false := by
    simp [h3_linear, sem_supp_out petersen_graph_ok hC]
  rw [hl, Bool.false_or] at hd
  exact hd.symm.trans (h3_six_target_of_computes hC k)

lemma h3_linear_on_side {D : Dag} {w : ℕ} {i : Fin 10}
    (hs : supp 10 D w = SideGeometry.side i) (k : Fin 6) :
    h3_linear D (h3_row_input k) w = (h3_side_mask i).testBit k.val := by
  simpa only [h3_linear, hs] using h3_sides_linear_table i k

lemma h3_noise_and_sides {D : Dag} (hS : Strict 10 D) {j : ℕ}
    (hj : j < D.length) (ht : tag D j = true) {i : Fin 10}
    (ha : supp 10 D (opA D j) = SideGeometry.side i)
    (hb : supp 10 D (opB D j) = SideGeometry.side (SideGeometry.opposite i)) (k : Fin 6) :
    h3_noise D hS (h3_row_input k) (10 + j) =
      (((h3_side_mask i).testBit k.val || h3_noise D hS (h3_row_input k) (opA D j)) &&
      ((h3_side_mask (SideGeometry.opposite i)).testBit k.val ||
        h3_noise D hS (h3_row_input k) (opB D j))) := by
  rw [h3_noise_gate hS _ hj, ht]
  simp only [↓reduceIte]
  rw [val_gate hS _ j hj, ht, gop_true, h3_noise_decomposition hS _ (opA D j),
    h3_noise_decomposition hS _ (opB D j), h3_linear_on_side ha k, h3_linear_on_side hb k]

lemma h3_noise_and_empty {D : Dag} (hS : Strict 10 D) {j : ℕ}
    (hj : j < D.length) (ht : tag D j = true)
    (ha : supp 10 D (opA D j) = ∅) (hb : supp 10 D (opB D j) = ∅) (x : Fin 10 → Bool) :
    h3_noise D hS x (10 + j) =
      (h3_noise D hS x (opA D j) && h3_noise D hS x (opB D j)) := by
  rw [h3_noise_gate hS x hj, ht]
  simp only [↓reduceIte]
  rw [val_gate hS x j hj, ht, gop_true, h3_noise_decomposition hS x (opA D j),
    h3_noise_decomposition hS x (opB D j)]
  simp [h3_linear, ha, hb]

lemma h3_noise_dirty {D : Dag} (hS : Strict 10 D) {j : ℕ}
    (hj : j < D.length) (ht : tag D j = true)
    (ha : supp 10 D (opA D j) = SideGeometry.side 8)
    (hb : supp 10 D (opB D j) = SideGeometry.side 9) (k : Fin 6) :
    h3_noise D hS (h3_row_input k) (10 + j) = true := by
  have hop : SideGeometry.opposite (8 : Fin 10) = 9 := by decide
  have h := h3_noise_and_sides hS hj ht ha (by rw [hop]; exact hb) k
  have hbits : ∀ a : Fin 6, (63 : Nat).testBit a.val = true := by decide
  have hm8 : h3_side_mask 8 = 63 := by decide
  have hm9 : h3_side_mask 9 = 63 := by decide
  rw [hop, hm8, hm9, hbits k] at h
  simpa only [Bool.true_or, Bool.true_and] using h

lemma h3_noise_before_source {n : ℕ} {D : Dag} (hS : Strict n D) (x : Fin n → Bool)
    (d : ℕ)
    (hsource : ∀ j, j < D.length → j < d → tag D j = true →
      (h3_linear D x (opA D j) && h3_linear D x (opB D j)) = false) :
    ∀ w, w < n + d → h3_noise D hS x w = false := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hwd
    by_cases hn : w < n
    · exact h3_noise_input hS x hn
    · by_cases hlt : w < n + D.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < D.length := by omega
        have hjd : j < d := by omega
        obtain ⟨ha, hb, _⟩ := hS j hj
        have hna := ih _ ha (by omega)
        have hnb := ih _ hb (by omega)
        rw [h3_noise_gate hS x hj]
        cases ht : tag D j
        · simp only [Bool.false_eq_true, ↓reduceIte, hna, hnb, Bool.false_or]
        · simp only [↓reduceIte]
          rw [val_gate hS x j hj, ht, gop_true, h3_noise_decomposition hS x (opA D j),
            h3_noise_decomposition hS x (opB D j), hna, hnb, Bool.or_false, Bool.or_false]
          exact hsource j hj hjd ht
      · have hj : ¬ w - n < D.length := by omega
        rw [h3_noise]
        simp only [hn, ↓reduceDIte, hj]

lemma h3_side_products_zero : ∀ i : Fin 10, i.val < 8 → ∀ k : Fin 6,
    ((h3_side_mask i).testBit k.val &&
      (h3_side_mask (SideGeometry.opposite i)).testBit k.val) = false := by
  unfold h3_side_mask SideGeometry.opposite
  decide +kernel

lemma h3_noise_before_dirty {D : Dag} (hS : Strict 10 D)
    (r : Fin 10 → ℕ × Bool)
    (hopp : ∀ i : Fin 10, r (SideGeometry.opposite i) = ((r i).1, !(r i).2))
    (htypes : ∀ j, j < D.length → tag D j = true →
      (∃ i : Fin 10, r i = (j, false) ∧
        supp 10 D (opA D j) = SideGeometry.side i ∧
        supp 10 D (opB D j) = SideGeometry.side (SideGeometry.opposite i)) ∨
      (supp 10 D (opA D j) = ∅ ∧ supp 10 D (opB D j) = ∅)) (k : Fin 6) :
    ∀ w, w < 10 + (r 8).1 → h3_noise D hS (h3_row_input k) w = false := by
  apply h3_noise_before_source hS (h3_row_input k) (r 8).1
  intro j hj hjd ht
  rcases htypes j hj ht with ⟨i, hi, ha, hb⟩ | ⟨ha, hb⟩
  · have hismall : i.val < 8 := by
      by_contra hn
      have hicases : i = 8 ∨ i = 9 := by omega
      rcases hicases with hi8 | hi9
      · subst i
        have h := congrArg Prod.fst hi
        dsimp only at h
        omega
      · subst i
        have h := congrArg Prod.fst hi
        have hop := congrArg Prod.fst (hopp 8)
        have ho : SideGeometry.opposite (8 : Fin 10) = 9 := by decide
        have h89 : (r 9).1 = (r 8).1 := by simpa only [ho] using hop
        dsimp only at h
        omega
    rw [h3_linear_on_side ha k, h3_linear_on_side hb k]
    exact h3_side_products_zero i hismall k
  · simp [h3_linear, ha, hb]

end DagTools

namespace FiveGroup.CausalBarrier

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

def Step (T : Finset (Fin 10)) (pool : List Wire) (w : Wire) : Prop :=
  ∃ a ∈ pool, ∃ b ∈ pool,
    w = Join a b ∨ (Separates T a.1 b.1 ∧ w = Meet a b)

def Trace (T : Finset (Fin 10)) (pool : List Wire) : List Wire → Prop
  | [] => True
  | w :: ws => Step T pool w ∧ Trace T (w :: pool) ws

lemma safe_step {T : Finset (Fin 10)} {pool : List Wire} {w : Wire}
    (hp : ∀ a ∈ pool, Safe T a) (h : Step T pool w) : Safe T w := by
  rcases h with ⟨a, ha, b, hb, h | ⟨hs, h⟩⟩
  · subst w
    exact safe_join (hp a ha) (hp b hb)
  · subst w
    exact safe_meet (hp a ha) (hp b hb) hs

lemma safe_trace {T : Finset (Fin 10)} {pool ws : List Wire}
    (hp : ∀ a ∈ pool, Safe T a) (h : Trace T pool ws) :
    ∀ w ∈ ws, Safe T w := by
  induction ws generalizing pool with
  | nil => simp
  | cons a ws ih =>
      obtain ⟨hs, ht⟩ := h
      have ha := safe_step hp hs
      have hp' : ∀ b ∈ a :: pool, Safe T b := by
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact ha
        · exact hp b hb
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact ha
      · exact ih hp' ht w hw

lemma safe_zero_false {T : Finset (Fin 10)} {w : Wire}
    (h : Safe T w) (hz : w.1 = ∅) : w.2 = false := by
  cases hv : w.2
  · rfl
  · have hn := h hv
    simp [hz] at hn

def OtherSides : List (Finset (Fin 10) × Finset (Fin 10)) :=
  [({0}, {1, 4, 5}), ({1}, {2, 6}), ({4}, {3, 9}), ({5}, {7, 8}), (∅, ∅)]

def DirtyEdges : List (Finset (Fin 10)) :=
  [{2, 3}, {3, 8}, {6, 8}, {6, 9}, {2, 7}, {7, 9}]

def UniversalEdge (v : Fin 10) : Finset (Fin 10) :=
  match v.val with
  | 0 => {2, 3}
  | 1 => {3, 8}
  | 2 => {2, 3}
  | 3 => {2, 3}
  | 4 => {6, 8}
  | 5 => {6, 9}
  | 6 => {6, 8}
  | 7 => {2, 7}
  | 8 => {3, 8}
  | _ => {6, 9}

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

end FiveGroup.CausalBarrier

namespace FiveGroup.ResourceExclusion

open CausalBarrier

abbrev Resource := Finset (Fin 10) × (Finset (Fin 10) → Bool)

def CrossPairs : List (Finset (Fin 10)) :=
  [{2, 3}, {3, 8}, {3, 9}, {2, 6}, {6, 8}, {6, 9}, {2, 7}, {7, 8}, {7, 9}]

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
  w.1 = ∅ ∧ (∀ E ∈ DirtyEdges, w.2 E = true) ∧ w.2 {3, 9} = false

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
  refine ⟨{2, 3}, by simp [DirtyEdges], {2, 3}, ?_, ?_⟩
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
    have ht := hdt {3, 9} (by simp [CrossPairs])
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

def ResourceTrace (p : Multiset Resource) : List (Multiset Resource) → Prop
  | [] => True
  | q :: qs => ResourceStep p q ∧ ResourceTrace q qs

lemma invariant_trace {p : Multiset Resource} {qs : List (Multiset Resource)}
    (hp : Invariant p) (ht : ResourceTrace p qs) : ∀ q ∈ qs, Invariant q := by
  induction qs generalizing p with
  | nil => simp
  | cons q qs ih =>
      obtain ⟨hs, ht⟩ := ht
      have hq := invariant_step hp hs
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hq
      · exact ih hq ht r hr

lemma canonical_resource_exclusion {d : Resource} {ordinary : Multiset Resource}
    {qs : List (Multiset Resource)} {q : Multiset Resource} {out : Resource}
    (hd : d.1 = ∅) (hdt : ∀ E ∈ CrossPairs, d.2 E = true)
    (ho : AllOrdinary ordinary) (ht : ResourceTrace (d ::ₘ ordinary) qs)
    (hq : q ∈ qs) (hout : out ∈ q) : ¬ Target out := by
  have hi : Invariant (d ::ₘ ordinary) := Or.inr ⟨d, ordinary, rfl, hd, hdt, ho⟩
  exact invariant_no_target (invariant_trace hi ht q hq) hout

end FiveGroup.ResourceExclusion

namespace FiveGroup.IndexSchedule

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

lemma seeded_program_exclusion {W : ℕ → Resource} {start n d : ℕ} {A B : ℕ → ℕ}
    (hd : d < start) (hz : (W d).1 = ∅)
    (ht : ∀ E ∈ CrossPairs, (W d).2 E = true)
    (ho : ∀ i < start, i ≠ d → Ordinary (W i))
    (hv : ValidUpTo start A B n) (hl : LinearUpTo W start A B n)
    (hc : CanonicalUpTo W start A B n) :
    ∀ t < n, ¬ Target (W (start + t)) :=
  canonical_program_exclusion (initial_exceptional hd hz ht ho) hv hl hc


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

end FiveGroup.IndexSchedule
namespace FiveGroup.DAGBridge

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
    · simp only [DagTools.inner, Finset.mem_range]
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

def DirtyA : Finset (Fin 10) := {3, 6, 7}

def DirtyB : Finset (Fin 10) := {2, 8, 9}

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

end FiveGroup.DAGBridge

namespace DagTools

open FiveGroup.CausalBarrier FiveGroup.ResourceExclusion FiveGroup.DAGBridge

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma h3r_other_sides : ∀ i : Fin 10, i ≠ 8 → i ≠ 9 →
    (SideGeometry.side i, SideGeometry.side (SideGeometry.opposite i)) ∈ OtherSides ∨
    (SideGeometry.side (SideGeometry.opposite i), SideGeometry.side i) ∈ OtherSides := by
  unfold SideGeometry.side SideGeometry.mask SideGeometry.opposite OtherSides
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma h3r_dirty_edges : ∀ E ∈ DirtyEdges, sem_Edge petersenAdj (sem_ind E) := by
  unfold DirtyEdges sem_Edge petersenAdj sem_ind
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma h3r_bad_pair : ¬ sem_Edge petersenAdj (sem_ind ({3, 9} : Finset (Fin 10))) := by
  unfold sem_Edge petersenAdj sem_ind
  decide +kernel

lemma h3r_output_target {D : Dag} (hC : sem_Comp 10 petersenAdj D) :
    Target (DagResource D (outW 10 D)) := by
  refine ⟨sem_supp_out petersen_graph_ok hC, ?_, ?_⟩
  · intro E hE
    exact (hC _).mpr (h3r_dirty_edges E hE)
  · apply Bool.eq_false_iff.mpr
    intro ht
    exact h3r_bad_pair ((hC _).mp ht)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma h3_tight_bzero_positive {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hB : Bplus 10 D = (eligSet 10 D).card) : 1 ≤ Bzero 10 D := by
  by_contra hnot
  have hB0 : Bzero 10 D = 0 := by omega
  obtain ⟨r, _, hopp, hsources, hW, hvalid, _, htypes⟩ := h3_tight_typed_sources_exist h hC hz hB
  have hp : r 9 = ((r 8).1, !(r 8).2) := by
    simpa [SideGeometry.opposite] using hopp 8
  have hdirty : DirtySides D (r 8).1 := by
    have h8 := hsources 8
    have h9 := hsources 9
    have h8S : SideGeometry.side 8 = DirtyA := by decide +kernel
    have h9S : SideGeometry.side 9 = DirtyB := by decide +kernel
    rw [h8S] at h8
    rw [h9S] at h9
    cases hb : (r 8).2
    · left
      exact ⟨by simpa [src, hb] using h8, by simpa [hp, src, hb] using h9⟩
    · right
      exact ⟨by simpa [hp, src, hb] using h9, by simpa [src, hb] using h8⟩
  have hother : OtherAndSides D (r 8).1 := by
    intro j hj hne ht
    rcases htypes j hj ht with ⟨i, hi, hA, hB⟩ | ⟨hA, hB⟩
    · have hi8 : i ≠ 8 := by
        intro hi8
        subst i
        exact hne (congrArg Prod.fst hi).symm
      have hi9 : i ≠ 9 := by
        intro hi9
        subst i
        have hh := congrArg Prod.fst hi
        rw [hp] at hh
        exact hne hh.symm
      change (supp 10 D (opA D j), supp 10 D (opB D j)) ∈ OtherSides ∨
        (supp 10 D (opB D j), supp 10 D (opA D j)) ∈ OtherSides
      rw [hA, hB]
      exact h3r_other_sides i hi8 hi9
    · change (supp 10 D (opA D j), supp 10 D (opB D j)) ∈ OtherSides ∨
        (supp 10 D (opB D j), supp 10 D (opA D j)) ∈ OtherSides
      simp [hA, hB, OtherSides]
  exact canonical_dag_exclusion h.1 hB0 (hvalid 8).1 (hvalid 8).2.1 hdirty hother
    (outW 10 D) (by unfold outW; omega) (h3r_output_target hC)

lemma h3_tight_size19 {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hB : Bplus 10 D = (eligSet 10 D).card) (hs : D.length ≤ 19) :
    Bplus 10 D = 9 ∧ Bzero 10 D = 1 ∧ D.length = 19 := by
  obtain ⟨hp, hzle, hlo⟩ := h3_tight_size_budget h hC hz hB hs
  have hzpos := h3_tight_bzero_positive h hC hz hB
  have ht := surplus_identity h
  rw [totalSurplus_split] at ht
  omega

lemma h3_exact_i1_budget_cases {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hi : (ineligSet 10 D).card = 1) (hs : D.length ≤ 19) :
    D.length = 19 ∧
      ((Bplus 10 D = 9 ∧ Bzero 10 D = 1) ∨
       (Bplus 10 D = 10 ∧ Bzero 10 D = 0)) := by
  have hc := inelig_card_add 10 D
  obtain ⟨b, hb⟩ := sem_exists_pureBranch petersen_graph_ok h.1 hC
  have hplo := elig_le_Bplus h.1 b hb
  have ht := surplus_identity h
  rw [totalSurplus_split] at ht
  by_cases hB : Bplus 10 D = (eligSet 10 D).card
  · obtain ⟨hp, hz, hn⟩ := h3_tight_size19 h hC hz hB hs
    exact ⟨hn, Or.inl ⟨hp, hz⟩⟩
  · have hp : Bplus 10 D = 10 := by omega
    exact ⟨by omega, Or.inr ⟨hp, by omega⟩⟩

end DagTools

def tokenPack (a s : List Nat) (f p : Nat) (z b : Bool) : Nat :=
  let c := a.filter (fun x => x != 0)
  if 2 < c.length then 281474976710656 else
  let x := c.getD 0 0
  let y := c.getD 1 0
  let lo := if y = 0 then x else min x y
  let hi := if y = 0 then 0 else max x y
  lo + 64 * hi + 4096 * s.getD 0 0 + 524288 * s.getD 1 0 +
    67108864 * s.getD 2 0 + 8589934592 * f + 549755813888 * p +
    70368744177664 * (if z then 1 else 0) + 140737488355328 * (if b then 1 else 0)

def tokenActive (t : Nat) : List Nat := [t % 64, t / 64 % 64].filter (fun x => x != 0)

def tokenSeeds (t : Nat) : List Nat :=
  [t / 4096 % 128, t / 524288 % 128, t / 67108864 % 128]

def tokenNext (t : Nat) : List Nat :=
  let a := tokenActive t
  let s := tokenSeeds t
  let f := t / 8589934592 % 64
  let p := t / 549755813888 % 128
  let z := decide (t / 70368744177664 % 2 = 1)
  let b := decide (t / 140737488355328 % 2 = 1)
  let drop := (List.range a.length).map (fun i =>
    tokenPack (a.eraseIdx i) s f p z b)
  let zeroStar := if z then [] else [tokenPack a s 0 0 true b]
  let merge := if a.length = 2 then
    [tokenPack [a.getD 0 0 ||| a.getD 1 0] s f p z b,
     tokenPack [a.getD 0 0 &&& a.getD 1 0] s f p z b] else []
  let fork := if b then [] else (List.range a.length).map (fun i =>
    tokenPack (a.eraseIdx i ++ [a.getD i 0, a.getD i 0]) s f p z true)
  let move := (List.range a.length).flatMap (fun i =>
    let x := a.getD i 0
    let rest := a.eraseIdx i
    let branches := (List.range 3).flatMap (fun v =>
      let q := s.getD v 0
      if q = 0 then
        [tokenPack rest (s.set v (x + 1)) f p z b] ++
        (if z then [] else [tokenPack rest (s.set v (x + 1)) (f ||| x) p z b])
      else if 2 ≤ q then
        let seeds := s.set v (((q - 1) ||| x) + 1)
        [tokenPack rest seeds f p z b] ++
        (if z then [] else [tokenPack rest seeds (f ||| x) p z b])
      else [])
    let pool := if z then [] else
      [tokenPack rest s f (if p = 0 then x + 1 else (((p - 1) ||| x) + 1)) z b,
       tokenPack (rest ++ [x &&& (f ||| (if p = 0 then 0 else p - 1))]) s 0 0 true b]
    branches ++ pool)
  let finish := (List.range 3).flatMap (fun v =>
    let q := s.getD v 0
    if 2 ≤ q then
      let x := q - 1
      let seeds := s.set v 1
      let k := ([25, 42, 52] : List Nat).getD v 0
      [tokenPack (a ++ [x &&& k]) seeds f p z b] ++
        (List.range a.length).map (fun i =>
          tokenPack (a.eraseIdx i ++ [x &&& (k ||| a.getD i 0)]) seeds f p z b)
    else [])
  drop ++ zeroStar ++ merge ++ fork ++ move ++ finish

def tokenTreeValues : BinaryTree Nat → List Nat
  | .nil => []
  | .node v l r => tokenTreeValues l ++ v :: tokenTreeValues r

def tokenTreeLookup (x : Nat) : BinaryTree Nat → Bool
  | .nil => false
  | .node v l r => if x < v then tokenTreeLookup x l else
      if x = v then true else tokenTreeLookup x r

lemma token_tree_lookup_sound (t : BinaryTree Nat) {x : Nat}
    (h : tokenTreeLookup x t = true) : x ∈ tokenTreeValues t := by
  induction t with
  | nil => exact False.elim (Bool.false_ne_true h)
  | node v l r ihl ihr =>
    change x ∈ tokenTreeValues l ++ v :: tokenTreeValues r
    by_cases hlt : x < v
    · have hl : tokenTreeLookup x l = true := by
        simpa only [tokenTreeLookup, hlt, ite_true] using h
      exact List.mem_append.mpr (Or.inl (ihl hl))
    · by_cases heq : x = v
      · exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl heq)))
      · have hr : tokenTreeLookup x r = true := by
          simpa only [tokenTreeLookup, hlt, heq, ite_false] using h
        exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr (ihr hr))))

def tokenChunk0 : List Nat :=
  [0,
   63,
   4096,
   4121,
   262144,
   524288,
   524330,
   528384,
   528392,
   700416,
   13635584,
   33554432,
   67108864,
   67108916,
   67112960,
   67112976,
   67325952,
   67633152,
   67633184,
   67637248,
   67768320,
   76025856,
   94896128,
   604508160,
   1744834560,
   2886205440,
   4294967296,
   68787113984,
   69323984896,
   137506590720,
   137514979328,
   214748893184,
   214748893192,
   214762000384,
   214815477760,
   214815477776,
   214816002048,
   214824390656,
   215352872960,
   216493199360,
   274945544192,
   274945675264,
   360777781248,
   360777781256,
   360777953280,
   360844886016,
   360844886048,
   360844890112,
   360845021184,
   361381761024,
   363663458304,
   446743711744,
   446743711760,
   446743924736,
   446744231936,
   446744231968,
   446744236032,
   446744367104,
   446752624640,
   446771494912,
   541165883392,
   541165883417,
   541166141440,
   541166403584]

def tokenChunk1 : List Nat :=
  [541166403626,
   541166407680,
   541166407688,
   541166579712,
   541179514880,
   541199433728,
   541232988160,
   541232988212,
   541232992256,
   541232992272,
   541233205248,
   541233512448,
   541233512480,
   541233516544,
   541233647616,
   541241905152,
   541260775424,
   541770387456,
   542910713856,
   544052084736,
   545460846592,
   4947802853376,
   5162551218176,
   5308580106240,
   5488968732672,
   9345915949056,
   9560664313856,
   9792592547840,
   9887081828352,
   14293651165184,
   14834817044480,
   18142009491456,
   18502786744320,
   18588686090240,
   18683175370752,
   23639500521472,
   24180666400768,
   29137125244928,
   29678291124224,
   35184372088832,
   70368744177664,
   70368744177727,
   70368744181760,
   70368744181785,
   70368744439808,
   70368744701952,
   70368744701994,
   70368744706048,
   70368744706056,
   70368744878080,
   70368757813248,
   70368777732096,
   70368811286528,
   70368811286580,
   70368811290624,
   70368811290640,
   70368811503616,
   70368811810816,
   70368811810848,
   70368811814912,
   70368811945984,
   70368820203520,
   70368839073792,
   70369348685824]

def tokenChunk2 : List Nat :=
  [70370489012224,
   70371630383104,
   70373039144960,
   140737488355328,
   140737488355391,
   140737488359423,
   140737488359424,
   140737488359449,
   140737488359487,
   140737488361049,
   140737488363481,
   140737488617472,
   140737488617535,
   140737488879616,
   140737488879658,
   140737488879679,
   140737488882346,
   140737488883690,
   140737488883712,
   140737488883720,
   140737488883737,
   140737488883754,
   140737488883771,
   140737488883775,
   140737488884232,
   140737488885320,
   140737488886408,
   140737488886425,
   140737488887752,
   140737489055744,
   140737489055786,
   140737489055807,
   140737489141760,
   140737489141802,
   140737501990912,
   140737501990937,
   140737501990975,
   140737521909760,
   140737521909823,
   140737521913856,
   140737521913881,
   140737522171904,
   140737555464192,
   140737555464244,
   140737555464255,
   140737555467572,
   140737555468276,
   140737555468288,
   140737555468304,
   140737555468313,
   140737555468340,
   140737555468349,
   140737555468351,
   140737555469328,
   140737555469904,
   140737555471632,
   140737555471641,
   140737555472336,
   140737555681280,
   140737555681332,
   140737555681343,
   140737555726336,
   140737555726388,
   140737555988480]

def tokenChunk3 : List Nat :=
  [140737555988512,
   140737555988522,
   140737555988532,
   140737555988542,
   140737555988543,
   140737555990560,
   140737555991200,
   140737555991840,
   140737555991850,
   140737555992544,
   140737555992576,
   140737555992584,
   140737555992592,
   140737555992600,
   140737555992601,
   140737555992608,
   140737555992616,
   140737555992618,
   140737555992624,
   140737555992628,
   140737555992633,
   140737555992634,
   140737555992636,
   140737555992639,
   140737555993608,
   140737555994632,
   140737555994640,
   140737555994649,
   140737555995280,
   140737555995912,
   140737556123648,
   140737556123680,
   140737556123690,
   140737556123700,
   140737556123711,
   140737556164608,
   140737556164640,
   140737556164660,
   140737556205568,
   140737556205600,
   140737556205610,
   140737556246528,
   140737556250624,
   140737556250656,
   140737564381184,
   140737564381200,
   140737564381209,
   140737564381236,
   140737564381247,
   140737569099776,
   140737569099792,
   140737569099828,
   140737583251456,
   140737583251508,
   140737583251519,
   140737583255552,
   140737583255568,
   140737583255577,
   140737583468544,
   140737583513600,
   140737587974144,
   140737589018624,
   140737589018676,
   140737589022720]

def tokenChunk4 : List Nat :=
  [140737589022736,
   140737589235712,
   140738092863488,
   140738092863496,
   140738092863513,
   140738092863530,
   140738092863551,
   140739233189888,
   140739233189913,
   140739233189951,
   140739233714176,
   140739233714184,
   140739233714218,
   140739246821376,
   140739266744320,
   140740374560768,
   140740374560810,
   140740374560831,
   140740374564864,
   140740374564872,
   140740374564889,
   140740374736896,
   140740374822912,
   140741515415552,
   140741783322624,
   140741783322687,
   140741783326720,
   140741783326745,
   140741783584768,
   140741783846912,
   140741783846954,
   140741783851008,
   140741783851016,
   140741784023040,
   140741796958208,
   140741816877056,
   140806275469312,
   140806275469320,
   140806275469328,
   140806275469337,
   140806275469344,
   140806275469354,
   140806275469364,
   140806275469375,
   140806812340224,
   140806812340232,
   140806812340249,
   140806812340266,
   140806812340287,
   140807953190912,
   140809094041600,
   140810503327744,
   140874994946048,
   140874994946056,
   140874994946064,
   140874994946073,
   140874994946080,
   140874994946090,
   140874994946100,
   140874994946111,
   140875003334656,
   140875003334672,
   140875003334681,
   140875003334708]

def tokenChunk5 : List Nat :=
  [140875003334719,
   140875008053248,
   140875022209024,
   140875027976192,
   140952237248512,
   140952237248520,
   140952237248537,
   140952237248554,
   140952237248575,
   140952237249032,
   140952237250120,
   140952237252552,
   140952250355712,
   140952250355737,
   140952250355775,
   140952270278656,
   140952303833088,
   140952303833104,
   140952303833113,
   140952303833140,
   140952303833151,
   140952303834128,
   140952303834704,
   140952303837136,
   140952304357376,
   140952304357384,
   140952304357392,
   140952304357400,
   140952304357401,
   140952304357408,
   140952304357416,
   140952304357418,
   140952304357424,
   140952304357428,
   140952304357434,
   140952304357436,
   140952304357439,
   140952304358408,
   140952304360080,
   140952304360712,
   140952312745984,
   140952312746000,
   140952312746009,
   140952312746047,
   140952317464576,
   140952317464592,
   140952317464628,
   140952331620352,
   140952336338944,
   140952337387520,
   140952337387536,
   140952841228288,
   140952841228296,
   140952841228313,
   140952841228351,
   140953981554688,
   140953981554713,
   140953981554751,
   140953982078976,
   140953982078984,
   140953982079018,
   140953995186176,
   140954015109120,
   140955122929664]

def tokenChunk6 : List Nat :=
  [140956263780352,
   140956531691520,
   140956532215808,
   140956532215816,
   140956545323008,
   141012433899520,
   141012433899528,
   141012433899536,
   141012433899545,
   141012433899552,
   141012433899562,
   141012433899572,
   141012433899583,
   141012434030592,
   141012434030624,
   141012434030634,
   141012434030644,
   141012434030655,
   141012434071552,
   141012434112512,
   141012434157568,
   141098266136576,
   141098266136584,
   141098266136601,
   141098266136618,
   141098266136639,
   141098266137096,
   141098266139272,
   141098266140616,
   141098266308608,
   141098266308650,
   141098266308671,
   141098266394624,
   141098333241344,
   141098333241376,
   141098333241386,
   141098333241396,
   141098333241407,
   141098333243424,
   141098333244064,
   141098333245408,
   141098333245440,
   141098333245448,
   141098333245456,
   141098333245464,
   141098333245465,
   141098333245472,
   141098333245480,
   141098333245482,
   141098333245488,
   141098333245492,
   141098333245497,
   141098333245500,
   141098333245503,
   141098333247496,
   141098333247513,
   141098333248776,
   141098333376512,
   141098333376544,
   141098333376554,
   141098333376575,
   141098333417472,
   141098333417504,
   141098333417524]

def tokenChunk7 : List Nat :=
  [141098333458432,
   141098333499392,
   141098333503488,
   141098333503520,
   141098870116352,
   141098870116360,
   141098870116394,
   141098870116415,
   141100010967040,
   141101151813632,
   141101151813674,
   141101151813695,
   141101151817728,
   141101151817736,
   141101151817753,
   141101151989760,
   141101152075776,
   141102292668416,
   141102561099776,
   141102561103872,
   141102561103880,
   141102561275904,
   141184232067072,
   141184232067088,
   141184232067097,
   141184232067124,
   141184232067135,
   141184232068112,
   141184232070416,
   141184232071120,
   141184232280064,
   141184232280116,
   141184232280127,
   141184232325120,
   141184232587264,
   141184232587296,
   141184232587306,
   141184232587316,
   141184232587327,
   141184232589344,
   141184232590624,
   141184232591328,
   141184232591360,
   141184232591368,
   141184232591376,
   141184232591384,
   141184232591385,
   141184232591392,
   141184232591400,
   141184232591402,
   141184232591408,
   141184232591412,
   141184232591417,
   141184232591418,
   141184232591423,
   141184232593424,
   141184232593433,
   141184232594064,
   141184232722432,
   141184232722464,
   141184232722484,
   141184232722495,
   141184232763392,
   141184232804352]

def tokenChunk8 : List Nat :=
  [141184232804384,
   141184232804394,
   141184232845312,
   141184232849408,
   141184232849440,
   141184240979968,
   141184240979984,
   141184240980020,
   141184240980031,
   141184245698560,
   141184259850240,
   141184259850292,
   141184259850303,
   141184259854336,
   141184259854352,
   141184259854361,
   141184260067328,
   141184260112384,
   141184264572928,
   141184265617408,
   141184265621504,
   141184265621520,
   141184265834496,
   141244362133504,
   141244362133520,
   141244362133536,
   141244362133552,
   141246039855104,
   141247180705792,
   141248321556480,
   141261542002688,
   141261542002696,
   141261542002720,
   141261542002728,
   141261555109888,
   141261569265664,
   141261573984256,
   141270131937280,
   141270131937288,
   141270131937296,
   141270131937304,
   141270132109312,
   141270132150272,
   141270132191232,
   141278654238720,
   141278654238745,
   141278654238783,
   141278654240345,
   141278654242777,
   141278654496768,
   141278654496831,
   141278654758912,
   141278654758954,
   141278654758975,
   141278654761642,
   141278654762986,
   141278654763008,
   141278654763016,
   141278654763033,
   141278654763050,
   141278654763067,
   141278654763071,
   141278654763528,
   141278654764616]

def tokenChunk9 : List Nat :=
  [141278654765704,
   141278654765721,
   141278654767048,
   141278654935040,
   141278654935082,
   141278654935103,
   141278655021056,
   141278655021098,
   141278667870208,
   141278667870233,
   141278667870271,
   141278687789056,
   141278687789119,
   141278687793152,
   141278687793177,
   141278688051200,
   141278721343488,
   141278721343540,
   141278721343551,
   141278721346868,
   141278721347572,
   141278721347584,
   141278721347600,
   141278721347609,
   141278721347636,
   141278721347645,
   141278721347647,
   141278721348624,
   141278721349200,
   141278721350928,
   141278721350937,
   141278721351632,
   141278721560576,
   141278721560628,
   141278721560639,
   141278721605632,
   141278721605684,
   141278721867776,
   141278721867808,
   141278721867818,
   141278721867828,
   141278721867838,
   141278721867839,
   141278721869856,
   141278721870496,
   141278721871136,
   141278721871146,
   141278721871840,
   141278721871872,
   141278721871880,
   141278721871888,
   141278721871896,
   141278721871897,
   141278721871904,
   141278721871912,
   141278721871914,
   141278721871920,
   141278721871924,
   141278721871929,
   141278721871930,
   141278721871932,
   141278721871935,
   141278721872904,
   141278721873928]

def tokenChunk10 : List Nat :=
  [141278721873936,
   141278721873945,
   141278721874576,
   141278721875208,
   141278722002944,
   141278722002976,
   141278722002986,
   141278722002996,
   141278722003007,
   141278722043904,
   141278722043936,
   141278722043956,
   141278722084864,
   141278722084896,
   141278722084906,
   141278722125824,
   141278722129920,
   141278722129952,
   141278730260480,
   141278730260496,
   141278730260505,
   141278730260532,
   141278730260543,
   141278734979072,
   141278734979088,
   141278734979124,
   141278749130752,
   141278749130804,
   141278749130815,
   141278749134848,
   141278749134864,
   141278749134873,
   141278749347840,
   141278749392896,
   141278753853440,
   141278754897920,
   141278754897972,
   141278754902016,
   141278754902032,
   141278755115008,
   141279258742784,
   141279258742792,
   141279258742809,
   141279258742826,
   141279258742847,
   141280399069184,
   141280399069209,
   141280399069247,
   141280399593472,
   141280399593480,
   141280399593514,
   141280412700672,
   141280432623616,
   141281540440064,
   141281540440106,
   141281540440127,
   141281540444160,
   141281540444168,
   141281540444185,
   141281540616192,
   141281540702208,
   141282681294848,
   141282949201920,
   141282949201983]

def tokenChunk11 : List Nat :=
  [141282949206016,
   141282949206041,
   141282949464064,
   141282949726208,
   141282949726250,
   141282949730304,
   141282949730312,
   141282949902336,
   141282962837504,
   141282982756352,
   145685291208704,
   145685291208712,
   145685291208729,
   145685291208746,
   145685291208767,
   145685358317568,
   145685358317584,
   145685358317600,
   145685358317620,
   145685895188480,
   145687036039168,
   145688176889856,
   145689586176000,
   145754077794304,
   145754614665216,
   145822797271040,
   145900039573504,
   145900039573512,
   145900039573529,
   145900039573567,
   145900106682368,
   145900106682384,
   145900106682420,
   145900643553280,
   145901784403968,
   145904334540800,
   145960236224512,
   146046068461568,
   146046068461576,
   146046068461610,
   146046068461631,
   146046135570432,
   146046135570464,
   146046135570484,
   146046672441344,
   146048954142720,
   146050363428864,
   146132034916352,
   146209344327680,
   146217934262272,
   146226457088000,
   146226457088008,
   146226457088025,
   146226457088042,
   146226457088063,
   146226524196864,
   146226524196880,
   146226524196896,
   146226524196916,
   146227061067776,
   146228201918464,
   146229342769152,
   146230752055296,
   150083404304384]

def tokenChunk12 : List Nat :=
  [150083404304400,
   150083404304409,
   150083404304436,
   150083404304447,
   150083404828672,
   150083404828680,
   150083404828704,
   150083404828714,
   150083413217280,
   150083417935872,
   150083432091648,
   150083437858816,
   150152124305408,
   150220843782144,
   150220852170752,
   150298152669184,
   150298152669200,
   150298152669209,
   150298152669247,
   150298153193472,
   150298153193480,
   150298153193514,
   150298161582080,
   150298166300672,
   150298186223616,
   150358282735616,
   150444182081536,
   150530080903168,
   150530080903184,
   150530080903220,
   150530080903231,
   150530081427456,
   150530081427488,
   150530081427498,
   150530089816064,
   150530108690432,
   150530114457600,
   150590210969600,
   150615980773376,
   150624570183680,
   150624570183696,
   150624570183705,
   150624570183732,
   150624570183743,
   150624570707968,
   150624570707976,
   150624570708000,
   150624570708010,
   150624579096576,
   150624583815168,
   150624597970944,
   150624603738112,
   154481451339776,
   154696199704576,
   154842228592640,
   154928127938560,
   155014027284480,
   155022617219072,
   155031139520512,
   155031139520537,
   155031139520575,
   155031140044800,
   155031140044808,
   155031140044842]

def tokenChunk13 : List Nat :=
  [155031153152000,
   155031173074944,
   155031206629376,
   155031206629392,
   155031206629428,
   155031207153664,
   155031207153696,
   155031215542272,
   155031234416640,
   155031744024576,
   155032884350976,
   155034025725952,
   155035434487808,
   155099926630400,
   155100463501312,
   155168646107136,
   155168654495744,
   155245888409600,
   155245888409608,
   155245901516800,
   155245954994176,
   155245954994192,
   155245955518464,
   155245963907072,
   155246492389376,
   155247632715776,
   155306085060608,
   155391917297664,
   155391984406528,
   155391984406560,
   155394802978816,
   155477883228160,
   155477883752448,
   155477883752480,
   155477911015424,
   155572305399808,
   155572305399833,
   155572305399871,
   155572305924096,
   155572305924104,
   155572305924138,
   155572319031296,
   155572338954240,
   155572372508672,
   155572372508688,
   155572372508724,
   155572373032960,
   155572373032992,
   155572381421568,
   155572400295936,
   155572909903872,
   155574050230272,
   155575191605248,
   155576600367104,
   158879497846784,
   158879497846816,
   158879497846826,
   158879497846836,
   158879497846847,
   158879497850880,
   158879497850888,
   158879497850896,
   158879497850905,
   158879497981952]

def tokenChunk14 : List Nat :=
  [158879498022912,
   158879498063872,
   158879498108928,
   158948217327616,
   159016936804352,
   159094246215680,
   159154375757824,
   159154375888896,
   159240275099648,
   159240275099680,
   159240275099690,
   159240275099711,
   159240275103744,
   159240275103752,
   159240275103769,
   159240275234816,
   159240275275776,
   159240275361792,
   159326174445568,
   159326174445600,
   159326174445620,
   159326174445631,
   159326174449664,
   159326174449680,
   159326174449689,
   159326174580736,
   159326174662656,
   159326174707712,
   159386303991808,
   159403483860992,
   159420663726080,
   159420663726112,
   159420663726122,
   159420663726132,
   159420663726143,
   159420663730176,
   159420663730184,
   159420663730192,
   159420663730201,
   159420663861248,
   159420663902208,
   159420663943168,
   159420663988224,
   163277544361984,
   163492292726784,
   163638321614848,
   163724220960768,
   163801530372096,
   163818710241280,
   164376988876800,
   164376988876842,
   164376988876863,
   164376988880896,
   164376988880904,
   164376988880921,
   164376989052928,
   164376989138944,
   164377055985664,
   164377055985696,
   164377055985716,
   164377055989760,
   164377055989776,
   164377056120832,
   164377056202752]

def tokenChunk15 : List Nat :=
  [164377592860672,
   164378733711360,
   164379874557952,
   164381283844096,
   164445775466496,
   164446312337408,
   164514494943232,
   164591737245696,
   164591804354560,
   164591804354576,
   164593482076160,
   164651933896704,
   164651934027776,
   164737766133760,
   164737766133768,
   164737766305792,
   164737833238528,
   164737833238560,
   164737833242624,
   164737833373696,
   164738370113536,
   164740651810816,
   164823732584448,
   164823732588544,
   164823732588560,
   164823732801536,
   164918154756096,
   164918154756138,
   164918154756159,
   164918154760192,
   164918154760200,
   164918154760217,
   164918154932224,
   164918155018240,
   164918221864960,
   164918221864992,
   164918221865012,
   164918221869056,
   164918221869072,
   164918222000128,
   164918222082048,
   164918758739968,
   164919899590656,
   164921040437248,
   164922449723392,
   167675590873088,
   167890339237888,
   168036368125952,
   168122267471872,
   168182397014016,
   168216756752384,
   169874613600256,
   169874613600308,
   169874613600319,
   169874613604352,
   169874613604368,
   169874613604377,
   169874613817344,
   169874613862400,
   169874614124544,
   169874614124576,
   169874614124586,
   169874614128640,
   169874614128648]

def tokenChunk16 : List Nat :=
  [169874614259712,
   169874614300672,
   169874622517248,
   169874627235840,
   169874641387520,
   169874647154688,
   169943333605376,
   170012053082112,
   170012061470720,
   170089361969152,
   170089362493440,
   170089362493448,
   170089375600640,
   170149492035584,
   170149492166656,
   170235391377408,
   170235391381504,
   170235391381512,
   170235391553536,
   170321290203136,
   170321290203152,
   170321290416128,
   170321290723328,
   170321290723360,
   170321290727424,
   170321290858496,
   170321299116032,
   170321317986304,
   170415779479552,
   170415779479604,
   170415779479615,
   170415779483648,
   170415779483664,
   170415779483673,
   170415779696640,
   170415779741696,
   170415780003840,
   170415780003872,
   170415780003882,
   170415780007936,
   170415780007944,
   170415780139008,
   170415780179968,
   170415788396544,
   170415793115136,
   170415807266816,
   170415813033984,
   172623393198080,
   172984170450944,
   173070069796864,
   173164559077376,
   173173149011968,
   173387897376768,
   173619825610752,
   173714314891264,
   173722837716992,
   174264003596288,
   174272660639744,
   174487409004544,
   174633437892608,
   174813826519040,
   174822415929344,
   175363581808640,
   175372172263424]

def tokenChunk17 : List Nat :=
  [175913338142720,
   175921860444160,
   175921860444223,
   175921860448256,
   175921860448281,
   175921860706304,
   175921860968448,
   175921860968490,
   175921860972544,
   175921860972552,
   175921861144576,
   175921874079744,
   175921893998592,
   175921927553024,
   175921927553076,
   175921927557120,
   175921927557136,
   175921927770112,
   175921928077312,
   175921928077344,
   175921928081408,
   175921928212480,
   175921936470016,
   175921955340288,
   175922464952320,
   175923605278720,
   175924746649600,
   175926155411456,
   175990647558144,
   175991184429056,
   176059367034880,
   176059375423488,
   176136609337344,
   176136609337352,
   176136622444544,
   176136675921920,
   176136675921936,
   176136676446208,
   176136684834816,
   176137213317120,
   176138353643520,
   176196805988352,
   176196806119424,
   176282638225408,
   176282638225416,
   176282638397440,
   176282705330176,
   176282705330208,
   176282705334272,
   176282705465344,
   176283242205184,
   176285523902464,
   176368604155904,
   176368604155920,
   176368604368896,
   176368604676096,
   176368604676128,
   176368604680192,
   176368604811264,
   176368613068800,
   176368631939072,
   176463026327552,
   176463026327577,
   176463026585600]

def tokenChunk18 : List Nat :=
  [176463026847744,
   176463026847786,
   176463026851840,
   176463026851848,
   176463027023872,
   176463039959040,
   176463059877888,
   176463093432320,
   176463093432372,
   176463093436416,
   176463093436432,
   176463093649408,
   176463093956608,
   176463093956640,
   176463093960704,
   176463094091776,
   176463102349312,
   176463121219584,
   176463630831616,
   176464771158016,
   176465912528896,
   176467321290752,
   211106232532992,
   211106232533055,
   211106232537087,
   211106232537088,
   211106232537113,
   211106232537151,
   211106232538713,
   211106232541145,
   211106232795136,
   211106232795199,
   211106233057280,
   211106233057322,
   211106233057343,
   211106233060010,
   211106233061354,
   211106233061376,
   211106233061384,
   211106233061401,
   211106233061418,
   211106233061435,
   211106233061439,
   211106233061896,
   211106233062984,
   211106233064072,
   211106233064089,
   211106233065416,
   211106233233408,
   211106233233450,
   211106233233471,
   211106233319424,
   211106233319466,
   211106246168576,
   211106246168601,
   211106246168639,
   211106266087424,
   211106266087487,
   211106266091520,
   211106266091545,
   211106266349568,
   211106299641856,
   211106299641908,
   211106299641919]

def tokenChunk19 : List Nat :=
  [211106299645236,
   211106299645940,
   211106299645952,
   211106299645968,
   211106299645977,
   211106299646004,
   211106299646013,
   211106299646015,
   211106299646992,
   211106299647568,
   211106299649296,
   211106299649305,
   211106299650000,
   211106299858944,
   211106299858996,
   211106299859007,
   211106299904000,
   211106299904052,
   211106300166144,
   211106300166176,
   211106300166186,
   211106300166196,
   211106300166206,
   211106300166207,
   211106300168224,
   211106300168864,
   211106300169504,
   211106300169514,
   211106300170208,
   211106300170240,
   211106300170248,
   211106300170256,
   211106300170264,
   211106300170265,
   211106300170272,
   211106300170280,
   211106300170282,
   211106300170288,
   211106300170292,
   211106300170297,
   211106300170298,
   211106300170300,
   211106300170303,
   211106300171272,
   211106300172296,
   211106300172304,
   211106300172313,
   211106300172944,
   211106300173576,
   211106300301312,
   211106300301344,
   211106300301354,
   211106300301364,
   211106300301375,
   211106300342272,
   211106300342304,
   211106300342324,
   211106300383232,
   211106300383264,
   211106300383274,
   211106300424192,
   211106300428288,
   211106300428320,
   211106308558848]

def tokenChunk20 : List Nat :=
  [211106308558864,
   211106308558873,
   211106308558900,
   211106308558911,
   211106313277440,
   211106313277456,
   211106313277492,
   211106327429120,
   211106327429172,
   211106327429183,
   211106327433216,
   211106327433232,
   211106327433241,
   211106327646208,
   211106327691264,
   211106332151808,
   211106333196288,
   211106333196340,
   211106333200384,
   211106333200400,
   211106333413376,
   211106837041152,
   211106837041160,
   211106837041177,
   211106837041194,
   211106837041215,
   211107977367552,
   211107977367577,
   211107977367615,
   211107977891840,
   211107977891848,
   211107977891882,
   211107990999040,
   211108010921984,
   211109118738432,
   211109118738474,
   211109118738495,
   211109118742528,
   211109118742536,
   211109118742553,
   211109118914560,
   211109119000576,
   211110259593216,
   211110527500288,
   211110527500351,
   211110527504384,
   211110527504409,
   211110527762432,
   211110528024576,
   211110528024618,
   211110528028672,
   211110528028680,
   211110528200704,
   211110541135872,
   211110561054720]

def tokenCodes : List Nat :=
  tokenChunk0 ++ tokenChunk1 ++ tokenChunk2 ++ tokenChunk3 ++ tokenChunk4 ++ tokenChunk5 ++ tokenChunk6 ++ tokenChunk7 ++ tokenChunk8 ++ tokenChunk9 ++ tokenChunk10 ++ tokenChunk11 ++ tokenChunk12 ++ tokenChunk13 ++ tokenChunk14 ++ tokenChunk15 ++ tokenChunk16 ++ tokenChunk17 ++ tokenChunk18 ++ tokenChunk19 ++ tokenChunk20

def tokenTree : BinaryTree Nat :=
  (.node 141278749130804
    (.node 140952250355737
      (.node 140737521909823
        (.node 544052084736
          (.node 274945675264
            (.node 67768320
              (.node 13635584
                (.node 524288
                  (.node 4096
                    (.node 63
                      (.node 0
                        .nil
                        .nil)
                      .nil)
                    (.node 262144
                      (.node 4121
                        .nil
                        .nil)
                      .nil))
                  (.node 528392
                    (.node 528384
                      (.node 524330
                        .nil
                        .nil)
                      .nil)
                    (.node 700416
                      .nil
                      .nil)))
                (.node 67112976
                  (.node 67108916
                    (.node 67108864
                      (.node 33554432
                        .nil
                        .nil)
                      .nil)
                    (.node 67112960
                      .nil
                      .nil))
                  (.node 67633184
                    (.node 67633152
                      (.node 67325952
                        .nil
                        .nil)
                      .nil)
                    (.node 67637248
                      .nil
                      .nil))))
              (.node 214748893184
                (.node 4294967296
                  (.node 604508160
                    (.node 94896128
                      (.node 76025856
                        .nil
                        .nil)
                      .nil)
                    (.node 2886205440
                      (.node 1744834560
                        .nil
                        .nil)
                      .nil))
                  (.node 137506590720
                    (.node 69323984896
                      (.node 68787113984
                        .nil
                        .nil)
                      .nil)
                    (.node 137514979328
                      .nil
                      .nil)))
                (.node 214816002048
                  (.node 214815477760
                    (.node 214762000384
                      (.node 214748893192
                        .nil
                        .nil)
                      .nil)
                    (.node 214815477776
                      .nil
                      .nil))
                  (.node 216493199360
                    (.node 215352872960
                      (.node 214824390656
                        .nil
                        .nil)
                      .nil)
                    (.node 274945544192
                      .nil
                      .nil)))))
            (.node 541166141440
              (.node 446743711760
                (.node 360844890112
                  (.node 360777953280
                    (.node 360777781256
                      (.node 360777781248
                        .nil
                        .nil)
                      .nil)
                    (.node 360844886048
                      (.node 360844886016
                        .nil
                        .nil)
                      .nil))
                  (.node 363663458304
                    (.node 361381761024
                      (.node 360845021184
                        .nil
                        .nil)
                      .nil)
                    (.node 446743711744
                      .nil
                      .nil)))
                (.node 446744367104
                  (.node 446744231968
                    (.node 446744231936
                      (.node 446743924736
                        .nil
                        .nil)
                      .nil)
                    (.node 446744236032
                      .nil
                      .nil))
                  (.node 541165883392
                    (.node 446771494912
                      (.node 446752624640
                        .nil
                        .nil)
                      .nil)
                    (.node 541165883417
                      .nil
                      .nil))))
              (.node 541232992272
                (.node 541179514880
                  (.node 541166407680
                    (.node 541166403626
                      (.node 541166403584
                        .nil
                        .nil)
                      .nil)
                    (.node 541166579712
                      (.node 541166407688
                        .nil
                        .nil)
                      .nil))
                  (.node 541232988212
                    (.node 541232988160
                      (.node 541199433728
                        .nil
                        .nil)
                      .nil)
                    (.node 541232992256
                      .nil
                      .nil)))
                (.node 541233647616
                  (.node 541233512480
                    (.node 541233512448
                      (.node 541233205248
                        .nil
                        .nil)
                      .nil)
                    (.node 541233516544
                      .nil
                      .nil))
                  (.node 541770387456
                    (.node 541260775424
                      (.node 541241905152
                        .nil
                        .nil)
                      .nil)
                    (.node 542910713856
                      .nil
                      .nil))))))
          (.node 70368820203520
            (.node 70368744177664
              (.node 14834817044480
                (.node 9345915949056
                  (.node 5162551218176
                    (.node 4947802853376
                      (.node 545460846592
                        .nil
                        .nil)
                      .nil)
                    (.node 5488968732672
                      (.node 5308580106240
                        .nil
                        .nil)
                      .nil))
                  (.node 9887081828352
                    (.node 9792592547840
                      (.node 9560664313856
                        .nil
                        .nil)
                      .nil)
                    (.node 14293651165184
                      .nil
                      .nil)))
                (.node 23639500521472
                  (.node 18588686090240
                    (.node 18502786744320
                      (.node 18142009491456
                        .nil
                        .nil)
                      .nil)
                    (.node 18683175370752
                      .nil
                      .nil))
                  (.node 29678291124224
                    (.node 29137125244928
                      (.node 24180666400768
                        .nil
                        .nil)
                      .nil)
                    (.node 35184372088832
                      .nil
                      .nil))))
              (.node 70368777732096
                (.node 70368744701994
                  (.node 70368744181785
                    (.node 70368744181760
                      (.node 70368744177727
                        .nil
                        .nil)
                      .nil)
                    (.node 70368744701952
                      (.node 70368744439808
                        .nil
                        .nil)
                      .nil))
                  (.node 70368744878080
                    (.node 70368744706056
                      (.node 70368744706048
                        .nil
                        .nil)
                      .nil)
                    (.node 70368757813248
                      .nil
                      .nil)))
                (.node 70368811503616
                  (.node 70368811290624
                    (.node 70368811286580
                      (.node 70368811286528
                        .nil
                        .nil)
                      .nil)
                    (.node 70368811290640
                      .nil
                      .nil))
                  (.node 70368811814912
                    (.node 70368811810848
                      (.node 70368811810816
                        .nil
                        .nil)
                      .nil)
                    (.node 70368811945984
                      .nil
                      .nil)))))
            (.node 140737488883712
              (.node 140737488359487
                (.node 140737488355328
                  (.node 70370489012224
                    (.node 70369348685824
                      (.node 70368839073792
                        .nil
                        .nil)
                      .nil)
                    (.node 70373039144960
                      (.node 70371630383104
                        .nil
                        .nil)
                      .nil))
                  (.node 140737488359424
                    (.node 140737488359423
                      (.node 140737488355391
                        .nil
                        .nil)
                      .nil)
                    (.node 140737488359449
                      .nil
                      .nil)))
                (.node 140737488879616
                  (.node 140737488617472
                    (.node 140737488363481
                      (.node 140737488361049
                        .nil
                        .nil)
                      .nil)
                    (.node 140737488617535
                      .nil
                      .nil))
                  (.node 140737488882346
                    (.node 140737488879679
                      (.node 140737488879658
                        .nil
                        .nil)
                      .nil)
                    (.node 140737488883690
                      .nil
                      .nil))))
              (.node 140737488887752
                (.node 140737488883775
                  (.node 140737488883754
                    (.node 140737488883737
                      (.node 140737488883720
                        .nil
                        .nil)
                      .nil)
                    (.node 140737488883771
                      .nil
                      .nil))
                  (.node 140737488886408
                    (.node 140737488885320
                      (.node 140737488884232
                        .nil
                        .nil)
                      .nil)
                    (.node 140737488886425
                      .nil
                      .nil)))
                (.node 140737489141802
                  (.node 140737489055807
                    (.node 140737489055786
                      (.node 140737489055744
                        .nil
                        .nil)
                      .nil)
                    (.node 140737489141760
                      .nil
                      .nil))
                  (.node 140737501990975
                    (.node 140737501990937
                      (.node 140737501990912
                        .nil
                        .nil)
                      .nil)
                    (.node 140737521909760
                      .nil
                      .nil)))))))
        (.node 140737583468544
          (.node 140737555992616
            (.node 140737555681332
              (.node 140737555468313
                (.node 140737555464255
                  (.node 140737522171904
                    (.node 140737521913881
                      (.node 140737521913856
                        .nil
                        .nil)
                      .nil)
                    (.node 140737555464244
                      (.node 140737555464192
                        .nil
                        .nil)
                      .nil))
                  (.node 140737555468288
                    (.node 140737555468276
                      (.node 140737555467572
                        .nil
                        .nil)
                      .nil)
                    (.node 140737555468304
                      .nil
                      .nil)))
                (.node 140737555469904
                  (.node 140737555468351
                    (.node 140737555468349
                      (.node 140737555468340
                        .nil
                        .nil)
                      .nil)
                    (.node 140737555469328
                      .nil
                      .nil))
                  (.node 140737555472336
                    (.node 140737555471641
                      (.node 140737555471632
                        .nil
                        .nil)
                      .nil)
                    (.node 140737555681280
                      .nil
                      .nil))))
              (.node 140737555991200
                (.node 140737555988522
                  (.node 140737555726388
                    (.node 140737555726336
                      (.node 140737555681343
                        .nil
                        .nil)
                      .nil)
                    (.node 140737555988512
                      (.node 140737555988480
                        .nil
                        .nil)
                      .nil))
                  (.node 140737555988543
                    (.node 140737555988542
                      (.node 140737555988532
                        .nil
                        .nil)
                      .nil)
                    (.node 140737555990560
                      .nil
                      .nil)))
                (.node 140737555992584
                  (.node 140737555992544
                    (.node 140737555991850
                      (.node 140737555991840
                        .nil
                        .nil)
                      .nil)
                    (.node 140737555992576
                      .nil
                      .nil))
                  (.node 140737555992601
                    (.node 140737555992600
                      (.node 140737555992592
                        .nil
                        .nil)
                      .nil)
                    (.node 140737555992608
                      .nil
                      .nil)))))
            (.node 140737556164660
              (.node 140737555994649
                (.node 140737555992636
                  (.node 140737555992628
                    (.node 140737555992624
                      (.node 140737555992618
                        .nil
                        .nil)
                      .nil)
                    (.node 140737555992634
                      (.node 140737555992633
                        .nil
                        .nil)
                      .nil))
                  (.node 140737555994632
                    (.node 140737555993608
                      (.node 140737555992639
                        .nil
                        .nil)
                      .nil)
                    (.node 140737555994640
                      .nil
                      .nil)))
                (.node 140737556123690
                  (.node 140737556123648
                    (.node 140737555995912
                      (.node 140737555995280
                        .nil
                        .nil)
                      .nil)
                    (.node 140737556123680
                      .nil
                      .nil))
                  (.node 140737556164608
                    (.node 140737556123711
                      (.node 140737556123700
                        .nil
                        .nil)
                      .nil)
                    (.node 140737556164640
                      .nil
                      .nil))))
              (.node 140737564381247
                (.node 140737556250656
                  (.node 140737556205610
                    (.node 140737556205600
                      (.node 140737556205568
                        .nil
                        .nil)
                      .nil)
                    (.node 140737556250624
                      (.node 140737556246528
                        .nil
                        .nil)
                      .nil))
                  (.node 140737564381209
                    (.node 140737564381200
                      (.node 140737564381184
                        .nil
                        .nil)
                      .nil)
                    (.node 140737564381236
                      .nil
                      .nil)))
                (.node 140737583251508
                  (.node 140737569099828
                    (.node 140737569099792
                      (.node 140737569099776
                        .nil
                        .nil)
                      .nil)
                    (.node 140737583251456
                      .nil
                      .nil))
                  (.node 140737583255568
                    (.node 140737583255552
                      (.node 140737583251519
                        .nil
                        .nil)
                      .nil)
                    (.node 140737583255577
                      .nil
                      .nil))))))
          (.node 140806275469312
            (.node 140740374560768
              (.node 140738092863530
                (.node 140737589022736
                  (.node 140737589018624
                    (.node 140737587974144
                      (.node 140737583513600
                        .nil
                        .nil)
                      .nil)
                    (.node 140737589022720
                      (.node 140737589018676
                        .nil
                        .nil)
                      .nil))
                  (.node 140738092863496
                    (.node 140738092863488
                      (.node 140737589235712
                        .nil
                        .nil)
                      .nil)
                    (.node 140738092863513
                      .nil
                      .nil)))
                (.node 140739233714176
                  (.node 140739233189913
                    (.node 140739233189888
                      (.node 140738092863551
                        .nil
                        .nil)
                      .nil)
                    (.node 140739233189951
                      .nil
                      .nil))
                  (.node 140739246821376
                    (.node 140739233714218
                      (.node 140739233714184
                        .nil
                        .nil)
                      .nil)
                    (.node 140739266744320
                      .nil
                      .nil))))
              (.node 140741783326720
                (.node 140740374736896
                  (.node 140740374564864
                    (.node 140740374560831
                      (.node 140740374560810
                        .nil
                        .nil)
                      .nil)
                    (.node 140740374564889
                      (.node 140740374564872
                        .nil
                        .nil)
                      .nil))
                  (.node 140741783322624
                    (.node 140741515415552
                      (.node 140740374822912
                        .nil
                        .nil)
                      .nil)
                    (.node 140741783322687
                      .nil
                      .nil)))
                (.node 140741783851008
                  (.node 140741783846912
                    (.node 140741783584768
                      (.node 140741783326745
                        .nil
                        .nil)
                      .nil)
                    (.node 140741783846954
                      .nil
                      .nil))
                  (.node 140741796958208
                    (.node 140741784023040
                      (.node 140741783851016
                        .nil
                        .nil)
                      .nil)
                    (.node 140741816877056
                      .nil
                      .nil)))))
            (.node 140874994946090
              (.node 140806812340266
                (.node 140806275469364
                  (.node 140806275469337
                    (.node 140806275469328
                      (.node 140806275469320
                        .nil
                        .nil)
                      .nil)
                    (.node 140806275469354
                      (.node 140806275469344
                        .nil
                        .nil)
                      .nil))
                  (.node 140806812340232
                    (.node 140806812340224
                      (.node 140806275469375
                        .nil
                        .nil)
                      .nil)
                    (.node 140806812340249
                      .nil
                      .nil)))
                (.node 140874994946048
                  (.node 140809094041600
                    (.node 140807953190912
                      (.node 140806812340287
                        .nil
                        .nil)
                      .nil)
                    (.node 140810503327744
                      .nil
                      .nil))
                  (.node 140874994946073
                    (.node 140874994946064
                      (.node 140874994946056
                        .nil
                        .nil)
                      .nil)
                    (.node 140874994946080
                      .nil
                      .nil))))
              (.node 140875027976192
                (.node 140875003334681
                  (.node 140875003334656
                    (.node 140874994946111
                      (.node 140874994946100
                        .nil
                        .nil)
                      .nil)
                    (.node 140875003334672
                      .nil
                      .nil))
                  (.node 140875008053248
                    (.node 140875003334719
                      (.node 140875003334708
                        .nil
                        .nil)
                      .nil)
                    (.node 140875022209024
                      .nil
                      .nil)))
                (.node 140952237248575
                  (.node 140952237248537
                    (.node 140952237248520
                      (.node 140952237248512
                        .nil
                        .nil)
                      .nil)
                    (.node 140952237248554
                      .nil
                      .nil))
                  (.node 140952237252552
                    (.node 140952237250120
                      (.node 140952237249032
                        .nil
                        .nil)
                      .nil)
                    (.node 140952250355712
                      .nil
                      .nil))))))))
      (.node 141184232591417
        (.node 141098333241344
          (.node 140953981554688
            (.node 140952304357434
              (.node 140952304357376
                (.node 140952303833140
                  (.node 140952303833088
                    (.node 140952270278656
                      (.node 140952250355775
                        .nil
                        .nil)
                      .nil)
                    (.node 140952303833113
                      (.node 140952303833104
                        .nil
                        .nil)
                      .nil))
                  (.node 140952303834704
                    (.node 140952303834128
                      (.node 140952303833151
                        .nil
                        .nil)
                      .nil)
                    (.node 140952303837136
                      .nil
                      .nil)))
                (.node 140952304357408
                  (.node 140952304357400
                    (.node 140952304357392
                      (.node 140952304357384
                        .nil
                        .nil)
                      .nil)
                    (.node 140952304357401
                      .nil
                      .nil))
                  (.node 140952304357424
                    (.node 140952304357418
                      (.node 140952304357416
                        .nil
                        .nil)
                      .nil)
                    (.node 140952304357428
                      .nil
                      .nil))))
              (.node 140952317464592
                (.node 140952312745984
                  (.node 140952304358408
                    (.node 140952304357439
                      (.node 140952304357436
                        .nil
                        .nil)
                      .nil)
                    (.node 140952304360712
                      (.node 140952304360080
                        .nil
                        .nil)
                      .nil))
                  (.node 140952312746047
                    (.node 140952312746009
                      (.node 140952312746000
                        .nil
                        .nil)
                      .nil)
                    (.node 140952317464576
                      .nil
                      .nil)))
                (.node 140952337387536
                  (.node 140952336338944
                    (.node 140952331620352
                      (.node 140952317464628
                        .nil
                        .nil)
                      .nil)
                    (.node 140952337387520
                      .nil
                      .nil))
                  (.node 140952841228313
                    (.node 140952841228296
                      (.node 140952841228288
                        .nil
                        .nil)
                      .nil)
                    (.node 140952841228351
                      .nil
                      .nil)))))
            (.node 141012433899583
              (.node 140956532215808
                (.node 140953995186176
                  (.node 140953982078976
                    (.node 140953981554751
                      (.node 140953981554713
                        .nil
                        .nil)
                      .nil)
                    (.node 140953982079018
                      (.node 140953982078984
                        .nil
                        .nil)
                      .nil))
                  (.node 140956263780352
                    (.node 140955122929664
                      (.node 140954015109120
                        .nil
                        .nil)
                      .nil)
                    (.node 140956531691520
                      .nil
                      .nil)))
                (.node 141012433899536
                  (.node 141012433899520
                    (.node 140956545323008
                      (.node 140956532215816
                        .nil
                        .nil)
                      .nil)
                    (.node 141012433899528
                      .nil
                      .nil))
                  (.node 141012433899562
                    (.node 141012433899552
                      (.node 141012433899545
                        .nil
                        .nil)
                      .nil)
                    (.node 141012433899572
                      .nil
                      .nil))))
              (.node 141098266136601
                (.node 141012434071552
                  (.node 141012434030634
                    (.node 141012434030624
                      (.node 141012434030592
                        .nil
                        .nil)
                      .nil)
                    (.node 141012434030655
                      (.node 141012434030644
                        .nil
                        .nil)
                      .nil))
                  (.node 141098266136576
                    (.node 141012434157568
                      (.node 141012434112512
                        .nil
                        .nil)
                      .nil)
                    (.node 141098266136584
                      .nil
                      .nil)))
                (.node 141098266140616
                  (.node 141098266137096
                    (.node 141098266136639
                      (.node 141098266136618
                        .nil
                        .nil)
                      .nil)
                    (.node 141098266139272
                      .nil
                      .nil))
                  (.node 141098266308671
                    (.node 141098266308650
                      (.node 141098266308608
                        .nil
                        .nil)
                      .nil)
                    (.node 141098266394624
                      .nil
                      .nil))))))
          (.node 141101151813695
            (.node 141098333247496
              (.node 141098333245464
                (.node 141098333244064
                  (.node 141098333241396
                    (.node 141098333241386
                      (.node 141098333241376
                        .nil
                        .nil)
                      .nil)
                    (.node 141098333243424
                      (.node 141098333241407
                        .nil
                        .nil)
                      .nil))
                  (.node 141098333245448
                    (.node 141098333245440
                      (.node 141098333245408
                        .nil
                        .nil)
                      .nil)
                    (.node 141098333245456
                      .nil
                      .nil)))
                (.node 141098333245488
                  (.node 141098333245480
                    (.node 141098333245472
                      (.node 141098333245465
                        .nil
                        .nil)
                      .nil)
                    (.node 141098333245482
                      .nil
                      .nil))
                  (.node 141098333245500
                    (.node 141098333245497
                      (.node 141098333245492
                        .nil
                        .nil)
                      .nil)
                    (.node 141098333245503
                      .nil
                      .nil))))
              (.node 141098333499392
                (.node 141098333376575
                  (.node 141098333376512
                    (.node 141098333248776
                      (.node 141098333247513
                        .nil
                        .nil)
                      .nil)
                    (.node 141098333376554
                      (.node 141098333376544
                        .nil
                        .nil)
                      .nil))
                  (.node 141098333417524
                    (.node 141098333417504
                      (.node 141098333417472
                        .nil
                        .nil)
                      .nil)
                    (.node 141098333458432
                      .nil
                      .nil)))
                (.node 141098870116394
                  (.node 141098870116352
                    (.node 141098333503520
                      (.node 141098333503488
                        .nil
                        .nil)
                      .nil)
                    (.node 141098870116360
                      .nil
                      .nil))
                  (.node 141101151813632
                    (.node 141100010967040
                      (.node 141098870116415
                        .nil
                        .nil)
                      .nil)
                    (.node 141101151813674
                      .nil
                      .nil)))))
            (.node 141184232280127
              (.node 141184232067072
                (.node 141102292668416
                  (.node 141101151817753
                    (.node 141101151817736
                      (.node 141101151817728
                        .nil
                        .nil)
                      .nil)
                    (.node 141101152075776
                      (.node 141101151989760
                        .nil
                        .nil)
                      .nil))
                  (.node 141102561103880
                    (.node 141102561103872
                      (.node 141102561099776
                        .nil
                        .nil)
                      .nil)
                    (.node 141102561275904
                      .nil
                      .nil)))
                (.node 141184232068112
                  (.node 141184232067124
                    (.node 141184232067097
                      (.node 141184232067088
                        .nil
                        .nil)
                      .nil)
                    (.node 141184232067135
                      .nil
                      .nil))
                  (.node 141184232280064
                    (.node 141184232071120
                      (.node 141184232070416
                        .nil
                        .nil)
                      .nil)
                    (.node 141184232280116
                      .nil
                      .nil))))
              (.node 141184232591360
                (.node 141184232587316
                  (.node 141184232587296
                    (.node 141184232587264
                      (.node 141184232325120
                        .nil
                        .nil)
                      .nil)
                    (.node 141184232587306
                      .nil
                      .nil))
                  (.node 141184232590624
                    (.node 141184232589344
                      (.node 141184232587327
                        .nil
                        .nil)
                      .nil)
                    (.node 141184232591328
                      .nil
                      .nil)))
                (.node 141184232591392
                  (.node 141184232591384
                    (.node 141184232591376
                      (.node 141184232591368
                        .nil
                        .nil)
                      .nil)
                    (.node 141184232591385
                      .nil
                      .nil))
                  (.node 141184232591408
                    (.node 141184232591402
                      (.node 141184232591400
                        .nil
                        .nil)
                      .nil)
                    (.node 141184232591412
                      .nil
                      .nil)))))))
        (.node 141278667870208
          (.node 141261542002688
            (.node 141184245698560
              (.node 141184232804352
                (.node 141184232722432
                  (.node 141184232593424
                    (.node 141184232591423
                      (.node 141184232591418
                        .nil
                        .nil)
                      .nil)
                    (.node 141184232594064
                      (.node 141184232593433
                        .nil
                        .nil)
                      .nil))
                  (.node 141184232722495
                    (.node 141184232722484
                      (.node 141184232722464
                        .nil
                        .nil)
                      .nil)
                    (.node 141184232763392
                      .nil
                      .nil)))
                (.node 141184232849440
                  (.node 141184232845312
                    (.node 141184232804394
                      (.node 141184232804384
                        .nil
                        .nil)
                      .nil)
                    (.node 141184232849408
                      .nil
                      .nil))
                  (.node 141184240980020
                    (.node 141184240979984
                      (.node 141184240979968
                        .nil
                        .nil)
                      .nil)
                    (.node 141184240980031
                      .nil
                      .nil))))
              (.node 141184265621504
                (.node 141184259854361
                  (.node 141184259850303
                    (.node 141184259850292
                      (.node 141184259850240
                        .nil
                        .nil)
                      .nil)
                    (.node 141184259854352
                      (.node 141184259854336
                        .nil
                        .nil)
                      .nil))
                  (.node 141184264572928
                    (.node 141184260112384
                      (.node 141184260067328
                        .nil
                        .nil)
                      .nil)
                    (.node 141184265617408
                      .nil
                      .nil)))
                (.node 141244362133536
                  (.node 141244362133504
                    (.node 141184265834496
                      (.node 141184265621520
                        .nil
                        .nil)
                      .nil)
                    (.node 141244362133520
                      .nil
                      .nil))
                  (.node 141247180705792
                    (.node 141246039855104
                      (.node 141244362133552
                        .nil
                        .nil)
                      .nil)
                    (.node 141248321556480
                      .nil
                      .nil)))))
            (.node 141278654758912
              (.node 141270132109312
                (.node 141261573984256
                  (.node 141261542002728
                    (.node 141261542002720
                      (.node 141261542002696
                        .nil
                        .nil)
                      .nil)
                    (.node 141261569265664
                      (.node 141261555109888
                        .nil
                        .nil)
                      .nil))
                  (.node 141270131937296
                    (.node 141270131937288
                      (.node 141270131937280
                        .nil
                        .nil)
                      .nil)
                    (.node 141270131937304
                      .nil
                      .nil)))
                (.node 141278654238783
                  (.node 141278654238720
                    (.node 141270132191232
                      (.node 141270132150272
                        .nil
                        .nil)
                      .nil)
                    (.node 141278654238745
                      .nil
                      .nil))
                  (.node 141278654496768
                    (.node 141278654242777
                      (.node 141278654240345
                        .nil
                        .nil)
                      .nil)
                    (.node 141278654496831
                      .nil
                      .nil))))
              (.node 141278654763528
                (.node 141278654763016
                  (.node 141278654761642
                    (.node 141278654758975
                      (.node 141278654758954
                        .nil
                        .nil)
                      .nil)
                    (.node 141278654763008
                      (.node 141278654762986
                        .nil
                        .nil)
                      .nil))
                  (.node 141278654763067
                    (.node 141278654763050
                      (.node 141278654763033
                        .nil
                        .nil)
                      .nil)
                    (.node 141278654763071
                      .nil
                      .nil)))
                (.node 141278654935040
                  (.node 141278654765721
                    (.node 141278654765704
                      (.node 141278654764616
                        .nil
                        .nil)
                      .nil)
                    (.node 141278654767048
                      .nil
                      .nil))
                  (.node 141278655021056
                    (.node 141278654935103
                      (.node 141278654935082
                        .nil
                        .nil)
                      .nil)
                    (.node 141278655021098
                      .nil
                      .nil))))))
          (.node 141278721871888
            (.node 141278721350928
              (.node 141278721346868
                (.node 141278687793177
                  (.node 141278687789056
                    (.node 141278667870271
                      (.node 141278667870233
                        .nil
                        .nil)
                      .nil)
                    (.node 141278687793152
                      (.node 141278687789119
                        .nil
                        .nil)
                      .nil))
                  (.node 141278721343540
                    (.node 141278721343488
                      (.node 141278688051200
                        .nil
                        .nil)
                      .nil)
                    (.node 141278721343551
                      .nil
                      .nil)))
                (.node 141278721347636
                  (.node 141278721347600
                    (.node 141278721347584
                      (.node 141278721347572
                        .nil
                        .nil)
                      .nil)
                    (.node 141278721347609
                      .nil
                      .nil))
                  (.node 141278721348624
                    (.node 141278721347647
                      (.node 141278721347645
                        .nil
                        .nil)
                      .nil)
                    (.node 141278721349200
                      .nil
                      .nil))))
              (.node 141278721867828
                (.node 141278721605632
                  (.node 141278721560576
                    (.node 141278721351632
                      (.node 141278721350937
                        .nil
                        .nil)
                      .nil)
                    (.node 141278721560639
                      (.node 141278721560628
                        .nil
                        .nil)
                      .nil))
                  (.node 141278721867808
                    (.node 141278721867776
                      (.node 141278721605684
                        .nil
                        .nil)
                      .nil)
                    (.node 141278721867818
                      .nil
                      .nil)))
                (.node 141278721871136
                  (.node 141278721869856
                    (.node 141278721867839
                      (.node 141278721867838
                        .nil
                        .nil)
                      .nil)
                    (.node 141278721870496
                      .nil
                      .nil))
                  (.node 141278721871872
                    (.node 141278721871840
                      (.node 141278721871146
                        .nil
                        .nil)
                      .nil)
                    (.node 141278721871880
                      .nil
                      .nil)))))
            (.node 141278722002996
              (.node 141278721871935
                (.node 141278721871920
                  (.node 141278721871904
                    (.node 141278721871897
                      (.node 141278721871896
                        .nil
                        .nil)
                      .nil)
                    (.node 141278721871914
                      (.node 141278721871912
                        .nil
                        .nil)
                      .nil))
                  (.node 141278721871930
                    (.node 141278721871929
                      (.node 141278721871924
                        .nil
                        .nil)
                      .nil)
                    (.node 141278721871932
                      .nil
                      .nil)))
                (.node 141278721874576
                  (.node 141278721873936
                    (.node 141278721873928
                      (.node 141278721872904
                        .nil
                        .nil)
                      .nil)
                    (.node 141278721873945
                      .nil
                      .nil))
                  (.node 141278722002976
                    (.node 141278722002944
                      (.node 141278721875208
                        .nil
                        .nil)
                      .nil)
                    (.node 141278722002986
                      .nil
                      .nil))))
              (.node 141278722129952
                (.node 141278722084864
                  (.node 141278722043936
                    (.node 141278722043904
                      (.node 141278722003007
                        .nil
                        .nil)
                      .nil)
                    (.node 141278722043956
                      .nil
                      .nil))
                  (.node 141278722125824
                    (.node 141278722084906
                      (.node 141278722084896
                        .nil
                        .nil)
                      .nil)
                    (.node 141278722129920
                      .nil
                      .nil)))
                (.node 141278730260543
                  (.node 141278730260505
                    (.node 141278730260496
                      (.node 141278730260480
                        .nil
                        .nil)
                      .nil)
                    (.node 141278730260532
                      .nil
                      .nil))
                  (.node 141278734979124
                    (.node 141278734979088
                      (.node 141278734979072
                        .nil
                        .nil)
                      .nil)
                    (.node 141278749130752
                      .nil
                      .nil)))))))))
    (.node 164918758739968
      (.node 155031206629376
        (.node 146132034916352
          (.node 141282949730304
            (.node 141280399593472
              (.node 141278754902032
                (.node 141278749392896
                  (.node 141278749134864
                    (.node 141278749134848
                      (.node 141278749130815
                        .nil
                        .nil)
                      .nil)
                    (.node 141278749347840
                      (.node 141278749134873
                        .nil
                        .nil)
                      .nil))
                  (.node 141278754897972
                    (.node 141278754897920
                      (.node 141278753853440
                        .nil
                        .nil)
                      .nil)
                    (.node 141278754902016
                      .nil
                      .nil)))
                (.node 141279258742826
                  (.node 141279258742792
                    (.node 141279258742784
                      (.node 141278755115008
                        .nil
                        .nil)
                      .nil)
                    (.node 141279258742809
                      .nil
                      .nil))
                  (.node 141280399069209
                    (.node 141280399069184
                      (.node 141279258742847
                        .nil
                        .nil)
                      .nil)
                    (.node 141280399069247
                      .nil
                      .nil))))
              (.node 141281540616192
                (.node 141281540440106
                  (.node 141280412700672
                    (.node 141280399593514
                      (.node 141280399593480
                        .nil
                        .nil)
                      .nil)
                    (.node 141281540440064
                      (.node 141280432623616
                        .nil
                        .nil)
                      .nil))
                  (.node 141281540444168
                    (.node 141281540444160
                      (.node 141281540440127
                        .nil
                        .nil)
                      .nil)
                    (.node 141281540444185
                      .nil
                      .nil)))
                (.node 141282949206016
                  (.node 141282949201920
                    (.node 141282681294848
                      (.node 141281540702208
                        .nil
                        .nil)
                      .nil)
                    (.node 141282949201983
                      .nil
                      .nil))
                  (.node 141282949726208
                    (.node 141282949464064
                      (.node 141282949206041
                        .nil
                        .nil)
                      .nil)
                    (.node 141282949726250
                      .nil
                      .nil)))))
            (.node 145900039573504
              (.node 145685358317584
                (.node 145685291208712
                  (.node 141282962837504
                    (.node 141282949902336
                      (.node 141282949730312
                        .nil
                        .nil)
                      .nil)
                    (.node 145685291208704
                      (.node 141282982756352
                        .nil
                        .nil)
                      .nil))
                  (.node 145685291208767
                    (.node 145685291208746
                      (.node 145685291208729
                        .nil
                        .nil)
                      .nil)
                    (.node 145685358317568
                      .nil
                      .nil)))
                (.node 145688176889856
                  (.node 145685895188480
                    (.node 145685358317620
                      (.node 145685358317600
                        .nil
                        .nil)
                      .nil)
                    (.node 145687036039168
                      .nil
                      .nil))
                  (.node 145754614665216
                    (.node 145754077794304
                      (.node 145689586176000
                        .nil
                        .nil)
                      .nil)
                    (.node 145822797271040
                      .nil
                      .nil))))
              (.node 146046068461568
                (.node 145900106682420
                  (.node 145900039573567
                    (.node 145900039573529
                      (.node 145900039573512
                        .nil
                        .nil)
                      .nil)
                    (.node 145900106682384
                      (.node 145900106682368
                        .nil
                        .nil)
                      .nil))
                  (.node 145904334540800
                    (.node 145901784403968
                      (.node 145900643553280
                        .nil
                        .nil)
                      .nil)
                    (.node 145960236224512
                      .nil
                      .nil)))
                (.node 146046135570464
                  (.node 146046068461631
                    (.node 146046068461610
                      (.node 146046068461576
                        .nil
                        .nil)
                      .nil)
                    (.node 146046135570432
                      .nil
                      .nil))
                  (.node 146048954142720
                    (.node 146046672441344
                      (.node 146046135570484
                        .nil
                        .nil)
                      .nil)
                    (.node 146050363428864
                      .nil
                      .nil))))))
          (.node 150358282735616
            (.node 150083404828672
              (.node 146226524196916
                (.node 146226457088042
                  (.node 146226457088000
                    (.node 146217934262272
                      (.node 146209344327680
                        .nil
                        .nil)
                      .nil)
                    (.node 146226457088025
                      (.node 146226457088008
                        .nil
                        .nil)
                      .nil))
                  (.node 146226524196880
                    (.node 146226524196864
                      (.node 146226457088063
                        .nil
                        .nil)
                      .nil)
                    (.node 146226524196896
                      .nil
                      .nil)))
                (.node 150083404304384
                  (.node 146229342769152
                    (.node 146228201918464
                      (.node 146227061067776
                        .nil
                        .nil)
                      .nil)
                    (.node 146230752055296
                      .nil
                      .nil))
                  (.node 150083404304436
                    (.node 150083404304409
                      (.node 150083404304400
                        .nil
                        .nil)
                      .nil)
                    (.node 150083404304447
                      .nil
                      .nil))))
              (.node 150298152669184
                (.node 150083432091648
                  (.node 150083404828714
                    (.node 150083404828704
                      (.node 150083404828680
                        .nil
                        .nil)
                      .nil)
                    (.node 150083417935872
                      (.node 150083413217280
                        .nil
                        .nil)
                      .nil))
                  (.node 150220843782144
                    (.node 150152124305408
                      (.node 150083437858816
                        .nil
                        .nil)
                      .nil)
                    (.node 150220852170752
                      .nil
                      .nil)))
                (.node 150298153193480
                  (.node 150298152669247
                    (.node 150298152669209
                      (.node 150298152669200
                        .nil
                        .nil)
                      .nil)
                    (.node 150298153193472
                      .nil
                      .nil))
                  (.node 150298166300672
                    (.node 150298161582080
                      (.node 150298153193514
                        .nil
                        .nil)
                      .nil)
                    (.node 150298186223616
                      .nil
                      .nil)))))
            (.node 150624570708000
              (.node 150530114457600
                (.node 150530081427456
                  (.node 150530080903184
                    (.node 150530080903168
                      (.node 150444182081536
                        .nil
                        .nil)
                      .nil)
                    (.node 150530080903231
                      (.node 150530080903220
                        .nil
                        .nil)
                      .nil))
                  (.node 150530089816064
                    (.node 150530081427498
                      (.node 150530081427488
                        .nil
                        .nil)
                      .nil)
                    (.node 150530108690432
                      .nil
                      .nil)))
                (.node 150624570183705
                  (.node 150624570183680
                    (.node 150615980773376
                      (.node 150590210969600
                        .nil
                        .nil)
                      .nil)
                    (.node 150624570183696
                      .nil
                      .nil))
                  (.node 150624570707968
                    (.node 150624570183743
                      (.node 150624570183732
                        .nil
                        .nil)
                      .nil)
                    (.node 150624570707976
                      .nil
                      .nil))))
              (.node 155014027284480
                (.node 150624603738112
                  (.node 150624583815168
                    (.node 150624579096576
                      (.node 150624570708010
                        .nil
                        .nil)
                      .nil)
                    (.node 150624597970944
                      .nil
                      .nil))
                  (.node 154842228592640
                    (.node 154696199704576
                      (.node 154481451339776
                        .nil
                        .nil)
                      .nil)
                    (.node 154928127938560
                      .nil
                      .nil)))
                (.node 155031140044800
                  (.node 155031139520537
                    (.node 155031139520512
                      (.node 155022617219072
                        .nil
                        .nil)
                      .nil)
                    (.node 155031139520575
                      .nil
                      .nil))
                  (.node 155031153152000
                    (.node 155031140044842
                      (.node 155031140044808
                        .nil
                        .nil)
                      .nil)
                    (.node 155031173074944
                      .nil
                      .nil)))))))
        (.node 159326174449664
          (.node 155572372508688
            (.node 155245963907072
              (.node 155099926630400
                (.node 155031234416640
                  (.node 155031207153664
                    (.node 155031206629428
                      (.node 155031206629392
                        .nil
                        .nil)
                      .nil)
                    (.node 155031215542272
                      (.node 155031207153696
                        .nil
                        .nil)
                      .nil))
                  (.node 155034025725952
                    (.node 155032884350976
                      (.node 155031744024576
                        .nil
                        .nil)
                      .nil)
                    (.node 155035434487808
                      .nil
                      .nil)))
                (.node 155245888409608
                  (.node 155168654495744
                    (.node 155168646107136
                      (.node 155100463501312
                        .nil
                        .nil)
                      .nil)
                    (.node 155245888409600
                      .nil
                      .nil))
                  (.node 155245954994192
                    (.node 155245954994176
                      (.node 155245901516800
                        .nil
                        .nil)
                      .nil)
                    (.node 155245955518464
                      .nil
                      .nil))))
              (.node 155477911015424
                (.node 155391984406560
                  (.node 155306085060608
                    (.node 155247632715776
                      (.node 155246492389376
                        .nil
                        .nil)
                      .nil)
                    (.node 155391984406528
                      (.node 155391917297664
                        .nil
                        .nil)
                      .nil))
                  (.node 155477883752448
                    (.node 155477883228160
                      (.node 155394802978816
                        .nil
                        .nil)
                      .nil)
                    (.node 155477883752480
                      .nil
                      .nil)))
                (.node 155572305924104
                  (.node 155572305399871
                    (.node 155572305399833
                      (.node 155572305399808
                        .nil
                        .nil)
                      .nil)
                    (.node 155572305924096
                      .nil
                      .nil))
                  (.node 155572338954240
                    (.node 155572319031296
                      (.node 155572305924138
                        .nil
                        .nil)
                      .nil)
                    (.node 155572372508672
                      .nil
                      .nil)))))
            (.node 158879498063872
              (.node 158879497846816
                (.node 155572909903872
                  (.node 155572373032992
                    (.node 155572373032960
                      (.node 155572372508724
                        .nil
                        .nil)
                      .nil)
                    (.node 155572400295936
                      (.node 155572381421568
                        .nil
                        .nil)
                      .nil))
                  (.node 155576600367104
                    (.node 155575191605248
                      (.node 155574050230272
                        .nil
                        .nil)
                      .nil)
                    (.node 158879497846784
                      .nil
                      .nil)))
                (.node 158879497850888
                  (.node 158879497846847
                    (.node 158879497846836
                      (.node 158879497846826
                        .nil
                        .nil)
                      .nil)
                    (.node 158879497850880
                      .nil
                      .nil))
                  (.node 158879497981952
                    (.node 158879497850905
                      (.node 158879497850896
                        .nil
                        .nil)
                      .nil)
                    (.node 158879498022912
                      .nil
                      .nil))))
              (.node 159240275103744
                (.node 159154375888896
                  (.node 159016936804352
                    (.node 158948217327616
                      (.node 158879498108928
                        .nil
                        .nil)
                      .nil)
                    (.node 159154375757824
                      (.node 159094246215680
                        .nil
                        .nil)
                      .nil))
                  (.node 159240275099690
                    (.node 159240275099680
                      (.node 159240275099648
                        .nil
                        .nil)
                      .nil)
                    (.node 159240275099711
                      .nil
                      .nil)))
                (.node 159240275361792
                  (.node 159240275234816
                    (.node 159240275103769
                      (.node 159240275103752
                        .nil
                        .nil)
                      .nil)
                    (.node 159240275275776
                      .nil
                      .nil))
                  (.node 159326174445620
                    (.node 159326174445600
                      (.node 159326174445568
                        .nil
                        .nil)
                      .nil)
                    (.node 159326174445631
                      .nil
                      .nil))))))
          (.node 164377592860672
            (.node 163277544361984
              (.node 159420663726132
                (.node 159386303991808
                  (.node 159326174580736
                    (.node 159326174449689
                      (.node 159326174449680
                        .nil
                        .nil)
                      .nil)
                    (.node 159326174707712
                      (.node 159326174662656
                        .nil
                        .nil)
                      .nil))
                  (.node 159420663726112
                    (.node 159420663726080
                      (.node 159403483860992
                        .nil
                        .nil)
                      .nil)
                    (.node 159420663726122
                      .nil
                      .nil)))
                (.node 159420663730201
                  (.node 159420663730184
                    (.node 159420663730176
                      (.node 159420663726143
                        .nil
                        .nil)
                      .nil)
                    (.node 159420663730192
                      .nil
                      .nil))
                  (.node 159420663943168
                    (.node 159420663902208
                      (.node 159420663861248
                        .nil
                        .nil)
                      .nil)
                    (.node 159420663988224
                      .nil
                      .nil))))
              (.node 164376988880921
                (.node 164376988876800
                  (.node 163724220960768
                    (.node 163638321614848
                      (.node 163492292726784
                        .nil
                        .nil)
                      .nil)
                    (.node 163818710241280
                      (.node 163801530372096
                        .nil
                        .nil)
                      .nil))
                  (.node 164376988880896
                    (.node 164376988876863
                      (.node 164376988876842
                        .nil
                        .nil)
                      .nil)
                    (.node 164376988880904
                      .nil
                      .nil)))
                (.node 164377055985716
                  (.node 164377055985664
                    (.node 164376989138944
                      (.node 164376989052928
                        .nil
                        .nil)
                      .nil)
                    (.node 164377055985696
                      .nil
                      .nil))
                  (.node 164377056120832
                    (.node 164377055989776
                      (.node 164377055989760
                        .nil
                        .nil)
                      .nil)
                    (.node 164377056202752
                      .nil
                      .nil)))))
            (.node 164740651810816
              (.node 164651933896704
                (.node 164514494943232
                  (.node 164381283844096
                    (.node 164379874557952
                      (.node 164378733711360
                        .nil
                        .nil)
                      .nil)
                    (.node 164446312337408
                      (.node 164445775466496
                        .nil
                        .nil)
                      .nil))
                  (.node 164591804354576
                    (.node 164591804354560
                      (.node 164591737245696
                        .nil
                        .nil)
                      .nil)
                    (.node 164593482076160
                      .nil
                      .nil)))
                (.node 164737833238528
                  (.node 164737766133768
                    (.node 164737766133760
                      (.node 164651934027776
                        .nil
                        .nil)
                      .nil)
                    (.node 164737766305792
                      .nil
                      .nil))
                  (.node 164737833373696
                    (.node 164737833242624
                      (.node 164737833238560
                        .nil
                        .nil)
                      .nil)
                    (.node 164738370113536
                      .nil
                      .nil))))
              (.node 164918154760217
                (.node 164918154756096
                  (.node 164823732588560
                    (.node 164823732588544
                      (.node 164823732584448
                        .nil
                        .nil)
                      .nil)
                    (.node 164823732801536
                      .nil
                      .nil))
                  (.node 164918154760192
                    (.node 164918154756159
                      (.node 164918154756138
                        .nil
                        .nil)
                      .nil)
                    (.node 164918154760200
                      .nil
                      .nil)))
                (.node 164918221865012
                  (.node 164918221864960
                    (.node 164918155018240
                      (.node 164918154932224
                        .nil
                        .nil)
                      .nil)
                    (.node 164918221864992
                      .nil
                      .nil))
                  (.node 164918222000128
                    (.node 164918221869072
                      (.node 164918221869056
                        .nil
                        .nil)
                      .nil)
                    (.node 164918222082048
                      .nil
                      .nil))))))))
      (.node 176463102349312
        (.node 174822415929344
          (.node 170321290203136
            (.node 169874614128640
              (.node 169874613600308
                (.node 168036368125952
                  (.node 164922449723392
                    (.node 164921040437248
                      (.node 164919899590656
                        .nil
                        .nil)
                      .nil)
                    (.node 167890339237888
                      (.node 167675590873088
                        .nil
                        .nil)
                      .nil))
                  (.node 168216756752384
                    (.node 168182397014016
                      (.node 168122267471872
                        .nil
                        .nil)
                      .nil)
                    (.node 169874613600256
                      .nil
                      .nil)))
                (.node 169874613817344
                  (.node 169874613604368
                    (.node 169874613604352
                      (.node 169874613600319
                        .nil
                        .nil)
                      .nil)
                    (.node 169874613604377
                      .nil
                      .nil))
                  (.node 169874614124576
                    (.node 169874614124544
                      (.node 169874613862400
                        .nil
                        .nil)
                      .nil)
                    (.node 169874614124586
                      .nil
                      .nil))))
              (.node 170089361969152
                (.node 169874641387520
                  (.node 169874614300672
                    (.node 169874614259712
                      (.node 169874614128648
                        .nil
                        .nil)
                      .nil)
                    (.node 169874627235840
                      (.node 169874622517248
                        .nil
                        .nil)
                      .nil))
                  (.node 170012053082112
                    (.node 169943333605376
                      (.node 169874647154688
                        .nil
                        .nil)
                      .nil)
                    (.node 170012061470720
                      .nil
                      .nil)))
                (.node 170149492166656
                  (.node 170089375600640
                    (.node 170089362493448
                      (.node 170089362493440
                        .nil
                        .nil)
                      .nil)
                    (.node 170149492035584
                      .nil
                      .nil))
                  (.node 170235391381512
                    (.node 170235391381504
                      (.node 170235391377408
                        .nil
                        .nil)
                      .nil)
                    (.node 170235391553536
                      .nil
                      .nil)))))
            (.node 170415780007944
              (.node 170415779479615
                (.node 170321290858496
                  (.node 170321290723328
                    (.node 170321290416128
                      (.node 170321290203152
                        .nil
                        .nil)
                      .nil)
                    (.node 170321290727424
                      (.node 170321290723360
                        .nil
                        .nil)
                      .nil))
                  (.node 170415779479552
                    (.node 170321317986304
                      (.node 170321299116032
                        .nil
                        .nil)
                      .nil)
                    (.node 170415779479604
                      .nil
                      .nil)))
                (.node 170415779741696
                  (.node 170415779483673
                    (.node 170415779483664
                      (.node 170415779483648
                        .nil
                        .nil)
                      .nil)
                    (.node 170415779696640
                      .nil
                      .nil))
                  (.node 170415780003882
                    (.node 170415780003872
                      (.node 170415780003840
                        .nil
                        .nil)
                      .nil)
                    (.node 170415780007936
                      .nil
                      .nil))))
              (.node 173173149011968
                (.node 170415813033984
                  (.node 170415788396544
                    (.node 170415780179968
                      (.node 170415780139008
                        .nil
                        .nil)
                      .nil)
                    (.node 170415807266816
                      (.node 170415793115136
                        .nil
                        .nil)
                      .nil))
                  (.node 173070069796864
                    (.node 172984170450944
                      (.node 172623393198080
                        .nil
                        .nil)
                      .nil)
                    (.node 173164559077376
                      .nil
                      .nil)))
                (.node 174264003596288
                  (.node 173714314891264
                    (.node 173619825610752
                      (.node 173387897376768
                        .nil
                        .nil)
                      .nil)
                    (.node 173722837716992
                      .nil
                      .nil))
                  (.node 174633437892608
                    (.node 174487409004544
                      (.node 174272660639744
                        .nil
                        .nil)
                      .nil)
                    (.node 174813826519040
                      .nil
                      .nil))))))
          (.node 176137213317120
            (.node 175921928077312
              (.node 175921860972544
                (.node 175921860448256
                  (.node 175913338142720
                    (.node 175372172263424
                      (.node 175363581808640
                        .nil
                        .nil)
                      .nil)
                    (.node 175921860444223
                      (.node 175921860444160
                        .nil
                        .nil)
                      .nil))
                  (.node 175921860968448
                    (.node 175921860706304
                      (.node 175921860448281
                        .nil
                        .nil)
                      .nil)
                    (.node 175921860968490
                      .nil
                      .nil)))
                (.node 175921927553024
                  (.node 175921874079744
                    (.node 175921861144576
                      (.node 175921860972552
                        .nil
                        .nil)
                      .nil)
                    (.node 175921893998592
                      .nil
                      .nil))
                  (.node 175921927557136
                    (.node 175921927557120
                      (.node 175921927553076
                        .nil
                        .nil)
                      .nil)
                    (.node 175921927770112
                      .nil
                      .nil))))
              (.node 175991184429056
                (.node 175922464952320
                  (.node 175921928212480
                    (.node 175921928081408
                      (.node 175921928077344
                        .nil
                        .nil)
                      .nil)
                    (.node 175921955340288
                      (.node 175921936470016
                        .nil
                        .nil)
                      .nil))
                  (.node 175926155411456
                    (.node 175924746649600
                      (.node 175923605278720
                        .nil
                        .nil)
                      .nil)
                    (.node 175990647558144
                      .nil
                      .nil)))
                (.node 176136622444544
                  (.node 176136609337344
                    (.node 176059375423488
                      (.node 176059367034880
                        .nil
                        .nil)
                      .nil)
                    (.node 176136609337352
                      .nil
                      .nil))
                  (.node 176136676446208
                    (.node 176136675921936
                      (.node 176136675921920
                        .nil
                        .nil)
                      .nil)
                    (.node 176136684834816
                      .nil
                      .nil)))))
            (.node 176368631939072
              (.node 176283242205184
                (.node 176282638397440
                  (.node 176196806119424
                    (.node 176196805988352
                      (.node 176138353643520
                        .nil
                        .nil)
                      .nil)
                    (.node 176282638225416
                      (.node 176282638225408
                        .nil
                        .nil)
                      .nil))
                  (.node 176282705334272
                    (.node 176282705330208
                      (.node 176282705330176
                        .nil
                        .nil)
                      .nil)
                    (.node 176282705465344
                      .nil
                      .nil)))
                (.node 176368604676096
                  (.node 176368604155920
                    (.node 176368604155904
                      (.node 176285523902464
                        .nil
                        .nil)
                      .nil)
                    (.node 176368604368896
                      .nil
                      .nil))
                  (.node 176368604811264
                    (.node 176368604680192
                      (.node 176368604676128
                        .nil
                        .nil)
                      .nil)
                    (.node 176368613068800
                      .nil
                      .nil))))
              (.node 176463059877888
                (.node 176463026847786
                  (.node 176463026585600
                    (.node 176463026327577
                      (.node 176463026327552
                        .nil
                        .nil)
                      .nil)
                    (.node 176463026847744
                      .nil
                      .nil))
                  (.node 176463027023872
                    (.node 176463026851848
                      (.node 176463026851840
                        .nil
                        .nil)
                      .nil)
                    (.node 176463039959040
                      .nil
                      .nil)))
                (.node 176463093649408
                  (.node 176463093436416
                    (.node 176463093432372
                      (.node 176463093432320
                        .nil
                        .nil)
                      .nil)
                    (.node 176463093436432
                      .nil
                      .nil))
                  (.node 176463093960704
                    (.node 176463093956640
                      (.node 176463093956608
                        .nil
                        .nil)
                      .nil)
                    (.node 176463094091776
                      .nil
                      .nil)))))))
        (.node 211106300170282
          (.node 211106266091520
            (.node 211106233061376
              (.node 211106232537151
                (.node 211106232532992
                  (.node 176464771158016
                    (.node 176463630831616
                      (.node 176463121219584
                        .nil
                        .nil)
                      .nil)
                    (.node 176467321290752
                      (.node 176465912528896
                        .nil
                        .nil)
                      .nil))
                  (.node 211106232537088
                    (.node 211106232537087
                      (.node 211106232533055
                        .nil
                        .nil)
                      .nil)
                    (.node 211106232537113
                      .nil
                      .nil)))
                (.node 211106233057280
                  (.node 211106232795136
                    (.node 211106232541145
                      (.node 211106232538713
                        .nil
                        .nil)
                      .nil)
                    (.node 211106232795199
                      .nil
                      .nil))
                  (.node 211106233060010
                    (.node 211106233057343
                      (.node 211106233057322
                        .nil
                        .nil)
                      .nil)
                    (.node 211106233061354
                      .nil
                      .nil))))
              (.node 211106233233408
                (.node 211106233061896
                  (.node 211106233061418
                    (.node 211106233061401
                      (.node 211106233061384
                        .nil
                        .nil)
                      .nil)
                    (.node 211106233061439
                      (.node 211106233061435
                        .nil
                        .nil)
                      .nil))
                  (.node 211106233064089
                    (.node 211106233064072
                      (.node 211106233062984
                        .nil
                        .nil)
                      .nil)
                    (.node 211106233065416
                      .nil
                      .nil)))
                (.node 211106246168576
                  (.node 211106233319424
                    (.node 211106233233471
                      (.node 211106233233450
                        .nil
                        .nil)
                      .nil)
                    (.node 211106233319466
                      .nil
                      .nil))
                  (.node 211106266087424
                    (.node 211106246168639
                      (.node 211106246168601
                        .nil
                        .nil)
                      .nil)
                    (.node 211106266087487
                      .nil
                      .nil)))))
            (.node 211106299859007
              (.node 211106299646004
                (.node 211106299645236
                  (.node 211106299641856
                    (.node 211106266349568
                      (.node 211106266091545
                        .nil
                        .nil)
                      .nil)
                    (.node 211106299641919
                      (.node 211106299641908
                        .nil
                        .nil)
                      .nil))
                  (.node 211106299645968
                    (.node 211106299645952
                      (.node 211106299645940
                        .nil
                        .nil)
                      .nil)
                    (.node 211106299645977
                      .nil
                      .nil)))
                (.node 211106299649296
                  (.node 211106299646992
                    (.node 211106299646015
                      (.node 211106299646013
                        .nil
                        .nil)
                      .nil)
                    (.node 211106299647568
                      .nil
                      .nil))
                  (.node 211106299858944
                    (.node 211106299650000
                      (.node 211106299649305
                        .nil
                        .nil)
                      .nil)
                    (.node 211106299858996
                      .nil
                      .nil))))
              (.node 211106300169504
                (.node 211106300166196
                  (.node 211106300166144
                    (.node 211106299904052
                      (.node 211106299904000
                        .nil
                        .nil)
                      .nil)
                    (.node 211106300166186
                      (.node 211106300166176
                        .nil
                        .nil)
                      .nil))
                  (.node 211106300168224
                    (.node 211106300166207
                      (.node 211106300166206
                        .nil
                        .nil)
                      .nil)
                    (.node 211106300168864
                      .nil
                      .nil)))
                (.node 211106300170256
                  (.node 211106300170240
                    (.node 211106300170208
                      (.node 211106300169514
                        .nil
                        .nil)
                      .nil)
                    (.node 211106300170248
                      .nil
                      .nil))
                  (.node 211106300170272
                    (.node 211106300170265
                      (.node 211106300170264
                        .nil
                        .nil)
                      .nil)
                    (.node 211106300170280
                      .nil
                      .nil))))))
          (.node 211106327691264
            (.node 211106300383232
              (.node 211106300172944
                (.node 211106300170303
                  (.node 211106300170297
                    (.node 211106300170292
                      (.node 211106300170288
                        .nil
                        .nil)
                      .nil)
                    (.node 211106300170300
                      (.node 211106300170298
                        .nil
                        .nil)
                      .nil))
                  (.node 211106300172304
                    (.node 211106300172296
                      (.node 211106300171272
                        .nil
                        .nil)
                      .nil)
                    (.node 211106300172313
                      .nil
                      .nil)))
                (.node 211106300301364
                  (.node 211106300301344
                    (.node 211106300301312
                      (.node 211106300173576
                        .nil
                        .nil)
                      .nil)
                    (.node 211106300301354
                      .nil
                      .nil))
                  (.node 211106300342304
                    (.node 211106300342272
                      (.node 211106300301375
                        .nil
                        .nil)
                      .nil)
                    (.node 211106300342324
                      .nil
                      .nil))))
              (.node 211106313277440
                (.node 211106308558848
                  (.node 211106300424192
                    (.node 211106300383274
                      (.node 211106300383264
                        .nil
                        .nil)
                      .nil)
                    (.node 211106300428320
                      (.node 211106300428288
                        .nil
                        .nil)
                      .nil))
                  (.node 211106308558900
                    (.node 211106308558873
                      (.node 211106308558864
                        .nil
                        .nil)
                      .nil)
                    (.node 211106308558911
                      .nil
                      .nil)))
                (.node 211106327429183
                  (.node 211106327429120
                    (.node 211106313277492
                      (.node 211106313277456
                        .nil
                        .nil)
                      .nil)
                    (.node 211106327429172
                      .nil
                      .nil))
                  (.node 211106327433241
                    (.node 211106327433232
                      (.node 211106327433216
                        .nil
                        .nil)
                      .nil)
                    (.node 211106327646208
                      .nil
                      .nil)))))
            (.node 211109118738474
              (.node 211106837041215
                (.node 211106333413376
                  (.node 211106333196340
                    (.node 211106333196288
                      (.node 211106332151808
                        .nil
                        .nil)
                      .nil)
                    (.node 211106333200400
                      (.node 211106333200384
                        .nil
                        .nil)
                      .nil))
                  (.node 211106837041177
                    (.node 211106837041160
                      (.node 211106837041152
                        .nil
                        .nil)
                      .nil)
                    (.node 211106837041194
                      .nil
                      .nil)))
                (.node 211107977891848
                  (.node 211107977367615
                    (.node 211107977367577
                      (.node 211107977367552
                        .nil
                        .nil)
                      .nil)
                    (.node 211107977891840
                      .nil
                      .nil))
                  (.node 211108010921984
                    (.node 211107990999040
                      (.node 211107977891882
                        .nil
                        .nil)
                      .nil)
                    (.node 211109118738432
                      .nil
                      .nil))))
              (.node 211110527504384
                (.node 211109118914560
                  (.node 211109118742536
                    (.node 211109118742528
                      (.node 211109118738495
                        .nil
                        .nil)
                      .nil)
                    (.node 211109118742553
                      .nil
                      .nil))
                  (.node 211110527500288
                    (.node 211110259593216
                      (.node 211109119000576
                        .nil
                        .nil)
                      .nil)
                    (.node 211110527500351
                      .nil
                      .nil)))
                (.node 211110528028672
                  (.node 211110528024576
                    (.node 211110527762432
                      (.node 211110527504409
                        .nil
                        .nil)
                      .nil)
                    (.node 211110528024618
                      .nil
                      .nil))
                  (.node 211110541135872
                    (.node 211110528200704
                      (.node 211110528028680
                        .nil
                        .nil)
                      .nil)
                    (.node 211110561054720
                      .nil
                      .nil))))))))))

def tokenMember (x : Nat) : Bool := tokenTreeLookup x tokenTree

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma token_tree_codes : tokenTreeValues tokenTree = tokenCodes := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma token_chunk_checked_0 :
    tokenChunk0.all (fun s => (tokenNext s).all tokenMember && !(tokenActive s).contains 56) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma token_chunk_checked_1 :
    tokenChunk1.all (fun s => (tokenNext s).all tokenMember && !(tokenActive s).contains 56) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma token_chunk_checked_2 :
    tokenChunk2.all (fun s => (tokenNext s).all tokenMember && !(tokenActive s).contains 56) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma token_chunk_checked_3 :
    tokenChunk3.all (fun s => (tokenNext s).all tokenMember && !(tokenActive s).contains 56) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma token_chunk_checked_4 :
    tokenChunk4.all (fun s => (tokenNext s).all tokenMember && !(tokenActive s).contains 56) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma token_chunk_checked_5 :
    tokenChunk5.all (fun s => (tokenNext s).all tokenMember && !(tokenActive s).contains 56) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma token_chunk_checked_6 :
    tokenChunk6.all (fun s => (tokenNext s).all tokenMember && !(tokenActive s).contains 56) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma token_chunk_checked_7 :
    tokenChunk7.all (fun s => (tokenNext s).all tokenMember && !(tokenActive s).contains 56) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma token_chunk_checked_8 :
    tokenChunk8.all (fun s => (tokenNext s).all tokenMember && !(tokenActive s).contains 56) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma token_chunk_checked_9 :
    tokenChunk9.all (fun s => (tokenNext s).all tokenMember && !(tokenActive s).contains 56) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma token_chunk_checked_10 :
    tokenChunk10.all (fun s => (tokenNext s).all tokenMember && !(tokenActive s).contains 56) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma token_chunk_checked_11 :
    tokenChunk11.all (fun s => (tokenNext s).all tokenMember && !(tokenActive s).contains 56) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma token_chunk_checked_12 :
    tokenChunk12.all (fun s => (tokenNext s).all tokenMember && !(tokenActive s).contains 56) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma token_chunk_checked_13 :
    tokenChunk13.all (fun s => (tokenNext s).all tokenMember && !(tokenActive s).contains 56) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma token_chunk_checked_14 :
    tokenChunk14.all (fun s => (tokenNext s).all tokenMember && !(tokenActive s).contains 56) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma token_chunk_checked_15 :
    tokenChunk15.all (fun s => (tokenNext s).all tokenMember && !(tokenActive s).contains 56) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma token_chunk_checked_16 :
    tokenChunk16.all (fun s => (tokenNext s).all tokenMember && !(tokenActive s).contains 56) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma token_chunk_checked_17 :
    tokenChunk17.all (fun s => (tokenNext s).all tokenMember && !(tokenActive s).contains 56) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma token_chunk_checked_18 :
    tokenChunk18.all (fun s => (tokenNext s).all tokenMember && !(tokenActive s).contains 56) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma token_chunk_checked_19 :
    tokenChunk19.all (fun s => (tokenNext s).all tokenMember && !(tokenActive s).contains 56) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma token_chunk_checked_20 :
    tokenChunk20.all (fun s => (tokenNext s).all tokenMember && !(tokenActive s).contains 56) = true := by
  decide +kernel

lemma token_checked :
    tokenCodes.all (fun s => (tokenNext s).all tokenMember && !(tokenActive s).contains 56) = true := by
  simp only [tokenCodes, List.all_append, token_chunk_checked_0, token_chunk_checked_1, token_chunk_checked_2, token_chunk_checked_3, token_chunk_checked_4, token_chunk_checked_5, token_chunk_checked_6, token_chunk_checked_7, token_chunk_checked_8, token_chunk_checked_9, token_chunk_checked_10, token_chunk_checked_11, token_chunk_checked_12, token_chunk_checked_13, token_chunk_checked_14, token_chunk_checked_15, token_chunk_checked_16, token_chunk_checked_17, token_chunk_checked_18, token_chunk_checked_19, token_chunk_checked_20, Bool.and_self]

lemma token_closure_checked :
    tokenCodes.all (fun s => (tokenNext s).all tokenMember) = true := by
  apply List.all_eq_true.mpr
  intro s hs
  exact (Bool.and_eq_true_iff.mp (List.all_eq_true.mp token_checked s hs)).1

lemma token_no_target_checked :
    tokenCodes.all (fun s => !(tokenActive s).contains 56) = true := by
  apply List.all_eq_true.mpr
  intro s hs
  exact (Bool.and_eq_true_iff.mp (List.all_eq_true.mp token_checked s hs)).2

lemma token_start_mem : 63 ∈ tokenCodes := by decide +kernel

lemma token_overflow_not_mem : 281474976710656 ∉ tokenCodes := by decide +kernel

lemma token_member_sound {x : Nat} (hx : tokenMember x = true) : x ∈ tokenCodes := by
  have h := token_tree_lookup_sound tokenTree hx
  rwa [token_tree_codes] at h

lemma token_codes_closed {s t : Nat} (hs : s ∈ tokenCodes) (ht : t ∈ tokenNext s) :
    t ∈ tokenCodes := by
  have h := List.all_eq_true.mp token_closure_checked s hs
  exact token_member_sound (List.all_eq_true.mp h t ht)

lemma token_codes_no_target {s : Nat} (hs : s ∈ tokenCodes) : 56 ∉ tokenActive s := by
  have h := List.all_eq_true.mp token_no_target_checked s hs
  intro ht
  have htrue : (tokenActive s).contains 56 = true := List.contains_iff_mem.mpr ht
  rw [htrue] at h
  exact Bool.false_ne_true h

lemma token_reachable_no_threshold {s : Nat}
    (h : Relation.ReflTransGen (fun a b : Nat => b ∈ tokenNext a) 63 s) :
    56 ∉ tokenActive s := by
  have hs : s ∈ tokenCodes := by
    induction h with
    | refl => exact token_start_mem
    | tail _ hstep ih => exact token_codes_closed ih hstep
  exact token_codes_no_target hs

end PEqualNP.Outside.L_meta_2590_aux
