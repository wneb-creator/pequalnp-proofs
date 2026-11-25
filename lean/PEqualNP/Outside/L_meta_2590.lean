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

end DagTools

namespace DagTools

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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma paired_disjoint : ∀ i : Fin 10, Disjoint (side i) (side (opposite i)) := by
  unfold side opposite mask
  decide +kernel

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

end DagTools

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

end DagTools

namespace DagTools

def sem_W (n : ℕ) (D : Dag) (x : Fin n) : Finset (ℕ × Bool) := exitArcs n D (carrierT n D {x})

def sem_bar (e : ℕ × Bool) : ℕ × Bool := (e.1, !e.2)


section H3ResidualCodes

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

lemma sem_mem_W {x : Fin n} {e : ℕ × Bool} : e ∈ sem_W n D x ↔
    e.1 < D.length ∧ x ∈ supp n D (src D e) ∧ x ∉ supp n D (n + e.1) := sem_mem_exit1

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

end DagTools

namespace DagTools

section H3ForkRouting

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

lemma h3_sem_arm_or (hS : Strict n D) {x : Fin n}
    (hM : merges n D (carrierT n D {x}) = ∅) {a b : ℕ}
    (hab : sem_Arm n D {x} a b) : tag D (b - n) = false := by
  obtain ⟨hb, hnb, _⟩ := hab.1
  have he : n + (b - n) = b := by omega
  apply (sem_zm_gate hS hM (j := b - n) (by omega) ?_).1
  rw [he]
  exact (hab.2.2 x (by simp)).2

end H3ForkRouting

end DagTools

namespace DagTools

end DagTools





namespace DagTools

end DagTools

namespace DagTools

section H3OrPaths

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

def h3_OrStep (n : ℕ) (D : Dag) (a b : ℕ) : Prop :=
  sem_step n D a b ∧ tag D (b - n) = false

lemma h3_sem_route_or_path (hS : Strict n D) {x : Fin n}
    (hM : merges n D (carrierT n D {x}) = ∅) {r j : ℕ}
    (hj : j ∈ readers D r) {e : ℕ × Bool} (he : e ∈ sem_W n D x)
    (hp : (e.1 = j ∧ src D e = r) ∨
      Relation.ReflTransGen (sem_Arm n D {x}) (n + j) (src D e)) :
    Relation.ReflTransGen (h3_OrStep n D) r (src D e) := by
  rcases hp with ⟨_, heq⟩ | hp
  · rw [heq]
  · have hxstart : x ∈ supp n D (n + j) := by
      rcases Relation.ReflTransGen.cases_head hp with heq | ⟨c, hac, hcb⟩
      · rw [heq]
        exact (sem_mem_W.mp he).2.1
      · exact (hac.2.2 x (by simp)).1
    have hj' := Finset.mem_filter.mp hj
    have hjl := Finset.mem_range.mp hj'.1
    have hstep : sem_step n D r (n + j) := by
      refine ⟨by omega, by omega, ?_⟩
      simpa only [Nat.add_sub_cancel_left] using hj'.2
    have hfirst : h3_OrStep n D r (n + j) := by
      refine ⟨hstep, ?_⟩
      simpa only [Nat.add_sub_cancel_left] using (sem_zm_gate hS hM hjl hxstart).1
    apply Relation.ReflTransGen.head hfirst
    exact sem_rtg_mono (fun _ _ hab => ⟨hab.1, h3_sem_arm_or hS hM hab⟩) hp

end H3OrPaths

end DagTools

namespace DagTools

section H3OrPathSupport

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

lemma h3_or_path_support_subset (hS : Strict n D) {a b : ℕ}
    (hp : Relation.ReflTransGen (h3_OrStep n D) a b) : supp n D a ⊆ supp n D b := by
  induction hp with
  | refl => exact Finset.Subset.refl _
  | @tail b c hab hbc ih =>
    obtain ⟨hc, hnc, hop⟩ := hbc.1
    have he : n + (c - n) = c := by omega
    have hs := sem_supp_or hS (j := c - n) (by omega) hbc.2
    rw [he] at hs
    rw [hs]
    rcases hop with hA | hB
    · exact ih.trans (hA ▸ Finset.subset_union_left)
    · exact ih.trans (hB ▸ Finset.subset_union_right)

end H3OrPathSupport

end DagTools

namespace DagTools

section H3ResidualPaths
variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

lemma h3_two_arms_or_paths (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (X : Finset (Fin n)) (hX : X.Nonempty)
    (hM : ∀ x ∈ X, merges n D (carrierT n D {x}) = ∅) (r : ℕ)
    (hr : ∀ x ∈ X, x ∈ supp n D r) (hf : 2 ≤ fanout D r)
    (hlow : ∀ x ∈ X, ∀ w, r < w → x ∈ supp n D w → fanout D w ≤ 1) :
    ∃ P Q : ℕ × Bool, P.1 ≠ Q.1 ∧
      (∀ x ∈ X, P ∈ sem_W n D x ∧ Q ∈ sem_W n D x) ∧
      Relation.ReflTransGen (h3_OrStep n D) r (src D P) ∧
      Relation.ReflTransGen (h3_OrStep n D) r (src D Q) := by
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
  have hdistinct : P.1 ≠ Q.1 := by
    intro hPQ
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
  refine ⟨P, Q, hdistinct, fun x hx => ⟨hP1 x hx, hQ1 x hx⟩, ?_, ?_⟩
  · apply h3_sem_route_or_path hS (hM x0 hx0) hj1 (hP1 x0 hx0)
    rcases hP2 with hp | hp
    · exact Or.inl hp
    · exact Or.inr (sem_rtg_mono (fun _ _ hab =>
        ⟨hab.1, hab.2.1, fun x hx => by
          have he : x = x0 := Finset.mem_singleton.mp hx
          subst x
          exact hab.2.2 x0 hx0⟩) hp)
  · apply h3_sem_route_or_path hS (hM x0 hx0) hj2 (hQ1 x0 hx0)
    rcases hQ2 with hp | hp
    · exact Or.inl hp
    · exact Or.inr (sem_rtg_mono (fun _ _ hab =>
        ⟨hab.1, hab.2.1, fun x hx => by
          have he : x = x0 := Finset.mem_singleton.mp hx
          subst x
          exact hab.2.2 x0 hx0⟩) hp)

lemma h3_common_terminals_actual_paths (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (b : Fin n → ℕ) (hb : sem_MinBranch n D b) (hone : Bplus n D = (eligSet n D).card + 1)
    (X : Finset (Fin n)) (hX : X.Nonempty) (hsat : ∀ x ∈ X, 3 ≤ (sem_W n D x).card) :
    ∃ u0 : (Σ _ : ℕ, ℕ), ∃ P Q : ℕ × Bool, residualUnits n D b = {u0} ∧
      P.1 ≠ Q.1 ∧ (∀ x ∈ X, P ∈ sem_W n D x ∧ Q ∈ sem_W n D x) ∧
      Relation.ReflTransGen (h3_OrStep n D) u0.1 (src D P) ∧
      Relation.ReflTransGen (h3_OrStep n D) u0.1 (src D Q) ∧
      supp n D u0.1 ⊆ supp n D (src D P) ∩ supp n D (src D Q) := by
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
  have hlow : ∀ x ∈ X, ∀ w, u0.1 < w → x ∈ supp n D w → fanout D w ≤ 1 := by
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
  obtain ⟨P, Q, hPQ, hW, hP, hQ⟩ := h3_two_arms_or_paths hG h hC X hX
    (fun x hx => (sem_saturated hG h hC b hbp hres (hsat x hx)).2.1)
    u0.1 (fun x hx => (sem_saturated hG h hC b hbp hres (hsat x hx)).2.2.2) hfr hlow
  refine ⟨u0, P, Q, hres, hPQ, hW, hP, hQ, ?_⟩
  exact Finset.subset_inter (h3_or_path_support_subset hS hP) (h3_or_path_support_subset hS hQ)

end H3ResidualPaths


end DagTools

namespace DagTools

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
  · cases tag D j <;> simp [src, gop, Bool.and_comm, Bool.or_comm]

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

end DagTools

namespace H3CoStar
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

end H3CoStar

namespace DagTools

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
lemma h3_petersen_zero_neighbors : ∀ a : Fin 10,
    petersenAdj 0 a ↔ a ∈ ({1, 4, 5} : Finset (Fin 10)) := by
  unfold petersenAdj
  decide +kernel

end DagTools

namespace DagTools

def h3_star0Exposure (x y : Fin 10) : Finset (Fin 10) :=
  let m := ([
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 20, 104, 20, 36, 80, 208, 276, 548,
    0, 2, 0, 10, 18, 34, 104, 130, 258, 514,
    0, 18, 20, 0, 16, 36, 80, 144, 258, 548,
    0, 10, 548, 10, 0, 40, 104, 138, 770, 514,
    0, 130, 276, 138, 144, 0, 208, 130, 258, 770,
    0, 2, 276, 10, 18, 34, 0, 130, 258, 514,
    0, 34, 20, 40, 20, 32, 96, 0, 276, 514,
    0, 10, 36, 10, 48, 32, 80, 138, 0, 544,
    0, 18, 20, 104, 16, 48, 80, 130, 272, 0] : List ℕ).getD (10 * x.val + y.val) 0
  Finset.univ.filter (fun a => m.testBit a.val = true)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma h3_star0Exposure_spec : ∀ x : Fin 10, x ≠ 0 → ∀ y : Fin 10, y ≠ 0 → y ≠ x →
    (∀ a ∈ h3_star0Exposure x y, ∀ b ∈ h3_star0Exposure x y, ¬ petersenAdj a b) ∧
      y ∈ h3_star0Exposure x y ∧
      (∃ a ∈ h3_star0Exposure x y, a ∈ ({1, 4, 5} : Finset (Fin 10))) ∧
      ∃ a ∈ h3_star0Exposure x y, petersenAdj x a := by
  unfold h3_star0Exposure petersenAdj
  decide +kernel

lemma h3_petersen_any_other_exit_pure {D : Dag} (hS : Strict 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    {x : Fin 10} (hx : x ≠ 0) {e f : ℕ × Bool}
    (hW : exitArcs 10 D (carrierT 10 D {x}) ⊆ {e, f})
    (hf : f ∈ exitArcs 10 D (carrierT 10 D {x}))
    (hSub : ({1, 4, 5} : Finset (Fin 10)) ⊆ supp 10 D (src D e)) :
    supp 10 D (src D f) = {x} := by
  apply sem_two_exit_other_pure petersen_graph_ok hS hC hx hz hW hf hSub
  intro y hy0 hyx
  exact ⟨h3_star0Exposure x y, h3_star0Exposure_spec x hx y hy0 hyx⟩


end DagTools

namespace DagTools

lemma h3_star0_two_exit_completion {D : Dag} (hS : Strict 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    {x : Fin 10} (hx : x ≠ 0) {e : ℕ × Bool}
    (he : e ∈ exitArcs 10 D (carrierT 10 D {x}))
    (hbar : supp 10 D (src D (e.1, !e.2)) = {0})
    (hN : ({1, 4, 5} : Finset (Fin 10)) ⊆ supp 10 D (src D e))
    (hc : (exitArcs 10 D (carrierT 10 D {x})).card ≤ 2) :
    ∃ f : ℕ × Bool, f ≠ e ∧ exitArcs 10 D (carrierT 10 D {x}) = {e, f} ∧
      supp 10 D (src D f) = {x} ∧
      ∀ y : Fin 10, petersenAdj x y → y ≠ 0 →
        (f.1, !f.2) ∈ exitArcs 10 D (carrierT 10 D {y}) := by
  have ha : ∀ b : Fin 10, ∃ a ∈ ({1, 4, 5} : Finset (Fin 10)), a ≠ b := by decide
  obtain ⟨a, haN, hax⟩ := ha x
  have hlo := sem_nonpure_exit_card petersen_graph_ok hS hC he (hN haN) hax
  have hcard : (exitArcs 10 D (carrierT 10 D {x})).card = 2 := by omega
  have herase : ((exitArcs 10 D (carrierT 10 D {x})).erase e).card = 1 := by
    rw [Finset.card_erase_of_mem he, hcard]
  obtain ⟨f, hf⟩ := Finset.card_eq_one.mp herase
  have hfm : f ∈ (exitArcs 10 D (carrierT 10 D {x})).erase e := by rw [hf]; simp
  obtain ⟨hne, hfW⟩ := Finset.mem_erase.mp hfm
  have hWeq : exitArcs 10 D (carrierT 10 D {x}) = {e, f} := by
    rw [← Finset.insert_erase he, hf]
  have hWsub : exitArcs 10 D (carrierT 10 D {x}) ⊆ {e, f} := by rw [hWeq]
  refine ⟨f, hne, hWeq, h3_petersen_any_other_exit_pure hS hC hz hx hWsub hfW hN, ?_⟩
  intro y hxy hy0
  exact sem_two_exit_remaining_slot petersen_graph_ok hS hC hWsub hbar hxy hy0

lemma h3_star0_extra_label_forces_full_star {D : Dag} (hS : Strict 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    {x : Fin 10} (hx : x ≠ 0) (hxN : x ∉ ({1, 4, 5} : Finset (Fin 10))) {e : ℕ × Bool}
    (he : e ∈ exitArcs 10 D (carrierT 10 D {x}))
    (hbar : supp 10 D (src D (e.1, !e.2)) = {0})
    (hN : ({1, 4, 5} : Finset (Fin 10)) ⊆ supp 10 D (src D e))
    (hc : (exitArcs 10 D (carrierT 10 D {x})).card ≤ 2) :
    ∃ f : ℕ × Bool, f ≠ e ∧ exitArcs 10 D (carrierT 10 D {x}) = {e, f} ∧
      supp 10 D (src D f) = {x} ∧
      ∀ y : Fin 10, petersenAdj x y →
        (f.1, !f.2) ∈ exitArcs 10 D (carrierT 10 D {y}) := by
  obtain ⟨f, hfe, hW, hsrc, hrest⟩ := h3_star0_two_exit_completion hS hC hz hx he hbar hN hc
  refine ⟨f, hfe, hW, hsrc, ?_⟩
  intro y hxy
  apply hrest y hxy
  intro hy0
  subst y
  exact hxN ((h3_petersen_zero_neighbors x).mp (petersen_graph_ok.1 x 0 hxy))


end DagTools

namespace DagTools

lemma h3_all_two_petersen_five_groups {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hc : ∀ x : Fin 10, x ≠ 0 → (exitArcs 10 D (carrierT 10 D {x})).card = 2) :
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


lemma h3_all_two_sources_exist {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hc : ∀ x : Fin 10, x ≠ 0 → (exitArcs 10 D (carrierT 10 D {x})).card = 2) :
    ∃ r : Fin 10 → ℕ × Bool, Function.Injective r ∧
      (∀ i, r (SideGeometry.opposite i) = ((r i).1, !(r i).2)) ∧
      (∀ i, supp 10 D (src D (r i)) = SideGeometry.side i) ∧
      ∀ x : Fin 10, exitArcs 10 D (carrierT 10 D {x}) =
        (Finset.univ.filter (fun i : Fin 10 => x ∈ SideGeometry.side i)).image r := by
  obtain ⟨e0, e1, e4, e5, d, _, _, _, _, hW0, hW1, hW2, hW3, hW4,
    hW5, hW6, hW7, hW8, hW9⟩ := h3_all_two_petersen_five_groups h hC hz hc
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


end DagTools

namespace DagTools

lemma h3_indexed_and_equal_or_pair {D : Dag} (hS : Strict 10 D)
    (r : Fin 10 → ℕ × Bool)
    (hW : ∀ x : Fin 10, exitArcs 10 D (carrierT 10 D {x}) =
      (Finset.univ.filter (fun i : Fin 10 => x ∈ SideGeometry.side i)).image r)
    (hopp : ∀ i : Fin 10, r (SideGeometry.opposite i) = ((r i).1, !(r i).2))
    (hsources : ∀ i, supp 10 D (src D (r i)) = SideGeometry.side i)
    {j : ℕ} (hj : j < D.length) (ht : tag D j = true) :
    (∃ i : Fin 10, r i = (j, false) ∧
      supp 10 D (opA D j) = SideGeometry.side i ∧
      supp 10 D (opB D j) = SideGeometry.side (SideGeometry.opposite i)) ∨
      supp 10 D (opA D j) = supp 10 D (opB D j) := by
  classical
  by_cases he : ∃ i : Fin 10, r i = (j, false)
  · obtain ⟨i, hi⟩ := he
    have hother : r (SideGeometry.opposite i) = (j, true) := by
      rw [hopp, hi]
      rfl
    left
    refine ⟨i, hi, ?_, ?_⟩
    · simpa only [hi, sb_src_false] using hsources i
    · simpa only [hother, sb_src_true] using hsources (SideGeometry.opposite i)
  · right
    apply Finset.Subset.antisymm
    · intro x hx
      by_contra hn
      have hex : (j, false) ∈ exitArcs 10 D (carrierT 10 D {x}) := by
        apply sem_mem_exit1.mpr
        refine ⟨hj, by simpa only [sb_src_false] using hx, ?_⟩
        rw [sem_supp_and hS hj ht, Finset.mem_inter]
        exact fun hh => hn hh.2
      rw [hW] at hex
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hex
      exact he ⟨i, hi⟩
    · intro x hx
      by_contra hn
      have hex : (j, true) ∈ exitArcs 10 D (carrierT 10 D {x}) := by
        apply sem_mem_exit1.mpr
        refine ⟨hj, by simpa only [sb_src_true] using hx, ?_⟩
        rw [sem_supp_and hS hj ht, Finset.mem_inter]
        exact fun hh => hn hh.1
      rw [hW] at hex
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hex
      apply he
      refine ⟨SideGeometry.opposite i, ?_⟩
      rw [hopp, hi]
      rfl

lemma h3_indexed_exact_gate_valid {D : Dag} (hS : Strict 10 D)
    (r : Fin 10 → ℕ × Bool)
    (hW : ∀ x : Fin 10, exitArcs 10 D (carrierT 10 D {x}) =
      (Finset.univ.filter (fun i : Fin 10 => x ∈ SideGeometry.side i)).image r)
    (hopp : ∀ i : Fin 10, r (SideGeometry.opposite i) = ((r i).1, !(r i).2))
    (hsources : ∀ i, supp 10 D (src D (r i)) = SideGeometry.side i) (i : Fin 10) :
    (r i).1 < D.length ∧ tag D (r i).1 = true ∧ supp 10 D (10 + (r i).1) = ∅ := by
  obtain ⟨x, hx⟩ := SideGeometry.side_nonempty i
  have hex : r i ∈ exitArcs 10 D (carrierT 10 D {x}) := by
    rw [hW]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hx⟩, rfl⟩
  have hj := (sem_mem_exit1.mp hex).1
  have ht := h3_exit_tag_and hS hex
  refine ⟨hj, ht, ?_⟩
  have ha := hsources i
  have hb := hsources (SideGeometry.opposite i)
  rw [hopp] at hb
  have hdis := SideGeometry.paired_disjoint i
  rw [sem_supp_and hS hj ht]
  cases hs : (r i).2
  · have hA : supp 10 D (opA D (r i).1) = SideGeometry.side i := by simpa [src, hs] using ha
    have hB : supp 10 D (opB D (r i).1) = SideGeometry.side (SideGeometry.opposite i) := by simpa [src, hs] using hb
    rw [hA, hB]
    exact Finset.disjoint_iff_inter_eq_empty.mp hdis
  · have hA : supp 10 D (opA D (r i).1) = SideGeometry.side (SideGeometry.opposite i) := by simpa [src, hs] using hb
    have hB : supp 10 D (opB D (r i).1) = SideGeometry.side i := by simpa [src, hs] using ha
    rw [hA, hB]
    exact Finset.disjoint_iff_inter_eq_empty.mp hdis.symm

lemma h3_all_two_typed_sources_exist {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hc : ∀ x : Fin 10, x ≠ 0 → (exitArcs 10 D (carrierT 10 D {x})).card = 2) :
    ∃ r : Fin 10 → ℕ × Bool, Function.Injective r ∧
      (∀ i, r (SideGeometry.opposite i) = ((r i).1, !(r i).2)) ∧
      (∀ i, supp 10 D (src D (r i)) = SideGeometry.side i) ∧
      (∀ x : Fin 10, exitArcs 10 D (carrierT 10 D {x}) =
        (Finset.univ.filter (fun i : Fin 10 => x ∈ SideGeometry.side i)).image r) ∧
      (∀ i : Fin 10, (r i).1 < D.length ∧ tag D (r i).1 = true ∧
        supp 10 D (10 + (r i).1) = ∅) ∧
      ∀ j, j < D.length → tag D j = true →
        (∃ i : Fin 10, r i = (j, false) ∧
          supp 10 D (opA D j) = SideGeometry.side i ∧
          supp 10 D (opB D j) = SideGeometry.side (SideGeometry.opposite i)) ∨
        supp 10 D (opA D j) = supp 10 D (opB D j) := by
  obtain ⟨r, hinj, hopp, hsources, hW⟩ := h3_all_two_sources_exist h hC hz hc
  exact ⟨r, hinj, hopp, hsources, hW, h3_indexed_exact_gate_valid h.1 r hW hopp hsources,
    fun _ hj ht => h3_indexed_and_equal_or_pair h.1 r hW hopp hsources hj ht⟩


end DagTools



namespace R1FlexibleResource.CausalBarrier

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
  [({0}, {1, 4, 5}), ({1}, {2, 6}), ({4}, {3, 9}), ({5}, {7, 8}), (∅, ∅),
   ({1}, {2}), ({1}, {6}), ({1}, ∅), ({2}, ∅), ({2, 6}, ∅), ({3, 6}, ∅)]

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

end R1FlexibleResource.CausalBarrier

namespace R1FlexibleResource.ResourceExclusion

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
  ((a.1 = b.1 ∨ ((a.1, b.1) ∈ OtherSides ∨ (b.1, a.1) ∈ OtherSides)) ∨
    ((a.1.Nonempty ∧ a.1 ⊆ b.1) ∨ (b.1.Nonempty ∧ b.1 ⊆ a.1))) ∨
  ((a.1 = ∅ ∧ ∀ E ∈ CrossPairs, b.2 E = true) ∨
    (b.1 = ∅ ∧ ∀ E ∈ CrossPairs, a.2 E = true))

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

lemma rsafe_meet_same {E T : Finset (Fin 10)} {a b : Resource}
    (hab : a.1 = b.1) (ha : RSafe E T a) : RSafe E T (RMeet a b) := by
  intro ht
  have hat : a.2 E = true := (Bool.and_eq_true_iff.mp ht).1
  have hh := ha hat
  change ((a.1 ∩ b.1) ∩ T).Nonempty
  simpa only [← hab, Finset.inter_self] using hh

lemma rsafe_meet_left_subset {E T : Finset (Fin 10)} {a b : Resource}
    (hab : a.1 ⊆ b.1) (ha : RSafe E T a) : RSafe E T (RMeet a b) := by
  intro ht
  have hat : a.2 E = true := (Bool.and_eq_true_iff.mp ht).1
  have hh := ha hat
  change ((a.1 ∩ b.1) ∩ T).Nonempty
  simpa only [Finset.inter_eq_left.mpr hab] using hh

lemma rsafe_meet_right_subset {E T : Finset (Fin 10)} {a b : Resource}
    (hba : b.1 ⊆ a.1) (hb : RSafe E T b) : RSafe E T (RMeet a b) := by
  intro ht
  have hbt : b.2 E = true := (Bool.and_eq_true_iff.mp ht).2
  have hh := hb hbt
  change ((a.1 ∩ b.1) ∩ T).Nonempty
  simpa only [Finset.inter_eq_right.mpr hba] using hh

lemma allowed_sides_swap {a b : Resource} (hs : AllowedSides a b) : AllowedSides b a := by
  rcases hs with hs | hs
  · left
    rcases hs with hs | hs | hs
    · rcases hs with heq | hp
      · exact Or.inl (Or.inl heq.symm)
      · exact Or.inl (Or.inr (Or.symm hp))
    · exact Or.inr (Or.inr hs)
    · exact Or.inr (Or.inl hs)
  · exact Or.inr (Or.symm hs)

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
  rcases hs with hs | hs
  · rcases hs with hs | hs | hs
    · rcases hs with heq | hs
      · exact rsafe_meet_same heq (ha E hE)
      · apply rsafe_meet (ha E hE) (hb E hE)
        rcases hs with hs | hs
        · exact (cross_separation E hE _ hs).1
        · exact (cross_separation E hE _ hs).2
    · exact rsafe_meet_left_subset hs.2 (ha E hE)
    · exact rsafe_meet_right_subset hs.2 (hb E hE)
  · apply rsafe_meet (ha E hE) (hb E hE)
    rcases hs with hs | hs
    · simp [Separates, hs.1]
    · simp [Separates, hs.1]

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
    · rcases hside with hside | hside
      · rcases hside with hside | hside | hside
        · rcases hside with heq | hside
          · exact rsafe_meet_same heq ha
          · apply rsafe_meet ha hb
            rcases hside with hside | hside
            · exact (hT _ hside).1
            · exact (hT _ hside).2
        · exact rsafe_meet_left_subset hside.2 ha
        · exact rsafe_meet_right_subset hside.2 hb
      · apply rsafe_meet ha hb
        rcases hside with hs | hs
        · simp [Separates, hs.1]
        · simp [Separates, hs.1]
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
    (∃ E ∈ DirtyEdges, b.1 ∩ E = ∅) ∨ (∀ E ∈ CrossPairs, b.2 E = true) := by
  rcases hs with hs | hs
  · left
    rcases hs with hs | hs | hs
    · rcases hs with heq | hs
      · refine ⟨UniversalEdge 0, universal_edge_valid 0, ?_⟩
        rw [← heq, ha]
        simp
      · have hzero : ∀ AB ∈ OtherSides,
            (AB.1 = ∅ → ∃ E ∈ DirtyEdges, AB.2 ∩ E = ∅) ∧
            (AB.2 = ∅ → ∃ E ∈ DirtyEdges, AB.1 ∩ E = ∅) := by
          simp [OtherSides, DirtyEdges]
        rcases hs with hs | hs
        · exact (hzero _ hs).1 ha
        · exact (hzero _ hs).2 ha
    · have hn := hs.1
      rw [ha] at hn
      exact False.elim (Finset.not_nonempty_empty hn)
    · have hn := hs.1.mono hs.2
      rw [ha] at hn
      exact False.elim (Finset.not_nonempty_empty hn)
  · rcases hs with hs | hs
    · exact Or.inr hs.2
    · left
      refine ⟨UniversalEdge 0, universal_edge_valid 0, ?_⟩
      simp [hs.1]

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
  · rcases zero_side_of_allowed hd hs with hmiss | hfull
    · left
      obtain ⟨E, hE, hdisj⟩ := hmiss
      have hcross := dirty_mem_cross E hE
      refine ⟨E, hE, E, cross_separation E hcross, ?_⟩
      have hc : RSafe E E (RMeet d b) := by
        intro ht
        have hbt : b.2 E = true := (Bool.and_eq_true_iff.mp ht).2
        have hh := hb E hcross hbt
        rw [hdisj] at hh
        exact False.elim (Finset.not_nonempty_empty hh)
      have hpool : AllOrdinary (Keep d + Keep b + rest) := by
        apply allOrdinary_add
        · apply allOrdinary_add
          · intro w hw
            simp [Keep, hd] at hw
          · exact keep_ordinary hb
        · exact hr
      intro w hw
      rcases Multiset.mem_cons.mp hw with rfl | hw
      · exact hc
      · exact hpool w hw E hcross
    · right
      refine ⟨RMeet d b, Keep d + Keep b + rest, rfl, ?_, ?_, ?_⟩
      · simp [RMeet, hd]
      · intro E hE
        simp [RMeet, hdt E hE, hfull E hE]
      · apply allOrdinary_add
        · apply allOrdinary_add
          · intro w hw
            simp [Keep, hd] at hw
          · exact keep_ordinary hb
        · exact hr


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
          exact ⟨allowed_sides_swap hs, hc.trans (rmeet_swap _ _)⟩
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

end R1FlexibleResource.ResourceExclusion

namespace R1FlexibleResource.IndexSchedule

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

end R1FlexibleResource.IndexSchedule
namespace R1FlexibleResource.DAGBridge

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

lemma h3_full_side_resource_true {D : Dag} (hS : Strict 10 D) {w : ℕ}
    (hfull : DirtyA ⊆ supp 10 D w ∨ DirtyB ⊆ supp 10 D w)
    (E : Finset (Fin 10)) (hE : E ∈ CrossPairs) : (DagResource D w).2 E = true := by
  have hh := cross_hits E hE
  apply support_hit_true hS
  rcases hfull with hfull | hfull
  · obtain ⟨v, hv⟩ := hh.1
    exact ⟨v, Finset.mem_inter.mpr ⟨hfull (Finset.mem_inter.mp hv).1, (Finset.mem_inter.mp hv).2⟩⟩
  · obtain ⟨v, hv⟩ := hh.2
    exact ⟨v, Finset.mem_inter.mpr ⟨hfull (Finset.mem_inter.mp hv).1, (Finset.mem_inter.mp hv).2⟩⟩


lemma h3_full_side_allowed_left {D : Dag} (hS : Strict 10 D) {u v : ℕ}
    (hu : supp 10 D u = ∅)
    (hv : DirtyA ⊆ supp 10 D v ∨ DirtyB ⊆ supp 10 D v) :
    AllowedSides (DagResource D u) (DagResource D v) := by
  exact Or.inr (Or.inl ⟨hu, h3_full_side_resource_true hS hv⟩)

lemma h3_full_side_allowed_right {D : Dag} (hS : Strict 10 D) {u v : ℕ}
    (hv : supp 10 D v = ∅)
    (hu : DirtyA ⊆ supp 10 D u ∨ DirtyB ⊆ supp 10 D u) :
    AllowedSides (DagResource D u) (DagResource D v) := by
  exact Or.inr (Or.inr ⟨hv, h3_full_side_resource_true hS hu⟩)

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

end R1FlexibleResource.DAGBridge

namespace DagTools

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma h3_r1_flexible_allowed_sides_exclusion {D : Dag} (hS : Strict 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hB : Bzero 10 D = 0)
    {g : ℕ} (hg : g < D.length) (hgt : tag D g = true)
    (hdirty : R1FlexibleResource.DAGBridge.DirtySides D g)
    (hother : R1FlexibleResource.DAGBridge.OtherAndSides D g) : False := by
  apply R1FlexibleResource.DAGBridge.canonical_dag_exclusion hS hB hg hgt hdirty hother
    (outW 10 D) (by unfold outW; omega)
  refine ⟨sem_supp_out petersen_graph_ok hC, ?_, ?_⟩
  · intro E hE
    have hedges : ∀ E ∈ R1FlexibleResource.CausalBarrier.DirtyEdges,
        sem_Edge petersenAdj (sem_ind E) := by
      unfold R1FlexibleResource.CausalBarrier.DirtyEdges sem_Edge petersenAdj sem_ind
      decide +kernel
    exact (hC _).mpr (hedges E hE)
  · apply Bool.eq_false_iff.mpr
    intro ht
    have hbad : ¬ sem_Edge petersenAdj (sem_ind ({3, 9} : Finset (Fin 10))) := by
      unfold sem_Edge petersenAdj sem_ind
      decide +kernel
    exact hbad ((hC _).mp ht)

end DagTools

namespace DagTools

open R1FlexibleResource.CausalBarrier R1FlexibleResource.ResourceExclusion R1FlexibleResource.DAGBridge

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma h3_all_two_flexible_other_sides : ∀ i : Fin 10, i ≠ 8 → i ≠ 9 →
    (SideGeometry.side i, SideGeometry.side (SideGeometry.opposite i)) ∈ OtherSides ∨
    (SideGeometry.side (SideGeometry.opposite i), SideGeometry.side i) ∈ OtherSides := by
  unfold SideGeometry.side SideGeometry.mask SideGeometry.opposite OtherSides
  decide +kernel

lemma h3_all_two_bzero_exclusion {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hc : ∀ x : Fin 10, x ≠ 0 → (exitArcs 10 D (carrierT 10 D {x})).card = 2)
    (hB0 : Bzero 10 D = 0) : False := by
  obtain ⟨r, _, hopp, hsources, hW, hvalid, htypes⟩ := h3_all_two_typed_sources_exist h hC hz hc
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
    rcases htypes j hj ht with ⟨i, hi, hA, hB⟩ | hequal
    · left
      left
      right
      have hi8 : i ≠ 8 := by
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
      exact h3_all_two_flexible_other_sides i hi8 hi9
    · left
      left
      left
      exact hequal
  exact h3_r1_flexible_allowed_sides_exclusion h.1 hC hB0 (hvalid 8).1 (hvalid 8).2.1 hdirty hother


end DagTools

namespace DagTools

lemma h3_petersen_le_two_exit_card {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hle : ∀ x : Fin 10, (exitArcs 10 D (carrierT 10 D {x})).card ≤ 2) :
    ∀ x : Fin 10, x ≠ 0 → (exitArcs 10 D (carrierT 10 D {x})).card = 2 := by
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


lemma h3_all_le_two_bzero_exclusion {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hle : ∀ x : Fin 10, (exitArcs 10 D (carrierT 10 D {x})).card ≤ 2)
    (hB0 : Bzero 10 D = 0) : False :=
  h3_all_two_bzero_exclusion h hC hz (h3_petersen_le_two_exit_card h hC hz hle) hB0

lemma h3_bzero_has_three_exits {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hB0 : Bzero 10 D = 0) :
    ∃ x : Fin 10, x ≠ 0 ∧ 3 ≤ (exitArcs 10 D (carrierT 10 D {x})).card := by
  by_contra hno
  have hle : ∀ x : Fin 10, (exitArcs 10 D (carrierT 10 D {x})).card ≤ 2 := by
    intro x
    by_cases hx : x = 0
    · subst x
      obtain ⟨e, _, _, _, _, _, hW, _⟩ := sem_inelig_consumer petersen_graph_ok h hC hz
      rw [hW, Finset.card_singleton]
      decide
    · have hn : ¬ 3 ≤ (exitArcs 10 D (carrierT 10 D {x})).card :=
        fun hh => hno ⟨x, hx, hh⟩
      omega
  exact h3_all_le_two_bzero_exclusion h hC hz hle hB0


end DagTools

namespace DagTools

lemma h3_outside_le_two_nonzero_ge_two {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hle : ∀ x ∈ ({1, 4, 5} : Finset (Fin 10)), (exitArcs 10 D (carrierT 10 D {x})).card ≤ 2) :
    ∀ x : Fin 10, x ≠ 0 → 2 ≤ (exitArcs 10 D (carrierT 10 D {x})).card := by
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
    exact Nat.le_antisymm (hle x hx) hge
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
  · have hh := hn x hxN
    omega
  · exact hrest x hx hxN

lemma h3_four_bounds_except_one_ge_two {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hle : ∀ x ∈ ({3, 4, 5, 8} : Finset (Fin 10)),
      (exitArcs 10 D (carrierT 10 D {x})).card ≤ 2) :
    ∀ x : Fin 10, x ≠ 0 → x ≠ 1 → 2 ≤ (exitArcs 10 D (carrierT 10 D {x})).card := by
  obtain ⟨e0, he0, _, hp0, ho0, hn0, _, _⟩ := sem_inelig_consumer petersen_graph_ok h hC hz
  let A := h3_opp e0
  have hbar : supp 10 D (src D (A.1, !A.2)) = {0} := by simpa [A, h3_opp] using hp0
  have hAN : ({1, 4, 5} : Finset (Fin 10)) ⊆ supp 10 D (src D A) := by
    intro x hx
    apply hn0
    have hh : ∀ a ∈ ({1, 4, 5} : Finset (Fin 10)), petersenAdj 0 a := by
      unfold petersenAdj
      decide
    exact hh x hx
  have hAmem : ∀ x ∈ ({1, 4, 5} : Finset (Fin 10)), A ∈ exitArcs 10 D (carrierT 10 D {x}) := by
    intro x hx
    apply sem_mem_exit1.mpr
    exact ⟨he0, hAN hx, by rw [show 10 + A.1 = 10 + e0.1 from rfl, ho0]; simp⟩
  have hlo4 := sem_nonpure_exit_card petersen_graph_ok h.1 hC
    (hAmem 4 (by decide)) (hAN (by decide : (1 : Fin 10) ∈ ({1, 4, 5} : Finset (Fin 10)))) (by decide)
  have hlo5 := sem_nonpure_exit_card petersen_graph_ok h.1 hC
    (hAmem 5 (by decide)) (hAN (by decide : (1 : Fin 10) ∈ ({1, 4, 5} : Finset (Fin 10)))) (by decide)
  have hc4 := Nat.le_antisymm (hle 4 (by decide)) hlo4
  have hc5 := Nat.le_antisymm (hle 5 (by decide)) hlo5
  obtain ⟨e4, _, hW4⟩ := h3_pair_of_card_two (hAmem 4 (by decide)) hc4
  obtain ⟨e5, _, hW5⟩ := h3_pair_of_card_two (hAmem 5 (by decide)) hc5
  have hp4 : supp 10 D (src D e4) = {4} := petersen_other_exit_pure h.1 hC hz
    (by decide) (by rw [hW4]) (by rw [hW4]; simp) hAN
  have hp5 : supp 10 D (src D e5) = {5} := petersen_other_exit_pure h.1 hC hz
    (by decide) (by rw [hW5]) (by rw [hW5]; simp) hAN
  have hlo3 : 2 ≤ (exitArcs 10 D (carrierT 10 D {(3 : Fin 10)})).card :=
    sem_two_exit_neighbor_card petersen_graph_ok h.1 hC (by rw [hW4]) hbar
      (by unfold petersenAdj; decide) (by unfold petersenAdj; decide : petersenAdj 4 9)
      (by decide) (by decide) (by decide)
  have hlo9 : 2 ≤ (exitArcs 10 D (carrierT 10 D {(9 : Fin 10)})).card :=
    sem_two_exit_neighbor_card petersen_graph_ok h.1 hC (by rw [hW4]) hbar
      (by unfold petersenAdj; decide) (by unfold petersenAdj; decide : petersenAdj 4 3)
      (by decide) (by decide) (by decide)
  have hlo7 : 2 ≤ (exitArcs 10 D (carrierT 10 D {(7 : Fin 10)})).card :=
    sem_two_exit_neighbor_card petersen_graph_ok h.1 hC (by rw [hW5]) hbar
      (by unfold petersenAdj; decide) (by unfold petersenAdj; decide : petersenAdj 5 8)
      (by decide) (by decide) (by decide)
  have hlo8 : 2 ≤ (exitArcs 10 D (carrierT 10 D {(8 : Fin 10)})).card :=
    sem_two_exit_neighbor_card petersen_graph_ok h.1 hC (by rw [hW5]) hbar
      (by unfold petersenAdj; decide) (by unfold petersenAdj; decide : petersenAdj 5 7)
      (by decide) (by decide) (by decide)
  have ha3 : h3_opp e4 ∈ exitArcs 10 D (carrierT 10 D {(3 : Fin 10)}) :=
    sem_two_exit_remaining_slot petersen_graph_ok h.1 hC (by rw [hW4]) hbar
      (by unfold petersenAdj; decide) (by decide)
  have ha8 : h3_opp e5 ∈ exitArcs 10 D (carrierT 10 D {(8 : Fin 10)}) :=
    sem_two_exit_remaining_slot petersen_graph_ok h.1 hC (by rw [hW5]) hbar
      (by unfold petersenAdj; decide) (by decide)
  obtain ⟨g3, _, hW3⟩ := h3_pair_of_card_two ha3 (Nat.le_antisymm (hle 3 (by decide)) hlo3)
  obtain ⟨g8, _, hW8⟩ := h3_pair_of_card_two ha8 (Nat.le_antisymm (hle 8 (by decide)) hlo8)
  have hb3 : supp 10 D (src D ((h3_opp e4).1, !(h3_opp e4).2)) = {4} := by simpa [h3_opp] using hp4
  have hb8 : supp 10 D (src D ((h3_opp e5).1, !(h3_opp e5).2)) = {5} := by simpa [h3_opp] using hp5
  have hlo2 : 2 ≤ (exitArcs 10 D (carrierT 10 D {(2 : Fin 10)})).card :=
    sem_two_exit_neighbor_card petersen_graph_ok h.1 hC (by rw [hW3]) hb3
      (by unfold petersenAdj; decide) (by unfold petersenAdj; decide : petersenAdj 3 8)
      (by decide) (by decide) (by decide)
  have hlo6 : 2 ≤ (exitArcs 10 D (carrierT 10 D {(6 : Fin 10)})).card :=
    sem_two_exit_neighbor_card petersen_graph_ok h.1 hC (by rw [hW8]) hb8
      (by unfold petersenAdj; decide) (by unfold petersenAdj; decide : petersenAdj 8 3)
      (by decide) (by decide) (by decide)
  intro x hx0 hx1
  fin_cases x
  · exact (hx0 rfl).elim
  · exact (hx1 rfl).elim
  · exact hlo2
  · exact hlo3
  · exact hlo4
  · exact hlo5
  · exact hlo6
  · exact hlo7
  · exact hlo8
  · exact hlo9

lemma h3_singleton_two_other_exit_cards {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hu : ∀ x : Fin 10, x ≠ 0 → x ≠ 2 → (exitArcs 10 D (carrierT 10 D {x})).card ≤ 2) :
    ∀ x : Fin 10, x ≠ 0 → x ≠ 2 → (exitArcs 10 D (carrierT 10 D {x})).card = 2 := by
  have hfinite : ∀ x ∈ ({1, 4, 5} : Finset (Fin 10)), x ≠ 0 ∧ x ≠ 2 := by decide
  have hlo := h3_outside_le_two_nonzero_ge_two h hC hz
    (fun x hx => hu x (hfinite x hx).1 (hfinite x hx).2)
  exact fun x hx0 hx2 => Nat.le_antisymm (hu x hx0 hx2) (hlo x hx0)

lemma h3_singleton_one_other_exit_cards {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hu : ∀ x : Fin 10, x ≠ 0 → x ≠ 1 → (exitArcs 10 D (carrierT 10 D {x})).card ≤ 2) :
    ∀ x : Fin 10, x ≠ 0 → x ≠ 1 → (exitArcs 10 D (carrierT 10 D {x})).card = 2 := by
  have hfinite : ∀ x ∈ ({3, 4, 5, 8} : Finset (Fin 10)), x ≠ 0 ∧ x ≠ 1 := by decide
  have hlo := h3_four_bounds_except_one_ge_two h hC hz
    (fun x hx => hu x (hfinite x hx).1 (hfinite x hx).2)
  exact fun x hx0 hx1 => Nat.le_antisymm (hu x hx0 hx1) (hlo x hx0 hx1)

lemma h3_outside_saturated_le_two {D : Dag} {S : Finset (Fin 10)}
    (hS : h3_saturatedSet 10 D = S) {x : Fin 10} (hx : x ∉ S) :
    (exitArcs 10 D (carrierT 10 D {x})).card ≤ 2 := by
  by_contra hh
  apply hx
  rw [← hS]
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, by omega⟩

lemma h3_saturated_two_other_exit_cards {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hS : h3_saturatedSet 10 D = {2}) :
    ∀ x : Fin 10, x ≠ 0 → x ≠ 2 → (exitArcs 10 D (carrierT 10 D {x})).card = 2 :=
  h3_singleton_two_other_exit_cards h hC hz
    (fun x _ hx2 => h3_outside_saturated_le_two hS (by simpa only [Finset.mem_singleton] using hx2))

lemma h3_saturated_one_other_exit_cards {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hS : h3_saturatedSet 10 D = {1}) :
    ∀ x : Fin 10, x ≠ 0 → x ≠ 1 → (exitArcs 10 D (carrierT 10 D {x})).card = 2 :=
  h3_singleton_one_other_exit_cards h hC hz
    (fun x _ hx1 => h3_outside_saturated_le_two hS (by simpa only [Finset.mem_singleton] using hx1))


end DagTools

namespace S2Geometry

def side (i : Fin 11) : Finset (Fin 10) :=
  SideGeometry.mask (([1, 50, 2, 68, 16, 520, 32, 384, 200, 772, 4] : List Nat).getD i.val 0)

def allowed (i : Fin 11) : Finset (Fin 10) :=
  SideGeometry.mask (([1, 1023, 3, 68, 17, 520, 33, 384, 200, 772, 1023] : List Nat).getD i.val 0)

def witnessCode (i : Fin 11) (y : Fin 10) : Nat :=
  ([0, 2, 20, 10, 16, 32, 80, 130, 258, 514, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1044, 1128, 1044, 1060, 1104, 1232, 1300, 1572, 6529, 6154, 0, 6154, 6290, 6186, 0, 6274, 6528, 6664, 0, 4106, 4644, 4106, 0, 4136, 4200, 4234, 4866, 4610, 3141, 3218, 3140, 0, 3152, 3172, 3140, 3216, 3456, 0, 0, 5250, 5396, 5258, 5264, 0, 5328, 5250, 5378, 5890, 7237, 7210, 7236, 7208, 7252, 7208, 7236, 0, 0, 7688, 3589, 3842, 3588, 0, 6420, 3620, 0, 0, 3840, 3588, 8329, 8330, 0, 8328, 8400, 9320, 8384, 8328, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List Nat).getD (i.val * 10 + y.val) 0

def witnessVertex (i : Fin 11) (y : Fin 10) : Fin 10 :=
  ⟨witnessCode i y / 1024 % 10, Nat.mod_lt _ (by decide)⟩

def witnessSet (i : Fin 11) (y : Fin 10) : Finset (Fin 10) :=
  SideGeometry.mask (witnessCode i y % 1024)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma witness_valid : ∀ i : Fin 11, ∀ y : Fin 10, y ∉ allowed i →
    let x := witnessVertex i y
    let A := witnessSet i y
    x ∈ side i ∧ y ∈ A ∧
    (∀ u ∈ A, ∀ v ∈ A, ¬ SideGeometry.adj u v) ∧
    (∃ v ∈ A, SideGeometry.adj x v) ∧
    ∀ j : Fin 11, x ∈ side j → j ≠ i → (side j ∩ A).Nonempty := by
  unfold SideGeometry.adj
  decide +kernel

lemma support_bound (S : Fin 11 → Finset (Fin 10))
    (hsub : ∀ i, side i ⊆ S i)
    (hex : ∀ x A, (∀ u ∈ A, ∀ v ∈ A, ¬ SideGeometry.adj u v) →
      (∃ v ∈ A, SideGeometry.adj x v) →
      ∃ i : Fin 11, x ∈ side i ∧ Disjoint (S i) A) :
    ∀ i, S i ⊆ allowed i := by
  intro i y hy
  by_contra hn
  obtain ⟨hx, hyA, hA, hnb, hother⟩ := witness_valid i y hn
  obtain ⟨j, hj, hd⟩ := hex _ _ hA hnb
  by_cases he : j = i
  · subst j
    exact Finset.disjoint_left.mp hd hy hyA
  · obtain ⟨v, hv⟩ := hother j hj he
    obtain ⟨hv, hvA⟩ := Finset.mem_inter.mp hv
    exact Finset.disjoint_left.mp hd (hsub j hv) hvA

end S2Geometry

namespace DagTools

lemma h3_s2_source_bounds {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (r : Fin 11 → Nat × Bool)
    (hW : ∀ x : Fin 10, sem_W 10 D x =
      (Finset.univ.filter (fun i : Fin 11 => x ∈ S2Geometry.side i)).image r) :
    ∀ i, supp 10 D (src D (r i)) ⊆ S2Geometry.allowed i := by
  apply S2Geometry.support_bound
  · intro i x hx
    apply (sem_mem_W.mp ?_).2.1
    rw [hW]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hx⟩, rfl⟩
  · intro x A hA hnb
    obtain ⟨j, s, hj, _, hxs, hxn, hd⟩ :=
      sem_exposure petersen_graph_ok h.1 hC A hA x hnb
    have hm : (j, s) ∈ sem_W 10 D x := sem_mem_W.mpr ⟨hj, hxs, hxn⟩
    rw [hW] at hm
    obtain ⟨i, hi, hri⟩ := Finset.mem_image.mp hm
    exact ⟨i, (Finset.mem_filter.mp hi).2, by simpa only [hri] using hd⟩

end DagTools

namespace DagTools

lemma h3_singleton_two_exit_pattern {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hc : ∀ x : Fin 10, x ≠ 0 → x ≠ 2 → (exitArcs 10 D (carrierT 10 D {x})).card = 2)
    (hc2 : (exitArcs 10 D (carrierT 10 D {(2 : Fin 10)})).card = 3) :
    ∃ e0 e1 e4 e5 d q : ℕ × Bool,
      supp 10 D (src D e0) = {0} ∧ supp 10 D (src D e1) = {1} ∧
      supp 10 D (src D e4) = {4} ∧ supp 10 D (src D e5) = {5} ∧
      exitArcs 10 D (carrierT 10 D {0}) = {e0} ∧
      exitArcs 10 D (carrierT 10 D {1}) = {h3_opp e0, e1} ∧
      exitArcs 10 D (carrierT 10 D {2}) = {h3_opp e1, h3_opp d, q} ∧
      exitArcs 10 D (carrierT 10 D {3}) = {h3_opp e4, d} ∧
      exitArcs 10 D (carrierT 10 D {4}) = {h3_opp e0, e4} ∧
      exitArcs 10 D (carrierT 10 D {5}) = {h3_opp e0, e5} ∧
      exitArcs 10 D (carrierT 10 D {6}) = {h3_opp e1, d} ∧
      exitArcs 10 D (carrierT 10 D {7}) = {h3_opp e5, d} ∧
      exitArcs 10 D (carrierT 10 D {8}) = {h3_opp e5, h3_opp d} ∧
      exitArcs 10 D (carrierT 10 D {9}) = {h3_opp e4, h3_opp d} ∧
      q ≠ h3_opp e1 ∧ q ≠ h3_opp d := by
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
  obtain ⟨e1, _, hW1⟩ := h3_pair_of_card_two (hAmem 1 (by decide)) (hc 1 (by decide) (by decide))
  obtain ⟨e4, _, hW4⟩ := h3_pair_of_card_two (hAmem 4 (by decide)) (hc 4 (by decide) (by decide))
  obtain ⟨e5, _, hW5⟩ := h3_pair_of_card_two (hAmem 5 (by decide)) (hc 5 (by decide) (by decide))
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
  obtain ⟨g3, _, hW3⟩ := h3_pair_of_card_two ha3 (hc 3 (by decide) (by decide))
  obtain ⟨g6, _, hW6⟩ := h3_pair_of_card_two ha6 (hc 6 (by decide) (by decide))
  obtain ⟨g7, _, hW7⟩ := h3_pair_of_card_two ha7 (hc 7 (by decide) (by decide))
  obtain ⟨g8, _, hW8⟩ := h3_pair_of_card_two ha8 (hc 8 (by decide) (by decide))
  obtain ⟨g9, _, hW9⟩ := h3_pair_of_card_two ha9 (hc 9 (by decide) (by decide))
  have hb1 : supp 10 D (src D (h3_opp (h3_opp e1))) = {(1 : Fin 10)} := by rw [h3_opp_opp]; exact hp1
  have hb4 : supp 10 D (src D (h3_opp (h3_opp e4))) = {(4 : Fin 10)} := by rw [h3_opp_opp]; exact hp4
  have hb5 : supp 10 D (src D (h3_opp (h3_opp e5))) = {(5 : Fin 10)} := by rw [h3_opp_opp]; exact hp5
  have h38 : h3_opp g3 = g8 := h3_split_edge_pair petersen_graph_ok h.1 hC
    (by rw [hW3]) (by rw [hW8]) hb4 hb5 (by decide) (by decide) (by unfold petersenAdj; decide)
  have h86 : h3_opp g8 = g6 := h3_split_edge_pair petersen_graph_ok h.1 hC
    (by rw [hW8]) (by rw [hW6]) hb5 hb1 (by decide) (by decide) (by unfold petersenAdj; decide)
  have h69 : h3_opp g6 = g9 := h3_split_edge_pair petersen_graph_ok h.1 hC
    (by rw [hW6]) (by rw [hW9]) hb1 hb4 (by decide) (by decide) (by unfold petersenAdj; decide)
  have h97 : h3_opp g9 = g7 := h3_split_edge_pair petersen_graph_ok h.1 hC
    (by rw [hW9]) (by rw [hW7]) hb4 hb5 (by decide) (by decide) (by unfold petersenAdj; decide)
  have hg6 : g6 = g3 := by rw [← h86, ← h38, h3_opp_opp]
  have hg9 : g9 = h3_opp g3 := by rw [← h69, hg6]
  have hg7 : g7 = g3 := by rw [← h97, hg9, h3_opp_opp]

  have hd2 : h3_opp g3 ∈ exitArcs 10 D (carrierT 10 D {(2 : Fin 10)}) :=
    sem_two_exit_remaining_slot petersen_graph_ok h.1 hC (by rw [hW3]) hb4
      (by unfold petersenAdj; decide) (by decide)
  have hg3mem : g3 ∈ exitArcs 10 D (carrierT 10 D {(3 : Fin 10)}) := by rw [hW3]; simp
  have h3in : (3 : Fin 10) ∈ supp 10 D (src D g3) := (sem_mem_exit1.mp hg3mem).2.1
  have hneq : h3_opp e1 ≠ h3_opp g3 := by
    intro he
    have he' : e1 = g3 := by
      have ht := congrArg h3_opp he
      simpa only [h3_opp_opp] using ht
    rw [← he', hp1] at h3in
    simp at h3in
  have hcardErase : ((exitArcs 10 D (carrierT 10 D {(2 : Fin 10)})).erase (h3_opp e1)).card = 2 := by
    rw [Finset.card_erase_of_mem ha2, hc2]
  have hdErase : h3_opp g3 ∈ (exitArcs 10 D (carrierT 10 D {(2 : Fin 10)})).erase (h3_opp e1) :=
    Finset.mem_erase.mpr ⟨Ne.symm hneq, hd2⟩
  obtain ⟨q, hqd, hrest⟩ := h3_pair_of_card_two hdErase hcardErase
  have hqErase : q ∈ (exitArcs 10 D (carrierT 10 D {(2 : Fin 10)})).erase (h3_opp e1) := by
    rw [hrest]; simp
  have hq1 := (Finset.mem_erase.mp hqErase).1
  have hW2 : exitArcs 10 D (carrierT 10 D {(2 : Fin 10)}) = {h3_opp e1, h3_opp g3, q} := by
    rw [← Finset.insert_erase ha2, hrest]
  refine ⟨e0, e1, e4, e5, g3, q, hp0, hp1, hp4, hp5, hW0, hW1, hW2,
    hW3, hW4, hW5, ?_, ?_, ?_, ?_, hq1, hqd⟩
  · simpa only [hg6] using hW6
  · simpa only [hg7] using hW7
  · simpa only [← h38] using hW8
  · simpa only [hg9] using hW9


end DagTools

namespace DagTools

lemma h3_star0_exact_of_two_exit_pure_companion {D : Dag}
    (h : StrictLive 10 D) (hC : sem_Comp 10 petersenAdj D)
    (hz : (0 : Fin 10) ∈ ineligSet 10 D) (hB0 : Bzero 10 D = 0)
    (A e4 : ℕ × Bool)
    (hW4 : exitArcs 10 D (carrierT 10 D {(4 : Fin 10)}) = {A, e4})
    (hp4 : supp 10 D (src D e4) = {(4 : Fin 10)})
    (hAN : ({1, 4, 5} : Finset (Fin 10)) ⊆ supp 10 D (src D A)) :
    supp 10 D (src D A) = {1, 4, 5} := by
  classical
  apply Finset.Subset.antisymm ?_ hAN
  intro c hc
  by_contra hcN
  have hzero : ∀ a : Fin 10, petersenAdj 0 a ↔
      a ∈ ({1, 4, 5} : Finset (Fin 10)) := by
    unfold petersenAdj
    decide +kernel
  have hci : ¬ petersenAdj 0 c := fun h => hcN ((hzero c).mp h)
  obtain ⟨e, heW, hec, heN⟩ := H3CoStar.sem_neighbor_exclusion_slot_of_bzero
    petersen_graph_ok h hC hB0 hz c hci
  have he4 : e ∈ exitArcs 10 D (carrierT 10 D {(4 : Fin 10)}) :=
    heW 4 ((hzero 4).mpr (by decide))
  rw [hW4, Finset.mem_insert, Finset.mem_singleton] at he4
  rcases he4 with heA | he4
  · exact hec (heA.symm ▸ hc)
  · have he5 := heN 5 ((hzero 5).mpr (by decide))
    rw [he4, hp4, Finset.mem_singleton] at he5
    exact (by decide : (5 : Fin 10) ≠ 4) he5

lemma h3_singleton_two_exact_star0 {D : Dag}
    (h : StrictLive 10 D) (hC : sem_Comp 10 petersenAdj D)
    (hz : (0 : Fin 10) ∈ ineligSet 10 D) (hB0 : Bzero 10 D = 0)
    (hc : ∀ x : Fin 10, x ≠ 0 → x ≠ 2 →
      (exitArcs 10 D (carrierT 10 D {x})).card = 2)
    (hc2 : (exitArcs 10 D (carrierT 10 D {(2 : Fin 10)})).card = 3) :
    ∃ e : ℕ × Bool, e.1 < D.length ∧ tag D e.1 = true ∧
      supp 10 D (src D e) = {0} ∧
      supp 10 D (src D (e.1, !e.2)) = {1, 4, 5} ∧
      supp 10 D (10 + e.1) = ∅ ∧
      exitArcs 10 D (carrierT 10 D {0}) = {e} := by
  obtain ⟨e0, e1, e4, e5, d, q, _, _, hp4, _, hW0, _, _, _, hW4, _⟩ :=
    h3_singleton_two_exit_pattern h hC hz hc hc2
  obtain ⟨e, he, ht, hsrc, hout, hN, heW, _⟩ :=
    sem_inelig_consumer petersen_graph_ok h hC hz
  have heq : e = e0 := Finset.singleton_injective (heW.symm.trans hW0)
  have hAN : ({1, 4, 5} : Finset (Fin 10)) ⊆ supp 10 D (src D (h3_opp e0)) := by
    intro x hx
    have hnb : ∀ a : Fin 10, a ∈ ({1, 4, 5} : Finset (Fin 10)) → petersenAdj 0 a := by
      unfold petersenAdj
      decide +kernel
    simpa only [heq, h3_opp] using hN x (hnb x hx)
  have hstar := h3_star0_exact_of_two_exit_pure_companion h hC hz hB0
    (h3_opp e0) e4 hW4 hp4 hAN
  refine ⟨e, he, ht, hsrc, ?_, hout, heW⟩
  simpa only [heq, h3_opp] using hstar



end DagTools

namespace DagTools

def h3_s2_sideMap (e0 e1 e4 e5 d q : ℕ × Bool) (i : Fin 11) : ℕ × Bool :=
  ([e0,h3_opp e0,e1,h3_opp e1,e4,h3_opp e4,e5,h3_opp e5,d,h3_opp d,q] :
    List (ℕ × Bool)).getD i.val e0

def h3_s2_incidenceIndices (x : Fin 10) : Finset (Fin 11) :=
  match x.val with
  | 0 => {0}
  | 1 => {1,2}
  | 2 => {3,9,10}
  | 3 => {5,8}
  | 4 => {1,4}
  | 5 => {1,6}
  | 6 => {3,8}
  | 7 => {7,8}
  | 8 => {7,9}
  | _ => {5,9}

set_option maxRecDepth 100000 in
lemma h3_s2_incidence_indices : ∀ x : Fin 10,
    Finset.univ.filter (fun i : Fin 11 => x ∈ S2Geometry.side i) = h3_s2_incidenceIndices x := by
  decide +kernel

lemma h3_singleton_two_sources_exist {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hB0 : Bzero 10 D = 0)
    (hc : ∀ x : Fin 10, x ≠ 0 → x ≠ 2 → (exitArcs 10 D (carrierT 10 D {x})).card = 2)
    (hc2 : (exitArcs 10 D (carrierT 10 D {(2 : Fin 10)})).card = 3) :
    ∃ r : Fin 10 → ℕ × Bool, ∃ q : ℕ × Bool,
      Function.Injective r ∧
      (∀ i, r (SideGeometry.opposite i) = ((r i).1, !(r i).2)) ∧
      (∀ i, supp 10 D (src D (r i)) = SideGeometry.side i) ∧
      (∀ x : Fin 10, exitArcs 10 D (carrierT 10 D {x}) =
        (Finset.univ.filter (fun i : Fin 10 => x ∈ SideGeometry.side i)).image r ∪
          if x = 2 then {q} else ∅) ∧
      (∀ i, (r i).1 < D.length ∧ tag D (r i).1 = true ∧ supp 10 D (10+(r i).1) = ∅) ∧
      q ≠ r 3 ∧ q ≠ r 9 := by
  obtain ⟨e0,e1,e4,e5,d,q,hp0,hp1,hp4,hp5,hW0,hW1,hW2,hW3,hW4,hW5,
    hW6,hW7,hW8,hW9,hq1,hqd⟩ := h3_singleton_two_exit_pattern h hC hz hc hc2
  let r := h3_sideMap e0 e1 e4 e5 d
  let R := h3_s2_sideMap e0 e1 e4 e5 d q
  have hW11 : ∀ x : Fin 10, exitArcs 10 D (carrierT 10 D {x}) =
      (Finset.univ.filter (fun i : Fin 11 => x ∈ S2Geometry.side i)).image R := by
    intro x
    rw [h3_s2_incidence_indices]
    fin_cases x
    · simpa [R,h3_s2_sideMap,h3_s2_incidenceIndices] using hW0
    · simpa [R,h3_s2_sideMap,h3_s2_incidenceIndices] using hW1
    · simpa [R,h3_s2_sideMap,h3_s2_incidenceIndices] using hW2
    · simpa [R,h3_s2_sideMap,h3_s2_incidenceIndices] using hW3
    · simpa [R,h3_s2_sideMap,h3_s2_incidenceIndices] using hW4
    · simpa [R,h3_s2_sideMap,h3_s2_incidenceIndices] using hW5
    · simpa [R,h3_s2_sideMap,h3_s2_incidenceIndices] using hW6
    · simpa [R,h3_s2_sideMap,h3_s2_incidenceIndices] using hW7
    · simpa [R,h3_s2_sideMap,h3_s2_incidenceIndices] using hW8
    · simpa [R,h3_s2_sideMap,h3_s2_incidenceIndices] using hW9
  have hb := h3_s2_source_bounds h hC R hW11
  have hlo : ∀ i : Fin 11, S2Geometry.side i ⊆ supp 10 D (src D (R i)) := by
    intro i x hx
    apply (sem_mem_exit1.mp ?_).2.1
    rw [hW11]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i,hx⟩,rfl⟩
  have hfirst : ∀ i : Fin 10, R ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩ = r i := by
    intro i; fin_cases i <;> rfl
  have hside : ∀ i : Fin 10,
      S2Geometry.side ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩ = SideGeometry.side i := by
    decide +kernel
  have hfromBounds : ∀ i : Fin 10,
      S2Geometry.allowed ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩ = SideGeometry.side i →
      supp 10 D (src D (r i)) = SideGeometry.side i := by
    intro i hi
    have hu := hb ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩
    have hl := hlo ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩
    rw [hfirst i, hi] at hu
    rw [hfirst i,hside i] at hl
    exact Finset.Subset.antisymm hu hl
  obtain ⟨ez,_,_,_,hstarZ,_,hWz⟩ := h3_singleton_two_exact_star0 h hC hz hB0 hc hc2
  have hez : ez = e0 := Finset.singleton_injective (hWz.symm.trans hW0)
  have hstar : supp 10 D (src D (h3_opp e0)) = {1,4,5} := by
    simpa only [hez,h3_opp] using hstarZ
  have hsources : ∀ i : Fin 10, supp 10 D (src D (r i)) = SideGeometry.side i := by
    intro i
    fin_cases i
    · exact hp0.trans (by decide)
    · exact hstar.trans (by decide)
    · exact hp1.trans (by decide)
    · exact hfromBounds 3 (by decide)
    · exact hp4.trans (by decide)
    · exact hfromBounds 5 (by decide)
    · exact hp5.trans (by decide)
    · exact hfromBounds 7 (by decide)
    · exact hfromBounds 8 (by decide)
    · exact hfromBounds 9 (by decide)
  have hSideInj : Function.Injective SideGeometry.side := by decide +kernel
  have hinj : Function.Injective r := by
    intro i j hij
    apply hSideInj
    rw [← hsources i, ← hsources j, hij]
  have hopp : ∀ i : Fin 10, r (SideGeometry.opposite i) = ((r i).1, !(r i).2) :=
    h3_sideMap_opposite e0 e1 e4 e5 d
  have hW : ∀ x : Fin 10, exitArcs 10 D (carrierT 10 D {x}) =
      (Finset.univ.filter (fun i : Fin 10 => x ∈ SideGeometry.side i)).image r ∪
        if x = 2 then {q} else ∅ := by
    intro x
    rw [SideGeometry.incidence_indices]
    fin_cases x
    · simpa [r,h3_sideMap,SideGeometry.incidenceIndices] using hW0
    · simpa [r,h3_sideMap,SideGeometry.incidenceIndices] using hW1
    · simpa [r,h3_sideMap,SideGeometry.incidenceIndices,Finset.insert_comm] using hW2
    · simpa [r,h3_sideMap,SideGeometry.incidenceIndices] using hW3
    · simpa [r,h3_sideMap,SideGeometry.incidenceIndices] using hW4
    · simpa [r,h3_sideMap,SideGeometry.incidenceIndices] using hW5
    · simpa [r,h3_sideMap,SideGeometry.incidenceIndices] using hW6
    · simpa [r,h3_sideMap,SideGeometry.incidenceIndices] using hW7
    · simpa [r,h3_sideMap,SideGeometry.incidenceIndices] using hW8
    · simpa [r,h3_sideMap,SideGeometry.incidenceIndices] using hW9
  have hvalid : ∀ i : Fin 10, (r i).1 < D.length ∧ tag D (r i).1 = true ∧
      supp 10 D (10+(r i).1) = ∅ := by
    intro i
    obtain ⟨x,hx⟩ := SideGeometry.side_nonempty i
    have hm : r i ∈ exitArcs 10 D (carrierT 10 D {x}) := by
      rw [hW]
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hx⟩,rfl⟩
    have hj := (sem_mem_exit1.mp hm).1
    have ht := h3_exit_tag_and h.1 hm
    refine ⟨hj,ht,?_⟩
    have hd : Disjoint (supp 10 D (src D (r i)))
        (supp 10 D (src D ((r i).1, !(r i).2))) := by
      rw [← hopp i, hsources i, hsources (SideGeometry.opposite i)]
      exact SideGeometry.paired_disjoint i
    rw [sem_supp_and h.1 hj ht]
    apply Finset.disjoint_iff_inter_eq_empty.mp
    rcases he : r i with ⟨j,s⟩
    cases s <;> simpa only [he, Bool.not_false, Bool.not_true, sb_src_false, sb_src_true,
      disjoint_comm] using hd
  refine ⟨r,q,hinj,hopp,hsources,hW,hvalid,?_,?_⟩
  · simpa [r,h3_sideMap] using hq1
  · simpa [r,h3_sideMap] using hqd


end DagTools

namespace DagTools

lemma h3_nonindexed_and_same_off {n : Nat} {D : Dag} (hS : Strict n D)
    {ι : Type*} (r : ι → Nat × Bool) (v : Fin n)
    (hcover : ∀ x : Fin n, x ≠ v → ∀ e ∈ sem_W n D x, ∃ i, r i = e)
    {j : Nat} (hj : j < D.length) (ht : tag D j = true)
    (hne : ∀ i, (r i).1 ≠ j) :
    ∀ x : Fin n, x ≠ v →
      (x ∈ supp n D (opA D j) ↔ x ∈ supp n D (opB D j)) := by
  intro x hx
  have hp (s : Bool) (ha : x ∈ supp n D (src D (j, s)))
      (hb : x ∉ supp n D (src D (j, !s))) : False := by
    have hout : x ∉ supp n D (n + j) :=
      fun hh => hb (sem_supp_and_sub hS hj ht (!s) hh)
    obtain ⟨i, he⟩ := hcover x hx (j, s) (sem_mem_W.mpr ⟨hj, ha, hout⟩)
    exact hne i (congrArg Prod.fst he)
  constructor
  · intro ha
    by_contra hb
    exact hp false ha hb
  · intro hb
    by_contra ha
    exact hp true hb ha

end DagTools

namespace R1FlexibleResource.ResourceExclusion
open CausalBarrier

lemma h3_allowed_if_difference_two (a b : Resource)
    (he : ∀ x : Fin 10, x ≠ 2 → (x ∈ a.1 ↔ x ∈ b.1)) :
    AllowedSides a b := by
  classical
  have hbase (a b : Resource) (hs : a.1 ⊆ b.1)
      (he : ∀ x : Fin 10, x ≠ 2 → (x ∈ a.1 ↔ x ∈ b.1)) :
      AllowedSides a b := by
    apply Or.inl
    by_cases ha : a.1.Nonempty
    · exact Or.inr (Or.inl ⟨ha, hs⟩)
    · have haz : a.1 = ∅ := Finset.not_nonempty_iff_eq_empty.mp ha
      have hbsub : b.1 ⊆ {(2 : Fin 10)} := by
        intro x hx
        apply Finset.mem_singleton.mpr
        by_contra hn
        have hxa := (he x hn).mpr hx
        rw [haz] at hxa
        exact Finset.notMem_empty _ hxa
      by_cases hbz : b.1 = ∅
      · exact Or.inl (Or.inl (haz.trans hbz.symm))
      · have hbe : b.1 = {(2 : Fin 10)} := by
          obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hbz
          have hx2 := Finset.mem_singleton.mp (hbsub hx)
          exact Finset.Subset.antisymm hbsub
            (Finset.singleton_subset_iff.mpr (hx2 ▸ hx))
        apply Or.inl
        right
        right
        simp [OtherSides, haz, hbe]
  by_cases hs : a.1 ⊆ b.1
  · exact hbase a b hs he
  · obtain ⟨v, hva, hvb⟩ := Finset.not_subset.mp hs
    have hv : v = 2 := by
      by_contra hn
      exact hvb ((he v hn).mp hva)
    have hsub : b.1 ⊆ a.1 := by
      intro x hx
      by_cases hx2 : x = 2
      · exact False.elim (hvb (by simpa only [hv, hx2] using hx))
      · exact (he x hx2).mpr hx
    exact allowed_sides_swap (hbase b a hsub (fun x hx => (he x hx).symm))

end R1FlexibleResource.ResourceExclusion

namespace DagTools
open R1FlexibleResource.CausalBarrier R1FlexibleResource.ResourceExclusion
  R1FlexibleResource.DAGBridge

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma h3_s2_other_sides : ∀ i : Fin 10, i ≠ 8 → i ≠ 9 →
    (SideGeometry.side i, SideGeometry.side (SideGeometry.opposite i)) ∈ OtherSides ∨
    (SideGeometry.side (SideGeometry.opposite i), SideGeometry.side i) ∈ OtherSides := by
  unfold SideGeometry.side SideGeometry.mask SideGeometry.opposite OtherSides
  decide +kernel

lemma h3_canonical_except_two_exclusion {D : Dag} (hS : Strict 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hB0 : Bzero 10 D = 0)
    (r : Fin 10 → Nat × Bool)
    (hopp : ∀ i, r (SideGeometry.opposite i) = ((r i).1, !(r i).2))
    (hsrc : ∀ i, supp 10 D (src D (r i)) = SideGeometry.side i)
    (hvalid : ∀ i, (r i).1 < D.length ∧ tag D (r i).1 = true)
    (hcover : ∀ x : Fin 10, x ≠ 2 → ∀ e ∈ sem_W 10 D x, ∃ i, r i = e) : False := by
  have hp : r 9 = ((r 8).1, !(r 8).2) := by
    simpa [SideGeometry.opposite] using hopp 8
  have hdirty : DirtySides D (r 8).1 := by
    have h8 := hsrc 8
    have h9 := hsrc 9
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
    intro j hj hjd ht
    by_cases hex : ∃ i, (r i).1 = j
    · obtain ⟨i, hi⟩ := hex
      have he : ∃ k, r k = (j, false) := by
        cases hb : (r i).2
        · exact ⟨i, Prod.ext hi hb⟩
        · refine ⟨SideGeometry.opposite i, ?_⟩
          rw [hopp, hi, hb]
          rfl
      obtain ⟨k, hk⟩ := he
      have hka : supp 10 D (opA D j) = SideGeometry.side k := by
        simpa [hk, src] using hsrc k
      have hkb : supp 10 D (opB D j) = SideGeometry.side (SideGeometry.opposite k) := by
        simpa [hopp, hk, src] using hsrc (SideGeometry.opposite k)
      have hk8 : k ≠ 8 := by
        intro he
        subst k
        exact hjd (congrArg Prod.fst hk).symm
      have hk9 : k ≠ 9 := by
        intro he
        subst k
        have heq := congrArg Prod.fst hk
        rw [hp] at heq
        exact hjd heq.symm
      apply Or.inl
      apply Or.inl
      apply Or.inr
      change (supp 10 D (opA D j), supp 10 D (opB D j)) ∈ OtherSides ∨
        (supp 10 D (opB D j), supp 10 D (opA D j)) ∈ OtherSides
      rw [hka, hkb]
      exact h3_s2_other_sides k hk8 hk9
    · apply h3_allowed_if_difference_two
      exact h3_nonindexed_and_same_off hS r 2 hcover hj ht
        (fun i hi => hex ⟨i, hi⟩)
  exact h3_r1_flexible_allowed_sides_exclusion hS hC hB0
    (hvalid 8).1 (hvalid 8).2 hdirty hother

end DagTools

namespace DagTools

lemma h3_singleton_two_bzero_exclusion {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hB0 : Bzero 10 D = 0)
    (hc : ∀ x : Fin 10, x ≠ 0 → x ≠ 2 → (exitArcs 10 D (carrierT 10 D {x})).card = 2)
    (hc2 : (exitArcs 10 D (carrierT 10 D {(2 : Fin 10)})).card = 3) : False := by
  obtain ⟨r, q, _, hopp, hsrc, hW, hvalid, _⟩ :=
    h3_singleton_two_sources_exist h hC hz hB0 hc hc2
  apply h3_canonical_except_two_exclusion h.1 hC hB0 r hopp hsrc
    (fun i => ⟨(hvalid i).1, (hvalid i).2.1⟩)
  intro x hx e he
  change e ∈ exitArcs 10 D (carrierT 10 D {x}) at he
  rw [hW, if_neg hx, Finset.union_empty] at he
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp he
  exact ⟨i, hi⟩

end DagTools

namespace DagTools

lemma h3_residual_saturated_two_exclusion {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hB0 : Bzero 10 D = 0) (hone : Bplus 10 D = (eligSet 10 D).card + 1)
    (hSat : h3_saturatedSet 10 D = {2}) : False := by
  apply h3_singleton_two_bzero_exclusion h hC hz hB0
    (h3_saturated_two_other_exit_cards h hC hz hSat)
  have hx : (2 : Fin 10) ∈ h3_saturatedSet 10 D := by
    rw [hSat]
    exact Finset.mem_singleton_self _
  exact (h3_one_residual_saturation petersen_graph_ok h hC hone 2 hx).1

end DagTools


namespace DagTools

lemma h3_exposure_exit {n : ℕ} {D : Dag} {G : Fin n → Fin n → Prop}
    (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    (A : Finset (Fin n)) (hA : ∀ a ∈ A, ∀ b ∈ A, ¬ G a b) (x : Fin n)
    (hnb : ∃ a ∈ A, G x a) :
    ∃ e ∈ exitArcs n D (carrierT n D {x}), Disjoint (supp n D (src D e)) A := by
  obtain ⟨j, s, hj, _, hx, hn, hd⟩ := sem_exposure hG hS hC A hA x hnb
  exact ⟨(j, s), sem_mem_exit1.mpr ⟨hj, hx, hn⟩, hd⟩

lemma h3_two_blocked_exits_equal {n : ℕ} {D : Dag} {G : Fin n → Fin n → Prop}
    (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {x : Fin n} {e f : ℕ × Bool} (hc : (exitArcs n D (carrierT n D {x})).card ≤ 2)
    (he : e ∈ exitArcs n D (carrierT n D {x})) (hf : f ∈ exitArcs n D (carrierT n D {x}))
    (A : Finset (Fin n)) (hA : ∀ a ∈ A, ∀ b ∈ A, ¬ G a b) (hnb : ∃ a ∈ A, G x a)
    (hbe : ¬ Disjoint (supp n D (src D e)) A) (hbf : ¬ Disjoint (supp n D (src D f)) A) : e = f := by
  by_contra hne
  have hp : ({e, f} : Finset (ℕ × Bool)) = exitArcs n D (carrierT n D {x}) := by
    apply Finset.eq_of_subset_of_card_le
    · intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl <;> assumption
    · simpa [hne] using hc
  obtain ⟨g, hg, hd⟩ := h3_exposure_exit hG hS hC A hA x hnb
  rw [← hp] at hg
  simp only [Finset.mem_insert, Finset.mem_singleton] at hg
  rcases hg with rfl | rfl
  · exact hbe hd
  · exact hbf hd

lemma h3_remaining_exit_disjoint {n : ℕ} {D : Dag} {G : Fin n → Fin n → Prop}
    (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {x : Fin n} {e f : ℕ × Bool}
    (hW : exitArcs n D (carrierT n D {x}) ⊆ {e, f})
    (A : Finset (Fin n)) (hA : ∀ a ∈ A, ∀ b ∈ A, ¬ G a b) (hnb : ∃ a ∈ A, G x a)
    (hbe : ¬ Disjoint (supp n D (src D e)) A) : Disjoint (supp n D (src D f)) A := by
  obtain ⟨g, hg, hd⟩ := h3_exposure_exit hG hS hC A hA x hnb
  have hh := hW hg
  simp only [Finset.mem_insert, Finset.mem_singleton] at hh
  rcases hh with rfl | rfl
  · exact (hbe hd).elim
  · exact hd

lemma h3_two_exit_avoid {n : ℕ} {D : Dag} {G : Fin n → Fin n → Prop}
    (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {x y : Fin n} {e f : ℕ × Bool}
    (hW : exitArcs n D (carrierT n D {x}) ⊆ {e, f})
    (hbar : y ∉ supp n D (src D (h3_opp e))) (hxy : G x y) :
    h3_opp f ∈ exitArcs n D (carrierT n D {y}) := by
  obtain ⟨j, hj, _, _, hxn, hyn, s, hxs, _, hys, _⟩ := sem_joint_meeting hG hS hC hxy
  have hh := hW (sem_mem_exit1.mpr ⟨hj, hxs, hxn⟩)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hh
  rcases hh with he | hf
  · exact False.elim (hbar (by simpa only [← he, h3_opp] using hys))
  · apply sem_mem_exit1.mpr
    simpa only [← hf, h3_opp] using And.intro hj (And.intro hys hyn)

lemma h3_singleton_one_core {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hc : ∀ x : Fin 10, x ≠ 0 → x ≠ 1 → (exitArcs 10 D (carrierT 10 D {x})).card ≤ 2) :
    ∃ e0 e4 e5 d a b : ℕ × Bool,
      supp 10 D (src D e0) = {0} ∧ supp 10 D (src D e4) = {4} ∧ supp 10 D (src D e5) = {5} ∧
      exitArcs 10 D (carrierT 10 D {0}) = {e0} ∧
      exitArcs 10 D (carrierT 10 D {4}) = {h3_opp e0, e4} ∧
      exitArcs 10 D (carrierT 10 D {5}) = {h3_opp e0, e5} ∧
      exitArcs 10 D (carrierT 10 D {3}) = {h3_opp e4, d} ∧
      exitArcs 10 D (carrierT 10 D {7}) = {h3_opp e5, d} ∧
      exitArcs 10 D (carrierT 10 D {8}) = {h3_opp e5, h3_opp d} ∧
      exitArcs 10 D (carrierT 10 D {9}) = {h3_opp e4, h3_opp d} ∧
      exitArcs 10 D (carrierT 10 D {2}) = {h3_opp d, a} ∧
      exitArcs 10 D (carrierT 10 D {6}) = {d, b} ∧
      h3_opp e0 ∈ exitArcs 10 D (carrierT 10 D {1}) ∧
      h3_opp a ∈ exitArcs 10 D (carrierT 10 D {1}) ∧
      h3_opp b ∈ exitArcs 10 D (carrierT 10 D {1}) ∧
      h3_opp a ≠ h3_opp e0 ∧ h3_opp b ≠ h3_opp e0 ∧
      1 ∉ supp 10 D (src D d) ∧ 1 ∉ supp 10 D (src D (h3_opp d)) := by
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
  have hc4 : (exitArcs 10 D (carrierT 10 D {(4 : Fin 10)})).card = 2 :=
    Nat.le_antisymm (hc 4 (by decide) (by decide))
      (sem_nonpure_exit_card petersen_graph_ok h.1 hC (x := (4 : Fin 10)) (y := (1 : Fin 10)) (hAmem 4 (by decide)) (hAN (by decide)) (by decide))
  have hc5 : (exitArcs 10 D (carrierT 10 D {(5 : Fin 10)})).card = 2 :=
    Nat.le_antisymm (hc 5 (by decide) (by decide))
      (sem_nonpure_exit_card petersen_graph_ok h.1 hC (x := (5 : Fin 10)) (y := (1 : Fin 10)) (hAmem 5 (by decide)) (hAN (by decide)) (by decide))
  obtain ⟨e4, _, hW4⟩ := h3_pair_of_card_two (hAmem 4 (by decide)) hc4
  obtain ⟨e5, _, hW5⟩ := h3_pair_of_card_two (hAmem 5 (by decide)) hc5
  have hp4 : supp 10 D (src D e4) = {(4 : Fin 10)} :=
    petersen_other_exit_pure h.1 hC hz (by decide) (by rw [hW4]) (by rw [hW4]; simp) hAN
  have hp5 : supp 10 D (src D e5) = {(5 : Fin 10)} :=
    petersen_other_exit_pure h.1 hC hz (by decide) (by rw [hW5]) (by rw [hW5]; simp) hAN
  have ha3 : h3_opp e4 ∈ exitArcs 10 D (carrierT 10 D {3}) :=
    sem_two_exit_remaining_slot petersen_graph_ok h.1 hC (by rw [hW4]) hbarA (by unfold petersenAdj; decide) (by decide)
  have ha9 : h3_opp e4 ∈ exitArcs 10 D (carrierT 10 D {9}) :=
    sem_two_exit_remaining_slot petersen_graph_ok h.1 hC (by rw [hW4]) hbarA (by unfold petersenAdj; decide) (by decide)
  have ha7 : h3_opp e5 ∈ exitArcs 10 D (carrierT 10 D {7}) :=
    sem_two_exit_remaining_slot petersen_graph_ok h.1 hC (by rw [hW5]) hbarA (by unfold petersenAdj; decide) (by decide)
  have ha8 : h3_opp e5 ∈ exitArcs 10 D (carrierT 10 D {8}) :=
    sem_two_exit_remaining_slot petersen_graph_ok h.1 hC (by rw [hW5]) hbarA (by unfold petersenAdj; decide) (by decide)
  have hc3 : (exitArcs 10 D (carrierT 10 D {(3 : Fin 10)})).card = 2 :=
    Nat.le_antisymm (hc 3 (by decide) (by decide))
      (sem_nonpure_exit_card petersen_graph_ok h.1 hC ha3 (sem_mem_exit1.mp ha9).2.1 (by decide))
  have hc7 : (exitArcs 10 D (carrierT 10 D {(7 : Fin 10)})).card = 2 :=
    Nat.le_antisymm (hc 7 (by decide) (by decide))
      (sem_nonpure_exit_card petersen_graph_ok h.1 hC ha7 (sem_mem_exit1.mp ha8).2.1 (by decide))
  have hc8 : (exitArcs 10 D (carrierT 10 D {(8 : Fin 10)})).card = 2 :=
    Nat.le_antisymm (hc 8 (by decide) (by decide))
      (sem_nonpure_exit_card petersen_graph_ok h.1 hC ha8 (sem_mem_exit1.mp ha7).2.1 (by decide))
  have hc9 : (exitArcs 10 D (carrierT 10 D {(9 : Fin 10)})).card = 2 :=
    Nat.le_antisymm (hc 9 (by decide) (by decide))
      (sem_nonpure_exit_card petersen_graph_ok h.1 hC ha9 (sem_mem_exit1.mp ha3).2.1 (by decide))
  obtain ⟨g3, _, hW3⟩ := h3_pair_of_card_two ha3 hc3
  obtain ⟨g7, _, hW7⟩ := h3_pair_of_card_two ha7 hc7
  obtain ⟨g8, _, hW8⟩ := h3_pair_of_card_two ha8 hc8
  obtain ⟨g9, _, hW9⟩ := h3_pair_of_card_two ha9 hc9
  have hb4 : supp 10 D (src D (h3_opp (h3_opp e4))) = {(4 : Fin 10)} := by rw [h3_opp_opp]; exact hp4
  have hb5 : supp 10 D (src D (h3_opp (h3_opp e5))) = {(5 : Fin 10)} := by rw [h3_opp_opp]; exact hp5
  have h38 : h3_opp g3 = g8 := h3_split_edge_pair petersen_graph_ok h.1 hC
    (by rw [hW3]) (by rw [hW8]) hb4 hb5 (by decide) (by decide) (by unfold petersenAdj; decide)
  have h79 : h3_opp g7 = g9 := h3_split_edge_pair petersen_graph_ok h.1 hC
    (by rw [hW7]) (by rw [hW9]) hb5 hb4 (by decide) (by decide) (by unfold petersenAdj; decide)
  have h23 : h3_opp g3 ∈ exitArcs 10 D (carrierT 10 D {2}) :=
    sem_two_exit_remaining_slot petersen_graph_ok h.1 hC (by rw [hW3]) hb4 (by unfold petersenAdj; decide) (by decide)
  have h27 : h3_opp g7 ∈ exitArcs 10 D (carrierT 10 D {2}) :=
    sem_two_exit_remaining_slot petersen_graph_ok h.1 hC (by rw [hW7]) hb5 (by unfold petersenAdj; decide) (by decide)
  have hI : ∀ a ∈ ({1, 8, 9} : Finset (Fin 10)), ∀ b ∈ ({1, 8, 9} : Finset (Fin 10)), ¬ petersenAdj a b := by
    unfold petersenAdj
    decide
  have hJ : ∀ a ∈ ({1, 3, 7} : Finset (Fin 10)), ∀ b ∈ ({1, 3, 7} : Finset (Fin 10)), ¬ petersenAdj a b := by
    unfold petersenAdj
    decide
  have heq : h3_opp g3 = h3_opp g7 := by
    apply h3_two_blocked_exits_equal petersen_graph_ok h.1 hC (hc 2 (by decide) (by decide)) h23 h27 {1, 8, 9} hI
      ⟨1, by decide, by unfold petersenAdj; decide⟩
    · intro hd
      have hm : (8 : Fin 10) ∈ supp 10 D (src D (h3_opp g3)) := by
        rw [h38]
        exact (sem_mem_exit1.mp (by rw [hW8]; simp : g8 ∈ exitArcs 10 D (carrierT 10 D {8}))).2.1
      exact Finset.disjoint_left.mp hd hm (by decide)
    · intro hd
      have hm : (9 : Fin 10) ∈ supp 10 D (src D (h3_opp g7)) := by
        rw [h79]
        exact (sem_mem_exit1.mp (by rw [hW9]; simp : g9 ∈ exitArcs 10 D (carrierT 10 D {9}))).2.1
      exact Finset.disjoint_left.mp hd hm (by decide)
  have hg7 : g7 = g3 := by
    have hh := congrArg h3_opp heq
    simpa only [h3_opp_opp] using hh.symm
  have hg8 : g8 = h3_opp g3 := h38.symm
  have hg9 : g9 = h3_opp g3 := by rw [← h79, hg7]
  have hnd : (1 : Fin 10) ∉ supp 10 D (src D g3) := by
    have hd := h3_remaining_exit_disjoint petersen_graph_ok h.1 hC (by rw [hW3]) {1, 8, 9} hI
      (x := (3 : Fin 10)) ⟨8, by decide, by unfold petersenAdj; decide⟩ (by
        intro he
        exact Finset.disjoint_left.mp he (sem_mem_exit1.mp ha9).2.1 (by decide))
    exact fun hm => Finset.disjoint_left.mp hd hm (by decide)
  have hnbd : (1 : Fin 10) ∉ supp 10 D (src D (h3_opp g3)) := by
    have hd := h3_remaining_exit_disjoint petersen_graph_ok h.1 hC (by rw [hW8, hg8]) {1, 3, 7} hJ
      (x := (8 : Fin 10)) ⟨3, by decide, by unfold petersenAdj; decide⟩ (by
        intro he
        exact Finset.disjoint_left.mp he (sem_mem_exit1.mp ha7).2.1 (by decide))
    exact fun hm => Finset.disjoint_left.mp hd hm (by decide)
  have h6d : g3 ∈ exitArcs 10 D (carrierT 10 D {6}) := by
    have hh := sem_two_exit_remaining_slot petersen_graph_ok h.1 hC (by rw [hW8]) hb5
      (x := (8 : Fin 10)) (y := (6 : Fin 10)) (by unfold petersenAdj; decide) (by decide)
    change h3_opp g8 ∈ exitArcs 10 D (carrierT 10 D {6}) at hh
    simpa only [hg8, h3_opp_opp] using hh
  have hc2 : (exitArcs 10 D (carrierT 10 D {(2 : Fin 10)})).card = 2 := by
    apply Nat.le_antisymm (hc 2 (by decide) (by decide))
    apply sem_nonpure_exit_card petersen_graph_ok h.1 hC h23 (y := (8 : Fin 10))
    · rw [h38]
      exact (sem_mem_exit1.mp (by rw [hW8]; simp : g8 ∈ exitArcs 10 D (carrierT 10 D {(8 : Fin 10)}))).2.1
    · decide
  have hc6 : (exitArcs 10 D (carrierT 10 D {(6 : Fin 10)})).card = 2 := by
    apply Nat.le_antisymm (hc 6 (by decide) (by decide))
    apply sem_nonpure_exit_card petersen_graph_ok h.1 hC h6d (y := (3 : Fin 10))
    · exact (sem_mem_exit1.mp (by rw [hW3]; simp : g3 ∈ exitArcs 10 D (carrierT 10 D {(3 : Fin 10)}))).2.1
    · decide
  obtain ⟨a, _, hW2⟩ := h3_pair_of_card_two h23 hc2
  obtain ⟨b, _, hW6⟩ := h3_pair_of_card_two h6d hc6
  have ha1 : h3_opp a ∈ exitArcs 10 D (carrierT 10 D {1}) :=
    h3_two_exit_avoid petersen_graph_ok h.1 hC (by rw [hW2]) (by simpa only [h3_opp_opp] using hnd)
      (by unfold petersenAdj; decide)
  have hb1 : h3_opp b ∈ exitArcs 10 D (carrierT 10 D {1}) :=
    h3_two_exit_avoid petersen_graph_ok h.1 hC (by rw [hW6]) hnbd (by unfold petersenAdj; decide)
  have hna : h3_opp a ≠ h3_opp e0 := by
    intro he
    have haeq : a = e0 := by have hh := congrArg h3_opp he; simpa only [h3_opp_opp] using hh
    have hm := (sem_mem_exit1.mp (by rw [hW2]; simp : a ∈ exitArcs 10 D (carrierT 10 D {2}))).2.1
    rw [haeq, hp0] at hm
    simp at hm
  have hnb : h3_opp b ≠ h3_opp e0 := by
    intro he
    have hbeq : b = e0 := by have hh := congrArg h3_opp he; simpa only [h3_opp_opp] using hh
    have hm := (sem_mem_exit1.mp (by rw [hW6]; simp : b ∈ exitArcs 10 D (carrierT 10 D {6}))).2.1
    rw [hbeq, hp0] at hm
    simp at hm
  refine ⟨e0, e4, e5, g3, a, b, hp0, hp4, hp5, hW0, hW4, hW5, hW3, ?_, ?_, ?_, hW2, hW6,
    hAmem 1 (by decide), ha1, hb1, hna, hnb, hnd, hnbd⟩
  · simpa only [hg7] using hW7
  · simpa only [hg8] using hW8
  · simpa only [hg9] using hW9

lemma h3_card_three_two_remaining {α : Type} [DecidableEq α] {W : Finset α} {a b c : α}
    (hcard : W.card = 3) (ha : a ∈ W) (hb : b ∈ W) (hc : c ∈ W)
    (hba : b ≠ a) (hca : c ≠ a) :
    (b = c ∧ ∃ f, f ≠ a ∧ f ≠ b ∧ W = {a, b, f}) ∨
    (b ≠ c ∧ W = {a, b, c}) := by
  have he : (W.erase a).card = 2 := by rw [Finset.card_erase_of_mem ha, hcard]
  obtain ⟨f, hfb, hWf⟩ := h3_pair_of_card_two (Finset.mem_erase.mpr ⟨hba, hb⟩) he
  have hfm : f ∈ W.erase a := by rw [hWf]; simp
  have hfa := (Finset.mem_erase.mp hfm).1
  have hW : W = {a, b, f} := by rw [← Finset.insert_erase ha, hWf]
  by_cases hbc : b = c
  · exact Or.inl ⟨hbc, f, hfa, hfb, hW⟩
  · refine Or.inr ⟨hbc, ?_⟩
    rw [hW] at hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with he | he | he
    · exact (hca he).elim
    · exact (hbc he.symm).elim
    · simpa only [← he] using hW

lemma h3_singleton_one_profiles {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hc : ∀ x : Fin 10, x ≠ 0 → x ≠ 1 → (exitArcs 10 D (carrierT 10 D {x})).card ≤ 2)
    (hc1 : (exitArcs 10 D (carrierT 10 D {(1 : Fin 10)})).card = 3) :
    ∃ e0 e4 e5 d a b : ℕ × Bool,
      supp 10 D (src D e0) = {0} ∧ supp 10 D (src D e4) = {4} ∧ supp 10 D (src D e5) = {5} ∧
      exitArcs 10 D (carrierT 10 D {0}) = {e0} ∧
      exitArcs 10 D (carrierT 10 D {4}) = {h3_opp e0, e4} ∧
      exitArcs 10 D (carrierT 10 D {5}) = {h3_opp e0, e5} ∧
      exitArcs 10 D (carrierT 10 D {3}) = {h3_opp e4, d} ∧
      exitArcs 10 D (carrierT 10 D {7}) = {h3_opp e5, d} ∧
      exitArcs 10 D (carrierT 10 D {8}) = {h3_opp e5, h3_opp d} ∧
      exitArcs 10 D (carrierT 10 D {9}) = {h3_opp e4, h3_opp d} ∧
      exitArcs 10 D (carrierT 10 D {2}) = {h3_opp d, a} ∧
      exitArcs 10 D (carrierT 10 D {6}) = {d, b} ∧
      ((a = b ∧ ∃ f, f ≠ h3_opp e0 ∧ f ≠ h3_opp a ∧
          exitArcs 10 D (carrierT 10 D {(1 : Fin 10)}) = {h3_opp e0, h3_opp a, f}) ∨
       (a ≠ b ∧ exitArcs 10 D (carrierT 10 D {(1 : Fin 10)}) = {h3_opp e0, h3_opp a, h3_opp b})) := by
  obtain ⟨e0, e4, e5, d, a, b, hp0, hp4, hp5, hW0, hW4, hW5, hW3, hW7, hW8, hW9,
    hW2, hW6, hm0, hma, hmb, hna, hnb, _, _⟩ := h3_singleton_one_core h hC hz hc
  refine ⟨e0, e4, e5, d, a, b, hp0, hp4, hp5, hW0, hW4, hW5, hW3, hW7, hW8, hW9, hW2, hW6, ?_⟩
  rcases h3_card_three_two_remaining hc1 hm0 hma hmb hna hnb with ⟨he, f, hfa, hfb, hW⟩ | ⟨he, hW⟩
  · left
    refine ⟨?_, f, hfa, hfb, hW⟩
    have hh := congrArg h3_opp he
    simpa only [h3_opp_opp] using hh
  · right
    refine ⟨?_, hW⟩
    intro hab
    exact he (congrArg h3_opp hab)


end DagTools

namespace S1BaseGeometry

def side (i : Fin 11) : Finset (Fin 10) :=
  SideGeometry.mask (([1, 50, 2, 68, 16, 520, 32, 384, 200, 772, 2] : List Nat).getD i.val 0)

def allowed (i : Fin 11) : Finset (Fin 10) :=
  SideGeometry.mask (([1, 1023, 1023, 68, 17, 520, 33, 384, 200, 772, 1023] : List Nat).getD i.val 0)

def witnessCode (i : Fin 11) (y : Fin 10) : Nat :=
  ([0, 2, 20, 10, 16, 32, 80, 130, 258, 514, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2433, 2306, 0, 2568, 2322, 2594, 0, 2432, 2306, 2562, 0, 4106, 4644, 4106, 0, 4136, 4200, 4234, 4866, 4610, 3141, 3218, 3140, 0, 3152, 3172, 3140, 3216, 3456, 0, 0, 5250, 5396, 5258, 5264, 0, 5328, 5250, 5378, 5890, 7237, 7210, 7236, 7208, 7252, 7208, 7236, 0, 0, 7688, 3589, 3842, 3588, 0, 6420, 3620, 0, 0, 3840, 3588, 2121, 8330, 0, 2120, 2256, 2152, 2120, 2240, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List Nat).getD (i.val * 10 + y.val) 0

def witnessVertex (i : Fin 11) (y : Fin 10) : Fin 10 :=
  ⟨witnessCode i y / 1024 % 10, Nat.mod_lt _ (by decide)⟩

def witnessSet (i : Fin 11) (y : Fin 10) : Finset (Fin 10) :=
  SideGeometry.mask (witnessCode i y % 1024)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma witness_valid : ∀ i : Fin 11, ∀ y : Fin 10, y ∉ allowed i →
    let x := witnessVertex i y
    let A := witnessSet i y
    x ∈ side i ∧ y ∈ A ∧
    (∀ u ∈ A, ∀ v ∈ A, ¬ SideGeometry.adj u v) ∧
    (∃ v ∈ A, SideGeometry.adj x v) ∧
    ∀ j : Fin 11, x ∈ side j → j ≠ i → (side j ∩ A).Nonempty := by
  unfold SideGeometry.adj
  decide +kernel

lemma support_bound (S : Fin 11 → Finset (Fin 10))
    (hsub : ∀ i, side i ⊆ S i)
    (hex : ∀ x A, (∀ u ∈ A, ∀ v ∈ A, ¬ SideGeometry.adj u v) →
      (∃ v ∈ A, SideGeometry.adj x v) →
      ∃ i : Fin 11, x ∈ side i ∧ Disjoint (S i) A) :
    ∀ i, S i ⊆ allowed i := by
  intro i y hy
  by_contra hn
  obtain ⟨hx, hyA, hA, hnb, hother⟩ := witness_valid i y hn
  obtain ⟨j, hj, hd⟩ := hex _ _ hA hnb
  by_cases he : j = i
  · subst j
    exact Finset.disjoint_left.mp hd hy hyA
  · obtain ⟨v, hv⟩ := hother j hj he
    obtain ⟨hv, hvA⟩ := Finset.mem_inter.mp hv
    exact Finset.disjoint_left.mp hd (hsub j hv) hvA

end S1BaseGeometry

namespace DagTools

lemma h3_s1_base_source_bounds {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (r : Fin 11 → Nat × Bool)
    (hW : ∀ x : Fin 10, sem_W 10 D x =
      (Finset.univ.filter (fun i : Fin 11 => x ∈ S1BaseGeometry.side i)).image r) :
    ∀ i, supp 10 D (src D (r i)) ⊆ S1BaseGeometry.allowed i := by
  apply S1BaseGeometry.support_bound
  · intro i x hx
    apply (sem_mem_W.mp ?_).2.1
    rw [hW]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hx⟩, rfl⟩
  · intro x A hA hnb
    obtain ⟨j, s, hj, _, hxs, hxn, hd⟩ :=
      sem_exposure petersen_graph_ok h.1 hC A hA x hnb
    have hm : (j, s) ∈ sem_W 10 D x := sem_mem_W.mpr ⟨hj, hxs, hxn⟩
    rw [hW] at hm
    obtain ⟨i, hi, hri⟩ := Finset.mem_image.mp hm
    exact ⟨i, (Finset.mem_filter.mp hi).2, by simpa only [hri] using hd⟩

end DagTools

namespace S1SplitGeometry

def side (i : Fin 12) : Finset (Fin 10) :=
  SideGeometry.mask (([1, 50, 2, 4, 2, 64, 16, 520, 32, 384, 200, 772] : List Nat).getD i.val 0)

def allowed (i : Fin 12) : Finset (Fin 10) :=
  SideGeometry.mask (([1, 1023, 1023, 68, 1023, 68, 17, 520, 33, 384, 200, 772] : List Nat).getD i.val 0)

def witnessCode (i : Fin 12) (y : Fin 10) : Nat :=
  ([0, 2, 20, 10, 16, 32, 80, 130, 258, 514, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2433, 2306, 0, 2568, 2322, 2594, 0, 2432, 2306, 2562, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6529, 6154, 0, 6154, 6290, 6186, 0, 6274, 6528, 6664, 0, 4106, 4644, 4106, 0, 4136, 4200, 4234, 4866, 4610, 3141, 3218, 3140, 0, 3152, 3172, 3140, 3216, 3456, 0, 0, 5250, 5396, 5258, 5264, 0, 5328, 5250, 5378, 5890, 7237, 7210, 7236, 7208, 7252, 7208, 7236, 0, 0, 7688, 3589, 3842, 3588, 0, 7444, 3620, 0, 0, 3840, 3588, 8329, 8330, 0, 8328, 8400, 9320, 8384, 8328, 0, 0] : List Nat).getD (i.val * 10 + y.val) 0

def witnessVertex (i : Fin 12) (y : Fin 10) : Fin 10 :=
  ⟨witnessCode i y / 1024 % 10, Nat.mod_lt _ (by decide)⟩

def witnessSet (i : Fin 12) (y : Fin 10) : Finset (Fin 10) :=
  SideGeometry.mask (witnessCode i y % 1024)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma witness_valid : ∀ i : Fin 12, ∀ y : Fin 10, y ∉ allowed i →
    let x := witnessVertex i y
    let A := witnessSet i y
    x ∈ side i ∧ y ∈ A ∧
    (∀ u ∈ A, ∀ v ∈ A, ¬ SideGeometry.adj u v) ∧
    (∃ v ∈ A, SideGeometry.adj x v) ∧
    ∀ j : Fin 12, x ∈ side j → j ≠ i → (side j ∩ A).Nonempty := by
  unfold SideGeometry.adj
  decide +kernel

lemma support_bound (S : Fin 12 → Finset (Fin 10))
    (hsub : ∀ i, side i ⊆ S i)
    (hex : ∀ x A, (∀ u ∈ A, ∀ v ∈ A, ¬ SideGeometry.adj u v) →
      (∃ v ∈ A, SideGeometry.adj x v) →
      ∃ i : Fin 12, x ∈ side i ∧ Disjoint (S i) A) :
    ∀ i, S i ⊆ allowed i := by
  intro i y hy
  by_contra hn
  obtain ⟨hx, hyA, hA, hnb, hother⟩ := witness_valid i y hn
  obtain ⟨j, hj, hd⟩ := hex _ _ hA hnb
  by_cases he : j = i
  · subst j
    exact Finset.disjoint_left.mp hd hy hyA
  · obtain ⟨v, hv⟩ := hother j hj he
    obtain ⟨hv, hvA⟩ := Finset.mem_inter.mp hv
    exact Finset.disjoint_left.mp hd (hsub j hv) hvA

end S1SplitGeometry

namespace DagTools

lemma h3_s1_split_source_bounds {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (r : Fin 12 → Nat × Bool)
    (hW : ∀ x : Fin 10, sem_W 10 D x =
      (Finset.univ.filter (fun i : Fin 12 => x ∈ S1SplitGeometry.side i)).image r) :
    ∀ i, supp 10 D (src D (r i)) ⊆ S1SplitGeometry.allowed i := by
  apply S1SplitGeometry.support_bound
  · intro i x hx
    apply (sem_mem_W.mp ?_).2.1
    rw [hW]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hx⟩, rfl⟩
  · intro x A hA hnb
    obtain ⟨j, s, hj, _, hxs, hxn, hd⟩ :=
      sem_exposure petersen_graph_ok h.1 hC A hA x hnb
    have hm : (j, s) ∈ sem_W 10 D x := sem_mem_W.mpr ⟨hj, hxs, hxn⟩
    rw [hW] at hm
    obtain ⟨i, hi, hri⟩ := Finset.mem_image.mp hm
    exact ⟨i, (Finset.mem_filter.mp hi).2, by simpa only [hri] using hd⟩

end DagTools

namespace S1BaseGeometry

def incidenceIndices (x : Fin 10) : Finset (Fin 11) :=
  ([{0}, {1, 2, 10}, {3, 9}, {5, 8}, {1, 4}, {1, 6}, {3, 8}, {7, 8}, {7, 9}, {5, 9}] : List (Finset (Fin 11))).getD x.val ∅

lemma incidence_indices : ∀ x : Fin 10,
    Finset.univ.filter (fun i : Fin 11 => x ∈ side i) = incidenceIndices x := by
  decide +kernel

end S1BaseGeometry

namespace S1SplitGeometry

def incidenceIndices (x : Fin 10) : Finset (Fin 12) :=
  ([{0}, {1, 2, 4}, {3, 11}, {7, 10}, {1, 6}, {1, 8}, {5, 10}, {9, 10}, {9, 11}, {7, 11}] : List (Finset (Fin 12))).getD x.val ∅

lemma incidence_indices : ∀ x : Fin 10,
    Finset.univ.filter (fun i : Fin 12 => x ∈ side i) = incidenceIndices x := by
  decide +kernel

end S1SplitGeometry

namespace DagTools

def h3_s1_baseMap (e0 e4 e5 d a f : ℕ × Bool) (i : Fin 11) : ℕ × Bool :=
  ([e0, h3_opp e0, h3_opp a, a, e4, h3_opp e4, e5, h3_opp e5, d, h3_opp d, f] :
    List (ℕ × Bool)).getD i.val e0

def h3_s1_splitMap (e0 e4 e5 d a b : ℕ × Bool) (i : Fin 12) : ℕ × Bool :=
  ([e0, h3_opp e0, h3_opp a, a, h3_opp b, b, e4, h3_opp e4, e5, h3_opp e5, d, h3_opp d] :
    List (ℕ × Bool)).getD i.val e0

lemma h3_s1_indexed_profiles {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hc : ∀ x : Fin 10, x ≠ 0 → x ≠ 1 → (sem_W 10 D x).card ≤ 2)
    (hc1 : (sem_W 10 D (1 : Fin 10)).card = 3) :
    (∃ e0 e4 e5 d a f : ℕ × Bool,
      supp 10 D (src D e0) = {0} ∧ supp 10 D (src D e4) = {4} ∧ supp 10 D (src D e5) = {5} ∧
      ∀ x : Fin 10, sem_W 10 D x =
        (Finset.univ.filter (fun i : Fin 11 => x ∈ S1BaseGeometry.side i)).image (h3_s1_baseMap e0 e4 e5 d a f)) ∨
    (∃ e0 e4 e5 d a b : ℕ × Bool,
      supp 10 D (src D e0) = {0} ∧ supp 10 D (src D e4) = {4} ∧ supp 10 D (src D e5) = {5} ∧
      ∀ x : Fin 10, sem_W 10 D x =
        (Finset.univ.filter (fun i : Fin 12 => x ∈ S1SplitGeometry.side i)).image (h3_s1_splitMap e0 e4 e5 d a b)) := by
  obtain ⟨e0, e4, e5, d, a, b, hp0, hp4, hp5, hW0, hW4, hW5, hW3, hW7, hW8, hW9, hW2, hW6, hcase⟩ :=
    h3_singleton_one_profiles h hC hz hc hc1
  rcases hcase with ⟨hab, f, _, _, hW1⟩ | ⟨hab, hW1⟩
  · subst b
    left
    refine ⟨e0, e4, e5, d, a, f, hp0, hp4, hp5, ?_⟩
    intro x
    rw [S1BaseGeometry.incidence_indices]
    fin_cases x
    · simpa [sem_W, h3_s1_baseMap, S1BaseGeometry.incidenceIndices, Finset.pair_comm] using hW0
    · simpa [sem_W, h3_s1_baseMap, S1BaseGeometry.incidenceIndices, Finset.pair_comm] using hW1
    · simpa [sem_W, h3_s1_baseMap, S1BaseGeometry.incidenceIndices, Finset.pair_comm] using hW2
    · simpa [sem_W, h3_s1_baseMap, S1BaseGeometry.incidenceIndices, Finset.pair_comm] using hW3
    · simpa [sem_W, h3_s1_baseMap, S1BaseGeometry.incidenceIndices, Finset.pair_comm] using hW4
    · simpa [sem_W, h3_s1_baseMap, S1BaseGeometry.incidenceIndices, Finset.pair_comm] using hW5
    · simpa [sem_W, h3_s1_baseMap, S1BaseGeometry.incidenceIndices, Finset.pair_comm] using hW6
    · simpa [sem_W, h3_s1_baseMap, S1BaseGeometry.incidenceIndices, Finset.pair_comm] using hW7
    · simpa [sem_W, h3_s1_baseMap, S1BaseGeometry.incidenceIndices, Finset.pair_comm] using hW8
    · simpa [sem_W, h3_s1_baseMap, S1BaseGeometry.incidenceIndices, Finset.pair_comm] using hW9
  · right
    refine ⟨e0, e4, e5, d, a, b, hp0, hp4, hp5, ?_⟩
    intro x
    rw [S1SplitGeometry.incidence_indices]
    fin_cases x
    · simpa [sem_W, h3_s1_splitMap, S1SplitGeometry.incidenceIndices, Finset.pair_comm] using hW0
    · simpa [sem_W, h3_s1_splitMap, S1SplitGeometry.incidenceIndices, Finset.pair_comm] using hW1
    · simpa [sem_W, h3_s1_splitMap, S1SplitGeometry.incidenceIndices, Finset.pair_comm] using hW2
    · simpa [sem_W, h3_s1_splitMap, S1SplitGeometry.incidenceIndices, Finset.pair_comm] using hW3
    · simpa [sem_W, h3_s1_splitMap, S1SplitGeometry.incidenceIndices, Finset.pair_comm] using hW4
    · simpa [sem_W, h3_s1_splitMap, S1SplitGeometry.incidenceIndices, Finset.pair_comm] using hW5
    · simpa [sem_W, h3_s1_splitMap, S1SplitGeometry.incidenceIndices, Finset.pair_comm] using hW6
    · simpa [sem_W, h3_s1_splitMap, S1SplitGeometry.incidenceIndices, Finset.pair_comm] using hW7
    · simpa [sem_W, h3_s1_splitMap, S1SplitGeometry.incidenceIndices, Finset.pair_comm] using hW8
    · simpa [sem_W, h3_s1_splitMap, S1SplitGeometry.incidenceIndices, Finset.pair_comm] using hW9

end DagTools

namespace R1FlexibleResource.ResourceExclusion
open CausalBarrier

lemma h3_allowed_if_difference_singleton (a b : Resource) (v : Fin 10)
    (hv : ({v}, ∅) ∈ OtherSides)
    (he : ∀ x : Fin 10, x ≠ v → (x ∈ a.1 ↔ x ∈ b.1)) :
    AllowedSides a b := by
  classical
  have hbase (a b : Resource) (hs : a.1 ⊆ b.1)
      (he : ∀ x : Fin 10, x ≠ v → (x ∈ a.1 ↔ x ∈ b.1)) :
      AllowedSides a b := by
    by_cases ha : a.1.Nonempty
    · exact Or.inl (Or.inr (Or.inl ⟨ha, hs⟩))
    · have haz : a.1 = ∅ := Finset.not_nonempty_iff_eq_empty.mp ha
      have hbsub : b.1 ⊆ {v} := by
        intro x hx
        apply Finset.mem_singleton.mpr
        by_contra hn
        have hxa := (he x hn).mpr hx
        rw [haz] at hxa
        exact Finset.notMem_empty _ hxa
      by_cases hbz : b.1 = ∅
      · exact Or.inl (Or.inl (Or.inl (haz.trans hbz.symm)))
      · have hbe : b.1 = {v} := by
          obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hbz
          have hxv := Finset.mem_singleton.mp (hbsub hx)
          exact Finset.Subset.antisymm hbsub
            (Finset.singleton_subset_iff.mpr (hxv ▸ hx))
        exact Or.inl (Or.inl (Or.inr (Or.inr (by simpa only [haz, hbe] using hv))))
  by_cases hs : a.1 ⊆ b.1
  · exact hbase a b hs he
  · obtain ⟨w, hwa, hwb⟩ := Finset.not_subset.mp hs
    have hw : w = v := by
      by_contra hn
      exact hwb ((he w hn).mp hwa)
    have hsub : b.1 ⊆ a.1 := by
      intro x hx
      by_cases hxv : x = v
      · exact False.elim (hwb (by simpa only [hw, hxv] using hx))
      · exact (he x hxv).mpr hx
    exact allowed_sides_swap (hbase b a hsub (fun x hx => (he x hx).symm))

lemma h3_allowed_if_difference_one (a b : Resource)
    (he : ∀ x : Fin 10, x ≠ 1 → (x ∈ a.1 ↔ x ∈ b.1)) :
    AllowedSides a b :=
  h3_allowed_if_difference_singleton a b 1 (by decide +kernel) he

end R1FlexibleResource.ResourceExclusion

namespace DagTools
open R1FlexibleResource.CausalBarrier R1FlexibleResource.ResourceExclusion
  R1FlexibleResource.DAGBridge

lemma h3_indexed_except_one_exclusion {D : Dag} (hS : Strict 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hB0 : Bzero 10 D = 0)
    {ι : Type*} (r : ι → Nat × Bool) (side : ι → Finset (Fin 10)) (op : ι → ι) (dirty : ι)
    (hopp : ∀ i, r (op i) = ((r i).1, !(r i).2))
    (hsrc : ∀ i, supp 10 D (src D (r i)) = side i)
    (hvalid : ∀ i, (r i).1 < D.length ∧ tag D (r i).1 = true)
    (hda : side dirty = DirtyA) (hdb : side (op dirty) = DirtyB)
    (hothers : ∀ i, i ≠ dirty → op i ≠ dirty →
      (side i, side (op i)) ∈ OtherSides ∨ (side (op i), side i) ∈ OtherSides)
    (hcover : ∀ x : Fin 10, x ≠ 1 → ∀ e ∈ sem_W 10 D x, ∃ i, r i = e) : False := by
  have hdirty : DirtySides D (r dirty).1 := by
    have hA := hsrc dirty
    have hB := hsrc (op dirty)
    rw [hda] at hA
    rw [hdb] at hB
    cases hb : (r dirty).2
    · left
      exact ⟨by simpa [src, hb] using hA, by simpa [hopp, src, hb] using hB⟩
    · right
      exact ⟨by simpa [hopp, src, hb] using hB, by simpa [src, hb] using hA⟩
  have hother : OtherAndSides D (r dirty).1 := by
    intro j hj hjd ht
    by_cases hex : ∃ i, (r i).1 = j
    · obtain ⟨i, hi⟩ := hex
      have he : ∃ k, r k = (j, false) := by
        cases hb : (r i).2
        · exact ⟨i, Prod.ext hi hb⟩
        · refine ⟨op i, ?_⟩
          rw [hopp, hi, hb]
          rfl
      obtain ⟨k, hk⟩ := he
      have hka : supp 10 D (opA D j) = side k := by
        simpa [hk, src] using hsrc k
      have hkb : supp 10 D (opB D j) = side (op k) := by
        simpa [hopp, hk, src] using hsrc (op k)
      have hkd : k ≠ dirty := by
        intro he
        subst k
        exact hjd (congrArg Prod.fst hk).symm
      have hkod : op k ≠ dirty := by
        intro he
        have hh := congrArg Prod.fst (hopp k)
        rw [he, hk] at hh
        exact hjd hh.symm
      apply Or.inl
      apply Or.inl
      apply Or.inr
      change (supp 10 D (opA D j), supp 10 D (opB D j)) ∈ OtherSides ∨
        (supp 10 D (opB D j), supp 10 D (opA D j)) ∈ OtherSides
      rw [hka, hkb]
      exact hothers k hkd hkod
    · apply h3_allowed_if_difference_one
      exact h3_nonindexed_and_same_off hS r 1 hcover hj ht (fun i hi => hex ⟨i, hi⟩)
  exact h3_r1_flexible_allowed_sides_exclusion hS hC hB0
    (hvalid dirty).1 (hvalid dirty).2 hdirty hother


def h3_s1_splitOpposite (i : Fin 12) : Fin 12 :=
  ([1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10] : List (Fin 12)).getD i.val 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma h3_s1_base_other_sides : ∀ i : Fin 10, i ≠ 8 → SideGeometry.opposite i ≠ 8 →
    (SideGeometry.side i, SideGeometry.side (SideGeometry.opposite i)) ∈ OtherSides ∨
    (SideGeometry.side (SideGeometry.opposite i), SideGeometry.side i) ∈ OtherSides := by
  unfold SideGeometry.side SideGeometry.mask SideGeometry.opposite OtherSides
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma h3_s1_split_other_sides : ∀ i : Fin 12, i ≠ 10 → h3_s1_splitOpposite i ≠ 10 →
    (S1SplitGeometry.side i, S1SplitGeometry.side (h3_s1_splitOpposite i)) ∈ OtherSides ∨
    (S1SplitGeometry.side (h3_s1_splitOpposite i), S1SplitGeometry.side i) ∈ OtherSides := by
  unfold S1SplitGeometry.side SideGeometry.mask h3_s1_splitOpposite OtherSides
  decide +kernel

lemma h3_s1_base_indexed_exclusion {D : Dag} (hS : Strict 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hB0 : Bzero 10 D = 0)
    (r : Fin 10 → Nat × Bool)
    (hopp : ∀ i, r (SideGeometry.opposite i) = ((r i).1, !(r i).2))
    (hsrc : ∀ i, supp 10 D (src D (r i)) = SideGeometry.side i)
    (hvalid : ∀ i, (r i).1 < D.length ∧ tag D (r i).1 = true)
    (hcover : ∀ x : Fin 10, x ≠ 1 → ∀ e ∈ sem_W 10 D x, ∃ i, r i = e) : False :=
  h3_indexed_except_one_exclusion hS hC hB0 r SideGeometry.side SideGeometry.opposite 8
    hopp hsrc hvalid (by decide +kernel) (by decide +kernel) h3_s1_base_other_sides hcover

lemma h3_s1_split_indexed_exclusion {D : Dag} (hS : Strict 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hB0 : Bzero 10 D = 0)
    (r : Fin 12 → Nat × Bool)
    (hopp : ∀ i, r (h3_s1_splitOpposite i) = ((r i).1, !(r i).2))
    (hsrc : ∀ i, supp 10 D (src D (r i)) = S1SplitGeometry.side i)
    (hvalid : ∀ i, (r i).1 < D.length ∧ tag D (r i).1 = true)
    (hcover : ∀ x : Fin 10, x ≠ 1 → ∀ e ∈ sem_W 10 D x, ∃ i, r i = e) : False :=
  h3_indexed_except_one_exclusion hS hC hB0 r S1SplitGeometry.side h3_s1_splitOpposite 10
    hopp hsrc hvalid (by decide +kernel) (by decide +kernel) h3_s1_split_other_sides hcover

end DagTools

namespace DagTools

lemma h3_s1_baseMap_prefix (e0 e4 e5 d a f : Nat × Bool) (i : Fin 10) :
    h3_s1_baseMap e0 e4 e5 d a f ⟨i.val, by omega⟩ = h3_sideMap e0 (h3_opp a) e4 e5 d i := by
  fin_cases i <;> simp [h3_s1_baseMap, h3_sideMap, h3_opp_opp]

lemma h3_s1_splitMap_opposite (e0 e4 e5 d a b : Nat × Bool) : ∀ i : Fin 12,
    h3_s1_splitMap e0 e4 e5 d a b (h3_s1_splitOpposite i) =
      ((h3_s1_splitMap e0 e4 e5 d a b i).1, !(h3_s1_splitMap e0 e4 e5 d a b i).2) := by
  intro i
  fin_cases i <;> simp [h3_s1_splitMap, h3_s1_splitOpposite, h3_opp]

lemma h3_nonempty_incidence_gate_valid {D : Dag} (hS : Strict 10 D)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (side : ι → Finset (Fin 10))
    (r : ι → Nat × Bool) (hn : ∀ i, (side i).Nonempty)
    (hW : ∀ x : Fin 10, sem_W 10 D x =
      (Finset.univ.filter (fun i => x ∈ side i)).image r) :
    ∀ i, (r i).1 < D.length ∧ tag D (r i).1 = true := by
  intro i
  obtain ⟨x, hx⟩ := hn i
  have hm : r i ∈ sem_W 10 D x := by
    rw [hW]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hx⟩, rfl⟩
  exact ⟨(sem_mem_W.mp hm).1, h3_exit_tag_and hS hm⟩

lemma h3_s1_base_first_ten_cover {D : Dag} (e0 e4 e5 d a f : Nat × Bool)
    (hW : ∀ x : Fin 10, sem_W 10 D x =
      (Finset.univ.filter (fun i : Fin 11 => x ∈ S1BaseGeometry.side i)).image
        (h3_s1_baseMap e0 e4 e5 d a f)) :
    ∀ x : Fin 10, x ≠ 1 → ∀ e ∈ sem_W 10 D x,
      ∃ i : Fin 10, h3_sideMap e0 (h3_opp a) e4 e5 d i = e := by
  intro x hx e he
  rw [hW] at he
  obtain ⟨i, hi, hr⟩ := Finset.mem_image.mp he
  by_cases hlt : i.val < 10
  · refine ⟨⟨i.val, hlt⟩, ?_⟩
    rw [← h3_s1_baseMap_prefix e0 e4 e5 d a f]
    convert hr using 1
  · have hi10 : i = 10 := Fin.ext (by omega)
    subst i
    have hm := (Finset.mem_filter.mp hi).2
    have hs : S1BaseGeometry.side 10 = {(1 : Fin 10)} := by decide +kernel
    rw [hs, Finset.mem_singleton] at hm
    exact (hx hm).elim

lemma h3_s1_split_cover {D : Dag} (r : Fin 12 → Nat × Bool)
    (hW : ∀ x : Fin 10, sem_W 10 D x =
      (Finset.univ.filter (fun i : Fin 12 => x ∈ S1SplitGeometry.side i)).image r) :
    ∀ x : Fin 10, x ≠ 1 → ∀ e ∈ sem_W 10 D x, ∃ i, r i = e := by
  intro x _ e he
  rw [hW] at he
  obtain ⟨i, _, hr⟩ := Finset.mem_image.mp he
  exact ⟨i, hr⟩

lemma h3_s1_base_gate_valid {D : Dag} (hS : Strict 10 D) (e0 e4 e5 d a f : Nat × Bool)
    (hW : ∀ x : Fin 10, sem_W 10 D x =
      (Finset.univ.filter (fun i : Fin 11 => x ∈ S1BaseGeometry.side i)).image
        (h3_s1_baseMap e0 e4 e5 d a f)) :
    ∀ i : Fin 10, (h3_sideMap e0 (h3_opp a) e4 e5 d i).1 < D.length ∧
      tag D (h3_sideMap e0 (h3_opp a) e4 e5 d i).1 = true := by
  have hv := h3_nonempty_incidence_gate_valid hS S1BaseGeometry.side
    (h3_s1_baseMap e0 e4 e5 d a f) (by decide +kernel) hW
  intro i
  simpa only [h3_s1_baseMap_prefix] using hv ⟨i.val, by omega⟩

lemma h3_s1_split_gate_valid {D : Dag} (hS : Strict 10 D) (r : Fin 12 → Nat × Bool)
    (hW : ∀ x : Fin 10, sem_W 10 D x =
      (Finset.univ.filter (fun i : Fin 12 => x ∈ S1SplitGeometry.side i)).image r) :
    ∀ i, (r i).1 < D.length ∧ tag D (r i).1 = true :=
  h3_nonempty_incidence_gate_valid hS S1SplitGeometry.side r (by decide +kernel) hW


end DagTools

namespace DagTools

lemma h3_s1_no_and_output {D : Dag} (hS : Strict 10 D) (x : Fin 10)
    (hM : merges 10 D (carrierT 10 D {x}) = ∅)
    {j : Nat} (hj : j < D.length) (ht : tag D j = true) : x ∉ supp 10 D (10+j) := by
  intro hx
  have ha : x ∈ supp 10 D (opA D j) := sem_supp_and_sub hS hj ht false hx
  have hb : x ∈ supp 10 D (opB D j) := sem_supp_and_sub hS hj ht true hx
  have hm : j ∈ merges 10 D (carrierT 10 D {x}) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, sem_mem_carrier1.mpr hx,
      sem_mem_carrier1.mpr ha,sem_mem_carrier1.mpr hb⟩
  rw [hM] at hm
  exact Finset.notMem_empty j hm

lemma h3_s1_pair_output_empty {D : Dag} (hS : Strict 10 D)
    (hM2 : merges 10 D (carrierT 10 D {(2 : Fin 10)}) = ∅)
    (hM6 : merges 10 D (carrierT 10 D {(6 : Fin 10)}) = ∅)
    (e : Nat × Bool) (he : e.1 < D.length) (ht : tag D e.1 = true)
    (hb : supp 10 D (src D (h3_opp e)) ⊆ {(2 : Fin 10),6}) :
    supp 10 D (10+e.1) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hb' : x ∈ supp 10 D (src D (h3_opp e)) := sem_supp_and_sub hS he ht (!e.2) hx
  have hm := hb hb'
  simp only [Finset.mem_insert,Finset.mem_singleton] at hm
  rcases hm with rfl | rfl
  · exact h3_s1_no_and_output hS 2 hM2 he ht hx
  · exact h3_s1_no_and_output hS 6 hM6 he ht hx

lemma h3_three_slots_distinct {α : Type*} [DecidableEq α] (a b c : α)
    (hc : ({a,b,c} : Finset α).card = 3) : b ≠ a ∧ c ≠ a ∧ b ≠ c := by
  have hab : b ≠ a := by
    intro h; subst b
    have hh : ({a,c} : Finset α).card ≤ 2 := Finset.card_le_two
    have hc' : ({a,c} : Finset α).card = 3 := by simpa using hc
    omega
  have hac : c ≠ a := by
    intro h; subst c
    have hh : ({a,b} : Finset α).card ≤ 2 := Finset.card_le_two
    have he : ({a,b,a} : Finset α) = {a,b} := by ext x; simp; tauto
    rw [he] at hc
    omega
  have hbc : b ≠ c := by
    intro h; subst b
    have hh : ({a,c} : Finset α).card ≤ 2 := Finset.card_le_two
    have hc' : ({a,c} : Finset α).card = 3 := by simpa using hc
    omega
  exact ⟨hab,hac,hbc⟩

lemma h3_indexed_source_lower {D : Dag} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ι → Nat × Bool) (side : ι → Finset (Fin 10))
    (hW : ∀ x : Fin 10, sem_W 10 D x = (Finset.univ.filter (fun i => x ∈ side i)).image r) :
    ∀ i, side i ⊆ supp 10 D (src D (r i)) := by
  intro i x hx
  apply (sem_mem_W.mp ?_).2.1
  rw [hW]
  exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hx⟩,rfl⟩

lemma h3_indexed_mem_of_side {D : Dag} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ι → Nat × Bool) (side : ι → Finset (Fin 10))
    (hW : ∀ x : Fin 10, sem_W 10 D x = (Finset.univ.filter (fun i => x ∈ side i)).image r)
    {i : ι} {x : Fin 10} (hx : x ∈ side i) : r i ∈ sem_W 10 D x := by
  rw [hW]
  exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hx⟩,rfl⟩

lemma h3_source_index_of_empty_output {D : Dag} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ι → Nat × Bool) (side : ι → Finset (Fin 10))
    (hW : ∀ x : Fin 10, sem_W 10 D x = (Finset.univ.filter (fun i => x ∈ side i)).image r)
    {e : Nat × Bool} (he : e.1 < D.length) (hout : supp 10 D (10+e.1) = ∅)
    {y : Fin 10} (hy : y ∈ supp 10 D (src D e)) : ∃ j, y ∈ side j ∧ r j = e := by
  have hm : e ∈ sem_W 10 D y := sem_mem_W.mpr ⟨he,hy,by rw [hout]; simp⟩
  rw [hW] at hm
  obtain ⟨j,hj,heq⟩ := Finset.mem_image.mp hm
  exact ⟨j,(Finset.mem_filter.mp hj).2,heq⟩

lemma h3_private_one_source {D : Dag} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ι → Nat × Bool) (side allowed : ι → Finset (Fin 10)) (star : ι)
    (hW : ∀ x : Fin 10, sem_W 10 D x = (Finset.univ.filter (fun i => x ∈ side i)).image r)
    (hb : ∀ i, supp 10 D (src D (r i)) ⊆ allowed i)
    (hgeo : ∀ j y, (1 : Fin 10) ∈ allowed j → y ∈ side j → y ≠ 1 → j = star)
    {e : Nat × Bool} (he : e ∈ sem_W 10 D (1 : Fin 10))
    (hout : supp 10 D (10+e.1) = ∅) (hne : e ≠ r star) :
    supp 10 D (src D e) = {(1 : Fin 10)} := by
  apply Finset.Subset.antisymm
  · intro y hy
    apply Finset.mem_singleton.mpr
    by_contra hy1
    obtain ⟨j,hj,hrj⟩ := h3_source_index_of_empty_output r side hW (sem_mem_W.mp he).1 hout hy
    have h1 : (1 : Fin 10) ∈ allowed j := hb j (by rw [hrj]; exact (sem_mem_W.mp he).2.1)
    have hjstar := hgeo j y h1 hj hy1
    exact hne (hrj.symm.trans (congrArg r hjstar))
  · exact Finset.singleton_subset_iff.mpr (sem_mem_W.mp he).2.1

end DagTools

namespace S1BaseGeometry
lemma one_location : ∀ j : Fin 11, ∀ y : Fin 10,
    1 ∈ allowed j → y ∈ side j → y ≠ 1 → j = 1 := by decide +kernel
end S1BaseGeometry

namespace S1SplitGeometry
lemma one_location : ∀ j : Fin 12, ∀ y : Fin 10,
    1 ∈ allowed j → y ∈ side j → y ≠ 1 → j = 1 := by decide +kernel
lemma six_with_two : ∀ j : Fin 12, 6 ∈ side j → 2 ∈ allowed j → j = 5 := by decide +kernel
lemma two_with_six : ∀ j : Fin 12, 2 ∈ side j → 6 ∈ allowed j → j = 3 := by decide +kernel
end S1SplitGeometry

namespace DagTools

lemma h3_s1_base_sources {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hB0 : Bzero 10 D = 0)
    (hM2 : merges 10 D (carrierT 10 D {(2 : Fin 10)}) = ∅)
    (hM6 : merges 10 D (carrierT 10 D {(6 : Fin 10)}) = ∅)
    (e0 e4 e5 d a f : Nat × Bool)
    (hp0 : supp 10 D (src D e0) = {0})
    (hp4 : supp 10 D (src D e4) = {4})
    (hp5 : supp 10 D (src D e5) = {5})
    (hc1 : (sem_W 10 D (1 : Fin 10)).card = 3)
    (hW : ∀ x : Fin 10, sem_W 10 D x =
      (Finset.univ.filter (fun i : Fin 11 => x ∈ S1BaseGeometry.side i)).image
        (h3_s1_baseMap e0 e4 e5 d a f)) :
    ∀ i : Fin 11, i ≠ 10 →
      supp 10 D (src D (h3_s1_baseMap e0 e4 e5 d a f i)) = S1BaseGeometry.side i := by
  let R := h3_s1_baseMap e0 e4 e5 d a f
  have hb := h3_s1_base_source_bounds h hC R hW
  have hlo := h3_indexed_source_lower R S1BaseGeometry.side hW
  have hfromBounds (i : Fin 11) (hi : S1BaseGeometry.allowed i = S1BaseGeometry.side i) :
      supp 10 D (src D (R i)) = S1BaseGeometry.side i := by
    apply Finset.Subset.antisymm
    · simpa only [hi] using hb i
    · exact hlo i
  have hc : ({R 1,R 2,R 10} : Finset (Nat × Bool)).card = 3 := by
    rw [hW,S1BaseGeometry.incidence_indices] at hc1
    simpa [S1BaseGeometry.incidenceIndices,R] using hc1
  have hneq := h3_three_slots_distinct (R 1) (R 2) (R 10) hc
  have hm2 : R 2 ∈ sem_W 10 D (1 : Fin 10) :=
    h3_indexed_mem_of_side R S1BaseGeometry.side hW (by decide)
  have hbar : supp 10 D (src D (h3_opp (R 2))) ⊆ {(2 : Fin 10),6} := by
    have hu := hb 3
    rw [show S1BaseGeometry.allowed 3 = ({2,6} : Finset (Fin 10)) by decide] at hu
    simpa [R,h3_s1_baseMap,h3_opp_opp] using hu
  have hout2 := h3_s1_pair_output_empty h.1 hM2 hM6 (R 2)
    (sem_mem_W.mp hm2).1 (sem_W_and h.1 hm2) hbar
  have hp1 := h3_private_one_source R S1BaseGeometry.side S1BaseGeometry.allowed 1 hW hb
    S1BaseGeometry.one_location hm2 hout2 hneq.1
  have hW4 : sem_W 10 D (4 : Fin 10) = {h3_opp e0,e4} := by
    rw [hW,S1BaseGeometry.incidence_indices]
    simp [h3_s1_baseMap,S1BaseGeometry.incidenceIndices]
  have hN : ({1,4,5} : Finset (Fin 10)) ⊆ supp 10 D (src D (h3_opp e0)) := by
    have hh := hlo 1
    rw [show S1BaseGeometry.side 1 = ({1,4,5} : Finset (Fin 10)) by decide] at hh
    simpa [R,h3_s1_baseMap] using hh
  have hstar := h3_star0_exact_of_two_exit_pure_companion h hC hz hB0 (h3_opp e0) e4 hW4 hp4 hN
  intro i hi
  fin_cases i
  · exact hp0.trans (by decide)
  · exact hstar.trans (by decide)
  · exact hp1.trans (by decide)
  · exact hfromBounds 3 (by decide)
  · exact hp4.trans (by decide)
  · exact hfromBounds 5 (by decide)
  · exact hp5.trans (by decide)
  · exact hfromBounds 7 (by decide)
  · exact hfromBounds 8 (by decide)
  · exact hfromBounds 9 (by decide)
  · exact (hi rfl).elim

end DagTools

namespace DagTools

lemma h3_s1_split_sources {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hB0 : Bzero 10 D = 0)
    (hM2 : merges 10 D (carrierT 10 D {(2 : Fin 10)}) = ∅)
    (hM6 : merges 10 D (carrierT 10 D {(6 : Fin 10)}) = ∅)
    (e0 e4 e5 d a b : Nat × Bool)
    (hp0 : supp 10 D (src D e0) = {0})
    (hp4 : supp 10 D (src D e4) = {4})
    (hp5 : supp 10 D (src D e5) = {5})
    (hc1 : (sem_W 10 D (1 : Fin 10)).card = 3)
    (hW : ∀ x : Fin 10, sem_W 10 D x =
      (Finset.univ.filter (fun i : Fin 12 => x ∈ S1SplitGeometry.side i)).image
        (h3_s1_splitMap e0 e4 e5 d a b)) :
    ∀ i : Fin 12,
      supp 10 D (src D (h3_s1_splitMap e0 e4 e5 d a b i)) = S1SplitGeometry.side i := by
  let R := h3_s1_splitMap e0 e4 e5 d a b
  have hbnd := h3_s1_split_source_bounds h hC R hW
  have hlo := h3_indexed_source_lower R S1SplitGeometry.side hW
  have hfromBounds (i : Fin 12) (hi : S1SplitGeometry.allowed i = S1SplitGeometry.side i) :
      supp 10 D (src D (R i)) = S1SplitGeometry.side i := by
    apply Finset.Subset.antisymm
    · simpa only [hi] using hbnd i
    · exact hlo i
  have hc : ({R 1,R 2,R 4} : Finset (Nat × Bool)).card = 3 := by
    rw [hW,S1SplitGeometry.incidence_indices] at hc1
    simpa [S1SplitGeometry.incidenceIndices,R] using hc1
  have hneq := h3_three_slots_distinct (R 1) (R 2) (R 4) hc
  have hm2 : R 2 ∈ sem_W 10 D (1 : Fin 10) :=
    h3_indexed_mem_of_side R S1SplitGeometry.side hW (by decide)
  have hm4 : R 4 ∈ sem_W 10 D (1 : Fin 10) :=
    h3_indexed_mem_of_side R S1SplitGeometry.side hW (by decide)
  have hm3 : R 3 ∈ sem_W 10 D (2 : Fin 10) :=
    h3_indexed_mem_of_side R S1SplitGeometry.side hW (by decide)
  have hm5 : R 5 ∈ sem_W 10 D (6 : Fin 10) :=
    h3_indexed_mem_of_side R S1SplitGeometry.side hW (by decide)
  have hbar2 : supp 10 D (src D (h3_opp (R 2))) ⊆ {(2 : Fin 10),6} := by
    have hu := hbnd 3
    rw [show S1SplitGeometry.allowed 3 = ({2,6} : Finset (Fin 10)) by decide] at hu
    simpa [R,h3_s1_splitMap,h3_opp_opp] using hu
  have hbar4 : supp 10 D (src D (h3_opp (R 4))) ⊆ {(2 : Fin 10),6} := by
    have hu := hbnd 5
    rw [show S1SplitGeometry.allowed 5 = ({2,6} : Finset (Fin 10)) by decide] at hu
    simpa [R,h3_s1_splitMap,h3_opp_opp] using hu
  have hout2 := h3_s1_pair_output_empty h.1 hM2 hM6 (R 2)
    (sem_mem_W.mp hm2).1 (sem_W_and h.1 hm2) hbar2
  have hout4 := h3_s1_pair_output_empty h.1 hM2 hM6 (R 4)
    (sem_mem_W.mp hm4).1 (sem_W_and h.1 hm4) hbar4
  have hpA := h3_private_one_source R S1SplitGeometry.side S1SplitGeometry.allowed 1 hW hbnd
    S1SplitGeometry.one_location hm2 hout2 hneq.1
  have hpB := h3_private_one_source R S1SplitGeometry.side S1SplitGeometry.allowed 1 hW hbnd
    S1SplitGeometry.one_location hm4 hout4 hneq.2.1
  have h35 : R 3 ≠ R 5 := by
    intro he
    apply hneq.2.2
    simpa [R,h3_s1_splitMap,h3_opp_opp] using congrArg h3_opp he
  have hout3 : supp 10 D (10+(R 3).1) = ∅ := by simpa [R,h3_s1_splitMap,h3_opp] using hout2
  have hout5 : supp 10 D (10+(R 5).1) = ∅ := by simpa [R,h3_s1_splitMap,h3_opp] using hout4
  have hnot6 : (6 : Fin 10) ∉ supp 10 D (src D (R 3)) := by
    intro hy
    obtain ⟨j,hj,hrj⟩ := h3_source_index_of_empty_output R S1SplitGeometry.side hW
      (sem_mem_W.mp hm3).1 hout3 hy
    have h2 : (2 : Fin 10) ∈ S1SplitGeometry.allowed j := hbnd j (by
      rw [hrj]; exact (sem_mem_W.mp hm3).2.1)
    have hj5 := S1SplitGeometry.six_with_two j hj h2
    rw [hj5] at hrj
    exact h35 hrj.symm
  have hnot2 : (2 : Fin 10) ∉ supp 10 D (src D (R 5)) := by
    intro hy
    obtain ⟨j,hj,hrj⟩ := h3_source_index_of_empty_output R S1SplitGeometry.side hW
      (sem_mem_W.mp hm5).1 hout5 hy
    have h6 : (6 : Fin 10) ∈ S1SplitGeometry.allowed j := hbnd j (by
      rw [hrj]; exact (sem_mem_W.mp hm5).2.1)
    have hj3 := S1SplitGeometry.two_with_six j hj h6
    rw [hj3] at hrj
    exact h35 hrj
  have hp3 : supp 10 D (src D (R 3)) = {(2 : Fin 10)} := by
    apply Finset.Subset.antisymm
    · intro x hx
      have hh := hbnd 3 hx
      rw [show S1SplitGeometry.allowed 3 = ({2,6} : Finset (Fin 10)) by decide] at hh
      simp only [Finset.mem_insert,Finset.mem_singleton] at hh
      rcases hh with he | he
      · exact Finset.mem_singleton.mpr he
      · exact (hnot6 (he ▸ hx)).elim
    · exact Finset.singleton_subset_iff.mpr (sem_mem_W.mp hm3).2.1
  have hp5' : supp 10 D (src D (R 5)) = {(6 : Fin 10)} := by
    apply Finset.Subset.antisymm
    · intro x hx
      have hh := hbnd 5 hx
      rw [show S1SplitGeometry.allowed 5 = ({2,6} : Finset (Fin 10)) by decide] at hh
      simp only [Finset.mem_insert,Finset.mem_singleton] at hh
      rcases hh with he | he
      · exact (hnot2 (he ▸ hx)).elim
      · exact Finset.mem_singleton.mpr he
    · exact Finset.singleton_subset_iff.mpr (sem_mem_W.mp hm5).2.1
  have hW4 : sem_W 10 D (4 : Fin 10) = {h3_opp e0,e4} := by
    rw [hW,S1SplitGeometry.incidence_indices]
    simp [h3_s1_splitMap,S1SplitGeometry.incidenceIndices]
  have hN : ({1,4,5} : Finset (Fin 10)) ⊆ supp 10 D (src D (h3_opp e0)) := by
    have hh := hlo 1
    rw [show S1SplitGeometry.side 1 = ({1,4,5} : Finset (Fin 10)) by decide] at hh
    simpa [R,h3_s1_splitMap] using hh
  have hstar := h3_star0_exact_of_two_exit_pure_companion h hC hz hB0 (h3_opp e0) e4 hW4 hp4 hN
  intro i
  fin_cases i
  · exact hp0.trans (by decide)
  · exact hstar.trans (by decide)
  · exact hpA.trans (by decide)
  · exact hp3.trans (by decide)
  · exact hpB.trans (by decide)
  · exact hp5'.trans (by decide)
  · exact hp4.trans (by decide)
  · exact hfromBounds 7 (by decide)
  · exact hp5.trans (by decide)
  · exact hfromBounds 9 (by decide)
  · exact hfromBounds 10 (by decide)
  · exact hfromBounds 11 (by decide)

end DagTools

namespace DagTools

lemma h3_s1_base_side_prefix (i : Fin 10) :
    S1BaseGeometry.side ⟨i.val, by omega⟩ = SideGeometry.side i := by
  fin_cases i <;> decide +kernel

lemma h3_singleton_one_exclusion {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hB0 : Bzero 10 D = 0)
    (hM2 : merges 10 D (carrierT 10 D {(2 : Fin 10)}) = ∅)
    (hM6 : merges 10 D (carrierT 10 D {(6 : Fin 10)}) = ∅)
    (hc : ∀ x : Fin 10, x ≠ 0 → x ≠ 1 → (sem_W 10 D x).card ≤ 2)
    (hc1 : (sem_W 10 D (1 : Fin 10)).card = 3) : False := by
  rcases h3_s1_indexed_profiles h hC hz hc hc1 with
    ⟨e0, e4, e5, d, a, f, hp0, hp4, hp5, hW⟩ | ⟨e0, e4, e5, d, a, b, hp0, hp4, hp5, hW⟩
  · have hsrc : ∀ i : Fin 10,
        supp 10 D (src D (h3_sideMap e0 (h3_opp a) e4 e5 d i)) = SideGeometry.side i := by
      intro i
      have hs := h3_s1_base_sources h hC hz hB0 hM2 hM6 e0 e4 e5 d a f hp0 hp4 hp5 hc1 hW
        ⟨i.val, by omega⟩ (by intro he; have hv := congrArg Fin.val he; simp at hv; omega)
      simpa only [h3_s1_baseMap_prefix, h3_s1_base_side_prefix] using hs
    exact h3_s1_base_indexed_exclusion h.1 hC hB0 (h3_sideMap e0 (h3_opp a) e4 e5 d)
      (h3_sideMap_opposite e0 (h3_opp a) e4 e5 d) hsrc
      (h3_s1_base_gate_valid h.1 e0 e4 e5 d a f hW)
      (h3_s1_base_first_ten_cover e0 e4 e5 d a f hW)
  · have hsrc := h3_s1_split_sources h hC hz hB0 hM2 hM6 e0 e4 e5 d a b hp0 hp4 hp5 hc1 hW
    exact h3_s1_split_indexed_exclusion h.1 hC hB0 (h3_s1_splitMap e0 e4 e5 d a b)
      (h3_s1_splitMap_opposite e0 e4 e5 d a b) hsrc
      (h3_s1_split_gate_valid h.1 (h3_s1_splitMap e0 e4 e5 d a b) hW)
      (h3_s1_split_cover (h3_s1_splitMap e0 e4 e5 d a b) hW)


end DagTools

namespace DagTools

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

end DagTools

namespace H3ResidualLocalization
open PEqualNP.Outside.L_meta_2590_aux.DagTools
open PEqualNP.Outside.L_meta_2590_aux.H3CoStar

set_option maxHeartbeats 0 in
lemma zero_neighbors : ∀ x : (Fin 10), petersenAdj 0 x ↔ x ∈ ({1,4,5} : Finset (Fin 10)) := by
  unfold petersenAdj
  decide +kernel

set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 65536 in
lemma exposure_vertices : ∀ x c : (Fin 10), petersenAdj 0 x → c ≠ 0 → ¬ petersenAdj 0 c →
    ∃ m y : (Fin 10), petersenAdj x m ∧ petersenAdj 0 y ∧ ¬ petersenAdj c m ∧ ¬ petersenAdj c y ∧ ¬ petersenAdj m y := by
  unfold petersenAdj
  decide +kernel

lemma exposure_geometry {x c : (Fin 10)} (hx : petersenAdj 0 x) (hc : c ≠ 0) (hcn : ¬ petersenAdj 0 c) :
    ∃ A : Finset (Fin 10), (∀ a ∈ A, ∀ d ∈ A, ¬ petersenAdj a d) ∧ c ∈ A ∧
      (∃ a ∈ A, petersenAdj 0 a) ∧ (∃ a ∈ A, petersenAdj x a) := by
  obtain ⟨m,y,hxm,hiy,hcm,hcy,hmy⟩ := exposure_vertices x c hx hc hcn
  refine ⟨{c,m,y},?_,by simp,⟨y,by simp,hiy⟩,⟨m,by simp,hxm⟩⟩
  intro a ha d hd
  simp only [Finset.mem_insert,Finset.mem_singleton] at ha hd
  rcases ha with rfl | rfl | rfl <;> rcases hd with rfl | rfl | rfl
  · exact petersen_graph_ok.2.1 _
  · exact hcm
  · exact hcy
  · exact fun hmc => hcm (petersen_graph_ok.1 _ _ hmc)
  · exact petersen_graph_ok.2.1 _
  · exact hmy
  · exact fun hyc => hcy (petersen_graph_ok.1 _ _ hyc)
  · exact fun hym => hmy (petersen_graph_ok.1 _ _ hym)
  · exact petersen_graph_ok.2.1 _

lemma residual_support_eligible {n : Nat} {D : Dag} {b : Fin n → Nat}
    {r : Sigma (fun _ : Nat => Nat)} (hr : r ∈ residualUnits n D b) :
    supp n D r.1 ⊆ eligSet n D := by
  have hu : r ∈ unitsPlus n D := (Finset.mem_sdiff.mp hr).1
  have hm : r ∈ units n D := (Finset.mem_filter.mp hu).1
  have hf := (mem_units.mp hm).2
  intro a ha
  exact mem_eligSet.mpr ⟨r.1,by omega,ha⟩

def ZeroOmission (D : Dag) (c : (Fin 10)) : Prop :=
  ∃ e : Nat × Bool, (∀ x : (Fin 10), petersenAdj 0 x → e ∈ sem_W 10 D x) ∧
    c ∉ supp 10 D (src D e) ∧ ∀ a : (Fin 10), petersenAdj 0 a → a ∈ supp 10 D (src D e)

lemma outside_not_in_single_residual {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 petersenAdj D)
    (b : Fin 10 → Nat) (hb : PureBranch 10 D b)
    (hi : (0 : (Fin 10)) ∈ ineligSet 10 D)
    {r : Sigma (fun _ : Nat => Nat)} (hR : residualUnits 10 D b = {r})
    {x c : (Fin 10)} (hx : petersenAdj 0 x) (hxr : x ∈ supp 10 D r.1)
    (hcE : c ∈ eligSet 10 D) (hcn : ¬ petersenAdj 0 c) (localExit : ZeroOmission D c) :
    c ∉ supp 10 D r.1 := by
  have hr : r ∈ residualUnits 10 D b := hR ▸ Finset.mem_singleton_self r
  have hxE := residual_support_eligible hr hxr
  have hc0 : c ≠ 0 := by
    intro he
    exact (sem_mem_inelig.mp hi) (he ▸ hcE)
  obtain ⟨A,ind,ca,hit0,hitx⟩ := exposure_geometry hx hc0 hcn
  obtain ⟨e,he,hec,hall⟩ := localExit
  obtain ⟨g,s,hg,_,hxs,hxo,free⟩ := sem_exposure petersen_graph_ok h.1 hc A ind x hitx
  have hf : (g,s) ∈ sem_W 10 D x := sem_mem_W.mpr ⟨hg,hxs,hxo⟩
  have hfc : c ∉ supp 10 D (src D (g,s)) := fun hm => Finset.disjoint_left.mp free hm ca
  have hef : e ≠ (g,s) := by
    intro eq
    obtain ⟨a,ha,hia⟩ := hit0
    have has := hall a hia
    rw [eq] at has
    exact Finset.disjoint_left.mp free has ha
  obtain ⟨u,hu,_,hcu⟩ := residual_separation_of_two_omissions petersen_graph_ok h hc b hb
    (show x ≠ c from fun eq => hcn (eq ▸ hx)) hxE ⟨r,hr,hxr⟩ (he x hx) hf hef hec hfc
  have eq : u = r := by simpa only [hR,Finset.mem_singleton] using hu
  exact eq ▸ hcu

lemma single_residual_support_subset {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 petersenAdj D)
    (b : Fin 10 → Nat) (hb : PureBranch 10 D b)
    (hi : (0 : (Fin 10)) ∈ ineligSet 10 D)
    {r : Sigma (fun _ : Nat => Nat)} (hR : residualUnits 10 D b = {r})
    (coded : ∃ x : (Fin 10), petersenAdj 0 x ∧ x ∈ supp 10 D r.1)
    (localExits : ∀ c : (Fin 10), c ∈ eligSet 10 D → ¬ petersenAdj 0 c → ZeroOmission D c) :
    supp 10 D r.1 ⊆ ({1,4,5} : Finset (Fin 10)) := by
  obtain ⟨x,hx,hxr⟩ := coded
  have hr : r ∈ residualUnits 10 D b := hR ▸ Finset.mem_singleton_self r
  intro c hcr
  apply (zero_neighbors c).mp
  by_contra hcn
  have hcE := residual_support_eligible hr hcr
  exact outside_not_in_single_residual h hc b hb hi hR hx hxr hcE hcn
    (localExits c hcE hcn) hcr


lemma single_residual_support_subset_of_bzero {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 petersenAdj D)
    (b : Fin 10 → Nat) (hb : PureBranch 10 D b)
    (zero : Bzero 10 D = 0) (hi : (0 : (Fin 10)) ∈ ineligSet 10 D)
    {r : Sigma (fun _ : Nat => Nat)} (hR : residualUnits 10 D b = {r})
    (coded : ∃ x : (Fin 10), petersenAdj 0 x ∧ x ∈ supp 10 D r.1) :
    supp 10 D r.1 ⊆ ({1,4,5} : Finset (Fin 10)) := by
  classical
  exact single_residual_support_subset h hc b hb hi hR coded
    (fun c _ hcn => sem_neighbor_exclusion_slot_of_bzero petersen_graph_ok h hc zero hi c hcn)

end H3ResidualLocalization

namespace DagTools

lemma h3_single_residual_support_subset_of_bzero {D : Dag}
    (h : StrictLive 10 D) (hC : sem_Comp 10 petersenAdj D)
    (b : Fin 10 → ℕ) (hb : PureBranch 10 D b)
    (hB0 : Bzero 10 D = 0) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    {r : Σ _ : ℕ, ℕ} (hR : residualUnits 10 D b = {r})
    (coded : ∃ x ∈ ({1, 4, 5} : Finset (Fin 10)), x ∈ supp 10 D r.1) :
    supp 10 D r.1 ⊆ ({1, 4, 5} : Finset (Fin 10)) := by
  obtain ⟨x, hx, hxr⟩ := coded
  exact H3ResidualLocalization.single_residual_support_subset_of_bzero h hC b hb hB0 hz hR
    ⟨x, (H3ResidualLocalization.zero_neighbors x).mpr hx, hxr⟩

end DagTools

namespace DagTools

lemma h3_saturated_one_exclusion {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hB0 : Bzero 10 D = 0)
    (hone : Bplus 10 D = (eligSet 10 D).card + 1)
    (hSat : h3_saturatedSet 10 D = {1}) : False := by
  obtain ⟨b, hb⟩ := sem_exists_pureBranch petersen_graph_ok h.1 hC
  have hcard : (residualUnits 10 D b).card = 1 := by
    have := card_residual h.1 b hb
    omega
  obtain ⟨r, hR⟩ := Finset.card_eq_one.mp hcard
  have h1 : (1 : Fin 10) ∈ h3_saturatedSet 10 D := by
    rw [hSat]
    exact Finset.mem_singleton_self _
  have h13 : 3 ≤ (sem_W 10 D (1 : Fin 10)).card :=
    (Finset.mem_filter.mp h1).2
  obtain ⟨hc1, _, _, h1R⟩ := sem_saturated petersen_graph_ok h hC b hb hR h13
  have hRS := h3_single_residual_support_subset_of_bzero h hC b hb hB0 hz hR
    ⟨1, by decide, h1R⟩
  have hc := h3_saturated_one_other_exit_cards h hC hz hSat
  have hm (x : Fin 10) (hx0 : x ≠ 0) (hx1 : x ≠ 1)
      (hxR : x ∉ ({1, 4, 5} : Finset (Fin 10))) :
      merges 10 D (carrierT 10 D {x}) = ∅ := by
    have hxR' : x ∉ supp 10 D r.1 := fun hh => hxR (hRS hh)
    have hf := h3_residual_singleton_flow petersen_graph_ok h hC b hb r hR x
    rw [hc x hx0 hx1, if_neg hxR'] at hf
    have he : (if x ∈ eligSet 10 D then 1 else 0) ≤ 1 := by split <;> omega
    exact Finset.card_eq_zero.mp (by omega)
  exact h3_singleton_one_exclusion h hC hz hB0
    (hm 2 (by decide) (by decide) (by decide))
    (hm 6 (by decide) (by decide) (by decide))
    (fun x hx0 hx1 => (hc x hx0 hx1).le) hc1

end DagTools

namespace DagTools

lemma h3_no_opposite_exit {n : Nat} {D : Dag} (hS : Strict n D)
    {x : Fin n} {e : Nat × Bool}
    (he : e ∈ exitArcs n D (carrierT n D {x})) :
    h3_opp e ∉ exitArcs n D (carrierT n D {x}) := by
  intro hf
  obtain ⟨j,s⟩ := e
  obtain ⟨hj,hx,hn⟩ := sem_mem_exit1.mp he
  have hy := (sem_mem_exit1.mp hf).2.1
  apply hn
  rw [sem_supp_and hS hj (h3_exit_tag_and hS he)]
  cases s
  · exact Finset.mem_inter.mpr ⟨hx,hy⟩
  · exact Finset.mem_inter.mpr ⟨hy,hx⟩

lemma h3_common_terminals_force_pair {n : Nat} {D : Dag} (hS : Strict n D)
    {x y : Fin n} {A B C P Q : Nat × Bool}
    (hycard : (exitArcs n D (carrierT n D {y})).card = 3)
    (hAy : A ∈ exitArcs n D (carrierT n D {y}))
    (hBy : B ∈ exitArcs n D (carrierT n D {y}))
    (hCy : C ∈ exitArcs n D (carrierT n D {y}))
    (hAB : A ≠ B) (hAC : A ≠ C)
    (hBx : h3_opp B ∈ exitArcs n D (carrierT n D {x}))
    (hCx : h3_opp C ∈ exitArcs n D (carrierT n D {x}))
    (hPx : P ∈ exitArcs n D (carrierT n D {x}))
    (hPy : P ∈ exitArcs n D (carrierT n D {y}))
    (hQx : Q ∈ exitArcs n D (carrierT n D {x}))
    (hQy : Q ∈ exitArcs n D (carrierT n D {y})) (hPQ : P ≠ Q) : B = C := by
  by_contra hBC
  have hWy : exitArcs n D (carrierT n D {y}) = {A,B,C} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl <;> assumption
    · rw [hycard]
      simp [hAB,hAC,hBC]
  have hcommon (e : Nat × Bool)
      (hex : e ∈ exitArcs n D (carrierT n D {x}))
      (hey : e ∈ exitArcs n D (carrierT n D {y})) : e = A := by
    rw [hWy] at hey
    simp only [Finset.mem_insert, Finset.mem_singleton] at hey
    rcases hey with heA | heB | heC
    · exact heA
    · subst e
      exact False.elim (h3_no_opposite_exit hS hex hBx)
    · subst e
      exact False.elim (h3_no_opposite_exit hS hex hCx)
  exact hPQ ((hcommon P hPx hPy).trans (hcommon Q hQx hQy).symm)

lemma h3_pair26_exit_pattern {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hc : ∀ x : Fin 10, x ≠ 0 → x ≠ 2 → x ≠ 6 → (exitArcs 10 D (carrierT 10 D {x})).card = 2)
    (hc2 : (exitArcs 10 D (carrierT 10 D {(2 : Fin 10)})).card = 3)
    (hc6 : (exitArcs 10 D (carrierT 10 D {(6 : Fin 10)})).card = 3)
    (P Q : Nat × Bool) (hPQ : P ≠ Q)
    (hP2 : P ∈ exitArcs 10 D (carrierT 10 D {(2 : Fin 10)}))
    (hP6 : P ∈ exitArcs 10 D (carrierT 10 D {(6 : Fin 10)}))
    (hQ2 : Q ∈ exitArcs 10 D (carrierT 10 D {(2 : Fin 10)}))
    (hQ6 : Q ∈ exitArcs 10 D (carrierT 10 D {(6 : Fin 10)})) :
    ∃ e0 e1 e4 e5 d q : ℕ × Bool,
      supp 10 D (src D e0) = {0} ∧ supp 10 D (src D e1) = {1} ∧
      supp 10 D (src D e4) = {4} ∧ supp 10 D (src D e5) = {5} ∧
      exitArcs 10 D (carrierT 10 D {0}) = {e0} ∧
      exitArcs 10 D (carrierT 10 D {1}) = {h3_opp e0, e1} ∧
      exitArcs 10 D (carrierT 10 D {2}) = {h3_opp e1, h3_opp d, q} ∧
      exitArcs 10 D (carrierT 10 D {3}) = {h3_opp e4, d} ∧
      exitArcs 10 D (carrierT 10 D {4}) = {h3_opp e0, e4} ∧
      exitArcs 10 D (carrierT 10 D {5}) = {h3_opp e0, e5} ∧
      exitArcs 10 D (carrierT 10 D {6}) = {h3_opp e1, d, q} ∧
      exitArcs 10 D (carrierT 10 D {7}) = {h3_opp e5, d} ∧
      exitArcs 10 D (carrierT 10 D {8}) = {h3_opp e5, h3_opp d} ∧
      exitArcs 10 D (carrierT 10 D {9}) = {h3_opp e4, h3_opp d} ∧
      q ≠ h3_opp e1 ∧ q ≠ h3_opp d ∧ q ≠ d := by
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
  obtain ⟨e1, _, hW1⟩ := h3_pair_of_card_two (hAmem 1 (by decide)) (hc 1 (by decide) (by decide) (by decide))
  obtain ⟨e4, _, hW4⟩ := h3_pair_of_card_two (hAmem 4 (by decide)) (hc 4 (by decide) (by decide) (by decide))
  obtain ⟨e5, _, hW5⟩ := h3_pair_of_card_two (hAmem 5 (by decide)) (hc 5 (by decide) (by decide) (by decide))
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
  obtain ⟨g3, _, hW3⟩ := h3_pair_of_card_two ha3 (hc 3 (by decide) (by decide) (by decide))
  obtain ⟨g7, _, hW7⟩ := h3_pair_of_card_two ha7 (hc 7 (by decide) (by decide) (by decide))
  obtain ⟨g8, _, hW8⟩ := h3_pair_of_card_two ha8 (hc 8 (by decide) (by decide) (by decide))
  obtain ⟨g9, _, hW9⟩ := h3_pair_of_card_two ha9 (hc 9 (by decide) (by decide) (by decide))
  have hb1 : supp 10 D (src D (h3_opp (h3_opp e1))) = {(1 : Fin 10)} := by rw [h3_opp_opp]; exact hp1
  have hb4 : supp 10 D (src D (h3_opp (h3_opp e4))) = {(4 : Fin 10)} := by rw [h3_opp_opp]; exact hp4
  have hb5 : supp 10 D (src D (h3_opp (h3_opp e5))) = {(5 : Fin 10)} := by rw [h3_opp_opp]; exact hp5
  have h38 : h3_opp g3 = g8 := h3_split_edge_pair petersen_graph_ok h.1 hC
    (by rw [hW3]) (by rw [hW8]) hb4 hb5 (by decide) (by decide) (by unfold petersenAdj; decide)
  have h79 : h3_opp g7 = g9 := h3_split_edge_pair petersen_graph_ok h.1 hC
    (by rw [hW7]) (by rw [hW9]) hb5 hb4 (by decide) (by decide) (by unfold petersenAdj; decide)
  have hd2 : h3_opp g3 ∈ exitArcs 10 D (carrierT 10 D {(2 : Fin 10)}) :=
    sem_two_exit_remaining_slot petersen_graph_ok h.1 hC (by rw [hW3]) hb4
      (by unfold petersenAdj; decide) (by decide)
  have hd6a : g3 ∈ exitArcs 10 D (carrierT 10 D {(6 : Fin 10)}) := by
    have hh := sem_two_exit_remaining_slot petersen_graph_ok h.1 hC (by rw [hW8]) hb5
      (by unfold petersenAdj; decide : petersenAdj 8 6) (by decide : (6 : Fin 10) ≠ 5)
    simpa [← h38, h3_opp] using hh
  have hd2b : h3_opp g7 ∈ exitArcs 10 D (carrierT 10 D {(2 : Fin 10)}) :=
    sem_two_exit_remaining_slot petersen_graph_ok h.1 hC (by rw [hW7]) hb5
      (by unfold petersenAdj; decide) (by decide)
  have hd6b : g7 ∈ exitArcs 10 D (carrierT 10 D {(6 : Fin 10)}) := by
    have hh := sem_two_exit_remaining_slot petersen_graph_ok h.1 hC (by rw [hW9]) hb4
      (by unfold petersenAdj; decide : petersenAdj 9 6) (by decide : (6 : Fin 10) ≠ 4)
    simpa [← h79, h3_opp] using hh
  have hAd3 : h3_opp e1 ≠ g3 := by
    intro he
    exact h3_no_opposite_exit h.1 (he ▸ ha2) hd2
  have hAd7 : h3_opp e1 ≠ g7 := by
    intro he
    exact h3_no_opposite_exit h.1 (he ▸ ha2) hd2b
  have hd37 : g3 = g7 := h3_common_terminals_force_pair h.1 hc6 ha6 hd6a hd6b
    hAd3 hAd7 hd2 hd2b hP2 hP6 hQ2 hQ6 hPQ
  have hg9 : g9 = h3_opp g3 := by rw [← h79, ← hd37]

  have hg3mem : g3 ∈ exitArcs 10 D (carrierT 10 D {(3 : Fin 10)}) := by rw [hW3]; simp
  have h3in : (3 : Fin 10) ∈ supp 10 D (src D g3) := (sem_mem_exit1.mp hg3mem).2.1
  have hneq : h3_opp e1 ≠ h3_opp g3 := by
    intro he
    have he' : e1 = g3 := by
      have ht := congrArg h3_opp he
      simpa only [h3_opp_opp] using ht
    rw [← he', hp1] at h3in
    simp at h3in
  have hcardErase : ((exitArcs 10 D (carrierT 10 D {(2 : Fin 10)})).erase (h3_opp e1)).card = 2 := by
    rw [Finset.card_erase_of_mem ha2, hc2]
  have hdErase : h3_opp g3 ∈ (exitArcs 10 D (carrierT 10 D {(2 : Fin 10)})).erase (h3_opp e1) :=
    Finset.mem_erase.mpr ⟨Ne.symm hneq, hd2⟩
  obtain ⟨q, hqd, hrest⟩ := h3_pair_of_card_two hdErase hcardErase
  have hqErase : q ∈ (exitArcs 10 D (carrierT 10 D {(2 : Fin 10)})).erase (h3_opp e1) := by
    rw [hrest]; simp
  have hq1 := (Finset.mem_erase.mp hqErase).1
  have hW2 : exitArcs 10 D (carrierT 10 D {(2 : Fin 10)}) = {h3_opp e1, h3_opp g3, q} := by
    rw [← Finset.insert_erase ha2, hrest]
  have hd6 : g3 ∈ exitArcs 10 D (carrierT 10 D {(6 : Fin 10)}) := hd6a
  have hcardErase6 : ((exitArcs 10 D (carrierT 10 D {(6 : Fin 10)})).erase (h3_opp e1)).card = 2 := by
    rw [Finset.card_erase_of_mem ha6, hc6]
  have hdErase6 : g3 ∈ (exitArcs 10 D (carrierT 10 D {(6 : Fin 10)})).erase (h3_opp e1) :=
    Finset.mem_erase.mpr ⟨Ne.symm hAd3, hd6⟩
  obtain ⟨q6, hq6d, hrest6⟩ := h3_pair_of_card_two hdErase6 hcardErase6
  have hW6 : exitArcs 10 D (carrierT 10 D {(6 : Fin 10)}) = {h3_opp e1, g3, q6} := by
    rw [← Finset.insert_erase ha6, hrest6]
  have hcommon (e : Nat × Bool) (heA : e ≠ h3_opp e1)
      (he2 : e ∈ exitArcs 10 D (carrierT 10 D {(2 : Fin 10)}))
      (he6 : e ∈ exitArcs 10 D (carrierT 10 D {(6 : Fin 10)})) : e = q ∧ e = q6 := by
    have heD : e ≠ g3 := by
      intro hh
      exact h3_no_opposite_exit h.1 (hh ▸ he2) hd2
    have heBarD : e ≠ h3_opp g3 := by
      intro hh
      exact h3_no_opposite_exit h.1 hd6 (hh ▸ he6)
    rw [hW2] at he2
    rw [hW6] at he6
    simp only [Finset.mem_insert, Finset.mem_singleton] at he2 he6
    exact ⟨he2.resolve_left heA |>.resolve_left heBarD,
      he6.resolve_left heA |>.resolve_left heD⟩
  have hqq6 : q = q6 := by
    by_cases hPA : P = h3_opp e1
    · have hQA : Q ≠ h3_opp e1 := fun hh => hPQ (hPA.trans hh.symm)
      exact (hcommon Q hQA hQ2 hQ6).1.symm.trans (hcommon Q hQA hQ2 hQ6).2
    · exact (hcommon P hPA hP2 hP6).1.symm.trans (hcommon P hPA hP2 hP6).2
  refine ⟨e0, e1, e4, e5, g3, q, hp0, hp1, hp4, hp5, hW0, hW1, hW2,
    hW3, hW4, hW5, ?_, ?_, ?_, ?_, hq1, hqd, ?_⟩
  · simpa only [hqq6] using hW6
  · simpa only [← hd37] using hW7
  · simpa only [← h38] using hW8
  · simpa only [hg9] using hW9
  · exact hqq6 ▸ hq6d


lemma h3_saturated_pair26_exit_pattern {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hone : Bplus 10 D = (eligSet 10 D).card + 1)
    (hSat : h3_saturatedSet 10 D = {2,6}) :
    ∃ e0 e1 e4 e5 d q : ℕ × Bool,
      supp 10 D (src D e0) = {0} ∧ supp 10 D (src D e1) = {1} ∧
      supp 10 D (src D e4) = {4} ∧ supp 10 D (src D e5) = {5} ∧
      exitArcs 10 D (carrierT 10 D {0}) = {e0} ∧
      exitArcs 10 D (carrierT 10 D {1}) = {h3_opp e0, e1} ∧
      exitArcs 10 D (carrierT 10 D {2}) = {h3_opp e1, h3_opp d, q} ∧
      exitArcs 10 D (carrierT 10 D {3}) = {h3_opp e4, d} ∧
      exitArcs 10 D (carrierT 10 D {4}) = {h3_opp e0, e4} ∧
      exitArcs 10 D (carrierT 10 D {5}) = {h3_opp e0, e5} ∧
      exitArcs 10 D (carrierT 10 D {6}) = {h3_opp e1, d, q} ∧
      exitArcs 10 D (carrierT 10 D {7}) = {h3_opp e5, d} ∧
      exitArcs 10 D (carrierT 10 D {8}) = {h3_opp e5, h3_opp d} ∧
      exitArcs 10 D (carrierT 10 D {9}) = {h3_opp e4, h3_opp d} ∧
      q ≠ h3_opp e1 ∧ q ≠ h3_opp d ∧ q ≠ d := by
  have hfin : ∀ x ∈ ({1,4,5} : Finset (Fin 10)), x ∉ ({2,6} : Finset (Fin 10)) := by decide
  have hlo := h3_outside_le_two_nonzero_ge_two h hC hz
    (fun x hx => h3_outside_saturated_le_two hSat (hfin x hx))
  have hc (x : Fin 10) (hx0 : x ≠ 0) (hx2 : x ≠ 2) (hx6 : x ≠ 6) :
      (exitArcs 10 D (carrierT 10 D {x})).card = 2 :=
    Nat.le_antisymm (h3_outside_saturated_le_two hSat (by simp [hx2,hx6])) (hlo x hx0)
  have hm2 : (2 : Fin 10) ∈ h3_saturatedSet 10 D := by rw [hSat]; simp
  have hm6 : (6 : Fin 10) ∈ h3_saturatedSet 10 D := by rw [hSat]; simp
  have hc2 := (h3_one_residual_saturation petersen_graph_ok h hC hone 2 hm2).1
  have hc6 := (h3_one_residual_saturation petersen_graph_ok h hC hone 6 hm6).1
  obtain ⟨P,Q,hPQ,hcommon⟩ := h3_one_residual_common_terminals petersen_graph_ok h hC hone
  exact h3_pair26_exit_pattern h hC hz hc hc2 hc6 P Q
    (fun he => hPQ (congrArg Prod.fst he))
    (hcommon 2 hm2).1 (hcommon 6 hm6).1 (hcommon 2 hm2).2 (hcommon 6 hm6).2


end DagTools

namespace Pair26Geometry

def side (i : Fin 11) : Finset (Fin 10) :=
  SideGeometry.mask (([1, 50, 2, 68, 16, 520, 32, 384, 200, 772, 68] : List Nat).getD i.val 0)

def allowed (i : Fin 11) : Finset (Fin 10) :=
  SideGeometry.mask (([1, 1023, 3, 1023, 17, 520, 33, 384, 200, 772, 1023] : List Nat).getD i.val 0)

def witnessCode (i : Fin 11) (y : Fin 10) : Nat :=
  ([0, 2, 20, 10, 16, 32, 80, 130, 258, 514, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1044, 1128, 1044, 1060, 1104, 1232, 1300, 1572, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4106, 4644, 4106, 0, 4136, 4200, 4234, 4866, 4610, 3141, 3218, 3140, 0, 3152, 3172, 3140, 3216, 3456, 0, 0, 5250, 5396, 5258, 5264, 0, 5328, 5250, 5378, 5890, 7237, 7210, 7236, 7208, 7252, 7208, 7236, 0, 0, 7688, 3589, 3842, 3588, 0, 6420, 3620, 0, 0, 3840, 3588, 2121, 8330, 0, 2120, 2256, 2152, 2120, 2240, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List Nat).getD (i.val * 10 + y.val) 0

def witnessVertex (i : Fin 11) (y : Fin 10) : Fin 10 :=
  ⟨witnessCode i y / 1024 % 10, Nat.mod_lt _ (by decide)⟩

def witnessSet (i : Fin 11) (y : Fin 10) : Finset (Fin 10) :=
  SideGeometry.mask (witnessCode i y % 1024)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma witness_valid : ∀ i : Fin 11, ∀ y : Fin 10, y ∉ allowed i →
    let x := witnessVertex i y
    let A := witnessSet i y
    x ∈ side i ∧ y ∈ A ∧
    (∀ u ∈ A, ∀ v ∈ A, ¬ SideGeometry.adj u v) ∧
    (∃ v ∈ A, SideGeometry.adj x v) ∧
    ∀ j : Fin 11, x ∈ side j → j ≠ i → (side j ∩ A).Nonempty := by
  unfold SideGeometry.adj
  decide +kernel

lemma support_bound (S : Fin 11 → Finset (Fin 10))
    (hsub : ∀ i, side i ⊆ S i)
    (hex : ∀ x A, (∀ u ∈ A, ∀ v ∈ A, ¬ SideGeometry.adj u v) →
      (∃ v ∈ A, SideGeometry.adj x v) →
      ∃ i : Fin 11, x ∈ side i ∧ Disjoint (S i) A) :
    ∀ i, S i ⊆ allowed i := by
  intro i y hy
  by_contra hn
  obtain ⟨hx, hyA, hA, hnb, hother⟩ := witness_valid i y hn
  obtain ⟨j, hj, hd⟩ := hex _ _ hA hnb
  by_cases he : j = i
  · subst j
    exact Finset.disjoint_left.mp hd hy hyA
  · obtain ⟨v, hv⟩ := hother j hj he
    obtain ⟨hv, hvA⟩ := Finset.mem_inter.mp hv
    exact Finset.disjoint_left.mp hd (hsub j hv) hvA

end Pair26Geometry

namespace DagTools

lemma h3_pair26_source_bounds {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (r : Fin 11 → Nat × Bool)
    (hW : ∀ x : Fin 10, sem_W 10 D x =
      (Finset.univ.filter (fun i : Fin 11 => x ∈ Pair26Geometry.side i)).image r) :
    ∀ i, supp 10 D (src D (r i)) ⊆ Pair26Geometry.allowed i := by
  apply Pair26Geometry.support_bound
  · intro i x hx
    apply (sem_mem_W.mp ?_).2.1
    rw [hW]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hx⟩, rfl⟩
  · intro x A hA hnb
    obtain ⟨j, s, hj, _, hxs, hxn, hd⟩ :=
      sem_exposure petersen_graph_ok h.1 hC A hA x hnb
    have hm : (j, s) ∈ sem_W 10 D x := sem_mem_W.mpr ⟨hj, hxs, hxn⟩
    rw [hW] at hm
    obtain ⟨i, hi, hri⟩ := Finset.mem_image.mp hm
    exact ⟨i, (Finset.mem_filter.mp hi).2, by simpa only [hri] using hd⟩

end DagTools

namespace DagTools

def h3_pair26_sideMap (e0 e1 e4 e5 d q : ℕ × Bool) (i : Fin 11) : ℕ × Bool :=
  ([e0,h3_opp e0,e1,h3_opp e1,e4,h3_opp e4,e5,h3_opp e5,d,h3_opp d,q] :
    List (ℕ × Bool)).getD i.val e0

def h3_pair26_incidenceIndices (x : Fin 10) : Finset (Fin 11) :=
  match x.val with
  | 0 => {0}
  | 1 => {1,2}
  | 2 => {3,9,10}
  | 3 => {5,8}
  | 4 => {1,4}
  | 5 => {1,6}
  | 6 => {3,8,10}
  | 7 => {7,8}
  | 8 => {7,9}
  | _ => {5,9}

set_option maxRecDepth 100000 in
lemma h3_pair26_incidence_indices : ∀ x : Fin 10,
    Finset.univ.filter (fun i : Fin 11 => x ∈ Pair26Geometry.side i) = h3_pair26_incidenceIndices x := by
  decide +kernel

lemma h3_saturated_pair26_sources_exist {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hB0 : Bzero 10 D = 0)
    (hone : Bplus 10 D = (eligSet 10 D).card + 1)
    (hSat : h3_saturatedSet 10 D = {2,6}) :
    ∃ r : Fin 10 → ℕ × Bool, ∃ q : ℕ × Bool,
      Function.Injective r ∧
      (∀ i, r (SideGeometry.opposite i) = ((r i).1, !(r i).2)) ∧
      (∀ i, supp 10 D (src D (r i)) = SideGeometry.side i) ∧
      (∀ x : Fin 10, exitArcs 10 D (carrierT 10 D {x}) =
        (Finset.univ.filter (fun i : Fin 10 => x ∈ SideGeometry.side i)).image r ∪
          if x ∈ ({2,6} : Finset (Fin 10)) then {q} else ∅) ∧
      (∀ i, (r i).1 < D.length ∧ tag D (r i).1 = true ∧ supp 10 D (10+(r i).1) = ∅) ∧
      q ≠ r 3 ∧ q ≠ r 9 ∧ q ≠ r 8 := by
  obtain ⟨e0,e1,e4,e5,d,q,hp0,hp1,hp4,hp5,hW0,hW1,hW2,hW3,hW4,hW5,
    hW6,hW7,hW8,hW9,hq1,hqd,hqd2⟩ := h3_saturated_pair26_exit_pattern h hC hz hone hSat
  let r := h3_sideMap e0 e1 e4 e5 d
  let R := h3_pair26_sideMap e0 e1 e4 e5 d q
  have hW11 : ∀ x : Fin 10, exitArcs 10 D (carrierT 10 D {x}) =
      (Finset.univ.filter (fun i : Fin 11 => x ∈ Pair26Geometry.side i)).image R := by
    intro x
    rw [h3_pair26_incidence_indices]
    fin_cases x
    · simpa [R,h3_pair26_sideMap,h3_pair26_incidenceIndices] using hW0
    · simpa [R,h3_pair26_sideMap,h3_pair26_incidenceIndices] using hW1
    · simpa [R,h3_pair26_sideMap,h3_pair26_incidenceIndices] using hW2
    · simpa [R,h3_pair26_sideMap,h3_pair26_incidenceIndices] using hW3
    · simpa [R,h3_pair26_sideMap,h3_pair26_incidenceIndices] using hW4
    · simpa [R,h3_pair26_sideMap,h3_pair26_incidenceIndices] using hW5
    · simpa [R,h3_pair26_sideMap,h3_pair26_incidenceIndices] using hW6
    · simpa [R,h3_pair26_sideMap,h3_pair26_incidenceIndices] using hW7
    · simpa [R,h3_pair26_sideMap,h3_pair26_incidenceIndices] using hW8
    · simpa [R,h3_pair26_sideMap,h3_pair26_incidenceIndices] using hW9
  have hb := h3_pair26_source_bounds h hC R hW11
  have hlo : ∀ i : Fin 11, Pair26Geometry.side i ⊆ supp 10 D (src D (R i)) := by
    intro i x hx
    apply (sem_mem_exit1.mp ?_).2.1
    rw [hW11]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i,hx⟩,rfl⟩
  have hfirst : ∀ i : Fin 10, R ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩ = r i := by
    intro i; fin_cases i <;> rfl
  have hside : ∀ i : Fin 10,
      Pair26Geometry.side ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩ = SideGeometry.side i := by
    decide +kernel
  have hfromBounds : ∀ i : Fin 10,
      Pair26Geometry.allowed ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩ = SideGeometry.side i →
      supp 10 D (src D (r i)) = SideGeometry.side i := by
    intro i hi
    have hu := hb ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩
    have hl := hlo ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩
    rw [hfirst i, hi] at hu
    rw [hfirst i,hside i] at hl
    exact Finset.Subset.antisymm hu hl
  have hAN : ({1,4,5} : Finset (Fin 10)) ⊆ supp 10 D (src D (h3_opp e0)) := by
    have hh := hlo (1 : Fin 11)
    have he : Pair26Geometry.side 1 = ({1,4,5} : Finset (Fin 10)) := by decide +kernel
    simpa [he, R, h3_pair26_sideMap] using hh
  have hstar := h3_star0_exact_of_two_exit_pure_companion h hC hz hB0
    (h3_opp e0) e4 hW4 hp4 hAN
  have hpartial : ∀ i : Fin 10, i ≠ 3 → supp 10 D (src D (r i)) = SideGeometry.side i := by
    intro i hi
    fin_cases i
    · exact hp0.trans (by decide)
    · exact hstar.trans (by decide)
    · exact hp1.trans (by decide)
    · exact False.elim (hi rfl)
    · exact hp4.trans (by decide)
    · exact hfromBounds 5 (by decide)
    · exact hp5.trans (by decide)
    · exact hfromBounds 7 (by decide)
    · exact hfromBounds 8 (by decide)
    · exact hfromBounds 9 (by decide)
  have hme1 : e1 ∈ exitArcs 10 D (carrierT 10 D {(1 : Fin 10)}) := by rw [hW1]; simp
  have hj1 := (sem_mem_exit1.mp hme1).1
  have ht1 := h3_exit_tag_and h.1 hme1
  have hout1 : supp 10 D (10+e1.1) = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨x,hx⟩
    have hs := sem_supp_and_sub h.1 hj1 ht1 e1.2 hx
    change x ∈ supp 10 D (src D e1) at hs
    rw [hp1,Finset.mem_singleton] at hs
    exact (sem_mem_exit1.mp hme1).2.2 (hs ▸ hx)
  have hKlow : ({2,6} : Finset (Fin 10)) ⊆ supp 10 D (src D (r 3)) := by
    have hh := hlo (3 : Fin 11)
    have he : Pair26Geometry.side 3 = ({2,6} : Finset (Fin 10)) := by decide +kernel
    simpa [he,R,h3_pair26_sideMap,r,h3_sideMap] using hh
  have hKexact : supp 10 D (src D (r 3)) = ({2,6} : Finset (Fin 10)) := by
    apply Finset.Subset.antisymm ?_ hKlow
    intro x hx
    by_contra hxN
    have hm : r 3 ∈ exitArcs 10 D (carrierT 10 D {x}) := by
      apply sem_mem_exit1.mpr
      refine ⟨hj1,hx,?_⟩
      change x ∉ supp 10 D (10+e1.1)
      rw [hout1]
      exact Finset.notMem_empty x
    rw [hW11] at hm
    obtain ⟨j,hj,hje⟩ := Finset.mem_image.mp hm
    have hxj := (Finset.mem_filter.mp hj).2
    have hj10 : j.val < 10 := by
      by_contra hn
      have je : j = 10 := Fin.ext (by omega)
      subst j
      have he : Pair26Geometry.side 10 = ({2,6} : Finset (Fin 10)) := by decide +kernel
      exact hxN (he ▸ hxj)
    let k : Fin 10 := ⟨j.val,hj10⟩
    have hjk : j = ⟨k.val,Nat.lt_trans k.isLt (by decide)⟩ := Fin.ext rfl
    have hkr : r k = r 3 := by rw [hjk,hfirst k] at hje; exact hje
    have hk3 : k ≠ 3 := by
      intro he
      have heSide : Pair26Geometry.side 3 = ({2,6} : Finset (Fin 10)) := by decide +kernel
      have hh : j = 3 := Fin.ext (congrArg (fun a : Fin 10 => a.val) he)
      exact hxN (by simpa only [hh,heSide] using hxj)
    have hforbid : ∀ i : Fin 10, i ≠ 3 → ¬ ({2,6} : Finset (Fin 10)) ⊆ SideGeometry.side i := by
      decide +kernel
    apply hforbid k hk3
    rw [← hpartial k hk3,hkr]
    exact hKlow
  have hsources : ∀ i : Fin 10, supp 10 D (src D (r i)) = SideGeometry.side i := by
    intro i
    by_cases hi : i = 3
    · subst i
      exact hKexact.trans (by decide +kernel)
    · exact hpartial i hi
  have hSideInj : Function.Injective SideGeometry.side := by decide +kernel
  have hinj : Function.Injective r := by
    intro i j hij
    apply hSideInj
    rw [← hsources i, ← hsources j, hij]
  have hopp : ∀ i : Fin 10, r (SideGeometry.opposite i) = ((r i).1, !(r i).2) :=
    h3_sideMap_opposite e0 e1 e4 e5 d
  have hW : ∀ x : Fin 10, exitArcs 10 D (carrierT 10 D {x}) =
      (Finset.univ.filter (fun i : Fin 10 => x ∈ SideGeometry.side i)).image r ∪
        if x ∈ ({2,6} : Finset (Fin 10)) then {q} else ∅ := by
    intro x
    rw [SideGeometry.incidence_indices]
    fin_cases x
    · simpa [r,h3_sideMap,SideGeometry.incidenceIndices] using hW0
    · simpa [r,h3_sideMap,SideGeometry.incidenceIndices] using hW1
    · simpa [r,h3_sideMap,SideGeometry.incidenceIndices,Finset.insert_comm] using hW2
    · simpa [r,h3_sideMap,SideGeometry.incidenceIndices] using hW3
    · simpa [r,h3_sideMap,SideGeometry.incidenceIndices] using hW4
    · simpa [r,h3_sideMap,SideGeometry.incidenceIndices] using hW5
    · simpa [r,h3_sideMap,SideGeometry.incidenceIndices] using hW6
    · simpa [r,h3_sideMap,SideGeometry.incidenceIndices] using hW7
    · simpa [r,h3_sideMap,SideGeometry.incidenceIndices] using hW8
    · simpa [r,h3_sideMap,SideGeometry.incidenceIndices] using hW9
  have hvalid : ∀ i : Fin 10, (r i).1 < D.length ∧ tag D (r i).1 = true ∧
      supp 10 D (10+(r i).1) = ∅ := by
    intro i
    obtain ⟨x,hx⟩ := SideGeometry.side_nonempty i
    have hm : r i ∈ exitArcs 10 D (carrierT 10 D {x}) := by
      rw [hW]
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hx⟩,rfl⟩
    have hj := (sem_mem_exit1.mp hm).1
    have ht := h3_exit_tag_and h.1 hm
    refine ⟨hj,ht,?_⟩
    have hd : Disjoint (supp 10 D (src D (r i)))
        (supp 10 D (src D ((r i).1, !(r i).2))) := by
      rw [← hopp i, hsources i, hsources (SideGeometry.opposite i)]
      exact SideGeometry.paired_disjoint i
    rw [sem_supp_and h.1 hj ht]
    apply Finset.disjoint_iff_inter_eq_empty.mp
    rcases he : r i with ⟨j,s⟩
    cases s <;> simpa only [he, Bool.not_false, Bool.not_true, sb_src_false, sb_src_true,
      disjoint_comm] using hd
  refine ⟨r,q,hinj,hopp,hsources,hW,hvalid,?_,?_,?_⟩
  · simpa [r,h3_sideMap] using hq1
  · simpa [r,h3_sideMap] using hqd
  · simpa [r,h3_sideMap] using hqd2


end DagTools

namespace DagTools

lemma h3_nonindexed_and_shared_extra_type {n : Nat} {D : Dag} (hS : Strict n D)
    {ι : Type*} (r : ι → Nat × Bool) (X : Finset (Fin n)) (q : Nat × Bool)
    (hcover : ∀ x : Fin n, ∀ e ∈ exitArcs n D (carrierT n D {x}),
      (∃ i, r i = e) ∨ (x ∈ X ∧ e = q))
    (hq : ∀ x ∈ X, q ∈ exitArcs n D (carrierT n D {x}))
    {j : Nat} (hj : j < D.length) (ht : tag D j = true)
    (hne : ∀ i, (r i).1 ≠ j) :
    supp n D (opA D j) = supp n D (opB D j) ∨
    ((supp n D (opA D j)).Nonempty ∧ supp n D (opA D j) ⊆ supp n D (opB D j)) ∨
    ((supp n D (opB D j)).Nonempty ∧ supp n D (opB D j) ⊆ supp n D (opA D j)) ∨
    (supp n D (opA D j) = ∅ ∧ supp n D (opB D j) = X) ∨
    (supp n D (opB D j) = ∅ ∧ supp n D (opA D j) = X) := by
  have hdiff (s : Bool) {x : Fin n}
      (hx : x ∈ supp n D (src D (j,s)))
      (hn : x ∉ supp n D (src D (j,!s))) : x ∈ X ∧ (j,s) = q := by
    have hm : (j,s) ∈ exitArcs n D (carrierT n D {x}) := by
      apply sem_mem_exit1.mpr
      exact ⟨hj,hx,fun hh => hn (sem_supp_and_sub hS hj ht (!s) hh)⟩
    rcases hcover x (j,s) hm with ⟨i,hi⟩ | he
    · exact False.elim (hne i (congrArg Prod.fst hi))
    · exact he
  have hlow (s : Bool) (he : (j,s) = q) : X ⊆ supp n D (src D (j,s)) := by
    intro x hx
    have hh := (sem_mem_exit1.mp (hq x hx)).2.1
    simpa only [← he] using hh
  by_cases hab : supp n D (opA D j) ⊆ supp n D (opB D j)
  · by_cases hba : supp n D (opB D j) ⊆ supp n D (opA D j)
    · exact Or.inl (Finset.Subset.antisymm hab hba)
    · obtain ⟨x,hxb,hxa⟩ := Finset.not_subset.mp hba
      have hqe := (hdiff true hxb hxa).2
      by_cases hneA : (supp n D (opA D j)).Nonempty
      · exact Or.inr (Or.inl ⟨hneA,hab⟩)
      · have ha0 : supp n D (opA D j) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hneA
        have hbX : supp n D (opB D j) = X := by
          apply Finset.Subset.antisymm ?_ (hlow true hqe)
          intro y hy
          exact (hdiff true hy (by change y ∉ supp n D (opA D j); rw [ha0]; simp)).1
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ha0,hbX⟩)))
  · obtain ⟨x,hxa,hxb⟩ := Finset.not_subset.mp hab
    have hqe := (hdiff false hxa hxb).2
    have hba : supp n D (opB D j) ⊆ supp n D (opA D j) := by
      intro y hy
      by_contra hn
      have hqe' := (hdiff true hy hn).2
      have hh := congrArg Prod.snd (hqe.trans hqe'.symm)
      simp at hh
    by_cases hneB : (supp n D (opB D j)).Nonempty
    · exact Or.inr (Or.inr (Or.inl ⟨hneB,hba⟩))
    · have hb0 : supp n D (opB D j) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hneB
      have haX : supp n D (opA D j) = X := by
        apply Finset.Subset.antisymm ?_ (hlow false hqe)
        intro y hy
        exact (hdiff false hy (by change y ∉ supp n D (opB D j); rw [hb0]; simp)).1
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hb0,haX⟩)))


end DagTools

namespace DagTools

open R1FlexibleResource.CausalBarrier R1FlexibleResource.ResourceExclusion
  R1FlexibleResource.DAGBridge

lemma h3_residual_saturated_pair26_exclusion {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hB0 : Bzero 10 D = 0) (hone : Bplus 10 D = (eligSet 10 D).card + 1)
    (hSat : h3_saturatedSet 10 D = {2,6}) : False := by
  obtain ⟨r,q,_,hopp,hsrc,hW,hvalid,_⟩ := h3_saturated_pair26_sources_exist h hC hz hB0 hone hSat
  have hp : r 9 = ((r 8).1, !(r 8).2) := by
    simpa [SideGeometry.opposite] using hopp 8
  have hdirty : DirtySides D (r 8).1 := by
    have h8 := hsrc 8
    have h9 := hsrc 9
    have h8S : SideGeometry.side 8 = DirtyA := by decide +kernel
    have h9S : SideGeometry.side 9 = DirtyB := by decide +kernel
    rw [h8S] at h8
    rw [h9S] at h9
    cases hb : (r 8).2
    · left
      exact ⟨by simpa [src, hb] using h8, by simpa [hp, src, hb] using h9⟩
    · right
      exact ⟨by simpa [hp, src, hb] using h9, by simpa [src, hb] using h8⟩
  have hcover : ∀ x : Fin 10, ∀ e ∈ exitArcs 10 D (carrierT 10 D {x}),
      (∃ i, r i = e) ∨ (x ∈ ({2,6} : Finset (Fin 10)) ∧ e = q) := by
    intro x e he
    rw [hW] at he
    rcases Finset.mem_union.mp he with he | he
    · obtain ⟨i,_,hi⟩ := Finset.mem_image.mp he
      exact Or.inl ⟨i,hi⟩
    · right
      by_cases hx : x ∈ ({2,6} : Finset (Fin 10))
      · rw [ite_eq_left hx,Finset.mem_singleton] at he
        exact ⟨hx,he⟩
      · simp only [ite_eq_right hx,Finset.notMem_empty] at he
  have hq : ∀ x ∈ ({2,6} : Finset (Fin 10)), q ∈ exitArcs 10 D (carrierT 10 D {x}) := by
    intro x hx
    rw [hW]
    apply Finset.mem_union_right
    rw [ite_eq_left hx]
    exact Finset.mem_singleton_self q
  have hother : OtherAndSides D (r 8).1 := by
    intro j hj hjd ht
    by_cases hex : ∃ i, (r i).1 = j
    · obtain ⟨i, hi⟩ := hex
      have he : ∃ k, r k = (j, false) := by
        cases hb : (r i).2
        · exact ⟨i, Prod.ext hi hb⟩
        · refine ⟨SideGeometry.opposite i, ?_⟩
          rw [hopp, hi, hb]
          rfl
      obtain ⟨k, hk⟩ := he
      have hka : supp 10 D (opA D j) = SideGeometry.side k := by
        simpa [hk, src] using hsrc k
      have hkb : supp 10 D (opB D j) = SideGeometry.side (SideGeometry.opposite k) := by
        simpa [hopp, hk, src] using hsrc (SideGeometry.opposite k)
      have hk8 : k ≠ 8 := by
        intro he
        subst k
        exact hjd (congrArg Prod.fst hk).symm
      have hk9 : k ≠ 9 := by
        intro he
        subst k
        have heq := congrArg Prod.fst hk
        rw [hp] at heq
        exact hjd heq.symm
      apply Or.inl
      apply Or.inl
      apply Or.inr
      change (supp 10 D (opA D j), supp 10 D (opB D j)) ∈ OtherSides ∨
        (supp 10 D (opB D j), supp 10 D (opA D j)) ∈ OtherSides
      rw [hka, hkb]
      exact h3_all_two_flexible_other_sides k hk8 hk9
    · rcases h3_nonindexed_and_shared_extra_type h.1 r {2,6} q hcover hq hj ht
        (fun i hi => hex ⟨i,hi⟩) with he | ha | hb | ⟨ha0,hbX⟩ | ⟨hb0,haX⟩
      · exact Or.inl (Or.inl (Or.inl he))
      · exact Or.inl (Or.inr (Or.inl ha))
      · exact Or.inl (Or.inr (Or.inr hb))
      · apply Or.inl
        apply Or.inl
        apply Or.inr
        right
        change (supp 10 D (opB D j), supp 10 D (opA D j)) ∈ OtherSides
        simp [OtherSides,ha0,hbX]
      · apply Or.inl
        apply Or.inl
        apply Or.inr
        left
        change (supp 10 D (opA D j), supp 10 D (opB D j)) ∈ OtherSides
        simp [OtherSides,hb0,haX]
  exact h3_r1_flexible_allowed_sides_exclusion h.1 hC hB0
    (hvalid 8).1 (hvalid 8).2.1 hdirty hother


end DagTools

namespace DagTools

lemma h3_tight_bzero_positive {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hB : Bplus 10 D = (eligSet 10 D).card) : 1 ≤ Bzero 10 D := by
  by_contra hn
  have hB0 : Bzero 10 D = 0 := by omega
  exact h3_all_le_two_bzero_exclusion h hC hz
    (sem_tight_exit_le_two petersen_graph_ok h hC hB) hB0

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

-- proof/r1_split_resource_fragment.lean
namespace R1SplitResource.CausalBarrier

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
  [({0}, {1, 4, 5}), ({1}, {2, 6}), ({4}, {3, 9}), ({5}, {7, 8}), (∅, ∅),
   ({1}, {2}), ({1}, {6}), ({1}, ∅), ({2}, ∅), ({2, 6}, ∅), ({3, 6}, ∅),
    ({3, 6}, {8})]

def DirtyEdges : List (Finset (Fin 10)) :=
  [{2, 3}, {2, 7}, {6, 9}, {7, 9}]

def UniversalEdge (v : Fin 10) : Finset (Fin 10) :=
  match v.val with
  | 0 => {2, 3}
  | 1 => {7, 9}
  | 2 => {2, 3}
  | 3 => {2, 3}
  | 4 => {2, 7}
  | 5 => {2, 3}
  | 6 => {2, 3}
  | 7 => {2, 3}
  | 8 => {2, 7}
  | _ => {2, 3}

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

end R1SplitResource.CausalBarrier

namespace R1SplitResource.ResourceExclusion

open CausalBarrier

abbrev Resource := Finset (Fin 10) × (Finset (Fin 10) → Bool)

def CrossPairs : List (Finset (Fin 10)) :=
  [{2, 3}, {3, 9}, {2, 6}, {6, 9}, {2, 7}, {7, 9}]

def RSafe (E T : Finset (Fin 10)) (w : Resource) : Prop :=
  w.2 E = true → (w.1 ∩ T).Nonempty

def Ordinary (w : Resource) : Prop := ∀ E ∈ CrossPairs, RSafe E E w

def AllOrdinary (p : Multiset Resource) : Prop := ∀ w ∈ p, Ordinary w

def RJoin (a b : Resource) : Resource :=
  (a.1 ∪ b.1, fun E => a.2 E || b.2 E)

def RMeet (a b : Resource) : Resource :=
  (a.1 ∩ b.1, fun E => a.2 E && b.2 E)

def AllowedSides (a b : Resource) : Prop :=
  ((a.1 = b.1 ∨ ((a.1, b.1) ∈ OtherSides ∨ (b.1, a.1) ∈ OtherSides)) ∨
    ((a.1.Nonempty ∧ a.1 ⊆ b.1) ∨ (b.1.Nonempty ∧ b.1 ⊆ a.1))) ∨
  ((a.1 = ∅ ∧ ∀ E ∈ CrossPairs, b.2 E = true) ∨
    (b.1 = ∅ ∧ ∀ E ∈ CrossPairs, a.2 E = true))

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

lemma rsafe_meet_same {E T : Finset (Fin 10)} {a b : Resource}
    (hab : a.1 = b.1) (ha : RSafe E T a) : RSafe E T (RMeet a b) := by
  intro ht
  have hat : a.2 E = true := (Bool.and_eq_true_iff.mp ht).1
  have hh := ha hat
  change ((a.1 ∩ b.1) ∩ T).Nonempty
  simpa only [← hab, Finset.inter_self] using hh

lemma rsafe_meet_left_subset {E T : Finset (Fin 10)} {a b : Resource}
    (hab : a.1 ⊆ b.1) (ha : RSafe E T a) : RSafe E T (RMeet a b) := by
  intro ht
  have hat : a.2 E = true := (Bool.and_eq_true_iff.mp ht).1
  have hh := ha hat
  change ((a.1 ∩ b.1) ∩ T).Nonempty
  simpa only [Finset.inter_eq_left.mpr hab] using hh

lemma rsafe_meet_right_subset {E T : Finset (Fin 10)} {a b : Resource}
    (hba : b.1 ⊆ a.1) (hb : RSafe E T b) : RSafe E T (RMeet a b) := by
  intro ht
  have hbt : b.2 E = true := (Bool.and_eq_true_iff.mp ht).2
  have hh := hb hbt
  change ((a.1 ∩ b.1) ∩ T).Nonempty
  simpa only [Finset.inter_eq_right.mpr hba] using hh

lemma allowed_sides_swap {a b : Resource} (hs : AllowedSides a b) : AllowedSides b a := by
  rcases hs with hs | hs
  · left
    rcases hs with hs | hs | hs
    · rcases hs with heq | hp
      · exact Or.inl (Or.inl heq.symm)
      · exact Or.inl (Or.inr (Or.symm hp))
    · exact Or.inr (Or.inr hs)
    · exact Or.inr (Or.inl hs)
  · exact Or.inr (Or.symm hs)

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
  rcases hs with hs | hs
  · rcases hs with hs | hs | hs
    · rcases hs with heq | hs
      · exact rsafe_meet_same heq (ha E hE)
      · apply rsafe_meet (ha E hE) (hb E hE)
        rcases hs with hs | hs
        · exact (cross_separation E hE _ hs).1
        · exact (cross_separation E hE _ hs).2
    · exact rsafe_meet_left_subset hs.2 (ha E hE)
    · exact rsafe_meet_right_subset hs.2 (hb E hE)
  · apply rsafe_meet (ha E hE) (hb E hE)
    rcases hs with hs | hs
    · simp [Separates, hs.1]
    · simp [Separates, hs.1]

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
    · rcases hside with hside | hside
      · rcases hside with hside | hside | hside
        · rcases hside with heq | hside
          · exact rsafe_meet_same heq ha
          · apply rsafe_meet ha hb
            rcases hside with hside | hside
            · exact (hT _ hside).1
            · exact (hT _ hside).2
        · exact rsafe_meet_left_subset hside.2 ha
        · exact rsafe_meet_right_subset hside.2 hb
      · apply rsafe_meet ha hb
        rcases hside with hs | hs
        · simp [Separates, hs.1]
        · simp [Separates, hs.1]
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
    (∃ E ∈ DirtyEdges, b.1 ∩ E = ∅) ∨ (∀ E ∈ CrossPairs, b.2 E = true) := by
  rcases hs with hs | hs
  · left
    rcases hs with hs | hs | hs
    · rcases hs with heq | hs
      · refine ⟨UniversalEdge 0, universal_edge_valid 0, ?_⟩
        rw [← heq, ha]
        simp
      · have hzero : ∀ AB ∈ OtherSides,
            (AB.1 = ∅ → ∃ E ∈ DirtyEdges, AB.2 ∩ E = ∅) ∧
            (AB.2 = ∅ → ∃ E ∈ DirtyEdges, AB.1 ∩ E = ∅) := by
          simp [OtherSides, DirtyEdges]
        rcases hs with hs | hs
        · exact (hzero _ hs).1 ha
        · exact (hzero _ hs).2 ha
    · have hn := hs.1
      rw [ha] at hn
      exact False.elim (Finset.not_nonempty_empty hn)
    · have hn := hs.1.mono hs.2
      rw [ha] at hn
      exact False.elim (Finset.not_nonempty_empty hn)
  · rcases hs with hs | hs
    · exact Or.inr hs.2
    · left
      refine ⟨UniversalEdge 0, universal_edge_valid 0, ?_⟩
      simp [hs.1]

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
  · rcases zero_side_of_allowed hd hs with hmiss | hfull
    · left
      obtain ⟨E, hE, hdisj⟩ := hmiss
      have hcross := dirty_mem_cross E hE
      refine ⟨E, hE, E, cross_separation E hcross, ?_⟩
      have hc : RSafe E E (RMeet d b) := by
        intro ht
        have hbt : b.2 E = true := (Bool.and_eq_true_iff.mp ht).2
        have hh := hb E hcross hbt
        rw [hdisj] at hh
        exact False.elim (Finset.not_nonempty_empty hh)
      have hpool : AllOrdinary (Keep d + Keep b + rest) := by
        apply allOrdinary_add
        · apply allOrdinary_add
          · intro w hw
            simp [Keep, hd] at hw
          · exact keep_ordinary hb
        · exact hr
      intro w hw
      rcases Multiset.mem_cons.mp hw with rfl | hw
      · exact hc
      · exact hpool w hw E hcross
    · right
      refine ⟨RMeet d b, Keep d + Keep b + rest, rfl, ?_, ?_, ?_⟩
      · simp [RMeet, hd]
      · intro E hE
        simp [RMeet, hdt E hE, hfull E hE]
      · apply allOrdinary_add
        · apply allOrdinary_add
          · intro w hw
            simp [Keep, hd] at hw
          · exact keep_ordinary hb
        · exact hr


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
          exact ⟨allowed_sides_swap hs, hc.trans (rmeet_swap _ _)⟩
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

end R1SplitResource.ResourceExclusion

namespace R1SplitResource.IndexSchedule

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

end R1SplitResource.IndexSchedule
namespace R1SplitResource.DAGBridge

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

def DirtyB : Finset (Fin 10) := {2, 9}

def DirtySides (D : Dag) (g : ℕ) : Prop :=
  (supp 10 D (opA D g) = DirtyA ∧ supp 10 D (opB D g) = DirtyB) ∨
  (supp 10 D (opA D g) = DirtyB ∧ supp 10 D (opB D g) = DirtyA)

lemma cross_hits : ∀ E ∈ CrossPairs,
    (DirtyA ∩ E).Nonempty ∧ (DirtyB ∩ E).Nonempty := by
  simp [CrossPairs, DirtyA, DirtyB]

lemma h3_full_side_resource_true {D : Dag} (hS : Strict 10 D) {w : ℕ}
    (hfull : DirtyA ⊆ supp 10 D w ∨ DirtyB ⊆ supp 10 D w)
    (E : Finset (Fin 10)) (hE : E ∈ CrossPairs) : (DagResource D w).2 E = true := by
  have hh := cross_hits E hE
  apply support_hit_true hS
  rcases hfull with hfull | hfull
  · obtain ⟨v, hv⟩ := hh.1
    exact ⟨v, Finset.mem_inter.mpr ⟨hfull (Finset.mem_inter.mp hv).1, (Finset.mem_inter.mp hv).2⟩⟩
  · obtain ⟨v, hv⟩ := hh.2
    exact ⟨v, Finset.mem_inter.mpr ⟨hfull (Finset.mem_inter.mp hv).1, (Finset.mem_inter.mp hv).2⟩⟩


lemma h3_full_side_allowed_left {D : Dag} (hS : Strict 10 D) {u v : ℕ}
    (hu : supp 10 D u = ∅)
    (hv : DirtyA ⊆ supp 10 D v ∨ DirtyB ⊆ supp 10 D v) :
    AllowedSides (DagResource D u) (DagResource D v) := by
  exact Or.inr (Or.inl ⟨hu, h3_full_side_resource_true hS hv⟩)

lemma h3_full_side_allowed_right {D : Dag} (hS : Strict 10 D) {u v : ℕ}
    (hv : supp 10 D v = ∅)
    (hu : DirtyA ⊆ supp 10 D u ∨ DirtyB ⊆ supp 10 D u) :
    AllowedSides (DagResource D u) (DagResource D v) := by
  exact Or.inr (Or.inr ⟨hv, h3_full_side_resource_true hS hu⟩)

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

end R1SplitResource.DAGBridge

namespace DagTools

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma h3_r1_split_allowed_sides_exclusion {D : Dag} (hS : Strict 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hB : Bzero 10 D = 0)
    {g : ℕ} (hg : g < D.length) (hgt : tag D g = true)
    (hdirty : R1SplitResource.DAGBridge.DirtySides D g)
    (hother : R1SplitResource.DAGBridge.OtherAndSides D g) : False := by
  apply R1SplitResource.DAGBridge.canonical_dag_exclusion hS hB hg hgt hdirty hother
    (outW 10 D) (by unfold outW; omega)
  refine ⟨sem_supp_out petersen_graph_ok hC, ?_, ?_⟩
  · intro E hE
    have hedges : ∀ E ∈ R1SplitResource.CausalBarrier.DirtyEdges,
        sem_Edge petersenAdj (sem_ind E) := by
      unfold R1SplitResource.CausalBarrier.DirtyEdges sem_Edge petersenAdj sem_ind
      decide +kernel
    exact (hC _).mpr (hedges E hE)
  · apply Bool.eq_false_iff.mpr
    intro ht
    have hbad : ¬ sem_Edge petersenAdj (sem_ind ({3, 9} : Finset (Fin 10))) := by
      unfold sem_Edge petersenAdj sem_ind
      decide +kernel
    exact hbad ((hC _).mp ht)

end DagTools

-- proof/pair36_pattern_fragment.lean
namespace DagTools

lemma h3_card_three_eq_of_mem {α : Type} [DecidableEq α] {W : Finset α} {a b c : α}
    (hc : W.card = 3) (ha : a ∈ W) (hb : b ∈ W) (hcm : c ∈ W)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : W = {a,b,c} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl <;> assumption
  · rw [hc]
    simp [hab,hac,hbc]

lemma h3_common_pair_third {α : Type} [DecidableEq α] {X Y : Finset α}
    {a b d P Q : α} (hX : X.card = 3) (hY : Y.card = 3)
    (ha : a ∈ X) (hb : b ∈ Y) (hdX : d ∈ X) (hdY : d ∈ Y)
    (haY : a ∉ Y) (hbX : b ∉ X)
    (hPX : P ∈ X) (hPY : P ∈ Y) (hQX : Q ∈ X) (hQY : Q ∈ Y) (hPQ : P ≠ Q) :
    ∃ q, q ≠ d ∧ X = {a,d,q} ∧ Y = {b,d,q} := by
  have hda : d ≠ a := fun he => haY (he ▸ hdY)
  have hdb : d ≠ b := fun he => hbX (he ▸ hdX)
  have hxcard : (X.erase a).card = 2 := by rw [Finset.card_erase_of_mem ha,hX]
  have hycard : (Y.erase b).card = 2 := by rw [Finset.card_erase_of_mem hb,hY]
  obtain ⟨q,hqd,hqx⟩ := h3_pair_of_card_two (Finset.mem_erase.mpr ⟨hda,hdX⟩) hxcard
  obtain ⟨r,_,hry⟩ := h3_pair_of_card_two (Finset.mem_erase.mpr ⟨hdb,hdY⟩) hycard
  have hx : X = {a,d,q} := by rw [←Finset.insert_erase ha,hqx]
  have hy : Y = {b,d,r} := by rw [←Finset.insert_erase hb,hry]
  have hcommon (e : α) (heX : e ∈ X) (heY : e ∈ Y) (hed : e ≠ d) : e = q ∧ e = r := by
    have hea : e ≠ a := fun he => haY (he ▸ heY)
    have heb : e ≠ b := fun he => hbX (he ▸ heX)
    rw [hx] at heX
    rw [hy] at heY
    simp only [Finset.mem_insert,Finset.mem_singleton] at heX heY
    exact ⟨(heX.resolve_left hea).resolve_left hed,(heY.resolve_left heb).resolve_left hed⟩
  have hqr : q = r := by
    by_cases hPd : P = d
    · have hQd : Q ≠ d := fun he => hPQ (hPd.trans he.symm)
      exact (hcommon Q hQX hQY hQd).1.symm.trans (hcommon Q hQX hQY hQd).2
    · exact (hcommon P hPX hPY hPd).1.symm.trans (hcommon P hPX hPY hPd).2
  exact ⟨q,hqd,hx,by simpa only [←hqr] using hy⟩

lemma h3_pair36_exit_pattern {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hc : ∀ x : Fin 10, x ≠ 0 → x ≠ 3 → x ≠ 6 → (exitArcs 10 D (carrierT 10 D {x})).card = 2)
    (hc3 : (exitArcs 10 D (carrierT 10 D {(3 : Fin 10)})).card = 3)
    (hc6 : (exitArcs 10 D (carrierT 10 D {(6 : Fin 10)})).card = 3)
    (P Q : Nat × Bool) (hPQ : P ≠ Q)
    (hP3 : P ∈ exitArcs 10 D (carrierT 10 D {(3 : Fin 10)}))
    (hP6 : P ∈ exitArcs 10 D (carrierT 10 D {(6 : Fin 10)}))
    (hQ3 : Q ∈ exitArcs 10 D (carrierT 10 D {(3 : Fin 10)}))
    (hQ6 : Q ∈ exitArcs 10 D (carrierT 10 D {(6 : Fin 10)})) :
    ∃ e0 e1 e4 e5 d c : ℕ × Bool,
      supp 10 D (src D e0) = {0} ∧ supp 10 D (src D e1) = {1} ∧
      supp 10 D (src D e4) = {4} ∧ supp 10 D (src D e5) = {5} ∧
      exitArcs 10 D (carrierT 10 D {0}) = {e0} ∧
      exitArcs 10 D (carrierT 10 D {1}) = {h3_opp e0,e1} ∧
      exitArcs 10 D (carrierT 10 D {2}) = {h3_opp e1,h3_opp d} ∧
      exitArcs 10 D (carrierT 10 D {4}) = {h3_opp e0,e4} ∧
      exitArcs 10 D (carrierT 10 D {5}) = {h3_opp e0,e5} ∧
      exitArcs 10 D (carrierT 10 D {7}) = {h3_opp e5,d} ∧
      exitArcs 10 D (carrierT 10 D {8}) = {h3_opp e5,h3_opp c} ∧
      exitArcs 10 D (carrierT 10 D {9}) = {h3_opp e4,h3_opp d} ∧
      ((c = d ∧ ∃ q, q ≠ d ∧
          exitArcs 10 D (carrierT 10 D {3}) = {h3_opp e4,d,q} ∧
          exitArcs 10 D (carrierT 10 D {6}) = {h3_opp e1,d,q}) ∨
       (c ≠ d ∧ exitArcs 10 D (carrierT 10 D {3}) = {h3_opp e4,d,c} ∧
          exitArcs 10 D (carrierT 10 D {6}) = {h3_opp e1,d,c})) := by
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
  obtain ⟨e1, _, hW1⟩ := h3_pair_of_card_two (hAmem 1 (by decide)) (hc 1 (by decide) (by decide) (by decide))
  obtain ⟨e4, _, hW4⟩ := h3_pair_of_card_two (hAmem 4 (by decide)) (hc 4 (by decide) (by decide) (by decide))
  obtain ⟨e5, _, hW5⟩ := h3_pair_of_card_two (hAmem 5 (by decide)) (hc 5 (by decide) (by decide) (by decide))
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
  obtain ⟨g2, _, hW2⟩ := h3_pair_of_card_two ha2 (hc 2 (by decide) (by decide) (by decide))
  obtain ⟨g7, _, hW7⟩ := h3_pair_of_card_two ha7 (hc 7 (by decide) (by decide) (by decide))
  obtain ⟨g8, _, hW8⟩ := h3_pair_of_card_two ha8 (hc 8 (by decide) (by decide) (by decide))
  obtain ⟨g9, _, hW9⟩ := h3_pair_of_card_two ha9 (hc 9 (by decide) (by decide) (by decide))
  have hb1 : supp 10 D (src D (h3_opp (h3_opp e1))) = {(1 : Fin 10)} := by rw [h3_opp_opp]; exact hp1
  have hb4 : supp 10 D (src D (h3_opp (h3_opp e4))) = {(4 : Fin 10)} := by rw [h3_opp_opp]; exact hp4
  have hb5 : supp 10 D (src D (h3_opp (h3_opp e5))) = {(5 : Fin 10)} := by rw [h3_opp_opp]; exact hp5
  have h27 : h3_opp g2 = g7 := h3_split_edge_pair petersen_graph_ok h.1 hC
    (by rw [hW2]) (by rw [hW7]) hb1 hb5 (by decide) (by decide) (by unfold petersenAdj; decide)
  have h79 : h3_opp g7 = g9 := h3_split_edge_pair petersen_graph_ok h.1 hC
    (by rw [hW7]) (by rw [hW9]) hb5 hb4 (by decide) (by decide) (by unfold petersenAdj; decide)
  have hg2 : g2 = h3_opp g7 := by
    have hh := congrArg h3_opp h27
    simpa only [h3_opp_opp] using hh
  have hg9 : g9 = h3_opp g7 := h79.symm
  have hd3 : g7 ∈ exitArcs 10 D (carrierT 10 D {(3 : Fin 10)}) := by
    have hh := sem_two_exit_remaining_slot petersen_graph_ok h.1 hC (by rw [hW2]) hb1
      (by unfold petersenAdj; decide : petersenAdj 2 3) (by decide : (3 : Fin 10) ≠ 1)
    simpa [hg2,h3_opp] using hh
  have hd6 : g7 ∈ exitArcs 10 D (carrierT 10 D {(6 : Fin 10)}) := by
    have hh := sem_two_exit_remaining_slot petersen_graph_ok h.1 hC (by rw [hW9]) hb4
      (by unfold petersenAdj; decide : petersenAdj 9 6) (by decide : (6 : Fin 10) ≠ 4)
    simpa [hg9,h3_opp] using hh
  have hc3' : h3_opp g8 ∈ exitArcs 10 D (carrierT 10 D {(3 : Fin 10)}) :=
    sem_two_exit_remaining_slot petersen_graph_ok h.1 hC (by rw [hW8]) hb5
      (by unfold petersenAdj; decide) (by decide)
  have hc6' : h3_opp g8 ∈ exitArcs 10 D (carrierT 10 D {(6 : Fin 10)}) :=
    sem_two_exit_remaining_slot petersen_graph_ok h.1 hC (by rw [hW8]) hb5
      (by unfold petersenAdj; decide) (by decide)
  have h2src : (2 : Fin 10) ∈ supp 10 D (src D (h3_opp g7)) := by
    rw [←hg2]
    exact (sem_mem_exit1.mp (by rw [hW2]; simp : g2 ∈ exitArcs 10 D (carrierT 10 D {(2 : Fin 10)}))).2.1
  have h9src : (9 : Fin 10) ∈ supp 10 D (src D (h3_opp g7)) := by
    rw [←hg9]
    exact (sem_mem_exit1.mp (by rw [hW9]; simp : g9 ∈ exitArcs 10 D (carrierT 10 D {(9 : Fin 10)}))).2.1
  have h8src : (8 : Fin 10) ∈ supp 10 D (src D g8) :=
    (sem_mem_exit1.mp (by rw [hW8]; simp : g8 ∈ exitArcs 10 D (carrierT 10 D {(8 : Fin 10)}))).2.1
  have h31 : (3 : Fin 10) ∉ supp 10 D (src D (h3_opp e1)) := by
    have hI : ∀ a ∈ ({1,3,9} : Finset (Fin 10)), ∀ b ∈ ({1,3,9} : Finset (Fin 10)), ¬petersenAdj a b := by
      unfold petersenAdj; decide
    have hd := h3_remaining_exit_disjoint petersen_graph_ok h.1 hC
      (e := h3_opp g7) (f := h3_opp e1) (x := (2 : Fin 10))
      (by rw [hW2,hg2]; exact Finset.subset_of_eq (Finset.pair_comm _ _))
      {1,3,9} hI ⟨1,by decide,by unfold petersenAdj; decide⟩
      (fun he => Finset.disjoint_left.mp he h9src (by decide))
    exact fun hm => Finset.disjoint_left.mp hd hm (by decide)
  have h64 : (6 : Fin 10) ∉ supp 10 D (src D (h3_opp e4)) := by
    have hI : ∀ a ∈ ({2,4,6} : Finset (Fin 10)), ∀ b ∈ ({2,4,6} : Finset (Fin 10)), ¬petersenAdj a b := by
      unfold petersenAdj; decide
    have hd := h3_remaining_exit_disjoint petersen_graph_ok h.1 hC
      (e := h3_opp g7) (f := h3_opp e4) (x := (9 : Fin 10))
      (by rw [hW9,hg9]; exact Finset.subset_of_eq (Finset.pair_comm _ _))
      {2,4,6} hI ⟨4,by decide,by unfold petersenAdj; decide⟩
      (fun he => Finset.disjoint_left.mp he h2src (by decide))
    exact fun hm => Finset.disjoint_left.mp hd hm (by decide)
  have hA3n6 : h3_opp e4 ∉ exitArcs 10 D (carrierT 10 D {(6 : Fin 10)}) :=
    fun hm => h64 (sem_mem_exit1.mp hm).2.1
  have hA6n3 : h3_opp e1 ∉ exitArcs 10 D (carrierT 10 D {(3 : Fin 10)}) :=
    fun hm => h31 (sem_mem_exit1.mp hm).2.1
  refine ⟨e0,e1,e4,e5,g7,h3_opp g8,hp0,hp1,hp4,hp5,hW0,hW1,?_,hW4,hW5,hW7,?_,?_,?_⟩
  · simpa only [hg2] using hW2
  · simpa only [h3_opp_opp] using hW8
  · simpa only [hg9] using hW9
  · by_cases hcd : h3_opp g8 = g7
    · left
      exact ⟨hcd,h3_common_pair_third hc3 hc6 ha3 ha6 hd3 hd6 hA3n6 hA6n3 hP3 hP6 hQ3 hQ6 hPQ⟩
    · right
      refine ⟨hcd,?_,?_⟩
      · exact h3_card_three_eq_of_mem hc3 ha3 hd3 hc3'
          (fun he => hA3n6 (he.symm ▸ hd6)) (fun he => hA3n6 (he.symm ▸ hc6')) (Ne.symm hcd)
      · exact h3_card_three_eq_of_mem hc6 ha6 hd6 hc6'
          (fun he => hA6n3 (he.symm ▸ hd3)) (fun he => hA6n3 (he.symm ▸ hc3')) (Ne.symm hcd)

lemma h3_saturated_pair36_exit_pattern {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hone : Bplus 10 D = (eligSet 10 D).card + 1)
    (hSat : h3_saturatedSet 10 D = {3,6}) :
    ∃ e0 e1 e4 e5 d c : ℕ × Bool,
      supp 10 D (src D e0) = {0} ∧ supp 10 D (src D e1) = {1} ∧
      supp 10 D (src D e4) = {4} ∧ supp 10 D (src D e5) = {5} ∧
      exitArcs 10 D (carrierT 10 D {0}) = {e0} ∧
      exitArcs 10 D (carrierT 10 D {1}) = {h3_opp e0,e1} ∧
      exitArcs 10 D (carrierT 10 D {2}) = {h3_opp e1,h3_opp d} ∧
      exitArcs 10 D (carrierT 10 D {4}) = {h3_opp e0,e4} ∧
      exitArcs 10 D (carrierT 10 D {5}) = {h3_opp e0,e5} ∧
      exitArcs 10 D (carrierT 10 D {7}) = {h3_opp e5,d} ∧
      exitArcs 10 D (carrierT 10 D {8}) = {h3_opp e5,h3_opp c} ∧
      exitArcs 10 D (carrierT 10 D {9}) = {h3_opp e4,h3_opp d} ∧
      ((c = d ∧ ∃ q, q ≠ d ∧
          exitArcs 10 D (carrierT 10 D {3}) = {h3_opp e4,d,q} ∧
          exitArcs 10 D (carrierT 10 D {6}) = {h3_opp e1,d,q}) ∨
       (c ≠ d ∧ exitArcs 10 D (carrierT 10 D {3}) = {h3_opp e4,d,c} ∧
          exitArcs 10 D (carrierT 10 D {6}) = {h3_opp e1,d,c})) := by
  have hfin : ∀ x ∈ ({1,4,5} : Finset (Fin 10)), x ∉ ({3,6} : Finset (Fin 10)) := by decide
  have hlo := h3_outside_le_two_nonzero_ge_two h hC hz
    (fun x hx => h3_outside_saturated_le_two hSat (hfin x hx))
  have hc (x : Fin 10) (hx0 : x ≠ 0) (hx3 : x ≠ 3) (hx6 : x ≠ 6) :
      (exitArcs 10 D (carrierT 10 D {x})).card = 2 :=
    Nat.le_antisymm (h3_outside_saturated_le_two hSat (by simp [hx3,hx6])) (hlo x hx0)
  have hm3 : (3 : Fin 10) ∈ h3_saturatedSet 10 D := by rw [hSat]; simp
  have hm6 : (6 : Fin 10) ∈ h3_saturatedSet 10 D := by rw [hSat]; simp
  have hc3 := (h3_one_residual_saturation petersen_graph_ok h hC hone 3 hm3).1
  have hc6 := (h3_one_residual_saturation petersen_graph_ok h hC hone 6 hm6).1
  obtain ⟨P,Q,hPQ,hcommon⟩ := h3_one_residual_common_terminals petersen_graph_ok h hC hone
  exact h3_pair36_exit_pattern h hC hz hc hc3 hc6 P Q
    (fun he => hPQ (congrArg Prod.fst he))
    (hcommon 3 hm3).1 (hcommon 6 hm6).1 (hcommon 3 hm3).2 (hcommon 6 hm6).2

end DagTools

-- geometry/s36_base_geometry_fragment.lean
namespace S36BaseGeometry

def side (i : Fin 11) : Finset (Fin 10) :=
  SideGeometry.mask (([1, 50, 2, 68, 16, 520, 32, 384, 200, 772, 72] : List Nat).getD i.val 0)

def allowed (i : Fin 11) : Finset (Fin 10) :=
  SideGeometry.mask (([1, 1023, 3, 68, 17, 520, 33, 384, 232, 772, 1023] : List Nat).getD i.val 0)

def witnessCode (i : Fin 11) (y : Fin 10) : Nat :=
  ([0, 2, 20, 10, 16, 32, 80, 130, 258, 514, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1044, 1128, 1044, 1060, 1104, 1232, 1300, 1572, 2433, 2306, 0, 2568, 2322, 2594, 0, 2432, 2306, 2562, 0, 4106, 4644, 4106, 0, 4136, 4200, 4234, 4866, 4610, 3141, 9490, 3140, 0, 3152, 3172, 3140, 3280, 9488, 0, 0, 5250, 5396, 5258, 5264, 0, 5328, 5250, 5378, 5890, 7237, 7210, 7236, 7208, 7252, 7208, 7236, 0, 0, 7688, 7429, 7938, 7428, 0, 7444, 0, 0, 0, 7428, 7936, 2121, 8330, 0, 2120, 2256, 2152, 2120, 2240, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List Nat).getD (i.val * 10 + y.val) 0

def witnessVertex (i : Fin 11) (y : Fin 10) : Fin 10 :=
  ⟨witnessCode i y / 1024 % 10, Nat.mod_lt _ (by decide)⟩

def witnessSet (i : Fin 11) (y : Fin 10) : Finset (Fin 10) :=
  SideGeometry.mask (witnessCode i y % 1024)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma witness_valid : ∀ i : Fin 11, ∀ y : Fin 10, y ∉ allowed i →
    let x := witnessVertex i y
    let A := witnessSet i y
    x ∈ side i ∧ y ∈ A ∧
    (∀ u ∈ A, ∀ v ∈ A, ¬ SideGeometry.adj u v) ∧
    (∃ v ∈ A, SideGeometry.adj x v) ∧
    ∀ j : Fin 11, x ∈ side j → j ≠ i → (side j ∩ A).Nonempty := by
  unfold SideGeometry.adj
  decide +kernel

lemma support_bound (S : Fin 11 → Finset (Fin 10))
    (hsub : ∀ i, side i ⊆ S i)
    (hex : ∀ x A, (∀ u ∈ A, ∀ v ∈ A, ¬ SideGeometry.adj u v) →
      (∃ v ∈ A, SideGeometry.adj x v) →
      ∃ i : Fin 11, x ∈ side i ∧ Disjoint (S i) A) :
    ∀ i, S i ⊆ allowed i := by
  intro i y hy
  by_contra hn
  obtain ⟨hx, hyA, hA, hnb, hother⟩ := witness_valid i y hn
  obtain ⟨j, hj, hd⟩ := hex _ _ hA hnb
  by_cases he : j = i
  · subst j
    exact Finset.disjoint_left.mp hd hy hyA
  · obtain ⟨v, hv⟩ := hother j hj he
    obtain ⟨hv, hvA⟩ := Finset.mem_inter.mp hv
    exact Finset.disjoint_left.mp hd (hsub j hv) hvA

end S36BaseGeometry

namespace DagTools

lemma h3_s36_base_source_bounds {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (r : Fin 11 → Nat × Bool)
    (hW : ∀ x : Fin 10, sem_W 10 D x =
      (Finset.univ.filter (fun i : Fin 11 => x ∈ S36BaseGeometry.side i)).image r) :
    ∀ i, supp 10 D (src D (r i)) ⊆ S36BaseGeometry.allowed i := by
  apply S36BaseGeometry.support_bound
  · intro i x hx
    apply (sem_mem_W.mp ?_).2.1
    rw [hW]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hx⟩, rfl⟩
  · intro x A hA hnb
    obtain ⟨j, s, hj, _, hxs, hxn, hd⟩ :=
      sem_exposure petersen_graph_ok h.1 hC A hA x hnb
    have hm : (j, s) ∈ sem_W 10 D x := sem_mem_W.mpr ⟨hj, hxs, hxn⟩
    rw [hW] at hm
    obtain ⟨i, hi, hri⟩ := Finset.mem_image.mp hm
    exact ⟨i, (Finset.mem_filter.mp hi).2, by simpa only [hri] using hd⟩

end DagTools

-- geometry/s36_split_geometry_fragment.lean
namespace S36SplitGeometry

def side (i : Fin 12) : Finset (Fin 10) :=
  SideGeometry.mask (([1, 50, 2, 68, 16, 520, 32, 384, 200, 516, 72, 256] : List Nat).getD i.val 0)

def allowed (i : Fin 12) : Finset (Fin 10) :=
  SideGeometry.mask (([1, 1023, 3, 84, 17, 522, 33, 384, 232, 772, 1023, 804] : List Nat).getD i.val 0)

def witnessCode (i : Fin 12) (y : Fin 10) : Nat :=
  ([0, 2, 20, 10, 16, 32, 80, 130, 258, 514, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1044, 1128, 1044, 1060, 1104, 1232, 1300, 1572, 2569, 2562, 0, 2568, 0, 2594, 0, 6282, 2818, 2562, 0, 4106, 4644, 4106, 0, 4136, 4200, 4234, 4866, 4610, 3141, 0, 3140, 0, 3152, 3172, 3140, 3280, 9492, 0, 0, 5250, 5396, 5258, 5264, 0, 5328, 5250, 5378, 5890, 7237, 7210, 7236, 7208, 7252, 7208, 7236, 0, 0, 7688, 7429, 7938, 7428, 0, 7444, 0, 0, 0, 7428, 7936, 2121, 9354, 0, 2120, 2256, 2152, 2120, 2240, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8329, 8330, 0, 8328, 8400, 0, 8384, 8328, 0, 0] : List Nat).getD (i.val * 10 + y.val) 0

def witnessVertex (i : Fin 12) (y : Fin 10) : Fin 10 :=
  ⟨witnessCode i y / 1024 % 10, Nat.mod_lt _ (by decide)⟩

def witnessSet (i : Fin 12) (y : Fin 10) : Finset (Fin 10) :=
  SideGeometry.mask (witnessCode i y % 1024)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma witness_valid : ∀ i : Fin 12, ∀ y : Fin 10, y ∉ allowed i →
    let x := witnessVertex i y
    let A := witnessSet i y
    x ∈ side i ∧ y ∈ A ∧
    (∀ u ∈ A, ∀ v ∈ A, ¬ SideGeometry.adj u v) ∧
    (∃ v ∈ A, SideGeometry.adj x v) ∧
    ∀ j : Fin 12, x ∈ side j → j ≠ i → (side j ∩ A).Nonempty := by
  unfold SideGeometry.adj
  decide +kernel

lemma support_bound (S : Fin 12 → Finset (Fin 10))
    (hsub : ∀ i, side i ⊆ S i)
    (hex : ∀ x A, (∀ u ∈ A, ∀ v ∈ A, ¬ SideGeometry.adj u v) →
      (∃ v ∈ A, SideGeometry.adj x v) →
      ∃ i : Fin 12, x ∈ side i ∧ Disjoint (S i) A) :
    ∀ i, S i ⊆ allowed i := by
  intro i y hy
  by_contra hn
  obtain ⟨hx, hyA, hA, hnb, hother⟩ := witness_valid i y hn
  obtain ⟨j, hj, hd⟩ := hex _ _ hA hnb
  by_cases he : j = i
  · subst j
    exact Finset.disjoint_left.mp hd hy hyA
  · obtain ⟨v, hv⟩ := hother j hj he
    obtain ⟨hv, hvA⟩ := Finset.mem_inter.mp hv
    exact Finset.disjoint_left.mp hd (hsub j hv) hvA

end S36SplitGeometry

namespace DagTools

lemma h3_s36_split_source_bounds {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (r : Fin 12 → Nat × Bool)
    (hW : ∀ x : Fin 10, sem_W 10 D x =
      (Finset.univ.filter (fun i : Fin 12 => x ∈ S36SplitGeometry.side i)).image r) :
    ∀ i, supp 10 D (src D (r i)) ⊆ S36SplitGeometry.allowed i := by
  apply S36SplitGeometry.support_bound
  · intro i x hx
    apply (sem_mem_W.mp ?_).2.1
    rw [hW]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hx⟩, rfl⟩
  · intro x A hA hnb
    obtain ⟨j, s, hj, _, hxs, hxn, hd⟩ :=
      sem_exposure petersen_graph_ok h.1 hC A hA x hnb
    have hm : (j, s) ∈ sem_W 10 D x := sem_mem_W.mpr ⟨hj, hxs, hxn⟩
    rw [hW] at hm
    obtain ⟨i, hi, hri⟩ := Finset.mem_image.mp hm
    exact ⟨i, (Finset.mem_filter.mp hi).2, by simpa only [hri] using hd⟩

end DagTools

-- proof/pair36_indexed_fragment.lean
namespace S36BaseGeometry

def incidenceIndices (x : Fin 10) : Finset (Fin 11) :=
  ([{0}, {1, 2}, {3, 9}, {5, 8, 10}, {1, 4}, {1, 6}, {3, 8, 10}, {7, 8}, {7, 9}, {5, 9}] : List (Finset (Fin 11))).getD x.val ∅

lemma incidence_indices : ∀ x : Fin 10,
    Finset.univ.filter (fun i : Fin 11 => x ∈ side i) = incidenceIndices x := by
  decide +kernel

end S36BaseGeometry

namespace S36SplitGeometry

def incidenceIndices (x : Fin 10) : Finset (Fin 12) :=
  ([{0}, {1, 2}, {3, 9}, {5, 8, 10}, {1, 4}, {1, 6}, {3, 8, 10}, {7, 8}, {7, 11}, {5, 9}] : List (Finset (Fin 12))).getD x.val ∅

lemma incidence_indices : ∀ x : Fin 10,
    Finset.univ.filter (fun i : Fin 12 => x ∈ side i) = incidenceIndices x := by
  decide +kernel

end S36SplitGeometry

namespace DagTools

def h3_s36_baseMap (e0 e1 e4 e5 d q : Nat × Bool) (i : Fin 11) : Nat × Bool :=
  ([e0,h3_opp e0,e1,h3_opp e1,e4,h3_opp e4,e5,h3_opp e5,d,h3_opp d,q] :
    List (Nat × Bool)).getD i.val e0

def h3_s36_splitMap (e0 e1 e4 e5 d c : Nat × Bool) (i : Fin 12) : Nat × Bool :=
  ([e0,h3_opp e0,e1,h3_opp e1,e4,h3_opp e4,e5,h3_opp e5,d,h3_opp d,c,h3_opp c] :
    List (Nat × Bool)).getD i.val e0

lemma h3_saturated_pair36_indexed_profiles {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hone : Bplus 10 D = (eligSet 10 D).card + 1)
    (hSat : h3_saturatedSet 10 D = {3,6}) :
    (∃ e0 e1 e4 e5 d q : Nat × Bool,
      supp 10 D (src D e0) = {0} ∧ supp 10 D (src D e1) = {1} ∧
      supp 10 D (src D e4) = {4} ∧ supp 10 D (src D e5) = {5} ∧ q ≠ d ∧
      ∀ x : Fin 10, sem_W 10 D x =
        (Finset.univ.filter (fun i : Fin 11 => x ∈ S36BaseGeometry.side i)).image (h3_s36_baseMap e0 e1 e4 e5 d q)) ∨
    (∃ e0 e1 e4 e5 d c : Nat × Bool,
      supp 10 D (src D e0) = {0} ∧ supp 10 D (src D e1) = {1} ∧
      supp 10 D (src D e4) = {4} ∧ supp 10 D (src D e5) = {5} ∧ c ≠ d ∧
      ∀ x : Fin 10, sem_W 10 D x =
        (Finset.univ.filter (fun i : Fin 12 => x ∈ S36SplitGeometry.side i)).image (h3_s36_splitMap e0 e1 e4 e5 d c)) := by
  obtain ⟨e0,e1,e4,e5,d,c,hp0,hp1,hp4,hp5,hW0,hW1,hW2,hW4,hW5,hW7,hW8,hW9,hcase⟩ :=
    h3_saturated_pair36_exit_pattern h hC hz hone hSat
  rcases hcase with ⟨hcd,q,hqd,hW3,hW6⟩ | ⟨hcd,hW3,hW6⟩
  · subst c
    left
    refine ⟨e0,e1,e4,e5,d,q,hp0,hp1,hp4,hp5,hqd,?_⟩
    intro x
    rw [S36BaseGeometry.incidence_indices]
    fin_cases x
    · simpa [sem_W,h3_s36_baseMap,S36BaseGeometry.incidenceIndices,Finset.pair_comm] using hW0
    · simpa [sem_W,h3_s36_baseMap,S36BaseGeometry.incidenceIndices,Finset.pair_comm] using hW1
    · simpa [sem_W,h3_s36_baseMap,S36BaseGeometry.incidenceIndices,Finset.pair_comm] using hW2
    · simpa [sem_W,h3_s36_baseMap,S36BaseGeometry.incidenceIndices,Finset.pair_comm] using hW3
    · simpa [sem_W,h3_s36_baseMap,S36BaseGeometry.incidenceIndices,Finset.pair_comm] using hW4
    · simpa [sem_W,h3_s36_baseMap,S36BaseGeometry.incidenceIndices,Finset.pair_comm] using hW5
    · simpa [sem_W,h3_s36_baseMap,S36BaseGeometry.incidenceIndices,Finset.pair_comm] using hW6
    · simpa [sem_W,h3_s36_baseMap,S36BaseGeometry.incidenceIndices,Finset.pair_comm] using hW7
    · simpa [sem_W,h3_s36_baseMap,S36BaseGeometry.incidenceIndices,Finset.pair_comm] using hW8
    · simpa [sem_W,h3_s36_baseMap,S36BaseGeometry.incidenceIndices,Finset.pair_comm] using hW9
  · right
    refine ⟨e0,e1,e4,e5,d,c,hp0,hp1,hp4,hp5,hcd,?_⟩
    intro x
    rw [S36SplitGeometry.incidence_indices]
    fin_cases x
    · simpa [sem_W,h3_s36_splitMap,S36SplitGeometry.incidenceIndices,Finset.pair_comm] using hW0
    · simpa [sem_W,h3_s36_splitMap,S36SplitGeometry.incidenceIndices,Finset.pair_comm] using hW1
    · simpa [sem_W,h3_s36_splitMap,S36SplitGeometry.incidenceIndices,Finset.pair_comm] using hW2
    · simpa [sem_W,h3_s36_splitMap,S36SplitGeometry.incidenceIndices,Finset.pair_comm] using hW3
    · simpa [sem_W,h3_s36_splitMap,S36SplitGeometry.incidenceIndices,Finset.pair_comm] using hW4
    · simpa [sem_W,h3_s36_splitMap,S36SplitGeometry.incidenceIndices,Finset.pair_comm] using hW5
    · simpa [sem_W,h3_s36_splitMap,S36SplitGeometry.incidenceIndices,Finset.pair_comm] using hW6
    · simpa [sem_W,h3_s36_splitMap,S36SplitGeometry.incidenceIndices,Finset.pair_comm] using hW7
    · simpa [sem_W,h3_s36_splitMap,S36SplitGeometry.incidenceIndices,Finset.pair_comm] using hW8
    · simpa [sem_W,h3_s36_splitMap,S36SplitGeometry.incidenceIndices,Finset.pair_comm] using hW9

end DagTools

-- proof/common_pair_residual_fragment.lean
namespace DagTools

lemma h3_residual_subset_common_pair {n : Nat} {D : Dag} {G : Fin n → Fin n → Prop}
    (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (b : Fin n → Nat) (hb : sem_MinBranch n D b)
    (hone : Bplus n D = (eligSet n D).card + 1)
    (X : Finset (Fin n)) (hX : X.Nonempty) (hsat : ∀ x ∈ X, 3 ≤ (sem_W n D x).card)
    (d c : Nat × Bool)
    (hpair : ∀ e : Nat × Bool, (∀ x ∈ X, e ∈ sem_W n D x) → e = d ∨ e = c) :
    ∀ u ∈ residualUnits n D b, supp n D u.1 ⊆ supp n D (src D d) ∩ supp n D (src D c) := by
  obtain ⟨u0,P,Q,hres,hPQ,hcommon,_,_,hsub⟩ :=
    h3_common_terminals_actual_paths hG h hC b hb hone X hX hsat
  have hP := hpair P (fun x hx => (hcommon x hx).1)
  have hQ := hpair Q (fun x hx => (hcommon x hx).2)
  intro u hu
  rw [hres,Finset.mem_singleton] at hu
  subst u
  rcases hP with rfl | rfl <;> rcases hQ with hQ | hQ
  · exact (hPQ (congrArg Prod.fst hQ.symm)).elim
  · simpa only [hQ] using hsub
  · simpa only [hQ,Finset.inter_comm] using hsub
  · exact (hPQ (congrArg Prod.fst hQ.symm)).elim

lemma h3_pair36_residual_subset {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (b : Fin 10 → Nat) (hb : sem_MinBranch 10 D b)
    (hone : Bplus 10 D = (eligSet 10 D).card + 1)
    (hSat : h3_saturatedSet 10 D = {3,6})
    (A d c : Nat × Bool)
    (hW3 : sem_W 10 D (3 : Fin 10) = {A,d,c})
    (hA6 : (6 : Fin 10) ∉ supp 10 D (src D A)) :
    ∀ u ∈ residualUnits 10 D b, supp 10 D u.1 ⊆ supp 10 D (src D d) ∩ supp 10 D (src D c) := by
  refine h3_residual_subset_common_pair petersen_graph_ok h hC b hb hone {3,6}
    (by simp) ?_ d c ?_
  · intro x hx
    have hm : x ∈ h3_saturatedSet 10 D := by rwa [hSat]
    exact (Finset.mem_filter.mp hm).2
  · intro e he
    have he3 := he 3 (by simp)
    have he6 := he 6 (by simp)
    rw [hW3] at he3
    simp only [Finset.mem_insert,Finset.mem_singleton] at he3
    rcases he3 with rfl | he | he
    · exact (hA6 (sem_mem_W.mp he6).2.1).elim
    · exact Or.inl he
    · exact Or.inr he

end DagTools

-- geometry/s36_sources_common_fragment.lean
namespace DagTools

lemma h3_injective_source_exact {D : Dag} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ι → Nat × Bool) (side : ι → Finset (Fin 10))
    (hW : ∀ x : Fin 10, sem_W 10 D x = (Finset.univ.filter (fun i => x ∈ side i)).image r)
    (hinj : Function.Injective r) (i : ι) (he : (r i).1 < D.length)
    (hout : supp 10 D (10+(r i).1) = ∅) :
    supp 10 D (src D (r i)) = side i := by
  apply Finset.Subset.antisymm
  · intro y hy
    obtain ⟨j,hj,heq⟩ := h3_source_index_of_empty_output r side hW he hout hy
    simpa only [hinj heq] using hj
  · exact h3_indexed_source_lower r side hW i

lemma h3_output_empty_of_disjoint_upper {D : Dag} (hS : Strict 10 D)
    (e : Nat × Bool) (he : e.1 < D.length) (ht : tag D e.1 = true)
    (A B : Finset (Fin 10))
    (ha : supp 10 D (src D e) ⊆ A)
    (hb : supp 10 D (src D (h3_opp e)) ⊆ B) (hd : Disjoint A B) :
    supp 10 D (10+e.1) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact Finset.disjoint_left.mp hd (ha (sem_supp_and_sub hS he ht e.2 hx))
    (hb (sem_supp_and_sub hS he ht (!e.2) hx))

end DagTools

namespace S36BaseGeometry
def tight (i : Fin 11) : Finset (Fin 10) :=
  SideGeometry.mask (([1, 50, 2, 68, 16, 520, 32, 384, 232, 772, 1023] : List Nat).getD i.val 0)

def pair (i : Fin 11) : Fin 11 :=
  ([1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 10] : List (Fin 11)).getD i.val 0

lemma compatible : ∀ i j : Fin 11, side i ⊆ tight j → side j ⊆ tight i →
    i = j ∨ (i = 8 ∧ j = 10) ∨ (i = 10 ∧ j = 8) := by
  decide +kernel

lemma tight_disjoint : ∀ i : Fin 11, i.val < 10 → Disjoint (tight i) (tight (pair i)) := by
  decide +kernel
end S36BaseGeometry

namespace S36SplitGeometry
def tight (i : Fin 12) : Finset (Fin 10) :=
  SideGeometry.mask (([1, 50, 2, 84, 16, 522, 32, 384, 232, 772, 1023, 804] : List Nat).getD i.val 0)

def pair (i : Fin 12) : Fin 12 :=
  ([1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10] : List (Fin 12)).getD i.val 0

lemma compatible : ∀ i j : Fin 12, side i ⊆ tight j → side j ⊆ tight i →
    i = j ∨ (i = 8 ∧ j = 10) ∨ (i = 10 ∧ j = 8) ∨ (i = 9 ∧ j = 11) ∨ (i = 11 ∧ j = 9) := by
  decide +kernel

lemma tight_disjoint : ∀ i : Fin 12, i.val < 10 → Disjoint (tight i) (tight (pair i)) := by
  decide +kernel
end S36SplitGeometry

-- geometry/s36_base_sources_fragment.lean
namespace DagTools

lemma h3_s36_base_first_sources {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hB0 : Bzero 10 D = 0) (e0 e1 e4 e5 d q : Nat × Bool)
    (hp0 : supp 10 D (src D e0) = {0})
    (hp1 : supp 10 D (src D e1) = {1})
    (hp4 : supp 10 D (src D e4) = {4})
    (hp5 : supp 10 D (src D e5) = {5}) (hne : q ≠ d)
    (hW : ∀ x : Fin 10, sem_W 10 D x =
      (Finset.univ.filter (fun i : Fin 11 => x ∈ S36BaseGeometry.side i)).image
        (h3_s36_baseMap e0 e1 e4 e5 d q)) :
    Function.Injective (h3_s36_baseMap e0 e1 e4 e5 d q) ∧
    ∀ i : Fin 11, i.val < 10 →
      supp 10 D (src D (h3_s36_baseMap e0 e1 e4 e5 d q i)) = S36BaseGeometry.side i := by
  let R := h3_s36_baseMap e0 e1 e4 e5 d q
  have hb := h3_s36_base_source_bounds h hC R hW
  have hlo := h3_indexed_source_lower R S36BaseGeometry.side hW
  have hW4 : sem_W 10 D (4 : Fin 10) = {h3_opp e0,e4} := by
    rw [hW,S36BaseGeometry.incidence_indices]
    simp [h3_s36_baseMap,S36BaseGeometry.incidenceIndices]
  have hN : ({1,4,5} : Finset (Fin 10)) ⊆ supp 10 D (src D (h3_opp e0)) := by
    have hh := hlo 1
    rw [show S36BaseGeometry.side 1 = ({1,4,5} : Finset (Fin 10)) by decide] at hh
    simpa [R,h3_s36_baseMap] using hh
  have hstar := h3_star0_exact_of_two_exit_pure_companion h hC hz hB0 (h3_opp e0) e4 hW4 hp4 hN
  have ht : ∀ i : Fin 11, supp 10 D (src D (R i)) ⊆ S36BaseGeometry.tight i := by
    intro i
    fin_cases i
    · exact (hp0.trans (by decide)).subset
    · exact (hstar.trans (by decide)).subset
    · exact (hp1.trans (by decide)).subset
    · exact hb 3
    · exact (hp4.trans (by decide)).subset
    · exact hb 5
    · exact (hp5.trans (by decide)).subset
    · exact hb 7
    · exact hb 8
    · exact hb 9
    · exact hb 10
  have hinj : Function.Injective R := by
    intro i j heq
    have ha : S36BaseGeometry.side i ⊆ S36BaseGeometry.tight j := by
      intro x hx
      apply ht j
      rw [← heq]
      exact hlo i hx
    have hb' : S36BaseGeometry.side j ⊆ S36BaseGeometry.tight i := by
      intro x hx
      apply ht i
      rw [heq]
      exact hlo j hx
    rcases S36BaseGeometry.compatible i j ha hb' with he | ⟨hi,hj⟩ | ⟨hi,hj⟩
    · exact he
    · subst i; subst j; exact (hne heq.symm).elim
    · subst i; subst j; exact (hne heq).elim
  refine ⟨hinj, ?_⟩
  have hv := h3_nonempty_incidence_gate_valid h.1 S36BaseGeometry.side R (by decide +kernel) hW
  have hp : ∀ i : Fin 11, i.val < 10 → R (S36BaseGeometry.pair i) = h3_opp (R i) := by
    intro i hi
    fin_cases i <;> simp [R,h3_s36_baseMap,S36BaseGeometry.pair,h3_opp] at hi ⊢
  intro i hi
  apply h3_injective_source_exact R S36BaseGeometry.side hW hinj i (hv i).1
  apply h3_output_empty_of_disjoint_upper h.1 (R i) (hv i).1 (hv i).2
    (S36BaseGeometry.tight i) (S36BaseGeometry.tight (S36BaseGeometry.pair i)) (ht i)
  · simpa only [hp i hi] using ht (S36BaseGeometry.pair i)
  · exact S36BaseGeometry.tight_disjoint i hi

end DagTools

-- geometry/s36_split_sources_fragment.lean
namespace DagTools

lemma h3_s36_split_first_sources {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hB0 : Bzero 10 D = 0) (e0 e1 e4 e5 d c : Nat × Bool)
    (hp0 : supp 10 D (src D e0) = {0})
    (hp1 : supp 10 D (src D e1) = {1})
    (hp4 : supp 10 D (src D e4) = {4})
    (hp5 : supp 10 D (src D e5) = {5}) (hne : c ≠ d)
    (hW : ∀ x : Fin 10, sem_W 10 D x =
      (Finset.univ.filter (fun i : Fin 12 => x ∈ S36SplitGeometry.side i)).image
        (h3_s36_splitMap e0 e1 e4 e5 d c)) :
    Function.Injective (h3_s36_splitMap e0 e1 e4 e5 d c) ∧
    ∀ i : Fin 12, i.val < 10 →
      supp 10 D (src D (h3_s36_splitMap e0 e1 e4 e5 d c i)) = S36SplitGeometry.side i := by
  let R := h3_s36_splitMap e0 e1 e4 e5 d c
  have hb := h3_s36_split_source_bounds h hC R hW
  have hlo := h3_indexed_source_lower R S36SplitGeometry.side hW
  have hW4 : sem_W 10 D (4 : Fin 10) = {h3_opp e0,e4} := by
    rw [hW,S36SplitGeometry.incidence_indices]
    simp [h3_s36_splitMap,S36SplitGeometry.incidenceIndices]
  have hN : ({1,4,5} : Finset (Fin 10)) ⊆ supp 10 D (src D (h3_opp e0)) := by
    have hh := hlo 1
    rw [show S36SplitGeometry.side 1 = ({1,4,5} : Finset (Fin 10)) by decide] at hh
    simpa [R,h3_s36_splitMap] using hh
  have hstar := h3_star0_exact_of_two_exit_pure_companion h hC hz hB0 (h3_opp e0) e4 hW4 hp4 hN
  have ht : ∀ i : Fin 12, supp 10 D (src D (R i)) ⊆ S36SplitGeometry.tight i := by
    intro i
    fin_cases i
    · exact (hp0.trans (by decide)).subset
    · exact (hstar.trans (by decide)).subset
    · exact (hp1.trans (by decide)).subset
    · exact hb 3
    · exact (hp4.trans (by decide)).subset
    · exact hb 5
    · exact (hp5.trans (by decide)).subset
    · exact hb 7
    · exact hb 8
    · exact hb 9
    · exact hb 10
    · exact hb 11
  have hinj : Function.Injective R := by
    intro i j heq
    have ha : S36SplitGeometry.side i ⊆ S36SplitGeometry.tight j := by
      intro x hx
      apply ht j
      rw [← heq]
      exact hlo i hx
    have hb' : S36SplitGeometry.side j ⊆ S36SplitGeometry.tight i := by
      intro x hx
      apply ht i
      rw [heq]
      exact hlo j hx
    rcases S36SplitGeometry.compatible i j ha hb' with he | ⟨hi,hj⟩ | ⟨hi,hj⟩ | ⟨hi,hj⟩ | ⟨hi,hj⟩
    · exact he
    · subst i; subst j; exact (hne heq.symm).elim
    · subst i; subst j; exact (hne heq).elim
    · subst i; subst j
      apply False.elim
      apply hne
      have hh := congrArg h3_opp heq
      simpa [R,h3_s36_splitMap,h3_opp_opp] using hh.symm
    · subst i; subst j
      apply False.elim
      apply hne
      have hh := congrArg h3_opp heq
      simpa [R,h3_s36_splitMap,h3_opp_opp] using hh
  refine ⟨hinj, ?_⟩
  have hv := h3_nonempty_incidence_gate_valid h.1 S36SplitGeometry.side R (by decide +kernel) hW
  have hp : ∀ i : Fin 12, i.val < 10 → R (S36SplitGeometry.pair i) = h3_opp (R i) := by
    intro i hi
    fin_cases i <;> simp [R,h3_s36_splitMap,S36SplitGeometry.pair,h3_opp] at hi ⊢
  intro i hi
  apply h3_injective_source_exact R S36SplitGeometry.side hW hinj i (hv i).1
  apply h3_output_empty_of_disjoint_upper h.1 (R i) (hv i).1 (hv i).2
    (S36SplitGeometry.tight i) (S36SplitGeometry.tight (S36SplitGeometry.pair i)) (ht i)
  · simpa only [hp i hi] using ht (S36SplitGeometry.pair i)
  · exact S36SplitGeometry.tight_disjoint i hi

end DagTools

-- geometry/s36_split_full_sources_fragment.lean
namespace DagTools

lemma h3_s36_split_full_sources {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hB0 : Bzero 10 D = 0)
    (hone : Bplus 10 D = (eligSet 10 D).card + 1)
    (hSat : h3_saturatedSet 10 D = {3,6}) (e0 e1 e4 e5 d c : Nat × Bool)
    (hp0 : supp 10 D (src D e0) = {0})
    (hp1 : supp 10 D (src D e1) = {1})
    (hp4 : supp 10 D (src D e4) = {4})
    (hp5 : supp 10 D (src D e5) = {5}) (hne : c ≠ d)
    (hW : ∀ x : Fin 10, sem_W 10 D x =
      (Finset.univ.filter (fun i : Fin 12 => x ∈ S36SplitGeometry.side i)).image
        (h3_s36_splitMap e0 e1 e4 e5 d c)) :
    ∀ i : Fin 12, supp 10 D (src D (h3_s36_splitMap e0 e1 e4 e5 d c i)) =
      S36SplitGeometry.side i := by
  let R := h3_s36_splitMap e0 e1 e4 e5 d c
  obtain ⟨hinj,hfirst⟩ := h3_s36_split_first_sources h hC hz hB0 e0 e1 e4 e5 d c
    hp0 hp1 hp4 hp5 hne hW
  have hb := h3_s36_split_source_bounds h hC R hW
  have hv := h3_nonempty_incidence_gate_valid h.1 S36SplitGeometry.side R (by decide +kernel) hW
  have hW3 : sem_W 10 D (3 : Fin 10) = {h3_opp e4,d,c} := by
    rw [hW,S36SplitGeometry.incidence_indices]
    simp [h3_s36_splitMap,S36SplitGeometry.incidenceIndices]
  have hA6 : (6 : Fin 10) ∉ supp 10 D (src D (h3_opp e4)) := by
    have hh := hfirst 5 (by decide)
    rw [show S36SplitGeometry.side 5 = ({3,9} : Finset (Fin 10)) by decide] at hh
    change supp 10 D (src D (h3_opp e4)) = {3,9} at hh
    rw [hh]
    decide
  obtain ⟨b,hbm⟩ := sem_exists_minBranch petersen_graph_ok h.1 hC
  have hbp := sem_minBranch_pure hbm
  have hcR : (residualUnits 10 D b).card = 1 := by
    have := card_residual h.1 b hbp
    omega
  obtain ⟨u,hRu⟩ := Finset.card_eq_one.mp hcR
  have hres := h3_pair36_residual_subset h hC b hbm hone hSat (h3_opp e4) d c hW3 hA6
    u (by rw [hRu]; simp)
  have hu : supp 10 D u.1 ⊆ S36SplitGeometry.side 8 := by
    intro x hx
    have hh := (Finset.mem_inter.mp (hres hx)).1
    have hd := hfirst 8 (by decide)
    change supp 10 D (src D d) = S36SplitGeometry.side 8 at hd
    simpa only [hd] using hh
  have hcfinite : ∀ x ∈ SideGeometry.mask 804,
      (Finset.univ.filter (fun i : Fin 12 => x ∈ S36SplitGeometry.side i)).card = 2 := by
    decide +kernel
  have hm : ∀ x ∈ SideGeometry.mask 804, merges 10 D (carrierT 10 D {x}) = ∅ := by
    intro x hx
    have hxR : x ∉ supp 10 D u.1 := by
      intro hh
      have hd : Disjoint (S36SplitGeometry.side 8) (SideGeometry.mask 804) := by decide +kernel
      exact Finset.disjoint_left.mp hd (hu hh) hx
    have hcx : (exitArcs 10 D (carrierT 10 D {x})).card = 2 := by
      change (sem_W 10 D x).card = 2
      rw [hW,Finset.card_image_of_injective _ hinj]
      exact hcfinite x hx
    have hf := h3_residual_singleton_flow petersen_graph_ok h hC b hbp u hRu x
    rw [hcx,ite_eq_right hxR] at hf
    have he : (if x ∈ eligSet 10 D then 1 else 0) ≤ 1 := by split <;> omega
    exact Finset.card_eq_zero.mp (by omega)
  have houtc : supp 10 D (10+c.1) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hop : x ∈ supp 10 D (src D (R 11)) :=
      sem_supp_and_sub h.1 (hv 10).1 (hv 10).2 (!c.2) hx
    have hxA : x ∈ SideGeometry.mask 804 := hb 11 hop
    exact h3_s1_no_and_output h.1 x (hm x hxA) (hv 10).1 (hv 10).2 hx
  intro i
  by_cases hi : i.val < 10
  · exact hfirst i hi
  · have hei : i = 10 ∨ i = 11 := by omega
    rcases hei with rfl | rfl
    · exact h3_injective_source_exact R S36SplitGeometry.side hW hinj 10 (hv 10).1 houtc
    · exact h3_injective_source_exact R S36SplitGeometry.side hW hinj 11 (hv 11).1 houtc

end DagTools

-- proof/pair36_resource_fragment.lean
namespace DagTools

open R1FlexibleResource.CausalBarrier R1FlexibleResource.ResourceExclusion
  R1FlexibleResource.DAGBridge in
lemma h3_canonical_shared_extra_exclusion {D : Dag} (hS : Strict 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hB0 : Bzero 10 D = 0)
    (r : Fin 10 → Nat × Bool) (q : Nat × Bool) (X : Finset (Fin 10))
    (hX : (X,∅) ∈ R1FlexibleResource.CausalBarrier.OtherSides)
    (hopp : ∀ i, r (SideGeometry.opposite i) = ((r i).1,!(r i).2))
    (hsrc : ∀ i, supp 10 D (src D (r i)) = SideGeometry.side i)
    (hvalid : ∀ i, (r i).1 < D.length ∧ tag D (r i).1 = true)
    (hcover : ∀ x : Fin 10, ∀ e ∈ exitArcs 10 D (carrierT 10 D {x}),
      (∃ i, r i = e) ∨ (x ∈ X ∧ e = q))
    (hq : ∀ x ∈ X, q ∈ exitArcs 10 D (carrierT 10 D {x})) : False := by
  have hp : r 9 = ((r 8).1, !(r 8).2) := by
    simpa [SideGeometry.opposite] using hopp 8
  have hdirty : DirtySides D (r 8).1 := by
    have h8 := hsrc 8
    have h9 := hsrc 9
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
    intro j hj hjd ht
    by_cases hex : ∃ i, (r i).1 = j
    · obtain ⟨i, hi⟩ := hex
      have he : ∃ k, r k = (j, false) := by
        cases hb : (r i).2
        · exact ⟨i, Prod.ext hi hb⟩
        · refine ⟨SideGeometry.opposite i, ?_⟩
          rw [hopp, hi, hb]
          rfl
      obtain ⟨k, hk⟩ := he
      have hka : supp 10 D (opA D j) = SideGeometry.side k := by
        simpa [hk, src] using hsrc k
      have hkb : supp 10 D (opB D j) = SideGeometry.side (SideGeometry.opposite k) := by
        simpa [hopp, hk, src] using hsrc (SideGeometry.opposite k)
      have hk8 : k ≠ 8 := by
        intro he
        subst k
        exact hjd (congrArg Prod.fst hk).symm
      have hk9 : k ≠ 9 := by
        intro he
        subst k
        have heq := congrArg Prod.fst hk
        rw [hp] at heq
        exact hjd heq.symm
      apply Or.inl
      apply Or.inl
      apply Or.inr
      change (supp 10 D (opA D j), supp 10 D (opB D j)) ∈ OtherSides ∨
        (supp 10 D (opB D j), supp 10 D (opA D j)) ∈ OtherSides
      rw [hka, hkb]
      exact h3_all_two_flexible_other_sides k hk8 hk9
    · rcases h3_nonindexed_and_shared_extra_type hS r X q hcover hq hj ht
        (fun i hi => hex ⟨i,hi⟩) with he | ha | hb | ⟨ha0,hbX⟩ | ⟨hb0,haX⟩
      · exact Or.inl (Or.inl (Or.inl he))
      · exact Or.inl (Or.inr (Or.inl ha))
      · exact Or.inl (Or.inr (Or.inr hb))
      · apply Or.inl
        apply Or.inl
        apply Or.inr
        right
        change (supp 10 D (opB D j), supp 10 D (opA D j)) ∈ OtherSides
        simpa only [ha0,hbX] using hX
      · apply Or.inl
        apply Or.inl
        apply Or.inr
        left
        change (supp 10 D (opA D j), supp 10 D (opB D j)) ∈ OtherSides
        simpa only [hb0,haX] using hX
  exact h3_r1_flexible_allowed_sides_exclusion hS hC hB0
    (hvalid 8).1 (hvalid 8).2 hdirty hother

lemma h3_nonindexed_and_equal {n : Nat} {D : Dag} (hS : Strict n D)
    {ι : Type*} (r : ι → Nat × Bool)
    (hcover : ∀ x : Fin n, ∀ e ∈ sem_W n D x, ∃ i, r i = e)
    {j : Nat} (hj : j < D.length) (ht : tag D j = true) (hne : ∀ i, (r i).1 ≠ j) :
    supp n D (opA D j) = supp n D (opB D j) := by
  have hside (s : Bool) {x : Fin n} (hx : x ∈ supp n D (src D (j,s))) :
      x ∈ supp n D (src D (j,!s)) := by
    by_contra hn
    have hout : x ∉ supp n D (n+j) := fun hh => hn (sem_supp_and_sub hS hj ht (!s) hh)
    obtain ⟨i,hi⟩ := hcover x (j,s) (sem_mem_W.mpr ⟨hj,hx,hout⟩)
    exact hne i (congrArg Prod.fst hi)
  ext x
  exact ⟨hside false,hside true⟩

open R1SplitResource.CausalBarrier R1SplitResource.ResourceExclusion R1SplitResource.DAGBridge in
lemma h3_s36_split_other_sides : ∀ i : Fin 12, i ≠ 8 → h3_s1_splitOpposite i ≠ 8 →
    (S36SplitGeometry.side i,S36SplitGeometry.side (h3_s1_splitOpposite i)) ∈ OtherSides ∨
    (S36SplitGeometry.side (h3_s1_splitOpposite i),S36SplitGeometry.side i) ∈ OtherSides := by
  unfold S36SplitGeometry.side SideGeometry.mask h3_s1_splitOpposite OtherSides
  decide +kernel

open R1SplitResource.CausalBarrier R1SplitResource.ResourceExclusion R1SplitResource.DAGBridge in
lemma h3_s36_split_indexed_exclusion {D : Dag} (hS : Strict 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hB0 : Bzero 10 D = 0)
    (r : Fin 12 → Nat × Bool)
    (hopp : ∀ i, r (h3_s1_splitOpposite i) = ((r i).1,!(r i).2))
    (hsrc : ∀ i, supp 10 D (src D (r i)) = S36SplitGeometry.side i)
    (hvalid : ∀ i, (r i).1 < D.length ∧ tag D (r i).1 = true)
    (hcover : ∀ x : Fin 10, ∀ e ∈ sem_W 10 D x, ∃ i, r i = e) : False := by
  have hdirty : DirtySides D (r 8).1 := by
    have hA := hsrc 8
    have hB := hsrc (h3_s1_splitOpposite 8)
    have hda : S36SplitGeometry.side 8 = DirtyA := by decide +kernel
    have hdb : S36SplitGeometry.side (h3_s1_splitOpposite 8) = DirtyB := by decide +kernel
    rw [hda] at hA
    rw [hdb] at hB
    cases hb : (r 8).2
    · left
      exact ⟨by simpa [src,hb] using hA,by simpa [hopp,src,hb] using hB⟩
    · right
      exact ⟨by simpa [hopp,src,hb] using hB,by simpa [src,hb] using hA⟩
  have hother : OtherAndSides D (r 8).1 := by
    intro j hj hjd ht
    by_cases hex : ∃ i, (r i).1 = j
    · obtain ⟨i,hi⟩ := hex
      have he : ∃ k, r k = (j,false) := by
        cases hb : (r i).2
        · exact ⟨i,Prod.ext hi hb⟩
        · refine ⟨h3_s1_splitOpposite i,?_⟩
          rw [hopp,hi,hb]
          rfl
      obtain ⟨k,hk⟩ := he
      have hka : supp 10 D (opA D j) = S36SplitGeometry.side k := by
        simpa [hk,src] using hsrc k
      have hkb : supp 10 D (opB D j) = S36SplitGeometry.side (h3_s1_splitOpposite k) := by
        simpa [hopp,hk,src] using hsrc (h3_s1_splitOpposite k)
      have hkd : k ≠ 8 := by
        intro he; subst k
        exact hjd (congrArg Prod.fst hk).symm
      have hkod : h3_s1_splitOpposite k ≠ 8 := by
        intro he
        have hh := congrArg Prod.fst (hopp k)
        rw [he,hk] at hh
        exact hjd hh.symm
      apply Or.inl
      apply Or.inl
      apply Or.inr
      change (supp 10 D (opA D j),supp 10 D (opB D j)) ∈ OtherSides ∨
        (supp 10 D (opB D j),supp 10 D (opA D j)) ∈ OtherSides
      rw [hka,hkb]
      exact h3_s36_split_other_sides k hkd hkod
    · apply Or.inl
      apply Or.inl
      apply Or.inl
      exact h3_nonindexed_and_equal hS r hcover hj ht (fun i hi => hex ⟨i,hi⟩)
  exact h3_r1_split_allowed_sides_exclusion hS hC hB0 (hvalid 8).1 (hvalid 8).2 hdirty hother

end DagTools

-- proof/pair36_map_facts_fragment.lean
namespace DagTools

lemma h3_s36_baseMap_prefix (e0 e1 e4 e5 d q : Nat × Bool) (i : Fin 10) :
    h3_s36_baseMap e0 e1 e4 e5 d q ⟨i.val,by omega⟩ = h3_sideMap e0 e1 e4 e5 d i := by
  fin_cases i <;> simp [h3_s36_baseMap,h3_sideMap]

lemma h3_s36_base_side_prefix (i : Fin 10) :
    S36BaseGeometry.side ⟨i.val,by omega⟩ = SideGeometry.side i := by
  fin_cases i <;> decide +kernel

lemma h3_s36_splitMap_opposite (e0 e1 e4 e5 d c : Nat × Bool) : ∀ i : Fin 12,
    h3_s36_splitMap e0 e1 e4 e5 d c (h3_s1_splitOpposite i) =
      ((h3_s36_splitMap e0 e1 e4 e5 d c i).1,!(h3_s36_splitMap e0 e1 e4 e5 d c i).2) := by
  intro i
  fin_cases i <;> simp [h3_s36_splitMap,h3_s1_splitOpposite,h3_opp]

lemma h3_s36_base_cover {D : Dag} (e0 e1 e4 e5 d q : Nat × Bool)
    (hW : ∀ x : Fin 10, sem_W 10 D x =
      (Finset.univ.filter (fun i : Fin 11 => x ∈ S36BaseGeometry.side i)).image
        (h3_s36_baseMap e0 e1 e4 e5 d q)) :
    (∀ x : Fin 10, ∀ e ∈ sem_W 10 D x,
      (∃ i : Fin 10,h3_sideMap e0 e1 e4 e5 d i = e) ∨ (x ∈ ({3,6} : Finset (Fin 10)) ∧ e = q)) ∧
    (∀ x ∈ ({3,6} : Finset (Fin 10)),q ∈ sem_W 10 D x) := by
  have hs : S36BaseGeometry.side 10 = ({3,6} : Finset (Fin 10)) := by decide +kernel
  constructor
  · intro x e he
    rw [hW] at he
    obtain ⟨i,hi,hr⟩ := Finset.mem_image.mp he
    by_cases hlt : i.val < 10
    · left
      refine ⟨⟨i.val,hlt⟩,?_⟩
      rw [←h3_s36_baseMap_prefix e0 e1 e4 e5 d q]
      convert hr using 1
    · have hi10 : i = 10 := Fin.ext (by omega)
      subst i
      right
      refine ⟨?_,?_⟩
      · simpa only [hs] using (Finset.mem_filter.mp hi).2
      · simpa [h3_s36_baseMap] using hr.symm
  · intro x hx
    rw [hW]
    apply Finset.mem_image.mpr
    refine ⟨10,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
    · simpa only [hs] using hx
    · simp [h3_s36_baseMap]

lemma h3_s36_split_cover {D : Dag} (r : Fin 12 → Nat × Bool)
    (hW : ∀ x : Fin 10,sem_W 10 D x =
      (Finset.univ.filter (fun i : Fin 12 => x ∈ S36SplitGeometry.side i)).image r) :
    ∀ x : Fin 10,∀ e ∈ sem_W 10 D x,∃ i,r i = e := by
  intro x e he
  rw [hW] at he
  obtain ⟨i,_,hr⟩ := Finset.mem_image.mp he
  exact ⟨i,hr⟩

lemma h3_s36_base_gate_valid {D : Dag} (hS : Strict 10 D) (e0 e1 e4 e5 d q : Nat × Bool)
    (hW : ∀ x : Fin 10,sem_W 10 D x =
      (Finset.univ.filter (fun i : Fin 11 => x ∈ S36BaseGeometry.side i)).image
        (h3_s36_baseMap e0 e1 e4 e5 d q)) :
    ∀ i : Fin 10,(h3_sideMap e0 e1 e4 e5 d i).1 < D.length ∧ tag D (h3_sideMap e0 e1 e4 e5 d i).1 = true := by
  have hv := h3_nonempty_incidence_gate_valid hS S36BaseGeometry.side
    (h3_s36_baseMap e0 e1 e4 e5 d q) (by decide +kernel) hW
  intro i
  simpa only [h3_s36_baseMap_prefix] using hv ⟨i.val,by omega⟩

lemma h3_s36_split_gate_valid {D : Dag} (hS : Strict 10 D) (r : Fin 12 → Nat × Bool)
    (hW : ∀ x : Fin 10,sem_W 10 D x =
      (Finset.univ.filter (fun i : Fin 12 => x ∈ S36SplitGeometry.side i)).image r) :
    ∀ i,(r i).1 < D.length ∧ tag D (r i).1 = true :=
  h3_nonempty_incidence_gate_valid hS S36SplitGeometry.side r (by decide +kernel) hW

end DagTools

-- proof/pair36_exclusion_fragment.lean
namespace DagTools

lemma h3_saturated_pair36_exclusion {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hB0 : Bzero 10 D = 0) (hone : Bplus 10 D = (eligSet 10 D).card + 1)
    (hSat : h3_saturatedSet 10 D = {3,6}) : False := by
  rcases h3_saturated_pair36_indexed_profiles h hC hz hone hSat with
    ⟨e0,e1,e4,e5,d,q,hp0,hp1,hp4,hp5,hne,hW⟩ | ⟨e0,e1,e4,e5,d,c,hp0,hp1,hp4,hp5,hne,hW⟩
  · obtain ⟨_,hfirst⟩ := h3_s36_base_first_sources h hC hz hB0 e0 e1 e4 e5 d q hp0 hp1 hp4 hp5 hne hW
    have hsrc : ∀ i : Fin 10,supp 10 D (src D (h3_sideMap e0 e1 e4 e5 d i)) = SideGeometry.side i := by
      intro i
      simpa only [h3_s36_baseMap_prefix,h3_s36_base_side_prefix] using
        hfirst ⟨i.val,by omega⟩ i.isLt
    have hcover := h3_s36_base_cover e0 e1 e4 e5 d q hW
    exact h3_canonical_shared_extra_exclusion h.1 hC hB0 (h3_sideMap e0 e1 e4 e5 d) q {3,6}
      (by decide +kernel) (h3_sideMap_opposite e0 e1 e4 e5 d) hsrc
      (h3_s36_base_gate_valid h.1 e0 e1 e4 e5 d q hW) hcover.1 hcover.2
  · have hsrc := h3_s36_split_full_sources h hC hz hB0 hone hSat e0 e1 e4 e5 d c hp0 hp1 hp4 hp5 hne hW
    exact h3_s36_split_indexed_exclusion h.1 hC hB0 (h3_s36_splitMap e0 e1 e4 e5 d c)
      (h3_s36_splitMap_opposite e0 e1 e4 e5 d c) hsrc
      (h3_s36_split_gate_valid h.1 (h3_s36_splitMap e0 e1 e4 e5 d c) hW)
      (h3_s36_split_cover (h3_s36_splitMap e0 e1 e4 e5 d c) hW)

end DagTools


namespace DagTools

def h3_fullAExposure (x y : Fin 10) : Finset (Fin 10) :=
  SideGeometry.mask (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 8, 144, 40, 72, 128, 384, 520, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 68, 8, 80, 40, 64, 136, 0, 520, 0, 130, 68, 72, 80, 96, 64, 128, 384, 0] : List Nat).getD (10*x.val+y.val) 0)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma h3_fullAExposure_spec : ∀ x ∈ ({2,8,9} : Finset (Fin 10)), ∀ y : Fin 10,
    y ≠ 0 → y ≠ x →
    (∀ a ∈ h3_fullAExposure x y, ∀ b ∈ h3_fullAExposure x y, ¬ petersenAdj a b) ∧
    y ∈ h3_fullAExposure x y ∧
    (∃ a ∈ h3_fullAExposure x y, a ∈ ({3,6,7} : Finset (Fin 10))) ∧
    ∃ a ∈ h3_fullAExposure x y, petersenAdj x a := by
  unfold h3_fullAExposure SideGeometry.mask petersenAdj
  decide +kernel

lemma h3_fullA_other_exit_pure {D : Dag} (hS : Strict 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    {x : Fin 10} (hx : x ∈ ({2,8,9} : Finset (Fin 10))) {e f : Nat × Bool}
    (hW : exitArcs 10 D (carrierT 10 D {x}) ⊆ {e,f})
    (hf : f ∈ exitArcs 10 D (carrierT 10 D {x}))
    (hSub : ({3,6,7} : Finset (Fin 10)) ⊆ supp 10 D (src D e)) :
    supp 10 D (src D f) = {x} := by
  have hx0 : x ≠ 0 := by intro he; subst x; simp at hx
  apply sem_two_exit_other_pure petersen_graph_ok hS hC hx0 hz hW hf hSub
  intro y hy0 hyx
  exact ⟨h3_fullAExposure x y, h3_fullAExposure_spec x hx y hy0 hyx⟩

lemma h3_opposite_pure_ne {n : Nat} {D : Dag} {e f : Nat × Bool} {a b : Fin n}
    (he : supp n D (src D (h3_opp e)) = {a})
    (hf : supp n D (src D (h3_opp f)) = {b}) (hab : a ≠ b) : e ≠ f := by
  intro hh
  subst f
  exact hab (Finset.singleton_injective (he.symm.trans hf))

lemma h3_card_three_eq {α : Type*} [DecidableEq α] {W : Finset α} {a b c : α}
    (hc : W.card = 3) (ha : a ∈ W) (hb : b ∈ W) (hc' : c ∈ W)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : W = {a,b,c} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl <;> assumption
  · rw [hc]
    simp [hab,hac,hbc]

lemma h3_three_pure_opposites_no_edge {n : Nat} {D : Dag} {G : Fin n → Fin n → Prop}
    (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {x y a b c : Fin n} {e f g : Nat × Bool}
    (hW : exitArcs n D (carrierT n D {x}) ⊆ {e,f,g})
    (he : supp n D (src D (h3_opp e)) = {a})
    (hf : supp n D (src D (h3_opp f)) = {b})
    (hg : supp n D (src D (h3_opp g)) = {c})
    (hxy : G x y) (hya : y ≠ a) (hyb : y ≠ b) (hyc : y ≠ c) : False := by
  obtain ⟨j,hj,_,_,hxn,_,s,hxs,_,hys,_⟩ := sem_joint_meeting hG hS hC hxy
  have hm := hW (sem_mem_exit1.mpr ⟨hj,hxs,hxn⟩)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with hh | hh | hh
  · have hy : y ∈ supp n D (src D (h3_opp e)) := by simpa [← hh,h3_opp] using hys
    exact hya (Finset.mem_singleton.mp (he ▸ hy))
  · have hy : y ∈ supp n D (src D (h3_opp f)) := by simpa [← hh,h3_opp] using hys
    exact hyb (Finset.mem_singleton.mp (hf ▸ hy))
  · have hy : y ∈ supp n D (src D (h3_opp g)) := by simpa [← hh,h3_opp] using hys
    exact hyc (Finset.mem_singleton.mp (hg ▸ hy))

lemma h3_fullA_private_obstruction {D : Dag} (hS : Strict 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    {z a p u t : Fin 10} {P f K : Nat × Bool}
    (hzB : z ∈ ({2,8,9} : Finset (Fin 10)))
    (hWz : exitArcs 10 D (carrierT 10 D {z}) ⊆ {P,f})
    (hf : f ∈ exitArcs 10 D (carrierT 10 D {z}))
    (hP : supp 10 D (src D (h3_opp P)) = {p})
    (hK : supp 10 D (src D (h3_opp K)) = {u})
    (hSub : ({3,6,7} : Finset (Fin 10)) ⊆ supp 10 D (src D P))
    (hPa : P ∈ exitArcs 10 D (carrierT 10 D {a}))
    (hKa : K ∈ exitArcs 10 D (carrierT 10 D {a}))
    (hca : (exitArcs 10 D (carrierT 10 D {a})).card = 3)
    (hza : petersenAdj z a) (hap : a ≠ p)
    (hup : u ≠ p) (huz : u ≠ z) (hpz : p ≠ z)
    (hat : petersenAdj a t) (htu : t ≠ u) (htp : t ≠ p) (htz : t ≠ z) : False := by
  have hfp := h3_fullA_other_exit_pure hS hC hz hzB hWz hf hSub
  have hfa : h3_opp f ∈ exitArcs 10 D (carrierT 10 D {a}) :=
    sem_two_exit_remaining_slot petersen_graph_ok hS hC hWz hP hza hap
  have hff : supp 10 D (src D (h3_opp (h3_opp f))) = {z} := by
    rw [h3_opp_opp]
    exact hfp
  have hWa := h3_card_three_eq hca hKa hPa hfa
    (h3_opposite_pure_ne hK hP hup) (h3_opposite_pure_ne hK hff huz)
    (h3_opposite_pure_ne hP hff hpz)
  exact h3_three_pure_opposites_no_edge petersen_graph_ok hS hC
    (by rw [hWa]) hK hP hff hat htu htp htz

end DagTools

namespace DagTools

lemma h3_opposite_choice_of_private {n : Nat} {D : Dag} {z u : Fin n}
    {b K P Q : Nat × Bool} (hz : z ∈ supp n D (src D b))
    (hK : supp n D (src D (h3_opp K)) = {u}) (hzu : z ≠ u)
    (he : h3_opp b ∈ ({K,P,Q} : Finset (Nat × Bool))) :
    b = h3_opp P ∨ b = h3_opp Q := by
  simp only [Finset.mem_insert,Finset.mem_singleton] at he
  rcases he with he | he | he
  · have hh : supp n D (src D b) = {u} := by
      simpa only [← he,h3_opp_opp] using hK
    exact False.elim (hzu (Finset.mem_singleton.mp (hh ▸ hz)))
  · left
    simpa only [h3_opp_opp] using (congrArg h3_opp he)
  · right
    simpa only [h3_opp_opp] using (congrArg h3_opp he)

lemma h3_saturated_fullA_exit_pattern {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hB0 : Bzero 10 D = 0) (hone : Bplus 10 D = (eligSet 10 D).card + 1)
    (hSat : h3_saturatedSet 10 D = {3,6,7}) :
    ∃ e0 e1 e4 e5 P Q b2 b8 b9 : Nat × Bool,
      supp 10 D (src D e0) = {0} ∧ supp 10 D (src D e1) = {1} ∧
      supp 10 D (src D e4) = {4} ∧ supp 10 D (src D e5) = {5} ∧
      supp 10 D (src D (h3_opp e0)) = {1,4,5} ∧
      exitArcs 10 D (carrierT 10 D {0}) = {e0} ∧
      exitArcs 10 D (carrierT 10 D {1}) = {h3_opp e0,e1} ∧
      exitArcs 10 D (carrierT 10 D {4}) = {h3_opp e0,e4} ∧
      exitArcs 10 D (carrierT 10 D {5}) = {h3_opp e0,e5} ∧
      exitArcs 10 D (carrierT 10 D {3}) = {h3_opp e4,P,Q} ∧
      exitArcs 10 D (carrierT 10 D {6}) = {h3_opp e1,P,Q} ∧
      exitArcs 10 D (carrierT 10 D {7}) = {h3_opp e5,P,Q} ∧
      exitArcs 10 D (carrierT 10 D {2}) = {h3_opp e1,b2} ∧
      exitArcs 10 D (carrierT 10 D {8}) = {h3_opp e5,b8} ∧
      exitArcs 10 D (carrierT 10 D {9}) = {h3_opp e4,b9} ∧
      P.1 ≠ Q.1 ∧
      (b2 = h3_opp P ∨ b2 = h3_opp Q) ∧
      (b8 = h3_opp P ∨ b8 = h3_opp Q) ∧
      (b9 = h3_opp P ∨ b9 = h3_opp Q) := by
  have hfin : ∀ x ∈ ({1,4,5} : Finset (Fin 10)), x ∉ ({3,6,7} : Finset (Fin 10)) := by decide
  have hlo := h3_outside_le_two_nonzero_ge_two h hC hz
    (fun x hx => h3_outside_saturated_le_two hSat (hfin x hx))
  have hc (x : Fin 10) (hx0 : x ≠ 0) (hxA : x ∉ ({3,6,7} : Finset (Fin 10))) :
      (exitArcs 10 D (carrierT 10 D {x})).card = 2 :=
    Nat.le_antisymm (h3_outside_saturated_le_two hSat hxA) (hlo x hx0)
  have hca (x : Fin 10) (hx : x ∈ ({3,6,7} : Finset (Fin 10))) :
      (exitArcs 10 D (carrierT 10 D {x})).card = 3 :=
    (h3_one_residual_saturation petersen_graph_ok h hC hone x (hSat ▸ hx)).1
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
  obtain ⟨e1, _, hW1⟩ := h3_pair_of_card_two (hAmem 1 (by decide)) (hc 1 (by decide) (by decide))
  obtain ⟨e4, _, hW4⟩ := h3_pair_of_card_two (hAmem 4 (by decide)) (hc 4 (by decide) (by decide))
  obtain ⟨e5, _, hW5⟩ := h3_pair_of_card_two (hAmem 5 (by decide)) (hc 5 (by decide) (by decide))
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
  obtain ⟨b2,_,hW2⟩ := h3_pair_of_card_two ha2 (hc 2 (by decide) (by decide))
  obtain ⟨b8,_,hW8⟩ := h3_pair_of_card_two ha8 (hc 8 (by decide) (by decide))
  obtain ⟨b9,_,hW9⟩ := h3_pair_of_card_two ha9 (hc 9 (by decide) (by decide))
  have hb1 : supp 10 D (src D (h3_opp (h3_opp e1))) = {1} := by rw [h3_opp_opp]; exact hp1
  have hb4 : supp 10 D (src D (h3_opp (h3_opp e4))) = {4} := by rw [h3_opp_opp]; exact hp4
  have hb5 : supp 10 D (src D (h3_opp (h3_opp e5))) = {5} := by rw [h3_opp_opp]; exact hp5
  have hstar := h3_star0_exact_of_two_exit_pure_companion h hC hz hB0 A e4 hW4 hp4 hAN
  obtain ⟨P,Q,hPQ,hterm⟩ := h3_one_residual_common_terminals petersen_graph_ok h hC hone
  have hterms (x : Fin 10) (hx : x ∈ ({3,6,7} : Finset (Fin 10))) :
      P ∈ exitArcs 10 D (carrierT 10 D {x}) ∧ Q ∈ exitArcs 10 D (carrierT 10 D {x}) :=
    hterm x (hSat ▸ hx)
  have hnot (R : Nat × Bool)
      (hR : ∀ x ∈ ({3,6,7} : Finset (Fin 10)), R ∈ exitArcs 10 D (carrierT 10 D {x})) :
      R ≠ h3_opp e1 ∧ R ≠ h3_opp e4 ∧ R ≠ h3_opp e5 := by
    have hSub : ({3,6,7} : Finset (Fin 10)) ⊆ supp 10 D (src D R) :=
      fun x hx => (sem_mem_exit1.mp (hR x hx)).2.1
    refine ⟨?_,?_,?_⟩
    · intro he
      subst R
      apply h3_fullA_private_obstruction h.1 hC hz (z := 2) (a := 3) (p := 1) (u := 4) (t := 8)
        (by decide) (by rw [hW2]) (by rw [hW2]; simp) hb1 hb4 hSub
        (hR 3 (by decide)) ha3 (hca 3 (by decide))
        <;> (first | unfold petersenAdj; decide | decide)
    · intro he
      subst R
      apply h3_fullA_private_obstruction h.1 hC hz (z := 9) (a := 6) (p := 4) (u := 1) (t := 8)
        (by decide) (by rw [hW9]) (by rw [hW9]; simp) hb4 hb1 hSub
        (hR 6 (by decide)) ha6 (hca 6 (by decide))
        <;> (first | unfold petersenAdj; decide | decide)
    · intro he
      subst R
      apply h3_fullA_private_obstruction h.1 hC hz (z := 8) (a := 3) (p := 5) (u := 4) (t := 2)
        (by decide) (by rw [hW8]) (by rw [hW8]; simp) hb5 hb4 hSub
        (hR 3 (by decide)) ha3 (hca 3 (by decide))
        <;> (first | unfold petersenAdj; decide | decide)
  have hnotP := hnot P (fun x hx => (hterms x hx).1)
  have hnotQ := hnot Q (fun x hx => (hterms x hx).2)
  have hPQ' : P ≠ Q := fun he => hPQ (congrArg Prod.fst he)
  have hW3 := h3_card_three_eq (hca 3 (by decide)) ha3 (hterms 3 (by decide)).1 (hterms 3 (by decide)).2
    (Ne.symm hnotP.2.1) (Ne.symm hnotQ.2.1) hPQ'
  have hW6 := h3_card_three_eq (hca 6 (by decide)) ha6 (hterms 6 (by decide)).1 (hterms 6 (by decide)).2
    (Ne.symm hnotP.1) (Ne.symm hnotQ.1) hPQ'
  have hW7 := h3_card_three_eq (hca 7 (by decide)) ha7 (hterms 7 (by decide)).1 (hterms 7 (by decide)).2
    (Ne.symm hnotP.2.2) (Ne.symm hnotQ.2.2) hPQ'
  have hchoice2 : b2 = h3_opp P ∨ b2 = h3_opp Q := by
    have hb2 := sem_two_exit_remaining_slot petersen_graph_ok h.1 hC (by rw [hW2]) hb1
      (by unfold petersenAdj; decide : petersenAdj 2 3) (by decide : (3 : Fin 10) ≠ 1)
    apply h3_opposite_choice_of_private (u := 4)
      ((sem_mem_exit1.mp (show b2 ∈ exitArcs 10 D (carrierT 10 D {(2 : Fin 10)}) by rw [hW2]; simp)).2.1)
      hb4 (by decide)
    simpa only [hW3,h3_opp] using hb2
  have hchoice8 : b8 = h3_opp P ∨ b8 = h3_opp Q := by
    have hb8 := sem_two_exit_remaining_slot petersen_graph_ok h.1 hC (by rw [hW8]) hb5
      (by unfold petersenAdj; decide : petersenAdj 8 3) (by decide : (3 : Fin 10) ≠ 5)
    apply h3_opposite_choice_of_private (u := 4)
      ((sem_mem_exit1.mp (show b8 ∈ exitArcs 10 D (carrierT 10 D {(8 : Fin 10)}) by rw [hW8]; simp)).2.1)
      hb4 (by decide)
    simpa only [hW3,h3_opp] using hb8
  have hchoice9 : b9 = h3_opp P ∨ b9 = h3_opp Q := by
    have hb9 := sem_two_exit_remaining_slot petersen_graph_ok h.1 hC (by rw [hW9]) hb4
      (by unfold petersenAdj; decide : petersenAdj 9 6) (by decide : (6 : Fin 10) ≠ 4)
    apply h3_opposite_choice_of_private (u := 1)
      ((sem_mem_exit1.mp (show b9 ∈ exitArcs 10 D (carrierT 10 D {(9 : Fin 10)}) by rw [hW9]; simp)).2.1)
      hb1 (by decide)
    simpa only [hW6,h3_opp] using hb9
  exact ⟨e0,e1,e4,e5,P,Q,b2,b8,b9,hp0,hp1,hp4,hp5,hstar,hW0,hW1,hW4,hW5,
    hW3,hW6,hW7,hW2,hW8,hW9,hPQ,hchoice2,hchoice8,hchoice9⟩

end DagTools

namespace DagTools

lemma h3_exit_opposite_not_mem {n : Nat} {D : Dag} (hS : Strict n D)
    {x : Fin n} {e : Nat × Bool} (he : e ∈ exitArcs n D (carrierT n D {x})) :
    x ∉ supp n D (src D (h3_opp e)) := by
  intro hf
  obtain ⟨j,s⟩ := e
  obtain ⟨hj,hx,hn⟩ := sem_mem_exit1.mp he
  apply hn
  rw [sem_supp_and hS hj (h3_exit_tag_and hS he)]
  cases s
  · exact Finset.mem_inter.mpr ⟨hx,hf⟩
  · exact Finset.mem_inter.mpr ⟨hf,hx⟩

lemma h3_saturated_fullA_no_merges {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hB0 : Bzero 10 D = 0) (hone : Bplus 10 D = (eligSet 10 D).card + 1)
    (hSat : h3_saturatedSet 10 D = {3,6,7}) :
    ∀ x : Fin 10, merges 10 D (carrierT 10 D {x}) = ∅ := by
  obtain ⟨e0,e1,e4,e5,P,Q,b2,b8,b9,hp0,hp1,hp4,hp5,hstar,hW0,hW1,hW4,hW5,
    hW3,hW6,hW7,hW2,hW8,hW9,hPQ,hchoice2,hchoice8,hchoice9⟩ :=
    h3_saturated_fullA_exit_pattern h hC hz hB0 hone hSat
  obtain ⟨b,hb⟩ := sem_exists_minBranch petersen_graph_ok h.1 hC
  have hbp := sem_minBranch_pure hb
  have hsat : ∀ x ∈ ({3,6,7} : Finset (Fin 10)), 3 ≤ (sem_W 10 D x).card := by
    intro x hx
    have hm : x ∈ h3_saturatedSet 10 D := hSat ▸ hx
    exact (Finset.mem_filter.mp hm).2
  obtain ⟨u0,P',Q',hres,hPQ',hterms,hpathP,hpathQ,hsub⟩ :=
    h3_common_terminals_actual_paths petersen_graph_ok h hC b hb hone {3,6,7}
      (by decide) hsat
  have h36 : h3_opp e4 ≠ h3_opp e1 := by
    apply h3_opposite_pure_ne (a := (4 : Fin 10)) (b := 1)
    · simpa only [h3_opp_opp] using hp4
    · simpa only [h3_opp_opp] using hp1
    · decide
  have hcommon (R : Nat × Bool)
      (hR3 : R ∈ sem_W 10 D 3) (hR6 : R ∈ sem_W 10 D 6) : R = P ∨ R = Q := by
    change R ∈ exitArcs 10 D (carrierT 10 D {(3 : Fin 10)}) at hR3
    change R ∈ exitArcs 10 D (carrierT 10 D {(6 : Fin 10)}) at hR6
    rw [hW3] at hR3
    rw [hW6] at hR6
    simp only [Finset.mem_insert,Finset.mem_singleton] at hR3 hR6
    rcases hR3 with he | he
    · rcases hR6 with hf | hf
      · exact False.elim (h36 (he.symm.trans hf))
      · exact hf
    · exact he
  have hPchoice := hcommon P' (hterms 3 (by decide)).1 (hterms 6 (by decide)).1
  have hQchoice := hcommon Q' (hterms 3 (by decide)).2 (hterms 6 (by decide)).2
  have hsubPQ : supp 10 D u0.1 ⊆ supp 10 D (src D P) ∩ supp 10 D (src D Q) := by
    rcases hPchoice with hp | hp <;> rcases hQchoice with hq | hq
    · exact False.elim (hPQ' (by rw [hp,hq]))
    · simpa only [hp,hq] using hsub
    · simpa only [hp,hq,Finset.inter_comm] using hsub
    · exact False.elim (hPQ' (by rw [hp,hq]))
  have hAres : ({3,6,7} : Finset (Fin 10)) ⊆ supp 10 D u0.1 := by
    intro x hx
    exact (sem_saturated petersen_graph_ok h hC b hbp hres (hsat x hx)).2.2.2
  have hzero : (0 : Fin 10) ∉ supp 10 D u0.1 := by
    intro hx
    have hu : u0 ∈ residualUnits 10 D b := by rw [hres]; simp
    exact (sem_mem_inelig.mp hz) (H3ResidualLocalization.residual_support_eligible hu hx)
  have hNzero : ∀ x ∈ ({1,4,5} : Finset (Fin 10)), x ∉ supp 10 D u0.1 := by
    intro x hx hxr
    have hn := h3_single_residual_support_subset_of_bzero h hC b hbp hB0 hz hres ⟨x,hx,hxr⟩
    exact (by decide : (3 : Fin 10) ∉ ({1,4,5} : Finset (Fin 10))) (hn (hAres (by decide)))
  have hBzero (x : Fin 10) (e : Nat × Bool)
      (he : e ∈ exitArcs 10 D (carrierT 10 D {x}))
      (heq : e = h3_opp P ∨ e = h3_opp Q) : x ∉ supp 10 D u0.1 := by
    intro hx
    have hh := hsubPQ hx
    apply h3_exit_opposite_not_mem h.1 he
    rcases heq with heq | heq
    · simpa only [heq,h3_opp_opp] using (Finset.mem_inter.mp hh).1
    · simpa only [heq,h3_opp_opp] using (Finset.mem_inter.mp hh).2
  have h2zero := hBzero 2 b2 (by rw [hW2]; simp) hchoice2
  have h8zero := hBzero 8 b8 (by rw [hW8]; simp) hchoice8
  have h9zero := hBzero 9 b9 (by rw [hW9]; simp) hchoice9
  have hresExact : supp 10 D u0.1 = ({3,6,7} : Finset (Fin 10)) := by
    apply Finset.Subset.antisymm ?_ hAres
    intro x hx
    fin_cases x
    · exact False.elim (hzero hx)
    · exact False.elim (hNzero 1 (by decide) hx)
    · exact False.elim (h2zero hx)
    · decide
    · exact False.elim (hNzero 4 (by decide) hx)
    · exact False.elim (hNzero 5 (by decide) hx)
    · decide
    · decide
    · exact False.elim (h8zero hx)
    · exact False.elim (h9zero hx)
  have hfin : ∀ x ∈ ({1,4,5} : Finset (Fin 10)), x ∉ ({3,6,7} : Finset (Fin 10)) := by decide
  have hlo := h3_outside_le_two_nonzero_ge_two h hC hz
    (fun x hx => h3_outside_saturated_le_two hSat (hfin x hx))
  intro x
  by_cases hxA : x ∈ ({3,6,7} : Finset (Fin 10))
  · exact (h3_one_residual_saturation petersen_graph_ok h hC hone x (hSat ▸ hxA)).2.1
  · have hf := h3_residual_singleton_flow petersen_graph_ok h hC b hbp u0 hres x
    rw [hresExact,ite_eq_right hxA] at hf
    by_cases hx0 : x = 0
    · subst x
      have hze : (0 : Fin 10) ∉ eligSet 10 D := sem_mem_inelig.mp hz
      rw [ite_eq_right hze,hW0,Finset.card_singleton] at hf
      exact Finset.card_eq_zero.mp (by omega)
    · have hc := hlo x hx0
      split_ifs at hf <;> exact Finset.card_eq_zero.mp (by omega)

lemma h3_saturated_fullA_and_empty {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hB0 : Bzero 10 D = 0) (hone : Bplus 10 D = (eligSet 10 D).card + 1)
    (hSat : h3_saturatedSet 10 D = {3,6,7}) {j : Nat}
    (hj : j < D.length) (ht : tag D j = true) : supp 10 D (10+j) = ∅ := by
  rw [sem_supp_and h.1 hj ht]
  exact Finset.disjoint_iff_inter_eq_empty.mp
    (h3_no_merges_inputs_disjoint h.1 (h3_saturated_fullA_no_merges h hC hz hB0 hone hSat) hj)

end DagTools

namespace DagTools

lemma h3_three_card_ne {α : Type*} [DecidableEq α] {a b c : α}
    (hc : ({a,b,c} : Finset α).card = 3) : a ≠ b ∧ a ≠ c := by
  have hp (x y : α) : ({x,y} : Finset α).card ≤ 2 :=
    Finset.card_le_two
  constructor
  · intro he
    subst b
    have hh := hp a c
    simp only [Finset.insert_eq_of_mem (Finset.mem_insert_self a {c})] at hc
    omega
  · intro he
    subst c
    have hh := hp a b
    have heq : ({a,b,a} : Finset α) = {a,b} := by ext x; simp; tauto
    rw [heq] at hc
    omega

lemma h3_pure_private_gates_injective {n : Nat} {D : Dag} {ι : Type*}
    (e : ι → Nat × Bool) (v : ι → Fin n) (hv : Function.Injective v)
    (hp : ∀ i, supp n D (src D (e i)) = {v i})
    (hm : ∀ i, ∃ x y : Fin n, x ∈ supp n D (src D (h3_opp (e i))) ∧
      y ∈ supp n D (src D (h3_opp (e i))) ∧ x ≠ y) :
    Function.Injective (fun i => (e i).1) := by
  intro i j hij
  have hs : e j = e i ∨ e j = h3_opp (e i) := by
    simpa only [sem_bar,h3_opp] using (sem_same_gate hij)
  rcases hs with hs | hs
  · apply hv
    apply Finset.singleton_injective
    rw [← hp i,← hp j,hs]
  · obtain ⟨x,y,hx,hy,hxy⟩ := hm i
    rw [← hs,hp j,Finset.mem_singleton] at hx hy
    exact False.elim (hxy (hx.trans hy.symm))

def h3_pairedArcs {ι : Type*} (c : ι → Nat × Bool) (i : ι × Bool) : Nat × Bool :=
  if i.2 then h3_opp (c i.1) else c i.1

lemma h3_pairedArcs_fst {ι : Type*} (c : ι → Nat × Bool) (i : ι × Bool) :
    (h3_pairedArcs c i).1 = (c i.1).1 := by
  rcases i with ⟨i,s⟩
  cases s <;> rfl

lemma h3_pairedArcs_injective {ι : Type*} (c : ι → Nat × Bool)
    (hc : Function.Injective (fun i => (c i).1)) : Function.Injective (h3_pairedArcs c) := by
  rintro ⟨i,s⟩ ⟨j,t⟩ hij
  have hfst := congrArg Prod.fst hij
  rw [h3_pairedArcs_fst,h3_pairedArcs_fst] at hfst
  have he : i = j := hc hfst
  subst j
  cases s <;> cases t
  · rfl
  · have hbad := congrArg Prod.snd hij
    simp [h3_pairedArcs,h3_opp] at hbad
  · have hbad := congrArg Prod.snd hij
    simp [h3_pairedArcs,h3_opp] at hbad
  · rfl

lemma h3_empty_indexed_sources_exact {n : Nat} {D : Dag} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (r : ι → Nat × Bool) (S : ι → Finset (Fin n))
    (hinj : Function.Injective r)
    (hW : ∀ x : Fin n, exitArcs n D (carrierT n D {x}) =
      (Finset.univ.filter (fun i => x ∈ S i)).image r)
    (hvalid : ∀ i, (r i).1 < D.length ∧ supp n D (n+(r i).1) = ∅) :
    ∀ i, supp n D (src D (r i)) = S i := by
  intro i
  ext x
  constructor
  · intro hx
    have he : r i ∈ exitArcs n D (carrierT n D {x}) :=
      sem_mem_exit1.mpr ⟨(hvalid i).1,hx,by rw [(hvalid i).2]; simp⟩
    rw [hW] at he
    obtain ⟨j,hj,hji⟩ := Finset.mem_image.mp he
    have hji' := hinj hji
    simpa only [hji'] using (Finset.mem_filter.mp hj).2
  · intro hx
    apply (sem_mem_exit1.mp ?_).2.1
    rw [hW]
    exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hx⟩,rfl⟩

end DagTools

namespace DagTools

def h3_fullA_part (b2 b8 b9 : Bool) : Finset (Fin 10) :=
  (if b2 then {2} else ∅) ∪ (if b8 then {8} else ∅) ∪ (if b9 then {9} else ∅)

def h3_fullA_side (b2 b8 b9 : Bool) (i : Fin 6 × Bool) : Finset (Fin 10) :=
  match i.1.val with
  | 0 => if i.2 then {1,4,5} else {0}
  | 1 => if i.2 then {2,6} else {1}
  | 2 => if i.2 then {3,9} else {4}
  | 3 => if i.2 then {7,8} else {5}
  | 4 => if i.2 then h3_fullA_part b2 b8 b9 else {3,6,7}
  | _ => if i.2 then {2,8,9} \ h3_fullA_part b2 b8 b9 else {3,6,7}

def h3_fullA_incidence (b2 b8 b9 : Bool) (x : Fin 10) : Finset (Fin 6 × Bool) :=
  match x.val with
  | 0 => {(0,false)}
  | 1 => {(0,true),(1,false)}
  | 2 => {(1,true),(if b2 then 4 else 5,true)}
  | 3 => {(2,true),(4,false),(5,false)}
  | 4 => {(0,true),(2,false)}
  | 5 => {(0,true),(3,false)}
  | 6 => {(1,true),(4,false),(5,false)}
  | 7 => {(3,true),(4,false),(5,false)}
  | 8 => {(3,true),(if b8 then 4 else 5,true)}
  | _ => {(2,true),(if b9 then 4 else 5,true)}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma h3_fullA_incidence_eq : ∀ b2 b8 b9 : Bool, ∀ x : Fin 10,
    Finset.univ.filter (fun i : Fin 6 × Bool => x ∈ h3_fullA_side b2 b8 b9 i) =
      h3_fullA_incidence b2 b8 b9 x := by
  decide +kernel

lemma h3_fullA_part_subset (b2 b8 b9 : Bool) : h3_fullA_part b2 b8 b9 ⊆ ({2,8,9} : Finset (Fin 10)) := by
  cases b2 <;> cases b8 <;> cases b9 <;> decide

end DagTools

namespace DagTools

set_option maxHeartbeats 3000000 in
lemma h3_saturated_fullA_sources_exist {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hB0 : Bzero 10 D = 0) (hone : Bplus 10 D = (eligSet 10 D).card + 1)
    (hSat : h3_saturatedSet 10 D = {3,6,7}) :
    ∃ β2 β8 β9 : Bool, ∃ c : Fin 6 → Nat × Bool,
      Function.Injective (fun i => (c i).1) ∧
      (∀ i, (c i).1 < D.length ∧ tag D (c i).1 = true) ∧
      (∀ i : Fin 6 × Bool, supp 10 D (src D (h3_pairedArcs c i)) = h3_fullA_side β2 β8 β9 i) ∧
      (∀ j, j < D.length → tag D j = true → (∀ i, (c i).1 ≠ j) →
        supp 10 D (opA D j) = ∅ ∧ supp 10 D (opB D j) = ∅) := by
  obtain ⟨e0,e1,e4,e5,P,Q,b2,b8,b9,hp0,hp1,hp4,hp5,hstar,hW0,hW1,hW4,hW5,
    hW3,hW6,hW7,hW2,hW8,hW9,hPQ,hchoice2,hchoice8,hchoice9⟩ :=
    h3_saturated_fullA_exit_pattern h hC hz hB0 hone hSat
  have hca (x : Fin 10) (hx : x ∈ ({3,6,7} : Finset (Fin 10))) :
      (exitArcs 10 D (carrierT 10 D {x})).card = 3 :=
    (h3_one_residual_saturation petersen_graph_ok h hC hone x (hSat ▸ hx)).1
  have h3ne := h3_three_card_ne (hW3 ▸ hca 3 (by decide))
  have h6ne := h3_three_card_ne (hW6 ▸ hca 6 (by decide))
  have h7ne := h3_three_card_ne (hW7 ▸ hca 7 (by decide))
  let e : Fin 4 → Nat × Bool := fun i => ([e0,e1,e4,e5] : List (Nat × Bool)).getD i.val e0
  let v : Fin 4 → Fin 10 := fun i => ([0,1,4,5] : List (Fin 10)).getD i.val 0
  have hvinj : Function.Injective v := by decide +kernel
  have hp : ∀ i, supp 10 D (src D (e i)) = {v i} := by
    intro i; fin_cases i
    · exact hp0
    · exact hp1
    · exact hp4
    · exact hp5
  have hm : ∀ i, ∃ x y : Fin 10, x ∈ supp 10 D (src D (h3_opp (e i))) ∧
      y ∈ supp 10 D (src D (h3_opp (e i))) ∧ x ≠ y := by
    intro i; fin_cases i
    · exact ⟨1,4,by simp [e,hstar],by simp [e,hstar],by decide⟩
    · exact ⟨2,6,(sem_mem_exit1.mp (by rw [hW2]; simp [e])).2.1,
        (sem_mem_exit1.mp (by rw [hW6]; simp [e])).2.1,by decide⟩
    · exact ⟨3,9,(sem_mem_exit1.mp (by rw [hW3]; simp [e])).2.1,
        (sem_mem_exit1.mp (by rw [hW9]; simp [e])).2.1,by decide⟩
    · exact ⟨7,8,(sem_mem_exit1.mp (by rw [hW7]; simp [e])).2.1,
        (sem_mem_exit1.mp (by rw [hW8]; simp [e])).2.1,by decide⟩
  have hpriv := h3_pure_private_gates_injective e v hvinj hp hm
  have hRsource (R : Nat × Bool) (hR : R = P ∨ R = Q) : (3 : Fin 10) ∈ supp 10 D (src D R) := by
    apply (sem_mem_exit1.mp ?_).2.1
    rw [hW3]
    rcases hR with rfl | rfl <;> simp
  have hRnot (R : Nat × Bool) (hR : R = P ∨ R = Q) : ∀ i, R ≠ h3_opp (e i) := by
    intro i
    fin_cases i
    · intro he
      have hh := hRsource R hR
      rw [he] at hh
      change (3 : Fin 10) ∈ supp 10 D (src D (h3_opp e0)) at hh
      rw [hstar] at hh
      exact (by decide : (3 : Fin 10) ∉ ({1,4,5} : Finset (Fin 10))) hh
    · rcases hR with rfl | rfl
      · exact Ne.symm h6ne.1
      · exact Ne.symm h6ne.2
    · rcases hR with rfl | rfl
      · exact Ne.symm h3ne.1
      · exact Ne.symm h3ne.2
    · rcases hR with rfl | rfl
      · exact Ne.symm h7ne.1
      · exact Ne.symm h7ne.2
  have hRgate (R : Nat × Bool) (hR : R = P ∨ R = Q) : ∀ i, (e i).1 ≠ R.1 := by
    intro i hi
    have he : R = e i ∨ R = h3_opp (e i) := by
      simpa only [sem_bar,h3_opp] using sem_same_gate hi
    rcases he with he | he
    · have hh := hRsource R hR
      rw [he,hp i,Finset.mem_singleton] at hh
      have hn : ∀ i : Fin 4, (3 : Fin 10) ≠ v i := by decide +kernel
      exact hn i hh
    · exact hRnot R hR i he
  have h0P := hRgate P (Or.inl rfl) 0
  have h1P := hRgate P (Or.inl rfl) 1
  have h4P := hRgate P (Or.inl rfl) 2
  have h5P := hRgate P (Or.inl rfl) 3
  have h0Q := hRgate Q (Or.inr rfl) 0
  have h1Q := hRgate Q (Or.inr rfl) 1
  have h4Q := hRgate Q (Or.inr rfl) 2
  have h5Q := hRgate Q (Or.inr rfl) 3
  have h01 : e0.1 ≠ e1.1 := fun hh => (by decide : (0 : Fin 4) ≠ 1) (hpriv hh)
  have h04 : e0.1 ≠ e4.1 := fun hh => (by decide : (0 : Fin 4) ≠ 2) (hpriv hh)
  have h05 : e0.1 ≠ e5.1 := fun hh => (by decide : (0 : Fin 4) ≠ 3) (hpriv hh)
  have h14 : e1.1 ≠ e4.1 := fun hh => (by decide : (1 : Fin 4) ≠ 2) (hpriv hh)
  have h15 : e1.1 ≠ e5.1 := fun hh => (by decide : (1 : Fin 4) ≠ 3) (hpriv hh)
  have h45 : e4.1 ≠ e5.1 := fun hh => (by decide : (2 : Fin 4) ≠ 3) (hpriv hh)
  let c : Fin 6 → Nat × Bool := fun i => ([e0,e1,e4,e5,P,Q] : List (Nat × Bool)).getD i.val e0
  have hginj : Function.Injective (fun i => (c i).1) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [c,e]
  obtain ⟨β2,hβ2⟩ : ∃ β : Bool, b2 = if β then h3_opp P else h3_opp Q := by
    rcases hchoice2 with hh | hh
    · exact ⟨true,hh⟩
    · exact ⟨false,hh⟩
  obtain ⟨β8,hβ8⟩ : ∃ β : Bool, b8 = if β then h3_opp P else h3_opp Q := by
    rcases hchoice8 with hh | hh
    · exact ⟨true,hh⟩
    · exact ⟨false,hh⟩
  obtain ⟨β9,hβ9⟩ : ∃ β : Bool, b9 = if β then h3_opp P else h3_opp Q := by
    rcases hchoice9 with hh | hh
    · exact ⟨true,hh⟩
    · exact ⟨false,hh⟩
  have hW : ∀ x : Fin 10, exitArcs 10 D (carrierT 10 D {x}) =
      (Finset.univ.filter (fun i : Fin 6 × Bool => x ∈ h3_fullA_side β2 β8 β9 i)).image (h3_pairedArcs c) := by
    intro x
    rw [h3_fullA_incidence_eq]
    fin_cases x
    · simpa [h3_fullA_incidence,h3_pairedArcs,c] using hW0
    · simpa [h3_fullA_incidence,h3_pairedArcs,c] using hW1
    · cases β2 <;> simpa [h3_fullA_incidence,h3_pairedArcs,c,hβ2] using hW2
    · simpa [h3_fullA_incidence,h3_pairedArcs,c] using hW3
    · simpa [h3_fullA_incidence,h3_pairedArcs,c] using hW4
    · simpa [h3_fullA_incidence,h3_pairedArcs,c] using hW5
    · simpa [h3_fullA_incidence,h3_pairedArcs,c] using hW6
    · simpa [h3_fullA_incidence,h3_pairedArcs,c] using hW7
    · cases β8 <;> simpa [h3_fullA_incidence,h3_pairedArcs,c,hβ8] using hW8
    · cases β9 <;> simpa [h3_fullA_incidence,h3_pairedArcs,c,hβ9] using hW9
  have hvalid : ∀ i, (c i).1 < D.length ∧ tag D (c i).1 = true := by
    have hv {x : Fin 10} {e : Nat × Bool} (he : e ∈ exitArcs 10 D (carrierT 10 D {x})) :=
      And.intro (sem_mem_exit1.mp he).1 (h3_exit_tag_and h.1 he)
    intro i; fin_cases i
    · exact hv (by rw [hW0]; simp [c])
    · exact hv (by rw [hW1]; simp [c])
    · exact hv (by rw [hW4]; simp [c])
    · exact hv (by rw [hW5]; simp [c])
    · exact hv (by rw [hW3]; simp [c])
    · exact hv (by rw [hW3]; simp [c])
  have hempty : ∀ {j : Nat}, j < D.length → tag D j = true → supp 10 D (10+j) = ∅ :=
    fun hj ht => h3_saturated_fullA_and_empty h hC hz hB0 hone hSat hj ht
  have hpairvalid : ∀ i : Fin 6 × Bool, (h3_pairedArcs c i).1 < D.length ∧
      supp 10 D (10+(h3_pairedArcs c i).1) = ∅ := by
    intro i
    rw [h3_pairedArcs_fst]
    exact ⟨(hvalid i.1).1,hempty (hvalid i.1).1 (hvalid i.1).2⟩
  have hsources := h3_empty_indexed_sources_exact (h3_pairedArcs c) (h3_fullA_side β2 β8 β9)
    (h3_pairedArcs_injective c hginj) hW hpairvalid
  refine ⟨β2,β8,β9,c,hginj,hvalid,hsources,?_⟩
  intro j hj ht hn
  have hside (s : Bool) : supp 10 D (src D (j,s)) = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨x,hx⟩
    have he : (j,s) ∈ exitArcs 10 D (carrierT 10 D {x}) :=
      sem_mem_exit1.mpr ⟨hj,hx,by rw [hempty hj ht]; simp⟩
    rw [hW] at he
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp he
    have hh := congrArg Prod.fst hi
    rw [h3_pairedArcs_fst] at hh
    exact hn i.1 hh
  exact ⟨hside false,hside true⟩

end DagTools

namespace DagTools

lemma h3_saturated_meets_centers_subset {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hB0 : Bzero 10 D = 0) (hone : Bplus 10 D = (eligSet 10 D).card + 1)
    (hmeet : ∃ a ∈ h3_saturatedSet 10 D, a ∈ ({1,4,5} : Finset (Fin 10))) :
    h3_saturatedSet 10 D ⊆ ({1,4,5} : Finset (Fin 10)) := by
  obtain ⟨b,hb⟩ := sem_exists_pureBranch petersen_graph_ok h.1 hC
  have hr : (residualUnits 10 D b).card = 1 := by
    have := card_residual h.1 b hb
    omega
  obtain ⟨r,hR⟩ := Finset.card_eq_one.mp hr
  have hin (x : Fin 10) (hx : x ∈ h3_saturatedSet 10 D) : x ∈ supp 10 D r.1 :=
    (sem_saturated petersen_graph_ok h hC b hb hR (Finset.mem_filter.mp hx).2).2.2.2
  obtain ⟨a,ha,hac⟩ := hmeet
  have hRsub := h3_single_residual_support_subset_of_bzero h hC b hb hB0 hz hR
    ⟨a,hac,hin a ha⟩
  exact fun x hx => hRsub (hin x hx)

lemma h3_center_cycle_disjoint :
    Disjoint ({1,4,5} : Finset (Fin 10)) {2,3,6,7,8,9} := by decide

lemma h3_cycle_neighbor_centers_distinct : ∀ x ∈ ({2,3,6,7,8,9} : Finset (Fin 10)),
    ∀ y ∈ ({2,3,6,7,8,9} : Finset (Fin 10)), ∀ a ∈ ({1,4,5} : Finset (Fin 10)),
    ∀ b ∈ ({1,4,5} : Finset (Fin 10)),
    petersenAdj a x → petersenAdj b y → petersenAdj x y → a ≠ b := by
  unfold petersenAdj
  decide +kernel

lemma h3_cycle_edge_continuation : ∀ x ∈ ({2,3,6,7,8,9} : Finset (Fin 10)),
    ∀ y ∈ ({2,3,6,7,8,9} : Finset (Fin 10)), petersenAdj x y →
    ∃ w ∈ ({2,3,6,7,8,9} : Finset (Fin 10)), ∃ z ∈ ({2,3,6,7,8,9} : Finset (Fin 10)),
      w ≠ y ∧ petersenAdj x w ∧ petersenAdj w z ∧
      (∀ a ∈ ({y,z} : Finset (Fin 10)), ∀ b ∈ ({y,z} : Finset (Fin 10)), ¬ petersenAdj a b) := by
  unfold petersenAdj
  decide +kernel

lemma h3_three_exit_avoid {n : Nat} {D : Dag} {G : Fin n → Fin n → Prop}
    (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {x y : Fin n} {P Q r : Nat × Bool}
    (hW : sem_W n D x ⊆ {P,Q,r})
    (hP : y ∉ supp n D (src D (h3_opp P)))
    (hQ : y ∉ supp n D (src D (h3_opp Q))) (hxy : G x y) :
    h3_opp r ∈ sem_W n D y := by
  obtain ⟨j,hj,_,_,hxn,hyn,s,hxs,_,hys,_⟩ := sem_joint_meeting hG hS hC hxy
  have hh := hW (sem_mem_W.mpr ⟨hj,hxs,hxn⟩)
  simp only [Finset.mem_insert,Finset.mem_singleton] at hh
  rcases hh with he | he | he
  · exact (hP (by simpa only [←he,h3_opp] using hys)).elim
  · exact (hQ (by simpa only [←he,h3_opp] using hys)).elim
  · apply sem_mem_W.mpr
    simpa only [←he,h3_opp] using And.intro hj (And.intro hys hyn)

end DagTools

namespace DagTools

lemma h3_saturated_cycle_independent {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D)
    (hone : Bplus 10 D = (eligSet 10 D).card + 1)
    (hcycle : h3_saturatedSet 10 D ⊆ ({2,3,6,7,8,9} : Finset (Fin 10)))
    (hprivate : ∀ x ∈ ({2,3,6,7,8,9} : Finset (Fin 10)),
      ∃ a ∈ ({1,4,5} : Finset (Fin 10)), ∃ e : Nat × Bool,
        e ∈ sem_W 10 D x ∧ supp 10 D (src D (h3_opp e)) = {a} ∧ petersenAdj a x) :
    ∀ x ∈ h3_saturatedSet 10 D, ∀ y ∈ h3_saturatedSet 10 D, ¬ petersenAdj x y := by
  have hncenter : ∀ a ∈ ({1,4,5} : Finset (Fin 10)),
      ∀ v ∈ ({2,3,6,7,8,9} : Finset (Fin 10)), v ≠ a := by decide
  obtain ⟨P,Q,hPQ,hcommon⟩ := h3_one_residual_common_terminals petersen_graph_ok h hC hone
  have hPQ' : P ≠ Q := fun he => hPQ (congrArg Prod.fst he)
  intro x hx y hy hxy
  have hxcy := hcycle hx
  have hycy := hcycle hy
  obtain ⟨ax,hax,ex,hex,hpx,haxedge⟩ := hprivate x hxcy
  obtain ⟨ay,hay,ey,hey,hpy,hayedge⟩ := hprivate y hycy
  have haxa := h3_cycle_neighbor_centers_distinct x hxcy y hycy ax hax ay hay haxedge hayedge hxy
  obtain ⟨j,hj,_,_,hxn,hyn,s,hxs,hyns,hys,hxns⟩ :=
    sem_joint_meeting petersen_graph_ok h.1 hC hxy
  let r : Nat × Bool := (j,s)
  change x ∈ supp 10 D (src D r) at hxs
  change y ∉ supp 10 D (src D r) at hyns
  change y ∈ supp 10 D (src D (h3_opp r)) at hys
  change x ∉ supp 10 D (src D (h3_opp r)) at hxns
  have hrx : r ∈ sem_W 10 D x := sem_mem_W.mpr ⟨hj,hxs,hxn⟩
  have hry : h3_opp r ∈ sem_W 10 D y := sem_mem_W.mpr ⟨hj,hys,hyn⟩
  have hPr : P ≠ r := fun he => hyns (he ▸ (sem_mem_W.mp (hcommon y hy).1).2.1)
  have hQr : Q ≠ r := fun he => hyns (he ▸ (sem_mem_W.mp (hcommon y hy).2).2.1)
  have hPb : P ≠ h3_opp r := fun he => hxns (he ▸ (sem_mem_W.mp (hcommon x hx).1).2.1)
  have hQb : Q ≠ h3_opp r := fun he => hxns (he ▸ (sem_mem_W.mp (hcommon x hx).2).2.1)
  have hWx : sem_W 10 D x = {P,Q,r} := h3_card_three_eq_of_mem
    (h3_one_residual_saturation petersen_graph_ok h hC hone x hx).1
    (hcommon x hx).1 (hcommon x hx).2 hrx hPQ' hPr hQr
  have hWy : sem_W 10 D y = {P,Q,h3_opp r} := h3_card_three_eq_of_mem
    (h3_one_residual_saturation petersen_graph_ok h hC hone y hy).1
    (hcommon y hy).1 (hcommon y hy).2 hry hPQ' hPb hQb
  have hexr : ex ≠ r := by
    intro he
    have hh : y ∈ supp 10 D (src D (h3_opp ex)) := by simpa only [he] using hys
    rw [hpx,Finset.mem_singleton] at hh
    exact hncenter ax hax y hycy hh
  have heyr : ey ≠ h3_opp r := by
    intro he
    have hh : x ∈ supp 10 D (src D (h3_opp ey)) := by simpa only [he,h3_opp_opp] using hxs
    rw [hpy,Finset.mem_singleton] at hh
    exact hncenter ay hay x hxcy hh
  have hexpq : ex = P ∨ ex = Q := by
    rw [hWx] at hex
    simpa only [Finset.mem_insert,Finset.mem_singleton,hexr,or_false] using hex
  have heypq : ey = P ∨ ey = Q := by
    rw [hWy] at hey
    simpa only [Finset.mem_insert,Finset.mem_singleton,heyr,or_false] using hey
  have hexy : ex ≠ ey := by
    intro he
    have hh : ({ax} : Finset (Fin 10)) = {ay} := hpx.symm.trans ((congrArg (fun e => supp 10 D (src D (h3_opp e))) he).trans hpy)
    exact haxa (Finset.singleton_injective hh)
  have hpqprivate : (ex = P ∧ ey = Q) ∨ (ex = Q ∧ ey = P) := by
    rcases hexpq with hxP | hxQ <;> rcases heypq with hyP | hyQ
    · exact (hexy (hxP.trans hyP.symm)).elim
    · exact Or.inl ⟨hxP,hyQ⟩
    · exact Or.inr ⟨hxQ,hyP⟩
    · exact (hexy (hxQ.trans hyQ.symm)).elim
  have havoid : ∀ v ∈ ({2,3,6,7,8,9} : Finset (Fin 10)),
      v ∉ supp 10 D (src D (h3_opp P)) ∧ v ∉ supp 10 D (src D (h3_opp Q)) := by
    intro v hv
    have hxv : v ∉ supp 10 D (src D (h3_opp ex)) := by
      rw [hpx,Finset.mem_singleton]; exact hncenter ax hax v hv
    have hyv : v ∉ supp 10 D (src D (h3_opp ey)) := by
      rw [hpy,Finset.mem_singleton]; exact hncenter ay hay v hv
    rcases hpqprivate with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨hxv,hyv⟩
    · exact ⟨hyv,hxv⟩
  obtain ⟨w,hwcy,z,hzcy,hwy,hxw,hwz,hA⟩ := h3_cycle_edge_continuation x hxcy y hycy hxy
  have hwnsat : w ∉ h3_saturatedSet 10 D := by
    intro hw
    exact hwy (h3_one_residual_matching petersen_graph_ok h hC hone x hx w hw y hy hxw hxy)
  have hwcard : (sem_W 10 D w).card ≤ 2 := by
    by_contra hc
    apply hwnsat
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by change 3 ≤ (sem_W 10 D w).card; omega⟩
  have hrw : h3_opp r ∈ sem_W 10 D w := h3_three_exit_avoid petersen_graph_ok h.1 hC
    (by rw [hWx]) (havoid w hwcy).1 (havoid w hwcy).2 hxw
  obtain ⟨aw,haw,ew,hew,hpw,_⟩ := hprivate w hwcy
  have hewr : ew ≠ h3_opp r := by
    intro he
    have hh : x ∈ supp 10 D (src D (h3_opp ew)) := by simpa only [he,h3_opp_opp] using hxs
    rw [hpw,Finset.mem_singleton] at hh
    exact hncenter aw haw x hxcy hh
  have hWw : sem_W 10 D w = {ew,h3_opp r} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro e he
      simp only [Finset.mem_insert,Finset.mem_singleton] at he
      rcases he with rfl | rfl <;> assumption
    · simpa [hewr] using hwcard
  have hrz : r ∈ sem_W 10 D z := by
    have hh := h3_two_exit_avoid petersen_graph_ok h.1 hC
      (show exitArcs 10 D (carrierT 10 D {w}) ⊆ {ew,h3_opp r} by change sem_W 10 D w ⊆ _; rw [hWw])
      (show z ∉ supp 10 D (src D (h3_opp ew)) by rw [hpw,Finset.mem_singleton]; exact hncenter aw haw z hzcy) hwz
    simpa only [h3_opp_opp,sem_W] using hh
  obtain ⟨e,he,hd⟩ := h3_exposure_exit petersen_graph_ok h.1 hC {y,z} hA x ⟨y,by simp,hxy⟩
  change e ∈ sem_W 10 D x at he
  rw [hWx] at he
  simp only [Finset.mem_insert,Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl
  · exact Finset.disjoint_left.mp hd (sem_mem_W.mp (hcommon y hy).1).2.1 (by simp)
  · exact Finset.disjoint_left.mp hd (sem_mem_W.mp (hcommon y hy).2).2.1 (by simp)
  · exact Finset.disjoint_left.mp hd (sem_mem_W.mp hrz).2.1 (by simp)

end DagTools

namespace DagTools
lemma h3_cycle_private_exits {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hcentercard : ∀ a ∈ ({1,4,5} : Finset (Fin 10)), (sem_W 10 D a).card ≤ 2) :
    ∀ x ∈ ({2,3,6,7,8,9} : Finset (Fin 10)),
      ∃ a ∈ ({1,4,5} : Finset (Fin 10)), ∃ e : Nat × Bool,
        e ∈ sem_W 10 D x ∧ supp 10 D (src D (h3_opp e)) = {a} ∧ petersenAdj a x := by
  obtain ⟨e0,he0,_,hp0,ho0,hn0,_,_⟩ := sem_inelig_consumer petersen_graph_ok h hC hz
  let A := h3_opp e0
  have hbar : supp 10 D (src D (A.1,!A.2)) = {(0 : Fin 10)} := by
    simpa [A,h3_opp] using hp0
  have hN : ({1,4,5} : Finset (Fin 10)) ⊆ supp 10 D (src D A) := by
    intro a ha
    apply hn0
    have hh : ∀ b ∈ ({1,4,5} : Finset (Fin 10)),petersenAdj 0 b := by
      unfold petersenAdj; decide
    exact hh a ha
  have hAmem : ∀ a ∈ ({1,4,5} : Finset (Fin 10)),A ∈ sem_W 10 D a := by
    intro a ha
    apply sem_mem_W.mpr
    exact ⟨he0,hN ha,by rw [show 10+A.1 = 10+e0.1 from rfl,ho0]; simp⟩
  have hgeo : ∀ x ∈ ({2,3,6,7,8,9} : Finset (Fin 10)),
      x ≠ 0 ∧ ∃ a ∈ ({1,4,5} : Finset (Fin 10)),a ≠ 0 ∧ petersenAdj a x := by
    unfold petersenAdj; decide
  intro x hx
  obtain ⟨hx0,a,ha,ha0,hax⟩ := hgeo x hx
  obtain ⟨f,_,_,hfp,hfr⟩ := h3_star0_two_exit_completion h.1 hC hz ha0
    (hAmem a ha) hbar hN (hcentercard a ha)
  refine ⟨a,ha,h3_opp f,hfr x hax hx0,?_,hax⟩
  simpa only [h3_opp_opp] using hfp

end DagTools

namespace DagTools

lemma h3_saturated_centers_or_independent_cycle {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hB0 : Bzero 10 D = 0) (hone : Bplus 10 D = (eligSet 10 D).card + 1) :
    h3_saturatedSet 10 D ⊆ ({1,4,5} : Finset (Fin 10)) ∨
      (h3_saturatedSet 10 D ⊆ ({2,3,6,7,8,9} : Finset (Fin 10)) ∧
        ∀ x ∈ h3_saturatedSet 10 D, ∀ y ∈ h3_saturatedSet 10 D, ¬ petersenAdj x y) := by
  by_cases hmeet : ∃ a ∈ h3_saturatedSet 10 D, a ∈ ({1,4,5} : Finset (Fin 10))
  · exact Or.inl (h3_saturated_meets_centers_subset h hC hz hB0 hone hmeet)
  · have hcentercard : ∀ a ∈ ({1,4,5} : Finset (Fin 10)), (sem_W 10 D a).card ≤ 2 := by
      intro a ha
      by_contra hcard
      apply hmeet
      refine ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ha⟩
      change 3 ≤ (sem_W 10 D a).card
      omega
    have hcycle : h3_saturatedSet 10 D ⊆ ({2,3,6,7,8,9} : Finset (Fin 10)) := by
      intro x hx
      have hxN : x ∉ ({1,4,5} : Finset (Fin 10)) := fun hh => hmeet ⟨x,hx,hh⟩
      have hx0 : x ≠ 0 := by
        intro he
        have hxe := (h3_one_residual_saturation petersen_graph_ok h hC hone x hx).2.2
        have hznot := (Finset.mem_sdiff.mp hz).2
        exact hznot (he ▸ hxe)
      have hf : ∀ v : Fin 10, v ≠ 0 → v ∉ ({1,4,5} : Finset (Fin 10)) →
          v ∈ ({2,3,6,7,8,9} : Finset (Fin 10)) := by decide
      exact hf x hx0 hxN
    exact Or.inr ⟨hcycle, h3_saturated_cycle_independent h hC hone hcycle
      (h3_cycle_private_exits h hC hz hcentercard)⟩

end DagTools

namespace DagTools

lemma h3_relabel_src {n : Nat} (σ : Equiv.Perm (Fin n)) (D : Dag)
    (e : Nat × Bool) (he : e.1 < D.length) :
    src (relabel σ D) e = liftP σ (src D e) := by
  rcases e with ⟨j,s⟩
  cases s
  · exact tr_opA σ D j he
  · exact tr_opB σ D j he

lemma h3_relabel_supp_mem {n : Nat} (σ : Equiv.Perm (Fin n)) {D : Dag}
    (hS : Strict n D) (w : Nat) (x : Fin n) :
    σ x ∈ supp n (relabel σ D) (liftP σ w) ↔ x ∈ supp n D w := by
  rw [relabel_supp σ hS]
  simp only [Finset.mem_image, σ.injective.eq_iff, exists_eq_right]

lemma h3_relabel_exit {n : Nat} (σ : Equiv.Perm (Fin n)) {D : Dag}
    (hS : Strict n D) (x : Fin n) :
    exitArcs n (relabel σ D) (carrierT n (relabel σ D) {σ x}) =
      exitArcs n D (carrierT n D {x}) := by
  ext e
  rw [sem_mem_exit1, sem_mem_exit1, relabel_length]
  by_cases he : e.1 < D.length
  · rw [h3_relabel_src σ D e he]
    have hg : n + e.1 = liftP σ (n + e.1) := (tr_liftP_ge σ (by omega)).symm
    rw [hg, h3_relabel_supp_mem σ hS, h3_relabel_supp_mem σ hS]
    rw [tr_liftP_ge σ (Nat.le_add_right n e.1)]
  · simp [he]

lemma h3_relabel_saturated {n : Nat} (σ : Equiv.Perm (Fin n)) {D : Dag}
    (hS : Strict n D) :
    h3_saturatedSet n (relabel σ D) = (h3_saturatedSet n D).image σ := by
  ext x
  obtain ⟨x,rfl⟩ := σ.surjective x
  simp only [h3_saturatedSet, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_image, σ.injective.eq_iff, exists_eq_right, h3_relabel_exit σ hS]

lemma h3_relabel_zero {n : Nat} (σ : Equiv.Perm (Fin n)) {D : Dag}
    (hS : Strict n D) (hB : Bzero n D = 0) : Bzero n (relabel σ D) = 0 := by
  unfold Bzero surplusOn
  apply Finset.sum_eq_zero
  intro w hw
  obtain ⟨w,rfl⟩ : ∃ v, w = liftP σ v := ⟨liftP σ⁻¹ w, (tr_liftP_inv' σ w).symm⟩
  rw [relabel_fanout]
  by_contra hn
  have hf : 2 ≤ fanout D w := by omega
  have hp : (supp n D w).Nonempty := by
    by_contra hz
    have hm : w ∈ (inner n D).filter (fun w => ¬ (supp n D w).Nonempty) :=
      Finset.mem_filter.mpr ⟨sb_mem_inner.mpr (lt_of_fanout_pos hS (by omega)), hz⟩
    have hh := Finset.single_le_sum (f := fun w => fanout D w - 1)
      (fun _ _ => Nat.zero_le _) hm
    change fanout D w - 1 ≤ Bzero n D at hh
    omega
  have hn' := (Finset.mem_filter.mp hw).2
  rw [relabel_supp σ hS] at hn'
  exact hn' (hp.image σ)

lemma h3_relabel_one {n : Nat} (σ : Equiv.Perm (Fin n)) {D : Dag}
    (h : StrictLive n D) (hB : Bzero n D = 0)
    (hone : Bplus n D = (eligSet n D).card + 1) :
    Bplus n (relabel σ D) = (eligSet n (relabel σ D)).card + 1 := by
  have hb' := h3_relabel_zero σ h.1 hB
  have ht := surplus_identity h
  have ht' := surplus_identity (relabel_strictLive σ h)
  rw [totalSurplus_split, hB] at ht
  rw [totalSurplus_split, hb', relabel_length] at ht'
  rw [relabel_eligSet σ h.1, Finset.card_image_of_injective _ σ.injective]
  omega

lemma h3_relabel_comp {n : Nat} (σ : Equiv.Perm (Fin n))
    {G : Fin n → Fin n → Prop} {D : Dag} (h : StrictLive n D)
    (hC : sem_Comp n G D) (hG : ∀ a b, G (σ a) (σ b) ↔ G a b) :
    sem_Comp n G (relabel σ D) := by
  intro x
  rw [relabel_out σ h.1 h.2.2, hC]
  constructor
  · rintro ⟨a,b,hab,ha,hb⟩
    exact ⟨σ a,σ b,(hG a b).mpr hab,ha,hb⟩
  · rintro ⟨a,b,hab,ha,hb⟩
    obtain ⟨a,rfl⟩ := σ.surjective a
    obtain ⟨b,rfl⟩ := σ.surjective b
    exact ⟨a,b,(hG a b).mp hab,ha,hb⟩

end DagTools

namespace DagTools

def h3_stabilizerMap (k : Fin 12) (x : Fin 10) : Fin 10 :=
  ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 4, 3, 8, 5, 1, 9, 2, 6, 7, 0, 5, 8, 6, 1, 4, 7, 3, 9, 2, 0, 1, 6, 9, 4, 5, 2, 8, 7, 3, 0, 4, 9, 7, 5, 1, 3, 6, 2, 8, 0, 5, 7, 2, 1, 4, 8, 9, 3, 6, 0, 1, 2, 7, 5, 4, 6, 3, 9, 8, 0, 4, 3, 2, 1, 5, 9, 8, 7, 6, 0, 5, 8, 3, 4, 1, 7, 6, 2, 9, 0, 1, 6, 8, 5, 4, 2, 9, 3, 7, 0, 4, 9, 6, 1, 5, 3, 7, 8, 2, 0, 5, 7, 9, 4, 1, 8, 2, 6, 3] : List (Fin 10)).getD (10 * k.val + x.val) 0

def h3_stabilizerInverse (k : Fin 12) : Fin 12 :=
  ([0, 5, 4, 3, 2, 1, 6, 7, 8, 9, 10, 11] : List (Fin 12)).getD k.val 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma h3_stabilizerMap_inverse : ∀ (k : Fin 12) (x : Fin 10),
    h3_stabilizerMap (h3_stabilizerInverse k) (h3_stabilizerMap k x) = x ∧
    h3_stabilizerMap k (h3_stabilizerMap (h3_stabilizerInverse k) x) = x := by
  decide +kernel

def h3_stabilizer (k : Fin 12) : Equiv.Perm (Fin 10) :=
  { toFun := h3_stabilizerMap k
    invFun := h3_stabilizerMap (h3_stabilizerInverse k)
    left_inv := fun x => (h3_stabilizerMap_inverse k x).1
    right_inv := fun x => (h3_stabilizerMap_inverse k x).2 }

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma h3_stabilizerMap_graph : ∀ k : Fin 12,
    h3_stabilizerMap k 0 = 0 ∧
    ∀ x y : Fin 10, petersenAdj (h3_stabilizerMap k x) (h3_stabilizerMap k y) ↔ petersenAdj x y := by
  unfold petersenAdj
  decide +kernel

def h3_orbitCanonical (S : Finset (Fin 10)) : Prop :=
  S = ∅ ∨ S = {1} ∨ S = {2} ∨ S = {1,4} ∨ S = {2,6} ∨
    S = {3,6} ∨ S = {1,4,5} ∨ S = {3,6,7}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma h3_stabilizer_orbit_table : ∀ S : Finset (Fin 10),
    (S ⊆ {1,4,5} ∨ (S ⊆ {2,3,6,7,8,9} ∧
      ∀ x ∈ S, ∀ y ∈ S, ¬ petersenAdj x y)) →
    ∃ k : Fin 12, h3_orbitCanonical (S.image (h3_stabilizerMap k)) := by
  unfold h3_orbitCanonical petersenAdj
  decide +kernel

lemma h3_petersen_stabilizer_orbit (S : Finset (Fin 10))
    (hS : S ⊆ {1,4,5} ∨ (S ⊆ {2,3,6,7,8,9} ∧
      ∀ x ∈ S, ∀ y ∈ S, ¬ petersenAdj x y)) :
    ∃ σ : Equiv.Perm (Fin 10), σ 0 = 0 ∧
      (∀ x y : Fin 10, petersenAdj (σ x) (σ y) ↔ petersenAdj x y) ∧
      h3_orbitCanonical (S.image σ) := by
  obtain ⟨k,hk⟩ := h3_stabilizer_orbit_table S hS
  exact ⟨h3_stabilizer k,(h3_stabilizerMap_graph k).1,
    (h3_stabilizerMap_graph k).2,hk⟩

end DagTools


namespace DagTools

lemma h3_r1_reduction_three {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hB0 : Bzero 10 D = 0) (hone : Bplus 10 D = (eligSet 10 D).card + 1) :
    ∃ E : Dag, StrictLive 10 E ∧ sem_Comp 10 petersenAdj E ∧
      (0 : Fin 10) ∈ ineligSet 10 E ∧ Bzero 10 E = 0 ∧
      Bplus 10 E = (eligSet 10 E).card + 1 ∧ E.length = D.length ∧
      (h3_saturatedSet 10 E = {1,4} ∨ h3_saturatedSet 10 E = {1,4,5} ∨
        h3_saturatedSet 10 E = {3,6,7}) := by
  obtain ⟨σ,hσ0,hσG,hcan⟩ := h3_petersen_stabilizer_orbit (h3_saturatedSet 10 D)
    (h3_saturated_centers_or_independent_cycle h hC hz hB0 hone)
  let E := relabel σ D
  have hE : StrictLive 10 E := relabel_strictLive σ h
  have hEC : sem_Comp 10 petersenAdj E := h3_relabel_comp σ h hC hσG
  have hEz : (0 : Fin 10) ∈ ineligSet 10 E := by
    rw [show ineligSet 10 E = (ineligSet 10 D).image σ from relabel_ineligSet σ h.1]
    exact Finset.mem_image.mpr ⟨0,hz,hσ0⟩
  have hEB : Bzero 10 E = 0 := h3_relabel_zero σ h.1 hB0
  have hEone : Bplus 10 E = (eligSet 10 E).card + 1 := h3_relabel_one σ h hB0 hone
  have hEq : h3_orbitCanonical (h3_saturatedSet 10 E) := by
    rw [show h3_saturatedSet 10 E = (h3_saturatedSet 10 D).image σ from
      h3_relabel_saturated σ h.1]
    exact hcan
  refine ⟨E,hE,hEC,hEz,hEB,hEone,relabel_length σ D,?_⟩
  rcases hEq with he | he | he | he | he | he | he | he
  · obtain ⟨x,_,hx⟩ := h3_bzero_has_three_exits hE hEC hEz hEB
    have hm : x ∈ h3_saturatedSet 10 E := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩
    rw [he] at hm
    exact False.elim (Finset.notMem_empty _ hm)
  · exact False.elim (h3_saturated_one_exclusion hE hEC hEz hEB hEone he)
  · exact False.elim (h3_residual_saturated_two_exclusion hE hEC hEz hEB hEone he)
  · exact Or.inl he
  · exact False.elim (h3_residual_saturated_pair26_exclusion hE hEC hEz hEB hEone he)
  · exact False.elim (h3_saturated_pair36_exclusion hE hEC hEz hEB hEone he)
  · exact Or.inr (Or.inl he)
  · exact Or.inr (Or.inr he)

end DagTools


namespace DagTools
open R1FlexibleResource.CausalBarrier R1FlexibleResource.ResourceExclusion
  R1FlexibleResource.DAGBridge

lemma h3_fullA_trivial_side_table : ∀ b : Bool, ∀ i : Fin 6,
    i ≠ (if b then 4 else 5) →
    (h3_fullA_side b b b (i,false), h3_fullA_side b b b (i,true)) ∈ OtherSides ∨
    (h3_fullA_side b b b (i,false) = DirtyA ∧ h3_fullA_side b b b (i,true) = ∅) := by
  decide +kernel

lemma h3_fullA_trivial_exclusion {D : Dag} (hS : Strict 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hB0 : Bzero 10 D = 0)
    (b : Bool) (c : Fin 6 → Nat × Bool)
    (hc : Function.Injective (fun i => (c i).1))
    (hv : ∀ i, (c i).1 < D.length ∧ tag D (c i).1 = true)
    (hs : ∀ i : Fin 6 × Bool,
      supp 10 D (src D (h3_pairedArcs c i)) = h3_fullA_side b b b i)
    (ho : ∀ j, j < D.length → tag D j = true → (∀ i, (c i).1 ≠ j) →
      supp 10 D (opA D j) = ∅ ∧ supp 10 D (opB D j) = ∅) : False := by
  let d : Fin 6 := if b then 4 else 5
  have hsd : supp 10 D (src D (c d)) = DirtyA := by
    have hh := hs (d,false)
    cases b <;> simpa [h3_pairedArcs,d,h3_fullA_side,DirtyA] using hh
  have htd : supp 10 D (src D (h3_opp (c d))) = DirtyB := by
    have hh := hs (d,true)
    cases b <;> simpa [h3_pairedArcs,d,h3_fullA_side,h3_fullA_part,DirtyB] using hh
  have hd : DirtySides D (c d).1 := by
    cases hb : (c d).2
    · exact Or.inl ⟨by simpa [src,hb] using hsd,by simpa [src,h3_opp,hb] using htd⟩
    · exact Or.inr ⟨by simpa [src,h3_opp,hb] using htd,by simpa [src,hb] using hsd⟩
  have hother : OtherAndSides D (c d).1 := by
    intro j hj hjd ht
    by_cases hex : ∃ i, (c i).1 = j
    · obtain ⟨i,hi⟩ := hex
      have hid : i ≠ d := by intro hh; subst i; exact hjd hi.symm
      have ha : supp 10 D (src D (c i)) = h3_fullA_side b b b (i,false) := by
        simpa [h3_pairedArcs] using hs (i,false)
      have hb : supp 10 D (src D (h3_opp (c i))) = h3_fullA_side b b b (i,true) := by
        simpa [h3_pairedArcs] using hs (i,true)
      have hh : AllowedSides (DagResource D (src D (c i)))
          (DagResource D (src D (h3_opp (c i)))) := by
        rcases h3_fullA_trivial_side_table b i hid with hmem | ⟨hA,hz⟩
        · apply Or.inl; apply Or.inl; apply Or.inr; apply Or.inl
          change (supp 10 D (src D (c i)),supp 10 D (src D (h3_opp (c i)))) ∈ OtherSides
          rwa [ha,hb]
        · apply h3_full_side_allowed_right hS (hb.trans hz)
          exact Or.inl (by rw [ha,hA])
      cases hside : (c i).2
      · simpa [src,h3_opp,hi,hside] using hh
      · have hswap := allowed_sides_swap hh
        simpa [src,h3_opp,hi,hside] using hswap
    · obtain ⟨ha,hb⟩ := ho j hj ht (fun i hi => hex ⟨i,hi⟩)
      exact Or.inl (Or.inl (Or.inl (ha.trans hb.symm)))
  exact h3_r1_flexible_allowed_sides_exclusion hS hC hB0 (hv d).1 (hv d).2 hd hother

end DagTools

namespace DagTools

def h3_fullA_code (β2 β8 β9 : Bool) : Nat :=
  (if β2 then 1 else 0) + (if β8 then 2 else 0) + (if β9 then 4 else 0)

def h3_fullA_normalizerIndex (β2 β8 β9 : Bool) : Fin 12 :=
  ([0,0,4,2,2,4,0,0] : List (Fin 12)).getD (h3_fullA_code β2 β8 β9) 0

def h3_fullA_gateMap (β2 β8 β9 : Bool) (i : Fin 6) : Fin 6 :=
  ([0,1,2,3,4,5, 0,1,2,3,4,5, 0,3,1,2,4,5, 0,2,3,1,5,4,
    0,2,3,1,4,5, 0,3,1,2,5,4, 0,1,2,3,5,4, 0,1,2,3,4,5] : List (Fin 6)).getD
      (6*h3_fullA_code β2 β8 β9+i.val) 0

def h3_fullA_gateInverse (β2 β8 β9 : Bool) (i : Fin 6) : Fin 6 :=
  ([0,1,2,3,4,5, 0,1,2,3,4,5, 0,2,3,1,4,5, 0,3,1,2,5,4,
    0,3,1,2,4,5, 0,2,3,1,5,4, 0,1,2,3,5,4, 0,1,2,3,4,5] : List (Fin 6)).getD
      (6*h3_fullA_code β2 β8 β9+i.val) 0

set_option maxRecDepth 100000 in
lemma h3_fullA_gate_inverse : ∀ β2 β8 β9 : Bool, ∀ i : Fin 6,
    h3_fullA_gateInverse β2 β8 β9 (h3_fullA_gateMap β2 β8 β9 i) = i ∧
    h3_fullA_gateMap β2 β8 β9 (h3_fullA_gateInverse β2 β8 β9 i) = i := by
  decide +kernel

def h3_fullA_gatePerm (β2 β8 β9 : Bool) : Equiv.Perm (Fin 6) :=
  { toFun := h3_fullA_gateMap β2 β8 β9
    invFun := h3_fullA_gateInverse β2 β8 β9
    left_inv := fun i => (h3_fullA_gate_inverse β2 β8 β9 i).1
    right_inv := fun i => (h3_fullA_gate_inverse β2 β8 β9 i).2 }

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma h3_fullA_normalization_table : ∀ β2 β8 β9 : Bool, (β2 ≠ β8 ∨ β2 ≠ β9) →
    (({3,6,7} : Finset (Fin 10)).image (h3_stabilizerMap (h3_fullA_normalizerIndex β2 β8 β9)) = {3,6,7}) ∧
    ∀ i : Fin 6 × Bool,
      (h3_fullA_side β2 β8 β9 (h3_fullA_gateMap β2 β8 β9 i.1,i.2)).image
        (h3_stabilizerMap (h3_fullA_normalizerIndex β2 β8 β9)) = h3_fullA_side true false false i := by
  decide +kernel

lemma h3_relabel_arc_supp {n : Nat} (σ : Equiv.Perm (Fin n)) {D : Dag}
    (hS : Strict n D) (e : Nat × Bool) (he : e.1 < D.length) :
    supp n (relabel σ D) (src (relabel σ D) e) = (supp n D (src D e)).image σ := by
  rw [h3_relabel_src σ D e he,relabel_supp σ hS]

lemma h3_fullA_nontrivial_normalization {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hB0 : Bzero 10 D = 0) (hone : Bplus 10 D = (eligSet 10 D).card + 1)
    (hSat : h3_saturatedSet 10 D = {3,6,7})
    (β2 β8 β9 : Bool) (hneq : β2 ≠ β8 ∨ β2 ≠ β9) (c : Fin 6 → Nat × Bool)
    (hinj : Function.Injective (fun i => (c i).1))
    (hvalid : ∀ i, (c i).1 < D.length ∧ tag D (c i).1 = true)
    (hsources : ∀ i : Fin 6 × Bool,
      supp 10 D (src D (h3_pairedArcs c i)) = h3_fullA_side β2 β8 β9 i)
    (hother : ∀ j, j < D.length → tag D j = true → (∀ i, (c i).1 ≠ j) →
      supp 10 D (opA D j) = ∅ ∧ supp 10 D (opB D j) = ∅) :
    ∃ E : Dag, ∃ d : Fin 6 → Nat × Bool,
      E.length = D.length ∧ StrictLive 10 E ∧ sem_Comp 10 petersenAdj E ∧
      (0 : Fin 10) ∈ ineligSet 10 E ∧ Bzero 10 E = 0 ∧
      Bplus 10 E = (eligSet 10 E).card + 1 ∧ h3_saturatedSet 10 E = {3,6,7} ∧
      Function.Injective (fun i => (d i).1) ∧
      (∀ i, (d i).1 < E.length ∧ tag E (d i).1 = true) ∧
      (∀ i : Fin 6 × Bool, supp 10 E (src E (h3_pairedArcs d i)) = h3_fullA_side true false false i) ∧
      (∀ j, j < E.length → tag E j = true → (∀ i, (d i).1 ≠ j) →
        supp 10 E (opA E j) = ∅ ∧ supp 10 E (opB E j) = ∅) := by
  let σ := h3_stabilizer (h3_fullA_normalizerIndex β2 β8 β9)
  let κ := h3_fullA_gatePerm β2 β8 β9
  let E := relabel σ D
  let d : Fin 6 → Nat × Bool := fun i => c (κ i)
  have hσ0 : σ 0 = 0 := (h3_stabilizerMap_graph _).1
  have hσG : ∀ x y : Fin 10, petersenAdj (σ x) (σ y) ↔ petersenAdj x y :=
    (h3_stabilizerMap_graph _).2
  have htable := h3_fullA_normalization_table β2 β8 β9 hneq
  have hE : StrictLive 10 E := relabel_strictLive σ h
  have hEC : sem_Comp 10 petersenAdj E := h3_relabel_comp σ h hC hσG
  have hEz : (0 : Fin 10) ∈ ineligSet 10 E := by
    rw [show E = relabel σ D from rfl,relabel_ineligSet σ h.1]
    exact Finset.mem_image.mpr ⟨0,hz,hσ0⟩
  have hEB0 : Bzero 10 E = 0 := h3_relabel_zero σ h.1 hB0
  have hEone : Bplus 10 E = (eligSet 10 E).card + 1 := h3_relabel_one σ h hB0 hone
  have hESat : h3_saturatedSet 10 E = {3,6,7} := by
    rw [show E = relabel σ D from rfl,h3_relabel_saturated σ h.1,hSat]
    exact htable.1
  have hdinj : Function.Injective (fun i => (d i).1) :=
    fun i j he => κ.injective (hinj he)
  have hdvalid : ∀ i, (d i).1 < E.length ∧ tag E (d i).1 = true := by
    intro i
    change (c (κ i)).1 < (relabel σ D).length ∧ tag (relabel σ D) (c (κ i)).1 = true
    rw [relabel_length,tr_tag σ D _ (hvalid (κ i)).1]
    exact hvalid (κ i)
  have hdsources : ∀ i : Fin 6 × Bool,
      supp 10 E (src E (h3_pairedArcs d i)) = h3_fullA_side true false false i := by
    rintro ⟨i,s⟩
    change supp 10 (relabel σ D) (src (relabel σ D) (h3_pairedArcs c (κ i,s))) = _
    rw [h3_relabel_arc_supp σ h.1 _ (by rw [h3_pairedArcs_fst]; exact (hvalid (κ i)).1),hsources]
    exact htable.2 (i,s)
  refine ⟨E,d,relabel_length σ D,hE,hEC,hEz,hEB0,hEone,hESat,hdinj,hdvalid,hdsources,?_⟩
  intro j hj ht hn
  have hjD : j < D.length := by simpa only [E,relabel_length] using hj
  have htD : tag D j = true := by simpa only [E,tr_tag σ D j hjD] using ht
  have hnD : ∀ i, (c i).1 ≠ j := by
    intro i
    have hh := hn (κ.symm i)
    simpa only [d,κ.apply_symm_apply] using hh
  obtain ⟨ha,hb⟩ := hother j hjD htD hnD
  constructor
  · change supp 10 (relabel σ D) (opA (relabel σ D) j) = ∅
    rw [tr_opA σ D j hjD,relabel_supp σ h.1,ha,Finset.image_empty]
  · change supp 10 (relabel σ D) (opB (relabel σ D) j) = ∅
    rw [tr_opB σ D j hjD,relabel_supp σ h.1,hb,Finset.image_empty]

end DagTools

namespace DagTools

lemma h3_fullA_reduction_representative {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hB0 : Bzero 10 D = 0) (hone : Bplus 10 D = (eligSet 10 D).card + 1)
    (hSat : h3_saturatedSet 10 D = {3,6,7}) :
    ∃ E : Dag, ∃ d : Fin 6 → Nat × Bool,
      E.length = D.length ∧ StrictLive 10 E ∧ sem_Comp 10 petersenAdj E ∧
      (0 : Fin 10) ∈ ineligSet 10 E ∧ Bzero 10 E = 0 ∧
      Bplus 10 E = (eligSet 10 E).card + 1 ∧ h3_saturatedSet 10 E = {3,6,7} ∧
      Function.Injective (fun i => (d i).1) ∧
      (∀ i, (d i).1 < E.length ∧ tag E (d i).1 = true) ∧
      (∀ i : Fin 6 × Bool, supp 10 E (src E (h3_pairedArcs d i)) = h3_fullA_side true false false i) ∧
      (∀ j, j < E.length → tag E j = true → (∀ i, (d i).1 ≠ j) →
        supp 10 E (opA E j) = ∅ ∧ supp 10 E (opB E j) = ∅) := by
  obtain ⟨β2,β8,β9,c,hinj,hvalid,hsources,hother⟩ :=
    h3_saturated_fullA_sources_exist h hC hz hB0 hone hSat
  by_cases hn : β2 ≠ β8 ∨ β2 ≠ β9
  · exact h3_fullA_nontrivial_normalization h hC hz hB0 hone hSat
      β2 β8 β9 hn c hinj hvalid hsources hother
  · have h28 : β2 = β8 := by tauto
    have h29 : β2 = β9 := by tauto
    subst β8
    subst β9
    exact False.elim (h3_fullA_trivial_exclusion h.1 hC hB0 β2 c hinj hvalid hsources hother)

end DagTools

end PEqualNP.Outside.L_meta_2590_aux
