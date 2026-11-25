import PEqualNP.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.BitVec
import Mathlib.Tactic.FinCases
import Mathlib.Data.List.GetD
import Mathlib.Data.Tree.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Tactic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Relation
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Powerset

namespace PEqualNP.Outside.L_meta_2590

namespace DAGBridge.DagTools

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

def outW (n : ℕ) (D : Dag) : ℕ := n + D.length - 1

def single {n : ℕ} (v : Fin n) : Fin n → Bool := fun i => decide (i = v)

def supp (n : ℕ) (D : Dag) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => val D (single v) w = true)

def surplusOn (D : Dag) (K : Finset ℕ) : ℕ := ∑ w ∈ K, (fanout D w - 1)

def inner (n : ℕ) (D : Dag) : Finset ℕ := Finset.range (n + D.length - 1)

def Bzero (n : ℕ) (D : Dag) : ℕ :=
  surplusOn D ((inner n D).filter (fun w => ¬ (supp n D w).Nonempty))

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

variable {n : ℕ} {D : Dag}

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

lemma supp_gate (hS : Strict n D) (j : ℕ) (hj : j < D.length) :
    supp n D (n + j) = if tag D j = true then supp n D (opA D j) ∩ supp n D (opB D j)
      else supp n D (opA D j) ∪ supp n D (opB D j) := by
  ext v
  rw [mem_supp, val_gate hS _ j hj]
  cases tag D j <;> simp [mem_supp, gop]

end DAGBridge.DagTools

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

def OtherSides : List (Finset (Fin 10) × Finset (Fin 10)) :=
  [({0}, {1, 4, 5}), ({1}, {2, 6}), ({4}, {3, 9}), ({5}, {7, 8}), (∅, ∅)]

end FiveGroup.CausalBarrier

namespace FiveGroup.ResourceExclusion

open CausalBarrier

abbrev Resource := Finset (Fin 10) × (Finset (Fin 10) → Bool)

def CrossPairs : List (Finset (Fin 10)) :=
  [{2, 3}, {3, 8}, {3, 9}, {2, 6}, {6, 8}, {6, 9}, {2, 7}, {7, 8}, {7, 9}]

def RSafe (E T : Finset (Fin 10)) (w : Resource) : Prop :=
  w.2 E = true → (w.1 ∩ T).Nonempty

def Ordinary (w : Resource) : Prop := ∀ E ∈ CrossPairs, RSafe E E w

def RJoin (a b : Resource) : Resource :=
  (a.1 ∪ b.1, fun E => a.2 E || b.2 E)

def RMeet (a b : Resource) : Resource :=
  (a.1 ∩ b.1, fun E => a.2 E && b.2 E)

def AllowedSides (a b : Resource) : Prop :=
  (a.1, b.1) ∈ OtherSides ∨ (b.1, a.1) ∈ OtherSides

lemma rsafe_join {E T : Finset (Fin 10)} {a b : Resource}
    (ha : RSafe E T a) (hb : RSafe E T b) : RSafe E T (RJoin a b) := by
  exact safe_join (a := (a.1, a.2 E)) (b := (b.1, b.2 E)) ha hb

lemma rsafe_meet {E T : Finset (Fin 10)} {a b : Resource}
    (ha : RSafe E T a) (hb : RSafe E T b) (hs : Separates T a.1 b.1) :
    RSafe E T (RMeet a b) := by
  exact safe_meet (a := (a.1, a.2 E)) (b := (b.1, b.2 E)) ha hb hs

lemma cross_separation :
    ∀ E ∈ CrossPairs, ∀ AB ∈ OtherSides,
      Separates E AB.1 AB.2 ∧ Separates E AB.2 AB.1 := by
  simp [CrossPairs, OtherSides, Separates]

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

lemma ordinary_result {a b c : Resource} (ha : Ordinary a) (hb : Ordinary b)
    (hc : c = RJoin a b ∨ (AllowedSides a b ∧ c = RMeet a b)) : Ordinary c := by
  rcases hc with rfl | ⟨hs, rfl⟩
  · exact ordinary_join ha hb
  · exact ordinary_meet ha hb hs

end FiveGroup.ResourceExclusion

namespace FiveGroup.IndexSchedule

open ResourceExclusion

def ValidUpTo (start : ℕ) (A B : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ t < n, A (start + t) < start + t ∧ B (start + t) < start + t ∧
    A (start + t) ≠ B (start + t)

def CanonicalUpTo (W : ℕ → Resource) (start : ℕ) (A B : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ t < n,
    W (start + t) = RJoin (W (A (start + t))) (W (B (start + t))) ∨
    (AllowedSides (W (A (start + t))) (W (B (start + t))) ∧
      W (start + t) = RMeet (W (A (start + t))) (W (B (start + t))))

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

open PEqualNP.Outside.L_meta_2590.DAGBridge.DagTools
open ResourceExclusion IndexSchedule CausalBarrier

def DagResource (D : Dag) (w : ℕ) : Resource :=
  (supp 10 D w, fun E => val D (fun v => decide (v ∈ E)) w)

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

end FiveGroup.DAGBridge
namespace ResourceCertificate

def search {α β : Type} [BEq α] (lt : α → α → Bool)
    (xs : Array β) (decode : β → α) (needle : α) : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, lo, hi =>
      if lo < hi then
        let mid := (lo + hi) / 2
        if h : mid < xs.size then
          if decode xs[mid] == needle then true
          else if lt needle (decode xs[mid]) then
            search lt xs decode needle fuel lo mid
          else search lt xs decode needle fuel (mid + 1) hi
        else false
      else false

lemma reachable_mem {α : Type} (states : List α) (next : α → List α)
    (contains : α → Bool)
    (hcontains : ∀ s, contains s = true → s ∈ states)
    (hclosed : states.all (fun s => (next s).all contains) = true)
    {start finish : α} (hstart : contains start = true)
    (hreach : Relation.ReflTransGen (fun a b => b ∈ next a) start finish) :
    finish ∈ states := by
  have step : ∀ a ∈ states, ∀ b ∈ next a, b ∈ states := by
    intro a ha b hb
    exact hcontains b (List.all_eq_true.mp (List.all_eq_true.mp hclosed a ha) b hb)
  induction hreach with
  | refl => exact hcontains start hstart
  | @tail b c hab hbc ih => exact step b ih c hbc

lemma reachable_safe {α : Type} (states : List α) (next : α → List α)
    (contains safe : α → Bool)
    (hcontains : ∀ s, contains s = true → s ∈ states)
    (hclosed : states.all (fun s => (next s).all contains) = true)
    (hsafe : states.all safe = true)
    {start finish : α} (hstart : contains start = true)
    (hreach : Relation.ReflTransGen (fun a b => b ∈ next a) start finish) :
    safe finish = true := by
  exact List.all_eq_true.mp hsafe finish
    (reachable_mem states next contains hcontains hclosed hstart hreach)

end ResourceCertificate

namespace ResourceCertificate

def searchIndex {α : Type} [BEq α] (lt : α → α → Bool)
    (get : Nat → α) (bound : Nat) (needle : α) : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, lo, hi =>
      if lo < hi then
        let mid := (lo + hi) / 2
        if mid < bound then
          if get mid == needle then true
          else if lt needle (get mid) then
            searchIndex lt get bound needle fuel lo mid
          else searchIndex lt get bound needle fuel (mid + 1) hi
        else false
      else false

lemma searchIndex_sound {α : Type} [BEq α] [LawfulBEq α]
    (lt : α → α → Bool) (get : Nat → α) (bound : Nat)
    (needle : α) (fuel lo hi : Nat)
    (hsearch : searchIndex lt get bound needle fuel lo hi = true) :
    ∃ i < bound, get i = needle := by
  induction fuel generalizing lo hi with
  | zero => simp [searchIndex] at hsearch
  | succ fuel ih =>
      simp only [searchIndex] at hsearch
      split at hsearch
      next hlt =>
        split at hsearch
        next hmid =>
          split at hsearch
          next heq => exact ⟨(lo + hi) / 2, hmid, eq_of_beq heq⟩
          next hne =>
            split at hsearch
            next => exact ih _ _ hsearch
            next => exact ih _ _ hsearch
        next => cases hsearch
      next => cases hsearch

lemma index_reachable_safe {α : Type} (get : Nat → α) (bound : Nat)
    (next : α → List α) (contains safe : α → Bool)
    (hcontains : ∀ s, contains s = true → ∃ i < bound, get i = s)
    (hclosed : (List.range bound).all
      (fun i => (next (get i)).all contains) = true)
    (hsafe : (List.range bound).all (fun i => safe (get i)) = true)
    {start finish : α} (hstart : contains start = true)
    (hreach : Relation.ReflTransGen (fun a b => b ∈ next a) start finish) :
    safe finish = true := by
  apply reachable_safe ((List.range bound).map get) next contains safe ?_
      ?_ ?_ hstart hreach
  · intro s hs
    obtain ⟨i, hi, heq⟩ := hcontains s hs
    exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, heq⟩
  · simpa only [List.all_map, Function.comp_def] using hclosed
  · simpa only [List.all_map, Function.comp_def] using hsafe

end ResourceCertificate

namespace ResourceCertificate

lemma chunked_all (checked : Nat → Bool) (bound width count : Nat)
    (hwidth : 0 < width) (hbound : bound ≤ count * width)
    (hchunks : ∀ k < count, (List.range width).all
      (fun j => if k * width + j < bound then checked (k * width + j) else true) = true) :
    (List.range bound).all checked = true := by
  apply List.all_eq_true.mpr
  intro i hi
  have hibound : i < bound := List.mem_range.mp hi
  have hk : i / width < count :=
    (Nat.div_lt_iff_lt_mul hwidth).mpr (Nat.lt_of_lt_of_le hibound hbound)
  have hj : i % width < width := Nat.mod_lt _ hwidth
  have hsum : i / width * width + i % width = i := by
    rw [Nat.mul_comm, Nat.div_add_mod]
  have h := List.all_eq_true.mp (hchunks (i / width) hk)
    (i % width) (List.mem_range.mpr hj)
  simpa only [hsum, ite_eq_left hibound] using h

lemma all_and_parts {α : Type} (xs : List α) (p q : α → Bool)
    (h : xs.all (fun a => p a && q a) = true) :
    xs.all p = true ∧ xs.all q = true := by
  constructor
  · apply List.all_eq_true.mpr
    intro a ha
    exact (Bool.and_eq_true_iff.mp (List.all_eq_true.mp h a ha)).1
  · apply List.all_eq_true.mpr
    intro a ha
    exact (Bool.and_eq_true_iff.mp (List.all_eq_true.mp h a ha)).2

lemma chunked_index_reachable_safe {α : Type}
    (get : Nat → α) (bound width count : Nat)
    (next : α → List α) (contains safe : α → Bool)
    (hwidth : 0 < width) (hbound : bound ≤ count * width)
    (hcontains : ∀ s, contains s = true → ∃ i < bound, get i = s)
    (hchunks : ∀ k < count, (List.range width).all (fun j =>
      if k * width + j < bound then
        safe (get (k * width + j)) && (next (get (k * width + j))).all contains
      else true) = true)
    {start finish : α} (hstart : contains start = true)
    (hreach : Relation.ReflTransGen (fun a b => b ∈ next a) start finish) :
    safe finish = true := by
  have hall := chunked_all (fun i => safe (get i) && (next (get i)).all contains)
    bound width count hwidth hbound hchunks
  obtain ⟨hsafe, hclosed⟩ := all_and_parts (List.range bound)
    (fun i => safe (get i)) (fun i => (next (get i)).all contains) hall
  exact index_reachable_safe get bound next contains safe hcontains hclosed hsafe hstart hreach

lemma chunked_searchIndex_reachable_safe {α : Type} [BEq α] [LawfulBEq α]
    (lt : α → α → Bool) (get : Nat → α) (bound width count fuel : Nat)
    (next : α → List α) (safe : α → Bool)
    (hwidth : 0 < width) (hbound : bound ≤ count * width)
    (hchunks : ∀ k < count, (List.range width).all (fun j =>
      if k * width + j < bound then
        safe (get (k * width + j)) && (next (get (k * width + j))).all
          (fun s => searchIndex lt get bound s fuel 0 bound)
      else true) = true)
    {start finish : α}
    (hstart : searchIndex lt get bound start fuel 0 bound = true)
    (hreach : Relation.ReflTransGen (fun a b => b ∈ next a) start finish) :
    safe finish = true := by
  exact chunked_index_reachable_safe get bound width count next
    (fun s => searchIndex lt get bound s fuel 0 bound) safe hwidth hbound
    (fun s hs => searchIndex_sound lt get bound s fuel 0 bound hs)
    hchunks hstart hreach

end ResourceCertificate

namespace OnceResource

abbrev State := ℕ × List ℕ × List ℕ × Bool

def values (bits : ℕ) : List ℕ := (List.range 64).filter bits.testBit

def pairMasks (op : ℕ → ℕ → ℕ) (a b : ℕ) : ℕ :=
  (values a).foldl (fun acc x =>
    (values b).foldl (fun acc y => acc ||| (1 <<< op x y)) acc) 0

def mergePools (a b : ℕ) : ℕ := pairMasks (· ||| ·) a b

def addCarrier (pool k : ℕ) : ℕ := pool ||| mergePools pool (1 <<< k)

def live (used loc : ℕ) : Bool :=
  if loc = 0 then !used.testBit 0
  else if loc < 4 then !used.testBit 0 || !used.testBit loc
  else !used.testBit (loc - 3)

def prune (s : State) : State :=
  (s.1, (List.range 7).map (fun i =>
    if live s.1 i then s.2.1.getD i 1 else 1), s.2.2.1, s.2.2.2)

def sortedInsert (k : ℕ) : List ℕ → List ℕ
  | [] => [k]
  | x :: xs => if k ≤ x then k :: x :: xs else x :: sortedInsert k xs

def zeroSort : List ℕ → List ℕ
  | [] => []
  | x :: xs => sortedInsert x (zeroSort xs)

def insertZero (k : ℕ) (zs : List ℕ) : List ℕ := zeroSort (k :: zs)

def basis : ℕ → ℕ | 0 => 0 | 1 => 25 | 2 => 42 | _ => 52

def rightPool (ps : List ℕ) (g : ℕ) : ℕ :=
  if g = 0 then mergePools (mergePools (ps.getD 1 1) (ps.getD 2 1)) (ps.getD 3 1)
  else mergePools (1 <<< basis g) (ps.getD (g + 3) 1)

def groupNext (s : State) : List State :=
  (List.range 4).flatMap fun g =>
    if s.1.testBit g then [] else
    (values (pairMasks (· &&& ·) (s.2.1.getD g 1) (rightPool s.2.1 g))).filterMap
      fun k => if k = 0 then none else
        some (prune (s.1 ||| (1 <<< g), s.2.1, insertZero k s.2.2.1, s.2.2.2))

def forkNext (s : State) : List State :=
  if s.2.2.2 then [] else s.2.2.1.map fun k =>
    prune (s.1, s.2.1, insertZero k s.2.2.1, true)

def liftNext (s : State) : List State :=
  s.2.2.1.flatMap fun k => (List.range 7).filterMap fun loc =>
    if live s.1 loc then
      let old := s.2.1.getD loc 1
      let new := addCarrier old k
      if new = old then none else
        some (prune (s.1, s.2.1.set loc new, s.2.2.1.erase k, s.2.2.2))
    else none

def discardNext (s : State) : List State :=
  s.2.2.1.map fun k => prune (s.1, s.2.1, s.2.2.1.erase k, s.2.2.2)

def combineNext (s : State) : List State :=
  s.2.2.1.flatMap fun a => (s.2.2.1.erase a).flatMap fun b =>
    [a &&& b, a ||| b].filterMap fun k => if k = 0 then none else
      some (prune (s.1, s.2.1, insertZero k ((s.2.2.1.erase a).erase b), s.2.2.2))

def successors (s : State) : List State :=
  groupNext s ++ forkNext s ++ liftNext s ++ discardNext s ++ combineNext s

def initial : State := (0, List.replicate 7 1, [63], false)

def listLess : List ℕ → List ℕ → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a = b then listLess as bs else decide (a < b)

def stateLess (a b : State) : Bool :=
  if a.1 ≠ b.1 then decide (a.1 < b.1)
  else if a.2.1 ≠ b.2.1 then listLess a.2.1 b.2.1
  else if a.2.2.1 ≠ b.2.2.1 then listLess a.2.2.1 b.2.2.1
  else !a.2.2.2 && b.2.2.2

def safe (s : State) : Bool := !s.2.2.1.contains 56

def packedPools : ℕ := 0xc010040000000001c000000000000001a010000002000001a0000000000000019010000000000101900000000000000188000400020000018800000000000001840004000001000184000000000000018200000102000001820000000000000180100001000000018010000000010001801000000000000180010001000100018001000000000001800004010000000180000400000001018000040000000001800001010000010180000100000000018000000100000001800000000201000180000000020001018000000002000001800000000101010180000000010000018000000000010001800000000000010180000000000000015410040001000001501004000000010150000400000000014410040000010001441000000000000140100400000000014000000001000001400000000000000132100100020000013010000002000101300000000200000122100001020000012210000000000001201000000200000120000100000000012000000000000001101000000000010110000000000000010e010400020000010c000400020100010c000000020000010a000401020000010a0004000000000108010000000000010800040002000001080000000000000104000400000100010400000000000001020000010200000102000000000000010011000100010001001100000000000100100001000000010010000000010001001000000000000100010001000100010001000000000001000005010000010100000500000000010000040100000001000004000000010100000400000000010000010100000101000001000000000100000001000000010000000003010101000000000300000100000000020100010000000002000101000000000200000100000000010101010000000001000001000000000001000100000000000001010000000000000001

def poolLookup (i : ℕ) : ℕ := (packedPools >>> (64 * i)) &&& 0xffffffffffffffff

def poolA0 : ℕ := 0x1a00000198000019000001880000180000017800000c000000b800000b006e00a802800a800400a800000a8000dca000050a000034a000028a007200a006e00a002a00a002800a000400a000000a00000088000008000000780000070000dc680005068000346800028680000068000dc5000050500003450000285000000500011c000010800000fc0006edc00028dc00000dc00000c400000bc00000580006e5000028500000050000003c000003400000280008e00000780000072000006e0000052000004e000002a0000028000000e000000a0000004000000000000

def poolA1 : ℕ := 0xa826e00a022800a020400a020000a02000238100021010001e010001c810001c010001b810001881000078100007010000681000298000029000002880000280000027800002700000268000026000002580000250000024000a023800402380000238000022800002180000210000020000001f800001f000001e806e01e002801e000a01e000401e000001e000001d800001d006e01c800a01c800401c800001c800001c0000ddb800051b800035b800029b807801b807201b806e01b805201b804e01b802801b800e01b800a01b800401b800001b800001b000001a80

def poolA2 : ℕ := 0x6e00014280001400000140000a130001b920000a12000000f000068e0001e0d0001c8d0001b8d0000a8d0000a0d000070d000068d000050d00dc00d005000d003400d002800d000000d000068c0001b8b000068b0001e0a0001b8a0000a8a0000a0a000070a000068a000050a00dc00a005000a003400a002800a000000a0001b870001b86000238500021050001f850001e050001c850001c056e01b852801b850a01b850401b850001b850001b840001b8300018830001783000238200021020001e020001c820001c026e01b820a01b820401b820001b8200018820000b02

def poolA3 : ℕ := 0x470000042000003f0001bbc0001bb90000a390001bb800006b80001e370001cb70001c370a01bb70401bb70001bb70000ab70400a370000a37000073700006b7000053700dc0370050037003403700280376e00037280003700000370000031000002f0001ba90001ba70001ba600006a60001ba500006a50001b9e0001b9d0001b9c0000a1c0001b9b0000a1b0001b9a0001b9900000160000a150001e140001c140a01b940001b940000a940400a140000a1400007140000694000051400dc014005001400340140028014

def poolALookup (k : ℕ) : ℕ := (if k < 2 then (if k < 1 then poolA0 else poolA1) else (if k < 3 then poolA2 else poolA3))

def poolB0 : ℕ := 0x142b702142810a0408500042b80015b800a180050a0028100140000a0238200f01007208037040038200141000008053000290001200008e000420001f0000f0000720003800ddb801adc0056e000b70001b8000780003a0000e00dc6801a340051a0008d0000680001c0000c01b8500342800a140010a0000500dc0801a0400502000810000080840003c0001c0000dc0003c0001d000070000340000c0000500000800000000

def poolB1 : ℕ := 0x201b8000dc0375c01bad00dd6006eac037540202900fd48070a4037520002900dd400809c0374e0002700dcc006e5c0472c01f9600f0b0072580372c01f9500dca80005404b28025140124a008e50046280229400fca0078500392801b940000a000a24037100028800183800a1c0000e0238600dc3000e180050c000866e0030500180800c000060144280a0140470a01d0500e02816e140370a0048500202800e140060a04285

def poolB2 : ℕ := 0xddc803ce40057200039011dc006ee000f70006b80005c3700e068070040380001c00aadc0546e028b70141b809adc04c6e023b70115b8088dc0426e0203700fdb8074dc0396e01c371addb816edc0376e01237008db8044dc0216e01037007db803cdc01d6e008b70041b801edc00e6edc6b71a35b851adc08d6e006b70021b800edc6856e002b76e05b8d02dc0816e000b78401bb800ddb806e780373a01b8e00dc6806e14037

def poolB3 : ℕ := 0x6f54037a801bd100de800013c0009c01bcd00166806f3000598006cb00365006f240428e01fc700e23806f1c0008e01bc5007a2803b1400d8800043011e100730803784007c200361000f0800584000c26e0210d0108280840404200021001b0403780006c00109f806efc01e7e007bf0039f801afc0007a007bc0035e0002f0680780403c0001e006ee80057402139

def poolBLookup (k : ℕ) : ℕ := (if k < 2 then (if k < 1 then poolB0 else poolB1) else (if k < 3 then poolB2 else poolB3))

def packedZeroFork : ℕ := 0x7ffd03f607e80f981eb03c6076c0e981cbff4ba6940d181a20307fd574aad55502a605480a1ff05d20b541608281030205fb37466d4cd819acb3406580ca0187fa17442d485810aca1504280830105f917422d445808ac9150229045008601080008000

def poolALookupCode (i : ℕ) : ℕ :=
  (poolALookup (i / 64) >>> (28 * (i % 64))) &&& 0xfffffff

def poolBLookupCode (i : ℕ) : ℕ :=
  (poolBLookup (i / 64) >>> (21 * (i % 64))) &&& 0x1fffff

def zeroForkLookup (i : ℕ) : ℕ := (packedZeroFork >>> (15 * i)) &&& 0x7fff

def decode (code : ℕ) : State :=
  let a := poolALookupCode ((code >>> 4) &&& 255)
  let b := poolBLookupCode ((code >>> 12) &&& 255)
  let z := zeroForkLookup ((code >>> 20) &&& 63)
  (code &&& 15,
    [poolLookup (a &&& 127), poolLookup ((a >>> 7) &&& 127),
      poolLookup (b &&& 127), poolLookup ((b >>> 7) &&& 127),
      poolLookup ((a >>> 14) &&& 127), poolLookup ((a >>> 21) &&& 127),
      poolLookup ((b >>> 14) &&& 127)],
    (List.range ((z >>> 1) &&& 3)).map (fun i => (z >>> (3 + 6 * i)) &&& 63),
    z.testBit 0)

def block0 : ℕ := 0x4810841004f10401244108421cc01084100421068400417e15105f8204185001cdf800417e001048054412008104900073200010480004100ed005fb800120e000403980100e200423803300e000403800000e0005f908012042004013c010049004210833004200401080000420068400017e15005f8200185000cdf800017e00001f80001201500480200124000cc8000012000000800001001700420543300150040054000015004202033000800400200000080cc200001080000020003400000cc000032000000400000000000

def block1 : ℕ := 0x4815c811157204016c810059204215c8102572cc015c950057204015c8000572070d08818c42205f910818042255f908817e422051508813f42204d524813544204e5088137422ccd508953542204d5088035422049d088120442048908952042204810881114920445108115422044d08b311422544508811142200450881004b204092495004920401248108442040910b3004425401108100442000110810a4225421088108422cc090895024220409088002422cc01089a0042258010895004225001088100422000108817e421

def block2 : ℕ := 0xccd400d53500304d400c035003049c00c120023048800d520003048000c111083044408c115003044c00f311003544400c111003004400c1000a3040820d500083040020c108023040808f300023540008c100023000008c10a003542000c108003cc0800d502003040800c002003cc0000da00003580000d500003500000c100003000000c100f720403c88135ed20447b48100ef2040bb49500ed20403b4810096205fa3c81358f204823c81118f204024c810091204223c81028f2cc023c95008f204023c80008f205f95c8135572

def block3 : ℕ := 0x60481337e2048df881017e20401f88101dd004076c0101d3154074c3501d700407580133d30048f4c0101d3004034c0101a900406843501a30048e840101a100406405501900d40650010193004ce40012390004064001009000405f86501811548df855017e15406143501810d4cdf835237e0d405f835007e0d4061c01238500406140133810048e04010181004020401337e00499f801247e0048df801227e00405f801007e004070c00c18c00305f808c18000355f800c17e003051400c13f00304d420c13502304e400c137003

def block4 : ℕ := 0x47001411b005cc60016318005046001401800504006541041558c0055410015504203541040d5cc003563000d504003540000d5042c01630800504200173040058c10014104005001001730000598000164000058c00016200005040001400000505fbe5017ee84074f810190e0405fb910181e048dfb81017ee0405fad5017eb14074ead01a1ab40642ad017eaf405fab50185ab40606ad337eab48dfaad017eab401faad017e604074d09019042405f93501814248df909017e424074c8101a1204064081017e24405f8890185204

def block5 : ℕ := 0xcecc81a3b32060ecc8181b320602cc8181a420606888183a120606848181952060644818390206064081818b2060628818189206ce2081a3882060e2081818820602208181862060e148181852060608818381206060481b37f2068dfc81837f20605fc81807f206cdf881a37e20629f881887e20611f881837e20609f881817e20601f881810060504610941004d5041109630042504010941202050460814100245040089410820504108173002058c00814100205000081412900504803541230058c8001412000504605541180d5

def block6 : ℕ := 0x553109834c426053109804c426051d0981464260d1509814542605050981404260cfd09813f42604f909813d42604f109b33b42654ed09833b42604ed09803b42604e909833942604e50981384260cdd098137426ccd90995364260cd909813642600d909b33542654d5098a3542618d50984354260cd509823542604d5098035426074c9581b325606849581902560620958185256060495817f256cdf895a37e2560df895817e25601f89581e020607608181d42060f4c8181d320606e88181b820606dc8181b620606d48181b4206

def block7 : ℕ := 0x5f95d814c57604ed5d81365760cd55d8135576070d41817e506053141814550604fd41813b50604e541813750604d941b33550654d541833550604d541803550607c90981f142607650981d5426574d0981d342607250981c742607190981c5426071109a3c34260f0d0981c342606cd09819a42606650981924265641098190426063509a38c4260631098188426061109818342656050981814268e0109818042605fd09ae7e4268df909987e42655f909837e42605f90981534260545098150426053d09814e426053509b34c426

def block8 : ℕ := 0x5fec5837eb1605fac581359a605fa618135946074e3d81908f606063da37e8f605fa3d814c8f604ee3d81368f60cd63d81358f605f9e5813578604d5d981c375605f9d5814c7560515d5813f75604edd5813975604ddd58136756ccd5d595357560cd5d5813575600d5d5817e726074dc581b37160685c581907160621c581857160605c5817f716cdf9c5a37e7160df9c5817e71601f9c5817e6c605f9ad817e616070d8181b36060631818188606060181817f60655f981837e60605f98181355c6074d5d819057606055da37e576

def block9 : ℕ := 0xcc3001e30c007543001c30c007043001c00c007042401c308007042001c107007041801c105007541001c304007041001c1030078c0801c302007040801f3010078c0401d5010070c0401c101007000401f300007b80001e300007600001d500007280001c800007180001c4000070c0001c200007040001c00000704d7d1817ef3604d7c1814ced604efb58136ed60cd7b58135ed605fba581b3e860623a1817fe860dfba1817ee8605fb5d817ed6605fae1817eb76070ed5818cb560602d5957eb5605fad5817eb2606cec58188b16

def block10 : ℕ := 0x684020162008057056015c0f8057022015c048cd7002295c008057002005c00804a856012a0f804a822012a048cca802292a00804a802002a00804806a0120168a4805601201580480460120108cc803e29200f804803e00200f804802e29200880480223320048a4801201200480080123320008ac80022a20008a4800228200080480020020008049401c1210070c8001c120007047c01c11e007047401c11a007046401d5180070c6001c118007045801c114007044801e3110070c4401c111007044001c10f007043801c10d007

def block11 : ℕ := 0x400464100109cc003e69000f904003e40000f904002e69000890400227300049a4001241000490000127300009ac00026a00009a40002680000904000240000090483ea0120ea8057382012ae080483960120e18a483820120e0804832a0120c780686f6015cbd804aaf60120c3804830a0120bf80482fa3320bd8a482f60120bd80082f6012063805710a012a42804813a0120468a4810a01204280684a6015c29804a8a601203280480c601202d80480ae3320298a480a601202980080a601e600806b00201a10f806841229a1008

def block12 : ℕ := 0x4a8aa8c2a29a04a8a681262da0498ae81262aacc98a6a92629a3098a6812629a0098a681202ea3080b681202da0480b28c202ba0480aeb3202aaa480aa8c202aa0480aa80202aacc80a6a92029a4880a6912029a3480a68c2029a2c80a6812029a0080a68100639056d0a41004e904011a690042904010a417e299056ca641003290400c641002d90400ae7300299a400a641002990000a641e500905f83e417e049a5f802417e009056c56415b0f9056c22415b049cd6c02695b009056c02405b00904006a4100169a400564100159

def block13 : ℕ := 0x30810a812042a045d26811744a045d0eb31742a545d0a8c1742a045d0a801742a04452a8c1149a044526811145a304512811144acc450e951143a30450e811143a00450eb31142a54450a921142a38450a8d1142a30450a8b1142a04450a801142a0684ce815c33a04c4ce812a33a0498ce812036a0480d6812034acc80cea92033a3080ce812033a0080ce81bf29a0694a681a12aa3284a681a129a059ca6815d29a0570aa8c5c29a0570a6813429a04c8a681312da04c4ae81312aaccc4a6a93129a30c4a6813129a00c4a6812b29a

def block14 : ℕ := 0x48146811751a044552811153a04454ab31151a5445468c1151a044546801151a06f50a818e42a06310e8c8c42a06310a817542a05c50a815e42a057112955c42a05710a815642a05250a814546aa5150a814542a05090a813f43a30fd0a813f42a04cd0a813142a04c10a812f49a04bd12812f43accbd0a952f42a30bd0a812f42a00bd0a812d42a04b10a812a44a54a90a812a42a04a10a812746a049d0ea92742a309d0a812742a04990a812048a04811e952046a04811aa92044a048112812043ac0810aa92042a64810a952042a

def block15 : ℕ := 0xa4823e81208fa045e3e811190a30463e81118fa04822a811188a04461e818c82a04fe0a812f82a049e0a812082a045e0a811185a044612811183acc460a951182a30460a811182a00460a81207fa0685ee815c7ba04c5ee812a7ba0499ee81207ea0481f681207cacc81eea9207ba3081ee81207ba0081ee812070a0481be812066a05158e813163a049d8e812663a048196812064a54818e8c2063a04818e81115da05715e812f57a04a95e81205aaa4815e812057a045d5e811158a30455e811157a063146813f51a04bd46812751a

def block16 : ℕ := 0x4001ac10005b540012cc0004b040012c10003ba4000acc0002b04000af30001ba40006d50001b300006c10001b000006f30000bc00002e90000b640002d50000b480002d10000b380002cd0000b300002cb0000b040002c00000b0447da8120f5a0447c6812feda045fb68111eea3047b68111eda0483b28131eaa049baa8120eba3083aa8120eaa0483768120dca04833a8120cda05172a8127caa04832e9520caa04832a8120c9a04c71e8126c7a0483228c20c7a04831e81119ba048266811195a05723e812f8fa04aa3e812092a

def block17 : ℕ := 0x58c0301620cc718803016200c057c57015f0fc057c33335f00ca57c031c5f00c057c03005f00c0570631c5c15c057057015c12c71703f015c0fccd7033295c0cc717033015c0cc017033335c00ca57003205c00c7d70031d5c00c7170031b5c00c057003005c00c06f002c17e01b31f802c17e00b05d002c17000b059802c15b02b056c06d55b00b316c02c15b00b055402c13504b04d406e93500b30d402c13500b04b822c12e04b04b80ac12e01bccb802e92e00b54b802cc2e00b04b802c02e00b040026cc0008b040022c10007b

def block18 : ℕ := 0x3280301b200c06c40301ac0dc8eb00301ac00c06a80301a90fc06a43329a900c72a40301a900c069c0301a114c06844f23a10fc06843f29a10dc06843701a10ccc6840329a100c96840323a100c72840301a100c06585701960dc065833339600c8e58031c9600c065803009600c0640631c9015c06405701900ec72403701900dcce403323900cc72403301900cc024033339000c8e4003209000c7a40031d9000c7240031b9000c064003009000c05b403016c00c05a45701690fc05a433336900ca5a4031c6900c05a403006900c

def block19 : ℕ := 0x7988301ca20c06b08301a123ca6848301a120c065883019021c724083019020c07986f01db1bc07286f01a91bc06846f01961bc06407f01901dc06407333901bc8e406f1c901bc06406f00901bc05a46f01621bc057c6f015c1fc05707b015c1cccd706f295c1bc71706f015c1bc01706f01f600c07d40301ea00c07a40301e800c07983701e60cc8f98031ce600c07980301e100c077c0301dd0fca7740301dd00c07700301db0cc736c0301db00c073c0301ce00c07300301ca15c07283701ca0cccf280323ca00c73280301ca00c

def block20 : ℕ := 0x686bb29a1abc0686af0196abc0642b31c90abc0642af0190a6c05729b015ca4c06428b0190a1c05728701e69cc076e7301ca9cc06a67301a19cc065a730190a0c06427b01909dcce427323909cc72427301909cc02427301699cc058a73015f9cc057283015c9fc057277335c9cca572731c5c9cc057273005c9cc06417b015c5ec07290b019642c0641331c9042c06410b016942c057d0b015c4cc71710b015c42c0684f301a13ac0570df01dd29c06a4a701a130c8e84a701a129c05a4a7015f29c0570bf1c5c29c0570a7019026c

def block21 : ℕ := 0x40053410013d04004b63000fd70003f41000fd04003b69000dd70003741000ddcc003369000cd8c00335c000cd04003340000cdcc0003710000da40003650000d8c0003600000d7c00035e0000d7400035c0000d6c0003410000d0000034190f8c0573e30190e7c05739f01cae0c065b830190e3c7243830190e0c05a783015fe0c05738f1c5ce0c05738301a1dfc06877b015ccfc068717015cc4c0776f701a9bdc06870723a1bdc0686f70169bdc057ef7015cc0c7172f7015cbdc0642e701a1b3c0642c301e6abc072aaf01acabc

def block22 : ℕ := 0x6bc8383ac20e06b08381a820ea6908381a420ebe8483a9a120e86848389a120e0e848381a120e066083819720e0e5883819620e725483819520e8640839c9020e1e4083839020e064083838820e06208381ca1be06586f9c901be06406f81691be057c6f9c5c1be05706f81005ed0401335c0042d04010b41003cd0400eb410037d0400c341002fd8c00a75c0029d0400a7410026d04008f410021da400835c0020d04008341001fd04007b41001dd04007373001bda4006f63001bd70006f41001bd00006f410018d700057410015d

def block23 : ℕ := 0x694a7ada129e9e84a7a3a129e4284a78ca129e0684a7816f29e05b8a7816a29e31a4a7816929e05a0a79c6729e059ca7816129e0580a78c5f29e057ca79c5d29e0574a7a75c29e7170a78f5c29e3170a7815c29e04c8a78c3129e04c4a7819028e06849f819027e06e09b819526e0e409b819026e07989781ca25e06b097a9a125e068497819625e724097819025e06209781f420e07cc8381e720e0f988381e620e07488381d120e07408381cb20e0f288381ca20e06ec83a9ba20e06e88381b920e72e08381b820e06dc8381b020e

def block24 : ℕ := 0x5090b8c4142e05050b933f42e30fd0b853f42e0cfd0b813f42e0ced0b813b42e04c10b8c2f42e04bd0b81a141e06850381a13fe0684fb81a13de0708f381bf3ce06e8f381a63ce0694f381a43ce4e84f38ca13ce0e84f381a13ce0684ef81c23ae0698eb93a13ae0684eb815c39e0684e3815c38e059cdf815d37e3170df815c37e0774cf81a933e8e84cf81a133e05a4cf815f33e7170cf815c33e04c4cf81f029e07b8a781e429e0778a78cdd29e0774a781c029e8efca781bf29e06b8a781ad29e06aca78ca929e06a4a7a3a529e

def block25 : ℕ := 0x32310b818c42e05f50b817c42e05ed0b817a42e05e50b817842e05dd0b817642e85d50b9c7542e0dd50b817542e05cd0b817242e85c50b817142e05b90b816b42e55a50b816942e05950b816442e05810b955f42e057d0b9c5e42e05790bac5c42e9d710b9c5c42e5d710b955c42e05710b815a42e05650b815842e055d0b835642e05590b815442ea54d0b815342e05490b8c5142e05450b815042e052d0b814a42e0d250b814942e05210ba94742e051d0baf4542ea5150b934542e25150b834542e05150b814442e050d0b834242e

def block26 : ℕ := 0x8e3147818c51e054547814151e0cfd47813f51e04bd47817550e055943814950ea51543814550e0509438c3f50e04fd43813b50e07bd0b81ed42e07b10b81eb42e078d0b81e242e07690b8cd942e07650b81d042e07350b95ca42e07290b81c842e731d0b81c742e07050b81be42e8ef50b81bd42e06810b819f42e06790b819d42e06710b819b42e9e690b9c9a42e32690b819a42e9e650b819942e065d0b959642e06590bac9042e86410b9c9042e5e410b959042e06410b818f42e8e390b818e42eb6310ba38c42e4e310b908c42e

def block27 : ℕ := 0x5d5d7815675e0525d7a94575e0515d7814275e30fdd7813f75e04edd781a174e0641cf81e671e0729c781ac71ea685c781a171e0659c79c9071e0641c7818871e0515bb81456de0631ab818c69e0641a3815c68e06419f815c67e054d8f814763e0d158f814563e06698b819962e05718b81bd60e0639838c8c60e06318381905fe05d57f81715fe071d7b819a5ee56417b81905ee05d57b815e5ee55717b815c5ee07295f819657e72415f819057e05a55f815f57e71715f815c57e04fd5b818c55e051557813f55e076547819a51e

def block28 : ℕ := 0x686a38190a8e06429f815ca7e071e9b819aa6e56429b8190a6e05d69b815ea6e55729b815ca6e0572978167a4e0576938c5ca4e0572938190a3e06e28b8195a2e0e428b8190a2e064287815ca1e06425f815c97e072a3f81968fe72423f81908fe05a63f815f8fe71723f815c8fe04fe3b818c8de051637813f8de06863381a18be063227813f86e07660b819a82e8e320b818c82e05460b814182e0cfe0b813f82e04be0b81a181e05720381dd7be06a5efa3a17be0685ef81697be057def9c5c7be0571ef81317be0515eb813f77e

def block29 : ℕ := 0x2f0000fb40003ec0000fa40003e70000f8c0003e10000f700003d70000f540003d30000f400003cf0000f300003c90000f1c0003c50000f0c0003c10000f05176f81a1dae05176781a1d8e06335781a1d4e06334f81a1d2e064347815cd1e064343815cd0e0517338153cae051f2b8345cae05172b81a1c6e06eb1781a4c5e0e871781a1c5e0572f3819abbe0666ef815cbbe0686eb815cbae0632db81bdb5e063ad78c8cb5e0632d781a1b4e06fecf81a5b3e3286cf81a1b3e0642ab8190a9e05d6a78171a9e

def blockLookup (k : ℕ) : ℕ := (if k < 15 then (if k < 7 then (if k < 3 then (if k < 1 then block0 else (if k < 2 then block1 else block2)) else (if k < 5 then (if k < 4 then block3 else block4) else (if k < 6 then block5 else block6))) else (if k < 11 then (if k < 9 then (if k < 8 then block7 else block8) else (if k < 10 then block9 else block10)) else (if k < 13 then (if k < 12 then block11 else block12) else (if k < 14 then block13 else block14)))) else (if k < 22 then (if k < 18 then (if k < 16 then block15 else (if k < 17 then block16 else block17)) else (if k < 20 then (if k < 19 then block18 else block19) else (if k < 21 then block20 else block21))) else (if k < 26 then (if k < 24 then (if k < 23 then block22 else block23) else (if k < 25 then block24 else block25)) else (if k < 28 then (if k < 27 then block26 else block27) else (if k < 29 then block28 else block29)))))

def getCode (i : ℕ) : ℕ :=
  (blockLookup (i / 64) >>> (26 * (i % 64))) &&& 0x3ffffff

def getState (i : ℕ) : State := decode (getCode i)

def contains (s : State) : Bool :=
  ResourceCertificate.searchIndex stateLess getState 1917 s 12 0 1917

def checked (i : ℕ) : Bool := safe (getState i) && (successors (getState i)).all contains

def chunkCheck (k : ℕ) : Bool :=
  (List.range 64).all (fun j => if k * 64 + j < 1917 then checked (k * 64 + j) else true)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk0_closed : chunkCheck 0 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk1_closed : chunkCheck 1 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk2_closed : chunkCheck 2 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk3_closed : chunkCheck 3 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk4_closed : chunkCheck 4 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk5_closed : chunkCheck 5 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk6_closed : chunkCheck 6 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk7_closed : chunkCheck 7 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk8_closed : chunkCheck 8 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk9_closed : chunkCheck 9 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk10_closed : chunkCheck 10 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk11_closed : chunkCheck 11 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk12_closed : chunkCheck 12 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk13_closed : chunkCheck 13 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk14_closed : chunkCheck 14 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk15_closed : chunkCheck 15 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk16_closed : chunkCheck 16 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk17_closed : chunkCheck 17 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk18_closed : chunkCheck 18 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk19_closed : chunkCheck 19 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk20_closed : chunkCheck 20 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk21_closed : chunkCheck 21 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk22_closed : chunkCheck 22 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk23_closed : chunkCheck 23 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk24_closed : chunkCheck 24 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk25_closed : chunkCheck 25 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk26_closed : chunkCheck 26 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk27_closed : chunkCheck 27 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk28_closed : chunkCheck 28 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk29_closed : chunkCheck 29 = true := by decide +kernel

lemma all_chunks_checked : (List.range 30).all chunkCheck = true := by
  change ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29] : List ℕ).all chunkCheck = true
  simp only [List.all_cons, List.all_nil, chunk0_closed, chunk1_closed, chunk2_closed, chunk3_closed, chunk4_closed, chunk5_closed, chunk6_closed, chunk7_closed, chunk8_closed, chunk9_closed, chunk10_closed, chunk11_closed, chunk12_closed, chunk13_closed, chunk14_closed, chunk15_closed, chunk16_closed, chunk17_closed, chunk18_closed, chunk19_closed, chunk20_closed, chunk21_closed, chunk22_closed, chunk23_closed, chunk24_closed, chunk25_closed, chunk26_closed, chunk27_closed, chunk28_closed, chunk29_closed, Bool.and_self]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma initial_contains : contains initial = true := by decide +kernel

lemma reachable_safe {finish : State}
    (hreach : Relation.ReflTransGen (fun a b => b ∈ successors a) initial finish) :
    safe finish = true := by
  apply ResourceCertificate.chunked_searchIndex_reachable_safe stateLess getState
    1917 64 30 12 successors safe (by decide) (by decide) ?_ initial_contains hreach
  intro k hk
  change chunkCheck k = true
  exact List.all_eq_true.mp all_chunks_checked k (List.mem_range.mpr hk)

lemma reachable_no_target {finish : State}
    (hreach : Relation.ReflTransGen (fun a b => b ∈ successors a) initial finish) :
    56 ∉ finish.2.2.1 := by
  simpa [safe] using reachable_safe hreach

end OnceResource
namespace OnceGeometry

def rowSet (r : Fin 6) : Finset (Fin 10) :=
  match r.val with
  | 0 => {2, 6}
  | 1 => {3, 9}
  | 2 => {7, 8}
  | 3 => {2, 3}
  | 4 => {6, 8}
  | _ => {7, 9}

def vertexClass (v : Fin 10) : Fin 7 :=
  match v.val with
  | 0 => 0
  | 1 => 1
  | 4 => 2
  | 5 => 3
  | 2 => 4
  | 6 => 4
  | 3 => 5
  | 9 => 5
  | _ => 6

def port (g : Fin 4) (right : Bool) : Finset (Fin 10) :=
  if right then match g.val with
    | 0 => {1, 4, 5}
    | 1 => {2, 6}
    | 2 => {3, 9}
    | _ => {7, 8}
  else match g.val with
    | 0 => {0}
    | 1 => {1}
    | 2 => {4}
    | _ => {5}

def locations (g : Fin 4) (right : Bool) : Finset (Fin 7) :=
  if right then match g.val with
    | 0 => {1, 2, 3}
    | 1 => {4}
    | 2 => {5}
    | _ => {6}
  else {⟨g.val, by omega⟩}

lemma port_class : ∀ (g : Fin 4) (b : Bool) (v : Fin 10),
    v ∈ port g b ↔ vertexClass v ∈ locations g b := by decide

lemma support_class {S : Finset (Fin 10)} {g : Fin 4} {b : Bool}
    (hS : S ⊆ port g b) {v : Fin 10} (hv : v ∈ S) :
    vertexClass v ∈ locations g b := (port_class g b v).mp (hS hv)

lemma port_locations_live {used : ℕ} (hu : used < 16) {g : Fin 4}
    (hg : used.testBit g.val = false) (b : Bool) {loc : Fin 7}
    (hl : loc ∈ locations g b) : OnceResource.live used loc.val = true := by
  have h : ∀ (u : Fin 16) (g : Fin 4) (b : Bool) (loc : Fin 7),
      u.val.testBit g.val = false → loc ∈ locations g b →
      OnceResource.live u.val loc.val = true := by decide
  exact h ⟨used, hu⟩ g b loc hg hl

def bits (f : Fin 6 → Bool) : BitVec 6 :=
  BitVec.ofBoolListLE [f 0, f 1, f 2, f 3, f 4, f 5]

def mask (f : Fin 6 → Bool) : ℕ := (bits f).toNat

lemma bits_get (f : Fin 6 → Bool) (r : Fin 6) : (bits f).getLsbD r.val = f r := by
  unfold bits
  rw [BitVec.getLsbD_ofBoolListLE]
  fin_cases r <;> rfl

lemma bits_or (f g : Fin 6 → Bool) : bits (fun r => f r || g r) = bits f ||| bits g := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  have hf := bits_get f ⟨i, hi⟩
  have hg := bits_get g ⟨i, hi⟩
  have hr := bits_get (fun r => f r || g r) ⟨i, hi⟩
  simpa only [BitVec.getLsbD_eq_getElem hi, BitVec.getElem_or] using hr.trans (congrArg₂ (· || ·) hf.symm hg.symm)

lemma bits_and (f g : Fin 6 → Bool) : bits (fun r => f r && g r) = bits f &&& bits g := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  have hf := bits_get f ⟨i, hi⟩
  have hg := bits_get g ⟨i, hi⟩
  have hr := bits_get (fun r => f r && g r) ⟨i, hi⟩
  simpa only [BitVec.getLsbD_eq_getElem hi, BitVec.getElem_and] using hr.trans (congrArg₂ (· && ·) hf.symm hg.symm)

lemma mask_or (f g : Fin 6 → Bool) : mask (fun r => f r || g r) = mask f ||| mask g := by
  simp [mask, bits_or]

lemma mask_and (f g : Fin 6 → Bool) : mask (fun r => f r && g r) = mask f &&& mask g := by
  simp [mask, bits_and]

lemma mask_lt (f : Fin 6 → Bool) : mask f < 64 := by
  exact (bits f).isLt

def rawMask (S : Finset (Fin 10)) : ℕ :=
  mask (fun r => decide ((S ∩ rowSet r).Nonempty))

lemma rawMask_port : ∀ (g : Fin 4) (b : Bool),
    rawMask (port g b) = if b then OnceResource.basis g.val else 0 := by decide

lemma rawMask_empty : rawMask ∅ = 0 := by decide

lemma rawMask_union (S T : Finset (Fin 10)) : rawMask (S ∪ T) = rawMask S ||| rawMask T := by
  unfold rawMask
  have h : (fun r => decide (((S ∪ T) ∩ rowSet r).Nonempty)) =
      (fun r => decide ((S ∩ rowSet r).Nonempty) || decide ((T ∩ rowSet r).Nonempty)) := by
    funext r
    simp [Finset.union_inter_distrib_right]
  rw [h, mask_or]

end OnceGeometry
namespace OnceGeometry

open PEqualNP.Outside.L_meta_2590.DAGBridge.DagTools

def rowInput (r : Fin 6) : Fin 10 → Bool := fun v => decide (v ∈ rowSet r)

def wireMask (D : Dag) (w : ℕ) : ℕ := mask (fun r => val D (rowInput r) w)

lemma wireMask_lt (D : Dag) (w : ℕ) : wireMask D w < 64 := mask_lt _

lemma wireMask_gate {D : Dag} (hS : Strict 10 D) {j : ℕ} (hj : j < D.length) :
    wireMask D (10 + j) = if tag D j then
      wireMask D (opA D j) &&& wireMask D (opB D j)
      else wireMask D (opA D j) ||| wireMask D (opB D j) := by
  have hfun : (fun r => val D (rowInput r) (10 + j)) =
      (fun r => gop (tag D j) (val D (rowInput r) (opA D j)) (val D (rowInput r) (opB D j))) := by
    funext r
    exact val_gate hS _ j hj
  unfold wireMask
  rw [hfun]
  cases tag D j <;> simp only [gop, Bool.false_eq_true, ite_false, ite_true, mask_or, mask_and]

lemma support_row_true {D : Dag} (hS : Strict 10 D) {w : ℕ} {r : Fin 6}
    (hh : (supp 10 D w ∩ rowSet r).Nonempty) : val D (rowInput r) w = true := by
  obtain ⟨v, hv⟩ := hh
  obtain ⟨hvs, hvE⟩ := Finset.mem_inter.mp hv
  apply val_mono hS (single v) (rowInput r) ?_ w (mem_supp.mp hvs)
  intro u hu
  have huv : u = v := by simpa [single] using hu
  subst u
  exact decide_eq_true hvE

end OnceGeometry
namespace OnceResource

lemma mem_values_iff {bits x : ℕ} : x ∈ values bits ↔ x < 64 ∧ bits.testBit x = true := by
  simp [values]

lemma testBit_singleton_iff {k x : ℕ} : (1 <<< k : ℕ).testBit x = true ↔ k = x := by
  simp [Nat.shiftLeft_eq, Nat.testBit_two_pow]

lemma testBit_fold_or_iff (xs : List ℕ) (f : ℕ → ℕ) (acc z : ℕ) :
    (xs.foldl (fun a x => a ||| f x) acc).testBit z = true ↔
      acc.testBit z = true ∨ ∃ x ∈ xs, (f x).testBit z = true := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih => simp [List.foldl_cons, ih, or_assoc]

lemma testBit_fold_pairs_iff (xs ys : List ℕ) (op : ℕ → ℕ → ℕ) (acc z : ℕ) :
    (xs.foldl (fun acc x => ys.foldl (fun acc y => acc ||| (1 <<< op x y)) acc) acc).testBit z = true ↔
      acc.testBit z = true ∨ ∃ x ∈ xs, ∃ y ∈ ys, op x y = z := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, testBit_fold_or_iff, testBit_singleton_iff]
    simp [or_assoc]

lemma mem_pairMasks_iff {op : ℕ → ℕ → ℕ} {a b z : ℕ} :
    z ∈ values (pairMasks op a b) ↔
      z < 64 ∧ ∃ x ∈ values a, ∃ y ∈ values b, op x y = z := by
  simp [mem_values_iff, pairMasks, testBit_fold_pairs_iff]

lemma mem_pairMasks {op : ℕ → ℕ → ℕ} {a b x y : ℕ}
    (hx : x ∈ values a) (hy : y ∈ values b) (hxy : op x y < 64) :
    op x y ∈ values (pairMasks op a b) := by
  exact mem_pairMasks_iff.mpr ⟨hxy, x, hx, y, hy, rfl⟩

lemma mem_singleton_iff {k x : ℕ} :
    x ∈ values (1 <<< k) ↔ x < 64 ∧ k = x := by
  rw [mem_values_iff, testBit_singleton_iff]

lemma mem_singleton {k : ℕ} (hk : k < 64) : k ∈ values (1 <<< k) := by
  exact mem_singleton_iff.mpr ⟨hk, rfl⟩

lemma or_lt_64 {x y : ℕ} (hx : x < 64) (hy : y < 64) : x ||| y < 64 := by
  exact Nat.or_lt_two_pow (n := 6) hx hy

lemma mem_addCarrier_of_mem {p k x : ℕ} (hx : x ∈ values p) :
    x ∈ values (addCarrier p k) := by
  obtain ⟨hxb, hxt⟩ := mem_values_iff.mp hx
  apply mem_values_iff.mpr
  simp [addCarrier, hxb, hxt]

lemma mem_addCarrier_or {p k x : ℕ} (hx : x ∈ values p) (hk : k < 64) :
    x ||| k ∈ values (addCarrier p k) := by
  apply mem_values_iff.mpr
  have hb := or_lt_64 (mem_values_iff.mp hx).1 hk
  have hm := mem_pairMasks (op := (· ||| ·)) hx (mem_singleton hk) hb
  have ht := (mem_values_iff.mp hm).2
  simp [addCarrier, mergePools, hb, ht]

lemma mem_addCarrier_iff {p k z : ℕ} (hk : k < 64) :
    z ∈ values (addCarrier p k) ↔
      z ∈ values p ∨ ∃ x ∈ values p, x ||| k = z := by
  constructor
  · intro hz
    obtain ⟨hzb, hzt⟩ := mem_values_iff.mp hz
    simp only [addCarrier, Nat.testBit_or, Bool.or_eq_true] at hzt
    rcases hzt with hp | hm
    · exact Or.inl (mem_values_iff.mpr ⟨hzb, hp⟩)
    · have hm' : z ∈ values (pairMasks (· ||| ·) p (1 <<< k)) :=
        mem_values_iff.mpr ⟨hzb, hm⟩
      obtain ⟨_, x, hx, y, hy, heq⟩ := mem_pairMasks_iff.mp hm'
      obtain ⟨_, rfl⟩ := mem_singleton_iff.mp hy
      exact Or.inr ⟨x, hx, heq⟩
  · rintro (hz | ⟨x, hx, rfl⟩)
    · exact mem_addCarrier_of_mem hz
    · exact mem_addCarrier_or hx hk

lemma addCarrier_or_closed {p k : ℕ} (hk : k < 64)
    (hclosed : ∀ x ∈ values p, ∀ y ∈ values p, x ||| y ∈ values p) :
    ∀ x ∈ values (addCarrier p k), ∀ y ∈ values (addCarrier p k),
      x ||| y ∈ values (addCarrier p k) := by
  intro x hx y hy
  rcases (mem_addCarrier_iff hk).mp hx with hx | ⟨a, ha, rfl⟩
  · rcases (mem_addCarrier_iff hk).mp hy with hy | ⟨b, hb, rfl⟩
    · exact mem_addCarrier_of_mem (hclosed x hx y hy)
    · rw [← Nat.or_assoc]
      exact mem_addCarrier_or (hclosed x hx b hb) hk
  · rcases (mem_addCarrier_iff hk).mp hy with hy | ⟨b, hb, rfl⟩
    · have heq : (a ||| k) ||| y = (a ||| y) ||| k := by ac_rfl
      rw [heq]
      exact mem_addCarrier_or (hclosed a ha y hy) hk
    · have heq : (a ||| k) ||| (b ||| k) = (a ||| b) ||| (k ||| k) := by ac_rfl
      rw [heq, Nat.or_self]
      exact mem_addCarrier_or (hclosed a ha b hb) hk

lemma addCarrier_zero_and_or_closed {p k : ℕ} (hk : k < 64)
    (hzero : 0 ∈ values p)
    (hclosed : ∀ x ∈ values p, ∀ y ∈ values p, x ||| y ∈ values p) :
    0 ∈ values (addCarrier p k) ∧
      ∀ x ∈ values (addCarrier p k), ∀ y ∈ values (addCarrier p k),
        x ||| y ∈ values (addCarrier p k) := by
  exact ⟨mem_addCarrier_of_mem hzero, addCarrier_or_closed hk hclosed⟩

lemma sortedInsert_perm (k : ℕ) (xs : List ℕ) :
    List.Perm (sortedInsert k xs) (k :: xs) := by
  induction xs with
  | nil => exact List.Perm.refl _
  | cons x xs ih =>
      simp only [sortedInsert]
      split
      · exact List.Perm.refl _
      · exact (List.Perm.cons x ih).trans (List.Perm.swap _ _ _)

lemma zeroSort_perm (xs : List ℕ) : List.Perm (zeroSort xs) xs := by
  induction xs with
  | nil => exact List.Perm.refl _
  | cons x xs ih =>
      exact (sortedInsert_perm x (zeroSort xs)).trans (List.Perm.cons x ih)

lemma insertZero_perm (k : ℕ) (xs : List ℕ) :
    List.Perm (insertZero k xs) (k :: xs) :=
  zeroSort_perm (k :: xs)

lemma prune_pool_getD (s : State) (i : ℕ) (hi : i < 7) :
    (prune s).2.1.getD i 1 = if live s.1 i then s.2.1.getD i 1 else 1 := by
  change ((List.range 7).map (fun j =>
    if live s.1 j then s.2.1.getD j 1 else 1)).getD i 1 = _
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hi, Option.map_some, Option.getD_some]

lemma prune_idempotent (s : State) : prune (prune s) = prune s := by
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  change (List.range 7).map (fun i =>
    if live s.1 i then (prune s).2.1.getD i 1 else 1) =
      (List.range 7).map (fun i => if live s.1 i then s.2.1.getD i 1 else 1)
  apply List.map_congr_left
  intro i hi
  rw [prune_pool_getD s i (List.mem_range.mp hi)]
  split <;> rfl

lemma groupNext_mem_successors {s t : State} (h : t ∈ groupNext s) :
    t ∈ successors s := by
  simp only [successors, List.mem_append, h, true_or]

lemma forkNext_mem_successors {s t : State} (h : t ∈ forkNext s) :
    t ∈ successors s := by
  simp only [successors, List.mem_append, h, true_or, or_true]

lemma liftNext_mem_successors {s t : State} (h : t ∈ liftNext s) :
    t ∈ successors s := by
  simp only [successors, List.mem_append, h, true_or, or_true]

lemma discardNext_mem_successors {s t : State} (h : t ∈ discardNext s) :
    t ∈ successors s := by
  simp only [successors, List.mem_append, h, true_or, or_true]

lemma combineNext_mem_successors {s t : State} (h : t ∈ combineNext s) :
    t ∈ successors s := by
  simp only [successors, List.mem_append, h, or_true]

lemma group_successor {s : State} {g k : ℕ}
    (hg : g < 4) (hunused : s.1.testBit g = false)
    (hk : k ∈ values (pairMasks (· &&& ·) (s.2.1.getD g 1) (rightPool s.2.1 g)))
    (hkn : k ≠ 0) :
    prune (s.1 ||| (1 <<< g), s.2.1, insertZero k s.2.2.1, s.2.2.2) ∈ successors s := by
  apply groupNext_mem_successors
  apply List.mem_flatMap.mpr
  refine ⟨g, List.mem_range.mpr hg, ?_⟩
  simp only [hunused, Bool.false_eq_true, ↓reduceIte]
  apply List.mem_filterMap.mpr
  exact ⟨k, hk, by simp [hkn]⟩

lemma fork_successor {s : State} {k : ℕ}
    (hk : k ∈ s.2.2.1) (hf : s.2.2.2 = false) :
    prune (s.1, s.2.1, insertZero k s.2.2.1, true) ∈ successors s := by
  apply forkNext_mem_successors
  simp only [forkNext, hf, Bool.false_eq_true, ↓reduceIte]
  exact List.mem_map.mpr ⟨k, hk, rfl⟩

lemma lift_successor {s : State} {k loc : ℕ}
    (hk : k ∈ s.2.2.1) (hloc : loc < 7) (hlive : live s.1 loc = true)
    (hchange : addCarrier (s.2.1.getD loc 1) k ≠ s.2.1.getD loc 1) :
    prune (s.1, s.2.1.set loc (addCarrier (s.2.1.getD loc 1) k),
      s.2.2.1.erase k, s.2.2.2) ∈ successors s := by
  apply liftNext_mem_successors
  apply List.mem_flatMap.mpr
  refine ⟨k, hk, ?_⟩
  apply List.mem_filterMap.mpr
  exact ⟨loc, List.mem_range.mpr hloc, by simp only [hlive, hchange, ↓reduceIte]⟩

lemma discard_successor {s : State} {k : ℕ} (hk : k ∈ s.2.2.1) :
    prune (s.1, s.2.1, s.2.2.1.erase k, s.2.2.2) ∈ successors s := by
  apply discardNext_mem_successors
  exact List.mem_map.mpr ⟨k, hk, rfl⟩

lemma combine_successor {s : State} {a b k : ℕ}
    (ha : a ∈ s.2.2.1) (hb : b ∈ s.2.2.1.erase a)
    (hk : k = a &&& b ∨ k = a ||| b) (hkn : k ≠ 0) :
    prune (s.1, s.2.1, insertZero k ((s.2.2.1.erase a).erase b), s.2.2.2) ∈ successors s := by
  apply combineNext_mem_successors
  apply List.mem_flatMap.mpr
  refine ⟨a, ha, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨b, hb, ?_⟩
  apply List.mem_filterMap.mpr
  refine ⟨k, ?_, by simp [hkn]⟩
  simpa only [List.mem_cons, List.not_mem_nil, or_false] using hk

lemma set_getD_self (xs : List ℕ) (i d : ℕ) : xs.set i (xs.getD i d) = xs := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => exact congrArg (List.cons x) (ih i)

lemma lift_successor_or_discard {s : State} {k loc : ℕ}
    (hk : k ∈ s.2.2.1) (hloc : loc < 7) (hlive : live s.1 loc = true) :
    prune (s.1, s.2.1.set loc (addCarrier (s.2.1.getD loc 1) k),
      s.2.2.1.erase k, s.2.2.2) ∈ successors s := by
  by_cases hchange : addCarrier (s.2.1.getD loc 1) k = s.2.1.getD loc 1
  · rw [hchange, set_getD_self]
    exact discard_successor hk
  · exact lift_successor hk hloc hlive hchange

lemma lift_reachable {s : State} {k loc : ℕ}
    (hk : k ∈ s.2.2.1) (hloc : loc < 7) (hlive : live s.1 loc = true) :
    Relation.ReflTransGen (fun a b : State => b ∈ successors a) s
      (prune (s.1, s.2.1.set loc (addCarrier (s.2.1.getD loc 1) k),
        s.2.2.1.erase k, s.2.2.2)) :=
  Relation.ReflTransGen.single (lift_successor_or_discard hk hloc hlive)

namespace ZeroTransitions

def token (k : ℕ) : Multiset ℕ := if k = 0 then 0 else {k}

lemma mem_of_zero_eq {zs : List ℕ} {a : ℕ} {rest : Multiset ℕ}
    (hz : (zs : Multiset ℕ) = {a} + rest) : a ∈ zs := by
  change a ∈ (zs : Multiset ℕ)
  rw [hz]
  simp

lemma erase_of_zero_eq {zs : List ℕ} {a : ℕ} {rest : Multiset ℕ}
    (hz : (zs : Multiset ℕ) = {a} + rest) :
    (zs.erase a : Multiset ℕ) = rest := by
  change (zs : Multiset ℕ).erase a = rest
  rw [hz]
  simp

lemma coe_insertZero (k : ℕ) (zs : List ℕ) :
    (insertZero k zs : Multiset ℕ) = {k} + (zs : Multiset ℕ) := by
  change (insertZero k zs : Multiset ℕ) = ((k :: zs : List ℕ) : Multiset ℕ)
  exact Quot.sound (insertZero_perm k zs)

lemma discard_one {s : State} {a : ℕ} {rest : Multiset ℕ}
    (hz : (s.2.2.1 : Multiset ℕ) = {a} + rest) :
    ∃ t : State,
      Relation.ReflTransGen (fun p q : State => q ∈ successors p) s t ∧
      (t.2.2.1 : Multiset ℕ) = rest ∧ t.1 = s.1 ∧ t.2.2.2 = s.2.2.2 ∧
      t.2.1 = (prune s).2.1 := by
  refine ⟨prune (s.1, s.2.1, s.2.2.1.erase a, s.2.2.2),
    Relation.ReflTransGen.single (discard_successor (mem_of_zero_eq hz)),
    erase_of_zero_eq hz, rfl, rfl, rfl⟩

lemma discard_two {s : State} {a b : ℕ} {rest : Multiset ℕ}
    (hz : (s.2.2.1 : Multiset ℕ) = {a} + {b} + rest) :
    ∃ t : State,
      Relation.ReflTransGen (fun p q : State => q ∈ successors p) s t ∧
      (t.2.2.1 : Multiset ℕ) = rest ∧ t.1 = s.1 ∧ t.2.2.2 = s.2.2.2 ∧
      t.2.1 = (prune s).2.1 := by
  have hz' : (s.2.2.1 : Multiset ℕ) = {a} + ({b} + rest) := by
    simpa only [Multiset.add_assoc] using hz
  have ha := mem_of_zero_eq hz'
  have hz1 := erase_of_zero_eq hz'
  have hb := mem_of_zero_eq hz1
  have hz2 := erase_of_zero_eq hz1
  let t1 : State := prune (s.1, s.2.1, s.2.2.1.erase a, s.2.2.2)
  let t2 : State := prune (s.1, s.2.1, (s.2.2.1.erase a).erase b, s.2.2.2)
  have h1 : t1 ∈ successors s := discard_successor ha
  have h2 : t2 ∈ successors t1 := by
    have hh := discard_successor (s := t1) (k := b) hb
    change prune (prune (s.1, s.2.1, (s.2.2.1.erase a).erase b, s.2.2.2)) ∈
      successors t1 at hh
    rw [prune_idempotent] at hh
    exact hh
  exact ⟨t2, (Relation.ReflTransGen.single h1).trans (Relation.ReflTransGen.single h2),
    hz2, rfl, rfl, rfl⟩

lemma combine_nonzero {s : State} {a b k : ℕ} {rest : Multiset ℕ}
    (hz : (s.2.2.1 : Multiset ℕ) = {a} + {b} + rest)
    (hop : k = a &&& b ∨ k = a ||| b) (hk : k ≠ 0) :
    ∃ t : State,
      Relation.ReflTransGen (fun p q : State => q ∈ successors p) s t ∧
      (t.2.2.1 : Multiset ℕ) = {k} + rest ∧ t.1 = s.1 ∧ t.2.2.2 = s.2.2.2 ∧
      t.2.1 = (prune s).2.1 := by
  have hz' : (s.2.2.1 : Multiset ℕ) = {a} + ({b} + rest) := by
    simpa only [Multiset.add_assoc] using hz
  have ha := mem_of_zero_eq hz'
  have hz1 := erase_of_zero_eq hz'
  have hb := mem_of_zero_eq hz1
  have hz2 := erase_of_zero_eq hz1
  refine ⟨prune (s.1, s.2.1, insertZero k ((s.2.2.1.erase a).erase b), s.2.2.2),
    Relation.ReflTransGen.single (combine_successor ha hb hop hk), ?_, rfl, rfl, rfl⟩
  change (insertZero k ((s.2.2.1.erase a).erase b) : Multiset ℕ) = {k} + rest
  rw [coe_insertZero, hz2]

lemma zero_binary {s : State} (a b : ℕ) (isAnd : Bool) (rest : Multiset ℕ)
    (hz : (s.2.2.1 : Multiset ℕ) = token a + token b + rest) :
    ∃ t : State,
      Relation.ReflTransGen (fun p q : State => q ∈ successors p) s t ∧
      (t.2.2.1 : Multiset ℕ) = token (if isAnd then a &&& b else a ||| b) + rest ∧
      t.1 = s.1 ∧ t.2.2.2 = s.2.2.2 ∧
      (t.2.1 = s.2.1 ∨ t.2.1 = (prune s).2.1) := by
  by_cases ha : a = 0
  · subst a
    cases isAnd
    · refine ⟨s, Relation.ReflTransGen.refl, ?_, rfl, rfl, Or.inl rfl⟩
      simpa [token] using hz
    · by_cases hb : b = 0
      · subst b
        refine ⟨s, Relation.ReflTransGen.refl, ?_, rfl, rfl, Or.inl rfl⟩
        simpa [token] using hz
      · have hz' : (s.2.2.1 : Multiset ℕ) = {b} + rest := by simpa [token, hb] using hz
        obtain ⟨t, hr, ht, hu, hf, hp⟩ := discard_one hz'
        exact ⟨t, hr, by simpa [token] using ht, hu, hf, Or.inr hp⟩
  · by_cases hb : b = 0
    · subst b
      cases isAnd
      · refine ⟨s, Relation.ReflTransGen.refl, ?_, rfl, rfl, Or.inl rfl⟩
        simpa [token] using hz
      · have hz' : (s.2.2.1 : Multiset ℕ) = {a} + rest := by simpa [token, ha] using hz
        obtain ⟨t, hr, ht, hu, hf, hp⟩ := discard_one hz'
        exact ⟨t, hr, by simpa [token] using ht, hu, hf, Or.inr hp⟩
    · have hz' : (s.2.2.1 : Multiset ℕ) = {a} + {b} + rest := by
        simpa [token, ha, hb] using hz
      let k := if isAnd then a &&& b else a ||| b
      by_cases hk : k = 0
      · obtain ⟨t, hr, ht, hu, hf, hp⟩ := discard_two hz'
        refine ⟨t, hr, ?_, hu, hf, Or.inr hp⟩
        change (t.2.2.1 : Multiset ℕ) = token k + rest
        rw [hk]
        simpa [token] using ht
      · have hop : k = a &&& b ∨ k = a ||| b := by cases isAnd <;> simp [k]
        obtain ⟨t, hr, ht, hu, hf, hp⟩ := combine_nonzero hz' hop hk
        refine ⟨t, hr, ?_, hu, hf, Or.inr hp⟩
        change (t.2.2.1 : Multiset ℕ) = token k + rest
        simpa [token, hk] using ht

end ZeroTransitions

end OnceResource

namespace OncePositive

open OnceResource OnceGeometry

abbrev Pools := Fin 7 → ℕ

def or7 (f : Fin 7 → ℕ) : ℕ :=
  f 0 ||| f 1 ||| f 2 ||| f 3 ||| f 4 ||| f 5 ||| f 6

def PoolsGood (P : Pools) : Prop := ∀ i,
  0 ∈ values (P i) ∧ ∀ a ∈ values (P i), ∀ b ∈ values (P i), a ||| b ∈ values (P i)

def Witness (P : Pools) (L : Finset (Fin 7)) (f : Fin 7 → ℕ) : Prop :=
  ∀ i, f i ∈ values (P i) ∧ (i ∉ L → f i = 0)

def Rep (used : ℕ) (P : Pools) (S : Finset (Fin 10)) (m : ℕ) : Prop :=
  ∀ (g : Fin 4) (b : Bool), used.testBit g.val = false → S ⊆ port g b →
    ∃ f, Witness P (locations g b) f ∧ m = rawMask S ||| or7 f

def liftPool (P : Pools) (loc : Fin 7) (k : ℕ) : Pools :=
  Function.update P loc (addCarrier (P loc) k)

lemma or7_or (f h : Fin 7 → ℕ) :
    or7 (fun i => f i ||| h i) = or7 f ||| or7 h := by
  dsimp only [or7]
  ac_rfl

lemma or7_update (f : Fin 7 → ℕ) (loc : Fin 7) (k : ℕ) :
    or7 (Function.update f loc (f loc ||| k)) = or7 f ||| k := by
  fin_cases loc <;> simp [or7, Function.update]
  all_goals
    generalize f (0 : Fin 7) = x0
    generalize f (1 : Fin 7) = x1
    generalize f (2 : Fin 7) = x2
    generalize f (3 : Fin 7) = x3
    generalize f (4 : Fin 7) = x4
    generalize f (5 : Fin 7) = x5
    generalize f (6 : Fin 7) = x6
    ac_rfl

lemma rep_raw {used : ℕ} {P : Pools} (hp : PoolsGood P) (S : Finset (Fin 10)) :
    Rep used P S (rawMask S) := by
  intro g b _ _
  refine ⟨fun _ => 0, ?_, ?_⟩
  · exact fun i => ⟨(hp i).1, fun _ => rfl⟩
  · simp [or7]

lemma rep_or {used : ℕ} {P : Pools} (hp : PoolsGood P)
    {S T : Finset (Fin 10)} {a b : ℕ} (ha : Rep used P S a) (hb : Rep used P T b) :
    Rep used P (S ∪ T) (a ||| b) := by
  intro g side hu hST
  have hS : S ⊆ port g side := fun v hv => hST (Finset.mem_union_left _ hv)
  have hT : T ⊆ port g side := fun v hv => hST (Finset.mem_union_right _ hv)
  obtain ⟨f, hf, ha⟩ := ha g side hu hS
  obtain ⟨h, hh, hb⟩ := hb g side hu hT
  refine ⟨fun i => f i ||| h i, ?_, ?_⟩
  · intro i
    refine ⟨(hp i).2 _ (hf i).1 _ (hh i).1, ?_⟩
    intro hi
    change f i ||| h i = 0
    rw [(hf i).2 hi, (hh i).2 hi]
    rfl
  · rw [ha, hb, rawMask_union, or7_or]
    ac_rfl

lemma rep_mono {used : ℕ} {P Q : Pools} {S : Finset (Fin 10)} {m : ℕ}
    (hPQ : ∀ i x, x ∈ values (P i) → x ∈ values (Q i))
    (h : Rep used P S m) : Rep used Q S m := by
  intro g b hg hS
  obtain ⟨f, hf, hm⟩ := h g b hg hS
  exact ⟨f, fun i => ⟨hPQ i _ (hf i).1, (hf i).2⟩, hm⟩

lemma liftPool_mono (P : Pools) (loc : Fin 7) (k : ℕ) :
    ∀ i x, x ∈ values (P i) → x ∈ values (liftPool P loc k i) := by
  intro i x hx
  by_cases hi : i = loc
  · subst i
    simpa [liftPool] using mem_addCarrier_of_mem (k := k) hx
  · simpa [liftPool, hi] using hx

lemma poolsGood_lift {P : Pools} (hp : PoolsGood P) (loc : Fin 7) {k : ℕ} (hk : k < 64) :
    PoolsGood (liftPool P loc k) := by
  intro i
  by_cases hi : i = loc
  · subst i
    simpa [liftPool] using addCarrier_zero_and_or_closed hk (hp loc).1 (hp loc).2
  · simpa [liftPool, hi] using hp i

lemma rep_lift {used : ℕ} {P : Pools} {S : Finset (Fin 10)} {m k : ℕ}
    (h : Rep used P S m) (hk : k < 64) {v : Fin 10} (hv : v ∈ S) :
    Rep used (liftPool P (vertexClass v) k) S (m ||| k) := by
  intro g b hg hS
  have hvL := support_class hS hv
  obtain ⟨f, hf, hm⟩ := h g b hg hS
  refine ⟨Function.update f (vertexClass v) (f (vertexClass v) ||| k), ?_, ?_⟩
  · intro i
    by_cases hi : i = vertexClass v
    · subst i
      constructor
      · simpa [liftPool] using mem_addCarrier_or (hf (vertexClass v)).1 hk
      · intro hnot
        exact False.elim (hnot hvL)
    · simpa [liftPool, Function.update_apply, hi] using hf i
  · rw [or7_update, hm]
    ac_rfl

lemma rep_restrict_pools {old new : ℕ} {P Q : Pools} {S : Finset (Fin 10)} {m : ℕ}
    (hgroups : ∀ g : Fin 4, new.testBit g.val = false → old.testBit g.val = false)
    (hzero : ∀ i, 0 ∈ values (Q i))
    (hpools : ∀ (g : Fin 4) (b : Bool), new.testBit g.val = false →
      ∀ i ∈ locations g b, Q i = P i)
    (h : Rep old P S m) : Rep new Q S m := by
  intro g b hg hS
  obtain ⟨f, hf, hm⟩ := h g b (hgroups g hg) hS
  refine ⟨f, ?_, hm⟩
  intro i
  refine ⟨?_, (hf i).2⟩
  by_cases hi : i ∈ locations g b
  · rw [hpools g b hg i hi]
    exact (hf i).1
  · rw [(hf i).2 hi]
    exact hzero i

end OncePositive

namespace OncePositive

open OnceResource OnceGeometry

def rightChoices (P : Pools) (g : Fin 4) : ℕ :=
  match g.val with
  | 0 => mergePools (mergePools (P 1) (P 2)) (P 3)
  | 1 => mergePools (1 <<< 25) (P 4)
  | 2 => mergePools (1 <<< 42) (P 5)
  | _ => mergePools (1 <<< 52) (P 6)

def portChoices (P : Pools) (g : Fin 4) (b : Bool) : ℕ :=
  if b then rightChoices P g else P ⟨g.val, by omega⟩

def poolView (ps : List ℕ) : Pools := fun i => ps.getD i.val 1

lemma portChoices_view (ps : List ℕ) (g : Fin 4) (b : Bool) :
    portChoices (poolView ps) g b =
      if b then rightPool ps g.val else ps.getD g.val 1 := by
  fin_cases g <;> cases b <;> rfl

lemma or7_filtered {L : Finset (Fin 7)} {f : Fin 7 → ℕ}
    (hf : ∀ i, i ∉ L → f i = 0) :
    or7 f = or7 (fun i => if i ∈ L then f i else 0) := by
  congr 1
  funext i
  by_cases hi : i ∈ L
  · simp [hi]
  · simp [hi, hf i hi]

lemma merge_mem {p q a b : ℕ} (ha : a ∈ values p) (hb : b ∈ values q) :
    a ||| b ∈ values (mergePools p q) := by
  exact mem_pairMasks ha hb (or_lt_64 (mem_values_iff.mp ha).1 (mem_values_iff.mp hb).1)

lemma portChoices_membership (P : Pools) (g : Fin 4) (b : Bool) (f : Fin 7 → ℕ)
    (hf : ∀ i, f i ∈ values (P i)) :
    rawMask (port g b) ||| or7 (fun i => if i ∈ locations g b then f i else 0) ∈
      values (portChoices P g b) := by
  rw [rawMask_port]
  fin_cases g <;> cases b
  · simpa [portChoices, locations, or7] using hf 0
  · simpa [portChoices, rightChoices, locations, or7, basis] using
      merge_mem (merge_mem (hf 1) (hf 2)) (hf 3)
  · simpa [portChoices, locations, or7] using hf 1
  · simpa [portChoices, rightChoices, locations, or7, basis] using
      merge_mem (mem_singleton (by decide : 25 < 64)) (hf 4)
  · simpa [portChoices, locations, or7] using hf 2
  · simpa [portChoices, rightChoices, locations, or7, basis] using
      merge_mem (mem_singleton (by decide : 42 < 64)) (hf 5)
  · simpa [portChoices, locations, or7] using hf 3
  · simpa [portChoices, rightChoices, locations, or7, basis] using
      merge_mem (mem_singleton (by decide : 52 < 64)) (hf 6)

lemma rep_port_mem {used : ℕ} {P : Pools} {g : Fin 4} {b : Bool} {m : ℕ}
    (h : Rep used P (port g b) m) (hu : used.testBit g.val = false) :
    m ∈ values (portChoices P g b) := by
  obtain ⟨f, hf, hm⟩ := h g b hu (Finset.Subset.refl _)
  rw [hm, or7_filtered (fun i => (hf i).2)]
  exact portChoices_membership P g b f (fun i => (hf i).1)

lemma group_candidate {used : ℕ} {P : Pools} {g : Fin 4} {a b : ℕ}
    (ha : Rep used P (port g false) a) (hb : Rep used P (port g true) b)
    (hu : used.testBit g.val = false) (hab : a &&& b < 64) :
    a &&& b ∈ values (pairMasks (· &&& ·) (P ⟨g.val, by omega⟩) (rightChoices P g)) := by
  have hleft := rep_port_mem ha hu
  have hright := rep_port_mem hb hu
  exact mem_pairMasks hleft hright hab

end OncePositive

namespace OncePositive

open OnceResource OnceGeometry

lemma poolView_prune (s : State) (i : Fin 7) :
    poolView (prune s).2.1 i = if live s.1 i.val then poolView s.2.1 i else 1 := by
  simp [poolView, prune, List.getD_eq_getElem?_getD]

lemma prune_pools_length (s : State) : (prune s).2.1.length = 7 := by
  simp [prune]

lemma mem_values_one_iff {x : ℕ} : x ∈ values 1 ↔ x = 0 := by
  rw [mem_values_iff, Nat.testBit_one_eq_true_iff_self_eq_zero]
  constructor
  · exact And.right
  · intro h
    subst x
    exact ⟨by decide, rfl⟩

lemma one_pool_good :
    0 ∈ values 1 ∧ ∀ a ∈ values 1, ∀ b ∈ values 1, a ||| b ∈ values 1 := by
  constructor
  · exact mem_values_one_iff.mpr rfl
  · intro a ha b hb
    obtain rfl := mem_values_one_iff.mp ha
    obtain rfl := mem_values_one_iff.mp hb
    exact mem_values_one_iff.mpr rfl

lemma poolsGood_prune {s : State} (hp : PoolsGood (poolView s.2.1)) :
    PoolsGood (poolView (prune s).2.1) := by
  intro i
  rw [poolView_prune]
  split
  · exact hp i
  · exact one_pool_good

lemma rep_prune {s : State} {S : Finset (Fin 10)} {m : ℕ}
    (hu : s.1 < 16) (hp : PoolsGood (poolView s.2.1))
    (h : Rep s.1 (poolView s.2.1) S m) :
    Rep (prune s).1 (poolView (prune s).2.1) S m := by
  apply rep_restrict_pools (fun _ hg => hg) (fun i => (poolsGood_prune hp i).1) ?_ h
  intro g b hg i hi
  rw [poolView_prune, port_locations_live hu hg b hi]
  rfl

lemma unused_of_or_unused {used extra i : ℕ}
    (h : (used ||| extra).testBit i = false) : used.testBit i = false := by
  rw [Nat.testBit_or] at h
  exact (Bool.or_eq_false_iff.mp h).1

lemma mark_used_lt {used : ℕ} (hu : used < 16) (g : Fin 4) :
    used ||| (1 <<< g.val) < 16 := by
  have hg : (1 <<< g.val : ℕ) < 16 := by fin_cases g <;> decide
  exact Nat.or_lt_two_pow (n := 4) hu hg

lemma rep_mark {used : ℕ} {P : Pools} {S : Finset (Fin 10)} {m : ℕ}
    (h : Rep used P S m) (g : Fin 4) : Rep (used ||| (1 <<< g.val)) P S m := by
  intro g' b hg hS
  exact h g' b (unused_of_or_unused hg) hS

lemma rep_mark_prune {used : ℕ} {ps : List ℕ} {S : Finset (Fin 10)} {m : ℕ}
    (hu : used < 16) (hp : PoolsGood (poolView ps)) (h : Rep used (poolView ps) S m)
    (g : Fin 4) (zs : List ℕ) (forked : Bool) :
    Rep (used ||| (1 <<< g.val))
      (poolView (prune (used ||| (1 <<< g.val), ps, zs, forked)).2.1) S m := by
  exact rep_prune (s := (used ||| (1 <<< g.val), ps, zs, forked))
    (mark_used_lt hu g) hp (rep_mark h g)

lemma poolView_set {ps : List ℕ} (hlen : ps.length = 7) (loc : Fin 7) (k : ℕ) :
    poolView (ps.set loc.val (addCarrier (ps.getD loc.val 1) k)) =
      liftPool (poolView ps) loc k := by
  funext i
  by_cases hi : i = loc
  · subst i
    have hb : loc.val < ps.length := by simpa only [hlen] using loc.isLt
    simp [poolView, liftPool, List.getD_eq_getElem?_getD, List.getElem?_set_self hb]
  · have hne : loc.val ≠ i.val := fun h => hi (Fin.ext h.symm)
    simp [poolView, liftPool, hi, List.getD_eq_getElem?_getD, List.getElem?_set_ne hne]

lemma poolsGood_set {ps : List ℕ} (hlen : ps.length = 7)
    (hp : PoolsGood (poolView ps)) (loc : Fin 7) {k : ℕ} (hk : k < 64) :
    PoolsGood (poolView (ps.set loc.val (addCarrier (ps.getD loc.val 1) k))) := by
  rw [poolView_set hlen]
  exact poolsGood_lift hp loc hk

lemma poolView_replicate_one : poolView (List.replicate 7 1) = fun _ => 1 := by
  funext i
  fin_cases i <;> rfl

lemma poolsGood_replicate_one : PoolsGood (poolView (List.replicate 7 1)) := by
  rw [poolView_replicate_one]
  exact fun _ => one_pool_good

end OncePositive

namespace OncePositive
open OnceResource OnceGeometry

lemma rep_of_dead_class {used : ℕ} {P : Pools} {S : Finset (Fin 10)} {v : Fin 10}
    (hu : used < 16) (hv : v ∈ S) (hd : live used (vertexClass v).val = false) (m : ℕ) :
    Rep used P S m := by
  intro g b hg hS
  have hl := port_locations_live hu hg b (support_class hS hv)
  simp [hd] at hl

lemma positive_lift_step {s : State} {S : Finset (Fin 10)} {m k : ℕ}
    (hu : s.1 < 16) (hlen : s.2.1.length = 7) (hp : PoolsGood (poolView s.2.1))
    (h : Rep s.1 (poolView s.2.1) S m) (hs : S.Nonempty)
    (hk : k < 64) (hmem : k ∈ s.2.2.1) :
    ∃ t : State,
      Relation.ReflTransGen (fun a b : State => b ∈ successors a) s t ∧
      t.1 = s.1 ∧ t.2.2.1 = s.2.2.1.erase k ∧ t.2.2.2 = s.2.2.2 ∧
      t.2.1.length = 7 ∧ PoolsGood (poolView t.2.1) ∧
      (∀ T n, Rep s.1 (poolView s.2.1) T n → Rep t.1 (poolView t.2.1) T n) ∧
      Rep t.1 (poolView t.2.1) S (m ||| k) := by
  obtain ⟨v, hv⟩ := hs
  by_cases hl : live s.1 (vertexClass v).val = true
  · let q : State := (s.1,
        s.2.1.set (vertexClass v).val (addCarrier (s.2.1.getD (vertexClass v).val 1) k),
        s.2.2.1.erase k, s.2.2.2)
    have hqgood : PoolsGood (poolView q.2.1) := poolsGood_set hlen hp (vertexClass v) hk
    refine ⟨prune q, lift_reachable hmem (vertexClass v).isLt hl, rfl, rfl, rfl,
      prune_pools_length q, poolsGood_prune hqgood, ?_, ?_⟩
    · intro T n hT
      apply rep_prune (s := q) hu hqgood
      change Rep s.1 (poolView (s.2.1.set (vertexClass v).val
        (addCarrier (s.2.1.getD (vertexClass v).val 1) k))) T n
      rw [poolView_set hlen]
      exact rep_mono (liftPool_mono _ _ _) hT
    · apply rep_prune (s := q) hu hqgood
      change Rep s.1 (poolView (s.2.1.set (vertexClass v).val
        (addCarrier (s.2.1.getD (vertexClass v).val 1) k))) S (m ||| k)
      rw [poolView_set hlen]
      exact rep_lift h hk hv
  · have hd : live s.1 (vertexClass v).val = false := Bool.eq_false_of_not_eq_true hl
    let q : State := (s.1, s.2.1, s.2.2.1.erase k, s.2.2.2)
    refine ⟨prune q, Relation.ReflTransGen.single (discard_successor hmem), rfl, rfl, rfl,
      prune_pools_length q, poolsGood_prune hp, ?_, ?_⟩
    · intro T n hT
      exact rep_prune (s := q) hu hp hT
    · exact rep_of_dead_class hu hv hd _

lemma positive_group_step {s : State} {g : Fin 4} {a b : ℕ}
    (hu : s.1 < 16) (hp : PoolsGood (poolView s.2.1))
    (ha : Rep s.1 (poolView s.2.1) (port g false) a)
    (hb : Rep s.1 (poolView s.2.1) (port g true) b)
    (hg : s.1.testBit g.val = false) (hab : a &&& b < 64) (hne : a &&& b ≠ 0) :
    let t := prune (s.1 ||| (1 <<< g.val), s.2.1, insertZero (a &&& b) s.2.2.1, s.2.2.2)
    t ∈ successors s ∧ t.1 < 16 ∧ t.2.1.length = 7 ∧ PoolsGood (poolView t.2.1) ∧
      (∀ T n, Rep s.1 (poolView s.2.1) T n → Rep t.1 (poolView t.2.1) T n) := by
  dsimp only
  have hc := group_candidate ha hb hg hab
  have hr : rightChoices (poolView s.2.1) g = rightPool s.2.1 g.val := by
    exact portChoices_view s.2.1 g true
  rw [hr] at hc
  refine ⟨group_successor g.isLt hg hc hne, mark_used_lt hu g,
    prune_pools_length _, poolsGood_prune hp, ?_⟩
  intro T n hT
  exact rep_mark_prune hu hp hT g _ _

end OncePositive

namespace OncePositive

open OnceResource OnceGeometry

lemma frame_preserves {s t : State}
    (hu : s.1 < 16) (hlen : s.2.1.length = 7) (hp : PoolsGood (poolView s.2.1))
    (ht : t.1 = s.1) (hps : t.2.1 = s.2.1 ∨ t.2.1 = (prune s).2.1) :
    t.1 < 16 ∧ t.2.1.length = 7 ∧ PoolsGood (poolView t.2.1) ∧
      (∀ T n, Rep s.1 (poolView s.2.1) T n → Rep t.1 (poolView t.2.1) T n) := by
  refine ⟨by simpa only [ht] using hu, ?_⟩
  rcases hps with he | he
  · rw [he, ht]
    exact ⟨hlen, hp, fun _ _ h => h⟩
  · rw [he, ht]
    exact ⟨prune_pools_length s, poolsGood_prune hp, fun _ _ h => rep_prune hu hp h⟩

lemma zero_binary_positive_state {s : State} (a b : ℕ) (isAnd : Bool) (rest : Multiset ℕ)
    (hu : s.1 < 16) (hlen : s.2.1.length = 7) (hp : PoolsGood (poolView s.2.1))
    (hz : (s.2.2.1 : Multiset ℕ) =
      ZeroTransitions.token a + ZeroTransitions.token b + rest) :
    ∃ t : State,
      Relation.ReflTransGen (fun p q : State => q ∈ successors p) s t ∧
      t.1 = s.1 ∧ t.2.2.2 = s.2.2.2 ∧
      (t.2.2.1 : Multiset ℕ) =
        ZeroTransitions.token (if isAnd then a &&& b else a ||| b) + rest ∧
      t.1 < 16 ∧ t.2.1.length = 7 ∧ PoolsGood (poolView t.2.1) ∧
      (∀ T n, Rep s.1 (poolView s.2.1) T n → Rep t.1 (poolView t.2.1) T n) := by
  obtain ⟨t, hr, hz', ht, hf, hps⟩ := ZeroTransitions.zero_binary a b isAnd rest hz
  exact ⟨t, hr, ht, hf, hz', frame_preserves hu hlen hp ht hps⟩

end OncePositive

namespace OncePositive

open OnceResource OnceGeometry

lemma insertZero_multiset (k : ℕ) (xs : List ℕ) :
    (insertZero k xs : Multiset ℕ) = {k} + (xs : Multiset ℕ) := by
  simpa only [Multiset.singleton_add, Multiset.cons_coe] using
    (Multiset.coe_eq_coe.mpr (insertZero_perm k xs))

lemma fork_state_spec {s t : State} {k : ℕ}
    (hk : k ∈ s.2.2.1) (hf : s.2.2.2 = false) (hu : s.1 < 16)
    (hp : PoolsGood (poolView s.2.1))
    (ht : t = prune (s.1, s.2.1, insertZero k s.2.2.1, true)) :
    t ∈ successors s ∧ t.1 = s.1 ∧ t.2.1.length = 7 ∧
      PoolsGood (poolView t.2.1) ∧
      (∀ (S : Finset (Fin 10)) (m : ℕ), Rep s.1 (poolView s.2.1) S m →
        Rep t.1 (poolView t.2.1) S m) ∧
      (t.2.2.1 : Multiset ℕ) = {k} + (s.2.2.1 : Multiset ℕ) ∧ t.2.2.2 = true := by
  subst t
  refine ⟨fork_successor hk hf, rfl, prune_pools_length _, poolsGood_prune hp, ?_, ?_, rfl⟩
  · intro S m h
    exact rep_prune (s := (s.1, s.2.1, insertZero k s.2.2.1, true)) hu hp h
  · exact insertZero_multiset k s.2.2.1

lemma exists_fork_state {s : State} {k : ℕ}
    (hk : k ∈ s.2.2.1) (hf : s.2.2.2 = false) (hu : s.1 < 16)
    (hp : PoolsGood (poolView s.2.1)) :
    ∃ t : State, t ∈ successors s ∧ t.1 = s.1 ∧ t.2.1.length = 7 ∧
      PoolsGood (poolView t.2.1) ∧
      (∀ (S : Finset (Fin 10)) (m : ℕ), Rep s.1 (poolView s.2.1) S m →
        Rep t.1 (poolView t.2.1) S m) ∧
      (t.2.2.1 : Multiset ℕ) = {k} + (s.2.2.1 : Multiset ℕ) ∧ t.2.2.2 = true := by
  exact ⟨prune (s.1, s.2.1, insertZero k s.2.2.1, true), fork_state_spec hk hf hu hp rfl⟩

end OncePositive

namespace OnceResource.ZeroTransitions

lemma fork_token {s : State} (k : ℕ) (rest : Multiset ℕ)
    (hf : s.2.2.2 = false) (hz : (s.2.2.1 : Multiset ℕ) = token k + rest) :
    ∃ t : State,
      Relation.ReflTransGen (fun p q : State => q ∈ successors p) s t ∧
      (t.2.2.1 : Multiset ℕ) = token k + token k + rest ∧
      t.1 = s.1 ∧ t.2.2.2 = decide (k ≠ 0) ∧
      (t.2.1 = s.2.1 ∨ t.2.1 = (prune s).2.1) := by
  by_cases hk : k = 0
  · refine ⟨s, Relation.ReflTransGen.refl, ?_, rfl, ?_, Or.inl rfl⟩
    · simpa [token, hk] using hz
    · simpa [hk] using hf
  · have hz' : (s.2.2.1 : Multiset ℕ) = {k} + rest := by simpa [token, hk] using hz
    have hm := mem_of_zero_eq hz'
    refine ⟨prune (s.1, s.2.1, insertZero k s.2.2.1, true),
      Relation.ReflTransGen.single (fork_successor hm hf), ?_, rfl, ?_, Or.inr rfl⟩
    · change (insertZero k s.2.2.1 : Multiset ℕ) = token k + token k + rest
      rw [coe_insertZero, hz']
      simp [token, hk]
    · simp [prune, hk]

end OnceResource.ZeroTransitions

namespace OncePositive

open OnceResource OnceGeometry

lemma zero_fork_positive_state {s : State} (k : ℕ) (rest : Multiset ℕ)
    (hu : s.1 < 16) (hlen : s.2.1.length = 7) (hp : PoolsGood (poolView s.2.1))
    (hf : s.2.2.2 = false)
    (hz : (s.2.2.1 : Multiset ℕ) = ZeroTransitions.token k + rest) :
    ∃ t : State,
      Relation.ReflTransGen (fun p q : State => q ∈ successors p) s t ∧
      t.1 = s.1 ∧ t.2.2.2 = decide (k ≠ 0) ∧
      (t.2.2.1 : Multiset ℕ) =
        ZeroTransitions.token k + ZeroTransitions.token k + rest ∧
      t.1 < 16 ∧ t.2.1.length = 7 ∧ PoolsGood (poolView t.2.1) ∧
      (∀ T n, Rep s.1 (poolView s.2.1) T n → Rep t.1 (poolView t.2.1) T n) := by
  obtain ⟨t, hr, hz', ht, hf', hps⟩ := ZeroTransitions.fork_token k rest hf hz
  exact ⟨t, hr, ht, hf', hz', frame_preserves hu hlen hp ht hps⟩

end OncePositive

namespace OnceResource.IndexCopies

def Reads (start : ℕ) (A B : ℕ → ℕ) (t x : ℕ) : Prop :=
  A (start + t) = x ∨ B (start + t) = x

def Readers (start : ℕ) (A B : ℕ → ℕ) (t x : ℕ) : Finset ℕ :=
  (Finset.range t).filter (fun j => A (start + j) = x ∨ B (start + j) = x)

def ReadCount (start : ℕ) (A B : ℕ → ℕ) (t x : ℕ) : ℕ :=
  (Readers start A B t x).card

def Capacity (fork x : ℕ) : ℕ := if x = fork then 2 else 1

def Valid (start : ℕ) (A B : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ t < n, A (start + t) < start + t ∧ B (start + t) < start + t ∧
    A (start + t) ≠ B (start + t)

lemma readers_mono {start t n x : ℕ} {A B : ℕ → ℕ} (ht : t ≤ n) :
    Readers start A B t x ⊆ Readers start A B n x := by
  intro j hj
  obtain ⟨hj, hr⟩ := Finset.mem_filter.mp hj
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hj) ht), hr⟩

lemma readCount_succ (start : ℕ) (A B : ℕ → ℕ) (t x : ℕ) :
    ReadCount start A B (t + 1) x = ReadCount start A B t x +
      if A (start + t) = x ∨ B (start + t) = x then 1 else 0 := by
  have hnot : t ∉ Readers start A B t x := by simp [Readers]
  unfold ReadCount Readers
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with hr
  · exact Finset.card_insert_of_notMem hnot
  · simp

lemma earlier_readers_lt_capacity {start n t x fork : ℕ} {A B : ℕ → ℕ}
    (ht : t < n) (hr : Reads start A B t x)
    (hcap : ReadCount start A B n x ≤ Capacity fork x) :
    ReadCount start A B t x < Capacity fork x := by
  have hle := Finset.card_le_card (readers_mono (start := start) (A := A) (B := B)
    (x := x) (show t + 1 ≤ n by omega))
  change ReadCount start A B (t + 1) x ≤ ReadCount start A B n x at hle
  rw [readCount_succ] at hle
  change A (start + t) = x ∨ B (start + t) = x at hr
  rw [ite_eq_left hr] at hle
  omega

lemma readCount_zero_of_future {start n t x : ℕ} {A B : ℕ → ℕ}
    (hv : Valid start A B n) (ht : t ≤ n) (hx : start + t ≤ x) :
    ReadCount start A B t x = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  obtain ⟨hj, hr⟩ := Finset.mem_filter.mp hj
  have hjt := Finset.mem_range.mp hj
  obtain ⟨ha, hb, _⟩ := hv j (by omega)
  rcases hr with hr | hr <;> omega

variable (Z : ℕ → Prop) [DecidablePred Z]

def Copies (fork x : ℕ) : ℕ := if Z x then Capacity fork x else 1

def Drop (i : ℕ) (ids : Multiset ℕ) : Multiset ℕ :=
  if Z i then ids.erase i else ids

def Give (fork out : ℕ) (ids : Multiset ℕ) : Multiset ℕ :=
  out ::ₘ (if Z out ∧ out = fork then out ::ₘ ids else ids)

def Initial (start fork : ℕ) : Multiset ℕ :=
  Multiset.range start + if Z fork ∧ fork < start then {fork} else 0

def Available (start fork : ℕ) (A B : ℕ → ℕ) : ℕ → Multiset ℕ
  | 0 => Initial Z start fork
  | t + 1 => Give Z fork (start + t)
      (Drop Z (B (start + t)) (Drop Z (A (start + t)) (Available start fork A B t)))

lemma count_drop (ids : Multiset ℕ) (i x : ℕ) :
    (Drop Z i ids).count x = ids.count x - if Z x ∧ x = i then 1 else 0 := by
  by_cases hxi : x = i
  · subst x
    by_cases hi : Z i <;> simp [Drop, hi, Multiset.count_erase_self]
  · by_cases hi : Z i <;> simp [Drop, hi, hxi, Multiset.count_erase_of_ne hxi]

lemma count_drop_two (ids : Multiset ℕ) {a b : ℕ} (hab : a ≠ b) (x : ℕ) :
    (Drop Z b (Drop Z a ids)).count x =
      ids.count x - if Z x ∧ (a = x ∨ b = x) then 1 else 0 := by
  rw [count_drop, count_drop]
  by_cases hz : Z x
  · by_cases hxa : x = a
    · subst x
      simp [hz, hab]
    · by_cases hxb : x = b
      · subst x
        simp [hz, hxa, Ne.symm hxa]
      · simp [hz, hxa, hxb, Ne.symm hxa, Ne.symm hxb]
  · simp [hz]

lemma count_give (ids : Multiset ℕ) (fork out x : ℕ) :
    (Give Z fork out ids).count x = ids.count x + if x = out then Copies Z fork out else 0 := by
  by_cases hf : out = fork
  · subst out
    by_cases hx : x = fork
    · subst x
      by_cases hz : Z fork <;> simp [Give, Copies, Capacity, hz, Nat.add_assoc]
    · by_cases hz : Z fork <;> simp [Give, hz, hx]
  · by_cases hx : x = out
    · subst x
      by_cases hz : Z out <;> simp [Give, Copies, Capacity, hz, hf]
    · simp [Give, hf, hx]

lemma count_initial (start fork x : ℕ) :
    (Initial Z start fork).count x = if x < start then Copies Z fork x else 0 := by
  have hrange : (Multiset.range start).count x = if x < start then 1 else 0 := by
    simpa using Multiset.count_eq_of_nodup (a := x) (Multiset.nodup_range start)
  by_cases hx : x < start <;> by_cases hxf : x = fork
  · subst x
    by_cases hz : Z fork <;>
      simp [Initial, Multiset.count_add, hrange, hx, hz, Copies, Capacity]
  · by_cases hz : Z fork ∧ fork < start <;> by_cases hzx : Z x <;>
      simp [Initial, Multiset.count_add, hrange, hx, hz, Copies, Capacity, hxf, hzx]
  · subst x
    simp [Initial, hx]
  · by_cases hz : Z fork ∧ fork < start <;>
      simp [Initial, hx, hz, hxf]

lemma count_available {start fork n : ℕ} {A B : ℕ → ℕ}
    (hv : Valid start A B n) (t : ℕ) (ht : t ≤ n) (x : ℕ) :
    (Available Z start fork A B t).count x =
      if x < start + t then
        if Z x then Capacity fork x - ReadCount start A B t x else 1
      else 0 := by
  induction t with
  | zero => simp [Available, count_initial, Copies, ReadCount, Readers]
  | succ t ih =>
    have ht' : t ≤ n := by omega
    have ih' := ih ht'
    obtain ⟨ha, hb, hab⟩ := hv t (by omega)
    rw [Available, count_give, count_drop_two Z _ hab, ih']
    by_cases hf : x = start + t
    · subst x
      have hrc := readCount_zero_of_future hv ht' (x := start + t) (by omega)
      have hr : ¬(A (start + t) = start + t ∨ B (start + t) = start + t) := by omega
      have hn : start + t < start + (t + 1) := by omega
      simp [readCount_succ, hrc, hr, hn, Copies]
    · by_cases hold : x < start + t
      · have hn : x < start + (t + 1) := by omega
        simp only [ite_eq_left hold, ite_eq_right hf, Nat.add_zero, ite_eq_left hn]
        rw [readCount_succ]
        by_cases hz : Z x
        · by_cases hr : A (start + t) = x ∨ B (start + t) = x <;>
            simp [hz, hr, Nat.sub_sub]
        · simp [hz]
      · have hn : ¬ x < start + (t + 1) := by omega
        have hna : A (start + t) ≠ x := by omega
        have hnb : B (start + t) ≠ x := by omega
        simp [hold, hf, hn, hna, hnb]

lemma source_available {start fork n t x : ℕ} {A B : ℕ → ℕ}
    (hv : Valid start A B n)
    (hcap : ∀ x, Z x → ReadCount start A B n x ≤ Capacity fork x)
    (ht : t < n) (hx : x < start + t) (hr : Reads start A B t x) :
    x ∈ Available Z start fork A B t := by
  apply Multiset.count_pos.mp
  rw [count_available Z hv t (by omega) x, ite_eq_left hx]
  by_cases hz : Z x
  · rw [ite_eq_left hz]
    have hlt := earlier_readers_lt_capacity ht hr (hcap x hz)
    omega
  · simp [hz]

def Retain (x : ℕ) : Multiset ℕ := if Z x then 0 else {x}

lemma two_decomp {ids : Multiset ℕ} {a b : ℕ}
    (ha : a ∈ ids) (hb : b ∈ ids) (hab : a ≠ b) :
    ids = a ::ₘ b ::ₘ ((ids.erase a).erase b) := by
  have hb' := (Multiset.mem_erase_of_ne (Ne.symm hab)).mpr hb
  calc
    ids = a ::ₘ ids.erase a := (Multiset.cons_erase ha).symm
    _ = a ::ₘ b ::ₘ ((ids.erase a).erase b) :=
      congrArg (Multiset.cons a) (Multiset.cons_erase hb').symm

lemma drop_two_decomp {ids : Multiset ℕ} {a b : ℕ}
    (ha : a ∈ ids) (hb : b ∈ ids) (hab : a ≠ b) :
    Drop Z b (Drop Z a ids) =
      Retain Z a + Retain Z b + ((ids.erase a).erase b) := by
  by_cases hza : Z a <;> by_cases hzb : Z b
  · simp [Drop, Retain, hza, hzb]
  · simp only [Drop, Retain, hza, hzb, ↓reduceIte, Multiset.zero_add, Multiset.singleton_add]
    exact (Multiset.cons_erase ((Multiset.mem_erase_of_ne (Ne.symm hab)).mpr hb)).symm
  · simp only [Drop, Retain, hza, hzb, ↓reduceIte, Multiset.add_zero, Multiset.singleton_add]
    rw [Multiset.erase_comm]
    exact (Multiset.cons_erase ((Multiset.mem_erase_of_ne hab).mpr ha)).symm
  · simp only [Drop, Retain, hza, hzb, ↓reduceIte, Multiset.cons_add, Multiset.singleton_add]
    exact two_decomp ha hb hab

lemma available_step_decomp {start fork n t : ℕ} {A B : ℕ → ℕ}
    (hv : Valid start A B n)
    (hcap : ∀ x, Z x → ReadCount start A B n x ≤ Capacity fork x)
    (ht : t < n) :
    ∃ rest : Multiset ℕ,
      Available Z start fork A B t = A (start + t) ::ₘ B (start + t) ::ₘ rest ∧
      Available Z start fork A B (t + 1) =
        (start + t) ::ₘ
          (if Z (start + t) ∧ start + t = fork then
            (start + t) ::ₘ (Retain Z (A (start + t)) + Retain Z (B (start + t)) + rest)
          else Retain Z (A (start + t)) + Retain Z (B (start + t)) + rest) := by
  obtain ⟨ha, hb, hab⟩ := hv t ht
  have haa := source_available Z hv hcap ht ha (Or.inl rfl)
  have hba := source_available Z hv hcap ht hb (Or.inr rfl)
  refine ⟨((Available Z start fork A B t).erase (A (start + t))).erase (B (start + t)),
    two_decomp haa hba hab, ?_⟩
  simp only [Available, Give, drop_two_decomp Z haa hba hab]

end OnceResource.IndexCopies

namespace OnceResource.TokenMap

open IndexCopies

def token (k : ℕ) : Multiset ℕ := if k = 0 then 0 else {k}

def project (Z : ℕ → Prop) [DecidablePred Z] (M : ℕ → ℕ) (ids : Multiset ℕ) : Multiset ℕ :=
  (ids.filter (fun i => Z i ∧ M i ≠ 0)).map M

variable (Z : ℕ → Prop) [DecidablePred Z] (M : ℕ → ℕ)

lemma project_cons (i : ℕ) (ids : Multiset ℕ) :
    project Z M (i ::ₘ ids) = (if Z i then token (M i) else 0) + project Z M ids := by
  by_cases hz : Z i <;> by_cases hm : M i = 0 <;>
    simp [project, hz, hm, token]

lemma project_add (ids rest : Multiset ℕ) :
    project Z M (ids + rest) = project Z M ids + project Z M rest := by
  simp [project]

lemma project_retain (i : ℕ) : project Z M (Retain Z i) = 0 := by
  by_cases hz : Z i <;> simp [Retain, project, hz]

lemma project_mem {i : ℕ} {ids : Multiset ℕ} (hi : i ∈ ids)
    (hz : Z i) (hm : M i ≠ 0) : M i ∈ project Z M ids := by
  exact Multiset.mem_map.mpr ⟨i, Multiset.mem_filter.mpr ⟨hi, hz, hm⟩, rfl⟩

lemma project_give (fork out : ℕ) (ids : Multiset ℕ) :
    project Z M (Give Z fork out ids) =
      (if Z out then token (M out) else 0) +
      (if Z out ∧ out = fork then token (M out) else 0) + project Z M ids := by
  by_cases hf : out = fork
  · subst out
    by_cases hz : Z fork <;> simp [Give, hz, project_cons, Multiset.add_assoc]
  · by_cases hz : Z out <;> simp [Give, hz, hf, project_cons]

lemma project_step {ids rest : Multiset ℕ} {a b out fork : ℕ}
    (hid : ids = a ::ₘ b ::ₘ rest) (hab : a ≠ b) :
    project Z M (Give Z fork out (Drop Z b (Drop Z a ids))) =
      (if Z out then token (M out) else 0) +
      (if Z out ∧ out = fork then token (M out) else 0) + project Z M rest := by
  rw [project_give]
  have ha : a ∈ ids := by rw [hid]; simp
  have hb : b ∈ ids := by rw [hid]; simp
  rw [drop_two_decomp Z ha hb hab, project_add, project_add, project_retain, project_retain]
  simp only [Multiset.zero_add]
  have herase : (ids.erase a).erase b = rest := by rw [hid]; simp
  rw [herase]

lemma project_initial_one {start seed : ℕ} (hseed : seed < start)
    (hzseed : Z seed) (hmseed : M seed ≠ 0)
    (hother : ∀i<start, Z i → i ≠ seed → M i = 0) :
    project Z M (Multiset.range start) = {M seed} := by
  have hf : (Multiset.range start).filter (fun i => Z i ∧ M i ≠ 0) = {seed} := by
    apply Multiset.ext.mpr
    intro i
    rw [Multiset.count_eq_of_nodup ((Multiset.nodup_range start).filter _)]
    by_cases hi : i = seed
    · subst i
      simp [hseed, hzseed, hmseed]
    · have hn : ¬(i ∈ Multiset.range start ∧ Z i ∧ M i ≠ 0) := by
        rintro ⟨hi', hz, hm⟩
        exact hm (hother i (Multiset.mem_range.mp hi') hz hi)
      simp only [Multiset.mem_range] at hn
      simp [hn, hi]
  simp [project, hf]

lemma project_initial {start seed fork : ℕ} (hseed : seed < start)
    (hzseed : Z seed) (hmseed : M seed ≠ 0)
    (hother : ∀i<start, Z i → i ≠ seed → M i = 0) :
    project Z M (Initial Z start fork) =
      {M seed} + if fork = seed then {M seed} else 0 := by
  rw [Initial, project_add, project_initial_one Z M hseed hzseed hmseed hother]
  congr 1
  by_cases hf : fork = seed
  · subst fork
    simp [hseed, hzseed, hmseed, project, Multiset.filter_singleton]
  · by_cases h : Z fork ∧ fork < start
    · have hm : M fork = 0 := hother fork h.2 h.1 hf
      simp [h, hf, project, hm]
    · simp [h, hf, project]

end OnceResource.TokenMap

namespace OnceSimulation
open OnceResource OnceGeometry OncePositive

def contrib (S : Finset (Fin 10)) (m : ℕ) : Multiset ℕ :=
  if S = ∅ then TokenMap.token m else 0

def Healthy (s : State) : Prop :=
  s.1 < 16 ∧ s.2.1.length = 7 ∧ PoolsGood (poolView s.2.1)

def Preserves (s t : State) : Prop :=
  ∀ T m, Rep s.1 (poolView s.2.1) T m → Rep t.1 (poolView t.2.1) T m

def LocalResult (s q : State) (S : Finset (Fin 10)) (m : ℕ)
    (rest : Multiset ℕ) (group : Option (Fin 4)) : Prop :=
  Relation.ReflTransGen (fun a b : State => b ∈ successors a) s q ∧
  q.2.2.2 = s.2.2.2 ∧ Healthy q ∧
  (q.2.2.1 : Multiset ℕ) = contrib S m + rest ∧ Preserves s q ∧
  (S.Nonempty → Rep q.1 (poolView q.2.1) S m) ∧
  (∀ g : Fin 4, q.1.testBit g.val = true → s.1.testBit g.val = true ∨ group = some g)

lemma lift_token_step {s : State} {S : Finset (Fin 10)} {m k : ℕ} {rest : Multiset ℕ}
    (hs : Healthy s) (hS : S.Nonempty) (hm : Rep s.1 (poolView s.2.1) S m)
    (hk : k < 64) (hz : (s.2.2.1 : Multiset ℕ) = TokenMap.token k + rest) :
    ∃ q, LocalResult s q S (m ||| k) rest none := by
  have hne : S ≠ ∅ := hS.ne_empty
  by_cases hk0 : k = 0
  · subst k
    refine ⟨s, Relation.ReflTransGen.refl, rfl, hs, ?_, (fun _ _ h => h), ?_, ?_⟩
    · simpa [contrib, TokenMap.token, hne] using hz
    · intro _
      simpa using hm
    · exact fun _ h => Or.inl h
  · have hmem : k ∈ s.2.2.1 := by
      have hm' : k ∈ (s.2.2.1 : Multiset ℕ) := by rw [hz]; simp [TokenMap.token, hk0]
      exact hm'
    obtain ⟨q, hr, hu, hqz, hf, hl, hp, hpres, hrep⟩ :=
      positive_lift_step hs.1 hs.2.1 hs.2.2 hm hS hk hmem
    refine ⟨q, hr, hf, ⟨by simpa [hu] using hs.1, hl, hp⟩, ?_, hpres,
      (fun _ => hrep), ?_⟩
    · rw [hqz, ← Multiset.coe_erase, hz]
      simp [contrib, hne, TokenMap.token, hk0]
    · intro g hg
      exact Or.inl (hu ▸ hg)

lemma or_local {s : State} {S T : Finset (Fin 10)} {a b : ℕ} {rest : Multiset ℕ}
    (hs : Healthy s) (ha : S.Nonempty → Rep s.1 (poolView s.2.1) S a)
    (hb : T.Nonempty → Rep s.1 (poolView s.2.1) T b)
    (hab : a < 64 ∧ b < 64)
    (hz : (s.2.2.1 : Multiset ℕ) = contrib S a + contrib T b + rest) :
    ∃ q, LocalResult s q (S ∪ T) (a ||| b) rest none := by
  by_cases hS : S = ∅
  · subst S
    by_cases hT : T = ∅
    · subst T
      have hz' : (s.2.2.1 : Multiset ℕ) =
          ZeroTransitions.token a + ZeroTransitions.token b + rest := by
        simpa [contrib, ZeroTransitions.token, TokenMap.token] using hz
      obtain ⟨q, hr, hu, hf, hqz, hqu, hql, hqp, hpres⟩ :=
        zero_binary_positive_state a b false rest hs.1 hs.2.1 hs.2.2 hz'
      refine ⟨q, hr, hf, ⟨hqu, hql, hqp⟩, ?_, hpres, ?_, ?_⟩
      · simpa [contrib, ZeroTransitions.token, TokenMap.token] using hqz
      · simp
      · intro g hg
        exact Or.inl (hu ▸ hg)
    · have hTn : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr hT
      have hz' : (s.2.2.1 : Multiset ℕ) = TokenMap.token a + rest := by
        simpa [contrib, hT] using hz
      obtain ⟨q, hq⟩ := lift_token_step hs hTn (hb hTn) hab.1 hz'
      refine ⟨q, ?_⟩
      simpa [Nat.or_comm] using hq
  · have hSn : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
    by_cases hT : T = ∅
    · subst T
      have hz' : (s.2.2.1 : Multiset ℕ) = TokenMap.token b + rest := by
        simpa [contrib, hS] using hz
      obtain ⟨q, hq⟩ := lift_token_step hs hSn (ha hSn) hab.2 hz'
      exact ⟨q, by simpa using hq⟩
    · have hTn : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr hT
      have hST : S ∪ T ≠ ∅ := (hSn.mono Finset.subset_union_left).ne_empty
      refine ⟨s, Relation.ReflTransGen.refl, rfl, hs, ?_, (fun _ _ h => h), ?_, ?_⟩
      · simpa [contrib, hS, hT, hST] using hz
      · intro _
        exact rep_or hs.2.2 (ha hSn) (hb hTn)
      · exact fun _ h => Or.inl h

lemma marked_group {used : ℕ} {g h : Fin 4}
    (ht : (used ||| (1 <<< g.val)).testBit h.val = true) :
    used.testBit h.val = true ∨ g = h := by
  rw [Nat.testBit_or, Bool.or_eq_true] at ht
  rcases ht with ht | ht
  · exact Or.inl ht
  · right
    have hsingle := testBit_singleton_iff.mp ht
    exact Fin.ext hsingle

lemma pure_local {s : State} {g : Fin 4} {a b : ℕ} {rest : Multiset ℕ}
    (hs : Healthy s) (ha : Rep s.1 (poolView s.2.1) (port g false) a)
    (hb : Rep s.1 (poolView s.2.1) (port g true) b)
    (hk : a &&& b < 64) (hunused : s.1.testBit g.val = false)
    (hz : (s.2.2.1 : Multiset ℕ) = rest) :
    ∃ q, LocalResult s q ∅ (a &&& b) rest (some g) := by
  by_cases hk0 : a &&& b = 0
  · refine ⟨s, Relation.ReflTransGen.refl, rfl, hs, ?_, (fun _ _ h => h), ?_, ?_⟩
    · simpa [contrib, TokenMap.token, hk0] using hz
    · simp
    · exact fun _ h => Or.inl h
  · let q := prune (s.1 ||| (1 <<< g.val), s.2.1, insertZero (a &&& b) s.2.2.1, s.2.2.2)
    obtain ⟨hr, hu, hl, hp, hpres⟩ := positive_group_step hs.1 hs.2.2 ha hb hunused hk hk0
    refine ⟨q, Relation.ReflTransGen.single hr, rfl, ⟨hu, hl, hp⟩, ?_, hpres, ?_, ?_⟩
    · change (insertZero (a &&& b) s.2.2.1 : Multiset ℕ) = _
      rw [insertZero_multiset, hz]
      simp [contrib, TokenMap.token, hk0]
    · simp
    · intro h hh
      rcases marked_group hh with hh | hh
      · exact Or.inl hh
      · exact Or.inr (congrArg some hh)

lemma zero_local {s : State} {a b : ℕ} {rest : Multiset ℕ}
    (hs : Healthy s)
    (hz : (s.2.2.1 : Multiset ℕ) = TokenMap.token a + TokenMap.token b + rest) :
    ∃ q, LocalResult s q ∅ (a &&& b) rest none := by
  obtain ⟨q, hr, hu, hf, hqz, hqu, hql, hqp, hpres⟩ :=
    zero_binary_positive_state a b true rest hs.1 hs.2.1 hs.2.2 hz
  refine ⟨q, hr, hf, ⟨hqu, hql, hqp⟩, ?_, hpres, ?_, ?_⟩
  · exact hqz
  · simp
  · intro g hg
    exact Or.inl (hu ▸ hg)

end OnceSimulation

namespace OnceSimulation
open OnceResource OnceGeometry OncePositive

lemma gate_local {s : State} {S T U : Finset (Fin 10)} {a b c : ℕ}
    {rest : Multiset ℕ} (op : Bool) (group : Option (Fin 4))
    (hs : Healthy s) (ha : S.Nonempty → Rep s.1 (poolView s.2.1) S a)
    (hb : T.Nonempty → Rep s.1 (poolView s.2.1) T b)
    (hm : a < 64 ∧ b < 64 ∧ c < 64)
    (hz : (s.2.2.1 : Multiset ℕ) = contrib S a + contrib T b + rest)
    (hunused : ∀g : Fin 4, group = some g → s.1.testBit g.val = false)
    (hsem : if op then
      U = ∅ ∧ c = a &&& b ∧
        (match group with
        | none => S = ∅ ∧ T = ∅
        | some g => (S = port g false ∧ T = port g true) ∨
          (S = port g true ∧ T = port g false))
      else group = none ∧ U = S ∪ T ∧ c = a ||| b) :
    ∃q, LocalResult s q U c rest group := by
  cases op with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hsem
    obtain ⟨rfl, rfl, rfl⟩ := hsem
    exact or_local hs ha hb ⟨hm.1, hm.2.1⟩ hz
  | true =>
    simp only [↓reduceIte] at hsem
    obtain ⟨rfl, rfl, hports⟩ := hsem
    cases group with
    | none =>
      obtain ⟨rfl, rfl⟩ := hports
      exact zero_local hs (by simpa [contrib] using hz)
    | some g =>
      have hl : (port g false).Nonempty := by fin_cases g <;> decide
      have hr : (port g true).Nonempty := by fin_cases g <;> decide
      have hu := hunused g rfl
      rcases hports with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have hz' : (s.2.2.1 : Multiset ℕ) = rest := by
          simpa [contrib, hl.ne_empty, hr.ne_empty] using hz
        exact pure_local hs (ha hl) (hb hr) hm.2.2 hu hz'
      · have hz' : (s.2.2.1 : Multiset ℕ) = rest := by
          simpa [contrib, hl.ne_empty, hr.ne_empty] using hz
        obtain ⟨q, hq⟩ := pure_local hs (hb hl) (ha hr)
          (by simpa [Nat.and_comm] using hm.2.2) hu hz'
        exact ⟨q, by simpa [Nat.and_comm] using hq⟩

end OnceSimulation

namespace OnceSimulation

open OnceResource OncePositive IndexCopies TokenMap

abbrev Reach (s t : State) : Prop :=
  Relation.ReflTransGen (fun a b : State => b ∈ successors a) s t

def ProgramCallback (S : ℕ → Finset (Fin 10)) (M A B : ℕ → ℕ)
    (G : ℕ → Option (Fin 4)) (start n : ℕ) : Prop :=
  ∀ t < n, ∀ (s : State) (rest : Multiset ℕ),
    Healthy s →
    ((S (A (start + t))).Nonempty →
      Rep s.1 (poolView s.2.1) (S (A (start + t))) (M (A (start + t)))) →
    ((S (B (start + t))).Nonempty →
      Rep s.1 (poolView s.2.1) (S (B (start + t))) (M (B (start + t)))) →
    (s.2.2.1 : Multiset ℕ) =
      contrib (S (A (start + t))) (M (A (start + t))) +
      contrib (S (B (start + t))) (M (B (start + t))) + rest →
    (∀ g : Fin 4, G (start + t) = some g → s.1.testBit g.val = false) →
    ∃ q : State, Reach s q ∧ q.2.2.2 = s.2.2.2 ∧ Healthy q ∧
      (q.2.2.1 : Multiset ℕ) = contrib (S (start + t)) (M (start + t)) + rest ∧
      Preserves s q ∧
      ((S (start + t)).Nonempty →
        Rep q.1 (poolView q.2.1) (S (start + t)) (M (start + t))) ∧
      ∀ g : Fin 4, q.1.testBit g.val = true →
        s.1.testBit g.val = true ∨ G (start + t) = some g

def GroupUnique (G : ℕ → Option (Fin 4)) (start n : ℕ) : Prop :=
  ∀ i < n, ∀ j < n, ∀ g : Fin 4,
    G (start + i) = some g → G (start + j) = some g → i = j

def ProgramInv (S : ℕ → Finset (Fin 10)) (M A B : ℕ → ℕ)
    (G : ℕ → Option (Fin 4)) (start fork t : ℕ) (s : State) : Prop :=
  Healthy s ∧
    (s.2.2.1 : Multiset ℕ) =
      project (fun w => S w = ∅) M (Available (fun w => S w = ∅) start fork A B t) ∧
    (∀ w < start + t, (S w).Nonempty → Rep s.1 (poolView s.2.1) (S w) (M w)) ∧
    s.2.2.2 = decide (S fork = ∅ ∧ M fork ≠ 0 ∧ fork < start + t) ∧
    ∀ g : Fin 4, s.1.testBit g.val = true → ∃ j < t, G (start + j) = some g

lemma preserves_refl (s : State) : Preserves s s := fun _ _ h => h

lemma finish_output_fork (S : ℕ → Finset (Fin 10)) (M : ℕ → ℕ)
    (fork out : ℕ) {q : State} {rest : Multiset ℕ}
    (hq : Healthy q)
    (hflag : q.2.2.2 = decide (S fork = ∅ ∧ M fork ≠ 0 ∧ fork < out))
    (hzero : (q.2.2.1 : Multiset ℕ) = contrib (S out) (M out) + rest) :
    ∃ r : State, Reach q r ∧ r.1 = q.1 ∧ Healthy r ∧ Preserves q r ∧
      (r.2.2.1 : Multiset ℕ) =
        contrib (S out) (M out) + (if S out = ∅ ∧ out = fork then token (M out) else 0) + rest ∧
      r.2.2.2 = decide (S fork = ∅ ∧ M fork ≠ 0 ∧ fork < out + 1) := by
  by_cases hevent : S out = ∅ ∧ out = fork ∧ M out ≠ 0
  · obtain ⟨hz, hout, hm⟩ := hevent
    subst fork
    have hf : q.2.2.2 = false := by simp [hflag]
    have hk : M out ∈ q.2.2.1 := by
      have hk' : M out ∈ (q.2.2.1 : Multiset ℕ) := by
        rw [hzero]
        simp [contrib, hz, token, hm]
      exact hk'
    obtain ⟨r, hr, hused, hlen, hgood, hpres, hzeros, htrue⟩ :=
      exists_fork_state hk hf hq.1 hq.2.2
    refine ⟨r, Relation.ReflTransGen.single hr, hused, ?_, hpres, ?_, ?_⟩
    · exact ⟨hused ▸ hq.1, hlen, hgood⟩
    · rw [hzeros, hzero]
      simp [contrib, hz, token, hm, Multiset.add_assoc]
    · simp [htrue, hz, hm]
  · refine ⟨q, Relation.ReflTransGen.refl, rfl, hq, preserves_refl q, ?_, ?_⟩
    · rw [hzero]
      by_cases hz : S out = ∅
      · by_cases ho : out = fork
        · have hm : M out = 0 := by by_contra hm; exact hevent ⟨hz, ho, hm⟩
          subst fork
          simp [hz, hm, token]
        · simp [ho]
      · simp [hz]
    · rw [hflag]
      congr 1
      apply propext
      constructor
      · rintro ⟨hz, hm, hf⟩
        exact ⟨hz, hm, by omega⟩
      · rintro ⟨hz, hm, hf⟩
        refine ⟨hz, hm, ?_⟩
        have hne : out ≠ fork := by
          intro ho
          exact hevent ⟨ho ▸ hz, ho, ho ▸ hm⟩
        omega

lemma program_inv_step {S : ℕ → Finset (Fin 10)} {M A B : ℕ → ℕ}
    {G : ℕ → Option (Fin 4)} {start fork n t : ℕ} {s : State}
    (hv : Valid start A B n)
    (hcap : ∀ w, S w = ∅ → ReadCount start A B n w ≤ Capacity fork w)
    (hgroups : GroupUnique G start n) (hcallback : ProgramCallback S M A B G start n)
    (ht : t < n) (hinv : ProgramInv S M A B G start fork t s) :
    ∃ r : State, Reach s r ∧ ProgramInv S M A B G start fork (t + 1) r := by
  obtain ⟨hhealthy, hzeros, hreps, hflag, hused⟩ := hinv
  obtain ⟨ha, hb, hab⟩ := hv t ht
  obtain ⟨rest, hids, _⟩ := available_step_decomp (fun w => S w = ∅) hv hcap ht
  have hzero_input : (s.2.2.1 : Multiset ℕ) =
      contrib (S (A (start + t))) (M (A (start + t))) +
      contrib (S (B (start + t))) (M (B (start + t))) + project (fun w => S w = ∅) M rest := by
    rw [hzeros, hids, project_cons, project_cons]
    simp only [contrib, Multiset.add_assoc]
  have hunused : ∀ g : Fin 4, G (start + t) = some g → s.1.testBit g.val = false := by
    intro g hg
    cases hbit : s.1.testBit g.val with
    | false => rfl
    | true =>
      obtain ⟨j, hj, hjg⟩ := hused g hbit
      have heq := hgroups t ht j (by omega) g hg hjg
      omega
  obtain ⟨q, hreachq, hflagq, hhealthyq, hzeroq, hpresq, hnewq, husedq⟩ :=
    hcallback t ht s (project (fun w => S w = ∅) M rest) hhealthy
      (hreps _ ha) (hreps _ hb) hzero_input hunused
  obtain ⟨r, hreachr, husedr, hhealthyr, hpresr, hzeror, hflagr⟩ :=
    finish_output_fork S M fork (start + t) hhealthyq (hflagq.trans hflag) hzeroq
  refine ⟨r, hreachq.trans hreachr, hhealthyr, ?_, ?_, ?_, ?_⟩
  · rw [Available, project_step (fun w => S w = ∅) M hids hab]
    exact hzeror
  · intro w hw hSw
    by_cases hold : w < start + t
    · exact hpresr _ _ (hpresq _ _ (hreps w hold hSw))
    · have heq : w = start + t := by omega
      subst w
      exact hpresr _ _ (hnewq hSw)
  · simpa only [Nat.add_assoc] using hflagr
  · intro g hg
    rw [husedr] at hg
    rcases husedq g hg with hg | hg
    · obtain ⟨j, hj, hjg⟩ := hused g hg
      exact ⟨j, by omega, hjg⟩
    · exact ⟨t, by omega, hg⟩

lemma program_induction_prefix {S : ℕ → Finset (Fin 10)} {M A B : ℕ → ℕ}
    {G : ℕ → Option (Fin 4)} {start fork n : ℕ} {s₀ : State}
    (hv : Valid start A B n)
    (hcap : ∀ w, S w = ∅ → ReadCount start A B n w ≤ Capacity fork w)
    (hgroups : GroupUnique G start n) (hcallback : ProgramCallback S M A B G start n)
    (hinit : ProgramInv S M A B G start fork 0 s₀) :
    ∀ t ≤ n, ∃ s : State, Reach s₀ s ∧ ProgramInv S M A B G start fork t s := by
  intro t
  induction t with
  | zero =>
    intro _
    exact ⟨s₀, Relation.ReflTransGen.refl, hinit⟩
  | succ t ih =>
    intro ht
    obtain ⟨s, hreach, hinv⟩ := ih (by omega)
    obtain ⟨r, hstep, hinvr⟩ := program_inv_step hv hcap hgroups hcallback (by omega) hinv
    exact ⟨r, hreach.trans hstep, hinvr⟩

lemma program_induction {S : ℕ → Finset (Fin 10)} {M A B : ℕ → ℕ}
    {G : ℕ → Option (Fin 4)} {start fork n : ℕ} {s₀ : State}
    (hv : Valid start A B n)
    (hcap : ∀ w, S w = ∅ → ReadCount start A B n w ≤ Capacity fork w)
    (hgroups : GroupUnique G start n) (hcallback : ProgramCallback S M A B G start n)
    (hinit : ProgramInv S M A B G start fork 0 s₀) :
    ∃ s : State, Reach s₀ s ∧ ProgramInv S M A B G start fork n s :=
  program_induction_prefix hv hcap hgroups hcallback hinit n (Nat.le_refl n)

end OnceSimulation

namespace OnceSimulation
open OnceResource OnceGeometry OncePositive

def ProgramSemantics (S : ℕ → Finset (Fin 10)) (M A B : ℕ → ℕ)
    (G : ℕ → Option (Fin 4)) (Op : ℕ → Bool) (start n : ℕ) : Prop :=
  ∀ t < n,
    if Op (start + t) then
      S (start + t) = ∅ ∧ M (start + t) = M (A (start + t)) &&& M (B (start + t)) ∧
        (match G (start + t) with
        | none => S (A (start + t)) = ∅ ∧ S (B (start + t)) = ∅
        | some g =>
          (S (A (start + t)) = port g false ∧ S (B (start + t)) = port g true) ∨
          (S (A (start + t)) = port g true ∧ S (B (start + t)) = port g false))
    else G (start + t) = none ∧
      S (start + t) = S (A (start + t)) ∪ S (B (start + t)) ∧
      M (start + t) = M (A (start + t)) ||| M (B (start + t))

lemma semantic_callback {S : ℕ → Finset (Fin 10)} {M A B : ℕ → ℕ}
    {G : ℕ → Option (Fin 4)} {Op : ℕ → Bool} {start n : ℕ}
    (hm : ∀w, M w < 64) (hsem : ProgramSemantics S M A B G Op start n) :
    ProgramCallback S M A B G start n := by
  intro t ht s rest hs ha hb hz hgroups
  generalize hg : G (start + t) = group at hgroups ⊢
  cases group with
  | none =>
    exact gate_local (Op (start + t)) none hs ha hb
      ⟨hm _, hm _, hm _⟩ hz hgroups (by simpa [hg] using hsem t ht)
  | some g =>
    exact gate_local (Op (start + t)) (some g) hs ha hb
      ⟨hm _, hm _, hm _⟩ hz hgroups (by simpa [hg] using hsem t ht)

end OnceSimulation

namespace OnceSimulation

open OnceResource OnceGeometry OncePositive

lemma initial_state_witness (S : ℕ → Finset (Fin 10)) (M : ℕ → ℕ)
    {start seed fork : ℕ} (hseed : seed < start)
    (hSseed : S seed = ∅) (hMseed : M seed = 63)
    (hother : ∀ w < start, S w = ∅ → w ≠ seed → M w = 0)
    (hpositive : ∀ w < start, (S w).Nonempty → M w = rawMask (S w)) :
    ∃ s : State,
      Relation.ReflTransGen (fun p q : State => q ∈ successors p) initial s ∧
      Healthy s ∧ s.1 = 0 ∧
      (s.2.2.1 : Multiset ℕ) = TokenMap.project (fun w => S w = ∅) M
        (IndexCopies.Initial (fun w => S w = ∅) start fork) ∧
      (∀ w < start, (S w).Nonempty → Rep s.1 (poolView s.2.1) (S w) (M w)) ∧
      s.2.2.2 = decide (S fork = ∅ ∧ M fork ≠ 0 ∧ fork < start) := by
  have hi : Healthy initial := ⟨by decide, rfl, poolsGood_replicate_one⟩
  have hr : ∀ w < start, (S w).Nonempty →
      Rep initial.1 (poolView initial.2.1) (S w) (M w) := by
    intro w hw hS
    rw [hpositive w hw hS]
    exact rep_raw hi.2.2 _
  have hMne : M seed ≠ 0 := by rw [hMseed]; decide
  have hproj := TokenMap.project_initial (fun w => S w = ∅) M
    (fork := fork) hseed hSseed hMne hother
  rw [hMseed] at hproj
  have hflag : (S fork = ∅ ∧ M fork ≠ 0 ∧ fork < start) ↔ fork = seed := by
    constructor
    · rintro ⟨hS, hM, hlt⟩
      by_contra hne
      exact hM (hother fork hlt hS hne)
    · intro heq
      subst fork
      exact ⟨hSseed, hMne, hseed⟩
  by_cases hf : fork = seed
  · have hz : (initial.2.2.1 : Multiset ℕ) = ZeroTransitions.token 63 + 0 := by decide
    obtain ⟨s, hreach, hu, hfork, hzeros, hsused, hslen, hsgood, hpres⟩ :=
      zero_fork_positive_state 63 0 hi.1 hi.2.1 hi.2.2 rfl hz
    refine ⟨s, hreach, ⟨hsused, hslen, hsgood⟩, hu, ?_, ?_, ?_⟩
    · rw [hproj]
      simpa [hf, ZeroTransitions.token] using hzeros
    · intro w hw hS
      exact hpres _ _ (hr w hw hS)
    · rw [decide_eq_true (hflag.mpr hf)]
      simpa using hfork
  · refine ⟨initial, Relation.ReflTransGen.refl, hi, rfl, ?_, hr, ?_⟩
    · rw [hproj]
      simp [initial, hf]
    · simp [initial, hflag, hf]

end OnceSimulation

namespace OnceSimulation

open OnceResource OncePositive OnceGeometry IndexCopies TokenMap

lemma program_target_excluded {S : ℕ → Finset (Fin 10)} {M A B : ℕ → ℕ}
    {G : ℕ → Option (Fin 4)} {start fork n w : ℕ}
    (hsafe : ∀ s : State, Reach initial s → 56 ∉ s.2.2.1)
    (hv : Valid start A B n)
    (hcap : ∀ u, S u = ∅ → ReadCount start A B n u ≤ Capacity fork u)
    (hgroups : GroupUnique G start n) (hcallback : ProgramCallback S M A B G start n)
    (hinit : ∃ s₀ : State, Reach initial s₀ ∧ ProgramInv S M A B G start fork 0 s₀)
    (hw : w ∈ Available (fun u => S u = ∅) start fork A B n)
    (hSw : S w = ∅) (hMw : M w = 56) : False := by
  obtain ⟨s₀, hreach₀, hinv₀⟩ := hinit
  obtain ⟨s, hreach, hinv⟩ := program_induction hv hcap hgroups hcallback hinv₀
  have hMne : M w ≠ 0 := by omega
  have hmem := project_mem (fun u => S u = ∅) M hw hSw hMne
  rw [hMw] at hmem
  have htarget : 56 ∈ s.2.2.1 := by
    have hm : 56 ∈ (s.2.2.1 : Multiset ℕ) := by
      rw [hinv.2.1]
      exact hmem
    exact hm
  exact hsafe s (hreach₀.trans hreach) htarget

end OnceSimulation

namespace OnceSimulation

open OnceResource OncePositive OnceGeometry IndexCopies TokenMap

lemma program_target_excluded_certified {S : ℕ → Finset (Fin 10)} {M A B : ℕ → ℕ}
    {G : ℕ → Option (Fin 4)} {start fork n w : ℕ}
    (hv : Valid start A B n)
    (hcap : ∀ u, S u = ∅ → ReadCount start A B n u ≤ Capacity fork u)
    (hgroups : GroupUnique G start n) (hcallback : ProgramCallback S M A B G start n)
    (hinit : ∃ s₀ : State, Reach initial s₀ ∧ ProgramInv S M A B G start fork 0 s₀)
    (hw : w ∈ Available (fun u => S u = ∅) start fork A B n)
    (hSw : S w = ∅) (hMw : M w = 56) : False := by
  exact program_target_excluded (fun _ h => reachable_no_target h)
    hv hcap hgroups hcallback hinit hw hSw hMw

end OnceSimulation

namespace OnceResourceBudget

open PEqualNP.Outside.L_meta_2590.DAGBridge.DagTools

variable {n : ℕ} {D : Dag}

lemma zero_reader_inner (hS : Strict n D) {j w : ℕ} (hj : j < D.length)
    (he : supp n D w = ∅) (hr : opA D j = w ∨ opB D j = w) :
    w ∈ (DAGBridge.DagTools.inner n D).filter (fun u => ¬(supp n D u).Nonempty) := by
  have hw : w < n + j := by
    obtain ⟨ha, hb, _⟩ := hS j hj
    rcases hr with hr | hr <;> omega
  apply Finset.mem_filter.mpr
  constructor
  · simp only [DAGBridge.DagTools.inner, Finset.mem_range]
    omega
  · simp [he]

lemma zero_branch_inner (hS : Strict n D) {w : ℕ} (he : supp n D w = ∅)
    (hf : 2 ≤ fanout D w) :
    w ∈ (DAGBridge.DagTools.inner n D).filter (fun u => ¬(supp n D u).Nonempty) := by
  have hp : 0 < (readers D w).card := by change 0 < fanout D w; omega
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hp
  obtain ⟨hj, hr⟩ := Finset.mem_filter.mp hj
  exact zero_reader_inner hS (Finset.mem_range.mp hj) he hr

lemma zero_fanout_le_two (hS : Strict n D) (hB : Bzero n D ≤ 1)
    {w : ℕ} (he : supp n D w = ∅) : fanout D w ≤ 2 := by
  by_cases hf : 2 ≤ fanout D w
  · have hsum : fanout D w - 1 ≤ Bzero n D := by
      unfold Bzero surplusOn
      exact Finset.single_le_sum (f := fun u => fanout D u - 1)
        (fun _ _ => Nat.zero_le _) (zero_branch_inner hS he hf)
    omega
  · omega

lemma zero_branch_unique (hS : Strict n D) (hB : Bzero n D ≤ 1)
    {a b : ℕ} (ha : supp n D a = ∅) (hb : supp n D b = ∅)
    (hfa : 2 ≤ fanout D a) (hfb : 2 ≤ fanout D b) : a = b := by
  by_contra hne
  have hsub : ({a, b} : Finset ℕ) ⊆
      (DAGBridge.DagTools.inner n D).filter (fun u => ¬(supp n D u).Nonempty) := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact zero_branch_inner hS ha hfa
    · have hwb : w = b := Finset.mem_singleton.mp hw
      subst w
      exact zero_branch_inner hS hb hfb
  have hsum := Finset.sum_le_sum_of_subset (f := fun w => fanout D w - 1) hsub
  rw [Finset.sum_pair hne] at hsum
  unfold Bzero surplusOn at hB
  omega

lemma exists_fork_id (hS : Strict n D) (hB : Bzero n D ≤ 1) :
    ∃ fork : ℕ, ∀ w, supp n D w = ∅ →
      fanout D w ≤ if w = fork then 2 else 1 := by
  classical
  by_cases hb : ∃ b, supp n D b = ∅ ∧ 2 ≤ fanout D b
  · obtain ⟨b, hb, hfb⟩ := hb
    refine ⟨b, ?_⟩
    intro w hw
    by_cases hwb : w = b
    · simp only [hwb, ite_true]
      exact zero_fanout_le_two hS hB hb
    · simp only [hwb, ite_false]
      by_contra hbad
      have hwf : 2 ≤ fanout D w := by omega
      exact hwb (zero_branch_unique hS hB hw hb hwf hfb)
  · refine ⟨0, ?_⟩
    intro w hw
    have hf : fanout D w ≤ 1 := by
      by_contra hbad
      exact hb ⟨w, hw, by omega⟩
    split_ifs <;> omega

end OnceResourceBudget

namespace OnceActualSchedule

open DAGBridge.DagTools OnceResource.IndexCopies

def start (g : ℕ) : ℕ := 10 + g + 1

def remaining (D : Dag) (g : ℕ) : ℕ := D.length - g - 1

def sourceA (D : Dag) (w : ℕ) : ℕ := opA D (w - 10)

def sourceB (D : Dag) (w : ℕ) : ℕ := opB D (w - 10)

abbrev Zero (D : Dag) (w : ℕ) : Prop := supp 10 D w = ∅

def ids (D : Dag) (g fork t : ℕ) : Multiset ℕ :=
  Available (Zero D) (start g) fork (sourceA D) (sourceB D) t

lemma continuation_index (g t : ℕ) : start g + t - 10 = g + 1 + t := by
  unfold start
  omega

lemma continuation_valid {D : Dag} (hS : Strict 10 D) (g : ℕ) :
    Valid (start g) (sourceA D) (sourceB D) (remaining D g) := by
  intro t ht
  have hj : g + 1 + t < D.length := by unfold remaining at ht; omega
  have hs := hS (g + 1 + t) hj
  have hout : 10 + (g + 1 + t) = start g + t := by unfold start; omega
  simpa only [sourceA, sourceB, continuation_index, hout] using hs

lemma continuation_readCount_le_fanout (D : Dag) (g w : ℕ) :
    ReadCount (start g) (sourceA D) (sourceB D) (remaining D g) w ≤ fanout D w := by
  unfold ReadCount fanout
  apply Finset.card_le_card_of_injOn (fun j => g + 1 + j)
  · intro j hj
    obtain ⟨hj, hr⟩ := Finset.mem_filter.mp hj
    have hjt := Finset.mem_range.mp hj
    have hjD : g + 1 + j < D.length := by unfold remaining at hjt; omega
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr hjD, ?_⟩
    simpa only [sourceA, sourceB, continuation_index] using hr
  · intro i _ j _ heq
    change g + 1 + i = g + 1 + j at heq
    omega

lemma exists_continuation_fork {D : Dag} (hS : Strict 10 D) (hB : Bzero 10 D ≤ 1)
    (g : ℕ) :
    ∃ fork : ℕ, ∀ w, Zero D w →
      ReadCount (start g) (sourceA D) (sourceB D) (remaining D g) w ≤ Capacity fork w := by
  obtain ⟨fork, hcap⟩ := OnceResourceBudget.exists_fork_id hS hB
  refine ⟨fork, ?_⟩
  intro w hw
  exact (continuation_readCount_le_fanout D g w).trans (hcap w hw)

lemma actual_id_count {D : Dag} (hS : Strict 10 D) (g fork t w : ℕ)
    (ht : t ≤ remaining D g) :
    (ids D g fork t).count w =
      if w < start g + t then
        if Zero D w then Capacity fork w - ReadCount (start g) (sourceA D) (sourceB D) t w else 1
      else 0 := by
  exact count_available (Zero D) (continuation_valid hS g) t ht w

end OnceActualSchedule

namespace OnceActualSchedule

open DAGBridge.DagTools OnceResource.IndexCopies

lemma final_fanout_zero {D : Dag} (hS : Strict 10 D) : fanout D (outW 10 D) = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  obtain ⟨hj, hr⟩ := Finset.mem_filter.mp hj
  have hjD := Finset.mem_range.mp hj
  obtain ⟨ha, hb, _⟩ := hS j hjD
  unfold outW at hr
  rcases hr with hr | hr <;> omega

lemma final_readCount_zero {D : Dag} (hS : Strict 10 D) (g : ℕ) :
    ReadCount (start g) (sourceA D) (sourceB D) (remaining D g) (outW 10 D) = 0 := by
  have hle := continuation_readCount_le_fanout D g (outW 10 D)
  rw [final_fanout_zero hS] at hle
  omega

lemma final_output_count {D : Dag} (hS : Strict 10 D) {g : ℕ}
    (hg : g < D.length) (fork : ℕ) :
    (ids D g fork (remaining D g)).count (outW 10 D) = Copies (Zero D) fork (outW 10 D) := by
  rw [actual_id_count hS g fork (remaining D g) (outW 10 D) (Nat.le_refl _)]
  have hbound : outW 10 D < start g + remaining D g := by
    unfold outW start remaining
    omega
  rw [ite_eq_left hbound, final_readCount_zero hS g]
  simp only [Copies, Nat.sub_zero]

lemma final_output_available {D : Dag} (hS : Strict 10 D) {g : ℕ}
    (hg : g < D.length) (fork : ℕ) :
    outW 10 D ∈ ids D g fork (remaining D g) := by
  apply Multiset.count_pos.mp
  rw [final_output_count hS hg fork]
  unfold Copies Capacity
  split_ifs <;> decide

end OnceActualSchedule

namespace OnceGeometry

open PEqualNP.Outside.L_meta_2590.DAGBridge.DagTools

lemma rowSet_mem_crossPairs : ∀ r : Fin 6,
    rowSet r ∈ FiveGroup.ResourceExclusion.CrossPairs := by decide

lemma wireMask_of_ordinary {D : Dag} (hS : Strict 10 D) {w : ℕ}
    (ho : FiveGroup.ResourceExclusion.Ordinary (FiveGroup.DAGBridge.DagResource D w)) :
    wireMask D w = rawMask (supp 10 D w) := by
  unfold wireMask rawMask
  apply congrArg mask
  funext r
  have hu := ho (rowSet r) (rowSet_mem_crossPairs r)
  change val D (rowInput r) w = true → (supp 10 D w ∩ rowSet r).Nonempty at hu
  by_cases hh : (supp 10 D w ∩ rowSet r).Nonempty
  · rw [support_row_true hS hh, decide_eq_true hh]
  · cases hv : val D (rowInput r) w with
    | false => simp [hh]
    | true => exact False.elim (hh (hu hv))

lemma before_seed_wireMask {D : Dag} (hS : Strict 10 D) {g : ℕ}
    (hg : g < D.length) (hsides : FiveGroup.DAGBridge.OtherAndSides D g)
    {w : ℕ} (hw : w < 10 + g) :
    wireMask D w = rawMask (supp 10 D w) :=
  wireMask_of_ordinary hS (FiveGroup.DAGBridge.before_seed_ordinary hS hg hsides w hw)

lemma before_seed_zero {D : Dag} (hS : Strict 10 D) {g : ℕ}
    (hg : g < D.length) (hsides : FiveGroup.DAGBridge.OtherAndSides D g)
    {w : ℕ} (hw : w < 10 + g) (hz : supp 10 D w = ∅) : wireMask D w = 0 := by
  rw [before_seed_wireMask hS hg hsides hw, hz, rawMask_empty]

lemma dirty_wire_mask_unoriented {D : Dag} (hS : Strict 10 D) {g : ℕ}
    (hg : g < D.length) (ht : tag D g = true)
    (hdirty : FiveGroup.DAGBridge.DirtySides D g) : wireMask D (10 + g) = 63 := by
  have hd := (FiveGroup.DAGBridge.dirty_seed hS hg ht hdirty).2
  have heq : (fun r => val D (rowInput r) (10 + g)) = (fun _ => true) := by
    funext r
    exact hd (rowSet r) (rowSet_mem_crossPairs r)
  unfold wireMask
  rw [heq]
  decide

end OnceGeometry

namespace OnceSimulation

open OnceResource OnceGeometry OncePositive
open PEqualNP.Outside.L_meta_2590.DAGBridge.DagTools

lemma actual_initial_state {D : Dag} (hS : Strict 10 D) {g fork : ℕ}
    (hg : g < D.length) (ht : tag D g = true)
    (hdirty : FiveGroup.DAGBridge.DirtySides D g)
    (hsides : FiveGroup.DAGBridge.OtherAndSides D g) :
    ∃ s : State,
      Relation.ReflTransGen (fun p q : State => q ∈ successors p) initial s ∧
      Healthy s ∧ s.1 = 0 ∧
      (s.2.2.1 : Multiset ℕ) = TokenMap.project (fun w => supp 10 D w = ∅) (wireMask D)
        (IndexCopies.Initial (fun w => supp 10 D w = ∅) (10 + g + 1) fork) ∧
      (∀ w < 10 + g + 1, (supp 10 D w).Nonempty →
        Rep s.1 (poolView s.2.1) (supp 10 D w) (wireMask D w)) ∧
      s.2.2.2 = decide (supp 10 D fork = ∅ ∧ wireMask D fork ≠ 0 ∧ fork < 10 + g + 1) := by
  have hseed : supp 10 D (10 + g) = ∅ :=
    (FiveGroup.DAGBridge.dirty_seed hS hg ht hdirty).1
  apply initial_state_witness (supp 10 D) (wireMask D) (seed := 10 + g)
    (by omega) hseed (dirty_wire_mask_unoriented hS hg ht hdirty)
  · intro w hw hz hne
    exact before_seed_zero hS hg hsides (by omega) hz
  · intro w hw hpos
    have hne : w ≠ 10 + g := by
      intro heq
      subst w
      exact hpos.ne_empty hseed
    exact before_seed_wireMask hS hg hsides (by omega)

end OnceSimulation

namespace OnceSimulation
open OnceResource OnceGeometry OncePositive OnceActualSchedule
open DAGBridge.DagTools

end OnceSimulation

namespace OnceSimulation
open OnceResource OnceGeometry OncePositive OnceActualSchedule
open DAGBridge.DagTools

lemma actual_target_exclusion {D : Dag} (hS : Strict 10 D) (hB : Bzero 10 D ≤ 1)
    {g : ℕ} (hg : g < D.length) (ht : tag D g = true)
    (hdirty : FiveGroup.DAGBridge.DirtySides D g)
    (hsides : FiveGroup.DAGBridge.OtherAndSides D g)
    {G : ℕ → Option (Fin 4)}
    (hgroups : GroupUnique G (start g) (remaining D g))
    (hsem : ProgramSemantics (supp 10 D) (wireMask D) (sourceA D) (sourceB D) G
      (fun w => tag D (w - 10)) (start g) (remaining D g)) :
    ¬ (supp 10 D (10 + D.length - 1) = ∅ ∧ wireMask D (10 + D.length - 1) = 56) := by
  intro hout
  obtain ⟨fork, hcap⟩ := exists_continuation_fork hS hB g
  obtain ⟨s₀, hr, hh, hu, hz, hp, hf⟩ := actual_initial_state (fork := fork) hS hg ht hdirty hsides
  have hinit : ∃ s₀ : State, Reach initial s₀ ∧
      ProgramInv (supp 10 D) (wireMask D) (sourceA D) (sourceB D) G (start g) fork 0 s₀ := by
    refine ⟨s₀, hr, hh, hz, ?_, ?_, ?_⟩
    · simpa only [start, Nat.add_zero] using hp
    · apply Bool.eq_iff_iff.mpr
      rw [hf]
      simp only [decide_eq_true_eq, start, Nat.add_zero]
      constructor
      · exact fun h => decide_eq_true h
      · exact fun h => of_decide_eq_true h
    · intro k hk
      simp [hu] at hk
  exact program_target_excluded_certified (continuation_valid hS g) hcap hgroups
    (semantic_callback (wireMask_lt D) hsem) hinit
    (final_output_available hS hg fork) hout.1 hout.2

end OnceSimulation

namespace OnceActualLabels
open DAGBridge.DagTools OnceGeometry

def firstFour (g : Fin 4) : Fin 5 := ⟨g.val, by omega⟩

noncomputable def label (gate : Fin 5 → ℕ) (j : ℕ) : Option (Fin 4) :=
  if h : ∃ g : Fin 4, j = gate (firstFour g) then some (Classical.choose h) else none

lemma firstFour_injective : Function.Injective firstFour := by
  intro a b h
  apply Fin.ext
  exact congrArg (fun x : Fin 5 => x.val) h

lemma label_some_iff {gate : Fin 5 → ℕ} (hinj : Function.Injective gate)
    (j : ℕ) (g : Fin 4) : label gate j = some g ↔ j = gate (firstFour g) := by
  classical
  unfold label
  split_ifs with h
  · constructor
    · intro he
      have he' : Classical.choose h = g := Option.some.inj he
      exact he' ▸ Classical.choose_spec h
    · intro he
      have he' : firstFour (Classical.choose h) = firstFour g :=
        hinj ((Classical.choose_spec h).symm.trans he)
      rw [firstFour_injective he']
  · simp only [Option.noConfusion, false_iff]
    intro he
    exact h ⟨g, he⟩

lemma label_none_iff (gate : Fin 5 → ℕ) (j : ℕ) :
    label gate j = none ↔ ∀ g : Fin 4, j ≠ gate (firstFour g) := by
  classical
  unfold label
  split_ifs with h
  · simp only [Option.some_ne_none, false_iff, not_forall, Classical.not_not]
    exact h
  · simp only [true_iff]
    intro g he
    exact h ⟨g, he⟩

lemma label_unique {gate : Fin 5 → ℕ} (hinj : Function.Injective gate)
    {j k : ℕ} {g : Fin 4} (hj : label gate j = some g)
    (hk : label gate k = some g) : j = k :=
  ((label_some_iff hinj j g).mp hj).trans ((label_some_iff hinj k g).mp hk).symm

lemma gate_split (k : Fin 5) : k = 4 ∨ ∃ g : Fin 4, k = firstFour g := by
  by_cases hk : k.val = 4
  · exact Or.inl (Fin.ext hk)
  · refine Or.inr ⟨⟨k.val, by omega⟩, ?_⟩
    rfl

lemma label_semantics {D : Dag} (hS : Strict 10 D) {gate : Fin 5 → ℕ}
    (hinj : Function.Injective gate)
    (hvalid : ∀ k, gate k < D.length ∧ tag D (gate k) = true)
    (hports : ∀ g : Fin 4,
      (supp 10 D (opA D (gate (firstFour g))) = port g false ∧
       supp 10 D (opB D (gate (firstFour g))) = port g true) ∨
      (supp 10 D (opA D (gate (firstFour g))) = port g true ∧
       supp 10 D (opB D (gate (firstFour g))) = port g false))
    (htypes : ∀ j, j < D.length → tag D j = true →
      (∃ k : Fin 5, j = gate k) ∨
      (supp 10 D (opA D j) = ∅ ∧ supp 10 D (opB D j) = ∅))
    (j : ℕ) (hj : j < D.length) (hdirty : j ≠ gate 4) :
    if tag D j then
      supp 10 D (10+j) = ∅ ∧
      wireMask D (10+j) = wireMask D (opA D j) &&& wireMask D (opB D j) ∧
      (match label gate j with
      | none => supp 10 D (opA D j) = ∅ ∧ supp 10 D (opB D j) = ∅
      | some g =>
        (supp 10 D (opA D j) = port g false ∧ supp 10 D (opB D j) = port g true) ∨
        (supp 10 D (opA D j) = port g true ∧ supp 10 D (opB D j) = port g false))
    else label gate j = none ∧
      supp 10 D (10+j) = supp 10 D (opA D j) ∪ supp 10 D (opB D j) ∧
      wireMask D (10+j) = wireMask D (opA D j) ||| wireMask D (opB D j) := by
  classical
  have hm := wireMask_gate hS hj
  have hs := supp_gate hS j hj
  cases ht : tag D j with
  | false =>
    simp only [ht, Bool.false_eq_true, ↓reduceIte] at hm hs ⊢
    refine ⟨(label_none_iff gate j).mpr ?_, hs, hm⟩
    intro g he
    have hh := (hvalid (firstFour g)).2
    rw [← he, ht] at hh
    cases hh
  | true =>
    simp only [ht, ↓reduceIte] at hm hs ⊢
    cases hl : label gate j with
    | none =>
      have hz : supp 10 D (opA D j) = ∅ ∧ supp 10 D (opB D j) = ∅ := by
        rcases htypes j hj ht with ⟨k, hk⟩ | hz
        · rcases gate_split k with rfl | ⟨g, rfl⟩
          · exact False.elim (hdirty hk)
          · exact False.elim ((label_none_iff gate j).mp hl g hk)
        · exact hz
      refine ⟨?_, hm, hz⟩
      simpa only [hz.1, Finset.empty_inter] using hs
    | some g =>
      have he := (label_some_iff hinj j g).mp hl
      have hp := hports g
      rw [← he] at hp
      refine ⟨?_, hm, hp⟩
      have hd : port g false ∩ port g true = ∅ := by fin_cases g <;> decide
      rcases hp with ⟨ha,hb⟩ | ⟨ha,hb⟩
      · simpa only [ha,hb,hd] using hs
      · simpa only [ha,hb,Finset.inter_comm (port g true) (port g false),hd] using hs

end OnceActualLabels

namespace OnceActualLabels
open DAGBridge.DagTools OnceGeometry

lemma actual_other_sides {D : Dag} {gate : Fin 5 → ℕ}
    (hports : ∀ g : Fin 4,
      (supp 10 D (opA D (gate (firstFour g))) = port g false ∧
       supp 10 D (opB D (gate (firstFour g))) = port g true) ∨
      (supp 10 D (opA D (gate (firstFour g))) = port g true ∧
       supp 10 D (opB D (gate (firstFour g))) = port g false))
    (htypes : ∀ j, j < D.length → tag D j = true →
      (∃ k : Fin 5, j = gate k) ∨
      (supp 10 D (opA D j) = ∅ ∧ supp 10 D (opB D j) = ∅)) :
    FiveGroup.DAGBridge.OtherAndSides D (gate 4) := by
  intro j hj hne ht
  change (supp 10 D (opA D j), supp 10 D (opB D j)) ∈
      FiveGroup.CausalBarrier.OtherSides ∨
    (supp 10 D (opB D j), supp 10 D (opA D j)) ∈
      FiveGroup.CausalBarrier.OtherSides
  rcases htypes j hj ht with ⟨k,hk⟩ | ⟨ha,hb⟩
  · rcases gate_split k with rfl | ⟨g,rfl⟩
    · exact False.elim (hne hk)
    · have hp := hports g
      rw [← hk] at hp
      have hm : (port g false, port g true) ∈ FiveGroup.CausalBarrier.OtherSides := by
        fin_cases g <;> decide
      rcases hp with ⟨ha,hb⟩ | ⟨ha,hb⟩
      · exact Or.inl (by simpa only [ha,hb] using hm)
      · exact Or.inr (by simpa only [ha,hb] using hm)
  · left
    rw [ha,hb]
    decide

end OnceActualLabels

namespace OnceActualLabels
open DAGBridge.DagTools OnceGeometry OnceSimulation OnceActualSchedule

noncomputable def wireLabel (gate : Fin 5 → ℕ) (w : ℕ) : Option (Fin 4) := label gate (w - 10)

lemma actual_group_unique {gate : Fin 5 → ℕ} (hinj : Function.Injective gate) :
    GroupUnique (wireLabel gate) (start (gate 4)) (remaining D (gate 4)) := by
  intro i hi j hj g hgi hgj
  have he := label_unique hinj hgi hgj
  change start (gate 4) + i - 10 = start (gate 4) + j - 10 at he
  unfold start at he
  omega

lemma actual_program_semantics {D : Dag} (hS : Strict 10 D) {gate : Fin 5 → ℕ}
    (hinj : Function.Injective gate)
    (hvalid : ∀ k, gate k < D.length ∧ tag D (gate k) = true)
    (hports : ∀ g : Fin 4,
      (supp 10 D (opA D (gate (firstFour g))) = port g false ∧
       supp 10 D (opB D (gate (firstFour g))) = port g true) ∨
      (supp 10 D (opA D (gate (firstFour g))) = port g true ∧
       supp 10 D (opB D (gate (firstFour g))) = port g false))
    (htypes : ∀ j, j < D.length → tag D j = true →
      (∃ k : Fin 5, j = gate k) ∨
      (supp 10 D (opA D j) = ∅ ∧ supp 10 D (opB D j) = ∅)) :
    ProgramSemantics (supp 10 D) (wireMask D) (sourceA D) (sourceB D)
      (wireLabel gate) (fun w => tag D (w-10)) (start (gate 4)) (remaining D (gate 4)) := by
  intro t ht
  have hj : gate 4 + 1 + t < D.length := by unfold remaining at ht; omega
  have hn : gate 4 + 1 + t ≠ gate 4 := by omega
  have h := label_semantics hS hinj hvalid hports htypes (gate 4 + 1 + t) hj hn
  have he : start (gate 4) + t = 10 + (gate 4 + 1 + t) := by unfold start; omega
  simpa only [sourceA, sourceB, wireLabel, continuation_index, he, Nat.add_sub_cancel_left] using h

end OnceActualLabels

namespace OnceActualLabels
open DAGBridge.DagTools OnceGeometry OnceSimulation

end OnceActualLabels

namespace OnceActualLabels
open DAGBridge.DagTools OnceGeometry OnceSimulation

lemma five_gate_target_exclusion {D : Dag} (hS : Strict 10 D)
    (hB : Bzero 10 D ≤ 1) {gate : Fin 5 → ℕ}
    (hinj : Function.Injective gate)
    (hvalid : ∀ k, gate k < D.length ∧ tag D (gate k) = true)
    (hports : ∀ g : Fin 4,
      (supp 10 D (opA D (gate (firstFour g))) = port g false ∧
       supp 10 D (opB D (gate (firstFour g))) = port g true) ∨
      (supp 10 D (opA D (gate (firstFour g))) = port g true ∧
       supp 10 D (opB D (gate (firstFour g))) = port g false))
    (hdirty : FiveGroup.DAGBridge.DirtySides D (gate 4))
    (htypes : ∀ j, j < D.length → tag D j = true →
      (∃ k : Fin 5, j = gate k) ∨
      (supp 10 D (opA D j) = ∅ ∧ supp 10 D (opB D j) = ∅)) :
    ¬ (supp 10 D (10 + D.length - 1) = ∅ ∧ wireMask D (10 + D.length - 1) = 56) := by
  exact actual_target_exclusion hS hB (hvalid 4).1 (hvalid 4).2 hdirty
    (actual_other_sides hports htypes) (actual_group_unique hinj)
    (actual_program_semantics hS hinj hvalid hports htypes)

end OnceActualLabels


namespace SupportCount

lemma target_card_le_intermediate_card
    {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (F : Finset α) (H : Finset β)
    (target : α → Finset γ) (support : β → Finset γ)
    (hcard : H.card ≤ 2)
    (hnonempty : ∀ i ∈ F, (target i).Nonempty)
    (hdisjoint : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (target i) (target j))
    (hwitness : ∀ i ∈ F,
      (∃ h ∈ H, (support h).Nonempty ∧ support h ⊆ target i) ∨
      (∃ a ∈ H, ∃ b ∈ H, a ≠ b ∧ support a ∩ support b = target i)) :
    F.card ≤ H.card := by
  classical
  by_cases hand : ∃ i ∈ F, ∃ a ∈ H, ∃ b ∈ H,
      a ≠ b ∧ support a ∩ support b = target i
  · obtain ⟨i, hi, a, ha, b, hb, hab, hinter⟩ := hand
    have hpair : ({a, b} : Finset β) ⊆ H := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ha
      · exact (Finset.mem_singleton.mp hx) ▸ hb
    have hpaircard : ({a, b} : Finset β).card = 2 := by simp [hab]
    have hH : H = {a, b} :=
      (Finset.eq_of_subset_of_card_le hpair (by omega)).symm
    have hcontains : ∀ h ∈ H, target i ⊆ support h := by
      intro h hh x hx
      have hx' : x ∈ support a ∩ support b := by simpa [hinter] using hx
      rw [hH] at hh
      rcases Finset.mem_insert.mp hh with rfl | hh
      · exact (Finset.mem_inter.mp hx').1
      · rw [Finset.mem_singleton] at hh
        subst h
        exact (Finset.mem_inter.mp hx').2
    have hF : F ⊆ {i} := by
      intro j hj
      rw [Finset.mem_singleton]
      by_contra hji
      have hsubset : target i ⊆ target j := by
        rcases hwitness j hj with ⟨h, hh, _, hs⟩ | ⟨c, hc, d, hd, _, heq⟩
        · exact Finset.Subset.trans (hcontains h hh) hs
        · intro x hx
          rw [← heq]
          exact Finset.mem_inter.mpr ⟨hcontains c hc hx, hcontains d hd hx⟩
      obtain ⟨x, hx⟩ := hnonempty i hi
      exact Finset.disjoint_left.mp (hdisjoint i hi j hj (Ne.symm hji)) hx (hsubset hx)
    have hFcard : F.card ≤ 1 := by
      simpa using Finset.card_le_card hF
    rw [hH, hpaircard]
    omega
  · have hor : ∀ i : F, ∃ h : H,
        (support h).Nonempty ∧ support h ⊆ target i := by
      intro i
      rcases hwitness i i.property with ⟨h, hh, hne, hs⟩ | ⟨a, ha, b, hb, hab, heq⟩
      · exact ⟨⟨h, hh⟩, hne, hs⟩
      · exact False.elim (hand ⟨i, i.property, a, ha, b, hb, hab, heq⟩)
    choose f hf using hor
    apply Finset.card_le_card_of_injective (f := f)
    intro i j hij
    apply Subtype.ext
    by_contra hne
    obtain ⟨x, hx⟩ := (hf i).1
    have hxi : x ∈ target i := (hf i).2 hx
    have hxj : x ∈ target j := (hf j).2 (by simpa [hij] using hx)
    exact Finset.disjoint_left.mp
      (hdisjoint i i.property j j.property hne) hxi hxj

lemma six_le_counted_add_free
    {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (F : Finset α) (H : Finset β)
    (target : α → Finset γ) (support : β → Finset γ)
    (n k : Nat)
    (hbudget : H.card + 3 ≤ n)
    (hclasses : 3 ≤ F.card + k)
    (hnonempty : ∀ i ∈ F, (target i).Nonempty)
    (hdisjoint : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (target i) (target j))
    (hwitness : ∀ i ∈ F,
      (∃ h ∈ H, (support h).Nonempty ∧ support h ⊆ target i) ∨
      (∃ a ∈ H, ∃ b ∈ H, a ≠ b ∧ support a ∩ support b = target i)) :
    6 ≤ n + k := by
  by_contra hsmall
  have hcard : H.card ≤ 2 := by omega
  have hbound := target_card_le_intermediate_card F H target support hcard
    hnonempty hdisjoint hwitness
  omega

end SupportCount


namespace SupportBirth

lemma not_target_of_overlap {α : Type*} [DecidableEq α]
    {T : Finset (Finset α)} {P A : Finset α}
    (hdis : ∀ X ∈ T, ∀ Y ∈ T, X ≠ Y → Disjoint X Y)
    (hP : P ∈ T) (hAP : A ≠ P) (hinter : (A ∩ P).Nonempty) : A ∉ T := by
  intro hA
  obtain ⟨x, hx⟩ := hinter
  exact Finset.disjoint_left.mp (hdis A hA P hP hAP)
    (Finset.mem_inter.mp hx).1 (Finset.mem_inter.mp hx).2

lemma union_birth_support {α : Type*} [DecidableEq α]
    {T : Finset (Finset α)} {P A B : Finset α}
    (hdis : ∀ X ∈ T, ∀ Y ∈ T, X ≠ Y → Disjoint X Y)
    (hP : P ∈ T) (hAP : A ≠ P) (hBP : B ≠ P)
    (hunion : A ∪ B = P) : A ∉ T ∧ A.Nonempty ∧ A ⊆ P := by
  have hnonempty : A.Nonempty := by
    by_contra h
    have hz : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    exact hBP (by simpa only [hz, Finset.empty_union] using hunion)
  have hsub : A ⊆ P := by
    intro x hx
    rw [← hunion]
    exact Finset.mem_union_left B hx
  refine ⟨not_target_of_overlap hdis hP hAP ?_, hnonempty, hsub⟩
  obtain ⟨x, hx⟩ := hnonempty
  exact ⟨x, Finset.mem_inter.mpr ⟨hx, hsub hx⟩⟩

lemma inter_birth_support {α : Type*} [DecidableEq α]
    {T : Finset (Finset α)} {P A B : Finset α}
    (hdis : ∀ X ∈ T, ∀ Y ∈ T, X ≠ Y → Disjoint X Y)
    (hP : P ∈ T) (hPn : P.Nonempty) (hAP : A ≠ P) (hBP : B ≠ P)
    (hinter : A ∩ B = P) :
    A ∉ T ∧ B ∉ T ∧ A.Nonempty ∧ B.Nonempty ∧ A ≠ B := by
  obtain ⟨x, hx⟩ := hPn
  have hxab : x ∈ A ∩ B := by rw [hinter]; exact hx
  obtain ⟨hxa, hxb⟩ := Finset.mem_inter.mp hxab
  refine ⟨not_target_of_overlap hdis hP hAP ⟨x, Finset.mem_inter.mpr ⟨hxa, hx⟩⟩,
    not_target_of_overlap hdis hP hBP ⟨x, Finset.mem_inter.mpr ⟨hxb, hx⟩⟩,
    ⟨x, hxa⟩, ⟨x, hxb⟩, ?_⟩
  intro hAB
  exact hAP (by simpa only [← hAB, Finset.inter_self] using hinter)

lemma earlier_mem_nontarget {α : Type*} [DecidableEq α]
    (S : ℕ → Finset α) (T : Finset (Finset α)) (H : Finset ℕ)
    {j n i : ℕ} (hzero : S 0 = ∅) (hj : j ≤ n)
    (hH : ∀ h, 0 < h → h ≤ n → S h ∉ T → h ∈ H)
    (hi : i < j) (hni : (S i).Nonempty) (hti : S i ∉ T) : i ∈ H := by
  have hipos : 0 < i := by
    apply Nat.pos_of_ne_zero
    intro hiz
    subst i
    simp only [hzero, Finset.not_nonempty_empty] at hni
  exact hH i hipos (Nat.le_trans (Nat.le_of_lt hi) hj) hti

lemma birth_gate_witness {α : Type*} [DecidableEq α]
    (S : ℕ → Finset α) (T : Finset (Finset α)) (H : Finset ℕ)
    {j n : ℕ} {P : Finset α}
    (hzero : S 0 = ∅) (hj : j ≤ n)
    (hdis : ∀ X ∈ T, ∀ Y ∈ T, X ≠ Y → Disjoint X Y)
    (hP : P ∈ T) (hPn : P.Nonempty)
    (hfirst : ∀ i < j, S i ≠ P)
    (hH : ∀ h, 0 < h → h ≤ n → S h ∉ T → h ∈ H)
    (hgate :
      (∃ a < j, ∃ F : Finset α, S a ∪ F = P ∧ F ≠ P) ∨
      (∃ a < j, ∃ b < j, S a ∪ S b = P) ∨
      (∃ a < j, ∃ b < j, S a ∩ S b = P)) :
    (∃ h ∈ H, (S h).Nonempty ∧ S h ⊆ P) ∨
      (∃ a ∈ H, ∃ b ∈ H, a ≠ b ∧ S a ∩ S b = P) := by
  rcases hgate with ⟨a, ha, F, heq, hF⟩ | ⟨a, ha, b, hb, heq⟩ | ⟨a, ha, b, hb, heq⟩
  · obtain ⟨hnt, hne, hsub⟩ := union_birth_support hdis hP (hfirst a ha) hF heq
    exact Or.inl ⟨a, earlier_mem_nontarget S T H hzero hj hH ha hne hnt, hne, hsub⟩
  · obtain ⟨hnt, hne, hsub⟩ := union_birth_support hdis hP (hfirst a ha) (hfirst b hb) heq
    exact Or.inl ⟨a, earlier_mem_nontarget S T H hzero hj hH ha hne hnt, hne, hsub⟩
  · obtain ⟨hna, hnb, hanea, hbnea, hab⟩ :=
      inter_birth_support hdis hP hPn (hfirst a ha) (hfirst b hb) heq
    refine Or.inr ⟨a, earlier_mem_nontarget S T H hzero hj hH ha hanea hna,
      b, earlier_mem_nontarget S T H hzero hj hH hb hbnea hnb, ?_, heq⟩
    intro h
    exact hab (congrArg S h)

end SupportBirth

namespace SupportCount

lemma nontarget_card_add_target_card_le
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (G : Finset α) (T : Finset β) (S : α → β)
    (hoccurs : T ⊆ G.image S) :
    (G.filter (fun i => S i ∉ T)).card + T.card ≤ G.card := by
  have himage : T ⊆ (G.filter (fun i => S i ∈ T)).image S := by
    intro t ht
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp (hoccurs ht)
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, by simpa [heq] using ht⟩, heq⟩
  have hbound := (Finset.card_le_card himage).trans (Finset.card_image_le)
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := G) (fun i => S i ∈ T)
  omega

lemma sequence_six_le_gates_add_exact_free_targets
    {α : Type*} [DecidableEq α]
    (S : Nat → Finset α) (T Free : Finset (Finset α)) (n : Nat)
    (hzero : S 0 = ∅)
    (hthree : T.card = 3)
    (hnonempty : ∀ P ∈ T, P.Nonempty)
    (hdisjoint : ∀ P ∈ T, ∀ Q ∈ T, P ≠ Q → Disjoint P Q)
    (hoccurs : ∀ P ∈ T, ∃ j, 0 < j ∧ j ≤ n ∧ S j = P)
    (hgate : ∀ j, 0 < j → j ≤ n →
      (∃ a < j, ∃ F ∈ Free, S a ∪ F = S j) ∨
      (∃ a < j, ∃ b < j, S a ∪ S b = S j) ∨
      (∃ a < j, ∃ b < j, S a ∩ S b = S j)) :
    6 ≤ n + (T ∩ Free).card := by
  classical
  let G := (Finset.range (n + 1)).erase 0
  let H := G.filter (fun i => S i ∉ T)
  have hGmem : ∀ i, i ∈ G ↔ 0 < i ∧ i ≤ n := by
    intro i
    simp only [G, Finset.mem_erase, Finset.mem_range]
    omega
  have hGcard : G.card = n := by
    simp [G, Finset.card_erase_of_mem]
  have hTimage : T ⊆ G.image S := by
    intro P hP
    obtain ⟨j, hjpos, hjle, heq⟩ := hoccurs P hP
    exact Finset.mem_image.mpr ⟨j, (hGmem j).mpr ⟨hjpos, hjle⟩, heq⟩
  have hbudget : H.card + 3 ≤ n := by
    have hb := nontarget_card_add_target_card_le G T S hTimage
    simpa only [H, hthree, hGcard] using hb
  have hclasses : 3 ≤ (T \ Free).card + (T ∩ Free).card := by
    rw [Finset.card_sdiff_add_card_inter, hthree]
  apply six_le_counted_add_free (T \ Free) H id S n (T ∩ Free).card
    hbudget hclasses
  · intro P hP
    exact hnonempty P (Finset.mem_sdiff.mp hP).1
  · intro P hP Q hQ hne
    exact hdisjoint P (Finset.mem_sdiff.mp hP).1 Q (Finset.mem_sdiff.mp hQ).1 hne
  · intro P hP
    have hPT : P ∈ T := (Finset.mem_sdiff.mp hP).1
    have hPF : P ∉ Free := (Finset.mem_sdiff.mp hP).2
    obtain ⟨j₀, _, hj₀le, hj₀eq⟩ := hoccurs P hPT
    have hex : ∃ j, S j = P := ⟨j₀, hj₀eq⟩
    let j := Nat.find hex
    have hjeq : S j = P := Nat.find_spec hex
    have hjle : j ≤ n := (Nat.find_min' hex hj₀eq).trans hj₀le
    have hjpos : 0 < j := by
      apply Nat.pos_of_ne_zero
      intro hz
      have hPe : P = ∅ := by simpa [hz, hzero] using hjeq.symm
      simpa [hPe] using hnonempty P hPT
    apply SupportBirth.birth_gate_witness S T H hzero hjle hdisjoint hPT
      (hnonempty P hPT)
    · intro i hi
      exact Nat.find_min hex hi
    · intro i hipos hile hint
      exact Finset.mem_filter.mpr ⟨(hGmem i).mpr ⟨hipos, hile⟩, hint⟩
    · rcases hgate j hjpos hjle with
        ⟨a, ha, F, hF, heq⟩ | ⟨a, ha, b, hb, heq⟩ | ⟨a, ha, b, hb, heq⟩
      · left
        refine ⟨a, ha, F, heq.trans hjeq, ?_⟩
        intro hFP
        exact hPF (hFP ▸ hF)
      · exact Or.inr (Or.inl ⟨a, ha, b, hb, heq.trans hjeq⟩)
      · exact Or.inr (Or.inr ⟨a, ha, b, hb, heq.trans hjeq⟩)

end SupportCount

namespace S18Resource

abbrev State := Nat × List Nat × List Nat

def values (bits : Nat) : List Nat := (List.range 64).filter bits.testBit

def pairMasks (op : Nat → Nat → Nat) (a b : Nat) : Nat :=
  (values a).foldl (fun acc x =>
    (values b).foldl (fun acc y => acc ||| (1 <<< op x y)) acc) 0

def mergePools (a b : Nat) : Nat := pairMasks (· ||| ·) a b

def addCarrier (pool k : Nat) : Nat := pool ||| mergePools pool (1 <<< k)

def live (used loc : Nat) : Bool :=
  if loc = 0 then !used.testBit 0
  else if loc = 1 then !used.testBit 0 || !used.testBit 1 || !used.testBit 4
  else if loc = 2 then !used.testBit 0 || !used.testBit 1 || !used.testBit 2
  else if loc = 3 then !used.testBit 0 || !used.testBit 3
  else !used.testBit (loc - 3)

def prune (s : State) : State :=
  (s.1, (List.range 7).map (fun i =>
    if live s.1 i then s.2.1.getD i 1 else 1), s.2.2)

def sortedInsert (k : Nat) : List Nat → List Nat
  | [] => [k]
  | x :: xs => if k ≤ x then k :: x :: xs else x :: sortedInsert k xs

def zeroSort : List Nat → List Nat
  | [] => []
  | x :: xs => sortedInsert x (zeroSort xs)

def insertZero (k : Nat) (zs : List Nat) : List Nat := zeroSort (k :: zs)

def basis : Nat → Nat | 0 => 0 | 1 => 25 | 2 => 42 | _ => 52

def leftPool (ps : List Nat) (g : Nat) : Nat :=
  if g = 1 then mergePools (ps.getD 1 1) (ps.getD 2 1)
  else ps.getD g 1

def rightPool (ps : List Nat) (g : Nat) : Nat :=
  if g = 0 then mergePools (mergePools (ps.getD 1 1) (ps.getD 2 1)) (ps.getD 3 1)
  else mergePools (1 <<< basis g) (ps.getD (g + 3) 1)

def groupNext (s : State) : List State :=
  (List.range 4).flatMap fun g =>
    if s.1.testBit g then [] else
    (values (pairMasks (· &&& ·) (leftPool s.2.1 g) (rightPool s.2.1 g))).filterMap
      fun k => if k = 0 then none else
        some (prune (s.1 ||| (1 <<< g), s.2.1, insertZero k s.2.2))

def filterNext (s : State) : List State :=
  if s.1.testBit 4 then [] else
    s.2.2.flatMap fun k => (values (s.2.1.getD 1 1)).filterMap fun carrier =>
      let result := k &&& carrier
      if result = 0 then none else
        some (prune (s.1 ||| 16, s.2.1, insertZero result (s.2.2.erase k)))

def liftNext (s : State) : List State :=
  s.2.2.flatMap fun k => (List.range 7).filterMap fun loc =>
    if live s.1 loc then
      let old := s.2.1.getD loc 1
      let new := addCarrier old k
      if new = old then none else
        some (prune (s.1, s.2.1.set loc new, s.2.2.erase k))
    else none

def discardNext (s : State) : List State :=
  s.2.2.map fun k => prune (s.1, s.2.1, s.2.2.erase k)

def combineNext (s : State) : List State :=
  s.2.2.flatMap fun a => (s.2.2.erase a).flatMap fun b =>
    [a &&& b, a ||| b].filterMap fun k => if k = 0 then none else
      some (prune (s.1, s.2.1, insertZero k ((s.2.2.erase a).erase b)))

def successors (s : State) : List State :=
  groupNext s ++ filterNext s ++ liftNext s ++ discardNext s ++ combineNext s

-- Bit 5 records the distinguished dirty group, already used to create the seed.
def initial : State := (32, List.replicate 7 1, [63])

def listLess : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a = b then listLess as bs else decide (a < b)

def stateLess (a b : State) : Bool :=
  if a.1 ≠ b.1 then decide (a.1 < b.1)
  else if a.2.1 ≠ b.2.1 then listLess a.2.1 b.2.1
  else listLess a.2.2 b.2.2

def safe (s : State) : Bool := !s.2.2.contains 56

end S18Resource

namespace S18Resource

def packedPools : Nat := 121608561898064014147021414705752949099162774474703125027321757479661145081590905157238438155875226178729781485626217712387796141810405527523166399723919755669875797908573244849821282364567855833959848593836245638019415292524477920439951550711281725004076418959585141878413515860175275056672677413519376589383992567835339064435085607967545858727875135051145162031207038444923787131123499919472074251187488024884891917518167954129094530917391629580422705508468003500602659689747429277688643844431379471246932953981845989845214700034950490182798821365371183426763756526338260906051498883484141471701259610913553049978397854532224139612200677261129330271771344052060004369976404166936298384779408106831182368143618355514567970986203640434290633403671882020628834273717823363299713650525398476178101217244693670907318709748935377863682834739565494978060713548183654609291092243551095556274138459296387955732655907784576294208941070279160870907663720973568639327644807107448131599702528526113673560648531934314471583000332034836485430394715373569

def packedZeros : Nat := 30000203416136824821977595774444455736107963233630955626066618064519015329683750912

def poolLookup (i : Nat) : Nat :=
  (packedPools >>> (64 * i)) &&& 18446744073709551615

def zeroLookup (i : Nat) : List Nat :=
  let code := (packedZeros >>> (14 * i)) &&& 16383
  (List.range (code &&& 3)).map (fun j => (code >>> (2 + 6 * j)) &&& 63)

def decode (code : Nat) : State :=
  (code &&& 63,
    (List.range 7).map (fun i => poolLookup ((code >>> (6 + 6 * i)) &&& 63)),
    zeroLookup ((code >>> 48) &&& 31))

def block0 : Nat := 72710421370522604700857262819324816779856813473353856732079586568382450281712674712396593931461901206482341183683548350425786527324139229564269331718415276373674865417859382516942386776585494420777334887815928748498660478773337089571813678436063856344657511958346215281032979760171589375009941792153031005913315694676521958791435032113387704973171115622191683119035643119846652856386376972228442070110625303713327048659443616483747186305874721884516507690778859183480262837615568994822133519986564999967042410323044626561703107345483139804532203581191343966625164053431555237441761091812329300061793945382638740859471644828308280831777205054336216688878991159834912261261819446227568660051530830288811823339537248332304085731837531529642052208953909714354592103114922572046073010688994980690708156110055598402236676169917181957582795091088050430668137901933423177198034711807083526923473803694301923778866062140919139391381985255834670324082294006532075493224514741640128969475816992571979431055756042324615931040366624

def block1 : Nat := 5041255017920412444141958781371372284730392262881733827502792897583148475098456451672961770911609229809711761858645707380538104049612322254905668921775413463354641695654613024358324027234099790930996023181635171622600842997683150682993906769297643533552695868119820331177994671750062816831529084228964986893884744317483076385270691609336356949931071872578310562669415013599068422411688842070526377045533309614280117328021831842938865519774938158191476818395285014535385987580480493847679592877293635675415761275762112599796839231704149185210670738930464972791063288527259020706106308128148575107919496358014050702040498368639062719915255329790309213045258841073513348364654077534652752185420419005332579163610171347422629243529171354751588196288367643281813062824674920983549822161621683048528075417318063735140837912834402793910082840992734348320095176480187501613004827847597543733439028236587103077260163971810631035032195303738608148290024296662959376760139870079588819853572421438196843645106753250594353967274917926

def block2 : Nat := 6059200925060566922104548198305115823262754564906709270836336022757705130051126838432421155795448002357916379642549969038111214326190932056784874790339251820656227183140697535432643482420457010043541471919092148080283367179414128097434506914095814676861915562556321054058435290585224725635768502198972892890260324839138911481374388684210917302423118305766904320015697642230071645446500766098742461184679990778616401759835197904302113974923320517012707987068677331980092439824571870618972305446246669759776047896171535485782380559975442162670170477227528936176818030576667885523233025884981725817797627916773451600173024400380592024448017989676636818250850698348690245452414713741230921855381381524791763103673274000325445761380079971219772879227332331960664090674436920682905725704031498542809976040312593936467846350849044087355317195479149768922750381379610822132003660330228769325478639714257738982551376381621659329138978431202847381214453512090816155228533536461173865104291753264576664831657531405544161190609254

def block3 : Nat := 208852846818731719419178466731087647347482467303503507537958339196164278058406748120403751205961381556530491012565470998387506879458508535156275534020789756179480071015574640537869582394016262717380742500215423859244387191342363196416711677389177416498538496948995601149514983385903657156822135300786800426229193193314247504787669946606432198644216726890927270338313487005574892376988906803307461963767075243542573904089634369130300162098343715194006189364141148073540693132002207363367722066656785621298975102173756473340603248408336262997460290258690649185388447350023897632097462148204993830624676265548105024657782532726591740469279955045197799107458948473672300232213537872582829192818035128057451957797297801582655115865264324553066167673329580409651271404111224235179236756013289615017405819330623626820484540549576717126436289020892681752829500061747569914599705553028824432804229188215549242476982414700518582748489826905097122714094113737804137265556472158238772330279437850301919858214806677276995623

def block4 : Nat := 659833002239371150106987823948621190647475714383725084170674129072239322825364775064542655442497485832729787240120759602620842550773562845006975994932944582823358736350107675210436806812352263353451923368597961646177161972253580667908822998895814446729308094716915365186530069893233425743747190807728154954903039996109698379383587703094858920265015295543256028969515642448178340458203715040575391174744701484189831172533333275590337378908812144765569933032566197113893491079427669534268812864398418701679035508395566959737925375605207706309146466999887962374121977617871436077463621799339170461358112265349966110129156921507930010864645095241169200699895053032975467944435439833185331826498123139458623583970095015268790808352976821879701658711558309841507691974492492704622780269537275144173523384946195654639893667466865083861838377713960078377528933181424056976918468193916626054025487490392584089666428593928847390945135132363098708219057202903903018001527735059690867087463939195538538846300599207043443195948

def block5 : Nat := 815491632493278160268624924005160130146616766718088252279020270105227518581800356675065786861404227594016798927717630784034029404792047069801126291168281540632356491873148143337000478217838624228439477457519849615234357583194533552540910104340643454804963710624662093618436970389796618291329029025488273137370350763928937341123966310198465072044218223158496239933935807667040615282860963338471752626112809401957525895291108167806153727027415476095602026767730547011370174122530658227588366711784022411317861024197221796278011618744661419964698908998200874017817129724918952895126454574847904955157062863084921587919678942538467727178471854745610204890291467228900652775118979154839534019287149325502453941870015918022531259420904250132557374548878374856579835952890966627828982454270330419215235264265470612361136300638933460957796394276210505645479456984113486159176556928137411434024716301039507121352251449525912395515901835541939713070897085822644306181339531777513038359883523708377500902856035275987539984430

def block6 : Nat := 22637033715350634847786154035748017086759061741446935729060629603423743528902969931921037702610513846687179461666811697922050059654214867251415584626633568337408196806850779639000869740389185737395588275472738093693417074245936998439056140277674751726773536406960884292634825581589802225848409531168060780454976248922975458249355208128220353604980599541274969817934278842074552646065692873939046153553482091960017349914806862060765132111320738400036636119839429203255325918632065161865833017609301067200396692378986796773309724305244104295204870183732543514705571699236095225165872675737005728120902496952815798516781985691619901419923399391582958462496688523486238637301347959842750054966078289597381496916847819481131950560258663621026263884838804262040290458231527382089643744486608748836786332751136346714298549501907378003373692627511204822954726152084465870021905419689142114145803197750428525055658860481170443297901067931297602940626524430203186326816788875777041267630792581660940657918435267493494958

def block7 : Nat := 189465790404133074901223358270229708470998370908669637046138900161688632974238734646900732744934583836679720722482871483969440347912254532036959007990215903700294178892984777151361199889501761862396005930825289682031030473370354878319129725334586015269657068498676544730167305704335825070098971778117256843946554709700485489173408347983606674439345588730039513675505171345918485914776669141087118919968689956292771892571792684744345994046374120841167773050052198733278252727316843430309557756529525194207054272579917746927833107922009526097309750980733783215045398326923274995072828808808233456599724330223139207843473826009634269402280843856396843311902418300022658945242521648375020305914582067313034551211393037185951233719419103222019556238535538550259895894485161415148651539087231522173515432111014105800005486377846446309621009726318441169829075021457465533378419819096416338945139507956845018135543787602519775072533949560536872321701928678267808686309789821781151615916733513169608871129556660417773304827951

def block8 : Nat := 22716266189773038924939671770290981861277659233073410602810954277958271466949087020320198838772449461202940702802407839558842106130490

def blockLookup (k : Nat) : Nat := (if k < 4 then (if k < 2 then (if k < 1 then block0 else block1) else (if k < 3 then block2 else block3)) else (if k < 6 then (if k < 5 then block4 else block5) else (if k < 7 then block6 else (if k < 8 then block7 else block8))))

def getCode (i : Nat) : Nat :=
  (blockLookup (i / 64) >>> (53 * (i % 64))) &&& 9007199254740991

def getState (i : Nat) : State := decode (getCode i)

def contains (s : State) : Bool :=
  ResourceCertificate.searchIndex stateLess getState 521 s 11 0 521

def checked (i : Nat) : Bool := safe (getState i) && (successors (getState i)).all contains

def chunkCheck (k : Nat) : Bool :=
  (List.range 64).all (fun j => if k * 64 + j < 521 then checked (k * 64 + j) else true)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk0_closed : chunkCheck 0 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk1_closed : chunkCheck 1 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk2_closed : chunkCheck 2 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk3_closed : chunkCheck 3 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk4_closed : chunkCheck 4 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk5_closed : chunkCheck 5 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk6_closed : chunkCheck 6 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk7_closed : chunkCheck 7 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk8_closed : chunkCheck 8 = true := by decide +kernel

lemma all_chunks_checked : (List.range 9).all chunkCheck = true := by
  change ([0, 1, 2, 3, 4, 5, 6, 7, 8] : List Nat).all chunkCheck = true
  simp only [List.all_cons, List.all_nil, chunk0_closed, chunk1_closed, chunk2_closed, chunk3_closed, chunk4_closed, chunk5_closed, chunk6_closed, chunk7_closed, chunk8_closed, Bool.and_self]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma initial_contains : contains initial = true := by decide +kernel

lemma reachable_safe {finish : State}
    (hreach : Relation.ReflTransGen (fun a b => b ∈ successors a) initial finish) :
    safe finish = true := by
  apply ResourceCertificate.chunked_searchIndex_reachable_safe stateLess getState
    521 64 9 11 successors safe (by decide) (by decide) ?_ initial_contains hreach
  intro k hk
  change chunkCheck k = true
  exact List.all_eq_true.mp all_chunks_checked k (List.mem_range.mpr hk)

lemma reachable_no_target {finish : State}
    (hreach : Relation.ReflTransGen (fun a b => b ∈ successors a) initial finish) :
    56 ∉ finish.2.2 := by
  simpa [safe] using reachable_safe hreach

end S18Resource

namespace S18Prefix

open DAGBridge.DagTools OnceGeometry

def allowedPairs : List (Finset (Fin 10) × Finset (Fin 10)) :=
  [(∅, ∅), (∅, {1}), ({0}, {1, 4, 5}), ({1, 4}, {2, 6}),
    ({4}, {3, 9}), ({5}, {7, 8})]

def AndSides (S T : Finset (Fin 10)) : Prop :=
  (S, T) ∈ allowedPairs ∨ (T, S) ∈ allowedPairs

set_option maxRecDepth 4096 in
lemma allowed_geometry : ∀ p ∈ allowedPairs,
    p.1 ∩ p.2 = ∅ ∧ rawMask p.1 &&& rawMask p.2 = 0 := by
  intro p hp
  simp only [allowedPairs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

lemma and_geometry {S T : Finset (Fin 10)} (h : AndSides S T) :
    S ∩ T = ∅ ∧ rawMask S &&& rawMask T = 0 := by
  rcases h with h | h
  · exact allowed_geometry (S, T) h
  · simpa only [Finset.inter_comm, Nat.and_comm] using allowed_geometry (T, S) h

lemma input_raw (D : Dag) (i : Fin 10) :
    wireMask D i.val = rawMask (supp 10 D i.val) := by
  rw [supp_input]
  unfold wireMask rawMask
  apply congrArg mask
  funext r
  rw [val_input D (rowInput r) i.val i.isLt]
  simp only [rowInput, decide_eq_decide]
  constructor
  · intro h
    exact ⟨i, Finset.mem_inter.mpr ⟨Finset.mem_singleton_self i, h⟩⟩
  · rintro ⟨v, hv⟩
    obtain ⟨hv, hr⟩ := Finset.mem_inter.mp hv
    have he : v = i := Finset.mem_singleton.mp hv
    simpa only [he] using hr

lemma before_seed_raw {D : Dag} (hS : Strict 10 D) {g : ℕ} (hg : g ≤ D.length)
    (hbefore : ∀ j < g, tag D j = true →
      AndSides (supp 10 D (opA D j)) (supp 10 D (opB D j)))
    {w : ℕ} (hw : w < 10 + g) : wireMask D w = rawMask (supp 10 D w) := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < 10
    · exact input_raw D ⟨w, hn⟩
    · obtain ⟨j, rfl⟩ : ∃j, w = 10 + j := ⟨w - 10, by omega⟩
      have hjg : j < g := by omega
      have hj : j < D.length := by omega
      obtain ⟨ha, hb, _⟩ := hS j hj
      have hA := ih _ ha (by omega)
      have hB := ih _ hb (by omega)
      rw [wireMask_gate hS hj, supp_gate hS j hj, hA, hB]
      cases ht : tag D j with
      | false => simpa only [Bool.false_eq_true, ite_false] using
          (rawMask_union (supp 10 D (opA D j)) (supp 10 D (opB D j))).symm
      | true =>
        obtain ⟨hs, hm⟩ := and_geometry (hbefore j hjg ht)
        simp only [ite_true, hs, hm, rawMask_empty]

lemma before_seed_zero {D : Dag} (hS : Strict 10 D) {g : ℕ} (hg : g ≤ D.length)
    (hbefore : ∀ j < g, tag D j = true →
      AndSides (supp 10 D (opA D j)) (supp 10 D (opB D j)))
    {w : ℕ} (hw : w < 10 + g) (hz : supp 10 D w = ∅) : wireMask D w = 0 := by
  rw [before_seed_raw hS hg hbefore hw, hz, rawMask_empty]

lemma dirty_seed {D : Dag} (hS : Strict 10 D) {g : ℕ}
    (hg : g < D.length) (ht : tag D g = true)
    (hdirty : FiveGroup.DAGBridge.DirtySides D g) :
    supp 10 D (10 + g) = ∅ ∧ wireMask D (10 + g) = 63 := by
  exact ⟨(FiveGroup.DAGBridge.dirty_seed hS hg ht hdirty).1,
    dirty_wire_mask_unoriented hS hg ht hdirty⟩

end S18Prefix


namespace S18Budget

open DAGBridge.DagTools OnceResource.IndexCopies OnceActualSchedule

lemma zero_fanout_le_one {D : Dag} (hS : Strict 10 D) (hB : Bzero 10 D = 0)
    {w : ℕ} (hz : supp 10 D w = ∅) : fanout D w ≤ 1 := by
  by_cases hf : fanout D w ≤ 1
  · exact hf
  · have htwo : 2 ≤ fanout D w := by omega
    have hi := OnceResourceBudget.zero_branch_inner hS hz htwo
    have hm : w ∈ (inner 10 D).filter (fun w => ¬(supp 10 D w).Nonempty) := by
      exact hi
    have hs := Finset.single_le_sum (fun x _ => Nat.zero_le (fanout D x - 1)) hm
    change fanout D w - 1 ≤ Bzero 10 D at hs
    rw [hB] at hs
    omega

lemma continuation_capacity {D : Dag} (hS : Strict 10 D) (hB : Bzero 10 D = 0)
    (g : ℕ) : ∀ w, supp 10 D w = ∅ →
      ReadCount (start g) (sourceA D) (sourceB D) (remaining D g) w ≤ 1 := by
  intro w hw
  exact (continuation_readCount_le_fanout D g w).trans (zero_fanout_le_one hS hB hw)

end S18Budget


namespace S18Resource

lemma sortedInsert_perm (k : ℕ) (xs : List ℕ) :
    List.Perm (sortedInsert k xs) (k :: xs) := by
  induction xs with
  | nil => exact List.Perm.refl _
  | cons x xs ih =>
      simp only [sortedInsert]
      split
      · exact List.Perm.refl _
      · exact (List.Perm.cons x ih).trans (List.Perm.swap _ _ _)

lemma zeroSort_perm (xs : List ℕ) : List.Perm (zeroSort xs) xs := by
  induction xs with
  | nil => exact List.Perm.refl _
  | cons x xs ih =>
      exact (sortedInsert_perm x (zeroSort xs)).trans (List.Perm.cons x ih)

lemma insertZero_perm (k : ℕ) (xs : List ℕ) :
    List.Perm (insertZero k xs) (k :: xs) :=
  zeroSort_perm (k :: xs)

lemma mem_sortedInsert (a k : ℕ) (xs : List ℕ) :
    a ∈ sortedInsert k xs ↔ a = k ∨ a ∈ xs := by
  rw [(sortedInsert_perm k xs).mem_iff, List.mem_cons]

lemma mem_zeroSort (a : ℕ) (xs : List ℕ) :
    a ∈ zeroSort xs ↔ a ∈ xs :=
  (zeroSort_perm xs).mem_iff

lemma mem_insertZero (a k : ℕ) (xs : List ℕ) :
    a ∈ insertZero k xs ↔ a = k ∨ a ∈ xs := by
  rw [(insertZero_perm k xs).mem_iff, List.mem_cons]

lemma sortedInsert_length (k : ℕ) (xs : List ℕ) :
    (sortedInsert k xs).length = xs.length + 1 := by
  simpa only [List.length_cons] using (sortedInsert_perm k xs).length_eq

lemma zeroSort_length (xs : List ℕ) : (zeroSort xs).length = xs.length :=
  (zeroSort_perm xs).length_eq

lemma insertZero_length (k : ℕ) (xs : List ℕ) :
    (insertZero k xs).length = xs.length + 1 := by
  simpa only [List.length_cons] using (insertZero_perm k xs).length_eq

lemma prune_used (s : State) : (prune s).1 = s.1 := rfl

lemma prune_zeros (s : State) : (prune s).2.2 = s.2.2 := rfl

lemma prune_pool_getD (s : State) (i : ℕ) (hi : i < 7) :
    (prune s).2.1.getD i 1 = if live s.1 i then s.2.1.getD i 1 else 1 := by
  change ((List.range 7).map (fun j =>
    if live s.1 j then s.2.1.getD j 1 else 1)).getD i 1 = _
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hi, Option.map_some, Option.getD_some]

lemma prune_idempotent (s : State) : prune (prune s) = prune s := by
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  change (List.range 7).map (fun i =>
    if live s.1 i then (prune s).2.1.getD i 1 else 1) =
      (List.range 7).map (fun i => if live s.1 i then s.2.1.getD i 1 else 1)
  apply List.map_congr_left
  intro i hi
  rw [prune_pool_getD s i (List.mem_range.mp hi)]
  split <;> rfl

lemma prune_pools_congr (s t : State) (hused : s.1 = t.1)
    (hpools : s.2.1 = t.2.1) : (prune s).2.1 = (prune t).2.1 := by
  change (List.range 7).map (fun i => if live s.1 i then s.2.1.getD i 1 else 1) =
    (List.range 7).map (fun i => if live t.1 i then t.2.1.getD i 1 else 1)
  rw [hused, hpools]

lemma groupNext_mem_successors {s t : State} (h : t ∈ groupNext s) :
    t ∈ successors s := by
  simp only [successors, List.mem_append, h, true_or]

lemma liftNext_mem_successors {s t : State} (h : t ∈ liftNext s) :
    t ∈ successors s := by
  simp only [successors, List.mem_append, h, true_or, or_true]

lemma discardNext_mem_successors {s t : State} (h : t ∈ discardNext s) :
    t ∈ successors s := by
  simp only [successors, List.mem_append, h, true_or, or_true]

lemma combineNext_mem_successors {s t : State} (h : t ∈ combineNext s) :
    t ∈ successors s := by
  simp only [successors, List.mem_append, h, or_true]

lemma group_successor {s : State} {g k : ℕ}
    (hg : g < 4) (hunused : s.1.testBit g = false)
    (hk : k ∈ values (pairMasks (· &&& ·) (leftPool s.2.1 g) (rightPool s.2.1 g)))
    (hkn : k ≠ 0) :
    prune (s.1 ||| (1 <<< g), s.2.1, insertZero k s.2.2) ∈ successors s := by
  apply groupNext_mem_successors
  apply List.mem_flatMap.mpr
  refine ⟨g, List.mem_range.mpr hg, ?_⟩
  simp only [hunused, Bool.false_eq_true, ↓reduceIte]
  apply List.mem_filterMap.mpr
  exact ⟨k, hk, by simp [hkn]⟩

lemma lift_successor {s : State} {k loc : ℕ}
    (hk : k ∈ s.2.2) (hloc : loc < 7) (hlive : live s.1 loc = true)
    (hchange : addCarrier (s.2.1.getD loc 1) k ≠ s.2.1.getD loc 1) :
    prune (s.1, s.2.1.set loc (addCarrier (s.2.1.getD loc 1) k),
      s.2.2.erase k) ∈ successors s := by
  apply liftNext_mem_successors
  apply List.mem_flatMap.mpr
  refine ⟨k, hk, ?_⟩
  apply List.mem_filterMap.mpr
  exact ⟨loc, List.mem_range.mpr hloc, by simp only [hlive, hchange, ↓reduceIte]⟩

lemma discard_successor {s : State} {k : ℕ} (hk : k ∈ s.2.2) :
    prune (s.1, s.2.1, s.2.2.erase k) ∈ successors s := by
  apply discardNext_mem_successors
  exact List.mem_map.mpr ⟨k, hk, rfl⟩

lemma combine_successor {s : State} {a b k : ℕ}
    (ha : a ∈ s.2.2) (hb : b ∈ s.2.2.erase a)
    (hk : k = a &&& b ∨ k = a ||| b) (hkn : k ≠ 0) :
    prune (s.1, s.2.1, insertZero k ((s.2.2.erase a).erase b)) ∈ successors s := by
  apply combineNext_mem_successors
  apply List.mem_flatMap.mpr
  refine ⟨a, ha, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨b, hb, ?_⟩
  apply List.mem_filterMap.mpr
  refine ⟨k, ?_, by simp [hkn]⟩
  simpa only [List.mem_cons, List.not_mem_nil, or_false] using hk

lemma reachable_of_eq_or_successor {s t : State}
    (h : t = s ∨ t ∈ successors s) :
    Relation.ReflTransGen (fun a b : State => b ∈ successors a) s t := by
  rcases h with rfl | h
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single h

lemma filterNext_mem_successors {s t : State} (h : t ∈ filterNext s) :
    t ∈ successors s := by
  simp only [successors, List.mem_append, h, true_or, or_true]

lemma filter_successor {s : State} {k carrier : Nat}
    (hk : k ∈ s.2.2) (hunused : s.1.testBit 4 = false)
    (hc : carrier ∈ values (s.2.1.getD 1 1))
    (hresult : k &&& carrier ≠ 0) :
    prune (s.1 ||| 16, s.2.1, insertZero (k &&& carrier) (s.2.2.erase k)) ∈
      successors s := by
  apply filterNext_mem_successors
  simp only [filterNext, hunused, Bool.false_eq_true, ↓reduceIte]
  apply List.mem_flatMap.mpr
  refine ⟨k, hk, ?_⟩
  apply List.mem_filterMap.mpr
  exact ⟨carrier, hc, by simp [hresult]⟩

namespace ZeroTransitions

def token (k : ℕ) : Multiset ℕ := if k = 0 then 0 else {k}

lemma mem_of_zero_eq {zs : List ℕ} {a : ℕ} {rest : Multiset ℕ}
    (hz : (zs : Multiset ℕ) = {a} + rest) : a ∈ zs := by
  change a ∈ (zs : Multiset ℕ)
  rw [hz]
  simp

lemma erase_of_zero_eq {zs : List ℕ} {a : ℕ} {rest : Multiset ℕ}
    (hz : (zs : Multiset ℕ) = {a} + rest) :
    (zs.erase a : Multiset ℕ) = rest := by
  change (zs : Multiset ℕ).erase a = rest
  rw [hz]
  simp

lemma coe_insertZero (k : ℕ) (zs : List ℕ) :
    (insertZero k zs : Multiset ℕ) = {k} + (zs : Multiset ℕ) := by
  change (insertZero k zs : Multiset ℕ) = ((k :: zs : List ℕ) : Multiset ℕ)
  exact Quot.sound (insertZero_perm k zs)

lemma discard_one {s : State} {a : ℕ} {rest : Multiset ℕ}
    (hz : (s.2.2 : Multiset ℕ) = {a} + rest) :
    ∃ t : State,
      Relation.ReflTransGen (fun p q : State => q ∈ successors p) s t ∧
      (t.2.2 : Multiset ℕ) = rest ∧ t.1 = s.1 ∧
      t.2.1 = (prune s).2.1 := by
  refine ⟨prune (s.1, s.2.1, s.2.2.erase a),
    Relation.ReflTransGen.single (discard_successor (mem_of_zero_eq hz)),
    erase_of_zero_eq hz, rfl, rfl⟩

lemma discard_two {s : State} {a b : ℕ} {rest : Multiset ℕ}
    (hz : (s.2.2 : Multiset ℕ) = {a} + {b} + rest) :
    ∃ t : State,
      Relation.ReflTransGen (fun p q : State => q ∈ successors p) s t ∧
      (t.2.2 : Multiset ℕ) = rest ∧ t.1 = s.1 ∧
      t.2.1 = (prune s).2.1 := by
  have hz' : (s.2.2 : Multiset ℕ) = {a} + ({b} + rest) := by
    simpa only [Multiset.add_assoc] using hz
  have ha := mem_of_zero_eq hz'
  have hz1 := erase_of_zero_eq hz'
  have hb := mem_of_zero_eq hz1
  have hz2 := erase_of_zero_eq hz1
  let t1 : State := prune (s.1, s.2.1, s.2.2.erase a)
  let t2 : State := prune (s.1, s.2.1, (s.2.2.erase a).erase b)
  have h1 : t1 ∈ successors s := discard_successor ha
  have h2 : t2 ∈ successors t1 := by
    have hh := discard_successor (s := t1) (k := b) hb
    change prune (prune (s.1, s.2.1, (s.2.2.erase a).erase b)) ∈
      successors t1 at hh
    rw [prune_idempotent] at hh
    exact hh
  exact ⟨t2, (Relation.ReflTransGen.single h1).trans (Relation.ReflTransGen.single h2),
    hz2, rfl, rfl⟩

lemma combine_nonzero {s : State} {a b k : ℕ} {rest : Multiset ℕ}
    (hz : (s.2.2 : Multiset ℕ) = {a} + {b} + rest)
    (hop : k = a &&& b ∨ k = a ||| b) (hk : k ≠ 0) :
    ∃ t : State,
      Relation.ReflTransGen (fun p q : State => q ∈ successors p) s t ∧
      (t.2.2 : Multiset ℕ) = {k} + rest ∧ t.1 = s.1 ∧
      t.2.1 = (prune s).2.1 := by
  have hz' : (s.2.2 : Multiset ℕ) = {a} + ({b} + rest) := by
    simpa only [Multiset.add_assoc] using hz
  have ha := mem_of_zero_eq hz'
  have hz1 := erase_of_zero_eq hz'
  have hb := mem_of_zero_eq hz1
  have hz2 := erase_of_zero_eq hz1
  refine ⟨prune (s.1, s.2.1, insertZero k ((s.2.2.erase a).erase b)),
    Relation.ReflTransGen.single (combine_successor ha hb hop hk), ?_, rfl, rfl⟩
  change (insertZero k ((s.2.2.erase a).erase b) : Multiset ℕ) = {k} + rest
  rw [coe_insertZero, hz2]

lemma zero_binary {s : State} (a b : ℕ) (isAnd : Bool) (rest : Multiset ℕ)
    (hz : (s.2.2 : Multiset ℕ) = token a + token b + rest) :
    ∃ t : State,
      Relation.ReflTransGen (fun p q : State => q ∈ successors p) s t ∧
      (t.2.2 : Multiset ℕ) = token (if isAnd then a &&& b else a ||| b) + rest ∧
      t.1 = s.1 ∧
      (t.2.1 = s.2.1 ∨ t.2.1 = (prune s).2.1) := by
  by_cases ha : a = 0
  · subst a
    cases isAnd
    · refine ⟨s, Relation.ReflTransGen.refl, ?_, rfl, Or.inl rfl⟩
      simpa [token] using hz
    · by_cases hb : b = 0
      · subst b
        refine ⟨s, Relation.ReflTransGen.refl, ?_, rfl, Or.inl rfl⟩
        simpa [token] using hz
      · have hz' : (s.2.2 : Multiset ℕ) = {b} + rest := by simpa [token, hb] using hz
        obtain ⟨t, hr, ht, hu, hp⟩ := discard_one hz'
        exact ⟨t, hr, by simpa [token] using ht, hu, Or.inr hp⟩
  · by_cases hb : b = 0
    · subst b
      cases isAnd
      · refine ⟨s, Relation.ReflTransGen.refl, ?_, rfl, Or.inl rfl⟩
        simpa [token] using hz
      · have hz' : (s.2.2 : Multiset ℕ) = {a} + rest := by simpa [token, ha] using hz
        obtain ⟨t, hr, ht, hu, hp⟩ := discard_one hz'
        exact ⟨t, hr, by simpa [token] using ht, hu, Or.inr hp⟩
    · have hz' : (s.2.2 : Multiset ℕ) = {a} + {b} + rest := by
        simpa [token, ha, hb] using hz
      let k := if isAnd then a &&& b else a ||| b
      by_cases hk : k = 0
      · obtain ⟨t, hr, ht, hu, hp⟩ := discard_two hz'
        refine ⟨t, hr, ?_, hu, Or.inr hp⟩
        change (t.2.2 : Multiset ℕ) = token k + rest
        rw [hk]
        simpa [token] using ht
      · have hop : k = a &&& b ∨ k = a ||| b := by cases isAnd <;> simp [k]
        obtain ⟨t, hr, ht, hu, hp⟩ := combine_nonzero hz' hop hk
        refine ⟨t, hr, ?_, hu, Or.inr hp⟩
        change (t.2.2 : Multiset ℕ) = token k + rest
        simpa [token, hk] using ht

end ZeroTransitions

namespace ZeroTransitions

lemma zero_filter {s : State} (k carrier : Nat) (rest : Multiset Nat)
    (hz : (s.2.2 : Multiset Nat) = token k + rest)
    (hunused : s.1.testBit 4 = false)
    (hc : carrier ∈ values (s.2.1.getD 1 1)) :
    ∃ t : State,
      Relation.ReflTransGen (fun p q : State => q ∈ successors p) s t ∧
      (t.2.2 : Multiset Nat) = token (k &&& carrier) + rest ∧
      t.1 = (if k &&& carrier = 0 then s.1 else s.1 ||| 16) ∧
      (t.2.1 = s.2.1 ∨ t.2.1 = (prune (t.1, s.2.1, [])).2.1) := by
  by_cases hk : k = 0
  · subst k
    refine ⟨s, Relation.ReflTransGen.refl, ?_, ?_, Or.inl rfl⟩
    · simpa only [Nat.zero_and] using hz
    · simp
  · have hz' : (s.2.2 : Multiset Nat) = {k} + rest := by
      simpa [token, hk] using hz
    by_cases hresult : k &&& carrier = 0
    · obtain ⟨t, hreach, ht, hu, hp⟩ := discard_one hz'
      refine ⟨t, hreach, ?_, ?_, Or.inr ?_⟩
      · simpa [token, hresult] using ht
      · simpa [hresult] using hu
      · rw [hp, hu]
        rfl
    · refine ⟨prune (s.1 ||| 16, s.2.1, insertZero (k &&& carrier) (s.2.2.erase k)),
        Relation.ReflTransGen.single (filter_successor (mem_of_zero_eq hz') hunused hc hresult),
        ?_, ?_, Or.inr rfl⟩
      · change (insertZero (k &&& carrier) (s.2.2.erase k) : Multiset Nat) =
          token (k &&& carrier) + rest
        rw [coe_insertZero, erase_of_zero_eq hz']
        simp [token, hresult]
      · simp only [prune, hresult, ↓reduceIte]

end ZeroTransitions

end S18Resource


namespace S18Geometry

open OnceGeometry

def port (g : Fin 5) (right : Bool) : Finset (Fin 10) :=
  if right then match g.val with
    | 0 => {1, 4, 5}
    | 1 => {2, 6}
    | 2 => {3, 9}
    | 3 => {7, 8}
    | _ => {1}
  else match g.val with
    | 0 => {0}
    | 1 => {1, 4}
    | 2 => {4}
    | 3 => {5}
    | _ => ∅

def locations (g : Fin 5) (right : Bool) : Finset (Fin 7) :=
  if right then match g.val with
    | 0 => {1, 2, 3}
    | 1 => {4}
    | 2 => {5}
    | 3 => {6}
    | _ => {1}
  else match g.val with
    | 0 => {0}
    | 1 => {1, 2}
    | 2 => {2}
    | 3 => {3}
    | _ => ∅

def consumers (loc : Fin 7) : Finset (Fin 5) :=
  match loc.val with
  | 0 => {0}
  | 1 => {0, 1, 4}
  | 2 => {0, 1, 2}
  | 3 => {0, 3}
  | 4 => {1}
  | 5 => {2}
  | _ => {3}

lemma port_class : ∀ (g : Fin 5) (b : Bool) (v : Fin 10),
    v ∈ port g b ↔ vertexClass v ∈ locations g b := by decide

lemma support_class {S : Finset (Fin 10)} {g : Fin 5} {b : Bool}
    (hS : S ⊆ port g b) {v : Fin 10} (hv : v ∈ S) :
    vertexClass v ∈ locations g b := (port_class g b v).mp (hS hv)

lemma consumer_iff : ∀ (g : Fin 5) (loc : Fin 7),
    g ∈ consumers loc ↔ ∃ b : Bool, loc ∈ locations g b := by decide

lemma port_locations_live {used : ℕ} {g : Fin 5}
    (hg : used.testBit g.val = false) (b : Bool) {loc : Fin 7}
    (hl : loc ∈ locations g b) : S18Resource.live used loc.val = true := by
  fin_cases g <;> cases b <;> fin_cases loc <;>
    simp_all [locations, S18Resource.live]

lemma live_mark_dirty (used : ℕ) (loc : Fin 7) :
    S18Resource.live (used ||| 32) loc.val = S18Resource.live used loc.val := by
  have h1 : Nat.testBit 32 1 = false := by decide
  have h2 : Nat.testBit 32 2 = false := by decide
  have h3 : Nat.testBit 32 3 = false := by decide
  have h4 : Nat.testBit 32 4 = false := by decide
  fin_cases loc <;> simp [S18Resource.live, Nat.testBit_or, h1, h2, h3, h4]

lemma initial_locations_live : ∀ loc : Fin 7, S18Resource.live 32 loc.val = true := by decide

lemma rawMask_port : ∀ (g : Fin 5) (b : Bool),
    rawMask (port g b) = if b then if g.val < 4 then S18Resource.basis g.val else 0 else 0 := by
  decide

end S18Geometry

namespace S18Resource

lemma prune_getD_of_live {s : State} {loc : ℕ}
    (hloc : loc < 7) (hlive : live s.1 loc = true) :
    (prune s).2.1.getD loc 1 = s.2.1.getD loc 1 := by
  simp [prune, List.getD_eq_getElem?_getD, List.getElem?_range hloc, hlive]

lemma prune_pools_length (s : State) : (prune s).2.1.length = 7 := by simp [prune]

lemma prune_port_getD {s : State} {g : Fin 5} {b : Bool} {loc : Fin 7}
    (hg : s.1.testBit g.val = false) (hl : loc ∈ S18Geometry.locations g b) :
    (prune s).2.1.getD loc.val 1 = s.2.1.getD loc.val 1 :=
  prune_getD_of_live loc.isLt (S18Geometry.port_locations_live hg b hl)

lemma prune_leftPool {s : State} {g : Fin 4} (hg : s.1.testBit g.val = false) :
    leftPool (prune s).2.1 g.val = leftPool s.2.1 g.val := by
  fin_cases g
  · exact prune_port_getD (g := 0) (b := false) (loc := 0) hg (by decide)
  · exact congrArg₂ mergePools
      (prune_port_getD (g := 1) (b := false) (loc := 1) hg (by decide))
      (prune_port_getD (g := 1) (b := false) (loc := 2) hg (by decide))
  · exact prune_port_getD (g := 2) (b := false) (loc := 2) hg (by decide)
  · exact prune_port_getD (g := 3) (b := false) (loc := 3) hg (by decide)

lemma prune_rightPool {s : State} {g : Fin 4} (hg : s.1.testBit g.val = false) :
    rightPool (prune s).2.1 g.val = rightPool s.2.1 g.val := by
  fin_cases g
  · exact congrArg₂ mergePools
      (congrArg₂ mergePools
        (prune_port_getD (g := 0) (b := true) (loc := 1) hg (by decide))
        (prune_port_getD (g := 0) (b := true) (loc := 2) hg (by decide)))
      (prune_port_getD (g := 0) (b := true) (loc := 3) hg (by decide))
  · exact congrArg (mergePools (1 <<< 25))
      (prune_port_getD (g := 1) (b := true) (loc := 4) hg (by decide))
  · exact congrArg (mergePools (1 <<< 42))
      (prune_port_getD (g := 2) (b := true) (loc := 5) hg (by decide))
  · exact congrArg (mergePools (1 <<< 52))
      (prune_port_getD (g := 3) (b := true) (loc := 6) hg (by decide))

lemma prune_filterPool {s : State} (hg : s.1.testBit 4 = false) :
    (prune s).2.1.getD 1 1 = s.2.1.getD 1 1 :=
  prune_port_getD (g := 4) (b := true) (loc := 1) hg (by decide)

lemma prune_group_pairMasks {s : State} {g : Fin 4} (hg : s.1.testBit g.val = false) :
    pairMasks (· &&& ·) (leftPool (prune s).2.1 g.val) (rightPool (prune s).2.1 g.val) =
      pairMasks (· &&& ·) (leftPool s.2.1 g.val) (rightPool s.2.1 g.val) := by
  rw [prune_leftPool hg, prune_rightPool hg]

end S18Resource


namespace S18Positive

open S18Resource OnceGeometry

abbrev Pools := OncePositive.Pools
abbrev or7 := OncePositive.or7
abbrev PoolsGood := OncePositive.PoolsGood
abbrev Witness := OncePositive.Witness
abbrev liftPool := OncePositive.liftPool
abbrev poolView := OncePositive.poolView

lemma or7_or (f h : Fin 7 → ℕ) : or7 (fun i => f i ||| h i) = or7 f ||| or7 h :=
  OncePositive.or7_or f h

lemma or7_update (f : Fin 7 → ℕ) (loc : Fin 7) (k : ℕ) :
    or7 (Function.update f loc (f loc ||| k)) = or7 f ||| k :=
  OncePositive.or7_update f loc k

lemma or7_filtered {L : Finset (Fin 7)} {f : Fin 7 → ℕ}
    (hf : ∀ i, i ∉ L → f i = 0) :
    or7 f = or7 (fun i => if i ∈ L then f i else 0) :=
  OncePositive.or7_filtered hf

def Rep (used : ℕ) (P : Pools) (S : Finset (Fin 10)) (m : ℕ) : Prop :=
  ∀ (g : Fin 5) (b : Bool), used.testBit g.val = false → S ⊆ S18Geometry.port g b →
    ∃ f, Witness P (S18Geometry.locations g b) f ∧ m = rawMask S ||| or7 f

lemma rep_raw {used : ℕ} {P : Pools} (hp : PoolsGood P) (S : Finset (Fin 10)) :
    Rep used P S (rawMask S) := by
  intro g b _ _
  refine ⟨fun _ => 0, ?_, ?_⟩
  · exact fun i => ⟨(hp i).1, fun _ => rfl⟩
  · simp [or7, OncePositive.or7]

lemma rep_or {used : ℕ} {P : Pools} (hp : PoolsGood P)
    {S T : Finset (Fin 10)} {a b : ℕ} (ha : Rep used P S a) (hb : Rep used P T b) :
    Rep used P (S ∪ T) (a ||| b) := by
  intro g side hu hST
  have hS : S ⊆ S18Geometry.port g side := fun v hv => hST (Finset.mem_union_left _ hv)
  have hT : T ⊆ S18Geometry.port g side := fun v hv => hST (Finset.mem_union_right _ hv)
  obtain ⟨f, hf, ha⟩ := ha g side hu hS
  obtain ⟨h, hh, hb⟩ := hb g side hu hT
  refine ⟨fun i => f i ||| h i, ?_, ?_⟩
  · intro i
    refine ⟨(hp i).2 _ (hf i).1 _ (hh i).1, ?_⟩
    intro hi
    change f i ||| h i = 0
    rw [(hf i).2 hi, (hh i).2 hi]
    rfl
  · rw [ha, hb, rawMask_union, or7_or]
    ac_rfl

lemma rep_mono {used : ℕ} {P Q : Pools} {S : Finset (Fin 10)} {m : ℕ}
    (hPQ : ∀ i x, x ∈ values (P i) → x ∈ values (Q i))
    (h : Rep used P S m) : Rep used Q S m := by
  intro g b hg hS
  obtain ⟨f, hf, hm⟩ := h g b hg hS
  exact ⟨f, fun i => ⟨hPQ i _ (hf i).1, (hf i).2⟩, hm⟩

lemma liftPool_mono (P : Pools) (loc : Fin 7) (k : ℕ) :
    ∀ i x, x ∈ values (P i) → x ∈ values (liftPool P loc k i) :=
  OncePositive.liftPool_mono P loc k

lemma poolsGood_lift {P : Pools} (hp : PoolsGood P) (loc : Fin 7) {k : ℕ} (hk : k < 64) :
    PoolsGood (liftPool P loc k) := OncePositive.poolsGood_lift hp loc hk

lemma rep_lift {used : ℕ} {P : Pools} {S : Finset (Fin 10)} {m k : ℕ}
    (h : Rep used P S m) (hk : k < 64) {v : Fin 10} (hv : v ∈ S) :
    Rep used (liftPool P (vertexClass v) k) S (m ||| k) := by
  intro g b hg hS
  have hvL := S18Geometry.support_class hS hv
  obtain ⟨f, hf, hm⟩ := h g b hg hS
  refine ⟨Function.update f (vertexClass v) (f (vertexClass v) ||| k), ?_, ?_⟩
  · intro i
    by_cases hi : i = vertexClass v
    · subst i
      constructor
      · simpa [liftPool, OncePositive.liftPool] using OnceResource.mem_addCarrier_or (hf (vertexClass v)).1 hk
      · intro hnot
        exact False.elim (hnot hvL)
    · simpa [liftPool, OncePositive.liftPool, Function.update_apply, hi] using hf i
  · rw [or7_update, hm]
    ac_rfl

lemma rep_restrict_pools {old new : ℕ} {P Q : Pools} {S : Finset (Fin 10)} {m : ℕ}
    (hgroups : ∀ g : Fin 5, new.testBit g.val = false → old.testBit g.val = false)
    (hzero : ∀ i, 0 ∈ values (Q i))
    (hpools : ∀ (g : Fin 5) (b : Bool), new.testBit g.val = false →
      ∀ i ∈ S18Geometry.locations g b, Q i = P i)
    (h : Rep old P S m) : Rep new Q S m := by
  intro g b hg hS
  obtain ⟨f, hf, hm⟩ := h g b (hgroups g hg) hS
  refine ⟨f, ?_, hm⟩
  intro i
  refine ⟨?_, (hf i).2⟩
  by_cases hi : i ∈ S18Geometry.locations g b
  · rw [hpools g b hg i hi]
    exact (hf i).1
  · rw [(hf i).2 hi]
    exact hzero i

lemma poolView_prune (s : State) (i : Fin 7) :
    poolView (prune s).2.1 i = if live s.1 i.val then poolView s.2.1 i else 1 := by
  simp [poolView, OncePositive.poolView, prune, List.getD_eq_getElem?_getD]

lemma mem_values_one_iff {x : ℕ} : x ∈ values 1 ↔ x = 0 := by
  rw [show (x ∈ values 1) ↔ x < 64 ∧ (1 : ℕ).testBit x = true from OnceResource.mem_values_iff,
    Nat.testBit_one_eq_true_iff_self_eq_zero]
  constructor
  · exact And.right
  · intro h; subst x; exact ⟨by decide, rfl⟩

lemma one_pool_good :
    0 ∈ values 1 ∧ ∀ a ∈ values 1, ∀ b ∈ values 1, a ||| b ∈ values 1 := by
  constructor
  · exact mem_values_one_iff.mpr rfl
  · intro a ha b hb
    obtain rfl := mem_values_one_iff.mp ha
    obtain rfl := mem_values_one_iff.mp hb
    exact mem_values_one_iff.mpr rfl

lemma poolsGood_prune {s : State} (hp : PoolsGood (poolView s.2.1)) :
    PoolsGood (poolView (prune s).2.1) := by
  intro i
  rw [poolView_prune]
  split
  · exact hp i
  · exact one_pool_good

lemma rep_prune {s : State} {S : Finset (Fin 10)} {m : ℕ}
    (hp : PoolsGood (poolView s.2.1)) (h : Rep s.1 (poolView s.2.1) S m) :
    Rep (prune s).1 (poolView (prune s).2.1) S m := by
  apply rep_restrict_pools (fun _ hg => hg) (fun i => (poolsGood_prune hp i).1) ?_ h
  intro g b hg i hi
  rw [poolView_prune, S18Geometry.port_locations_live hg b hi]
  rfl

lemma unused_of_or_unused {used extra i : ℕ}
    (h : (used ||| extra).testBit i = false) : used.testBit i = false := by
  rw [Nat.testBit_or] at h
  exact (Bool.or_eq_false_iff.mp h).1

lemma mark_used_lt {used : ℕ} (hu : used < 64) (g : Fin 5) :
    used ||| (1 <<< g.val) < 64 := by
  have hg : (1 <<< g.val : ℕ) < 64 := by fin_cases g <;> decide
  exact Nat.or_lt_two_pow (n := 6) hu hg

lemma rep_mark {used : ℕ} {P : Pools} {S : Finset (Fin 10)} {m : ℕ}
    (h : Rep used P S m) (g : Fin 5) : Rep (used ||| (1 <<< g.val)) P S m := by
  intro g' b hg hS
  exact h g' b (unused_of_or_unused hg) hS

lemma rep_mark_prune {used : ℕ} {ps : List ℕ} {S : Finset (Fin 10)} {m : ℕ}
    (hp : PoolsGood (poolView ps)) (h : Rep used (poolView ps) S m)
    (g : Fin 5) (zs : List ℕ) :
    Rep (used ||| (1 <<< g.val))
      (poolView (prune (used ||| (1 <<< g.val), ps, zs)).2.1) S m := by
  exact rep_prune (s := (used ||| (1 <<< g.val), ps, zs)) hp (rep_mark h g)

lemma poolView_set {ps : List ℕ} (hlen : ps.length = 7) (loc : Fin 7) (k : ℕ) :
    poolView (ps.set loc.val (addCarrier (ps.getD loc.val 1) k)) =
      liftPool (poolView ps) loc k := by
  funext i
  by_cases hi : i = loc
  · subst i
    have hb : loc.val < ps.length := by simpa only [hlen] using loc.isLt
    simp [poolView, OncePositive.poolView, liftPool, OncePositive.liftPool,
      List.getD_eq_getElem?_getD, List.getElem?_set_self hb]
    rfl
  · have hne : loc.val ≠ i.val := fun h => hi (Fin.ext h.symm)
    simp [poolView, OncePositive.poolView, liftPool, OncePositive.liftPool, hi,
      List.getD_eq_getElem?_getD, List.getElem?_set_ne hne]

lemma poolsGood_set {ps : List ℕ} (hlen : ps.length = 7)
    (hp : PoolsGood (poolView ps)) (loc : Fin 7) {k : ℕ} (hk : k < 64) :
    PoolsGood (poolView (ps.set loc.val (addCarrier (ps.getD loc.val 1) k))) := by
  rw [poolView_set hlen]
  exact poolsGood_lift hp loc hk

lemma poolView_replicate_one : poolView (List.replicate 7 1) = fun _ => 1 := by
  funext i
  fin_cases i <;> rfl

lemma poolsGood_replicate_one : PoolsGood (poolView (List.replicate 7 1)) := by
  rw [poolView_replicate_one]
  exact fun _ => one_pool_good

def leftChoices (P : Pools) (g : Fin 5) : ℕ :=
  match g.val with
  | 0 => P 0
  | 1 => mergePools (P 1) (P 2)
  | 2 => P 2
  | 3 => P 3
  | _ => 1

def rightChoices (P : Pools) (g : Fin 5) : ℕ :=
  match g.val with
  | 0 => mergePools (mergePools (P 1) (P 2)) (P 3)
  | 1 => mergePools (1 <<< 25) (P 4)
  | 2 => mergePools (1 <<< 42) (P 5)
  | 3 => mergePools (1 <<< 52) (P 6)
  | _ => P 1

def portChoices (P : Pools) (g : Fin 5) (b : Bool) : ℕ :=
  if b then rightChoices P g else leftChoices P g

lemma portChoices_view (ps : List ℕ) (g : Fin 4) (b : Bool) :
    portChoices (poolView ps) ⟨g.val, by omega⟩ b =
      if b then rightPool ps g.val else leftPool ps g.val := by
  fin_cases g <;> cases b <;> rfl

lemma merge_mem {p q a b : ℕ} (ha : a ∈ values p) (hb : b ∈ values q) :
    a ||| b ∈ values (mergePools p q) :=
  OncePositive.merge_mem ha hb

lemma portChoices_membership (P : Pools) (g : Fin 5) (b : Bool) (f : Fin 7 → ℕ)
    (hf : ∀ i, f i ∈ values (P i)) :
    rawMask (S18Geometry.port g b) ||| or7 (fun i => if i ∈ S18Geometry.locations g b then f i else 0) ∈
      values (portChoices P g b) := by
  rw [S18Geometry.rawMask_port]
  fin_cases g <;> cases b
  · simpa [portChoices, leftChoices, S18Geometry.locations, or7, OncePositive.or7] using hf 0
  · simpa [portChoices, rightChoices, S18Geometry.locations, or7, OncePositive.or7, basis] using
      merge_mem (merge_mem (hf 1) (hf 2)) (hf 3)
  · simpa [portChoices, leftChoices, S18Geometry.locations, or7, OncePositive.or7] using
      merge_mem (hf 1) (hf 2)
  · simpa [portChoices, rightChoices, S18Geometry.locations, or7, OncePositive.or7, basis] using
      merge_mem (OnceResource.mem_singleton (by decide : 25 < 64)) (hf 4)
  · simpa [portChoices, leftChoices, S18Geometry.locations, or7, OncePositive.or7] using hf 2
  · simpa [portChoices, rightChoices, S18Geometry.locations, or7, OncePositive.or7, basis] using
      merge_mem (OnceResource.mem_singleton (by decide : 42 < 64)) (hf 5)
  · simpa [portChoices, leftChoices, S18Geometry.locations, or7, OncePositive.or7] using hf 3
  · simpa [portChoices, rightChoices, S18Geometry.locations, or7, OncePositive.or7, basis] using
      merge_mem (OnceResource.mem_singleton (by decide : 52 < 64)) (hf 6)
  · simpa [portChoices, leftChoices, S18Geometry.locations, or7, OncePositive.or7] using one_pool_good.1
  · simpa [portChoices, rightChoices, S18Geometry.locations, or7, OncePositive.or7] using hf 1

lemma rep_port_mem {used : ℕ} {P : Pools} {g : Fin 5} {b : Bool} {m : ℕ}
    (h : Rep used P (S18Geometry.port g b) m) (hu : used.testBit g.val = false) :
    m ∈ values (portChoices P g b) := by
  obtain ⟨f, hf, hm⟩ := h g b hu (Finset.Subset.refl _)
  rw [hm, or7_filtered (fun i => (hf i).2)]
  exact portChoices_membership P g b f (fun i => (hf i).1)

lemma group_candidate {used : ℕ} {ps : List ℕ} {g : Fin 4} {a b : ℕ}
    (ha : Rep used (poolView ps) (S18Geometry.port ⟨g.val, by omega⟩ false) a)
    (hb : Rep used (poolView ps) (S18Geometry.port ⟨g.val, by omega⟩ true) b)
    (hu : used.testBit g.val = false) (hab : a &&& b < 64) :
    a &&& b ∈ values (pairMasks (· &&& ·) (leftPool ps g.val) (rightPool ps g.val)) := by
  have hleft := rep_port_mem ha hu
  have hright := rep_port_mem hb hu
  simp only [portChoices_view, Bool.false_eq_true, ↓reduceIte] at hleft hright
  exact OnceResource.mem_pairMasks hleft hright hab

lemma filter_candidate {used : ℕ} {ps : List ℕ} {m : ℕ}
    (h : Rep used (poolView ps) (S18Geometry.port 4 true) m)
    (hu : used.testBit 4 = false) : m ∈ values (ps.getD 1 1) :=
  rep_port_mem h hu

end S18Positive


namespace S18Resource

lemma set_getD_self (xs : List ℕ) (i d : ℕ) : xs.set i (xs.getD i d) = xs := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => exact congrArg (List.cons x) (ih i)

lemma lift_successor_or_discard {s : State} {k loc : ℕ}
    (hk : k ∈ s.2.2) (hloc : loc < 7) (hlive : live s.1 loc = true) :
    prune (s.1, s.2.1.set loc (addCarrier (s.2.1.getD loc 1) k), s.2.2.erase k) ∈ successors s := by
  by_cases hchange : addCarrier (s.2.1.getD loc 1) k = s.2.1.getD loc 1
  · rw [hchange, set_getD_self]
    exact discard_successor hk
  · exact lift_successor hk hloc hlive hchange

lemma lift_reachable {s : State} {k loc : ℕ}
    (hk : k ∈ s.2.2) (hloc : loc < 7) (hlive : live s.1 loc = true) :
    Relation.ReflTransGen (fun a b : State => b ∈ successors a) s
      (prune (s.1, s.2.1.set loc (addCarrier (s.2.1.getD loc 1) k), s.2.2.erase k)) :=
  Relation.ReflTransGen.single (lift_successor_or_discard hk hloc hlive)

end S18Resource

namespace S18Positive

open S18Resource OnceGeometry

lemma rep_of_dead_class {used : ℕ} {P : Pools} {S : Finset (Fin 10)} {v : Fin 10}
    (hv : v ∈ S) (hd : live used (vertexClass v).val = false) (m : ℕ) :
    Rep used P S m := by
  intro g b hg hS
  have hl := S18Geometry.port_locations_live hg b (S18Geometry.support_class hS hv)
  simp [hd] at hl

lemma positive_lift_step {s : State} {S : Finset (Fin 10)} {m k : ℕ}
    (hlen : s.2.1.length = 7) (hp : PoolsGood (poolView s.2.1))
    (h : Rep s.1 (poolView s.2.1) S m) (hs : S.Nonempty)
    (hk : k < 64) (hmem : k ∈ s.2.2) :
    ∃ t : State,
      Relation.ReflTransGen (fun a b : State => b ∈ successors a) s t ∧
      t.1 = s.1 ∧ t.2.2 = s.2.2.erase k ∧
      t.2.1.length = 7 ∧ PoolsGood (poolView t.2.1) ∧
      (∀ T n, Rep s.1 (poolView s.2.1) T n → Rep t.1 (poolView t.2.1) T n) ∧
      Rep t.1 (poolView t.2.1) S (m ||| k) := by
  obtain ⟨v, hv⟩ := hs
  by_cases hl : live s.1 (vertexClass v).val = true
  · let q : State := (s.1,
        s.2.1.set (vertexClass v).val (addCarrier (s.2.1.getD (vertexClass v).val 1) k),
        s.2.2.erase k)
    have hqgood : PoolsGood (poolView q.2.1) := poolsGood_set hlen hp (vertexClass v) hk
    refine ⟨prune q, lift_reachable hmem (vertexClass v).isLt hl, rfl, rfl,
      prune_pools_length q, poolsGood_prune hqgood, ?_, ?_⟩
    · intro T n hT
      apply rep_prune (s := q) hqgood
      change Rep s.1 (poolView (s.2.1.set (vertexClass v).val
        (addCarrier (s.2.1.getD (vertexClass v).val 1) k))) T n
      rw [poolView_set hlen]
      exact rep_mono (liftPool_mono _ _ _) hT
    · apply rep_prune (s := q) hqgood
      change Rep s.1 (poolView (s.2.1.set (vertexClass v).val
        (addCarrier (s.2.1.getD (vertexClass v).val 1) k))) S (m ||| k)
      rw [poolView_set hlen]
      exact rep_lift h hk hv
  · have hd : live s.1 (vertexClass v).val = false := Bool.eq_false_of_not_eq_true hl
    let q : State := (s.1, s.2.1, s.2.2.erase k)
    refine ⟨prune q, Relation.ReflTransGen.single (discard_successor hmem), rfl, rfl,
      prune_pools_length q, poolsGood_prune hp, ?_, ?_⟩
    · intro T n hT
      exact rep_prune (s := q) hp hT
    · exact rep_of_dead_class hv hd _

lemma positive_group_step {s : State} {g : Fin 4} {a b : ℕ}
    (hu : s.1 < 64) (hp : PoolsGood (poolView s.2.1))
    (ha : Rep s.1 (poolView s.2.1) (S18Geometry.port ⟨g.val, by omega⟩ false) a)
    (hb : Rep s.1 (poolView s.2.1) (S18Geometry.port ⟨g.val, by omega⟩ true) b)
    (hg : s.1.testBit g.val = false) (hab : a &&& b < 64) (hne : a &&& b ≠ 0) :
    let t := prune (s.1 ||| (1 <<< g.val), s.2.1, insertZero (a &&& b) s.2.2)
    t ∈ successors s ∧ t.1 < 64 ∧ t.2.1.length = 7 ∧ PoolsGood (poolView t.2.1) ∧
      (∀ T n, Rep s.1 (poolView s.2.1) T n → Rep t.1 (poolView t.2.1) T n) := by
  dsimp only
  have hc := group_candidate ha hb hg hab
  refine ⟨group_successor g.isLt hg hc hne, mark_used_lt hu ⟨g.val, by omega⟩,
    prune_pools_length _, poolsGood_prune hp, ?_⟩
  intro T n hT
  exact rep_mark_prune hp hT ⟨g.val, by omega⟩ _

lemma positive_filter_step {s : State} {k carrier : ℕ}
    (hu : s.1 < 64) (hp : PoolsGood (poolView s.2.1))
    (hmem : k ∈ s.2.2)
    (hcarrier : Rep s.1 (poolView s.2.1) (S18Geometry.port 4 true) carrier)
    (hg : s.1.testBit 4 = false) (hne : k &&& carrier ≠ 0) :
    let t := prune (s.1 ||| 16, s.2.1, insertZero (k &&& carrier) (s.2.2.erase k))
    t ∈ successors s ∧ t.1 < 64 ∧ t.2.1.length = 7 ∧ PoolsGood (poolView t.2.1) ∧
      (∀ T n, Rep s.1 (poolView s.2.1) T n → Rep t.1 (poolView t.2.1) T n) := by
  dsimp only
  have hc := filter_candidate hcarrier hg
  refine ⟨filter_successor hmem hg hc hne, mark_used_lt hu 4,
    prune_pools_length _, poolsGood_prune hp, ?_⟩
  intro T n hT
  exact rep_mark_prune hp hT 4 _

end S18Positive


namespace S18Simulation

open S18Resource S18Positive
open OnceResource.IndexCopies OnceResource.TokenMap

abbrev Reach (s t : State) : Prop :=
  Relation.ReflTransGen (fun a b : State => b ∈ successors a) s t

def contrib (S : Finset (Fin 10)) (m : ℕ) : Multiset ℕ :=
  if S = ∅ then OnceResource.TokenMap.token m else 0

def Healthy (s : State) : Prop :=
  s.1 < 64 ∧ s.2.1.length = 7 ∧ OncePositive.PoolsGood (OncePositive.poolView s.2.1)

def Preserves (s t : State) : Prop :=
  ∀ T m, S18Positive.Rep s.1 (OncePositive.poolView s.2.1) T m →
    S18Positive.Rep t.1 (OncePositive.poolView t.2.1) T m

def LocalResult (s q : State) (S : Finset (Fin 10)) (m : ℕ)
    (rest : Multiset ℕ) (group : Option (Fin 5)) : Prop :=
  Reach s q ∧ Healthy q ∧ (q.2.2 : Multiset ℕ) = contrib S m + rest ∧
  Preserves s q ∧ (S.Nonempty → Rep q.1 (OncePositive.poolView q.2.1) S m) ∧
  (∀ g : Fin 5, q.1.testBit g.val = true → s.1.testBit g.val = true ∨ group = some g)

def ProgramCallback (S : ℕ → Finset (Fin 10)) (M A B : ℕ → ℕ)
    (G : ℕ → Option (Fin 5)) (start n : ℕ) : Prop :=
  ∀ t < n, ∀ (s : State) (rest : Multiset ℕ), Healthy s →
    ((S (A (start + t))).Nonempty →
      Rep s.1 (OncePositive.poolView s.2.1) (S (A (start + t))) (M (A (start + t)))) →
    ((S (B (start + t))).Nonempty →
      Rep s.1 (OncePositive.poolView s.2.1) (S (B (start + t))) (M (B (start + t)))) →
    (s.2.2 : Multiset ℕ) = contrib (S (A (start + t))) (M (A (start + t))) +
      contrib (S (B (start + t))) (M (B (start + t))) + rest →
    (∀ g : Fin 5, G (start + t) = some g → s.1.testBit g.val = false) →
    ∃ q, LocalResult s q (S (start + t)) (M (start + t)) rest (G (start + t))

def GroupUnique (G : ℕ → Option (Fin 5)) (start n : ℕ) : Prop :=
  ∀ i < n, ∀ j < n, ∀ g : Fin 5,
    G (start + i) = some g → G (start + j) = some g → i = j

def ProgramInv (S : ℕ → Finset (Fin 10)) (M A B : ℕ → ℕ)
    (G : ℕ → Option (Fin 5)) (start n t : ℕ) (s : State) : Prop :=
  Healthy s ∧ (s.2.2 : Multiset ℕ) =
    project (fun w => S w = ∅) M (Available (fun w => S w = ∅) start (start+n) A B t) ∧
  (∀ w < start + t, (S w).Nonempty →
    Rep s.1 (OncePositive.poolView s.2.1) (S w) (M w)) ∧
  ∀ g : Fin 5, s.1.testBit g.val = true → ∃ j < t, G (start + j) = some g

lemma program_inv_step {S : ℕ → Finset (Fin 10)} {M A B : ℕ → ℕ}
    {G : ℕ → Option (Fin 5)} {start n t : ℕ} {s : State}
    (hv : Valid start A B n)
    (hcap : ∀ w, S w = ∅ → ReadCount start A B n w ≤ 1)
    (hgroups : GroupUnique G start n) (hcallback : ProgramCallback S M A B G start n)
    (ht : t < n) (hinv : ProgramInv S M A B G start n t s) :
    ∃ q, Reach s q ∧ ProgramInv S M A B G start n (t+1) q := by
  obtain ⟨hhealthy, hzeros, hreps, hused⟩ := hinv
  obtain ⟨ha, hb, hab⟩ := hv t ht
  have hcap' : ∀ w, S w = ∅ → ReadCount start A B n w ≤ Capacity (start+n) w := by
    intro w hw
    apply (hcap w hw).trans
    unfold Capacity
    split_ifs <;> decide
  obtain ⟨rest, hids, _⟩ := available_step_decomp (fun w => S w = ∅) hv hcap' ht
  have hzero_input : (s.2.2 : Multiset ℕ) =
      contrib (S (A (start + t))) (M (A (start + t))) +
      contrib (S (B (start + t))) (M (B (start + t))) + project (fun w => S w = ∅) M rest := by
    rw [hzeros, hids, project_cons, project_cons]
    simp only [contrib, Multiset.add_assoc]
  have hunused : ∀ g : Fin 5, G (start + t) = some g → s.1.testBit g.val = false := by
    intro g hg
    cases hbit : s.1.testBit g.val with
    | false => rfl
    | true =>
      obtain ⟨j, hj, hjg⟩ := hused g hbit
      have heq := hgroups t ht j (by omega) g hg hjg
      omega
  obtain ⟨q, hreach, hhealth, hzero, hpres, hnew, huse⟩ :=
    hcallback t ht s (project (fun w => S w = ∅) M rest) hhealthy
      (hreps _ ha) (hreps _ hb) hzero_input hunused
  refine ⟨q, hreach, hhealth, ?_, ?_, ?_⟩
  · rw [Available, project_step (fun w => S w = ∅) M hids hab]
    have hne : start+t ≠ start+n := by omega
    simpa only [hne, and_false, ite_false, Multiset.add_zero, contrib] using hzero
  · intro w hw hSw
    by_cases hold : w < start+t
    · exact hpres _ _ (hreps w hold hSw)
    · have heq : w = start+t := by omega
      subst w
      exact hnew hSw
  · intro g hg
    rcases huse g hg with hg | hg
    · obtain ⟨j, hj, hjg⟩ := hused g hg
      exact ⟨j, by omega, hjg⟩
    · exact ⟨t, by omega, hg⟩

lemma program_induction_prefix {S : ℕ → Finset (Fin 10)} {M A B : ℕ → ℕ}
    {G : ℕ → Option (Fin 5)} {start n : ℕ} {s₀ : State}
    (hv : Valid start A B n) (hcap : ∀ w, S w = ∅ → ReadCount start A B n w ≤ 1)
    (hgroups : GroupUnique G start n) (hcallback : ProgramCallback S M A B G start n)
    (hinit : ProgramInv S M A B G start n 0 s₀) :
    ∀ t ≤ n, ∃ s, Reach s₀ s ∧ ProgramInv S M A B G start n t s := by
  intro t
  induction t with
  | zero => intro _; exact ⟨s₀, Relation.ReflTransGen.refl, hinit⟩
  | succ t ih =>
    intro ht
    obtain ⟨s, hreach, hinv⟩ := ih (by omega)
    obtain ⟨q, hstep, hiq⟩ := program_inv_step hv hcap hgroups hcallback (by omega) hinv
    exact ⟨q, hreach.trans hstep, hiq⟩

lemma program_target_excluded {S : ℕ → Finset (Fin 10)} {M A B : ℕ → ℕ}
    {G : ℕ → Option (Fin 5)} {start n w : ℕ}
    (hsafe : ∀ s : State, Reach initial s → 56 ∉ s.2.2)
    (hv : Valid start A B n) (hcap : ∀ u, S u = ∅ → ReadCount start A B n u ≤ 1)
    (hgroups : GroupUnique G start n) (hcallback : ProgramCallback S M A B G start n)
    (hinit : ProgramInv S M A B G start n 0 initial)
    (hw : w ∈ Available (fun u => S u = ∅) start (start+n) A B n)
    (hSw : S w = ∅) (hMw : M w = 56) : False := by
  obtain ⟨s, hr, hi⟩ := program_induction_prefix hv hcap hgroups hcallback hinit n (Nat.le_refl n)
  have hMne : M w ≠ 0 := by omega
  have hm := project_mem (fun u => S u = ∅) M hw hSw hMne
  rw [hMw] at hm
  have ht : 56 ∈ s.2.2 := by
    change 56 ∈ (s.2.2 : Multiset ℕ)
    rw [hi.2.1]
    exact hm
  exact hsafe s hr ht

end S18Simulation


namespace S18Simulation

open S18Geometry

def ProgramSemantics (S : ℕ → Finset (Fin 10)) (M A B : ℕ → ℕ)
    (G : ℕ → Option (Fin 5)) (Op : ℕ → Bool) (start n : ℕ) : Prop :=
  ∀ t < n,
    if Op (start + t) then
      S (start + t) = ∅ ∧ M (start + t) = M (A (start + t)) &&& M (B (start + t)) ∧
        (match G (start + t) with
        | none => S (A (start + t)) = ∅ ∧ S (B (start + t)) = ∅
        | some g =>
          (S (A (start + t)) = port g false ∧ S (B (start + t)) = port g true) ∨
          (S (A (start + t)) = port g true ∧ S (B (start + t)) = port g false))
    else G (start + t) = none ∧
      S (start + t) = S (A (start + t)) ∪ S (B (start + t)) ∧
      M (start + t) = M (A (start + t)) ||| M (B (start + t))

end S18Simulation


namespace S18Simulation

open S18Resource S18Positive OnceGeometry
open OnceResource.IndexCopies OnceResource.TokenMap

lemma initial_program_inv (S : ℕ → Finset (Fin 10)) (M A B : ℕ → ℕ)
    (G : ℕ → Option (Fin 5)) {start n seed : ℕ}
    (hseed : seed < start) (hSseed : S seed = ∅) (hMseed : M seed = 63)
    (hother : ∀ w < start, S w = ∅ → w ≠ seed → M w = 0)
    (hpositive : ∀ w < start, (S w).Nonempty → M w = rawMask (S w)) :
    ProgramInv S M A B G start n 0 initial := by
  have hi : Healthy initial := ⟨by decide, rfl, poolsGood_replicate_one⟩
  refine ⟨hi, ?_, ?_, ?_⟩
  · have hMne : M seed ≠ 0 := by omega
    have hf : start+n ≠ seed := by omega
    have hproj := project_initial (fun w => S w = ∅) M
      (fork := start+n) hseed hSseed hMne hother
    rw [Available, hproj, hMseed]
    simp [initial, hf]
  · intro w hw hSw
    rw [hpositive w (by omega) hSw]
    exact rep_raw hi.2.2 _
  · intro g hg
    have hn : (32 : ℕ).testBit g.val = false := by fin_cases g <;> decide
    change (32 : ℕ).testBit g.val = true at hg
    rw [hn] at hg
    contradiction

end S18Simulation


namespace S18Positive

open S18Resource OnceGeometry

lemma frame_preserves {s t : State}
    (hu : s.1 < 64) (hlen : s.2.1.length = 7) (hp : PoolsGood (poolView s.2.1))
    (ht : t.1 = s.1) (hps : t.2.1 = s.2.1 ∨ t.2.1 = (prune s).2.1) :
    t.1 < 64 ∧ t.2.1.length = 7 ∧ PoolsGood (poolView t.2.1) ∧
      (∀ T n, Rep s.1 (poolView s.2.1) T n → Rep t.1 (poolView t.2.1) T n) := by
  refine ⟨by simpa only [ht] using hu, ?_⟩
  rcases hps with he | he
  · rw [he, ht]
    exact ⟨hlen, hp, fun _ _ h => h⟩
  · rw [he, ht]
    exact ⟨prune_pools_length s, poolsGood_prune hp, fun _ _ h => rep_prune hp h⟩

lemma zero_binary_positive_state {s : State} (a b : ℕ) (isAnd : Bool) (rest : Multiset ℕ)
    (hu : s.1 < 64) (hlen : s.2.1.length = 7) (hp : PoolsGood (poolView s.2.1))
    (hz : (s.2.2 : Multiset ℕ) =
      ZeroTransitions.token a + ZeroTransitions.token b + rest) :
    ∃ t : State,
      Relation.ReflTransGen (fun p q : State => q ∈ successors p) s t ∧
      t.1 = s.1 ∧
      (t.2.2 : Multiset ℕ) =
        ZeroTransitions.token (if isAnd then a &&& b else a ||| b) + rest ∧
      t.1 < 64 ∧ t.2.1.length = 7 ∧ PoolsGood (poolView t.2.1) ∧
      (∀ T n, Rep s.1 (poolView s.2.1) T n → Rep t.1 (poolView t.2.1) T n) := by
  obtain ⟨t, hr, hz', ht, hps⟩ := ZeroTransitions.zero_binary a b isAnd rest hz
  exact ⟨t, hr, ht, hz', frame_preserves hu hlen hp ht hps⟩

end S18Positive

namespace S18Simulation
open S18Resource S18Geometry S18Positive

lemma lift_token_step {s : State} {S : Finset (Fin 10)} {m k : ℕ} {rest : Multiset ℕ}
    (hs : Healthy s) (hS : S.Nonempty) (hm : Rep s.1 (poolView s.2.1) S m)
    (hk : k < 64) (hz : (s.2.2 : Multiset ℕ) = OnceResource.TokenMap.token k + rest) :
    ∃ q, LocalResult s q S (m ||| k) rest none := by
  have hne : S ≠ ∅ := hS.ne_empty
  by_cases hk0 : k = 0
  · subst k
    refine ⟨s, Relation.ReflTransGen.refl, hs, ?_, (fun _ _ h => h), ?_, ?_⟩
    · simpa [contrib, OnceResource.TokenMap.token, hne] using hz
    · intro _
      simpa using hm
    · exact fun _ h => Or.inl h
  · have hmem : k ∈ s.2.2 := by
      have hm' : k ∈ (s.2.2 : Multiset ℕ) := by rw [hz]; simp [OnceResource.TokenMap.token, hk0]
      exact hm'
    obtain ⟨q, hr, hu, hqz, hl, hp, hpres, hrep⟩ :=
      positive_lift_step hs.2.1 hs.2.2 hm hS hk hmem
    refine ⟨q, hr, ⟨by simpa [hu] using hs.1, hl, hp⟩, ?_, hpres,
      (fun _ => hrep), ?_⟩
    · rw [hqz, ← Multiset.coe_erase, hz]
      simp [contrib, hne, OnceResource.TokenMap.token, hk0]
    · intro g hg
      exact Or.inl (hu ▸ hg)

lemma or_local {s : State} {S T : Finset (Fin 10)} {a b : ℕ} {rest : Multiset ℕ}
    (hs : Healthy s) (ha : S.Nonempty → Rep s.1 (poolView s.2.1) S a)
    (hb : T.Nonempty → Rep s.1 (poolView s.2.1) T b)
    (hab : a < 64 ∧ b < 64)
    (hz : (s.2.2 : Multiset ℕ) = contrib S a + contrib T b + rest) :
    ∃ q, LocalResult s q (S ∪ T) (a ||| b) rest none := by
  by_cases hS : S = ∅
  · subst S
    by_cases hT : T = ∅
    · subst T
      have hz' : (s.2.2 : Multiset ℕ) =
          ZeroTransitions.token a + ZeroTransitions.token b + rest := by
        simpa [contrib, ZeroTransitions.token, OnceResource.TokenMap.token] using hz
      obtain ⟨q, hr, hu, hqz, hqu, hql, hqp, hpres⟩ :=
        zero_binary_positive_state a b false rest hs.1 hs.2.1 hs.2.2 hz'
      refine ⟨q, hr, ⟨hqu, hql, hqp⟩, ?_, hpres, ?_, ?_⟩
      · simpa [contrib, ZeroTransitions.token, OnceResource.TokenMap.token] using hqz
      · simp
      · intro g hg
        exact Or.inl (hu ▸ hg)
    · have hTn : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr hT
      have hz' : (s.2.2 : Multiset ℕ) = OnceResource.TokenMap.token a + rest := by
        simpa [contrib, hT] using hz
      obtain ⟨q, hq⟩ := lift_token_step hs hTn (hb hTn) hab.1 hz'
      refine ⟨q, ?_⟩
      simpa [Nat.or_comm] using hq
  · have hSn : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
    by_cases hT : T = ∅
    · subst T
      have hz' : (s.2.2 : Multiset ℕ) = OnceResource.TokenMap.token b + rest := by
        simpa [contrib, hS] using hz
      obtain ⟨q, hq⟩ := lift_token_step hs hSn (ha hSn) hab.2 hz'
      exact ⟨q, by simpa using hq⟩
    · have hTn : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr hT
      have hST : S ∪ T ≠ ∅ := (hSn.mono Finset.subset_union_left).ne_empty
      refine ⟨s, Relation.ReflTransGen.refl, hs, ?_, (fun _ _ h => h), ?_, ?_⟩
      · simpa [contrib, hS, hT, hST] using hz
      · intro _
        exact rep_or hs.2.2 (ha hSn) (hb hTn)
      · exact fun _ h => Or.inl h

lemma marked_group {used : ℕ} {g h : Fin 5}
    (ht : (used ||| (1 <<< g.val)).testBit h.val = true) :
    used.testBit h.val = true ∨ g = h := by
  rw [Nat.testBit_or, Bool.or_eq_true] at ht
  rcases ht with ht | ht
  · exact Or.inl ht
  · right
    have hsingle := OnceResource.testBit_singleton_iff.mp ht
    exact Fin.ext hsingle

lemma pure_local {s : State} {g : Fin 4} {a b : ℕ} {rest : Multiset ℕ}
    (hs : Healthy s) (ha : Rep s.1 (poolView s.2.1) (port ⟨g.val, by omega⟩ false) a)
    (hb : Rep s.1 (poolView s.2.1) (port ⟨g.val, by omega⟩ true) b)
    (hk : a &&& b < 64) (hunused : s.1.testBit g.val = false)
    (hz : (s.2.2 : Multiset ℕ) = rest) :
    ∃ q, LocalResult s q ∅ (a &&& b) rest (some (⟨g.val, by omega⟩ : Fin 5)) := by
  by_cases hk0 : a &&& b = 0
  · refine ⟨s, Relation.ReflTransGen.refl, hs, ?_, (fun _ _ h => h), ?_, ?_⟩
    · simpa [contrib, OnceResource.TokenMap.token, hk0] using hz
    · simp
    · exact fun _ h => Or.inl h
  · let q := prune (s.1 ||| (1 <<< g.val), s.2.1, insertZero (a &&& b) s.2.2 )
    obtain ⟨hr, hu, hl, hp, hpres⟩ := positive_group_step hs.1 hs.2.2 ha hb hunused hk hk0
    refine ⟨q, Relation.ReflTransGen.single hr, ⟨hu, hl, hp⟩, ?_, hpres, ?_, ?_⟩
    · change (insertZero (a &&& b) s.2.2 : Multiset ℕ) = _
      rw [ZeroTransitions.coe_insertZero, hz]
      simp [contrib, OnceResource.TokenMap.token, hk0]
    · simp
    · intro h hh
      change (s.1 ||| (1 <<< g.val)).testBit h.val = true at hh
      rcases marked_group (g := (⟨g.val, by omega⟩ : Fin 5)) hh with hh | hh
      · exact Or.inl hh
      · exact Or.inr (congrArg some hh)

lemma zero_local {s : State} {a b : ℕ} {rest : Multiset ℕ}
    (hs : Healthy s)
    (hz : (s.2.2 : Multiset ℕ) = OnceResource.TokenMap.token a + OnceResource.TokenMap.token b + rest) :
    ∃ q, LocalResult s q ∅ (a &&& b) rest none := by
  obtain ⟨q, hr, hu, hqz, hqu, hql, hqp, hpres⟩ :=
    zero_binary_positive_state a b true rest hs.1 hs.2.1 hs.2.2 hz
  refine ⟨q, hr, ⟨hqu, hql, hqp⟩, ?_, hpres, ?_, ?_⟩
  · exact hqz
  · simp
  · intro g hg
    exact Or.inl (hu ▸ hg)

end S18Simulation

namespace S18Simulation

open S18Resource S18Geometry S18Positive

lemma filter_local {s : State} {k carrier : ℕ} {rest : Multiset ℕ}
    (hs : Healthy s)
    (hb : Rep s.1 (poolView s.2.1) (port 4 true) carrier)
    (hunused : s.1.testBit 4 = false)
    (hz : (s.2.2 : Multiset ℕ) = OnceResource.TokenMap.token k + rest) :
    ∃ q, LocalResult s q ∅ (k &&& carrier) rest (some (4 : Fin 5)) := by
  by_cases hk : k = 0
  · subst k
    refine ⟨s, Relation.ReflTransGen.refl, hs, ?_, (fun _ _ h => h), ?_, ?_⟩
    · simpa [contrib, OnceResource.TokenMap.token] using hz
    · simp
    · exact fun _ h => Or.inl h
  · have hz' : (s.2.2 : Multiset ℕ) = {k} + rest := by
      simpa [OnceResource.TokenMap.token, hk] using hz
    by_cases hresult : k &&& carrier = 0
    · obtain ⟨q, hr, hqz, hu, hpool⟩ := ZeroTransitions.discard_one hz'
      obtain ⟨hqu, hql, hgood, hpres⟩ :=
        frame_preserves hs.1 hs.2.1 hs.2.2 hu (Or.inr hpool)
      refine ⟨q, hr, ⟨hqu, hql, hgood⟩, ?_, hpres, ?_, ?_⟩
      · simpa [contrib, OnceResource.TokenMap.token, hresult] using hqz
      · simp
      · intro g hg
        exact Or.inl (hu ▸ hg)
    · have hmem := ZeroTransitions.mem_of_zero_eq hz'
      let q : State := prune (s.1 ||| 16, s.2.1,
        insertZero (k &&& carrier) (s.2.2.erase k))
      obtain ⟨hr, hu, hl, hp, hpres⟩ :=
        positive_filter_step hs.1 hs.2.2 hmem hb hunused hresult
      refine ⟨q, Relation.ReflTransGen.single hr, ⟨hu, hl, hp⟩, ?_, hpres, ?_, ?_⟩
      · change (insertZero (k &&& carrier) (s.2.2.erase k) : Multiset ℕ) = _
        rw [ZeroTransitions.coe_insertZero, ZeroTransitions.erase_of_zero_eq hz']
        simp [contrib, OnceResource.TokenMap.token, hresult]
      · simp
      · intro g hg
        rcases marked_group (used := s.1) (g := (4 : Fin 5)) (h := g) hg with hg | hg
        · exact Or.inl hg
        · exact Or.inr (congrArg some hg)

end S18Simulation

namespace S18Simulation
open S18Resource S18Geometry S18Positive

lemma gate_local {s : State} {S T U : Finset (Fin 10)} {a b c : Nat}
    {rest : Multiset Nat} (op : Bool) (group : Option (Fin 5))
    (hs : Healthy s) (ha : S.Nonempty → Rep s.1 (poolView s.2.1) S a)
    (hb : T.Nonempty → Rep s.1 (poolView s.2.1) T b)
    (hm : a < 64 ∧ b < 64 ∧ c < 64)
    (hz : (s.2.2 : Multiset Nat) = contrib S a + contrib T b + rest)
    (hunused : ∀ g : Fin 5, group = some g → s.1.testBit g.val = false)
    (hsem : if op then
      U = ∅ ∧ c = a &&& b ∧
        (match group with
        | none => S = ∅ ∧ T = ∅
        | some g => (S = port g false ∧ T = port g true) ∨
          (S = port g true ∧ T = port g false))
      else group = none ∧ U = S ∪ T ∧ c = a ||| b) :
    ∃ q, LocalResult s q U c rest group := by
  cases op with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hsem
    obtain ⟨rfl, rfl, rfl⟩ := hsem
    exact or_local hs ha hb ⟨hm.1, hm.2.1⟩ hz
  | true =>
    simp only [↓reduceIte] at hsem
    obtain ⟨rfl, rfl, hports⟩ := hsem
    cases group with
    | none =>
      obtain ⟨rfl, rfl⟩ := hports
      exact zero_local hs (by simpa [contrib] using hz)
    | some g =>
      have hu := hunused g rfl
      by_cases hg : g.val < 4
      · have hl : (port g false).Nonempty := by fin_cases g <;> simp_all [port]
        have hr : (port g true).Nonempty := by fin_cases g <;> simp [port]
        rcases hports with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · have hz' : (s.2.2 : Multiset Nat) = rest := by
            simpa [contrib, hl.ne_empty, hr.ne_empty] using hz
          exact pure_local (g := ⟨g.val, hg⟩) hs (ha hl) (hb hr) hm.2.2 hu hz'
        · have hz' : (s.2.2 : Multiset Nat) = rest := by
            simpa [contrib, hl.ne_empty, hr.ne_empty] using hz
          obtain ⟨q, hq⟩ := pure_local (g := ⟨g.val, hg⟩) hs (hb hl) (ha hr)
            (by simpa [Nat.and_comm] using hm.2.2) hu hz'
          exact ⟨q, by simpa [Nat.and_comm] using hq⟩
      · have hg4 : g = 4 := Fin.ext (by omega)
        subst g
        have hr : (port 4 true).Nonempty := by decide
        rcases hports with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · have hz' : (s.2.2 : Multiset Nat) = OnceResource.TokenMap.token a + rest := by
            simpa [contrib, port] using hz
          exact filter_local hs (hb hr) hu hz'
        · have hz' : (s.2.2 : Multiset Nat) = OnceResource.TokenMap.token b + rest := by
            simpa [contrib, port] using hz
          obtain ⟨q, hq⟩ := filter_local hs (ha hr) hu hz'
          exact ⟨q, by simpa [Nat.and_comm] using hq⟩

lemma semantic_callback {S : Nat → Finset (Fin 10)} {M A B : Nat → Nat}
    {G : Nat → Option (Fin 5)} {Op : Nat → Bool} {start n : Nat}
    (hm : ∀ w, M w < 64) (hsem : ProgramSemantics S M A B G Op start n) :
    ProgramCallback S M A B G start n := by
  intro t ht s rest hs ha hb hz hgroups
  generalize hg : G (start + t) = group at hgroups ⊢
  cases group with
  | none =>
    exact gate_local (Op (start + t)) none hs ha hb
      ⟨hm _, hm _, hm _⟩ hz hgroups (by simpa [hg] using hsem t ht)
  | some g =>
    exact gate_local (Op (start + t)) (some g) hs ha hb
      ⟨hm _, hm _, hm _⟩ hz hgroups (by simpa [hg] using hsem t ht)

end S18Simulation


namespace S18Simulation

open S18Resource S18Positive OnceGeometry OnceActualSchedule
open DAGBridge.DagTools

lemma actual_target_exclusion {D : Dag} (hS : Strict 10 D) (hB : Bzero 10 D = 0)
    {g : ℕ} (hg : g < D.length) (ht : tag D g = true)
    (hdirty : FiveGroup.DAGBridge.DirtySides D g)
    (hbefore : ∀ j < g, tag D j = true →
      S18Prefix.AndSides (supp 10 D (opA D j)) (supp 10 D (opB D j)))
    {G : ℕ → Option (Fin 5)}
    (hgroups : GroupUnique G (start g) (remaining D g))
    (hsem : ProgramSemantics (supp 10 D) (wireMask D) (sourceA D) (sourceB D) G
      (fun w => tag D (w - 10)) (start g) (remaining D g)) :
    ¬ (supp 10 D (outW 10 D) = ∅ ∧ wireMask D (outW 10 D) = 56) := by
  intro hout
  have hd := S18Prefix.dirty_seed hS hg ht hdirty
  have hinit : ProgramInv (supp 10 D) (wireMask D) (sourceA D) (sourceB D) G
      (start g) (remaining D g) 0 initial := by
    apply initial_program_inv (supp 10 D) (wireMask D) (sourceA D) (sourceB D) G
      (seed := 10+g) (by unfold start; omega) hd.1 hd.2
    · intro w hw hz hne
      apply S18Prefix.before_seed_zero hS (Nat.le_of_lt hg) hbefore _ hz
      unfold start at hw
      omega
    · intro w hw hpos
      have hne : w ≠ 10+g := by intro heq; subst w; exact hpos.ne_empty hd.1
      apply S18Prefix.before_seed_raw hS (Nat.le_of_lt hg) hbefore
      unfold start at hw
      omega
  exact program_target_excluded (fun _ hr => reachable_no_target hr)
    (continuation_valid hS g) (S18Budget.continuation_capacity hS hB g)
    hgroups (semantic_callback (wireMask_lt D) hsem) hinit
    (final_output_available hS hg (start g + remaining D g)) hout.1 hout.2

end S18Simulation


namespace S18ActualLabels
open DAGBridge.DagTools OnceGeometry

def firstFive (g : Fin 5) : Fin 6 := ⟨g.val, by omega⟩

noncomputable def label (gate : Fin 6 → ℕ) (j : ℕ) : Option (Fin 5) :=
  if h : ∃ g : Fin 5, j = gate (firstFive g) then some (Classical.choose h) else none

lemma firstFive_injective : Function.Injective firstFive := by
  intro a b h
  apply Fin.ext
  exact congrArg (fun x : Fin 6 => x.val) h

lemma label_some_iff {gate : Fin 6 → ℕ} (hinj : Function.Injective gate)
    (j : ℕ) (g : Fin 5) : label gate j = some g ↔ j = gate (firstFive g) := by
  classical
  unfold label
  split_ifs with h
  · constructor
    · intro he
      have he' : Classical.choose h = g := Option.some.inj he
      exact he' ▸ Classical.choose_spec h
    · intro he
      have he' : firstFive (Classical.choose h) = firstFive g :=
        hinj ((Classical.choose_spec h).symm.trans he)
      rw [firstFive_injective he']
  · simp only [Option.noConfusion, false_iff]
    intro he
    exact h ⟨g, he⟩

lemma label_none_iff (gate : Fin 6 → ℕ) (j : ℕ) :
    label gate j = none ↔ ∀ g : Fin 5, j ≠ gate (firstFive g) := by
  classical
  unfold label
  split_ifs with h
  · simp only [Option.some_ne_none, false_iff, not_forall, Classical.not_not]
    exact h
  · simp only [true_iff]
    intro g he
    exact h ⟨g, he⟩

lemma label_unique {gate : Fin 6 → ℕ} (hinj : Function.Injective gate)
    {j k : ℕ} {g : Fin 5} (hj : label gate j = some g)
    (hk : label gate k = some g) : j = k :=
  ((label_some_iff hinj j g).mp hj).trans ((label_some_iff hinj k g).mp hk).symm

lemma gate_split (k : Fin 6) : k = 5 ∨ ∃ g : Fin 5, k = firstFive g := by
  by_cases hk : k.val = 5
  · exact Or.inl (Fin.ext hk)
  · refine Or.inr ⟨⟨k.val, by omega⟩, ?_⟩
    rfl

lemma label_semantics {D : Dag} (hS : Strict 10 D) {gate : Fin 6 → ℕ}
    (hinj : Function.Injective gate)
    (hvalid : ∀ k, gate k < D.length ∧ tag D (gate k) = true)
    (hports : ∀ g : Fin 5,
      (supp 10 D (opA D (gate (firstFive g))) = S18Geometry.port g false ∧
       supp 10 D (opB D (gate (firstFive g))) = S18Geometry.port g true) ∨
      (supp 10 D (opA D (gate (firstFive g))) = S18Geometry.port g true ∧
       supp 10 D (opB D (gate (firstFive g))) = S18Geometry.port g false))
    (htypes : ∀ j, j < D.length → tag D j = true →
      (∃ k : Fin 6, j = gate k) ∨
      (supp 10 D (opA D j) = ∅ ∧ supp 10 D (opB D j) = ∅))
    (j : ℕ) (hj : j < D.length) (hdirty : j ≠ gate 5) :
    if tag D j then
      supp 10 D (10+j) = ∅ ∧
      wireMask D (10+j) = wireMask D (opA D j) &&& wireMask D (opB D j) ∧
      (match label gate j with
      | none => supp 10 D (opA D j) = ∅ ∧ supp 10 D (opB D j) = ∅
      | some g =>
        (supp 10 D (opA D j) = S18Geometry.port g false ∧ supp 10 D (opB D j) = S18Geometry.port g true) ∨
        (supp 10 D (opA D j) = S18Geometry.port g true ∧ supp 10 D (opB D j) = S18Geometry.port g false))
    else label gate j = none ∧
      supp 10 D (10+j) = supp 10 D (opA D j) ∪ supp 10 D (opB D j) ∧
      wireMask D (10+j) = wireMask D (opA D j) ||| wireMask D (opB D j) := by
  classical
  have hm := wireMask_gate hS hj
  have hs := supp_gate hS j hj
  cases ht : tag D j with
  | false =>
    simp only [ht, Bool.false_eq_true, ↓reduceIte] at hm hs ⊢
    refine ⟨(label_none_iff gate j).mpr ?_, hs, hm⟩
    intro g he
    have hh := (hvalid (firstFive g)).2
    rw [← he, ht] at hh
    cases hh
  | true =>
    simp only [ht, ↓reduceIte] at hm hs ⊢
    cases hl : label gate j with
    | none =>
      have hz : supp 10 D (opA D j) = ∅ ∧ supp 10 D (opB D j) = ∅ := by
        rcases htypes j hj ht with ⟨k, hk⟩ | hz
        · rcases gate_split k with rfl | ⟨g, rfl⟩
          · exact False.elim (hdirty hk)
          · exact False.elim ((label_none_iff gate j).mp hl g hk)
        · exact hz
      refine ⟨?_, hm, hz⟩
      simpa only [hz.1, Finset.empty_inter] using hs
    | some g =>
      have he := (label_some_iff hinj j g).mp hl
      have hp := hports g
      rw [← he] at hp
      refine ⟨?_, hm, hp⟩
      have hd : S18Geometry.port g false ∩ S18Geometry.port g true = ∅ := by fin_cases g <;> decide
      rcases hp with ⟨ha,hb⟩ | ⟨ha,hb⟩
      · simpa only [ha,hb,hd] using hs
      · simpa only [ha,hb,Finset.inter_comm (S18Geometry.port g true) (S18Geometry.port g false),hd] using hs

end S18ActualLabels

namespace S18ActualLabels
open DAGBridge.DagTools OnceGeometry

lemma actual_other_sides {D : Dag} {gate : Fin 6 → ℕ}
    (hports : ∀ g : Fin 5,
      (supp 10 D (opA D (gate (firstFive g))) = S18Geometry.port g false ∧
       supp 10 D (opB D (gate (firstFive g))) = S18Geometry.port g true) ∨
      (supp 10 D (opA D (gate (firstFive g))) = S18Geometry.port g true ∧
       supp 10 D (opB D (gate (firstFive g))) = S18Geometry.port g false))
    (htypes : ∀ j, j < D.length → tag D j = true →
      (∃ k : Fin 6, j = gate k) ∨
      (supp 10 D (opA D j) = ∅ ∧ supp 10 D (opB D j) = ∅)) :
    ∀ j, j < D.length → j ≠ gate 5 → tag D j = true →
      S18Prefix.AndSides (supp 10 D (opA D j)) (supp 10 D (opB D j)) := by
  intro j hj hne ht
  change (supp 10 D (opA D j), supp 10 D (opB D j)) ∈ S18Prefix.allowedPairs ∨
    (supp 10 D (opB D j), supp 10 D (opA D j)) ∈ S18Prefix.allowedPairs
  rcases htypes j hj ht with ⟨k,hk⟩ | ⟨ha,hb⟩
  · rcases gate_split k with rfl | ⟨g,rfl⟩
    · exact False.elim (hne hk)
    · have hp := hports g
      rw [← hk] at hp
      have hm : (S18Geometry.port g false, S18Geometry.port g true) ∈
          S18Prefix.allowedPairs := by fin_cases g <;> decide
      rcases hp with ⟨ha,hb⟩ | ⟨ha,hb⟩
      · exact Or.inl (by simpa only [ha,hb] using hm)
      · exact Or.inr (by simpa only [ha,hb] using hm)
  · left
    rw [ha,hb]
    decide

lemma actual_before_sides {D : Dag} {gate : Fin 6 → ℕ}
    (hvalid : ∀ k, gate k < D.length ∧ tag D (gate k) = true)
    (hports : ∀ g : Fin 5,
      (supp 10 D (opA D (gate (firstFive g))) = S18Geometry.port g false ∧
       supp 10 D (opB D (gate (firstFive g))) = S18Geometry.port g true) ∨
      (supp 10 D (opA D (gate (firstFive g))) = S18Geometry.port g true ∧
       supp 10 D (opB D (gate (firstFive g))) = S18Geometry.port g false))
    (htypes : ∀ j, j < D.length → tag D j = true →
      (∃ k : Fin 6, j = gate k) ∨
      (supp 10 D (opA D j) = ∅ ∧ supp 10 D (opB D j) = ∅)) :
    ∀ j < gate 5, tag D j = true →
      S18Prefix.AndSides (supp 10 D (opA D j)) (supp 10 D (opB D j)) := by
  intro j hj ht
  exact actual_other_sides hports htypes j (by have := (hvalid 5).1; omega)
    (by omega) ht

end S18ActualLabels

namespace S18ActualLabels
open DAGBridge.DagTools OnceGeometry S18Simulation OnceActualSchedule

noncomputable def wireLabel (gate : Fin 6 → ℕ) (w : ℕ) : Option (Fin 5) := label gate (w - 10)

lemma actual_group_unique {gate : Fin 6 → ℕ} (hinj : Function.Injective gate) :
    GroupUnique (wireLabel gate) (start (gate 5)) (remaining D (gate 5)) := by
  intro i hi j hj g hgi hgj
  have he := label_unique hinj hgi hgj
  change start (gate 5) + i - 10 = start (gate 5) + j - 10 at he
  unfold start at he
  omega

lemma actual_program_semantics {D : Dag} (hS : Strict 10 D) {gate : Fin 6 → ℕ}
    (hinj : Function.Injective gate)
    (hvalid : ∀ k, gate k < D.length ∧ tag D (gate k) = true)
    (hports : ∀ g : Fin 5,
      (supp 10 D (opA D (gate (firstFive g))) = S18Geometry.port g false ∧
       supp 10 D (opB D (gate (firstFive g))) = S18Geometry.port g true) ∨
      (supp 10 D (opA D (gate (firstFive g))) = S18Geometry.port g true ∧
       supp 10 D (opB D (gate (firstFive g))) = S18Geometry.port g false))
    (htypes : ∀ j, j < D.length → tag D j = true →
      (∃ k : Fin 6, j = gate k) ∨
      (supp 10 D (opA D j) = ∅ ∧ supp 10 D (opB D j) = ∅)) :
    ProgramSemantics (supp 10 D) (wireMask D) (sourceA D) (sourceB D)
      (wireLabel gate) (fun w => tag D (w-10)) (start (gate 5)) (remaining D (gate 5)) := by
  intro t ht
  have hj : gate 5 + 1 + t < D.length := by unfold remaining at ht; omega
  have hn : gate 5 + 1 + t ≠ gate 5 := by omega
  have h := label_semantics hS hinj hvalid hports htypes (gate 5 + 1 + t) hj hn
  have he : start (gate 5) + t = 10 + (gate 5 + 1 + t) := by unfold start; omega
  simpa only [sourceA, sourceB, wireLabel, continuation_index, he, Nat.add_sub_cancel_left] using h

end S18ActualLabels

namespace S18ActualLabels
open DAGBridge.DagTools OnceGeometry S18Simulation

lemma six_gate_target_exclusion {D : Dag} (hS : Strict 10 D)
    (hB : Bzero 10 D = 0) {gate : Fin 6 → ℕ}
    (hinj : Function.Injective gate)
    (hvalid : ∀ k, gate k < D.length ∧ tag D (gate k) = true)
    (hports : ∀ g : Fin 5,
      (supp 10 D (opA D (gate (firstFive g))) = S18Geometry.port g false ∧
       supp 10 D (opB D (gate (firstFive g))) = S18Geometry.port g true) ∨
      (supp 10 D (opA D (gate (firstFive g))) = S18Geometry.port g true ∧
       supp 10 D (opB D (gate (firstFive g))) = S18Geometry.port g false))
    (hdirty : FiveGroup.DAGBridge.DirtySides D (gate 5))
    (htypes : ∀ j, j < D.length → tag D j = true →
      (∃ k : Fin 6, j = gate k) ∨
      (supp 10 D (opA D j) = ∅ ∧ supp 10 D (opB D j) = ∅)) :
    ¬ (supp 10 D (10 + D.length - 1) = ∅ ∧ wireMask D (10 + D.length - 1) = 56) := by
  exact actual_target_exclusion hS hB (hvalid 5).1 (hvalid 5).2 hdirty
    (actual_before_sides hvalid hports htypes) (actual_group_unique hinj)
    (actual_program_semantics hS hinj hvalid hports htypes)

end S18ActualLabels



namespace S18Structural

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

open PEqualNP.Outside.L_meta_2590.S18Structural.DagTools
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

namespace DagTools

def h3_evenSide (k : Fin 5) : Fin 10 := ⟨2 * k.val, by omega⟩

def h3_groupGate (r : Fin 10 → ℕ × Bool) (k : Fin 5) : ℕ :=
  (r (h3_evenSide k)).1

lemma h3_evenSide_injective : Function.Injective h3_evenSide := by
  intro k l he
  have := congrArg Fin.val he
  apply Fin.ext
  simp only [h3_evenSide] at this
  omega

lemma h3_evenSide_ne_opposite : ∀ k l : Fin 5,
    h3_evenSide k ≠ SideGeometry.opposite (h3_evenSide l) := by
  unfold h3_evenSide SideGeometry.opposite
  decide +kernel

lemma h3_side_in_pair : ∀ i : Fin 10, ∃ k : Fin 5,
    i = h3_evenSide k ∨ i = SideGeometry.opposite (h3_evenSide k) := by
  unfold h3_evenSide SideGeometry.opposite
  decide +kernel

lemma h3_groupGate_injective (r : Fin 10 → ℕ × Bool) (hinj : Function.Injective r)
    (hopp : ∀ i, r (SideGeometry.opposite i) = ((r i).1, !(r i).2)) :
    Function.Injective (h3_groupGate r) := by
  intro k l hkl
  rcases sem_same_gate hkl with he | he
  · exact (h3_evenSide_injective (hinj he)).symm
  · have he' : r (h3_evenSide l) = r (SideGeometry.opposite (h3_evenSide k)) := by
      rw [hopp]
      exact he
    exact False.elim (h3_evenSide_ne_opposite l k (hinj he'))

lemma h3_side_gate_is_group (r : Fin 10 → ℕ × Bool)
    (hopp : ∀ i, r (SideGeometry.opposite i) = ((r i).1, !(r i).2)) (i : Fin 10) :
    ∃ k : Fin 5, (r i).1 = h3_groupGate r k := by
  obtain ⟨k, hk | hk⟩ := h3_side_in_pair i
  · exact ⟨k, hk ▸ rfl⟩
  · refine ⟨k, ?_⟩
    rw [hk, hopp]
    rfl

lemma h3_group_supports {D : Dag} (r : Fin 10 → ℕ × Bool)
    (hopp : ∀ i, r (SideGeometry.opposite i) = ((r i).1, !(r i).2))
    (hsources : ∀ i, supp 10 D (src D (r i)) = SideGeometry.side i) (k : Fin 5) :
    (supp 10 D (opA D (h3_groupGate r k)) = SideGeometry.side (h3_evenSide k) ∧
      supp 10 D (opB D (h3_groupGate r k)) =
        SideGeometry.side (SideGeometry.opposite (h3_evenSide k))) ∨
    (supp 10 D (opA D (h3_groupGate r k)) =
        SideGeometry.side (SideGeometry.opposite (h3_evenSide k)) ∧
      supp 10 D (opB D (h3_groupGate r k)) = SideGeometry.side (h3_evenSide k)) := by
  cases hs : (r (h3_evenSide k)).2 with
  | false =>
    have hr : r (h3_evenSide k) = (h3_groupGate r k, false) := Prod.ext rfl hs
    have ho : r (SideGeometry.opposite (h3_evenSide k)) = (h3_groupGate r k, true) := by
      rw [hopp, hr]
      rfl
    exact Or.inl ⟨by simpa only [hr, sb_src_false] using hsources (h3_evenSide k),
      by simpa only [ho, sb_src_true] using hsources (SideGeometry.opposite (h3_evenSide k))⟩
  | true =>
    have hr : r (h3_evenSide k) = (h3_groupGate r k, true) := Prod.ext rfl hs
    have ho : r (SideGeometry.opposite (h3_evenSide k)) = (h3_groupGate r k, false) := by
      rw [hopp, hr]
      rfl
    exact Or.inr ⟨by simpa only [ho, sb_src_false] using hsources (SideGeometry.opposite (h3_evenSide k)),
      by simpa only [hr, sb_src_true] using hsources (h3_evenSide k)⟩

lemma h3_group_dirty_sides :
    SideGeometry.side (h3_evenSide 4) = SideGeometry.mask 200 ∧
    SideGeometry.side (SideGeometry.opposite (h3_evenSide 4)) = SideGeometry.mask 772 := by
  decide +kernel

lemma h3_first_four_groups_pure : ∀ k : Fin 5, k.val < 4 →
    ∀ a ∈ SideGeometry.side (h3_evenSide k),
      ∀ b ∈ SideGeometry.side (SideGeometry.opposite (h3_evenSide k)), petersenAdj a b := by
  unfold h3_evenSide SideGeometry.side SideGeometry.opposite SideGeometry.mask petersenAdj
  decide +kernel

lemma h3_tight_five_gates_exist {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hB : Bplus 10 D = (eligSet 10 D).card) :
    ∃ (r : Fin 10 → ℕ × Bool) (gate : Fin 5 → ℕ),
      Function.Injective r ∧ Function.Injective gate ∧
      (∀ k, gate k = (r (h3_evenSide k)).1) ∧
      (∀ i, r (SideGeometry.opposite i) = ((r i).1, !(r i).2)) ∧
      (∀ i, supp 10 D (src D (r i)) = SideGeometry.side i) ∧
      (∀ x : Fin 10, exitArcs 10 D (carrierT 10 D {x}) =
        (Finset.univ.filter (fun i : Fin 10 => x ∈ SideGeometry.side i)).image r) ∧
      (∀ k, gate k < D.length ∧ tag D (gate k) = true ∧ supp 10 D (10 + gate k) = ∅) ∧
      (∀ k,
        (supp 10 D (opA D (gate k)) = SideGeometry.side (h3_evenSide k) ∧
          supp 10 D (opB D (gate k)) = SideGeometry.side (SideGeometry.opposite (h3_evenSide k))) ∨
        (supp 10 D (opA D (gate k)) = SideGeometry.side (SideGeometry.opposite (h3_evenSide k)) ∧
          supp 10 D (opB D (gate k)) = SideGeometry.side (h3_evenSide k))) ∧
      ∀ j, j < D.length → tag D j = true →
        (∃ k, j = gate k) ∨ (supp 10 D (opA D j) = ∅ ∧ supp 10 D (opB D j) = ∅) := by
  obtain ⟨r, hinj, hopp, hsources, hW, hvalid, _, htypes⟩ :=
    h3_tight_typed_sources_exist h hC hz hB
  refine ⟨r, h3_groupGate r, hinj, h3_groupGate_injective r hinj hopp,
    fun _ => rfl, hopp, hsources, hW, ?_, h3_group_supports r hopp hsources, ?_⟩
  · intro k
    exact hvalid (h3_evenSide k)
  · intro j hj ht
    rcases htypes j hj ht with ⟨i, hi, _, _⟩ | hzero
    · left
      obtain ⟨k, hk⟩ := h3_side_gate_is_group r hopp i
      exact ⟨k, by simpa only [hi] using hk⟩
    · exact Or.inr hzero

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

lemma h3_or_path_true (hS : Strict n D) {a b : ℕ}
    (hp : Relation.ReflTransGen (h3_OrStep n D) a b) (z : Fin n → Bool)
    (ha : val D z a = true) : val D z b = true := by
  induction hp with
  | refl => exact ha
  | @tail b c hab hbc ih =>
    obtain ⟨hc, hnc, hop⟩ := hbc.1
    have he : n + (c - n) = c := by omega
    have hval := val_gate hS z (c - n) (by omega)
    rw [he, hbc.2] at hval
    rw [hval]
    change val D z (opA D (c - n)) || val D z (opB D (c - n)) = true
    rcases hop with hA | hB
    · rw [hA, ih]
      simp
    · rw [hB, ih]
      simp



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

noncomputable def h3_terminalPorts (D : Dag) (r : Fin 10 → ℕ × Bool) (w : ℕ) : Finset (Fin 10) :=
  by classical exact Finset.univ.filter (fun i => Relation.ReflTransGen (h3_OrStep 10 D) w (src D (r i)))


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

namespace S18Profile

open DagTools

def side (i : Fin 12) : Finset (Fin 10) :=
  Finset.univ.filter (fun x =>
    (([0, 2, 1, 50, 16, 520, 18, 68, 32, 384, 200, 772] : List Nat).getD i.val 0).testBit x.val = true)

def opposite (i : Fin 12) : Fin 12 :=
  ⟨(([1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10] : List Nat).getD i.val 0) % 12,
    Nat.mod_lt _ (by decide)⟩

def incidence (x : Fin 10) : Nat :=
  if x = 0 then 1 else if x = 1 ∨ x = 4 then 3 else 2

lemma paired_disjoint : ∀ i : Fin 12, Disjoint (side i) (side (opposite i)) := by
  decide +kernel

lemma incidence_card : ∀ x : Fin 10,
    (Finset.univ.filter (fun i : Fin 12 => x ∈ side i)).card = incidence x := by
  decide +kernel

def known (r : Fin 12 → Nat × Bool) (x : Fin 10) : Finset (Nat × Bool) :=
  (Finset.univ.filter (fun i : Fin 12 => x ∈ side i)).image r

lemma known_card (r : Fin 12 → Nat × Bool) (hinj : Function.Injective r) (x : Fin 10) :
    (known r x).card = incidence x := by
  rw [known, Finset.card_image_of_injective _ hinj, incidence_card]

lemma indexed_output_empty {D : Dag} (hS : Strict 10 D)
    (r : Fin 12 → Nat × Bool)
    (hvalid : ∀ i, (r i).1 < D.length ∧ tag D (r i).1 = true)
    (hopp : ∀ i, r (opposite i) = ((r i).1, !(r i).2))
    (hsrc : ∀ i, supp 10 D (src D (r i)) = side i) (i : Fin 12) :
    supp 10 D (10 + (r i).1) = ∅ := by
  have ha := hsrc i
  have hb := hsrc (opposite i)
  rw [hopp] at hb
  rw [sem_supp_and hS (hvalid i).1 (hvalid i).2]
  cases hs : (r i).2
  · have hA : supp 10 D (opA D (r i).1) = side i := by simpa [src, hs] using ha
    have hB : supp 10 D (opB D (r i).1) = side (opposite i) := by simpa [src, hs] using hb
    rw [hA, hB]
    exact Finset.disjoint_iff_inter_eq_empty.mp (paired_disjoint i)
  · have hA : supp 10 D (opA D (r i).1) = side (opposite i) := by simpa [src, hs] using hb
    have hB : supp 10 D (opB D (r i).1) = side i := by simpa [src, hs] using ha
    rw [hA, hB]
    exact Finset.disjoint_iff_inter_eq_empty.mp (paired_disjoint i).symm

lemma known_subset {D : Dag} (hS : Strict 10 D)
    (r : Fin 12 → Nat × Bool)
    (hvalid : ∀ i, (r i).1 < D.length ∧ tag D (r i).1 = true)
    (hopp : ∀ i, r (opposite i) = ((r i).1, !(r i).2))
    (hsrc : ∀ i, supp 10 D (src D (r i)) = side i) (x : Fin 10) :
    known r x ⊆ exitArcs 10 D (carrierT 10 D {x}) := by
  intro e he
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
  apply sem_mem_exit1.mpr
  refine ⟨(hvalid i).1, ?_, ?_⟩
  · rw [hsrc i]
    exact (Finset.mem_filter.mp hi).2
  · rw [indexed_output_empty hS r hvalid hopp hsrc i]
    simp

lemma profile_flow_no_merges {D : Dag} (hS : Strict 10 D)
    (r : Fin 12 → Nat × Bool) (hinj : Function.Injective r)
    (hvalid : ∀ i, (r i).1 < D.length ∧ tag D (r i).1 = true)
    (hopp : ∀ i, r (opposite i) = ((r i).1, !(r i).2))
    (hsrc : ∀ i, supp 10 D (src D (r i)) = side i)
    (hupper : ∀ x : Fin 10,
      (exitArcs 10 D (carrierT 10 D {x})).card +
        (merges 10 D (carrierT 10 D {x})).card ≤ incidence x) :
    (∀ x : Fin 10, merges 10 D (carrierT 10 D {x}) = ∅) ∧
    (∀ x : Fin 10, exitArcs 10 D (carrierT 10 D {x}) = known r x) ∧
    (∀ j, j < D.length → tag D j = true → (∀ i, (r i).1 ≠ j) →
      supp 10 D (opA D j) = ∅ ∧ supp 10 D (opB D j) = ∅) := by
  have hlo (x : Fin 10) : incidence x ≤ (exitArcs 10 D (carrierT 10 D {x})).card := by
    rw [← known_card r hinj x]
    exact Finset.card_le_card (known_subset hS r hvalid hopp hsrc x)
  have hM (x : Fin 10) : merges 10 D (carrierT 10 D {x}) = ∅ := by
    apply Finset.card_eq_zero.mp
    have := hlo x
    have := hupper x
    omega
  have hW (x : Fin 10) : exitArcs 10 D (carrierT 10 D {x}) = known r x := by
    apply (Finset.eq_of_subset_of_card_le (known_subset hS r hvalid hopp hsrc x) ?_).symm
    rw [known_card r hinj x]
    have := hupper x
    omega
  refine ⟨hM, hW, ?_⟩
  intro j hj ht hnot
  have hout : supp 10 D (10 + j) = ∅ := by
    rw [sem_supp_and hS hj ht]
    exact Finset.disjoint_iff_inter_eq_empty.mp (h3_no_merges_inputs_disjoint hS hM hj)
  have hnone (s : Bool) : ¬ (supp 10 D (src D (j, s))).Nonempty := by
    rintro ⟨x, hx⟩
    have he : (j, s) ∈ exitArcs 10 D (carrierT 10 D {x}) :=
      sem_mem_exit1.mpr ⟨hj, hx, by rw [hout]; simp⟩
    rw [hW x] at he
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp he
    exact hnot i (congrArg Prod.fst hi)
  constructor
  · exact Finset.not_nonempty_iff_eq_empty.mp (by simpa only [sb_src_false] using hnone false)
  · exact Finset.not_nonempty_iff_eq_empty.mp (by simpa only [sb_src_true] using hnone true)

lemma profile_residual_no_merges {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (b : Fin 10 → Nat) (hb : PureBranch 10 D b) (u : Σ _ : Nat, Nat)
    (hres : residualUnits 10 D b = {u}) (hsupp : supp 10 D u.1 ⊆ ({1, 4} : Finset (Fin 10)))
    (r : Fin 12 → Nat × Bool) (hinj : Function.Injective r)
    (hvalid : ∀ i, (r i).1 < D.length ∧ tag D (r i).1 = true)
    (hopp : ∀ i, r (opposite i) = ((r i).1, !(r i).2))
    (hsrc : ∀ i, supp 10 D (src D (r i)) = side i) :
    (∀ x : Fin 10, merges 10 D (carrierT 10 D {x}) = ∅) ∧
    (∀ x : Fin 10, exitArcs 10 D (carrierT 10 D {x}) = known r x) ∧
    (∀ j, j < D.length → tag D j = true → (∀ i, (r i).1 ≠ j) →
      supp 10 D (opA D j) = ∅ ∧ supp 10 D (opB D j) = ∅) := by
  apply profile_flow_no_merges h.1 r hinj hvalid hopp hsrc
  intro x
  have hf := h3_residual_singleton_flow petersen_graph_ok h hC b hb u hres x
  by_cases hx0 : x = 0
  · subst x
    have he : (0 : Fin 10) ∉ eligSet 10 D := (Finset.mem_sdiff.mp hz).2
    have hr : (0 : Fin 10) ∉ supp 10 D u.1 := by
      intro hx
      have := hsupp hx
      simp at this
    simpa [incidence, he, hr] using hf.le
  · by_cases hx : x = 1 ∨ x = 4
    · simp [incidence, hx0, hx]
      split_ifs at hf <;> omega
    · have hr : x ∉ supp 10 D u.1 := by
        intro hy
        have := hsupp hy
        exact hx (by simpa only [Finset.mem_insert, Finset.mem_singleton] using this)
      simp [incidence, hx0, hx]
      simp only [if_neg hr] at hf
      split_ifs at hf <;> omega

end S18Profile

namespace S18Profile

lemma common_side_one_four : ∀ i : Fin 12,
    (1 ∈ side i ∧ 4 ∈ side i) ↔ i = 3 ∨ i = 6 := by
  decide +kernel

lemma known_common_one_four (r : Fin 12 → Nat × Bool)
    (hinj : Function.Injective r) {e : Nat × Bool}
    (h1 : e ∈ known r 1) (h4 : e ∈ known r 4) :
    e = r 3 ∨ e = r 6 := by
  obtain ⟨i, hi, hie⟩ := Finset.mem_image.mp h1
  obtain ⟨j, hj, hje⟩ := Finset.mem_image.mp h4
  have hij : i = j := hinj (hie.trans hje.symm)
  have hi1 : (1 : Fin 10) ∈ side i := (Finset.mem_filter.mp hi).2
  have hi4 : (4 : Fin 10) ∈ side i := by
    simpa only [hij] using (Finset.mem_filter.mp hj).2
  rcases (common_side_one_four i).mp ⟨hi1, hi4⟩ with hi3 | hi6
  · exact Or.inl (by simpa only [hi3] using hie.symm)
  · exact Or.inr (by simpa only [hi6] using hie.symm)

lemma common_terminal_support_inter (r : Fin 12 → Nat × Bool)
    (hinj : Function.Injective r) (support : Nat × Bool → Finset (Fin 10))
    (hsrc : ∀ i, support (r i) = side i) {P Q : Nat × Bool}
    (hP1 : P ∈ known r 1) (hP4 : P ∈ known r 4)
    (hQ1 : Q ∈ known r 1) (hQ4 : Q ∈ known r 4)
    (hPQ : P.1 ≠ Q.1) :
    support P ∩ support Q = {1, 4} := by
  rcases known_common_one_four r hinj hP1 hP4 with hP | hP <;>
    rcases known_common_one_four r hinj hQ1 hQ4 with hQ | hQ
  · exact False.elim (hPQ (by rw [hP, hQ]))
  · rw [hP, hQ, hsrc 3, hsrc 6]
    decide +kernel
  · rw [hP, hQ, hsrc 6, hsrc 3]
    decide +kernel
  · exact False.elim (hPQ (by rw [hP, hQ]))

end S18Profile

namespace S18Profile

open DagTools

lemma profile_budget_no_merges {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hone : Bplus 10 D = (eligSet 10 D).card + 1)
    (r : Fin 12 → Nat × Bool) (hinj : Function.Injective r)
    (hvalid : ∀ i, (r i).1 < D.length ∧ tag D (r i).1 = true)
    (hopp : ∀ i, r (opposite i) = ((r i).1, !(r i).2))
    (hsrc : ∀ i, supp 10 D (src D (r i)) = side i) :
    (∀ x : Fin 10, merges 10 D (carrierT 10 D {x}) = ∅) ∧
    (∀ x : Fin 10, exitArcs 10 D (carrierT 10 D {x}) = known r x) ∧
    (∀ j, j < D.length → tag D j = true → (∀ i, (r i).1 ≠ j) →
      supp 10 D (opA D j) = ∅ ∧ supp 10 D (opB D j) = ∅) := by
  obtain ⟨b, hb⟩ := sem_exists_minBranch petersen_graph_ok h.1 hC
  have hbp := sem_minBranch_pure hb
  have hlo (x : Fin 10) : incidence x ≤ (sem_W 10 D x).card := by
    change incidence x ≤ (exitArcs 10 D (carrierT 10 D {x})).card
    rw [← known_card r hinj x]
    exact Finset.card_le_card (known_subset h.1 r hvalid hopp hsrc x)
  have hsat : ∀ x ∈ ({1, 4} : Finset (Fin 10)), 3 ≤ (sem_W 10 D x).card := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · simpa [incidence] using hlo 1
    · have hx4 := Finset.mem_singleton.mp hx
      subst x
      simpa [incidence] using hlo 4
  obtain ⟨u, P, Q, hres, hPQ, hterms, _, _, hsub⟩ :=
    h3_common_terminals_actual_paths petersen_graph_ok h hC b hb hone
      ({1, 4} : Finset (Fin 10)) (by decide) hsat
  have hWeq (x : Fin 10) (hx : x ∈ ({1, 4} : Finset (Fin 10))) :
      exitArcs 10 D (carrierT 10 D {x}) = known r x := by
    have hc := (sem_saturated petersen_graph_ok h hC b hbp hres (hsat x hx)).1
    change (exitArcs 10 D (carrierT 10 D {x})).card = 3 at hc
    have hi : incidence x = 3 := by
      rcases Finset.mem_insert.mp hx with rfl | hx
      · decide
      · have hx4 := Finset.mem_singleton.mp hx
        subst x
        decide
    apply (Finset.eq_of_subset_of_card_le (known_subset h.1 r hvalid hopp hsrc x) ?_).symm
    rw [known_card r hinj x, hc, hi]
  have hP1 : P ∈ known r 1 := by
    rw [← hWeq 1 (by decide)]
    exact (hterms 1 (by decide)).1
  have hP4 : P ∈ known r 4 := by
    rw [← hWeq 4 (by decide)]
    exact (hterms 4 (by decide)).1
  have hQ1 : Q ∈ known r 1 := by
    rw [← hWeq 1 (by decide)]
    exact (hterms 1 (by decide)).2
  have hQ4 : Q ∈ known r 4 := by
    rw [← hWeq 4 (by decide)]
    exact (hterms 4 (by decide)).2
  have hinter := common_terminal_support_inter r hinj
    (fun e => supp 10 D (src D e)) hsrc hP1 hP4 hQ1 hQ4 hPQ
  have hsupp : supp 10 D u.1 ⊆ ({1, 4} : Finset (Fin 10)) := by
    rw [hinter] at hsub
    exact hsub
  exact profile_residual_no_merges h hC hz b hbp u hres hsupp r hinj hvalid hopp hsrc

end S18Profile

namespace S18Profile

open DagTools

def representative (k : Fin 6) : Fin 12 :=
  ⟨(([2, 6, 4, 8, 0, 10] : List Nat).getD k.val 0) % 12,
    Nat.mod_lt _ (by decide)⟩

def gateIds (r : Fin 12 → Nat × Bool) (k : Fin 6) : Nat :=
  (r (representative k)).1

def left (k : Fin 6) : Finset (Fin 10) :=
  SideGeometry.mask (([1, 18, 16, 32, 0, 200] : List Nat).getD k.val 0)

def right (k : Fin 6) : Finset (Fin 10) :=
  SideGeometry.mask (([50, 68, 520, 384, 2, 772] : List Nat).getD k.val 0)

lemma representative_injective : Function.Injective representative := by decide +kernel

lemma representative_not_opposite :
    ∀ i j : Fin 6, representative i ≠ opposite (representative j) := by decide +kernel

lemma representative_covers : ∀ i : Fin 12,
    ∃ k : Fin 6, i = representative k ∨ i = opposite (representative k) := by decide +kernel

lemma left_eq_side : ∀ k : Fin 6, left k = side (representative k) := by decide +kernel

lemma right_eq_side : ∀ k : Fin 6, right k = side (opposite (representative k)) := by decide +kernel

lemma gateIds_injective (r : Fin 12 → Nat × Bool) (hinj : Function.Injective r)
    (hopp : ∀ i, r (opposite i) = ((r i).1, !(r i).2)) : Function.Injective (gateIds r) := by
  intro i j he
  change (r (representative i)).1 = (r (representative j)).1 at he
  by_cases hs : (r (representative i)).2 = (r (representative j)).2
  · exact representative_injective (hinj (Prod.ext he hs))
  · have hb : (r (representative i)).2 = !(r (representative j)).2 := by
      cases hi : (r (representative i)).2 <;>
        cases hj : (r (representative j)).2 <;> simp_all
    have hr : r (representative i) = r (opposite (representative j)) := by
      rw [hopp]
      exact Prod.ext he hb
    exact False.elim (representative_not_opposite i j (hinj hr))

lemma gateIds_sources {D : Dag} (r : Fin 12 → Nat × Bool)
    (hopp : ∀ i, r (opposite i) = ((r i).1, !(r i).2))
    (hsrc : ∀ i, supp 10 D (src D (r i)) = side i) (k : Fin 6) :
    (supp 10 D (opA D (gateIds r k)) = left k ∧
      supp 10 D (opB D (gateIds r k)) = right k) ∨
    (supp 10 D (opA D (gateIds r k)) = right k ∧
      supp 10 D (opB D (gateIds r k)) = left k) := by
  have ha := hsrc (representative k)
  have hb := hsrc (opposite (representative k))
  rw [hopp] at hb
  rw [left_eq_side, right_eq_side]
  cases hs : (r (representative k)).2
  · exact Or.inl ⟨by simpa [src, hs, gateIds] using ha,
      by simpa [src, hs, gateIds] using hb⟩
  · exact Or.inr ⟨by simpa [src, hs, gateIds] using hb,
      by simpa [src, hs, gateIds] using ha⟩

lemma profile_typed_six_gates {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hone : Bplus 10 D = (eligSet 10 D).card + 1)
    (r : Fin 12 → Nat × Bool) (hinj : Function.Injective r)
    (hvalid : ∀ i, (r i).1 < D.length ∧ tag D (r i).1 = true)
    (hopp : ∀ i, r (opposite i) = ((r i).1, !(r i).2))
    (hsrc : ∀ i, supp 10 D (src D (r i)) = side i) :
    Function.Injective (gateIds r) ∧
    (∀ k, gateIds r k < D.length ∧ tag D (gateIds r k) = true) ∧
    (∀ k,
      (supp 10 D (opA D (gateIds r k)) = left k ∧
        supp 10 D (opB D (gateIds r k)) = right k) ∨
      (supp 10 D (opA D (gateIds r k)) = right k ∧
        supp 10 D (opB D (gateIds r k)) = left k)) ∧
    (∀ j, j < D.length → tag D j = true →
      (∃ k : Fin 6, j = gateIds r k) ∨
      (supp 10 D (opA D j) = ∅ ∧ supp 10 D (opB D j) = ∅)) := by
  refine ⟨gateIds_injective r hinj hopp, fun k => hvalid (representative k),
    gateIds_sources r hopp hsrc, ?_⟩
  intro j hj ht
  by_cases hex : ∃ k : Fin 6, j = gateIds r k
  · exact Or.inl hex
  · apply Or.inr
    apply (profile_budget_no_merges h hC hz hone r hinj hvalid hopp hsrc).2.2 j hj ht
    intro i hi
    obtain ⟨k, hk | hk⟩ := representative_covers i
    · apply hex
      exact ⟨k, by simpa only [hk, gateIds] using hi.symm⟩
    · apply hex
      refine ⟨k, ?_⟩
      rw [hk, hopp] at hi
      exact hi.symm

end S18Profile

end S18Structural

namespace S18Structural.DagTools

lemma h3_out_empty {D : Dag} (hC : sem_Comp 10 petersenAdj D) :
    supp 10 D (outW 10 D) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  have hh := (hC (single v)).mp (mem_supp.mp hv)
  have hf : ∀ v : Fin 10, ¬ sem_Edge petersenAdj (single v) := by
    unfold sem_Edge petersenAdj single
    decide +kernel
  exact hf v hh

lemma h3_six_rows : ∀ r : Fin 6,
    decide (3 ≤ r.val) = true ↔
    sem_Edge petersenAdj (PEqualNP.Outside.L_meta_2590.OnceGeometry.rowInput r) := by
  unfold PEqualNP.Outside.L_meta_2590.OnceGeometry.rowInput
    PEqualNP.Outside.L_meta_2590.OnceGeometry.rowSet sem_Edge petersenAdj
  decide +kernel

lemma h3_output_mask {D : Dag} (hC : sem_Comp 10 petersenAdj D) :
    PEqualNP.Outside.L_meta_2590.OnceGeometry.wireMask D (outW 10 D) = 56 := by
  have hh : (fun r => val D (PEqualNP.Outside.L_meta_2590.OnceGeometry.rowInput r) (outW 10 D)) =
      (fun r : Fin 6 => decide (3 ≤ r.val)) := by
    funext r
    apply Bool.eq_iff_iff.mpr
    exact (hC _).trans (h3_six_rows r).symm
  change PEqualNP.Outside.L_meta_2590.OnceGeometry.mask
    (fun r => val D (PEqualNP.Outside.L_meta_2590.OnceGeometry.rowInput r) (outW 10 D)) = 56
  rw [hh]
  decide +kernel

end S18Structural.DagTools

namespace S18Structural.S18Profile

open DagTools

lemma exported_ports : ∀ g : Fin 5,
    left (PEqualNP.Outside.L_meta_2590.S18ActualLabels.firstFive g) =
      PEqualNP.Outside.L_meta_2590.S18Geometry.port g false ∧
    right (PEqualNP.Outside.L_meta_2590.S18ActualLabels.firstFive g) =
      PEqualNP.Outside.L_meta_2590.S18Geometry.port g true := by decide +kernel

lemma exported_dirty :
    left 5 = PEqualNP.Outside.L_meta_2590.FiveGroup.DAGBridge.DirtyA ∧
    right 5 = PEqualNP.Outside.L_meta_2590.FiveGroup.DAGBridge.DirtyB := by decide +kernel

lemma profile_bzero_zero_exclusion {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hone : Bplus 10 D = (eligSet 10 D).card + 1) (hB : Bzero 10 D = 0)
    (r : Fin 12 → Nat × Bool) (hinj : Function.Injective r)
    (hvalid : ∀ i, (r i).1 < D.length ∧ tag D (r i).1 = true)
    (hopp : ∀ i, r (opposite i) = ((r i).1, !(r i).2))
    (hsrc : ∀ i, supp 10 D (src D (r i)) = side i) : False := by
  obtain ⟨hginj, hgv, hps, htypes⟩ := profile_typed_six_gates h hC hz hone r hinj hvalid hopp hsrc
  have hp : ∀ g : Fin 5,
      (supp 10 D (opA D (gateIds r (PEqualNP.Outside.L_meta_2590.S18ActualLabels.firstFive g))) =
          PEqualNP.Outside.L_meta_2590.S18Geometry.port g false ∧
       supp 10 D (opB D (gateIds r (PEqualNP.Outside.L_meta_2590.S18ActualLabels.firstFive g))) =
          PEqualNP.Outside.L_meta_2590.S18Geometry.port g true) ∨
      (supp 10 D (opA D (gateIds r (PEqualNP.Outside.L_meta_2590.S18ActualLabels.firstFive g))) =
          PEqualNP.Outside.L_meta_2590.S18Geometry.port g true ∧
       supp 10 D (opB D (gateIds r (PEqualNP.Outside.L_meta_2590.S18ActualLabels.firstFive g))) =
          PEqualNP.Outside.L_meta_2590.S18Geometry.port g false) := by
    intro g
    simpa only [(exported_ports g).1, (exported_ports g).2] using
      hps (PEqualNP.Outside.L_meta_2590.S18ActualLabels.firstFive g)
  have hd : PEqualNP.Outside.L_meta_2590.FiveGroup.DAGBridge.DirtySides D (gateIds r 5) := by
    change (supp 10 D (opA D (gateIds r 5)) =
        PEqualNP.Outside.L_meta_2590.FiveGroup.DAGBridge.DirtyA ∧
      supp 10 D (opB D (gateIds r 5)) =
        PEqualNP.Outside.L_meta_2590.FiveGroup.DAGBridge.DirtyB) ∨
      (supp 10 D (opA D (gateIds r 5)) =
        PEqualNP.Outside.L_meta_2590.FiveGroup.DAGBridge.DirtyB ∧
      supp 10 D (opB D (gateIds r 5)) =
        PEqualNP.Outside.L_meta_2590.FiveGroup.DAGBridge.DirtyA)
    simpa only [exported_dirty.1, exported_dirty.2] using hps 5
  exact PEqualNP.Outside.L_meta_2590.S18ActualLabels.six_gate_target_exclusion
    h.1 hB hginj hgv hp hd htypes ⟨h3_out_empty hC, h3_output_mask hC⟩

end S18Structural.S18Profile

end PEqualNP.Outside.L_meta_2590
