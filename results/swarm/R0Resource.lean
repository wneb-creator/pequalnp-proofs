import PEqualNP.Defs
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.BitVec
import Mathlib.Tactic.FinCases

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
    w ∈ (inner n D).filter (fun u => ¬(supp n D u).Nonempty) := by
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
    w ∈ (inner n D).filter (fun u => ¬(supp n D u).Nonempty) := by
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
      (inner n D).filter (fun u => ¬(supp n D u).Nonempty) := by
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

end PEqualNP.Outside.L_meta_2590
