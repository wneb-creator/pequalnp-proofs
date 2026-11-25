import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1884.InputEssentiality

open PEqualNP.CircuitLowerBounds

def target (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
    x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def neighbor : Fin 10 → Fin 10 := ![1, 2, 3, 4, 0, 0, 1, 2, 3, 4]

def singleton (v : Fin 10) : Fin 10 → Bool := fun j => decide (j = v)

def pair (v w : Fin 10) : Fin 10 → Bool := fun j => decide (j = v ∨ j = w)

lemma singleton_false : ∀ v : Fin 10, target (singleton v) = false := by decide

lemma neighbor_pair_true : ∀ v : Fin 10, target (pair v (neighbor v)) = true := by
  decide

lemma map_covers_nonzero (C : Circuit) (π : Fin 10 → Fin 10) (u : Bool → Bool)
    (hcomputes : ∀ x : Fin 10 → Bool,
      C.eval (List.ofFn (x ∘ π) ++ [u (x 0)]) = target x) :
    ∀ v : Fin 10, v ≠ 0 → ∃ i : Fin 10, π i = v := by
  classical
  intro v hv
  by_contra hmissing
  have hn : ∀ i, π i ≠ v := by simpa only [not_exists] using hmissing
  have hzero : (0 : Fin 10) ≠ v := Ne.symm hv
  have hcomp : pair v (neighbor v) ∘ π = singleton (neighbor v) ∘ π := by
    funext i
    simp [Function.comp_def, pair, singleton, hn i]
  have harg :
      List.ofFn (pair v (neighbor v) ∘ π) ++ [u (pair v (neighbor v) 0)] =
      List.ofFn (singleton (neighbor v) ∘ π) ++ [u (singleton (neighbor v) 0)] := by
    rw [hcomp]
    simp [pair, singleton, hzero]
  have heq := congrArg C.eval harg
  rw [hcomputes, hcomputes, neighbor_pair_true, singleton_false] at heq
  cases heq

lemma missing_nonzero_counterexample (C : Circuit) (π : Fin 10 → Fin 10)
    (u : Bool → Bool) (v : Fin 10) (hv : v ≠ 0) (hmissing : ∀ i, π i ≠ v) :
    ∃ x : Fin 10 → Bool, C.eval (List.ofFn (x ∘ π) ++ [u (x 0)]) ≠ target x := by
  classical
  by_contra h
  have hcomputes : ∀ x : Fin 10 → Bool,
      C.eval (List.ofFn (x ∘ π) ++ [u (x 0)]) = target x := by
    simpa only [not_exists, not_not] using h
  obtain ⟨i, hi⟩ := map_covers_nonzero C π u hcomputes v hv
  exact hmissing i hi

lemma map_surjective_of_zero (C : Circuit) (π : Fin 10 → Fin 10) (u : Bool → Bool)
    (hcomputes : ∀ x : Fin 10 → Bool,
      C.eval (List.ofFn (x ∘ π) ++ [u (x 0)]) = target x)
    (hzero : ∃ i : Fin 10, π i = 0) : Function.Surjective π := by
  intro v
  by_cases hv : v = 0
  · simpa only [hv] using hzero
  · exact map_covers_nonzero C π u hcomputes v hv

end PEqualNP.Outside.L_meta_1884.InputEssentiality

namespace PEqualNP.Outside.L_meta_1884.KW

open Finset

def edges : List (Fin 10 × Fin 10) :=
  [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
def negative : List Nat := [50,69,104,116,138,201,208,276,385,402,521,548,554,770,773]
def weights : List (List Int) := [
  [0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1],
  [0, 0, 0, 1, 0, 0, -1, 0, 0, 1, -1, 0, 1, 0, 1],
  [0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 1, 0, 1, 0, 1],
  [0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, -1],
  [0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, -1, -1, 1],
  [0, 1, 0, 1, 0, 1, 0, 0, 0, -1, 0, 0, 1, 0, 0],
  [0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, -1],
  [0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, -1, 0, 0],
  [0, 0, 0, -1, 0, 1, -1, 0, 0, 1, 0, 0, 1, 0, 1],
  [0, 0, 0, 1, 0, -1, 0, 1, 0, 0, 0, 0, 0, 1, 1],
  [0, -1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, -1, 0],
  [0, 0, 0, -1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0],
  [0, 0, 0, 1, -1, 1, 0, -1, 0, 0, 0, 0, 1, 0, 1],
  [0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, -1, 0, 1],
  [0, 0, 0, 1, 0, -1, 0, 0, 0, 1, 0, 0, 1, 1, 0]
]
def wt (i j : Fin 15) : Int := (weights.getD i.val []).getD j.val 0
def pos (i : Fin 15) (v : Fin 10) : Bool :=
  decide (v = (edges.getD i.val (0,0)).1 ∨ v = (edges.getD i.val (0,0)).2)
def neg (j : Fin 15) (v : Fin 10) : Bool := (negative.getD j.val 0).testBit v.val
def inc (v : Fin 10) : Finset (Fin 15) := univ.filter (fun i => pos i v)
def cap (v : Fin 10) (A : Finset (Fin 15)) : Int :=
  ∑ j : Fin 15, if neg j v then 0 else max 0 (∑ i ∈ A, wt i j)
def rect (A B : Finset (Fin 15)) : Int := ∑ j ∈ B, ∑ i ∈ A, wt i j

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma certificateSet (v : Fin 10) :
    ((inc v).powerset.filter (fun A => cap v A ≤ 2)) = (inc v).powerset := by
  fin_cases v <;> decide

lemma certificate (v : Fin 10) (A : Finset (Fin 15))
    (hA : A ∈ (inc v).powerset) : cap v A ≤ 2 := by
  have hm : A ∈ (inc v).powerset.filter (fun A => cap v A ≤ 2) := by
    rw [certificateSet]
    exact hA
  exact (mem_filter.mp hm).2

set_option maxRecDepth 10000 in
lemma total : rect univ univ = 40 := by decide

lemma rectangle_bound (v : Fin 10) (A B : Finset (Fin 15))
    (hA : ∀ i ∈ A, pos i v = true) (hB : ∀ j ∈ B, neg j v = false) :
    rect A B ≤ 2 := by
  have sub : A ⊆ inc v := by
    intro i hi
    exact mem_filter.mpr ⟨mem_univ i, hA i hi⟩
  apply le_trans (b := cap v A) _ (certificate v A (mem_powerset.mpr sub))
  unfold rect cap
  calc
    ∑ j ∈ B, ∑ i ∈ A, wt i j ≤
        ∑ j ∈ B, if neg j v then 0 else max 0 (∑ i ∈ A, wt i j) := by
      apply sum_le_sum
      intro j hj
      rw [hB j hj]
      exact le_max_right _ _
    _ ≤ ∑ j : Fin 15, if neg j v then 0 else max 0 (∑ i ∈ A, wt i j) := by
      apply sum_le_sum_of_subset_of_nonneg (subset_univ B)
      intro j hj hn
      split <;> positivity

def positive : PEqualNP.MetaComplexity.DMFormula 10 → Prop
  | .lit _ b => b = true
  | .and a b => positive a ∧ positive b
  | .or a b => positive a ∧ positive b

lemma split_left (A B : Finset (Fin 15)) (p : Fin 15 → Prop) [DecidablePred p] :
    rect (A.filter p) B + rect (A.filter (fun i => ¬ p i)) B = rect A B := by
  unfold rect
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro j hj
  exact sum_filter_add_sum_filter_not A p (fun i => wt i j)

lemma split_right (A B : Finset (Fin 15)) (p : Fin 15 → Prop) [DecidablePred p] :
    rect A (B.filter p) + rect A (B.filter (fun j => ¬ p j)) = rect A B := by
  exact sum_filter_add_sum_filter_not B p (fun j => ∑ i ∈ A, wt i j)

lemma formula_bound (f : PEqualNP.MetaComplexity.DMFormula 10) (hf : positive f) :
    ∀ (A B : Finset (Fin 15)),
    (∀ i ∈ A, f.eval (pos i) = true) →
    (∀ j ∈ B, f.eval (neg j) = false) →
    rect A B ≤ 2 * (f.leaves : Int) := by
  induction f with
  | lit v b =>
    have hb : b = true := hf
    subst b
    intro A B hA hB
    simpa only [PEqualNP.MetaComplexity.DMFormula.leaves, Nat.cast_one, mul_one] using
      rectangle_bound v A B hA hB
  | and a b iha ihb =>
    intro A B hA hB
    have hfa := iha hf.1 A (B.filter (fun j => a.eval (neg j) = false))
      (fun i hi => (by have hx := hA i hi; simp only [PEqualNP.MetaComplexity.DMFormula.eval, Bool.and_eq_true] at hx; exact hx.1))
      (fun j hj => (mem_filter.mp hj).2)
    have hfb := ihb hf.2 A (B.filter (fun j => ¬ a.eval (neg j) = false))
      (fun i hi => (by have hx := hA i hi; simp only [PEqualNP.MetaComplexity.DMFormula.eval, Bool.and_eq_true] at hx; exact hx.2))
      (by
        intro j hj
        have hx := hB j (mem_filter.mp hj).1
        have hn := (mem_filter.mp hj).2
        change (a.eval (neg j) && b.eval (neg j)) = false at hx
        cases ha : a.eval (neg j) <;> simp_all)
    have hs := split_right A B (fun j => a.eval (neg j) = false)
    simp only [PEqualNP.MetaComplexity.DMFormula.leaves, Nat.cast_add]
    linarith
  | or a b iha ihb =>
    intro A B hA hB
    have hfa := iha hf.1 (A.filter (fun i => a.eval (pos i) = true)) B
      (fun i hi => (mem_filter.mp hi).2)
      (fun j hj => (Bool.or_eq_false_iff.mp (hB j hj)).1)
    have hfb := ihb hf.2 (A.filter (fun i => ¬ a.eval (pos i) = true)) B
      (by
        intro i hi
        have hx := hA i (mem_filter.mp hi).1
        have hn := (mem_filter.mp hi).2
        change (a.eval (pos i) || b.eval (pos i)) = true at hx
        cases ha : a.eval (pos i) <;> simp_all)
      (fun j hj => (Bool.or_eq_false_iff.mp (hB j hj)).2)
    have hs := split_left A B (fun i => a.eval (pos i) = true)
    simp only [PEqualNP.MetaComplexity.DMFormula.leaves, Nat.cast_add]
    linarith

lemma twenty_leaves (f : PEqualNP.MetaComplexity.DMFormula 10) (hf : positive f)
    (hpos : ∀ i : Fin 15, f.eval (pos i) = true)
    (hneg : ∀ j : Fin 15, f.eval (neg j) = false) : 20 ≤ f.leaves := by
  have h := formula_bound f hf univ univ (fun i hi => hpos i) (fun j hj => hneg j)
  rw [total] at h
  omega

end PEqualNP.Outside.L_meta_1884.KW

namespace PEqualNP.Outside.L_meta_1884.SoleOrPartner

def target (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
    x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def singleton (v : Fin 10) : Fin 10 → Bool := fun j => decide (j = v)

def pair (v w : Fin 10) : Fin 10 → Bool := fun j => decide (j = v ∨ j = w)

def triple (v w u : Fin 10) : Fin 10 → Bool :=
  fun j => decide (j = v ∨ j = w ∨ j = u)

lemma witness : ∀ v : Fin 10, v ≠ 0 → ∀ w : Fin 10, w ≠ v →
    ∃ u : Fin 10, u ≠ 0 ∧ u ≠ v ∧ u ≠ w ∧
      target (pair w u) = false ∧ target (triple v w u) = true := by decide

lemma rejects_other_singleton (v : Fin 10) (hv : v ≠ 0)
    (H : (Fin 10 → Bool) → Bool)
    (hmono : ∀ x y : Fin 10 → Bool, x 0 = y 0 →
      (∀ i, x i = true → y i = true) → H x = true → H y = true)
    (hfactor : ∀ x y : Fin 10 → Bool,
      (∀ i, i ≠ v → x i = y i) →
      (x v || H x) = (y v || H y) → target x = target y)
    (w : Fin 10) (hw : w ≠ v) : H (singleton w) = false := by
  cases hh : H (singleton w)
  · rfl
  · obtain ⟨u, hu0, huv, huw, hnegative, hpositive⟩ := witness v hv w hw
    have hzero : singleton w 0 = pair w u 0 := by
      simp [singleton, pair, Ne.symm hu0]
    have hle : ∀ i, singleton w i = true → pair w u i = true := by
      intro i hi
      simp only [singleton, decide_eq_true_eq] at hi
      simp [pair, hi]
    have hp : H (pair w u) = true := hmono _ _ hzero hle hh
    have hagree : ∀ i, i ≠ v → pair w u i = triple v w u i := by
      intro i hi
      simp [pair, triple, hi]
    have hgate : (pair w u v || H (pair w u)) =
        (triple v w u v || H (triple v w u)) := by
      simp [hp, triple]
    have hbad := hfactor _ _ hagree hgate
    rw [hnegative, hpositive] at hbad
    cases hbad

lemma rejects_zero (v : Fin 10) (hv : v ≠ 0)
    (H : (Fin 10 → Bool) → Bool)
    (hmono : ∀ x y : Fin 10 → Bool, x 0 = y 0 →
      (∀ i, x i = true → y i = true) → H x = true → H y = true)
    (hfactor : ∀ x y : Fin 10 → Bool,
      (∀ i, i ≠ v → x i = y i) →
      (x v || H x) = (y v || H y) → target x = target y) :
    H (fun _ => false) = false := by
  have hex : ∀ v : Fin 10, ∃ w : Fin 10, w ≠ 0 ∧ w ≠ v := by decide
  obtain ⟨w, hw0, hwv⟩ := hex v
  have hreject := rejects_other_singleton v hv H hmono hfactor w hwv
  cases hh : H (fun _ => false)
  · rfl
  · have hzero : (false : Bool) = singleton w 0 := by
      simp [singleton, Ne.symm hw0]
    have hle : ∀ i : Fin 10, false = true → singleton w i = true := by
      simp
    have hbad := hmono (fun _ => false) (singleton w) hzero hle hh
    rw [hreject] at hbad
    cases hbad

lemma rejects_singleton (v : Fin 10) (hv : v ≠ 0)
    (H : (Fin 10 → Bool) → Bool)
    (hmono : ∀ x y : Fin 10 → Bool, x 0 = y 0 →
      (∀ i, x i = true → y i = true) → H x = true → H y = true)
    (hindependent : ∀ x y : Fin 10 → Bool,
      (∀ i, i ≠ v → x i = y i) → H x = H y)
    (hfactor : ∀ x y : Fin 10 → Bool,
      (∀ i, i ≠ v → x i = y i) →
      (x v || H x) = (y v || H y) → target x = target y)
    (w : Fin 10) : H (singleton w) = false := by
  by_cases hw : w = v
  · subst w
    have hagree : ∀ i : Fin 10, i ≠ v → singleton v i = false := by
      intro i hi
      simp [singleton, hi]
    rw [hindependent (singleton v) (fun _ => false) hagree]
    exact rejects_zero v hv H hmono hfactor
  · exact rejects_other_singleton v hv H hmono hfactor w hw


def quad (v w u z : Fin 10) : Fin 10 → Bool :=
  fun j => decide (j = v ∨ j = w ∨ j = u ∨ j = z)

def exceptional (v w u : Fin 10) : Prop :=
  (v = 1 ∧ ((w = 3 ∧ u = 9) ∨ (w = 9 ∧ u = 3) ∨
    (w = 7 ∧ u = 8) ∨ (w = 8 ∧ u = 7))) ∨
  (v = 4 ∧ ((w = 2 ∧ u = 6) ∨ (w = 6 ∧ u = 2) ∨
    (w = 7 ∧ u = 8) ∨ (w = 8 ∧ u = 7))) ∨
  (v = 5 ∧ ((w = 2 ∧ u = 6) ∨ (w = 6 ∧ u = 2) ∨
    (w = 3 ∧ u = 9) ∨ (w = 9 ∧ u = 3)))

lemma pair_witness : ∀ v : Fin 10, v ≠ 0 → ∀ w u : Fin 10,
    w ≠ u → w ≠ v → u ≠ v → target (pair w u) = false →
    exceptional v w u ∨ ∃ z : Fin 10, z ≠ 0 ∧ z ≠ v ∧
      target (triple w u z) = false ∧ target (quad v w u z) = true := by
  intro v
  fin_cases v <;> simp only [exceptional] <;> decide

lemma exceptional_zero : ∀ v w u : Fin 10, exceptional v w u →
    target (triple w u 0) = false ∧ target (quad v w u 0) = true := by
  intro v
  fin_cases v <;> simp only [exceptional] <;> decide

lemma localizes_nonedge_pair (v : Fin 10) (hv : v ≠ 0)
    (H : (Fin 10 → Bool) → Bool)
    (hmono : ∀ x y : Fin 10 → Bool, x 0 = y 0 →
      (∀ i, x i = true → y i = true) → H x = true → H y = true)
    (hindependent : ∀ x y : Fin 10 → Bool,
      (∀ i, i ≠ v → x i = y i) → H x = H y)
    (hfactor : ∀ x y : Fin 10 → Bool,
      (∀ i, i ≠ v → x i = y i) →
      (x v || H x) = (y v || H y) → target x = target y)
    (w u : Fin 10) (hnegative : target (pair w u) = false)
    (hh : H (pair w u) = true) : exceptional v w u := by
  have hsingle := rejects_singleton v hv H hmono hindependent hfactor
  have hwu : w ≠ u := by
    intro heq
    subst u
    have hp : pair w w = singleton w := by funext i; simp [pair, singleton]
    rw [hp, hsingle] at hh
    cases hh
  have hwv : w ≠ v := by
    intro heq
    subst w
    have hagree : ∀ i, i ≠ v → pair v u i = singleton u i := by
      intro i hi
      simp [pair, singleton, hi]
    rw [hindependent _ _ hagree, hsingle] at hh
    cases hh
  have huv : u ≠ v := by
    intro heq
    subst u
    have hagree : ∀ i, i ≠ v → pair w v i = singleton w i := by
      intro i hi
      simp [pair, singleton, hi]
    rw [hindependent _ _ hagree, hsingle] at hh
    cases hh
  rcases pair_witness v hv w u hwu hwv huv hnegative with hex | hother
  · exact hex
  · obtain ⟨z, hz0, hzv, hneg, hpos⟩ := hother
    have hzero : pair w u 0 = triple w u z 0 := by
      simp [pair, triple, Ne.symm hz0]
    have hle : ∀ i, pair w u i = true → triple w u z i = true := by
      intro i hi
      simp only [pair, decide_eq_true_eq] at hi
      rcases hi with hi | hi <;> simp [triple, hi]
    have hH : H (triple w u z) = true := hmono _ _ hzero hle hh
    have hagree : ∀ i, i ≠ v → triple w u z i = quad v w u z i := by
      intro i hi
      simp [triple, quad, hi]
    have hgate : (triple w u z v || H (triple w u z)) =
        (quad v w u z v || H (quad v w u z)) := by
      simp [hH, quad]
    have hbad := hfactor _ _ hagree hgate
    rw [hneg, hpos] at hbad
    cases hbad

lemma rejects_nonedge_zero_extension (v : Fin 10) (hv : v ≠ 0)
    (H : (Fin 10 → Bool) → Bool)
    (hmono : ∀ x y : Fin 10 → Bool, x 0 = y 0 →
      (∀ i, x i = true → y i = true) → H x = true → H y = true)
    (hindependent : ∀ x y : Fin 10 → Bool,
      (∀ i, i ≠ v → x i = y i) → H x = H y)
    (hfactor : ∀ x y : Fin 10 → Bool,
      (∀ i, i ≠ v → x i = y i) →
      (x v || H x) = (y v || H y) → target x = target y)
    (w u : Fin 10) (hnegative : target (pair w u) = false)
    (hh : H (pair w u) = true) : H (triple w u 0) = false := by
  have hex := localizes_nonedge_pair v hv H hmono hindependent hfactor w u hnegative hh
  obtain ⟨hneg, hpos⟩ := exceptional_zero v w u hex
  cases hH : H (triple w u 0)
  · rfl
  · have hagree : ∀ i, i ≠ v → triple w u 0 i = quad v w u 0 i := by
      intro i hi
      simp [triple, quad, hi]
    have hgate : (triple w u 0 v || H (triple w u 0)) =
        (quad v w u 0 v || H (quad v w u 0)) := by
      simp [hH, quad]
    have hbad := hfactor _ _ hagree hgate
    rw [hneg, hpos] at hbad
    cases hbad

end PEqualNP.Outside.L_meta_1884.SoleOrPartner
