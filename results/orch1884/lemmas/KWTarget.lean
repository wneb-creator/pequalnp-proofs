import PEqualNP.Defs

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

def petersen (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
    x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

lemma positive_rows : ∀ i : Fin 15, petersen (pos i) = true := by decide
lemma negative_rows : ∀ j : Fin 15, petersen (neg j) = false := by decide

lemma petersen_twenty_leaves (f : PEqualNP.MetaComplexity.DMFormula 10)
    (hf : positive f) (correct : ∀ x : Fin 10 → Bool, f.eval x = petersen x) :
    20 ≤ f.leaves := by
  exact twenty_leaves f hf
    (fun i => (correct (pos i)).trans (positive_rows i))
    (fun j => (correct (neg j)).trans (negative_rows j))

end PEqualNP.Outside.L_meta_1884.KW
