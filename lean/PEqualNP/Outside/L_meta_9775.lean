import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9775.CircuitHarness

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edges : List (Fin 14 × Fin 14) := [(0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]

def postedEdges : List (Nat × Nat) := [(0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]

def target (x : Fin 14 → Bool) : Bool := edges.any (fun e => x e.1 && x e.2)

lemma edge_iff : ∀ u v : Fin 14, (u, v) ∈ edges ↔ (u.val, v.val) ∈ postedEdges := by decide

lemma target_spec (x : Fin 14 → Bool) : target x = true ↔
    ∃ u v : Fin 14, (u.val, v.val) ∈ postedEdges ∧ x u = true ∧ x v = true := by
  simp only [target, List.any_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨⟨u, v⟩, he, hu, hv⟩
    exact ⟨u, v, (edge_iff u v).mp he, hu, hv⟩
  · rintro ⟨u, v, he, hu, hv⟩
    exact ⟨(u, v), (edge_iff u v).mpr he, hu, hv⟩

theorem validated (C : Circuit) (hm : Monotone2 C) (hs : C.size ≤ 24)
    (hc : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = target x) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 24 ∧
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin 14, (u.val, v.val) ∈ postedEdges ∧ x u = true ∧ x v = true) := by
  refine ⟨C, hm, hs, ?_⟩
  intro x
  rw [hc x]
  exact target_spec x

def baseline : Circuit :=
  ⟨[⟨.or, [8, 10]⟩,
    ⟨.and, [0, 14]⟩,
    ⟨.or, [7, 9]⟩,
    ⟨.or, [16, 13]⟩,
    ⟨.and, [1, 17]⟩,
    ⟨.or, [8, 13]⟩,
    ⟨.and, [2, 19]⟩,
    ⟨.or, [7, 11]⟩,
    ⟨.or, [21, 12]⟩,
    ⟨.and, [3, 22]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.or, [24, 13]⟩,
    ⟨.and, [4, 25]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.or, [27, 12]⟩,
    ⟨.and, [5, 28]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.or, [30, 11]⟩,
    ⟨.and, [6, 31]⟩,
    ⟨.or, [15, 18]⟩,
    ⟨.or, [33, 20]⟩,
    ⟨.or, [34, 23]⟩,
    ⟨.or, [35, 26]⟩,
    ⟨.or, [36, 29]⟩,
    ⟨.or, [37, 32]⟩], 38⟩

lemma baseline_size : baseline.size = 25 := rfl

lemma baseline_monotone : Monotone2 baseline := by
  simp [Monotone2, baseline]

lemma and_or (a b c : Bool) : (a && (b || c)) = ((a && b) || (a && c)) := by
  cases a <;> cases b <;> cases c <;> rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma baseline_correct (x : Fin 14 → Bool) : baseline.eval (List.ofFn x) = target x := by
  simp [baseline, Circuit.eval, Circuit.wires, GateOp.eval, target, edges,
    List.getD_eq_getElem?_getD, and_or, Bool.or_assoc]

lemma baseline_spec (x : Fin 14 → Bool) : baseline.eval (List.ofFn x) = true ↔
    ∃ u v : Fin 14, (u.val, v.val) ∈ postedEdges ∧ x u = true ∧ x v = true := by
  rw [baseline_correct]
  exact target_spec x

end PEqualNP.Outside.L_meta_9775.CircuitHarness


namespace PEqualNP.Outside.L_meta_9775.KW

open Finset

def edges : List (Fin 14 × Fin 14) :=
  [(0,8), (0,10), (1,7), (1,9), (1,13), (2,8), (2,13), (3,7), (3,11), (3,12), (4,10), (4,11), (4,13), (5,9), (5,10), (5,12), (6,8), (6,9), (6,11)]
def negative : List Nat := [127, 245, 314, 432, 541, 792, 1102, 1290, 1548, 2087, 2213, 2338, 4183, 4309, 4370, 4757, 5008, 5190, 5316, 6151, 6789, 7174, 7426, 7812, 8297, 8417, 8488, 8713, 9288, 9992, 10401, 10656, 12481, 13504, 14977, 16256]
def weights : List (List Int) := [
  [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0],
  [0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 2, 0, 2, 0, 0, 0, 1, 0, 0, 0, -2, 0, 0, 0, 1, 0, 0],
  [0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, -1, 0, 0, 2, 0, 0, 0, -1, 0, 0],
  [0, 0, 2, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 1, 0, 0],
  [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0],
  [0, 0, -2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0],
  [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 2, 0, 0],
  [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, -2, 0, 0],
  [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0],
  [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, -1, 0, 1, 0, 0, 0, -1, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0],
  [0, 0, 2, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, -1, 0, 2, 0, 0, 2, 0, -1, 0, 2, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 2, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
  [0, 0, 0, 2, 0, 0, 0, 0, -2, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 2, 0, 0, -2, -2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0],
  [0, 0, 0, 0, 0, 2, 1, 0, 2, 0, 0, -2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
  [0, 0, 0, 0, 0, -2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0]
]
def wt (i : Fin 19) (j : Fin 36) : Int := (weights.getD i.val []).getD j.val 0
def pos (i : Fin 19) (v : Fin 14) : Bool :=
  decide (v = (edges.getD i.val (0,0)).1 ∨ v = (edges.getD i.val (0,0)).2)
def neg (j : Fin 36) (v : Fin 14) : Bool := (negative.getD j.val 0).testBit v.val
def inc (v : Fin 14) : Finset (Fin 19) := univ.filter (fun i => pos i v)
def cap (v : Fin 14) (A : Finset (Fin 19)) : Int :=
  ∑ j : Fin 36, if neg j v then 0 else max 0 (∑ i ∈ A, wt i j)
def rect (A : Finset (Fin 19)) (B : Finset (Fin 36)) : Int := ∑ j ∈ B, ∑ i ∈ A, wt i j
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma certificateSet (v : Fin 14) :
    ((inc v).powerset.filter (fun A => cap v A ≤ 4)) = (inc v).powerset := by
  fin_cases v <;> decide

lemma certificate (v : Fin 14) (A : Finset (Fin 19))
    (hA : A ∈ (inc v).powerset) : cap v A ≤ 4 := by
  have hm : A ∈ (inc v).powerset.filter (fun A => cap v A ≤ 4) := by
    rw [certificateSet]
    exact hA
  exact (mem_filter.mp hm).2

set_option maxRecDepth 10000 in
lemma total : rect univ univ = 104 := by decide

lemma rectangle_bound (v : Fin 14) (A : Finset (Fin 19)) (B : Finset (Fin 36))
    (hA : ∀ i ∈ A, pos i v = true) (hB : ∀ j ∈ B, neg j v = false) :
    rect A B ≤ 4 := by
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
    _ ≤ ∑ j : Fin 36, if neg j v then 0 else max 0 (∑ i ∈ A, wt i j) := by
      apply sum_le_sum_of_subset_of_nonneg (subset_univ B)
      intro j hj hn
      split <;> positivity

def positive : PEqualNP.MetaComplexity.DMFormula 14 → Prop
  | .lit _ b => b = true
  | .and a b => positive a ∧ positive b
  | .or a b => positive a ∧ positive b

lemma split_left (A : Finset (Fin 19)) (B : Finset (Fin 36)) (p : Fin 19 → Prop) [DecidablePred p] :
    rect (A.filter p) B + rect (A.filter (fun i => ¬ p i)) B = rect A B := by
  unfold rect
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro j hj
  exact sum_filter_add_sum_filter_not A p (fun i => wt i j)

lemma split_right (A : Finset (Fin 19)) (B : Finset (Fin 36)) (p : Fin 36 → Prop) [DecidablePred p] :
    rect A (B.filter p) + rect A (B.filter (fun j => ¬ p j)) = rect A B := by
  exact sum_filter_add_sum_filter_not B p (fun j => ∑ i ∈ A, wt i j)

lemma formula_bound (f : PEqualNP.MetaComplexity.DMFormula 14) (hf : positive f) :
    ∀ (A : Finset (Fin 19)) (B : Finset (Fin 36)),
    (∀ i ∈ A, f.eval (pos i) = true) →
    (∀ j ∈ B, f.eval (neg j) = false) →
    rect A B ≤ 4 * (f.leaves : Int) := by
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

lemma twentysix_leaves (f : PEqualNP.MetaComplexity.DMFormula 14) (hf : positive f)
    (hpos : ∀ i : Fin 19, f.eval (pos i) = true)
    (hneg : ∀ j : Fin 36, f.eval (neg j) = false) : 26 ≤ f.leaves := by
  have h := formula_bound f hf univ univ (fun i hi => hpos i) (fun j hj => hneg j)
  rw [total] at h
  omega


def target (x : Fin 14 → Bool) : Bool := edges.any (fun uv => x uv.1 && x uv.2)

set_option maxRecDepth 10000 in
lemma rows_correct : (∀ i : Fin 19,target (pos i)=true) ∧
    (∀ j : Fin 36,target (neg j)=false) := by decide

theorem formula_lower (f : PEqualNP.MetaComplexity.DMFormula 14) (hf : positive f)
    (correct : ∀ x,f.eval x=target x) : 26≤f.leaves := by
  apply twentysix_leaves f hf
  · intro i
    rw [correct]
    exact rows_correct.1 i
  · intro j
    rw [correct]
    exact rows_correct.2 j

end PEqualNP.Outside.L_meta_9775.KW
