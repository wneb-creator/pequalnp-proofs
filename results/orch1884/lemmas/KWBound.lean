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
lemma certificate : ∀ v : Fin 10, ∀ A ∈ (inc v).powerset, cap v A ≤ 2 := by
  decide +kernel

set_option maxRecDepth 10000 in
lemma total : rect univ univ = 40 := by decide +kernel

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

end PEqualNP.Outside.L_meta_1884.KW
