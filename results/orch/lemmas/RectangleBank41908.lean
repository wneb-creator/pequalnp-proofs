import RectangleRunIndexed
import RectangleOrEdgeRun

namespace PEqualNP.Outside.L_meta_2373.RectangleBank41908

open Live1024

def raw (i : Fin 10) : Sig := RectangleOrEdgeRun.basis i.castSucc

def positiveSample (r : Fin 15) (i : Fin 10) : Bool := RectangleOrEdge.positiveSample r i.castSucc
def negativeSample (r : Fin 15) (i : Fin 10) : Bool := RectangleOrEdge.negativeSample r i.castSucc
def weight : Fin 15 → Fin 15 → Int := ![
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 3, 0, 0, 0, -3, 0, 0, 0, 2, 0, 0, 3],
  ![0, 0, 0, 3, 0, 6, 2, 3, 0, 0, 0, -2, 6, -2, -6],
  ![0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, -6, 0, 6],
  ![0, 0, 0, 0, 0, 4, 0, 0, -4, 0, 0, 0, 0, 0, 4],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 3, 0, -3],
  ![0, 0, 0, 2, 0, 0, 0, 6, 0, 0, 0, 0, -6, 0, 4],
  ![0, 0, 0, -3, 0, 3, 0, 3, 0, 0, 0, -2, 3, 2, 3],
  ![0, 0, 0, 2, 0, -8, 0, 4, 0, 6, 0, 2, 6, 2, 2],
  ![0, 0, 4, 2, 0, 4, 0, -2, 4, 0, 0, 0, 6, -2, -4],
  ![0, 0, -4, -2, 0, 6, 0, -4, 0, 6, 0, 0, 6, 2, 4],
  ![0, 0, 4, 2, 0, 6, 0, 0, 0, -6, 0, 0, 3, 0, 3],
  ![0, 0, 0, 3, 0, 3, 0, 0, 0, 3, 0, 0, -3, 0, 3],
  ![0, 0, 0, 1, 0, -4, 0, 2, 4, 0, 0, 2, 3, 2, 0]]
def costs : Fin 10 → Int := ![0, 0, 0, 8, 12, 8, 6, 12, 6, 12]
def positions : Fin 10 → Fin 3 → Fin 15 := ![
  ![0, 4, 5],
  ![0, 1, 6],
  ![1, 2, 7],
  ![2, 3, 8],
  ![3, 4, 9],
  ![5, 10, 14],
  ![6, 12, 13],
  ![7, 10, 11],
  ![8, 13, 14],
  ![9, 11, 12]]

def rect (S T : Finset (Fin 15)) : Int := ∑ r ∈ S, ∑ c ∈ T, weight r c

def negativeSet (i : Fin 10) : Finset (Fin 15) :=
  Finset.univ.filter (fun c => negativeSample c i = false)

def selected (i : Fin 10) (keep : Fin 3 → Bool) : Finset (Fin 15) :=
  (Finset.univ.filter (fun k => keep k = true)).image (positions i)

def maxRect (i : Fin 10) (S : Finset (Fin 15)) : Int :=
  ∑ c ∈ negativeSet i, max (∑ r ∈ S, weight r c) 0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma positions_cover : ∀ (i : Fin 10) (r : Fin 15),
    positiveSample r i = true ↔ ∃ k : Fin 3, positions i k = r := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma finite_rectangle_bound : ∀ (i : Fin 10) (keep : Fin 3 → Bool),
    maxRect i (selected i keep) ≤ costs i := by
  intro i
  fin_cases i <;> decide +kernel

lemma selected_covers (i : Fin 10) (S : Finset (Fin 15))
    (hs : ∀ r ∈ S, positiveSample r i = true) :
    selected i (fun k => decide (positions i k ∈ S)) = S := by
  ext r
  simp only [selected, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and, decide_eq_true_eq]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact hk
  · intro hr
    obtain ⟨k, hk⟩ := (positions_cover i r).mp (hs r hr)
    exact ⟨k, by simpa only [hk] using hr, hk⟩

lemma leaf_bound (i : Fin 10) (S T : Finset (Fin 15))
    (hs : ∀ r ∈ S, positiveSample r i = true)
    (ht : ∀ c ∈ T, negativeSample c i = false) : rect S T ≤ costs i := by
  have sub : T ⊆ negativeSet i := by
    intro c hc
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ c, ht c hc⟩
  calc
    rect S T = ∑ c ∈ T, ∑ r ∈ S, weight r c := by
      unfold rect
      rw [Finset.sum_comm]
    _ ≤ ∑ c ∈ T, max (∑ r ∈ S, weight r c) 0 :=
      Finset.sum_le_sum (fun _ _ => le_max_left _ _)
    _ ≤ maxRect i S := by
      exact Finset.sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => le_max_right _ _)
    _ ≤ costs i := by
      rw [← selected_covers i S hs]
      exact finite_rectangle_bound i _

lemma raw_bound (i : Fin 10) : RectangleRun.Bounds
    RectangleOrEdgeRun.positiveRows RectangleOrEdgeRun.negativeRows weight (observe (raw i)) (costs i) := by
  intro S T hs ht
  apply leaf_bound i S T
  · intro r hr
    change RectangleOrEdge.positiveSample r i.castSucc = true
    rw [← RectangleOrEdgeRun.positive_inputs]
    exact hs r hr
  · intro c hc
    change RectangleOrEdge.negativeSample c i.castSucc = false
    rw [← RectangleOrEdgeRun.negative_inputs]
    exact ht c hc

def labels : List (Fin 10) := [0, 0, 0, 1, 1, 2, 2, 2, 3, 3, 4, 5, 5, 6, 6, 7, 8, 8, 9, 9]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma full_weight : rect Finset.univ Finset.univ = 116 := by decide +kernel

lemma total_cost : (labels.map costs).sum = 104 := by decide +kernel

lemma bank_exclusion
    (trace : Run false (observe graph) 19 (labels.map (fun i => observe (raw i)))) : False := by
  have bounds := RectangleRun.tight_run_indexed
    RectangleOrEdgeRun.positiveRows RectangleOrEdgeRun.negativeRows weight
    (fun i => observe (raw i)) costs labels trace (by decide) (fun i _ => raw_bound i)
  have bound := bounds Finset.univ Finset.univ
    (fun r _ => RectangleOrEdgeRun.positive_graph r)
    (fun c _ => RectangleOrEdgeRun.negative_graph c)
  change rect Finset.univ Finset.univ ≤ (labels.map costs).sum at bound
  rw [full_weight, total_cost] at bound
  omega

end PEqualNP.Outside.L_meta_2373.RectangleBank41908
