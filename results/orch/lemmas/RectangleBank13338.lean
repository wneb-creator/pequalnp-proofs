import RectangleRunIndexed
import RectangleOrEdgeRun

namespace PEqualNP.Outside.L_meta_2373.RectangleBank13338

open Live1024

def raw (i : Fin 12) : Sig :=
  Fin.lastCases (bin 1 (inputs.getD 7 zero) (inputs.getD 8 zero)) RectangleOrEdgeRun.basis i

def positiveRows : Fin 15 → Row := fun r => Fin.ofNat 1024 (![3, 6, 12, 24, 17, 33, 66, 132, 264, 528, 160, 640, 576, 320, 288] r)
def negativeRows : Fin 15 → Row := fun r => Fin.ofNat 1024 (![50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773] r)
def positiveSample : Fin 15 → Fin 12 → Bool := ![![true, true, false, false, false, false, false, false, false, false, true, false], ![false, true, true, false, false, false, false, false, false, false, true, false], ![false, false, true, true, false, false, false, false, false, false, false, false], ![false, false, false, true, true, false, false, false, false, false, false, false], ![true, false, false, false, true, false, false, false, false, false, true, false], ![true, false, false, false, false, true, false, false, false, false, true, false], ![false, true, false, false, false, false, true, false, false, false, true, false], ![false, false, true, false, false, false, false, true, false, false, false, true], ![false, false, false, true, false, false, false, false, true, false, false, true], ![false, false, false, false, true, false, false, false, false, true, false, false], ![false, false, false, false, false, true, false, true, false, false, false, true], ![false, false, false, false, false, false, false, true, false, true, false, true], ![false, false, false, false, false, false, true, false, false, true, false, false], ![false, false, false, false, false, false, true, false, true, false, false, true], ![false, false, false, false, false, true, false, false, true, false, false, true]]
def negativeSample : Fin 15 → Fin 12 → Bool := ![![false, true, false, false, true, true, false, false, false, false, true, false], ![true, false, true, false, false, false, true, false, false, false, true, false], ![false, false, false, true, false, true, true, false, false, false, false, false], ![false, false, true, false, true, true, true, false, false, false, false, false], ![false, true, false, true, false, false, false, true, false, false, true, true], ![true, false, false, true, false, false, true, true, false, false, true, true], ![false, false, false, false, true, false, true, true, false, false, false, true], ![false, false, true, false, true, false, false, false, true, false, false, true], ![true, false, false, false, false, false, false, true, true, false, true, true], ![false, true, false, false, true, false, false, true, true, false, true, true], ![true, false, false, true, false, false, false, false, false, true, true, false], ![false, false, true, false, false, true, false, false, false, true, false, false], ![false, true, false, true, false, true, false, false, false, true, true, false], ![false, true, false, false, false, false, false, false, true, true, true, true], ![true, false, true, false, false, false, false, false, true, true, true, true]]
def weight : Fin 15 → Fin 15 → Int := ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, -3, 0, 0, 0, 0, 3, 0, 0, 3, 0, 0], ![0, 0, 0, 5, 3, 0, 0, 0, 0, -5, 0, 0, 3, 0, 5], ![0, 0, 2, 5, 0, 4, 0, 0, 0, 5, 6, 0, 0, 0, -10], ![0, 2, 0, 0, 0, 4, 0, 0, 0, 0, -6, 0, 0, 0, 6], ![0, 4, 0, 0, 0, 2, 0, 0, 0, -6, 0, 0, 0, 0, 6], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 3, -3, 0], ![0, 0, 0, 4, 3, 0, 0, 0, 0, 3, 0, 0, -4, 0, 4], ![0, 0, 0, -5, 0, 5, 0, 0, 0, 5, 0, 0, 5, 0, 5], ![0, -2, -2, 4, 0, -4, 0, 0, 0, 4, 6, 0, 0, 0, 6], ![0, 0, 0, 4, 0, 6, 0, 0, 0, 6, 0, 0, 4, -2, -6], ![0, 0, 0, -4, 0, 4, 0, 0, 0, 4, 0, 0, 4, 2, 2], ![0, 2, 2, 4, 0, 0, 0, 0, 0, -4, 0, 0, 3, 3, 0], ![0, 4, 0, 5, 0, 1, 0, 0, 0, 3, 0, 0, -5, 3, 0], ![0, -4, 0, 5, 0, -6, 0, 0, 0, 6, 0, 0, 5, 2, 4]]
def costs : Fin 12 → Int := ![0, 0, 6, 10, 12, 12, 6, 8, 10, 8, 0, 18]
def positions : Fin 12 → Fin 6 → Fin 15 := ![![0, 4, 5, 0, 0, 0], ![0, 1, 6, 0, 0, 0], ![1, 2, 7, 1, 1, 1], ![2, 3, 8, 2, 2, 2], ![3, 4, 9, 3, 3, 3], ![5, 10, 14, 5, 5, 5], ![6, 12, 13, 6, 6, 6], ![7, 10, 11, 7, 7, 7], ![8, 13, 14, 8, 8, 8], ![9, 11, 12, 9, 9, 9], ![0, 1, 4, 5, 6, 0], ![7, 8, 10, 11, 13, 14]]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma positive_inputs : ∀ r i, observe (raw i) (positiveRows r) = positiveSample r i := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma negative_inputs : ∀ r i, observe (raw i) (negativeRows r) = negativeSample r i := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma positive_graph : ∀ r, observe graph (positiveRows r) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma negative_graph : ∀ r, observe graph (negativeRows r) = false := by decide +kernel

def rect (S T : Finset (Fin 15)) : Int := ∑ r ∈ S, ∑ c ∈ T, weight r c

def negativeSet (i : Fin 12) : Finset (Fin 15) :=
  Finset.univ.filter (fun c => negativeSample c i = false)

def selected (i : Fin 12) (keep : Fin 6 → Bool) : Finset (Fin 15) :=
  (Finset.univ.filter (fun k => keep k = true)).image (positions i)

def maxRect (i : Fin 12) (S : Finset (Fin 15)) : Int :=
  ∑ c ∈ negativeSet i, max (∑ r ∈ S, weight r c) 0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma positions_cover : ∀ (i : Fin 12) (r : Fin 15),
    positiveSample r i = true ↔ ∃ k : Fin 6, positions i k = r := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma finite_rectangle_bound : ∀ (i : Fin 12) (keep : Fin 6 → Bool),
    maxRect i (selected i keep) ≤ costs i := by
  intro i
  fin_cases i <;> decide +kernel

lemma selected_covers (i : Fin 12) (S : Finset (Fin 15))
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

lemma leaf_bound (i : Fin 12) (S T : Finset (Fin 15))
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

lemma raw_bound (i : Fin 12) : RectangleRun.Bounds
    positiveRows negativeRows weight (observe (raw i)) (costs i) := by
  intro S T hs ht
  apply leaf_bound i S T
  · intro r hr
    rw [← positive_inputs]
    exact hs r hr
  · intro c hc
    rw [← negative_inputs]
    exact ht c hc

def labels : List (Fin 12) := [0, 0, 1, 1, 2, 2, 3, 3, 4, 5, 6, 7, 8, 9, 9, 10, 11, 11]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma full_weight : rect Finset.univ Finset.univ = 135 := by decide +kernel

lemma total_cost : (labels.map costs).sum = 132 := by decide +kernel

lemma bank_exclusion
    (trace : Run false (observe graph) 17 (labels.map (fun i => observe (raw i)))) : False := by
  have bounds := RectangleRun.tight_run_indexed
    positiveRows negativeRows weight
    (fun i => observe (raw i)) costs labels trace (by decide) (fun i _ => raw_bound i)
  have bound := bounds Finset.univ Finset.univ
    (fun r _ => positive_graph r)
    (fun c _ => negative_graph c)
  change rect Finset.univ Finset.univ ≤ (labels.map costs).sum at bound
  rw [full_weight, total_cost] at bound
  omega

end PEqualNP.Outside.L_meta_2373.RectangleBank13338
