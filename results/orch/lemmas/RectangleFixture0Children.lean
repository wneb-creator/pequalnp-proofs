import PrunedInterface
import RectangleRunIndexed

namespace PEqualNP.Outside.L_meta_2373.Live1024.RectangleFixture0Children

def signal : Fin 13 → Sig := ![0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc, 0xf8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 0xfffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaa, 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000, 0xfffffffffffffffffffffffffffffffffaaafaaafaaafaaafaaafaaafaaafaaafffffffffffffffffffffffffffffffffaaafaaafaaafaaafaaafaaafaaafaaafffffffffffffffffffffffffffffffffaaafaaafaaafaaafaaafaaafaaafaaafffffffffffffffffffffffffffffffffaaafaaafaaafaaafaaafaaafaaafaaa, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0xfffffffffaaafaaafffffffffaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafffffffffaaafaaafffffffffaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafffffffffaaafaaafffffffffaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafffffffffaaafaaafffffffffaaafaaafaaafaaafaaafaaafaaafaaafaaafaaa]
def baseRaw (i : Fin 12) : Sig := signal i.castSucc
def baseRoots : Finset (Fin 12) := Finset.univ
def support : Fin 13 → Finset (Fin 12) := ![{0}, {1}, {2}, {3}, {4}, {5}, {6}, {7}, {8}, {9}, {10}, {11}, {5, 8}]
def copiedRoots (i : Fin 13) := duplicateRoots baseRoots (support i)
def copiedRaw (i : Fin 13) := duplicateRaw baseRaw (signal i)
def signalIndex (i : Fin 13) : Sum (Fin 12) Bool → Fin 13 := Sum.elim Fin.castSucc (fun _ => i)
def rootLabels : Fin 13 → List (Sum (Fin 12) Bool) := ![[(Sum.inl 1), (Sum.inl 2), (Sum.inl 3), (Sum.inl 4), (Sum.inl 5), (Sum.inl 6), (Sum.inl 7), (Sum.inl 8), (Sum.inl 9), (Sum.inl 10), (Sum.inl 11), (Sum.inr false), (Sum.inr true)], [(Sum.inl 0), (Sum.inl 2), (Sum.inl 3), (Sum.inl 4), (Sum.inl 5), (Sum.inl 6), (Sum.inl 7), (Sum.inl 8), (Sum.inl 9), (Sum.inl 10), (Sum.inl 11), (Sum.inr false), (Sum.inr true)], [(Sum.inl 0), (Sum.inl 1), (Sum.inl 3), (Sum.inl 4), (Sum.inl 5), (Sum.inl 6), (Sum.inl 7), (Sum.inl 8), (Sum.inl 9), (Sum.inl 10), (Sum.inl 11), (Sum.inr false), (Sum.inr true)], [(Sum.inl 0), (Sum.inl 1), (Sum.inl 2), (Sum.inl 4), (Sum.inl 5), (Sum.inl 6), (Sum.inl 7), (Sum.inl 8), (Sum.inl 9), (Sum.inl 10), (Sum.inl 11), (Sum.inr false), (Sum.inr true)], [(Sum.inl 0), (Sum.inl 1), (Sum.inl 2), (Sum.inl 3), (Sum.inl 5), (Sum.inl 6), (Sum.inl 7), (Sum.inl 8), (Sum.inl 9), (Sum.inl 10), (Sum.inl 11), (Sum.inr false), (Sum.inr true)], [(Sum.inl 0), (Sum.inl 1), (Sum.inl 2), (Sum.inl 3), (Sum.inl 4), (Sum.inl 6), (Sum.inl 7), (Sum.inl 8), (Sum.inl 9), (Sum.inl 10), (Sum.inl 11), (Sum.inr false), (Sum.inr true)], [(Sum.inl 0), (Sum.inl 1), (Sum.inl 2), (Sum.inl 3), (Sum.inl 4), (Sum.inl 5), (Sum.inl 7), (Sum.inl 8), (Sum.inl 9), (Sum.inl 10), (Sum.inl 11), (Sum.inr false), (Sum.inr true)], [(Sum.inl 0), (Sum.inl 1), (Sum.inl 2), (Sum.inl 3), (Sum.inl 4), (Sum.inl 5), (Sum.inl 6), (Sum.inl 8), (Sum.inl 9), (Sum.inl 10), (Sum.inl 11), (Sum.inr false), (Sum.inr true)], [(Sum.inl 0), (Sum.inl 1), (Sum.inl 2), (Sum.inl 3), (Sum.inl 4), (Sum.inl 5), (Sum.inl 6), (Sum.inl 7), (Sum.inl 9), (Sum.inl 10), (Sum.inl 11), (Sum.inr false), (Sum.inr true)], [(Sum.inl 0), (Sum.inl 1), (Sum.inl 2), (Sum.inl 3), (Sum.inl 4), (Sum.inl 5), (Sum.inl 6), (Sum.inl 7), (Sum.inl 8), (Sum.inl 10), (Sum.inl 11), (Sum.inr false), (Sum.inr true)], [(Sum.inl 0), (Sum.inl 1), (Sum.inl 2), (Sum.inl 3), (Sum.inl 4), (Sum.inl 5), (Sum.inl 6), (Sum.inl 7), (Sum.inl 8), (Sum.inl 9), (Sum.inl 11), (Sum.inr false), (Sum.inr true)], [(Sum.inl 0), (Sum.inl 1), (Sum.inl 2), (Sum.inl 3), (Sum.inl 4), (Sum.inl 5), (Sum.inl 6), (Sum.inl 7), (Sum.inl 8), (Sum.inl 9), (Sum.inl 10), (Sum.inr false), (Sum.inr true)], [(Sum.inl 0), (Sum.inl 1), (Sum.inl 2), (Sum.inl 3), (Sum.inl 4), (Sum.inl 6), (Sum.inl 7), (Sum.inl 9), (Sum.inl 10), (Sum.inl 11), (Sum.inr false), (Sum.inr true)]]

def positiveRows : Fin 15 → Row := fun r => Fin.ofNat 1024 (![3, 6, 12, 24, 17, 33, 66, 132, 264, 528, 160, 640, 576, 320, 288] r)
def negativeRows : Fin 15 → Row := fun r => Fin.ofNat 1024 (![50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773] r)
def positiveSample : Fin 15 → Fin 13 → Bool := ![![true, true, false, false, false, true, false, false, true, false, false, false, true], ![true, true, false, false, false, false, false, false, false, false, false, false, false], ![false, true, true, false, false, true, false, false, true, false, false, false, true], ![false, false, true, true, false, false, false, false, false, false, false, false, false], ![false, false, false, true, false, true, false, false, true, false, false, false, true], ![false, false, false, false, true, true, false, false, true, false, false, false, true], ![true, false, false, false, false, false, true, false, false, false, true, false, false], ![false, true, false, false, false, false, false, true, true, false, false, false, false], ![false, false, true, false, false, false, false, false, false, true, true, false, false], ![false, false, false, true, false, false, false, false, false, false, false, true, false], ![false, false, false, false, true, true, false, true, true, false, false, false, true], ![false, false, false, false, false, false, false, true, true, false, false, true, false], ![false, false, false, false, false, false, true, false, false, false, true, true, false], ![false, false, false, false, false, false, true, false, false, true, true, false, false], ![false, false, false, false, true, true, false, false, false, true, true, false, false]]
def negativeSample : Fin 15 → Fin 13 → Bool := ![![true, false, false, true, true, true, false, false, false, false, false, false, false], ![false, true, false, false, false, true, true, false, true, false, true, false, true], ![false, false, true, false, true, true, true, false, false, false, true, false, false], ![false, true, false, true, true, true, true, false, false, false, true, false, false], ![true, false, true, false, false, false, false, true, true, false, false, false, false], ![false, false, true, false, false, true, true, true, true, false, true, false, true], ![false, false, false, true, false, false, true, true, true, false, true, false, false], ![false, true, false, true, false, false, false, false, false, true, true, false, false], ![false, false, false, false, false, true, false, true, true, true, true, false, true], ![true, false, false, true, false, false, false, true, true, true, true, false, false], ![false, false, true, false, false, true, false, false, true, false, false, true, true], ![false, true, false, false, true, true, false, false, false, false, false, true, false], ![true, false, true, false, true, true, false, false, false, false, false, true, false], ![true, false, false, false, false, false, false, false, false, true, true, true, false], ![false, true, false, false, false, true, false, false, true, true, true, true, true]]
def weight : Fin 15 → Fin 15 → Int := ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, -3, 0, 0, 0, 0, 3, 0, 0, 3, 0, 0], ![0, 0, 0, 5, 3, 0, 0, 0, 0, -5, 0, 0, 3, 0, 5], ![0, 0, 2, 5, 0, 4, 0, 0, 0, 5, 6, 0, 0, 0, -10], ![0, 2, 0, 0, 0, 4, 0, 0, 0, 0, -6, 0, 0, 0, 6], ![0, 4, 0, 0, 0, 2, 0, 0, 0, -6, 0, 0, 0, 0, 6], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 3, -3, 0], ![0, 0, 0, 4, 3, 0, 0, 0, 0, 3, 0, 0, -4, 0, 4], ![0, 0, 0, -5, 0, 5, 0, 0, 0, 5, 0, 0, 5, 0, 5], ![0, -2, -2, 4, 0, -4, 0, 0, 0, 4, 6, 0, 0, 0, 6], ![0, 0, 0, 4, 0, 6, 0, 0, 0, 6, 0, 0, 4, -2, -6], ![0, 0, 0, -4, 0, 4, 0, 0, 0, 4, 0, 0, 4, 2, 2], ![0, 2, 2, 4, 0, 0, 0, 0, 0, -4, 0, 0, 3, 3, 0], ![0, 4, 0, 5, 0, 1, 0, 0, 0, 3, 0, 0, -5, 3, 0], ![0, -4, 0, 5, 0, -6, 0, 0, 0, 6, 0, 0, 5, 2, 4]]
def costs : Fin 13 → Int := ![0, 6, 10, 12, 12, 12, 6, 8, 16, 10, 16, 8, 20]
def positions : Fin 13 → Fin 7 → Fin 15 := ![![0, 1, 6, 0, 0, 0, 0], ![0, 1, 2, 7, 0, 0, 0], ![2, 3, 8, 2, 2, 2, 2], ![3, 4, 9, 3, 3, 3, 3], ![5, 10, 14, 5, 5, 5, 5], ![0, 2, 4, 5, 10, 14, 0], ![6, 12, 13, 6, 6, 6, 6], ![7, 10, 11, 7, 7, 7, 7], ![0, 2, 4, 5, 7, 10, 11], ![8, 13, 14, 8, 8, 8, 8], ![6, 8, 12, 13, 14, 6, 6], ![9, 11, 12, 9, 9, 9, 9], ![0, 2, 4, 5, 10, 0, 0]]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma positive_inputs : ∀ r i, observe (signal i) (positiveRows r) = positiveSample r i := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma negative_inputs : ∀ r i, observe (signal i) (negativeRows r) = negativeSample r i := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma positive_graph : ∀ r, observe graph (positiveRows r) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma negative_graph : ∀ r, observe graph (negativeRows r) = false := by decide +kernel

def rect (S T : Finset (Fin 15)) : Int := ∑ r ∈ S, ∑ c ∈ T, weight r c

def negativeSet (i : Fin 13) : Finset (Fin 15) :=
  Finset.univ.filter (fun c => negativeSample c i = false)

def selected (i : Fin 13) (keep : Fin 7 → Bool) : Finset (Fin 15) :=
  (Finset.univ.filter (fun k => keep k = true)).image (positions i)

def maxRect (i : Fin 13) (S : Finset (Fin 15)) : Int :=
  ∑ c ∈ negativeSet i, max (∑ r ∈ S, weight r c) 0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma positions_cover : ∀ (i : Fin 13) (r : Fin 15),
    positiveSample r i = true ↔ ∃ k : Fin 7, positions i k = r := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma finite_rectangle_bound : ∀ (i : Fin 13) (keep : Fin 7 → Bool),
    maxRect i (selected i keep) ≤ costs i := by
  intro i
  fin_cases i <;> decide +kernel

lemma selected_covers (i : Fin 13) (S : Finset (Fin 15))
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

lemma leaf_bound (i : Fin 13) (S T : Finset (Fin 15))
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

lemma raw_bound (i : Fin 13) : RectangleRun.Bounds
    positiveRows negativeRows weight (observe (signal i)) (costs i) := by
  intro S T hs ht
  apply leaf_bound i S T
  · intro r hr
    rw [← positive_inputs]
    exact hs r hr
  · intro c hc
    rw [← negative_inputs]
    exact ht c hc


set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma full_weight : rect Finset.univ Finset.univ = 135 := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma child_facts : ∀ i, (rootLabels i).Nodup ∧ (rootLabels i).toFinset = copiedRoots i ∧
    ((rootLabels i).map (fun r => costs (signalIndex i r))).sum < 135 := by
  decide +kernel

lemma copied_raw (i : Fin 13) (r : Sum (Fin 12) Bool) :
    copiedRaw i r = signal (signalIndex i r) := by cases r <;> rfl

lemma all_budget_cuts (i : Fin 13) :
    BudgetRunCut (duplicateRoots baseRoots (support i))
      (duplicateRaw baseRaw (signal i)) false graph 0 := by
  intro k cap trace
  change Run false (observe graph) k ((copiedRoots i).toList.map (fun r => observe (copiedRaw i r))) at trace
  have facts := child_facts i
  have perm : (copiedRoots i).toList.Perm (rootLabels i) := by
    apply List.perm_of_nodup_nodup_toFinset_eq (Finset.nodup_toList _) facts.1
    simpa using facts.2.1.symm
  have ordered := Run.perm (perm.map (fun r => observe (copiedRaw i r))) trace
  have lengths : (copiedRoots i).card = (rootLabels i).length := by simpa using perm.length_eq
  have lower := RectangleRun.run_length_le ordered
  simp only [List.length_map] at lower
  have tight : (rootLabels i).length = k + 1 := by
    change k + 1 ≤ (copiedRoots i).card + 0 at cap
    omega
  have bounds := RectangleRun.tight_run_indexed positiveRows negativeRows weight
    (fun r => observe (copiedRaw i r)) (fun r => costs (signalIndex i r))
    (rootLabels i) ordered tight (fun r _ => by simpa only [copied_raw] using raw_bound (signalIndex i r))
  have bound := bounds Finset.univ Finset.univ
    (fun r _ => positive_graph r) (fun r _ => negative_graph r)
  change rect Finset.univ Finset.univ ≤ _ at bound
  rw [full_weight] at bound
  have strict := facts.2.2
  omega

def entries : List (Finset (Fin 12) × Sig) := List.ofFn (fun i : Fin 13 => (support i, signal i))

lemma entry_cuts {A : Finset (Fin 12)} {w : Sig} (entry : (A, w) ∈ entries) :
    BudgetRunCut (duplicateRoots baseRoots A) (duplicateRaw baseRaw w) false graph 0 := by
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp entry
  have parts := Prod.mk.inj hi
  simpa only [parts.1, parts.2] using all_budget_cuts i

end PEqualNP.Outside.L_meta_2373.Live1024.RectangleFixture0Children
