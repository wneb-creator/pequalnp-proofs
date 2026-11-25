import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux.OrbitCover

def edges : List (Fin 10 × Fin 10) :=
  [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),
   (5,7),(7,9),(9,6),(6,8),(8,5)]

def adjacent (u v : Fin 10) : Prop := (u,v) ∈ edges ∨ (v,u) ∈ edges

def independent (M : Finset (Fin 10)) : Bool :=
  edges.all (fun e => !(decide (e.1 ∈ M) && decide (e.2 ∈ M)))

def maximal (M : Finset (Fin 10)) : Bool :=
  independent M && (List.ofFn (fun v : Fin 10 => v)).all
    (fun v => decide (v ∈ M) || !(independent (insert v M)))

def maximalSets : List (Finset (Fin 10)) :=
  [{1, 4, 5}, {0, 2, 6}, {3, 5, 6}, {2, 4, 5, 6}, {1, 3, 7}, {0, 3, 6, 7}, {4, 6, 7}, {2, 4, 8}, {0, 7, 8}, {1, 4, 7, 8}, {0, 3, 9}, {2, 5, 9}, {1, 3, 5, 9}, {1, 8, 9}, {0, 2, 8, 9}]

def permutations : List (Fin 10 → Fin 10) :=
  [![0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
    ![0, 1, 2, 7, 5, 4, 6, 3, 9, 8],
    ![0, 1, 6, 8, 5, 4, 2, 9, 3, 7],
    ![0, 1, 6, 9, 4, 5, 2, 8, 7, 3],
    ![0, 4, 3, 2, 1, 5, 9, 8, 7, 6],
    ![0, 4, 3, 8, 5, 1, 9, 2, 6, 7],
    ![0, 4, 9, 6, 1, 5, 3, 7, 8, 2],
    ![0, 4, 9, 7, 5, 1, 3, 6, 2, 8],
    ![0, 5, 7, 2, 1, 4, 8, 9, 3, 6],
    ![0, 5, 7, 9, 4, 1, 8, 2, 6, 3],
    ![0, 5, 8, 3, 4, 1, 7, 6, 2, 9],
    ![0, 5, 8, 6, 1, 4, 7, 3, 9, 2],
    ![1, 0, 4, 3, 2, 6, 5, 9, 8, 7],
    ![1, 0, 4, 9, 6, 2, 5, 3, 7, 8],
    ![1, 0, 5, 7, 2, 6, 4, 8, 9, 3],
    ![1, 0, 5, 8, 6, 2, 4, 7, 3, 9],
    ![1, 2, 3, 4, 0, 6, 7, 8, 9, 5],
    ![1, 2, 3, 8, 6, 0, 7, 4, 5, 9],
    ![1, 2, 7, 5, 0, 6, 3, 9, 8, 4],
    ![1, 2, 7, 9, 6, 0, 3, 5, 4, 8],
    ![1, 6, 8, 3, 2, 0, 9, 5, 4, 7],
    ![1, 6, 8, 5, 0, 2, 9, 3, 7, 4],
    ![1, 6, 9, 4, 0, 2, 8, 7, 3, 5],
    ![1, 6, 9, 7, 2, 0, 8, 4, 5, 3],
    ![2, 1, 0, 4, 3, 7, 6, 5, 9, 8],
    ![2, 1, 0, 5, 7, 3, 6, 4, 8, 9],
    ![2, 1, 6, 8, 3, 7, 0, 9, 5, 4],
    ![2, 1, 6, 9, 7, 3, 0, 8, 4, 5],
    ![2, 3, 4, 0, 1, 7, 8, 9, 5, 6],
    ![2, 3, 4, 9, 7, 1, 8, 0, 6, 5],
    ![2, 3, 8, 5, 7, 1, 4, 6, 0, 9],
    ![2, 3, 8, 6, 1, 7, 4, 5, 9, 0],
    ![2, 7, 5, 0, 1, 3, 9, 8, 4, 6],
    ![2, 7, 5, 8, 3, 1, 9, 0, 6, 4],
    ![2, 7, 9, 4, 3, 1, 5, 6, 0, 8],
    ![2, 7, 9, 6, 1, 3, 5, 4, 8, 0],
    ![3, 2, 1, 0, 4, 8, 7, 6, 5, 9],
    ![3, 2, 1, 6, 8, 4, 7, 0, 9, 5],
    ![3, 2, 7, 5, 8, 4, 1, 9, 0, 6],
    ![3, 2, 7, 9, 4, 8, 1, 5, 6, 0],
    ![3, 4, 0, 1, 2, 8, 9, 5, 6, 7],
    ![3, 4, 0, 5, 8, 2, 9, 1, 7, 6],
    ![3, 4, 9, 6, 8, 2, 0, 7, 1, 5],
    ![3, 4, 9, 7, 2, 8, 0, 6, 5, 1],
    ![3, 8, 5, 0, 4, 2, 6, 7, 1, 9],
    ![3, 8, 5, 7, 2, 4, 6, 0, 9, 1],
    ![3, 8, 6, 1, 2, 4, 5, 9, 0, 7],
    ![3, 8, 6, 9, 4, 2, 5, 1, 7, 0],
    ![4, 0, 1, 2, 3, 9, 5, 6, 7, 8],
    ![4, 0, 1, 6, 9, 3, 5, 2, 8, 7],
    ![4, 0, 5, 7, 9, 3, 1, 8, 2, 6],
    ![4, 0, 5, 8, 3, 9, 1, 7, 6, 2],
    ![4, 3, 2, 1, 0, 9, 8, 7, 6, 5],
    ![4, 3, 2, 7, 9, 0, 8, 1, 5, 6],
    ![4, 3, 8, 5, 0, 9, 2, 6, 7, 1],
    ![4, 3, 8, 6, 9, 0, 2, 5, 1, 7],
    ![4, 9, 6, 1, 0, 3, 7, 8, 2, 5],
    ![4, 9, 6, 8, 3, 0, 7, 1, 5, 2],
    ![4, 9, 7, 2, 3, 0, 6, 5, 1, 8],
    ![4, 9, 7, 5, 0, 3, 6, 2, 8, 1],
    ![5, 0, 1, 2, 7, 8, 4, 6, 3, 9],
    ![5, 0, 1, 6, 8, 7, 4, 2, 9, 3],
    ![5, 0, 4, 3, 8, 7, 1, 9, 2, 6],
    ![5, 0, 4, 9, 7, 8, 1, 3, 6, 2],
    ![5, 7, 2, 1, 0, 8, 9, 3, 6, 4],
    ![5, 7, 2, 3, 8, 0, 9, 1, 4, 6],
    ![5, 7, 9, 4, 0, 8, 2, 6, 3, 1],
    ![5, 7, 9, 6, 8, 0, 2, 4, 1, 3],
    ![5, 8, 3, 2, 7, 0, 6, 4, 1, 9],
    ![5, 8, 3, 4, 0, 7, 6, 2, 9, 1],
    ![5, 8, 6, 1, 0, 7, 3, 9, 2, 4],
    ![5, 8, 6, 9, 7, 0, 3, 1, 4, 2],
    ![6, 1, 0, 4, 9, 8, 2, 5, 3, 7],
    ![6, 1, 0, 5, 8, 9, 2, 4, 7, 3],
    ![6, 1, 2, 3, 8, 9, 0, 7, 4, 5],
    ![6, 1, 2, 7, 9, 8, 0, 3, 5, 4],
    ![6, 8, 3, 2, 1, 9, 5, 4, 7, 0],
    ![6, 8, 3, 4, 9, 1, 5, 2, 0, 7],
    ![6, 8, 5, 0, 1, 9, 3, 7, 4, 2],
    ![6, 8, 5, 7, 9, 1, 3, 0, 2, 4],
    ![6, 9, 4, 0, 1, 8, 7, 3, 5, 2],
    ![6, 9, 4, 3, 8, 1, 7, 0, 2, 5],
    ![6, 9, 7, 2, 1, 8, 4, 5, 3, 0],
    ![6, 9, 7, 5, 8, 1, 4, 2, 0, 3],
    ![7, 2, 1, 0, 5, 9, 3, 6, 4, 8],
    ![7, 2, 1, 6, 9, 5, 3, 0, 8, 4],
    ![7, 2, 3, 4, 9, 5, 1, 8, 0, 6],
    ![7, 2, 3, 8, 5, 9, 1, 4, 6, 0],
    ![7, 5, 0, 1, 2, 9, 8, 4, 6, 3],
    ![7, 5, 0, 4, 9, 2, 8, 1, 3, 6],
    ![7, 5, 8, 3, 2, 9, 0, 6, 4, 1],
    ![7, 5, 8, 6, 9, 2, 0, 3, 1, 4],
    ![7, 9, 4, 0, 5, 2, 6, 3, 1, 8],
    ![7, 9, 4, 3, 2, 5, 6, 0, 8, 1],
    ![7, 9, 6, 1, 2, 5, 4, 8, 0, 3],
    ![7, 9, 6, 8, 5, 2, 4, 1, 3, 0],
    ![8, 3, 2, 1, 6, 5, 4, 7, 0, 9],
    ![8, 3, 2, 7, 5, 6, 4, 1, 9, 0],
    ![8, 3, 4, 0, 5, 6, 2, 9, 1, 7],
    ![8, 3, 4, 9, 6, 5, 2, 0, 7, 1],
    ![8, 5, 0, 1, 6, 3, 7, 4, 2, 9],
    ![8, 5, 0, 4, 3, 6, 7, 1, 9, 2],
    ![8, 5, 7, 2, 3, 6, 0, 9, 1, 4],
    ![8, 5, 7, 9, 6, 3, 0, 2, 4, 1],
    ![8, 6, 1, 0, 5, 3, 9, 2, 4, 7],
    ![8, 6, 1, 2, 3, 5, 9, 0, 7, 4],
    ![8, 6, 9, 4, 3, 5, 1, 7, 0, 2],
    ![8, 6, 9, 7, 5, 3, 1, 4, 2, 0],
    ![9, 4, 0, 1, 6, 7, 3, 5, 2, 8],
    ![9, 4, 0, 5, 7, 6, 3, 1, 8, 2],
    ![9, 4, 3, 2, 7, 6, 0, 8, 1, 5],
    ![9, 4, 3, 8, 6, 7, 0, 2, 5, 1],
    ![9, 6, 1, 0, 4, 7, 8, 2, 5, 3],
    ![9, 6, 1, 2, 7, 4, 8, 0, 3, 5],
    ![9, 6, 8, 3, 4, 7, 1, 5, 2, 0],
    ![9, 6, 8, 5, 7, 4, 1, 3, 0, 2],
    ![9, 7, 2, 1, 6, 4, 5, 3, 0, 8],
    ![9, 7, 2, 3, 4, 6, 5, 1, 8, 0],
    ![9, 7, 5, 0, 4, 6, 2, 8, 1, 3],
    ![9, 7, 5, 8, 6, 4, 2, 0, 3, 1]]

def cases (p : Fin 10 → Fin 10) (M : Finset (Fin 10)) (e : Fin 10 × Fin 10) : Prop :=
  (M.image p = {1,4,5} ∧
    ({p e.1,p e.2} = ({0,1} : Finset (Fin 10)) ∨
     {p e.1,p e.2} = ({1,2} : Finset (Fin 10)) ∨
     {p e.1,p e.2} = ({2,3} : Finset (Fin 10)))) ∨
  (M.image p = {2,4,5,6} ∧
    ({p e.1,p e.2} = ({0,1} : Finset (Fin 10)) ∨
     {p e.1,p e.2} = ({1,2} : Finset (Fin 10))))

def validDecidable (p : Fin 10 → Fin 10) :
    Decidable ((∀ u v : Fin 10, p u = p v → u = v) ∧
      (∀ v : Fin 10, ∃ u : Fin 10, p u = v) ∧
      ∀ u v, adjacent (p u) (p v) ↔ adjacent u v) := by
  letI (u v : Fin 10) : Decidable (adjacent u v) := inferInstanceAs (Decidable ((u,v) ∈ edges ∨ (v,u) ∈ edges))
  infer_instance

def casesDecidable (p : Fin 10 → Fin 10) (M : Finset (Fin 10)) (e : Fin 10 × Fin 10) :
    Decidable (cases p M e) := by
  unfold cases
  infer_instance

set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
lemma maximal_sets_complete : ∀ M : Finset (Fin 10), maximal M = true → M ∈ maximalSets := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
lemma permutations_valid : permutations.all (fun p =>
    @decide ((∀ u v : Fin 10, p u = p v → u = v) ∧
      (∀ v : Fin 10, ∃ u : Fin 10, p u = v) ∧
      ∀ u v, adjacent (p u) (p v) ↔ adjacent u v) (validDecidable p)) = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
lemma representatives_complete : maximalSets.all (fun M =>
    edges.all (fun e => permutations.any (fun p => @decide (cases p M e) (casesDecidable p M e)))) = true := by
  decide +kernel

lemma maximal_pair_representative (M : Finset (Fin 10)) (hM : maximal M = true)
    (e : Fin 10 × Fin 10) (he : e ∈ edges) :
    ∃ p : Fin 10 → Fin 10, Function.Bijective p ∧
      (∀ u v, adjacent (p u) (p v) ↔ adjacent u v) ∧ cases p M e := by
  have hm := maximal_sets_complete M hM
  have allEdges := List.all_eq_true.mp representatives_complete M hm
  obtain ⟨p, hp, representative⟩ := List.any_eq_true.mp (List.all_eq_true.mp allEdges e he)
  have valid := @of_decide_eq_true _ (validDecidable p) (List.all_eq_true.mp permutations_valid p hp)
  exact ⟨p, ⟨fun {_ _} equal => valid.1 _ _ equal, valid.2.1⟩, valid.2.2,
    @of_decide_eq_true _ (casesDecidable p M e) representative⟩

lemma independent_true_iff (M : Finset (Fin 10)) :
    independent M = true ↔ ∀ e ∈ edges, ¬ (e.1 ∈ M ∧ e.2 ∈ M) := by
  change edges.all _ = true ↔ _
  rw [List.all_eq_true]
  constructor
  · intro hm e he both
    have value := hm e he
    simp [both.1, both.2] at value
  · intro hm e he
    by_cases hu : e.1 ∈ M
    · have hv : e.2 ∉ M := fun hv => hm e he ⟨hu,hv⟩
      simp [hu,hv]
    · simp [hu]

lemma maximal_true_of_inclusion_maximal (M : Finset (Fin 10))
    (free : ∀ e ∈ edges, ¬ (e.1 ∈ M ∧ e.2 ∈ M))
    (largest : ∀ T : Finset (Fin 10), M ⊆ T →
      (∀ e ∈ edges, ¬ (e.1 ∈ T ∧ e.2 ∈ T)) → T = M) : maximal M = true := by
  have hi := (independent_true_iff M).mpr free
  unfold maximal
  rw [hi, Bool.true_and]
  apply List.all_eq_true.mpr
  intro v _
  by_cases hv : v ∈ M
  · simp [hv]
  · have bad : independent (insert v M) = false := by
      cases value : independent (insert v M) with
      | false => rfl
      | true =>
        have same := largest (insert v M) (Finset.subset_insert v M)
          ((independent_true_iff (insert v M)).mp value)
        have member : v ∈ M := same ▸ Finset.mem_insert_self v M
        exact (hv member).elim
    simp [hv,bad]

end PEqualNP.Outside.L_meta_2592_aux.OrbitCover
