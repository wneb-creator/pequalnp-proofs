import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux.PairSeparation

def pet (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def pairInput (a b w : Fin 10) (u v : Bool) : Fin 10 → Bool :=
  fun i => if i = a then u else if i = b then v else decide (i = w)

set_option maxHeartbeats 1000000 in
lemma firstProjection : ∀ a b : Fin 10, a ≠ b →
    ∃ w : Fin 10, ∀ u v : Bool, pet (pairInput a b w u v) = u := by
  decide +kernel

lemma pairInput_swap (a b w : Fin 10) (hne : a ≠ b) (u v : Bool) :
    pairInput b a w v u = pairInput a b w u v := by
  funext i
  by_cases ha : i = a
  · subst i
    simp [pairInput, hne]
  · by_cases hb : i = b
    · subst i
      simp [pairInput, hne.symm]
    · simp [pairInput, ha, hb]

lemma secondProjection (a b : Fin 10) (hne : a ≠ b) :
    ∃ w : Fin 10, ∀ u v : Bool, pet (pairInput a b w u v) = v := by
  obtain ⟨w, hw⟩ := firstProjection b a hne.symm
  refine ⟨w, ?_⟩
  intro u v
  rw [← pairInput_swap a b w hne u v]
  exact hw v u

lemma noPairFactor (a b : Fin 10) (hne : a ≠ b) (q : Bool → Bool → Bool)
    (factor : ∀ w : Fin 10, ∃ r : Bool → Bool,
      ∀ u v : Bool, pet (pairInput a b w u v) = r (q u v)) : False := by
  obtain ⟨wa, ha⟩ := firstProjection a b hne
  obtain ⟨wb, hb⟩ := secondProjection a b hne
  obtain ⟨ra, hra⟩ := factor wa
  obtain ⟨rb, hrb⟩ := factor wb
  have left (u v : Bool) : ra (q u v) = u := (hra u v).symm.trans (ha u v)
  have right (u v : Bool) : rb (q u v) = v := (hrb u v).symm.trans (hb u v)
  have ne01 : q false false ≠ q false true := by
    intro h
    have hh := congrArg rb h
    rw [right false false, right false true] at hh
    cases hh
  have ne10 : q false false ≠ q true false := by
    intro h
    have hh := congrArg ra h
    rw [left false false, left true false] at hh
    cases hh
  have ne12 : q false true ≠ q true false := by
    intro h
    have hh := congrArg ra h
    rw [left false true, left true false] at hh
    cases hh
  cases h0 : q false false <;> cases h1 : q false true <;>
    cases h2 : q true false <;> simp_all

set_option maxHeartbeats 1000000 in
lemma cofactorWitness : ∀ v u : Fin 10, v ≠ u → ∀ val : Bool,
    ∃ w : Fin 10,
      pet (Function.update (Function.update (fun i => decide (i = w)) u val) v false) ≠
      pet (Function.update (Function.update (fun i => decide (i = w)) u val) v true) := by
  decide +kernel

lemma cofactorKeepsOtherInput (v u : Fin 10) (hne : v ≠ u) (val : Bool) :
    ∃ x : Fin 10 → Bool,
      pet (Function.update (Function.update x u val) v false) ≠
      pet (Function.update (Function.update x u val) v true) := by
  obtain ⟨w, hw⟩ := cofactorWitness v u hne val
  exact ⟨fun i => decide (i = w), hw⟩

def vertexPerm (v : Fin 10) : Fin 10 → Fin 10 :=
  (![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
    ![1, 2, 3, 4, 0, 6, 7, 8, 9, 5],
    ![2, 3, 4, 0, 1, 7, 8, 9, 5, 6],
    ![3, 4, 0, 1, 2, 8, 9, 5, 6, 7],
    ![4, 0, 1, 2, 3, 9, 5, 6, 7, 8],
    ![5, 7, 9, 6, 8, 0, 2, 4, 1, 3],
    ![6, 8, 5, 7, 9, 1, 3, 0, 2, 4],
    ![7, 9, 6, 8, 5, 2, 4, 1, 3, 0],
    ![8, 5, 7, 9, 6, 3, 0, 2, 4, 1],
    ![9, 6, 8, 5, 7, 4, 1, 3, 0, 2]]) v

lemma vertexPerm_bijective : ∀ v : Fin 10, Function.Bijective (vertexPerm v) := by
  decide +kernel

lemma vertexPerm_zero : ∀ v : Fin 10, vertexPerm v 0 = v := by
  decide +kernel

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
lemma pet_vertexPerm : ∀ (v : Fin 10) (x : Fin 10 → Bool),
    pet (x ∘ vertexPerm v) = pet x := by
  decide +kernel

end PEqualNP.Outside.L_meta_2592_aux.PairSeparation
