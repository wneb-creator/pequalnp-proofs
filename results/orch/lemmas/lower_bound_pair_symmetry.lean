import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux

def petersenEdges : List (Fin 10 × Fin 10) :=
  [(0,1), (1,2), (2,3), (3,4), (4,0), (0,5), (1,6), (2,7), (3,8), (4,9),
   (5,7), (7,9), (9,6), (6,8), (8,5)]

def petersenAdjacent (a b : Fin 10) : Prop :=
  (a,b) ∈ petersenEdges ∨ (b,a) ∈ petersenEdges

def pairSecond (a b : Fin 10) : Fin 10 :=
  if (a,b) ∈ petersenEdges ∨ (b,a) ∈ petersenEdges then 1 else 2

def pairMove : Fin 10 → Fin 10 → Fin 10 → Fin 10 :=
  ![![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
      ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
      ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
      ![0, 4, 3, 2, 1, 5, 9, 8, 7, 6],
      ![0, 4, 3, 2, 1, 5, 9, 8, 7, 6],
      ![0, 5, 7, 2, 1, 4, 8, 9, 3, 6],
      ![0, 1, 6, 8, 5, 4, 2, 9, 3, 7],
      ![0, 5, 7, 2, 1, 4, 8, 9, 3, 6],
      ![0, 5, 8, 3, 4, 1, 7, 6, 2, 9],
      ![0, 4, 9, 6, 1, 5, 3, 7, 8, 2]],
    ![![1, 0, 4, 3, 2, 6, 5, 9, 8, 7],
      ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
      ![1, 2, 3, 4, 0, 6, 7, 8, 9, 5],
      ![1, 2, 3, 4, 0, 6, 7, 8, 9, 5],
      ![1, 0, 4, 3, 2, 6, 5, 9, 8, 7],
      ![1, 0, 5, 7, 2, 6, 4, 8, 9, 3],
      ![1, 6, 8, 3, 2, 0, 9, 5, 4, 7],
      ![1, 2, 7, 5, 0, 6, 3, 9, 8, 4],
      ![1, 6, 8, 3, 2, 0, 9, 5, 4, 7],
      ![1, 6, 9, 4, 0, 2, 8, 7, 3, 5]],
    ![![2, 1, 0, 4, 3, 7, 6, 5, 9, 8],
      ![2, 1, 0, 4, 3, 7, 6, 5, 9, 8],
      ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
      ![2, 3, 4, 0, 1, 7, 8, 9, 5, 6],
      ![2, 3, 4, 0, 1, 7, 8, 9, 5, 6],
      ![2, 7, 5, 0, 1, 3, 9, 8, 4, 6],
      ![2, 1, 6, 8, 3, 7, 0, 9, 5, 4],
      ![2, 7, 5, 0, 1, 3, 9, 8, 4, 6],
      ![2, 3, 8, 5, 7, 1, 4, 6, 0, 9],
      ![2, 7, 9, 4, 3, 1, 5, 6, 0, 8]],
    ![![3, 4, 0, 1, 2, 8, 9, 5, 6, 7],
      ![3, 2, 1, 0, 4, 8, 7, 6, 5, 9],
      ![3, 2, 1, 0, 4, 8, 7, 6, 5, 9],
      ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
      ![3, 4, 0, 1, 2, 8, 9, 5, 6, 7],
      ![3, 8, 5, 0, 4, 2, 6, 7, 1, 9],
      ![3, 8, 6, 1, 2, 4, 5, 9, 0, 7],
      ![3, 2, 7, 5, 8, 4, 1, 9, 0, 6],
      ![3, 8, 5, 0, 4, 2, 6, 7, 1, 9],
      ![3, 4, 9, 6, 8, 2, 0, 7, 1, 5]],
    ![![4, 0, 1, 2, 3, 9, 5, 6, 7, 8],
      ![4, 0, 1, 2, 3, 9, 5, 6, 7, 8],
      ![4, 3, 2, 1, 0, 9, 8, 7, 6, 5],
      ![4, 3, 2, 1, 0, 9, 8, 7, 6, 5],
      ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
      ![4, 0, 5, 7, 9, 3, 1, 8, 2, 6],
      ![4, 9, 6, 1, 0, 3, 7, 8, 2, 5],
      ![4, 9, 7, 2, 3, 0, 6, 5, 1, 8],
      ![4, 3, 8, 5, 0, 9, 2, 6, 7, 1],
      ![4, 9, 6, 1, 0, 3, 7, 8, 2, 5]],
    ![![5, 0, 1, 2, 7, 8, 4, 6, 3, 9],
      ![5, 0, 1, 2, 7, 8, 4, 6, 3, 9],
      ![5, 7, 2, 1, 0, 8, 9, 3, 6, 4],
      ![5, 8, 3, 2, 7, 0, 6, 4, 1, 9],
      ![5, 0, 4, 3, 8, 7, 1, 9, 2, 6],
      ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
      ![5, 8, 6, 1, 0, 7, 3, 9, 2, 4],
      ![5, 7, 2, 1, 0, 8, 9, 3, 6, 4],
      ![5, 8, 3, 2, 7, 0, 6, 4, 1, 9],
      ![5, 7, 9, 4, 0, 8, 2, 6, 3, 1]],
    ![![6, 1, 0, 4, 9, 8, 2, 5, 3, 7],
      ![6, 1, 0, 4, 9, 8, 2, 5, 3, 7],
      ![6, 1, 2, 3, 8, 9, 0, 7, 4, 5],
      ![6, 8, 3, 2, 1, 9, 5, 4, 7, 0],
      ![6, 9, 4, 0, 1, 8, 7, 3, 5, 2],
      ![6, 8, 5, 0, 1, 9, 3, 7, 4, 2],
      ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
      ![6, 9, 7, 2, 1, 8, 4, 5, 3, 0],
      ![6, 8, 3, 2, 1, 9, 5, 4, 7, 0],
      ![6, 9, 4, 0, 1, 8, 7, 3, 5, 2]],
    ![![7, 5, 0, 1, 2, 9, 8, 4, 6, 3],
      ![7, 2, 1, 0, 5, 9, 3, 6, 4, 8],
      ![7, 2, 1, 0, 5, 9, 3, 6, 4, 8],
      ![7, 2, 3, 4, 9, 5, 1, 8, 0, 6],
      ![7, 9, 4, 0, 5, 2, 6, 3, 1, 8],
      ![7, 5, 0, 1, 2, 9, 8, 4, 6, 3],
      ![7, 9, 6, 1, 2, 5, 4, 8, 0, 3],
      ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
      ![7, 5, 8, 3, 2, 9, 0, 6, 4, 1],
      ![7, 9, 4, 0, 5, 2, 6, 3, 1, 8]],
    ![![8, 5, 0, 1, 6, 3, 7, 4, 2, 9],
      ![8, 6, 1, 0, 5, 3, 9, 2, 4, 7],
      ![8, 3, 2, 1, 6, 5, 4, 7, 0, 9],
      ![8, 3, 2, 1, 6, 5, 4, 7, 0, 9],
      ![8, 3, 4, 0, 5, 6, 2, 9, 1, 7],
      ![8, 5, 0, 1, 6, 3, 7, 4, 2, 9],
      ![8, 6, 1, 0, 5, 3, 9, 2, 4, 7],
      ![8, 5, 7, 2, 3, 6, 0, 9, 1, 4],
      ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
      ![8, 6, 9, 4, 3, 5, 1, 7, 0, 2]],
    ![![9, 4, 0, 1, 6, 7, 3, 5, 2, 8],
      ![9, 6, 1, 0, 4, 7, 8, 2, 5, 3],
      ![9, 7, 2, 1, 6, 4, 5, 3, 0, 8],
      ![9, 4, 3, 2, 7, 6, 0, 8, 1, 5],
      ![9, 4, 0, 1, 6, 7, 3, 5, 2, 8],
      ![9, 7, 5, 0, 4, 6, 2, 8, 1, 3],
      ![9, 6, 1, 0, 4, 7, 8, 2, 5, 3],
      ![9, 7, 2, 1, 6, 4, 5, 3, 0, 8],
      ![9, 6, 8, 3, 4, 7, 1, 5, 2, 0],
      ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9]]]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 10000 in
lemma pairMove_properties : ∀ a b : Fin 10, a ≠ b →
    pairMove a b 0 = a ∧ pairMove a b (pairSecond a b) = b ∧
    Function.Bijective (pairMove a b) ∧
    ∀ i j : Fin 10, petersenAdjacent (pairMove a b i) (pairMove a b j) ↔
      petersenAdjacent i j := by
  unfold petersenAdjacent
  decide +kernel

def edgeFunction (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

lemma edgeFunction_edges (x : Fin 10 → Bool) : edgeFunction x = true ↔
    ∃ e ∈ petersenEdges, x e.1 = true ∧ x e.2 = true := by
  simp [edgeFunction, petersenEdges, Bool.or_eq_true, Bool.and_eq_true, or_assoc]

lemma edgeFunction_adjacent (x : Fin 10 → Bool) : edgeFunction x = true ↔
    ∃ i j : Fin 10, petersenAdjacent i j ∧ x i = true ∧ x j = true := by
  rw [edgeFunction_edges]
  constructor
  · rintro ⟨⟨i,j⟩, he, hi, hj⟩
    exact ⟨i,j,Or.inl he,hi,hj⟩
  · rintro ⟨i,j,he,hi,hj⟩
    rcases he with he | he
    · exact ⟨(i,j),he,hi,hj⟩
    · exact ⟨(j,i),he,hj,hi⟩

lemma edgeFunction_pairMove (a b : Fin 10) (hne : a ≠ b) (x : Fin 10 → Bool) :
    edgeFunction (fun i => x (pairMove a b i)) = edgeFunction x := by
  obtain ⟨_,_,hbij,hadj⟩ := pairMove_properties a b hne
  apply Bool.eq_iff_iff.mpr
  rw [edgeFunction_adjacent,edgeFunction_adjacent]
  constructor
  · rintro ⟨i,j,he,hi,hj⟩
    exact ⟨pairMove a b i,pairMove a b j,(hadj i j).mpr he,hi,hj⟩
  · rintro ⟨i,j,he,hi,hj⟩
    obtain ⟨i,rfl⟩ := hbij.2 i
    obtain ⟨j,rfl⟩ := hbij.2 j
    exact ⟨i,j,(hadj i j).mp he,hi,hj⟩

end PEqualNP.Outside.L_meta_2592_aux
