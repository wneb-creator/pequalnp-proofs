import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592.Automorphisms

def edges : List (Fin 10 × Fin 10) :=
  [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),
   (5,7),(7,9),(9,6),(6,8),(8,5)]

def adj (a b : Fin 10) : Bool := edges.contains (a,b) || edges.contains (b,a)

def value (x : Fin 10 → Bool) : Bool := edges.any (fun e => x e.1 && x e.2)

def row (i j : Fin 10) : Fin 10 → Fin 10 :=
  (![![![0,1,2,3,4,5,6,7,8,9],
     ![0,1,2,3,4,5,6,7,8,9],
     ![0,1,2,3,4,5,6,7,8,9],
     ![0,4,3,2,1,5,9,8,7,6],
     ![0,4,3,2,1,5,9,8,7,6],
     ![0,4,3,8,5,1,9,2,6,7],
     ![0,1,6,8,5,4,2,9,3,7],
     ![0,4,3,8,5,1,9,2,6,7],
     ![0,4,9,7,5,1,3,6,2,8],
     ![0,4,9,6,1,5,3,7,8,2]],
    ![![1,0,4,3,2,6,5,9,8,7],
     ![0,1,2,3,4,5,6,7,8,9],
     ![4,0,1,2,3,9,5,6,7,8],
     ![4,0,1,2,3,9,5,6,7,8],
     ![1,0,4,3,2,6,5,9,8,7],
     ![1,0,4,9,6,2,5,3,7,8],
     ![4,0,5,7,9,3,1,8,2,6],
     ![4,0,1,6,9,3,5,2,8,7],
     ![4,0,5,7,9,3,1,8,2,6],
     ![4,0,5,8,3,9,1,7,6,2]],
    ![![2,1,0,4,3,7,6,5,9,8],
     ![2,1,0,4,3,7,6,5,9,8],
     ![0,1,2,3,4,5,6,7,8,9],
     ![3,4,0,1,2,8,9,5,6,7],
     ![3,4,0,1,2,8,9,5,6,7],
     ![3,4,0,5,8,2,9,1,7,6],
     ![6,1,0,4,9,8,2,5,3,7],
     ![3,4,0,5,8,2,9,1,7,6],
     ![8,5,0,1,6,3,7,4,2,9],
     ![8,5,0,4,3,6,7,1,9,2]],
    ![![2,3,4,0,1,7,8,9,5,6],
     ![3,2,1,0,4,8,7,6,5,9],
     ![3,2,1,0,4,8,7,6,5,9],
     ![0,1,2,3,4,5,6,7,8,9],
     ![2,3,4,0,1,7,8,9,5,6],
     ![3,8,5,0,4,2,6,7,1,9],
     ![8,3,4,0,5,6,2,9,1,7],
     ![8,6,1,0,5,3,9,2,4,7],
     ![3,8,5,0,4,2,6,7,1,9],
     ![6,8,5,0,1,9,3,7,4,2]],
    ![![1,2,3,4,0,6,7,8,9,5],
     ![1,2,3,4,0,6,7,8,9,5],
     ![4,3,2,1,0,9,8,7,6,5],
     ![4,3,2,1,0,9,8,7,6,5],
     ![0,1,2,3,4,5,6,7,8,9],
     ![1,6,8,5,0,2,9,3,7,4],
     ![4,3,8,5,0,9,2,6,7,1],
     ![4,9,7,5,0,3,6,2,8,1],
     ![4,9,6,1,0,3,7,8,2,5],
     ![4,3,8,5,0,9,2,6,7,1]],
    ![![1,2,3,8,6,0,7,4,5,9],
     ![1,2,3,8,6,0,7,4,5,9],
     ![4,3,2,7,9,0,8,1,5,6],
     ![4,9,7,2,3,0,6,5,1,8],
     ![1,6,8,3,2,0,9,5,4,7],
     ![0,1,2,3,4,5,6,7,8,9],
     ![4,3,8,6,9,0,2,5,1,7],
     ![4,3,2,7,9,0,8,1,5,6],
     ![4,3,8,6,9,0,2,5,1,7],
     ![4,9,6,8,3,0,7,1,5,2]],
    ![![2,1,6,8,3,7,0,9,5,4],
     ![2,1,6,8,3,7,0,9,5,4],
     ![6,1,2,3,8,9,0,7,4,5],
     ![8,5,7,2,3,6,0,9,1,4],
     ![3,4,9,7,2,8,0,6,5,1],
     ![3,4,9,6,8,2,0,7,1,5],
     ![0,1,2,3,4,5,6,7,8,9],
     ![8,5,7,9,6,3,0,2,4,1],
     ![3,4,9,6,8,2,0,7,1,5],
     ![3,4,9,7,2,8,0,6,5,1]],
    ![![2,3,4,9,7,1,8,0,6,5],
     ![3,2,1,6,8,4,7,0,9,5],
     ![3,2,1,6,8,4,7,0,9,5],
     ![8,6,1,2,3,5,9,0,7,4],
     ![3,8,5,7,2,4,6,0,9,1],
     ![2,3,4,9,7,1,8,0,6,5],
     ![8,3,4,9,6,5,2,0,7,1],
     ![0,1,2,3,4,5,6,7,8,9],
     ![6,8,5,7,9,1,3,0,2,4],
     ![3,8,5,7,2,4,6,0,9,1]],
    ![![2,3,8,5,7,1,4,6,0,9],
     ![3,2,7,5,8,4,1,9,0,6],
     ![8,3,2,1,6,5,4,7,0,9],
     ![3,8,6,1,2,4,5,9,0,7],
     ![3,8,6,1,2,4,5,9,0,7],
     ![2,3,8,5,7,1,4,6,0,9],
     ![3,2,7,5,8,4,1,9,0,6],
     ![6,8,3,4,9,1,5,2,0,7],
     ![0,1,2,3,4,5,6,7,8,9],
     ![8,6,9,4,3,5,1,7,0,2]],
    ![![2,3,8,6,1,7,4,5,9,0],
     ![3,2,7,9,4,8,1,5,6,0],
     ![8,3,2,7,5,6,4,1,9,0],
     ![6,8,3,2,1,9,5,4,7,0],
     ![2,3,8,6,1,7,4,5,9,0],
     ![3,8,6,9,4,2,5,1,7,0],
     ![3,2,7,9,4,8,1,5,6,0],
     ![3,8,6,9,4,2,5,1,7,0],
     ![8,6,9,7,5,3,1,4,2,0],
     ![0,1,2,3,4,5,6,7,8,9]]]) i j

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma row_bijective : ∀ i j : Fin 10, Function.Bijective (row i j) := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma row_positions : ∀ i j : Fin 10, i ≠ j →
    row i j i = 0 ∧ row i j j = (if adj i j then 1 else 2) := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma row_adj : ∀ i j a b : Fin 10, adj (row i j a) (row i j b) = adj a b := by decide +kernel

noncomputable def pairPerm (i j : Fin 10) : Equiv.Perm (Fin 10) := Equiv.ofBijective (row i j) (row_bijective i j)

lemma pairPerm_positions (i j : Fin 10) (hne : i ≠ j) :
    pairPerm i j i = 0 ∧ pairPerm i j j = (if adj i j then 1 else 2) := row_positions i j hne

lemma value_true (x : Fin 10 → Bool) : value x = true ↔
    ∃ a b : Fin 10, adj a b = true ∧ x a = true ∧ x b = true := by
  simp only [value, List.any_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨⟨a,b⟩,hmem,ha,hb⟩
    exact ⟨a,b,by simp [adj,hmem],ha,hb⟩
  · rintro ⟨a,b,hab,ha,hb⟩
    simp only [adj, Bool.or_eq_true, List.contains_iff_mem] at hab
    rcases hab with hab | hab
    · exact ⟨(a,b),hab,ha,hb⟩
    · exact ⟨(b,a),hab,hb,ha⟩

lemma pairPerm_value (i j : Fin 10) (x : Fin 10 → Bool) :
    value (fun k => x (pairPerm i j k)) = value x := by
  rw [Bool.eq_iff_iff, value_true, value_true]
  constructor
  · rintro ⟨a,b,hab,ha,hb⟩
    exact ⟨pairPerm i j a,pairPerm i j b,(row_adj i j a b).trans hab,ha,hb⟩
  · rintro ⟨a,b,hab,ha,hb⟩
    refine ⟨(pairPerm i j).symm a,(pairPerm i j).symm b,?_,?_,?_⟩
    · have h := row_adj i j ((pairPerm i j).symm a) ((pairPerm i j).symm b)
      change adj (pairPerm i j ((pairPerm i j).symm a))
        (pairPerm i j ((pairPerm i j).symm b)) = _ at h
      simpa only [Equiv.apply_symm_apply,hab] using h.symm
    · simpa using ha
    · simpa using hb

lemma canonical_pair (i j : Fin 10) (hne : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin 10), σ i = 0 ∧ σ j = (if adj i j then 1 else 2) ∧
      ∀ x : Fin 10 → Bool, value (fun k => x (σ k)) = value x :=
  ⟨pairPerm i j,(pairPerm_positions i j hne).1,(pairPerm_positions i j hne).2,
    pairPerm_value i j⟩

end PEqualNP.Outside.L_meta_2592.Automorphisms
