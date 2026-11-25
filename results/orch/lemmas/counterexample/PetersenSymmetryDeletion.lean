import PEqualNP.Defs

namespace PEqualNP.Outside.Pilot110SymmetryDeletion

def petersenFunction (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
  x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
  x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 ||
  x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def edges : List (Fin 10 × Fin 10) :=
  [(0,1), (1,2), (2,3), (3,4), (4,0), (0,5), (1,6), (2,7),
   (3,8), (4,9), (5,7), (7,9), (9,6), (6,8), (8,5)]

def adjacent (a b : Fin 10) : Prop := (a,b) ∈ edges ∨ (b,a) ∈ edges

def perm (u v : Fin 10) : Fin 10 :=
  (([[0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
    [1, 2, 3, 4, 0, 6, 7, 8, 9, 5],
    [2, 3, 4, 0, 1, 7, 8, 9, 5, 6],
    [3, 4, 0, 1, 2, 8, 9, 5, 6, 7],
    [4, 0, 1, 2, 3, 9, 5, 6, 7, 8],
    [5, 7, 9, 6, 8, 0, 2, 4, 1, 3],
    [6, 8, 5, 7, 9, 1, 3, 0, 2, 4],
    [7, 9, 6, 8, 5, 2, 4, 1, 3, 0],
    [8, 5, 7, 9, 6, 3, 0, 2, 4, 1],
    [9, 6, 8, 5, 7, 4, 1, 3, 0, 2]] : List (List (Fin 10))).getD u.val []).getD v.val 0

lemma perm_zero : ∀ u : Fin 10, perm u 0 = u := by
  decide +kernel

set_option maxHeartbeats 1000000 in
lemma perm_bijective : ∀ u : Fin 10, Function.Bijective (perm u) := by
  decide +kernel

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 100000 in
lemma perm_adjacent : ∀ u a b : Fin 10, adjacent (perm u a) (perm u b) ↔ adjacent a b := by
  unfold adjacent edges
  decide +kernel

lemma function_edges (x : Fin 10 → Bool) :
    petersenFunction x = edges.any (fun e => x e.1 && x e.2) := by
  simp [petersenFunction, edges, Bool.or_assoc]

lemma function_true_iff (x : Fin 10 → Bool) :
    petersenFunction x = true ↔
      ∃ a b : Fin 10, adjacent a b ∧ x a = true ∧ x b = true := by
  rw [function_edges]
  simp only [List.any_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨⟨a,b⟩, member, ha, hb⟩
    exact ⟨a,b,Or.inl member,ha,hb⟩
  · rintro ⟨a,b,adj,ha,hb⟩
    rcases adj with member | member
    · exact ⟨(a,b),member,ha,hb⟩
    · exact ⟨(b,a),member,hb,ha⟩

lemma petersenFunction_comp_of_adjacent (σ : Fin 10 → Fin 10)
    (bij : Function.Bijective σ)
    (pres : ∀ a b : Fin 10, adjacent (σ a) (σ b) ↔ adjacent a b)
    (x : Fin 10 → Bool) :
    petersenFunction (fun i => x (σ i)) = petersenFunction x := by
  apply Bool.eq_iff_iff.mpr
  rw [function_true_iff, function_true_iff]
  constructor
  · rintro ⟨a,b,adj,ha,hb⟩
    exact ⟨σ a,σ b,(pres a b).mpr adj,ha,hb⟩
  · rintro ⟨a,b,adj,ha,hb⟩
    obtain ⟨a,rfl⟩ := bij.surjective a
    obtain ⟨b,rfl⟩ := bij.surjective b
    exact ⟨a,b,(pres a b).mp adj,ha,hb⟩

lemma petersenFunction_comp_perm (u : Fin 10) (x : Fin 10 → Bool) :
    petersenFunction (fun i => x (perm u i)) = petersenFunction x :=
  petersenFunction_comp_of_adjacent (perm u) (perm_bijective u) (perm_adjacent u) x

def permLast (u v : Fin 10) : Fin 10 :=
  perm u (perm 9 (perm 9 (perm 9 v)))

lemma permLast_last (u : Fin 10) : permLast u 9 = u := by
  change perm u 0 = u
  exact perm_zero u

lemma permLast_bijective (u : Fin 10) : Function.Bijective (permLast u) :=
  (perm_bijective u).comp ((perm_bijective 9).comp
    ((perm_bijective 9).comp (perm_bijective 9)))

lemma permLast_adjacent (u a b : Fin 10) :
    adjacent (permLast u a) (permLast u b) ↔ adjacent a b :=
  (perm_adjacent u _ _).trans ((perm_adjacent 9 _ _).trans
    ((perm_adjacent 9 _ _).trans (perm_adjacent 9 _ _)))

lemma petersenFunction_comp_permLast (u : Fin 10) (x : Fin 10 → Bool) :
    petersenFunction (fun i => x (permLast u i)) = petersenFunction x :=
  petersenFunction_comp_of_adjacent (permLast u) (permLast_bijective u)
    (permLast_adjacent u) x

lemma exists_last_equiv (u : Fin 10) :
    ∃ e : Fin 10 ≃ Fin 10, e 9 = u ∧
      ∀ x : Fin 10 → Bool, petersenFunction (fun i => x (e i)) = petersenFunction x := by
  let e : Fin 10 ≃ Fin 10 := Equiv.ofBijective (permLast u) (permLast_bijective u)
  exact ⟨e, permLast_last u, petersenFunction_comp_permLast u⟩

lemma rename_last_update (F : (Fin 10 → Bool) → Bool) (u : Fin 10)
    (e : Fin 10 ≃ Fin 10) (he : e 9 = u)
    (hinv : ∀ x : Fin 10 → Bool, F (fun i => x (e i)) = F x)
    (y : Fin 9 → Bool) :
    let z : Fin 10 → Bool := fun i => Fin.lastCases false y (e.symm i)
    z u = false ∧ F (Function.update z u false) = F (Fin.lastCases false y) := by
  let z : Fin 10 → Bool := fun i => Fin.lastCases false y (e.symm i)
  change z u = false ∧ F (Function.update z u false) = _
  have zero : z u = false := by
    change Fin.lastCases false y (e.symm u) = false
    rw [← he, Equiv.symm_apply_apply]
    exact Fin.lastCases_last
  have update : Function.update z u false = z := by
    rw [← zero]
    exact Function.update_eq_self u z
  refine ⟨zero, ?_⟩
  rw [update]
  simpa only [z, Equiv.symm_apply_apply] using (hinv z).symm

end PEqualNP.Outside.Pilot110SymmetryDeletion
